#!/usr/bin/env bash
set -euo pipefail

# Generate a timestamped launch report with deltas vs previous run.
#
# Usage:
#   scripts/yolo_launch.sh
#   scripts/yolo_launch.sh --top 7 --strategy impact --focus logic

TOP=5
STRATEGY="blended"
FOCUS=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --top)
      TOP="$2"
      shift 2
      ;;
    --strategy)
      STRATEGY="$2"
      shift 2
      ;;
    --focus)
      FOCUS="$2"
      shift 2
      ;;
    *)
      echo "Unknown argument: $1" >&2
      exit 1
      ;;
  esac
done

if ! command -v python3 >/dev/null 2>&1; then
  echo "python3 is required" >&2
  exit 1
fi

TOP="$TOP" STRATEGY="$STRATEGY" FOCUS="$FOCUS" python3 - <<'PY'
from __future__ import annotations

import datetime as dt
import json
import os
from collections import Counter
from pathlib import Path

repo_root = Path.cwd()
reports_dir = repo_root / "reports"
reports_dir.mkdir(parents=True, exist_ok=True)

metadata_path = repo_root / "Learning" / "task_metadata.json"
solutions_tier0 = repo_root / "Solutions" / "Tier0"
snapshot_path = reports_dir / "launch_latest.json"

top_n = int(os.environ.get("TOP", "5"))
strategy = os.environ.get("STRATEGY", "blended")
focus = os.environ.get("FOCUS", "").strip()
if strategy not in {"blended", "easiest", "impact"}:
    raise SystemExit(f"Unsupported strategy: {strategy}")


def load_tasks() -> list[dict]:
    with metadata_path.open() as f:
        return json.load(f)["tasks"]


def solved_task_ids() -> set[str]:
    solved = set()
    if solutions_tier0.exists():
        for p in solutions_tier0.glob("T0_*.lean"):
            solved.add(p.stem)
    return solved


def unlocked(task: dict, solved: set[str]) -> bool:
    prereqs = task.get("prerequisites") or []
    return all(pr in solved for pr in prereqs)


def score(task: dict) -> float:
    diff = int(task.get("difficulty") or 3)
    eta = float(task.get("expected_minutes") or 30)
    rel = float(task.get("downstream_relevance") or 1)

    if strategy == "easiest":
        return 100 - (diff * 10 + eta / 10)
    if strategy == "impact":
        return rel * 10 - diff
    return rel * 4 + (7 - diff) * 3 + max(0, 60 - eta) / 15


def plus_minus(n: int) -> str:
    return f"+{n}" if n > 0 else str(n)


tasks = load_tasks()
solved = solved_task_ids()

# Unlocked task set
unlocked_ids: set[str] = set()
for task in tasks:
    tid = task.get("id")
    if not tid or tid in solved:
        continue
    if unlocked(task, solved):
        unlocked_ids.add(tid)

# Concept coverage
concept_total = Counter()
concept_done = Counter()
for task in tasks:
    tid = task.get("id")
    for concept in (task.get("concepts") or []):
        concept_total[concept] += 1
        if tid in solved:
            concept_done[concept] += 1

all_total_mentions = sum(concept_total.values())
all_done_mentions = sum(concept_done.values())
coverage_pct = (100.0 * all_done_mentions / all_total_mentions) if all_total_mentions else 0.0

# Recommendations
candidates: list[tuple[float, dict]] = []
for task in tasks:
    tid = task.get("id")
    if not tid or tid in solved or not unlocked(task, solved):
        continue
    s = score(task)
    concepts = task.get("concepts") or []
    if focus and focus not in concepts:
        s -= 2
    candidates.append((s, task))
candidates.sort(key=lambda pair: pair[0], reverse=True)
recs = candidates[:top_n]

# Previous snapshot (if available)
prev = None
if snapshot_path.exists():
    with snapshot_path.open() as f:
        prev = json.load(f)

prev_unlocked = set((prev or {}).get("unlocked_ids", []))
newly_unlocked = sorted(unlocked_ids - prev_unlocked)
no_longer_unlocked = sorted(prev_unlocked - unlocked_ids)

prev_coverage_pct = float((prev or {}).get("coverage_pct", 0.0)) if prev else None

prev_rec_ids = (prev or {}).get("recommendation_ids", []) if prev else []
cur_rec_ids = [task["id"] for _, task in recs]
added_recs = [rid for rid in cur_rec_ids if rid not in prev_rec_ids]
dropped_recs = [rid for rid in prev_rec_ids if rid not in cur_rec_ids]

rank_changes = []
prev_ranks = {rid: i + 1 for i, rid in enumerate(prev_rec_ids)}
for i, rid in enumerate(cur_rec_ids, start=1):
    if rid in prev_ranks:
        delta = prev_ranks[rid] - i
        if delta != 0:
            direction = "up" if delta > 0 else "down"
            rank_changes.append(f"- {rid}: {direction} {abs(delta)} (from #{prev_ranks[rid]} to #{i})")

now = dt.datetime.now(dt.timezone.utc)
datestamp = now.strftime("%Y%m%d")
report_path = reports_dir / f"launch_{datestamp}.md"

lines = []
lines.append(f"# Launch Report — {now.strftime('%Y-%m-%d %H:%M UTC')}")
lines.append("")
lines.append(f"- Strategy: `{strategy}`")
lines.append(f"- Focus: `{focus or 'none'}`")
lines.append(f"- Top N: `{top_n}`")
if prev:
    lines.append(f"- Compared to previous snapshot: `{prev.get('generated_at', 'unknown')}`")
else:
    lines.append("- Compared to previous snapshot: _none (baseline run)_")
lines.append("")

lines.append("## Unlocked tasks (unsolved)")
unlock_delta = len(unlocked_ids) - len(prev_unlocked)
lines.append(f"- Current: **{len(unlocked_ids)}** ({plus_minus(unlock_delta)} vs prior)")
if prev:
    lines.append(f"- Newly unlocked: {', '.join(newly_unlocked) if newly_unlocked else 'none'}")
    lines.append(f"- No longer unlocked: {', '.join(no_longer_unlocked) if no_longer_unlocked else 'none'}")
lines.append("")

lines.append("## Concept coverage")
if prev_coverage_pct is None:
    lines.append(f"- Overall solved concept mentions: **{all_done_mentions}/{all_total_mentions} ({coverage_pct:.1f}%)**")
else:
    cov_delta = coverage_pct - prev_coverage_pct
    lines.append(
        f"- Overall solved concept mentions: **{all_done_mentions}/{all_total_mentions} ({coverage_pct:.1f}%)** "
        f"({cov_delta:+.1f}pp vs prior)"
    )

if prev:
    prev_done = Counter((prev or {}).get("concept_done", {}))
    concept_deltas = []
    for concept in concept_total:
        delta = concept_done[concept] - int(prev_done.get(concept, 0))
        if delta != 0:
            concept_deltas.append((concept, delta, concept_done[concept], concept_total[concept]))
    concept_deltas.sort(key=lambda x: abs(x[1]), reverse=True)
    if concept_deltas:
        lines.append("- Concepts with solved-count change:")
        for concept, delta, done, total in concept_deltas[:10]:
            lines.append(f"  - {concept}: {done}/{total} ({plus_minus(delta)} solved tasks)")
    else:
        lines.append("- Concepts with solved-count change: none")
else:
    lines.append("- Concepts with solved-count change: n/a (baseline run)")
lines.append("")

lines.append("## Top recommendations")
for idx, (s, task) in enumerate(recs, start=1):
    concepts = ",".join(task.get("concepts") or []) or "-"
    lines.append(
        f"{idx}. `{task['id']}` ({task.get('tier', '?')}) score={s:.1f} "
        f"difficulty={task.get('difficulty', '?')} eta={task.get('expected_minutes', '?')}m "
        f"relevance={task.get('downstream_relevance', '?')} concepts={concepts}"
    )
if not recs:
    lines.append("- No unlocked unsolved tasks found in metadata.")

if prev:
    lines.append("")
    lines.append("### Recommendation deltas vs prior")
    lines.append(f"- Added to top list: {', '.join(added_recs) if added_recs else 'none'}")
    lines.append(f"- Dropped from top list: {', '.join(dropped_recs) if dropped_recs else 'none'}")
    if rank_changes:
        lines.append("- Rank changes:")
        lines.extend(rank_changes)
    else:
        lines.append("- Rank changes: none")

report_path.write_text("\n".join(lines) + "\n")

snapshot = {
    "generated_at": now.isoformat(),
    "report_path": str(report_path.relative_to(repo_root)),
    "strategy": strategy,
    "focus": focus,
    "top": top_n,
    "unlocked_ids": sorted(unlocked_ids),
    "coverage_pct": coverage_pct,
    "concept_done": dict(concept_done),
    "concept_total": dict(concept_total),
    "recommendation_ids": cur_rec_ids,
}
snapshot_path.write_text(json.dumps(snapshot, indent=2, sort_keys=True) + "\n")

print(f"Wrote {report_path.relative_to(repo_root)}")
print(f"Updated {snapshot_path.relative_to(repo_root)}")
PY
