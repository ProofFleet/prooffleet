#!/usr/bin/env python3
"""Generate a simple learning/research dashboard from task metadata."""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
METADATA_PATH = REPO_ROOT / "Learning" / "task_metadata.json"
SOLUTIONS_TIER0 = REPO_ROOT / "Solutions" / "Tier0"


def load_tasks() -> list[dict]:
    with METADATA_PATH.open() as f:
        return json.load(f)["tasks"]


def solved_task_ids() -> set[str]:
    solved = set()
    if SOLUTIONS_TIER0.exists():
        for p in SOLUTIONS_TIER0.glob("T0_*.lean"):
            solved.add(p.stem)
    return solved


def main() -> None:
    tasks = load_tasks()
    solved = solved_task_ids()

    tier_counts = Counter(t["tier"] for t in tasks)
    tier_solved = Counter(t["tier"] for t in tasks if t["id"] in solved)

    concept_counts = Counter()
    solved_concept_counts = Counter()
    for t in tasks:
        for c in t["concepts"]:
            concept_counts[c] += 1
            if t["id"] in solved:
                solved_concept_counts[c] += 1

    print("# Learning Dashboard")
    print()
    print("## Tier Progress")
    for tier in sorted(tier_counts):
        total = tier_counts[tier]
        done = tier_solved[tier]
        pct = (100 * done / total) if total else 0
        print(f"- {tier}: {done}/{total} solved ({pct:.1f}%)")

    print("\n## Concept Coverage")
    for concept, total in concept_counts.most_common():
        done = solved_concept_counts[concept]
        pct = 100 * done / total
        print(f"- {concept}: {done}/{total} ({pct:.1f}%)")

    print("\n## Suggested Readiness Signal")
    unsolved_unlocked = 0
    for t in tasks:
        if t["id"] in solved:
            continue
        if all(pr in solved for pr in t["prerequisites"]):
            unsolved_unlocked += 1
    print(f"- Unlocked unsolved tasks in metadata: {unsolved_unlocked}")


if __name__ == "__main__":
    main()
