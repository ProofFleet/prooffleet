#!/usr/bin/env python3
"""Generate a *truthful* starter Learning/task_metadata.json from the repo.

Design goal: avoid misinformation. We extract only what we can reliably read:
- id, file, tier
- hint (from a line like `-- Hint: ...` if present)

Everything else is optional and left as conservative defaults.

Usage:
  python3 scripts/generate_task_metadata.py > Learning/task_metadata.json
"""

from __future__ import annotations

import json
import re
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
TASKS_ROOT = REPO_ROOT / "Tasks"


def extract_hint(text: str) -> str | None:
    for line in text.splitlines():
        m = re.match(r"^\s*--\s*Hint:\s*(.*)\s*$", line)
        if m:
            return m.group(1).strip()
    return None


def main() -> None:
    tasks: list[dict] = []

    for tier_dir in ["Tier0", "Tier1"]:
        d = TASKS_ROOT / tier_dir
        if not d.exists():
            continue
        for p in sorted(d.glob("T*_*.lean")):
            tid = p.stem
            rel = p.relative_to(REPO_ROOT).as_posix()
            txt = p.read_text(encoding="utf-8", errors="replace")
            hint = extract_hint(txt)

            tasks.append(
                {
                    "id": tid,
                    "file": rel,
                    "tier": tier_dir,
                    "hint": hint or "",
                    "prerequisites": [],
                    "difficulty": 1 if tier_dir == "Tier0" else 4,
                    "expected_minutes": 20 if tier_dir == "Tier0" else 60,
                    "downstream_relevance": 1,
                    "concepts": [],
                }
            )

    print(json.dumps({"tasks": tasks}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
