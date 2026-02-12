#!/usr/bin/env python3
"""Recommend next tasks from Learning/task_metadata.json.

Usage:
  python scripts/next_task_recommender.py
  python scripts/next_task_recommender.py --focus logic --top 5
  python scripts/next_task_recommender.py --strategy impact
"""

from __future__ import annotations

import argparse
import json
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


def unlocked(task: dict, solved: set[str]) -> bool:
    return all(pr in solved for pr in task["prerequisites"])


def score(task: dict, strategy: str) -> float:
    if strategy == "easiest":
        return 100 - (task["difficulty"] * 10 + task["expected_minutes"] / 10)
    if strategy == "impact":
        return task["downstream_relevance"] * 10 - task["difficulty"]
    # blended
    return (
        task["downstream_relevance"] * 4
        + (7 - task["difficulty"]) * 3
        + max(0, 60 - task["expected_minutes"]) / 15
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--top", type=int, default=3)
    parser.add_argument("--strategy", choices=["blended", "easiest", "impact"], default="blended")
    parser.add_argument("--focus", help="Prefer tasks containing this concept.")
    args = parser.parse_args()

    tasks = load_tasks()
    solved = solved_task_ids()

    candidates = []
    for task in tasks:
        if task["id"] in solved:
            continue
        if not unlocked(task, solved):
            continue
        s = score(task, args.strategy)
        if args.focus and args.focus not in task["concepts"]:
            s -= 2
        candidates.append((s, task))

    candidates.sort(key=lambda pair: pair[0], reverse=True)

    print(f"Solved tasks detected: {sorted(solved) if solved else 'none'}")
    print(f"Recommendation strategy: {args.strategy}")
    if args.focus:
        print(f"Focus concept: {args.focus}")
    print("\nTop recommendations:")

    for rank, (s, task) in enumerate(candidates[: args.top], start=1):
        print(
            f"{rank}. {task['id']} ({task['tier']}) score={s:.1f} "
            f"difficulty={task['difficulty']} eta={task['expected_minutes']}m "
            f"relevance={task['downstream_relevance']} concepts={','.join(task['concepts'])}"
        )

    if not candidates:
        print("No unlocked unsolved tasks found in metadata.")


if __name__ == "__main__":
    main()
