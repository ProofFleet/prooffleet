#!/usr/bin/env python3
"""Validate Learning/task_metadata.json covers all Tier0/Tier1 task files."""

from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
METADATA_PATH = REPO_ROOT / "Learning" / "task_metadata.json"
REQUIRED_FIELDS = {
    "id",
    "file",
    "tier",
    "hint",
    "prerequisites",
    "difficulty",
    "expected_minutes",
    "downstream_relevance",
    "concepts",
}


def main() -> int:
    data = json.loads(METADATA_PATH.read_text(encoding="utf-8"))
    tasks = data.get("tasks")

    if not isinstance(tasks, list):
        print("ERROR: Learning/task_metadata.json must contain a top-level 'tasks' array.")
        return 1

    metadata_files: set[str] = set()
    errors: list[str] = []

    for i, entry in enumerate(tasks):
        if not isinstance(entry, dict):
            errors.append(f"tasks[{i}] is not an object")
            continue

        missing_fields = sorted(REQUIRED_FIELDS - set(entry.keys()))
        if missing_fields:
            errors.append(
                f"tasks[{i}] missing required fields: {', '.join(missing_fields)}"
            )

        file_value = entry.get("file")
        if isinstance(file_value, str):
            metadata_files.add(file_value)
        else:
            errors.append(f"tasks[{i}].file must be a string")

    task_files = {
        p.relative_to(REPO_ROOT).as_posix()
        for tier in ("Tier0", "Tier1")
        for p in (REPO_ROOT / "Tasks" / tier).glob("T*_*.lean")
    }

    missing_metadata = sorted(task_files - metadata_files)
    stale_metadata = sorted(metadata_files - task_files)

    if missing_metadata:
        errors.append(
            "missing metadata entries for task files: " + ", ".join(missing_metadata)
        )

    if stale_metadata:
        errors.append(
            "metadata entries reference non-existent task files: " + ", ".join(stale_metadata)
        )

    if errors:
        print("Task metadata coverage check failed:")
        for err in errors:
            print(f"- {err}")
        return 1

    print(
        f"Task metadata coverage OK: {len(task_files)} task files with matching metadata entries."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
