#!/usr/bin/env python3
"""Shared solved-task detection for metadata-driven tooling.

Solved state is inferred from solution files committed under Solutions/.
"""

from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent

# (relative directory, filename glob)
SOLVED_SOURCES: tuple[tuple[str, str], ...] = (
    ("Solutions/Tier0", "T0_*.lean"),
    ("Solutions/Tier1", "T1_*.lean"),
)


def solved_task_ids(repo_root: Path = REPO_ROOT) -> set[str]:
    """Return solved task IDs inferred from solution source files.

    Contract:
    - each source file's stem is the canonical task id (e.g. ``T0_07``), and
    - a task is considered solved when such a file exists in one configured source.
    """

    solved: set[str] = set()
    for relative_dir, pattern in SOLVED_SOURCES:
        source_dir = repo_root / relative_dir
        if not source_dir.exists():
            continue
        for solution_file in source_dir.glob(pattern):
            solved.add(solution_file.stem)
    return solved
