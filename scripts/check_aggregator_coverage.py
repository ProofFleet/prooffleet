#!/usr/bin/env python3
"""Every module under MoltResearch/ must actually be compiled by CI.

`lake build` only compiles the import closure of what it is given. A module that no
aggregator imports and that nobody names in `scripts/ci_targets.txt` is therefore invisible
to CI: it can rot, or never have compiled at all, and nothing reports it. That failure mode
has bitten this repo before -- `NormalFormExamples` once accumulated ~95 compile errors
unnoticed, and a false Stage-2 stub axiom sat unnoticed (issue #2843).

The standalone audit and regression modules are *deliberately* outside the aggregators (the
stable surface cannot import its own regression tests without a cycle), so "imported by
something" is not the right rule. The right rule is reachability from the CI target set:

    every MoltResearch/**/*.lean is in the transitive import closure of some CI target.

Run it after adding a module. If it reports an orphan, either wire the module into the
aggregator it belongs to, or -- for an opt-in or compile-only module that must stay out of the
stable surface -- add it to `scripts/ci_targets.txt`.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
CI_TARGETS = REPO / "scripts" / "ci_targets.txt"
ALLOWLIST = REPO / "scripts" / "uncompiled_allowlist.txt"

IMPORT_RE = re.compile(r"^import\s+([\w.]+)", re.MULTILINE)

# Declared in lakefile.lean with `.submodules` globs: the lib compiles every file in
# the tree regardless of imports, so each file is a build root in its own right.
GLOB_LIBS = {"Tasks", "Conjectures"}


def module_name(path: Path) -> str:
    return ".".join(path.relative_to(REPO).with_suffix("").parts)


def read_targets() -> list[str]:
    targets: list[str] = []
    for raw in CI_TARGETS.read_text(encoding="utf-8").splitlines():
        entry = raw.split("#", 1)[0].strip()
        if entry:
            targets.append(entry)
    return targets


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--warn-only",
        action="store_true",
        help="report orphans without failing (rollout aid)",
    )
    args = parser.parse_args()

    if not CI_TARGETS.exists():
        print(f"ERROR: {CI_TARGETS.relative_to(REPO)} not found", file=sys.stderr)
        return 2

    # Map every library module to its imports. All four trees matter, not just MoltResearch:
    # the backlog libs import MoltResearch modules, so a module reachable only from a
    # Conjectures stage file is still compiled by CI and must not be reported as an orphan.
    imports: dict[str, set[str]] = {}
    for tree in ("MoltResearch", "Solutions", "Tasks", "Conjectures"):
        for path in sorted((REPO / tree).rglob("*.lean")):
            imports[module_name(path)] = set(IMPORT_RE.findall(path.read_text(encoding="utf-8")))
    # Root entrypoints (MoltResearch.lean, Solutions.lean, …) sit at the repo root.
    for entry in ("MoltResearch", "Solutions", "Tasks", "Conjectures"):
        root = REPO / f"{entry}.lean"
        if root.exists():
            imports[entry] = set(IMPORT_RE.findall(root.read_text(encoding="utf-8")))

    reachable: set[str] = set()

    def visit(name: str) -> None:
        if name in reachable or name not in imports:
            return
        reachable.add(name)
        for dep in imports[name]:
            visit(dep)

    for target in read_targets():
        if target in GLOB_LIBS:
            # lakefile declares these with `.submodules` globs: every file in the tree is
            # compiled whether or not anything imports it, so each is its own seed.
            for name in imports:
                if name.startswith(f"{target}."):
                    visit(name)
        else:
            visit(target)

    # The reachability graph spans every tree (so a Conjectures -> MoltResearch import counts),
    # but the invariant being enforced is about the verified nucleus: every module under
    # MoltResearch/. The backlog trees are compiled wholesale by their globs, and their root
    # entrypoints are docstring-only, so neither needs accounting for here.
    modules = {m for m in imports if m.startswith("MoltResearch.")}
    orphans = sorted(modules - reachable)

    print(
        f"check_aggregator_coverage: {len(modules)} modules, "
        f"{len(modules & reachable)} reachable from scripts/ci_targets.txt"
    )

    if not orphans:
        print("check_aggregator_coverage: OK - every module is compiled by CI")
        return 0

    allowed: set[str] = set()
    if ALLOWLIST.exists():
        for raw in ALLOWLIST.read_text(encoding="utf-8").splitlines():
            entry = raw.split("#", 1)[0].strip()
            if entry:
                allowed.add(entry)

    known = [o for o in orphans if o in allowed]
    unknown = [o for o in orphans if o not in allowed]

    if known:
        print(f"\nWARN: {len(known)} known-uncompiled module(s) (see {ALLOWLIST.name}):")
        for orphan in known:
            print(f"  {orphan}")

    if unknown:
        label = "WARN" if args.warn_only else "ERROR"
        print(f"\n{label}: {len(unknown)} module(s) that CI never compiles:")
        for orphan in unknown:
            rel = Path(*orphan.split(".")).with_suffix(".lean")
            print(f"  {orphan}  ({rel})")
        print(
            "\nWire each into the aggregator it belongs to, or add it to "
            "scripts/ci_targets.txt if it must stay outside the stable surface "
            "(opt-in simp modules and compile-only regression files)."
        )
        return 0 if args.warn_only else 1

    return 0


if __name__ == "__main__":
    # Behave like a normal CLI filter when piped into `head`.
    import signal

    if hasattr(signal, "SIGPIPE"):
        signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    raise SystemExit(main())
