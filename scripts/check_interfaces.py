#!/usr/bin/env python3
"""Interface-review linter for hypothesis classes (`*Assumption`).

The Track C proof plane states its results conditionally, via Prop-valued typeclasses that
stand in for cited theorems of the literature.  `TrackCAxiomAudit.lean` already pins the
*axiom footprint* of the flagship theorems, but a footprint audit is blind to the failure
mode that actually matters here: an interface whose **statement** silently drifts from the
paper it cites (too strong to ever discharge, or too weak to carry the consumer).

This script makes the repo's prose conventions mechanical.  For every `class <Name>Assumption`
under `Conjectures/` it checks:

1. **Citation** — the class docstring or its module header names a source (`arXiv:NNNN.NNNNN`
   or an explicit `Source:` line).  Axiom-hygiene rule, `Problems/tao2015_analytic_core.md` §6.
2. **Instance honesty** — a file claiming "no instance ... may be declared" must actually have
   no instance of that class, and vice versa.  These claims go stale silently when a campaign
   discharges an interface.
3. **Registry** — the class is transcribed in `Problems/sources/tao2015_statements.md`, the
   quotable source of truth interfaces are meant to be diffable against.
4. **Location** — the class lives under an `Interfaces/` directory, so path-based CI gates can
   detect interface changes.  Classes listed in `scripts/interface_location_allowlist.txt` are
   exempt while the extraction campaign runs.

Exit status is 0 (warnings only) unless `--strict` is passed; the intended rollout is warning
mode first, then `--strict` in CI once the current findings are cleared.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

CONJECTURES = REPO / "Conjectures"
REGISTRY = REPO / "Problems" / "sources" / "tao2015_statements.md"
LOCATION_ALLOWLIST = REPO / "scripts" / "interface_location_allowlist.txt"

# `class Foo Assumption : Prop where`, captured with the docstring that precedes it (if any).
CLASS_RE = re.compile(r"^class\s+(\w*Assumption)\b", re.MULTILINE)
# A doc comment `/-- ... -/` or module doc `/-! ... -/`.
DOCSTRING_RE = re.compile(r"/--(.*?)-/", re.DOTALL)
CITATION_RE = re.compile(r"arXiv:\d{4}\.\d{4,5}|^\s*Source:", re.MULTILINE | re.IGNORECASE)
# "No (unconditional) instance ... is (or may be) declared", tolerant of line wrapping.
NO_INSTANCE_RE = re.compile(
    r"no\s+(?:unconditional\s+)?instance\s+of\s+this\s+class[^.]{0,200}?declared"
    r"|no\s+instance[^.]{0,120}?(?:is|may)\s+(?:or\s+may\s+be\s+)?declared",
    re.IGNORECASE | re.DOTALL,
)


def lean_files(root: Path) -> list[Path]:
    return sorted(p for p in root.rglob("*.lean"))


def docstring_for(text: str, class_start: int) -> str:
    """Return the doc comment immediately preceding the class declaration, if any."""
    head = text[:class_start]
    matches = list(DOCSTRING_RE.finditer(head))
    if not matches:
        return ""
    last = matches[-1]
    # Only count it if nothing but whitespace/attributes separates it from the class.
    between = head[last.end():]
    if re.fullmatch(r"\s*(@\[[^\]]*\]\s*)*", between):
        return last.group(1)
    return ""


INSTANCE_START_RE = re.compile(r"^\s*(noncomputable\s+)?(local\s+)?instance\b")


def find_instances(name: str, files: list[Path]) -> list[str]:
    """Locate genuine `instance` declarations *of* `name`.

    The subtlety worth getting right: a class is used two ways, and only one is an instance.

        instance (priority := 90) Foo.ofAllAlpha : Foo := ...     -- declares an instance of Foo
        instance bar [Foo] : Baz := ...                           -- *consumes* Foo as a hypothesis

    A naive "class name near the word instance" search reports the second as the first, which
    would flag every correctly-documented open interface the moment something consumes it.  So
    we read the instance signature (up to `where` / `:=`), drop bracketed instance-implicit
    hypotheses, and accept only the result-type position or the `instance Foo.name` namespace form.
    """
    hits: list[str] = []
    for path in files:
        lines = path.read_text(encoding="utf-8").splitlines()
        for i, line in enumerate(lines):
            if not INSTANCE_START_RE.match(line):
                continue
            # Accumulate the signature: this line plus continuations, stopping at the body.
            # Parenthesised groups are masked before looking for the body delimiter, because
            # `instance (priority := 90) foo :` carries a `:=` that is not the body.
            signature = []
            for j in range(i, min(i + 12, len(lines))):
                chunk = lines[j]
                signature.append(chunk)
                masked = re.sub(r"\([^)]*\)", " ", chunk)
                if "where" in masked or ":=" in masked:
                    break
            text = re.sub(r"\([^)]*\)", " ", " ".join(signature))
            text = text.split("where")[0].split(":=")[0]
            # Instance-implicit args are hypotheses, not the declared instance.
            hypotheses = re.findall(r"\[([^\]]*)\]", text)
            stripped = re.sub(r"\[[^\]]*\]", " ", text)
            namespace_form = re.search(
                rf"\binstance\b\s*(\([^)]*\)\s*)?{re.escape(name)}\.", stripped
            )
            result_form = re.search(rf":\s*{re.escape(name)}\b", stripped)
            if not (namespace_form or result_form):
                continue
            # An instance carrying another interface as a hypothesis is a *reduction*
            # (`MajorArc.ofAllAlpha`, `VK from Littlewood`), not a discharge — the docstrings
            # that say "no instance may be declared" mean no unconditional one, and several
            # explicitly note the weakening instance below them.  Only count discharges.
            conditional = any(re.search(r"\w*Assumption\b", h) for h in hypotheses)
            if not conditional:
                hits.append(f"{path.relative_to(REPO)}:{i + 1}")
    return hits


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--strict",
        action="store_true",
        help="exit non-zero on findings (CI enforcement mode)",
    )
    args = parser.parse_args()

    if not CONJECTURES.is_dir():
        print(f"ERROR: {CONJECTURES} not found", file=sys.stderr)
        return 2

    files = lean_files(CONJECTURES)
    registry = REGISTRY.read_text(encoding="utf-8") if REGISTRY.exists() else ""
    if not registry:
        print(f"WARNING: registry {REGISTRY.relative_to(REPO)} not found or empty")

    allowlist: set[str] = set()
    if LOCATION_ALLOWLIST.exists():
        for raw in LOCATION_ALLOWLIST.read_text(encoding="utf-8").splitlines():
            entry = raw.split("#", 1)[0].strip()
            if entry:
                allowlist.add(entry)

    findings: list[str] = []
    classes: list[tuple[str, Path]] = []

    for path in files:
        text = path.read_text(encoding="utf-8")
        for match in CLASS_RE.finditer(text):
            name = match.group(1)
            rel = path.relative_to(REPO)
            classes.append((name, path))

            # 1. Citation: class docstring first, then the whole file (module header).
            doc = docstring_for(text, match.start())
            if not CITATION_RE.search(doc) and not CITATION_RE.search(text):
                findings.append(
                    f"{rel}: `{name}` has no citation "
                    f"(expected `arXiv:NNNN.NNNNN` or a `Source:` line in its docstring)"
                )

            # 2. Instance honesty.  Scope the claim to the class's own docstring; only fall back
            # to the module header when the file declares a single class, since a module claim
            # in a two-class file (Elliott, Fourier) belongs to just one of them.
            single_class_file = len(CLASS_RE.findall(text)) == 1
            claim_scope = doc if not single_class_file else text
            claims_none = bool(NO_INSTANCE_RE.search(claim_scope))
            instances = find_instances(name, files)
            if claims_none and instances:
                findings.append(
                    f"{rel}: `{name}` docstring claims no instance may be declared, "
                    f"but instances exist: {', '.join(instances)}"
                )

            # 3. Registry coverage.
            if registry and name not in registry:
                findings.append(
                    f"{rel}: `{name}` is missing from "
                    f"{REGISTRY.relative_to(REPO)} (interfaces must be diffable "
                    f"against the transcribed source)"
                )

            # 4. Location.
            if "Interfaces" not in rel.parts and name not in allowlist:
                findings.append(
                    f"{rel}: `{name}` is not under an `Interfaces/` directory "
                    f"(add it to {LOCATION_ALLOWLIST.relative_to(REPO)} if the "
                    f"extraction has not reached it yet)"
                )

    print(f"check_interfaces: scanned {len(files)} files, found {len(classes)} interface classes")
    for name, path in sorted(classes):
        print(f"  - {name}  ({path.relative_to(REPO)})")

    if findings:
        print(f"\ncheck_interfaces: {len(findings)} finding(s):")
        for finding in findings:
            print(f"  {'ERROR' if args.strict else 'WARN'}: {finding}")
        if args.strict:
            return 1
        print("\n(warning mode: pass --strict to make these failures)")
    else:
        print("\ncheck_interfaces: no findings")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
