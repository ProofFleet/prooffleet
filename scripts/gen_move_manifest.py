#!/usr/bin/env python3
"""Generate the analytic-layer move manifest (rehome phase R1).

`MoltResearch/Discrepancy/` holds two different things: the Erdős-discrepancy nucleus
(`apSum`/`discOffset` and its normal-form calculus) and a large body of general analytic
number theory that was merely built there. The rehome moves the latter to
`MoltResearch/Analytic/<Topic>/` so future problem cards can use it without importing EDP.

This script computes the split mechanically instead of by hand, because the tree grows by
one to three modules a day during an active campaign — a hand-curated manifest is stale
within days. A file is a **mover** when it neither reaches `Discrepancy/Basic.lean` through
its transitive imports nor mentions a nucleus identifier in code; everything else stays.

Run it again at freeze time, immediately before the move PR, and diff against the committed
snapshot. Anything landing in UNCLASSIFIED is a deliberate decision, not a default: the
script exits non-zero so the manifest cannot be regenerated on autopilot.

    python3 scripts/gen_move_manifest.py                 # human-readable report
    python3 scripts/gen_move_manifest.py --markdown      # MOVES.md table
    python3 scripts/gen_move_manifest.py --sed           # import-rewrite sed script
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
DISCREPANCY = REPO / "MoltResearch" / "Discrepancy"

NUCLEUS_ROOT = "MoltResearch.Discrepancy.Basic"

IMPORT_RE = re.compile(r"^import\s+([\w.]+)", re.MULTILINE)

# Identifiers that make a module EDP-specific regardless of what it imports.
NUCLEUS_IDENTS = re.compile(
    r"\b(?:apSum|apSumOffset|apSumFrom|apSupport|discOffset|discOffsetUpTo|discUpTo"
    r"|discAlong|discrepancy|IsSignSequence|HasDiscrepancyAtLeast|BoundedDisc\w*"
    r"|UnboundedDisc\w*)\b"
)

# First match wins; order matters (PerronWindow is a Window, not a Zeta module).
TOPIC_RULES: list[tuple[str, str]] = [
    (r"Window|BumpDeriv|DyadicMVT", "Windows"),
    (r"Selberg|Sieve|BrunTitchmarsh|SmoothRankin|SingularMoment", "Sieve"),
    (r"Zeta|ZeroFree|Landau|LogDifferences|LFunction|EulerLog", "Zeta"),
    (r"Mertens|Chebyshev|PrimeSumBounds|CoprimeHarmonic|TruncatedBridge"
     r"|PrincipalEulerRatio", "PrimeCounts"),
    (r"Halasz|Pretentious|LogAvgCorr|LargeValues|Repulsion|Ramare|TypicalFactorization"
     r"|VinogradovTypeI|ThreeScale|LogUniformDist|LogUniform|CMOfPrimes|ZetaWeighted"
     r"|Conductor|ResidueClassReduction|PropConv|SingularSeries|Riesz", "Pretentious"),
    (r"Char|AdditiveCharCancellation|PerfectCancellation|AlmostOrthogonality|ProductFourier"
     r"|ExpSums|Parseval|Plancherel|GoodResidues|PureScaleCount"
     r"|PrincipalAndEquidistribution|MajorArcFreeze|CircleMethod|Discretize|LogGrid"
     r"|ArchimedeanTaylor", "Characters"),
    (r"Entropy|Hoeffding|TuranKubilius|StochasticMultiplicative|UniformCounting"
     r"|PatternLaws", "Probability"),
]

# Modules that are technically decoupled from the nucleus but are EDP-specific *consumers* of
# analytic material — Tao §2 spectral reduction, the §4 endgame, the Elliott observable. They
# belong in Discrepancy/ after the rehome, which is exactly what that directory should hold.
STAY_OVERRIDES = {
    "ChiTildeCutoff",
    "DecrementObservable",
    "DilationCover",
    "EndgameAssembly",
    "EndgameContradiction",
    "PrimeDataSpace",
    "ResidueMaxPipelineExample",
}

# Movers that change name as they move.
RENAMES = {
    # The analytic regression module becomes the analytic layer's own NormalFormExamples.
    "NormalFormExamplesAnalytic": ("", "NormalFormExamples"),
}

# The one import edge the rehome removes first (phase R2): MultiplicativeC's ℂ-multiplicative
# language layer is Mathlib-only apart from a short bridge tail, which moves to
# Discrepancy/MultiplicativeCBridge.lean. Severing it is what frees the pretentious/Halász
# stack — 37 modules — to move. Pass --assume-split to model the post-R2 tree before R2 lands.
SPLIT_EDGE = ("MoltResearch.Discrepancy.MultiplicativeC", "MoltResearch.Discrepancy.Multiplicative")


def strip_comments(text: str) -> str:
    """Blank out Lean block comments (`/- … -/`, including `/-!` and `/--`) and `--` lines."""
    out: list[str] = []
    depth = 0
    i = 0
    while i < len(text):
        two = text[i:i + 2]
        if two == "/-":
            depth += 1
            i += 2
            continue
        if two == "-/":
            depth = max(0, depth - 1)
            i += 2
            continue
        if depth == 0 and two == "--":
            j = text.find("\n", i)
            i = len(text) if j == -1 else j
            continue
        if depth == 0:
            out.append(text[i])
        i += 1
    return "".join(out)


def module_name(path: Path) -> str:
    return ".".join(path.relative_to(REPO).with_suffix("").parts)


def topic_for(stem: str) -> str:
    for pattern, topic in TOPIC_RULES:
        if re.search(pattern, stem):
            return topic
    return "UNCLASSIFIED"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--markdown", action="store_true", help="emit the MOVES.md table")
    parser.add_argument("--sed", action="store_true", help="emit an import-rewrite sed script")
    parser.add_argument(
        "--assume-split",
        action="store_true",
        help="model the tree after the phase-R2 MultiplicativeC split (planning aid; "
        "unnecessary once R2 has actually landed)",
    )
    args = parser.parse_args()

    if not DISCREPANCY.is_dir():
        print(f"ERROR: {DISCREPANCY} not found", file=sys.stderr)
        return 2

    files = sorted(DISCREPANCY.glob("*.lean"))
    imports: dict[str, set[str]] = {}
    uses_nucleus: dict[str, bool] = {}

    for path in files:
        raw = path.read_text(encoding="utf-8")
        name = module_name(path)
        imports[name] = set(IMPORT_RE.findall(raw))
        # Import lines are not "use"; strip comments so prose mentions don't count either.
        body = strip_comments(raw)
        body = IMPORT_RE.sub("", body)
        uses_nucleus[name] = bool(NUCLEUS_IDENTS.search(body))

    if args.assume_split:
        src, dep = SPLIT_EDGE
        if src in imports:
            imports[src] = {d for d in imports[src] if d != dep}

    def reaches_nucleus(name: str, seen: set[str] | None = None) -> bool:
        if seen is None:
            seen = set()
        if name in seen:
            return False
        seen.add(name)
        for dep in imports.get(name, ()):
            if dep == NUCLEUS_ROOT:
                return True
            if dep in imports and reaches_nucleus(dep, seen):
                return True
        return False

    movers: list[tuple[str, str, Path]] = []
    stays: list[tuple[str, Path]] = []
    for path in files:
        name = module_name(path)
        stem = path.stem
        if stem in STAY_OVERRIDES:
            stays.append(("EDP consumer (policy)", path))
        elif name == NUCLEUS_ROOT or reaches_nucleus(name) or uses_nucleus[name]:
            reason = "nucleus identifiers" if uses_nucleus[name] else "imports Basic"
            stays.append((reason, path))
        else:
            topic, new_stem = RENAMES.get(stem, (topic_for(stem), stem))
            movers.append((topic, new_stem, path))

    unclassified = [m for m in movers if m[0] == "UNCLASSIFIED"]

    def destination(topic: str, stem: str) -> tuple[str, str]:
        """Return (module name, repo-relative path) for a mover's new home."""
        parts = ["MoltResearch", "Analytic"] + ([topic] if topic else []) + [stem]
        return ".".join(parts), "/".join(parts) + ".lean"

    if args.sed:
        for topic, stem, path in sorted(movers):
            old = f"MoltResearch.Discrepancy.{path.stem}"
            new, _ = destination(topic, stem)
            print(f"s/\\b{re.escape(old)}\\b/{new}/g")
        return 1 if unclassified else 0

    if args.markdown:
        print("# Analytic-layer move manifest\n")
        print(f"{len(movers)} modules move; {len(stays)} stay in `MoltResearch/Discrepancy/`.\n")
        print("| module | from | to |")
        print("| --- | --- | --- |")
        for topic, stem, path in sorted(movers):
            _, dest = destination(topic, stem)
            print(f"| `{path.stem}` | `{path.relative_to(REPO)}` | `{dest}` |")
        return 1 if unclassified else 0

    by_topic: dict[str, list[str]] = {}
    for topic, stem, _ in movers:
        by_topic.setdefault(topic, []).append(stem)

    print(f"gen_move_manifest: {len(files)} modules under MoltResearch/Discrepancy/")
    print(f"  movers: {len(movers)}   stay: {len(stays)}\n")
    for topic in sorted(by_topic):
        names = sorted(by_topic[topic])
        print(f"  {topic or '(Analytic root)'} ({len(names)}):")
        for chunk in (names[i:i + 4] for i in range(0, len(names), 4)):
            print("      " + ", ".join(chunk))
    print(f"\n  staying ({len(stays)}):")
    reasons: dict[str, int] = {}
    for reason, _ in stays:
        reasons[reason] = reasons.get(reason, 0) + 1
    for reason, count in sorted(reasons.items()):
        print(f"      {count} via {reason}")

    if unclassified:
        print(f"\nERROR: {len(unclassified)} module(s) have no topic; extend TOPIC_RULES:")
        for _, stem, _ in sorted(unclassified):
            print(f"  - {stem}")
        return 1

    print("\ngen_move_manifest: every mover has a topic")
    return 0


if __name__ == "__main__":
    # Behave like a normal CLI filter when piped into `head`.
    import signal

    if hasattr(signal, "SIGPIPE"):
        signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    raise SystemExit(main())
