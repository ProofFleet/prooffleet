import Conjectures.C0002_erdos_discrepancy.src.Tao2015

/-!
# Track C: Stage 2 boundary (Tao 2015 plane)

This module is **Conjectures-only** glue: it introduces a *named stage boundary* for the Tao 2015
Erdős discrepancy proof pipeline.

Design goals:
- Keep the interface small and typed (IO contract, not a pile of lemmas).
- Avoid lemma sprawl: downstream work should prove theorems *about this boundary*, rather than
  repeatedly re-stating the same intermediate reductions.

No statements here are intended for the verified substrate (`MoltResearch/`).
-/

namespace MoltResearch

namespace Tao2015

/-!
Stage 1 (`ReductionOutput`) packages a shift reduction from the original sign sequence `f` to an
auxiliary sign sequence `g` together with a step size `d`.

Stage 2 (this file) is the next boundary we want to populate: from the Stage-1 reduced sequence,
produce a fixed-step *unboundedness witness form* (`UnboundedDiscrepancyAlong`).

The point of naming this as a record is so later stages can consume it without depending on the
exact internal path used to obtain unboundedness.
-/

/-- Output of Stage 2 of the Track C pipeline.

This is intentionally minimal:
- we keep the full Stage-1 `ReductionOutput` so later stages have access to `g`, `d`, `m`, and the
  bridge contracts;
- we expose the Stage-2 result as *unbounded discrepancy along the fixed step* `d`.

Downstream stages should treat `out1.g` (at step `out1.d`) as the canonical fixed-step locus.
-/
structure Stage2Output (f : ℕ → ℤ) : Type where
  out1 : Tao2015.ReductionOutput f
  unbounded : Tao2015.UnboundedDiscrepancyAlong out1.g out1.d


/-!
## Stage 2 output lemmas

The `Stage2Output` record is defined in this file. The bulk of the convenience lemmas about
`Stage2Output` live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Output`.
-/

/-!
## Stage 2 conjecture stub

The Stage-2 conjecture/axiom stub lives in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Stub` so that this file remains mostly
“API + wiring”.
-/

end Tao2015

end MoltResearch
