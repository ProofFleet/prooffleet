import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Core

/-!
# Track C: Stage 3 boundary (Tao 2015 plane)

This module is **Conjectures-only** glue.

Stage 2 produces a fixed-step unboundedness witness for the reduced sequence `g` (at step `d`),
plus a transport lemma back to an *offset discrepancy* witness for the original sequence `f`.

Stage 3 is the boundary where we finally discharge the global goal `¬ BoundedDiscrepancy f`.

Design goal: keep the hard-gate surface small.

Most convenience lemmas about `Stage3Output` live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3Output`.
-/

namespace MoltResearch

namespace Tao2015

/-- Output of Stage 3 of the Track C pipeline.

We keep the full Stage-2 output for traceability. The global conclusion
`¬ BoundedDiscrepancy f` is derived (as `Stage3Output.notBounded`) from the Stage-2 boundary.
-/
structure Stage3Output (f : ℕ → ℤ) : Type where
  out2 : Tao2015.Stage2Output f

namespace Stage3Output

variable {f : ℕ → ℤ}

/-- Convenience projection: Stage 3 carries the full Stage-2 output, hence also carries the
underlying Stage-1 reduction output.

This is occasionally useful when later stages want access to the deterministic parameters
`g, d, m` and the Stage-1 transport contracts, without reaching through multiple record fields.
-/
abbrev out1 (out : Stage3Output f) : Tao2015.ReductionOutput f :=
  out.out2.out1

/-- Stage 3 already closes the global goal `¬ BoundedDiscrepancy f`.

We intentionally do not store this as a field: it is derived from the Stage-2 output.

Design note: we prove this directly from the Stage-1 transport contract carried by the Stage-2
output (via `ReductionOutput.not_boundedDiscrepancy_of_unboundedDiscrepancyAlong`), so this module
does not need to import the larger Stage-2 convenience-lemma layer.
-/
theorem notBounded (out : Stage3Output f) : ¬ BoundedDiscrepancy f := by
  -- Delegate to the canonical Stage-2 “bridge back to the global statement” lemma.
  exact out.out2.notBoundedOriginal (f := f)

/-- Deterministic Stage-3 completion: a Stage-2 output already contains enough information to
contradict any global boundedness hypothesis.

This is the main “stage boundary” lemma: it is *proved* (no `sorry`) and should remain stable.
-/
def ofStage2Output (out2 : Tao2015.Stage2Output f) : Stage3Output f :=
  ⟨out2⟩

/-- Stage 3 output implies the usual surface statement `∀ C, HasDiscrepancyAtLeast f C`.

We keep this lemma in the hard-gate module so `ErdosDiscrepancy.lean` can remain minimal.
-/
theorem forall_hasDiscrepancyAtLeast (out : Stage3Output f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  -- Reuse the Stage-2 surface lemma rather than re-proving it.
  exact out.out2.forall_hasDiscrepancyAtLeast (f := f)

end Stage3Output

/-!
## Stage 3 entry point

The Stage-3 entry point `stage3` (a definition, not an axiom) lives in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryCore` (re-exported by
`...TrackCStage3Entry`) so that this file remains purely “API + wiring”.
-/

end Tao2015

end MoltResearch
