import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Proof

/-!
# Track C: Stage 3 boundary (Tao 2015 plane)

This module is **Conjectures-only** glue.

Stage 2 produces a fixed-step unboundedness witness for the reduced sequence `g` (at step `d`),
plus a transport lemma back to an *offset discrepancy* witness for the original sequence `f`.

Stage 3 is the boundary where we finally discharge the global goal `¬ BoundedDiscrepancy f`.

Design goal: keep the interface small and typed; avoid sprinkling ad-hoc “unboundedness → not bounded”
lemmas throughout the codebase.
-/

namespace MoltResearch

namespace Tao2015

/-- Output of Stage 3 of the Track C pipeline.

We keep the full Stage-2 output for traceability, and package the global conclusion
`¬ BoundedDiscrepancy f` as the consumer-facing end of the Conjectures-only plane.
-/
structure Stage3Output (f : ℕ → ℤ) : Type where
  out2 : Tao2015.Stage2Output f
  notBounded : ¬ BoundedDiscrepancy f

namespace Stage3Output

variable {f : ℕ → ℤ}

/-- Deterministic Stage-3 completion: a Stage-2 output already contains enough information to
contradict any global boundedness hypothesis.

This is the main “stage boundary” lemma: it is *proved* (no `sorry`) and should remain stable.
-/
def ofStage2Output (out2 : Tao2015.Stage2Output f) : Stage3Output f := by
  refine ⟨out2, ?_⟩
  -- Stage 2 gives unbounded offset discrepancy witnesses for the original sequence.
  -- The Stage-1 reduction output has the generic lemma that this implies global unboundedness.
  exact
    out2.out1.not_boundedDiscrepancy_of_forall_exists_discOffset_gt (f := f)
      (out2.forall_exists_discOffset_gt (f := f))

end Stage3Output

/-!
## Stage 3 conjecture stub

This is the “single entry point” version of Stage 3: from a sign sequence, produce a Stage-3
output.

It is still a conjecture stub only because Stage 2 is a conjecture stub.
-/

noncomputable def stage3 (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage3Output f := by
  -- Run Stage 2, then close the global goal via the proved boundary lemma.
  exact (Stage3Output.ofStage2Output (f := f) (Tao2015.stage2 (f := f) (hf := hf)))

end Tao2015

end MoltResearch
