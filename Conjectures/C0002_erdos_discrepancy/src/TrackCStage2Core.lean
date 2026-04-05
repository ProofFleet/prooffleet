import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Boundary

/-!
# Track C: Stage 2 core lemmas (Tao 2015 plane)

This file is intentionally tiny.

It contains the minimal proved lemmas about `Tao2015.Stage2Output` needed by later stages to
close the global goal `¬ BoundedDiscrepancy f`.

Design note: Track C's hard-gate build for
`Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy`
should not need to compile the full library of Stage-2 convenience lemmas.
-/

namespace MoltResearch

namespace Tao2015

namespace Stage2Output

variable {f : ℕ → ℤ}

/-- Consumer-facing form: Stage 2 implies global unbounded discrepancy for the original sequence.

This is the minimal “bridge back to the main theorem statement” lemma: it packages the fact that
Stage 2 gives unbounded discrepancy along the reduced sequence, and uses the Stage-1 contract
carried by `out.out1` to conclude `¬ BoundedDiscrepancy f`.
-/
theorem notBoundedOriginal (out : Stage2Output f) : ¬ BoundedDiscrepancy f := by
  exact out.out1.not_boundedDiscrepancy_of_unboundedDiscrepancyAlong (f := f) out.unbounded

/-- Stage 2 output implies the usual surface statement `∀ C, HasDiscrepancyAtLeast f C`.

This is a thin wrapper around `notBoundedOriginal`.
-/
theorem forall_hasDiscrepancyAtLeast (out : Stage2Output f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  refine (forall_hasDiscrepancyAtLeast_iff_not_boundedDiscrepancy f).2 ?_
  exact out.notBoundedOriginal (f := f)

/-- Stage 2 output implies the nucleus witness form

`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is the most pipeline-friendly surface statement for consuming Stage 2 without going through
Stage 3.
-/
theorem forall_exists_d_ge_one_witness_pos (out : Stage2Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_d_ge_one_witness_pos f).1
      (out.forall_hasDiscrepancyAtLeast (f := f))

end Stage2Output

end Tao2015

end MoltResearch
