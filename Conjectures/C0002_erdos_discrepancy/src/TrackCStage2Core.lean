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

/-!
## Stage-2 minimal projections

These are the small, proved projections off `Tao2015.Stage2Output` that downstream stages use
frequently.

We keep them in this core file so consumers can avoid importing the much larger library of
Stage-2 convenience lemmas in `TrackCStage2Output.lean`.
-/

/-- Convenience projection: the reduced step size. -/
abbrev d (out : Stage2Output f) : ℕ := out.out1.d

/-- Convenience projection: the reduced sequence. -/
abbrev g (out : Stage2Output f) : ℕ → ℤ := out.out1.g

/-- The reduced sequence packaged by Stage 2 is a sign sequence. -/
theorem hg (out : Stage2Output f) : IsSignSequence out.g := by
  simpa [Stage2Output.g] using out.out1.hg

/-- Convenience projection: the offset parameter bundled in Stage 1. -/
abbrev m (out : Stage2Output f) : ℕ := out.out1.m

/-- Rewrite for the reduced sequence produced by Stage 2: it is a shift by `m*d`. -/
theorem g_eq (out : Stage2Output f) (k : ℕ) :
    out.g k = f (k + out.m * out.d) := by
  simpa [Stage2Output.g, Stage2Output.m, Stage2Output.d] using out.out1.g_eq k

/-- Convenience projection: positivity of the reduced step size. -/
abbrev hd (out : Stage2Output f) : out.d > 0 := out.out1.hd

/-- Convenience lemma: the reduced step size is nonzero. -/
theorem d_ne_zero (out : Stage2Output f) : out.d ≠ 0 := by
  exact Nat.ne_of_gt out.hd

/-- Convenience lemma: the reduced step size is at least `1`. -/
theorem one_le_d (out : Stage2Output f) : 1 ≤ out.d := by
  -- `out.hd` is `0 < out.d`.
  simpa using (Nat.succ_le_iff).2 out.hd

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

/-- Variant of `forall_exists_d_ge_one_witness_pos` with the step-size condition written as `d > 0`.

This is sometimes a more convenient normal form when the next stage naturally assumes `d ≠ 0`
(or uses lemmas phrased with strict positivity).
-/
theorem forall_exists_d_pos_witness_pos (out : Stage2Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  intro C
  rcases out.forall_exists_d_ge_one_witness_pos (f := f) C with ⟨d, n, hd, hn, hw⟩
  refine ⟨d, n, ?_, hn, hw⟩
  exact lt_of_lt_of_le Nat.zero_lt_one hd

end Stage2Output

end Tao2015

end MoltResearch
