import Conjectures.C0002_erdos_discrepancy.src.TrackCStage4Core

/-!
# Track C — Stage 4 proof file (derived wrappers)

Stage 4 is meant to stay API + wiring. This file collects the derived witness-form wrappers that
are convenient for downstream analytic stages.

Current policy: keep the Stage-4 boundary core minimal; put these wrappers here.
-/

namespace MoltResearch
namespace Tao2015

namespace Stage4Output

variable {f : ℕ → ℤ}

/-- Stage 4 output yields unboundedness of the bundled offset discrepancy family at the concrete
Stage-2 parameters carried by Stage 4.

This is a thin wrapper around the proved Stage-2 core lemma `Stage2Output.unboundedDiscOffset`.
-/
theorem unboundedDiscOffset (out : Stage4Output f) :
    UnboundedDiscOffset f out.out2.d out.out2.m := by
  simpa using (out.out2.unboundedDiscOffset (f := f))

/-- Negation-normal-form packaging of Stage-4 offset unboundedness:
`¬ ∃ B, ∀ n, discOffset f out.out2.d out.out2.m n ≤ B`.

This is a thin wrapper around the equivalence
`unboundedDiscOffset_iff_not_exists_forall_discOffset_le`.
-/
theorem not_exists_forall_discOffset_le (out : Stage4Output f) :
    ¬ ∃ B : ℕ, ∀ n : ℕ, discOffset f out.out2.d out.out2.m n ≤ B := by
  have hunb : UnboundedDiscOffset f out.out2.d out.out2.m := out.unboundedDiscOffset (f := f)
  exact
    (unboundedDiscOffset_iff_not_exists_forall_discOffset_le (f := f)
          (d := out.out2.d) (m := out.out2.m)).1
      hunb

/-- Stable boundedness-negation packaging of Stage-4 offset unboundedness:
`¬ ∃ B, BoundedDiscOffset f out.out2.d out.out2.m B`.

This is a thin wrapper around the bridge equivalence
`unboundedDiscOffset_iff_not_exists_boundedDiscOffset`.
-/
theorem not_exists_boundedDiscOffset (out : Stage4Output f) :
    ¬ ∃ B : ℕ, BoundedDiscOffset f out.out2.d out.out2.m B := by
  have hunb : UnboundedDiscOffset f out.out2.d out.out2.m := out.unboundedDiscOffset (f := f)
  exact
    (unboundedDiscOffset_iff_not_exists_boundedDiscOffset (f := f)
          (d := out.out2.d) (m := out.out2.m)).1
      hunb

/-- Negation-normal-form packaging of Stage-4 offset unboundedness at the raw nucleus level:
`¬ ∃ B, ∀ n, Int.natAbs (apSumOffset f out.out2.d out.out2.m n) ≤ B`.

This is `not_exists_forall_discOffset_le` rewritten by unfolding `discOffset`.
-/
theorem not_exists_forall_natAbs_apSumOffset_le (out : Stage4Output f) :
    ¬ ∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumOffset f out.out2.d out.out2.m n) ≤ B := by
  have hunb : UnboundedDiscOffset f out.out2.d out.out2.m := out.unboundedDiscOffset (f := f)
  exact
    (UnboundedDiscOffset.iff_not_exists_forall_natAbs_apSumOffset_le (f := f)
          (d := out.out2.d) (m := out.out2.m)).1
      hunb

/-- Existential packaging: Stage 4 yields concrete Stage-2 parameters `d, m` (with `1 ≤ d`) such
that the bundled offset discrepancy family `discOffset f d m` is unbounded.

This is a tiny wrapper around `unboundedDiscOffset` together with the proved side condition
`Stage2Output.one_le_d` carried by `out.out2`.
-/
theorem exists_params_one_le_unboundedDiscOffset (out : Stage4Output f) :
    ∃ d m : ℕ, 1 ≤ d ∧ UnboundedDiscOffset f d m := by
  refine ⟨out.out2.d, out.out2.m, out.out2.one_le_d (f := f), ?_⟩
  simpa using out.unboundedDiscOffset (f := f)

/-- Positive-length witness form: Stage 4 yields arbitrarily large bundled offset discrepancies
`discOffset f out.out2.d out.out2.m n`, with witnesses `n > 0`.

This is a thin wrapper around the proved Stage-2 output lemma
`Stage2Output.forall_exists_discOffset_gt'_witness_pos`.
-/
theorem forall_exists_discOffset_gt'_witness_pos (out : Stage4Output f) :
    ∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ discOffset f out.out2.d out.out2.m n > B := by
  simpa using (out.out2.forall_exists_discOffset_gt'_witness_pos (f := f))

/-- Stage 4 output implies the nucleus witness form

`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is the most pipeline-friendly surface statement: it avoids `discrepancy` and goes straight to
the nucleus `apSum`.
-/
theorem forall_exists_d_ge_one_witness_pos (out : Stage4Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_d_ge_one_witness_pos f).1
      (out.forall_hasDiscrepancyAtLeast (f := f))

/-- Variant of `forall_exists_d_ge_one_witness_pos` with the step-size condition written as
`d > 0`.

This is sometimes a more convenient normal form when downstream stages naturally assume `d ≠ 0`
(or use lemmas phrased with strict positivity).
-/
theorem forall_exists_d_pos_witness_pos (out : Stage4Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  intro C
  rcases out.forall_exists_d_ge_one_witness_pos (f := f) C with ⟨d, n, hd, hn, hw⟩
  refine ⟨d, n, ?_, hn, hw⟩
  exact lt_of_lt_of_le Nat.zero_lt_one hd

/-- Variant of `forall_exists_d_pos_witness_pos` with the step-size condition written as `d ≠ 0`. -/
theorem forall_exists_d_ne_zero_witness_pos (out : Stage4Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≠ 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  intro C
  rcases out.forall_exists_d_pos_witness_pos (f := f) C with ⟨d, n, hd, hn, hw⟩
  exact ⟨d, n, Nat.ne_of_gt hd, hn, hw⟩

/-- Stage 4 output implies the explicit discrepancy witness normal form

`∀ C, ∃ d n, d > 0 ∧ discrepancy f d n > C`.

This is a thin wrapper around `forall_hasDiscrepancyAtLeast` via
`HasDiscrepancyAtLeast_iff_exists_discrepancy`.
-/
theorem forall_exists_discrepancy_gt (out : Stage4Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ discrepancy f d n > C := by
  intro C
  exact
    (HasDiscrepancyAtLeast_iff_exists_discrepancy (f := f) (C := C)).1
      (out.forall_hasDiscrepancyAtLeast (f := f) C)

/-- Strengthened witness form of `forall_exists_discrepancy_gt` with a positive-length witness.

This is sometimes convenient when downstream stages want to rule out the degenerate case `n = 0`.
-/
theorem forall_exists_discrepancy_gt_witness_pos (out : Stage4Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ discrepancy f d n > C := by
  intro C
  rcases out.forall_exists_d_pos_witness_pos (f := f) C with ⟨d, n, hd, hn, hw⟩
  refine ⟨d, n, hd, hn, ?_⟩
  -- `discrepancy f d n` is definitionally `Int.natAbs (apSum f d n)`.
  change Int.natAbs (apSum f d n) > C
  exact hw

/-- Stage 4 output implies the paper-notation witness form

`∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ Int.natAbs (∑ i ∈ Icc 1 n, f (i*d)) > C`.

This is a thin wrapper around `forall_hasDiscrepancyAtLeast` via
`forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos`.
-/
theorem forall_exists_sum_Icc_witness_pos (out : Stage4Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧
      Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos f).1
      (out.forall_hasDiscrepancyAtLeast (f := f))

/-- Variant of `forall_exists_sum_Icc_witness_pos` writing the step-size side condition as
`d ≥ 1`.

This is often the most readable paper-notation witness form when `d : ℕ`.
-/
theorem forall_exists_sum_Icc_d_ge_one_witness_pos (out : Stage4Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧
      Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos f).1
      (out.forall_hasDiscrepancyAtLeast (f := f))

end Stage4Output

/-- Consumer-facing shortcut: Stage 4 yields unboundedness of the bundled offset discrepancy family
at the deterministic parameters produced by the Stage-4 output.
-/
theorem stage4_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    UnboundedDiscOffset f
      (stage4Out (f := f) (hf := hf)).out2.d
      (stage4Out (f := f) (hf := hf)).out2.m := by
  simpa using (stage4Out (f := f) (hf := hf)).unboundedDiscOffset (f := f)

/-- Consumer-facing shortcut: stable boundedness-negation normal form of `stage4_unboundedDiscOffset`.

Normal form:
`¬ ∃ B, BoundedDiscOffset f (stage4Out ...).out2.d (stage4Out ...).out2.m B`.
-/
theorem stage4_not_exists_boundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ,
      BoundedDiscOffset f
        (stage4Out (f := f) (hf := hf)).out2.d
        (stage4Out (f := f) (hf := hf)).out2.m B := by
  simpa using (stage4Out (f := f) (hf := hf)).not_exists_boundedDiscOffset (f := f)

/-- Consumer-facing shortcut: Stage 4 yields concrete Stage-2 parameters `d, m` (with `1 ≤ d`) such
that the bundled offset discrepancy family `discOffset f d m` is unbounded.

This is the existential packaging of `stage4_unboundedDiscOffset`.
-/
theorem stage4_exists_params_one_le_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ UnboundedDiscOffset f d m := by
  simpa using
    (stage4Out (f := f) (hf := hf)).exists_params_one_le_unboundedDiscOffset (f := f)

/-- Consumer-facing shortcut: Stage 4 yields the nucleus witness form

`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is the most pipeline-friendly surface statement for consuming Stage 4.
-/
theorem stage4_forall_exists_d_ge_one_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact (stage4Out (f := f) (hf := hf)).forall_exists_d_ge_one_witness_pos (f := f)

/-- Consumer-facing shortcut: Stage 4 yields the nucleus witness form with strict positivity for
`d`.

Normal form:
`∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.
-/
theorem stage4_forall_exists_d_pos_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact (stage4Out (f := f) (hf := hf)).forall_exists_d_pos_witness_pos (f := f)

/-- Variant of `stage4_forall_exists_d_pos_witness_pos` with the step-size condition written as
`d ≠ 0`.
-/
theorem stage4_forall_exists_d_ne_zero_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≠ 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact (stage4Out (f := f) (hf := hf)).forall_exists_d_ne_zero_witness_pos (f := f)

/-- Consumer-facing shortcut: Stage 4 yields explicit discrepancy witnesses

`∀ C, ∃ d n, d > 0 ∧ discrepancy f d n > C`.

This is the witness-form normal form of `stage4_forall_hasDiscrepancyAtLeast`.
-/
theorem stage4_forall_exists_discrepancy_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ discrepancy f d n > C := by
  exact (stage4Out (f := f) (hf := hf)).forall_exists_discrepancy_gt (f := f)

/-- Strengthened witness form of `stage4_forall_exists_discrepancy_gt` with a positive-length witness.

This is sometimes convenient when downstream stages want to rule out the degenerate case `n = 0`.
-/
theorem stage4_forall_exists_discrepancy_gt_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ discrepancy f d n > C := by
  exact (stage4Out (f := f) (hf := hf)).forall_exists_discrepancy_gt_witness_pos (f := f)

/-- Consumer-facing shortcut: Stage 4 yields the paper-notation witness form

`∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ Int.natAbs (∑ i ∈ Icc 1 n, f (i*d)) > C`.

This is a thin wrapper around `Stage4Output.forall_exists_sum_Icc_witness_pos`.
-/
theorem stage4_forall_exists_sum_Icc_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧
      Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  exact (stage4Out (f := f) (hf := hf)).forall_exists_sum_Icc_witness_pos (f := f)

/-- Variant of `stage4_forall_exists_sum_Icc_witness_pos` writing the step-size side condition as
`d ≥ 1`.

This is often the most readable surface form when `d : ℕ`.
-/
theorem stage4_forall_exists_sum_Icc_d_ge_one_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧
      Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  exact (stage4Out (f := f) (hf := hf)).forall_exists_sum_Icc_d_ge_one_witness_pos (f := f)

end Tao2015
end MoltResearch
