import MoltResearch.Discrepancy
import Conjectures.C0002_erdos_discrepancy.src.Tao2015
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage1Examples
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2

/-!
A conjecture-style stub for the Erdős discrepancy theorem (Tao 2015).

This file may contain `sorry` (backlog only). Verified, reusable definitions belong in `MoltResearch/`.
-/

namespace MoltResearch

/-- Trivial base case: any sign sequence has discrepancy at least 0. -/
theorem erdos_discrepancy_zero (f : ℕ → ℤ) (hf : IsSignSequence f) :
    HasDiscrepancyAtLeast f 0 := by
  simpa using IsSignSequence.hasDiscrepancyAtLeast_zero (hf := hf)

-- Tao 2015 proof skeleton lives in `Conjectures.C0002_erdos_discrepancy.src.Tao2015`.

/-- Erdős discrepancy theorem.

Every ±1 sequence has unbounded discrepancy on homogeneous arithmetic progressions.

In this file we derive the usual `∀ C, HasDiscrepancyAtLeast f C` statement from the single
boundedness-negation normal form `¬ BoundedDiscrepancy f`.
-/
theorem erdos_discrepancy (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  -- Quantifier-level normalization: `∀ C, ...` ↔ `¬BoundedDiscrepancy`.
  refine (forall_hasDiscrepancyAtLeast_iff_not_boundedDiscrepancy f).2 ?_
  exact tao2015_not_boundedDiscrepancy (f := f) (hf := hf)

/-- Witness form of `erdos_discrepancy` directly in terms of the nucleus `apSum`.

This is the most pipeline-friendly surface statement:
`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ |apSum f d n| > C`.
-/
theorem erdos_discrepancy_apSum (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_d_ge_one_witness_pos f).1
      (erdos_discrepancy (f := f) (hf := hf))

/-- Paper-notation surface form of `erdos_discrepancy`, matching `∑_{i=1}^n f (i*d)`.

This is a thin wrapper around `erdos_discrepancy_apSum`, via
`forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos`.
-/
theorem erdos_discrepancy_sum_Icc (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧
      Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos f).1
      (erdos_discrepancy (f := f) (hf := hf))

/-- Variant of `erdos_discrepancy_sum_Icc` writing the step-size side condition as `d ≥ 1`.

This is often the most readable surface form when `d : ℕ`.
-/
theorem erdos_discrepancy_sum_Icc_d_ge_one (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧
      Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos f).1
      (erdos_discrepancy (f := f) (hf := hf))

end MoltResearch
