import MoltResearch.Discrepancy

/-!
A conjecture-style stub for the Erdős discrepancy theorem (Tao 2015).

This file may contain `sorry` (backlog only). Verified, reusable definitions belong in `MoltResearch/`.
-/

namespace MoltResearch

/-- Trivial base case: any sign sequence has discrepancy at least 0. -/
theorem erdos_discrepancy_zero (f : ℕ → ℤ) (hf : IsSignSequence f) :
    HasDiscrepancyAtLeast f 0 := by
  simpa using IsSignSequence.hasDiscrepancyAtLeast_zero (hf := hf)

/-- Erdős discrepancy theorem.

Every ±1 sequence has unbounded discrepancy on homogeneous arithmetic progressions.

This is a long-horizon target for the repo; we start by building the definition + lemma substrate.
-/
theorem erdos_discrepancy (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  sorry

/-- Surface form of `erdos_discrepancy`, matching the usual notation `∑_{i=1}^n f (i*d)`.

This is a thin wrapper around the nucleus predicate `HasDiscrepancyAtLeast`, via
`forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc`.
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
