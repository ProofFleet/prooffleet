import MoltResearch.Discrepancy.Basic

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
/-- If we can beat every bound by one, we can beat every bound. -/
theorem erdos_discrepancy_of_succ (f : ℕ → ℤ) :
    (∀ C : ℕ, HasDiscrepancyAtLeast f (C + 1)) → (∀ C : ℕ, HasDiscrepancyAtLeast f C) := by
  intro h C
  exact HasDiscrepancyAtLeast.of_succ (h C)

theorem erdos_discrepancy (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  sorry

end MoltResearch
