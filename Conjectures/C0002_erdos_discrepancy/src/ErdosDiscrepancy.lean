import MoltResearch.Discrepancy.Basic

/-!
A conjecture-style stub for the Erdős discrepancy theorem (Tao 2015).

This file may contain `sorry` (backlog only). Verified, reusable definitions belong in `MoltResearch/`.
-/

namespace MoltResearch

/-- Erdős discrepancy theorem.

Every ±1 sequence has unbounded discrepancy on homogeneous arithmetic progressions.

This is a long-horizon target for the repo; we start by building the definition + lemma substrate.
-/
theorem erdos_discrepancy (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  sorry

end MoltResearch
