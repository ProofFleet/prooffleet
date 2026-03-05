import MoltResearch.Discrepancy.Basic

/-!
# Discrepancy: bounded vs unbounded (quantifier normal forms)

This file packages the common “unbounded discrepancy” statement

`∀ C, HasDiscrepancyAtLeast f C`

as the negation of a single boundedness predicate.

These lemmas are logically elementary, but they are high‑leverage glue for composing
conjecture stubs (e.g. routing a paper theorem stated as “not bounded” into our nucleus
predicate `HasDiscrepancyAtLeast`).
-/

namespace MoltResearch

/-- `f` has *bounded discrepancy* if there is a uniform bound on all homogeneous AP partial sums.

This is the natural negation‑normal form of the Erdős discrepancy statement.
-/
def BoundedDiscrepancy (f : ℕ → ℤ) : Prop :=
  ∃ B : ℕ, ∀ d n : ℕ, d > 0 → Int.natAbs (apSum f d n) ≤ B

/-- Quantifier-level normal form: unbounded discrepancy is the negation of `BoundedDiscrepancy`.

This is classical in the `¬BoundedDiscrepancy → ∀ C, ...` direction (it is not possible to
construct witnesses from a purely negative hypothesis).
-/
theorem forall_hasDiscrepancyAtLeast_iff_not_boundedDiscrepancy (f : ℕ → ℤ) :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔ ¬ BoundedDiscrepancy f := by
  classical
  constructor
  · intro hunb hb
    rcases hb with ⟨B, hB⟩
    rcases hunb B with ⟨d, n, hd, hgt⟩
    exact (not_le_of_gt hgt) (hB d n hd)
  · intro hnb C
    by_contra hC
    have hB : ∀ d n : ℕ, d > 0 → Int.natAbs (apSum f d n) ≤ C := by
      intro d n hd
      have hnotgt : ¬ Int.natAbs (apSum f d n) > C := by
        intro hgt
        exact hC ⟨d, n, hd, hgt⟩
      exact le_of_not_gt hnotgt
    exact hnb ⟨C, hB⟩

end MoltResearch
