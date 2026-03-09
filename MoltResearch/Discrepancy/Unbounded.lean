import MoltResearch.Discrepancy.Reindex

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

/-!
## Closure properties

These are small, kernel-checked “reduction steps” that appear in many discrepancy arguments:
if you can control discrepancy for `f`, you can control it for simple transforms of `f`.

They are also useful for proving contrapositive-style statements:
unbounded discrepancy of a derived sequence implies unbounded discrepancy of the original.
-/

/-- Bounded discrepancy is stable under dilation of the input (`n ↦ n * k`).

Concretely, if `f` has uniformly bounded discrepancy, then so does `n ↦ f (n*k)`.
-/
theorem BoundedDiscrepancy.map_mul {f : ℕ → ℤ} (hb : BoundedDiscrepancy f) {k : ℕ} (hk : k > 0) :
    BoundedDiscrepancy (fun n => f (n * k)) := by
  rcases hb with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro d n hd
  -- `apSum (fun n => f (n*k)) d n = apSum f (d*k) n`.
  simpa [apSum_map_mul] using hB (d * k) n (Nat.mul_pos hd hk)

/-- Contrapositive form of `BoundedDiscrepancy.map_mul`.

If a dilated sequence `n ↦ f (n*k)` has unbounded discrepancy, then so does `f`.
-/
theorem not_boundedDiscrepancy_of_not_boundedDiscrepancy_map_mul {f : ℕ → ℤ} {k : ℕ} (hk : k > 0)
    (hnb : ¬ BoundedDiscrepancy (fun n => f (n * k))) : ¬ BoundedDiscrepancy f := by
  intro hb
  exact hnb (BoundedDiscrepancy.map_mul (f := f) hb hk)

end MoltResearch
