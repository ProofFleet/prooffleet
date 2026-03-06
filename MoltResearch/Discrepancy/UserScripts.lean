import MoltResearch.Discrepancy

/-!
# Discrepancy: typical “paper → normal form” user scripts

These are deliberately tiny examples meant to look like what a user does after reading a paper
statement:

- start from an `Icc` sum (or a difference of such sums),
- normalize into the stable-surface wrappers `apSumOffset` / `discOffset`,
- discharge the goal with a single `simpa`/`rw` pipeline.

This file imports only the stable surface `MoltResearch.Discrepancy`.
-/

namespace MoltResearch

section UserScripts

variable (f : ℕ → ℤ) (a d m n C : ℕ)

-- 1) Paper tail sum bound (`Icc (m+1) (m+n)`) → `discOffset` bound.
example
    (h : Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) ≤ C) :
    discOffset f d m n ≤ C := by
  simpa using h

-- 2) Paper difference of affine partial sums → `discOffset` of an offset tail on a shifted sequence.
example
    (h : Int.natAbs (apSumFrom f a d (m + n) - apSumFrom f a d m) ≤ C) :
    discOffset (fun k => f (k + a)) d m n ≤ C := by
  simpa [apSumFrom_sub_eq_apSumOffset_shift_add] using h

-- 3) Paper difference of paper affine sums → `discOffset` (paper → nucleus → tail → offset).
example
    (h :
        Int.natAbs
            ((Finset.Icc 1 (m + n)).sum (fun i => f (a + i * d)) -
              (Finset.Icc 1 m).sum (fun i => f (a + i * d))) ≤
          C) :
    discOffset (fun k => f (k + a)) d m n ≤ C := by
  -- First: paper sums → affine nucleus (`apSumFrom`).
  have h' : Int.natAbs (apSumFrom f a d (m + n) - apSumFrom f a d m) ≤ C := by
    simpa [sum_Icc_eq_apSumFrom] using h
  -- Then: affine difference → offset tail on the shifted sequence.
  have h'' : Int.natAbs (apSumOffset (fun k => f (k + a)) d m n) ≤ C := by
    simpa [apSumFrom_sub_eq_apSumOffset_shift_add] using h'
  -- Finally: repackage `Int.natAbs (apSumOffset …)` as `discOffset …`.
  change Int.natAbs (apSumOffset (fun k => f (k + a)) d m n) ≤ C
  exact h''

end UserScripts

end MoltResearch
