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

-- 3) Paper difference of paper affine sums → `discOffset` (difference → tail → offset).
example
    (h :
        Int.natAbs
            ((Finset.Icc 1 (m + n)).sum (fun i => f (a + i * d)) -
              (Finset.Icc 1 m).sum (fun i => f (a + i * d))) ≤
          C) :
    discOffset (fun k => f (k + a)) d m n ≤ C := by
  -- Avoid `simp` loops by rewriting the goal to the underlying `Int.natAbs (apSumOffset …)` form.
  change Int.natAbs (apSumOffset (fun k => f (k + a)) d m n) ≤ C
  simpa [sum_Icc_eq_apSumFrom, apSumFrom_sub_eq_apSumOffset_shift_add] using h

-- 3b) Same as (3), but with the affine summand written in mul-left form `a + d*i`.
example
    (h :
        Int.natAbs
            ((Finset.Icc 1 (m + n)).sum (fun i => f (a + d * i)) -
              (Finset.Icc 1 m).sum (fun i => f (a + d * i))) ≤
          C) :
    discOffset (fun k => f (k + a)) d m n ≤ C := by
  -- First normalize the mul-left summand into the `i * d` convention.
  have h' :
      Int.natAbs
          ((Finset.Icc 1 (m + n)).sum (fun i => f (a + i * d)) -
            (Finset.Icc 1 m).sum (fun i => f (a + i * d))) ≤
        C := by
    simpa [Nat.mul_comm] using h
  change Int.natAbs (apSumOffset (fun k => f (k + a)) d m n) ≤ C
  simpa [sum_Icc_eq_apSumFrom, apSumFrom_sub_eq_apSumOffset_shift_add] using h'

-- 4) Paper tail sum with translation-friendly summand `i*d + a` → `discOffset` bound.
example
    (h : Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d + a))) ≤ C) :
    discOffset (fun k => f (k + a)) d m n ≤ C := by
  -- Avoid `simp` loops by rewriting the goal to the underlying `Int.natAbs (apSumOffset …)` form.
  change Int.natAbs (apSumOffset (fun k => f (k + a)) d m n) ≤ C
  simpa [sum_Icc_eq_apSumFrom_tail_add, apSumFrom_tail_eq_apSumOffset_shift_add_left] using h

-- 5) Paper tail sum with affine endpoints (`hmn : m ≤ n`) → `discOffset` bound.
example (hmn : m ≤ n)
    (h : Int.natAbs ((Finset.Icc (m + 1) n).sum (fun i => f (a + i * d))) ≤ C) :
    discOffset (fun k => f (a + k)) d m (n - m) ≤ C := by
  change Int.natAbs (apSumOffset (fun k => f (a + k)) d m (n - m)) ≤ C
  simpa [
    sum_Icc_eq_apSumOffset_of_le_affineEndpoints (f := f) (a := a) (d := d) (m := m) (n := n) hmn] using h

-- 5b) Same as (5), but with the summand written as `a + d*i` (mul-left convention).
example (hmn : m ≤ n)
    (h : Int.natAbs ((Finset.Icc (m + 1) n).sum (fun i => f (a + d * i))) ≤ C) :
    discOffset (fun k => f (a + k)) d m (n - m) ≤ C := by
  change Int.natAbs (apSumOffset (fun k => f (a + k)) d m (n - m)) ≤ C
  simpa [
    sum_Icc_eq_apSumOffset_of_le_affineEndpoints_mul_left (f := f) (a := a) (d := d) (m := m) (n := n) hmn] using h

-- 6) Difference of affine partial sums (`hmn : m ≤ n`) → `discOffset` bound.
example (hmn : m ≤ n)
    (h : Int.natAbs (apSumFrom f a d n - apSumFrom f a d m) ≤ C) :
    discOffset (fun k => f (a + k)) d m (n - m) ≤ C := by
  change Int.natAbs (apSumOffset (fun k => f (a + k)) d m (n - m)) ≤ C
  simpa [
    apSumFrom_sub_apSumFrom_eq_apSumOffset_shift (f := f) (a := a) (d := d) (m := m) (n := n) hmn] using h

-- 7) Paper difference of *paper* affine sums with affine endpoints (`hmn : m ≤ n`).
--
-- Normalize the paper statement directly into the stable-surface offset wrapper.
example (hmn : m ≤ n)
    (h :
        Int.natAbs
            ((Finset.Icc 1 n).sum (fun i => f (a + i * d)) -
              (Finset.Icc 1 m).sum (fun i => f (a + i * d))) ≤
          C) :
    discOffset (fun k => f (a + k)) d m (n - m) ≤ C := by
  -- Avoid `simp` loops by rewriting the goal to the underlying `Int.natAbs (apSumOffset …)` form.
  change Int.natAbs (apSumOffset (fun k => f (a + k)) d m (n - m)) ≤ C
  -- paper → nucleus (`apSumFrom`), then difference → offset tail.
  simpa [sum_Icc_eq_apSumFrom,
    apSumFrom_sub_apSumFrom_eq_apSumOffset_shift (f := f) (a := a) (d := d) (m := m) (n := n) hmn] using h

-- 7b) Same as (7), but with mul-left convention `a + d*i` in the paper statement.
example (hmn : m ≤ n)
    (h :
        Int.natAbs
            ((Finset.Icc 1 n).sum (fun i => f (a + d * i)) -
              (Finset.Icc 1 m).sum (fun i => f (a + d * i))) ≤
          C) :
    discOffset (fun k => f (a + k)) d m (n - m) ≤ C := by
  change Int.natAbs (apSumOffset (fun k => f (a + k)) d m (n - m)) ≤ C
  -- Normalize the paper mul-left summand `a + d*i` into the canonical `i*d` convention.
  have h' :
      Int.natAbs
          ((Finset.Icc 1 n).sum (fun i => f (a + i * d)) -
            (Finset.Icc 1 m).sum (fun i => f (a + i * d))) ≤
        C := by
    simpa [Nat.mul_comm] using h
  simpa [sum_Icc_eq_apSumFrom,
    apSumFrom_sub_apSumFrom_eq_apSumOffset_shift (f := f) (a := a) (d := d) (m := m) (n := n) hmn] using h'

-- 8) Paper tail sum with translation-friendly summand `i*d + a` → `discOffset` bound.
--
-- This is a one-liner once you use the simp-friendly alias
-- `sum_Icc_eq_apSumOffset_of_le_shift_add_len`.
example
    (h : Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d + a))) ≤ C) :
    discOffset (fun k => f (k + a)) d m n ≤ C := by
  change Int.natAbs (apSumOffset (fun k => f (k + a)) d m n) ≤ C
  simpa [sum_Icc_eq_apSumOffset_of_le_shift_add_len] using h

-- 8b) Same as (8) but with the summand written as `d*i + a` (mul-left convention).
example
    (h : Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i + a))) ≤ C) :
    discOffset (fun k => f (k + a)) d m n ≤ C := by
  change Int.natAbs (apSumOffset (fun k => f (k + a)) d m n) ≤ C
  simpa [sum_Icc_eq_apSumOffset_of_le_shift_add_len_mul_left] using h

-- 9) Same normalization as (8), but landing directly in the `apSumOffset` API.
example
    (h : Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d + a))) ≤ C) :
    Int.natAbs (apSumOffset (fun k => f (k + a)) d m n) ≤ C := by
  simpa [sum_Icc_eq_apSumOffset_of_le_shift_add_len] using h

-- 10) Difference of two Icc sums → `discOffset` of the tail
-- (using `sum_Icc_sub_sum_Icc_eq_apSumOffset`).
example (n₁ n₂ : ℕ)
    (h :
        Int.natAbs
            ((Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d)) -
              (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d))) ≤ C) :
    discOffset f d (m + n₁) n₂ ≤ C := by
  have hx :
      (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d)) -
          (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d)) =
        apSumOffset f d (m + n₁) n₂ := by
    simpa using
      (sum_Icc_sub_sum_Icc_eq_apSumOffset (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))
  have h' := h
  rw [hx] at h'
  simpa using h'

-- 10b) Same as (10) but with the mul-left convention `d * i`.
example (n₁ n₂ : ℕ)
    (h :
        Int.natAbs
            ((Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (d * i)) -
              (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (d * i))) ≤ C) :
    discOffset f d (m + n₁) n₂ ≤ C := by
  have hx :
      (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (d * i)) -
          (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (d * i)) =
        apSumOffset f d (m + n₁) n₂ := by
    simpa using
      (sum_Icc_sub_sum_Icc_eq_apSumOffset_mul_left (f := f) (d := d) (m := m) (n₁ := n₁)
        (n₂ := n₂))
  have h' := h
  rw [hx] at h'
  simpa using h'

-- 11) Affine-endpoint tail sum → `discOffset` in a single `simpa` (no manual `change`).
example (hmn : m ≤ n)
    (h : Int.natAbs ((Finset.Icc (m + 1) n).sum (fun i => f (a + i * d))) ≤ C) :
    discOffset (fun k => f (a + k)) d m (n - m) ≤ C := by
  simpa [sum_Icc_eq_apSumOffset_of_le_affineEndpoints (f := f) (a := a) (d := d)
      (m := m) (n := n) hmn] using h

-- 12) Affine-endpoint tail sum with translation-friendly summand `i*d + a` → `discOffset`.
example (hmn : m ≤ n)
    (h : Int.natAbs ((Finset.Icc (m + 1) n).sum (fun i => f (i * d + a))) ≤ C) :
    discOffset (fun k => f (k + a)) d m (n - m) ≤ C := by
  simpa [sum_Icc_eq_apSumOffset_of_le_shift_add (f := f) (a := a) (d := d)
      (m := m) (n := n) hmn] using h

-- 13) Difference of two paper tail sums → `discOffset` of the tail.
example (n₁ n₂ : ℕ)
    (h :
        Int.natAbs
            ((Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d)) -
              (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d))) ≤
          C) :
    discOffset f d (m + n₁) n₂ ≤ C := by
  -- Use a `rw` rewrite on the whole difference to avoid simp rewriting each summand separately.
  have h' := h
  rw [sum_Icc_sub_sum_Icc_eq_apSumOffset (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)] at h'
  -- Let `simp` rewrite `Int.natAbs (apSumOffset …)` to the `discOffset` wrapper.
  simpa using h'

-- 14) Paper difference of affine partial sums with affine endpoints → `discOffset` (single `simpa`).
example (hmn : m ≤ n)
    (h :
        Int.natAbs
            ((Finset.Icc 1 n).sum (fun i => f (a + i * d)) -
              (Finset.Icc 1 m).sum (fun i => f (a + i * d))) ≤
          C) :
    discOffset (fun k => f (a + k)) d m (n - m) ≤ C := by
  simpa [sum_Icc_eq_apSumFrom,
    apSumFrom_sub_apSumFrom_eq_apSumOffset_shift (f := f) (a := a) (d := d) (m := m) (n := n) hmn] using h

end UserScripts

end MoltResearch
