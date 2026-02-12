import MoltResearch.Discrepancy.Affine
import MoltResearch.Discrepancy.Offset

/-!
# Discrepancy bounds

This file provides simple triangle‑inequality bounds for the arithmetic‑progression sum
functions defined in `MoltResearch.Discrepancy.Affine`.  Given a uniform bound `B` on the
pointwise `Int.natAbs` of a function `f : ℕ → ℤ`, we show that the absolute value of the
sums is bounded by `n * B`.
-/

namespace MoltResearch

lemma natAbs_apSum_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (d n : ℕ) :
    Int.natAbs (apSum f d n) ≤ n * B := by
  induction n with
  | zero =>
      simp [apSum]
  | succ n ih =>
      have hsum :
          Int.natAbs (apSum f d (Nat.succ n)) ≤
            Int.natAbs (apSum f d n) + Int.natAbs (f ((n + 1) * d)) := by
        simpa [apSum_succ] using
          (Int.natAbs_add_le (apSum f d n) (f ((n + 1) * d)))
      have hfn : Int.natAbs (f ((n + 1) * d)) ≤ B := hB ((n + 1) * d)
      have hbound :
          Int.natAbs (apSum f d n) + Int.natAbs (f ((n + 1) * d)) ≤ n * B + B :=
        Nat.add_le_add ih hfn
      have : Int.natAbs (apSum f d (Nat.succ n)) ≤ n * B + B :=
        Nat.le_trans hsum hbound
      simpa [Nat.succ_mul] using this

lemma natAbs_apSumOffset_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (d m n : ℕ) :
    Int.natAbs (apSumOffset f d m n) ≤ n * B := by
  induction n with
  | zero =>
      simp [apSumOffset]
  | succ n ih =>
      have hsum :
          Int.natAbs (apSumOffset f d m (Nat.succ n)) ≤
            Int.natAbs (apSumOffset f d m n) + Int.natAbs (f ((m + n + 1) * d)) := by
        simpa [apSumOffset_succ] using
          (Int.natAbs_add_le (apSumOffset f d m n) (f ((m + n + 1) * d)))
      have hfn : Int.natAbs (f ((m + n + 1) * d)) ≤ B := hB ((m + n + 1) * d)
      have hbound :
          Int.natAbs (apSumOffset f d m n) + Int.natAbs (f ((m + n + 1) * d)) ≤ n * B + B :=
        Nat.add_le_add ih hfn
      have : Int.natAbs (apSumOffset f d m (Nat.succ n)) ≤ n * B + B :=
        Nat.le_trans hsum hbound
      simpa [Nat.succ_mul] using this

lemma natAbs_apSum_sub_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (d m n : ℕ) :
    Int.natAbs (apSum f d (m + n) - apSum f d m) ≤ n * B := by
  have h := natAbs_apSumOffset_le_mul (f := f) (B := B) (hB := hB) (d := d) (m := m) (n := n)
  simpa [apSumOffset_eq_sub] using h

lemma natAbs_apSumFrom_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (a d n : ℕ) :
    Int.natAbs (apSumFrom f a d n) ≤ n * B := by
  induction n with
  | zero =>
      simp [apSumFrom]
  | succ n ih =>
      have hsum :
          Int.natAbs (apSumFrom f a d (Nat.succ n)) ≤
            Int.natAbs (apSumFrom f a d n) + Int.natAbs (f (a + (n + 1) * d)) := by
        simpa [apSumFrom_succ] using
          (Int.natAbs_add_le (apSumFrom f a d n) (f (a + (n + 1) * d)))
      have hfn : Int.natAbs (f (a + (n + 1) * d)) ≤ B := hB (a + (n + 1) * d)
      have hbound :
          Int.natAbs (apSumFrom f a d n) + Int.natAbs (f (a + (n + 1) * d)) ≤ n * B + B :=
        Nat.add_le_add ih hfn
      have : Int.natAbs (apSumFrom f a d (Nat.succ n)) ≤ n * B + B :=
        Nat.le_trans hsum hbound
      simpa [Nat.succ_mul] using this

lemma natAbs_apSumFrom_sub_le_mul (f : ℕ → ℤ) (B : ℕ)
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (a d m n : ℕ) :
    Int.natAbs (apSumFrom f a d (m + n) - apSumFrom f a d m) ≤ n * B := by
  have h := natAbs_apSumFrom_le_mul (f := f) (B := B) (hB := hB)
    (a := a + m * d) (d := d) (n := n)
  simpa [apSumFrom_tail_eq_sub] using h

lemma HasDiscrepancyAtLeast.exists_witness_d_ge_one_and_length_mul_bound_gt {f : ℕ → ℤ} {C B : ℕ}
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (h : HasDiscrepancyAtLeast f C) :
    ∃ d n, d ≥ 1 ∧ n * B > C ∧ Int.natAbs (apSum f d n) > C := by
  rcases h.exists_witness_d_ge_one with ⟨d, n, hd, hgt⟩
  have hle : Int.natAbs (apSum f d n) ≤ n * B :=
    natAbs_apSum_le_mul (f := f) (B := B) (hB := hB) (d := d) (n := n)
  have hnB : n * B > C := lt_of_lt_of_le hgt hle
  exact ⟨d, n, hd, hnB, hgt⟩

lemma HasAffineDiscrepancyAtLeast.exists_witness_d_ge_one_and_length_mul_bound_gt {f : ℕ → ℤ} {C B : ℕ}
    (hB : ∀ n, Int.natAbs (f n) ≤ B) (h : HasAffineDiscrepancyAtLeast f C) :
    ∃ a d n, d ≥ 1 ∧ n * B > C ∧ Int.natAbs (apSumFrom f a d n) > C := by
  rcases h.exists_witness_d_ge_one with ⟨a, d, n, hd, hgt⟩
  have hle : Int.natAbs (apSumFrom f a d n) ≤ n * B :=
    natAbs_apSumFrom_le_mul (f := f) (B := B) (hB := hB) (a := a) (d := d) (n := n)
  have hnB : n * B > C := lt_of_lt_of_le hgt hle
  exact ⟨a, d, n, hd, hnB, hgt⟩

end MoltResearch
