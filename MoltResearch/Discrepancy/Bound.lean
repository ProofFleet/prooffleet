import MoltResearch.Discrepancy.Affine

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

end MoltResearch
