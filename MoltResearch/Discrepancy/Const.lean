import MoltResearch.Discrepancy.Basic

/-!
# Constant discrepancy lemmas

Lemmas about arithmetic progression sums of constant functions.
-/

namespace MoltResearch

lemma apSum_const (c : ℤ) (d n : ℕ) :
    apSum (fun _ => c) d n = n • c := by
  unfold apSum
  simp

lemma apSumOffset_const (c : ℤ) (d m n : ℕ) :
    apSumOffset (fun _ => c) d m n = n • c := by
  unfold apSumOffset
  simp

@[simp] lemma apSum_const_zero (d n : ℕ) :
    apSum (fun _ => (0 : ℤ)) d n = 0 := by
  simpa using (apSum_const (c := (0 : ℤ)) d n)

@[simp] lemma apSum_const_one (d n : ℕ) :
    apSum (fun _ => (1 : ℤ)) d n = n := by
  simpa using (apSum_const (c := (1 : ℤ)) d n)

@[simp] lemma apSumOffset_const_zero (d m n : ℕ) :
    apSumOffset (fun _ => (0 : ℤ)) d m n = 0 := by
  simpa using (apSumOffset_const (c := (0 : ℤ)) d m n)

@[simp] lemma apSumOffset_const_one (d m n : ℕ) :
    apSumOffset (fun _ => (1 : ℤ)) d m n = n := by
  simpa using (apSumOffset_const (c := (1 : ℤ)) d m n)

/-- A non‑zero constant sequence has arbitrarily large discrepancy. -/
lemma hasDiscrepancyAtLeast_const_of_ne_zero (c : ℤ) (hc : c ≠ 0) (C : ℕ) :
    HasDiscrepancyAtLeast (fun _ : ℕ => c) C := by
  -- choose `d = 1` and `n = C + 1`
  refine ⟨1, C + 1, by decide, ?_⟩
  -- compute the absolute value of the sum
  have hnatAbs :
      Int.natAbs (apSum (fun _ => c) 1 (C + 1)) = (C + 1) * Int.natAbs c := by
    simpa [apSum_const, nsmul_eq_mul] using
      (Int.natAbs_mul (a := (C + 1 : ℤ)) (b := c))
  -- `Int.natAbs c` is at least `1`
  have hpos : 1 ≤ Int.natAbs c := by
    have hne : Int.natAbs c ≠ 0 := by
      intro hzero
      have : c = 0 := by
        exact (Int.natAbs_eq_zero.mp hzero)
      exact hc this
    have hgt : 0 < Int.natAbs c := Nat.pos_of_ne_zero hne
    exact Nat.succ_le_iff.mpr hgt
  -- now the inequality
  have hgt : (C + 1) * Int.natAbs c > C := by
    have : (C + 1) * Int.natAbs c ≥ (C + 1) * 1 :=
      Nat.mul_le_mul_left (C + 1) hpos
    have : (C + 1) * Int.natAbs c ≥ C + 1 := by
      simpa using this
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self C) this
  -- finish
  simpa [hnatAbs] using hgt

end MoltResearch
