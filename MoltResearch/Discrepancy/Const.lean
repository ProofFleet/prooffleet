import MoltResearch.Discrepancy.Basic
import MoltResearch.Discrepancy.Affine

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

/-- Sum of a constant function over an arithmetic progression with a start index. -/
lemma apSumFrom_const (c : ℤ) (a d n : ℕ) :
    apSumFrom (fun _ => c) a d n = n • c := by
  unfold apSumFrom
  simp

@[simp] lemma apSumFrom_const_zero (a d n : ℕ) :
    apSumFrom (fun _ => (0 : ℤ)) a d n = 0 := by
  simpa using (apSumFrom_const (c := (0 : ℤ)) a d n)

@[simp] lemma apSumFrom_const_one (a d n : ℕ) :
    apSumFrom (fun _ => (1 : ℤ)) a d n = n := by
  simpa using (apSumFrom_const (c := (1 : ℤ)) a d n)

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

/-- A constant zero function never has discrepancy at least `C`. -/
lemma not_hasDiscrepancyAtLeast_const_zero (C : ℕ) :
    ¬ HasDiscrepancyAtLeast (fun _ : ℕ => (0 : ℤ)) C := by
  intro h
  rcases h with ⟨d, n, hdn, hgt⟩
  have hsum : apSum (fun _ => (0 : ℤ)) d n = 0 := by
    simpa using (apSum_const_zero d n)
  have hnat : Int.natAbs (apSum (fun _ => (0 : ℤ)) d n) = 0 := by
    simpa [hsum]
  have hzero : (0 : ℕ) > C := by
    simpa [hnat] using hgt
  cases C with
  | zero =>
      have : (0 : ℕ) > 0 := hzero
      exact (Nat.not_lt_zero 0) this
  | succ C' =>
      have : Nat.succ C' < 0 := by
        simpa using hzero
      exact (Nat.not_lt_zero (Nat.succ C')) this

/-- A constant function has discrepancy at least `C` iff it is non‑zero. -/
lemma hasDiscrepancyAtLeast_const_iff (c : ℤ) (C : ℕ) :
    HasDiscrepancyAtLeast (fun _ : ℕ => c) C ↔ c ≠ 0 := by
  constructor
  · intro h
    by_contra hc
    have h0 : HasDiscrepancyAtLeast (fun _ : ℕ => (0 : ℤ)) C := by
      simpa [hc] using h
    exact not_hasDiscrepancyAtLeast_const_zero (C := C) h0
  · intro hc
    exact hasDiscrepancyAtLeast_const_of_ne_zero c hc C

/-- A non‑zero constant sequence has arbitrarily large affine discrepancy. -/
lemma hasAffineDiscrepancyAtLeast_const_of_ne_zero (c : ℤ) (hc : c ≠ 0) (C : ℕ) :
    HasAffineDiscrepancyAtLeast (fun _ : ℕ => c) C := by
  -- choose `a = 0`, `d = 1` and `n = C + 1`
  refine ⟨0, 1, C + 1, by decide, ?_⟩
  have hnatAbs :
      Int.natAbs (apSumFrom (fun _ => c) 0 1 (C + 1)) = (C + 1) * Int.natAbs c := by
    simpa [apSumFrom_const, nsmul_eq_mul] using
      (Int.natAbs_mul (a := (C + 1 : ℤ)) (b := c))
  have hpos : 1 ≤ Int.natAbs c := by
    have hne : Int.natAbs c ≠ 0 := by
      intro hzero
      have : c = 0 := by
        exact (Int.natAbs_eq_zero.mp hzero)
      exact hc this
    have hgt : 0 < Int.natAbs c := Nat.pos_of_ne_zero hne
    exact Nat.succ_le_iff.mpr hgt
  have hgt : (C + 1) * Int.natAbs c > C := by
    have : (C + 1) * Int.natAbs c ≥ (C + 1) * 1 :=
      Nat.mul_le_mul_left (C + 1) hpos
    have : (C + 1) * Int.natAbs c ≥ C + 1 := by
      simpa using this
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self C) this
  simpa [hnatAbs] using hgt

/-- A constant zero function never has affine discrepancy at least `C`. -/
lemma not_hasAffineDiscrepancyAtLeast_const_zero (C : ℕ) :
    ¬ HasAffineDiscrepancyAtLeast (fun _ : ℕ => (0 : ℤ)) C := by
  intro h
  rcases h with ⟨a, d, n, hdn, hgt⟩
  have hsum : apSumFrom (fun _ => (0 : ℤ)) a d n = 0 := by
    simpa using (apSumFrom_const_zero a d n)
  have hnat : Int.natAbs (apSumFrom (fun _ => (0 : ℤ)) a d n) = 0 := by
    simpa [hsum]
  have hzero : (0 : ℕ) > C := by
    simpa [hnat] using hgt
  cases C with
  | zero =>
      have : (0 : ℕ) > 0 := hzero
      exact (Nat.not_lt_zero 0) this
  | succ C' =>
      have : Nat.succ C' < 0 := by
        simpa using hzero
      exact (Nat.not_lt_zero (Nat.succ C')) this

/-- A constant function has affine discrepancy at least `C` iff it is non‑zero. -/
lemma hasAffineDiscrepancyAtLeast_const_iff (c : ℤ) (C : ℕ) :
    HasAffineDiscrepancyAtLeast (fun _ : ℕ => c) C ↔ c ≠ 0 := by
  constructor
  · intro h
    by_contra hc
    have h0 : HasAffineDiscrepancyAtLeast (fun _ : ℕ => (0 : ℤ)) C := by
      simpa [hc] using h
    exact not_hasAffineDiscrepancyAtLeast_const_zero (C := C) h0
  · intro hc
    exact hasAffineDiscrepancyAtLeast_const_of_ne_zero c hc C

end MoltResearch
