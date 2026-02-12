import MoltResearch.Discrepancy.Basic
import MoltResearch.Discrepancy.Affine

/-!
# Discrepancy: scaling lemmas

If `f` has discrepancy at least `C`, then scaling by a nonzero integer preserves
that discrepancy level.
-/

namespace MoltResearch

lemma HasDiscrepancyAtLeast.mul_left_of_ne_zero {f : ℕ → ℤ} {C : ℕ} (c : ℤ) (hc : c ≠ 0) :
    HasDiscrepancyAtLeast f C → HasDiscrepancyAtLeast (fun n => c * f n) C := by
  rintro ⟨d, n, hd, hgt⟩
  refine ⟨d, n, hd, ?_⟩
  -- derive `1 ≤ |c|`
  have hk : 1 ≤ Int.natAbs c := by
    have hne : Int.natAbs c ≠ 0 := by
      intro h
      have : c = 0 := (Int.natAbs_eq_zero).mp h
      exact hc this
    have hpos : 0 < Int.natAbs c := Nat.pos_of_ne_zero hne
    exact Nat.succ_le_iff.mpr hpos
  let A := Int.natAbs (apSum f d n)
  have hCA : C < A := by
    dsimp [A] at *
    exact hgt
  have hA_mul : A ≤ (Int.natAbs c) * A := by
    have := Nat.mul_le_mul_right A hk
    simpa [one_mul] using this
  have hC_mul : C < (Int.natAbs c) * A := lt_of_lt_of_le hCA hA_mul
  simpa [apSum_mul_left, Int.natAbs_mul, A] using hC_mul

lemma HasDiscrepancyAtLeast.mul_right_of_ne_zero {f : ℕ → ℤ} {C : ℕ} (c : ℤ) (hc : c ≠ 0) :
    HasDiscrepancyAtLeast f C → HasDiscrepancyAtLeast (fun n => f n * c) C := by
  rintro ⟨d, n, hd, hgt⟩
  refine ⟨d, n, hd, ?_⟩
  have hk : 1 ≤ Int.natAbs c := by
    have hne : Int.natAbs c ≠ 0 := by
      intro h
      have : c = 0 := (Int.natAbs_eq_zero).mp h
      exact hc this
    have hpos : 0 < Int.natAbs c := Nat.pos_of_ne_zero hne
    exact Nat.succ_le_iff.mpr hpos
  let A := Int.natAbs (apSum f d n)
  have hCA : C < A := by
    dsimp [A] at *
    exact hgt
  have hA_mul : A ≤ A * (Int.natAbs c) := by
    have := Nat.mul_le_mul_left A hk
    simpa [one_mul] using this
  have hC_mul : C < A * (Int.natAbs c) := lt_of_lt_of_le hCA hA_mul
  simpa [apSum_mul_right, Int.natAbs_mul, A] using hC_mul

lemma HasDiscrepancyAtLeast.mul_left_scale {f : ℕ → ℤ} {C : ℕ} (c : ℤ) (hc : c ≠ 0) :
    HasDiscrepancyAtLeast f C → HasDiscrepancyAtLeast (fun n => c * f n) (Int.natAbs c * C) := by
  rintro ⟨d, n, hd, hgt⟩
  refine ⟨d, n, hd, ?_⟩
  let k := Int.natAbs c
  have hkpos : 0 < k := by
    have hne : k ≠ 0 := by
      intro h
      have : c = 0 := (Int.natAbs_eq_zero).mp h
      exact hc this
    exact Nat.pos_of_ne_zero hne
  have hC_mul : k * C < k * Int.natAbs (apSum f d n) := by
    have := Nat.mul_lt_mul_of_pos_left hgt hkpos
    simpa using this
  simpa [apSum_mul_left, Int.natAbs_mul, k] using hC_mul

lemma HasDiscrepancyAtLeast.mul_right_scale {f : ℕ → ℤ} {C : ℕ} (c : ℤ) (hc : c ≠ 0) :
    HasDiscrepancyAtLeast f C → HasDiscrepancyAtLeast (fun n => f n * c) (Int.natAbs c * C) := by
  rintro ⟨d, n, hd, hgt⟩
  refine ⟨d, n, hd, ?_⟩
  let k := Int.natAbs c
  have hkpos : 0 < k := by
    have hne : k ≠ 0 := by
      intro h
      have : c = 0 := (Int.natAbs_eq_zero).mp h
      exact hc this
    exact Nat.pos_of_ne_zero hne
  have hC_mul : k * C < k * Int.natAbs (apSum f d n) := by
    have := Nat.mul_lt_mul_of_pos_left hgt hkpos
    simpa using this
  simpa [apSum_mul_right, Int.natAbs_mul, k, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hC_mul

lemma HasAffineDiscrepancyAtLeast.mul_left_of_ne_zero {f : ℕ → ℤ} {C : ℕ} (c : ℤ) (hc : c ≠ 0) :
    HasAffineDiscrepancyAtLeast f C → HasAffineDiscrepancyAtLeast (fun n => c * f n) C := by
  rintro ⟨a, d, n, hd, hgt⟩
  refine ⟨a, d, n, hd, ?_⟩
  have hk : 1 ≤ Int.natAbs c := by
    have hne : Int.natAbs c ≠ 0 := by
      intro h
      have : c = 0 := (Int.natAbs_eq_zero).mp h
      exact hc this
    have hpos : 0 < Int.natAbs c := Nat.pos_of_ne_zero hne
    exact Nat.succ_le_iff.mpr hpos
  let A := Int.natAbs (apSumFrom f a d n)
  have hCA : C < A := by
    dsimp [A] at *
    exact hgt
  have hA_mul : A ≤ (Int.natAbs c) * A := by
    have := Nat.mul_le_mul_right A hk
    simpa [one_mul] using this
  have hC_mul : C < (Int.natAbs c) * A := lt_of_lt_of_le hCA hA_mul
  simpa [apSumFrom_mul_left, Int.natAbs_mul, A] using hC_mul

lemma HasAffineDiscrepancyAtLeast.mul_right_of_ne_zero {f : ℕ → ℤ} {C : ℕ} (c : ℤ) (hc : c ≠ 0) :
    HasAffineDiscrepancyAtLeast f C → HasAffineDiscrepancyAtLeast (fun n => f n * c) C := by
  rintro ⟨a, d, n, hd, hgt⟩
  refine ⟨a, d, n, hd, ?_⟩
  have hk : 1 ≤ Int.natAbs c := by
    have hne : Int.natAbs c ≠ 0 := by
      intro h
      have : c = 0 := (Int.natAbs_eq_zero).mp h
      exact hc this
    have hpos : 0 < Int.natAbs c := Nat.pos_of_ne_zero hne
    exact Nat.succ_le_iff.mpr hpos
  let A := Int.natAbs (apSumFrom f a d n)
  have hCA : C < A := by
    dsimp [A] at *
    exact hgt
  have hA_mul : A ≤ A * (Int.natAbs c) := by
    have := Nat.mul_le_mul_left A hk
    simpa [one_mul] using this
  have hC_mul : C < A * (Int.natAbs c) := lt_of_lt_of_le hCA hA_mul
  simpa [apSumFrom_mul_right, Int.natAbs_mul, A] using hC_mul

lemma HasAffineDiscrepancyAtLeast.mul_left_scale {f : ℕ → ℤ} {C : ℕ} (c : ℤ) (hc : c ≠ 0) :
    HasAffineDiscrepancyAtLeast f C → HasAffineDiscrepancyAtLeast (fun n => c * f n) (Int.natAbs c * C) := by
  rintro ⟨a, d, n, hd, hgt⟩
  refine ⟨a, d, n, hd, ?_⟩
  let k := Int.natAbs c
  have hkpos : 0 < k := by
    have hne : k ≠ 0 := by
      intro h
      have : c = 0 := (Int.natAbs_eq_zero).mp h
      exact hc this
    exact Nat.pos_of_ne_zero hne
  have hC_mul : k * C < k * Int.natAbs (apSumFrom f a d n) := by
    have := Nat.mul_lt_mul_of_pos_left hgt hkpos
    simpa using this
  simpa [apSumFrom_mul_left, Int.natAbs_mul, k] using hC_mul

lemma HasAffineDiscrepancyAtLeast.mul_right_scale {f : ℕ → ℤ} {C : ℕ} (c : ℤ) (hc : c ≠ 0) :
    HasAffineDiscrepancyAtLeast f C → HasAffineDiscrepancyAtLeast (fun n => f n * c) (Int.natAbs c * C) := by
  rintro ⟨a, d, n, hd, hgt⟩
  refine ⟨a, d, n, hd, ?_⟩
  let k := Int.natAbs c
  have hkpos : 0 < k := by
    have hne : k ≠ 0 := by
      intro h
      have : c = 0 := (Int.natAbs_eq_zero).mp h
      exact hc this
    exact Nat.pos_of_ne_zero hne
  have hC_mul : k * C < k * Int.natAbs (apSumFrom f a d n) := by
    have := Nat.mul_lt_mul_of_pos_left hgt hkpos
    simpa using this
  simpa [apSumFrom_mul_right, Int.natAbs_mul, k, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hC_mul

end MoltResearch
