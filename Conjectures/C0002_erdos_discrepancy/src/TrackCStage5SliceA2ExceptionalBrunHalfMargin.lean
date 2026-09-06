import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalQuotientLog

/-!
# Track R A2-V': half-scale Brun margin

The fixed logarithmic coefficient and the `X^(1/3)` Brun envelope consume
strictly less than half of `X = log A₁` at every sufficiently large scale.
-/

namespace MoltResearch

namespace Tao2015

/-- The selected Brun envelope eventually fits in half of the base-window
logarithm.  The explicit allocation is `1/8 + 1/16 + 1/4 = 7/16`. -/
theorem exists_sliceA2_brun_half_log_margin (budget : ℝ) :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 →
      let X := Real.log (A1 : ℝ)
      let y := X ^ (1 / 3 : ℝ)
      Real.log (32 / budget) + y + 2 * y ^ 2 ≤ X / 2 := by
  let D : ℝ := max 0 (Real.log (32 / budget))
  let C : ℝ := max 512 (8 * (D + 1))
  obtain ⟨A0, hA0⟩ := exists_sliceA2_log_ge C
  refine ⟨A0, fun A1 hA1 ↦ ?_⟩
  let X := Real.log (A1 : ℝ)
  let y := X ^ (1 / 3 : ℝ)
  have hCX : C ≤ X := by simpa [X] using hA0 A1 hA1
  have hX512 : (512 : ℝ) ≤ X := (le_max_left _ _).trans hCX
  have hXpos : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hD0 : 0 ≤ D := le_max_left _ _
  have hD : D ≤ X / 8 := by
    have hDC : 8 * (D + 1) ≤ C := le_max_right _ _
    have : 8 * (D + 1) ≤ X := hDC.trans hCX
    linarith
  have hlogCoeff : Real.log (32 / budget) ≤ X / 8 :=
    (le_max_right 0 (Real.log (32 / budget))).trans hD
  have hEight : (8 : ℝ) ≤ y := by
    have hbase : (8 : ℝ) ^ 3 = 512 := by norm_num
    have hr := Real.rpow_le_rpow
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 8) 3)
      (by simpa [hbase] using hX512)
      (by norm_num : (0 : ℝ) ≤ (3 : ℝ)⁻¹)
    calc
      (8 : ℝ) = ((8 : ℝ) ^ 3) ^ ((3 : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 8)
          (by norm_num : (3 : ℕ) ≠ 0)).symm
      _ ≤ X ^ ((3 : ℝ)⁻¹) := hr
      _ = y := by norm_num [y]
  have hySq : y ^ 2 = X ^ (2 / 3 : ℝ) := by
    dsimp [y]
    rw [pow_two, ← Real.rpow_add hXpos]
    norm_num
  have hyCube : y * y ^ 2 = X := by
    rw [hySq]
    dsimp [y]
    rw [← Real.rpow_add hXpos]
    norm_num
  have hySixteenth : y ≤ X / 16 := by
    have h16 : (16 : ℝ) ≤ y ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left h16 hy0
    rw [hyCube] at hmul
    linarith
  have htwoYSq : 2 * y ^ 2 ≤ X / 4 := by
    have hmul := mul_le_mul_of_nonneg_right hEight (sq_nonneg y)
    rw [hyCube] at hmul
    linarith
  dsimp only
  linarith

end Tao2015

end MoltResearch
