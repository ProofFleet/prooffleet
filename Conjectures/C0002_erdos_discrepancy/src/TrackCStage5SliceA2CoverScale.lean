import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2CoverEnvelopes
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalDomination

/-!
# Track R A2-V': the raw cover scale margin

After the moment estimate, the time factors use only the power `24/25` of
the window scale.  The remaining `1/25` pays two copies of the exceptional
upper endpoint, provided the last ordinary cell count is no larger than
that endpoint.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The fixed coefficient in the twenty-fifth-power cover calculation. -/
noncomputable def sliceA2CoverScaleCoefficient : ℝ :=
  (2 * (2 : ℝ) ^ (23 / 50 : ℝ)) ^ 25

/-- A twenty-fifth-power endpoint margin closes the raw cover scale once
the last ordinary cell count is bounded by the remote upper endpoint. -/
theorem sliceA2ExceptionalCover_scale_margin
    (A1 A : ℕ) (epsc T Ccells : ℝ)
    (hA1 : 1 ≤ A1) (hA : A1 ≤ A) (hT : 1 ≤ T) (hTA : T ≤ A)
    (hcells : Ccells ≤ exceptionalPrimeUpper A1 epsc)
    (hmargin : sliceA2CoverScaleCoefficient *
        (exceptionalPrimeUpper A1 epsc : ℝ) ^ 50 ≤ A1) :
    2 * Ccells *
          Real.exp ((23 / 50 : ℝ) * Real.log (2 * T)) * Real.sqrt T *
            (exceptionalPrimeUpper A1 epsc : ℝ) ≤ A := by
  let Q : ℝ := exceptionalPrimeUpper A1 epsc
  let D : ℝ := 2 * (2 : ℝ) ^ (23 / 50 : ℝ)
  have hApos : (0 : ℝ) < A := by
    exact_mod_cast (show 0 < A by omega)
  have hA1pos : (0 : ℝ) < A1 := by exact_mod_cast (show 0 < A1 by omega)
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have htime :
      Real.exp ((23 / 50 : ℝ) * Real.log (2 * T)) * Real.sqrt T =
        (2 : ℝ) ^ (23 / 50 : ℝ) * T ^ (24 / 25 : ℝ) := by
    have h2T : 0 < 2 * T := by positivity
    have hexp : Real.exp ((23 / 50 : ℝ) * Real.log (2 * T)) =
        (2 * T) ^ (23 / 50 : ℝ) := by
      rw [Real.rpow_def_of_pos h2T]
      congr 1
      ring
    rw [hexp, Real.mul_rpow (by norm_num) hTpos.le, Real.sqrt_eq_rpow]
    calc
      (2 : ℝ) ^ (23 / 50 : ℝ) * T ^ (23 / 50 : ℝ) * T ^ (1 / 2 : ℝ) =
          (2 : ℝ) ^ (23 / 50 : ℝ) *
            (T ^ (23 / 50 : ℝ) * T ^ (1 / 2 : ℝ)) := by ring
      _ = (2 : ℝ) ^ (23 / 50 : ℝ) *
            T ^ ((23 / 50 : ℝ) + 1 / 2) := by
        rw [← Real.rpow_add hTpos]
      _ = _ := by norm_num
  have hFpow : (D * Q ^ 2) ^ 25 =
      sliceA2CoverScaleCoefficient * Q ^ 50 := by
    dsimp [D, sliceA2CoverScaleCoefficient]
    rw [mul_pow, ← pow_mul]
  have hroot : D * Q ^ 2 ≤ (A1 : ℝ) ^ (1 / 25 : ℝ) := by
    have hpowmargin : (D * Q ^ 2) ^ 25 ≤ (A1 : ℝ) :=
      hFpow.le.trans hmargin
    have hp := Real.rpow_le_rpow
      (pow_nonneg (mul_nonneg hD0 (sq_nonneg Q)) 25)
      hpowmargin
      (by norm_num : (0 : ℝ) ≤ (25 : ℝ)⁻¹)
    calc
      D * Q ^ 2 = ((D * Q ^ 2) ^ 25) ^ ((25 : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (mul_nonneg hD0 (sq_nonneg Q))
          (by norm_num : (25 : ℕ) ≠ 0)).symm
      _ ≤ (A1 : ℝ) ^ ((25 : ℝ)⁻¹) := hp
      _ = (A1 : ℝ) ^ (1 / 25 : ℝ) := by norm_num
  have hTpow : T ^ (24 / 25 : ℝ) ≤ (A : ℝ) ^ (24 / 25 : ℝ) :=
    Real.rpow_le_rpow hTpos.le (by exact_mod_cast hTA) (by norm_num)
  have hA1pow : (A1 : ℝ) ^ (1 / 25 : ℝ) ≤
      (A : ℝ) ^ (1 / 25 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hA) (by norm_num)
  calc
    2 * Ccells * Real.exp ((23 / 50 : ℝ) * Real.log (2 * T)) *
          Real.sqrt T * (exceptionalPrimeUpper A1 epsc : ℝ) =
        2 * Ccells *
          (Real.exp ((23 / 50 : ℝ) * Real.log (2 * T)) *
            Real.sqrt T) * Q := by dsimp [Q]; ring
    _ = 2 * Ccells *
          ((2 : ℝ) ^ (23 / 50 : ℝ) * T ^ (24 / 25 : ℝ)) * Q := by
        rw [htime]
    _ = (2 * Ccells * (2 : ℝ) ^ (23 / 50 : ℝ) * Q) *
          T ^ (24 / 25 : ℝ) := by ring
    _ ≤ (D * Q ^ 2) * T ^ (24 / 25 : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hTpos.le _)
      dsimp [D]
      have hpow0 : 0 ≤ (2 : ℝ) ^ (23 / 50 : ℝ) := by positivity
      nlinarith [mul_nonneg hpow0 hQ0,
        mul_nonneg hpow0 (mul_nonneg hQ0 hQ0)]
    _ ≤ (A1 : ℝ) ^ (1 / 25 : ℝ) * T ^ (24 / 25 : ℝ) := by
      gcongr
    _ ≤ (A : ℝ) ^ (1 / 25 : ℝ) * (A : ℝ) ^ (24 / 25 : ℝ) := by
      exact mul_le_mul hA1pow hTpow (Real.rpow_nonneg hTpos.le _)
        (Real.rpow_nonneg (by positivity) _)
    _ = A := by
      rw [← Real.rpow_add hApos]
      norm_num

/-- The endpoint domination theorem supplies the preceding fixed margin
uniformly over the whole scale window. -/
theorem exists_sliceA2ExceptionalCover_scale_margin (epsc : ℝ) :
    ∃ A0 : ℕ, ∀ A1 A : ℕ, A0 ≤ A1 → A1 ≤ A →
      ∀ T Ccells : ℝ, 1 ≤ T → T ≤ A →
        Ccells ≤ exceptionalPrimeUpper A1 epsc →
        2 * Ccells *
            Real.exp ((23 / 50 : ℝ) * Real.log (2 * T)) * Real.sqrt T *
              (exceptionalPrimeUpper A1 epsc : ℝ) ≤ A := by
  obtain ⟨A0, hA0⟩ := exists_const_mul_exceptionalPrimeUpper_pow_le
    sliceA2CoverScaleCoefficient 50 epsc
    (by unfold sliceA2CoverScaleCoefficient; positivity) (by norm_num)
  refine ⟨max 1 A0, fun A1 A hA1 hA T Ccells hT hTA hcells => ?_⟩
  apply sliceA2ExceptionalCover_scale_margin A1 A epsc T Ccells
    ((le_max_left 1 A0).trans hA1) hA hT hTA hcells
  exact hA0 A1 ((le_max_right 1 A0).trans hA1)

end Tao2015

end MoltResearch
