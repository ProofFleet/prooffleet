import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalRankinScale

/-!
# Track R A2-V': exceptional Rankin decay

The factor `exp(-c X^(1/50))` absorbs the remaining linear logarithm and
the fixed tilted Euler-product envelope.
-/

namespace MoltResearch

namespace Tao2015

open Filter

/-- The scalar envelope for the sharp Rankin tail eventually enters its
fixed exceptional allocation. -/
theorem exists_sliceA2Exceptional_rankin_scalar_margin
    (Cp : ℝ)
    (epsc eps rho0 : ℝ) (heps : 0 < eps) (hrho0 : 0 < rho0) :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 →
      let X := Real.log (A1 : ℝ)
      (3 * X + 2) * Real.exp (6 * sliceA2ExceptionalMass 0 epsc) *
          Real.exp (-(X ^ (1 / 50 : ℝ) /
            (16 * (exceptionalIntervalRatio epsc : ℝ)))) ≤
        sliceA2ExceptionalTailBudget Cp epsc eps rho0 := by
  let R : ℝ := exceptionalIntervalRatio epsc
  let C : ℝ := Real.exp (6 * sliceA2ExceptionalMass 0 epsc)
  let target := sliceA2ExceptionalTailBudget Cp epsc eps rho0
  let b : ℝ := 1 / (16 * R)
  have hR : 0 < R := by
    dsimp [R]
    exact_mod_cast (show 0 < exceptionalIntervalRatio epsc by
      have := exceptionalIntervalRatio_three_le epsc
      omega)
  have hC : 0 < C := by dsimp [C]; positivity
  have htarget : 0 < target := by
    simpa [target] using sliceA2ExceptionalTailBudget_pos Cp epsc eps rho0 heps hrho0
  have hb : 0 < b := by dsimp [b]; positivity
  have hconst : Tendsto (fun _ : ℝ => 5 * C) atTop (nhds (5 * C)) :=
    tendsto_const_nhds
  have hlimZ : Tendsto
      (fun z : ℝ => (5 * C) *
        (z ^ (50 : ℝ) * Real.exp (-b * z))) atTop (nhds 0) := by
    convert hconst.mul
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 50 b hb) using 1 <;>
        simp
  have hlimX : Tendsto
      (fun X : ℝ => (5 * C) *
        ((X ^ (1 / 50 : ℝ)) ^ (50 : ℝ) *
          Real.exp (-b * X ^ (1 / 50 : ℝ)))) atTop (nhds 0) :=
    hlimZ.comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 50))
  have hevent := (tendsto_order.1 hlimX).2 target htarget
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨X0, hX0⟩ := hevent
  obtain ⟨A0, hA0⟩ := exists_sliceA2_log_ge (max 1 X0)
  refine ⟨A0, fun A1 hA1 ↦ ?_⟩
  let X := Real.log (A1 : ℝ)
  have hX : max 1 X0 ≤ X := by simpa [X] using hA0 A1 hA1
  have hX1 : 1 ≤ X := (le_max_left _ _).trans hX
  have hX0' : X0 ≤ X := (le_max_right _ _).trans hX
  have hdec := hX0 X hX0'
  have hrootpow : (X ^ (1 / 50 : ℝ)) ^ (50 : ℝ) = X := by
    rw [← Real.rpow_mul (by linarith : 0 ≤ X)]
    norm_num
  have hdec' : 5 * C * X *
      Real.exp (-(X ^ (1 / 50 : ℝ) / (16 * R))) < target := by
    have hbexp : -b * X ^ (1 / 50 : ℝ) =
        -(X ^ (1 / 50 : ℝ) / (16 * R)) := by
      dsimp [b]
      ring
    rw [hrootpow, hbexp] at hdec
    nlinarith
  have hpoly : 3 * X + 2 ≤ 5 * X := by linarith
  have hnonneg : 0 ≤ C * Real.exp
      (-(X ^ (1 / 50 : ℝ) / (16 * R))) := by positivity
  have hbound := mul_le_mul_of_nonneg_right hpoly hnonneg
  dsimp only
  change (3 * X + 2) * C *
      Real.exp (-(X ^ (1 / 50 : ℝ) / (16 * R))) ≤ target
  calc
    (3 * X + 2) * C *
          Real.exp (-(X ^ (1 / 50 : ℝ) / (16 * R))) ≤
        5 * X * (C *
          Real.exp (-(X ^ (1 / 50 : ℝ) / (16 * R)))) := by
      nlinarith
    _ = 5 * C * X *
          Real.exp (-(X ^ (1 / 50 : ℝ) / (16 * R))) := by ring
    _ ≤ target := hdec'.le

end Tao2015

end MoltResearch
