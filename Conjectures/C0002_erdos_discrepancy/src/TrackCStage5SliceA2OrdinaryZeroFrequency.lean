import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryZeroPrimeClose

/-!
# Track R A2-V': bottom frequency-side fit

The remaining level-zero cost is linear in `T/A`.  This leaf records its
fixed coefficient after the bottom ratio and resolution have been chosen.
-/

namespace MoltResearch

namespace Tao2015

/-- Fixed coefficient multiplying `T/A` in the bottom frequency-side
schedule estimate. -/
noncomputable def sliceA2OrdinaryZeroFrequencyCoefficient
    (P0 ratio0 eta : ℕ) (eps rho0 : ℝ) : ℝ :=
  let Nbar := sliceA2OrdinaryZeroNBound ratio0 eps rho0
  let R : ℝ := max 2 ratio0
  (2 * Nbar * R + 2) * Real.log (P0 : ℝ) *
    (Real.exp Real.pi * Real.log 4 *
      (2 * Real.exp 1 *
        ((sliceA2LadderQ P0 ratio0 eta 0 : ℝ) ^ (13 / 20 : ℝ) *
          Real.exp 1) * (4 * Nbar + 1)))

theorem sliceA2OrdinaryZeroFrequencyCoefficient_pos
    (P0 ratio0 eta : ℕ) (eps rho0 : ℝ)
    (hP0 : 3 ≤ P0) (heps : 0 < eps) (hrho0 : 0 < rho0) :
    0 < sliceA2OrdinaryZeroFrequencyCoefficient
      P0 ratio0 eta eps rho0 := by
  have hN := sliceA2OrdinaryZeroNBound_pos ratio0 eps rho0 heps hrho0
  have hlogP : 0 < Real.log (P0 : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P0 by omega))
  have hQ : (0 : ℝ) < sliceA2LadderQ P0 ratio0 eta 0 := by
    exact_mod_cast (show 0 < sliceA2LadderQ P0 ratio0 eta 0 by
      have := sliceA2LadderP_two_le P0 ratio0 eta 0 (by omega)
      have := sliceA2LadderP_le_Q P0 ratio0 eta 0
      omega)
  unfold sliceA2OrdinaryZeroFrequencyCoefficient
  dsimp only
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  positivity

/-- The exact frequency-side schedule inequality follows from a single
explicit height-to-window ratio margin. -/
theorem sliceA2Ordinary_zero_frequency_fit_of_ratio
    (P0 ratio0 eta A : ℕ) (eps rho0 T : ℝ)
    (hP0 : 3 ≤ P0) (hA : 1 ≤ A)
    (heps : 0 < eps) (hrho0 : 0 < rho0) (hT : 0 ≤ T)
    (hratio :
      (T / (A : ℝ)) *
          sliceA2OrdinaryZeroFrequencyCoefficient
            P0 ratio0 eta eps rho0 ≤
        sliceA2KappaMain 0 / 2 * (eps ^ 2 * rho0 / 8)) :
    (2 * (sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℝ) *
          (Real.log (sliceA2LadderQ P0 ratio0 eta 0) -
            Real.log (sliceA2LadderP P0 ratio0 eta 0)) + 2) *
        (Real.exp Real.pi * Real.log 4 *
          ((2 * T * Real.exp
              (1 / ((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ)) /
              (A : ℝ)) *
            ((sliceA2LadderQ P0 ratio0 eta 0 : ℝ) ^
                (1 - 2 * innerBandScheduleAlpha 0) *
              Real.exp ((1 - 2 * innerBandScheduleAlpha 0) /
                ((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ))) *
            (((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ) /
                (1 - 2 * innerBandScheduleAlpha 0) + 1))) ≤
        sliceA2KappaMain 0 / 2 * (eps ^ 2 * rho0 / 8) := by
  let N := sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0
  let Nbar := sliceA2OrdinaryZeroNBound ratio0 eps rho0
  let R := max 2 ratio0
  let P : ℝ := P0
  let Q : ℝ := sliceA2LadderQ P0 ratio0 eta 0
  have hNpos : 0 < N := by
    dsimp [N]
    exact sliceA2OrdinaryN_pos P0 ratio0 eta 0 eps rho0
  have hN : (N : ℝ) ≤ Nbar := by
    simpa [N, Nbar] using sliceA2OrdinaryN_zero_le_fixed
      P0 ratio0 eta eps rho0 hP0 heps hrho0
  have hNbar : 0 < Nbar := by
    simpa [Nbar] using sliceA2OrdinaryZeroNBound_pos
      ratio0 eps rho0 heps hrho0
  have hR : 1 ≤ R := by dsimp [R]; omega
  have hP3 : (3 : ℝ) ≤ P := by
    change (3 : ℝ) ≤ (P0 : ℝ)
    exact_mod_cast hP0
  have hPpos : 0 < P := by linarith
  have hQpos : 0 < Q := by dsimp [Q]; positivity
  have hlogP1 : 1 ≤ Real.log P := by
    have hexp : Real.exp 1 < 3 := Real.exp_one_lt_three
    exact (calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.strictMonoOn_log (Real.exp_pos 1)
        (by norm_num) hexp
      _ ≤ Real.log P := Real.log_le_log (by norm_num) hP3).le
  have halpha : 2 * innerBandScheduleAlpha 0 = 7 / 20 := by
    unfold innerBandScheduleAlpha
    simpa using scheduleAlpha_one
  have halphaComp : 1 - 2 * innerBandScheduleAlpha 0 = 13 / 20 := by
    rw [halpha]
    norm_num
  have hwidth :
      Real.log (sliceA2LadderQ P0 ratio0 eta 0 : ℝ) -
          Real.log (sliceA2LadderP P0 ratio0 eta 0 : ℝ) ≤
        (R : ℝ) * Real.log P := by
    have hlogQ :
        Real.log (sliceA2LadderQ P0 ratio0 eta 0 : ℝ) =
          (R : ℝ) * Real.log P := by
      simp only [sliceA2LadderQ_eq, sliceA2LadderP_zero,
        sliceA2LadderRatio_zero, Nat.cast_pow, Real.log_pow]
      rfl
    rw [hlogQ]
    simp only [sliceA2LadderP_zero]
    change (R : ℝ) * Real.log P - Real.log P ≤ (R : ℝ) * Real.log P
    linarith
  have hwidth0 : 0 ≤
      Real.log (sliceA2LadderQ P0 ratio0 eta 0 : ℝ) -
        Real.log (sliceA2LadderP P0 ratio0 eta 0 : ℝ) := by
    apply sub_nonneg.mpr
    apply Real.log_le_log
    · positivity
    · exact_mod_cast sliceA2LadderP_le_Q P0 ratio0 eta 0
  have hcell :
      2 * (N : ℝ) *
          (Real.log (sliceA2LadderQ P0 ratio0 eta 0 : ℝ) -
            Real.log (sliceA2LadderP P0 ratio0 eta 0 : ℝ)) + 2 ≤
        (2 * Nbar * (R : ℝ) + 2) * Real.log P := by
    calc
      2 * (N : ℝ) *
            (Real.log (sliceA2LadderQ P0 ratio0 eta 0 : ℝ) -
              Real.log (sliceA2LadderP P0 ratio0 eta 0 : ℝ)) + 2 ≤
          2 * Nbar * ((R : ℝ) * Real.log P) + 2 := by gcongr
      _ ≤ (2 * Nbar * (R : ℝ) + 2) * Real.log P := by nlinarith
  have hN2 : 2 ≤ N := by
    dsimp [N, sliceA2OrdinaryN, sliceA2LevelN]
    exact le_max_left _ _
  have hcast : (4 : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by
    exact_mod_cast (show 4 ≤ 2 * N by omega)
  have hexpUnit :
      Real.exp (1 / ((2 * N : ℕ) : ℝ)) ≤ Real.exp 1 := by
    rw [Real.exp_le_exp]
    apply (div_le_one (by positivity : (0 : ℝ) < ((2 * N : ℕ) : ℝ))).2
    linarith
  have hexpAlpha :
      Real.exp ((1 - 2 * innerBandScheduleAlpha 0) /
          ((2 * N : ℕ) : ℝ)) ≤ Real.exp 1 := by
    rw [Real.exp_le_exp, halphaComp]
    apply (div_le_one (by positivity : (0 : ℝ) < ((2 * N : ℕ) : ℝ))).2
    norm_num at hcast ⊢
    linarith
  have hdenom :
      (((2 * N : ℕ) : ℝ) / (1 - 2 * innerBandScheduleAlpha 0) + 1) ≤
        4 * Nbar + 1 := by
    rw [halphaComp]
    push_cast
    have hN0 : (0 : ℝ) ≤ N := by positivity
    have hforty : (40 / 13 : ℝ) ≤ 4 := by norm_num
    have hratioN : (N : ℝ) * (40 / 13 : ℝ) ≤ (N : ℝ) * 4 :=
      mul_le_mul_of_nonneg_left hforty hN0
    have hNbar' : (N : ℝ) * 4 ≤ Nbar * 4 := by gcongr
    convert add_le_add_right (hratioN.trans hNbar') 1 using 1 <;> ring
  have hQpow0 : 0 ≤ Q ^ (13 / 20 : ℝ) := Real.rpow_nonneg hQpos.le _
  have hfactor :
      Real.exp Real.pi * Real.log 4 *
          ((2 * T * Real.exp (1 / ((2 * N : ℕ) : ℝ)) / (A : ℝ)) *
            ((sliceA2LadderQ P0 ratio0 eta 0 : ℝ) ^
                (1 - 2 * innerBandScheduleAlpha 0) *
              Real.exp ((1 - 2 * innerBandScheduleAlpha 0) /
                ((2 * N : ℕ) : ℝ))) *
            (((2 * N : ℕ) : ℝ) /
                (1 - 2 * innerBandScheduleAlpha 0) + 1)) ≤
        (T / (A : ℝ)) *
          (Real.exp Real.pi * Real.log 4 *
            (2 * Real.exp 1 * (Q ^ (13 / 20 : ℝ) * Real.exp 1) *
              (4 * Nbar + 1))) := by
    rw [halphaComp]
    change _ ≤ (T / (A : ℝ)) * _
    have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
    have hinner :
        Real.exp Real.pi * Real.log 4 *
            (2 * Real.exp (1 / ((2 * N : ℕ) : ℝ)) *
              (Q ^ (13 / 20 : ℝ) *
                Real.exp ((13 / 20 : ℝ) / ((2 * N : ℕ) : ℝ))) *
              (((2 * N : ℕ) : ℝ) / (13 / 20 : ℝ) + 1)) ≤
          Real.exp Real.pi * Real.log 4 *
            (2 * Real.exp 1 * (Q ^ (13 / 20 : ℝ) * Real.exp 1) *
              (4 * Nbar + 1)) := by
      gcongr
      · simpa [halphaComp] using hexpAlpha
      · simpa [halphaComp] using hdenom
    calc
      Real.exp Real.pi * Real.log 4 *
          ((2 * T * Real.exp (1 / ((2 * N : ℕ) : ℝ)) / (A : ℝ)) *
            (Q ^ (13 / 20 : ℝ) *
              Real.exp ((13 / 20 : ℝ) / ((2 * N : ℕ) : ℝ))) *
            (((2 * N : ℕ) : ℝ) / (13 / 20 : ℝ) + 1)) =
        (T / (A : ℝ)) *
          (Real.exp Real.pi * Real.log 4 *
            (2 * Real.exp (1 / ((2 * N : ℕ) : ℝ)) *
              (Q ^ (13 / 20 : ℝ) *
                Real.exp ((13 / 20 : ℝ) / ((2 * N : ℕ) : ℝ))) *
              (((2 * N : ℕ) : ℝ) / (13 / 20 : ℝ) + 1))) := by ring
      _ ≤ (T / (A : ℝ)) *
          (Real.exp Real.pi * Real.log 4 *
            (2 * Real.exp 1 * (Q ^ (13 / 20 : ℝ) * Real.exp 1) *
              (4 * Nbar + 1))) :=
        mul_le_mul_of_nonneg_left hinner (div_nonneg hT hA0.le)
  calc
    (2 * (sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℝ) *
          (Real.log (sliceA2LadderQ P0 ratio0 eta 0) -
            Real.log (sliceA2LadderP P0 ratio0 eta 0)) + 2) *
        (Real.exp Real.pi * Real.log 4 *
          ((2 * T * Real.exp
              (1 / ((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ)) /
              (A : ℝ)) *
            ((sliceA2LadderQ P0 ratio0 eta 0 : ℝ) ^
                (1 - 2 * innerBandScheduleAlpha 0) *
              Real.exp ((1 - 2 * innerBandScheduleAlpha 0) /
                ((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ))) *
            (((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ) /
                (1 - 2 * innerBandScheduleAlpha 0) + 1))) ≤
        ((2 * Nbar * (R : ℝ) + 2) * Real.log P) *
          ((T / (A : ℝ)) *
            (Real.exp Real.pi * Real.log 4 *
              (2 * Real.exp 1 * (Q ^ (13 / 20 : ℝ) * Real.exp 1) *
                (4 * Nbar + 1)))) := by
      change (2 * (N : ℝ) * _ + 2) * _ ≤ _
      exact mul_le_mul hcell hfactor (by positivity) (by positivity)
    _ = (T / (A : ℝ)) *
          sliceA2OrdinaryZeroFrequencyCoefficient
            P0 ratio0 eta eps rho0 := by
      unfold sliceA2OrdinaryZeroFrequencyCoefficient
      dsimp only
      simp only [Nbar, R, P, Q, Nat.cast_max]
      ring
    _ ≤ _ := hratio

end Tao2015

end MoltResearch
