import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryZeroEnvelope

/-!
# Track R A2-V': bottom prime-side fit

After fixing the bottom ratio and resolution, the prime-side level-zero
cost is bounded by a constant times `log P0 * P0^(-7/20)`.
-/

namespace MoltResearch

namespace Tao2015

/-- Fixed coefficient in the bottom prime-side main-term envelope. -/
noncomputable def sliceA2OrdinaryZeroPrimeCoefficient
    (ratio0 : ℕ) (eps rho0 : ℝ) : ℝ :=
  let Nbar := sliceA2OrdinaryZeroNBound ratio0 eps rho0
  let R : ℝ := max 2 ratio0
  (2 * Nbar * R + 2) * Real.exp Real.pi * Real.log 4 *
    (8 * Real.exp 1 * (6 * Nbar + 1))

theorem sliceA2OrdinaryZeroPrimeCoefficient_pos
    (ratio0 : ℕ) (eps rho0 : ℝ) (heps : 0 < eps) (hrho0 : 0 < rho0) :
    0 < sliceA2OrdinaryZeroPrimeCoefficient ratio0 eps rho0 := by
  have hN := sliceA2OrdinaryZeroNBound_pos ratio0 eps rho0 heps hrho0
  unfold sliceA2OrdinaryZeroPrimeCoefficient
  dsimp only
  have hR : (0 : ℝ) < max 2 (ratio0 : ℝ) := by positivity
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  positivity

/-- The exact prime-side schedule inequality follows from its one-factor
bottom envelope. -/
theorem sliceA2Ordinary_zero_prime_fit_of_envelope
    (P0 ratio0 eta : ℕ) (eps rho0 : ℝ)
    (hP0 : 3 ≤ P0) (heps : 0 < eps) (hrho0 : 0 < rho0)
    (henvelope :
      sliceA2OrdinaryZeroPrimeCoefficient ratio0 eps rho0 *
          Real.log (P0 : ℝ) * (P0 : ℝ) ^ (-(7 / 20 : ℝ)) ≤
        sliceA2KappaMain 0 / 2 * (eps ^ 2 * rho0 / 8)) :
    (2 * (sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℝ) *
          (Real.log (sliceA2LadderQ P0 ratio0 eta 0) -
            Real.log (sliceA2LadderP P0 ratio0 eta 0)) + 2) *
        (Real.exp Real.pi * Real.log 4 *
          (8 * ((sliceA2LadderP P0 ratio0 eta 0 : ℝ) ^
              (-(2 * innerBandScheduleAlpha 0)) *
            Real.exp (2 * innerBandScheduleAlpha 0 /
              ((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ))) *
            (((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ) /
              (2 * innerBandScheduleAlpha 0) + 1))) ≤
        sliceA2KappaMain 0 / 2 * (eps ^ 2 * rho0 / 8) := by
  let N := sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0
  let Nbar := sliceA2OrdinaryZeroNBound ratio0 eps rho0
  let R := max 2 ratio0
  let P : ℝ := P0
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
  have hR0 : (0 : ℝ) ≤ R := by exact_mod_cast (show 0 ≤ R by omega)
  have hP3 : (3 : ℝ) ≤ P := by
    change (3 : ℝ) ≤ (P0 : ℝ)
    exact_mod_cast hP0
  have hPpos : 0 < P := by linarith
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
    have hlogP0 : 0 ≤ Real.log P := zero_le_one.trans hlogP1
    rw [hlogQ]
    simp only [sliceA2LadderP_zero]
    change (R : ℝ) * Real.log P - Real.log P ≤ (R : ℝ) * Real.log P
    linarith
  have hcell :
      2 * (N : ℝ) *
          (Real.log (sliceA2LadderQ P0 ratio0 eta 0 : ℝ) -
            Real.log (sliceA2LadderP P0 ratio0 eta 0 : ℝ)) + 2 ≤
        (2 * Nbar * (R : ℝ) + 2) * Real.log P := by
    have hwidth0 : 0 ≤
        Real.log (sliceA2LadderQ P0 ratio0 eta 0 : ℝ) -
          Real.log (sliceA2LadderP P0 ratio0 eta 0 : ℝ) := by
      apply sub_nonneg.mpr
      apply Real.log_le_log
      · positivity
      · exact_mod_cast sliceA2LadderP_le_Q P0 ratio0 eta 0
    calc
      2 * (N : ℝ) *
            (Real.log (sliceA2LadderQ P0 ratio0 eta 0 : ℝ) -
              Real.log (sliceA2LadderP P0 ratio0 eta 0 : ℝ)) + 2 ≤
          2 * Nbar * ((R : ℝ) * Real.log P) + 2 := by gcongr
      _ ≤ (2 * Nbar * (R : ℝ) + 2) * Real.log P := by
        nlinarith
  have hexp : Real.exp
      (2 * innerBandScheduleAlpha 0 / ((2 * N : ℕ) : ℝ)) ≤ Real.exp 1 := by
    rw [Real.exp_le_exp, halpha]
    apply (div_le_one (by positivity : (0 : ℝ) < ((2 * N : ℕ) : ℝ))).2
    have hN2 : 2 ≤ N := by
      dsimp [N, sliceA2OrdinaryN, sliceA2LevelN]
      exact le_max_left _ _
    have hcast : (4 : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by
      exact_mod_cast (show 4 ≤ 2 * N by omega)
    norm_num at hcast ⊢
    linarith
  have hdenom :
      (((2 * N : ℕ) : ℝ) / (2 * innerBandScheduleAlpha 0) + 1) ≤
        6 * Nbar + 1 := by
    rw [halpha]
    push_cast
    have hN0 : (0 : ℝ) ≤ N := by positivity
    have hforty : (40 / 7 : ℝ) ≤ 6 := by norm_num
    have hratioN : (N : ℝ) * (40 / 7 : ℝ) ≤ (N : ℝ) * 6 :=
      mul_le_mul_of_nonneg_left hforty hN0
    have hNbar' : (N : ℝ) * 6 ≤ Nbar * 6 := by gcongr
    convert add_le_add_right (hratioN.trans hNbar') 1 using 1 <;> ring
  have hpow :
      (sliceA2LadderP P0 ratio0 eta 0 : ℝ) ^
          (-(2 * innerBandScheduleAlpha 0)) =
        P ^ (-(7 / 20 : ℝ)) := by
    rw [halpha]
    rfl
  have hpow0 : 0 ≤ P ^ (-(7 / 20 : ℝ)) := Real.rpow_nonneg hPpos.le _
  have hmainFactor :
      Real.exp Real.pi * Real.log 4 *
          (8 * ((sliceA2LadderP P0 ratio0 eta 0 : ℝ) ^
              (-(2 * innerBandScheduleAlpha 0)) *
            Real.exp (2 * innerBandScheduleAlpha 0 / ((2 * N : ℕ) : ℝ))) *
            (((2 * N : ℕ) : ℝ) / (2 * innerBandScheduleAlpha 0) + 1)) ≤
        Real.exp Real.pi * Real.log 4 *
          (8 * (P ^ (-(7 / 20 : ℝ)) * Real.exp 1) *
            (6 * Nbar + 1)) := by
    rw [hpow]
    gcongr
  calc
    (2 * (sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℝ) *
          (Real.log (sliceA2LadderQ P0 ratio0 eta 0) -
            Real.log (sliceA2LadderP P0 ratio0 eta 0)) + 2) *
        (Real.exp Real.pi * Real.log 4 *
          (8 * ((sliceA2LadderP P0 ratio0 eta 0 : ℝ) ^
              (-(2 * innerBandScheduleAlpha 0)) *
            Real.exp (2 * innerBandScheduleAlpha 0 /
              ((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ))) *
            (((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ) /
              (2 * innerBandScheduleAlpha 0) + 1))) ≤
        ((2 * Nbar * (R : ℝ) + 2) * Real.log P) *
          (Real.exp Real.pi * Real.log 4 *
            (8 * (P ^ (-(7 / 20 : ℝ)) * Real.exp 1) *
              (6 * Nbar + 1))) := by
      change (2 * (N : ℝ) * _ + 2) * _ ≤ _
      exact mul_le_mul hcell hmainFactor (by positivity) (by positivity)
    _ = sliceA2OrdinaryZeroPrimeCoefficient ratio0 eps rho0 *
          Real.log (P0 : ℝ) * (P0 : ℝ) ^ (-(7 / 20 : ℝ)) := by
      unfold sliceA2OrdinaryZeroPrimeCoefficient
      dsimp only
      simp only [Nbar, R, P, Nat.cast_max]
      ring
    _ ≤ _ := henvelope

end Tao2015

end MoltResearch
