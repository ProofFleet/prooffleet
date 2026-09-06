import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryParameterBounds

/-!
# Track R A2-V': close the bottom data at one polynomial threshold

The exponent `1200000` records the largest loss in the fixed bottom
ledger.  Its dominant term is the logarithmic not-too-far condition:
`2 * 14 * 40960 = 1146880`.  The twentieth-power close margin costs only
`2560` powers.
-/

namespace MoltResearch

namespace Tao2015

def sliceA2BottomPower : ℕ := 1200000

noncomputable def sliceA2ZeroPrimeTargetConstant : ℝ :=
  sliceA2KappaMain 0 / (16 * 163880000)

noncomputable def sliceA2BottomPowerConstant (Cp epsc : ℝ) (Qlog0 : ℕ) : ℝ :=
  max 21 (max Qlog0
    (max (Real.exp (Real.log 6 + 256))
      (max (Real.exp
        (40960 * (2 * Real.log (sliceA2FarPowerConstant Cp epsc) + 11)))
        (max (sliceA2ClosePowerConstant Cp epsc ^ 20 * (2 : ℝ) ^ 720)
          (max ((160 * 2048 : ℝ) * Real.exp Real.pi * 163880000 / 3)
            ((sliceA2ZeroPrimePowerConstant epsc /
              sliceA2ZeroPrimeTargetConstant) ^ 4))))))

theorem sliceA2ZeroPrimeTargetConstant_pos :
    0 < sliceA2ZeroPrimeTargetConstant := by
  unfold sliceA2ZeroPrimeTargetConstant sliceA2KappaMain ordinaryLegShare
  positivity

theorem sliceA2BottomPowerConstant_pos (Cp epsc : ℝ) (Qlog0 : ℕ) :
    0 < sliceA2BottomPowerConstant Cp epsc Qlog0 := by
  unfold sliceA2BottomPowerConstant
  exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem sliceA2BottomPower_farExponent :
    2 * 14 * 40960 ≤ sliceA2BottomPower := by
  norm_num [sliceA2BottomPower]

theorem sliceA2BottomPower_closeExponent :
    128 * 20 ≤ sliceA2BottomPower := by
  norm_num [sliceA2BottomPower]

theorem sliceA2BottomPower_primeExponent :
    12 * 4 ≤ sliceA2BottomPower := by
  norm_num [sliceA2BottomPower]

set_option maxHeartbeats 1000000 in
/-- One lower bound of size `C(epsc,Qlog0) / e^1200000` supplies the fixed
bottom package and the exact zero-level schedule callback. -/
theorem sliceA2_bottom_closed_of_power
    (Cp epsc eps : ℝ) (P0 Qlog0 : ℕ) (hCp1 : 1 ≤ Cp)
    (hepsc : 0 < epsc) (heps : 0 < eps)
    (hlogFit : ∀ Q : ℕ, Qlog0 ≤ Q →
      Real.log (Q : ℝ) ^ 6 ≤ (Q : ℝ) ^ (1 / 20 : ℝ))
    (hP0 : sliceA2BottomPowerConstant Cp epsc Qlog0 /
        sliceA2EffectiveEps eps ^ sliceA2BottomPower ≤ P0) :
    SliceA2OrdinaryBottomClosed P0 (exceptionalIntervalRatio epsc)
        (sliceA2ExceptionalLadderEta Cp (sliceA2EffectiveEps eps) epsc
          (sliceA2EffectiveEps eps / 100) (sliceA2CanonicalRho eps)) Qlog0
        (sliceA2EffectiveEps eps / 100) (sliceA2CanonicalRho eps) ∧
      ∀ A : ℕ, ∀ T : ℝ, 1 ≤ A → 0 ≤ T →
        (T / (A : ℝ)) *
            sliceA2OrdinaryZeroFrequencyCoefficient P0
              (exceptionalIntervalRatio epsc)
              (sliceA2ExceptionalLadderEta Cp (sliceA2EffectiveEps eps) epsc
                (sliceA2EffectiveEps eps / 100) (sliceA2CanonicalRho eps))
              (sliceA2EffectiveEps eps / 100) (sliceA2CanonicalRho eps) ≤
          sliceA2KappaMain 0 / 2 *
            ((sliceA2EffectiveEps eps / 100) ^ 2 *
              sliceA2CanonicalRho eps / 8) →
        SliceA2OrdinaryZeroFits P0 (exceptionalIntervalRatio epsc)
          (sliceA2ExceptionalLadderEta Cp (sliceA2EffectiveEps eps) epsc
            (sliceA2EffectiveEps eps / 100) (sliceA2CanonicalRho eps)) A
          (sliceA2EffectiveEps eps / 100) (sliceA2CanonicalRho eps) T := by
  let e := sliceA2EffectiveEps eps
  let rho := sliceA2CanonicalRho eps
  let eta := sliceA2ExceptionalLadderEta Cp e epsc (e / 100) rho
  let R := exceptionalIntervalRatio epsc
  let K := sliceA2BottomPower
  let C := sliceA2BottomPowerConstant Cp epsc Qlog0
  let F := sliceA2OrdinaryFarCoefficient R eta
  let D := sliceA2OrdinaryCloseCoefficient R eta (e / 100) rho
  have he : 0 < e := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).1
  have he1 : e ≤ 1 := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).2.1
  have hrho : 0 < rho := by simpa [rho] using sliceA2CanonicalRho_pos eps heps
  have hC : 0 < C := by simpa [C] using sliceA2BottomPowerConstant_pos Cp epsc Qlog0
  have heK : e ^ K ≤ 1 := pow_le_one₀ he.le he1
  have heK0 : 0 < e ^ K := by positivity
  have hP : C / e ^ K ≤ (P0 : ℝ) := by simpa [C, K, e] using hP0
  have hcomponent (x : ℝ) (hx0 : 0 ≤ x) (hxC : x ≤ C) : x ≤ (P0 : ℝ) := by
    have hxDiv : x / e ^ K ≤ C / e ^ K :=
      div_le_div_of_nonneg_right hxC (by positivity)
    have hxx : x ≤ x / e ^ K := by
      rw [le_div_iff₀ heK0]
      exact mul_le_of_le_one_right hx0 heK
    exact hxx.trans (hxDiv.trans hP)
  have hC21 : (21 : ℝ) ≤ C := by
    dsimp [C, sliceA2BottomPowerConstant]
    exact le_max_left _ _
  have hP021R : (21 : ℝ) ≤ P0 := hcomponent 21 (by norm_num) hC21
  have hP021 : 21 ≤ P0 := by exact_mod_cast hP021R
  have hP03 : 3 ≤ P0 := by omega
  have hP0pos : (0 : ℝ) < P0 := by positivity
  have hP01 : (1 : ℝ) ≤ P0 := by exact_mod_cast (show 1 ≤ P0 by omega)
  have hCQ : (Qlog0 : ℝ) ≤ C := by
    dsimp [C, sliceA2BottomPowerConstant]
    exact (le_max_left (Qlog0 : ℝ) _).trans (le_max_right 21 _)
  have hQlogR : (Qlog0 : ℝ) ≤ P0 :=
    hcomponent Qlog0 (by positivity) hCQ
  have hQlog : Qlog0 ≤ P0 := by exact_mod_cast hQlogR
  have hbaseC : Real.exp (Real.log 6 + 256) ≤ C := by
    dsimp [C, sliceA2BottomPowerConstant]
    exact (le_max_left _ _).trans
      ((le_max_right (Qlog0 : ℝ) _).trans (le_max_right 21 _))
  have hbaseP : Real.exp (Real.log 6 + 256) ≤ (P0 : ℝ) :=
    hcomponent _ (Real.exp_pos _).le hbaseC
  have hlogBase : Real.log 6 + 256 ≤ Real.log (P0 : ℝ) := by
    calc
      Real.log 6 + 256 = Real.log (Real.exp (Real.log 6 + 256)) :=
        (Real.log_exp _).symm
      _ ≤ Real.log (P0 : ℝ) := Real.log_le_log (Real.exp_pos _) hbaseP
  have hF : F ≤ sliceA2FarPowerConstant Cp epsc / e ^ 14 := by
    simpa [F, R, eta, e, rho] using
      sliceA2OrdinaryFarCoefficient_le_power Cp epsc eps hCp1 hepsc heps
  have hFpos : 0 < F := by
    dsimp [F, sliceA2OrdinaryFarCoefficient]
    positivity
  have hKFpos : 0 < sliceA2FarPowerConstant Cp epsc :=
    sliceA2FarPowerConstant_pos Cp epsc hCp1
  have hlogF : Real.log F ≤
      Real.log (sliceA2FarPowerConstant Cp epsc) - 14 * Real.log e := by
    have hlog := Real.log_le_log hFpos hF
    rw [Real.log_div (ne_of_gt hKFpos) (ne_of_gt (by positivity : 0 < e ^ 14)),
      Real.log_pow] at hlog
    exact hlog
  let LF := 40960 * (2 * Real.log (sliceA2FarPowerConstant Cp epsc) + 11)
  have hfarC : Real.exp LF ≤ C := by
    dsimp [C, LF, sliceA2BottomPowerConstant]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right (Qlog0 : ℝ) _).trans (le_max_right 21 _)))
  have hfarDiv : Real.exp LF / e ^ K ≤ (P0 : ℝ) :=
    (div_le_div_of_nonneg_right hfarC (by positivity)).trans hP
  have hfarLogP : LF - K * Real.log e ≤ Real.log (P0 : ℝ) := by
    have harg : 0 < Real.exp LF / e ^ K := by positivity
    have hlog := Real.log_le_log harg hfarDiv
    rw [Real.log_div (Real.exp_ne_zero _) (ne_of_gt (by positivity : 0 < e ^ K)),
      Real.log_exp, Real.log_pow] at hlog
    exact hlog
  have hlogE : Real.log e ≤ 0 := Real.log_nonpos he.le he1
  have hfarMargin : 40960 * (2 * Real.log F + 11) ≤ Real.log (P0 : ℝ) := by
    calc
      40960 * (2 * Real.log F + 11) ≤
          LF - (2 * 14 * 40960) * Real.log e := by
        dsimp [LF]
        nlinarith
      _ ≤ LF - K * Real.log e := by
        have hk := sliceA2BottomPower_farExponent
        have hkR : (2 * 14 * 40960 : ℝ) ≤ K := by exact_mod_cast hk
        nlinarith
      _ ≤ Real.log (P0 : ℝ) := hfarLogP
  have hD : D ≤ sliceA2ClosePowerConstant Cp epsc / e ^ 128 := by
    simpa [D, R, eta, e, rho] using
      sliceA2OrdinaryCloseCoefficient_le_power Cp epsc eps hCp1 hepsc heps
  have hD0 : 0 ≤ D := zero_le_one.trans
    (sliceA2OrdinaryCloseCoefficient_one_le R eta (e / 100) rho)
  have hDpow : D ^ 20 ≤
      sliceA2ClosePowerConstant Cp epsc ^ 20 / e ^ (128 * 20) := by
    have hp := pow_le_pow_left₀ hD0 hD 20
    calc
      D ^ 20 ≤ (sliceA2ClosePowerConstant Cp epsc / e ^ 128) ^ 20 := hp
      _ = sliceA2ClosePowerConstant Cp epsc ^ 20 / e ^ (128 * 20) := by
        field_simp
  have hcloseC : sliceA2ClosePowerConstant Cp epsc ^ 20 * (2 : ℝ) ^ 720 ≤ C := by
    dsimp [C, sliceA2BottomPowerConstant]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right (Qlog0 : ℝ) _).trans
        (le_max_right 21 _))))
  have hclose : D ^ 20 * (2 : ℝ) ^ 720 ≤ (P0 : ℝ) := by
    have hexp : 128 * 20 ≤ K := by simpa [K] using sliceA2BottomPower_closeExponent
    have hePow : e ^ K ≤ e ^ (128 * 20) :=
      pow_le_pow_of_le_one he.le he1 hexp
    calc
      D ^ 20 * (2 : ℝ) ^ 720 ≤
          (sliceA2ClosePowerConstant Cp epsc ^ 20 / e ^ (128 * 20)) *
            (2 : ℝ) ^ 720 := by gcongr
      _ = (sliceA2ClosePowerConstant Cp epsc ^ 20 * (2 : ℝ) ^ 720) /
            e ^ (128 * 20) := by ring
      _ ≤ C / e ^ K := by
        exact div_le_div₀ hC.le hcloseC (by positivity) hePow
      _ ≤ (P0 : ℝ) := hP
  have hcollisionC :
      (160 * 2048 : ℝ) * Real.exp Real.pi * 163880000 / 3 ≤ C := by
    dsimp [C, sliceA2BottomPowerConstant]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right (Qlog0 : ℝ) _).trans (le_max_right 21 _)))))
  have hcollisionBase :
      (160 * 2048 : ℝ) * Real.exp Real.pi * 163880000 / 3 ≤ (P0 : ℝ) :=
    hcomponent _ (by positivity) hcollisionC
  have hproductLower : e ^ 4 / 163880000 ≤ (e / 100) ^ 2 * rho := by
    calc
      e ^ 4 / 163880000 = (e / 100) ^ 2 * (e ^ 2 / 16388) := by ring
      _ ≤ (e / 100) ^ 2 * rho := by
        gcongr
        simpa [e, rho] using sliceA2EffectiveEps_sq_le_rho eps heps
  have he4K : e ^ K ≤ e ^ 4 :=
    pow_le_pow_of_le_one he.le he1 (by norm_num [K, sliceA2BottomPower])
  have hcollisionDiv :
      ((160 * 2048 : ℝ) * Real.exp Real.pi * 163880000 / 3) /
          e ^ K ≤ (P0 : ℝ) :=
    (div_le_div_of_nonneg_right hcollisionC (by positivity)).trans hP
  have hcollision : (160 * 2048 : ℝ) * Real.exp Real.pi ≤
      3 * (e / 100) ^ 2 * rho * P0 := by
    calc
      (160 * 2048 : ℝ) * Real.exp Real.pi ≤
          3 * (e ^ K / 163880000) *
            ((((160 * 2048 : ℝ) * Real.exp Real.pi * 163880000 / 3) /
              e ^ K)) := by
        field_simp
        norm_num
      _ ≤
          3 * (e ^ 4 / 163880000) *
            ((((160 * 2048 : ℝ) * Real.exp Real.pi * 163880000 / 3) /
              e ^ K)) := by
        gcongr
      _ ≤ 3 * (e / 100) ^ 2 * rho * P0 := by
        have hleft := mul_le_mul_of_nonneg_left hproductLower (by norm_num : (0 : ℝ) ≤ 3)
        have hmul := mul_le_mul hleft hcollisionDiv (by positivity) (by positivity)
        simpa [mul_assoc] using hmul
  have hzeroConstC :
      (sliceA2ZeroPrimePowerConstant epsc /
        sliceA2ZeroPrimeTargetConstant) ^ 4 ≤ C := by
    dsimp [C, sliceA2BottomPowerConstant]
    exact (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right (Qlog0 : ℝ) _).trans (le_max_right 21 _)))))
  have hzeroDiv :
      ((sliceA2ZeroPrimePowerConstant epsc /
        sliceA2ZeroPrimeTargetConstant) ^ 4) / e ^ K ≤ (P0 : ℝ) :=
    (div_le_div_of_nonneg_right hzeroConstC (by positivity)).trans hP
  have hzeroThreshold :
      (sliceA2ZeroPrimePowerConstant epsc /
        (sliceA2ZeroPrimeTargetConstant * e ^ 12)) ^ 4 ≤ (P0 : ℝ) := by
    have hexp : 12 * 4 ≤ K := by simpa [K] using sliceA2BottomPower_primeExponent
    have hePow : e ^ K ≤ e ^ (12 * 4) :=
      pow_le_pow_of_le_one he.le he1 hexp
    calc
      (sliceA2ZeroPrimePowerConstant epsc /
          (sliceA2ZeroPrimeTargetConstant * e ^ 12)) ^ 4 =
        (sliceA2ZeroPrimePowerConstant epsc /
          sliceA2ZeroPrimeTargetConstant) ^ 4 / e ^ (12 * 4) := by
            field_simp
      _ ≤ (sliceA2ZeroPrimePowerConstant epsc /
          sliceA2ZeroPrimeTargetConstant) ^ 4 / e ^ K := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hePow
      _ ≤ (P0 : ℝ) := hzeroDiv
  have hlogOne : 1 ≤ Real.log (P0 : ℝ) := by
    have hexp : Real.exp 1 < 3 := Real.exp_one_lt_three
    exact (calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.strictMonoOn_log (Real.exp_pos 1) (by norm_num) hexp
      _ ≤ Real.log (P0 : ℝ) := Real.log_le_log (by norm_num)
        (by exact_mod_cast hP03)).le
  have hlogSmall : Real.log (P0 : ℝ) ≤ (P0 : ℝ) ^ (1 / 20 : ℝ) := by
    have hlog6 := hlogFit P0 hQlog
    have hlogLePow : Real.log (P0 : ℝ) ≤ Real.log (P0 : ℝ) ^ 6 := by
      calc
        Real.log (P0 : ℝ) = Real.log (P0 : ℝ) ^ 1 := by simp
        _ ≤ Real.log (P0 : ℝ) ^ 6 := pow_le_pow_right₀ hlogOne (by omega)
    exact hlogLePow.trans hlog6
  let Z := sliceA2ZeroPrimePowerConstant epsc /
    (sliceA2ZeroPrimeTargetConstant * e ^ 12)
  have hZ0 : 0 ≤ Z := by
    dsimp [Z]
    positivity [sliceA2ZeroPrimePowerConstant_pos epsc,
      sliceA2ZeroPrimeTargetConstant_pos]
  have hroot : Z ≤ (P0 : ℝ) ^ (1 / 4 : ℝ) := by
    have hr := Real.rpow_le_rpow (pow_nonneg hZ0 4) hzeroThreshold
      (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹)
    calc
      Z = (Z ^ 4) ^ ((4 : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast hZ0 (by norm_num : (4 : ℕ) ≠ 0)).symm
      _ ≤ (P0 : ℝ) ^ ((4 : ℝ)⁻¹) := hr
      _ = (P0 : ℝ) ^ (1 / 4 : ℝ) := by norm_num
  have hquarter : (P0 : ℝ) ^ (1 / 4 : ℝ) ≤
      (P0 : ℝ) ^ (3 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hP01 (by norm_num)
  have hZ : Z ≤ (P0 : ℝ) ^ (3 / 10 : ℝ) := hroot.trans hquarter
  have hPpowPos : 0 < (P0 : ℝ) ^ (3 / 10 : ℝ) := by positivity
  have hprimeCoeff := sliceA2OrdinaryZeroPrimeCoefficient_le_power epsc eps heps
  have hprimeEnvelope :
      sliceA2OrdinaryZeroPrimeCoefficient R (e / 100) rho *
          Real.log (P0 : ℝ) * (P0 : ℝ) ^ (-(7 / 20 : ℝ)) ≤
        sliceA2KappaMain 0 / 2 * ((e / 100) ^ 2 * rho / 8) := by
    have hdecay : (P0 : ℝ) ^ (1 / 20 : ℝ) *
        (P0 : ℝ) ^ (-(7 / 20 : ℝ)) =
          1 / (P0 : ℝ) ^ (3 / 10 : ℝ) := by
      rw [← Real.rpow_add hP0pos]
      norm_num
      rw [Real.rpow_neg (le_of_lt hP0pos)]
    have hratio : (sliceA2ZeroPrimePowerConstant epsc / e ^ 8) /
          (P0 : ℝ) ^ (3 / 10 : ℝ) ≤
        sliceA2ZeroPrimeTargetConstant * e ^ 4 := by
      rw [div_le_iff₀ hPpowPos]
      dsimp [Z] at hZ
      rw [div_le_iff₀ (by positivity : 0 < e ^ 8)]
      have htarget := (div_le_iff₀
        (mul_pos sliceA2ZeroPrimeTargetConstant_pos (pow_pos he 12))).mp hZ
      calc
        sliceA2ZeroPrimePowerConstant epsc ≤
            (P0 : ℝ) ^ (3 / 10 : ℝ) *
              (sliceA2ZeroPrimeTargetConstant * e ^ 12) := htarget
        _ = (sliceA2ZeroPrimeTargetConstant * e ^ 4 *
            (P0 : ℝ) ^ (3 / 10 : ℝ)) * e ^ 8 := by ring
    calc
      sliceA2OrdinaryZeroPrimeCoefficient R (e / 100) rho *
          Real.log (P0 : ℝ) * (P0 : ℝ) ^ (-(7 / 20 : ℝ)) ≤
        (sliceA2ZeroPrimePowerConstant epsc / e ^ 8) *
          (P0 : ℝ) ^ (1 / 20 : ℝ) *
            (P0 : ℝ) ^ (-(7 / 20 : ℝ)) := by
          gcongr <;> positivity [sliceA2ZeroPrimePowerConstant_pos epsc]
      _ = (sliceA2ZeroPrimePowerConstant epsc / e ^ 8) /
          (P0 : ℝ) ^ (3 / 10 : ℝ) := by
        calc
          (sliceA2ZeroPrimePowerConstant epsc / e ^ 8) *
              (P0 : ℝ) ^ (1 / 20 : ℝ) *
                (P0 : ℝ) ^ (-(7 / 20 : ℝ)) =
            (sliceA2ZeroPrimePowerConstant epsc / e ^ 8) *
              ((P0 : ℝ) ^ (1 / 20 : ℝ) *
                (P0 : ℝ) ^ (-(7 / 20 : ℝ))) := by ring
          _ = _ := by rw [hdecay]; ring
      _ ≤ sliceA2ZeroPrimeTargetConstant * e ^ 4 := hratio
      _ ≤ sliceA2KappaMain 0 / 2 * ((e / 100) ^ 2 * rho / 8) := by
        unfold sliceA2ZeroPrimeTargetConstant
        have hk : 0 ≤ sliceA2KappaMain 0 / 16 := by
          unfold sliceA2KappaMain ordinaryLegShare
          positivity
        have hprod := mul_le_mul_of_nonneg_left hproductLower
          hk
        convert hprod using 1 <;> ring
  have hprimeFit := sliceA2Ordinary_zero_prime_fit_of_envelope
    P0 R eta (e / 100) rho hP03 (by positivity) hrho hprimeEnvelope
  refine ⟨?_, ?_⟩
  · refine ⟨hlogBase, ?_, hQlog, ?_, hcollision⟩
    · simpa [F, R, eta] using hfarMargin
    · simpa [D, R, eta] using hclose
  · intro A T hA hT hfrequency
    exact ⟨sliceA2Ordinary_zero_frequency_fit_of_ratio P0 R eta A
      (e / 100) rho T hP03 hA (by positivity) hrho hT hfrequency,
      hprimeFit⟩

end Tao2015

end MoltResearch
