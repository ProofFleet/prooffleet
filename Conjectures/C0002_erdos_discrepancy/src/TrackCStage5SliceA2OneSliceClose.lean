import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2FactorTwoAggregate
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2LowFit

/-!
# Track R A2-IV-3': close one local slice

All scale-asymptotic hypotheses of the low, inner, outer and conversion
estimates are collected here.  The only remaining height hypotheses are the
bottom frequency fit and the first positive-level reach.
-/

namespace MoltResearch

namespace Tao2015

open Real Finset MeasureTheory ExpSums

/-- At the final parameters the exceptional sharpness is automatically in
the unit range required by the inner capstone. -/
theorem sliceA2ExceptionalEpsilonPrime_le_eight_exp
    (A1 : ℕ) (epsc eps rho0 : ℝ)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hrho0 : 0 ≤ rho0) (hrho1 : rho0 ≤ 1) :
    sliceA2ExceptionalEpsilonPrime A1 epsc eps rho0 ≤ 8 * Real.exp 1 := by
  have hsqrtRho : Real.sqrt rho0 ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hrho1
  have hnum : eps * Real.sqrt rho0 ≤ 1 := by
    calc
      eps * Real.sqrt rho0 ≤ 1 * 1 :=
        mul_le_mul heps1 hsqrtRho (Real.sqrt_nonneg _) (by norm_num)
      _ = 1 := by ring
  have hR : (1 : ℝ) ≤ exceptionalIntervalRatio epsc := by
    exact_mod_cast (show 1 ≤ exceptionalIntervalRatio epsc by
      have := exceptionalIntervalRatio_three_le epsc
      omega)
  have hM : (1 : ℝ) ≤
      sliceA2ExceptionalPrimeCoefficient A1 epsc eps rho0 := by
    unfold sliceA2ExceptionalPrimeCoefficient
    exact le_max_left _ _
  have hsqrtM : 1 ≤ Real.sqrt
      (sliceA2ExceptionalPrimeCoefficient A1 epsc eps rho0) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hM
  have hexp : (1 : ℝ) ≤ Real.exp 13 := Real.one_le_exp (by norm_num)
  have hden : (1 : ℝ) ≤
      8 * Real.exp 13 * (exceptionalIntervalRatio epsc : ℝ) *
        Real.sqrt (sliceA2ExceptionalPrimeCoefficient A1 epsc eps rho0) := by
    calc
      (1 : ℝ) ≤ 8 := by norm_num
      _ ≤ 8 * Real.exp 13 := by nlinarith
      _ ≤ 8 * Real.exp 13 * (exceptionalIntervalRatio epsc : ℝ) :=
        le_mul_of_one_le_right (by positivity) hR
      _ ≤ 8 * Real.exp 13 * (exceptionalIntervalRatio epsc : ℝ) *
          Real.sqrt (sliceA2ExceptionalPrimeCoefficient A1 epsc eps rho0) :=
        le_mul_of_one_le_right (by positivity) hsqrtM
  have hdenPos : 0 <
      8 * Real.exp 13 * (exceptionalIntervalRatio epsc : ℝ) *
        Real.sqrt (sliceA2ExceptionalPrimeCoefficient A1 epsc eps rho0) :=
    zero_lt_one.trans_le hden
  have hquot : eps * Real.sqrt rho0 /
      (8 * Real.exp 13 * (exceptionalIntervalRatio epsc : ℝ) *
        Real.sqrt (sliceA2ExceptionalPrimeCoefficient A1 epsc eps rho0)) ≤ 1 := by
    rw [div_le_one hdenPos]
    exact hnum.trans hden
  unfold sliceA2ExceptionalEpsilonPrime exceptionalEpsilonPrime
  simpa only [Real.sqrt_one, mul_one] using hquot.trans (by
    have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith)

set_option maxHeartbeats 4000000 in
/-- For fixed bottom data satisfying the two height inequalities, the
canonical final level list obeys the explicit one-slice mean-square bound
uniformly in a quadratic scale window. -/
theorem exists_sliceA2_one_slice_closed
    [HalaszLargeValuesAssumption] [PrimeLargeValuesAssumption]
    (epsc eps : ℝ) (H P0 Qlog0 : ℕ) (Amin : ℝ)
    (hepsc : 0 < epsc) (heps : 0 < eps) (hP0 : 21 ≤ P0)
    (hgeom : 100 ≤ sliceA2GeomEps eps * H)
    (hround : 2000 ≤ sliceA2EffectiveEps eps * H)
    (hlipschitz :
      3072000 * (sliceA2Parts eps : ℝ) *
          explicitSliceWindowDerivBound (sliceA2GeomEps eps) ≤
        sliceA2EffectiveEps eps ^ 2 * H)
    (houter :
      4 * sliceA2OuterConstant *
          explicitSliceWindowDerivBound (sliceA2GeomEps eps) ≤
        sliceA2EffectiveEps eps * H)
    (hbottom :
      SliceA2OrdinaryBottomClosed P0 (exceptionalIntervalRatio epsc)
        (sliceA2ExceptionalLadderEta (sliceA2EffectiveEps eps) epsc
          (sliceA2EffectiveEps eps / 100)
          (1 / (4 * sliceA2Parts eps))) Qlog0
        (sliceA2EffectiveEps eps / 100)
        (1 / (4 * sliceA2Parts eps)))
    (hlogFit : ∀ Q : ℕ, Qlog0 ≤ Q →
      Real.log (Q : ℝ) ^ 6 ≤ (Q : ℝ) ^ (1 / 20 : ℝ))
    (hzeroClose : ∀ A : ℕ, ∀ T : ℝ, 1 ≤ A → 0 ≤ T →
      (T / (A : ℝ)) *
          sliceA2OrdinaryZeroFrequencyCoefficient P0
            (exceptionalIntervalRatio epsc)
            (sliceA2ExceptionalLadderEta (sliceA2EffectiveEps eps) epsc
              (sliceA2EffectiveEps eps / 100)
              (1 / (4 * sliceA2Parts eps)))
            (sliceA2EffectiveEps eps / 100)
            (1 / (4 * sliceA2Parts eps)) ≤
        sliceA2KappaMain 0 / 2 *
          ((sliceA2EffectiveEps eps / 100) ^ 2 *
            (1 / (4 * sliceA2Parts eps)) / 8) →
      SliceA2OrdinaryZeroFits P0 (exceptionalIntervalRatio epsc)
        (sliceA2ExceptionalLadderEta (sliceA2EffectiveEps eps) epsc
          (sliceA2EffectiveEps eps / 100)
          (1 / (4 * sliceA2Parts eps))) A
        (sliceA2EffectiveEps eps / 100)
        (1 / (4 * sliceA2Parts eps)) T)
    (hfirst : 1 ≤
      (sliceA2LadderP P0 (exceptionalIntervalRatio epsc)
        (sliceA2ExceptionalLadderEta (sliceA2EffectiveEps eps) epsc
          (sliceA2EffectiveEps eps / 100)
          (1 / (4 * sliceA2Parts eps))) 1 : ℝ) *
        (2 * sliceA2OuterConstant *
          explicitSliceWindowDerivBound (sliceA2GeomEps eps) /
            (sliceA2EffectiveEps eps * H)))
    (hfrequency :
      (sliceA2OuterConstant *
          explicitSliceWindowDerivBound (sliceA2GeomEps eps) /
            (sliceA2EffectiveEps eps * H)) *
        sliceA2OrdinaryZeroFrequencyCoefficient P0
          (exceptionalIntervalRatio epsc)
          (sliceA2ExceptionalLadderEta (sliceA2EffectiveEps eps) epsc
            (sliceA2EffectiveEps eps / 100)
            (1 / (4 * sliceA2Parts eps)))
          (sliceA2EffectiveEps eps / 100)
          (1 / (4 * sliceA2Parts eps)) ≤
      (sliceA2KappaMain 0 / 2 *
        ((sliceA2EffectiveEps eps / 100) ^ 2 *
          (1 / (4 * sliceA2Parts eps)) / 8)) / 2) :
    ∃ A0 : ℝ, 1 ≤ A0 ∧ (sliceA2Parts eps : ℝ) ≤ A0 ∧ Amin ≤ A0 ∧
      ∀ A1 : ℕ, A0 ≤ A1 → ∀ A X : ℕ,
        A1 ≤ A → A ≤ A1 ^ 2 → A ≤ X → X ≤ 2 * A →
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g →
        (∀ n, ‖g n‖ ≤ 1) → g 1 = 1 →
        NonPretentiousAt g A0 (2 * A + 1) →
        ∑ n ∈ Finset.Ioc X (X + A / sliceA2Parts eps),
            ‖∑ m ∈ (Finset.Ioc n (n + H)).filter
                (HasFactorInAll
                  (sliceA2FinalLevels P0 (exceptionalIntervalRatio epsc)
                    (sliceA2ExceptionalLadderEta (sliceA2EffectiveEps eps) epsc
                      (sliceA2EffectiveEps eps / 100)
                      (1 / (4 * sliceA2Parts eps))) A1 epsc (by omega))),
              g m‖ ^ 2 / n ≤
          (sliceA2EffectiveEps eps ^ 2 / 2) * (H : ℝ) ^ 2 *
            ∑ n ∈ Finset.Ioc X (X + A / sliceA2Parts eps),
              (1 : ℝ) / n := by
  let e := sliceA2EffectiveEps eps
  let eb := e / 100
  let M := sliceA2Parts eps
  let rho0 : ℝ := 1 / (4 * M)
  let ratio0 := exceptionalIntervalRatio epsc
  let eta := sliceA2ExceptionalLadderEta e epsc eb rho0
  let c := sliceA2OuterConstant *
    explicitSliceWindowDerivBound (sliceA2GeomEps eps) / (e * H)
  let coeff := sliceA2OrdinaryZeroFrequencyCoefficient
    P0 ratio0 eta eb rho0
  let target := sliceA2KappaMain 0 / 2 * (eb ^ 2 * rho0 / 8)
  obtain ⟨he, he1, heeps⟩ := sliceA2EffectiveEps_bounds eps heps
  have heb : 0 < eb := by dsimp [eb]; positivity
  have hM : 0 < M := by dsimp [M]; exact (sliceA2Parts_bounds eps heps).1
  have hrho : 0 < rho0 := by dsimp [rho0]; positivity
  have heta : 1 ≤ eta := by
    dsimp [eta]
    exact sliceA2ExceptionalLadderEta_one_le e epsc eb rho0
  have hlow : 0 < e := he
  obtain ⟨AW, hAW⟩ := exists_sliceA2WindowClosed eps H heps
    hgeom hround hlipschitz houter
  obtain ⟨AG, hAG⟩ := exists_sliceA2Exceptional_aggregate_closed_uniform_two
    P0 ratio0 e epsc eb rho0 (by omega) hlow heb hrho
  obtain ⟨D, AD, hD, hDeltaClose⟩ := exists_sliceA2Exceptional_delta_bound_two
    P0 ratio0 e epsc eb rho0 (by omega) hlow hepsc heb hrho
  obtain ⟨AS, hAS⟩ := exists_sliceA2Ordinary_scale_margins
    P0 ratio0 eta epsc eb rho0 (by omega) heta heb hrho
  obtain ⟨AR, hAR⟩ := exists_sliceA2ExceptionalLadder_low_remainder
    P0 ratio0 e epsc eb rho0 (by omega) hlow hepsc heb hrho
  obtain ⟨AH, hAH⟩ := exists_sliceA2Exceptional_anchor_margins epsc eb rho0
  obtain ⟨AU, hAU⟩ := exists_sliceA2Exceptional_wide_margins
    epsc eb rho0 heb hrho
  obtain ⟨Dlow, xlow, hDlow, hxlow, hlowFit⟩ :=
    sliceA2_low_band_fit eps heps
  have hcoeff : 0 < coeff := by
    dsimp [coeff]
    exact sliceA2OrdinaryZeroFrequencyCoefficient_pos
      P0 ratio0 eta eb rho0 (by omega) heb hrho
  have htarget : 0 < target := by
    dsimp [target, eb, rho0, sliceA2KappaMain, ordinaryLegShare]
    positivity
  let AF := ⌈4 * coeff / target⌉₊ + 1
  let AN := max M (max (10 ^ 16) (max AW (max AG (max AD (max AS
    (max AR (max AH (max AU (max AF (max xlow (cellHalaszThreshold ^ 2)))))))))))
  let logMargin := Real.log 2 + 12
  let A0 := max (AN : ℝ) (max Amin
    (max 27 (max (18 * D + 18 * logMargin)
      (18 * Dlow + 18 * logMargin))))
  refine ⟨A0, ?_, ?_, ?_, ?_⟩
  · have hAN : 1 ≤ AN := by
      exact (show 1 ≤ M by omega).trans (le_max_left _ _)
    exact (by exact_mod_cast hAN : (1 : ℝ) ≤ AN).trans (le_max_left _ _)
  · exact (by exact_mod_cast (le_max_left M _) : (M : ℝ) ≤ AN) |>.trans
      (le_max_left _ _)
  · exact (le_max_left Amin _).trans (le_max_right _ _)
  intro A1 hA01 A X hA1A hAupper hAX hX2A g hcm hg hg1 hNP
  have hANA1R : (AN : ℝ) ≤ A1 := (le_max_left _ _).trans hA01
  have hANA1 : AN ≤ A1 := by exact_mod_cast hANA1R
  have hlarge : 10 ^ 16 ≤ A1 :=
    (le_max_left (10 ^ 16) _).trans ((le_max_right M _).trans hANA1)
  have hAW1 : AW ≤ A1 := by dsimp [AN] at hANA1; omega
  have hAG1 : AG ≤ A1 := by dsimp [AN] at hANA1; omega
  have hAD1 : AD ≤ A1 := by dsimp [AN] at hANA1; omega
  have hAS1 : AS ≤ A1 := by dsimp [AN] at hANA1; omega
  have hAR1 : AR ≤ A1 := by dsimp [AN] at hANA1; omega
  have hAH1 : AH ≤ A1 := by dsimp [AN] at hANA1; omega
  have hAU1 : AU ≤ A1 := by dsimp [AN] at hANA1; omega
  have hAF1 : AF ≤ A1 := by dsimp [AN] at hANA1; omega
  have hxlowX : xlow ≤ X := by
    have : xlow ≤ A1 := by dsimp [AN] at hANA1; omega
    omega
  have hcellSq : cellHalaszThreshold ^ 2 ≤ X := by
    have : cellHalaszThreshold ^ 2 ≤ A1 := by dsimp [AN] at hANA1; omega
    omega
  have hXlarge : 10 ^ 16 ≤ X := hlarge.trans (hA1A.trans hAX)
  have hXupper : X ≤ 2 * A1 ^ 2 :=
    hX2A.trans (Nat.mul_le_mul_left 2 hAupper)
  have hA0nonneg : 0 ≤ A0 := by
    exact zero_le_one.trans (by
      have hAN : 1 ≤ AN := (show 1 ≤ M by omega).trans (le_max_left _ _)
      exact (by exact_mod_cast hAN : (1 : ℝ) ≤ AN).trans (le_max_left _ _))
  have hA027 : 27 ≤ A0 :=
    (le_max_left 27 _).trans ((le_max_right Amin _).trans (le_max_right _ _))
  have hstrengthD : 18 * D + 18 * logMargin ≤ A0 :=
    (le_max_left _ _).trans ((le_max_right 27 _).trans
      ((le_max_right Amin _).trans (le_max_right _ _)))
  have hstrengthLow : 18 * Dlow + 18 * logMargin ≤ A0 :=
    (le_max_right _ _).trans ((le_max_right 27 _).trans
      ((le_max_right Amin _).trans (le_max_right _ _)))
  have hwindow := hAW A1 A X hAW1 hA1A hAupper hAX hX2A
  rcases hwindow with ⟨hgeomX, hroundX, hlipschitzX, hMA, h3H,
    hcollarSmall, hconversion, hK2X, hK2L, hKK2, htail, htwoT,
    hlogLower, hlogUpper, hDeltaSmall⟩
  let Delta := A / M + 2 * H + 4 * sliceA2Collar (sliceA2GeomEps eps) H
  let K1 := sliceA2LowCutoff eps
  let K2 := sliceA2OuterCutoff eps X H
  let T := K2 + 2
  let J := sliceA2LadderJ P0 ratio0 eta A1 (by omega)
  let levels := sliceA2FinalLevels P0 ratio0 eta A1 epsc (by omega)
  have hX : 0 < X := by omega
  have hH : 0 < H := by
    by_contra! hz
    have : H = 0 := by omega
    subst H
    norm_num at hroundX
  have hDelta : Delta ≤ X := by
    dsimp [Delta, M]
    omega
  have hDelta0 : 0 < Delta := by
    have hs : 0 < A / M := (Nat.one_le_div_iff hM).mpr hMA
    dsimp [Delta]
    omega
  have hT1 : 1 ≤ T := by
    have hK2pos := sliceA2OuterCutoff_pos eps X H heps hX hH
    dsimp [T, K2]
    linarith
  have hTK2 : K2 + 2 ≤ T := by rfl
  have hTA : T ≤ X := by
    dsimp [T, K2] at htwoT ⊢
    linarith
  have htau0 : 0 ≤ 2 * T / (X : ℝ) := by positivity
  have htau : 2 * T / (X : ℝ) ≤ 1 := by
    have hXR : (0 : ℝ) < X := by exact_mod_cast hX
    rw [div_le_one hXR]
    simpa [T, K2] using htwoT
  have hcForm : K2 = c * X := by
    dsimp [K2, c, e]
    unfold sliceA2OuterCutoff
    ring
  have hfirstX : 1 ≤
      (sliceA2LadderP P0 ratio0 eta 1 : ℝ) * (2 * T / (X : ℝ)) := by
    have hXR : (0 : ℝ) < X := by exact_mod_cast hX
    have hratioLower : 2 * c ≤ 2 * T / (X : ℝ) := by
      dsimp [T]
      rw [hcForm]
      have hc0 : 0 ≤ c := by
        have hB0 : 0 ≤
            explicitSliceWindowDerivBound (sliceA2GeomEps eps) := by
          unfold explicitSliceWindowDerivBound
          positivity [one_le_explicitSliceWindowConstant]
        dsimp [c]
        exact div_nonneg
          (mul_nonneg sliceA2OuterConstant_pos.le hB0)
          (mul_nonneg he.le (by exact_mod_cast hH.le))
      field_simp
      nlinarith
    have hP1 : 0 ≤ (sliceA2LadderP P0 ratio0 eta 1 : ℝ) := by positivity
    have hfirst' : 1 ≤
        (sliceA2LadderP P0 ratio0 eta 1 : ℝ) * (2 * c) := by
      convert hfirst using 1 <;> simp only [ratio0, eta, c, e] <;> ring
    exact hfirst'.trans (mul_le_mul_of_nonneg_left hratioLower hP1)
  have hfrequencyTail : (2 / (X : ℝ)) * coeff ≤ target / 2 := by
    have hthreshold : 4 * coeff / target ≤ (X : ℝ) := by
      calc
        4 * coeff / target ≤ (⌈4 * coeff / target⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (AF : ℝ) := by dsimp [AF]; push_cast; linarith
        _ ≤ (A1 : ℝ) := by exact_mod_cast hAF1
        _ ≤ (X : ℝ) := by exact_mod_cast hA1A.trans hAX
    have hXR : (0 : ℝ) < X := by exact_mod_cast hX
    have hraw : 4 * coeff ≤ (X : ℝ) * target :=
      (div_le_iff₀ htarget).1 hthreshold
    rw [show 2 / (X : ℝ) * coeff = (2 * coeff) / X by ring]
    apply (div_le_iff₀ hXR).2
    nlinarith
  have hfrequencyX : (T / (X : ℝ)) * coeff ≤ target := by
    have hshape : T / (X : ℝ) = c + 2 / X := by
      dsimp [T]
      rw [hcForm]
      have hXR : (X : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hshape]
    have hmain : c * coeff ≤ target / 2 := by
      simpa [c, coeff, target, e, eb, rho0, ratio0, eta, M] using hfrequency
    nlinarith
  have hzeroFits : SliceA2OrdinaryZeroFits P0 ratio0 eta X eb rho0 T := by
    apply hzeroClose X T (by omega) (by positivity)
    simpa [ratio0, eta, eb, rho0, coeff, target] using hfrequencyX
  have hscale := hAS A1 X hAS1 (hA1A.trans hAX)
  rcases hscale with ⟨hsep, hdouble, hcollarEndpoint, hcardScale⟩
  have hordinary : SliceA2OrdinaryScheduleClosed g X Delta
      (exceptionalPrimes A1 epsc) P0 ratio0 eta J eb rho0 T K1 K2 := by
    have hbottom' := hbottom
    dsimp only [SliceA2OrdinaryBottomClosed] at hbottom'
    rcases hbottom' with ⟨hlogP0, hfarBottom, hQlog, hcloseBottom,
      hcollisionBottom⟩
    apply sliceA2_ordinary_schedule_closed g hg X Delta
      (exceptionalPrimes A1 epsc) P0 ratio0 eta J Qlog0 hP0
      (by dsimp [J]; exact sliceA2LadderJ_pos P0 ratio0 eta A1 (by omega))
      hDelta eb rho0 (2 * T / X) T K1 K2 heb hrho rfl htau0 htau
      hfirstX hdouble
      (hcollarEndpoint Delta (by simpa [Delta] using hDeltaSmall))
      (by positivity) hTA hTK2
    · have hM30 := (sliceA2Parts_bounds eps heps).2.1
      have hU := sliceA2Collar_bounds (sliceA2GeomEps eps) H
        (sliceA2GeomEps_bounds eps heps).2 (by simpa using hgeomX)
      obtain ⟨hs, hsX, hs30, h3HX, hU', h2UH, hplat, hDeltaX, hrhoX⟩ :=
        sliceA2_floor_width_geometry A X H M
          (sliceA2Collar (sliceA2GeomEps eps) H) hM hM30
          (by simpa [M] using hMA) hAX hX2A h3H hU.1 hU.2.2.2.1 hU.2.2.2.2
      simpa [rho0, Delta, M] using hrhoX
    · exact hzeroFits
    · exact hlogP0
    · exact hfarBottom
    · exact hQlog
    · exact hlogFit
    · exact hcloseBottom
    · simpa [J] using hcardScale
    · exact hcollisionBottom
  have haggregate := hAG g hg A1 X Delta hAG1 (hA1A.trans hAX)
    hXupper hDelta K1 K2 T hT1 hTK2 hTA hlogLower hlogUpper
  have hwide := hAU A1 X hAU1 (hA1A.trans hAX)
  have hanchors := hAH A1 hAH1
  have hDeltaBound := hDeltaClose A1 X Delta hAD1 (hA1A.trans hAX)
    hXupper hDelta
  have hxcut : cellHalaszThreshold ≤ exceptionalSharpCutoff X := by
    have hrad : (cellHalaszThreshold : ℝ) ^ 2 ≤
        3 * (2 * (X : ℝ) + 1) := by
      have hsquare : (cellHalaszThreshold : ℝ) ^ 2 ≤ X := by
        exact_mod_cast hcellSq
      nlinarith
    have hsqrt : (cellHalaszThreshold : ℝ) ≤
        Real.sqrt (3 * (2 * (X : ℝ) + 1)) := by
      apply (Real.le_sqrt (by positivity) (by positivity)).2
      simpa using hrad
    exact_mod_cast hsqrt.trans (exceptionalSharpCutoff_real_lower X)
  have hdeltaOne : sliceA2ExceptionalEpsilonPrime A1 epsc eb rho0 ≤
      8 * Real.exp 1 := by
    apply sliceA2ExceptionalEpsilonPrime_le_eight_exp
    · exact heb.le
    · dsimp [eb, e]
      linarith
    · exact hrho.le
    · dsimp [rho0]
      have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
      have hfourM : (1 : ℝ) ≤ 4 * M := by nlinarith
      exact (div_le_one (by positivity)).2 hfourM
  have hNPinner : NonPretentiousAt g (A0 / 3) (2 * X + 1) :=
    nonPretentiousAt_slice_scale g hg A X A0 hA0nonneg hAX hX2A hNP
  have hNPsharp : NonPretentiousAt g (A0 / 9) (3 * (2 * X + 1)) :=
    nonPretentiousAt_slice_sharp_scale g hg A X A0 hA0nonneg hAX hX2A hNP
  have hband := halaszM_band_le (3 * (2 * X + 1))
    (hXlarge.trans (by omega)) 1 (by norm_num)
  have hband' : 7 *
      (((halaszM (3 * (2 * X + 1)) : ℕ) : ℝ) + 1) ≤
        ((3 * (2 * X + 1) : ℕ) : ℝ) := by simpa only [one_mul] using hband
  have hrangeInner := sliceA2_sharp_range_of_T_le X T A0 hband'
    (by positivity) hTA hA027
  have hstrengthInner := sliceA2_sharp_strength_of_logLoss_le D A0
    (Real.log (Real.log ((3 * (2 * X + 1) : ℕ) : ℝ)) -
      Real.log (Real.log (exceptionalSharpCutoff X : ℝ)) + 12)
    (sliceA2Exceptional_sharp_logLoss_le X (by omega))
    (by simpa [logMargin] using hstrengthD)
  have hinner := sliceA2_inner_band_closed g hcm hg X Delta H P0 ratio0 A1
    e epsc eb rho0 K1 K2 T hP0 hX hH hDelta hlow heb hrho hT1 hTK2
    (by
      have hM30 := (sliceA2Parts_bounds eps heps).2.1
      have hU := sliceA2Collar_bounds (sliceA2GeomEps eps) H
        (sliceA2GeomEps_bounds eps heps).2 (by simpa using hgeomX)
      obtain ⟨hs, hsX, hs30, h3HX, hU', h2UH, hplat, hDeltaX, hrhoX⟩ :=
        sliceA2_floor_width_geometry A X H M
          (sliceA2Collar (sliceA2GeomEps eps) H) hM hM30
          (by simpa [M] using hMA) hAX hX2A h3H hU.1 hU.2.2.2.1 hU.2.2.2.2
      simpa [rho0, Delta, M] using hrhoX)
    (by simpa [ratio0, eta, e, eb, rho0, M, J] using hordinary)
    (by simpa [ratio0, eta, e, eb, rho0, M] using haggregate)
    D (A0 / 3) hD (by linarith) hNPinner
    (by convert hrangeInner using 1 <;> ring)
    (by convert hstrengthInner using 1 <;> ring) hxcut hdeltaOne
    hwide.1 hwide.2.1 hsep hanchors.2.2 hDeltaBound
  have hrem := hAR A1 hAR1 X Delta (hA1A.trans hAX) hDelta
  have hrangeLow := sliceA2_low_sharp_range eps X A0 heps hXlarge hA027
  have hstrengthLow' := sliceA2_sharp_strength_of_logLoss_le Dlow A0
    (Real.log (Real.log ((3 * (2 * X + 1) : ℕ) : ℝ)) -
      Real.log (Real.log (X : ℝ)) + 12)
    (sliceA2_low_sharp_logLoss_le X (by omega))
    (by simpa [logMargin] using hstrengthLow)
  have hlowBand := hlowFit g hcm hg1 hg
    (sliceA2LadderPrimes P0 ratio0 eta) (exceptionalPrimes A1 epsc) J
    (by dsimp [J]; exact sliceA2LadderJ_pos P0 ratio0 eta A1 (by omega))
    (fun p hp => sliceA2LadderPrimes_prime P0 ratio0 eta 0 p hp)
    (fun p hp => exceptionalPrimes_prime A1 epsc p hp)
    A X Delta (by simpa [M] using hMA) hAX hX2A hDelta0 hDelta hxlowX
    A0 (by linarith) hNPsharp Dlow le_rfl hrangeLow hstrengthLow' (by
      simpa [ratio0, eta, e, eb, rho0, M, J] using hrem)
  apply slice_meanSquare_typicalS_le_of_explicit_schedule levels g hg
    A X H eps heps
    (by simpa [M] using hMA) hAX hX2A h3H hgeomX hcollarSmall hroundX
    hlipschitzX hconversion hK2X hK2L hKK2 htail
  · simpa [levels, sliceA2FinalLevels, Delta, M, ratio0, eta, J,
      Nat.add_assoc] using hlowBand
  · intro w hwm hw0 hwsup
    simpa [levels, sliceA2FinalLevels, Delta, M, K1, K2, e, eb, ratio0,
      eta, J, Nat.add_assoc, Nat.cast_add] using
      hinner w hwm hw0 hwsup

end Tao2015

end MoltResearch
