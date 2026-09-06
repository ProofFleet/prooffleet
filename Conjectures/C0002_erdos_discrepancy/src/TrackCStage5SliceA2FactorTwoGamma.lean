import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2FactorTwoTail
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2MomentGamma

/-!
# Track R A2-V': exceptional moments on a doubled square window

The high-moment proof only needs the displayed bounds for `log A` and
`log (2T)`.  Stating those inputs directly absorbs the extra factor two
without changing the damping exponent.
-/

namespace MoltResearch

namespace Tao2015

open Filter Finset

/-- Common moment logarithms from direct base-window logarithmic bounds. -/
theorem sliceA2Exceptional_common_log_bounds_of_log_bounds
    (A1 A v : ℕ) (epsc eps rho0 T : ℝ)
    (hX : 1 ≤ Real.log (A1 : ℝ)) (hA : 3 ≤ A) (hT : 1 ≤ T)
    (hv : v ∈ sliceA2ExceptionalI A1 epsc eps rho0)
    (hanchor : 6 ≤ sliceA2ExceptionalAnchor A1 v epsc eps rho0)
    (hlog6 : 2 * Real.log 6 ≤
      Real.log (exceptionalPrimeLower A1 : ℝ))
    (hlogA : Real.log (A : ℝ) ≤ 3 * Real.log (A1 : ℝ))
    (hlogT : Real.log (2 * T) ≤ 3 * Real.log (A1 : ℝ)) :
    let X := Real.log (A1 : ℝ)
    let Z := Real.log X + sliceA2MomentLogConstant epsc
    0 ≤ Z ∧
      Real.log (2 * T) ≤ 3 * X ∧
      (sliceA2ExceptionalMoment A1 v epsc eps rho0 T : ℝ) ≤
        6 * X ^ (1 / 50 : ℝ) + 2 ∧
      Real.log (sliceA2ExceptionalMoment A1 v epsc eps rho0 T : ℝ) ≤ Z ∧
      Real.log (Real.log (2 *
        (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ))) ≤ Z ∧
      Real.log (Real.log (A : ℝ)) ≤ Z ∧
      Real.log (Real.log (2 * T)) ≤ Z := by
  let X := Real.log (A1 : ℝ)
  let C := sliceA2MomentLogConstant epsc
  let Z := Real.log X + C
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg hX
  have hC3 : 3 ≤ C := sliceA2MomentLogConstant_three_le epsc
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hlogTinner : Real.log (2 * T) ≤ 3 * X := by simpa [X] using hlogT
  have hell := sliceA2ExceptionalMoment_cast_le_six_rpow_add_two
    A1 v epsc eps rho0 T hX hT hv hanchor hlog6 hlogTinner
  have hx02 : 1 ≤ X ^ (1 / 50 : ℝ) :=
    Real.one_le_rpow hX (by norm_num)
  have hellEight :
      (sliceA2ExceptionalMoment A1 v epsc eps rho0 T : ℝ) ≤
        8 * X ^ (1 / 50 : ℝ) := by nlinarith
  have hellPos : (0 : ℝ) <
      sliceA2ExceptionalMoment A1 v epsc eps rho0 T := by
    exact_mod_cast (show 0 < sliceA2ExceptionalMoment A1 v epsc eps rho0 T by
      have := sliceA2ExceptionalMoment_one_le A1 v epsc eps rho0 T
      omega)
  have hlogell :
      Real.log (sliceA2ExceptionalMoment A1 v epsc eps rho0 T : ℝ) ≤ Z := by
    calc
      Real.log (sliceA2ExceptionalMoment A1 v epsc eps rho0 T : ℝ) ≤
          Real.log (8 * X ^ (1 / 50 : ℝ)) :=
        Real.log_le_log hellPos hellEight
      _ = Real.log 8 + (1 / 50 : ℝ) * Real.log X := by
        rw [Real.log_mul (by norm_num) (ne_of_gt (by positivity)),
          Real.log_rpow hXpos]
      _ ≤ Real.log X + 3 := by
        have hlog2one : Real.log 2 ≤ 1 :=
          ((Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).2
            Real.exp_one_gt_two).le
        have hlog8 : Real.log 8 ≤ 3 := by
          rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
          norm_num
          nlinarith
        nlinarith
      _ ≤ Z := by dsimp [Z]; linarith
  let B : ℝ := 1 + 3 * (exceptionalIntervalRatio epsc : ℝ)
  have hB1 : 1 ≤ B := by
    dsimp [B]
    have : (0 : ℝ) ≤ exceptionalIntervalRatio epsc := by positivity
    nlinarith
  have hlogAnchorInner := sliceA2Exceptional_log_two_anchor_le
    A1 v epsc eps rho0 hX hv hanchor
  have hlogAnchorPos : 0 < Real.log (2 *
      (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ)) :=
    Real.log_pos (by exact_mod_cast (show 1 < 2 *
      sliceA2ExceptionalAnchor A1 v epsc eps rho0 by omega))
  have hlogAnchor : Real.log (Real.log (2 *
      (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ))) ≤ Z := by
    calc
      Real.log (Real.log (2 *
          (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ))) ≤
          Real.log (B * X) :=
        Real.log_le_log hlogAnchorPos (by simpa [B, X] using hlogAnchorInner)
      _ = Real.log B + Real.log X :=
        Real.log_mul (by positivity) hXpos.ne'
      _ ≤ Z := by
        dsimp [Z, C, sliceA2MomentLogConstant, B]
        linarith
  have hlogApos : 0 < Real.log (A : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hloglogA : Real.log (Real.log (A : ℝ)) ≤ Z := by
    calc
      Real.log (Real.log (A : ℝ)) ≤ Real.log (3 * X) :=
        Real.log_le_log hlogApos (by simpa [X] using hlogA)
      _ = Real.log 3 + Real.log X :=
        Real.log_mul (by norm_num) hXpos.ne'
      _ ≤ Z := by
        have hlog3 : Real.log 3 ≤ 3 := by
          have h3 : Real.log 3 ≤ Real.log 9 :=
            Real.log_le_log (by norm_num) (by norm_num)
          exact h3.trans (log_nine_le.trans (by norm_num))
        dsimp [Z]
        linarith
  have hlogTpos : 0 < Real.log (2 * T) := Real.log_pos (by linarith)
  have hloglogT : Real.log (Real.log (2 * T)) ≤ Z := by
    calc
      Real.log (Real.log (2 * T)) ≤ Real.log (3 * X) :=
        Real.log_le_log hlogTpos hlogTinner
      _ = Real.log 3 + Real.log X :=
        Real.log_mul (by norm_num) hXpos.ne'
      _ ≤ Z := by
        have hlog3 : Real.log 3 ≤ 3 := by
          have h3 : Real.log 3 ≤ Real.log 9 :=
            Real.log_le_log (by norm_num) (by norm_num)
          exact h3.trans (log_nine_le.trans (by norm_num))
        dsimp [Z]
        linarith
  exact ⟨by linarith, hlogTinner, hell, hlogell,
    hlogAnchor, hloglogA, hloglogT⟩

/-- The scalar moment margin closes a cell whenever the two required
window logarithms are supplied directly. -/
theorem sliceA2ExceptionalGamma_fit_of_scalar_margin_of_log_bounds
    (A1 A v : ℕ) (epsc eps rho0 T : ℝ)
    (hX : 1 ≤ Real.log (A1 : ℝ)) (hA : 3 ≤ A) (hT : 1 ≤ T)
    (hv : v ∈ sliceA2ExceptionalI A1 epsc eps rho0)
    (hanchor : 6 ≤ sliceA2ExceptionalAnchor A1 v epsc eps rho0)
    (hlogAnchor : 256 ≤ Real.log
      (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ))
    (hlog6 : 2 * Real.log 6 ≤
      Real.log (exceptionalPrimeLower A1 : ℝ))
    (hlogA : Real.log (A : ℝ) ≤ 3 * Real.log (A1 : ℝ))
    (hlogT : Real.log (2 * T) ≤ 3 * Real.log (A1 : ℝ))
    (hscalar :
      let X := Real.log (A1 : ℝ)
      let C := sliceA2MomentLogConstant epsc
      220 * (6 * X ^ (1 / 50 : ℝ) + 3) *
          (Real.log X + C + 1) ≤ X ^ (9 / 50 : ℝ) / 6) :
    primeHighMomentCountCost
          (sliceA2ExceptionalAnchor A1 v epsc eps rho0)
          (sliceA2ExceptionalMoment A1 v epsc eps rho0 T)
          (eadicCell (exceptionalPrimes A1 epsc)
            (2 * sliceA2ExceptionalN A1 epsc eps rho0) v)
          T (exceptionalSplitThreshold A) 1 *
          (Real.log (2 * T)) ^ 2 ≤
        Real.exp (Real.log
          (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ) /
            (Real.log (2 * T)) ^ primeLargeValuesExponent) := by
  let X := Real.log (A1 : ℝ)
  let C := sliceA2MomentLogConstant epsc
  let Z := Real.log X + C
  let M := 6 * X ^ (1 / 50 : ℝ) + 2
  let P := sliceA2ExceptionalAnchor A1 v epsc eps rho0
  let ell := sliceA2ExceptionalMoment A1 v epsc eps rho0 T
  obtain ⟨hZ, hlogT', hell, hlogell, hlogP, hlogA', hloglogT⟩ :=
    sliceA2Exceptional_common_log_bounds_of_log_bounds
      A1 A v epsc eps rho0 T hX hA hT hv hanchor hlog6 hlogA hlogT
  have hlogTpos : 0 < Real.log (2 * T) := Real.log_pos (by linarith)
  have hhalf := sliceA2Exceptional_halfScaleLog_le_anchor_log
    A1 v epsc eps rho0 hv hanchor hlog6
  have hdamp : X ^ (9 / 50 : ℝ) / 6 ≤
      Real.log (P : ℝ) / (Real.log (2 * T)) ^ primeLargeValuesExponent := by
    apply exceptionalDamping_rpow_lower X (Real.log (P : ℝ))
      (Real.log (2 * T)) hX
    · simpa [X, P] using hhalf
    · exact hlogTpos
    · simpa [X] using hlogT'
  have hcert :
      Real.pi + ((ell : ℝ) + 2) * Real.log 2 +
            2 * (ell : ℝ) * Real.log (ell : ℝ) +
            2 * (Real.log 9 + Real.log (ell : ℝ) +
              Real.log (Real.log (2 * (P : ℝ)))) +
            200 * (ell : ℝ) * Real.log (Real.log (A : ℝ)) +
            2 * Real.log (Real.log (2 * T)) ≤
          Real.log (P : ℝ) /
            (Real.log (2 * T)) ^ primeLargeValuesExponent := by
    apply sliceA2ExceptionalMoment_logCertificate_of_bounds A P ell T M Z
    · simpa [M, X, ell] using hell
    · simpa [Z, X, C] using hZ
    · simpa [Z, X, C, ell] using hlogell
    · simpa [Z, X, C, P] using hlogP
    · simpa [Z, X, C] using hlogA'
    · simpa [Z, X, C] using hloglogT
    · have hs : 220 * (M + 1) * (Z + 1) ≤
        X ^ (9 / 50 : ℝ) / 6 := by
        dsimp [M, Z, X, C]
        convert hscalar using 1 <;> ring
      exact hs.trans hdamp
  apply sliceA2ExceptionalGamma_fit_of_log A A1 v epsc eps rho0 T
    hA hT hv hanchor hlogAnchor
  simpa [P, ell] using hcert

/-- All exceptional Gamma fits are uniform on the doubled window when the
already-available band logarithm is supplied. -/
theorem exists_sliceA2ExceptionalGamma_fit_two
    (epsc eps rho0 : ℝ) :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 →
      1 ≤ Real.log (A1 : ℝ) ∧
      1 ≤ Real.log (exceptionalPrimeLower A1 : ℝ) ∧
      2 * Real.log 6 ≤ Real.log (exceptionalPrimeLower A1 : ℝ) ∧
      (∀ v ∈ sliceA2ExceptionalI A1 epsc eps rho0,
        6 ≤ sliceA2ExceptionalAnchor A1 v epsc eps rho0) ∧
      ∀ A : ℕ, 3 ≤ A → A ≤ 2 * A1 ^ 2 →
        ∀ T : ℝ, 1 ≤ T → T ≤ A →
          Real.log (2 * T) ≤ 3 * Real.log (A1 : ℝ) →
          ∀ v ∈ sliceA2ExceptionalI A1 epsc eps rho0,
            256 ≤ Real.log
              (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ) ∧
            primeHighMomentCountCost
                  (sliceA2ExceptionalAnchor A1 v epsc eps rho0)
                  (sliceA2ExceptionalMoment A1 v epsc eps rho0 T)
                  (eadicCell (exceptionalPrimes A1 epsc)
                    (2 * sliceA2ExceptionalN A1 epsc eps rho0) v)
                  T (exceptionalSplitThreshold A) 1 *
                  (Real.log (2 * T)) ^ 2 ≤
                Real.exp (Real.log
                  (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ) /
                    (Real.log (2 * T)) ^ primeLargeValuesExponent) := by
  let C := sliceA2MomentLogConstant epsc
  obtain ⟨AS, hAS⟩ := exists_sliceA2ExceptionalMoment_scalar_margin C
    (by have := sliceA2MomentLogConstant_three_le epsc; linarith)
  obtain ⟨AA, hAA⟩ := exists_sliceA2Exceptional_anchor_margins epsc eps rho0
  have hevent := tendsto_exceptionalScaleLog.eventually_ge_atTop (512 : ℝ)
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨AR, hAR⟩ := hevent
  refine ⟨max (max AS AA) AR, fun A1 hA1 => ?_⟩
  have hAS1 : AS ≤ A1 := (le_max_left AS AA).trans
    (le_max_left (max AS AA) AR) |>.trans hA1
  have hAA1 : AA ≤ A1 := (le_max_right AS AA).trans
    (le_max_left (max AS AA) AR) |>.trans hA1
  have hAR1 : AR ≤ A1 := (le_max_right (max AS AA) AR).trans hA1
  obtain ⟨hX, hscalar⟩ := hAS A1 hAS1
  obtain ⟨hlog1, hlog6, hanchor⟩ := hAA A1 hAA1
  have hx512 : (512 : ℝ) ≤
      (Real.log (A1 : ℝ)) ^ (49 / 50 : ℝ) := hAR A1 hAR1
  refine ⟨hX, hlog1, hlog6, hanchor, ?_⟩
  intro A hA hAupper T hT hTA hlogT v hv
  let X := Real.log (A1 : ℝ)
  have hA1posNat : 0 < A1 := by
    by_contra hz
    have hz0 : A1 = 0 := Nat.eq_zero_of_not_pos hz
    subst A1
    norm_num at hX
  have hA1pos : (0 : ℝ) < A1 := by
    exact_mod_cast hA1posNat
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hupperR : (A : ℝ) ≤ 2 * (A1 : ℝ) ^ 2 := by exact_mod_cast hAupper
  have hlogA : Real.log (A : ℝ) ≤ 3 * X := by
    have hlogs : Real.log (A : ℝ) ≤ Real.log (2 * (A1 : ℝ) ^ 2) :=
      Real.log_le_log hApos hupperR
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlogs
    have hlog2 : Real.log 2 ≤ X := Real.log_two_lt_d9.le.trans (by linarith)
    norm_num at hlogs
    linarith
  have hhalf := sliceA2Exceptional_halfScaleLog_le_anchor_log
    A1 v epsc eps rho0 hv (hanchor v hv) hlog6
  have hlogAnchor : 256 ≤ Real.log
      (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ) := by
    calc
      (256 : ℝ) ≤ (Real.log (A1 : ℝ)) ^ (49 / 50 : ℝ) / 2 := by linarith
      _ ≤ Real.log (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ) := hhalf
  refine ⟨hlogAnchor, ?_⟩
  exact sliceA2ExceptionalGamma_fit_of_scalar_margin_of_log_bounds
    A1 A v epsc eps rho0 T hX hA hT hv (hanchor v hv) hlogAnchor hlog6
      (by simpa [X] using hlogA) hlogT (by simpa [C] using hscalar)

end Tao2015

end MoltResearch
