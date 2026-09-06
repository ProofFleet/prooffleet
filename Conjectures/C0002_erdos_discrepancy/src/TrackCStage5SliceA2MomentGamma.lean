import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2MomentWindows

/-!
# Track R A2-V': close the exceptional Gamma factor

The scalar `23/100` margin and the common window logarithm now discharge the
literal damped high-moment inequality.  A single eventual threshold supplies
it simultaneously for every remote cell and every scale in the square
window.
-/

namespace MoltResearch

namespace Tao2015

open Filter Finset

/-- The explicit scalar margin closes one literal remote-cell Gamma fit. -/
theorem sliceA2ExceptionalGamma_fit_of_scalar_margin
    (A1 A v : ℕ) (epsc eps rho0 T : ℝ)
    (hX : 1 ≤ Real.log (A1 : ℝ)) (hA : 3 ≤ A)
    (hAA1 : A ≤ A1 ^ 2) (hT : 1 ≤ T) (hTA : T ≤ A)
    (hv : v ∈ sliceA2ExceptionalI A1 epsc eps rho0)
    (hanchor : 6 ≤ sliceA2ExceptionalAnchor A1 v epsc eps rho0)
    (hlogAnchor : 256 ≤ Real.log
      (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ))
    (hlog6 : 2 * Real.log 6 ≤
      Real.log (exceptionalPrimeLower A1 : ℝ))
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
  obtain ⟨hZ, hlogT, hell, hlogell, hlogP, hlogA, hloglogT⟩ :=
    sliceA2Exceptional_common_log_bounds A1 A v epsc eps rho0 T
      hX hA hAA1 hT hTA hv hanchor hlog6
  have hlogTpos : 0 < Real.log (2 * T) := Real.log_pos (by linarith)
  have hhalf := sliceA2Exceptional_halfScaleLog_le_anchor_log
    A1 v epsc eps rho0 hv hanchor hlog6
  have hdamp : X ^ (9 / 50 : ℝ) / 6 ≤
      Real.log (P : ℝ) / (Real.log (2 * T)) ^ primeLargeValuesExponent := by
    apply exceptionalDamping_rpow_lower X (Real.log (P : ℝ))
      (Real.log (2 * T)) hX
    · simpa [X, P] using hhalf
    · exact hlogTpos
    · simpa [X] using hlogT
  have hcert :
      Real.pi + ((ell : ℝ) + 2) * Real.log 2 +
            2 * (ell : ℝ) * Real.log (ell : ℝ) +
            2 * (Real.log 9 + Real.log (ell : ℝ) +
              Real.log (Real.log (2 * (P : ℝ)))) +
            200 * (ell : ℝ) * Real.log (Real.log (A : ℝ)) +
            2 * Real.log (Real.log (2 * T)) ≤
          Real.log (P : ℝ) /
            (Real.log (2 * T)) ^ primeLargeValuesExponent := by
    apply sliceA2ExceptionalMoment_logCertificate_of_bounds
      A P ell T M Z
    · simpa [M, X, ell] using hell
    · simpa [Z, X, C] using hZ
    · simpa [Z, X, C, ell] using hlogell
    · simpa [Z, X, C, P] using hlogP
    · simpa [Z, X, C] using hlogA
    · simpa [Z, X, C] using hloglogT
    · have hs : 220 * (M + 1) * (Z + 1) ≤
      X ^ (9 / 50 : ℝ) / 6 := by
        dsimp [M, Z, X, C]
        convert hscalar using 1 <;> ring
      exact hs.trans hdamp
  apply sliceA2ExceptionalGamma_fit_of_log A A1 v epsc eps rho0 T
    hA hT hv hanchor hlogAnchor
  simpa [P, ell] using hcert

/-- The defining exceptional logarithmic scale tends to infinity. -/
theorem tendsto_exceptionalScaleLog :
    Filter.Tendsto
      (fun A1 : ℕ => (Real.log (A1 : ℝ)) ^ (49 / 50 : ℝ))
      Filter.atTop Filter.atTop := by
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 49 / 50)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- Beyond one base threshold, all elementary anchor margins and every
literal remote Gamma fit hold uniformly throughout the square window. -/
theorem exists_sliceA2ExceptionalGamma_fit
    (epsc eps rho0 : ℝ) :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 →
      1 ≤ Real.log (A1 : ℝ) ∧
      1 ≤ Real.log (exceptionalPrimeLower A1 : ℝ) ∧
      2 * Real.log 6 ≤ Real.log (exceptionalPrimeLower A1 : ℝ) ∧
      (∀ v ∈ sliceA2ExceptionalI A1 epsc eps rho0,
        6 ≤ sliceA2ExceptionalAnchor A1 v epsc eps rho0) ∧
      ∀ A : ℕ, 3 ≤ A → A ≤ A1 ^ 2 →
        ∀ T : ℝ, 1 ≤ T → T ≤ A →
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
    (by
      have := sliceA2MomentLogConstant_three_le epsc
      linarith)
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
  intro A hA hAupper T hT hTA v hv
  have hhalf := sliceA2Exceptional_halfScaleLog_le_anchor_log
    A1 v epsc eps rho0 hv (hanchor v hv) hlog6
  have hlogAnchor : 256 ≤ Real.log
      (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ) := by
    calc
      (256 : ℝ) ≤
          (Real.log (A1 : ℝ)) ^ (49 / 50 : ℝ) / 2 := by linarith
      _ ≤ Real.log
          (sliceA2ExceptionalAnchor A1 v epsc eps rho0 : ℝ) := hhalf
  refine ⟨hlogAnchor, ?_⟩
  exact sliceA2ExceptionalGamma_fit_of_scalar_margin
    A1 A v epsc eps rho0 T hX hA hAupper hT hTA hv
      (hanchor v hv) hlogAnchor hlog6 (by simpa [C] using hscalar)

end Tao2015

end MoltResearch
