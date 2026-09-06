import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2FactorTwoGamma
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2UniformAggregate

/-!
# Track R A2-V': exceptional aggregate on a doubled square window

The widened Rankin and Gamma estimates are reassembled into the exact
aggregate interface used by the shifted inner capstone.
-/

namespace MoltResearch

namespace Tao2015

open Finset MeasureTheory ExpSums

set_option maxHeartbeats 800000 in
/-- The exceptional aggregate fits are uniform through `2*A1^2`. -/
theorem exists_sliceA2Exceptional_aggregate_fits_uniform_two
    (Cp : ℝ) (hCp1 : 1 ≤ Cp)
    (P0 ratio0 eta : ℕ) (epsc eps rho0 : ℝ)
    (hP0 : 2 ≤ P0) (heta : 1 ≤ eta) (heps : 0 < eps)
    (hrho0 : 0 < rho0) :
    ∃ A0 : ℕ, ∀ g : ℕ → ℂ, (∀ m, ‖g m‖ ≤ 1) →
      ∀ A1 A Delta : ℕ,
      A0 ≤ A1 → A1 ≤ A → A ≤ 2 * A1 ^ 2 → Delta ≤ A →
      ∀ K1 K2 T tail rem : ℝ,
        1 ≤ T → K2 + 2 ≤ T → T ≤ A →
        Real.log (A1 : ℝ) / 2 ≤ Real.log (2 * T) →
        Real.log (2 * T) ≤ 3 * Real.log (A1 : ℝ) →
        0 ≤ tail → 0 ≤ rem →
        2 * tail + rem ≤
          4 * sliceA2ExceptionalEpsilonPrime Cp A1 epsc eps rho0 *
            Real.exp 13 * (exceptionalIntervalRatio epsc : ℝ) →
        let J := sliceA2LadderJ P0 ratio0 eta A1 hP0
        let d := sliceA2ExceptionalDeltaEnvelope Cp A1 epsc eps rho0 tail rem
        (2 * ((sliceA2ExceptionalI A1 epsc eps rho0).card : ℝ) *
            (∑ v ∈ sliceA2ExceptionalI A1 epsc eps rho0,
              exceptionalIntegerCellCost (exceptionalSplitThreshold A)
                (sliceA2ExceptionalBq A Delta A1 v epsc eps rho0)
                (sliceA2ExceptionalCover g P0 ratio0 eta J A1
                  eps epsc rho0 K1 K2) T
                (sliceA2ExceptionalLogFactor T)
                (sliceA2ExceptionalCoeffMass g A Delta P0 ratio0 eta J A1 v
                  epsc eps rho0)) ≤ eps ^ 2 * rho0 / 64) ∧
        (2 * ((sliceA2ExceptionalI A1 epsc eps rho0).card : ℝ) *
            (∑ v ∈ sliceA2ExceptionalI A1 epsc eps rho0,
              exceptionalPrimeCellCost Cp
                (fun u => eadicCell (exceptionalPrimes A1 epsc)
                  (2 * sliceA2ExceptionalN A1 epsc eps rho0) u)
                (sliceA2ExceptionalAnchor A1 · epsc eps rho0) g (fun _ => d)
                (sliceA2ExceptionalGamma A A1 · epsc eps rho0 T) v) ≤
          eps ^ 2 * rho0 / 64) ∧
        (2 * (2 * replacementEnergyBoundWide A (exceptionalPrimes A1 epsc)
              (sliceA2ExceptionalN A1 epsc eps rho0) T +
            2 * (4 * collisionEnergyBoundWide A
              (exceptionalPrimes A1 epsc) T)) ≤ eps ^ 2 * rho0 / 32) := by
  obtain ⟨AC, hAC⟩ := exists_sliceA2ExceptionalCover_scale_uniform
    P0 ratio0 eta epsc eps rho0 hP0 heta heps hrho0
  obtain ⟨AP, hAP⟩ :=
    exists_sliceA2Exceptional_integer_polylog_margin epsc eps rho0 heps hrho0
  obtain ⟨AW, hAW⟩ :=
    exists_sliceA2Exceptional_wide_margins epsc eps rho0 heps hrho0
  obtain ⟨AG, hAG⟩ := exists_sliceA2ExceptionalGamma_fit_two epsc eps rho0
  let A0 := max 3 (max AC (max AP (max AW AG)))
  refine ⟨A0, fun g hg A1 A Delta hA1 hAlo hAupper hDelta
    K1 K2 T tail rem hT hTK2 hTA hLlower hLupper htail0 hrem0 htail => ?_⟩
  have hA3 : 3 ≤ A := by
    have : 3 ≤ A1 := by dsimp [A0] at hA1; omega
    omega
  have hAC1 : AC ≤ A1 := by dsimp [A0] at hA1; omega
  have hAP1 : AP ≤ A := by
    have : AP ≤ A1 := by dsimp [A0] at hA1; omega
    omega
  have hAW1 : AW ≤ A1 := by dsimp [A0] at hA1; omega
  have hAG1 : AG ≤ A1 := by dsimp [A0] at hA1; omega
  obtain ⟨hQsq, hNuQ, hreplacementCard, hcollisionPrime, hcollisionCard⟩ :=
    hAW A1 A hAW1 hAlo
  obtain ⟨hX, hlog1, hlog6, hanchor, hGammaAll⟩ := hAG A1 hAG1
  have hcover := hAC g hg A1 A hAC1 hAlo K1 K2 T hT hTK2 hTA
    hLlower hLupper
  have hpoly := hAP A hAP1
  have hinteger := sliceA2Exceptional_integer_scale_fit
    g P0 ratio0 eta (sliceA2LadderJ P0 ratio0 eta A1 hP0) A1 A
    epsc eps rho0 K1 K2 T hA3 hT hTA hQsq hlog1 hcover hpoly
  apply sliceA2Exceptional_aggregate_fits Cp hCp1 g hg A Delta P0 ratio0 eta
    (sliceA2LadderJ P0 ratio0 eta A1 hP0) A1 epsc eps rho0 K1 K2 T tail rem
    (by omega) hDelta hQsq hT hTA heps hrho0 htail0 hrem0 hanchor hlog1 hlog6
    hinteger
  · intro v hv
    exact (hGammaAll A hA3 hAupper T hT hTA hLupper v hv).2
  · exact htail
  · exact hreplacementCard
  · exact hcollisionPrime
  · exact hcollisionCard

/-- The specialized aggregate closure is uniform through the doubled
quadratic window. -/
theorem exists_sliceA2Exceptional_aggregate_closed_uniform_two
    (Cp : ℝ) (hCp1 : 1 ≤ Cp)
    (P0 ratio0 : ℕ) (lowBudget epsc eps rho0 : ℝ)
    (hP0 : 3 ≤ P0) (hlow : 0 < lowBudget)
    (heps : 0 < eps) (hrho0 : 0 < rho0) :
    ∃ A0 : ℕ, ∀ g : ℕ → ℂ, (∀ m, ‖g m‖ ≤ 1) →
      ∀ A1 A Delta : ℕ,
      A0 ≤ A1 → A1 ≤ A → A ≤ 2 * A1 ^ 2 → Delta ≤ A →
      ∀ K1 K2 T : ℝ,
        1 ≤ T → K2 + 2 ≤ T → T ≤ A →
        Real.log (A1 : ℝ) / 2 ≤ Real.log (2 * T) →
        Real.log (2 * T) ≤ 3 * Real.log (A1 : ℝ) →
        SliceA2ExceptionalAggregateClosed Cp g A Delta P0 ratio0 A1
          lowBudget epsc eps rho0 K1 K2 T (by omega) := by
  let eta := sliceA2ExceptionalLadderEta Cp lowBudget epsc eps rho0
  have heta : 1 ≤ eta := by
    simpa [eta] using sliceA2ExceptionalLadderEta_one_le
      Cp lowBudget epsc eps rho0
  obtain ⟨A0, hA0⟩ := exists_sliceA2Exceptional_aggregate_fits_uniform_two
    Cp hCp1 P0 ratio0 eta epsc eps rho0 (by omega) heta heps hrho0
  refine ⟨A0, fun g hg A1 A Delta hA1 hA hAupper hDelta
    K1 K2 T hT hTK2 hTA hLlower hLupper => ?_⟩
  let tail := sliceA2ExceptionalTailBudget Cp epsc eps rho0
  let rem := sliceA2ExceptionalLadderBudget Cp lowBudget epsc eps rho0 / 4
  have htail0 : 0 ≤ tail := by
    exact (sliceA2ExceptionalTailBudget_pos Cp epsc eps rho0 heps hrho0).le
  have hrem0 : 0 ≤ rem := by
    dsimp [rem]
    exact div_nonneg
      (sliceA2ExceptionalLadderBudget_pos
        Cp lowBudget epsc eps rho0 hlow heps hrho0).le (by norm_num)
  have hsmall := sliceA2Exceptional_tail_remainder_small
    Cp lowBudget epsc eps rho0 A1
  have hfits := hA0 g hg A1 A Delta hA1 hA hAupper hDelta
    K1 K2 T tail rem hT hTK2 hTA hLlower hLupper htail0 hrem0
    (by simpa [tail, rem] using hsmall)
  simpa [SliceA2ExceptionalAggregateClosed, eta, tail, rem] using hfits

end Tao2015

end MoltResearch
