import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalAggregateClose
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2BottomClose

/-!
# Track R A2-V': uniform exceptional aggregate threshold

The exceptional cover estimates use the completely multiplicative function
only through its unit norm bound.  Choosing every scalar threshold first
therefore gives the quantifier order required by `SliceMeanSquareA2`.
-/

namespace MoltResearch

namespace Tao2015

open Finset MeasureTheory ExpSums

set_option maxHeartbeats 800000 in
/-- The exceptional cover threshold can be chosen before the bounded
completely multiplicative function. -/
theorem exists_sliceA2ExceptionalCover_scale_uniform
    (P0 ratio0 eta : ℕ) (epsc eps rho0 : ℝ)
    (hP0 : 2 ≤ P0) (heta : 1 ≤ eta) (heps : 0 < eps)
    (hrho0 : 0 < rho0) :
    ∃ A0 : ℕ, ∀ g : ℕ → ℂ, (∀ p, ‖g p‖ ≤ 1) →
      ∀ A1 A : ℕ, A0 ≤ A1 → A1 ≤ A →
      ∀ K1 K2 T : ℝ, 1 ≤ T → K2 + 2 ≤ T → T ≤ A →
        Real.log (A1 : ℝ) / 2 ≤ Real.log (2 * T) →
        Real.log (2 * T) ≤ 3 * Real.log (A1 : ℝ) →
        sliceA2ExceptionalCover g P0 ratio0 eta
            (sliceA2LadderJ P0 ratio0 eta A1 hP0) A1
            eps epsc rho0 K1 K2 * Real.sqrt T *
              (exceptionalPrimeUpper A1 epsc : ℝ) ≤ A := by
  obtain ⟨AE, hAE⟩ := exists_sliceA2OrdinaryCover_logEnvelopes
    P0 ratio0 eta epsc eps rho0 hP0 heta
  obtain ⟨AA, hAA⟩ := exists_sliceA2Ordinary_last_anchor_margins
    P0 ratio0 eta eps rho0 hP0
  obtain ⟨AC, hAC⟩ :=
    exists_sliceA2Ordinary_last_cell_card_le_exceptionalPrimeUpper
      P0 ratio0 eta epsc eps rho0 hP0 heta heps hrho0
  obtain ⟨AS, hAS⟩ := exists_sliceA2ExceptionalCover_scale_margin epsc
  let A0 := max AE (max AA (max AC AS))
  refine ⟨A0, fun g hg A1 A hA1 hA K1 K2 T hT hTK2 hTA
    hLlower hLupper => ?_⟩
  have hAE1 : AE ≤ A1 := (le_max_left AE (max AA (max AC AS))).trans hA1
  have hAA1 : AA ≤ A1 := (le_max_left AA (max AC AS)).trans
    ((le_max_right AE (max AA (max AC AS))).trans hA1)
  have hAC1 : AC ≤ A1 := (le_max_left AC AS).trans
    ((le_max_right AA (max AC AS)).trans
      ((le_max_right AE (max AA (max AC AS))).trans hA1))
  have hAS1 : AS ≤ A1 := (le_max_right AC AS).trans
    ((le_max_right AA (max AC AS)).trans
      ((le_max_right AE (max AA (max AC AS))).trans hA1))
  let J := sliceA2LadderJ P0 ratio0 eta A1 hP0
  obtain ⟨hJ, hlog⟩ := hAE A1 hAE1
  obtain ⟨hJA, hanchors⟩ := hAA A1 hAA1
  have hcard := hAC A1 hAC1
  have hrawScale :
      2 * ((Finset.Ico
          (sliceA2OrdinaryV0 P0 ratio0 eta (J - 1) eps rho0)
          (sliceA2OrdinaryV1 P0 ratio0 eta (J - 1) eps rho0 + 1)).card : ℝ) *
          Real.exp ((23 / 50 : ℝ) * Real.log (2 * T)) * Real.sqrt T *
            (exceptionalPrimeUpper A1 epsc : ℝ) ≤ A := by
    apply hAS A1 A hAS1 hA T
      ((Finset.Ico
        (sliceA2OrdinaryV0 P0 ratio0 eta (J - 1) eps rho0)
        (sliceA2OrdinaryV1 P0 ratio0 eta (J - 1) eps rho0 + 1)).card : ℝ)
      hT hTA
    simpa [J] using hcard
  apply sliceA2ExceptionalCover_scale_of_log g hg P0 ratio0 eta J A1 A
    eps epsc rho0 K1 K2 T ((23 / 50 : ℝ) * Real.log (2 * T))
    hP0 (by simpa [J] using hJ) hT hTK2
  · intro r hr
    exact (hanchors r (by simpa [J] using hr)).1
  · intro r hr
    exact (hanchors r (by simpa [J] using hr)).2
  · intro r hr
    simpa [J, sliceA2OrdinaryCoverWeight] using
      hlog T hT hLlower hLupper r (by simpa [J] using hr)
  · simpa [J] using hrawScale

set_option maxHeartbeats 800000 in
/-- All three exceptional aggregate fits admit a common threshold chosen
uniformly before `g`. -/
theorem exists_sliceA2Exceptional_aggregate_fits_uniform
    (P0 ratio0 eta : ℕ) (epsc eps rho0 : ℝ)
    (hP0 : 2 ≤ P0) (heta : 1 ≤ eta) (heps : 0 < eps)
    (hrho0 : 0 < rho0) :
    ∃ A0 : ℕ, ∀ g : ℕ → ℂ, (∀ m, ‖g m‖ ≤ 1) →
      ∀ A1 A Delta : ℕ,
      A0 ≤ A1 → A1 ≤ A → A ≤ A1 ^ 2 → Delta ≤ A →
      ∀ K1 K2 T tail rem : ℝ,
        1 ≤ T → K2 + 2 ≤ T → T ≤ A →
        Real.log (A1 : ℝ) / 2 ≤ Real.log (2 * T) →
        Real.log (2 * T) ≤ 3 * Real.log (A1 : ℝ) →
        0 ≤ tail → 0 ≤ rem →
        2 * tail + rem ≤
          4 * sliceA2ExceptionalEpsilonPrime A1 epsc eps rho0 *
            Real.exp 13 * (exceptionalIntervalRatio epsc : ℝ) →
        let J := sliceA2LadderJ P0 ratio0 eta A1 hP0
        let d := sliceA2ExceptionalDeltaEnvelope A1 epsc eps rho0 tail rem
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
              exceptionalPrimeCellCost
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
  obtain ⟨AG, hAG⟩ := exists_sliceA2ExceptionalGamma_fit epsc eps rho0
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
  apply sliceA2Exceptional_aggregate_fits g hg A Delta P0 ratio0 eta
    (sliceA2LadderJ P0 ratio0 eta A1 hP0) A1 epsc eps rho0 K1 K2 T tail rem
    (by omega) hDelta hQsq hT hTA heps hrho0 htail0 hrem0 hanchor hlog1 hlog6
    hinteger
  · intro v hv
    exact (hGammaAll A hA3 hAupper T hT hTA v hv).2
  · exact htail
  · exact hreplacementCard
  · exact hcollisionPrime
  · exact hcollisionCard

/-- The final exceptional aggregate threshold is independent of the
bounded completely multiplicative function. -/
theorem exists_sliceA2Exceptional_aggregate_closed_uniform
    (P0 ratio0 : ℕ) (lowBudget epsc eps rho0 : ℝ)
    (hP0 : 3 ≤ P0) (hlow : 0 < lowBudget)
    (heps : 0 < eps) (hrho0 : 0 < rho0) :
    ∃ A0 : ℕ, ∀ g : ℕ → ℂ, (∀ m, ‖g m‖ ≤ 1) →
      ∀ A1 A Delta : ℕ,
      A0 ≤ A1 → A1 ≤ A → A ≤ A1 ^ 2 → Delta ≤ A →
      ∀ K1 K2 T : ℝ,
        1 ≤ T → K2 + 2 ≤ T → T ≤ A →
        Real.log (A1 : ℝ) / 2 ≤ Real.log (2 * T) →
        Real.log (2 * T) ≤ 3 * Real.log (A1 : ℝ) →
        SliceA2ExceptionalAggregateClosed g A Delta P0 ratio0 A1
          lowBudget epsc eps rho0 K1 K2 T (by omega) := by
  let eta := sliceA2ExceptionalLadderEta lowBudget epsc eps rho0
  have heta : 1 ≤ eta := by
    simpa [eta] using sliceA2ExceptionalLadderEta_one_le
      lowBudget epsc eps rho0
  obtain ⟨A0, hA0⟩ := exists_sliceA2Exceptional_aggregate_fits_uniform
    P0 ratio0 eta epsc eps rho0 (by omega) heta heps hrho0
  refine ⟨A0, fun g hg A1 A Delta hA1 hA hAupper hDelta
    K1 K2 T hT hTK2 hTA hLlower hLupper => ?_⟩
  let tail := sliceA2ExceptionalTailBudget epsc eps rho0
  let rem := sliceA2ExceptionalLadderBudget lowBudget epsc eps rho0 / 4
  have htail0 : 0 ≤ tail := by
    exact (sliceA2ExceptionalTailBudget_pos epsc eps rho0 heps hrho0).le
  have hrem0 : 0 ≤ rem := by
    dsimp [rem]
    exact div_nonneg
      (sliceA2ExceptionalLadderBudget_pos
        lowBudget epsc eps rho0 hlow heps hrho0).le (by norm_num)
  have hsmall := sliceA2Exceptional_tail_remainder_small
    lowBudget epsc eps rho0 A1
  have hfits := hA0 g hg A1 A Delta hA1 hA hAupper hDelta
    K1 K2 T tail rem hT hTK2 hTA hLlower hLupper htail0 hrem0
    (by simpa [tail, rem] using hsmall)
  simpa [SliceA2ExceptionalAggregateClosed, eta, tail, rem] using hfits

end Tao2015

end MoltResearch
