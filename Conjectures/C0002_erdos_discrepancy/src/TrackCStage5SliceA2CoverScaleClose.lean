import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2CoverAnchors

/-!
# Track R A2-V': close the literal exceptional cover scale

The uniform moment envelope, anchor margins, cell count and twenty-fifth
power calculation now discharge the raw cover-scale hypothesis of the
exceptional integer estimate.
-/

namespace MoltResearch

namespace Tao2015

open Finset ExpSums

set_option maxHeartbeats 800000 in
/-- Beyond one schedule threshold, the literal exceptional cover is small
enough throughout every admissible scale and time window. -/
theorem exists_sliceA2ExceptionalCover_scale
    (g : ℕ → ℂ) (hg : ∀ p, ‖g p‖ ≤ 1)
    (P0 ratio0 eta : ℕ) (epsc eps rho0 : ℝ)
    (hP0 : 2 ≤ P0) (heta : 1 ≤ eta) (heps : 0 < eps)
    (hrho0 : 0 < rho0) :
    ∃ A0 : ℕ, ∀ A1 A : ℕ, A0 ≤ A1 → A1 ≤ A →
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
  refine ⟨A0, fun A1 A hA1 hA K1 K2 T hT hTK2 hTA hLlower hLupper => ?_⟩
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

end Tao2015

end MoltResearch
