import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2CoverScalar
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2BrunGrowth

/-!
# Track R A2-V': uniform last-level cover envelopes

The selected ladder growth theorem and the scalar remainder threshold now
give the `23/50` logarithmic moment bound simultaneously on all cells of the
last ordinary level.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- Beyond one threshold, any time scale whose logarithm lies in the natural
window `[log A1 / 2, 3 log A1]` has the required last-level cell envelopes. -/
theorem exists_sliceA2OrdinaryCover_logEnvelopes
    (P0 ratio0 eta : ℕ) (epsc eps rho0 : ℝ)
    (hP0 : 2 ≤ P0) (heta : 1 ≤ eta) :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 →
      let J := sliceA2LadderJ P0 ratio0 eta A1 hP0
      0 < J ∧
      ∀ T : ℝ, 1 ≤ T →
        Real.log (A1 : ℝ) / 2 ≤ Real.log (2 * T) →
        Real.log (2 * T) ≤ 3 * Real.log (A1 : ℝ) →
        ∀ r ∈ Finset.Ico
          (sliceA2OrdinaryV0 P0 ratio0 eta (J - 1) eps rho0)
          (sliceA2OrdinaryV1 P0 ratio0 eta (J - 1) eps rho0 + 1),
          sliceA2MomentLogEnvelope
              (sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r)
              (sliceA2OrdinaryCoverMoment P0 ratio0 eta J eps rho0 T r)
              (sliceA2OrdinaryCoverWeight P0 ratio0 eta J r eps rho0) ≤
            (23 / 50 : ℝ) * Real.log (2 * T) := by
  obtain ⟨AS, hAS⟩ := exists_sliceA2Cover_scalar_margins
  obtain ⟨AB, hAB⟩ :=
    exists_sliceA2Ladder_brunGrowthMargins P0 ratio0 eta epsc hP0 heta
  refine ⟨max AS AB, fun A1 hA1 => ?_⟩
  have hAS1 : AS ≤ A1 := (le_max_left AS AB).trans hA1
  have hAB1 : AB ≤ A1 := (le_max_right AS AB).trans hA1
  obtain ⟨hX, hlogX, hremX⟩ := hAS A1 hAS1
  obtain ⟨hn, hQ, hdepth, hbrun⟩ := hAB A1 hAB1
  let J := sliceA2LadderJ P0 ratio0 eta A1 hP0
  have hJ : 0 < J := by
    dsimp [J]
    exact sliceA2LadderJ_pos P0 ratio0 eta A1 hP0
  refine ⟨hJ, fun T hT hLlower hLupper r hr => ?_⟩
  apply sliceA2OrdinaryCover_logEnvelope_of_last_level
    P0 ratio0 eta J A1 r eps rho0 T hP0 hJ hr hT hX hlogX
  · simpa [J] using sliceA2LadderJ_last_reaches
      P0 ratio0 eta A1 hP0
  · simpa [J] using hQ
  · exact hLlower
  · exact hLupper
  · exact hremX

end Tao2015

end MoltResearch
