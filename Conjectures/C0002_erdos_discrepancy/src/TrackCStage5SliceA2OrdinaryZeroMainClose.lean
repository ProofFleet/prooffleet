import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryZeroClose

/-!
# Track R A2-V': closed bottom main term

This leaf feeds the packaged numerical pair into the instantiated analytic
level-zero theorem.
-/

namespace MoltResearch

namespace Tao2015

open Finset MeasureTheory ExpSums

theorem sliceA2_level_zero_main_closed
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta : ℕ) (Pu : Finset ℕ) (P0 ratio0 eta J : ℕ)
    (hP0 : 3 ≤ P0) (hJ : 0 < J) (hDelta : Delta ≤ A)
    (eps rho0 T K1 K2 : ℝ)
    (h2qA : ∀ v, 2 * sliceA2OrdinaryRepresentative
      P0 ratio0 eta 0 eps rho0 v ≤ A)
    (hT : 0 < T) (hTK2 : K2 + 2 ≤ T)
    (hratio : rho0 ≤ (Delta : ℝ) / A)
    (hfits : SliceA2OrdinaryZeroFits
      P0 ratio0 eta A eps rho0 T) :
    (∫ xi in bandPartOn
        (levelSmallSet
          (sliceA2LadderPrimes P0 ratio0 eta)
          (fun i => sliceA2OrdinaryN P0 ratio0 eta i eps rho0)
          (fun i => sliceA2OrdinaryV0 P0 ratio0 eta i eps rho0)
          (fun i => sliceA2OrdinaryV1 P0 ratio0 eta i eps rho0)
          g innerBandScheduleAlpha) J
        {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} 0,
      ‖typicalSCellUniformMain g A (A + Delta)
        (sliceA2LadderPrimes P0 ratio0 eta 0)
        (innerBandLevelsBefore (sliceA2LadderPrimes P0 ratio0 eta) J 0 ++
          innerBandLevelsAfter (sliceA2LadderPrimes P0 ratio0 eta) Pu J 0)
        (sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0)
        (sliceA2OrdinaryV0 P0 ratio0 eta 0 eps rho0)
        (sliceA2OrdinaryV1 P0 ratio0 eta 0 eps rho0)
        (sliceA2OrdinaryRepresentative P0 ratio0 eta 0 eps rho0) xi‖ ^ 2) ≤
      sliceA2KappaMain 0 * bandBudget 1 eps ((Delta : ℝ) / A) := by
  rcases hfits with ⟨hfitT, hfitP⟩
  exact sliceA2_level_zero_main g hg A Delta Pu P0 ratio0 eta J
    (by omega) hJ hDelta eps rho0 T K1 K2 h2qA hT hTK2 hratio hfitT hfitP

end Tao2015

end MoltResearch
