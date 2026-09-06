import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalFit

/-!
# Track R A2-V'-14: ordinary schedule assembly

Level zero and the later ladder have different proofs, but the shifted
capstone consumes one uniform family.  This leaf performs that final split
and fixes all three ordinary allocations to `ordinaryLegShare`.
-/

namespace MoltResearch

namespace Tao2015

open Finset MeasureTheory ExpSums

/-- Assemble the level-zero and positive-level main bounds, together with
the two wide error families, into the exact ordinary interface of the
shifted sharp-cell capstone. -/
theorem sliceA2_ordinary_schedule
    (g : ℕ → ℂ) (A Delta : ℕ)
    (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ) (J : ℕ)
    (Nl v0l v1l : ℕ → ℕ) (ql : ℕ → ℕ → ℕ)
    (K1 K2 T c3 eps : ℝ)
    (hzero :
      (∫ xi in bandPartOn
          (levelSmallSet Pl Nl v0l v1l g innerBandScheduleAlpha) J
          {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} 0,
        ‖typicalSCellUniformMain g A (A + Delta) (Pl 0)
          (innerBandLevelsBefore Pl J 0 ++ innerBandLevelsAfter Pl Pu J 0)
          (Nl 0) (v0l 0) (v1l 0) (ql 0) xi‖ ^ 2) ≤
        sliceA2KappaMain 0 *
          bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)))
    (hlater : ∀ j, 0 < j → j < J →
      (∫ xi in bandPartOn
          (levelSmallSet Pl Nl v0l v1l g innerBandScheduleAlpha) J
          {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} j,
        ‖typicalSCellUniformMain g A (A + Delta) (Pl j)
          (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j)
          (Nl j) (v0l j) (v1l j) (ql j) xi‖ ^ 2) ≤
        sliceA2KappaMain j *
          bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)))
    (hreplacement : ∀ j < J,
      2 * replacementEnergyBoundWide A (Pl j) (Nl j) T ≤
        sliceA2KappaReplacement j *
          bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)))
    (hcollision : ∀ j < J,
      8 * collisionEnergyBoundWide A (Pl j) T ≤
        sliceA2KappaCollision j *
          bandBudget c3 eps ((Delta : ℝ) / (A : ℝ))) :
    (∀ j < J,
      (∫ xi in bandPartOn
          (levelSmallSet Pl Nl v0l v1l g innerBandScheduleAlpha) J
          {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} j,
        ‖typicalSCellUniformMain g A (A + Delta) (Pl j)
          (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j)
          (Nl j) (v0l j) (v1l j) (ql j) xi‖ ^ 2) ≤
        sliceA2KappaMain j *
          bandBudget c3 eps ((Delta : ℝ) / (A : ℝ))) ∧
      (∀ j < J,
        2 * replacementEnergyBoundWide A (Pl j) (Nl j) T ≤
          sliceA2KappaReplacement j *
            bandBudget c3 eps ((Delta : ℝ) / (A : ℝ))) ∧
      (∀ j < J,
        8 * collisionEnergyBoundWide A (Pl j) T ≤
          sliceA2KappaCollision j *
            bandBudget c3 eps ((Delta : ℝ) / (A : ℝ))) ∧
      (∀ j < J,
        2 * sliceA2KappaMain j + 2 * sliceA2KappaReplacement j +
            2 * sliceA2KappaCollision j ≤ (1 : ℝ) / 2 ^ (j + 2)) := by
  refine ⟨?_, hreplacement, hcollision, fun j _ => sliceA2Kappa_share_fit j⟩
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact hzero
  · exact hlater j hj0 hj

end Tao2015

end MoltResearch
