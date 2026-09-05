import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5InnerBandAssembly
import MoltResearch.Discrepancy.WideLevelErrorLegs

/-!
# Wide-polynomial inner-band wrappers

This file exposes the one-polynomial replacement and collision estimates at
the Stage 5 inner-band interface.  It deliberately leaves the scale-only
representative variants to the separate cell-representative layer.
-/

namespace MoltResearch

open Finset Set

namespace Tao2015

open MeasureTheory in
/-- The cell-replacement contribution of an ordinary level, priced by the
single wide Dirichlet polynomial. -/
theorem innerBand_replacement_leg_wide
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta : ℕ) (hA : 1 ≤ A) (hDeltaA : Delta ≤ A)
    (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ)
    (Nl v₀l v₁l : ℕ → ℕ) (ql : ℕ → ℕ → ℕ) (alpha : ℕ → ℝ)
    (J j : ℕ) (hNj : 0 < Nl j)
    (hPlj : ∀ p ∈ Pl j, p.Prime)
    (hcov : (Finset.Ico (v₀l j) (v₁l j + 1)).biUnion
      (eadicCell (Pl j) (2 * Nl j)) = Pl j)
    (hqup : ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      (ql j v : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (Nl j : ℝ))))
    (hq1 : ∀ v, 1 ≤ ql j v)
    (hqmin : ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v, ql j v ≤ p)
    (hqratio : ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
        Nl j * p ≤ (Nl j + 1) * ql j v)
    (K₁ K₂ T : ℝ) (hT : 0 < T) (hTK₂ : K₂ + 2 ≤ T)
    (c₃ eps kappa : ℝ)
    (hfitWide : 2 * replacementEnergyBoundWide A (Pl j) (Nl j) T
      ≤ kappa * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))) :
    2 * (∫ xi in bandPartOn (levelSmallSet Pl Nl v₀l v₁l g alpha) J
        {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
      ‖typicalSCellReplacement g A (A + Delta) (Pl j)
        (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j)
        (Nl j) (v₀l j) (v₁l j) (ql j) xi‖ ^ 2)
      ≤ kappa * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
  have _hscale := hqup
  let G := bandPartOn (levelSmallSet Pl Nl v₀l v₁l g alpha) J
    {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j
  have hGT : G ⊆ Set.Ioc (-T) T :=
    innerBandPartOn_subset_Ioc _ J j K₁ K₂ T hTK₂
  have hwide := setIntegral_norm_sq_typicalSCellReplacement_wide_le
    g hg A (A + Delta) hA (Nat.le_add_right A Delta) (by omega)
    (Pl j) hPlj
    (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j)
    (Nl j) (v₀l j) (v₁l j) hNj hcov (ql j) hq1 hqmin hqratio T hT G hGT
  linarith

open MeasureTheory in
/-- A scheduled ordinary level assembled using the single-polynomial
collision envelope. -/
theorem innerBand_level_leg_of_main_wide
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta H : ℕ) (hA : 1 ≤ A) (hDeltaA : Delta ≤ A)
    (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ) (J j : ℕ) (hjJ : j < J)
    (hPl : ∀ i < J, ∀ p ∈ Pl i, p.Prime)
    (hPu : ∀ p ∈ Pu, p.Prime)
    (hdisj : ∀ i < J, ∀ k < J, i ≠ k → Disjoint (Pl i) (Pl k))
    (hdisjU : ∀ i < J, Disjoint (Pl i) Pu)
    (Nl v₀l v₁l : ℕ → ℕ)
    (hcov : (Finset.Ico (v₀l j) (v₁l j + 1)).biUnion
      (eadicCell (Pl j) (2 * Nl j)) = Pl j)
    (ql : ℕ → ℕ → ℕ) (alpha : ℕ → ℝ)
    (K₁ K₂ T : ℝ) (hT : 0 < T) (hTK₂ : K₂ + 2 ≤ T)
    (kappaMain kappaReplacement kappaCollision c₃ eps : ℝ)
    (hc₃ : 0 ≤ c₃)
    (hmain : (∫ xi in bandPartOn (levelSmallSet Pl Nl v₀l v₁l g alpha) J
        {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
      ‖typicalSCellUniformMain g A (A + Delta) (Pl j)
        (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j)
        (Nl j) (v₀l j) (v₁l j) (ql j) xi‖ ^ 2)
      ≤ kappaMain * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hreplacement : 2 * (∫ xi in bandPartOn
        (levelSmallSet Pl Nl v₀l v₁l g alpha) J
          {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
        ‖typicalSCellReplacement g A (A + Delta) (Pl j)
          (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j)
          (Nl j) (v₀l j) (v₁l j) (ql j) xi‖ ^ 2)
      ≤ kappaReplacement * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hcollisionFitWide : 8 * collisionEnergyBoundWide A (Pl j) T
      ≤ kappaCollision * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hshare : (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (2 * kappaMain + 2 * kappaReplacement + 2 * kappaCollision)
      ≤ (1 : ℝ) / 2 ^ (j + 1)) :
    (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (∫ xi in bandPartOn (levelSmallSet Pl Nl v₀l v₁l g alpha) J
            {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
          ‖∑ m ∈ typicalS A (A + Delta) (innerBandLevels Pl Pu J),
              (g m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
      ≤ (1 / 2 ^ (j + 1))
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
  have hpartT := innerBandPartOn_subset_Ioc
    (levelSmallSet Pl Nl v₀l v₁l g alpha) J j K₁ K₂ T hTK₂
  have hstable := innerBandLevel_stable_of_disjoint Pl Pu J j hjJ hPl hPu hdisj hdisjU
  rw [innerBandLevels_eq_middle Pl Pu J j hjJ]
  exact typicalS_level_leg_le_budget_of_collision_fit_middle_wide
    g hcm hg A Delta H hA hDeltaA
    (innerBandLevelsBefore Pl J j) (innerBandLevelsAfter Pl Pu J j) (Pl j)
    (hPl j hjJ) (Nl j) (v₀l j) (v₁l j) hcov hstable (ql j)
    K₁ K₂ T hT J j (levelSmallSet Pl Nl v₀l v₁l g alpha)
    (levelSmallSet_measurableSet Pl Nl v₀l v₁l g alpha) hpartT
    kappaMain kappaReplacement kappaCollision c₃ eps hc₃ hmain hreplacement
    hcollisionFitWide hshare

end Tao2015

end MoltResearch
