import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryMain

/-!
# Track R A2-V'-12: level-zero main term at a short budget

The existing level-zero theorem already contains the two geometric-sum
estimates.  Only its last comparison used the old band size.  Here the two
displayed fits are checked against the relative floor `rho0` and then lifted
to the actual band budget.
-/

namespace MoltResearch

namespace Tao2015

open Finset MeasureTheory ExpSums

theorem band_energy_level_zero_main_of_ratio
    (P : Finset ℕ) (N : ℕ) (hN : 0 < N) (v0 v1 : ℕ) (q : ℕ → ℕ)
    (A B R : ℕ) (hR : 1 ≤ R) (hB : B ≤ R * A)
    (hq1 : ∀ v, 1 ≤ q v) (hqA : ∀ v, 2 * q v ≤ A)
    (hqup : ∀ v ∈ Finset.Ico v0 (v1 + 1),
      (q v : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ))))
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1) (S : Finset ℕ)
    (T : ℝ) (hT : 0 < T)
    (G : Set ℝ) (hGm : MeasurableSet G) (hGT : G ⊆ Set.Ioc (-T) T)
    (alpha : ℝ) (hAlpha : 0 < alpha) (hAlpha2 : 2 * alpha < 1)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ v ∈ Finset.Ico v0 (v1 + 1),
      ∑ m ∈ Finset.Ioc (A / q v) (B / q v), (1 : ℝ) / (m : ℝ) ≤ C)
    (hsmall : ∀ v ∈ Finset.Ico v0 (v1 + 1), ∀ xi ∈ G,
      ‖levelCellPoly P N v g xi‖ ≤
        Real.exp (-(alpha * (v : ℝ) / ((2 * N : ℕ) : ℝ))))
    (Plo Qhi c3 eps rho0 rho kappa : ℝ)
    (hPlo0 : 0 < Plo) (hQhi0 : 0 < Qhi)
    (htop : (v1 : ℝ) ≤ 2 * (N : ℝ) * Real.log Qhi)
    (hbot : 2 * (N : ℝ) * Real.log Plo - 1 ≤ (v0 : ℝ))
    (hc3 : 0 ≤ c3) (hkappa : 0 ≤ kappa) (hratio : rho0 ≤ rho)
    (hfitT : ((Finset.Ico v0 (v1 + 1)).card : ℝ) *
        (Real.exp Real.pi * C *
          ((2 * T * Real.exp (1 / ((2 * N : ℕ) : ℝ)) / (A : ℝ)) *
            (Qhi ^ (1 - 2 * alpha) *
              Real.exp ((1 - 2 * alpha) / ((2 * N : ℕ) : ℝ))) *
            (((2 * N : ℕ) : ℝ) / (1 - 2 * alpha) + 1))) ≤
      kappa / 2 * (c3 * eps ^ 2 * rho0 / 8))
    (hfitP : ((Finset.Ico v0 (v1 + 1)).card : ℝ) *
        (Real.exp Real.pi * C *
          (4 * (R : ℝ) *
            (Plo ^ (-(2 * alpha)) *
              Real.exp (2 * alpha / ((2 * N : ℕ) : ℝ))) *
            (((2 * N : ℕ) : ℝ) / (2 * alpha) + 1))) ≤
      kappa / 2 * (c3 * eps ^ 2 * rho0 / 8)) :
    (∫ xi in G, ‖∑ v ∈ Finset.Ico v0 (v1 + 1),
        levelCellPoly P N v g xi *
          (∑ m ∈ Finset.Ioc (A / q v) (B / q v),
            (typicalSQuotCoeff g P S m / (m : ℂ)) *
              ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))‖ ^ 2) ≤
      kappa * bandBudget c3 eps rho := by
  have hbudget := bandBudget_lower_of_ratio c3 eps rho0 rho hc3 hratio
  have hhalf : 0 ≤ kappa / 2 := by positivity
  have hfitT' : ((Finset.Ico v0 (v1 + 1)).card : ℝ) *
        (Real.exp Real.pi * C *
          ((2 * T * Real.exp (1 / ((2 * N : ℕ) : ℝ)) / (A : ℝ)) *
            (Qhi ^ (1 - 2 * alpha) *
              Real.exp ((1 - 2 * alpha) / ((2 * N : ℕ) : ℝ))) *
            (((2 * N : ℕ) : ℝ) / (1 - 2 * alpha) + 1))) ≤
      kappa / 2 * bandBudget c3 eps rho :=
    hfitT.trans (mul_le_mul_of_nonneg_left hbudget hhalf)
  have hfitP' : ((Finset.Ico v0 (v1 + 1)).card : ℝ) *
        (Real.exp Real.pi * C *
          (4 * (R : ℝ) *
            (Plo ^ (-(2 * alpha)) *
              Real.exp (2 * alpha / ((2 * N : ℕ) : ℝ))) *
            (((2 * N : ℕ) : ℝ) / (2 * alpha) + 1))) ≤
      kappa / 2 * bandBudget c3 eps rho :=
    hfitP.trans (mul_le_mul_of_nonneg_left hbudget hhalf)
  exact band_energy_level_one_main_le_budget_of_qup P N hN v0 v1 q
    A B R hR hB hq1 hqA hqup g hg S T hT G hGm hGT alpha hAlpha hAlpha2
    C hC0 hC hsmall Plo Qhi c3 eps rho kappa hPlo0 hQhi0 htop hbot
    hfitT' hfitP'

end Tao2015

end MoltResearch
