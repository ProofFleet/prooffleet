import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2LowFit
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2LadderDensity

/-!
# Track R A2-V': the positive-ladder low-band remainder

The selected ladder ratio pays both density accuracy and mean-square
accuracy.  Its dyadic Brun estimate therefore gives the absolute `e/4`
remainder used by the explicit low-band slot.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- Restricting the integer interval can only decrease the sifted logarithmic
mass. -/
theorem ladderSiftedLogMass_mono_right
    (a b c : ℕ) (ladder : List (Finset ℕ)) (hbc : b ≤ c) :
    ladderSiftedLogMass a b ladder ≤ ladderSiftedLogMass a c ladder := by
  classical
  unfold ladderSiftedLogMass
  apply Finset.sum_le_sum
  intro P hP
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset_filter _
      (Finset.Ioc_subset_Ioc le_rfl hbc)
  · intro n hn hnc
    positivity

/-- The chosen ratio also pays the Brun budget with the first accuracy
parameter on the right-hand side. -/
theorem sliceA2LadderEta_brun_budget_left
    (eps epsc : ℝ) (heps : 0 < eps) (hepsc : 0 < epsc) :
    64 * Real.exp 12 ≤ eps * sliceA2LadderEta eps epsc := by
  have h := sliceA2LadderEta_brun_budget epsc eps hepsc heps
  simpa [sliceA2LadderEta, min_comm] using h

/-- Uniform absolute low-band remainder for every subinterval of a dyadic
block. -/
theorem exists_sliceA2PositiveLadder_low_remainder
    (P0 ratio0 : ℕ) (eps epsc : ℝ)
    (hP0 : 3 ≤ P0) (heps : 0 < eps) (hepsc : 0 < epsc) :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 → ∀ X Delta : ℕ, A1 ≤ X →
      Delta ≤ X →
      ladderSiftedLogMass X (X + Delta)
          ((List.range
            (sliceA2LadderJ P0 ratio0
              (sliceA2LadderEta (sliceA2EffectiveEps eps) epsc)
              A1 (by omega) - 1)).map
            (fun i ↦ sliceA2LadderPrimes P0 ratio0
              (sliceA2LadderEta (sliceA2EffectiveEps eps) epsc) (i + 1))) ≤
        sliceA2EffectiveEps eps / 4 := by
  let e := sliceA2EffectiveEps eps
  have he : 0 < e := sliceA2EffectiveEps_bounds eps heps |>.1
  obtain ⟨A0, hA0⟩ := exists_sliceA2PositiveLadder_density
    P0 ratio0 (sliceA2LadderEta e epsc) e hP0 he
      (sliceA2LadderEta_one_le e epsc)
      (by
        exact sliceA2LadderEta_brun_budget_left e epsc he hepsc)
  refine ⟨max A0 1, fun A1 hA1 X Delta hA1X hDelta ↦ ?_⟩
  have hA0A1 : A0 ≤ A1 := (le_max_left A0 1).trans hA1
  have hA11 : 1 ≤ A1 := (le_max_right A0 1).trans hA1
  have hX1 : 1 ≤ X := hA11.trans hA1X
  have hdyadic := hA0 A1 hA0A1 X hA1X
  have hrestrict := ladderSiftedLogMass_mono_right X (X + Delta)
    (2 * X)
    ((List.range
      (sliceA2LadderJ P0 ratio0 (sliceA2LadderEta e epsc)
        A1 (by omega) - 1)).map
      (fun i ↦ sliceA2LadderPrimes P0 ratio0
        (sliceA2LadderEta e epsc) (i + 1))) (by omega)
  have hmass :
      ∑ n ∈ Finset.Ioc X (2 * X), (1 : ℝ) / n ≤ 1 := by
    have hupp := sliceA2_harmonic_upper X X hX1
    have hratio : (X : ℝ) / X ≤ 1 := by
      have hXR : (0 : ℝ) < X := by exact_mod_cast hX1
      rw [div_self (ne_of_gt hXR)]
    simpa only [show X + X = 2 * X by omega] using hupp.trans hratio
  calc
    ladderSiftedLogMass X (X + Delta)
        ((List.range
          (sliceA2LadderJ P0 ratio0 (sliceA2LadderEta e epsc)
            A1 (by omega) - 1)).map
          (fun i ↦ sliceA2LadderPrimes P0 ratio0
            (sliceA2LadderEta e epsc) (i + 1))) ≤
      ladderSiftedLogMass X (2 * X)
        ((List.range
          (sliceA2LadderJ P0 ratio0 (sliceA2LadderEta e epsc)
            A1 (by omega) - 1)).map
          (fun i ↦ sliceA2LadderPrimes P0 ratio0
            (sliceA2LadderEta e epsc) (i + 1))) := hrestrict
    _ ≤ (e / 4) * ∑ n ∈ Finset.Ioc X (2 * X), (1 : ℝ) / n := hdyadic
    _ ≤ (e / 4) * 1 := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = sliceA2EffectiveEps eps / 4 := by simp [e]

end Tao2015

end MoltResearch
