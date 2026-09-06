import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2SharpMargins

/-!
# Track R A2-V': low remainder for the joint ladder

The final ladder ratio is selected from the minimum of the low-band and
exceptional-cell budgets.  This leaf specializes the dyadic Brun estimate
to an arbitrary ratio that pays the requested low budget, ensuring that the
low and inner estimates use the identical level list.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- Any fixed ladder ratio paying `64*exp(12) <= budget*eta` has absolute
remainder at most `budget/4` on every subinterval of a large dyadic block. -/
theorem exists_sliceA2PositiveLadder_low_remainder_of_budget
    (P0 ratio0 eta : ℕ) (budget : ℝ)
    (hP0 : 3 ≤ P0) (hbudget : 0 < budget) (heta1 : 1 ≤ eta)
    (heta : 64 * Real.exp 12 ≤ budget * eta) :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 → ∀ X Delta : ℕ, A1 ≤ X →
      Delta ≤ X →
      ladderSiftedLogMass X (X + Delta)
          ((List.range
            (sliceA2LadderJ P0 ratio0 eta A1 (by omega) - 1)).map
            (fun i ↦ sliceA2LadderPrimes P0 ratio0 eta (i + 1))) ≤
        budget / 4 := by
  obtain ⟨A0, hA0⟩ := exists_sliceA2PositiveLadder_density
    P0 ratio0 eta budget hP0 hbudget heta1 heta
  refine ⟨max A0 1, fun A1 hA1 X Delta hA1X hDelta ↦ ?_⟩
  have hA0A1 : A0 ≤ A1 := (le_max_left A0 1).trans hA1
  have hA11 : 1 ≤ A1 := (le_max_right A0 1).trans hA1
  have hX1 : 1 ≤ X := hA11.trans hA1X
  have hdyadic := hA0 A1 hA0A1 X hA1X
  have hrestrict := ladderSiftedLogMass_mono_right X (X + Delta)
    (2 * X)
    ((List.range
      (sliceA2LadderJ P0 ratio0 eta A1 (by omega) - 1)).map
      (fun i ↦ sliceA2LadderPrimes P0 ratio0 eta (i + 1))) (by omega)
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
          (sliceA2LadderJ P0 ratio0 eta A1 (by omega) - 1)).map
          (fun i ↦ sliceA2LadderPrimes P0 ratio0 eta (i + 1))) ≤
      ladderSiftedLogMass X (2 * X)
        ((List.range
          (sliceA2LadderJ P0 ratio0 eta A1 (by omega) - 1)).map
          (fun i ↦ sliceA2LadderPrimes P0 ratio0 eta (i + 1))) := hrestrict
    _ ≤ (budget / 4) *
        ∑ n ∈ Finset.Ioc X (2 * X), (1 : ℝ) / n := hdyadic
    _ ≤ (budget / 4) * 1 :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = budget / 4 := by ring

/-- The concrete exceptional ladder pays the low-band remainder at the
first argument of its joint budget. -/
theorem exists_sliceA2ExceptionalLadder_low_remainder
    (P0 ratio0 : ℕ) (lowBudget epsc eps rho0 : ℝ)
    (hP0 : 3 ≤ P0) (hlow : 0 < lowBudget) (hepsc : 0 < epsc)
    (heps : 0 < eps) (hrho0 : 0 < rho0) :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 → ∀ X Delta : ℕ, A1 ≤ X →
      Delta ≤ X →
      let eta := sliceA2ExceptionalLadderEta lowBudget epsc eps rho0
      ladderSiftedLogMass X (X + Delta)
          ((List.range
            (sliceA2LadderJ P0 ratio0 eta A1 (by omega) - 1)).map
            (fun i ↦ sliceA2LadderPrimes P0 ratio0 eta (i + 1))) ≤
        lowBudget / 4 := by
  let eta := sliceA2ExceptionalLadderEta lowBudget epsc eps rho0
  let budget := sliceA2ExceptionalLadderBudget lowBudget epsc eps rho0
  have hbudget : 0 < budget := by
    simpa [budget] using sliceA2ExceptionalLadderBudget_pos
      lowBudget epsc eps rho0 hlow heps hrho0
  have heta1 : 1 ≤ eta := by
    simpa [eta] using sliceA2ExceptionalLadderEta_one_le
      lowBudget epsc eps rho0
  have hetaJoint : 64 * Real.exp 12 ≤ budget * eta := by
    simpa [budget, eta] using sliceA2ExceptionalLadderEta_brun_budget
      lowBudget epsc eps rho0 hlow hepsc heps hrho0
  have hetaLow : 64 * Real.exp 12 ≤ lowBudget * eta :=
    hetaJoint.trans (mul_le_mul_of_nonneg_right
      (sliceA2ExceptionalLadderBudget_le_low lowBudget epsc eps rho0)
      (by positivity))
  simpa [eta] using
    exists_sliceA2PositiveLadder_low_remainder_of_budget
      P0 ratio0 eta lowBudget hP0 hlow heta1 hetaLow

end Tao2015

end MoltResearch
