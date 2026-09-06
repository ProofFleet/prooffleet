import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalAggregateMargins
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2LowRemainder

/-!
# Track R A2-V': the joint ladder budget

One geometric ladder must serve both the low-band approximation and the
exceptional sharp envelope.  Its target is therefore the minimum of those
two fixed budgets.
-/

namespace MoltResearch

namespace Tao2015

/-- Fixed positive-ladder remainder budget.  The factor eight makes its
quarter-budget exactly half of the exceptional `DeltaU` tail allowance. -/
noncomputable def sliceA2ExceptionalLadderBudget
    (lowBudget epsc eps rho0 : ℝ) : ℝ :=
  min lowBudget
    (8 * sliceA2ExceptionalEpsilonPrime 0 epsc eps rho0 *
      Real.exp 13 * (exceptionalIntervalRatio epsc : ℝ))

/-- The common ladder ratio chosen from density and both mean-square uses. -/
noncomputable def sliceA2ExceptionalLadderEta
    (lowBudget epsc eps rho0 : ℝ) : ℕ :=
  sliceA2LadderEta
    (sliceA2ExceptionalLadderBudget lowBudget epsc eps rho0) epsc

theorem sliceA2ExceptionalLadderBudget_pos
    (lowBudget epsc eps rho0 : ℝ)
    (hlow : 0 < lowBudget) (heps : 0 < eps) (hrho0 : 0 < rho0) :
    0 < sliceA2ExceptionalLadderBudget lowBudget epsc eps rho0 := by
  unfold sliceA2ExceptionalLadderBudget
  apply lt_min hlow
  have hp := sliceA2ExceptionalEpsilonPrime_pos 0 epsc eps rho0 heps hrho0
  have hR : (0 : ℝ) < exceptionalIntervalRatio epsc := by
    exact_mod_cast (show 0 < exceptionalIntervalRatio epsc by
      have := exceptionalIntervalRatio_three_le epsc
      omega)
  positivity

theorem sliceA2ExceptionalLadderBudget_le_low
    (lowBudget epsc eps rho0 : ℝ) :
    sliceA2ExceptionalLadderBudget lowBudget epsc eps rho0 ≤ lowBudget := by
  unfold sliceA2ExceptionalLadderBudget
  exact min_le_left _ _

theorem sliceA2ExceptionalLadderBudget_quarter_le_delta
    (lowBudget epsc eps rho0 : ℝ) :
    sliceA2ExceptionalLadderBudget lowBudget epsc eps rho0 / 4 ≤
      2 * sliceA2ExceptionalEpsilonPrime 0 epsc eps rho0 *
        Real.exp 13 * (exceptionalIntervalRatio epsc : ℝ) := by
  have h := min_le_right lowBudget
    (8 * sliceA2ExceptionalEpsilonPrime 0 epsc eps rho0 *
      Real.exp 13 * (exceptionalIntervalRatio epsc : ℝ))
  unfold sliceA2ExceptionalLadderBudget
  linarith

theorem sliceA2ExceptionalLadderEta_one_le
    (lowBudget epsc eps rho0 : ℝ) :
    1 ≤ sliceA2ExceptionalLadderEta lowBudget epsc eps rho0 := by
  unfold sliceA2ExceptionalLadderEta
  exact sliceA2LadderEta_one_le _ _

/-- The chosen ratio pays the ladder remainder at the joint budget. -/
theorem sliceA2ExceptionalLadderEta_brun_budget
    (lowBudget epsc eps rho0 : ℝ)
    (hlow : 0 < lowBudget) (hepsc : 0 < epsc)
    (heps : 0 < eps) (hrho0 : 0 < rho0) :
    64 * Real.exp 12 ≤
      sliceA2ExceptionalLadderBudget lowBudget epsc eps rho0 *
        sliceA2ExceptionalLadderEta lowBudget epsc eps rho0 := by
  let b := sliceA2ExceptionalLadderBudget lowBudget epsc eps rho0
  have hb : 0 < b := sliceA2ExceptionalLadderBudget_pos
    lowBudget epsc eps rho0 hlow heps hrho0
  simpa [b, sliceA2ExceptionalLadderEta] using
    sliceA2LadderEta_brun_budget_left b epsc hb hepsc

/-- The same ratio still pays the independent density budget. -/
theorem sliceA2ExceptionalLadderEta_density_budget
    (lowBudget epsc eps rho0 : ℝ)
    (hlow : 0 < lowBudget) (hepsc : 0 < epsc)
    (heps : 0 < eps) (hrho0 : 0 < rho0) :
    64 * Real.exp 12 ≤
      epsc * sliceA2ExceptionalLadderEta lowBudget epsc eps rho0 := by
  let b := sliceA2ExceptionalLadderBudget lowBudget epsc eps rho0
  have hb : 0 < b := sliceA2ExceptionalLadderBudget_pos
    lowBudget epsc eps rho0 hlow heps hrho0
  simpa [b, sliceA2ExceptionalLadderEta] using
    sliceA2LadderEta_brun_budget b epsc hb hepsc

end Tao2015

end MoltResearch
