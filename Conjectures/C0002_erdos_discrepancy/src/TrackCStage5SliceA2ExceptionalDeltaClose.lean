import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalSharpBound

/-!
# Track R A2-V': close the exceptional delta envelope

The uniform sharp-cell estimate and the uniform positive-ladder Brun
remainder are added here.  Their fixed allocations also satisfy the exact
smallness inequality used by the aggregate prime fit.
-/

namespace MoltResearch

namespace Tao2015

/-- Twice the Rankin allocation plus one quarter of the joint ladder budget
fits the remaining fixed sharp-envelope margin. -/
theorem sliceA2Exceptional_tail_remainder_small
    (lowBudget epsc eps rho0 : ℝ) (A1 : ℕ) :
    2 * sliceA2ExceptionalTailBudget epsc eps rho0 +
        sliceA2ExceptionalLadderBudget lowBudget epsc eps rho0 / 4 ≤
      4 * sliceA2ExceptionalEpsilonPrime A1 epsc eps rho0 *
        Real.exp 13 * (exceptionalIntervalRatio epsc : ℝ) := by
  have hquarter := sliceA2ExceptionalLadderBudget_quarter_le_delta
    lowBudget epsc eps rho0
  rw [sliceA2ExceptionalEpsilonPrime_eq_zero A1 epsc eps rho0]
  unfold sliceA2ExceptionalTailBudget
  linarith

/-- The canonical sharp cost plus the positive-ladder sifted remainder is
bounded by the chosen fixed `DeltaU` envelope on every exceptional cell. -/
theorem exists_sliceA2Exceptional_delta_bound
    (P0 ratio0 : ℕ) (lowBudget epsc eps rho0 : ℝ)
    (hP0 : 3 ≤ P0) (hlow : 0 < lowBudget) (hepsc : 0 < epsc)
    (heps : 0 < eps) (hrho0 : 0 < rho0) :
    ∃ (D : ℝ) (A0 : ℕ), 1 ≤ D ∧
      ∀ A1 A Delta : ℕ,
        A0 ≤ A1 → A1 ≤ A → A ≤ A1 ^ 2 → Delta ≤ A →
        ∀ v : ℕ,
          let eta := sliceA2ExceptionalLadderEta lowBudget epsc eps rho0
          let J := sliceA2LadderJ P0 ratio0 eta A1 (by omega)
          let tail := sliceA2ExceptionalTailBudget epsc eps rho0
          let rem := sliceA2ExceptionalLadderBudget lowBudget epsc eps rho0 / 4
          cellHalaszSharpBound
                (exceptionalSharpCutoff A) D
                (exceptionalDelta0
                  (sliceA2ExceptionalEpsilonPrime A1 epsc eps rho0))
                (A / sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
                ((A + Delta) /
                  sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
                (exceptionalPrimes A1 epsc)
                [sliceA2LadderPrimes P0 ratio0 eta 0] +
              ladderSiftedLogMass
                (A / sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
                ((A + Delta) /
                  sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
                ((List.range (J - 1)).map
                  (fun i => sliceA2LadderPrimes P0 ratio0 eta (i + 1))) ≤
            sliceA2ExceptionalDeltaEnvelope A1 epsc eps rho0 tail rem := by
  let budget := sliceA2ExceptionalLadderBudget lowBudget epsc eps rho0
  let eta := sliceA2ExceptionalLadderEta lowBudget epsc eps rho0
  have hbudget : 0 < budget := by
    simpa [budget] using sliceA2ExceptionalLadderBudget_pos
      lowBudget epsc eps rho0 hlow heps hrho0
  have heta : 1 ≤ eta := by
    simpa [eta] using sliceA2ExceptionalLadderEta_one_le
      lowBudget epsc eps rho0
  have hetaBrun : 64 * Real.exp 12 ≤ budget * eta := by
    simpa [budget, eta] using sliceA2ExceptionalLadderEta_brun_budget
      lowBudget epsc eps rho0 hlow hepsc heps hrho0
  obtain ⟨D, AS, hD, hsharp⟩ :=
    exists_sliceA2Exceptional_sharp_bound epsc eps rho0 heps hrho0
  obtain ⟨AB, hbrun⟩ :=
    exists_sliceA2PositiveLadder_exceptional_remainder_le_quarter
      P0 ratio0 eta epsc eps rho0 budget hP0 heta hbudget hetaBrun
  refine ⟨D, max AS AB, hD,
    fun A1 A Delta hA1 hA hAupper hDelta v => ?_⟩
  have hAS1 : AS ≤ A1 := by omega
  have hAB1 : AB ≤ A1 := by omega
  let J := sliceA2LadderJ P0 ratio0 eta A1 (by omega)
  let tail := sliceA2ExceptionalTailBudget epsc eps rho0
  let rem := budget / 4
  have hs := hsharp A1 A Delta hAS1 hA hAupper hDelta v
    (sliceA2LadderPrimes P0 ratio0 eta 0)
  have hb := hbrun A1 A Delta hAB1 hA hDelta v
  have hdelta := sliceA2Exceptional_delta_bound_of_sharp_remainder
    A1 epsc eps rho0 tail rem
    (cellHalaszSharpBound
      (exceptionalSharpCutoff A) D
      (exceptionalDelta0
        (sliceA2ExceptionalEpsilonPrime A1 epsc eps rho0))
      (A / sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
      ((A + Delta) / sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
      (exceptionalPrimes A1 epsc)
      [sliceA2LadderPrimes P0 ratio0 eta 0])
    (ladderSiftedLogMass
      (A / sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
      ((A + Delta) / sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
      ((List.range (J - 1)).map
        (fun i => sliceA2LadderPrimes P0 ratio0 eta (i + 1)))) hs
    (by simpa [rem, budget, J] using hb)
  simpa [eta, budget, J, tail, rem] using hdelta

end Tao2015

end MoltResearch
