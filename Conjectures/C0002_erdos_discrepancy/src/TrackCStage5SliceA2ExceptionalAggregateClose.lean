import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalDeltaClose

/-!
# Track R A2-V': close the exceptional aggregate

This packages the integer, prime, and wide exceptional fits at the canonical
Rankin-tail and joint-ladder allocations.
-/

namespace MoltResearch

namespace Tao2015

open Finset MeasureTheory ExpSums

/-- The three literal aggregate inequalities consumed by the shifted inner
capstone, specialized to the final exceptional choices. -/
def SliceA2ExceptionalAggregateClosed
    (g : ℕ → ℂ) (A Delta P0 ratio0 A1 : ℕ)
    (lowBudget epsc eps rho0 K1 K2 T : ℝ) (hP0 : 2 ≤ P0) : Prop :=
  let eta := sliceA2ExceptionalLadderEta lowBudget epsc eps rho0
  let J := sliceA2LadderJ P0 ratio0 eta A1 hP0
  let tail := sliceA2ExceptionalTailBudget epsc eps rho0
  let rem := sliceA2ExceptionalLadderBudget lowBudget epsc eps rho0 / 4
  let d := sliceA2ExceptionalDeltaEnvelope A1 epsc eps rho0 tail rem
  (2 * ((sliceA2ExceptionalI A1 epsc eps rho0).card : ℝ) *
      (∑ v ∈ sliceA2ExceptionalI A1 epsc eps rho0,
        exceptionalIntegerCellCost (exceptionalSplitThreshold A)
          (sliceA2ExceptionalBq A Delta A1 v epsc eps rho0)
          (sliceA2ExceptionalCover g P0 ratio0 eta J A1
            eps epsc rho0 K1 K2) T
          (sliceA2ExceptionalLogFactor T)
          (sliceA2ExceptionalCoeffMass g A Delta P0 ratio0 eta J A1 v
            epsc eps rho0)) ≤ eps ^ 2 * rho0 / 64) ∧
  (2 * ((sliceA2ExceptionalI A1 epsc eps rho0).card : ℝ) *
      (∑ v ∈ sliceA2ExceptionalI A1 epsc eps rho0,
        exceptionalPrimeCellCost
          (fun u => eadicCell (exceptionalPrimes A1 epsc)
            (2 * sliceA2ExceptionalN A1 epsc eps rho0) u)
          (sliceA2ExceptionalAnchor A1 · epsc eps rho0) g (fun _ => d)
          (sliceA2ExceptionalGamma A A1 · epsc eps rho0 T) v) ≤
    eps ^ 2 * rho0 / 64) ∧
  (2 * (2 * replacementEnergyBoundWide A (exceptionalPrimes A1 epsc)
        (sliceA2ExceptionalN A1 epsc eps rho0) T +
      2 * (4 * collisionEnergyBoundWide A
        (exceptionalPrimes A1 epsc) T)) ≤ eps ^ 2 * rho0 / 32)

/-- The exceptional aggregate is closed uniformly throughout every
quadratic scale window once the two elementary band-log bounds hold. -/
theorem exists_sliceA2Exceptional_aggregate_closed
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (P0 ratio0 : ℕ) (lowBudget epsc eps rho0 : ℝ)
    (hP0 : 3 ≤ P0) (hlow : 0 < lowBudget)
    (heps : 0 < eps) (hrho0 : 0 < rho0) :
    ∃ A0 : ℕ, ∀ A1 A Delta : ℕ,
      A0 ≤ A1 → A1 ≤ A → A ≤ A1 ^ 2 → Delta ≤ A →
      ∀ K1 K2 T : ℝ,
        1 ≤ T → K2 + 2 ≤ T → T ≤ A →
        Real.log (A1 : ℝ) / 2 ≤ Real.log (2 * T) →
        Real.log (2 * T) ≤ 3 * Real.log (A1 : ℝ) →
        SliceA2ExceptionalAggregateClosed g A Delta P0 ratio0 A1
          lowBudget epsc eps rho0 K1 K2 T (by omega) := by
  let eta := sliceA2ExceptionalLadderEta lowBudget epsc eps rho0
  have heta : 1 ≤ eta := by
    simpa [eta] using sliceA2ExceptionalLadderEta_one_le
      lowBudget epsc eps rho0
  obtain ⟨A0, hA0⟩ := exists_sliceA2Exceptional_aggregate_fits
    g hg P0 ratio0 eta epsc eps rho0 (by omega) heta heps hrho0
  refine ⟨A0, fun A1 A Delta hA1 hA hAupper hDelta
    K1 K2 T hT hTK2 hTA hLlower hLupper => ?_⟩
  let tail := sliceA2ExceptionalTailBudget epsc eps rho0
  let rem := sliceA2ExceptionalLadderBudget lowBudget epsc eps rho0 / 4
  have htail0 : 0 ≤ tail := by
    exact (sliceA2ExceptionalTailBudget_pos epsc eps rho0 heps hrho0).le
  have hrem0 : 0 ≤ rem := by
    dsimp [rem]
    exact div_nonneg
      (sliceA2ExceptionalLadderBudget_pos
        lowBudget epsc eps rho0 hlow heps hrho0).le (by norm_num)
  have hsmall := sliceA2Exceptional_tail_remainder_small
    lowBudget epsc eps rho0 A1
  have hfits := hA0 A1 A Delta hA1 hA hAupper hDelta
    K1 K2 T tail rem hT hTK2 hTA hLlower hLupper htail0 hrem0
    (by simpa [tail, rem] using hsmall)
  simpa [SliceA2ExceptionalAggregateClosed, eta, tail, rem] using hfits

end Tao2015

end MoltResearch
