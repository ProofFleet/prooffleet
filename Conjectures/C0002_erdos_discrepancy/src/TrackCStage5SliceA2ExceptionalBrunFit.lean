import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalBrunQuotient

/-!
# Track R A2-V': conditional exceptional Brun fit

The dyadic main term, finite Brun error, and sole division-rounding point
are assigned respectively `1/8`, `1/16`, and `1/16` of the fixed ladder
budget.
-/

namespace MoltResearch

namespace Tao2015

open Finset

set_option maxHeartbeats 800000 in
/-- The selected positive ladder has a quarter-budget remainder on every
exceptional quotient interval once the displayed scale margins hold. -/
theorem sliceA2PositiveLadder_exceptional_remainder_le_quarter
    (P0 ratio0 eta n A Delta q : ℕ) (budget y : ℝ)
    (hP0 : 3 ≤ P0) (hq : 0 < q) (ha : 1 ≤ A / q)
    (hDelta : Delta ≤ A) (hbudget : 0 < budget) (hy : 0 ≤ y)
    (heta : 64 * Real.exp 12 ≤ budget * eta)
    (hn : (n : ℝ) ≤ Real.exp y)
    (hQ : (sliceA2LadderQ P0 ratio0 eta n : ℝ) + 1 ≤ Real.exp y)
    (hK : (brunPowerIntervalDepth
      (sliceA2LadderRatio ratio0 eta n) : ℝ) ≤ y)
    (hmargin : Real.log (32 / budget) + y + 2 * y ^ 2 ≤
      Real.log ((A / q : ℕ) : ℝ))
    (hround : (n : ℝ) / (2 * (A / q) + 1 : ℕ) ≤ budget / 16) :
    ladderSiftedLogMass (A / q) ((A + Delta) / q)
        ((List.range n).map
          (fun i => sliceA2LadderPrimes P0 ratio0 eta (i + 1))) ≤
      budget / 4 := by
  let a := A / q
  let L := fun i => sliceA2LadderPrimes P0 ratio0 eta (i + 1)
  have hquot := ladderSiftedLogMass_quotient_le_dyadic_add_one
    A Delta q n L hq hDelta
  have hadd := ladderSiftedLogMass_dyadic_add_one a n L ha
  have hmain := sliceA2PositiveLadder_brun_le_main_add_errors
    P0 ratio0 eta n a budget ha hP0 hbudget heta
  have herrRaw := sliceA2PositiveLadder_brunErrors_le
    P0 ratio0 eta n a hP0 ha
  have herrEnvelope := brunLastEnvelope_le_eps_div_sixteen
    a n (sliceA2LadderQ P0 ratio0 eta n)
      (brunPowerIntervalDepth (sliceA2LadderRatio ratio0 eta n))
      budget y ha hbudget hy hn hQ hK hmargin
  have herr : ∑ i ∈ range n,
      brunPowerIntervalFiniteError a
        (sliceA2LadderP P0 ratio0 eta (i + 1))
        (sliceA2LadderRatio ratio0 eta (i + 1)) ≤ budget / 16 :=
    herrRaw.trans (by simpa using herrEnvelope)
  have hmass : ∑ m ∈ Ioc a (2 * a), (1 : ℝ) / m ≤ 1 := by
    have hupp := sliceA2_harmonic_upper a a ha
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
    simpa only [show a + a = 2 * a by omega, div_self (ne_of_gt ha0)] using hupp
  have hdyadic : ladderSiftedLogMass a (2 * a)
      ((List.range n).map L) ≤ 3 * budget / 16 := by
    calc
      ladderSiftedLogMass a (2 * a) ((List.range n).map L) ≤
          (budget / 8) * (∑ m ∈ Ioc a (2 * a), (1 : ℝ) / m) +
            ∑ i ∈ range n,
              brunPowerIntervalFiniteError a
                (sliceA2LadderP P0 ratio0 eta (i + 1))
                (sliceA2LadderRatio ratio0 eta (i + 1)) := by
        simpa [L] using hmain
      _ ≤ (budget / 8) * 1 + budget / 16 := by gcongr
      _ = 3 * budget / 16 := by ring
  calc
    ladderSiftedLogMass (A / q) ((A + Delta) / q)
        ((List.range n).map L) ≤
      ladderSiftedLogMass a (2 * a + 1) ((List.range n).map L) := by
        simpa [a, L] using hquot
    _ ≤ ladderSiftedLogMass a (2 * a) ((List.range n).map L) +
        (n : ℝ) / (2 * a + 1 : ℕ) := hadd
    _ ≤ 3 * budget / 16 + budget / 16 := by
      gcongr
    _ = budget / 4 := by ring

end Tao2015

end MoltResearch
