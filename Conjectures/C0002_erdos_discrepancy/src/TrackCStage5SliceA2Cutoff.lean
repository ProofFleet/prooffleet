import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinarySchedule

/-!
# Track R A2-V'-15: two-ratio cutoff overshoot

The scale-dependent number of ordinary levels is the least index whose lower
endpoint crosses `(log A1)^40`.  These are the exact minimality and overshoot
identities for the final two-ratio ladder.
-/

namespace MoltResearch

namespace Tao2015

/-- Any explicit crossing bounds the least chosen ladder height. -/
theorem sliceA2LadderJ_le_of_reaches
    (P0 ratio0 eta A1 : ℕ) (hP0 : 2 ≤ P0) (j : ℕ)
    (hj : ordinaryLadderCutoff A1 ≤
      (sliceA2LadderP P0 ratio0 eta j : ℝ)) :
    sliceA2LadderJ P0 ratio0 eta A1 hP0 ≤ j + 1 := by
  unfold sliceA2LadderJ
  exact Nat.add_le_add_right
    (Nat.find_min' (sliceA2Ladder_reaches_cutoff P0 ratio0 eta A1 hP0) hj) 1

/-- Exact last-upper-endpoint formula, retaining both adjacent ratios. -/
theorem sliceA2LadderQ_last_formula
    (P0 ratio0 eta n : ℕ) (hn : 0 < n) :
    sliceA2LadderQ P0 ratio0 eta n =
      ((sliceA2LadderP P0 ratio0 eta (n - 1) ^
          sliceA2LadderRatio ratio0 eta (n - 1)) ^
          (100 * n ^ 2)) ^ sliceA2LadderRatio ratio0 eta n := by
  rw [sliceA2LadderQ_eq]
  have hP : sliceA2LadderP P0 ratio0 eta n =
      sliceA2LadderQ P0 ratio0 eta (n - 1) ^ (100 * n ^ 2) := by
    have hns : n - 1 + 1 = n := by omega
    simpa only [hns] using sliceA2LadderP_succ P0 ratio0 eta (n - 1)
  rw [hP, sliceA2LadderQ_eq]

/-- The least-crossing overshoot, in a form which keeps every exponent
visible for the later polylogarithmic estimate. -/
theorem sliceA2LadderQ_lt_cutoff_pow
    (P0 ratio0 eta A1 : ℕ) (hP0 : 2 ≤ P0)
    (hJ2 : 2 ≤ sliceA2LadderJ P0 ratio0 eta A1 hP0) :
    (sliceA2LadderQ P0 ratio0 eta
        (sliceA2LadderJ P0 ratio0 eta A1 hP0 - 1) : ℝ) <
      ordinaryLadderCutoff A1 ^
        (sliceA2LadderRatio ratio0 eta
            (sliceA2LadderJ P0 ratio0 eta A1 hP0 - 2) *
          (100 * (sliceA2LadderJ P0 ratio0 eta A1 hP0 - 1) ^ 2) *
          sliceA2LadderRatio ratio0 eta
            (sliceA2LadderJ P0 ratio0 eta A1 hP0 - 1)) := by
  let J := sliceA2LadderJ P0 ratio0 eta A1 hP0
  let n := J - 1
  have hn : 0 < n := by dsimp [n, J]; omega
  have hnprev : n - 1 = J - 2 := by dsimp [n]; omega
  have hprev := sliceA2LadderJ_prev_lt P0 ratio0 eta A1 hP0 hJ2
  have hexp0 : 0 <
      sliceA2LadderRatio ratio0 eta (n - 1) * (100 * n ^ 2) *
        sliceA2LadderRatio ratio0 eta n := by
    exact Nat.mul_pos
      (Nat.mul_pos
        (lt_of_lt_of_le (by norm_num)
          (sliceA2LadderRatio_two_le ratio0 eta (n - 1)))
        (Nat.mul_pos (by norm_num) (pow_pos hn 2)))
      (lt_of_lt_of_le (by norm_num)
        (sliceA2LadderRatio_two_le ratio0 eta n))
  have hprev' :
      (sliceA2LadderP P0 ratio0 eta (n - 1) : ℝ) <
        ordinaryLadderCutoff A1 := by
    simpa [n, hnprev] using hprev
  have hp := pow_lt_pow_left₀ hprev' (by positivity :
    (0 : ℝ) ≤ sliceA2LadderP P0 ratio0 eta (n - 1))
      (Nat.ne_of_gt hexp0)
  rw [sliceA2LadderQ_last_formula P0 ratio0 eta n hn]
  norm_num only [Nat.cast_pow]
  rw [← pow_mul, ← pow_mul]
  simpa [n, hnprev, mul_assoc] using hp

/-- A uniform elementary upper bound for the two-ratio schedule. -/
theorem sliceA2LadderRatio_le
    (ratio0 eta j : ℕ) :
    sliceA2LadderRatio ratio0 eta j ≤ 2 + ratio0 + 2 ^ j * eta := by
  unfold sliceA2LadderRatio
  split_ifs
  · exact (max_le_iff.mpr ⟨by omega, by omega⟩)
  · exact (max_le_iff.mpr ⟨by omega, by omega⟩)

/-- Away from level zero only the geometrically growing ratio remains. -/
theorem sliceA2LadderRatio_le_of_pos
    (ratio0 eta j : ℕ) (hj : 0 < j) :
    sliceA2LadderRatio ratio0 eta j ≤ 2 + 2 ^ j * eta := by
  rw [sliceA2LadderRatio_of_pos ratio0 eta j hj]
  exact max_le_iff.mpr ⟨by omega, by omega⟩

end Tao2015

end MoltResearch
