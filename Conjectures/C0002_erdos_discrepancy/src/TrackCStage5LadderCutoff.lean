import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5OrdinaryLadderData

/-!
# Track R L3-3: truncating the fixed ladder

The ordinary ladder is fixed after `P0` and the integral ratio constant
`eta` have been chosen.  At base scale `A1`, `ordinaryLadderJ` stops just
after the first lower endpoint reaching `(log A1)^40`.  This file records the
growth, existence, least-index property, and exact overshoot formula.
-/

namespace MoltResearch

namespace Tao2015

/-- Every step of the ladder at least squares the previous lower endpoint. -/
theorem ordinaryLadderP_sq_le_succ
    (P0 eta j : ℕ) (hP0 : 2 ≤ P0) :
    ordinaryLadderP P0 eta j ^ 2 ≤ ordinaryLadderP P0 eta (j + 1) := by
  have hP1 : 1 ≤ ordinaryLadderP P0 eta j :=
    (ordinaryLadderP_two_le P0 eta j hP0).trans' (by norm_num)
  have hratio : 2 ≤ ordinaryLadderRatio eta j :=
    ordinaryLadderRatio_two_le eta j
  have hfirst : ordinaryLadderP P0 eta j ^ 2 ≤
      ordinaryLadderQ P0 eta j := by
    rw [ordinaryLadderQ_eq]
    exact pow_le_pow_right' hP1 hratio
  have hexp0 : 0 < 100 * (j + 1) ^ 2 := by
    exact Nat.mul_pos (by norm_num) (pow_pos (Nat.succ_pos j) 2)
  rw [ordinaryLadderP_succ]
  exact hfirst.trans (Nat.le_pow hexp0)

/-- A simple double-exponential lower bound, sufficient to show that every
real cutoff is eventually crossed. -/
theorem two_pow_two_pow_le_ordinaryLadderP
    (P0 eta j : ℕ) (hP0 : 2 ≤ P0) :
    2 ^ (2 ^ j) ≤ ordinaryLadderP P0 eta j := by
  induction j with
  | zero => simpa using hP0
  | succ j ih =>
      calc
        2 ^ (2 ^ (j + 1)) = (2 ^ (2 ^ j)) ^ 2 := by
          rw [pow_succ, pow_mul]
        _ ≤ ordinaryLadderP P0 eta j ^ 2 := pow_le_pow_left' ih 2
        _ ≤ ordinaryLadderP P0 eta (j + 1) :=
          ordinaryLadderP_sq_le_succ P0 eta j hP0

/-- The real threshold used to select the last ordinary level. -/
noncomputable def ordinaryLadderCutoff (A1 : ℕ) : ℝ :=
  Real.log (A1 : ℝ) ^ 40

theorem ordinaryLadderCutoff_nonneg (A1 : ℕ) :
    0 ≤ ordinaryLadderCutoff A1 := by
  unfold ordinaryLadderCutoff
  positivity

/-- The fixed ladder reaches `(log A1)^40`. -/
theorem ordinaryLadder_reaches_cutoff
    (P0 eta A1 : ℕ) (hP0 : 2 ≤ P0) :
    ∃ j : ℕ, ordinaryLadderCutoff A1 ≤ (ordinaryLadderP P0 eta j : ℝ) := by
  let x := ordinaryLadderCutoff A1
  let j : ℕ := ⌈x⌉₊
  refine ⟨j, ?_⟩
  have hxceil : x ≤ (j : ℝ) := by
    dsimp [j]
    exact Nat.le_ceil x
  have hjpow : j ≤ 2 ^ j := Nat.lt_two_pow_self.le
  have hpowpow : 2 ^ j ≤ 2 ^ (2 ^ j) :=
    pow_le_pow_right' (by norm_num : 1 ≤ (2 : ℕ)) hjpow
  have hgrowth := two_pow_two_pow_le_ordinaryLadderP P0 eta j hP0
  exact hxceil.trans (by exact_mod_cast hjpow.trans hpowpow |>.trans hgrowth)

/-- One plus the least ladder index whose lower endpoint crosses the cutoff. -/
noncomputable def ordinaryLadderJ
    (P0 eta A1 : ℕ) (hP0 : 2 ≤ P0) : ℕ :=
  Nat.find (ordinaryLadder_reaches_cutoff P0 eta A1 hP0) + 1

theorem ordinaryLadderJ_pos
    (P0 eta A1 : ℕ) (hP0 : 2 ≤ P0) :
    0 < ordinaryLadderJ P0 eta A1 hP0 := by
  unfold ordinaryLadderJ
  omega

/-- The last included lower endpoint reaches the target. -/
theorem ordinaryLadderJ_last_reaches
    (P0 eta A1 : ℕ) (hP0 : 2 ≤ P0) :
    ordinaryLadderCutoff A1 ≤
      (ordinaryLadderP P0 eta (ordinaryLadderJ P0 eta A1 hP0 - 1) : ℝ) := by
  unfold ordinaryLadderJ
  simpa using Nat.find_spec (ordinaryLadder_reaches_cutoff P0 eta A1 hP0)

theorem ordinaryLadderJ_two_le_of_bottom_lt
    (P0 eta A1 : ℕ) (hP0 : 2 ≤ P0)
    (hbottom : (P0 : ℝ) < ordinaryLadderCutoff A1) :
    2 ≤ ordinaryLadderJ P0 eta A1 hP0 := by
  let hex := ordinaryLadder_reaches_cutoff P0 eta A1 hP0
  have hfind : 0 < Nat.find hex := by
    by_contra hzero
    have hz : Nat.find hex = 0 := Nat.eq_zero_of_not_pos hzero
    have hspec := Nat.find_spec hex
    rw [hz, ordinaryLadderP_zero] at hspec
    exact (not_le_of_gt hbottom) hspec
  unfold ordinaryLadderJ
  omega

/-- Any explicit crossing gives an upper bound on the chosen number of
levels.  This is the interface used with the sharper triangular growth
witness. -/
theorem ordinaryLadderJ_le_of_reaches
    (P0 eta A1 : ℕ) (hP0 : 2 ≤ P0) (j : ℕ)
    (hj : ordinaryLadderCutoff A1 ≤ (ordinaryLadderP P0 eta j : ℝ)) :
    ordinaryLadderJ P0 eta A1 hP0 ≤ j + 1 := by
  unfold ordinaryLadderJ
  exact Nat.add_le_add_right
    (Nat.find_min' (ordinaryLadder_reaches_cutoff P0 eta A1 hP0) hj) 1

/-- When at least two levels are present, the preceding lower endpoint has
not yet reached the cutoff. -/
theorem ordinaryLadderJ_prev_lt
    (P0 eta A1 : ℕ) (hP0 : 2 ≤ P0)
    (hJ2 : 2 ≤ ordinaryLadderJ P0 eta A1 hP0) :
    (ordinaryLadderP P0 eta (ordinaryLadderJ P0 eta A1 hP0 - 2) : ℝ) <
      ordinaryLadderCutoff A1 := by
  let hex := ordinaryLadder_reaches_cutoff P0 eta A1 hP0
  let n := Nat.find hex
  have hn : 0 < n := by
    dsimp [ordinaryLadderJ] at hJ2
    omega
  have hnot : ¬ ordinaryLadderCutoff A1 ≤
      (ordinaryLadderP P0 eta (n - 1) : ℝ) :=
    Nat.find_min hex (by omega : n - 1 < n)
  have hshape : ordinaryLadderJ P0 eta A1 hP0 - 2 = n - 1 := by
    dsimp [ordinaryLadderJ, n, hex]
    omega
  rw [hshape]
  exact lt_of_not_ge hnot

/-- Exact formula for the last upper endpoint in terms of the predecessor
lower endpoint.  It records all overshoot exponents without asymptotic
notation. -/
theorem ordinaryLadderQ_last_formula
    (P0 eta n : ℕ) (hn : 0 < n) :
    ordinaryLadderQ P0 eta n =
      ((ordinaryLadderP P0 eta (n - 1) ^ ordinaryLadderRatio eta (n - 1)) ^
          (100 * n ^ 2)) ^ ordinaryLadderRatio eta n := by
  rw [ordinaryLadderQ_eq]
  have hP : ordinaryLadderP P0 eta n =
      ordinaryLadderQ P0 eta (n - 1) ^ (100 * n ^ 2) := by
    have hns : n - 1 + 1 = n := by omega
    simpa only [hns] using ordinaryLadderP_succ P0 eta (n - 1)
  rw [hP, ordinaryLadderQ_eq]

/-- The least-crossing overshoot bound in a directly usable power form. -/
theorem ordinaryLadderQ_lt_cutoff_pow
    (P0 eta A1 : ℕ) (hP0 : 2 ≤ P0)
    (hJ2 : 2 ≤ ordinaryLadderJ P0 eta A1 hP0) :
    (ordinaryLadderQ P0 eta (ordinaryLadderJ P0 eta A1 hP0 - 1) : ℝ) <
      ordinaryLadderCutoff A1 ^
        (ordinaryLadderRatio eta (ordinaryLadderJ P0 eta A1 hP0 - 2) *
          (100 * (ordinaryLadderJ P0 eta A1 hP0 - 1) ^ 2) *
          ordinaryLadderRatio eta (ordinaryLadderJ P0 eta A1 hP0 - 1)) := by
  let J := ordinaryLadderJ P0 eta A1 hP0
  let n := J - 1
  have hn : 0 < n := by dsimp [n, J]; omega
  have hnprev : n - 1 = J - 2 := by dsimp [n]; omega
  have hprev := ordinaryLadderJ_prev_lt P0 eta A1 hP0 hJ2
  have hexp0 : 0 <
      ordinaryLadderRatio eta (n - 1) * (100 * n ^ 2) *
        ordinaryLadderRatio eta n := by
    exact Nat.mul_pos
      (Nat.mul_pos
        (lt_of_lt_of_le (by norm_num) (ordinaryLadderRatio_two_le eta (n - 1)))
        (Nat.mul_pos (by norm_num) (pow_pos hn 2)))
      (lt_of_lt_of_le (by norm_num) (ordinaryLadderRatio_two_le eta n))
  have hprev' :
      (ordinaryLadderP P0 eta (n - 1) : ℝ) < ordinaryLadderCutoff A1 := by
    simpa [n, hnprev] using hprev
  have hp := pow_lt_pow_left₀ hprev' (by positivity :
    (0 : ℝ) ≤ ordinaryLadderP P0 eta (n - 1)) (Nat.ne_of_gt hexp0)
  rw [ordinaryLadderQ_last_formula P0 eta n hn]
  norm_num only [Nat.cast_pow]
  rw [← pow_mul, ← pow_mul]
  simpa [n, hnprev, mul_assoc] using hp

end Tao2015

end MoltResearch
