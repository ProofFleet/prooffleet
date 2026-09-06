import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2Cutoff

/-!
# Track R A2-V'-16: triangular ladder growth

The later ratios contribute a factor `2^j` at step `j`.  Iterating those
factors gives the triangular exponent which keeps the least crossing far
below `loglog A1`.
-/

namespace MoltResearch

namespace Tao2015

/-- Every ladder step contains at least the scheduled `2^j` power. -/
theorem two_pow_le_sliceA2_step_exponent
    (ratio0 eta j : ℕ) (heta : 1 ≤ eta) :
    2 ^ j ≤ sliceA2LadderRatio ratio0 eta j * (100 * (j + 1) ^ 2) := by
  by_cases hj : j = 0
  · subst j
    norm_num
    have hr := sliceA2LadderRatio_two_le ratio0 eta 0
    omega
  · have hj0 : 0 < j := Nat.pos_of_ne_zero hj
    have hratio : 2 ^ j ≤ sliceA2LadderRatio ratio0 eta j := by
      rw [sliceA2LadderRatio_of_pos ratio0 eta j hj0]
      exact le_max_of_le_right (Nat.le_mul_of_pos_right _ (by omega))
    have hsq : 1 ≤ (j + 1) ^ 2 := Nat.one_le_pow 2 (j + 1) (by omega)
    have hfactor : 1 ≤ 100 * (j + 1) ^ 2 := by omega
    exact hratio.trans (Nat.le_mul_of_pos_right _ hfactor)

/-- The lower endpoint has a double-exponential triangular lower bound. -/
theorem two_pow_triangular_le_sliceA2LadderP
    (P0 ratio0 eta j : ℕ) (hP0 : 2 ≤ P0) (heta : 1 ≤ eta) :
    2 ^ (2 ^ (j * (j - 1) / 2)) ≤
      sliceA2LadderP P0 ratio0 eta j := by
  induction j with
  | zero => simpa using hP0
  | succ j ih =>
      have hstep := two_pow_le_sliceA2_step_exponent ratio0 eta j heta
      have hbase : 1 ≤ sliceA2LadderP P0 ratio0 eta j :=
        (sliceA2LadderP_two_le P0 ratio0 eta j hP0).trans' (by norm_num)
      have hpow := pow_le_pow_left' ih (2 ^ j)
      have hexp :
          j * (j - 1) / 2 + j = (j + 1) * ((j + 1) - 1) / 2 := by
        rw [← Finset.sum_range_id j, ← Finset.sum_range_id (j + 1),
          Finset.sum_range_succ]
      calc
        2 ^ (2 ^ ((j + 1) * ((j + 1) - 1) / 2)) =
            (2 ^ (2 ^ (j * (j - 1) / 2))) ^ (2 ^ j) := by
          rw [← pow_mul, ← pow_add, hexp]
        _ ≤ sliceA2LadderP P0 ratio0 eta j ^ (2 ^ j) := hpow
        _ ≤ sliceA2LadderP P0 ratio0 eta j ^
            (sliceA2LadderRatio ratio0 eta j * (100 * (j + 1) ^ 2)) :=
          pow_le_pow_right' hbase hstep
        _ = sliceA2LadderP P0 ratio0 eta (j + 1) := by
          rw [sliceA2LadderP_succ, sliceA2LadderQ_eq, pow_mul]

/-- A square-root-sized explicit index crosses any integral target `C`.
The extra factor two avoids all parity bookkeeping in the triangular number. -/
theorem sliceA2LadderP_crosses_at_sqrt_log
    (P0 ratio0 eta C : ℕ) (hP0 : 2 ≤ P0) (heta : 1 ≤ eta) :
    let L := Nat.log 2 C + 1
    let j := 2 * (Nat.sqrt L + 1)
    C ≤ sliceA2LadderP P0 ratio0 eta j := by
  dsimp only
  let L := Nat.log 2 C + 1
  let s := Nat.sqrt L + 1
  let j := 2 * s
  have hCL : C ≤ 2 ^ L := by
    dsimp [L]
    exact (Nat.lt_pow_succ_log_self (by norm_num) C).le
  have hLs : L ≤ s ^ 2 := by
    dsimp [s]
    exact (Nat.lt_succ_sqrt' L).le
  have hs1 : 1 ≤ s := by dsimp [s]; omega
  have htri : L ≤ j * (j - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have hsle : s ≤ j - 1 := by dsimp [j]; omega
    calc
      L * 2 ≤ s ^ 2 * 2 := Nat.mul_le_mul_right 2 hLs
      _ = j * s := by dsimp [j]; rw [pow_two]; ring
      _ ≤ j * (j - 1) := Nat.mul_le_mul_left j hsle
  have hpowL : 2 ^ L ≤ 2 ^ (j * (j - 1) / 2) :=
    pow_le_pow_right' (by norm_num) htri
  have houter : 2 ^ (j * (j - 1) / 2) ≤
      2 ^ (2 ^ (j * (j - 1) / 2)) := by
    exact Nat.lt_two_pow_self.le
  exact hCL.trans (hpowL.trans (houter.trans
    (two_pow_triangular_le_sliceA2LadderP P0 ratio0 eta j hP0 heta)))

/-- Consequently the selected number of levels has an explicit
square-root-logarithmic upper bound. -/
theorem sliceA2LadderJ_le_sqrt_log_cutoff
    (P0 ratio0 eta A1 : ℕ) (hP0 : 2 ≤ P0) (heta : 1 ≤ eta) :
    let C := ⌈ordinaryLadderCutoff A1⌉₊
    sliceA2LadderJ P0 ratio0 eta A1 hP0 ≤
      2 * (Nat.sqrt (Nat.log 2 C + 1) + 1) + 1 := by
  dsimp only
  let C := ⌈ordinaryLadderCutoff A1⌉₊
  let j := 2 * (Nat.sqrt (Nat.log 2 C + 1) + 1)
  have hcutC : ordinaryLadderCutoff A1 ≤ (C : ℝ) := by
    dsimp [C]
    exact Nat.le_ceil _
  have hcross : C ≤ sliceA2LadderP P0 ratio0 eta j := by
    simpa [j] using sliceA2LadderP_crosses_at_sqrt_log
      P0 ratio0 eta C hP0 heta
  apply sliceA2LadderJ_le_of_reaches P0 ratio0 eta A1 hP0 j
  exact hcutC.trans (by exact_mod_cast hcross)

end Tao2015

end MoltResearch
