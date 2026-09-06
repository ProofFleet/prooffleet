import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalAggregateClose

/-!
# Track R A2-V': ordinary lower-scale growth margins

The fixed ladder jump makes every lower endpoint dominate
`P₀^(2^j)`.  Consequently all reciprocal-lower-endpoint collision margins
reduce to one inequality at level zero.
-/

namespace MoltResearch

namespace Tao2015

/-- The lower endpoints retain a double-exponential power of the chosen
bottom endpoint. -/
theorem sliceA2LadderP0_pow_two_pow_le
    (P0 ratio0 eta j : ℕ) (hP0 : 2 ≤ P0) :
    P0 ^ (2 ^ j) ≤ sliceA2LadderP P0 ratio0 eta j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hPj : 1 ≤ sliceA2LadderP P0 ratio0 eta j :=
        (sliceA2LadderP_two_le P0 ratio0 eta j hP0).trans' (by norm_num)
      have hstep : 2 ≤
          sliceA2LadderRatio ratio0 eta j * (100 * (j + 1) ^ 2) := by
        have hr := sliceA2LadderRatio_two_le ratio0 eta j
        have hs0 : 0 < 100 * (j + 1) ^ 2 := by positivity
        have hs : 1 ≤ 100 * (j + 1) ^ 2 := by omega
        exact hr.trans (Nat.le_mul_of_pos_right _ (by omega))
      calc
        P0 ^ (2 ^ (j + 1)) = (P0 ^ (2 ^ j)) ^ 2 := by
          rw [pow_succ, pow_mul]
        _ ≤ sliceA2LadderP P0 ratio0 eta j ^ 2 :=
          pow_le_pow_left' ih 2
        _ ≤ sliceA2LadderP P0 ratio0 eta j ^
            (sliceA2LadderRatio ratio0 eta j * (100 * (j + 1) ^ 2)) :=
          pow_le_pow_right' hPj hstep
        _ = sliceA2LadderP P0 ratio0 eta (j + 1) := by
          rw [sliceA2LadderP_succ, sliceA2LadderQ_eq, pow_mul]

/-- A convenient linear consequence of the retained bottom-endpoint
power. -/
theorem sliceA2LadderP0_mul_two_pow_le
    (P0 ratio0 eta j : ℕ) (hP0 : 2 ≤ P0) :
    P0 * 2 ^ j ≤ sliceA2LadderP P0 ratio0 eta j := by
  have hj : j ≤ 2 ^ j - 1 := by
    have := Nat.lt_two_pow_self (n := j)
    omega
  have hbase : 2 ^ j ≤ P0 ^ j :=
    pow_le_pow_left' hP0 j
  have hpow : P0 ^ j ≤ P0 ^ (2 ^ j - 1) :=
    pow_le_pow_right' (by omega : 1 ≤ P0) hj
  have hlinear : P0 * 2 ^ j ≤ P0 ^ (2 ^ j) := by
    calc
      P0 * 2 ^ j ≤ P0 * P0 ^ (2 ^ j - 1) :=
        Nat.mul_le_mul_left P0 (hbase.trans hpow)
      _ = P0 ^ (2 ^ j) := by
        have hk : 2 ^ j - 1 + 1 = 2 ^ j := by
          have := pow_pos (by norm_num : 0 < (2 : ℕ)) j
          omega
        rw [← pow_succ', hk]
  exact hlinear.trans (sliceA2LadderP0_pow_two_pow_le P0 ratio0 eta j hP0)

/-- Every ordinary collision-prime margin follows from a single fixed
bottom-scale inequality. -/
theorem sliceA2Ordinary_collision_prime_margin
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ)
    (hP0 : 2 ≤ P0) (heps : 0 < eps) (hrho0 : 0 < rho0)
    (hbottom :
      (160 * 2048 : ℝ) * Real.exp Real.pi ≤
        3 * eps ^ 2 * rho0 * P0) :
    160 * Real.exp Real.pi /
        (sliceA2LadderP P0 ratio0 eta j : ℝ) ≤
      sliceA2KappaCollision j * eps ^ 2 * rho0 / 16 := by
  let Pj := sliceA2LadderP P0 ratio0 eta j
  have hPj : (0 : ℝ) < Pj := by
    exact_mod_cast (show 0 < Pj by
      have := sliceA2LadderP_two_le P0 ratio0 eta j hP0
      omega)
  have hscaleNat := sliceA2LadderP0_mul_two_pow_le P0 ratio0 eta j hP0
  have hscale : (P0 : ℝ) * (2 ^ j : ℕ) ≤ Pj := by
    exact_mod_cast hscaleNat
  have hP00 : (0 : ℝ) < P0 := by exact_mod_cast (show 0 < P0 by omega)
  have htwo : (0 : ℝ) < (2 ^ j : ℕ) := by positivity
  have hcross :
      160 * Real.exp Real.pi * (2048 * (2 ^ j : ℕ)) ≤
        3 * eps ^ 2 * rho0 * Pj := by
    calc
      160 * Real.exp Real.pi * (2048 * (2 ^ j : ℕ)) =
          ((160 * 2048 : ℝ) * Real.exp Real.pi) * (2 ^ j : ℕ) := by ring
      _ ≤ (3 * eps ^ 2 * rho0 * P0) * (2 ^ j : ℕ) := by gcongr
      _ ≤ 3 * eps ^ 2 * rho0 * Pj := by
        have hcoef : 0 ≤ 3 * eps ^ 2 * rho0 := by positivity
        calc
          (3 * eps ^ 2 * rho0 * P0) * (2 ^ j : ℕ) =
              (3 * eps ^ 2 * rho0) * ((P0 : ℝ) * (2 ^ j : ℕ)) := by ring
          _ ≤ (3 * eps ^ 2 * rho0) * Pj :=
            mul_le_mul_of_nonneg_left hscale hcoef
  have hrhs : sliceA2KappaCollision j * eps ^ 2 * rho0 / 16 =
      (3 * eps ^ 2 * rho0) / (2048 * (2 : ℝ) ^ j) := by
    unfold sliceA2KappaCollision ordinaryLegShare
    rw [pow_succ]
    field_simp
    ring
  rw [hrhs, div_le_div_iff₀ hPj (by positivity : (0 : ℝ) < 2048 * (2 : ℝ) ^ j)]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hcross
  simpa [mul_assoc, mul_left_comm, mul_comm] using hcross

end Tao2015

end MoltResearch
