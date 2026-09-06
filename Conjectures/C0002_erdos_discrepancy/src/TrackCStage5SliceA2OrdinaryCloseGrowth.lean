import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryCloseEnvelope
import MoltResearch.Discrepancy.VinogradovTypeI

/-!
# Track R A2-V': growth behind the ordinary close margin

Two twentieth-powers of the previous endpoint absorb, respectively, the
sixth logarithmic power and every exponential-in-level prefactor.  This
leaves seven twentieth-powers of decay from the original `9/20` saving.
-/

namespace MoltResearch

namespace Tao2015

/-- Sixth logarithmic powers are eventually below a twentieth power. -/
theorem exists_log_six_le_twentieth_rpow :
    ∃ Q0 : ℕ, 3 ≤ Q0 ∧ ∀ Q : ℕ, Q0 ≤ Q →
      Real.log (Q : ℝ) ^ 6 ≤ (Q : ℝ) ^ (1 / 20 : ℝ) := by
  obtain ⟨Q0, hQ0⟩ := ExpSums.exists_log_pow_le 120 1 (by norm_num)
  refine ⟨max 3 Q0, le_max_left _ _, fun Q hQ => ?_⟩
  have hQlarge : Q0 ≤ Q := (le_max_right 3 Q0).trans hQ
  have hQ3 : 3 ≤ Q := (le_max_left 3 Q0).trans hQ
  have hQ0R : (0 : ℝ) ≤ Q := by positivity
  have hlog0 : 0 ≤ Real.log (Q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q by omega))
  have hraw : Real.log (Q : ℝ) ^ 120 ≤ (Q : ℝ) := by
    simpa using hQ0 Q hQlarge
  have hleft : (Real.log (Q : ℝ) ^ 6) ^ 20 =
      Real.log (Q : ℝ) ^ 120 := by rw [← pow_mul]
  have hright : ((Q : ℝ) ^ (1 / 20 : ℝ)) ^ 20 = (Q : ℝ) := by
    convert Real.rpow_inv_natCast_pow hQ0R (by norm_num : (20 : ℕ) ≠ 0) using 1 <;>
      norm_num
  apply (pow_le_pow_iff_left₀ (pow_nonneg hlog0 6)
    (Real.rpow_nonneg hQ0R _) (by norm_num : (20 : ℕ) ≠ 0)).mp
  rw [hleft, hright]
  exact hraw

/-- At positive level `j`, the previous upper endpoint retains
`P₀^(2^j)`. -/
theorem sliceA2LadderP0_pow_two_pow_le_previous_Q
    (P0 ratio0 eta j : ℕ) (hP0 : 2 ≤ P0) (hj : 0 < j) :
    P0 ^ (2 ^ j) ≤ sliceA2LadderQ P0 ratio0 eta (j - 1) := by
  let Pprev := sliceA2LadderP P0 ratio0 eta (j - 1)
  let Rprev := sliceA2LadderRatio ratio0 eta (j - 1)
  have hbase := sliceA2LadderP0_pow_two_pow_le P0 ratio0 eta (j - 1) hP0
  have hsq : (P0 ^ (2 ^ (j - 1))) ^ 2 ≤ Pprev ^ 2 :=
    pow_le_pow_left' hbase 2
  have hR2 : 2 ≤ Rprev := by
    dsimp [Rprev]
    exact sliceA2LadderRatio_two_le ratio0 eta (j - 1)
  have hPprev1 : 1 ≤ Pprev := by
    dsimp [Pprev]
    have := sliceA2LadderP_two_le P0 ratio0 eta (j - 1) hP0
    omega
  calc
    P0 ^ (2 ^ j) = (P0 ^ (2 ^ (j - 1))) ^ 2 := by
      have hjshape : j - 1 + 1 = j := by omega
      have hpowshape : 2 ^ j = 2 ^ (j - 1) * 2 := by
        calc
          2 ^ j = 2 ^ (j - 1 + 1) := congrArg (fun k : ℕ => 2 ^ k) hjshape.symm
          _ = 2 ^ (j - 1) * 2 := pow_succ _ _
      rw [hpowshape, pow_mul]
    _ ≤ Pprev ^ 2 := hsq
    _ ≤ Pprev ^ Rprev := pow_le_pow_right' hPprev1 hR2
    _ = sliceA2LadderQ P0 ratio0 eta (j - 1) := by
      simp only [Pprev, Rprev, sliceA2LadderQ]

/-- One explicit bottom-scale inequality absorbs a fixed coefficient and
`2^(36j)` at every positive ladder level. -/
theorem sliceA2Ordinary_exponential_cost_le_twentieth_rpow
    (P0 ratio0 eta j : ℕ) (D : ℝ)
    (hP0 : 2 ≤ P0) (hj : 0 < j) (hD : 1 ≤ D)
    (hbottom : D ^ 20 * (2 : ℝ) ^ 720 ≤ P0) :
    D * (2 : ℝ) ^ (36 * j) ≤
      (sliceA2LadderQ P0 ratio0 eta (j - 1) : ℝ) ^ (1 / 20 : ℝ) := by
  let Qprev := sliceA2LadderQ P0 ratio0 eta (j - 1)
  have hjpow : j ≤ 2 ^ j := Nat.lt_two_pow_self.le
  have honepow : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by norm_num)
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hbase0 : 0 ≤ D ^ 20 * (2 : ℝ) ^ 720 := by positivity
  have hbottomPow :
      (D ^ 20 * (2 : ℝ) ^ 720) ^ (2 ^ j) ≤
        (P0 : ℝ) ^ (2 ^ j) := by
    exact pow_le_pow_left₀ hbase0 hbottom (2 ^ j)
  have hDpow : D ^ 20 ≤ D ^ (20 * 2 ^ j) :=
    pow_le_pow_right₀ hD (Nat.mul_le_mul_left 20 honepow)
  have htwoPow : (2 : ℝ) ^ (720 * j) ≤ (2 : ℝ) ^ (720 * 2 ^ j) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left 720 hjpow)
  have hcostPow : (D * (2 : ℝ) ^ (36 * j)) ^ 20 ≤
      (D ^ 20 * (2 : ℝ) ^ 720) ^ (2 ^ j) := by
    calc
      (D * (2 : ℝ) ^ (36 * j)) ^ 20 =
          D ^ 20 * (2 : ℝ) ^ (720 * j) := by
        rw [mul_pow, ← pow_mul]
        congr 2
        omega
      _ ≤ D ^ (20 * 2 ^ j) * (2 : ℝ) ^ (720 * 2 ^ j) :=
        mul_le_mul hDpow htwoPow (by positivity) (by positivity)
      _ = (D ^ 20 * (2 : ℝ) ^ 720) ^ (2 ^ j) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]
  have hQnat := sliceA2LadderP0_pow_two_pow_le_previous_Q
    P0 ratio0 eta j hP0 hj
  have hQ : (P0 : ℝ) ^ (2 ^ j) ≤ (Qprev : ℝ) := by
    norm_num only [Nat.cast_pow]
    exact_mod_cast hQnat
  have hcostQ : (D * (2 : ℝ) ^ (36 * j)) ^ 20 ≤ (Qprev : ℝ) :=
    hcostPow.trans (hbottomPow.trans hQ)
  have hQ0 : (0 : ℝ) ≤ Qprev := by positivity
  have hroot : ((Qprev : ℝ) ^ (1 / 20 : ℝ)) ^ 20 = (Qprev : ℝ) := by
    convert Real.rpow_inv_natCast_pow hQ0 (by norm_num : (20 : ℕ) ≠ 0) using 1 <;>
      norm_num
  apply (pow_le_pow_iff_left₀ (mul_nonneg hD0 (by positivity))
    (Real.rpow_nonneg hQ0 _) (by norm_num : (20 : ℕ) ≠ 0)).mp
  rwa [hroot]

end Tao2015

end MoltResearch
