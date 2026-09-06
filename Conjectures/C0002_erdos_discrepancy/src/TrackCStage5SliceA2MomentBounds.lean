import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2MomentLog

/-!
# Track R A2-V': elementary high-moment logarithmic bounds

This leaf bounds every combinatorial factor in the exact logarithmic moment
envelope.  For the exceptional split, the complete loss is
`200 * ell * loglog A`; no hidden power of the ambient scale remains.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The factorial and large-value logarithms in one moment have the stated
elementary envelope. -/
theorem sliceA2MomentLogEnvelope_exceptional_le
    (A P ell : ℕ) (hA : 3 ≤ A) (hP : 2 ≤ P) (hell : 1 ≤ ell) :
    sliceA2MomentLogEnvelope P ell (exceptionalSplitThreshold A) ≤
      Real.pi + ((ell : ℝ) + 2) * Real.log 2 +
        2 * (ell : ℝ) * Real.log (ell : ℝ) +
        2 * (Real.log 9 + Real.log (ell : ℝ) +
          Real.log (Real.log (2 * (P : ℝ)))) +
        200 * (ell : ℝ) * Real.log (Real.log (A : ℝ)) := by
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hellpos : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
  have hlogA : 0 < Real.log (A : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hlog2P : 1 ≤ Real.log (2 * (P : ℝ)) := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    exact Real.exp_one_lt_three.le.trans (by
      have hPR : (2 : ℝ) ≤ P := by exact_mod_cast hP
      nlinarith)
  have hfirstNat : 1 + 2 * 2 ^ ell ≤ 2 ^ (ell + 2) := by
    have hone : 1 ≤ 2 ^ (ell + 1) := Nat.one_le_pow _ _ (by norm_num)
    calc
      1 + 2 * 2 ^ ell = 1 + 2 ^ (ell + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (ell + 1) + 2 ^ (ell + 1) := by omega
      _ = 2 ^ (ell + 2) := by rw [pow_succ]; ring
  have hfirst : Real.log (1 + 2 * ((2 ^ ell : ℕ) : ℝ)) ≤
      ((ell : ℝ) + 2) * Real.log 2 := by
    have hleft : (0 : ℝ) < 1 + 2 * ((2 ^ ell : ℕ) : ℝ) := by positivity
    have hcast : (1 : ℝ) + 2 * ((2 ^ ell : ℕ) : ℝ) ≤
        ((2 ^ (ell + 2) : ℕ) : ℝ) := by exact_mod_cast hfirstNat
    calc
      Real.log (1 + 2 * ((2 ^ ell : ℕ) : ℝ)) ≤
          Real.log (((2 ^ (ell + 2) : ℕ) : ℝ)) :=
        Real.log_le_log hleft hcast
      _ = ((ell : ℝ) + 2) * Real.log 2 := by
        norm_num only [Nat.cast_pow, Nat.cast_ofNat]
        rw [Real.log_pow]
        norm_num
        ring
  have hfacNat := Nat.factorial_le_pow ell
  have hfac : Real.log (Nat.factorial ell : ℝ) ≤
      (ell : ℝ) * Real.log (ell : ℝ) := by
    have hfacpos : (0 : ℝ) < Nat.factorial ell := by positivity
    have hcast : (Nat.factorial ell : ℝ) ≤ (ell : ℝ) ^ ell := by
      exact_mod_cast hfacNat
    calc
      Real.log (Nat.factorial ell : ℝ) ≤ Real.log ((ell : ℝ) ^ ell) :=
        Real.log_le_log hfacpos hcast
      _ = (ell : ℝ) * Real.log (ell : ℝ) := Real.log_pow _ _
  let z : ℝ := (ell : ℝ) * Real.log (2 * (P : ℝ))
  have hz1 : 1 ≤ z := by
    dsimp [z]
    have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
    nlinarith
  have hlogpow : Real.log ((((2 * P : ℕ) : ℝ) ^ ell)) = z := by
    dsimp [z]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    rw [Real.log_pow]
  have hpi : Real.pi ≤ 4 := Real.pi_lt_four.le
  have hlastRaw : 2 + (2 * Real.pi * z) ^ 2 ≤ (9 * z) ^ 2 := by
    have hz0 : 0 ≤ z := zero_le_one.trans hz1
    have hterm : 2 * Real.pi * z ≤ 8 * z := by nlinarith
    have hsq : (2 * Real.pi * z) ^ 2 ≤ (8 * z) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hterm 2
    nlinarith [sq_nonneg z]
  have hlast : Real.log (2 +
      (2 * Real.pi * Real.log ((2 * P : ℕ) ^ ell)) ^ 2) ≤
      2 * (Real.log 9 + Real.log (ell : ℝ) +
        Real.log (Real.log (2 * (P : ℝ)))) := by
    rw [hlogpow]
    have hleft : (0 : ℝ) < 2 + (2 * Real.pi * z) ^ 2 := by positivity
    have h9z : (0 : ℝ) < 9 * z := by positivity
    calc
      Real.log (2 + (2 * Real.pi * z) ^ 2) ≤ Real.log ((9 * z) ^ 2) :=
        Real.log_le_log hleft hlastRaw
      _ = 2 * Real.log (9 * z) := Real.log_pow _ _
      _ = 2 * (Real.log 9 + Real.log (ell : ℝ) +
          Real.log (Real.log (2 * (P : ℝ)))) := by
        rw [Real.log_mul (by norm_num : (9 : ℝ) ≠ 0) (ne_of_gt (by positivity : 0 < z)),
          show z = (ell : ℝ) * Real.log (2 * (P : ℝ)) by rfl,
          Real.log_mul (ne_of_gt hellpos) (ne_of_gt (lt_of_lt_of_le zero_lt_one hlog2P))]
        ring
  have hVlog : Real.log (exceptionalSplitThreshold A) =
      -100 * Real.log (Real.log (A : ℝ)) := by
    unfold exceptionalSplitThreshold
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (ne_of_gt (pow_pos hlogA 100)), Real.log_one, Real.log_pow]
    ring
  unfold sliceA2MomentLogEnvelope
  rw [hVlog]
  linarith

end Tao2015

end MoltResearch
