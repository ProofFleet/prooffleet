import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2MomentGamma

/-!
# Track R A2-V': ordinary-cover moment factors

This leaf separates the universal combinatorial factors in a high-moment
cover from the weight-specific logarithmic loss.  It is the ordinary-cover
counterpart of the exceptional split estimate.
-/

namespace MoltResearch

namespace Tao2015

/-- The exact moment envelope is bounded by elementary logarithms plus any
chosen upper bound for its weight loss. -/
theorem sliceA2MomentLogEnvelope_le_of_weightLoss
    (P ell : ℕ) (V E : ℝ) (hP : 2 ≤ P) (hell : 1 ≤ ell)
    (hV : 0 < V)
    (hweight : -(2 * (ell : ℝ)) * Real.log V ≤ E) :
    sliceA2MomentLogEnvelope P ell V ≤
      Real.pi + ((ell : ℝ) + 2) * Real.log 2 +
        2 * (ell : ℝ) * Real.log (ell : ℝ) +
        2 * (Real.log 9 + Real.log (ell : ℝ) +
          Real.log (Real.log (2 * (P : ℝ)))) + E := by
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hellpos : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
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
  have hfac : Real.log (Nat.factorial ell : ℝ) ≤
      (ell : ℝ) * Real.log (ell : ℝ) := by
    have hfacpos : (0 : ℝ) < Nat.factorial ell := by positivity
    have hcast : (Nat.factorial ell : ℝ) ≤ (ell : ℝ) ^ ell := by
      exact_mod_cast Nat.factorial_le_pow ell
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
  have hlastRaw : 2 + (2 * Real.pi * z) ^ 2 ≤ (9 * z) ^ 2 := by
    have hz0 : 0 ≤ z := zero_le_one.trans hz1
    have hterm : 2 * Real.pi * z ≤ 8 * z := by
      nlinarith [Real.pi_lt_four.le]
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
        rw [Real.log_mul (by norm_num) (ne_of_gt (by positivity : 0 < z)),
          show z = (ell : ℝ) * Real.log (2 * (P : ℝ)) by rfl,
          Real.log_mul (ne_of_gt hellpos)
            (ne_of_gt (lt_of_lt_of_le zero_lt_one hlog2P))]
        ring
  unfold sliceA2MomentLogEnvelope
  linarith

end Tao2015

end MoltResearch
