import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalIntegerMargins

/-!
# Track R A2-V': logarithmic high-moment envelopes

Both exceptional estimates are products of the same four positive factors.
Writing that product as the exponential of an exact logarithmic envelope
turns the remaining cover and damping arguments into additive exponent
bookkeeping.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- Exact logarithm of `ordinaryCoverMomentEnvelope`. -/
noncomputable def sliceA2MomentLogEnvelope (P ell : ℕ) (V : ℝ) : ℝ :=
  Real.pi +
    Real.log (1 + 2 * ((2 ^ ell : ℕ) : ℝ)) +
    2 * Real.log (Nat.factorial ell : ℝ) +
    Real.log (2 +
      (2 * Real.pi * Real.log ((2 * P : ℕ) ^ ell)) ^ 2) -
    (2 * (ell : ℝ)) * Real.log V

theorem ordinaryCoverMomentEnvelope_pos
    (P ell : ℕ) (V : ℝ) (hV : 0 < V) :
    0 < ordinaryCoverMomentEnvelope P ell V := by
  unfold ordinaryCoverMomentEnvelope
  positivity

/-- The closed moment envelope is exactly the exponential of its additive
logarithmic form. -/
theorem ordinaryCoverMomentEnvelope_eq_exp_logEnvelope
    (P ell : ℕ) (V : ℝ) (hV : 0 < V) :
    ordinaryCoverMomentEnvelope P ell V =
      Real.exp (sliceA2MomentLogEnvelope P ell V) := by
  let a : ℝ := 1 + 2 * ((2 ^ ell : ℕ) : ℝ)
  let b : ℝ := Nat.factorial ell
  let c : ℝ := 2 +
    (2 * Real.pi * Real.log ((2 * P : ℕ) ^ ell)) ^ 2
  have hfac : (0 : ℝ) < Nat.factorial ell := by positivity
  have hfirst : (0 : ℝ) < 1 + 2 * ((2 ^ ell : ℕ) : ℝ) := by positivity
  have hlast : (0 : ℝ) < 2 +
      (2 * Real.pi * Real.log ((2 * P : ℕ) ^ ell)) ^ 2 := by positivity
  have ha : 0 < a := by simpa [a] using hfirst
  have hb : 0 < b := by simpa [b] using hfac
  have hc : 0 < c := by simpa [c] using hlast
  have hnum : Real.exp
      (Real.pi + Real.log a + 2 * Real.log b + Real.log c) =
      Real.exp Real.pi * a * b ^ 2 * c := by
    rw [show Real.pi + Real.log a + 2 * Real.log b + Real.log c =
        (Real.pi + Real.log a) + (2 * Real.log b) + Real.log c by ring,
      Real.exp_add, Real.exp_add, Real.exp_add,
      show 2 * Real.log b = ((2 : ℕ) : ℝ) * Real.log b by norm_num,
      Real.exp_nat_mul,
      Real.exp_log ha, Real.exp_log hb, Real.exp_log hc]
  have hden : Real.exp ((2 * (ell : ℝ)) * Real.log V) =
      V ^ (2 * ell) := by
    rw [show (2 * (ell : ℝ)) * Real.log V =
        ((2 * ell : ℕ) : ℝ) * Real.log V by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log hV]
  unfold ordinaryCoverMomentEnvelope sliceA2MomentLogEnvelope
  change (Real.exp Real.pi * a * b ^ 2 * c) / V ^ (2 * ell) = _
  rw [show Real.pi + Real.log a + 2 * Real.log b + Real.log c -
      2 * (ell : ℝ) * Real.log V =
      (Real.pi + Real.log a + 2 * Real.log b + Real.log c) -
        ((2 * (ell : ℝ)) * Real.log V) by ring,
    Real.exp_sub, hnum, hden]

/-- An additive logarithmic certificate bounds one ordinary cover moment. -/
theorem ordinaryCoverMomentEnvelope_le_exp_of_log
    (P ell : ℕ) (V Z : ℝ) (hV : 0 < V)
    (hlog : sliceA2MomentLogEnvelope P ell V ≤ Z) :
    ordinaryCoverMomentEnvelope P ell V ≤ Real.exp Z := by
  rw [ordinaryCoverMomentEnvelope_eq_exp_logEnvelope P ell V hV]
  exact Real.exp_le_exp.mpr hlog

/-- The same logarithmic certificate, with the two damping-log factors
included, proves the literal `Gamma <= 1` input used by the prime leg. -/
theorem primeHighMomentCountCost_damped_fit_of_log
    (P ell : ℕ) (Y : Finset ℕ) (T V Z : ℝ)
    (hP : 1 ≤ P) (hT : 1 ≤ T) (hV : 0 < V)
    (htime : (T + 1) / ((P ^ ell : ℕ) : ℝ) ≤ 1)
    (hmass : ∑ p ∈ Y, (1 : ℝ) / p ≤ 1)
    (hlog : sliceA2MomentLogEnvelope P ell V +
        2 * Real.log (Real.log (2 * T)) ≤ Z) :
    primeHighMomentCountCost P ell Y T V 1 *
        (Real.log (2 * T)) ^ 2 ≤ Real.exp Z := by
  have hmass0 : 0 ≤ ∑ p ∈ Y, (1 : ℝ) / p := by positivity
  have hcost := primeHighMomentCountCost_le_coverEnvelope P ell Y T V
    hP (by linarith) hV htime hmass0 hmass
  have hlog2T : 0 < Real.log (2 * T) := by
    exact Real.log_pos (by linarith)
  have henv := ordinaryCoverMomentEnvelope_eq_exp_logEnvelope P ell V hV
  have hsquare : Real.log (2 * T) ^ 2 =
      Real.exp (2 * Real.log (Real.log (2 * T))) := by
    rw [show 2 * Real.log (Real.log (2 * T)) =
        ((2 : ℕ) : ℝ) * Real.log (Real.log (2 * T)) by norm_num,
      Real.exp_nat_mul, Real.exp_log hlog2T]
  calc
    primeHighMomentCountCost P ell Y T V 1 *
          (Real.log (2 * T)) ^ 2 ≤
        ordinaryCoverMomentEnvelope P ell V *
          (Real.log (2 * T)) ^ 2 :=
      mul_le_mul_of_nonneg_right hcost (sq_nonneg _)
    _ = Real.exp (sliceA2MomentLogEnvelope P ell V +
          2 * Real.log (Real.log (2 * T))) := by
      rw [henv, hsquare, Real.exp_add]
    _ ≤ Real.exp Z := Real.exp_le_exp.mpr hlog

end Tao2015

end MoltResearch
