import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalBrunFit

/-!
# Track R A2-V': exceptional quotient logarithm

The fourth-power separation between an exceptional representative and the
window scale leaves half of `log A₁` available after natural-number division.
-/

namespace MoltResearch

namespace Tao2015

/-- If `q⁴ ≤ A₁ ≤ A`, then the integer quotient `A / q` retains at least
half of `log A₁`, once the fixed factor two from division is absorbed. -/
theorem sliceA2Exceptional_quotient_log_lower
    (A1 A q : ℕ) (hA1 : 2 ≤ A1) (hA : A1 ≤ A) (hq : 1 ≤ q)
    (hq4 : q ^ 4 ≤ A1)
    (hlog2 : 4 * Real.log 2 ≤ Real.log (A1 : ℝ)) :
    Real.log (A1 : ℝ) / 2 ≤ Real.log ((A / q : ℕ) : ℝ) := by
  let a := A / q
  have hq0 : 0 < q := by omega
  have hA0 : 0 < A := by omega
  have hq2q4 : q ^ 2 ≤ q ^ 4 :=
    pow_le_pow_right' hq (by omega)
  have hq2A : q * q ≤ A := by
    simpa [pow_two] using hq2q4.trans (hq4.trans hA)
  have hqa : q ≤ a := by
    dsimp [a]
    exact (Nat.le_div_iff_mul_le hq0).2 hq2A
  have ha : 1 ≤ a := hq.trans hqa
  have hA_lt : A < q * (a + 1) := by
    simpa [a] using Nat.lt_mul_div_succ A hq0
  have ha_succ : a + 1 ≤ 2 * a := by omega
  have hA_twoqa : A < 2 * q * a := by
    calc
      A < q * (a + 1) := hA_lt
      _ ≤ q * (2 * a) := Nat.mul_le_mul_left q ha_succ
      _ = 2 * q * a := by ring
  have hlogA1A : Real.log (A1 : ℝ) ≤ Real.log (A : ℝ) := by
    exact Real.log_le_log (by positivity) (by exact_mod_cast hA)
  have hlogA_twoqa : Real.log (A : ℝ) ≤
      Real.log 2 + Real.log (q : ℝ) + Real.log (a : ℝ) := by
    have hcast : (A : ℝ) ≤ 2 * (q : ℝ) * (a : ℝ) := by
      exact_mod_cast hA_twoqa.le
    calc
      Real.log (A : ℝ) ≤ Real.log (2 * (q : ℝ) * (a : ℝ)) :=
        Real.log_le_log (by positivity) hcast
      _ = Real.log 2 + Real.log (q : ℝ) + Real.log (a : ℝ) := by
        rw [Real.log_mul (by positivity : (2 : ℝ) * q ≠ 0)
            (by exact_mod_cast (show a ≠ 0 by omega)),
          Real.log_mul (by norm_num) (by exact_mod_cast hq0.ne')]
  have hlogq : 4 * Real.log (q : ℝ) ≤ Real.log (A1 : ℝ) := by
    have hcast : ((q : ℝ) ^ 4) ≤ (A1 : ℝ) := by exact_mod_cast hq4
    have hlogs := Real.log_le_log (by positivity) hcast
    rw [Real.log_pow] at hlogs
    norm_num at hlogs
    exact hlogs
  linarith

end Tao2015

end MoltResearch
