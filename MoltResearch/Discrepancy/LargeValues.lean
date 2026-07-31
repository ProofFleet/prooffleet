import MoltResearch.Discrepancy.PlancherelHarness
import MoltResearch.Discrepancy.BrunTitchmarsh
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Track C: large values of prime-block phase sums (Track R, C4a)

The kernel toolkit for the C4a window-energy bound: the oscillation kernel
`‖∫_{-L}^{L} e(−sξ) dξ‖ ≤ 1/(π|s|)`, the phase-product law
`e(−uξ)·conj(e(−vξ)) = e(−((u−v)ξ))`, the interval real-part commute, and
the log-separation `log q − log p ≥ (q−p)/q`.

The window-energy expansion (next unit) combines these with the
reciprocal prime-gap sum of `BrunTitchmarsh.lean`: the energy of
`S(ξ) = ∑_{p∈P} (a_p/p)·e(−ξ·log p)` over `[−L, L]` is at most
`2L·∑ 1/p² + (∑ 1/p)·O(loglog P₊)`, which caps the number of
`1`-separated `δE`-large values at `O_δ(1)` — the first leg of the C4
dichotomy.
-/

namespace MoltResearch

namespace ExpSums

open Real MeasureTheory

/-- The oscillation kernel: `‖∫_{-L}^{L} e(−sξ) dξ‖ ≤ 1/(π|s|)`. -/
theorem norm_intervalIntegral_char_le {s : ℝ} (hs : s ≠ 0) (L : ℝ) :
    ‖∫ ξ in (-L)..L, ((Real.fourierChar (-(s * ξ)) : Circle) : ℂ)‖
      ≤ 1/(Real.pi * |s|) := by
  set c : ℂ := (((-(2*Real.pi*s) : ℝ)) : ℂ) * Complex.I with hc_def
  have hc : c ≠ 0 := by
    rw [hc_def]
    simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false,
      Complex.ofReal_eq_zero]
    intro h
    have := Real.pi_ne_zero
    rcases mul_eq_zero.mp (by linarith [h] : (2*Real.pi)*s = 0) with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · norm_num at h2
      · exact this h2
    · exact hs h1
  have hchar : ∀ ξ : ℝ, ((Real.fourierChar (-(s * ξ)) : Circle) : ℂ)
      = Complex.exp (c * ξ) := by
    intro ξ
    rw [Real.fourierChar_apply, hc_def]
    congr 1
    push_cast
    ring
  rw [intervalIntegral.integral_congr (fun ξ _ => hchar ξ)]
  rw [integral_exp_mul_complex hc]
  rw [norm_div]
  have hre : ∀ x : ℝ, (c * (x:ℂ)).re = 0 := by
    intro x
    rw [hc_def]
    simp [Complex.mul_re, Complex.mul_im]
  have h1 : ‖Complex.exp (c * (L:ℂ))‖ = 1 := by
    rw [Complex.norm_exp, hre, Real.exp_zero]
  have h2 : ‖Complex.exp (c * ((-L:ℝ):ℂ))‖ = 1 := by
    rw [Complex.norm_exp, hre, Real.exp_zero]
  have hnum : ‖Complex.exp (c * (L:ℂ)) - Complex.exp (c * ((-L:ℝ):ℂ))‖
      ≤ 2 := by
    calc ‖Complex.exp (c * (L:ℂ)) - Complex.exp (c * ((-L:ℝ):ℂ))‖
        ≤ ‖Complex.exp (c * (L:ℂ))‖ + ‖Complex.exp (c * ((-L:ℝ):ℂ))‖ :=
          norm_sub_le _ _
      _ = 2 := by rw [h1, h2]; norm_num
  have hden : ‖c‖ = 2*Real.pi*|s| := by
    rw [hc_def, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_neg, abs_mul]
    rw [abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)]
  rw [hden]
  have hs0 : (0:ℝ) < |s| := abs_pos.mpr hs
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc ‖Complex.exp (c * (L:ℂ)) - Complex.exp (c * ((-L:ℝ):ℂ))‖
        * (Real.pi * |s|)
      ≤ 2 * (Real.pi * |s|) :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = 1 * (2*Real.pi*|s|) := by ring

/-- Phase products combine: `e(−uξ)·conj(e(−vξ)) = e(−((u−v)ξ))`. -/
theorem char_mul_conj_char (u v ξ : ℝ) :
    ((Real.fourierChar (-(u * ξ)) : Circle) : ℂ)
      * (starRingEnd ℂ) ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ)
      = ((Real.fourierChar (-((u - v) * ξ)) : Circle) : ℂ) := by
  rw [Real.fourierChar_apply, Real.fourierChar_apply, Real.fourierChar_apply]
  rw [← Complex.exp_conj]
  rw [← Complex.exp_add]
  congr 1
  have h1 : (starRingEnd ℂ) ((((2*Real.pi*(-(v*ξ)) : ℝ)):ℂ) * Complex.I)
      = -((((2*Real.pi*(-(v*ξ)) : ℝ)):ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [h1]
  push_cast
  ring

/-- The real part commutes with the interval integral. -/
theorem intervalIntegral_re (g : ℝ → ℂ) {a b : ℝ}
    (hg : IntervalIntegrable g MeasureTheory.volume a b) :
    ∫ ξ in a..b, (g ξ).re = (∫ ξ in a..b, g ξ).re := by
  rcases le_total a b with hab | hab
  · rw [intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_of_le hab]
    exact integral_re hg.1
  · rw [intervalIntegral.integral_of_ge hab,
      intervalIntegral.integral_of_ge hab]
    rw [Complex.neg_re]
    exact congrArg Neg.neg (integral_re hg.2)

/-- `log` separates naturals: `log q − log p ≥ (q−p)/q` for `1 ≤ p < q`. -/
theorem log_sub_log_ge (p q : ℕ) (hp : 1 ≤ p) (hpq : p < q) :
    ((q:ℝ) - p)/q ≤ Real.log q - Real.log p := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  have hq0 : (0:ℝ) < q := by
    have : (0:ℕ) < q := by omega
    exact_mod_cast this
  -- `log(p/q) ≤ p/q − 1` gives `log q − log p ≥ 1 − p/q = (q−p)/q`
  have h1 : Real.log ((p:ℝ)/q) ≤ (p:ℝ)/q - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log ((p:ℝ)/q) = Real.log p - Real.log q :=
    Real.log_div (ne_of_gt hp0) (ne_of_gt hq0)
  have h3 : ((q:ℝ) - p)/q = 1 - (p:ℝ)/q := by
    field_simp
  rw [h3]
  rw [h2] at h1
  linarith

end ExpSums

end MoltResearch
