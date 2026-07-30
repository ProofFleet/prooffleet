import MoltResearch.Discrepancy.LandauLemma
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Track C: the zero-free region substrate (Track R, campaign #3044, phase P4)

The `ζ'/ζ` legs of the zero-free region: the 3-4-1 positivity (the classical
`3 + 4cos θ + cos 2θ = 2(1+cos θ)² ≥ 0` amplification, through the von Mangoldt
L-series), and the pole bound `-ζ'/ζ(σ) ≤ 1/(σ-1) + c` on `(1, 2]` by the
compactness route (the ε-form interfaces permit nonconstructive constants, so
continuity of `-ζ'/ζ - 1/(σ-1)` up to `σ = 1` plus compactness of `[1,2]`
replaces Chebyshev partial summation entirely).

Together with `landau_inequality` and `zeta_strip_bound` these are the only
inputs of the region (P6); the Perron machinery is needed only by the later
prime-sum legs, not here.
-/

namespace MoltResearch

namespace ExpSums

open Complex

/-- The real part of an L-series-style term of a real arithmetic function:
`(f n / n^{σ+it}).re = f n · n^{-σ} · cos (t log n)`. -/
theorem re_term_eq (f : ℕ → ℝ) (σ t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ((f n : ℂ) / (n : ℂ) ^ ((σ:ℂ) + (t:ℂ) * Complex.I)).re
      = f n * (n:ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hnne : ((n:ℕ):ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hcpow : ((n:ℕ):ℂ) ^ ((σ:ℂ) + (t:ℂ) * Complex.I)
      = Complex.exp (((σ:ℂ) + (t:ℂ) * Complex.I) * (Real.log n : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hnne,
      show ((n:ℕ):ℂ) = (((n:ℝ)):ℂ) from by push_cast; ring,
      ← Complex.ofReal_log hn0.le]
    exact congrArg Complex.exp (mul_comm _ _)
  have hdiv : ((f n : ℂ)) / ((n:ℕ):ℂ) ^ ((σ:ℂ) + (t:ℂ) * Complex.I)
      = (f n : ℂ)
        * Complex.exp (-(((σ:ℂ) + (t:ℂ) * Complex.I) * (Real.log n : ℂ))) := by
    rw [hcpow, div_eq_mul_inv, ← Complex.exp_neg]
  rw [hdiv]
  set w : ℂ := -(((σ:ℂ) + (t:ℂ) * Complex.I) * (Real.log n : ℂ)) with hw_def
  have hwre : w.re = -(σ * Real.log n) := by
    rw [hw_def]
    simp only [Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hwim : w.im = -(t * Real.log n) := by
    rw [hw_def]
    simp only [Complex.neg_im, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  rw [show ((f n : ℂ) * Complex.exp w).re = f n * (Complex.exp w).re from by
      rw [Complex.re_ofReal_mul]]
  rw [Complex.exp_re, hwre, hwim, Real.cos_neg]
  have hexp : Real.exp (-(σ * Real.log n)) = (n:ℝ) ^ (-σ) := by
    rw [Real.rpow_def_of_pos hn0]
    congr 1
    ring
  rw [hexp]
  ring

open ArithmeticFunction in
/-- The real part of the von Mangoldt L-series at `σ + it`:
`∑ Λ(n)·n^{-σ}·cos(t log n)`. -/
theorem re_LSeries_vonMangoldt (σ t : ℝ) (hσ : 1 < σ) :
    (LSeries (fun n => (vonMangoldt n : ℂ)) ((σ:ℂ) + (t:ℂ) * Complex.I)).re
      = ∑' n : ℕ, vonMangoldt n * (n:ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
  have hre : ((σ:ℂ) + (t:ℂ) * Complex.I).re = σ := by
    simp
  have hsum : LSeriesSummable (fun n => (vonMangoldt n : ℂ))
      ((σ:ℂ) + (t:ℂ) * Complex.I) := by
    have := LSeriesSummable_vonMangoldt (s := (σ:ℂ) + (t:ℂ) * Complex.I)
      (by rw [hre]; exact hσ)
    exact this
  rw [LSeries, Complex.re_tsum hsum]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with h0 | h1
  · subst h0
    rw [LSeries.term_zero]
    simp
  · rw [LSeries.term_of_ne_zero (by omega : n ≠ 0)]
    exact re_term_eq (fun n => vonMangoldt n) σ t n h1

open ArithmeticFunction in
/-- Summability of the real von Mangoldt series with a cosine weight. -/
theorem summable_vonMangoldt_cos (σ t : ℝ) (hσ : 1 < σ) :
    Summable (fun n : ℕ =>
      vonMangoldt n * (n:ℝ) ^ (-σ) * Real.cos (t * Real.log n)) := by
  have hsum : LSeriesSummable (fun n => (vonMangoldt n : ℂ))
      ((σ:ℂ) + (t:ℂ) * Complex.I) := by
    refine LSeriesSummable_vonMangoldt ?_
    simp [hσ]
  have hre : Summable (fun n =>
      (LSeries.term (fun n => (vonMangoldt n : ℂ))
        ((σ:ℂ) + (t:ℂ) * Complex.I) n).re) :=
    (Complex.hasSum_re hsum.hasSum).summable
  refine hre.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with h0 | h1
  · subst h0
    rw [LSeries.term_zero]
    simp
  · rw [LSeries.term_of_ne_zero (by omega : n ≠ 0)]
    exact re_term_eq (fun n => vonMangoldt n) σ t n h1

open ArithmeticFunction in
/-- **The 3-4-1 positivity**: for `σ > 1`,
`3·Re L(Λ)(σ) + 4·Re L(Λ)(σ+it) + Re L(Λ)(σ+2it) ≥ 0` — termwise
`Λ(n)·n^{-σ}·(3 + 4cos θ + cos 2θ) = Λ(n)·n^{-σ}·2(1+cos θ)² ≥ 0`. -/
theorem vonMangoldt_341_nonneg (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (LSeries (fun n => (vonMangoldt n : ℂ))
        ((σ:ℂ) + ((0:ℝ):ℂ) * Complex.I)).re
      + 4 * (LSeries (fun n => (vonMangoldt n : ℂ))
        ((σ:ℂ) + (t:ℂ) * Complex.I)).re
      + (LSeries (fun n => (vonMangoldt n : ℂ))
        ((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I)).re := by
  rw [re_LSeries_vonMangoldt σ 0 hσ, re_LSeries_vonMangoldt σ t hσ,
    re_LSeries_vonMangoldt σ (2*t) hσ]
  have h1 := summable_vonMangoldt_cos σ 0 hσ
  have h2 := summable_vonMangoldt_cos σ t hσ
  have h3 := summable_vonMangoldt_cos σ (2*t) hσ
  rw [← tsum_mul_left, ← tsum_mul_left]
  rw [← (h1.mul_left 3).tsum_add (h2.mul_left 4),
    ← ((h1.mul_left 3).add (h2.mul_left 4)).tsum_add h3]
  refine tsum_nonneg fun n => ?_
  rcases Nat.eq_zero_or_pos n with h0 | hn1
  · subst h0
    simp
  · set θ : ℝ := t * Real.log n with hθ_def
    have hcos2 : Real.cos (2*t * Real.log n) = 2 * Real.cos θ ^ 2 - 1 := by
      rw [show 2*t * Real.log n = 2 * θ from by rw [hθ_def]; ring,
        Real.cos_two_mul]
    have hcos0 : Real.cos (0 * Real.log n) = 1 := by
      rw [zero_mul, Real.cos_zero]
    rw [hcos0, hcos2]
    have hΛ : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
    have hpow : (0:ℝ) ≤ (n:ℝ) ^ (-σ) := by positivity
    have hkey : 3 * (vonMangoldt n * (n:ℝ) ^ (-σ) * 1)
        + 4 * (vonMangoldt n * (n:ℝ) ^ (-σ) * Real.cos θ)
        + vonMangoldt n * (n:ℝ) ^ (-σ) * (2 * Real.cos θ ^ 2 - 1)
        = vonMangoldt n * (n:ℝ) ^ (-σ) * (2 * (1 + Real.cos θ) ^ 2) := by
      ring
    rw [hkey]
    positivity

end ExpSums

end MoltResearch
