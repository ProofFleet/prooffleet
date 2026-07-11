import MoltResearch.Discrepancy.MultiplicativeC
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Discrepancy: zeta-weighted sums and the Euler product bridge

Language-layer module for the Tao 2015 §4 analysis (`Problems/tao2015_derivation_c.md`,
issue #2871): the zeta-type weighted sums `∑_n g(n)/n^σ` (the paper works at
`σ = 1 + 1/log X`, whose mass `∑ n^{-σ} ≍ log X` acts as a smooth truncation at `X`), and
their Euler products for completely multiplicative 1-bounded `g`.

§4 uses these for the singular series `𝔖 = ∑_n h(n)/n^{1+1/log X}` of the pretentious part
`h` and its character-twisted variants (residue-class equidistribution mod `q^k`).

Encoding notes:
- Junk values: the `n = 0` term is `g 0 / 0^σ = 0` by ℂ-division junk once `σ ≠ 0`
  (`Complex.zero_cpow`), so tsums over all of `ℕ` are safe.
- The bridge to Mathlib's Euler-product machinery is
  `CompletelyMultiplicativeC.zetaWeightHom`: for guarded-CM `g` with `g 1 = 1` the weight
  `n ↦ g n / n^σ` is a genuine `ℕ →*₀ ℂ` — the `0`-guards (issue #2879) cost nothing here
  because the weight vanishes at `0` on its own.
-/

namespace MoltResearch

/-- The zeta-weighted sum `∑_n g(n)/n^σ` (the `n = 0` term vanishes by junk conventions for
`σ ≠ 0`). At `σ = 1 + 1/log X` this is the paper's smooth-truncation-at-`X` average. -/
noncomputable def zetaWeightedSum (g : ℕ → ℂ) (σ : ℝ) : ℂ :=
  ∑' n : ℕ, g n / (n : ℂ) ^ (σ : ℂ)

namespace CompletelyMultiplicativeC

variable {g : ℕ → ℂ}

/-- The zeta weight `n ↦ g n / n^σ` of a completely multiplicative `g` with `g 1 = 1`,
bundled as a `MonoidWithZeroHom` — the shape Mathlib's Euler-product machinery consumes.
The `0`-guards of `CompletelyMultiplicativeC` cost nothing: the weight vanishes at `0`. -/
noncomputable def zetaWeightHom (hg : CompletelyMultiplicativeC g) (hg1 : g 1 = 1)
    {σ : ℝ} (hσ : σ ≠ 0) : ℕ →*₀ ℂ where
  toFun n := g n / (n : ℂ) ^ (σ : ℂ)
  map_zero' := by
    rw [Nat.cast_zero, Complex.zero_cpow (Complex.ofReal_ne_zero.mpr hσ), div_zero]
  map_one' := by simp [hg1]
  map_mul' m n := by
    rcases eq_or_ne m 0 with rfl | hm
    · rw [Nat.zero_mul]
      simp [Complex.zero_cpow (Complex.ofReal_ne_zero.mpr hσ)]
    rcases eq_or_ne n 0 with rfl | hn
    · rw [Nat.mul_zero]
      simp [Complex.zero_cpow (Complex.ofReal_ne_zero.mpr hσ)]
    show g (m * n) / ((m * n : ℕ) : ℂ) ^ (σ : ℂ) = _
    rw [hg m n hm hn]
    push_cast
    rw [Complex.natCast_mul_natCast_cpow, div_mul_div_comm]

@[simp] theorem zetaWeightHom_apply (hg : CompletelyMultiplicativeC g) (hg1 : g 1 = 1)
    {σ : ℝ} (hσ : σ ≠ 0) (n : ℕ) :
    hg.zetaWeightHom hg1 hσ n = g n / (n : ℂ) ^ (σ : ℂ) :=
  rfl

end CompletelyMultiplicativeC

/-- Norm bound for the zeta weight of a 1-bounded sequence: `‖g n / n^σ‖ ≤ 1 / n^σ`
(with the junk `n = 0` term equal to `0` on both sides for `σ > 0`). -/
theorem norm_zetaWeight_le {g : ℕ → ℂ} (hb : ∀ n, ‖g n‖ ≤ 1) {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    ‖g n / (n : ℂ) ^ (σ : ℂ)‖ ≤ 1 / (n : ℝ) ^ σ := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.cast_zero, Complex.zero_cpow (Complex.ofReal_ne_zero.mpr hσ.ne'), div_zero,
      norm_zero, Nat.cast_zero, Real.zero_rpow hσ.ne', div_zero]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [norm_div, show ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) from by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hn', Complex.ofReal_re]
    exact div_le_div_of_nonneg_right (hb n) (Real.rpow_pos_of_pos hn' σ).le

/-- Absolute convergence of the zeta-weighted sum of a 1-bounded sequence at `σ > 1`. -/
theorem summable_norm_zetaWeight {g : ℕ → ℂ} (hb : ∀ n, ‖g n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => ‖g n / (n : ℂ) ^ (σ : ℂ)‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => norm_zetaWeight_le hb (lt_trans one_pos hσ) n) ?_
  exact Real.summable_one_div_nat_rpow.mpr hσ

/-- **Euler product for zeta-weighted completely multiplicative sequences** (the paper's
`𝔖`-computation input): for completely multiplicative 1-bounded `g` with `g 1 = 1` and
`σ > 1`,

`∏'_p (1 − g(p)/p^σ)⁻¹ = ∑'_n g(n)/n^σ`.

Bridge to `EulerProduct.eulerProduct_completely_multiplicative_tprod` via `zetaWeightHom`. -/
theorem tprod_eulerFactor_eq_zetaWeightedSum {g : ℕ → ℂ} (hg : CompletelyMultiplicativeC g)
    (hg1 : g 1 = 1) (hb : ∀ n, ‖g n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    ∏' p : Nat.Primes, (1 - g p / (p : ℂ) ^ (σ : ℂ))⁻¹ = zetaWeightedSum g σ :=
  EulerProduct.eulerProduct_completely_multiplicative_tprod
    (f := hg.zetaWeightHom hg1 (by linarith)) (summable_norm_zetaWeight hb hσ)

end MoltResearch