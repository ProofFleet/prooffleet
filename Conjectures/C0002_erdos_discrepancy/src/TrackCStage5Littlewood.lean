import MoltResearch.Discrepancy

/-!
# Track C: Stage 5 — the Littlewood L-bound interface (W3 of issue #2935)

The **standard analytic input** that the VK/Littlewood campaign reduces
`VinogradovKorobovAssumption` to: an upper bound of Littlewood strength on Dirichlet
L-functions just right of the `1`-line,

  `‖L(χ, 1 + 1/log y − it)‖ ≤ C · (log(q(|t|+2)))^{1−c}`,

uniformly in the modulus. This is the textbook consequence of a quantitative zero-free
region (de la Vallée Poussin gives it with any `c < 1` fixed; Vinogradov–Korobov gives
the stronger `(log)^{2/3+ε}`; even Littlewood's `log/log log` refinement is far more
than needed). The **qualitative** non-vanishing on `Re s = 1` in Mathlib
(`DirichletCharacter.LFunction_ne_zero_of_re_eq_one`) is *not* sufficient: the
derivation needs the exponent gain `1 − c` to beat the `log log` main term of the
Mertens floor.

No unconditional instance of this class is (or may be) declared until such a bound is
actually formalized; consumers must carry it as a hypothesis.
-/

namespace MoltResearch

namespace Tao2015

/-- **Littlewood L-bound assumption**: an upper bound of Littlewood strength on
Dirichlet L-values just right of the `1`-line, uniform in the modulus — the standard
consequence of a quantitative zero-free region, and the sole analytic input to which
`VinogradovKorobovAssumption` is reduced (issue #2935). -/
class LittlewoodLBoundAssumption : Prop where
  bound : ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
    ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) (y : ℕ),
      3 ≤ y → 1 ≤ q → 1 ≤ |t| →
      ‖LSeries (fun n => χ n) (((1 + 1 / Real.log y : ℝ) : ℂ) - Complex.I * t)‖
        ≤ C * Real.log ((q : ℝ) * (|t| + 2)) ^ (1 - c)

/-- Consumer-facing restatement, so the W4 assembly can use the bound without
projecting the class field. -/
theorem littlewood_LBound [inst : LittlewoodLBoundAssumption] :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) (y : ℕ),
        3 ≤ y → 1 ≤ q → 1 ≤ |t| →
        ‖LSeries (fun n => χ n) (((1 + 1 / Real.log y : ℝ) : ℂ) - Complex.I * t)‖
          ≤ C * Real.log ((q : ℝ) * (|t| + 2)) ^ (1 - c) :=
  inst.bound

-- Consumer example (compile-only): combined with the truncated Euler-product bridge
-- (`sum_re_twist_div_le_log_norm_LSeries`), the interface bounds the pretense term of
-- the VK interface by `(1−c)·log log(q(|t|+2))` plus constants — the shape the W4
-- assembly feeds into the Mertens floor.
example [LittlewoodLBoundAssumption] {q : ℕ} (χ : DirichletCharacter ℂ q)
    {y : ℕ} (hy : 3 ≤ y) {t : ℝ} (hq : 1 ≤ q) (ht : 1 ≤ |t|) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
      ∑ p ∈ y.primesBelow, (χ p * (p : ℂ) ^ (Complex.I * t)).re / p
        ≤ Real.log (C * Real.log ((q : ℝ) * (|t| + 2)) ^ (1 - c)) + 13 := by
  obtain ⟨c, C, hc0, hc1, hC1, hbound⟩ := littlewood_LBound
  refine ⟨c, C, hc0, hc1, hC1, ?_⟩
  refine le_trans (sum_re_twist_div_le_log_norm_LSeries χ hy t) ?_
  have hL := hbound q χ t y hy hq ht
  rcases eq_or_lt_of_le (norm_nonneg
    (LSeries (fun n => χ n) (((1 + 1 / Real.log y : ℝ) : ℂ) - Complex.I * t))) with h0 | h0
  · rw [← h0, Real.log_zero]
    have hbase : (1 : ℝ) ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have h1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
      have h3 : (3 : ℝ) ≤ (q : ℝ) * (|t| + 2) := by nlinarith [abs_nonneg t]
      linarith [Real.exp_one_lt_d9]
    have hr1 : (1 : ℝ) ≤ Real.log ((q : ℝ) * (|t| + 2)) ^ (1 - c) :=
      calc (1 : ℝ) = Real.log ((q : ℝ) * (|t| + 2)) ^ (0 : ℝ) :=
            (Real.rpow_zero _).symm
        _ ≤ Real.log ((q : ℝ) * (|t| + 2)) ^ (1 - c) :=
            Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    have hlog0 : 0 ≤ Real.log (C * Real.log ((q : ℝ) * (|t| + 2)) ^ (1 - c)) :=
      Real.log_nonneg (by nlinarith)
    linarith
  · linarith [Real.log_le_log h0 hL]

end Tao2015

end MoltResearch
