import MoltResearch.Discrepancy.MultiplicativeC

/-!
# Discrepancy: log-averaged two-point correlation

Language-layer module for the Tao 2015 analytic core (`Problems/tao2015_analytic_core.md`):
the log-averaged two-point correlation that the logarithmically averaged Elliott interface
(arXiv:1509.05422, Thm 1.3) is stated about:

`logAvgCorr g a b N = (∑ n ∈ Icc 1 N, g (n + a) * conj (g (n + b)) / n) / log N`.

Conventions (from the card's decision record):
- division is ℂ-division throughout (`/ (n : ℂ)`, never `Nat` division);
- `Real.log N` junk values at `N ≤ 1` are embraced, not fought: `Real.log 0 = Real.log 1 = 0`
  and ℂ-division by `0` is `0`, so `logAvgCorr g a b N = 0` for `N ≤ 1` — normalized by the
  simp lemmas below.

Degenerate-parameter simp lemmas:
- `logAvgCorr_zero_N` / `logAvgCorr_one_N` — the `N ≤ 1` junk values are `0`.
- `Unimodular.logAvgCorr_self` — the diagonal `a = b` value for unimodular `g` collapses to the
  log-averaged harmonic sum `(∑ n ∈ Icc 1 N, (n : ℂ)⁻¹) / log N` (each correlation term is `1`).
-/

namespace MoltResearch

/-- Log-averaged two-point correlation of a ℂ-valued sequence at shifts `a`, `b` up to `N`:

`logAvgCorr g a b N = (∑ n ∈ Icc 1 N, g (n + a) * conj (g (n + b)) / n) / log N`.

This is the quantity controlled by the logarithmically averaged two-point Elliott theorem
(arXiv:1509.05422): for non-pretentious completely multiplicative unimodular `g` and distinct
shifts it tends to `0`.

Junk-value conventions: ℂ-division by `n` (never `Nat` division), and `Real.log N = 0` for
`N ≤ 1` makes the whole expression `0` there (see `logAvgCorr_zero_N` / `logAvgCorr_one_N`).
-/
noncomputable def logAvgCorr (g : ℕ → ℂ) (a b N : ℕ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 N, g (n + a) * (starRingEnd ℂ) (g (n + b)) / (n : ℂ)) /
    (Real.log N : ℂ)

/-- Degenerate parameter: at `N = 0` the sum is empty, so the correlation is `0`. -/
@[simp] theorem logAvgCorr_zero_N (g : ℕ → ℂ) (a b : ℕ) : logAvgCorr g a b 0 = 0 := by
  simp [logAvgCorr]

/-- Degenerate parameter: at `N = 1` the normalization `Real.log 1 = 0` makes the value `0`
(ℂ-division by zero). -/
@[simp] theorem logAvgCorr_one_N (g : ℕ → ℂ) (a b : ℕ) : logAvgCorr g a b 1 = 0 := by
  simp [logAvgCorr]

namespace Unimodular

variable {g : ℕ → ℂ}

/-- A unimodular value times its own conjugate is `1` (its squared norm). -/
theorem mul_conj_self (hg : Unimodular g) (n : ℕ) :
    g n * (starRingEnd ℂ) (g n) = 1 := by
  rw [Complex.mul_conj]
  norm_cast
  simp [Complex.normSq_eq_norm_sq, hg n]

/-- Diagonal value: for unimodular `g`, the `a = b` correlation collapses to the log-averaged
harmonic sum — each correlation term `g (n + a) * conj (g (n + a))` is `1`.

Normal form: `logAvgCorr g a a N = (∑ n ∈ Icc 1 N, (n : ℂ)⁻¹) / log N`.
-/
theorem logAvgCorr_self (hg : Unimodular g) (a N : ℕ) :
    logAvgCorr g a a N = (∑ n ∈ Finset.Icc 1 N, ((n : ℂ))⁻¹) / (Real.log N : ℂ) := by
  unfold logAvgCorr
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hg.mul_conj_self (n + a), one_div]

end Unimodular

end MoltResearch
