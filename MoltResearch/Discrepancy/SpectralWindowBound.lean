import MoltResearch.Discrepancy.ProductFourier
import MoltResearch.Discrepancy.AveragedWindowBound

/-!
# Discrepancy: the spectral window bound

Tao 2015 §2 (arXiv:1509.05363, `Problems/tao2015_derivation_c.md`, issue #2920): the
spectral form of eq. (fpi).  The windowed Plancherel identity
(`avg_normSq_shift_sum_eq`) turns the averaged window bound
(`avg_normSq_window_smoothEval_le`) into a bound on the `‖F̂‖²`-weighted character
windows, and Plancherel plus unimodularity of the sign sequence makes `‖F̂‖²` an exact
probability mass:

* `sum_normSq_prodDFT_smoothEval` — `∑_ξ ‖F̂(ξ)‖² = 1` (the spectral measure is a
  probability distribution — the random frequency `ξ` of the paper);
* `spectral_window_bound` — `∑_ξ ‖F̂(ξ)‖²·‖∑_{j ≤ n} prodChar (piExp j) ξ‖² ≤ B² + 1`
  for `n ≤ X` and `M ≥ r·log₂X·X²`.

The §2 construction (P5) reads these as: the random completely multiplicative function
`g_ξ(p) = e(ξ_p/M)` has `𝔼‖∑_{j≤n} g_ξ(j)‖² ≤ B² + 1` for all `n ≤ X`.
-/

namespace MoltResearch

open Finset

variable {X M : ℕ} [NeZero M]

/-- **The spectral mass is exactly `1`** (Plancherel at a unimodular function): the
`‖F̂‖²` weights of the sign-sequence evaluation form a probability distribution. -/
theorem sum_normSq_prodDFT_smoothEval {f : ℕ → ℤ} (hs : IsSignSequence f) :
    ∑ ξ : PrimeIdx X → ZMod M, ‖prodDFT (smoothEval f X) ξ‖ ^ 2 = 1 := by
  rw [sum_normSq_prodDFT]
  have hone : ∀ x : PrimeIdx X → ZMod M, ‖smoothEval f X x‖ ^ 2 = 1 := by
    intro x
    unfold smoothEval
    rcases hs (dExp X x) with h | h <;> rw [h] <;> norm_num
  rw [Finset.sum_congr rfl fun x _ => hone x, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, ZMod.card, nsmul_eq_mul, mul_one]
  have hM0 : ((M : ℝ)) ^ Fintype.card (PrimeIdx X) ≠ 0 := by
    have := NeZero.ne M
    positivity
  rw [show ((M ^ Fintype.card (PrimeIdx X) : ℕ) : ℝ)
      = ((M : ℝ)) ^ Fintype.card (PrimeIdx X) from by push_cast; ring]
  field_simp

/-- **The spectral window bound** (Tao 2015 §2): the `‖F̂‖²`-weighted character windows
are uniformly small — the estimate that becomes `𝔼‖∑_{j≤n} g_ξ(j)‖² ≤ B² + 1` once
`‖F̂‖²` is read as the law of the random frequency `ξ`. -/
theorem spectral_window_bound {f : ℕ → ℤ} (hs : IsSignSequence f)
    {B : ℕ} (hB : ∀ d n : ℕ, d > 0 → (apSum f d n).natAbs ≤ B)
    {n : ℕ} (hnX : n ≤ X)
    (hM : Fintype.card (PrimeIdx X) * Nat.log 2 X * X ^ 2 ≤ M) :
    ∑ ξ : PrimeIdx X → ZMod M,
        ‖prodDFT (smoothEval f X) ξ‖ ^ 2
          * ‖∑ j ∈ Finset.Icc 1 n, prodChar (piExp X M j) ξ‖ ^ 2
      ≤ (B : ℝ) ^ 2 + 1 := by
  rw [← avg_normSq_shift_sum_eq (Finset.Icc 1 n) (piExp X M) (smoothEval f X)]
  exact avg_normSq_window_smoothEval_le hs hB hnX hM

end MoltResearch
