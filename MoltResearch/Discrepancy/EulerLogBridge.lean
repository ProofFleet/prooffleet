import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Discrepancy: the Euler-product log bridge

Track C, VK/Littlewood campaign (`Problems/tao2015_derivation_c.md`, issue #2935, W2a):
for `Re s > 1` and any Dirichlet character `χ`,

  `∑'_p Re(χ(p) p^{−s}) ≤ log ‖L(χ, s)‖ + 1`,

the classical bridge between prime character sums and the logarithm of the L-function:
`log L = ∑_p −log(1 − χ(p)p^{−s})` (Mathlib's Euler-product `exp`/`log` variant), and the
prime-power tail `∑_p ‖log(1−w_p)⁻¹ − w_p‖ ≤ ∑_p p^{−2} ≤ 1` is uniformly bounded.

With the truncation step (W2b/W2c) this turns an upper bound on `‖L‖` just right of the
`1`-line into an upper bound on `∑_{p<y} Re(χ(p)p^{−it})/p` — the pretense term of the
Vinogradov–Korobov interface.
-/

namespace MoltResearch

open Complex

/-- Telescoping series: `∑_{k≥0} 1/((k+1)(k+2)) = 1`. -/
private theorem hasSum_one_div_succ_mul_succ :
    HasSum (fun k : ℕ => (1 : ℝ) / ((k + 1) * (k + 2))) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => by positivity)]
  have hpart : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 : ℝ) / ((k + 1) * (k + 2))
      = 1 - 1 / (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      have h2 : ((m : ℝ) + 2) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
  simp only [hpart]
  have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have := Filter.Tendsto.const_sub (1 : ℝ) h0
  simpa using this

/-- The prime square-reciprocal sum is at most `1`. -/
private theorem tsum_primes_rpow_neg_two_le_one :
    ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) ≤ 1 := by
  have hsummable : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 : ℝ) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  have htel := hasSum_one_div_succ_mul_succ
  rw [← htel.tsum_eq]
  refine Summable.tsum_le_tsum_of_inj (fun p : Nat.Primes => (p : ℕ) - 2)
    (fun p q h => ?_) (fun k _ => by positivity) (fun p => ?_) hsummable htel.summable
  · have hp2 := p.prop.two_le
    have hq2 := q.prop.two_le
    have h' : (p : ℕ) - 2 = (q : ℕ) - 2 := h
    exact Subtype.ext (by omega)
  · have hp2 := p.prop.two_le
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.pos
    have hcast1 : (((p : ℕ) - 2 : ℕ) : ℝ) + 1 = ((p : ℕ) : ℝ) - 1 := by
      have : ((p : ℕ) - 2 : ℕ) = (p : ℕ) - 2 := rfl
      push_cast [Nat.cast_sub hp2]
      ring
    have hcast2 : (((p : ℕ) - 2 : ℕ) : ℝ) + 2 = ((p : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hp2]
      ring
    rw [hcast1, hcast2]
    have hrpow : ((p : ℕ) : ℝ) ^ (-2 : ℝ) = 1 / (((p : ℕ) : ℝ) * ((p : ℕ) : ℝ)) := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) from by norm_num,
        Real.rpow_neg hp0.le, Real.rpow_natCast]
      rw [one_div, sq]
    rw [hrpow]
    have hp1 : (0 : ℝ) < ((p : ℕ) : ℝ) - 1 := by
      have : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hp2
      linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

variable {N : ℕ}

/-- Norm bound for the Dirichlet prime summand: `‖χ(p) p^{−s}‖ ≤ p^{−Re s}`. -/
private theorem norm_dirichlet_summand_le (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) (p : Nat.Primes) :
    ‖χ (p : ℕ) * (p : ℂ) ^ (-s)‖ ≤ ((p : ℕ) : ℝ) ^ (-s.re) := by
  rw [norm_mul]
  have hnorm : ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s).re := by
    rw [← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg _)
        (re_neg_ne_zero_of_one_lt_re hs)]
  rw [hnorm, neg_re]
  exact mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)

/-- The summand norms are at most `1/2` (from `p ≥ 2`, `Re s > 1`). -/
private theorem norm_dirichlet_summand_le_half (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) (p : Nat.Primes) :
    ‖χ (p : ℕ) * (p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  refine le_trans (norm_dirichlet_summand_le χ hs p) ?_
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
  calc ((p : ℕ) : ℝ) ^ (-s.re)
      ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = 1 / ((p : ℕ) : ℝ) := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2

open scoped LSeries.notation in
/-- **The Euler-product log bridge** (Tao 2015 §4 input chain; classical): for `Re s > 1`,
the real part of the prime character sum is controlled by `log ‖L(χ, s)‖` up to an
absolute constant — the prime-power tail of the Euler product contributes at most `1`. -/
theorem tsum_re_dirichlet_le_log_norm_LSeries (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    ∑' p : Nat.Primes, (χ (p : ℕ) * (p : ℂ) ^ (-s)).re
      ≤ Real.log ‖L ↗χ s‖ + 1 := by
  classical
  set w : Nat.Primes → ℂ := fun p => χ (p : ℕ) * (p : ℂ) ^ (-s) with hw
  -- summability of the summands and of their logs
  have hsum : Summable w := by
    have h := (summable_dirichletSummand χ hs).of_norm
    exact h.subtype _
  have hhalf : ∀ p : Nat.Primes, ‖w p‖ ≤ 1 / 2 :=
    fun p => norm_dirichlet_summand_le_half χ hs p
  have hlt1 : ∀ p : Nat.Primes, ‖w p‖ < 1 :=
    fun p => lt_of_le_of_lt (hhalf p) (by norm_num)
  have hsumlog : Summable fun p : Nat.Primes => -Complex.log (1 - w p) :=
    hsum.clog_one_sub.neg
  -- log of the L-value is the real part of the log sum
  have hexp := DirichletCharacter.LSeries_eulerProduct_exp_log χ hs
  have hlogL : Real.log ‖L ↗χ s‖
      = ∑' p : Nat.Primes, (-Complex.log (1 - w p)).re := by
    rw [← hexp, Complex.norm_exp, Real.log_exp, Complex.re_tsum hsumlog]
  -- the per-prime error is second order
  have herr : ∀ p : Nat.Primes,
      ‖-Complex.log (1 - w p) - w p‖ ≤ ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
    intro p
    have hre : (0 : ℝ) < (1 - w p).re := by
      have habs : |(w p).re| ≤ ‖w p‖ := abs_re_le_norm _
      have := hhalf p
      simp only [sub_re, one_re]
      have : (w p).re ≤ 1 / 2 := le_trans (le_abs_self _) (le_trans habs this)
      linarith
    have hlog_inv : Complex.log (1 - w p)⁻¹ = -Complex.log (1 - w p) :=
      Complex.log_inv _ (Complex.slitPlane_arg_ne_pi (Or.inl hre))
    have hbound := Complex.norm_log_one_sub_inv_sub_self_le (hlt1 p)
    rw [hlog_inv] at hbound
    refine le_trans hbound ?_
    have hinv : (1 - ‖w p‖)⁻¹ ≤ 2 := by
      have := hhalf p
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have hn := norm_dirichlet_summand_le χ hs p
    have hw0 : (0 : ℝ) ≤ ‖w p‖ := norm_nonneg _
    have hsq : ‖w p‖ ^ 2 ≤ (((p : ℕ) : ℝ) ^ (-s.re)) ^ 2 := by
      exact pow_le_pow_left₀ hw0 hn 2
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.pos
    have hexpsq : (((p : ℕ) : ℝ) ^ (-s.re)) ^ 2 = ((p : ℕ) : ℝ) ^ (-(2 * s.re)) := by
      rw [← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-s.re)) 2, ← Real.rpow_mul hp0.le]
      ring_nf
    have hmono : ((p : ℕ) : ℝ) ^ (-(2 * s.re)) ≤ ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le ?_ (by linarith)
      have h2p : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
      linarith
    calc ‖w p‖ ^ 2 * (1 - ‖w p‖)⁻¹ / 2
        ≤ ‖w p‖ ^ 2 * 2 / 2 := by
          have : (0 : ℝ) ≤ ‖w p‖ ^ 2 := by positivity
          gcongr
      _ = ‖w p‖ ^ 2 := by ring
      _ ≤ ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
          rw [hexpsq] at hsq
          exact le_trans hsq hmono
  -- assemble
  have hsumErr : Summable fun p : Nat.Primes => -Complex.log (1 - w p) - w p :=
    hsumlog.sub hsum
  have hsumlogRe : Summable fun p : Nat.Primes => (-Complex.log (1 - w p)).re :=
    (Complex.hasSum_re hsumlog.hasSum).summable
  have hsumErrRe : Summable fun p : Nat.Primes => (-Complex.log (1 - w p) - w p).re :=
    (Complex.hasSum_re hsumErr.hasSum).summable
  have hsplit : ∑' p : Nat.Primes, (w p).re
      = (∑' p : Nat.Primes, (-Complex.log (1 - w p)).re)
        - ∑' p : Nat.Primes, (-Complex.log (1 - w p) - w p).re := by
    rw [← Summable.tsum_sub hsumlogRe hsumErrRe]
    congr 1
    funext p
    simp [Complex.sub_re]
  have htail : ∑' p : Nat.Primes, (-Complex.log (1 - w p) - w p).re ≥ -1 := by
    have habs : ∀ p : Nat.Primes, |(-Complex.log (1 - w p) - w p).re|
        ≤ ((p : ℕ) : ℝ) ^ (-2 : ℝ) :=
      fun p => le_trans (abs_re_le_norm _) (herr p)
    have hsummable2 : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 : ℝ) :=
      Nat.Primes.summable_rpow.mpr (by norm_num)
    have hlower : ∀ p : Nat.Primes, -(((p : ℕ) : ℝ) ^ (-2 : ℝ))
        ≤ (-Complex.log (1 - w p) - w p).re :=
      fun p => neg_le_of_abs_le (habs p)
    calc ∑' p : Nat.Primes, (-Complex.log (1 - w p) - w p).re
        ≥ ∑' p : Nat.Primes, -(((p : ℕ) : ℝ) ^ (-2 : ℝ)) :=
          Summable.tsum_le_tsum hlower hsummable2.neg hsumErrRe
      _ = -(∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ)) := by rw [tsum_neg]
      _ ≥ -1 := neg_le_neg tsum_primes_rpow_neg_two_le_one
  rw [hlogL, hsplit]
  linarith

end MoltResearch
