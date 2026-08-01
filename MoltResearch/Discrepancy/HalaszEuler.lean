import MoltResearch.Discrepancy.MultiplicativeC
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Track C: the Euler-product log bridge, upper direction (Track R, C4b-1)

The pointwise Euler input of the Halász leg: for a completely
multiplicative `f` bounded by `1`, just right of the `1`-line,

  `log ‖L_f(s)‖ ≤ ∑'_p Re(f(p) p^{−s}) + 1`.

This is the mirror of `EulerLogBridge.tsum_re_dirichlet_le_log_norm_LSeries`
(which bounds the prime sum *by* the L-norm), generalized from Dirichlet
characters to arbitrary completely multiplicative bounded `f` via Mathlib's
`EulerProduct.exp_tsum_primes_log_eq_tsum`. Both directions share the same
second-order tail: `∑_p ‖log(1−w_p)⁻¹ − w_p‖ ≤ ∑_p p^{−2} ≤ 1`.

Downstream (C4b-2/3): truncation at `y` and Mertens turn this into
`‖L_f(1 + 1/log y − it)‖ ≤ C · (log y) · exp(−D(f, p^{it}; y)²)` — the
Halász-quality pointwise decay on the non-pretentious range, consumed by
the `𝒯₀`-window bound and the `𝒯₁`-mean-square assembly (C4e).
-/

open Complex

namespace MoltResearch

/-- Telescoping series: `∑_{k≥0} 1/((k+1)(k+2)) = 1` (local copy of W2a's
private lemma). -/
private theorem hasSum_one_div_succ_mul_succ' :
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

/-- The prime square-reciprocal sum is at most `1` (local copy). -/
private theorem tsum_primes_rpow_neg_two_le_one' :
    ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) ≤ 1 := by
  have hsummable : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 : ℝ) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  have htel := hasSum_one_div_succ_mul_succ'
  rw [← htel.tsum_eq]
  refine Summable.tsum_le_tsum_of_inj (fun p : Nat.Primes => (p : ℕ) - 2)
    (fun p q h => ?_) (fun k _ => by positivity) (fun p => ?_) hsummable htel.summable
  · have hp2 := p.prop.two_le
    have hq2 := q.prop.two_le
    have h' : (p : ℕ) - 2 = (q : ℕ) - 2 := h
    exact Subtype.ext (by omega)
  · have hp2 := p.prop.two_le
    have hcast1 : (((p : ℕ) - 2 : ℕ) : ℝ) + 1 = ((p : ℕ) : ℝ) - 1 := by
      push_cast [Nat.cast_sub hp2]
      ring
    have hcast2 : (((p : ℕ) - 2 : ℕ) : ℝ) + 2 = ((p : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hp2]
      ring
    rw [hcast1, hcast2]
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.pos
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

/-- **The Euler-product log bridge, upper direction** (C4b-1): for a
completely multiplicative `f` bounded by `1` with `f 1 = 1` and
`Re s > 1`, the log of the L-series norm is at most the real part of
the prime sum plus `1`. The mirror of
`tsum_re_dirichlet_le_log_norm_LSeries`, for general `f` — the
pointwise Euler input of the Halász leg. -/
theorem log_norm_LSeries_le_tsum_re_add_one
    (f : ℕ → ℂ) (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (hb : ∀ n, ‖f n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Real.log ‖LSeries (fun n => f n) s‖
      ≤ (∑' p : Nat.Primes, (f p * (p : ℂ) ^ (-s)).re) + 1 := by
  classical
  -- package the damped summand as a MonoidWithZeroHom
  set F : ℕ →*₀ ℂ :=
    { toFun := fun n => if n = 0 then 0 else f n * (n : ℂ) ^ (-s)
      map_zero' := by simp
      map_one' := by simp [h1]
      map_mul' := by
        intro a b
        rcases eq_or_ne a 0 with ha | ha
        · simp [ha]
        rcases eq_or_ne b 0 with hb0 | hb0
        · simp [hb0]
        have hab : a * b ≠ 0 := mul_ne_zero ha hb0
        simp only [if_neg ha, if_neg hb0, if_neg hab]
        have hcast : ((a * b : ℕ) : ℂ) ^ (-s)
            = ((a : ℕ) : ℂ) ^ (-s) * ((b : ℕ) : ℂ) ^ (-s) := by
          have h1' : ((a * b : ℕ) : ℂ) = (((a : ℕ) : ℝ) : ℂ) * (((b : ℕ) : ℝ) : ℂ) := by
            push_cast; ring
          have h2' : ((a : ℕ) : ℂ) = (((a : ℕ) : ℝ) : ℂ) := by push_cast; ring
          have h3' : ((b : ℕ) : ℂ) = (((b : ℕ) : ℝ) : ℂ) := by push_cast; ring
          rw [h1', h2', h3',
            mul_cpow_ofReal_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
        rw [hcm a b ha hb0, hcast]
        ring } with hF_def
  have hFapply : ∀ n : ℕ, F n = if n = 0 then 0 else f n * (n : ℂ) ^ (-s) :=
    fun n => rfl
  -- summability of the norms
  have hFsum : Summable (‖F ·‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) (Real.summable_nat_rpow.mpr (by linarith : -s.re < -1))
    rw [hFapply]
    rcases eq_or_ne n 0 with hn | hn
    · simp [hn, Real.zero_rpow (by linarith : -s.re ≠ 0)]
    · rw [if_neg hn, norm_mul]
      have hn0 : (0 : ℝ) < (n : ℝ) := by
        have : 0 < n := Nat.pos_of_ne_zero hn
        exact_mod_cast this
      have hnorm : ‖((n : ℕ) : ℂ) ^ (-s)‖ = ((n : ℕ) : ℝ) ^ (-s.re) := by
        rw [show ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) from by push_cast; rfl,
          Complex.norm_cpow_eq_rpow_re_of_pos hn0]
        simp
      rw [hnorm]
      exact mul_le_of_le_one_left (by positivity) (hb n)
  -- the prime summand
  set w : Nat.Primes → ℂ := fun p => f p * (p : ℂ) ^ (-s) with hw
  have hFw : ∀ p : Nat.Primes, F (p : ℕ) = w p := by
    intro p
    rw [hFapply, if_neg p.prop.ne_zero]
  have hsum : Summable w := by
    have h := hFsum.of_norm.subtype {p | p.Prime}
    refine h.congr ?_
    intro p
    exact hFw p
  have hsumnorm : Summable fun p : Nat.Primes => ‖w p‖ := by
    have h := hFsum.subtype {p | p.Prime}
    refine h.congr ?_
    intro p
    simp only [Function.comp_apply]
    rw [hFw p]
  -- norm bounds on the summand
  have hnormw : ∀ p : Nat.Primes, ‖w p‖ ≤ ((p : ℕ) : ℝ) ^ (-s.re) := by
    intro p
    rw [hw, norm_mul]
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.pos
    have hnorm : ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s.re) := by
      rw [show ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) from by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hp0]
      simp
    rw [hnorm]
    exact mul_le_of_le_one_left (by positivity) (hb p)
  have hhalf : ∀ p : Nat.Primes, ‖w p‖ ≤ 1 / 2 := by
    intro p
    refine le_trans (hnormw p) ?_
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
    calc ((p : ℕ) : ℝ) ^ (-s.re)
        ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 1 / ((p : ℕ) : ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  have hlt1 : ∀ p : Nat.Primes, ‖w p‖ < 1 :=
    fun p => lt_of_le_of_lt (hhalf p) (by norm_num)
  have hsumlog : Summable fun p : Nat.Primes => -Complex.log (1 - w p) :=
    hsum.clog_one_sub.neg
  -- the L-series is the tsum of F
  have hL_eq : LSeries (fun n => f n) s = ∑' n : ℕ, F n := by
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with hn | hn
    · rw [hn, LSeries.term_zero, hFapply]
      simp
    · rw [LSeries.term_of_ne_zero hn, hFapply, if_neg hn, cpow_neg,
        div_eq_mul_inv]
  -- Euler product in exp/log form
  have hexp := EulerProduct.exp_tsum_primes_log_eq_tsum (f := F) hFsum
  have hexp' : Complex.exp (∑' p : Nat.Primes, -Complex.log (1 - w p))
      = ∑' n : ℕ, F n := by
    rw [← hexp]
    congr 1
    exact tsum_congr fun p => by rw [hFw p]
  have hlogL : Real.log ‖LSeries (fun n => f n) s‖
      = ∑' p : Nat.Primes, (-Complex.log (1 - w p)).re := by
    rw [hL_eq, ← hexp', Complex.norm_exp, Real.log_exp, Complex.re_tsum hsumlog]
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
    have hn := hnormw p
    have hw0 : (0 : ℝ) ≤ ‖w p‖ := norm_nonneg _
    have hsq : ‖w p‖ ^ 2 ≤ (((p : ℕ) : ℝ) ^ (-s.re)) ^ 2 :=
      pow_le_pow_left₀ hw0 hn 2
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.pos
    have hexpsq : (((p : ℕ) : ℝ) ^ (-s.re)) ^ 2 = ((p : ℕ) : ℝ) ^ (-(2 * s.re)) := by
      rw [← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-s.re)) 2, ← Real.rpow_mul hp0.le]
      ring_nf
    have hmono : ((p : ℕ) : ℝ) ^ (-(2 * s.re)) ≤ ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le ?_ (by linarith)
      exact_mod_cast p.prop.one_lt.le
    calc ‖w p‖ ^ 2 * (1 - ‖w p‖)⁻¹ / 2
        ≤ ‖w p‖ ^ 2 * 2 / 2 := by
          have h2 : (0 : ℝ) ≤ ‖w p‖ ^ 2 := by positivity
          have := mul_le_mul_of_nonneg_left hinv h2
          linarith
      _ = ‖w p‖ ^ 2 := by ring
      _ ≤ (((p : ℕ) : ℝ) ^ (-s.re)) ^ 2 := hsq
      _ = ((p : ℕ) : ℝ) ^ (-(2 * s.re)) := hexpsq
      _ ≤ ((p : ℕ) : ℝ) ^ (-2 : ℝ) := hmono
  -- summability of the error terms
  have hdiff_sum : Summable fun p : Nat.Primes => -Complex.log (1 - w p) - w p :=
    hsumlog.sub hsum
  -- assemble
  have hre_split : ∀ p : Nat.Primes,
      (-Complex.log (1 - w p)).re = (w p).re + (-Complex.log (1 - w p) - w p).re := by
    intro p
    simp [Complex.sub_re]
  have hsumRe : Summable fun p : Nat.Primes => (w p).re :=
    (Complex.hasSum_re hsum.hasSum).summable
  have hsumErrRe : Summable fun p : Nat.Primes => (-Complex.log (1 - w p) - w p).re :=
    (Complex.hasSum_re hdiff_sum.hasSum).summable
  have hsplit_tsum : ∑' p : Nat.Primes, (-Complex.log (1 - w p)).re
      = (∑' p : Nat.Primes, (w p).re)
        + ∑' p : Nat.Primes, (-Complex.log (1 - w p) - w p).re := by
    rw [← Summable.tsum_add hsumRe hsumErrRe]
    exact tsum_congr hre_split
  have herr_tsum : ∑' p : Nat.Primes, (-Complex.log (1 - w p) - w p).re ≤ 1 := by
    have hsumP2 : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 : ℝ) :=
      Nat.Primes.summable_rpow.mpr (by norm_num)
    calc ∑' p : Nat.Primes, (-Complex.log (1 - w p) - w p).re
        ≤ ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
          refine Summable.tsum_le_tsum (fun p => ?_) hsumErrRe hsumP2
          exact le_trans (le_trans (le_abs_self _) (Complex.abs_re_le_norm _)) (herr p)
      _ ≤ 1 := tsum_primes_rpow_neg_two_le_one'
  rw [hlogL, hsplit_tsum]
  linarith [herr_tsum]

end MoltResearch
