import MoltResearch.Discrepancy.MultiplicativeC
import MoltResearch.Discrepancy.TruncatedBridge
import MoltResearch.Discrepancy.PretentiousDist
import MoltResearch.Discrepancy.ChebyshevTail
import MoltResearch.Discrepancy.MertensFirst
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.SmoothNumbers
import MoltResearch.Discrepancy.SmoothRankin
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

/-- **The truncated Euler upper bound** (C4b-2): for completely
multiplicative `f` bounded by `1`, the log of the L-norm at
`1 + 1/log y − it` is at most the truncated twisted prime sum plus `13`
— the upper mirror of `sum_re_twist_div_le_log_norm_LSeries`, with the
same three costs (bridge `1`, tail `8`, weight `4`). -/
theorem log_norm_LSeries_le_sum_re_twist_add (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1)
    {y : ℕ} (hy : 3 ≤ y) (t : ℝ) :
    Real.log ‖LSeries (fun n => f n)
        (((1 + 1 / Real.log y : ℝ) : ℂ) - Complex.I * t)‖
      ≤ (∑ p ∈ y.primesBelow, (f p * (p : ℂ) ^ (Complex.I * t)).re / p) + 13 := by
  classical
  set ε : ℝ := 1 / Real.log y with hε
  have hlogy : (1 : ℝ) < Real.log y := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    have h3 : (3 : ℝ) ≤ y := by exact_mod_cast hy
    linarith [Real.exp_one_lt_d9]
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hε1 : ε < 1 := by
    rw [hε, div_lt_one (by linarith)]
    exact hlogy
  set s : ℂ := ((1 + ε : ℝ) : ℂ) - Complex.I * t with hs_def
  have hsre : s.re = 1 + ε := by
    rw [hs_def]
    simp
  have hs1 : 1 < s.re := by rw [hsre]; linarith
  set w : Nat.Primes → ℂ := fun p => f p * (p : ℂ) ^ (-s) with hw
  -- norm bound and summability
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
  have hsumnorm : Summable fun p : Nat.Primes => ‖w p‖ := by
    refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => hnormw p) ?_
    exact Nat.Primes.summable_rpow.mpr (by rw [hsre]; linarith)
  have hsum : Summable w := hsumnorm.of_norm
  -- C4b-1 at s
  have hbridge0 := log_norm_LSeries_le_tsum_re_add_one f hcm h1 hb hs1
  have hbridge : Real.log ‖LSeries (fun n => f n) s‖
      ≤ (∑' p : Nat.Primes, (w p).re) + 1 := hbridge0
  -- the real-part identity
  have hreid : ∀ (p : ℕ), p.Prime →
      (f p * (p : ℂ) ^ (Complex.I * t)).re * (p : ℝ) ^ (-(1 + ε))
        = (f p * (p : ℂ) ^ (-s)).re := by
    intro p hpp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hsplit : ((p : ℕ) : ℂ) ^ (-s)
        = ((p : ℂ) ^ (Complex.I * t)) * ((((p : ℝ) ^ (-(1 + ε)) : ℝ)) : ℂ) := by
      rw [Complex.ofReal_cpow hp0.le]
      push_cast
      rw [← Complex.cpow_add _ _ (by exact_mod_cast hpp.ne_zero)]
      congr 1
      rw [hs_def]
      push_cast
      ring
    rw [hsplit, ← mul_assoc]
    rw [Complex.mul_re]
    simp [Complex.ofReal_re, Complex.ofReal_im]
  -- weight comparison
  have hweight : ∀ (p : ℕ), 2 ≤ p →
      0 ≤ 1 / (p : ℝ) - (p : ℝ) ^ (-(1 + ε))
        ∧ 1 / (p : ℝ) - (p : ℝ) ^ (-(1 + ε)) ≤ ε * Real.log p / p := by
    intro p hp2
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      linarith
    have hfact : (p : ℝ) ^ (-(1 + ε)) = (1 / p) * (p : ℝ) ^ (-ε) := by
      rw [show -(1 + ε) = -1 + -ε from by ring, Real.rpow_add hp0,
        Real.rpow_neg_one, one_div]
    have hexpform : (p : ℝ) ^ (-ε) = Real.exp (-(ε * Real.log p)) := by
      rw [Real.rpow_def_of_pos hp0]
      ring_nf
    have hlogp : (0 : ℝ) ≤ Real.log p :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt hp2)
    constructor
    · rw [hfact]
      have hle1 : (p : ℝ) ^ (-ε) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos
          (by exact_mod_cast Nat.one_le_of_lt hp2) (by linarith)
      have : (0 : ℝ) < 1 / p := by positivity
      nlinarith
    · rw [hfact, hexpform]
      have hexp : 1 - Real.exp (-(ε * Real.log p)) ≤ ε * Real.log p := by
        linarith [Real.add_one_le_exp (-(ε * Real.log p))]
      have h1p : (0 : ℝ) ≤ 1 / p := by positivity
      calc 1 / (p : ℝ) - 1 / p * Real.exp (-(ε * Real.log p))
          = (1 / p) * (1 - Real.exp (-(ε * Real.log p))) := by ring
        _ ≤ (1 / p) * (ε * Real.log p) := by
            refine mul_le_mul_of_nonneg_left ?_ h1p
            exact hexp
        _ = ε * Real.log p / p := by ring
  -- the twist has real part in [−1, 1]
  have htwist1 : ∀ (p : ℕ), p.Prime →
      |(f p * (p : ℂ) ^ (Complex.I * t)).re| ≤ 1 := by
    intro p hpp
    refine le_trans (Complex.abs_re_le_norm _) ?_
    rw [norm_mul]
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hpp.pos
    have hnorm : ‖((p : ℕ) : ℂ) ^ (Complex.I * (t : ℂ))‖ = 1 := by
      rw [show ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) from by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hp0]
      simp
    rw [hnorm, mul_one]
    exact hb p
  -- reversed STEP 1: damped head ≤ twist head + 4
  have hstep1 : ∑ p ∈ y.primesBelow, (f p * (p : ℂ) ^ (-s)).re
      ≤ (∑ p ∈ y.primesBelow, (f p * (p : ℂ) ^ (Complex.I * t)).re / p) + 4 := by
    have hpt : ∀ p ∈ y.primesBelow,
        (f p * (p : ℂ) ^ (-s)).re
          ≤ (f p * (p : ℂ) ^ (Complex.I * t)).re / p + ε * Real.log p / p := by
      intro p hp
      have hpp := Nat.prime_of_mem_primesBelow hp
      have hw' := hweight p hpp.two_le
      rw [← hreid p hpp]
      set R := (f p * (p : ℂ) ^ (Complex.I * t)).re with hRdef
      have habs : |R * ((p:ℝ) ^ (-(1+ε)) - 1/p)| ≤ 1/(p:ℝ) - (p:ℝ) ^ (-(1+ε)) := by
        rw [abs_mul, abs_sub_comm, abs_of_nonneg hw'.1]
        calc |R| * (1/(p:ℝ) - (p:ℝ) ^ (-(1+ε)))
            ≤ 1 * (1/(p:ℝ) - (p:ℝ) ^ (-(1+ε))) :=
              mul_le_mul_of_nonneg_right (htwist1 p hpp) hw'.1
          _ = 1/(p:ℝ) - (p:ℝ) ^ (-(1+ε)) := one_mul _
      have hsplit' : R * (p:ℝ) ^ (-(1+ε)) - R/p = R * ((p:ℝ) ^ (-(1+ε)) - 1/p) := by
        ring
      have h6 := le_abs_self (R * ((p:ℝ) ^ (-(1+ε)) - 1/p))
      linarith [hw'.2]
    calc ∑ p ∈ y.primesBelow, (f p * (p : ℂ) ^ (-s)).re
        ≤ ∑ p ∈ y.primesBelow,
            ((f p * (p : ℂ) ^ (Complex.I * t)).re / p + ε * Real.log p / p) :=
          Finset.sum_le_sum hpt
      _ = (∑ p ∈ y.primesBelow, (f p * (p : ℂ) ^ (Complex.I * t)).re / p)
            + ε * ∑ p ∈ y.primesBelow, Real.log p / p := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun p _ => by ring
      _ ≤ (∑ p ∈ y.primesBelow, (f p * (p : ℂ) ^ (Complex.I * t)).re / p) + 4 := by
          have hm := sum_log_div_primesBelow_le y
          have h4 : ε * ∑ p ∈ y.primesBelow, Real.log p / p ≤ 4 := by
            calc ε * ∑ p ∈ y.primesBelow, Real.log p / p
                ≤ ε * (4 * Real.log y) :=
                  mul_le_mul_of_nonneg_left hm hε0.le
              _ = 4 * (ε * Real.log y) := by ring
              _ = 4 := by
                  rw [hε]
                  field_simp
          linarith
  -- the finset of primes below y, as a finset of Nat.Primes
  set Sy : Finset Nat.Primes := y.primesBelow.attach.image
    (fun q => (⟨q.1, Nat.prime_of_mem_primesBelow q.2⟩ : Nat.Primes)) with hSy
  have hmemSy : ∀ P : Nat.Primes, P ∈ Sy ↔ (P : ℕ) < y := by
    intro P
    constructor
    · intro hP
      rw [hSy, Finset.mem_image] at hP
      obtain ⟨q, -, rfl⟩ := hP
      exact Nat.lt_of_mem_primesBelow q.2
    · intro hP
      rw [hSy, Finset.mem_image]
      exact ⟨⟨(P : ℕ), Nat.mem_primesBelow.mpr ⟨hP, P.prop⟩⟩,
        Finset.mem_attach _ _, Subtype.ext rfl⟩
  have hsum_eq : ∑ p ∈ y.primesBelow, (f p * (p : ℂ) ^ (-s)).re
      = ∑ P ∈ Sy, (w P).re := by
    have h1' : ∑ P ∈ Sy, (w P).re
        = ∑ q ∈ y.primesBelow.attach, (f q.1 * (q.1 : ℂ) ^ (-s)).re := by
      rw [hSy]
      exact Finset.sum_image fun q _ r _ h =>
        Subtype.ext (congrArg (Subtype.val : Nat.Primes → ℕ) h)
    have h2' : ∑ q ∈ y.primesBelow.attach, (f q.1 * (q.1 : ℂ) ^ (-s)).re
        = ∑ p ∈ y.primesBelow, (f p * (p : ℂ) ^ (-s)).re :=
      Finset.sum_attach y.primesBelow (fun p => (f p * (p : ℂ) ^ (-s)).re)
    exact (h1'.trans h2').symm
  -- split the full tsum
  have hsumRe : Summable fun P : Nat.Primes => (w P).re :=
    (Complex.hasSum_re hsum.hasSum).summable
  have htail_f : Summable fun P : Nat.Primes =>
      (if y ≤ (P : ℕ) then (w P).re else 0) := by
    refine Summable.of_norm_bounded (g := fun P : Nat.Primes => ‖w P‖) hsumnorm ?_
    intro P
    by_cases h : y ≤ (P : ℕ) <;> simp [h, Complex.abs_re_le_norm]
  have hhead_f : Summable fun P : Nat.Primes =>
      (if (P : ℕ) < y then (w P).re else 0) := by
    refine Summable.of_norm_bounded (g := fun P : Nat.Primes => ‖w P‖) hsumnorm ?_
    intro P
    by_cases h : (P : ℕ) < y <;> simp [h, Complex.abs_re_le_norm]
  have hsplit_pt : ∀ P : Nat.Primes,
      (w P).re = (if (P : ℕ) < y then (w P).re else 0)
        + (if y ≤ (P : ℕ) then (w P).re else 0) := by
    intro P
    by_cases h : (P : ℕ) < y
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  have hhead_eq : ∑' P : Nat.Primes, (if (P : ℕ) < y then (w P).re else 0)
      = ∑ P ∈ Sy, (w P).re := by
    rw [tsum_eq_sum (s := Sy) (fun P hP => if_neg (fun hlt => hP ((hmemSy P).mpr hlt)))]
    exact Finset.sum_congr rfl fun P hP => if_pos ((hmemSy P).mp hP)
  have htsum_split : ∑' P : Nat.Primes, (w P).re
      = (∑ P ∈ Sy, (w P).re)
        + ∑' P : Nat.Primes, (if y ≤ (P : ℕ) then (w P).re else 0) := by
    rw [← hhead_eq, ← Summable.tsum_add hhead_f htail_f]
    exact tsum_congr hsplit_pt
  -- the tail is at most 8
  have htail_le : ∑' P : Nat.Primes, (if y ≤ (P : ℕ) then (w P).re else 0) ≤ 8 := by
    have hbound : ∀ P : Nat.Primes,
        (if y ≤ (P : ℕ) then (w P).re else 0)
          ≤ (if y ≤ (P : ℕ) then ((P : ℕ) : ℝ) ^ (-(1 + ε)) else 0) := by
      intro P
      by_cases h : y ≤ (P : ℕ)
      · rw [if_pos h, if_pos h]
        have h1' : |(w P).re| ≤ ‖w P‖ := Complex.abs_re_le_norm _
        have h2' : ‖w P‖ ≤ ((P : ℕ) : ℝ) ^ (-s.re) := hnormw P
        rw [hsre] at h2'
        have := le_abs_self (w P).re
        linarith
      · rw [if_neg h, if_neg h]
    have hsummable_tail : Summable fun P : Nat.Primes =>
        (if y ≤ (P : ℕ) then ((P : ℕ) : ℝ) ^ (-(1 + ε)) else 0) := by
      refine Summable.of_nonneg_of_le (fun P => by positivity) (fun P => ?_)
        (Nat.Primes.summable_rpow.mpr (show -(1 + ε) < -1 by linarith))
      by_cases h : y ≤ (P : ℕ)
      · rw [if_pos h]
      · rw [if_neg h]; positivity
    have htail8 := tsum_primes_tail_rpow_le hy
    rw [← hε] at htail8
    calc ∑' P : Nat.Primes, (if y ≤ (P : ℕ) then (w P).re else 0)
        ≤ ∑' P : Nat.Primes,
            (if y ≤ (P : ℕ) then ((P : ℕ) : ℝ) ^ (-(1 + ε)) else 0) :=
          Summable.tsum_le_tsum hbound htail_f hsummable_tail
      _ ≤ 8 := htail8
  -- assemble
  have hLform : LSeries (fun n => f n) s
      = LSeries (fun n => f n) (((1 + 1 / Real.log y : ℝ) : ℂ) - Complex.I * t) := by
    rw [hs_def, hε]
  rw [← hLform]
  calc Real.log ‖LSeries (fun n => f n) s‖
      ≤ (∑' p : Nat.Primes, (w p).re) + 1 := hbridge
    _ = ((∑ P ∈ Sy, (w P).re)
          + ∑' P : Nat.Primes, (if y ≤ (P : ℕ) then (w P).re else 0)) + 1 := by
        rw [htsum_split]
    _ ≤ (∑ P ∈ Sy, (w P).re) + 8 + 1 := by linarith [htail_le]
    _ = (∑ p ∈ y.primesBelow, (f p * (p : ℂ) ^ (-s)).re) + 9 := by
        rw [hsum_eq]
        ring
    _ ≤ ((∑ p ∈ y.primesBelow, (f p * (p : ℂ) ^ (Complex.I * t)).re / p) + 4) + 9 := by
        linarith [hstep1]
    _ = (∑ p ∈ y.primesBelow, (f p * (p : ℂ) ^ (Complex.I * t)).re / p) + 13 := by
        ring


/-- **The Halász-quality ratio bound** (C4b-3): for completely
multiplicative `f` bounded by `1`, the L-norm at `1 + 1/log y − it` is
at most the zeta value at the same abscissa damped by
`exp(−D(f, n^{−it}; y)²)`, up to `e^{26}`. The prime mass cancels
exactly between the two bridge directions — no Mertens asymptotic, no
log-power loss. -/
theorem norm_LSeries_le_zeta_mul_exp (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1)
    {y : ℕ} (hy : 3 ≤ y) (t : ℝ) :
    ‖LSeries (fun n => f n) (((1 + 1 / Real.log y : ℝ) : ℂ) - Complex.I * t)‖
      ≤ ‖LSeries (fun _ => (1 : ℂ)) (((1 + 1 / Real.log y : ℝ) : ℂ))‖
        * Real.exp (26
            - pretentiousDistSq f (fun n => (n : ℂ) ^ (-(Complex.I * t))) y) := by
  classical
  have hσ1 : (1 : ℝ) < 1 + 1 / Real.log y := by
    have hlogy : (1 : ℝ) < Real.log y := by
      rw [Real.lt_log_iff_exp_lt (by positivity)]
      have h3 : (3 : ℝ) ≤ y := by exact_mod_cast hy
      linarith [Real.exp_one_lt_d9]
    have : (0 : ℝ) < 1 / Real.log y := by positivity
    linarith
  -- (A) the truncated twisted sum is mass minus distance
  have hconj : ∀ (p : ℕ), p.Prime →
      (starRingEnd ℂ) (((p : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ))))
        = ((p : ℕ) : ℂ) ^ (Complex.I * (t : ℂ)) := by
    intro p hpp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hplus : ((p : ℕ) : ℂ) ^ (Complex.I * (t : ℂ))
        = Complex.exp (((t * Real.log p : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.cpow_def_of_ne_zero
        (by exact_mod_cast hpp.ne_zero)]
      congr 1
      push_cast
      ring
    have hminus : ((p : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))
        = Complex.exp (-(((t * Real.log p : ℝ) : ℂ) * Complex.I)) := by
      rw [Complex.cpow_def_of_ne_zero
        (by exact_mod_cast hpp.ne_zero)]
      congr 1
      push_cast
      ring
    rw [hminus, ← Complex.exp_conj, hplus]
    congr 1
    rw [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hDistEq : ∑ p ∈ y.primesBelow, (f p * (p : ℂ) ^ (Complex.I * t)).re / p
      = (∑ p ∈ y.primesBelow, (1 : ℝ) / p)
        - pretentiousDistSq f (fun n => (n : ℂ) ^ (-(Complex.I * t))) y := by
    rw [pretentiousDistSq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpp := Nat.prime_of_mem_primesBelow hp
    rw [hconj p hpp]
    ring
  -- (B) the mass is bounded by the zeta log (lower bridge at χ = 1, t = 0)
  have hlow : (∑ p ∈ y.primesBelow, (1 : ℝ) / p)
      ≤ Real.log ‖LSeries (fun _ => (1 : ℂ))
          (((1 + 1 / Real.log y : ℝ) : ℂ))‖ + 13 := by
    have hbridge := sum_re_twist_div_le_log_norm_LSeries
      (N := 1) (1 : DirichletCharacter ℂ 1) hy 0
    have hsummand : ∀ p ∈ y.primesBelow,
        (((1 : DirichletCharacter ℂ 1) p
            * (p : ℂ) ^ (Complex.I * ((0 : ℝ) : ℂ))).re) / p = (1 : ℝ) / p := by
      intro p hp
      have hχ : (1 : DirichletCharacter ℂ 1) p = 1 :=
        congrFun (DirichletCharacter.modOne_eq_one
          (χ := (1 : DirichletCharacter ℂ 1))) p
      rw [hχ, one_mul]
      norm_num
    rw [Finset.sum_congr rfl hsummand] at hbridge
    have hLconv : LSeries (fun n => (1 : DirichletCharacter ℂ 1) n)
        = LSeries (fun _ => 1) := by
      congr 1
      funext n
      exact congrFun (DirichletCharacter.modOne_eq_one
        (χ := (1 : DirichletCharacter ℂ 1))) n
    rw [hLconv] at hbridge
    have hpt : (((1 + 1 / Real.log y : ℝ) : ℂ) - Complex.I * ((0 : ℝ) : ℂ))
        = ((1 + 1 / Real.log y : ℝ) : ℂ) := by
      simp
    rw [hpt] at hbridge
    exact hbridge
  -- (C) the zeta norm is at least 1
  have hζsum : LSeriesSummable (fun _ => (1 : ℂ))
      (((1 + 1 / Real.log y : ℝ) : ℂ)) := by
    refine LSeriesSummable_of_bounded_of_one_lt_re
      (m := 1) (fun n _ => by norm_num) ?_
    rw [Complex.ofReal_re]
    exact hσ1
  have hterm_re : ∀ n : ℕ,
      (LSeries.term (fun _ => (1 : ℂ)) (((1 + 1 / Real.log y : ℝ) : ℂ)) n).re
        = if n = 0 then 0 else 1 / (n : ℝ) ^ (1 + 1 / Real.log y) := by
    intro n
    rcases eq_or_ne n 0 with hn | hn
    · rw [hn]
      simp
    · rw [LSeries.term_of_ne_zero hn, if_neg hn]
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hcpow : ((n : ℕ) : ℂ) ^ (((1 + 1 / Real.log y : ℝ)) : ℂ)
          = (((n : ℝ) ^ (1 + 1 / Real.log y) : ℝ) : ℂ) := by
        rw [show ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) from by push_cast; rfl,
          ← Complex.ofReal_cpow hn0]
      rw [hcpow, show (1 : ℂ) = ((1 : ℝ) : ℂ) from by norm_num,
        ← Complex.ofReal_div, Complex.ofReal_re]
  have hζre : (1 : ℝ)
      ≤ (LSeries (fun _ => (1 : ℂ)) (((1 + 1 / Real.log y : ℝ) : ℂ))).re := by
    have hsumre : Summable fun n : ℕ =>
        (LSeries.term (fun _ => (1 : ℂ)) (((1 + 1 / Real.log y : ℝ) : ℂ)) n).re :=
      (Complex.hasSum_re hζsum.hasSum).summable
    have hre_eq : (LSeries (fun _ => (1 : ℂ)) (((1 + 1 / Real.log y : ℝ) : ℂ))).re
        = ∑' n : ℕ,
            (LSeries.term (fun _ => (1 : ℂ)) (((1 + 1 / Real.log y : ℝ) : ℂ)) n).re :=
      Complex.re_tsum hζsum
    rw [hre_eq]
    have hone : (LSeries.term (fun _ => (1 : ℂ))
        (((1 + 1 / Real.log y : ℝ) : ℂ)) 1).re = 1 := by
      rw [hterm_re]
      norm_num
    calc (1 : ℝ)
        = (LSeries.term (fun _ => (1 : ℂ)) (((1 + 1 / Real.log y : ℝ) : ℂ)) 1).re :=
          hone.symm
      _ ≤ ∑' n : ℕ, (LSeries.term (fun _ => (1 : ℂ))
            (((1 + 1 / Real.log y : ℝ) : ℂ)) n).re := by
          refine hsumre.le_tsum 1 fun n hn => ?_
          rw [hterm_re]
          rcases eq_or_ne n 0 with h0 | h0
          · rw [if_pos h0]
          · rw [if_neg h0]
            positivity
  have hζpos : (0 : ℝ)
      < ‖LSeries (fun _ => (1 : ℂ)) (((1 + 1 / Real.log y : ℝ) : ℂ))‖ := by
    have habs := Complex.abs_re_le_norm
      (LSeries (fun _ => (1 : ℂ)) (((1 + 1 / Real.log y : ℝ) : ℂ)))
    have := le_abs_self
      (LSeries (fun _ => (1 : ℂ)) (((1 + 1 / Real.log y : ℝ) : ℂ))).re
    linarith
  -- (D) assemble
  have hup := log_norm_LSeries_le_sum_re_twist_add f hcm h1 hb hy t
  rw [hDistEq] at hup
  rcases eq_or_lt_of_le (norm_nonneg (LSeries (fun n => f n)
      (((1 + 1 / Real.log y : ℝ) : ℂ) - Complex.I * t))) with h0 | h0
  · rw [← h0]
    positivity
  · have hlog : Real.log ‖LSeries (fun n => f n)
        (((1 + 1 / Real.log y : ℝ) : ℂ) - Complex.I * t)‖
        ≤ Real.log ‖LSeries (fun _ => (1 : ℂ)) (((1 + 1 / Real.log y : ℝ) : ℂ))‖
          + (26 - pretentiousDistSq f (fun n => (n : ℂ) ^ (-(Complex.I * t))) y) := by
      linarith [hup, hlow]
    calc ‖LSeries (fun n => f n) (((1 + 1 / Real.log y : ℝ) : ℂ) - Complex.I * t)‖
        = Real.exp (Real.log ‖LSeries (fun n => f n)
            (((1 + 1 / Real.log y : ℝ) : ℂ) - Complex.I * t)‖) :=
          (Real.exp_log h0).symm
      _ ≤ Real.exp (Real.log ‖LSeries (fun _ => (1 : ℂ))
            (((1 + 1 / Real.log y : ℝ) : ℂ))‖
          + (26 - pretentiousDistSq f (fun n => (n : ℂ) ^ (-(Complex.I * t))) y)) :=
          Real.exp_le_exp.mpr hlog
      _ = Real.exp (Real.log ‖LSeries (fun _ => (1 : ℂ))
            (((1 + 1 / Real.log y : ℝ) : ℂ))‖)
          * Real.exp (26
              - pretentiousDistSq f (fun n => (n : ℂ) ^ (-(Complex.I * t))) y) :=
          Real.exp_add _ _
      _ = ‖LSeries (fun _ => (1 : ℂ)) (((1 + 1 / Real.log y : ℝ) : ℂ))‖
          * Real.exp (26
              - pretentiousDistSq f (fun n => (n : ℂ) ^ (-(Complex.I * t))) y) := by
          rw [Real.exp_log hζpos]


/-- Primes below the cut are smooth. -/
theorem prime_mem_smoothNumbers {p y : ℕ} (hp : p.Prime) (hpy : p < y) :
    p ∈ Nat.smoothNumbers y := by
  rw [Nat.mem_smoothNumbers']
  intro q hq hqp
  have := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
  omega

/-- The smooth restriction of a completely multiplicative function is
completely multiplicative. -/
theorem completelyMultiplicativeC_smooth_restrict (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (y : ℕ) :
    CompletelyMultiplicativeC
      (fun n => if n ∈ Nat.smoothNumbers y then f n else 0) := by
  classical
  intro a b ha hb
  dsimp only
  by_cases hab : a * b ∈ Nat.smoothNumbers y
  · have haS : a ∈ Nat.smoothNumbers y :=
      Nat.mem_smoothNumbers_of_dvd hab ⟨b, rfl⟩
    have hbS : b ∈ Nat.smoothNumbers y :=
      Nat.mem_smoothNumbers_of_dvd hab ⟨a, mul_comm a b⟩
    rw [if_pos hab, if_pos haS, if_pos hbS, hcm a b ha hb]
  · rw [if_neg hab]
    by_cases haS : a ∈ Nat.smoothNumbers y
    · by_cases hbS : b ∈ Nat.smoothNumbers y
      · exact absurd (Nat.mul_mem_smoothNumbers haS hbS) hab
      · rw [if_neg hbS, mul_zero]
    · rw [if_neg haS, zero_mul]

/-- The smooth restriction agrees with `f` on every distance summand
below the cut. -/
theorem pretentiousDistSq_smooth_restrict (f : ℕ → ℂ) (h : ℕ → ℂ)
    (y : ℕ) :
    pretentiousDistSq
        (fun n => if n ∈ Nat.smoothNumbers y then f n else 0) h y
      = pretentiousDistSq f h y := by
  classical
  unfold pretentiousDistSq
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpp := Nat.prime_of_mem_primesBelow hp
  have hpy := (Nat.mem_primesBelow.mp hp).1
  dsimp only
  rw [if_pos (prime_mem_smoothNumbers hpp hpy)]

/-- **The cheap-Halász `L^∞` factor** (Track R, M2-h): the small-prime
Euler factor `F₁ = L_{f·1_{y-smooth}}` on the shifted line is bounded
by the zeta head damped by the scale-`x` distance, at the affordable
transfer price `10·(loglog x − loglog y) + 30`. -/
theorem norm_LSeries_smooth_le_zeta_mul_exp (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (hb : ∀ n, ‖f n‖ ≤ 1) {y x : ℕ} (hy : 4 ≤ y) (hyx : y ≤ x) (t : ℝ) :
    ‖LSeries (fun n => if n ∈ Nat.smoothNumbers y then f n else 0)
        (((1 + 1 / Real.log y : ℝ) : ℂ) - Complex.I * t)‖
      ≤ ‖LSeries (fun _ => (1 : ℂ)) (((1 + 1 / Real.log y : ℝ) : ℂ))‖
        * Real.exp (56
            + 10*(Real.log (Real.log x) - Real.log (Real.log y))
            - pretentiousDistSq f (fun n => (n : ℂ) ^ (-(Complex.I * t))) x) := by
  classical
  set g : ℕ → ℂ := fun n => if n ∈ Nat.smoothNumbers y then f n else 0
    with hg_def
  have hgcm := completelyMultiplicativeC_smooth_restrict f hcm y
  have hg1 : g 1 = 1 := by
    rw [hg_def]
    dsimp only
    rw [if_pos (by
      rw [Nat.mem_smoothNumbers']
      intro q hq hq1
      have := Nat.le_of_dvd (by norm_num) hq1
      have := hq.two_le
      omega), h1]
  have hgb : ∀ n, ‖g n‖ ≤ 1 := by
    intro n
    rw [hg_def]
    dsimp only
    split
    · exact hb n
    · simp
  have hratio := norm_LSeries_le_zeta_mul_exp g hgcm hg1 hgb
    (y := y) (by omega) t
  refine le_trans hratio ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [Real.exp_le_exp]
  -- distance bookkeeping
  have hDeq : pretentiousDistSq g
        (fun n => (n : ℂ) ^ (-(Complex.I * t))) y
      = pretentiousDistSq f
        (fun n => (n : ℂ) ^ (-(Complex.I * t))) y :=
    pretentiousDistSq_smooth_restrict f _ y
  have hb1 : ∀ p : ℕ, ‖(fun n => (n:ℂ) ^ (-(Complex.I * (t:ℂ)))) p‖ ≤ 1 := by
    intro p
    dsimp only
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp
      rcases eq_or_ne (-(Complex.I * (t:ℂ))) 0 with h0 | h0
      · simp [h0]
      · simp [Complex.zero_cpow h0]
    · rw [Complex.norm_natCast_cpow_of_pos hp]
      rw [show (-(Complex.I * (t:ℂ))).re = 0 from by simp]
      rw [Real.rpow_zero]
  have htransfer := pretentiousDistSq_le_add_mass f
    (fun n => (n : ℂ) ^ (-(Complex.I * t))) hb hb1 hyx
  have hmass := mass_diff_le y x hy hyx
  rw [hDeq]
  linarith [htransfer, hmass]


/-- **The finite Euler identity on the closed half-plane**
(Track R, M2-i4a1): a `y`-smooth completely multiplicative `1`-bounded
function has an absolutely convergent Dirichlet series at any `s` with
`Re s = 1`, equal to the finite Euler product over the primes below
the cut. -/
theorem smooth_tsum_eq_finprod (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (hb : ∀ n, ‖f n‖ ≤ 1) (y : ℕ) (hy : 1 ≤ y) (s : ℂ) (hs : s.re = 1) :
    ∑' n : ℕ, (if n ∈ Nat.smoothNumbers y then f n else 0)
        * (if n = 0 then 0 else (n:ℂ)^(-s))
      = ∏ p ∈ y.primesBelow,
          (1 - (f p) * (p:ℂ)^(-s))⁻¹ := by
  classical
  set g : ℕ → ℂ := fun n => if n ∈ Nat.smoothNumbers y then f n else 0
    with hg_def
  have hgcm : ∀ a b : ℕ, a ≠ 0 → b ≠ 0 → g (a*b) = g a * g b := by
    intro a b ha hb
    rw [hg_def]
    exact completelyMultiplicativeC_smooth_restrict f hcm y a b ha hb
  have hg1 : g 1 = 1 := by
    rw [hg_def]
    dsimp only
    rw [if_pos (by
      rw [Nat.mem_smoothNumbers']
      intro q hq hq1
      have := Nat.le_of_dvd (by norm_num) hq1
      have := hq.two_le
      omega), h1]
  have hgb : ∀ n, ‖g n‖ ≤ 1 := by
    intro n
    rw [hg_def]
    dsimp only
    split
    · exact hb n
    · simp
  -- the monoid-hom packaging
  set F : ℕ →*₀ ℂ :=
    { toFun := fun n => g n * (if n = 0 then 0 else (n:ℂ)^(-s))
      map_zero' := by simp
      map_one' := by simp [hg1]
      map_mul' := by
        intro a b
        rcases eq_or_ne a 0 with ha | ha
        · simp [ha, hg_def]
        rcases eq_or_ne b 0 with hb0 | hb0
        · simp [hb0, hg_def]
        have hab : a * b ≠ 0 := mul_ne_zero ha hb0
        simp only [if_neg ha, if_neg hb0, if_neg hab]
        have hcast : ((a * b : ℕ) : ℂ) ^ (-s)
            = ((a : ℕ) : ℂ) ^ (-s) * ((b : ℕ) : ℂ) ^ (-s) := by
          have h1' : ((a * b : ℕ) : ℂ)
              = (((a : ℕ) : ℝ) : ℂ) * (((b : ℕ) : ℝ) : ℂ) := by
            push_cast
            ring
          have h2' : ((a : ℕ) : ℂ) = (((a : ℕ) : ℝ) : ℂ) := by
            push_cast
            ring
          have h3' : ((b : ℕ) : ℂ) = (((b : ℕ) : ℝ) : ℂ) := by
            push_cast
            ring
          rw [h1', h2', h3',
            mul_cpow_ofReal_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
        rw [hcast, hgcm a b ha hb0]
        ring }
    with hF_def
  -- norm-summability at Re s = 1: the smooth harmonic mass converges
  have hFapply : ∀ n : ℕ, F n = g n * (if n = 0 then 0 else (n:ℂ)^(-s)) :=
    fun n => rfl
  set h : ℕ → ℝ := fun n =>
    if n ∈ Nat.smoothNumbers y then 1/(n:ℝ) else 0 with hh_def
  have hh_nonneg : ∀ n, 0 ≤ h n := by
    intro n
    rw [hh_def]
    dsimp only
    split
    · positivity
    · exact le_refl 0
  have hh_sum : Summable h := by
    refine summable_of_sum_le
      (c := ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(-(1:ℝ)))⁻¹)
      hh_nonneg fun u => ?_
    have h1 : ∑ n ∈ u, h n
        ≤ ∑ n ∈ Nat.smoothNumbersUpTo (u.sup id + 1) y, (1:ℝ)/n := by
      rw [hh_def]
      rw [← Finset.sum_filter]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_
        (fun n _ _ => by positivity)
      intro n hn
      rw [Finset.mem_filter] at hn
      rw [Nat.mem_smoothNumbersUpTo]
      refine ⟨?_, hn.2⟩
      have h2 := Finset.le_sup (f := id) hn.1
      simp only [id_eq] at h2
      omega
    have h2 : ∑ n ∈ Nat.smoothNumbersUpTo (u.sup id + 1) y, (1:ℝ)/n
        ≤ ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(-(1:ℝ)))⁻¹ := by
      have hr := sum_rpow_smoothNumbersUpTo_le 1 (by norm_num) y
        (u.sup id + 1)
      refine le_trans (le_of_eq ?_) hr
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Real.rpow_neg_one, one_div]
    exact le_trans h1 h2
  have hFle : ∀ n, ‖F n‖ ≤ h n := by
    intro n
    rcases eq_or_ne n 0 with hn | hn
    · rw [hFapply, hn]
      simpa using hh_nonneg 0
    · rw [hFapply, if_neg hn, norm_mul]
      have hn0 : 0 < n := Nat.pos_of_ne_zero hn
      have hnorm : ‖((n:ℕ):ℂ)^(-s)‖ = 1/(n:ℝ) := by
        rw [Complex.norm_natCast_cpow_of_pos hn0]
        rw [show (-s).re = -1 from by rw [Complex.neg_re, hs]]
        rw [Real.rpow_neg_one, one_div]
      rw [hnorm, hh_def]
      dsimp only
      rw [hg_def]
      dsimp only
      by_cases hsm : n ∈ Nat.smoothNumbers y
      · rw [if_pos hsm, if_pos hsm]
        calc ‖f n‖ * (1/(n:ℝ)) ≤ 1 * (1/(n:ℝ)) :=
            mul_le_mul_of_nonneg_right (hb n)
              (one_div_nonneg.mpr (Nat.cast_nonneg n))
          _ = 1/(n:ℝ) := one_mul _
      · rw [if_neg hsm, if_neg hsm, norm_zero, zero_mul]
  have hsum : Summable (fun n => ‖F n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hFle hh_sum
  have hEuler := EulerProduct.eulerProduct_completely_multiplicative
    (f := F) hsum
  have hzero_beyond : ∀ p : ℕ, p.Prime → y ≤ p → F p = 0 := by
    intro p hp hyp
    rw [hFapply, hg_def]
    dsimp only
    rw [if_neg (by
      intro hmem
      have := Nat.mem_smoothNumbers'.mp hmem p hp dvd_rfl
      omega), zero_mul]
  have hconst : ∀ n, y ≤ n → ∏ p ∈ Nat.primesBelow n, (1 - F p)⁻¹
      = ∏ p ∈ y.primesBelow, (1 - F p)⁻¹ := by
    intro n hn
    refine (Finset.prod_subset ?_ ?_).symm
    · intro p hp
      rw [Nat.mem_primesBelow] at hp ⊢
      exact ⟨by omega, hp.2⟩
    · intro p hp hnot
      rw [Nat.mem_primesBelow] at hp
      have hyp : y ≤ p := by
        by_contra hlt
        push_neg at hlt
        exact hnot (Nat.mem_primesBelow.mpr ⟨hlt, hp.2⟩)
      rw [hzero_beyond p hp.2 hyp, sub_zero, inv_one]
  have hconstT : Filter.Tendsto
      (fun n : ℕ => ∏ p ∈ Nat.primesBelow n, (1 - F p)⁻¹)
      Filter.atTop (nhds (∏ p ∈ y.primesBelow, (1 - F p)⁻¹)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop y] with n hn
    exact (hconst n hn).symm
  have hkey := tendsto_nhds_unique hEuler hconstT
  calc ∑' n : ℕ, (if n ∈ Nat.smoothNumbers y then f n else 0)
        * (if n = 0 then 0 else (n:ℂ)^(-s))
      = ∑' n, F n := by
        refine tsum_congr fun n => ?_
        rw [hFapply, hg_def]
    _ = ∏ p ∈ y.primesBelow, (1 - F p)⁻¹ := hkey
    _ = ∏ p ∈ y.primesBelow, (1 - (f p) * (p:ℂ)^(-s))⁻¹ := by
        refine Finset.prod_congr rfl fun p hp => ?_
        have hpp := Nat.prime_of_mem_primesBelow hp
        have hpy := (Nat.mem_primesBelow.mp hp).1
        rw [hFapply, if_neg hpp.ne_zero, hg_def]
        dsimp only
        rw [if_pos (prime_mem_smoothNumbers hpp hpy)]


set_option maxHeartbeats 1600000 in
/-- **The 1-line smooth Euler bound** (Track R, M2-i4a2): the finite
Euler product of a `1`-bounded function over the primes below `y`,
evaluated on the 1-line at frequency `ξ`, is exponentially controlled
by the prime mass minus the pretentious distance to the `ξ`-twist —
the `L^∞` input of the cheap-Halász band term, with no abscissa
shift. -/
theorem norm_smooth_finprod_le (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1)
    (y : ℕ) (ξ : ℝ) :
    ‖∏ p ∈ y.primesBelow, (1 - (f p) * (p:ℂ)^(-(1 + Complex.I*(ξ:ℂ))))⁻¹‖
      ≤ Real.exp ((∑ p ∈ y.primesBelow, (1:ℝ)/p)
          - pretentiousDistSq f (fun n => (n:ℂ)^(Complex.I*(ξ:ℂ))) y + 1) := by
  classical
  set s : ℂ := 1 + Complex.I*(ξ:ℂ) with hs_def
  set w : ℕ → ℂ := fun p => f p * (p:ℂ)^(-s) with hw_def
  have hsre : s.re = 1 := by
    rw [hs_def]
    simp
  -- per-prime norm facts
  have hnw : ∀ p ∈ y.primesBelow, ‖w p‖ ≤ 1/(p:ℝ) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primesBelow hp
    have hp0 : 0 < p := hpp.pos
    rw [hw_def]
    dsimp only
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp0]
    have hre : (-s).re = -1 := by
      rw [Complex.neg_re, hsre]
    rw [hre, Real.rpow_neg_one]
    rw [one_div]
    have h1 : ‖f p‖ * ((p:ℝ))⁻¹ ≤ 1 * ((p:ℝ))⁻¹ := by
      refine mul_le_mul_of_nonneg_right (hb p) ?_
      positivity
    linarith [h1]
  have hhalf : ∀ p ∈ y.primesBelow, ‖w p‖ ≤ 1/2 := by
    intro p hp
    have hp2 := (Nat.prime_of_mem_primesBelow hp).two_le
    refine le_trans (hnw p hp) ?_
    rw [div_le_div_iff₀ (by exact_mod_cast (by omega : 0 < p)) (by norm_num)]
    have : (2:ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  have hlt1 : ∀ p ∈ y.primesBelow, ‖w p‖ < 1 := by
    intro p hp
    have := hhalf p hp
    linarith
  -- per-factor exponential bound
  have hfac : ∀ p ∈ y.primesBelow,
      ‖(1 - w p)⁻¹‖ ≤ Real.exp ((w p).re + ‖w p‖^2) := by
    intro p hp
    have hne : (1 : ℂ) - w p ≠ 0 := by
      intro h
      have h1 : ‖(1:ℂ)‖ = ‖w p‖ := by
        rw [show (1:ℂ) = w p from by linear_combination h]
      rw [norm_one] at h1
      have := hlt1 p hp
      linarith
    have hpos : 0 < ‖(1 - w p)⁻¹‖ := by
      rw [norm_inv]
      have : 0 < ‖(1:ℂ) - w p‖ := norm_pos_iff.mpr hne
      positivity
    rw [← Real.exp_log hpos, Real.exp_le_exp]
    have hlogre : Real.log ‖(1 - w p)⁻¹‖
        = (Complex.log ((1 - w p)⁻¹)).re := by
      rw [Complex.log_re]
    rw [hlogre]
    have hbound := Complex.norm_log_one_sub_inv_sub_self_le (hlt1 p hp)
    have hre_diff : (Complex.log ((1 - w p)⁻¹)).re - (w p).re
        ≤ ‖Complex.log ((1 - w p)⁻¹) - w p‖ := by
      calc (Complex.log ((1 - w p)⁻¹)).re - (w p).re
          = (Complex.log ((1 - w p)⁻¹) - w p).re := by
            rw [Complex.sub_re]
        _ ≤ ‖Complex.log ((1 - w p)⁻¹) - w p‖ := Complex.re_le_norm _
    have hinv2 : (1 - ‖w p‖)⁻¹ ≤ 2 := by
      have := hhalf p hp
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have hsq : ‖w p‖^2 * (1 - ‖w p‖)⁻¹ / 2 ≤ ‖w p‖^2 := by
      have h0 : (0:ℝ) ≤ ‖w p‖^2 := sq_nonneg _
      nlinarith
    linarith [hbound, hre_diff, hsq]
  -- assemble the product
  calc ‖∏ p ∈ y.primesBelow, (1 - w p)⁻¹‖
      = ∏ p ∈ y.primesBelow, ‖(1 - w p)⁻¹‖ := norm_prod _ _
    _ ≤ ∏ p ∈ y.primesBelow, Real.exp ((w p).re + ‖w p‖^2) := by
        refine Finset.prod_le_prod (fun p _ => norm_nonneg _) hfac
    _ = Real.exp (∑ p ∈ y.primesBelow, ((w p).re + ‖w p‖^2)) := by
        rw [Real.exp_sum]
    _ ≤ Real.exp ((∑ p ∈ y.primesBelow, (1:ℝ)/p)
          - pretentiousDistSq f (fun n => (n:ℂ)^(Complex.I*(ξ:ℂ))) y + 1) := by
        rw [Real.exp_le_exp]
        have hsum_re : ∑ p ∈ y.primesBelow, (w p).re
            = (∑ p ∈ y.primesBelow, (1:ℝ)/p)
              - pretentiousDistSq f (fun n => (n:ℂ)^(Complex.I*(ξ:ℂ))) y := by
          unfold pretentiousDistSq
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun p hp => ?_
          have hpp := Nat.prime_of_mem_primesBelow hp
          have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
          have hsplit : w p = (f p * (p:ℂ)^(-(Complex.I*(ξ:ℂ)))) / (p:ℂ) := by
            rw [hw_def]
            dsimp only
            rw [hs_def]
            rw [show -(1 + Complex.I*(ξ:ℂ))
                = (-(Complex.I*(ξ:ℂ))) + (-1) from by ring]
            rw [Complex.cpow_add _ _ (by
              exact_mod_cast hpp.ne_zero : ((p:ℕ):ℂ) ≠ 0)]
            rw [Complex.cpow_neg_one]
            field_simp
          rw [hsplit]
          have hdiv_re : ((f p * (p:ℂ)^(-(Complex.I*(ξ:ℂ)))) / (p:ℂ)).re
              = (f p * (p:ℂ)^(-(Complex.I*(ξ:ℂ)))).re / (p:ℝ) := by
            have h1 : (f p * (p:ℂ)^(-(Complex.I*(ξ:ℂ)))) / (p:ℂ)
                = (f p * (p:ℂ)^(-(Complex.I*(ξ:ℂ))))
                  * (((1/(p:ℝ)):ℝ):ℂ) := by
              push_cast
              field_simp
            rw [h1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
              mul_zero, sub_zero, mul_one_div]
          rw [hdiv_re]
          have hconjp : (starRingEnd ℂ) (((p:ℕ):ℂ)^(Complex.I*(ξ:ℂ)))
              = ((p:ℕ):ℂ)^(-(Complex.I*(ξ:ℂ))) := by
            have hplus : ((p:ℕ):ℂ) ^ (Complex.I * (ξ:ℂ))
                = Complex.exp (((ξ * Real.log p : ℝ) : ℂ) * Complex.I) := by
              rw [Complex.cpow_def_of_ne_zero
                (by exact_mod_cast hpp.ne_zero)]
              congr 1
              push_cast
              ring
            have hminus : ((p:ℕ):ℂ) ^ (-(Complex.I * (ξ:ℂ)))
                = Complex.exp (-(((ξ * Real.log p : ℝ) : ℂ) * Complex.I)) := by
              rw [Complex.cpow_def_of_ne_zero
                (by exact_mod_cast hpp.ne_zero)]
              congr 1
              push_cast
              ring
            rw [hplus, hminus, ← Complex.exp_conj, map_mul,
              Complex.conj_ofReal, Complex.conj_I]
            ring_nf
          dsimp only
          rw [hconjp]
          ring
        have hsum_sq : ∑ p ∈ y.primesBelow, ‖w p‖^2 ≤ 1 := by
          have h1 : ∑ p ∈ y.primesBelow, ‖w p‖^2
              ≤ ∑ p ∈ y.primesBelow, (1/(p:ℝ))^2 := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hle := hnw p hp
            have h0 : (0:ℝ) ≤ ‖w p‖ := norm_nonneg _
            nlinarith
          have h2 : ∑ p ∈ y.primesBelow, (1/(p:ℝ))^2
              ≤ ∑ p ∈ y.primesBelow, 1/((p:ℝ)*((p:ℝ)-1)) := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hp2 : (2:ℝ) ≤ p := by
              exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
            rw [div_pow, one_pow]
            rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
            nlinarith
          linarith [h1, h2, sum_one_div_mul_pred_primesBelow_le y]
        rw [Finset.sum_add_distrib, hsum_re]
        linarith [hsum_sq]


set_option maxHeartbeats 1600000 in
/-- **The smooth series tail** (Track R, M2-i4a3): truncating the
smooth Dirichlet series on the 1-line at the box `X` costs at most
`X^{−δ}·∏_{p<y}(1−p^{δ−1})⁻¹` for any `δ ∈ (0,1)` — the Rankin
device applied to the tail. -/
theorem norm_smooth_tsum_sub_sum_le (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1)
    (y X : ℕ) (hX : 1 ≤ X) (s : ℂ) (hs : s.re = 1)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ‖(∑' n : ℕ, (if n ∈ Nat.smoothNumbers y then f n else 0)
          * (if n = 0 then 0 else (n:ℂ)^(-s)))
        - ∑ n ∈ Nat.smoothNumbersUpTo X y,
            (if n ∈ Nat.smoothNumbers y then f n else 0)
              * (if n = 0 then 0 else (n:ℂ)^(-s))‖
      ≤ (X:ℝ)^(-δ) * ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹ := by
  classical
  set F : ℕ → ℂ := fun n => (if n ∈ Nat.smoothNumbers y then f n else 0)
    * (if n = 0 then 0 else (n:ℂ)^(-s)) with hF_def
  -- the norm majorant and its summability
  set h : ℕ → ℝ := fun n =>
    if n ∈ Nat.smoothNumbers y then 1/(n:ℝ) else 0 with hh_def
  have hFle : ∀ n, ‖F n‖ ≤ h n := by
    intro n
    rw [hF_def, hh_def]
    dsimp only
    rcases eq_or_ne n 0 with hn | hn
    · subst hn
      have h0 : (0:ℕ) ∉ Nat.smoothNumbers y := by
        intro hmem
        exact (Nat.ne_zero_of_mem_smoothNumbers hmem) rfl
      rw [if_neg h0]
      simp
    · rw [if_neg hn, norm_mul]
      have hn0 : 0 < n := Nat.pos_of_ne_zero hn
      have hnorm : ‖((n:ℕ):ℂ)^(-s)‖ = 1/(n:ℝ) := by
        rw [Complex.norm_natCast_cpow_of_pos hn0,
          show (-s).re = -1 from by rw [Complex.neg_re, hs],
          Real.rpow_neg_one, one_div]
      rw [hnorm]
      by_cases hsm : n ∈ Nat.smoothNumbers y
      · rw [if_pos hsm, if_pos hsm]
        have := hb n
        have h1 : (0:ℝ) ≤ 1/(n:ℝ) := by positivity
        nlinarith [norm_nonneg (f n)]
      · rw [if_neg hsm, if_neg hsm, norm_zero, zero_mul]
  have hh_nonneg : ∀ n, 0 ≤ h n := by
    intro n
    rw [hh_def]
    dsimp only
    split
    · positivity
    · exact le_refl 0
  have hh_sum : Summable h := by
    refine summable_of_sum_le
      (c := ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(-(1:ℝ)))⁻¹)
      hh_nonneg fun u => ?_
    have h1 : ∑ n ∈ u, h n
        ≤ ∑ n ∈ Nat.smoothNumbersUpTo (u.sup id + 1) y, (1:ℝ)/n := by
      rw [hh_def]
      rw [← Finset.sum_filter]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_
        (fun n _ _ => by positivity)
      intro n hn
      rw [Finset.mem_filter] at hn
      rw [Nat.mem_smoothNumbersUpTo]
      refine ⟨?_, hn.2⟩
      have h2 := Finset.le_sup (f := id) hn.1
      simp only [id_eq] at h2
      omega
    have h2 : ∑ n ∈ Nat.smoothNumbersUpTo (u.sup id + 1) y, (1:ℝ)/n
        ≤ ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(-(1:ℝ)))⁻¹ := by
      have hr := sum_rpow_smoothNumbersUpTo_le 1 (by norm_num) y
        (u.sup id + 1)
      refine le_trans (le_of_eq ?_) hr
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Real.rpow_neg_one, one_div]
    exact le_trans h1 h2
  have hFsum : Summable F :=
    Summable.of_norm (Summable.of_nonneg_of_le
      (fun n => norm_nonneg _) hFle hh_sum)
  -- the split
  have hsplit := hFsum.sum_add_tsum_compl
    (s := Nat.smoothNumbersUpTo X y)
  have hdiff : (∑' n : ℕ, F n) - ∑ n ∈ Nat.smoothNumbersUpTo X y, F n
      = ∑' n : ↥((↑(Nat.smoothNumbersUpTo X y) : Set ℕ)ᶜ), F n := by
    linear_combination (hsplit).symm
  rw [hdiff]
  -- bound the complement sum by the Rankin tail
  have hcompl_sum : Summable fun n : ↥((↑(Nat.smoothNumbersUpTo X y) : Set ℕ)ᶜ)
      => ‖F n.1‖ := by
    exact (Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      hFle hh_sum).subtype _
  refine le_trans (norm_tsum_le_tsum_norm hcompl_sum) ?_
  -- pointwise tail majorant on the complement
  set h' : ℕ → ℝ := fun n =>
    if n ∈ Nat.smoothNumbers y then (X:ℝ)^(-δ) * (n:ℝ)^(δ-1) else 0
    with hh'_def
  have hle' : ∀ n : ↥((↑(Nat.smoothNumbersUpTo X y) : Set ℕ)ᶜ),
      ‖F n.1‖ ≤ h' n.1 := by
    rintro ⟨n, hn⟩
    dsimp only
    rw [Set.mem_compl_iff, Finset.mem_coe,
      Nat.mem_smoothNumbersUpTo] at hn
    push_neg at hn
    by_cases hsm : n ∈ Nat.smoothNumbers y
    · have hnX : X < n := by
        by_contra hle
        push_neg at hle
        exact (hn hle) hsm
      have hn1 : 1 ≤ n := by
        have := Nat.ne_zero_of_mem_smoothNumbers hsm
        omega
      refine le_trans (hFle n) ?_
      rw [hh_def, hh'_def]
      dsimp only
      rw [if_pos hsm, if_pos hsm]
      have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn1
      have hXr : (X:ℝ) ≤ n := by
        exact_mod_cast (by omega : X ≤ n)
      have hX0 : (0:ℝ) < X := by exact_mod_cast hX
      -- 1/n = n^{δ−1}·n^{−δ} ≤ n^{δ−1}·X^{−δ}
      have h1 : (1:ℝ)/(n:ℝ) = (n:ℝ)^(δ-1) * (n:ℝ)^(-δ) := by
        rw [← Real.rpow_add (by linarith)]
        rw [show δ-1 + -δ = -1 from by ring, Real.rpow_neg_one, one_div]
      rw [h1]
      have h2 : (n:ℝ)^(-δ) ≤ (X:ℝ)^(-δ) := by
        exact Real.rpow_le_rpow_of_nonpos hX0 hXr (by linarith)
      calc (n:ℝ)^(δ-1) * (n:ℝ)^(-δ)
          ≤ (n:ℝ)^(δ-1) * (X:ℝ)^(-δ) := by
            refine mul_le_mul_of_nonneg_left h2 ?_
            positivity
        _ = (X:ℝ)^(-δ) * (n:ℝ)^(δ-1) := by ring
    · rw [hh'_def]
      dsimp only
      rw [if_neg hsm]
      have : F n = 0 := by
        rw [hF_def]
        dsimp only
        rw [if_neg hsm, zero_mul]
      rw [this, norm_zero]
  -- the base Rankin-summable and the partial-sum bound
  have hbase_nonneg : ∀ n, 0 ≤ (if n ∈ Nat.smoothNumbers y
      then (n:ℝ)^(δ-1) else 0) := by
    intro n
    split
    · positivity
    · exact le_refl 0
  have hbase_partial : ∀ u : Finset ℕ,
      ∑ n ∈ u, (if n ∈ Nat.smoothNumbers y then (n:ℝ)^(δ-1) else 0)
        ≤ ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹ := by
    intro u
    have h1 : ∑ n ∈ u, (if n ∈ Nat.smoothNumbers y then (n:ℝ)^(δ-1) else 0)
        ≤ ∑ n ∈ Nat.smoothNumbersUpTo (u.sup id + 1) y, (n:ℝ)^(-(1-δ)) := by
      rw [← Finset.sum_filter]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_
        (fun n _ _ => by positivity))
        (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
      · intro n hn
        rw [Finset.mem_filter] at hn
        rw [Nat.mem_smoothNumbersUpTo]
        refine ⟨?_, hn.2⟩
        have h2 := Finset.le_sup (f := id) hn.1
        simp only [id_eq] at h2
        omega
      · congr 1
        ring
    have h2 := sum_rpow_smoothNumbersUpTo_le (1-δ) (by linarith) y
      (u.sup id + 1)
    have h3 : ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(-(1-δ)))⁻¹
        = ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹ := by
      refine Finset.prod_congr rfl fun p _ => ?_
      congr 2
      ring
    rw [h3] at h2
    exact le_trans h1 h2
  have hbase_sum : Summable (fun n =>
      if n ∈ Nat.smoothNumbers y then (n:ℝ)^(δ-1) else 0) :=
    summable_of_sum_le hbase_nonneg hbase_partial
  have hh'_sum : Summable h' := by
    refine Summable.congr (hbase_sum.mul_left ((X:ℝ)^(-δ))) fun n => ?_
    rw [hh'_def]
    dsimp only
    split
    · rfl
    · rw [mul_zero]
  -- complement tsum chain
  have hsub_le : (∑' n : ↥((↑(Nat.smoothNumbersUpTo X y) : Set ℕ)ᶜ), ‖F n.1‖)
      ≤ ∑' n : ↥((↑(Nat.smoothNumbersUpTo X y) : Set ℕ)ᶜ), h' n.1 :=
    Summable.tsum_le_tsum hle' hcompl_sum (hh'_sum.subtype _)
  have hh'_nonneg : ∀ n, 0 ≤ h' n := by
    intro n
    rw [hh'_def]
    dsimp only
    split
    · positivity
    · exact le_refl 0
  have hsub_full : (∑' n : ↥((↑(Nat.smoothNumbersUpTo X y) : Set ℕ)ᶜ), h' n.1)
      ≤ ∑' n : ℕ, h' n := by
    rw [show (∑' n : ↥((↑(Nat.smoothNumbersUpTo X y) : Set ℕ)ᶜ), h' n.1)
        = ∑' n : ℕ, Set.indicator
            {n : ℕ | n ∉ Nat.smoothNumbersUpTo X y} h' n from
      tsum_subtype _ _]
    refine Summable.tsum_le_tsum (fun n => ?_) (hh'_sum.indicator _) hh'_sum
    by_cases hn : n ∈ {n : ℕ | n ∉ Nat.smoothNumbersUpTo X y}
    · rw [Set.indicator_of_mem hn]
    · rw [Set.indicator_of_notMem hn]
      exact hh'_nonneg n
  have hfull : (∑' n : ℕ, h' n)
      ≤ (X:ℝ)^(-δ) * ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹ := by
    refine Real.tsum_le_of_sum_le (fun n => ?_) fun u => ?_
    · rw [hh'_def]
      dsimp only
      split
      · positivity
      · exact le_refl 0
    · rw [hh'_def]
      calc ∑ n ∈ u, (if n ∈ Nat.smoothNumbers y
            then (X:ℝ)^(-δ) * (n:ℝ)^(δ-1) else 0)
          = (X:ℝ)^(-δ) * ∑ n ∈ u, (if n ∈ Nat.smoothNumbers y
              then (n:ℝ)^(δ-1) else 0) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun n _ => ?_
            split
            · rfl
            · rw [mul_zero]
        _ ≤ (X:ℝ)^(-δ) * ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹ := by
            refine mul_le_mul_of_nonneg_left (hbase_partial u) ?_
            positivity
  linarith [hsub_le, hsub_full, hfull]


end MoltResearch
