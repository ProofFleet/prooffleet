import MoltResearch.Discrepancy.SmoothRankin

/-!
# The §3 capstone at the Riesz window (Track R)

The assembly leaf: the per-block instantiation of `tripleConvR_le` and
the `k`-sum balance live here, downstream of the whole `SmoothRankin`
substrate, so that capstone units never force a rebuild of the 9.8k-line
core file (see AGENTS.md, "CI-efficiency rule").

This file opens with the missing glue between §4's suppliers and
`tripleConvR_le`'s interface: the energy bound
`ghsPrimePoly_unit_energy_final_le` carries GHS's own threshold
`T² ≤ q`, but the `Q` that `tripleConvR_le` enlarges into contains
*every* prime below `x/p` — including the small ones.  The state-file
resolution ("small primes contribute `O(1)`, discard separately") is
formalised as `ghsPrimePoly_unit_energy_split_le`: split the polynomial
at `T²`, price the small half by its trivial sup
(`norm_ghsPrimePoly_le`, a Mertens mass `≍ 2·log T`), and pay a factor
`2` on both halves.
-/

namespace MoltResearch

open MeasureTheory Real Complex Finset in
/-- **The unit-interval energy, with the small primes priced in**
(Track R, N179): for `Q` any set of primes `≤ X` — *no* lower
threshold — and any frequency `N`,

  `∫_{N−1/2}^{N+1/2} ‖P₃(t)‖² dt`
  `  ≤ 2·e^π·(12290·(log(X+1) + 2) + 4T·(6144 + e^{−πT²/64}·B))`
  `    + 2·(∑_{q ∈ Q, q < T²} log q/q)²`.

`ghsPrimePoly_unit_energy_final_le` demands `T² ≤ q` throughout — GHS's
own Lemma-1 hypothesis, which their `Q` satisfies by fiat and ours does
not: `tripleConvR_le` enlarges the moving inner range into a `Q` that
contains every prime below `x/p`.  So split at the threshold.  The
large half is the final energy bound; the small half is a polynomial
with Mertens mass `∑_{q<T²} log q/q ≍ 2·log T` — at the forced
`T ≍ √(log x)` this is `≍ log log x`, entering squared, against the
`≍ e^{−k}·log x` of the main term.  The two halves cost a factor `2`
each by `‖a+b‖² ≤ 2‖a‖² + 2‖b‖²`.

This is the `hV` supplier for the per-block instantiation: it has the
same shape as the final bound, with no hypothesis on `Q` below `X`. -/
theorem ghsPrimePoly_unit_energy_split_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (Q : Finset ℕ) (X : ℕ) (hX : 2 ≤ X) (T : ℝ) (hT : 5 ≤ T)
    (hQp : ∀ q ∈ Q, q.Prime) (hQX : ∀ q ∈ Q, q ≤ X)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∑ q ∈ Q, Real.log (q:ℝ) ≤ B)
    (hwide : ∀ w : ℕ → ℂ, IntervalIntegrable
      (fun u => ‖∑ q ∈ Q.filter (fun q : ℕ => T^2 ≤ (q:ℝ)), w q
        * ((Real.fourierChar (-(Real.log (q:ℝ) * u)) : Circle) : ℂ)‖^2)
      volume (-T) T)
    (N : ℝ) :
    (∫ t in (N - 1/2)..(N + 1/2), ‖ghsPrimePoly f Q t‖^2)
      ≤ 2 * (Real.exp π * (12290 * (Real.log ((X+1 : ℕ):ℝ) + 2)
            + 4*T * (6144 + Real.exp (-(π*T^2/64)) * B)))
        + 2 * (∑ q ∈ Q.filter (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
            Real.log (q:ℝ)/(q:ℝ))^2 := by
  classical
  set Ql : Finset ℕ := Q.filter (fun q : ℕ => T^2 ≤ (q:ℝ)) with hQl_def
  set Qs : Finset ℕ := Q.filter (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)) with hQs_def
  have hab : N - 1/2 ≤ N + 1/2 := by linarith
  -- the polynomial splits at the threshold
  have hsplit : ∀ t : ℝ, ghsPrimePoly f Q t
      = ghsPrimePoly f Ql t + ghsPrimePoly f Qs t := by
    intro t
    rw [hQl_def, hQs_def]
    simp only [ghsPrimePoly]
    exact (Finset.sum_filter_add_sum_filter_not Q _ _).symm
  -- pointwise, the square splits at cost 2
  have hpt : ∀ t ∈ Set.Icc (N - 1/2) (N + 1/2), ‖ghsPrimePoly f Q t‖^2
      ≤ 2*‖ghsPrimePoly f Ql t‖^2 + 2*‖ghsPrimePoly f Qs t‖^2 := by
    intro t _
    rw [hsplit t]
    have h1 := norm_add_le (ghsPrimePoly f Ql t) (ghsPrimePoly f Qs t)
    have h0 := norm_nonneg (ghsPrimePoly f Ql t + ghsPrimePoly f Qs t)
    nlinarith [sq_nonneg (‖ghsPrimePoly f Ql t‖ - ‖ghsPrimePoly f Qs t‖),
      norm_nonneg (ghsPrimePoly f Ql t), norm_nonneg (ghsPrimePoly f Qs t)]
  -- integrability, all from continuity
  have hiQ : IntervalIntegrable (fun t => ‖ghsPrimePoly f Q t‖^2)
      volume (N - 1/2) (N + 1/2) :=
    ((continuous_ghsPrimePoly f Q).norm.pow 2).intervalIntegrable _ _
  have hiQl : IntervalIntegrable (fun t => ‖ghsPrimePoly f Ql t‖^2)
      volume (N - 1/2) (N + 1/2) :=
    ((continuous_ghsPrimePoly f Ql).norm.pow 2).intervalIntegrable _ _
  have hiQs : IntervalIntegrable (fun t => ‖ghsPrimePoly f Qs t‖^2)
      volume (N - 1/2) (N + 1/2) :=
    ((continuous_ghsPrimePoly f Qs).norm.pow 2).intervalIntegrable _ _
  have hisum : IntervalIntegrable
      (fun t => 2*‖ghsPrimePoly f Ql t‖^2 + 2*‖ghsPrimePoly f Qs t‖^2)
      volume (N - 1/2) (N + 1/2) :=
    ((hiQl.const_mul 2).add (hiQs.const_mul 2))
  -- the integral comparison
  have hmono := intervalIntegral.integral_mono_on hab hiQ hisum hpt
  rw [intervalIntegral.integral_add (hiQl.const_mul 2) (hiQs.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    at hmono
  -- the large half: the final energy bound, hypotheses restricted
  have hQlp : ∀ q ∈ Ql, q.Prime := by
    intro q hq
    rw [hQl_def] at hq
    exact hQp q (Finset.mem_filter.mp hq).1
  have hQlX : ∀ q ∈ Ql, q ≤ X := by
    intro q hq
    rw [hQl_def] at hq
    exact hQX q (Finset.mem_filter.mp hq).1
  have hQlT : ∀ q ∈ Ql, T^2 ≤ (q:ℝ) := by
    intro q hq
    rw [hQl_def] at hq
    exact (Finset.mem_filter.mp hq).2
  have hBl : ∑ q ∈ Ql, Real.log (q:ℝ) ≤ B := by
    refine le_trans ?_ hB
    rw [hQl_def]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun q _ _ => Real.log_natCast_nonneg q)
  have hlarge := ghsPrimePoly_unit_energy_final_le f hf Ql X hX T hT
    hQlp hQlX hQlT B hB0 hBl hwide N
  -- the small half: the trivial sup, squared, over a unit interval
  have hsmall : (∫ t in (N - 1/2)..(N + 1/2), ‖ghsPrimePoly f Qs t‖^2)
      ≤ (∑ q ∈ Qs, Real.log (q:ℝ)/(q:ℝ))^2 := by
    set Ms : ℝ := ∑ q ∈ Qs, Real.log (q:ℝ)/(q:ℝ) with hMs_def
    have hpts : ∀ t ∈ Set.Icc (N - 1/2) (N + 1/2),
        ‖ghsPrimePoly f Qs t‖^2 ≤ Ms^2 := by
      intro t _
      have h := norm_ghsPrimePoly_le f hf Qs t
      nlinarith [norm_nonneg (ghsPrimePoly f Qs t)]
    have hconst : IntervalIntegrable (fun _ : ℝ => Ms^2)
        volume (N - 1/2) (N + 1/2) := intervalIntegrable_const
    have h := intervalIntegral.integral_mono_on hab hiQs hconst hpts
    rw [intervalIntegral.integral_const] at h
    have hone : (N + 1/2) - (N - 1/2) = 1 := by ring
    rw [hone, one_smul] at h
    exact h
  linarith [hmono, hlarge, hsmall]


open Finset in
/-- **The smooth restriction moves into the index set** (Track R,
N180): for the main polynomial, killing `f` off the `y`-smooth numbers
is the same as filtering the summation range,

  `ghsMainPoly (f·1_{y-smooth}) S = ghsMainPoly f (S ∩ smooth)`.

The bridge between `tripleConvR_le` and the Halász Euler-product bound:
the former hardwires the index set `Icc 1 x` and varies `f`, the latter
(`norm_ghsMainPoly_smooth_band_le`) hardwires `f` and filters the set.
With this identity the smooth-restricted `g` — still completely
multiplicative by `completelyMultiplicativeC_smooth_restrict`, so the
whole §3 chain runs on it unchanged — hands `hBu` straight to the band
bound. -/
theorem ghsMainPoly_smooth_restrict_eq (f : ℕ → ℂ) (y : ℕ) (S : Finset ℕ) :
    ghsMainPoly (fun n => if n ∈ Nat.smoothNumbers y then f n else 0) S
      = ghsMainPoly f (S.filter (· ∈ Nat.smoothNumbers y)) := by
  classical
  funext ξ
  simp only [ghsMainPoly]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : n ∈ Nat.smoothNumbers y
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, zero_div, zero_mul]

open Finset in
/-- **The real smooth restriction complexifies pointwise** (Track R,
N180): the `ℝ → ℂ` coercion `tripleConvR_le` applies to its `f`
commutes with the smooth cut, so `hBu` for the real restricted `g`
is `hBu` for the complex restricted `(f:ℂ)`.

`Complex.ofReal` through `ite`, recorded once so the instantiation
never has to push coercions by hand. -/
theorem smooth_restrict_ofReal (f : ℕ → ℝ) (y : ℕ) :
    (fun n : ℕ => (((if n ∈ Nat.smoothNumbers y then f n else 0 : ℝ)) : ℂ))
      = fun n : ℕ => if n ∈ Nat.smoothNumbers y then ((f n : ℝ) : ℂ) else 0 := by
  classical
  funext n
  by_cases h : n ∈ Nat.smoothNumbers y
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, Complex.ofReal_zero]


open MeasureTheory Real Complex Finset in
/-- **The unit-interval energy at `Q = primesBelow X`, all hypotheses
discharged** (Track R, N181): for any `X ≥ 2`, `T ≥ 5` and frequency
`N`,

  `∫_{N−1/2}^{N+1/2} ‖P₃(t)‖² dt`
  `  ≤ 2·e^π·(12290·(log(X+1) + 2) + 4T·(6144 + e^{−πT²/64}·X·log 4))`
  `    + 2·(∑_{q < X, q < T²} log q/q)²`.

`ghsPrimePoly_unit_energy_split_le` at the concrete inner range the
per-block instantiation feeds `tripleConvR_le`: `Q = (x/blockLo x k).
primesBelow ⊇ (x/p).primesBelow` for every `p` in block `k`.  The three
side inputs close for free at this `Q`: membership gives primality and
`q ≤ X`, Chebyshev's `θ`-bound (`sum_log_primesBelow_le`) gives
`B = X·log 4`, and `hwide` is the continuity of finite character sums
(`ExpSums.continuous_char_poly`).

This is the `hV` that block `k` hands to `tripleConvR_le`, with only
the frequency `N` left quantified — exactly `halaszRange`'s shape. -/
theorem ghsPrimePoly_unit_energy_primesBelow_le (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (X : ℕ) (hX : 2 ≤ X) (T : ℝ) (hT : 5 ≤ T)
    (N : ℝ) :
    (∫ t in (N - 1/2)..(N + 1/2), ‖ghsPrimePoly f X.primesBelow t‖^2)
      ≤ 2 * (Real.exp π * (12290 * (Real.log ((X+1 : ℕ):ℝ) + 2)
            + 4*T * (6144 + Real.exp (-(π*T^2/64)) * ((X:ℝ) * Real.log 4))))
        + 2 * (∑ q ∈ X.primesBelow.filter (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
            Real.log (q:ℝ)/(q:ℝ))^2 := by
  classical
  refine ghsPrimePoly_unit_energy_split_le f hf X.primesBelow X hX T hT
    (fun q hq => (Nat.mem_primesBelow.mp hq).2)
    (fun q hq => le_of_lt (Nat.mem_primesBelow.mp hq).1)
    ((X:ℝ) * Real.log 4)
    (mul_nonneg (Nat.cast_nonneg X) (Real.log_nonneg (by norm_num)))
    (sum_log_primesBelow_le X)
    (fun w => ((ExpSums.continuous_char_poly
      (X.primesBelow.filter (fun q : ℕ => T^2 ≤ (q:ℝ))) w
      (fun q => Real.log (q:ℝ))).norm.pow 2).intervalIntegrable _ _)
    N


open MeasureTheory Real Complex Finset in
open scoped FourierTransform in
/-- **The Riesz block energy on a fitted block, Chebyshev priced**
(Track R, N182): for `P` inside block `k` of a fitted tiling
(`2·blockHi ≤ x`) with `T² ≤ p` throughout,

  `∫ ‖P₂‖²·‖𝓕V‖ ≤ e^π·(12290·(e^{2k}/log²x)·(4((e−1)e^{−k}·log x + log 2) + 4·log 4)`
  `      + T·(6144 + e^{−πT²/64}·x·log 4)·(16/log²x + 4/(√⌊√x⌋·log²2)))`
  `    + (∑_{p∈P} log p/(p·|log(x/p)|))²·(1/(2π²T))`.

`ghsBlock_E1_riesz_le` with its two remaining generic inputs closed on
the block: `2p ≤ x` from `p < blockHi` and the fit, and the Chebyshev
budget `B = x·log 4` from `P ⊆ x.primesBelow` and
`sum_log_primesBelow_le` — the same `θ`-pricing as N181's inner range,
so the two halves of §4 now quote constants from the same source.

`hPT` stays a hypothesis: on retained blocks it is free from
`y ≤ blockLo ≤ p` once the capstone fixes `T ≍ √(log x) ≪ √y`, and
that choice belongs to the balance, not to the block. -/
theorem ghsBlock_E1_riesz_block_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x k : ℕ) (hx : 2 ≤ x) (hk : 1 ≤ k) (P : Finset ℕ)
    (T : ℝ) (hT : 5 ≤ T)
    (hP : ∀ p ∈ P, p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k)
    (hfit : 2 * blockHi x k ≤ x)
    (hPT : ∀ p ∈ P, T^2 ≤ (p:ℝ)) :
    (∫ ξ, ‖ghsBlockPoly f x P ξ‖^2
        * ‖𝓕 (fun v => ((ExpSums.rieszWindow v : ℝ) : ℂ)) ξ‖)
      ≤ Real.exp π *
          (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
              * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
                  + Real.log 2) + 4 * Real.log 4))
            + T * (6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
                * (16/(Real.log (x:ℝ))^2
                    + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
        + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
            * (1/(2*Real.pi^2*T)) := by
  classical
  have h2p : ∀ p ∈ P, 2*p ≤ x := by
    intro p hp
    obtain ⟨-, -, hpB⟩ := hP p hp
    omega
  have hsub : P ⊆ x.primesBelow := by
    intro p hp
    obtain ⟨hpp, -, hpB⟩ := hP p hp
    rw [Nat.mem_primesBelow]
    exact ⟨by omega, hpp⟩
  have hB : ∑ p ∈ P, Real.log (p:ℝ) ≤ (x:ℝ) * Real.log 4 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p _ _ => Real.log_natCast_nonneg p)) ?_
    exact sum_log_primesBelow_le x
  exact ghsBlock_E1_riesz_le f hf x k hx hk P T hT hP hPT h2p
    ((x:ℝ) * Real.log 4)
    (mul_nonneg (Nat.cast_nonneg x) (Real.log_nonneg (by norm_num)))
    hB


open MeasureTheory Real Complex Finset in
open scoped FourierTransform in
/-- **§3's sharp estimate on a retained block, suppliers plugged in**
(Track R, N183): for `P` inside fitted block `k` with `T² ≤ p`
throughout, and `b` any band sup for the main polynomial,

  `|tripleConvR f x P| ≤ x·√(E₁·(5·V₃·6b² + Mtail)) + 2x·log 4`,

with `E₁` the block energy of N182, `V₃` the unit-interval energy of
N181 at the enlarged inner range `X = x/blockLo x k`, and `Mtail` the
Riesz tail mass at the widened band `halaszM x`.

The assembly of the campaign: `tripleConvR_le` with every analytic
input in concrete form except `b` — which stays parametric because the
Halász Euler-product bound (`norm_ghsMainPoly_smooth_band_le` +
N180's transfer) prices it by the pretentious distance, and that
instantiation is the balance step's to make.  The inner range `Q =
X.primesBelow` absorbs every `(x/p).primesBelow` by divisor
monotonicity; `3 ≤ X` puts `q = 2` in `Q`, which is what makes the
tail mass strictly positive, as `tripleConvR_le`'s `hMtail0` demands.

Positivity bookkeeping aside, nothing happens here — which is the
point: after N179–N182 the per-block estimate is an application, not
an argument. -/
theorem tripleConvR_block_sharp_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (x k : ℕ) (hx : 2 ≤ x) (hk : 1 ≤ k) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k)
    (hfit : 2 * blockHi x k ≤ x)
    (hX3 : 3 ≤ x / blockLo x k)
    (T : ℝ) (hT : 5 ≤ T) (hPT : ∀ p ∈ P, T^2 ≤ (p:ℝ))
    (b : ℝ) (hb0 : 0 ≤ b)
    (hBu : ∀ t : ℝ,
      ‖ghsMainPoly (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 x) t‖ ≤ b) :
    |tripleConvR f x P|
      ≤ (x:ℝ) * Real.sqrt
          ((Real.exp π *
              (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
                  * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ))
                        * Real.log (x:ℝ) + Real.log 2) + 4 * Real.log 4))
                + T * (6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
                    * (16/(Real.log (x:ℝ))^2
                        + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
            + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
                * (1/(2*Real.pi^2*T)))
          * (5 * (2 * (Real.exp π * (12290
                * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
                + 4*T * (6144 + Real.exp (-(π*T^2/64))
                    * (((x / blockLo x k : ℕ):ℝ) * Real.log 4))))
              + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
                    (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
                  Real.log (q:ℝ)/(q:ℝ))^2)
              * (6*b^2)
            + (∑ q ∈ (x / blockLo x k).primesBelow,
                  Real.log (q:ℝ)/(q:ℝ))^2
                * (∑ n ∈ Finset.Icc 1 x, (1:ℝ)/(n:ℝ))^2
                * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))))
        + 2*(x:ℝ)*Real.log 4 := by
  classical
  have hx1 : 1 ≤ x := by omega
  obtain ⟨hlo1, hlohi⟩ := blockLo_le_blockHi x k hx1
  have hfc : ∀ n, ‖((f n : ℝ) : ℂ)‖ ≤ 1 := by
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hf n
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have h2p : ∀ p ∈ P, 2*p ≤ x := by
    intro p hp
    obtain ⟨-, -, hpB⟩ := hP p hp
    omega
  have hX2 : 2 ≤ x / blockLo x k := by omega
  -- the enlarged inner range
  have hQp : ∀ q ∈ (x / blockLo x k).primesBelow, q.Prime :=
    fun q hq => (Nat.mem_primesBelow.mp hq).2
  have hQpos : ∀ q ∈ (x / blockLo x k).primesBelow, 0 < q :=
    fun q hq => (hQp q hq).pos
  have hQsub : ∀ p ∈ P, (x/p).primesBelow ⊆ (x / blockLo x k).primesBelow := by
    intro p hp q hq
    obtain ⟨-, hlop, -⟩ := hP p hp
    rw [Nat.mem_primesBelow] at hq ⊢
    exact ⟨lt_of_lt_of_le hq.1 (Nat.div_le_div_left hlop (by omega)), hq.2⟩
  -- positivity of the block energy
  have hlogx : (0:ℝ) < Real.log (x:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 2 ≤ x))
  have he1 : (0:ℝ) < Real.exp 1 - 1 := by
    have := Real.add_one_le_exp (1:ℝ)
    linarith
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hT0 : (0:ℝ) < T := by linarith
  have hsqx : (0:ℝ) < Real.sqrt ((Nat.sqrt x : ℕ):ℝ) := by
    refine Real.sqrt_pos.mpr ?_
    have : 1 ≤ Nat.sqrt x := by
      have := Nat.sqrt_pos.mpr (by omega : 0 < x)
      omega
    exact_mod_cast this
  have hE₁0 : (0:ℝ) < Real.exp π *
      (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
          * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ))
                * Real.log (x:ℝ) + Real.log 2) + 4 * Real.log 4))
        + T * (6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
            * (16/(Real.log (x:ℝ))^2
                + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
      + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
          * (1/(2*Real.pi^2*T)) := by
    have hA : (0:ℝ) < 12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
        * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ))
              * Real.log (x:ℝ) + Real.log 2) + 4 * Real.log 4)) := by
      have h1 : (0:ℝ) < (Real.exp 1 - 1) * Real.exp (-(k:ℝ))
          * Real.log (x:ℝ) := by positivity
      positivity
    have hB' : (0:ℝ) ≤ T * (6144 + Real.exp (-(π*T^2/64))
        * ((x:ℝ) * Real.log 4))
        * (16/(Real.log (x:ℝ))^2
            + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)) := by
      positivity
    have hC : (0:ℝ) ≤ (∑ p ∈ P, Real.log (p:ℝ)
        /((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2 * (1/(2*Real.pi^2*T)) := by
      positivity
    nlinarith [Real.exp_pos π, mul_pos (Real.exp_pos π) hA,
      mul_nonneg (Real.exp_pos π).le hB']
  -- non-negativity of the unit-interval energy
  have hV₃0 : (0:ℝ) ≤ 2 * (Real.exp π * (12290
        * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
        + 4*T * (6144 + Real.exp (-(π*T^2/64))
            * (((x / blockLo x k : ℕ):ℝ) * Real.log 4))))
      + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
            (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
          Real.log (q:ℝ)/(q:ℝ))^2 := by
    have hlogX1 : (0:ℝ) ≤ Real.log ((x / blockLo x k + 1 : ℕ):ℝ) :=
      Real.log_natCast_nonneg _
    positivity
  -- strict positivity of the tail mass: `2` is in the inner range
  have h2mem : 2 ∈ (x / blockLo x k).primesBelow :=
    Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩
  have hQsum : (0:ℝ) < ∑ q ∈ (x / blockLo x k).primesBelow,
      Real.log (q:ℝ)/(q:ℝ) := by
    have hle : Real.log ((2:ℕ):ℝ)/((2:ℕ):ℝ)
        ≤ ∑ q ∈ (x / blockLo x k).primesBelow, Real.log (q:ℝ)/(q:ℝ) :=
      Finset.single_le_sum
        (fun q _ => div_nonneg (Real.log_natCast_nonneg q)
          (Nat.cast_nonneg q)) h2mem
    have h2 : (0:ℝ) < Real.log ((2:ℕ):ℝ)/((2:ℕ):ℝ) := by
      have : ((2:ℕ):ℝ) = (2:ℝ) := by norm_num
      rw [this]
      positivity
    linarith
  have hnsum : (0:ℝ) < ∑ n ∈ Finset.Icc 1 x, (1:ℝ)/(n:ℝ) := by
    have h1mem : 1 ∈ Finset.Icc 1 x := Finset.mem_Icc.mpr ⟨le_refl 1, hx1⟩
    have hle : (1:ℝ)/((1:ℕ):ℝ) ≤ ∑ n ∈ Finset.Icc 1 x, (1:ℝ)/(n:ℝ) :=
      Finset.single_le_sum (f := fun n : ℕ => (1:ℝ)/(n:ℝ))
        (fun n _ => div_nonneg zero_le_one (Nat.cast_nonneg n)) h1mem
    have : (0:ℝ) < (1:ℝ)/((1:ℕ):ℝ) := by norm_num
    linarith
  have hMtail0 : (0:ℝ) < (∑ q ∈ (x / blockLo x k).primesBelow,
        Real.log (q:ℝ)/(q:ℝ))^2
      * (∑ n ∈ Finset.Icc 1 x, (1:ℝ)/(n:ℝ))^2
      * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2))) := by
    have hM : (0:ℝ) < ((halaszM x : ℕ):ℝ) + 1/2 := by positivity
    have hpi := Real.pi_pos
    positivity
  -- the suppliers
  have hE₁ := ghsBlock_E1_riesz_block_le (fun n => ((f n : ℝ) : ℂ)) hfc
    x k hx hk P T hT hP hfit hPT
  have hV : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2),
        ‖ghsPrimePoly (fun n => ((f n : ℝ) : ℂ))
          (x / blockLo x k).primesBelow t‖^2)
      ≤ 2 * (Real.exp π * (12290
            * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
            + 4*T * (6144 + Real.exp (-(π*T^2/64))
                * (((x / blockLo x k : ℕ):ℝ) * Real.log 4))))
          + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
                (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
              Real.log (q:ℝ)/(q:ℝ))^2 :=
    fun N _ => ghsPrimePoly_unit_energy_primesBelow_le
      (fun n => ((f n : ℝ) : ℂ)) hfc (x / blockLo x k) hX2 T hT (N:ℝ)
  exact tripleConvR_le f hf x hx P hPp h2p
    (x / blockLo x k).primesBelow hQp hQpos hQsub
    _ _ _ b hE₁0 hb0 hV₃0 hMtail0 hE₁ hBu hV le_rfl


open Real Finset in
/-- **§3's `k`-split at the Riesz window** (Track R, N184):

  `∑_{k ∈ [1, M]} |tripleConvR f x (P k)| ≤ K·A + T`,

`tripleConv_ksplit_le` ported verbatim — the split is bookkeeping over
the index range and never looks inside the convolution, so the Riesz
kernel changes nothing.

Left parametric in `A` and `T` as on the sharp side, and for the same
reason: the head is `tripleConvR_block_sharp_le` (N183) with the block
mass and the Halász sup still free, the tail is
`tripleConvR_tail_blocks_le` (N177), and the balance — `K₀`, `T`, and
the smooth cut — is struck once, in the open, in the capstone. -/
theorem tripleConvR_ksplit_le (f : ℕ → ℝ) (x : ℕ) (K M : ℕ) (hKM : K ≤ M)
    (Pk : ℕ → Finset ℕ) (A T : ℝ)
    (hhead : ∀ k ∈ Finset.Icc 1 K, |tripleConvR f x (Pk k)| ≤ A)
    (htail : ∑ k ∈ Finset.Icc (K+1) M, |tripleConvR f x (Pk k)| ≤ T) :
    ∑ k ∈ Finset.Icc 1 M, |tripleConvR f x (Pk k)| ≤ (K:ℝ) * A + T := by
  classical
  have hsplit : Finset.Icc 1 M
      = Finset.Icc 1 K ∪ Finset.Icc (K+1) M := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 K) (Finset.Icc (K+1) M) := by
    refine Finset.disjoint_left.mpr fun k hk1 hk2 => ?_
    rw [Finset.mem_Icc] at hk1 hk2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have hhead' : ∑ k ∈ Finset.Icc 1 K, |tripleConvR f x (Pk k)| ≤ (K:ℝ) * A := by
    refine le_trans (Finset.sum_le_sum hhead) ?_
    simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
    have hcard : ((K + 1 - 1 : ℕ):ℝ) = (K:ℝ) := by
      simp
    rw [hcard]
  linarith [hhead', htail]


open Real in
/-- **The enlarged inner range is the block-scaled one** (Track R,
N185): for `x ≥ 2`,

  `log(x / blockLo x k) ≤ e^{1−k}·log x`.

The fact behind the N185 balance audit: `blockLo x k = ⌈x^{1−e^{1−k}}⌉`
never undershoots its power, so the inner range `X = x/blockLo x k`
that N181 feeds `tripleConvR_le` satisfies `log X ≤ e^{1−k}·log x` —
which is `V₃(k) ≍ e^{−k}·log x`, the decay that meets `E₁(k) ≍
e^{k}/log x` and makes the per-block bound uniform in `k`.  Without
this the enlargement would have traded GHS's block-scaled inner sum
for a `log x` loss per block; with it, the trade is free. -/
theorem log_div_blockLo_le (x k : ℕ) (hx : 2 ≤ x) :
    Real.log ((x / blockLo x k : ℕ):ℝ)
      ≤ Real.exp (1 - (k:ℝ)) * Real.log (x:ℝ) := by
  have hx0 : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hlogx : (0:ℝ) ≤ Real.log (x:ℝ) := Real.log_natCast_nonneg x
  have hrhs0 : (0:ℝ) ≤ Real.exp (1 - (k:ℝ)) * Real.log (x:ℝ) :=
    mul_nonneg (Real.exp_pos _).le hlogx
  rcases Nat.eq_zero_or_pos (x / blockLo x k) with h0 | hpos
  · rw [h0]
    simpa using hrhs0
  · have hcast : (0:ℝ) < ((x / blockLo x k : ℕ):ℝ) := by exact_mod_cast hpos
    have hpow0 : (0:ℝ) < (x:ℝ) ^ (1 - Real.exp (1 - (k:ℝ))) :=
      Real.rpow_pos_of_pos hx0 _
    have hlo : (x:ℝ) ^ (1 - Real.exp (1 - (k:ℝ))) ≤ ((blockLo x k : ℕ):ℝ) := by
      rw [blockLo]
      exact Nat.le_ceil _
    have hdiv : ((x / blockLo x k : ℕ):ℝ) ≤ (x:ℝ) / ((blockLo x k : ℕ):ℝ) :=
      Nat.cast_div_le
    have hdiv2 : (x:ℝ) / ((blockLo x k : ℕ):ℝ)
        ≤ (x:ℝ) / (x:ℝ) ^ (1 - Real.exp (1 - (k:ℝ))) :=
      div_le_div_of_nonneg_left hx0.le hpow0 hlo
    have hrw : (x:ℝ) ^ (Real.exp (1 - (k:ℝ)))
        = (x:ℝ) / (x:ℝ) ^ (1 - Real.exp (1 - (k:ℝ))) := by
      rw [show Real.exp (1 - (k:ℝ)) = 1 - (1 - Real.exp (1 - (k:ℝ))) by ring,
        Real.rpow_sub hx0, Real.rpow_one]
      congr 2
      ring
    calc Real.log ((x / blockLo x k : ℕ):ℝ)
        ≤ Real.log ((x:ℝ) ^ (Real.exp (1 - (k:ℝ)))) := by
          refine Real.log_le_log hcast ?_
          rw [hrw]
          exact le_trans hdiv hdiv2
      _ = Real.exp (1 - (k:ℝ)) * Real.log (x:ℝ) := Real.log_rpow hx0 _


open Real Finset in
/-- **The harmonic sum, priced** (Track R, N186): `∑_{n ≤ x} 1/n ≤ 1 + log x`.
`sum_one_div_add_le_log`'s telescope from `c = 2`, plus the `n = 1` term.
The `HSum` factor of the Riesz tail mass `Mtail`. -/
theorem harmonic_Icc_le (x : ℕ) (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 x, (1:ℝ)/(n:ℝ) ≤ 1 + Real.log (x:ℝ) := by
  classical
  have hsplit : Finset.Icc 1 x = insert 1 (Finset.Ico 2 (x+1)) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
    omega
  have hnotmem : 1 ∉ Finset.Ico 2 (x+1) := by
    simp [Finset.mem_Ico]
  rw [hsplit, Finset.sum_insert hnotmem]
  have h1 : (1:ℝ)/((1:ℕ):ℝ) = 1 := by norm_num
  rw [h1]
  have hre : ∑ n ∈ Finset.Ico 2 (x+1), (1:ℝ)/(n:ℝ)
      = ∑ j ∈ Finset.range (x + 1 - 2), (1:ℝ)/((2 + j : ℕ):ℝ) := by
    rw [Finset.sum_Ico_eq_sum_range]
  rcases Nat.lt_or_ge x 2 with hx2 | hx2
  · -- `x = 1`: the upper sum is empty and `log x = 0` is fine
    have hxe : x = 1 := by omega
    subst hxe
    simp
  · rw [hre]
    have htel := sum_one_div_add_le_log 2 (by norm_num) (x + 1 - 2)
    have hcast : ∀ j : ℕ, (1:ℝ)/((2 + j : ℕ):ℝ) = 1/((2:ℝ) + (j:ℝ)) := by
      intro j
      push_cast
      ring_nf
    rw [Finset.sum_congr rfl fun j _ => hcast j]
    have hRHS : Real.log (2 + ((x + 1 - 2 : ℕ):ℝ) - 1) - Real.log (2 - 1)
        = Real.log (x:ℝ) := by
      have hJ : ((x + 1 - 2 : ℕ):ℝ) = (x:ℝ) - 1 := by
        have h' : x + 1 - 2 = x - 1 := by omega
        rw [h']
        push_cast [Nat.cast_sub (by omega : 1 ≤ x)]
        ring
      have h1 : (2:ℝ) + ((x:ℝ) - 1) - 1 = (x:ℝ) := by ring
      rw [hJ, h1, show (2:ℝ) - 1 = 1 by norm_num, Real.log_one, sub_zero]
    have hS := le_trans htel (le_of_eq hRHS)
    linarith


open Real Finset in
/-- **The small-prime mass is a `T`-quantity** (Track R, N186): the
below-threshold half of N179's split has Mertens mass

  `∑_{q < X prime, q < T²} log q/q ≤ log ⌈T²⌉ + 2`,

independent of `X`.  At the forced `T ≍ √(log x)` this is
`≍ log log x`, entering `V₃` squared and doubled, against the
`≍ e^{−k}·log x` of the main term — the price of N179's threshold
removal, now in closed form. -/
theorem smallMass_le (X : ℕ) (T : ℝ) (hT : 5 ≤ T) :
    ∑ q ∈ X.primesBelow.filter (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
        Real.log (q:ℝ)/(q:ℝ)
      ≤ Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2 := by
  classical
  have hceil2 : 2 ≤ ⌈T^2⌉₊ := by
    have h25 : (25:ℝ) ≤ T^2 := by nlinarith
    have h2 : (2:ℝ) ≤ (⌈T^2⌉₊ : ℝ) :=
      le_trans (by norm_num) (le_trans h25 (Nat.le_ceil _))
    exact_mod_cast h2
  have hsub : X.primesBelow.filter (fun q : ℕ => ¬ T^2 ≤ (q:ℝ))
      ⊆ (⌈T^2⌉₊).primesBelow := by
    intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hqm, hqT⟩ := hq
    rw [Nat.mem_primesBelow] at hqm ⊢
    exact ⟨Nat.lt_ceil.mpr (not_le.mp hqT), hqm.2⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun q _ _ => div_nonneg (Real.log_natCast_nonneg q)
      (Nat.cast_nonneg q))) ?_
  exact sum_log_div_primesBelow_le_sharp _ hceil2

open Real Finset in
/-- **The inner-range Mertens mass decays with the block** (Track R,
N186): `∑_{q < x/blockLo x k} log q/q ≤ e^{1−k}·log x + 2`.

Sharp Mertens (`sum_log_div_primesBelow_le_sharp`) at the enlarged
inner range, transported through N185: the `QMass` factor of `Mtail`
carries the same `e^{−k}` decay as `V₃`, which is what keeps
`E₁·Mtail ≍ e^{−k}/log x` negligible in the balance. -/
theorem qMass_le (x k : ℕ) (hx : 2 ≤ x) (hX2 : 2 ≤ x / blockLo x k) :
    ∑ q ∈ (x / blockLo x k).primesBelow, Real.log (q:ℝ)/(q:ℝ)
      ≤ Real.exp (1 - (k:ℝ)) * Real.log (x:ℝ) + 2 := by
  refine le_trans (sum_log_div_primesBelow_le_sharp _ hX2) ?_
  have := log_div_blockLo_le x k hx
  linarith



/-- The tail absorption `81T ≤ epi·81T` folded into the bracket. -/
private lemma bal_prodOne (Y b T epi eone : ℝ) (hepi : 1 ≤ epi)
    (hepi0 : 0 < epi) (hT0 : 0 < T) (hb0 : 0 ≤ b)
    (heone0 : 0 ≤ eone) (heone : eone ≤ 2.72)
    (hY0 : 0 ≤ Y) (hY : Y ≤ epi * (331830 + 6145*T) + 81*T) :
    (60*12290) * (eone * (epi * b^2)) * Y
      ≤ epi^2 * ((3*10^12) * b^2 + (2*10^10) * (T * b^2)) := by
  have hcoef0 : (0:ℝ) ≤ (60*12290) * (eone * (epi * b^2)) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hY hcoef0
  refine le_trans h1 ?_
  have h81 : (81:ℝ)*T ≤ epi * (81*T) := by nlinarith [hepi, hT0]
  have hfac : epi * (331830 + 6145*T) + 81*T
      ≤ epi * (331830 + 6226*T) := by nlinarith [h81]
  refine le_trans (mul_le_mul_of_nonneg_left hfac hcoef0) ?_
  have hb2 : (0:ℝ) ≤ b^2 := sq_nonneg b
  have hepi2b : (0:ℝ) ≤ epi^2 * b^2 := by positivity
  have hepi2Tb : (0:ℝ) ≤ epi^2 * (T*b^2) := by positivity
  nlinarith [heone, heone0, hepi0, hb2, hepi2b, hepi2Tb, hT0,
    mul_nonneg (mul_nonneg hepi0.le hepi0.le) hb2,
    mul_nonneg (mul_nonneg (mul_nonneg hepi0.le hepi0.le) hb2) hT0.le]

private lemma bal_prodTwo (E b T γ lg2 epi : ℝ) (hepi0 : 0 < epi)
    (hE0 : 0 ≤ E) (hE : E ≤ epi * 448602) (hT0 : 0 < T)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hb0 : 0 ≤ b)
    (hlg2 : 0 ≤ lg2) (hlg2u : lg2 ≤ 0.694) :
    E * (60 * (epi * (12290 * (lg2 + 2) + 4*T*(6144 + γ))) * b^2)
      ≤ epi^2 * ((9*10^11) * b^2 + (7*10^11) * (T * b^2)) := by
  have hin : 12290 * (lg2 + 2) + 4*T*(6144 + γ) ≤ 33110 + 24580*T := by
    nlinarith [hlg2u, hγ1, hT0]
  have hin0 : (0:ℝ) ≤ 12290 * (lg2 + 2) + 4*T*(6144 + γ) := by positivity
  have hV : 60 * (epi * (12290 * (lg2 + 2) + 4*T*(6144 + γ))) * b^2
      ≤ 60 * (epi * (33110 + 24580*T)) * b^2 := by
    have h1 : epi * (12290 * (lg2 + 2) + 4*T*(6144 + γ))
        ≤ epi * (33110 + 24580*T) := mul_le_mul_of_nonneg_left hin hepi0.le
    have h2 : (60:ℝ) * (epi * (12290 * (lg2 + 2) + 4*T*(6144 + γ)))
        ≤ 60 * (epi * (33110 + 24580*T)) :=
      mul_le_mul_of_nonneg_left h1 (by norm_num)
    exact mul_le_mul_of_nonneg_right h2 (sq_nonneg b)
  have hV0 : (0:ℝ) ≤ 60 * (epi * (12290 * (lg2 + 2) + 4*T*(6144 + γ))) * b^2 := by
    positivity
  have hstep := mul_le_mul hE hV hV0 (by positivity : (0:ℝ) ≤ epi * 448602)
  refine le_trans hstep ?_
  have hb2 : (0:ℝ) ≤ b^2 := sq_nonneg b
  have hepi2b : (0:ℝ) ≤ epi^2 * b^2 := by positivity
  have hepi2Tb : (0:ℝ) ≤ epi^2 * (T*b^2) := by positivity
  nlinarith [hepi0, hb2, hepi2b, hepi2Tb, hT0,
    mul_nonneg (mul_nonneg hepi0.le hepi0.le) hb2,
    mul_nonneg (mul_nonneg (mul_nonneg hepi0.le hepi0.le) hb2) hT0.le]

private lemma bal_prodThree (E b SM epi : ℝ) (hepi : 1 ≤ epi)
    (hepi0 : 0 < epi) (hE0 : 0 ≤ E) (hE : E ≤ epi * 448602)
    (hb0 : 0 ≤ b) (hSM0 : 0 ≤ SM) :
    E * (60 * SM^2 * b^2) ≤ epi^2 * ((3*10^7) * (SM^2 * b^2)) := by
  have hX0 : (0:ℝ) ≤ 60 * SM^2 * b^2 := by positivity
  have hstep := mul_le_mul_of_nonneg_right hE hX0
  refine le_trans hstep ?_
  have hSb : (0:ℝ) ≤ SM^2 * b^2 := by positivity
  have h1 : (0:ℝ) ≤ epi * (SM^2 * b^2) := by positivity
  nlinarith [hepi, hepi0, hSb, h1,
    mul_nonneg (mul_nonneg hepi0.le hepi0.le) hSb]

private lemma bal_prodFour (E M epi : ℝ) (hepi : 1 ≤ epi)
    (hepi0 : 0 < epi) (hE0 : 0 ≤ E) (hE : E ≤ epi * 448602)
    (hM0 : 0 ≤ M) (hM : M ≤ 23) :
    E * M ≤ epi^2 * (11*10^6) := by
  have hstep := mul_le_mul hE hM hM0 (by positivity : (0:ℝ) ≤ epi * 448602)
  refine le_trans hstep ?_
  nlinarith [hepi, hepi0, mul_pos hepi0 hepi0]

private lemma bal_Ec17 (X u epi : ℝ) (hX : X ≤ 17 * u^2)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (hepi : 1 ≤ epi) : X ≤ epi * 17 := by
  nlinarith [hX, hu0, hu1, hepi]

private lemma bal_sum (b T SM epi : ℝ) (hb0 : 0 ≤ b) (hT0 : 0 < T)
    (hSM0 : 0 ≤ SM) (hepi0 : 0 < epi) :
    epi^2 * ((3*10^12) * b^2 + (2*10^10) * (T * b^2))
      + epi^2 * ((9*10^11) * b^2 + (7*10^11) * (T * b^2))
      + epi^2 * ((3*10^7) * (SM^2 * b^2))
      + epi^2 * (11*10^6)
      ≤ epi^2 * 10^15 * ((SM^2 + T + 1) * b^2 + 1) := by
  have hb2 : (0:ℝ) ≤ b^2 := sq_nonneg b
  have h1 : (0:ℝ) ≤ epi^2 * b^2 := by positivity
  have h2 : (0:ℝ) ≤ epi^2 * (T*b^2) := by
    have : (0:ℝ) ≤ T * b^2 := mul_nonneg hT0.le hb2
    positivity
  have h3 : (0:ℝ) ≤ epi^2 * (SM^2*b^2) := by positivity
  have h4 : (0:ℝ) ≤ epi^2 := by positivity
  nlinarith [h1, h2, h3, h4]

set_option maxHeartbeats 3200000 in
open Real in
/-- **The balance, as pure algebra** (Track R, N187): with `P = u·L`
standing for `e^{−k}·log x`, the per-block √-argument of N183 — its
three energy summands against the four V-side pieces — is bounded,
`k`-freely, by

  `(e^π)²·10¹⁵·((SM² + T + 1)·b² + 1)`.

The twelve products reduce to three mechanisms: the diagonal
`(1/P)·P`-cancellations (with `c₀ = 12·log 2 ≤ 12·P` exact, no
numerics), the fit condition `log 2 ≤ P` capping every `1/P`, and
`L ≤ T²` killing the `u³L/T` cross term of the Fourier tail (audit
correction 2).  `V₃`'s `4T·(6144+γ)` term survives undamped — it is
the `T·b²` of the target, `≍ √(log x)·b²` at the forced `T ≍ √(log x)`,
harmless against a Halász-small `b` (audit correction 1).

No Finsets, no integrals: N188's instantiation feeds this with the
N186 masses and N183's expressions, and `gcongr` does the rest. -/
theorem balance_product_le (L u T b γ S Mp SM HS W : ℝ)
    (hL2 : Real.log 2 ≤ u * L) (hu0 : 0 < u) (hu1 : u ≤ 1) (hL1 : 1 ≤ L)
    (hT5 : 5 ≤ T) (hTL : T ≤ L) (hLT : L ≤ T^2)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hS0 : 0 ≤ S) (hSL : S * L ≤ 1)
    (hMp0 : 0 ≤ Mp) (hMp : Mp ≤ 38 * u)
    (hSM0 : 0 ≤ SM) (hHS0 : 0 ≤ HS)
    (hW0 : 0 ≤ W) (hW : W * (L^2 * HS^2) ≤ 1)
    (hb0 : 0 ≤ b) :
    (Real.exp π * (12290 * ((1/(u^2*L^2))
          * (4*(Real.exp 1 - 1)*(u*L) + (4*Real.log 2 + 4*Real.log 4))))
        + Real.exp π * (T * (6144 + γ) * (16/L^2 + S))
      + Mp^2 * (1/(2*Real.pi^2*T)))
    * (5 * (2 * (Real.exp π * (12290 * (Real.exp 1 * (u*L) + Real.log 2 + 2)
          + 4*T*(6144 + γ))) + 2*SM^2) * (6*b^2)
      + (Real.exp 1 * (u*L) + 2)^2 * HS^2 * W)
    ≤ (Real.exp π)^2 * 10^15 * ((SM^2 + T + 1) * b^2 + 1) := by
  -- opaque `P = u·L`: a `set` here let-binds and poisons every later
  -- `nlinarith` through whnf unfolding (the pin's set-poisoning gotcha)
  obtain ⟨P, hP_def⟩ : ∃ p : ℝ, p = u * L := ⟨u * L, rfl⟩
  have hL2P : Real.log 2 ≤ P := by rw [hP_def]; exact hL2
  have hP0 : (0:ℝ) < P := lt_of_lt_of_le (Real.log_pos (by norm_num)) hL2P
  have hPL : P ≤ L := by
    rw [hP_def]
    nlinarith [hL1, hu1, hu0]
  have hL0 : (0:ℝ) < L := by linarith
  have hT0 : (0:ℝ) < T := by linarith
  have hlog2l : (0.693:ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlog2u : Real.log 2 ≤ (0.694:ℝ) := by
    have := Real.log_two_lt_d9
    linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    push_cast
    ring
  have he_lt : Real.exp 1 ≤ (2.7182818286:ℝ) := Real.exp_one_lt_d9.le
  have he272 : Real.exp 1 ≤ (2.72:ℝ) := by linarith
  have heπ : (1:ℝ) ≤ Real.exp π := by
    have h1 := Real.add_one_le_exp π
    have h2 := Real.pi_gt_three
    linarith
  have heπ0 : (0:ℝ) < Real.exp π := Real.exp_pos _
  have hπ2 : (9:ℝ) ≤ Real.pi^2 := by
    have := Real.pi_gt_three
    nlinarith
  have hP69 : (0.693:ℝ) ≤ P := le_trans hlog2l hL2P
  -- fold the goal into `P`-form
  rw [show u^2*L^2 = (u*L)^2 by ring,
    show (4:ℝ)*Real.log 2 + 4*Real.log 4 = 12*Real.log 2 by rw [hlog4]; ring,
    ← hP_def]
  -- ===== E-side bounds (literal expressions) =====
  have hEa_le : Real.exp π * (12290 * (1/P^2
      * (4*(Real.exp 1 - 1)*P + 12*Real.log 2))) ≤ Real.exp π * 344120 := by
    have hkey : 1/P^2 * (4*(Real.exp 1 - 1)*P + 12*Real.log 2) ≤ 28 := by
      rw [show 1/P^2 * (4*(Real.exp 1 - 1)*P + 12*Real.log 2)
          = (4*(Real.exp 1 - 1)*P + 12*Real.log 2)/P^2 by ring,
        div_le_iff₀ (by positivity)]
      have h1 : 4*(Real.exp 1 - 1)*P ≤ 6.88 * P := by nlinarith [he272, hP0]
      have h2 : 12*Real.log 2 ≤ 12 * P := by linarith [hL2P]
      have h3 : (18.88:ℝ) * P ≤ 28 * P^2 := by nlinarith [hP69, hP0]
      linarith
    calc Real.exp π * (12290 * (1/P^2
        * (4*(Real.exp 1 - 1)*P + 12*Real.log 2)))
        ≤ Real.exp π * (12290 * 28) := by
          have h12 : 12290 * (1/P^2 * (4*(Real.exp 1 - 1)*P + 12*Real.log 2))
              ≤ 12290 * 28 := by linarith
          exact mul_le_mul_of_nonneg_left h12 heπ0.le
      _ = Real.exp π * 344120 := by norm_num
  have hPEa_le : P * (Real.exp π * (12290 * (1/P^2
      * (4*(Real.exp 1 - 1)*P + 12*Real.log 2)))) ≤ Real.exp π * 233510 := by
    have hkey : P * (1/P^2 * (4*(Real.exp 1 - 1)*P + 12*Real.log 2)) ≤ 19 := by
      rw [show P * (1/P^2 * (4*(Real.exp 1 - 1)*P + 12*Real.log 2))
          = (4*(Real.exp 1 - 1)*P + 12*Real.log 2)/P by field_simp,
        div_le_iff₀ hP0]
      have h1 : 4*(Real.exp 1 - 1)*P ≤ 6.88 * P := by nlinarith [he272, hP0]
      have h2 : 12*Real.log 2 ≤ 12 * P := by linarith [hL2P]
      linarith
    calc P * (Real.exp π * (12290 * (1/P^2
        * (4*(Real.exp 1 - 1)*P + 12*Real.log 2))))
        = Real.exp π * (12290
          * (P * (1/P^2 * (4*(Real.exp 1 - 1)*P + 12*Real.log 2)))) := by ring
      _ ≤ Real.exp π * (12290 * 19) := by
          have h12 : 12290 * (P * (1/P^2
              * (4*(Real.exp 1 - 1)*P + 12*Real.log 2))) ≤ 12290 * 19 := by
            linarith
          exact mul_le_mul_of_nonneg_left h12 heπ0.le
      _ = Real.exp π * 233510 := by norm_num
  have hEb_le : Real.exp π * (T * (6144 + γ) * (16/L^2 + S))
      ≤ Real.exp π * 104465 := by
    have h16 : T * (16/L^2) ≤ 16 := by
      rw [show T * (16/L^2) = 16*T/L^2 by ring,
        div_le_iff₀ (by positivity : (0:ℝ) < L^2)]
      nlinarith [hTL, hL1, hL0]
    have hTS : T * S ≤ 1 := by nlinarith [hSL, hTL, hS0, hT0, hL0]
    have hexp : T * (6144 + γ) * (16/L^2 + S) ≤ 104465 := by
      have hg : (6144 + γ) ≤ 6145 := by linarith
      have hsum : T * (16/L^2 + S) ≤ 17 := by
        have hh : T * (16/L^2 + S) = T * (16/L^2) + T * S := by ring
        rw [hh]; linarith
      have hns : (0:ℝ) ≤ 16/L^2 + S := by positivity
      nlinarith [hT0.le, hsum, hg, mul_nonneg hT0.le hns]
    exact mul_le_mul_of_nonneg_left hexp heπ0.le
  have hPEb_le : P * (Real.exp π * (T * (6144 + γ) * (16/L^2 + S)))
      ≤ Real.exp π * (98320 + 6145*T) := by
    have h16P : T * (6144 + γ) * (16*P/L^2) ≤ 98320 := by
      rw [show T * (6144 + γ) * (16*P/L^2)
          = (T * (6144 + γ) * (16*P))/L^2 by ring,
        div_le_iff₀ (by positivity : (0:ℝ) < L^2)]
      have hTP : T * P ≤ L^2 := by nlinarith [hTL, hPL, hP0, hT0, hL0]
      have hTg : T * (6144 + γ) ≤ 6145 * T := by nlinarith [hγ1, hT0]
      calc T * (6144 + γ) * (16*P)
          ≤ 6145 * T * (16*P) :=
            mul_le_mul_of_nonneg_right hTg (by positivity)
        _ = 98320 * (T*P) := by ring
        _ ≤ 98320 * L^2 := by nlinarith [hTP]
    have hSP : T * (6144 + γ) * (S*P) ≤ 6145 * T := by
      have hSP1 : S * P ≤ 1 := by nlinarith [hSL, hPL, hS0, hL0]
      have hTg0 : (0:ℝ) ≤ T * (6144 + γ) := by positivity
      calc T * (6144 + γ) * (S*P)
          ≤ T * (6144 + γ) * 1 := mul_le_mul_of_nonneg_left hSP1 hTg0
        _ = T * (6144 + γ) := mul_one _
        _ ≤ 6145 * T := by nlinarith [hγ1, hT0]
    calc P * (Real.exp π * (T * (6144 + γ) * (16/L^2 + S)))
        = Real.exp π * (T * (6144 + γ) * (16*P/L^2)
            + T * (6144 + γ) * (S*P)) := by ring
      _ ≤ Real.exp π * (98320 + 6145*T) := by
          have hcomb : T * (6144 + γ) * (16*P/L^2)
              + T * (6144 + γ) * (S*P) ≤ 98320 + 6145*T := by linarith
          exact mul_le_mul_of_nonneg_left hcomb heπ0.le
  have hEc_le : Mp^2 * (1/(2*Real.pi^2*T)) ≤ 17 * u^2 := by
    have hMp2 : Mp^2 ≤ 1444 * u^2 := by nlinarith [hMp, hMp0, hu0]
    have hinv : 1/(2*Real.pi^2*T) ≤ 1/90 := by
      rw [div_le_div_iff₀ (by nlinarith [hπ2, hT5] : (0:ℝ) < 2*Real.pi^2*T)
        (by norm_num : (0:ℝ) < 90)]
      nlinarith [hπ2, hT5]
    have hinv0 : (0:ℝ) ≤ 1/(2*Real.pi^2*T) := by positivity
    calc Mp^2 * (1/(2*Real.pi^2*T))
        ≤ 1444 * u^2 * (1/(2*Real.pi^2*T)) :=
          mul_le_mul_of_nonneg_right hMp2 hinv0
      _ ≤ 1444 * u^2 * (1/90) :=
          mul_le_mul_of_nonneg_left hinv
            (by positivity : (0:ℝ) ≤ 1444 * u^2)
      _ ≤ 17 * u^2 := by linarith [sq_nonneg u]
  have hPEc_le : P * (Mp^2 * (1/(2*Real.pi^2*T))) ≤ 81 * T := by
    have hMp2 : Mp^2 ≤ 1444 * u^2 := by nlinarith [hMp, hMp0, hu0]
    have hden0 : (0:ℝ) < 2*Real.pi^2*T := by nlinarith [hπ2, hT5]
    have hu3 : u^3 ≤ 1 := pow_le_one₀ hu0.le hu1
    have hu3L : u^3 * L ≤ T^2 := by nlinarith [hLT, hu3, hL0]
    rw [show P * (Mp^2 * (1/(2*Real.pi^2*T)))
        = P * Mp^2 / (2*Real.pi^2*T) by ring,
      div_le_iff₀ hden0]
    have hPMp : P * Mp^2 ≤ 1444 * (u^3 * L) := by
      rw [hP_def]
      nlinarith [hMp2, hu0, hL0, sq_nonneg u]
    nlinarith [hPMp, hu3L, hπ2, hT5, hT0, sq_nonneg T]
  -- ===== V-side pieces and non-negativity =====
  have he1nn : (0:ℝ) ≤ Real.exp 1 - 1 := by
    linarith [Real.exp_one_gt_d9.le]
  have hEa0 : (0:ℝ) ≤ Real.exp π * (12290 * (1/P^2
      * (4*(Real.exp 1 - 1)*P + 12*Real.log 2))) := by
    have hnum : (0:ℝ) ≤ 4*(Real.exp 1 - 1)*P + 12*Real.log 2 := by
      nlinarith [mul_nonneg he1nn hP0.le, hlog2l]
    positivity
  have hEb0 : (0:ℝ) ≤ Real.exp π * (T * (6144 + γ) * (16/L^2 + S)) := by
    positivity
  have hEc0 : (0:ℝ) ≤ Mp^2 * (1/(2*Real.pi^2*T)) := by positivity
  have hE0 : (0:ℝ) ≤ Real.exp π * (12290 * (1/P^2
      * (4*(Real.exp 1 - 1)*P + 12*Real.log 2)))
      + Real.exp π * (T * (6144 + γ) * (16/L^2 + S))
      + Mp^2 * (1/(2*Real.pi^2*T)) := by linarith [hEa0, hEb0, hEc0]
  have hE_le : Real.exp π * (12290 * (1/P^2
        * (4*(Real.exp 1 - 1)*P + 12*Real.log 2)))
      + Real.exp π * (T * (6144 + γ) * (16/L^2 + S))
      + Mp^2 * (1/(2*Real.pi^2*T)) ≤ Real.exp π * 448602 := by
    have hEc17 : Mp^2 * (1/(2*Real.pi^2*T)) ≤ Real.exp π * 17 :=
      bal_Ec17 _ u (Real.exp π) hEc_le hu0 hu1 heπ
    linarith [hEa_le, hEb_le]
  have hPE_le : P * (Real.exp π * (12290 * (1/P^2
        * (4*(Real.exp 1 - 1)*P + 12*Real.log 2)))
      + Real.exp π * (T * (6144 + γ) * (16/L^2 + S))
      + Mp^2 * (1/(2*Real.pi^2*T)))
      ≤ Real.exp π * (331830 + 6145*T) + 81*T := by
    have hexpand : P * (Real.exp π * (12290 * (1/P^2
          * (4*(Real.exp 1 - 1)*P + 12*Real.log 2)))
        + Real.exp π * (T * (6144 + γ) * (16/L^2 + S))
        + Mp^2 * (1/(2*Real.pi^2*T)))
        = P * (Real.exp π * (12290 * (1/P^2
            * (4*(Real.exp 1 - 1)*P + 12*Real.log 2))))
          + P * (Real.exp π * (T * (6144 + γ) * (16/L^2 + S)))
          + P * (Mp^2 * (1/(2*Real.pi^2*T))) := by ring
    rw [hexpand]
    have hsum := add_le_add (add_le_add hPEa_le hPEb_le) hPEc_le
    refine le_trans hsum (le_of_eq ?_)
    ring
  have hMt_le : (Real.exp 1 * P + 2)^2 * HS^2 * W ≤ 23 := by
    have h1 : Real.exp 1 * P + 2 ≤ 4.72 * L := by
      have ha : Real.exp 1 * P ≤ 2.72 * P :=
        mul_le_mul_of_nonneg_right he272 hP0.le
      have hb2 : (2.72:ℝ) * P ≤ 2.72 * L :=
        mul_le_mul_of_nonneg_left hPL (by norm_num)
      linarith [hL1]
    have h10 : (0:ℝ) ≤ Real.exp 1 * P + 2 := by positivity
    have h2 : (Real.exp 1 * P + 2)^2 ≤ 22.2784 * L^2 := by
      have hsq := mul_self_le_mul_self h10 h1
      calc (Real.exp 1 * P + 2)^2
          = (Real.exp 1 * P + 2) * (Real.exp 1 * P + 2) := sq (Real.exp 1 * P + 2) ▸ by ring
        _ ≤ (4.72 * L) * (4.72 * L) := hsq
        _ = 22.2784 * L^2 := by ring
    have h4 : (0:ℝ) ≤ HS^2 * W := by positivity
    calc (Real.exp 1 * P + 2)^2 * HS^2 * W
        = (Real.exp 1 * P + 2)^2 * (HS^2 * W) := by ring
      _ ≤ 22.2784 * L^2 * (HS^2 * W) :=
          mul_le_mul_of_nonneg_right h2 h4
      _ = 22.2784 * (W * (L^2 * HS^2)) := by ring
      _ ≤ 22.2784 * 1 :=
          mul_le_mul_of_nonneg_left hW (by norm_num)
      _ ≤ 23 := by norm_num
  have hMt0 : (0:ℝ) ≤ (Real.exp 1 * P + 2)^2 * HS^2 * W := by positivity
  -- ===== the assembly =====
  have hVsplit : 5 * (2 * (Real.exp π * (12290 * (Real.exp 1 * P
        + Real.log 2 + 2) + 4*T*(6144 + γ))) + 2*SM^2) * (6*b^2)
      + (Real.exp 1 * P + 2)^2 * HS^2 * W
      = (60*12290) * (Real.exp 1 * (Real.exp π * b^2)) * P
        + 60 * (Real.exp π * (12290 * (Real.log 2 + 2)
            + 4*T*(6144 + γ))) * b^2
        + 60 * SM^2 * b^2
        + (Real.exp 1 * P + 2)^2 * HS^2 * W := by ring
  rw [hVsplit, mul_add, mul_add, mul_add]
  have hPE0 : (0:ℝ) ≤ P * (Real.exp π * (12290 * (1/P^2
      * (4*(Real.exp 1 - 1)*P + 12*Real.log 2)))
      + Real.exp π * (T * (6144 + γ) * (16/L^2 + S))
      + Mp^2 * (1/(2*Real.pi^2*T))) := mul_nonneg hP0.le hE0
  have h1 : (Real.exp π * (12290 * (1/P^2
        * (4*(Real.exp 1 - 1)*P + 12*Real.log 2)))
      + Real.exp π * (T * (6144 + γ) * (16/L^2 + S))
      + Mp^2 * (1/(2*Real.pi^2*T)))
      * ((60*12290) * (Real.exp 1 * (Real.exp π * b^2)) * P)
      ≤ (Real.exp π)^2 * ((3*10^12) * b^2 + (2*10^10) * (T * b^2)) := by
    rw [show (Real.exp π * (12290 * (1/P^2
          * (4*(Real.exp 1 - 1)*P + 12*Real.log 2)))
        + Real.exp π * (T * (6144 + γ) * (16/L^2 + S))
        + Mp^2 * (1/(2*Real.pi^2*T)))
        * ((60*12290) * (Real.exp 1 * (Real.exp π * b^2)) * P)
        = (60*12290) * (Real.exp 1 * (Real.exp π * b^2))
          * (P * (Real.exp π * (12290 * (1/P^2
              * (4*(Real.exp 1 - 1)*P + 12*Real.log 2)))
            + Real.exp π * (T * (6144 + γ) * (16/L^2 + S))
            + Mp^2 * (1/(2*Real.pi^2*T)))) by ring]
    exact bal_prodOne _ b T (Real.exp π) (Real.exp 1) heπ heπ0 hT0 hb0
      (Real.exp_pos 1).le he272 hPE0 hPE_le
  have h2 : (Real.exp π * (12290 * (1/P^2
        * (4*(Real.exp 1 - 1)*P + 12*Real.log 2)))
      + Real.exp π * (T * (6144 + γ) * (16/L^2 + S))
      + Mp^2 * (1/(2*Real.pi^2*T)))
      * (60 * (Real.exp π * (12290 * (Real.log 2 + 2)
          + 4*T*(6144 + γ))) * b^2)
      ≤ (Real.exp π)^2 * ((9*10^11) * b^2 + (7*10^11) * (T * b^2)) :=
    bal_prodTwo _ b T γ (Real.log 2) (Real.exp π) heπ0 hE0 hE_le hT0
      hγ0 hγ1 hb0 (Real.log_nonneg (by norm_num)) hlog2u
  have h3 : (Real.exp π * (12290 * (1/P^2
        * (4*(Real.exp 1 - 1)*P + 12*Real.log 2)))
      + Real.exp π * (T * (6144 + γ) * (16/L^2 + S))
      + Mp^2 * (1/(2*Real.pi^2*T)))
      * (60 * SM^2 * b^2)
      ≤ (Real.exp π)^2 * ((3*10^7) * (SM^2 * b^2)) :=
    bal_prodThree _ b SM (Real.exp π) heπ heπ0 hE0 hE_le hb0 hSM0
  have h4 : (Real.exp π * (12290 * (1/P^2
        * (4*(Real.exp 1 - 1)*P + 12*Real.log 2)))
      + Real.exp π * (T * (6144 + γ) * (16/L^2 + S))
      + Mp^2 * (1/(2*Real.pi^2*T)))
      * ((Real.exp 1 * P + 2)^2 * HS^2 * W)
      ≤ (Real.exp π)^2 * (11*10^6) :=
    bal_prodFour _ _ (Real.exp π) heπ heπ0 hE0 hE_le hMt0 hMt_le
  refine le_trans (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) ?_
  exact bal_sum b T SM (Real.exp π) hb0 hT0 hSM0 heπ0


open Real in
/-- **The block index, as `u = e^{−k}`** (Track R, N188): the two
exponential shapes of the energy bound coincide,
`e^{2k}/L² = 1/((e^{−k})²·L²)`. -/
private lemma exp_two_k_div_sq (k : ℕ) (L : ℝ) :
    Real.exp (2*(k:ℝ)) / L^2 = 1/((Real.exp (-(k:ℝ)))^2 * L^2) := by
  have h : (Real.exp (-(k:ℝ)))^2 = Real.exp (-(2*(k:ℝ))) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [h, Real.exp_neg]
  field_simp

open Real in
/-- `4·(e−1)·e^{−k}·L` in the `u`-form the balance lemma reads. -/
private lemma exp_neg_k_mul_shape (k : ℕ) (L : ℝ) :
    4*(Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * L
      = 4*(Real.exp 1 - 1) * (Real.exp (-(k:ℝ)) * L) := by
  ring

open Real in
/-- `e^{1−k}·L = e·(e^{−k}·L)` — N185's decay in the balance's `e·P` shape. -/
private lemma exp_one_sub_k_mul (k : ℕ) (L : ℝ) :
    Real.exp (1 - (k:ℝ)) * L = Real.exp 1 * (Real.exp (-(k:ℝ)) * L) := by
  rw [show (1 - (k:ℝ)) = 1 + (-(k:ℝ)) by ring, Real.exp_add]
  ring

open Real in
/-- `1 ≤ log x` for `x ≥ 3` — the balance's `hL1`. -/
private lemma one_le_log_of_three_le (x : ℕ) (hx : 3 ≤ x) :
    (1:ℝ) ≤ Real.log (x:ℝ) := by
  have he : Real.exp 1 ≤ (x:ℝ) := by
    have h3 : (3:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
    have := Real.exp_one_lt_d9
    linarith
  calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (x:ℝ) := Real.log_le_log (Real.exp_pos 1) he


set_option maxHeartbeats 3200000 in
open MeasureTheory Real Complex ArithmeticFunction Finset in
open scoped FourierTransform in
/-- **§3's per-block estimate, balanced** (Track R, N189): on a fitted
block with `T² ≤ p`, under the six balance side conditions (all
discharged at the concrete `T ≍ √(log x)` later),

  `|tripleConvR f x P| ≤ x·√((e^π)²·10¹⁵·((SM² + T + 1)·b² + 1)) + 2x·log 4`,

with `SM` the small-prime Mertens mass of N179's split — the only
`k`-dependence left, and it is bounded (`smallMass_le`, `≍ log log x`).

N183's expressions walk into `balance_product_le` by pure monotonicity:
the energy side is *ring-equal* to the `u`-form (N188's bridges), the
`V`-side loses `γ_X ≤ γ_x` and `log(X+1)+2 ≤ e·P+log 2+2` (N185), the
tail loses `(∑_Q log q/q)² ≤ (e·P+2)²` (N186's `qMass_le`), and `hL2`
is `block_index_le_of_fit` — the fit condition, again, is the entire
uniformity. -/
theorem tripleConvR_block_balanced_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (x k : ℕ) (hx3 : 3 ≤ x) (hk : 1 ≤ k) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k)
    (hfit : 2 * blockHi x k ≤ x)
    (hX3 : 3 ≤ x / blockLo x k)
    (T : ℝ) (hT : 5 ≤ T) (hPT : ∀ p ∈ P, T^2 ≤ (p:ℝ))
    (b : ℝ) (hb0 : 0 ≤ b)
    (hBu : ∀ t : ℝ,
      ‖ghsMainPoly (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 x) t‖ ≤ b)
    (hTL : T ≤ Real.log (x:ℝ)) (hLT : Real.log (x:ℝ) ≤ T^2)
    (hγ1 : Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4) ≤ 1)
    (hSL : 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)
      * Real.log (x:ℝ) ≤ 1)
    (hMp : ∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|)
      ≤ 38 * Real.exp (-(k:ℝ)))
    (hW : (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))
      * ((Real.log (x:ℝ))^2
        * (∑ n ∈ Finset.Icc 1 x, (1:ℝ)/(n:ℝ))^2) ≤ 1) :
    |tripleConvR f x P|
      ≤ (x:ℝ) * Real.sqrt ((Real.exp π)^2 * 10^15
          * (((∑ q ∈ (x / blockLo x k).primesBelow.filter
                (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
              Real.log (q:ℝ)/(q:ℝ))^2 + T + 1) * b^2 + 1))
        + 2*(x:ℝ)*Real.log 4 := by
  classical
  have hx : 2 ≤ x := by omega
  have hxR0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
  have hL0 : (0:ℝ) < Real.log (x:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 2 ≤ x))
  have hu0 : (0:ℝ) < Real.exp (-(k:ℝ)) := Real.exp_pos _
  have hu1 : Real.exp (-(k:ℝ)) ≤ 1 := by
    rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (Nat.cast_nonneg k))
  refine le_trans (tripleConvR_block_sharp_le f hf x k hx hk P hP hfit hX3
    T hT hPT b hb0 hBu) ?_
  -- the √-argument chain
  have hX1 : 1 ≤ x / blockLo x k := by omega
  have hXx : x / blockLo x k ≤ x := Nat.div_le_self x _
  -- (i) the enlarged-range γ is dominated by the global one
  have hγmono : Real.exp (-(π*T^2/64)) * (((x / blockLo x k : ℕ):ℝ) * Real.log 4)
      ≤ Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4) := by
    have hc : ((x / blockLo x k : ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast hXx
    have h4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hc h4) (Real.exp_pos _).le
  -- (ii) `log(X+1) + 2 ≤ e·(u·L) + log 2 + 2`
  have hlogX1 : Real.log ((x / blockLo x k + 1 : ℕ):ℝ)
      ≤ Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + Real.log 2 := by
    have hle2X : ((x / blockLo x k + 1 : ℕ):ℝ)
        ≤ 2 * ((x / blockLo x k : ℕ):ℝ) := by
      have : x / blockLo x k + 1 ≤ 2 * (x / blockLo x k) := by omega
      exact_mod_cast this
    have hX0 : (0:ℝ) < ((x / blockLo x k : ℕ):ℝ) := by
      exact_mod_cast (by omega : 0 < x / blockLo x k)
    calc Real.log ((x / blockLo x k + 1 : ℕ):ℝ)
        ≤ Real.log (2 * ((x / blockLo x k : ℕ):ℝ)) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < x / blockLo x k + 1))
            hle2X
      _ = Real.log 2 + Real.log ((x / blockLo x k : ℕ):ℝ) :=
          Real.log_mul (by norm_num) (ne_of_gt hX0)
      _ ≤ Real.log 2 + Real.exp (1 - (k:ℝ)) * Real.log (x:ℝ) := by
          linarith [log_div_blockLo_le x k hx]
      _ = Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + Real.log 2 := by
          rw [exp_one_sub_k_mul]
          ring
  -- (iii) the tail mass in the `e·P + 2` shape
  have hqm : ∑ q ∈ (x / blockLo x k).primesBelow, Real.log (q:ℝ)/(q:ℝ)
      ≤ Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + 2 := by
    have h := qMass_le x k hx (by omega)
    rw [exp_one_sub_k_mul] at h
    linarith
  have hqm0 : (0:ℝ) ≤ ∑ q ∈ (x / blockLo x k).primesBelow,
      Real.log (q:ℝ)/(q:ℝ) :=
    Finset.sum_nonneg fun q _ => div_nonneg (Real.log_natCast_nonneg q)
      (Nat.cast_nonneg q)
  have hqm_sq : (∑ q ∈ (x / blockLo x k).primesBelow,
        Real.log (q:ℝ)/(q:ℝ))^2
      ≤ (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + 2)^2 := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self hqm0 hqm
  -- non-negativity of the energy factor
  have he1nn : (0:ℝ) ≤ Real.exp 1 - 1 := by linarith [Real.exp_one_gt_d9.le]
  have hA1nn : (0:ℝ) ≤ 4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ))
      * Real.log (x:ℝ) + Real.log 2) + 4 * Real.log 4 := by
    have h1 : (0:ℝ) ≤ (Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ) :=
      mul_nonneg (mul_nonneg he1nn hu0.le) hL0.le
    have h2 := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)
    have h4 := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)
    linarith
  have hE0 : (0:ℝ) ≤ Real.exp π *
      (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
          * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
              + Real.log 2) + 4 * Real.log 4))
        + T * (6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
            * (16/(Real.log (x:ℝ))^2
                + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
      + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
          * (1/(2*Real.pi^2*T)) := by
    have hT0 : (0:ℝ) < T := by linarith
    have hb1 : (0:ℝ) ≤ Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2 := by positivity
    have hb2 : (0:ℝ) ≤ T * (6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
        * (16/(Real.log (x:ℝ))^2
            + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)) := by
      positivity
    have hb3 : (0:ℝ) ≤ (∑ p ∈ P, Real.log (p:ℝ)
        /((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2 * (1/(2*Real.pi^2*T)) := by
      positivity
    have hb4 : (0:ℝ) ≤ 12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
        * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
            + Real.log 2) + 4 * Real.log 4)) := by
      have := mul_nonneg hb1 hA1nn
      nlinarith [this]
    have := mul_nonneg (Real.exp_pos π).le (add_nonneg hb4 hb2)
    linarith
  -- the V-side monotonicity
  have hT0' : (0:ℝ) ≤ T := by linarith
  have hVinner : 12290 * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
        + 4*T*(6144 + Real.exp (-(π*T^2/64))
            * (((x / blockLo x k : ℕ):ℝ) * Real.log 4))
      ≤ 12290 * (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
            + Real.log 2 + 2)
        + 4*T*(6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4)) := by
    have h1 : Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2
        ≤ Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
          + Real.log 2 + 2 := by linarith [hlogX1]
    have h2 : (6144:ℝ) + Real.exp (-(π*T^2/64))
        * (((x / blockLo x k : ℕ):ℝ) * Real.log 4)
        ≤ 6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4) := by
      linarith [hγmono]
    have h3 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 12290)
    have h4 := mul_le_mul_of_nonneg_left h2
      (by positivity : (0:ℝ) ≤ 4*T)
    linarith
  have hVle : 2 * (Real.exp π * (12290
        * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
        + 4*T*(6144 + Real.exp (-(π*T^2/64))
            * (((x / blockLo x k : ℕ):ℝ) * Real.log 4))))
      + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
            (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
          Real.log (q:ℝ)/(q:ℝ))^2
      ≤ 2 * (Real.exp π * (12290
            * (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
              + Real.log 2 + 2)
            + 4*T*(6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))))
        + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
              (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
            Real.log (q:ℝ)/(q:ℝ))^2 := by
    have := mul_le_mul_of_nonneg_left hVinner (Real.exp_pos π).le
    linarith
  -- the tail-mass monotonicity
  have hMtle : (∑ q ∈ (x / blockLo x k).primesBelow,
        Real.log (q:ℝ)/(q:ℝ))^2
      * (∑ n ∈ Finset.Icc 1 x, (1:ℝ)/(n:ℝ))^2
      * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))
      ≤ (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + 2)^2
        * (∑ n ∈ Finset.Icc 1 x, (1:ℝ)/(n:ℝ))^2
        * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2))) := by
    have h1 := mul_le_mul_of_nonneg_right hqm_sq
      (sq_nonneg (∑ n ∈ Finset.Icc 1 x, (1:ℝ)/(n:ℝ)))
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  -- the bracket
  have hbrk : 5 * (2 * (Real.exp π * (12290
        * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
        + 4*T*(6144 + Real.exp (-(π*T^2/64))
            * (((x / blockLo x k : ℕ):ℝ) * Real.log 4))))
      + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
            (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
          Real.log (q:ℝ)/(q:ℝ))^2) * (6*b^2)
      + (∑ q ∈ (x / blockLo x k).primesBelow,
            Real.log (q:ℝ)/(q:ℝ))^2
          * (∑ n ∈ Finset.Icc 1 x, (1:ℝ)/(n:ℝ))^2
          * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))
      ≤ 5 * (2 * (Real.exp π * (12290
            * (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
              + Real.log 2 + 2)
            + 4*T*(6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))))
          + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
                (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
              Real.log (q:ℝ)/(q:ℝ))^2) * (6*b^2)
        + (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + 2)^2
          * (∑ n ∈ Finset.Icc 1 x, (1:ℝ)/(n:ℝ))^2
          * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2))) := by
    have h5 := mul_le_mul_of_nonneg_left hVle (by norm_num : (0:ℝ) ≤ 5)
    have h56 := mul_le_mul_of_nonneg_right h5
      (by positivity : (0:ℝ) ≤ 6*b^2)
    linarith [hMtle]
  -- E-rewrite into the u-form
  have hEeq : Real.exp π *
      (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
          * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
              + Real.log 2) + 4 * Real.log 4))
        + T * (6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
            * (16/(Real.log (x:ℝ))^2
                + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
      + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
          * (1/(2*Real.pi^2*T))
      = Real.exp π * (12290 * (1/((Real.exp (-(k:ℝ)))^2*(Real.log (x:ℝ))^2)
          * (4*(Real.exp 1 - 1)*(Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
            + (4*Real.log 2 + 4*Real.log 4))))
        + Real.exp π * (T * (6144 + Real.exp (-(π*T^2/64))
            * ((x:ℝ) * Real.log 4))
          * (16/(Real.log (x:ℝ))^2
              + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
        + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
            * (1/(2*Real.pi^2*T)) := by
    rw [exp_two_k_div_sq]
    ring
  -- the full argument bound
  have harg : (Real.exp π *
      (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
          * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
              + Real.log 2) + 4 * Real.log 4))
        + T * (6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
            * (16/(Real.log (x:ℝ))^2
                + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
      + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
          * (1/(2*Real.pi^2*T)))
      * (5 * (2 * (Real.exp π * (12290
            * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
            + 4*T*(6144 + Real.exp (-(π*T^2/64))
                * (((x / blockLo x k : ℕ):ℝ) * Real.log 4))))
          + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
                (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
              Real.log (q:ℝ)/(q:ℝ))^2) * (6*b^2)
        + (∑ q ∈ (x / blockLo x k).primesBelow,
              Real.log (q:ℝ)/(q:ℝ))^2
            * (∑ n ∈ Finset.Icc 1 x, (1:ℝ)/(n:ℝ))^2
            * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2))))
      ≤ (Real.exp π)^2 * 10^15
          * (((∑ q ∈ (x / blockLo x k).primesBelow.filter
                (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
              Real.log (q:ℝ)/(q:ℝ))^2 + T + 1) * b^2 + 1) := by
    refine le_trans (mul_le_mul_of_nonneg_left hbrk hE0) ?_
    rw [hEeq]
    exact balance_product_le (Real.log (x:ℝ)) (Real.exp (-(k:ℝ))) T b
      (Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
      (4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2))
      (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))
      (∑ q ∈ (x / blockLo x k).primesBelow.filter
          (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)), Real.log (q:ℝ)/(q:ℝ))
      (∑ n ∈ Finset.Icc 1 x, (1:ℝ)/(n:ℝ))
      (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))
      (block_index_le_of_fit x k hx hfit) hu0 hu1
      (one_le_log_of_three_le x hx3) hT hTL hLT
      (by positivity) hγ1 (by positivity) hSL
      (Finset.sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p)
        (by positivity)) hMp
      (Finset.sum_nonneg fun q _ => div_nonneg (Real.log_natCast_nonneg q)
        (Nat.cast_nonneg q))
      (Finset.sum_nonneg fun n _ => div_nonneg zero_le_one (Nat.cast_nonneg n))
      (by positivity) hW hb0
  have hs := Real.sqrt_le_sqrt harg
  have hxs := mul_le_mul_of_nonneg_left hs hxR0
  linarith

end MoltResearch
