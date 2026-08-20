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

end MoltResearch
