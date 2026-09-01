import MoltResearch.Discrepancy.SmoothRankin
import MoltResearch.Discrepancy.HalaszEuler

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



open MeasureTheory Real Complex Finset in
/-- **The unit-interval energy, split at 64, shell form** (Track R,
budget repair R-b2-a): for `Q` any set of primes `≤ X` and any
frequency `N`,

  `∫_{N−1/2}^{N+1/2}‖P₃(t)‖²
     ≤ 2·e^π·8·(1539·(log(X+1)+2) + 24576)
       + 2·(∑_{q ∈ Q, q < 64} log q/q)²`.

The split threshold is the *absolute* `64 = 8²` of the fixed-width
shell energy, not the free `T²`: the large half goes through
`ghsPrimePoly_unit_energy_shell_le` + `ghsPrime_energy_sum_shell_le`
(T-free), and the small half's Mertens mass runs over the primes below
`64` — an absolute constant, where the `T²`-split's was `≍ 2 log T =`
`≍ log log x` and entered the balance envelope squared against `b²`.
Nothing in this bound depends on `T`, `B`, or the block index. -/
theorem ghsPrimePoly_unit_energy_split_shell_le (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1)
    (Q : Finset ℕ) (X : ℕ) (hX : 2 ≤ X)
    (hQp : ∀ q ∈ Q, q.Prime) (hQX : ∀ q ∈ Q, q ≤ X)
    (hwide : ∀ w : ℕ → ℂ, IntervalIntegrable
      (fun u => ‖∑ q ∈ Q.filter (fun q : ℕ => 64 ≤ q), w q
        * ((Real.fourierChar (-(Real.log (q:ℝ) * u)) : Circle) : ℂ)‖^2)
      volume (-(8:ℝ)) (8:ℝ))
    (N : ℝ) :
    (∫ t in (N - 1/2)..(N + 1/2), ‖ghsPrimePoly f Q t‖^2)
      ≤ 2 * (Real.exp π * 8
            * (1539 * (Real.log ((X+1 : ℕ):ℝ) + 2) + 6144 * 4))
        + 2 * (∑ q ∈ Q.filter (fun q : ℕ => ¬ 64 ≤ q),
            Real.log (q:ℝ)/(q:ℝ))^2 := by
  classical
  set Ql : Finset ℕ := Q.filter (fun q : ℕ => 64 ≤ q) with hQl_def
  set Qs : Finset ℕ := Q.filter (fun q : ℕ => ¬ 64 ≤ q) with hQs_def
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
  have hQl64 : ∀ q ∈ Ql, 64 ≤ q := by
    intro q hq
    rw [hQl_def] at hq
    exact (Finset.mem_filter.mp hq).2
  have hlarge : (∫ t in (N - 1/2)..(N + 1/2), ‖ghsPrimePoly f Ql t‖^2)
      ≤ Real.exp π * 8
          * (1539 * (Real.log ((X+1 : ℕ):ℝ) + 2) + 6144 * 4) := by
    refine le_trans (ghsPrimePoly_unit_energy_shell_le f hf Ql
      hQlp hQl64 hwide N) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact ghsPrime_energy_sum_shell_le Ql X hX hQlp hQlX hQl64
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
/-- **The unit-interval energy at `Q = primesBelow X`, shell form**
(Track R, budget repair R-b2-b): for any `X ≥ 2` and frequency `N`,

  `∫_{N−1/2}^{N+1/2}‖P₃(t)‖² ≤ 2·e^π·8·(1539·(log(X+1)+2) + 24576)
      + 2·(∑_{q<X, q<64} log q/q)²`

— `ghsPrimePoly_unit_energy_split_shell_le` at the concrete inner
range the per-block instantiation feeds, side inputs discharged as in
N181, and nothing left that depends on `T` or a mass budget. -/
theorem ghsPrimePoly_unit_energy_primesBelow_shell_le (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (X : ℕ) (hX : 2 ≤ X) (N : ℝ) :
    (∫ t in (N - 1/2)..(N + 1/2), ‖ghsPrimePoly f X.primesBelow t‖^2)
      ≤ 2 * (Real.exp π * 8
            * (1539 * (Real.log ((X+1 : ℕ):ℝ) + 2) + 6144 * 4))
        + 2 * (∑ q ∈ X.primesBelow.filter (fun q : ℕ => ¬ 64 ≤ q),
            Real.log (q:ℝ)/(q:ℝ))^2 := by
  classical
  refine ghsPrimePoly_unit_energy_split_shell_le f hf X.primesBelow X hX
    (fun q hq => (Nat.mem_primesBelow.mp hq).2)
    (fun q hq => le_of_lt (Nat.mem_primesBelow.mp hq).1)
    (fun w => ((ExpSums.continuous_char_poly
      (X.primesBelow.filter (fun q : ℕ => 64 ≤ q)) w
      (fun q => Real.log (q:ℝ))).norm.pow 2).intervalIntegrable _ _)
    N

open Real Finset in
/-- **The sub-64 prime mass is an absolute constant** (Track R, budget
repair R-b2-b): for any set of primes, `∑_{q < 64} log q/q ≤ 7` —
the small half of the 64-split enters the balance as `2·7² = 98`, an
absolute constant, where the `T²`-split's small mass was
`≍ 2·log T ≍ loglog x` and entered squared against `b²`. -/
theorem small_prime_mass_64_le (Q : Finset ℕ) (hQp : ∀ q ∈ Q, q.Prime) :
    ∑ q ∈ Q.filter (fun q : ℕ => ¬ 64 ≤ q), Real.log (q:ℝ)/(q:ℝ) ≤ 7 := by
  classical
  obtain ⟨h1, -⟩ := prime_masses_le (Q.filter (fun q : ℕ => ¬ 64 ≤ q)) 63
    (by norm_num)
    (fun q hq => hQp q (Finset.mem_filter.mp hq).1)
    (fun q hq => (hQp q (Finset.mem_filter.mp hq).1).two_le)
    (fun q hq => by
      have := (Finset.mem_filter.mp hq).2
      omega)
  refine le_trans h1 ?_
  have h64 : Real.log ((63+1 : ℕ):ℝ) = 6 * Real.log 2 := by
    have hc : ((63+1 : ℕ):ℝ) = (2:ℝ)^(6:ℕ) := by norm_num
    rw [hc, Real.log_pow]
    push_cast
    ring
  rw [h64]
  nlinarith [Real.log_two_lt_d9]

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
    (hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
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



open MeasureTheory Real Complex Finset in
open scoped FourierTransform in
/-- **§3's sharp estimate on a retained block, shell form** (Track R,
budget repair R-b2-b-ii): N183 with the unit-interval energy supplied
by the 64-split shell chain —

  `|tripleConvR f x P| ≤ x·√(E₁·(5·V₃''·6b² + Mtail)) + 2x·log 4`,

with `V₃'' = 2·e^π·8·(1539·(log(X+1)+2) + 24576) + 2·(∑_{q<64} log q/q)²`
at `X = x/blockLo x k` — **no `T` and no block mass anywhere in the
`b²`-coefficient**.  `T` remains only in `E₁`'s own budget, where the
balance is free to take it as large as `log x`.  The `T²`-threshold
small mass (`≍ log log x`, squared, against `b²`) is now the absolute
constant `2·(∑_{q<64} log q/q)² ≤ 98`. -/
theorem tripleConvR_block_sharp_shell_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (x k : ℕ) (hx : 2 ≤ x) (hk : 1 ≤ k) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k)
    (hfit : 2 * blockHi x k ≤ x)
    (hX3 : 3 ≤ x / blockLo x k)
    (T : ℝ) (hT : 5 ≤ T) (hPT : ∀ p ∈ P, T^2 ≤ (p:ℝ))
    (b : ℝ) (hb0 : 0 ≤ b)
    (hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
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
          * (5 * (2 * (Real.exp π * 8
                * (1539 * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
                  + 6144 * 4))
              + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
                    (fun q : ℕ => ¬ 64 ≤ q),
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
  have hV₃0 : (0:ℝ) ≤ 2 * (Real.exp π * 8
        * (1539 * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
          + 6144 * 4))
      + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
            (fun q : ℕ => ¬ 64 ≤ q),
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
      ≤ 2 * (Real.exp π * 8
            * (1539 * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
              + 6144 * 4))
          + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
                (fun q : ℕ => ¬ 64 ≤ q),
              Real.log (q:ℝ)/(q:ℝ))^2 :=
    fun N _ => ghsPrimePoly_unit_energy_primesBelow_shell_le
      (fun n => ((f n : ℝ) : ℂ)) hfc (x / blockLo x k) hX2 (N:ℝ)
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
    (hMp0 : 0 ≤ Mp) (hMp : Mp ≤ 18)
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
  have hEc_le : Mp^2 * (1/(2*Real.pi^2*T)) ≤ 4 := by
    have hMp2 : Mp^2 ≤ 324 := by nlinarith [hMp, hMp0]
    have hinv : 1/(2*Real.pi^2*T) ≤ 1/90 := by
      rw [div_le_div_iff₀ (by nlinarith [hπ2, hT5] : (0:ℝ) < 2*Real.pi^2*T)
        (by norm_num : (0:ℝ) < 90)]
      nlinarith [hπ2, hT5]
    have hinv0 : (0:ℝ) ≤ 1/(2*Real.pi^2*T) := by positivity
    calc Mp^2 * (1/(2*Real.pi^2*T))
        ≤ 324 * (1/(2*Real.pi^2*T)) :=
          mul_le_mul_of_nonneg_right hMp2 hinv0
      _ ≤ 324 * (1/90) :=
          mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ ≤ 4 := by norm_num
  have hPEc_le : P * (Mp^2 * (1/(2*Real.pi^2*T))) ≤ 81 * T := by
    have hMp2 : Mp^2 ≤ 324 := by nlinarith [hMp, hMp0]
    have hden0 : (0:ℝ) < 2*Real.pi^2*T := by nlinarith [hπ2, hT5]
    rw [show P * (Mp^2 * (1/(2*Real.pi^2*T)))
        = P * Mp^2 / (2*Real.pi^2*T) by ring,
      div_le_iff₀ hden0]
    -- `P·Mp² ≤ 324·L ≤ 324·T² ≤ 81·T·(2π²T)` via `L ≤ T²`, `π² ≥ 9`
    have hPMp : P * Mp^2 ≤ 324 * L := by
      nlinarith [hMp2, hP0, hPL, hL0, sq_nonneg Mp]
    nlinarith [hPMp, hLT, hπ2, hT5, hT0, sq_nonneg T]
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
    have hEc17 : Mp^2 * (1/(2*Real.pi^2*T)) ≤ Real.exp π * 17 := by
      nlinarith [hEc_le, heπ]
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
    (hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖ghsMainPoly (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 x) t‖ ≤ b)
    (hTL : T ≤ Real.log (x:ℝ)) (hLT : Real.log (x:ℝ) ≤ T^2)
    (hγ1 : Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4) ≤ 1)
    (hSL : 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)
      * Real.log (x:ℝ) ≤ 1)
    (hMp : ∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|)
      ≤ 18)
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


open Real Finset in
/-- **The band weight absorbs the harmonic mass, unconditionally**
(Track R, N190): for every `x ≥ 2`,

  `(1/(2π²·(halaszM x + ½)))·((log x)²·(∑_{n≤x} 1/n)²) ≤ 1`.

N189's `hW`, discharged with no side condition: the widened band
`halaszM x = ⌈log⁴x⌉ + 1` dominates `log⁴x + 1`, the harmonic sum is
`≤ 1 + log x` (`harmonic_Icc_le`), and `L²(1+L)² ≤ 4(L⁴+1)` for every
`L ≥ 0` — the reason the band was widened to the fourth power in the
first place. -/
theorem bandWeight_mass_le_one (x : ℕ) (hx : 2 ≤ x) :
    (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))
      * ((Real.log (x:ℝ))^2
        * (∑ n ∈ Finset.Icc 1 x, (1:ℝ)/(n:ℝ))^2) ≤ 1 := by
  have hL0 : (0:ℝ) < Real.log (x:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 2 ≤ x))
  have hHS0 : (0:ℝ) ≤ ∑ n ∈ Finset.Icc 1 x, (1:ℝ)/(n:ℝ) :=
    Finset.sum_nonneg fun n _ => div_nonneg zero_le_one (Nat.cast_nonneg n)
  have hH := harmonic_Icc_le x (by omega)
  have hπ2 : (9:ℝ) ≤ Real.pi^2 := by
    have := Real.pi_gt_three
    nlinarith
  -- the band dominates `L⁴ + 1`
  have hM : (Real.log (x:ℝ))^4 + 1 ≤ ((halaszM x : ℕ):ℝ) := by
    have h4 : (0:ℝ) ≤ (Real.log (x:ℝ))^4 := by positivity
    have hle := Int.le_ceil ((Real.log (x:ℝ))^4)
    have hnn : (0:ℤ) ≤ ⌈(Real.log (x:ℝ))^4⌉ + 1 := by
      have := Int.ceil_nonneg h4
      omega
    calc (Real.log (x:ℝ))^4 + 1
        ≤ ((⌈(Real.log (x:ℝ))^4⌉ : ℤ):ℝ) + 1 := by
          push_cast
          linarith
      _ = ((⌈(Real.log (x:ℝ))^4⌉ + 1 : ℤ):ℝ) := by push_cast; ring
      _ = (((⌈(Real.log (x:ℝ))^4⌉ + 1).toNat : ℕ):ℝ) := by
          rw [show ((((⌈(Real.log (x:ℝ))^4⌉ + 1).toNat : ℕ)):ℝ)
              = ((((⌈(Real.log (x:ℝ))^4⌉ + 1).toNat : ℕ) : ℤ):ℝ) by push_cast; ring,
            Int.toNat_of_nonneg hnn]
      _ = ((halaszM x : ℕ):ℝ) := by rw [halaszM]
  -- numerator against `4(L⁴+1)`
  have hsq : (∑ n ∈ Finset.Icc 1 x, (1:ℝ)/(n:ℝ))^2
      ≤ (1 + Real.log (x:ℝ))^2 := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self hHS0 hH
  have hnum : (Real.log (x:ℝ))^2
      * (∑ n ∈ Finset.Icc 1 x, (1:ℝ)/(n:ℝ))^2
      ≤ 4 * ((Real.log (x:ℝ))^4 + 1) := by
    have h1 := mul_le_mul_of_nonneg_left hsq (sq_nonneg (Real.log (x:ℝ)))
    have h2 : (Real.log (x:ℝ))^2 * (1 + Real.log (x:ℝ))^2
        ≤ 4 * ((Real.log (x:ℝ))^4 + 1) := by
      nlinarith [sq_nonneg (Real.log (x:ℝ)), hL0,
        sq_nonneg ((Real.log (x:ℝ))^2 - Real.log (x:ℝ)),
        sq_nonneg ((Real.log (x:ℝ))^2 - 1),
        sq_nonneg (Real.log (x:ℝ) - 1)]
    linarith
  -- denominator dominates
  have hden0 : (0:ℝ) < 2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2) := by
    have : (0:ℝ) ≤ ((halaszM x : ℕ):ℝ) := Nat.cast_nonneg _
    nlinarith [hπ2]
  rw [show (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))
      * ((Real.log (x:ℝ))^2
        * (∑ n ∈ Finset.Icc 1 x, (1:ℝ)/(n:ℝ))^2)
      = ((Real.log (x:ℝ))^2
        * (∑ n ∈ Finset.Icc 1 x, (1:ℝ)/(n:ℝ))^2)
        / (2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)) by ring,
    div_le_one hden0]
  have hfin : 4 * ((Real.log (x:ℝ))^4 + 1)
      ≤ 2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2) := by
    nlinarith [hπ2, hM, (show (0:ℝ) ≤ ((halaszM x : ℕ):ℝ) from Nat.cast_nonneg _), pow_nonneg hL0.le 4]
  linarith


open Real in
/-- **The Gaussian damping wins past the threshold** (Track R, N191):
if `(64/π)·log(x·log 4) ≤ T²` then `e^{−πT²/64}·x·log 4 ≤ 1` — N189's
`hγ1`, reduced to a lower bound on the Gaussian width.  At the campaign
`T ≍ 4.5·√(log x)` the hypothesis reads `T² ≳ 20.4·log x`, which is
where the constant `4.5 > √(64/π)/√{≈}` comes from. -/
theorem gamma_le_one_of (x : ℕ) (T : ℝ) (hx : 2 ≤ x)
    (hT : (64/π) * Real.log ((x:ℝ) * Real.log 4) ≤ T^2) :
    Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4) ≤ 1 := by
  have hπ0 : (0:ℝ) < π := Real.pi_pos
  have hA0 : (0:ℝ) < (x:ℝ) * Real.log 4 := by
    have hx0 : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
    have h4 : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    positivity
  -- `log A ≤ πT²/64` from the hypothesis
  have hlogA : Real.log ((x:ℝ) * Real.log 4) ≤ π*T^2/64 := by
    have h := mul_le_mul_of_nonneg_left hT (by positivity : (0:ℝ) ≤ π/64)
    calc Real.log ((x:ℝ) * Real.log 4)
        = (π/64) * ((64/π) * Real.log ((x:ℝ) * Real.log 4)) := by
          field_simp
      _ ≤ (π/64) * T^2 := h
      _ = π*T^2/64 := by ring
  -- so `A ≤ e^{πT²/64}`, i.e. the damping is at least `1/A`
  have hAexp : (x:ℝ) * Real.log 4 ≤ Real.exp (π*T^2/64) :=
    (Real.log_le_iff_le_exp hA0).mp hlogA
  calc Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4)
      ≤ Real.exp (-(π*T^2/64)) * Real.exp (π*T^2/64) :=
        mul_le_mul_of_nonneg_left hAexp (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp


open Real Finset in
/-- **The survivor-block mass is at most 18** (Track R, N193): for `P`
inside block `k`, one step short of the boundary
(`e·log 2 ≤ e^{−k}·log x`),

  `∑_{p ∈ P} log p/(p·|log(x/p)|) ≤ 18`.

N192's `hMp`, discharged.  Every `p < blockHi = ⌈x^{1−u}⌉` has
`log(x/p) ≥ u·log x − log 2 > 0`, the block Mertens mass is
`≤ 4((e−1)·u·log x + log 2) + 4·log 4` (`sum_log_div_Ico_le_log` +
`log_blockHi_sub_log_blockLo_le`), and the quotient closes at
`(22−4e)·e ≥ 30` — under one percent to spare, so `18` is honest.
The boundary block fails the hypothesis and goes to the geometric
tail, which is free. -/
theorem blockMass_le_const (x k : ℕ) (hx : 2 ≤ x) (hk : 1 ≤ k)
    (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k)
    (huL : Real.exp 1 * Real.log 2
      ≤ Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) :
    ∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|) ≤ 18 := by
  classical
  have hx1 : 1 ≤ x := by omega
  obtain ⟨hlo1, hlohi⟩ := blockLo_le_blockHi x k hx1
  have hxR : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx1
  have hx0 : (0:ℝ) < (x:ℝ) := by linarith
  have hL0 : (0:ℝ) < Real.log (x:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 2 ≤ x))
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hu0 : (0:ℝ) < Real.exp (-(k:ℝ)) := Real.exp_pos _
  have hu1 : Real.exp (-(k:ℝ)) ≤ 1 := by
    rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (Nat.cast_nonneg k))
  have he_lt : Real.exp 1 ≤ (2.7182818286:ℝ) := Real.exp_one_lt_d9.le
  have he_gt : (2.7182818283:ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
  have hgap0 : (0:ℝ) < Real.exp (-(k:ℝ)) * Real.log (x:ℝ) - Real.log 2 := by
    have h1 : Real.log 2 < Real.exp 1 * Real.log 2 := by
      nlinarith [he_gt, hlog2]
    linarith [huL]
  -- the denominator floor on the block
  have hden : ∀ p ∈ P, Real.exp (-(k:ℝ)) * Real.log (x:ℝ) - Real.log 2
      ≤ Real.log ((x:ℝ)/(p:ℝ)) := by
    intro p hp
    obtain ⟨hpp, -, hpB⟩ := hP p hp
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
    rw [Real.log_div (ne_of_gt hx0) (ne_of_gt hp0)]
    -- `log p ≤ log 2 + (1−u)·log x`
    have hexp0 : (0:ℝ) ≤ 1 - Real.exp (-(k:ℝ)) := by linarith
    have hpow1 : (1:ℝ) ≤ (x:ℝ) ^ (1 - Real.exp (-(k:ℝ))) := by
      have h := Real.rpow_le_rpow_of_exponent_le hxR hexp0
      rwa [Real.rpow_zero] at h
    have hceil : ((blockHi x k : ℕ):ℝ)
        ≤ 2 * (x:ℝ) ^ (1 - Real.exp (-(k:ℝ))) := by
      rw [blockHi]
      have h1 := Nat.ceil_lt_add_one
        (by positivity : (0:ℝ) ≤ (x:ℝ) ^ (1 - Real.exp (-(k:ℝ))))
      linarith [hpow1, h1.le]
    have hlogp : Real.log (p:ℝ)
        ≤ Real.log 2 + (1 - Real.exp (-(k:ℝ))) * Real.log (x:ℝ) := by
      have hpB' : (p:ℝ) ≤ 2 * (x:ℝ) ^ (1 - Real.exp (-(k:ℝ))) := by
        have h1 : (p:ℝ) ≤ ((blockHi x k : ℕ):ℝ) := by
          exact_mod_cast Nat.le_of_lt hpB
        linarith [hceil]
      calc Real.log (p:ℝ)
          ≤ Real.log (2 * (x:ℝ) ^ (1 - Real.exp (-(k:ℝ)))) :=
            Real.log_le_log hp0 hpB'
        _ = Real.log 2 + (1 - Real.exp (-(k:ℝ))) * Real.log (x:ℝ) := by
            rw [Real.log_mul (by norm_num)
              (ne_of_gt (Real.rpow_pos_of_pos hx0 _)),
              Real.log_rpow hx0]
    linarith
  -- termwise: pull the denominator floor out
  have hterm : ∀ p ∈ P,
      Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|)
      ≤ (Real.log (p:ℝ)/(p:ℝ))
        * (1/(Real.exp (-(k:ℝ)) * Real.log (x:ℝ) - Real.log 2)) := by
    intro p hp
    obtain ⟨hpp, -, -⟩ := hP p hp
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
    have hlp : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
    have hd := hden p hp
    have habs : |Real.log ((x:ℝ)/(p:ℝ))| = Real.log ((x:ℝ)/(p:ℝ)) :=
      abs_of_nonneg (le_trans hgap0.le hd)
    rw [habs]
    have h1 : 1/Real.log ((x:ℝ)/(p:ℝ))
        ≤ 1/(Real.exp (-(k:ℝ)) * Real.log (x:ℝ) - Real.log 2) :=
      one_div_le_one_div_of_le hgap0 hd
    calc Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ)))
        = (Real.log (p:ℝ)/(p:ℝ)) * (1/Real.log ((x:ℝ)/(p:ℝ))) := by
          rw [div_mul_eq_div_div, div_eq_mul_one_div]
      _ ≤ (Real.log (p:ℝ)/(p:ℝ))
          * (1/(Real.exp (-(k:ℝ)) * Real.log (x:ℝ) - Real.log 2)) :=
          mul_le_mul_of_nonneg_left h1 (div_nonneg hlp hp0.le)
  -- the block Mertens mass
  have hsub : P ⊆ (Finset.Ico (blockLo x k) (blockHi x k)).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpp, hlop, hpB⟩ := hP p hp
    rw [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨hlop, hpB⟩, hpp⟩
  have hmass : ∑ p ∈ P, Real.log (p:ℝ)/(p:ℝ)
      ≤ 4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
          + Real.log 2) + 4 * Real.log 4 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p _ _ => div_nonneg (Real.log_natCast_nonneg p)
        (Nat.cast_nonneg p))) ?_
    refine le_trans (sum_log_div_Ico_le_log (blockLo x k) (blockHi x k)
      hlo1 hlohi) ?_
    have hwidth := log_blockHi_sub_log_blockLo_le x k hx hk
    linarith
  -- assemble and close numerically
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul] at hsum
  refine le_trans hsum ?_
  have hnn : (0:ℝ) ≤ ∑ p ∈ P, Real.log (p:ℝ)/(p:ℝ) :=
    Finset.sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p)
      (Nat.cast_nonneg p)
  have hstep : (∑ p ∈ P, Real.log (p:ℝ)/(p:ℝ))
      * (1/(Real.exp (-(k:ℝ)) * Real.log (x:ℝ) - Real.log 2))
      ≤ (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
          + Real.log 2) + 4 * Real.log 4)
        * (1/(Real.exp (-(k:ℝ)) * Real.log (x:ℝ) - Real.log 2)) :=
    mul_le_mul_of_nonneg_right hmass (by positivity)
  refine le_trans hstep ?_
  rw [mul_one_div, div_le_iff₀ hgap0]
  -- `4(e−1)uL + 12·log2 ≤ 18·(uL − log2)` from `uL ≥ e·log2`, `(22−4e)e ≥ 30`
  rw [hlog4]
  have hcoef : (0:ℝ) < 22 - 4*Real.exp 1 := by nlinarith [he_lt]
  have h1 : (22 - 4*Real.exp 1)
      * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
      ≥ (22 - 4*Real.exp 1) * (Real.exp 1 * Real.log 2) :=
    mul_le_mul_of_nonneg_left huL hcoef.le
  have h2 : (22 - 4*Real.exp 1) * (Real.exp 1 * Real.log 2)
      ≥ 30 * Real.log 2 := by
    have he2 : (22 - 4*Real.exp 1) * Real.exp 1 ≥ 30 := by
      nlinarith [he_gt, he_lt]
    nlinarith [he2, hlog2]
  nlinarith [h1, h2]


open Real in
/-- **The fourth-root tail beats the logarithm** (Track R, N194): for
`x ≥ 10¹⁶`,

  `(4/(√⌊√x⌋·log²2))·log x ≤ 1`,

N189's `hSL`.  The route: `log x ≤ 8·x^{1/8}` (the log-linear bound at
the eighth root), `⌊√x⌋ ≥ √x/2`, so `√⌊√x⌋ ≥ x^{1/4}/√2`, and at
`x ≥ 10¹⁶` the exact `x^{1/8} ≥ 100` closes `32·x^{1/8} ≤
(log²2/√2)·x^{1/4}` with six percent to spare.  A large-`x` statement,
as the asymptotic interface permits. -/
theorem tailS_mul_log_le_one (x : ℕ) (hx : 10^16 ≤ x) :
    4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)
      * Real.log (x:ℝ) ≤ 1 := by
  have hx2 : (2:ℕ) ≤ x := le_trans (by norm_num) hx
  have hx0 : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hxR : (10:ℝ)^16 ≤ (x:ℝ) := by exact_mod_cast hx
  have hL0 : (0:ℝ) < Real.log (x:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 2 ≤ x))
  have hlog2 : (0.693:ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  -- `x^{1/8} ≥ 100`, exactly at the threshold
  have h8 : (100:ℝ) ≤ (x:ℝ) ^ ((1:ℝ)/8) := by
    have h1 : ((10:ℝ)^16) ^ ((1:ℝ)/8) ≤ (x:ℝ) ^ ((1:ℝ)/8) :=
      Real.rpow_le_rpow (by positivity) hxR (by norm_num)
    have h2 : ((10:ℝ)^16) ^ ((1:ℝ)/8) = 100 := by
      rw [← Real.rpow_natCast (10:ℝ) 16, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith
  have h80 : (0:ℝ) < (x:ℝ) ^ ((1:ℝ)/8) := Real.rpow_pos_of_pos hx0 _
  -- `log x ≤ 8·x^{1/8}`
  have hlogx : Real.log (x:ℝ) ≤ 8 * (x:ℝ) ^ ((1:ℝ)/8) := by
    have h1 : Real.log ((x:ℝ) ^ ((1:ℝ)/8)) = (1/8) * Real.log (x:ℝ) :=
      Real.log_rpow hx0 _
    have h2 : Real.log ((x:ℝ) ^ ((1:ℝ)/8)) ≤ (x:ℝ) ^ ((1:ℝ)/8) - 1 :=
      Real.log_le_sub_one_of_pos h80
    nlinarith [h1, h2, h80]
  -- `⌊√x⌋ ≥ √x/2`
  have hs2 : (2:ℝ) ≤ Real.sqrt (x:ℝ) := by
    have h4 : (4:ℝ) ≤ (x:ℝ) := by nlinarith [hxR]
    have := Real.sqrt_le_sqrt h4
    rwa [show Real.sqrt 4 = 2 by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
  have hfloor : Real.sqrt (x:ℝ)/2 ≤ ((Nat.sqrt x : ℕ):ℝ) := by
    have h1 : x < (Nat.sqrt x + 1)^2 := Nat.lt_succ_sqrt' x
    have h2 : (x:ℝ) < (((Nat.sqrt x + 1):ℕ):ℝ)^2 := by exact_mod_cast h1
    have h3 : Real.sqrt (x:ℝ) < ((Nat.sqrt x : ℕ):ℝ) + 1 := by
      have h4 : Real.sqrt (x:ℝ) < Real.sqrt ((((Nat.sqrt x + 1):ℕ):ℝ)^2) :=
        Real.sqrt_lt_sqrt (Nat.cast_nonneg x) h2
      rwa [Real.sqrt_sq (by positivity), Nat.cast_add, Nat.cast_one] at h4
    linarith [hs2]
  -- `√⌊√x⌋ ≥ x^{1/4}/√2`
  have hsq2 : Real.sqrt 2 ≤ 1.415 := by
    have h1 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2, h1]
  have hsq20 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hquarter : Real.sqrt (Real.sqrt (x:ℝ)) = (x:ℝ) ^ ((1:ℝ)/4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
    norm_num
  have hroot : (x:ℝ) ^ ((1:ℝ)/4) / Real.sqrt 2
      ≤ Real.sqrt ((Nat.sqrt x : ℕ):ℝ) := by
    have h1 : Real.sqrt (Real.sqrt (x:ℝ)/2)
        ≤ Real.sqrt ((Nat.sqrt x : ℕ):ℝ) := Real.sqrt_le_sqrt hfloor
    rwa [show Real.sqrt (Real.sqrt (x:ℝ)/2)
        = Real.sqrt (Real.sqrt (x:ℝ))/Real.sqrt 2 from
      Real.sqrt_div (Real.sqrt_nonneg _) 2, hquarter] at h1
  -- assemble: `4·log x ≤ √⌊√x⌋·log²2`
  have hA0 : (0:ℝ) < Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2 := by
    have := lt_of_lt_of_le (by positivity : (0:ℝ) < (x:ℝ)^((1:ℝ)/4)/Real.sqrt 2)
      hroot
    positivity
  rw [div_mul_eq_mul_div, div_le_one hA0]
  -- `x^{1/4} = x^{1/8}·x^{1/8}`
  have hquarter8 : (x:ℝ) ^ ((1:ℝ)/4)
      = (x:ℝ) ^ ((1:ℝ)/8) * (x:ℝ) ^ ((1:ℝ)/8) := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hkey : 32 * (x:ℝ) ^ ((1:ℝ)/8)
      ≤ Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2 := by
    have h1 : (x:ℝ) ^ ((1:ℝ)/4) / Real.sqrt 2 * (Real.log 2)^2
        ≤ Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2 :=
      mul_le_mul_of_nonneg_right hroot (sq_nonneg _)
    refine le_trans ?_ h1
    rw [hquarter8, div_mul_eq_mul_div, le_div_iff₀ hsq20]
    -- `32·x^{1/8}·√2 ≤ x^{1/8}·x^{1/8}·log²2`, stepwise
    have hlog2sq : (0.48:ℝ) ≤ (Real.log 2)^2 := by nlinarith [hlog2]
    calc 32 * (x:ℝ)^((1:ℝ)/8) * Real.sqrt 2
        ≤ 32 * (x:ℝ)^((1:ℝ)/8) * 1.415 :=
          mul_le_mul_of_nonneg_left hsq2 (by positivity)
      _ ≤ 0.48 * (100 * (x:ℝ)^((1:ℝ)/8)) := by nlinarith [h80]
      _ ≤ 0.48 * ((x:ℝ)^((1:ℝ)/8) * (x:ℝ)^((1:ℝ)/8)) := by
          have h100 := mul_le_mul_of_nonneg_right h8 h80.le
          nlinarith [h100]
      _ ≤ (x:ℝ)^((1:ℝ)/8) * (x:ℝ)^((1:ℝ)/8) * (Real.log 2)^2 := by
          nlinarith [hlog2sq, mul_nonneg h80.le h80.le]
  linarith [hlogx, hkey]



set_option maxHeartbeats 1600000 in
open Real in
/-- **The sharp small-`S` bound** (Track R, budget repair R-b2-e): the
tail scale beats the *square* of the logarithm,

  `4/(√⌊√x⌋·log²2)·(log x)² ≤ 32`

for `x ≥ 10¹⁶` — the hypothesis shape the rebuilt balance's
`S·L² ≤ 32` slot wants.  Where `tailS_mul_log_le_one` paid one
logarithm via `log x ≤ 8·x^{1/8}`, here `log x ≤ 16·x^{1/16}` squares
to `256·x^{1/8}` against the same `√⌊√x⌋·log²2 ≥ 32·x^{1/8}` floor,
and `4·256 = 32·32` exactly. -/
theorem tailS_mul_log_sq_le (x : ℕ) (hx : 10^16 ≤ x) :
    4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)
      * (Real.log (x:ℝ))^2 ≤ 32 := by
  have hx2 : (2:ℕ) ≤ x := le_trans (by norm_num) hx
  have hx0 : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hxR : (10:ℝ)^16 ≤ (x:ℝ) := by exact_mod_cast hx
  have hL0 : (0:ℝ) < Real.log (x:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 2 ≤ x))
  have hlog2 : (0.693:ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  -- `x^{1/8} ≥ 100`, exactly at the threshold
  have h8 : (100:ℝ) ≤ (x:ℝ) ^ ((1:ℝ)/8) := by
    have h1 : ((10:ℝ)^16) ^ ((1:ℝ)/8) ≤ (x:ℝ) ^ ((1:ℝ)/8) :=
      Real.rpow_le_rpow (by positivity) hxR (by norm_num)
    have h2 : ((10:ℝ)^16) ^ ((1:ℝ)/8) = 100 := by
      rw [← Real.rpow_natCast (10:ℝ) 16, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith
  have h80 : (0:ℝ) < (x:ℝ) ^ ((1:ℝ)/8) := Real.rpow_pos_of_pos hx0 _
  -- `log x ≤ 8·x^{1/8}`
  have hlogx : Real.log (x:ℝ) ≤ 8 * (x:ℝ) ^ ((1:ℝ)/8) := by
    have h1 : Real.log ((x:ℝ) ^ ((1:ℝ)/8)) = (1/8) * Real.log (x:ℝ) :=
      Real.log_rpow hx0 _
    have h2 : Real.log ((x:ℝ) ^ ((1:ℝ)/8)) ≤ (x:ℝ) ^ ((1:ℝ)/8) - 1 :=
      Real.log_le_sub_one_of_pos h80
    nlinarith [h1, h2, h80]
  -- the `1/16`-power pieces for the squared logarithm
  have h16 : (10:ℝ) ≤ (x:ℝ) ^ ((1:ℝ)/16) := by
    have h1 : ((10:ℝ)^16) ^ ((1:ℝ)/16) ≤ (x:ℝ) ^ ((1:ℝ)/16) :=
      Real.rpow_le_rpow (by positivity) hxR (by norm_num)
    have h2 : ((10:ℝ)^16) ^ ((1:ℝ)/16) = 10 := by
      rw [← Real.rpow_natCast (10:ℝ) 16, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith
  have h160 : (0:ℝ) < (x:ℝ) ^ ((1:ℝ)/16) := Real.rpow_pos_of_pos hx0 _
  have hlogx16 : Real.log (x:ℝ) ≤ 16 * (x:ℝ) ^ ((1:ℝ)/16) := by
    have h1 : Real.log ((x:ℝ) ^ ((1:ℝ)/16)) = (1/16) * Real.log (x:ℝ) :=
      Real.log_rpow hx0 _
    have h2 : Real.log ((x:ℝ) ^ ((1:ℝ)/16)) ≤ (x:ℝ) ^ ((1:ℝ)/16) - 1 :=
      Real.log_le_sub_one_of_pos h160
    nlinarith [h1, h2, h160]
  have heighth : (x:ℝ) ^ ((1:ℝ)/8)
      = (x:ℝ) ^ ((1:ℝ)/16) * (x:ℝ) ^ ((1:ℝ)/16) := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hsq16 : (Real.log (x:ℝ))^2 ≤ 256 * (x:ℝ) ^ ((1:ℝ)/8) := by
    rw [heighth]
    nlinarith [hlogx16, hL0.le, h160]
  -- `⌊√x⌋ ≥ √x/2`
  have hs2 : (2:ℝ) ≤ Real.sqrt (x:ℝ) := by
    have h4 : (4:ℝ) ≤ (x:ℝ) := by nlinarith [hxR]
    have := Real.sqrt_le_sqrt h4
    rwa [show Real.sqrt 4 = 2 by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
  have hfloor : Real.sqrt (x:ℝ)/2 ≤ ((Nat.sqrt x : ℕ):ℝ) := by
    have h1 : x < (Nat.sqrt x + 1)^2 := Nat.lt_succ_sqrt' x
    have h2 : (x:ℝ) < (((Nat.sqrt x + 1):ℕ):ℝ)^2 := by exact_mod_cast h1
    have h3 : Real.sqrt (x:ℝ) < ((Nat.sqrt x : ℕ):ℝ) + 1 := by
      have h4 : Real.sqrt (x:ℝ) < Real.sqrt ((((Nat.sqrt x + 1):ℕ):ℝ)^2) :=
        Real.sqrt_lt_sqrt (Nat.cast_nonneg x) h2
      rwa [Real.sqrt_sq (by positivity), Nat.cast_add, Nat.cast_one] at h4
    linarith [hs2]
  -- `√⌊√x⌋ ≥ x^{1/4}/√2`
  have hsq2 : Real.sqrt 2 ≤ 1.415 := by
    have h1 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2, h1]
  have hsq20 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hquarter : Real.sqrt (Real.sqrt (x:ℝ)) = (x:ℝ) ^ ((1:ℝ)/4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
    norm_num
  have hroot : (x:ℝ) ^ ((1:ℝ)/4) / Real.sqrt 2
      ≤ Real.sqrt ((Nat.sqrt x : ℕ):ℝ) := by
    have h1 : Real.sqrt (Real.sqrt (x:ℝ)/2)
        ≤ Real.sqrt ((Nat.sqrt x : ℕ):ℝ) := Real.sqrt_le_sqrt hfloor
    rwa [show Real.sqrt (Real.sqrt (x:ℝ)/2)
        = Real.sqrt (Real.sqrt (x:ℝ))/Real.sqrt 2 from
      Real.sqrt_div (Real.sqrt_nonneg _) 2, hquarter] at h1
  -- assemble: `4·log x ≤ √⌊√x⌋·log²2`
  have hA0 : (0:ℝ) < Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2 := by
    have := lt_of_lt_of_le (by positivity : (0:ℝ) < (x:ℝ)^((1:ℝ)/4)/Real.sqrt 2)
      hroot
    positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hA0]
  -- `x^{1/4} = x^{1/8}·x^{1/8}`
  have hquarter8 : (x:ℝ) ^ ((1:ℝ)/4)
      = (x:ℝ) ^ ((1:ℝ)/8) * (x:ℝ) ^ ((1:ℝ)/8) := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hkey : 32 * (x:ℝ) ^ ((1:ℝ)/8)
      ≤ Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2 := by
    have h1 : (x:ℝ) ^ ((1:ℝ)/4) / Real.sqrt 2 * (Real.log 2)^2
        ≤ Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2 :=
      mul_le_mul_of_nonneg_right hroot (sq_nonneg _)
    refine le_trans ?_ h1
    rw [hquarter8, div_mul_eq_mul_div, le_div_iff₀ hsq20]
    -- `32·x^{1/8}·√2 ≤ x^{1/8}·x^{1/8}·log²2`, stepwise
    have hlog2sq : (0.48:ℝ) ≤ (Real.log 2)^2 := by nlinarith [hlog2]
    calc 32 * (x:ℝ)^((1:ℝ)/8) * Real.sqrt 2
        ≤ 32 * (x:ℝ)^((1:ℝ)/8) * 1.415 :=
          mul_le_mul_of_nonneg_left hsq2 (by positivity)
      _ ≤ 0.48 * (100 * (x:ℝ)^((1:ℝ)/8)) := by nlinarith [h80]
      _ ≤ 0.48 * ((x:ℝ)^((1:ℝ)/8) * (x:ℝ)^((1:ℝ)/8)) := by
          have h100 := mul_le_mul_of_nonneg_right h8 h80.le
          nlinarith [h100]
      _ ≤ (x:ℝ)^((1:ℝ)/8) * (x:ℝ)^((1:ℝ)/8) * (Real.log 2)^2 := by
          nlinarith [hlog2sq, mul_nonneg h80.le h80.le]
  nlinarith [hsq16, hkey, Real.rpow_pos_of_pos hx0 ((1:ℝ)/8)]

open Real in
/-- **The Gaussian window** (Track R, N195): for `x ≥ 10¹⁶` and any
`T` in the window `√(21·log x) ≤ T ≤ log x`, the three scalar side
conditions of N189 hold at once:

  `5 ≤ T`, `log x ≤ T²`, and `(64/π)·log(x·log 4) ≤ T²`.

The window is nonempty (`21·L ≤ L²` at `L ≥ 32`), and its lower edge
is exactly the Gaussian threshold of N191 with one unit of slack:
`(64/π)·(L + log log 4) ≤ 20.38·L + 8 ≤ 21·L`. -/
theorem T_window_conditions (x : ℕ) (T : ℝ) (hx : 10^16 ≤ x)
    (hT1 : Real.sqrt (21 * Real.log (x:ℝ)) ≤ T)
    (hT2 : T ≤ Real.log (x:ℝ)) :
    5 ≤ T ∧ Real.log (x:ℝ) ≤ T^2
      ∧ (64/π) * Real.log ((x:ℝ) * Real.log 4) ≤ T^2 := by
  have hx0 : (0:ℝ) < (x:ℝ) := by
    have : (0:ℕ) < x := by
      calc 0 < 10^16 := by norm_num
        _ ≤ x := hx
    exact_mod_cast this
  have hxR : (10:ℝ)^16 ≤ (x:ℝ) := by exact_mod_cast hx
  have he_lt : Real.exp 1 ≤ (2.7182818286:ℝ) := Real.exp_one_lt_d9.le
  -- `L ≥ 32` from `log 10 ≥ 2` (i.e. `e² ≤ 10`)
  have hL32 : (32:ℝ) ≤ Real.log (x:ℝ) := by
    have hlog10 : (2:ℝ) ≤ Real.log 10 := by
      have h1 : Real.exp 2 ≤ 10 := by
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos 1, he_lt]
      calc (2:ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
        _ ≤ Real.log 10 := Real.log_le_log (Real.exp_pos 2) h1
    have h1 : Real.log ((10:ℝ)^16) = 16 * Real.log 10 := by
      rw [Real.log_pow]
      push_cast
      ring
    have h2 : Real.log ((10:ℝ)^16) ≤ Real.log (x:ℝ) :=
      Real.log_le_log (by positivity) hxR
    nlinarith [hlog10]
  have hL0 : (0:ℝ) < Real.log (x:ℝ) := by linarith
  -- `T² ≥ 21·L` from the window's lower edge
  have hT0 : (0:ℝ) ≤ T := le_trans (Real.sqrt_nonneg _) hT1
  have hTsq : 21 * Real.log (x:ℝ) ≤ T^2 := by
    have h1 : (0:ℝ) ≤ 21 * Real.log (x:ℝ) := by linarith
    have h2 := Real.sq_sqrt h1
    have h3 := mul_self_le_mul_self (Real.sqrt_nonneg (21 * Real.log (x:ℝ))) hT1
    calc 21 * Real.log (x:ℝ)
        = Real.sqrt (21 * Real.log (x:ℝ))^2 := h2.symm
      _ = Real.sqrt (21 * Real.log (x:ℝ))
          * Real.sqrt (21 * Real.log (x:ℝ)) := by ring
      _ ≤ T * T := h3
      _ = T^2 := by ring
  refine ⟨?_, ?_, ?_⟩
  · -- `5 ≤ T` from `T² ≥ 21·32`
    nlinarith [hTsq, hL32, hT0]
  · -- `L ≤ 21·L ≤ T²`
    linarith [hTsq, hL0]
  · -- the Gaussian threshold with slack
    have hlog4u : Real.log 4 ≤ (1.39:ℝ) := by
      have := Real.log_two_lt_d9
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
        push_cast
        ring
      linarith [h4]
    have hlog4l : (1:ℝ) ≤ Real.log 4 := by
      have := Real.log_two_gt_d9
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
        push_cast
        ring
      linarith [h4]
    have hll4 : Real.log (Real.log 4) ≤ 0.39 := by
      have h1 : Real.log (Real.log 4) ≤ Real.log 4 - 1 :=
        Real.log_le_sub_one_of_pos (by linarith)
      linarith
    have hsplit : Real.log ((x:ℝ) * Real.log 4)
        = Real.log (x:ℝ) + Real.log (Real.log 4) :=
      Real.log_mul (ne_of_gt hx0) (by linarith)
    have hπ : (3.1415:ℝ) ≤ π := Real.pi_gt_d4.le
    have hπ0 : (0:ℝ) < π := Real.pi_pos
    -- `(64/π)·(L + 0.39) ≤ 20.38·L + 8 ≤ 21·L ≤ T²`
    have h64π : 64/π ≤ 20.38 := by
      rw [div_le_iff₀ hπ0]
      nlinarith [hπ]
    have harg : Real.log ((x:ℝ) * Real.log 4) ≤ Real.log (x:ℝ) + 0.39 := by
      rw [hsplit]
      linarith [hll4]
    have harg0 : (0:ℝ) ≤ Real.log ((x:ℝ) * Real.log 4) := by
      rw [hsplit]
      have : (0:ℝ) ≤ Real.log (Real.log 4) :=
        Real.log_nonneg (by linarith)
      linarith
    calc (64/π) * Real.log ((x:ℝ) * Real.log 4)
        ≤ 20.38 * Real.log ((x:ℝ) * Real.log 4) :=
          mul_le_mul_of_nonneg_right h64π harg0
      _ ≤ 20.38 * (Real.log (x:ℝ) + 0.39) :=
          mul_le_mul_of_nonneg_left harg (by norm_num)
      _ ≤ 21 * Real.log (x:ℝ) := by nlinarith [hL32]
      _ ≤ T^2 := hTsq


open Real Finset in
/-- **The block mass bound, fit-free** (Track R, N197): `Sk_trivial_mass_le'`
with the per-element `2p ≤ x` the survivors carry, in place of the block-level
`2B ≤ x` — which the split's covering block can never satisfy. -/
private theorem Sk_trivial_mass_le'' (x A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ A ≤ p ∧ p < B)
    (h2P : ∀ p ∈ P, 2*p ≤ x) :
    ∑ p ∈ P, (Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
        * (∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ))
      ≤ 16 * (Real.log (B:ℝ) - Real.log (A:ℝ)) + 16 * Real.log 4 := by
  classical
  have hterm : ∀ p ∈ P,
      (Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
          * (∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ))
        ≤ 4 * (Real.log (p:ℝ)/(p:ℝ)) := by
    intro p hp
    obtain ⟨hpp, hAp, hpB⟩ := hP p hp
    have hp1 : 1 ≤ p := hpp.one_lt.le
    exact inner_mertens_cancel x p hp1 (h2P p hp)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  -- the index set embeds in the full block
  have hsub : P ⊆ (Finset.Ico A B).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpp, hAp, hpB⟩ := hP p hp
    simp only [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨hAp, hpB⟩, hpp⟩
  have hmono : ∑ p ∈ P, Real.log (p:ℝ)/(p:ℝ)
      ≤ ∑ p ∈ (Finset.Ico A B).filter Nat.Prime, Real.log (p:ℝ)/(p:ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => div_nonneg (Real.log_natCast_nonneg i) (Nat.cast_nonneg _))
  have hmass := sum_log_div_Ico_le_log A B hA hAB
  linarith [hmono, hmass]


open Real Finset in
/-- **The trivial Riesz bound, fit-free** (Track R, N197):
`norm_tripleConvR_le'` with per-element `2p ≤ x` instead of `2B ≤ x`.
The split's top block has `blockHi > x/2` by construction — that is what
makes it the top block — so the fit hypothesis is unsatisfiable there;
but every survivor still carries `2p ≤ x` individually, which is all
the proof ever used. -/
theorem norm_tripleConvR_le'' (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (x A B : ℕ)
    (hA : 1 ≤ A) (hAB : A ≤ B)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ A ≤ p ∧ p < B)
    (h2P : ∀ p ∈ P, 2*p ≤ x) :
    |tripleConvR f x P|
      ≤ (x:ℝ) * (16 * (Real.log (B:ℝ) - Real.log (A:ℝ)) + 16 * Real.log 4) := by
  classical
  have hx0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
  rw [tripleConvR]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ p ∈ P,
      |(Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
        * ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
            * ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
                f n * (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ))|
      ≤ (x:ℝ) * ((Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
          * ∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ)) := by
    intro p hp
    obtain ⟨hpp, hAp, hpB⟩ := hP p hp
    have hp1 : 1 ≤ p := hpp.one_lt.le
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp1
    have h2p : 2*p ≤ x := h2P p hp
    have hquot : (2:ℝ) ≤ (x:ℝ)/(p:ℝ) := by
      rw [le_div_iff₀ hp0]
      have hc : ((2*p : ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast h2p
      push_cast at hc
      linarith
    have hlogpos : (0:ℝ) < Real.log ((x:ℝ)/(p:ℝ)) := Real.log_pos (by linarith)
    have hlogp : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
    -- the Riesz mean at `x/pq`, priced by `|R_f(y)| ≤ y`
    have hmid : |∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
          * ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
              f n * (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ))|
        ≤ ((x:ℝ)/(p:ℝ)) * ∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun q hq => ?_
      rw [Nat.mem_primesBelow] at hq
      obtain ⟨hqlt, hqp⟩ := hq
      have hq1 : 1 ≤ q := hqp.one_lt.le
      have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq1
      have hlogq : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_natCast_nonneg q
      -- `pq < x`, so the scale exceeds `1` and `norm_rieszMean_le` applies
      have hpqx : p*q < x := by
        have h1 : p*q < p*(x/p) := by
          have hp0' : 0 < p := hpp.pos
          exact (Nat.mul_lt_mul_left hp0').mpr hqlt
        have h2 : p*(x/p) ≤ x := by
          rw [Nat.mul_comm]; exact Nat.div_mul_le_self x p
        omega
      have hy1 : (1:ℝ) ≤ (x:ℝ)/((p:ℝ)*(q:ℝ)) := by
        rw [le_div_iff₀ (by positivity)]
        have : ((p*q : ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast hpqx.le
        push_cast at this; linarith
      have hinner := ExpSums.norm_rieszMean_le f hf
        ((x:ℝ)/((p:ℝ)*(q:ℝ))) hy1
      rw [abs_mul, abs_mul, abs_of_nonneg hlogq]
      calc Real.log (q:ℝ) * |f q|
            * |∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
                f n * (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ))|
          ≤ Real.log (q:ℝ) * 1 * ((x:ℝ)/((p:ℝ)*(q:ℝ))) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left (hf q) hlogq)
              hinner (abs_nonneg _) (by positivity)
        _ = (x:ℝ)/(p:ℝ) * (Real.log (q:ℝ)/(q:ℝ)) := by field_simp
    rw [abs_mul]
    have houter : |Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ))|
        ≤ Real.log (p:ℝ) / Real.log ((x:ℝ)/(p:ℝ)) := by
      rw [abs_div, abs_mul, abs_of_nonneg hlogp, abs_of_nonneg hlogpos.le]
      refine div_le_div_of_nonneg_right ?_ hlogpos.le
      calc Real.log (p:ℝ) * |f p| ≤ Real.log (p:ℝ) * 1 :=
            mul_le_mul_of_nonneg_left (hf p) hlogp
        _ = Real.log (p:ℝ) := mul_one _
    calc |Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ))|
          * |∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
              * ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
                  f n * (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ))|
        ≤ (Real.log (p:ℝ) / Real.log ((x:ℝ)/(p:ℝ)))
            * (((x:ℝ)/(p:ℝ)) * ∑ q ∈ (x/p).primesBelow,
                Real.log (q:ℝ)/(q:ℝ)) := by
          refine mul_le_mul houter hmid (abs_nonneg _) ?_
          exact div_nonneg hlogp hlogpos.le
      _ = (x:ℝ) * ((Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
            * ∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ)) := by
          field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (Sk_trivial_mass_le'' x A B hA hAB P hP h2P) hx0


open Real in
/-- **The mass floor implies the fit** (Track R, N197): if
`e·log 2 ≤ e^{−k}·log x` and `x ≥ 4` then `2·blockHi x k ≤ x` — the
converse of `block_index_le_of_fit`, with the margin `(e−2)·log 2` to
spare.  `x^u ≥ x^{log 4/log x} = 4` needs only `e ≥ 2`, so
`x^{1−u} ≤ x/4` and the ceiling costs one.  Kills N196's standalone
`hfit` hypothesis: every head block sits above the mass floor. -/
theorem fit_of_mass_floor (x k : ℕ) (hx : 4 ≤ x)
    (huL : Real.exp 1 * Real.log 2
      ≤ Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) :
    2 * blockHi x k ≤ x := by
  have hx0 : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hxR : (4:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have he2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9.le]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    push_cast
    ring
  -- `x^u ≥ 4`
  have hxu4 : (4:ℝ) ≤ (x:ℝ) ^ (Real.exp (-(k:ℝ))) := by
    rw [Real.rpow_def_of_pos hx0]
    have h1 : Real.log 4 ≤ Real.log (x:ℝ) * Real.exp (-(k:ℝ)) := by
      rw [hlog4]
      nlinarith [huL, he2, hlog2]
    calc (4:ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log (x:ℝ) * Real.exp (-(k:ℝ))) :=
          Real.exp_le_exp.mpr h1
  -- `x^{1−u} ≤ x/4`, ceiling costs one, double
  have hxpow : (x:ℝ) ^ (1 - Real.exp (-(k:ℝ))) ≤ (x:ℝ)/4 := by
    rw [Real.rpow_sub hx0, Real.rpow_one]
    exact div_le_div_of_nonneg_left hx0.le (by norm_num) hxu4
  have hceil : ((blockHi x k : ℕ):ℝ) ≤ (x:ℝ)/4 + 1 := by
    rw [blockHi]
    have h1 := Nat.ceil_lt_add_one
      (by positivity : (0:ℝ) ≤ (x:ℝ) ^ (1 - Real.exp (-(k:ℝ))))
    linarith [hxpow]
  have hfinal : 2 * ((blockHi x k : ℕ):ℝ) ≤ (x:ℝ) := by
    linarith [hceil, hxR]
  exact_mod_cast hfinal


set_option maxHeartbeats 3200000 in
open Real Finset in
/-- **§3's head, closed** (Track R, N196): under the campaign window
(`x ≥ 10¹⁶`, `√(21·log x) ≤ T ≤ log x`, `T² ≤ y`), with `K₀` the last
block before the mass floor (`e·log 2 ≤ e^{−K₀}·log x`, maximal), the
survivor sum obeys

  `|tripleConvR f x (survivors)| ≤ K₀·A + 2·x·(16((e−1)·e·log 2 + log 2)
      + 16·log 4)`,

with the `k`-free head bound

  `A = x·√((e^π)²·10¹⁵·(((log⌈T²⌉+2)² + T + 1)·b² + 1)) + 2x·log 4`.

Every rider of N189 is discharged by N190–N195; the boundary blocks
`K₀+1, K₀+2` are priced fit-free (`norm_tripleConvR_le''`) with widths
capped by maximality of `K₀`, and the split at `K₀+2` is valid because
the same maximality puts `e^{−(K₀+2)}·log x` below `log 2`.  The head
blocks' fit is `fit_of_mass_floor` — no fit hypothesis survives.  After this lemma §3's head is an inequality between named
quantities — the balance is struck. -/
theorem tripleConvR_survivors_balanced_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (x y K₀ : ℕ) (hx : 10^16 ≤ x) (hy2 : 2 ≤ y)
    (T : ℝ) (hT1 : Real.sqrt (21 * Real.log (x:ℝ)) ≤ T)
    (hT2 : T ≤ Real.log (x:ℝ)) (hTy : T^2 ≤ (y:ℝ))
    (hK₀1 : 1 ≤ K₀)
    (hK₀low : Real.exp 1 * Real.log 2
      ≤ Real.exp (-(K₀:ℝ)) * Real.log (x:ℝ))
    (hK₀max : Real.exp (-((K₀:ℝ)+1)) * Real.log (x:ℝ)
      < Real.exp 1 * Real.log 2)
    (hX3 : ∀ k ∈ Finset.Icc 1 K₀, 3 ≤ x / blockLo x k)
    (b : ℝ) (hb0 : 0 ≤ b)
    (hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖ghsMainPoly (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 x) t‖ ≤ b) :
    |tripleConvR f x ((((Finset.Icc 1 x).filter Nat.Prime).filter
        (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p))|
      ≤ (K₀:ℝ) * ((x:ℝ) * Real.sqrt ((Real.exp π)^2 * 10^15
            * (((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1) * b^2 + 1))
          + 2*(x:ℝ)*Real.log 4)
        + 2 * ((x:ℝ) * (16 * ((Real.exp 1 - 1) * (Real.exp 1 * Real.log 2)
            + Real.log 2) + 16 * Real.log 4)) := by
  classical
  have hx2 : (2:ℕ) ≤ x := le_trans (by norm_num) hx
  have hx3' : (3:ℕ) ≤ x := le_trans (by norm_num) hx
  have hx1 : (1:ℕ) ≤ x := by omega
  have hL0 : (0:ℝ) < Real.log (x:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 2 ≤ x))
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨h5T, hLT2, hγT⟩ := T_window_conditions x T hx hT1 hT2
  -- split validity at `K₀+2`
  have hK : Real.exp (-((K₀+2:ℕ):ℝ)) * Real.log (x:ℝ) < Real.log 2 := by
    have h1 : Real.exp (-((K₀+2:ℕ):ℝ))
        = Real.exp (-1) * Real.exp (-((K₀:ℝ)+1)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    have h2 : Real.exp (-1) * (Real.exp 1 * Real.log 2) = Real.log 2 := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    calc Real.exp (-((K₀+2:ℕ):ℝ)) * Real.log (x:ℝ)
        = Real.exp (-1) * (Real.exp (-((K₀:ℝ)+1)) * Real.log (x:ℝ)) := by
          rw [h1]; ring
      _ < Real.exp (-1) * (Real.exp 1 * Real.log 2) := by
          exact mul_lt_mul_of_pos_left hK₀max (Real.exp_pos _)
      _ = Real.log 2 := h2
  -- split, triangle, k-split
  rw [tripleConvR_survivor_split f x y (K₀+2) hx1 hK]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine tripleConvR_ksplit_le f x K₀ (K₀+2) (by omega)
    (fun k => (((Finset.Ico (blockLo x k) (blockHi x k)).filter
      Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p))) _ _ ?_ ?_
  · -- the head: N189 per block, then the SM-monotone step
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk1 : 1 ≤ k := hk.1
    have hkK : k ≤ K₀ := hk.2
    -- the block-membership facts
    have hP : ∀ p ∈ (((Finset.Ico (blockLo x k) (blockHi x k)).filter
        Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p)),
        p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Ico] at hp
      exact ⟨hp.1.2, hp.1.1.1, hp.1.1.2⟩
    have hPT : ∀ p ∈ (((Finset.Ico (blockLo x k) (blockHi x k)).filter
        Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p)),
        T^2 ≤ (p:ℝ) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Ico] at hp
      have hyp : y ≤ p := Nat.le_of_not_lt hp.2.1
      have : (y:ℝ) ≤ (p:ℝ) := by exact_mod_cast hyp
      linarith [hTy]
    -- the per-block mass floor
    have huL : Real.exp 1 * Real.log 2
        ≤ Real.exp (-(k:ℝ)) * Real.log (x:ℝ) := by
      have hmono : Real.exp (-(K₀:ℝ)) ≤ Real.exp (-(k:ℝ)) := by
        refine Real.exp_le_exp.mpr ?_
        have : (k:ℝ) ≤ (K₀:ℝ) := by exact_mod_cast hkK
        linarith
      have := mul_le_mul_of_nonneg_right hmono hL0.le
      linarith [hK₀low]
    have hMp := blockMass_le_const x k hx2 hk1 _ hP huL
    have hγ1 := gamma_le_one_of x T hx2 hγT
    have hSL := tailS_mul_log_le_one x hx
    have hW := bandWeight_mass_le_one x hx2
    have hbal := tripleConvR_block_balanced_le f hf x k hx3' hk1 _ hP
      (fit_of_mass_floor x k (by omega) huL) (hX3 k (by rw [Finset.mem_Icc]; omega)) T h5T hPT
      b hb0 hBu hT2 hLT2 hγ1 hSL hMp hW
    refine le_trans hbal ?_
    -- the SM-monotone step: `SM(k) ≤ log⌈T²⌉ + 2`
    have hSM := smallMass_le (x / blockLo x k) T h5T
    have hSM0 : (0:ℝ) ≤ ∑ q ∈ (x / blockLo x k).primesBelow.filter
        (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)), Real.log (q:ℝ)/(q:ℝ) :=
      Finset.sum_nonneg fun q _ => div_nonneg (Real.log_natCast_nonneg q)
        (Nat.cast_nonneg q)
    have hSMsq : (∑ q ∈ (x / blockLo x k).primesBelow.filter
          (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)), Real.log (q:ℝ)/(q:ℝ))^2
        ≤ (Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 := by
      nlinarith [hSM, hSM0]
    have hargmono : (Real.exp π)^2 * 10^15
        * (((∑ q ∈ (x / blockLo x k).primesBelow.filter
            (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
          Real.log (q:ℝ)/(q:ℝ))^2 + T + 1) * b^2 + 1)
        ≤ (Real.exp π)^2 * 10^15
          * (((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1) * b^2 + 1) := by
      have h1 : ((∑ q ∈ (x / blockLo x k).primesBelow.filter
            (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
          Real.log (q:ℝ)/(q:ℝ))^2 + T + 1) * b^2
          ≤ ((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1) * b^2 :=
        mul_le_mul_of_nonneg_right (by linarith [hSMsq]) (sq_nonneg b)
      have h2 : (0:ℝ) ≤ (Real.exp π)^2 * 10^15 := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith [h1]) h2
    have hxR0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
    have hs := Real.sqrt_le_sqrt hargmono
    have := mul_le_mul_of_nonneg_left hs hxR0
    linarith
  · -- the tail: two boundary blocks, fit-free
    have htb : ∀ k ∈ Finset.Icc (K₀+1) (K₀+2),
        |tripleConvR f x (((Finset.Ico (blockLo x k) (blockHi x k)).filter
          Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p))|
        ≤ (x:ℝ) * (16 * ((Real.exp 1 - 1) * (Real.exp 1 * Real.log 2)
            + Real.log 2) + 16 * Real.log 4) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hk1 : 1 ≤ k := by omega
      obtain ⟨hlo1, hlohi⟩ := blockLo_le_blockHi x k hx1
      have hP' : ∀ p ∈ (((Finset.Ico (blockLo x k) (blockHi x k)).filter
          Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p)),
          p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ico] at hp
        exact ⟨hp.1.2, hp.1.1.1, hp.1.1.2⟩
      have h2P : ∀ p ∈ (((Finset.Ico (blockLo x k) (blockHi x k)).filter
          Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p)), 2*p ≤ x := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ico] at hp
        omega
      refine le_trans (norm_tripleConvR_le'' f hf x (blockLo x k)
        (blockHi x k) hlo1 hlohi _ hP' h2P) ?_
      have hw := log_blockHi_sub_log_blockLo_le x k hx2 hk1
      have hmono : Real.exp (-(k:ℝ)) ≤ Real.exp (-((K₀:ℝ)+1)) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : ((K₀+1:ℕ):ℝ) ≤ (k:ℝ) := by exact_mod_cast hk.1
        push_cast at h1
        linarith
      have huk : Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
          ≤ Real.exp 1 * Real.log 2 := by
        have h1 := mul_le_mul_of_nonneg_right hmono hL0.le
        linarith [hK₀max]
      have he1nn : (0:ℝ) ≤ Real.exp 1 - 1 := by
        linarith [Real.exp_one_gt_d9.le]
      have hwidth2 : Real.log ((blockHi x k : ℕ):ℝ)
          - Real.log ((blockLo x k : ℕ):ℝ)
          ≤ (Real.exp 1 - 1) * (Real.exp 1 * Real.log 2) + Real.log 2 := by
        have h2 : (Real.exp 1 - 1) * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
            ≤ (Real.exp 1 - 1) * (Real.exp 1 * Real.log 2) :=
          mul_le_mul_of_nonneg_left huk he1nn
        nlinarith [hw, h2]
      have hx0' : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
      refine mul_le_mul_of_nonneg_left ?_ hx0'
      linarith [hwidth2]
    refine le_trans (Finset.sum_le_sum htb) ?_
    rw [Finset.sum_const, Nat.card_Icc]
    have h2c : K₀+2+1 - (K₀+1) = 2 := by omega
    rw [h2c]
    simp [nsmul_eq_mul]


open Real in
/-- **The window is inhabited** (Track R, N198): for `x ≥ 10¹⁶` there
is a Gaussian width in the campaign window — `T := √(21·log x)`
works. -/
theorem exists_window_T (x : ℕ) (hx : 10^16 ≤ x) :
    ∃ T : ℝ, Real.sqrt (21 * Real.log (x:ℝ)) ≤ T
      ∧ T ≤ Real.log (x:ℝ) := by
  refine ⟨Real.sqrt (21 * Real.log (x:ℝ)), le_refl _, ?_⟩
  have hxR : (10:ℝ)^16 ≤ (x:ℝ) := by exact_mod_cast hx
  have he_lt : Real.exp 1 ≤ (2.7182818286:ℝ) := Real.exp_one_lt_d9.le
  have hL32 : (32:ℝ) ≤ Real.log (x:ℝ) := by
    have hlog10 : (2:ℝ) ≤ Real.log 10 := by
      have h1 : Real.exp 2 ≤ 10 := by
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos 1, he_lt]
      calc (2:ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
        _ ≤ Real.log 10 := Real.log_le_log (Real.exp_pos 2) h1
    have h1 : Real.log ((10:ℝ)^16) = 16 * Real.log 10 := by
      rw [Real.log_pow]; push_cast; ring
    have h2 : Real.log ((10:ℝ)^16) ≤ Real.log (x:ℝ) :=
      Real.log_le_log (by positivity) hxR
    nlinarith [hlog10]
  have h21 : 21 * Real.log (x:ℝ) ≤ (Real.log (x:ℝ))^2 := by
    nlinarith [hL32]
  calc Real.sqrt (21 * Real.log (x:ℝ))
      ≤ Real.sqrt ((Real.log (x:ℝ))^2) := Real.sqrt_le_sqrt h21
    _ = Real.log (x:ℝ) := Real.sqrt_sq (by linarith)

open Real in
/-- **The block index is inhabited** (Track R, N198):
`K₀ := ⌊log(log x/(e·log 2))⌋` is at least one, sits above the mass
floor, and is maximal — the three hypotheses of the head/tail split,
witnessed. -/
theorem exists_K₀ (x : ℕ) (hx : 10^16 ≤ x) :
    ∃ K₀ : ℕ, 1 ≤ K₀
      ∧ Real.exp 1 * Real.log 2
          ≤ Real.exp (-(K₀:ℝ)) * Real.log (x:ℝ)
      ∧ Real.exp (-((K₀:ℝ)+1)) * Real.log (x:ℝ)
          < Real.exp 1 * Real.log 2 := by
  have hxR : (10:ℝ)^16 ≤ (x:ℝ) := by exact_mod_cast hx
  have he_lt : Real.exp 1 ≤ (2.7182818286:ℝ) := Real.exp_one_lt_d9.le
  have he_gt : (2.7182818283:ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
  have hlog2l : (0.693:ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlog2u : Real.log 2 ≤ (0.694:ℝ) := by
    have := Real.log_two_lt_d9; linarith
  have hL32 : (32:ℝ) ≤ Real.log (x:ℝ) := by
    have hlog10 : (2:ℝ) ≤ Real.log 10 := by
      have h1 : Real.exp 2 ≤ 10 := by
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos 1, he_lt]
      calc (2:ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
        _ ≤ Real.log 10 := Real.log_le_log (Real.exp_pos 2) h1
    have h1 : Real.log ((10:ℝ)^16) = 16 * Real.log 10 := by
      rw [Real.log_pow]; push_cast; ring
    have h2 : Real.log ((10:ℝ)^16) ≤ Real.log (x:ℝ) :=
      Real.log_le_log (by positivity) hxR
    nlinarith [hlog10]
  have hden0 : (0:ℝ) < Real.exp 1 * Real.log 2 := by
    nlinarith [he_gt, hlog2l]
  have harg0 : (0:ℝ) < Real.log (x:ℝ) / (Real.exp 1 * Real.log 2) := by
    have : (0:ℝ) < Real.log (x:ℝ) := by linarith
    positivity
  -- the argument is at least `e`, so the floor is at least one
  have harge : Real.exp 1 ≤ Real.log (x:ℝ) / (Real.exp 1 * Real.log 2) := by
    rw [le_div_iff₀ hden0]
    nlinarith [he_lt, hlog2u, hL32]
  refine ⟨⌊Real.log (Real.log (x:ℝ) / (Real.exp 1 * Real.log 2))⌋₊, ?_, ?_, ?_⟩
  · -- `1 ≤ K₀`
    have h1 : (1:ℝ) ≤ Real.log (Real.log (x:ℝ) / (Real.exp 1 * Real.log 2)) := by
      calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log (Real.log (x:ℝ) / (Real.exp 1 * Real.log 2)) :=
            Real.log_le_log (Real.exp_pos 1) harge
    exact Nat.le_floor (by exact_mod_cast h1)
  · -- the mass floor
    have hfl := Nat.floor_le (Real.log_nonneg (by
      calc (1:ℝ) ≤ Real.exp 1 := by linarith [he_gt]
        _ ≤ _ := harge))
    have h1 : Real.exp ((⌊Real.log (Real.log (x:ℝ)
        / (Real.exp 1 * Real.log 2))⌋₊ : ℝ))
        ≤ Real.log (x:ℝ) / (Real.exp 1 * Real.log 2) := by
      calc Real.exp ((⌊Real.log (Real.log (x:ℝ)
          / (Real.exp 1 * Real.log 2))⌋₊ : ℝ))
          ≤ Real.exp (Real.log (Real.log (x:ℝ)
              / (Real.exp 1 * Real.log 2))) := Real.exp_le_exp.mpr hfl
        _ = Real.log (x:ℝ) / (Real.exp 1 * Real.log 2) :=
            Real.exp_log harg0
    rw [Real.exp_neg]
    rw [inv_mul_eq_div, le_div_iff₀ (Real.exp_pos _)]
    rw [le_div_iff₀ hden0] at h1
    linarith [h1]
  · -- maximality
    have hfl := Nat.lt_floor_add_one (Real.log (Real.log (x:ℝ)
      / (Real.exp 1 * Real.log 2)))
    have h1 : Real.log (x:ℝ) / (Real.exp 1 * Real.log 2)
        < Real.exp ((⌊Real.log (Real.log (x:ℝ)
          / (Real.exp 1 * Real.log 2))⌋₊ : ℝ) + 1) := by
      calc Real.log (x:ℝ) / (Real.exp 1 * Real.log 2)
          = Real.exp (Real.log (Real.log (x:ℝ)
              / (Real.exp 1 * Real.log 2))) := (Real.exp_log harg0).symm
        _ < Real.exp ((⌊Real.log (Real.log (x:ℝ)
            / (Real.exp 1 * Real.log 2))⌋₊ : ℝ) + 1) :=
            Real.exp_lt_exp.mpr hfl
    rw [Real.exp_neg]
    rw [inv_mul_eq_div, div_lt_iff₀ (Real.exp_pos _)]
    rw [div_lt_iff₀ hden0] at h1
    linarith [h1]


open Real Complex in
/-- **The trivial character twist is the pure phase** (Track R, N200):
at modulus one, `charTwist` is `m ↦ m^{it}` — `ZMod 1` has one
element, and every character sends it to `1`. -/
theorem charTwist_one (χ : DirichletCharacter ℂ 1) (t : ℝ) :
    charTwist 1 χ t = fun m : ℕ => (m:ℂ) ^ (Complex.I * (t:ℂ)) := by
  funext m
  rw [charTwist]
  have h1 : ((m : ZMod 1)) = 1 := Subsingleton.elim _ _
  rw [h1, map_one, one_mul]

open Real Complex Finset in
/-- **The Halász band sup, priced by non-pretentiousness** (Track R,
N200): if `f` is `A`-non-pretentious at scale `x` and the band fits
under the frequency budget (`7·(halaszM + 1) ≤ A·x`), then on the whole
band the smooth main polynomial obeys the Euler-product bound with
`M := A`,

  `‖P₁(ξ)‖ ≤ exp(∑_{p<y₂}1/p − A + 2(∑_{p<x}1/p − ∑_{p<y₂}1/p) + 1)
      + x^{−δ}·∏_{p<y₂}(1 − p^{δ−1})⁻¹`.

`norm_ghsMainPoly_smooth_band_le` at the trivial character:
`NonPretentiousAt` hands the distance floor at `q = 1`, `t = 2πξ`
(`charTwist_one`), and `|2πξ| ≤ 7·(halaszM+1) ≤ A·x` keeps the
frequency inside the hypothesis range.  This is `hBu`'s content —
band-restricted exactly as N199 demands. -/
theorem bandSup_of_nonPretentious (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (hb : ∀ n, ‖f n‖ ≤ 1) (y₂ x : ℕ) (hy₂ : 1 ≤ y₂) (hyx : y₂ ≤ x)
    (hx : 1 ≤ x) (A : ℝ) (hA : NonPretentiousAt f A x) (h1A : 1 ≤ A)
    (hband : 7 * (((halaszM x : ℕ):ℝ) + 1) ≤ A * x)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∀ ξ : ℝ, |ξ| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖ghsMainPoly f ((Finset.Icc 1 x).filter
          (· ∈ Nat.smoothNumbers y₂)) ξ‖
        ≤ Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - A
              + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
                - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
          + (x:ℝ)^(-δ) * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹ := by
  intro ξ hξ
  -- the distance floor at the trivial character
  have hπ7 : (2:ℝ) * π ≤ 7 := by
    have := Real.pi_lt_d2
    linarith
  have hfreq : |2 * π * ξ| ≤ A * (x:ℝ) := by
    have h0 : (0:ℝ) ≤ ((halaszM x : ℕ):ℝ) + 1 := by positivity
    calc |2 * π * ξ| = (2 * π) * |ξ| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*π)]
      _ ≤ 7 * (((halaszM x : ℕ):ℝ) + 1) := by
          have := mul_le_mul (le_refl (2*π)) hξ (abs_nonneg ξ) (by positivity : (0:ℝ) ≤ 2*π)
          nlinarith [hπ7, abs_nonneg ξ, hξ, h0]
      _ ≤ A * (x:ℝ) := hband
  have hM := hA 1 1 (2 * π * ξ) (by exact_mod_cast h1A) hfreq
  rw [charTwist_one] at hM
  -- feed the band lemma
  exact norm_ghsMainPoly_smooth_band_le f hcm h1 hb y₂ x hy₂ hyx hx ξ A δ
    hδ0 hδ1 (by
      convert hM using 2)


open Real Complex Finset in
/-- **`hBu` for the smooth-restricted `f`, delivered** (Track R, N201):
under `A`-non-pretentiousness of `f`'s complexification, the closer's
band hypothesis holds for `g = f·1_{y₂-smooth}` with the Euler-product
bound as `b` — N180's two transfers feed N200's pricing.  The last
gluing of the analytic side: what enters `tripleConvR_survivors_
balanced_le`'s `hBu` is exactly this statement's conclusion. -/
theorem bandSup_smooth_restrict_of_nonPretentious (f : ℕ → ℝ)
    (hcm : CompletelyMultiplicativeC (fun n => ((f n : ℝ) : ℂ)))
    (h1 : f 1 = 1) (hf : ∀ n, |f n| ≤ 1)
    (y₂ x : ℕ) (hy₂ : 1 ≤ y₂) (hyx : y₂ ≤ x) (hx : 1 ≤ x)
    (A : ℝ) (hA : NonPretentiousAt (fun n => ((f n : ℝ) : ℂ)) A x)
    (h1A : 1 ≤ A)
    (hband : 7 * (((halaszM x : ℕ):ℝ) + 1) ≤ A * x)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖ghsMainPoly (fun n => (((if n ∈ Nat.smoothNumbers y₂ then f n
          else 0 : ℝ)) : ℂ)) (Finset.Icc 1 x) t‖
        ≤ Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - A
              + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
                - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
          + (x:ℝ)^(-δ) * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹ := by
  intro t ht
  rw [smooth_restrict_ofReal, ghsMainPoly_smooth_restrict_eq]
  have hfc1 : (fun n : ℕ => ((f n : ℝ) : ℂ)) 1 = 1 := by
    simp [h1]
  have hfcb : ∀ n, ‖(fun n : ℕ => ((f n : ℝ) : ℂ)) n‖ ≤ 1 := by
    intro n
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact hf n
  exact bandSup_of_nonPretentious _ hcm hfc1 hfcb y₂ x hy₂ hyx hx
    A hA h1A hband δ hδ0 hδ1 t ht


open Finset in
/-- **The real smooth restriction is completely multiplicative**
(Track R, N202): `completelyMultiplicativeC_smooth_restrict`, over
`ℝ` — smoothness is divisor-closed, so the cut respects products.
The `hmul` that `sum_after_discards` demands of the outer chain's
`g = f·1_{y-smooth}`. -/
theorem smooth_restrict_mul (f : ℕ → ℝ) (y : ℕ)
    (hmul : ∀ a b, f (a*b) = f a * f b) :
    ∀ a b, (if a*b ∈ Nat.smoothNumbers y then f (a*b) else 0)
      = (if a ∈ Nat.smoothNumbers y then f a else 0)
        * (if b ∈ Nat.smoothNumbers y then f b else 0) := by
  classical
  intro a b
  by_cases hab : a*b ∈ Nat.smoothNumbers y
  · have haS : a ∈ Nat.smoothNumbers y :=
      Nat.mem_smoothNumbers_of_dvd hab ⟨b, rfl⟩
    have hbS : b ∈ Nat.smoothNumbers y :=
      Nat.mem_smoothNumbers_of_dvd hab ⟨a, mul_comm a b⟩
    rw [if_pos hab, if_pos haS, if_pos hbS, hmul]
  · rw [if_neg hab]
    by_cases haS : a ∈ Nat.smoothNumbers y
    · by_cases hbS : b ∈ Nat.smoothNumbers y
      · exact absurd (Nat.mul_mem_smoothNumbers haS hbS) hab
      · rw [if_neg hbS, mul_zero]
    · rw [if_neg haS, zero_mul]

open Finset in
/-- **The real smooth restriction stays 1-bounded** (Track R, N202). -/
theorem smooth_restrict_abs_le (f : ℕ → ℝ) (y : ℕ)
    (hf : ∀ n, |f n| ≤ 1) :
    ∀ n, |(if n ∈ Nat.smoothNumbers y then f n else 0 : ℝ)| ≤ 1 := by
  classical
  intro n
  split
  · exact hf n
  · simp


open Real in
/-- **The logarithm under the cube root** (Track R, N203):
`log t ≤ 3·t^{1/3}` for `t ≥ 1` — the exponent that keeps the diagonal
sum linear. -/
theorem log_le_three_rpow_third (t : ℝ) (ht : 1 ≤ t) :
    Real.log t ≤ 3 * t ^ ((1:ℝ)/3) := by
  have ht0 : (0:ℝ) < t := by linarith
  have h30 : (0:ℝ) < t ^ ((1:ℝ)/3) := Real.rpow_pos_of_pos ht0 _
  have h1 : Real.log (t ^ ((1:ℝ)/3)) = (1/3) * Real.log t :=
    Real.log_rpow ht0 _
  have h2 : Real.log (t ^ ((1:ℝ)/3)) ≤ t ^ ((1:ℝ)/3) - 1 :=
    Real.log_le_sub_one_of_pos h30
  nlinarith [h1, h2, h30]

open Real Finset in
/-- **The `2/3`-power partial sum telescopes** (Track R, N203):
`∑_{n≤x} n^{−2/3} ≤ 3·x^{1/3}` — cube-root differences, mirroring the
`√`-telescope of `sum_log_div_sq_le`. -/
theorem sum_rpow_neg_twothirds_le (x : ℕ) (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 x, ((n:ℝ)) ^ (-(2:ℝ)/3)
      ≤ 3 * (x:ℝ) ^ ((1:ℝ)/3) := by
  induction x, hx using Nat.le_induction with
  | base =>
    norm_num
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N+1)]
    have hN0 : (0:ℝ) < ((N:ℕ):ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hN10 : (0:ℝ) < (((N+1):ℕ):ℝ) := by
      exact_mod_cast (by omega : 0 < N+1)
    -- the key step: `(N+1)^{−2/3} ≤ 3((N+1)^{1/3} − N^{1/3})`
    have hkey : (((N+1):ℕ):ℝ) ^ (-(2:ℝ)/3)
        ≤ 3 * ((((N+1):ℕ):ℝ) ^ ((1:ℝ)/3) - ((N:ℕ):ℝ) ^ ((1:ℝ)/3)) := by
      set a : ℝ := (((N+1):ℕ):ℝ) ^ ((1:ℝ)/3) with ha_def
      set b : ℝ := ((N:ℕ):ℝ) ^ ((1:ℝ)/3) with hb_def
      have ha0 : (0:ℝ) < a := Real.rpow_pos_of_pos hN10 _
      have hb0 : (0:ℝ) < b := Real.rpow_pos_of_pos hN0 _
      have ha3 : a^3 = (((N+1):ℕ):ℝ) := by
        rw [ha_def, ← Real.rpow_natCast ((((N+1):ℕ):ℝ) ^ ((1:ℝ)/3)) 3,
          ← Real.rpow_mul hN10.le]
        norm_num
      have hb3 : b^3 = ((N:ℕ):ℝ) := by
        rw [hb_def, ← Real.rpow_natCast (((N:ℕ):ℝ) ^ ((1:ℝ)/3)) 3,
          ← Real.rpow_mul hN0.le]
        norm_num
      have hdiff : a^3 - b^3 = 1 := by
        rw [ha3, hb3]
        push_cast
        ring
      have hba : b ≤ a := by
        have h1 : b^3 ≤ a^3 := by
          rw [ha3, hb3]
          exact_mod_cast (by omega : N ≤ N+1)
        nlinarith [ha0, hb0, sq_nonneg (a-b), sq_nonneg (a+b)]
      -- `1 = (a−b)(a²+ab+b²) ≤ (a−b)·3a²`, so `3(a−b) ≥ 1/a² = (N+1)^{−2/3}`
      have hfac : (a - b) * (a^2 + a*b + b^2) = 1 := by
        nlinarith [hdiff]
      have hinv : (((N+1):ℕ):ℝ) ^ (-(2:ℝ)/3) = 1 / a^2 := by
        rw [ha_def, ← Real.rpow_natCast ((((N+1):ℕ):ℝ) ^ ((1:ℝ)/3)) 2,
          ← Real.rpow_mul hN10.le, one_div, ← Real.rpow_neg hN10.le]
        norm_num
      rw [hinv, div_le_iff₀ (by positivity : (0:ℝ) < a^2)]
      nlinarith [hfac, hba, ha0, hb0, sq_nonneg a, sq_nonneg b,
        mul_pos ha0 hb0]
    linarith [ih, hkey]

open Real Finset in
/-- **The Riesz diagonal is linear** (Track R, N203):
`∑_{n≤x} (log x − log n)² ≤ 27·x` — the second term of
`rieszMean_log_identity`, priced.  `log(x/n) ≤ 3(x/n)^{1/3}` squares to
`9·x^{2/3}·n^{−2/3}`, and the `2/3`-telescope closes at `27x`. -/
theorem sum_log_sub_sq_le (x : ℕ) (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 x, (Real.log (x:ℝ) - Real.log (n:ℝ))^2
      ≤ 27 * (x:ℝ) := by
  have hx0 : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hterm : ∀ n ∈ Finset.Icc 1 x,
      (Real.log (x:ℝ) - Real.log (n:ℝ))^2
      ≤ 9 * ((x:ℝ) ^ ((2:ℝ)/3) * ((n:ℝ)) ^ (-(2:ℝ)/3)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hnx : (n:ℝ) ≤ (x:ℝ) := by exact_mod_cast hn.2
    have hq1 : (1:ℝ) ≤ (x:ℝ)/(n:ℝ) := by
      rw [le_div_iff₀ hn0]
      linarith
    have hlogd : Real.log (x:ℝ) - Real.log (n:ℝ)
        = Real.log ((x:ℝ)/(n:ℝ)) := (Real.log_div (ne_of_gt hx0)
          (ne_of_gt hn0)).symm
    have hlog0 : (0:ℝ) ≤ Real.log ((x:ℝ)/(n:ℝ)) := Real.log_nonneg hq1
    have hcube := log_le_three_rpow_third ((x:ℝ)/(n:ℝ)) hq1
    have hsq : (Real.log ((x:ℝ)/(n:ℝ)))^2
        ≤ 9 * (((x:ℝ)/(n:ℝ)) ^ ((1:ℝ)/3))^2 := by
      nlinarith [hcube, hlog0,
        Real.rpow_pos_of_pos (by positivity : (0:ℝ) < (x:ℝ)/(n:ℝ)) ((1:ℝ)/3)]
    have hpow : (((x:ℝ)/(n:ℝ)) ^ ((1:ℝ)/3))^2
        = (x:ℝ) ^ ((2:ℝ)/3) * ((n:ℝ)) ^ (-(2:ℝ)/3) := by
      rw [← Real.rpow_natCast (((x:ℝ)/(n:ℝ)) ^ ((1:ℝ)/3)) 2,
        ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (x:ℝ)/(n:ℝ)),
        Real.div_rpow hx0.le hn0.le, div_eq_mul_inv,
        ← Real.rpow_neg hn0.le]
      norm_num
    rw [hlogd]
    calc (Real.log ((x:ℝ)/(n:ℝ)))^2
        ≤ 9 * (((x:ℝ)/(n:ℝ)) ^ ((1:ℝ)/3))^2 := hsq
      _ = 9 * ((x:ℝ) ^ ((2:ℝ)/3) * ((n:ℝ)) ^ (-(2:ℝ)/3)) := by rw [hpow]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hsum := sum_rpow_neg_twothirds_le x hx
  have hx23 : (0:ℝ) ≤ (x:ℝ) ^ ((2:ℝ)/3) := by positivity
  calc 9 * ((x:ℝ) ^ ((2:ℝ)/3)
        * ∑ n ∈ Finset.Icc 1 x, ((n:ℝ)) ^ (-(2:ℝ)/3))
      ≤ 9 * ((x:ℝ) ^ ((2:ℝ)/3) * (3 * (x:ℝ) ^ ((1:ℝ)/3))) := by
        have := mul_le_mul_of_nonneg_left hsum hx23
        linarith
    _ = 27 * ((x:ℝ) ^ ((2:ℝ)/3) * (x:ℝ) ^ ((1:ℝ)/3)) := by ring
    _ = 27 * (x:ℝ) := by
        rw [← Real.rpow_add hx0]
        norm_num


open Real Finset in
/-- **The raw Riesz mean is priced by its scale** (Track R, N203):
`|∑_{m ≤ ⌊Y⌋} f(m)·(log Y − log m)| ≤ Y` for `1`-bounded `f` — every
inner sum of the R-world discard chain is worth its scale and nothing
more.  `∑(log N − log m) ≤ N` is `sum_log_ratio_mass_le`; the
real-scale correction `N·log(Y/N) ≤ Y − N` is the log-linear bound. -/
theorem abs_rieszMean_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (Y : ℝ) (hY : 1 ≤ Y) :
    |∑ m ∈ Finset.Icc 1 ⌊Y⌋₊, f m * (Real.log Y - Real.log (m:ℝ))|
      ≤ Y := by
  classical
  have hY0 : (0:ℝ) < Y := by linarith
  have hN1 : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  have hNY : ((⌊Y⌋₊ : ℕ):ℝ) ≤ Y := Nat.floor_le hY0.le
  have hN0 : (0:ℝ) < ((⌊Y⌋₊ : ℕ):ℝ) := by
    exact_mod_cast (by omega : 0 < ⌊Y⌋₊)
  have hterm : ∀ m ∈ Finset.Icc 1 ⌊Y⌋₊,
      |f m * (Real.log Y - Real.log (m:ℝ))|
      ≤ Real.log Y - Real.log (m:ℝ) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hmY : (m:ℝ) ≤ Y := le_trans (by exact_mod_cast hm.2) hNY
    have hpos : (0:ℝ) ≤ Real.log Y - Real.log (m:ℝ) := by
      have := Real.log_le_log hm0 hmY
      linarith
    rw [abs_mul, abs_of_nonneg hpos]
    nlinarith [hf m, abs_nonneg (f m)]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hcard : (Finset.Icc 1 ⌊Y⌋₊).card = ⌊Y⌋₊ := by
    rw [Nat.card_Icc]
    omega
  have hsum_eq : ∑ m ∈ Finset.Icc 1 ⌊Y⌋₊,
      (Real.log Y - Real.log (m:ℝ))
      = (∑ m ∈ Finset.Icc 1 ⌊Y⌋₊,
          (Real.log ((⌊Y⌋₊ : ℕ):ℝ) - Real.log (m:ℝ)))
        + ((⌊Y⌋₊ : ℕ):ℝ) * (Real.log Y - Real.log ((⌊Y⌋₊ : ℕ):ℝ)) := by
    have h1 : ∑ m ∈ Finset.Icc 1 ⌊Y⌋₊, (Real.log Y - Real.log (m:ℝ))
        = ∑ m ∈ Finset.Icc 1 ⌊Y⌋₊,
            ((Real.log ((⌊Y⌋₊ : ℕ):ℝ) - Real.log (m:ℝ))
              + (Real.log Y - Real.log ((⌊Y⌋₊ : ℕ):ℝ))) :=
      Finset.sum_congr rfl fun m _ => by ring
    rw [h1, Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul]
  rw [hsum_eq]
  have h2 := sum_log_ratio_mass_le ⌊Y⌋₊ hN1
  have hdivpos : (0:ℝ) < Y/((⌊Y⌋₊ : ℕ):ℝ) := by positivity
  have h3 : Real.log Y - Real.log ((⌊Y⌋₊ : ℕ):ℝ)
      ≤ Y/((⌊Y⌋₊ : ℕ):ℝ) - 1 := by
    have hlg := Real.log_le_sub_one_of_pos hdivpos
    rw [Real.log_div (ne_of_gt hY0) (ne_of_gt hN0)] at hlg
    linarith
  have hcancel : ((⌊Y⌋₊ : ℕ):ℝ) * (Y/((⌊Y⌋₊ : ℕ):ℝ)) = Y :=
    mul_div_cancel₀ Y (ne_of_gt hN0)
  have h4 : ((⌊Y⌋₊ : ℕ):ℝ) * (Real.log Y - Real.log ((⌊Y⌋₊ : ℕ):ℝ))
      ≤ Y - ((⌊Y⌋₊ : ℕ):ℝ) := by
    have := mul_le_mul_of_nonneg_left h3 hN0.le
    nlinarith [this, hcancel]
  linarith [h2, h4]


open Real Finset ArithmeticFunction in
/-- **The R-world mean value, prime-restricted** (Track R, N203):

  `|R_f(x)·log x − ∑_p f(p)·log p·R-inner(x/p)| ≤ 35·x`,

`rieszMean_log_identity`'s maiden application — the R-analogue of
`sum_mul_log_prime_restrict`, with the identity already factored so no
convolution-splitting is needed.  The non-prime Λ-support prices at
`8x` (`sum_vonMangoldt_div_properPrimePow_le` against
`abs_rieszMean_le`), the diagonal at `27x` (`sum_log_sub_sq_le`). -/
theorem rieszMean_mul_log_prime_restrict (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) (hmul : ∀ a b, f (a*b) = f a * f b)
    (x : ℕ) (hx : 1 ≤ x) :
    |(∑ n ∈ Finset.Icc 1 x, f n * (Real.log (x:ℝ) - Real.log (n:ℝ)))
        * Real.log (x:ℝ)
      - ∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime,
          f p * vonMangoldt p
            * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
                f m * (Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ))|
      ≤ 35 * (x:ℝ) := by
  classical
  have hx0 : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hid := rieszMean_log_identity f hmul (x:ℝ) hx0
  rw [Nat.floor_natCast] at hid
  rw [hid]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 x) Nat.Prime
    (fun d => f d * vonMangoldt d
      * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(d:ℝ)⌋₊,
          f m * (Real.log ((x:ℝ)/(d:ℝ)) - Real.log (m:ℝ)))]
  -- the prime part cancels; the rest is the non-prime Λ-support + diagonal
  have hcancel : ∀ A B C : ℝ, (A + B) + C - A = B + C := by
    intro A B C
    ring
  rw [hcancel]
  refine le_trans (abs_add_le _ _) ?_
  -- the non-prime branch
  have hNP : |∑ d ∈ (Finset.Icc 1 x).filter (fun d => ¬ d.Prime),
      f d * vonMangoldt d
        * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(d:ℝ)⌋₊,
            f m * (Real.log ((x:ℝ)/(d:ℝ)) - Real.log (m:ℝ))|
      ≤ 8 * (x:ℝ) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ d ∈ (Finset.Icc 1 x).filter (fun d => ¬ d.Prime),
        |f d * vonMangoldt d
          * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(d:ℝ)⌋₊,
              f m * (Real.log ((x:ℝ)/(d:ℝ)) - Real.log (m:ℝ))|
        ≤ (x:ℝ) * (vonMangoldt d / (d:ℝ)) := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_Icc] at hd
      have hd1 : 1 ≤ d := hd.1.1
      have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd1
      have hdx : (d:ℝ) ≤ (x:ℝ) := by exact_mod_cast hd.1.2
      have hY1 : (1:ℝ) ≤ (x:ℝ)/(d:ℝ) := by
        rw [le_div_iff₀ hd0]
        linarith
      have hR := abs_rieszMean_le f hf ((x:ℝ)/(d:ℝ)) hY1
      rw [abs_mul, abs_mul, abs_of_nonneg vonMangoldt_nonneg]
      calc |f d| * vonMangoldt d
            * |∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(d:ℝ)⌋₊,
                f m * (Real.log ((x:ℝ)/(d:ℝ)) - Real.log (m:ℝ))|
          ≤ 1 * vonMangoldt d * ((x:ℝ)/(d:ℝ)) := by
            have h1 := hf d
            have h2 : (0:ℝ) ≤ vonMangoldt d := vonMangoldt_nonneg
            have h3 := abs_nonneg (∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(d:ℝ)⌋₊,
              f m * (Real.log ((x:ℝ)/(d:ℝ)) - Real.log (m:ℝ)))
            nlinarith [hR, mul_nonneg h2 h3, abs_nonneg (f d),
              mul_nonneg (abs_nonneg (f d)) h2]
        _ = (x:ℝ) * (vonMangoldt d / (d:ℝ)) := by
            field_simp
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    -- restrict to the proper prime powers, where `Λ` lives
    have hsupp : ∑ d ∈ (Finset.Icc 1 x).filter (fun d => ¬ d.Prime),
        vonMangoldt d / (d:ℝ)
        = ∑ d ∈ (Finset.Icc 1 x).filter
            (fun d => IsPrimePow d ∧ ¬ d.Prime),
            vonMangoldt d / (d:ℝ) := by
      refine (Finset.sum_subset ?_ ?_).symm
      · intro d hd
        rw [Finset.mem_filter] at hd ⊢
        exact ⟨hd.1, hd.2.2⟩
      · intro d hd hnd
        rw [Finset.mem_filter] at hd hnd
        have : ¬ IsPrimePow d := by
          intro hpp
          exact hnd ⟨hd.1, hpp, hd.2⟩
        rw [vonMangoldt_eq_zero_iff.mpr this, zero_div]
    rw [hsupp]
    have hmass := sum_vonMangoldt_div_properPrimePow_le x
    nlinarith [hmass, hx0]
  -- the diagonal
  have hD : |∑ n ∈ Finset.Icc 1 x,
      f n * (Real.log (x:ℝ) - Real.log (n:ℝ))^2| ≤ 27 * (x:ℝ) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ n ∈ Finset.Icc 1 x,
        |f n * (Real.log (x:ℝ) - Real.log (n:ℝ))^2|
        ≤ (Real.log (x:ℝ) - Real.log (n:ℝ))^2 := by
      intro n _
      rw [abs_mul, abs_of_nonneg
        (sq_nonneg (Real.log (x:ℝ) - Real.log (n:ℝ)))]
      nlinarith [hf n, abs_nonneg (f n), sq_nonneg
        (Real.log (x:ℝ) - Real.log (n:ℝ))]
    exact le_trans (Finset.sum_le_sum hterm) (sum_log_sub_sq_le x hx)
  linarith [hNP, hD]


open Real Finset ArithmeticFunction in
/-- **The R-world head discard** (Track R, N204): the primes below `y`
cost `x·(log y + 2)` — `prime_head_sum_le` with the Riesz inner priced
by `abs_rieszMean_le`. -/
theorem rieszMean_prime_head_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (x y : ℕ) (hy : 2 ≤ y) :
    |∑ p ∈ ((Finset.Icc 1 x).filter Nat.Prime).filter (fun p => p < y),
        f p * vonMangoldt p
          * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
              f m * (Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ))|
      ≤ (x:ℝ) * (Real.log (y:ℝ) + 2) := by
  classical
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ p ∈ ((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => p < y),
      |f p * vonMangoldt p
        * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
            f m * (Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ))|
      ≤ (x:ℝ) * (Real.log (p:ℝ)/(p:ℝ)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hp1, hpx⟩, hpp⟩, -⟩ := hp
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
    have hY1 : (1:ℝ) ≤ (x:ℝ)/(p:ℝ) := by
      rw [le_div_iff₀ hp0]
      have : (p:ℝ) ≤ (x:ℝ) := by exact_mod_cast hpx
      linarith
    have hR := abs_rieszMean_le f hf ((x:ℝ)/(p:ℝ)) hY1
    rw [vonMangoldt_apply_prime hpp, abs_mul, abs_mul,
      abs_of_nonneg (Real.log_natCast_nonneg p)]
    have hlog0 : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
    calc |f p| * Real.log (p:ℝ)
          * |∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
              f m * (Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ))|
        ≤ 1 * Real.log (p:ℝ) * ((x:ℝ)/(p:ℝ)) := by
          have h1 := hf p
          have h3 := abs_nonneg (∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
            f m * (Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ)))
          nlinarith [hR, abs_nonneg (f p),
            mul_nonneg (abs_nonneg (f p)) hlog0,
            mul_nonneg hlog0 h3]
      _ = (x:ℝ) * (Real.log (p:ℝ)/(p:ℝ)) := by
          field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hsub : ((Finset.Icc 1 x).filter Nat.Prime).filter (fun p => p < y)
      ⊆ y.primesBelow := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    rw [Nat.mem_primesBelow]
    exact ⟨hp.2, hp.1.2⟩
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  have hmass := sum_log_div_primesBelow_le_sharp y hy
  have hx0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
  nlinarith [hmono, hmass, hx0]

open Real Finset ArithmeticFunction in
/-- **The R-world tail discard** (Track R, N204): the primes above
`x/2` cost `(x+1)·log 4` — Chebyshev against the scale-2 inner. -/
theorem rieszMean_prime_tail_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (x : ℕ) :
    |∑ p ∈ ((Finset.Icc 1 x).filter Nat.Prime).filter (fun p => x < 2*p),
        f p * vonMangoldt p
          * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
              f m * (Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ))|
      ≤ 2*((x:ℝ)+1) * Real.log 4 := by
  classical
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ p ∈ ((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => x < 2*p),
      |f p * vonMangoldt p
        * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
            f m * (Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ))|
      ≤ 2 * Real.log (p:ℝ) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hp1, hpx⟩, hpp⟩, h2p⟩ := hp
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
    have hY1 : (1:ℝ) ≤ (x:ℝ)/(p:ℝ) := by
      rw [le_div_iff₀ hp0]
      have : (p:ℝ) ≤ (x:ℝ) := by exact_mod_cast hpx
      linarith
    have hY2 : (x:ℝ)/(p:ℝ) ≤ 2 := by
      rw [div_le_iff₀ hp0]
      have : (x:ℝ) < 2*(p:ℝ) := by exact_mod_cast h2p
      linarith
    have hR := abs_rieszMean_le f hf ((x:ℝ)/(p:ℝ)) hY1
    rw [vonMangoldt_apply_prime hpp, abs_mul, abs_mul,
      abs_of_nonneg (Real.log_natCast_nonneg p)]
    have hlog0 : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
    have h3 := abs_nonneg (∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
      f m * (Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ)))
    nlinarith [hR, hY2, hf p, abs_nonneg (f p),
      mul_nonneg (abs_nonneg (f p)) hlog0, mul_nonneg hlog0 h3]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hsub : ((Finset.Icc 1 x).filter Nat.Prime).filter (fun p => x < 2*p)
      ⊆ (x+1).primesBelow := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    rw [Nat.mem_primesBelow]
    exact ⟨by omega, hp.1.2⟩
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => Real.log_natCast_nonneg p)
  have hmass := sum_log_primesBelow_le (x+1)
  have hcast : ((x+1 : ℕ):ℝ) = (x:ℝ)+1 := by push_cast; ring
  rw [hcast] at hmass
  have hlog4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  nlinarith [hmono, hmass, hlog4]


open Real Finset in
/-- **The Riesz diagonal at real scale** (Track R, N205a): the `R₂`
diagonal costs `55·Y` at any real scale — `sum_log_sub_sq_le` pushed
through `log Y ≤ log 2 + log ⌊Y⌋`. -/
theorem sum_log_sub_sq_le' (Y : ℝ) (hY : 1 ≤ Y) :
    ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (Real.log Y - Real.log (n:ℝ))^2
      ≤ 55 * Y := by
  have hY0 : (0:ℝ) < Y := by linarith
  have hN1 : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  have hNR : (1:ℝ) ≤ ((⌊Y⌋₊:ℕ):ℝ) := by exact_mod_cast hN1
  have hNY : ((⌊Y⌋₊:ℕ):ℝ) ≤ Y := Nat.floor_le hY0.le
  have hYN : Y < ((⌊Y⌋₊:ℕ):ℝ) + 1 := Nat.lt_floor_add_one Y
  have hlogY : Real.log Y ≤ Real.log 2 + Real.log ((⌊Y⌋₊:ℕ):ℝ) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log hY0 (by linarith)
  have hterm : ∀ n ∈ Finset.Icc 1 ⌊Y⌋₊,
      (Real.log Y - Real.log (n:ℝ))^2
      ≤ 1 + 2*(Real.log ((⌊Y⌋₊:ℕ):ℝ) - Real.log (n:ℝ))^2 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn.1
    have hnN : (n:ℝ) ≤ ((⌊Y⌋₊:ℕ):ℝ) := by exact_mod_cast hn.2
    have ha : 0 ≤ Real.log ((⌊Y⌋₊:ℕ):ℝ) - Real.log (n:ℝ) := by
      have := Real.log_le_log hn0 hnN
      linarith
    have hb : 0 ≤ Real.log Y - Real.log (n:ℝ) := by
      have := Real.log_le_log hn0 (le_trans hnN hNY)
      linarith
    have hc : Real.log Y - Real.log (n:ℝ)
        ≤ Real.log 2 + (Real.log ((⌊Y⌋₊:ℕ):ℝ) - Real.log (n:ℝ)) := by
      linarith
    nlinarith [sq_nonneg (Real.log 2
        - (Real.log ((⌊Y⌋₊:ℕ):ℝ) - Real.log (n:ℝ))),
      Real.log_two_lt_d9, Real.log_two_gt_d9, ha, hb, hc]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hsq := sum_log_sub_sq_le ⌊Y⌋₊ hN1
  calc ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊,
        (1 + 2*(Real.log ((⌊Y⌋₊:ℕ):ℝ) - Real.log (n:ℝ))^2)
      = ((⌊Y⌋₊:ℕ):ℝ) + 2 * ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊,
          (Real.log ((⌊Y⌋₊:ℕ):ℝ) - Real.log (n:ℝ))^2 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum,
          Nat.card_Icc]
        simp
    _ ≤ ((⌊Y⌋₊:ℕ):ℝ) + 2 * (27*((⌊Y⌋₊:ℕ):ℝ)) := by linarith
    _ = 55 * ((⌊Y⌋₊:ℕ):ℝ) := by ring
    _ ≤ 55 * Y := by linarith

open Real Finset ArithmeticFunction in
/-- **The R-mean value at real scale** (Track R, N205a): the identity
error is linear at any real scale `Y ≥ 1` — the mirror of
`rieszMean_mul_log_prime_restrict` with `x` replaced by `⌊Y⌋` and the
diagonal priced by `sum_log_sub_sq_le'`. -/
theorem rieszMean_mul_log_prime_restrict' (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) (hmul : ∀ a b, f (a*b) = f a * f b)
    (Y : ℝ) (hY : 1 ≤ Y) :
    |(∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, f n * (Real.log Y - Real.log (n:ℝ)))
        * Real.log Y
      - ∑ p ∈ (Finset.Icc 1 ⌊Y⌋₊).filter Nat.Prime,
          f p * vonMangoldt p
            * ∑ m ∈ Finset.Icc 1 ⌊Y/(p:ℝ)⌋₊,
                f m * (Real.log (Y/(p:ℝ)) - Real.log (m:ℝ))|
      ≤ 63 * Y := by
  classical
  have hY0 : (0:ℝ) < Y := by linarith
  have hid := rieszMean_log_identity f hmul Y hY0
  rw [hid]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 ⌊Y⌋₊) Nat.Prime
    (fun d => f d * vonMangoldt d
      * ∑ m ∈ Finset.Icc 1 ⌊Y/(d:ℝ)⌋₊,
          f m * (Real.log (Y/(d:ℝ)) - Real.log (m:ℝ)))]
  have hcancel : ∀ A B C : ℝ, (A + B) + C - A = B + C := by
    intro A B C
    ring
  rw [hcancel]
  refine le_trans (abs_add_le _ _) ?_
  -- the non-prime branch
  have hNP : |∑ d ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun d => ¬ d.Prime),
      f d * vonMangoldt d
        * ∑ m ∈ Finset.Icc 1 ⌊Y/(d:ℝ)⌋₊,
            f m * (Real.log (Y/(d:ℝ)) - Real.log (m:ℝ))|
      ≤ 8 * Y := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ d ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun d => ¬ d.Prime),
        |f d * vonMangoldt d
          * ∑ m ∈ Finset.Icc 1 ⌊Y/(d:ℝ)⌋₊,
              f m * (Real.log (Y/(d:ℝ)) - Real.log (m:ℝ))|
        ≤ Y * (vonMangoldt d / (d:ℝ)) := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_Icc] at hd
      have hd1 : 1 ≤ d := hd.1.1
      have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd1
      have hdN : (d:ℝ) ≤ ((⌊Y⌋₊:ℕ):ℝ) := by exact_mod_cast hd.1.2
      have hdx : (d:ℝ) ≤ Y := le_trans hdN (Nat.floor_le hY0.le)
      have hY1 : (1:ℝ) ≤ Y/(d:ℝ) := by
        rw [le_div_iff₀ hd0]
        linarith
      have hR := abs_rieszMean_le f hf (Y/(d:ℝ)) hY1
      rw [abs_mul, abs_mul, abs_of_nonneg vonMangoldt_nonneg]
      calc |f d| * vonMangoldt d
            * |∑ m ∈ Finset.Icc 1 ⌊Y/(d:ℝ)⌋₊,
                f m * (Real.log (Y/(d:ℝ)) - Real.log (m:ℝ))|
          ≤ 1 * vonMangoldt d * (Y/(d:ℝ)) := by
            have h1 := hf d
            have h2 : (0:ℝ) ≤ vonMangoldt d := vonMangoldt_nonneg
            have h3 := abs_nonneg (∑ m ∈ Finset.Icc 1 ⌊Y/(d:ℝ)⌋₊,
              f m * (Real.log (Y/(d:ℝ)) - Real.log (m:ℝ)))
            nlinarith [hR, mul_nonneg h2 h3, abs_nonneg (f d),
              mul_nonneg (abs_nonneg (f d)) h2]
        _ = Y * (vonMangoldt d / (d:ℝ)) := by
            field_simp
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hsupp : ∑ d ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun d => ¬ d.Prime),
        vonMangoldt d / (d:ℝ)
        = ∑ d ∈ (Finset.Icc 1 ⌊Y⌋₊).filter
            (fun d => IsPrimePow d ∧ ¬ d.Prime),
            vonMangoldt d / (d:ℝ) := by
      refine (Finset.sum_subset ?_ ?_).symm
      · intro d hd
        rw [Finset.mem_filter] at hd ⊢
        exact ⟨hd.1, hd.2.2⟩
      · intro d hd hnd
        rw [Finset.mem_filter] at hd hnd
        have : ¬ IsPrimePow d := by
          intro hpp
          exact hnd ⟨hd.1, hpp, hd.2⟩
        rw [vonMangoldt_eq_zero_iff.mpr this, zero_div]
    rw [hsupp]
    have hmass := sum_vonMangoldt_div_properPrimePow_le ⌊Y⌋₊
    nlinarith [hmass, hY0]
  -- the diagonal
  have hD : |∑ n ∈ Finset.Icc 1 ⌊Y⌋₊,
      f n * (Real.log Y - Real.log (n:ℝ))^2| ≤ 55 * Y := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ n ∈ Finset.Icc 1 ⌊Y⌋₊,
        |f n * (Real.log Y - Real.log (n:ℝ))^2|
        ≤ (Real.log Y - Real.log (n:ℝ))^2 := by
      intro n _
      rw [abs_mul, abs_of_nonneg
        (sq_nonneg (Real.log Y - Real.log (n:ℝ)))]
      nlinarith [hf n, abs_nonneg (f n), sq_nonneg
        (Real.log Y - Real.log (n:ℝ))]
    exact le_trans (Finset.sum_le_sum hterm) (sum_log_sub_sq_le' Y hY)
  linarith [hNP, hD]

open Real Finset ArithmeticFunction in
/-- **The R-mean value in `primesBelow` form** (Track R, N205b): the
boundary prime `⌊Y⌋` costs one more `Y` — this is the identity error in
exactly the range `tripleConvR`'s inner sum uses. -/
theorem rieszMean_mul_log_primesBelow_le (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) (hmul : ∀ a b, f (a*b) = f a * f b)
    (Y : ℝ) (hY : 1 ≤ Y) :
    |(∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, f n * (Real.log Y - Real.log (n:ℝ)))
        * Real.log Y
      - ∑ q ∈ (⌊Y⌋₊).primesBelow,
          f q * vonMangoldt q
            * ∑ m ∈ Finset.Icc 1 ⌊Y/(q:ℝ)⌋₊,
                f m * (Real.log (Y/(q:ℝ)) - Real.log (m:ℝ))|
      ≤ 64 * Y := by
  classical
  have hY0 : (0:ℝ) < Y := by linarith
  have hbase := rieszMean_mul_log_prime_restrict' f hf hmul Y hY
  by_cases hNp : (⌊Y⌋₊).Prime
  · have hset : (Finset.Icc 1 ⌊Y⌋₊).filter Nat.Prime
        = insert ⌊Y⌋₊ ((⌊Y⌋₊).primesBelow) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
        Nat.mem_primesBelow]
      constructor
      · rintro ⟨⟨hq1, hqN⟩, hqp⟩
        rcases eq_or_lt_of_le hqN with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, hqp⟩
      · rintro (rfl | ⟨hlt, hqp⟩)
        · exact ⟨⟨hNp.one_lt.le, le_refl _⟩, hNp⟩
        · exact ⟨⟨hqp.one_lt.le, hlt.le⟩, hqp⟩
    have hnotmem : ⌊Y⌋₊ ∉ (⌊Y⌋₊).primesBelow := by
      simp [Nat.mem_primesBelow]
    rw [hset, Finset.sum_insert hnotmem] at hbase
    have hN1 : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
    have hN0 : (0:ℝ) < ((⌊Y⌋₊:ℕ):ℝ) := by exact_mod_cast hN1
    have hNY : ((⌊Y⌋₊:ℕ):ℝ) ≤ Y := Nat.floor_le hY0.le
    have hY1' : (1:ℝ) ≤ Y/((⌊Y⌋₊:ℕ):ℝ) := by
      rw [le_div_iff₀ hN0]
      linarith
    have hR := abs_rieszMean_le f hf (Y/((⌊Y⌋₊:ℕ):ℝ)) hY1'
    have hlogN : Real.log ((⌊Y⌋₊:ℕ):ℝ) ≤ ((⌊Y⌋₊:ℕ):ℝ) := by
      have := Real.log_le_sub_one_of_pos hN0
      linarith
    have hterm : |f ⌊Y⌋₊ * vonMangoldt ⌊Y⌋₊
        * ∑ m ∈ Finset.Icc 1 ⌊Y/((⌊Y⌋₊:ℕ):ℝ)⌋₊,
            f m * (Real.log (Y/((⌊Y⌋₊:ℕ):ℝ)) - Real.log (m:ℝ))| ≤ Y := by
      rw [vonMangoldt_apply_prime hNp, abs_mul, abs_mul,
        abs_of_nonneg (Real.log_natCast_nonneg _)]
      have hq0 : (0:ℝ) ≤ Y/((⌊Y⌋₊:ℕ):ℝ) := by positivity
      calc |f ⌊Y⌋₊| * Real.log ((⌊Y⌋₊:ℕ):ℝ)
            * |∑ m ∈ Finset.Icc 1 ⌊Y/((⌊Y⌋₊:ℕ):ℝ)⌋₊,
                f m * (Real.log (Y/((⌊Y⌋₊:ℕ):ℝ)) - Real.log (m:ℝ))|
          ≤ 1 * Real.log ((⌊Y⌋₊:ℕ):ℝ) * (Y/((⌊Y⌋₊:ℕ):ℝ)) := by
            have h1 := hf ⌊Y⌋₊
            have h2 : (0:ℝ) ≤ Real.log ((⌊Y⌋₊:ℕ):ℝ) :=
              Real.log_natCast_nonneg _
            have h3 := abs_nonneg (∑ m ∈ Finset.Icc 1 ⌊Y/((⌊Y⌋₊:ℕ):ℝ)⌋₊,
              f m * (Real.log (Y/((⌊Y⌋₊:ℕ):ℝ)) - Real.log (m:ℝ)))
            nlinarith [hR, abs_nonneg (f ⌊Y⌋₊),
              mul_nonneg (abs_nonneg (f ⌊Y⌋₊)) h2,
              mul_nonneg h2 h3]
        _ ≤ ((⌊Y⌋₊:ℕ):ℝ) * (Y/((⌊Y⌋₊:ℕ):ℝ)) := by
            nlinarith [hlogN, hq0]
        _ = Y := by
            field_simp
    have hsplit : (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊,
          f n * (Real.log Y - Real.log (n:ℝ))) * Real.log Y
        - ∑ q ∈ (⌊Y⌋₊).primesBelow,
            f q * vonMangoldt q
              * ∑ m ∈ Finset.Icc 1 ⌊Y/(q:ℝ)⌋₊,
                  f m * (Real.log (Y/(q:ℝ)) - Real.log (m:ℝ))
        = ((∑ n ∈ Finset.Icc 1 ⌊Y⌋₊,
              f n * (Real.log Y - Real.log (n:ℝ))) * Real.log Y
            - (f ⌊Y⌋₊ * vonMangoldt ⌊Y⌋₊
                * ∑ m ∈ Finset.Icc 1 ⌊Y/((⌊Y⌋₊:ℕ):ℝ)⌋₊,
                    f m * (Real.log (Y/((⌊Y⌋₊:ℕ):ℝ)) - Real.log (m:ℝ))
              + ∑ q ∈ (⌊Y⌋₊).primesBelow,
                  f q * vonMangoldt q
                    * ∑ m ∈ Finset.Icc 1 ⌊Y/(q:ℝ)⌋₊,
                        f m * (Real.log (Y/(q:ℝ)) - Real.log (m:ℝ))))
          + f ⌊Y⌋₊ * vonMangoldt ⌊Y⌋₊
              * ∑ m ∈ Finset.Icc 1 ⌊Y/((⌊Y⌋₊:ℕ):ℝ)⌋₊,
                  f m * (Real.log (Y/((⌊Y⌋₊:ℕ):ℝ)) - Real.log (m:ℝ)) := by
      ring
    rw [hsplit]
    refine le_trans (abs_add_le _ _) ?_
    linarith [hbase, hterm]
  · have hset : (Finset.Icc 1 ⌊Y⌋₊).filter Nat.Prime
        = (⌊Y⌋₊).primesBelow := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesBelow]
      constructor
      · rintro ⟨⟨hq1, hqN⟩, hqp⟩
        rcases eq_or_lt_of_le hqN with h | h
        · exact absurd (h ▸ hqp) hNp
        · exact ⟨h, hqp⟩
      · rintro ⟨hlt, hqp⟩
        exact ⟨⟨hqp.one_lt.le, hlt.le⟩, hqp⟩
    rw [hset] at hbase
    linarith [hbase, hY0]


open Real Finset ArithmeticFunction in
/-- **The survivor sum becomes the triple convolution** (Track R,
N205cd): over the survivors `y ≤ p`, `2p ≤ x`, iterating the identity
once more (`rieszMean_mul_log_primesBelow_le` at `Y = x/p`) turns
`∑_p f(p)Λ(p)·R(x/p)` into `tripleConvR` at Mertens cost — the scale
floor `log(x/p) ≥ log 2` prices the division. -/
theorem rieszMean_survivors_to_tripleConvR (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) (hmul : ∀ a b, f (a*b) = f a * f b)
    (x y : ℕ) (hx : 1 ≤ x) :
    |∑ p ∈ (((Finset.Icc 1 x).filter Nat.Prime).filter
          (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p),
        f p * vonMangoldt p
          * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
              f m * (Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ))
      - tripleConvR f x ((((Finset.Icc 1 x).filter Nat.Prime).filter
          (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p))|
      ≤ 64 * (x:ℝ) / Real.log 2 * (Real.log ((x+1:ℕ):ℝ) + 2) := by
  classical
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [tripleConvR, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ p ∈ (((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p),
      |f p * vonMangoldt p
          * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
              f m * (Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ))
        - (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
            * ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
                * ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
                    f n * (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                      - Real.log (n:ℝ))|
      ≤ 64 * (x:ℝ) / Real.log 2 * (Real.log (p:ℝ)/(p:ℝ)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨⟨hp1, hpx⟩, hpp⟩, -⟩, h2p⟩ := hp
    have h2p' : 2*p ≤ x := by omega
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
    have hY2 : (2:ℝ) ≤ (x:ℝ)/(p:ℝ) := by
      rw [le_div_iff₀ hp0]
      exact_mod_cast h2p'
    have hY1 : (1:ℝ) ≤ (x:ℝ)/(p:ℝ) := by linarith
    have hlogY : Real.log 2 ≤ Real.log ((x:ℝ)/(p:ℝ)) :=
      Real.log_le_log (by norm_num) hY2
    have hlogY0 : (0:ℝ) < Real.log ((x:ℝ)/(p:ℝ)) :=
      lt_of_lt_of_le hlog2 hlogY
    have hfloor : ⌊(x:ℝ)/(p:ℝ)⌋₊ = x/p := by
      rw [Nat.floor_div_natCast, Nat.floor_natCast]
    rw [hfloor]
    have hb := rieszMean_mul_log_primesBelow_le f hf hmul
      ((x:ℝ)/(p:ℝ)) hY1
    rw [hfloor] at hb
    have hstuff : ∑ q ∈ (x/p).primesBelow,
        f q * vonMangoldt q
          * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)/(q:ℝ)⌋₊,
              f m * (Real.log ((x:ℝ)/(p:ℝ)/(q:ℝ)) - Real.log (m:ℝ))
        = ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
            * ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
                f n * (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ)) := by
      refine Finset.sum_congr rfl fun q hq => ?_
      have hqp := (Nat.mem_primesBelow.mp hq).2
      rw [vonMangoldt_apply_prime hqp, div_div]
      ring
    rw [hstuff] at hb
    have hdiff : f p * vonMangoldt p
          * ∑ m ∈ Finset.Icc 1 (x/p),
              f m * (Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ))
        - (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
            * ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
                * ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
                    f n * (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                      - Real.log (n:ℝ))
        = (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
            * ((∑ m ∈ Finset.Icc 1 (x/p),
                  f m * (Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ)))
                * Real.log ((x:ℝ)/(p:ℝ))
              - ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
                  * ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
                      f n * (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                        - Real.log (n:ℝ))) := by
      rw [vonMangoldt_apply_prime hpp]
      field_simp
    rw [hdiff, abs_mul]
    have habs1 : |Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ))|
        ≤ Real.log (p:ℝ) / Real.log 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg (Real.log_natCast_nonneg p),
        abs_of_pos hlogY0, div_le_div_iff₀ hlogY0 hlog2]
      nlinarith [hf p, abs_nonneg (f p), Real.log_natCast_nonneg p,
        hlog2.le, hlogY, mul_nonneg (Real.log_natCast_nonneg p) hlog2.le]
    calc |Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ))|
          * |(∑ m ∈ Finset.Icc 1 (x/p),
                f m * (Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ)))
              * Real.log ((x:ℝ)/(p:ℝ))
            - ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
                * ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
                    f n * (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                      - Real.log (n:ℝ))|
        ≤ (Real.log (p:ℝ) / Real.log 2) * (64 * ((x:ℝ)/(p:ℝ))) :=
          mul_le_mul habs1 hb (abs_nonneg _)
            (div_nonneg (Real.log_natCast_nonneg p) hlog2.le)
      _ = 64 * (x:ℝ) / Real.log 2 * (Real.log (p:ℝ)/(p:ℝ)) := by
          field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hsub : (((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p)
      ⊆ (x+1).primesBelow := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    rw [Nat.mem_primesBelow]
    exact ⟨by omega, hp.1.1.2⟩
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  have hmass := sum_log_div_primesBelow_le_sharp (x+1) (by omega)
  have hc0 : (0:ℝ) ≤ 64 * (x:ℝ) / Real.log 2 := by positivity
  exact mul_le_mul_of_nonneg_left (le_trans hmono hmass) hc0


open Real Finset ArithmeticFunction in
/-- **§3, end to end** (Track R, N205e): the Riesz mean at the top
scale is priced by the balanced triple convolution plus linear and
Mertens errors.  The chain: the identity error (N203), the head and
tail discards (N204), the survivor iteration (N205cd), and the
balanced per-block estimate over the survivors (N197c). -/
theorem rieszMean_log_le_of_nonPretentious (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) (hmul : ∀ a b, f (a*b) = f a * f b)
    (x y K₀ : ℕ) (hx : 10^16 ≤ x) (hy2 : 2 ≤ y) (hyx : 2*y ≤ x)
    (T : ℝ) (hT1 : Real.sqrt (21 * Real.log (x:ℝ)) ≤ T)
    (hT2 : T ≤ Real.log (x:ℝ)) (hTy : T^2 ≤ (y:ℝ))
    (hK₀1 : 1 ≤ K₀)
    (hK₀low : Real.exp 1 * Real.log 2
      ≤ Real.exp (-(K₀:ℝ)) * Real.log (x:ℝ))
    (hK₀max : Real.exp (-((K₀:ℝ)+1)) * Real.log (x:ℝ)
      < Real.exp 1 * Real.log 2)
    (hX3 : ∀ k ∈ Finset.Icc 1 K₀, 3 ≤ x / blockLo x k)
    (b : ℝ) (hb0 : 0 ≤ b)
    (hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖ghsMainPoly (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 x) t‖ ≤ b) :
    |(∑ n ∈ Finset.Icc 1 x, f n * (Real.log (x:ℝ) - Real.log (n:ℝ)))
        * Real.log (x:ℝ)|
      ≤ 35*(x:ℝ) + (x:ℝ)*(Real.log (y:ℝ) + 2) + 2*((x:ℝ)+1)*Real.log 4
        + 64 * (x:ℝ) / Real.log 2 * (Real.log ((x+1:ℕ):ℝ) + 2)
        + ((K₀:ℝ) * ((x:ℝ) * Real.sqrt ((Real.exp π)^2 * 10^15
              * (((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1) * b^2 + 1))
            + 2*(x:ℝ)*Real.log 4)
          + 2 * ((x:ℝ) * (16 * ((Real.exp 1 - 1) * (Real.exp 1 * Real.log 2)
              + Real.log 2) + 16 * Real.log 4))) := by
  classical
  have hx1 : (1:ℕ) ≤ x := le_trans (by norm_num) hx
  have hid := rieszMean_mul_log_prime_restrict f hf hmul x hx1
  have hhead := rieszMean_prime_head_le f hf x y hy2
  have htail := rieszMean_prime_tail_le f hf x
  have hbridge := rieszMean_survivors_to_tripleConvR f hf hmul x y hx1
  have hconv := tripleConvR_survivors_balanced_le f hf x y K₀ hx hy2
    T hT1 hT2 hTy hK₀1 hK₀low hK₀max hX3 b hb0 hBu
  -- the three-way split of the prime sum
  have hfe : (((Finset.Icc 1 x).filter Nat.Prime).filter
        (fun p => ¬ p < y)).filter (fun p => x < 2*p)
      = ((Finset.Icc 1 x).filter Nat.Prime).filter (fun p => x < 2*p) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hS, _⟩, h2⟩
      exact ⟨hS, h2⟩
    · rintro ⟨hS, h2⟩
      exact ⟨⟨hS, by omega⟩, h2⟩
  have hsplit1 := Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 x).filter Nat.Prime) (fun p => p < y)
    (fun p => f p * vonMangoldt p
      * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
          f m * (Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ)))
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    (((Finset.Icc 1 x).filter Nat.Prime).filter (fun p => ¬ p < y))
    (fun p => x < 2*p)
    (fun p => f p * vonMangoldt p
      * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
          f m * (Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ)))
  rw [hfe] at hsplit2
  -- name the five quantities
  set A := (∑ n ∈ Finset.Icc 1 x,
      f n * (Real.log (x:ℝ) - Real.log (n:ℝ))) * Real.log (x:ℝ) with hA_def
  set H := ∑ p ∈ ((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => p < y),
      f p * vonMangoldt p
        * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
            f m * (Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ)) with hH_def
  set Tl := ∑ p ∈ ((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => x < 2*p),
      f p * vonMangoldt p
        * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
            f m * (Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ)) with hTl_def
  set Sv := ∑ p ∈ (((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p),
      f p * vonMangoldt p
        * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
            f m * (Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ)) with hSv_def
  set C := tripleConvR f x ((((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p)) with hC_def
  set Sp := ∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime,
      f p * vonMangoldt p
        * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
            f m * (Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ)) with hSp_def
  -- the split as an equation between the named sums
  have hSp : Sp = H + (Tl + Sv) := by
    rw [← hsplit1, ← hsplit2]
  -- triangle chain
  have habs1 : |A| ≤ |A - Sp| + |Sp| := by
    have h : A = (A - Sp) + Sp := by ring
    calc |A| = |(A - Sp) + Sp| := by rw [← h]
      _ ≤ |A - Sp| + |Sp| := abs_add_le _ _
  have habs2 : |Sp| ≤ |H| + (|Tl| + |Sv|) := by
    rw [hSp]
    calc |H + (Tl + Sv)| ≤ |H| + |Tl + Sv| := abs_add_le _ _
      _ ≤ |H| + (|Tl| + |Sv|) := by
          have := abs_add_le Tl Sv
          linarith
  have habs3 : |Sv| ≤ |Sv - C| + |C| := by
    have h : Sv = (Sv - C) + C := by ring
    calc |Sv| = |(Sv - C) + C| := by rw [← h]
      _ ≤ |Sv - C| + |C| := abs_add_le _ _
  have hsum := add_le_add hid (add_le_add hhead (add_le_add htail
    (add_le_add hbridge hconv)))
  have hchain : |A| ≤ |A - Sp| + (|H| + (|Tl| + (|Sv - C| + |C|))) := by
    linarith [habs1, habs2, habs3]
  linarith [le_trans hchain hsum]


open Real Finset in
/-- **The blocks are inhabited at the window** (Track R, N206a): below
`K₀` the discarded range is at most `x·e^{−e²log 2} < x/147`, so every
block quotient `x / blockLo x k` is at least `3` — the `hX3`
hypothesis of the balanced estimate, discharged. -/
theorem three_le_div_blockLo (x K₀ : ℕ) (hx : 10^16 ≤ x)
    (hK₀low : Real.exp 1 * Real.log 2
      ≤ Real.exp (-(K₀:ℝ)) * Real.log (x:ℝ)) :
    ∀ k ∈ Finset.Icc 1 K₀, 3 ≤ x / blockLo x k := by
  intro k hk
  rw [Finset.mem_Icc] at hk
  have hx1 : (1:ℕ) ≤ x := le_trans (by norm_num) hx
  have hx0 : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hxR : (10:ℝ)^16 ≤ (x:ℝ) := by exact_mod_cast hx
  have hL0 : (0:ℝ) < Real.log (x:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : (1:ℕ) < x))
  -- the damping exponent is at least `e²·log 2` throughout the window
  have hmono : Real.exp (-(K₀:ℝ)) ≤ Real.exp (-(k:ℝ) + 1 - 1) := by
    rw [Real.exp_le_exp]
    have : (k:ℝ) ≤ (K₀:ℝ) := by exact_mod_cast hk.2
    linarith
  have hexp : Real.exp 1 * (Real.exp 1 * Real.log 2)
      ≤ Real.exp (1 - (k:ℝ)) * Real.log (x:ℝ) := by
    have h1 : Real.exp (1 - (k:ℝ))
        = Real.exp 1 * Real.exp (-(k:ℝ)) := by
      rw [← Real.exp_add]
      congr 1
    rw [h1, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
    calc Real.exp 1 * Real.log 2
        ≤ Real.exp (-(K₀:ℝ)) * Real.log (x:ℝ) := hK₀low
      _ ≤ Real.exp (-(k:ℝ)) * Real.log (x:ℝ) := by
          have := hmono
          have h2 : Real.exp (-(K₀:ℝ)) ≤ Real.exp (-(k:ℝ)) := by
            rw [Real.exp_le_exp]
            have : (k:ℝ) ≤ (K₀:ℝ) := by exact_mod_cast hk.2
            linarith
          exact mul_le_mul_of_nonneg_right h2 hL0.le
  -- `exp(e²·log2) ≥ 147`
  have ha : (2.718:ℝ) ≤ Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have hlog2l : (0.693:ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hb : (7.38:ℝ) ≤ (Real.exp 1)^2 := by nlinarith [ha]
  have h5 : (5:ℝ) ≤ Real.exp 1 * (Real.exp 1 * Real.log 2) := by
    nlinarith [hb, hlog2l]
  have hc : (54.4:ℝ) ≤ (Real.exp 1)^4 := by nlinarith [hb]
  have hd : (147:ℝ) ≤ (Real.exp 1)^5 := by nlinarith [hc, ha]
  have h15 : Real.exp (5:ℝ) = (Real.exp 1)^(5:ℕ) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have he5 : (147:ℝ) ≤ Real.exp (Real.exp 1 * (Real.exp 1 * Real.log 2)) := by
    calc (147:ℝ) ≤ (Real.exp 1)^(5:ℕ) := hd
      _ = Real.exp (5:ℝ) := h15.symm
      _ ≤ Real.exp (Real.exp 1 * (Real.exp 1 * Real.log 2)) := by
          rw [Real.exp_le_exp]
          exact h5
  -- the discarded range is tiny
  have hpow : (x:ℝ) ^ (1 - Real.exp (1 - (k:ℝ)))
      ≤ (x:ℝ) * (1/147) := by
    rw [Real.rpow_def_of_pos hx0]
    have h1 : Real.log (x:ℝ) * (1 - Real.exp (1 - (k:ℝ)))
        = Real.log (x:ℝ)
          + (-(Real.exp (1 - (k:ℝ)) * Real.log (x:ℝ))) := by
      ring
    rw [h1, Real.exp_add, Real.exp_log hx0]
    refine mul_le_mul_of_nonneg_left ?_ hx0.le
    have h2 : Real.exp (-(Real.exp (1 - (k:ℝ)) * Real.log (x:ℝ)))
        ≤ Real.exp (-(Real.exp 1 * (Real.exp 1 * Real.log 2))) := by
      rw [Real.exp_le_exp]
      linarith [hexp]
    refine le_trans h2 ?_
    rw [Real.exp_neg]
    have h3 : (0:ℝ) < 147 := by norm_num
    calc (Real.exp (Real.exp 1 * (Real.exp 1 * Real.log 2)))⁻¹
        = 1 / Real.exp (Real.exp 1 * (Real.exp 1 * Real.log 2)) := by
          rw [one_div]
      _ ≤ 1/147 := one_div_le_one_div_of_le h3 he5
  -- `3·blockLo ≤ x`, hence the nat quotient is at least 3
  have hceil : ((blockLo x k : ℕ):ℝ)
      < (x:ℝ) * (1/147) + 1 := by
    rw [blockLo]
    calc ((⌈(x:ℝ) ^ (1 - Real.exp (1 - (k:ℝ)))⌉₊ : ℕ):ℝ)
        < (x:ℝ) ^ (1 - Real.exp (1 - (k:ℝ))) + 1 :=
          Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le _)
      _ ≤ (x:ℝ) * (1/147) + 1 := by linarith [hpow]
  have h3b : 3 * blockLo x k ≤ x := by
    have h1 : (3:ℝ) * ((blockLo x k : ℕ):ℝ) < (x:ℝ) := by
      have := hceil
      nlinarith [hxR]
    have h2 : ((3 * blockLo x k : ℕ):ℝ) < ((x:ℕ):ℝ) := by
      push_cast
      linarith [h1]
    exact le_of_lt (by exact_mod_cast h2)
  have hpos : 0 < blockLo x k := by
    rw [blockLo]
    refine Nat.ceil_pos.mpr ?_
    exact Real.rpow_pos_of_pos hx0 _
  exact (Nat.le_div_iff_mul_le hpos).mpr (by omega)


open Real Finset in
/-- **§3 under non-pretentiousness** (Track R, N206b): the end-to-end
bound `rieszMean_log_le_of_nonPretentious` specialised to the
`y₂`-smooth restriction of `f`, with the band hypothesis discharged by
`bandSup_smooth_restrict_of_nonPretentious` and the block hypothesis
by `three_le_div_blockLo`.  All analytic input is now
`NonPretentiousAt`. -/
theorem rieszMean_log_le_smooth_of_nonPretentious (f : ℕ → ℝ)
    (hcm : CompletelyMultiplicativeC (fun n => ((f n : ℝ) : ℂ)))
    (h1 : f 1 = 1) (hf : ∀ n, |f n| ≤ 1)
    (hmul : ∀ a b, f (a*b) = f a * f b)
    (x y y₂ K₀ : ℕ) (hx : 10^16 ≤ x) (hy2 : 2 ≤ y) (hyx : 2*y ≤ x)
    (hy₂ : 1 ≤ y₂) (hy₂x : y₂ ≤ x)
    (T : ℝ) (hT1 : Real.sqrt (21 * Real.log (x:ℝ)) ≤ T)
    (hT2 : T ≤ Real.log (x:ℝ)) (hTy : T^2 ≤ (y:ℝ))
    (hK₀1 : 1 ≤ K₀)
    (hK₀low : Real.exp 1 * Real.log 2
      ≤ Real.exp (-(K₀:ℝ)) * Real.log (x:ℝ))
    (hK₀max : Real.exp (-((K₀:ℝ)+1)) * Real.log (x:ℝ)
      < Real.exp 1 * Real.log 2)
    (A : ℝ) (hA : NonPretentiousAt (fun n => ((f n : ℝ) : ℂ)) A x)
    (h1A : 1 ≤ A)
    (hband : 7 * (((halaszM x : ℕ):ℝ) + 1) ≤ A * (x:ℝ))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    |(∑ n ∈ Finset.Icc 1 x,
        (if n ∈ Nat.smoothNumbers y₂ then f n else 0)
          * (Real.log (x:ℝ) - Real.log (n:ℝ))) * Real.log (x:ℝ)|
      ≤ 35*(x:ℝ) + (x:ℝ)*(Real.log (y:ℝ) + 2) + 2*((x:ℝ)+1)*Real.log 4
        + 64 * (x:ℝ) / Real.log 2 * (Real.log ((x+1:ℕ):ℝ) + 2)
        + ((K₀:ℝ) * ((x:ℝ) * Real.sqrt ((Real.exp π)^2 * 10^15
              * (((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1)
                * (Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - A
                      + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
                        - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
                    + (x:ℝ)^(-δ)
                      * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹)^2
                + 1))
            + 2*(x:ℝ)*Real.log 4)
          + 2 * ((x:ℝ) * (16 * ((Real.exp 1 - 1) * (Real.exp 1 * Real.log 2)
              + Real.log 2) + 16 * Real.log 4))) := by
  classical
  have hx1 : (1:ℕ) ≤ x := le_trans (by norm_num) hx
  have hb0 : (0:ℝ) ≤ Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - A
        + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
          - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
      + (x:ℝ)^(-δ) * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹ := by
    have h2 : (0:ℝ) ≤ (x:ℝ)^(-δ)
        * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹ := by
      refine mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) _) ?_
      refine Finset.prod_nonneg fun p hp => ?_
      have hp2 : 2 ≤ p := (Nat.mem_primesBelow.mp hp).2.two_le
      have hp1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp2
      have hlt : (p:ℝ)^(δ-1) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
      exact inv_nonneg.mpr (by linarith)
    exact add_nonneg (Real.exp_pos _).le h2
  exact rieszMean_log_le_of_nonPretentious
    (fun n => if n ∈ Nat.smoothNumbers y₂ then f n else 0)
    (smooth_restrict_abs_le f y₂ hf)
    (smooth_restrict_mul f y₂ hmul)
    x y K₀ hx hy2 hyx T hT1 hT2 hTy hK₀1 hK₀low hK₀max
    (three_le_div_blockLo x K₀ hx hK₀low)
    _ hb0
    (bandSup_smooth_restrict_of_nonPretentious f hcm h1 hf y₂ x
      hy₂ hy₂x hx1 A hA h1A hband δ hδ0 hδ1)


open Real Finset in
/-- **The §3 window, witnessed** (Track R, N206c): at any `x ≥ 10¹⁶`
the whole window package exists — `T` from `exists_window_T`, `K₀`
from `exists_K₀`, and `y := ⌈T²⌉` sits between `T²` and `x/2` because
`log²x ≤ 9·x^{2/3}`.  Consumers destructure this and feed
`rieszMean_log_le_smooth_of_nonPretentious`. -/
theorem exists_section3_window (x : ℕ) (hx : 10^16 ≤ x) :
    ∃ (y K₀ : ℕ) (T : ℝ),
      2 ≤ y ∧ 2*y ≤ x
      ∧ Real.sqrt (21 * Real.log (x:ℝ)) ≤ T ∧ T ≤ Real.log (x:ℝ)
      ∧ T^2 ≤ (y:ℝ)
      ∧ (y:ℝ) ≤ 2*(Real.log (x:ℝ))^2
      ∧ 1 ≤ K₀
      ∧ Real.exp 1 * Real.log 2
          ≤ Real.exp (-(K₀:ℝ)) * Real.log (x:ℝ)
      ∧ Real.exp (-((K₀:ℝ)+1)) * Real.log (x:ℝ)
          < Real.exp 1 * Real.log 2 := by
  obtain ⟨T, hT1, hT2⟩ := exists_window_T x hx
  obtain ⟨K₀, hK₀1, hK₀low, hK₀max⟩ := exists_K₀ x hx
  have hx1 : (1:ℕ) ≤ x := le_trans (by norm_num) hx
  have hx0 : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hxR : (10:ℝ)^16 ≤ (x:ℝ) := by exact_mod_cast hx
  have hL0 : (0:ℝ) ≤ Real.log (x:ℝ) := Real.log_natCast_nonneg x
  have hT0 : (0:ℝ) ≤ T := le_trans (Real.sqrt_nonneg _) hT1
  -- `21·L ≤ T²` and `L ≥ 32`
  have hTsq : 21 * Real.log (x:ℝ) ≤ T^2 := by
    have h := mul_self_le_mul_self
      (Real.sqrt_nonneg (21 * Real.log (x:ℝ))) hT1
    rw [Real.mul_self_sqrt (by positivity)] at h
    rw [pow_two]
    exact h
  have hL32 : (32:ℝ) ≤ Real.log (x:ℝ) := by
    have he_lt : Real.exp 1 ≤ (2.7182818286:ℝ) := Real.exp_one_lt_d9.le
    have hlog10 : (2:ℝ) ≤ Real.log 10 := by
      have h1 : Real.exp 2 ≤ 10 := by
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]
          norm_num
        nlinarith [Real.exp_pos 1, he_lt]
      calc (2:ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
        _ ≤ Real.log 10 := Real.log_le_log (Real.exp_pos 2) h1
    have h1 : Real.log ((10:ℝ)^16) = 16 * Real.log 10 := by
      rw [Real.log_pow]
      push_cast
      ring
    have h2 : Real.log ((10:ℝ)^16) ≤ Real.log (x:ℝ) :=
      Real.log_le_log (by positivity) hxR
    nlinarith [hlog10]
  have hceil : ((⌈T^2⌉₊:ℕ):ℝ) < T^2 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hTL : T^2 ≤ (Real.log (x:ℝ))^2 := by
    have h := mul_self_le_mul_self hT0 hT2
    rw [pow_two, pow_two]
    exact h
  refine ⟨⌈T^2⌉₊, K₀, T, ?_, ?_, hT1, hT2, Nat.le_ceil _, ?_,
    hK₀1, hK₀low, hK₀max⟩
  · -- `2 ≤ ⌈T²⌉`
    have h2 : (1:ℕ) < ⌈T^2⌉₊ := by
      rw [Nat.lt_ceil]
      push_cast
      nlinarith [hTsq, hL32]
    omega
  · -- `2·⌈T²⌉ ≤ x` via `L² ≤ 9·x^{2/3}`
    have hLcube : Real.log (x:ℝ) ≤ 3 * (x:ℝ) ^ ((1:ℝ)/3) :=
      log_le_three_rpow_third (x:ℝ) (by exact_mod_cast hx1)
    have hx13 : (x:ℝ)^((1:ℝ)/3) * (x:ℝ)^((1:ℝ)/3) = (x:ℝ)^((2:ℝ)/3) := by
      rw [← Real.rpow_add hx0]
      norm_num
    have hL2 : (Real.log (x:ℝ))^2 ≤ 9 * (x:ℝ)^((2:ℝ)/3) := by
      have h9 := mul_self_le_mul_self hL0 hLcube
      rw [pow_two]
      calc Real.log (x:ℝ) * Real.log (x:ℝ)
          ≤ (3*(x:ℝ)^((1:ℝ)/3)) * (3*(x:ℝ)^((1:ℝ)/3)) := h9
        _ = 9 * (x:ℝ)^((2:ℝ)/3) := by
            rw [← hx13]
            ring
    have h20 : (20:ℝ) ≤ (x:ℝ)^((1:ℝ)/3) := by
      have h8000 : (8000:ℝ) ≤ (x:ℝ) := by linarith [hxR]
      have h1 : (20:ℝ) = (8000:ℝ)^((1:ℝ)/3) := by
        rw [show (8000:ℝ) = 20^(3:ℕ) by norm_num,
          ← Real.rpow_natCast (20:ℝ) 3, ← Real.rpow_mul (by norm_num)]
        norm_num
      rw [h1]
      exact Real.rpow_le_rpow (by norm_num) h8000 (by norm_num)
    have hx23 : 20 * (x:ℝ)^((2:ℝ)/3) ≤ (x:ℝ) := by
      have hxx : (x:ℝ)^((2:ℝ)/3) * (x:ℝ)^((1:ℝ)/3) = (x:ℝ) := by
        rw [← Real.rpow_add hx0]
        norm_num
      calc 20 * (x:ℝ)^((2:ℝ)/3)
          ≤ (x:ℝ)^((1:ℝ)/3) * (x:ℝ)^((2:ℝ)/3) := by
            refine mul_le_mul_of_nonneg_right h20 ?_
            exact Real.rpow_nonneg hx0.le _
        _ = (x:ℝ) := by
            rw [mul_comm]
            exact hxx
    have hr : ((2 * ⌈T^2⌉₊ : ℕ):ℝ) < (x:ℝ) := by
      push_cast
      linarith [hceil, hTL, hL2, hx23, hxR]
    exact le_of_lt (by exact_mod_cast hr)
  · -- `⌈T²⌉ ≤ 2·L²`
    have hL1024 : (1024:ℝ) ≤ (Real.log (x:ℝ))^2 := by
      nlinarith [hL32]
    linarith [hceil, hTL, hL1024]


open Real Finset in
set_option maxHeartbeats 3200000 in
/-- **§3, priced** (Track R, N206d): the closed form.  Destructuring
`exists_section3_window` into `rieszMean_log_le_smooth_of_nonPretentious`
and pricing every window quantity — `K₀ ≤ log log x`, `T ≤ log x`,
`log⌈T²⌉ ≤ 2 log log x + 1`, `log y ≤ 2 log log x + 1`,
`log(x+1) ≤ log x + 1`, `64/log 2 ≤ 92.4` — gives §3's bound as an
explicit function of `x` alone (and the Halász band constant `B`). -/
theorem rieszMean_log_le_closed (f : ℕ → ℝ)
    (hcm : CompletelyMultiplicativeC (fun n => ((f n : ℝ) : ℂ)))
    (h1 : f 1 = 1) (hf : ∀ n, |f n| ≤ 1)
    (hmul : ∀ a b, f (a*b) = f a * f b)
    (x y₂ : ℕ) (hx : 10^16 ≤ x) (hy₂ : 1 ≤ y₂) (hy₂x : y₂ ≤ x)
    (A : ℝ) (hA : NonPretentiousAt (fun n => ((f n : ℝ) : ℂ)) A x)
    (h1A : 1 ≤ A)
    (hband : 7 * (((halaszM x : ℕ):ℝ) + 1) ≤ A * (x:ℝ))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    |(∑ n ∈ Finset.Icc 1 x,
        (if n ∈ Nat.smoothNumbers y₂ then f n else 0)
          * (Real.log (x:ℝ) - Real.log (n:ℝ))) * Real.log (x:ℝ)|
      ≤ (x:ℝ) * (93 * Real.log (x:ℝ)
            + 2 * Real.log (Real.log (x:ℝ)) + 491)
        + Real.log (Real.log (x:ℝ)) * (x:ℝ)
          * (Real.sqrt ((Real.exp π)^2 * 10^15
              * (((2 * Real.log (Real.log (x:ℝ)) + 3)^2
                  + Real.log (x:ℝ) + 1)
                * (Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - A
                      + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
                        - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
                    + (x:ℝ)^(-δ)
                      * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹)^2
                + 1)) + 3) := by
  classical
  obtain ⟨y, K₀, T, hy2, hyx, hT1, hT2, hTy, hyUB, hK₀1, hK₀low, hK₀max⟩ :=
    exists_section3_window x hx
  have hmain := rieszMean_log_le_smooth_of_nonPretentious f hcm h1 hf hmul
    x y y₂ K₀ hx hy2 hyx hy₂ hy₂x T hT1 hT2 hTy hK₀1 hK₀low hK₀max
    A hA h1A hband δ hδ0 hδ1
  -- shared numerics
  have hx1 : (1:ℕ) ≤ x := le_trans (by norm_num) hx
  have hx0 : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hxR : (10:ℝ)^16 ≤ (x:ℝ) := by exact_mod_cast hx
  have hL32 : (32:ℝ) ≤ Real.log (x:ℝ) := by
    have he_lt : Real.exp 1 ≤ (2.7182818286:ℝ) := Real.exp_one_lt_d9.le
    have hlog10 : (2:ℝ) ≤ Real.log 10 := by
      have h1' : Real.exp 2 ≤ 10 := by
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]
          norm_num
        nlinarith [Real.exp_pos 1, he_lt]
      calc (2:ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
        _ ≤ Real.log 10 := Real.log_le_log (Real.exp_pos 2) h1'
    have h1' : Real.log ((10:ℝ)^16) = 16 * Real.log 10 := by
      rw [Real.log_pow]
      push_cast
      ring
    have h2 : Real.log ((10:ℝ)^16) ≤ Real.log (x:ℝ) :=
      Real.log_le_log (by positivity) hxR
    nlinarith [hlog10]
  have hL0 : (0:ℝ) < Real.log (x:ℝ) := by linarith
  have hLL1 : (1:ℝ) ≤ Real.log (Real.log (x:ℝ)) := by
    have he_lt : Real.exp 1 ≤ (2.7182818286:ℝ) := Real.exp_one_lt_d9.le
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (Real.log (x:ℝ)) :=
          Real.log_le_log (Real.exp_pos 1) (by linarith)
  have hlog2l : (0.693:ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlog2u : Real.log 2 ≤ (0.694:ℝ) := by
    have := Real.log_two_lt_d9
    linarith
  have hlog2pos : (0:ℝ) < Real.log 2 := by linarith
  have hlog4 : Real.log 4 ≤ (1.388:ℝ) := by
    rw [show (4:ℝ) = 2^(2:ℕ) by norm_num, Real.log_pow]
    push_cast
    linarith
  have hlog40 : (0:ℝ) ≤ Real.log 4 :=
    Real.log_nonneg (by norm_num)
  have hT0 : (0:ℝ) ≤ T := le_trans (Real.sqrt_nonneg _) hT1
  have hTpos : (0:ℝ) < T := by
    refine lt_of_lt_of_le ?_ hT1
    exact Real.sqrt_pos.mpr (by nlinarith [hL32])
  -- the two ceiling logs
  have hTL2 : T^2 ≤ (Real.log (x:ℝ))^2 := by
    have h := mul_self_le_mul_self hT0 hT2
    rw [pow_two, pow_two]
    exact h
  have hL2ge1 : (1:ℝ) ≤ (Real.log (x:ℝ))^2 := by nlinarith [hL32]
  have hceilUB : ((⌈T^2⌉₊:ℕ):ℝ) ≤ 2*(Real.log (x:ℝ))^2 := by
    have h := Nat.ceil_lt_add_one (le_of_lt (by positivity : (0:ℝ) < T^2))
    linarith [hTL2, hL2ge1, h]
  have hlog2L : Real.log (2*(Real.log (x:ℝ))^2)
      = Real.log 2 + 2 * Real.log (Real.log (x:ℝ)) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  have hlogceil : Real.log ((⌈T^2⌉₊:ℕ):ℝ)
      ≤ 2 * Real.log (Real.log (x:ℝ)) + 1 := by
    have hpos : (0:ℝ) < ((⌈T^2⌉₊:ℕ):ℝ) := by
      have : 0 < ⌈T^2⌉₊ := Nat.ceil_pos.mpr (by positivity)
      exact_mod_cast this
    calc Real.log ((⌈T^2⌉₊:ℕ):ℝ)
        ≤ Real.log (2*(Real.log (x:ℝ))^2) :=
          Real.log_le_log hpos hceilUB
      _ = Real.log 2 + 2 * Real.log (Real.log (x:ℝ)) := hlog2L
      _ ≤ 2 * Real.log (Real.log (x:ℝ)) + 1 := by linarith
  have hlogy : Real.log (y:ℝ)
      ≤ 2 * Real.log (Real.log (x:ℝ)) + 1 := by
    have hpos : (0:ℝ) < (y:ℝ) := by exact_mod_cast (by omega : 0 < y)
    calc Real.log (y:ℝ)
        ≤ Real.log (2*(Real.log (x:ℝ))^2) :=
          Real.log_le_log hpos hyUB
      _ = Real.log 2 + 2 * Real.log (Real.log (x:ℝ)) := hlog2L
      _ ≤ 2 * Real.log (Real.log (x:ℝ)) + 1 := by linarith
  -- `log(x+1) ≤ log x + 1`
  have hlogx1 : Real.log ((x+1:ℕ):ℝ) ≤ Real.log (x:ℝ) + 1 := by
    have h1' : ((x+1:ℕ):ℝ) ≤ Real.exp 1 * (x:ℝ) := by
      have he_gt : (2.7182818283:ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
      push_cast
      nlinarith [hxR]
    calc Real.log ((x+1:ℕ):ℝ)
        ≤ Real.log (Real.exp 1 * (x:ℝ)) :=
          Real.log_le_log (by positivity) h1'
      _ = 1 + Real.log (x:ℝ) := by
          rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hx0),
            Real.log_exp]
      _ = Real.log (x:ℝ) + 1 := by ring
  -- `K₀ ≤ log log x`
  have hK₀LL : (K₀:ℝ) ≤ Real.log (Real.log (x:ℝ)) := by
    have h2 : Real.exp (K₀:ℝ) * (Real.exp (-(K₀:ℝ)) * Real.log (x:ℝ))
        = Real.log (x:ℝ) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    have h1' : Real.exp (K₀:ℝ) * (Real.exp 1 * Real.log 2)
        ≤ Real.log (x:ℝ) := by
      have := mul_le_mul_of_nonneg_left hK₀low (Real.exp_pos (K₀:ℝ)).le
      rwa [h2] at this
    have h3 : Real.exp (K₀:ℝ) ≤ Real.log (x:ℝ) := by
      have he_gt : (2.7182818283:ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
      have h4 : (1:ℝ) ≤ Real.exp 1 * Real.log 2 := by
        nlinarith [he_gt, hlog2l]
      nlinarith [Real.exp_pos (K₀:ℝ), h4, h1']
    calc (K₀:ℝ) = Real.log (Real.exp (K₀:ℝ)) := (Real.log_exp _).symm
      _ ≤ Real.log (Real.log (x:ℝ)) :=
          Real.log_le_log (Real.exp_pos _) h3
  have hLL0 : (0:ℝ) ≤ Real.log (Real.log (x:ℝ)) := by linarith
  -- the square-root monotonicity
  have hB2 : (0:ℝ) ≤ (Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - A
        + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
          - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
      + (x:ℝ)^(-δ) * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹)^2 :=
    sq_nonneg _
  have hsq : (Real.log ((⌈T^2⌉₊:ℕ):ℝ) + 2)^2
      ≤ (2 * Real.log (Real.log (x:ℝ)) + 3)^2 := by
    have h0 : (0:ℝ) ≤ Real.log ((⌈T^2⌉₊:ℕ):ℝ) :=
      Real.log_natCast_nonneg _
    nlinarith [hlogceil, h0, hLL0]
  have hinner : (Real.exp π)^2 * 10^15
        * (((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1)
          * (Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - A
                + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
                  - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
              + (x:ℝ)^(-δ)
                * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹)^2
          + 1)
      ≤ (Real.exp π)^2 * 10^15
        * (((2 * Real.log (Real.log (x:ℝ)) + 3)^2
            + Real.log (x:ℝ) + 1)
          * (Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - A
                + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
                  - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
              + (x:ℝ)^(-δ)
                * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹)^2
          + 1) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact add_le_add (mul_le_mul_of_nonneg_right
      (by linarith [hsq, hT2]) hB2) le_rfl
  have hsqrt := Real.sqrt_le_sqrt hinner
  -- price each summand of `hmain`
  have hp2 : (x:ℝ)*(Real.log (y:ℝ) + 2)
      ≤ (x:ℝ)*(2 * Real.log (Real.log (x:ℝ)) + 3) := by
    refine mul_le_mul_of_nonneg_left ?_ hx0.le
    linarith [hlogy]
  have hp3 : 2*((x:ℝ)+1)*Real.log 4 ≤ (2.79:ℝ)*(x:ℝ) := by
    nlinarith [hlog4, hlog40, hxR]
  have hp4 : 64 * (x:ℝ) / Real.log 2 * (Real.log ((x+1:ℕ):ℝ) + 2)
      ≤ 92.4*(x:ℝ) * (Real.log (x:ℝ) + 3) := by
    have hd : 64 * (x:ℝ) / Real.log 2 ≤ 92.4*(x:ℝ) := by
      rw [div_le_iff₀ hlog2pos]
      nlinarith [hlog2l, hx0.le]
    have hnn : (0:ℝ) ≤ Real.log ((x+1:ℕ):ℝ) + 2 := by
      have := Real.log_natCast_nonneg (x+1)
      linarith
    have hup : Real.log ((x+1:ℕ):ℝ) + 2 ≤ Real.log (x:ℝ) + 3 := by
      linarith [hlogx1]
    calc 64 * (x:ℝ) / Real.log 2 * (Real.log ((x+1:ℕ):ℝ) + 2)
        ≤ 92.4*(x:ℝ) * (Real.log ((x+1:ℕ):ℝ) + 2) :=
          mul_le_mul_of_nonneg_right hd hnn
      _ ≤ 92.4*(x:ℝ) * (Real.log (x:ℝ) + 3) := by
          refine mul_le_mul_of_nonneg_left hup (by positivity)
  have hp5 : (K₀:ℝ) * ((x:ℝ) * Real.sqrt ((Real.exp π)^2 * 10^15
        * (((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1)
          * (Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - A
                + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
                  - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
              + (x:ℝ)^(-δ)
                * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹)^2
          + 1)) + 2*(x:ℝ)*Real.log 4)
      ≤ Real.log (Real.log (x:ℝ)) * ((x:ℝ)
          * Real.sqrt ((Real.exp π)^2 * 10^15
            * (((2 * Real.log (Real.log (x:ℝ)) + 3)^2
                + Real.log (x:ℝ) + 1)
              * (Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - A
                    + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
                      - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
                  + (x:ℝ)^(-δ)
                    * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹)^2
              + 1)) + 3*(x:ℝ)) := by
    have hK₀0 : (0:ℝ) ≤ (K₀:ℝ) := Nat.cast_nonneg _
    have hs1 : (x:ℝ) * Real.sqrt ((Real.exp π)^2 * 10^15
          * (((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1)
            * (Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - A
                  + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
                    - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
                + (x:ℝ)^(-δ)
                  * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹)^2
            + 1)) + 2*(x:ℝ)*Real.log 4
        ≤ (x:ℝ) * Real.sqrt ((Real.exp π)^2 * 10^15
            * (((2 * Real.log (Real.log (x:ℝ)) + 3)^2
                + Real.log (x:ℝ) + 1)
              * (Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - A
                    + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
                      - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
                  + (x:ℝ)^(-δ)
                    * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹)^2
              + 1)) + 3*(x:ℝ) := by
      have h1' := mul_le_mul_of_nonneg_left hsqrt hx0.le
      nlinarith [hlog4, hx0.le, h1']
    have hs0 : (0:ℝ) ≤ (x:ℝ) * Real.sqrt ((Real.exp π)^2 * 10^15
          * (((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1)
            * (Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - A
                  + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
                    - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
                + (x:ℝ)^(-δ)
                  * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹)^2
            + 1)) + 2*(x:ℝ)*Real.log 4 := by
      have := Real.sqrt_nonneg ((Real.exp π)^2 * 10^15
          * (((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1)
            * (Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - A
                  + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
                    - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
                + (x:ℝ)^(-δ)
                  * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹)^2
            + 1))
      nlinarith [hx0.le, hlog40]
    exact mul_le_mul hK₀LL hs1 hs0 hLL0
  have hp6 : 2 * ((x:ℝ) * (16 * ((Real.exp 1 - 1)
        * (Real.exp 1 * Real.log 2) + Real.log 2) + 16 * Real.log 4))
      ≤ 171*(x:ℝ) := by
    have he_lt : Real.exp 1 ≤ (2.7182818286:ℝ) := Real.exp_one_lt_d9.le
    have he_gt : (2.7182818283:ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
    have hprod : (Real.exp 1 - 1) * (Real.exp 1 * Real.log 2)
        ≤ (3.25:ℝ) := by
      have h1' : (0:ℝ) ≤ Real.exp 1 - 1 := by linarith
      have h2 : Real.exp 1 * Real.log 2 ≤ (1.887:ℝ) := by
        nlinarith [he_lt, hlog2u, hlog2l, he_gt]
      have h3 : Real.exp 1 - 1 ≤ (1.719:ℝ) := by linarith
      have h4 : (0:ℝ) ≤ Real.exp 1 * Real.log 2 := by
        nlinarith [he_gt, hlog2l]
      nlinarith [h1', h2, h3, h4]
    have hconst : 16 * ((Real.exp 1 - 1)
        * (Real.exp 1 * Real.log 2) + Real.log 2) + 16 * Real.log 4
        ≤ (85.5:ℝ) := by
      linarith [hprod, hlog4, hlog2u]
    nlinarith [hconst, hx0.le, hlog40, hlog2l, hprod]
  have hxL0 : (0:ℝ) ≤ (x:ℝ) * Real.log (x:ℝ) :=
    mul_nonneg hx0.le (by linarith)
  have hxLL0 : (0:ℝ) ≤ (x:ℝ) * Real.log (Real.log (x:ℝ)) :=
    mul_nonneg hx0.le hLL0
  linarith [hmain, hp2, hp3, hp4, hp5, hp6, hxR, hL32, hLL1, hx0,
    hxL0, hxLL0]

end MoltResearch
