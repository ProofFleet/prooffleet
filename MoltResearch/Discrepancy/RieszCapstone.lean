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

end MoltResearch
