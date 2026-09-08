import MoltResearch.Discrepancy.ChebyshevBlock

/-!
# Upstreaming slot UP-3: Chebyshev's lower bound on dyadic blocks

Pre-allocated leaf for card item UP-3 of `Problems/nucleus_upstreaming.md`. The claimant of UP-3 fills this file with
the Mathlib-style restatement, proved from the imported tree lemmas; no other file is to be edited.
-/

namespace MoltResearch

namespace Upstream

private theorem primesBelow_filter_eq_prime_Ioc (n : ℕ) :
    (2 * n + 1).primesBelow.filter (fun p => n < p) =
      (Finset.Ioc n (2 * n)).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_filter, Nat.mem_primesBelow, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hp_lt, hp_prime⟩, hn_lt⟩
    exact ⟨⟨hn_lt, by omega⟩, hp_prime⟩
  · rintro ⟨⟨hn_lt, hp_le⟩, hp_prime⟩
    exact ⟨⟨by omega, hp_prime⟩, hn_lt⟩

/-- **Chebyshev's dyadic-block lower bound**: the logarithmic mass of the
primes in `(n, 2n]` is at least `(log 4 / 6) n` once `n ≥ 2²⁸`.

This is a Mathlib-style restatement of the classical estimate originating in
P. L. Chebyshev's 1852 memoir *Mémoire sur les nombres premiers*, using the
elementary central-binomial-coefficient proof later popularized by Erdős. -/
theorem sum_log_prime_Ioc_ge {n : ℕ} (hn : 2 ^ 28 ≤ n) :
    (n : ℝ) * Real.log 4 / 6 ≤
      ∑ p ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime, Real.log p := by
  classical
  rw [← primesBelow_filter_eq_prime_Ioc, ← blockLog]
  exact blockLog_ge hn

/-- **Chebyshev's reciprocal-mass corollary**: the primes in `(n, 2n]` have
reciprocal mass at least `(log 4 / 12) / log (2n)` for `n ≥ 2²⁸`.

This is the reciprocal-weight consequence of Chebyshev's classical dyadic
logarithmic-mass estimate (1852). -/
theorem sum_one_div_prime_Ioc_ge {n : ℕ} (hn : 2 ^ 28 ≤ n) :
    Real.log 4 / 12 / Real.log (2 * (n : ℝ)) ≤
      ∑ p ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime, (1 : ℝ) / p := by
  classical
  rw [← primesBelow_filter_eq_prime_Ioc]
  exact sum_one_div_prime_block_ge hn

/-- **Chebyshev's dyadic-block upper bound**: the number of primes in
`(n, 2n]` is at most `2 log(4) n / log n` for `n ≥ 2`.

This explicit form follows from the classical Chebyshev upper bound for the
first Chebyshev function (Chebyshev, 1852). -/
theorem card_prime_Ioc_le {n : ℕ} (hn : 2 ≤ n) :
    (((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℝ) ≤
      2 * (n : ℝ) * Real.log 4 / Real.log n := by
  classical
  rw [← primesBelow_filter_eq_prime_Ioc]
  exact card_block_le hn

example {n : ℕ} (hn : 2 ^ 28 ≤ n) :
    (n : ℝ) * Real.log 4 / 6 ≤
      ∑ p ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime, Real.log p :=
  sum_log_prime_Ioc_ge hn

example {n : ℕ} (hn : 2 ^ 28 ≤ n) :
    Real.log 4 / 12 / Real.log (2 * (n : ℝ)) ≤
      ∑ p ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime, (1 : ℝ) / p :=
  sum_one_div_prime_Ioc_ge hn

example {n : ℕ} (hn : 2 ≤ n) :
    (((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℝ) ≤
      2 * (n : ℝ) * Real.log 4 / Real.log n :=
  card_prime_Ioc_le hn

end Upstream

end MoltResearch
