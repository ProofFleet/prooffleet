import MoltResearch.Discrepancy

/-!
# Track C: Stage 5 — the large-values interfaces (issue #3044, Track R, A2-III IV-1/IV-2)

Two quotable literature statements about **large values of Dirichlet polynomials**:
one for integer-supported polynomials, one for prime-supported ones.

Why they are here rather than proved.  The `[mrt]` A.2 band estimate closes
elementarily on every frequency range except the exceptional set `𝒰`, and the
`𝒰` leg provably does not: sup-times-measure is circular, continuous integration
loses `exp(log A/loglog A)`, and even full discretisation against the *integer*
large-values theorem (`HalaszLargeValuesAssumption` below) misses by `(log A)²`.
The irreducible input is the **prime-supported** large-values theorem
(`PrimeLargeValuesAssumption`), whose only known proof runs through a
Vinogradov–Korobov zero-free region for `ζ` — absent from Mathlib at the pinned
revision.

Recording the boundary explicitly is the point.  The in-tree elementary ladder now
reaches the *measure* of the large-frequency set
(`MoltResearch.measure_large_prime_poly_le`) and the measure-to-count bridge for
general polynomials (`MoltResearch.ExpSums.sum_norm_sq_le_integral_of_separated`,
Gallagher).  What these two classes add is exactly the prime-supported count, and
nothing else.

Sources:

- Iwaniec–Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53 (2004),
  Theorem 9.6 (the mean-value/large-sieve inequality for Dirichlet polynomials at
  well-spaced points, in its stated range `T ≥ 1`).
- Matomäki–Radziwiłł, *Multiplicative functions in short intervals*, Annals of
  Mathematics 183 (2016), Lemma 8 (arXiv:1501.04585).

The integer-supported class is now discharged in
`TrackCStage5LargeValuesDischarge.lean` by the in-tree theorem
`MoltResearch.halaszMontgomery_large_values`.  No instance of the prime-supported
class is declared here until Phase 6 lands: consumers must continue to carry that
theorem of the literature as a hypothesis.  Both statements are transcribed in
`Problems/sources/tao2015_statements.md` and should be diffed against that file,
not against this docstring.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- **Halász large values, integer support** (Iwaniec–Kowalski, *Analytic Number
Theory*, Theorem 9.6): at points of `[-T, T]` that are pairwise `1`-separated, the
squared values of an integer-supported Dirichlet polynomial of length `N` sum to at
most `(N + |𝒯|√T)·log(2T)` times the polynomial's coefficient mass.

The source theorem is stated for `T ≥ 1`; that range is explicit here so the
logarithmic factor is positive even for a singleton set of sample points.

The `64` and the `+1` are slack: any absolute constant serves the consumer, and the
statement is deliberately written with explicit numerals rather than `O(·)` so that
it is checkable against the source.

It is discharged by the in-tree theorem `MoltResearch.halaszMontgomery_large_values`
in `TrackCStage5LargeValuesDischarge.lean`. -/
class HalaszLargeValuesAssumption : Prop where
  bound : ∀ (N : ℕ) (a : ℕ → ℂ) (T : ℝ) (𝒯 : Finset ℝ),
    1 ≤ T → (∀ t ∈ 𝒯, |t| ≤ T) →
    (∀ t ∈ 𝒯, ∀ u ∈ 𝒯, t ≠ u → 1 ≤ |t - u|) →
    ∑ t ∈ 𝒯, ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
        * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖^2
      ≤ 64 * ((N:ℝ) + (𝒯.card:ℝ) * Real.sqrt T) * (Real.log (2*T) + 1)
          * ∑ n ∈ Finset.Icc 1 N, ‖a n‖^2/(n:ℝ)^2

/-- The exponent of the prime large-values saving: Chudakov's region
`1 − c/((log t)^{3/4}(loglog t)^{3/4})` beats `(log t)^{−4/5}`. -/
noncomputable def primeLargeValuesExponent : ℝ := 4 / 5

/-- **Halász large values, prime support** (Matomäki–Radziwiłł, Annals 183 (2016),
Lemma 8): for a Dirichlet polynomial supported on primes of a dyadic range
`[P, 2P]`, the count of `1`-separated large points is smaller than the
integer-support bound by a factor
`exp(−log P/(log 2T)^primeLargeValuesExponent)`.

This saving is the whole content, and it is not elementary: the known proof is
duality plus a Mellin shift of `ζ'/ζ` into the Vinogradov–Korobov zero-free region.

The source lemma is used only in its stated large-height range; we record that
range as `T ≥ 1`, which also makes every real power of `log (2*T)` unambiguous.

The source has an `ε`-dependent implied constant and exponent `2/3 + ε`.
Here that constant is recorded honestly by `∃ C`, so it can absorb the
small-height range, and the named exponent is the fixed choice `4/5 < 1` needed
by the consumer.

No instance may be declared until Phase 6 lands — see the module docstring. -/
class PrimeLargeValuesAssumption : Prop where
  bound : ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : ℕ) (Y : Finset ℕ), (∀ p ∈ Y, p.Prime) →
    (∀ p ∈ Y, P ≤ p ∧ p ≤ 2*P) → ∀ (a : ℕ → ℂ) (T : ℝ) (𝒯 : Finset ℝ),
    2 ≤ P → 1 ≤ T → (∀ t ∈ 𝒯, |t| ≤ T) →
    (∀ t ∈ 𝒯, ∀ u ∈ 𝒯, t ≠ u → 1 ≤ |t - u|) →
    ∑ t ∈ 𝒯, ‖∑ p ∈ Y, (a p/(p:ℂ))
        * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖^2
      ≤ C * (1 + (𝒯.card:ℝ)
              * Real.exp (-(Real.log P /
                (Real.log (2*T))^primeLargeValuesExponent))
              * (Real.log (2*T))^2)
          * (∑ p ∈ Y, ‖a p‖^2/(p:ℝ)^2) * (P:ℝ) / Real.log P

end Tao2015

end MoltResearch
