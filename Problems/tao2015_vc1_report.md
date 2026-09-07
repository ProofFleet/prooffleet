# Track R — V-C1: Codex run 22 final report (2026-09-06/07)

Verbatim final report of Codex run 22 (gpt-5.6-sol, brief `Problems/tao2015_vc1_brief.md`), whose five commits shipped as the V-C1 PR:
the weak explicit Linnik–Karatsuba form of Vinogradov's mean value theorem, `vinogradov_mean_value`, in the new leaf
`MoltResearch/Discrepancy/VinogradovMeanValue.lean` (Mathlib-only imports). Findings: Linnik's Vandermonde step needs `k < p`; the
fundamental lemma uses Vaughan's condition `P < q^k` with primes above `q` (the brief's `p^k ≤ P` pointed the wrong way); a single prime
cannot make both selected blocks non-singular, so a bounded chain of Bertrand primes and the discriminant product are used (Vaughan's
absorption). Commit hashes are the run's, before cherry-pick.

---

# Track R — V-C1 report

## Summary

Completed the weak explicit Linnik–Karatsuba form of Vinogradov's mean value
theorem in the new analytic leaf
`MoltResearch/Discrepancy/VinogradovMeanValue.lean`, registered from
`MoltResearch/DiscrepancyAnalytic.lean`.

The public capstone is:

```lean
theorem vinogradov_mean_value (k : ℕ) (hk : 2 ≤ k) (τ : ℕ) (hτ : 1 ≤ τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℕ, 1 ≤ P →
      (vinogradovJ (k * τ) k P : ℝ) ≤ C * (P : ℝ) ^
        (2 * k * τ - k * (k + 1) / 2 +
          (k ^ 2 / 2) * (1 - 1 / k) ^ τ : ℝ)
```

The chosen witness is recorded as `vinogradovMeanValueConstant k τ`.  Its
construction starts with `k! + 1`; each induction step adds the explicit
nonsingular prime-power contribution, the singular-tuple contribution, and a
finite-range constant for small `P`.

## Units

- V-C1-1 (`cec72d6b`): counting definition and exact solution-system
  characterization, monotonicity, trivial bound, translation invariance,
  representation fibers, Cauchy–Schwarz, and union subadditivity.
- V-C1-2 (`285f9792`): well-conditioned tuples, collision/ill-conditioned
  count, first-block split, and its Cauchy–Schwarz bound.
- V-C1-3 (`a0ee5db6`): Newton identities, Vandermonde/full-moment fibers,
  compatible moment-vector count, and Linnik's prime-power lemma with constant
  `k!`.
- V-C1-4 (`4dbac65b`): finite Fourier/Hölder energy bounds, translation and
  residue decomposition, the Linnik fiber application, coordinate
  permutations, singular-tuple cover, bounded Bertrand-prime family, and the
  fundamental lemma.
- V-C1-5 (`3b027ec8`): diagonal base case, root-scale choice, exact excess
  recursion, singular/nonsingular power estimates, iteration, named constant,
  and the capstone.

## Fundamental lemma recorded

Put

```text
M = (2 * choose(k, 2)) * k + 1
L = 2^M * q
D = k(k - 1)/2.
```

For `0 < r`, `2 ≤ k`, `1 ≤ P`, `k ≤ q`, and `P < q^k`, the proved bound is

```text
J_{r+k,k}(P)
 ≤ 2 ((r+k)!^2 M)
       L^(2r) (2r) P^k k! L^D J_{r,k}(P/q+1)
   + 2 (k P^(k-1) k^(r+k))^2.
```

The first term is the nonsingular contribution.  The second comes from tuples
having fewer than `k` distinct coordinate values.  The bounded prime family
has `M` members and lies below `L`; a discriminant product argument guarantees
that one member separates both selected blocks.

## Findings

- `Problems/tao2015_vc_design_notes.md` is not present in this checkout.  The
  implementation used Phase 6 of
  `Problems/tao2015_a1_r6r7_design_report.md` and Vaughan, Chapter 5,
  §§5.2–5.3.
- Linnik's Vandermonde step needs `k < p`.  The formal theorem records this
  necessary hypothesis in addition to primality and `2 ≤ k`.
- The brief's V-C1-4 wording combines `p^k ≤ P` with a suggested prime
  `p > P^(1/k)`; those inequalities point in opposite directions.  The formal
  fundamental lemma uses the Vaughan-compatible condition `P < q^k`, followed
  by primes above `q`.
- A single predetermined prime cannot uniformly make both selected blocks
  nonsingular: it may divide their discriminants.  The proof therefore uses
  a bounded chain of Bertrand primes and the discriminant product, which is
  the absorption mechanism in Vaughan's argument.
- The requested exponent is nonnegative.  This was proved from Bernoulli's
  inequality; the exact recurrence formalized is
  `Δ_(τ+1) = Δ_τ * (1 - 1/k)`.

## Verification

- `lake env lean MoltResearch/Discrepancy/VinogradovMeanValue.lean` — passed
  with no warnings.
- forbidden-token grep over `MoltResearch` and `Solutions` — passed.
- `./scripts/check_layering.sh` — passed.
- `python3 scripts/check_aggregator_coverage.py` — passed (194 modules, 192
  reachable; the two reported allowlisted modules are pre-existing).
- `lake build MoltResearch.DiscrepancyAnalytic` — passed (8,121 jobs).

No push, merge, or rebase was performed.  This report is intentionally left
uncommitted.
