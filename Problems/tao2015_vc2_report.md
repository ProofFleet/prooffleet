# Track R — V-C2: Codex run 24 report (2026-09-07)

Verbatim final report of Codex run 24 (gpt-5.6-sol, brief `Problems/tao2015_vc2_brief.md`), whose seven commits shipped as the V-C2a PR:
the analytic core of Vinogradov's method for `∑ (n+u)^{−it}` — the logarithmic Taylor phase, shift averaging and Hölder, the orthogonality
identity with `vinogradovJ`, the control of logarithmic blocks by polynomial moments, coefficient boxes and top-frequency spacing, the exact
frequency-box multiplicity, and the aggregate reduction with the phase conversion. Findings (Finding V-3 in the design report): the brief's
parameter bookkeeping treated the box multiplicity as `O(1)`; Ford's Lemma 6.3 has `M ≍ N^{1−λ/(k+1)}` with multiplicity `O(M)`, giving the
natural saving `1/(k² log k)` before constant absorption; and `vinogradov_mean_value`'s existential constant `C_{k,τ}` has no public growth bound,
so the fixed-form theorem needs a V-C1 export (run 27), with the honest target `1 − c/(λ³ log²(2λ))`. Commit hashes are the run's, before cherry-pick.

---

# Track R V-C2 report

## Outcome

This run did **not** prove the requested theorem `vinogradov_weyl_sum`.
It formalized the analytic core through Ford's frequency-box reduction, found
and corrected the parameter bookkeeping in the brief, and stopped at a
genuine uniformity gap in the public V-C1 interface.

The new registered leaf is
`MoltResearch/Discrepancy/VinogradovWeylSum.lean`.  It contains no admitted
proofs and does not introduce assumptions.

## What was proved

1. The logarithmic Taylor formula, its exact remainder bound, and the
   normalized-character perturbation estimate.
2. Exact shift averaging on an interval, including the `2U` endpoint cost,
   and the finite Holder inequality needed after averaging.
3. The exponential-sum form of Vinogradov orthogonality:
   `integral_norm_polynomialSum_pow_even` identifies the `2s` moment on the
   unit coefficient cube with `vinogradovJ s k M`.
4. Discrete partial summation and Ford's partial-sum majorant, with
   `integral_polynomialPartialMajorant_pow_le` giving the explicit cost
   `2^(4s) * vinogradovJ s k M`.
5. The derivative bookkeeping inside a coefficient box.  The Taylor tail and
   coefficient error each cost `1/(2*pi*M)`, hence consecutive residual
   characters differ by at most `2/M`.  Consequently each short logarithmic
   block is pointwise bounded by the polynomial partial-sum majorant.
6. Centered fractional coefficient boxes, their exact volume, integer-shift
   periodicity of the polynomial majorant, and the box-to-integral inequality.
7. Sharp top-coefficient spacing and an elementary separated-set packing
   lemma.  The resulting exact multiplicity is

   ```text
   nu(beta) <= 2 * (2*r_k/d_k + 1),
   r_k = 1 / (2*pi*k^2*M^k),
   d_k = t / (2*pi*(2*N+1)^(k+1)).
   ```

   Equivalently,

   ```text
   nu(beta) <=
     2 * (2*(2*N+1)^(k+1)/(k^2*t*M^k) + 1).
   ```

   The leading factor `2` records the only two possible integer lifts of a
   top coefficient of magnitude below one.
8. The summed frequency-box reduction
   `sum_log_blocks_pow_mul_volume_le`, up to folding the enlarged centered
   cube `[-1,2]^k` back to the unit torus.
9. The requested conversion of phase conventions:

   ```text
   (y : C)^(-(t : C)*I) = e(-(t/(2*pi))*log y)    (0 < y).
   ```

## Corrected Ford bookkeeping

The contradictory `U` choices in the brief come from treating the
multiplicity as `O(1)`.  Ford Lemma 6.3 instead uses a short length `M` with

```text
1 <= M <= N*t^(-1/(k+1)),    t <= N^k.
```

For `k-1 <= lambda <= k`, where `lambda = log t/log N`, take
`M` at scale `N^(1-lambda/(k+1))`.  The overlap multiplicity is then `O(M)`,
not `O(1)`.  The factor `M` combines with

```text
J_(s,k)(M) <= C_(k,tau) * M^(2s-k(k+1)/2+delta_tau)
```

and the inverse box volume to give a short-block moment of scale
`M^(2s+1+delta_tau)`.  After Holder and division by the shift length, the
main term is

```text
N * (M^(1+delta_tau)/N)^(1/(2s)).
```

Thus `tau` of order `k*log k`, `s = k*tau`, and `delta_tau <= 1/2`
produce the intended natural saving of order
`1/(k^2*log k)` before constant absorption.

## Stop condition and blocker

The public theorem `vinogradov_mean_value` supplies a separate existential
constant `C_(k,tau)` for every pair `(k,tau)`.  Its construction is explicit
inside `VinogradovMeanValue.lean`, but the specification theorem for the
named `vinogradovMeanValueConstant` and all recurrence estimates are private.
There is therefore no public theorem bounding the growth of `C_(k,tau)` as
`k` varies.

This matters because the requested conclusion has one global constant `C`.
After taking a `2s`-th root, the available theorem leaves the prefactor
`C_(k,tau)^(1/(2s))`.  With no growth bound, absorbing it changes the saving
to one involving `log C_(k,tau)`, not to
`c/(lambda^a*log(2*lambda)^b)` for fixed `a,b,c`.  This is exactly the brief's
stop condition.

The design notes state an envelope of the rough form

```text
D_(k,tau) = (k*tau)^(2*k*tau) * (2*k)^(4*k*(k+1)*tau).
```

If a public V-C1 lemma exports that bound (or any bound with
`log D/(2s) = O(k*log k)`), the usual large-`N` absorption / small-`N`
trivial split yields a safe fixed-form target with the deliberately weakened
saving

```text
c / (lambda^3 * log(2*lambda)^2).
```

That exponent has fixed `a = 3`, `b = 2` and is sufficient for V-C3.  This
parameter conclusion is not claimed as a Lean theorem in this run.

Two further pieces would remain after exporting the V-C1 envelope: fold the
centered cube `[-1,2]^k` to three unit periods per coordinate, then perform
the long-interval shift assembly and the bounded-`lambda` second-derivative
case.

## Commits

- `0626f3b6` — Taylor phase.
- `bf249196` — shift averaging and Holder.
- `dc2f24f0` — polynomial moment orthogonality.
- `8c408cf8` — logarithmic blocks controlled by polynomial moments.
- `1aa0ecd1` — coefficient boxes and top-frequency spacing.
- `5733ded1` — exact frequency-box multiplicity.
- `db5ca098` — aggregate box reduction and complex-power conversion.

Every commit contains the run link and co-author trailer.  No push, merge, or
rebase was performed.

## Verification

- `lake env lean MoltResearch/Discrepancy/VinogradovWeylSum.lean` — passed
  without warnings.
- `lake build MoltResearch.DiscrepancyAnalytic` — passed (8,124 jobs).
- `scripts/forbid_sorry.sh` — passed.
- `scripts/forbid_axiom_unsafe.sh` — passed.
- `scripts/check_layering.sh` — passed.
- `python3 scripts/check_aggregator_coverage.py` — passed (197 modules, 195
  reachable; the two reported modules are allowlisted and pre-existing).
- `#print axioms` for the Taylor, shift, orthogonality, moment-majorant,
  multiplicity, aggregate reduction, and complex-power conversion theorems
  reports only `propext`, `Classical.choice`, and `Quot.sound`.

`CODEX_REPORT.md` is intentionally uncommitted.


---

# Run 27 (V-C1′ + V-C2-8/9): the constant export and the main-term assembly

Verbatim final report of Codex run 27 (the V-C2 brief with its resume note), whose three commits shipped as the V-C2b PR: the fold of the
coefficient cube (`3^k`), **V-C1′** (the public specification of `vinogradovMeanValueConstant`, its envelope `(2^{32}(k+τ+1)^{16})^{128kτ(k+τ+1)}`
and the logarithmic bound), and the normalised Weyl main term `N·(prefactor·M^{δ}/N)^{1/(2kτ)} + 2M`. Finding V-4: `δ_τ ≤ 1/2` needs
`τ ≈ 2k log k`, and the recursion's `((kτ+k)!)²` factors make `log D_{k,τ}/(2kτ) = O(k log² k)`, so the absorbable fixed form is
`1 − c/(λ³ log³(2λ))` (run 28's target; V-C3 still closes at `a' = 33/25`); the `vdc2` route for small `λ` is void at `t = N²`.

---

# Track R / V-C2 — run 27 report

## Completed and committed

- `978eddad` — V-C2-8: folds the enlarged coefficient cube `[-1,2]^k`
  into three unit periods per coordinate, with the exact factor `3^k`.
- `84bd3499` — V-C1': exports the named VMVT constant specification,
  positivity, the closed envelope
  `(2^32 (k+τ+1)^16)^(128 k τ (k+τ+1))`, and its logarithmic bound.
- `1cd4da24` — V-C2-9 analytic core: inserts the named VMVT constant into
  the folded moment, computes the exact common coefficient-box volume,
  cancels the triangular degree loss, and assembles shift averaging and
  Holder into
  `N * (vinogradovWeylPrefactor * M^vinogradovDelta / N)^(1/(2*k*τ)) + 2*M`.

The compiled entry points are:

- `vinogradovMeanValueConstant_spec`
- `vinogradovMeanValueConstant_le`
- `log_vinogradovMeanValueEnvelope_le`
- `sum_log_blocks_pow_mul_volume_le_meanValue`
- `vinogradovWeylMomentFactor_div_volume`
- `norm_log_sum_le_vinogradovAssembly`
- `norm_log_sum_le_vinogradovMainTerm`
- `cpow_neg_mul_I_eq_e_log`

## Blocking bookkeeping contradiction

The requested fixed exponent `1-c/(lambda^3 log^2(2 lambda))` cannot be
closed by the named recursive constant and the prescribed trivial
small-`N` branch.

There are two separate discrepancies in the resume bookkeeping.

1. With
   `delta = (k^2/2) * (1-1/k)^τ`, the choice
   `τ = ceil(k log k)+1` gives only `delta = O(k)`, not `delta <= 1/2`.
   Reaching `delta <= 1/2` requires `τ` of size `2*k*log k`.

2. More decisively, the explicit recursion itself contains the multiplier
   `((k*τ+k)!)^2` at step `τ`.  Consequently, after the required
   `τ = Theta(k log k)` steps, its logarithm has unavoidable size

       sum_{j <= τ} log((k*j)!^2) = Omega(k^3 log^3 k).

   This is also reflected by the proved public upper envelope: after the
   `2*k*τ` root its logarithmic cost is `O(k log^2 k)`, not `O(k log k)`.

For the worst integer bands `lambda = k-1`, every Taylor-admissible degree
is at least `k-1`, and obtaining any saving forces `τ = Omega(k log k)`.
Thus the prefactor can only be absorbed once
`log N = Omega(k^3 log^3 k)`.  On the complementary range, the proposed
trivial estimate would require an absolute constant at least

    N^(c/(k^3 log^2(2*k))) = k^(Omega(c)),

which is unbounded in `k`.  Enlarging the degree worsens this ledger, so no
admissible parameter choice for this recursive VMVT constant removes the
failure.  The same method naturally supports an additional logarithm in
the denominator (for example `lambda^3 log^3(2 lambda)`), or a larger power
of `lambda`; the fixed `(a,b)=(3,2)` form needs a genuinely sharper VMVT
constant construction.

The V-C2-10 route in the resume has a separate endpoint error: at `t=N^2`
the displayed second-derivative estimate has a first term of size `N`, not
`N^(3/4)`.  A degree-two VMVT argument or rational approximation can supply
the small-lambda regime, but it cannot repair the high-lambda constant
obstruction above.

## Verification

- `lake env lean MoltResearch/Discrepancy/VinogradovWeylSum.lean` — passed.
- `lake build MoltResearch.Discrepancy.VinogradovWeylSum` — passed.
- `scripts/check_layering.sh` — passed.
- `scripts/check_aggregator_coverage.py` — passed (the two reported modules
  are the repository's known allowlisted examples).
- `lake build MoltResearch.DiscrepancyAnalytic` — passed (8124 jobs).
- Forbidden-declaration scan of both touched source files — passed.
- `#print axioms` for the exported constant theorems, folded VMVT moment,
  normalized main term, and complex-power conversion reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
