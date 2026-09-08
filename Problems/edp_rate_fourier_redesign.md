# Finite Fourier redesign within the source budget

Research snapshot: 2026-09-08. This memo accompanies
[`FiniteFourierBudget.lean`](../Conjectures/C0003_edp_rate/src/FiniteFourierBudget.lean)
and the revised schedule in
[`Reduction.lean`](../Conjectures/C0003_edp_rate/src/Reduction.lean). It proves the
finite Fourier assumption only. It does **not** prove an Erdős-discrepancy rate: the
finite van der Corput and structured-branch assumptions remain open.

## Outcome

Candidate (a) succeeds after making the analysis cutoff budget-adaptive. For each
outer product horizon `x`, use the largest exponent-box scale whose **exact** A4
source budget is at most `⌊x⌋₊`. The resulting Lean instance
`finiteFourierReductionAssumption_budgetSafe` discharges
`FiniteFourierReductionAssumption` without a global discrepancy hypothesis.

The revised conditional target is

\[
g(x)=10^{-7}(\log\log\log x)^{1/500}
\]

above `edpRateStart`, and `g(x)=1` below it. The smaller coefficient is calibration
slack, not a constant extracted from McNamara. The two remaining assumption classes
must still show that their thresholds fit below the new cutoff; consequently this PR
does not assert `HasDiscrepancyRateBy g` unconditionally.

## 1. Known

### 1.1 Literature

Tao's finite Fourier reduction takes the primes up to a window scale `X`, evaluates
the source function on the exponent group `(ℤ/Mℤ)^r`, and separates points at which
translation by the exponent vector of every `j ≤ X` does not wrap. At the good
points the translated window is a homogeneous progression; at exceptional points
the triangle inequality gives the bound `n ≤ X`. Tao then takes **“M sufficiently
large depending on C, X”** and applies Fourier expansion and Plancherel to obtain a
random completely multiplicative function with bounded second moments for every
`n ≤ X`. [Tao, Section 2, pp. 9–11][Tao16]

Tao explicitly says that a quantitative proof should **“avoid this compactness
argument and work instead with truncated versions”**, with corresponding
truncations later in the proof. [Tao, footnote 4, p. 9][Tao16] Thus using one finite
law only through a cutoff follows the published architecture; the source-budget
calibration below is our addition.

McNamara's quantitative endpoint is a rectangle

\[
 n\le N,\qquad
 d\le \exp\!\left(\frac{N}{(\log\log N)^{1/242}}\right),
\]

with discrepancy lower bound `(log log N)^(1/484-o(1))`. His proof is an
end-to-end quantitative traversal of the Fourier, nonpretentious, and structured
stages. [McNamara, Theorem 4.1.1 and Lemmas 4.2.1–4.4.4, pp. 118–124][Mc21]

### 1.2 Formal results inherited from A4 and A5

For a spectral scale `X`, exponent modulus `M`, and requested moment `n`, A4 proves
that the greatest source product queried at a wrap-free exponent-group point is

\[
 \operatorname{SB}(X,M,n)
 =n\prod_{p<X+1}p^{M-(\lfloor\log_2X\rfloor+1)}. \tag{1}
\]

Natural-number subtraction is intended. The maximum is attained when
`⌊log₂ X⌋ < M`. A4 also proves the localized spectral estimate using only
progressions with product at most (1). See `spectralSourceBudget_isGreatest` and
`spectral_window_bound_of_sourceBudget` in
[`SourceBudget.lean`](../Conjectures/C0003_edp_rate/src/SourceBudget.lean).

A5 proves `finiteFourierReduction_of_schedule`: once the terminal inequality

\[
 (\operatorname{SB}(L(x),M(L(x)),L(x)):\mathbb R)\le x \tag{2}
\]

holds, the exponent-box law supplies all moments requested by
`FiniteSecondMomentBound`. A5 also proves that failure of (2) is attained by a
wrap-free source progression, so a looser estimate cannot repair the old schedule.
See [`FiniteFourier.lean`](../Conjectures/C0003_edp_rate/src/FiniteFourier.lean)
and [PR #3773][PR3773].

## 2. Conjectured and still open

Erdős's conjectured rate is `D_f(x) ≫ log x`, much stronger than the conditional
triple-log target retained here. [Erdős Problems #67][EP67]

This redesign does not establish either remaining analytic interface:

1. `FiniteVanDerCorputRateAssumption` must fit its shift window and Elliott
   threshold below the revised cutoff.
2. `FiniteBorweinChoiCoonsRateAssumption` must fit its structured terminal scale
   below the same cutoff.

Whether the coefficient `10^-7` and exponent `1/500` survive those two exact
threshold audits is open. The coefficient is deliberately identified as our design
choice, not as a theorem from the cited literature.

## 3. Our construction: candidate (a)

Let

\[
 \ell_N=\lfloor\log_2N\rfloor,\qquad
 r_N=\#\{p:p<N+1\},
\]

and choose exactly the modulus already proved sufficient for the wraparound error,

\[
 M_N=\max(1,r_N\ell_NN^2). \tag{3}
\]

Define the scheduled terminal budget

\[
 B_N=N\prod_{p<N+1}p^{M_N-(\ell_N+1)}. \tag{4}
\]

This is `edpScheduledSourceBudget N`. The revised cutoff is the finite maximum

\[
 L(x)=\max\{N\le\lfloor x\rfloor:B_N\le\lfloor x\rfloor\}. \tag{5}
\]

The set in (5) is never empty: `B₀=0`, so `N=0` is feasible. In Lean, (5) is
implemented with `Nat.findGreatest`.

### 3.1 Exact source inequality

By the defining property of the greatest feasible integer,

\[
 B_{L(x)}\le\lfloor x\rfloor. \tag{6}
\]

For every requested moment `n ≤ L(x)` and every source progression `(d,m)` used
by the wrap-free part of the Fourier calculation, A4 and monotonicity in `n` give

\[
\begin{aligned}
 dm
 &\le \operatorname{SB}(L(x),M_{L(x)},n)\\
 &\le \operatorname{SB}(L(x),M_{L(x)},L(x))\\
 &=B_{L(x)}\\
 &\le\lfloor x\rfloor\le x. \tag{7}
\end{aligned}
\]

Equation (3) simultaneously gives the wraparound requirement

\[
 r_{L(x)}\ell_{L(x)}L(x)^2\le M_{L(x)}. \tag{8}
\]

Equations (6)–(8) are exact integer inequalities, not asymptotic estimates.
They are the content of
`edpScheduledSourceBudget_cutoff_le_floor`,
`edpFourierSourceBudget_eq_scheduled`,
`edpFourierSourceBudget_le_outer`, and
`spectralSourceBudget_at_cutoff_le_outer`. Combining them with A5 yields the
unconditional instance `finiteFourierReductionAssumption_budgetSafe`.

### 3.2 The cutoff is not permanently small

For each fixed natural scale `N`, set

\[
 X_N=\max(N,B_N). \tag{9}
\]

If `X_N ≤ x`, then both `N ≤ ⌊x⌋` and `B_N ≤ ⌊x⌋`; hence `N` is a feasible
candidate in (5) and

\[
 N\le L(x). \tag{10}
\]

The Lean theorem `le_edpAnalysisCutoff_of_outer_ge` proves (10). It is a fully
explicit cofinality statement: every finite downstream threshold can in principle
be admitted by increasing the outer product horizon to the fixed natural number
in (9). It does not by itself synchronize all thresholds required by A7 and A9.

### 3.3 What moment range this buys

The exact output is one stochastic completely multiplicative law satisfying

\[
 \mathbb E\left|\sum_{j\le n}G(j)\right|^2
 \le g(x)^2+1\qquad(0\le n\le L(x)). \tag{11}
\]

No moment beyond `L(x)` is claimed. Using the prime number theorem only as an
asymptotic guide, `r_N ~ N/log N`, `ℓ_N ~ log N/log 2`, and
`∑_{p≤N} log p ~ N`, so (3)–(4) suggest

\[
 \log B_N\sim N^4/\log 2,
 \qquad L(x)\asymp(\log x)^{1/4}. \tag{12}
\]

Consequently `log log L(x) = log log log x + O(1)`, so shrinking to the exact
budget-safe scale does not change the expected iterated-log *order* of McNamara's
moment argument. This is our asymptotic calculation, not a Lean theorem. The PR
reduces the coefficient from `10^-6` to `10^-7` as conservative calibration slack;
the final value remains subject to A7, A9, and A10.

## 4. Why candidates (b) and (c) are not selected

The card orders the candidates, so the successful exact construction in Section 3
stops the search before (b) and (c). We do not claim that either alternative fails.

For comparison, importing McNamara's rectangular theorem would require the separate
product fit

\[
 N\exp\!\left(\frac{N}{(\log\log N)^{1/242}}\right)\le x. \tag{13}
\]

The reparameterization in the literature memo makes (13) true for sufficiently
large `x`, but formalizing McNamara's distinct finite Fourier package would duplicate
substantial machinery and is unnecessary once (7) is available.

Likewise, the present wrap-tolerant estimate already bounds the exceptional mass.
With `r` prime coordinates, valuation width `ℓ`, modulus `M`, and `n ≤ L`, its
contribution to the averaged squared window is at most

\[
 \frac{r\ell}{M}n^2\le\frac{r\ell L^2}{M}. \tag{14}
\]

Keeping the existing `+1` moment error therefore asks for exactly
`rℓL² ≤ M`, which is (8). Merely retaining the same pointwise bound while calling
the proof wrap-tolerant does not permit a smaller modulus; an actual candidate (c)
would need cancellation on the exceptional set or a redesigned moment interface.
Again, this is a diagnosis of the current estimate, not a proof that every
wrap-tolerant construction is impossible.

## 5. Lean proof map

| Theorem / instance | Role |
|---|---|
| `edpScheduledSourceBudget_cutoff_le_floor` | Proves (6) from `Nat.findGreatest`. |
| `le_edpAnalysisCutoff_of_scheduledBudget` | Admits any feasible candidate scale. |
| `le_edpAnalysisCutoff_of_outer_ge` | Gives the explicit cofinal threshold (9). |
| `edpFourierSourceBudget_eq_scheduled` | Identifies A5's terminal budget with (4). |
| `edpFourierSourceBudget_le_outer` | Casts (6) to the real outer horizon. |
| `spectralSourceBudget_at_cutoff_le_outer` | Proves the full chain (7) for every requested moment. |
| `finiteFourierReductionAssumption_budgetSafe` | Installs the Fourier assumption using A5. |

## References

[Tao16]: https://arxiv.org/pdf/1509.05363
[Mc21]: https://escholarship.org/uc/item/4wr015m0
[EP67]: https://www.erdosproblems.com/67
[PR3773]: https://github.com/ProofFleet/moltresearch/pull/3773
