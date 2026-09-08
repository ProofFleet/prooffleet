# A finite-scale route to a first Erdős-discrepancy rate

Research snapshot: 2026-09-08.  This memo specifies the interfaces in
[`Reduction.lean`](../Conjectures/C0003_edp_rate/src/Reduction.lean).  It is a
reduction plan, not a proof of a quantitative bound.  Every unproved
mathematical input is exposed there as an `*Assumption` class.

## Executive decision

The finite Fourier objects already in the tree are better than the stale Track Q
design suggested: every sample is **exactly** completely multiplicative and
unimodular.  There is no approximate-multiplicativity defect to repair.  The
real missing estimate is a source-budgeted version of the finite spectral
second-moment bound.  The current theorem assumes a discrepancy bound for every
homogeneous progression, whereas a rate proof may assume smallness only for
`m * d ≤ x`.

The proposed pipeline therefore keeps a single finite probability law and an
explicit cutoff throughout:

```text
no witness of size g(x) under m*d ≤ x
                 |
                 v
 finite spectral law with moments through L(x)       [Fourier reduction]
                 |
                 v
 persistent pretentiousness for X₀ ≤ X ≤ L(x)       [van der Corput/Elliott]
                 |
                 v
 contradiction before L(x)                          [structured branch]
```

The first concrete target is

\[
 g(x)=10^{-6}(\log\log\log x)^{1/500}
\]

past a fixed positive-log threshold, and `g(x) = 1` below it.  The strict
inequality `1/500 < 1/484` leaves room for the lower-order iterated-log factors
in McNamara's theorem.  The coefficient and the low-scale threshold are design
values, not constants extracted from the literature; the three finite
assumptions are responsible for them.  They should be recalibrated once their
proofs expose actual thresholds.

## 1. Known facts used by the design

### Known in the literature

Tao's Fourier step constructs, for every finite scale, a probability law of
completely multiplicative functions and bounds each fixed second moment.  He
then uses compactness of probability measures to pass to one limiting law that
obeys all moment bounds simultaneously.  The compactness selection has no
modulus.  Tao explicitly notes that a quantitative version should avoid this
step, work with finite truncations, and control the errors caused by truncated
Euler products.  [Tao, Section 2 and footnote 4][Tao16]

McNamara carries out a quantitative form of the three-part strategy.  His
Theorem 4.1.1 gives, in the Hilbert-valued setting, a lower bound of shape

\[
 \frac{(\log\log N)^{1/484}}
 {(\log\log\log\log N)^{1/4}
  (\log\log\log\log\log N)^{1/2}}
\]

with `m ≤ N` and
`d ≤ exp(N / (log log N)^(1/242))`.  His Chapter 4 identifies the finite
Fourier reduction, quantitative nonpretentious branch, and structured branch
as the three ingredients.  [McNamara, Theorem 4.1.1 and Lemmas 4.2.1--4.4.4][Mc21]

For a product budget `x`, take heuristically

\[
 N=\left\lfloor\tfrac13\log x\,
        (\log\log\log x)^{1/242}\right\rfloor.
\]

Then McNamara's dilation ceiling is `x^(1/3+o(1))`, while `N` is
subpolynomial in `x`, so `m*d ≤ x` for all sufficiently large `x`.  Also
`log log N = (1+o(1)) log log log x`.  Thus his theorem implies the
product-scale shape

\[
 D_f(x)\ \gtrsim\
 (\log\log\log x)^{1/484-o(1)}.
\]

This reparameterization is our deduction from the cited theorem.  In
particular, the source does not justify dropping its slowly growing denominator
at the endpoint exponent `1/484`; choosing `1/500` is the conservative way to
obtain a fixed power after a sufficiently large threshold.

Tao's logarithmically averaged Elliott theorem is stated nonasymptotically in
the relevant two-point form: once a strength parameter and the two affine forms
are fixed, there is a sufficiently large threshold.  The dependence is
effective in principle but not numerically recorded in the paper.  It therefore
provides the correct *shape* for a finite interface, but not by itself a
verified function `x ↦ cutoff`.  [Tao, Theorem 1.3 and Remark 1.4][TaoElliott]

### Known in the formal tree

The following statements are proved, not proposed:

* [`spectralSample_completelyMultiplicativeC`](../MoltResearch/Discrepancy/FiniteSpectralSample.lean)
  and `spectralSample_unimodular` say that every finite frequency gives an
  exact completely multiplicative unimodular function on all natural numbers.
* [`weighted_normSq_apSumC_spectralSample_le`](../MoltResearch/Discrepancy/FiniteSpectralSample.lean)
  gives the weighted second-moment bound for windows `n ≤ X`, and
  [`integral_windowFunctional_spectralLaw_le`](../MoltResearch/Discrepancy/SpectralLaw.lean)
  packages it as a probability law.
* [`exists_limit_law`](../MoltResearch/Discrepancy/SpectralLimit.lean) is the
  sole compactness passage.  It takes an ultrafilter limit of `scaleLaws` so
  that one law satisfies the bound for every `n`.
* The van-der-Corput proof in
  [`TrackCStage5VanDerCorputProof.lean`](../Conjectures/C0002_erdos_discrepancy/src/TrackCStage5VanDerCorputProof.lean)
  already makes the elementary choices explicit: after replacing a moment
  bound `C` by `max C 1`, it takes `H = ceil(8*C/ε)`, Elliott strength
  `1/(8*H)`, and a maximum of finitely many Elliott thresholds.  Its remaining
  threshold is not a closed numerical function because the Elliott interface
  returns existential thresholds.
* The qualitative structured-branch consumer is isolated as
  `BorweinChoiCoonsAssumption` in
  [`TrackCStage5Derivation.lean`](../Conjectures/C0002_erdos_discrepancy/src/TrackCStage5Derivation.lean).
  The surrounding tree contains explicit-in-form pretentious-distance,
  Mertens, repulsion, zero-free-region, and Euler-product layers, but they have
  not been assembled with one common finite cutoff for this rate.

The important correction to the old Track Q sketch is the first two bullets:
the finite law is already exact.  What prevents direct reuse is the hypothesis
of the spectral bound.  It currently asks for a single global natural bound
`B` on every `apSum f d n`.  Contraposition of
`HasDiscrepancyRateBy g` supplies only

```text
|apSum f d m| < g(x)  when 0 < d and m*d ≤ x.
```

A quantitative proof must audit every translated/dilated sum in the Fourier
calculation and show that it remains inside this product budget.

## 2. Conjectured statement versus open proof obligations

### Conjectured

Erdős's rate conjecture predicts the much stronger `D_f(x) ≫ log x` uniformly
for every sign sequence.  The `1/500` triple-log target is not the conjecture;
it is a first mechanizable milestone compatible with the shape of the best
published quantitative result.  [Erdős Problems #67][EP67]

### Open obligations in this reduction

None of the following is claimed known.  They are the three classes in
`Reduction.lean`:

1. `FiniteFourierReductionAssumption` converts the absence of a rate witness
   under the exact budget `m*d ≤ x` into a probability law `G` with
   `sndMomentPartialSum G n ≤ g(x)^2 + 1` for every
   `n ≤ edpAnalysisCutoff x`.
2. `FiniteVanDerCorputRateAssumption` converts that finite family of moment
   bounds into `FinitePersistentPretentious μ G x`.  It must ensure every
   auxiliary window and every Elliott threshold fits below the same cutoff.
3. `FiniteBorweinChoiCoonsRateAssumption` says the same finite moment bounds
   rule out that persistent-pretentiousness conclusion before the cutoff.  It
   must perform the structured argument without taking a limit in `x`.

These assumptions are intentionally stronger and cleaner than the next
low-level lemmas will be.  Proving an instance may enlarge `edpRateStart`, reduce
the coefficient in `g`, or replace `edpAnalysisCutoff` by a slower schedule.
Such calibration is legitimate; silently treating an existential threshold as
explicit is not.

## 3. Our finite interface

This section describes our design choices; it does not attribute them to Tao or
McNamara.

### The scale and moment package

`edpAnalysisCutoff x` is

\[
 \left\lfloor \frac13\log x\,
   (\log\log\log x)^{1/242}\right\rfloor.
\]

It mirrors the `N` used in the product-scale reparameterization.  A
`FiniteSecondMomentBound μ G x` asks for the single uniform cap
`g(x)^2 + 1` only through this cutoff.  The `+1` matches the existing spectral
estimate and avoids an artificial rounding obligation.

The Fourier assumption quantifies over the source sequence and scale first, and
then returns an arbitrary finite-law model `(Ω, μ, G)`.  Downstream stages may
use only the finite moment package; they cannot recover a global discrepancy
hypothesis or invoke `exists_limit_law`.

### The finite pretentious conclusion

`finitePretentiousEvent G Q T B X` consists of samples for which there are a
modulus `q ≤ Q`, a Dirichlet character `χ mod q`, and `|t| ≤ T*X` such that the
squared pretentious distance from `χ(n)n^(it)` through `X` is at most `B`.

`FinitePersistentPretentious μ G x` requires:

* one `K ≥ 0` chosen before `ε`;
* for every `0 < ε ≤ 1`, one finite parameter package `Q,T,B,X₀`;
* a nonvacuity certificate `1 ≤ X₀ ≤ edpAnalysisCutoff x`; and
* probability at least `1-Kε` at every integer truncation in the finite interval
  `X₀ ≤ X ≤ edpAnalysisCutoff x`.

The upper endpoint is essential.  Omitting it would merely restate Tao's
infinite-tail conclusion and would make a finite Fourier law unusable.  Requiring
`X₀ ≤ cutoff` prevents the conclusion from being vacuous.  Allowing `Q,T,B` to
depend on `ε`, but not on `X` within the interval, matches the parameter order
of the existing qualitative van-der-Corput interface.

### The glue theorem

`discrepancyRate_of_assumptions` is fully proved in Lean.  At
`x ≤ edpRateStart`, the one-term progression `(d,m)=(1,1)` has magnitude one.
Above that threshold, failure of the desired witness supplies the strict
smallness premise of the Fourier class.  The returned finite moment package is
both accepted by the van-der-Corput class and rejected by the structured class,
giving a contradiction.

This theorem establishes only the implication

```text
[three finite assumptions] -> HasDiscrepancyRateBy edpTripleLogRate.
```

It is not an unconditional EDP-rate theorem, and this file declares no
instances of the three classes.

## 4. Proof obligations and likely failure points

### Fourier/source-budget leg

The first task is to revisit the proof of `spectral_window_bound`, not the
definition of `spectralSample`.  Every occurrence of the source sequence should
be annotated by the actual pair `(d,m)` it requests.  One needs a bound of the
form `d*m ≤ Budget(X,M,n)` and then a schedule making this budget at most the
outer `x`.  The modulus condition
`card(PrimeIdx X) * Nat.log 2 X * X^2 ≤ M` also has to be paid for without
forcing a translating dilation outside `x`.

The danger is that a proof using a global `hB` can hide an enormous dilation:
locality in the window index `n` alone does not imply locality in the original
homogeneous progression.  This audit is the decisive replacement for
compactness.

### Nonpretentious leg

The existing van-der-Corput proof gives a useful dependency graph, but its
Elliott threshold `A₀` is chosen existentially for each shift pair.  A finite
version needs function-form threshold data, a maximum over `h,h' ≤ H`, and an
explicit check that the resulting `ceil W` and every terminal `X` fit below
`edpAnalysisCutoff x`.  The moment estimate must also be localized to all
indices touched by `windowSumC`; an off-by-`H` demand beyond the cutoff cannot
be discarded.

Recent quantitative Elliott estimates may reduce losses, but importing such a
result is not enough: its nonpretentiousness parameters and exceptional scales
must be synchronized uniformly with the random law returned by the Fourier
step.  [Tao--Teräväinen, Theorem 3.1][TT25]

### Structured leg

The structured branch needs a finite `X` in the permitted interval at which
pretentious mass forces a second moment above `g(x)^2+1`.  Its modulus,
frequency, distance, prime cutoff, and Euler-product truncation must all depend
only on the preceding finite parameter package.  The likely bottleneck is not
the logical contradiction but proving that a sufficiently large usable `X`
still lies below `edpAnalysisCutoff x` after all nested thresholds are expanded.

## 5. Phase 2 lemma DAG

These are proposed follow-up card items.  Their identifiers and `after:` edges
make the dependency graph explicit; all remain unproved.

* **B0: Source-budget audit** (`after: A3`).  Prove a bound that records, for
  every invocation in `SpectralWindowBound`, the largest source product `d*m`
  in terms of the spectral parameters.  Deliver a theorem usable without a
  global discrepancy hypothesis.
* **B1: Finite Fourier package** (`after: B0`).  Select the spectral scale and
  modulus as functions of outer `x`; prove all requested products are at most
  `x`; instantiate `FiniteFourierReductionAssumption` (or report the exact
  schedule obstruction).
* **B2: Function-form Elliott thresholds** (`after: A3`).  Replace the
  existential threshold used by the current nonasymptotic Elliott consumer with
  explicit threshold data, and prove the finite van-der-Corput estimates with
  every touched moment index recorded.
* **B3: Finite van-der-Corput package** (`after: B1, B2`).  Fit the `H`, shift
  maximum, Elliott window, and `X₀` below the common cutoff and instantiate
  `FiniteVanDerCorputRateAssumption`.
* **B4: Structured-branch threshold extraction** (`after: A3`).  Audit the
  Mertens/repulsion/zero-free/Euler-product chain into a function-form finite
  statement, including truncation error and an explicit required terminal
  scale.
* **B5: Finite structured package** (`after: B1, B4`).  Show that the terminal
  scale fits below the common cutoff and instantiate
  `FiniteBorweinChoiCoonsRateAssumption`.
* **B6: Rate calibration and audit** (`after: B3, B5`).  Reconcile all threshold
  inequalities, lower the exponent or coefficient if the proved schedules
  require it, prove divergence of the final concrete rate, and pin the final
  conditional-instance footprint.

In graph form:

```text
A3 --> B0 --> B1 --> B3 --> B6
 |             \      ^      ^
 |              -> B5 ------/
 +--> B2 ----------> B3
 +--> B4 ----------> B5
```

The graph deliberately permits the analytic threshold audits `B2` and `B4` to
run in parallel with the source-budget work.  `B3` and `B5` wait for `B1`
because there is no value in claiming a common cutoff until the Fourier leg
states what cutoff it can actually supply.

## 6. What would falsify this plan

This reduction remains useful even if the proposed schedule is too optimistic:
the class boundary will expose which inequality fails.  The present plan should
be revised, rather than patched informally, if any of the following occurs:

1. the source-budget audit requires products superlinear in the outer budget
   for every viable spectral modulus;
2. the function-form Elliott threshold grows faster than the finite Fourier
   cutoff can support;
3. the structured branch requires a truncation beyond the same cutoff; or
4. the finite moment cap required by either analytic branch is not the one the
   spectral law supplies.

In any such case, a slower explicit `g` is still a valid M1 target.  What is not
valid is importing the qualitative limit law and calling the resulting cutoff
effective.

## References

[EP67]: https://www.erdosproblems.com/67
[Tao16]: https://arxiv.org/abs/1509.05363
[TaoElliott]: https://arxiv.org/abs/1509.05422
[Mc21]: https://escholarship.org/uc/item/4wr015m0
[TT25]: https://arxiv.org/abs/2512.01739
