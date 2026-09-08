# Erdős #1144: approach memo and conditional reduction

## Status and honest outcome

This memo does **not** prove Erdős #1144.  It records a small, independently checked conditional
prime-block reduction and identifies its genuinely difficult local input.  The companion Lean file
`Conjectures/C0006_erdos1144_random_mult/src/Reduction.lean` proves only the following
conditional statement:

> If a sequence of measurable block events forces positive, uncentred partial-sum maxima;
> if each failure probability is bounded by an explicit budget; and if those budgets are
> summable at every fixed height, then `Erdos1144` follows.

The Borel--Cantelli closure is machine-checked.  No instance of any `*Assumption` class is
provided, so the open analytic work remains visible.

This is no longer a route proposed in ignorance of prior work.  On 2026-09-06, Sigurd William
Rachlew Høystad released
[saasom/Erdos1144 v1.0.0](https://github.com/saasom/Erdos1144/tree/v1.0.0), whose
[proof guide](https://github.com/saasom/Erdos1144/blob/v1.0.0/notes/1144/complete_proof.md)
claims an unconditional Lean theorem for exactly the positive, frequent-exceedance statement on
the complete sign model.  The D1 audit checked the tagged source hashes, the successful public CI
run, the preserved axiom report, and the endpoint definitions; it found no statement mismatch and
reports only `propext`, `Classical.choice`, and `Quot.sound` in the endpoint's transitive axiom
closure.  It did not complete a fresh local rebuild on this aarch64 machine.  See
[`Problems/erdos1144_literature.md`, §4](erdos1144_literature.md#4-audit-of-the-live-proof-claim),
the release's
[verification record](https://github.com/saasom/Erdos1144/blob/v1.0.0/verification/README.md),
and its
[final theorem](https://github.com/saasom/Erdos1144/blob/v1.0.0/Erdos/Problem1144/Final.lean).

Accordingly, this memo is **not a competing proof claim** and this PR is **not an independent
verification** of that release.  The latter is the separate card item D3v.  The reduction below is
useful as a compact alternative interface and as a check of the outer probability logic.  It is
also strictly more demanding than the tagged proof's active final route: we ask for summably small
block-failure probabilities, while the release proves a fixed positive crossing mass under every
finite cylinder law, derives a fixed deficit for the global upper-envelope event, and uses cylinder
concentration to show that event is null.  The release retains a `PositiveBlockOmega`/
first-Borel--Cantelli closure very close to ours as a comparison route, but its final theorem uses
`candidate_scheduledGaussianRobustCrossing_certificate` and the cylinder-envelope closure instead.

## 1. Exact target

Write

```text
F(n) = product over p^a || n of epsilon_p^a,
S(x) = sum over n <= x of F(n),
```

where the `epsilon_p` are independent uniform signs.  The merged `Statement.lean` asks for

```text
for almost every omega, for every M in R,
  S(N) / sqrt(N) >= M for infinitely many N.
```

Three features cannot be weakened during the argument:

1. the maximum is **positive**, not an absolute value;
2. `S` is **uncentred**;
3. the assertion is almost sure and recurrent, not a fixed-scale tail estimate.

For this model, `E F(n) = 1` on squares and `0` otherwise, so
`E S(x) = floor(sqrt(x))`.  The square contribution is useful context but does not itself imply
unbounded normalized positive fluctuations.

## 2. Known inputs and non-inputs

Everything in this section is known or already proved in the tree.

### 2.1 The large-prime decomposition is deterministic

If `x < X^2`, every `n <= x` has at most one prime factor greater than `X`, and that prime occurs
to the first power.  Complete multiplicativity therefore gives the exact split

```text
S(x)
  = sum_{n <= x, P(n) <= X} F(n)
    + sum_{X < p <= x} epsilon_p * S(x / p).                 (2.1)
```

Here integer parts are understood in `S(x / p)`.  If, for example,
`X^(8/7) <= x <= X^(4/3)`, then `x / p <= X^(1/3)` in the second term.  After conditioning on
the signs at primes at most `X`, every inner partial sum is fixed, while the signs with `p > X`
remain independent.  Thus the second term is a family of correlated linear forms in fresh
Rademacher variables as `x` varies.

This is the part of Harper's large-prime decomposition that transfers algebraically to the
completely multiplicative sign model.  Harper uses the same shape of split, conditional
Gaussian approximation, and covariance analysis for the squarefree-supported Rademacher and
Steinhaus models; see the introduction and Theorem 2 of
[Harper, *Almost sure large fluctuations of random multiplicative functions*](https://arxiv.org/abs/2012.15809).

### 2.2 Harper does not settle this target

Harper's theorem concerns Steinhaus functions and the squarefree-supported Rademacher model and
produces arbitrarily large values of the **absolute** partial sum.  His paper explicitly notes
that raw partial sums at widely separated scales retain substantial dependence.  The proof
therefore obtains a high-probability local maximum theorem and applies the first
Borel--Cantelli lemma along a sparse sequence, rather than declaring the raw block events
independent.

Those distinctions matter here.  A squarefree Rademacher function is zero on nonsquarefree
integers, whereas `F(p^2) = 1`; and an absolute-value maximum does not imply the required
positive maximum.

### 2.3 The squarefree convolution exposes, but does not remove, the obstruction

Let `f` be the squarefree-supported function with the same prime signs.  Then

```text
F = f * 1_square,
S_F(x) = sum_{a b^2 <= x} f(a).
```

Atherfold rewrites this as a weighted squarefree sum plus a fractional-part error in equation
(1.7), and records the analogous weighted identity in (1.8); see
[Atherfold, *Almost sure bounds for weighted sums of Rademacher multiplicative functions*](https://arxiv.org/abs/2501.11076).
The paper emphasizes that the fractional-part term breaks the multiplicative structure and is
difficult to control.  Consequently Harper's squarefree lower fluctuation cannot simply be
inserted into this identity.  Atherfold's results yield upper bounds for the completely
multiplicative model, not the positive divergent limsup required here.

### 2.4 Recent weighted oscillation is qualitatively different

Angelo and Xu prove that the weighted completely multiplicative sum
`sum_{n <= x} F(n) / sqrt(n)` changes sign infinitely often almost surely, and also study
conditioning many initial prime signs to `+1`; see
[Angelo--Xu, *Oscillations of random multiplicative functions under initial bias*](https://arxiv.org/abs/2411.14447).
This is relevant evidence that one-sided questions survive substantial initial bias, but it
does not give a growing positive amplitude for the unweighted `S(x) / sqrt(x)`.

### 2.5 The recurrence theorem is already available

Mathlib's `MeasureTheory.ae_eventually_notMem` is the first Borel--Cantelli lemma in an
almost-everywhere form: summable event measures imply eventual avoidance.  The Lean reduction
applies it to the complements of positive block-success events.  No probabilistic recurrence
principle is assumed.

This is the closure proved in this repository.  It should not be attributed to the tagged release's
active certificate.  That release contains the analogous
[`PositiveBlockOmega`](https://github.com/saasom/Erdos1144/blob/v1.0.0/Erdos/Problem1144/PositiveBlockCertificate.lean)
route, but its final stationary-candidate path avoids summable failures through the finite-cylinder
upper-envelope argument described above.

## 3. Conjectured local statement

This section is our conjectural proposal.  It is the intended content of the Lean assumption
classes, not a claim established by the cited papers.

Choose a rapidly increasing sequence `X_k` and a grid of endpoints

```text
X_k^(8/7) <= x_{k,j} <= X_k^(4/3).
```

For each natural height `h`, seek an event `E(h,k)` satisfying

```text
E(h,k) is contained in
  {there exists x in block k with S(x) / sqrt(x) >= h},       (3.1)

P(E(h,k)^c) <= delta(h,k),                                   (3.2)

sum_k delta(h,k) < infinity for every fixed h.               (3.3)
```

The event may be a strict surrogate for raw success: it can include good-variance, low-
covariance, Gaussian-approximation, and smooth-remainder conditions.  What matters is the
deterministic implication (3.1), not equality with the raw success event.

A useful local theorem would say that for each fixed `h` and `eta > 0`, all sufficiently large
`X` admit such a block with failure probability at most `eta`.  A diagonal scale choice can
then make, simultaneously for all `h <= k`,

```text
delta(h,k) <= 2^(-k).
```

The finitely many blocks with `k < h` are harmless, so (3.3) follows for every fixed height.

## 4. Our proposed route

Everything in this section is our idea unless explicitly attributed above.

### 4.1 Condition within a block, not across raw blocks

For each `X_k`, condition on `epsilon_p` for `p <= X_k` and write (2.1) as

```text
S(x) / sqrt(x) = R_X(x) + L_X(x),

L_X(x) = (1 / sqrt(x)) * sum_{X < p <= x} epsilon_p S(x / p),
```

where `R_X(x)` is the normalized `X`-smooth contribution.  Conditional on the small-prime
sigma-algebra, the vector `(L_X(x_{k,j}))_j` is a sum of independent random vectors.  This is
the independence exposed by the prime-factor split.  We do **not** assume that success events
from different `k` are independent.

The next analytic task is a conditional multivariate normal approximation.  Its target is a
set of many grid points with:

- variances bounded below;
- most pairwise covariances small relative to those variances;
- a Lindeberg or small-coefficient error adequate for a maximum estimate.

The tree's Dirichlet-polynomial mean values and random Euler-product infrastructure may help
with the covariance estimates, but no theorem currently supplies the target-model statement.

### 4.2 Make the Gaussian step one-sided

Harper's absolute maximum is insufficient.  We need a conditional estimate for

```text
max_j (L_X(x_{k,j}) + R_X(x_{k,j})) >= h.                    (4.1)
```

For a weakly correlated centred Gaussian vector, a large positive maximum is natural.  The
problem is the conditioned shift `R_X`: it could be negative on many grid points.  A valid
proof must therefore establish at least one of the following, with summably small exceptions:

1. `R_X` is not too negative on a positive proportion of the usable grid;
2. the Gaussian maximum is large enough to dominate its negative part;
3. a paired-endpoint or martingale argument absorbs the shift without replacing (4.1) by an
   absolute value.

The positive square mean does not justify any of these pathwise statements.  Smooth-remainder
control is the most conspicuous missing lemma.

### 4.3 Demand high probability, then use first Borel--Cantelli

Exact independence of raw block maxima is implausible because small prime signs influence all
later partial sums.  The proposed reduction instead asks for summable **failure** probabilities.
Once (3.1)--(3.3) hold, first Borel--Cantelli says that, for each `h`, almost every sample lies
in `E(h,k)` for all sufficiently large `k`.  A countable intersection handles all natural
heights.  Strictly increasing block starts make the associated witness indices unbounded, and
choosing `h >= M` handles an arbitrary real threshold `M`.

This closure is exactly what `erdos1144_of_assumptions` proves.

The tagged proof claim shows that this probability target is sufficient but not necessary.  Its
active route only needs a uniform positive crossing mass after conditioning on an arbitrary finite
prime cylinder.  That is enough to contradict positive density of any bounded-above envelope.  An
independent attempt should therefore not spend effort proving summable failures unless that stronger
estimate is genuinely easier for its chosen block decomposition.

## 5. Lean interface and proof DAG

`PrimeBlockScheme` contains only data:

```text
start         : Nat -> Nat
success       : Nat -> Nat -> Set Omega
failureBudget : Nat -> Nat -> ENNReal
```

The proof obligations are separate `Prop`-valued classes:

1. `PrimeBlockDecompositionAssumption scheme`
   - `start` is strictly monotone;
   - every `success h k` is measurable;
   - membership supplies `N` in `[start k, start (k+1))` with
     `h <= S(N) / sqrt(N)`.
2. `PositiveBlockProbabilityAssumption scheme`
   - `P(success h k complement) <= failureBudget h k` for every `h,k`.
3. `SummableBlockBudgetAssumption scheme`
   - `sum_k failureBudget h k` is finite for every fixed `h`.
4. `eventually_primeBlock_success`
   - proved from 2 and 3 using Mathlib's first Borel--Cantelli lemma.
5. `erdos1144_of_assumptions`
   - proved from 1, 4, countable intersection over `h`, and the Archimedean choice of a natural
     height above any real `M`.

The dependency graph actually checked by Lean is:

```text
PrimeBlockScheme
  └─ PrimeBlockDecompositionAssumption ───────────────────────┐
PositiveBlockProbabilityAssumption ─┐                         │
                                    ├─ eventually_primeBlock_success
SummableBlockBudgetAssumption ──────┘                         │
                                                              ├─ erdos1144_of_assumptions
all integer heights + exists_nat_ge + strict block starts ────┘
```

The classes do not assert `Erdos1144`, a limsup, or eventual success directly.  In particular,
the final recurrence implication is audited rather than hidden in an assumption.

Relative to the tagged release, this DAG abstracts the release's retained `PositiveBlockOmega`
comparison route, not the final stationary-candidate DAG.  The latter passes through a literal
fresh-prime Gaussian field, complete/squarefree stationary covariance comparisons, two uniform
Gaussian tail estimates, scheduled prime-law identification, a robust fixed-cylinder crossing,
and finally a cylinder-envelope gap.  Reproducing and auditing those links is more urgent than
trying to instantiate the stronger assumptions above from scratch.

## 6. Where the route can fail

These are current obstructions, not cosmetic details.

1. **Model transfer.**  Prime powers change the Euler product and all conditional variance and
   covariance estimates.  Reusing a theorem whose Rademacher function vanishes off squarefree
   integers would be invalid without a new comparison.
2. **One-sidedness.**  Neither an absolute maximum nor unbounded second moments fixes the sign.
3. **Smooth remainder.**  The conditioned `X`-smooth term is shared across the grid and can
   shift every fresh-prime linear form.
4. **Covariance.**  The endpoint linear forms reuse large-prime signs.  Fresh coordinates give
   conditional independence of summands, not independence of endpoints.
5. **Probability strength.**  A positive probability bounded away from zero is not enough for
   this first-Borel--Cantelli route.  One needs failure tending to zero fast enough to select a
   summable diagonal schedule, or a different conditional recurrence theorem.
6. **Uniformity in height.**  Each local theorem may depend on `h`; the scale sequence must be
   diagonalized so one scheme works for every integer height.
7. **Over-strong probability endpoint.**  Summably small failure is not known to be the natural
   estimate here.  The tagged claim's cylinder-envelope closure demonstrates a different endpoint
   from fixed positive conditional mass.  Failure to reach summable failure would not refute that
   proof strategy.

The established literature cited above does not resolve items 1--3 together in the form needed
to instantiate this stronger summable-failure route.  The v1.0.0 release claims to resolve the
original target through a different stationary/cylinder argument, but this memo has not
independently rebuilt or re-derived those analytic modules.  Thus the route here remains a research
program, not a near-formal proof with a missing routine estimate; the external claim remains a
high-priority verification target rather than an assumption silently imported into this reduction.

## 7. Phase 2 items

The proof claim changes the priority of Phase 2.  Independent reproduction and targeted audit
should come before a parallel attempt to rebuild its 207,626-line analytic closure.  Each item below
should be a separate PR.

### 7.1 Verification lane (preferred)

- **D3v: Architecture-matched rebuild and endpoint comparison** (`after: D1`; already on the
  card).  Rebuild tag `v1.0.0` at commit `a0050daf`, rerun `#print axioms`, and compare every target
  definition with this repository's `Statement.lean`.  Report only what the local rebuild shows.
- **D4v: Cylinder-envelope closure audit** (`after: D3v`).  Independently check the deterministic
  and measure-theoretic path from fixed-cylinder crossing mass to nullity of every upper envelope,
  focusing on cylinder concentration, quantifier order, and the passage from no global envelope to
  frequent positive crossings.
- **D5v: Complete/squarefree stationary comparison audit** (`after: D3v`).  Audit the exact
  covariance decompositions, positive-semidefinite comparisons, selector preservation, and scaling
  constants in the modules feeding `HarperCandidateScheduledCompleteWhite.lean`.
- **D6v: Uniform Gaussian-tail audit** (`after: D5v`).  Check both the high-frequency and
  stationary-extension tail rates, especially uniformity over the original grid cardinality and
  the use of `(alpha - 1) * kappa > 2`.
- **D7v: Final-certificate dependency audit** (`after: D4v, D6v`).  Trace the actual declarations
  used by `candidate_scheduledGaussianRobustCrossing_certificate`, rerun declaration-level axiom
  checks, and reconcile the result with the release's source snapshot and proof guide.

### 7.2 Independent stronger-failure lane (secondary)

- **D4: Large-prime block identity and measurable scheme** (`after: D3`).  Formalize (2.1),
  finite-coordinate measurability of its grid events, and a concrete `PrimeBlockScheme`; prove
  `PrimeBlockDecompositionAssumption` only when the surrogate-to-raw implication is fully
  established.
- **D5: Conditional variance and covariance package** (`after: D4`).  For the completely
  multiplicative sign model, prove lower conditional variance on many endpoints and a
  quantitative bound for exceptional covariance pairs.  Keep squarefree-model results behind
  an explicit transfer lemma rather than importing them silently.
- **D6: One-sided local positive maximum** (`after: D5`).  Add the conditional Gaussian
  approximation and control the smooth shift to prove the pointwise failure-budget inequality;
  discharge `PositiveBlockProbabilityAssumption`.
- **D7: Diagonal sparse schedule** (`after: D6`).  Choose one increasing scale sequence valid
  for all integer heights and prove `SummableBlockBudgetAssumption`.
- **D8: Unconditional assembly and audit** (`after: D4, D6, D7`).  Install the three instances,
  invoke `erdos1144_of_assumptions`, and audit that the resulting theorem uses only standard
  axioms.  If D6 or D7 remains conditional, D8 must remain blocked rather than restating an
  assumption as the conclusion.

## 8. Why this route was selected

The convolution route through squarefree `f` is attractive but leaves an uncontrolled
fractional-part term and does not preserve positive sign.  A direct claim of independence for
raw maxima is also false in spirit because small primes persist across scales.  The selected
route retains the transferable deterministic large-prime identity, uses independence only
after conditioning within a block, and asks for exactly the one-sided high-probability local
statement needed by a proved first-Borel--Cantelli closure.

After the v1.0.0 claim, “selected” means selected as the smallest independent conditional reduction
that satisfies this card item, not selected as the best current route to a new proof.  The tagged
stationary-candidate route has already exhibited a weaker and apparently more efficient probability
endpoint.  Unless its verification fails, the verification lane in §7.1 has higher evidentiary
value than extending the secondary lane in §7.2.
