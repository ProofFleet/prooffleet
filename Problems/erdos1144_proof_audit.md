# Erdős #1144: proof-idea audit of the stationary-candidate certificate

Audit date: 2026-09-08.  Audited release: `saasom/Erdos1144` v1.0.0,
commit [`a0050daf4bf4992355b5ab189ee9c75cd44795a3`](https://github.com/saasom/Erdos1144/commit/a0050daf4bf4992355b5ab189ee9c75cd44795a3).

## Status and scope

This is a mathematical reading guide, not a second proof and not a verdict on
the proof claim.  D3v already established the narrower machine fact: the
pinned source rebuilt, the endpoint has only Lean's standard axioms
`propext`, `Classical.choice`, and `Quot.sound`, and its statement matches our
Erdős #1144 statement.  See the
[independent verification memo](erdos1144_verification.md) and the release's
[complete-proof guide](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/notes/1144/complete_proof.md).

The present audit traces the active proof term backwards from
`candidate_scheduledGaussianRobustCrossing_certificate`.  It explains the
mathematics represented by the principal declarations, but it does not
rederive every estimate in the 294 candidate modules reported by the release.
In particular, the covariance moment campaign and the Rankin-ballot energy
campaign deserve line-by-line specialist review beyond what is attempted
here.

The evidence categories used below are intentionally separate.

### Known or directly checked

- The model, target, active declaration chain, constants, and displayed
  inequalities below are direct readings of the pinned Lean source.
- D3v independently rebuilt the source and checked the kernel dependency of
  the final certificate and theorem.
- The large-prime split, finite-product symmetry, Gaussian convolution,
  Fourier/Parseval conversion, Markov bounds, and density of finite cylinders
  are standard tools.  Calling a tool standard does not certify that every
  application here has received expert review.
- The squarefree lower-bound campaign is a formalized Harper-type
  variance/covariance and Gaussian-maximum argument.  Its methodological
  ancestor is Harper's paper on almost-sure large fluctuations
  ([arXiv:2012.15809](https://arxiv.org/abs/2012.15809)); the active certificate
  does not merely assume a theorem from that paper.

### Claimed mathematics not independently rederived here

The active Lean theorem has no analytic assumption, so there is no
`*Assumption` or conjectural premise inside its proof term.  Nevertheless, an
external mathematical referee still has to assess the long formalizations of
the Rankin-ballot half moment, near/far covariance-degree estimates,
prime-to-white approximation, reciprocal-zeta spectral comparison, and
uniform fractional energy moment.  This memo treats their proved Lean
statements as the proof claim under audit, not as independently established
paper theorems.

The problem page still labels #1144 open.  Acceptance, priority, and the claim
that particular mechanisms are new therefore remain external questions; this
memo uses “new” only to mean *new in the submitted route as described by its
authors*, not a literature-priority verdict.

### Our audit findings

- The active route is a cylinder-density contradiction, not a Borel--Cantelli
  argument.  It never requires independence of success events at different
  scales.
- A fixed positive absolute-crossing mass is enough.  The formal route does
  not need the crossing probability to tend to one.
- The formal stationary bridge uses an elementary factor-two reflection
  substitute three times, losing a factor eight.  This is more conservative
  than the informal candidate's appeal to Anderson's inequality, and the loss
  is visible in the final threshold and mass.
- The active stationary-extension tail uses a uniform `1/8` moment of a
  damped complete-process energy.  It does not use Atherfold's pathwise
  weighted upper bound at this step.
- Conditioning on old signs is represented by exact finite-cylinder laws and
  finite fresh-flip fibers.  This makes the independence boundary more
  explicit than the informal phrase “condition on the old signs.”

## 1. The route at a glance

For log time `t`, write

\[
  a_\omega(t)=\frac{S_\omega(\lfloor e^t\rfloor)}{e^{t/2}}.
\]

For a large-prime cutoff `X`, the proof constructs

\[
  a_\omega(t)=O_{X,\omega}(t)+Z_{X,\omega}(t),
\]

where `O` uses only `X`-smooth integers and `Z` is linear in the signs of
primes larger than `X`.  On a carefully chosen deterministic grid it proves a
fixed positive conditional probability that `|Z|` crosses a prescribed
threshold on a large set of indices where `O >= -b`.  A simultaneous flip of
all visible fresh signs makes at least half of that absolute crossing mass
positive.  Hence a positive crossing contradicts an assumed global upper
envelope for `a`.

The global closure is:

```text
squarefree prefix energy
  -> screened squarefree Gaussian crossing on a large retained set
  -> stationary squarefree field at the smaller time V = T / W
  -> low-frequency stationary complete field
  -> truncated complete white field
  -> finite fresh-prime Gaussian field
  -> actual fresh Rademacher field
  -> positive crossing after reflection
  -> a uniform probability deficit for every finite cylinder's upper envelope
  -> the upper envelope has measure zero
  -> arbitrarily late positive crossings above every real height.
```

The instantiated parameters are

\[
  \alpha=7/6,\qquad \beta=5/4,\qquad \kappa=18,\qquad \rho=1/2,
\]

so `1 < alpha < beta < 4/3` and
`(alpha - 1) * kappa = 3 > 2`.  The certificate is packaged in
[`candidate_scheduledGaussianRobustCrossing_certificate`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateFinalCertificate.lean#L9),
and the endpoint consumes exactly that certificate in
[`erdos1144`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/Final.lean#L266).

## 2. Exact large-prime decomposition and the independence boundary

Let `N < X^2`.  Every `n <= N` has at most one prime factor larger than
`X`, and such a factor occurs to exponent one.  Complete multiplicativity
therefore gives the exact identity

\[
  S_\omega(N)
   = \sum_{\substack{n\le N\\P^+(n)\le X}} f_\omega(n)
     + \sum_{X<p\le N}\varepsilon_p S_\omega(\lfloor N/p\rfloor).
\]

The source declarations are
[`S_eq_smoothSum_add_largePrimeContribution`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperDecomposition.lean#L386),
[`largePrimeProcess_eq_sum_coeff`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperProcess.lean#L362),
and, with the exact floor/exponential normalization,
[`harperCandidateLogProcess_eq_logOld_add_logFresh`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateLogScreen.lean#L26).

This is where the useful independence appears.  If `p > X`, then
`N/p < X`; consequently the coefficient `S(N/p)` uses no sign at a prime
larger than `X`.  The field is thus a linear form in fresh signs with
old-measurable coefficients.  The proof does not assert that the values at
different grid points are independent—they share both coefficients and fresh
primes.

There are four exact implementations of “freshness.”

1. The base product measure has independent coordinate projections in
   [`iIndepFun_coordinates`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/Model.lean#L46).
2. A finite assignment on coordinates `s` is unchanged by flips on a
   disjoint fresh set; the conditional law is measure-preserving by
   [`candidateCylinderLaw_freshSignFlip`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateCylinderScreen.lean#L23).
3. Averaging all finite fresh flips produces the exact product law of
   independent Rademacher signs in
   [`candidate_freshFlip_eps_law`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateGaussianFiber.lean#L39)
   and
   [`candidate_selected_fresh_sign_fiber_average`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateGaussianFiber.lean#L135).
4. Auxiliary Gaussian coordinates are explicit product measures
   `Measure.pi (fun _ => gaussianReal 0 1)`.  Gaussian covariance sums are
   realized using independent product components, for example in
   [`candidate_gaussian_selected_sum_le`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateStationaryGaussianComparison.lean#L75).

Thus “independence” is used inside a single scale to expose and replace the
fresh linear field.  It is not used between blocks or between successive
values of `T`.

**Classification: standard.**  The unique-large-prime split and conditioning
principle are classical.  The exact finite-flip formulation is a careful
formal implementation whose quantifier order should still be audited.

## 3. Obtaining fixed positive crossing mass under every cylinder

The lower crossing is first proved for an auxiliary squarefree white-noise
field.  The path has three layers.

### 3.1 A simultaneous variance floor

The Rankin/ballot campaign proves a lower half moment for a squarefree
coefficient-prefix energy in
[`candidate_rankinShiftedHalfMomentLowerStatement_unconditional`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateEnergyHalfMoment.lean#L198).
It yields a fixed-probability energy event.  Finite coordinate changes compare
that event across every cylinder; the probability `delta` remains universal,
while the numerical energy floor loses a factor `49 ^ s.card`.  The relevant
endpoint is
[`candidate_exists_squarefree_prefix_energy_lower_probability_cylinder`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateEnergyLowerEvent.lean#L65).

The common prefix energy gives a variance lower bound simultaneously at every
point of every finite grid in `[alpha*T,beta*T]`.  The source packages this as
[`candidate_exists_squarefree_white_variance_lower_probability`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateGaussianVarianceLower.lean#L75),
then pays mesh, screen-deletion, and Perron approximation errors in
[`candidate_exists_scheduledRetainedVariance_probability_linear_grid`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateCovarianceScheduledRetainedVariance.lean#L70).

The important quantifier is “all grid coordinates” on one energy event.  The
event is not selected after a Gaussian winner is seen.

**Classification: delicate.**  The half-moment lower bound, its second-moment
control, the finite-cylinder energy comparison, and preservation of a
simultaneous floor are substantial parts of the claim.  The method is
Harper-type; the exact unconditional chain is specific to this development.

### 3.2 Covariance degree and a Gaussian maximum

Near- and far-covariance moments imply that the graph of pairs whose
covariance exceeds the threshold has maximum degree at most about
`T^(4/5)`, with failure tending to zero uniformly for every grid cardinality
`n <= T`.  The assembled statement is
[`candidate_exists_scheduledGridDegreeControl_uniform_failure`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateCovarianceScheduledGridDegree.lean#L88).

The retained selector always has at least `2*T^(9/10)` points.  Greedy
thinning leaves enough weakly correlated coordinates because `9/10 - 4/5 =
1/10`.  After variance normalization, a Gaussian maximum estimate gives at
least `1/4` crossing probability.  The finite Gaussian core is
[`candidate_gaussian_selected_max_ge_quarter_of_bad_degree`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateGaussianSelectedLower.lean#L73),
and the fully screened conclusion is
[`candidate_exists_squarefreeWhite_linear_grid_crossing`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateGaussianWhiteGridLower.lean#L51).
The latter takes `p = delta/16`, so `p > 0` is independent of the cylinder,
grid, selector, and fixed log-log threshold parameters.

**Classification: delicate.**  Greedy thinning and the Gaussian maximum bound
are standard, but the near/far moment rates, uniformity in `n`, and the
interaction of the exponents `4/5`, `9/10`, and the shrinking variance scale
are among the highest-value places for independent checking.

### 3.3 Change to the stationary time scale

Put

\[
  W=\kappa\log\log T,\qquad V=T/W,\qquad D=T/W^2.
\]

The outer schedule has about `D/(2*pi)` coordinates, but the squarefree
lower theorem is applied at observation time `V`.  Exact rounding lemmas show
that the original coordinate count is at most `V`, the same retained selector
has more than `2*V^(9/10)` points, and the translated grid lies in
`[alpha*V,beta*V]`.  The stationary transfer threshold is shown to be at most
a fixed multiple of `log(1+log V)^8`, within the preceding theorem's range.
This is exactly
[`candidate_exists_stationary_squarefree_selected_lower`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateStationarySquarefreeLower.lean#L15).

**Classification: standard but delicate bookkeeping.**  The rescaling idea is
natural; cofinal limits, floors, original versus translated cardinality, and
preservation of the random selector are easy places for a silent quantifier
error.  Here they are explicit declarations rather than prose estimates.

## 4. The stationary squarefree-to-complete bridge

This is the conceptual center of the claimed proof.  For one frozen sign
world and one selected finite grid, let:

- `A` be the squarefree white covariance at time `V`;
- `L + H` be its stationary covariance split at spectral cutoff
  `|tau| = (log T)^2`;
- `Q + E` be the complete stationary covariance split into the retained
  time range and the omitted stationary extension;
- `B` be the complete white covariance at time `T`.

The source proves three positive-semidefinite comparisons, with diagonal
rescalings `R` and `D`:

\[
  L+H\succeq RAR,\qquad Q+E\succeq cL,\qquad
  \lambda B\succeq DQD.                                      \tag{4.1}
\]

The first and last are time-domain weight comparisons.  The middle one is the
arithmetic bridge.  Fourier transformation identifies the stationary
covariances with spectral densities; the exact complete/squarefree transform
identity contributes a zeta factor; a reciprocal-zeta bound on
`|tau| <= (log T)^2` yields

\[
  c=\frac{1}{W\,[C\log(2(\log T)^2+4)^7]^2}.
\]

The pointwise density comparison is
[`exists_candidate_complete_spectralDensity_window_domination`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateSpectralWindow.lean#L59),
and its PSD covariance form is
[`exists_candidate_complete_stationaryCovariance_window_domination`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateSpectralCovariance.lean#L239).

The three comparisons are assembled in
[`candidate_exists_ae_squarefree_complete_white_comparison`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateStationaryWhiteComparison.lean#L24).
The finite-dimensional Gaussian lemma behind it is
[`candidate_gaussian_stationary_selected_comparison`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateStationaryGaussianComparison.lean#L108),
which proves schematically

\[
 \frac{1}{8}P(\max_{i\in J}|G_A(i)|>K_*)
 \le P(\max_{i\in J}|G_B(i)|>K)
      +\frac14P(\max|G_H|\ge1)
      +\frac12P(\max|G_E|\ge1).                              \tag{4.2}
\]

The same selected set `J` survives all three comparisons.  Each factor two
comes from the reflection lemma
[`candidate_multivariateGaussian_selected_absolute_ge_half`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateGaussianComparison.lean#L57):
if `B-A` is PSD, realize `G_B = G_A + G_{B-A}` with independent centered
Gaussians and compare the two reflected values of the added component.  This
is not a direct invocation of Anderson's inequality.

**Classification: new.**  The proof candidate itself identifies the two
stationary covariance comparisons as essential new steps.  This audit does
not judge priority, but (4.1), the zeta normalization, and the factor-eight
selected-crossing transfer are the most distinctive ideas of the route and
the first target for a specialist referee.

## 5. Why both omitted Gaussian fields vanish

Equation (4.2) has two error fields.

1. For the squarefree high-frequency covariance `H`, Parseval and
   squarefree orthogonality give a diagonal tail bound.  A finite Gaussian
   maximum inequality costs only `log(2m)`.  With `m <= T` and cutoff
   `(log T)^2`, the averaged tail probability tends to zero uniformly over
   grid locations.  The scheduled result is
   [`candidate_eventually_squarefreeHighCovariance_tail_lt`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateStationaryGaussianTailRates.lean#L22).
2. For the complete stationary extension `E`, the omitted variance is bounded
   by `exp(-cW)/W` times the damped energy
   \[
      \sigma\int_0^\infty e^{-2\sigma t}a_\omega(t)^2\,dt.
   \]
   The development proves a uniform `1/8` moment of this energy from finite
   Euler-frequency estimates, Fourier convergence, zeta factorization,
   Parseval, and Fatou in
   [`candidate_exists_dampedCompleteEnergy_uniform_eighth_moment`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateEnergyFatouUniform.lean#L13).
   Markov plus the Gaussian maximum bound makes the scheduled error vanish
   when `2 < c*kappa`; this is
   [`candidate_eventually_stationaryExtension_tail_lt`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateStationaryGaussianTailRates.lean#L75).

Integrating the pointwise comparison in the old sign world is justified in
[`candidate_exists_integral_squarefree_complete_white_comparison`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateStationaryWhiteAveraging.lean#L12).
Combining the squarefree mass, (4.2), the two vanishing tails, and the exact
schedule geometry gives a complete-white crossing mass `p/8 - epsilon` in
[`candidate_exists_scheduled_completeWhite_crossing`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateScheduledCompleteWhite.lean#L14).

**Classification: delicate.**  Gaussian maximum bounds and Markov are
standard.  Uniformity of the spectral tail and, especially, the uniform
fractional complete-energy moment as the damping tends to zero are major
analytic claims.  The formal route here is materially different from the
informal candidate's use of an almost-sure weighted bound.

## 6. White noise, finite prime Gaussians, and actual signs

The complete white field is still an integral Gaussian field.  Two further
transfers identify it with the actual fresh-prime contribution.

First partition the log-prime interval into bins of width
`h = exp(-T^(1/20))`.  Prime-number-theorem estimates match the bin variances
to white-noise increments; mean-square increment estimates replace bin
endpoints by the actual kernels.  The comparison is uniform over grids of at
most polynomial size, fixed cylinders, and arbitrary measurable selectors:
[`candidate_eventually_prime_white_ceil_selected_crossing_le`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidatePrimeWhiteComparisonRates.lean#L148).

The whole-bin covariance is then identified exactly with the increasing
enumeration of the primes visible on the actual grid by
[`candidate_complete_comparison_prime_crossing_eq_fresh`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateScheduledPrimeLaw.lean#L80).
The assembled white-to-literal-Gaussian statement is
[`candidateSchedule_completeWhite_fresh_selected_crossing`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateScheduledWhiteAssembly.lean#L41).

Finally, a smooth multivariate Lindeberg replacement changes the independent
standard Gaussians to independent signs.  Its relevant error is bounded by

\[
  C m^3\exp((3\beta/2-2)T),
\]

which vanishes for the scheduled `m <= T` because `beta < 4/3`.  The analytic
replacement is
[`candidate_selected_fresh_max_rademacher_comparison`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateGaussianFresh.lean#L10);
the exact cylinder/fiber transfer is
[`candidate_conditional_logFresh_max_comparison`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateGaussianConditional.lean#L144).

**Classification: new for the prime-to-white coupling; standard for the
Lindeberg replacement.**  The binning and accumulated error estimates are
delicate.  The final sign replacement is a familiar invariance-principle
step, but its application depends crucially on the coefficients and retained
selector being invariant under every fresh flip.

## 7. From an absolute fresh crossing to a deterministic screen

The outer argument controls the old negative contribution without trying to
bound it uniformly over the whole grid.

For every fixed `T > 0`, the finite-smooth Laplace transform is a strictly
positive finite Euler product.  Mean absolute convergence of the smooth
transforms implies almost-sure nonnegativity of the full transform,

\[
  \int_0^\infty e^{-t/T}a_\omega(t)\,dt\ge0.
\]

The exact declarations are
[`candidate_integral_laplace_logOld_pos`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateLaplaceSmooth.lean#L210),
[`candidate_ae_laplace_nonneg`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateLaplaceApproximation.lean#L246),
and its cylinder version
[`candidateCylinderLaw_ae_laplace_nonneg`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateLaplaceApproximation.lean#L253).

If `E_M` is the event that every normalized cutoff is at most `M`, this
positivity bounds the time integral of the negative part of `a`.  Fresh-sign
reflection also gives

\[
  Q(O_X(t)<-b)\le 2Q(a(t)<-b).
\]

Average these probabilities over `[alpha*T,beta*T]`, partition almost all of
the interval into blocks of width `2*pi*m`, and average the grid shift in
`(0,2*pi]`.  This produces one deterministic block and shift—chosen from
probabilities, not from the realized signs—whose mean number of old-bad
indices is small.  The exact result is
[`candidate_exists_log_grid_old_negative_average_le`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateOldTailGrid.lean#L52).

Define the retained selector to be the old-good indices if they occupy at
least a fraction `rho` of the grid, and the full grid otherwise.  Markov's
inequality bounds the fallback event.  The selector remains invariant under
fresh flips.  A common flip negates every fresh coordinate and fixes every old
coordinate, so at least half the absolute crossing mass becomes a positive
crossing.  On a non-fallback world, that positive crossing plus `O >= -b`
contradicts `a <= M`.  This finite-screen inequality is
[`candidate_measureReal_log_envelope_le_of_absolute_crossing`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateLogScreen.lean#L87).

The exact schedule

```text
W = kappa * log(log T)
D = T / W^2
m = floor(D / (2*pi))
number of blocks = floor((beta-alpha)*T / (2*pi*m))
X = floor(exp T)
```

pays the discarded terminal interval and chooses `b` before `T`.  The
assembly from the Laplace bound plus robust crossing to a cylinder screen is
[`candidateLogCylinderScreenStatement_of_scheduledInputs`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateScheduleAssembly.lean#L53).

**Classification: new.**  The submitted candidate identifies this averaged
negative-tail contradiction as an essential new step.  The individual tools
are elementary, but the deterministic block selection, old-measurable
fallback selector, and preservation of a cylinder law by the common flip are
the mechanism that converts an absolute Gaussian maximum into the required
one-sided statement without paying a number-of-blocks factor.

## 8. The cylinder-envelope density-gap closure

Fix a natural height `M`, a cylinder `C(s,eta)`, and write

\[
  q=Q_{s,\eta}(E_M).
\]

The scheduled old-tail bound is asymptotically at most
`2*(1-q)` per coordinate.  If the robust absolute fresh crossing has mass
`p0`, the reflection and fallback estimates give, for every `epsilon > 0`,

\[
 q\le 1-\frac{p_0-\epsilon}{2}
       +\frac{2(1-q)+\epsilon}{1-\rho}.
\]

Letting `epsilon` disappear and solving for `q` yields

\[
  q\le 1-\frac{p_0(1-\rho)}{2(3-\rho)}.                       \tag{8.1}
\]

This is
[`candidate_conditionalEnvelope_gap_of_logScreens_with_mass`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidatePositiveScreen.lean#L60).
The right-side deficit is uniform over every finite coordinate set and
assignment; it may depend on the fixed height `M` through the screen, although
the instantiated crossing mass itself is universal.

Now suppose `mu(E_M) > 0`.  Density of the finite-cylinder algebra gives a
single assignment cylinder on which the conditional density of `E_M` is
arbitrarily close to one.  Choosing it closer than the fixed deficit in
(8.1) contradicts (8.1).  Hence `mu(E_M)=0`.  The relevant declarations are
[`exists_candidateCylinder_concentration`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateEnvelope.lean#L94),
[`candidate_upperEnvelope_null_of_cylinder_gap`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateEnvelope.lean#L167),
and
[`erdos1144_of_candidateConditionalEnvelopeGap`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateEnvelope.lean#L197).

Intersecting the complements of `E_M` over natural `M` gives one
probability-one event.  Absence of every global integer upper envelope is
upgraded to *frequent* crossing above every real `A`: given a starting index,
choose `M` larger than both `A` and the deterministic square-root bound on
that finite prefix.  This is
[`candidate_positive_frequently_of_no_upperEnvelope`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/HarperCandidateEnvelope.lean#L147).

**Classification: standard.**  This is a density theorem for a generating
finite-cylinder algebra followed by a countable null-set argument.  Its
importance is structural: it removes any need for a tail-event zero-one law,
block independence, or summable block failures.

## 9. Declaration ledger and primary classification

“New” below means distinctive to the submitted route, not a priority claim.
“Delicate” means that the declaration packages a substantive chain whose
mathematical content merits independent rechecking.

| Mathematical step | Primary classification | Principal Lean declarations |
|---|---|---|
| Complete large-prime split at `N < X^2` | Standard | `S_eq_smoothSum_add_largePrimeContribution`; `harperCandidateLogProcess_eq_logOld_add_logFresh` |
| Exact fresh-coordinate law under a fixed cylinder | Standard | `candidateCylinderLaw_freshSignFlip`; `candidate_freshFlip_eps_law`; `candidate_selected_fresh_sign_fiber_average` |
| Rankin/ballot prefix-energy lower event in every cylinder | Delicate | `candidate_rankinShiftedHalfMomentLowerStatement_unconditional`; `candidate_exists_squarefree_prefix_energy_lower_probability_cylinder` |
| Uniform retained variance and covariance-degree screen | Delicate | `candidate_exists_scheduledRetainedVariance_probability_linear_grid`; `candidate_exists_scheduledGridDegreeControl_uniform_failure` |
| Positive squarefree Gaussian maximum on arbitrary dense selectors | Delicate | `candidate_gaussian_selected_max_ge_quarter_of_bad_degree`; `candidate_exists_squarefreeWhite_linear_grid_crossing` |
| Translation to the smaller stationary time | Standard | `candidate_exists_stationary_squarefree_selected_lower` and the `candidateScheduleWhiteTime*` geometry lemmas |
| Three-PSD stationary squarefree/complete bridge | New | `exists_candidate_complete_stationaryCovariance_window_domination`; `candidate_gaussian_stationary_selected_comparison`; `candidate_exists_ae_squarefree_complete_white_comparison` |
| Vanishing high-frequency and stationary-extension tails | Delicate | `candidate_eventually_squarefreeHighCovariance_tail_lt`; `candidate_exists_dampedCompleteEnergy_uniform_eighth_moment`; `candidate_eventually_stationaryExtension_tail_lt` |
| Log-prime Gaussian to white-noise comparison | New | `candidate_eventually_prime_white_ceil_selected_crossing_le`; `candidateSchedule_completeWhite_fresh_selected_crossing` |
| Gaussian-to-sign replacement | Standard | `candidate_selected_fresh_max_rademacher_comparison`; `candidate_conditional_logFresh_max_comparison` |
| Laplace-positive old-tail averaging and retained screen | New | `candidate_ae_laplace_nonneg`; `candidate_exists_log_grid_old_negative_average_le`; `candidate_measureReal_log_envelope_le_of_absolute_crossing` |
| Cylinder density gap and frequent-exceedance closure | Standard | `candidate_conditionalEnvelope_gap_of_logScreens_with_mass`; `candidate_upperEnvelope_null_of_cylinder_gap`; `candidate_positive_frequently_of_no_upperEnvelope` |

## 10. Questions a referee should ask

These are requests for focused checking, not assertions that a defect exists.

1. **Rankin-ballot provenance.**  Can the first- and second-moment estimates
   feeding `candidate_rankinShiftedHalfMomentLowerStatement_unconditional` be
   restated as a compact paper lemma, with every uniformity parameter and the
   polynomial loss `38` visible?
2. **Cylinder energy transfer.**  Does the finite-flip comparison leading to
   the `49 ^ s.card` loss cover arbitrary natural-coordinate cylinders,
   including non-prime coordinates, without changing the universal lower
   probability `delta`?
3. **Uniform covariance screen.**  In the near/far moment campaign, are the
   bounds genuinely uniform in every grid size `n <= T`, affine origin, fixed
   cylinder, and measurable retained selector used later?  Are the Markov and
   maximum-degree thresholds in the right direction?
4. **Exponent budget.**  Recheck the whole chain using degree `T^(4/5)`,
   retained size `2*T^(9/10)`, variance
   `(1+log T)^(-1/2)`, and an eighth-power log-log threshold.  Does the
   Gaussian density criterion still have polynomial room after every
   normalization?
5. **Selector timing.**  At each Gaussian comparison, is the selector fixed
   after conditioning on the sign world but before sampling Gaussian noise?
   At each sign replacement, are both the selector and every coefficient
   invariant under the finite fresh cube?
6. **Fourier normalization.**  Verify the factors `2*pi`, the passage from
   ordinary to angular frequency, the damping `sigma=W/T`, and the relative
   normalizations `T` versus `V=T/W` in
   `candidateStationaryCovariance_eq_spectral`.
7. **Zeta bridge.**  Recheck the exact Fourier identity relating the complete
   and squarefree log processes, the argument `1+2*sigma+2*i*tau` of zeta,
   zero-freeness on the closed window, and the uniform seventh-log
   reciprocal-zeta estimate.  Does squaring it produce precisely the constant
   `c` used in the PSD comparison?
8. **PSD directions.**  Check all three inequalities in (4.1), especially
   translation of the stationary grid, the diagonal factors `R` and `D`, and
   the scalar `lambda = beta*exp(2*sigma*D)`.  Reversing any one order would
   reverse the maximum comparison.
9. **Reflection versus Anderson.**  The formal proof loses a factor two at
   each PSD transfer.  Confirm that the reflection cover proves the stated
   result even for singular covariance matrices and arbitrary selected
   absolute-max events, and that all three losses are included in the
   threshold and final mass.
10. **High-frequency tail.**  Verify that the spectral diagonal bound is
    uniform in coordinate location, that `log(2m)` is the only maximum cost,
    and that restriction to a fixed cylinder merely divides the expectation
    by its fixed positive mass.
11. **Complete-energy moment.**  The stationary-extension estimate now rests
    on a uniform `1/8` moment rather than a pathwise Atherfold bound.  Check the
    finite spectral moment, prime-Euler/Fourier limit, the two Fatou steps, and
    uniformity for every `0 < sigma <= 1/8`.
12. **Tail-rate arithmetic.**  Starting from that fractional moment, redo the
    optimization of the energy cap and verify that `2 < (alpha-1)*kappa` is
    sufficient after the grid maximum and cylinder losses.  For the chosen
    constants it becomes `2 < 3`.
13. **Prime-to-white comparison.**  For bins of width
    `exp(-T^(1/20))`, verify the prime-number-theorem error, the last
    overshooting bin, the mean-square increment bound for the complete model,
    and accumulation over all `m <= T` coordinates.
14. **Lindeberg error.**  Confirm the cubic coefficient budget and that
    `m^3*exp((3*beta/2-2)T)` is the full active replacement loss.  Check that
    the strict condition `beta < 4/3` is used before any limiting choice of
    grid or cylinder.
15. **Auxiliary continuation.**  The stationary fields depend on the full
    sign world although the literal fresh coefficients depend only on old
    signs.  Verify that integration under one fixed cylinder law, followed by
    the fiber identities, implements the claimed auxiliary continuation
    without conditioning on an actual fresh sign.
16. **Laplace positivity quantifiers.**  The finite smooth Euler products are
    positive for each `X`; the full transform is nonnegative only almost
    surely at each fixed `T`.  Confirm that the screen chooses `T` in an order
    compatible with those almost-everywhere statements and never intersects
    uncountably many exceptional sets.
17. **Deterministic grid selection.**  Check the Fubini and measurability steps
    in `candidate_exists_log_grid_old_negative_average_le`, especially that
    the block and shift depend only on averaged probabilities and introduce
    no hidden factor equal to the number of blocks.
18. **Final algebra.**  Recompute the fallback Markov loss, the one-half
    positive-reflection loss, and the rearrangement yielding (8.1).  Confirm
    that the final cylinder deficit is positive and uniform in `s,eta`.
19. **Density closure.**  Confirm that the measurable finite cylinders used
    by `MeasureDense` generate the full product sigma-algebra and that every
    assignment cylinder has positive measure, including cylinders containing
    irrelevant non-prime coordinates.
20. **Integer endpoint.**  Recheck the floor/exponential normalization and the
    last passage from absence of a global natural-height envelope to frequent
    integer-cutoff exceedances above every real threshold.  This is where
    one-sided unboundedness becomes the exact `Frequently` target.

## Bottom line

The certificate route has a coherent mathematical spine.  It exposes fresh
prime signs linearly, builds a fixed positive squarefree Gaussian crossing on
large old-measurable selectors, transfers that crossing through a stationary
spectral comparison to the complete field, replaces Gaussian noises by the
actual signs, and closes by a finite-cylinder density gap.  The outer closure
is especially clean: it uses neither scale-to-scale independence nor
Borel--Cantelli.

What remains after D3v is mathematical review, not a visible formal premise.
The highest-value audit targets are the Rankin-ballot energy lower bound, the
near/far covariance-degree rates, the zeta-based PSD bridge, the uniform
damped-energy eighth moment, and the prime-to-white accumulated error.  This
memo found no contradiction in the declaration-level route, but it does not
turn that reading into an independent proof or change the problem's external
status.
