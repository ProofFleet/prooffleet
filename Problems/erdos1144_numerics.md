# Erdős #1144: numerical reconnaissance

This memo studies the model on the [Erdős #1144 problem page](https://www.erdosproblems.com/1144):
choose independent signs `f(p) ∈ {−1,1}` at the primes and extend them **completely**
multiplicatively.  It does not simulate the squarefree-supported Rademacher model.

## Reproduction

The recorded run used:

```bash
python3 scripts/research/erdos1144_numerics.py \
  --N 10000000 --trials 256 --seed 1144 --quiet \
  --output /tmp/erdos1144_N1e7_T256_seed1144.json
```

Environment: Python 3.13.5, NumPy 2.1.3, Numba 0.61.0.  The script records these
versions, every final per-trial value, and all aggregate statistics in its JSON output.
It uses `numpy.random.PCG64`, with `SeedSequence(1144).spawn(256)` giving one stream per
trial.  Hence trial `k` is stable if the trial loop is reordered or batched.

A shared smallest-prime-factor sieve found 664,579 primes through `10^7` (the known
value of `π(10^7)`).  For each trial the recurrence

```text
f(1) = 1,          f(n) = f(spf(n)) f(n / spf(n))
```

then generates the completely multiplicative function.  An independent trial on every
`n ≤ 500` compared this recurrence against direct repeated factorization and agreed at
every partial sum.  The full run took 14.35 seconds on the research worktree machine;
timing is not part of the numerical claim.

## Known facts and source-grounded comparators

### The target has a deterministic square bias

For this completely multiplicative sign model,

```text
E f(n) = 1  if n is a square,
         0  otherwise.
```

Indeed, an odd exponent in the prime factorization leaves a mean-zero prime sign, while
all exponents are even for a square.  Thus

```text
E S(N) = floor(sqrt(N)).
```

At `N = 10^7`, the exact expected normalized value is `3162/sqrt(10^7) =
0.999912`.  This is an elementary check specific to the target model and explains why
raw positive and negative fluctuations should not look symmetric.

### Harper's `(log log N)^(1/4)` scale is not a theorem for this model

Harper defines the Rademacher model to be supported only on squarefree integers and
proves, for that model and the Steinhaus model,
`E|S(N)| ≍ sqrt(N)/(log log N)^(1/4)`; see the definitions and Theorems 1–2 in
[Harper, *Moments of random multiplicative functions, I*](https://arxiv.org/abs/1703.06654).
The normalized comparator `1/(log log N)^(1/4)` is included in the output, but it must
not be transferred to the completely multiplicative sign model without a new argument.
For orientation it equals `0.774446` at `N = 10^7`.

### Atherfold's upper envelope

Atherfold explicitly relates a squarefree-supported Rademacher function `f` to the
completely multiplicative sign function `f*` in equations (1.7)–(1.8).  Corollary 1
bounds the weighted sum of `f*`, and the following partial-summation paragraph gives,
for every `ε > 0`, almost surely

```text
sum_{n ≤ x} f*(n) ≪ sqrt(x) (log x)^(1+ε).
```

See pp. 5–6 of [Atherfold, *Almost sure bounds for weighted sums of Rademacher random
multiplicative functions*](https://arxiv.org/abs/2501.11076).  The
[problem page](https://www.erdosproblems.com/1144) records this as
`sqrt(x) (log x)^(1+o(1))`.  At `10^7`, the baseline normalized comparator `log N` is
`16.1181`.  Since the theorem is asymptotic and has a sample-dependent implied constant,
finite samples above or below `log N` neither test nor contradict it.

## Numerical observations

Everything in this section is an observation from the fixed-seed run, not an
almost-sure statement.

### Fixed endpoint `N = 10^7`

| Statistic | `S(N)/sqrt(N)` | `(S(N) - floor(sqrt(N)))/sqrt(N)` |
|---|---:|---:|
| mean | 1.1438 | 0.1438 |
| sample standard deviation | 3.6225 | 3.6225 |
| minimum | -4.8143 | -5.8142 |
| 5% quantile | -0.6748 | -1.6747 |
| 25% quantile | -0.0283 | -1.0282 |
| median | 0.3624 | -0.6375 |
| 75% quantile | 1.1686 | 0.1687 |
| 95% quantile | 5.3322 | 4.3323 |
| maximum | 42.4074 | 41.4075 |

The raw mean is compatible with the exact mean `0.999912`, but it is not representative
of a typical trial.  The endpoint distribution is strongly right-skewed: removing only
the largest observation changes the mean from `1.1438` to `0.9819`, while the median is
`0.3624`.  Of 256 endpoints, 191 were positive and 65 negative.

The extreme endpoint is trial 164: `S(10^7) = 134104`, or `42.4074 sqrt(N)`.
The most negative endpoint is trial 124: `S(10^7) = -15224`, or `-4.8143 sqrt(N)`.

### Running extrema and `log log N`

Here `max` and `min` mean extrema of `S(n)/sqrt(n)` over all `1 ≤ n ≤ N`.
The Harper column is only the squarefree/Steinhaus endpoint comparator described above.

| `N` | `log log N` | `1/(log log N)^(1/4)` | endpoint median | running max median | running max mean | running max 95% | running min median |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 100 | 1.5272 | 0.8996 | 0.6000 | 1.4142 | 1.9847 | 5.0829 | -0.4472 |
| 1,000 | 1.9326 | 0.8481 | 0.5060 | 1.5076 | 2.2454 | 5.5967 | -0.6207 |
| 10,000 | 2.2203 | 0.8192 | 0.5000 | 1.5678 | 2.4235 | 6.1679 | -0.7071 |
| 100,000 | 2.4435 | 0.7998 | 0.3700 | 1.6155 | 2.5717 | 6.7213 | -0.8333 |
| 1,000,000 | 2.6258 | 0.7856 | 0.3300 | 1.6870 | 2.6938 | 6.7816 | -0.9175 |
| 10,000,000 | 2.7799 | 0.7744 | 0.3624 | 1.7120 | 2.7883 | 6.9969 | -0.9551 |

At the final cutoff, 106/256 paths reached a positive running maximum at least `2`,
65/256 reached at least `3`, 32/256 reached at least `5`, and 13/256 reached at least
`7`.  Forty-four paths set their final record after `10^6`, so all record growth is not
an artifact of the smallest indices.  The largest path maximum was `42.4498` at
`n = 9,981,965` (trial 164).  The smallest path minimum was `-5.4441` at
`n = 4,700,333` (trial 161).

The median running maximum rises from `1.4142` to `1.7120` while
`(log log N)^(1/4)` rises from `1.1117` to `1.2912`.  This very short range in
`log log N` cannot distinguish bounded growth, a small power, or a slower law.

## Conjectured interpretation

The conjecture is that the **positive** running maximum is unbounded almost surely.
The monotone empirical maxima and the late records are consistent with that conjecture,
but a finite simulation cannot test an almost-sure limsup.  The single value `42.4498`
is evidence of a heavy positive tail at this scale, not evidence that a typical path has
begun a divergent regime.

No claim is made that Harper's squarefree/Steinhaus first-moment scale governs this
model.  In particular, the deterministic square contribution and the observed skewness
are concrete obstructions to reading the table through a symmetric or centered-normal
heuristic.

## Our ideas for the next numerical pass

1. Condition on the signs of the first few primes.  Trial 164 suggests that rare
   small-prime configurations may dominate both the mean and the positive tail; stratified
   sampling would estimate those contributions far better than adding unconditioned trials.
2. Record maxima on disjoint logarithmic blocks, not only cumulative maxima.  This would
   separate genuinely new large-scale records from a large record inherited from small `n`.
3. Run the centered diagnostic `S(N) - floor(sqrt(N))` alongside the raw conjectural
   quantity, but never replace the raw one: centering removes a known mean, whereas Erdős
   #1144 asks about `S(N)/sqrt(N)` itself.
4. Extend selected prime-sign samples past `10^7` using a segmented smallest-prime-factor
   pass.  Following the same paths is more informative for recurrence than drawing fresh
   samples at each cutoff.

These are experimental proposals only; none supplies a transfer theorem or a proof route.
