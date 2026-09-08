# Erdős #177: finite residue-prefix balancing experiment

## Executive summary

This report tests the finite interface isolated in `Problems/erdos177_approach.md`. For each
`α ∈ {1/2, 1, 2, 4, 7}` and `N ∈ {256, 1024, 4096, 8192}`, the extended
`scripts/research/erdos177_numerics.py` constructs a sign vector in rounds and then evaluates every
constraint in `FiniteResiduePrefixWitness f α C N`, for all steps `1 ≤ d ≤ N`.

The achieved barrier grows from `2.333333` to `3.420744` for `α=1/2`, from `1.6` to `2` for
`α=1`, and from `1` to `1.16` for `α=2`. It is exactly `1` at all four horizons for `α=4` and
`α=7`. Thus the run exhibits a bounded barrier over the tested range for `α=4,7`, but not for
`α=1/2`; the `α=1,2` data are inconclusive. These are finite achieved bounds, not evidence strong
enough to discharge C3-BAL or prove any infinite exponent.

## 1. Known definitions and checks

For a sign vector `x : {0,...,N-1} → {−1,1}`, define its finite residue-prefix barrier by

```text
B(N, α, x) = max |sum_{j<M} x(r + jd)| / d^α,
               d > 0, r < d, r + Md ≤ N.
```

This is the normalized maximum in the Lean definition `FiniteResiduePrefixWitness`. In
particular, an output with `B(N,α,x)=C` is a checked finite witness with that numerical constant.
The endpoint condition matters: the last sampled index is at most `N-d`. The new evaluator uses
that condition literally rather than reusing the interval-discrepancy profile from the Phase-1
experiment.

For every nonempty finite witness, `B(N,α,x) ≥ 1`: take `d=1`, `r=0`, and `M=1`. Consequently,
the barrier-`1` results below are certified optimal for those particular finite instances even
though their construction was heuristic.

The self-test performs three independent checks:

1. it compares the optimized profile with a definition-level `(d,r,M)` loop on random small
   instances;
2. at every partial-coloring checkpoint, it compares the traced barrier with a fresh evaluation
   after replacing all not-yet-colored entries by zero;
3. it reconstructs a searched sign string and checks the reported final barrier from scratch.

## 2. Conjectured and unresolved content

C3-BAL, formalized as `FiniteResiduePrefixBalancingAssumption α`, asserts that one constant `C`
works for every finite horizon. The experiment checks only four horizons. It does not establish
that the observed constants remain bounded, and its independently optimized witnesses are not
prefixes of one common infinite coloring.

The central unresolved question for these data is whether growth with `N` is mathematical or an
optimizer artifact. This is clearest at `α=1/2`, where the best-found barrier rises at every
horizon, but four data points cannot distinguish slow divergence from a bounded sequence whose
small instances have not saturated. Conversely, a flat table at `α=4,7` does not prove uniform
finite feasibility.

## 3. Our computational idea

### 3.1 Prefix-frozen rounds

The search begins with the zero partial coloring. A round freezes half of the remaining
positions, always extending the already frozen contiguous prefix:

```text
N/2, 3N/4, 7N/8, ..., N-1, N.
```

Earlier signs are never revisited. At each round, four independently perturbed extensions are
tried and the best is frozen. For each new sign, the primary score is the largest normalized
residue-prefix barrier seen so far for `d≤128`. A randomly perturbed quadratic residue energy,
weighted by `d^(-2α)`, breaks barrier plateaus. Round candidates are compared lexicographically by
the maximum barrier and then the sum of normalized per-step barriers.

This is a partial-coloring **surrogate**, not an implementation of the Lovett--Meka edge walk,
Banaszczyk's theorem, or Beck's infinite-dimensional argument. Freezing a contiguous prefix makes
the extension obstruction visible and gives unambiguous round checkpoints, but it is more
restrictive than allowing an arbitrary half of the variables to become integral.

### 3.2 Full finite-witness audit

The cutoff `d≤128` affects only search decisions. After the final round, a separate quadratic-time
pass evaluates every `d≤N`, every `r<d`, and every allowed prefix length. It records the exact
integer per-step profile, the normalized barrier, and one worst coordinate `(d,r,M,sum)`. The same
pass reconstructs the all-step barrier after each round by treating the unfrozen suffix as zero.

In all 20 recorded instances, the full all-step barrier equals the search-cutoff barrier. Thus no
step above `128` hid a worse constraint in this run.

## 4. Reproduction

The recorded run used CPython 3.13.5 and only the standard library, from the repository root:

```bash
python3 scripts/research/erdos177_numerics.py self-test

python3 scripts/research/erdos177_numerics.py balance-suite \
  --Ns 256,1024,4096,8192 \
  --alphas 0.5,1,2,4,7 \
  --search-D 128 \
  --trials-per-round 4 \
  --freeze-fraction 0.5 \
  --seed 177 \
  --format markdown
```

On the development worker, the suite took `1:25.73` wall-clock time and peaked at `20,936 KiB`
resident memory. `N=8192` was therefore chosen as the largest horizon in the under-two-minute
reproducibility budget. The exact all-step audit is `Θ(N²)`; search itself is approximately
`Θ(N·min(N,search_D)·trials)`.

Use the single-instance `balance` command to obtain JSON containing every round. Add
`--emit-signs` to include the full witness; by default the output includes only a SHA-256 prefix
so large logs stay compact.

## 5. Final barriers

The table reports achieved upper bounds. “Search barrier” uses `d≤128`; “full barrier” is the
independent audit through `d=N`.

| `N` | `α` | full barrier | search barrier | worst `(d,r,M,sum)` | witness hash |
|---:|---:|---:|---:|:---|:---|
| 256 | 1/2 | 2.333333 | 2.333333 | `(9,5,27,7)` | `5cbf255aba8d6e9c` |
| 1024 | 1/2 | 2.710687 | 2.710687 | `(23,9,43,13)` | `52fb13ed35c50919` |
| 4096 | 1/2 | 3.232895 | 3.232895 | `(31,14,118,18)` | `820b5232fca1a9eb` |
| 8192 | 1/2 | 3.420744 | 3.420744 | `(67,7,114,-28)` | `7aeb0e7aba4302cb` |
| 256 | 1 | 1.600000 | 1.600000 | `(5,0,32,-8)` | `99d34f4955102e86` |
| 1024 | 1 | 1.666667 | 1.666667 | `(3,1,81,5)` | `ff314f4d4315d99a` |
| 4096 | 1 | 2.000000 | 2.000000 | `(3,0,250,-6)` | `2c0f1ce23c1b2a3f` |
| 8192 | 1 | 2.000000 | 2.000000 | `(1,0,2240,2)` | `e30cdb3432fbc11b` |
| 256 | 2 | 1.000000 | 1.000000 | `(1,0,1,-1)` | `83a5ebb7171ae6f8` |
| 1024 | 2 | 1.000000 | 1.000000 | `(1,0,1,-1)` | `c61a697e0a77c00a` |
| 4096 | 2 | 1.120000 | 1.120000 | `(5,2,722,28)` | `24c3f25f0bafe491` |
| 8192 | 2 | 1.160000 | 1.160000 | `(5,1,923,29)` | `3e58d52b733c207f` |
| 256 | 4 | 1.000000 | 1.000000 | `(1,0,1,-1)` | `4069e3483d2b1840` |
| 1024 | 4 | 1.000000 | 1.000000 | `(1,0,1,-1)` | `8102090e47127bdf` |
| 4096 | 4 | 1.000000 | 1.000000 | `(1,0,1,-1)` | `86e18c8395f21a05` |
| 8192 | 4 | 1.000000 | 1.000000 | `(1,0,1,-1)` | `df9c21746f9fe536` |
| 256 | 7 | 1.000000 | 1.000000 | `(1,0,1,-1)` | `4069e3483d2b1840` |
| 1024 | 7 | 1.000000 | 1.000000 | `(1,0,1,-1)` | `888d379923b8946b` |
| 4096 | 7 | 1.000000 | 1.000000 | `(1,0,1,-1)` | `39d467014d07db24` |
| 8192 | 7 | 1.000000 | 1.000000 | `(1,0,1,-1)` | `b3436a56cfdf4e04` |

## 6. Barrier by partial-coloring round at `N=8192`

The omitted rounds between `98.438%` and `100%` have the same barrier as the final row. Barriers
are monotone by definition because a prefix witnessed in an earlier round remains present later.

| colored | `α=1/2` | `α=1` | `α=2` | `α=4` | `α=7` |
|---:|---:|---:|---:|---:|---:|
| 50% | 3.316625 | 2.000000 | 1.160000 | 1.000000 | 1.000000 |
| 75% | 3.316625 | 2.000000 | 1.160000 | 1.000000 | 1.000000 |
| 87.5% | 3.420744 | 2.000000 | 1.160000 | 1.000000 | 1.000000 |
| 93.75% | 3.420744 | 2.000000 | 1.160000 | 1.000000 | 1.000000 |
| 96.875% | 3.420744 | 2.000000 | 1.160000 | 1.000000 | 1.000000 |
| 98.438% | 3.420744 | 2.000000 | 1.160000 | 1.000000 | 1.000000 |
| 100% | 3.420744 | 2.000000 | 1.160000 | 1.000000 | 1.000000 |

At this horizon, only the square-root run acquires a new worst barrier after its first round, and
that increase occurs before `87.5%` of the signs are frozen. The other four runs reach their final
barrier in the first half. This says the tested heuristic did not accumulate a fresh fixed-size
error on every late round; it does not establish the barrier-preservation lemma required by C6.

## 7. Empirical verdict for C3-BAL

- `α=1/2`: no bounded-barrier behavior is visible. The barrier increases at all four horizons,
  by about `47%` from `N=256` to `N=8192`.
- `α=1`: the barrier rises from `1.6` to `2` and then plateaus across the two largest horizons.
  This is compatible with boundedness but too short a plateau to be persuasive.
- `α=2`: barrier `1` is lost between `N=1024` and `4096`, followed by a smaller increase to
  `1.16`. The tested range is again inconclusive.
- `α=4` and `α=7`: the barrier remains at its universal finite lower bound `1` through `8192`.
  These are the strongest positive finite observations, but there is no inferred theorem for
  untested horizons.

The useful C6 signal is narrower than “high exponents look easy.” In every recorded instance the
worst constraint has `d≤67`, and auditing the unoptimized tail `129≤d≤N` changes no result. A
barrier argument should therefore pay special attention to repeated pressure from small steps,
not only to the number of large-step coordinates. The square-root run also shows that merely
avoiding a per-round additive loss does not prevent the barrier from increasing when the horizon
itself grows.

## 8. Limitations

- The witness at each `(N,α)` is optimized independently. Compactness needs uniform feasibility,
  not a visually stable finite table.
- Only seed `177` is reported. Four alternatives are tried within every round, but this is not a
  distributional study over optimizer seeds.
- The partial coloring is prefix-frozen. A genuine vector-balancing algorithm may freeze a
  noncontiguous subset and may maintain fractional values before rounding.
- Floating-point normalization is adequate for comparing these integer finite profiles, but the
  output is not a formal certificate consumed by Lean.
- The `d≤128` search cutoff succeeded in the recorded range only because the independent all-step
  audit confirmed it afterward; it is not assumed safe in advance.

No Lean assumption class is instantiated by this experiment, and no improvement to Beck's
exponent is claimed.
