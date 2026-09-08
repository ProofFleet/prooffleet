# Erdős #177: finite numerical experiments

This memo accompanies `scripts/research/erdos177_numerics.py`. It reports exact finite
progression profiles, small exhaustive optima, and reproducible heuristic upper bounds. The
experiments do **not** prove an infinite bound or improve Beck's exponent.

## 1. Known results and definitions

For a sign sequence on the positive integers, Erdős Problem 177 asks for a bound depending only
on the common difference `d`, uniformly over the start and length of every finite arithmetic
progression. The problem page records the factorial construction of Cantor--Erdős--Schreiber--
Straus, Roth's square-root lower obstruction, and Beck's `d^(8+ε)` upper bound [Erdős Problems
#177](https://www.erdosproblems.com/177).

Beck's source is J. Beck, *A Discrepancy Problem: Balancing Infinite Dimensional Vectors*, in
*Number Theory -- Diophantine Problems, Uniform Distribution and Applications* (2017), pp.
61--82, [DOI 10.1007/978-3-319-55357-3_3](https://doi.org/10.1007/978-3-319-55357-3_3).
Roth's source is K. F. Roth, *Remark concerning integer sequences*, *Acta Arithmetica* 9 (1964),
257--260, [DOI 10.4064/aa-9-3-257-260](https://doi.org/10.4064/aa-9-3-257-260).

The finite problem used here restricts every progression to `[1,N]` and every step to `1 ≤ d ≤
D`. For a coloring `x`, define

```text
h_N,x(d) = max |sum x(a + j d)|,
             a ≥ 1, L ≥ 0, a + (L-1)d ≤ N,

Q_N,D,α(x) = max_{1 ≤ d ≤ D} h_N,x(d) / d^α.
```

For fixed `d`, the points in each residue class form a linearly ordered sequence. Every permitted
progression is a contiguous interval in one such sequence. If `P_0,...,P_m` are its prefix sums,
the maximum absolute interval sum is exactly `max P_i - min P_i`. Thus the script computes the
entire `h(d)` profile exactly in `O(ND)` time. Only the subsequent minimization over colorings is
heuristic unless the `exact` command is used.

## 2. Conjectured or unresolved

- It remains open whether an infinite coloring can attain an exponent below `8`; these finite
  experiments make no conjectural bound available to Lean.
- The data below do not determine whether `Q_N,D,1/2` stays bounded as `N` and then `D` grow. A
  slow increase can reflect a real obstruction, a poor optimizer, or the incompatibility between
  independently optimized finite colorings.
- No extrapolation from the fitted values is asserted. In particular, the hashes in the tables
  identify finite witnesses, not prefixes of one common infinite witness.

## 3. Our computational idea

### 3.1 Exact evaluator and exhaustive mode

The prefix-range identity above avoids enumerating `O(N²D)` start/length pairs. The `exact`
command enumerates all colorings after fixing the first sign to `+1`; global sign reversal leaves
the objective unchanged. It therefore checks `2^(N-1)` assignments and certifies the reported
small-instance optimum.

The built-in self-test compares the prefix-range evaluator with the definition-level triple loop
on random instances. It also checks 100 accepted incremental flips against a fresh full profile.

### 3.2 Structured candidates

The comparison set is deliberately heterogeneous:

- alternating signs;
- Thue--Morse signs `(-1)^popcount(n-1)`;
- Rudin--Shapiro signs given by the parity of adjacent `11` bit pairs in `n-1`;
- alternating constant blocks of lengths `2,4,8,16`;
- an iid seeded random coloring;
- a randomized energy-balancing construction.

The last construction colors positions from left to right. At each position it chooses the sign
that reduces a randomly perturbed, `d^(-2α)`-weighted quadratic energy of the active residue-class
prefix sums. It is only a **Beck-inspired surrogate**. It does not implement, and supplies no
evidence for, the infinite-dimensional partial-coloring theorem in Beck's paper.

### 3.3 Local search

A single sign flip shifts a suffix of exactly one residue-class prefix array for each `d`. The
script tentatively recomputes only those `D` ranges, then performs seeded simulated annealing.
The primary comparison is the requested maximum `Q`; a sum of normalized discrepancies breaks
ties. Each result is re-evaluable from the deterministic command and is tagged with the first 16
hexadecimal digits of a SHA-256 hash of its sign vector.

## 4. Reproduction

The recorded run used CPython 3.13.5 and only the standard library, from the repository root:

```bash
python3 scripts/research/erdos177_numerics.py self-test

for n in 8 12 16 18 20; do
  python3 scripts/research/erdos177_numerics.py exact \
    --N "$n" --D 8 --alpha 0.5
done

python3 scripts/research/erdos177_numerics.py suite \
  --Ns 256,1024,4096 --D 16 --alphas 0.5 \
  --iterations 5000 --restarts 4 --seed 177 --format markdown

python3 scripts/research/erdos177_numerics.py suite \
  --Ns 1024 --D 16 --alphas 0,0.5,1,2 \
  --iterations 5000 --restarts 4 --seed 177 --format markdown

python3 scripts/research/erdos177_numerics.py search \
  --N 4096 --D 64 --alpha 0.5 \
  --iterations 2000 --restarts 2 --seed 177
```

Use `search --emit-signs` to include the complete best sign string in the JSON output. Omitting it
keeps large experiment logs compact.

## 5. Results

### 5.1 Certified small instances

Here `D=8` and `α=1/2`. “Optimum” is exhaustive, not heuristic.

| `N` | assignments after symmetry | certified optimum | one optimal `h(1),...,h(8)` | witness hash |
|---:|---:|---:|:---|:---|
| 8 | 128 | 2.000000 | `2,1,2,2,2,1,1,1` | `e0a4401fa25f91d9` |
| 12 | 2,048 | 2.000000 | `2,1,2,3,2,1,2,2` | `d27565a318119f2c` |
| 16 | 32,768 | 2.000000 | `2,1,2,4,2,1,2,2` | `3397e34b4bc33099` |
| 18 | 131,072 | 2.000000 | `2,2,3,4,2,2,3,2` | `13eb9d62ac89bea2` |
| 20 | 524,288 | 2.000000 | `2,2,3,4,3,2,3,2` | `e6f5a93564c84d7c` |

So a constant `2` multiplying `sqrt(d)` is exactly sufficient for all tested instances through
`N=20`, `D=8`. This statement is only about those finite instances.

### 5.2 Structured candidates at `N=1024`, `D=16`, `α=1/2`

| candidate | `Q` |
|:---|---:|
| randomized energy balancing | 5.366563 |
| alternating blocks, length 16 | 16.000000 |
| alternating blocks, length 8 | 16.000000 |
| iid random | 31.000000 |
| alternating blocks, length 4 | 45.254834 |
| Rudin--Shapiro | 63.000000 |
| Thue--Morse | 93.530744 |
| alternating blocks, length 2 | 128.000000 |
| alternating | 362.038672 |

The deterministic automatic sequences control some steps very well but resonate catastrophically
with others. For example, alternating signs have `h(1)=1` but `h(2)=512`; Thue--Morse has
`h(1)=2` but `h(3)=162`. The randomized balancing surrogate is the only tested structured seed
without a comparably dominant resonance.

### 5.3 Square-root objective as `N` grows

These are the best witnesses found with `D=16`, `α=1/2`, 5,000 flips per restart and four
restarts.

| `N` | best structured `Q` | post-search `Q` | witness hash |
|---:|---:|---:|:---|
| 256 | 4.618802 | 4.472136 | `149d7f4c5bc9e97e` |
| 1,024 | 5.366563 | 5.291503 | `474dd65ced0b63a4` |
| 4,096 | 7.181325 | 6.656402 | `3fe133d29f5d185d` |

The achieved small-step profiles are:

| `N` | `h(1),...,h(16)` |
|---:|:---|
| 256 | `4,4,5,6,10,6,9,8,9,8,9,5,10,10,6,8` |
| 1,024 | `5,6,9,10,11,9,14,11,14,10,17,12,16,12,13,12` |
| 4,096 | `6,7,9,9,12,11,17,13,18,13,22,16,24,17,19,18` |

The best-found coefficient increases across these three sizes. Thus the run does not exhibit a
stable `C sqrt(d)` profile at fixed `D=16`; it also does not rule one out. Expanding the largest
case to `D=64` produced `Q=6.790998` (hash `3449b0a192de880f`), only modestly above the `D=16`
value in a shorter run. In this experiment the hardest constraints were already among small
steps.

### 5.4 Sensitivity to the candidate exponent

At `N=1024`, `D=16`, with the same 5,000-by-four search budget:

| `α` | post-search `Q` | witness hash |
|---:|---:|:---|
| 0 | 12.000000 | `7040a87d9c073f79` |
| 1/2 | 5.291503 | `474dd65ced0b63a4` |
| 1 | 3.333333 | `11f5822f78f14dc9` |
| 2 | 2.000000 | `efdcc7c7dc3f405d` |

Increasing `α` relaxes the large-step constraints, after which the step-one partial-sum range
dominates. This is an optimizer diagnostic, not evidence about the infinite critical exponent.

## 6. Limitations and next experiments

- The exhaustive certificate stops at `N=20`; all larger values are achieved upper bounds with
  no matching lower-bound certificate.
- Every `N` is optimized independently. A useful next constraint is prefix compatibility: freeze
  the first `N` signs before extending to `2N`, matching the quantifiers of one infinite coloring.
- `D=64` is still tiny relative to `N=4096`. Larger-step sweeps are cheap for profile evaluation
  but make flip search progressively more expensive.
- The annealer uses single-coordinate flips and four restarts. Block moves, discrepancy-aware
  constraint sampling, SAT/ILP certificates at intermediate sizes, and many-seed distributions
  would help distinguish optimization failure from genuine growth.
- The randomized energy surrogate controls full residue-prefix sums, whereas interval
  discrepancy depends on their range. A range-aware potential is the clearest immediate
  algorithmic improvement.

In short: square-root scaling with coefficient `2` is exactly attainable in the smallest tested
window, while the best heuristic coefficient rises to about `6.66` by `N=4096`, `D=16`. The
structured tests mainly reveal resonances to avoid; they do not yet reveal an infinite
construction.
