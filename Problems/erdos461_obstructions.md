# Erdős 461: exact matching obstructions

## Executive verdict

The two multiple-matching leads in the problem card are false, for explicit
and repeatable reasons.  At `t = 8, n = 1255`, the upper-half primes 5 and 7
have the same sole interval multiple, 1260.  More generally, placing an
interval around a center divisible by every upper-half divisor makes the
maximum upper-half multiple matching have size 1 for odd `t` and 2 for even
`t`, while the left set has size `floor(t / 2)`.

These are obstructions to matching divisors to **distinct interval
integers**.  They are not counterexamples to Erdős 461, whose right vertices
are smooth-component values, and they do not refute the positive-proportion
lower-half component-matching interface in
[`Reduction.lean`](../Conjectures/C0004_erdos461_smooth/src/Reduction.lean).
At the explicit obstruction that interface has zero Hall defect.  The same is
true computationally at the divisible centers through `t = 40`.

## Known and machine-checked facts

### Source and claim status

Erdős and Graham ask whether the number of distinct `t`-smooth components in
every interval `(n,n+t]` is bounded below by a positive constant times `t`;
they record the weaker `t / log t` order lower bound on p. 92
[ErGr80, p. 92][ErGr80].  The maintained problem page continues to list the
positive-proportion question as open [EP461].  Nothing in this memo proves or
disproves that question.

The earlier numerical memo found the `t = 8` example and the centered pattern
[B2].  The approach memo records why matching to multiples is not the same as
matching to distinct smooth-component values [B3].

### The exact `t = 8, n = 1255` obstruction

The interval is

\[
(1255,1263]=\{1256,1257,1258,1259,1260,1261,1262,1263\}.
\]

Its smooth components, in offset order, are

\[
8,3,2,1,1260,1,2,3.
\]

Thus the component image is `\{1,2,3,8,1260\}` and `f(1255,8)=5`.  Both 5
and 7 have exactly the neighbor `1260` in the multiple graph.  The following
statements are proved in
[`Obstructions.lean`](../Conjectures/C0004_erdos461_smooth/src/Obstructions.lean),
using decidable finite computations for the interval sets and explicit
`norm_num` proofs for the noncomputable `smoothPart` values:

```lean
theorem multipleNeighbors_1255_eight_five :
    multipleNeighbors 1255 8 5 = {1260}

theorem multipleNeighbors_1255_eight_seven :
    multipleNeighbors 1255 8 7 = {1260}

theorem prime_pair_choices_coincide ... : m₅ = m₇

theorem smoothComponentCount_1255_eight :
    smoothComponentCount 1255 8 = 5
```

For a left set `U`, write

\[
\delta(U)=\max(0,|U|-|N(U)|).
\]

The exact profiles computed by the script begin as follows.  “Upper-half
multiples” uses left set `\{4,5,6,7\}` and interval integers as right
vertices.  “Lower-half components” uses left set `\{1,2,3,4\}` and distinct
smooth-component values as right vertices.

| graph at `t=8,n=1255` | `|L|` | `|N(L)|` | maximum matching | maximum defect |
|:--|--:|--:|--:|--:|
| primes 5 and 7 to multiples | 2 | 1 | 1 | 1 |
| upper-half divisors to multiples | 4 | 2 | 2 | 2 |
| lower-half divisors to components | 4 | 5 | 4 | 0 |

For the prime pair the full subset distribution is

| `|U|` | number of subsets | `|N(U)| : count` | `δ(U) : count` |
|---:|---:|:--|:--|
| 0 | 1 | `0:1` | `0:1` |
| 1 | 2 | `1:2` | `0:2` |
| 2 | 1 | `1:1` | `1:1` |

For all four upper-half divisors it is

| `|U|` | number of subsets | `|N(U)| : count` | `δ(U) : count` |
|---:|---:|:--|:--|
| 0 | 1 | `0:1` | `0:1` |
| 1 | 4 | `1:3, 2:1` | `0:4` |
| 2 | 6 | `1:3, 2:3` | `0:3, 1:3` |
| 3 | 4 | `1:1, 2:3` | `1:3, 2:1` |
| 4 | 1 | `2:1` | `2:1` |

In contrast, all 16 subsets of the lower-half component graph have defect
zero.  One perfect matching is `1 ↦ 1`, `2 ↦ 2`, `3 ↦ 3`, `4 ↦ 8`.

### The highly-divisible-center family

Let `C` be divisible by every integer in the relevant upper half and put

\[
n=C-(\lfloor t/2\rfloor+1).
\]

The interval is centered asymmetrically only when `t` is even.

For `t=2k+1`, the interval is `[C-k,C+k]` and the left set is
`L^+_t=[k+1,2k]`.  Every `d∈L^+_t` has exactly one represented multiple,
namely `C`.  Hence, for every nonempty `U⊆L^+_t`,

\[
|N(U)|=1,\qquad \delta(U)=|U|-1.
\]

There are `binom(k,r)` subsets of size `r`, the maximum defect is `k-1`,
and the maximum matching has size 1.

For `t=2k`, the interval is `[C-k,C+k-1]` and
`L^+_t=[k,2k-1]`.  The boundary divisor `k` has neighbors `C-k` and `C`;
every `d>k` has only `C`.  Consequently, among subsets of size `r`,

- `binom(k-1,r)` omit `k`, have neighborhood size 1 when nonempty, and
  defect `r-1`;
- `binom(k-1,r-1)` contain `k`, have neighborhood size 2, and defect
  `max(0,r-2)`.

The maximum defect is `k-2`, and the maximum matching has size 2.  These
neighbor equalities and exact full-set defects are proved for every admissible
`k` and `C` in `Obstructions.lean`.  The file then instantiates them with
`C=(2k+1)!` and `C=(2k)!`, giving explicit infinite parametric families:

```lean
theorem multipleDefect_factorial_center_odd (k : ℕ) (hk : 1 ≤ k) :
    ... = k - 1

theorem multipleDefect_factorial_center_even (k : ℕ) (hk : 2 ≤ k) :
    ... = k - 2
```

The script uses the smaller center `lcm(1,...,t)` and independently recovers
the same formulas.  Its self-check verifies the subset counts, the finite Hall
identity `maximum defect = |L| - maximum matching`, and the neighbor formulas
for every requested `t`.

## Conjectured or still open

- Erdős 461 remains open [EP461].
- `ProportionalComponentMatchingAssumption` remains an assumption.  B3 proves
  that it would imply Erdős 461, not that it holds [B3].
- Zero defect for the lower-half component graph at `t=8,n=1255` and at the
  `lcm(1,...,t)` centers for `3≤t≤40` is only a finite computation.  It does
  not assert a uniform perfect-matching theorem.  The public discussion has a
  separate obstruction to an overly strong perfect component matching
  [EP461-thread].

## Our computational method and new interpretation

`hall_defect_profile` represents each right neighborhood by a bit mask and
uses dynamic programming on `(left-subset size, neighborhood mask)`.  It
therefore counts every pair `( |U|, |N(U)| )` exactly without relying on
random sampling or materializing all subsets.  For each report it also runs
the augmenting-path maximum-matching algorithm already used in B2.

Reproduce every profile through `t=40` and check its invariants with:

```bash
python3 scripts/research/erdos461_numerics.py \
  --max-t 40 --obstruction-profiles --self-check
```

For machine-readable records, add `--json`.  The original minimum search is
unchanged when `--obstruction-profiles` is absent.

Our interpretation is that the choice of both sides matters:

1. **Upper-half divisors → interval multiples is not viable.**  Its matching
   size is bounded by 1 or 2 throughout the formal family while its left set
   grows linearly.
2. **Upper-half primes → interval multiples is not viable as the proposed
   injection.**  The two-element failure is already exact at `t=8`; at a
   divisible center all strict upper-half divisors other than the even
   boundary share the sole neighbor `C`.
3. **Lower-half divisors → smooth components remains viable as a
   positive-proportion target.**  The B6 obstructions do not damage it: its
   exact maximum defect is zero at the explicit example and at every tested
   divisible center through `t=40`.  This is evidence about an interface, not
   a proof of it.
4. **B7 should be multiscale and component-valued.**  A useful refinement must
   control component neighborhoods after separating concentration at one
   highly divisible interval integer.  Returning to distinct multiples or to
   a single upper-half scale repeats the obstruction proved here.

## What surprised us

The obstruction is stronger than a bad greedy choice: it is the complete
Hall profile, with defect growing like half the left-set size.  Yet quotienting
to smooth components and switching to the B3 lower-half left set reverses the
diagnostic at the same interval: every subset satisfies Hall.  The negative
result therefore narrows the graph that B7 should study without supplying
negative evidence against the open conjecture itself.

[B2]: erdos461_numerics.md
[B3]: erdos461_approach.md
[EP461]: https://www.erdosproblems.com/461
[EP461-thread]: https://www.erdosproblems.com/forum/thread/461
[ErGr80]: https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf
