# EDP-rate numerics

This memo reports exact finite computations of

\[
D_f(x)=\max_{dm\le x}\left|\sum_{k=1}^{m}f(kd)\right|.
\]

It separates source-backed facts, the open conjecture, and observations made by the committed
script.  None of the finite computations below proves an asymptotic lower bound.

## Reproduction and scope

Run from the repository root (Python 3 and NumPy are required):

```bash
python3 scripts/research/edp_rate_numerics.py --max-x 10000000
```

The run used NumPy 2.1.3 and completed in about five seconds on the card worktree.  It downloads
two version-pinned primary-source bundles, refuses changed content by SHA-256, checks that the
127,645-term witness is completely multiplicative, and compares its exact-discrepancy algorithm
with brute force through `x = 200`.  For offline reruns, pass the downloaded bundles using
`--konev-source` and `--le-bras-source`.  CSV output is available with `--format csv`.

The exact algorithm enumerates every pair `dm ≤ x`; it is not a sampler.  It splits the lattice
under the hyperbola at `d = floor(sqrt(x))`, scanning the small-`d` half by `d` and the large-`d`
half by `m`.  The reported `(d,m)` is one attaining pair; ties are not exhaustively listed.

Source payloads used by the script:

- Konev--Lisitsa, arXiv:1405.3097v2 source,
  `f0a74969c7228733e208afcd3818bbaa60151de0d81431c19b41f01bf721943d`.
- Le Bras--Gomes--Selman, arXiv:1407.2510v1 source,
  `07fbdd98908a9bc61c9cd7ece416689b9dc375032c9323c14a17602e422347f7`.

## Known results and input sequences

Borwein, Choi, and Coons define, for an odd prime `p`, the completely multiplicative modified
quadratic character

\[
\lambda_{p,+}(p^v m)=\left(\frac{m}{p}\right)\qquad(p\nmid m).
\]

Their base-digit theorem expresses its partial sum in terms of the base-`p` digits of `n`, and
the maximum theorem in their section “A bound for `|L_p(n)|`” gives

\[
\max_{n<p^i}|L_p(n)|=i\max_{n<p}|L_p(n)|.
\]

Thus these are genuine `O(log x)` examples, not numerical guesses.  In particular they prove
`|L_3(n)| ≤ floor(log_3 n)+1` and `|L_5(n)| ≤ floor(log_5 n)+1`.
See [Borwein--Choi--Coons, *Completely multiplicative functions taking values in
{−1,1}*](https://arxiv.org/abs/0809.1691).

The script also varies the filled-in value at `p`:

\[
\lambda_{p,\epsilon}(p^v m)=\epsilon^v\left(\frac{m}{p}\right),
\qquad \epsilon\in\{-1,+1\}.
\]

For `p=3, ε=-1` this is the improved Walters sequence
`μ₃(3n)=-μ₃(n)`, `μ₃(3n+1)=+1`, `μ₃(3n+2)=-1`, as defined in §3 of
[Le Bras--Gomes--Selman](https://arxiv.org/abs/1407.2510).  Complete multiplicativity reduces
the full homogeneous-AP maximum to the ordinary prefix maximum, so `d=1` always supplies an
attaining pair; this is also the content of
`CompletelyMultiplicative.discrepancy_eq_discrepancy_one` in this repository.

The finite input data are primary-source witnesses rather than regenerated SAT solutions:

- Appendix B of [Konev--Lisitsa, *Computer-Aided Proof of Erdős Discrepancy
  Properties*](https://arxiv.org/abs/1405.3097) contains all 1,160 signs of a discrepancy-2
  sequence.  The same paper reports a 130,000-term unrestricted discrepancy-3 sequence,
  but its version-pinned source does not include those signs; the script therefore does not
  attach numerical measurements to unavailable witness data.
- The source bundle of [Le Bras--Gomes--Selman](https://arxiv.org/abs/1407.2510) contains
  `sequence127645.tex`, all 127,645 signs of their discrepancy-3 completely multiplicative
  sequence.  The script independently confirms finite complete multiplicativity and `D=3`.
- §4 of the latter paper gives the lift that replaces every ninth position by the source
  sequence and fills the other residues with
  `(+,-,-,+,-,+,+,-)`.  A full lift multiplies length by 9 and raises the proved discrepancy
  ceiling by at most 1.  The script recomputes the exact discrepancy instead of relying on that
  ceiling.

## Numerical results: modified characters

At the largest requested scale, the exact results are:

| `p` | `f(p)` | `D(10^7)` | attaining `(d,m)` | `D(10^7)/ln(10^7)` |
|---:|---:|---:|---:|---:|
| 3 | +1 | 15 | (1, 7,174,453) | 0.930631 |
| 3 | −1 | 8 | (1, 5,380,840) | 0.496337 |
| 5 | +1 | 10 | (1, 2,441,406) | 0.620421 |
| 5 | −1 | 10 | (1, 3,255,208) | 0.620421 |
| 7 | +1 | 17 | (1, 7,686,401) | 1.054715 |
| 7 | −1 | 9 | (1, 6,005,001) | 0.558379 |
| 11 | +1 | 21 | (1, 9,743,585) | 1.302883 |
| 11 | −1 | 12 | (1, 8,931,620) | 0.744505 |

The period-3 comparison shows how strongly the choice at the missing character value matters:

| `x` | `D(x)`, `f(3)=+1` | ratio | `D(x)`, `f(3)=−1` | ratio |
|---:|---:|---:|---:|---:|
| 10 | 2 | 0.868589 | 2 | 0.868589 |
| 100 | 4 | 0.868589 | 3 | 0.651442 |
| 1,000 | 6 | 0.868589 | 4 | 0.579059 |
| 10,000 | 9 | 0.977163 | 5 | 0.542868 |
| 100,000 | 11 | 0.955448 | 6 | 0.521153 |
| 1,000,000 | 13 | 0.940971 | 7 | 0.506677 |
| 10,000,000 | 15 | 0.930631 | 8 | 0.496337 |

For the `f(p)=+1` Borwein--Choi--Coons sequences, their exact theorem gives the natural
logarithmic coefficients `M_p/ln p`, where `M_p=max_{n<p}|L_p(n)|`.  For the four tested primes
these are respectively `1/ln 3 = 0.910239`, `1/ln 5 = 0.621335`,
`2/ln 7 = 1.027797`, and `3/ln 11 = 1.251097`.  The finite ratios oscillate around or above
these scale coefficients because `D(x)` changes discretely.

## Numerical results: published witnesses and lifts

Each row is exhaustively checked over every `dm ≤ x`.

| source/construction | `x` | `D(x)` | attaining `(d,m)` | `D(x)/ln x` |
|---|---:|---:|---:|---:|
| Konev--Lisitsa witness | 1,160 | 2 | (1, 12) | 0.283440 |
| one period-9 lift | 10,440 | 3 | (1, 109) | 0.324205 |
| two lifts | 93,960 | 4 | (1, 982) | 0.349326 |
| three lifts | 845,640 | 5 | (1, 8,839) | 0.366358 |
| four lifts | 7,610,760 | 6 | (1, 79,552) | 0.378667 |
| prefix of five lifts | 10,000,000 | 7 | (1, 715,969) | 0.434294 |
| Le Bras--Gomes--Selman witness | 127,645 | 3 | (1, 91) | 0.255167 |
| one period-9 lift | 1,148,805 | 4 | (1, 820) | 0.286651 |
| prefix of two lifts | 10,000,000 | 5 | (1, 7,381) | 0.310210 |

The last value is the smallest ratio in the `10^6`--`10^7` range among the tested finite
constructions.  It is a finite-prefix fact, not an upper bound on a universal asymptotic
constant: successive period-9 lifts are not nested extensions of one fixed infinite sequence.

## The conjecture

Erdős conjectured that there is a universal `c>0` such that every infinite sign sequence has
`D_f(x) ≥ c ln x` at all sufficiently large scales; see
[Erdős Problems 67](https://www.erdosproblems.com/67).  The computations here test candidate
upper examples.  They do not address the universal lower bound.

## Our observations and ideas (unproved)

1. Among the eight small modified characters tested, the improved Walters choice
   `(p, f(p))=(3,-1)` is decisively best at `10^7`: `D=8`, versus `9` for the next-best
   `(7,-1)` choice.
2. Its first witnesses for discrepancies `2,3,…,8` occur at
   `10, 91, 820, 7,381, 66,430, 597,871, 5,380,840`.  These equal
   `(9^r-1)/8`.  The observed recurrence suggests the asymptotic coefficient
   `1/ln 9 = 0.455120`.  Establishing the recurrence for all `r` would be a separate proof;
   this memo claims only the checked finite range.
3. If that recurrence is proved, this single infinite sequence would force any universal
   logarithmic constant in the conjecture to satisfy `c ≤ 1/ln 9`.  The unusually smaller
   finite ratio `0.310210` from the lifted 127,645-term witness does **not** imply a stronger
   restriction, because it is not presently an infinite construction with that coefficient.
4. Every maximum reported in these families happened at `d=1`.  For modified characters this
   is forced by complete multiplicativity.  For the nonmultiplicative lifts it is an empirical
   output of the exhaustive checker and may help narrow future searches, but is not a theorem
   about the construction.

## What the numerics do not show

- No fitted exponent is reported: the discrepancy values are tiny integers over only seven
  decades, making log/log or power fits misleading.
- The SAT witnesses are not continued by arbitrary signs.  Only the cited period-9 construction
  is used beyond their published lengths.
- A finite low ratio does not prove a restriction on Erdős's asymptotic constant, and none of
  these computations improves McNamara's lower bound.
