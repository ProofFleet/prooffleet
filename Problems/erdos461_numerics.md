# Erdős 461: numerical search for small smooth-component counts

## Scope and status

For $t \ge 2$, let $s_t(m)$ be the product, with multiplicity, of the
prime factors $p<t$ of $m$, and let

\[
f(n,t)=\left|\{s_t(n+1),\ldots,s_t(n+t)\}\right|.
\]

This is the convention in [Erdős--Graham, p. 92][ErGr80] and on the
[Erdős Problems page][EP461].  The problem asks whether $f(n,t) \gg t$
uniformly; the page records only the known $t/\log t$ lower bound.  Nothing
below proves the open conjecture.  Rows marked **exact** are global finite
computations justified by the collision period below.  Rows marked
**sampled** are upper bounds on the unknown minimum (the best value found),
not certifications of minimality.

## Known facts used

- If $s_t(x)=s_t(y)=S$, then $S\mid |x-y|$.  In particular a shared
  component $S\ge t/2$ occurs at most twice in an interval of length $t$,
  and a shared component $S\ge t$ cannot occur twice.
- Erdős and Graham state the problem in the original monograph, and the
  maintained problem page records it as open and gives the
  $f(n,t)\gg t/\log t$ result [ErGr80, p. 92][ErGr80] [EP461].
- A finite search cannot settle the uniform asymptotic question.  The
  website's discussion also already contains a different counterexample to
  an overly optimistic matching proposal [EP461-thread].

## Conjectured statements (not established here)

- The target $f(n,t)\gg t$ remains open.
- The observed value
  $⌊t/2⌋+1$ is the exact minimum for every $3\le t\le11$, and the
  search finds the same value through $t=40$.  We do **not** extrapolate
  this as a conjectural formula: the public discussion gives an averaging
  argument against an asymptotic $t/2$ lower bound [EP461-thread], and the
  sampled rows are not exhaustive.

## Our computational method

### An exact period for collisions

For every prime $p<t$, put

\[
a_p=\min\{a\ge1:p^a\ge t\},\qquad
P_t=\prod_{p<t}p^{a_p}.
\]

The equality pattern among the $t$ smooth components is periodic in $n$
with period $P_t$.  Here is the elementary justification used by the
program.  If two different interval elements have the same smooth part and
their common $p$-adic valuation is at least $a_p$, then $p^{a_p}$
divides their positive difference, although that difference is less than
$t\le p^{a_p}$, a contradiction.  Every actual collision therefore has
all common valuations below $a_p$.  Those truncated valuations are
determined by $n+i\pmod {p^{a_p}}$, and the Chinese remainder theorem gives
period $P_t$.  Enumerating every $0\le n<P_t$ is consequently a global
search, not an assumption that smooth-part values themselves are periodic.

The default cutoff $P_t\le10^6$ makes the rows through $t=11$ exact.  For
larger periods the program combines:

- residues near $0,-1,-⌊t/2⌋$ modulo $P_t$,
  $\operatorname{lcm}(1,\ldots,t)$, primorials, prime-prefix products, and
  primorials with one factor removed; and
- 20,000 uniform pseudorandom residues modulo $P_t$, using seed 461.

It also computes maximum bipartite matchings from every
$s\in[\lceil t/2\rceil,t)$ to its multiples in the interval, and separately
does the same for primes in $(t/2,t)$.  No third-party packages are used.

Reproduce the table and run the built-in periodicity/invariant checks with:

```bash
python3 scripts/research/erdos461_numerics.py \
  --max-t 40 --exact-period-limit 1000000 \
  --random-samples 20000 --seed 461 --self-check
```

The `--json` option emits the same records as machine-readable JSON.

## Results

In the collision column, write $t=2k$ or $2k+1$ and $c=k+1$.
`c±[1,r]` means that smooth part $s$ is shared by exactly the two
offsets $c-s,c+s$, for every $1\le s\le r$; these are all the collisions
at the reported $n$.  This compactly gives every colliding residue rather
than suppressing a long list.

| $t$ | collision period $P_t$ | search (residues tested) | $f$ | $f/t$ | least reported $n$ | collisions |
|---:|---:|:---|---:|---:|---:|:---|
| 2 | 1 | exact (1) | 1 | 0.5000 | 0 | exceptional: part 1 at offsets 1,2 |
| 3 | 4 | exact (4) | 2 | 0.6667 | 0 | c±[1,1] |
| 4 | 36 | exact (36) | 3 | 0.7500 | 3 | c±[1,1] |
| 5 | 72 | exact (72) | 3 | 0.6000 | 9 | c±[1,2] |
| 6 | 1800 | exact (1800) | 4 | 0.6667 | 56 | c±[1,2] |
| 7 | 1800 | exact (1800) | 4 | 0.5714 | 176 | c±[1,3] |
| 8 | 88200 | exact (88200) | 5 | 0.6250 | 1255 | c±[1,3] |
| 9 | 176400 | exact (176400) | 5 | 0.5556 | 2515 | c±[1,4] |
| 10 | 529200 | exact (529200) | 6 | 0.6000 | 2514 | c±[1,4] |
| 11 | 529200 | exact (529200) | 6 | 0.5455 | 5034 | c±[1,5] |
| 12 | 64033200 | sampled (20695) | 7 | 0.5833 | 55433 | c±[1,5] |
| 13 | 64033200 | sampled (20740) | 7 | 0.5385 | 360353 | c±[1,6] |
| 14 | 10821610800 | sampled (21017) | 8 | 0.5714 | 360352 | c±[1,6] |
| 15 | 10821610800 | sampled (21069) | 8 | 0.5333 | 360352 | c±[1,7] |
| 16 | 10821610800 | sampled (21147) | 9 | 0.5625 | 2162151 | c±[1,7] |
| 17 | 21643221600 | sampled (21199) | 9 | 0.5294 | 12252231 | c±[1,8] |
| 18 | 6254891042400 | sampled (21551) | 10 | 0.5556 | 12252230 | c±[1,8] |
| 19 | 6254891042400 | sampled (21615) | 10 | 0.5263 | 6254891042390 | c±[1,9] |
| 20 | 2258015666306400 | sampled (22015) | 11 | 0.5500 | 2258015666306389 | c±[1,9] |
| 21 | 2258015666306400 | sampled (22091) | 11 | 0.5238 | 2258015666306389 | c±[1,10] |
| 22 | 2258015666306400 | sampled (22205) | 12 | 0.5455 | 2258015666306388 | c±[1,10] |
| 23 | 2258015666306400 | sampled (22281) | 12 | 0.5217 | 2258015666306388 | c±[1,11] |
| 24 | 1194490287476085600 | sampled (22759) | 13 | 0.5417 | 1194490287476085587 | c±[1,11] |
| 25 | 1194490287476085600 | sampled (22847) | 13 | 0.5200 | 1194490287476085587 | c±[1,12] |
| 26 | 5972451437380428000 | sampled (22979) | 14 | 0.5385 | 5972451437380427986 | c±[1,12] |
| 27 | 5972451437380428000 | sampled (23067) | 14 | 0.5185 | 160626866386 | c±[1,13] |
| 28 | 17917354312141284000 | sampled (23199) | 15 | 0.5357 | 160626866385 | c±[1,13] |
| 29 | 17917354312141284000 | sampled (23287) | 15 | 0.5172 | 6987268688385 | c±[1,14] |
| 30 | 15068494976510819844000 | sampled (23873) | 16 | 0.5333 | 6987268688384 | c±[1,14] |
| 31 | 15068494976510819844000 | sampled (23973) | 16 | 0.5161 | 72201776446784 | c±[1,15] |
| 32 | 14480823672426897870084000 | sampled (24607) | 17 | 0.5312 | 433210658680783 | c±[1,15] |
| 33 | 28961647344853795740168000 | sampled (24719) | 17 | 0.5152 | 433210658680783 | c±[1,16] |
| 34 | 28961647344853795740168000 | sampled (24887) | 18 | 0.5294 | 433210658680782 | c±[1,16] |
| 35 | 28961647344853795740168000 | sampled (24999) | 18 | 0.5143 | 433210658680782 | c±[1,17] |
| 36 | 28961647344853795740168000 | sampled (25167) | 19 | 0.5278 | 433210658680781 | c±[1,17] |
| 37 | 28961647344853795740168000 | sampled (25279) | 19 | 0.5135 | 10685862914126381 | c±[1,18] |
| 38 | 39648495215104846368289992000 | sampled (26021) | 20 | 0.5263 | 10685862914126380 | c±[1,18] |
| 39 | 39648495215104846368289992000 | sampled (26145) | 20 | 0.5128 | 39648495215104846368289991980 | c±[1,19] |
| 40 | 39648495215104846368289992000 | sampled (26331) | 21 | 0.5250 | 39648495215104846368289991979 | c±[1,19] |

### Diagnostics for the two proposed leads

1. **Primes in $(t/2,t)$: false as a uniform injection.**  For the least
   multiple of each such prime, every reported minimizing interval with
   $t\ge3$ produced only one distinct selected smooth part.  More strongly,
   the maximum matching from those primes to distinct multiples had size one
   in every reported interval, although there are as many as five relevant
   primes.  The smallest exact counterexample is $t=8,n=1255$: both 5 and 7
   have only the multiple 1260 in $(1255,1263]$, whose smooth part is 1260.
   Thus the proposed prime count does not follow without an additional
   matching argument, and that matching is itself false.

2. **Divisors in $[t/2,t)$: the Hall route collapses at highly divisible
   centers.**  At every reported odd $t\ge3$, the maximum number of distinct
   multiples assigned to these divisors was 1 out of $⌊t/2⌋$; at every
   reported even $t\ge4$, it was 2 out of $t/2$ (for $t=2$, 1 out of 1).
   In the near-period construction, all the divisors share the central
   multiple and only the even-length endpoint permits one extra assignment.
   This is a direct family of Hall obstructions, consistent with the distinct
   $t=38$ obstruction reported on the discussion page [EP461-thread].

3. **Fiber sizes:** all collision fibers in the table have size exactly two:
   there are $⌊t/2⌋$ such fibers for odd $t$, and $t/2-1$ for even
   $t\ge4$.  For $t\ge3$, none has component at least $t/2$; every
   high-component fiber is a singleton.  (At the exceptional $t=2$, the
   component 1 occurs twice.)  So the proposed "at most two" observation
   passes all tests, but contributes no lower bound in these worst intervals
   because the collisions sit just below its threshold.

## What surprised us

The minima found by a broad residue search were not random-looking.  They
were centered at an integer with enough small-prime divisibility to make the
smooth parts at symmetric offsets equal to the offsets themselves.  This
simultaneously creates almost $t/2$ pair collisions and destroys both
suggested matching arguments.  The computation therefore supplies useful
negative evidence about those proof routes, while providing no evidence
against the original positive-proportion conjecture.

[EP461]: https://www.erdosproblems.com/461
[EP461-thread]: https://www.erdosproblems.com/forum/thread/461
[ErGr80]: https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf
