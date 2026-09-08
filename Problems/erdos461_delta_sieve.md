# Erdős 461: Delta/sieve attack on component expansion

Accessed 2026-09-08.  This memo separates cited or machine-checked facts,
open statements, and our route analysis.  Its outcome is a rigorous
**no-route result for the proposed Delta-plus-one-fibre-sieve method**, not a
negative result about Erdős 461.  No instance of
`MultiscaleComponentExpansionAssumption` is constructed.

## Executive verdict

The published Erdős--Hooley Delta estimates do not discharge the B7
multiscale component-expansion interface.  There are two exact mismatches.

1. The strongest cited Delta upper bounds are mean-value or density-one
   statements over integers up to a height `x`.  B7 is pointwise in an
   arbitrary interval start `n`, every `t`, every left subset `U`, and the
   nonlinear set of component values represented in that interval.  Those
   component values can include deliberately chosen Delta exceptions.
2. Even a hypothetical uniform Delta bound controls the number of divisor
   edges into one component, whereas B7 needs an almost-Hall inequality.
   First-moment edge counting gives only a multiplicative expansion
   `|N(U)| >= |U| / D`; B7 needs the additive estimate

   \[
   |N(U)|\ge |U|-\bigl(|L_t|-\lceil t/4\rceil\bigr).
   \]

Removing high-degree right vertices does not repair the mismatch.  The new
Lean file proves that at `t = 38`, after retaining only components with at
most two lower-half divisor neighbours, at most nine left vertices can be
matched.  The B7 target is ten.  It also proves that `(t/2)!` is a represented
component of maximum possible right degree, so uniformity does not permit us
to declare all high-degree components absent.

The interval Brun sieve remains useful for a single smooth-component fibre,
as B5 proved, but it supplies neither the lower degrees nor the simultaneous
exceptional-incidence estimate needed below.  The exact missing input is a
uniform correlation statement between different component fibres, not a
stronger known estimate for Delta or a sharper one-fibre sieve remainder.

## 1. Known and machine-checked facts

### 1.1 The B7 target

Put

\[
 L_t=\{1,\ldots,\lfloor t/2\rfloor\},\qquad
 q_t=\lceil t/4\rceil=(t+3)/4.
\]

For `U subset L_t`, let `N(U)` be the set of represented smooth-component
values divisible by at least one `d in U`.  B4 proves the finite defect form
of Hall's theorem, and B7 asks for

\[
 |U|-|N(U)|\le |L_t|-q_t                                      \tag{1}
\]

for every `n,t,U`.  B7's dyadic sum is exact bookkeeping:
`multiscaleComponentNeighborhoodCard n t U = |N(U)|`; it does not create
extra neighbours by recounting a component at several scales [B4] [B7].

At `t=38`, `|L_t|=19`, `q_t=10`, and the permitted defect is `9`.  The public
perfect-matching counterexample at `n=1407302` has maximum defect only `1`,
so it satisfies (1) comfortably; B7 records the exact witness and computation
[B7] [EP461-thread].

### 1.2 Right degrees and divisor inheritance

For a positive component value `S`, define its full right degree

\[
 r_t(S)=\#\{d\in L_t:d\mid S\}.
\]

The new file
[`DeltaSieve.lean`](../Conjectures/C0004_erdos461_smooth/src/DeltaSieve.lean)
defines this as `componentDivisorDegree`.  It proves the elementary but
important inheritance inequality

\[
 d\in L_t,\ d\mid S \quad\Longrightarrow\quad \tau(d)\le r_t(S), \tag{2}
\]

because every positive divisor of `d` is again in `L_t` and divides `S`.

Two further facts are machine-checked.

* Every `d in L_t` divides `(t/2)!`, so
  `r_t((t/2)!)=|L_t|` (`componentDivisorDegree_factorial`).
* For `t>=2`, `(t/2)!` is `t`-smooth and occurs as a component in the
  interval beginning at `(t/2)!-1` (`factorial_mem_componentValues`).

Thus maximum-degree components are not artificial graph vertices.  They can
occur in intervals covered by the universal quantifiers of (1).

### 1.3 The degree-two pruning obstruction

If `r_t(S)<=2` and `d in L_t` divides `S`, (2) gives `tau(d)<=2`.  At `t=38`
the eligible left vertices are therefore exactly

\[
 \{1,2,3,5,7,11,13,17,19\},
\]

the number `1` and the eight primes at most `19`.  Lean evaluates this set's
cardinality as nine (`boundedDegreeEligibleLeft_card_38`) and proves, uniformly
in `n`,

```lean
theorem no_degreeTwo_quarterMatching_38 (n : ℕ) :
    ¬ ∃ M : ComponentMatching n 38,
      10 ≤ M.domain.card ∧
        ∀ d ∈ M.domain, componentDivisorDegree 38 (M.component d) ≤ 2
```

This theorem does **not** say that the full graph lacks a ten-vertex matching.
It says that deleting all right vertices of degree greater than two deletes
too much arithmetic structure to prove the quarter target.

## 2. Known results about the Erdős--Hooley Delta function

For `S>=1`, the Erdős--Hooley function is

\[
 \Delta(S)=\sup_{u\in\mathbb R}
   \#\{d\mid S:e^u<d\le e^{u+1}\}.
\]

The following are cited results, not results of this project.

* Hooley proved
  `sum_{S<=x} Delta(S) << x (log x)^(4/pi-1)` in 1979
  [Hooley79].
* Koukoulopoulos and Tao proved the much smaller mean upper bound
  \[
    \sum_{S\le x}\Delta(S)\ll x(\operatorname{Log}_2 x)^{11/4}
  \]
  (with their truncated logarithm convention) [KT23, Theorem 1][KT23].
  A 2024 note improves the exponent `11/4` to `5/2`; the 2025 real-moment
  paper records that current mean estimate and proves weighted moment bounds
  [BT24] [BT25, introduction and Theorems 1.1--1.4][BT25].
* De la Bretèche and Tenenbaum prove the normal-order upper estimate
  \[
    \Delta(S)\le(\log_2 S)^{\gamma}
  \]
  for every `gamma > 0.6102495...` on a density-one set [BT22, Theorem
  1.3][BT22].
* Ford, Green, and Koukoulopoulos prove, for every fixed `epsilon>0`,
  \[
    \Delta(S)\ge(\log\log S)^{0.35332277\ldots-\epsilon}
  \]
  for almost all `S` [FGK23, Theorem 1][FGK23].  Ford, Koukoulopoulos, and
  Tao also prove a complementary lower bound for the mean [FKT24, Theorem
  2][FKT24].

The source wording was checked against the linked abstracts/PDFs.  In
particular, Koukoulopoulos--Tao say, “We prove that” before their displayed
mean bound [KT23]; de la Bretèche--Tenenbaum describe “upper bounds for the
average and normal orders” [BT22]; and Ford--Green--Koukoulopoulos state
“for almost all n, a bound we believe to be sharp” [FGK23].  The 2025 moment
paper says it provides “new upper bounds for weighted real moments” [BT25].

All four kinds of statement concern an average or a density-one set as the
height tends to infinity.  None is a pointwise upper bound for every `S`, a
maximal-gap theorem for exceptions, or an estimate for component values in
every shifted interval.

There is also a direct pointwise warning.  Let `L=floor(t/2)` and take
`S=lcm(1,...,L)` (or a positive power of it).  Every integer in `(L/e,L]`
divides `S`, hence

\[
 \Delta(S)\ge L-\lfloor L/e\rfloor.                         \tag{3}
\]

All prime factors of `S` are below `t`, so `S` is its own `t`-smooth
component; choosing `n=S-1` represents it in `(n,n+t]`.  For fixed `t>=4`,
positive powers of `S` put the same linear-size Delta exception at arbitrarily
large heights inside the exact family B7 must handle.  Equation (3) is an
elementary construction here, not a claim extracted from the average-order
papers.

## 3. Our Delta attack and its exact stopping point

Everything in this section is our deduction from the cited estimates and the
machine-checked graph definitions.  No displayed sufficient condition is
claimed to be known.

### 3.1 Converting Delta to a right-degree bound loses a logarithm

Let

\[
 J=\lceil\log_2 L\rceil\quad(L\ge1).
\]

Partition the divisors `2<=d<=L` into the `J` half-open dyadic windows
`(2^(j-1),2^j]`.  Each factor-two window is contained in a factor-`e`
window from the definition of Delta.  Consequently

\[
 r_t(S)\le 1+J\Delta(S).                                    \tag{4}
\]

The extra `1` is the divisor `d=1`.  Formula (4) is pointwise and elementary,
but it is already too lossy for (1): even the impossible idealization
`Delta(S)=1` leaves a right-degree cap of order `log t`.

One can avoid the factor `J` by partitioning the **left divisors** into
dyadic bands.  That does not match B7's accounting.  The same component can
be adjacent to divisors in many left bands, so summing their neighbourhood
sizes overcounts right vertices.  B7 instead partitions the right component
values by `Nat.log2 S`, precisely so that its band sum remains equal to
`|N(U)|` [B7].  Delta concerns the locations of divisors *inside* a fixed
`S`; B7's scale is the size of `S` itself.  These are different axes.

### 3.2 First-moment edge counting is weaker than defect-Hall

For `U subset L_t`, put

\[
 r_U(S)=\#\{d\in U:d\mid S\},\qquad
 E(U)=\sum_{S\in N(U)}r_U(S).
\]

Double-counting edges gives

\[
 E(U)=\sum_{d\in U}|N(\{d\})|\ge |U|,                       \tag{5}
\]

because B4 proves that every left vertex has a neighbour.  Since
`r_U(S)>=1` on `N(U)`, (5) implies only

\[
 |U|-|N(U)|
 \le \sum_{S\in N(U)}(r_U(S)-1).                            \tag{6}
\]

Combining (4) and (6) yields

\[
 |U|-|N(U)|\le J\sum_{S\in N(U)}\Delta(S).                  \tag{7}

This is the wrong inequality shape.  Published results estimate Delta over
all integers up to `x`, not the adversarial component support `N(U)`, and
their polylogarithmic mean losses make the right side of (7) much larger than
the allowed slack in (1).  More importantly, (6) counts harmless redundant
edges as if they were Hall defect.

The public `t=38` witness makes that loss exact.  For

```text
U    = {13, 15, 16, 17, 18, 19}
N(U) = {323, 1365, 1710, 4176, 7072},
```

the five values have `U`-degrees `2,2,3,2,3`.  Therefore

\[
 E(U)=12,\qquad \sum(r_U(S)-1)=7,
 \qquad |U|-|N(U)|=1.                                      \tag{8}

The surplus bound loses a factor seven on the exact set where Hall first
fails.  Equation (8) is reproduced by direct divisibility checks; the B6
script independently computes the neighbourhood and defect [B6-script].

### 3.3 Why exceptional-component removal does not close the gap

Fix a cutoff `D` and call a component good when `r_t(S)<=D`.  If every
`d in U` retains a good neighbour, the same edge count gives only

\[
 |N_{good}(U)|\ge\lceil |U|/D\rceil.                        \tag{9}

For `U=L_t`, B7 needs about `|L_t|/2` neighbours.  A theorem using only
coverage plus a maximum right degree therefore needs essentially `D<=2`;
the star graph shows (9) is sharp for that information.  But (2) says the
degree-two subgraph can touch only `d` with `tau(d)<=2`, and the Lean theorem
at `t=38` shows that this leaves fewer than the required ten vertices.

Raising `D` restores more arithmetic vertices but makes (9) too weak.
Keeping the exceptional components rather than deleting them can help --
indeed they are essential in the `t=38` graph -- but then a proof needs to
control *which subsets of left vertices have alternative neighbours*.
Neither `Delta(S)` nor the number of exceptional right vertices records that
incidence information.

For reference, the exact `n=1407302,t=38` graph has a maximum matching of
`18`.  After retaining only right vertices with total degree at most `2`, the
existing B6 routines find only five covered left vertices and matching size
five.  This computation is not used by the Lean theorem, whose uniform
arithmetic upper bound is nine.  It can be reproduced without changing the
script by importing `lower_component_neighbors` and `maximum_matching` from
[`erdos461_numerics.py`](../scripts/research/erdos461_numerics.py).

### 3.4 The interval sieve remains one-fibre information

B5 proves for each fixed component `S` an injection of its fibre into a
`t`-rough quotient interval, followed by the tree's explicit Brun bound
[B5-Lean] [TreeBrun].  In the notation of B5, it has the shape

\[
 |F_S(n,t)|\le
 \ell_S\left(
   \prod_{p<t}(1-1/p)
   +\frac{(\sum_{p<t}1/p)^{2k+1}}{(2k+1)!}
 \right)
 +(\pi(t)+1)^{2k},                                         \tag{10}
\]

where

\[
 \ell_S=\left\lfloor\frac{n+t}{S}\right\rfloor
       -\left\lfloor\frac nS\right\rfloor.
\]

Summing (10) over realized components introduces both
`sum_S ell_S`, for which no required worst-case bound is available, and one
endpoint term per component.  More structurally, (10) is an upper bound on
the number of interval integers in one component fibre.  The edge quantities
in (5)--(9) ask how many *different component values divisible by each left
divisor* survive, simultaneously for every subset `U`.  No implication from
(10) to that statement was found.

This is the same simultaneous-support obstruction isolated independently in
`Problems/erdos461_known_bound.md`: the sieve controls each fibre after `S`
is fixed, but not the total collision loss or the correlations among all
fibres [B5].  Adding a mean Delta estimate does not create that missing
correlation.

## 4. Conjectured and assumed statements

The following remain open or conditional.

* Erdős 461 asks whether some absolute positive proportion of distinct
  components always occurs [ErGr80, p. 92][ErGr80] [EP461].
* `MultiscaleComponentExpansionAssumption` is B7's stronger quarter-matching
  target.  No instance exists [B7].
* The reported `t/log t` lower bound still has no located proof or precise
  source.  B5 proves it only from `SimultaneousFiberLossAssumption`; no
  instance exists [B1] [B5].

Nothing in the Delta literature cited above claims any of these statements.

## 5. Our conclusion and the input B9 would actually need

The tested route can be summarized as follows.

```text
Delta(S) on logarithmic divisor windows
  -> total right degree r_t(S) <= 1 + ceil(log2(t/2)) Delta(S)
  -> first-moment expansion |N(U)| >= |U| / degree-cap
  -X-> additive defect-Hall inequality (1)

one-fibre Brun upper bound
  -> control of |F_S(n,t)| after S is fixed
  -X-> simultaneous neighbourhood or collision-excess control

delete high-degree components
  -X-> quarter matching (formally fails for degree <= 2 at t=38)
```

A viable continuation would need a genuinely joint statement, for example a
uniform bound on the left vertices whose **entire** neighbourhood lies in an
exceptional component set, together with expansion for the remaining graph;
or a second-moment/incidence estimate that controls actual Hall defect rather
than the edge surplus in (6).  Such a result would have to be pointwise in
`n`, stable under the factorial/lcm components above, and simultaneous in
all `U subset L_t`.  No cited Delta theorem or existing interval-sieve theorem
has that form.

Accordingly B8 supplies no assumption instance and no proof of a new lower
bound.  Its positive formal output is the divisor-inheritance lemma, the
existence of represented maximum-degree components, and the exact
degree-two-pruning obstruction.  Its research output is the precise reason
the Delta/sieve combination stops.

[B1]: https://github.com/ProofFleet/moltresearch/pull/3730
[B4]: ../Conjectures/C0004_erdos461_smooth/src/ComponentGraph.lean
[B5]: erdos461_known_bound.md
[B5-Lean]: ../Conjectures/C0004_erdos461_smooth/src/KnownBound.lean
[B6-script]: ../scripts/research/erdos461_numerics.py
[B7]: erdos461_expansion.md
[BT22]: https://arxiv.org/abs/2210.13897
[BT24]: https://arxiv.org/abs/2309.03958
[BT25]: https://arxiv.org/abs/2512.05652
[EP461]: https://www.erdosproblems.com/461
[EP461-thread]: https://www.erdosproblems.com/forum/thread/461
[ErGr80]: https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf
[FGK23]: https://arxiv.org/abs/1908.00378
[FKT24]: https://arxiv.org/abs/2308.11987
[Hooley79]: https://doi.org/10.1112/plms/s3-38.1.115
[KT23]: https://arxiv.org/abs/2306.08615
[TreeBrun]: ../MoltResearch/Discrepancy/BrunIntervalSieve.lean
