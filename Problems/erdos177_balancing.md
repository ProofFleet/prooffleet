# Erdős #177: barrier-preserving balancing audit

## Executive summary

We did not find a theorem that proves the finite residue-prefix balancing input at any exponent
below `8`.  The obstruction is not the finite-to-infinite compactness step; that is already proved
in `Compactness.lean`.  It is the absence of a partial-coloring theorem that keeps the **total
current state** inside one fixed, step-weighted prefix barrier while more signs become integral.

`Conjectures/C0005_erdos177_ap/src/Balancing.lean` records that missing statement as
`BarrierPreservingPartialColoringAssumption α`.  It proves, without changing the target, that this
strictly stronger assumption implies `FiniteResiduePrefixBalancingAssumption α`, and hence
conditionally proves `Erdos177Exponent α`.  No instance of the new assumption is supplied.  In
particular, this memo and the Lean file do **not** prove exponent `7` or any improvement of Beck's
bound.

The sharpest obstruction found is already present in the `d=1` prefix rows.  A direct use of the
Lovett--Meka partial-coloring lemma with a horizon-independent barrier `B` would need thresholds
`c_M ≤ B/√M`.  Its entropy sum then has order `N`, rather than the required at most `N/16`.
Banaszczyk's final-sum theorem and Bansal's bounded-degree theorem likewise acquire explicit
horizon dependence under the raw prefix encoding.  Prefix-vector encodings exploit nesting but
the available worst-case bound still contains `√log N`.  None preserves the invariant needed by
C6.

## 1. Known results

### 1.1 The target left by C3--C5

For a partial coloring `x : [0,N) → {−1,0,1}`, put

```text
P_x(d,r,M) = sum_{j<M} x(r+jd),
B_α(x) = max |P_x(d,r,M)| / d^α,
```

where `d>0`, `r<d`, and `r+Md≤N`.  C3 isolated the assertion that some constant `C` admits a
full coloring with `B_α(x)≤C` for every `N`.  C4 proved that uniform finite feasibility passes to
one infinite coloring without changing `C`.  C5 found heuristic witnesses with barrier exactly
`1` through `N=8192` for `α=4` and `α=7`; it explicitly did not establish uniform feasibility.

Thus any factor depending on `N`, including `log N` or `log log N`, is fatal.  Increasing `α`
cannot absorb such a factor at `d=1`, because `1^α=1`.

### 1.2 What Beck's published statement supplies

Beck's accessible abstract says the arithmetic-progression result is obtained “as a corollary of
a general balancing result.”  It gives one coloring with

```text
D_g(d) ≤ d^(8+ε)
```

for all sufficiently large `d`, uniformly in the start and length [Beck 2017, Rutgers publication
record and abstract](https://scholarship.libraries.rutgers.edu/esploro/outputs/bookChapter/A-Discrepancy-Problem-Balancing-Infinite-Dimensional/991031665483404646),
[DOI](https://doi.org/10.1007/978-3-319-55357-3_3).

For the countable-family formulation, the published problem record states a prefix bound
`O(K^(4+ε))` for the first `K` sequences [Erdős Problem
178](https://www.erdosproblems.com/178).  Enumerating the residue sequences `(q,r)` with
`1≤q≤d` uses

```text
K(d) = sum_{q≤d} q = d(d+1)/2 = Θ(d²).
```

Black-box substitution therefore gives `K(d)^(4+ε)=d^(8+2ε)`; renaming the epsilon recovers
the stated exponent.  An exponent below `8` requires either a countable-family exponent below
`4` or a theorem that uses relations among residue sequences.  The black-box theorem alone
cannot do it.

We could access the abstract and bibliographic record, but not the full 2017 chapter.  Therefore
this audit does not claim a line-by-line diagnosis of Beck's internal proof or of each constant in
the exponent `4`.  That source obstruction is the same one recorded on C1.  The conclusion here is
limited to the exact input-output implication above.

### 1.3 Lovett--Meka and Bansal partial coloring

Lovett and Meka's main partial-coloring lemma starts from `x₀∈[-1,1]^n`, vectors
`v₁,…,v_m∈ℝⁿ`, and thresholds `c_j≥0` satisfying

```text
sum_j exp(-c_j²/16) ≤ n/16.
```

It finds `x` with at least half the coordinates close to `±1` and controls **increments** by

```text
|⟨x-x₀,v_j⟩| ≤ c_j ||v_j||₂.
```

This is Theorem 4 of [Lovett--Meka 2012](https://arxiv.org/pdf/1203.5747).  The distinction
between an increment and the total state is decisive below.

Bansal's SDP/random-walk algorithm gives finite set-system discrepancy
`O(√n log(2m/n))`, and its bounded-degree theorem gives `O(√t log n)` when each variable occurs
in at most `t` sets [Bansal 2010, Theorems 1.1 and
1.2](https://arxiv.org/pdf/1002.2259).  These are full-coloring conclusions, but their parameters
are those of the finite horizon.

Bansal and Garg identify the iteration problem exactly: “the errors can add up in an adversarial
way.”  Their beyond-partial-coloring framework removes that loss for several finite discrepancy
problems, but it does not state a nonuniform, countable-coordinate theorem for the residue-prefix
barrier [Bansal--Garg 2017](https://arxiv.org/pdf/1611.01805).

### 1.4 Banaszczyk and prefix discrepancy

Banaszczyk's 1998 theorem signs Euclidean-small vectors into a convex body of Gaussian measure at
least `1/2` [Banaszczyk
1998](https://onlinelibrary.wiley.com/doi/abs/10.1002/%28SICI%291098-2418%28199807%2912%3A4%3C351%3A%3AAID-RSA3%3E3.0.CO%3B2-S).
It controls one final vector sum.  It is not, as stated, a theorem about preserving an already
occupied prefix barrier.

The [signed-series version](https://doi.org/10.1002/rsa.20373) does address every chronological
prefix of a finite vector sequence.  A recent primary-source summary states the worst-case bound
for `T` unit vectors in dimension `k` as `O(√(log k + log T))`
[Bansal--Jiang--Meka--Singla--Sinha 2022, Theorem
1](https://doi.org/10.4230/LIPIcs.ITCS.2022.13).  The authors describe this as “incurring a
`√log T` dependence on the number of vectors `T`.”  Their improved smoothed theorem still depends
on `log log T` and assumes random perturbations; the deterministic residue-incidence vectors do
not satisfy that model.

For comparison, Matoušek and Spencer prove a coloring of `[N]` whose discrepancy over all finite
arithmetic progressions is `O(N^(1/4))` [Matoušek--Spencer
1996](https://doi.org/10.1090/S0894-0347-96-00175-0).  That important finite theorem is uniform
over progressions, not step-weighted, and its `N^(1/4)` dependence cannot survive the `d=1`
quantifier here.

## 2. Conjectured sharpening recorded in Lean

The new class asks for a constant `C>0`, independent of `N`, with the following property.
Whenever a partial coloring `f` has

```text
|P_f(d,r,M)| ≤ C d^α
```

for every visible residue prefix and has at least one zero entry, there is a partial coloring `g`
such that:

1. `g` obeys the same barrier with the same `C`;
2. `g` agrees with `f` at every already colored position;
3. `g` has strictly fewer zero entries.

This is `BarrierPreservingPartialColoringAssumption α`.  It is stronger than the finite balancing
assumption in two ways: it extends every feasible partial state, rather than merely the zero state,
and it preserves old signs.  A standard constant-fraction conclusion would be stronger still;
strict progress is all the finite-descent proof needs.

The Lean proof starts from the zero coloring, whose residue-prefix sums vanish, and repeatedly
uses strict decrease of `uncoloredCount`.  Termination gives a full sign coloring with the same
barrier.  The resulting instance chain is

```text
BarrierPreservingPartialColoringAssumption α
    -> FiniteResiduePrefixBalancingAssumption α
    -> ResiduePrefixBoundedBy f α C          (C4 compactness)
    -> Erdos177Exponent α                    (C3 reduction).
```

Only the arrows are proved.  The first node remains an uninstantiated conjectural interface.

## 3. Our obstruction calculations

### 3.1 Raw prefix rows fail the Lovett--Meka entropy test

At the first round all `N` variables are alive.  For `d=1`, the length-`M` prefix has indicator
row `v_M=1_[0,M)` and `||v_M||₂=√M`.  To keep its increment within a fixed barrier `B`, the
Lovett--Meka conclusion would require

```text
c_M ||v_M||₂ ≤ B, hence c_M ≤ B/√M.
```

The contribution from the `d=1` rows alone is therefore bounded below by

```text
sum_{M=1}^N exp(-c_M²/16)
  ≥ sum_{M=ceil(B²)}^N exp(-B²/(16M))
  ≥ (N-ceil(B²)+1) exp(-1/16).
```

For every fixed `B`, this exceeds `N/16` for all sufficiently large `N`.  Thus the sufficient
entropy hypothesis fails before any other step or residue is included.  This does not prove that a
good coloring is impossible; alternating signs show that the nested `d=1` family itself is easy.
It proves that treating its prefixes as unrelated Lovett--Meka rows loses the nesting that the
desired theorem must exploit.

At a later round the theorem controls `A(x-x₀)`, not `Ax`.  If a coordinate of `Ax₀` is already on
the barrier, any symmetric nonzero increment allowance permits an outward move.  Barrier
preservation needs a slack-aware or one-sided condition on active faces, not another application
with the original symmetric thresholds.

### 3.2 Raw all-prefix matrices fail the other black boxes

There are `N` nonempty `d=1` prefix rows.  The column for position `0` lies in every one, so its
Euclidean norm in the raw incidence matrix is at least `√N`.  Normalizing columns to use
Banaszczyk's 1998 theorem shrinks the desired `d=1` body width to `O(B/√N)`; even its
one-dimensional Gaussian marginal then has measure tending to zero, rather than at least `1/2`.

The same column belongs to at least `N` sets, so the bounded-degree parameter in Bansal's theorem
satisfies `t≥N`.  Its `O(√t log N)` conclusion is consequently horizon-dependent before the rows
for `d>1` are counted.

These are obstructions to the direct encodings, not lower bounds against a structure-sensitive
factorization or a different convex body.

### 3.3 Prefix-vector encoding still leaks the horizon

Fix a step cutoff `D` and make one coordinate for each residue sequence `(d,r)` with `d≤D`.
There are `K(D)=Θ(D²)` coordinates.  At chronological time `n`, the incidence vector has one
nonzero coordinate for each step, so its Euclidean norm is `√D`.  After normalization, the
signed-series bound gives the original residue prefixes at size

```text
O(√D * √(log K(D) + log N)).
```

The `√log N` factor fails the required uniformity.  Taking `D=N` also makes the bound on the
`d=1` coordinate grow.  Dimension-only signed-series bounds avoid `N` for a fixed `D`, but give
one common allowance depending on `D` to all coordinates; that allowance again diverges at
`d=1` when `D→∞`.  A proof must assign compatible coordinate-dependent budgets while constructing
one coloring for every cutoff simultaneously.  That is the role Beck's countable-family theorem
plays, at exponent `4+ε` in the sequence index.

## 4. Our proposed next lemma

The natural state space is the polytope

```text
Q_N(C,α) = {x in [-1,1]^N : |P_x(d,r,M)| ≤ C d^α for every visible prefix}.
```

A candidate edge walk would remain in `Q_N(C,α)`, keep coordinates already at `±1` fixed, and
hit at least one new coordinate face.  The first geometric sublemma one would seek is that, at
every reachable state, the inward/tangent cone of the currently tight prefix faces contains a
direction supported on the unfixed coordinates that can reach a new cube face.

That sublemma alone would **not** imply the Lean interface above.  The interface deliberately uses
ternary states: every coordinate not yet fixed at `±1` is exactly `0`.  A generic edge-walk step
from such a state makes the other live coordinates fractional.  Even with no prefix constraints,
starting at `(0,0)` in direction `(1,1/2)` reaches `(1,1/2)`, not a new element of
`{−1,0,1}²`.  Resetting the second coordinate to zero need not preserve the prefix barrier.  Thus
a usable next lemma must do one of two additional things:

1. produce a new **ternary** feasible state directly, with at least one additional sign; or
2. use a fractional-state invariant throughout, count coordinates fixed at `±1`, and prove that
   its terminal state converts to the full integer witness required by
   `FiniteResiduePrefixBalancingAssumption`.

The second route matches standard edge walks better but requires a new formal interface and a
termination proof; it is not supplied by the tangent-cone observation.  A constant-dimensional
family of admissible directions could support constant-fraction progress only after this state
space mismatch is resolved.

The residue structure offers possible input: for fixed `d` the residue classes partition the
variables, and prefix rows within one residue are nested.  Across steps, intersections are governed
by `gcd/lcm`.  What is missing is an inequality converting those facts into a rank, Gaussian
measure, or entropy bound for the **active faces at the current state**.  Bounding fresh increments
band by band is insufficient: summing one `O(d^α)` increment over `Θ(log N)` rounds recreates the
forbidden horizon factor.

The Lean class quantifies over every feasible partial state.  That is convenient and matches the
arbitrary-start form of modern edge-walk lemmas, but it may be stronger than necessary: a proof
restricted to states reachable from zero would also discharge finite balancing.  If trapped
feasible states exist, C7 should replace the class by a reachability-indexed invariant rather than
weaken the final discrepancy statement.

## 5. No-route verdict

No cited theorem closes C6 as written.

| input | exact stopping point |
|:---|:---|
| Beck `K^(4+ε)` countable-family bound | `K(d)=Θ(d²)` gives exponent `8+2ε`; the full proof was unavailable for an internal sharpening audit |
| Lovett--Meka | its entropy condition fails at fixed barrier using the `d=1` raw prefix rows; it controls increments, not the occupied barrier |
| Bansal 2010 | the raw prefix set system has degree at least `N`, so the guarantee depends on the horizon |
| Banaszczyk 1998 | direct all-prefix columns have norm at least `√N`, and the normalized target body loses the required Gaussian measure |
| Banaszczyk signed-series bound | the prefix-vector encoding retains `√log N` in the worst-case guarantee |
| Bansal--Garg / smoothed prefix methods | they remove some iteration loss only under different finite or stochastic hypotheses; no deterministic countable weighted barrier theorem is stated |
| Matoušek--Spencer finite AP theorem | its `N^(1/4)` guarantee is not step-dependent and grows at `d=1` |

Accordingly, C6 lands a precise conditional interface and its finite-descent proof, not an
unconditional exponent.  The exact remaining mathematical task is to prove a stateful,
barrier-preserving walk for the structured residue-prefix polytope, or to find a weaker
zero-reachable invariant that still yields the same finite witnesses.
