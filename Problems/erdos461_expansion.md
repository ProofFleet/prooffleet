# Erdős 461: multiscale component expansion

## Executive verdict

The viable Phase-2 interface is a defect-Hall inequality after partitioning
the **smooth-component values** into disjoint dyadic bands.  It asks that the
total band-by-band neighbourhood of every lower-half divisor set leave at
most the slack needed for a matching of size
`ceil(t / 4) = (t + 3) / 4`.  The interface is explicit and falsifiable, but
it is not proved here and no Lean instance is declared.

The machine-checked result is only the reduction: this multiscale inequality
implies `ProportionalComponentMatchingAssumption`, with constant `1 / 4`, and
hence conditionally implies `Erdos461`.  The B6 multiple-matching
obstructions do not refute the new inequality.  Their lower-half component
graphs have zero Hall defect in the exact `t = 8, n = 1255` computation and
at every tested divisible centre through `t = 40` [B6].

## Known and machine-checked facts

Erdős and Graham ask for a uniform positive-proportion lower bound for the
number of distinct smooth components in `(n,n+t]`; the maintained problem
page still lists the question as open [ErGr80, p. 92][ErGr80] [EP461].  The
B3 reduction isolates a positive-proportion matching from
`{1,...,floor(t/2)}` to distinct component values [B3].  B4 proves the exact
finite defect-Hall criterion for such a matching [B4].

For a left set `U`, let `N(U)` be its component neighbourhood.  The new Lean
file assigns each represented component value `S` the scale

\[
j(S)=\lfloor \log_2 S\rfloor,
\]

implemented by `Nat.log2 S`, and defines

\[
N_j(U)=\{S\in N(U):j(S)=j\}.
\]

The `N_j(U)` are disjoint.  Lean proves the exact accounting identity

\[
\sum_{j\in j(R_{n,t})}|N_j(U)|=|N(U)|
\]

as `multiscaleComponentNeighborhoodCard_eq`.  This matters because summing
neighbourhoods of different **left** scales can count the same highly
divisible component many times; partitioning the right values cannot.

The rounding facts needed by the reduction are also proved: for `t >= 2`,
`ceil(t/4) <= floor(t/2)`, and as real numbers
`t/4 <= ceil(t/4)`.  Combining these with B4 gives the theorem

```lean
theorem proportionalComponentMatchingAssumption_of_multiscale
    [MultiscaleComponentExpansionAssumption] :
    ProportionalComponentMatchingAssumption
```

and then the conditional theorem

```lean
theorem erdos461_of_multiscaleComponentExpansion
    [MultiscaleComponentExpansionAssumption] : Erdos461
```

These theorem statements are checked in
[`Expansion.lean`](../Conjectures/C0004_erdos461_smooth/src/Expansion.lean).

## Conjectured or assumed statement

The single new open input is:

```lean
class MultiscaleComponentExpansionAssumption : Prop where
  defect_bound : ∀ n t : ℕ, 2 ≤ t → ∀ U ⊆ componentLeft t,
    U.card ≤ multiscaleComponentNeighborhoodCard n t U +
      ((componentLeft t).card - (t + 3) / 4)
```

Equivalently, because the band sum is exactly `|N(U)|`, every left set has
Hall defect at most

\[
|L_t|-\lceil t/4\rceil.
\]

This is stronger than Erdős 461: the original problem asks for some unknown
positive constant and does not require divisor-compatible representatives.
The choice `1/4` is therefore a concrete research target, not a known
constant and not a claim inferred from the finite computations.  No instance
of the assumption class exists in this PR.

## Our proposed route

The point of the reformulation is to give B8 a sum whose terms line up with
divisor-window and sieve estimates while preserving exact Hall bookkeeping.
For each `U subset L_t`, one can try to lower-bound `|N_j(U)|` separately in
the ranges `2^j <= S < 2^(j+1)`, then sum the disjoint contributions.  A
successful proof must establish

\[
|U|\le \sum_j |N_j(U)|+|L_t|-\lceil t/4\rceil
\]

uniformly in `n`, `t`, and `U`.

The formal dependency graph is:

```text
scale fibres N_j(U)
  -> exact disjoint sum = |N(U)|                    (proved here)

MultiscaleComponentExpansionAssumption
  -> B4 finite defect-Hall with q = ceil(t/4)       (proved here)
  -> ProportionalComponentMatchingAssumption, c=1/4
  -> Erdos461                                       (conditional)

divisor-window bounds + interval sieve
  - - -> per-scale lower bounds                     (open; B8)
```

### Check against the B6 obstructions

The false upper-half route matched divisors to interval **integers**.  Around
a highly divisible centre, many left vertices then share one integer and the
defect grows linearly [B6].  The refined interface instead keeps B3's
lower-half divisors and component-valued right side.

At `t = 8, n = 1255`, B6 computes zero defect for all 16 subsets of the
lower-half component graph.  The reproducible B6 self-check finds the same
zero maximum defect at its divisible-centre tests for every `3 <= t <= 40`
[B6-script].  Zero defect implies the proposed inequality immediately,
since its allowed slack is nonnegative.  Thus there is no B6 counterexample
to retain for this interface.

This is only finite evidence.  The public discussion includes a different
failure of a perfect component matching at `t = 38, n = 1407302` [EP461-thread].
Running the B6 exact defect routine on that interval gives left-set size 19,
maximum matching 18, and maximum defect 1.  One defect witness is

```text
U = {13, 15, 16, 17, 18, 19}
N(U) = {323, 1365, 1710, 4176, 7072}.
```

The quarter target is `ceil(38/4) = 10`, so the permitted defect is
`19 - 10 = 9`; the public example satisfies the proposed inequality.  This
is our exact computation using the B6 script, not a literature claim.  The
inequality remains an assumption until it is proved or exhaustively refuted.
It can be reproduced without changing the script:

```bash
python3 -c 'import runpy; m=runpy.run_path("scripts/research/erdos461_numerics.py"); p=m["hall_defect_profile"](m["lower_component_neighbors"](1407302,38)); print(p.matching_size,p.max_defect,p.witness_left,p.witness_neighbors)'
```

## Where the route stops

The multiscale sum is exact bookkeeping, not new expansion.  Neither B6 nor
the cited literature supplies a uniform lower bound for its terms.  In
particular, normal-order information about divisors cannot be substituted
for the worst-case, every-interval, every-subset inequality needed here.
B8 must either prove enough per-scale expansion after exceptional components
are isolated or return an exact counterexample/no-route result.

[B3]: erdos461_approach.md
[B4]: ../Conjectures/C0004_erdos461_smooth/src/ComponentGraph.lean
[B6]: erdos461_obstructions.md
[B6-script]: ../scripts/research/erdos461_numerics.py
[EP461]: https://www.erdosproblems.com/461
[EP461-thread]: https://www.erdosproblems.com/forum/thread/461
[ErGr80]: https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf
