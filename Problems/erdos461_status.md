# Erdős #461: B9 milestone status

Accessed 2026-09-08.  This memo separates established or machine-checked
facts, conjectural statements, and our deductions.  B9 does **not** prove a
new lower bound and declares no assumption instance.

## Executive summary

Neither milestone has been reached.  The positive-proportion conjecture is
still open, and the bound `f(n,t) ≫ t / log t` reported by Erdős and Graham
still has no proof or precise citation located by this project.  The sharpest
formal capstone is instead two exact obstruction statements in
[`Discharge.lean`](../Conjectures/C0004_erdos461_smooth/src/Discharge.lean).

```text
MultiscaleComponentExpansionAssumption
    <-> every interval has a divisor-compatible matching of size ceil(t / 4)
     -> Erdos461

Erdos461LogBound
    <-> SimultaneousFiberLossAssumption.
```

The first equivalence closes the B7 reduction to its exact matching target;
the last arrow is one-way because divisor-compatible matching is stronger
than merely counting distinct components.  The second equivalence is exact
for the reported logarithmic claim, because B5's collision ledger is an
identity.  The two direct conditional endpoints and the three B9 theorems are
guarded by `#print axioms` checks; they use only `propext`,
`Classical.choice`, and `Quot.sound`.

## 1. Known and machine-checked

### 1.1 Literature boundary

The maintained [Erdős Problems entry][EP461] currently marks Problem 461
open.  It asks whether the number of distinct `t`-smooth components in every
interval `(n,n+t]` is bounded below by a positive constant times `t`, and it
reports that Erdős and Graham could show a lower bound of order
`t / log t`.  Their original source states that report on printed p. 92
[ErGr80].  As documented by the source audit in [draft PR #3730][B1] and the
[B5 memo][B5-memo], the source gives no proof or citation for the display,
and no proof exposition was located.  Thus this project treats the
logarithmic estimate as reported, not as independently verified.  At the
access date, the tracker itself listed zero proof expositions.

The related distinct-multiples theorem of van Doorn, Li, and Tang determines
the general guarantee in an interval of length twice the largest divisor as
`min(m, ceil(2 sqrt(m)))` [VDLT26].  It concerns distinct integers rather
than distinct smooth-component values and gives only square-root scale for
the initial segment, so it does not discharge either B9 endpoint.

Published Erdős--Hooley Delta results also have the wrong quantifiers for
the present target.  Koukoulopoulos and Tao prove a mean-value upper bound
for `sum_{a <= x} Delta(a)` [KT23], while Ford, Green, and Koukoulopoulos
prove a lower bound for almost all integers [FGK23].  Neither is a
pointwise statement for the adversarial component support of every shifted
interval.

### 1.2 Exact endpoint of the B7 matching route

B4 proves the finite defect form of Hall's theorem for the lower-half
component graph.  B7 proves that its dyadic band sum counts the full
component neighbourhood exactly.  B9 packages the target as the proposition

```lean
def UniformQuarterComponentMatching : Prop :=
  ∀ n t : ℕ, 2 ≤ t →
    ∃ M : ComponentMatching n t, (t + 3) / 4 ≤ M.domain.card
```

and proves

```lean
theorem multiscaleComponentExpansionAssumption_iff_uniformQuarterMatching :
    MultiscaleComponentExpansionAssumption ↔
      UniformQuarterComponentMatching
```

in both directions.  Consequently the B7 class hides no additional
multiscale bookkeeping obligation: proving it is exactly proving a uniform
quarter-size matching in that graph.  B9 also proves the explicit conditional
endpoint

```lean
theorem erdos461_of_uniformQuarterComponentMatching
    (h : UniformQuarterComponentMatching) : Erdos461
```

No proof of its hypothesis is supplied.

### 1.3 Exact endpoint of the B5 collision route

B5 proves the integer identity

```text
collisionExcess(n,t) + smoothComponentCount(n,t) = t.
```

Moving one term across this equality shows that its named simultaneous-loss
interface is logically equivalent to the logarithmic lower bound, with the
same positive constant.  B9 proves

```lean
theorem erdos461LogBound_iff_simultaneousFiberLossAssumption :
    Erdos461LogBound ↔ SimultaneousFiberLossAssumption
```

This is an exact reformulation, not a proof of either side.  It also confirms
that improving the already formalized one-fibre Brun estimate cannot finish
the argument without genuinely new information coupling all fibres.

### 1.4 What B8 rules out

The [B8 memo][B8-memo] gives a no-route result for the proposed combination
of Delta bounds and the one-fibre interval sieve.  Its Lean component proves
that high-degree right vertices really occur: `(t / 2)!` is a represented
component of maximum lower-half divisor degree.  It also proves that at
`t = 38`, deleting every component of degree greater than two leaves at most
nine eligible matching vertices, below the B7 target ten.  These results rule
out that pruning argument; they do not refute the full quarter-matching
proposition or Erdős 461.

## 2. Conjectured and unresolved

`Erdos461`, `Erdos461LogBound`, `UniformQuarterComponentMatching`,
`MultiscaleComponentExpansionAssumption`, and
`SimultaneousFiberLossAssumption` are all uninhabited in this development.
No unconditional positive-proportion or logarithmic lower bound is claimed.

For the linear matching route, the exact remaining proposition is uniform
quarter matching: for every `n`, every `t >= 2`, and every left subset in the
equivalent defect formulation, the component neighbourhood must lose at
most `|L_t| - ceil(t/4)` vertices.  This is exact for the B7 route but remains
stronger than Erdős 461, which may admit a proof with no divisor-compatible
matching.

For the logarithmic route, the exact remaining proposition is the uniform
simultaneous collision inequality in `SimultaneousFiberLossAssumption`.
Unlike a per-fibre estimate, it must bound the total excess over all realized
component fibres at once and uniformly in the interval start.

## 3. Our deduction and the next useful target

The Phase-2 investigation shows that changing only a scalar estimate is
unlikely to help.  The missing input is incidence-sensitive and joint:

```text
one-fibre Brun bounds                       Delta mean/density bounds
          |                                          |
          +---------- no uniform coupling -----------+
                                  |
                                  X
             simultaneous collision loss / Hall defect
```

A viable next theorem would control, pointwise in `n`, the left vertices
whose entire neighbourhood lies among high-degree components, while proving
expansion for the remaining graph.  Equivalently, a second-moment or
incidence estimate could target actual fibre collision excess rather than
the much larger count of redundant divisor edges.  It must tolerate the
factorial and least-common-multiple components from B8, which occur inside
the universal family and cannot be discarded as density-zero exceptions.

This is our proposed research direction, not a consequence of the cited
Delta literature.  Any alternative route directly bounding the number of
represented smooth components could bypass quarter matching, but it would
still need uniform information across all component fibres to recover the
reported logarithmic estimate through the B5 ledger.

## 4. Milestone decision

- **M1 (`t / log t`) status:** not reached; exact equivalent obstruction
  `SimultaneousFiberLossAssumption`, with no instance.
- **M3 (`t`) status:** not reached; the refined route is exactly uniform
  quarter component matching, with no instance.
- **Lean results landed:** both equivalences above and the conditional theorem
  from uniform quarter matching to `Erdos461`, all audit-pinned.
- **Route excluded:** mean-value/density-one Delta estimates plus independent
  one-fibre Brun bounds and degree-two pruning.
- **Next target:** a pointwise joint incidence theorem controlling exceptional
  component neighbourhoods or total fibre collisions.

[B1]: https://github.com/ProofFleet/moltresearch/pull/3730
[B5-memo]: erdos461_known_bound.md
[B8-memo]: erdos461_delta_sieve.md
[EP461]: https://www.erdosproblems.com/461
[ErGr80]: https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf
[FGK23]: https://arxiv.org/abs/1908.00378
[KT23]: https://arxiv.org/abs/2306.08615
[VDLT26]: https://arxiv.org/abs/2603.28636
