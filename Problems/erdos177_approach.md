# Erdős #177: a residue-prefix route below exponent 8

## Executive summary

This memo proposes exponent `7`, not as a theorem, but as a sharply isolated conditional route.
The corresponding Lean theorem is
`erdos177Exponent_seven_of_assumptions` in
`Conjectures/C0005_erdos177_ap/src/Reduction.lean`. It requires two uninstantiated classes:

1. `FiniteResiduePrefixBalancingAssumption 7`, the research input;
2. `ResiduePrefixCompactnessAssumption 7`, a standard compactness step not yet formalized here.

The proved part converts anchored residue-prefix bounds into arbitrary arithmetic-progression
interval bounds with a factor of `2` and no exponent loss. Nothing in this memo or its Lean file
claims an unconditional improvement of Beck's `8+ε` exponent.

## 1. Known results

### 1.1 The target and Beck's theorem

For a coloring `f : ℕ → {−1,1}`, let `D_f(d)` be the supremum of the absolute sum on a finite
arithmetic progression with common difference `d`. Erdős Problem 177 asks how slowly a function
bounding every `D_f(d)` can grow. The problem page records Roth's square-root obstruction and
Beck's upper bound `D_f(d) ≤ d^(8+ε)` for every `ε>0` [Erdős Problems
#177](https://www.erdosproblems.com/177).

Beck's chapter says the AP result is obtained “as a corollary of a general balancing result.” The
published abstract states the bound for all sufficiently large `d`; a multiplicative constant
absorbs the finitely many remaining steps in the `Erdos177Exponent` formulation [Beck 2017,
Rutgers record and abstract](https://scholarship.libraries.rutgers.edu/esploro/outputs/bookChapter/A-Discrepancy-Problem-Balancing-Infinite-Dimensional/991031665483404646),
[DOI](https://doi.org/10.1007/978-3-319-55357-3_3).

The related countable-family problem starts with infinite sets
`A_i={a_i1<a_i2<...}` and seeks one coloring controlling the initial sums on the first `K` sets.
The database summary of Beck's result gives a `K^(4+ε)` bound [Erdős Problems
#178](https://www.erdosproblems.com/178). This is the general balancing exponent relevant below.

### 1.2 Where the arithmetic-progression exponent 8 comes from

This subsection is a reconstruction from the two stated Beck bounds, not a substitute for the
line-by-line proof audit assigned to C1.

For each positive step `q`, its arithmetic progressions split into the `q` residue sequences

```text
A_(q,r) = { r, r+q, r+2q, ... },       0 ≤ r < q.
```

Through step `d` there are

```text
K(d) = 1 + 2 + ... + d = d(d+1)/2 = Θ(d²)
```

such sequences. Applying a `K^(4+ε)` countable-family bound at `K=K(d)` gives
`d^(8+2ε)` up to constants; renaming `2ε` gives `d^(8+ε)`. An arbitrary interval in one residue
sequence is the difference of two initial sums, which costs a factor `2`, not another power.

Thus the visible exponent ledger is:

| source | exponent effect |
|:---|:---|
| enumerate all residues through step `d` | `K(d)=Θ(d²)` |
| Beck countable-family prefix bound | `K^(4+ε)` |
| substitute `K(d)` | `d^(8+2ε)` |
| prefix-to-interval conversion | constant factor `2` |

The quadratic count is real: every residue class is needed because the start is arbitrary. The
candidate place to move is therefore the `4` in the general balancing step, or a direct argument
that exploits relations among these residue sequences instead of treating them as arbitrary.

### 1.3 Available finite vector-balancing tools

Banaszczyk's theorem balances Euclidean-bounded vectors into a convex body of Gaussian measure at
least one half [Banaszczyk 1998](https://doi.org/10.1002/%28SICI%291098-2418%28199807%2912%3A4%3C351%3A%3AAID-RSA3%3E3.0.CO%3B2-S).
Bansal gave an SDP/random-walk algorithm for entropy-method discrepancy bounds [Bansal 2010,
arXiv:1002.2259](https://arxiv.org/abs/1002.2259), and Lovett--Meka's edge walk gives a constructive
partial-coloring lemma [Lovett--Meka 2012, arXiv:1203.5747](https://arxiv.org/abs/1203.5747).

These results motivate a finite partial-coloring attack. None of the cited finite theorems, as
stated, supplies one coloring with a bound independent of every future horizon. A successful use
here must also prevent discrepancy accumulated over successive blocks from producing a factor
depending on the length of the progression.

## 2. Conjectured inputs

### C3-BAL: finite residue-prefix balancing at exponent 7

For `0≤r<d`, define the anchored prefix

```text
P_f(d,r,M) = sum_{j<M} f(r + j d).
```

The main conjectural lemma is:

> There is a constant `C>0` such that, for every ambient horizon `N`, one can sign `[0,N)` so that
> `|P_f(d,r,M)| ≤ C d^7` whenever `r+Md≤N`, simultaneously for all positive `d`, `r<d`, and `M`.

This is exactly `FiniteResiduePrefixBalancingAssumption (7 : ℝ)`. It is deliberately stronger
than a collection of independent finite-`d` statements: the same finite coloring handles every
step and prefix visible below `N`.

There is no claim that changing to prefix notation makes the open problem disappear. The Lean
theorem `residuePrefixBoundedBy_of_apDiscrepancyBoundedBy` proves the reverse bookkeeping map
with no loss, while the forward map costs only `2`. Thus global residue-prefix balancing is
equivalent to the original target up to constants. The value of C3-BAL is that it exposes the
specific vector operator on which a structural improvement must act.

The exponent `7` corresponds to replacing the general prefix-balancing exponent `4+ε` by `7/2`
for this residue family, then paying the quadratic coordinate count: `(d²)^(7/2)=d^7`. There is
currently no proof of that half-power gain. It is a concrete research target, chosen because it is
strictly below `8` while leaving visible slack above Roth's `1/2` obstruction.

### C3-COMP: one infinite coloring from the finite witnesses

The second interface says that uniform finite feasibility has an infinite limit with the same
constant. This is `ResiduePrefixCompactnessAssumption α`.

Mathematically, form a finitely branching tree whose level-`N` vertices are valid sign strings of
length `N`; retain a vertex when it extends to valid strings at arbitrarily large horizons.
König's infinity lemma produces a branch. Equivalently, use compactness of the product
`{−1,1}^ℕ` and the finite-intersection property of the cylinder constraints. This is classified as
known, not conjectural mathematics. It stays an assumption only because C3 is limited to two
deliverables and the topological/tree extraction deserves its own tested leaf. Mathlib contains
the relevant compact-intersection API in
[`Mathlib.Topology.Compactness.Compact`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Compactness/Compact.html).

## 3. Our idea: exploit the residue incidence operator

The proposed proof of C3-BAL should not feed the residue sequences to a black-box theorem as
unrelated sets. Their incidence structure has three special features:

1. For fixed `d`, the `d` residue classes partition the integers. A variable contributes to
   exactly one residue coordinate at that step.
2. Two coordinates `(d,r)` and `(e,s)` intersect only when the congruences are compatible modulo
   `gcd(d,e)`; then their intersection has density `1/lcm(d,e)`.
3. Prefix constraints for one coordinate are nested in the horizon. They should be handled by a
   barrier potential, rather than paid for independently with a union bound.

The candidate analytic route is:

- center the incidence vectors within each fixed-`d` partition, separating the global partial sum
  (the `d=1` coordinate) from residue fluctuations;
- group steps dyadically and use the `gcd/lcm` overlap formula to bound the Gram energy of each
  step band;
- run an entropy/edge-walk partial coloring with thresholds proportional to `d^7`, freezing a
  constant fraction of the remaining variables at each round;
- include the current residue-prefix state in the convex barrier, so each round recenters rather
  than adding an independent error;
- iterate until integral and use compactness across ambient horizons.

The barrier-preservation bullet is the fragile one. A proof that merely bounds each new block by
`O(d^7)` accumulates `O(log N)` over dyadic blocks and does not establish C3-BAL. The needed lemma
must keep the *total state* in the same band at every round.

This route is inspired by finite vector-balancing machinery, but the proposed half-power gain and
barrier iteration are our ideas. We found no cited theorem that already supplies either one for
the infinite residue-prefix system.

## 4. Formal DAG

```text
C3-BAL  FiniteResiduePrefixBalancingAssumption α       [unproved research class]
   │
   ├──────────────┐
   │              ▼
   │      C3-COMP ResiduePrefixCompactnessAssumption α [known, unproved class]
   │              │
   │              ▼
   │      one f with |P_f(d,r,M)| ≤ C d^α
   │              │
   │              ├──────────────┐
   ▼              ▼              │
finite API   prefix split identity│                     [proved]
                  │              │
                  ▼              │
          arbitrary AP = P₂ - P₁                       [proved]
                  │
                  ▼
          APDiscrepancyBoundedBy f (2C d^α)             [proved]
                  │
                  ▼
          erdos177Exponent_of_assumptions α             [proved, conditional]
                  │
                  ▼
          Erdos177Exponent 7 and 7 < 8                  [conditional / proved arithmetic]
```

The exact Lean statements are:

- `finiteResiduePrefixWitness_of_global` — proved restriction to every finite horizon;
- `residuePrefixBoundedBy_of_apDiscrepancyBoundedBy` — proved reverse normalization, showing no
  difficulty is hidden by the prefix formulation;
- `residuePrefixSum_add_length` — proved range split;
- `intervalSum_eq_residuePrefixSum_sub` — proved normalization using division with remainder;
- `apDiscrepancyBoundedBy_of_residuePrefixBoundedBy` — proved triangle-inequality transfer;
- `erdos177Exponent_of_assumptions` — proved generic conditional capstone;
- `erdos177Exponent_seven_of_assumptions` — the exponent-seven specialization;
- `erdos177_seven_lt_eight` — proved strict numerical inequality.

No default or noncomputable instance discharges either assumption.

## 5. Failure modes and falsification tests

- **Hidden horizon loss.** Any estimate containing `log N`, however slowly, fails the problem's
  length-uniform quantifier. Track the barrier after every partial-coloring round.
- **Independent-coloring fallacy.** Choosing a new coloring for each `N` does not itself define an
  infinite coloring. C3-COMP is explicit so this quantifier change cannot be hidden.
- **Residue omission.** Controlling only residue `0` recovers homogeneous APs and is insufficient;
  every `r<d` is present in C3-BAL.
- **Endpoint mismatch.** The finite witness constrains a prefix only when its ambient endpoint
  `r+Md` is at most `N`; it never reads unconstrained signs beyond the finite horizon.
- **Generic black-box regression.** If the Gram/entropy calculation uses only the number of
  coordinates and ignores partition and `gcd/lcm` structure, it should reproduce Beck's exponent,
  not improve it.
- **Overclaiming compactness.** The compactness interface preserves a fixed constant `C`; allowing
  `C_N` to grow with `N` would make the conclusion false.

## 6. Phase-2 items

These are proposed follow-up items; all checkboxes are intentionally open.

- [ ] C3-P2.1 (after: C3): Prove `ResiduePrefixCompactnessAssumption α` by a finitely branching
  tree or compact-product argument. Deliverable:
  `Conjectures/C0005_erdos177_ap/src/ResiduePrefixCompactness.lean`.
- [ ] C3-P2.2 (after: C3): Formalize the partition and pair-overlap identities, including the
  compatibility criterion modulo `gcd(d,e)` and density/count bounds through a finite horizon.
  Deliverable: `MoltResearch/Discrepancy/ResiduePrefixIncidence.lean` plus its stable-surface
  example.
- [ ] C3-P2.3 (after: C1, C3): Translate Beck's actual general balancing theorem into the
  `P_f(d,r,M)` notation and verify the `4 × 2 = 8` exponent ledger against every constant and
  cutoff in the paper. Deliverable: `Problems/erdos177_beck_translation.md`.
- [ ] C3-P2.4 (after: C2, C3): Add prefix-compatible numerics: optimize at `N`, freeze that prefix,
  extend to `2N`, and log the barrier slack by `(d,r)`. Deliverables:
  `scripts/research/erdos177_prefix_extension.py` and
  `Problems/erdos177_prefix_extension.md`.
- [ ] C3-P2.5 (after: C3-P2.2, C3-P2.3): State the range-aware weighted partial-coloring lemma
  with a `d^7` barrier and prove every entropy/Gram side condition that follows from the residue
  incidence identities. Deliverable:
  `Conjectures/C0005_erdos177_ap/src/ResidueBarrierPartialColoring.lean`.
- [ ] C3-P2.6 (after: C3-P2.1, C3-P2.5): Iterate the partial coloring without horizon loss and
  discharge `FiniteResiduePrefixBalancingAssumption 7`; only then apply the existing conditional
  capstone. Deliverable:
  `Conjectures/C0005_erdos177_ap/src/ExponentSeven.lean`.

## 7. Bottom line

The reduction cleanly separates three issues. Prefix-to-interval bookkeeping is finished in Lean
and costs only `2`. Compactness is standard but still needs a dedicated formal proof. The actual
open work is C3-BAL: a structure-sensitive, barrier-preserving finite balancing lemma. A
half-power improvement from `4` to `7/2` at that stage would give exponent `7`, hence a genuine
strict improvement over Beck. Until that assumption is discharged, the result remains entirely
conditional.
