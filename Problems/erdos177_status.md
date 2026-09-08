# Erdős #177: C7 milestone status

## Executive summary

C7 does **not** reach M2.  We found no proof of `Erdos177Exponent α` for any `α < 8`, and this
change declares no instance of either balancing assumption.  The strongest rigorous capstone is
instead an exact obstruction theorem:

```text
Erdos177Exponent α
    ↔ FiniteResiduePrefixBalancingAssumption α.
```

The theorem `erdos177Exponent_iff_finiteResiduePrefixBalancing` in
`Conjectures/C0005_erdos177_ap/src/Discharge.lean` proves both directions.  In particular, at
`α = 7` the finite residue-prefix balancing proposition is not merely one convenient sufficient
condition; after the C4 compactness discharge it is equivalent to the desired exponent-seven
statement.  The exact remaining mathematical task is therefore uniform finite balancing with a
constant independent of the horizon.  C6's barrier-preserving partial-coloring interface is a
concrete sufficient route to that task, but is stronger than the exact obstruction and remains
uninstantiated.

## 1. Known and proved

### 1.1 Literature boundary

Erdős Problem 177 asks for one sign sequence whose discrepancy on every finite arithmetic
progression is bounded by a function of the common difference alone.  The problem record lists
Roth's square-root lower bound and Beck's `d^(8+ε)` upper bound, and still records the problem as
open [Erdős Problems #177](https://www.erdosproblems.com/177).  Beck's published abstract states
that his bound is uniform in the start and length and is derived from a general infinite-dimensional
vector-balancing result [Beck 2017, Rutgers record](https://scholarship.libraries.rutgers.edu/esploro/outputs/bookChapter/A-Discrepancy-Problem-Balancing-Infinite-Dimensional/991031665483404646),
[DOI](https://doi.org/10.1007/978-3-319-55357-3_3).

Those literature results remain recorded as propositions in `Statement.lean`; this project has not
machine-checked their proofs.  In particular, C7 makes no new unconditional discrepancy claim.

### 1.2 Formal reduction now closed in both directions

The tree proves the following steps:

1. A global AP bound controls anchored residue prefixes with the same constant
   (`residuePrefixBoundedBy_of_apDiscrepancyBoundedBy`).
2. A global residue-prefix bound restricts to a valid witness at every finite horizon
   (`finiteResiduePrefixWitness_of_global`).
3. Uniform finite witnesses have one coherent infinite limit with no loss in the constant; C4
   supplies `residuePrefixCompactnessAssumption α` for every `α`.
4. Every AP interval is the difference of two anchored prefixes, costing the constant factor `2`
   but no power of the step (`apDiscrepancyBoundedBy_of_residuePrefixBoundedBy`).

C7 combines both routes.  If `Erdos177Exponent α` holds with a constant `C`, the one-term
progression at step `1` gives `1 ≤ C`, so `C > 0`; restricting the same coloring gives the finite
balancing class.  Conversely, an inhabitant of that class passes through the proved compactness
instance and prefix-to-interval reduction to give `Erdos177Exponent α`.  This proves the displayed
equivalence without adding an assumption instance.

### 1.3 What C6 proves

C6 proves a finite descent

```text
BarrierPreservingPartialColoringAssumption α
    → FiniteResiduePrefixBalancingAssumption α
    ↔ Erdos177Exponent α.
```

The first arrow is one-way: the barrier-preserving class requires every feasible ternary partial
state to extend while preserving old colors and the same barrier.  The exact finite balancing
proposition only asks for one full witness at each horizon.  C7 therefore identifies finite
balancing, not the stronger barrier-preserving walk, as the exact logical obstruction.

## 2. Conjectured and unresolved

No value `α < 8` is known here to inhabit `FiniteResiduePrefixBalancingAssumption α`.  The proposed
case

```text
FiniteResiduePrefixBalancingAssumption (7 : ℝ)
```

remains conjectural.  By the C7 equivalence, instantiating it would be exactly an unconditional
proof of `Erdos177Exponent 7`, hence a strict improvement over Beck.  Conversely, any proof of
exponent seven would automatically supply the finite class by restriction, so changing the
presentation cannot evade this obligation.

The C6 class `BarrierPreservingPartialColoringAssumption 7` is also conjectural.  It is a plausible
proof interface, not a claim that every feasible partial state actually extends.  A weaker
reachability-indexed or fractional-state invariant could still prove finite balancing without
proving the C6 class.

## 3. Our obstruction analysis and next route

### 3.1 Exact stopping point for the direct Lovett--Meka encoding

For horizon `N`, the raw `d = 1` prefix rows are `v_M = 1_[0,M)`, with
`‖v_M‖₂ = √M`.  Keeping every increment within a fixed barrier `B` would require thresholds
`c_M ≤ B/√M`.  Lovett and Meka's main partial-coloring lemma requires

```text
sum_M exp(-c_M^2 / 16) ≤ N / 16.
```

For all `M ≥ B²`, each summand is at least `exp(-1/16)`, so the left side is asymptotic to `N`
and eventually exceeds `N/16`.  The sufficient entropy test therefore fails already on the nested
step-one rows.  The source theorem also controls the increment `x - x₀` and returns fractional
values for coordinates not near `±1`; it does not preserve an occupied absolute barrier or return
the ternary state required by the C6 interface [Lovett--Meka 2012, Theorem
4](https://arxiv.org/pdf/1203.5747).

This is a no-route result for that direct encoding, not a lower bound against structured
balancing.  Alternating signs alone balance the nested `d = 1` family, showing that the black-box
entropy accounting discards useful nesting.

### 3.2 Why the usual finite bounds do not close the gap

In the raw all-prefix set system, the variable at position zero occurs in at least `N` step-one
prefixes.  A bounded-degree estimate therefore inherits horizon dependence.  Bansal's finite
set-system theorem gives a discrepancy bound containing `√t log n` in the bounded-degree regime
[Bansal 2010](https://arxiv.org/abs/1002.2259); here `t ≥ N` before rows for `d > 1` are counted.
Likewise, iterating a partial coloring with a fresh fixed-size error per round leaks a `log N`
factor.  Any such factor is fatal at `d = 1`, since it cannot be absorbed into `d^α`.

The numerical witnesses through `N = 8192` with barrier `1` at `α = 4,7` are finite observations,
not a uniform theorem and not a source of an assumption instance.  Their useful signal is only that
small steps deserve a structure-sensitive treatment.

### 3.3 Sharp next target

The next proof should target `FiniteResiduePrefixBalancingAssumption 7` directly.  The most
plausible refinement is a walk inside the step-weighted residue-prefix polytope that uses nesting
within each residue class and `gcd/lcm` structure across steps.  It may replace the overstrong
“extend every ternary state” requirement with either:

1. an invariant only for states reachable from the zero coloring; or
2. a fractional-state invariant that counts fixed coordinates and proves an integral terminal
   witness.

Either route must keep the **total current state** inside one horizon-independent barrier.  A bound
on fresh increments, followed by triangle inequality over rounds, is insufficient.

## 4. Milestone decision

- **M2 status:** not reached.
- **Lean result landed:** the generic equivalence
  `Erdos177Exponent α ↔ FiniteResiduePrefixBalancingAssumption α` and its exponent-seven
  specialization.
- **New assumption instances:** none.
- **Exact remaining obstruction:** prove uniform finite residue-prefix balancing at some
  `α < 8`; for the proposed milestone, prove it at `α = 7`.
- **Best currently formalized sufficient route:** discharge
  `BarrierPreservingPartialColoringAssumption 7`, or replace it with a weaker reachable/fractional
  invariant and prove that invariant yields the same finite witnesses.

No theorem in C7 claims an unconditional improvement of Beck's exponent.
