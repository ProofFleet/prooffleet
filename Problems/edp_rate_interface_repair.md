# EDP-rate finite-endpoint interface repair (A3′)

Status: interface design and checked conditional glue. This memo does **not** prove an
unconditional discrepancy rate. The analytic A7′ and A9′ instances remain open.

## 1. Finding A-1

The A3 interface put two different asymptotic ideas at the same last finite index

```text
L = edpAnalysisCutoff x.
```

The van-der-Corput leg needed moments through `X + H` but asked for its conclusion through
`X = L`. The structured leg was allowed to choose `(Q,T,B,X₀)` after seeing `L`, so it could
take `X₀ = L` and enlarge `B` until the only event had probability one. These are the two
faces of one defect: after the analytic package was fixed, the interface left no later scale
at which to consume it.

The checked records are:

- [PR #3791](https://github.com/ProofFleet/moltresearch/pull/3791), whose
  `finiteVdCWindowScheduleFits_false` specializes the requested interval at `X = L` and
  obtains the impossible inequality `L + H ≤ L` with `1 ≤ H`;
- [PR #3794](https://github.com/ProofFleet/moltresearch/pull/3794), whose
  `finitePersistentPretentious_of_one_le_cutoff` takes `X₀ = L`, `Q = T = 1`, and the
  sample-independent universal finite-distance bound as `B`.

## 2. Known

Tao's Proposition 1.11 starts with a second-moment bound at all natural indices. For every
positive error and all sufficiently large truncations, it obtains a high-probability
pretentious description with the character, frequency, and distance bounds depending on
the moment bound and error. The subsequent generalized Borwein--Choi--Coons argument is run
at a still later scale. This is an asymptotic tail statement, not a statement about one final
endpoint. See [Tao, *The Erdős discrepancy problem*, Proposition 1.11 and Sections 3--4](https://arxiv.org/html/1509.05363v6).

The local A6 ledger proves a sharper finite fact:

```text
a window based at X and of length H touches moments X and X + H.
```

This is kernel-checked by `windowSndMoment_le_of_two_indices`,
`mem_elliottWindow_moment_indices`, and the two cutoff-local Elliott-window theorems in
`ElliottThresholds.lean`. Thus the endpoint available to the pretentious conclusion must be
at most `L - H`; changing a strict inequality or increasing a fixed `L` cannot repair the
old `X = L` call.

A8 also makes the structured dependence visible. Its
`structuredTerminalScaleOfTCut Q T B ...` is selected only after the package
`(Q,T,B,...)` is fixed. Any finite interface must therefore establish that this dependent
terminal scale lies in the remaining interval. Finiteness alone gives no such comparison;
see `Problems/edp_rate_structured_thresholds.md`.

## 3. Conjectured and still open

The Erdős discrepancy-rate conjecture remains open. In particular, this repair does not
establish any of the following:

1. that the finite Elliott/van-der-Corput proof produces parameters below the new caps;
2. that its chosen accuracy leaves a nonempty window below the source-budget cutoff;
3. that A8's terminal scale fits below the shortened endpoint uniformly for every admissible
   parameter package; or
4. that `HasDiscrepancyRateBy edpTripleLogRate` holds without the three named assumption
   classes.

Those are exactly the A7′ and A9′ obligations. The theorem
`discrepancyRate_of_assumptions` remains conditional and keeps the A5′ rate

```text
10^-7 * (log log log x)^(1/500)
```

above `edpRateStart`.

## 4. Our idea: a budgeted endpoint policy

This section is our interface design, not a claim from the cited literature.

### 4.1 One accuracy sufficient for the contradiction

The qualitative statement quantifies over every error `ε`. A finite contradiction needs one
accuracy with positive probability after the probability constant `K` is known. The repaired
target therefore asks for one `ε` satisfying

```text
0 < ε ≤ 1,        K * ε ≤ 1/4.
```

This is weaker than the full qualitative tail, but is the exact finite information consumed
by the structured two-event argument. The weakening is explicit in the definition and only
changes an open assumption interface; the conclusion of the conditional glue theorem is not
weakened.

### 4.2 Reserve the A6 window before choosing pretentious parameters

For the second-moment cap `C(x) = edpTripleLogRate x ^ 2 + 1`, define

```text
H(x, ε) = max 1 ⌈8 * max(C(x), 1) / ε⌉₊.
```

This is definitionally the A6 choice `edpVdCWindowLength C(x) ε`, stated in
`Reduction.lean` to avoid an import cycle. A budgeted package must choose `X₀` with

```text
1 ≤ X₀,           X₀ + H(x, ε) ≤ L,
```

and supplies its probability estimate at every `X` satisfying

```text
X₀ ≤ X,           X + H(x, ε) ≤ L.
```

Thus the last permitted base scale is exactly `L - H(x,ε)`, and every moment used by A6 is
within the Fourier cutoff. `one_le_edpPersistentWindowLength` and
`budgetedFinitePersistentPretentious_has_slack` check the nonzero slack in Lean.

### 4.3 Fix cofinal caps before the package

At cutoff `L`, the interface fixes

```text
Qcap(L) = max(1, log(L + 1)),
Tcap(L) = max(1, log(L + 1)),
Bcap(L) = max(0, (1/4) log log(L + 3)).
```

The van-der-Corput package must then provide

```text
1 ≤ Q ≤ Qcap(L),
1 ≤ T ≤ Tcap(L),
0 ≤ B ≤ Bcap(L).
```

All three cap functions have unbounded range as `L → ∞`; hence each fixed qualitative
package is eventually admitted. Their values at a given cutoff are fixed before `(Q,T,B)`
is selected. In particular, `B` can no longer be enlarged after seeing the final endpoint.

The precise cap growth is a calibration choice. If A7′ proves different explicit parameter
bounds, these functions may be slowed or accelerated together with the analysis schedule,
but they must stay fixed functions with unbounded range. Replacing a cap by an unrestricted
existential would recreate Finding A-1.

### 4.4 Policy indexing and compatibility

`FiniteEndpointPolicy` has two constructors:

- `.historical` is the original A3 proposition. It remains the default only so the merged
  A7/A9 obstruction artifacts continue to compile as regression records.
- `.budgeted` is the repaired proposition above. The three active classes and
  `discrepancyRate_of_assumptions` explicitly use this policy.

The policy index prevents a historical instance or obstruction from being used accidentally
in the repaired proof. The Fourier class has the same mathematical payload under either
policy because source-budgeted moment construction does not inspect pretentious parameters.
`FiniteFourierBudget.lean` nevertheless installs a fresh `.budgeted` instance, rather than
letting the historical typeclass cross the boundary implicitly.

## 5. Why the two obstruction proofs do not reproduce

### A7 endpoint theorem

The theorem `edpVdC_endpoint_window_does_not_fit` remains true: no positive window fits when
based at `X = L`. It no longer attacks the active target because `X = L` is not admissible.
For a `.budgeted` witness, Lean exposes

```text
X + edpPersistentWindowLength x ε ≤ L
```

and proves the window length is at least one. Substituting `X = L` contradicts witness
admissibility before any probability estimate is considered. A7′ must instead construct its
package on the shortened interval and prove that its selected `ε` makes that interval
nonempty.

### A9 automatic finite package

The historical proof makes two endpoint moves that are unavailable:

1. `X₀ = L` violates `X₀ + H(x,ε) ≤ L` because `1 ≤ H(x,ε)`.
2. Setting `B` to `2 * ∑_{p<L} 1/p` does not supply the new obligation
   `B ≤ Bcap(L)`.

The old theorem therefore remains a theorem only about `.historical`. It cannot inhabit the
`.budgeted` target required by `FiniteBorweinChoiCoonsRateAssumption .budgeted`.

For A9′, negating the existential budgeted target means handling every package satisfying
the displayed cap inequalities. After destructing such a package, the proof must choose the
A8 terminal scale and establish

```text
structuredTerminalScaleOfTCut ... + H(x, ε) ≤ L
```

(with the extra `+1` needed by the two-event call accounted for). This is now a real,
visible comparison. It cannot be bypassed by choosing a one-point interval.

## 6. Checked composition

The active dependency graph is

```text
FiniteFourierReductionAssumption .budgeted
  -> finite second moments through L
  -> FiniteVanDerCorputRateAssumption .budgeted
  -> BudgetedFinitePersistentPretentious
  -> contradiction with FiniteBorweinChoiCoonsRateAssumption .budgeted
  -> HasDiscrepancyRateBy edpTripleLogRate.
```

`discrepancyRate_of_assumptions` kernel-checks this composition. The small-`x` one-term
argument and the large-`x` contradiction are unchanged. The A5′ spectral construction is
re-exported as `finiteFourierReductionAssumption_budgetSafe` at the `.budgeted` policy.

## 7. Next proofs

### A7′

- identify the A6 probability constant `K` and choose one explicit `ε` with
  `Kε ≤ 1/4`;
- prove `edpVdCWindowLength C(x) ε = edpPersistentWindowLength x ε`;
- prove the chosen `X₀` and full shortened interval fit below `L`;
- extract explicit `Q,T,B` estimates and prove the three cap inequalities.

### A9′

- destruct the budgeted witness, retaining every cap and endpoint-fit proof;
- make A8's per-character `Xpair` and modulus-zero `Xzero` thresholds function-form;
- bound the worst terminal scale over all admissible `(Q,T,B)` by `L-H-1`;
- run the two-event structured contradiction only at scales certified inside the shortened
  interval.

If either terminal comparison fails for the current cutoff, that is a schedule-calibration
failure to report explicitly. It is not permission to remove the cap or restore `X = L`.

## References

- Terence Tao, [*The Erdős discrepancy problem*](https://arxiv.org/abs/1509.05363),
  Discrete Analysis 2016:1, especially Proposition 1.11 and Sections 2--4.
- A7 obstruction record, [PR #3791](https://github.com/ProofFleet/moltresearch/pull/3791).
- A9 obstruction record, [PR #3794](https://github.com/ProofFleet/moltresearch/pull/3794).
- `Problems/edp_rate_elliott_thresholds.md` (A6 moment ledger).
- `Problems/edp_rate_structured_thresholds.md` (A8 terminal-scale ledger).
- `Problems/edp_rate_fourier_redesign.md` (A5′ source-budget-safe cutoff).
