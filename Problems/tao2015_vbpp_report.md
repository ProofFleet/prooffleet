# Track R — V-B′/V-B″ + V-C4-4: Codex runs 25–26 final reports (2026-09-07)

Run 25 (brief `Problems/tao2015_vbprime_brief.md`) committed the height-indexed record `ZeroFreeRegionDataH θ m` (a `Type`-valued record with the
free constants `η₀`, `M₀`; width `min η₀ (log 2Z)^{−θ}`, bound `max M₀ (log 2Z)^m` at height `Z`) and the Mellin shift at height `8πT + √P`, then
stopped with a correct counterexample to the brief's two-regime envelope (Finding V-2). Run 26 (brief `Problems/tao2015_vbpp_brief.md`)
completed V-B″: the balanced height `zeroFreeRegionHeightHMax θ T P = max(8πT, exp((log P)^{1/(1+θ)}))`, the sharpened regular-part exponent
`m = 1/a + 1/10` (`zeta_regular_logDeriv_bound_of_growth_sharp`, via the honest disc growth budget, the 3-4-1 lower bound and Borel–Carathéodory),
the three-regime envelope (`exists_balanced_long_error_envelope`, thresholds recorded; Regime II splits at `y < q/6`), the theorem
`prime_large_values_bound_of_zeroFreeRegionDataH'` and its compositions `primeLargeValues_of_zeroFreeRegionH`, `trackR_edp_of_zeroFreeRegionH`;
then **V-C4-4** (`zeroFreeRegionDataH_of_growth`: the compactness step `exists_zeta_compact_strip_data` for small heights, the width comparison
`(log 2Z)^{−(1/a+1/100)} ≤ d(loglog 2Z)^{1/a−1}/(log 2Z)^{1/a}` above) and the final compositions **`primeLargeValues_of_zetaGrowth`** and
**`trackR_edp_of_zetaGrowth`** — the Erdős discrepancy theorem conditional only on a growth bound `log‖ζ(σ+it)‖ ≤ B(1−σ)^a log|t| + b loglog|t| + B₀`
— pinned. Verbatim reports follow (run 25, then run 26).

---

# Track R — V-B′ / V-C4-4 report

## Outcome

V-B′-1 and V-B′-2 are implemented and committed.  Work stopped before
V-B′-3 under the brief's stop rule: the proposed Regime II envelope has an
unbounded-factor obstruction for every admissible `κ` at the endpoint
`theta = 5/7 + 1/100`, `theta' = 31/40`.  Consequently V-C4-4 and the
Conjectures compositions were not asserted.

The design-report headings named in the brief were not present in this
worktree's `origin/main`; the reproduced Finding V-1 in the brief and the
existing `CODEX_REPORT_vc4.md` were used as the design source.

## Commits

- `a0ab39ce` — `Track R: add height-indexed zero-free data (#3044, V-B′-1)`
- `64e7d16c` — `Track R: rerun the Mellin shift at square-root height (#3044, V-B′-2)`

No push, merge, or rebase was performed.

## Compiled V-B′ interfaces

Lean does not permit real-valued fields in a structure whose sort is
`Prop`.  The repaired two-parameter record is therefore a data structure in
`Type`:

```text
ZeroFreeRegionDataH (theta m : R)
```

It contains `theta_pos`, `eta0`, `0 < eta0`, `eta0 <= 1/2`, `M0`,
`1 <= M0`, and the pointwise-in-height `zero` and `reg` fields with

```text
eta(Z) = min eta0 (log(2Z))^(-theta)
M(Z)   = max M0 (log(2Z))^m.
```

The V-B′-2 wrapper compiles V-A at

```text
Z = 8*pi*T + sqrt(P)
```

and obtains its zero-free and regular-part hypotheses from the record at
that same `Z`.

## Finding: the V-B′-3 envelope is false as stated

Write

```text
x = log P,
y = log(2T),
theta = 5/7 + 1/100,
theta' = 31/40.
```

For every admissible positive `κ`,

```text
theta * (1 + κ) < theta'
```

implies

```text
theta/theta' < 1/(1 + κ).
```

Also `1 - theta < theta/theta'`.  Choose any fixed

```text
1 - theta < q < theta/theta'.
```

(then automatically `q < 1/(1+κ)`), and let `x -> infinity` along natural
`P` with

```text
y = x^q,   T = exp(y)/2.
```

This is Regime II because

```text
y^(1+κ) = x^(q(1+κ)) < x.
```

Since `q < 1`, the square-root term dominates the rectangle height:

```text
Z = 8*pi*T + sqrt(P),
log(2Z) = x/2 + O(1),
eta(Z) = (log(2Z))^(-theta) asymptotically.
```

Thus the main contour term, after division by `P`, has size at least a
constant multiple on the logarithmic scale of

```text
exp(-C * x^(1-theta)).
```

The proposed envelope after division by `P` is

```text
C' * (1/(2T+1) + exp(-x/y^theta') * y^2)
 = C' * (O(exp(-x^q))
          + exp(-x^(1-q*theta')) * x^(2q)).
```

Both terms are smaller by an unbounded factor:

- `q > 1-theta`, so `exp(-x^q) / exp(-C*x^(1-theta)) -> 0`;
- `q < theta/theta'`, so `1-q*theta' > 1-theta`, hence
  `x^(2q) * exp(-x^(1-q*theta') + C*x^(1-theta)) -> 0`.

Equivalently, the ratio of the main V-A error to the entire claimed
right-hand envelope tends to infinity.  The free constants `eta0` and `M0`
do not change this: for large `x` the logarithmic width is below `eta0`, and
`M(Z) >= M0 >= 1`.

The sign error in the brief occurs at

```text
(log(2T))^theta' < (log P)^(theta'/(1+κ)).
```

This implies

```text
exp(-log P/(log(2T))^theta')
  < exp(-(log P)^(1-theta'/(1+κ))),
```

whereas the proposed Regime II argument needs the reverse inequality.

This obstruction applies to every admissible `κ`, because the interval for
`q` above remains nonempty and lies below `1/(1+κ)`.  It is therefore the
brief's explicit stop condition, not a missing Mathlib compactness fact.

## Repair options

The height-indexed record itself is sound, but the target `T`-envelope needs
different bookkeeping.  Viable directions include:

1. use a contour height adapted to both variables, rather than a fixed
   positive power of `P` (for example make the added height track the target
   exponential scale); or
2. weaken the target in the intermediate range
   `(log P)^(1-theta) << log T << (log P)^(theta/theta')`; or
3. supply an additional analytic input that improves the zero-free saving
   in that range.

Merely changing `κ` cannot repair the stated envelope.

## Verification

After the stop-rule cleanup:

- `lake env lean MoltResearch/Discrepancy/PrimeLargeValuesFromRegionH.lean`:
  passed.
- `./scripts/forbid_sorry.sh`: passed.
- `./scripts/forbid_axiom_unsafe.sh`: passed.
- `./scripts/check_layering.sh`: passed.
- `python3 scripts/check_aggregator_coverage.py`: 200 modules, 198 reachable;
  only the two existing allowlisted example modules remain outside the graph.
- `lake build MoltResearch.DiscrepancyAnalytic Conjectures`: 8347 jobs,
  passed.
- `#print axioms
  MoltResearch.exists_primeMellin_kernel_bound_of_zeroFreeRegionDataH`:
  only `propext`, `Classical.choice`, and `Quot.sound`.

The branch finished nine commits ahead of and three commits behind the
moving `origin/main`; it was deliberately left unre-based.

---

# Track R — V-B″ / V-C4 run 26 report

All requested statements compile without `sorry`, new axioms, or `unsafe`.

## Commits

- `f3a651a2` — balanced Mellin height (V-B″-1)
- `f40be985` — sharp regular zeta exponent (V-C4-3′)
- `e393e448` — three-regime envelope and H bridge (V-B″-2)
- `66668f4e` — growth to height-indexed data (V-C4-4)
- `12425283` — zeta-growth compositions

All commits carry the run-26 session line and required co-author trailer.
Nothing was pushed, merged, or rebased.

## Analytic results

`zeroFreeRegionHeightHMax theta T P` is
`max (8*pi*T) (exp ((log P)^(1/(1+theta))))`.
The max-height kernel evaluates both `eta(Z)` and `M(Z)` at that height.

`zeta_regular_logDeriv_bound_of_growth_sharp` proves the requested
`C*(log |t|)^(1/a+1/10)` estimate using the honest disc growth budget,
the 3-4-1 lower bound, and Borel–Carathéodory.

The record bound is `max M0 (log 2Z)^m`, so a fixed coefficient cannot be
absorbed at the same exponent. The companion half-slack theorem proves
`C*(log |t|)^(1/a+1/20)`; the eventual unit-coefficient theorem spends the
remaining `1/20` and lands exactly at `m = 1/a+1/10`.

## Three-regime thresholds

`exists_balanced_long_error_envelope` records:

- `x0,C` from the raw balanced-contour bound;
- `cI = log(8*pi)`, `y1` from shifted-power absorption, and
  `YI = max y1 |cI|` for Regime I;
- `beta = 1+theta-theta'`, thresholds `qexp` and `qpoly`, and
  `Q = max 1 (max (2*log 2) (max qexp qpoly))` for Regime II;
- bounded Regime-II height `B = (Q^(1+theta))^(1/theta')`;
- `DI = (exp YI+1)*C*(YI+|cI|)^2`,
  `DII = (exp B+1)*C*(Q+log 2)^2`, and
  final `D = 1+DI+DII+100*C`.

The trivial/transition constant is
`1+12*exp 1+3*(exp (x0^(1/theta'))+1)*x0`.
Regime II splits at `y < q/6` (rather than the sketch's `q/3`) so the
remaining exponential absorbs the `q^2` factor.

The final analytic theorem is
`prime_large_values_bound_of_zeroFreeRegionDataH'`.
Its stable compositions are `primeLargeValues_of_zeroFreeRegionH` and
`trackR_edp_of_zeroFreeRegionH`.

## Growth-to-record compactness

`exists_zeta_compact_strip_data` separates the compact segment `Re=1`
from the closed zero set of the entire pole-removed zeta function. This gives
a positive strip width and a compact bound for its analytic regular
logarithmic derivative.

Above that height, `exists_record_width_le_growth_model` proves

```text
(log (2Z))^(-(1/a+1/100))
  <= d * (log (log (2Z)))^(1/a-1) / (log (2Z))^(1/a).
```

`growth_model_le_zetaGrowthWidth` transfers this model to every
`|Im z| <= Z`. The compiled record is
`ExpSums.zeroFreeRegionDataH_of_growth`, with exact exponents
`theta=1/a+1/100` and `m=1/a+1/10`.

Because `ZeroFreeRegionDataH` is Type-valued while the analytic existence
results are propositions, the proof first gives
`nonempty_zeroFreeRegionDataH_of_growth`; the named record is its
noncomputable classical choice.

The final compositions are `primeLargeValues_of_zetaGrowth` and
`trackR_edp_of_zetaGrowth`. Their axiom pins report only
`propext`, `Classical.choice`, and `Quot.sound`.

## Verification

Passed:

- `./scripts/forbid_sorry.sh`
- `./scripts/forbid_axiom_unsafe.sh`
- `./scripts/check_layering.sh`
- `python3 scripts/check_aggregator_coverage.py`
- `~/.elan/bin/lake build MoltResearch.DiscrepancyAnalytic Conjectures`

The final build completed successfully with 8354 jobs. Aggregator coverage
reports 205 modules, 203 reachable, plus the two existing allowlisted
compile-excluded example modules.

`TrackCAxiomAudit.lean` was not edited because repository contribution
rules protect it; the run-26 pins are in the new composition leaves instead.
`CODEX_REPORT.md` remains uncommitted as requested.
