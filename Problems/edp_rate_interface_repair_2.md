# EDP-rate second interface repair (A3″)

Status: checked interface design and conditional glue. This memo does **not** prove an
unconditional discrepancy rate. The A7″ and A9″ analytic instances remain open.

## 1. The two new findings

### Finding A-3: the first repaired start was too early

[PR #3803](https://github.com/ProofFleet/moltresearch/pull/3803) gives a kernel-checked
counterexample to `FiniteVanDerCorputRateAssumption .budgeted` as it stood after A3′. At
the concrete outer horizon `x = 10^10`, it proves

```text
edpRateStart < x,
edpAnalysisCutoff x ≤ 2,
8 ≤ edpPersistentWindowLength x ε       (0 < ε ≤ 1).
```

The deterministic Liouville law in that PR satisfies the finite second-moment premise
through the cutoff. Any proposed persistent package would nevertheless require
`1 ≤ X₀` and `X₀ + H ≤ 2`, which is impossible. This obstruction occurs before an Elliott
threshold or a pretentious parameter is used.

### Finding A-2: three scalar caps did not bound the structured terminal scale

[PR #3804](https://github.com/ProofFleet/moltresearch/pull/3804) records the exact A9′
comparison

```text
structuredTerminalScaleOfTCut ... + 1 + H(x, ε) ≤ edpAnalysisCutoff x.
```

The A3′ policy capped `(Q,T,B)`, but A8's terminal constructor still accepted `Xpair` and
`Xzero` as free natural inputs, while its function-form
`structuredTCutThreshold Q T B ...` had no cutoff comparison. The checked counterexample
takes the admissible scalar package `(Q,T,B) = (1,1,0)` and the uncapped input
`Xpair = L + 1`, where `L = edpAnalysisCutoff x`. The terminal maximum is then already
larger than `L` before adding the second event or the A6 window.

## 2. Known

Tao's Proposition 1.11 is an asymptotic tail statement: after the second-moment bound and
accuracy are fixed, the proof chooses a sufficiently large truncation and obtains a
high-probability pretentious description at every later scale. The Borwein--Choi--Coons
argument then chooses a further scale after the pretentious package is fixed. See
[Tao, *The Erdős discrepancy problem*, Proposition 1.11 and Sections 3--4](https://arxiv.org/html/1509.05363v6).

The local finite audits make the hidden ordering quantitative:

- `ElliottThresholds.lean` proves that an A6 window based at `X` touches moments at both
  `X` and `X + H`.
- `StructuredThresholds.lean` defines the A8 function-form t-cut and the joint terminal
  maximum. Its terminal constructor is the maximum of `Xstart`, `Xpair`, `Xzero`, the
  logarithmic and real-power thresholds, `3`, and the ceiling of the t-cut witness.
- The structured probability argument uses pretentious events at `X` and `X + 1`, so the
  finite interface must reserve `X + 1 + H`, not merely `X + H`.

These facts are formalized locally in `windowSndMoment_le_of_two_indices`,
`structuredTerminalScaleOfTCut_spec`, and the obstruction artifacts linked above. The A8
ledger and its cited source analysis are in
[`Problems/edp_rate_structured_thresholds.md`](edp_rate_structured_thresholds.md).

## 3. Conjectured and still open

The logarithmic Erdős discrepancy-rate conjecture remains open. This repair does not prove:

1. a function-form Elliott threshold with the bounds required by A7″;
2. that A7″ produces `K`, `ε`, `X₀`, `Q`, `T`, and `B` below the new caps;
3. cutoff bounds for the actual per-character `Xpair`, modulus-zero `Xzero`, or A8 t-cut
   functions;
4. that the actual A8 joint terminal maximum is admissible; or
5. that the new pointwise large-scale branch eventually occurs, hence that
   `edpBudgetedTripleLogRate` diverges.

Items 1--2 are A7″ obligations, items 3--4 are A9″ obligations, and item 5 belongs to the
final A10 calibration. In particular, `discrepancyRate_of_assumptions` remains conditional
on all three named assumption classes. No theorem in this PR claims the open rate.

## 4. Our idea: make entry into the branch carry the missing inequalities

Everything in this section is an interface proposal, not a statement from Tao's paper.

### 4.1 Cap the probability constant and bound every admissible window

For `L = edpAnalysisCutoff x`, define

```text
Kcap(L) = max(1, log(L + 1)),
εmin(L) = 1 / (4 * (Kcap(L) + 1)),
Xcap(L) = max(1, floor(log₂(L + 1))).
```

An accuracy is admissible when `εmin(L) ≤ ε ≤ 1`. The Lean theorems
`edpAccuracyFloor_pos`, `edpAccuracyFloor_le_one`, and
`edpProbabilityLoss_mul_accuracyFloor_le` check that the range is nonempty and that the
choice `ε = εmin(L)` pays `Kε ≤ 1/4` for every admitted `K ≤ Kcap(L)`.

Since the window length is decreasing in `ε`, its maximum over the complete admissible
range is

```text
Hmax(x) = edpPersistentWindowLength x εmin(L).
```

`edpPersistentWindowLength_le_max` proves this comparison for every admissible `ε`.
The required analysis index is therefore fixed before the package:

```text
R(x) = Xcap(L) + Hmax(x) + 1.
```

The last `+1` is the structured two-event charge.

### 4.2 A source-budget-dependent start

The old constant is retained as `edpRateStart` only so the historical A5/A7/A9 regression
files remain buildable. The active start is

```text
edpBudgetedRateStart(x)
  = max(edpRateStart,
        max(R(x), edpScheduledSourceBudget(R(x)))).
```

The `.budgeted` van-der-Corput and structured classes now open only under the pointwise
condition `edpBudgetedRateStart x < x`. The Fourier class keeps its old positivity premise
because its source-budget payload is independent of endpoint policy; the active premise
implies the old one.

The important point is not the spelling of the maximum but its proved consequence:

```text
edpBudgetedRateStart x < x
  -> R(x) ≤ edpAnalysisCutoff x
  -> X₀ + H(x,ε) + 1 ≤ edpAnalysisCutoff x
```

for every admissible `ε` and every `X₀ ≤ Xcap(L)`. These arrows are the Lean theorems
`edpBudgetedRequiredCutoff_le_analysisCutoff` and
`edpBudgeted_window_fits_of_rateStart_lt`. They follow from the defining
`Nat.findGreatest` source-budget predicate, rather than an asymptotic assertion.

The rate used by the repaired glue is correspondingly

```text
edpBudgetedTripleLogRate(x) =
  1                                      if x ≤ edpBudgetedRateStart(x),
  10^-7 (log log log x)^(1/500)         otherwise.
```

On the second branch it is definitionally the same analytic formula as the A5′ rate.
`edpTripleLogRate_eq_budgeted_of_rateStart_lt` performs the bridge needed by the unchanged
Fourier moment construction.

### 4.3 Function-form structured caps and the joint maximum

The repaired interface exposes three new cutoff functions:

```text
XpairCap(L) = Xcap(L),
XzeroCap(L) = Xcap(L),
tCutCap(L)  = max(0, log(L + 1)).
```

For proposed function-form witnesses `(Xpair,Xzero)` and the actual A8 value
`structuredTCutThreshold Q T B ...`, `BudgetedStructuredThresholdsAdmissible` requires all
three individual comparisons. These are cofinal caps: a fixed witness is eventually
admitted. They prevent a witness from being enlarged after the endpoint is known.

Individual comparisons still do not control the nonlinear logarithmic and real-power
thresholds in `structuredTerminalScaleOfTCut`. The interface therefore names the exact
joint charge

```text
edpStructuredTerminalMaximum(...)
  = structuredTerminalScaleOfTCut(...) + 1 + H(x,ε)
```

and requires the base terminal scale to lie below

```text
edpStructuredTerminalCap(x,ε) = L - (1 + H(x,ε)).
```

This final comparison is intentionally explicit rather than inferred from the three
individual caps. It is the real quantitative A9″ obligation. The theorem
`edpStructuredTerminalMaximum_le_cutoff_of_admissible` proves the complete terminal fit for
every admissible data package. `BudgetedFinitePersistentPretentious` carries the same
universal terminal-fit projection, so a future structured consumer does not rely on an
unstated endpoint convention.

## 5. Why neither obstruction reproduces

### A7′ / Finding A-3

The old proof applies the active class at `x = 10^10` using only
`edpRateStart < 10^10`. That is no longer the class premise. From the new premise, Lean
proves

```text
3 ≤ edpAnalysisCutoff x
```

in `three_le_edpAnalysisCutoff_of_budgetedRateStart_lt`. PR #3803 proves the cutoff at its
test point is at most `2`, so it cannot supply the new premise. More strongly, the theorem
`edpBudgeted_window_fits_of_rateStart_lt` already supplies the precise
`X₀ + H + 1 ≤ L` inequality for every admissible schedule. The Liouville law does not
create a contradiction once entry to the branch is refused at the undersized cutoff.

### A9′ / Finding A-2

The old checked counterexample sets `Xpair = L + 1`. For every active cutoff, Lean proves

```text
XpairCap(L) ≤ L,
```

so this value violates the first conjunct of
`BudgetedStructuredThresholdsAdmissible`. The theorem
`not_budgetedStructuredThresholdsAdmissible_cutoff_add_one` checks that exact rejection.
An arbitrary t-cut witness likewise has to prove its comparison with `tCutCap(L)`, and all
accepted witnesses must prove the named joint terminal comparison. Thus the previous
theorem that `(Q,T,B)` caps alone do not force a fit remains a true historical observation,
but it no longer targets the active interface, which has strictly more premises.

## 6. Checked composition and next obligations

The active graph is now

```text
source-budget-safe Fourier law
  -> finite moments through L
  -> A7″ under the schedule-dependent branch premise
  -> budgeted persistent package with ε, X₀ and terminal slack
  -> A9″ using admissible function-form structured witnesses
  -> contradiction
  -> HasDiscrepancyRateBy edpBudgetedTripleLogRate.
```

`FiniteFourierBudget.lean` rechecks the Fourier instance at every active scale, and
`discrepancyRate_of_assumptions` rechecks the conditional composition. A7″ must now prove
the caps and build the persistent estimate. A9″ must expose the actual `Xpair` and `Xzero`
functions, prove their individual caps together with the A8 t-cut cap, and prove the joint
terminal cap. If either package cannot do so, that is a new quantitative obstruction rather
than permission to weaken the interface silently.

## References

- Terence Tao, [*The Erdős discrepancy problem*](https://arxiv.org/abs/1509.05363),
  Discrete Analysis 2016:1, especially Proposition 1.11 and Sections 2--4.
- [PR #3803: A7′ finite van der Corput obstruction](https://github.com/ProofFleet/moltresearch/pull/3803).
- [PR #3804: A9′ finite structured obstruction](https://github.com/ProofFleet/moltresearch/pull/3804).
- [`Problems/edp_rate_elliott_thresholds.md`](edp_rate_elliott_thresholds.md).
- [`Problems/edp_rate_structured_thresholds.md`](edp_rate_structured_thresholds.md).
- [`Problems/edp_rate_fourier_redesign.md`](edp_rate_fourier_redesign.md).
