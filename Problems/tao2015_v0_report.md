# Track R — V-0: Codex run 18 final report (2026-09-06)

Verbatim final report of Codex run 18 (gpt-5.6-sol, brief `Problems/tao2015_v0_brief.md`), whose two non-empty commits shipped as the V-0 PR.
V-0 makes `PrimeLargeValuesAssumption` honest — an existential constant `C ≥ 1` and the named exponent `primeLargeValuesExponent = 4/5`
(`[MR]` Lemma 8 has an `ε`-dependent implied constant and the exponent `2/3 + ε`) — and threads the witness `Cp` through the band,
schedule, exceptional-set and L3 chain; the statements of `sliceMeanSquareA2`, `trackR_edp`, `trackR_edp_halasz` and their pins are
unchanged. Commit hashes are the run's, before cherry-pick.

---

# CODEX REPORT — Track R V-0

## Result

Track R V-0 is complete.  The prime large-values interface now states an
honest existential-constant estimate with the named exponent
`primeLargeValuesExponent = 4 / 5`.  Its consumers choose that witness once in
`sliceMeanSquareA2` and pass `Cp`, `1 ≤ Cp`, and the corresponding bound through
the full band, schedule, exceptional-set, and L3 closure chain.

No public theorem was weakened.  In particular, the statements of
`sliceMeanSquareA2`, `trackR_edp`, and `trackR_edp_halasz` are unchanged, and
the five requested public declarations retain their exact axiom sets.

No `PrimeLargeValuesAssumption` instance was added.  The actual analytic
discharge remains Phase 6 work.

## Commits

1. `31585cd7 Track R: make the prime large-values interface honest (#3044, V-0-1)`
2. `90a345fb Track R: thread the prime large-values witness (#3044, V-0-2)`
3. `f9a0dc49 Track R: verify the public axiom pins (#3044, V-0-3)`

The V-0-3 commit is intentionally empty: the repository's existing exact
guards in `TrackCAxiomAudit.lean` already covered all five requested
declarations, and the contribution rules prohibit editing that audit file in
lane work.

Every commit contains the requested session/run link and `Co-Authored-By`
trailer.  Nothing was pushed, merged, or rebased.

## V-0-1: interface and source transcription

`Interfaces/LargeValues.lean` now defines

```lean
/-- The exponent of the prime large-values saving: Chudakov's region
`1 - c / ((log t)^(3/4) (loglog t)^(3/4))` beats `(log t)^(-4/5)`. -/
noncomputable def primeLargeValuesExponent : ℝ := 4 / 5
```

and the class field has the form

```lean
class PrimeLargeValuesAssumption : Prop where
  bound : ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : ℕ) (Y : Finset ℕ),
    (∀ p ∈ Y, p.Prime) →
    (∀ p ∈ Y, P ≤ p ∧ p ≤ 2 * P) →
    ∀ (a : ℕ → ℂ) (T : ℝ) (𝒯 : Finset ℝ),
      2 ≤ P →
      1 ≤ T →
      (∀ t ∈ 𝒯, |t| ≤ T) →
      (∀ t ∈ 𝒯, ∀ u ∈ 𝒯, t ≠ u → 1 ≤ |t - u|) →
      ∑ t ∈ 𝒯,
          ‖∑ p ∈ Y, (a p / (p : ℂ)) *
            ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖ ^ 2
        ≤ C *
            (1 + (𝒯.card : ℝ) *
              Real.exp (-(Real.log P /
                (Real.log (2 * T)) ^ primeLargeValuesExponent)) *
              (Real.log (2 * T)) ^ 2) *
            (∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2) *
            (P : ℝ) / Real.log P
```

The class documentation records the `[MR]` source, the existential constant,
the fixed exponent below one, and the absence of an instance before Phase 6.
`Problems/sources/tao2015_statements.md` now accurately transcribes the
epsilon-dependent implied constant and exponent `2/3 + ε`, and explains the
formal `Cp`/`4/5` specialization.

## V-0-2: witness flow

The universal body of the field is exposed as the proposition
`PrimeLargeValuesBound Cp`.  The final proof chooses the class witness once:

```lean
obtain ⟨Cp, hCp1, hprimeBound⟩ :=
  PrimeLargeValuesAssumption.bound
```

All intermediate consumers take these data explicitly:

- `Cp : ℝ`;
- `hCp1 : 1 ≤ Cp`;
- `hprime : PrimeLargeValuesBound Cp` where the analytic estimate is invoked.

Consequently the prime part of the band-energy estimate is multiplied by
`Cp`, every re-cut `Γ` uses `primeLargeValuesExponent`, and the schedule and L3
fit hypotheses carry the same fixed witness.  The public endpoint statements
do not expose `Cp`.

## New exponent and L3 margins

Write `X = log A₁` and `θ = primeLargeValuesExponent = 4/5`.  From the existing
prime-window and time-height bounds,

```text
log Pc ≥ X^(49/50) / 2,
log (2T) ≤ 3X.
```

Since `0 ≤ θ ≤ 1`, the formal proof bounds

```text
(log (2T))^θ ≤ (3X)^θ ≤ 3 X^θ.
```

Thus the exponential damping exponent has the lower bound

```text
log Pc / (log (2T))^θ
  ≥ X^(49/50 - 4/5) / 6
  = X^(9/50) / 6.
```

The moment loss costs `X^(1/50)`, leaving the positive exponent margin

```text
9/50 - 1/50 = 8/50 = 4/25.
```

The scalar closure is therefore recast around

```text
W^2 / 100 ≤ exp ((4/25) W),
```

under the retained explicit threshold

```text
100 * (11880 * (C + 2)) ≤ log X.
```

This proves the required `Γ ≤ 1` estimates at exponent `4/5`; no numerical
obstruction occurred.

After `Γ ≤ 1`, the per-cell prime contribution is

```text
8 * Cp * Ccells * N * R * d^2 * E.
```

The existing `/192` allocation produces coefficient `1536 * Cp`; the `/64`
ratio produces `512 * Cp`; and the sixfold short-slice envelope produces
`3072 * Cp`.  These factors are absorbed into the exceptional prime
coefficient, `ε'`, the exceptional budget denominator, the ladder parameter,
and the final height constant.  This is precisely where the formerly hard
coded prime constant entered the L3 closure.

## Changed sites

The following is the complete source-file inventory across V-0-1 and V-0-2.

### Interface and source record

- `Conjectures/C0002_erdos_discrepancy/src/Interfaces/LargeValues.lean` — named
  exponent, existential witness, `PrimeLargeValuesBound`, and documentation.
- `Problems/sources/tao2015_statements.md` — corrected `[MR]` Lemma 8
  transcription and formalization note.

### Prime energy, re-cut, capstone, and schedules

- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5BandEnergyExceptional.lean`
  — consumes the supplied bound; prime coefficient is `Cp`.
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5ExceptionalReCut.lean`
  — re-cut `Γ` uses the named exponent and `Cp`.
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5BandEnergyExceptionalReCut.lean`
  — threads the revised re-cut data.
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5BandCapstone.lean`
  — passes `Cp` through the capstone and declares its direct constants import.
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5BandCapstoneFamily.lean`
  — threads `Cp` through the family form.
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5InnerBandAssembly.lean`
  — threads the prime witness through assembled bands.
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5InnerBandSchedule.lean`
  — updates schedule hypotheses and calls.
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5InnerBandScheduleSharp.lean`
  — updates the sharp schedule.
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5InnerBandScheduleSharpFit.lean`
  — updates sharp-fit hypotheses and declares its direct scale import.
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5InnerBandScheduleSharpCells.lean`
  — threads `Cp` through cell schedules.
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5InnerBandScheduleSharpCellsWide.lean`
  — threads `Cp` through wide cell schedules.
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5InnerBandScheduleSharpCellsWideShifted.lean`
  — threads `Cp` through shifted wide schedules.

### Prime fit and ladder numerology

- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5ExceptionalPrimeFit.lean`
  — reproves `Γ ≤ 1` with the named `4/5` exponent and the `4/25` residual
  margin.
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5LadderNumerology.lean`
  — propagates the `Cp`-dependent exceptional coefficient.
- `MoltResearch/Discrepancy/ExceptionalConstants.lean` — generalizes the
  existing exceptional-ratio threshold lemma from the literal exponent to an
  arbitrary exponent `θ < 1`; no new nucleus lemma or file was introduced.

### Slice A2 exceptional and factor-two chain

- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2ExceptionalAggregate.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2ExceptionalAggregateClose.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2ExceptionalAggregateMargins.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2ExceptionalDeltaClose.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2ExceptionalFit.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2ExceptionalLadderBudget.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2ExceptionalPrime.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2ExceptionalPrimeEnvelope.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2ExceptionalRankinBasic.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2ExceptionalRankinDecay.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2ExceptionalRankinExpTail.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2ExceptionalRankinTail.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2ExceptionalSharpBound.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2FactorTwoAggregate.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2FactorTwoGamma.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2FactorTwoTail.lean`

These files thread `Cp`, replace the prime `64` allocations by the derived
`1536 * Cp`, `512 * Cp`, and `3072 * Cp` coefficients as appropriate, and
absorb the fixed witness into the exceptional fit and budget parameters.

### Slice A2 closure and public endpoint

- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2BottomPowerClose.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2Bump.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2Final.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2HeightChoice.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2InnerClose.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2InnerSchedule.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2JointLowRemainder.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2MeanSquareClose.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2MomentClose.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2MomentGamma.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2MomentScalar.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2OneSliceClose.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2OrdinaryParameterBounds.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2ParameterBounds.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5SliceA2UniformAggregate.lean`

These files carry the revised parameters through the remaining L3 leaves and
choose the existential witness inside `sliceMeanSquareA2`.  The bump leaf also
declares its direct `BumpDeriv` import, exposed by removal of a transitive
aggregate import earlier in the chain.

## Import-boundary findings

Removing the pre-existing aggregate import from
`TrackCStage5BandEnergyExceptional.lean` exposed three transitive dependency
leaks.  They were repaired with narrow direct imports:

- `TrackCStage5BandCapstone.lean` directly imports `ExceptionalConstants`;
- `TrackCStage5InnerBandScheduleSharpFit.lean` directly imports
  `MajorArcBlockScale`;
- `TrackCStage5SliceA2Bump.lean` directly imports `BumpDeriv`.

No analytic aggregate was introduced into a conjecture/task leaf, and no new
leaf registration was needed because V-0 added no new nucleus lemma.

## V-0-3: exact axiom pins

Direct compilation of `TrackCAxiomAudit.lean` confirms that each requested
declaration has exactly

```text
[propext, Classical.choice, Quot.sound]
```

as its axiom set:

- `edp_of_sliceMeanSquareA2`;
- `theorem18_of_sliceMeanSquareA2`;
- `sliceMeanSquareA2`;
- `trackR_edp`;
- `trackR_edp_halasz`.

## Verification

- `~/.elan/bin/lake env lean <file>` passed for every touched Lean file: 47
  source files across V-0-1 and V-0-2.
- `~/.elan/bin/lake env lean Conjectures/C0002_erdos_discrepancy/src/TrackCAxiomAudit.lean`
  passed.
- `~/.elan/bin/lake build MoltResearch.DiscrepancyAnalytic Conjectures` passed:
  `Build completed successfully (8338 jobs).`
- `./scripts/check_layering.sh` passed: `check_layering: OK`.
- `python3 scripts/check_aggregator_coverage.py` passed: 192 modules, 190
  reachable, with only the two existing allowlisted example-file warnings.
- The prohibited-token scan under `MoltResearch/` and `Solutions/` passed.
- The no-added-assumption-instance scan passed.
- The protected-file scan passed: no listed protected nucleus file changed.
- The no-analytic-aggregate-import scan for conjecture/task leaves passed.
- The diff scan found no newly added literal `(3 / 4 : ℝ)` and no added line
  coupling the prime estimate to `64`.
- `git diff --check` passed before report creation.

The remaining literal `3/4` occurrences in
`TrackCStage5SliceA2HeightChoice.lean` are unchanged height-choice exponents,
paired with `1/4`; they are not the prime large-values decay exponent.

## Work left and repository state

There is no V-0 numerical blocker.  Phase 6 must still construct the genuine
analytic `PrimeLargeValuesAssumption` instance; V-0 deliberately adds none.

During the run, `origin/main` advanced independently.  In accordance with the
brief, the branch was left untouched: no pull, rebase, merge, or push was
performed.  At report time it is ahead by the pre-existing seven commits plus
the three V-0 commits, and behind the updated remote by one commit.

This report is intentionally uncommitted.
