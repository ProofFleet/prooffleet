# Track R — L3: Codex run 14 final report (2026-09-05)

Verbatim final report of Codex run 14 (gpt-5.6-sol, brief `Problems/tao2015_l3_brief.md` without its resume note), whose one commit
shipped as the L3a PR. Run 14 stopped at L3-5: the exceptional part's share in the band partition is `1/2^{J+1}` with `J = J(A₁) → ∞`,
while the exceptional leg's total cost is a fixed positive constant (the recut's Cauchy–Schwarz over `#cells_U ≥ log Q_𝒰` cells against
`∑_v` prime parts `≥ 64 d² E_𝒰/log Q_𝒰`), so no cell-share distribution helps — Finding E.7 of the design report; the repair (a fixed
exceptional share `1/2`, ordinary shares `1/2^{j+2}`) is the resume note of run 15. Commit hash is the run's, before cherry-pick.

---

# Track R L3 report — stopped at the exceptional cell-share fit

Date: 2026-09-05

Branch: `vex/track-r-l3`

Base supplied to this run: `ec46c210` (the L4/V1 branch tip)

Run commit: `342d74f7` — `Track R: isolate the exceptional cell-share obstruction (#3044, L3-5)`

## Outcome

The Phase-4 brief fails at L3-5, before A2-IV-3', by a factor unbounded in
the scale-window base `A1`.  I stopped under the stated stop rule and did not
enter A2-IV-3', A2-V', the endpoint theorem, or the audit file.

The reversed margin is in the exceptional prime part of `hfitUCell`, combined
with the outer exceptional-cell Cauchy factor in `hfitU`.  The issue is not the
run-13 MVT normalization or the replacement collars.

## Exact failed margin

Write

```text
I       = #cells_U,
L       = log P_U,
kappa_v = 1 / (2^(J+4) I^2),
d       = epsilon' / 8.
```

The brief explicitly reduces the prime part and asks for the sufficient
condition

```text
DeltaU(v)^2 <= kappa_v * c3 * eps^2 * L / (24*1024).
```

The existing theorem `cellHalaszSharpBound_ge_eps_div_eight` gives
`DeltaU(v) >= d` on the long quotient when
`delta0 = epsilon'/(8*exp 1)`.  The canonical contiguous e-adic range satisfies

```text
I >= 2*Nu*(log Q_U - log P_U).
```

Since `Q_U = P_U^R`, where the density requirement has `R >= 2`, this gives
`I >= L` already for `Nu = 1`.  Substitution forces

```text
384 * 2^(J+4) * epsilon'^2 * L <= c3 * eps^2,
```

or equivalently

```text
L <= c3 * eps^2 / (6144 * 2^J * epsilon'^2).
```

But the prescribed exceptional scale has
`L >= (log A1)^(49/50)`, while `epsilon'`, `c3`, and `eps` are fixed before the
universal `A1` and `J(A1)` is nondecreasing and unbounded.  The failure factor

```text
6144 * 2^J * epsilon'^2 * log(P_U) / (c3 * eps^2)
```

is therefore unbounded in `A1`.  The brief's claim that a growing `log P_U`
makes this fit hold has the direction reversed: the `I^2` in the denominator
of the per-cell share leaves only `O(1/(2^J log P_U))` on the right.

## Why parameter changes do not repair it

1. Increasing `Nu` increases `I`, so it worsens the uniform-share margin.
2. The exceptional density clause needs a fixed positive reciprocal-prime
   mass.  With `Q_U = P_U^R`, this requires a fixed `R > 1`; taking a larger
   `R` also increases `I`.
3. Taking `epsilon'` extremely small changes only the fixed threshold.  It
   cannot depend on arbitrarily large `A1`: `sharpRamareCost_le_eps` requires
   `D >= D0(epsilon')`, while `hstrengthSharp` bounds `D` in terms of the one
   `A0` selected before `forall A1`.
4. Nonuniform shares do not remove the geometric loss.  For unit-modulus
   prime coefficients, summing the exact prime pieces gives the lower cost

   ```text
   64*d^2*E_U/log Q_U.
   ```

   The same e-adic width gives `I >= log Q_U`.  Hence the aggregate hypothesis
   itself forces

   ```text
   16 * 2^(J+1) * epsilon'^2 * E_U <= c3 * eps^2.
   ```

   The density construction has `E_U` bounded below by a fixed positive
   constant, so this fails by an unbounded factor as `J(A1) -> infinity`.
   This is independent of how the individual `kappaU(v)` are distributed.

The required repair is therefore structural: remove the outer `#cells_U`
Cauchy loss for the exceptional prime term, or give the exceptional band a
share bounded below independently of `J`.  Neither repair is available in
the exact compiled interface
`band_energy_typicalS_le_of_schedule_sharp_cells_wide` required by the brief.

## Machine-checked statements

The new Conjectures leaf
`Conjectures/C0002_erdos_discrepancy/src/TrackCStage5LadderNumerology.lean`
contains:

- `phase4EadicIndexRange_width_le_card`;
- `phase4EadicIndexRange_log_lower`;
- `ladderExceptionalCellShare_prime_fit_forces_log_upper`;
- `ladderExceptionalCellShare_prime_fit_fails_of_large_log`;
- `ladderExceptionalAggregate_prime_fit_forces_level_upper`;
- `ladderExceptionalAggregate_fixed_floor_forces_level_upper`.

The first pair proves the exact contiguous-cell count lower bound.  The next
pair records the uniform-share contradiction.  The last pair records the
share-independent aggregate contradiction and the exact coefficient `16`
after substituting `d = epsilon'/8`.

## Verification

Passed before the stop:

```text
lake env lean Conjectures/C0002_erdos_discrepancy/src/TrackCStage5LadderNumerology.lean
lake build Conjectures.C0002_erdos_discrepancy.src.TrackCStage5LadderNumerology
./scripts/forbid_sorry.sh
./scripts/forbid_axiom_unsafe.sh
./scripts/check_layering.sh
python3 scripts/check_aggregator_coverage.py
lake build MoltResearch.DiscrepancyAnalytic Conjectures
```

The target build completed 8124 jobs, and the final combined build completed
8194 jobs.  Aggregator coverage reports 185 modules, 183 reachable, with only
the two repository-allowlisted example modules outside the compiled graph.
No forbidden nucleus file, `TrackCAxiomAudit.lean`, or A2 file was edited.  No
assumption-class instance was added.  No push, merge, or rebase was performed.
This report is intentionally uncommitted.


---

# Run 15 (L3 resumed with the fixed exceptional share): completion

Verbatim final report of Codex run 15 (same branch, resumed from `342d74f7` with the run-15 resume note), whose 148 commits
shipped as the L3b PR: L3-0 (the exceptional part's share `1/2`, `band_energy_typicalS_le_of_schedule_sharp_cells_wide'`),
L3-1…L3-6, A2-IV-3′, A2-V′-1…138, **`theorem sliceMeanSquareA2 [HalaszLargeValuesAssumption] [PrimeLargeValuesAssumption] :
SliceMeanSquareA2`**, the endpoint **`trackR_edp`** (`¬ BoundedDiscrepancy f` for every sign sequence under exactly the two
large-values interfaces), and their audit pins (`[propext, Classical.choice, Quot.sound]`).

---

# Track R L3 / A2 completion report

Date: 2026-09-06

Branch: `vex/track-r-l3`

Resume point: `342d74f7` (`Track R: isolate the exceptional cell-share obstruction`)

Final commit: `e25dfc37` (`Track R: pin the completed A2 axiom footprint`)

## Outcome

Run 15 repairs the bookkeeping artifact identified in run 14 and completes
L3, A2-IV-3', A2-V', `sliceMeanSquareA2`, and the discrepancy endpoint. No
stop-rule obstruction remains.

The exceptional band now receives the fixed share `1/2`, while ordinary
level `j` receives `1/2^(j+2)`. The theorem `shifted_shares_le_one` proves
that the resulting partition has total share at most one, and
`band_energy_typicalS_le_of_schedule_sharp_cells_wide'` is the requested
capstone with the revised ordinary and exceptional hypotheses. None of the
old schedule theorems was modified.

The exceptional prime contribution is summed before the outer Cauchy factor.
Brun--Titchmarsh cell cardinality cancels the cell width in the aggregate, so
the prime part is a fixed `Nu * N_U * DeltaU^2` cost instead of the invalid
`2^J`-shrinking pointwise allocation. The `V0` contribution retains its
negative logarithmic power and vanishes uniformly in the quadratic window.

## Recorded final choices

The final construction uses

```text
e       = min eps 1
rho     = 1 / (4 * sliceA2Parts eps)
eb      = e / 100
R       = exceptionalIntervalRatio epsc
eta     = sliceA2ExceptionalLadderEta e epsc eb rho
P0      = max 21 ceil(h^(1/(4R)))
k       = 4 * R * 1200000 + 100
```

The fixed bottom exponent is `1200000`; its dominant explicitly recorded
loss is `2 * 14 * 40960 = 1146880`. The height constant is

```text
max 1 (
  max ((sliceA2BottomPowerConstant epsc Qlog0)^(4R))
      (max sliceA2WindowPowerConstant
           (sliceA2FrequencyPowerConstant epsc)^2))
```

where `sliceA2WindowPowerConstant` contains the geometric, rounding,
Lipschitz, and outer-band constants, and the frequency target is
`sliceA2KappaMain 0 / (32 * 163880000)`.

The exceptional fixed-parameter ledger records

```text
N_U coefficient       = 3 + 73728*163880000*exp(pi)*exceptionalMass
prime coefficient     = 1 + 196608*Ncoef*R*exceptionalMass
epsilon denominator   = 800*16388*exp(13)*R*primeCoefficient
eta coefficient       = 64*exp(12)*max(epsilonDenominator,1/epsc) + 2
```

Thus the chosen exceptional accuracy is bounded below by a fixed multiple of
`e^7`, and `eta` is bounded above by a fixed multiple of `e^(-7)`. The
ordinary ledgers record `e^(-4)` cell and resolution costs, `e^(-14)` far
costs, `e^(-128)` close costs, and `e^(-8)` zero-prime and zero-frequency
coefficients. Every constant depends only on the already-fixed outer density
parameter (and `Qlog0` where displayed), never on `A1`.

The analytic witness now accepts a caller-supplied minimum scale. The final
proof puts both the density threshold and the eventual inequality
`P0 <= exceptionalPrimeLower A1` into that minimum before selecting `A0`.
Consequently the prime, polylog cutoff, density, and mean-square clauses all
use exactly the same `sliceA2FinalLevels` witness and the same
`NonPretentiousAt` strength.

## Final theorems and audit

`TrackCStage5SliceA2Final.lean` adds:

- `exists_sliceA2HeightP0_above_polylog`;
- `sliceMeanSquareA2 [HalaszLargeValuesAssumption]
  [PrimeLargeValuesAssumption] : SliceMeanSquareA2`;
- `trackR_edp`, the endpoint `edp_of_sliceMeanSquareA2 sliceMeanSquareA2`
  with no separate A.2 hypothesis at its call site.

`TrackCAxiomAudit.lean` pins both new theorem footprints to exactly

```text
[propext, Classical.choice, Quot.sound]
```

The two large-values interfaces remain theorem parameters. No
`FarRegimeRepulsionAssumption` occurs in either footprint, and no new
assumption-class instance was added.

## Verification

Passed:

```text
lake env lean TrackCStage5SliceA2HeightChoice.lean
lake env lean TrackCStage5SliceA2Final.lean
lake env lean TrackCAxiomAudit.lean
./scripts/forbid_sorry.sh
./scripts/forbid_axiom_unsafe.sh
./scripts/check_layering.sh
python3 scripts/check_aggregator_coverage.py
lake build MoltResearch.DiscrepancyAnalytic Conjectures
```

The final aggregate build completed 8336 jobs. Aggregator coverage reports
191 modules, 189 reachable, with only the two repository-allowlisted example
modules outside the compiled graph. No push, merge, or rebase was performed.
This report is intentionally uncommitted.
