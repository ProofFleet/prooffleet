# Track R — L1/L2: Codex run 11 final report (2026-09-05)

Verbatim final report of Codex run 11 (gpt-5.6-sol, brief `Problems/tao2015_l1l2_brief.md`), whose two commits shipped as
the L1/L2 PR. L1/L2 make the later-level leg per cell in both indices (Finding E.3 of the design report): the nucleus
leaf `LaterLevelCells.lean` (per-cell `(ℓ, A', Δ')`, the exact previous-cell threshold `e^{−βr/(2N)}`, no M-3/M-9), and
the Conjectures wrappers `innerBand_later_level_main_cells`, `band_energy_typicalS_le_of_levels_recut_cells`,
`band_energy_typicalS_le_of_schedule_sharp_cells` with free per-cell shares `kappaCell`. Commit hashes are the run's,
before cherry-pick.

---

# Track R L1/L2 report — per-cell later-level leg (Finding E.3)

## Outcome

Implemented and committed both requested units:

- `090959ca` — `Track R: add per-cell later-level nucleus bounds (#3044, L1)`
- `527353cf` — `Track R: thread per-cell later legs through the sharp schedule (#3044, L2)`

No existing theorem was modified.  The optional L3 moment-growth lemma and the
convenience proof of `T / (Pmom ^ ell * A') ≤ 1` were not added; both belong
with the ladder numerology.

## Statements

### L1: `MoltResearch/Discrepancy/LaterLevelCells.lean`

1. `setIntegral_norm_sq_level_sum_of_prev_large_le_cells`

   This is `setIntegral_norm_sq_level_sum_of_prev_large_le` with
   `ℓ A' Δ' : ℕ → ℕ`.  Its hypotheses are cellwise on `I`, including
   `1 ≤ ℓ v`, `1 ≤ A' v`, `Δ' v ≤ A' v`, and
   `S v ⊆ Ioc (A' v) (A' v + Δ' v)`.  The conclusion retains the
   Cauchy–Schwarz factor `card I` and the explicit sum of the per-cell
   previous-large-cell moment bounds.

2. `band_energy_later_main_le_budget_cells`

   This is the later main-term budget wrapper with
   `A' Delta' ell : ℕ → ℕ`.  It uses the exact large threshold
   `exp (-(beta * r / (2 * Nprev)))` supplied by `hlargeCell`.  There are no
   level endpoint parameters and no endpoint hypotheses.

### L2: Conjectures leaves

3. `innerBand_later_level_main_cells`

   This has `A' Delta' ell : ℕ → ℕ → ℕ`, indexed by `(r,v)`, and an explicit
   current-cell sum in `hfit r`.  The least-large-previous-cell partition and
   its share sum are unchanged.

4. `band_energy_typicalS_le_of_levels_recut_cells`

   This is the internal recut level assembler needed because the existing
   recut assembler closes over the old later-level wrapper.  Level zero keeps
   scalar `Plo0`, `Qhi0`, `htop0`, and `hbot0`; later levels use no endpoints.

5. `band_energy_typicalS_le_of_schedule_sharp_cells`

   This has `A' Delta' ell : ℕ → ℕ → ℕ → ℕ`, indexed by `(j,r,v)`, and
   `Pmom : ℕ → ℕ → ℕ`.  It accepts free shares
   `kappaCell : ℕ → ℕ → ℝ`, their nonnegativity `hkappaCell`, and
   `hsharesCells`, which sums them against `ordinaryLegShare j`.  It does not
   use `geometricCellShare` for later levels.  Level zero, replacement,
   collision, exceptional, and recut hypotheses retain the sharp theorem's
   shapes.

Both Conjectures leaves document the natural choices

```text
A' j r v     := A / ql j v
Delta' j r v := (A + Delta) / ql j v - A / ql j v
ell j r v    := ⌈log (2 * ql j v * T / A) / log (Pmom j r)⌉₊ + 1
```

and record `Delta + ql j v ≤ A` as a convenient natural-number division guard
for `Delta' j r v ≤ A' j r v`.

## Exact compiled later-cell fit

The schedule theorem's `hscheduleLaterCells` elaborates in this shape (binder
names normalized only for readability):

```lean
∀ j, 0 < j → j < J →
  ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
  ((Finset.Ico (v₀l j) (v₁l j + 1)).card : ℝ)
    * ∑ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      (Real.exp (-(innerBandScheduleAlpha j * (v : ℝ) /
          ((2 * Nl j : ℕ) : ℝ)))) ^ 2
        / (Real.exp (-(innerBandScheduleAlpha (j - 1) * (r : ℝ) /
            ((2 * Nl (j - 1) : ℕ) : ℝ)))) ^ (2 * ell j r v)
        * (Real.exp Real.pi
            * (T / ((Pmom j r ^ ell j r v * A' j r v : ℕ) : ℝ)
              + 2 * ((2 ^ (ell j r v + 1) : ℕ) : ℝ))
          * ((Nat.factorial (ell j r v) : ℝ) ^ 2
            * (((2 ^ (ell j r v + 1) : ℕ) : ℝ)
              * ((ell j r v : ℝ) + 1)
              * (∑ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r,
                  (1 : ℝ) / (p : ℝ)) ^ ell j r v)))
    ≤ kappaCell j r * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))
```

The L1 budget theorem has the same expression with
`alpha`, `beta`, `Ncur`, `Nprev`, `Pmom`, `A' v`, and `ell v`; its right-hand
side is `kappa * bandBudget c₃ eps rho`.

## Proof provenance and deviations

- `setIntegral_norm_sq_level_sum_of_prev_large_le_cells` was copied from
  `BandCapstone.setIntegral_norm_sq_level_sum_of_prev_large_le`.  The
  continuity block and call to
  `setIntegral_norm_sq_sum_le_card_mul_of_setIntegral` are unchanged; only the
  arguments passed to `band_energy_level_le_of_prev_large` became functions of
  `v`.
- `band_energy_later_main_le_budget_cells` was copied from
  `LevelLegs.band_energy_later_main_le_budget`.  The M-3 call to
  `levelLargeness_ge` and the M-9 call to `levelJ_le_budget_eadic` were removed.
  The exact cell threshold is passed directly, and the raw estimate closes by
  the explicit `hfit`.
- `innerBand_later_level_main_cells` was copied from
  `TrackCStage5InnerBandAssembly.innerBand_later_level_main`.  Besides changing
  the interval/moment binders to `(r,v)`, the only proof change is the call to
  `band_energy_later_main_le_budget_cells`; the `hlarge` and `hsmall` blocks are
  unchanged.
- `band_energy_typicalS_le_of_levels_recut_cells` was copied from the recut
  assembler in `TrackCStage5InnerBandScheduleSharp`.  Its later-level call was
  replaced by `innerBand_later_level_main_cells`; level-zero endpoints were
  made scalar because no later-level proof consumes them.
- `band_energy_typicalS_le_of_schedule_sharp_cells` was copied from
  `TrackCStage5InnerBandScheduleSharp.band_energy_typicalS_le_of_schedule_sharp`.
  The old `laterLevel_fit_of_schedule` conversion was deleted: the new
  explicit schedule hypothesis is already the core fit.  At the final Fourier
  weight rescaling, `kappaCell/Cw` replaces the geometric shares.  The proof
  normalizes `max (kappaCell j r) 0` back to `kappaCell j r` using
  `hkappaCell`; this is provably equal to the requested free nonnegative share.
  All exceptional, replacement, collision, and recut proof blocks were copied
  unchanged.

The only direct-file warning is the retained `hDeltaU0` parameter in the sharp
schedule theorem; the original sharp theorem emits the same warning.

## Verification

Passed:

```text
lake env lean MoltResearch/Discrepancy/LaterLevelCells.lean
lake env lean Conjectures/C0002_erdos_discrepancy/src/TrackCStage5InnerBandAssemblyCells.lean
lake env lean Conjectures/C0002_erdos_discrepancy/src/TrackCStage5InnerBandScheduleSharpCells.lean
./scripts/forbid_sorry.sh
./scripts/forbid_axiom_unsafe.sh
./scripts/check_layering.sh
python3 scripts/check_aggregator_coverage.py
lake build MoltResearch.DiscrepancyAnalytic Conjectures
```

Aggregator coverage reports 181 modules, 179 reachable, with only the two
repository-allowlisted example modules outside the compiled graph.

`#print axioms` reports for both L1 theorems:

```text
[propext, Classical.choice, Quot.sound]
```

## Findings

- The stop rule did not trigger: the existing core is fully per-cell in every
  datum needed here.
- The worktree began clean but one commit behind `origin/main`
  (`719471d7`, the Finding E/Phase 4 report and related phase-3 record).  While
  the run was in progress, `origin/main` advanced again to `10e43ce8` (R9), so
  the final branch is two commits behind.  Per the explicit no-merge/no-rebase
  rule, branch history was not rewritten.  The two L1/L2 commits above are
  therefore ready to transplant onto that updated base if required.
