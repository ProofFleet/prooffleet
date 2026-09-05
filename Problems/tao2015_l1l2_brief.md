# Track R — L1/L2 brief: the per-cell later-level leg (Finding E.3)

**Ground rules:** `Problems/tao2015_vi9g_brief.md` §0 verbatim (no `sorry`/`axiom`/`unsafe` under `MoltResearch/`, `Solutions/`
— not even in comments; new nucleus lemmas go in a **new leaf file** registered by one import line in
`MoltResearch/DiscrepancyAnalytic.lean`; never edit `PlancherelHarness`, never append to `BandSchedule`/`WindowTK`/
`WindowAssembly`/`HalaszComplex`; no instances of `*Assumption` classes; one commit per unit `Track R: <one line> (#3044, L<n>)`;
never push/merge/rebase; `CODEX_REPORT.md` uncommitted at the end). Read first: the design report
`Problems/tao2015_a1_r6r7_design_report.md` §"Finding E" (item 3) and §"Phase 4"; `MoltResearch/Discrepancy/BandCapstone.lean`
(`band_energy_level_le_of_prev_large`, `setIntegral_norm_sq_level_sum_of_prev_large_le`,
`setIntegral_norm_sq_sum_le_card_mul_of_setIntegral`); `MoltResearch/Discrepancy/LevelLegs.lean`
(`band_energy_later_main_le_budget`, `levelSmallSet`, `firstPrevLargePart`, `levelLargeness_ge`);
`Conjectures/C0002_erdos_discrepancy/src/TrackCStage5InnerBandAssembly.lean` (`innerBand_later_level_main`,
`innerBand_level_leg_of_main`); `TrackCStage5InnerBandScheduleSharp.lean` (`band_energy_typicalS_le_of_schedule_sharp`,
its `hscheduleLater`).

## Why

The later-level leg borrows `ℓ` copies of the previous level's large cell polynomial `Q_r` (`|Q_r| ≥ e^{−βr/(2N_prev)} = p_r^{−β}`
on the part `G_r`) to lengthen the current cell's quotient polynomial `R_v` (length `≍ A/p_v`) to `≥ T`, then applies the mean
value theorem. The existing wrapper uses **one** `(A', Δ', ℓ)` for all current cells `v` and replaces the threshold by the
level-wide lower bound `Qprev^{−β}e^{−β/(2N)}` (M-3, `levelLargeness_ge`). For a level of width `ratio = log Q_j/log P_j > 1`
this loses `(Q_j/h)^{2β·ratio_{j−1}}` against the smallness `P_j^{−2α_j}`, which no schedule can pay (design report,
Finding E.3). Per cell — `A'_v ≍ A/p_v`, `ℓ_{r,v} ≈ log(p_v T/A)/log p_r`, threshold `p_r^{−β}` — the loss is
`(p_v T/A)^{2β}p_r^{2β}(ℓ!)²…` against `p_v^{−2α_j}`, and the level sums converge (`[MR]`'s "not too far/not too close").
The nucleus core `band_energy_level_le_of_prev_large` is already per cell (it takes `S v`, `ℓ`, `A'`, `large` as parameters);
only the two wrappers above fix them across `v`.

## L1 — nucleus leaf `MoltResearch/Discrepancy/LaterLevelCells.lean` (import `MoltResearch.Discrepancy.LevelLegs`; register in `DiscrepancyAnalytic.lean`)

1. `setIntegral_norm_sq_level_sum_of_prev_large_le_cells`: `setIntegral_norm_sq_level_sum_of_prev_large_le` with
   `ℓ A' Δ' : ℕ → ℕ` (hypotheses `∀ v ∈ I, 1 ≤ ℓ v`, `1 ≤ A' v`, `Δ' v ≤ A' v`, `S v ⊆ Ioc (A' v) (A' v + Δ' v)`) and conclusion
   `≤ card I · ∑_{v∈I} (small v)²/large^{2ℓ v} · (e^π(T/((P^{ℓ v}·A' v : ℕ)) + 2·2^{ℓ v+1}) · ((ℓ v)!)²·(2^{ℓ v+1}(ℓ v+1)(∑_{p∈Y}1/p)^{ℓ v}))`.
   Proof: the same two lines (`setIntegral_norm_sq_sum_le_card_mul_of_setIntegral` + `band_energy_level_le_of_prev_large` per `v`).
2. `band_energy_later_main_le_budget_cells`: `band_energy_later_main_le_budget` with `A' Delta' ell : ℕ → ℕ` (per current cell `v`),
   `hSblk : ∀ v ∈ Ico v₀ (v₁+1), Sblk v ⊆ Ioc (A' v) (A' v + Delta' v)`, **no** `Plo Qhi Qprev v₁prev hr htopPrev htop hbot`, the
   large threshold used directly: `large := Real.exp (-(beta * r / ((2 * Nprev : ℕ) : ℝ)))` (from `hlargeCell`, skipping M-3), and
   ```
   hfit : ((Ico v₀ (v₁+1)).card : ℝ) * ∑ v ∈ Ico v₀ (v₁+1),
       (Real.exp (-(alpha * v / ((2*Ncur : ℕ) : ℝ))))^2 / (Real.exp (-(beta * r / ((2*Nprev : ℕ) : ℝ))))^(2 * ell v)
       * (Real.exp Real.pi * (T / ((Pmom ^ ell v * A' v : ℕ) : ℝ) + 2 * ((2 ^ (ell v + 1) : ℕ) : ℝ))
          * ((Nat.factorial (ell v) : ℝ)^2 * (((2 ^ (ell v + 1) : ℕ) : ℝ) * ((ell v : ℝ) + 1)
              * (∑ p ∈ eadicCell Pprev (2 * Nprev) r, (1:ℝ)/p) ^ ell v)))
     ≤ kappa * bandBudget c₃ eps rho
   ```
   with the same conclusion. Keep the docstring honest: it is the per-cell form of the level-`j` main term; M-9 (level endpoints)
   is deliberately not applied — the numerology (L3) sums the explicit `v`-series.
3. Sanity lemma (for L3): `∑_{v∈Ico v₀ (v₁+1)} exp(−2α v/(2N))·w v ≤ …` is not needed here; do add
   `laterMomentCells_le_pow`: `((ℓ)!)²·2^{ℓ+1}(ℓ+1)·M^ℓ ≤ (2ℓ²·(4M))^ℓ·… ` only if cheap (mirror `dyadic_moment_ratio_le_schedule`);
   otherwise leave to L3.

## L2 — Conjectures

1. `innerBand_later_level_main_cells` (in a **new** file `TrackCStage5InnerBandAssemblyCells.lean`, importing the assembly file):
   `innerBand_later_level_main` with `A' Delta' ell : ℕ → ℕ → ℕ` (indices `r v`), `hSblk : ∀ r v, Ioc (A / ql j v) ((A+Delta)/ql j v) ⊆
   Ioc (A' r v) (A' r v + Delta' r v)`, `hA' hDelta' hell` per `(r, v)`, no `Plo Qhi`, and `hfit r` in the L1 shape (the `v`-sum with
   `alpha j`, `alpha (j−1)`, `Nl j`, `Nl (j−1)`, `Pmom r`, `eadicCell (Pl (j−1)) (2 Nl (j−1)) r`). Proof: the existing one with
   `band_energy_later_main_le_budget_cells` in place of `band_energy_later_main_le_budget` (the `hlarge`/`hsmall` blocks are unchanged).
2. `band_energy_typicalS_le_of_schedule_sharp_cells` (new file `TrackCStage5InnerBandScheduleSharpCells.lean`): the sharp schedule
   theorem with `A' Delta' ell : ℕ → ℕ → ℕ → ℕ` (`j r v`), `hSblk/hA'/hDelta'/hell` per `(j, r, v)`, **no** `Plo/Qhi/htop/hbot` for
   `j ≥ 1` (keep them for level 0, whose leg is unchanged), and `hscheduleLater` replaced by
   ```
   hscheduleLaterCells : ∀ j, 0 < j → j < J → ∀ r ∈ Ico (v₀l (j−1)) (v₁l (j−1) + 1),
     ((Ico (v₀l j) (v₁l j + 1)).card : ℝ) * ∑ v ∈ Ico (v₀l j) (v₁l j + 1),
       (Real.exp (-(innerBandScheduleAlpha j * v / ((2 * Nl j : ℕ) : ℝ))))^2
         / (Real.exp (-(innerBandScheduleAlpha (j-1) * r / ((2 * Nl (j-1) : ℕ) : ℝ))))^(2 * ell j r v)
       * (Real.exp Real.pi * (T / ((Pmom j r ^ ell j r v * A' j r v : ℕ) : ℝ) + 2 * ((2 ^ (ell j r v + 1) : ℕ) : ℝ))
          * ((Nat.factorial (ell j r v) : ℝ)^2 * (((2 ^ (ell j r v + 1) : ℕ) : ℝ) * ((ell j r v : ℝ) + 1)
              * (∑ p ∈ eadicCell (Pl (j-1)) (2 * Nl (j-1)) r, (1:ℝ)/p) ^ ell j r v)))
     ≤ kappaCell j r * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))
   ```
   with a **free** per-cell share `kappaCell : ℕ → ℕ → ℝ`, `hkappaCell : ∀ j r, 0 ≤ kappaCell j r`, and
   `hsharesCells : ∀ j, 0 < j → j < J → ∑ r ∈ Ico (v₀l (j-1)) (v₁l (j-1) + 1), kappaCell j r ≤ ordinaryLegShare j`
   (not `geometricCellShare`: `κ/2^{r+1}` decays like `Q_{j−1}^{−2N log 2}` in the cell index, which no level saving pays; the
   numerology will take the uniform `ordinaryLegShare j / #cells_{j−1}`). Everything else (level 0, replacement/collision fits, the exceptional legs `hfitInt`/`hfitPri`, the recut) verbatim; the proof
   swaps the later-level call. Do **not** modify the existing theorems.
3. A docstring note in both new files: the natural choices are `A' j r v := A / ql j v`, `Delta' j r v := (A+Delta)/ql j v − A/ql j v`
   (state the ℕ-division guard that gives `Delta' ≤ A'`, e.g. `Delta + ql j v ≤ A`), `ell j r v := ⌈log(2·ql j v·T/A)/log (Pmom j r)⌉₊ + 1`
   (so `Pmom^ell·A' ≥ T`); prove the small lemma `T / (Pmom^ell * A') ≤ 1` for that `ell` if convenient (L3 needs it).

## Verification and report

`lake env lean` each new file; `lake build MoltResearch.DiscrepancyAnalytic Conjectures`; the grep gates and
`python3 scripts/check_aggregator_coverage.py` (the new nucleus file must be reachable — the import line in `DiscrepancyAnalytic.lean`).
`#print axioms` of the two nucleus lemmas (standard three only). `CODEX_REPORT.md`: statements, what was copied from where, any
place the copied proof needed more than the swap, and the exact `hfit` shape as compiled.

## Stop rule

Constant-factor differences are yours. Stop only if the per-cell statement cannot be proved from the existing core (e.g. a
hypothesis of `band_energy_level_le_of_prev_large` that is not per-cell) — record exactly which, and report.
