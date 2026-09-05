# Track R — VI-9g phase 2 brief: the sharp exceptional schedule on the recut capstone, then `sliceMeanSquareA2`

**Status (2026-09-05, after PR #3686).** Codex run 6 (`Problems/tao2015_vi9g_report.md`) shipped
**VI-9g-1** — the recut cell-uniform capstone `band_energy_typicalS_le_of_cellUniform_fit_recut`
(`Conjectures/…/TrackCStage5BandEnergyExceptionalReCut.lean`), whose exceptional fit is the exact
**fixed-threshold** inequality

```
hfit : 2·( V₀²·Aint_v + δ_v²·Bpri_v·(1 + Γ_v) ) ≤ κ'_v · bandBudget c₃ ε (Δ/A)
  Aint_v = 64·((A+Δ)/q_v + #Kcov·√T)·(log 2T + 1)·∑_{n ≤ (A+Δ)/q_v} ‖cellBlockCoeff … n‖²/n²
  Kcov   = cellsMeetingSet (bandCells K₂) (bandPartOn Pset J {K₁ ≤ |ξ| ≤ K₂} J)
  Bpri_v = 64·(∑_{p ∈ cell_v} ‖g p‖²/p²)·Pc_v/log Pc_v
  Γ_v    = primeHighMomentCountCost Pc_v ℓ_v cell_v T V₀ λ_v · e^{−log Pc_v/(log 2T)^{3/4}} · (log 2T)²
```

— and **A2-IV-1′** (`LowBandTypicalSSharp.lean`, `integral_norm_typicalS_dirichlet_poly_sq_le_low_band_eps`).
The run also found that the `√`-optimised fit `exceptionalCell_fit_of_schedule` the phase-1 brief
presupposed is **not** an upper bound when `Γ ∝ V₀^{−2ℓ}`; the decision (design report, "Phase VI-9g
as run") is to keep `V₀ := exceptionalSplitThreshold A = (log A)^{−100}` and fit the two terms
separately. This brief is that repair and the rest of the ladder. Read first: `Problems/tao2015_vi9g_brief.md`
(§0 ground rules apply verbatim; §1 the target; §2 what is on main; §4 numerology), then the design report's
"The `𝒯₀` leg", "The `t₁`-split is unnecessary at fixed `ε`", and "Phase VI-9g as run".

## 1. What is on main for the exceptional block (do not rebuild)

- `hdelta` (the pointwise bound for **every** `|t| ≤ T`): `norm_cellBlock_poly_le_cellHalaszSharpBound_of_top`
  (`TrackCStage5ExceptionalSharp.lean`) — hypotheses `cellHalaszThreshold ≤ x0`, `1 ≤ D`, `0 < δ₀ ≤ 1`,
  `NonPretentiousAt g A₀ N`, `1 ≤ A₀`, `3·((A+Δ)/q) ≤ N`, `2πT + 2π(halaszM N + 1) ≤ A₀·N`,
  `2D ≤ A₀ − 2(loglog N − loglog x0 + 12)`; conclusion `‖∑_{n≤(A+Δ)/q} cellBlockCoeff …‖ ≤
  cellHalaszSharpBound x0 D δ₀ (A/q) ((A+Δ)/q) P rest`. Positivity: `cellHalaszSharpBound_pos`.
- `δ` explicit: `cellHalaszSharpBound_le_explicit` — `∀ ε, ∃ D₀ ≥ 1, x₀ ≥ 10¹⁶, ∀ D ≥ D₀, x0 ≥ x₀,
  1 ≤ Aq ≤ Bq ≤ 2Aq+1, P prime with p^{−(1−s)} ≤ 1/2, 0 < s < 1, rest:
  cellHalaszSharpBound x0 D (ε/(8e)) Aq Bq P rest ≤ 2^{#rest}·(2ε·e^{2∑_{p∈P}1/p} + (log Bq + 1)(Aq/x0)^{−s}·e^{2∑_{p∈P} p^{−(1−s)}})`.
- `#Kcov`: `card_cellsMeeting_exceptional_le_highMomentCost` (recut file :296) — for `Pset = levelSmallSet P N v0 v1 g alpha`
  (check that this is the schedule's `Pset`), `#Kcov ≤ ∑_{r ∈ I_{J−1}} 2·primeHighMomentCountCost (Panchor r) (ℓ r) (cell_{J−1,r}) T (e^{−α_{J−1} r/(2N_{J−1})}) (λ r)`.
- The top-scale hypothesis is the Prop's `NonPretentiousAt g A₀ (2A+1)`; lift to `N := 3(2A+1)` by
  `nonPretentiousAt_scale_up` (`MajorArcAssembly.lean`; strength `A₀/3`, `c = 3`); `3((A+Δ)/q) ≤ 3(A+Δ) ≤ 6A < N`.
- The schedule's level legs: `band_energy_typicalS_le_of_schedule'` (`TrackCStage5InnerBandSchedule.lean` :612)
  — reuse its level-leg proof blocks verbatim (`laterLevel_fit_of_schedule`, `eadic_replacement_costs_of_schedule`,
  `collision_fit_of_schedule`, `ordinaryLegShares_fit`, `level_subset_primeInterval`, `level_primeMass_le`, …).
- The old exceptional envelopes `exceptionalDeltaSchedule`, `exceptionalIntegerSchedule`, `exceptionalPrimeSchedule`,
  `exceptionalRatioSchedule`, `cellHalaszBound*` are **superseded**; do not use them.

## 2. The units

Dependency: `9g-2′ → 9g-3′ → A2-IV-3 → A2-V-1 → A2-V-2 → A2-V-3 → A2-V-4 → sliceMeanSquareA2 (+ audit pin)`.
Do not enter A2-IV-3/A2-V while a 9g unit is open.

- **VI-9g-2′ (the sharp exceptional schedule).** New Conjectures leaf (e.g. `TrackCStage5InnerBandScheduleSharp.lean`,
  importing the recut file, `TrackCStage5ExceptionalSharp`, `TrackCStage5InnerBandSchedule` for its
  level-leg lemmas): `band_energy_typicalS_le_of_schedule_sharp`, concluding
  `∫_{K₁≤|ξ|≤K₂} ‖F‖²·w ≤ (4H/A)²·bandBudget c₃ ε (Δ/A)` (VI-9a's honest accounting) with the level legs as
  in `band_energy_typicalS_le_of_schedule'` and the exceptional block:
  `Vsplit v := exceptionalSplitThreshold A`, `delta v := cellHalaszSharpBound x0 D δ₀ (A/qu v) ((A+Δ)/qu v) Pu restU`,
  `hdelta` from `_of_top` (hypotheses of the new theorem: `hNPtop : NonPretentiousAt g A₀ (2A+1)`, `x0`, `D`, `δ₀`,
  the range inequality `2πT + 2π(halaszM (3(2A+1)) + 1) ≤ (A₀/3)·3(2A+1)`, the strength inequality
  `2D ≤ A₀/3 − 2(loglog(3(2A+1)) − loglog x0 + 12)`), and **`hfit` proven from two explicit schedule
  inequalities**, each a hypothesis of the new theorem in schedule quantities only:
  * `hfitInt v : 2·V₀²·64·((A+Δ)/q_v + KcovBound·√T)·(log 2T + 1)·harmBound_v ≤ (κ'_v/2)·budget`, where
    `harmBound_v ≥ ∑_{n ≤ (A+Δ)/q_v} ‖cellBlockCoeff…‖²/n²` — prove the small lemma
    `∑_{n ∈ Icc 1 (B/q)} ‖cellBlockCoeff g A B P rest q n‖²/n² ≤ ∑_{n ∈ Ioc (A/q) (B/q)} 1/n² ≤ ((B/q) − (A/q))/((A/q)·((A/q)+1)) + …`
    (support `Ioc (A/q) (B/q)`, `‖coeff‖ ≤ 1` by `norm_cellBlockCoeff_le_one`; bound `∑_{n∈Ioc a b} 1/n² ≤ (b−a)/(a(a+1))`-type
    or simply `≤ 1/a` for `a ≥ 1` via `∑_{n>a} 1/n² ≤ 1/a`), and `KcovBound ≥ #Kcov` from
    `card_cellsMeeting_exceptional_le_highMomentCost`;
  * `hfitPri v : 2·Δ_U(v)²·(64·(#cell_v/Pc_v²)·Pc_v/log Pc_v)·(1 + Γ_v) ≤ (κ'_v/2)·budget`, where
    `Δ_U(v) ≥ delta v` is the explicit bound of `cellHalaszSharpBound_le_explicit` (its `D₀, x₀` become
    hypotheses-with-witnesses of the schedule theorem: state the schedule for `D ≥ D₀`, `x0 ≥ x₀` given by that
    lemma, or take `Δ_U` itself as a hypothesis `hΔU : ∀ v, delta v ≤ Δ_U v` discharged in 9g-3′), and
    `∑_{p∈cell}‖g p‖²/p² ≤ #cell/Pc²` (`hlo`, `hg`).
  Then `hfit` is `add_le_add` of the two, and the theorem calls `band_energy_typicalS_le_of_cellUniform_fit_recut`.
  Record the exact `hfitInt`/`hfitPri` statements in the docstring.
- **VI-9g-3′ (the fixed-`ε` S6 numerology).** Discharge `hfitInt`, `hfitPri`, the range and strength
  inequalities, `hBqCutoff`-type conditions (`(A+Δ)/q_v ≥ x0` with `x0 = ⌈√(3(2A+1))⌉₊` needs `Q_𝒰 ≤ √A/3`),
  and `p^{−(1−s)} ≤ 1/2`, from: `P_𝒰 := ⌈exp((log A)^{49/50})⌉₊` (so `e^{−log P_𝒰/(log 2T)^{3/4}} ≤
  exp(−(log A)^{49/50}/(log 2T)^{3/4})` kills every polylog once `T ≤ A`: `(log A)^{49/50−3/4} = (log A)^{0.23}`),
  `Q_𝒰 := ⌈exp((C/ε³)(log A)^{49/50})⌉₊`, `N_𝒰 := ⌈C/ε³⌉₊`, `s := 1/log Q_𝒰`, `ℓ := 1` (or the smallest `ℓ` making
  `Γ_v ≤ 1`), `V₀ = (log A)^{−100}`, `δ₀ := ε'/(8e)` with `ε' := ε⁶/(C·2^{J}·e^{2E_𝒰})`, `D := max(D₀(ε'), 1)`,
  `A₀ := 3(2D + 2 log 2 + 24) + (the low-band/level thresholds)`. All as **existence** statements
  (`∃ A₀, ∀ A ≥ A₀, …`) using `exists_forall_polylog_le`, `exists_exp_decay_le`, `exists_loglog_le_log`,
  `Real.isLittleO_pow_log_id_atTop`. Record every margin; where a fit fails as stated, record the exact
  inequality with numbers and stop (do not force it).
- **A2-IV-3** `SliceMeanSquareA2`'s mean-square clause from `slice_energy_le_of_bands` + A2-IV-1′ (low band) +
  A2-IV-2 (weight conversion) + 9g-2′ (inner band) + the outer band; the density clause from
  `window_typicalS_complement_le` + Mertens; the level-prime clause from A2-V-2.
- **A2-V-1..4** as in the phase-1 brief §3; **`theorem sliceMeanSquareA2 : SliceMeanSquareA2`** (a theorem,
  not an instance) with the audit pin in `TrackCAxiomAudit.lean` (dependency cone exactly
  `{HalaszLargeValuesAssumption, PrimeLargeValuesAssumption}` + standard axioms; `FarRegimeRepulsionAssumption`
  must not appear), and the card checkbox.

## 3. Deliverables

Commits per unit with findings in the bodies (`Track R: <one line> (#3044, VI-9g-2′)` etc.); `CODEX_REPORT.md`
at the end as in phase 1. Never push, merge, or rebase.
