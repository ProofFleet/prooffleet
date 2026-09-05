# Track R — VI-9g brief: the fixed-`ε` exceptional schedule at the sharp Halász cost, then `sliceMeanSquareA2`

**Status (2026-09-05, after T0-1…T0-7c, PRs #3678–#3684).** The two analytic gaps of the Phase 0
report (`Problems/tao2015_phase0_vi9_report.md`, "Work left undone") are closed or bypassed:

- the central-window gap (Finding C) is **fixed**: `halaszBudgetSharp` carries no `loglog` against
  `e^{−A}`, and `sharpTwistedDirichletCost_le_eps` gives, for every `ε`, a fixed strength `D₀(ε)` and
  scale `x₀(ε)` with the twisted Dirichlet block `≤ ε·b/(a+1)` **uniformly in the scale**;
- the far-regime gap is **bypassed**: at fixed `ε` there is no `t₁`-split at all. The Halász window
  `HalaszWindowAt` of `g·n^{−2πit}` holds at every frequency of the band from the interface's single
  top-scale `NonPretentiousAt g A₀ N` (`halaszWindowAt_archTwist_of_nonPretentiousAt`,
  `halaszWindowAt_twist_of_top`), so `FarRegimeRepulsionAssumption` is not needed for the A.2
  discharge. Read the design report `Problems/tao2015_a1_r6r7_design_report.md`, §"The `𝒯₀` leg" and
  §"The `t₁`-split is unnecessary at fixed `ε`", before anything else.

What remains between main and `theorem sliceMeanSquareA2 : SliceMeanSquareA2` is bookkeeping: the
exceptional leg's schedule with the sharp `δ` at the fixed-`ε` S6 (VI-9g), the per-slice statement
(A2-IV-3) and the instantiation (A2-V). This brief is written for a Codex-scale run (one worktree,
commit per unit, phase PRs), following the process that closed VI-9a–f.

## 0. Ground rules for the run

- Git worktree on a fresh branch from `origin/main`; `.lake` symlinked to the main checkout's
  prebuilt build directory. **Never `lake update`, never build Mathlib, never `lake exe cache
  get`.** Typecheck one file with `lake env lean <file>`; after editing a nucleus module rebuild
  its olean (`lake build MoltResearch.Discrepancy.<Mod>`) before typechecking a downstream file.
  `lake build Conjectures` at the end of each phase.
- `MoltResearch/` and `Solutions/` admit no `sorry`/`axiom`/`unsafe` (grep-enforced, comments
  included). New nucleus lemma bundles go in **new leaf files** under `MoltResearch/Discrepancy/`,
  each registered by one import line in `MoltResearch/DiscrepancyAnalytic.lean`; never append to
  `BandSchedule`, `WindowTK`, `WindowAssembly`, `PlancherelHarness`, `HalaszComplex`. Conjectures
  files import the narrowest nucleus module, never `MoltResearch.DiscrepancyAnalytic`.
- One unit per commit, commit before touching the next file. Record honestly (in the docstring
  and in a `## Findings` section of `CODEX_REPORT.md`) every fit that fails as stated; the point is
  the true accounting, not a forced one. Do not enter A2-IV-3/A2-V while a VI-9g unit is open.
- Both large-values interfaces (`HalaszLargeValuesAssumption` = IK 9.6, `PrimeLargeValuesAssumption`
  = MR Lemma 8, `Conjectures/…/Interfaces/LargeValues.lean`) may be used as stated. **No instance
  of any `*Assumption` class may be declared.** `FarRegimeRepulsionAssumption` must **not** appear
  in the dependency cone of `sliceMeanSquareA2`.
- Lean lessons from T0 (all hit this week): `linarith` fails on 8-summand goals whose differences
  are exactly three hypotheses — use `linear_combination h₁ + h₂ + h₃`; `field_simp` often closes
  the goal alone (a following `ring` errors "no goals"); `omega` loses nonnegativity of variable
  quotients `↑A/↑n₁` — `generalize A / n1 = d at h ⊢` first; filter predicates with casts need
  `fun n : ℕ => …`; `Real.finset_prod_rpow : ∏ f i ^ r = (∏ f i) ^ r` (rewrite with `←`);
  `nlinarith`/`gcongr`/`positivity` time out in contexts carrying the A.2 clauses — split every
  numeric fact into a small lemma with a minimal context; `set_option … in` goes before the
  docstring.

## 1. The target, transcribed

`SliceMeanSquareA2` (`Conjectures/…/TrackCStage5MajorArcA2.lean` :54):

```
∀ εc > 0, ∀ B (C > 0), ∃ h₁ (C₁ > 0) k, ∀ ε > 0, ∀ h ≥ h₁ with C₁/ε^k ≤ h,
  ∃ levels A₀ ≥ 1,
    (∀ P ∈ levels, ∀ p ∈ P, p.Prime) ∧
    (∀ P ∈ levels, ∀ p ∈ P, C·(log h)^B < p) ∧
    (∀ A ≥ A₀, ∑_{n∈(A,2A], ¬𝒮 n} 1/n ≤ εc·∑_{(A,2A]} 1/n) ∧
    (∀ A ≥ A₀, ∀ g CM 1-bounded with g 1 = 1 and NonPretentiousAt g A₀ (2A+1), ∀ J ≤ A,
       ∑_{n∈(A,A+J]} ‖∑_{m∈(n,n+h]∩𝒮} g m‖²/n ≤ ε²h²·∑_{(A,A+J]} 1/n)
```

`edp_of_sliceMeanSquareA2` (`TrackCStage5MajorArcEDP.lean`, audit-pinned) is EDP on exactly this
Prop. Its `h`-threshold must be polynomial in `1/ε` (the wrapper takes `ε ≍ ε₀/(log H)^B`).

## 2. What is on main (do not rebuild)

- **The abstract-`δ` capstone** `band_energy_typicalS_le_of_cellUniform_fit`
  (`TrackCStage5BandCapstoneFamily.lean` :727): per exceptional cell `v`, `hδ0 : 0 < δ v`,
  `hδ : ∀ t, |t| ≤ T → ‖∑_{n ≤ N v} (a v n/n)·e(−t log n)‖ ≤ δ v`, `hA0/hB0/hΓ0`, and
  `hfit : 2(δ v² Bpri v + 2 δ v √(Aint v · Bpri v · Γ v)) ≤ κ' v · budget`, `hfitU`. Its per-cell
  input is `setIntegral_band_energy_exceptional_le_budget` (`TrackCStage5BandEnergyExceptional.lean`
  :527) ← `setIntegral_band_energy_exceptional_max_le` (:385) ← `sum_prime_integer_energy_le` (:57),
  with the **old** shapes `Aint = 64(N + #K·√T)(log 2T + 1)∑‖a‖²/n²` (`#K ≤ 2T`: Finding B row 1)
  and `Γ ∝ ((T+1)/P + 4)` (row 2).
- **VI-9b/c/d (the recut inputs, never wired into the capstone):** `card_large_prime_poly_pow_le`
  (`LargePrimePolynomialCount.lean`), `cellsMeetingSet`, `largeValueCells`,
  `cellsMeeting_exceptional_subset_biUnion`, `card_cellsMeeting_exceptional_le_sum`,
  `card_largeValueCells_prime_poly_pow_le` (`ExceptionalCellCover.lean`), and
  `sum_prime_integer_energy_high_moment_le` with `primeHighMomentCountCost`,
  `exceptionalSplitThreshold = (log A)^{−100}` (`TrackCStage5ExceptionalReCut.lean`) — the discrete
  energy with the prime term `δ²·64(1 + primeHighMomentCountCost·e^{−log P/(log 2T)^{3/4}}(log 2T)²)·…`,
  no `T/P`.
- **The sharp `δ` (T0-7c, `TrackCStage5ExceptionalSharp.lean`):**
  `norm_cellBlock_poly_le_cellHalaszSharpBound_of_top` — for **every** `|t| ≤ T`,
  `‖cell block polynomial‖ ≤ cellHalaszSharpBound x0 D δ₀ (A/q) ((A+Δ)/q) P rest`, from
  `NonPretentiousAt g A₀ N` with `3·((A+Δ)/q) ≤ N`, `2πT + 2π(halaszM N + 1) ≤ A₀·N`,
  `2D ≤ A₀ − 2(loglog N − loglog x0 + 12)`, `cellHalaszThreshold ≤ x0`, `1 ≤ D`, `0 < δ₀ ≤ 1`;
  `cellHalaszSharpBound_pos`; `cellHalaszSharpBound_le_explicit` — `∀ ε, ∃ D₀ ≥ 1, x₀ ≥ 10¹⁶,
  ∀ D ≥ D₀, x0 ≥ x₀, 1 ≤ Aq ≤ Bq ≤ 2Aq+1, P with p^{−(1−s)} ≤ 1/2, 0 < s < 1, rest:
  cellHalaszSharpBound x0 D (ε/(8e)) Aq Bq P rest ≤ 2^{#rest}(2ε e^{2∑_{p∈P}1/p}
  + (log Bq + 1)(Aq/x0)^{−s} e^{2∑_{p∈P} p^{−(1−s)}})`. Below it: `HalaszSharpEps.lean`
  (`sharpTwistedDirichletCost_le_eps`), `SmoothRankinTail.lean` (`sharpRamareCost_le_eps`,
  `pSmooth_harmonic_tail_le`, `prod_inv_one_sub_le_exp`), `ExceptionalHalaszSharp.lean`,
  `HalaszSharpTwist.lean` (the bridge), `HalaszSharpWindow.lean`, `HalaszSharpSurvivors.lean`.
- **The schedule** `band_energy_typicalS_le_of_schedule'` (`TrackCStage5InnerBandSchedule.lean`
  :612–1154, VI-9a): its exceptional block is `deltaU v := exceptionalDeltaSchedule …`, `hdeltaU0`,
  `hdeltaU` (from `norm_cellBlock_poly_le_cellHalaszBound_of_uniform` + `cellHalaszBound_le_explicit_schedule`),
  `hfitUCell` (from `hscheduleUCell : exceptionalCellScheduleCost (exceptionalIntegerSchedule …)
  (exceptionalPrimeSchedule …) (exceptionalRatioSchedule …) (deltaU v) ≤ kappaU v · budget`),
  then the call to `band_energy_typicalS_le_of_cellUniform_fit`. The level legs (ordinary levels,
  replacement, collision) are correct and stay.
- **A2-IV-0/1/2:** `slice_energy_le_of_bands` (`SliceA2.lean`), `LowBandTypicalS.lean`
  (`integral_norm_typicalS_dirichlet_poly_sq_le_low_band` — NOTE: built on
  `cheap_halasz_twisted_dirichlet_block`, whose `|2πt| ≤ (D/2)a` is fine on the LOW band
  `|ξ| ≤ K ≍ C/ε³` at scales `≥ 10¹⁶`, but its cost carries `W ≥ 22`: `e^{W loglog b + W − D/2}` is
  a `(log b)^{22}` LOSS — the low band must be re-priced with `sharp_halasz_twisted_dirichlet_block`
  (T0-5; frequency condition satisfied there) or `_window`; see unit A2-IV-1′), `SliceWeightConversion.lean`.
- **The density clause:** `window_typicalS_complement_le` (`WindowTK.lean`) + Mertens
  (`log_log_le_sum_one_div_primesBelow`, `sum_one_div_primesBelow_le_sharp`).
- **Scale transfer:** `nonPretentiousAt_scale_up` (`MajorArcAssembly.lean`: strength `A/c` at scale
  `≤ c·x`), `nonPretentiousAt_scale_transfer` (down, Mertens loss), `halaszM_band_le`.

## 3. The units

Dependency: `9g-1 → 9g-2 → 9g-3 ; A2-IV-1′ ; A2-IV-3 after 9g-3 and A2-IV-1′ ; A2-V-1 → A2-V-2 →
A2-V-3 → A2-V-4 → sliceMeanSquareA2`.

- **VI-9g-1 (the recut capstone).** `setIntegral_band_energy_exceptional_le_budget_recut`: the
  `_max_le` + `_le_budget` pair with `sum_prime_integer_energy_high_moment_le` in place of
  `sum_prime_integer_energy_le`, so `Γ_recut = primeHighMomentCountCost P ℓ Y T V₀ λ · e^{−log P/(log 2T)^{3/4}} (log 2T)²`
  (no `T/P`; `ℓ` a free moment order); and `Aint_recut = 64(N + #K_cov √T)(log 2T + 1)∑‖a‖²/n²` with
  `#K_cov` the covered-cell count of VI-9c (`card_cellsMeeting_exceptional_le_sum` +
  `card_largeValueCells_prime_poly_pow_le` at level `J−1`), replacing `#K ≤ 2T`. Then
  `band_energy_typicalS_le_of_cellUniform_fit_recut` (BandCapstoneFamily mirror, `hfit` in the recut
  shapes). Keep `hδ` ungated (the design of `_le_budget`'s docstring). Record the exact new fit.
- **ERRATUM (Codex run 6, `Problems/tao2015_vi9g_report.md`).** VI-9g-2/3 below presuppose the `√`-optimised fit
  `exceptionalCell_fit_of_schedule`; with the high-moment count `Γ(V) ∝ V^{−2ℓ}` that shape is not an upper
  bound. Use the **fixed-threshold** fit of `band_energy_typicalS_le_of_cellUniform_fit_recut`,
  `2(V₀²·Aint + δ²·Bpri(1+Γ(V₀))) ≤ κ·budget` at `V₀ = exceptionalSplitThreshold A`, and fit the two terms
  separately (design report, "Phase VI-9g as run", for the numerology). A2-IV-1′ is done
  (`LowBandTypicalSSharp.lean`).
- **VI-9g-2 (the sharp exceptional block).** In a new Conjectures leaf: the exceptional block of
  the schedule at `deltaU v := cellHalaszSharpBound x0 D δ₀ (A/qu v) ((A+Δ)/qu v) Pu restU` —
  `hdeltaU` from `norm_cellBlock_poly_le_cellHalaszSharpBound_of_top` at the top scale
  `N := 3(2A+1)` (it needs `3((A+Δ)/q) ≤ N`, and `3(A+Δ) ≤ 6A < 3(2A+1)`); the Prop's
  `NonPretentiousAt g A₀ (2A+1)` is lifted there by `nonPretentiousAt_scale_up` with `c = 3`, at
  strength `A₀/3`), `hdeltaU0` from `cellHalaszSharpBound_pos`, `hfitUCell` via
  `exceptionalCell_fit_of_schedule` with `Delta` from `cellHalaszSharpBound_le_explicit`. Then the
  schedule theorem `band_energy_typicalS_le_of_schedule_sharp` = `band_energy_typicalS_le_of_schedule'`
  with the exceptional block swapped (and, after 9g-1, the recut capstone). Hypotheses of the
  new schedule: `hNPtop : NonPretentiousAt g A₀ (2A+1)` (the Prop's clause, verbatim), `x0`, `D`,
  `δ₀`, the two range/strength inequalities, and the sharp fit
  `hscheduleUCellSharp : exceptionalCellScheduleCost (Aint_recut) (Bpri) (Γ_recut) (Δ_U) ≤ kappaU v·budget`
  with `Δ_U := 2^{J}(2ε' e^{2E_𝒰} + (log Bq + 1)(Aq/x0)^{−s} e^{2∑_{p∈𝒰} p^{−(1−s)}})`.
- **VI-9g-3 (the fixed-`ε` S6 numerology).** Report §5 "On S6 at fixed `ε`": free `(P_𝒰, Q_𝒰, N_𝒰)`
  with `log Q_𝒰/log P_𝒰 = C/ε³`, `N_𝒰 ≍ C/ε³`, `log P_𝒰 ≥ C(log T)^{3/4}` (Lemma 8),
  `N_𝒰·Q_𝒰 ≤ A` (erratum 10), `hBqCutoff` (erratum 11: `(A+Δ)/q_v ≥ x0` cell by cell — with
  `x0 = ⌈√(2A+1)⌉₊`-scale this needs `q_v·√(2A) ≲ A`, i.e. `Q_𝒰 ≤ √A/2`), `x0 := ⌈(N:ℝ)^{1/2}⌉₊` so
  the bridge loss is `≤ 2 log 2 + 24`, `s := 1/log Q_𝒰` (then `p^{−(1−s)} ≤ 1/2` for `p ≥ 4` and
  `e^{2∑ p^{−(1−s)}} ≤ e^{2e·E_𝒰}`), the tail `(Aq/x0)^{−s} ≤ exp(−(log A − log(2Q_𝒰√(2A+1)))/log Q_𝒰)`
  negligible once `log A ≥ C·log Q_𝒰·(1 + E_𝒰 + log(1/ε))`, `ε' := ε⁶/(C·2^{J} e^{2E_𝒰})`-scale so
  `Δ_U ≲ ε⁶`, `D := D₀(ε')`, `A₀ ≥ 3(2D + 2 log 2 + 24)`, and the fit
  `2(Δ_U² Bpri + 2Δ_U√(Aint_recut Bpri Γ_recut)) ≤ κ_U·budget` checked honestly against the recut
  shapes (the report's prefactor `≍ N_𝒰 (log Q/log P)²` and sift term `log P/log Q`). Produce the
  explicit `hschedule*` inequalities and prove them from the parameter choice; record every
  margin. Errata 12–14 of the A2-III report go into the design report.
- **A2-IV-1′ (re-price the low band).** `integral_norm_typicalS_dirichlet_poly_sq_le_low_band`
  with the `W`-lossy cost replaced by `sharpTwistedDirichletCost` (via
  `sharp_halasz_twisted_dirichlet_block` — the frequency condition `|2πξ| ≤ (D/2)a` holds on the
  low band `|ξ| ≤ K ≍ C/ε³` for `a ≥ 10¹⁶` — or the windowed one) and its `ε`-form from
  `sharpTwistedDirichletCost_le_eps`; the `2^{J+1}` twists via `halaszWindowAt_levelFreeTwist_archTwist`
  or `nonPretentiousAt_levelFreeTwist`.
- **A2-IV-3** `SliceMeanSquareA2`'s mean-square clause from A2-IV-0..2 + 9g-2's capstone at `s = 1`,
  the density clause (§1 (iii)) and the level-prime clause from the instantiation.
- **A2-V-1..4** `hqcell*` weakened to nonempty cells with `ql j v := (cell).min'`; level one
  `P₁ = ⌈W^{25}⌉`, `Q₁ = ⌊h/W³⌋`, `J = 1`, e-adic data, `htop/hbot`, `hNbb`; the `hschedule*`
  numerics for level one (errata 9–11); the exceptional block at 9g-3. Finally
  `theorem sliceMeanSquareA2 : SliceMeanSquareA2` — a theorem, not an instance — and the card's
  checkbox. Its dependency cone must be exactly `{HalaszLargeValuesAssumption,
  PrimeLargeValuesAssumption}` + standard axioms: add the audit pin in `TrackCAxiomAudit.lean`.

## 4. Numerology the units must respect

- `E_P ≥ 8·#levels/εc` per level for the density clause; `h₁(εc) ≈ exp(exp(16/εc)·125)`;
  `E_𝒰 ≍ log(C/ε³)` is a condition on the fixed-`ε` S6.
- The level primes exceed `C(log h)^B`: `W ≥ (log h)^{B'}`, `P₁ = W^{25}` (slack to `W^{21}`).
- `hNbb`/`hNuQ`: `N_j·Q_j ≤ A`, `N_𝒰·Q_𝒰 ≤ A`. `hBqCutoff` at the new cutoff `x0 ≈ √N`.
- The twist range: `2πT + 2π(halaszM N + 1) ≤ A₀·N` with `T = K₂ + 2 ≍ A/H·polylog` and
  `halaszM N ≈ (log N)⁴`: true for `A₀ ≥ 7`-ish once `A ≥ A₀`; check `halaszM_band_le`'s style.
- The bridge strength: `2D ≤ A₀/3 − 2(loglog N − loglog x0 + 12)`, with `x0 ≥ √N` giving
  `loglog N − loglog x0 ≤ log 2`.
- Read `c₃''` off `slice_energy_le_of_bands`, not off the report (§10 of the design report).

## 5. Deliverables

Commits per unit with findings in the bodies; `CODEX_REPORT.md` at the end (statements verbatim,
per-unit findings, "Accounting discrepancies found", "Work left undone and exact blocker",
final `lake build MoltResearch.DiscrepancyAnalytic Conjectures` exit code). Never push, never
merge, never rebase.
