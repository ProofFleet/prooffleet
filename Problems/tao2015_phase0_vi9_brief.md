# Track R — Phase 0 "VI-9": the exceptional-leg re-cut that discharges `SliceMeanSquareA2`

**Status (2026-09-05).** The R6/R7 chain is complete: `edp_of_sliceMeanSquareA2`
(`Conjectures/C0002_erdos_discrepancy/src/TrackCStage5MajorArcEDP.lean`, audit-pinned) gives the
Erdős discrepancy theorem on exactly the Prop `SliceMeanSquareA2`
(`TrackCStage5MajorArcA2.lean`). This brief is the design for discharging that Prop. It is
written for a Codex-scale run (one worktree, phase PRs), following the process that closed
VI-2/VI-5/VI-6/VI-8 (`Problems/tao2015_a1_r6r7_design_report.md` §8, "Phase 0"; the four
findings A–D of that report are the reason this re-cut exists).

## 0. Ground rules for the run

- Git worktree on a fresh branch from `origin/main`; `.lake` symlinked to the main checkout's
  prebuilt build directory. **Never `lake update`, never build Mathlib, never `lake exe cache
  get`.** Typecheck one file with `lake env lean <file>`; after editing a nucleus module rebuild
  its olean (`lake build MoltResearch.Discrepancy.<Mod>`) before typechecking a downstream file.
- `MoltResearch/` and `Solutions/` admit no `sorry`/`axiom`/`unsafe` (grep-enforced, comments
  included). New nucleus lemma bundles go in **new leaf files** under `MoltResearch/Discrepancy/`,
  each registered by one import line in `MoltResearch/DiscrepancyAnalytic.lean`; never append to
  `BandSchedule`, `WindowTK`, `WindowAssembly`, `PlancherelHarness`. Conjectures files import the
  narrowest nucleus module, never `MoltResearch.DiscrepancyAnalytic`.
- One unit per commit, commit before touching the next file. Record honestly (in the
  docstring and in a `## Findings` section of the run log) every leg whose fit fails as
  stated: the point of Phase 0 is to make the true accounting visible, not to force it.
- Both large-values interfaces (`HalaszLargeValuesAssumption` = IK 9.6,
  `PrimeLargeValuesAssumption` = MR Lemma 8, `Conjectures/…/Interfaces/LargeValues.lean`) may
  be used in the shape they are stated (`𝒯` an arbitrary `1`-separated finset in `[−T, T]`).
  No instance of either may be declared.

## 1. The target, transcribed

`SliceMeanSquareA2` (`TrackCStage5MajorArcA2.lean`):

```
∀ εc > 0, ∀ B (C > 0), ∃ h₁ (C₁ > 0) k, ∀ ε > 0, ∀ h ≥ h₁ with C₁/ε^k ≤ h,
  ∃ levels A₀ ≥ 1,
    (∀ P ∈ levels, ∀ p ∈ P, p.Prime) ∧
    (∀ P ∈ levels, ∀ p ∈ P, C·(log h)^B < p) ∧
    (∀ A ≥ A₀, ∑_{n∈(A,2A], ¬𝒮 n} 1/n ≤ εc·∑_{(A,2A]} 1/n) ∧
    (∀ A ≥ A₀, ∀ g CM 1-bounded with g 1 = 1 and NonPretentiousAt g A₀ (2A+1), ∀ J ≤ A,
       ∑_{n∈(A,A+J]} ‖∑_{m∈(n,n+h]∩𝒮} g m‖²/n ≤ ε²h²·∑_{(A,A+J]} 1/n)
```

Three clauses to produce. (i) and (ii) are the instantiation's choice of levels (A2-V).
(iii) is `[mrt]` Lemma "excep" in the tree's shape: `window_typicalS_complement_le`
(`WindowTK.lean`) + Mertens (`log_log_le_sum_one_div_primesBelow`,
`sum_one_div_primesBelow_le_sharp`) once every level has prime mass `E_P ≥ 8·#levels/εc`;
since `εc` is fixed, `h₁` may be as large as `exp(exp(16/εc)·125)`. (iv) is the mean square:
`slice_energy_le_of_bands` (`SliceA2.lean`, A2-IV-0) fed by the inner-band capstone
`band_energy_typicalS_le_of_schedule` (`TrackCStage5InnerBandSchedule.lean`) — **whose
exceptional-cell fits are false under the honest accounting** (report §4–§5). That is what
VI-9 repairs. The `h`-threshold must be polynomial in `1/ε` (`C₁/ε^k ≤ h`), because the wrapper
takes `ε ≍ ε₀/(log H)^B`; the level-one fit (`Q₁ = h/W³ ≥ P₁^{1+}`) and the low band give that.

## 2. What is on main (do not rebuild)

- Capstone `band_energy_typicalS_le_of_schedule` (Schedule file): every fit is a
  `hschedule*` inequality in schedule parameters. Its conclusion is the **weighted** energy
  `∫_{K₁≤|ξ|≤K₂} ‖F‖²·w ≤ bandBudget c₃ ε ρ` with `w ≤ (4H/A)²` (`hwsup`); the exceptional
  share enters through `hscheduleUShare : … ≤ (1/2^{J+1})/(4H/A)²`.
- Consumer `slice_energy_le_of_bands` (`SliceA2.lean`): inner band as a weight-quantified
  hypothesis; with `h m = 1_𝒮(m)·g m·(A/m)` the plain polynomial is `A·F_norm`, so the inner
  band must deliver `∫‖F_norm‖²·w ≲ (H/A)²·ε²·(s/A)/6`, i.e. `bandBudget` at
  `c₃'' = (4H/A)²·c₃_report` (report §4).
- The exceptional level: `norm_cellBlock_poly_le_cellHalaszBound` (Assembly file, VI-7-1),
  `cellHalaszBound`/`cellHalaszThreshold`/`pSmoothHarmonicMass`/`levelFreeTwist`/
  `nonPretentiousAt_levelFreeTwist` (`CellHalasz.lean`), the schedule forms
  `exceptionalCellScheduleCost`, `exceptionalIntegerSchedule`, `exceptionalPrimeSchedule`,
  `exceptionalRatioSchedule`, `exceptionalDeltaSchedule` (Schedule file).
- Large values: `measure_large_prime_poly_le` (`WindowTK.lean`, the `ℓ`-th moment measure
  bound), `norm_deriv_dirichlet_kernel_le` (`WindowAssembly.lean`), the unit-cell sampling of
  VI-1d-1, `bandCells`/`card_cells_le` (`BandCapstone.lean`).
- Level structure: `firstPrevLargePart_*` (`LevelLegs.lean` :1983–2066: measurable, subset of
  `bandPartOn`, large, pairwise disjoint, cover), `bandPartOn`.
- Halász: `cheap_halasz_twisted` (`HalaszAssembly.lean` :1730), `halaszBudgetShell`
  (`WindowAssembly.lean`), the GHS `𝒯₀` leg (#3368–#3373 — audit its `LL` factors),
  `pretentiousDistSq_twist_ge` (`Repulsion.lean` :222, mid regime).
- Low band: `low_band_block_sup` (`WindowAssembly.lean` :1488), `sum_typicalS_eq_inclexcl`
  (`TypicalFactorization.lean` :1322, `2^{J+1}` terms).

## 3. The units (report §8 Phase 0, with the R6/R7-era corrections)

Dependency: `9a → 9b → 9c → 9d ; 9e ; 9f (needs the R3 far-regime lemma) → 9g ; A2-IV-1 →
A2-IV-2 → A2-IV-3 after 9g`. Ship 9a–9e first; 9f is the research risk — attempt the
mid-regime part, record the far regime as a named hypothesis if it does not close.

- **VI-9a** (accounting wrapper, Schedule file): `band_energy_typicalS_le_of_schedule'`
  concluding `≤ (4H/A)²·bandBudget c₃ ε ρ`, with the level fits verbatim and
  `hscheduleUShare' : 2·#I·∑κ_U + 2κ_rep + 2κ_coll ≤ 1/2^{J+1}` (no `/(4H/A)²`). Route: the
  existing proof's `hfitU` step is the only place the `(4H/A)²` enters (Schedule file :518);
  restate `hfitU` against `(4H/A)²·𝔅` and push the factor through `band_energy_typicalS_le_of_levels`
  by taking `c₃ := (4H/A)²·c₃` in that call **only for the exceptional leg's budget**, or, if the
  levels call cannot be split, by proving the wrapper from the capstone at
  `c₃' = c₃·(4H/A)²` and rescaling the level fits (`bandBudget` is linear in `c₃`). Two lines
  of algebra either way; the deliverable is the honest statement in the tree.
- **VI-9b** `card_large_prime_poly_pow_le` (new leaf): the cardinality `le:Rupest` for a
  `1`-separated set of cell maxima — `#{t ∈ 𝒯 : |Q(t)| > V}` from `measure_large_prime_poly_le`
  (`ℓ`-th moment of the prime polynomial `Q^ℓ`) and the unit-cell sampling of VI-1d-1
  (Gallagher/Sobolev step via `norm_deriv_dirichlet_kernel_le`). Target shape:
  `#𝒯 ≤ C·(N^ℓ + T)·(mass)^ℓ / V^{2ℓ}`-type with every constant named.
- **VI-9c** the exceptional cover: `#{cells of [−T,T] meeting bandPartOn … J} ≤
  ∑_{r∈I_{J−1}} #{cells with |Q_r| > small_r}` via `firstPrevLargePart_*` (a point of the
  exceptional part fails every level's cell estimate, in particular level `J−1`'s), then VI-9b
  at `k = ⌈log T/log P_{J−1}⌉`; feed the resulting `𝒯` to `HalaszLargeValuesAssumption` —
  the integer-support term becomes `Aint ≍ N`, not `T^{3/2}` (report §5 (B)).
- **VI-9d** the `𝒯_S/𝒯_L` split at `V₀ = (log A)^{−100}`: `|𝒯_L|` by VI-9b on the `𝒰` cell
  polynomial; the prime-support term `Γ` replaced by `|𝒯_L|·e^{−log P/(log 2T)^{3/4}}·(log 2T)²`
  (the `PrimeLargeValuesAssumption` shape, no `T/P`).
- **VI-9e** the pointwise `|R_v(t)|` via `cheap_halasz_twisted` on `levelFreeTwist g · n^{−2πit}`
  (no Abel factor `3 + 2πT`), smooth mass `exp(2∑_{p∈P} 1/p)`, the short branch priced by its
  own harmonic mass — replaces `cellHalaszBound`; keep `cellHalaszThreshold`.
- **VI-9f** the `t₁`-split: `t₁ := argmin` of the twisted distance over the band;
  `𝒯₀ := {|t−t₁| ≤ (log A)^{1/16}} ∩ band` by the GHS leg + `eq:T0claim`'s `1/(1+|t−t₁|)`
  integration; `𝒯₁` at strength `ρ·loglog u`, `ρ = 1/6 − 1/(3π)`, from `pretentiousDistSq_twist_ge`
  (mid regime `|t−t₁| ≤ (log A)^{20}`) + the far-regime equidistribution lemma (Erdős–Turán +
  the Track L `ζ`-bounds; **new**, the R3 remainder). If the far regime stalls: state it as a
  named hypothesis class with citation, list it in the interface registry, and close the rest.
- **VI-9g** the fixed-`ε` S6 (`log Q_𝒰/log P_𝒰 = C/ε³`, `N_𝒰 ≍ C/ε³`, `log P_𝒰 ≥ C(log T)^{3/4}`,
  `N_𝒰 Q_𝒰 ≤ A`) and the exceptional fits at it; errata 12–14 into
  `Problems/tao2015_a2iii_design_report.md`.
- **A2-IV-1** the low band `|ξ| ≤ K` for the `𝒮`-restricted polynomial: `sum_typicalS_eq_inclexcl`
  + `low_band_block_sup` per free twist (`nonPretentiousAt_levelFreeTwist`); `K ≍ C/ε³`.
- **A2-IV-2** the weight conversion `‖∑_{(n,n+H]} g m − (n/A)·∑_{(n,n+H]} g m·A/m‖ ≤ H²/n` and
  its `L²` form over a slice.
- **A2-IV-3** the Prop's mean-square clause from A2-IV-0..2 + VI-9's capstone, at `s = 1`;
  then the density clause (§1 (iii)) and the level-prime clause from the instantiation
  (A2-V-1..4: `hqcell*` weakened to nonempty cells with `ql j v := (cell).min'`; level one
  `P₁ = ⌈W^{25}⌉`, `Q₁ = ⌊h/W³⌋`, `J = 1`; `hschedule*` numerics with errata 9–11; the
  exceptional block at the fixed-`ε` S6). Finally `theorem sliceMeanSquareA2 : SliceMeanSquareA2`
  — a theorem, not an instance — and the card's checkbox.

## 4. Numerology the units must respect

- The `𝒮ᶜ` density needs `E_P ≥ 8·#levels/εc` per level: `E₁ ≍ log(log h/(125 loglog h))`
  gives `h₁(εc) ≈ exp(exp(16/εc)·125)`; `E_𝒰 ≍ log(C/ε³)` is a condition on the fixed-`ε` S6.
- The level primes must exceed `C(log h)^B` for the requested `B`: take `W ≥ (log h)^{B'}`,
  `P₁ = W^{25}`; the level-one `P`-fit has slack to `W^{21}` (report §9.1).
- `hNbb`/`hNuQ` (errata 10): `N_j·Q_j ≤ A`, `N_𝒰·Q_𝒰 ≤ A` — `N_j` cannot be chosen
  arbitrarily large. `hBqCutoff` (erratum 11): `(A+Δ)/q_v ≥ 10¹⁶` cell by cell.
- Read `c₃''` off `slice_energy_le_of_bands`, not off the report (§10).
