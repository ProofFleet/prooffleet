# Track R — VI-9g phase 3 brief: the fixed-`ε` numerology at `Δ ≥ A/2`, then A2-IV-3, A2-V, `sliceMeanSquareA2`

**Status (2026-09-05, after PR #3690).** R8 made the target Prop honest: `SliceMeanSquareA2`'s mean-square clause
now quantifies over slices `A/2 ≤ J ≤ A` only (`Problems/tao2015_r8_report.md`; design report §"R8 as run").
Consequently every producer of the clause works with `Δ := J ≥ A/2`, i.e. `Δ/A ≥ 1/2` and
`bandBudget c₃ ε (Δ/A) ≥ c₃ε²/16` — a **fixed** budget — and Codex run 7's obstruction
(`…SharpNumerology.lean`: `hfitPri ⟹ A ≤ κc₃ε²·Δ·Pc·log Pc/(32ε'²)`) becomes the fixed condition
`ε'² ≤ κ·c₃·ε²·Pc·log Pc/64` (its R8-7 docstring note). On main: the sharp schedule
`band_energy_typicalS_le_of_schedule_sharp` (`TrackCStage5InnerBandScheduleSharp.lean` :442) with its two half-budget
fits `hfitInt`/`hfitPri`, the recut capstone, the sharp low band `integral_norm_typicalS_dirichlet_poly_sq_le_low_band_eps`,
A2-IV-0 (`slice_energy_le_of_bands`, `SliceA2.lean`), A2-IV-2 (`SliceWeightConversion.lean`), the density inputs,
the scale lifts. Ground rules: `Problems/tao2015_vi9g_brief.md` §0 verbatim; read also the phase-2 brief
(`Problems/tao2015_vi9g_phase2_brief.md`) §1 and its A2-IV-3/A2-V items, and this file supersedes its VI-9g-3′.

## 1. VI-9g-3′ — the fixed-`ε` S6 numerology (Conjectures leaf, e.g. `TrackCStage5InnerBandScheduleSharpFit.lean`)

Prove, as **existence statements**, the exceptional hypotheses of `band_energy_typicalS_le_of_schedule_sharp` from a
parameter choice, under `A / 2 ≤ Delta` (so `1/2 ≤ Delta/A`), for all `A ≥ A₀(ε, …)`:

- `hfitInt v`: `2·V₀²·64·((A+Δ)/q_v + KcovBound·√T)(log 2T + 1)·(2/((A/q_v)+1)) ≤ (κ_U(v)/2)·bandBudget c₃ ε (Δ/A)` with
  `V₀ = exceptionalSplitThreshold A = (log A)^{−100}`. Use `(A+Δ)/q_v ≤ 2A/q_v`, `2/((A/q_v)+1) ≤ 2q_v/A`, so the first
  summand is `≲ 256·V₀²·(log 2T+1)`; the second is `≲ 256·V₀²·KcovBound·√T·q_v·(log 2T+1)/A`. With
  `T ≤ K₂ + 2 ≤ A` (state the needed `hTA : T ≤ A`), `q_v ≤ Q_𝒰 ≤ √A`, and `KcovBound = sharpExceptionalCoverBound … ≤`
  a polylog (each `primeHighMomentCountCost` at the level-`J−1` anchors with `V = e^{−α r/(2N)} ≥ e^{−α}`-type; state
  the needed bound as a hypothesis `hKcov : KcovBound ≤ (log A)^{k}` with `k` a fixed natural, to be discharged in
  A2-V), everything is `≤ C·(log A)^{k+2}·(log A)^{−200}` — negligible against `c₃ε²/16·κ_U/2` once `A ≥ A₀`.
- `hfitPri v`: `2·Δ_U(v)²·(64·#cell_v/Pc_v²·Pc_v/log Pc_v)(1 + Γ_v) ≤ (κ_U(v)/2)·bandBudget`. Use `#cell_v ≤ Pc_v`
  (the cell is a set of primes in `(Pc_v, 2Pc_v]`; `hlo/hhi`), so the prime factor is `≤ 64/log Pc_v`; `Γ_v ≤ 1` once
  `e^{−log Pc_v/(log 2T)^{3/4}}·(log 2T)²·primeHighMomentCountCost(…, V₀, …) ≤ 1` — with
  `Pc_v ≥ P_𝒰 := ⌈exp((log A)^{49/50})⌉₊`, `T ≤ A`, the saving is `≤ exp(−(log A)^{49/50}/(log 2A)^{3/4})` and the
  count is `≤ (log A)^{200ℓ}·polylog` (take `ℓ := 1`), so `Γ_v ≤ 1` for `A ≥ A₀`; and `Δ_U(v) ≤ Δ_U` from
  `cellHalaszSharpBound_le_explicit` at `ε'` with `x0 := ⌈√(3(2A+1))⌉₊`, `s := 1/log Q_𝒰`,
  `Q_𝒰 := ⌈exp((C/ε³)(log A)^{49/50})⌉₊`: `Δ_U ≤ 2^{J}(2ε'e^{2E_𝒰} + (log(2A) + 1)·(A/(q_v x0))^{−s}·e^{2e·E_𝒰})` — the
  tail is `≤ (log 2A + 1)·exp(−(log A − log(2Q_𝒰√(6A+3)))/log Q_𝒰 + 2e·E_𝒰)`, and `log A/log Q_𝒰 = (ε³/C)(log A)^{1/50} → ∞`,
  so the tail is `≤ ε'` for `A ≥ A₀`. Then `hfitPri` reads `2·(2^{J}·3ε' e^{2E_𝒰})²·128/log Pc_v ≤ κ_U(v)·c₃ε²/32`, i.e.
  `ε' ≤ ε·√(κ_U c₃ log Pc_v)/(2^{J}·e^{2E_𝒰}·C')` — choose `ε' := ε/(2^{J+6}·e^{2E_𝒰})·√(κ_U c₃)` (all fixed) and `A₀`
  large. State the exact inequality you prove and its margin.
- The range/strength hypotheses: `2πT + 2π(halaszM(3(2A+1)) + 1) ≤ (A₀/3)·3(2A+1)` from `T ≤ A`, `halaszM N ≤ (log N)⁴ + 2`
  (`halaszM_band_le`'s style), `A₀ ≥ 8`; `2D ≤ A₀/3 − 2(loglog(3(2A+1)) − loglog x0 + 12)` with `x0 ≥ √(3(2A+1))`
  giving `loglog N − loglog x0 ≤ log 2`, so `A₀ ≥ 3(2D + 2log 2 + 24)` suffices, `D := max 1 D₀(ε')` from
  `sharpTwistedDirichletCost_le_eps`.
- `hBqCutoff`-type: `(A+Δ)/q_v ≥ x0` needs `q_v ≤ Q_𝒰 ≤ √A/3` — true for `A ≥ A₀` since `log Q_𝒰 = (C/ε³)(log A)^{49/50} ≤ (log A)/2 − 2`.
- Record every inequality with numbers; if one fails as stated, stop that branch and report (the stop rule).

## 2. A2-IV-3 — `SliceMeanSquareA2`'s mean-square clause at `s = 1`

From `slice_energy_le_of_bands` (A2-IV-0; read its hypotheses: inner band as a weight-quantified hypothesis at
`c₃'' = (4H/A)²c₃`, outer band `band_energy_outer_le`/`outer_le_budget`, low band, tail) + A2-IV-1′ (low band) +
A2-IV-2 (weight conversion) + §1's schedule (inner band): for `A ≥ A₀`, `g` CM 1-bounded, `g 1 = 1`,
`NonPretentiousAt g A₀ (2A+1)`, and `A/2 ≤ J ≤ A`: `∑_{n∈(A,A+J]} ‖∑_{(n,n+h]∩𝒮} g‖²/n ≤ ε²h²∑_{(A,A+J]} 1/n`.
The `h`-threshold must be polynomial in `1/ε` (`C₁/ε^k ≤ h`).

## 3. A2-V — the instantiation, and the theorem

As in the phase-2 brief §2: A2-V-1 (`hqcell*` on nonempty cells, `ql j v := (cell).min'`), A2-V-2 (level one
`P₁ = ⌈W^{25}⌉`, `Q₁ = ⌊h/W³⌋`, `J = 1`, e-adic data, `htop/hbot`, `hNbb`), A2-V-3 (level-one `hschedule*` numerics,
errata 9–11), A2-V-4 (the exceptional level `𝒰` at §1's parameters: `P_𝒰, Q_𝒰, N_𝒰 = ⌈C/ε³⌉₊`, cells, anchors,
`hKcov`), the density clause (`window_typicalS_complement_le` + Mertens, `E_P ≥ 8·#levels/εc`), the level-prime clause
(`C(log h)^B < p`). Finally **`theorem sliceMeanSquareA2 : SliceMeanSquareA2`** (a theorem, not an instance) and its
audit pin in `TrackCAxiomAudit.lean` (`#print axioms` must show exactly the standard three axioms plus the two
large-values interfaces' constants, i.e. the theorem is stated under `[HalaszLargeValuesAssumption]
[PrimeLargeValuesAssumption]`); `FarRegimeRepulsionAssumption` must not appear. Then the card checkbox.

## 4. Deliverables

Commits per unit (`Track R: <one line> (#3044, VI-9g-3′)`, `(A2-IV-3)`, `(A2-V-<n>)`), findings in bodies;
`CODEX_REPORT.md` as before; never push/merge/rebase.

## Amendments after runs 9a/9b (2026-09-05; design report §"Two calibration errors of the phase-3 brief")

1. **Budget floor.** `A / 2 ≤ Δ` in ℕ gives `Δ/A ≥ 1/3`, so the fixed floor is `bandBudget ≥ c₃ε²/24` (each half-fit
   at `/48`), not `/16` (`bandBudget_one_twenty_four_le_of_nat_half_le`, `half_bandBudget_fit_of_nat_half_le`).
2. **Moment order.** Not `ℓ := 1`: use `[MR]`'s `ℓ := ⌈log(2T)/log Pc⌉₊ + 1`, so `(T+1)/Pc^ℓ ≤ 1`; then
   `log Γ_v ≤ π + (ℓ+1)log 2 + 2ℓ log ℓ + ℓ log(3/2) + log(2 + 40ℓ²(log 2Pc)²) + 200ℓ·loglog A + 2 loglog 2T
   − log Pc/(log 2T)^{3/4}` (`λ := 1`, `∑_{Pc≤p≤2Pc}1/p ≤ 3/2`), and `Γ_v ≤ 1` for `A ≥ A₀` because
   `ℓ ≤ 2(log A)^{1/50} + 2` while the saving exponent is `≥ (log A)^{0.23}`. At `ℓ = 1` the fit is impossible
   (`time_scale_bound_of_fixed_split_moment_one_Gamma_le_one`).
3. **`𝒰` is not a level of the Prop's `levels`.** `levels := (List.range J).map Pl` (level one only). In A2-IV-3 split
   `𝒮 = 𝒮'(A) ⊔ (𝒮 ∖ 𝒮'(A))`, `𝒮'(A) = typicalS … (innerBandLevels Pl (Pu A) J)`: the `𝒮'` part by §1–§2 at
   accuracy `ε/2`; the sifted part by `‖∑ g‖² ≤ h·#((n,n+h]∩¬Pu)`, the sum swap (`2h ≤ A`) and
   `window_typicalS_complement_le … [Pu A]`, which needs `E_𝒰 ≥ 32/ε²`: hence `N_𝒰 := ⌈exp(64/ε²)⌉₊` in place of
   `⌈C/ε³⌉₊` throughout §1 (fixed constants only). A2-V-4 builds `Pu(A)` per block scale; the Prop's density and
   level-prime clauses involve level one only.
