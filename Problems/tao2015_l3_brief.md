## RESUME NOTE (run 15) — read before anything else
Run 14 stopped at L3-5 with commit `342d74f7` (`TrackCStage5LadderNumerology.lean`): the exceptional part's share in the band partition is
`1/2^{J+1}` with `J = J(A₁) → ∞`, while the exceptional leg's total cost is a **fixed** positive constant — the recut's Cauchy–Schwarz over the
`#cells_U ≥ log Q_𝒰` cells multiplies `∑_v (prime parts) ≥ 64 d² E_𝒰/log Q_𝒰`, giving `≥ 128 d² E_𝒰` for `d ≍ ε'` — so no cell-share
distribution helps (`ladderExceptionalAggregate_prime_fit_forces_level_upper`). **This is a bookkeeping artifact, not a design failure:** the
partition shares `(fun j => 1/2^{j+1})` with the exceptional part at index `J` were chosen when `J` was fixed. Fix and continue:

- **L3-0.** In a new Conjectures file, state and prove `band_energy_typicalS_le_of_schedule_sharp_cells_wide'` = the wide capstone with the
  share vector `s j := if j = J then 1/2 else 1/2^{j+2}` (`∑_{j ≤ J} s j ≤ 1`): the ordinary hypothesis `hshare j : 2κ_main j + 2κ_repl j + 2κ_coll j ≤ 1/2^{j+2}`,
  the exceptional `hfitU : 2·#cells_U·(∑_v kappaU v)·bandBudget + 2(2·replacementEnergyBoundWide A Pu Nu T + 8·collisionEnergyBoundWide A Pu T) ≤ (1/2)·bandBudget`.
  The proof is the existing one with the share vector and its `≤ 1` lemma swapped (look at how `band_energy_typicalS_le_of_cellUniform_fit_recut_wide`
  passes `(fun j => 1 / 2 ^ (j + 1))` and `geometric_shares_le_one (J + 1)` to the partition lemma; write `shifted_shares_le_one J`). Do not modify
  the existing theorems.
- **Per-cell exceptional shares.** Take `kappaU v := (the left side of hfitUCell for v)/bandBudget` (so `hfitUCell` is an identity) and verify
  `hfitU` as the aggregate inequality: `2·#cells_U·∑_v cost_v + 2(…) ≤ (1/2)·bandBudget`. Use `#cell_v ≤ C_BT·PcU v/(Nu·log PcU v)` (Brun–Titchmarsh
  for the cell `(PcU, PcU·e^{1/(2Nu)}]`, `BrunTitchmarsh.lean`/`card_block_le`) so that `∑_v 64·(#cell_v/PcU²)·PcU/log PcU ≤ C/log P_𝒰`, hence
  `2·#cells_U·∑_v DeltaU²·(…)(1+Γ_v) ≤ C'·Nu·N_𝒰·DeltaU²` — a fixed constant; the V₀-parts contribute `≤ (log A₁)^{1.96}·(log A)^{−199}·… → 0`.
  Then `hfitU` reads `C'·Nu·N_𝒰·DeltaU² + o(1) ≤ c₃eps²/48`, a **fixed** condition on `ε'` (through `DeltaU ≤ 2(2ε'e^{12}N_𝒰 + tail) + RemU`): choose
  `ε' := eps·√c₃/(C''·N_𝒰^{3/2}·Nu^{1/2}·e^{12})` and `A₀` large. Record the constants.
- Everything else in this brief stands; the ordinary levels now fit against `1/2^{j+2}` (their savings are `Q_{j−1}^{−0.45}`, `P₀^{−2α₀}`).
- Then L3-6, A2-IV-3′, A2-V′ (`theorem sliceMeanSquareA2`), the audit pin. Stop rule unchanged (unbounded-in-`A₁` failures only).

# Track R — L3 brief: the ladder numerology, then A2-IV-3′, A2-V′ and `theorem sliceMeanSquareA2` (Phase 4, final)

**Ground rules:** `Problems/tao2015_vi9g_brief.md` §0 verbatim (no `sorry`/`axiom`/`unsafe` under `MoltResearch/`, `Solutions/`, not even in comments;
new nucleus lemmas only in new leaf files registered in `MoltResearch/DiscrepancyAnalytic.lean`; never edit `PlancherelHarness`, never append to
`BandSchedule`/`WindowTK`/`WindowAssembly`/`HalaszComplex`; no instances of `*Assumption` classes — `sliceMeanSquareA2` is a **theorem** under
`[HalaszLargeValuesAssumption] [PrimeLargeValuesAssumption]`; one commit per unit `Track R: <one line> (#3044, L3-<n>)` / `(A2-IV-3′)` / `(A2-V′-<n>)`;
never push/merge/rebase; `CODEX_REPORT.md` uncommitted). Read first: the design report `Problems/tao2015_a1_r6r7_design_report.md` §"Finding E"
(items 1–6) and §"Phase 4"; the reports `Problems/tao2015_r9_report.md`, `tao2015_l1l2_report.md`, and the S+X and L4 reports (their compiled
statements are what you instantiate); the target theorem `band_energy_typicalS_le_of_schedule_sharp_cells_wide` (L4-5) and its full hypothesis list;
`MoltResearch/Discrepancy/SliceA2.lean` (`slice_energy_le_of_bands`, A2-IV-0), `SliceWeightConversion.lean` (A2-IV-2), the split low band
(`TypicalSLadderSplit.lean`), the Prop `SliceMeanSquareA2` (`TrackCStage5MajorArcA2.lean`, R9 shape), `TrackCAxiomAudit.lean`.

**Run-13 corrections to keep in mind.** The MVT closed forms are normalised by `∑‖c_n‖²/n` (so `replacementEnergyBoundWide`, `collisionEnergyBoundWide`
are `O(1)` shapes as displayed in §0′); the collars need `hqratio : N·p ≤ (N+1)·q`; empty cells get representative `1`.

**Stop rule.** Constants and parameter choices are yours (record every margin). Stop only when an inequality fails by a factor **unbounded in `A₁`**
after every admissible parameter choice; record it exactly and report. Do not enter A2-V′ while an L3 unit is open.

## 0. The quantities

Prop data: `εc > 0`, `B`, `C > 0` (outer), then `ε > 0`, `h` with `h₁ ≤ h`, `C₁/ε^k ≤ h` (inner). Scale window: `A₁ ≥ A₀`, `A ∈ [A₁, A₁²]`,
slice `A/2 ≤ J_s ≤ A` (write `Delta := J_s`, so `Delta/A ≥ 1/3`; `bandBudget c₃ eps ρ = c₃ eps² ρ/8 ≥ c₃ eps²/24`). Band constants from
A2-IV-0 (`slice_energy_le_of_bands`): `K₂ = γB'A/(2πh)`-type outer cutoff, `T := K₂ + 2 ≤ A` (state `hTA`), so `T/A ≤ c_T/h + 2/A` with a fixed `c_T`;
the schedule accuracy `eps` is fixed by A2-IV-3′ from `ε` (read `slice_energy_le_of_bands`' constants: `6·Einner ≤ (ε²/8)h²∑1/n`-type; take
`eps := min(eps(ε), 1/3)`, `hrho` holds). `α_j := innerBandScheduleAlpha j = 1/4 − (1/20)(1 + 1/(2(j+1)))` (`α₀ = 0.175`, `α_j ↑ 0.2`,
`Δα_j := α_j − α_{j−1} = 1/(40j(j+1))`, `β := α_{j−1}`). Shares: `ordinaryLegShare j = 3/(64·2^{j+1})`; the per-cell shares
`kappaCell j r := ordinaryLegShare j / #cells_{j−1}` (uniform), `#cells_j := (Ico (v₀l j) (v₁l j + 1)).card`.


## 0′. The target interface (as compiled by run 13 — `TrackCStage5InnerBandScheduleSharpCellsWide.lean`)

`band_energy_typicalS_le_of_schedule_sharp_cells_wide` has **exactly** these hypotheses (discharge each; the ordinary main terms are
*inputs*, not schedule fits):

* levels: `hJ : 0 < J`, `hPl`, `hPu`, `hPAu : ∀ p ∈ Pu, p*p ≤ A`, `hdisj`, `hdisjU`; cells `Nl v0l v1l ql alpha`, `hNl`, `hcovl`,
  `hqupl : (ql j v : ℝ) ≤ exp((v+1)/(2 Nl j))`, `hq1l`, `hqminl`, `hqratiol : Nl j * p ≤ (Nl j + 1) * ql j v` — all supplied for
  `ql j v := scaleCellRepresentative (Pl j) (Nl j) v` by `ScaleOnlyCellRepresentatives.lean` (`qup_of_ceil_or_one`, `one_le_scaleCellRepresentative`,
  `scaleCellRepresentative_le_mem`, `scaleCellRepresentative_ratio_le`, `two_mul_scaleCellRepresentative_le`); `alpha := innerBandScheduleAlpha`.
* band: `K1 K2 T`, `hT1`, `hTK2 : K2 + 2 ≤ T`; budget `c3 eps hc3`.
* **`hmain : ∀ j < J, ∫_{part j} ‖typicalSCellUniformMain … (ql j)‖² ≤ kappaMain j · bandBudget`** — for `j = 0` by
  `band_energy_level_one_main_le_budget_of_qup` (its `hfitT/hfitP` are the level-0 fits of §1); for `1 ≤ j < J` by
  `innerBand_later_level_main_cells` (L2) with the per-cell fit `hfit r` of §L3-1 and `hshares`.
* `hfitReplacementWide : ∀ j < J, 2·replacementEnergyBoundWide A (Pl j) (Nl j) T ≤ kappaReplacement j · bandBudget`, with
  `replacementEnergyBoundWide A P N T = e^π(T/A + 8)·32·(E_P/N + #P/A)`; `hfitCollisionWide : ∀ j < J, 8·collisionEnergyBoundWide A (Pl j) T ≤
  kappaCollision j · bandBudget`, with `collisionEnergyBoundWide A P T = e^π(T/A + 4)(2∑_{p∈P}1/p² + #P/A)`;
  `hshare : ∀ j < J, 2κ_main + 2κ_repl + 2κ_coll ≤ 1/2^{j+1}` (take `κ_main j := 1/2^{j+3}`, `κ_repl j := κ_coll j := 1/2^{j+4}`).
* exceptional: `Nu v0u v1u hNu hcovU qu hqupU hq1U hqminU hqratioU hLAU hLBU`, weight `w hwm hw0 hwsup`, `PcU hPcU hloU hhiU`, `ellU hellU`,
  `Vsplit lamU hVsplit hlamU` (`Vsplit v := exceptionalSplitThreshold A`, `lamU v := 1`), `x0 hx0 D delta0 A0 hD hdelta0 hdelta1 hA0 hNPtop
  hrangeSharp hstrengthSharp`, `DeltaU hDeltaU0`,
  **`hDeltaU : cellHalaszSharpBound x0 D delta0 (A/qu v) ((A+Delta)/qu v) Pu [Pl 0] + ladderSiftedLogMass (A/qu v) ((A+Delta)/qu v)
  ((List.range (J−1)).map (fun i => Pl (i+1))) ≤ DeltaU v`** (bound the sifted mass by `ladderBrunLogMassBound` — X's `_split_brun`
  route — and the sharp bound by `sharpRamareCost_le_eps` as in §L3-5),
  **`hfitUCell : ∀ v, 2·(Vsplit v²·(64·((A+Δ)/qu v + #Kcov·√T)(log 2T + 1)·∑_{n≤(A+Δ)/qu v} ‖cellBlockCoeff …‖²/n²) + DeltaU v²·((64·∑_{p∈cell v}‖g p‖²/p²·PcU v/log PcU v)(1 + Γ_v))) ≤ kappaU v · bandBudget`**
  where `#Kcov = (cellsMeetingSet (bandCells K2) (bandPartOn (levelSmallSet …) J band J)).card` is the **raw** cover cardinality: bound it by
  `card_cellsMeeting_exceptional_le_highMomentCost` (`TrackCStage5BandEnergyExceptionalReCut.lean`) at the level-`(J−1)` anchors with
  `ℓ_r = ⌈log 2T/log Panchor_r⌉₊ + 1`, i.e. by `sharpExceptionalCoverBound`-type sums, then §L3-4; the coefficient sums by
  `∑_{n≤B/q}‖cellBlockCoeff‖²/n² ≤ 2/((A/q)+1)` (`norm_cellBlockCoeff_le_one`, support `Ioc (A/q) (B/q)`, `∑_{n>a}1/n² ≤ 1/a`) and
  `∑_{p∈cell}‖g p‖²/p² ≤ #cell/PcU²` — copy the reductions from the proof of `band_energy_typicalS_le_of_schedule_sharp`,
  **`hfitU : 2·#cells_U·(∑_v kappaU v)·bandBudget + 2(2·replacementEnergyBoundWide A Pu Nu T + 8·collisionEnergyBoundWide A Pu T) ≤ (1/2^{J+1})·bandBudget`**
  (take `kappaU v := 1/(2^{J+4}·#cells_U²)`, so the first term is `2^{−J−3}`; the wide legs for `Pu` need `Nu ≥ C·E_𝒰·2^{J+4}/(c3 eps²)` and
  `∑_{p∈Pu}1/p² ≤ 1/P_𝒰 — trivial`).

The conclusion is the weighted inner-band energy `≤ (4H/A)²·bandBudget c3 eps (Delta/A)` — the `hinner` of `slice_energy_le_of_bands`.

## 1. Level 0 (`Pl 0`) — the Prop's bottom level

Parameters `P₀ Q₀ N₀ : ℕ`, `Pl 0 := (Ioc P₀ Q₀).filter Nat.Prime`, e-adic index range `v₀l 0 := ⌈2N₀ log P₀⌉₊ − 1`, `v₁l 0 := ⌊2N₀ log Q₀⌋₊`
(`htop/hbot`), representatives `ql 0 v := scaleCellRepresentative (Pl 0) N₀ v` (run 13: lower-endpoint ceiling on occupied cells, `1` on empty ones;
suppliers `qup_of_ceil_or_one`, `one_le_scaleCellRepresentative`, `scaleCellRepresentative_le_mem`, `scaleCellRepresentative_ratio_le`,
`two_mul_scaleCellRepresentative_le` — the raw `⌈e^{v/(2N)}⌉₊` does **not** satisfy `hqup` for small `v`). Constraints (prove each as an explicit inequality; then `∃ h₁ C₁ k, ∀ ε h, … → ∃ P₀ Q₀ N₀, …`):

* `C·(log h)^B < P₀` (level-prime clause) and `P₀ ≥ e^{256}` (so the dyadic cell mass `≤ 256/log Pmom ≤ 1` for every anchor).
* `hscheduleP0`: `(2N₀(log Q₀ − log P₀) + 2)·e^π log(2R)·4R·P₀^{−2α₀}e^{α₀/N₀}(N₀/α₀ + 1) ≤ (ordinaryLegShare 0/2)·c₃eps²/24` with `R = 2`:
  `P₀ ≥ (C₂·N₀²·E₀·log P₀/(c₃ eps²))^{1/(2α₀)}`, `E₀ := log(log Q₀/log P₀)`; polynomial in `1/eps`.
* `hscheduleT0`: `(2N₀(log Q₀ − log P₀) + 2)·e^π log 4·(2T e^{1/(2N₀)}/A)·Q₀^{1−2α₀}e^{…}(2N₀/(1−2α₀) + 1) ≤ (ordinaryLegShare 0/2)·c₃eps²/24`:
  with `T/A ≤ 2c_T/h`, `Q₀^{0.65} ≤ c₃ eps² h/(C₃ N₀² E₀ log P₀)`.
* Wide error legs (L4) at level 0: replacement `2·e^π(T/A + 2)·C₁(E₀/N₀ + #Pl 0/A) ≤ κ_repl,0·c₃eps²/24` — `N₀ ≥ C₄ E₀/(κ_repl,0 c₃ eps²)`;
  collision `8·e^π(T/A+2)(2∑_{p∈Pl 0}1/p² + #Pl 0/A) ≤ κ_coll,0·c₃eps²/24` — `P₀ log P₀ ≥ C₅/(κ_coll,0 c₃ eps²)` (`∑_{p>P₀} 1/p² ≤ 1/(P₀ log P₀)`-type).
* TK density of level 0 (the Prop's density clause, half of `εc`): `window_typicalS_complement_le` at `levels = [Pl 0]` gives
  `(E₀'·∑1/n + O(#Pl 0²/A))/E₀'²` with `E₀' = ∑_{p∈Pl 0} 1/p ≥ log log(Q₀+1) − log log(P₀+1) − 12` — the tree's **lower Mertens bound** `prime_Ioc_mass_lower_mertens`
  (`BrunIntervalSieve.lean`, run 12; `3 ≤ lo ≤ hi`). Require `E₀' ≥ 4/εc`: `log(Q₀+1) ≥ e^{4/εc + 12}·log(P₀+1)`; the `O(#Pl 0²/A)` term is `≤ Q₀²/A → 0`.
* Hence the `h`-threshold: `log h ≥ (1/0.65)·e^{4/εc + c_M}·log P₀ + log(C₃N₀²E₀ log P₀/(c₃eps²))` with `P₀ ≍ (1/eps)^{1/(2α₀)}·polylog(h)` —
  polynomial in `1/ε` with exponent `k(εc)`; record `k` and `C₁` explicitly.

## 2. The ladder `Pl j`, `1 ≤ j < J` — a fixed sequence

`ratio_j := ⌈2^j·C'/min eps εc⌉₊` (`C' := 64e^{12}`, see §3), `P_j := Q_{j−1}^{100j²}`, `Q_j := P_j^{ratio_j}` (ℕ powers; `log P_j = 100j² log Q_{j−1}`,
`log Q_j = ratio_j log P_j`), `Pl j := (Ioc P_j Q_j).filter Nat.Prime`, `N_j := ⌈C₄·E_j/(κ_repl,j c₃ eps²)⌉₊` with `E_j := log ratio_j + 12`
(upper Mertens, `sum_one_div_prime_Ioc_le_mertens`), `κ_repl,j := κ_coll,j := ordinaryLegShare j/8`, `κ_main,j := ordinaryLegShare j/2` (check `hshare j`'s exact form in the
`_cells_wide` theorem — it may carry `(4H/A)²`; adjust). Anchors `Pmom j r := ⌊exp(r/(2N_{j−1}))⌋₊` (so `Pmom < p ≤ 2Pmom` on cell `r`, since
`e^{r/(2N)} ≤ p < e^{(r+1)/(2N)} ≤ 2e^{r/(2N)}`), current data `A' j r v := A/ql j v`, `Delta' j r v := (A+Delta)/ql j v − A/ql j v`,
`ell j r v := ⌈log(2·ql j v·T/A)/log(Pmom j r)⌉₊ + 1`.

**L3-1 (the per-cell fit of `innerBand_later_level_main_cells`, scale-free).** For every `j ≥ 1`, `r`, prove (this is its `hfit r`;
the theorem then gives `hmain j` with `kappaMain j = ∑_r kappaCell j r`)
`#cells_j · ∑_v e^{−α_j v/N_j}/e^{−β r ℓ/N_{j−1}} · e^π(T/(Pmom^ℓ A') + 2^{ℓ+2}) · (ℓ!)²2^{ℓ+1}(ℓ+1)·mass_r^ℓ ≤ kappaCell j r · c₃eps²/24` by the chain
(each step a lemma):
1. `e^{−α_j v/N_j} ≤ p_v^{−2α_j} e^{α_j/N_j}` for `p_v := ql j v` (`hqup`: `p_v ≤ e^{(v+1)/(2N_j)}`; and `e^{v/(2N_j)} ≤ p_v` on nonempty cells —
   on an empty cell the representative is `1` and the cell polynomial vanishes, so that `v`-term of the fit only needs the trivial bound — but the fit
   as stated sums over all `v`; bound the empty-cell summands by their value at `p_v := 1`, or restrict the sum to occupied cells if the L2 theorem's `hfit`
   allows; record which).
2. `1/e^{−βrℓ/N_{j−1}} = (e^{r/(2N_{j−1})})^{2βℓ} ≤ (2Pmom)^{2βℓ}` and `Pmom^ℓ < Pmom²·(2q_vT/A)` (minimality of `⌈·⌉₊`), so
   `≤ 4^{βℓ}·Pmom^{4β}·(2q_vT/A)^{2β}`.
3. `T/(Pmom^ℓ A') ≤ 1` (`Pmom^ℓ ≥ 2q_vT/A`, `A' = A/q_v ≥ A/(2q_v)`).
4. `mass_r ≤ 1` (`sum_one_div_prime_dyadic_le`: `≤ 256/log Pmom ≤ 1` for `Pmom ≥ e^{256}`), `(ℓ!)² ≤ ℓ^{2ℓ}`, and with `L_j := log Q_j/log P_{j−1} + 2 ≥ ℓ`
   (from `q_v ≤ Q_j`, `T/A ≤ 1`, `Pmom ≥ P_{j−1}`): `4^{βℓ}2^{ℓ+2}2^{ℓ+1}(ℓ+1)ℓ^{2ℓ}e^π ≤ exp(ℓ(2 log L_j + 3) + 10)`, and
   `ℓ ≤ log(2q_vT/A)/log P_{j−1} + 2 ≤ log p_v/log P_{j−1} + 2` (`2T/A ≤ 1`).
5. Net per `(r, v)`: `≤ C_j·Pmom^{4β}·(2T/A)^{2β}·p_v^{−2α_j + 2β + (2 log L_j + 3)/log P_{j−1}}` with `C_j := e^{α_j/N_j + 2(2 log L_j + 3) + 10}`.
6. **Not too far:** `log P_{j−1} ≥ (2 log L_j + 3)/Δα_j` — then the exponent is `≤ −Δα_j`. For `j = 1` this is a condition on `P₀`:
   `log P₀ ≥ 160(2 log L₁ + 3)`, `L₁ = 100·ratio₁·ratio₀ + 2` — polynomial in `1/eps` (`(log L₁ = O(1/εc + log(1/eps)))`); for `j ≥ 2` it follows from
   `log P_{j−1} = 100(j−1)² log Q_{j−2} ≥ 100 log Q₀` once `log Q₀ ≥ 2j(j+1)(2 log L_j + 3)/(j−1)²·(1/100)·40`… — prove the general statement
   `∀ j ≥ 2, 80j(j+1)(2 log L_j + 3) ≤ 100(j−1)² log Q₀` from `log Q₀ ≥ C₆(1/εc + log(1/eps))·j`-type growth (`log L_j ≤ 2j + log(100C'²/(eps·εc)²) + 2`).
7. Sum over `v`: `∑_v p_v^{−Δα_j} ≤ e·P_j^{−Δα_j}(2N_j/Δα_j + 1)`; over `r`: `Pmom^{4β} ≤ Q_{j−1}^{4β}`, `#cells_{j−1}` terms — but the fit is **per `r`**
   with the uniform `kappaCell j r = ordinaryLegShare j/#cells_{j−1}`, so what must hold is
   `#cells_j·C_j·Q_{j−1}^{4β}·e·P_j^{−Δα_j}(2N_j/Δα_j + 1) ≤ (ordinaryLegShare j/#cells_{j−1})·c₃eps²/24`.
8. **Not too close:** `P_j^{−Δα_j}Q_{j−1}^{4β} = Q_{j−1}^{4β − 100j²Δα_j} = Q_{j−1}^{4β − 2.5j/(j+1)} ≤ Q_{j−1}^{−0.45}` (`4β ≤ 0.8`, `j ≥ 1`). The polylog
   factors (`#cells_j ≤ 2N_j ratio_j log P_j + 2`, `#cells_{j−1}`, `C_j`, `N_j`) are polynomial in `log Q_{j−1}`, `2^j`, `1/eps`, `1/εc`; prove
   `∀ j ≥ 1, polylog_j ≤ Q_{j−1}^{0.45}·ordinaryLegShare j·c₃eps²/24` from `log Q_{j−1} ≥ log Q₀ ≥ Λ(eps, εc)` for an explicit `Λ` (the `j = 1` case
   fixes `Q₀`; for `j ≥ 2`, `log Q_{j−1}` grows like `exp(Θ(j²))·log Q₀` while the polylog grows like `exp(O(j))`).
Record `Λ` and the resulting `P₀`-threshold; both feed §1's `h`-threshold (`Q₀ = P₀^{ratio₀}`).

**L3-2 (level data for all `j`).** `hPl`, `hPAl` (`Q_{J−1}² ≤ A`: polylog vs `A`), `hdisj` (`P_j > Q_{j−1}`), `hcovl`, `hqupl/hq1l/hqminl/hqratiol` (via `scaleCellRepresentative`), `hNl`, the wide replacement/collision fits
`hfitReplacementWide j`/`hfitCollisionWide j` (§0 constants: `N_j ≥ 32·9e^π·E_j·2^{j+4}·24/(c3 eps²)`-type, `∑_{p∈Pl j}1/p² ≤ 1/P_j` trivial,
`#Pl j/A ≤ Q_j/A → 0`), `hshare j`, and for `innerBand_later_level_main_cells`: `hA' hDelta' hSblk hPmom hlo hhi hell` per `(r, v)` and
`hshares`. (`hPAl`, `hLAl/hLBl`, `Pb/Kc/bb/aa/hNbb`, `hrho` are no longer hypotheses of the wide theorem.)

**L3-3 (how many levels).** `J(A₁) := Nat.find (∃ j, (log A₁)^{40} ≤ P_j) + 1` (`P_j ≥ 2^{2^j}`-type growth gives existence; `J ≥ 1`;
`J ≥ 2` for `A₁` large since `P₀` is fixed). Bounds: `P_{J−1} ≥ (log A₁)^{40}`, and `P_{J−1} = Q_{J−2}^{100(J−1)²} < (log A₁)^{40·ratio_{J−2}·100(J−1)²}`
when `J ≥ 2`, so `log Q_{J−1} ≤ 4000(J−1)² ratio_{J−1} ratio_{J−2} loglog A₁`; `J(A₁) ≤ 2 + √(2 log(40 loglog A₁)/log 2)`-type (from
`log P_j ≥ 2^{j(j−1)/2} log P₀`) — prove `J(A₁) ≤ loglog A₁` (crude) and `log Q_{J−1} ≤ (loglog A₁)^{C₇}`, hence `Q_{J−1}^2 ≤ A₁` and
`Q_{J−1} < P_𝒰(A₁)` for `A₁ ≥ A₀`.

## 3. The exceptional level `𝒰(A₁)` at the window

`P_𝒰 := ⌈exp((log A₁)^{49/50})⌉₊`, `N_𝒰 := ⌈e^{4/εc}⌉₊` (TK for its density: `1/E_𝒰 ≤ εc/4` with `E_𝒰 ≥ log N_𝒰 − 12 − o(1)` by `prime_Ioc_mass_lower_mertens`, so `N_𝒰 := ⌈exp(4/εc + 13)⌉₊`; or `no_factor_density_le_of_ratio` with `e^{−E_𝒰}`), `Q_𝒰 := P_𝒰^{N_𝒰}`,
`Pu := (Ioc P_𝒰 Q_𝒰).filter Nat.Prime`, cells with `Nu := 2`, representatives as in §1 (`hqupU`), `PcU v := ⌊e^{v/(2Nu)}⌋₊`, `ellU v := ⌈log(2T)/log(PcU v)⌉₊ + 1`,
`lamU v := 1`; anchors at level `J−1`: `PanchorU r := Pmom (J−1) r`-style `⌊e^{r/(2N_{J−1})}⌋₊`, `coverEllU r := ⌈log(2T)/log(PanchorU r)⌉₊ + 1`,
`coverLamU r := 1`; `V₀ = exceptionalSplitThreshold A = (log A)^{−100}`; `x0 := ⌈√(3(2A+1))⌉₊`, `s := 1/log Q_𝒰`, `ε'` and `D := max 1 (D₀ ε')`,
`delta₀ := ε'/(8e)` from `sharpRamareCost_le_eps ε'`; all for `A ∈ [A₁, A₁²]` (so `T ≤ A ≤ A₁²`, `log 2T ≤ 2.1 log A₁`, `loglog A ≤ loglog A₁ + 1`).

* **L3-4 (`hfitInt`).** `KcovBound = ∑_r 2·primeHighMomentCountCost (PanchorU r) (coverEllU r) (cell r) T (e^{−α_{J−1} r/(2N_{J−1})}) 1`. Per `r`:
  `(T+1)/Panchor^ℓ ≤ 1`; `V^{−2ℓ} = (e^{r/(2N)})^{2αℓ} ≤ (2Panchor)^{2αℓ} ≤ 4^{αℓ}(Panchor²·2T)^{2α}` (`Panchor^ℓ < Panchor²·2T`);
  `(ℓ!)² ≤ ℓ^{2ℓ} ≤ (2T)^{2 log ℓ/log Panchor}·…` with `ℓ ≤ log 2T/(40 loglog A₁) + 2` ⇒ `(ℓ!)² ≤ (2T)^{0.055}·e^{O(log ℓ)}` for `A₁ ≥ A₀`;
  `mass^ℓ ≤ 1`; `(1+λ) + (2π log((2P)^ℓ))²/λ ≤ 2 + 40ℓ²(log 2Panchor)²` polylog; `(1 + 2^{ℓ+1})4^{αℓ} = (2T)^{O(1/loglog A₁)}`. Hence
  `KcovBound ≤ #cells_{J−1}·polylog(A₁)·(2T)^{2α_{J−1} + 0.06} ≤ (2T)^{0.46+o(1)}` (`α_{J−1} < 0.2`). Then
  `2V₀²·64·((A+Δ)/q_v + KcovBound√T)(log 2T + 1)·2/((A/q_v)+1) ≤ 256V₀²·3(log 2T+1) + 256V₀²·(2T)^{0.96+o(1)}q_v(log 2T+1)/A`
  `≤ (log A)^{−200}(768 log 2T + A^{−0.04+o(1)}Q_𝒰·…) ≤ (kappaU v/2)·c₃eps²/24` for `A₁ ≥ A₀`, with `kappaU v := 2^{−(J+3)}/(2·#cells_U²)`-type
  shares fixed by `hscheduleUShare` (`2·#cells_U·∑_v kappaU v + 2κ_repl,U + 2κ_coll,U ≤ 1/2^{J+1}`); note `J = J(A₁)` grows, so the budget is
  `2^{−J(A₁)} ≥ 2^{−loglog A₁}`, which every saving here beats (`A^{−0.04}`, `(log A)^{−200}`, `1/log P_𝒰 ≤ (log A₁)^{−0.98}`).
* **L3-5 (`hfitPri`).** `Γ_v = cost(PcU v, ellU v, cell v, T, V₀, 1)·e^{−log PcU/(log 2T)^{3/4}}(log 2T)²`; `log Γ_v ≤ π + (ℓ+1) log 2 + 2ℓ log ℓ + log(2 + 40ℓ²(log 2PcU)²)
  + 200ℓ(loglog A₁ + 1) + 2 log(2.1 log A₁) − (log A₁)^{0.98}/(2.1 log A₁)^{0.75}` with `ℓ = ellU v ≤ 2(log A₁)^{0.02} + 3`; the saving exponent is
  `≥ 0.57(log A₁)^{0.23}` and dominates ⇒ `Γ_v ≤ 1` for `A₁ ≥ A₀` (`exists_exp_decay_le`/`exists_loglog_le_log` patterns of `HalaszSharpEps.lean`).
  Then `2·DeltaU v²·(64·#cell_v/PcU²·PcU/log PcU)(1 + Γ_v) ≤ 2·DeltaU v²·(128/log P_𝒰)·2 ≤ (kappaU v/2)c₃eps²/24` once
  `DeltaU v² ≤ kappaU v·c₃eps²·log P_𝒰/(24·1024)` — with `log P_𝒰 ≥ (log A₁)^{0.98}` this holds for `A₁ ≥ A₀` for **any** fixed `DeltaU`; so the
  exceptional pointwise bound only needs to be **bounded**: `DeltaU v := 2·(2ε'·pSmoothHarmonicMass(…) + tail) + RemU v` from `hDeltaU` (X-split with
  `base = [Pl 0]`): `sharpRamareCost_le_eps` gives `≤ 2ε'·pSmoothHarmonicMass B Pu + (log B + 1)(A/(q x0))^{−s}∏(1 − p^{−(1−s)})⁻¹`, and
  `pSmoothHarmonicMass B Pu = ∑_{n≤B, Pu-smooth} 1/n ≤ ∏_{p∈Pu}(1 − 1/p)⁻¹` (`sum_pSmooth_rpow_le_prod` at `s = 1`, `SmoothRankinTail.lean`) and
  `∏_{p∈Pu}(1 − 1/p)⁻¹ ≤ exp(∑_{p∈Pu} 1/p + ∑ 1/p²·…)` (`prod_inv_one_sub_le_exp`) `≤ e^{E_𝒰 + c_M} ≍ N_𝒰·e^{c_M}` by the **upper** Mertens
  bound (`sum_one_div_prime_Ioc_le_mertens`, `PrimeMassCell.lean`; `c_M = 12`) — a **fixed** constant (not `log Q_𝒰`), so `DeltaU v ≤ 2(2ε'e^{12}N_𝒰 + tail) + RemU v`
  is bounded uniformly in `A`, as required The tail `(A/(q x0))^{−s}` with `s = 1/log Q_𝒰`,
  `A/(qx0) ≥ √A/(3Q_𝒰)`: `exp(−(log A − log(6Q_𝒰√A))/log Q_𝒰) ≤ exp(−(log A₁)^{0.02}/(4N_𝒰))·… → 0`; `RemU v = ladderSiftedLogMass (A/q_v) ((A+Δ)/q_v) ladder ≤ ladderBrunLogMassBound … ks` (X's `_split_brun`), and with
  `ks L := ⌈e·E_L⌉₊`, `∏_{p∈L}(1−1/p) ≤ e^{−E_L} ≤ e^{12}/ratio_L` (lower Mertens): `RemU v ≤ ∑_{j≥1} (3e^{12}/ratio_j + 3·2^{−2ks−1}) + ∑_j 2(#Pl j+1)^{2ks}q_v/A
  ≤ 6e^{12}·eps/C' + o_A(1)`; with `C' := 64e^{12}` in `ratio_j := ⌈2^j·C'/min eps εc⌉₊` this is `≤ eps/10 + o_A(1)` (record every constant; all are fixed).
* **L3-6 (the rest of the exceptional data).** `hPu, hPAu (Q_𝒰² ≤ A), hdisjU (P_𝒰 > Q_{J−1}), hcovU, hqupU/hq1U/hqminU, hLAU/hLBU, hPcU/hloU/hhiU,
  hPanchorU/hloCoverU/hhiCoverU/hellCoverU/hlamCoverU, hellU/hlamU, hx0, hD, hdelta₀/hdelta₁, hA₀ (3 ≤ A₀), hrangeSharp (T ≤ A, halaszM N ≤ (log N)^4+2,
  A₀ ≥ 8), hstrengthSharp (x0 ≥ √N gives loglog N − loglog x0 ≤ log 2; A₀ ≥ 3(2D + 2log 2 + 24)), hAqU, hDeltaU0/hDeltaU (§L3-5), kappaU,
  hPminU/hQmaxU/hPulo/hPuhi/hNuQ (Nu·Q_𝒰 ≤ A), the wide replacement/collision fits for 𝒰 (`N_𝒰`-cells: `Nu ≥ C₄E_𝒰/(κ c₃eps²)` — take `Nu` accordingly
  instead of `2`), hscheduleUShare`.

## 4. A2-IV-3′ — the mean-square clause at the window

For `A ∈ [A₁, A₁²]`, `g` CM 1-bounded, `g 1 = 1`, `NonPretentiousAt g A₀ (2A+1)`, `A/2 ≤ J_s ≤ A`, with `levels(A₁) := Pl 0 :: ((List.range (J−1)).map (Pl ∘ succ)) ++ [Pu]`
(`= innerBandLevels Pl Pu J` up to `typicalS_perm`): `∑_{n∈(A,A+J_s]} ‖∑_{(n,n+h]∩𝒮} g‖²/n ≤ ε²h²∑1/n` from `slice_energy_le_of_bands` (its `hinner` from
`band_energy_typicalS_le_of_schedule_sharp_cells_wide` at §1–§3, `hlow` from the split low band — `integral_norm_typicalS_dirichlet_poly_sq_le_low_band_eps_split`
at `base = [Pl 0, Pu]` with the sieved remainder of §L3-5's type, `htot` trivial, the outer band and tail as in A2-IV-0) plus A2-IV-2's weight conversion.
Record the exact `eps(ε)` and every constant.

## 5. A2-V′ — the theorem

`theorem sliceMeanSquareA2 [HalaszLargeValuesAssumption] [PrimeLargeValuesAssumption] : SliceMeanSquareA2`: unfold; `h₁ C₁ k` from §1; for `ε, h` choose
`P₀ Q₀ N₀`, the ladder, `A₀ := max(...)` (the strength/scale/threshold list: §1–§3's `A₀`, `D`, `x0`-thresholds, `Q_{J−1}² ≤ A₁`, `Q_𝒰² ≤ A₁`,
`16·(…)`); for `A₁ ≥ A₀` produce `levels(A₁)` and the four clauses: primes; `C(log h)^B < p` (all levels above `P₀`); the density clause on `(A, 2A]` for
`A ∈ [A₁, A₁²]` (`window_typicalS_complement_le` at `[Pl 0]` and `[Pu]` — TK, `εc/4` each — plus S-3 for the ladder levels, `∑_{j≥1} 2/ratio_j ≤ εc/4`, and the
`(#L+1)^{2k}/A` remainders); the mean-square clause from §4. Then the audit pin in `TrackCAxiomAudit.lean`: `#print axioms sliceMeanSquareA2` must be
exactly the standard three plus the two interfaces' constants (state the theorem under the two classes, so no interface constant appears as an axiom —
check how the existing pins of `edp_of_sliceMeanSquareA2` are phrased and add the analogous guard), and **`FarRegimeRepulsionAssumption` must not appear**.
Then the card checkbox is done: `edp_of_sliceMeanSquareA2 sliceMeanSquareA2 : ErdosDiscrepancy`-type endpoint — add the unconditional theorem next to the
pins if the endpoint file structure allows (report exactly what was added).
