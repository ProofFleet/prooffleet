# Track R — L4 brief: the replacement and collision legs of a wide level as single polynomials (Finding E.5)

**Ground rules:** `Problems/tao2015_vi9g_brief.md` §0 verbatim (no `sorry`/`axiom`/`unsafe` under `MoltResearch/`, `Solutions/`, not even in
comments; new nucleus lemmas in a **new leaf file** registered by one import line in `MoltResearch/DiscrepancyAnalytic.lean`; never edit
`PlancherelHarness`, never append to `BandSchedule`/`WindowTK`/`WindowAssembly`/`HalaszComplex`; one commit per unit
`Track R: <one line> (#3044, L4-<n>)` (V1 commits as `L4-4`); never push/merge/rebase; `CODEX_REPORT.md` uncommitted). Read: the design report
`Problems/tao2015_a1_r6r7_design_report.md` §"Finding E" (item 5) and §"Phase 4"; `MoltResearch/Discrepancy/LevelLegs.lean`
(`typicalSCellReplacement`, `typicalSCollision`, `collisionEnergyBound`, `typicalSQuotCoeff`, `typicalS_level_leg_le_budget_of_collision_fit_middle`
and its `hreplacement`/`hcollisionFit`); `MoltResearch/Discrepancy/ReplacementSchedule.lean` (`replacementCost`, `replacement_endpoint_cost_pair`,
`eadic_replacement_error_le_budget_of_schedule`); the mean value theorem for Dirichlet polynomials of `MoltResearch/Discrepancy/DyadicMVT.lean`
(the `e^π((T+1)/A + …)`-shaped bound used by `band_energy_level_le_of_prev_large` and by the replacement/collision lemmas);
`Conjectures/…/TrackCStage5InnerBandAssembly.lean` (`innerBand_replacement_leg`, `innerBand_level_leg_of_main`).

## Why

The decomposition lemma `typicalS_level_leg_le_budget_of_collision_fit_middle` takes the level's replacement leg as an integral of the
polynomial `typicalSCellReplacement` over the part and its collision leg as `8·collisionEnergyBound`. Both current bounds price each
prime `p` of the level separately and apply the mean value theorem to a polynomial of length `A/p` (replacement: `replacementCost A N Q T =
e^π(2TQ/A + 4)(2/N)`) or `A/p²` (`collisionEnergyBound`: `e^π(T/(A/p²) + 8)`), so they carry `T·Q_j/A ≈ Q_j/h` and `T·Q_j²/A ≈ Q_j²/h`,
and `hscheduleReplacement`/`hscheduleCollision` can only hold for a level inside `[1, h^{1/2}]`. The ladder levels sit at
`P_j ≥ Q_{j−1}^{100 j²} ≫ h`. `[MR]` prices these errors as **one** Dirichlet polynomial supported on `(A, B]` (length `≍ A`), so the mean
value theorem loses only `T/A + O(1) ≤ 5`, and the coefficient mass is what it is: the collar mass `≍ E_j/(N_j A)` for the replacement, the
square-divisor mass `≍ 1/(A·P_j log P_j)` for the collision.

## L4-1 — the replacement polynomial as one Dirichlet polynomial (new leaf `MoltResearch/Discrepancy/WideLevelErrorLegs.lean`)

`typicalSCellReplacement g A B P rest N v₀ v₁ q ξ = ∑_v ∑_{p∈cell v} (g p/p)e(−log p·ξ)·(∑_{m∈Ioc(A/p, B/p)} c_m/m·e(−log m·ξ) − ∑_{m∈Ioc(A/q_v, B/q_v)} …)`
with `c_m = typicalSQuotCoeff g P (typicalS 0 B rest) m`, `‖c_m‖ ≤ 1`, `q_v ≤ p ≤ q_v·e^{1/(2N)}` (`hqmin`, `mem_eadicCell`).

* `typicalSCellReplacement_eq_dirichlet`: it equals `∑_{n ∈ Ioc A' B'} e_n/n · e(−log n·ξ)` for the collar range `A' := A/(…)`, `B' := B`
  — precisely: the difference of the two `m`-sums is `∑_{m ∈ Ioc(A/p, A/q_v)} − ∑_{m ∈ Ioc(B/p, B/q_v)}` (for `q_v ≤ p`; check the
  ℕ-division monotonicity), so `n = p·m` runs over `(A, A·p/q_v + p] ∪ (B, B·p/q_v + p]`-type collars; define `e_n := ∑_{v} ∑_{p ∈ cell v, p ∣ n,
  n/p ∈ collar_v(p)} g(p)·c_{n/p}·(±1)` and prove **`‖e_n‖ ≤ 1`** via the Ramaré weight: each of the `ω_P(n)` primes `p ∣ n` contributes at
  most `1/(ω_P(n/p) + 1)`, and `ω_P(n/p) + 1 ≥ ω_P(n)` whether or not `p² ∣ n`, so the sum is `≤ ω_P(n)/ω_P(n) = 1`. (The crude
  `‖e_n‖ ≤ ω_P(n) ≤ log n/log Pmin` is **not** acceptable: it costs `log A/log P_j`, unbounded in `A`.) State the exact support: `n ∈ Ioc A ⌊B·e^{1/(2N)}⌋ + …` — take the
  simplest correct superset, e.g. `n ∈ Ioc A (2B)` with `e_n = 0` off the collars.
* `replacement_coeff_mass_le`: `∑_n ‖e_n‖²/n² ≤ ∑_n ‖e_n‖/n² ≤ ∑_v ∑_{p∈cell v} ∑_{m ∈ collar_v(p)} 1/(pm)² ≤ ∑_{p∈P} (1/p²)·(#collar(p))·(p/A)²`
  with `#collar(p) ≤ 2(A/(N p) + 1) + …` (two collars of relative length `e^{1/(2N)} − 1 ≤ 1/N`), so the target shape is
  `≤ C₁·(E_P/(N·A) + #P/A²)`, `E_P = ∑_{p∈P} 1/p`, with an explicit `C₁` (about `8`) — **no** `log A` factor.
* `integral_norm_sq_typicalSCellReplacement_le`: `∫_{−T}^{T} ‖typicalSCellReplacement …‖² ≤ e^π·((T+1)/A + c)·∑_n ‖e_n‖²/n²` from the
  `DyadicMVT` mean value theorem applied once to the single polynomial (no per-`p` splitting), and the corollary
  `≤ e^π((T+1)/A + c)·C₁·(E_P/(N·A) + #P/A²)`; the set-integral version over any `G ⊆ Ioc (−T) T` (monotonicity of the set integral
  of a nonnegative integrand) is what `hreplacement` needs.

## L4-2 — the collision polynomial as one Dirichlet polynomial

`typicalSCollision g A B P rest ξ = ∑_{p∈P} ∑_{m : pm ∈ typicalS A B rest, p ∣ m} (g(pm)/(pm))e(−log(pm)·ξ)/ω_P(pm)`; as a polynomial in
`n = pm ∈ (A, B]`: `e_n = ∑_{p∈P, p² ∣ n} g(n)/ω_P(n)` (for `n ∈ typicalS A B rest`), so `‖e_n‖ ≤ #{p ∈ P : p² ∣ n}/ω_P(n) ≤ 1`.

* `typicalSCollision_eq_dirichlet`, `collision_coeff_mass_le`: `∑_{n∈Ioc A B} ‖e_n‖²/n² ≤ ∑_{p∈P} #{n ∈ Ioc A B : p² ∣ n}/A² ≤ ∑_{p∈P} ((B−A)/p² + 1)/A²
  ≤ (2/A)·∑_{p∈P} 1/p² + #P/A²` (state with `B ≤ 2A`).
* `integral_norm_sq_typicalSCollision_le`: `∫_{−T}^{T}‖typicalSCollision …‖² ≤ e^π((T+1)/A + c)·[(2/A)∑_{p∈P}1/p² + #P/A²]`, and the comparison
  lemma `collision_energy_single_le`: this bound is what replaces `8·collisionEnergyBound` — provide
  `collisionEnergyBound_alt`: a **new** closed form `collisionEnergyBoundWide A B P T := e^π((T+1)/A + c)·((2/A)∑_{p∈P}1/p² + #P/A²)` together
  with a variant of the nucleus lemma that assembles the level leg from `hcollisionFitWide : 8·collisionEnergyBoundWide … ≤ κ·budget`
  (find where `collisionEnergyBound` enters `typicalS_level_leg_le_budget_of_collision_fit` — the collision integral is bounded by it via
  "Weighted Cauchy–Schwarz assembles the repeated-prime collision"; restate that step with the single-polynomial bound. If the collision
  integral bound is a separate lemma with the integral on the left, only that lemma needs the variant).

## L4-3 — the Conjectures wrappers

In a new file `TrackCStage5InnerBandAssemblyWide.lean`: `innerBand_replacement_leg_wide` (hypothesis `hfitWide : 2·e^π((T+1)/A + c)·C₁·(E_{Pl j}/(Nl j·A) + #Pl j/A²) ≤ κ_repl·budget`)
and `innerBand_level_leg_of_main_wide` (collision via `collisionEnergyBoundWide`), then a schedule theorem variant is **not** required here — L3/L2
compose them; record the exact compiled hypotheses.


## L4-4 (unit V1 of the design report) — scale-only cell representatives (empty cells)

Every level-leg lemma demands `hqcell : ∀ v ∈ Ico v₀ (v₁+1), q v ∈ eadicCell P (2N) v`, which forces every e-adic cell to be **nonempty**
(`BandCapstone.lean`, the ⚠️ note before `setIntegral_norm_sq_cell_prime_block_le`). At width `e^{1/(2N)} < 2` no theorem in Mathlib or the tree
excludes empty cells (Bertrand needs width `2`; `ChebyshevBlock.lean` records that there is no lower Chebyshev bound), so the ladder
instantiation cannot supply `hqcell`. The proofs use the representative only through `quotient_scale_le_cell_scale`, i.e. through the
**upper** scale bound `(q v : ℝ) ≤ exp((v+1)/(2N))` (`eadicCell_bounds`' upper half) together with `hq1`, `hqA`, `hqmin` (vacuous on an
empty cell). Therefore:

* In the new leaf(s), state every lemma you copy or write with `hqup : ∀ v ∈ Ico v₀ (v₁+1), (q v : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ)))`
  in place of `hqcell` — provide `quotient_scale_le_cell_scale_of_le` (the existing proof with the membership step replaced by `hqup`), and
  copy-with-swap the level-one chain: `band_energy_level_one_le` (`WindowAssembly.lean:2726`, ≈80 lines — copy it into the new leaf, do not
  edit `WindowAssembly`), `setIntegral_norm_sq_cell_prime_block_le` (`BandCapstone`), and the three `LevelLegs` users (`…:1199`, `…:1385`,
  `band_energy_level_one_main_le_budget` at `…:1627`), plus whatever the exceptional recut chain (`band_energy_typicalS_le_of_cellUniform_fit_recut`
  → its nucleus lemmas) consumes from `hqcellU`. Name the variants `…_of_qup`. An empty cell contributes `0` to every polynomial (its
  `levelCellPoly` is an empty sum), so no bound changes.
* Provide the two trivial suppliers for the numerology: `qup_of_mem` (membership gives `hqup`) and `qup_of_ceil` (`q v := ⌈exp(v/(2N))⌉₊` satisfies
  `hqup` for `N ≥ 1`, together with `hq1` and — for `A ≥ 2e^{(v+1)/(2N)}` — `hqA`; `hqmin` holds for any representative below the cell, i.e.
  `⌈exp(v/(2N))⌉₊ ≤ p` for `p` in the cell).

## L4-5 — the combined schedule theorem

`band_energy_typicalS_le_of_schedule_sharp_cells_wide` in a new Conjectures file: `band_energy_typicalS_le_of_schedule_sharp_cells` (L2) with
(i) the replacement and collision hypotheses replaced by the wide fits of L4-1/L4-2 (for **all** levels `j < J` and for the exceptional level),
(ii) `hqcelll`/`hqcellU` replaced by `hqupl`/`hqupU`,
(iii) the exceptional pointwise bound through unit X's split: the hypothesis `hDeltaU` becomes
`∀ v, cellHalaszSharpBound x0 D delta₀ (A/qu v) ((A+Delta)/qu v) Pu [Pl 0] + RemU v ≤ DeltaU v`, where `RemU v` is the sieved remainder
`∑_{i ∈ range (J−1)} ∑_{n ∈ Ioc (A/qu v) ((A+Delta)/qu v), ∀ p ∈ Pl (i+1), ¬ p ∣ n} 1/n` (the ladder levels `Pl 1, …, Pl (J−1)` leave the
inclusion–exclusion; `J ≥ 1`), and the proof uses `norm_typicalS_quot_block_poly_le_sharp_split` (unit X, `MoltResearch/Discrepancy/TypicalSLadderSplit.lean`,
landed by run 12 — read its compiled statement) with `base = [Pl 0]`, `ladder = (List.range (J−1)).map (fun i => Pl (i+1))`
(`(List.range J).map Pl = Pl 0 :: …` for `J ≥ 1`, rotate as `typicalS_perm` allows). If `norm_typicalS_quot_block_poly_le_sharp` is applied inside a
nucleus lemma rather than in the schedule theorem, thread the split at that point (a `_split` variant of that lemma).
(iv) nothing else changed. This is the theorem the ladder numerology (L3) instantiates;
record its full hypothesis list in the report.

## Normalisation (record, do not prove)

The mean value theorem for `∑_{A<n≤B} a_n n^{−1−it}` gives `∫_{−T}^{T} ≲ e^π(T + B)·∑ |a_n|²/n²`, so with `B ≤ 2A` the two error legs are
`≈ e^π(T/A + 2)·C₁·(E_j/N_j + #P_j/A)` (replacement) and `≈ e^π(T/A + 2)·(2∑_{p∈P_j}1/p² + #P_j/A)` (collision) — `O(1)` quantities compared
with `κ·bandBudget ≈ κ·c₃ε²/24`, exactly like the existing level-0 fits (`hscheduleT0` has `2T·Qhi^{1−2α}/A`). With `T/A ≍ c/h ≤ 1` and
`E_j = log ratio_j`, the replacement leg needs `N_j ≳ E_j/(κ_j c₃ ε²)` and the collision leg `P_j log P_j ≳ 1/(κ_j c₃ ε²)`.

## Verification, report, stop rule

`lake env lean` new files; `lake build MoltResearch.DiscrepancyAnalytic Conjectures`; grep gates; `check_layering.sh`; aggregator coverage;
`#print axioms` (standard three). Stop only if the polynomial identity cannot be established from the definitions (report the exact obstruction).
