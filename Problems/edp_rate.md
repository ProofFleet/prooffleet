# Problem Card: Erdős's discrepancy-growth conjecture (the EDP rate) — OPEN

Status: active (opened 2026-09-08). Research card: the target is an **open problem**; see §1 for what a PR may and may not claim.

## 0. One-line pitch

Erdős conjectured (Er64b, Er65b, Er81; recorded on erdosproblems.com/67) that the discrepancy of every ±1 sequence grows at least
logarithmically: for every `f : ℕ → {−1, 1}`,
`max_{m·d ≤ x} |∑_{k ≤ m} f(k d)| ≫ log x`.
Tao's theorem (formalized in this tree as `erdos_discrepancy_unconditional`) gives unboundedness with **no rate**; the best known
rate is McNamara (2021): `max_{m ≤ x} max_{d ≤ e^x} |∑_{k≤m} f(kd)| ≫ (log log x)^{1/484 − o(1)}` (note the wider range of `d`).
The modified-character sequences show `O(log x)` is attainable, so the conjecture is sharp if true. Erdős (Er85c) also asked
about the special case of multiplicative `f`.

## 1. Rules for this card (read with `AGENTS.md` and `Problems/nucleus_upstreaming.md` §1)

- Claim an item by branch `ra/<id>-<name>` + a **draft PR** titled `<id>: <item name>` before working; one item per agent at a time
  (a blocked draft does not count); check `gh pr list --state open --search "<id>"` first; respect `after:` prerequisites.
- Edit only the item's listed deliverables. No `sorry`/`axiom`/`unsafe` anywhere, including `Conjectures/` (the tree is sorry-free
  and stays so): an open statement is a `def … : Prop`, never a `theorem … := by sorry`; a strategy is a *conditional* theorem whose
  hypotheses are `*Assumption` classes with a docstring citing the memo that states them.
- **Honesty rules for research items.** A memo separates *known* (with citation), *conjectured* (by whom), and *our idea*
  (unproved). No PR title or body may claim the problem, or any bound, is proved unless the Lean theorem is in the PR and
  audit-pinned. Numerics must be reproducible from a committed script. If an item cannot be completed as specified, keep the draft
  and write the exact obstruction in the body (`Blocked:` line).
- PR metadata: `Card: Problems/edp_rate.md`, `Track: N/A`, `Checklist item: <verbatim>`. The conductor merges and ticks.

## 2. What the tree already has (the reason this problem is ours to try)

- `MoltResearch.Tao2015.erdos_discrepancy_unconditional`, standard axioms only, with explicit constants everywhere **except one
  step**: `exists_limit_law` in `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5FourierProof.lean` (a weak-* limiting law on
  the compact `PrimeData` space, §2 of Tao's paper). Issue #3019 ("Track Q") audited the whole chain for effectivity: every other
  layer is effective in form. PR #3022 (stale, July 2026) drafted function-form interfaces and the finite-scale target shapes
  `HasDiscrepancyRateBy` / `ExplicitEDPRateTarget` in `TrackQEffectiveInterfaces.lean`; reuse its ideas, not its bitrot.
- The Elliott/entropy-decrement step (`TrackCStage5Assembly.lean`) is stated non-asymptotically (`LogElliottNonasymptoticAssumption`,
  explicit `A₀`), the sieve (`PrimeQuadrupleCountAssumption`, `C = 2^40 e^30`), Halász–Montgomery, the zero-free region and
  Vinogradov's MVT are all explicit.

## 3. Decomposition — Phase 1 (four independent items; Phase 2 is written after A3)

- [x] A0: Formal statement — `Conjectures/C0003_edp_rate/src/Statement.lean`: `def HasDiscrepancyRateBy (g : ℝ → ℝ) : Prop := ∀ f, IsSignSequence f → ∀ x : ℝ, 2 ≤ x → ∃ d m : ℕ, 0 < d ∧ (m * d : ℝ) ≤ x ∧ g x ≤ |(apSum f d m : ℝ)|`, `def ErdosDiscrepancyRateConjecture : Prop := ∃ c : ℝ, 0 < c ∧ HasDiscrepancyRateBy (fun x => c * Real.log x)`, the McNamara-shaped statement (max over `d ≤ e^x`) as a second `def`, the multiplicative special case as a third, and a proved lemma `hasDiscrepancyRateBy_of_unbounded`-style sanity check connecting `HasDiscrepancyRateBy` to `¬ BoundedDiscrepancy` for constant `g` (so the definitions are exercised). Docstrings cite the sources. Deliverables: `Conjectures/C0003_edp_rate/src/Statement.lean`.

- [x] A1: Literature memo — `Problems/edp_rate_literature.md`: Erdős's formulations (Er64b, Er65b, Er81, Er85c), the `O(log x)` upper examples (Borwein–Choi–Coons; modified characters) with the exact constant, McNamara 2021 (statement, method, where the `1/484` comes from, the range of `d`), Tao 2015 §2 (why the limiting law is non-effective) and the Tao–Teräväinen / Konieczny-style quantitative Elliott results if any apply, computational EDP results (Konev–Lisitsa: discrepancy 2 is impossible beyond 1160, discrepancy 3 beyond 127 645), and a one-page "what stops each method". Every claim cited. Deliverables: `Problems/edp_rate_literature.md`.

- [x] A2: Numerics — `scripts/research/edp_rate_numerics.py` + `Problems/edp_rate_numerics.md`: for the modified-character sequences (period-3 and other small moduli) and for the best known low-discrepancy sequences, compute `D(x) = max_{md ≤ x} |∑_{k ≤ m} f(kd)|` for `x` up to `10^6`–`10^7` and report `D(x)/log x`; report the empirical constant and which `(d, m)` attain the max; anything that bears on the conjectured constant `c`. Reproducible from the script. Deliverables: `scripts/research/edp_rate_numerics.py`, `Problems/edp_rate_numerics.md`.

- [x] A3: Approach memo and reduction (after: A0) — `Problems/edp_rate_approach.md` + `Conjectures/C0003_edp_rate/src/Reduction.lean`: the finite-scale replacement of `exists_limit_law` (Q2 of #3019): state precisely, as `*Assumption` classes with docstrings citing the memo, the lemmas that would give `HasDiscrepancyRateBy g` for an explicit `g` from the tree's effective layers; prove in Lean the conditional theorem `discrepancyRate_of_assumptions : [classes] → HasDiscrepancyRateBy g` for a concrete `g` (iterated logs are acceptable for a first rate); list the lemma DAG with `after:` edges as the Phase-2 items. The memo says what is known, what is conjectured, and what is our idea. Deliverables: `Problems/edp_rate_approach.md`, `Conjectures/C0003_edp_rate/src/Reduction.lean`.

## 3b. Decomposition — Phase 2 (written 2026-09-08 from the A3 memo `Problems/edp_rate_approach.md`; same rules)

A3 isolated three interfaces — `FiniteFourierReductionAssumption`, `FiniteVanDerCorputRateAssumption`,
`FiniteBorweinChoiCoonsRateAssumption` — and proved `discrepancyRate_of_assumptions` giving the concrete piecewise rate
`10^-6 · (log log log x)^(1/500)` from them (deliberately below McNamara's endpoint). Its finding: approximate multiplicativity is not
the missing Track-Q repair; the gap is the **source budget** (keeping every invoked product `d·m ≤ x`). The memo's items B0–B6 are
renamed A4–A10 here (card B's identifiers are taken).

- [x] A4: Source-budget audit (after: A3) — a theorem recording, for every invocation inside `SpectralWindowBound`, the largest source product `d·m` in terms of the spectral parameters, usable without a global discrepancy hypothesis. Deliverables: `Conjectures/C0003_edp_rate/src/SourceBudget.lean`, `Problems/edp_rate_source_budget.md`.

- [x] A5: Finite Fourier package (after: A4) **(merged as #3773 → 17b8ac26 as a recorded obstruction, not an instance: `finiteFourierReduction_of_schedule` is proved conditional on the terminal-budget inequality `edpFourierSourceBudget x ≤ x`, and `exists_wrapFree_source_exceeds_of_schedule_failure` proves that inequality's failure is attained by a wrap-free progression outside `x`; the A3 schedule provides no such bound, so the construction or the A3 scale must change — see A5′)** — choose the spectral scale and modulus as functions of the outer `x`, prove every requested product is `≤ x`, and instantiate `FiniteFourierReductionAssumption` (or record the exact schedule obstruction as a `Blocked:` finding). Deliverables: `Conjectures/C0003_edp_rate/src/FiniteFourier.lean`.

- [x] A5′: Finite Fourier construction within the source budget (after: A5) **(merged: route (a) — the analysis cutoff is now the largest scale whose scheduled budget fits below `x`; `finiteFourierReductionAssumption_budgetSafe : FiniteFourierReductionAssumption` is an unconditional instance, audit-clean; coefficient revised to `10^-7`)** — replace the exponent-box spectral sampling by a construction whose every invoked product `m·d` is `≤ x`. Candidates to try in order, each with exact inequalities: (a) shrink the analysis cutoff so the primorial budget `cutoff · ∏_{p ≤ cutoff} p^(modSchedule − (log₂ cutoff + 1))` fits below `x` and recompute the moment control this buys (a weaker rate `g` is acceptable and should be stated); (b) McNamara's quantitative Fourier step as reconstructed in `Problems/edp_rate_literature.md` (what modulus and scale it uses and why its products stay below the horizon); (c) a wrap-tolerant window estimate that bounds the wrap-around contribution instead of forbidding it, so that a small modulus suffices. Deliver either an instance of `FiniteFourierReductionAssumption` (possibly for a revised `g`, in which case `edpTripleLogRate` and `discrepancyRate_of_assumptions` are revised in the same PR) or a memo proving all three routes fail with the exact inequality each violates. Deliverables: `Conjectures/C0003_edp_rate/src/FiniteFourierBudget.lean`, `Problems/edp_rate_fourier_redesign.md`, `Conjectures/C0003_edp_rate/src/Reduction.lean` (only if `g` changes).

- [x] A6: Function-form Elliott thresholds (after: A3) — replace the existential threshold of the nonasymptotic Elliott consumer by explicit threshold data and prove the finite van der Corput estimates with every touched moment index recorded. Deliverables: `Conjectures/C0003_edp_rate/src/ElliottThresholds.lean`, `Problems/edp_rate_elliott_thresholds.md`.

- [x] A7: Finite van der Corput package (after: A5′, A6) **(merged #3791 → b5130b0f as a recorded obstruction: `finiteVdCWindowScheduleFits_false` — `FinitePersistentPretentious` includes the top endpoint `X = L`, where A6's window needs `L + H ≤ L`; independent of cutoff growth; see A3′)** — fit `H`, the shift maximum, the Elliott window and `X₀` below the common cutoff and instantiate `FiniteVanDerCorputRateAssumption`. Deliverables: `Conjectures/C0003_edp_rate/src/FiniteVanDerCorput.lean`.

- [x] A8: Structured-branch threshold extraction (after: A3) — audit the Mertens / repulsion / zero-free / Euler-product chain into a function-form finite statement with truncation error and an explicit terminal scale. Deliverables: `Conjectures/C0003_edp_rate/src/StructuredThresholds.lean`, `Problems/edp_rate_structured_thresholds.md`.

- [x] A9: Finite structured package (after: A5′, A8) **(merged #3794 → b41cb3ee as a recorded obstruction: on every finite cutoff `L` the persistent-pretentious event is automatic (`X₀ = L`, `Q = T = 1`, `B = 2∑_{p<L} 1/p`), so the structured package would have to negate an automatic event, and A8's terminal scale is chosen after `B` and need not fit below `L`; the finite target lost the qualitative argument's cofinal tail; see A3′)** — show the terminal scale fits below the common cutoff and instantiate `FiniteBorweinChoiCoonsRateAssumption`. Deliverables: `Conjectures/C0003_edp_rate/src/FiniteStructured.lean`.

- [x] A3′: Interface repair at the finite endpoint (after: A7, A9) **(merged: policy-indexed classes; the `.budgeted` policy reserves the A6 window `X + H ≤ L`, caps `Q`, `T`, `B` by cofinal functions of the cutoff, and asks for one post-`K` accuracy; `discrepancyRate_of_assumptions` re-proved with the unchanged rate; Fourier instance re-established; the A7/A9 obstructions provably do not reproduce)** — the A3 reduction is mis-specified at the endpoint (Finding A-1: both packages block on the same defect). Revise `FinitePersistentPretentious` and the three classes in `Conjectures/C0003_edp_rate/src/Reduction.lean` so that (i) the persistent interval ends at `L − H_max` (or the moment bound carries slack through `L + H_max`) so every A6 window fits, and (ii) the pretentious parameters `(Q, T, B)` are capped by explicit functions of the cutoff fixed *before* the package, so the event is not automatic and A8's terminal scale must fit below the cutoff for all admissible `(Q, T, B)` — i.e. the interface retains a cofinal range after the package is fixed. Re-prove `discrepancyRate_of_assumptions` for the revised classes (a smaller rate `g` is acceptable, stated), and re-establish A5′'s Fourier instance against the revised Fourier class (`FiniteFourierBudget.lean`). Both obstruction theorems from A7/A9 must become *unprovable* for the revised interface by construction (explain why in the memo). Deliverables: `Conjectures/C0003_edp_rate/src/Reduction.lean`, `Conjectures/C0003_edp_rate/src/FiniteFourierBudget.lean`, `Problems/edp_rate_interface_repair.md`.

- [ ] A7′: Finite van der Corput package, revised (after: A3′) **(blocked, PR #3803 merging as a recorded obstruction — Finding A-3: the budgeted class is *false* as stated: at `x = 10^10` the source-budget cutoff is `≤ 2` while every admissible window has length `≥ 8`, so no `X₀ ≥ 1` fits; `not_finiteVanDerCorputRateAssumption_budgeted` kernel-checked via a deterministic Liouville law; fix = schedule-dependent `edpRateStart`)** — as A7 against the revised interface. Deliverables: `Conjectures/C0003_edp_rate/src/FiniteVanDerCorput.lean`.

- [ ] A9′: Finite structured package, revised (after: A3′) **(blocked, PR #3804 merging as a recorded obstruction — Finding A-2: capping `(Q, T, B)` is not enough; the structured route's terminal scale depends on the uncapped function-form `Xpair`, `Xzero` and t-cut witness; `budgetedCaps_do_not_force_structuredTerminalFit` kernel-checked; the exact required fit is `FiniteStructuredTerminalFits`)** — as A9 against the revised interface, with the terminal-scale fit proved for all admissible `(Q, T, B)`. Deliverables: `Conjectures/C0003_edp_rate/src/FiniteStructured.lean`.

- [ ] A3″: Second interface repair — fix Findings A-2 and A-3 together in `Conjectures/C0003_edp_rate/src/Reduction.lean` (read the obstruction files on the branches of PR #3803 `FiniteVanDerCorput.lean` and PR #3804 `FiniteStructured.lean` first; they need not be merged): (i) make `edpRateStart` schedule-dependent — the large-`x` branch may begin only once `edpAnalysisCutoff x ≥ X₀ + H_max(ε) + 1` for all admissible `ε`, with the inequality proved, so `not_finiteVanDerCorputRateAssumption_budgeted` cannot be reproduced; (ii) extend the budgeted policy to expose and cap the function-form `Xpair`, `Xzero` and t-cut witnesses of the structured route by explicit functions of the cutoff, and state the joint terminal maximum so that `FiniteStructuredTerminalFits` becomes provable for all admissible data (or prove it cannot and say why); re-prove `discrepancyRate_of_assumptions` (a smaller `g` acceptable, stated) and re-establish the Fourier instance. This is the last interface round budgeted on this card: if A7″ or A9″ block again, the card is parked with its ledger. Deliverables: `Conjectures/C0003_edp_rate/src/Reduction.lean`, `Conjectures/C0003_edp_rate/src/FiniteFourierBudget.lean`, `Problems/edp_rate_interface_repair_2.md`.

- [ ] A7″: Finite van der Corput package, second revision (after: A3″) — as A7′ against the A3″ interface. Deliverables: `Conjectures/C0003_edp_rate/src/FiniteVanDerCorput.lean`.

- [ ] A9″: Finite structured package, second revision (after: A3″) — as A9′ against the A3″ interface, with `FiniteStructuredTerminalFits` proved for all admissible data. Deliverables: `Conjectures/C0003_edp_rate/src/FiniteStructured.lean`.

- [ ] A10: Rate calibration and audit (after: A7″, A9″) — reconcile all threshold inequalities, lower the exponent or coefficient if the proved schedules require it, prove divergence of the final concrete rate, and pin the unconditional rate theorem (`#guard_msgs` on `#print axioms`); write the result section. Deliverables: `Conjectures/C0003_edp_rate/src/RateTheorem.lean`, `Problems/edp_rate_result.md`.

## 4. Milestones beyond Phase 1 (for orientation; items are written after A3)

M1 the first machine-checked EDP rate (any `g → ∞`); M2 a rate matching or beating McNamara's `(log log x)^{1/484}`; M3 the
multiplicative special case (Er85c) with `(log x)^c`; M4 the conjecture.

## 5. References / links

- erdosproblems.com/67 (problem page, with the growth conjecture and the McNamara bound in the remarks).
- Tao, *The Erdős discrepancy problem*, Discrete Analysis 2016:1 (arXiv:1509.05363); the logarithmically averaged Elliott paper
  arXiv:1509.05422.
- Issue #3019 (Track Q effectivity audit), PR #3022 (function-form interfaces, stale).
- `Problems/tao2015_a1_r6r7_design_report.md` (the formal chain, with constants).
