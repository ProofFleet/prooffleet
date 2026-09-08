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

- [ ] A1: Literature memo — `Problems/edp_rate_literature.md`: Erdős's formulations (Er64b, Er65b, Er81, Er85c), the `O(log x)` upper examples (Borwein–Choi–Coons; modified characters) with the exact constant, McNamara 2021 (statement, method, where the `1/484` comes from, the range of `d`), Tao 2015 §2 (why the limiting law is non-effective) and the Tao–Teräväinen / Konieczny-style quantitative Elliott results if any apply, computational EDP results (Konev–Lisitsa: discrepancy 2 is impossible beyond 1160, discrepancy 3 beyond 127 645), and a one-page "what stops each method". Every claim cited. Deliverables: `Problems/edp_rate_literature.md`.

- [ ] A2: Numerics — `scripts/research/edp_rate_numerics.py` + `Problems/edp_rate_numerics.md`: for the modified-character sequences (period-3 and other small moduli) and for the best known low-discrepancy sequences, compute `D(x) = max_{md ≤ x} |∑_{k ≤ m} f(kd)|` for `x` up to `10^6`–`10^7` and report `D(x)/log x`; report the empirical constant and which `(d, m)` attain the max; anything that bears on the conjectured constant `c`. Reproducible from the script. Deliverables: `scripts/research/edp_rate_numerics.py`, `Problems/edp_rate_numerics.md`.

- [ ] A3: Approach memo and reduction (after: A0) — `Problems/edp_rate_approach.md` + `Conjectures/C0003_edp_rate/src/Reduction.lean`: the finite-scale replacement of `exists_limit_law` (Q2 of #3019): state precisely, as `*Assumption` classes with docstrings citing the memo, the lemmas that would give `HasDiscrepancyRateBy g` for an explicit `g` from the tree's effective layers; prove in Lean the conditional theorem `discrepancyRate_of_assumptions : [classes] → HasDiscrepancyRateBy g` for a concrete `g` (iterated logs are acceptable for a first rate); list the lemma DAG with `after:` edges as the Phase-2 items. The memo says what is known, what is conjectured, and what is our idea. Deliverables: `Problems/edp_rate_approach.md`, `Conjectures/C0003_edp_rate/src/Reduction.lean`.

## 4. Milestones beyond Phase 1 (for orientation; items are written after A3)

M1 the first machine-checked EDP rate (any `g → ∞`); M2 a rate matching or beating McNamara's `(log log x)^{1/484}`; M3 the
multiplicative special case (Er85c) with `(log x)^c`; M4 the conjecture.

## 5. References / links

- erdosproblems.com/67 (problem page, with the growth conjecture and the McNamara bound in the remarks).
- Tao, *The Erdős discrepancy problem*, Discrete Analysis 2016:1 (arXiv:1509.05363); the logarithmically averaged Elliott paper
  arXiv:1509.05422.
- Issue #3019 (Track Q effectivity audit), PR #3022 (function-form interfaces, stale).
- `Problems/tao2015_a1_r6r7_design_report.md` (the formal chain, with constants).
