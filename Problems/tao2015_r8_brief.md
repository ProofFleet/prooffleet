# Track R — R8 brief: the honest slice quantifier of `SliceMeanSquareA2`

**Status (2026-09-05, after PR #3688).** Codex run 7 (`Problems/tao2015_vi9g_phase2_report.md`) proved that the
fixed-`ε` exceptional fit `hfitPri` forces `A ≤ κ·c₃·ε²·Δ·Pc·log Pc/(32ε'²)` at fixed slice length `Δ` — the
machine-checked symptom of a defect in the **target Prop**: `SliceMeanSquareA2` (`TrackCStage5MajorArcA2.lean` :54)
quantifies its mean-square clause over **every** slice length `J ≤ A`, which at `J = 1` is a pointwise
short-interval bound that `[mrt]` A.2 never asserts and that is false in general. Read the design report
`Problems/tao2015_a1_r6r7_design_report.md`, §"The slice quantifier of `SliceMeanSquareA2` is over-strong (R8)",
first: it has the diagnosis, the arithmetic, and the 5-step repair. This brief is that repair, unit by unit.
Ground rules: `Problems/tao2015_vi9g_brief.md` §0 verbatim. **This unit edits existing theorems of the audited
R6/R7 chain; every statement change must be the minimal one below, and `edp_of_sliceMeanSquareA2` plus the
three audit pins in `TrackCAxiomAudit.lean` must still compile with the same axiom set.**

## 1. The new Prop (the only change to `SliceMeanSquareA2`)

In `Conjectures/…/TrackCStage5MajorArcA2.lean` :54, the mean-square clause becomes

```
(∀ A : ℕ, A₀ ≤ A →
  ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → (∀ n, ‖g n‖ ≤ 1) → g 1 = 1 →
    NonPretentiousAt g A₀ (2 * A + 1) →
    ∀ J : ℕ, A / 2 ≤ J → J ≤ A →
      ∑ n ∈ Finset.Ioc A (A + J), ‖∑ m ∈ (Finset.Ioc n (n + h)).filter (HasFactorInAll levels), g m‖^2 / n
        ≤ ε^2 * (h : ℝ)^2 * ∑ n ∈ Finset.Ioc A (A + J), (1:ℝ)/n)
```

(`A / 2` is ℕ-division.) Everything else in the `def` is unchanged. This is weaker than the old clause, so
nothing that *produces* the Prop breaks; every *consumer* of the clause must be re-proved (§3).

## 2. The two analytic re-proofs (nucleus, `MoltResearch/Discrepancy/MajorArcAssembly.lean`)

Edit **in place** (the file is a Track R leaf; keep names, add hypotheses).

- **R6-5′ `logavg_le_of_meanSquare_dyadic`** (:~640). New statement:
  ```
  theorem logavg_le_of_meanSquare_dyadic (W : ℕ → ℝ) (hW : ∀ n, 0 ≤ W n) (ε h : ℝ) (hε : 0 ≤ ε) (hh : 0 ≤ h)
      (hWh : ∀ n, W n ≤ h) (A₀ N : ℕ)
      (hA2 : ∀ A J : ℕ, A₀ ≤ A → A / 2 ≤ J → J ≤ A → A + J ≤ N →
        ∑ n ∈ Finset.Ioc A (A + J), (W n)^2 / n ≤ ε^2 * h^2 * ∑ n ∈ Finset.Ioc A (A + J), (1:ℝ)/n)
      (a b : ℕ) (ha : A₀ ≤ a) (ha1 : 1 ≤ a) (hb_lo : 3 * a ≤ 2 * b) (hb4 : b ≤ 2 * a + 4) (hbN : b ≤ N) :
      ∑ n ∈ Finset.Ioc a b, W n / n
        ≤ ε * h * ∑ n ∈ Finset.Ioc a b, (1:ℝ)/n + 4 * h / ((2 * a + 1 : ℕ) : ℝ)
  ```
  Proof: keep `hsingle` (Cauchy–Schwarz on one block) but require `A/2 ≤ J`, i.e. in `hsingle a b` add
  `3 * a ≤ 2 * b` (then `J = b − a ≥ a/2`: `a / 2 ≤ b − a` by omega from `3a ≤ 2b`). Case `b ≤ 2a`: one block
  (its `3a ≤ 2b` is `hb_lo`), leftover `0 ≤ 4h/(2a+1)`. Case `b > 2a`: block `(a, 2a]` (`J = a`, `3a ≤ 4a` ✓,
  `2a ≤ N` from `hbN`) by `hsingle`, plus the leftover `(2a, b]` bounded **trivially**:
  `∑_{n∈(2a,b]} W n / n ≤ ∑_{n∈(2a,b]} h/(2a+1) = (b − 2a)·h/(2a+1) ≤ 4h/(2a+1)` (`hWh`, `n ≥ 2a+1`, `b − 2a ≤ 4`).
  Split with `Finset.sum_Ioc_consecutive` as now.
- **R6-6c′ `sum_div_comp_div_le_of_meanSquare`** (:~1027). New statement: add `(hWh : ∀ n, W n ≤ h)` and
  `(hεA₁ : 2 ≤ ε * A₁)`, change `hA2` to the `A' / 2 ≤ J →` shape; **conclusion unchanged** (`≤ 4 * (ε * h)`).
  Proof: as now, with the new R6-5′ at `a := (A+c)/d − 1`, `b := (2A+c)/d`, and
  * `hb_lo : 3 * a ≤ 2 * b` — from `Nat.add_div_le_add_div : x/d + y/d ≤ (x+y)/d` at `x = A`, `y = A + c`
    (`b ≥ A/d + (A+c)/d`) and `(A+c)/d ≤ A/d + c/d + 1` (`Nat.add_div`), `c ≤ A/3 ≤ A` so `c/d ≤ A/d`; omega
    after `generalize A / d = u; generalize (A + c) / d = v; generalize (2*A+c)/d = w; generalize c / d = t`;
  * `hb4 : b ≤ 2 * a + 4` — `(2A+c)/d = (A + (A+c))/d ≤ A/d + (A+c)/d + 1 ≤ 2·((A+c)/d) + 1` (`Nat.add_div`,
    `A/d ≤ (A+c)/d`), and `(A+c)/d ≥ 1`;
  * the harmonic mass of `(a, b]` is `≤ 2` (**not** `3`): every `n ∈ (a, b]` has `n ≥ a + 1 = (A+c)/d ≥ 4`
    and there are `b − a ≤ a + 4 ≤ 2(a+1)` points, so `∑ 1/n ≤ (a+4)/(a+1) ≤ 2` — replace `hharm … ≤ 3`;
  * the reindexing factor `4/3` (`sum_div_comp_div_le`) is unchanged; assemble
    `(4/3)·(2εh + 4h/(2a+1)) ≤ (8/3)εh + (16/3)h/(2a+1) ≤ (8/3)εh + (8/3)h/(a+1) ≤ 4εh` using
    `2 ≤ ε·(a+1)` from `hεA₁` and `A₁ ≤ a` (`(8/3)h/(a+1) ≤ (4/3)εh ⟺ 2 ≤ ε(a+1)`).
  Record in the docstring: "ratio just above 2, leftover ≤ 4 points priced trivially, `2 ≤ εA₁`".
- **R6-6d′ `sum_restricted_window_logavg_le_of_meanSquare`** (:~1104): `hA2` gains `A' / 2 ≤ J →`; add
  `(hεA₁ : 2 ≤ ε' * A₁)`; supply `hWh` to R6-6c′ from `norm_filter_block_le_card` (`W d χ n' ≤ h₀`: the window
  `(n', n'+h₀]` has `h₀` points, coefficients `χ·g` are `1`-bounded). Conclusion unchanged.
- Any other `hA2 : ∀ A J, … → J ≤ A → …` in the file (:652 is R6-5 itself) — none else expected; grep
  `J ≤ A' →` and `J ≤ A →` to be sure.

## 3. Threading (Conjectures)

- `TrackCStage5MajorArcA2.lean`: **R6-8 `majorArc_block_bound_restricted`** — `hA2` takes the new Prop shape
  (`∀ J, A / 2 ≤ J → J ≤ A → …`); add `(hε'A₀ : 2 ≤ ε' * A₀)`; at the instantiation site (:118) pass `hJ2` through
  (`hA2 A' hA₀A' … hnp' J hJ2 hJ`) and derive `2 ≤ ε'·(A/q − 1)` from `hε'A₀` and `⌈A₀⌉₊ + 1 ≤ A/q`
  (`A₀ ≤ ⌈A₀⌉₊ ≤ A/q − 1`, `ε' ≥ 0`).
- `TrackCStage5MajorArcMR.lean`: `good_block_total_le` (:45, its `hms`), `block_total_le_trichotomy` (:366, `hms`),
  `exists_wrapper_params` (:122 — the Prop-derived clause it *exports* now has the `A/2 ≤ J →` guard, weaker, fine),
  `majorArc_bound_of_A2_of_le_one` (:543), `matomakiRadziwillMajorArc_of_A2` (:696): thread `2 ≤ ε'·A₀` — in the
  wrapper's `set A₀ : ℝ := 8 * (Q * M + 50 + 2 * Real.log (64 / ε)) + Real.exp K` (:576) add the summand
  `256 * Q / ε` (so `A₀ ≥ 256Q/ε` gives `2 ≤ (ε/(128Q))·A₀`; the wrapper's `ε' = ε/(128Q)`); `hms`
  hypotheses take the `A / 2 ≤ J →` shape. `TrackCStage5MajorArcEDP.lean` and `TrackCAxiomAudit.lean` should
  compile unchanged (they name the Prop); if a pin's `#print axioms` output changes, stop and report.
- `Conjectures/…/TrackCStage5InnerBandScheduleSharp*.lean` are unaffected; the producers (`slice_energy_le_of_bands`,
  A2-IV-3, not yet written) now get `Δ = J ≥ A/2`, i.e. `Δ/A ≥ 1/2` — record this in a one-line docstring note in
  `…SharpNumerology.lean` ("with `J ≥ A/2` the forced bound is `A ≤ … ·(A/2) …`, i.e. a fixed condition
  `ε'² ≤ κc₃ε²·Pc·log Pc/64`").

## 4. Verification and deliverables

`lake build MoltResearch.Discrepancy.MajorArcAssembly` after §2; `lake build Conjectures` after §3; the five gates;
`lake build MoltResearch.DiscrepancyAnalytic Conjectures` at the end; **`python3 scripts/check_interfaces.py` and the
audit file must report the same axiom sets as before** (compare `#print axioms` of `edp_of_sliceMeanSquareA2`
before/after in the report). One commit per bullet of §2–§3 (`Track R: <one line> (#3044, R8-<n>)`), findings in
bodies; `CODEX_REPORT.md` as before; never push/merge/rebase. If a floor inequality resists `omega`, generalize
the quotients first (`generalize A / d = u at *`).
