# Track R — R9 brief: the `[mrt]` `X₀`-shape of `SliceMeanSquareA2` (levels per scale window `[A₁, A₁²]`)

**Ground rules:** `Problems/tao2015_vi9g_brief.md` §0 verbatim (no `sorry`/`axiom`/`unsafe` under `MoltResearch/`,
`Solutions/`; never edit `PlancherelHarness`, never append to `BandSchedule`/`WindowTK`/`WindowAssembly`/`HalaszComplex`;
no instances of `*Assumption` classes; one commit per unit `Track R: <one line> (#3044, R9-<n>)`; never push/merge/rebase;
`CODEX_REPORT.md` uncommitted at the end with statements, findings, verification). Read first: the design report
`Problems/tao2015_a1_r6r7_design_report.md` §"Finding E" and §"Phase 4", the R8 report `Problems/tao2015_r8_report.md`
(the previous re-thread of the same consumers), `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5MajorArcA2.lean`
(the Prop and R6-8), `TrackCStage5MajorArcMR.lean` (R7), `TrackCAxiomAudit.lean` (the pins).

## Why

`[mrt]` (1503.05121, App. A, before Theorem A.2): "let `X₀` be a quantity with `√X ≤ X₀ ≤ X` … `J` the largest index with
`Q_J ≤ exp((log X₀)^{1/2})`" — the set `𝒮` is chosen from a fixed level sequence but its length depends on the scale, and
one choice serves every `X ∈ [X₀, X₀²]`. Finding E shows the discharge needs this: the exceptional cover's anchor level
must sit at height `(log A)^{40}`, so the level list cannot be fixed before `∀ A`. The current Prop fixes `levels` before
`∀ A ≥ A₀`; R9 makes it choose `levels` per window.

## R9-1 — the Prop

Replace the last block of `SliceMeanSquareA2` (after `C₁ / ε ^ k ≤ h →`) by

```lean
      ∃ A₀ : ℝ, 1 ≤ A₀ ∧
        ∀ A₁ : ℕ, A₀ ≤ A₁ →
          ∃ levels : List (Finset ℕ),
            (∀ P ∈ levels, ∀ p ∈ P, p.Prime) ∧
            (∀ P ∈ levels, ∀ p ∈ P, C * Real.log h ^ B < p) ∧
            (∀ A : ℕ, A₁ ≤ A → A ≤ A₁ ^ 2 →
              ∑ n ∈ (Finset.Ioc A (2 * A)).filter (fun n => ¬ HasFactorInAll levels n), (1:ℝ)/n
                ≤ εc * ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n) ∧
            (∀ A : ℕ, A₁ ≤ A → A ≤ A₁ ^ 2 →
              ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → (∀ n, ‖g n‖ ≤ 1) → g 1 = 1 →
                NonPretentiousAt g A₀ (2 * A + 1) →
                ∀ J : ℕ, A / 2 ≤ J → J ≤ A →
                  ∑ n ∈ Finset.Ioc A (A + J),
                    ‖∑ m ∈ (Finset.Ioc n (n + h)).filter (HasFactorInAll levels), g m‖^2 / n
                    ≤ ε^2 * (h : ℝ)^2 * ∑ n ∈ Finset.Ioc A (A + J), (1:ℝ)/n)
```

(the two clauses now range over `A ∈ [A₁, A₁²]` with the window's own `levels`; everything before is unchanged). Update
the docstring and the module header: the quantifier order is `[mrt]`'s `X₀` device; `A₀` is still chosen after `h`.

## R9-2 — R6-8 (`majorArc_block_bound_restricted`)

Takes `levels` and the two clauses as hypotheses for the scales it uses: read its proof and state exactly which scales
`A'` (the class scales `A/q`, `A/q − 1`, the density blocks) the clauses are invoked at, as a scale set `S(A, Q)`; keep the
theorem's shape, restricting the clause hypotheses to `A' ∈ S(A, Q)` if that is what the proof uses (or leave them as
`∀ A' ≥ A₀` if R9-3 can supply that — it cannot beyond `A₁²`, so restrict).

## R9-3 — R7 (`exists_wrapper_params`, `good_block_total_le`, `block_total_le_trichotomy`, `majorArc_bound_of_A2_of_le_one`)

`exists_wrapper_params` now exports, for `H ≥ H₀`: `Q, h₀, A₀` and **per block** data:
`∀ A : ℕ, A₀ ≤ A → ∃ levels, (primes) ∧ (Q < p) ∧ (density on (A, 2A] and (2A, 4A]) ∧ (mean square at every scale in S(A, Q))`
— obtained from the Prop at `A₁ := A / (4 * ⌈Q⌉₊ + 4)` (ℕ-division), which needs `A₀ ≥ (4⌈Q⌉₊+4)·max(A₀^{Prop}, 256Q/ε, …)`
and `4A + O(1) ≤ A₁²` (true once `A ≥ 16(4⌈Q⌉₊+4)²`); prove the window containment `S(A, Q) ⊆ [A₁, A₁²]` as a lemma. Then
`good_block_total_le`/`block_total_le_trichotomy` take the per-block `levels` (they already take `levels` as a parameter —
check whether any step uses the *same* `levels` across two blocks; the `𝒮ᶜ` removal is per block via
`sum_complement_Ioc_le_of_density`, so it should not), and `majorArc_bound_of_A2_of_le_one` picks `levels` inside the
block loop. `2 ≤ (ε/(128Q))·A₀` and the `NonPretentiousAt` strength transport as in R8-6.

## R9-4 — pins

`edp_of_sliceMeanSquareA2`, `theorem18_of_sliceMeanSquareA2` and their `#print axioms` pins in `TrackCAxiomAudit.lean`
compile with byte-identical axiom sets (`[propext, Classical.choice, Quot.sound]`). Record the exact new scale set `S(A, Q)`
and the exact new threshold in the report and in the docstrings.

## Stop rule

Constant and parameter-choice adjustments are yours; stop only if the re-thread needs a clause the Prop cannot provide
(e.g. a scale outside `[A₁, A₁²]`) — then record the exact scale and why, and report.
