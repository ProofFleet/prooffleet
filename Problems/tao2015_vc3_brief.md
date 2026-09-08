# Track R — V-C3 brief: the growth bound `log‖ζ(σ+it)‖ ≤ B(1−σ)^{a} log t + b loglog t + B₀` from the Weyl-sum bound

**Ground rules:** `Problems/tao2015_vi9g_brief.md` §0 verbatim (no `sorry`/`axiom`/`unsafe` under `MoltResearch/`, `Solutions/`, not even in comments;
new nucleus lemmas only in new leaf files registered in `MoltResearch/DiscrepancyAnalytic.lean`; never edit `PlancherelHarness`, never append to
`BandSchedule`/`WindowTK`/`WindowAssembly`/`HalaszComplex`; respect `scripts/check_layering.sh`; one commit per unit `Track R: <one line> (#3044, V-C3-<n>)`;
never push/merge/rebase; `CODEX_REPORT.md` uncommitted). Read: the design report §"Phase 6", `Problems/tao2015_vc_design_notes.md`,
`MoltResearch/Discrepancy/VinogradovWeylSum.lean` (V-C2's `vinogradov_weyl_sum` — read its exact compiled statement: the phase form, the range of
`u`, and the exponent `1 − c/(λ^a log^b 2λ)` actually proved), `MoltResearch/Discrepancy/ZetaBound.lean` (`zeta_afe_strip`: for `1/2 ≤ Re s`,
`2 ≤ |Im s|`, `4‖s−1‖ ≤ N`, `ζ(s) = ∑_{n<N} n^{−s} + zPot s N + zTail s N`; `zPot s N = N^{1−s}/(s−1)`; the tail bound used in `zeta_strip_bound`:
`‖zTail‖ ≤ 2‖s−1‖(N−1)^{−σ}/σ`; `norm_sum_cpow_block_le_strip`; `zeta_LSeries_bound` for `σ > 1`), and the V-C4 interface
`ZetaGrowthBound t₀ a B b B₀` (from `Problems/tao2015_vc4_brief.md`, or the compiled structure if V-C4 has landed in the tree — match it exactly).


**Exponent update (after run 24).** V-C2 delivers the weakened saving `1 − c/(λ³ log²(2λ))` (`a = 3`, `b = 2`). Then `E(σ) ≍ (1−σ)^{4/3}(log(2/(1−σ)))^{2/3}`, and the growth bound must be stated with `a' := 33/25 = 1.32` (absorb `(1−σ)^{4/3 − 1.32}(log(2/(1−σ)))^{2/3} ≤ C` on `1−σ ≤ 1/4`): `ZetaGrowthBound t₀ (33/25) B 1 B₀`. V-C4-4 then gives `θ = 1/a' + 1/100 = 0.7676 < 31/40` ✓ (record the margin). Replace `7/5` by `33/25` throughout below.

## Target

New leaf `MoltResearch/Discrepancy/ZetaGrowthVinogradov.lean`:
```
theorem zeta_growth_vinogradov :
    ∃ (t₀ B B₀ : ℝ), 3 ≤ t₀ ∧ 0 < B ∧ ∀ σ t : ℝ, t₀ ≤ |t| → 3/4 ≤ σ → σ ≤ 2 →
      Real.log ‖riemannZeta (σ + Complex.I * t)‖
        ≤ B * (max (1 - σ) 0) ^ (7/5 : ℝ) * Real.log |t| + Real.log (Real.log |t|) + B₀
```
i.e. `ZetaGrowthBound t₀ (7/5) B 1 B₀` (any `a > 5/4` serves V-C4; `7/5` leaves room to absorb the `log^b(2λ)` loss of the weak Weyl bound;
if V-C2 proved the classical `1 − c/λ²`, take `a = 3/2`). Also package it as the V-C4 structure and prove the corollary
`zeroFreeRegionData_vinogradov : ZeroFreeRegionData θ m` for the `θ = 31/40`… — **no**: V-C4-4's `zeroFreeRegionData_of_growth` does that;
here only produce the `ZetaGrowthBound` instance/term and, if V-C4 is in the tree, the one-line composition `zeroFreeRegionData_from_vinogradov`
and then **`instance : PrimeLargeValuesAssumption := primeLargeValues_of_zeroFreeRegion …`** in a Conjectures file
`TrackCStage5PrimeLargeValuesDischarge.lean`, **`theorem erdos_discrepancy_unconditional (f) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f`**
(no class hypotheses), and its `#print axioms` pin (standard three) in `TrackCAxiomAudit.lean` — the campaign's endpoint. If V-C4 is not yet in the
tree, stop after the growth bound and say so.

## The proof (Karatsuba VI Thm 3; Titchmarsh §5.17–5.18; Ford §7 in outline)

- **V-C3-1 (partial summation on a dyadic block).** From V-C2 (`u = 0`, all `R ∈ (N, 2N]`): for `σ ≥ 0`,
  `‖∑_{N<n≤2N} n^{−σ−it}‖ ≤ 3·N^{−σ}·max_{N<R≤2N} ‖∑_{N<n≤R} n^{−it}‖` (Abel summation against the decreasing weight `n^{−σ}`; total variation
  `≤ N^{−σ}`), hence `≤ 3C·N^{1−σ−c/(λ_N^a log^b 2λ_N)}` with `λ_N = log t/log N`, for `2 ≤ N ≤ t`.
- **V-C3-2 (the dyadic sum).** For `s = σ + it`, `|t| ≥ t₀`, `3/4 ≤ σ ≤ 1`: apply `zeta_afe_strip` with `N₀ := ⌈4‖s−1‖⌉₊ + 1 ≤ 8|t|`;
  `‖zPot‖ ≤ N₀^{1−σ}/‖s−1‖ ≤ (8|t|)^{1−σ}/|t| ≤ 8`, `‖zTail‖ ≤ 2‖s−1‖(N₀−1)^{−σ}/σ ≤ 3`; the partial sum `∑_{1≤n<N₀} n^{−s}` splits into
  `n = 1` and dyadic blocks `(2^j, 2^{j+1}]`, `j < log₂ N₀ ≤ log₂(8|t|)`, each bounded by V-C3-1 (for `2^j ≤ |t|`; the last block, if `2^{j+1} > |t|`,
  by the trivial `norm_sum_cpow_block_le_strip`, `≤ 2^j·2^{−jσ} ≤ (8|t|)^{1−σ}`).
- **V-C3-3 (the optimisation).** Bound each block `3C·N^{1−σ−c/(λ^a log^b 2λ)}` by `3C·|t|^{E(σ)}` where
  `E(σ) := max_{λ ≥ 1} [(1−σ)/λ − c/(λ^{a+1} log^b 2λ)]₊`: prove `E(σ) ≤ B(1−σ)^{1+1/a}·(log(2/(1−σ)))^{b/a}`-type (elementary calculus: the maximizer
  has `λ^a log^b 2λ ≍ c(a+1)/(1−σ)`; do the two cases `(1−σ)λ^a log^b(2λ) ≤ c/2` — then the bracket is `≤ 0` — and its complement — then
  `λ ≥ λ*(σ)` and `(1−σ)/λ ≤ (1−σ)/λ*`), then absorb `(log(2/(1−σ)))^{b/a}(1−σ)^{1+1/a} ≤ C'(1−σ)^{7/5}` for `a = 2`, `b ≤ 1` (or state the exponent
  your V-C2 supports and record it). The blocks with `N ≤ |t|^{1/λ₁}` for the fixed `λ₁` where V-C2's small-`λ` regime applies contribute
  `≤ 3C|t|^{(1−σ)/λ₁ − c₁}`… — all blocks are covered by the single formula since V-C2 holds for all `λ ≥ 1`. Sum: `≤ 1 + 8 + 3 + log₂(8|t|)·3C·|t|^{E(σ)}`,
  so `log‖ζ‖ ≤ E(σ) log|t| + loglog|t| + B₀` with `B₀` explicit.
- **V-C3-4 (`σ > 1` and the join).** For `1 < σ ≤ 2` use `zeta_LSeries_bound` (`log‖ζ‖ ≤ log(8192 log(|t|+2)) ≤ loglog|t| + B₀'`); at `σ = 1` either
  side works (continuity not needed: the strip theorem covers `σ ≤ 1`). Assemble `ZetaGrowthBound` with `t₀ := max(3, …)`.
- **V-C3-5 (the endpoint, if V-C4 is present).** `zeroFreeRegionData_of_growth` ∘ V-C3 → `ZeroFreeRegionData θ m` at the `θ < 31/40`… — check
  what V-C4-4 produces (`θ = 1/a + ε₀ = 5/7 + ε₀ < 31/40 = 0.775` ✓ for `a = 7/5`); then the instance, `erdos_discrepancy_unconditional`, the pin.

**Verification/report** as always; `#print axioms erdos_discrepancy_unconditional` must be exactly `[propext, Classical.choice, Quot.sound]`.
**Stop rule:** stop only if V-C2's exponent shape cannot be optimised to `(1−σ)^{a'}` with `a' > 5/4` (record the exact exponent obtained).
