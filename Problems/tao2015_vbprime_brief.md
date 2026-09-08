# Track R — V-B′ + V-C4-4 brief: the height-indexed region record, the two-regime envelope, and the growth-to-data theorem

**Ground rules:** `Problems/tao2015_vi9g_brief.md` §0 verbatim (no `sorry`/`axiom`/`unsafe` under `MoltResearch/`, `Solutions/`, not even in comments;
new nucleus lemmas only in new leaf files registered in `MoltResearch/DiscrepancyAnalytic.lean`; never edit `PlancherelHarness`, never append to
`BandSchedule`/`WindowTK`/`WindowAssembly`/`HalaszComplex`; do **not** modify the existing V-B theorems — add new ones; respect
`scripts/check_layering.sh`; one commit per unit `Track R: <one line> (#3044, V-B′-<n>)` / `(V-C4-4)`; never push/merge/rebase; `CODEX_REPORT.md`
uncommitted). You are in the worktree that holds V-C4-1/2/3/5 (branch `vex/track-r-vc4`); read your own `CODEX_REPORT.md` there (Finding "V-C4-4
interface obstruction") and the design report's §"V-C4 as run — status and Finding V-1" (in `Problems/tao2015_a1_r6r7_design_report.md` on `origin/main`
after the V-C4a PR merges — if not yet merged, the same text is reproduced below). Read `MoltResearch/Discrepancy/PrimeSumZeroFree.lean` (the V-A
theorems and their `hzero`/`hreg` hypotheses at height `Y`), `PrimeLargeValuesFromRegion.lean` (`ZeroFreeRegionData`, `prime_large_values_bound_of_zeroFreeRegionData`,
the envelope field), the Conjectures bridge with `primeLargeValues_of_zeroFreeRegion`/`trackR_edp_of_zeroFreeRegion`, and your V-C4 leaves
(`zeta_zero_free_of_growth`, `zeta_regular_logDeriv_bound_of_growth`, the exported `eta(t)`, `m(a)`).

## The defect and the repair (Finding V-1)

`ZeroFreeRegionData.region` demands, for each `P ≥ 2`, `T ≥ 1`, the region up to height `Z = 8πT + P²` with width `η(T)` and bound `M(T)` — impossible
as `P → ∞` at fixed `T`. Repair: index the record by the **height**.

**V-B′-1 (the record).** New leaf `MoltResearch/Discrepancy/PrimeLargeValuesFromRegionH.lean`:
```
structure ZeroFreeRegionDataH (θ m : ℝ) : Prop where
  zero : ∀ Z : ℝ, 2 ≤ Z → ∀ z : ℂ, 1 - min (1/2) ((Real.log (2*Z))^(-θ)) ≤ z.re → z.re ≤ 2 → |z.im| ≤ Z → z ≠ 1 → riemannZeta z ≠ 0
  reg  : ∀ Z : ℝ, 2 ≤ Z → ∀ z : ℂ, 1 - min (1/2) ((Real.log (2*Z))^(-θ)) ≤ z.re → z.re ≤ 2 → |z.im| ≤ Z → z ≠ 1 →
           ‖-deriv riemannZeta z / riemannZeta z - 1/(z-1)‖ ≤ (Real.log (2*Z))^m
```
(pointwise-in-height form: since the true width decreases with the height, "region up to height `Z` with the width at `Z`" is what V-C4-3 delivers;
at small heights the record still requires a width `≥ 1/2`-capped `(log 2Z)^{−θ}` — V-C4-4 supplies it by compactness, see below).

**V-B′-2 (the rectangle height).** Re-run V-A's composition at height `Z := 8πT + √P` (any `Z ≥ 8πT + P^{c₀}` with `c₀ < 1 − η/2` works: the right-line
tail `≲ e·P·log(2P)/√P = e√P log 2P ≤ P^{1−η/2}` for `P ≥ P₀`). Restate V-A's prime-sum theorem for this `Z` with `η := min(1/2, (log 2Z)^{−θ})`,
`M := (log 2Z)^m` taken from the record at this `Z`.

**V-B′-3 (the two-regime envelope).** Prove `prime_large_values_bound_of_zeroFreeRegionDataH (h : ZeroFreeRegionDataH θ m) (hθ : θ*(1+κ) < θ') …` giving the
V-0 field's shape with exponent `θ' = primeLargeValuesExponent = 4/5`… — **careful**: V-B fixed `θ' = 31/40` in the bridge and the class uses
`primeLargeValuesExponent = 4/5`; V-B's two-region "envelope" absorbed `31/40 → 4/5`. Keep the same architecture: the nucleus theorem concludes with an
exponent `θ'` satisfying `θ(1+κ) < θ' < 4/5`, and the bridge composes as before. The dual-form bound is `(C₁P + #𝒯·E)·∑‖a_p‖²/p²·(P/log P)`-normalised with
`E := C₂·P^{1−η(Z)/2}·M(Z)` (plus the truncation and prime-power terms, both `≤ C√P log 2P`); it must be shown `≤ C(1 + #𝒯·exp(−log P/(log 2T)^{θ'})(log 2T)²)`:
- **Regime I** `log P ≤ (log 2T)^{1+κ}`: `log(2Z) ≤ log(16πT + 2√P) ≤ (log 2T)^{1+κ}` for `T ≥ T₀(κ)`, so `η(Z) ≥ (log 2T)^{−θ(1+κ)}` and `M(Z) ≤ (log 2T)^{m(1+κ)}`;
  then `P^{−η/2}M ≤ exp(−log P/(2(log 2T)^{θ(1+κ)}))(log 2T)^{m(1+κ)} ≤ exp(−log P/(log 2T)^{θ'})(log 2T)²` once `2(log 2T)^{θ(1+κ)} ≤ (log 2T)^{θ'}/… ` — i.e. for
  `T ≥ T₁`; for `T < T₁` (finitely many `T`-scales but all `P`) use `#𝒯 ≤ 2T₁ + 1` and the trivial absorption into `C`… — no: for `T < T₁`, `P^{−η/2}M` with
  `η(Z) ≥ (log(16πT₁ + 2√P))^{−θ}` gives `E ≤ C₂P·exp(−c(log P)^{1−θ})(log P)^m ≤ C₃P`, so `#𝒯E ≤ (2T₁+1)C₃P` is absorbed into the diagonal constant `C`. Record `T₀, T₁`.
- **Regime II** `log P > (log 2T)^{1+κ}`: `Z ≤ 8πT + √P ≤ 2√P` (for `P ≥ P₁`; `T < exp((log P)^{1/(1+κ)})`), so `η(Z) ≥ (log 4√P)^{−θ} ≥ (log P)^{−θ}·c`, and
  `E ≤ C₂P·exp(−c(log P)^{1−θ}/2)(log P)^m`; the target term `P·exp(−log P/(log 2T)^{θ'})(log 2T)² ≥ P·exp(−(log P)^{1−θ'/(1+κ)})` (since `(log 2T)^{θ'} < (log P)^{θ'/(1+κ)}`);
  so it suffices that `c(log P)^{1−θ}/2 − m loglog P ≥ (log P)^{1−θ'/(1+κ)} + log C₂`, true for `P ≥ P₂` when `1 − θ > 1 − θ'/(1+κ)`, i.e. `θ(1+κ) < θ'` ✓ the same
  condition; for `P < P₂` absorb into `C`. (If instead you find it cleaner to bound `#𝒯E ≤ 3T·E ≤ C P` directly in Regime II, note it needs
  `log T ≤ (log P)^{1/(1+κ)} ≤ c(log P)^{1−θ}` i.e. `1/(1+κ) ≤ 1 − θ` — FALSE for `θ ≈ 5/7`; use the comparison with the target term as above.)
- Diagonal, pole terms, packing: as in V-B. Conclude `primeLargeValues_of_zeroFreeRegionH (h : ZeroFreeRegionDataH θ m) (hθ : θ < 31/40·(1/(1+κ))…)` — fix concrete
  numbers: `θ ≤ 5/7 + 1/100`, `κ := 1/20` (then `θ(1+κ) ≤ 0.76 < 31/40 = 0.775`), any `m`; and `trackR_edp_of_zeroFreeRegionH` with its pin (Conjectures file).

**V-C4-4 (the data from the growth bound).** `zeroFreeRegionDataH_of_growth (h : ZetaGrowthBound t₀ a B b B₀) (ha : 1 < a) : ZeroFreeRegionDataH (1/a + ε₀) (m(a))`
for an explicit `ε₀` (e.g. `1/100`): for `Z ≥ Z₁` (large) the V-C4-2/3 theorems give width `c(loglog Z)^{1/a−1}(log Z)^{−1/a} ≥ (log 2Z)^{−(1/a+ε₀)}` and the
bound `C(log Z)^{2+1/a} ≤ (log 2Z)^{m}` with `m := 3 + 1/a` (absorbing `C`); for `2 ≤ Z < Z₁` use **compactness**: ζ has no zeros with `Re z ≥ 1` except… (`riemannZeta_ne_zero_of_one_le_re`
covers `Re z ≥ 1`, `z ≠ 1`), zeros are isolated and `ζ` is analytic on the closed rectangle `[1/2, 2] × [−Z₁, Z₁]` minus `1`, so there is `η₁ > 0` with no zeros in
`[1 − η₁, 2] × [−Z₁, Z₁]` (finitely many zeros in the compact set by `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`-type isolation, or directly: the
zero set is closed, disjoint from the compact `{Re z ≥ 1} ∩ box`, hence at positive distance) and the regular part `−ζ'/ζ − 1/(z−1)` is continuous on the
compact `[1 − η₁, 2] × [−Z₁, Z₁]` (analytic there — `exists_zeta_pole_reg` gives the analytic regularisation), hence bounded by some `M₁`; then take the record's
width `min(1/2, (log 2Z)^{−θ})` ≤ … — the record's width must be ≤ the true width: for `Z < Z₁` require `(log 2Z)^{−θ} ≤ η₁`?? Not automatic (`(log 4)^{−θ} ≈ 0.78 > 1/2`
is capped at `1/2`, but `1/2` may exceed `η₁`). **So change the record**: replace `min (1/2) ((log 2Z)^(-θ))` by `min η₀ ((log 2Z)^(-θ))` with a *free* `η₀ > 0`
field of the structure (`ZeroFreeRegionDataH θ m η₀`, `0 < η₀ ≤ 1/2`), and `M` by `max M₀ ((log 2Z)^m)` with a free `M₀`; V-B′-3 carries `η₀, M₀` as constants
(they only affect the finite range `Z ≤ Z₁`, absorbed into `C`). Record the compiled statement.

**Then** the composition `zeroFreeRegionDataH_of_growth` + `primeLargeValues_of_zeroFreeRegionH` gives `PrimeLargeValuesAssumption` from any `ZetaGrowthBound` with
`1/a + ε₀ ≤ 5/7 + 1/100`, i.e. `a ≥ 7/5` ✓ (V-C3's target). State that composed theorem `primeLargeValues_of_zetaGrowth` and `trackR_edp_of_zetaGrowth`, pinned.

**Verification/report** as always (`lake env lean`, `lake build MoltResearch.DiscrepancyAnalytic Conjectures`, gates, layering, coverage, `#print axioms`).
**Stop rule:** stop only if the two-regime envelope fails by an unbounded factor for every admissible `κ` (record the exact inequality) or if the compactness
step needs a Mathlib fact that is absent (record which).
