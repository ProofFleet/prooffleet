# Track R — V-B″ brief (run 26): the height `Z = max(8πT, exp((log P)^{1/(1+θ)}))`, the sharpened regular-part exponent, the three-regime envelope, V-C4-4, and the compositions

**Ground rules:** as in the V-B′ brief (no `sorry`/`axiom`/`unsafe` under `MoltResearch/`, `Solutions/`; new nucleus lemmas in new leaf files registered in
`MoltResearch/DiscrepancyAnalytic.lean`; never edit `PlancherelHarness`, never append to `BandSchedule`/`WindowTK`/`WindowAssembly`/`HalaszComplex`; do not modify
existing theorems — add new ones; one commit per unit `Track R: <one line> (#3044, V-B″-<n>)` / `(V-C4-3′)` / `(V-C4-4)`; never push/merge/rebase; `CODEX_REPORT.md`
uncommitted). You are on branch `vex/track-r-vc4` with V-C4-1/2/3/5 and V-B′-1/2 committed; read your `CODEX_REPORT.md` (the V-B′-3 counterexample) and
`CODEX_REPORT_vc4.md`, `MoltResearch/Discrepancy/PrimeLargeValuesFromRegionH.lean` (the record `ZeroFreeRegionDataH θ m` with `η(Z) = min η₀ (log 2Z)^{−θ}`,
`M(Z) = max M₀ (log 2Z)^m`, and the V-B′-2 wrapper), `PrimeSumZeroFree.lean`, `PrimeLargeValuesFromRegion.lean`, and your V-C4 leaves.

## Why V-B′-3 failed, and the correct bookkeeping (accepted: your counterexample is right)

With `Z = 8πT + √P` the width is `≈ (log P)^{−θ}·2^θ` whenever `√P > 8πT`, which is far too small for `log 2T` between `(log P)^{1−θ}` and `(log P)^{θ/θ'}`. The
height must be the **smallest** height at which the right-line truncation tail (`≲ e·P·log(2P)/H` for the `1/(1+τ²)` window decay) is below the shifted-line size
`P^{1−η(H)/2}`: with `η(H) = (log 2H)^{−θ}` this is `log H ≈ (log P)^{1/(1+θ)}`. So:

**V-B″-1.** Re-run the V-A composition at `Z := max (8π T) (Real.exp ((Real.log P)^(1/(1+θ))))` (plus whatever `+ 2` margins the rectangle needs), with
`η := η(Z)`, `M := M(Z)` from the record at this `Z`. Check: the truncation tail `e·P·log(2P)/(Z/2) ≤ 2e·P log(2P)·exp(−(log P)^{1/(1+θ)})` and the shifted-line term
`P^{1−η(Z)/2}·M(Z) ≥ P·exp(−(log P)·(log 2Z)^{−θ}/2)`; with `log 2Z ≥ (log P)^{1/(1+θ)}`: `(log P)(log 2Z)^{−θ} ≤ (log P)^{1−θ/(1+θ)} = (log P)^{1/(1+θ)}`, so the
shifted term is `≥ P exp(−(log P)^{1/(1+θ)}/2)`, which dominates the tail for `P ≥ P₀` ✓. Write `x := log P`, `y := log 2T`, `E := the off-diagonal per-point
bound = C₂·P^{1−η(Z)/2}·M(Z) + tails`; the dual bound is `∑_t‖S(t)‖² ≤ (C₁P + #𝒯·E)·(∑‖a_p‖²/p²)·(P/log P)/P`-normalised as in V-B.

**V-C4-3′ (sharpen the regular-part exponent).** Your `m(a) = 2 + 1/a` is too crude for the envelope (it needs `m ≤ 2`). Re-prove the Borel–Carathéodory step
with the growth bound used honestly: on the disc of radius `2η` about `c = 1 + η/2 + it` (`η = η_zf(t)` the zero-free half-width), `log max|ζ| ≤ B(3η/2)^a log|t| + b loglog|t| + B₀`,
and `(3η/2)^a log|t| ≤ C` because `η_zf(t)^a log|t| = c^a(loglog|t|)^{1−a}·… ≤ c^a` (your `η_zf = c(loglog t)^{1/a−1}(log t)^{−1/a}`); and
`log(1/‖ζ(c)‖) ≤ (3/4)log(C/η) + (1/4)(b loglog|t| + B₀ + …)` by the 3-4-1 lower bound (`zeta_norm_lower_341`-type with the growth bound in place of the crude
`10⁴(2t)²`). Hence `‖ζ'/ζ(z)‖ ≤ (4/η)·(C₁ loglog|t| + C₂ log(1/η) + C₃) ≤ C₄·(log|t|)^{1/a}·(loglog|t|)^{2}` on `Re z ≥ 1 − η/2`, and the regular part differs by
`1/|z−1| ≤ 1/|t|`. Conclude `m := 1/a + 1/10` (so `m < 1 < 2` for `a ≥ 7/5`; record the exact `m` and `Z₁`).

**V-B″-2 (the three-regime envelope).** Prove `prime_large_values_bound_of_zeroFreeRegionDataH'`: for `θ < θ'`, `m ≤ 2`, there is `C` with the V-0 field's
right-hand side `C(1 + #𝒯·exp(−x/y^{θ'})·y²)·(∑‖a_p‖²/p²)·P/log P` for all `P ≥ 2`, `T ≥ 1`, well-spaced `𝒯 ⊂ [−T, T]`:
- **Regime 0** `x ≤ y^{θ'}`: the trivial bound `∑_t‖S(t)‖² ≤ #𝒯·#Y·∑‖a_p‖²/p²` (Cauchy–Schwarz), `#Y ≤ 2P`, and `2P ≤ C e^{−x/y^{θ'}}y²·P/log P` since
  `e^{x/y^{θ'}} ≤ e` and `2e·log P ≤ 2e·y^{θ'} ≤ C y²` (for `y ≥ 1`; for `y < 1`, `x < 1` and `2e < 0.48C`).
- **Regime I** `x > y^{θ'}` and `8πT ≥ exp(x^{1/(1+θ)})`: `Z = 8πT`, `log 2Z = y + log 8π`; option A: `E/P ≤ C₂ exp(−x/(2(y + c')^θ))·(y + c')^m ≤ C e^{−x/y^{θ'}}·y²`
  because `2(y+c')^θ ≤ y^{θ'}` for `y ≥ y₁(θ, θ')` (so the exponential is smaller) and `(y+c')^m ≤ e^{c'm}·y^m ≤ e^{2c'}y²` (`m ≤ 2`, `y ≥ 1`); for `y < y₁` use
  option B: `#𝒯 ≤ 2T + 1 ≤ 2e^{y₁}`, `E ≤ C₃P` (`P^{−η/2}M ≤ C₃`), so `#𝒯·E ≤ C P` is absorbed into the diagonal constant.
- **Regime II** `exp(x^{1/(1+θ)}) > 8πT`: `Z = H := exp(x^{1/(1+θ)})`, `η(Z) ≥ (x^{1/(1+θ)} + log 2)^{−θ}`, `E/P ≤ C₂ exp(−x^{1/(1+θ)}/3)·(2x)^{m/(1+θ)}` (for `x ≥ x₀`);
  if `y ≥ x^{1/(1+θ)}/3` use option A: `x/y^{θ'} ≤ 3^{θ'}x^{1 − θ'/(1+θ)}` and `1 − θ'/(1+θ) < 1/(1+θ)` (as `θ < θ'`), so `x^{1/(1+θ)}/3 − m' log(2x) ≥ 3^{θ'}x^{1−θ'/(1+θ)} + log C₂ − 2 log y`
  for `x ≥ x₁` ✓; if `y < x^{1/(1+θ)}/3` use option B: `#𝒯·E/P ≤ 3e^{y}·C₂ exp(−x^{1/(1+θ)}/3)(2x)^{m'} ≤ C` ✓; for `x < max(x₀, x₁)` (bounded `P`, hence
  `Z ≤ 8πT + H₀` bounded height in `P`) — either regime 0 applies or `#𝒯 E ≤ (2T+1)·C₃P`… no: bounded `P` and large `T` is regime 0 (`x ≤ y^{θ'}` once
  `y^{θ'} ≥ x₁`), else `T` is bounded too and option B absorbs. Record every threshold (`y₁, x₀, x₁, P₀`) and the final `C`.
Then `primeLargeValues_of_zeroFreeRegionH (h : ZeroFreeRegionDataH θ m) (hθ : θ < 31/40) (hm : m ≤ 2) : PrimeLargeValuesAssumption` via the existing V-B bridge
(`31/40 → 4/5` absorption) and `trackR_edp_of_zeroFreeRegionH`, pinned.

**V-C4-4.** `zeroFreeRegionDataH_of_growth (h : ZetaGrowthBound t₀ a B b B₀) (ha : 7/5 ≤ a) : ZeroFreeRegionDataH (1/a + 1/100) (1/a + 1/10)` (θ = 5/7 + 1/100 < 31/40 ✓,
`m < 2` ✓): for `Z ≥ Z₁` from V-C4-2 and V-C4-3′ (the record's width `(log 2Z)^{−θ}` is below the true width `c(loglog Z)^{1/a−1}(log Z)^{−1/a}` for `Z ≥ Z₁` since
`θ > 1/a`; the record's `M(Z) = max M₀ (log 2Z)^m` is above the proved bound for `Z ≥ Z₁`); for `2 ≤ Z < Z₁` by compactness: `ζ` has no zeros on `Re z ≥ 1`
(`riemannZeta_ne_zero_of_one_le_re`), the zero set of `ζ` on the compact box `[1/2, 2] × [−Z₁, Z₁]` minus a small disc about `1` is closed and disjoint from
`{Re z ≥ 1}`, hence at positive distance `η₁`; take the record's `η₀ := min(1/2, η₁, …)`; the regular part `−ζ'/ζ(z) − 1/(z−1)` is analytic on a neighbourhood of
`[1 − η₁, 2] × [−Z₁, Z₁]` (via `exists_zeta_pole_reg`), hence bounded there by some `M₀`. Record the compiled statement.

**Compositions.** `primeLargeValues_of_zetaGrowth (h : ZetaGrowthBound t₀ a B b B₀) (ha : 7/5 ≤ a) : PrimeLargeValuesAssumption` and `trackR_edp_of_zetaGrowth`
(EDP for every sign sequence, conditional only on a growth bound `log‖ζ(σ+it)‖ ≤ B(1−σ)^{a} log|t| + b loglog|t| + B₀` with `a ≥ 7/5`), pinned in the audit file.

**Verification/report** as always. **Stop rule:** stop only if one of the three regimes fails by an unbounded factor for every `θ < θ'`, `m ≤ 2` (record the exact
inequality and the `(x, y)` family), or if the compactness step needs an absent Mathlib fact (record which).
