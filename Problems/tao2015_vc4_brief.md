# Track R — V-C4 brief: the zero-free region and the `ζ'/ζ` bound from a growth bound on `ζ`, parametrized (Landau + 3-4-1, generalized)

**Ground rules:** `Problems/tao2015_vi9g_brief.md` §0 verbatim (no `sorry`/`axiom`/`unsafe` under `MoltResearch/`, `Solutions/`, not even in comments;
new nucleus lemmas only in new leaf files registered in `MoltResearch/DiscrepancyAnalytic.lean`; never edit `PlancherelHarness`, never append to
`BandSchedule`/`WindowTK`/`WindowAssembly`/`HalaszComplex`; one commit per unit `Track R: <one line> (#3044, V-C4-<n>)`; never push/merge/rebase;
`CODEX_REPORT.md` uncommitted). Read: the design report §"Phase 6" (V-C4 and the V-B interface `ZeroFreeRegionData`), the V-A/V-B report
(`Problems/tao2015_va_report.md`) for the exact region hypotheses `hzero`/`hlog` that V-A consumes, `MoltResearch/Discrepancy/ZeroFreeRegion.lean`
(`zeta_landau_core`, `zeta_norm_lower_341`, `zeta_norm_upper`, `zeta_real_upper`, `zeta_logDeriv_pole_bound`, `vonMangoldt_341_nonneg`, `zeta_341_prod_ge_one`,
and the proof of `zeta_zero_free_region`), `MoltResearch/Discrepancy/LandauLemma.lean` (`landau_inequality`, `landau_inequality_free`,
`norm_logDeriv_le_of_ratio_le` = Borel–Carathéodory), and `ZetaBound.lean` (`zeta_LSeries_bound`, `zeta_strip_bound`).


**Interface note (from run 19).** V-A consumes the region as `hzero` plus a bound on the **regular part** `‖−ζ'/ζ(z) − 1/(z−1)‖ ≤ M` on the full closed rectangle `1 − η ≤ Re z ≤ 2`, `|Im z| ≤ Y` (`hreg`), not a bound on `ζ'/ζ` away from the pole; V-C4-3 must produce that form (Borel–Carathéodory applied to the regular part, which is analytic on the region).

## What to prove

**V-C4-1 (Landau's core at a free radius).** Generalize `zeta_landau_core`: for `c := σ₀ + iτ` with `1 < σ₀ ≤ 3/2`, a radius `0 < R ≤ 1/2`, and a
bound `‖ζ(s)‖ ≤ e^{K}·‖ζ(c)‖` on `closedBall c R` (hypothesis `K ≥ 0`), the two conclusions of `zeta_landau_core` with `32(log(…)+1)` replaced by
`C_L·(K + 1)/R` (read `landau_inequality`'s constant; the current `32` is its value at `R = 1/2`), both in the designated-zero form (zeros in
`closedBall c (R/4)`) and the zero-free form. The quarter-ball non-vanishing condition still comes from `riemannZeta_ne_zero_of_one_le_re`.

**V-C4-2 (the growth-to-region theorem).** Package a growth bound as
```
structure ZetaGrowthBound (t₀ a B b B₀ : ℝ) : Prop where
  bound : ∀ σ t : ℝ, t₀ ≤ |t| → 1 - 1/4 ≤ σ → σ ≤ 2 →
    Real.log ‖riemannZeta (σ + I*t)‖ ≤ B * (max (1 - σ) 0)^a * Real.log |t| + b * Real.log (Real.log |t|) + B₀
```
(`a > 1`; the region will not use `σ < 1 − 1/4`) and prove, by the existing 3-4-1 assembly with `σ₀ := 1 + η`, `η := η(t)`, radius `R := R(t)` chosen so
that `B R^{a} log t ≍ loglog t`, i.e. `R(t) := (loglog t/(B log t))^{1/a}` and `η(t) := c₁·R(t)/(loglog t)` … — do the calculation honestly: the Landau
bound gives, for a zero `β + iτ` with `|τ − t| ≤ R/4`, `−Re(ζ'/ζ)(σ₀ + iτ) ≤ C_L(K+1)/R − 1/(σ₀ − β)` with `K ≤ B R^{a} log t + b loglog t + B₀ − log‖ζ(c)‖`
and `−log‖ζ(c)‖ ≤ (3/4)·log(1 + 1/η)+ …` from `zeta_norm_lower_341`-type lower bounds (redo `zeta_norm_lower_341` with the growth bound in place of
`10⁴(2t)²`), and the 3-4-1 combination `3(−Re ζ'/ζ)(σ₀) + 4(−Re ζ'/ζ)(σ₀+iτ) + (−Re ζ'/ζ)(σ₀+2iτ) ≥ 0` with `−ζ'/ζ(σ₀) ≤ 1/η + c_p`
(`zeta_logDeriv_pole_bound`) yields `4/(σ₀ − β) ≤ 3/η + 5C_L(K+1)/R + O(1)`; with `η = κ R/(K+1)` for a small fixed `κ` this forces
`1 − β ≥ … ≥ κ' R/(K+1)`, i.e. the zero-free width `η_zf(t) := κ'·R(t)/(B R(t)^{a} log t + b loglog t + B₀ + log(1/η) + 1)`, which for the choice of `R(t)`
above is `≍ (loglog t)^{1/a − 1}(log t)^{−1/a}`. Conclude:
```
theorem zeta_zero_free_of_growth (h : ZetaGrowthBound t₀ a B b B₀) (ha : 1 < a) … :
  ∃ c t₁ : ℝ, 0 < c ∧ t₀ ≤ t₁ ∧ ∀ β t : ℝ, t₁ ≤ |t| → riemannZeta (β + I*t) = 0 →
    β ≤ 1 - c * (Real.log (Real.log |t|))^(1/a - 1) / (Real.log |t|)^(1/a)
```
Then **V-C4-3 (the `ζ'/ζ` bound in the half-width region)**: for `Re s ≥ 1 − η_zf(|Im s|)/2`, `|Im s| ≥ t₁`, `‖ζ'/ζ(s)‖ ≤ C·(K(|Im s|) + 1)/η_zf(|Im s|)`
by Borel–Carathéodory (`norm_logDeriv_le_of_ratio_le`) on the disc of radius `η_zf` around `1 + η_zf/2 + i·Im s` (zero-free by V-C4-2, ratio bound from
the growth bound and the 3-4-1 lower bound), giving `‖ζ'/ζ‖ ≤ (log t)^{m}` for an explicit `m = m(a)` (record it). **V-C4-4**: package
`ZeroFreeRegionData θ m` exactly as V-B consumes it (`θ := 1/a + ε₀` for a small explicit `ε₀`, since `(loglog t)^{1/a−1}(log t)^{−1/a} ≥ (log t)^{−θ}` for
`t ≥ t₂`; for `t < t₂` the region hypotheses at height `Y` only concern `|Im s| ≤ Y`, and the small-height part is covered by the de la Vallée Poussin
region `zeta_zero_free_region` with its own constant — reconcile the two into one `η(T)` by taking the minimum, as V-B's data requires), and prove
`zeroFreeRegionData_of_growth : ZetaGrowthBound t₀ a B b B₀ → 1 < a → ZeroFreeRegionData (1/a + ε₀) m` — the theorem V-C3 will feed.

**V-C4-5 (validation).** Instantiate V-C4-2 with the tree's crude bound `zeta_norm_upper` (`log‖ζ‖ ≤ 2 log t + log 10⁴`, i.e. `a` arbitrary with `B = 0`,
`b = 0`, `B₀ = 2·…` — or add a variant of the theorem for a bound of the form `Real.log ‖ζ‖ ≤ b' log t + B₀`, `b' = 2`) and check that it reproduces a
de la Vallée Poussin region `β ≤ 1 − c/log|t|` — this validates the parametrization against the existing `zeta_zero_free_region`.

**Verification/report** as always; `#print axioms` of the main theorems (standard three). **Stop rule:** stop only if the Landau generalisation needs a
hypothesis the tree's `landau_inequality` cannot supply (record it) — constants and the exact `η(t), R(t)` choices are yours; record them.
