# Track R — V-A brief: prime sums from a zero-free region (the Mellin shift), and V-B: `[MR]` Lemma 8 from it

**Ground rules:** `Problems/tao2015_vi9g_brief.md` §0 verbatim (no `sorry`/`axiom`/`unsafe` under `MoltResearch/`, `Solutions/`, not even in comments;
new nucleus lemmas only in new leaf files registered in `MoltResearch/DiscrepancyAnalytic.lean`; never edit `PlancherelHarness`, never append to
`BandSchedule`/`WindowTK`/`WindowAssembly`/`HalaszComplex`; one commit per unit `Track R: <one line> (#3044, V-A-<n>)` / `(V-B-<n>)`; never push/merge/rebase;
`CODEX_REPORT.md` uncommitted). Read: the design report §"Phase 6" (units V-A, V-B and the `[MR]` Lemma 8 proof sketch), `Problems/sources/tao2015_statements.md`
(Lemma 8), `MoltResearch/Discrepancy/ZeroFreeRegion.lean` (`exists_zeta_pole_reg`, `zeta_logDeriv_pole_bound`, `zeta_norm_upper`, `re_LSeries_vonMangoldt`),
`MoltResearch/Discrepancy/PerronWindow.lean` (`exists_master_transition`, `exists_perron_window`, `fourier_pointwise_decay`, `fourier_window_le_inv_one_add_sq`,
`perron_sandwich`), `MoltResearch/Discrepancy/HalaszMontgomeryLargeValues.lean` (`sum_norm_sq_le_norm_sq_mul_sup_kernel`, the well-spaced packing lemmas),
Mathlib `Mathlib/Analysis/MellinTransform.lean`, `MellinInversion.lean` (`mellinInv_mellin_eq`), `Mathlib/Analysis/Complex/CauchyIntegral.lean`
(`Complex.integral_boundary_rect_eq_zero_of_differentiableOn` and its `_off_countable` form), `Mathlib/NumberTheory/LSeries/*` (`LSeries_vonMangoldt_eq_deriv_riemannZeta_div`
or its current name: `−ζ'/ζ(s) = ∑ Λ(n) n^{−s}` for `Re s > 1`), `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` (`riemannZeta_ne_zero_of_one_le_re`),
and the interface file `Conjectures/…/Interfaces/LargeValues.lean` in its V-0 form (existential constant, `primeLargeValuesExponent`).

## The mathematics (`[MR]` Lemma 8, ar5iv 1501.04585, §"Lemma 10"–"Lemma 8")

Fix a smooth window `w(x) = ψ(log(x/P)/log 2)` with `ψ` a fixed `C^∞` bump on `[0, 1]`, `0 ≤ ψ ≤ 1` (build it from `exists_master_transition`; only
`‖ψ‖, ‖ψ'‖, ‖ψ''‖ ≤ C_ψ` are used). Its Mellin transform `w̃(s) = ∫_0^∞ w(x) x^{s−1} dx` is entire, `w̃(σ + iτ) = P^{σ}·Ψ_σ(τ)` with
`‖w̃(σ+iτ)‖ ≤ C P^{σ}/(1 + |τ|)²` (two integrations by parts; this is `fourier_window_le_inv_one_add_sq`'s content in Mellin clothing). For `c > 1`,
`∑_n Λ(n) w(n) n^{−iu} = (1/2πi)∫_{(c)} w̃(s)·(−ζ'/ζ)(s + iu) ds` (Mellin inversion + absolute convergence of `∑ Λ(n) n^{−c}`). Shift the contour to
`Re s = 1 − η/2` inside a region where `ζ` has no zeros: the pole of `−ζ'/ζ(s+iu)` at `s = 1 − iu` contributes `w̃(1 − iu)`, of size `≤ C P/u²` for `|u| ≥ 1`,
and the shifted integral is `≤ C·M·P^{1−η/2}·∫ dτ/(1+|τ|)² ≤ 3C·M·P^{1−η/2}` when `‖ζ'/ζ‖ ≤ M` on the shifted line. Prime powers cost `≤ 3√P log(2P)`.

## V-A — the theorem (new nucleus leaf `MoltResearch/Discrepancy/PrimeSumZeroFree.lean`)

State the region as explicit hypotheses (no class):
```
(η Y M : ℝ) (hη : 0 < η) (hη1 : η ≤ 1/2) (hY : 1 ≤ Y) (hM : 1 ≤ M)
(hzero : ∀ s : ℂ, 1 - η ≤ s.re → s.re ≤ 2 → |s.im| ≤ Y → s ≠ 1 → riemannZeta s ≠ 0)
(hlog  : ∀ s : ℂ, 1 - η/2 ≤ s.re → s.re ≤ 2 → |s.im| ≤ Y → 1/4 ≤ ‖s - 1‖ → ‖deriv riemannZeta s / riemannZeta s‖ ≤ M)
```
and prove, for the window `w` at scale `P ≥ 2` and every `u` with `1 ≤ |u| ≤ Y/2`:
```
‖∑ p ∈ (Finset.Ioc P (2*P)).filter Nat.Prime, (w p * Real.log p : ℂ) * (p:ℂ)^(-(u:ℂ)*I)  −  w̃(1 − iu)‖
   ≤ C₀ * (M * P^{1−η/2} / η + P * Real.log (2*P) / (Y/2) + Real.sqrt P * Real.log (2*P))
```
with an explicit absolute `C₀` (and `‖w̃(1 − iu)‖ ≤ C₀ P/u²`). Route, each step a lemma: **V-A-1** the window and its Mellin transform (`mellin` of a
compactly supported smooth function is entire; the vertical decay `‖w̃(σ+iτ)‖ ≤ C P^σ/(1+τ²)` uniformly for `σ ∈ [1/2, 2]`); **V-A-2** the Mellin
representation of `∑_n Λ(n) w(n) n^{−iu}` on `Re s = c := 1 + 1/log(2P)` (Mellin inversion `mellinInv_mellin_eq` per `n`, then interchange of `∑_n` and
`∫` by dominated convergence — `∑_n Λ(n) n^{−c} ≤ C log(2P)`, `zeta_logDeriv_pole_bound`-type — and `LSeries_vonMangoldt`); **V-A-3** truncation of
the right line at `|Im s| ≤ Y − |u|` (tail `≤ C P^{c} log(2P)/(Y − |u|)` from the `1/(1+τ²)` decay times the `log(2P)` bound of `−ζ'/ζ` on `Re s = c`);
**V-A-4** the rectangle: subtract the pole with `exists_zeta_pole_reg` (or write `−ζ'/ζ(s) = 1/(s−1) + g(s)` with `g` analytic on the region — the
tree's `exists_zeta_pole_reg` supplies the analytic regularisation), apply `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` to
`w̃(s)·g(s+iu)` on the rectangle `[1−η/2, c] × [−(Y−|u|), Y−|u|]` (differentiable since `hzero` gives no zeros there), and Cauchy's integral formula for the
rational part `w̃(s)/(s + iu − 1)` (residue `w̃(1 − iu)`; apply the rectangle theorem to `(w̃(s) − w̃(1−iu))/(s+iu−1)`); **V-A-5** bound the three
remaining sides: the shifted line by `hlog` and the decay (`≤ 3C M P^{1−η/2}`), the two horizontal segments by `hlog` and the decay at `|τ| = Y − |u| ≥ Y/2`
(`≤ C M P^{c}(c − 1 + η/2)/(Y/2)²`); **V-A-6** prime powers (`∑_{p^k ≤ 2P, k ≥ 2} log p ≤ 3√P log(2P)`). Record `C₀`.

## V-B — Lemma 8 from V-A (same leaf or `PrimeLargeValuesFromRegion.lean`)

For `T ≥ 1`, `𝒯 ⊂ [−T, T]` well-spaced (`1 ≤ |t − t'|`), `Y ≥ 2T + 2`, primes `Y_P ⊆ (P, 2P]`, coefficients `a`:
`∑_{t∈𝒯} ‖∑_{p∈Y_P} (a_p/p) e(−t log p)‖² ≤ C₁·(1 + #𝒯·(M P^{−η/2}/η + P^{1/2}log(2P)/… ) …)·(∑ ‖a_p‖²/p²)·P/log P` — precisely: by
`sum_norm_sq_le_norm_sq_mul_sup_kernel` (H-1) with the phases `χ_p(t) = e(−t log p)` and coefficients `b_p = a_p/p`, the kernel is
`K(u) = ∑_{p∈Y_P} e(−u log p)`; bound it on the window `w ≡ 1` on `[P, 2P]`?? — no: the kernel is unweighted, so use `[MR]`'s device: apply the duality
to the weighted matrix `(√(log p)·w(p)^{1/2} …)` or, simpler, **prove Lemma 8 directly as `[MR]` do**: the dual form `∑_p log p·w(p)·‖∑_t η_t p^{it}‖²
= ∑_{t,t'} η_t η̄_{t'} ∑_p log p·w(p) p^{i(t−t')}`, the diagonal `t = t'` gives `#`-free `∑_p log p w(p) ≤ C P`, the off-diagonal by V-A:
`|∑_p log p w(p) p^{i(t−t')}| ≤ ‖w̃(1 − i(t−t'))‖ + E(P)`, `E(P) := C₀(M P^{1−η/2}/η + 2P log(2P)/Y + √P log(2P))`; with
`|η_tη_{t'}| ≤ (|η_t|² + |η_{t'}|²)/2` and the well-spaced packing `∑_{t'≠t} 1/|t−t'|² ≤ 4` (prove it; the tree has the `1/|t−t'|` and `√|t−t'|` versions):
`∑_p log p·w(p)‖∑_t η_t p^{it}‖² ≤ (C P + 4C₀P + #𝒯·E(P))·∑_t|η_t|²`. Duality (the standard `‖A‖ = ‖A*‖` between `ℓ²(𝒯)` and the weighted `ℓ²(primes)`,
`[MR]` Lemma 10 — prove it as a finite-dimensional Cauchy–Schwarz statement: `∑_t ‖∑_p b_p χ_p(t)‖² ≤ B·∑_p ‖b_p‖²/(log p·w(p))` whenever
`∑_p log p·w(p)‖∑_t η_t \overline{χ_p(t)}‖² ≤ B∑_t|η_t|²` for all `η`) and `w ≥ 1/2`-type lower bounds on `[P√2, P√2·…]`... — **cover `(P, 2P]` by two
windows** (`w₁ + w₂ ≥ 1` on `(P, 2P]`, each of the V-A shape at scales `P` and `√2 P`) so that `∑_p ‖b_p‖²/(log p·w) ≤ 2∑_p ‖b_p‖²/log P`. Conclusion:
```
∑_{t∈𝒯} ‖∑_{p∈Y_P} (a_p/p)·e(−t log p)‖² ≤ C₂·(1 + #𝒯·(M·P^{−η/2}/η + log(2P)/√P + P log(2P)/Y))·(∑_p ‖a_p‖²/p²)·P/log P
```
with explicit `C₂`. Then **V-B-2**: with `η := (log(2T))^{−θ}`, `θ := primeLargeValuesExponent`, `M := (log(2T))^{m}`, `Y := 2T + P²`, this is the V-0 field's
right-hand side `C·(1 + #𝒯·exp(−log P/(log 2T)^{θ})·(log 2T)²)·…` once `M P^{−η/2}/η ≤ exp(−log P/(2(log 2T)^{θ}))·(log 2T)^{m+θ} ≤ exp(−log P/(log 2T)^{θ'})(log 2T)²`
for the class's exponent — **state V-B-2 with the region strength as a hypothesis** (a `ZeroFreeRegionData θ m` structure: `∀ T ≥ 1, hzero/hlog at
η = (log 2T)^{−θ}, Y = 2T + P², M = (log 2T)^m`) and conclude the class field for the exponent `θ' > θ` it supports; record exactly which `(θ, m)` give the
V-0 field at `primeLargeValuesExponent = 4/5` (e.g. `θ = 3/4 + 1/40`, any `m`, since `(log 2T)^{m+θ} e^{−x/2} ≤ e^{−x/(…)}` … — do the algebra and record).
Finally `theorem primeLargeValues_of_zeroFreeRegion (h : ZeroFreeRegionData …) : PrimeLargeValuesAssumption` as a **theorem producing the class**
(not an instance): this is the milestone — `trackR_edp_halasz` composed with it gives EDP conditional on the zero-free region alone; add
`trackR_edp_of_zeroFreeRegion` and its pin.

**Verification/report** as always (`lake env lean`, full `lake build MoltResearch.DiscrepancyAnalytic Conjectures`, gates, layering, coverage, `#print axioms`).
**Stop rule:** stop only if a needed complex-analytic ingredient is missing from Mathlib/the tree with no elementary substitute (record exactly which; e.g.
the Mellin representation's interchange, or the rectangle theorem's hypotheses) — constants and window choices are yours.
