# A1/R6/R7 design report — `[mrt]` A.1, the major-arc assembly, and the `mrp` wrapper (Track R)

Paper-first session, 2026-09-04. No Lean written before this report; one numeric
sanity script (`ucheck2.py`, reproduced in §4). Sources read in full for this
report: `[mrt]` = arXiv:1503.05121 `Chowla.tex` (§2 `S-def`/`excep`/`second`/`third`,
§"Proof of major arc estimate" `:527–630`, Appendix A `:806–1191`); `[MR]` =
arXiv:1501.04585 `ShorterIntervals55.tex` (`le:Halappl`, `le:Rupest`,
`le:Hallargevalint`, `le:Hallargevalprimes`, §8.3 "Bounding ∫_𝒰" `:1234–1310`);
Tao arXiv:1509.05422 (Proposition 2.4 and its proof, the `c_p = 1` remarks after
Proposition 2.6 and Remark 3.8); the in-repo `tao2015_a2iii_design_report.md`
(§1.4–1.8, §4, §5, errata 1–11) and `sources/tao2015_statements.md`; and the
statements of every tree object named below.

Campaign: issue #3044 (Track R), phases **R5 (A.2/A.1 assembly), R6, R7**.

---

## 0. Executive summary — read this first

1. **The A.2 inner band is not closed in a form A.1 can consume.** The schedule
   capstone `band_energy_typicalS_le_of_schedule` (#3655) concludes
   `∫_{K₁≤|ξ|≤K₂} ‖F‖²·w ≤ bandBudget c₃ ε (Δ/A)` with `w ≤ (4H/A)²`. For a fixed
   `c₃` that conclusion is **implied by the sharp mean value theorem alone** as soon as
   `A² ≥ 10⁷·H/ε³` — i.e. throughout the consumer's regime (`A ≥ A₀(H)`, `A → ∞`).
   To be non-trivial the consumer must read every `bandBudget` in the inner band at
   `c₃'' = (4H/A)²·c₃_report`. Under that reading the **level legs stay closed**
   (their fits are stated at fixed shares against the unweighted budget, exactly the
   report's §4.3 conditions), but the **exceptional cell fit `hscheduleUCell` fails by
   a factor between 10¹⁵⁰ and 10^{10⁶}** at every EDP-scale point checked (§4). The
   VI-8 closure of the exceptional leg is an artefact of `hscheduleUShare`'s right-hand
   side `(1/2^{J+1})/(4H/A)²`, which lets each exceptional share be `≍ (A/4H)²`.
2. **Why the exceptional leg fails: the tree deviates from `[MR]` §8.3 in five places**
   (§5), every one of them a power of `A` or a polylog too expensive: (a) the integer
   large-values input `Aint` is fed the *full* cell cover (`#K ≤ 2T`, so `Aint ≍ T^{3/2}`)
   where `[MR]` first bounds `|𝒯| ≪ T^{1/2−η}` by the top level's largeness; (b) the
   large-`Q` count `Γ` is a *second-moment* count (`∝ T/P`) where `[MR]` uses the
   `k`-th-moment `le:Rupest` count `exp((log X)^{1/48+o(1)})`; (c) the pointwise Halász
   envelope carries the Abel factor `3 + 2πT` (untwisted partial sums) where the twisted
   function must be used — `T ≍ A/(εH)`; (d) the envelope adds the *trivial* cost
   `log B + 2 ≍ log A` and the smooth mass `e¹²·log y ≍ log A` unconditionally, so it
   is `10¹⁷×` worse than the trivial bound on the quotient polynomial; (e) the S6 block
   `[exp((log A)^{49/50}), exp(log A/loglog A)]` is **empty** unless
   `(log A)^{1/50} > loglog A`, i.e. `log A ≳ 10¹²⁰`.
3. **The Halász regime was misread by VI-6.** The in-tree Halász
   (`halaszBudgetShell`, `cheap_halasz_twisted`) saves `≈ 10¹¹·loglog z·e^{−D}` at
   strength `D` and scale `z`; its consumer check (state file, "ρ ≈ 0.0606 closes")
   assumed **`D = ρ·loglog z` with `ρ = 1/6 − 1/(3π) = 0.0606`** — that is `[mrt]`
   Appendix A's `𝒯₁` constant, the strength supplied *by the repulsion lemma away from
   `t₁`*, not by the interface. VI-6 instead used the interface's *uniform, fixed*
   strength `2D` (`hNP : ∀ u, NonPretentiousAt g (2D) u`), for which the in-tree Halász
   gives no saving at all once `loglog z > e^{D}/10¹¹`. The `t₁`-split of `[mrt]` A.3
   (`𝒯₀` = the GHS leg, on main since #3373; `𝒯₁` = the repulsion-strength Halász, the
   **remaining R3 item**, never built) is not optional.
4. **A.1 is the wrong intermediate cut for the tree's major arcs (Finding D, §7).**
   Tao's remark that `[mrt, L2.2 + T2.3]` "can be replaced with the simpler `[mrt,
   Theorem A.1]`" presumes arcs of **bounded** denominator (Siegel–Walfisz-strength
   classification). The tree's `instPrimeBlockMajorArcAssumption` gives `q ≤ (log n₀)^{20}`.
   The character expansion of a residue class costs a factor `q` (`[mrt]` `:596–630`
   pays `q ≤ W` and absorbs it with A.2's `W^{−5/4}`), and an A.1-type error carries
   the `𝒮`-density `≍ 1/log h` which cannot beat `(log H)^{20}`. The order must be
   `[mrt]`'s: assemble the arcs on the **`𝒮`-restricted** sum (A.2 per twist `gχ̄`,
   which absorbs `q` through its `ε'`), and remove `𝒮ᶜ` **once**, at the top, for
   the untwisted count. A.1 becomes the `α = 0` corollary, not a step.
5. **R6 and R7 are small and can be built now against one explicit A.2 hypothesis.**
   Their content is bookkeeping the tree already half-owns (`ShortIntervalRestriction`,
   `MajorArcFreeze`, `ParsevalBridge`, `nonPretentiousAt_scale_transfer` +
   `mertens_mass_diff_le`, the `FilteredMR` socket). §8 gives the ladder: ≈ 9 units
   for R6, ≈ 7 for R7, all conditional on one named Prop `SliceMeanSquareA2` (§1.2).
   The exceptional-leg re-cut ("VI-9", §8 Phase 0, ≈ 14 units, needs the R3 `𝒯₁`
   Halász) is what discharges that Prop; it is the real remaining content and it is
   Codex-scale.
6. Two smaller structural facts that any instantiation must respect (§7): the cell
   representatives `hqcell*` force **every** e-adic cell in the index range to contain
   a prime (a Hoheisel-strength statement at resolution `1/(2N)`), so the index set must
   be filtered to nonempty cells; and the `𝒮`-density available in-tree is
   Turán–Kubilius (`∑_j 1/E_j`, not `∑_j e^{−E_j}`), so A.1 needs `J = O(1)` ordinary
   levels — which the tree's capstone allows (`J` is free) and which is also what the
   ε-form wants.

---

## 1. The targets, transcribed

### 1.1 `[mrt]` Theorem A.1 (`th:MRinCnotInS`, `Chowla.tex:810`)

> `f` 1-bounded multiplicative, `X ≥ h ≥ 10`:
> `(1/X)∫_X^{2X} |(1/h)∑_{x≤n≤x+h} f(n)|² dx ≪ e^{−M(f;X)}M(f;X) + (loglog h)²/(log h)² + (log X)^{−1/50}`.

Proof (`:1176–1191`): `η = 1/12`, `P₁ = (log h)^{480}`, `Q₁ = h`; split `n ∈ 𝒮` /
`n ∉ 𝒮`; the `𝒮` part is A.2; the complement is `|(1/h)#{window ∖ 𝒮}|²`, bounded by
`[MR] Thm 3 with f = 1` (the window count of `𝒮` is close to its block density) plus
`excep` (the block density of `𝒮ᶜ` is `≪ log P₁/log Q₁ = 480 loglog h/log h`). Hence
the **squared** density `(loglog h)²/(log h)²`.

**Tree form.** R6 does *not* consume A.1 (§7.3). A.1 is recorded as the `α = 0`
corollary of R7's chain (unit R7-7), in the slice shape of `WindowAssembly`, with the
`𝒮`-removal paid by A1-1's `sum_norm_sq_window_le_restricted_logavg` (cost: the density,
not its square — `[MR]`'s "f = 1" trick needs an A.2 *about the mean*, which the tree's
is not; the ε-form does not care):

```lean
/-- `[mrt]` A.1, tree form (corollary). -/
def ShortIntervalMeanSquareA1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ h₀ : ℕ, ∀ h : ℕ, h₀ ≤ h → ∃ A₀ : ℝ, ∀ A : ℕ, A₀ ≤ A →
    ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → (∀ n, ‖g n‖ ≤ 1) → g 1 = 1 →
      NonPretentiousAt g A₀ (2*A+1) →      -- strength ≥ A₀(h, ε), at the block's top
      ∀ s J : ℕ, 1 ≤ s → s ≤ ε*A/2 → A + J*s ≤ 2*A →
        ∑ n ∈ Finset.Ioc A (A + J*s), ‖∑ m ∈ Finset.Ioc n (n+h), g m‖^2 / n
          ≤ ε^2 * h^2 * ∑ n ∈ Finset.Ioc A (A + J*s), (1:ℝ)/n
```

The strength is `A₀` (a function of `h, ε` only), *not* `A`: the interface's
quantifier order (§1.3), and `[mrt] second`'s (`W ≤ exp(M/3)`, `W ≥ (log H)⁵`, i.e.
`M ≥ 15 loglog H`).

### 1.2 `[mrt]` Theorem A.2, tree form — the Prop everything is conditional on

```lean
/-- `[mrt]` A.2 (𝒮-restricted), per slice, ε-form.  `levels` is the `J₀`-level list
the instantiation fixes as a function of `(h, ε)` alone (§7.2, §8 A2-V), so that
`𝒮`-membership is the same predicate for every twist and every scale. -/
def SliceMeanSquareA2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ h₀ : ℕ, ∀ h : ℕ, h₀ ≤ h →
    ∃ (levels : List (Finset ℕ)) (A₀ : ℝ), (∀ P ∈ levels, ∀ p ∈ P, p.Prime) →
      ∀ A : ℕ, A₀ ≤ A →
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → (∀ n, ‖g n‖ ≤ 1) → g 1 = 1 →
        NonPretentiousAt g A₀ (2*A+1) →
        ∀ s J : ℕ, 1 ≤ s → s ≤ ε*A/2 → A + J*s ≤ 2*A →
          ∑ n ∈ Finset.Ioc A (A + J*s),
              ‖∑ m ∈ (Finset.Ioc n (n+h)).filter (HasFactorInAll levels), g m‖^2 / n
            ≤ ε^2 * h^2 * ∑ n ∈ Finset.Ioc A (A + J*s), (1:ℝ)/n
```

`[mrt]` A.2 (`th:MRinC`): `≪ e^{−M}M + (log h)^{1/3}/P₁^{1/6−η} + (log X)^{−1/50}`,
via Parseval + Proposition A.3. In the tree: `slice_energy_le_of_window_energy` (E-5)
+ `window_energy_le_of_low_mid` (E-4) + {low band, inner band = the capstone, outer
band `band_energy_outer_le`, tail `Mtot²·Eder/L²`}. §4 says what the capstone must
deliver for this composition to close. The right-hand side is
`window_logavg_eps_of_slice_budget`'s `hbudget` (G10c-0), so the log-averaged `L¹`
form follows by that lemma.

**Two facts R6 relies on.** (i) `HasFactorInAll levels (d₀·m) ↔ HasFactorInAll levels m`
whenever no prime of `d₀` lies in any level — true for `d₀ ≤ q ≤ (log H)^{20} < P₁`;
(ii) `g·χ̄` is completely multiplicative, `1`-bounded, and
`NonPretentiousAt (g·χ̄) A₀ x` follows from `NonPretentiousAt g A₀ x` for `q₀ ≤ A₀`
(the predicate already quantifies over all `χ` mod `q ≤ A₀`).

### 1.3 R6 — the major-arc assembly (`Chowla.tex:527–630`, adapted to `c_p = 1`)

Target `MatomakiRadziwillMajorArcAssumption.bound`
(`TrackCStage5MatomakiRadziwillMajorArc.lean`): for `ε, C > 0`, `B : ℕ`, ∃ `H₀`,
∀ `H ≥ H₀`, ∃ `A₀`, ∀ `A ≥ A₀`, ∀ `A ≤ w ≤ x`, ∀ `g` CM unimodular with
`NonPretentiousAt g A ⌈x⌉₊`, ∀ `α = a/q + δ` with `1 ≤ q ≤ C(log H)^B`,
`|δ| ≤ C(log H)^B/(Hq)`:

```
∑_{n ∈ (x/w, x]} ‖∑_{j=1}^{H} g(n+j) e(jα)‖ / (Hn) ≤ ε log w .
```

Tao's remark (1509.05422 after Prop 2.6, and Remark 3.8): for `g₂ = ḡ₁` one has
`c_p = 1`, the frequency set `Ξ_H` is major-arc, and "`[mrt, Lemma 2.2, Theorem 2.3]`
can be replaced with the simpler estimate in `[mrt, Theorem A.1]`". The paper's
major-arc section does, for `α = a/q + θ`, `q ≤ W`, `θ = O(W/(Hq))`:

1. **integration by parts** removes `e(θn)` at cost `(W/(Hq))·∫_0^{H/d}|…| dH'` — at
   our polylog widths this is the block **freeze** instead (`MajorArcFreeze`:
   `norm_sum_mul_exp_le_sum_blocks_add`, cost `H·2π|δ|ℓ` for blocks of length `ℓ`);
2. **residue split** `n ≡ b (mod q)`, `d₀ = gcd(b,q)`, `n = d₀m`, `g(n) = g(d₀)g(m)`
   (complete multiplicativity; `d₀ ≤ q < P₁` keeps `𝒮` intact — in the tree
   `𝒮`-membership of `d₀m` for `d₀` coprime to every level is `HasFactorInAll` of `m`);
3. **character expansion** `1_{m≡b₀ (q₀)} = (1/φ(q₀))∑_χ χ(b₀)χ̄(m)`
   (`sum_filter_residue_eq_char_avg`, in tree);
4. `y ≤ X/W^{10}` **trivially** (our "bad low blocks", §9.3), the rest in **dyadic
   blocks** (`sum_Ioc_eq_sum_dyadic_fibres`);
5. **A.2 per twist `gχ̄`**, at window length `ℓ/d₀`, on the `𝒮`-restricted sum
   (`𝒮` is preserved by `m ↦ d₀m`, §1.2(i)), with
   `M(gχ̄; X') ≥ M(g; X, W) − O(1)` (`NonPretentiousAt g A x` already quantifies over
   every `χ` mod `q ≤ A`, so `q ≤ C(log H)^B ≤ A₀(H)` is free; scale transfer by
   `nonPretentiousAt_scale_transfer` + `mertens_mass_diff_le`);
6. **Cauchy–Schwarz** `L¹ ← L²` (`sum_div_le_sqrt_mul_sqrt`).

The paper's accounting `∑_b (d₀/φ(q₀))∑_χ` has total weight `∑_{d₀|q} φ(q/d₀) = q`
(`:620`: "≪ q·HX/(dW^{5/4})", then "using q ≤ W"), so R6 costs a factor
`q ≤ C(log H)^B` in `ε`, absorbed by applying **A.2** at `ε' = ε/(4q)` — possible
because A.2's error has no density term (§7.3, §9.1). R6's output is the
**`𝒮`-restricted** twisted bound on one dyadic block.

### 1.4 R7 — the `mrp` wrapper (1509.05422, Prop 2.4 and its proof)

> "Applying `[23, Lemma 2.2, Theorem 2.3]` (with `W := log⁵ H`), we see that
> `(1/X)∑_{X≤n≤2X}(1/H)|∑_{j=1}^H g₁(n+j)e(αj)| ≪ loglog H/log H` for all
> `x/2ω ≤ X ≤ 2x`; […] `X ≥ x/2ω ≥ log² x ≥ log² A`, hence `W = log⁵ H` will be much less
> than `A` or `(log X)^{1/125}`. Averaging this estimate from `X` between `x/2ω` and
> `2x`, we obtain (2.5)."

So R7 is: dyadic decomposition of `(x/w, x]`, per block the `𝒮`-restricted twisted
R6 bound in log-averaged `L¹` form, summed to `(ε/2) log w`; the **`𝒮ᶜ` removal, once**
(`‖∑_{window} g e(·α)‖ ≤ ‖∑_{window∩𝒮} …‖ + #(window ∖ 𝒮)`, then `sum_card_window_le`
and the block density `≤ (ε/4)·∑1/n` by `window_typicalS_complement_le` — this is
`[mrt]` `excep` used exactly as Tao's proof of Prop 2.4 uses `[23, Lemma 2.2]`); plus
the **bad-block** bookkeeping R0
found glossed (§9.3): the hypothesis at scale `x` transfers to a block at scale `X` at
cost `2(loglog x − loglog X + 12)`, which is unaffordable for `X ≤ x^{e^{−(A−A₀)/2}}`;
those blocks exist only when `w` is within that factor of `x`, are at most
`log x·e^{−(A−A₀)/2}/log 2 ≤ 2 log w·e^{−(A−A₀)/2}/log 2` in number, and cost `log 2`
each by the trivial bound. Packaging: `theorem matomakiRadziwillMajorArc_of_A2
(hA2 : SliceMeanSquareA2) : MatomakiRadziwillMajorArcAssumption` — a theorem
producing the class, not an instance (the class docstring forbids instances until the
content is formalised; the content *is* `hA2`). Composed with the discharged
`instPrimeBlockMajorArcAssumption`, `filteredMR_of_majorArc` (`TrackCStage5FilteredMR.
lean:237`) then gives `FilteredMR`, `elliott_master_majorArc`, and
`edp_of_majorArcMR` conditional on exactly `{SliceMeanSquareA2}`, i.e. on the two
large-values interfaces once A2 is discharged.

---

## 2. Substrate audit (what the tree has; nothing here needs to be rebuilt)

| need | tree object | status |
|---|---|---|
| per-slice harness, energy slots | `slice_energy_le_of_window_energy` (E-5), `window_energy_le_of_low_mid` (E-4), `window_energy_regime_energy_le` (E-2) | ✅ |
| slice window + bump plumbing | `exists_slice_window'`, `exists_bump_deriv_bound`, `slice_rIn_lower`, `slice_ratio_upper/lower` | ✅ (as used by `slice_energy_le`) |
| window transform sup / decay | `norm_fourier_slice_window_le` (`(4H/A)²`), `norm_fourier_slice_window_decay` (`2B'/(π|ξ|)`) | ✅ |
| low band `|ξ| < K` | `low_band_block_sup` (plain block, twisted cheap Halász) + inclusion–exclusion `sum_typicalS_eq_inclexcl` + `nonPretentiousAt_levelFreeTwist` | ✅ pieces, no composition |
| outer band | `band_energy_outer_le`, `outer_le_budget` | ✅ |
| inner band | `band_energy_typicalS_le_of_schedule` | ⚠️ §4–§6 |
| `L¹ ← L²`, dyadic, slices → log-avg | `sum_div_le_sqrt_mul_sqrt`, `sum_Ioc_eq_sum_dyadic_fibres`, `window_logavg_eps_of_slice_budget` | ✅ |
| `𝒮`-removal cost | `sum_card_window_le`, `card_le_mul_logavg`, `sum_norm_sq_window_le_restricted(_logavg)` (A1-1) | ✅ (Icc windows, no `1/n`; reshape needed) |
| `𝒮`-density | `window_typicalS_complement_le` (block, TK), `typicalS_complement_logavg_le` (range, TK) | ✅ (§7.2) |
| phase freeze, residue → characters | `norm_sum_mul_exp_freeze_sub_le`, `norm_sum_mul_exp_le_sum_blocks_add`, `sum_filter_residue_eq_char_avg` | ✅ |
| scale transfer of non-pretentiousness | `nonPretentiousAt_scale_transfer`, `mertens_mass_diff_le` | ✅ |
| twisted CM function is CM / non-pretentious | `CompletelyMultiplicativeC.mul`, `completelyMultiplicativeC_natCast_cpow`, `nonPretentiousAt_archTwist`; for `χ`: `charTwist`, `NonPretentiousAt` already ranges over `χ` | ✅ |
| socket | `matomakiRadziwill_filtered_bound`, `filteredMR_of_majorArc`, `elliott_master_majorArc`, `edp_of_majorArcMR` | ✅ |
| exceptional-leg ingredients `[MR]` §8.3 uses | `measure_large_prime_poly_le` (`le:Rupest`, measure form), `card_large_prime_poly_le` (second moment only), `firstPrevLargePart_*` (top-level largeness refinement), `cheap_halasz_twisted`, `pretentiousDistSq_twist_ge` (repulsion, mid regime), GHS `rieszMean_log_le_of_nonPretentious` | ⚠️ present but **not plumbed** into the 𝒰 leg |

---

## 3. What is missing

The two things the A.1 survey (state file, 2026-09-03) recorded remain true — no
theorem removes the `𝒮`-restriction from a slice bound, and R6 has one lemma. The
four findings below (§4–§7.3) are new.

---

## 4. Finding A — the weight accounting

`band_energy_le_budget` (BandCapstone) charges each part `Cw·∫_{part}‖F‖² ≤ κ·𝔅` and
concludes `∫_G ‖F‖²·w ≤ 𝔅` for `w ≤ Cw = (4H/A)²`. The assembly (VI-5) discharges the
level legs from fits `unweighted_cost ≤ kappa·𝔅` with
`hshare : (4H/A)²·(2·kappaMain + 2·kappaReplacement + 2·kappaCollision) ≤ 1/2^{j+1}`,
and VI-8 instantiates the level shares as the **fixed** `ordinaryLegShare j = 3/(64·2^{j+1})`
(`ordinaryLegShares_fit` under `3H ≤ A`). The exceptional level instead has
`hscheduleUShare : 2·#I_𝒰·∑κ_U + 2κ_repl + 2κ_coll ≤ (1/2^{J+1})/(4H/A)²`, i.e. each
exceptional share may be `≍ (A/4H)²`.

**The consumer's target.** Feed the harness `h' m := 1_𝒮(m)·g m·(A/m)` (1-bounded on
`(A, 2A+1]`), so the plain polynomial is `A·F_norm` and the plain window sum is
`A·∑ g m/m`; the time-side conversion `‖∑_{(n,n+H]} g m − (n/A)·A∑ g m/m‖ ≤ H²/n` is
elementary (§8, A2-IV-2). The slice target `ε²H²∑_{slice}1/n` forces the mid slot
`Emid = A²·∫_{mid}‖F_norm‖²·w ≲ ε²H²s/(36A)`, i.e.

```
∫_{inner} ‖F_norm‖²·w  ≤  (H/A)²·(ε²ρ/36)   =   (4H/A)²·bandBudget c₃ ε ρ   with c₃ = 2/9 .
```

The report's §4.1 budget `𝔅 = c₃ε²ρ/8` is the **unweighted** normalised budget, derived
*through* the sup `(4H/A)²`; the capstone applies to the **weighted** energy. So the
capstone must be used at `c₃'' = (4H/A)²·c₃_report`, under which every leg is charged
its unweighted cost against the report's `𝔅` — the level legs exactly as VI-8 states
them (unchanged), the exceptional leg with shares summing to `1/2^{J+1}` (not
`(A/4H)²/2^{J+1}`).

**The numbers.** `ucheck2.py` (mpmath), all formulas copied from the Lean definitions
(`exceptionalIntegerSchedule`, `exceptionalPrimeSchedule`, `exceptionalRatioSchedule`,
`exceptionalDeltaSchedule ≥ 2^J·e¹²·log y·(2 + log B)`, `exceptionalCellScheduleCost`),
at S1–S7 (`W = (log H)⁵`, `ε = W^{−5/4}`, `c₃ = 1/48`, `B' = 2`, `K₂ = γB'A/(2πH)`,
`T = K₂ + 2`, `q = P_𝒰 = exp((log A)^{49/50})`, `J = 1`):

| `log A` | `log H` | `log₁₀ T` | `log₁₀ cost_v` | `log₁₀(κ_correct·𝔅)` | `log₁₀(κ_VI8·𝔅)` | `log₁₀(Cw·trivial)` vs `log₁₀ 𝔅` |
|---|---|---|---|---|---|---|
| 300 | 20 | 134 | **125** | −31 | 211 | −246 vs −27 |
| 3 000 | 40 | 1 297 | **1 084** | −38 | 2 532 | −2 579 vs −33 |
| 30 000 | 60 | 13 016 | **10 988** | −42 | 25 962 | −26 014 vs −36 |
| 300 000 | 100 | 130 260 | **112 220** | −47 | 260 440 | −260 500 vs −40 |
| 3·10⁶ | 150 | 1.30·10⁶ | **1.15·10⁶** | −51 | 2.61·10⁶ | −2.61·10⁶ vs −44 |

Read across: `cost_v` is a power of `A` (`≈ T^{0.85}`), the correct per-cell budget is
`10^{−31}…10^{−51}`, VI-8's inflated budget `10^{211}…10^{2.6·10⁶}` absorbs it; and the
last column is the vacuity: the **weighted trivial bound** `(4H/A)²·e^π(T/A+2)·ρ`
sits `10^{220}…10^{2.6·10⁶}` below `𝔅`. (The block `[P_𝒰, Q_𝒰]` is empty at all five
points — §5(e) — so `#I_𝒰` was taken as the formula's absolute value; the conclusion
does not depend on it.)

**Consequence.** `band_energy_typicalS_le_of_schedule` is true and sorry-free, but in
the consumer's regime it is implied by `intervalIntegral_norm_sq_poly_le_sharp_ratio`
plus `hwsup`. The level legs (VI-2 … VI-8a–e) are genuine and survive the correct
accounting; the exceptional leg (IV-3e, VI-1d, M-5, M-6, VI-3, VI-6, VI-7-1, VI-8f) does
not. The repair of the *statement* is one wrapper: apply the capstone at `c₃''`,
conclude `≤ (4H/A)²·bandBudget c₃ ε ρ`, keep the level fits, tighten
`hscheduleUShare` to `≤ 1/2^{J+1}`. The repair of the *leg* is §8 Phase 0.

---

## 5. Finding B — the exceptional leg against `[MR]` §8.3

`[MR]` (`:1234–1310`), for `t ∈ 𝒰`, with the `𝒰`-block Ramaré step
(`P = exp((log X)^{1−1/48})`, `Q = exp(log X/loglog X)`, `H = (log X)^{1/48}`):

1. discretise: well-spaced `𝒯 ⊆ 𝒰`, `∫_𝒰|QR|² ≤ 2∑_{t∈𝒯}|Q|²|R|²`;
2. **`|𝒯| ≪ T^{1/2−η}X^{o(1)}`** — every `t ∈ 𝒰` has some level-`J` cell polynomial
   large, and `le:Rupest` (the `k`-th moment, `k = ⌈log T/log P_J⌉`) counts those `t`;
3. split at `|Q_{v,H}| = (log X)^{−100}`;
4. `𝒯_S`: `(log X)^{−200}·∑_𝒯|R|²` with `le:Hallargevalint`
   `≪ (Xe^{−v/H} + |𝒯|√T)·log(2T)/(Xe^{−v/H})` — **`|𝒯|√T ≤ T^{1−η} ≤ N`**, so this is
   `(log X)^{−199}`;
5. `𝒯_L`: **`|𝒯_L| ≪ exp((log X)^{1/48+o(1)})`** by `le:Rupest` on `Q_{v,H}` at
   `V = (log X)^{100}`; `max|R| ≪ (log X)^{−1/16+o(1)}(log Q/log P)` by `le:Halappl`;
   `∑_{𝒯_L}|Q|²` by `le:Hallargevalprimes`
   `≪ (P + |𝒯_L|P·e^{−log P/(log T)^{2/3+ε}}(log T)²)∑|a_p|²/log P`;
6. total `H(log X)²·(log X)^{−1/8}(log Q)²/(log P)⁴ ≪ (log X)^{−1/48}`.

The tree's IV-3e/VI-1d exceptional estimate is `2(V₀²·Aint + δ²·Bpri·(1 + Γ/V₀²))`,
optimised to `2δ²Bpri + 4δ√(Aint·Bpri·Γ)`, with (M-5, M-6, VI-6, VI-8):

| `[MR]` step | tree | gap |
|---|---|---|
| 2: `|𝒯| ≪ T^{1/2−η}` via top-level largeness | cover `K = bandCells K₂`, `#K ≤ 2T` (`card_cells_le`), fed to IK 9.6 | `Aint ≍ T^{3/2}` instead of `≍ N`; a factor `T^{1/2+η} ≍ A^{0.6}` |
| 5: `|𝒯_L| ≪ exp((log X)^{1/48+o(1)})` via `le:Rupest` | `Γ ∝ ((T+1)/P + 4)` — a second-moment (Ramaré-`λ`) count (`exists_lam_exceptional_ratio_le`) | `T/P ≍ A^{1−o(1)}` instead of `exp((log A)^{1/50+o(1)})` |
| 5: `max|R|` by Halász on the **twisted** function | `cellHalaszLongCost = partialBudget·(3+2πT)/a` from **untwisted** partial sums (`norm_short_poly_le_sup_partial`) | factor `2πT ≍ A/(εH)` |
| 5: smooth mass `∏_{p∈[P,Q]}(1−1/p)^{−1} ≍ log Q/log P` | `pSmoothHarmonicMass ≤ e¹²·log y` (Rankin over all `y`-smooth) | factor `log A/loglog A` |
| — | `cellHalaszScheduleQuotientBound := … + 1 + (log B + 1)` adds the **trivial** long-branch cost unconditionally | envelope `≥ log A` for a polynomial whose trivial bound is `≍ ε` |
| S6 block | `P_𝒰 = exp((log A)^{49/50}) > Q_𝒰 = exp(log A/loglog A)` unless `(log A)^{1/50} > loglog A` | the block is **empty** for `log A ≲ 10¹²⁰` |

Each row alone breaks the fit by a power of `A` or of `log A`; the first two are the
structural ones and they are exactly the two `le:Rupest` applications the tree never
made (`measure_large_prime_poly_le` exists in measure form; the cardinality form for
well-spaced maxima needs one Gallagher/Sobolev-type unit). `firstPrevLargePart_*`
(LevelLegs) already refines the exceptional part by "the least failing cell at the
previous level", which is precisely the largeness step 2 needs.

**On S6 at fixed `ε`.** The ε-form does not need `(log X)^{−1/50}`. Redoing step 6 with
free `(P, Q, N_𝒰)`: the prefactor of `δ²` is `≍ N_𝒰·(log Q/log P)²`, the sift term is
`log P/log Q`, the collars need `N_𝒰 ≳ C/ε³` and `N_𝒰·Q ≤ A` (erratum 10), Lemma 8
needs `log P ≥ C(log T)^{3/4}`. Choosing `log Q/log P = C/ε³` gives a prefactor
`≍ C³/ε⁹` and a sift term `ε³/C`: a **fixed** pointwise saving `δ ≲ ε⁶` suffices, and
the block is nonempty. This is the S6 to instantiate; it removes the `(log A)^{−1/50}`
calibration and with it the `W ≤ (log A)^{1/320}` re-tune (S-cal-5), which was priced
against `[MR]`'s `(4/ε²)·D` shape and not against the tree's cost expression.

---

## 6. Finding C — the Halász strength regime

`halaszBudgetShell A z / (z log z) ≈ 800·loglog z/log z + 10¹¹·loglog z·e^{−A}` (the
`√((e⁵(2+log z)e^{−A})² + 1)` term). `cheap_halasz_twisted` / `low_band_block_sup`
give `‖block‖ ≤ 2n₂(ε' + e^{W·loglog n₂ + W − A'/2})`. At **fixed** `A'` and scale
`n₂ → ∞` these are vacuous; the saving exists only for `loglog n₂ ≲ A'/(2W)`.

The state-file consumer check ("ε ≈ loglog²·e^{−A} + C·loglog/log ⟹ with
`A = ρ·loglog`, ε ≈ (log)^{−ρ+o(1)}, ρ ≈ 0.0606 closes") is exactly `[mrt]` A.3's
`𝒯₁` regime: for `|t − t₁| > (log X)^{1/16}/2`,
`𝔻(fg_𝒥, p^{it}; X)² ≥ (1/6 − 1/(3π) − ε)·loglog X` (Chowla.tex `:904–960`, the
repulsion lemma (ii)), and `1/6 − 1/(3π) = 0.0606…`. So the in-tree Halász was built
for, and checked in, the regime "strength `≍ ρ·loglog(scale)` supplied by repulsion".
VI-6 (`norm_typicalS_quot_block_poly_le`, `hNP : ∀ u ∈ [10¹⁶, 3B/q], NonPretentiousAt g
(2D) u`) applied it at the interface's **uniform fixed** strength, where it saves
nothing as `A → ∞`. Independently of Finding B, then, the exceptional leg needs the
`t₁`-split of A.3:

- **`𝒯₀ = {|t − t₁| ≤ (log X)^{1/16}} ∩ band`**: `F(1+it) ≪ e^{−M/2}/(1+|t−t₁|) +
  (log X)^{−1/16}` (`eq:T0claim`, via `le:T0est` — the GHS leg, on main:
  `rieszMean_log_le_of_nonPretentious`, `rieszMean_log_le_closed`, #3368–#3373). The
  `e^{−M}` here must be **loglog-free** (it is the only place the interface's fixed
  `A` is spent); whether the in-tree closed form is, must be audited (its statement
  carries `LL` factors).
- **`𝒯₁`**: distance `≥ ρ·loglog u` from the repulsion lemma — mid regime
  `(log X)^{1/16} ≤ |t−t₁| ≤ (log X)^{20}` is `pretentiousDistSq_twist_ge`-shaped
  (in tree, `Repulsion.lean:222`); far regime `|t−t₁| > (log X)^{20}` needs
  equidistribution of `(t−t₁)log p` (Erdős–Turán + `ζ` bounds; R0: replayable with
  `TruncatedBridge` + `zeta_LSeries_bound`). Then the twisted cheap Halász at strength
  `ρ·loglog u` gives `(log u)^{−ρ+o(1)}` — the **remaining R3 item** ("GS-Decay-Cor-1
  Halász for the `𝒯₁` leg", never started).

With the fixed-`ε` S6 of §5 the `𝒯₁` saving needed is only `ε⁶`, but the *mechanism*
(strength growing with the scale) is still required, because a fixed strength `D`
gives `10¹¹·loglog u·e^{−D}`, which is not `≤ ε⁶` uniformly in `u`.

---

## 7. Two smaller structural items

### 7.1 Cell representatives (`hqcell*`)

`hqcelll : ∀ j < J, ∀ v ∈ Ico (v₀l j) (v₁l j + 1), ql j v ∈ eadicCell (Pl j) (2·Nl j) v`
(and `hqcellU`) require **every** cell of the contiguous index range to be nonempty —
a prime in every `(e^{v/2N}, e^{(v+1)/2N}]`, a Hoheisel-strength statement at
`N ≳ C/ε³`; even `N = 1` (ratio `e^{1/2} < 2`) is beyond Bertrand. Uses: 6 in
`LevelLegs`, 9 in the Assembly, 5 in the Family file, 4 in the Schedule file, 3 in
`BandCapstone`, 2 in `WindowAssembly`. The base lemmas
(`intervalIntegral_norm_sq_cell_fibre_sub_le`, `_cell_replace_le`,
`quotient_scale_le_cell_scale`) use `hq` only through `eadicCell_bounds` (the scale
`e^{v/2N} ≤ q < e^{(v+1)/2N}`) and, in `_replace_le`, to make the cell's sum
nonvacuous. Fix (A2-V-1): weaken every `hqcell*` to
`(eadicCell P (2N) v).Nonempty → q v ∈ eadicCell P (2N) v`, with `q v := 1` on empty
cells (then `hq1`, `hqA`, `hBqCutoff` hold trivially and `hqmin/hLA/hLB` are vacuous);
each of the ~29 uses is either under a `∀ p ∈ cell` (vacuous when empty) or a per-cell
integral that is `0 = 0` when empty. Alternatively index by `I := (Ico …).filter
Nonempty` — more invasive (`cellCount_le`, `hcov*`, the `firstPrevLargePart` least
index).

### 7.2 The `𝒮`-density and the number of levels

In-tree density is Turán–Kubilius: `window_typicalS_complement_le` gives, on
`Ioc A B`, `∑_{n∉𝒮}1/n ≤ ∑_{P∈levels}[(E_P·∑1/n + O(#P²/A))/E_P²] ≈ (∑_P 1/E_P)·log(B/A)`,
`E_P = ∑_{p∈P}1/p ≍ log(log Q/log P)`. `[mrt]`'s `excep` (fundamental lemma) gives
`∑_j e^{−E_j} = ∑_j (1/j²)(log P₁/log Q₁)`, summable in `j`; `∑_j 1/E_j` is **not**
(`E_j ≍ E₁ + 2 log j`), so A.1 via TK needs `J = O(1)`. That is available: `J` is free
in the capstone, the exceptional block `Pu` is itself a level of `𝒮`
(`innerBandLevels Pl Pu J = (List.range J).map Pl ++ [Pu]`), and for the ε-form
`J = 1` (one ordinary level `[P₁, Q₁]` + the `𝒰` block) is enough: density
`≈ 1/E₁ + 1/E_𝒰` with `E₁ ≍ log(log h/(25 log W)) → ∞` in `h` and
`E_𝒰 ≍ log(C/ε³)` by the fixed-`ε` S6. Hence `h₀(ε) ≈ exp(exp(C/ε))` for the once-paid removal (§7.3). The A.1
error is the density (not its square, §1.1): fine for the ε-form. (A sieve-strength
density is *not* out of reach — Brun's pure sieve on a dyadic block for the tiny
sifting set `[P₁,Q₁] ⊂ [1,h]`, `h^{2k} ≪ A`, or the Track S Selberg machinery
`card_rough_interval_le` — but nothing needs it once the order of §7.3 is followed.)

### 7.3 Finding D — restrict first, remove `𝒮ᶜ` last

The residue split + character expansion of R6 turns one class sum of trivial size
`H/q` into an average of `φ(q₀)` full sums of trivial size `H/d₀`: summed over the
classes, the bound is `q` times what the classes' own mass would suggest. `[mrt]`
pays this (`:620–630`, "`≪ qHX/(dW^{5/4})`, using `q ≤ W`") and absorbs it in A.2's
`W^{−5/4}`. Tao's `c_p = 1` shortcut ("replace `[mrt, L2.2 + T2.3]` by A.1") is
stated for arcs "of bounded denominator" (Remark 3.8), where `q = O_ε(1)`; that
classification is Siegel–Walfisz-strength. The tree's classification (R4v,
`instPrimeBlockMajorArcAssumption`) is Vinogradov Type I/II alone: `q ≤ (log n₀)^{20}`.

With `q ≍ (log H)^{20}`, applying an **A.1**-type bound per twist at accuracy
`ε' = ε/(4q)` would need its density term `≤ ε'² ≍ ε²/(log H)^{40}`; the density is
`≍ log P₁/log Q₁ ≥ 21 log W/log h ≥ 105 loglog H/log H` (sieve) or `≍ 1/loglog h` (TK),
and `Q₁ ≤ h ≤ H`. Impossible — even `[mrt]`'s squared density `(loglog h/log h)²`
loses to `(log H)^{−40}`. Applying **A.2** per twist has no density term: its error
`e^{−M}M + (log h)^{1/3}/P₁^{1/6−η} + [𝒰]` is `≤ ε'²` for `P₁ = W^{25} ≥ (log H)^{125}`,
`A₀ ≥ 2 log(16q²/ε²) ≈ 80 loglog H + 2 log(16/ε²)` (Tao: "`W = log⁵ H` will be much less
than `A`"), and the fixed-`ε'` S6 of §5. Then the complement is removed once, for the
untwisted count `#(window ∖ 𝒮)`, at cost `density·∑1/n ≤ (ε/4)∑1/n` — TK suffices
(`1/E₁ ≍ 1/loglog H`). **So the chain is A.2 → R6 (restricted) → R7 (removal once,
dyadic, bad blocks) → interface, and A.1 is a corollary.** The A1-1 lemmas (#3606)
are exactly the removal step, in the right shape; nothing built for A.1 is wasted,
but no further A.1 units should be cut.

---

## 8. The corrected campaign

Conventions as in the A2-III report. **Two tracks run in parallel**: the
R6/R7 chain against the named Prop `SliceMeanSquareA2` (buildable now, ≈ 16 units), and the
exceptional-leg re-cut that discharges it (Phase 0, Codex-scale).

### Phase 0 — "VI-9": the exceptional leg re-cut (discharges `SliceMeanSquareA2`)

- **VI-9a** (accounting wrapper, `TrackCStage5InnerBandSchedule.lean`):
  `band_energy_typicalS_le_of_schedule'` concluding
  `≤ (4H/A)²·bandBudget c₃ ε ρ`, level fits verbatim, `hscheduleUShare' : … ≤ 1/2^{J+1}`.
  Two lines of algebra; it makes the vacuity of the old statement and the failure of
  the exceptional fits visible in the tree.
- **VI-9b** `card_large_prime_poly_pow_le`: the cardinality `le:Rupest` for a
  `1`-separated set of cell maxima, from `measure_large_prime_poly_le` (`ℓ`-th moment)
  and the unit-cell sampling of VI-1d-1 (a Gallagher/Sobolev step or the
  derivative bound `norm_deriv_dirichlet_kernel_le`).
- **VI-9c** the exceptional cover: `#{cells of [−T,T] meeting bandPartOn … J}
  ≤ ∑_{r∈I_{J−1}} #{cells with |Q_r| > small_r}`, via `firstPrevLargePart_*` and
  VI-9b at `k = ⌈log T/log P_{J−1}⌉`; then IK 9.6 (`HalaszLargeValuesAssumption`)
  with this `𝒯` — `Aint ≍ N`.
- **VI-9d** the `𝒯_S/𝒯_L` split at `V₀ = (log A)^{−100}` with `|𝒯_L|` by VI-9b on the
  `𝒰` cell polynomial; `Γ` replaced by `|𝒯_L|·e^{−log P/(log 2T)^{3/4}}·(log 2T)²`
  (the `PrimeLargeValuesAssumption` shape, no `T/P`).
- **VI-9e** the pointwise `|R_v(t)|` via `cheap_halasz_twisted` on
  `levelFreeTwist g · n^{−2πit}` (no Abel factor in `T`), smooth mass
  `exp(2∑_{p∈P}1/p)`, short branch priced by its own harmonic mass — replaces
  `cellHalaszBound`; keep `cellHalaszThreshold`.
- **VI-9f** the `t₁`-split: `t₁ := argmin` of the twisted distance over the band;
  `𝒯₀ := {|t−t₁| ≤ (log A)^{1/16}} ∩ band` by the GHS leg + `eq:T0claim`'s
  `1/(1+|t−t₁|)` integration; `𝒯₁` strength `ρ·loglog u` from `pretentiousDistSq_twist_ge`
  (mid) + the far-regime equidistribution lemma (**new**, the R3 remainder).
- **VI-9g** the fixed-`ε` S6 (`log Q_𝒰/log P_𝒰 = C/ε³`, `N_𝒰 ≍ C/ε³`,
  `log P_𝒰 ≥ C(log T)^{3/4}`, `N_𝒰 Q_𝒰 ≤ A`) and the exceptional fits at it; errata
  12–14 (§4, §5(e), §6) into the A2-III report.

### Phase A2-IV — the per-slice A.2 statement (`Conjectures/…/TrackCStage5SliceA2.lean`)

- **A2-IV-0** the accounting theorem: from `∫_{inner}‖F_norm‖²w ≤ (4H/A)²𝔅_report`,
  the outer band (`band_energy_outer_le` at S2's `K₂`, `outer_le_budget` at `c₃''`),
  the low band and the tail, conclude the slice energy `≤ ε²H²∑_{slice}1/n` via E-5 +
  E-4. This settles §4 mechanically and is independent of Phase 0.
- **A2-IV-1** the low band `|ξ| ≤ K` for the `𝒮`-restricted polynomial:
  `sum_typicalS_eq_inclexcl` (`2^{J+1}` terms) + `low_band_block_sup` per free twist
  (`nonPretentiousAt_levelFreeTwist`); `K ≍ C/ε³` is forced by `g = 1`
  (`|F_norm(ξ)| ≈ 1/(2π|ξ|)` beyond `1/ε`), so the inner band starts at `K₁ = K`.
- **A2-IV-2** the weight conversion `‖∑_{(n,n+H]} g m − (n/A)·∑_{(n,n+H]} g m·A/m‖ ≤ H²/n`
  and its `L²` form over a slice (`≤ 2·((A+s)/A)²·… + 2H⁴s/A³`).
- **A2-IV-3** `SliceMeanSquareA2` from A2-IV-0..2 + Phase 0's capstone.

### Phase A2-V — the instantiation

- **A2-V-1** nonempty-cell weakening of `hqcell*` (§7.1), with `ql j v := (cell).min'`
  on nonempty cells.
- **A2-V-2** the level `[P₁, Q₁]`, `P₁ = ⌈W^{25}⌉`-scale (the level-one `P`-fit has
  slack to `W^{21}`), `Q₁ = ⌊h/W³⌋`, `J = 1`, e-adic data, `htop/hbot`, `hNbb`.
- **A2-V-3** the `hschedule*` numerics for level one at S1–S7 (errata 9–11 carried).
- **A2-V-4** the exceptional block at the fixed-`ε` S6 and its fits (after VI-9g).

### (no Phase A1) — the `𝒮`-removal lives in R7-3; A.1 is R7-7

### Phase R6 — the major-arc assembly on the `𝒮`-restricted sum
(new leaf `MoltResearch/Discrepancy/MajorArcAssembly.lean`, importing `MajorArcFreeze`
+ `TypicalFactorization`; the A.2-consuming units in `Conjectures/…/TrackCStage5MajorArcA2.lean`)

- **R6-1** `∑_{j∈Icc 1 H} g(n+j)e(jα) = e(−nα)·∑_{m∈Ioc n (n+H)} g m·e(mα)` (norms equal),
  and the `𝒮`-restricted/complement split of the window sum.
- **R6-2** `HasFactorInAll levels (d₀m) ↔ HasFactorInAll levels m` for `d₀` coprime to
  every level; `𝒮`-restricted residue split with `d₀ = gcd(b, q)`:
  `∑_{m∈window∩𝒮} g m e(ma/q)φ(m) = ∑_{d₀|q} g(d₀)∑_{b: gcd=d₀} e(ba/q)
  ∑_{m'∈Ioc (n/d₀) ((n+H)/d₀) ∩ 𝒮, m'≡b₀ (q₀)} g m'·φ(d₀m')` (CM, `Nat.div` bookkeeping).
- **R6-3** character expansion of the class sum (`sum_filter_residue_eq_char_avg`);
  `gχ̄` CM and `1`-bounded; `NonPretentiousAt (g·χ̄) A x ⟸ NonPretentiousAt g A x`
  for `q₀ ≤ A` (reindex `charTwist`).
- **R6-4** the freeze at block length `ℓ := ⌊εHq/(16πC(log H)^B)⌋` inside each class
  (frequency `d₀δ`, blocks of `ℓ/d₀` in `m'`): total cost `≤ H·2π|δ|ℓ ≤ εH/8` per `n`
  (`norm_sum_mul_exp_le_sum_blocks_add`).
- **R6-5** the shifted-window averaging: for fixed `(d₀, b, χ, k)`, the `n`-average
  over `Ioc A (2A)` of `‖∑_{m'∈window_k(n)∩𝒮} gχ̄(m')‖/(Hn)` is
  `≤ d₀·(ℓ/H)·[A.2's `L¹` bound for `gχ̄` at length `ℓ/d₀`, scale `A/d₀`]` — each `n'`
  is hit by `≤ d₀` values of `n`, and `n ≥ d₀n'/2`.
- **R6-6** summing over the `H/ℓ` blocks, the `q` weighted class/character pairs and
  the freeze cost: the restricted twisted log-averaged bound on one dyadic block at
  `ε/2`, given `SliceMeanSquareA2` at `ε' = ε/(4q)` and `ℓ/q ≥ h₀(ε')`.
- **R6-7** transfer of `NonPretentiousAt g A ⌈x⌉₊` to the block scale
  (`nonPretentiousAt_scale_transfer` + `mertens_mass_diff_le`): strength
  `A − 2(loglog x − loglog X + 12) ≥ A₀(ℓ/q, ε')` when `log X ≥ log x·e^{−(A−A₀−24)/2}`.
- **R6-8** the packaged per-block theorem `majorArc_block_bound_restricted`.
- **R6-9** the `α = 0`, `q = 1` specialisation (no freeze, no characters), for R7-7.

### Phase R7 — the `mrp` wrapper (`Conjectures/…/TrackCStage5MajorArcMR.lean`)

- **R7-1** dyadic decomposition of `Ioc ⌊x/w⌋₊ ⌊x⌋₊` (`sum_Ioc_eq_sum_dyadic_fibres`)
  with each fibre inside one `Ioc A (2A)` block.
- **R7-2** the good/bad block split at `X* := x^{e^{−(A−A₀−24)/2}}`; bad blocks exist
  only if `log w > log x(1 − e^{−(A−A₀−24)/2})`, number
  `≤ 2 log w·e^{−(A−A₀−24)/2}/log 2`, trivial cost `≤ log 2 + 1` each.
- **R7-3** the `𝒮ᶜ` removal, once, on a good block: `‖∑_{window} g e(·α)‖ ≤
  ‖∑_{window∩𝒮} …‖ + #(window ∖ 𝒮)`; `sum_card_window_le` (A1-1) reshaped to `Ioc`
  windows with `1/n` weights; the block density from `window_typicalS_complement_le`
  at the `J₀` levels, `≤ (ε/4)∑1/n` once `E_P ≥ 8J₀/ε` for every level (Mertens lower
  bounds `log_log_le_sum_one_div_primesBelow`, `mertens_mass_diff_le`), which fixes
  `H₀(ε)`.
- **R7-4** good blocks: R6-8 at `ε/2` + R7-3 summed to `(3ε/4)·(log w + 1)`.
- **R7-5** `A₀(H, ε, C, B) := A₀^{A.2}(ℓ(H)/q, ε/(4C(log H)^B)) + 2 log(8/(ε log 2)) + 26`
  (R0's shape `15 loglog H + 2 log(2C/ε)` with the A.2 threshold in place of
  `15 loglog H`).
- **R7-6** `theorem matomakiRadziwillMajorArc_of_A2 (h : SliceMeanSquareA2) :
  MatomakiRadziwillMajorArcAssumption`; then `edp_of_sliceMeanSquareA2` through
  `filteredMR_of_majorArc` and `edp_of_majorArcMR`; audit pin; card note.
- **R7-7** `ShortIntervalMeanSquareA1` from R6-9 + R7-3 (`[mrt]` A.1 in tree form, the
  paper's statement, for the record).

### R6/R7 as built — errata (2026-09-05, PRs #3658–#3673)

The chain above was built in `MoltResearch/Discrepancy/MajorArcAssembly.lean`,
`MoltResearch/Discrepancy/MajorArcBlockScale.lean`, and the Conjectures leaves
`TrackCStage5MajorArcA2.lean` (the Prop + `majorArc_block_bound_restricted`),
`TrackCStage5MajorArcMR.lean` (the wrapper) and `TrackCStage5MajorArcEDP.lean`
(`edp_of_sliceMeanSquareA2`, audit-pinned).  Three departures from the plan above:

1. **Classes before the freeze (R6-4/R6-5 order).** Freezing first gives dilated windows
   of length `ℓ/d₀`, one per divisor `d₀ ∣ q`; but the Prop chooses `levels` (= `𝒮`) as a
   function of the window length, so the classes would have seen different `𝒮`'s and the
   once-paid `𝒮ᶜ` removal would not be well defined.  As built: residue split
   (`sum_mul_exp_ratl_eq_sum_residues`, the arc phase riding along), gcd dilation
   (`sum_restricted_residue_mul_eq_gcd_dilate`, phase `e(m'·d₀δ)`), characters, and only
   then the freeze in the dilated variable at **one** window length `h₀`
   (`norm_twisted_filter_block_le_windows_add`, trimmed so every sub-block is a full window
   or empty).  Same cost `2πQh₀` per `n`.
2. **The Prop carries the `𝒮ᶜ` density and the level-prime bound.** §1.2's Prop had only
   primality of the levels; R7-3 cannot be closed against that (the levels depend on `h`
   and their masses are not visible to the wrapper).  `SliceMeanSquareA2` as defined
   quantifies `∀ εc > 0, ∀ B C, ∃ h₁ C₁ k, ∀ ε > 0, ∀ h ≥ h₁ with C₁/ε^k ≤ h, ∃ levels A₀`
   with: primes, primes `> C(log h)^B`, `𝒮ᶜ` log-density `≤ εc` on dyadic blocks above `A₀`,
   and the mean square at `s = 1`.  The `h`-threshold is polynomial in `1/ε` (the wrapper
   takes `ε' = ε/(128Q)`, `Q ≍ (log H)^B`); the density parameter `εc = ε/48` is fixed, so
   its threshold `h₁` may be anything (`H₀(ε) ≈ exp(exp(16/ε)·125)` of §9.3 lives there).
   The Prop is invoked at polylog constant `2^B·C`, so that `2^B C(log h₀)^B ≥ C(log H)^B`
   follows from `H ≤ h₀²`.
3. **Constants, and the block scale.** Block `(A, 2A]` exactly (the range is *covered* by
   dyadic blocks, `sum_Ioc_le_sum_dyadic_cover`; short partial blocks break the `∑1/n`
   comparison).  Good block: `6qH ≤ A`, `7q² ≤ A`, `⌈A₀⌉₊ + 1 ≤ ⌊A/q⌋`, and the A.2 input
   is demanded only on blocks ending below `3A`, fed for every twist from **one**
   hypothesis `NonPretentiousAt g (qA₀ + 26) (6A+1)` (`nonPretentiousAt_charMul_of_block`,
   Mertens cost `≤ 26` since `⌊A/q⌋² ≥ 6A+1`), itself obtained from the interface's
   `NonPretentiousAt g A ⌈x⌉₊` by going **up** to `8⌈x⌉₊` at strength `A/8`
   (`nonPretentiousAt_scale_up`; the top blocks' scale exceeds `x`) and down at cost
   `2log(1/θ) + 24` on the good blocks `log(6A+1) ≥ θ log(8⌈x⌉₊)`, `θ = ε/64`
   (`nonPretentiousAt_block_of_good`).  Per good block the coefficient is
   `16qε' + qh₀/H + 4πq²|δ|h₀ + 6εc ≤ (21/64)ε`; small blocks (`A < L₀ = ⌈Q(6H+7Q+A₀+2)⌉₊`)
   cost `≤ log(2L₀)`, bad blocks `≤ 2 + 15ε/64 + (ε/32)log w`; the interface's threshold
   is `A₀ := 8(QA₀^{A.2} + 50 + 2log(64/ε)) + exp((6log(2L₀) + 80)/ε)`.  R6-9/R7-7 (A.1 for
   the record) were not cut; §7.3 stands.

### Phase 0 as run — status (2026-09-05, Codex run 5, PRs #3675–#3676; report in `Problems/tao2015_phase0_vi9_report.md`)

Done: **VI-9a** (`band_energy_typicalS_le_of_schedule'`, honest `(4H/A)²` accounting), **VI-9b**
(`card_large_prime_poly_pow_le`), **VI-9c** (`ExceptionalCellCover`), **VI-9d**
(`TrackCStage5ExceptionalReCut`: no `T/P`), **VI-9e** (`ExceptionalHalaszTwist`: no `3+2πT`, smooth
mass `≤ exp(2E_P)`, nonuniform quotient costs), **VI-9f** mid/far split (`PretentiousBandSplit`, the
`t₁` minimizer, `pretentiousDistSq_archTwist_ge_mid`) with the far regime isolated as the cited
interface **`FarRegimeRepulsionAssumption`** (`Conjectures/…/Interfaces/FarRegimeRepulsion.lean`;
arXiv:1503.05121 App. A, proof of Prop A.3; no instance may be declared), **A2-IV-1**
(`LowBandTypicalS`), **A2-IV-2** (`SliceWeightConversion`).

Not done, with exact blockers: the **central `T₀` window** of VI-9f — wanted
`|F(1+it)| ≤ C(e^{−M/2}/(1+|t−t₁|) + (log A)^{−1/16})` uniformly for `|t−t₁| ≤ (log A)^{1/16}`,
free of `loglog A` factors; the tree's best shell is
`loglog x · x · √((eπ)²·10¹⁵·((e⁵(2+log x)e^{−A})² + 1))`, whose `+1` floor survives as `A → ∞`
and whose outer `loglog x` breaks the fixed-strength central budget (`rieszMean_log_le_closed` is
weaker still). This is a second genuine fit failure beyond the far-regime gap (§10) — the
Finding-C problem in its sharpest form. Consequently **VI-9g, A2-IV-3, A2-V and
`sliceMeanSquareA2 : SliceMeanSquareA2` were not attempted.** Next: a paper-first design of the
GHS central window at fixed strength (the `𝒯₀` leg of `[mrt]` A.3, `eq:T0claim`), then the
Erdős–Turán far-regime lemma; both are analytic-core units, not bookkeeping.

### The `𝒯₀` leg — paper-first design and the Finding-C fix (2026-09-05, T0-1…T0-4 on main)

**Where the `loglog` came from.** `tripleConvRC_survivors_balanced_shell_le` prices every one of
the `K₀ ≈ loglog x` prime blocks `p ∈ [x^{1−e^{1−k}}, x^{1−e^{−k}})` of §3's survivor set by the
*same* band-sup shell `x·√((e^π)²10¹⁵(b²+1)) + 2x·log 4`, `b = e⁵(2+log x)e^{−A}`. That is the
classical Halász–Montgomery `∫ dσ/σ` loss, and it is an artefact of the accounting: block `k` also
has the fit-free trivial bound `x·(16(log blockHi − log blockLo) + 16 log 4) ≤ 16(e−1)e^{−k}·x·log x
+ 48 log 2·x` (`norm_tripleConvRC_le''` + `log_blockHi_sub_log_blockLo_le`), geometric in `k`.
Pricing only `K₁ := min(K₀, ⌈A⌉)` blocks by the shell and the rest trivially
(`tripleConvRC_survivors_sharp_le`, new leaf `MoltResearch/Discrepancy/HalaszSharpSurvivors.lean`)
gives, after the same identity/head/tail/bridge assembly and the §3 window, the **sharp budget**

```
Ĥ⁺(A,z) = 35z + z(log(2log²z)+2) + 2(z+1)log 4 + 64z(12 loglog z + 18)
        + (A+1)·z·√((e^π)²10¹⁵)·e⁵(2+log z)·e^{−A}
        + loglog z·z·(√((e^π)²10¹⁵) + 2 log 4)
        + 16(e−1)·z·(e^{−A}·log z + e²·log 2)
        + (loglog z + 2)·z·48 log 2
```

(`halaszBudgetSharp`, `rieszMeanC_log_sharp_le`), i.e.

```
Ĥ⁺(A,z)/(z·log z) ≤ (A+1)·1.2·10¹¹·e^{−A} + 28·e^{−A} + 7.4·10⁸·loglog z/log z + 1400/log z
```

— **no `loglog z` against `e^{−A}`**; the shell's `+1` floor and the trivial tail sit in the
`loglog z/log z` group. The plain-sum wrapper `plain_sumC_le_halaszBudgetSharp`,
`halaszBudgetSharp_nonneg`, `halaszBudgetSharp_mono` are the exact mirrors of the shell's (the divided
form `plain_sumC_le_halaszBudgetSharp_div` is in `HalaszSharpWindow.lean`, T0-5). At a
fixed strength `A` the two-scale differencing at `log(X/x) = δ₀ ≍ √((A+1)e^{−A})` now yields
`‖∑_{n≤x} f‖/x ≲ √(A+1)·e^{−A/2} + o_x(1)` **uniformly in the scale** — the `(1+M)e^{−M}` shape of
GHS Cor. 1.2, obtained inside the existing §3 machinery. This removes the blocker recorded in the
Phase 0 report ("VI-9f central window").

**The window itself is `|t − t₁| < 6`, not `(log A)^{1/16}`.** `[mrt]` needs the wide window
because its `𝒯₁` repulsion is the GS Lemma 2.3 cosine argument, which requires
`|t − t₁| ≥ (log X)^{1/16}/2`, and then needs the shift lemma (GS Lemma 7.1, `le:renorm`) to buy
the `1/(1+|t−t₁|)` decay across the window, plus the Euler-product `≤ 1` trick for the `2^J`
inclusion–exclusion. The tree's mid-regime repulsion is the ζ-based
`pretentiousDistSq_archTwist_ge_mid`, valid already for `6 ≤ |t − t₁|`, with the exact fit
`ρ·loglog y ≤ ((1−3ρ)·loglog y − loglog(|t−t₁|+2) − 24)/3 − M` exposed. Whenever that fit fails
for `|t − t₁| ≤ (log y)^{20}` one has `M ≥ 0.27·loglog y − 9 ≥ ρ·loglog y − 9` outright, so
**every `t` with `6 ≤ |t − t₁|` (below the far regime) carries strength `≥ ρ·loglog y − 9`** and
the shell budget (with its `√(loglog)` factor) suffices there. On `|t − t₁| < 6` — a window of
measure `12` — one applies the sharp plain-sum bound pointwise at the interface's fixed strength
(`𝔻(g, n^{it}; ·)² ≥ A₀` for every `t` in the band, so `t₁` plays no role) and pays
`∫_{𝒯₀}|F|² ≤ 12·sup² ≲ (A₀+1)e^{−A₀}`. No shift lemma, no `(log A)^{1/16}` measure factor, and
since the tree's instantiation has a bounded number of levels (`J = 1` plus the fixed-`ε` 𝒰),
the `2^J` inclusion–exclusion costs a constant and the Euler-product trick is unnecessary.

**Erratum on VI-9e (recorded, not yet fixed).** `cheap_halasz_eps` fixes `W ≥ 8B + 22 ≥ 22`, so
`cheapTwistedDirichletCost eps W D a b = 2b(eps + e^{W loglog b + W − D/2})/(a+1)` is a **loss** of
`(log b)^{22}` against `e^{−D/2}` — vacuous at the fixed strength of `𝒯₀` *and* at the
`ρ·loglog` strength of `𝒯₁` (`ρ/2 ≈ 0.03 ≪ 22`). VI-9e's `norm_typicalS_quot_block_poly_le_recut`
therefore cannot be the Halász input of either leg; its accounting seams (no `3+2πT`, nonuniform
Ramaré) are right, but the block bound must come from the GHS budgets: the sharp one on `𝒯₀`, the
shell one on `𝒯₁`. This is the re-plumb T0-6 below.

**Ladder (replaces the "central `T₀` window" blocker):**

- **T0-1…T0-4** (`HalaszSharpSurvivors.lean`, this PR): the sharp survivor split, the §3 assembly
  at a free split index, the `b`-instantiation, the windowed `halaszBudgetSharp` and its wrappers.
- **T0-5** (`HalaszSharpWindow.lean`, on main): `prefix_le_sharpPartialBudget` — for `10¹⁶ ≤ a ≤ u ≤ B'`
  and non-pretentiousness at strength `A` on `[a, 3B']`, `‖∑_{n≤u} f‖ ≤ sharpPartialBudget A δ₀ a B' :=
  2Ĥ⁺(A,3B')/(δ₀·log a) + (e·B'·δ₀+1)` (auxiliary scale `X_u = ⌈u·e^{δ₀}⌉ ≤ 3B'`; **both denominators kept
  as `log a`** — the shell plumbing `sup_partial_le_halaszBudgetShell` prices them by `36`, a `log B'/36`
  loss that this mirror does not repeat); and the **sharp twisted Dirichlet block**
  `sharp_halasz_twisted_dirichlet_block`: for `|2πt| ≤ (D/2)·a`, strength `D ≥ 2` on `[a, 3b]`,
  `‖∑_{(a,b]} g(n)n⁻¹e(−t log n)‖ ≤ sharpTwistedDirichletCost (D/2) δ₀ a b := 2·sharpPartialBudget (D/2) δ₀ a b/(a+1)`
  via `nonPretentiousAt_archTwist` + `norm_sum_div_le_of_partial` — the shape of
  `cheap_halasz_twisted_dirichlet_block` with the sharp budget in place of `W`. Numerics for `b ≤ 3a`,
  `a ≥ 10¹⁶`: `cost ≤ (b/a)·(13E/δ₀ + 5.5δ₀) + 2/a` with `E = Ĥ⁺(D/2,3b)/(3b·log 3b)`, so at
  `δ₀ = 1.5√E` the cost is `≲ 17(b/a)√E ≈ 6·10⁶·(b/a)·√(D/2+1)·e^{−D/4} + o(1)`.
- **T0-6** (`HalaszSharpTwist.lean`, on main) — **the twist-range finding and the windowed chain.**
  `NonPretentiousAt f A x` bundles the distance floor with the frequency range `|s| ≤ A·x` centred at
  `0`, so for the twisted `g(n)n^{−iξ}` it holds at scale `x` only when `|ξ| ≤ (A−A')·x`
  (`nonPretentiousAt_archTwist`). The exceptional cells apply the twisted bound at quotient scales
  `x = A_scale/(q·n₁)` and frequencies `|t| ≤ T ≍ A_scale/H`: `2π|t| ≫ x` as soon as `q·n₁ ≫ H`, and
  with `q ≥ P_𝒰 ≈ (log A_scale)^{3/4} → ∞` at fixed `H` **no quotient is in range**. So every twisted
  block bound stated with `|2πt| ≤ (D/2)·a` — VI-9e's `cheap_halasz_twisted_dirichlet_block`, T0-5's
  `sharp_halasz_twisted_dirichlet_block` — is inapplicable to the exceptional leg (and VI-6's untwisted
  route paid the Abel factor `3+2πT ≍ A_scale/H` instead). `[mrt]` has no such constraint: `M(f;X)` is
  the infimum over all `|t| ≤ X`, and Halász is applied at scale `X/p` with twists up to `X`. The
  capstone itself needs only the *window* `HalaszWindowAt f A x := ∀ t, |t| ≤ halaszM x + 1 →
  A ≤ 𝔻(f, n^{2πit}; x)²` (`norm_phase_euler_prod_le_of_nonPretentious` uses one level-one twist per
  frequency). Built: `norm_phase_euler_prod_le_of_distSq`, `norm_smoothPhaseSum_le_of_distSq`,
  `rieszMeanC_log_le_sharp_halasz_of_window`, `rieszMeanC_log_sharp_le_window` (via the extracted
  pricing lemma `sharp_survivor_price`), `plain_sumC_le_halaszBudgetSharp_window(_div)`,
  `prefix_le_sharpPartialBudget_window`, the **bridge** `halaszWindowAt_archTwist_of_nonPretentiousAt`
  (from `NonPretentiousAt g A N` at the top scale and `|ξ| + 2π(halaszM u + 1) ≤ A·N`, the twisted
  window at any `4 ≤ u ≤ N` at strength `A − 2(loglog N − loglog u + 12)`, by
  `pretentiousDistSq_le_add_mass` + `mertens_mass_diff_le`; `≤ 2 log 2 + 24` lost for `u ≥ √N`), and
  `sharp_halasz_twisted_dirichlet_block_window` (cost `sharpTwistedDirichletCost D δ₀ a b`, no
  frequency condition). The consumer's non-pretentiousness lives at the top scale `N = 2A_scale+1`
  with range `A₀·N ≫ 2πT`, exactly what the bridge needs.
- **T0-6b** (`ExceptionalHalaszSharp.lean`, on main) the recut at the windowed sharp cost:
  `halaszWindowAt_levelFreeTwist_archTwist` (Ramaré robustness for the window: `g·n^{−iξ}` at `2D`
  gives every `levelFreeTwist g S · n^{−iξ}` at `D`), `sharpQuotientCost` (long: the windowed sharp
  block at strength `D`; short: harmonic mass), `norm_filter_levelFreeTwist_quotient_le_sharp`,
  `sharpRamareCost`, `norm_levelFreeTwist_ramare_poly_le_sharp`, `cellHalaszSharpBound`,
  `norm_typicalS_quot_block_poly_le_sharp` — VI-9e's chain with the window hypothesis demanded
  **only on long quotients** `(A/q)/n₁ ≥ 10¹⁶` and no frequency condition at all (VI-9e's recut
  demands `|2πt| ≤ (D/2)·((A/q)/n₁)` for *every* `P`-smooth `n₁ ≤ B/q`, which forces `t = 0` whenever
  `B/q > A/q` — a second reason it cannot be consumed). The consumer supplies the window per long
  quotient from the top-scale `NonPretentiousAt` via `halaszWindowAt_archTwist_of_nonPretentiousAt`.
- **T0-6c** (`HalaszSharpEps.lean`, on main) the `ε`-form: `Ĥ⁺(A,z) ≤ z·(log z·e^{−A}((A+1)Q + 16(e−1)) +
  c₂ loglog z + c₃)` for `z ≥ e³⁶`; on `10¹⁶ ≤ a ≤ b ≤ 3a`,
  `sharpTwistedDirichletCost D δ₀ a b ≤ (b/(a+1))(13e^{−D}((D+1)Q+16(e−1))/δ₀ + 12(c₂ loglog 9a + c₃)/(δ₀ log a)
  + 2eδ₀) + 2/(a+1)`; the two thresholds; and `∀ ε, ∃ D₀ x₀, ∀ D ≥ D₀, ∀ x₀ ≤ a ≤ b ≤ 3a,
  sharpTwistedDirichletCost D (ε/(8e)) a b ≤ ε·b/(a+1)` — the fixed-strength saving, uniform in the scale.
**The `t₁`-split is unnecessary at fixed `ε` (2026-09-05, after T0-6c).** §6 recorded that the
fixed-`ε` S6 needs only a saving `ε⁶` from the exceptional leg's Halász input, and that the
`𝒯₀/𝒯₁` split was forced solely by the `loglog u` factor of the shell budget at a fixed strength.
With `halaszBudgetSharp` that factor is gone: `sharpTwistedDirichletCost_le_eps` gives, for every
`ε`, a fixed strength `D₀(ε)` and scale `x₀(ε)` with the block cost `≤ ε·b/(a+1)` **uniformly in the
scale**, and the bridge `halaszWindowAt_archTwist_of_nonPretentiousAt` supplies the window at every
frequency of the band from the interface's single top-scale `NonPretentiousAt g A₀ (2A+1)` (range
`A₀·(2A+1) ≫ 2πT`). So the exceptional-cell pointwise bound holds at the fixed strength `A₀` for
**all** `|t| ≤ T`: no minimiser `t₁`, no `𝒯₁` repulsion, and `FarRegimeRepulsionAssumption` is **not
needed** for the A.2 discharge (it stays in the tree as the cited interface of the `[mrt]`-shaped
`M(f;X)` statement, unused by the ε-form). The `[mrt]` split exists because their Prop is stated with
the sharp `e^{−M}` for *all* `M`; the tree's target is the fixed-strength `ε`-form.

What remains for the exceptional leg is bookkeeping, not analysis:

- **T0-7a** the long/short cutoff of `ExceptionalHalaszSharp` as a parameter `x₀ ≥ 10¹⁶` (the bridge
  loses `2(loglog N − loglog u + 12)`, bounded only for quotient scales `u ≥ N^{c}`; so long
  quotients are `(A/q)/n₁ ≥ N^{c}` and the rest are short);
- **T0-7b** (`SmoothRankinTail.lean`, on main: `sum_pSmooth_rpow_le_prod`, `pSmooth_harmonic_tail_le`,
  `prod_inv_one_sub_le_exp`, `sharpRamareCost_le_split`, `sharpRamareCost_le_eps`) the `P`-smooth Rankin tail: `∑_{n₁ P-smooth, n₁ > y} 1/n₁ ≤ y^{−σ}∏_{p∈P}(1−p^{σ−1})^{−1}`
  (the box-product technique of `pSmoothHarmonicMass_le_exp_primeMass` with the weight
  `n^{σ−1}`), so that the short quotients' harmonic charges beyond `y = N^{c}/q` are negligible, and
  the `ε`-form of `sharpRamareCost` / `cellHalaszSharpBound`;
- **T0-7c** (`Conjectures/…/TrackCStage5ExceptionalSharp.lean`, on main): `halaszM_mono`,
  `halaszWindowAt_twist_of_top` (from the top-scale `NonPretentiousAt g A₀ N` with
  `2πT + 2π(halaszM N + 1) ≤ A₀·N` and `2D ≤ A₀ − 2(loglog N − loglog x₀ + 12)`: the window of
  `g·n^{−2πit}` at strength `2D` at every scale `u ∈ [x₀, N]`, for **every** `|t| ≤ T`),
  `norm_cellBlock_poly_le_cellHalaszSharpBound(_of_top)` (the capstone's `hδ` at the sharp cost),
  `cellHalaszSharpBound_pos` (its `hδ0`), `cellHalaszSharpBound_le_explicit` (`≤ 2^{#rest}(2ε·e^{2E_P} +
  (log Bq + 1)(Aq/x₀)^{−s}·exp(2∑_{p∈P} p^{−(1−s)}))` at `D ≥ D₀(ε)`, `x₀ ≥ x₀(ε)`). What remains is
  **VI-9g**: the fixed-`ε` S6 schedule with this `δ` — `hfitUCell` from `exceptionalCell_fit_of_schedule`
  with `Delta := 2^{J}(2ε e^{2E_𝒰} + tail)`, the parameters `log Q_𝒰/log P_𝒰 = C/ε³`, `N_𝒰 ≍ C/ε³`,
  `x₀ = N^{1/2}`, `s = 1/log Q_𝒰`, `A₀ ≥ 2D₀(ε) + 2(log 2 + 12)` — then A2-IV-3 → A2-V → `sliceMeanSquareA2`.

(Superseded T0-7 entry, kept for the record: **T0-7** (Conjectures) the `𝒯₀/𝒯₁` assembly of VI-9f: `𝒯₀ := {|t−t₁| < 6} ∩ band` at the
  sharp cost, `𝒯₁` at strength `ρ·loglog − 9` from `pretentiousDistSq_archTwist_ge_of_mid_or_far`
  or from `M` itself, far regime via `FarRegimeRepulsionAssumption`; then VI-9g.)

### Phase VI-9g as run — status (2026-09-05, Codex run 6, PR #3686; report in `Problems/tao2015_vi9g_report.md`)

Done: **VI-9g-1** (`TrackCStage5BandEnergyExceptionalReCut.lean`: `setIntegral_band_energy_exceptional_max_le_recut`,
`_le_budget_recut`, `band_energy_le_budget_of_exceptional_family_recut`,
`card_cellsMeeting_exceptional_le_highMomentCost`, **`band_energy_typicalS_le_of_cellUniform_fit_recut`** —
the capstone with `Aint` on the **covered** cells `Kcov = cellsMeetingSet (bandCells K₂) (bandPartOn … J)`
and the prime term `Γ = primeHighMomentCountCost·e^{−log P/(log 2T)^{3/4}}(log 2T)²`; no `#bandCells`, no
`T/P` — Finding B rows 1–2 closed), **A2-IV-1′** (`LowBandTypicalSSharp.lean`:
`norm_typicalS_dirichlet_poly_le_low_band_sharp`, `integral_…_le_low_band_sharp`,
`integral_norm_typicalS_dirichlet_poly_sq_le_low_band_eps` — the low band at the sharp cost, `2^{#levels}·η·b/(a+1)`,
no `W`).

**Brief erratum (found by the run).** VI-9g-2 presupposed the `√`-optimised fit
`exceptionalCell_fit_of_schedule` (`2δ²Bpri + 4δ√(Aint·Bpri·Γ)`), which was derived for `Γ` independent of the
threshold `V`. With the high-moment count `Γ(V) ∝ V^{−2ℓ}` it is **not** an upper bound (report: `ℓ = 2, V = 1/2,
Aint = Bpri = δ = 1, C·saving = 1` gives exact cost `34.5` against the advertised `18`). The recut capstone's
fit is the exact fixed-threshold one, `2(V₀²·Aint + δ²·Bpri(1+Γ(V₀))) ≤ κ·budget`.

**Repair (decision).** Retain `exceptionalSplitThreshold A = (log A)^{−100}` (VI-9d's choice) and fit the two
terms separately. Numerology: `∑‖cellBlockCoeff‖²/n² ≤ ∑_{n∈(A/q,B/q]} 1/n² ≲ Δq/A²`, so
`V₀²·Aint ≲ (log A)^{−200}·64(log 2T + 1)·(ρ + #Kcov·√T·q/A)` — negligible against `c₃ε²ρ/8` once
`log A ≫ 1` and `#Kcov ≤ ∑_r 2·primeHighMomentCountCost(…)` is polylog (level `J−1` anchors);
`δ²·Bpri(1+Γ)` needs `Γ(V₀) ≲ 1`, i.e. `e^{−log P_𝒰/(log 2T)^{3/4}} ≤ (log A)^{−200ℓ−2}·(…)`: with
`P_𝒰 = exp((log A)^{49/50})` (MR's choice) the saving `exp(−(log A)^{49/50−3/4})` kills every polylog, and the
fixed-`ε` S6 becomes `Q_𝒰 = exp((C/ε³)(log A)^{49/50})` — admissible (`N_𝒰·Q_𝒰 ≤ A`) for `A ≥ A₀(ε)`. Then
`δ ≲ ε⁶`-type from `cellHalaszSharpBound_le_explicit` and `Bpri ≲ 64/(N_𝒰 log² P_𝒰)` fit
`2δ²Bpri·2 ≤ κ_U·budget`. This is VI-9g-2′/3′: a schedule theorem on `band_energy_typicalS_le_of_cellUniform_fit_recut`
with the sharp `δ` and these two explicit fits; then A2-IV-3, A2-V.

### The slice quantifier of `SliceMeanSquareA2` is over-strong (R8) — found by Codex run 7 (2026-09-05, PR #3688)

**Phase VI-9g-2 as run.** Codex run 7 shipped **VI-9g-2′** (`TrackCStage5InnerBandScheduleSharp.lean`:
`band_energy_typicalS_le_of_schedule_sharp` on the recut capstone, exceptional block `δ_v = cellHalaszSharpBound`,
`V₀ = exceptionalSplitThreshold A`, the two half-budget fits `hfitInt`/`hfitPri`, the covered-cell bound
`sharpExceptionalCoverBound`, and `nonPretentiousAt_scale_up_of_norm_le_one` — the Prop's `g` is only 1-bounded,
the old scale-up wrapper needed `Unimodular`) and **VI-9g-3′** (`…SharpNumerology.lean`): a machine-checked
**obstruction**. `cellHalaszSharpBound ≥ ε'/8` on a long quotient (the two-scale differencing's edge term
`e·b·δ₀` at `δ₀ = ε'/(8e)` — a *fixed* saving is the design), so `hfitPri` with a nonempty cell forces
`A ≤ κ·c₃·ε²·Δ·Pc·log Pc/(32ε'²)`, i.e. `Δ/A ≳ ε'²/(ε²·Pc log Pc)`: **the budget `bandBudget c₃ ε (Δ/A) ∝ Δ/A` vanishes
as `A → ∞` at fixed slice length `Δ`.** The run stopped per the stop rule; A2-IV-3, A2-V not entered.

**Diagnosis.** The slice length is the Prop's `J`: `SliceMeanSquareA2` demands, for every `A ≥ A₀` and **every
`J ≤ A`**, `∑_{n∈(A,A+J]} ‖∑_{(n,n+h]∩𝒮} g‖²/n ≤ ε²h²∑_{(A,A+J]} 1/n`. At `J = 1` that is a *pointwise* bound
`‖∑_{(n,n+h]∩𝒮} g‖ ≤ εh` at every single `n ≥ A₀` — a uniform short-interval statement, which is false in
general (in the random model the largest of `X` window sums of length `h` is `≍ √(h log X)`, unbounded in `X` for
fixed `h`, hence `> εh` eventually). `[mrt]` A.2 is the mean square over a **dyadic** block, `J = A`. The
over-strong quantifier entered with R6-8 (#3667). Since the R6/R7 chain is *conditional* on the Prop, the
theorems are correct, but `edp_of_sliceMeanSquareA2` is conditional on a hypothesis stronger than `[mrt]` proves
and very likely false — the discharge campaign would have hit this wall at A2-IV-3 in any case; the run's
obstruction is its exact numerical form.

**What the chain actually uses.** The only instantiation of the mean-square clause is R6-5
(`logavg_le_of_meanSquare_dyadic`) inside R6-6c (`sum_div_comp_div_le_of_meanSquare`): the reindexed block
`(a, b]`, `a = ⌊(A+c)/d⌋ − 1`, `b = ⌊(2A+c)/d⌋`, with `4d ≤ A`, `3c ≤ A`. Arithmetic: `b − a ≥ A/d ≥ (3/4)(a+1)`
and `b ≤ 2a + 4`. R6-5 splits `(a, b]` into `(a, min(b,2a)]` — a block with `J ≥ (3/4)a ≥ a/2` — and the leftover
`(2a, b]` of **at most 4 points**, which R6-5 currently also feeds to the Prop (this is the pointwise use).

**Repair (R8, decision).**
1. Weaken the Prop's clause to `∀ J, A/2 ≤ J → J ≤ A → …` (the honest dyadic-type average; `[mrt]`'s `J = A` is
   the special case). Its consumers in `SliceA2`/VI-9g then have `Δ/A ≥ 1/2`, so `bandBudget ≥ c₃ε²/16` is
   **fixed** and `hfitPri` closes (`ε'² ≲ κc₃ε² log Pc/64`) — the run's obstruction disappears.
2. R6-5′: from the weakened clause plus the trivial bound `W ≤ h` (`norm_filter_block_le_card`), on `(a, b]` with
   `3a ≤ 2b`, `b ≤ 2a + 4`, `b ≤ N`: `∑_{(a,b]} W/n ≤ εh·∑_{(a,b]} 1/n + 4h/(2a+1)` (main block by the clause and
   Cauchy–Schwarz as now; leftover trivially).
3. R6-6c′: the harmonic mass of the reindexed block is `≤ 2` (not `3`: `b ≤ 2a + 4`), so
   `(4/3)(2εh + 4h/(2a+1)) ≤ (8/3)εh + (8/3)h/a ≤ 4εh` once `2 ≤ ε·a` — the conclusion `≤ 4(εh)` is **unchanged**;
   new hypothesis `2 ≤ ε·A₁` (threaded up: R6-6d, R6-8 `majorArc_block_bound_restricted`, R7-C1/C2/C3/6 — the
   wrapper's `A₀_int` is `≥ exp(…)`, so it is trivially available), plus the floor facts `3a ≤ 2b`,
   `b ≤ 2a+4` from `Nat.add_div`/`Nat.add_div_le_add_div`.
4. The Prop's shape changes in `TrackCStage5MajorArcA2.lean` (`def`, R6-8's `hA2`), `MajorArcMR.lean` (:54, :136,
   :376), and every `hA2 : ∀ A' J, A₁ ≤ A' → J ≤ A' → …` in `MajorArcAssembly.lean` (:652, :1031, :1106) gains
   `A'/2 ≤ J →`. `MajorArcEDP.lean` and the audit pins are unchanged in shape (they name the Prop). Re-run the audit.
5. VI-9g-3′ then proceeds with `Δ ≥ A/2`; the obstruction file stays as the record (its theorems are true).

### R8 as run — status (2026-09-05, Codex run 8, PR #3690; report in `Problems/tao2015_r8_report.md`)

Done, exactly per the R8 brief: **R8-1** the Prop's clause is `∀ J, A / 2 ≤ J → J ≤ A → …`; **R8-2**
`logavg_le_of_meanSquare_dyadic` (main block `(a, min b (2a)]` by Cauchy–Schwarz, leftover `≤ 4` points priced by
`W ≤ h`: `+ 4h/(2a+1)`); **R8-3** `sum_div_comp_div_le_of_meanSquare` (harmonic mass `≤ 2`, `2 ≤ ε·A₁`, conclusion
`4(εh)` unchanged); **R8-4** `sum_restricted_window_logavg_le_of_meanSquare`; **R8-5** `majorArc_block_bound_restricted`
(`hε'A₀ : 2 ≤ ε'·A₀`); **R8-6** R7 (`good_block_total_le`, `block_total_le_trichotomy`, `exists_wrapper_params` now
exports `2 ≤ (ε/(128Q))·A₀` by taking `max A₀ (256Q/ε)` and transporting both clauses — the brief's "add `256Q/ε`
to the wrapper's `A₀`" was not enough, since the Prop chooses its own threshold); **R8-7** the docstring note in
`…SharpNumerology.lean`: with `J ≥ A/2` the forced condition is the fixed `ε'² ≤ κc₃ε²·Pc·log Pc/64`.
`edp_of_sliceMeanSquareA2` and the audit pins compile with identical axiom sets. **The conditional EDP is now
conditional on the honest `[mrt]`-shaped Prop.** Next: VI-9g-3′ with `Δ/A ≥ 1/2` (the fixed prime fit), then
A2-IV-3 → A2-V → `sliceMeanSquareA2`.

### Two calibration errors of the phase-3 brief (runs 9a/9b, 2026-09-05; report in `Problems/tao2015_vi9g_phase3_report.md`)

Codex run 9a stopped on a constant (`/16 → /24`: the ℕ-floor guard `A / 2 ≤ Δ` gives `Δ/A ≥ 1/3`, not `1/2`; the
half-budget fit now runs at `/48`), run 9b on a genuine unbounded obstruction, and its report re-raised a quantifier
conflict first flagged by run 7. Both are errors of the brief's parameters, not of the design; `…SharpFit.lean`
(phase-3a PR) keeps the `ℓ = 1` branch as a record (`time_scale_bound_of_fixed_split_moment_one_Gamma_le_one`).

**(i) The moment order.** The brief prescribed `ℓ := 1` in `primeHighMomentCountCost P ℓ Y T V λ =
e^π((T+1)/P^ℓ + 2·2^ℓ)(ℓ!)²(∑_{p∈Y}1/p)^ℓ((1+λ) + (2π log(2P)^ℓ)²/λ)/V^{2ℓ}` and claimed the count polylogarithmic.
At `ℓ = 1` the `(T+1)/P` summand survives, so `Γ ≤ 1` on a nonempty cell forces
`e^π(T+1)e^{−log P/(log 2T)^{3/4}}(log 2T)² ≤ 2P²/(log A)^{200}`, i.e. `log A − 2N_𝒰(log A)^{49/50} − (log A)^{0.23}
+ 202 loglog A → ∞`: no `A₀` helps. The count exists precisely so that `ℓ` can grow: `[MR]`'s `le:Rupest`
calibration is `ℓ := ⌈log(2T)/log Pc⌉ + 1`, so `Pc^ℓ ≥ 2T` and `(T+1)/Pc^ℓ ≤ 1`. With `Pc ≥ P_𝒰 =
exp((log A)^{49/50})`, `T ≤ A` this is `ℓ ≍ (log A)^{1/50}`, every `ℓ`-factor (`2^{ℓ+1}`, `(ℓ!)²`, `(3/2)^ℓ`,
`(2πℓ log 2Pc)²`, `V₀^{−2ℓ} = (log A)^{200ℓ}`) has logarithm `O((log A)^{1/50}·loglog A)`, and the saving
`e^{−log Pc/(log 2T)^{3/4}}` has exponent `≥ (log A)^{49/50 − 3/4} = (log A)^{0.23}`. So `Γ_v ≤ 1` holds for
`A ≥ A₀` — as an *eventual* inequality (`C(log A)^{1/50} loglog A ≤ (log A)^{0.23}`; the crossover is
astronomically late, `log A ≳ 10²⁰`, which is irrelevant for a `∀ε ∃A₀` Prop). The same `ℓ` serves the level-`J−1`
cover anchors of `sharpExceptionalCoverBound` (their `V = e^{−αr/(2N)}` is a fixed constant, `V^{−2ℓ} = e^{O(ℓ)}`).

**(ii) The level status of `𝒰`.** §7.2 above and the brief make the exceptional block `Pu = 𝒰(A)` a **level of `𝒮`**
(`innerBandLevels Pl Pu J = … ++ [Pu]`) and pay its complement in the Prop's density clause. But `P_𝒰(A), Q_𝒰(A)`
depend on the block scale (`log P_𝒰 ≥ C(log T)^{3/4}` is what buys the Vinogradov saving at `T ≍ A`), while
`SliceMeanSquareA2` fixes `levels` before `∀ A ≥ A₀`; a fixed exceptional level has no saving as `T → ∞`. The source
settles it: `[mrt]` A.2's `𝒮` depends on the scale only through the number `J(X₀)` of levels from one fixed
sequence, and the Vinogradov interval is `[MR]` §8.3's **auxiliary** `[P, Q]`, `P = exp((log X)^{1−1/48})`, which is
not a level — the integers without a prime factor in `[P, Q]` are paid by a sift term `≍ log P/log Q` *inside* the
mean-square bound (the origin of `(log X)^{−1/50}`; §5 "On S6 at fixed ε" already carries it as `ε³/C`; §7.2 misrouted
it). Repair, with **no change to the Prop or to R6/R7**: the Prop's `levels` are the ordinary levels only
(`J = 1`: `[P₁, Q₁]`, a function of `(h, ε)`); in A2-IV-3 split each window sum over `𝒮` into the part over
`𝒮'(A) := typicalS … (innerBandLevels Pl (Pu A) J)` — bounded by the existing per-scale band machinery at accuracy
`ε/2` (`slice_energy_le_of_bands` is generic in the 1-bounded coefficients) — and the sifted part, which is elementary:
`‖∑_{(n,n+h]∩¬Pu} g‖² ≤ h·#((n,n+h]∩¬Pu)`, swapping the sums gives `≤ 2h·∑_{m∈(A,A+J+h], ¬Pu} 1/m` for `2h ≤ A`, and
`window_typicalS_complement_le … [Pu]` prices that by `(1/E_𝒰 + O_A(1/A))·∑1/m`, `E_𝒰 = ∑_{p∈Pu}1/p ≈ log N_𝒰`. The
sifted slice energy is `≤ 4h²(1/E_𝒰 + o(1))∑_{(A,A+J]}1/n ≤ (ε²/4)h²∑1/n` once `E_𝒰 ≥ 32/ε²`, so `N_𝒰 :=
⌈exp(64/ε²)⌉₊` replaces `⌈C/ε³⌉₊` (only fixed constants move: `e^{2E_𝒰}` in `ε'`, the prime-fit prefactor `≍ N_𝒰³`,
`D₀(ε')`, `A₀`). The density clause of the Prop then involves level one only (`E₁ ≥ 8/εc`, the `h₁(εc)` threshold).
Run 9d (brief = phase-3 brief + resume notes 2–3) executes both repairs, then A2-IV-3 → A2-V → `sliceMeanSquareA2`.

### Finding E — the exceptional cover forces the `[MR]` ladder and a scale-dependent level list (Codex run 9d, 2026-09-05)

Run 9d (`…SharpFit.lean`: `sharpExceptionalCoverBound_fixed_anchor_lower`, `schedule_hfitInt_forces_fixed_anchor_term`,
`exists_const_mul_log_pow_le_sqrt`; report in `Problems/tao2015_vi9g_phase3_report.md`): `sharpExceptionalCoverBound`
counts the cells of the exceptional part through the anchors of the **last ordinary level** (`firstPrevLargePart`,
`le:Rupest` at level `J−1`), and for a nonempty anchored cell at a *fixed* prime scale `P` the count is
`≥ e^π(T+1)/(2P)^{4P}` for **every** moment order — a fixed Dirichlet polynomial is large on a positive proportion of
`[−T, T]`. With §7.2's "`J = 1` + `𝒰`" the anchor level is `[P₁, Q₁] ⊂ [1, h]`, so `KcovBound ≍ T` and `hfitInt`'s
term `V₀²·KcovBound·√T·q_v/A ≍ √A/(log A)^{200}`. This is `[MR]` step 2 (`|𝒯| ≪ T^{1/2−η}X^{o(1)}`) attempted at the
wrong level. The count works at an anchor level of height `P_{J−1} ≥ (log T)^{40}`: with `ℓ_r = ⌈log 2T/log p_r⌉ + 1`
the `(T+1)/p_r^{ℓ}` term is `≤ 1`, `(ℓ!)² ≤ T^{2·loglog 2T/log P_{J−1}} ≤ T^{1/20}`, and the per-cell threshold
`e^{−α r/(2N)} = p_r^{−α_{J−1}}` gives `V^{−2ℓ} ≈ (2T·p_r)^{2α_{J−1}}`; hence `KcovBound ≤ T^{2α_{J−1}+0.06+o(1)} ≤ T^{0.46}`
(`α_j = scheduleAlpha (1/20) (j+1) < 1/5`) and `hfitInt`'s term is `A^{−0.04+o(1)}`. Three consequences.

1. **The level list must depend on the scale.** An anchor at height `(log A)^{40}` cannot belong to a `levels` fixed
   before `∀ A`. `[mrt]` A.2 has exactly this: `𝒮 = 𝒮(X₀)`, `√X ≤ X₀ ≤ X` — one level list serves all scales in
   `[X₀, X₀²]`, the level *sequence* is fixed and only the number `J(X₀)` of levels grows. This is **R9** (below). It also
   retires the sift device of the phase-3 amendments: `𝒰(A₁)` with `P_𝒰(A₁) = exp((log A₁)^{49/50})` is again a level of
   `𝒮(A₁)` (its saving at `T ≤ 2A₁²+1` is `≥ exp(−(log A₁)^{49/50}/(log(4A₁²+2))^{3/4}) = exp(−c(log A₁)^{0.23})`), and every
   level's complement is paid by TK in the Prop's density clause.
2. **The ladder is needed; one jump does not work.** The later-level moment trick borrows `ℓ = ⌈log(p_v T/A)/log p_r⌉`
   copies of the previous large cell polynomial and pays `(ℓ!)² ≤ p_v^{2 log L_j/log P_{j−1}}`, `L_j := log Q_j/log P_{j−1}`,
   against the current cell's smallness `p_v^{−2α_j}` and the previous cell's largeness `p_r^{2α_{j−1}ℓ} ≈ (p_v T/A)^{2α_{j−1}}p_r^{2α_{j−1}}`;
   the net per-cell factor is `p_v^{−2Δα_j + 2 log L_j/log P_{j−1}}·p_r^{2α_{j−1}}·(T/A)^{2α_{j−1}}`, `Δα_j = α_j − α_{j−1} = 1/(40j(j+1))`,
   so the level below must satisfy `P_{j−1} ≥ L_j^{2/Δα_j}` — `[MR]`'s "not too far" `loglog Q_j ≤ (η/4j²) log P_{j−1}`. A
   fixed level 0 below an anchor at `(log A)^{40}` has `L ≈ 40 loglog A/log P₀ → ∞`. The ladder: a **fixed** sequence
   `P_j = Q_{j−1}^{40j²}` (not too close: the summed loss `Q_{j−1}^{2α_{j−1}}` against `P_j^{−Δα_j}` is `Q_{j−1}^{0.4 − j/(j+1)} ≤ Q_{j−1}^{−0.1}`),
   `log Q_j = ratio_j·log P_j` with `ratio_j = e^{2^{j+1}/εc}` (TK density `∑_{j≥1} 1/E_j ≤ εc/2`, `E_j = log ratio_j`), which
   satisfies `P_{j−1} ≥ L_j^{2/Δα_j}` (`L_j = 40j²·ratio_j·ratio_{j−1}`, a condition `log P_{j−1} ≥ 80j(j+1)·log(40j² ratio_j ratio_{j−1})`,
   linear in `2^j/εc` while `log P_{j−1}` is exponential in it) once `P₀` is large; `J(A₁) := min{j : P_j ≥ (log A₁)^{40}} + 1`,
   `≍ √logloglog A₁`. All per-level conditions are independent of `A` (only `T/A ≍ γB'/(2πh)` enters).
3. **The later-level wrapper must be per cell in both indices.** `innerBand_later_level_main` and the nucleus
   `band_energy_later_main_le_budget` take one `(A', Δ', ℓ)` for all current cells `v` and lower-bound the previous
   threshold by `Qprev^{−β}` (its M-3 step), so their fit loses `(Q_j/h)^{2β·ratio_{j−1}}` against `P_j^{−2α_j}` — satisfiable
   only for `ratio ≈ 1`, i.e. never for a level that sifts. The per-`(r, v)` form (`A'_v ≍ A/p_v`, `ℓ_{r,v}`, threshold
   `e^{−βr/(2N)}`, which `hlargeCell` already supplies) is the nucleus lemma with `large := e^{−βr/(2N)}` (no M-3) applied
   cell by cell, plus Cauchy–Schwarz over `v` in the wrapper: `∫‖∑_v Q_vR_v‖² ≤ #cells·∑_v ∫‖Q_vR_v‖²`.

**What stands.** Level 0's leg (`hscheduleT0/P0` and the S-cal numerics), the recut capstone, the sharp exceptional
legs at the `[MR]` moment order, R6/R7 up to R9's re-thread, A2-IV-0/1′/2. **Withdrawn:** §7.2's "`J = 1` suffices" and
the phase-3 amendments' sift device (`N_𝒰 = ⌈exp(64/ε²)⌉₊`); `N_𝒰 := ⌈exp(4/εc)⌉₊` (TK) is enough once `𝒰` is a level.
**Numerology of level 0 under R9 (to be re-verified):** `Q₀ ≤ (c ε² h)^{1/(1−2α₀)}` from `hscheduleT0` (`T/A ≍ 1/h`),
`P₀ ≥ (N₀²E₀/(cε²))^{1/(2α₀)}` from `hscheduleP0`, `log Q₀ ≥ e^{2/εc} log P₀` for the density clause, `P₀ > C(log h)^B`;
together `h ≥ (C'/(εc ε²))^{6e^{2/εc}}·(log h)^{…}` — polynomial in `1/ε` with `k = k(εc)`, as the Prop allows.

### Phase 4 — the ladder (R9, L1–L3, A2-IV-3′, A2-V′)

- **R9 — the `[mrt]` `X₀`-shape of the Prop** (`Problems/tao2015_r9_brief.md`): `SliceMeanSquareA2`'s last block becomes
  `∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A₁ : ℕ, A₀ ≤ A₁ → ∃ levels, (primes) ∧ (C(log h)^B < p) ∧ (∀ A, A₁ ≤ A → A ≤ A₁^2 → density on (A, 2A])
  ∧ (∀ A, A₁ ≤ A → A ≤ A₁^2 → ∀ g …, NonPretentiousAt g A₀ (2A+1) → ∀ J, A/2 ≤ J → J ≤ A → mean square)`. R6-8 keeps its
  shape (it takes `levels` and the clauses); R7's `exists_wrapper_params` exports per-block data (block `A` uses
  `A₁ := A/(4⌈Q⌉+4)`, so the class scales `A/q ± O(1)`, `q ≤ Q`, and the density blocks `(A, 2A], (2A, 4A]` lie in
  `[A₁, A₁²]` for `A ≥ A₀'`); `good_block_total_le`, `block_total_le_trichotomy`, `majorArc_bound_of_A2_of_le_one` re-threaded;
  `edp_of_sliceMeanSquareA2`/`theorem18_of_sliceMeanSquareA2` and the audit pins byte-identical.
- **L1** (nucleus leaf): `band_energy_later_main_le_budget_cell` — `band_energy_later_main_le_budget` with
  `large := exp(−β r/(2Nprev))` in the fit (no M-3), stated for a single current cell `v` (or a cell range with per-`v` data).
- **L2** (Conjectures): `innerBand_later_level_main_cells` (fits `hfit r v`, Cauchy–Schwarz over `v`) and the schedule
  theorem `band_energy_typicalS_le_of_schedule_sharp_cells` with `hscheduleLater r v` at `A'_v = A/(2q_v)`-type blocks and
  `ℓ_{r,v} = ⌈log(2 q_v T/A)/log Pmom_r⌉₊ + 1`.
- **L3** (numerology, Conjectures leaf): the fixed ladder of Finding E.2 and `J(A₁)`; `hscheduleLater r v` for every
  `j ≥ 1` (scale-free), `hscheduleT0/P0` for level 0, the cover count at anchor level `J−1` (`ℓ_r = ⌈log 2T/log p_r⌉₊+1`,
  `KcovBound ≤ T^{0.46}`), `hfitInt`/`hfitPri` at the `[MR]` moment order for `𝒰(A₁)` and all `A ∈ [A₁, A₁²]`, the
  range/strength conditions, `hqcell*`/e-adic covers uniformly in `j` — every inequality as an existence statement with
  its margin recorded.
- **A2-IV-3′ / A2-V′**: `𝒮(A₁) = level 0 ∪ ladder(J(A₁)) ∪ 𝒰(A₁)`, the TK density clause with the `εc`-driven ratios,
  the level-prime clause, **`theorem sliceMeanSquareA2 : SliceMeanSquareA2`** and its audit pin.

### Dependency order

```
A2-IV-0  (settles §4 mechanically)          — first, alone
R6-1 → R6-2 → R6-3 → R6-4 → R6-5 → R6-6 → R6-7 → R6-8 → R6-9   — against SliceMeanSquareA2
R7-1 → R7-2 → R7-3 → R7-4 → R7-5 → R7-6 → R7-7
VI-9a → VI-9b → VI-9c → VI-9d ;  VI-9e ;  VI-9f (needs the R3 far-regime lemma) → VI-9g
A2-V-1 → A2-V-2 → A2-V-3 ;  A2-V-4 after VI-9g ;  A2-IV-1 → A2-IV-2 → A2-IV-3 after VI-9g
```

---

## 9. Numerology for R6/R7

1. **The `q` factor.** R6's class/character weights sum to `q ≤ C(log H)^B`; A.2 is
   applied at `ε' = ε/(4q)`, so `A₀` grows by `2 log(4C(log H)^B/ε)` and `P₁` must be
   `≥ (16q²/ε²)^{1/(2α₁)}·polylog ≈ (log H)^{115}ε^{−6}` — met by `P₁ = W^{25}`,
   `W ≥ (log H)⁵`. `A₀` is chosen after `H`, so all of this is free (Tao: "`W = log⁵H`
   will be much less than `A`"). It is *not* free for A.1 (§7.3).
2. **The block length.** `ℓ = εHq/(16πC(log H)^B) ≥ εH/(16πC(log H)^B)`, and the A.2
   window is `ℓ/d₀ ≥ ℓ/q → ∞`; A.2 needs `ℓ/q ≥ h₀(ε')`, where `h₀` comes from the
   level-one fit (`Q₁ = h/W³ ≥ P₁^{1+}`, i.e. `log h ≳ 25·1.2 log W`) and the low band —
   polynomial in `log(1/ε')`, hence `h₀(ε') = (log H)^{O(B)}·ε^{−O(1)} ≪ H`. This is
   where the density-free shape of A.2 is load-bearing (§7.3): a TK density `1/loglog h`
   would have forced `h₀ ≈ exp(exp(q²/ε²)) ≫ H`.
3. **The removal, once.** `#(window ∖ 𝒮)` summed over a good block costs
   `(h+1)·#(block ∖ 𝒮)/H·…`, i.e. the block's `𝒮ᶜ` log-density
   `≤ ∑_P 1/E_P + O(#P²/A)` (TK, `window_typicalS_complement_le`) against `ε/4`:
   `E_P ≥ 8J₀/ε` for each of the `J₀ = 2` levels — `E₁ ≍ log(log H/(125 loglog H))`
   gives `H₀(ε) ≈ exp(exp(16/ε)·125)`, and `E_𝒰 ≍ log(C/ε³)` is a condition on the
   fixed-`ε` S6 constant.
4. **Bad blocks.** As R0 found: transfer cost `2(loglog x − loglog X + 12)`, count
   `≤ 2 log w·e^{−(A−A₀−24)/2}/log 2`; `A₀ ≥ A₀^{A.2} + 26 + 2 log(8/(ε log 2))` closes it.
5. **The `W` re-tune (A2-III §5.3, `1/125 → 1/320`)** was a consequence of pricing the
   `𝒰` leg by `[MR]`'s `(4/ε²)·(log A)^{−1/50}`; with the fixed-`ε` S6 of §5 the `𝒰` leg
   no longer constrains `W`'s upper range and no published constant changes. Record
   this in the A2-III errata when VI-9g lands.

---

## 10. Risks and open questions

- **R3's far-regime repulsion lemma** (`|t − t₁| > (log A)^{20}`, Erdős–Turán +
  equidistribution of `(t−t₁)log p`) is the one piece of Phase 0 with no in-tree
  precedent beyond the Track L `ζ`-bounds. If it stalls, the `𝒯₁` strength can be
  taken from the mid-regime lemma alone by restricting the band to
  `|t − t₁| ≤ (log A)^{20}` and paying the far band trivially — but the far band has
  measure `≍ T` and the trivial bound does not fit; there is no cheap way around it.
- **The GHS `𝒯₀` closed form's `loglog` factors** must be audited before VI-9f: the
  interface's fixed `A` is spent exactly once, there.
- **The two large-values interfaces stay.** Nothing here changes the endgame
  "EDP conditional on exactly {IK 9.6, MR Lemma 8}"; Phase 0 uses both in the shape
  they are stated (`𝒯` arbitrary well-spaced), which is why VI-9c/9d are bookkeeping.
- **A2-IV-0 may move the constants** (`36`, `2/9`, S2's `γ`); the leg fits have margins
  `W^{60}`–`W^{397}` (S-cal-7) so this is safe, but §4's `c₃''` should be read off the
  theorem, not from this report.
