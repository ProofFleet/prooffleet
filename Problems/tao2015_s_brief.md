# Track R — S brief: Brun's pure sieve on a block, for the ladder levels (Finding E.4)

**Ground rules:** `Problems/tao2015_vi9g_brief.md` §0 verbatim (no `sorry`/`axiom`/`unsafe` under `MoltResearch/`, `Solutions/`,
not even in comments; new nucleus lemmas in a **new leaf file** registered by one import line in `MoltResearch/DiscrepancyAnalytic.lean`;
never edit `PlancherelHarness`, never append to `BandSchedule`/`WindowTK`/`WindowAssembly`/`HalaszComplex`; one commit per unit
`Track R: <one line> (#3044, S-<n>)`; never push/merge/rebase; `CODEX_REPORT.md` uncommitted). Read the design report
`Problems/tao2015_a1_r6r7_design_report.md` §"Finding E" item 4 and §"Phase 4" (unit S); look at `MoltResearch/Discrepancy/WindowTK.lean`
(`window_sifted_le`, `window_typicalS_complement_le`, the Mertens-type bounds it uses) and `TypicalFactorization.lean`
(`HasFactorInAll`, `typicalS`) for the tree's conventions and reusable pieces (e.g. counting multiples in `Ioc`, harmonic sums).

## Why

The ladder levels `[P_j, Q_j]`, `j ≥ 1`, have to be removed from the `𝒮`-restriction inside two pointwise bounds and in the Prop's
density clause at strength `log P_j/log Q_j = 1/ratio_j` — Turán–Kubilius (`1/E_j = 1/log ratio_j`) is not summable over
`J(A₁) → ∞` levels at polynomial ratios. Brun's pure sieve gives the sieve density with an error that is negligible for
`Q_j ≤ polylog(A)` and blocks of length `≥ A^{1−o(1)}`.

## S-1 — the Bonferroni bound (new leaf `MoltResearch/Discrepancy/BrunIntervalSieve.lean`)

For a finite set of primes `𝒫` and `m : ℕ`, with `ω_𝒫(m) := (𝒫.filter (· ∣ m)).card`:

* `bonferroni_even_nonneg`: `∀ r k : ℕ, 0 ≤ ∑ j ∈ range (2k+1), (-1)^j * (r.choose j : ℤ)` (it equals `(r−1).choose (2k)` for `r ≥ 1`
  and `1` for `r = 0`; prove by the identity `∑_{j≤m} (-1)^j C(r,j) = (-1)^m C(r−1, m)` or by induction on `r`).
* `indicator_coprime_le_truncated_inclexcl`: `(if ω_𝒫(m) = 0 then 1 else 0 : ℤ) ≤ ∑ d ∈ (𝒫.powerset.filter (fun D => D.card ≤ 2k)), (-1)^(D.card) * (if ∀ p ∈ D, p ∣ m then 1 else 0)`
  (the inner condition is `(∏ p ∈ D, p) ∣ m` for squarefree `D`; group by `D ⊆ 𝒫.filter (· ∣ m)` and apply the previous lemma
  with `r = ω_𝒫(m)`).
* `card_multiples_Ioc`: `((Ioc a b).filter (d ∣ ·)).card ≤ (b − a)/d + 1` (as reals: `≤ (b − a)/d + 1`) for `1 ≤ d`.
* `card_no_factor_Ioc_le_brun` (the theorem):
  ```
  (((Finset.Ioc a b).filter (fun m => ∀ p ∈ 𝒫, ¬ p ∣ m)).card : ℝ)
    ≤ ((b : ℝ) − a) * (∏ p ∈ 𝒫, (1 − 1/(p:ℝ)) + (∑ p ∈ 𝒫, 1/(p:ℝ))^(2k+1) / ((2k+1).factorial : ℝ))
      + ((𝒫.card : ℝ) + 1)^(2k)
  ```
  Proof: sum the indicator bound over `m ∈ Ioc a b`, swap sums, `∑_{D, |D| ≤ 2k} (-1)^{|D|}·#multiples(∏D) ≤ (b−a)·∑_{|D|≤2k}(-1)^{|D|}/∏D + #{D : |D| ≤ 2k}`;
  the truncated alternating sum of elementary symmetric functions `∑_{|D| ≤ 2k} (-1)^{|D|}/∏_{p∈D} p` is `≤ ∏(1 − 1/p) + e_{2k+1}(1/p)`
  where `e_{2k+1} ≤ (∑ 1/p)^{2k+1}/(2k+1)!` (Bonferroni again, now for the numbers `1/p`, or directly: `∏(1 − x_p) = ∑_D (-1)^{|D|}∏_D x_p`
  and the tail `∑_{|D| ≥ 2k+1}` has alternating partial sums bounded by its first term); `#{D ⊆ 𝒫 : |D| ≤ 2k} ≤ (#𝒫 + 1)^{2k}`.
  State every intermediate inequality as its own lemma; prefer `Finset.prod_one_sub`-type expansions (`Finset.prod_sub`/`Finset.prod_add`
  over the two-element sum) or induction on `𝒫`.

## S-2 — the log-mass corollary and the Mertens input

* `sum_one_div_no_factor_Ioc_le_brun`: for `1 ≤ a ≤ b`, `∑_{m ∈ Ioc a b, no factor in 𝒫} 1/m ≤ (1/a)·[RHS of S-1]` (or the dyadic
  version on `Ioc a (2a)` with `∑_{Ioc a 2a} 1/m ≥ 1/2` so that the bound reads `≤ 2(∏(1−1/p) + E^{2k+1}/(2k+1)!)·∑_{Ioc a 2a} 1/m + 2(#𝒫+1)^{2k}/a`).
* `prod_one_sub_inv_le_exp_neg_sum`: `∏_{p∈𝒫}(1 − 1/p) ≤ exp(−∑_{p∈𝒫} 1/p)` (from `1 − x ≤ e^{−x}`).
* Connect to the tree's Mertens bounds for `E = ∑_{P ≤ p ≤ Q} 1/p ≥ log(log Q/log P) − c` (find the existing lemma — the density clause
  of the phase briefs cites "`window_typicalS_complement_le` + Mertens"; `levelPrimeMassBound` in `TrackCStage5InnerBandSchedule.lean`
  is the upper envelope; the lower bound may be in `MoltResearch/Discrepancy/Mertens*.lean` or `PrimeSums*.lean` — search) so that
  `∏(1 − 1/p) ≤ e^{c}·log P/log Q`. If no lower Mertens bound exists in the tree, state the corollary with `E` as a parameter and record it.

## S-3 — the ladder application (a docstring + one lemma)

`no_factor_density_le_of_ratio`: with `k := ⌈e·E⌉₊` (so `E^{2k+1}/(2k+1)! ≤ (eE/(2k+1))^{2k+1} ≤ 2^{−2k−1}`), the sifted log-mass on
`Ioc a (2a)` is `≤ 2(e^{−E} + 2^{−2k−1})∑_{Ioc a 2a}1/m + 2(#𝒫+1)^{2k}/a`; record that for `#𝒫 ≤ Q ≤ exp((log a)^{1/2})` and `k ≤ 3E`
the remainder `(Q+1)^{2k}/a ≤ a^{−1/2}` for `a ≥ a₀(E)`.


## S-4 (unit X of the design report) — the ladder levels leave the inclusion–exclusion (second leaf `MoltResearch/Discrepancy/TypicalSLadderSplit.lean`, importing `ExceptionalHalaszSharp`, `LowBandTypicalSSharp`, `BrunIntervalSieve`)

Both pointwise bounds carry `2^{#levels}` from `norm_typicalSQuotCoeff_poly_le_inclexcl` / the low-band inclusion–exclusion. With a
ladder of `J(A₁) → ∞` levels this cannot be paid at fixed strength. Split `levels = base ++ ladder` and remove the ladder by density:

* `typicalSQuotCoeff_append_sub_support`: for `n`, `typicalSQuotCoeff g P (typicalS 0 B (base ++ ladder)) n` and
  `typicalSQuotCoeff g P (typicalS 0 B base) n` agree unless `n ∈ typicalS 0 B base` and `∃ L ∈ ladder, ∀ p ∈ L, ¬ p ∣ n`; each has norm `≤ 1`
  (`norm_typicalSQuotCoeff_le_one`). (`HasFactorInAll (base ++ ladder) n ↔ HasFactorInAll base n ∧ HasFactorInAll ladder n` — check
  `TypicalFactorization.lean` for the `append` lemma.)
* `norm_typicalS_quot_block_poly_le_sharp_split`: under the hypotheses of `norm_typicalS_quot_block_poly_le_sharp` for `rest := base`,
  ```
  ‖∑ n ∈ Ioc (A/q) (B/q), (typicalSQuotCoeff g P (typicalS 0 B (base ++ ladder)) n / n) * e(−log n · t)‖
    ≤ cellHalaszSharpBound x0 D δ₀ (A/q) (B/q) P base
      + ∑ L ∈ ladder, ∑ n ∈ (Ioc (A/q) (B/q)).filter (fun n => ∀ p ∈ L, ¬ p ∣ n), (1:ℝ)/n
  ```
  (triangle inequality on the difference, `‖coeff‖ ≤ 1`, union bound over `L`), and the corollary with S-2 for each `L`:
  `+ ∑_{L∈ladder} (1/(A/q))·[(B/q − A/q)(∏_{p∈L}(1−1/p) + E_L^{2k_L+1}/(2k_L+1)!) + (#L+1)^{2k_L}]`.
* `norm_typicalS_dirichlet_poly_le_low_band_sharp_split` and `integral_norm_typicalS_dirichlet_poly_sq_le_low_band_eps_split`: the same for
  the low band — the polynomial over `typicalS a b (base ++ ladder)` is the one over `typicalS a b base` minus the terms with `m` sifted
  by some ladder level, so the pointwise bound is `C_base + ∑_{L} ∑_{m ∈ Ioc a b, no factor in L} 1/m` and the integral bound is
  `2K·(2^{#base}·η·b/(a+1) + ∑_L (…))²` (state it with the sieved remainder as an explicit parameter `Rem`, plus the S-2 instance).

Record in the report the exact compiled shapes of the split bounds; they are what unit L3 instantiates with `base = [level 0]`
(quotient sums) and `base = [level 0, 𝒰]` (low band).

## Verification, report, stop rule

`lake env lean` the new file; `lake build MoltResearch.DiscrepancyAnalytic`; grep gates; `check_layering.sh`; `python3 scripts/check_aggregator_coverage.py`;
`#print axioms` of `card_no_factor_Ioc_le_brun` (standard three). `CODEX_REPORT.md`: statements as compiled, which Mertens lower bound
was found (or that none exists). Stop only on a genuine impossibility (there is none expected — this is textbook).
