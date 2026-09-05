# Track R — S+X: Codex run 12 final report (2026-09-05)

Verbatim final report of Codex run 12 (gpt-5.6-sol, brief `Problems/tao2015_s_brief.md`), whose four commits shipped as the S+X PR.
S = Brun's pure sieve on a block (`MoltResearch/Discrepancy/BrunIntervalSieve.lean`: Bonferroni, `card_no_factor_Ioc_le_brun`,
the log-mass corollary, the Euler-product/Mertens consequences — the tree's lower Mertens bound is `prime_Ioc_mass_lower_mertens`
with loss `12`, from `MertensFloor`/`MertensFirst` — and `no_factor_density_le_of_ratio`); X = the ladder levels leave the
inclusion–exclusion of the two pointwise bounds (`TypicalSLadderSplit.lean`: `norm_typicalS_quot_block_poly_le_sharp_split(_brun)`,
the low-band pointwise and integral splits with `ladderSiftedLogMass`/`ladderBrunLogMassBound`). See the design report, Finding E.4.
Commit hashes are the run's, before cherry-pick.

---

# Track R — Brun ladder sieve report

## Result

Units S-1 through S-4 are implemented in two analytic leaf modules and
registered in `MoltResearch/DiscrepancyAnalytic.lean`.

- `MoltResearch/Discrepancy/BrunIntervalSieve.lean`: signed Bonferroni,
  interval multiple counts with two-sided endpoint error, elementary
  symmetric truncation, Brun cardinality and log-mass bounds, Euler-product
  and Mertens consequences, and the canonical ladder-depth specialization.
- `MoltResearch/Discrepancy/TypicalSLadderSplit.lean`: append support,
  quotient and low-band pointwise splits, explicit per-level Brun
  remainders, and low-band integral splits with either an abstract `Rem` or
  the direct Brun expression.

## Findings

1. The cardinality theorem needs `a ≤ b`. Without it, the displayed main
   term `(b : ℝ) - a` can be negative even though `Ioc a b` is empty.
2. The product-divisibility conversion needs every member of `P` to be
   prime. This is explicit as `hP : ∀ p ∈ P, p.Prime`.
3. A signed inclusion--exclusion estimate cannot use only an upper bound for
   the number of multiples: odd-cardinality subsets reverse the inequality.
   The implementation proves the two-sided error
   `|#multiples - (b-a)/d| ≤ 1` and sums that error.
4. The Mertens lower input exists. The implementation combines
   `log_log_le_sum_one_div_primesBelow` from `MertensFloor.lean` (loss `1`)
   with `sum_one_div_primesBelow_le_sharp` from `MertensFirst.lean` (loss
   `11`). Thus the interval mass has constant `12`, and the product is at
   most
   `exp 12 * log (lo+1) / log (hi+1)`.
5. In `no_factor_density_le_of_ratio`, `E` is the actual reciprocal mass,
   not merely a lower bound. This is necessary because the factorial tail
   contains the actual mass. A lower Mertens estimate is applied separately
   to the Euler-product term.
6. Ladder sums use `ladder.toFinset`. Repeated identical levels are counted
   once, which strengthens the union bound.

## Principal compiled statements

```lean
card_no_factor_Ioc_le_brun
    (a b : ℕ) (hab : a ≤ b)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (k : ℕ) :
  (((Ioc a b).filter (fun m => ∀ p ∈ P, ¬ p ∣ m)).card : ℝ) ≤
    ((b : ℝ) - a) *
      ((∏ p ∈ P, (1 - 1 / (p : ℝ))) +
        (∑ p ∈ P, (1 : ℝ) / p) ^ (2 * k + 1) /
          ((2 * k + 1).factorial : ℝ)) +
      ((P.card : ℝ) + 1) ^ (2 * k)

sum_one_div_no_factor_Ioc_le_brun
    (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (k : ℕ) :
  (∑ m ∈ (Ioc a b).filter (fun m => ∀ p ∈ P, ¬ p ∣ m),
      (1 : ℝ) / m) ≤
    (1 / (a : ℝ)) *
      (((b : ℝ) - a) *
        ((∏ p ∈ P, (1 - 1 / (p : ℝ))) +
          (∑ p ∈ P, (1 : ℝ) / p) ^ (2 * k + 1) /
            ((2 * k + 1).factorial : ℝ)) +
        ((P.card : ℝ) + 1) ^ (2 * k))

prime_Ioc_mass_lower_mertens (lo hi : ℕ)
    (hlo : 3 ≤ lo) (hlohi : lo ≤ hi) :
  Real.log (Real.log ((hi : ℝ) + 1)) -
      Real.log (Real.log ((lo : ℝ) + 1)) - 12 ≤
    ∑ p ∈ (Ioc lo hi).filter Nat.Prime, (1 : ℝ) / p

no_factor_density_le_of_ratio
    (a : ℕ) (ha : 1 ≤ a)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (E : ℝ) (hE : 0 ≤ E)
    (hmass : E = ∑ p ∈ P, (1 : ℝ) / p) :
  let k := ⌈Real.exp 1 * E⌉₊
  (∑ m ∈ (Ioc a (2 * a)).filter (fun m => ∀ p ∈ P, ¬ p ∣ m),
      (1 : ℝ) / m) ≤
    2 * (Real.exp (-E) + (2 : ℝ) ^ (-(↑(2 * k + 1) : ℤ))) *
        (∑ m ∈ Ioc a (2 * a), (1 : ℝ) / m) +
      2 * ((P.card : ℝ) + 1) ^ (2 * k) / a
```

The compiled support statement is:

```lean
typicalSQuotCoeff_append_sub_support
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (P : Finset ℕ) (B n : ℕ)
    (base ladder : List (Finset ℕ)) :
  (typicalSQuotCoeff g P (typicalS 0 B (base ++ ladder)) n ≠
      typicalSQuotCoeff g P (typicalS 0 B base) n →
    n ∈ typicalS 0 B base ∧ MissingFactorInSome ladder n) ∧
  ‖typicalSQuotCoeff g P (typicalS 0 B (base ++ ladder)) n‖ ≤ 1 ∧
  ‖typicalSQuotCoeff g P (typicalS 0 B base) n‖ ≤ 1
```

The quotient split has the same hypotheses as
`norm_typicalS_quot_block_poly_le_sharp` for `base`, and compiles with
conclusion:

```lean
‖∑ n ∈ Ioc (A / q) (B / q),
    (typicalSQuotCoeff g P (typicalS 0 B (base ++ ladder)) n / (n : ℂ)) *
      ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤
  cellHalaszSharpBound x0 D δ₀ (A / q) (B / q) P base +
    ladderSiftedLogMass (A / q) (B / q) ladder
```

`norm_typicalS_quot_block_poly_le_sharp_split_brun` replaces the last term
verbatim by
`ladderBrunLogMassBound (A / q) (B / q) ladder ks`, under
`1 ≤ A/q` and primality of every ladder level.

The low-band pointwise split compiles with conclusion:

```lean
‖∑ m ∈ typicalS a b (base ++ ladder),
    (g m / (m : ℂ)) *
      ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖ ≤
  (2 ^ base.length : ℕ) *
      sharpTwistedDirichletCost (D / 2) delta0 a b +
    ladderSiftedLogMass a b ladder
```

For every `eta > 0`, `eta ≤ 1`,
`integral_norm_typicalS_dirichlet_poly_sq_le_low_band_eps_split` supplies
fixed `D0` and `x0`. Under the original low-band hypotheses and
`0 ≤ Rem`, `ladderSiftedLogMass a b ladder ≤ Rem`, its compiled conclusion
is:

```lean
(∫ t in {t : ℝ | |t| < K},
  ‖∑ m ∈ typicalS a b (base ++ ladder),
      (g m / (m : ℂ)) *
        ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖ ^ 2) ≤
  2 * K * ((2 ^ base.length : ℕ) *
      (eta * (b : ℝ) / ((a + 1 : ℕ) : ℝ)) + Rem) ^ 2
```

The `_split_brun` corollary instantiates `Rem` as
`ladderBrunLogMassBound a b ladder ks`.

Definitions expand as follows:

```lean
ladderSiftedLogMass a b ladder =
  ∑ L ∈ ladder.toFinset,
    ∑ n ∈ (Ioc a b).filter (fun n => ∀ p ∈ L, ¬ p ∣ n), (1 : ℝ) / n

ladderBrunLogMassBound a b ladder ks =
  ∑ L ∈ ladder.toFinset,
    (1 / (a : ℝ)) *
      (((b : ℝ) - a) *
        ((∏ p ∈ L, (1 - 1 / (p : ℝ))) +
          (∑ p ∈ L, (1 : ℝ) / p) ^ (2 * ks L + 1) /
            ((2 * ks L + 1).factorial : ℝ)) +
        ((L.card : ℝ) + 1) ^ (2 * ks L))
```

## Verification

- `lake env lean MoltResearch/Discrepancy/BrunIntervalSieve.lean`: passed.
- `lake env lean MoltResearch/Discrepancy/TypicalSLadderSplit.lean`: passed.
- `lake build MoltResearch.DiscrepancyAnalytic`: passed (8109 jobs).
- `scripts/forbid_sorry.sh`: passed.
- `scripts/forbid_axiom_unsafe.sh`: passed.
- `scripts/check_layering.sh`: passed.
- `python3 scripts/check_aggregator_coverage.py`: passed; 182 modules,
  180 reachable, with only the two existing allowlisted example modules.
- `#print axioms MoltResearch.card_no_factor_Ioc_le_brun`:
  `[propext, Classical.choice, Quot.sound]`.

## Commits

- `0b6c4e0b` — `Track R: prove Brun's interval sieve bound (#3044, S-1)`
- `96d81e74` — `Track R: add Brun log-mass and Mertens bounds (#3044, S-2)`
- `85e75949` — `Track R: specialize Brun's sieve to ladder density (#3044, S-3)`
- `08181c6d` — `Track R: split ladder levels from sharp bounds (#3044, S-4)`

No push, merge, or rebase was performed. This report remains uncommitted.
