# Problem Card: nucleus upstreaming pilot (multi-agent demonstration)

Status: active

## 0. One-line pitch

Six independent, self-contained restatements of results the Track R campaign proved in repository-specific form, each rewritten in
Mathlib idiom in its own pre-allocated leaf — a demonstration that several agents can work the same card concurrently with the card and
CI as the only coordination (no conductor-written briefs). Each item is also an upstreaming candidate (these results are absent from Mathlib).

## 1. Rules for this card (read with `AGENTS.md`)

- **One item per agent at a time; one item per PR.** Claim an item by pushing a branch `up/<id>-<yourname>` and opening a **draft PR**
  titled `<id>: <item name>` *before* writing Lean; check `gh pr list --state open --search "<id>"` first — an item with an open PR is taken.
- **Edit only your pre-allocated file** `MoltResearch/Discrepancy/Upstream/<File>.lean` (already registered in `MoltResearch/DiscrepancyUpstream.lean`,
  a CI target). Do not modify any other file. Do not add imports beyond your file's listed sources plus Mathlib.
- The deliverable: the Mathlib-style statement(s) with a docstring citing the classical source, proved from the named tree lemmas (a
  restatement/reduction, not a re-proof), and one `example` exercising the new statement. No `sorry`/`axiom`/`unsafe`.
- Before marking the PR ready: `~/.elan/bin/lake env lean <your file>`, `./scripts/forbid_sorry.sh`, `./scripts/forbid_axiom_unsafe.sh`,
  `./scripts/check_layering.sh`, `python3 scripts/check_aggregator_coverage.py`, `~/.elan/bin/lake build MoltResearch.DiscrepancyUpstream`.
- PR body must carry the metadata lines: `Card: Problems/nucleus_upstreaming.md`, `Track: B`, `Checklist item: <the item's checkbox text verbatim>`.
- Do not merge; do not tick the checkbox (the conductor ticks after the squash-merge). Write your findings in the PR body.

## 2. Decomposition (mergeable sub-tasks)

- [x] Setup: card, pre-allocated leaf slots, aggregator, CI target

- [ ] UP-1: Mertens' first theorem — `∑_{p ≤ x, p prime} log p / p = log x + O(1)` as two explicit one-sided bounds in Mathlib idiom (`Finset.filter Nat.Prime (Finset.Icc 1 x)`, `Real.log`, explicit absolute constants), proved from `MoltResearch/Discrepancy/MertensFirst.lean` and `MertensFloor.lean`. Deliverable in `MoltResearch/Discrepancy/Upstream/MertensFirst.lean`.

- [ ] UP-2: Mertens' second theorem — `|∑_{p ≤ x, p prime} 1/p − log log x| ≤ C` for `x ≥ 3`, two-sided, explicit `C`, in Mathlib idiom, proved from `MertensFloor.lean` (`log_log_le_sum_one_div_primesBelow`), `PrimeMassCell.lean` (`sum_one_div_prime_Ioc_le_mertens`) and `BrunIntervalSieve.lean` (`prime_Ioc_mass_lower_mertens`). Deliverable in `MoltResearch/Discrepancy/Upstream/MertensSecond.lean`.

- [ ] UP-3: Chebyshev's lower bound on dyadic blocks — `θ(2n) − θ(n) ≥ c·n` and `∑_{n < p ≤ 2n} 1/p ≥ c'/log n` for `n ≥ n₀`, plus `#{n < p ≤ 2n} ≤ C n/log n`, in Mathlib idiom (`Nat.primesBelow`/`Finset.filter Nat.Prime`, `Real.log`), proved from `ChebyshevBlock.lean` (`blockLog_ge`, `sum_one_div_prime_block_ge`, `card_block_le`). Deliverable in `MoltResearch/Discrepancy/Upstream/ChebyshevBlock.lean`.

- [ ] UP-4: Kusmin–Landau and the second-derivative test — the Kusmin–Landau inequality and van der Corput's discrete second-derivative test as standalone Mathlib-style statements about `∑_{n ∈ Finset.Ico M N} exp(2πi f(n))` (phases as `ℕ → ℝ`, hypotheses on first/second differences, explicit constants, no repository-specific notation in the statement), proved from `ExpSums.lean` (`kusmin_landau`, `vdc2`). Deliverable in `MoltResearch/Discrepancy/Upstream/ExponentialSumTests.lean`.

- [ ] UP-5: Brun's pure sieve on an interval — `#{m ∈ (a, b] : ∀ p ∈ P, ¬ p ∣ m} ≤ (b − a)(∏_{p∈P}(1 − 1/p) + E^{2k+1}/(2k+1)!) + (#P + 1)^{2k}` for any finite set `P` of primes and any `k`, in Mathlib idiom (`Finset.Ioc`, `Finset.prod`, `Nat.factorial`), with the log-mass corollary, proved from `BrunIntervalSieve.lean` (`card_no_factor_Ioc_le_brun`, `sum_one_div_no_factor_Ioc_le_brun`). Deliverable in `MoltResearch/Discrepancy/Upstream/BrunSieve.lean`.

- [ ] UP-6: Gallagher's separated-sum inequality and the Halász–Montgomery duality lemma — Gallagher's inequality `∑_{t ∈ 𝒯} ‖F t‖² ≤ ∫_{−T}^{T+1} (‖F‖² + 2‖F‖‖F'‖)` for `1`-separated points, and the abstract duality/Schur bound `∑_t ‖∑_i b_i χ_i(t)‖² ≤ (∑_i ‖b_i‖²)·max_t ∑_s ‖∑_i χ_i(t) conj(χ_i(s))‖`, both as standalone Mathlib-style statements (general index types, `Finset`, `ℂ`), proved from `DyadicMVT.lean` (`sum_norm_sq_le_integral_of_separated`) and `HalaszMontgomeryLargeValues.lean` (`sum_norm_sq_le_norm_sq_mul_sup_kernel`). Deliverable in `MoltResearch/Discrepancy/Upstream/LargeValuesDuality.lean`.

