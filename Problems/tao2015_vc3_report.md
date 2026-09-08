# Track R — V-C3 and the endpoint: Codex run 29 final report (2026-09-08)

Verbatim final report of Codex run 29 (gpt-5.6-sol, brief `Problems/tao2015_vc3_brief.md`), whose six commits shipped as the V-C3 PR:
`MoltResearch/Discrepancy/ZetaGrowthVinogradov.lean` (the Weyl saving transferred to ζ blocks, the optimisation, the assembled bound with the
repaired cutoff `N = ⌊t⌋² + 1`, **`zeta_growth_vinogradov`** and **`exists_zetaGrowthBound_vinogradov : ∃ t₀ B B₀, ZetaGrowthBound t₀ (33/25) B 1 B₀`**),
the V-C4 threshold lowered to `a ≥ 33/25` (margin `47/6600`), and `Conjectures/…/TrackCStage5PrimeLargeValuesDischarge.lean`: the
`ZeroFreeRegionDataH` value from the growth bound, **`instance primeLargeValuesAssumption_vinogradov : PrimeLargeValuesAssumption`**, and
**`theorem erdos_discrepancy_unconditional (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f`**, pinned in `TrackCAxiomAudit.lean` to
`[propext, Classical.choice, Quot.sound]`. Finding: the brief's approximate-functional-equation cutoff `N ≍ |t|` does not make the tail `≤ 3`
uniformly (the compiled tail is `≍ |t|^{1−σ}`); the proof uses `X = ⌊|t|⌋`, `N = X² + 1`, with V-C2 on the blocks up to `X` and the Kusmin estimate
plus Abel summation on the blocks from `X` to `X²`. Commit hashes are the run's, before cherry-pick.

---

# Track R V-C3 report

## Result

The V-C2 estimate with saving

```text
1 - c / (lambda^3 * log(2 * lambda)^3)
```

has been transferred to zeta blocks, optimized, assembled across the full
strip, packaged for V-C4, and composed through the height-indexed zero-free
region to the unconditional EDP endpoint.

The final growth theorem is:

```lean
theorem zeta_growth_vinogradov :
    ∃ (t₀ B B₀ : ℝ), 3 ≤ t₀ ∧ 0 < B ∧ ∀ sigma t : ℝ,
      t₀ ≤ |t| → 3 / 4 ≤ sigma → sigma ≤ 2 →
        Real.log ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤
          B * (max (1 - sigma) 0) ^ (33 / 25 : ℝ) * Real.log |t| +
            Real.log (Real.log |t|) + B₀
```

The packaged V-C4 term is:

```lean
theorem exists_zetaGrowthBound_vinogradov :
    ∃ (t₀ B B₀ : ℝ), 3 ≤ t₀ ∧ 0 < B ∧
      ZetaGrowthBound t₀ (33 / 25) B 1 B₀
```

The campaign endpoint is:

```lean
theorem erdos_discrepancy_unconditional (f : ℕ → ℤ)
    (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f
```

Its checked footprint is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

## Per-unit findings

- V-C3-1 (`d3865900`): Abel summation transfers the V-C2 phase estimate to
  weighted zeta blocks. The formal endpoint allowance is `2 * C`, stronger
  than the requested round factor `3 * C`.
- V-C3-3 (`3b2f9234`): `log(2 * lambda)^3 ≤ 54000 * lambda^(1/10)` for
  `lambda ≥ 1`. The resulting elementary optimization first gives exponent
  `41/31`; monotonicity for `0 ≤ 1 - sigma ≤ 1` weakens this safely to
  `33/25`.
- V-C3-2 (`33ae71f5`): the dyadic partial sum, approximate functional
  equation, logarithmic conversion, right-strip L-series estimate, and final
  existential growth theorem are assembled in the new leaf.
- V-C3-4 (`d174cc4a`): the leaf is registered in
  `MoltResearch.DiscrepancyAnalytic`.
- V-C3-5 (`6bd810d5`): the landed V-C4 API and its Conjectures composition
  now accept `a ≥ 33/25`. The exact consumer margin is
  `31/40 - (25/33 + 1/100) = 47/6600 > 0`.
- V-C3-6 (`0d1627f7`): the V-C4 `ZeroFreeRegionDataH` value, global
  `PrimeLargeValuesAssumption`, hypothesis-free EDP theorem, and audit pin
  are complete.

## Findings

The approximate-functional-equation cutoff proposed in the brief does not
make its stated tail bound uniform. With `N` only comparable to `|t|`, the
compiled estimate

```text
2 * ‖s - 1‖ * (N - 1)^(-sigma) / sigma
```

is of order `|t|^(1 - sigma)`, so it cannot be bounded by `3` uniformly on
`3/4 ≤ sigma ≤ 1`.

The proof uses the repaired cutoff

```text
X = floor |t|,  N = X^2 + 1.
```

This makes both the pole term and analytic tail bounded. Blocks up to `X`
use V-C2; blocks from `X` to `X^2` use the existing Kusmin estimate followed
by Abel summation. Both ranges contain `O(log |t|)` dyadic blocks, so the
required single `loglog |t|` term is preserved.

The brief also retains stale `7/5` text after its explicit exponent update.
The implementation follows the update and uses `33/25` throughout, including
the V-C4 admissibility threshold.

## Accounting discrepancies found

1. The claimed `N ≍ |t|` tail bound `≤ 3` is false for the compiled
   `zeta_afe_strip` tail estimate. The long-cutoff/Kusmin repair above is used.
2. The old V-C4 code required `7/5 ≤ a`; this was incompatible with the
   mandated `33/25` output and was updated. The downstream strict exponent
   comparison remains valid with margin `47/6600`.

## Verification

- `lake env lean MoltResearch/Discrepancy/ZetaGrowthVinogradov.lean`: exit 0.
- `lake build Conjectures.C0002_erdos_discrepancy.src.TrackCStage5PrimeLargeValuesDischarge Conjectures.C0002_erdos_discrepancy.src.TrackCAxiomAudit`: exit 0.
- forbidden-declaration grep under `MoltResearch/` and `Solutions/`: empty.
- `./scripts/check_layering.sh`: exit 0, `check_layering: OK`.
- `python3 scripts/check_aggregator_coverage.py`: exit 0; 208 modules, 206
  reachable, with only the two repository allowlisted example modules.
- `lake build MoltResearch.DiscrepancyAnalytic Conjectures`: exit 0, 8358
  jobs completed. Output contains pre-existing lint warnings only.

## Work left undone and exact blocker

None. The growth estimate, V-C4 composition, global prime-large-values
discharge, unconditional EDP theorem, and exact axiom audit are complete.
