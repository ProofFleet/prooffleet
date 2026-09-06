# Track R — V-A: Codex runs 19–20 report (2026-09-06)

Run 19 (brief `Problems/tao2015_va_brief.md`) committed V-A-1…V-A-3 and stopped on three defects of the brief (report below, verbatim): the
region hypothesis `hlog` excluded the `1/4`-neighbourhood of the pole that the shifted contour crosses (repair: a bound `‖−ζ'/ζ(z) − 1/(z−1)‖ ≤ M`
on the **regular part** over the full closed rectangle, `hreg`), the symmetric rectangle put the pole on the boundary at `|u| = Y/2` (repair:
asymmetric heights `[−Y−u, Y−u]`), and two windows supported on `[Q, 2Q]` cannot cover `(P, 2P]` (repair: a plateau window, `ψ ≡ 1` on `[0,1]`,
supported in `[−1/2, 3/2]`). Run 20 (the brief with its resume note) completed **V-A**: the plateau window (`bedbad1f`), the asymmetric Mellin
rectangle shift with the pole handled by Cauchy's formula for the rational part (`0af4bd2c`), the regular contour sides (`44af54f3`), and the
prime powers (`ad68c614`) — all in `MoltResearch/Discrepancy/PrimeSumZeroFree.lean`. Run 20 was then cut off by the Codex usage limit while
writing V-B (`PrimeLargeValuesFromRegion.lean`, 236 lines uncommitted, saved for the resume). The seven V-A commits shipped as the V-A PR.
Run 19's verbatim report follows (run 20 wrote no final report).

---

# Track R V-A / V-B run report

## Completed units

- `abe654a8` — `Track R: construct the Mellin window and vertical decay (#3044, V-A-1)`
  - Defines the smooth multiplicative window and its Mellin transform.
  - Proves compact support, smoothness, entire differentiability, and the explicit
    vertical estimate with constant `60000 * (C + 1)^2`.
- `1e3440e1` — `Track R: prove the Mellin representation of von Mangoldt sums (#3044, V-A-2)`
  - Proves Mellin convergence and vertical integrability.
  - Applies `mellinInv_mellin_eq` termwise.
  - Justifies the sum/integral interchange by summability of the integrals of
    norms.
  - Identifies the Dirichlet series with `-ζ'/ζ` on
    `c = 1 + 1 / log (2P)`.
- `fb43e70b` — `Track R: truncate the right Mellin line with an explicit tail (#3044, V-A-3)`
  - Derives the right-line logarithmic bound from absolute convergence and
    `zeta_logDeriv_pole_bound`.
  - Proves the two-sided majorant tail
    `∫_{(-∞,-H]∪(H,∞)} (1+τ²)⁻¹ dτ ≤ 2/H`.
  - Proves the requested `O(P^c log(2P)/H)` right-line tail estimate.

The new nucleus leaf is
`MoltResearch/Discrepancy/PrimeSumZeroFree.lean`, registered in
`MoltResearch/DiscrepancyAnalytic.lean`.

## Stop condition

The shifted-line estimate required by V-A-5 is not implied by the stated
`hlog` hypothesis.  On the shifted line, take the point of the translated
zeta argument

```text
z = 1 - η/2 + 0 i.
```

It obeys `‖z - 1‖ = η/2 ≤ 1/4`, and the inequality is strict whenever
`η < 1/2`.  Therefore the premise `1/4 ≤ ‖z - 1‖` of `hlog` is unavailable on
an interval of the shifted contour.  `hzero` gives only nonvanishing, not a
quantitative bound for `‖ζ'/ζ‖`; `exists_zeta_pole_reg` supplies an analytic
regularization but no bound for its reciprocal denominator in terms of the
given `M` and `η`.  Consequently the claimed shifted-side bound
`O(M P^(1-η/2) / η)` cannot be derived from the supplied inputs.

A sufficient repair is to add a local regular-part hypothesis, for example

```text
hreg : ∀ z, 1 - η ≤ z.re → z.re ≤ 2 → |z.im| ≤ Y →
  z ≠ 1 → ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤ M / η
```

or to strengthen `hlog` so it covers the full punctured rectangle with the
pole term priced explicitly.

The symmetric rectangle in the brief also places the pole on the boundary
when `|u| = Y/2`.  This is repairable without a new hypothesis by using the
asymmetric `s`-heights `-Y-u` and `Y-u`, so that the translated zeta argument
has heights exactly `-Y` and `Y` and the pole remains internal.

## Later V-B issue

With the V-A-1 profile, a window at scale `Q` is supported on `[Q, 2Q]` and
vanishes at its lower endpoint.  Thus windows at scales `P` and `sqrt(2) P`
cannot satisfy `w₁ + w₂ ≥ 1` on all of `(P, 2P]`: immediately above `P`, the
second window is zero and the first tends to zero.  V-B needs a wider-support
partition of unity or additional overlapping scales.

## Verification

All final checks passed:

- forbidden-token grep over `MoltResearch/` and `Solutions/`: no matches;
- `./scripts/check_layering.sh`: `OK`;
- `python3 scripts/check_aggregator_coverage.py`: 193 modules, 191 reachable,
  with only the two allowlisted example modules reported;
- `lake build MoltResearch.DiscrepancyAnalytic Conjectures`: 8339 jobs,
  completed successfully;
- axiom reports for `exists_primeMellin_window`,
  `primeMellin_vonMangoldt_representation`,
  `primeMellin_vonMangoldt_zeta_representation`, and
  `exists_primeMellin_right_tail_bound`: each depends only on `propext`,
  `Classical.choice`, and `Quot.sound`.
