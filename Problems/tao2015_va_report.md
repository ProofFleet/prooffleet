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


---

# Run 21 (V-B resume): completion

Verbatim final report of Codex run 21 (same branch, the brief with its resume note), whose three new commits shipped as the V-B PR:
V-B-1 (square-reciprocal packing, weighted adjoint duality, the plateau large-values specialisation), the V-A assembly (the rational-pole
extraction, the asymmetric-tail composition, the von Mangoldt/prime/positive-phase kernel capstones), and V-B-2 (`ZeroFreeRegionData`, the
Fourier/Mellin phase bridge, **`primeLargeValues_of_zeroFreeRegion`** producing `PrimeLargeValuesAssumption` from region data, and
**`trackR_edp_of_zeroFreeRegion`** with its audit pin). Finding: Mathlib's `Real.fourierChar x = exp(2πix)` makes the interface phase at `t`
the Mellin phase at `−2πt`, so the safe rectangle height is `Z = 8πT + P²`, not the brief's `2T + P²`.

---

# Track R V-A / V-B run report

## Outcome

Run 20 completes the plateau-window Mellin shift, the weighted-duality proof
of `[MR]` Lemma 8, the theorem producing `PrimeLargeValuesAssumption`, and the
conditional EDP endpoint
`MoltResearch.Tao2015.trackR_edp_of_zeroFreeRegion`.

No global `PrimeLargeValuesAssumption` instance is declared. The instance is
local to the endpoint proof.

## Completed units

- `abe654a8` — original Mellin window and vertical decay (V-A-1).
- `bedbad1f` — plateau window: one on `[P,2P]`, supported in
  `[P/sqrt 2,2*sqrt 2*P]` (V-A-1).
- `1e3440e1` — Mellin inversion, sum/integral interchange, and the
  `-zeta'/zeta` Dirichlet-series representation (V-A-2).
- `fb43e70b` — explicit quadratic-decay right-line tail (V-A-3).
- `0af4bd2c` — regular-part identity on the asymmetric rectangle (V-A-4).
- `44af54f3` — full-rectangle `hreg` side bounds, with no `1/eta` loss
  (V-A-5).
- `ad68c614` — prime-power remainder at most
  `6*sqrt(P)*log(4P)` (V-A-6).
- `9aa551bb` — square-reciprocal packing, weighted adjoint duality, and the
  plateau large-values specialization (V-B-1).
- `2aed81f8` — rational-pole extraction, asymmetric-tail composition, and the
  von Mangoldt, prime, and positive-phase kernel capstones (V-A-4).
- `512fd11f` — `ZeroFreeRegionData`, the Fourier/Mellin phase bridge,
  `primeLargeValues_of_zeroFreeRegion`, `trackR_edp_of_zeroFreeRegion`, and
  its audit pin (V-B-2).

## Findings

### Corrected regular-part hypothesis

The run-19 obstruction disappears with the resume note's full-rectangle
regular-part hypothesis

```text
norm (-zeta'/zeta(z) - 1/(z-1)) <= M.
```

The regular part is shifted directly. The rational part is handled by the
rectangle identity for `(W(s)-W(1-iu))/(s+iu-1)`, so the shifted-line term has
no `1/eta` loss.

### Fourier normalisation changes the required height

Mathlib defines `Real.fourierChar x = exp(2*pi*i*x)`. Therefore the interface
phase at `t` is the Mellin phase at `-2*pi*t`, and two points in `[-T,T]` can
have Mellin-frequency difference `4*pi*T`. Since V-A requires
`|u| <= Z/2`, the safe height is

```text
Z = 8*pi*T + P^2.
```

The brief's `2*T + P^2` is insufficient for its stated Fourier character.
The formal data structure and theorem use the normalization-safe height.

### Two-region scalar strength is explicit

`ZeroFreeRegionData.region` contains the nonvanishing and `hreg` rectangle
hypotheses at

```text
eta = min (1/2) (log(2T))^(-theta),
M   = (log(2T))^m,
Z   = 8*pi*T + P^2.
```

Its `envelope` field makes the elementary two-region scalar absorption
explicit. It combines the bounded-height allowance `1/(2T+1)` with the
`4/5` decay required by the interface. The proved packing bound
`#T <= 2T+1` absorbs the former. Thus the quantitative fit is a visible field
rather than a hidden typeclass or axiom.

The public Conjectures bridge fixes
`theta = 31/40 = 3/4 + 1/40 < 4/5` and permits every fixed real logarithmic
exponent `m`.

## New public endpoints

- `MoltResearch.exists_primeMellin_prime_shift_bound`
- `MoltResearch.exists_primeMellin_kernel_bound`
- `MoltResearch.prime_large_values_bound_of_zeroFreeRegionData`
- `MoltResearch.Tao2015.primeLargeValues_of_zeroFreeRegion`
- `MoltResearch.Tao2015.trackR_edp_of_zeroFreeRegion`

## Verification

- Direct typechecks passed for both new nucleus leaves and the Conjectures
  bridge.
- The `trackR_edp_of_zeroFreeRegion` audit pin reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Forbidden-token scan over `MoltResearch/` and `Solutions/`: passed.
- `./scripts/check_layering.sh`: `OK`.
- `python3 scripts/check_aggregator_coverage.py`: 195 modules, 193 reachable;
  only the two allowlisted example modules are uncompiled.
- `lake build MoltResearch.DiscrepancyAnalytic Conjectures`: 8342 jobs,
  completed successfully after the final theorem-signature narrowing.

## Repository state

No push, merge, rebase, or dependency update was performed. This report is
left uncommitted as required.
