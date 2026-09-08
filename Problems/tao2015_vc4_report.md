# Track R — V-C4: Codex run 23 final report (2026-09-07)

Verbatim final report of Codex run 23 (gpt-5.6-sol, brief `Problems/tao2015_vc4_brief.md`), whose four commits shipped as the V-C4a PR:
Landau's core at a free radius, the zero-free region from a growth bound on `ζ` (`zeta_zero_free_of_growth`, width `c(loglog t)^{1/a−1}(log t)^{−1/a}`),
the regular-part bound on `ζ'/ζ` inside the region (`zeta_regular_logDeriv_bound_of_growth`, exponent `m(a) = 2 + 1/a`), and the validation
against the tree's crude bound. **V-C4-4 stopped on a defect of V-B's `ZeroFreeRegionData`** (Finding V-1 in the design report): the record
asks for the region up to height `Z = 8πT + P²` with the width and the regular-part bound fixed by `T`, which no region satisfies as `P → ∞` at
fixed `T`. Repair: a height-indexed record and a two-regime envelope (run 25). Commit hashes are the run's, before cherry-pick.

---

# Track R — V-C4 report

## Outcome

V-C4-1, V-C4-2, V-C4-3, and V-C4-5 are implemented as new analytic leaf
modules and committed separately. V-C4-4 is not asserted: the current
`ZeroFreeRegionData` quantifiers ask for height-uniform information that does
not follow from the height-dependent region proved here (or from the existing
de la Vallee Poussin region).

## Commits

- `7933f86e` — `Track R: generalize the Landau core to a free radius (#3044, V-C4-1)`
- `3924b3af` — `Track R: derive the zero-free region from zeta growth (#3044, V-C4-2)`
- `c0fd08b4` — `Track R: bound the regular zeta logarithmic derivative (#3044, V-C4-3)`
- `8ffe006e` — `Track R: validate the crude logarithmic growth regime (#3044, V-C4-5)`

No push, merge, or rebase was performed.

## Parameter choices

The free-radius Landau constant is `C_L = 16`, so the conclusion is
`16 * (K + 1) / R`; at `R = 1/2` this is the tree's coefficient `32`.
The zeta specialization retains `1 <= |tau|`, which ensures that the full
closed ball of radius at most `1/2` avoids the pole. This is the domain
hypothesis needed to feed `landau_inequality`; the tree supplies everything
else.

For the growth region, with `L = log |t|` and `ell = log L`, the proof uses

```text
R = (ell / (B * L))^(1/a)
Q = 6 + 3*b + 2*B0
P = max(c_pole, 0)
V = 1000 * (Q + P + 1)
delta = R / (V * ell)
c = B^(-1/a) / (9*V).
```

The two Landau budgets are at most `Q * ell`. The `3-4-1` inequality and the
pole estimate then give the claimed zero-free width

```text
c * ell^(1/a - 1) / L^(1/a).
```

For the regular-part estimate, the exported half-width is

```text
eta(t) = min(1/8, (c/2) * zetaGrowthWidth a (2*|t|)),
```

and the recorded logarithmic exponent is

```text
m(a) = 2 + 1/a.
```

The Borel--Caratheodory disc has center `1 + eta/2 + i*t` and outer radius
`2*eta`. Its closed half-disc therefore reaches `Re z = 1 - eta/2`, while the
outer disc remains inside the zero-free width. The near-one half is controlled
by the analytic logarithm; `Re z > 1 + eta` is controlled by absolute
convergence of the von Mangoldt series. The final statement is directly for
the regular part

```text
norm (-zeta'/zeta(z) - 1/(z-1)) <= C * (log |Im z|)^m.
```

## Findings

### V-C4-4 interface obstruction

`ZeroFreeRegionData.region` quantifies over every natural `P >= 2` and every
`T >= 1`, but sets

```text
eta = min(1/2, (log (2*T))^(-theta))
Z = 8*pi*T + P^2
M = (log (2*T))^m.
```

At fixed `T = 1`, `eta = 1/2`, while `Z` tends to infinity with `P` and `M`
stays fixed. Thus the field requires nonvanishing on `Re z >= 1/2` and a
fixed regular-part bound through arbitrarily large heights. A theorem whose
width decreases and whose logarithmic-derivative bound grows with `|Im z|`
cannot discharge that field. Taking a minimum with the existing de la Vallee
Poussin region only narrows the width as the height grows; it cannot produce
the fixed `eta(T)` required by the record.

A viable repair must change V-B's bookkeeping. Two natural options are:

1. evaluate the region width and regular bound at the actual rectangle height
   `Z`, then redo the envelope with those quantities; or
2. require the region only in the range where `P` is bounded by a fixed power
   of `T`, and make `prime_large_values_bound_of_zeroFreeRegionData` use its
   direct/short-height estimate in the complementary range.

The second option preserves the desired `T`-based decay more closely, but it
requires a V-B theorem change. No interface class or audit file was changed.

### V-C4-5 zero-coefficient issue

The crude tree estimate gives

```text
log norm zeta <= 2 * log |t| + log 10000.
```

It is not an instance of the stated `ZetaGrowthBound` with `B = b = 0`, since
that would make its right-hand side constant even at `sigma >= 1`. The
validation leaf therefore records the honest linear-logarithmic bound and
checks it against the tree's existing machine-checked de la Vallee Poussin
conclusion `beta <= 1 - c/log |t|`.

## Verification

- Single-file checks passed for all four new leaves.
- Forbidden-token grep over `MoltResearch/` and `Solutions/`: passed.
- `./scripts/check_layering.sh`: passed.
- `python3 scripts/check_aggregator_coverage.py`: 199 modules, 197 reachable;
  only the two existing allowlisted example modules remain outside the graph.
- `lake build MoltResearch.DiscrepancyAnalytic Conjectures`: 8346 jobs, passed.
- `#print axioms` for `zeta_landau_core_at_radius`,
  `zeta_zero_free_of_growth`, `zeta_regular_logDeriv_bound_of_growth`, and
  `zeta_crude_growth_validation`: each reports only `propext`,
  `Classical.choice`, and `Quot.sound`.

The branch is ahead of `origin/main` and also behind its two newest commits;
it was left unre-based as required.
