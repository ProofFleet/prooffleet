# Track R — L4/V1: Codex run 13 final report (2026-09-05)

Verbatim final report of Codex run 13 (gpt-5.6-sol, brief `Problems/tao2015_l4_brief.md`), whose five commits shipped as the
L4/V1 PR. L4 = the replacement and collision legs of a level as single Dirichlet polynomials on `(A, 2B]` with one mean value
application (`WideLevelErrorLegs.lean`: `replacementEnergyBoundWide`, `collisionEnergyBoundWide`, coefficient bound `≤ 1` by the
Ramaré weight); V1 = scale-only cell representatives (`ScaleOnlyCellRepresentatives.lean`: `hqup`, `scaleCellRepresentative`, the
level-one chain `_of_qup`); and the combined capstone `band_energy_typicalS_le_of_schedule_sharp_cells_wide`
(`TrackCStage5InnerBandScheduleSharpCellsWide.lean`) with the unit-X split of the exceptional pointwise bound. See the design report,
Finding E.5/E.6. Commit hashes are the run's, before cherry-pick.

---

# Track R L4 report — wide level error legs

Date: 2026-09-05  
Branch: `vex/track-r-l4`

## Result

All five units compile and are committed separately:

| Unit | Commit | Artifact |
|---|---|---|
| L4-1 | `6989a3eb` | `MoltResearch/Discrepancy/WideLevelErrorLegs.lean`: collected replacement polynomial, coefficient bound, collar mass, one-MVT interval/set bounds |
| L4-2 | `bdcbf5ee` | same leaf: collected collision polynomial, square-divisor mass, wide collision envelope, adjusted-collision and level-leg variants |
| L4-3 | `0bd5c1d3` | `TrackCStage5InnerBandAssemblyWide.lean`: ordinary replacement and level-leg wrappers |
| L4-4 | `79726e58` | `MoltResearch/Discrepancy/ScaleOnlyCellRepresentatives.lean`: scale-only chain and an empty-cell-safe representative |
| L4-5 | `6e15b533` | `TrackCStage5InnerBandScheduleSharpCellsWide.lean`: exceptional recut, unit-X split, and combined wide capstone |

The two nucleus leaves are registered in `MoltResearch/DiscrepancyAnalytic.lean`.

## L4-1 — replacement

The leaf defines `wideReplacementCoeff` by collecting all signed collar
incidences at `n = p*m`.  The compiled identity is

```lean
typicalSCellReplacement_eq_dirichlet :
  typicalSCellReplacement ... xi =
    ∑ n ∈ Finset.Ioc A (2 * B),
      (wideReplacementCoeff ... n / (n : ℂ)) * fourierChar ...
```

The support proof uses `B ≤ 2*A` only later, for the MVT range; the identity
uses the correct superset `(A, 2B]`.  `norm_wideReplacementCoeff_le_one`
is the Ramaré estimate.  For every contributing prime, its summand has norm at
most `1 / omega_P(n)`, using
`omega_P(n/p) + 1 ≥ omega_P(n)`; summing the at most `omega_P(n)` incidences
gives one.  There is no `log A / log P` loss.

The squared coefficient mass is

```text
sum_{A<n<=2B} ||e_n||^2/n^2
  <= 8 * (E_P/(N*A) + #P/A^2),
E_P = sum_{p in P} 1/p.
```

The exact compiled hypotheses include `A ≥ 1`, `B ≤ 2A`, prime support,
the e-adic cover, `N > 0`, `q ≥ 1`, `q_v ≤ p`, and

```text
N*p <= (N+1)*q_v.
```

The corresponding harmonic mass, which is the coefficient normalization
actually consumed by the repository MVT, is

```text
sum ||e_n||^2/n <= 32 * (E_P/N + #P/A).
```

Thus the compiled closed form is

```text
replacementEnergyBoundWide A P N T
  = exp(pi) * (T/A + 8) * 32 * (E_P/N + #P/A),
```

with interval and arbitrary-set versions
`intervalIntegral_norm_sq_typicalSCellReplacement_wide_le` and
`setIntegral_norm_sq_typicalSCellReplacement_wide_le`.

## L4-2 — collision

`wideCollisionCoeff` collects the repeated-prime sum at `n`.  The identity
`typicalSCollision_eq_dirichlet` is supported on `(A,B]`, and
`norm_wideCollisionCoeff_le_one` proves

```text
||e_n|| <= #{p in P : p^2 | n} / omega_P(n) <= 1.
```

The squared and harmonic coefficient masses are respectively

```text
sum ||e_n||^2/n^2 <= (2/A) * sum_{p in P} 1/p^2 + #P/A^2,
sum ||e_n||^2/n   <= 2 * sum_{p in P} 1/p^2 + #P/A.
```

The compiled closed form is

```text
collisionEnergyBoundWide A P T
  = exp(pi) * (T/A + 4)
      * (2 * sum_{p in P} 1/p^2 + #P/A).
```

The leaf includes one-polynomial bounds for `typicalSCollision`, the added
collision family, and `typicalSAdjustedCollision`, followed by
`typicalS_level_leg_le_budget_of_collision_fit_middle_wide`.  Its capstone
input is exactly

```text
8 * collisionEnergyBoundWide A P T <= kappaCollision * budget.
```

## L4-3 — Conjectures wrappers

`TrackCStage5InnerBandAssemblyWide.lean` exports:

- `innerBand_replacement_leg_wide`, whose fit is
  `2 * replacementEnergyBoundWide A (Pl j) (Nl j) T <= kappa * budget`;
- `innerBand_level_leg_of_main_wide`, whose collision fit is
  `8 * collisionEnergyBoundWide A (Pl j) T <= kappaCollision * budget`.

The replacement wrapper's representative inputs are exactly `hqup`, `hq1`,
`hqmin`, and `hqratio`; the proof uses the last three in the collar theorem and
retains `hqup` as the public scale-only interface.

## L4-4 — empty cells

`ScaleOnlyCellRepresentatives.lean` provides the following compiled chain:

```text
quotient_scale_le_cell_scale_of_le
setIntegral_norm_sq_cell_prime_block_le_of_qup
setIntegral_norm_sq_typicalS_le_cell_uniform_add_errors_of_qup
setIntegral_norm_sq_typicalSCellReplacement_le_of_qup
band_energy_level_one_le_of_qup
band_energy_level_one_main_le_budget_of_qup
```

It also provides `qup_of_mem` and the empty-cell-safe selector

```lean
scaleCellRepresentative P N v :=
  if (eadicCell P (2*N) v).Nonempty then
    Nat.ceil (Real.exp (v/(2*N)))
  else 1
```

with:

```text
qup_of_ceil_or_one
one_le_scaleCellRepresentative
scaleCellRepresentative_le_mem
two_mul_scaleCellRepresentative_le
scaleCellRepresentative_ratio_le
```

The last theorem supplies `N*p <= (N+1)*q_v` on occupied cells.  Empty cells
contribute empty sums, while their representative is one.

## L4-5 — exact compiled capstone interface

`band_energy_typicalS_le_of_schedule_sharp_cells_wide` concludes

```text
weighted inner-band energy
  <= (4H/A)^2 * bandBudget c3 eps (Delta/A).
```

Its hypotheses, in declaration order and grouped without omission, are:

1. the two large-values typeclass parameters;
2. `g`, complete multiplicativity, and `||g n|| <= 1`;
3. `A, Delta, H`, positivity of `A,H`, and `Delta <= A`;
4. `Pl, Pu, J`, `J > 0`, primality, `p^2 <= A` for `Pu`, pairwise ordinary
   disjointness, and ordinary/exceptional disjointness;
5. ordinary `Nl,v0l,v1l,ql,alpha`, with `Nl j > 0`, the e-adic cover,
   `hqupl`, `hq1l`, `hqminl`, and `hqratiol`;
6. `K1,K2,T`, `1 <= T`, and `K2+2 <= T`;
7. `c3,eps`, `0 <= c3`, and the three ordinary share functions;
8. the already-assembled ordinary main estimates `hmain`;
9. for every `j<J`,

   ```text
   2 * replacementEnergyBoundWide A (Pl j) (Nl j) T
     <= kappaReplacement j * budget,
   8 * collisionEnergyBoundWide A (Pl j) T
     <= kappaCollision j * budget,
   2*kappaMain j + 2*kappaReplacement j + 2*kappaCollision j
     <= 1/2^(j+1);
   ```

10. exceptional `Nu,v0u,v1u`, its cover, and `qu` with `hqupU`, `hq1U`,
    `hqminU`, `hqratioU`, plus the two legacy quotient guards `hLAU,hLBU`;
11. the measurable nonnegative weight and its `(4H/A)^2` supremum;
12. exceptional prime moment data `PcU`, its lower/upper cell bounds, `ellU`,
    `Vsplit`, `lamU`, and their positivity assumptions;
13. sharp Halász inputs `x0,D,delta0,A0`, their size conditions,
    `NonPretentiousAt g A0 (2A+1)`, and the exact range and strength fits at
    scale `3*(2A+1)` and strength `A0/3`;
14. `DeltaU`, its nonnegativity, and the exact pointwise split

    ```text
    cellHalaszSharpBound x0 D delta0 (A/qu v) ((A+Delta)/qu v)
        Pu [Pl 0]
      + ladderSiftedLogMass (A/qu v) ((A+Delta)/qu v)
          ((List.range (J-1)).map (fun i => Pl (i+1)))
      <= DeltaU v;
    ```

15. the fixed-threshold exceptional per-cell fit `hfitUCell`, verbatim in the
    recut shape with `DeltaU v`, the actual covered-cell cardinality, the
    coefficient square mass, and `primeHighMomentCountCost`;
16. the aggregate exceptional fit

    ```text
    2 * #cells * (sum_v kappaU v) * budget
      + 2 * (2 * replacementEnergyBoundWide A Pu Nu T
        + 2 * (4 * collisionEnergyBoundWide A Pu T))
      <= 1/2^(J+1) * budget.
    ```

The theorem deliberately takes `hmain` as the ordinary-main interface.  L3
can supply level zero through `band_energy_level_one_main_le_budget_of_qup`
and later levels through `innerBand_later_level_main_cells`; this avoids
duplicating L2's arithmetic schedule in the L4 leaf.

The proof establishes

```text
(List.range J).map Pl
  = Pl 0 :: (List.range (J-1)).map (fun i => Pl (i+1))
```

and invokes `norm_typicalS_quot_block_poly_le_sharp_split` through
`norm_cellBlock_poly_le_cellHalaszSharpBound_split_of_top`.  Therefore only
`Pl 0` is charged to inclusion--exclusion.  The tail is exactly the unit-X
`ladderSiftedLogMass`; by its compiled definition the outer sum is over
`ladder.toFinset`.

## Findings and necessary corrections

### 1. The repository MVT normalization differs from the requested display

`intervalIntegral_norm_sq_poly_le_sharp_ratio` bounds a polynomial
`sum c_n/n * e(-log n xi)` by

```text
exp(pi) * (T/A + 2R) * sum ||c_n||^2/n,
```

not by the same factor times `sum ||c_n||^2/n^2`.  The latter statement is
false with this coefficient convention (a one-term polynomial already has
integral size proportional to `T/n^2`).  The implementation proves the
requested `n^-2` mass estimates as separate lemmas and converts them to the
correct harmonic `n^-1` masses before the single MVT application.  This is
why the closed forms contain `E_P/N + #P/A` and
`2*sum 1/p^2 + #P/A`, rather than an additional factor `1/A`.

### 2. Replacement collars require a ratio fact, not just an upper scale

`hqup`, `hq1`, and `hqmin` do not by themselves bound the distance between
`A/p` and `A/q`.  The exact required fact is

```text
N*p <= (N+1)*q.
```

This is available both from genuine cell membership and from the corrected
occupied-cell ceiling selector.  It is exposed as `hqratio` throughout the
wide replacement interfaces.

### 3. The unconditional raw-ceiling supplier is false on empty cells

The requested assertion

```text
ceil(exp(v/(2N))) <= exp((v+1)/(2N))  for every N>=1
```

is false.  For example, `N=2, v=1` asks for `2 <= exp(1/2)`.  The compiled
supplier therefore uses the lower-endpoint ceiling on occupied cells and
`1` on empty cells.  It satisfies the upper-scale, positivity, cutoff,
minimum, and ratio properties needed by the proofs.

## Normalisation record

With the repository coefficient convention, one MVT application at
`B <= 2A` gives the scale-free shapes

```text
replacement: exp(pi) * (T/A + O(1)) * O(E_j/N_j + #P_j/A),
collision:   exp(pi) * (T/A + O(1)) * O(sum_{p in P_j} 1/p^2 + #P_j/A).
```

Thus, when `T/A` is bounded, the replacement condition is of size
`N_j >= constant * E_j/(kappa_j*c3*eps^2)` and the collision condition is of
size `P_j*log P_j >= constant/(kappa_j*c3*eps^2)`, up to the explicit
constants in the compiled envelopes.  This paragraph is accounting only;
no numerology theorem is asserted here.

## Verification

Passed:

```text
lake env lean MoltResearch/Discrepancy/WideLevelErrorLegs.lean
lake env lean MoltResearch/Discrepancy/ScaleOnlyCellRepresentatives.lean
lake env lean TrackCStage5InnerBandAssemblyWide.lean
lake env lean TrackCStage5InnerBandScheduleSharpCellsWide.lean
lake build MoltResearch.DiscrepancyAnalytic Conjectures
./scripts/check_layering.sh
python3 scripts/check_aggregator_coverage.py
```

Aggregator coverage reports 185 modules, 183 reachable, with only the two
pre-existing allowlisted example modules.  The forbidden-token grep over
`MoltResearch/` and `Solutions/` is empty.

The following declarations each report exactly
`[propext, Classical.choice, Quot.sound]` under `#print axioms`:

```text
MoltResearch.typicalSCellReplacement_eq_dirichlet
MoltResearch.typicalSCollision_eq_dirichlet
MoltResearch.Tao2015.band_energy_typicalS_le_of_schedule_sharp_cells_wide
```
