# Track R — VI-9g phase 2: Codex run 7 final report (2026-09-05)

Verbatim final report of Codex run 7 (gpt-5.6-sol, brief `Problems/tao2015_vi9g_phase2_brief.md`),
whose two commits shipped as PR #3688 (VI-9g-2′, VI-9g-3′). Kept in the tree because its
"obstruction" (`hfitPri` forces `A ≤ κc₃ε²·Δ·Pc·log Pc/(32ε'²)` at fixed `Δ`) is the machine-checked
symptom of a defect in the **target Prop**, not in the schedule: `SliceMeanSquareA2` quantifies over
every slice length `J ≤ A`, i.e. for small `J` it asserts a pointwise short-interval bound that
`[mrt]` A.2 (a dyadic average) never claims — see the design report, "The slice quantifier of
`SliceMeanSquareA2` is over-strong (R8)". Paths below are relative to the run's worktree
`moltresearch-wt-codex7`; commit hashes are the run's, before cherry-pick
(`0bf90982 → b65f9b96`, `882f21de → a326efdc`).

---

# Track R VI-9g phase 2 — final report

Branch: `vex/track-r-vi9g-2`

Base: `origin/main` at the start of the run

Run: <https://chatgpt.com/codex/tasks/01a07257-c253-7250-aa98-a2a8dbf00c66>

Result: VI-9g-2' was proved and committed.  VI-9g-3' exposed a fatal
fixed-epsilon scale obstruction in `hfitPri`, proved the obstruction in Lean,
and was committed as the requested stop artifact.  In accordance with the
brief's stop rule, A2-IV-3, A2-V-1--4, `sliceMeanSquareA2`, and its audit pin
were not entered.

## Commit `0bf909820e7b35484c96d8e92bade5574e5d9c6b`

Subject: `Track R: sharp exceptional schedule on the recut capstone (#3044, VI-9g-2')`

File:
`Conjectures/C0002_erdos_discrepancy/src/TrackCStage5InnerBandScheduleSharp.lean`

### Statements

```lean
theorem nonPretentiousAt_scale_up_of_norm_le_one {g : ℕ → ℂ}
    (hg : ∀ n, ‖g n‖ ≤ 1) {A A' c : ℝ} {x z : ℕ}
    (h : NonPretentiousAt g A x) (hxz : x ≤ z) (hzc : (z : ℝ) ≤ c * x)
    (hA'0 : 0 ≤ A') (hc1 : 1 ≤ c) (hA' : A' * c ≤ A) :
    NonPretentiousAt g A' z
```

```lean
theorem sum_norm_cellBlockCoeff_sq_div_sq_le_two_div
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A B : ℕ) (P : Finset ℕ) (rest : List (Finset ℕ)) (q : ℕ)
    (hAq : 1 ≤ A / q) :
    (∑ n ∈ Finset.Icc 1 (B / q),
        ‖cellBlockCoeff g A B P rest q n‖ ^ 2 / (n : ℝ) ^ 2)
      ≤ 2 / (((A / q + 1 : ℕ) : ℝ))
```

```lean
theorem sum_norm_sq_div_prime_sq_le_card_div
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (Y : Finset ℕ) (Pc : ℕ) (hPc : 1 ≤ Pc)
    (hlo : ∀ p ∈ Y, Pc < p) :
    ∑ p ∈ Y, ‖g p‖ ^ 2 / (p : ℝ) ^ 2
      ≤ (Y.card : ℝ) / (Pc : ℝ) ^ 2
```

```lean
noncomputable def sharpExceptionalCoverBound
    (P : ℕ → Finset ℕ) (N v0 v1 : ℕ → ℕ) (alpha : ℕ → ℝ)
    (J : ℕ) (Panchor coverEll : ℕ → ℕ) (T : ℝ)
    (coverLam : ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.Ico (v0 (J - 1)) (v1 (J - 1) + 1),
    2 * primeHighMomentCountCost (Panchor r) (coverEll r)
      (eadicCell (P (J - 1)) (2 * N (J - 1)) r) T
      (Real.exp (-(alpha (J - 1) * (r : ℝ) /
        ((2 * N (J - 1) : ℕ) : ℝ)))) (coverLam r)
```

The two capstone statements retain the complete schedule hypothesis lists from
the source file.  Their exact conclusions and the new sharp inputs are:

```lean
theorem band_energy_typicalS_le_of_levels_recut
    [HalaszLargeValuesAssumption] [PrimeLargeValuesAssumption]
    (... ordinary-level, replacement, collision, exceptional-cover,
         pointwise-cell-bound, and fixed-threshold fit hypotheses ...) :
    (∫ xi in {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂},
        ‖∑ m ∈ typicalS A (A + Delta) (innerBandLevels Pl Pu J),
            (g m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2 * w xi)
      ≤ bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))
```

```lean
theorem band_energy_typicalS_le_of_schedule_sharp
    [HalaszLargeValuesAssumption] [PrimeLargeValuesAssumption]
    (... the ordinary schedule hypotheses of
         band_energy_typicalS_le_of_schedule',
      hNPtop : NonPretentiousAt g A₀ (2 * A + 1),
      hrangeSharp :
        2 * Real.pi * T
            + 2 * Real.pi * (((halaszM (3 * (2 * A + 1)) : ℕ) : ℝ) + 1)
          ≤ (A₀ / 3) * ((3 * (2 * A + 1) : ℕ) : ℝ),
      hstrengthSharp :
        2 * D ≤ A₀ / 3
          - 2 * (Real.log (Real.log ((3 * (2 * A + 1) : ℕ) : ℝ))
            - Real.log (Real.log (x0 : ℝ)) + 12),
      hDeltaU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
        cellHalaszSharpBound x0 D delta₀ (A / qu v) ((A + Delta) / qu v)
            Pu ((List.range J).map Pl) ≤ DeltaU v,
      hfitInt : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
        2 * exceptionalSplitThreshold A ^ 2
            * (64 * ((((A + Delta) / qu v : ℕ) : ℝ)
                + sharpExceptionalCoverBound Pl Nl v₀l v₁l
                    innerBandScheduleAlpha J PanchorU coverEllU T coverLamU
                    * Real.sqrt T)
              * (Real.log (2 * T) + 1)
              * (2 / (((A / qu v + 1 : ℕ) : ℝ))))
          ≤ kappaU v / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)),
      hfitPri : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
        2 * (DeltaU v) ^ 2
            * ((64 * ((eadicCell Pu (2 * Nu) v).card : ℝ)
                  / (PcU v : ℝ) ^ 2 * (PcU v : ℝ) / Real.log (PcU v))
              * (1 + primeHighMomentCountCost (PcU v) (ellU v)
                  (eadicCell Pu (2 * Nu) v) T
                  (exceptionalSplitThreshold A) (lamU v)
                * Real.exp (-(Real.log (PcU v) /
                  (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
                * (Real.log (2 * T)) ^ 2))
          ≤ kappaU v / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)),
      ... exceptional replacement, collision, and share hypotheses ...) :
    (∫ xi in {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂},
        ‖∑ m ∈ typicalS A (A + Delta) (innerBandLevels Pl Pu J),
            (g m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2 * w xi)
      ≤ (4 * (H : ℝ) / (A : ℝ)) ^ 2
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))
```

The canonical, fully expanded declarations are in the source at lines 139 and
442.  The elisions above cover only the inherited ordinary schedule arguments;
the displayed new sharp hypotheses and conclusions are verbatim.

### Finding

The recut capstone closes from two independent half-budget hypotheses.  The
proof internally supplies:

- `Vsplit = exceptionalSplitThreshold A`;
- the covered-cell cardinality via
  `card_cellsMeeting_exceptional_le_highMomentCost`;
- coefficient harmonic mass at most `2 / (A/q + 1)`;
- prime square mass at most `#cell / Pc^2`;
- the pointwise sharp cell bound from the top scale `3(2A+1)`;
- exact addition of `hfitInt` and `hfitPri` into the fixed-threshold recut fit.

The existing `nonPretentiousAt_scale_up` requires a unimodular function, while
`SliceMeanSquareA2` quantifies merely 1-bounded functions.  The new scale-up
lemma closes that interface mismatch directly from nonnegativity of the added
prime summands.

### Verification

- `lake env lean .../TrackCStage5InnerBandScheduleSharp.lean`: exit `0`.
- `lake build Conjectures.C0002_erdos_discrepancy.src.TrackCStage5InnerBandScheduleSharp`:
  exit `0`.
- `forbid_sorry`, `forbid_axiom_unsafe`, `check_layering`, and aggregator
  coverage before commit: all exit `0`.

## Commit `882f21decdeb07befe5ac7599ec63907efea8f2b`

Subject: `Track R: expose the fixed-epsilon prime-fit obstruction (#3044, VI-9g-3')`

File:
`Conjectures/C0002_erdos_discrepancy/src/TrackCStage5InnerBandScheduleSharpNumerology.lean`

### Statements

```lean
theorem cellHalaszSharpBound_ge_eps_div_eight
    (epsilon' : ℝ) (hepsilon' : 0 < epsilon')
    (x0 Aq Bq : ℕ) (hx0 : cellHalaszThreshold ≤ x0)
    (hx0Aq : x0 ≤ Aq) (hAqBq : Aq ≤ Bq)
    (D : ℝ) (hD : 0 ≤ D) (P : Finset ℕ) (rest : List (Finset ℕ)) :
    epsilon' / 8 ≤
      cellHalaszSharpBound x0 D (epsilon' / (8 * Real.exp 1)) Aq Bq P rest
```

```lean
theorem exceptional_prime_term_ge_fixed_floor
    (epsilon' DeltaU cellCard Pc logPc Gamma : ℝ)
    (hepsilon' : 0 < epsilon') (hDeltaU : epsilon' / 8 ≤ DeltaU)
    (hcellCard : 1 ≤ cellCard) (hPc : 0 < Pc) (hlogPc : 0 < logPc)
    (hGamma : 0 ≤ Gamma) :
    128 * (epsilon' / 8) ^ 2 / (Pc * logPc) ≤
      2 * DeltaU ^ 2 * (64 * (cellCard / Pc ^ 2) * Pc / logPc) *
        (1 + Gamma)
```

```lean
theorem fixed_floor_prime_fit_forces_scale_bound
    (A Delta Pc logPc kappa c3 eps epsilon' : ℝ)
    (hA : 0 < A) (hPc : 0 < Pc) (hlogPc : 0 < logPc)
    (hepsilon' : 0 < epsilon')
    (hfit : 128 * (epsilon' / 8) ^ 2 / (Pc * logPc) ≤
      (kappa / 2) * bandBudget c3 eps (Delta / A)) :
    A ≤ kappa * c3 * eps ^ 2 * Delta * Pc * logPc /
      (32 * epsilon' ^ 2)
```

```lean
theorem sharp_exceptional_prime_fit_forces_scale_bound
    (A Delta DeltaU cellCard Pc logPc Gamma kappa c3 eps epsilon' : ℝ)
    (hA : 0 < A) (hPc : 0 < Pc) (hlogPc : 0 < logPc)
    (hepsilon' : 0 < epsilon') (hDeltaU : epsilon' / 8 ≤ DeltaU)
    (hcellCard : 1 ≤ cellCard) (hGamma : 0 ≤ Gamma)
    (hfitPri :
      2 * DeltaU ^ 2 * (64 * (cellCard / Pc ^ 2) * Pc / logPc) *
          (1 + Gamma)
        ≤ (kappa / 2) * bandBudget c3 eps (Delta / A)) :
    A ≤ kappa * c3 * eps ^ 2 * Delta * Pc * logPc /
      (32 * epsilon' ^ 2)
```

```lean
theorem not_sharp_exceptional_prime_fit_of_scale_growth
    (A Delta DeltaU cellCard Pc logPc Gamma kappa c3 eps epsilon' : ℝ)
    (hA : 0 < A) (hPc : 0 < Pc) (hlogPc : 0 < logPc)
    (hepsilon' : 0 < epsilon') (hDeltaU : epsilon' / 8 ≤ DeltaU)
    (hcellCard : 1 ≤ cellCard) (hGamma : 0 ≤ Gamma)
    (hgrowth : kappa * c3 * eps ^ 2 * Delta * Pc * logPc <
      32 * epsilon' ^ 2 * A) :
    ¬ (2 * DeltaU ^ 2 * (64 * (cellCard / Pc ^ 2) * Pc / logPc) *
          (1 + Gamma)
        ≤ (kappa / 2) * bandBudget c3 eps (Delta / A))
```

### Finding and exact failed margin

For `delta0 = epsilon'/(8e)`, the `n1 = 1` long-quotient summand in
`sharpRamareCost` contains

```text
2 * (e * Bq * delta0) / (Aq + 1) >= epsilon'/8
```

when `x0 <= Aq <= Bq`.  Inclusion--exclusion only enlarges this positive
quantity.  Thus any explicit upper envelope `DeltaU` for the sharp cell bound
has `DeltaU >= epsilon'/8`.

For a nonempty cell and `Gamma >= 0`, `hfitPri` therefore requires

```text
128 * (epsilon'/8)^2 / (Pc * log Pc)
  <= (kappa/2) * (c3 * eps^2 * (Delta/A) / 8),
```

equivalently, with all constants retained,

```text
A <= kappa * c3 * eps^2 * Delta * Pc * log Pc / (32 * epsilon'^2).
```

In the A.2 quantifier order, `eps`, `epsilon'`, and the window-dependent
`Delta` are fixed before the universally quantified ambient scale `A`.  The
phase-2 proposal has

```text
Pc <= Q_U = ceil(exp((C/eps^3) * (log A)^(49/50))).
```

Hence `Pc * log Pc = exp(o(log A))`, and the forced upper bound is `A^o(1)`;
it is false for every sufficiently large `A`.  Increasing the moment order to
make `Gamma <= 1` cannot alter the floor, since the proof used only
`Gamma >= 0`.

### Verification

- `lake env lean .../TrackCStage5InnerBandScheduleSharpNumerology.lean`:
  exit `0`.
- `lake build Conjectures.C0002_erdos_discrepancy.src.TrackCStage5InnerBandScheduleSharpNumerology`:
  exit `0`.
- `#print axioms band_energy_typicalS_le_of_schedule_sharp`: only `propext`,
  `Classical.choice`, and `Quot.sound` reported; exit `0`.
- `#print axioms not_sharp_exceptional_prime_fit_of_scale_growth`: only
  `propext`, `Classical.choice`, and `Quot.sound` reported; exit `0`.

## Accounting discrepancies found

1. The proposed fixed-epsilon sharp envelope does not decay with the relative
   block length.  Its smoothing term gives the formal lower bound
   `cellHalaszSharpBound >= epsilon'/8` on every long quotient.

2. The exceptional prime fit is compared with a budget containing `Delta/A`.
   For the A.2 consumer, the window and therefore `Delta` are fixed before
   `A`, so this budget decays as `1/A`.  The proposed prime scale is subpower
   in `A`, which cannot compensate for the fixed envelope floor.

3. The suggested first moment `ell = 1` also leaves the term
   `(T+1)/P_U` inside `primeHighMomentCountCost`.  When `T` may be `A` and
   `P_U = exp((log A)^(49/50))`, this is not bounded by a polylogarithm.  An
   adaptive moment of order about `log T/log P_U` would be required, but that
   repair is moot until discrepancy 1 is fixed.

4. The old upward scale bridge is restricted to `Unimodular g`, whereas the
   target Prop supplies only `forall n, norm (g n) <= 1`.  VI-9g-2' adds and
   uses the correct 1-bounded bridge.

5. The inherited schedule still asks for `eps <= Delta/A`.  If its `eps` is
   instantiated by the fixed A.2 accuracy parameter as the phase brief
   prescribes, this also fails for fixed window length and arbitrarily large
   `A`.  A later repair must retain the literal `Delta/A` factor in the
   replacement-leg fit or explicitly reparameterize that schedule lemma.

6. The phase-2 proposal defines `P_U` and `Q_U` from the ambient block scale
   `A`, while `SliceMeanSquareA2` chooses `levels` before its universal
   `forall A`.  Therefore that varying exceptional level cannot directly
   instantiate the target Prop.  Holding the level fixed makes the prime-fit
   obstruction stronger; a repair also needs a level construction uniform in
   all later block scales.

## Work left undone and exact blocker

VI-9g-3' cannot be discharged as stated.  The exact blocker is the implication
proved in `sharp_exceptional_prime_fit_forces_scale_bound`:

```text
hfitPri and DeltaU >= epsilon'/8 and #cell >= 1 and Gamma >= 0
  imply
A <= kappa*c3*eps^2*Delta*Pc*log(Pc)/(32*epsilon'^2).
```

The proposed `Pc <= exp(O((log A)^(49/50)))` violates this necessary condition
for sufficiently large `A` at fixed window length.  A viable next design must
replace the envelope by one with a trivial relative-length fallback, for
example a positive version of
`min(cellHalaszSharpBound, O(Delta/A))`, or change the recut capstone so the
actual trivial cell-polynomial bound can be used on these large ambient
scales.  Allowing the Halasz strength to depend on `A` is not compatible with
the current `SliceMeanSquareA2` quantifier order and its fixed `A0`.

Per the explicit stop rule, these dependent units were not entered:

- A2-IV-3;
- A2-V-1, A2-V-2, A2-V-3, A2-V-4;
- `theorem sliceMeanSquareA2 : SliceMeanSquareA2`;
- the `TrackCAxiomAudit.lean` pin.

`theorem sliceMeanSquareA2 : SliceMeanSquareA2` was **not proved** and was
**not audit-pinned**.

## Final verification

- `./scripts/forbid_sorry.sh`: exit `0`.
- `./scripts/forbid_axiom_unsafe.sh`: exit `0`.
- `./scripts/check_layering.sh`: exit `0`.
- `python3 scripts/check_aggregator_coverage.py`: exit `0`; 180 modules, 178
  reachable, with the two pre-existing allowlisted compile-only modules.
- `python3 scripts/check_interfaces.py`: exit `0`; warning mode reported seven
  pre-existing documentation findings.
- `lake build MoltResearch.DiscrepancyAnalytic Conjectures`: exit `0`; 8183
  jobs.

The worktree is clean except for this required, intentionally uncommitted
`CODEX_REPORT.md`.
