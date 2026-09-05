# Track R — R8: Codex run 8 final report (2026-09-05)

Verbatim final report of Codex run 8 (gpt-5.6-sol, brief `Problems/tao2015_r8_brief.md`), whose seven
commits shipped as PR #3690. R8 restricts the slice quantifier of `SliceMeanSquareA2` to `A/2 ≤ J ≤ A`
(the honest transcription of `[mrt]` A.2's dyadic average; see the design report,
"The slice quantifier of `SliceMeanSquareA2` is over-strong (R8)"), re-proves R6-5/R6-6c with the
≤ 4-point leftover priced trivially (conclusion `4εh` unchanged, new hypothesis `2 ≤ ε·A₁`), threads the
guard and the scale condition through R6-6d, R6-8 and R7, and records the half-dyadic prime-fit
condition. The audit pins of `edp_of_sliceMeanSquareA2` and `theorem18_of_sliceMeanSquareA2` are
byte-for-byte unchanged (`[propext, Classical.choice, Quot.sound]`). One deviation from the brief, recorded
below: the wrapper cannot merely add `256Q/ε` to its own threshold, because the Prop chooses its own `A₀`;
`exists_wrapper_params` takes `max A₀ (256Q/ε)` and transports the density and mean-square clauses to
the larger threshold. Commit hashes are the run's, before cherry-pick.

---

# Track R — R8 final report

Branch: `vex/track-r-r8`

Base: `86539ae118f46b0f6919cc173b08f4fc04b9757b` (`origin/main`)

Head: `88d064c550126137b8def146f83010569092ccb2`

Codex run: `https://chatgpt.com/codex/tasks/01a0728c-2fc7-7140-bdaa-b446c027eb37`

## Outcome

R8 is complete. `SliceMeanSquareA2` now asks for mean square only on honest slices
`A / 2 ≤ J ≤ A`. The R6 analytic nucleus handles the at-most-four-point overshoot in
the reindexed interval trivially, and the scale condition `2 ≤ ε' A₀` is threaded
through R6-8 and R7. The EDP consumers and all audit guards compile unchanged. No
interface class was edited or added, and the R8 diff does not reference
`FarRegimeRepulsionAssumption`.

## Commits and declarations

### `4cf84519` — Track R: use the honest A2 slice quantifier (#3044, R8-1)

Finding: the old universal `J ≤ A` clause included `J = 1`, imposing a pointwise
short-interval assertion not supplied by `[mrt]` A.2. The only change to the target
Prop is the additional lower guard `A / 2 ≤ J`.

Full changed definition:

```lean
def SliceMeanSquareA2 : Prop :=
  ∀ (εc : ℝ), 0 < εc → ∀ (B : ℕ) (C : ℝ), 0 < C →
    ∃ (h₁ : ℕ) (C₁ : ℝ) (k : ℕ), 0 < C₁ ∧
    ∀ (ε : ℝ), 0 < ε → ∀ h : ℕ, h₁ ≤ h → C₁ / ε ^ k ≤ h →
      ∃ (levels : List (Finset ℕ)) (A₀ : ℝ), 1 ≤ A₀ ∧
        (∀ P ∈ levels, ∀ p ∈ P, p.Prime) ∧
        (∀ P ∈ levels, ∀ p ∈ P, C * Real.log h ^ B < p) ∧
        (∀ A : ℕ, A₀ ≤ A →
          ∑ n ∈ (Finset.Ioc A (2 * A)).filter (fun n => ¬ HasFactorInAll levels n), (1:ℝ)/n
            ≤ εc * ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n) ∧
        (∀ A : ℕ, A₀ ≤ A →
          ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → (∀ n, ‖g n‖ ≤ 1) → g 1 = 1 →
            NonPretentiousAt g A₀ (2 * A + 1) →
            ∀ J : ℕ, A / 2 ≤ J → J ≤ A →
              ∑ n ∈ Finset.Ioc A (A + J),
                ‖∑ m ∈ (Finset.Ioc n (n + h)).filter (HasFactorInAll levels), g m‖^2 / n
                ≤ ε^2 * (h : ℝ)^2 * ∑ n ∈ Finset.Ioc A (A + J), (1:ℝ)/n)
```

Verification: `lake env lean Conjectures/C0002_erdos_discrepancy/src/TrackCStage5MajorArcA2.lean` — exit 0.

### `997bfa80` — Track R: reprice almost-dyadic A2 blocks (#3044, R8-2)

Finding: Cauchy–Schwarz applies to `(a, min b (2a)]`; if `b > 2a`, `hb4` leaves at
most four terms, each bounded by `h/(2a+1)` using `W ≤ h`.

Full changed theorem statement:

```lean
theorem logavg_le_of_meanSquare_dyadic (W : ℕ → ℝ) (hW : ∀ n, 0 ≤ W n)
    (ε h : ℝ) (hε : 0 ≤ ε) (hh : 0 ≤ h) (hWh : ∀ n, W n ≤ h) (A₀ N : ℕ)
    (hA2 : ∀ A J : ℕ, A₀ ≤ A → A / 2 ≤ J → J ≤ A → A + J ≤ N →
      ∑ n ∈ Finset.Ioc A (A + J), (W n)^2 / n
        ≤ ε^2 * h^2 * ∑ n ∈ Finset.Ioc A (A + J), (1:ℝ)/n)
    (a b : ℕ) (ha : A₀ ≤ a) (ha1 : 1 ≤ a) (hb_lo : 3 * a ≤ 2 * b)
    (hb4 : b ≤ 2 * a + 4) (hbN : b ≤ N) :
    ∑ n ∈ Finset.Ioc a b, W n / n
      ≤ ε * h * ∑ n ∈ Finset.Ioc a b, (1:ℝ)/n
        + 4 * h / ((2 * a + 1 : ℕ) : ℝ)
```

Verification: `lake env lean MoltResearch/Discrepancy/MajorArcAssembly.lean` — exit 0.

## Verification summary

Commit order was R8-1 through R8-7:

1. `4cf84519`
2. `997bfa80`
3. `e30075cd`
4. `f913f687`
5. `704b824b`
6. `3fb12df8`
7. `88d064c5`

All requested checks completed successfully:

| Command | Exit | Result |
|---|---:|---|
| `lake build MoltResearch.Discrepancy.MajorArcAssembly` | 0 | 7,993 jobs |
| `lake build Conjectures.C0002_erdos_discrepancy.src.TrackCStage5MajorArcA2` | 0 | 8,019 jobs |
| `lake build Conjectures.C0002_erdos_discrepancy.src.TrackCStage5MajorArcMR` | 0 | 8,077 jobs |
| `lake build Conjectures` | 0 | 8,183 jobs; EDP and audit modules built |
| `lake env lean Conjectures/C0002_erdos_discrepancy/src/TrackCAxiomAudit.lean` | 0 | all audit guards accepted |
| `./scripts/forbid_sorry.sh` | 0 | clean |
| `./scripts/forbid_axiom_unsafe.sh` | 0 | clean |
| `./scripts/check_layering.sh` | 0 | clean |
| `python3 scripts/check_aggregator_coverage.py` | 0 | 180 modules; only the two allowlisted examples are unreachable |
| `python3 scripts/check_interfaces.py` | 0 | 16 existing interfaces; seven pre-existing documentation warnings |
| `lake build MoltResearch.DiscrepancyAnalytic Conjectures` | 0 | 8,183 jobs |
| `git diff --check origin/main..HEAD` | 0 | clean |

The interface checker’s seven warnings are the existing missing-citation/source-list
findings for `Stage2Assumption`, `LittlewoodLBoundAssumption`,
`MatomakiRadziwillAssumption`, `PrimeBlockMajorArcAssumption`, and
`PrimeQuadrupleCountAssumption`; R8 did not edit any of these interfaces.

## Accounting discrepancies found

1. **The displayed R6-6c overshoot comparison in the brief is false.** The step
   `4h/(2a+1) ≤ 2h/(a+1)` (equivalently the displayed coefficient-scaled version)
   fails for every `h > 0`, since cross-multiplication would require
   `4a + 4 ≤ 4a + 2`. For example, at `a = h = 1` the two sides are `4/3` and `1`.
   The proved route is
   `4h/(2a+1) ≤ 2h/a ≤ εh`, using `a > 0` and `2 ≤ εa`. This yields the requested
   unchanged conclusion `≤ 4(εh)`.

2. **The final wrapper summand alone does not establish the internal scale premise.**
   The A.2 Prop chooses its own threshold `M`; adding `256Q/ε` only to the later
   interface threshold does not prove `2 ≤ (ε/(128Q))M`, which R6-8 needs. The
   minimal valid plumbing raises the returned A.2 threshold itself to
   `M' = max M (256Q/ε)`, restricts density to `A ≥ M'`, and transports the
   mean-square clause from non-pretentiousness at strength `M'` down to strength
   `M`. The external threshold retains the prescribed `+ 256Q/ε` term.

No other statement deviation from the R8 brief was required.

## Work left undone and exact blocker

No requested R8 work is left undone, and there is no blocking Lean goal. The later
A2-IV producer/discharge campaign remains outside this refactor’s scope. R8 supplies
that campaign with the intended fixed-ratio hypothesis `J/A ≥ 1/2` and records its
fixed prime-fit condition in the sharp numerology module.

## Axiom audit: before and after

The temporary check file imported `TrackCStage5MajorArcEDP` and printed the two
requested endpoint declarations. Byte-for-byte comparison of the before and after
logs (`cmp`) exited 0.

Before:

```text
'MoltResearch.Tao2015.edp_of_sliceMeanSquareA2' depends on axioms: [propext, Classical.choice, Quot.sound]
'MoltResearch.Tao2015.theorem18_of_sliceMeanSquareA2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

After:

```text
'MoltResearch.Tao2015.edp_of_sliceMeanSquareA2' depends on axioms: [propext, Classical.choice, Quot.sound]
'MoltResearch.Tao2015.theorem18_of_sliceMeanSquareA2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`TrackCAxiomAudit.lean` itself was not edited and independently typechecked with exit
0; its before/after output logs are also byte-for-byte identical (`cmp` exit 0), so
its three pinned major-arc/EDP guards retain their pre-refactor axiom sets.

## Commits and declarations (continued)

### `3fb12df8` — Track R: thread the honest A2 scale through R7 (#3044, R8-6)

Finding: the threshold returned by the original Prop need not itself satisfy
`2 ≤ (ε/(128Q))A₀`. Merely enlarging the final wrapper threshold cannot repair that
internal premise. The parameter wrapper therefore replaces the Prop threshold by
`max A₀ (256Q/ε)`, transports density to the larger threshold, and transports mean
square using the fact that non-pretentiousness at the larger strength implies it at
the original strength. The final interface threshold also contains the prescribed
summand `256Q/ε`.

Full new helper and changed theorem statements:

```lean
theorem nonPretentiousAt_of_le_strength {g : ℕ → ℂ} {A A' : ℝ} {x : ℕ}
    (hAA' : A ≤ A') (h : NonPretentiousAt g A' x) : NonPretentiousAt g A x

theorem good_block_total_le
    (levels : List (Finset ℕ)) (hlv : ∀ P ∈ levels, ∀ p ∈ P, p.Prime)
    (A₀ : ℝ) (hA₀1 : 1 ≤ A₀) (h₀ : ℕ) (ε' εc : ℝ) (hε' : 0 ≤ ε') (hεc : 0 ≤ εc)
    (hε'A₀ : 2 ≤ ε' * A₀)
    (hdens : ∀ A : ℕ, A₀ ≤ A →
      ∑ n ∈ (Finset.Ioc A (2 * A)).filter (fun n => ¬ HasFactorInAll levels n), (1:ℝ)/n
        ≤ εc * ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n)
    (hms : ∀ A : ℕ, A₀ ≤ A →
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → (∀ n, ‖g n‖ ≤ 1) → g 1 = 1 →
        NonPretentiousAt g A₀ (2 * A + 1) →
        ∀ J : ℕ, A / 2 ≤ J → J ≤ A →
          ∑ n ∈ Finset.Ioc A (A + J),
            ‖∑ m ∈ (Finset.Ioc n (n + h₀)).filter (HasFactorInAll levels), g m‖^2 / n
            ≤ ε'^2 * (h₀ : ℝ)^2 * ∑ n ∈ Finset.Ioc A (A + J), (1:ℝ)/n)
    (g : ℕ → ℂ) (hg : CompletelyMultiplicativeC g) (hgu : Unimodular g)
    (q : ℕ) (hq : 0 < q) (hql : ∀ P ∈ levels, ∀ p ∈ P, ¬ p ∣ q) (a : ℤ) (α : ℝ)
    (A H : ℕ) (hh₀ : 0 < h₀) (h2h₀ : 2 * h₀ ≤ H) (hA : 6 * q * H ≤ A)
    (hA7 : 7 * q ^ 2 ≤ A) (hA₀q : ⌈A₀⌉₊ + 1 ≤ A / q)
    (hnp : NonPretentiousAt g (q * A₀ + 26) (6 * A + 1)) :
    ∑ n ∈ Finset.Ioc A (2 * A),
        ‖∑ m ∈ Finset.Ioc n (n + H),
          g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ))‖ / ((H : ℝ) * n)
      ≤ (16 * q * ε' + q * h₀ / H + 4 * Real.pi * q^2 * |α - (a : ℝ) / q| * h₀ + 6 * εc)
          * ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n

theorem exists_wrapper_params (hA2 : SliceMeanSquareA2) (ε C : ℝ) (B : ℕ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 < C) :
    ∃ H₀ : ℕ, ∀ H : ℕ, H₀ ≤ H →
      ∃ (Q : ℝ) (h₀ : ℕ) (levels : List (Finset ℕ)) (A₀ : ℝ),
        1 ≤ Q ∧ C * Real.log H ^ B ≤ Q ∧ 1 ≤ A₀ ∧
        2 ≤ (ε / (128 * Q)) * A₀ ∧ 0 < h₀ ∧ 2 * h₀ ≤ H ∧
        (h₀ : ℝ) ≤ ε * H / (64 * Real.pi * Q ^ 2) ∧
        (∀ P ∈ levels, ∀ p ∈ P, p.Prime) ∧
        (∀ P ∈ levels, ∀ p ∈ P, Q < p) ∧
        (∀ A : ℕ, A₀ ≤ A →
          ∑ n ∈ (Finset.Ioc A (2 * A)).filter (fun n => ¬ HasFactorInAll levels n), (1:ℝ)/n
            ≤ (ε / 48) * ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n) ∧
        (∀ A : ℕ, A₀ ≤ A →
          ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → (∀ n, ‖g n‖ ≤ 1) → g 1 = 1 →
            NonPretentiousAt g A₀ (2 * A + 1) →
            ∀ J : ℕ, A / 2 ≤ J → J ≤ A →
              ∑ n ∈ Finset.Ioc A (A + J),
                ‖∑ m ∈ (Finset.Ioc n (n + h₀)).filter (HasFactorInAll levels), g m‖^2 / n
                ≤ (ε / (128 * Q))^2 * (h₀ : ℝ)^2
                    * ∑ n ∈ Finset.Ioc A (A + J), (1:ℝ)/n)
```

```lean
theorem block_total_le_trichotomy
    (levels : List (Finset ℕ)) (hlv : ∀ P ∈ levels, ∀ p ∈ P, p.Prime)
    (A₀ : ℝ) (hA₀1 : 1 ≤ A₀) (h₀ H : ℕ) (Q ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hQ1 : 1 ≤ Q)
    (hεA₀ : 2 ≤ (ε / (128 * Q)) * A₀)
    (hh₀ : 0 < h₀) (h2h₀ : 2 * h₀ ≤ H)
    (hh₀Q : (h₀ : ℝ) ≤ ε * H / (64 * Real.pi * Q ^ 2))
    (hdens : ∀ A : ℕ, A₀ ≤ A →
      ∑ n ∈ (Finset.Ioc A (2 * A)).filter (fun n => ¬ HasFactorInAll levels n), (1:ℝ)/n
        ≤ (ε / 48) * ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n)
    (hms : ∀ A : ℕ, A₀ ≤ A →
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → (∀ n, ‖g n‖ ≤ 1) → g 1 = 1 →
        NonPretentiousAt g A₀ (2 * A + 1) →
        ∀ J : ℕ, A / 2 ≤ J → J ≤ A →
          ∑ n ∈ Finset.Ioc A (A + J),
            ‖∑ m ∈ (Finset.Ioc n (n + h₀)).filter (HasFactorInAll levels), g m‖^2 / n
            ≤ (ε / (128 * Q))^2 * (h₀ : ℝ)^2
                * ∑ n ∈ Finset.Ioc A (A + J), (1:ℝ)/n)
    (g : ℕ → ℂ) (hg : CompletelyMultiplicativeC g) (hgu : Unimodular g)
    (q : ℕ) (hq : 0 < q) (hqQ : (q : ℝ) ≤ Q)
    (hql : ∀ P ∈ levels, ∀ p ∈ P, ¬ p ∣ q)
    (a : ℤ) (α : ℝ) (harc : |α - (a : ℝ) / q| ≤ Q / ((H : ℝ) * q))
    (x' : ℕ) (hx' : 1 ≤ x') (A : ℝ) (hnp : NonPretentiousAt g A x')
    (hA8 : Q * A₀ + 50 + 2 * Real.log (64 / ε) ≤ A / 8)
    (L₀ X : ℕ) (hL₀ : Q * (6 * H + 7 * Q + A₀ + 2) ≤ L₀)
    (hX : (8 * (x' : ℝ)) ^ (ε / 64) ≤ X)
    (Ab : ℕ) (hAb1 : 1 ≤ Ab) (hAbx : Ab ≤ x') :
    ∑ n ∈ Finset.Ioc Ab (2 * Ab),
        ‖∑ m ∈ Finset.Ioc n (n + H),
          g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ))‖ / ((H : ℝ) * n)
      ≤ (if Ab < L₀ then ∑ n ∈ Finset.Ioc Ab (2 * Ab), (1:ℝ)/n else 0)
        + (if Ab < X then ∑ n ∈ Finset.Ioc Ab (2 * Ab), (1:ℝ)/n else 0)
        + (21 / 64) * ε * ∑ n ∈ Finset.Ioc Ab (2 * Ab), (1:ℝ)/n

theorem majorArc_bound_of_A2_of_le_one (hA2 : SliceMeanSquareA2) (ε C : ℝ) (B : ℕ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 < C) :
    ∃ H₀ : ℕ, ∀ H : ℕ, H₀ ≤ H →
      ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A → 1 ≤ A →
        ∀ x w : ℝ, A ≤ w → w ≤ x →
          ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → Unimodular g →
            NonPretentiousAt g A ⌈x⌉₊ →
            ∀ α : ℝ, ∀ a : ℤ, ∀ q : ℕ, 1 ≤ q →
              (q : ℝ) ≤ C * Real.log H ^ B →
              |α - (a : ℝ) / (q : ℝ)| ≤ C * Real.log H ^ B / ((H : ℝ) * (q : ℝ)) →
              ∑ n ∈ Finset.Ioc ⌊x / w⌋₊ ⌊x⌋₊,
                  ‖∑ j ∈ Finset.Icc 1 H,
                      g (n + j) * Complex.exp
                        (2 * Real.pi * Complex.I * (j : ℂ) * (α : ℂ))‖
                    / ((H : ℝ) * (n : ℝ))
                ≤ ε * Real.log w

theorem matomakiRadziwillMajorArc_of_A2 (hA2 : SliceMeanSquareA2) :
    MatomakiRadziwillMajorArcAssumption
```

Verification:

- `lake env lean Conjectures/C0002_erdos_discrepancy/src/TrackCStage5MajorArcMR.lean` — exit 0.
- `lake build Conjectures.C0002_erdos_discrepancy.src.TrackCStage5MajorArcMR` — exit 0; 8,077 jobs.

### `88d064c5` — Track R: record the half-dyadic prime-fit condition (#3044, R8-7)

Finding: the numerology documentation now records that `J ≥ A/2` turns the forced
fixed-length bound into the fixed condition
`ε'² ≤ κ c₃ ε² Pc log(Pc) / 64`; no theorem statement changed.

Verification: `lake env lean Conjectures/C0002_erdos_discrepancy/src/TrackCStage5InnerBandScheduleSharpNumerology.lean` — exit 0.

### `f913f687` — Track R: thread half-dyadic A2 through restricted blocks (#3044, R8-4)

Finding: the restricted window function has the needed pointwise bound because
`norm_filter_block_le_card` bounds a filtered interval of length `h₀` by `h₀` when
the coefficients `χ · g` are one-bounded. This supplies `hWh` to R6-6c, while
`2 ≤ ε'A₁` supplies the overshoot scale.

Full changed theorem statement:

```lean
theorem sum_restricted_window_logavg_le_of_meanSquare (g : ℕ → ℂ)
    (hg : CompletelyMultiplicativeC g) (hb : ∀ m, ‖g m‖ ≤ 1)
    (levels : List (Finset ℕ)) (hlv : ∀ P ∈ levels, ∀ p ∈ P, p.Prime)
    (q : ℕ) (hq : 0 < q) (hql : ∀ P ∈ levels, ∀ p ∈ P, ¬ p ∣ q) (a : ℤ) (δ : ℝ)
    (A H h₀ : ℕ) (hh₀ : 0 < h₀) (h2h₀ : 2 * h₀ ≤ H) (hA : 6 * q * H ≤ A)
    (ε' : ℝ) (hε' : 0 ≤ ε') (A₁ : ℕ) (hA₁ : A₁ + 1 ≤ A / q)
    (hεA₁ : 2 ≤ ε' * A₁)
    (hA2 : ∀ d : ℕ, 0 < d → d ∣ q → ∀ χ : DirichletCharacter ℂ (q / d),
      ∀ A' J : ℕ, A₁ ≤ A' → A' / 2 ≤ J → J ≤ A' → A' + J ≤ 3 * A →
        ∑ n' ∈ Finset.Ioc A' (A' + J),
          ‖∑ m' ∈ (Finset.Ioc n' (n' + h₀)).filter (HasFactorInAll levels),
            χ m' * g m'‖^2 / n'
          ≤ ε'^2 * (h₀ : ℝ)^2 * ∑ n' ∈ Finset.Ioc A' (A' + J), (1:ℝ)/n') :
    ∑ n ∈ Finset.Ioc A (2 * A),
        ‖∑ m ∈ (Finset.Ioc n (n + H)).filter (HasFactorInAll levels),
          g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ)
            * (((a : ℝ) / (q : ℝ) + δ : ℝ) : ℂ))‖ / ((H : ℝ) * n)
      ≤ (16 * q * ε' + q * h₀ / H + 4 * Real.pi * q^2 * |δ| * h₀)
          * ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n
```

Verification:

- `lake env lean MoltResearch/Discrepancy/MajorArcAssembly.lean` — exit 0.
- `lake build MoltResearch.Discrepancy.MajorArcAssembly` — exit 0; 7,993 jobs.

### `704b824b` — Track R: thread the honest slice guard through R6-8 (#3044, R8-5)

Finding: `⌈A₀⌉₊ + 1 ≤ A/q` implies `A₀ ≤ A/q - 1`; nonnegativity of `ε'`
therefore transports `2 ≤ ε'A₀` to the integer threshold used by R6-6d. The new
slice lower bound is passed unchanged to the A.2 clause.

Full new helper and changed theorem statements:

```lean
theorem two_le_mul_nat_sub_one_of_ceil_add_one_le (ε' A₀ : ℝ) (A q : ℕ)
    (hε' : 0 ≤ ε') (hε'A₀ : 2 ≤ ε' * A₀) (hA₀q : ⌈A₀⌉₊ + 1 ≤ A / q) :
    2 ≤ ε' * ((A / q - 1 : ℕ) : ℝ)

theorem majorArc_block_bound_restricted
    (levels : List (Finset ℕ)) (hlv : ∀ P ∈ levels, ∀ p ∈ P, p.Prime)
    (A₀ : ℝ) (hA₀1 : 1 ≤ A₀) (h₀ : ℕ) (ε' : ℝ) (hε' : 0 ≤ ε')
    (hε'A₀ : 2 ≤ ε' * A₀)
    (hA2 : ∀ A : ℕ, A₀ ≤ A →
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → (∀ n, ‖g n‖ ≤ 1) → g 1 = 1 →
        NonPretentiousAt g A₀ (2 * A + 1) →
        ∀ J : ℕ, A / 2 ≤ J → J ≤ A →
          ∑ n ∈ Finset.Ioc A (A + J),
            ‖∑ m ∈ (Finset.Ioc n (n + h₀)).filter (HasFactorInAll levels), g m‖^2 / n
            ≤ ε'^2 * (h₀ : ℝ)^2 * ∑ n ∈ Finset.Ioc A (A + J), (1:ℝ)/n)
    (g : ℕ → ℂ) (hg : CompletelyMultiplicativeC g) (hgu : Unimodular g)
    (q : ℕ) (hq : 0 < q) (hql : ∀ P ∈ levels, ∀ p ∈ P, ¬ p ∣ q) (a : ℤ) (δ : ℝ)
    (A H : ℕ) (hh₀ : 0 < h₀) (h2h₀ : 2 * h₀ ≤ H) (hA : 6 * q * H ≤ A)
    (hA7 : 7 * q ^ 2 ≤ A) (hA₀q : ⌈A₀⌉₊ + 1 ≤ A / q)
    (hnp : NonPretentiousAt g (q * A₀ + 26) (6 * A + 1)) :
    ∑ n ∈ Finset.Ioc A (2 * A),
        ‖∑ m ∈ (Finset.Ioc n (n + H)).filter (HasFactorInAll levels),
          g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ)
            * (((a : ℝ) / (q : ℝ) + δ : ℝ) : ℂ))‖ / ((H : ℝ) * n)
      ≤ (16 * q * ε' + q * h₀ / H + 4 * Real.pi * q^2 * |δ| * h₀)
          * ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n
```

Verification:

- `lake env lean Conjectures/C0002_erdos_discrepancy/src/TrackCStage5MajorArcA2.lean` — exit 0.
- `lake build Conjectures.C0002_erdos_discrepancy.src.TrackCStage5MajorArcA2` — exit 0; 8,019 jobs.

### `e30075cd` — Track R: absorb the reindexed A2 overshoot (#3044, R8-3)

Finding: the endpoint arithmetic gives the half-dyadic length and at most four-point
overshoot. Its harmonic mass is at most two. The overshoot is absorbed directly from
`2 ≤ εa`; this also exposes a false intermediate inequality in the brief, recorded
under accounting discrepancies below.

Full new helper and changed theorem statements:

```lean
theorem reindexed_block_endpoint_bounds (A c d : ℕ) (hd : 0 < d)
    (h4dA : 4 * d ≤ A) (hcA : 3 * c ≤ A) :
    3 * ((A + c) / d - 1) ≤ 2 * ((2 * A + c) / d) ∧
      (2 * A + c) / d ≤ 2 * ((A + c) / d - 1) + 4

theorem sum_one_div_Ioc_le_two_of_le_two_mul_add_four (a b : ℕ) (ha : 3 ≤ a)
    (hb : b ≤ 2 * a + 4) :
    ∑ n ∈ Finset.Ioc a b, (1 : ℝ) / n ≤ 2

theorem reindexed_meanSquare_numerics (ε h a : ℝ) (hh : 0 ≤ h)
    (ha : 0 < a) (hεa : 2 ≤ ε * a) :
    (4 / 3) * (ε * h * 2 + 4 * h / (2 * a + 1)) ≤ 4 * (ε * h)

theorem sum_div_comp_div_le_of_meanSquare (W : ℕ → ℝ) (hW : ∀ n, 0 ≤ W n)
    (ε h : ℝ) (hε : 0 ≤ ε) (hh : 0 ≤ h) (hWh : ∀ n, W n ≤ h) (A₁ N : ℕ)
    (hA2 : ∀ A' J : ℕ, A₁ ≤ A' → A' / 2 ≤ J → J ≤ A' → A' + J ≤ N →
      ∑ n ∈ Finset.Ioc A' (A' + J), (W n)^2 / n
        ≤ ε^2 * h^2 * ∑ n ∈ Finset.Ioc A' (A' + J), (1:ℝ)/n)
    (A c d : ℕ) (hd : 0 < d) (h4dA : 4 * d ≤ A) (hcA : 3 * c ≤ A)
    (hA₁ : A₁ + 1 ≤ (A + c) / d) (hεA₁ : 2 ≤ ε * A₁)
    (hN : (2 * A + c) / d ≤ N) :
    ∑ n ∈ Finset.Ioc A (2 * A), W ((n + c) / d) / n ≤ 4 * (ε * h)
```

Verification: `lake env lean MoltResearch/Discrepancy/MajorArcAssembly.lean` — exit 0.
