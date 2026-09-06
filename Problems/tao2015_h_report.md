# Track R — I-1 + H: Codex runs 16–17 final report (2026-09-06)

Run 16 (brief `Problems/tao2015_h_brief.md` without its resume note) stopped in seven minutes with a compiled counterexample: the interface
field `HalaszLargeValuesAssumption.bound` was false for `0 < T < 1/(2e)` (the factor `log(2T) + 1` is negative while a singleton `𝒯` is
allowed; the prime field had the same defect with a negative base under the `3/4` power) — a transcription bug, since Iwaniec–Kowalski 9.6
and `[MR]` Lemma 8 are stated for `T ≥ 1`. Run 17 (the brief with its resume note) did **I-1** (both fields now require `1 ≤ T`; threaded
through the consumers; pins byte-identical) and **H-1…H-5**: the Halász–Montgomery duality bound, the logarithmic Dirichlet kernel bound
(`‖K(u)‖ ≤ 40(N/|u| + √|u|(log 2N + 1) + 1)` from `vdc2` on the low dyadic blocks and `kusmin_landau` on the tail), the well-spaced row sums,
the exact constant `64` (charging the `√|u|` term only to the pre-Kusmin blocks, which removes the `log 2N` vs `log 2T` issue), and
**`halaszMontgomery_large_values`** — IK 9.6 exactly as the class states it — with `instance : HalaszLargeValuesAssumption` and
**`trackR_edp_halasz [PrimeLargeValuesAssumption] : ∀ f, IsSignSequence f → ¬ BoundedDiscrepancy f`**, pinned to the standard three axioms.
Verbatim run-17 report below; the run-16 counterexample is in the design report, Phase 5.

---

# Track R — Halász large-values discharge report

Date: 2026-09-06
Branch: `vex/track-r-halasz-lv`

## Outcome

Completed I-1 and H-1 through H-5.  Both large-values interfaces now require
`1 ≤ T`; the integer-supported interface is discharged by the in-tree
Halász–Montgomery theorem with the requested constant `64`.  The Track R EDP
endpoint consequently retains only `[PrimeLargeValuesAssumption]`.

No stop condition was reached.  The kernel bound was obtained from the tree's
discrete `kusmin_landau` and `vdc2` tools, and the constant `64` closed without
changing the class statement.

## Commits

- `8891fcce` — `Track R: require 1 ≤ T in the large-values interfaces (#3044, I-1)`
- `07843f50` — `Track R: prove the Halász–Montgomery duality bound (#3044, H-1)`
- `a5f8003c` — `Track R: bound the logarithmic Dirichlet kernel (#3044, H-2)`
- `9f1e01ad` — `Track R: bound the well-spaced kernel rows (#3044, H-3)`
- `bd61f16a` — `Track R: close the Halász–Montgomery constant (#3044, H-4)`
- `28ddb586` — `Track R: discharge the Halász large-values interface (#3044, H-5)`

Every commit has the required run and `Co-Authored-By` trailers.  Nothing was
pushed, merged, or rebased.

## I-1 — corrected interfaces

The two class fields in `Interfaces/LargeValues.lean` now begin with the true
large-values range:

```lean
bound : ∀ (N : ℕ) (a : ℕ → ℂ) (T : ℝ) (𝒯 : Finset ℝ),
  1 ≤ T → ...
```

The source transcription and every consumer through the schedule/capstone
chain were updated.  The four existing audit pins retained byte-identical
axiom sets.

## H-1 — duality and Schur

The compiled abstract wrapper is:

```lean
theorem sum_norm_sq_le_norm_sq_mul_sup_kernel {ι κ : Type*}
    (I : Finset ι) (J : Finset κ) (b : ι → ℂ) (χ : ι → κ → ℂ)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ t ∈ J,
      ∑ s ∈ J, ‖∑ i ∈ I, χ i t * (starRingEnd ℂ) (χ i s)‖ ≤ B) :
    ∑ t ∈ J, ‖∑ i ∈ I, b i * χ i t‖ ^ 2
      ≤ (∑ i ∈ I, ‖b i‖ ^ 2) * B
```

It is proved via the dual synthesis energy, Cauchy–Schwarz, and the symmetric
Schur row-sum bound.

## H-2 — logarithmic kernel

With

```lean
halaszKernel N u = ∑ n ∈ Finset.Icc 1 N, ExpSums.e (-(u * Real.log n))
```

the compiled H-2 theorem is:

```lean
theorem norm_halaszKernel_le (N : ℕ) (u : ℝ) (hu : 1 ≤ |u|) :
    ‖halaszKernel N u‖
      ≤ 40 * ((N : ℝ) / |u|
        + Real.sqrt |u| * (Real.log (2 * (N : ℝ)) + 1) + 1)
```

Thus `C₁ = 40`.  Before packaging into that uniform shape, the positive-
frequency proof records the sharper bound

```text
1 + 33 √v log(2N) + 36 N/v.
```

The low dyadic blocks use `vdc2`; after the phase increments enter a single
unit interval, the tail uses `kusmin_landau`.

## H-3 — well-spaced rows

The compiled packing lemmas include

```lean
∑ s ∈ 𝒯.erase t, (1 : ℝ) / |t - s|
  ≤ 2 * (Real.log (2 * T) + 1)

∑ s ∈ 𝒯.erase t, Real.sqrt |t - s|
  ≤ (𝒯.card : ℝ) * Real.sqrt (2 * T)
```

and the H-3 row theorem:

```lean
theorem sum_norm_halaszKernel_sub_le ... :
    ∑ s ∈ 𝒯, ‖halaszKernel N (t - s)‖
      ≤ (N : ℝ) + 80 * (N : ℝ) * (Real.log (2 * T) + 1)
        + 40 * (𝒯.card : ℝ) *
          (Real.sqrt (2 * T) * (Real.log (2 * (N : ℝ)) + 1) + 1)
```

The reciprocal estimate is obtained by splitting left/right of `t`, mapping
each side injectively to natural-number floors, and applying the harmonic-sum
bound.

## H-4 — exact constant ledger

Write `L = log(2T) + 1`.  Since `1 ≤ T`, both `L ≥ 1` and `√T ≥ 1`.

1. Each dyadic block satisfies

   ```text
   (if 13v ≤ 12(M+1) then 0 else 22√v) + 12(M+1)/v.
   ```

2. The endpoint sum satisfies

   ```text
   ∑j (2^j + 1) ≤ (5/2)N,
   ```

   so the Kusmin–Landau part contributes at most `30N/v`.

3. For `v ≤ 2T`, the number of pre-Kusmin blocks is at most `(3/2)L`.
   Hence their van der Corput contribution is at most `33√v L`, independent
   of `N`.

4. The scale-sensitive kernel estimate is therefore

   ```text
   ‖K(v)‖ ≤ 1 + 30N/v + 33√v L.
   ```

5. Harmonic and square-root packing give the row ledger

   ```text
   N + card(𝒯) + 60N L + 33 card(𝒯) √(2T) L.
   ```

6. Using `√2 ≤ 3/2`, `√T ≥ 1`, and `L ≥ 1`, the two portions close as

   ```text
   N + 60N L ≤ 64N L,
   card(𝒯) + 33 card(𝒯) √(2T) L ≤ 64 card(𝒯) √T L.
   ```

Thus the exact compiled row bound is:

```lean
theorem sum_norm_halaszKernel_sub_le_sixty_four ... :
    ∑ s ∈ 𝒯, ‖halaszKernel N (t - s)‖
      ≤ 64 * ((N : ℝ) + (𝒯.card : ℝ) * Real.sqrt T)
        * (Real.log (2 * T) + 1)
```

The `log(2N)`/`log(2T)` issue is removed by charging the square-root term only
to the pre-Kusmin blocks, rather than to every dyadic block.

## Compiled final theorem

```lean
theorem halaszMontgomery_large_values :
    ∀ (N : ℕ) (a : ℕ → ℂ) (T : ℝ) (𝒯 : Finset ℝ),
      1 ≤ T → (∀ t ∈ 𝒯, |t| ≤ T) →
      (∀ t ∈ 𝒯, ∀ u ∈ 𝒯, t ≠ u → 1 ≤ |t - u|) →
      ∑ t ∈ 𝒯, ‖∑ n ∈ Finset.Icc 1 N, (a n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ^ 2
        ≤ 64 * ((N : ℝ) + (𝒯.card : ℝ) * Real.sqrt T)
            * (Real.log (2 * T) + 1)
            * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2
```

This statement is definitionally suitable for:

```lean
instance : HalaszLargeValuesAssumption :=
  ⟨halaszMontgomery_large_values⟩
```

## H-5 — discharged endpoint and audit

The new Conjectures leaf compiles:

```lean
theorem trackR_edp_halasz [PrimeLargeValuesAssumption]
    (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f :=
  trackR_edp f hf
```

The old pins and the new pin all report exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Pins checked:

- `edp_of_sliceMeanSquareA2`
- `theorem18_of_sliceMeanSquareA2`
- `sliceMeanSquareA2`
- `trackR_edp`
- `trackR_edp_halasz`

## Verification

- `lake env lean MoltResearch/Discrepancy/HalaszMontgomeryLargeValues.lean`:
  passed.
- `lake env lean Conjectures/.../TrackCStage5LargeValuesDischarge.lean`:
  passed.
- `lake env lean Conjectures/.../TrackCAxiomAudit.lean`: passed; the only
  output was the pre-existing deprecated `ArithmeticFunction` import warning.
- `lake build MoltResearch.DiscrepancyAnalytic Conjectures`: passed, 8,338
  jobs; pre-existing linter warnings only.
- Forbidden-token grep under `MoltResearch/` and `Solutions/`: no matches
  (`rg` exit code 1, as expected).
- `./scripts/check_layering.sh`: `check_layering: OK`.
- `python3 scripts/check_aggregator_coverage.py`: passed; 192 modules, 190
  reachable, with only the two known allowlisted modules reported:
  `EndpointSimpExamples` and `PaperSimpExamples`.
- `git diff --check`: passed.

Final tracked worktree state is clean.  `CODEX_REPORT.md` is the sole
untracked file and is intentionally uncommitted.
