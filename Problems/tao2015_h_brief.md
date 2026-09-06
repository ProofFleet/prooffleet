## RESUME NOTE (run 17) — read before anything else
Run 16 found (correctly, `halaszLargeValues_bound_counterexample`) that the class field `HalaszLargeValuesAssumption.bound` is **false for
`0 < T < 1/(2e)`**: the factor `log(2T) + 1` is negative there while a singleton `𝒯` is allowed. `PrimeLargeValuesAssumption.bound` has the
same defect in a worse form (`(log(2T))^{3/4}` with a negative base). Both are transcription bugs of the interface, not of the literature
(IK 9.6 and `[MR]` Lemma 8 are stated for `T ≥ 1`/`T ≥ 2`). Do this first:

- **I-1 (interface hygiene).** In `Conjectures/C0002_erdos_discrepancy/src/Interfaces/LargeValues.lean` add the hypothesis **`1 ≤ T`** to both
  fields (replace `0 < T →` by `1 ≤ T →`; keep everything else verbatim; update the two docstrings and the transcription
  `Problems/sources/tao2015_statements.md` if it lists the fields). Then thread `1 ≤ T` through the consumers: the only call sites of the two
  fields are the two lemmas in `TrackCStage5BandEnergyExceptional.lean` (`hT : 0 < T` at line ≈95 and its prime twin) — strengthen their `hT` to
  `1 ≤ T` and fix every caller up to the schedule/capstone theorems, which already carry `hT1 : 1 ≤ T` (the recut/exceptional chain in
  `TrackCStage5ExceptionalReCut.lean`, `…BandEnergyExceptionalReCut.lean`, `…InnerBandScheduleSharp*.lean`, `…ScheduleSharpCellsWide*.lean`,
  the L3 leaves — derive `1 ≤ T` from `hT1` where available, or add it as a hypothesis and discharge it at the next level). The four audit pins
  (`edp_of_sliceMeanSquareA2`, `theorem18_of_sliceMeanSquareA2`, `sliceMeanSquareA2`, `trackR_edp`) must compile with byte-identical axiom
  sets. One commit `Track R: require 1 ≤ T in the large-values interfaces (#3044, I-1)`.
- Then **H-1 … H-5 as below** against the corrected field (with `1 ≤ T` the factor is `≥ 1 + log 2`). Note for H-4: with `1 ≤ T` the
  well-spaced sums are as stated; the `log 2N` vs `log 2T` comparison is the only remaining constant issue.

# Track R — H brief: discharge `HalaszLargeValuesAssumption` (Iwaniec–Kowalski Theorem 9.6) in the tree

**Ground rules:** `Problems/tao2015_vi9g_brief.md` §0 verbatim (no `sorry`/`axiom`/`unsafe` under `MoltResearch/`, `Solutions/`, not even in
comments; new nucleus lemmas only in new leaf files registered by one import line in `MoltResearch/DiscrepancyAnalytic.lean`; never edit
`PlancherelHarness`, never append to `BandSchedule`/`WindowTK`/`WindowAssembly`/`HalaszComplex`; one commit per unit `Track R: <one line> (#3044, H-<n>)`;
never push/merge/rebase; `CODEX_REPORT.md` uncommitted). Read first: `Conjectures/C0002_erdos_discrepancy/src/Interfaces/LargeValues.lean`
(the exact statement to prove — `HalaszLargeValuesAssumption.bound`), `MoltResearch/Discrepancy/ExpSums.lean` (`e`, `nint`, `kusmin_landau`,
`vdc2`), `MoltResearch/Discrepancy/VinogradovTypeI.lean` (`norm_sum_e_linear_le`), `MoltResearch/Discrepancy/DyadicMVT.lean`
(`sum_norm_sq_le_integral_of_separated`, the mean value theorems), `MoltResearch/Discrepancy/LargeValues.lean` (kernel toolkit), and the design
report `Problems/tao2015_a1_r6r7_design_report.md` §"Phase 5" (this unit and the frontier statement for `PrimeLargeValuesAssumption`).

**Target.** A theorem in a new nucleus leaf `MoltResearch/Discrepancy/HalaszMontgomeryLargeValues.lean` with **exactly** the statement of the
class field (so that `instance : HalaszLargeValuesAssumption := ⟨halaszMontgomery_large_values⟩` typechecks in a new Conjectures file
`TrackCStage5LargeValuesDischarge.lean`, next to which the audit file gets the pin `#print axioms trackR_edp_halasz` for the endpoint that
takes only `[PrimeLargeValuesAssumption]`):

```
∀ (N : ℕ) (a : ℕ → ℂ) (T : ℝ) (𝒯 : Finset ℝ), 0 < T → (∀ t ∈ 𝒯, |t| ≤ T) → (∀ t ∈ 𝒯, ∀ u ∈ 𝒯, t ≠ u → 1 ≤ |t - u|) →
  ∑ t ∈ 𝒯, ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ)) * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖^2
    ≤ 64 * ((N:ℝ) + (𝒯.card:ℝ) * Real.sqrt T) * (Real.log (2*T) + 1) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖^2/(n:ℝ)^2
```

(`Real.fourierChar (-(log n · t))` is `e(−t log n)` in the `e` notation of `ExpSums`; note the frequency normalisation `n^{−2πi t}`.)

**The proof (Montgomery, *Topics*, Thm 8.3 / IK 9.6), in four units.**

* **H-1 (duality/Schur).** For coefficients `b n := a n / n` and the phases `n ↦ e(−t log n)`:
  `∑_{t∈𝒯} ‖∑_n b_n e(−t log n)‖² ≤ (∑_n ‖b_n‖²) · max_{t∈𝒯} ∑_{s∈𝒯} ‖K(t − s)‖`, `K(u) := ∑_{n ∈ Icc 1 N} e(−u log n)` (Cauchy–Schwarz on the
  expansion `∑_t |∑_n b_n χ_n(t)|² = ∑_{n,m} b_n b̄_m ∑_t χ_n(t)χ̄_m(t)` is *not* the route; use the dual form: for any `c : 𝒯 → ℂ`,
  `‖∑_t c_t ∑_n b_n χ_n(t)‖ ≤ ‖b‖·(∑_n ‖∑_t c_t χ_n(t)‖²)^{1/2}` and `∑_n ‖∑_t c_t χ_n(t)‖² = ∑_{t,s} c_t c̄_s K(t−s) ≤ ‖c‖²·max_t ∑_s ‖K(t−s)‖`
  (Schur's test with the symmetric kernel `‖K(t−s)‖ = ‖K(s−t)‖`), then take `c_t := conj(S(t))/‖S‖` — or prove the primal inequality directly by
  `∑_t ‖S(t)‖² = ∑_t S(t)·conj(S(t)) = ∑_n b_n ∑_t conj(S(t)) χ_n(t)` and Cauchy–Schwarz + Schur; either way state it as a clean lemma
  `sum_norm_sq_le_norm_sq_mul_sup_kernel` for arbitrary finite families of unimodular phases).
* **H-2 (the kernel bound).** For `1 ≤ |u|`: `‖K(u)‖ ≤ C₁·((N:ℝ)/|u| + √|u|·(Real.log (2N) + 1) + 1)` with an explicit `C₁` (record it), by dyadic
  blocks `(M, 2M]`: on a block with `|u| ≤ M/4`-type range use Kusmin–Landau (`kusmin_landau`/`norm_sum_e_linear_le` after the phase
  `φ(n) = −u·log n/(2π)` has first differences `u/(2πn)`-ish bounded away from integers: `nint(φ(n+1) − φ(n)) ≥ |u|/(4πM)`) giving `≪ M/|u|`; on a block
  with `|u| > M/4`-type range use `vdc2` (second differences `≍ |u|/(2πn²)`, so `r ≍ |u|/M²`, `D ≍ |u|/M`, `θ := √r`) giving `≪ (|u|/M + 2)(M/√|u| + 1/√r) ≪ √|u| + M/√|u|`;
  sum the `≤ log₂(2N)` blocks. (Both tools are discrete; the phase is concave, so apply them to `−φ` or to `conj`; check the sign conventions of
  `vdc2`'s convexity hypothesis.)
* **H-3 (the well-spaced sum).** For `t ∈ 𝒯`: `∑_{s∈𝒯} ‖K(t−s)‖ ≤ N + ∑_{s ≠ t} C₁(N/|t−s| + √|t−s|(log 2N + 1) + 1)`, and with `1`-separation inside
  `[−T, T]`: `∑_{s≠t} 1/|t−s| ≤ 2(log(2T) + 1)` (compare with `2∑_{k ≤ 2T} 1/k`), `∑_{s≠t} √|t−s| ≤ 𝒯.card·√(2T)`, `#{s ≠ t} ≤ 𝒯.card`. Hence
  `max_t ∑_s ‖K(t−s)‖ ≤ N + 2C₁N(log 2T + 1) + C₁·𝒯.card·(√(2T)(log 2N + 1) + 1)`.
* **H-4 (the constant).** Close `≤ 64(N + 𝒯.card·√T)(log 2T + 1)` from H-3: the `N(log 2T + 1)` terms need `1 + 2C₁ ≤ 64`; the `𝒯.card·√T` term needs
  `C₁√2·(log 2N + 1) + C₁ ≤ 64(log 2T + 1)` — **this fails when `log 2N ≫ log 2T`**. Handle it: for `N ≤ (2T)^{k}` with a fixed `k` it is a constant
  matter (`log 2N ≤ k log 2T`; check what `C₁` allows, e.g. `k = 4`); for `N > (2T)^k` use instead `‖K(u)‖ ≤ N` trivially on the range `|u| ≤ √N`... —
  no: better, split `K(u) = ∑_{n ≤ N₀} + ∑_{N₀ < n ≤ N}` with `N₀ := ⌊(2T)^k⌋` and bound the tail block sums by the Kusmin–Landau branch only
  (for `n > (2T)^k ≥ |u|^k`, the first differences `|u|/(2πn)` are tiny, so K–L gives `≪ n/|u|` per block and the tail contributes `≪ N/|u|`), which
  keeps `√|u|·log(2N₀) ≤ k√|u|·log 2T`. Record the exact constant bookkeeping. If, after an honest attempt, the `64` cannot be met but a larger
  absolute constant can, **do not change the class**: prove the theorem with your constant, then derive the class's `64` form by the
  reduction `N ↦` … only if valid; otherwise report the exact constant achieved and stop the discharge at that point (the consumers' margins are
  enormous — the next run can adjust the class and the consumers together, but that is not this run's job).
* **H-5.** `instance : HalaszLargeValuesAssumption` in the new Conjectures file, `theorem trackR_edp_halasz [PrimeLargeValuesAssumption] (f) (hf) :
  ¬ BoundedDiscrepancy f := trackR_edp f hf`, and its `#print axioms` pin (standard three) in `TrackCAxiomAudit.lean`. Also update the docstring of
  `Interfaces/LargeValues.lean`'s class to say it is now discharged by `halaszMontgomery_large_values` (the "no instance" sentence must go for this class only).

**Verification/report.** `lake env lean` the new files; `lake build MoltResearch.DiscrepancyAnalytic Conjectures`; grep gates, layering, aggregator
coverage; `CODEX_REPORT.md` with the statements as compiled and the constant ledger. **Stop rule:** stop only if the kernel bound of H-2 cannot be
obtained from the tree's `kusmin_landau`/`vdc2` (record which hypothesis fails), or if H-4's constant cannot be met and no valid reduction exists.
