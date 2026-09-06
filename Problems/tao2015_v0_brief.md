# Track R — V-0 brief: the honest `PrimeLargeValuesAssumption` (existential constant, named exponent) and its consumers

**Ground rules:** `Problems/tao2015_vi9g_brief.md` §0 verbatim (no `sorry`/`axiom`/`unsafe` under `MoltResearch/`, `Solutions/`, not even in comments;
new nucleus lemmas only in new leaf files registered in `MoltResearch/DiscrepancyAnalytic.lean`; never edit `PlancherelHarness`, never append to
`BandSchedule`/`WindowTK`/`WindowAssembly`/`HalaszComplex`; no instances of `*Assumption` classes except where a theorem discharges one (as
`HalaszLargeValuesAssumption` now is, by run 17 — check `TrackCStage5LargeValuesDischarge.lean`); one commit per unit `Track R: <one line> (#3044, V-0-<n>)`;
never push/merge/rebase; `CODEX_REPORT.md` uncommitted). Read: the design report `Problems/tao2015_a1_r6r7_design_report.md` §"Phase 6" (unit V-0 and why),
`Conjectures/C0002_erdos_discrepancy/src/Interfaces/LargeValues.lean`, `Problems/sources/tao2015_statements.md` (the `[MR]` Lemma 8 transcription — update it),
`TrackCStage5BandEnergyExceptional.lean` (the call site `sum_prime_integer_energy_large_card_le`), `TrackCStage5ExceptionalReCut.lean` and
`TrackCStage5BandEnergyExceptionalReCut.lean` (the `Γ` shape `exp(−log Pc/(log 2T)^{3/4})·(log 2T)²`), the sharp/cells/wide schedule files, and the L3
leaves (`TrackCStage5*Ladder*`, `TrackCStage5SliceA2*`, `TrackCStage5ExceptionalPrimeFit.lean`) — `grep -rn "(3 / 4 : ℝ)"` lists every site.

## Why

`[MR]` Lemma 8 reads `∑_{t∈𝒯}|P(it)|² ≪_ε [P + |𝒯|·P·exp(−log P/(log T)^{2/3+ε})(log T)²]·∑_p|a_p|²/log P`: an `ε`-dependent implied constant (which
absorbs the small-`T` range) and an exponent strictly above the Vinogradov–Korobov `2/3`. The class fixed the constant at `64` and the exponent at `3/4`
with no slack; the VK width `c/((log t)^{2/3}(loglog t)^{1/3})` beats `(log t)^{−3/4}` only for `log t ≳ e^{72}`, so the literal field is not what any
zero-free region delivers at explicit constants. The consumer only needs *some* fixed constant and *some* exponent `< 1` (design report, Phase 6:
L3-5's margin is `49/50 − θ` against `(log A)^{1/50} loglog A`).

## V-0-1 — the interface

In `Interfaces/LargeValues.lean`:
```
/-- The exponent of the prime large-values saving: Chudakov's region `1 − c/((log t)^{3/4}(loglog t)^{3/4})` beats `(log t)^{−4/5}`. -/
noncomputable def primeLargeValuesExponent : ℝ := 4 / 5

class PrimeLargeValuesAssumption : Prop where
  bound : ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : ℕ) (Y : Finset ℕ), (∀ p ∈ Y, p.Prime) → (∀ p ∈ Y, P ≤ p ∧ p ≤ 2*P) →
    ∀ (a : ℕ → ℂ) (T : ℝ) (𝒯 : Finset ℝ), 2 ≤ P → 1 ≤ T → (∀ t ∈ 𝒯, |t| ≤ T) → (∀ t ∈ 𝒯, ∀ u ∈ 𝒯, t ≠ u → 1 ≤ |t - u|) →
    ∑ t ∈ 𝒯, ‖∑ p ∈ Y, (a p/(p:ℂ)) * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖^2
      ≤ C * (1 + (𝒯.card:ℝ) * Real.exp (-(Real.log P / (Real.log (2*T))^primeLargeValuesExponent)) * (Real.log (2*T))^2)
          * (∑ p ∈ Y, ‖a p‖^2/(p:ℝ)^2) * (P:ℝ) / Real.log P
```
(keep `1 ≤ T` from I-1; update the docstring: source, the `∃ C` and the exponent, "no instance until Phase 6 lands"; update the transcription file.)

## V-0-2 — the consumers

Thread the change with **no loss of any proved theorem**: obtain `C` once (`obtain ⟨C, hC1, hbound⟩ := PrimeLargeValuesAssumption.bound`) at the
call site and carry it as a parameter `Cp` (with `1 ≤ Cp`) through the chain — `sum_prime_integer_energy_large_card_le` (its `64` becomes `Cp`), the
recut's `Γ` (the literal `(3 / 4 : ℝ)` becomes `primeLargeValuesExponent`, the `64` in the prime part becomes `Cp`), `band_energy_typicalS_le_of_cellUniform_fit_recut(_wide)`,
the sharp/cells/wide schedule theorems (`hfitPri`/`hfitUCell` shapes), and the L3 leaves: `TrackCStage5ExceptionalPrimeFit.lean`'s `Γ ≤ 1` lemmas
(the eventual inequality now reads `… − log Pc/(log 2T)^{4/5} …`; the margin `(log A₁)^{49/50}/(2.1 log A₁)^{4/5} ≥ 0.5(log A₁)^{0.18}` against
`200ℓ(loglog A₁+1)`, `ℓ ≤ 2(log A₁)^{0.02} + 3` — re-prove with the named exponent, using `Real.rpow` lemmas as before), the exceptional-aggregate
fits where `64` entered as the prime constant (`Cp` is a fixed constant; the L3-5 fixed condition becomes `C'·Cp·Nu·N_𝒰·DeltaU² ≤ c₃eps²/48`, absorbed
into `ε'`), and `sliceMeanSquareA2`/`trackR_edp`(`_halasz`) whose statements do not change. Since `Cp` is existential in the class, the final theorem
obtains it inside its proof; all intermediate theorems take `Cp` explicitly. Prefer **new** files/variants only where a signature changes would otherwise
touch a no-append nucleus file; Conjectures files may be edited in place (they are backlog).

## V-0-3 — pins

`edp_of_sliceMeanSquareA2`, `theorem18_of_sliceMeanSquareA2`, `sliceMeanSquareA2`, `trackR_edp`, `trackR_edp_halasz` compile with byte-identical axiom sets.

**Verification/report.** `lake env lean` on every touched file; `lake build MoltResearch.DiscrepancyAnalytic Conjectures`; grep gates, layering, aggregator
coverage; `CODEX_REPORT.md` listing every site changed and the new margin computations. **Stop rule:** stop only if some proved numerology cannot be
re-established at exponent `4/5` with a fixed `Cp` (record the exact inequality) — constants are yours.
