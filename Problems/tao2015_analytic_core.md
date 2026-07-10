# Problem Card: Tao 2015 analytic core (deep inputs for Erdős discrepancy)

Status: active

Companion cards: `Problems/erdos_discrepancy.md` (substrate), `Problems/tao2015_pipeline.md`
(stage engineering). This card is the **blueprint for the actual mathematics**: the two deep
inputs of Tao's proof and the derivation that combines them.

## 0. One-line pitch

Everything merged so far is scaffolding around a hole. This card decomposes the hole: the
Fourier reduction to completely multiplicative functions, the logarithmically averaged two-point
Elliott theorem, and the derivation gluing them into the Erdős discrepancy theorem. Landing the
*statements* as typed interfaces makes "EDP conditional on named theorems of Tao" a real,
checkable milestone; discharging them is the long game.

## 1. Natural language statement (proof architecture of Tao 2015)

Tao's proof of EDP (arXiv:1509.05363) has three moving parts:

**(A) Fourier reduction** (§2, building on Polymath5): if EDP *fails* — some unit sequence has
bounded discrepancy — then there exists a **stochastic completely multiplicative function**
`g : ℕ → S¹` (a random completely multiplicative function valued in the complex unit circle)
whose partial sums have uniformly bounded second moment:
`∃ C, ∀ n, 𝔼 |∑_{j=1}^n g(j)|² ≤ C`.
Equivalently (contrapositive): to prove EDP it suffices to show every stochastic completely
multiplicative `g : ℕ → S¹` has `sup_n 𝔼 |∑_{j≤n} g(j)|² = ∞`.

**(B) Logarithmically averaged two-point Elliott** (companion paper, arXiv:1509.05422): for
`g : ℕ → ℂ` completely multiplicative with `|g| = 1`, if `g` does not "pretend" to be
`n ↦ χ(n) n^{it}` for any Dirichlet character `χ` and real `t` (pretentious distance sense),
then for any distinct shifts `a ≠ b`, the log-averaged correlation vanishes:
`(1/log N) ∑_{n≤N} g(n+a) · conj(g(n+b)) / n → 0`.
Its own proof needs the entropy decrement argument and Matomäki–Radziwiłł; on this card it is
an **input to be stated, not proved**.

**(C) The derivation** (§3): bounded-second-moment partial sums for stochastic multiplicative
`g` force strong self-correlations of `g` along nearby shifts (a van der Corput / expansion
argument), which after handling the "pretentious" branch (character-modulated case, dealt with
by a separate elementary argument) contradicts (B). Hence (A) + (B) ⇒ EDP.

## 2. Formalization target (Lean)

Two-layer target, mirroring the Track C stub discipline (single honest assumptions, quarantined
in `Conjectures/`, replaced by proofs over time):

- **Language layer (verified, lands in `MoltResearch/`)**: definitions only, no axioms —
  ℂ-valued sequence predicates and log-averaged sums.
- **Interface layer (`Conjectures/C0002_erdos_discrepancy/src/`)**: `Stage2Assumption`-style
  typed statements of (A), (B), and the conditional theorem (C).

Indicative signatures (names/homes to be settled in PRs; type-correctness is the deliverable):

```lean
-- Language layer (MoltResearch/Discrepancy/MultiplicativeC.lean or similar)
def CompletelyMultiplicativeC (g : ℕ → ℂ) : Prop := ∀ a b, g (a * b) = g a * g b
def Unimodular (g : ℕ → ℂ) : Prop := ∀ n, Complex.abs (g n) = 1
noncomputable def logAvgCorr (g : ℕ → ℂ) (a b N : ℕ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 N, g (n + a) * (starRingEnd ℂ) (g (n + b)) / n) / Real.log N

-- Interface layer (Conjectures/.../TrackCStage5*.lean)
-- (A) Fourier reduction, deterministic first cut (see §6 for the stochastic upgrade):
class FourierReductionAssumption : Prop where
  reduce : (∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → Unimodular g →
              ∀ C : ℝ, ∃ n, C < ‖∑ j ∈ Finset.Icc 1 n, g j‖) →
           ∀ f : ℕ → ℤ, IsSignSequence f → ¬ BoundedDiscrepancy f
-- (B) log-Elliott 2-point, stated with an explicit non-pretentiousness hypothesis
--     (pretentious distance needs defining; see decomposition).
-- (C) target theorem: [FourierReductionAssumption] + [LogElliottAssumption] ⊢
--     ∀ f, IsSignSequence f → ¬ BoundedDiscrepancy f
```

## 3. Dependencies

- Already in this repo (verified): `CompletelyMultiplicative` (ℤ-valued), the multiplicative
  reduction `EDP ⇔ unbounded partial sums` on the ±1 subclass, Stage-2 constructors
  (`TrackCStage2Multiplicative.lean`), the Stage 2–4 boundary pipeline.
- In Mathlib: `ℂ`, `Finset` sums, `Real.log`, Dirichlet characters (`DirichletCharacter`),
  probability measure spaces (`MeasureTheory`), `‖·‖` on ℂ.
- **Not in Mathlib (gap list, roughly increasing depth)**: pretentious (Granville–Soundararajan)
  distance; mean values of multiplicative functions (Halász-type); Matomäki–Radziwiłł;
  entropy decrement. The first is a definition (statable now); the rest are why (B) stays an
  interface for the foreseeable future.

## 4. Decomposition (mergeable sub-tasks)

Language layer (each: 1 file, `make ci`, definition of done = compiles + regression example):

- [x] Define `CompletelyMultiplicativeC` / `Unimodular` (ℂ-valued) with basic simp lemmas, and the ℤ→ℂ coercion bridge `CompletelyMultiplicative f → CompletelyMultiplicativeC (fun n => (f n : ℂ))` (sign sequences are unimodular).
  (Implemented in `MoltResearch/Discrepancy/MultiplicativeC.lean` (on the stable surface):
  `CompletelyMultiplicativeC`, `Unimodular`, `Unimodular.norm_eq_one`/`ne_zero`,
  `CompletelyMultiplicativeC.map_one_of_unimodular`, bridges `CompletelyMultiplicative.toC` and
  `IsSignSequence.unimodularC`; regression examples in `NormalFormExamples.lean`.)
- [x] ℂ-valued partial-sum collapse: port `apSum_eq_mul_apSum_one` to ℂ (`apSumC g d n = g d * apSumC g 1 n` for completely multiplicative `g`), with norm-level corollary for unimodular `g`.
  (Implemented in `MoltResearch/Discrepancy/MultiplicativeC.lean`: `apSumC` (mirrors `apSum`),
  `CompletelyMultiplicativeC.apSumC_eq_mul_apSumC_one`, and the norm-level corollary
  `norm_apSumC_eq_norm_apSumC_one`; regression examples in `NormalFormExamples.lean`.)
- [x] Define `logAvgCorr` (log-averaged two-point correlation) with degenerate-parameter simp lemmas (`N = 0`, `N = 1`, `a = b` diagonal value).
  (Implemented in `MoltResearch/Discrepancy/LogAvgCorr.lean` (on the stable surface):
  `logAvgCorr` with ℂ-division and embraced `Real.log` junk values, simp lemmas
  `logAvgCorr_zero_N` / `logAvgCorr_one_N`, and the unimodular diagonal collapse
  `Unimodular.logAvgCorr_self` (via `Unimodular.mul_conj_self`); regression examples in
  `NormalFormExamples.lean`.)
- [x] Define the pretentious distance `𝔻(g, h; N)` (finite-`N` Granville–Soundararajan distance over primes) — definition + monotonicity basics only.
  (Implemented in `MoltResearch/Discrepancy/PretentiousDist.lean` (on the stable surface):
  `pretentiousDistSq` (primary, over `Nat.primesBelow N`) and `pretentiousDist`, with
  summand/sum nonnegativity, monotonicity in `N` (`pretentiousDistSq_mono` /
  `pretentiousDist_mono`, for unimodular arguments), and diagonal degeneracy
  `Unimodular.pretentiousDistSq_self`; regression examples in `NormalFormExamples.lean`.)

Interface layer (each: 1 file in `Conjectures/`, wiring + consumer example, no new axioms
beyond the named assumption):

- [x] State `FourierReductionAssumption` (deterministic form above), with a consumer example deriving `¬ BoundedDiscrepancy f` from it plus a hypothesized universal-multiplicative witness.
  (Implemented in `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5Fourier.lean`: the class
  exactly as stated above, with **no instance and no axiom** (consumers carry it as a
  hypothesis), the consumer-facing theorem `fourierReduction_notBounded`, and a compile-only
  consumer `example`.)
- [ ] State `LogElliottAssumption` (log-averaged two-point Elliott with explicit non-pretentiousness hypothesis; cite arXiv:1509.05422 Thm 1.3).
- [ ] Stage-5 skeleton: `TrackCStage5Core.lean` packaging (A)+(B) as inputs and exposing the conditional target `stage5_notBounded [FourierReductionAssumption] [LogElliottAssumption] : ∀ f, IsSignSequence f → ¬ BoundedDiscrepancy f` — initially proved from the *existing* Stage-2 stub axiom, then re-proved from (A)+(C) when (C) lands, retiring the stub.
- [ ] Replace the Stage-2 stub axiom's role: derive `stage2Stub_exists_params_one_le_unboundedDiscOffset`'s content from `FourierReductionAssumption` + the multiplicative constructors on the reduced class (this is the first piece of (C)).

Discharge milestones (long-horizon; each becomes its own card when opened):

- [ ] (C) first: conditional EDP from (A)+(B) — the van der Corput expansion + pretentious-branch argument (§3 of the paper). Most self-contained; needs only Mathlib probability + the language layer.
- [ ] (A): the Fourier reduction — Hilbert-space valued sequences, Plancherel, the Polymath5 argument. Medium-hard; opens after (C).
- [ ] (B): entropy decrement + Matomäki–Radziwiłł. Do not open until (A) and (C) are done; expected to remain an interface for a long time.

## 5. References / links

- T. Tao, *The Erdős discrepancy problem*, arXiv:1509.05363 (Discrete Analysis 2016).
- T. Tao, *The logarithmically averaged Chowla and Elliott conjectures for two-point correlations*, arXiv:1509.05422 (Forum Math. Pi 2016).
- Polymath5 wiki (Fourier reduction): https://asone.ai/polymath/index.php?title=The_Erd%C5%91s_discrepancy_problem
- K. Matomäki, M. Radziwiłł, *Multiplicative functions in short intervals*, arXiv:1501.04585.
- Repo context: issue #2843 (why interface axioms must be exact literature statements), `Problems/tao2015_pipeline.md` (stage engineering).

## 6. Notes / gotchas

- **Decision record (±1 vs S¹):** the interfaces are stated over ℂ-valued unimodular functions.
  The ±1-valued "reduction" is NOT Tao's theorem — restricting to real multiplicative functions
  loses the character-modulated cases and the resulting assumption may be undischargeable. The
  ±1 multiplicative bridge already in `MoltResearch/` remains valuable (it is the hand-off once
  a reduction produces candidates) but must not be baked into interface statements.
- **Deterministic vs stochastic (A):** the paper's reduction produces a *random* completely
  multiplicative `g` with bounded *second moment* of partial sums. The deterministic first-cut
  interface above is intentionally simpler and is implied by the stochastic version; when the
  language layer gains probability packaging, add the stochastic form
  (`𝔼 |∑_{j≤n} g(j)|²` version) as the primary and re-derive the deterministic one. Keep both
  named separately so downstream code never silently assumes the wrong one.
- **Axiom hygiene (hard rule, from #2843):** every interface axiom/class on this card must be a
  named theorem of the literature (or strictly weaker), with the arXiv reference in its
  docstring, and must be stated *existentially/conditionally* exactly as in the source. Any new
  axiom in `Conjectures/` that is not on this card needs its own card first.
- **Division/log conventions:** `logAvgCorr` uses `Real.log N` (junk values at `N ≤ 1` are fine
  — normalize with simp lemmas, don't fight them) and ℂ-division by `n` (never `Nat` division);
  watch coercions in statements, they are the main blind-writing hazard here.
- Local verification: `./scripts/bootstrap.sh` once, then `make ci`; single file:
  `./scripts/check_task.sh <file>`.
