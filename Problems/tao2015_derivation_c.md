# Problem Card: Tao 2015 derivation (C) — EDP conditional on (A)+(B)

Status: active

Companion cards: `Problems/tao2015_analytic_core.md` (blueprint; this card opens its milestone
"(C) first"), `Problems/tao2015_pipeline.md` (stage engineering), `Problems/erdos_discrepancy.md`
(substrate). Paper: T. Tao, *The Erdős discrepancy problem*, arXiv:1509.05363 — this card is §3
(van der Corput) + §4 (generalized Borwein–Choi–Coons), i.e. the proof of the paper's Theorem 1.8
from its Theorem 1.10.

## 0. One-line pitch

The most self-contained of the three discharge milestones: prove that Tao's two deep inputs
actually imply EDP. Landing this turns `stage5_notBounded` from stub-wired to honestly
conditional and retires the Stage-2 stub axiom.

## 1. Natural language statement (faithful structure of the paper)

Dependency graph in the paper (verified against arXiv:1509.05363, ar5iv rendering):

- **Theorem 1.8** (stochastic form of EDP): every stochastic completely multiplicative
  `𝐠 : ℕ → S¹` has `sup_n 𝔼|∑_{j≤n} 𝐠(j)|² = ∞`. (Theorem 1.9 is the measure-theoretic
  restatement: a probability space `(Ω, μ)` and a measurable family `ω ↦ g_ω` of completely
  multiplicative unimodular functions, with `sup_n ∫ |∑_{j≤n} g_ω(j)|² dμ = ∞`.)
- **§2 (input (A), stochastic form)**: Theorem 1.1 (EDP, vector-valued) ⟺ Theorem 1.8. The
  direction needed here: a bounded-discrepancy sequence yields a stochastic completely
  multiplicative counterexample to Theorem 1.8.
- **Theorem 1.10** (input (B), *nonasymptotic* log-averaged two-point Elliott): for affine forms
  `a₁n+b₁`, `a₂n+b₂` with `a₁b₂ − a₂b₁ ≠ 0`, `ε > 0`, `A` large depending on `ε, aᵢ, bᵢ`,
  `x ≥ w ≥ A`, and 1-bounded multiplicative `g₁, g₂`: if
  `∑_{p≤x} (1 − Re(g₁(p)·conj(χ(p))·p^{−it}))/p ≥ A` for all Dirichlet characters `χ` of period
  `≤ A` and all real `|t| ≤ Ax`, then `|∑_{x/w<n≤x} g₁(a₁n+b₁)·g₂(a₂n+b₂)/n| ≤ ε·log w`.
- **Proposition 1.11** (van der Corput argument, §3; *this card's first half*): if
  `𝔼|∑_{j≤n} 𝐠(j)|² ≤ C²` for all `n`, then for large `X` and small `ε`, with probability
  `1 − O(ε)` there exist a stochastic Dirichlet character `𝛘` of period `q = O_{C,ε}(1)` and a
  stochastic real `𝐭 = O_{C,ε}(X)` with `∑_{p≤X} (1 − Re(𝐠(p)·conj(𝛘(p))·p^{−it}))/p ≪_{C,ε} 1`.
  Proved from Theorem 1.10.
- **§4** (generalized Borwein–Choi–Coons; *this card's second half*): a stochastic completely
  multiplicative `𝐠` that (with non-trivial probability) pretends to be `χ(n)·n^{it}` in the
  sense of Proposition 1.11's conclusion has `𝔼|∑_{j≤n} 𝐠(j)|²` unbounded (log-type growth), the
  classical Borwein–Choi–Coons phenomenon for character partial sums, upgraded to the stochastic
  modulated setting.
- **Glue**: Proposition 1.11 + §4 contradict each other under the bounded-second-moment
  hypothesis ⇒ Theorem 1.8 ⇒ (with §2) EDP.

## 2. Formalization target (Lean)

End state: re-prove `Tao2015.stage5_notBounded` from the interfaces, retiring the Stage-2 stub
axiom (`Conjectures/.../TrackCStage2Stub.lean`). Intermediate targets are typed interfaces in
`Conjectures/C0002_erdos_discrepancy/src/` following the established hygiene (classes, no
instances, no axioms; every statement a named theorem of the paper or strictly weaker).

**Interface mismatch to repair first (both are deliberate first-cuts recorded on the blueprint
card):** the existing `FourierReductionAssumption` is the *deterministic* simplification of §2,
and `LogElliottAssumption` is the *asymptotic* special case of Theorem 1.10. Derivation (C) as
in the paper needs the stochastic (A) and the nonasymptotic (B); the current forms should be
re-derived from the upgraded ones (never silently swapped — keep both named).

Indicative signatures (names/homes to be settled in PRs; type-correctness is the deliverable):

```lean
-- Language layer (MoltResearch/): measure-theoretic packaging, Theorem 1.9 style
structure StochasticMultiplicative (Ω : Type*) [MeasureSpace Ω] where
  g : Ω → ℕ → ℂ
  measurable : ∀ n, Measurable fun ω => g ω n
  mul : ∀ᵐ ω, CompletelyMultiplicativeC (g ω)
  unimodular : ∀ᵐ ω, Unimodular (g ω)

noncomputable def sndMomentPartialSum (G : StochasticMultiplicative Ω) (n : ℕ) : ℝ :=
  ∫ ω, ‖apSumC (G.g ω) 1 n‖ ^ 2

-- Interface layer (Conjectures/)
class FourierReductionStochasticAssumption : Prop where …  -- §2 direction, second-moment form
class LogElliottNonasymptoticAssumption : Prop where …     -- Theorem 1.10, all quantifiers

-- Derivation targets
theorem vanDerCorput …        -- Proposition 1.11 from LogElliottNonasymptoticAssumption
theorem borweinChoiCoons …    -- §4: pretentious ⇒ unbounded second moment
theorem theorem18 …           -- Theorem 1.8 from the two above
```

## 3. Dependencies

- In this repo (verified): the ℂ language layer (`CompletelyMultiplicativeC`, `Unimodular`,
  `apSumC` + collapse, `logAvgCorr`, `pretentiousDistSq`), the norm-level cast bridge, the
  Stage 2–5 pipeline, `stage2StubContent_of_univ_multiplicative` (the toy version of the glue).
- In Mathlib: `MeasureTheory` (integration, probability measures), `DirichletCharacter`,
  Dirichlet character orthogonality/partial-sum basics, `cpow`.
- Genuinely new: nonasymptotic pretentious-distance bookkeeping (period-`≤ A` and `|t| ≤ Ax`
  quantifier ranges); stochastic packaging; the Borwein–Choi–Coons growth estimate (the one
  place with real analytic content in this card — everything else is careful bookkeeping).

## 4. Decomposition (mergeable sub-tasks)

Language layer (each: 1 file in `MoltResearch/`, compiles + regression example, no axioms):

(Convention: keep each checkbox on a single line — the CI metadata gate matches `Checklist item:` lines against the card by exact fixed-string grep.)

- [x] Stochastic packaging (Theorem 1.9 style): `StochasticMultiplicative` (measure-theoretic family of completely multiplicative unimodular functions) + `sndMomentPartialSum`, with degenerate simp lemmas and a deterministic-example constructor (a single `g` as a trivial stochastic one).
  (Implemented in `MoltResearch/Discrepancy/StochasticMultiplicative.lean` (on the stable
  surface): the structure over an arbitrary `Measure Ω` with `∀ᵐ` pointwise fields,
  `sndMomentPartialSum` with zero-length simp lemma and nonnegativity, and
  `StochasticMultiplicative.ofDeterministic` with its probability-measure second-moment
  collapse; regression examples in `NormalFormExamples.lean`.)
- [x] Nonasymptotic non-pretentiousness language: bounded-range pretentious distance variants with explicit character-period and `|t|`-range quantifiers matching Theorem 1.10's hypothesis verbatim; relate to the existing `NonPretentious` (asymptotic ⇒ nonasymptotic-for-every-A direction only, stated as a lemma).
  (Implemented: `charTwist` (named `n ↦ χ(n)·nⁱᵗ` comparison), `charTwist_norm_le_one`,
  1-bounded-comparison generalizations of the distance order lemmas, and `NonPretentiousAt`
  (the Theorem-1.10 hypothesis shape) in `MoltResearch/Discrepancy/PretentiousDist.lean`;
  `NonPretentious` refactored over `charTwist` and related via
  `NonPretentious.of_forall_eventually_nonPretentiousAt` in `TrackCStage5Elliott.lean`.
  **Correction to this box's parenthetical:** the derivable direction is the reverse —
  uniform nonasymptotic bounds imply the pointwise asymptotic form; the asymptotic form cannot
  supply the uniformity over `|t| ≤ A·x`, which is exactly why derivation (C) consumes the
  nonasymptotic interface.)

Interface layer (each: 1 file in `Conjectures/`, class + consumer example, no instances/axioms):

- [x] State `FourierReductionStochasticAssumption` (§2 direction: bounded-discrepancy sign sequence ⇒ stochastic completely multiplicative counterexample to Theorem 1.8, second-moment form) and relate it to the existing deterministic `FourierReductionAssumption`.
  (Implemented in `TrackCStage5Fourier.lean` with the nucleus helper `apSumC_one_d`.
  **Correction to this box's original plan** ("re-derive the deterministic from it"): the
  derivable direction is deterministic ⇒ stochastic (point-mass embedding, landed as the
  instance `FourierReductionStochasticAssumption.ofDeterministic`); the converse fails, i.e.
  the deterministic first-cut is the *stronger*, non-literature axiom. Blueprint card §6
  record corrected accordingly. Derivation work must consume the stochastic class.)
- [x] State `LogElliottNonasymptoticAssumption` (Theorem 1.10 verbatim: affine forms, `a₁b₂ − a₂b₁ ≠ 0`, `ε/A/w/x` quantifiers, period-`≤ A` characters, `|t| ≤ Ax`, conclusion `≤ ε log w`) and relate it to the existing asymptotic `LogElliottAssumption`.
  (Implemented in `TrackCStage5Elliott.lean`: the class verbatim on the completely
  multiplicative subclass (strictly weaker, sufficient), window `Ioc ⌊x/w⌋₊ ⌊x⌋₊`, hypothesis
  `NonPretentiousAt g₁ A ⌈x⌉₊` (shown in the docstring to imply the paper's real-truncation
  hypothesis), with a quantifier-instantiating consumer example.
  **Correction to this box's original plan** ("re-derive the asymptotic from it"): the paper's
  asymptotic corollary (arXiv:1509.05422, Cor 1.5) needs the **uniform (inf-form)**
  non-pretentiousness, now defined as `NonPretentiousUniform` (with
  `NonPretentiousUniform.nonPretentious`); the existing pointwise-hypothesis
  `LogElliottAssumption` is a stronger-than-literature statement — demoted to toy-consumer
  convenience, mirroring the deterministic Fourier finding. Faithful asymptotic derivation is
  the new box below.)
- [x] Bridge: `NonPretentiousUniform` implies eventually-`NonPretentiousAt g A x` (finitely many Dirichlet characters of period `≤ A`).
  (Implemented as `NonPretentiousUniform.eventually_nonPretentiousAt` in
  `TrackCStage5Elliott.lean`: moduli range over `Finset.range (⌊A⌋₊ + 1)`, characters per
  modulus are finite via `DirichletCharacter.fintype`, and the per-character eventual bounds
  intersect via `Filter.eventually_all_finset` / `eventually_all`.)
- [x] Derive the faithful asymptotic corollary (Cor 1.5 form: uniform hypothesis, `o(log w(x))` conclusion) from `LogElliottNonasymptoticAssumption` + the bridge.
  (Implemented as `corollary15` in `TrackCStage5Elliott.lean`: `NonPretentiousUniform`
  hypothesis, arbitrary divergent window `w` with eventual `w x ≤ x`, `o(log w x)` in
  `ε`-form; proof composes the nonasymptotic class with
  `NonPretentiousUniform.eventually_nonPretentiousAt`. Full-window `w = id` consumer example.
  Deviations recorded in `Problems/sources/tao2015_statements.md`.)
- [x] State Proposition 1.11 as a typed intermediate interface, so §4 work can consume it before its proof lands.
  (Implemented in `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5VanDerCorput.lean`:
  `VanDerCorputAssumption` — bounded second moment ⇒ probability-`(1 − K·ε)` pretentious event
  with period `≤ Q`, `|t| ≤ T·X`, distance `≤ B` — in the per-sample existential form (strictly
  weaker than the paper's measurable selection; strengthen if §4 needs the selection), with the
  consumer theorem `vanDerCorput_pretentious` and a compile-only §4-call-site example. No
  instance, no axiom: it is the *target* of the van der Corput proof box below.)

Derivation (the real work; open a GitHub issue per box when starting):

- [x] Prove Proposition 1.11 from `LogElliottNonasymptoticAssumption` (the van der Corput expansion of the second moment, averaging/pigeonhole over shifts, contrapositive of Theorem 1.10).
  (Issue #2870, PRs #2874–#2877 + the instance PR. Nucleus substrate: `windowSumC` toolbox,
  van der Corput expansion, log-averaged expansion + pigeonhole, Markov step. The instance
  `vanDerCorputAssumption_of_logElliottNonasymptotic` lives in
  `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5VanDerCorputProof.lean`, with
  `K = 1`, `Q = T = B = A` dominating the finitely many per-pair Elliott thresholds, and
  window `Ioc ⌊X/W⌋₊ X` at `x := (X : ℝ)` — so `⌈x⌉₊ = X` and the flagged truncation
  friction needed no interface amendment; per-sample existential form sufficed, no
  measurable selection needed. Footprints pinned standard-only in `TrackCAxiomAudit.lean`;
  `theorem18_of_logElliottNonasymptotic` records the milestone: Theorem 1.8 now needs only
  the Elliott and §4 inputs.)
- [x] §4, deterministic core: Borwein–Choi–Coons for modulated characters — for a completely multiplicative `g` at bounded pretentious distance from `χ(n)·n^{it}`, the second moment of partial sums grows. Decompose further when opened.
  (DONE 2026-07-16, PRs #2903–#2918: ingredient layer, the (jock)→(contra) chain
  `contra_of_pretentious_window`, the κ-calculus #2911, the endgame series #2914–#2917
  ending in the extractor `exists_H_k_refuting_contra`, and the wrapper #2918.
  Opened, together with the stochastic-upgrade box, as issue #2871. Deep input identified
  while decomposing: the `𝐭`-cutting lemma needs Vinogradov–Korobov-strength zero-free-region
  technology — typed as the interface `VinogradovKorobovAssumption` in
  `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5VinogradovKorobov.lean` (no instance,
  no axiom; ledger entry in `Problems/sources/tao2015_statements.md`). The §4 target is
  `instance [LogElliottNonasymptoticAssumption] [VinogradovKorobovAssumption] :
  BorweinChoiCoonsAssumption`; `theorem18`'s honest deep-input set becomes
  {Elliott, Vinogradov–Korobov, Fourier §2}.)
- [x] §4, stochastic upgrade: from "with probability `1 − O(ε)` pretentious" (Prop 1.11's conclusion) to unbounded `sndMomentPartialSum`, contradicting the standing bound.
  (DONE 2026-07-16, PR #2918: `instance [VinogradovKorobovAssumption] :
  BorweinChoiCoonsAssumption` in `TrackCStage5BCCWrapper.lean` — note the instance needs
  NO Elliott input; the §4 branch consumes only VK. Milestone
  `theorem18_of_logElliott_vinogradovKorobov`: Theorem 1.8 rests on exactly
  {Elliott, Vinogradov–Korobov}. Footprints pinned in `TrackCAxiomAudit.lean`.)
- [x] Glue: Theorem 1.8 (`theorem18`) from the two halves; then Theorem 1.9 restatement.
  (Implemented in `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5Derivation.lean`:
  `theorem18 [VanDerCorputAssumption] [BorweinChoiCoonsAssumption]` by the paper's
  contradiction, plus `notBounded_of_derivation` — EDP from the three typed pieces with **no
  axiom on the path**. The derivation is now reduced to exactly two named proof obligations
  (the §3 and §4 boxes). Theorem 1.9 needs no separate restatement: `StochasticMultiplicative`
  is already the measure-theoretic packaging. Composing the glue also caught a quantifier-order
  bug in `VanDerCorputAssumption` — `K` must precede `ε` to encode `1 − O(ε)` non-vacuously —
  fixed in the same PR, along with factoring the shared `pretentiousEvent` set.)
- [x] §2, Fourier reduction: from a bounded-discrepancy sign sequence, construct the stochastic completely multiplicative counterexample (instance of FourierReductionStochasticAssumption). Decomposed as issue #2920. **Done** (PRs #2921–#2933): unconditional instance in `TrackCStage5FourierProof.lean`; milestone `edp_of_logElliott_vinogradovKorobov` — EDP for all sign sequences on exactly {LogElliottNonasymptoticAssumption, VinogradovKorobovAssumption}, standard axioms only (audit-pinned).
- [x] VK/Littlewood: discharge VinogradovKorobovAssumption down to a standard L-function bound near the 1-line (Mertens floor, Euler-product bridge, LittlewoodLBoundAssumption interface, assembly). Decomposed as issue #2935. **Done** (PRs #2936–#2942): `instance vinogradovKorobov_of_littlewoodLBound`; milestones `theorem18_of_logElliott_littlewood` / `edp_of_logElliott_littlewood` — Theorem 1.8 and EDP on exactly {LogElliottNonasymptoticAssumption, LittlewoodLBoundAssumption}, standard axioms only (audit-pinned). Mertens I & II, Chebyshev θ, and the dyadic prime tail formalized in the nucleus (absent from Mathlib — upstreaming candidates).
- [x] Elliott: discharge LogElliottNonasymptoticAssumption modulo a Matomäki–Radziwiłł interface (entropy toolbox, Pinsker, log-averaged sums, §2 reductions, §3 entropy decrement, assembly). Decomposed as issue #2946. **Done** (65 PRs, #2948–#3006): `elliott_master` in `TrackCStage5Assembly.lean` — the entropy-decrement proof of the nonasymptotic Elliott estimate with every constant explicit — and `instance logElliottNonasymptotic_of_matomakiRadziwill_quadrupleSieve` on exactly {MatomakiRadziwillAssumption, PrimeQuadrupleCountAssumption}; milestone `edp_of_matomakiRadziwill_quadrupleSieve_littlewood` (`TrackCStage5EDPMilestone.lean`) — EDP for all sign sequences on exactly the three cited-input interfaces, standard axioms only (audit-pinned). Shannon entropy toolbox, Pinsker, Chebyshev block lower bounds, Proposition conv, the decrement observable + Hoeffding, the ZMod circle method, and the polyGrid scale selection all formalized en route.
- [x] Littlewood leg: discharge the Weyl-strength L-bound via elementary van der Corput theory (Kusmin-Landau, derivative tests, zeta-block assembly, character twists) and land edp_of_matomakiRadziwill. Campaign #3020, Track L. **Done** (24 units, #3021–#3043): full elementary vdC theory (Kusmin–Landau → derivative tests → Weyl differencing → per-g cascade → scheduled head `zeta_head_bound` ≤ (d−2)/(K+2)+2^{K+7}+3 → telescope tail → `zeta_LSeries_bound` ≤ 8192·log|t|/loglog|t|); character twists dissolved by the unimodular power trick at k = |(ZMod q)ˣ| (no Pólya–Vinogradov); `instance vinogradovKorobov_unconditional`; **`edp_of_matomakiRadziwill` — EDP on exactly {MatomakiRadziwillAssumption}, standard axioms only, audit-pinned.**
- [x] Quadruple sieve: discharge PrimeQuadrupleCountAssumption via a Selberg Λ² upper bound (twin-type sift over the dyadic block, singular-series second moment, additive-quadruple count ≤ C·n₀³/log⁴n₀). Campaign #3004, Track S.
- [ ] Matomäki–Radziwiłł leg: discharge MatomakiRadziwillAssumption on the consumer's major-arc frequency set (weak interface, Vinogradov classification of the θ-large filter, [mrt] A.1/A.2 via Dirichlet-polynomial mean values, Halász, Ramaré decomposition, a θ<1 zero-free region, major-arc assembly, mrp wrapper) and land the unconditional erdos_discrepancy. Campaign #3044, Track R.
- [ ] Endgame: re-prove `stage5_notBounded` from `FourierReductionStochasticAssumption` + `theorem18`, retire the Stage-2 stub axiom, and flip the blueprint card's milestone (C) to done. CI must stay green with the axiom file deleted.

## 5. References / links

- T. Tao, *The Erdős discrepancy problem*, arXiv:1509.05363 (Discrete Analysis 2016). §3
  (Prop 1.11), §4 (generalized Borwein–Choi–Coons), Theorems 1.8–1.10.
- T. Tao, *The logarithmically averaged Chowla and Elliott conjectures for two-point
  correlations*, arXiv:1509.05422 (Forum Math. Pi 2016) — proves Theorem 1.10; stays interface.
- P. Borwein, S. Choi, M. Coons, *Completely multiplicative functions taking values in {−1,1}*,
  Trans. AMS 362 (2010) — the character partial-sum growth phenomenon behind §4.
- Repo context: `Problems/tao2015_analytic_core.md` §6 (decision records: ±1 vs S¹,
  deterministic vs stochastic, axiom hygiene, issue #2843).

## 6. Notes / gotchas

- **Both current Stage-5 interfaces are first-cuts.** Do not build (C) on
  `FourierReductionAssumption`/`LogElliottAssumption` directly — upgrade to the stochastic /
  nonasymptotic forms first (boxes above) and re-derive the old ones, keeping all four named.
  Downstream code must never silently assume the wrong strength (blueprint card §6).
- **Randomness is load-bearing.** The deterministic reduction is genuinely weaker: Prop 1.11's
  pigeonhole runs over the *distribution* of `𝐠`; formalizing with a single deterministic `g`
  makes §4's contradiction unreachable. Theorem 1.9's measure-theoretic phrasing is the
  Lean-friendly one — avoid trying to formalize "random function" any other way.
- **Nonasymptotic quantifiers are the hard bookkeeping.** Theorem 1.10 has five interacting
  parameters (`ε, A, w, x`, character period); getting their dependency order wrong makes the
  interface either false or useless. State it with explicit `∀ε, ∃A₀, ∀A ≥ A₀, …` structure and
  test with a consumer example that instantiates all quantifiers.
- **Junk-value conventions** carry over from the language layer: ℂ-division, `Real.log`
  degeneracy, `cpow` at `0`. The `∑_{x/w<n≤x} …/n` sum needs an `Ioc`-indexed nucleus
  definition — mirror the `logAvgCorr` conventions rather than inventing new ones.
- **Anti-vacuity discipline (issue #2879).** The original unguarded multiplicativity law
  `f (a*b) = f a * f b` for *all* `a b : ℕ` collided with `Unimodular`/`IsSignSequence` at
  `n = 0` and collapsed both completely-multiplicative classes to the constant-1 function —
  `theorem18`'s statement was provable with **no** assumption classes, and
  `FourierReductionStochasticAssumption` was silently equivalent to EDP itself. Both
  definitions are now guarded (`a ≠ 0 → b ≠ 0`), and `NormalFormExamples` +
  `TrackCAxiomAudit` carry Liouville-style inhabitation witnesses (`∃ g, CM ∧ unimodular ∧
  g 2 = −1`, deterministic and stochastic). **Rule**: every statement quantifying over a
  conjunction of predicate classes needs a non-degenerate inhabitation witness in a
  CI-built module — axiom-footprint audits cannot catch definition-level vacuity.
- Local verification: `./scripts/check_task.sh <file>` per file; `make ci` before any PR that
  touches `MoltResearch/`.
