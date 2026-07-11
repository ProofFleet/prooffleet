import MoltResearch.Discrepancy

/-!
# Track C: Stage 5 interface — van der Corput conclusion (Tao 2015, Proposition 1.11)

This file is **Conjectures-only** glue: the typed statement of Proposition 1.11 of
arXiv:1509.05363 (§3), as an intermediate interface so the §4 (generalized
Borwein–Choi–Coons) work can consume it before its proof lands
(`Problems/tao2015_derivation_c.md`).

**Proposition 1.11 (van der Corput argument):** if a stochastic completely multiplicative
unimodular `𝐠` has uniformly bounded second moment of partial sums, then for every small
`ε > 0` there are constants (depending on the bound and `ε`) such that for all large
truncations `X`, with probability `≥ 1 − K·ε` the sample `𝐠(ω)` *pretends* to be some
character-modulated twist `χ(n)·nⁱᵗ` with period `≤ Q` and `|t| ≤ T·X`, at bounded squared
pretentious distance `≤ B`.

Encoding notes:
- The pretentious event is the named set `pretentiousEvent`, shared with the §4 interface and
  the Theorem-1.8 glue (`TrackCStage5Derivation.lean`).
- **Quantifier order matters and was fixed once** (caught by the Theorem-1.8 glue, the first
  real consumer): the probability constant `K` is produced *before* `ε`, encoding the paper's
  `1 − O(ε)` — the implied constant may depend on the bound `C` (weaker than the source's
  absolute constant, hygiene-safe) but **not** on `ε`, otherwise the statement is vacuous for
  consumers (`K = 1/ε` would satisfy it).
- The paper's conclusion produces a *stochastic* (measurable) selection `(𝛘, 𝐭)`; the statement
  below only asserts the per-sample existential on a large-probability set — strictly weaker.
  If the §4 formalization turns out to need the measurable selection, strengthen this interface
  then (flagged on the derivation card).
- This was stated as a **target to be proved** from `LogElliottNonasymptoticAssumption`
  (derivation card), not a standing axiom. The proof has since landed:
  `TrackCStage5VanDerCorputProof.lean` provides the instance
  `[LogElliottNonasymptoticAssumption] → VanDerCorputAssumption` (no axiom — the Elliott
  input remains a hypothesis class). Consumers may still carry `VanDerCorputAssumption`
  as a hypothesis; under an Elliott hypothesis it now resolves automatically.
-/

namespace MoltResearch

namespace Tao2015

open MeasureTheory

variable {Ω : Type} [MeasurableSpace Ω]

/-- The pretentious event at truncation `X` with constants `(Q, T, B)`: the set of samples
whose sequence is at squared pretentious distance `≤ B` from some character twist with period
`≤ Q` and frequency `|t| ≤ T·X`.

Shared vocabulary between Proposition 1.11 (which concludes this has large probability) and
the §4 Borwein–Choi–Coons branch (which shows that is incompatible with bounded second
moments). -/
def pretentiousEvent {μ : Measure Ω} (G : StochasticMultiplicative μ)
    (Q T B : ℝ) (X : ℕ) : Set Ω :=
  {ω : Ω | ∃ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
    (q : ℝ) ≤ Q ∧ |t| ≤ T * X ∧
    pretentiousDistSq (G.g ω) (charTwist q χ t) X ≤ B}

/-- **Van der Corput assumption** (Tao 2015, arXiv:1509.05363, Proposition 1.11; per-sample
existential form).

A stochastic completely multiplicative unimodular function with uniformly bounded second
moment of partial sums is, with probability `1 − K·ε` at every large truncation `X`,
pretentious toward some character twist with controlled period, frequency, and distance. The
probability constant `K` depends only on the second-moment bound (not on `ε`).

To be proved from `LogElliottNonasymptoticAssumption` (the derivation card's van der Corput
box); until then consumers carry it as a hypothesis.
-/
class VanDerCorputAssumption : Prop where
  pretentious :
    ∀ {Ω : Type} [m : MeasurableSpace Ω] (μ : @Measure Ω m)
      [@IsProbabilityMeasure Ω m μ]
      (G : @StochasticMultiplicative Ω m μ) (C : ℝ),
      (∀ n : ℕ, @sndMomentPartialSum Ω m μ G n ≤ C) →
      ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∃ Q T B : ℝ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
          ENNReal.ofReal (1 - K * ε) ≤ μ (pretentiousEvent G Q T B X)

/-- Consumer-facing restatement as a plain theorem, so §4 call sites can use it without
projecting the class field. -/
theorem vanDerCorput_pretentious [inst : VanDerCorputAssumption]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) {C : ℝ}
    (hC : ∀ n : ℕ, sndMomentPartialSum G n ≤ C) :
    ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ Q T B : ℝ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        ENNReal.ofReal (1 - K * ε) ≤ μ (pretentiousEvent G Q T B X) :=
  inst.pretentious μ G C hC

-- Consumer example (compile-only): the §4 call site — a bounded-second-moment stochastic
-- counterexample hands the Borwein–Choi–Coons branch its large-probability pretentious
-- events, with the probability constant fixed before ε is chosen.
example [VanDerCorputAssumption]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) (hC : ∀ n : ℕ, sndMomentPartialSum G n ≤ 100) :
    ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ Q T B : ℝ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        ENNReal.ofReal (1 - K * ε) ≤ μ (pretentiousEvent G Q T B X) :=
  vanDerCorput_pretentious G hC

end Tao2015

end MoltResearch
