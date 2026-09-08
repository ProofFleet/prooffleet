import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5VanDerCorput
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Fourier

/-!
# Track C: Stage 5 — the derivation skeleton composes (Tao 2015, Theorem 1.8 glue)

This file is **Conjectures-only** glue: the typed statement of the §4 input (generalized
Borwein–Choi–Coons) and the **proof that the derivation composes**
(`Problems/tao2015_derivation_c.md`):

- `theorem18` — Theorem 1.8 of arXiv:1509.05363 (every stochastic completely multiplicative
  unimodular function has unbounded second moment of partial sums), proved from
  `[VanDerCorputAssumption]` + `[BorweinChoiCoonsAssumption]` by the paper's contradiction.
- `notBounded_of_derivation` — EDP for all sign sequences from the three typed pieces
  `[FourierReductionStochasticAssumption]` + the two above, with **no axiom anywhere on the
  path** (in particular, not the Stage-2 stub).

With this, the entire derivation is reduced to exactly two named proof obligations: prove
`VanDerCorputAssumption` from `LogElliottNonasymptoticAssumption` (§3) and prove
`BorweinChoiCoonsAssumption` (§4). The glue below is unconditional logic and will not change.

Note on Theorem 1.9: our `StochasticMultiplicative` is already the measure-theoretic packaging,
so `theorem18` *is* the Theorem 1.9 form; no separate restatement is needed.
-/

namespace MoltResearch

namespace Tao2015

open MeasureTheory

/-- **Borwein–Choi–Coons assumption** (Tao 2015, arXiv:1509.05363 §4, contrapositive
consumer form).

A stochastic completely multiplicative unimodular function with uniformly bounded second
moment cannot be persistently pretentious: for every probability constant `K > 0` there is a
small `ε` defeating every constant package `(Q, T, B, X₀)` — i.e. the van der Corput
conclusion at that `ε` fails.

This is the contrapositive of §4's growth statement ("a stochastic completely multiplicative
function that pretends to be `χ(n)·nⁱᵗ` with non-trivial probability has unbounded second
moment"), packaged in exactly the shape the Theorem-1.8 glue consumes. To be proved by the
derivation card's §4 boxes; until then consumers carry it as a hypothesis (no instance, no
nonstandard axiom).
-/
class BorweinChoiCoonsAssumption : Prop where
  not_persistently_pretentious :
    ∀ {Ω : Type} [m : MeasurableSpace Ω] (μ : @Measure Ω m)
      [@IsProbabilityMeasure Ω m μ]
      (G : @StochasticMultiplicative Ω m μ) (C : ℝ),
      (∀ n : ℕ, @sndMomentPartialSum Ω m μ G n ≤ C) →
      ∀ K : ℝ, 0 < K →
        ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
          ∀ Q T B : ℝ, ∀ X₀ : ℕ,
            ¬ (∀ X : ℕ, X₀ ≤ X →
                ENNReal.ofReal (1 - K * ε) ≤ μ (pretentiousEvent G Q T B X))

/-- **Theorem 1.8** (Tao 2015, arXiv:1509.05363), conditional on the two derivation inputs:
every stochastic completely multiplicative unimodular function has unbounded second moment of
partial sums.

The proof is the paper's contradiction, and it is pure glue: a uniform bound `C` feeds the van
der Corput argument, whose persistent pretentious events are exactly what the
Borwein–Choi–Coons branch rules out. (The probability constant from Prop 1.11 is bumped to
`max K 1 > 0` so the §4 input applies; the event bound transfers since `1 − (max K 1)·ε ≤
1 − K·ε`.)
-/
theorem theorem18 [VanDerCorputAssumption] [BorweinChoiCoonsAssumption]
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, sndMomentPartialSum G n ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨K, hK⟩ := VanDerCorputAssumption.pretentious μ G C hC
  obtain ⟨ε, hε0, hε1, hdefeat⟩ :=
    BorweinChoiCoonsAssumption.not_persistently_pretentious μ G C hC (max K 1)
      (lt_of_lt_of_le one_pos (le_max_right K 1))
  obtain ⟨Q, T, B, X₀, hX⟩ := hK ε hε0 hε1
  refine hdefeat Q T B X₀ fun X hXX => le_trans ?_ (hX X hXX)
  apply ENNReal.ofReal_le_ofReal
  have : K * ε ≤ max K 1 * ε := mul_le_mul_of_nonneg_right (le_max_left K 1) hε0.le
  linarith

/-- **EDP from the typed derivation skeleton** — no axiom anywhere on this path (in particular
not the Stage-2 stub): the stochastic Fourier reduction turns a bounded-discrepancy sequence
into a bounded-second-moment stochastic counterexample, which `theorem18` rules out.

This is the shape `stage5_notBounded`'s body will take once `VanDerCorputAssumption` and
`BorweinChoiCoonsAssumption` are discharged from `LogElliottNonasymptoticAssumption` (§3) and
§4 respectively.
-/
theorem notBounded_of_derivation
    [FourierReductionStochasticAssumption]
    [VanDerCorputAssumption] [BorweinChoiCoonsAssumption]
    (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  intro hb
  obtain ⟨Ω, m, μ, hprob, G, C, hC⟩ :=
    FourierReductionStochasticAssumption.reduce f hf hb
  exact theorem18 μ G ⟨C, hC⟩

-- Consumer example (compile-only): the full conditional pipeline in one application.
example [FourierReductionStochasticAssumption]
    [VanDerCorputAssumption] [BorweinChoiCoonsAssumption]
    (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f :=
  notBounded_of_derivation f hf

end Tao2015

end MoltResearch
