import MoltResearch.Discrepancy
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Elliott

/-!
# Track C: Stage 5 — the Matomäki–Radziwiłł interface (E4 of issue #2946)

The **permanent analytic input** of the Elliott campaign: short-interval averages of a
non-pretentious multiplicative function, modulated by additive characters, are small in
log-average (arXiv:1509.05422, Proposition `mrp`, which the paper derives from
Matomäki–Radziwiłł–Tao [mrt, Lemma 2.2 + Theorem 2.3]):

  `sup_α ∑_{x/w < n ≤ x} (1/(Hn)) · |∑_{j=1}^H g(n+j) e(jα)| = o_{H → ∞}(log w)`,

uniformly over the window and over unimodular completely multiplicative `g` that are
non-pretentious at strength `A`. This is the **only** way the §3 entropy decrement
argument consumes the non-pretentiousness hypothesis.

For the Erdős-discrepancy application the correlations are conjugate pairs (`c_p = 1`),
so only the *major-arc* case of [mrt] (Theorem A.1 there) is ultimately required — the
interface below is nevertheless stated for all `α` as in the source, since that is the
shape Proposition `conv` consumes.

Encoded in `ε`-form with the paper's quantifier order (`H` before `A`: the scale range
is fixed before the pretentiousness strength). No instance of this class is (or may be)
declared until the Matomäki–Radziwiłł theorem is actually formalized; consumers carry
it as a hypothesis.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- **Matomäki–Radziwiłł assumption** (arXiv:1509.05422, Proposition `mrp`, ε-form):
log-averaged short-interval character-modulated means of non-pretentious unimodular
completely multiplicative functions are `o_{H→∞}(log w)`, uniformly in the modulation,
the window, and the function. -/
class MatomakiRadziwillAssumption : Prop where
  bound :
    ∀ ε : ℝ, 0 < ε →
      ∃ H₀ : ℕ, ∀ H : ℕ, H₀ ≤ H →
        ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A → 1 ≤ A →
          ∀ x w : ℝ, A ≤ w → w ≤ x →
            ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → Unimodular g →
              NonPretentiousAt g A ⌈x⌉₊ →
              ∀ α : ℝ,
                ∑ n ∈ Finset.Ioc ⌊x / w⌋₊ ⌊x⌋₊,
                    ‖∑ j ∈ Finset.Icc 1 H,
                        g (n + j) * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (α : ℂ))‖
                      / ((H : ℝ) * (n : ℝ))
                  ≤ ε * Real.log w

/-- Consumer-facing restatement. -/
theorem matomakiRadziwill_bound [inst : MatomakiRadziwillAssumption] {ε : ℝ}
    (hε : 0 < ε) :
    ∃ H₀ : ℕ, ∀ H : ℕ, H₀ ≤ H →
      ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A → 1 ≤ A →
        ∀ x w : ℝ, A ≤ w → w ≤ x →
          ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → Unimodular g →
            NonPretentiousAt g A ⌈x⌉₊ →
            ∀ α : ℝ,
              ∑ n ∈ Finset.Ioc ⌊x / w⌋₊ ⌊x⌋₊,
                  ‖∑ j ∈ Finset.Icc 1 H,
                      g (n + j) * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (α : ℂ))‖
                    / ((H : ℝ) * (n : ℝ))
                ≤ ε * Real.log w :=
  inst.bound ε hε

-- Consumer example (compile-only): the zero-frequency specialization — the plain
-- log-averaged short-interval mean value, the α = 0 case the major-arc analysis
-- bootstraps from.
example [MatomakiRadziwillAssumption] {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ : ℕ, ∀ H : ℕ, H₀ ≤ H →
      ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A → 1 ≤ A →
        ∀ x w : ℝ, A ≤ w → w ≤ x →
          ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → Unimodular g →
            NonPretentiousAt g A ⌈x⌉₊ →
            ∑ n ∈ Finset.Ioc ⌊x / w⌋₊ ⌊x⌋₊,
                ‖∑ j ∈ Finset.Icc 1 H,
                    g (n + j) * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * ((0 : ℝ) : ℂ))‖
                  / ((H : ℝ) * (n : ℝ))
              ≤ ε * Real.log w := by
  obtain ⟨H₀, hH₀⟩ := matomakiRadziwill_bound hε
  exact ⟨H₀, fun H hH => by
    obtain ⟨A₀, hA₀⟩ := hH₀ H hH
    exact ⟨A₀, fun A hA hA1 x w hAw hwx g hcm huni hnp =>
      hA₀ A hA hA1 x w hAw hwx g hcm huni hnp 0⟩⟩

end Tao2015

end MoltResearch
