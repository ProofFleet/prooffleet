import MoltResearch.Discrepancy
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5MatomakiRadziwill

/-!
# Track C: Stage 5 — the major-arc Matomäki–Radziwiłł interface (R1 of issue #3044)

The **weak form** of the Matomäki–Radziwiłł interface, restricted to major-arc
modulation frequencies: the bound of `MatomakiRadziwillAssumption` is only asserted
for `α` within `C·(log H)^B/(H·q)` of a rational `a/q` with denominator
`q ≤ C·(log H)^B`.

This is the form the Erdős-discrepancy application actually needs. The consumer
(`elliott_master`) feeds the interface only frequencies `ξ/J` at which a dyadic
prime-block exponential sum is within a constant-times-`ε` factor of its trivial
(Mertens) size; by Vinogradov's estimates for exponential sums over primes, such
frequencies lie in major arcs of exactly this polylogarithmic-denominator shape
(arXiv:1509.05422, remarks following Proposition `mrp` and in §5: for conjugate-pair
correlations `c_p = 1`, only the major-arc case of [mrt] is required, and
[mrt, Lemma 2.2 + Theorem 2.3] may be replaced by the simpler [mrt, Theorem A.1]).

Design notes (Track R, issue #3044):

- The arc parameters `C, B` are quantified **outside** `H₀`, and the threshold `A₀`
  is chosen **after** `H`: the load-bearing quantifier order (`H` before `A`) of the
  strong interface is preserved verbatim.
- The arc family is polylogarithmic in `H` (not bounded), because the classification
  of an `ε`-fraction-of-trivial prime-block sum produces denominators up to
  `C(ε)·(log H)^B`; the [mrt] major-arc machinery tolerates any such family (its `W`
  parameter may be taken `≫ (log H)^B`).
- No instance of this class is (or may be) declared until the major-arc case of the
  Matomäki–Radziwiłł theorem is actually formalized; consumers carry it as a
  hypothesis.  The frozen all-`α` interface `MatomakiRadziwillAssumption` remains
  intact; the instance below records only the trivial weakening direction.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- **Major-arc Matomäki–Radziwiłł assumption** (arXiv:1509.05422, Proposition
`mrp`, ε-form, restricted to major arcs; discharged via [mrt, Theorem A.1] and the
major-arc analysis of [mrt, §Proof of major arc estimate]): log-averaged
short-interval character-modulated means of non-pretentious unimodular completely
multiplicative functions are `o_{H→∞}(log w)`, uniformly over modulation frequencies
lying in major arcs with polylogarithmic denominator and width. -/
class MatomakiRadziwillMajorArcAssumption : Prop where
  bound :
    ∀ ε C : ℝ, ∀ B : ℕ, 0 < ε → 0 < C →
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
                        g (n + j) * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (α : ℂ))‖
                      / ((H : ℝ) * (n : ℝ))
                  ≤ ε * Real.log w

/-- Consumer-facing restatement. -/
theorem matomakiRadziwillMajorArc_bound [inst : MatomakiRadziwillMajorArcAssumption]
    {ε C : ℝ} (B : ℕ) (hε : 0 < ε) (hC : 0 < C) :
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
                      g (n + j) * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (α : ℂ))‖
                    / ((H : ℝ) * (n : ℝ))
                ≤ ε * Real.log w :=
  inst.bound ε C B hε hC

/-- The trivial weakening direction: the frozen all-`α` interface implies the
major-arc interface (the arc data is simply discarded).  Kept as an instance so the
relationship between the two interfaces is machine-checked; no instance of the
premise exists or may be declared. -/
instance (priority := 90) MatomakiRadziwillMajorArcAssumption.ofAllAlpha
    [MatomakiRadziwillAssumption] : MatomakiRadziwillMajorArcAssumption where
  bound ε _C _B hε _hC := by
    obtain ⟨H₀, hH₀⟩ := matomakiRadziwill_bound hε
    exact ⟨H₀, fun H hH => by
      obtain ⟨A₀, hA₀⟩ := hH₀ H hH
      exact ⟨A₀, fun A hA hA1 x w hAw hwx g hcm huni hnp α _a _q _hq _hqB _harc =>
        hA₀ A hA hA1 x w hAw hwx g hcm huni hnp α⟩⟩

-- Consumer example (compile-only): the zero-frequency specialization through the
-- major-arc window `a = 0, q = 1, B = 0, C = 1` — the arc hypotheses close by
-- `norm_num`-level arithmetic, so downstream reworks can instantiate the arc data
-- without bespoke lemmas.
example [MatomakiRadziwillMajorArcAssumption] {ε : ℝ} (hε : 0 < ε) :
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
  obtain ⟨H₀, hH₀⟩ := matomakiRadziwillMajorArc_bound (C := 1) 0 hε one_pos
  refine ⟨H₀, fun H hH => ?_⟩
  obtain ⟨A₀, hA₀⟩ := hH₀ H hH
  refine ⟨A₀, fun A hA hA1 x w hAw hwx g hcm huni hnp => ?_⟩
  have harc : |(0 : ℝ) - ((0 : ℤ) : ℝ) / ((1 : ℕ) : ℝ)|
      ≤ 1 * Real.log H ^ 0 / ((H : ℝ) * ((1 : ℕ) : ℝ)) := by
    simp only [Int.cast_zero, Nat.cast_one, zero_div, sub_zero, abs_zero, pow_zero,
      mul_one, one_div]
    positivity
  exact hA₀ A hA hA1 x w hAw hwx g hcm huni hnp 0 0 1 le_rfl
    (by simp) harc

end Tao2015

end MoltResearch
