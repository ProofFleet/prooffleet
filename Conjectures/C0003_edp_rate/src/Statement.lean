import MoltResearch.Discrepancy.Multiplicative

/-!
# The Erdős discrepancy-growth conjecture

This file records three finite-scale statements about homogeneous arithmetic-progression
sums.  They are propositions, rather than theorem declarations: the logarithmic rate remains
open.  The one theorem at the end is only a quantifier sanity check against the established
qualitative predicate `BoundedDiscrepancy`.

References:

* [Erdős Problems, Problem 67](https://www.erdosproblems.com/67) records Erdős's logarithmic
  conjecture from [Er64b], [Er65b], and [Er81], and the multiplicative special case from [Er85c].
* [McNamara, *Dynamical Methods for the Sarnak and Chowla Conjectures* (2021)](
  https://escholarship.org/uc/item/4wr015m0) proves the wider-range
  `(log log x)^(1/484-o(1))` lower bound encoded below.
-/

namespace MoltResearch

/-- `HasDiscrepancyRateBy g` says that every sign sequence has, by every real scale `x ≥ 2`,
a homogeneous arithmetic-progression partial sum supported inside `md ≤ x` whose absolute
value is at least `g x`.

This is the finite-scale form of the rate conjecture recorded in
[Erdős Problems, Problem 67](https://www.erdosproblems.com/67).
-/
def HasDiscrepancyRateBy (g : ℝ → ℝ) : Prop :=
  ∀ f : ℕ → ℤ, IsSignSequence f →
    ∀ x : ℝ, 2 ≤ x →
      ∃ d m : ℕ, 0 < d ∧ (m * d : ℝ) ≤ x ∧ g x ≤ |(apSum f d m : ℝ)|

/-- Erdős's conjectured sharp logarithmic discrepancy-growth rate.

The formulation `max_{md ≤ x} |∑_{k ≤ m} f(kd)| ≫ log x` is attributed to Erdős [Er64b,
Er65b, Er81] by [Erdős Problems, Problem 67](https://www.erdosproblems.com/67).
-/
def ErdosDiscrepancyRateConjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧ HasDiscrepancyRateBy (fun x => c * Real.log x)

/-- McNamara's wider-range discrepancy-rate statement.

For every positive loss `ε`, this encodes
`max_{m ≤ x} max_{d ≤ exp x} |∑_{k ≤ m} f(kd)| ≫
  (log log x)^(1/484-ε)` uniformly over sign sequences, beyond a sufficiently large scale.
This is the usual quantified reading of the exponent `1/484-o(1)` in McNamara's 2021 thesis;
see [the thesis record](https://escholarship.org/uc/item/4wr015m0) and
[Erdős Problems, Problem 67](https://www.erdosproblems.com/67).
-/
def McNamaraDiscrepancyRateStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < (1 : ℝ) / 484 →
    ∃ c x₀ : ℝ, 0 < c ∧ 2 ≤ x₀ ∧
      ∀ f : ℕ → ℤ, IsSignSequence f →
        ∀ x : ℝ, x₀ ≤ x →
          ∃ d m : ℕ, 0 < d ∧ (m : ℝ) ≤ x ∧ (d : ℝ) ≤ Real.exp x ∧
            c * Real.rpow (Real.log (Real.log x)) ((1 : ℝ) / 484 - ε) ≤
              |(apSum f d m : ℝ)|

/-- Erdős's logarithmic-rate conjecture restricted to completely multiplicative sign
sequences, stated after the standard multiplicative collapse to step `d = 1`.

Erdős asked for the multiplicative special case in [Er85c], as recorded by
[Erdős Problems, Problem 67](https://www.erdosproblems.com/67).  The equivalence between all
homogeneous steps and step one for such a sequence is formalized by
`CompletelyMultiplicative.discrepancy_eq_discrepancy_one`.
-/
def MultiplicativeErdosDiscrepancyRateConjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ f : ℕ → ℤ, IsSignSequence f → CompletelyMultiplicative f →
      ∀ x : ℝ, 2 ≤ x →
        ∃ m : ℕ, (m : ℝ) ≤ x ∧ c * Real.log x ≤ |(apSum f 1 m : ℝ)|

/-- Sanity check: if the finite-scale rate statement holds for every constant natural lower
bound, then every sign sequence has unbounded discrepancy.

Quantifying over all constants is essential: one fixed constant lower bound does not contradict
`BoundedDiscrepancy`, while qualitative unboundedness alone does not locate a witness below every
prescribed finite scale.
-/
theorem not_boundedDiscrepancy_of_hasDiscrepancyRateBy_const
    (h : ∀ C : ℕ, HasDiscrepancyRateBy (fun _ => (C : ℝ)))
    (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  rintro ⟨B, hB⟩
  obtain ⟨d, m, hd, _, hlarge⟩ := h (B + 1) f hf 2 le_rfl
  have hsmall : |(apSum f d m : ℝ)| ≤ (B : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast hB d m hd
  have hlarge' : ((B + 1 : ℕ) : ℝ) ≤ |(apSum f d m : ℝ)| := by
    simpa using hlarge
  have himpossibleReal : ((B + 1 : ℕ) : ℝ) ≤ (B : ℝ) := by
    exact hlarge'.trans hsmall
  have himpossible : B + 1 ≤ B := by
    exact_mod_cast himpossibleReal
  omega

end MoltResearch
