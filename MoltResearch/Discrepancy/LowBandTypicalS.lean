import MoltResearch.Discrepancy.ExceptionalHalaszTwist
import MoltResearch.Discrepancy.BandCapstone

/-!
# The low-frequency energy of the typical-set polynomial

Inclusion--exclusion writes the `typicalS` restriction as `2^J`
level-free twists.  Each twist is completely multiplicative and inherits
half of the base non-pretentiousness strength, so the low-band Halász bound
applies without changing the frequency.  Abel summation against `1/m` is
provided by `cheap_halasz_levelFreeTwist_dirichlet_block`.
-/

namespace MoltResearch

open Finset MeasureTheory ExpSums

/-- A filtered inclusion--exclusion term is exactly the Dirichlet polynomial
of the corresponding level-free twist. -/
theorem sum_filter_eq_levelFreeTwist_dirichlet
    (g : ℕ → ℂ) (S : List (Finset ℕ)) (a b : ℕ) (t : ℝ) :
    ∑ m ∈ (Finset.Ioc a b).filter
        (fun n => ∀ Q ∈ S, ∀ p ∈ Q, ¬ p ∣ n),
        (g m / (m : ℂ)) *
          ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ) =
      ∑ m ∈ Finset.Ioc a b,
        (levelFreeTwist g S m / (m : ℂ)) *
          ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ) := by
  classical
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [levelFreeTwist_eq_if]
  by_cases hm : ∀ Q ∈ S, ∀ p ∈ Q, ¬ p ∣ m
  · rw [if_pos hm, if_pos hm]
  · rw [if_neg hm, if_neg hm]
    simp only [zero_div, zero_mul]

/-- **A2-IV-1, pointwise form.**  The normalized typical-set polynomial on
the low band is at most `2^J` copies of the no-frequency-loss twisted Halász
cost. -/
theorem norm_typicalS_dirichlet_poly_le_low_band
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (x0 : ℕ) (W : ℝ), 0 < W ∧
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → g 1 = 1 →
        (∀ n, ‖g n‖ ≤ 1) →
      ∀ levels : List (Finset ℕ),
        (∀ Q ∈ levels, ∀ p ∈ Q, p.Prime) →
      ∀ a b : ℕ, x0 ≤ a → a < b →
      ∀ D : ℝ, 2 ≤ D →
        (∀ u : ℕ, a ≤ u → u ≤ b → NonPretentiousAt g (2 * D) u) →
      ∀ t : ℝ, |2 * Real.pi * t| ≤ (D / 2) * a →
        ‖∑ m ∈ typicalS a b levels,
            (g m / (m : ℂ)) *
              ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖
          ≤ (2 ^ levels.length : ℕ) *
              cheapTwistedDirichletCost eps W D a b := by
  obtain ⟨x0, W, hW, hblock⟩ :=
    cheap_halasz_levelFreeTwist_dirichlet_block eps heps
  refine ⟨x0, W, hW, ?_⟩
  intro g hcm hg1 hgb levels hlevels a b hxa hab D hD hnp t ht
  refine (norm_sum_typicalS_le_inclexcl a b
    (fun m => (g m / (m : ℂ)) *
      ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)) levels).trans ?_
  let C : ℝ := cheapTwistedDirichletCost eps W D a b
  calc
    (levels.sublists.map fun S =>
        ‖∑ m ∈ (Finset.Ioc a b).filter
            (fun n => ∀ Q ∈ S, ∀ p ∈ Q, ¬ p ∣ n),
          (g m / (m : ℂ)) *
            ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖).sum
        = (levels.sublists.map fun S =>
            ‖∑ m ∈ Finset.Ioc a b,
              (levelFreeTwist g S m / (m : ℂ)) *
                ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖).sum := by
          congr 2
          funext S
          rw [sum_filter_eq_levelFreeTwist_dirichlet]
    _ ≤ (levels.sublists.map fun _ => C).sum := by
          apply List.sum_le_sum
          intro S hS
          exact hblock g hcm hg1 hgb S
            (by
              intro Q hQS p hp
              exact hlevels Q ((List.mem_sublists.mp hS).mem hQS) p hp)
            a b hxa hab D hD hnp t ht
    _ = (2 ^ levels.length : ℕ) *
          cheapTwistedDirichletCost eps W D a b := by
          rw [show (levels.sublists.map fun _ => C) =
              List.replicate levels.sublists.length C from List.map_const,
            List.sum_replicate, List.length_sublists, nsmul_eq_mul]

/-- The set `|t| < K` is the open interval `(-K,K)`. -/
theorem abs_lt_set_eq_Ioo (K : ℝ) :
    {t : ℝ | |t| < K} = Set.Ioo (-K) K := by
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_Ioo, abs_lt]

/-- **A2-IV-1, energy form.**  Integrating the pointwise bound over
`|t| < K` costs exactly the interval length `2K`. -/
theorem integral_norm_typicalS_dirichlet_poly_sq_le_low_band
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (x0 : ℕ) (W : ℝ), 0 < W ∧
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → g 1 = 1 →
        (∀ n, ‖g n‖ ≤ 1) →
      ∀ levels : List (Finset ℕ),
        (∀ Q ∈ levels, ∀ p ∈ Q, p.Prime) →
      ∀ a b : ℕ, x0 ≤ a → a < b →
      ∀ D : ℝ, 2 ≤ D →
        (∀ u : ℕ, a ≤ u → u ≤ b → NonPretentiousAt g (2 * D) u) →
      ∀ K : ℝ, 0 ≤ K → 2 * Real.pi * K ≤ (D / 2) * a →
        (∫ t in {t : ℝ | |t| < K},
          ‖∑ m ∈ typicalS a b levels,
              (g m / (m : ℂ)) *
                ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖^2)
          ≤ 2 * K *
              ((2 ^ levels.length : ℕ) *
                cheapTwistedDirichletCost eps W D a b)^2 := by
  obtain ⟨x0, W, hW, hpoint⟩ :=
    norm_typicalS_dirichlet_poly_le_low_band eps heps
  refine ⟨x0, W, hW, ?_⟩
  intro g hcm hg1 hgb levels hlevels a b hxa hab D hD hnp K hK hfreq
  let P : ℝ → ℂ := fun t =>
    ∑ m ∈ typicalS a b levels,
      (g m / (m : ℂ)) *
        ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)
  let C : ℝ := (2 ^ levels.length : ℕ) *
    cheapTwistedDirichletCost eps W D a b
  have hPc : Continuous P := continuous_char_poly _ _ _
  have hmeas : MeasurableSet {t : ℝ | |t| < K} :=
    measurableSet_lt measurable_abs measurable_const
  have hint : IntegrableOn (fun t => ‖P t‖^2) {t : ℝ | |t| < K} :=
    integrableOn_norm_sq_inner_band P hPc 0 K _ fun t ht =>
      ⟨abs_nonneg t, le_of_lt ht⟩
  have hfin : volume {t : ℝ | |t| < K} ≠ ⊤ := by
    rw [abs_lt_set_eq_Ioo K, Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hmono : (∫ t in {t : ℝ | |t| < K}, ‖P t‖^2) ≤
      ∫ _t in {t : ℝ | |t| < K}, C^2 := by
    refine setIntegral_mono_on hint (integrableOn_const hfin) hmeas ?_
    intro t ht
    have htK : |2 * Real.pi * t| ≤ 2 * Real.pi * K := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)]
      exact mul_le_mul_of_nonneg_left (le_of_lt ht) (by positivity)
    have hnorm : ‖P t‖ ≤ C := by
      exact hpoint g hcm hg1 hgb levels hlevels a b hxa hab D hD hnp t
        (le_trans htK hfreq)
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [abs_lt_set_eq_Ioo K, setIntegral_const,
    Real.volume_real_Ioo_of_le (by linarith), smul_eq_mul] at hmono
  rw [abs_lt_set_eq_Ioo K]
  dsimp only [P, C] at hmono ⊢
  convert hmono using 1 <;> ring

end MoltResearch
