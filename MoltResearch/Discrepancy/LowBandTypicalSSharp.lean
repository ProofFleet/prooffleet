import MoltResearch.Discrepancy.LowBandTypicalS
import MoltResearch.Discrepancy.HalaszSharpEps

/-!
# The low-frequency typical-set polynomial at the sharp Halász cost

The original low-band wrapper used `cheapTwistedDirichletCost`, whose fixed
positive `W` produces a power of `log b`.  This leaf repeats only the
inclusion--exclusion and integration bookkeeping with
`sharpTwistedDirichletCost`.  Its final form uses
`sharpTwistedDirichletCost_le_eps`, so the pointwise saving is uniform in the
scale once the strength and lower endpoint cross fixed thresholds.
-/

namespace MoltResearch

open Finset MeasureTheory ExpSums

/-- **A2-IV-1' — pointwise low-band bound at the sharp cost.** -/
theorem norm_typicalS_dirichlet_poly_le_low_band_sharp
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg1 : g 1 = 1)
    (hgb : ∀ n, ‖g n‖ ≤ 1)
    (levels : List (Finset ℕ))
    (hlevels : ∀ Q ∈ levels, ∀ p ∈ Q, p.Prime)
    (a b : ℕ) (ha : 10 ^ 16 ≤ a) (hab : a < b)
    (D : ℝ) (hD : 2 ≤ D)
    (hnp : ∀ u : ℕ, a ≤ u → u ≤ 3 * b → NonPretentiousAt g (2 * D) u)
    (delta0 : ℝ) (hdelta0 : 0 < delta0) (hdelta1 : delta0 ≤ 1)
    (t : ℝ) (hfreq : |2 * Real.pi * t| ≤ (D / 2) * a) :
    ‖∑ m ∈ typicalS a b levels,
        (g m / (m : ℂ))
          * ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖
      ≤ (2 ^ levels.length : ℕ)
          * sharpTwistedDirichletCost (D / 2) delta0 a b := by
  refine (norm_sum_typicalS_le_inclexcl a b
    (fun m => (g m / (m : ℂ))
      * ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)) levels).trans ?_
  let C : ℝ := sharpTwistedDirichletCost (D / 2) delta0 a b
  calc
    (levels.sublists.map fun S =>
        ‖∑ m ∈ (Finset.Ioc a b).filter
            (fun n => ∀ Q ∈ S, ∀ p ∈ Q, ¬p ∣ n),
          (g m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖).sum
        = (levels.sublists.map fun S =>
            ‖∑ m ∈ Finset.Ioc a b,
              (levelFreeTwist g S m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖).sum := by
          congr 2
          funext S
          rw [sum_filter_eq_levelFreeTwist_dirichlet]
    _ ≤ (levels.sublists.map fun _ => C).sum := by
          apply List.sum_le_sum
          intro S hS
          apply sharp_halasz_twisted_dirichlet_block
            (levelFreeTwist g S)
            (completelyMultiplicativeC_levelFreeTwist g hcm S (by
              intro Q hQS p hp
              exact hlevels Q ((List.mem_sublists.mp hS).mem hQS) p hp))
            (levelFreeTwist_one g hg1 S (by
              intro Q hQS p hp
              exact hlevels Q ((List.mem_sublists.mp hS).mem hQS) p hp))
            (norm_levelFreeTwist_le_one g hgb S) a b ha hab D hD
          · intro u hau hub
            exact nonPretentiousAt_levelFreeTwist g hgb S D (by linarith) u
              (hnp u hau hub)
          · exact hdelta0
          · exact hdelta1
          · exact hfreq
    _ = (2 ^ levels.length : ℕ)
          * sharpTwistedDirichletCost (D / 2) delta0 a b := by
          rw [show (levels.sublists.map fun _ => C) =
              List.replicate levels.sublists.length C from List.map_const,
            List.sum_replicate, List.length_sublists, nsmul_eq_mul]

/-- **A2-IV-1' — low-band energy at the sharp cost.**

Integrating the uniform pointwise estimate over `|t| < K` costs its exact
length `2K`. -/
theorem integral_norm_typicalS_dirichlet_poly_sq_le_low_band_sharp
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg1 : g 1 = 1)
    (hgb : ∀ n, ‖g n‖ ≤ 1)
    (levels : List (Finset ℕ))
    (hlevels : ∀ Q ∈ levels, ∀ p ∈ Q, p.Prime)
    (a b : ℕ) (ha : 10 ^ 16 ≤ a) (hab : a < b)
    (D : ℝ) (hD : 2 ≤ D)
    (hnp : ∀ u : ℕ, a ≤ u → u ≤ 3 * b → NonPretentiousAt g (2 * D) u)
    (delta0 : ℝ) (hdelta0 : 0 < delta0) (hdelta1 : delta0 ≤ 1)
    (K : ℝ) (hK : 0 ≤ K) (hfreq : 2 * Real.pi * K ≤ (D / 2) * a) :
    (∫ t in {t : ℝ | |t| < K},
      ‖∑ m ∈ typicalS a b levels,
          (g m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖ ^ 2)
      ≤ 2 * K * ((2 ^ levels.length : ℕ)
          * sharpTwistedDirichletCost (D / 2) delta0 a b) ^ 2 := by
  let P : ℝ → ℂ := fun t =>
    ∑ m ∈ typicalS a b levels, (g m / (m : ℂ))
      * ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)
  let C : ℝ := (2 ^ levels.length : ℕ)
    * sharpTwistedDirichletCost (D / 2) delta0 a b
  have hPc : Continuous P := continuous_char_poly _ _ _
  have hmeas : MeasurableSet {t : ℝ | |t| < K} :=
    measurableSet_lt measurable_abs measurable_const
  have hint : IntegrableOn (fun t => ‖P t‖ ^ 2) {t : ℝ | |t| < K} :=
    integrableOn_norm_sq_inner_band P hPc 0 K _ fun t ht =>
      ⟨abs_nonneg t, le_of_lt ht⟩
  have hfin : volume {t : ℝ | |t| < K} ≠ ⊤ := by
    rw [abs_lt_set_eq_Ioo K, Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hmono : (∫ t in {t : ℝ | |t| < K}, ‖P t‖ ^ 2)
      ≤ ∫ _t in {t : ℝ | |t| < K}, C ^ 2 := by
    refine setIntegral_mono_on hint (integrableOn_const hfin) hmeas ?_
    intro t ht
    have htK : |2 * Real.pi * t| ≤ 2 * Real.pi * K := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)]
      exact mul_le_mul_of_nonneg_left (le_of_lt ht) (by positivity)
    have hnorm : ‖P t‖ ≤ C :=
      norm_typicalS_dirichlet_poly_le_low_band_sharp g hcm hg1 hgb levels hlevels
        a b ha hab D hD hnp delta0 hdelta0 hdelta1 t (htK.trans hfreq)
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [abs_lt_set_eq_Ioo K, setIntegral_const,
    Real.volume_real_Ioo_of_le (by linarith), smul_eq_mul] at hmono
  rw [abs_lt_set_eq_Ioo K]
  dsimp only [P, C] at hmono ⊢
  convert hmono using 1
  all_goals ring

/-- **A2-IV-1' — the fixed-saving low-band estimate.**

For each `eta` there are fixed scale and strength thresholds.  Above them the
sharp cost is at most `eta * b/(a+1)`, uniformly in `a` and `b`. -/
theorem integral_norm_typicalS_dirichlet_poly_sq_le_low_band_eps
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ∃ (D0 : ℝ) (x0 : ℕ), 2 ≤ D0 ∧ 10 ^ 16 ≤ x0 ∧
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → g 1 = 1 →
        (∀ n, ‖g n‖ ≤ 1) →
      ∀ levels : List (Finset ℕ),
        (∀ Q ∈ levels, ∀ p ∈ Q, p.Prime) →
      ∀ a b : ℕ, x0 ≤ a → a < b → b ≤ 3 * a →
      ∀ D : ℝ, D0 ≤ D →
        (∀ u : ℕ, a ≤ u → u ≤ 3 * b → NonPretentiousAt g (2 * D) u) →
      ∀ K : ℝ, 0 ≤ K → 2 * Real.pi * K ≤ (D / 2) * a →
        (∫ t in {t : ℝ | |t| < K},
          ‖∑ m ∈ typicalS a b levels,
              (g m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖ ^ 2)
          ≤ 2 * K * ((2 ^ levels.length : ℕ)
              * (eta * (b : ℝ) / ((a + 1 : ℕ) : ℝ))) ^ 2 := by
  obtain ⟨Dcost, x0, hDcost, hx0, hcost⟩ :=
    sharpTwistedDirichletCost_le_eps eta heta
  refine ⟨2 * Dcost, x0, by linarith, hx0, ?_⟩
  intro g hcm hg1 hgb levels hlevels a b hxa hab hb3 D hD hnp K hK hfreq
  have ha16 : 10 ^ 16 ≤ a := hx0.trans hxa
  have hD2 : 2 ≤ D := by linarith
  have hdelta0 : 0 < eta / (8 * Real.exp 1) := by positivity
  have hdelta1 : eta / (8 * Real.exp 1) ≤ 1 := by
    have hden : (1 : ℝ) ≤ 8 * Real.exp 1 := by
      nlinarith [Real.exp_one_gt_d9]
    rw [div_le_one (by positivity)]
    exact heta1.trans hden
  have hraw := integral_norm_typicalS_dirichlet_poly_sq_le_low_band_sharp
    g hcm hg1 hgb levels hlevels a b ha16 hab D hD2 hnp
    (eta / (8 * Real.exp 1)) hdelta0 hdelta1 K hK hfreq
  have hcost' : sharpTwistedDirichletCost (D / 2)
      (eta / (8 * Real.exp 1)) a b
      ≤ eta * (b : ℝ) / ((a + 1 : ℕ) : ℝ) :=
    hcost (D / 2) (by linarith) a b hxa hab.le hb3
  have hK0 : 0 ≤ 2 * K := by positivity
  have hpow := pow_le_pow_left₀
    (mul_nonneg (by positivity) (sharpTwistedDirichletCost_nonneg
      (D / 2) (eta / (8 * Real.exp 1)) a b (by linarith) hdelta0
        (by omega) (by omega)))
    (mul_le_mul_of_nonneg_left hcost' (by positivity :
      (0 : ℝ) ≤ (2 ^ levels.length : ℕ))) 2
  exact hraw.trans (mul_le_mul_of_nonneg_left hpow hK0)

end MoltResearch
