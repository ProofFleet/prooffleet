import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2Window

/-!
# Track R A2-V'-1: low band from the single top-scale hypothesis

`SliceMeanSquareA2` supplies `NonPretentiousAt g A0 (2*A+1)`, not a family
of non-pretentiousness hypotheses at every prefix.  The sharp Halasz window
bridge was designed for precisely this quantifier order: it descends from the
one top scale, paying the explicit Mertens loss.  This file combines that
bridge with the base/ladder split, leaving only the two numerical top-scale
conditions which the final `A0` choice must satisfy.
-/

namespace MoltResearch

namespace Tao2015

open Real Finset MeasureTheory ExpSums

/-- Pointwise split low-band bound obtained from one top-scale
`NonPretentiousAt` hypothesis.  Inclusion--exclusion is confined to `base`;
the growing ladder is paid by its sifted logarithmic mass. -/
theorem norm_typicalS_dirichlet_poly_le_low_band_top_split
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg1 : g 1 = 1)
    (hg : ∀ n, ‖g n‖ ≤ 1)
    (base ladder : List (Finset ℕ))
    (hbase : ∀ Q ∈ base, ∀ p ∈ Q, p.Prime)
    (a b : ℕ) (ha : cellHalaszThreshold ≤ a) (hab : a < b)
    (A0 : ℝ) (N : ℕ) (hA0 : 1 ≤ A0)
    (hNP : NonPretentiousAt g A0 N) (h3bN : 3 * b ≤ N)
    (D delta0 K : ℝ) (hD : 1 ≤ D)
    (hdelta0 : 0 < delta0) (hdelta1 : delta0 ≤ 1)
    (hrange : 2 * Real.pi * K +
        2 * Real.pi * (((halaszM N : ℕ) : ℝ) + 1) ≤ A0 * (N : ℝ))
    (hstrength : 2 * D ≤ A0 -
      2 * (Real.log (Real.log (N : ℝ)) -
        Real.log (Real.log (a : ℝ)) + 12))
    (t : ℝ) (ht : |t| ≤ K) :
    ‖∑ m ∈ typicalS a b (base ++ ladder),
        (g m / (m : ℂ)) *
          ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖
      ≤ (2 ^ base.length : ℕ) *
          sharpTwistedDirichletCost D delta0 a b +
        ladderSiftedLogMass a b ladder := by
  have ha16 : 10 ^ 16 ≤ a := by simpa [cellHalaszThreshold] using ha
  have hbasePoly :
      ‖∑ m ∈ typicalS a b base,
          (g m / (m : ℂ)) *
            ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖
        ≤ (2 ^ base.length : ℕ) *
            sharpTwistedDirichletCost D delta0 a b := by
    refine (norm_sum_typicalS_le_inclexcl a b
      (fun m => (g m / (m : ℂ)) *
        ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)) base).trans ?_
    let C : ℝ := sharpTwistedDirichletCost D delta0 a b
    calc
      (base.sublists.map fun S =>
          ‖∑ m ∈ (Finset.Ioc a b).filter
              (fun n => ∀ Q ∈ S, ∀ p ∈ Q, ¬p ∣ n),
            (g m / (m : ℂ)) *
              ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖).sum
          = (base.sublists.map fun S =>
              ‖∑ m ∈ Finset.Ioc a b,
                (levelFreeTwist g S m / (m : ℂ)) *
                  ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖).sum := by
            congr 2
            funext S
            rw [sum_filter_eq_levelFreeTwist_dirichlet]
      _ ≤ (base.sublists.map fun _ => C).sum := by
            apply List.sum_le_sum
            intro S hS
            apply sharp_halasz_twisted_dirichlet_block_window
              (levelFreeTwist g S)
              (completelyMultiplicativeC_levelFreeTwist g hcm S (by
                intro Q hQS p hp
                exact hbase Q ((List.mem_sublists.mp hS).mem hQS) p hp))
              (levelFreeTwist_one g hg1 S (by
                intro Q hQS p hp
                exact hbase Q ((List.mem_sublists.mp hS).mem hQS) p hp))
              (norm_levelFreeTwist_le_one g hg S) a b ha16 hab D hD t
            · intro u hau hub
              apply halaszWindowAt_levelFreeTwist_archTwist g hg S D
                (2 * Real.pi * t) u
              apply halaszWindowAt_twist_of_top g hg A0 N hNP hA0 K
                hrange a (by omega) D hstrength t ht u
              · exact hau
              · exact hub.trans h3bN
            · exact hdelta0
            · exact hdelta1
      _ = (2 ^ base.length : ℕ) *
            sharpTwistedDirichletCost D delta0 a b := by
          rw [show (base.sublists.map fun _ => C) =
              List.replicate base.sublists.length C from List.map_const,
            List.sum_replicate, List.length_sublists, nsmul_eq_mul]
  let Pfull : ℂ := ∑ m ∈ typicalS a b (base ++ ladder),
    (g m / (m : ℂ)) *
      ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)
  let Pbase : ℂ := ∑ m ∈ typicalS a b base,
    (g m / (m : ℂ)) *
      ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)
  change ‖Pfull‖ ≤ _
  have hdiff : ‖Pfull - Pbase‖ ≤ ladderSiftedLogMass a b ladder := by
    dsimp only [Pfull, Pbase]
    exact norm_typicalS_append_poly_sub_le g hg a b base ladder t
  have hbasePoly' : ‖Pbase‖ ≤
      (2 ^ base.length : ℕ) *
        sharpTwistedDirichletCost D delta0 a b := by
    simpa only [Pbase] using hbasePoly
  calc
    ‖Pfull‖ = ‖(Pfull - Pbase) + Pbase‖ := by
      congr 1
      ring
    _ ≤ ‖Pfull - Pbase‖ + ‖Pbase‖ := norm_add_le _ _
    _ ≤ ladderSiftedLogMass a b ladder +
          (2 ^ base.length : ℕ) *
            sharpTwistedDirichletCost D delta0 a b :=
        add_le_add hdiff hbasePoly'
    _ = _ := add_comm _ _

/-- Integrated version of the top-scale split. -/
theorem integral_norm_typicalS_dirichlet_poly_sq_le_low_band_top_split
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg1 : g 1 = 1)
    (hg : ∀ n, ‖g n‖ ≤ 1)
    (base ladder : List (Finset ℕ))
    (hbase : ∀ Q ∈ base, ∀ p ∈ Q, p.Prime)
    (a b : ℕ) (ha : cellHalaszThreshold ≤ a) (hab : a < b)
    (A0 : ℝ) (N : ℕ) (hA0 : 1 ≤ A0)
    (hNP : NonPretentiousAt g A0 N) (h3bN : 3 * b ≤ N)
    (D delta0 K : ℝ) (hD : 1 ≤ D)
    (hdelta0 : 0 < delta0) (hdelta1 : delta0 ≤ 1)
    (hK : 0 ≤ K)
    (hrange : 2 * Real.pi * K +
        2 * Real.pi * (((halaszM N : ℕ) : ℝ) + 1) ≤ A0 * (N : ℝ))
    (hstrength : 2 * D ≤ A0 -
      2 * (Real.log (Real.log (N : ℝ)) -
        Real.log (Real.log (a : ℝ)) + 12)) :
    (∫ t in {t : ℝ | |t| < K},
      ‖∑ m ∈ typicalS a b (base ++ ladder),
          (g m / (m : ℂ)) *
            ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖ ^ 2)
      ≤ 2 * K * ((2 ^ base.length : ℕ) *
          sharpTwistedDirichletCost D delta0 a b +
        ladderSiftedLogMass a b ladder) ^ 2 := by
  let P : ℝ → ℂ := fun t =>
    ∑ m ∈ typicalS a b (base ++ ladder), (g m / (m : ℂ)) *
      ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)
  let C : ℝ := (2 ^ base.length : ℕ) *
      sharpTwistedDirichletCost D delta0 a b +
    ladderSiftedLogMass a b ladder
  have hPc : Continuous P := continuous_char_poly _ _ _
  have hmeas : MeasurableSet {t : ℝ | |t| < K} :=
    measurableSet_lt measurable_abs measurable_const
  have hint : IntegrableOn (fun t => ‖P t‖ ^ 2) {t : ℝ | |t| < K} :=
    integrableOn_norm_sq_inner_band P hPc 0 K _ fun t ht =>
      ⟨abs_nonneg t, le_of_lt ht⟩
  have hfin : volume {t : ℝ | |t| < K} ≠ ⊤ := by
    rw [abs_lt_set_eq_Ioo K, Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hmono : (∫ t in {t : ℝ | |t| < K}, ‖P t‖ ^ 2) ≤
      ∫ _t in {t : ℝ | |t| < K}, C ^ 2 := by
    refine setIntegral_mono_on hint (integrableOn_const hfin) hmeas ?_
    intro t ht
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_typicalS_dirichlet_poly_le_low_band_top_split
        g hcm hg1 hg base ladder hbase a b ha hab A0 N hA0 hNP h3bN
        D delta0 K hD hdelta0 hdelta1 hrange hstrength t (le_of_lt ht)) 2
  rw [abs_lt_set_eq_Ioo K, setIntegral_const,
    Real.volume_real_Ioo_of_le (by linarith), smul_eq_mul] at hmono
  rw [abs_lt_set_eq_Ioo K]
  dsimp only [P, C] at hmono ⊢
  convert hmono using 1
  all_goals ring

/-- Fixed-saving form of the top-scale low band.  The chosen
`delta0 = eta/(8e)` and all constants agree with
`sharpTwistedDirichletCost_le_eps`. -/
theorem integral_norm_typicalS_dirichlet_poly_sq_le_low_band_top_split_eps
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ∃ (D0 : ℝ) (x0 : ℕ), 1 ≤ D0 ∧ cellHalaszThreshold ≤ x0 ∧
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → g 1 = 1 →
        (∀ n, ‖g n‖ ≤ 1) →
      ∀ base ladder : List (Finset ℕ),
        (∀ Q ∈ base, ∀ p ∈ Q, p.Prime) →
      ∀ a b : ℕ, x0 ≤ a → a < b → b ≤ 3 * a →
      ∀ A0 : ℝ, 1 ≤ A0 → ∀ N : ℕ,
        NonPretentiousAt g A0 N → 3 * b ≤ N →
      ∀ D : ℝ, D0 ≤ D → ∀ K : ℝ, 0 ≤ K →
        2 * Real.pi * K +
            2 * Real.pi * (((halaszM N : ℕ) : ℝ) + 1) ≤ A0 * (N : ℝ) →
        2 * D ≤ A0 -
          2 * (Real.log (Real.log (N : ℝ)) -
            Real.log (Real.log (a : ℝ)) + 12) →
      ∀ Rem : ℝ, 0 ≤ Rem → ladderSiftedLogMass a b ladder ≤ Rem →
        (∫ t in {t : ℝ | |t| < K},
          ‖∑ m ∈ typicalS a b (base ++ ladder),
              (g m / (m : ℂ)) *
                ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖ ^ 2)
          ≤ 2 * K * ((2 ^ base.length : ℕ) *
              (eta * (b : ℝ) / ((a + 1 : ℕ) : ℝ)) + Rem) ^ 2 := by
  obtain ⟨Dcost, x0, hDcost, hx0, hcost⟩ :=
    sharpTwistedDirichletCost_le_eps eta heta
  refine ⟨max 1 Dcost, max cellHalaszThreshold x0, le_max_left _ _,
    le_max_left _ _, ?_⟩
  intro g hcm hg1 hg base ladder hbase a b hxa hab hb3 A0 hA0 N hNP
    h3bN D hD K hK hrange hstrength Rem hRem0 hRem
  have hx0a : x0 ≤ a := (le_max_right _ _).trans hxa
  have hthreshold : cellHalaszThreshold ≤ a :=
    (le_max_left _ _).trans hxa
  have hDcostD : Dcost ≤ D := (le_max_right _ _).trans hD
  have hD1 : 1 ≤ D := (le_max_left _ _).trans hD
  have hdelta0 : 0 < eta / (8 * Real.exp 1) := by positivity
  have hdelta1 : eta / (8 * Real.exp 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [Real.exp_one_gt_d9]
  have hraw := integral_norm_typicalS_dirichlet_poly_sq_le_low_band_top_split
    g hcm hg1 hg base ladder hbase a b hthreshold hab A0 N hA0 hNP h3bN
    D (eta / (8 * Real.exp 1)) K hD1 hdelta0 hdelta1 hK hrange hstrength
  have hcost' : sharpTwistedDirichletCost D
      (eta / (8 * Real.exp 1)) a b ≤
        eta * (b : ℝ) / ((a + 1 : ℕ) : ℝ) :=
    hcost D hDcostD a b hx0a hab.le hb3
  have hmain :
      (2 ^ base.length : ℕ) *
          sharpTwistedDirichletCost D (eta / (8 * Real.exp 1)) a b +
          ladderSiftedLogMass a b ladder ≤
        (2 ^ base.length : ℕ) *
          (eta * (b : ℝ) / ((a + 1 : ℕ) : ℝ)) + Rem :=
    add_le_add (mul_le_mul_of_nonneg_left hcost' (by positivity)) hRem
  have hleft0 : 0 ≤ (2 ^ base.length : ℕ) *
      sharpTwistedDirichletCost D (eta / (8 * Real.exp 1)) a b +
        ladderSiftedLogMass a b ladder := by
    exact add_nonneg
      (mul_nonneg (by positivity)
        (sharpTwistedDirichletCost_nonneg D
          (eta / (8 * Real.exp 1)) a b (by linarith) hdelta0
            (by omega) (by omega)))
      (by unfold ladderSiftedLogMass; positivity)
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hleft0 hmain 2) (by positivity))

end Tao2015

end MoltResearch
