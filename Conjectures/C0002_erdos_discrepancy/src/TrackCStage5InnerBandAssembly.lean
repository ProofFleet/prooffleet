import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5BandCapstoneFamily

/-!
# The `[mrt]` A.2 inner band from its level legs (Track R, A2-III, VI-5)

This file assembles the small-value level partition, the first and later level
estimates, and the exceptional cell-uniform estimate into the inner-band
capstone.
-/

namespace MoltResearch

namespace Tao2015

/-- The full typicality list: the `J` ordinary levels, followed by the
exceptional level. -/
def innerBandLevels (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ) (J : ℕ) :
    List (Finset ℕ) :=
  (List.range J).map Pl ++ [Pu]

/-- The ordinary levels strictly before level `j`. -/
def innerBandLevelsBefore (Pl : ℕ → Finset ℕ) (J j : ℕ) :
    List (Finset ℕ) :=
  ((List.range J).map Pl).take j

/-- The ordinary levels strictly after level `j`, followed by the exceptional
level. -/
def innerBandLevelsAfter (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ) (J j : ℕ) :
    List (Finset ℕ) :=
  ((List.range J).map Pl).drop (j + 1) ++ [Pu]

/-- A scheduled ordinary level occurs in its expected middle position in the
full list. -/
theorem innerBandLevels_eq_middle (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ)
    (J j : ℕ) (hjJ : j < J) :
    innerBandLevels Pl Pu J =
      innerBandLevelsBefore Pl J j ++
        Pl j :: innerBandLevelsAfter Pl Pu J j := by
  let levels := (List.range J).map Pl
  have hjlen : j < levels.length := by
    simpa [levels] using hjJ
  have hget : levels[j] = Pl j := by
    simp [levels]
  change levels ++ [Pu] = levels.take j ++ Pl j :: (levels.drop (j + 1) ++ [Pu])
  calc
    levels ++ [Pu] = (levels.take j ++ levels.drop j) ++ [Pu] := by
      rw [List.take_append_drop]
    _ = levels.take j ++ Pl j :: (levels.drop (j + 1) ++ [Pu]) := by
      rw [List.drop_eq_getElem_cons hjlen, hget]
      simp only [List.append_assoc, List.cons_append]

/-- Every level remaining after `Pl j` is either another scheduled ordinary
level or the exceptional level. -/
theorem mem_innerBandLevels_remaining (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ)
    (J j : ℕ) (hjJ : j < J) (Q : Finset ℕ)
    (hQ : Q ∈ innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j) :
    (∃ i < J, i ≠ j ∧ Pl i = Q) ∨ Q = Pu := by
  rw [List.mem_append] at hQ
  rcases hQ with hbefore | hafter
  · left
    unfold innerBandLevelsBefore at hbefore
    rw [← List.map_take, List.take_range,
      Nat.min_eq_left (Nat.le_of_lt hjJ)] at hbefore
    rw [List.mem_map] at hbefore
    obtain ⟨i, hi, hiQ⟩ := hbefore
    rw [List.mem_range] at hi
    exact ⟨i, hi.trans hjJ, Nat.ne_of_lt hi, hiQ⟩
  · unfold innerBandLevelsAfter at hafter
    rw [List.mem_append] at hafter
    rcases hafter with hlater | hPu
    · left
      rw [← List.map_drop] at hlater
      rw [show (List.range J).drop (j + 1) =
          List.range' (j + 1) (J - (j + 1)) by
            rw [List.range_eq_range']
            simp] at hlater
      rw [List.mem_map] at hlater
      obtain ⟨i, hi, hiQ⟩ := hlater
      rw [List.mem_range'] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      refine ⟨j + 1 + 1 * k, ?_, by omega, hiQ⟩
      omega
    · right
      simpa only [List.mem_singleton] using hPu

/-- Pairwise disjointness of the scheduled prime levels supplies the quotient
support stability needed after rotating any ordinary level to the head. -/
theorem innerBandLevel_stable_of_disjoint
    (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ) (J j : ℕ) (hjJ : j < J)
    (hPl : ∀ i < J, ∀ p ∈ Pl i, p.Prime)
    (hPu : ∀ p ∈ Pu, p.Prime)
    (hdisj : ∀ i < J, ∀ k < J, i ≠ k → Disjoint (Pl i) (Pl k))
    (hdisjU : ∀ i < J, Disjoint (Pl i) Pu) :
    ∀ p ∈ Pl j, ∀ m,
      HasFactorInAll
          (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j) (p * m) ↔
        HasFactorInAll
          (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j) m := by
  intro p hp m
  apply hasFactorInAll_mul_iff_of_disjoint (Pl j) (hPl j hjJ)
  · intro Q hQ q hq
    rcases mem_innerBandLevels_remaining Pl Pu J j hjJ Q hQ with
      ⟨i, hiJ, _, hiQ⟩ | hQU
    · subst Q
      exact hPl i hiJ q hq
    · subst Q
      exact hPu q hq
  · intro Q hQ
    rcases mem_innerBandLevels_remaining Pl Pu J j hjJ Q hQ with
      ⟨i, hiJ, hij, hiQ⟩ | hQU
    · subst Q
      exact hdisj j hjJ i hiJ hij.symm
    · subst Q
      exact hdisjU j hjJ
  · exact hp

/-- Every part of the inner-band partition lies in the interval used by the
level and exceptional energy estimates. -/
theorem innerBandPartOn_subset_Ioc (Pset : ℕ → Set ℝ) (J j : ℕ)
    (K₁ K₂ T : ℝ) (hTK₂ : K₂ + 2 ≤ T) :
    bandPartOn Pset J {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j ⊆
      Set.Ioc (-T) T := by
  intro xi hxi
  have hband := inner_band_subset_Icc K₁ K₂ (bandPartOn_subset Pset J _ j hxi)
  rw [Set.mem_Icc] at hband
  exact ⟨by linarith [hband.1], by linarith [hband.2]⟩

open MeasureTheory in
/-- The cell-replacement contribution of any ordinary level is discharged by
the VI-2k numerical fit. -/
theorem innerBand_replacement_leg
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta : ℕ) (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ)
    (Nl v₀l v₁l : ℕ → ℕ) (ql : ℕ → ℕ → ℕ) (alpha : ℕ → ℝ)
    (J j : ℕ) (hNj : 0 < Nl j)
    (hqcell : ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ql j v ∈ eadicCell (Pl j) (2 * Nl j) v)
    (hq1 : ∀ v, 1 ≤ ql j v)
    (hqmin : ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v, ql j v ≤ p)
    (hLA : ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
        A / (Nl j * p) + 1 ≤ A / p)
    (hLB : ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
        (A + Delta) / (Nl j * p) + 1 ≤ (A + Delta) / p)
    (K₁ K₂ T : ℝ) (hT : 0 < T) (hTK₂ : K₂ + 2 ≤ T)
    (Pb Kc bb : ℕ) (aa : ℕ → ℕ) (X c₃ eps kappa : ℝ)
    (hPb : 1 ≤ Pb) (hKc : 2 ≤ Kc) (hbb : 3 ≤ bb) (hX0 : 0 ≤ X)
    (hcostA : ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
        Real.exp Real.pi * (T / ((A / p : ℕ) : ℝ) + 4)
            * (((A / (Nl j * p) + 1 : ℕ) : ℝ) / ((A / p : ℕ) : ℝ)) ≤ X)
    (hcostB : ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
        Real.exp Real.pi * (T / (((A + Delta) / p : ℕ) : ℝ) + 4)
            * (((((A + Delta) / (Nl j * p)) + 1 : ℕ) : ℝ) /
              (((A + Delta) / p : ℕ) : ℝ)) ≤ X)
    (haa : ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1), Pb ≤ aa v)
    (hcell : ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      eadicCell (Pl j) (2 * Nl j) v ⊆
        (Finset.Ioc (aa v) (aa v + Kc)).filter Nat.Prime)
    (hlevel : ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      eadicCell (Pl j) (2 * Nl j) v ⊆
        (Finset.Ioc Pb bb).filter Nat.Prime)
    (hkappac : 0 ≤ kappa * c₃)
    (hrho : eps ≤ (Delta : ℝ) / (A : ℝ))
    (hfit : 64 * ((Finset.Ico (v₀l j) (v₁l j + 1)).card : ℝ) * X
        * ((256 * (Kc : ℝ) / ((Pb : ℝ) * Real.log Kc))
          * (Real.log (Real.log ((bb : ℝ) + 1)) + 11))
      ≤ kappa * c₃ * eps ^ 3) :
    2 * (∫ xi in bandPartOn (levelSmallSet Pl Nl v₀l v₁l g alpha) J
        {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
      ‖typicalSCellReplacement g A (A + Delta) (Pl j)
        (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j)
        (Nl j) (v₀l j) (v₁l j) (ql j) xi‖ ^ 2)
      ≤ kappa * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
  let G := bandPartOn (levelSmallSet Pl Nl v₀l v₁l g alpha) J
    {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j
  have hGm : MeasurableSet G :=
    bandPartOn_measurableSet _ (levelSmallSet_measurableSet Pl Nl v₀l v₁l g alpha)
      J _ (measurableSet_inner_band K₁ K₂) j
  have hGT : G ⊆ Set.Ioc (-T) T :=
    innerBandPartOn_subset_Ioc _ J j K₁ K₂ T hTK₂
  have hrepl := setIntegral_norm_sq_typicalSCellReplacement_le g hg A (A + Delta)
    (Nat.le_add_right A Delta) (Pl j)
    (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j)
    (Nl j) (v₀l j) (v₁l j) hNj (ql j) hqcell hq1 hqmin hLA hLB
    T hT G hGm hGT
  have hsched := eadic_replacement_error_le_budget (Pl j) (Nl j) (v₀l j) (v₁l j)
    A (A + Delta) Pb Kc bb T X c₃ eps ((Delta : ℝ) / (A : ℝ)) kappa aa
    hPb hKc hbb hX0 hcostA hcostB haa hcell hlevel hkappac hrho hfit
  calc
    2 * (∫ xi in G,
        ‖typicalSCellReplacement g A (A + Delta) (Pl j)
          (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j)
          (Nl j) (v₀l j) (v₁l j) (ql j) xi‖ ^ 2)
      ≤ 2 * cellReplacementEnergyBound (Pl j) (Nl j) (v₀l j) (v₁l j)
          A (A + Delta) T := by gcongr
    _ ≤ kappa * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := hsched

open MeasureTheory in
/-- The first ordinary level supplies the `j = 0` capstone leg over the full
typicality list. -/
theorem innerBand_first_level_leg
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta H : ℕ) (hDeltaA : Delta ≤ A)
    (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ) (J : ℕ) (hJ : 0 < J)
    (hPl : ∀ i < J, ∀ p ∈ Pl i, p.Prime)
    (hPu : ∀ p ∈ Pu, p.Prime)
    (hPA : ∀ i < J, ∀ p ∈ Pl i, p * p ≤ A)
    (hdisj : ∀ i < J, ∀ k < J, i ≠ k → Disjoint (Pl i) (Pl k))
    (hdisjU : ∀ i < J, Disjoint (Pl i) Pu)
    (Nl v₀l v₁l : ℕ → ℕ) (hN0 : 0 < Nl 0)
    (hcov0 : (Finset.Ico (v₀l 0) (v₁l 0 + 1)).biUnion
      (eadicCell (Pl 0) (2 * Nl 0)) = Pl 0)
    (ql : ℕ → ℕ → ℕ)
    (hqcell0 : ∀ v ∈ Finset.Ico (v₀l 0) (v₁l 0 + 1),
      ql 0 v ∈ eadicCell (Pl 0) (2 * Nl 0) v)
    (hq1_0 : ∀ v, 1 ≤ ql 0 v) (hqA0 : ∀ v, 2 * ql 0 v ≤ A)
    (alpha : ℕ → ℝ) (hAlpha0 : 0 < alpha 0) (hAlpha20 : 2 * alpha 0 < 1)
    (R : ℕ) (hR : 1 ≤ R) (hB : A + Delta ≤ R * A)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ v ∈ Finset.Ico (v₀l 0) (v₁l 0 + 1),
      ∑ m ∈ Finset.Ioc (A / ql 0 v) ((A + Delta) / ql 0 v),
        (1 : ℝ) / (m : ℝ) ≤ C)
    (Plo Qhi : ℕ → ℝ) (hPlo0 : 0 < Plo 0) (hQhi0 : 0 < Qhi 0)
    (htop0 : (v₁l 0 : ℝ) ≤ 2 * (Nl 0 : ℝ) * Real.log (Qhi 0))
    (hbot0 : 2 * (Nl 0 : ℝ) * Real.log (Plo 0) - 1 ≤ (v₀l 0 : ℝ))
    (K₁ K₂ T : ℝ) (hT : 0 < T) (hTK₂ : K₂ + 2 ≤ T)
    (kappaMain kappaReplacement kappaCollision c₃ eps : ℝ)
    (hc₃ : 0 ≤ c₃)
    (hfitT : ((Finset.Ico (v₀l 0) (v₁l 0 + 1)).card : ℝ)
        * (Real.exp Real.pi * C
          * ((2 * T * Real.exp (1 / ((2 * Nl 0 : ℕ) : ℝ)) / (A : ℝ))
            * ((Qhi 0) ^ (1 - 2 * alpha 0)
                * Real.exp ((1 - 2 * alpha 0) / ((2 * Nl 0 : ℕ) : ℝ)))
            * (((2 * Nl 0 : ℕ) : ℝ) / (1 - 2 * alpha 0) + 1)))
      ≤ kappaMain / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hfitP : ((Finset.Ico (v₀l 0) (v₁l 0 + 1)).card : ℝ)
        * (Real.exp Real.pi * C
          * (4 * (R : ℝ)
            * ((Plo 0) ^ (-(2 * alpha 0))
                * Real.exp (2 * alpha 0 / ((2 * Nl 0 : ℕ) : ℝ)))
            * (((2 * Nl 0 : ℕ) : ℝ) / (2 * alpha 0) + 1)))
      ≤ kappaMain / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hreplacement : 2 * (∫ xi in bandPartOn
        (levelSmallSet Pl Nl v₀l v₁l g alpha) J
          {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} 0,
        ‖typicalSCellReplacement g A (A + Delta) (Pl 0)
          (innerBandLevelsBefore Pl J 0 ++ innerBandLevelsAfter Pl Pu J 0)
          (Nl 0) (v₀l 0) (v₁l 0) (ql 0) xi‖ ^ 2)
      ≤ kappaReplacement * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hcollisionFit : 8 * collisionEnergyBound A (A + Delta) (Pl 0)
        (innerBandLevelsBefore Pl J 0 ++ innerBandLevelsAfter Pl Pu J 0) T
      ≤ kappaCollision * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hshare : (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (2 * kappaMain + 2 * kappaReplacement + 2 * kappaCollision)
      ≤ (1 : ℝ) / 2 ^ (0 + 1)) :
    (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (∫ xi in bandPartOn (levelSmallSet Pl Nl v₀l v₁l g alpha) J
            {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} 0,
          ‖∑ m ∈ typicalS A (A + Delta) (innerBandLevels Pl Pu J),
              (g m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
      ≤ (1 / 2 ^ (0 + 1))
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
  let G := bandPartOn (levelSmallSet Pl Nl v₀l v₁l g alpha) J
    {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} 0
  let rest := innerBandLevelsBefore Pl J 0 ++ innerBandLevelsAfter Pl Pu J 0
  have hGm : MeasurableSet G :=
    bandPartOn_measurableSet _ (levelSmallSet_measurableSet Pl Nl v₀l v₁l g alpha)
      J _ (measurableSet_inner_band K₁ K₂) 0
  have hGT : G ⊆ Set.Ioc (-T) T :=
    innerBandPartOn_subset_Ioc _ J 0 K₁ K₂ T hTK₂
  have hsmall : ∀ v ∈ Finset.Ico (v₀l 0) (v₁l 0 + 1), ∀ xi ∈ G,
      ‖levelCellPoly (Pl 0) (Nl 0) v g xi‖
        ≤ Real.exp (-(alpha 0 * (v : ℝ) / ((2 * Nl 0 : ℕ) : ℝ))) := by
    intro v hv xi hxi
    exact levelSmallSet_small_of_mem_bandPartOn Pl Nl v₀l v₁l g alpha J 0 _ xi
      hJ hxi v hv
  have hmain := band_energy_level_one_main_le_budget (Pl 0) (Nl 0) hN0
    (v₀l 0) (v₁l 0) (ql 0) A (A + Delta) R hR hB hq1_0 hqA0 hqcell0
    g hg (typicalS 0 (A + Delta) rest) T hT G hGm hGT
    (alpha 0) hAlpha0 hAlpha20 C hC0 hC hsmall
    (Plo 0) (Qhi 0) c₃ eps ((Delta : ℝ) / (A : ℝ)) kappaMain
    hPlo0 hQhi0 htop0 hbot0 hfitT hfitP
  have hstable := innerBandLevel_stable_of_disjoint Pl Pu J 0 hJ hPl hPu hdisj hdisjU
  rw [innerBandLevels_eq_middle Pl Pu J 0 hJ]
  exact typicalS_level_leg_le_budget_of_collision_fit_middle g hcm hg A Delta H
    hDeltaA (innerBandLevelsBefore Pl J 0) (innerBandLevelsAfter Pl Pu J 0) (Pl 0)
    (hPl 0 hJ) (hPA 0 hJ) (Nl 0) (v₀l 0) (v₁l 0) hcov0 hstable (ql 0)
    K₁ K₂ T hT J 0 (levelSmallSet Pl Nl v₀l v₁l g alpha)
    (levelSmallSet_measurableSet Pl Nl v₀l v₁l g alpha) hGT
    kappaMain kappaReplacement kappaCollision c₃ eps hc₃ hmain hreplacement
    hcollisionFit hshare

open MeasureTheory in
/-- On a fixed later level, the least-large-cell refinement assembles the
per-previous-cell moment estimates without a cardinality loss. -/
theorem innerBand_later_level_main
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta : ℕ) (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ)
    (Nl v₀l v₁l : ℕ → ℕ) (ql : ℕ → ℕ → ℕ) (alpha : ℕ → ℝ)
    (J j : ℕ) (hj0 : 0 < j) (hjJ : j < J)
    (hNcur : 0 < Nl j) (hNprev : 0 < Nl (j - 1))
    (hPprev : ∀ p ∈ Pl (j - 1), p.Prime)
    (A' Delta' Pmom ell : ℕ → ℕ)
    (hA' : ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1), 1 ≤ A' r)
    (hDelta' : ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      Delta' r ≤ A' r)
    (hSblk : ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
        Finset.Ioc (A / ql j v) ((A + Delta) / ql j v) ⊆
          Finset.Ioc (A' r) (A' r + Delta' r))
    (hPmom : ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      1 ≤ Pmom r)
    (hlo : ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      ∀ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r, Pmom r < p)
    (hhi : ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      ∀ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r, p ≤ 2 * Pmom r)
    (hell : ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1), 1 ≤ ell r)
    (Plo Qhi : ℕ → ℝ)
    (hAlpha : 0 < alpha j) (hBeta : 0 ≤ alpha (j - 1))
    (hPlo0 : 0 < Plo j) (hPloQhi : Plo j ≤ Qhi j)
    (hQprev0 : 0 < Qhi (j - 1))
    (htopPrev : (v₁l (j - 1) : ℝ) ≤
      2 * (Nl (j - 1) : ℝ) * Real.log (Qhi (j - 1)))
    (htop : (v₁l j : ℝ) ≤ 2 * (Nl j : ℝ) * Real.log (Qhi j))
    (hbot : 2 * (Nl j : ℝ) * Real.log (Plo j) - 1 ≤ (v₀l j : ℝ))
    (K₁ K₂ T : ℝ) (hT : 0 < T) (hTK₂ : K₂ + 2 ≤ T)
    (kappaCell : ℕ → ℝ) (kappaMain c₃ eps : ℝ) (hc₃ : 0 ≤ c₃)
    (hfit : ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      (2 * (Nl j : ℝ) * (Real.log (Qhi j) - Real.log (Plo j)) + 2)
        * (((Plo j) ^ (-(2 * alpha j))
              * Real.exp (2 * alpha j / ((2 * Nl j : ℕ) : ℝ))
              * (((2 * Nl j : ℕ) : ℝ) / (2 * alpha j) + 1))
            * ((Real.exp Real.pi
                  * (T / (((Pmom r) ^ (ell r) * A' r : ℕ) : ℝ)
                    + 2 * ((2 ^ (ell r + 1) : ℕ) : ℝ)))
              * (((Nat.factorial (ell r) : ℝ) ^ 2
                * (((2 ^ (ell r + 1) : ℕ) : ℝ) * ((ell r : ℝ) + 1)
                  * (∑ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r,
                      (1 : ℝ) / (p : ℝ)) ^ (ell r)))
                / ((Qhi (j - 1)) ^ (-(alpha (j - 1)))
                    * Real.exp (-(alpha (j - 1) /
                      ((2 * Nl (j - 1) : ℕ) : ℝ)))) ^ (2 * ell r))))
      ≤ kappaCell r * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hshares : ∑ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      kappaCell r ≤ kappaMain) :
    (∫ xi in bandPartOn (levelSmallSet Pl Nl v₀l v₁l g alpha) J
        {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
      ‖typicalSCellUniformMain g A (A + Delta) (Pl j)
        (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j)
        (Nl j) (v₀l j) (v₁l j) (ql j) xi‖ ^ 2)
      ≤ kappaMain * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
  let band := {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂}
  let Pset := levelSmallSet Pl Nl v₀l v₁l g alpha
  let rest := innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j
  let F := typicalSCellUniformMain g A (A + Delta) (Pl j) rest
    (Nl j) (v₀l j) (v₁l j) (ql j)
  have hbandm : MeasurableSet band := measurableSet_inner_band K₁ K₂
  have hpartT : bandPartOn Pset J band j ⊆ Set.Ioc (-T) T :=
    innerBandPartOn_subset_Ioc Pset J j K₁ K₂ T hTK₂
  have hcell : ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      (∫ xi in firstPrevLargePart Pl Nl v₀l v₁l g alpha J band j r,
          ‖F xi‖ ^ 2)
        ≤ kappaCell r * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    intro r hr
    let Gr := firstPrevLargePart Pl Nl v₀l v₁l g alpha J band j r
    have hGrm : MeasurableSet Gr :=
      firstPrevLargePart_measurableSet Pl Nl v₀l v₁l g alpha J band hbandm j r
    have hGrT : Gr ⊆ Set.Ioc (-T) T :=
      (firstPrevLargePart_subset_bandPartOn Pl Nl v₀l v₁l g alpha J band j r).trans
        hpartT
    have hsmall : ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1), ∀ xi ∈ Gr,
        ‖levelCellPoly (Pl j) (Nl j) v g xi‖
          ≤ Real.exp (-(alpha j * (v : ℝ) / ((2 * Nl j : ℕ) : ℝ))) := by
      intro v hv xi hxi
      exact levelSmallSet_small_of_mem_bandPartOn Pl Nl v₀l v₁l g alpha J j band xi
        hjJ (firstPrevLargePart_subset_bandPartOn
          Pl Nl v₀l v₁l g alpha J band j r hxi) v hv
    have hlarge : ∀ xi ∈ Gr,
        Real.exp (-(alpha (j - 1) * (r : ℝ) /
            ((2 * Nl (j - 1) : ℕ) : ℝ)))
          ≤ ‖levelCellPoly (Pl (j - 1)) (Nl (j - 1)) r g xi‖ := by
      intro xi hxi
      exact (firstPrevLargePart_large Pl Nl v₀l v₁l g alpha J band j r hr hxi).le
    have hrTop : r ≤ v₁l (j - 1) := by
      have := (Finset.mem_Ico.mp hr).2
      omega
    have hraw := band_energy_later_main_le_budget
      (Pl j) (Pl (j - 1)) (Nl j) (Nl (j - 1)) r (v₁l (j - 1))
      hNcur hNprev (v₀l j) (v₁l j)
      (fun v => Finset.Ioc (A / ql j v) ((A + Delta) / ql j v))
      (A' r) (Delta' r) (hA' r hr) (hDelta' r hr) (hSblk r hr)
      g hg (typicalS 0 (A + Delta) rest) (Pmom r) (hPmom r hr)
      hPprev (hlo r hr) (hhi r hr) (ell r) (hell r hr) T hT Gr hGrm hGrT
      (alpha j) (alpha (j - 1)) (Plo j) (Qhi j) (Qhi (j - 1))
      hAlpha hBeta hPlo0 hPloQhi hQprev0 hrTop htopPrev hsmall hlarge htop hbot
      c₃ eps ((Delta : ℝ) / (A : ℝ)) (kappaCell r) (hfit r hr)
    simpa [F, typicalSCellUniformMain, rest] using hraw
  exact setIntegral_norm_sq_later_le_budget_of_firstPrev Pl Nl v₀l v₁l g alpha
    J band hbandm j hj0 hjJ F
    (continuous_typicalSCellUniformMain g A (A + Delta) (Pl j) rest
      (Nl j) (v₀l j) (v₁l j) (ql j))
    T hpartT kappaCell kappaMain c₃ eps ((Delta : ℝ) / (A : ℝ)) hc₃
    (by positivity) hcell hshares

open MeasureTheory in
/-- A main-term estimate for a scheduled ordinary level, together with the
replacement and collision fits, gives its full-list capstone leg. -/
theorem innerBand_level_leg_of_main
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta H : ℕ) (hDeltaA : Delta ≤ A)
    (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ) (J j : ℕ) (hjJ : j < J)
    (hPl : ∀ i < J, ∀ p ∈ Pl i, p.Prime)
    (hPu : ∀ p ∈ Pu, p.Prime)
    (hPA : ∀ i < J, ∀ p ∈ Pl i, p * p ≤ A)
    (hdisj : ∀ i < J, ∀ k < J, i ≠ k → Disjoint (Pl i) (Pl k))
    (hdisjU : ∀ i < J, Disjoint (Pl i) Pu)
    (Nl v₀l v₁l : ℕ → ℕ)
    (hcov : (Finset.Ico (v₀l j) (v₁l j + 1)).biUnion
      (eadicCell (Pl j) (2 * Nl j)) = Pl j)
    (ql : ℕ → ℕ → ℕ) (alpha : ℕ → ℝ)
    (K₁ K₂ T : ℝ) (hT : 0 < T) (hTK₂ : K₂ + 2 ≤ T)
    (kappaMain kappaReplacement kappaCollision c₃ eps : ℝ)
    (hc₃ : 0 ≤ c₃)
    (hmain : (∫ xi in bandPartOn (levelSmallSet Pl Nl v₀l v₁l g alpha) J
        {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
      ‖typicalSCellUniformMain g A (A + Delta) (Pl j)
        (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j)
        (Nl j) (v₀l j) (v₁l j) (ql j) xi‖ ^ 2)
      ≤ kappaMain * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hreplacement : 2 * (∫ xi in bandPartOn
        (levelSmallSet Pl Nl v₀l v₁l g alpha) J
          {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
        ‖typicalSCellReplacement g A (A + Delta) (Pl j)
          (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j)
          (Nl j) (v₀l j) (v₁l j) (ql j) xi‖ ^ 2)
      ≤ kappaReplacement * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hcollisionFit : 8 * collisionEnergyBound A (A + Delta) (Pl j)
        (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j) T
      ≤ kappaCollision * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hshare : (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (2 * kappaMain + 2 * kappaReplacement + 2 * kappaCollision)
      ≤ (1 : ℝ) / 2 ^ (j + 1)) :
    (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (∫ xi in bandPartOn (levelSmallSet Pl Nl v₀l v₁l g alpha) J
            {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
          ‖∑ m ∈ typicalS A (A + Delta) (innerBandLevels Pl Pu J),
              (g m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
      ≤ (1 / 2 ^ (j + 1))
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
  have hpartT := innerBandPartOn_subset_Ioc
    (levelSmallSet Pl Nl v₀l v₁l g alpha) J j K₁ K₂ T hTK₂
  have hstable := innerBandLevel_stable_of_disjoint Pl Pu J j hjJ hPl hPu hdisj hdisjU
  rw [innerBandLevels_eq_middle Pl Pu J j hjJ]
  exact typicalS_level_leg_le_budget_of_collision_fit_middle g hcm hg A Delta H
    hDeltaA (innerBandLevelsBefore Pl J j) (innerBandLevelsAfter Pl Pu J j) (Pl j)
    (hPl j hjJ) (hPA j hjJ) (Nl j) (v₀l j) (v₁l j) hcov hstable (ql j)
    K₁ K₂ T hT J j (levelSmallSet Pl Nl v₀l v₁l g alpha)
    (levelSmallSet_measurableSet Pl Nl v₀l v₁l g alpha) hpartT
    kappaMain kappaReplacement kappaCollision c₃ eps hc₃ hmain hreplacement
    hcollisionFit hshare

end Tao2015

end MoltResearch
