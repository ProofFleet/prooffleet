import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5BandCapstoneFamily
import MoltResearch.Discrepancy.CellHalasz

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

/-- Disjointness from every ordinary level supplies the exceptional level's
quotient-support stability after it is rotated to the head. -/
theorem innerBandExceptional_stable_of_disjoint
    (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ) (J : ℕ)
    (hPl : ∀ i < J, ∀ p ∈ Pl i, p.Prime)
    (hPu : ∀ p ∈ Pu, p.Prime)
    (hdisjU : ∀ i < J, Disjoint (Pl i) Pu) :
    ∀ p ∈ Pu, ∀ m,
      HasFactorInAll ((List.range J).map Pl) (p * m) ↔
        HasFactorInAll ((List.range J).map Pl) m := by
  intro p hp m
  apply hasFactorInAll_mul_iff_of_disjoint Pu hPu
  · intro Q hQ q hq
    rw [List.mem_map] at hQ
    obtain ⟨i, hi, rfl⟩ := hQ
    rw [List.mem_range] at hi
    exact hPl i hi q hq
  · intro Q hQ
    rw [List.mem_map] at hQ
    obtain ⟨i, hi, rfl⟩ := hQ
    rw [List.mem_range] at hi
    exact (hdisjU i hi).symm
  · exact hp

open MeasureTheory in
/-- **A2-III VI-5 — the inner-band estimate assembled from all scheduled
levels.**

The first-index partition is the smallness partition of the ordinary levels.
Level zero is priced by the level-one estimate; every later level is refined by
its first large previous cell and priced by the moment estimate.  The final
prime set `Pu` is rotated to the head and supplied to the exceptional
cell-uniform capstone. -/
theorem band_energy_typicalS_le_of_levels [HalaszLargeValuesAssumption]
    (Cp : ℝ) (hCp1 : 1 ≤ Cp) (hprime : PrimeLargeValuesBound Cp)
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta H : ℕ) (hA : 0 < A) (hH : 0 < H) (hDeltaA : Delta ≤ A)
    (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ) (J : ℕ)
    (hPl : ∀ i < J, ∀ p ∈ Pl i, p.Prime)
    (hPu : ∀ p ∈ Pu, p.Prime)
    (hPAl : ∀ i < J, ∀ p ∈ Pl i, p * p ≤ A)
    (hPAu : ∀ p ∈ Pu, p * p ≤ A)
    (hdisj : ∀ i < J, ∀ k < J, i ≠ k → Disjoint (Pl i) (Pl k))
    (hdisjU : ∀ i < J, Disjoint (Pl i) Pu)
    (Nl v₀l v₁l : ℕ → ℕ) (ql : ℕ → ℕ → ℕ) (alpha : ℕ → ℝ)
    (hNl : ∀ j < J, 0 < Nl j)
    (hcovl : ∀ j < J, (Finset.Ico (v₀l j) (v₁l j + 1)).biUnion
      (eadicCell (Pl j) (2 * Nl j)) = Pl j)
    (hqcelll : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ql j v ∈ eadicCell (Pl j) (2 * Nl j) v)
    (hq1l : ∀ j < J, ∀ v, 1 ≤ ql j v)
    (hqAl : ∀ j < J, ∀ v, 2 * ql j v ≤ A)
    (hqminl : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v, ql j v ≤ p)
    (hLAl : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
        A / (Nl j * p) + 1 ≤ A / p)
    (hLBl : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
        (A + Delta) / (Nl j * p) + 1 ≤ (A + Delta) / p)
    (Plo Qhi : ℕ → ℝ)
    (hAlpha : ∀ j < J, 0 < alpha j)
    (hAlpha2_0 : 0 < J → 2 * alpha 0 < 1)
    (hPlo0 : ∀ j < J, 0 < Plo j) (hQhi0 : ∀ j < J, 0 < Qhi j)
    (hPloQhi : ∀ j < J, Plo j ≤ Qhi j)
    (htop : ∀ j < J,
      (v₁l j : ℝ) ≤ 2 * (Nl j : ℝ) * Real.log (Qhi j))
    (hbot : ∀ j < J,
      2 * (Nl j : ℝ) * Real.log (Plo j) - 1 ≤ (v₀l j : ℝ))
    (R : ℕ) (hR : 1 ≤ R) (hB : A + Delta ≤ R * A)
    (Clevel : ℕ → ℝ) (hClevel0 : 0 ≤ Clevel 0)
    (hClevel : 0 < J → ∀ v ∈ Finset.Ico (v₀l 0) (v₁l 0 + 1),
      ∑ m ∈ Finset.Ioc (A / ql 0 v) ((A + Delta) / ql 0 v),
        (1 : ℝ) / (m : ℝ) ≤ Clevel 0)
    (K₁ K₂ T : ℝ) (hT1 : 1 ≤ T) (hTK₂ : K₂ + 2 ≤ T)
    (c₃ eps : ℝ) (hc₃ : 0 ≤ c₃)
    (kappaMain kappaReplacement kappaCollision : ℕ → ℝ)
    (hfitT0 : 0 < J →
      ((Finset.Ico (v₀l 0) (v₁l 0 + 1)).card : ℝ)
        * (Real.exp Real.pi * Clevel 0
          * ((2 * T * Real.exp (1 / ((2 * Nl 0 : ℕ) : ℝ)) / (A : ℝ))
            * ((Qhi 0) ^ (1 - 2 * alpha 0)
                * Real.exp ((1 - 2 * alpha 0) / ((2 * Nl 0 : ℕ) : ℝ)))
            * (((2 * Nl 0 : ℕ) : ℝ) / (1 - 2 * alpha 0) + 1)))
      ≤ kappaMain 0 / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hfitP0 : 0 < J →
      ((Finset.Ico (v₀l 0) (v₁l 0 + 1)).card : ℝ)
        * (Real.exp Real.pi * Clevel 0
          * (4 * (R : ℝ)
            * ((Plo 0) ^ (-(2 * alpha 0))
                * Real.exp (2 * alpha 0 / ((2 * Nl 0 : ℕ) : ℝ)))
            * (((2 * Nl 0 : ℕ) : ℝ) / (2 * alpha 0) + 1)))
      ≤ kappaMain 0 / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (A' Delta' Pmom ell : ℕ → ℕ → ℕ)
    (hA' : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1), 1 ≤ A' j r)
    (hDelta' : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
        Delta' j r ≤ A' j r)
    (hSblk : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
        Finset.Ioc (A / ql j v) ((A + Delta) / ql j v) ⊆
          Finset.Ioc (A' j r) (A' j r + Delta' j r))
    (hPmom : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1), 1 ≤ Pmom j r)
    (hlomom : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      ∀ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r, Pmom j r < p)
    (hhimom : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      ∀ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r, p ≤ 2 * Pmom j r)
    (hell : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1), 1 ≤ ell j r)
    (kappaCell : ℕ → ℕ → ℝ)
    (hfitLater : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      (2 * (Nl j : ℝ) * (Real.log (Qhi j) - Real.log (Plo j)) + 2)
        * (((Plo j) ^ (-(2 * alpha j))
              * Real.exp (2 * alpha j / ((2 * Nl j : ℕ) : ℝ))
              * (((2 * Nl j : ℕ) : ℝ) / (2 * alpha j) + 1))
            * ((Real.exp Real.pi
                  * (T / (((Pmom j r) ^ (ell j r) * A' j r : ℕ) : ℝ)
                    + 2 * ((2 ^ (ell j r + 1) : ℕ) : ℝ)))
              * (((Nat.factorial (ell j r) : ℝ) ^ 2
                * (((2 ^ (ell j r + 1) : ℕ) : ℝ) * ((ell j r : ℝ) + 1)
                  * (∑ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r,
                      (1 : ℝ) / (p : ℝ)) ^ (ell j r)))
                / ((Qhi (j - 1)) ^ (-(alpha (j - 1)))
                    * Real.exp (-(alpha (j - 1) /
                      ((2 * Nl (j - 1) : ℕ) : ℝ)))) ^ (2 * ell j r))))
      ≤ kappaCell j r * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hsharesLater : ∀ j, 0 < j → j < J →
      ∑ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
        kappaCell j r ≤ kappaMain j)
    (Pb Kc bb : ℕ → ℕ) (aa : ℕ → ℕ → ℕ) (X : ℕ → ℝ)
    (hPb : ∀ j < J, 1 ≤ Pb j) (hKc : ∀ j < J, 2 ≤ Kc j)
    (hbb : ∀ j < J, 3 ≤ bb j) (hX0 : ∀ j < J, 0 ≤ X j)
    (hcostA : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
        Real.exp Real.pi * (T / ((A / p : ℕ) : ℝ) + 4)
            * (((A / (Nl j * p) + 1 : ℕ) : ℝ) / ((A / p : ℕ) : ℝ)) ≤ X j)
    (hcostB : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
        Real.exp Real.pi * (T / (((A + Delta) / p : ℕ) : ℝ) + 4)
            * (((((A + Delta) / (Nl j * p)) + 1 : ℕ) : ℝ) /
              (((A + Delta) / p : ℕ) : ℝ)) ≤ X j)
    (haa : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1), Pb j ≤ aa j v)
    (hcell : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      eadicCell (Pl j) (2 * Nl j) v ⊆
        (Finset.Ioc (aa j v) (aa j v + Kc j)).filter Nat.Prime)
    (hlevel : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      eadicCell (Pl j) (2 * Nl j) v ⊆
        (Finset.Ioc (Pb j) (bb j)).filter Nat.Prime)
    (hkappac : ∀ j < J, 0 ≤ kappaReplacement j * c₃)
    (hrho : eps ≤ (Delta : ℝ) / (A : ℝ))
    (hfitReplacement : ∀ j < J,
      64 * ((Finset.Ico (v₀l j) (v₁l j + 1)).card : ℝ) * X j
          * ((256 * (Kc j : ℝ) / ((Pb j : ℝ) * Real.log (Kc j)))
            * (Real.log (Real.log ((bb j : ℝ) + 1)) + 11))
        ≤ kappaReplacement j * c₃ * eps ^ 3)
    (hcollisionFit : ∀ j < J,
      8 * collisionEnergyBound A (A + Delta) (Pl j)
          (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j) T
        ≤ kappaCollision j * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hshare : ∀ j < J, (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (2 * kappaMain j + 2 * kappaReplacement j + 2 * kappaCollision j)
      ≤ (1 : ℝ) / 2 ^ (j + 1))
    (Nu v₀u v₁u : ℕ) (hNu : 0 < Nu)
    (hcovU : (Finset.Ico v₀u (v₁u + 1)).biUnion
      (eadicCell Pu (2 * Nu)) = Pu)
    (qu : ℕ → ℕ)
    (hqcellU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1), qu v ∈ eadicCell Pu (2 * Nu) v)
    (hq1U : ∀ v, 1 ≤ qu v)
    (hqminU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v, qu v ≤ p)
    (hLAU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v, A / (Nu * p) + 1 ≤ A / p)
    (hLBU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v,
        (A + Delta) / (Nu * p) + 1 ≤ (A + Delta) / p)
    (w : ℝ → ℝ) (hwm : Measurable w) (hw0 : ∀ xi, 0 ≤ w xi)
    (hwsup : ∀ xi, w xi ≤ (4 * (H : ℝ) / (A : ℝ)) ^ 2)
    (PcU : ℕ → ℕ) (hPcU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1), 2 ≤ PcU v)
    (hloU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v, PcU v < p)
    (hhiU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v, p ≤ 2 * PcU v)
    (deltaU : ℕ → ℝ) (hdeltaU0 : ∀ v ∈ Finset.Ico v₀u (v₁u + 1), 0 < deltaU v)
    (hdeltaU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1), ∀ t : ℝ, |t| ≤ T →
      ‖∑ n ∈ Finset.Icc 1 ((A + Delta) / qu v),
          (cellBlockCoeff g A (A + Delta) Pu ((List.range J).map Pl) (qu v) n /
              (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ deltaU v)
    (hA0 : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      0 < 64 * ((((A + Delta) / qu v : ℕ) : ℝ)
          + ((bandCells K₂).card : ℝ) * Real.sqrt T)
        * (Real.log (2 * T) + 1)
        * ∑ n ∈ Finset.Icc 1 ((A + Delta) / qu v),
            ‖cellBlockCoeff g A (A + Delta) Pu ((List.range J).map Pl) (qu v) n‖ ^ 2 /
              (n : ℝ) ^ 2)
    (hB0 : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      0 < Cp * (∑ p ∈ eadicCell Pu (2 * Nu) v, ‖g p‖ ^ 2 / (p : ℝ) ^ 2)
        * (PcU v : ℝ) / Real.log (PcU v))
    (kappaU : ℕ → ℝ)
    (hfitUCell : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      2 * ((deltaU v) ^ 2 * (Cp * (256 / (Real.log (PcU v)) ^ 2))
        + 2 * deltaU v * Real.sqrt
            ((128 * ((((A + Delta) / qu v : ℕ) : ℝ) + 2 * T * Real.sqrt T)
                * (Real.log (2 * T) + 1))
              * ((Cp * (256 / (Real.log (PcU v)) ^ 2))
                  * (Real.exp Real.pi * ((T + 1) / (PcU v : ℝ) + 4)
                    * (256 / Real.log (PcU v) + 2048 * Real.pi)
                    * Real.exp (-(Real.log (PcU v) /
                      (Real.log (2 * T)) ^ primeLargeValuesExponent))
                    * (Real.log (2 * T)) ^ 2))))
        ≤ kappaU v * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hfitU : 2 * ((Finset.Ico v₀u (v₁u + 1)).card : ℝ)
          * (∑ v ∈ Finset.Ico v₀u (v₁u + 1), kappaU v)
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))
        + 2 * (2 * cellReplacementEnergyBound Pu Nu v₀u v₁u A (A + Delta) T
            + 2 * (4 * collisionEnergyBound A (A + Delta) Pu
              ((List.range J).map Pl) T))
      ≤ (1 / 2 ^ (J + 1)) * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) /
          (4 * (H : ℝ) / (A : ℝ)) ^ 2) :
    (∫ xi in {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂},
        ‖∑ m ∈ typicalS A (A + Delta) (innerBandLevels Pl Pu J),
            (g m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2 * w xi)
      ≤ bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  let Pset := levelSmallSet Pl Nl v₀l v₁l g alpha
  have hPset : ∀ j, MeasurableSet (Pset j) :=
    levelSmallSet_measurableSet Pl Nl v₀l v₁l g alpha
  have hlevelLeg : ∀ j ∈ Finset.range (J + 1), j ≠ J →
      (4 * (H : ℝ) / (A : ℝ)) ^ 2
          * ∫ xi in bandPartOn Pset J {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
            ‖∑ m ∈ typicalS A (A + Delta) (innerBandLevels Pl Pu J),
                (g m / (m : ℂ))
                  * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2
        ≤ (1 / 2 ^ (j + 1)) * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    intro j hj hne
    have hjJ : j < J := by
      rw [Finset.mem_range] at hj
      omega
    have hrepl := innerBand_replacement_leg g hg A Delta Pl Pu Nl v₀l v₁l ql alpha
      J j (hNl j hjJ) (hqcelll j hjJ) (hq1l j hjJ) (hqminl j hjJ)
      (hLAl j hjJ) (hLBl j hjJ) K₁ K₂ T hT hTK₂
      (Pb j) (Kc j) (bb j) (aa j) (X j) c₃ eps (kappaReplacement j)
      (hPb j hjJ) (hKc j hjJ) (hbb j hjJ) (hX0 j hjJ)
      (hcostA j hjJ) (hcostB j hjJ) (haa j hjJ) (hcell j hjJ)
      (hlevel j hjJ) (hkappac j hjJ) hrho (hfitReplacement j hjJ)
    by_cases hj0 : j = 0
    · subst j
      exact innerBand_first_level_leg g hcm hg A Delta H hDeltaA Pl Pu J hjJ
        hPl hPu hPAl hdisj hdisjU Nl v₀l v₁l (hNl 0 hjJ) (hcovl 0 hjJ)
        ql (hqcelll 0 hjJ) (hq1l 0 hjJ) (hqAl 0 hjJ) alpha (hAlpha 0 hjJ)
        (hAlpha2_0 hjJ) R hR hB (Clevel 0) hClevel0 (hClevel hjJ)
        Plo Qhi (hPlo0 0 hjJ) (hQhi0 0 hjJ) (htop 0 hjJ) (hbot 0 hjJ)
        K₁ K₂ T hT hTK₂ (kappaMain 0) (kappaReplacement 0) (kappaCollision 0)
        c₃ eps hc₃ (hfitT0 hjJ) (hfitP0 hjJ) hrepl (hcollisionFit 0 hjJ)
        (hshare 0 hjJ)
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      have hjprevJ : j - 1 < J := by omega
      have hmain := innerBand_later_level_main g hg A Delta Pl Pu Nl v₀l v₁l ql
        alpha J j hjpos hjJ (hNl j hjJ) (hNl (j - 1) hjprevJ)
        (hPl (j - 1) hjprevJ) (A' j) (Delta' j) (Pmom j) (ell j)
        (hA' j hjpos hjJ) (hDelta' j hjpos hjJ) (hSblk j hjpos hjJ)
        (hPmom j hjpos hjJ) (hlomom j hjpos hjJ) (hhimom j hjpos hjJ)
        (hell j hjpos hjJ) Plo Qhi (hAlpha j hjJ) (hAlpha (j - 1) hjprevJ).le
        (hPlo0 j hjJ) (hPloQhi j hjJ) (hQhi0 (j - 1) hjprevJ)
        (htop (j - 1) hjprevJ) (htop j hjJ) (hbot j hjJ) K₁ K₂ T hT hTK₂
        (kappaCell j) (kappaMain j) c₃ eps hc₃ (hfitLater j hjpos hjJ)
        (hsharesLater j hjpos hjJ)
      exact innerBand_level_leg_of_main g hcm hg A Delta H hDeltaA Pl Pu J j hjJ
        hPl hPu hPAl hdisj hdisjU Nl v₀l v₁l (hcovl j hjJ) ql alpha
        K₁ K₂ T hT hTK₂ (kappaMain j) (kappaReplacement j) (kappaCollision j)
        c₃ eps hc₃ hmain hrepl (hcollisionFit j hjJ) (hshare j hjJ)
  let restU := (List.range J).map Pl
  have hstableU := innerBandExceptional_stable_of_disjoint Pl Pu J hPl hPu hdisjU
  have htyp : typicalS A (A + Delta) (innerBandLevels Pl Pu J) =
      typicalS A (A + Delta) (Pu :: restU) := by
    simpa [innerBandLevels, restU] using
      typicalS_middle A (A + Delta) ((List.range J).map Pl) [] Pu
  have hlegU : ∀ j ∈ Finset.range (J + 1), j ≠ J →
      (4 * (H : ℝ) / (A : ℝ)) ^ 2
          * ∫ xi in bandPartOn Pset J {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
            ‖∑ m ∈ typicalS A (A + Delta) (Pu :: restU),
                (g m / (m : ℂ))
                  * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2
        ≤ (1 / 2 ^ (j + 1)) * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    intro j hj hne
    rw [← htyp]
    exact hlevelLeg j hj hne
  rw [htyp]
  exact band_energy_typicalS_le_of_cellUniform_fit Cp hCp1 hprime
    g hcm hg A Delta H hA hH hDeltaA
    Pu hPu hPAu restU Nu v₀u v₁u hNu hcovU hstableU qu hqcellU hq1U hqminU
    hLAU hLBU w hwm hw0 hwsup K₁ K₂ J Pset hPset c₃ eps hc₃ hlegU
    PcU hPcU hloU hhiU T hT1 hTK₂ deltaU hdeltaU0 hdeltaU hA0 hB0
    kappaU hfitUCell hfitU


/-! ## The per-cell Halász input, plugged in (Track R, A2-III, VI-7-1) -/

/-- **A2-III VI-7-1 — the exceptional level's `hδ`, discharged by VI-6.**

The assembly's per-cell Halász hypothesis is a bound on the block polynomial
over `Icc 1 ((A+Δ)/q)` with the zero-extended `cellBlockCoeff`; by
`sum_cellBlockCoeff_Icc_eq` that polynomial is the cell-representative block of
`LevelLegs`, and `norm_typicalS_quot_block_poly_le` (VI-6f) bounds it uniformly on
`|t| ≤ T` by the closed form `cellHalaszBound`.  `A + Δ ≤ 2A` is `Δ ≤ A`. -/
theorem norm_cellBlock_poly_le_cellHalaszBound (g : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC g) (hg : ∀ n, ‖g n‖ ≤ 1) (h1 : g 1 = 1)
    (A Δ q : ℕ) (hq : 1 ≤ q) (hΔA : Δ ≤ A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (hrest : ∀ Q ∈ rest, ∀ p ∈ Q, p.Prime)
    (D : ℝ) (hD : 1 ≤ D) (δ₀ : ℝ) (hδ0 : 0 < δ₀) (hδ1 : δ₀ ≤ 1)
    (T t : ℝ) (ht : |t| ≤ T)
    (hNP : ∀ u : ℕ, cellHalaszThreshold ≤ u → u ≤ 3 * ((A + Δ) / q) →
      NonPretentiousAt g (2 * D) u) :
    ‖∑ n ∈ Finset.Icc 1 ((A + Δ) / q),
        (cellBlockCoeff g A (A + Δ) P rest q n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
      ≤ cellHalaszBound D δ₀ T (A / q) ((A + Δ) / q) P rest := by
  rw [sum_cellBlockCoeff_Icc_eq]
  exact norm_typicalS_quot_block_poly_le g hcm hg h1 A (A + Δ) q hq
    (Nat.le_add_right A Δ) (by omega) P hP rest hrest D hD δ₀ hδ0 hδ1 T t ht hNP

/-- The same, under non-pretentiousness on one range of scales shared by every
cell: `(A+Δ)/q ≤ A+Δ`, so a bound for `u ≤ 3(A+Δ)` serves each cell at once. -/
theorem norm_cellBlock_poly_le_cellHalaszBound_of_uniform (g : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC g) (hg : ∀ n, ‖g n‖ ≤ 1) (h1 : g 1 = 1)
    (A Δ q : ℕ) (hq : 1 ≤ q) (hΔA : Δ ≤ A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (hrest : ∀ Q ∈ rest, ∀ p ∈ Q, p.Prime)
    (D : ℝ) (hD : 1 ≤ D) (δ₀ : ℝ) (hδ0 : 0 < δ₀) (hδ1 : δ₀ ≤ 1)
    (T t : ℝ) (ht : |t| ≤ T)
    (hNP : ∀ u : ℕ, cellHalaszThreshold ≤ u → u ≤ 3 * (A + Δ) →
      NonPretentiousAt g (2 * D) u) :
    ‖∑ n ∈ Finset.Icc 1 ((A + Δ) / q),
        (cellBlockCoeff g A (A + Δ) P rest q n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
      ≤ cellHalaszBound D δ₀ T (A / q) ((A + Δ) / q) P rest :=
  norm_cellBlock_poly_le_cellHalaszBound g hcm hg h1 A Δ q hq hΔA P hP rest hrest
    D hD δ₀ hδ0 hδ1 T t ht (fun u hu hu' => hNP u hu
      (le_trans hu' (Nat.mul_le_mul_left 3 (Nat.div_le_self _ _))))

/-- **The per-cell Halász bound is strictly positive** on a nonempty block.

`cellHalaszBound = 2^{|rest|} · (P-smooth harmonic mass up to B) · (max cost)`.
The mass contains the factor `n₁ = 1`, and the maximum dominates the cost of
that factor: on a long block the Abel term is a positive budget over a positive
scale, on a short block it is the harmonic mass of a nonempty block.  This is
what the capstone's `hδ0 : 0 < δ v` asks for. -/
theorem cellHalaszBound_pos (D δ₀ T : ℝ) (hδ0 : 0 < δ₀) (hT : 0 ≤ T)
    (Aq Bq : ℕ) (hAq : 1 ≤ Aq) (hAB : Aq < Bq)
    (P : Finset ℕ) (rest : List (Finset ℕ)) :
    0 < cellHalaszBound D δ₀ T Aq Bq P rest := by
  classical
  unfold cellHalaszBound
  have hpow : (0:ℝ) < ((2 ^ rest.length : ℕ) : ℝ) := by positivity
  -- the smooth mass contains `n₁ = 1`
  have hone : 1 ∈ (Finset.Icc 1 Bq).filter (fun n => n.primeFactors ⊆ P) := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_refl 1, by omega⟩, by simp⟩
  have hmass : 0 < pSmoothHarmonicMass Bq P := by
    unfold pSmoothHarmonicMass
    refine Finset.sum_pos' (fun n _ => by positivity) ⟨1, hone, by norm_num⟩
  -- the maximum dominates the cost at `n₁ = 1`, which is positive
  have hcost1 : 0 < cellHalaszQuotientCost D δ₀ T (Aq / 1) (Bq / 1) := by
    rw [Nat.div_one, Nat.div_one]
    unfold cellHalaszQuotientCost
    split_ifs with hlong
    · unfold cellHalaszLongCost
      have hAq' : (0:ℝ) < (Aq:ℝ) := by exact_mod_cast (by omega : 0 < Aq)
      have hbud : 0 < cellHalaszPartialBudget D δ₀ Bq := by
        unfold cellHalaszPartialBudget
        have hBq : Real.exp 1 ≤ 3 * (Bq:ℝ) := by
          have h1 : (cellHalaszThreshold:ℝ) ≤ (Bq:ℝ) := by exact_mod_cast hlong
          have h2 : (cellHalaszThreshold:ℝ) = 10^16 := by
            unfold cellHalaszThreshold; norm_num
          have he : Real.exp 1 ≤ 2.72 := by
            have := Real.exp_one_lt_d9; linarith
          nlinarith
        have := ExpSums.halaszBudgetShell_nonneg D _ hBq
        have hthr : (0:ℝ) ≤ (cellHalaszThreshold:ℝ) := by positivity
        have : (0:ℝ) ≤ ExpSums.halaszBudgetShell D (3 * (Bq:ℝ)) / (18 * δ₀) := by positivity
        have : (0:ℝ) ≤ Real.exp 1 * (Bq:ℝ) * δ₀ := by positivity
        linarith
      have habel : 0 < cellHalaszAbelFactor T := by
        unfold cellHalaszAbelFactor
        have := Real.pi_pos
        nlinarith
      have htail : 0 ≤ cellHalaszDivisionTail Aq Bq := by
        unfold cellHalaszDivisionTail
        exact Finset.sum_nonneg fun n _ => by positivity
      have : 0 < cellHalaszPartialBudget D δ₀ Bq * cellHalaszAbelFactor T / (Aq:ℝ) := by
        positivity
      linarith
    · unfold cellHalaszTrivialCost
      refine Finset.sum_pos' (fun n _ => by positivity) ⟨Bq, ?_, ?_⟩
      · rw [Finset.mem_Ioc]; exact ⟨hAB, le_refl _⟩
      · have : (0:ℝ) < (Bq:ℝ) := by exact_mod_cast (by omega : 0 < Bq)
        positivity
  have hbudget : 0 < cellHalaszQuotientBudget D δ₀ T Aq Bq P := by
    unfold cellHalaszQuotientBudget
    refine lt_of_lt_of_le hcost1 (Finset.le_max' _ _ ?_)
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hone)
  positivity

end Tao2015

end MoltResearch
