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

end Tao2015

end MoltResearch
