import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5InnerBandScheduleSharpCellsWide

/-!
# Wide sharp-cell schedule with a fixed exceptional share

The exceptional band is assigned one half of the band budget.  Ordinary level
`j` receives `2⁻⁽ʲ⁺²⁾`; these shifted geometric shares still sum to at most
one for every ladder length.
-/

namespace MoltResearch

namespace Tao2015

/-- The ordinary shifted geometric shares together with a final share of one
half have total mass at most one. -/
theorem shifted_shares_le_one (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1),
        (if j = J then (1 : ℝ) / 2 else 1 / 2 ^ (j + 2)) ≤ 1 := by
  have hclosed : ∀ k : ℕ,
      ∑ j ∈ Finset.range k, (1 : ℝ) / 2 ^ (j + 2)
        = 1 / 2 - 1 / 2 ^ (k + 1) := by
    intro k
    induction k with
    | zero => norm_num
    | succ i ih =>
        rw [Finset.sum_range_succ, ih]
        have hpow : (0 : ℝ) < 2 ^ (i + 1) := by positivity
        have hpow' : (0 : ℝ) < 2 ^ (i + 2) := by positivity
        field_simp
        ring
  rw [Finset.sum_range_succ]
  have hord :
      ∑ j ∈ Finset.range J,
          (if j = J then (1 : ℝ) / 2 else 1 / 2 ^ (j + 2))
        = ∑ j ∈ Finset.range J, (1 : ℝ) / 2 ^ (j + 2) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [Nat.ne_of_lt (Finset.mem_range.mp hj)]
  rw [hord, hclosed]
  simp only [ite_true]
  have hpos : (0 : ℝ) < 1 / 2 ^ (J + 1) := by positivity
  linarith

theorem innerBand_level_leg_of_main_wide_shifted
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta H : ℕ) (hA : 1 ≤ A) (hDeltaA : Delta ≤ A)
    (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ) (J j : ℕ) (hjJ : j < J)
    (hPl : ∀ i < J, ∀ p ∈ Pl i, p.Prime)
    (hPu : ∀ p ∈ Pu, p.Prime)
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
    (hcollisionFitWide : 8 * collisionEnergyBoundWide A (Pl j) T
      ≤ kappaCollision * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hshare : (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (2 * kappaMain + 2 * kappaReplacement + 2 * kappaCollision)
      ≤ (1 : ℝ) / 2 ^ (j + 2)) :
    (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (∫ xi in bandPartOn (levelSmallSet Pl Nl v₀l v₁l g alpha) J
            {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
          ‖∑ m ∈ typicalS A (A + Delta) (innerBandLevels Pl Pu J),
              (g m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
      ≤ (1 / 2 ^ (j + 2))
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
  have hbudget (kappa : ℝ) :
      (2 * kappa) * bandBudget (c₃ / 2) eps ((Delta : ℝ) / (A : ℝ)) =
        kappa * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    unfold bandBudget
    ring
  have hmain' := hmain
  rw [← hbudget kappaMain] at hmain'
  have hreplacement' := hreplacement
  rw [← hbudget kappaReplacement] at hreplacement'
  have hcollisionFitWide' := hcollisionFitWide
  rw [← hbudget kappaCollision] at hcollisionFitWide'
  have hshare' : (4 * (H : ℝ) / (A : ℝ)) ^ 2
      * (2 * (2 * kappaMain) + 2 * (2 * kappaReplacement)
        + 2 * (2 * kappaCollision)) ≤ (1 : ℝ) / 2 ^ (j + 1) := by
    calc
      _ = 2 * ((4 * (H : ℝ) / (A : ℝ)) ^ 2
          * (2 * kappaMain + 2 * kappaReplacement + 2 * kappaCollision)) := by ring
      _ ≤ 2 * ((1 : ℝ) / 2 ^ (j + 2)) :=
        mul_le_mul_of_nonneg_left hshare (by norm_num)
      _ = (1 : ℝ) / 2 ^ (j + 1) := by
        rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
        ring
  have hraw := innerBand_level_leg_of_main_wide
    g hcm hg A Delta H hA hDeltaA Pl Pu J j hjJ hPl hPu hdisj hdisjU
    Nl v₀l v₁l hcov ql alpha K₁ K₂ T hT hTK₂
    (2 * kappaMain) (2 * kappaReplacement) (2 * kappaCollision)
    (c₃ / 2) eps (div_nonneg hc₃ (by norm_num))
    hmain' hreplacement' hcollisionFitWide' hshare'
  calc
    (4 * (H : ℝ) / (A : ℝ)) ^ 2
          * (∫ xi in bandPartOn (levelSmallSet Pl Nl v₀l v₁l g alpha) J
              {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
            ‖∑ m ∈ typicalS A (A + Delta) (innerBandLevels Pl Pu J),
                (g m / (m : ℂ))
                  * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
        ≤ (1 / 2 ^ (j + 1))
            * bandBudget (c₃ / 2) eps ((Delta : ℝ) / (A : ℝ)) := hraw
    _ = (1 / 2 ^ (j + 2))
            * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
      unfold bandBudget
      rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
      ring

theorem band_energy_typicalS_le_of_cellUniform_fit_recut_wide_shifted
    [HalaszLargeValuesAssumption] [PrimeLargeValuesAssumption]
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta H : ℕ) (hA : 0 < A) (hH : 0 < H) (hDeltaA : Delta ≤ A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPA : ∀ p ∈ P, p * p ≤ A)
    (rest : List (Finset ℕ))
    (N v0 v1 : ℕ) (hN : 0 < N)
    (hcov : (Finset.Ico v0 (v1 + 1)).biUnion (eadicCell P (2 * N)) = P)
    (hstable : ∀ p ∈ P, ∀ m,
      HasFactorInAll rest (p * m) ↔ HasFactorInAll rest m)
    (q : ℕ → ℕ)
    (hqup : ∀ v ∈ Finset.Ico v0 (v1 + 1),
      (q v : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ))))
    (hq1 : ∀ v, 1 ≤ q v)
    (hqmin : ∀ v ∈ Finset.Ico v0 (v1 + 1),
      ∀ p ∈ eadicCell P (2 * N) v, q v ≤ p)
    (hqratio : ∀ v ∈ Finset.Ico v0 (v1 + 1),
      ∀ p ∈ eadicCell P (2 * N) v, N * p ≤ (N + 1) * q v)
    (hLA : ∀ v ∈ Finset.Ico v0 (v1 + 1),
      ∀ p ∈ eadicCell P (2 * N) v, A / (N * p) + 1 ≤ A / p)
    (hLB : ∀ v ∈ Finset.Ico v0 (v1 + 1),
      ∀ p ∈ eadicCell P (2 * N) v,
        (A + Delta) / (N * p) + 1 ≤ (A + Delta) / p)
    (w : ℝ → ℝ) (hwm : Measurable w) (hw0 : ∀ xi, 0 ≤ w xi)
    (hwsup : ∀ xi, w xi ≤ (4 * (H : ℝ) / (A : ℝ)) ^ 2)
    (K1 K2 : ℝ)
    (J : ℕ) (Pset : ℕ → Set ℝ) (hPset : ∀ j, MeasurableSet (Pset j))
    (c3 eps : ℝ) (hc3 : 0 ≤ c3)
    (hleg : ∀ j ∈ Finset.range (J + 1), j ≠ J →
      (4 * (H : ℝ) / (A : ℝ)) ^ 2
          * ∫ xi in bandPartOn Pset J {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} j,
            ‖∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2
        ≤ (1 / 2 ^ (j + 2)) * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)))
    (Pc : ℕ → ℕ) (hPc : ∀ v ∈ Finset.Ico v0 (v1 + 1), 2 ≤ Pc v)
    (hlo : ∀ v ∈ Finset.Ico v0 (v1 + 1),
      ∀ p ∈ eadicCell P (2 * N) v, Pc v < p)
    (hhi : ∀ v ∈ Finset.Ico v0 (v1 + 1),
      ∀ p ∈ eadicCell P (2 * N) v, p ≤ 2 * Pc v)
    (T : ℝ) (hT1 : 1 ≤ T) (hTK2 : K2 + 2 ≤ T)
    (ell : ℕ → ℕ) (hell : ∀ v ∈ Finset.Ico v0 (v1 + 1), 1 ≤ ell v)
    (Vsplit delta lam : ℕ → ℝ)
    (hVsplit : ∀ v ∈ Finset.Ico v0 (v1 + 1), 0 < Vsplit v)
    (hlam : ∀ v ∈ Finset.Ico v0 (v1 + 1), 0 < lam v)
    (hdelta : ∀ v ∈ Finset.Ico v0 (v1 + 1), ∀ t : ℝ, |t| ≤ T →
      ‖∑ n ∈ Finset.Icc 1 ((A + Delta) / q v),
          (cellBlockCoeff g A (A + Delta) P rest (q v) n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ delta v)
    (kappa' : ℕ → ℝ)
    (hfit : ∀ v ∈ Finset.Ico v0 (v1 + 1),
      2 * ((Vsplit v) ^ 2
            * (64 * ((((A + Delta) / q v : ℕ) : ℝ)
                + ((cellsMeetingSet (bandCells K2)
                    (bandPartOn Pset J {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} J)).card : ℝ)
                    * Real.sqrt T)
              * (Real.log (2 * T) + 1)
              * ∑ n ∈ Finset.Icc 1 ((A + Delta) / q v),
                  ‖cellBlockCoeff g A (A + Delta) P rest (q v) n‖ ^ 2 /
                    (n : ℝ) ^ 2)
          + (delta v) ^ 2
            * ((64 * (∑ p ∈ eadicCell P (2 * N) v,
                    ‖g p‖ ^ 2 / (p : ℝ) ^ 2)
                * (Pc v : ℝ) / Real.log (Pc v))
              * (1 + primeHighMomentCountCost (Pc v) (ell v)
                  (eadicCell P (2 * N) v) T (Vsplit v) (lam v)
                * Real.exp (-(Real.log (Pc v) /
                  (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
                * (Real.log (2 * T)) ^ 2)))
        ≤ kappa' v * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)))
    (hfitU : 2 * ((Finset.Ico v0 (v1 + 1)).card : ℝ)
          * (∑ v ∈ Finset.Ico v0 (v1 + 1), kappa' v)
          * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ))
        + 2 * (2 * replacementEnergyBoundWide A P N T
            + 2 * (4 * collisionEnergyBoundWide A P T))
      ≤ (1 / 2) * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)) /
          (4 * (H : ℝ) / (A : ℝ)) ^ 2) :
    (∫ xi in {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2},
        ‖∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
          * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2 * w xi)
      ≤ bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)) := by
  let G : Set ℝ := bandPartOn Pset J {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} J
  let Kcov : Finset ℤ := cellsMeetingSet (bandCells K2) G
  let I := Finset.Ico v0 (v1 + 1)
  let error : ℝ → ℂ := fun xi =>
    typicalSCellReplacement g A (A + Delta) P rest N v0 v1 q xi
      + typicalSAdjustedCollision g A (A + Delta) P rest N v0 v1 xi
  have _hscale := hqup
  have hAone : 1 ≤ A := hA
  have hAreal : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hHreal : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hCw : (0 : ℝ) < (4 * (H : ℝ) / (A : ℝ)) ^ 2 := by positivity
  have hT : (0 : ℝ) < T := by linarith
  have hGT : G ⊆ Set.Ioc (-T) T := by
    intro xi hxi
    have h := inner_band_subset_Icc K1 K2 (bandPartOn_subset Pset J _ J hxi)
    rw [Set.mem_Icc] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hGm : MeasurableSet G :=
    bandPartOn_measurableSet Pset hPset J _ (measurableSet_inner_band K1 K2) J
  have hcoverBand : G ⊆ ⋃ k ∈ bandCells K2, Set.Ico (k : ℝ) ((k : ℝ) + 1) :=
    (bandPartOn_subset Pset J _ J).trans (inner_band_subset_bandCells K1 K2)
  have hcoverCov : G ⊆ ⋃ k ∈ Kcov, Set.Ico (k : ℝ) ((k : ℝ) + 1) := by
    intro xi hxi
    have hxcover := hcoverBand hxi
    rw [Set.mem_iUnion₂] at hxcover
    obtain ⟨k, hk, hxik⟩ := hxcover
    have hkcov : k ∈ Kcov := by
      dsimp [Kcov]
      rw [mem_cellsMeetingSet]
      exact ⟨hk, xi, ⟨hxik.1, hxik.2.le⟩, hxi⟩
    exact Set.mem_iUnion₂.mpr ⟨k, hkcov, hxik⟩
  have hKTCov : ∀ k ∈ Kcov, -T ≤ (k : ℝ) ∧ (k : ℝ) + 1 ≤ T := by
    intro k hk
    have hkband : k ∈ bandCells K2 := (mem_cellsMeetingSet.mp hk).1
    exact bandCells_mem_Icc K2 T hTK2 k hkband
  have hFc : Continuous fun xi : ℝ =>
      ∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
        * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ) :=
    ExpSums.continuous_char_poly (typicalS A (A + Delta) (P :: rest))
      (fun m => g m / (m : ℂ)) (fun m => Real.log m)
  have hwnorm : ∀ xi, ‖w xi‖ ≤ (4 * (H : ℝ) / (A : ℝ)) ^ 2 := fun xi => by
    rw [Real.norm_of_nonneg (hw0 xi)]
    exact hwsup xi
  have herrorc : Continuous error :=
    (continuous_typicalSCellReplacement g A (A + Delta) P rest N v0 v1 q).add
      (continuous_typicalSAdjustedCollision g A (A + Delta) P rest N v0 v1)
  have hX : ∀ v ∈ I, Continuous fun xi : ℝ =>
      (∑ p ∈ eadicCell P (2 * N) v, (g p / (p : ℂ))
          * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
        * (∑ n ∈ Finset.Icc 1 ((A + Delta) / q v),
          (cellBlockCoeff g A (A + Delta) P rest (q v) n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ)) := by
    intro v hv
    exact (ExpSums.continuous_char_poly (eadicCell P (2 * N) v)
      (fun p => g p / (p : ℂ)) (fun p => Real.log p)).mul
        (ExpSums.continuous_char_poly (Finset.Icc 1 ((A + Delta) / q v))
          (fun n => cellBlockCoeff g A (A + Delta) P rest (q v) n / (n : ℂ))
          (fun n => Real.log n))
  have hdecomp : ∀ xi ∈ G,
      ∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
          * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)
        = (∑ v ∈ I, (∑ p ∈ eadicCell P (2 * N) v, (g p / (p : ℂ))
              * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
            * (∑ n ∈ Finset.Icc 1 ((A + Delta) / q v),
              (cellBlockCoeff g A (A + Delta) P rest (q v) n / (n : ℂ))
                * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ)))
          + error xi := by
    intro xi hxi
    rw [typicalS_phase_eq_cellUniform_add_errors g hcm A Delta P hP rest N v0 v1
      hcov hstable q xi]
    congr 1
    unfold typicalSCellUniformMain levelCellPoly
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [sum_cellBlockCoeff_Icc_eq g A (A + Delta) P rest (q v) xi]
  have hfac0 := setIntegral_norm_sq_le_family_of_decomp
    (fun xi => ∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
      * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
    I _ error hX herrorc T G hGm hGT hdecomp
  simp_rw [norm_mul, mul_pow] at hfac0
  have hrepl : (∫ xi in G,
        ‖typicalSCellReplacement g A (A + Delta) P rest N v0 v1 q xi‖ ^ 2)
      ≤ replacementEnergyBoundWide A P N T :=
    setIntegral_norm_sq_typicalSCellReplacement_wide_le g hg A (A + Delta)
      hAone (Nat.le_add_right A Delta) (by omega) P hP rest N v0 v1 hN hcov
      q hq1 hqmin hqratio T hT G hGT
  have hcoll : (∫ xi in G,
        ‖typicalSAdjustedCollision g A (A + Delta) P rest N v0 v1 xi‖ ^ 2)
      ≤ 4 * collisionEnergyBoundWide A P T :=
    (ExpSums.setIntegral_le_intervalIntegral_of_nonneg
      (fun xi => ‖typicalSAdjustedCollision g A (A + Delta) P rest N v0 v1 xi‖ ^ 2)
      ((continuous_typicalSAdjustedCollision g A (A + Delta) P rest N v0 v1).norm.pow 2)
      (fun xi => sq_nonneg _) T hT.le G hGT).trans
      (intervalIntegral_norm_sq_typicalSAdjustedCollision_wide_le g hg A
        (A + Delta) hAone (by omega) P hP rest N v0 v1 hcov T hT)
  have hsplit : (∫ xi in G, ‖error xi‖ ^ 2)
      ≤ 2 * replacementEnergyBoundWide A P N T
        + 2 * (4 * collisionEnergyBoundWide A P T) := by
    have htri := ExpSums.setIntegral_norm_add_sq_le
      (typicalSCellReplacement g A (A + Delta) P rest N v0 v1 q)
      (typicalSAdjustedCollision g A (A + Delta) P rest N v0 v1)
      (continuous_typicalSCellReplacement g A (A + Delta) P rest N v0 v1 q)
      (continuous_typicalSAdjustedCollision g A (A + Delta) P rest N v0 v1)
      T G hGm hGT
    dsimp [error]
    linarith [htri, hrepl, hcoll]
  have hfac : (∫ xi in G,
        ‖∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
          * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
      ≤ 2 * (I.card : ℝ) * ∑ v ∈ I, (∫ xi in G,
          ‖∑ p ∈ eadicCell P (2 * N) v, (g p / (p : ℂ))
              * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ)‖ ^ 2
            * ‖∑ n ∈ Finset.Icc 1 ((A + Delta) / q v),
              (cellBlockCoeff g A (A + Delta) P rest (q v) n / (n : ℂ))
                * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ)‖ ^ 2)
        + 2 * (2 * replacementEnergyBoundWide A P N T
            + 2 * (4 * collisionEnergyBoundWide A P T)) := by
    linarith [hfac0, hsplit]
  exact band_energy_le_budget_of_exceptional_family_recut
    (fun xi => ∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
      * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
    w hw0 ((4 * (H : ℝ) / (A : ℝ)) ^ 2) hCw hwsup
    {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} (Finset.range (J + 1))
    (bandPartOn Pset J {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2})
    (fun j _ => bandPartOn_measurableSet Pset hPset J _
      (measurableSet_inner_band K1 K2) j)
    (bandPartOn_pairwiseDisjoint Pset J _)
    (bandPartOn_cover Pset J _)
    (fun j _ => integrableOn_norm_sq_inner_band _ hFc K1 K2 _
      (bandPartOn_subset Pset J _ j))
    (fun j _ => integrableOn_norm_sq_mul_inner_band _ hFc w hwm _ hwnorm K1 K2 _
      (bandPartOn_subset Pset J _ j))
    (fun j => if j = J then 1 / 2 else 1 / 2 ^ (j + 2))
    c3 eps ((Delta : ℝ) / (A : ℝ)) hc3
    (by positivity) (shifted_shares_le_one J) J
    (Finset.mem_range.mpr (Nat.lt_succ_self J)) (fun j hj hne => by
      simpa [hne] using hleg j hj hne)
    I Pc hPc (fun v => eadicCell P (2 * N) v)
    (fun v hv p hp => hP p (mem_eadicCell.mp hp).1) hlo hhi
    (fun _ => g) (fun _ _ p => hg p) ell hell
    (fun v => (A + Delta) / q v)
    (fun v => cellBlockCoeff g A (A + Delta) P rest (q v)) T hT1
    Kcov hcoverCov hKTCov Vsplit delta lam hVsplit hlam hdelta
    (2 * (I.card : ℝ))
    (2 * (2 * replacementEnergyBoundWide A P N T
      + 2 * (4 * collisionEnergyBoundWide A P T)))
    (by positivity) hfac
    (fun v => 64 * ((((A + Delta) / q v : ℕ) : ℝ)
        + (Kcov.card : ℝ) * Real.sqrt T) * (Real.log (2 * T) + 1)
      * ∑ n ∈ Finset.Icc 1 ((A + Delta) / q v),
          ‖cellBlockCoeff g A (A + Delta) P rest (q v) n‖ ^ 2 / (n : ℝ) ^ 2)
    (fun v => 64 * (∑ p ∈ eadicCell P (2 * N) v,
        ‖g p‖ ^ 2 / (p : ℝ) ^ 2) * (Pc v : ℝ) / Real.log (Pc v))
    (fun v => primeHighMomentCountCost (Pc v) (ell v) (eadicCell P (2 * N) v)
        T (Vsplit v) (lam v)
      * Real.exp (-(Real.log (Pc v) / (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
      * (Real.log (2 * T)) ^ 2)
    (fun v _ => rfl) (fun v _ => rfl) (fun v _ => rfl) kappa' (by
      intro v hv
      simpa [I, Kcov, G] using hfit v hv) (by simpa [I] using hfitU)

set_option maxHeartbeats 800000 in
/-- The wide sharp-cell capstone.  Ordinary main terms remain independent
inputs, while both error legs are the single-polynomial estimates, cell
representatives use only their upper scale, and the exceptional quotient
keeps only level zero inside the sharp inclusion--exclusion bound. -/
theorem band_energy_typicalS_le_of_schedule_sharp_cells_wide'
    [HalaszLargeValuesAssumption] [PrimeLargeValuesAssumption]
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta H : ℕ) (hA : 0 < A) (hH : 0 < H) (hDeltaA : Delta ≤ A)
    (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ) (J : ℕ) (hJ : 0 < J)
    (hPl : ∀ i < J, ∀ p ∈ Pl i, p.Prime)
    (hPu : ∀ p ∈ Pu, p.Prime)
    (hPAu : ∀ p ∈ Pu, p * p ≤ A)
    (hdisj : ∀ i < J, ∀ k < J, i ≠ k → Disjoint (Pl i) (Pl k))
    (hdisjU : ∀ i < J, Disjoint (Pl i) Pu)
    (Nl v0l v1l : ℕ → ℕ) (ql : ℕ → ℕ → ℕ) (alpha : ℕ → ℝ)
    (hNl : ∀ j < J, 0 < Nl j)
    (hcovl : ∀ j < J, (Finset.Ico (v0l j) (v1l j + 1)).biUnion
      (eadicCell (Pl j) (2 * Nl j)) = Pl j)
    (hqupl : ∀ j < J, ∀ v ∈ Finset.Ico (v0l j) (v1l j + 1),
      (ql j v : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (Nl j : ℝ))))
    (hq1l : ∀ j < J, ∀ v, 1 ≤ ql j v)
    (hqminl : ∀ j < J, ∀ v ∈ Finset.Ico (v0l j) (v1l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v, ql j v ≤ p)
    (hqratiol : ∀ j < J, ∀ v ∈ Finset.Ico (v0l j) (v1l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
        Nl j * p ≤ (Nl j + 1) * ql j v)
    (K1 K2 T : ℝ) (hT1 : 1 ≤ T) (hTK2 : K2 + 2 ≤ T)
    (c3 eps : ℝ) (hc3 : 0 ≤ c3)
    (kappaMain kappaReplacement kappaCollision : ℕ → ℝ)
    (hmain : ∀ j < J,
      (∫ xi in bandPartOn (levelSmallSet Pl Nl v0l v1l g alpha) J
          {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} j,
        ‖typicalSCellUniformMain g A (A + Delta) (Pl j)
          (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j)
          (Nl j) (v0l j) (v1l j) (ql j) xi‖ ^ 2)
        ≤ kappaMain j * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)))
    (hfitReplacementWide : ∀ j < J,
      2 * replacementEnergyBoundWide A (Pl j) (Nl j) T
        ≤ kappaReplacement j * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)))
    (hfitCollisionWide : ∀ j < J,
      8 * collisionEnergyBoundWide A (Pl j) T
        ≤ kappaCollision j * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)))
    (hshare : ∀ j < J,
      2 * kappaMain j + 2 * kappaReplacement j + 2 * kappaCollision j
        ≤ (1 : ℝ) / 2 ^ (j + 2))
    (Nu v0u v1u : ℕ) (hNu : 0 < Nu)
    (hcovU : (Finset.Ico v0u (v1u + 1)).biUnion
      (eadicCell Pu (2 * Nu)) = Pu)
    (qu : ℕ → ℕ)
    (hqupU : ∀ v ∈ Finset.Ico v0u (v1u + 1),
      (qu v : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (Nu : ℝ))))
    (hq1U : ∀ v, 1 ≤ qu v)
    (hqminU : ∀ v ∈ Finset.Ico v0u (v1u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v, qu v ≤ p)
    (hqratioU : ∀ v ∈ Finset.Ico v0u (v1u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v, Nu * p ≤ (Nu + 1) * qu v)
    (hLAU : ∀ v ∈ Finset.Ico v0u (v1u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v, A / (Nu * p) + 1 ≤ A / p)
    (hLBU : ∀ v ∈ Finset.Ico v0u (v1u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v,
        (A + Delta) / (Nu * p) + 1 ≤ (A + Delta) / p)
    (w : ℝ → ℝ) (hwm : Measurable w) (hw0 : ∀ xi, 0 ≤ w xi)
    (hwsup : ∀ xi, w xi ≤ (4 * (H : ℝ) / (A : ℝ)) ^ 2)
    (PcU : ℕ → ℕ) (hPcU : ∀ v ∈ Finset.Ico v0u (v1u + 1), 2 ≤ PcU v)
    (hloU : ∀ v ∈ Finset.Ico v0u (v1u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v, PcU v < p)
    (hhiU : ∀ v ∈ Finset.Ico v0u (v1u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v, p ≤ 2 * PcU v)
    (ellU : ℕ → ℕ) (hellU : ∀ v ∈ Finset.Ico v0u (v1u + 1), 1 ≤ ellU v)
    (Vsplit lamU : ℕ → ℝ)
    (hVsplit : ∀ v ∈ Finset.Ico v0u (v1u + 1), 0 < Vsplit v)
    (hlamU : ∀ v ∈ Finset.Ico v0u (v1u + 1), 0 < lamU v)
    (x0 : ℕ) (hx0 : cellHalaszThreshold ≤ x0)
    (D delta0 A0 : ℝ) (hD : 1 ≤ D)
    (hdelta0 : 0 < delta0) (hdelta1 : delta0 ≤ 1) (hA0 : 3 ≤ A0)
    (hNPtop : NonPretentiousAt g A0 (2 * A + 1))
    (hrangeSharp :
      2 * Real.pi * T
          + 2 * Real.pi * (((halaszM (3 * (2 * A + 1)) : ℕ) : ℝ) + 1)
        ≤ (A0 / 3) * ((3 * (2 * A + 1) : ℕ) : ℝ))
    (hstrengthSharp :
      2 * D ≤ A0 / 3 - 2 * (Real.log (Real.log ((3 * (2 * A + 1) : ℕ) : ℝ))
        - Real.log (Real.log (x0 : ℝ)) + 12))
    (DeltaU : ℕ → ℝ)
    (hDeltaU0 : ∀ v ∈ Finset.Ico v0u (v1u + 1), 0 ≤ DeltaU v)
    (hDeltaU : ∀ v ∈ Finset.Ico v0u (v1u + 1),
      cellHalaszSharpBound x0 D delta0 (A / qu v) ((A + Delta) / qu v)
          Pu [Pl 0]
        + ladderSiftedLogMass (A / qu v) ((A + Delta) / qu v)
            ((List.range (J - 1)).map (fun i => Pl (i + 1)))
        ≤ DeltaU v)
    (kappaU : ℕ → ℝ)
    (hfitUCell : ∀ v ∈ Finset.Ico v0u (v1u + 1),
      2 * ((Vsplit v) ^ 2
            * (64 * ((((A + Delta) / qu v : ℕ) : ℝ)
                + ((cellsMeetingSet (bandCells K2)
                    (bandPartOn (levelSmallSet Pl Nl v0l v1l g alpha) J
                      {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} J)).card : ℝ)
                    * Real.sqrt T)
              * (Real.log (2 * T) + 1)
              * ∑ n ∈ Finset.Icc 1 ((A + Delta) / qu v),
                  ‖cellBlockCoeff g A (A + Delta) Pu ((List.range J).map Pl)
                    (qu v) n‖ ^ 2 / (n : ℝ) ^ 2)
          + (DeltaU v) ^ 2
            * ((64 * (∑ p ∈ eadicCell Pu (2 * Nu) v,
                    ‖g p‖ ^ 2 / (p : ℝ) ^ 2)
                * (PcU v : ℝ) / Real.log (PcU v))
              * (1 + primeHighMomentCountCost (PcU v) (ellU v)
                  (eadicCell Pu (2 * Nu) v) T (Vsplit v) (lamU v)
                * Real.exp (-(Real.log (PcU v) /
                  (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
                * (Real.log (2 * T)) ^ 2)))
        ≤ kappaU v * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)))
    (hfitU : 2 * ((Finset.Ico v0u (v1u + 1)).card : ℝ)
          * (∑ v ∈ Finset.Ico v0u (v1u + 1), kappaU v)
          * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ))
        + 2 * (2 * replacementEnergyBoundWide A Pu Nu T
            + 2 * (4 * collisionEnergyBoundWide A Pu T))
      ≤ (1 / 2) * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ))) :
    (∫ xi in {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2},
        ‖∑ m ∈ typicalS A (A + Delta) (innerBandLevels Pl Pu J),
            (g m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2 * w xi)
      ≤ (4 * (H : ℝ) / (A : ℝ)) ^ 2
          * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)) := by
  by_cases hzero : g 1 = 0
  · have hgzero : ∀ n, n ≠ 0 → g n = 0 := by
      intro n hn
      have hmul := hcm 1 n one_ne_zero hn
      simpa [hzero] using hmul
    have hsum : ∀ xi : ℝ,
        ∑ m ∈ typicalS A (A + Delta) (innerBandLevels Pl Pu J),
            (g m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ) = 0 := by
      intro xi
      apply Finset.sum_eq_zero
      intro m hm
      have hmA := (mem_typicalS.mp hm).1.1
      simp [hgzero m (by omega)]
    simp only [hsum, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_mul, MeasureTheory.integral_zero]
    exact mul_nonneg (sq_nonneg _) (bandBudget_nonneg c3 eps
      ((Delta : ℝ) / (A : ℝ)) hc3 (by positivity))
  have hg1 : g 1 = 1 := by
    have hmul := hcm 1 1 one_ne_zero one_ne_zero
    have hcancel : g 1 * g 1 = g 1 * 1 := by simpa using hmul.symm
    exact mul_left_cancel₀ hzero hcancel
  have hT : 0 < T := zero_lt_one.trans_le hT1
  have hA1 : 1 ≤ A := hA
  let Cw : ℝ := (4 * (H : ℝ) / (A : ℝ)) ^ 2
  have hCw : 0 < Cw := by dsimp [Cw]; positivity
  have hbudgetScale :
      bandBudget (Cw * c3) eps ((Delta : ℝ) / (A : ℝ)) =
        Cw * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)) := by
    unfold bandBudget
    ring
  have hbudgetCancel (x : ℝ) :
      x / Cw * bandBudget (Cw * c3) eps ((Delta : ℝ) / (A : ℝ)) =
        x * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)) := by
    rw [hbudgetScale]
    field_simp
  let Pset := levelSmallSet Pl Nl v0l v1l g alpha
  have hPset : ∀ j, MeasurableSet (Pset j) :=
    levelSmallSet_measurableSet Pl Nl v0l v1l g alpha
  have hlevelLeg : ∀ j ∈ Finset.range (J + 1), j ≠ J →
      (4 * (H : ℝ) / (A : ℝ)) ^ 2
          * ∫ xi in bandPartOn Pset J {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} j,
            ‖∑ m ∈ typicalS A (A + Delta) (innerBandLevels Pl Pu J),
                (g m / (m : ℂ))
                  * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2
        ≤ (1 / 2 ^ (j + 2))
            * bandBudget (Cw * c3) eps ((Delta : ℝ) / (A : ℝ)) := by
    intro j hj hne
    have hjJ : j < J := by rw [Finset.mem_range] at hj; omega
    have hmain' :
        (∫ xi in bandPartOn Pset J {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} j,
          ‖typicalSCellUniformMain g A (A + Delta) (Pl j)
            (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j)
            (Nl j) (v0l j) (v1l j) (ql j) xi‖ ^ 2)
          ≤ kappaMain j / Cw
              * bandBudget (Cw * c3) eps ((Delta : ℝ) / (A : ℝ)) := by
      rw [hbudgetCancel]
      simpa [Pset] using hmain j hjJ
    have hrepl := innerBand_replacement_leg_wide g hg A Delta hA1 hDeltaA
      Pl Pu Nl v0l v1l ql alpha J j (hNl j hjJ) (hPl j hjJ)
      (hcovl j hjJ) (hqupl j hjJ) (hq1l j hjJ) (hqminl j hjJ)
      (hqratiol j hjJ) K1 K2 T hT hTK2 (Cw * c3) eps
      (kappaReplacement j / Cw) (by
        rw [hbudgetCancel]
        exact hfitReplacementWide j hjJ)
    have hshare' : (4 * (H : ℝ) / (A : ℝ)) ^ 2
          * (2 * (kappaMain j / Cw) + 2 * (kappaReplacement j / Cw)
            + 2 * (kappaCollision j / Cw))
        ≤ (1 : ℝ) / 2 ^ (j + 2) := by
      calc
        _ = 2 * kappaMain j + 2 * kappaReplacement j + 2 * kappaCollision j := by
          change Cw * _ = _
          field_simp
        _ ≤ _ := hshare j hjJ
    exact innerBand_level_leg_of_main_wide_shifted g hcm hg A Delta H hA1 hDeltaA
      Pl Pu J j hjJ hPl hPu hdisj hdisjU Nl v0l v1l (hcovl j hjJ)
      ql alpha K1 K2 T hT hTK2 (kappaMain j / Cw)
      (kappaReplacement j / Cw) (kappaCollision j / Cw) (Cw * c3) eps
      (mul_nonneg hCw.le hc3) hmain' hrepl (by
        rw [hbudgetCancel]
        exact hfitCollisionWide j hjJ) hshare'
  let restU := (List.range J).map Pl
  let ladder := (List.range (J - 1)).map (fun i => Pl (i + 1))
  have hrest : restU = [Pl 0] ++ ladder := by
    simpa [restU, ladder] using map_range_eq_cons_shifted Pl J hJ
  have hbase : ∀ Q ∈ ([Pl 0] : List (Finset ℕ)), ∀ p ∈ Q, p.Prime := by
    intro Q hQ p hp
    simp only [List.mem_singleton] at hQ
    subst Q
    exact hPl 0 hJ p hp
  have hNPsharp : NonPretentiousAt g (A0 / 3) (3 * (2 * A + 1)) := by
    apply nonPretentiousAt_scale_up_of_norm_le_one (c := 3) hg hNPtop
    · omega
    · norm_num [Nat.cast_mul, Nat.cast_add]
    · positivity
    · norm_num
    · ring_nf
      exact le_rfl
  have hdelta : ∀ v ∈ Finset.Ico v0u (v1u + 1), ∀ t : ℝ, |t| ≤ T →
      ‖∑ n ∈ Finset.Icc 1 ((A + Delta) / qu v),
          (cellBlockCoeff g A (A + Delta) Pu restU (qu v) n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ DeltaU v := by
    intro v hv t ht
    rw [hrest]
    exact (norm_cellBlock_poly_le_cellHalaszSharpBound_split_of_top
      g hcm hg hg1
      A Delta (qu v) Pu hPu [Pl 0] ladder hbase x0 hx0 D hD delta0 hdelta0
      hdelta1 (A0 / 3) (3 * (2 * A + 1)) hNPsharp (by linarith [hA0])
      (by have hq := Nat.div_le_self (A + Delta) (qu v); omega)
      T hrangeSharp hstrengthSharp t ht).trans (by
        simpa [ladder] using hDeltaU v hv)
  have hstableU := innerBandExceptional_stable_of_disjoint Pl Pu J hPl hPu hdisjU
  have htyp : typicalS A (A + Delta) (innerBandLevels Pl Pu J) =
      typicalS A (A + Delta) (Pu :: restU) := by
    simpa [innerBandLevels, restU] using
      typicalS_middle A (A + Delta) ((List.range J).map Pl) [] Pu
  have hlegU : ∀ j ∈ Finset.range (J + 1), j ≠ J →
      (4 * (H : ℝ) / (A : ℝ)) ^ 2
          * ∫ xi in bandPartOn Pset J {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} j,
            ‖∑ m ∈ typicalS A (A + Delta) (Pu :: restU),
                (g m / (m : ℂ))
                  * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2
        ≤ (1 / 2 ^ (j + 2))
            * bandBudget (Cw * c3) eps ((Delta : ℝ) / (A : ℝ)) := by
    intro j hj hne
    rw [← htyp]
    exact hlevelLeg j hj hne
  have hfitU' : 2 * ((Finset.Ico v0u (v1u + 1)).card : ℝ)
          * (∑ v ∈ Finset.Ico v0u (v1u + 1), kappaU v / Cw)
          * bandBudget (Cw * c3) eps ((Delta : ℝ) / (A : ℝ))
        + 2 * (2 * replacementEnergyBoundWide A Pu Nu T
            + 2 * (4 * collisionEnergyBoundWide A Pu T))
      ≤ (1 / 2) * bandBudget (Cw * c3) eps
          ((Delta : ℝ) / (A : ℝ)) / (4 * (H : ℝ) / (A : ℝ)) ^ 2 := by
    rw [hbudgetScale]
    change _ ≤ _ / Cw
    rw [← Finset.sum_div]
    convert hfitU using 1 <;> field_simp
  rw [htyp, ← hbudgetScale]
  exact band_energy_typicalS_le_of_cellUniform_fit_recut_wide_shifted g hcm hg
    A Delta H hA hH hDeltaA Pu hPu hPAu restU Nu v0u v1u hNu hcovU hstableU
    qu hqupU hq1U hqminU hqratioU hLAU hLBU w hwm hw0 hwsup K1 K2 J Pset
    hPset (Cw * c3) eps (mul_nonneg hCw.le hc3) hlegU PcU hPcU hloU hhiU
    T hT1 hTK2 ellU hellU Vsplit DeltaU lamU hVsplit hlamU hdelta
    (fun v => kappaU v / Cw) (by
      intro v hv
      rw [hbudgetCancel]
      simpa [restU, Pset] using hfitUCell v hv) hfitU'


end Tao2015

end MoltResearch
