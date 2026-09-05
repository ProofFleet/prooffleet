import MoltResearch.Discrepancy.BandCapstone
import MoltResearch.Discrepancy.LevelSizes
import MoltResearch.Discrepancy.PrimeMassCell

/-!
# The level legs of the `[mrt]` A.2 inner band (Track R, A2-III, VI-2)

The A.2 capstone takes the first-index partition abstractly.  This module binds
that partition to the small-value sets of the e-adic cell polynomials and then
composes the already proved level estimates with the schedule arithmetic.
-/

namespace MoltResearch

/-! ## The exact level decomposition -/

/-- The noncollision fibre in the Ramaré decomposition of the typical-set
polynomial. -/
noncomputable def typicalSMainFibre (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (p : ℕ) (xi : ℝ) : ℂ :=
  (g p / (p : ℂ))
      * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ)
      * ∑ m ∈ (((typicalS A B rest).filter (fun n => p ∣ n)).image (· / p)).filter
          (fun m => ¬ p ∣ m),
        ((g m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
          / (((P.filter (· ∣ m)).card : ℂ) + 1)

/-- The repeated-prime fibre left by the Ramaré decomposition. -/
noncomputable def typicalSCollision (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (xi : ℝ) : ℂ :=
  ∑ p ∈ P, ∑ m ∈ (((typicalS A B rest).filter
      (fun n => p ∣ n)).image (· / p)).filter (fun m => p ∣ m),
    ((g (p * m) / ((p * m : ℕ) : ℂ))
        * ((Real.fourierChar (-(Real.log (p * m : ℕ) * xi)) : Circle) : ℂ))
      / (((P.filter (· ∣ (p * m))).card : ℂ))

open Finset in
/-- **The exact typical-set decomposition, grouped by e-adic cells.**

The useful first half of the decomposition is purely algebraic:
`typicalS_phase_main_add_coll` supplies the corrected `1/(ω+1)` quotient
weight and the repeated-prime term, while disjointness of `eadicCell` changes
the outer prime sum into the level's cell range.  No estimate and no enlarged
quotient block enters this equality.

The cover is kept explicit because the analytic schedule normally indexes only
the cells between its endpoints `v₀` and `v₁`, rather than every cell from
zero. -/
theorem typicalS_phase_eq_eadic_main_add_collision
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g)
    (A B : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (xi : ℝ) :
    ∑ m ∈ typicalS A (A + B) (P :: rest), (g m / (m : ℂ))
        * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)
      = (∑ v ∈ Finset.Ico v₀ (v₁ + 1),
          ∑ p ∈ eadicCell P (2 * N) v,
            typicalSMainFibre g A (A + B) P rest p xi)
        + typicalSCollision g A (A + B) P rest xi := by
  classical
  rw [typicalS_phase_main_add_coll g hcm A B P hP rest xi]
  change (∑ p ∈ P, typicalSMainFibre g A (A + B) P rest p xi)
      + typicalSCollision g A (A + B) P rest xi = _
  congr 1
  have hdisj : Set.PairwiseDisjoint
      (↑(Finset.Ico v₀ (v₁ + 1)) : Set ℕ) (eadicCell P (2 * N)) :=
    fun v _ w _ hvw => eadicCell_disjoint P (2 * N) hvw
  calc
    ∑ p ∈ P, typicalSMainFibre g A (A + B) P rest p xi =
        ∑ p ∈ (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)),
          typicalSMainFibre g A (A + B) P rest p xi := by
            rw [hcov]
    _ = ∑ v ∈ Finset.Ico v₀ (v₁ + 1),
          ∑ p ∈ eadicCell P (2 * N) v,
            typicalSMainFibre g A (A + B) P rest p xi :=
      Finset.sum_biUnion hdisj

open MeasureTheory Finset ExpSums in
/-- **The exact decomposition costs one `L²` triangle.**

After the N3-f main term has been regrouped by cells, separating it from the
repeated-prime term costs precisely
`2 ∫‖main‖² + 2 ∫‖collision‖²`.  This is the pointwise inequality
`‖x+y‖² ≤ 2‖x‖²+2‖y‖²` integrated on the actual frequency set; the set is
not enlarged, so later small- and large-value information remains available.
-/
theorem setIntegral_norm_sq_typicalS_le_eadic_main_collision
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g)
    (A Delta : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (T : ℝ) (G : Set ℝ) (hGm : MeasurableSet G)
    (hGT : G ⊆ Set.Ioc (-T) T) :
    (∫ xi in G, ‖∑ m ∈ typicalS A (A + Delta) (P :: rest),
        (g m / (m : ℂ))
          * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
      ≤ 2 * (∫ xi in G,
          ‖∑ v ∈ Finset.Ico v₀ (v₁ + 1),
            ∑ p ∈ eadicCell P (2 * N) v,
              typicalSMainFibre g A (A + Delta) P rest p xi‖ ^ 2)
        + 2 * (∫ xi in G,
          ‖typicalSCollision g A (A + Delta) P rest xi‖ ^ 2) := by
  classical
  have hchar : ∀ w : ℝ, Continuous fun xi : ℝ =>
      ((Real.fourierChar (-(w * xi)) : Circle) : ℂ) := fun w =>
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hfibre : ∀ p : ℕ, Continuous fun xi : ℝ =>
      typicalSMainFibre g A (A + Delta) P rest p xi := by
    intro p
    unfold typicalSMainFibre
    refine (continuous_const.mul (hchar (Real.log p))).mul ?_
    refine continuous_finset_sum _ fun m _ => ?_
    exact (continuous_const.mul (hchar (Real.log m))).div_const _
  have hmain : Continuous fun xi : ℝ =>
      ∑ v ∈ Finset.Ico v₀ (v₁ + 1),
        ∑ p ∈ eadicCell P (2 * N) v,
          typicalSMainFibre g A (A + Delta) P rest p xi := by
    exact continuous_finset_sum _ fun v _ =>
      continuous_finset_sum _ fun p _ => hfibre p
  have hcollision : Continuous fun xi : ℝ =>
      typicalSCollision g A (A + Delta) P rest xi := by
    unfold typicalSCollision
    refine continuous_finset_sum _ fun p _ => ?_
    refine continuous_finset_sum _ fun m _ => ?_
    exact (continuous_const.mul (hchar (Real.log (p * m : ℕ)))).div_const _
  calc
    (∫ xi in G, ‖∑ m ∈ typicalS A (A + Delta) (P :: rest),
        (g m / (m : ℂ))
          * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
        = ∫ xi in G,
            ‖(∑ v ∈ Finset.Ico v₀ (v₁ + 1),
                ∑ p ∈ eadicCell P (2 * N) v,
                  typicalSMainFibre g A (A + Delta) P rest p xi)
              + typicalSCollision g A (A + Delta) P rest xi‖ ^ 2 := by
          apply setIntegral_congr_fun hGm
          intro xi _
          exact congrArg (· ^ 2) (congrArg norm
            (typicalS_phase_eq_eadic_main_add_collision g hcm A Delta P hP
              rest N v₀ v₁ hcov xi))
    _ ≤ 2 * (∫ xi in G,
          ‖∑ v ∈ Finset.Ico v₀ (v₁ + 1),
            ∑ p ∈ eadicCell P (2 * N) v,
              typicalSMainFibre g A (A + Delta) P rest p xi‖ ^ 2)
        + 2 * (∫ xi in G,
          ‖typicalSCollision g A (A + Delta) P rest xi‖ ^ 2) :=
      setIntegral_norm_add_sq_le _ _ hmain hcollision T G hGm hGT

/-! ## The quotient coefficients -/

/-- The `1/(ω_P+1)`-weighted coefficient of the quotient polynomial,
extended by zero away from its typical support. -/
noncomputable def typicalSQuotCoeff (g : ℕ → ℂ) (P S : Finset ℕ)
    (m : ℕ) : ℂ :=
  if m ∈ S then g m / (((P.filter (· ∣ m)).card : ℂ) + 1) else 0

/-- The Ramaré weight never enlarges a `1`-bounded coefficient. -/
theorem norm_typicalSQuotCoeff_le_one (g : ℕ → ℂ)
    (hg : ∀ m, ‖g m‖ ≤ 1) (P S : Finset ℕ) (m : ℕ) :
    ‖typicalSQuotCoeff g P S m‖ ≤ 1 := by
  classical
  unfold typicalSQuotCoeff
  split_ifs
  · rw [norm_div]
    have hden : ‖((P.filter (· ∣ m)).card : ℂ) + 1‖
        = ((P.filter (· ∣ m)).card : ℝ) + 1 := by
      rw [show ((P.filter (· ∣ m)).card : ℂ) + 1 =
          (((P.filter (· ∣ m)).card + 1 : ℕ) : ℂ) by push_cast; ring,
        Complex.norm_natCast]
      push_cast
      ring
    rw [hden, div_le_one (by positivity)]
    exact (hg m).trans (by
      have : (0 : ℝ) ≤ ((P.filter (· ∣ m)).card : ℝ) := by positivity
      linarith)
  · simp

/-- On every quotient block, the squared mass of the weighted typical
coefficient is no larger than the unweighted harmonic mass. -/
theorem typicalSQuotCoeff_mass_le (g : ℕ → ℂ)
    (hg : ∀ m, ‖g m‖ ≤ 1) (P S : Finset ℕ) (a b : ℕ) :
    ∑ m ∈ Finset.Ioc a b, ‖typicalSQuotCoeff g P S m‖ ^ 2 / (m : ℝ)
      ≤ ∑ m ∈ Finset.Ioc a b, (1 : ℝ) / (m : ℝ) := by
  classical
  refine Finset.sum_le_sum fun m hm => ?_
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (by have := (Finset.mem_Ioc.mp hm).1; omega : 0 < m)
  rw [div_le_div_iff₀ hm0 hm0]
  have hc := norm_typicalSQuotCoeff_le_one g hg P S m
  have hsq : ‖typicalSQuotCoeff g P S m‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (typicalSQuotCoeff g P S m)]
  exact mul_le_mul_of_nonneg_right hsq hm0.le

/-- The prime polynomial carried by one e-adic cell of a level. -/
noncomputable def levelCellPoly (P : Finset ℕ) (N v : ℕ) (g : ℕ → ℂ)
    (xi : ℝ) : ℂ :=
  ∑ p ∈ eadicCell P (2 * N) v, (g p / (p : ℂ))
    * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ)

/-- The frequencies where every cell polynomial of level `j` meets its
schedule threshold. -/
noncomputable def levelSmallSet (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ)
    (g : ℕ → ℂ) (alpha : ℕ → ℝ) (j : ℕ) : Set ℝ :=
  {xi | ∀ v ∈ Finset.Ico (v₀ j) (v₁ j + 1),
    ‖levelCellPoly (P j) (N j) v g xi‖
      ≤ Real.exp (-(alpha j * (v : ℝ) / ((2 * N j : ℕ) : ℝ)))}

@[simp] theorem mem_levelSmallSet
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (j : ℕ) (xi : ℝ) :
    xi ∈ levelSmallSet P N v₀ v₁ g alpha j ↔
      ∀ v ∈ Finset.Ico (v₀ j) (v₁ j + 1),
        ‖levelCellPoly (P j) (N j) v g xi‖
          ≤ Real.exp (-(alpha j * (v : ℝ) / ((2 * N j : ℕ) : ℝ))) :=
  Iff.rfl

/-- The level small-value sets are measurable. -/
theorem levelSmallSet_measurableSet
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (j : ℕ) :
    MeasurableSet (levelSmallSet P N v₀ v₁ g alpha j) := by
  classical
  rw [show levelSmallSet P N v₀ v₁ g alpha j =
      ⋂ v ∈ Finset.Ico (v₀ j) (v₁ j + 1),
        {xi : ℝ | ‖levelCellPoly (P j) (N j) v g xi‖
          ≤ Real.exp (-(alpha j * (v : ℝ) / ((2 * N j : ℕ) : ℝ)))} by
    ext xi
    simp]
  refine Finset.measurableSet_biInter _ fun v _ =>
    measurableSet_le ?_ measurable_const
  exact (ExpSums.continuous_char_poly (eadicCell (P j) (2 * N j) v)
    (fun p => g p / (p : ℂ)) (fun p => Real.log p)).norm.measurable

/-- On a nonexceptional first-index part, the current level is small in every
cell. -/
theorem levelSmallSet_small_of_mem_bandPartOn
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (J j : ℕ) (G : Set ℝ) (xi : ℝ)
    (hjJ : j < J)
    (hxi : xi ∈ bandPartOn (levelSmallSet P N v₀ v₁ g alpha) J G j) :
    ∀ v ∈ Finset.Ico (v₀ j) (v₁ j + 1),
      ‖levelCellPoly (P j) (N j) v g xi‖
        ≤ Real.exp (-(alpha j * (v : ℝ) / ((2 * N j : ℕ) : ℝ))) := by
  rw [bandPartOn, bandPart, if_pos hjJ] at hxi
  exact hxi.2.1

/-- On a later first-index part, failure of the previous level's smallness
selects a previous cell whose prime polynomial is large. -/
theorem exists_prev_cell_large_of_mem_bandPartOn
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (J j : ℕ) (G : Set ℝ) (xi : ℝ)
    (hj0 : 0 < j) (hjJ : j < J)
    (hxi : xi ∈ bandPartOn (levelSmallSet P N v₀ v₁ g alpha) J G j) :
    ∃ r ∈ Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1),
      Real.exp (-(alpha (j - 1) * (r : ℝ) /
          ((2 * N (j - 1) : ℕ) : ℝ)))
        < ‖levelCellPoly (P (j - 1)) (N (j - 1)) r g xi‖ := by
  rw [bandPartOn, bandPart, if_pos hjJ] at hxi
  have hprev : xi ∉ levelSmallSet P N v₀ v₁ g alpha (j - 1) := by
    intro h
    exact hxi.2.2 (Set.mem_iUnion₂.mpr
      ⟨j - 1, Finset.mem_range.mpr (by omega), h⟩)
  simp only [levelSmallSet, Set.mem_setOf_eq] at hprev
  push_neg at hprev
  exact hprev

end MoltResearch
