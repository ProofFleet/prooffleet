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

/-- The prime polynomial carried by one e-adic cell of a level. -/
noncomputable def levelCellPoly (P : Finset ℕ) (N v : ℕ) (g : ℕ → ℂ)
    (xi : ℝ) : ℂ :=
  ∑ p ∈ eadicCell P (2 * N) v, (g p / (p : ℂ))
    * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ)

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

open MeasureTheory Finset ExpSums in
/-- **The level-one main term meets its schedule share.**

`band_energy_level_one_le` supplies the closed-form energy of the cell-uniform
main term and `levelOne_le_budget` converts that expression to a band-budget
share.  For the Ramaré quotient coefficient the former's coefficient-mass
hypothesis reduces to the displayed harmonic-mass bound: boundedness of `g`
and `1/(ω+1) ≤ 1` are discharged by `typicalSQuotCoeff_mass_le`.
-/
theorem band_energy_level_one_main_le_budget
    (P : Finset ℕ) (N : ℕ) (hN : 0 < N) (v₀ v₁ : ℕ) (q : ℕ → ℕ)
    (A B R : ℕ) (hR : 1 ≤ R) (hB : B ≤ R * A)
    (hq1 : ∀ v, 1 ≤ q v) (hqA : ∀ v, 2 * q v ≤ A)
    (hqcell : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      q v ∈ eadicCell P (2 * N) v)
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1) (S : Finset ℕ)
    (T : ℝ) (hT : 0 < T)
    (G : Set ℝ) (hGm : MeasurableSet G) (hGT : G ⊆ Set.Ioc (-T) T)
    (alpha : ℝ) (hAlpha : 0 < alpha) (hAlpha2 : 2 * alpha < 1)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∑ m ∈ Finset.Ioc (A / q v) (B / q v), (1 : ℝ) / (m : ℝ) ≤ C)
    (hsmall : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), ∀ xi ∈ G,
      ‖levelCellPoly P N v g xi‖
        ≤ Real.exp (-(alpha * (v : ℝ) / ((2 * N : ℕ) : ℝ))))
    (Plo Qhi c₃ eps rho kappa : ℝ)
    (hPlo0 : 0 < Plo) (hQhi0 : 0 < Qhi)
    (htop : (v₁ : ℝ) ≤ 2 * (N : ℝ) * Real.log Qhi)
    (hbot : 2 * (N : ℝ) * Real.log Plo - 1 ≤ (v₀ : ℝ))
    (hfitT : ((Finset.Ico v₀ (v₁ + 1)).card : ℝ)
        * (Real.exp Real.pi * C
          * ((2 * T * Real.exp (1 / ((2 * N : ℕ) : ℝ)) / (A : ℝ))
            * (Qhi ^ (1 - 2 * alpha)
                * Real.exp ((1 - 2 * alpha) / ((2 * N : ℕ) : ℝ)))
            * (((2 * N : ℕ) : ℝ) / (1 - 2 * alpha) + 1)))
      ≤ kappa / 2 * bandBudget c₃ eps rho)
    (hfitP : ((Finset.Ico v₀ (v₁ + 1)).card : ℝ)
        * (Real.exp Real.pi * C
          * (4 * (R : ℝ)
            * (Plo ^ (-(2 * alpha))
                * Real.exp (2 * alpha / ((2 * N : ℕ) : ℝ)))
            * (((2 * N : ℕ) : ℝ) / (2 * alpha) + 1)))
      ≤ kappa / 2 * bandBudget c₃ eps rho) :
    (∫ xi in G, ‖∑ v ∈ Finset.Ico v₀ (v₁ + 1),
        levelCellPoly P N v g xi
          * (∑ m ∈ Finset.Ioc (A / q v) (B / q v),
              (typicalSQuotCoeff g P S m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))‖ ^ 2)
      ≤ kappa * bandBudget c₃ eps rho := by
  have hraw := band_energy_level_one_le P N hN v₀ v₁ q A B R hR hB hq1 hqA
    hqcell g (typicalSQuotCoeff g P S) T hT G hGm hGT alpha hAlpha hAlpha2 C hC0
    (fun v hv => (typicalSQuotCoeff_mass_le g hg P S _ _).trans (hC v hv))
    (by simpa [levelCellPoly] using hsmall)
  exact hraw.trans (levelOne_le_budget N R
    ((Finset.Ico v₀ (v₁ + 1)).card : ℝ) T A C Plo Qhi alpha c₃ eps rho kappa
    hN (by positivity) hC0 hT.le (by
      have hqa := hqA v₀
      have hq := hq1 v₀
      exact_mod_cast (by omega : 0 < A)) hAlpha hAlpha2 hPlo0 hQhi0 v₀ v₁
    htop hbot hfitT hfitP)

open MeasureTheory Finset ExpSums in
/-- **A later-level main term meets its schedule share after fixing the
previous large cell.**

The three existing layers line up without algebraic slack.  M-3 turns the
previous cell threshold into the uniform lower bound
`Qprev⁻ᵝ·exp(-β/(2Nprev))`; III-4 bounds each current cell after borrowing
`ℓ` copies of that previous polynomial; and M-9 sums the current cells and
converts their e-adic smallness into the level endpoints `Plo,Qhi`.

The previous cell index `r` is fixed in this statement.  On a whole
first-index part it is supplied by `exists_prev_cell_large_of_mem_bandPartOn`
and requires the standard further partition by the first offending cell.
-/
theorem band_energy_later_main_le_budget
    (Pcur Pprev : Finset ℕ) (Ncur Nprev r v₁prev : ℕ)
    (hNcur : 0 < Ncur) (hNprev : 0 < Nprev)
    (v₀ v₁ : ℕ) (Sblk : ℕ → Finset ℕ)
    (A' Delta' : ℕ) (hA' : 1 ≤ A') (hDelta' : Delta' ≤ A')
    (hSblk : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      Sblk v ⊆ Finset.Ioc A' (A' + Delta'))
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1) (Sco : Finset ℕ)
    (Pmom : ℕ) (hPmom : 1 ≤ Pmom)
    (hPprev : ∀ p ∈ Pprev, p.Prime)
    (hlo : ∀ p ∈ eadicCell Pprev (2 * Nprev) r, Pmom < p)
    (hhi : ∀ p ∈ eadicCell Pprev (2 * Nprev) r, p ≤ 2 * Pmom)
    (ell : ℕ) (hell : 1 ≤ ell)
    (T : ℝ) (hT : 0 < T)
    (G : Set ℝ) (hGm : MeasurableSet G) (hGT : G ⊆ Set.Ioc (-T) T)
    (alpha beta Plo Qhi Qprev : ℝ)
    (hAlpha : 0 < alpha) (hBeta : 0 ≤ beta)
    (hPlo0 : 0 < Plo) (hPloQhi : Plo ≤ Qhi) (hQprev0 : 0 < Qprev)
    (hr : r ≤ v₁prev)
    (htopPrev : (v₁prev : ℝ) ≤ 2 * (Nprev : ℝ) * Real.log Qprev)
    (hsmall : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), ∀ xi ∈ G,
      ‖levelCellPoly Pcur Ncur v g xi‖
        ≤ Real.exp (-(alpha * (v : ℝ) / ((2 * Ncur : ℕ) : ℝ))))
    (hlargeCell : ∀ xi ∈ G,
      Real.exp (-(beta * (r : ℝ) / ((2 * Nprev : ℕ) : ℝ)))
        ≤ ‖levelCellPoly Pprev Nprev r g xi‖)
    (htop : (v₁ : ℝ) ≤ 2 * (Ncur : ℝ) * Real.log Qhi)
    (hbot : 2 * (Ncur : ℝ) * Real.log Plo - 1 ≤ (v₀ : ℝ))
    (c₃ eps rho kappa : ℝ)
    (hfit : (2 * (Ncur : ℝ) * (Real.log Qhi - Real.log Plo) + 2)
        * ((Plo ^ (-(2 * alpha))
              * Real.exp (2 * alpha / ((2 * Ncur : ℕ) : ℝ))
              * (((2 * Ncur : ℕ) : ℝ) / (2 * alpha) + 1))
            * ((Real.exp Real.pi
                  * (T / ((Pmom ^ ell * A' : ℕ) : ℝ)
                    + 2 * ((2 ^ (ell + 1) : ℕ) : ℝ)))
              * (((Nat.factorial ell : ℝ) ^ 2
                * (((2 ^ (ell + 1) : ℕ) : ℝ) * ((ell : ℝ) + 1)
                  * (∑ p ∈ eadicCell Pprev (2 * Nprev) r,
                      (1 : ℝ) / (p : ℝ)) ^ ell))
                / (Qprev ^ (-beta)
                    * Real.exp (-(beta / ((2 * Nprev : ℕ) : ℝ)))) ^
                      (2 * ell))))
      ≤ kappa * bandBudget c₃ eps rho) :
    (∫ xi in G, ‖∑ v ∈ Finset.Ico v₀ (v₁ + 1),
        levelCellPoly Pcur Ncur v g xi
          * (∑ m ∈ Sblk v,
              (typicalSQuotCoeff g Pcur Sco m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))‖ ^ 2)
      ≤ kappa * bandBudget c₃ eps rho := by
  let large : ℝ := Qprev ^ (-beta)
    * Real.exp (-(beta / ((2 * Nprev : ℕ) : ℝ)))
  let E : ℝ := Real.exp Real.pi
    * (T / ((Pmom ^ ell * A' : ℕ) : ℝ)
      + 2 * ((2 ^ (ell + 1) : ℕ) : ℝ))
  let M : ℝ := (Nat.factorial ell : ℝ) ^ 2
    * (((2 ^ (ell + 1) : ℕ) : ℝ) * ((ell : ℝ) + 1)
      * (∑ p ∈ eadicCell Pprev (2 * Nprev) r, (1 : ℝ) / (p : ℝ)) ^ ell)
  have hlarge0 : 0 < large := by
    dsimp [large]
    positivity
  have hprime : ∀ p ∈ eadicCell Pprev (2 * Nprev) r, p.Prime :=
    fun p hp => hPprev p (mem_eadicCell.mp hp).1
  have hlarge : ∀ xi ∈ G, large ≤
      ‖∑ p ∈ eadicCell Pprev (2 * Nprev) r, (g p / (p : ℂ))
        * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ)‖ := by
    intro xi hxi
    change large ≤ ‖levelCellPoly Pprev Nprev r g xi‖
    exact (levelLargeness_ge Nprev r v₁prev Qprev beta hNprev hBeta hQprev0 hr
      htopPrev).trans (hlargeCell xi hxi)
  have hraw := setIntegral_norm_sq_level_sum_of_prev_large_le
    (eadicCell Pprev (2 * Nprev) r) hprime Pmom hPmom hlo hhi g hg ell hell
    A' Delta' hA' hDelta' (Finset.Ico v₀ (v₁ + 1)) Sblk hSblk
    (typicalSQuotCoeff g Pcur Sco)
    (norm_typicalSQuotCoeff_le_one g hg Pcur Sco)
    (fun v xi => levelCellPoly Pcur Ncur v g xi)
    (fun v _ => ExpSums.continuous_char_poly (eadicCell Pcur (2 * Ncur) v)
      (fun p => g p / (p : ℂ)) (fun p => Real.log p))
    T hT G hGm hGT
    (fun v => Real.exp (-(alpha * (v : ℝ) / ((2 * Ncur : ℕ) : ℝ))))
    large hlarge0 hsmall hlarge
  have hsched : ((Finset.Ico v₀ (v₁ + 1)).card : ℝ)
      * ∑ v ∈ Finset.Ico v₀ (v₁ + 1),
        (Real.exp (-(alpha * (v : ℝ) / ((2 * Ncur : ℕ) : ℝ)))) ^ 2
          / large ^ (2 * ell) * (E * M)
      ≤ kappa * bandBudget c₃ eps rho := by
    apply levelJ_le_budget_eadic Ncur v₀ v₁ ell Plo Qhi alpha large E M
      c₃ eps rho kappa hNcur hAlpha hPlo0 hPloQhi hlarge0
      (by dsimp [E]; positivity) (by dsimp [M]; positivity) htop hbot
    simpa [large, E, M] using hfit
  exact hraw.trans (by simpa [E, M] using hsched)

open MeasureTheory in
/-- **A decomposed level leg meets its weighted budget share.**

If `F = main + error` on the level part, the main energy costs twice its
declared share and the already square-split error costs its declared share.
Multiplication by the window supremum `Cw` is postponed to this final join, so
the unweighted level estimates keep their native statements.  The single
numerical condition `Cw * (2κ_main + κ_error) ≤ κ` records all bookkeeping.

The `error` slot is intentionally the *combined* replacement and collision
term.  The collar estimate M-10 can price the replacement component, while the
repeated-prime component needs its own collision estimate.
-/
theorem setIntegral_norm_sq_decomp_le_budget
    (F main error : ℝ → ℂ) (hmainc : Continuous main)
    (herrorc : Continuous error) (T : ℝ)
    (G : Set ℝ) (hGm : MeasurableSet G) (hGT : G ⊆ Set.Ioc (-T) T)
    (hdecomp : ∀ xi ∈ G, F xi = main xi + error xi)
    (Cw kappaMain kappaError kappa c₃ eps rho : ℝ)
    (hCw : 0 ≤ Cw) (hc₃ : 0 ≤ c₃) (hrho : 0 ≤ rho)
    (hmain : (∫ xi in G, ‖main xi‖ ^ 2)
      ≤ kappaMain * bandBudget c₃ eps rho)
    (herror : 2 * (∫ xi in G, ‖error xi‖ ^ 2)
      ≤ kappaError * bandBudget c₃ eps rho)
    (hshare : Cw * (2 * kappaMain + kappaError) ≤ kappa) :
    Cw * (∫ xi in G, ‖F xi‖ ^ 2)
      ≤ kappa * bandBudget c₃ eps rho := by
  have hB0 : 0 ≤ bandBudget c₃ eps rho :=
    bandBudget_nonneg c₃ eps rho hc₃ hrho
  have hsplit : (∫ xi in G, ‖F xi‖ ^ 2)
      ≤ 2 * (∫ xi in G, ‖main xi‖ ^ 2)
        + 2 * (∫ xi in G, ‖error xi‖ ^ 2) := by
    calc
      (∫ xi in G, ‖F xi‖ ^ 2) =
          ∫ xi in G, ‖main xi + error xi‖ ^ 2 := by
            apply setIntegral_congr_fun hGm
            intro xi hxi
            exact congrArg (· ^ 2) (congrArg norm (hdecomp xi hxi))
      _ ≤ 2 * (∫ xi in G, ‖main xi‖ ^ 2)
          + 2 * (∫ xi in G, ‖error xi‖ ^ 2) :=
        ExpSums.setIntegral_norm_add_sq_le main error hmainc herrorc T G hGm hGT
  have hparts : 2 * (∫ xi in G, ‖main xi‖ ^ 2)
        + 2 * (∫ xi in G, ‖error xi‖ ^ 2)
      ≤ (2 * kappaMain + kappaError) * bandBudget c₃ eps rho := by
    calc
      2 * (∫ xi in G, ‖main xi‖ ^ 2)
          + 2 * (∫ xi in G, ‖error xi‖ ^ 2)
        ≤ 2 * (kappaMain * bandBudget c₃ eps rho)
            + kappaError * bandBudget c₃ eps rho := by linarith
      _ = (2 * kappaMain + kappaError) * bandBudget c₃ eps rho := by ring
  calc
    Cw * (∫ xi in G, ‖F xi‖ ^ 2)
      ≤ Cw * (2 * (∫ xi in G, ‖main xi‖ ^ 2)
          + 2 * (∫ xi in G, ‖error xi‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hsplit hCw
    _ ≤ Cw * ((2 * kappaMain + kappaError)
          * bandBudget c₃ eps rho) :=
        mul_le_mul_of_nonneg_left hparts hCw
    _ = (Cw * (2 * kappaMain + kappaError))
          * bandBudget c₃ eps rho := by ring
    _ ≤ kappa * bandBudget c₃ eps rho :=
      mul_le_mul_of_nonneg_right hshare hB0

open MeasureTheory in
/-- **The capstone-facing level leg for the typical-set polynomial.**

This is the literal `hleg` shape required by `band_energy_typicalS_le`, at the
geometric share `2⁻⁽ʲ⁺¹⁾`.  A caller supplies a pointwise decomposition of
the typical-set polynomial into the cell/block main term and one combined
error.  The level-one main hypothesis is produced by
`band_energy_level_one_main_le_budget`; for later levels it is produced by
`band_energy_later_main_le_budget` after fixing the previous offending cell.
The error hypothesis is already square-split, matching the conclusion of the
collar and collision estimates.
-/
theorem typicalS_level_leg_le_budget_of_decomposition
    (g : ℕ → ℂ) (A Delta H : ℕ) (levels : List (Finset ℕ))
    (K₁ K₂ T : ℝ) (J j : ℕ) (Pset : ℕ → Set ℝ)
    (hPset : ∀ i, MeasurableSet (Pset i))
    (hpartT : bandPartOn Pset J {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j
      ⊆ Set.Ioc (-T) T)
    (main error : ℝ → ℂ) (hmainc : Continuous main)
    (herrorc : Continuous error)
    (hdecomp : ∀ xi ∈
      bandPartOn Pset J {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
      (∑ m ∈ typicalS A (A + Delta) levels, (g m / (m : ℂ))
          * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
        = main xi + error xi)
    (kappaMain kappaError c₃ eps : ℝ) (hc₃ : 0 ≤ c₃)
    (hmain : (∫ xi in bandPartOn Pset J
        {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j, ‖main xi‖ ^ 2)
      ≤ kappaMain * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (herror : 2 * (∫ xi in bandPartOn Pset J
        {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j, ‖error xi‖ ^ 2)
      ≤ kappaError * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hshare : (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (2 * kappaMain + kappaError) ≤ (1 : ℝ) / 2 ^ (j + 1)) :
    (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (∫ xi in bandPartOn Pset J
            {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
          ‖∑ m ∈ typicalS A (A + Delta) levels, (g m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
      ≤ (1 / 2 ^ (j + 1))
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
  let G : Set ℝ :=
    bandPartOn Pset J {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j
  have hGm : MeasurableSet G :=
    bandPartOn_measurableSet Pset hPset J _ (measurableSet_inner_band K₁ K₂) j
  exact setIntegral_norm_sq_decomp_le_budget
    (fun xi => ∑ m ∈ typicalS A (A + Delta) levels, (g m / (m : ℂ))
      * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
    main error hmainc herrorc T G hGm hpartT hdecomp
    ((4 * (H : ℝ) / (A : ℝ)) ^ 2) kappaMain kappaError
    ((1 : ℝ) / 2 ^ (j + 1)) c₃ eps ((Delta : ℝ) / (A : ℝ))
    (sq_nonneg _) hc₃ (by positivity) hmain herror hshare

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

/-! ## Refining a later level by its first large previous cell -/

/-- The frequencies where one specified e-adic cell polynomial exceeds its
schedule threshold. -/
noncomputable def levelLargeSet (P : Finset ℕ) (N v : ℕ) (g : ℕ → ℂ)
    (beta : ℝ) : Set ℝ :=
  {xi | Real.exp (-(beta * (v : ℝ) / ((2 * N : ℕ) : ℝ)))
    < ‖levelCellPoly P N v g xi‖}

/-- A one-cell large-value set is measurable. -/
theorem levelLargeSet_measurableSet (P : Finset ℕ) (N v : ℕ)
    (g : ℕ → ℂ) (beta : ℝ) :
    MeasurableSet (levelLargeSet P N v g beta) := by
  exact measurableSet_lt measurable_const
    (ExpSums.continuous_char_poly (eadicCell P (2 * N) v)
      (fun p => g p / (p : ℂ)) (fun p => Real.log p)).norm.measurable

/-- The part of level `j` assigned to the least previous cell whose estimate
fails.  The `if` makes indices outside the previous level empty. -/
noncomputable def firstPrevLargePart
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (J : ℕ) (G : Set ℝ) (j r : ℕ) : Set ℝ :=
  if _hr : r ∈ Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1) then
    (bandPartOn (levelSmallSet P N v₀ v₁ g alpha) J G j
        ∩ levelLargeSet (P (j - 1)) (N (j - 1)) r g (alpha (j - 1)))
      \ ⋃ s ∈ (Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1)).filter
          (fun s => s < r),
        levelLargeSet (P (j - 1)) (N (j - 1)) s g (alpha (j - 1))
  else ∅

/-- The least-large-cell refinement is measurable whenever the ambient band
is measurable. -/
theorem firstPrevLargePart_measurableSet
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (J : ℕ) (G : Set ℝ) (hG : MeasurableSet G)
    (j r : ℕ) : MeasurableSet (firstPrevLargePart P N v₀ v₁ g alpha J G j r) := by
  classical
  unfold firstPrevLargePart
  split
  · refine ((bandPartOn_measurableSet _
        (levelSmallSet_measurableSet P N v₀ v₁ g alpha) J G hG j).inter
        (levelLargeSet_measurableSet _ _ _ _ _)).diff ?_
    exact MeasurableSet.biUnion
      ((Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1)).filter
        (fun s => s < r)).countable_toSet
      (fun s _ => levelLargeSet_measurableSet _ _ _ _ _)
  · exact MeasurableSet.empty

/-- Each refined part stays inside its original first-index level. -/
theorem firstPrevLargePart_subset_bandPartOn
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (J : ℕ) (G : Set ℝ) (j r : ℕ) :
    firstPrevLargePart P N v₀ v₁ g alpha J G j r ⊆
      bandPartOn (levelSmallSet P N v₀ v₁ g alpha) J G j := by
  classical
  unfold firstPrevLargePart
  split
  · exact fun _ h => h.1.1
  · exact Set.empty_subset _

/-- On the part indexed by `r`, that fixed previous cell is large. -/
theorem firstPrevLargePart_large
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (J : ℕ) (G : Set ℝ) (j r : ℕ)
    (hr : r ∈ Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1))
    {xi : ℝ} (hxi : xi ∈ firstPrevLargePart P N v₀ v₁ g alpha J G j r) :
    Real.exp (-(alpha (j - 1) * (r : ℝ) /
        ((2 * N (j - 1) : ℕ) : ℝ)))
      < ‖levelCellPoly (P (j - 1)) (N (j - 1)) r g xi‖ := by
  rw [firstPrevLargePart, dif_pos hr] at hxi
  exact hxi.1.2

/-- Distinct least-large-cell parts are disjoint. -/
theorem firstPrevLargePart_pairwiseDisjoint
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (J : ℕ) (G : Set ℝ) (j : ℕ) :
    Set.Pairwise
      (↑(Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1)) : Set ℕ)
      (Function.onFun Disjoint (firstPrevLargePart P N v₀ v₁ g alpha J G j)) := by
  classical
  intro r hr s hs hrs
  have hrF : r ∈ Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1) := by
    simpa using hr
  have hsF : s ∈ Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1) := by
    simpa using hs
  change Disjoint
    (firstPrevLargePart P N v₀ v₁ g alpha J G j r)
    (firstPrevLargePart P N v₀ v₁ g alpha J G j s)
  rw [Set.disjoint_left]
  intro xi hxr hxs
  rcases lt_or_gt_of_ne hrs with hrs' | hsr'
  · rw [firstPrevLargePart, dif_pos hsF] at hxs
    exact hxs.2 (Set.mem_iUnion₂.mpr ⟨r,
      Finset.mem_filter.mpr ⟨hrF, hrs'⟩,
      firstPrevLargePart_large P N v₀ v₁ g alpha J G j r hrF hxr⟩)
  · rw [firstPrevLargePart, dif_pos hrF] at hxr
    exact hxr.2 (Set.mem_iUnion₂.mpr ⟨s,
      Finset.mem_filter.mpr ⟨hsF, hsr'⟩,
      firstPrevLargePart_large P N v₀ v₁ g alpha J G j s hsF hxs⟩)

/-- At every later nonexceptional level, the least-large-cell parts cover the
whole first-index part. -/
theorem firstPrevLargePart_cover
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (J : ℕ) (G : Set ℝ) (j : ℕ)
    (hj0 : 0 < j) (hjJ : j < J) :
    bandPartOn (levelSmallSet P N v₀ v₁ g alpha) J G j ⊆
      ⋃ r ∈ Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1),
        firstPrevLargePart P N v₀ v₁ g alpha J G j r := by
  classical
  intro xi hxi
  obtain ⟨r, hr, hlarge⟩ :=
    exists_prev_cell_large_of_mem_bandPartOn P N v₀ v₁ g alpha J j G xi
      hj0 hjJ hxi
  let W := (Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1)).filter
    (fun s => xi ∈ levelLargeSet (P (j - 1)) (N (j - 1)) s g (alpha (j - 1)))
  have hW : W.Nonempty := by
    refine ⟨r, Finset.mem_filter.mpr ⟨hr, ?_⟩⟩
    exact hlarge
  let r₀ := W.min' hW
  have hr₀W : r₀ ∈ W := Finset.min'_mem W hW
  have hr₀ := (Finset.mem_filter.mp hr₀W).1
  have hr₀large := (Finset.mem_filter.mp hr₀W).2
  refine Set.mem_iUnion₂.mpr ⟨r₀, hr₀, ?_⟩
  rw [firstPrevLargePart, dif_pos hr₀]
  refine ⟨⟨hxi, hr₀large⟩, ?_⟩
  intro hsmaller
  obtain ⟨s, hs, hslarge⟩ := Set.mem_iUnion₂.mp hsmaller
  have hsW : s ∈ W := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1, hslarge⟩
  have hr₀s : r₀ ≤ s := Finset.min'_le W s hsW
  exact (Nat.not_lt_of_ge hr₀s) (Finset.mem_filter.mp hs).2

open MeasureTheory in
/-- **Per-previous-cell bounds assemble to a later-level main bound.**

The least-offending-cell refinement is a measurable disjoint cover, so a
continuous nonnegative energy on the full later first-index part is at most the
sum of its energies on the refined parts.  Consequently per-cell shares
`κ_r` cost only `∑_r κ_r`; no cardinality factor is introduced by this
refinement.
-/
theorem setIntegral_norm_sq_later_le_budget_of_firstPrev
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (J : ℕ) (G : Set ℝ) (hG : MeasurableSet G)
    (j : ℕ) (hj0 : 0 < j) (hjJ : j < J)
    (F : ℝ → ℂ) (hF : Continuous F) (T : ℝ)
    (hpartT : bandPartOn (levelSmallSet P N v₀ v₁ g alpha) J G j
      ⊆ Set.Ioc (-T) T)
    (kappaCell : ℕ → ℝ) (kappa c₃ eps rho : ℝ)
    (hc₃ : 0 ≤ c₃) (hrho : 0 ≤ rho)
    (hcell : ∀ r ∈ Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1),
      (∫ xi in firstPrevLargePart P N v₀ v₁ g alpha J G j r, ‖F xi‖ ^ 2)
        ≤ kappaCell r * bandBudget c₃ eps rho)
    (hshares : ∑ r ∈ Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1),
      kappaCell r ≤ kappa) :
    (∫ xi in bandPartOn (levelSmallSet P N v₀ v₁ g alpha) J G j,
        ‖F xi‖ ^ 2)
      ≤ kappa * bandBudget c₃ eps rho := by
  let I := Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1)
  let part := firstPrevLargePart P N v₀ v₁ g alpha J G j
  have hpartT' : ∀ r ∈ I, part r ⊆ Set.Ioc (-T) T := by
    intro r _
    exact (firstPrevLargePart_subset_bandPartOn P N v₀ v₁ g alpha J G j r).trans
      hpartT
  have hint : ∀ r ∈ I, IntegrableOn (fun xi => ‖F xi‖ ^ 2) (part r) := by
    intro r hr
    exact ((hF.norm.pow 2).integrableOn_Ioc (a := -T) (b := T)).mono_set
      (hpartT' r hr)
  have hcover := firstPrevLargePart_cover P N v₀ v₁ g alpha J G j hj0 hjJ
  have hsplit : (∫ xi in bandPartOn
      (levelSmallSet P N v₀ v₁ g alpha) J G j, ‖F xi‖ ^ 2)
      ≤ ∑ r ∈ I, ∫ xi in part r, ‖F xi‖ ^ 2 := by
    exact ExpSums.setIntegral_le_sum_of_cover (fun xi => ‖F xi‖ ^ 2)
      (fun xi => sq_nonneg ‖F xi‖)
      (bandPartOn (levelSmallSet P N v₀ v₁ g alpha) J G j)
      I part
      (fun r _ => firstPrevLargePart_measurableSet P N v₀ v₁ g alpha J G hG j r)
      (firstPrevLargePart_pairwiseDisjoint P N v₀ v₁ g alpha J G j)
      hcover hint
  have hB0 : 0 ≤ bandBudget c₃ eps rho :=
    bandBudget_nonneg c₃ eps rho hc₃ hrho
  calc
    (∫ xi in bandPartOn (levelSmallSet P N v₀ v₁ g alpha) J G j,
        ‖F xi‖ ^ 2)
      ≤ ∑ r ∈ I, ∫ xi in part r, ‖F xi‖ ^ 2 := hsplit
    _ ≤ ∑ r ∈ I, kappaCell r * bandBudget c₃ eps rho := by
      exact Finset.sum_le_sum fun r hr => hcell r hr
    _ = (∑ r ∈ I, kappaCell r) * bandBudget c₃ eps rho := by
      rw [Finset.sum_mul]
    _ ≤ kappa * bandBudget c₃ eps rho :=
      mul_le_mul_of_nonneg_right hshares hB0

end MoltResearch
