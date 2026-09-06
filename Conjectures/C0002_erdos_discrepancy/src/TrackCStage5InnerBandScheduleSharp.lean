import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5BandEnergyExceptionalReCut
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5ExceptionalSharp
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5InnerBandSchedule

/-!
# Track R VI-9g-2': the sharp exceptional schedule after the recut
-/

namespace MoltResearch

namespace Tao2015

/-- Upward scale transfer for the `1`-bounded functions quantified by
`SliceMeanSquareA2`.  The existing unimodular wrapper has the same proof; this
version uses the nonnegativity of each newly added prime summand directly. -/
theorem nonPretentiousAt_scale_up_of_norm_le_one {g : ℕ → ℂ}
    (hg : ∀ n, ‖g n‖ ≤ 1) {A A' c : ℝ} {x z : ℕ}
    (h : NonPretentiousAt g A x) (hxz : x ≤ z) (hzc : (z : ℝ) ≤ c * x)
    (hA'0 : 0 ≤ A') (hc1 : 1 ≤ c) (hA' : A' * c ≤ A) :
    NonPretentiousAt g A' z := by
  intro q chi t hq ht
  have hAA' : A' ≤ A := le_trans (le_mul_of_one_le_right hA'0 hc1) hA'
  have hq' : (q : ℝ) ≤ A := le_trans hq hAA'
  have ht' : |t| ≤ A * x := by
    calc
      |t| ≤ A' * z := ht
      _ ≤ A' * (c * x) := mul_le_mul_of_nonneg_left hzc hA'0
      _ = (A' * c) * x := by ring
      _ ≤ A * x := mul_le_mul_of_nonneg_right hA' (Nat.cast_nonneg x)
  calc
    A' ≤ A := hAA'
    _ ≤ pretentiousDistSq g (charTwist q chi t) x := h q chi t hq' ht'
    _ ≤ pretentiousDistSq g (charTwist q chi t) z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rw [Nat.mem_primesBelow] at hp ⊢
        exact ⟨lt_of_lt_of_le hp.1 hxz, hp.2⟩
      · intro p _ _
        apply div_nonneg
        · have hre :
              (g p * (starRingEnd ℂ) (charTwist q chi t p)).re ≤ 1 := by
            calc
              (g p * (starRingEnd ℂ) (charTwist q chi t p)).re
                  ≤ ‖g p * (starRingEnd ℂ) (charTwist q chi t p)‖ :=
                    Complex.re_le_norm _
              _ = ‖g p‖ * ‖charTwist q chi t p‖ := by
                    rw [norm_mul, RCLike.norm_conj]
              _ ≤ 1 * 1 := mul_le_mul (hg p) (charTwist_norm_le_one q chi t p)
                    (norm_nonneg _) zero_le_one
              _ = 1 := one_mul 1
          linarith
        · exact Nat.cast_nonneg p

/-- The zero-extended cell coefficient has squared harmonic mass at most the
elementary reciprocal-square tail beginning at `A/q + 1`. -/
theorem sum_norm_cellBlockCoeff_sq_div_sq_le_two_div
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A B : ℕ) (P : Finset ℕ) (rest : List (Finset ℕ)) (q : ℕ)
    (hAq : 1 ≤ A / q) :
    (∑ n ∈ Finset.Icc 1 (B / q),
        ‖cellBlockCoeff g A B P rest q n‖ ^ 2 / (n : ℝ) ^ 2)
      ≤ 2 / (((A / q + 1 : ℕ) : ℝ)) := by
  classical
  have hsub : Finset.Ioc (A / q) (B / q) ⊆ Finset.Icc 1 (B / q) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_Icc]
    exact ⟨by omega, hn.2⟩
  have hsupp :
      (∑ n ∈ Finset.Icc 1 (B / q),
          ‖cellBlockCoeff g A B P rest q n‖ ^ 2 / (n : ℝ) ^ 2) =
        ∑ n ∈ Finset.Ioc (A / q) (B / q),
          ‖cellBlockCoeff g A B P rest q n‖ ^ 2 / (n : ℝ) ^ 2 := by
    rw [← Finset.sum_subset hsub]
    intro n _ hn
    simp [cellBlockCoeff, hn]
  rw [hsupp]
  calc
    (∑ n ∈ Finset.Ioc (A / q) (B / q),
        ‖cellBlockCoeff g A B P rest q n‖ ^ 2 / (n : ℝ) ^ 2)
        ≤ ∑ n ∈ Finset.Ioc (A / q) (B / q), (1 : ℝ) / (n : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun n hn => ?_
          exact div_le_div_of_nonneg_right
            (pow_le_one₀ (norm_nonneg _) (norm_cellBlockCoeff_le_one g hg A B P rest q n))
            (sq_nonneg _)
    _ = ∑ n ∈ Finset.Ico (A / q + 1) (B / q + 1), (1 : ℝ) / (n : ℝ) ^ 2 := by
          congr 1
          ext n
          simp only [Finset.mem_Ioc, Finset.mem_Ico]
          omega
    _ ≤ 2 / (((A / q + 1 : ℕ) : ℝ)) :=
          ExpSums.sum_inv_sq_Ico_le (A / q + 1) (B / q + 1) (by omega)

/-- A cell above `Pc` has prime square-mass at most its cardinality divided by
`Pc^2`. -/
theorem sum_norm_sq_div_prime_sq_le_card_div
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (Y : Finset ℕ) (Pc : ℕ) (hPc : 1 ≤ Pc)
    (hlo : ∀ p ∈ Y, Pc < p) :
    ∑ p ∈ Y, ‖g p‖ ^ 2 / (p : ℝ) ^ 2
      ≤ (Y.card : ℝ) / (Pc : ℝ) ^ 2 := by
  calc
    (∑ p ∈ Y, ‖g p‖ ^ 2 / (p : ℝ) ^ 2)
        ≤ ∑ _p ∈ Y, (1 : ℝ) / (Pc : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hnorm : ‖g p‖ ^ 2 ≤ 1 :=
            pow_le_one₀ (norm_nonneg _) (hg p)
          have hden : (Pc : ℝ) ^ 2 ≤ (p : ℝ) ^ 2 := by
            exact_mod_cast Nat.pow_le_pow_left (Nat.le_of_lt (hlo p hp)) 2
          calc
            ‖g p‖ ^ 2 / (p : ℝ) ^ 2 ≤ 1 / (p : ℝ) ^ 2 :=
              div_le_div_of_nonneg_right hnorm (sq_nonneg _)
            _ ≤ 1 / (Pc : ℝ) ^ 2 := by
              exact one_div_le_one_div_of_le (by positivity) hden
    _ = (Y.card : ℝ) / (Pc : ℝ) ^ 2 := by
          rw [Finset.sum_const, Finset.card_eq_sum_ones, nsmul_eq_mul]
          ring

/-- The last ordinary level's high-moment upper bound for the number of unit
cells meeting the exceptional band part. -/
noncomputable def sharpExceptionalCoverBound
    (P : ℕ → Finset ℕ) (N v0 v1 : ℕ → ℕ) (alpha : ℕ → ℝ)
    (J : ℕ) (Panchor coverEll : ℕ → ℕ) (T : ℝ)
    (coverLam : ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.Ico (v0 (J - 1)) (v1 (J - 1) + 1),
    2 * primeHighMomentCountCost (Panchor r) (coverEll r)
      (eadicCell (P (J - 1)) (2 * N (J - 1)) r) T
      (Real.exp (-(alpha (J - 1) * (r : ℝ) /
        ((2 * N (J - 1) : ℕ) : ℝ)))) (coverLam r)

-- This theorem elaborates the full ordinary-level decomposition before the
-- recut exceptional capstone.
set_option maxHeartbeats 800000 in
/-- The level assembly with the VI-9d fixed-threshold exceptional input.

This is the recut analogue of `band_energy_typicalS_le_of_levels`: the
ordinary level legs are unchanged, while the final exceptional call uses the
covered-cell integer cost and the high-moment prime count. -/
theorem band_energy_typicalS_le_of_levels_recut [HalaszLargeValuesAssumption]
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
    (ellU : ℕ → ℕ) (hellU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1), 1 ≤ ellU v)
    (Vsplit deltaU lamU : ℕ → ℝ)
    (hVsplit : ∀ v ∈ Finset.Ico v₀u (v₁u + 1), 0 < Vsplit v)
    (hlamU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1), 0 < lamU v)
    (hdeltaU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1), ∀ t : ℝ, |t| ≤ T →
      ‖∑ n ∈ Finset.Icc 1 ((A + Delta) / qu v),
          (cellBlockCoeff g A (A + Delta) Pu ((List.range J).map Pl) (qu v) n /
              (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ deltaU v)
    (kappaU : ℕ → ℝ)
    (hfitUCell : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      2 * ((Vsplit v) ^ 2
            * (64 * ((((A + Delta) / qu v : ℕ) : ℝ)
                + ((cellsMeetingSet (bandCells K₂)
                    (bandPartOn (levelSmallSet Pl Nl v₀l v₁l g alpha) J
                      {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} J)).card : ℝ)
                    * Real.sqrt T)
              * (Real.log (2 * T) + 1)
              * ∑ n ∈ Finset.Icc 1 ((A + Delta) / qu v),
                  ‖cellBlockCoeff g A (A + Delta) Pu ((List.range J).map Pl) (qu v) n‖ ^ 2 /
                    (n : ℝ) ^ 2)
          + (deltaU v) ^ 2
            * ((Cp * (∑ p ∈ eadicCell Pu (2 * Nu) v,
                    ‖g p‖ ^ 2 / (p : ℝ) ^ 2)
                * (PcU v : ℝ) / Real.log (PcU v))
              * (1 + primeHighMomentCountCost (PcU v) (ellU v)
                  (eadicCell Pu (2 * Nu) v) T (Vsplit v) (lamU v)
                * Real.exp (-(Real.log (PcU v) /
                  (Real.log (2 * T)) ^ primeLargeValuesExponent))
                * (Real.log (2 * T)) ^ 2)))
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
  exact band_energy_typicalS_le_of_cellUniform_fit_recut Cp hCp1 hprime
    g hcm hg A Delta H hA hH hDeltaA
    Pu hPu hPAu restU Nu v₀u v₁u hNu hcovU hstableU qu hqcellU hq1U hqminU
    hLAU hLBU w hwm hw0 hwsup K₁ K₂ J Pset hPset c₃ eps hc₃ hlegU
    PcU hPcU hloU hhiU T hT1 hTK₂ ellU hellU Vsplit deltaU lamU
    hVsplit hlamU hdeltaU kappaU hfitUCell hfitU


-- The sharp schedule expands every ordinary schedule leg and both exceptional
-- half-budget inequalities.
set_option maxHeartbeats 800000 in
/-- **VI-9g-2' — the sharp exceptional schedule on the recut capstone.**

The ordinary-level hypotheses and proof blocks are exactly those of
`band_energy_typicalS_le_of_schedule'`.  Put

* `V0 = exceptionalSplitThreshold A`,
* `KcovBound = sharpExceptionalCoverBound Pl Nl v0l v1l
    innerBandScheduleAlpha J PanchorU coverEllU T coverLamU`,
* `harmBound v = 2 / (A / qu v + 1)`, and
* `DeltaU v` above the sharp cell bound.

The two exceptional schedule hypotheses are exactly

`2 * V0^2 * 64 * ((A+Delta)/qu v + KcovBound*sqrt T)
    * (log (2*T)+1) * harmBound v
  <= (kappaU v/2) * bandBudget c3 eps (Delta/A)`

and

`2 * DeltaU v^2 * (Cp * card(cell v)/PcU v^2 * PcU v/log(PcU v))
    * (1 + primeHighMomentCountCost ... T V0 (lamU v)
      * exp(-log(PcU v)/log(2*T)^primeLargeValuesExponent) * log(2*T)^2)
  <= (kappaU v/2) * bandBudget c3 eps (Delta/A)`.

The coefficient harmonic mass, covered-cell cardinality, and prime square-mass
are bounded internally.  Adding the two half-budget inequalities gives the
fixed-threshold fit required by
`band_energy_typicalS_le_of_cellUniform_fit_recut`.  The conclusion retains
the honest Fourier-weight factor `(4H/A)^2`. -/
theorem band_energy_typicalS_le_of_schedule_sharp [HalaszLargeValuesAssumption]
    (Cp : ℝ) (hCp1 : 1 ≤ Cp) (hprime : PrimeLargeValuesBound Cp)
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta H : ℕ) (hA : 0 < A) (hH : 0 < H) (hDeltaA : Delta ≤ A)
    (h3HA : 3 * H ≤ A)
    (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ) (J : ℕ)
    (hPl : ∀ i < J, ∀ p ∈ Pl i, p.Prime)
    (hPu : ∀ p ∈ Pu, p.Prime)
    (hPAl : ∀ i < J, ∀ p ∈ Pl i, p * p ≤ A)
    (hPAu : ∀ p ∈ Pu, p * p ≤ A)
    (hdisj : ∀ i < J, ∀ k < J, i ≠ k → Disjoint (Pl i) (Pl k))
    (hdisjU : ∀ i < J, Disjoint (Pl i) Pu)
    (Nl v₀l v₁l : ℕ → ℕ) (ql : ℕ → ℕ → ℕ)
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
    (hPlo0 : ∀ j < J, 0 < Plo j) (hQhi0 : ∀ j < J, 0 < Qhi j)
    (hPloQhi : ∀ j < J, Plo j ≤ Qhi j)
    (htop : ∀ j < J,
      (v₁l j : ℝ) ≤ 2 * (Nl j : ℝ) * Real.log (Qhi j))
    (hbot : ∀ j < J,
      2 * (Nl j : ℝ) * Real.log (Plo j) - 1 ≤ (v₀l j : ℝ))
    (R : ℕ) (hR : 1 ≤ R) (hB : A + Delta ≤ R * A)
    (K₁ K₂ T : ℝ) (hT1 : 1 ≤ T) (hTK₂ : K₂ + 2 ≤ T)
    (c₃ eps : ℝ) (hc₃ : 0 ≤ c₃)
    (hscheduleT0 : 0 < J →
      (2 * (Nl 0 : ℝ) * (Real.log (Qhi 0) - Real.log (Plo 0)) + 2)
        * (Real.exp Real.pi * Real.log (2 * (R : ℝ))
          * ((2 * T * Real.exp (1 / ((2 * Nl 0 : ℕ) : ℝ)) / (A : ℝ))
            * ((Qhi 0) ^ (1 - 2 * innerBandScheduleAlpha 0)
              * Real.exp ((1 - 2 * innerBandScheduleAlpha 0) /
                ((2 * Nl 0 : ℕ) : ℝ)))
            * (((2 * Nl 0 : ℕ) : ℝ) / (1 - 2 * innerBandScheduleAlpha 0) + 1)))
      ≤ ordinaryLegShare 0 / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hscheduleP0 : 0 < J →
      (2 * (Nl 0 : ℝ) * (Real.log (Qhi 0) - Real.log (Plo 0)) + 2)
        * (Real.exp Real.pi * Real.log (2 * (R : ℝ))
          * (4 * (R : ℝ)
            * ((Plo 0) ^ (-(2 * innerBandScheduleAlpha 0))
              * Real.exp (2 * innerBandScheduleAlpha 0 /
                ((2 * Nl 0 : ℕ) : ℝ)))
            * (((2 * Nl 0 : ℕ) : ℝ) / (2 * innerBandScheduleAlpha 0) + 1)))
      ≤ ordinaryLegShare 0 / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
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
    (hPmom2 : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1), 2 ≤ Pmom j r)
    (hlomom : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      ∀ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r, Pmom j r < p)
    (hhimom : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      ∀ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r, p ≤ 2 * Pmom j r)
    (hell : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1), 1 ≤ ell j r)
    (hscheduleLater : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      (2 * (Nl j : ℝ) * (Real.log (Qhi j) - Real.log (Plo j)) + 2)
        * (((Plo j) ^ (-(2 * innerBandScheduleAlpha j))
              * Real.exp (2 * innerBandScheduleAlpha j / ((2 * Nl j : ℕ) : ℝ))
              * (((2 * Nl j : ℕ) : ℝ) / (2 * innerBandScheduleAlpha j) + 1))
          * ((Real.exp Real.pi
                * (T / (((Pmom j r) ^ (ell j r) * A' j r : ℕ) : ℝ)
                  + 2 * ((2 ^ (ell j r + 1) : ℕ) : ℝ)))
            * laterMomentScheduleBound (ell j r) (Pmom j r)
                ((Qhi (j - 1)) ^ (-(innerBandScheduleAlpha (j - 1)))
                  * Real.exp (-(innerBandScheduleAlpha (j - 1) /
                    ((2 * Nl (j - 1) : ℕ) : ℝ))))))
      ≤ geometricCellShare (ordinaryLegShare j) r
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (Pb Kc bb : ℕ → ℕ) (aa : ℕ → ℕ → ℕ)
    (hPb : ∀ j < J, 1 ≤ Pb j) (hKc : ∀ j < J, 2 ≤ Kc j)
    (hbb : ∀ j < J, 3 ≤ bb j)
    (haa : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1), Pb j ≤ aa j v)
    (hcell : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      eadicCell (Pl j) (2 * Nl j) v ⊆
        (Finset.Ioc (aa j v) (aa j v + Kc j)).filter Nat.Prime)
    (hlevel : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      eadicCell (Pl j) (2 * Nl j) v ⊆
        (Finset.Ioc (Pb j) (bb j)).filter Nat.Prime)
    (hNbb : ∀ j < J, Nl j * bb j ≤ A)
    (hrho : eps ≤ (Delta : ℝ) / (A : ℝ))
    (hscheduleReplacement : ∀ j < J,
      64 * ((Finset.Ico (v₀l j) (v₁l j + 1)).card : ℝ)
          * replacementCost A (Nl j) (bb j) T
          * ((256 * (Kc j : ℝ) / ((Pb j : ℝ) * Real.log (Kc j)))
            * levelPrimeMassBound (bb j))
        ≤ ordinaryLegShare j * c₃ * eps ^ 3)
    (hscheduleCollision : ∀ j < J,
      8 * (levelPrimeMassBound (bb j)
        * ((levelPrimeMassBound (bb j) / (Pb j : ℝ) ^ 2)
          * (Real.exp Real.pi * (2 * T * (bb j : ℝ) ^ 2 / (A : ℝ) + 8)
            * Real.log (2 * (R : ℝ)))))
        ≤ ordinaryLegShare j * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (Nu v₀u v₁u : ℕ) (hNu : 0 < Nu)
    (hcovU : (Finset.Ico v₀u (v₁u + 1)).biUnion (eadicCell Pu (2 * Nu)) = Pu)
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
    (hJpos : 0 < J)
    (PanchorU coverEllU : ℕ → ℕ) (coverLamU : ℕ → ℝ)
    (hPanchorU : ∀ r ∈ Finset.Ico (v₀l (J - 1)) (v₁l (J - 1) + 1),
      1 ≤ PanchorU r)
    (hloCoverU : ∀ r ∈ Finset.Ico (v₀l (J - 1)) (v₁l (J - 1) + 1),
      ∀ p ∈ eadicCell (Pl (J - 1)) (2 * Nl (J - 1)) r, PanchorU r < p)
    (hhiCoverU : ∀ r ∈ Finset.Ico (v₀l (J - 1)) (v₁l (J - 1) + 1),
      ∀ p ∈ eadicCell (Pl (J - 1)) (2 * Nl (J - 1)) r, p ≤ 2 * PanchorU r)
    (hellCoverU : ∀ r ∈ Finset.Ico (v₀l (J - 1)) (v₁l (J - 1) + 1),
      1 ≤ coverEllU r)
    (hlamCoverU : ∀ r ∈ Finset.Ico (v₀l (J - 1)) (v₁l (J - 1) + 1),
      0 < coverLamU r)
    (ellU : ℕ → ℕ) (hellU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1), 1 ≤ ellU v)
    (lamU : ℕ → ℝ) (hlamU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1), 0 < lamU v)
    (x0 : ℕ) (hx0 : cellHalaszThreshold ≤ x0)
    (D delta₀ A₀ : ℝ) (hD : 1 ≤ D)
    (hdelta₀ : 0 < delta₀) (hdelta₁ : delta₀ ≤ 1) (hA₀ : 3 ≤ A₀)
    (hNPtop : NonPretentiousAt g A₀ (2 * A + 1))
    (hrangeSharp :
      2 * Real.pi * T
          + 2 * Real.pi * (((halaszM (3 * (2 * A + 1)) : ℕ) : ℝ) + 1)
        ≤ (A₀ / 3) * ((3 * (2 * A + 1) : ℕ) : ℝ))
    (hstrengthSharp :
      2 * D ≤ A₀ / 3 - 2 * (Real.log (Real.log ((3 * (2 * A + 1) : ℕ) : ℝ))
        - Real.log (Real.log (x0 : ℝ)) + 12))
    (hAqU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1), 1 ≤ A / qu v)
    (DeltaU : ℕ → ℝ) (hDeltaU0 : ∀ v ∈ Finset.Ico v₀u (v₁u + 1), 0 ≤ DeltaU v)
    (hDeltaU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      cellHalaszSharpBound x0 D delta₀ (A / qu v) ((A + Delta) / qu v)
          Pu ((List.range J).map Pl) ≤ DeltaU v)
    (kappaU : ℕ → ℝ)
    (hfitInt : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      2 * exceptionalSplitThreshold A ^ 2
          * (64 * ((((A + Delta) / qu v : ℕ) : ℝ)
              + sharpExceptionalCoverBound Pl Nl v₀l v₁l innerBandScheduleAlpha J
                  PanchorU coverEllU T coverLamU * Real.sqrt T)
            * (Real.log (2 * T) + 1)
            * (2 / (((A / qu v + 1 : ℕ) : ℝ))))
        ≤ kappaU v / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hfitPri : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      2 * (DeltaU v) ^ 2
          * ((Cp * ((eadicCell Pu (2 * Nu) v).card : ℝ) / (PcU v : ℝ) ^ 2
                * (PcU v : ℝ) / Real.log (PcU v))
            * (1 + primeHighMomentCountCost (PcU v) (ellU v)
                (eadicCell Pu (2 * Nu) v) T (exceptionalSplitThreshold A) (lamU v)
              * Real.exp (-(Real.log (PcU v) /
                (Real.log (2 * T)) ^ primeLargeValuesExponent))
              * (Real.log (2 * T)) ^ 2))
        ≤ kappaU v / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (PminU QmaxU : ℕ) (hPminU : 1 ≤ PminU) (hQmaxU : 3 ≤ QmaxU)
    (hPulo : ∀ p ∈ Pu, PminU < p) (hPuhi : ∀ p ∈ Pu, p ≤ QmaxU)
    (hNuQ : Nu * QmaxU ≤ A)
    (kappaReplacementU kappaCollisionU : ℝ)
    (hkappaReplacementU : 0 ≤ kappaReplacementU * c₃)
    (hscheduleReplacementU :
      64 * ((Finset.Ico v₀u (v₁u + 1)).card : ℝ)
          * replacementCost A Nu QmaxU T
          * ((256 * (QmaxU : ℝ) / ((PminU : ℝ) * Real.log QmaxU))
            * levelPrimeMassBound QmaxU)
        ≤ kappaReplacementU * c₃ * eps ^ 3)
    (hscheduleCollisionU :
      8 * (levelPrimeMassBound QmaxU
        * ((levelPrimeMassBound QmaxU / (PminU : ℝ) ^ 2)
          * (Real.exp Real.pi * (2 * T * (QmaxU : ℝ) ^ 2 / (A : ℝ) + 8)
            * Real.log (2 * (R : ℝ)))))
        ≤ kappaCollisionU * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hscheduleUShare :
      2 * ((Finset.Ico v₀u (v₁u + 1)).card : ℝ)
          * (∑ v ∈ Finset.Ico v₀u (v₁u + 1), kappaU v)
          + 2 * kappaReplacementU + 2 * kappaCollisionU
        ≤ 1 / 2 ^ (J + 1)) :
    (∫ xi in {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂},
        ‖∑ m ∈ typicalS A (A + Delta) (innerBandLevels Pl Pu J),
            (g m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2 * w xi)
      ≤ (4 * (H : ℝ) / (A : ℝ)) ^ 2
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
  have hT0 : 0 ≤ T := zero_le_one.trans hT1
  have hT : 0 < T := zero_lt_one.trans_le hT1
  have hrho0 : 0 ≤ (Delta : ℝ) / (A : ℝ) := by positivity
  have hbudget0 := bandBudget_nonneg c₃ eps ((Delta : ℝ) / (A : ℝ)) hc₃ hrho0
  have hscale0 : 0 ≤ (4 * (H : ℝ) / (A : ℝ)) ^ 2 := sq_nonneg _
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
    simp_rw [hsum]
    simpa using mul_nonneg hscale0 hbudget0
  have h1 : g 1 = 1 := by
    have hmul := hcm 1 1 one_ne_zero one_ne_zero
    have hcancel : g 1 * g 1 = g 1 * 1 := by
      simpa using hmul.symm
    exact mul_left_cancel₀ hzero hcancel
  have halpha : ∀ j < J, 0 < innerBandScheduleAlpha j := by
    intro j hj
    unfold innerBandScheduleAlpha
    exact scheduleAlpha_pos (j + 1) (by omega)
  have halpha2 : 0 < J → 2 * innerBandScheduleAlpha 0 < 1 := by
    intro _
    unfold innerBandScheduleAlpha
    exact scheduleAlpha_two_lt_one 1 (by omega)
  have hC0 : 0 ≤ Real.log (2 * (R : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * R))
  have hC : 0 < J → ∀ v ∈ Finset.Ico (v₀l 0) (v₁l 0 + 1),
      ∑ m ∈ Finset.Ioc (A / ql 0 v) ((A + Delta) / ql 0 v),
        (1 : ℝ) / (m : ℝ) ≤ Real.log (2 * (R : ℝ)) := by
    intro hJ v hv
    exact quotient_harmonic_le_log_two_mul A (A + Delta) (ql 0 v) R
      (hq1l 0 hJ v) (by have := hqAl 0 hJ v; omega) hR hB
  have hfit0 : 0 < J →
      (((Finset.Ico (v₀l 0) (v₁l 0 + 1)).card : ℝ)
        * (Real.exp Real.pi * Real.log (2 * (R : ℝ))
          * ((2 * T * Real.exp (1 / ((2 * Nl 0 : ℕ) : ℝ)) / (A : ℝ))
            * ((Qhi 0) ^ (1 - 2 * innerBandScheduleAlpha 0)
              * Real.exp ((1 - 2 * innerBandScheduleAlpha 0) / ((2 * Nl 0 : ℕ) : ℝ)))
            * (((2 * Nl 0 : ℕ) : ℝ) / (1 - 2 * innerBandScheduleAlpha 0) + 1)))
          ≤ ordinaryLegShare 0 / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))) ∧
       (((Finset.Ico (v₀l 0) (v₁l 0 + 1)).card : ℝ)
        * (Real.exp Real.pi * Real.log (2 * (R : ℝ))
          * (4 * (R : ℝ)
            * ((Plo 0) ^ (-(2 * innerBandScheduleAlpha 0))
              * Real.exp (2 * innerBandScheduleAlpha 0 / ((2 * Nl 0 : ℕ) : ℝ)))
            * (((2 * Nl 0 : ℕ) : ℝ) / (2 * innerBandScheduleAlpha 0) + 1)))
          ≤ ordinaryLegShare 0 / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))) := by
    intro hJ
    exact levelOne_fit_pair_of_schedule (Nl 0) R T A (Plo 0) (Qhi 0)
      (innerBandScheduleAlpha 0) c₃ eps ((Delta : ℝ) / (A : ℝ))
      (ordinaryLegShare 0) (hNl 0 hJ) hR hT0 (by exact_mod_cast hA)
      (halpha 0 hJ) (halpha2 hJ) (hPlo0 0 hJ) (hPloQhi 0 hJ)
      (v₀l 0) (v₁l 0) (htop 0 hJ) (hbot 0 hJ)
      (hscheduleT0 hJ) (hscheduleP0 hJ)
  have hfitLater : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      (2 * (Nl j : ℝ) * (Real.log (Qhi j) - Real.log (Plo j)) + 2)
        * (((Plo j) ^ (-(2 * innerBandScheduleAlpha j))
              * Real.exp (2 * innerBandScheduleAlpha j / ((2 * Nl j : ℕ) : ℝ))
              * (((2 * Nl j : ℕ) : ℝ) / (2 * innerBandScheduleAlpha j) + 1))
            * ((Real.exp Real.pi
                  * (T / (((Pmom j r) ^ (ell j r) * A' j r : ℕ) : ℝ)
                    + 2 * ((2 ^ (ell j r + 1) : ℕ) : ℝ)))
              * (((Nat.factorial (ell j r) : ℝ) ^ 2
                * (((2 ^ (ell j r + 1) : ℕ) : ℝ) * ((ell j r : ℝ) + 1)
                  * (∑ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r,
                      (1 : ℝ) / (p : ℝ)) ^ (ell j r)))
                / ((Qhi (j - 1)) ^ (-(innerBandScheduleAlpha (j - 1)))
                    * Real.exp (-(innerBandScheduleAlpha (j - 1) /
                      ((2 * Nl (j - 1) : ℕ) : ℝ)))) ^ (2 * ell j r))))
      ≤ geometricCellShare (ordinaryLegShare j) r
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    intro j hj0 hjJ r hr
    have hjprev : j - 1 < J := by omega
    apply laterLevel_fit_of_schedule (Nl j) (Nl (j - 1)) (v₀l j) (v₁l j)
      (ell j r) (Pmom j r) (A' j r)
      (eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r)
      (Plo j) (Qhi j) (innerBandScheduleAlpha j) (Qhi (j - 1))
      (innerBandScheduleAlpha (j - 1)) T c₃ eps
      ((Delta : ℝ) / (A : ℝ)) (geometricCellShare (ordinaryLegShare j) r)
      (hNl j hjJ) (hNl (j - 1) hjprev) (halpha j hjJ)
      (halpha (j - 1) hjprev).le (hPlo0 j hjJ) (hPloQhi j hjJ)
      (hQhi0 (j - 1) hjprev) (hPmom2 j hj0 hjJ r hr) hT0
    · intro p hp
      exact hPl (j - 1) hjprev p (mem_eadicCell.mp hp).1
    · exact hlomom j hj0 hjJ r hr
    · exact hhimom j hj0 hjJ r hr
    · exact hscheduleLater j hj0 hjJ r hr
  have hlevelSub : ∀ j < J,
      Pl j ⊆ (Finset.Ioc (Pb j) (bb j)).filter Nat.Prime := by
    intro j hj
    exact level_subset_primeInterval (Pl j) (Nl j) (v₀l j) (v₁l j)
      (Pb j) (bb j) (hcovl j hj) (hlevel j hj)
  have hcosts : ∀ j < J,
      (∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
        ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
          Real.exp Real.pi * (T / ((A / p : ℕ) : ℝ) + 4)
              * (((A / (Nl j * p) + 1 : ℕ) : ℝ) / ((A / p : ℕ) : ℝ))
            ≤ replacementCost A (Nl j) (bb j) T) ∧
      (∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
        ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
          Real.exp Real.pi * (T / (((A + Delta) / p : ℕ) : ℝ) + 4)
              * (((((A + Delta) / (Nl j * p)) + 1 : ℕ) : ℝ) /
                (((A + Delta) / p : ℕ) : ℝ))
            ≤ replacementCost A (Nl j) (bb j) T) := by
    intro j hj
    exact eadic_replacement_costs_of_schedule (Pl j) (Nl j) (v₀l j) (v₁l j)
      A (A + Delta) (bb j) T (hNl j hj) hA (Nat.le_add_right A Delta) hT0
      (hPl j hj) (hPAl j hj)
      (fun p hp => (Finset.mem_Ioc.mp
        (Finset.mem_filter.mp (hlevelSub j hj hp)).1).2) (hNbb j hj)
  have hcollisionFit : ∀ j < J,
      8 * collisionEnergyBound A (A + Delta) (Pl j)
          (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j) T
        ≤ ordinaryLegShare j * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    intro j hj
    apply collision_fit_of_schedule A (A + Delta) R (Pl j)
      (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j) T
      (Pb j : ℝ) (bb j : ℝ) (levelPrimeMassBound (bb j)) c₃ eps
      ((Delta : ℝ) / (A : ℝ)) (ordinaryLegShare j) hA hR hB hT0
      (by exact_mod_cast hPb j hj) (by positivity) (hPl j hj) (hPAl j hj)
    · intro p hp
      exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hlevelSub j hj hp)).1).1.le
    · intro p hp
      exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hlevelSub j hj hp)).1).2
    · exact level_primeMass_le (Pl j) (Nl j) (v₀l j) (v₁l j)
        (Pb j) (bb j) (hbb j hj) (hcovl j hj) (hlevel j hj)
    · exact hscheduleCollision j hj
  let restU := (List.range J).map Pl
  let deltaU : ℕ → ℝ := fun v =>
    cellHalaszSharpBound x0 D delta₀ (A / qu v) ((A + Delta) / qu v) Pu restU
  let Vsplit : ℕ → ℝ := fun _ => exceptionalSplitThreshold A
  have hrestPrime : ∀ Q ∈ restU, ∀ p ∈ Q, p.Prime := by
    intro Q hQ p hp
    dsimp [restU] at hQ
    rw [List.mem_map] at hQ
    obtain ⟨j, hj, rfl⟩ := hQ
    exact hPl j (List.mem_range.mp hj) p hp
  have hVsplit : ∀ v ∈ Finset.Ico v₀u (v₁u + 1), 0 < Vsplit v := by
    intro v hv
    dsimp [Vsplit]
    apply exceptionalSplitThreshold_pos
    omega
  have hNPsharp : NonPretentiousAt g (A₀ / 3) (3 * (2 * A + 1)) := by
    apply nonPretentiousAt_scale_up_of_norm_le_one (c := 3) hg hNPtop
    · omega
    · norm_num [Nat.cast_mul, Nat.cast_add]
    · positivity
    · norm_num
    · ring_nf
      exact le_rfl
  have hdeltaU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1), ∀ t : ℝ, |t| ≤ T →
      ‖∑ n ∈ Finset.Icc 1 ((A + Delta) / qu v),
          (cellBlockCoeff g A (A + Delta) Pu restU (qu v) n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ deltaU v := by
    intro v hv t ht
    dsimp [deltaU]
    apply norm_cellBlock_poly_le_cellHalaszSharpBound_of_top g hcm hg h1
      A Delta (qu v) Pu hPu restU hrestPrime x0 hx0 D hD delta₀ hdelta₀ hdelta₁
      (A₀ / 3) (3 * (2 * A + 1)) hNPsharp (by linarith [hA₀])
    · have hq : (A + Delta) / qu v ≤ A + Delta := Nat.div_le_self _ _
      omega
    · exact hrangeSharp
    · exact hstrengthSharp
    · exact ht
  have hdeltaU0 : ∀ v ∈ Finset.Ico v₀u (v₁u + 1), 0 ≤ deltaU v := by
    intro v hv
    exact (norm_nonneg _).trans (hdeltaU v hv 0 (by simpa using hT0))
  have hKcov :
      ((cellsMeetingSet (bandCells K₂)
          (bandPartOn (levelSmallSet Pl Nl v₀l v₁l g innerBandScheduleAlpha) J
            {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} J)).card : ℝ)
        ≤ sharpExceptionalCoverBound Pl Nl v₀l v₁l innerBandScheduleAlpha J
            PanchorU coverEllU T coverLamU := by
    simpa [sharpExceptionalCoverBound] using
      (card_cellsMeeting_exceptional_le_highMomentCost Pl Nl v₀l v₁l g hg
        innerBandScheduleAlpha J hJpos
        {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} (bandCells K₂)
        PanchorU coverEllU coverLamU
        (hPl (J - 1) (by omega)) hPanchorU hloCoverU hhiCoverU hellCoverU
        hlamCoverU T hT0 (fun k hk => bandCells_mem_Icc K₂ T hTK₂ k hk))
  have hfitUCell : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      2 * ((Vsplit v) ^ 2
            * (64 * ((((A + Delta) / qu v : ℕ) : ℝ)
                + ((cellsMeetingSet (bandCells K₂)
                    (bandPartOn (levelSmallSet Pl Nl v₀l v₁l g innerBandScheduleAlpha) J
                      {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} J)).card : ℝ)
                    * Real.sqrt T)
              * (Real.log (2 * T) + 1)
              * ∑ n ∈ Finset.Icc 1 ((A + Delta) / qu v),
                  ‖cellBlockCoeff g A (A + Delta) Pu restU (qu v) n‖ ^ 2 /
                    (n : ℝ) ^ 2)
          + (deltaU v) ^ 2
            * ((Cp * (∑ p ∈ eadicCell Pu (2 * Nu) v,
                    ‖g p‖ ^ 2 / (p : ℝ) ^ 2)
                * (PcU v : ℝ) / Real.log (PcU v))
              * (1 + primeHighMomentCountCost (PcU v) (ellU v)
                  (eadicCell Pu (2 * Nu) v) T (Vsplit v) (lamU v)
                * Real.exp (-(Real.log (PcU v) /
                  (Real.log (2 * T)) ^ primeLargeValuesExponent))
                * (Real.log (2 * T)) ^ 2)))
        ≤ kappaU v * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    intro v hv
    have hHarm := sum_norm_cellBlockCoeff_sq_div_sq_le_two_div g hg A (A + Delta)
      Pu restU (qu v) (hAqU v hv)
    have hAint :
        64 * ((((A + Delta) / qu v : ℕ) : ℝ)
              + ((cellsMeetingSet (bandCells K₂)
                  (bandPartOn (levelSmallSet Pl Nl v₀l v₁l g innerBandScheduleAlpha) J
                    {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} J)).card : ℝ)
                  * Real.sqrt T)
            * (Real.log (2 * T) + 1)
            * ∑ n ∈ Finset.Icc 1 ((A + Delta) / qu v),
                ‖cellBlockCoeff g A (A + Delta) Pu restU (qu v) n‖ ^ 2 /
                  (n : ℝ) ^ 2
          ≤ 64 * ((((A + Delta) / qu v : ℕ) : ℝ)
              + sharpExceptionalCoverBound Pl Nl v₀l v₁l innerBandScheduleAlpha J
                  PanchorU coverEllU T coverLamU * Real.sqrt T)
            * (Real.log (2 * T) + 1)
            * (2 / (((A / qu v + 1 : ℕ) : ℝ))) := by
      have hlog : 0 ≤ Real.log (2 * T) + 1 := by
        have : 1 ≤ 2 * T := by linarith
        linarith [Real.log_nonneg this]
      have hsum : 0 ≤ ∑ n ∈ Finset.Icc 1 ((A + Delta) / qu v),
          ‖cellBlockCoeff g A (A + Delta) Pu restU (qu v) n‖ ^ 2 /
            (n : ℝ) ^ 2 := Finset.sum_nonneg fun n _ => by positivity
      calc
        64 * ((((A + Delta) / qu v : ℕ) : ℝ)
                + ((cellsMeetingSet (bandCells K₂)
                    (bandPartOn (levelSmallSet Pl Nl v₀l v₁l g innerBandScheduleAlpha) J
                      {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} J)).card : ℝ)
                    * Real.sqrt T)
              * (Real.log (2 * T) + 1) * _
            ≤ 64 * ((((A + Delta) / qu v : ℕ) : ℝ)
                + sharpExceptionalCoverBound Pl Nl v₀l v₁l innerBandScheduleAlpha J
                    PanchorU coverEllU T coverLamU * Real.sqrt T)
              * (Real.log (2 * T) + 1) * _ := by gcongr
        _ ≤ 64 * ((((A + Delta) / qu v : ℕ) : ℝ)
                + sharpExceptionalCoverBound Pl Nl v₀l v₁l innerBandScheduleAlpha J
                    PanchorU coverEllU T coverLamU * Real.sqrt T)
              * (Real.log (2 * T) + 1)
              * (2 / (((A / qu v + 1 : ℕ) : ℝ))) := by
            gcongr
            have hcover0 : 0 ≤ sharpExceptionalCoverBound Pl Nl v₀l v₁l
                innerBandScheduleAlpha J PanchorU coverEllU T coverLamU :=
              le_trans (Nat.cast_nonneg _) hKcov
            positivity
    have hIntActual :
        2 * (Vsplit v) ^ 2
            * (64 * ((((A + Delta) / qu v : ℕ) : ℝ)
                + ((cellsMeetingSet (bandCells K₂)
                    (bandPartOn (levelSmallSet Pl Nl v₀l v₁l g innerBandScheduleAlpha) J
                      {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} J)).card : ℝ)
                    * Real.sqrt T)
              * (Real.log (2 * T) + 1)
              * ∑ n ∈ Finset.Icc 1 ((A + Delta) / qu v),
                  ‖cellBlockCoeff g A (A + Delta) Pu restU (qu v) n‖ ^ 2 /
                    (n : ℝ) ^ 2)
          ≤ kappaU v / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
      refine le_trans ?_ (hfitInt v hv)
      exact mul_le_mul_of_nonneg_left hAint (by positivity)
    have hprimeMass := sum_norm_sq_div_prime_sq_le_card_div g hg
      (eadicCell Pu (2 * Nu) v) (PcU v)
      (le_trans (by norm_num) (hPcU v hv)) (hloU v hv)
    let Gamma : ℝ := primeHighMomentCountCost (PcU v) (ellU v)
        (eadicCell Pu (2 * Nu) v) T (Vsplit v) (lamU v)
      * Real.exp (-(Real.log (PcU v) /
        (Real.log (2 * T)) ^ primeLargeValuesExponent))
      * (Real.log (2 * T)) ^ 2
    have hGamma0 : 0 ≤ Gamma := by
      dsimp [Gamma]
      have hsum0 : 0 ≤ ∑ p ∈ eadicCell Pu (2 * Nu) v, (1 : ℝ) / (p : ℝ) := by
        refine Finset.sum_nonneg fun p hp => ?_
        have hpprime := hPu p (mem_eadicCell.mp hp).1
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
        positivity
      have hcost0 : 0 ≤ primeHighMomentCountCost (PcU v) (ellU v)
          (eadicCell Pu (2 * Nu) v) T (Vsplit v) (lamU v) := by
        unfold primeHighMomentCountCost
        have hPc0 : (0 : ℝ) < PcU v := by
          exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (hPcU v hv))
        have hV0 := hVsplit v hv
        have hlam0 := hlamU v hv
        positivity
      positivity
    have hdeltaSq : (deltaU v) ^ 2 ≤ (DeltaU v) ^ 2 :=
      pow_le_pow_left₀ (hdeltaU0 v hv) (by simpa [deltaU] using hDeltaU v hv) 2
    have hPriActual :
        2 * (deltaU v) ^ 2
            * ((Cp * (∑ p ∈ eadicCell Pu (2 * Nu) v,
                    ‖g p‖ ^ 2 / (p : ℝ) ^ 2)
                * (PcU v : ℝ) / Real.log (PcU v)) * (1 + Gamma))
          ≤ kappaU v / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
      calc
        2 * (deltaU v) ^ 2
              * ((Cp * (∑ p ∈ eadicCell Pu (2 * Nu) v,
                      ‖g p‖ ^ 2 / (p : ℝ) ^ 2)
                  * (PcU v : ℝ) / Real.log (PcU v)) * (1 + Gamma))
            ≤ 2 * (DeltaU v) ^ 2
              * ((Cp * ((eadicCell Pu (2 * Nu) v).card : ℝ) / (PcU v : ℝ) ^ 2
                  * (PcU v : ℝ) / Real.log (PcU v)) * (1 + Gamma)) := by
          have hlogPc : 0 < Real.log (PcU v : ℝ) :=
            Real.log_pos (by
              exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) (hPcU v hv)))
          have h64 :
              Cp * (∑ p ∈ eadicCell Pu (2 * Nu) v,
                  ‖g p‖ ^ 2 / (p : ℝ) ^ 2)
                ≤ Cp * ((eadicCell Pu (2 * Nu) v).card : ℝ) / (PcU v : ℝ) ^ 2 := by
            calc
              Cp * (∑ p ∈ eadicCell Pu (2 * Nu) v,
                    ‖g p‖ ^ 2 / (p : ℝ) ^ 2)
                  ≤ Cp * (((eadicCell Pu (2 * Nu) v).card : ℝ) /
                    (PcU v : ℝ) ^ 2) :=
                      mul_le_mul_of_nonneg_left hprimeMass (by linarith)
              _ = Cp * ((eadicCell Pu (2 * Nu) v).card : ℝ) /
                    (PcU v : ℝ) ^ 2 := by ring
          have hBpri :
              Cp * (∑ p ∈ eadicCell Pu (2 * Nu) v,
                    ‖g p‖ ^ 2 / (p : ℝ) ^ 2)
                  * (PcU v : ℝ) / Real.log (PcU v)
                ≤ Cp * ((eadicCell Pu (2 * Nu) v).card : ℝ) / (PcU v : ℝ) ^ 2
                  * (PcU v : ℝ) / Real.log (PcU v) := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right h64 (Nat.cast_nonneg _)) hlogPc.le
          have hfactor0 : 0 ≤ 1 + Gamma := by linarith
          have hinner := mul_le_mul_of_nonneg_right hBpri hfactor0
          have hinnerActual0 :
              0 ≤ (Cp * (∑ p ∈ eadicCell Pu (2 * Nu) v,
                    ‖g p‖ ^ 2 / (p : ℝ) ^ 2)
                  * (PcU v : ℝ) / Real.log (PcU v)) * (1 + Gamma) := by positivity
          have hprod :
              (deltaU v) ^ 2 *
                  ((Cp * (∑ p ∈ eadicCell Pu (2 * Nu) v,
                        ‖g p‖ ^ 2 / (p : ℝ) ^ 2)
                    * (PcU v : ℝ) / Real.log (PcU v)) * (1 + Gamma))
                ≤ (DeltaU v) ^ 2 *
                  ((Cp * ((eadicCell Pu (2 * Nu) v).card : ℝ) / (PcU v : ℝ) ^ 2
                    * (PcU v : ℝ) / Real.log (PcU v)) * (1 + Gamma)) :=
            mul_le_mul hdeltaSq hinner hinnerActual0 (sq_nonneg _)
          calc
            2 * (deltaU v) ^ 2 * _ = 2 * ((deltaU v) ^ 2 * _) := by ring
            _ ≤ 2 * ((DeltaU v) ^ 2 * _) :=
              mul_le_mul_of_nonneg_left hprod (by norm_num)
            _ = 2 * (DeltaU v) ^ 2 * _ := by ring
        _ ≤ kappaU v / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
          simpa [Gamma] using hfitPri v hv
    calc
      2 * ((Vsplit v) ^ 2 * _ + (deltaU v) ^ 2 * _)
          = 2 * (Vsplit v) ^ 2 * _ + 2 * (deltaU v) ^ 2 * _ := by ring
      _ ≤ kappaU v / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))
          + kappaU v / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) :=
            add_le_add hIntActual hPriActual
      _ = kappaU v * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by ring
  have hPuSub : Pu ⊆ (Finset.Ioc PminU QmaxU).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hPulo p hp, hPuhi p hp⟩, hPu p hp⟩
  have hmassU : ∑ p ∈ Pu, (1 : ℝ) / (p : ℝ) ≤ levelPrimeMassBound QmaxU := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hPuSub
      (fun p _ _ => by positivity)).trans ?_
    exact sum_one_div_prime_Ioc_le_mertens PminU QmaxU hQmaxU
  have hRepU : 2 * cellReplacementEnergyBound Pu Nu v₀u v₁u A (A + Delta) T
      ≤ kappaReplacementU * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    have hraw := eadic_replacement_error_le_budget_of_schedule Pu Nu v₀u v₁u
      A (A + Delta) QmaxU PminU QmaxU QmaxU T c₃ eps
      ((Delta : ℝ) / (A : ℝ)) kappaReplacementU (fun _ => PminU)
      hNu hA (Nat.le_add_right A Delta) hT0 hPu hPAu hPuhi hNuQ
      hPminU (by omega) hQmaxU
      (fun v _ => le_rfl)
      (fun v hv p hp => by
        rw [Finset.mem_filter, Finset.mem_Ioc]
        have hpP := (mem_eadicCell.mp hp).1
        exact ⟨⟨hPulo p hpP, by have := hPuhi p hpP; omega⟩, hPu p hpP⟩)
      (fun v hv p hp => hPuSub (mem_eadicCell.mp hp).1)
      hkappaReplacementU hrho
      hscheduleReplacementU
    simpa [cellReplacementEnergyBound] using hraw
  have hCollU : 8 * collisionEnergyBound A (A + Delta) Pu restU T
      ≤ kappaCollisionU * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    apply collision_fit_of_schedule A (A + Delta) R Pu restU T
      (PminU : ℝ) (QmaxU : ℝ) (levelPrimeMassBound QmaxU)
      c₃ eps ((Delta : ℝ) / (A : ℝ)) kappaCollisionU
      hA hR hB hT0 (by exact_mod_cast hPminU) (by positivity) hPu hPAu
      (fun p hp => by exact_mod_cast (hPulo p hp).le)
      (fun p hp => by exact_mod_cast hPuhi p hp) hmassU hscheduleCollisionU
  have hfitUHonest : 2 * ((Finset.Ico v₀u (v₁u + 1)).card : ℝ)
          * (∑ v ∈ Finset.Ico v₀u (v₁u + 1), kappaU v)
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))
        + 2 * (2 * cellReplacementEnergyBound Pu Nu v₀u v₁u A (A + Delta) T
            + 2 * (4 * collisionEnergyBound A (A + Delta) Pu restU T))
      ≤ (1 / 2 ^ (J + 1)) * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    have hshare := mul_le_mul_of_nonneg_right hscheduleUShare hbudget0
    calc
      2 * ((Finset.Ico v₀u (v₁u + 1)).card : ℝ)
            * (∑ v ∈ Finset.Ico v₀u (v₁u + 1), kappaU v)
            * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))
          + 2 * (2 * cellReplacementEnergyBound Pu Nu v₀u v₁u A (A + Delta) T
              + 2 * (4 * collisionEnergyBound A (A + Delta) Pu restU T))
        ≤ (2 * ((Finset.Ico v₀u (v₁u + 1)).card : ℝ)
              * (∑ v ∈ Finset.Ico v₀u (v₁u + 1), kappaU v)
              + 2 * kappaReplacementU + 2 * kappaCollisionU)
            * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
          nlinarith [hRepU, hCollU]
      _ ≤ (1 / 2 ^ (J + 1))
            * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := hshare
  let Cw : ℝ := (4 * (H : ℝ) / (A : ℝ)) ^ 2
  have hCwpos : 0 < Cw := by
    dsimp [Cw]
    positivity
  have hbudgetScale :
      bandBudget (Cw * c₃) eps ((Delta : ℝ) / (A : ℝ)) =
        Cw * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    unfold bandBudget
    ring
  have hbudgetCancel (x : ℝ) :
      x / Cw * bandBudget (Cw * c₃) eps ((Delta : ℝ) / (A : ℝ)) =
        x * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    rw [hbudgetScale]
    field_simp
  have hbudgetHalfCancel (x : ℝ) :
      x / Cw / 2 * bandBudget (Cw * c₃) eps ((Delta : ℝ) / (A : ℝ)) =
        x / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    rw [hbudgetScale]
    field_simp
  have hc₃Cancel (x : ℝ) : x / Cw * (Cw * c₃) = x * c₃ := by
    field_simp
  have hc₃EpsCancel (x : ℝ) :
      x / Cw * (Cw * c₃) * eps ^ 3 = x * c₃ * eps ^ 3 := by
    field_simp
  have hthreeCancel (x : ℝ) :
      Cw * (2 * (x / Cw) + 2 * (x / Cw) + 2 * (x / Cw)) =
        2 * x + 2 * x + 2 * x := by
    field_simp
  change (∫ xi in {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂},
      ‖∑ m ∈ typicalS A (A + Delta) (innerBandLevels Pl Pu J),
          (g m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2 * w xi)
    ≤ Cw * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))
  rw [← hbudgetScale]
  apply band_energy_typicalS_le_of_levels_recut Cp hCp1 hprime
    (X := fun j => replacementCost A (Nl j) (bb j) T)
    g hcm hg A Delta H hA hH hDeltaA
    Pl Pu J hPl hPu hPAl hPAu hdisj hdisjU Nl v₀l v₁l ql innerBandScheduleAlpha
    hNl hcovl hqcelll hq1l hqAl hqminl hLAl hLBl Plo Qhi halpha halpha2
    hPlo0 hQhi0 hPloQhi htop hbot R hR hB (fun _ => Real.log (2 * (R : ℝ)))
    hC0 hC K₁ K₂ T hT1 hTK₂ (Cw * c₃) eps (mul_nonneg hCwpos.le hc₃)
    (fun j => ordinaryLegShare j / Cw) (fun j => ordinaryLegShare j / Cw)
    (fun j => ordinaryLegShare j / Cw)
    (fun hJ => by rw [hbudgetHalfCancel]; exact (hfit0 hJ).1)
    (fun hJ => by rw [hbudgetHalfCancel]; exact (hfit0 hJ).2)
    A' Delta' Pmom ell hA' hDelta' hSblk hPmom hlomom hhimom hell
    (fun j r => geometricCellShare (ordinaryLegShare j) r / Cw)
    (fun j hj0 hjJ r hr => by
      rw [hbudgetCancel]
      exact hfitLater j hj0 hjJ r hr)
  · intro j hj0 hjJ
    change (∑ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      geometricCellShare (ordinaryLegShare j) r / Cw) ≤ ordinaryLegShare j / Cw
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right
      (sum_geometricCellShare_Ico_le (v₀l (j - 1)) (v₁l (j - 1))
        (ordinaryLegShare j) (by unfold ordinaryLegShare; positivity)) hCwpos.le
  · exact hPb
  · exact hKc
  · exact hbb
  · intro j hj
    unfold replacementCost
    positivity
  · exact fun j hj => (hcosts j hj).1
  · exact fun j hj => (hcosts j hj).2
  · exact haa
  · exact hcell
  · exact hlevel
  · intro j hj
    rw [hc₃Cancel]
    exact mul_nonneg (by unfold ordinaryLegShare; positivity) hc₃
  · exact hrho
  · intro j hj
    rw [hc₃EpsCancel]
    simpa [levelPrimeMassBound] using hscheduleReplacement j hj
  · intro j hj
    rw [hbudgetCancel]
    exact hcollisionFit j hj
  · intro j hj
    calc
      Cw * (2 * (ordinaryLegShare j / Cw) + 2 * (ordinaryLegShare j / Cw)
          + 2 * (ordinaryLegShare j / Cw))
          = 2 * ordinaryLegShare j + 2 * ordinaryLegShare j
              + 2 * ordinaryLegShare j := hthreeCancel _
      _ ≤ (1 : ℝ) / 2 ^ (j + 1) := ordinaryLegShares_fit_honest j
  · exact hNu
  · exact hcovU
  · exact hqcellU
  · exact hq1U
  · exact hqminU
  · exact hLAU
  · exact hLBU
  · exact hwm
  · exact hw0
  · exact hwsup
  · exact hPcU
  · exact hloU
  · exact hhiU
  · exact hellU
  · exact hVsplit
  · exact hlamU
  · simpa [restU] using hdeltaU
  · intro v hv
    rw [hbudgetCancel]
    exact hfitUCell v hv
  · rw [hbudgetScale]
    rw [show (4 * (H : ℝ) / (A : ℝ)) ^ 2 = Cw from rfl]
    convert hfitUHonest using 1 <;> field_simp
    rw [← Finset.sum_div (Finset.Ico v₀u (v₁u + 1)) kappaU Cw]
    dsimp [restU]
    field_simp

end Tao2015

end MoltResearch
