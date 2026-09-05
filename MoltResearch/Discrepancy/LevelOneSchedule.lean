import MoltResearch.Discrepancy.LevelSizes

/-!
# The first inner-band level in schedule form (Track R, A2-III, VI-8a)

This leaf removes the two non-schedule quantities from the level-one fit.  The
harmonic mass of every divided block is at most `log (2R)`; the factor two is
the honest loss from natural-number division.  The number of e-adic cells is
then replaced by `2N log(Q/P) + 2` using `cellCount_le`.
-/

namespace MoltResearch

/-- A divided block of multiplicative length at most `R` has harmonic mass at
most `log (2R)`.  The `2` is precisely the floor-division loss in
`Ioc_div_subset_Ioc_two_mul_ratio`. -/
theorem quotient_harmonic_le_log_two_mul (A B q R : ℕ) (hq : 1 ≤ q)
    (hqA : q ≤ A) (hR : 1 ≤ R) (hB : B ≤ R * A) :
    ∑ m ∈ Finset.Ioc (A / q) (B / q), (1 : ℝ) / (m : ℝ)
      ≤ Real.log (2 * (R : ℝ)) := by
  have ha : 1 ≤ A / q := (Nat.one_le_div_iff (by omega : 0 < q)).mpr hqA
  have hsub := ExpSums.Ioc_div_subset_Ioc_two_mul_ratio A B R q hq hqA hR hB
  have hmono :
      ∑ m ∈ Finset.Ioc (A / q) (B / q), (1 : ℝ) / (m : ℝ)
        ≤ ∑ m ∈ Finset.Ioc (A / q) (2 * R * (A / q)),
            (1 : ℝ) / (m : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => by positivity)
  have htop : A / q ≤ 2 * R * (A / q) := by
    have : 1 ≤ 2 * R := by omega
    exact Nat.le_mul_of_pos_left _ this
  refine hmono.trans ((sum_one_div_Ioc_le ha htop).trans ?_)
  have ha0 : (0 : ℝ) < (A / q : ℕ) := by exact_mod_cast ha
  have hR0 : (0 : ℝ) < 2 * (R : ℝ) := by exact_mod_cast (by omega : 0 < 2 * R)
  have hcast : ((2 * R * (A / q) : ℕ) : ℝ) =
      (2 * (R : ℝ)) * (A / q : ℕ) := by
    push_cast
    ring
  rw [hcast, Real.log_mul (ne_of_gt hR0) (ne_of_gt ha0)]
  simpa [mul_comm]

/-- The two level-one fits after replacing the cell count by its schedule
bound.  Both hypotheses are closed inequalities in `N,R,T,A,P,Q,α` and the
allocated budget; no cell endpoint remains on their left-hand sides. -/
theorem levelOne_fit_pair_of_schedule (N R : ℕ)
    (T A P Q α c₃ eps rho kappa : ℝ)
    (hN : 0 < N) (hR : 1 ≤ R) (hT0 : 0 ≤ T) (hA0 : 0 < A)
    (hα : 0 < α) (hα2 : 2 * α < 1) (hP0 : 0 < P) (hPQ : P ≤ Q)
    (v₀ v₁ : ℕ)
    (htop : (v₁ : ℝ) ≤ 2 * (N : ℝ) * Real.log Q)
    (hbot : 2 * (N : ℝ) * Real.log P - 1 ≤ (v₀ : ℝ))
    (hfitT : (2 * (N : ℝ) * (Real.log Q - Real.log P) + 2)
        * (Real.exp Real.pi * Real.log (2 * (R : ℝ))
          * ((2 * T * Real.exp (1 / ((2 * N : ℕ) : ℝ)) / A)
            * (Q ^ (1 - 2 * α) * Real.exp ((1 - 2 * α) / ((2 * N : ℕ) : ℝ)))
            * (((2 * N : ℕ) : ℝ) / (1 - 2 * α) + 1)))
      ≤ kappa / 2 * bandBudget c₃ eps rho)
    (hfitP : (2 * (N : ℝ) * (Real.log Q - Real.log P) + 2)
        * (Real.exp Real.pi * Real.log (2 * (R : ℝ))
          * (4 * (R : ℝ)
            * (P ^ (-(2 * α)) * Real.exp (2 * α / ((2 * N : ℕ) : ℝ)))
            * (((2 * N : ℕ) : ℝ) / (2 * α) + 1)))
      ≤ kappa / 2 * bandBudget c₃ eps rho) :
    (((Finset.Ico v₀ (v₁ + 1)).card : ℝ)
        * (Real.exp Real.pi * Real.log (2 * (R : ℝ))
          * ((2 * T * Real.exp (1 / ((2 * N : ℕ) : ℝ)) / A)
            * (Q ^ (1 - 2 * α) * Real.exp ((1 - 2 * α) / ((2 * N : ℕ) : ℝ)))
            * (((2 * N : ℕ) : ℝ) / (1 - 2 * α) + 1)))
      ≤ kappa / 2 * bandBudget c₃ eps rho) ∧
    (((Finset.Ico v₀ (v₁ + 1)).card : ℝ)
        * (Real.exp Real.pi * Real.log (2 * (R : ℝ))
          * (4 * (R : ℝ)
            * (P ^ (-(2 * α)) * Real.exp (2 * α / ((2 * N : ℕ) : ℝ)))
            * (((2 * N : ℕ) : ℝ) / (2 * α) + 1)))
      ≤ kappa / 2 * bandBudget c₃ eps rho) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le hP0 hPQ
  have hcount := cellCount_le N v₀ v₁ P Q hP0 hPQ htop hbot
  have hlogR : 0 ≤ Real.log (2 * (R : ℝ)) := by
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * R))
  have hQrpow : 0 ≤ Q ^ (1 - 2 * α) := (Real.rpow_pos_of_pos hQ0 _).le
  have hPrpow : 0 ≤ P ^ (-(2 * α)) := (Real.rpow_pos_of_pos hP0 _).le
  have hfitT0 : 0 ≤ Real.exp Real.pi * Real.log (2 * (R : ℝ))
      * ((2 * T * Real.exp (1 / ((2 * N : ℕ) : ℝ)) / A)
        * (Q ^ (1 - 2 * α) * Real.exp ((1 - 2 * α) / ((2 * N : ℕ) : ℝ)))
        * (((2 * N : ℕ) : ℝ) / (1 - 2 * α) + 1)) := by
    have : 0 < 1 - 2 * α := by linarith
    positivity
  have hfitP0 : 0 ≤ Real.exp Real.pi * Real.log (2 * (R : ℝ))
      * (4 * (R : ℝ)
        * (P ^ (-(2 * α)) * Real.exp (2 * α / ((2 * N : ℕ) : ℝ)))
        * (((2 * N : ℕ) : ℝ) / (2 * α) + 1)) := by
    positivity
  constructor
  · exact (mul_le_mul_of_nonneg_right hcount hfitT0).trans hfitT
  · exact (mul_le_mul_of_nonneg_right hcount hfitP0).trans hfitP

/-- `levelOne_le_budget` with both fit hypotheses discharged by the closed
schedule inequalities of `levelOne_fit_pair_of_schedule`. -/
theorem levelOne_le_budget_of_schedule (N R : ℕ)
    (T A P Q α c₃ eps rho kappa : ℝ)
    (hN : 0 < N) (hR : 1 ≤ R) (hT0 : 0 ≤ T) (hA0 : 0 < A)
    (hα : 0 < α) (hα2 : 2 * α < 1) (hP0 : 0 < P) (hPQ : P ≤ Q)
    (v₀ v₁ : ℕ)
    (htop : (v₁ : ℝ) ≤ 2 * (N : ℝ) * Real.log Q)
    (hbot : 2 * (N : ℝ) * Real.log P - 1 ≤ (v₀ : ℝ))
    (hfitT : (2 * (N : ℝ) * (Real.log Q - Real.log P) + 2)
        * (Real.exp Real.pi * Real.log (2 * (R : ℝ))
          * ((2 * T * Real.exp (1 / ((2 * N : ℕ) : ℝ)) / A)
            * (Q ^ (1 - 2 * α) * Real.exp ((1 - 2 * α) / ((2 * N : ℕ) : ℝ)))
            * (((2 * N : ℕ) : ℝ) / (1 - 2 * α) + 1)))
      ≤ kappa / 2 * bandBudget c₃ eps rho)
    (hfitP : (2 * (N : ℝ) * (Real.log Q - Real.log P) + 2)
        * (Real.exp Real.pi * Real.log (2 * (R : ℝ))
          * (4 * (R : ℝ)
            * (P ^ (-(2 * α)) * Real.exp (2 * α / ((2 * N : ℕ) : ℝ)))
            * (((2 * N : ℕ) : ℝ) / (2 * α) + 1)))
      ≤ kappa / 2 * bandBudget c₃ eps rho) :
    ((Finset.Ico v₀ (v₁ + 1)).card : ℝ)
        * (Real.exp Real.pi * Real.log (2 * (R : ℝ))
          * ((2 * T * Real.exp (1 / ((2 * N : ℕ) : ℝ)) / A)
                * Real.exp ((1 - 2 * α) * ((v₁ : ℝ) + 1) / ((2 * N : ℕ) : ℝ))
                * (((2 * N : ℕ) : ℝ) / (1 - 2 * α) + 1)
              + 4 * (R : ℝ) * Real.exp (-(2 * α * (v₀ : ℝ) / ((2 * N : ℕ) : ℝ)))
                * (((2 * N : ℕ) : ℝ) / (2 * α) + 1)))
      ≤ kappa * bandBudget c₃ eps rho := by
  have hQ0 : 0 < Q := lt_of_lt_of_le hP0 hPQ
  obtain ⟨hfitT', hfitP'⟩ := levelOne_fit_pair_of_schedule N R T A P Q α c₃ eps rho
    kappa hN hR hT0 hA0 hα hα2 hP0 hPQ v₀ v₁ htop hbot hfitT hfitP
  exact levelOne_le_budget N R ((Finset.Ico v₀ (v₁ + 1)).card : ℝ)
    T A (Real.log (2 * (R : ℝ))) P Q α c₃ eps rho kappa hN
    (by positivity) hlog_nonneg hT0 hA0 hα hα2 hP0 hQ0 v₀ v₁ htop hbot hfitT' hfitP'
  where
    hlog_nonneg : 0 ≤ Real.log (2 * (R : ℝ)) := by
      exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * R))

end MoltResearch
