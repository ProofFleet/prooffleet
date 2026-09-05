import MoltResearch.Discrepancy.LevelLegs

/-!
# Cell replacement in schedule form (Track R, A2-III, VI-8c)

The M-10 replacement fit already exposes the corrected cell-count and prime
mass factors.  Its remaining non-schedule hypotheses are the two endpoint
costs.  They follow from one scale condition `N·Q ≤ A`, where `Q` bounds the
level's primes, and have the common envelope

`e^π · (2TQ/A + 4) · (2/N)`.

The condition `N·Q ≤ A` is deliberately explicit.  The assembly's weaker
natural-division inequalities `hLA/hLB` only show that a collar ratio is at
most one; they do not imply the `1/N` saving required by the schedule.
-/

namespace MoltResearch

/-- The common endpoint-cost envelope used by the replacement schedule. -/
noncomputable def replacementCost (A N Q : ℕ) (T : ℝ) : ℝ :=
  Real.exp Real.pi * (2 * T * (Q : ℝ) / (A : ℝ) + 4) * (2 / (N : ℝ))

/-- Both endpoint collar costs fit the common schedule envelope. -/
theorem replacement_endpoint_cost_pair (A B N Q p : ℕ) (T : ℝ)
    (hN : 1 ≤ N) (hA : 0 < A) (hAB : A ≤ B) (hT : 0 ≤ T)
    (hp : p.Prime) (hppA : p * p ≤ A) (hpQ : p ≤ Q)
    (hNQ : N * Q ≤ A) :
    (Real.exp Real.pi * (T / ((A / p : ℕ) : ℝ) + 4)
          * (((A / (N * p) + 1 : ℕ) : ℝ) / ((A / p : ℕ) : ℝ))
        ≤ replacementCost A N Q T) ∧
    (Real.exp Real.pi * (T / ((B / p : ℕ) : ℝ) + 4)
          * (((B / (N * p) + 1 : ℕ) : ℝ) / ((B / p : ℕ) : ℝ))
        ≤ replacementCost A N Q T) := by
  have hp1 : 1 ≤ p := hp.one_le
  have h2pA : 2 * p ≤ A := by
    have hp2 := hp.two_le
    have : 2 * p ≤ p * p := Nat.mul_le_mul_right p hp2
    exact this.trans hppA
  have hNpA : N * p ≤ A :=
    (Nat.mul_le_mul_left N hpQ).trans hNQ
  have hNA : N ≤ A / p := (Nat.le_div_iff_mul_le hp.pos).mpr hNpA
  have hNB : N ≤ B / p := (Nat.le_div_iff_mul_le hp.pos).mpr (hNpA.trans hAB)
  have h2pB : 2 * p ≤ B := h2pA.trans hAB
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hB0 : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (lt_of_lt_of_le hA hAB)
  have hpQ' : (p : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hpQ
  have hcostA := collar_cost_le A N p T (Q : ℝ) hN hp1 h2pA hNA hT hpQ'
  have hcostB := collar_cost_le B N p T (Q : ℝ) hN hp1 h2pB hNB hT hpQ'
  constructor
  · simpa [replacementCost] using hcostA
  · refine hcostB.trans ?_
    have hnum : 0 ≤ 2 * T * (Q : ℝ) := by positivity
    have hfrac : 2 * T * (Q : ℝ) / (B : ℝ)
        ≤ 2 * T * (Q : ℝ) / (A : ℝ) := by
      rw [div_le_div_iff₀ hB0 hA0]
      have hAB' : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB
      nlinarith [mul_le_mul_of_nonneg_left hAB' hnum]
    unfold replacementCost
    gcongr

/-- The endpoint hypotheses of `eadic_replacement_error_le_budget` follow
uniformly from the level endpoint `Q` and `N·Q ≤ A`. -/
theorem eadic_replacement_costs_of_schedule
    (P : Finset ℕ) (N v₀ v₁ A B Q : ℕ) (T : ℝ)
    (hN : 0 < N) (hA : 0 < A) (hAB : A ≤ B) (hT : 0 ≤ T)
    (hprime : ∀ p ∈ P, p.Prime) (hppA : ∀ p ∈ P, p * p ≤ A)
    (hQ : ∀ p ∈ P, p ≤ Q) (hNQ : N * Q ≤ A) :
    (∀ v ∈ Finset.Ico v₀ (v₁ + 1), ∀ p ∈ eadicCell P (2 * N) v,
      Real.exp Real.pi * (T / ((A / p : ℕ) : ℝ) + 4)
          * (((A / (N * p) + 1 : ℕ) : ℝ) / ((A / p : ℕ) : ℝ))
        ≤ replacementCost A N Q T) ∧
    (∀ v ∈ Finset.Ico v₀ (v₁ + 1), ∀ p ∈ eadicCell P (2 * N) v,
      Real.exp Real.pi * (T / ((B / p : ℕ) : ℝ) + 4)
          * (((B / (N * p) + 1 : ℕ) : ℝ) / ((B / p : ℕ) : ℝ))
        ≤ replacementCost A N Q T) := by
  constructor <;> intro v hv p hp
  · exact (replacement_endpoint_cost_pair A B N Q p T hN hA hAB hT
      (hprime p (mem_eadicCell.mp hp).1) (hppA p (mem_eadicCell.mp hp).1)
      (hQ p (mem_eadicCell.mp hp).1) hNQ).1
  · exact (replacement_endpoint_cost_pair A B N Q p T hN hA hAB hT
      (hprime p (mem_eadicCell.mp hp).1) (hppA p (mem_eadicCell.mp hp).1)
      (hQ p (mem_eadicCell.mp hp).1) hNQ).2

/-- M-10 with its two endpoint costs discharged by schedule parameters.  The
remaining hypothesis is the corrected, explicit collar inequality. -/
theorem eadic_replacement_error_le_budget_of_schedule
    (P : Finset ℕ) (N v₀ v₁ A B Q Pb Kc bb : ℕ)
    (T c₃ eps rho kappa : ℝ) (aa : ℕ → ℕ)
    (hN : 0 < N) (hA : 0 < A) (hAB : A ≤ B) (hT : 0 ≤ T)
    (hprime : ∀ p ∈ P, p.Prime) (hppA : ∀ p ∈ P, p * p ≤ A)
    (hQ : ∀ p ∈ P, p ≤ Q) (hNQ : N * Q ≤ A)
    (hPb : 1 ≤ Pb) (hKc : 2 ≤ Kc) (hbb : 3 ≤ bb)
    (haa : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), Pb ≤ aa v)
    (hcell : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      eadicCell P (2 * N) v ⊆ (Finset.Ioc (aa v) (aa v + Kc)).filter Nat.Prime)
    (hlevel : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      eadicCell P (2 * N) v ⊆ (Finset.Ioc Pb bb).filter Nat.Prime)
    (hkappac : 0 ≤ kappa * c₃) (hrho : eps ≤ rho)
    (hschedule :
      64 * ((Finset.Ico v₀ (v₁ + 1)).card : ℝ) * replacementCost A N Q T
          * ((256 * (Kc : ℝ) / ((Pb : ℝ) * Real.log Kc))
            * (Real.log (Real.log ((bb : ℝ) + 1)) + 11))
        ≤ kappa * c₃ * eps ^ 3) :
    2 * (((Finset.Ico v₀ (v₁ + 1)).card : ℝ)
      * ∑ v ∈ Finset.Ico v₀ (v₁ + 1),
        (∑ p ∈ eadicCell P (2 * N) v, (1 : ℝ) / (p : ℝ))
          * ∑ p ∈ eadicCell P (2 * N) v, ((1 : ℝ) / (p : ℝ))
            * (2 * (Real.exp Real.pi * (T / ((A / p : ℕ) : ℝ) + 4)
                * (((A / (N * p) + 1 : ℕ) : ℝ) / ((A / p : ℕ) : ℝ)))
              + 2 * (Real.exp Real.pi * (T / ((B / p : ℕ) : ℝ) + 4)
                * (((B / (N * p) + 1 : ℕ) : ℝ) / ((B / p : ℕ) : ℝ)))))
      ≤ kappa * bandBudget c₃ eps rho := by
  obtain ⟨hcostA, hcostB⟩ := eadic_replacement_costs_of_schedule P N v₀ v₁ A B Q T
    hN hA hAB hT hprime hppA hQ hNQ
  exact eadic_replacement_error_le_budget P N v₀ v₁ A B Pb Kc bb T
    (replacementCost A N Q T) c₃ eps rho kappa aa hPb hKc hbb
    (by unfold replacementCost; positivity) hcostA hcostB haa hcell hlevel
    hkappac hrho hschedule

end MoltResearch
