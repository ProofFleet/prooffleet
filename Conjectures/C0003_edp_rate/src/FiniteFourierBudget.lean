import Conjectures.C0003_edp_rate.src.FiniteFourier

/-!
# A source-budget-safe finite Fourier schedule

The A5 exponent-box construction was conditional on its exact terminal source budget fitting
below the outer product horizon.  The revised analysis cutoff is the greatest scale for which
that inequality holds.  This file proves the cutoff invariant and installs the resulting
budgeted `FiniteFourierReductionAssumption` instance.

This is only the Fourier leg of the conditional reduction.  It does not supply either analytic
assumption and therefore does not prove an Erdős-discrepancy rate.  See
`Problems/edp_rate_fourier_redesign.md`.
-/

namespace MoltResearch

/-- The scheduled budget at the chosen cutoff fits below the integral outer horizon. -/
theorem edpScheduledSourceBudget_cutoff_le_floor (x : ℝ) :
    edpScheduledSourceBudget (edpAnalysisCutoff x) ≤ ⌊x⌋₊ := by
  unfold edpAnalysisCutoff
  exact Nat.findGreatest_spec (P := fun X => edpScheduledSourceBudget X ≤ ⌊x⌋₊)
    (Nat.zero_le _) (by simp [edpScheduledSourceBudget, spectralSourceBudget])

/-- Any individually feasible scale is admitted by the greatest-feasible cutoff.  This is the
finite statement needed later to show that the revised cutoff eventually exceeds each fixed
analytic threshold. -/
theorem le_edpAnalysisCutoff_of_scheduledBudget {x : ℝ} {X : ℕ}
    (hX : X ≤ ⌊x⌋₊) (hbudget : edpScheduledSourceBudget X ≤ ⌊x⌋₊) :
    X ≤ edpAnalysisCutoff x := by
  exact Nat.le_findGreatest hX hbudget

/-- A completely explicit outer threshold admits any fixed analysis scale.  In particular,
the revised cutoff is cofinal: to admit `X`, it is enough that the real outer horizon exceed
the natural number `max X (edpScheduledSourceBudget X)`. -/
theorem le_edpAnalysisCutoff_of_outer_ge {x : ℝ} (X : ℕ)
    (hx : ((max X (edpScheduledSourceBudget X) : ℕ) : ℝ) ≤ x) :
    X ≤ edpAnalysisCutoff x := by
  apply le_edpAnalysisCutoff_of_scheduledBudget
  · have hmax : X ≤ max X (edpScheduledSourceBudget X) := Nat.le_max_left _ _
    have hmaxR : (X : ℝ) ≤ (max X (edpScheduledSourceBudget X) : ℕ) := by
      exact_mod_cast hmax
    exact Nat.le_floor (hmaxR.trans hx)
  · have hmax : edpScheduledSourceBudget X ≤ max X (edpScheduledSourceBudget X) :=
      Nat.le_max_right _ _
    have hmaxR : (edpScheduledSourceBudget X : ℝ) ≤
        (max X (edpScheduledSourceBudget X) : ℕ) := by
      exact_mod_cast hmax
    exact Nat.le_floor (hmaxR.trans hx)

/-- The terminal source budget used by A5 is definitionally the scheduled budget at the
revised cutoff. -/
theorem edpFourierSourceBudget_eq_scheduled (x : ℝ) :
    edpFourierSourceBudget x = edpScheduledSourceBudget (edpAnalysisCutoff x) := by
  rfl

/-- Exact source-budget fit in the outer real horizon. -/
theorem edpFourierSourceBudget_le_outer {x : ℝ} (hx : 0 ≤ x) :
    (edpFourierSourceBudget x : ℝ) ≤ x := by
  rw [edpFourierSourceBudget_eq_scheduled]
  exact le_trans (by
    exact_mod_cast edpScheduledSourceBudget_cutoff_le_floor x) (Nat.floor_le hx)

/-- Every shorter spectral moment has its entire audited source budget inside the same outer
horizon. -/
theorem spectralSourceBudget_at_cutoff_le_outer {x : ℝ} {n : ℕ} (hx : 0 ≤ x)
    (hn : n ≤ edpAnalysisCutoff x) :
    (spectralSourceBudget (edpFourierScale x) (edpFourierModulus x) n : ℝ) ≤ x := by
  exact le_trans (by
    exact_mod_cast spectralSourceBudget_le_edpFourierSourceBudget (x := x) hn)
    (edpFourierSourceBudget_le_outer hx)

/-- Route (a) discharges the finite Fourier interface: the source-budget-aware cutoff turns
the sole premise isolated in A5 into a theorem. -/
noncomputable instance finiteFourierReductionAssumption_budgetSafe :
    FiniteFourierReductionAssumption .budgeted := by
  let hhistorical : FiniteFourierReductionAssumption .historical :=
    finiteFourierReduction_of_schedule fun _ hx =>
      edpFourierSourceBudget_le_outer (le_of_lt (lt_trans (by
        unfold edpRateStart
        positivity) hx))
  exact ⟨hhistorical.reduce⟩

end MoltResearch
