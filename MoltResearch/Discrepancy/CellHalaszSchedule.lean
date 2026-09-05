import MoltResearch.Discrepancy.CellHalasz
import MoltResearch.Discrepancy.SmoothRankin

/-!
# The exceptional cell in schedule form (Track R, A2-III, VI-8f)

This file supplies two monotonicity seams for the exceptional level.  First,
the `P`-supported harmonic mass in `cellHalaszBound` is bounded by the existing
Rankin--Mertens smooth-number estimate.  Second, the balanced exceptional fit
is monotone in the pointwise Halász bound `δ`.

Consequently a consumer only has to bound the finite quotient-cost maximum by
one schedule quantity `Cquot`; the full per-cell pointwise bound is then

`2^J · e^12 · log y · Cquot`.
-/

namespace MoltResearch

/-- If every allowed prime is below `y`, the `P`-supported factors form a
subset of the `y`-smooth numbers. -/
theorem pSmoothHarmonicMass_le (B y : ℕ) (P : Finset ℕ) (hy : 4 ≤ y)
    (hPy : ∀ p ∈ P, p < y) :
    pSmoothHarmonicMass B P ≤ Real.exp 12 * Real.log y := by
  have hsub : (Finset.Icc 1 B).filter (fun n => n.primeFactors ⊆ P)
      ⊆ Nat.smoothNumbersUpTo B y := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Nat.mem_smoothNumbersUpTo, Nat.mem_smoothNumbers]
    have hn0 : n ≠ 0 := by omega
    refine ⟨hn.1.2, hn0, ?_⟩
    intro p hp
    have hpf : p ∈ n.primeFactors := by
      rw [Nat.mem_primeFactors]
      have := (Nat.mem_primeFactorsList hn0).mp hp
      exact ⟨this.1, this.2, hn0⟩
    exact hPy p (hn.2 hpf)
  unfold pSmoothHarmonicMass
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n _ _ => by positivity)).trans (sum_smooth_one_div_le y B hy)

/-- The finite quotient-budget maximum is nonnegative because its defining
set explicitly contains zero. -/
theorem cellHalaszQuotientBudget_nonneg (D delta₀ T : ℝ)
    (A B : ℕ) (P : Finset ℕ) :
    0 ≤ cellHalaszQuotientBudget D delta₀ T A B P := by
  classical
  unfold cellHalaszQuotientBudget
  exact Finset.le_max' _ 0 (Finset.mem_insert_self 0 _)

/-- `cellHalaszBound` with its smooth mass and quotient maximum replaced by
schedule upper bounds. -/
theorem cellHalaszBound_le_schedule
    (D delta₀ T : ℝ) (Aq Bq y : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ)) (Cquot : ℝ)
    (hy : 4 ≤ y) (hPy : ∀ p ∈ P, p < y) (hCquot : 0 ≤ Cquot)
    (hquot : cellHalaszQuotientBudget D delta₀ T Aq Bq P ≤ Cquot) :
    cellHalaszBound D delta₀ T Aq Bq P rest
      ≤ ((2 ^ rest.length : ℕ) : ℝ)
        * (Real.exp 12 * Real.log y) * Cquot := by
  have hsmooth := pSmoothHarmonicMass_le Bq y P hy hPy
  have hsmooth0 : 0 ≤ pSmoothHarmonicMass Bq P := by
    unfold pSmoothHarmonicMass
    positivity
  have hschedule0 : 0 ≤ Real.exp 12 * Real.log y := by
    have : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (by omega : 1 ≤ y)
    positivity
  have hquot0 := cellHalaszQuotientBudget_nonneg D delta₀ T Aq Bq P
  unfold cellHalaszBound
  gcongr

/-- The balanced exceptional-cell cost as a function of its pointwise bound. -/
noncomputable def exceptionalCellScheduleCost
    (Aint Bpri Gamma delta : ℝ) : ℝ :=
  2 * (delta ^ 2 * Bpri + 2 * delta * Real.sqrt (Aint * (Bpri * Gamma)))

/-- The exceptional-cell cost is monotone in the nonnegative pointwise
Halász envelope. -/
theorem exceptionalCellScheduleCost_mono
    (Aint Bpri Gamma delta Delta : ℝ)
    (hA : 0 ≤ Aint) (hB : 0 ≤ Bpri) (hG : 0 ≤ Gamma)
    (hdelta : 0 ≤ delta) (hdeltaDelta : delta ≤ Delta) :
    exceptionalCellScheduleCost Aint Bpri Gamma delta
      ≤ exceptionalCellScheduleCost Aint Bpri Gamma Delta := by
  have hDelta : 0 ≤ Delta := hdelta.trans hdeltaDelta
  have hsqrt : 0 ≤ Real.sqrt (Aint * (Bpri * Gamma)) := Real.sqrt_nonneg _
  have hsq : delta ^ 2 ≤ Delta ^ 2 := by nlinarith
  unfold exceptionalCellScheduleCost
  nlinarith [mul_le_mul_of_nonneg_right hsq hB,
    mul_le_mul_of_nonneg_right hdeltaDelta hsqrt]

/-- A closed upper bound for `delta` discharges the exceptional cell's fit. -/
theorem exceptionalCell_fit_of_schedule
    (Aint Bpri Gamma delta Delta c₃ eps rho kappa : ℝ)
    (hA : 0 ≤ Aint) (hB : 0 ≤ Bpri) (hG : 0 ≤ Gamma)
    (hdelta : 0 ≤ delta) (hdeltaDelta : delta ≤ Delta)
    (hschedule : exceptionalCellScheduleCost Aint Bpri Gamma Delta
      ≤ kappa * bandBudget c₃ eps rho) :
    exceptionalCellScheduleCost Aint Bpri Gamma delta
      ≤ kappa * bandBudget c₃ eps rho :=
  (exceptionalCellScheduleCost_mono Aint Bpri Gamma delta Delta hA hB hG
    hdelta hdeltaDelta).trans hschedule

end MoltResearch
