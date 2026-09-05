import MoltResearch.Discrepancy.CellHalaszSchedule

/-!
# The exceptional quotient maximum in schedule form (Track R, A2-III, VI-8f)

This leaf bounds every long and short branch of
`cellHalaszQuotientBudget` by one expression at the top quotient scale.  The
long branch uses monotonicity of `halaszBudgetShell`; the short branch uses the
harmonic ceiling.  The possible division tail has at most one term.
-/

namespace MoltResearch

/-- The uniform schedule envelope for every quotient cost below `B`. -/
noncomputable def cellHalaszScheduleQuotientBound
    (D delta₀ T : ℝ) (B : ℕ) : ℝ :=
  cellHalaszPartialBudget D delta₀ B * cellHalaszAbelFactor T
    + 1 + (Real.log B + 1)

private theorem exp_one_le_three_mul_of_threshold (b : ℕ)
    (hb : cellHalaszThreshold ≤ b) :
    Real.exp 1 ≤ 3 * (b : ℝ) := by
  have he : Real.exp 1 ≤ 2.72 := by
    linarith [Real.exp_one_lt_d9]
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := by
    unfold cellHalaszThreshold at hb
    exact_mod_cast (by omega : 1 ≤ b)
  nlinarith

/-- The partial Halász budget is nonnegative on a long block. -/
theorem cellHalaszPartialBudget_nonneg (D delta₀ : ℝ) (b : ℕ)
    (hdelta : 0 < delta₀) (hb : cellHalaszThreshold ≤ b) :
    0 ≤ cellHalaszPartialBudget D delta₀ b := by
  have hshell := ExpSums.halaszBudgetShell_nonneg D (3 * (b : ℝ))
    (exp_one_le_three_mul_of_threshold b hb)
  unfold cellHalaszPartialBudget
  positivity

/-- The partial budget is monotone in the top scale throughout the long
regime. -/
theorem cellHalaszPartialBudget_mono (D delta₀ : ℝ) (b B : ℕ)
    (hdelta : 0 < delta₀) (hb : cellHalaszThreshold ≤ b) (hbB : b ≤ B) :
    cellHalaszPartialBudget D delta₀ b
      ≤ cellHalaszPartialBudget D delta₀ B := by
  have hshell := ExpSums.halaszBudgetShell_mono D
    (3 * (b : ℝ)) (3 * (B : ℝ))
    (exp_one_le_three_mul_of_threshold b hb) (by exact_mod_cast Nat.mul_le_mul_left 3 hbB)
  have hbB' : (b : ℝ) ≤ (B : ℝ) := by exact_mod_cast hbB
  unfold cellHalaszPartialBudget
  have hden : 0 < 18 * delta₀ := by positivity
  have hshell' : ExpSums.halaszBudgetShell D (3 * (b : ℝ)) / (18 * delta₀)
      ≤ ExpSums.halaszBudgetShell D (3 * (B : ℝ)) / (18 * delta₀) := by
    gcongr
  nlinarith [mul_le_mul_of_nonneg_left hbB' (by positivity : 0 ≤ Real.exp 1 * delta₀)]

/-- The division tail beyond `2a` has at most one harmonic term. -/
theorem cellHalaszDivisionTail_le_one (a b : ℕ) (hb : b ≤ 2 * a + 1) :
    cellHalaszDivisionTail a b ≤ 1 := by
  have hterm : ∀ n ∈ Finset.Ioc (2 * a) b, (1 : ℝ) / (n : ℝ) ≤ 1 := by
    intro n hn
    have hn1 : 1 ≤ n := by
      have := (Finset.mem_Ioc.mp hn).1
      omega
    exact (div_le_one (by exact_mod_cast hn1 : (0 : ℝ) < (n : ℝ))).mpr
      (by exact_mod_cast hn1)
  have hcard : (Finset.Ioc (2 * a) b).card ≤ 1 := by
    rw [Nat.card_Ioc]
    omega
  unfold cellHalaszDivisionTail
  calc
    ∑ n ∈ Finset.Ioc (2 * a) b, (1 : ℝ) / (n : ℝ)
        ≤ ∑ _n ∈ Finset.Ioc (2 * a) b, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = ((Finset.Ioc (2 * a) b).card : ℝ) := by simp
    _ ≤ 1 := by exact_mod_cast hcard

/-- Every long or short quotient cost is bounded by the top-scale schedule
envelope. -/
theorem cellHalaszQuotientCost_le_schedule
    (D delta₀ T : ℝ) (a b B : ℕ)
    (hdelta : 0 < delta₀) (hT : 0 ≤ T) (hB : cellHalaszThreshold ≤ B)
    (hbB : b ≤ B) (hb2 : b ≤ 2 * a + 1) :
    cellHalaszQuotientCost D delta₀ T a b
      ≤ cellHalaszScheduleQuotientBound D delta₀ T B := by
  have hB1 : 1 ≤ B := by
    unfold cellHalaszThreshold at hB
    omega
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast hB1)
  have hpartialB := cellHalaszPartialBudget_nonneg D delta₀ B hdelta hB
  have habel : 0 ≤ cellHalaszAbelFactor T := by
    unfold cellHalaszAbelFactor
    positivity
  by_cases hlong : cellHalaszThreshold ≤ b
  · rw [cellHalaszQuotientCost, if_pos hlong]
    have ha1 : 1 ≤ a := by
      unfold cellHalaszThreshold at hlong
      omega
    have hpartial := cellHalaszPartialBudget_mono D delta₀ b B
      hdelta hlong hbB
    have hpartial0 := cellHalaszPartialBudget_nonneg D delta₀ b hdelta hlong
    have hmain : cellHalaszPartialBudget D delta₀ b
          * cellHalaszAbelFactor T / (a : ℝ)
        ≤ cellHalaszPartialBudget D delta₀ B * cellHalaszAbelFactor T := by
      calc
        cellHalaszPartialBudget D delta₀ b * cellHalaszAbelFactor T / (a : ℝ)
            ≤ cellHalaszPartialBudget D delta₀ b * cellHalaszAbelFactor T := by
          exact div_le_self (mul_nonneg hpartial0 habel) (by exact_mod_cast ha1)
        _ ≤ cellHalaszPartialBudget D delta₀ B * cellHalaszAbelFactor T := by
          gcongr
    have htail := cellHalaszDivisionTail_le_one a b hb2
    unfold cellHalaszLongCost cellHalaszScheduleQuotientBound
    linarith
  · rw [cellHalaszQuotientCost, if_neg hlong]
    have hsub : Finset.Ioc a b ⊆ Finset.Icc 1 B := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      rw [Finset.mem_Icc]
      exact ⟨by omega, hn.2.trans hbB⟩
    have hmass : cellHalaszTrivialCost a b ≤ Real.log B + 1 := by
      unfold cellHalaszTrivialCost
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ => by positivity)).trans (ExpSums.sum_one_div_Icc_le_log B hB1)
    unfold cellHalaszScheduleQuotientBound
    nlinarith [mul_nonneg hpartialB habel]

/-- The finite maximum in `cellHalaszQuotientBudget` is bounded by the same
top-scale envelope. -/
theorem cellHalaszQuotientBudget_le_schedule
    (D delta₀ T : ℝ) (A B : ℕ) (P : Finset ℕ)
    (hdelta : 0 < delta₀) (hT : 0 ≤ T) (hB : cellHalaszThreshold ≤ B)
    (hB2 : B ≤ 2 * A + 1) :
    cellHalaszQuotientBudget D delta₀ T A B P
      ≤ cellHalaszScheduleQuotientBound D delta₀ T B := by
  classical
  have hbound0 : 0 ≤ cellHalaszScheduleQuotientBound D delta₀ T B := by
    have hp := cellHalaszPartialBudget_nonneg D delta₀ B hdelta hB
    have hB1 : 1 ≤ B := by unfold cellHalaszThreshold at hB; omega
    have hlog : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast hB1)
    unfold cellHalaszScheduleQuotientBound cellHalaszAbelFactor
    positivity
  unfold cellHalaszQuotientBudget
  apply Finset.max'_le
  intro x hx
  rw [Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · exact hbound0
  · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    have hn0 : 0 < n := by
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      omega
    exact cellHalaszQuotientCost_le_schedule D delta₀ T (A / n) (B / n) B
      hdelta hT hB (Nat.div_le_self B n)
      (div_le_two_mul_div_add_one A B n hn0 hB2)

/-- The complete pointwise Halász input, with every factor in schedule form. -/
theorem cellHalaszBound_le_explicit_schedule
    (D delta₀ T : ℝ) (Aq Bq y : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ))
    (hdelta : 0 < delta₀) (hT : 0 ≤ T)
    (hB : cellHalaszThreshold ≤ Bq) (hB2 : Bq ≤ 2 * Aq + 1)
    (hy : 4 ≤ y) (hPy : ∀ p ∈ P, p < y) :
    cellHalaszBound D delta₀ T Aq Bq P rest
      ≤ ((2 ^ rest.length : ℕ) : ℝ) * (Real.exp 12 * Real.log y)
        * cellHalaszScheduleQuotientBound D delta₀ T Bq := by
  apply cellHalaszBound_le_schedule D delta₀ T Aq Bq y P rest
    (cellHalaszScheduleQuotientBound D delta₀ T Bq) hy hPy
  · have := cellHalaszQuotientBudget_nonneg D delta₀ T Aq Bq P
    exact this.trans (cellHalaszQuotientBudget_le_schedule D delta₀ T Aq Bq P
      hdelta hT hB hB2)
  · exact cellHalaszQuotientBudget_le_schedule D delta₀ T Aq Bq P
      hdelta hT hB hB2

end MoltResearch
