import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalBrunHalfMargin

/-!
# Track R A2-V': uniform exceptional Brun closure

The selected ladder's growth envelope, fourth-power exceptional separation,
and the natural-division rounding allowance are assembled here.
-/

namespace MoltResearch

namespace Tao2015

set_option maxHeartbeats 800000 in
/-- At every sufficiently large window base, the positive ladder contributes
at most one quarter of the fixed exceptional remainder budget on every cell
quotient interval. -/
theorem exists_sliceA2PositiveLadder_exceptional_remainder_le_quarter
    (P0 ratio0 eta : ℕ) (epsc eps rho0 budget : ℝ)
    (hP0 : 3 ≤ P0) (heta : 1 ≤ eta) (hbudget : 0 < budget)
    (hetaBrun : 64 * Real.exp 12 ≤ budget * eta) :
    ∃ A0 : ℕ, ∀ A1 A Delta : ℕ, A0 ≤ A1 → A1 ≤ A → Delta ≤ A →
      ∀ v : ℕ,
        ladderSiftedLogMass
            (A / sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
            ((A + Delta) /
              sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
            ((List.range
              (sliceA2LadderJ P0 ratio0 eta A1 (by omega) - 1)).map
              (fun i => sliceA2LadderPrimes P0 ratio0 eta (i + 1))) ≤
          budget / 4 := by
  obtain ⟨AG, hAG⟩ := exists_sliceA2Ladder_brunGrowthMargins
    P0 ratio0 eta budget (by omega) heta
  obtain ⟨AH, hAH⟩ := exists_sliceA2_brun_half_log_margin budget
  obtain ⟨AQ, hAQ⟩ := exists_const_mul_exceptionalPrimeUpper_pow_le
    1 4 epsc (by norm_num) (by norm_num)
  obtain ⟨AL, hAL⟩ := exists_sliceA2_log_ge (4 * Real.log 2)
  refine ⟨max 2 (max AG (max AH (max AQ AL))), fun A1 A Delta hA1 hA hDelta v ↦ ?_⟩
  have hA12 : 2 ≤ A1 := (le_max_left _ _).trans hA1
  have hAG1 : AG ≤ A1 := (le_max_left AG (max AH (max AQ AL))).trans
    ((le_max_right 2 (max AG (max AH (max AQ AL)))).trans hA1)
  have hAH1 : AH ≤ A1 := (le_max_left AH (max AQ AL)).trans
    ((le_max_right AG (max AH (max AQ AL))).trans
      ((le_max_right 2 (max AG (max AH (max AQ AL)))).trans hA1))
  have hAQ1 : AQ ≤ A1 := (le_max_left AQ AL).trans
    ((le_max_right AH (max AQ AL)).trans
      ((le_max_right AG (max AH (max AQ AL))).trans
        ((le_max_right 2 (max AG (max AH (max AQ AL)))).trans hA1)))
  have hAL1 : AL ≤ A1 := (le_max_right AQ AL).trans
    ((le_max_right AH (max AQ AL)).trans
      ((le_max_right AG (max AH (max AQ AL))).trans
        ((le_max_right 2 (max AG (max AH (max AQ AL)))).trans hA1)))
  let X := Real.log (A1 : ℝ)
  let y := X ^ (1 / 3 : ℝ)
  let J := sliceA2LadderJ P0 ratio0 eta A1 (by omega)
  let n := J - 1
  let q := sliceA2ExceptionalRepresentative A1 v epsc eps rho0
  let a := A / q
  obtain ⟨hn, hQ, hK, -⟩ := hAG A1 hAG1
  have hhalf : Real.log (32 / budget) + y + 2 * y ^ 2 ≤ X / 2 := by
    simpa [X, y] using hAH A1 hAH1
  have hQ4real : (exceptionalPrimeUpper A1 epsc : ℝ) ^ 4 ≤ A1 := by
    simpa using hAQ A1 hAQ1
  have hQ4 : exceptionalPrimeUpper A1 epsc ^ 4 ≤ A1 := by
    exact_mod_cast hQ4real
  have hq : 1 ≤ q := by
    dsimp [q]
    exact (sliceA2Exceptional_cell_data A1 epsc eps rho0).2.2.1 v
  have hqQ : q ≤ exceptionalPrimeUpper A1 epsc := by
    exact sliceA2ExceptionalRepresentative_le_upper A1 v epsc eps rho0
  have hq4 : q ^ 4 ≤ A1 :=
    (pow_le_pow_left' hqQ 4).trans hQ4
  have hquotLog : X / 2 ≤ Real.log (a : ℝ) := by
    apply sliceA2Exceptional_quotient_log_lower A1 A q hA12 hA hq hq4
    simpa [X] using hAL A1 hAL1
  have ha : 1 ≤ a := by
    have hq2q4 : q ^ 2 ≤ q ^ 4 := pow_le_pow_right' hq (by omega)
    have hq2A : q * q ≤ A := by
      simpa [pow_two] using hq2q4.trans (hq4.trans hA)
    dsimp [a]
    exact hq.trans ((Nat.le_div_iff_mul_le (by omega)).2 hq2A)
  have hmargin : Real.log (32 / budget) + y + 2 * y ^ 2 ≤
      Real.log (a : ℝ) := hhalf.trans hquotLog
  have hlog16 : Real.log (16 / budget) ≤ Real.log (32 / budget) := by
    apply Real.log_le_log (by positivity)
    exact (div_le_div_iff_of_pos_right hbudget).2 (by norm_num)
  have hsmall : Real.log (16 / budget) + y ≤ X / 2 := by
    have hy2 : 0 ≤ 2 * y ^ 2 := by positivity
    linarith
  have hexpSmall : Real.exp y ≤ budget / 16 * Real.exp (X / 2) := by
    have hexp := Real.exp_le_exp.mpr hsmall
    rw [Real.exp_add, Real.exp_log (by positivity)] at hexp
    calc
      Real.exp y = budget / 16 * ((16 / budget) * Real.exp y) := by
        field_simp
      _ ≤ budget / 16 * Real.exp (X / 2) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
  have hexpA : Real.exp (X / 2) ≤ (a : ℝ) := by
    calc
      Real.exp (X / 2) ≤ Real.exp (Real.log (a : ℝ)) :=
        Real.exp_le_exp.mpr hquotLog
      _ = (a : ℝ) := Real.exp_log (by positivity)
  have hna : (n : ℝ) ≤ budget / 16 * (a : ℝ) := by
    calc
      (n : ℝ) ≤ Real.exp y := by simpa [n, J, X, y] using hn
      _ ≤ budget / 16 * Real.exp (X / 2) := hexpSmall
      _ ≤ budget / 16 * (a : ℝ) :=
        mul_le_mul_of_nonneg_left hexpA (by positivity)
  have hround : (n : ℝ) / (2 * a + 1 : ℕ) ≤ budget / 16 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 * a + 1 : ℕ))).2
    calc
      (n : ℝ) ≤ budget / 16 * (a : ℝ) := hna
      _ ≤ budget / 16 * (2 * a + 1 : ℕ) := by
        gcongr
        norm_num
        omega
  apply sliceA2PositiveLadder_exceptional_remainder_le_quarter
    P0 ratio0 eta n A Delta q budget y hP0 (by omega) ha hDelta
    hbudget (by dsimp [y]; positivity)
  · exact hetaBrun
  · simpa [n, J, X, y] using hn
  · simpa [n, J, X, y] using hQ
  · simpa [n, J, X, y] using hK
  · simpa [a] using hmargin
  · simpa [a] using hround

end Tao2015

end MoltResearch
