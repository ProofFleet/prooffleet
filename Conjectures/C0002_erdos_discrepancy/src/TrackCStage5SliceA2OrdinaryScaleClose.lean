import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2JointLowRemainder

/-!
# Track R A2-V': eventual ordinary endpoint margins

The selected last ordinary endpoint is eventually below the exceptional
lower endpoint.  Moreover `2^J` is no larger than that last endpoint, so one
quadratic exceptional-endpoint domination pays the complete wide cardinality
factor `Q_last*2^J/A` as well as the quotient and collar guards.
-/

namespace MoltResearch

namespace Tao2015

/-- All scale-dependent ordinary endpoint hypotheses of the closed schedule
hold throughout the final scale window. -/
theorem exists_sliceA2Ordinary_scale_margins
    (P0 ratio0 eta : ℕ) (epsc eps rho0 : ℝ)
    (hP0 : 2 ≤ P0) (heta : 1 ≤ eta)
    (heps : 0 < eps) (hrho0 : 0 < rho0) :
    ∃ A0 : ℕ, ∀ A1 A : ℕ, A0 ≤ A1 → A1 ≤ A →
      let J := sliceA2LadderJ P0 ratio0 eta A1 hP0
      let Q := sliceA2LadderQ P0 ratio0 eta (J - 1)
      Q ≤ exceptionalPrimeLower A1 ∧
        2 * Q ≤ A ∧
        (∀ Delta : ℕ, 15 * Delta ≤ A → Delta + Q ≤ A) ∧
        64 * 9 * Real.exp Real.pi * ((Q : ℝ) / A) ≤
          3 * eps ^ 2 * rho0 / (1024 * (2 : ℝ) ^ J) := by
  let target : ℝ := 3 * eps ^ 2 * rho0
  let coefficient : ℝ := 64 * 9 * Real.exp Real.pi * 1024
  let C : ℝ := max 1 (coefficient / target)
  have htarget : 0 < target := by dsimp [target]; positivity
  have hcoefficient : 0 < coefficient := by dsimp [coefficient]; positivity
  have hC : 0 < C :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 (coefficient / target))
  obtain ⟨AB, hAB⟩ :=
    exists_sliceA2Ladder_brunGrowthMargins P0 ratio0 eta epsc hP0 heta
  obtain ⟨AD, hAD⟩ := exists_const_mul_exceptionalPrimeUpper_pow_le
    C 2 epsc hC (by norm_num)
  let A0 := max 3 (max AB AD)
  refine ⟨A0, fun A1 A hA1 hAA1 ↦ ?_⟩
  have hA13 : 3 ≤ A1 := (le_max_left 3 (max AB AD)).trans hA1
  have hAB1 : AB ≤ A1 := (le_max_left AB AD).trans
    ((le_max_right 3 (max AB AD)).trans hA1)
  have hAD1 : AD ≤ A1 := (le_max_right AB AD).trans
    ((le_max_right 3 (max AB AD)).trans hA1)
  let X := Real.log (A1 : ℝ)
  let y := X ^ (1 / 3 : ℝ)
  let J := sliceA2LadderJ P0 ratio0 eta A1 hP0
  let Q := sliceA2LadderQ P0 ratio0 eta (J - 1)
  have hA1pos : (0 : ℝ) < A1 := by exact_mod_cast (show 0 < A1 by omega)
  have hX1 : 1 ≤ X := by
    have hstrict : (1 : ℝ) < Real.log (A1 : ℝ) := by
      calc
        (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
        _ ≤ Real.log (A1 : ℝ) := Real.log_le_log (by norm_num) (by
          exact_mod_cast hA13)
    simpa [X] using hstrict.le
  have hXpos : 0 < X := zero_lt_one.trans_le hX1
  obtain ⟨hn, hQ, hdepth, hbrun⟩ := hAB A1 hAB1
  have hyRemote : y ≤ X ^ (49 / 50 : ℝ) := by
    dsimp [y]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  have hQRemote : (Q : ℝ) ≤ exceptionalPrimeLower A1 := by
    calc
      (Q : ℝ) ≤ (Q : ℝ) + 1 := by norm_num
      _ ≤ Real.exp y := by simpa [Q, J, y, X] using hQ
      _ ≤ Real.exp (X ^ (49 / 50 : ℝ)) :=
        Real.exp_le_exp.mpr hyRemote
      _ ≤ (exceptionalPrimeLower A1 : ℝ) := by
        unfold exceptionalPrimeLower
        rw [Nat.cast_max]
        exact (Nat.le_ceil _).trans (le_max_right _ _)
  have hsep : Q ≤ exceptionalPrimeLower A1 := by exact_mod_cast hQRemote
  have hQU : Q ≤ exceptionalPrimeUpper A1 epsc :=
    hsep.trans (exceptionalPrimeLower_le_upper A1 epsc)
  have hdom := hAD A1 hAD1
  have hQU0 : (0 : ℝ) ≤ exceptionalPrimeUpper A1 epsc := by positivity
  have hQUsub : (exceptionalPrimeUpper A1 epsc : ℝ) ^ 2 ≤ A := by
    have honeC : (1 : ℝ) ≤ C := le_max_left _ _
    calc
      (exceptionalPrimeUpper A1 epsc : ℝ) ^ 2 ≤
          C * (exceptionalPrimeUpper A1 epsc : ℝ) ^ 2 := by
        exact le_mul_of_one_le_left (sq_nonneg _) honeC
      _ ≤ (A1 : ℝ) := by simpa [pow_two] using hdom
      _ ≤ (A : ℝ) := by exact_mod_cast hAA1
  have hdouble : 2 * Q ≤ A := by
    have hQ3 : 3 ≤ exceptionalPrimeUpper A1 epsc :=
      (exceptionalPrimeLower_three_le A1).trans
        (exceptionalPrimeLower_le_upper A1 epsc)
    have htwoQ : 2 * Q ≤ exceptionalPrimeUpper A1 epsc ^ 2 := by
      calc
        2 * Q ≤ 2 * exceptionalPrimeUpper A1 epsc :=
          Nat.mul_le_mul_left 2 hQU
        _ ≤ exceptionalPrimeUpper A1 epsc ^ 2 := by nlinarith
    exact htwoQ.trans (by exact_mod_cast hQUsub)
  have hJ : 0 < J := by
    dsimp [J]
    exact sliceA2LadderJ_pos P0 ratio0 eta A1 hP0
  have htwoJQ : (2 : ℕ) ^ J ≤ Q := by
    have hgrowth := sliceA2LadderP0_mul_two_pow_le
      P0 ratio0 eta (J - 1) hP0
    have hpowshape : (2 : ℕ) ^ J = 2 * 2 ^ (J - 1) := by
      conv_lhs => rw [show J = J - 1 + 1 by omega, pow_succ]
      ring
    rw [hpowshape]
    calc
      2 * 2 ^ (J - 1) ≤ P0 * 2 ^ (J - 1) :=
        Nat.mul_le_mul_right _ hP0
      _ ≤ sliceA2LadderP P0 ratio0 eta (J - 1) := hgrowth
      _ ≤ Q := by
        dsimp [Q]
        exact sliceA2LadderP_le_Q P0 ratio0 eta (J - 1)
  have hQsq : (Q : ℝ) ^ 2 ≤
      (exceptionalPrimeUpper A1 epsc : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hQU) 2
  have hratioC : coefficient / target ≤ C := le_max_right _ _
  have hscaled : coefficient * (Q : ℝ) ^ 2 ≤ target * A := by
    have hratioDom : (coefficient / target) *
        (exceptionalPrimeUpper A1 epsc : ℝ) ^ 2 ≤ A := by
      calc
        _ ≤ C * (exceptionalPrimeUpper A1 epsc : ℝ) ^ 2 := by gcongr
        _ ≤ (A1 : ℝ) := by simpa [pow_two] using hdom
        _ ≤ (A : ℝ) := by exact_mod_cast hAA1
    calc
      coefficient * (Q : ℝ) ^ 2 ≤
          coefficient * (exceptionalPrimeUpper A1 epsc : ℝ) ^ 2 := by
        gcongr
      _ = target * ((coefficient / target) *
          (exceptionalPrimeUpper A1 epsc : ℝ) ^ 2) := by field_simp
      _ ≤ target * A := mul_le_mul_of_nonneg_left hratioDom htarget.le
  have hcard : 64 * 9 * Real.exp Real.pi * ((Q : ℝ) / A) ≤
      3 * eps ^ 2 * rho0 / (1024 * (2 : ℝ) ^ J) := by
    have hApos : (0 : ℝ) < A := by
      exact_mod_cast (show 0 < A by omega)
    have hden : (0 : ℝ) < 1024 * (2 : ℝ) ^ J := by positivity
    rw [show 64 * 9 * Real.exp Real.pi * ((Q : ℝ) / A) =
      (64 * 9 * Real.exp Real.pi * Q) / A by ring]
    rw [div_le_div_iff₀ hApos hden]
    have hJcast : (2 : ℝ) ^ J ≤ Q := by
      exact_mod_cast htwoJQ
    have hprod : (Q : ℝ) * (2 : ℝ) ^ J ≤ (Q : ℝ) * Q :=
      mul_le_mul_of_nonneg_left hJcast (by positivity)
    calc
      (64 * 9 * Real.exp Real.pi * Q) *
          (1024 * (2 : ℝ) ^ J) ≤ coefficient * (Q : ℝ) ^ 2 := by
        dsimp [coefficient]
        nlinarith
      _ ≤ target * A := hscaled
      _ = (3 * eps ^ 2 * rho0) * A := by rfl
  refine ⟨hsep, hdouble, ?_, ?_⟩
  · intro Delta hDelta
    change Delta + Q ≤ A
    omega
  · simpa [J, Q] using hcard

end Tao2015

end MoltResearch
