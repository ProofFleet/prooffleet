import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2CoverCellCount
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2BrunGrowth

/-!
# Track R A2-V': uniform last-cell cardinality margin

The scalar hypotheses of the last-level cell-count estimate all hold beyond
one threshold depending only on the fixed schedule parameters.
-/

namespace MoltResearch

namespace Tao2015

open Finset

set_option maxHeartbeats 800000 in
/-- Uniformly at the selected ladder height, the last ordinary cell count is
at most the exceptional upper endpoint. -/
theorem exists_sliceA2Ordinary_last_cell_card_le_exceptionalPrimeUpper
    (P0 ratio0 eta : ℕ) (epsc eps rho0 : ℝ)
    (hP0 : 2 ≤ P0) (heta : 1 ≤ eta) (heps : 0 < eps)
    (hrho0 : 0 < rho0) :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 →
      let J := sliceA2LadderJ P0 ratio0 eta A1 hP0
      ((Finset.Ico
          (sliceA2OrdinaryV0 P0 ratio0 eta (J - 1) eps rho0)
          (sliceA2OrdinaryV1 P0 ratio0 eta (J - 1) eps rho0 + 1)).card : ℝ) ≤
        exceptionalPrimeUpper A1 epsc := by
  obtain ⟨AC, hAC⟩ :=
    exists_sliceA2Ladder_cutoff_envelopes P0 ratio0 eta hP0 heta
  obtain ⟨AB, hAB⟩ :=
    exists_sliceA2Ladder_brunGrowthMargins P0 ratio0 eta epsc hP0 heta
  let C : ℝ := max 16 (sliceA2CoverCellCoefficient eps rho0)
  let M : ℝ := max 10 (3 * Real.log C)
  let AG : ℕ := ⌈Real.exp (Real.exp M)⌉₊ + 1
  refine ⟨max AC (max AB AG), fun A1 hA1 => ?_⟩
  have hAC1 : AC ≤ A1 := (le_max_left AC (max AB AG)).trans hA1
  have hAB1 : AB ≤ A1 := (le_max_left AB AG).trans
    ((le_max_right AC (max AB AG)).trans hA1)
  have hAG1 : AG ≤ A1 := (le_max_right AB AG).trans
    ((le_max_right AC (max AB AG)).trans hA1)
  obtain ⟨hJ2, hn, hratio, hF, hcut⟩ := hAC A1 hAC1
  obtain ⟨hnB, hQ, hdepth, hbrun⟩ := hAB A1 hAB1
  let X := Real.log (A1 : ℝ)
  let W := Real.log X
  let y := X ^ (1 / 3 : ℝ)
  let J := sliceA2LadderJ P0 ratio0 eta A1 hP0
  have hA1pos : (0 : ℝ) < A1 := by
    exact_mod_cast (show 0 < A1 by dsimp [AG] at hAG1; omega)
  have hExpExp : Real.exp (Real.exp M) ≤ (A1 : ℝ) := by
    calc
      Real.exp (Real.exp M) ≤ (⌈Real.exp (Real.exp M)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (A1 : ℝ) := by
        exact_mod_cast (le_trans (Nat.le_succ ⌈Real.exp (Real.exp M)⌉₊) hAG1)
  have hX : Real.exp M ≤ X := by
    dsimp [X]
    exact (Real.le_log_iff_exp_le hA1pos).mpr hExpExp
  have hM0 : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 10).trans (le_max_left _ _)
  have hXpos : 0 < X := (Real.exp_pos M).trans_le hX
  have hW : M ≤ W := by
    dsimp [W]
    exact (Real.le_log_iff_exp_le hXpos).mpr hX
  have hW10 : (10 : ℝ) ≤ W := (le_max_left _ _).trans hW
  have hW1 : 1 ≤ W := by linarith
  have hX1 : 1 ≤ X := by
    exact (Real.one_le_exp hM0).trans hX
  have hCpos : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hlogC : Real.log C ≤ W / 3 := by
    have hthree : 3 * Real.log C ≤ W :=
      (le_max_right 10 (3 * Real.log C)).trans hW
    linarith
  have hyExp : y = Real.exp (W / 3) := by
    dsimp [y, W]
    rw [Real.rpow_def_of_pos hXpos]
    congr 1
    ring
  have hCy : C ≤ y := by
    rw [hyExp]
    calc
      C = Real.exp (Real.log C) := (Real.exp_log hCpos).symm
      _ ≤ Real.exp (W / 3) := Real.exp_le_exp.mpr hlogC
  have hy16 : (16 : ℝ) ≤ y := (le_max_left _ _).trans hCy
  have hcoefY : sliceA2CoverCellCoefficient eps rho0 ≤ y :=
    (le_max_right _ _).trans hCy
  have htail : 2 * W ≤ X ^ (49 / 50 : ℝ) := by
    let z : ℝ := (49 / 50 : ℝ) * W
    have hz0 : 0 ≤ z := by dsimp [z]; positivity
    have hseries := Real.pow_div_factorial_le_exp z hz0 2
    have hquad : 2 * W ≤ Real.exp z := by
      dsimp [z] at hseries ⊢
      norm_num at hseries
      nlinarith
    calc
      2 * W ≤ Real.exp z := hquad
      _ = X ^ (49 / 50 : ℝ) := by
        rw [Real.rpow_def_of_pos hXpos]
        congr 1
        dsimp [z, W]
        ring
  have hcard := sliceA2Ordinary_last_cell_card_le_exceptionalPrimeLower
    P0 ratio0 eta J A1 eps rho0 hP0 heps hrho0
    (by simpa [X] using hX1) (by simpa [W, X] using hW1)
    (by simpa [J, W, X] using hn)
    (by simpa [J, y, X] using hQ)
    (by simpa [y, X] using hy16)
    (by simpa [y, X] using hcoefY)
    (by simpa [W, X] using htail)
  have hlower : (exceptionalPrimeLower A1 : ℝ) ≤
      exceptionalPrimeUpper A1 epsc := by
    exact_mod_cast exceptionalPrimeLower_le_upper A1 epsc
  exact hcard.trans hlower

end Tao2015

end MoltResearch
