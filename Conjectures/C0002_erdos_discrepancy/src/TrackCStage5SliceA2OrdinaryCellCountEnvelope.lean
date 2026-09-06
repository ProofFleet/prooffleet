import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryFarMargin
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2CoverCellCount

/-!
# Track R A2-V': ordinary cell-count envelope

The Mertens resolution and the logarithmic width of one ordinary level cost
only a fixed multiple of `2^j (log Q_j)^2`.  This exposes the cell factors
which the `Q_{j-1}^{-9/20}` ladder saving must absorb.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- A level's nonnegative Mertens envelope is at most fourteen times the
logarithm of its upper endpoint. -/
theorem sliceA2LevelMass_le_fourteen_log_Q
    (P0 ratio0 eta j : ℕ) (hP0 : 3 ≤ P0) :
    sliceA2LevelMass P0 ratio0 eta j ≤
      14 * Real.log (sliceA2LadderQ P0 ratio0 eta j : ℝ) := by
  let Q := sliceA2LadderQ P0 ratio0 eta j
  have hQ3 : 3 ≤ Q :=
    hP0.trans ((sliceA2LadderP_mono P0 ratio0 eta (by omega)) (Nat.zero_le j)) |>.trans
      (sliceA2LadderP_le_Q P0 ratio0 eta j)
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hQadd0 : (0 : ℝ) < (Q : ℝ) + 1 := by positivity
  have hmass := sliceA2LevelMass_le_exp_envelope P0 ratio0 eta j
    (Real.log ((Q : ℝ) + 1)) (by omega)
    (by rw [Real.exp_log hQadd0])
  have hlogQ1 : 1 ≤ Real.log (Q : ℝ) := by
    have hexp : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hthreeQ : (3 : ℝ) ≤ Q := by exact_mod_cast hQ3
    exact (calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.strictMonoOn_log (Real.exp_pos 1)
        (by norm_num : (0 : ℝ) < 3) hexp
      _ ≤ Real.log (Q : ℝ) := Real.log_le_log (by norm_num) hthreeQ).le
  have haddSq : (Q : ℝ) + 1 ≤ (Q : ℝ) ^ 2 := by
    have hQ3R : (3 : ℝ) ≤ Q := by exact_mod_cast hQ3
    nlinarith [sq_nonneg ((Q : ℝ) - 1)]
  have hlogAdd : Real.log ((Q : ℝ) + 1) ≤ 2 * Real.log (Q : ℝ) := by
    calc
      Real.log ((Q : ℝ) + 1) ≤ Real.log ((Q : ℝ) ^ 2) :=
        Real.log_le_log hQadd0 haddSq
      _ = 2 * Real.log (Q : ℝ) := by rw [Real.log_pow]; norm_num
  change sliceA2LevelMass P0 ratio0 eta j ≤ 14 * Real.log (Q : ℝ)
  exact hmass.trans (by nlinarith)

/-- Fixed coefficient in the all-level ordinary cell-count bound. -/
noncomputable def sliceA2OrdinaryCellCountCoefficient
    (eps rho0 : ℝ) : ℝ :=
  8 + 28 * sliceA2CoverCellCoefficient eps rho0

theorem sliceA2OrdinaryCellCountCoefficient_pos
    (eps rho0 : ℝ) (heps : 0 < eps) (hrho0 : 0 < rho0) :
    0 < sliceA2OrdinaryCellCountCoefficient eps rho0 := by
  unfold sliceA2OrdinaryCellCountCoefficient sliceA2CoverCellCoefficient
  positivity

/-- Every ordinary e-adic index range has a uniform logarithmic envelope. -/
theorem sliceA2Ordinary_cell_card_le_envelope
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ)
    (hP0 : 3 ≤ P0) (heps : 0 < eps) (hrho0 : 0 < rho0) :
    ((Finset.Ico
        (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
        (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 + 1)).card : ℝ) ≤
      sliceA2OrdinaryCellCountCoefficient eps rho0 *
        (2 ^ j : ℕ) *
        Real.log (sliceA2LadderQ P0 ratio0 eta j : ℝ) ^ 2 := by
  let P := sliceA2LadderP P0 ratio0 eta j
  let Q := sliceA2LadderQ P0 ratio0 eta j
  let N := sliceA2OrdinaryN P0 ratio0 eta j eps rho0
  let C := sliceA2CoverCellCoefficient eps rho0
  have hP3 : 3 ≤ P := hP0.trans
    ((sliceA2LadderP_mono P0 ratio0 eta (by omega)) (Nat.zero_le j))
  have hPQ : P ≤ Q := sliceA2LadderP_le_Q P0 ratio0 eta j
  have hQ3 : 3 ≤ Q := hP3.trans hPQ
  have hlogP0 : 0 ≤ Real.log (P : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ P by omega))
  have hlogQ1 : 1 ≤ Real.log (Q : ℝ) := by
    have hexp : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hthreeQ : (3 : ℝ) ≤ Q := by exact_mod_cast hQ3
    exact (calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.strictMonoOn_log (Real.exp_pos 1)
        (by norm_num : (0 : ℝ) < 3) hexp
      _ ≤ Real.log (Q : ℝ) := Real.log_le_log (by norm_num) hthreeQ).le
  have hpow1 : (1 : ℝ) ≤ (2 ^ j : ℕ) := by
    exact_mod_cast Nat.one_le_pow j 2 (by norm_num)
  have hC0 : 0 < C := by dsimp [C, sliceA2CoverCellCoefficient]; positivity
  have hmass := sliceA2LevelMass_le_fourteen_log_Q P0 ratio0 eta j hP0
  have hNraw := sliceA2OrdinaryN_le_cellCoefficient
    P0 ratio0 eta j eps rho0 heps hrho0
  have hN : (N : ℝ) ≤
      3 + 14 * C * Real.log (Q : ℝ) * (2 ^ j : ℕ) := by
    calc
      (N : ℝ) ≤ 3 + C * sliceA2LevelMass P0 ratio0 eta j *
          (2 ^ j : ℕ) := by simpa [N, C] using hNraw
      _ ≤ 3 + C * (14 * Real.log (Q : ℝ)) * (2 ^ j : ℕ) := by gcongr
      _ = _ := by ring
  have hcardRaw := ordinaryLevel_cell_card_le P Q N (by omega) hPQ
    (by dsimp [N]; exact sliceA2OrdinaryN_pos P0 ratio0 eta j eps rho0)
  have hwidth : Real.log (Q : ℝ) - Real.log (P : ℝ) ≤ Real.log (Q : ℝ) := by
    linarith
  have hwidth0 : 0 ≤ Real.log (Q : ℝ) - Real.log (P : ℝ) :=
    sub_nonneg.mpr (Real.log_le_log (by positivity) (by exact_mod_cast hPQ))
  have hstep : ((Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 + 1)).card : ℝ) ≤
      2 * (3 + 14 * C * Real.log (Q : ℝ) * (2 ^ j : ℕ)) *
        Real.log (Q : ℝ) + 2 := by
    calc
      _ ≤ 2 * (N : ℝ) *
          (Real.log (Q : ℝ) - Real.log (P : ℝ)) + 2 := by
        simpa [sliceA2OrdinaryV0, sliceA2OrdinaryV1, P, Q, N] using hcardRaw
      _ ≤ 2 * (3 + 14 * C * Real.log (Q : ℝ) * (2 ^ j : ℕ)) *
          Real.log (Q : ℝ) + 2 := by gcongr
  calc
    _ ≤ 2 * (3 + 14 * C * Real.log (Q : ℝ) * (2 ^ j : ℕ)) *
        Real.log (Q : ℝ) + 2 := hstep
    _ ≤ (8 + 28 * C) * (2 ^ j : ℕ) * Real.log (Q : ℝ) ^ 2 := by
      have hlogQ0 : 0 ≤ Real.log (Q : ℝ) := zero_le_one.trans hlogQ1
      have hlogQsq : 1 ≤ Real.log (Q : ℝ) ^ 2 := by nlinarith
      have hYle : Real.log (Q : ℝ) ≤
          (2 ^ j : ℕ) * Real.log (Q : ℝ) ^ 2 := by
        calc
          Real.log (Q : ℝ) ≤ Real.log (Q : ℝ) ^ 2 := by nlinarith
          _ = 1 * Real.log (Q : ℝ) ^ 2 := by ring
          _ ≤ (2 ^ j : ℕ) * Real.log (Q : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hpow1 (sq_nonneg _)
      have hone : (1 : ℝ) ≤
          (2 ^ j : ℕ) * Real.log (Q : ℝ) ^ 2 := by
        nlinarith [mul_le_mul hpow1 hlogQsq (by norm_num) (by positivity)]
      nlinarith
    _ = _ := by rfl

end Tao2015

end MoltResearch
