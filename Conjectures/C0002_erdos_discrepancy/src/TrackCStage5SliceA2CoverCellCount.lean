import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2CoverScale

/-!
# Track R A2-V': last-level cell count

The last ordinary resolution and its logarithmic cell width are polynomial
in `log A1`.  This is negligible compared with the exceptional lower
endpoint `exp((log A1)^(49/50))`.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- Exact fixed coefficient in the upper bound for an ordinary resolution. -/
noncomputable def sliceA2CoverCellCoefficient (eps rho0 : ℝ) : ℝ :=
  393216 * Real.exp Real.pi / (eps ^ 2 * rho0)

/-- The Mertens envelope of a level below `exp y` is at most `y+12`. -/
theorem sliceA2LevelMass_le_exp_envelope
    (P0 ratio0 eta j : ℕ) (y : ℝ) (hP0 : 2 ≤ P0)
    (hQ : (sliceA2LadderQ P0 ratio0 eta j : ℝ) + 1 ≤ Real.exp y) :
    sliceA2LevelMass P0 ratio0 eta j ≤ y + 12 := by
  let P : ℝ := sliceA2LadderP P0 ratio0 eta j
  let Q : ℝ := sliceA2LadderQ P0 ratio0 eta j
  have hP2 : (2 : ℝ) ≤ P := by
    dsimp [P]
    exact_mod_cast sliceA2LadderP_two_le P0 ratio0 eta j hP0
  have hPQ : P ≤ Q := by
    dsimp [P, Q]
    exact_mod_cast sliceA2LadderP_le_Q P0 ratio0 eta j
  have hlogP1 : 1 ≤ Real.log (P + 1) := by
    have hexp : Real.exp 1 < 3 := Real.exp_one_lt_three
    apply (Real.le_log_iff_exp_le (by linarith : 0 < P + 1)).2
    linarith
  have hloglogP0 : 0 ≤ Real.log (Real.log (P + 1)) :=
    Real.log_nonneg hlogP1
  have hQpos : 0 < Q + 1 := by linarith
  have hlogQ : Real.log (Q + 1) ≤ y := by
    calc
      Real.log (Q + 1) ≤ Real.log (Real.exp y) :=
        Real.log_le_log hQpos hQ
      _ = y := Real.log_exp y
  have hlogQpos : 0 < Real.log (Q + 1) := by
    have : 1 < Q + 1 := by linarith
    exact Real.log_pos this
  have hloglogQ : Real.log (Real.log (Q + 1)) ≤ y := by
    calc
      Real.log (Real.log (Q + 1)) ≤ Real.log (Q + 1) - 1 :=
        Real.log_le_sub_one_of_pos hlogQpos
      _ ≤ y := by linarith
  unfold sliceA2LevelMass
  rw [show ((sliceA2LadderP P0 ratio0 eta j : ℝ) + 1) = P + 1 by rfl,
    show ((sliceA2LadderQ P0 ratio0 eta j : ℝ) + 1) = Q + 1 by rfl]
  exact max_le (by linarith) (by linarith)

/-- The ceiling definition gives a usable upper bound for each ordinary
resolution. -/
theorem sliceA2OrdinaryN_le_cellCoefficient
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ)
    (heps : 0 < eps) (hrho0 : 0 < rho0) :
    (sliceA2OrdinaryN P0 ratio0 eta j eps rho0 : ℝ) ≤
      3 + sliceA2CoverCellCoefficient eps rho0 *
        sliceA2LevelMass P0 ratio0 eta j * (2 ^ j : ℕ) := by
  let E := sliceA2LevelMass P0 ratio0 eta j
  let x : ℝ := 9216 * Real.exp Real.pi * E /
    (sliceA2KappaReplacement j * 1 * eps ^ 2 * rho0)
  have hE0 : 0 ≤ E := by dsimp [E]; exact sliceA2LevelMass_nonneg _ _ _ _
  have hk : 0 < sliceA2KappaReplacement j := by
    unfold sliceA2KappaReplacement ordinaryLegShare
    positivity
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hceil : (⌈x⌉₊ : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hx0).le
  have hmax : ((max 2 ⌈x⌉₊ : ℕ) : ℝ) ≤ 2 + (⌈x⌉₊ : ℕ) := by
    exact_mod_cast (show max 2 ⌈x⌉₊ ≤ 2 + ⌈x⌉₊ by omega)
  have hxform : x = sliceA2CoverCellCoefficient eps rho0 * E *
      (2 ^ j : ℕ) := by
    dsimp [x, sliceA2CoverCellCoefficient, sliceA2KappaReplacement,
      ordinaryLegShare]
    field_simp
    push_cast
    ring
  unfold sliceA2OrdinaryN sliceA2LevelN
  change ((max 2 ⌈x⌉₊ : ℕ) : ℝ) ≤ _
  calc
    ((max 2 ⌈x⌉₊ : ℕ) : ℝ) ≤ 2 + (⌈x⌉₊ : ℕ) := hmax
    _ ≤ 2 + (x + 1) := by gcongr
    _ = 3 + sliceA2CoverCellCoefficient eps rho0 * E *
        (2 ^ j : ℕ) := by rw [hxform]; ring
    _ = _ := by rfl

/-- Explicit logarithmic hypotheses imply that every last-level ordinary
cell fits below the exceptional lower endpoint. -/
theorem sliceA2Ordinary_last_cell_card_le_exceptionalPrimeLower
    (P0 ratio0 eta J A1 : ℕ) (eps rho0 : ℝ)
    (hP0 : 2 ≤ P0) (heps : 0 < eps) (hrho0 : 0 < rho0)
    (hX1 : 1 ≤ Real.log (A1 : ℝ))
    (hW1 : 1 ≤ Real.log (Real.log (A1 : ℝ)))
    (hn : ((J - 1 : ℕ) : ℝ) ≤
      Real.log (Real.log (A1 : ℝ)) / 1000)
    (hQ : (sliceA2LadderQ P0 ratio0 eta (J - 1) : ℝ) + 1 ≤
      Real.exp ((Real.log (A1 : ℝ)) ^ (1 / 3 : ℝ)))
    (hy16 : 16 ≤ (Real.log (A1 : ℝ)) ^ (1 / 3 : ℝ))
    (hCy : sliceA2CoverCellCoefficient eps rho0 ≤
      (Real.log (A1 : ℝ)) ^ (1 / 3 : ℝ))
    (htail : 2 * Real.log (Real.log (A1 : ℝ)) ≤
      (Real.log (A1 : ℝ)) ^ (49 / 50 : ℝ)) :
    ((Finset.Ico
        (sliceA2OrdinaryV0 P0 ratio0 eta (J - 1) eps rho0)
        (sliceA2OrdinaryV1 P0 ratio0 eta (J - 1) eps rho0 + 1)).card : ℝ) ≤
      exceptionalPrimeLower A1 := by
  let X := Real.log (A1 : ℝ)
  let W := Real.log X
  let y := X ^ (1 / 3 : ℝ)
  let j := J - 1
  let E := sliceA2LevelMass P0 ratio0 eta j
  let N := sliceA2OrdinaryN P0 ratio0 eta j eps rho0
  let P := sliceA2LadderP P0 ratio0 eta j
  let Q := sliceA2LadderQ P0 ratio0 eta j
  have hXpos : 0 < X := zero_lt_one.trans_le (by simpa [X] using hX1)
  have hWpos : 0 < W := zero_lt_one.trans_le (by simpa [W, X] using hW1)
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hy1 : 1 ≤ y := Real.one_le_rpow (by simpa [X] using hX1) (by norm_num)
  have hE : E ≤ y + 12 := by
    dsimp [E, y, X, Q, j]
    exact sliceA2LevelMass_le_exp_envelope P0 ratio0 eta (J - 1)
      (Real.log (A1 : ℝ) ^ (1 / 3 : ℝ)) hP0 hQ
  have hP2 : 2 ≤ P := by
    dsimp [P, j]
    exact sliceA2LadderP_two_le P0 ratio0 eta (J - 1) hP0
  have hPQ : P ≤ Q := by
    dsimp [P, Q, j]
    exact sliceA2LadderP_le_Q P0 ratio0 eta (J - 1)
  have hlogP0 : 0 ≤ Real.log (P : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ P by omega))
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hlogQ : Real.log (Q : ℝ) ≤ y := by
    have hQaddpos : (0 : ℝ) < (Q : ℝ) + 1 := by positivity
    have hlogAdd : Real.log ((Q : ℝ) + 1) ≤ y := by
      calc
        Real.log ((Q : ℝ) + 1) ≤ Real.log (Real.exp y) := by
          apply Real.log_le_log hQaddpos
          simpa [Q, y, X, j] using hQ
        _ = y := Real.log_exp y
    exact (Real.log_le_log hQpos (by linarith : (Q : ℝ) ≤ Q + 1)).trans hlogAdd
  have hpow : ((2 ^ j : ℕ) : ℝ) ≤ X ^ (1 / 1000 : ℝ) := by
    calc
      ((2 ^ j : ℕ) : ℝ) = (Real.exp (Real.log 2)) ^ j := by
        rw [Nat.cast_pow, Nat.cast_ofNat,
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp ((j : ℝ) * Real.log 2) := by
        rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (W / 1000) := by
        rw [Real.exp_le_exp]
        have hlogtwo : Real.log 2 ≤ 1 :=
          Real.log_two_lt_d9.le.trans (by norm_num)
        have hn' : (j : ℝ) ≤ W / 1000 := by simpa [j, W, X] using hn
        nlinarith
      _ = X ^ (1 / 1000 : ℝ) := by
        rw [Real.rpow_def_of_pos hXpos]
        congr 1
        dsimp [W]
        ring
  have hpowY : ((2 ^ j : ℕ) : ℝ) ≤ y := hpow.trans
    (Real.rpow_le_rpow_of_exponent_le (by simpa [X] using hX1)
      (by norm_num : (1 / 1000 : ℝ) ≤ 1 / 3))
  have hNraw := sliceA2OrdinaryN_le_cellCoefficient
    P0 ratio0 eta j eps rho0 heps hrho0
  have hN : (N : ℝ) ≤ y ^ 4 := by
    have hC0 : 0 < sliceA2CoverCellCoefficient eps rho0 := by
      unfold sliceA2CoverCellCoefficient
      positivity
    have hN1 : (N : ℝ) ≤
        3 + sliceA2CoverCellCoefficient eps rho0 * (y + 12) * y := by
      calc
        (N : ℝ) ≤ 3 + sliceA2CoverCellCoefficient eps rho0 * E *
            (2 ^ j : ℕ) := by simpa [N, E] using hNraw
        _ ≤ 3 + sliceA2CoverCellCoefficient eps rho0 * (y + 12) * y := by
          gcongr
    have hthirteen : y + 12 ≤ 13 * y := by nlinarith
    have hbound : (N : ℝ) ≤ 3 + 13 * y ^ 3 := by
      calc
        (N : ℝ) ≤ 3 + sliceA2CoverCellCoefficient eps rho0 *
            (y + 12) * y := hN1
        _ ≤ 3 + y * (13 * y) * y := by gcongr
        _ = 3 + 13 * y ^ 3 := by ring
    nlinarith [mul_nonneg (sq_nonneg y) (mul_nonneg hy0 (sub_nonneg.mpr hy16))]
  have hcardRaw := ordinaryLevel_cell_card_le P Q N hP2 hPQ
    (by dsimp [N, j]; exact sliceA2OrdinaryN_pos P0 ratio0 eta (J - 1) eps rho0)
  have hwidth : Real.log (Q : ℝ) - Real.log (P : ℝ) ≤ y := by linarith
  have hwidth0 : 0 ≤ Real.log (Q : ℝ) - Real.log (P : ℝ) := by
    exact sub_nonneg.mpr (Real.log_le_log (by positivity) (by exact_mod_cast hPQ))
  have hcardY : ((Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 + 1)).card : ℝ) ≤
      y ^ 6 := by
    have hstep : ((Finset.Ico
        (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
        (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 + 1)).card : ℝ) ≤
        2 * y ^ 4 * y + 2 := by
      calc
        _ ≤ 2 * (N : ℝ) * (Real.log Q - Real.log P) + 2 := by
          simpa [sliceA2OrdinaryV0, sliceA2OrdinaryV1, P, Q, N, j] using hcardRaw
        _ ≤ 2 * y ^ 4 * y + 2 := by gcongr
    have hy5one : 1 ≤ y ^ 5 := one_le_pow₀ hy1
    have hdiff : 2 ≤ y - 2 := by linarith
    have hprod : 2 ≤ y ^ 5 * (y - 2) := by
      calc
        (2 : ℝ) = 1 * 2 := by ring
        _ ≤ y ^ 5 * (y - 2) :=
          mul_le_mul hy5one hdiff (by norm_num) (by positivity)
    exact hstep.trans (by nlinarith)
  have hySix : y ^ 6 = X ^ 2 := by
    dsimp [y]
    rw [← Real.rpow_mul_natCast hXpos.le (1 / 3 : ℝ) 6]
    norm_num
  have hXsq : X ^ 2 ≤ Real.exp (X ^ (49 / 50 : ℝ)) := by
    calc
      X ^ 2 = (Real.exp (Real.log X)) ^ 2 := by rw [Real.exp_log hXpos]
      _ = Real.exp ((2 : ℕ) * Real.log X) := by
        rw [← Real.exp_nat_mul]
      _ = Real.exp (2 * W) := by simp only [Nat.cast_ofNat]; rfl
      _ ≤ Real.exp (X ^ (49 / 50 : ℝ)) := Real.exp_le_exp.mpr (by
        simpa [W, X] using htail)
  have hexceptional : Real.exp (X ^ (49 / 50 : ℝ)) ≤
      (exceptionalPrimeLower A1 : ℝ) := by
    unfold exceptionalPrimeLower
    rw [Nat.cast_max]
    exact (Nat.le_ceil _).trans (le_max_right _ _)
  have hfinal : y ^ 6 ≤ (exceptionalPrimeLower A1 : ℝ) :=
    hySix.le.trans (hXsq.trans hexceptional)
  simpa only [j] using hcardY.trans hfinal

end Tao2015

end MoltResearch
