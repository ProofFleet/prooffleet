import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryCellCountEnvelope

/-!
# Track R A2-V': ordinary not-too-close envelope

After both cell ranges and the borrowed-moment loss are exposed, every
positive-level prefactor is bounded by a fixed coefficient times
`2^(3j) L_j^8 (log Q_{j-1})^6`.  The remaining scale factor is exactly the
`Q_{j-1}^{-9/20}` saving from the ladder jump.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The current logarithmic endpoint is controlled by the borrowed-moment
envelope times the previous endpoint logarithm. -/
theorem sliceA2Ordinary_log_Q_le_moment_mul_log_previous
    (P0 ratio0 eta j : ℕ) (hP0 : 3 ≤ P0) (hj : 0 < j) :
    Real.log (sliceA2LadderQ P0 ratio0 eta j : ℝ) ≤
      sliceA2OrdinaryMomentEnvelope ratio0 eta j *
        Real.log (sliceA2LadderQ P0 ratio0 eta (j - 1) : ℝ) := by
  let Pprev := sliceA2LadderP P0 ratio0 eta (j - 1)
  let Qprev := sliceA2LadderQ P0 ratio0 eta (j - 1)
  let L := sliceA2OrdinaryMomentEnvelope ratio0 eta j
  let F : ℕ := 100 * j ^ 2 * sliceA2LadderRatio ratio0 eta (j - 1) *
    sliceA2LadderRatio ratio0 eta j
  have hformula : Real.log (sliceA2LadderQ P0 ratio0 eta j : ℝ) =
      (F : ℝ) * Real.log (Pprev : ℝ) := by
    simpa [F, Pprev] using sliceA2LadderQ_log_formula P0 ratio0 eta j hj
  have hFL : (F : ℝ) ≤ L := by
    dsimp [F, L, sliceA2OrdinaryMomentEnvelope]
    push_cast
    have hterm : 0 ≤ (j : ℝ) ^ 2 *
        (sliceA2LadderRatio ratio0 eta (j - 1) : ℝ) *
        (sliceA2LadderRatio ratio0 eta j : ℝ) := by positivity
    nlinarith
  have hPprev0 : (0 : ℝ) < Pprev := by
    exact_mod_cast (show 0 < Pprev by
      dsimp [Pprev]
      have := sliceA2LadderP_two_le P0 ratio0 eta (j - 1) (by omega)
      omega)
  have hPQ : Pprev ≤ Qprev := by
    dsimp [Pprev, Qprev]
    exact sliceA2LadderP_le_Q P0 ratio0 eta (j - 1)
  have hlogPQ : Real.log (Pprev : ℝ) ≤ Real.log (Qprev : ℝ) :=
    Real.log_le_log hPprev0 (by exact_mod_cast hPQ)
  have hPprev3 : 3 ≤ Pprev := hP0.trans
    ((sliceA2LadderP_mono P0 ratio0 eta (by omega)) (Nat.zero_le (j - 1)))
  have hlogP0 : 0 ≤ Real.log (Pprev : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ Pprev by omega))
  rw [hformula]
  exact (mul_le_mul_of_nonneg_right hFL hlogP0).trans
    (mul_le_mul_of_nonneg_left hlogPQ
      (zero_le_one.trans (sliceA2OrdinaryMomentEnvelope_one_le ratio0 eta j)))

/-- The exponential loss in the reduced ladder envelope costs at most four
powers of the borrowed-moment envelope and the fixed factor `exp 17`. -/
theorem sliceA2Ordinary_exp_loss_le
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ) :
    Real.exp
        (innerBandScheduleAlpha j /
            (sliceA2OrdinaryN P0 ratio0 eta j eps rho0 : ℝ) +
          2 * (2 * Real.log (sliceA2OrdinaryMomentEnvelope ratio0 eta j) + 3) +
          10) ≤
      Real.exp 17 * sliceA2OrdinaryMomentEnvelope ratio0 eta j ^ 4 := by
  let N := sliceA2OrdinaryN P0 ratio0 eta j eps rho0
  let L := sliceA2OrdinaryMomentEnvelope ratio0 eta j
  have hN1 : (1 : ℝ) ≤ N := by
    exact_mod_cast (show 1 ≤ N by
      dsimp [N]
      have := sliceA2OrdinaryN_pos P0 ratio0 eta j eps rho0
      omega)
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have halpha := innerBandScheduleAlpha_bounds j
  have hdiv : innerBandScheduleAlpha j / (N : ℝ) ≤ 1 := by
    rw [div_le_one hN0]
    linarith
  have hL1 : 1 ≤ L := by
    dsimp [L]
    exact sliceA2OrdinaryMomentEnvelope_one_le ratio0 eta j
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hexponent :
      innerBandScheduleAlpha j / (N : ℝ) +
          2 * (2 * Real.log L + 3) + 10 ≤
        17 + 4 * Real.log L := by
    linarith
  calc
    Real.exp
        (innerBandScheduleAlpha j / (N : ℝ) +
          2 * (2 * Real.log L + 3) + 10) ≤
        Real.exp (17 + 4 * Real.log L) := Real.exp_le_exp.mpr hexponent
    _ = Real.exp 17 * L ^ 4 := by
      rw [Real.exp_add]
      congr 1
      calc
        Real.exp (4 * Real.log L) = Real.exp (Real.log L) ^ 4 := by
          rw [← Real.exp_nat_mul]
          norm_num
        _ = L ^ 4 := by rw [Real.exp_log hL0]
    _ = _ := by rfl

/-- Fully exposed positive-level prefactor, including the denominator from
the uniform previous-cell share. -/
theorem sliceA2Ordinary_reduced_cost_le_close_envelope
    (P0 ratio0 eta j : ℕ) (eps rho0 tau : ℝ)
    (hP0 : 3 ≤ P0) (hj : 0 < j)
    (heps : 0 < eps) (hrho0 : 0 < rho0)
    (htau0 : 0 ≤ tau) (htau : tau ≤ 1) :
    let Icur := Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 + 1)
    let Iprev := Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1)
    let L := sliceA2OrdinaryMomentEnvelope ratio0 eta j
    let Qprev := sliceA2LadderQ P0 ratio0 eta (j - 1)
    (Icur.card : ℝ) ^ 2 *
        (Real.exp (innerBandScheduleAlpha j /
              (sliceA2OrdinaryN P0 ratio0 eta j eps rho0 : ℝ) +
            2 * (2 * Real.log L + 3) + 10) *
          tau ^ (2 * innerBandScheduleAlpha (j - 1)) *
          (Qprev : ℝ) ^ (-(9 : ℝ) / 20)) *
        (Iprev.card : ℝ) ≤
      sliceA2OrdinaryCellCountCoefficient eps rho0 ^ 3 * Real.exp 17 *
        (2 : ℝ) ^ (3 * j) * L ^ 8 * Real.log (Qprev : ℝ) ^ 6 *
        (Qprev : ℝ) ^ (-(9 : ℝ) / 20) := by
  dsimp only
  let C := sliceA2OrdinaryCellCountCoefficient eps rho0
  let L := sliceA2OrdinaryMomentEnvelope ratio0 eta j
  let Qprev := sliceA2LadderQ P0 ratio0 eta (j - 1)
  have hL1 : 1 ≤ L := sliceA2OrdinaryMomentEnvelope_one_le ratio0 eta j
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have hQprev3 : 3 ≤ Qprev :=
    hP0.trans ((sliceA2LadderP_mono P0 ratio0 eta (by omega))
      (Nat.zero_le (j - 1))) |>.trans
      (sliceA2LadderP_le_Q P0 ratio0 eta (j - 1))
  have hlogQ0 : 0 ≤ Real.log (Qprev : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ Qprev by omega))
  have hC0 : 0 ≤ C :=
    (sliceA2OrdinaryCellCountCoefficient_pos eps rho0 heps hrho0).le
  have hcurRaw := sliceA2Ordinary_cell_card_le_envelope
    P0 ratio0 eta j eps rho0 hP0 heps hrho0
  have hlogCur := sliceA2Ordinary_log_Q_le_moment_mul_log_previous
    P0 ratio0 eta j hP0 hj
  have hcur : ((Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 + 1)).card : ℝ) ≤
      C * (2 : ℝ) ^ j * L ^ 2 * Real.log (Qprev : ℝ) ^ 2 := by
    calc
      _ ≤ C * (2 ^ j : ℕ) *
          Real.log (sliceA2LadderQ P0 ratio0 eta j : ℝ) ^ 2 := hcurRaw
      _ ≤ C * (2 : ℝ) ^ j *
          (L * Real.log (Qprev : ℝ)) ^ 2 := by
        norm_num only [Nat.cast_pow, Nat.cast_ofNat]
        gcongr
      _ = _ := by push_cast; ring
  have hprevRaw := sliceA2Ordinary_cell_card_le_envelope
    P0 ratio0 eta (j - 1) eps rho0 hP0 heps hrho0
  have hpow : (2 : ℝ) ^ (j - 1) ≤ (2 : ℝ) ^ j :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hprev : ((Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1)).card : ℝ) ≤
      C * (2 : ℝ) ^ j * Real.log (Qprev : ℝ) ^ 2 := by
    calc
      _ ≤ C * (2 ^ (j - 1) : ℕ) * Real.log (Qprev : ℝ) ^ 2 := hprevRaw
      _ ≤ C * (2 : ℝ) ^ j * Real.log (Qprev : ℝ) ^ 2 := by
        norm_num only [Nat.cast_pow, Nat.cast_ofNat]
        gcongr
  have hexp := sliceA2Ordinary_exp_loss_le P0 ratio0 eta j eps rho0
  have htauPow : tau ^ (2 * innerBandScheduleAlpha (j - 1)) ≤ 1 :=
    Real.rpow_le_one htau0 htau (by
      have := innerBandScheduleAlpha_bounds (j - 1)
      nlinarith [this.1])
  have hQpow0 : 0 ≤ (Qprev : ℝ) ^ (-(9 : ℝ) / 20) := by positivity
  calc
    _ ≤ (C * (2 : ℝ) ^ j * L ^ 2 * Real.log (Qprev : ℝ) ^ 2) ^ 2 *
        ((Real.exp 17 * L ^ 4) * 1 *
          (Qprev : ℝ) ^ (-(9 : ℝ) / 20)) *
        (C * (2 : ℝ) ^ j * Real.log (Qprev : ℝ) ^ 2) := by gcongr
    _ = C ^ 3 * Real.exp 17 * (2 : ℝ) ^ (3 * j) * L ^ 8 *
        Real.log (Qprev : ℝ) ^ 6 *
        (Qprev : ℝ) ^ (-(9 : ℝ) / 20) := by
      have hpow3 : (2 : ℝ) ^ (3 * j) = ((2 : ℝ) ^ j) ^ 3 := by
        calc
          (2 : ℝ) ^ (3 * j) = (2 : ℝ) ^ (j * 3) := by congr 1 <;> omega
          _ = ((2 : ℝ) ^ j) ^ 3 := pow_mul _ _ _
      rw [hpow3]
      ring

end Tao2015

end MoltResearch
