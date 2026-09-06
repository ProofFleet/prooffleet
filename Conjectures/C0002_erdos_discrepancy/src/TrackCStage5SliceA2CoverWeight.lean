import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2CoverMomentBounds

/-!
# Track R A2-V': the ordinary-cover weight loss

At the last ordinary level, the lower endpoint is within a factor six of
every cell anchor.  The exponentially weighted high-moment loss is then at
most `0.404 log(2T) + 0.808 log P`, with the constants recorded exactly as
`101/250` and `101/125`.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- Every ordinary lower endpoint is within a factor six of each scheduled
cell's lower anchor. -/
theorem sliceA2LadderP_le_six_mul_ordinaryAnchor
    (P0 ratio0 eta j r : ℕ) (eps rho0 : ℝ)
    (hP0 : 2 ≤ P0) (hr : r ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1))
    (hanchor : 1 ≤ sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r) :
    (sliceA2LadderP P0 ratio0 eta (j - 1) : ℝ) ≤
      6 * (sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r : ℝ) := by
  let N := sliceA2OrdinaryN P0 ratio0 eta (j - 1) eps rho0
  let P := sliceA2LadderP P0 ratio0 eta (j - 1)
  let Pc := sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r
  have hN : 0 < N := by simpa [N] using
    sliceA2OrdinaryN_pos P0 ratio0 eta (j - 1) eps rho0
  have hlower := sliceA2Ordinary_lower_le_exp P0 ratio0 eta (j - 1)
    eps rho0 hP0 r hr
  have hfrac : (1 : ℝ) / (2 * (N : ℝ)) ≤ 1 := by
    have hden : (0 : ℝ) < 2 * (N : ℝ) := by positivity
    rw [div_le_one hden]
    have : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    nlinarith
  have hexpfrac : Real.exp (1 / (2 * (N : ℝ))) ≤ 3 :=
    (Real.exp_le_exp.mpr hfrac).trans Real.exp_one_lt_three.le
  have hsplit :
      Real.exp (((r : ℝ) + 1) / (2 * (N : ℝ))) =
        Real.exp ((r : ℝ) / (2 * (N : ℝ))) *
          Real.exp (1 / (2 * (N : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hPcExp : Real.exp ((r : ℝ) / (2 * (N : ℝ))) ≤ 2 * Pc := by
    simpa [N, Pc, sliceA2OrdinaryAnchor] using
      exp_cell_lower_le_two_anchor N r (by simpa [Pc] using hanchor)
  calc
    (sliceA2LadderP P0 ratio0 eta (j - 1) : ℝ) ≤
        Real.exp (((r : ℝ) + 1) / (2 * (N : ℝ))) := by
      simpa [N] using hlower
    _ = Real.exp ((r : ℝ) / (2 * (N : ℝ))) *
        Real.exp (1 / (2 * (N : ℝ))) := hsplit
    _ ≤ Real.exp ((r : ℝ) / (2 * (N : ℝ))) * 3 := by gcongr
    _ ≤ (2 * Pc) * 3 := by gcongr
    _ = 6 * (sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r : ℝ) := by
      dsimp [Pc]
      ring

/-- At logarithmic height at least `256`, adjoining the harmless factor two
costs at most one percent of an anchor logarithm. -/
theorem log_two_mul_le_one_point_zero_one_log
    (P : ℕ) (hlogP : 256 ≤ Real.log (P : ℝ)) :
    Real.log (2 * (P : ℝ)) ≤ (101 / 100 : ℝ) * Real.log (P : ℝ) := by
  have hPpos : (0 : ℝ) < P := by
    exact_mod_cast (show 0 < P by
      by_contra h
      have : P = 0 := Nat.eq_zero_of_not_pos h
      subst P
      norm_num at hlogP)
  have hlog2 : 100 * Real.log 2 ≤ Real.log (P : ℝ) := by
    have : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
    linarith
  rw [Real.log_mul (by norm_num) hPpos.ne']
  linarith

/-- Exponential weight used by the last ordinary level's cover moment. -/
noncomputable def sliceA2OrdinaryCoverWeight
    (P0 ratio0 eta J r : ℕ) (eps rho0 : ℝ) : ℝ :=
  Real.exp (-(innerBandScheduleAlpha (J - 1) * (r : ℝ) /
    ((2 * sliceA2OrdinaryN P0 ratio0 eta (J - 1)
      eps rho0 : ℕ) : ℝ)))

/-- The weight denominator in one ordinary cover moment has the stated
`0.404 log(2T) + 0.808 log P` bound. -/
theorem sliceA2OrdinaryCover_weightLoss_le
    (P0 ratio0 eta J r : ℕ) (eps rho0 T : ℝ)
    (hT : 1 ≤ T)
    (hanchor : 6 ≤ sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r)
    (hlogAnchor : 256 ≤ Real.log
      (sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r : ℝ)) :
    let P := sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r
    let ell := sliceA2OrdinaryCoverMoment P0 ratio0 eta J eps rho0 T r
    let V := sliceA2OrdinaryCoverWeight P0 ratio0 eta J r eps rho0
    (0 - 2 * (ell : ℝ)) * Real.log V ≤
      (101 / 250 : ℝ) * Real.log (2 * T) +
        (101 / 125 : ℝ) * Real.log (P : ℝ) := by
  dsimp only
  let P := sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r
  let ell := sliceA2OrdinaryCoverMoment P0 ratio0 eta J eps rho0 T r
  let N := sliceA2OrdinaryN P0 ratio0 eta (J - 1) eps rho0
  let alpha := innerBandScheduleAlpha (J - 1)
  let u := (r : ℝ) / (2 * (N : ℝ))
  let V := sliceA2OrdinaryCoverWeight P0 ratio0 eta J r eps rho0
  have hPtwo : 2 ≤ P := by dsimp [P]; omega
  have hlogPpos : 0 < Real.log (P : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hlogT0 : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
  have hell := adaptivePrimeMoment_cast_lt_log_ratio_add_two P T hPtwo hT
  have hell' : (ell : ℝ) <
      Real.log (2 * T) / Real.log (P : ℝ) + 2 := by
    simpa [ell, sliceA2OrdinaryCoverMoment] using hell
  have hellLog : (ell : ℝ) * Real.log (P : ℝ) ≤
      Real.log (2 * T) + 2 * Real.log (P : ℝ) := by
    calc
      (ell : ℝ) * Real.log (P : ℝ) ≤
          (Real.log (2 * T) / Real.log (P : ℝ) + 2) *
            Real.log (P : ℝ) :=
        mul_le_mul_of_nonneg_right hell'.le hlogPpos.le
      _ = Real.log (2 * T) + 2 * Real.log (P : ℝ) := by
        field_simp
  have halpha := innerBandScheduleAlpha_bounds (J - 1)
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (sliceA2OrdinaryN_pos P0 ratio0 eta (J - 1) eps rho0)
  have huExp : Real.exp u ≤ 2 * (P : ℝ) := by
    simpa [u, N, P, sliceA2OrdinaryAnchor] using
      exp_cell_lower_le_two_anchor N r (by
        simpa [P, sliceA2OrdinaryAnchor] using (show 1 ≤
          sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r by omega))
  have hu : u ≤ Real.log (2 * (P : ℝ)) := by
    calc
      u = Real.log (Real.exp u) := (Real.log_exp u).symm
      _ ≤ Real.log (2 * (P : ℝ)) := Real.log_le_log (Real.exp_pos u) huExp
  have hlog2P := log_two_mul_le_one_point_zero_one_log P hlogAnchor
  have hweight : -(2 * (ell : ℝ)) * Real.log V =
      2 * alpha * (ell : ℝ) * u := by
    dsimp [V, sliceA2OrdinaryCoverWeight]
    rw [Real.log_exp]
    dsimp [alpha, u, N]
    push_cast
    ring
  rw [show (0 - 2 * (ell : ℝ)) * Real.log V =
      -(2 * (ell : ℝ)) * Real.log V by ring, hweight]
  have hell0 : (0 : ℝ) ≤ ell := by positivity
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hlog2P0 : 0 ≤ Real.log (2 * (P : ℝ)) := by
    apply Real.log_nonneg
    have hPR : (2 : ℝ) ≤ P := by exact_mod_cast hPtwo
    nlinarith
  have hfirst : 2 * alpha * (ell : ℝ) * u ≤
      (2 / 5 : ℝ) * (ell : ℝ) * Real.log (2 * (P : ℝ)) := by
    have ha : 2 * alpha ≤ (2 : ℝ) / 5 := by linarith [halpha.2.le]
    have heu : (ell : ℝ) * u ≤
        (ell : ℝ) * Real.log (2 * (P : ℝ)) :=
      mul_le_mul_of_nonneg_left hu hell0
    calc
      2 * alpha * (ell : ℝ) * u =
          (2 * alpha) * ((ell : ℝ) * u) := by ring
      _ ≤ (2 / 5 : ℝ) * ((ell : ℝ) * u) :=
        mul_le_mul_of_nonneg_right ha (mul_nonneg hell0 hu0)
      _ ≤ (2 / 5 : ℝ) *
          ((ell : ℝ) * Real.log (2 * (P : ℝ))) :=
        mul_le_mul_of_nonneg_left heu (by norm_num)
      _ = (2 / 5 : ℝ) * (ell : ℝ) *
          Real.log (2 * (P : ℝ)) := by ring
  have hsecond : (2 / 5 : ℝ) * (ell : ℝ) *
      Real.log (2 * (P : ℝ)) ≤
      (101 / 250 : ℝ) * ((ell : ℝ) * Real.log (P : ℝ)) := by
    have hm := mul_le_mul_of_nonneg_left hlog2P hell0
    calc
      (2 / 5 : ℝ) * (ell : ℝ) * Real.log (2 * (P : ℝ)) =
          (2 / 5 : ℝ) * ((ell : ℝ) * Real.log (2 * (P : ℝ))) := by ring
      _ ≤ (2 / 5 : ℝ) *
          ((ell : ℝ) * ((101 / 100 : ℝ) * Real.log (P : ℝ))) := by
        gcongr
      _ = (101 / 250 : ℝ) *
          ((ell : ℝ) * Real.log (P : ℝ)) := by ring
  calc
    2 * alpha * (ell : ℝ) * u ≤
        (2 / 5 : ℝ) * (ell : ℝ) * Real.log (2 * (P : ℝ)) := hfirst
    _ ≤ (101 / 250 : ℝ) * ((ell : ℝ) * Real.log (P : ℝ)) := hsecond
    _ ≤ (101 / 250 : ℝ) *
        (Real.log (2 * T) + 2 * Real.log (P : ℝ)) := by gcongr
    _ = (101 / 250 : ℝ) * Real.log (2 * T) +
        (101 / 125 : ℝ) * Real.log (P : ℝ) := by ring

end Tao2015

end MoltResearch
