import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryMomentEnvelope

/-!
# Track R A2-V': ordinary not-too-far margin

The moment envelope grows only exponentially in the level index, whereas
the previous lower endpoint retains `P₀^(2^(j-1))`.  One fixed logarithmic
margin at `P₀` therefore supplies the schedule gap at every positive level.
-/

namespace MoltResearch

namespace Tao2015

/-- A convenient uniform cubic-versus-exponential estimate. -/
theorem nat_cube_le_128_mul_two_pow (j : ℕ) :
    j ^ 3 ≤ 128 * 2 ^ j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
      by_cases hj : j ≤ 4
      · interval_cases j <;> norm_num
      · have hj5 : 5 ≤ j := by omega
        have hprev := ih (j - 1) (by omega)
        have hcube : j ^ 3 ≤ 2 * (j - 1) ^ 3 := by
          have hj5z : (5 : ℤ) ≤ j := by exact_mod_cast hj5
          have hy : 0 ≤ (j : ℤ) - 5 := by omega
          have hy2 : 0 ≤ ((j : ℤ) - 5) ^ 2 := sq_nonneg _
          have hy3 : 0 ≤ ((j : ℤ) - 5) ^ 3 := pow_nonneg hy _
          have hcubeZ : (j : ℤ) ^ 3 ≤ 2 * ((j : ℤ) - 1) ^ 3 := by
            nlinarith
          have hsub : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
          have hcubeZ' : ((j ^ 3 : ℕ) : ℤ) ≤
              ((2 * (j - 1) ^ 3 : ℕ) : ℤ) := by
            push_cast
            rw [hsub]
            exact hcubeZ
          exact_mod_cast hcubeZ'
        calc
          j ^ 3 ≤ 2 * (j - 1) ^ 3 := hcube
          _ ≤ 2 * (128 * 2 ^ (j - 1)) := Nat.mul_le_mul_left 2 hprev
          _ = 128 * 2 ^ j := by
            have hjshape : j - 1 + 1 = j := by omega
            have hpowshape : 2 ^ j = 2 ^ (j - 1) * 2 := by
              calc
                2 ^ j = 2 ^ (j - 1 + 1) := congrArg (fun k : ℕ => 2 ^ k) hjshape.symm
                _ = 2 ^ (j - 1) * 2 := pow_succ _ _
            rw [hpowshape]
            ring

/-- Fixed coefficient controlling every ordinary moment envelope. -/
noncomputable def sliceA2OrdinaryFarCoefficient
    (ratio0 eta : ℕ) : ℝ :=
  204 * (2 + ratio0 + eta : ℕ) ^ 2

theorem sliceA2OrdinaryMomentEnvelope_le_farCoefficient
    (ratio0 eta j : ℕ) (hj : 0 < j) :
    sliceA2OrdinaryMomentEnvelope ratio0 eta j ≤
      sliceA2OrdinaryFarCoefficient ratio0 eta * (16 : ℝ) ^ j := by
  let M : ℕ := 2 + ratio0 + eta
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hjpow : j ≤ 2 ^ j := Nat.lt_two_pow_self.le
  have hj2 : (j : ℝ) ^ 2 ≤ ((2 : ℝ) ^ j) ^ 2 := by
    have : (j : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast hjpow
    nlinarith
  have hratioCur : (sliceA2LadderRatio ratio0 eta j : ℝ) ≤
      (M : ℝ) * (2 : ℝ) ^ j := by
    have hraw := sliceA2LadderRatio_le ratio0 eta j
    have hnat : 2 + ratio0 + 2 ^ j * eta ≤ M * 2 ^ j := by
      dsimp [M]
      have hpow : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by norm_num)
      nlinarith
    exact_mod_cast hraw.trans hnat
  have hratioPrev : (sliceA2LadderRatio ratio0 eta (j - 1) : ℝ) ≤
      (M : ℝ) * (2 : ℝ) ^ j := by
    have hraw := sliceA2LadderRatio_le ratio0 eta (j - 1)
    have hpow : 2 ^ (j - 1) ≤ 2 ^ j :=
      pow_le_pow_right' (by norm_num : 1 ≤ (2 : ℕ)) (by omega)
    have hnat : 2 + ratio0 + 2 ^ (j - 1) * eta ≤ M * 2 ^ j := by
      dsimp [M]
      have hjpow0 : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by norm_num)
      nlinarith
    exact_mod_cast hraw.trans hnat
  have hmain : 200 * (j : ℝ) ^ 2 *
      (sliceA2LadderRatio ratio0 eta (j - 1) : ℝ) *
      (sliceA2LadderRatio ratio0 eta j : ℝ) ≤
      200 * (M : ℝ) ^ 2 * (16 : ℝ) ^ j := by
    calc
      _ ≤ 200 * (((2 : ℝ) ^ j) ^ 2) *
          ((M : ℝ) * (2 : ℝ) ^ j) *
          ((M : ℝ) * (2 : ℝ) ^ j) := by gcongr
      _ = 200 * (M : ℝ) ^ 2 * (16 : ℝ) ^ j := by
        have h16 : (((2 : ℝ) ^ j) ^ 4) = (16 : ℝ) ^ j := by
          rw [← pow_mul]
          norm_num [show j * 4 = 4 * j by omega, pow_mul]
        rw [← h16]
        ring
  have hfour : (4 : ℝ) ≤ 4 * (M : ℝ) ^ 2 * (16 : ℝ) ^ j := by
    have hMsq : (1 : ℝ) ≤ (M : ℝ) ^ 2 := by exact_mod_cast one_le_pow₀ hM
    have h16 : (1 : ℝ) ≤ (16 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    nlinarith
  unfold sliceA2OrdinaryMomentEnvelope sliceA2OrdinaryFarCoefficient
  push_cast
  calc
    4 + 200 * (j : ℝ) ^ 2 *
        (sliceA2LadderRatio ratio0 eta (j - 1) : ℝ) *
        (sliceA2LadderRatio ratio0 eta j : ℝ) ≤
      4 * (M : ℝ) ^ 2 * (16 : ℝ) ^ j +
        200 * (M : ℝ) ^ 2 * (16 : ℝ) ^ j := add_le_add hfour hmain
    _ = 204 * (2 + ratio0 + eta : ℝ) ^ 2 * (16 : ℝ) ^ j := by
      dsimp [M]
      push_cast
      ring

/-- The logarithm of the moment envelope has a fixed affine bound in `j`. -/
theorem log_sliceA2OrdinaryMomentEnvelope_le
    (ratio0 eta j : ℕ) (hj : 0 < j) :
    Real.log (sliceA2OrdinaryMomentEnvelope ratio0 eta j) ≤
      Real.log (sliceA2OrdinaryFarCoefficient ratio0 eta) + 4 * j := by
  let C := sliceA2OrdinaryFarCoefficient ratio0 eta
  have hLpos : 0 < sliceA2OrdinaryMomentEnvelope ratio0 eta j :=
    lt_of_lt_of_le zero_lt_one
      (sliceA2OrdinaryMomentEnvelope_one_le ratio0 eta j)
  have hCpos : 0 < C := by
    dsimp [C, sliceA2OrdinaryFarCoefficient]
    positivity
  have hbound := sliceA2OrdinaryMomentEnvelope_le_farCoefficient ratio0 eta j hj
  have hlog := Real.log_le_log hLpos hbound
  have hlog16 : Real.log 16 ≤ 4 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    have hlog2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hlog2 ⊢
    nlinarith
  calc
    Real.log (sliceA2OrdinaryMomentEnvelope ratio0 eta j) ≤
        Real.log (C * (16 : ℝ) ^ j) := hlog
    _ = Real.log C + (j : ℝ) * Real.log 16 := by
      rw [Real.log_mul hCpos.ne' (by positivity), Real.log_pow]
    _ ≤ Real.log C + (j : ℝ) * 4 := by gcongr
    _ = Real.log (sliceA2OrdinaryFarCoefficient ratio0 eta) + 4 * j := by
      dsimp [C]
      ring

/-- One fixed bottom-log margin supplies the exact `Δα_j` condition at all
positive ordinary levels. -/
theorem sliceA2Ordinary_far_margin
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ)
    (hP0 : 21 ≤ P0) (hj : 0 < j)
    (hbottom :
      40960 * (2 * Real.log (sliceA2OrdinaryFarCoefficient ratio0 eta) + 11) ≤
        Real.log (P0 : ℝ))
    (r : ℕ) (hr : r ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1)) :
    (2 * Real.log (sliceA2OrdinaryMomentEnvelope ratio0 eta j) + 3) /
        Real.log (sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r : ℝ) ≤
      innerBandScheduleAlpha j - innerBandScheduleAlpha (j - 1) := by
  let C := sliceA2OrdinaryFarCoefficient ratio0 eta
  let L := sliceA2OrdinaryMomentEnvelope ratio0 eta j
  let Pc := sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r
  let Pprev := sliceA2LadderP P0 ratio0 eta (j - 1)
  let D := 2 * Real.log C + 11
  have hC1 : 1 ≤ C := by
    dsimp [C, sliceA2OrdinaryFarCoefficient]
    have hbase : (1 : ℝ) ≤ (2 + ratio0 + eta : ℕ) := by
      exact_mod_cast (show 1 ≤ 2 + ratio0 + eta by omega)
    have hbase2 : (1 : ℝ) ≤ ((2 + ratio0 + eta : ℕ) : ℝ) ^ 2 :=
      one_le_pow₀ hbase
    nlinarith
  have hlogC0 : 0 ≤ Real.log C := Real.log_nonneg hC1
  have hD0 : 0 ≤ D := by dsimp [D]; linarith
  have hlogL := log_sliceA2OrdinaryMomentEnvelope_le ratio0 eta j hj
  have hfactor : 2 * Real.log L + 3 ≤ D * j := by
    dsimp [L, D, C]
    have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith
  have hjcube := nat_cube_le_128_mul_two_pow j
  have hpoly : 40 * (j : ℝ) * ((j : ℝ) + 1) *
      (2 * Real.log L + 3) ≤ 10240 * D * (2 : ℝ) ^ j := by
    have hj1 : (j : ℝ) + 1 ≤ 2 * j := by exact_mod_cast (show j + 1 ≤ 2 * j by omega)
    have hjcubeR : (j : ℝ) ^ 3 ≤ 128 * (2 : ℝ) ^ j := by
      exact_mod_cast hjcube
    calc
      40 * (j : ℝ) * ((j : ℝ) + 1) * (2 * Real.log L + 3) ≤
          40 * (j : ℝ) * ((j : ℝ) + 1) * (D * j) := by
            exact mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ ≤ 40 * (j : ℝ) * (2 * j) * (D * j) := by gcongr
      _ = 80 * D * (j : ℝ) ^ 3 := by ring
      _ ≤ 80 * D * (128 * (2 : ℝ) ^ j) := by gcongr
      _ = 10240 * D * (2 : ℝ) ^ j := by ring
  have hPpower := sliceA2LadderP0_pow_two_pow_le
    P0 ratio0 eta (j - 1) (by omega)
  have hP00 : (0 : ℝ) < P0 := by exact_mod_cast (show 0 < P0 by omega)
  have hlogP0 : 0 < Real.log (P0 : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P0 by omega))
  have hlogPrev : (2 ^ (j - 1) : ℕ) * Real.log (P0 : ℝ) ≤
      Real.log (Pprev : ℝ) := by
    have hpowerR : (((P0 ^ (2 ^ (j - 1) : ℕ) : ℕ) : ℝ)) ≤
        (Pprev : ℝ) := by
      dsimp [Pprev]
      exact_mod_cast hPpower
    have hpow0 : (0 : ℝ) < ((P0 ^ (2 ^ (j - 1) : ℕ) : ℕ) : ℝ) := by
      positivity
    have hlog := Real.log_le_log hpow0 hpowerR
    rw [Nat.cast_pow, Real.log_pow] at hlog
    simpa [Pprev] using hlog
  have htwoShape : (2 : ℝ) ^ j = 2 * (2 ^ (j - 1) : ℕ) := by
    have hjshape : j - 1 + 1 = j := by omega
    calc
      (2 : ℝ) ^ j = (2 : ℝ) ^ (j - 1 + 1) :=
        congrArg (fun k : ℕ => (2 : ℝ) ^ k) hjshape.symm
      _ = (2 : ℝ) ^ (j - 1) * 2 := pow_succ _ _
      _ = 2 * (2 ^ (j - 1) : ℕ) := by push_cast; ring
  have hbottom' : 40960 * D ≤ Real.log (P0 : ℝ) := by
    simpa [D, C] using hbottom
  have htwice :
      2 * (40 * (j : ℝ) * ((j : ℝ) + 1) *
        (2 * Real.log L + 3)) ≤ Real.log (Pprev : ℝ) := by
    calc
      _ ≤ 2 * (10240 * D * (2 : ℝ) ^ j) := by gcongr
      _ = 40960 * D * (2 ^ (j - 1) : ℕ) := by rw [htwoShape]; ring
      _ ≤ Real.log (P0 : ℝ) * (2 ^ (j - 1) : ℕ) := by gcongr
      _ ≤ Real.log (Pprev : ℝ) := by simpa [mul_comm] using hlogPrev
  have hprevPc := sliceA2Ordinary_log_previous_le_two_log_anchor
    P0 ratio0 eta j eps rho0 hP0 hj r hr
  have htarget : 40 * (j : ℝ) * ((j : ℝ) + 1) *
      (2 * Real.log L + 3) ≤ Real.log (Pc : ℝ) := by
    dsimp [Pprev, Pc] at hprevPc htwice ⊢
    linarith
  have hPc6 := sliceA2Ordinary_anchor_six
    P0 ratio0 eta j eps rho0 hP0 hj r hr
  have hPcOne : 1 < Pc := by dsimp [Pc]; omega
  have hlogPc : 0 < Real.log (Pc : ℝ) :=
    Real.log_pos (by exact_mod_cast hPcOne)
  rw [innerBandScheduleAlpha_gap j hj]
  rw [div_le_div_iff₀ hlogPc (by positivity :
    (0 : ℝ) < 40 * (j : ℝ) * ((j : ℝ) + 1))]
  simpa [L, Pc, mul_assoc, mul_left_comm, mul_comm] using htarget

end Tao2015

end MoltResearch
