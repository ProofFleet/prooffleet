import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5LadderNumerology
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5InnerBandScheduleSharpFit

/-!
# Track R L3-1: ordinary-ladder numerology

This file records the exact margins used by the later ordinary levels.  The
schedule exponent is

`alpha j = 1/5 - 1/(40*(j+1))`,

so its increment at `j > 0` is `1/(40*j*(j+1))`.  The jump
`P_j = Q_{j-1}^{100*j^2}` therefore leaves at least the advertised
`Q_{j-1}^{-0.45}` after the borrowed previous-cell factor.  It also records
the uniform subdivision of the main-leg share and the tighter shifted level
share required by L3-0.
-/

namespace MoltResearch

namespace Tao2015

/-- Lower e-adic index used for a level with lower prime endpoint `P`. -/
noncomputable def ordinaryLevelIndexLower (P N : ℕ) : ℕ :=
  ⌈2 * (N : ℝ) * Real.log P⌉₊ - 1

/-- A scale which is `q` on the useful occupied cells up to taking a maximum,
and remains at least the level endpoint on empty cells. -/
noncomputable def ordinaryCurrentScale (P q : ℕ) : ℕ := max P q

/-- Every index above the scheduled lower index has upper e-adic endpoint at
least `P`. -/
theorem ordinaryLevel_lower_le_exp_upper
    (P N v : ℕ) (hP : 1 ≤ P) (hN : 0 < N)
    (hv : ordinaryLevelIndexLower P N ≤ v) :
    (P : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ))) := by
  have hceilv : ⌈2 * (N : ℝ) * Real.log P⌉₊ ≤ v + 1 := by
    unfold ordinaryLevelIndexLower at hv
    omega
  have hraw : 2 * (N : ℝ) * Real.log P ≤ (v : ℝ) + 1 := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast hceilv)
  have hN0 : (0 : ℝ) < 2 * (N : ℝ) := by positivity
  have hlog : Real.log P ≤ ((v : ℝ) + 1) / (2 * (N : ℝ)) := by
    apply (le_div_iff₀ hN0).2
    nlinarith
  calc
    (P : ℝ) = Real.exp (Real.log P) := by
      rw [Real.exp_log (by exact_mod_cast (show 0 < P by omega))]
    _ ≤ _ := Real.exp_le_exp.mpr hlog

/-- The max scale inherits the cell upper bound while being at least the
fixed lower endpoint. -/
theorem ordinaryCurrentScale_bounds
    (P q N v : ℕ) (hP : 1 ≤ P) (hN : 0 < N)
    (hv : ordinaryLevelIndexLower P N ≤ v)
    (hqup : (q : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ)))) :
    P ≤ ordinaryCurrentScale P q ∧
      (ordinaryCurrentScale P q : ℝ) ≤
        Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ))) := by
  constructor
  · exact le_max_left _ _
  · unfold ordinaryCurrentScale
    rw [Nat.cast_max]
    exact max_le (ordinaryLevel_lower_le_exp_upper P N v hP hN hv) hqup

/-- Converting current-cell smallness to a power of any scale below the cell's
upper endpoint.  This works for occupied and empty cells alike. -/
theorem current_cell_smallness_le_scale_power
    (alpha : ℝ) (halpha : 0 ≤ alpha) (N v t : ℕ) (hN : 0 < N)
    (ht : 1 ≤ t)
    (htop : (t : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ)))) :
    Real.exp (-(alpha * (v : ℝ) / ((2 * N : ℕ) : ℝ))) ^ 2 ≤
      Real.exp (alpha / (N : ℝ)) * (t : ℝ) ^ (-(2 * alpha)) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hlog := (Real.log_le_iff_le_exp ht0).2 htop
  rw [Real.rpow_def_of_pos ht0]
  rw [← Real.exp_add]
  have hcast : (((2 * N : ℕ) : ℝ)) = 2 * (N : ℝ) := by push_cast; ring
  have hmul := mul_le_mul_of_nonneg_left hlog
    (by positivity : (0 : ℝ) ≤ 2 * alpha)
  have hshape :
      2 * alpha * (((v : ℝ) + 1) / (2 * (N : ℝ))) =
        alpha * (v : ℝ) / (N : ℝ) + alpha / (N : ℝ) := by
    field_simp
  have hleft :
      -(alpha * (v : ℝ) / (2 * (N : ℝ))) +
          -(alpha * (v : ℝ) / (2 * (N : ℝ))) =
        -(alpha * (v : ℝ) / (N : ℝ)) := by
    field_simp
    ring
  calc
    Real.exp (-(alpha * (v : ℝ) / ((2 * N : ℕ) : ℝ))) ^ 2 =
        Real.exp (-(alpha * (v : ℝ) / (2 * (N : ℝ))) +
          -(alpha * (v : ℝ) / (2 * (N : ℝ)))) := by
            rw [hcast, pow_two, ← Real.exp_add]
    _ ≤ Real.exp (alpha / (N : ℝ) + Real.log (t : ℝ) * -(2 * alpha)) := by
      apply Real.exp_le_exp.mpr
      rw [hshape] at hmul
      rw [hleft]
      nlinarith

/-- Moment order borrowed from a previous ordinary cell. -/
noncomputable def ordinaryBorrowMoment (P : ℕ) (x : ℝ) : ℕ :=
  ⌈Real.log x / Real.log P⌉₊ + 1

theorem ordinaryBorrowMoment_one_le (P : ℕ) (x : ℝ) :
    1 ≤ ordinaryBorrowMoment P x := by
  unfold ordinaryBorrowMoment
  omega

/-- Minimality of the borrowed moment, in the upper-bound direction needed
for the previous-cell loss. -/
theorem pow_borrowMoment_lt
    (P : ℕ) (hP : 2 ≤ P) (x : ℝ) (hx : 1 ≤ x) :
    ((P ^ ordinaryBorrowMoment P x : ℕ) : ℝ) < (P : ℝ) ^ 2 * x := by
  have hP0 : (0 : ℝ) < P := by positivity
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hy0 : 0 ≤ Real.log x / Real.log P := by
    exact div_nonneg (Real.log_nonneg hx) hlogP.le
  have hceil := Nat.ceil_lt_add_one hy0
  have hell : (ordinaryBorrowMoment P x : ℝ) <
      Real.log x / Real.log P + 2 := by
    unfold ordinaryBorrowMoment
    push_cast
    linarith
  have hlog : (ordinaryBorrowMoment P x : ℝ) * Real.log P <
      Real.log x + 2 * Real.log P := by
    have := mul_lt_mul_of_pos_right hell hlogP
    field_simp at this
    nlinarith
  have hexp := Real.exp_lt_exp.mpr hlog
  have hleft : Real.exp ((ordinaryBorrowMoment P x : ℝ) * Real.log P) =
      (P : ℝ) ^ ordinaryBorrowMoment P x := by
    rw [show (ordinaryBorrowMoment P x : ℝ) * Real.log (P : ℝ) =
        (ordinaryBorrowMoment P x : ℕ) * Real.log (P : ℝ) by norm_cast,
      Real.exp_nat_mul, Real.exp_log hP0]
  have hright : Real.exp (Real.log x + 2 * Real.log P) =
      x * (P : ℝ) ^ 2 := by
    rw [Real.exp_add, Real.exp_log hx0,
      show 2 * Real.log (P : ℝ) = (2 : ℕ) * Real.log (P : ℝ) by norm_num,
      Real.exp_nat_mul, Real.exp_log hP0]
  rw [hleft, hright] at hexp
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  simpa [mul_comm] using hexp

/-- If the time ratio used to choose the moment is at most the current cell
scale, then the moment is at most `log t / log P + 2`. -/
theorem ordinaryBorrowMoment_le_log_scale
    (P : ℕ) (hP : 2 ≤ P) (x t : ℝ) (hx : 1 ≤ x) (hxt : x ≤ t) :
    (ordinaryBorrowMoment P x : ℝ) ≤ Real.log t / Real.log P + 2 := by
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have ht0 : 0 < t := hx0.trans_le hxt
  have hlogxt : Real.log x ≤ Real.log t := Real.log_le_log hx0 hxt
  have hdiv : Real.log x / Real.log P ≤ Real.log t / Real.log P := by gcongr
  have hy0 : 0 ≤ Real.log x / Real.log P :=
    div_nonneg (Real.log_nonneg hx) hlogP.le
  have hceil := Nat.ceil_lt_add_one hy0
  unfold ordinaryBorrowMoment
  push_cast
  linarith

/-- The exponential moment envelope separates into a fixed factor and one
small power of the current scale. -/
theorem exp_borrowMoment_le_scale_power
    (P : ℕ) (hP : 2 ≤ P) (x t c : ℝ) (hx : 1 ≤ x) (hxt : x ≤ t)
    (hc : 0 ≤ c) :
    Real.exp ((ordinaryBorrowMoment P x : ℝ) * c + 10) ≤
      Real.exp (2 * c + 10) * t ^ (c / Real.log P) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by linarith : 0 < x) hxt
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hell := ordinaryBorrowMoment_le_log_scale P hP x t hx hxt
  have hmul := mul_le_mul_of_nonneg_right hell hc
  rw [Real.rpow_def_of_pos ht0, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  field_simp at hmul ⊢
  nlinarith

/-- The "not too far" condition converts all current-scale powers into the
gain `Pcur^-(alpha-beta)`. -/
theorem ordinary_current_scale_power_saving
    (Pcur t : ℝ) (hPcur : 1 ≤ Pcur) (hPt : Pcur ≤ t)
    (alpha beta c logPprev : ℝ) (hgap : 0 ≤ alpha - beta)
    (hfar : c / logPprev ≤ alpha - beta) :
    t ^ (-(2 * alpha)) * t ^ (2 * beta) * t ^ (c / logPprev) ≤
      Pcur ^ (-(alpha - beta)) := by
  have ht : 1 ≤ t := hPcur.trans hPt
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hPcur0 : 0 < Pcur := lt_of_lt_of_le (by norm_num) hPcur
  have hexp : -(2 * alpha) + 2 * beta + c / logPprev ≤
      -(alpha - beta) := by linarith
  calc
    t ^ (-(2 * alpha)) * t ^ (2 * beta) * t ^ (c / logPprev) =
        t ^ (-(2 * alpha) + 2 * beta + c / logPprev) := by
          rw [← Real.rpow_add ht0, ← Real.rpow_add ht0]
    _ ≤ t ^ (-(alpha - beta)) :=
      Real.rpow_le_rpow_of_exponent_le ht hexp
    _ ≤ Pcur ^ (-(alpha - beta)) :=
      Real.rpow_le_rpow_of_nonpos hPcur0 hPt (by linarith)

/-- The previous-cell largeness denominator is controlled by the integral
lower anchor of that cell. -/
theorem inverse_previous_threshold_le_anchor
    (beta : ℝ) (hbeta : 0 ≤ beta) (N r ell P : ℕ) (hN : 0 < N)
    (hP : 1 ≤ P)
    (hexp : Real.exp ((r : ℝ) / (2 * (N : ℝ))) ≤ 2 * (P : ℝ)) :
    1 / Real.exp (-(beta * (r : ℝ) / ((2 * N : ℕ) : ℝ))) ^ (2 * ell) ≤
      (2 * (P : ℝ)) ^ (2 * beta * (ell : ℝ)) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h2P : (0 : ℝ) < 2 * (P : ℝ) := by positivity
  have hlog : (r : ℝ) / (2 * (N : ℝ)) ≤ Real.log (2 * (P : ℝ)) :=
    (Real.le_log_iff_exp_le h2P).2 hexp
  have hcoef : 0 ≤ 2 * beta * (ell : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hlog hcoef
  have hcast : (((2 * N : ℕ) : ℝ)) = 2 * (N : ℝ) := by push_cast; ring
  have hleft :
      1 / Real.exp (-(beta * (r : ℝ) / ((2 * N : ℕ) : ℝ))) ^
          (2 * ell) =
        Real.exp (((r : ℝ) / (2 * (N : ℝ))) *
          (2 * beta * (ell : ℝ))) := by
    rw [← Real.exp_nat_mul]
    rw [one_div, ← Real.exp_neg]
    congr 1
    rw [hcast]
    push_cast
    ring
  rw [hleft, Real.rpow_def_of_pos h2P]
  exact Real.exp_le_exp.mpr hmul

/-- Full previous-cell loss after the minimal borrowed moment is inserted. -/
theorem inverse_previous_threshold_le_borrow
    (beta : ℝ) (hbeta : 0 ≤ beta) (N r P : ℕ) (hN : 0 < N)
    (hP : 2 ≤ P) (x : ℝ) (hx : 1 ≤ x)
    (hexp : Real.exp ((r : ℝ) / (2 * (N : ℝ))) ≤ 2 * (P : ℝ)) :
    1 / Real.exp (-(beta * (r : ℝ) / ((2 * N : ℕ) : ℝ))) ^
          (2 * ordinaryBorrowMoment P x) ≤
      (4 : ℝ) ^ (beta * (ordinaryBorrowMoment P x : ℝ)) *
        (P : ℝ) ^ (4 * beta) * x ^ (2 * beta) := by
  let ell := ordinaryBorrowMoment P x
  have hraw := inverse_previous_threshold_le_anchor beta hbeta N r ell P hN
    (by omega) hexp
  have hpow := (pow_borrowMoment_lt P hP x hx).le
  have hpow0 : (0 : ℝ) ≤ ((P ^ ell : ℕ) : ℝ) := by positivity
  have hpowR : ((P ^ ell : ℕ) : ℝ) ^ (2 * beta) ≤
      ((P : ℝ) ^ 2 * x) ^ (2 * beta) :=
    Real.rpow_le_rpow hpow0 hpow (by positivity)
  have hP0 : (0 : ℝ) < P := by positivity
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have htwoP : (0 : ℝ) < 2 * (P : ℝ) := by positivity
  have hsplit :
      (2 * (P : ℝ)) ^ (2 * beta * (ell : ℝ)) =
        (4 : ℝ) ^ (beta * (ell : ℝ)) *
          ((P ^ ell : ℕ) : ℝ) ^ (2 * beta) := by
    rw [Real.rpow_def_of_pos htwoP,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4),
      Real.rpow_def_of_pos (by positivity : (0 : ℝ) < ((P ^ ell : ℕ) : ℝ)),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hP0.ne',
      show Real.log (4 : ℝ) = 2 * Real.log 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num,
      show Real.log (((P ^ ell : ℕ) : ℝ)) =
          (ell : ℝ) * Real.log P by
        norm_num only [Nat.cast_pow, Nat.cast_ofNat]; rw [Real.log_pow]]
    rw [← Real.exp_add]
    congr 1
    ring
  have htarget :
      ((P : ℝ) ^ 2 * x) ^ (2 * beta) =
        (P : ℝ) ^ (4 * beta) * x ^ (2 * beta) := by
    rw [Real.mul_rpow (sq_nonneg _) hx0.le, ← Real.rpow_natCast (P : ℝ) 2,
      ← Real.rpow_mul hP0.le]
    congr 2
    ring
  calc
    1 / Real.exp (-(beta * (r : ℝ) / ((2 * N : ℕ) : ℝ))) ^
          (2 * ordinaryBorrowMoment P x)
        ≤ (2 * (P : ℝ)) ^ (2 * beta * (ell : ℝ)) := hraw
    _ = (4 : ℝ) ^ (beta * (ell : ℝ)) *
          ((P ^ ell : ℕ) : ℝ) ^ (2 * beta) := hsplit
    _ ≤ (4 : ℝ) ^ (beta * (ell : ℝ)) *
          ((P : ℝ) ^ 2 * x) ^ (2 * beta) := by gcongr
    _ = (4 : ℝ) ^ (beta * (ordinaryBorrowMoment P x : ℝ)) *
          (P : ℝ) ^ (4 * beta) * x ^ (2 * beta) := by
      rw [htarget]
      dsimp [ell]
      ring

/-- Closed form of the zero-indexed `[mrt]` band exponent. -/
theorem innerBandScheduleAlpha_eq (j : ℕ) :
    innerBandScheduleAlpha j =
      (1 : ℝ) / 5 - 1 / (40 * ((j : ℝ) + 1)) := by
  unfold innerBandScheduleAlpha scheduleAlpha
  push_cast
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Exact increment between two consecutive ordinary ladder exponents. -/
theorem innerBandScheduleAlpha_gap (j : ℕ) (hj : 0 < j) :
    innerBandScheduleAlpha j - innerBandScheduleAlpha (j - 1) =
      1 / (40 * (j : ℝ) * ((j : ℝ) + 1)) := by
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
  rw [innerBandScheduleAlpha_eq, innerBandScheduleAlpha_eq]
  have hsub : (((j - 1 : ℕ) : ℝ) + 1) = (j : ℝ) := by
    exact_mod_cast (by omega : (j - 1 : ℕ) + 1 = j)
  rw [hsub]
  field_simp
  ring

/-- The scheduled exponents stay in the interval `(0,1/5)`. -/
theorem innerBandScheduleAlpha_bounds (j : ℕ) :
    0 < innerBandScheduleAlpha j ∧ innerBandScheduleAlpha j < (1 : ℝ) / 5 := by
  rw [innerBandScheduleAlpha_eq]
  have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by
    exact_mod_cast (Nat.le_add_left 1 j)
  have hden : (0 : ℝ) < 40 * ((j : ℝ) + 1) := by positivity
  constructor
  · have : 1 / (40 * ((j : ℝ) + 1)) ≤ (1 : ℝ) / 40 := by
      apply one_div_le_one_div_of_le (by norm_num) (by nlinarith)
    linarith
  · linarith [one_div_pos.mpr hden]

/-- The `100*j²` gap leaves more than `0.45` powers of the previous
upper endpoint, uniformly for every later level. -/
theorem ordinary_ladder_not_too_close (j : ℕ) (hj : 0 < j) :
    4 * innerBandScheduleAlpha (j - 1) -
        100 * (j : ℝ) ^ 2 *
          (innerBandScheduleAlpha j - innerBandScheduleAlpha (j - 1)) ≤
      -(9 : ℝ) / 20 := by
  rw [innerBandScheduleAlpha_gap j hj, innerBandScheduleAlpha_eq]
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hsub : (((j - 1 : ℕ) : ℝ) + 1) = (j : ℝ) := by
    exact_mod_cast (by omega : (j - 1 : ℕ) + 1 = j)
  rw [hsub]
  have hdenj : (j : ℝ) ≠ 0 := ne_of_gt hjR
  have hdenj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  nlinarith

/-- Power form of `ordinary_ladder_not_too_close`.  This is the exact
`P_j^{-Δα_j} Q_{j-1}^{4α_{j-1}} ≤ Q_{j-1}^{-0.45}` saving used
after setting `P_j = Q_{j-1}^{100*j²}`. -/
theorem ordinary_ladder_power_saving (Q : ℝ) (hQ : 1 ≤ Q)
    (j : ℕ) (hj : 0 < j) :
    (Q ^ (100 * j ^ 2) : ℝ) ^
          (-(innerBandScheduleAlpha j - innerBandScheduleAlpha (j - 1))) *
        Q ^ (4 * innerBandScheduleAlpha (j - 1)) ≤
      Q ^ (-(9 : ℝ) / 20) := by
  have hQ0 : 0 ≤ Q := le_trans (by norm_num) hQ
  have hQpos : 0 < Q := lt_of_lt_of_le (by norm_num) hQ
  rw [← Real.rpow_natCast Q (100 * j ^ 2), ← Real.rpow_mul hQ0,
    ← Real.rpow_add hQpos]
  apply Real.rpow_le_rpow_of_exponent_le hQ
  have hcast : ((100 * j ^ 2 : ℕ) : ℝ) = 100 * (j : ℝ) ^ 2 := by
    push_cast
    ring
  rw [hcast]
  nlinarith [ordinary_ladder_not_too_close j hj]

/-- Elementary factorial/power envelope occurring in one later-level cell. -/
noncomputable def ordinaryLadderMomentCore
    (ell : ℕ) (mass u : ℝ) : ℝ :=
  Real.exp Real.pi *
      (u + 2 * ((2 ^ (ell + 1) : ℕ) : ℝ)) *
    ((Nat.factorial ell : ℝ) ^ 2 *
      (((2 ^ (ell + 1) : ℕ) : ℝ) * ((ell : ℝ) + 1) * mass ^ ell))

private theorem nat_succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      omega

/-- The factorial and dyadic factors cost at most
`exp(pi) * 2^(3ell+4) * L^(2ell)`. -/
theorem ordinaryLadderMomentCore_le
    (ell : ℕ) (hell : 1 ≤ ell) (mass u L : ℝ)
    (hmass0 : 0 ≤ mass) (hmass : mass ≤ 1)
    (hu : u ≤ 1)
    (hL : (ell : ℝ) ≤ L) :
    ordinaryLadderMomentCore ell mass u ≤
      Real.exp Real.pi * (2 : ℝ) ^ (3 * ell + 4) * L ^ (2 * ell) := by
  have hfirst :
      u + 2 * ((2 ^ (ell + 1) : ℕ) : ℝ) ≤
        ((2 ^ (ell + 3) : ℕ) : ℝ) := by
    have hnat : 1 + 2 * 2 ^ (ell + 1) ≤ 2 ^ (ell + 3) := by
      have hone : 1 ≤ 2 * 2 ^ (ell + 1) := by
        exact Nat.one_le_iff_ne_zero.mpr (by positivity)
      calc
        1 + 2 * 2 ^ (ell + 1) ≤ 2 * 2 ^ (ell + 1) + 2 * 2 ^ (ell + 1) := by
          omega
        _ = 2 ^ (ell + 3) := by
          rw [show ell + 3 = (ell + 1) + 2 by omega, pow_add]
          norm_num
          ring
    calc
      u + 2 * ((2 ^ (ell + 1) : ℕ) : ℝ) ≤
          1 + 2 * ((2 ^ (ell + 1) : ℕ) : ℝ) := by linarith
      _ ≤ ((2 ^ (ell + 3) : ℕ) : ℝ) := by exact_mod_cast hnat
  have hfacNat := Nat.factorial_le_pow ell
  have hfac : (Nat.factorial ell : ℝ) ^ 2 ≤ (ell : ℝ) ^ (2 * ell) := by
    have hcast : (Nat.factorial ell : ℝ) ≤ (ell : ℝ) ^ ell := by
      exact_mod_cast hfacNat
    calc
      (Nat.factorial ell : ℝ) ^ 2 ≤ ((ell : ℝ) ^ ell) ^ 2 := by gcongr
      _ = (ell : ℝ) ^ (2 * ell) := by
        rw [← pow_mul]
        congr 1
        omega
  have hmassPow : mass ^ ell ≤ 1 := pow_le_one₀ hmass0 hmass
  have hsucc : (ell : ℝ) + 1 ≤ (2 : ℝ) ^ ell := by
    exact_mod_cast nat_succ_le_two_pow ell
  have hlast :
      (((2 ^ (ell + 1) : ℕ) : ℝ) * ((ell : ℝ) + 1) * mass ^ ell) ≤
        (2 : ℝ) ^ (2 * ell + 1) := by
    calc
      (((2 ^ (ell + 1) : ℕ) : ℝ) * ((ell : ℝ) + 1) * mass ^ ell)
          ≤ (2 : ℝ) ^ (ell + 1) * (2 : ℝ) ^ ell * 1 := by
            norm_num only [Nat.cast_pow, Nat.cast_ofNat]
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left hsucc (by positivity)) hmassPow
              (pow_nonneg hmass0 ell) (by positivity)
      _ = (2 : ℝ) ^ (2 * ell + 1) := by
        rw [mul_one, ← pow_add]
        congr 1
        omega
  have hL0 : 0 ≤ L := le_trans (by positivity : (0 : ℝ) ≤ ell) hL
  have hellL : (ell : ℝ) ^ (2 * ell) ≤ L ^ (2 * ell) :=
    pow_le_pow_left₀ (by positivity) hL _
  have hfirst' :
      u + 2 * ((2 ^ (ell + 1) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (ell + 3) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hfirst
  unfold ordinaryLadderMomentCore
  calc
    Real.exp Real.pi *
          (u + 2 * ((2 ^ (ell + 1) : ℕ) : ℝ)) *
        ((Nat.factorial ell : ℝ) ^ 2 *
          (((2 ^ (ell + 1) : ℕ) : ℝ) * ((ell : ℝ) + 1) * mass ^ ell))
        ≤ Real.exp Real.pi * (2 : ℝ) ^ (ell + 3) *
            ((ell : ℝ) ^ (2 * ell) * (2 : ℝ) ^ (2 * ell + 1)) := by
          gcongr
    _ ≤ Real.exp Real.pi * (2 : ℝ) ^ (ell + 3) *
            (L ^ (2 * ell) * (2 : ℝ) ^ (2 * ell + 1)) := by
          gcongr
    _ = Real.exp Real.pi * (2 : ℝ) ^ (3 * ell + 4) * L ^ (2 * ell) := by
          calc
            Real.exp Real.pi * (2 : ℝ) ^ (ell + 3) *
                (L ^ (2 * ell) * (2 : ℝ) ^ (2 * ell + 1)) =
              Real.exp Real.pi *
                ((2 : ℝ) ^ (ell + 3) * (2 : ℝ) ^ (2 * ell + 1)) *
                  L ^ (2 * ell) := by ring
            _ = Real.exp Real.pi * (2 : ℝ) ^ (3 * ell + 4) *
                  L ^ (2 * ell) := by
              rw [← pow_add]
              congr 3
              omega

/-- Exponential form of the preceding envelope, with the constants used in
the L3 brief. -/
theorem ordinaryLadderMomentCore_le_exp
    (ell : ℕ) (hell : 1 ≤ ell) (mass u L : ℝ)
    (hmass0 : 0 ≤ mass) (hmass : mass ≤ 1)
    (hu : u ≤ 1)
    (hLell : (ell : ℝ) ≤ L) (hL : 1 ≤ L) :
    ordinaryLadderMomentCore ell mass u ≤
      Real.exp ((ell : ℝ) * (2 * Real.log L + 3) + 10) := by
  refine (ordinaryLadderMomentCore_le ell hell mass u L hmass0 hmass hu hLell).trans ?_
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have htwo : (2 : ℝ) ^ (3 * ell + 4) =
      Real.exp (((3 * ell + 4 : ℕ) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hLpow : L ^ (2 * ell) =
      Real.exp (((2 * ell : ℕ) : ℝ) * Real.log L) := by
    rw [Real.exp_nat_mul, Real.exp_log hL0]
  rw [htwo, hLpow, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  push_cast
  nlinarith

/-- The `4^(βℓ)` loss from comparing the previous-cell threshold with
its integral anchor still fits inside the same exponent `2 log L + 3`. -/
theorem four_rpow_mul_ordinaryLadderMomentCore_le_exp
    (ell : ℕ) (hell : 1 ≤ ell) (mass u L beta : ℝ)
    (hmass0 : 0 ≤ mass) (hmass : mass ≤ 1) (hu : u ≤ 1)
    (hLell : (ell : ℝ) ≤ L) (hL : 1 ≤ L)
    (hbeta : beta ≤ (1 : ℝ) / 5) :
    (4 : ℝ) ^ (beta * (ell : ℝ)) *
        ordinaryLadderMomentCore ell mass u ≤
      Real.exp ((ell : ℝ) * (2 * Real.log L + 3) + 10) := by
  have hcore := ordinaryLadderMomentCore_le ell hell mass u L
    hmass0 hmass hu hLell
  have hfour0 : 0 ≤ (4 : ℝ) ^ (beta * (ell : ℝ)) := by positivity
  refine (mul_le_mul_of_nonneg_left hcore hfour0).trans ?_
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hlog2 : Real.log (2 : ℝ) < 0.7 := by
    linarith [Real.log_two_lt_d9]
  have hlog20 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hell0 : (0 : ℝ) ≤ ell := by positivity
  have hbetal : beta * (ell : ℝ) ≤ (1 / 5 : ℝ) * ell := by
    gcongr
  have hbetaLog :
      2 * Real.log 2 * (beta * (ell : ℝ)) ≤ (7 : ℝ) / 25 * ell := by
    calc
      2 * Real.log 2 * (beta * (ell : ℝ)) ≤
          2 * Real.log 2 * ((1 / 5 : ℝ) * ell) := by
            exact mul_le_mul_of_nonneg_left hbetal (by positivity)
      _ ≤ (7 : ℝ) / 25 * ell := by nlinarith
  have hdyadic :
      (((3 * ell + 4 : ℕ) : ℝ) * Real.log 2) ≤
        (21 : ℝ) / 10 * ell + 14 / 5 := by
    have hn : (0 : ℝ) ≤ ((3 * ell + 4 : ℕ) : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hlog2.le hn
    push_cast at this ⊢
    nlinarith
  have htwo : (2 : ℝ) ^ (3 * ell + 4) =
      Real.exp (((3 * ell + 4 : ℕ) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hLpow : L ^ (2 * ell) =
      Real.exp (((2 * ell : ℕ) : ℝ) * Real.log L) := by
    rw [Real.exp_nat_mul, Real.exp_log hL0]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4), htwo, hLpow,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [hlog4]
  push_cast
  nlinarith

/-- The literal per-`(r,v)` expression in `innerBand_later_level_main_cells`. -/
noncomputable def ordinaryLadderCellRaw
    (Ncur Nprev v r Pmom : ℕ) (alpha beta mass u x : ℝ) : ℝ :=
  let ell := ordinaryBorrowMoment Pmom x
  Real.exp (-(alpha * (v : ℝ) / ((2 * Ncur : ℕ) : ℝ))) ^ 2 /
      Real.exp (-(beta * (r : ℝ) / ((2 * Nprev : ℕ) : ℝ))) ^ (2 * ell) *
    ordinaryLadderMomentCore ell mass u

/-- Unfolding the abbreviation gives literally the summand required by
`innerBand_later_level_main_cells`. -/
theorem ordinaryLadderCellRaw_eq
    (Ncur Nprev v r Pmom : ℕ) (alpha beta mass u x : ℝ) :
    ordinaryLadderCellRaw Ncur Nprev v r Pmom alpha beta mass u x =
      Real.exp (-(alpha * (v : ℝ) / ((2 * Ncur : ℕ) : ℝ))) ^ 2 /
          Real.exp (-(beta * (r : ℝ) / ((2 * Nprev : ℕ) : ℝ))) ^
            (2 * ordinaryBorrowMoment Pmom x) *
        (Real.exp Real.pi *
          (u + 2 * ((2 ^ (ordinaryBorrowMoment Pmom x + 1) : ℕ) : ℝ)) *
          ((Nat.factorial (ordinaryBorrowMoment Pmom x) : ℝ) ^ 2 *
            (((2 ^ (ordinaryBorrowMoment Pmom x + 1) : ℕ) : ℝ) *
              ((ordinaryBorrowMoment Pmom x : ℝ) + 1) *
                mass ^ ordinaryBorrowMoment Pmom x))) := by
  rfl

/-- The eight elementary estimates of L3-1 compressed for one current cell.
The only surviving scale dependence is the fixed exponential constant, the
window ratio `tau^(2 beta)`, and
`Qprev^(4 beta) * Pcur^-(alpha-beta)`. -/
theorem ordinaryLadderCellRaw_le
    (Ncur Nprev v r Pmom : ℕ) (hNcur : 0 < Ncur) (hNprev : 0 < Nprev)
    (hPmom : 2 ≤ Pmom)
    (Pcur t : ℕ) (Qprev tau alpha beta mass u L : ℝ)
    (hPcur : 1 ≤ Pcur) (hPt : Pcur ≤ t)
    (hPmomQ : (Pmom : ℝ) ≤ Qprev)
    (htop : (t : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (Ncur : ℝ))))
    (hexpPrev : Real.exp ((r : ℝ) / (2 * (Nprev : ℝ))) ≤
      2 * (Pmom : ℝ))
    (htau0 : 0 ≤ tau) (htau : tau ≤ 1) (hx : 1 ≤ (t : ℝ) * tau)
    (halpha : 0 ≤ alpha) (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (1 : ℝ) / 5) (hgap : 0 ≤ alpha - beta)
    (hmass0 : 0 ≤ mass) (hmass : mass ≤ 1) (hu0 : 0 ≤ u) (hu : u ≤ 1)
    (hL : 1 ≤ L)
    (hellL : (ordinaryBorrowMoment Pmom ((t : ℝ) * tau) : ℝ) ≤ L)
    (hfar : (2 * Real.log L + 3) / Real.log Pmom ≤ alpha - beta) :
    ordinaryLadderCellRaw Ncur Nprev v r Pmom alpha beta mass u ((t : ℝ) * tau) ≤
      Real.exp (alpha / (Ncur : ℝ) + 2 * (2 * Real.log L + 3) + 10) *
        tau ^ (2 * beta) * Qprev ^ (4 * beta) *
          (Pcur : ℝ) ^ (-(alpha - beta)) := by
  let x : ℝ := (t : ℝ) * tau
  let ell : ℕ := ordinaryBorrowMoment Pmom x
  let c : ℝ := 2 * Real.log L + 3
  have ht : 1 ≤ t := hPcur.trans hPt
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hx1 : 1 ≤ x := by simpa [x] using hx
  have hxt : x ≤ (t : ℝ) := by
    dsimp [x]
    nlinarith [mul_le_mul_of_nonneg_left htau ht0.le]
  have hPmom0 : (0 : ℝ) < Pmom := by positivity
  have hQprev0 : 0 < Qprev := hPmom0.trans_le hPmomQ
  have hc0 : 0 ≤ c := by
    dsimp [c]
    have := Real.log_nonneg hL
    linarith
  have hcurrent := current_cell_smallness_le_scale_power alpha halpha Ncur v
    t hNcur ht htop
  have hprevious := inverse_previous_threshold_le_borrow beta hbeta0 Nprev r Pmom
    hNprev hPmom x hx1 hexpPrev
  have hmoment := four_rpow_mul_ordinaryLadderMomentCore_le_exp
    ell (by dsimp [ell]; exact ordinaryBorrowMoment_one_le Pmom x)
    mass u L beta hmass0 hmass hu (by simpa [ell] using hellL) hL hbeta
  have hborrowCore :
      (1 / Real.exp (-(beta * (r : ℝ) / ((2 * Nprev : ℕ) : ℝ))) ^
          (2 * ell)) * ordinaryLadderMomentCore ell mass u ≤
        (Pmom : ℝ) ^ (4 * beta) * x ^ (2 * beta) *
          Real.exp ((ell : ℝ) * c + 10) := by
    calc
      (1 / Real.exp (-(beta * (r : ℝ) / ((2 * Nprev : ℕ) : ℝ))) ^
          (2 * ell)) * ordinaryLadderMomentCore ell mass u ≤
        ((4 : ℝ) ^ (beta * (ell : ℝ)) *
            (Pmom : ℝ) ^ (4 * beta) * x ^ (2 * beta)) *
          ordinaryLadderMomentCore ell mass u := by
            apply mul_le_mul_of_nonneg_right
            · simpa [ell] using hprevious
            · unfold ordinaryLadderMomentCore
              positivity
      _ = (Pmom : ℝ) ^ (4 * beta) * x ^ (2 * beta) *
          ((4 : ℝ) ^ (beta * (ell : ℝ)) *
            ordinaryLadderMomentCore ell mass u) := by ring
      _ ≤ (Pmom : ℝ) ^ (4 * beta) * x ^ (2 * beta) *
          Real.exp ((ell : ℝ) * c + 10) := by
            apply mul_le_mul_of_nonneg_left
            · simpa [c] using hmoment
            · positivity
  have hexpMoment := exp_borrowMoment_le_scale_power Pmom hPmom x (t : ℝ) c hx1 hxt hc0
  have hxsplit : x ^ (2 * beta) = (t : ℝ) ^ (2 * beta) * tau ^ (2 * beta) := by
    dsimp [x]
    exact Real.mul_rpow ht0.le htau0
  have hPmomPow : (Pmom : ℝ) ^ (4 * beta) ≤ Qprev ^ (4 * beta) :=
    Real.rpow_le_rpow hPmom0.le hPmomQ (by positivity)
  have hscale := ordinary_current_scale_power_saving (Pcur : ℝ) (t : ℝ)
    (by exact_mod_cast hPcur) (by exact_mod_cast hPt)
    alpha beta c (Real.log Pmom) hgap (by simpa [c] using hfar)
  have hcur0 : 0 ≤ Real.exp (alpha / (Ncur : ℝ)) *
      (t : ℝ) ^ (-(2 * alpha)) :=
    by positivity
  have hcore0 : 0 ≤ ordinaryLadderMomentCore ell mass u := by
    unfold ordinaryLadderMomentCore
    positivity
  have hborrowNonneg :
      0 ≤ (1 / Real.exp (-(beta * (r : ℝ) / ((2 * Nprev : ℕ) : ℝ))) ^
          (2 * ell)) * ordinaryLadderMomentCore ell mass u :=
    mul_nonneg (by positivity) hcore0
  unfold ordinaryLadderCellRaw
  dsimp only
  rw [show ordinaryBorrowMoment Pmom ((t : ℝ) * tau) = ell by rfl]
  calc
    Real.exp (-(alpha * (v : ℝ) / ((2 * Ncur : ℕ) : ℝ))) ^ 2 /
          Real.exp (-(beta * (r : ℝ) / ((2 * Nprev : ℕ) : ℝ))) ^ (2 * ell) *
        ordinaryLadderMomentCore ell mass u =
      Real.exp (-(alpha * (v : ℝ) / ((2 * Ncur : ℕ) : ℝ))) ^ 2 *
        ((1 / Real.exp (-(beta * (r : ℝ) / ((2 * Nprev : ℕ) : ℝ))) ^
          (2 * ell)) * ordinaryLadderMomentCore ell mass u) := by ring
    _ ≤ (Real.exp (alpha / (Ncur : ℝ)) * (t : ℝ) ^ (-(2 * alpha))) *
        ((Pmom : ℝ) ^ (4 * beta) * x ^ (2 * beta) *
          Real.exp ((ell : ℝ) * c + 10)) := by
            exact mul_le_mul hcurrent hborrowCore hborrowNonneg hcur0
    _ ≤ (Real.exp (alpha / (Ncur : ℝ)) * (t : ℝ) ^ (-(2 * alpha))) *
        ((Pmom : ℝ) ^ (4 * beta) * x ^ (2 * beta) *
          (Real.exp (2 * c + 10) * (t : ℝ) ^ (c / Real.log Pmom))) := by gcongr
    _ = Real.exp (alpha / (Ncur : ℝ) + 2 * c + 10) * tau ^ (2 * beta) *
        ((Pmom : ℝ) ^ (4 * beta) *
          ((t : ℝ) ^ (-(2 * alpha)) * (t : ℝ) ^ (2 * beta) *
            (t : ℝ) ^ (c / Real.log Pmom))) := by
            rw [hxsplit]
            simp only [Real.exp_add]
            ring
    _ ≤ Real.exp (alpha / (Ncur : ℝ) + 2 * c + 10) * tau ^ (2 * beta) *
        (Qprev ^ (4 * beta) * (Pcur : ℝ) ^ (-(alpha - beta))) := by gcongr
    _ = Real.exp (alpha / (Ncur : ℝ) + 2 * (2 * Real.log L + 3) + 10) *
        tau ^ (2 * beta) * Qprev ^ (4 * beta) *
          (Pcur : ℝ) ^ (-(alpha - beta)) := by
      dsimp [c]
      ring

/-- The scale-free envelope left by the one-cell calculation. -/
noncomputable def ordinaryLadderCellEnvelope
    (Ncur Pcur : ℕ) (Qprev tau alpha beta L : ℝ) : ℝ :=
  Real.exp (alpha / (Ncur : ℝ) + 2 * (2 * Real.log L + 3) + 10) *
    tau ^ (2 * beta) * Qprev ^ (4 * beta) *
      (Pcur : ℝ) ^ (-(alpha - beta))

/-- Sum the pointwise L3-1 estimate over the current cells.  In particular,
empty cells cause no loss: their scale is allowed to be any `t v` satisfying
the same endpoint bounds, and later we take `max Pcur (ql j v)`. -/
theorem sum_ordinaryLadderCellRaw_le
    (Icur : Finset ℕ) (Ncur Nprev r Pmom Pcur : ℕ)
    (t : ℕ → ℕ) (u : ℕ → ℝ) (Qprev tau alpha beta mass L : ℝ)
    (hNcur : 0 < Ncur) (hNprev : 0 < Nprev) (hPmom : 2 ≤ Pmom)
    (hPcur : 1 ≤ Pcur)
    (hPt : ∀ v ∈ Icur, Pcur ≤ t v)
    (hPmomQ : (Pmom : ℝ) ≤ Qprev)
    (htop : ∀ v ∈ Icur,
      (t v : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (Ncur : ℝ))))
    (hexpPrev : Real.exp ((r : ℝ) / (2 * (Nprev : ℝ))) ≤
      2 * (Pmom : ℝ))
    (htau0 : 0 ≤ tau) (htau : tau ≤ 1)
    (hx : ∀ v ∈ Icur, 1 ≤ (t v : ℝ) * tau)
    (halpha : 0 ≤ alpha) (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (1 : ℝ) / 5) (hgap : 0 ≤ alpha - beta)
    (hmass0 : 0 ≤ mass) (hmass : mass ≤ 1)
    (hu0 : ∀ v ∈ Icur, 0 ≤ u v) (hu : ∀ v ∈ Icur, u v ≤ 1)
    (hL : 1 ≤ L)
    (hellL : ∀ v ∈ Icur,
      (ordinaryBorrowMoment Pmom ((t v : ℝ) * tau) : ℝ) ≤ L)
    (hfar : (2 * Real.log L + 3) / Real.log Pmom ≤ alpha - beta) :
    ∑ v ∈ Icur,
        ordinaryLadderCellRaw Ncur Nprev v r Pmom alpha beta mass (u v)
          ((t v : ℝ) * tau) ≤
      (Icur.card : ℝ) *
        ordinaryLadderCellEnvelope Ncur Pcur Qprev tau alpha beta L := by
  calc
    ∑ v ∈ Icur,
        ordinaryLadderCellRaw Ncur Nprev v r Pmom alpha beta mass (u v)
          ((t v : ℝ) * tau) ≤
      ∑ _v ∈ Icur,
        ordinaryLadderCellEnvelope Ncur Pcur Qprev tau alpha beta L := by
          apply Finset.sum_le_sum
          intro v hv
          exact ordinaryLadderCellRaw_le Ncur Nprev v r Pmom hNcur hNprev hPmom
            Pcur (t v) Qprev tau alpha beta mass (u v) L hPcur (hPt v hv)
            hPmomQ (htop v hv) hexpPrev htau0 htau (hx v hv) halpha hbeta0
            hbeta hgap hmass0 hmass (hu0 v hv) (hu v hv) hL (hellL v hv) hfar
    _ = (Icur.card : ℝ) *
        ordinaryLadderCellEnvelope Ncur Pcur Qprev tau alpha beta L := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- The finite-cell estimate implies the exact per-previous-cell budget fit
once the remaining explicit polylogarithmic inequality has been checked. -/
theorem ordinaryLadder_per_previous_cell_fit
    (Icur Iprev : Finset ℕ) (j : ℕ)
    (Ncur Nprev r Pmom Pcur : ℕ) (t : ℕ → ℕ) (u : ℕ → ℝ)
    (Qprev tau alpha beta mass L c3 eps : ℝ) (A Delta : ℕ)
    (hNcur : 0 < Ncur) (hNprev : 0 < Nprev) (hPmom : 2 ≤ Pmom)
    (hPcur : 1 ≤ Pcur)
    (hPt : ∀ v ∈ Icur, Pcur ≤ t v)
    (hPmomQ : (Pmom : ℝ) ≤ Qprev)
    (htop : ∀ v ∈ Icur,
      (t v : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (Ncur : ℝ))))
    (hexpPrev : Real.exp ((r : ℝ) / (2 * (Nprev : ℝ))) ≤
      2 * (Pmom : ℝ))
    (htau0 : 0 ≤ tau) (htau : tau ≤ 1)
    (hx : ∀ v ∈ Icur, 1 ≤ (t v : ℝ) * tau)
    (halpha : 0 ≤ alpha) (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (1 : ℝ) / 5) (hgap : 0 ≤ alpha - beta)
    (hmass0 : 0 ≤ mass) (hmass : mass ≤ 1)
    (hu0 : ∀ v ∈ Icur, 0 ≤ u v) (hu : ∀ v ∈ Icur, u v ≤ 1)
    (hL : 1 ≤ L)
    (hellL : ∀ v ∈ Icur,
      (ordinaryBorrowMoment Pmom ((t v : ℝ) * tau) : ℝ) ≤ L)
    (hfar : (2 * Real.log L + 3) / Real.log Pmom ≤ alpha - beta)
    (hc3 : 0 ≤ c3) (hA : 2 ≤ A) (hhalf : A / 2 ≤ Delta)
    (hnumerology :
      (Icur.card : ℝ) ^ 2 *
          ordinaryLadderCellEnvelope Ncur Pcur Qprev tau alpha beta L ≤
        (ordinaryLegShare j / (Iprev.card : ℝ)) * c3 * eps ^ 2 / 24) :
    (Icur.card : ℝ) *
        ∑ v ∈ Icur,
          ordinaryLadderCellRaw Ncur Nprev v r Pmom alpha beta mass (u v)
            ((t v : ℝ) * tau) ≤
      (ordinaryLegShare j / (Iprev.card : ℝ)) *
        bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)) := by
  have hsum := sum_ordinaryLadderCellRaw_le Icur Ncur Nprev r Pmom Pcur t u
    Qprev tau alpha beta mass L hNcur hNprev hPmom hPcur hPt hPmomQ htop
    hexpPrev htau0 htau hx halpha hbeta0 hbeta hgap hmass0 hmass hu0 hu hL
    hellL hfar
  have hbudget := bandBudget_one_twenty_four_le_of_nat_half_le
    c3 eps hc3 A Delta hA hhalf
  have hshare0 : 0 ≤ ordinaryLegShare j / (Iprev.card : ℝ) := by
    unfold ordinaryLegShare
    positivity
  calc
    (Icur.card : ℝ) *
          ∑ v ∈ Icur,
            ordinaryLadderCellRaw Ncur Nprev v r Pmom alpha beta mass (u v)
              ((t v : ℝ) * tau) ≤
        (Icur.card : ℝ) * ((Icur.card : ℝ) *
          ordinaryLadderCellEnvelope Ncur Pcur Qprev tau alpha beta L) := by
            exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (Icur.card : ℝ) ^ 2 *
          ordinaryLadderCellEnvelope Ncur Pcur Qprev tau alpha beta L := by ring
    _ ≤ (ordinaryLegShare j / (Iprev.card : ℝ)) * c3 * eps ^ 2 / 24 := hnumerology
    _ = (ordinaryLegShare j / (Iprev.card : ℝ)) * (c3 * eps ^ 2 / 24) := by ring
    _ ≤ (ordinaryLegShare j / (Iprev.card : ℝ)) *
        bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)) :=
      mul_le_mul_of_nonneg_left hbudget hshare0

/-- Substituting `Pcur = Qprev^(100*j^2)` exposes the advertised uniform
`Qprev^(-9/20)` saving before the harmless finite-cell factors. -/
theorem ordinaryLadderCellEnvelope_le_schedule
    (Ncur Qprev : ℕ) (tau L : ℝ) (j : ℕ) (hj : 0 < j)
    (hQprev : 1 ≤ Qprev) (htau0 : 0 ≤ tau) :
    ordinaryLadderCellEnvelope Ncur (Qprev ^ (100 * j ^ 2)) Qprev tau
        (innerBandScheduleAlpha j) (innerBandScheduleAlpha (j - 1)) L ≤
      Real.exp (innerBandScheduleAlpha j / (Ncur : ℝ) +
          2 * (2 * Real.log L + 3) + 10) *
        tau ^ (2 * innerBandScheduleAlpha (j - 1)) *
          (Qprev : ℝ) ^ (-(9 : ℝ) / 20) := by
  have hsaving := ordinary_ladder_power_saving (Qprev : ℝ)
    (by exact_mod_cast hQprev) j hj
  unfold ordinaryLadderCellEnvelope
  rw [Nat.cast_pow]
  have hnonneg : 0 ≤
      Real.exp (innerBandScheduleAlpha j / (Ncur : ℝ) +
          2 * (2 * Real.log L + 3) + 10) *
        tau ^ (2 * innerBandScheduleAlpha (j - 1)) := by positivity
  calc
    Real.exp (innerBandScheduleAlpha j / (Ncur : ℝ) +
          2 * (2 * Real.log L + 3) + 10) *
        tau ^ (2 * innerBandScheduleAlpha (j - 1)) *
        (Qprev : ℝ) ^ (4 * innerBandScheduleAlpha (j - 1)) *
        ((Qprev : ℝ) ^ (100 * j ^ 2)) ^
          (-(innerBandScheduleAlpha j - innerBandScheduleAlpha (j - 1))) =
      (Real.exp (innerBandScheduleAlpha j / (Ncur : ℝ) +
          2 * (2 * Real.log L + 3) + 10) *
        tau ^ (2 * innerBandScheduleAlpha (j - 1))) *
        (((Qprev : ℝ) ^ (100 * j ^ 2)) ^
          (-(innerBandScheduleAlpha j - innerBandScheduleAlpha (j - 1))) *
        (Qprev : ℝ) ^ (4 * innerBandScheduleAlpha (j - 1))) := by ring
    _ ≤ (Real.exp (innerBandScheduleAlpha j / (Ncur : ℝ) +
          2 * (2 * Real.log L + 3) + 10) *
        tau ^ (2 * innerBandScheduleAlpha (j - 1))) *
          (Qprev : ℝ) ^ (-(9 : ℝ) / 20) :=
      mul_le_mul_of_nonneg_left hsaving hnonneg
    _ = _ := by ring

/-- After the fixed ladder jump, checking the later-level fit is reduced to
one explicit inequality in which all dependence on the prime scales occurs
through `Qprev^(-9/20)`. -/
theorem ordinaryLadder_card_envelope_le_of_schedule
    (Icur Iprev : Finset ℕ) (Ncur Qprev : ℕ) (tau L c3 eps : ℝ)
    (j : ℕ) (hj : 0 < j) (hQprev : 1 ≤ Qprev) (htau0 : 0 ≤ tau)
    (hpolylog :
      (Icur.card : ℝ) ^ 2 *
          (Real.exp (innerBandScheduleAlpha j / (Ncur : ℝ) +
              2 * (2 * Real.log L + 3) + 10) *
            tau ^ (2 * innerBandScheduleAlpha (j - 1)) *
              (Qprev : ℝ) ^ (-(9 : ℝ) / 20)) ≤
        (ordinaryLegShare j / (Iprev.card : ℝ)) * c3 * eps ^ 2 / 24) :
    (Icur.card : ℝ) ^ 2 *
        ordinaryLadderCellEnvelope Ncur (Qprev ^ (100 * j ^ 2)) Qprev tau
          (innerBandScheduleAlpha j) (innerBandScheduleAlpha (j - 1)) L ≤
      (ordinaryLegShare j / (Iprev.card : ℝ)) * c3 * eps ^ 2 / 24 := by
  have henvelope := ordinaryLadderCellEnvelope_le_schedule
    Ncur Qprev tau L j hj hQprev htau0
  exact (mul_le_mul_of_nonneg_left henvelope (by positivity)).trans hpolylog

/-- The uniform per-previous-cell share used by L3-1. -/
noncomputable def ordinaryUniformCellShare
    (j : ℕ) (Iprev : Finset ℕ) : ℝ :=
  ordinaryLegShare j / (Iprev.card : ℝ)

/-- Uniform shares sum exactly to the parent main-leg share when the previous
cell range is nonempty. -/
theorem sum_ordinaryUniformCellShare
    (j : ℕ) (Iprev : Finset ℕ) (hI : Iprev.Nonempty) :
    ∑ _r ∈ Iprev, ordinaryUniformCellShare j Iprev = ordinaryLegShare j := by
  have hcard : (Iprev.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hI)
  simp only [ordinaryUniformCellShare, Finset.sum_const, nsmul_eq_mul]
  field_simp [hcard]

/-- The old three `ordinaryLegShare`s already fit the new shifted partition
share; there is a factor `32/18` of slack. -/
theorem ordinaryLegShares_fit_shifted (j : ℕ) :
    2 * ordinaryLegShare j + 2 * ordinaryLegShare j + 2 * ordinaryLegShare j ≤
      (1 : ℝ) / 2 ^ (j + 2) := by
  unfold ordinaryLegShare
  have hp : 0 < (2 : ℝ) ^ (j + 1) := by positivity
  have hp2 : (2 : ℝ) ^ (j + 2) = 2 * 2 ^ (j + 1) := by
    rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
    ring
  rw [hp2]
  field_simp
  norm_num

end Tao2015

end MoltResearch
