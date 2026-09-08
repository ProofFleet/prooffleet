import MoltResearch.Discrepancy.PrimeLargeValuesFromRegionHMax
import MoltResearch.Discrepancy.ZeroFreeRegionData
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Real-variable envelope for the balanced Mellin height

This leaf records the one-variable thresholds used by the three-regime
bookkeeping.  Keeping them named makes the later large-values assembly a
finite chain of inequalities rather than a collection of implicit
"sufficiently large" steps.
-/

namespace MoltResearch

open Filter

/-- A named threshold at which a constant and a logarithm are dominated by
a prescribed fraction of a positive real power. -/
theorem exists_const_add_log_le_rpow_quarter
    (r A : ℝ) (hr : 0 < r) (_hA : 0 ≤ A) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      A + Real.log x ≤ x ^ r / 4 := by
  have hlo := isLittleO_log_rpow_atTop hr
  have heps : (0 : ℝ) < 1 / 8 := by norm_num
  have hlog := hlo.def heps
  rw [Filter.eventually_atTop] at hlog
  obtain ⟨xlog, hxlog⟩ := hlog
  have hpowtop : Tendsto (fun x : ℝ => x ^ r) atTop atTop :=
    tendsto_rpow_atTop hr
  have hconst : ∀ᶠ x : ℝ in atTop, 8 * A ≤ x ^ r :=
    hpowtop.eventually (eventually_ge_atTop (8 * A))
  rw [Filter.eventually_atTop] at hconst
  obtain ⟨xconst, hxconst⟩ := hconst
  let x₀ : ℝ := max 1 (max xlog xconst)
  refine ⟨x₀, le_max_left _ _, ?_⟩
  intro x hx
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxlog' : xlog ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx)
  have hxconst' : xconst ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx)
  have hlog' := hxlog x hxlog'
  have hconst' := hxconst x hxconst'
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hpow0 : 0 ≤ x ^ r := Real.rpow_nonneg (by linarith) _
  simp only [Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_nonneg hpow0] at hlog'
  nlinarith

/-- A named threshold at which a smaller positive power is at most half of
the identity. -/
theorem exists_rpow_le_half_id
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      x ^ r ≤ x / 2 := by
  have ht : Tendsto (fun x : ℝ => x ^ (-(1 - r))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have hevent : ∀ᶠ x : ℝ in atTop, x ^ (-(1 - r)) < 1 / 2 :=
    ht.eventually_lt_const (by norm_num)
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨xpow, hxpow⟩ := hevent
  let x₀ : ℝ := max 1 xpow
  refine ⟨x₀, le_max_left _ _, ?_⟩
  intro x hx
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := by linarith
  have hp := hxpow x (le_trans (le_max_right _ _) hx)
  have heq : x ^ r / x = x ^ (-(1 - r)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hx0]
    congr 1
    ring
  rw [← heq] at hp
  calc
    x ^ r ≤ (1 / 2) * x := (div_le_iff₀ hx0).mp (le_of_lt hp)
    _ = x / 2 := by ring

/-- A polynomial is eventually absorbed by any positive exponential. -/
theorem exists_rpow_mul_exp_neg_le_one
    (s c : ℝ) (hc : 0 < c) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      x ^ s * Real.exp (-c * x) ≤ 1 := by
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s c hc
  have hevent : ∀ᶠ x : ℝ in atTop,
      x ^ s * Real.exp (-c * x) < 1 :=
    ht.eventually_lt_const zero_lt_one
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨xpow, hxpow⟩ := hevent
  refine ⟨max 1 xpow, le_max_left _ _, fun x hx => ?_⟩
  exact le_of_lt (hxpow x (le_trans (le_max_right _ _) hx))

/-- If `theta < theta'`, every fixed multiple of a shifted `theta`-power is
eventually below the `theta'`-power.  This is the named Regime-I threshold. -/
theorem exists_shifted_rpow_le
    (theta theta' c K : ℝ) (hgap : theta < theta')
    (htheta : 0 ≤ theta) (hK : 0 ≤ K) :
    ∃ y₁ : ℝ, 1 ≤ y₁ ∧ ∀ y : ℝ, y₁ ≤ y →
      K * (y + c) ^ theta ≤ y ^ theta' := by
  let A : ℝ := |c|
  let Q : ℝ := K * 2 ^ theta
  have hpowtop : Tendsto (fun y : ℝ => y ^ (theta' - theta)) atTop atTop :=
    tendsto_rpow_atTop (sub_pos.mpr hgap)
  have hevent : ∀ᶠ y : ℝ in atTop, Q ≤ y ^ (theta' - theta) :=
    hpowtop.eventually (eventually_ge_atTop Q)
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨ypow, hypow⟩ := hevent
  let y₁ : ℝ := max 1 (max A ypow)
  refine ⟨y₁, le_max_left _ _, ?_⟩
  intro y hy
  have hy1 : 1 ≤ y := le_trans (le_max_left _ _) hy
  have hy0 : 0 < y := by linarith
  have hAy : A ≤ y := le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) hy)
  have hc : c ≤ y := by
    exact le_trans (le_abs_self c) hAy
  have hcneg : -y ≤ c := by
    have := neg_le_of_abs_le (show |c| ≤ y by exact hAy)
    exact this
  have hsum : y + c ≤ 2 * y := by linarith
  have hshift : (y + c) ^ theta ≤ (2 * y) ^ theta :=
    Real.rpow_le_rpow (by linarith) hsum htheta
  have hmul : (2 * y) ^ theta = 2 ^ theta * y ^ theta := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hy0.le]
  have hQ := hypow y (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hy))
  have hthetaPow : 0 < y ^ theta := Real.rpow_pos_of_pos hy0 _
  have hsplit : y ^ theta' = y ^ (theta' - theta) * y ^ theta := by
    rw [← Real.rpow_add hy0]
    ring_nf
  calc
    K * (y + c) ^ theta ≤ K * (2 * y) ^ theta :=
      mul_le_mul_of_nonneg_left hshift hK
    _ = Q * y ^ theta := by rw [hmul]; dsimp only [Q]; ring
    _ ≤ y ^ (theta' - theta) * y ^ theta :=
      mul_le_mul_of_nonneg_right hQ hthetaPow.le
    _ = y ^ theta' := hsplit.symm

/-- A smaller real power and a logarithm are eventually dominated by a
fixed fraction of the identity.  This supplies the named Regime-II
threshold after writing `q = x^(1/(1+theta))`. -/
theorem exists_rpow_add_log_le_linear_sixth
    (beta A K : ℝ) (hbeta : beta < 1) (hA : 0 ≤ A) (hK : 0 ≤ K) :
    ∃ q₁ : ℝ, 1 ≤ q₁ ∧ ∀ q : ℝ, q₁ ≤ q →
      A * q ^ beta + K * Real.log q + A ≤ q / 6 := by
  have hpow : Tendsto (fun q : ℝ => q ^ (-(1 - beta))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have hpowEvent : ∀ᶠ q : ℝ in atTop,
      q ^ (-(1 - beta)) < 1 / (18 * (A + 1)) :=
    hpow.eventually_lt_const (by positivity)
  rw [Filter.eventually_atTop] at hpowEvent
  obtain ⟨qpow, hqpow⟩ := hpowEvent
  have hlogLittle := Real.isLittleO_log_id_atTop.def
    (show (0 : ℝ) < 1 / (18 * (K + 1)) by positivity)
  rw [Filter.eventually_atTop] at hlogLittle
  obtain ⟨qlog, hqlog⟩ := hlogLittle
  let qconst : ℝ := 18 * A + 1
  let q₁ : ℝ := max 1 (max qpow (max qlog qconst))
  refine ⟨q₁, le_max_left _ _, ?_⟩
  intro q hq
  have hq1 : 1 ≤ q := le_trans (le_max_left _ _) hq
  have hq0 : 0 < q := by linarith
  have hp := hqpow q (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) hq))
  have hl := hqlog q (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hq)))
  have hc : qconst ≤ q := le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hq))
  have hpow0 : 0 ≤ q ^ (-(1 - beta)) := Real.rpow_nonneg hq0.le _
  have hlog0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  simp only [Real.norm_eq_abs, id, abs_of_nonneg hlog0, abs_of_pos hq0] at hl
  have hratio : q ^ beta / q = q ^ (-(1 - beta)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hq0]
    congr 1
    ring
  have hApow : A * q ^ beta ≤ q / 18 := by
    have hp' : q ^ beta / q ≤ 1 / (18 * (A + 1)) := by
      rw [hratio]
      exact le_of_lt hp
    have hqbeta : q ^ beta ≤ q / (18 * (A + 1)) := by
      have := (div_le_iff₀ hq0).mp hp'
      convert this using 1 <;> field_simp <;> ring
    have hAA : A ≤ A + 1 := by linarith
    have hden0 : 0 < 18 * (A + 1) := by positivity
    calc
      A * q ^ beta ≤ A * (q / (18 * (A + 1))) :=
        mul_le_mul_of_nonneg_left hqbeta hA
      _ ≤ (A + 1) * (q / (18 * (A + 1))) :=
        mul_le_mul_of_nonneg_right hAA (by positivity)
      _ = q / 18 := by field_simp
  have hKlog : K * Real.log q ≤ q / 18 := by
    have hl' : Real.log q ≤ (1 / (18 * (K + 1))) * q := by
      simpa only [id, one_div, mul_comm] using hl
    have hKK : K ≤ K + 1 := by linarith
    calc
      K * Real.log q ≤ K * ((1 / (18 * (K + 1))) * q) :=
        mul_le_mul_of_nonneg_left hl' hK
      _ ≤ (K + 1) * ((1 / (18 * (K + 1))) * q) :=
        mul_le_mul_of_nonneg_right hKK (by positivity)
      _ = q / 18 := by field_simp
  have hAconst : A ≤ q / 18 := by
    dsimp only [qconst] at hc
    linarith
  linarith

/-- The harmless Perron-line power is at most `e * P`. -/
theorem rpow_one_add_inv_log_two_mul_le_exp_mul
    (P : ℝ) (hP : 2 ≤ P) :
    P ^ (1 + 1 / Real.log (2 * P)) ≤ Real.exp 1 * P := by
  have hP0 : 0 < P := by linarith
  have h2P0 : 0 < 2 * P := by positivity
  have hlogP0 : 0 < Real.log P := Real.log_pos (by linarith)
  have hlog2P0 : 0 < Real.log (2 * P) := Real.log_pos (by linarith)
  have hlogmono : Real.log P ≤ Real.log (2 * P) :=
    Real.log_le_log hP0 (by linarith)
  rw [Real.rpow_def_of_pos hP0]
  rw [show Real.exp 1 * P = Real.exp (1 + Real.log P) by
    rw [Real.exp_add, Real.exp_log hP0]]
  rw [Real.exp_le_exp]
  have hratio : Real.log P / Real.log (2 * P) ≤ 1 :=
    (div_le_one hlog2P0).2 hlogmono
  rw [mul_add, mul_one]
  have hterm : Real.log P * (1 / Real.log (2 * P)) =
      Real.log P / Real.log (2 * P) := by
    simp only [div_eq_mul_inv, one_mul]
  rw [hterm]
  linarith

/-- The logarithms occurring in the right-line and prime-power tails are
bounded by fixed multiples of `log P`. -/
theorem log_two_mul_le_two_log (P : ℝ) (hP : 2 ≤ P) :
    Real.log (2 * P) ≤ 2 * Real.log P := by
  have hP0 : 0 < P := by linarith
  have hlog2 : Real.log 2 ≤ Real.log P :=
    Real.log_le_log (by norm_num) hP
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hP0.ne']
  linarith

theorem log_four_mul_le_three_log (P : ℝ) (hP : 2 ≤ P) :
    Real.log (4 * P) ≤ 3 * Real.log P := by
  have hP0 : 0 < P := by linarith
  have hlog2 : Real.log 2 ≤ Real.log P :=
    Real.log_le_log (by norm_num) hP
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hP0.ne', hlog4]
  linarith

/-- The balancing power really is the inverse of `1 + theta`. -/
theorem balancing_rpow_pow (theta x : ℝ) (htheta : 0 < theta) (hx : 0 ≤ x) :
    (x ^ (1 / (1 + theta))) ^ (1 + theta) = x := by
  rw [← Real.rpow_mul hx]
  have hne : 1 + theta ≠ 0 := by linarith
  rw [one_div, inv_mul_cancel₀ hne, Real.rpow_one]

set_option maxHeartbeats 800000

/-- Uniform estimate for the four raw contour terms.  Its hypotheses are the
elementary consequences of the balanced choice `Z >= exp q`, where
`q = (log P)^(1/(1+theta))`.  The two polynomial--exponential hypotheses are
exactly the named large-`P` thresholds used below. -/
theorem balanced_raw_contour_bound
    (theta m eta0 M0 P u Z x q w : ℝ)
    (hP : 2 ≤ P) (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hM0 : 1 ≤ M0) (hm : m ≤ 2)
    (hx : x = Real.log P) (hq : q ^ (1 + theta) = x)
    (hq1 : 1 ≤ q) (hZ : Real.exp q ≤ Z)
    (hw : w = Real.log (2 * Z))
    (heta : zeroFreeRegionEtaH theta eta0 Z = w ^ (-theta))
    (hu : |u| ≤ Z / 2) (hqx : q ≤ x / 2)
    (hqpoly : q ^ (2 : ℝ) * Real.exp (-(1 / 2) * q) ≤ 1)
    (hxpoly : x * Real.exp (-(1 / 4) * x) ≤ 1) :
    let eta := zeroFreeRegionEtaH theta eta0 Z
    let M := zeroFreeRegionRegularBoundH m M0 Z
    let c := 1 + 1 / Real.log (2 * P)
    (M + 1) *
        (P ^ (1 - eta / 2) +
          P ^ c * Real.log (2 * P) / (Z - |u|) +
          P ^ c / Z ^ 2 + Real.sqrt P * Real.log (4 * P)) ≤
      ((M0 + 1) * (4 + 5 * Real.exp 1)) * P * w ^ 2 *
        Real.exp (-(x / (2 * w ^ theta))) := by
  dsimp only
  have hP0 : 0 < P := by linarith
  have hxpos : 0 < x := by rw [hx]; exact Real.log_pos (by linarith)
  have hq0 : 0 < q := by linarith
  have hZ0 : 0 < Z := lt_of_lt_of_le (Real.exp_pos q) hZ
  have hwq : q ≤ w := by
    rw [hw]
    have hmono := Real.log_le_log (Real.exp_pos q)
      (show Real.exp q ≤ 2 * Z by linarith)
    simpa using hmono
  have hw1 : 1 ≤ w := le_trans hq1 hwq
  have hw0 : 0 < w := by linarith
  have hetaX : w ^ (-theta) * x ≤ q := by
    have hneg : -theta ≤ 0 := by linarith
    have hrpow := Real.rpow_le_rpow_of_nonpos hq0 hwq hneg
    have hx0 : 0 ≤ x := hxpos.le
    have hqpow : q ^ (-theta) * x = q := by
      rw [← hq, ← Real.rpow_add hq0]
      convert Real.rpow_one q using 1 <;> ring
    calc
      w ^ (-theta) * x ≤ q ^ (-theta) * x :=
        mul_le_mul_of_nonneg_right hrpow hx0
      _ = q := hqpow
  have hetaX' : zeroFreeRegionEtaH theta eta0 Z * x ≤ q := by
    rw [heta]
    exact hetaX
  have hdpos : 0 < Real.exp (-(x / (2 * w ^ theta))) := Real.exp_pos _
  have hexpForm :
      Real.exp (-(zeroFreeRegionEtaH theta eta0 Z * x / 2)) =
        Real.exp (-(x / (2 * w ^ theta))) := by
    rw [heta, Real.rpow_neg hw0.le]
    congr 1
    field_simp
  have hshift : P ^ (1 - zeroFreeRegionEtaH theta eta0 Z / 2) =
      P * Real.exp (-(x / (2 * w ^ theta))) := by
    rw [Real.rpow_def_of_pos hP0]
    rw [show Real.log P * (1 - zeroFreeRegionEtaH theta eta0 Z / 2) =
        Real.log P + -(zeroFreeRegionEtaH theta eta0 Z * Real.log P / 2) by ring,
      Real.exp_add, Real.exp_log hP0]
    rw [← hx, hexpForm]
  have hqtheta : q ^ (1 + theta) ≤ q ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hxq2 : x ≤ q ^ (2 : ℝ) := by rw [← hq]; exact hqtheta
  have hmainQ : x / (2 * w ^ theta) ≤ q / 2 := by
    have hwtheta : q ^ theta ≤ w ^ theta :=
      Real.rpow_le_rpow hq0.le hwq htheta.le
    have hwtheta0 : 0 < w ^ theta := Real.rpow_pos_of_pos hw0 _
    have hqtheta0 : 0 < q ^ theta := Real.rpow_pos_of_pos hq0 _
    have hquot : x / w ^ theta ≤ q := by
      rw [← hq]
      have heq : q ^ (1 + theta) = q * q ^ theta := by
        rw [show 1 + theta = theta + 1 by ring, Real.rpow_add hq0,
          Real.rpow_one]
        ring
      rw [heq]
      exact (div_le_iff₀ hwtheta0).2 (by
        nlinarith [mul_le_mul_of_nonneg_left hwtheta hq0.le])
    calc
      x / (2 * w ^ theta) = (x / w ^ theta) / 2 := by ring
      _ ≤ q / 2 := div_le_div_of_nonneg_right hquot (by norm_num)
  have hexpQ : Real.exp (-(q / 2)) ≤
      Real.exp (-(x / (2 * w ^ theta))) := by
    rw [Real.exp_le_exp]
    linarith
  have hPerron := rpow_one_add_inv_log_two_mul_le_exp_mul P hP
  have hlog2P := log_two_mul_le_two_log P hP
  have hlog4P := log_four_mul_le_three_log P hP
  have hden : Z / 2 ≤ Z - |u| := by linarith
  have hden0 : 0 < Z - |u| := by linarith
  have hInvDen : 1 / (Z - |u|) ≤ 2 * Real.exp (-q) := by
    have hinv : 1 / (Z - |u|) ≤ 2 / Z := by
      calc
        1 / (Z - |u|) ≤ 1 / (Z / 2) :=
          one_div_le_one_div_of_le (by positivity) hden
        _ = 2 / Z := by field_simp
    have hzinv : 1 / Z ≤ Real.exp (-q) := by
      rw [Real.exp_neg]
      simpa only [one_div] using
        (one_div_le_one_div_of_le (Real.exp_pos q) hZ)
    calc
      1 / (Z - |u|) ≤ 2 / Z := hinv
      _ = 2 * (1 / Z) := by ring
      _ ≤ 2 * Real.exp (-q) := by gcongr
  have htailOne :
      P ^ (1 + 1 / Real.log (2 * P)) * Real.log (2 * P) /
          (Z - |u|) ≤
        4 * Real.exp 1 * P * Real.exp (-(x / (2 * w ^ theta))) := by
    have hnum0 : 0 ≤ P ^ (1 + 1 / Real.log (2 * P)) :=
      Real.rpow_nonneg hP0.le _
    have hlog0 : 0 ≤ Real.log (2 * P) :=
      Real.log_nonneg (by linarith)
    have hlog2Px : Real.log (2 * P) ≤ 2 * x := by simpa only [hx] using hlog2P
    have hstep :
        P ^ (1 + 1 / Real.log (2 * P)) * Real.log (2 * P) /
            (Z - |u|) ≤
          (Real.exp 1 * P) * (2 * x) * (2 * Real.exp (-q)) := by
      rw [div_eq_mul_inv]
      gcongr
      simpa only [div_eq_mul_inv, one_mul] using hInvDen
    have hxe : x * Real.exp (-q) ≤ Real.exp (-(q / 2)) := by
      have hpoly : x * Real.exp (-(q / 2)) ≤ 1 := by
        have hqp : q ^ (2 : ℝ) * Real.exp (-(q / 2)) ≤ 1 := by
          convert hqpoly using 1 <;> ring
        exact le_trans (mul_le_mul_of_nonneg_right hxq2
          (Real.exp_pos _).le) hqp
      rw [show -q = -(q / 2) + -(q / 2) by ring, Real.exp_add]
      nlinarith [Real.exp_pos (-(q / 2))]
    calc
      _ ≤ (Real.exp 1 * P) * (2 * x) * (2 * Real.exp (-q)) := hstep
      _ = 4 * Real.exp 1 * P * (x * Real.exp (-q)) := by ring
      _ ≤ 4 * Real.exp 1 * P * Real.exp (-(q / 2)) := by gcongr
      _ ≤ 4 * Real.exp 1 * P *
          Real.exp (-(x / (2 * w ^ theta))) := by gcongr
  have htailTwo :
      P ^ (1 + 1 / Real.log (2 * P)) / Z ^ 2 ≤
        Real.exp 1 * P * Real.exp (-(x / (2 * w ^ theta))) := by
    have hZsq : Real.exp (2 * q) ≤ Z ^ 2 := by
      rw [show Real.exp (2 * q) = (Real.exp q) ^ 2 by
        rw [show 2 * q = q + q by ring, Real.exp_add, pow_two]]
      nlinarith [Real.exp_pos q]
    have hinv : 1 / Z ^ 2 ≤ Real.exp (-(2 * q)) := by
      rw [Real.exp_neg]
      simpa only [one_div] using
        (one_div_le_one_div_of_le (Real.exp_pos (2 * q)) hZsq)
    have hexp : Real.exp (-(2 * q)) ≤
        Real.exp (-(x / (2 * w ^ theta))) := by
      rw [Real.exp_le_exp]
      linarith [hmainQ]
    rw [div_eq_mul_inv]
    calc
      _ ≤ (Real.exp 1 * P) * Real.exp (-(2 * q)) := by
        gcongr
        simpa only [div_eq_mul_inv, one_mul] using hinv
      _ ≤ Real.exp 1 * P * Real.exp (-(x / (2 * w ^ theta))) := by gcongr
  have hsqrt :
      Real.sqrt P * Real.log (4 * P) ≤
        3 * P * Real.exp (-(x / (2 * w ^ theta))) := by
    have hsqrtForm : Real.sqrt P = P * Real.exp (-(x / 2)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hP0, hx]
      rw [show Real.log P * (1 / (2 : ℝ)) =
          Real.log P + -(Real.log P / 2) by ring,
        Real.exp_add, Real.exp_log hP0]
    have hxexp : x * Real.exp (-(x / 2)) ≤ Real.exp (-(x / 4)) := by
      rw [show -(x / 2) = -(x / 4) + -(x / 4) by ring, Real.exp_add]
      have hp : x * Real.exp (-(x / 4)) ≤ 1 := by
        convert hxpoly using 1 <;> ring
      calc
        x * (Real.exp (-(x / 4)) * Real.exp (-(x / 4))) =
            (x * Real.exp (-(x / 4))) * Real.exp (-(x / 4)) := by ring
        _ ≤ 1 * Real.exp (-(x / 4)) :=
          mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
        _ = Real.exp (-(x / 4)) := one_mul _
    have hexpX : Real.exp (-(x / 4)) ≤
        Real.exp (-(x / (2 * w ^ theta))) := by
      rw [Real.exp_le_exp]
      linarith [hmainQ, hqx]
    rw [hsqrtForm]
    have hlog4Px : Real.log (4 * P) ≤ 3 * x := by
      simpa only [hx] using hlog4P
    calc
      P * Real.exp (-(x / 2)) * Real.log (4 * P) ≤
          P * Real.exp (-(x / 2)) * (3 * x) := by gcongr
      _ = 3 * P * (x * Real.exp (-(x / 2))) := by ring
      _ ≤ 3 * P * Real.exp (-(x / 4)) := by gcongr
      _ ≤ 3 * P * Real.exp (-(x / (2 * w ^ theta))) := by gcongr
  have hraw :
      P ^ (1 - zeroFreeRegionEtaH theta eta0 Z / 2) +
          P ^ (1 + 1 / Real.log (2 * P)) * Real.log (2 * P) / (Z - |u|) +
          P ^ (1 + 1 / Real.log (2 * P)) / Z ^ 2 +
          Real.sqrt P * Real.log (4 * P) ≤
        (4 + 5 * Real.exp 1) * P *
          Real.exp (-(x / (2 * w ^ theta))) := by
    rw [hshift]
    have he1 : 1 ≤ Real.exp 1 := (Real.one_le_exp_iff).2 (by norm_num)
    nlinarith
  have hmPow : w ^ m ≤ w ^ (2 : ℕ) := by
    simpa only [Real.rpow_two] using
      (Real.rpow_le_rpow_of_exponent_le hw1 hm)
  have hwSq1 : 1 ≤ w ^ (2 : ℕ) := by
    have hmul : (1 : ℝ) * 1 ≤ w * w :=
      mul_le_mul hw1 hw1 (by norm_num) (by linarith)
    simpa only [one_mul, pow_two] using hmul
  have hM : zeroFreeRegionRegularBoundH m M0 Z + 1 ≤
      (M0 + 1) * w ^ (2 : ℕ) := by
    dsimp only [zeroFreeRegionRegularBoundH]
    rw [← hw]
    have hM0w : M0 ≤ M0 * w ^ (2 : ℕ) := by
      nlinarith [mul_le_mul_of_nonneg_left hwSq1 (by linarith : 0 ≤ M0)]
    have hmw : w ^ m ≤ M0 * w ^ (2 : ℕ) := by
      have hM01 : 1 ≤ M0 := hM0
      nlinarith [mul_le_mul_of_nonneg_right hM01
        (sq_nonneg w)]
    have hmax : max M0 (w ^ m) ≤ M0 * w ^ (2 : ℕ) :=
      max_le hM0w hmw
    nlinarith
  have hraw0 : 0 ≤
      P ^ (1 - zeroFreeRegionEtaH theta eta0 Z / 2) +
          P ^ (1 + 1 / Real.log (2 * P)) * Real.log (2 * P) / (Z - |u|) +
          P ^ (1 + 1 / Real.log (2 * P)) / Z ^ 2 +
          Real.sqrt P * Real.log (4 * P) := by
    have hlog2nonneg : 0 ≤ Real.log (2 * P) :=
      Real.log_nonneg (by linarith)
    have hlog4nonneg : 0 ≤ Real.log (4 * P) :=
      Real.log_nonneg (by linarith)
    positivity
  calc
    _ ≤ ((M0 + 1) * w ^ (2 : ℕ)) *
        (P ^ (1 - zeroFreeRegionEtaH theta eta0 Z / 2) +
          P ^ (1 + 1 / Real.log (2 * P)) * Real.log (2 * P) / (Z - |u|) +
          P ^ (1 + 1 / Real.log (2 * P)) / Z ^ 2 +
          Real.sqrt P * Real.log (4 * P)) :=
      mul_le_mul_of_nonneg_right hM hraw0
    _ ≤ ((M0 + 1) * w ^ (2 : ℕ)) *
        ((4 + 5 * Real.exp 1) * P *
          Real.exp (-(x / (2 * w ^ theta)))) := by
      gcongr
    _ = ((M0 + 1) * (4 + 5 * Real.exp 1)) * P * w ^ 2 *
        Real.exp (-(x / (2 * w ^ theta))) := by
      let d := Real.exp (-(x / (2 * w ^ theta)))
      change ((M0 + 1) * w ^ 2) * ((4 + 5 * Real.exp 1) * P * d) =
        ((M0 + 1) * (4 + 5 * Real.exp 1)) * P * w ^ 2 * d
      ring

/-- Cauchy--Schwarz bound used in Regime 0 and in the bounded transition
ranges.  No zeta input enters here. -/
theorem prime_large_values_trivial
    (P : ℕ) (Y : Finset ℕ) (a : ℕ → ℂ) (𝒯 : Finset ℝ)
    (hP : 1 ≤ P) (hYrange : ∀ p ∈ Y, p ≤ 2 * P) :
    ∑ t ∈ 𝒯, ‖∑ p ∈ Y, (a p / (p : ℂ)) *
        ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖ ^ 2 ≤
      3 * (𝒯.card : ℝ) * P *
        (∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2) := by
  classical
  have hsubset : Y ⊆ Finset.range (2 * P + 1) := by
    intro p hp
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (hYrange p hp)
  have hcardNat : Y.card ≤ 2 * P + 1 :=
    by simpa using Finset.card_le_card hsubset
  have hcard : (Y.card : ℝ) ≤ 3 * P := by
    have hcast : (Y.card : ℝ) ≤ 2 * P + 1 := by exact_mod_cast hcardNat
    have hPR : (1 : ℝ) ≤ P := by exact_mod_cast hP
    linarith
  have hmass0 : 0 ≤ ∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2 := by positivity
  have hpoint : ∀ t : ℝ,
      ‖∑ p ∈ Y, (a p / (p : ℂ)) *
          ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖ ^ 2 ≤
        3 * P * (∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2) := by
    intro t
    have hcs := ExpSums.norm_sum_sq_le_card_mul Y
      (fun p => (a p / (p : ℂ)) *
        ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ))
    have hterm : (∑ p ∈ Y,
        ‖(a p / (p : ℂ)) *
          ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖ ^ 2) =
        ∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [norm_mul, Circle.norm_coe, mul_one, norm_div,
        Complex.norm_natCast, div_pow]
    rw [hterm] at hcs
    exact hcs.trans (mul_le_mul_of_nonneg_right hcard hmass0)
  calc
    _ ≤ ∑ _t ∈ 𝒯,
        (3 * P * (∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2)) :=
      Finset.sum_le_sum fun t ht => hpoint t
    _ = 3 * (𝒯.card : ℝ) * P *
        (∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      push_cast
      ring

/-- Large-`P` specialization of `balanced_raw_contour_bound`.  The returned
`x₀` is the maximum of four recorded thresholds: activation of the uncapped
zero-free width, absorption of the `q² exp(-q/2)` tail, absorption of the
prime-power tail, and `q ≤ x/2`. -/
theorem exists_balanced_raw_contour_bound_of_large_log
    {theta m : ℝ} (h : ZeroFreeRegionDataH theta m)
    (htheta1 : theta ≤ 1) (hm : m ≤ 2) :
    ∃ x₀ C : ℝ, 1 ≤ x₀ ∧ 1 ≤ C ∧ ∀ (P T u : ℝ),
      2 ≤ P → 1 ≤ T → 1 ≤ |u| → |u| ≤ 4 * Real.pi * T →
      x₀ ≤ Real.log P →
      let Z := zeroFreeRegionHeightHMax theta T P
      let eta := zeroFreeRegionEtaH theta h.eta0 Z
      let M := zeroFreeRegionRegularBoundH m h.M0 Z
      let c := 1 + 1 / Real.log (2 * P)
      let w := Real.log (2 * Z)
      (M + 1) *
          (P ^ (1 - eta / 2) +
            P ^ c * Real.log (2 * P) / (Z - |u|) +
            P ^ c / Z ^ 2 + Real.sqrt P * Real.log (4 * P)) ≤
        C * P * w ^ 2 * Real.exp (-(Real.log P / (2 * w ^ theta))) := by
  have htheta0 : 0 < theta := h.theta_pos
  have hetaLim : Tendsto (fun q : ℝ => q ^ (-theta)) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop htheta0
  have hetaEvent : ∀ᶠ q : ℝ in atTop, q ^ (-theta) < h.eta0 :=
    hetaLim.eventually_lt_const h.eta0_pos
  rw [Filter.eventually_atTop] at hetaEvent
  obtain ⟨qeta, hqeta⟩ := hetaEvent
  obtain ⟨qpoly, hqpoly1, hqpoly⟩ :=
    exists_rpow_mul_exp_neg_le_one (2 : ℝ) (1 / 2) (by norm_num)
  obtain ⟨xpoly, hxpoly1, hxpoly⟩ :=
    exists_rpow_mul_exp_neg_le_one (1 : ℝ) (1 / 4) (by norm_num)
  have hrpos : 0 < 1 / (1 + theta) :=
    one_div_pos.mpr (by linarith)
  have hrone : 1 / (1 + theta) < 1 := by
    rw [div_lt_one (by linarith : 0 < 1 + theta)]
    linarith
  obtain ⟨xhalf, hxhalf1, hxhalf⟩ :=
    exists_rpow_le_half_id (1 / (1 + theta)) hrpos hrone
  let Q : ℝ := max 1 (max qeta qpoly)
  let x₀ : ℝ := max 1 (max xpoly (max xhalf (Q ^ (1 + theta))))
  let C : ℝ := (h.M0 + 1) * (4 + 5 * Real.exp 1)
  have hC : 1 ≤ C := by
    dsimp only [C]
    have he : 1 ≤ Real.exp 1 := (Real.one_le_exp_iff).2 (by norm_num)
    nlinarith [h.one_le_M0]
  refine ⟨x₀, C, le_max_left _ _, hC, ?_⟩
  intro P T u hP hT hu1 huT hxlarge
  let x : ℝ := Real.log P
  let q : ℝ := x ^ (1 / (1 + theta))
  let Z : ℝ := zeroFreeRegionHeightHMax theta T P
  let w : ℝ := Real.log (2 * Z)
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hxlarge
  have hx0 : 0 < x := by linarith
  have hq0 : 0 < q := Real.rpow_pos_of_pos hx0 _
  have hQ1 : 1 ≤ Q := le_max_left _ _
  have hQ0 : 0 ≤ Q := by linarith
  have hQpow : Q ^ (1 + theta) ≤ x := by
    exact le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hxlarge))
  have hqbal : q ^ (1 + theta) = x := by
    dsimp only [q]
    exact balancing_rpow_pow theta x htheta0 hx0.le
  have hQq : Q ≤ q := by
    rw [← Real.rpow_le_rpow_iff hQ0 hq0.le (by linarith : 0 < 1 + theta)]
    rw [hqbal]
    exact hQpow
  have hq1 : 1 ≤ q := le_trans hQ1 hQq
  have hqeta' : qeta ≤ q :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hQq)
  have hqpoly' : qpoly ≤ q :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hQq)
  have hxpoly' : xpoly ≤ x :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) hxlarge)
  have hxhalf' : xhalf ≤ x :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hxlarge))
  have hZexp : Real.exp q ≤ Z := by
    dsimp only [Z, zeroFreeRegionHeightHMax, q, x]
    exact le_max_right _ _
  have hZ0 : 0 < Z := lt_of_lt_of_le (Real.exp_pos q) hZexp
  have hwq : q ≤ w := by
    dsimp only [w]
    have hmono := Real.log_le_log (Real.exp_pos q)
      (show Real.exp q ≤ 2 * Z by linarith)
    simpa using hmono
  have hetaPow : w ^ (-theta) ≤ h.eta0 := by
    have hqw : w ^ (-theta) ≤ q ^ (-theta) :=
      Real.rpow_le_rpow_of_nonpos hq0 hwq (by linarith : -theta ≤ 0)
    exact hqw.trans (le_of_lt (hqeta q hqeta'))
  have hetaEq : zeroFreeRegionEtaH theta h.eta0 Z = w ^ (-theta) := by
    dsimp only [zeroFreeRegionEtaH]
    exact min_eq_right hetaPow
  have huZ : |u| ≤ Z / 2 := by
    have hbase : 8 * Real.pi * T ≤ Z := by
      dsimp only [Z, zeroFreeRegionHeightHMax]
      exact le_max_left _ _
    linarith
  have hqx : q ≤ x / 2 := hxhalf x hxhalf'
  have hqpolyFinal : q ^ (2 : ℝ) * Real.exp (-(1 / 2) * q) ≤ 1 :=
    hqpoly q hqpoly'
  have hxpolyFinal : x * Real.exp (-(1 / 4) * x) ≤ 1 := by
    have hh := hxpoly x hxpoly'
    simpa only [Real.rpow_one] using hh
  have hcore := balanced_raw_contour_bound theta m h.eta0 h.M0 P u Z x q w
    hP htheta0 htheta1 h.one_le_M0 hm rfl hqbal hq1 hZexp rfl
    hetaEq huZ hqx hqpolyFinal hxpolyFinal
  simpa only [Z, w, C] using hcore

set_option maxHeartbeats 2500000

/-- The long-polynomial part of the three-regime envelope.  The short
polynomial range is intentionally excluded here: it is paid for directly by
`prime_large_values_trivial` in the final theorem. -/
theorem exists_balanced_long_error_envelope
    {theta theta' m : ℝ} (h : ZeroFreeRegionDataH theta m)
    (hgap : theta < theta') (htheta' : theta' ≤ 1) (hm : m ≤ 2) :
    ∃ x₀ D : ℝ, 1 ≤ x₀ ∧ 1 ≤ D ∧ ∀ (P T u n : ℝ),
      2 ≤ P → 1 ≤ T → 1 ≤ |u| → |u| ≤ 4 * Real.pi * T →
      0 ≤ n → n ≤ 2 * T + 1 → x₀ ≤ Real.log P →
      (Real.log (2 * T)) ^ theta' < Real.log P →
      let Z := zeroFreeRegionHeightHMax theta T P
      let eta := zeroFreeRegionEtaH theta h.eta0 Z
      let M := zeroFreeRegionRegularBoundH m h.M0 Z
      let c := 1 + 1 / Real.log (2 * P)
      n * (M + 1) *
          (P ^ (1 - eta / 2) +
            P ^ c * Real.log (2 * P) / (Z - |u|) +
            P ^ c / Z ^ 2 + Real.sqrt P * Real.log (4 * P)) ≤
        D * P * (1 + n * primeLargeValuesDecay theta' P T) := by
  have htheta0 : 0 < theta := h.theta_pos
  have htheta'0 : 0 < theta' := lt_trans htheta0 hgap
  have htheta1 : theta ≤ 1 := le_trans hgap.le htheta'
  obtain ⟨x₀, C, hx₀1, hC1, hraw⟩ :=
    exists_balanced_raw_contour_bound_of_large_log h htheta1 hm
  let cI : ℝ := Real.log (8 * Real.pi)
  obtain ⟨y₁, hy₁1, hy₁⟩ :=
    exists_shifted_rpow_le theta theta' cI 2 hgap htheta0.le (by norm_num)
  let YI : ℝ := max y₁ |cI|
  have hYI1 : 1 ≤ YI := le_trans hy₁1 (le_max_left _ _)
  have hcIYI : |cI| ≤ YI := le_max_right _ _
  let beta : ℝ := 1 + theta - theta'
  have hbeta0 : 0 < beta := by dsimp only [beta]; linarith
  have hbeta1 : beta < 1 := by dsimp only [beta]; linarith
  let KI : ℝ := 6 * 6 ^ theta'
  obtain ⟨qexp, hqexp1, hqexp⟩ :=
    exists_shifted_rpow_le beta 1 0 KI hbeta1 hbeta0.le (by
      dsimp only [KI]
      positivity)
  obtain ⟨qpoly, hqpoly1, hqpoly⟩ :=
    exists_rpow_mul_exp_neg_le_one (2 : ℝ) (1 / 6) (by norm_num)
  let Q : ℝ := max 1 (max (2 * Real.log 2) (max qexp qpoly))
  have hQ1 : 1 ≤ Q := le_max_left _ _
  have hQ0 : 0 ≤ Q := by linarith
  have htwoQ : 2 * Real.log 2 ≤ Q :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hqexpQ : qexp ≤ Q :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have hqpolyQ : qpoly ≤ Q :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  let B : ℝ := (Q ^ (1 + theta)) ^ (1 / theta')
  have hB0 : 0 ≤ B := Real.rpow_nonneg (Real.rpow_nonneg hQ0 _) _
  let DI : ℝ := (Real.exp YI + 1) * C * (YI + |cI|) ^ 2
  let DII : ℝ := (Real.exp B + 1) * C * (Q + Real.log 2) ^ 2
  let D : ℝ := 1 + DI + DII + 100 * C
  have hDI0 : 0 ≤ DI := by dsimp only [DI]; positivity
  have hDII0 : 0 ≤ DII := by dsimp only [DII]; positivity
  have hD : 1 ≤ D := by
    dsimp only [D]
    have hC0 : 0 ≤ C := by linarith
    linarith
  refine ⟨x₀, D, hx₀1, hD, ?_⟩
  intro P T u n hP hT hu1 huT hn0 hncard hxlarge hlong
  let x : ℝ := Real.log P
  let y : ℝ := Real.log (2 * T)
  let q : ℝ := x ^ (1 / (1 + theta))
  let Z : ℝ := zeroFreeRegionHeightHMax theta T P
  let w : ℝ := Real.log (2 * Z)
  let eta : ℝ := zeroFreeRegionEtaH theta h.eta0 Z
  let M : ℝ := zeroFreeRegionRegularBoundH m h.M0 Z
  let c : ℝ := 1 + 1 / Real.log (2 * P)
  let Raw : ℝ := P ^ (1 - eta / 2) +
    P ^ c * Real.log (2 * P) / (Z - |u|) +
    P ^ c / Z ^ 2 + Real.sqrt P * Real.log (4 * P)
  have hx1 : 1 ≤ x := by
    dsimp only [x]
    exact le_trans hx₀1 hxlarge
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by
    dsimp only [y]
    exact Real.log_pos (by linarith)
  have hq0 : 0 < q := Real.rpow_pos_of_pos hx0 _
  have hqbal : q ^ (1 + theta) = x := by
    dsimp only [q]
    exact balancing_rpow_pow theta x htheta0 hx0.le
  have hraw' : (M + 1) * Raw ≤
      C * P * w ^ 2 * Real.exp (-(x / (2 * w ^ theta))) := by
    have hh := hraw P T u hP hT hu1 huT hxlarge
    simpa only [x, Z, w, eta, M, c, Raw] using hh
  have hP0 : 0 ≤ P := by linarith
  have hdecay0 : 0 ≤ primeLargeValuesDecay theta' P T := by
    dsimp only [primeLargeValuesDecay]
    positivity
  have hbase : D * P ≤ D * P * (1 + n * primeLargeValuesDecay theta' P T) := by
    have hfac : 1 ≤ 1 + n * primeLargeValuesDecay theta' P T :=
      le_add_of_nonneg_right (mul_nonneg hn0 hdecay0)
    exact le_mul_of_one_le_right (mul_nonneg (by linarith [hD]) hP0) hfac
  have hTexp : Real.exp y = 2 * T := by
    dsimp only [y]
    rw [Real.exp_log (by linarith : 0 < 2 * T)]
  by_cases hI : Real.exp q ≤ 8 * Real.pi * T
  · have hZeq : Z = 8 * Real.pi * T := by
      dsimp only [Z, zeroFreeRegionHeightHMax]
      exact max_eq_left hI
    have hwEq : w = y + cI := by
      dsimp only [w, y, cI]
      rw [hZeq]
      have h2T0 : 2 * T ≠ 0 := by positivity
      have h8pi0 : 8 * Real.pi ≠ 0 := by positivity
      rw [show 2 * (8 * Real.pi * T) = (2 * T) * (8 * Real.pi) by ring,
        Real.log_mul h2T0 h8pi0]
    by_cases hylarge : YI ≤ y
    · have hpowI := hy₁ y (le_trans (le_max_left _ _) hylarge)
      have hmain : x / y ^ theta' ≤ x / (2 * w ^ theta) := by
        have hyPow0 : 0 < y ^ theta' := Real.rpow_pos_of_pos hy0 _
        have hwPow0 : 0 < w ^ theta := by
          rw [hwEq]
          have hwpos : 0 < y + cI := by
            rw [← hwEq]
            dsimp only [w]
            exact Real.log_pos (by
              rw [hZeq]
              nlinarith [Real.pi_gt_three])
          exact Real.rpow_pos_of_pos hwpos _
        rw [div_le_div_iff₀ hyPow0 (by positivity)]
        rw [hwEq]
        nlinarith [mul_le_mul_of_nonneg_left hpowI hx0.le]
      have hexpI : Real.exp (-(x / (2 * w ^ theta))) ≤
          Real.exp (-(x / y ^ theta')) := by
        rw [Real.exp_le_exp]
        linarith
      have hwY : w ^ 2 ≤ 4 * y ^ 2 := by
        have hcIy : |cI| ≤ y := by
          exact le_trans hcIYI hylarge
        have hwAbs : |w| ≤ 2 * y := by
          rw [hwEq]
          have := abs_add_le y cI
          rw [abs_of_pos hy0] at this
          linarith
        have habs0 : 0 ≤ |w| := abs_nonneg _
        nlinarith [mul_nonneg habs0 (sub_nonneg.mpr hwAbs), sq_abs w]
      have hpoint : (M + 1) * Raw ≤
          4 * C * P * primeLargeValuesDecay theta' P T := by
        dsimp only [primeLargeValuesDecay]
        calc
          (M + 1) * Raw ≤ C * P * w ^ 2 *
              Real.exp (-(x / (2 * w ^ theta))) := hraw'
          _ ≤ C * P * (4 * y ^ 2) * Real.exp (-(x / y ^ theta')) := by
            gcongr
          _ = 4 * C * P *
              (Real.exp (-(Real.log P / (Real.log (2 * T)) ^ theta')) *
                (Real.log (2 * T)) ^ 2) := by
            dsimp only [x, y]
            ring
      have hscaled := mul_le_mul_of_nonneg_left hpoint hn0
      calc
        n * (M + 1) * Raw = n * ((M + 1) * Raw) := by ring
          _ ≤ n * (4 * C * P * primeLargeValuesDecay theta' P T) := hscaled
          _ ≤ D * P * (1 + n * primeLargeValuesDecay theta' P T) := by
            have h4C : 4 * C ≤ D := by
              change 4 * C ≤ 1 + DI + DII + 100 * C
              linarith
            calc
              n * (4 * C * P * primeLargeValuesDecay theta' P T) =
                  (4 * C) * P * (n * primeLargeValuesDecay theta' P T) := by ring
              _ ≤ D * P * (n * primeLargeValuesDecay theta' P T) := by gcongr
              _ ≤ D * P * (1 + n * primeLargeValuesDecay theta' P T) := by
                gcongr
                linarith
    · have hylt : y < YI := lt_of_not_ge hylarge
      have hnBound : n ≤ Real.exp YI + 1 := by
        rw [← hTexp] at hncard
        have := Real.exp_le_exp.mpr hylt.le
        linarith
      have hwBound : w ^ 2 ≤ (YI + |cI|) ^ 2 := by
        have hw0 : 0 ≤ w := by
          dsimp only [w]
          apply Real.log_nonneg
          rw [hZeq]
          have hpi := Real.pi_gt_three
          nlinarith only [hpi, hT]
        have hwle : w ≤ YI + |cI| := by
          rw [hwEq]
          linarith [le_abs_self cI]
        simpa only [pow_two] using mul_self_le_mul_self hw0 hwle
      have hwpos : 0 < w := by
        dsimp only [w]
        apply Real.log_pos
        rw [hZeq]
        have hpi := Real.pi_gt_three
        nlinarith only [hpi, hT]
      have hexpOne : Real.exp (-(x / (2 * w ^ theta))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact neg_nonpos.mpr (div_nonneg hx0.le
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hwpos.le theta)))
      have hsmall : n * (M + 1) * Raw ≤ DI * P := by
        have hs := mul_le_mul_of_nonneg_left hraw' hn0
        dsimp only [DI]
        calc
          n * (M + 1) * Raw = n * ((M + 1) * Raw) := by ring
          _ ≤ n * (C * P * w ^ 2 * Real.exp (-(x / (2 * w ^ theta)))) := hs
          _ ≤ (Real.exp YI + 1) *
              (C * P * w ^ 2 * Real.exp (-(x / (2 * w ^ theta)))) := by
            have hinner0 : 0 ≤ C * P * w ^ 2 *
                Real.exp (-(x / (2 * w ^ theta))) :=
              mul_nonneg
                (mul_nonneg (mul_nonneg (by linarith : 0 ≤ C) hP0) (sq_nonneg w))
                (Real.exp_pos _).le
            exact mul_le_mul_of_nonneg_right hnBound hinner0
          _ ≤ (Real.exp YI + 1) *
              (C * P * (YI + |cI|) ^ 2 *
                Real.exp (-(x / (2 * w ^ theta)))) := by
            gcongr
          _ ≤ (Real.exp YI + 1) * (C * P * (YI + |cI|) ^ 2 * 1) := by
            gcongr
          _ = ((Real.exp YI + 1) * C * (YI + |cI|) ^ 2) * P := by ring
      calc
        n * (M + 1) * Raw ≤ DI * P := hsmall
        _ ≤ D * P := by
          have hDI : DI ≤ D := by
            change DI ≤ 1 + DI + DII + 100 * C
            linarith [hC1]
          gcongr
        _ ≤ D * P * (1 + n * primeLargeValuesDecay theta' P T) := hbase

  · have hII : 8 * Real.pi * T ≤ Real.exp q := le_of_not_ge hI
    have hZeq : Z = Real.exp q := by
      dsimp only [Z, zeroFreeRegionHeightHMax]
      exact max_eq_right hII
    have hwEq : w = q + Real.log 2 := by
      dsimp only [w]
      rw [hZeq, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (Real.exp_pos q).ne', Real.log_exp]
      ring
    by_cases hqlarge : Q ≤ q
    · have hlog2q : Real.log 2 ≤ q / 2 := by
        have htwo : 2 * Real.log 2 ≤ q := htwoQ.trans hqlarge
        linarith
      have hwUpper : w ≤ (3 / 2 : ℝ) * q := by rw [hwEq]; linarith
      have hw0 : 0 < w := by rw [hwEq]; positivity
      have hwtheta : w ^ theta ≤ (3 / 2 : ℝ) * q ^ theta := by
        have hmono := Real.rpow_le_rpow hw0.le hwUpper htheta0.le
        have hmul : ((3 / 2 : ℝ) * q) ^ theta =
            (3 / 2 : ℝ) ^ theta * q ^ theta := by
          rw [Real.mul_rpow (by norm_num) hq0.le]
        rw [hmul] at hmono
        have hconst : (3 / 2 : ℝ) ^ theta ≤ 3 / 2 :=
          Real.rpow_le_self_of_one_le (by norm_num) htheta1
        exact hmono.trans (mul_le_mul_of_nonneg_right hconst
          (Real.rpow_nonneg hq0.le theta))
      have hmainII : q / 3 ≤ x / (2 * w ^ theta) := by
        have hqtheta0 : 0 < q ^ theta := Real.rpow_pos_of_pos hq0 _
        have hwtheta0 : 0 < w ^ theta := Real.rpow_pos_of_pos hw0 _
        have hxform : x = q * q ^ theta := by
          rw [← hqbal, show 1 + theta = theta + 1 by ring,
            Real.rpow_add hq0, Real.rpow_one]
          ring
        rw [hxform]
        apply (le_div_iff₀ (by positivity : 0 < 2 * w ^ theta)).2
        calc
          q / 3 * (2 * w ^ theta) = (2 / 3 * q) * w ^ theta := by ring
          _ ≤ (2 / 3 * q) * ((3 / 2) * q ^ theta) :=
            mul_le_mul_of_nonneg_left hwtheta (by positivity)
          _ = q * q ^ theta := by ring
      have hexpMain : Real.exp (-(x / (2 * w ^ theta))) ≤
          Real.exp (-(q / 3)) := by
        rw [Real.exp_le_exp]
        linarith
      by_cases hyq : y < q / 6
      · have hnBound : n ≤ 2 * Real.exp y := by
          rw [← hTexp] at hncard
          have hey : 1 ≤ Real.exp y := (Real.one_le_exp_iff).2 hy0.le
          linarith
        have heyq : Real.exp y ≤ Real.exp (q / 6) :=
          Real.exp_le_exp.mpr hyq.le
        have hwSq : w ^ 2 ≤ (9 / 4 : ℝ) * q ^ (2 : ℝ) := by
          calc
            w ^ 2 ≤ ((3 / 2 : ℝ) * q) ^ 2 :=
              (sq_le_sq₀ hw0.le (by positivity)).2 hwUpper
            _ = (9 / 4 : ℝ) * q ^ (2 : ℝ) := by
              rw [Real.rpow_two]
              ring
        have hqpoly' : q ^ (2 : ℝ) * Real.exp (-(q / 6)) ≤ 1 := by
          have hqp := hqpoly q (hqpolyQ.trans hqlarge)
          convert hqp using 1 <;> ring
        have hexpcancel : Real.exp (q / 6) * Real.exp (-(q / 3)) =
            Real.exp (-(q / 6)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have hsmall : n * (M + 1) * Raw ≤ 5 * C * P := by
          have hs := mul_le_mul_of_nonneg_left hraw' hn0
          have hnQ : n ≤ 2 * Real.exp (q / 6) :=
            hnBound.trans (mul_le_mul_of_nonneg_left heyq (by norm_num))
          calc
            n * (M + 1) * Raw = n * ((M + 1) * Raw) := by ring
            _ ≤ n * (C * P * w ^ 2 *
                Real.exp (-(x / (2 * w ^ theta)))) := hs
            _ ≤ (2 * Real.exp (q / 6)) *
                (C * P * ((9 / 4) * q ^ (2 : ℝ)) * Real.exp (-(q / 3))) := by
              gcongr
            _ = (9 / 2) * C * P * q ^ (2 : ℝ) *
                (Real.exp (q / 6) * Real.exp (-(q / 3))) := by ring
            _ = (9 / 2) * C * P *
                (q ^ (2 : ℝ) * Real.exp (-(q / 6))) := by
              rw [hexpcancel]
              ring
            _ ≤ (9 / 2) * C * P * 1 := by
              exact mul_le_mul_of_nonneg_left hqpoly' (by positivity)
            _ ≤ 5 * C * P := by
              have hCP : 0 ≤ C * P := mul_nonneg (by linarith) hP0
              simpa only [mul_one, mul_assoc] using
                (mul_le_mul_of_nonneg_right (show (9 / 2 : ℝ) ≤ 5 by norm_num) hCP)
        calc
          n * (M + 1) * Raw ≤ 5 * C * P := hsmall
          _ ≤ D * P := by
            have h5C : 5 * C ≤ D := by
              change 5 * C ≤ 1 + DI + DII + 100 * C
              linarith
            gcongr
          _ ≤ D * P * (1 + n * primeLargeValuesDecay theta' P T) := hbase
      · have hyq' : q / 6 ≤ y := le_of_not_gt hyq
        have hwY : w ^ 2 ≤ 81 * y ^ 2 := by
          have hwle : w ≤ 9 * y := by
            rw [hwEq]
            have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
            linarith
          calc
            w ^ 2 ≤ (9 * y) ^ 2 := (sq_le_sq₀ hw0.le (by positivity)).2 hwle
            _ = 81 * y ^ 2 := by ring
        have hKIq : KI * q ^ beta ≤ q := by
          have := hqexp q (hqexpQ.trans hqlarge)
          simpa only [add_zero, Real.rpow_one] using this
        have hyPow : (q / 6) ^ theta' ≤ y ^ theta' :=
          Real.rpow_le_rpow (by positivity) hyq' htheta'0.le
        have hquot : x / y ^ theta' ≤ q / 6 := by
          have hyPow0 : 0 < y ^ theta' := Real.rpow_pos_of_pos hy0 _
          have hqPow0 : 0 < q ^ theta' := Real.rpow_pos_of_pos hq0 _
          have hscale : (q / 6) ^ theta' = q ^ theta' / (6 : ℝ) ^ theta' := by
            rw [Real.div_rpow hq0.le (by norm_num : (0 : ℝ) ≤ 6)]
          have hxform : x = q ^ beta * q ^ theta' := by
            rw [← hqbal, ← Real.rpow_add hq0]
            congr 1
            dsimp only [beta]
            ring
          rw [hxform]
          have hden : q ^ theta' / (6 : ℝ) ^ theta' ≤ y ^ theta' := by
            rw [← hscale]
            exact hyPow
          have h6pos : 0 < (6 : ℝ) ^ theta' :=
            Real.rpow_pos_of_pos (by norm_num) _
          have hden' : q ^ theta' ≤ (6 : ℝ) ^ theta' * y ^ theta' := by
            have hh := (div_le_iff₀ h6pos).mp hden
            simpa only [mul_comm] using hh
          have hcoef : (6 : ℝ) ^ theta' * q ^ beta ≤ q / 6 := by
            apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 6)).2
            dsimp only [KI] at hKIq
            convert hKIq using 1 <;> ring
          apply (div_le_iff₀ hyPow0).2
          calc
            q ^ beta * q ^ theta' ≤
                q ^ beta * ((6 : ℝ) ^ theta' * y ^ theta') :=
              mul_le_mul_of_nonneg_left hden' (Real.rpow_nonneg hq0.le beta)
            _ = ((6 : ℝ) ^ theta' * q ^ beta) * y ^ theta' := by ring
            _ ≤ (q / 6) * y ^ theta' :=
              mul_le_mul_of_nonneg_right hcoef hyPow0.le
        have hexpTarget : Real.exp (-(x / (2 * w ^ theta))) ≤
            Real.exp (-(x / y ^ theta')) := by
          rw [Real.exp_le_exp]
          linarith [hmainII, hquot]
        have hpoint : (M + 1) * Raw ≤
            81 * C * P * primeLargeValuesDecay theta' P T := by
          dsimp only [primeLargeValuesDecay]
          calc
            (M + 1) * Raw ≤ C * P * w ^ 2 *
                Real.exp (-(x / (2 * w ^ theta))) := hraw'
            _ ≤ C * P * (81 * y ^ 2) * Real.exp (-(x / y ^ theta')) := by
              gcongr
            _ = 81 * C * P *
                (Real.exp (-(Real.log P / (Real.log (2 * T)) ^ theta')) *
                  (Real.log (2 * T)) ^ 2) := by
              dsimp only [x, y]
              ring
        have hs := mul_le_mul_of_nonneg_left hpoint hn0
        calc
          n * (M + 1) * Raw = n * ((M + 1) * Raw) := by ring
          _ ≤ n * (81 * C * P * primeLargeValuesDecay theta' P T) := hs
          _ ≤ D * P * (1 + n * primeLargeValuesDecay theta' P T) := by
            have h81C : 81 * C ≤ D := by
              change 81 * C ≤ 1 + DI + DII + 100 * C
              linarith
            calc
              n * (81 * C * P * primeLargeValuesDecay theta' P T) =
                  (81 * C) * P * (n * primeLargeValuesDecay theta' P T) := by ring
              _ ≤ D * P * (n * primeLargeValuesDecay theta' P T) := by gcongr
              _ ≤ D * P * (1 + n * primeLargeValuesDecay theta' P T) := by
                gcongr
                linarith
    · have hqlt : q < Q := lt_of_not_ge hqlarge
      have hxQ : x ≤ Q ^ (1 + theta) := by
        rw [← hqbal]
        exact Real.rpow_le_rpow hq0.le hqlt.le (by linarith)
      have hyB : y ≤ B := by
        have hyPow : y ^ theta' ≤ Q ^ (1 + theta) :=
          (le_of_lt hlong).trans hxQ
        dsimp only [B]
        rw [← Real.rpow_le_rpow_iff hy0.le
          (Real.rpow_nonneg (Real.rpow_nonneg hQ0 _) _) htheta'0]
        rw [← Real.rpow_mul (Real.rpow_nonneg hQ0 _)]
        have hne : theta' ≠ 0 := htheta'0.ne'
        rw [one_div, inv_mul_cancel₀ hne, Real.rpow_one]
        exact hyPow
      have hnBound : n ≤ Real.exp B + 1 := by
        rw [← hTexp] at hncard
        have := Real.exp_le_exp.mpr hyB
        linarith
      have hwBound : w ^ 2 ≤ (Q + Real.log 2) ^ 2 := by
        have hw0 : 0 ≤ w := by
          rw [hwEq]
          exact add_nonneg hq0.le (Real.log_pos (by norm_num)).le
        have hwle : w ≤ Q + Real.log 2 := by
          rw [hwEq]
          simpa only [add_comm] using add_le_add_right hqlt.le (Real.log 2)
        have hright0 : 0 ≤ Q + Real.log 2 :=
          add_nonneg hQ0 (Real.log_pos (by norm_num)).le
        rw [pow_two, pow_two]
        exact mul_self_le_mul_self hw0 hwle
      have hwpos : 0 < w := by
        rw [hwEq]
        have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
        linarith only [hq0, hl]
      have hexpOne : Real.exp (-(x / (2 * w ^ theta))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact neg_nonpos.mpr (div_nonneg hx0.le
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hwpos.le theta)))
      have hsmall : n * (M + 1) * Raw ≤ DII * P := by
        have hs := mul_le_mul_of_nonneg_left hraw' hn0
        dsimp only [DII]
        calc
          n * (M + 1) * Raw = n * ((M + 1) * Raw) := by ring
          _ ≤ n * (C * P * w ^ 2 * Real.exp (-(x / (2 * w ^ theta)))) := hs
          _ ≤ (Real.exp B + 1) *
              (C * P * w ^ 2 * Real.exp (-(x / (2 * w ^ theta)))) := by
            have hinner0 : 0 ≤ C * P * w ^ 2 *
                Real.exp (-(x / (2 * w ^ theta))) :=
              mul_nonneg
                (mul_nonneg (mul_nonneg (by linarith : 0 ≤ C) hP0) (sq_nonneg w))
                (Real.exp_pos _).le
            exact mul_le_mul_of_nonneg_right hnBound hinner0
          _ ≤ (Real.exp B + 1) *
              (C * P * (Q + Real.log 2) ^ 2 *
                Real.exp (-(x / (2 * w ^ theta)))) := by gcongr
          _ ≤ (Real.exp B + 1) * (C * P * (Q + Real.log 2) ^ 2 * 1) := by
            gcongr
          _ = ((Real.exp B + 1) * C * (Q + Real.log 2) ^ 2) * P := by ring
      calc
        n * (M + 1) * Raw ≤ DII * P := hsmall
        _ ≤ D * P := by
          have hDII : DII ≤ D := by
            change DII ≤ 1 + DI + DII + 100 * C
            linarith [hC1]
          gcongr
        _ ≤ D * P * (1 + n * primeLargeValuesDecay theta' P T) := hbase

/-- Regime 0 and the bounded-`P` transition range, both discharged by the
same Cauchy--Schwarz estimate. -/
theorem exists_trivial_three_regime_bound
    (theta' x₀ : ℝ) (htheta'0 : 0 < theta') (htheta'1 : theta' ≤ 1)
    (hx₀ : 1 ≤ x₀) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : ℕ) (Y : Finset ℕ) (a : ℕ → ℂ)
      (T : ℝ) (𝒯 : Finset ℝ),
      2 ≤ P → (∀ p ∈ Y, p ≤ 2 * P) → 1 ≤ T →
      (∀ t ∈ 𝒯, |t| ≤ T) →
      (∀ t ∈ 𝒯, ∀ s ∈ 𝒯, t ≠ s → 1 ≤ |t - s|) →
      (Real.log P ≤ (Real.log (2 * T)) ^ theta' ∨
        (Real.log P < x₀ ∧ (Real.log (2 * T)) ^ theta' < Real.log P)) →
      ∑ t ∈ 𝒯, ‖∑ p ∈ Y, (a p / (p : ℂ)) *
          ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖ ^ 2 ≤
        C * (1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) *
          (∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2) *
          (P : ℝ) / Real.log P := by
  let B : ℝ := x₀ ^ (1 / theta')
  let Csmall : ℝ := 3 * (Real.exp B + 1) * x₀
  let C : ℝ := 1 + 12 * Real.exp 1 + Csmall
  have hB0 : 0 ≤ B := Real.rpow_nonneg (by linarith : 0 ≤ x₀) _
  have hCsmall0 : 0 ≤ Csmall := by dsimp only [Csmall]; positivity
  have hC : 1 ≤ C := by
    dsimp only [C]
    linarith [Real.exp_pos 1]
  refine ⟨C, hC, ?_⟩
  intro P Y a T 𝒯 hP hYrange hT hrange hsep hcase
  let x : ℝ := Real.log P
  let y : ℝ := Real.log (2 * T)
  let mass : ℝ := ∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2
  have hx0 : 0 < x := by
    dsimp only [x]
    exact Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hy0 : 0 < y := by
    dsimp only [y]
    exact Real.log_pos (by linarith)
  have hmass0 : 0 ≤ mass := by dsimp only [mass]; positivity
  have htriv := prime_large_values_trivial P Y a 𝒯 (by omega)
    (fun p hp => (hYrange p hp))
  have hcard := card_le_two_mul_add_one_of_one_separated T 𝒯 (by linarith)
    hrange hsep
  rcases hcase with hshort | hbounded
  · have hyPow0 : 0 < y ^ theta' := Real.rpow_pos_of_pos hy0 _
    have hratio : x / y ^ theta' ≤ 1 := (div_le_one hyPow0).2 hshort
    have hexpLower : Real.exp (-1) ≤ Real.exp (-(x / y ^ theta')) := by
      rw [Real.exp_le_exp]
      linarith
    have hySq : x ≤ 4 * y ^ 2 := by
      by_cases hy1 : 1 ≤ y
      · have hypowY : y ^ theta' ≤ y :=
          Real.rpow_le_self_of_one_le hy1 htheta'1
        have hxy : x ≤ y := hshort.trans hypowY
        have hyy : y ≤ y ^ 2 := by
          rw [pow_two]
          exact le_mul_of_one_le_left hy0.le hy1
        have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
        calc
          x ≤ y := hxy
          _ ≤ y ^ 2 := hyy
          _ ≤ 4 * y ^ 2 := by nlinarith
      · have hyle : y ≤ 1 := le_of_not_ge hy1
        have hypow1 : y ^ theta' ≤ 1 :=
          Real.rpow_le_one hy0.le hyle htheta'0.le
        have hx1 : x ≤ 1 := hshort.trans hypow1
        have hyhalf : 1 / 2 ≤ y := by
          dsimp only [y]
          have hlog := Real.log_two_gt_d9
          have hmono : Real.log 2 ≤ Real.log (2 * T) :=
            Real.log_le_log (by norm_num) (by linarith)
          linarith
        nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 2) hyhalf]
    have hfactor : 3 ≤ 12 * Real.exp 1 *
        (Real.exp (-(x / y ^ theta')) * y ^ 2 / x) := by
      have hexpProd : 1 ≤ Real.exp 1 * Real.exp (-(x / y ^ theta')) := by
        have := mul_le_mul_of_nonneg_left hexpLower (Real.exp_pos 1).le
        rw [← Real.exp_add] at this
        norm_num at this
        exact this
      have hyx : 1 / 4 ≤ y ^ 2 / x := by
        exact (le_div_iff₀ hx0).2 (by nlinarith)
      have hprod := mul_le_mul hexpProd hyx (by norm_num)
        (by positivity : 0 ≤ Real.exp 1 * Real.exp (-(x / y ^ theta')))
      have hprod' : (1 / 4 : ℝ) ≤
          (Real.exp 1 * Real.exp (-(x / y ^ theta'))) * (y ^ 2 / x) := by
        simpa only [one_mul] using hprod
      calc
        3 = 12 * (1 / 4 : ℝ) := by norm_num
        _ ≤ 12 * ((Real.exp 1 * Real.exp (-(x / y ^ theta'))) *
            (y ^ 2 / x)) := mul_le_mul_of_nonneg_left hprod' (by norm_num)
        _ = 12 * Real.exp 1 *
            (Real.exp (-(x / y ^ theta')) * y ^ 2 / x) := by ring
    have hcoef : 3 * (𝒯.card : ℝ) * P ≤
        C * (1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) * P / x := by
      have hcard0 : 0 ≤ (𝒯.card : ℝ) := by positivity
      have hdecayEq : primeLargeValuesDecay theta' P T =
          Real.exp (-(x / y ^ theta')) * y ^ 2 := by
        rfl
      rw [hdecayEq]
      have hC12 : 12 * Real.exp 1 ≤ C := by
        change 12 * Real.exp 1 ≤ 1 + 12 * Real.exp 1 + Csmall
        linarith
      have hnpart : 3 * (𝒯.card : ℝ) ≤
          C * ((𝒯.card : ℝ) *
            (Real.exp (-(x / y ^ theta')) * y ^ 2) / x) := by
        have hs := mul_le_mul_of_nonneg_left hfactor hcard0
        have hR0 : 0 ≤ (𝒯.card : ℝ) *
            (Real.exp (-(x / y ^ theta')) * y ^ 2) / x := by positivity
        calc
          3 * (𝒯.card : ℝ) = (𝒯.card : ℝ) * 3 := by ring
          _ ≤ (𝒯.card : ℝ) *
              (12 * Real.exp 1 *
                (Real.exp (-(x / y ^ theta')) * y ^ 2 / x)) := hs
          _ = 12 * Real.exp 1 * ((𝒯.card : ℝ) *
              (Real.exp (-(x / y ^ theta')) * y ^ 2) / x) := by ring
          _ ≤ C * ((𝒯.card : ℝ) *
              (Real.exp (-(x / y ^ theta')) * y ^ 2) / x) :=
            mul_le_mul_of_nonneg_right hC12 hR0
      have hP0 : 0 ≤ (P : ℝ) := by positivity
      apply (mul_le_mul_of_nonneg_right hnpart hP0).trans
      have hfac : (𝒯.card : ℝ) *
          (Real.exp (-(x / y ^ theta')) * y ^ 2) ≤
          1 + (𝒯.card : ℝ) *
            (Real.exp (-(x / y ^ theta')) * y ^ 2) := le_add_of_nonneg_left (by norm_num)
      have hxpos := hx0
      calc
        C * ((𝒯.card : ℝ) *
            (Real.exp (-(x / y ^ theta')) * y ^ 2) / x) * P ≤
            C * ((1 + (𝒯.card : ℝ) *
              (Real.exp (-(x / y ^ theta')) * y ^ 2)) / x) * P := by gcongr
        _ = C * (1 + (𝒯.card : ℝ) *
            (Real.exp (-(x / y ^ theta')) * y ^ 2)) * P / x := by field_simp
    have hscaled := mul_le_mul_of_nonneg_right hcoef hmass0
    calc
      _ ≤ 3 * (𝒯.card : ℝ) * P * mass := by simpa only [mass] using htriv
      _ ≤ (C * (1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) *
          P / x) * mass := hscaled
      _ = C * (1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) *
          mass * P / Real.log P := by dsimp only [x]; ring
  · obtain ⟨hxBound, hlong⟩ := hbounded
    have hyPow : y ^ theta' ≤ x₀ := (le_of_lt hlong).trans hxBound.le
    have hyB : y ≤ B := by
      dsimp only [B]
      rw [← Real.rpow_le_rpow_iff hy0.le (Real.rpow_nonneg (by linarith : 0 ≤ x₀) _)
        htheta'0]
      rw [← Real.rpow_mul (by linarith : 0 ≤ x₀)]
      have hne : theta' ≠ 0 := htheta'0.ne'
      rw [one_div, inv_mul_cancel₀ hne, Real.rpow_one]
      exact hyPow
    have hTexp : Real.exp y = 2 * T := by
      dsimp only [y]
      rw [Real.exp_log (by linarith : 0 < 2 * T)]
    have hn : (𝒯.card : ℝ) ≤ Real.exp B + 1 := by
      rw [← hTexp] at hcard
      have := Real.exp_le_exp.mpr hyB
      linarith
    have hcoef : 3 * (𝒯.card : ℝ) * P ≤
        C * (1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) * P / x := by
      have hCsmall : Csmall ≤ C := by
        change Csmall ≤ 1 + 12 * Real.exp 1 + Csmall
        nlinarith [Real.exp_pos 1]
      have hleft : 3 * (𝒯.card : ℝ) * x ≤ Csmall := by
        dsimp only [Csmall]
        have hxle : x ≤ x₀ := hxBound.le
        have hn0 : 0 ≤ (𝒯.card : ℝ) := by positivity
        calc
          3 * (𝒯.card : ℝ) * x ≤ 3 * (Real.exp B + 1) * x := by gcongr
          _ ≤ 3 * (Real.exp B + 1) * x₀ := by gcongr
      have hone : 1 ≤ 1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T :=
        le_add_of_nonneg_right (mul_nonneg (by positivity) (by
          dsimp only [primeLargeValuesDecay]; positivity))
      have hright : Csmall ≤ C *
          (1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) :=
        hCsmall.trans (le_mul_of_one_le_right (by positivity) hone)
      have hmain : 3 * (𝒯.card : ℝ) ≤ C *
          (1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) / x := by
        exact (le_div_iff₀ hx0).2 (hleft.trans hright)
      have hh := mul_le_mul_of_nonneg_right hmain (Nat.cast_nonneg P : (0 : ℝ) ≤ P)
      convert hh using 1 <;> ring
    have hscaled := mul_le_mul_of_nonneg_right hcoef hmass0
    calc
      _ ≤ 3 * (𝒯.card : ℝ) * P * mass := by simpa only [mass] using htriv
      _ ≤ (C * (1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) *
          P / x) * mass := hscaled
      _ = C * (1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) *
          mass * P / Real.log P := by dsimp only [x]; ring

end MoltResearch
