import MoltResearch.Discrepancy.ZetaLandauRadius

/-!
# A zero-free region from a parametrized zeta growth bound

This leaf carries out the Landau and `3-4-1` calculation at the radius

`R(t) = (log (log |t|) / (B * log |t|)) ^ (1 / a)`.

The centre is displaced to the right of one by
`R(t) / (V * log (log |t|))`.  The constant `V` is chosen after the compact
real-axis pole bound and is independent of `t`.
-/

namespace MoltResearch

namespace ExpSums

open Complex

/-- A near-one growth bound for zeta.  Only the substrip `3/4 ≤ σ ≤ 2`
is used by the zero-free-region argument. -/
structure ZetaGrowthBound (t₀ a B b B₀ : ℝ) : Prop where
  bound : ∀ σ t : ℝ, t₀ ≤ |t| → 1 - 1 / 4 ≤ σ → σ ≤ 2 →
    Real.log ‖riemannZeta ((σ : ℂ) + I * t)‖ ≤
      B * (max (1 - σ) 0) ^ a * Real.log |t| +
        b * Real.log (Real.log |t|) + B₀

/-- The Landau radius selected by a power-type growth bound. -/
noncomputable def zetaGrowthRadius (a B t : ℝ) : ℝ :=
  (Real.log (Real.log |t|) / (B * Real.log |t|)) ^ (1 / a)

/-- The asymptotic width, before its constant coefficient is chosen. -/
noncomputable def zetaGrowthWidth (a t : ℝ) : ℝ :=
  (Real.log (Real.log |t|)) ^ (1 / a - 1) /
    (Real.log |t|) ^ (1 / a)

theorem zetaGrowthRadius_div_loglog
    {a B t : ℝ} (ha : 0 < a) (hB : 0 < B)
    (hL : 0 < Real.log |t|) (hell : 0 < Real.log (Real.log |t|)) :
    zetaGrowthRadius a B t / Real.log (Real.log |t|) =
      B ^ (-1 / a) * zetaGrowthWidth a t := by
  have hB0 : 0 ≤ B := hB.le
  have hL0 : 0 ≤ Real.log |t| := hL.le
  have hell0 : 0 ≤ Real.log (Real.log |t|) := hell.le
  rw [zetaGrowthRadius, zetaGrowthWidth,
    Real.div_rpow hell0 (mul_nonneg hB0 hL0),
    Real.mul_rpow hB0 hL0, Real.rpow_sub hell]
  have hBpow : B ^ (1 / a) ≠ 0 := (Real.rpow_pos_of_pos hB _).ne'
  have hLpow : (Real.log |t|) ^ (1 / a) ≠ 0 :=
    (Real.rpow_pos_of_pos hL _).ne'
  have hellpow : (Real.log (Real.log |t|)) ^ (1 / a) ≠ 0 :=
    (Real.rpow_pos_of_pos hell _).ne'
  rw [show (-1 / a : ℝ) = -(1 / a) by ring, Real.rpow_neg hB0]
  rw [Real.rpow_one]
  field_simp

private theorem norm_le_exp_of_log_norm_le (z : ℂ) (U : ℝ)
    (h : Real.log ‖z‖ ≤ U) :
    ‖z‖ ≤ Real.exp U := by
  by_cases hz : z = 0
  · simp [hz, (Real.exp_pos U).le]
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [← Real.exp_log hn]
    exact Real.exp_le_exp.mpr h

/-- The `3-4-1` lower bound with an arbitrary logarithmic upper bound at
twice the height. -/
theorem zeta_norm_lower_341_of_log_upper
    (σ₀ t U : ℝ) (hσ : 1 < σ₀)
    (hU : Real.log ‖riemannZeta ((σ₀ : ℂ) + I * (2 * t))‖ ≤ U) :
    1 / ((1 + 1 / (σ₀ - 1)) ^ 3 * Real.exp U) ≤
      ‖riemannZeta ((σ₀ : ℂ) + I * t)‖ ^ 4 := by
  have hA : ‖riemannZeta (σ₀ : ℂ)‖ ≤ 1 + 1 / (σ₀ - 1) :=
    zeta_real_upper σ₀ hσ
  have hApos : 0 < 1 + 1 / (σ₀ - 1) := by
    have : 0 < σ₀ - 1 := by linarith
    positivity
  have htwice :
      ‖riemannZeta ((σ₀ : ℂ) + 2 * I * t)‖ ≤ Real.exp U := by
    rw [show (2 : ℂ) * I * (t : ℂ) = I * ((2 * t : ℝ) : ℂ) by
      push_cast
      ring]
    apply norm_le_exp_of_log_norm_le
    convert hU using 1 <;> push_cast <;> ring
  have h341 := zeta_341_prod_ge_one σ₀ t hσ
  rw [norm_mul, norm_mul, norm_pow, norm_pow] at h341
  let x := ‖riemannZeta (σ₀ : ℂ)‖
  let y := ‖riemannZeta ((σ₀ : ℂ) + I * t)‖
  let q := ‖riemannZeta ((σ₀ : ℂ) + 2 * I * t)‖
  have hx0 : 0 ≤ x := norm_nonneg _
  have hq0 : 0 ≤ q := norm_nonneg _
  have hchain : 1 ≤ (1 + 1 / (σ₀ - 1)) ^ 3 * y ^ 4 * Real.exp U := by
    calc
      1 ≤ x ^ 3 * y ^ 4 * q := h341
      _ ≤ (1 + 1 / (σ₀ - 1)) ^ 3 * y ^ 4 * q := by
        gcongr
      _ ≤ (1 + 1 / (σ₀ - 1)) ^ 3 * y ^ 4 * Real.exp U := by
        gcongr
  rw [div_le_iff₀ (mul_pos (pow_pos hApos 3) (Real.exp_pos U))]
  simpa only [y] using (show
    1 ≤ ‖riemannZeta ((σ₀ : ℂ) + I * t)‖ ^ 4 *
      ((1 + 1 / (σ₀ - 1)) ^ 3 * Real.exp U) by
        calc
          1 ≤ (1 + 1 / (σ₀ - 1)) ^ 3 * y ^ 4 * Real.exp U := hchain
          _ = y ^ 4 * ((1 + 1 / (σ₀ - 1)) ^ 3 * Real.exp U) := by ring)

private theorem neg_log_zeta_le_of_341
    (σ₀ t U : ℝ) (hσ : 1 < σ₀)
    (hU : Real.log ‖riemannZeta ((σ₀ : ℂ) + I * (2 * t))‖ ≤ U) :
    -Real.log ‖riemannZeta ((σ₀ : ℂ) + I * t)‖ ≤
      (3 * Real.log (1 + 1 / (σ₀ - 1)) + U) / 4 := by
  have hcne : riemannZeta ((σ₀ : ℂ) + I * t) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  have hcn : 0 < ‖riemannZeta ((σ₀ : ℂ) + I * t)‖ :=
    norm_pos_iff.mpr hcne
  have hA : 0 < 1 + 1 / (σ₀ - 1) := by
    have : 0 < σ₀ - 1 := by linarith
    positivity
  have hlower := zeta_norm_lower_341_of_log_upper σ₀ t U hσ hU
  have hden : 0 < (1 + 1 / (σ₀ - 1)) ^ 3 * Real.exp U := by positivity
  have hlog := Real.log_le_log (by positivity) hlower
  rw [Real.log_div (by norm_num) hden.ne', Real.log_one,
    Real.log_mul (pow_ne_zero 3 hA.ne') (Real.exp_ne_zero U),
    Real.log_pow, Real.log_exp, Real.log_pow] at hlog
  push_cast at hlog
  linarith

/-- A logarithmic growth budget for the Landau disc at height `τ`. -/
noncomputable def zetaGrowthLandauBudget
    (a B b B₀ R δ τ : ℝ) : ℝ :=
  max (B * R ^ a * Real.log (|τ| + R) +
      b * Real.log (Real.log (|τ| + R)) + B₀ +
      (3 * Real.log (1 + 1 / δ) +
        b * Real.log (Real.log |2 * τ|) + B₀) / 4) 0

private theorem zeta_growth_ratio_on_landau_disc
    {t₀ a B b B₀ R δ τ : ℝ}
    (h : ZetaGrowthBound t₀ a B b B₀)
    (ha : 1 < a) (hB : 0 < B) (hb : 0 ≤ b) (hB₀ : 0 ≤ B₀)
    (hR0 : 0 < R) (hRquarter : R ≤ 1 / 4)
    (hδ0 : 0 < δ) (hδquarter : δ ≤ 1 / 4)
    (ht : max t₀ 2 + R ≤ |τ|) :
    ∀ z ∈ Metric.closedBall (((1 + δ : ℝ) : ℂ) + I * τ) R,
      ‖riemannZeta z‖ ≤
        Real.exp (zetaGrowthLandauBudget a B b B₀ R δ τ) *
          ‖riemannZeta (((1 + δ : ℝ) : ℂ) + I * τ)‖ := by
  intro z hz
  let c : ℂ := (((1 + δ : ℝ) : ℂ) + I * τ)
  have hdist : ‖z - c‖ ≤ R := by
    rw [← dist_eq_norm]
    exact Metric.mem_closedBall.mp hz
  have hre : |z.re - (1 + δ)| ≤ R := by
    calc
      |z.re - (1 + δ)| = |(z - c).re| := by simp [c]
      _ ≤ ‖z - c‖ := Complex.abs_re_le_norm _
      _ ≤ R := hdist
  have him : |z.im - τ| ≤ R := by
    calc
      |z.im - τ| = |(z - c).im| := by simp [c]
      _ ≤ ‖z - c‖ := Complex.abs_im_le_norm _
      _ ≤ R := hdist
  have hzreLower : 1 - 1 / 4 ≤ z.re := by
    rw [abs_le] at hre
    linarith
  have hzreUpper : z.re ≤ 2 := by
    rw [abs_le] at hre
    linarith
  have hzimLower : max t₀ 2 ≤ |z.im| := by
    have hreverse : |τ| ≤ |z.im| + |z.im - τ| := by
      calc
        |τ| = |z.im - (z.im - τ)| := by ring_nf
        _ ≤ |z.im| + |z.im - τ| := abs_sub _ _
    linarith
  have hzimUpper : |z.im| ≤ |τ| + R := by
    calc
      |z.im| = |τ + (z.im - τ)| := by ring_nf
      _ ≤ |τ| + |z.im - τ| := abs_add_le _ _
      _ ≤ |τ| + R := by linarith
  have himPos : 0 < |z.im| := by
    have : 2 ≤ |z.im| := le_trans (le_max_right _ _) hzimLower
    linarith
  have htopPos : 0 < |τ| + R := by linarith [hzimUpper]
  have hlogIm : Real.log |z.im| ≤ Real.log (|τ| + R) :=
    Real.log_le_log himPos hzimUpper
  have hzimTwo : 2 ≤ |z.im| := le_trans (le_max_right _ _) hzimLower
  have htopTwo : 2 ≤ |τ| + R := le_trans hzimTwo hzimUpper
  have hlogImPos : 0 < Real.log |z.im| := Real.log_pos (by linarith)
  have hlogTopPos : 0 < Real.log (|τ| + R) := Real.log_pos (by linarith)
  have hloglogIm : Real.log (Real.log |z.im|) ≤
      Real.log (Real.log (|τ| + R)) :=
    Real.log_le_log hlogImPos hlogIm
  have hmax : max (1 - z.re) 0 ≤ R := by
    rw [max_le_iff]
    constructor
    · rw [abs_le] at hre
      linarith
    · exact hR0.le
  have hpow : (max (1 - z.re) 0) ^ a ≤ R ^ a :=
    Real.rpow_le_rpow (by positivity) hmax (by linarith)
  have hgrowth := h.bound z.re z.im
    (le_trans (le_max_left _ _) hzimLower) hzreLower hzreUpper
  have hzform : ((z.re : ℝ) : ℂ) + I * z.im = z := by
    apply Complex.ext <;> simp
  rw [hzform] at hgrowth
  have hupper : Real.log ‖riemannZeta z‖ ≤
      B * R ^ a * Real.log (|τ| + R) +
        b * Real.log (Real.log (|τ| + R)) + B₀ := by
    have hpowlog : B * (max (1 - z.re) 0) ^ a * Real.log |z.im| ≤
        B * R ^ a * Real.log (|τ| + R) := by
      have hBlog : 0 ≤ B * Real.log |z.im| := by positivity
      calc
        B * (max (1 - z.re) 0) ^ a * Real.log |z.im| =
            (max (1 - z.re) 0) ^ a * (B * Real.log |z.im|) := by ring
        _ ≤ R ^ a * (B * Real.log |z.im|) :=
          mul_le_mul_of_nonneg_right hpow hBlog
        _ = B * R ^ a * Real.log |z.im| := by ring
        _ ≤ B * R ^ a * Real.log (|τ| + R) := by
          gcongr
    linarith [mul_le_mul_of_nonneg_left hloglogIm hb]
  have hσ : 1 < 1 + δ := by linarith
  have hσ2 : 1 + δ ≤ 2 := by linarith
  have h2τ : t₀ ≤ |2 * τ| := by
    have hτlower : max t₀ 2 ≤ |τ| := by linarith
    have hτ0 : 0 ≤ |τ| := abs_nonneg _
    rw [abs_mul, abs_two]
    linarith [le_max_left t₀ 2]
  have hgrowth2 := h.bound (1 + δ) (2 * τ) h2τ (by linarith) hσ2
  have hzeroPow : (max (1 - (1 + δ)) 0) ^ a = 0 := by
    rw [max_eq_right (by linarith), Real.zero_rpow (by linarith : a ≠ 0)]
  rw [hzeroPow, mul_zero, zero_mul, zero_add] at hgrowth2
  have hgrowth2' : Real.log
      ‖riemannZeta (((1 + δ : ℝ) : ℂ) + I * (2 * τ))‖ ≤
        b * Real.log (Real.log |2 * τ|) + B₀ := by
    convert hgrowth2 using 1 <;> push_cast <;> ring
  have hlower' := neg_log_zeta_le_of_341 (1 + δ) τ
    (b * Real.log (Real.log |2 * τ|) + B₀) hσ hgrowth2'
  have hlower :
      -Real.log ‖riemannZeta (((1 + δ : ℝ) : ℂ) + I * τ)‖ ≤
        (3 * Real.log (1 + 1 / δ) +
          (b * Real.log (Real.log |2 * τ|) + B₀)) / 4 := by
    simpa only [show (1 + δ : ℝ) - 1 = δ by ring] using hlower'
  let raw : ℝ := B * R ^ a * Real.log (|τ| + R) +
      b * Real.log (Real.log (|τ| + R)) + B₀ +
      (3 * Real.log (1 + 1 / δ) +
        b * Real.log (Real.log |2 * τ|) + B₀) / 4
  let K : ℝ := max raw 0
  have hraw : Real.log ‖riemannZeta z‖ -
      Real.log ‖riemannZeta (((1 + δ : ℝ) : ℂ) + I * τ)‖ ≤ raw := by
    dsimp only [raw]
    linarith
  have hrawK : raw ≤ K := le_max_left _ _
  have hlogratio : Real.log ‖riemannZeta z‖ ≤
      K + Real.log ‖riemannZeta (((1 + δ : ℝ) : ℂ) + I * τ)‖ := by
    linarith
  have hcne : riemannZeta (((1 + δ : ℝ) : ℂ) + I * τ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  have hcn : 0 < ‖riemannZeta (((1 + δ : ℝ) : ℂ) + I * τ)‖ :=
    norm_pos_iff.mpr hcne
  by_cases hzeta : riemannZeta z = 0
  · rw [hzeta, norm_zero]
    positivity
  · have hzn : 0 < ‖riemannZeta z‖ := norm_pos_iff.mpr hzeta
    have hexp := Real.exp_le_exp.mpr hlogratio
    rw [Real.exp_add, Real.exp_log hzn, Real.exp_log hcn] at hexp
    simpa only [K, raw, zetaGrowthLandauBudget] using hexp

private theorem exists_zeta_growth_parameter_threshold
    (t₀ a B V : ℝ) (ha : 1 < a) (hB : 0 < B) (hV : 1 ≤ V) :
    ∃ t₁ : ℝ, t₀ ≤ t₁ ∧ 8 ≤ t₁ ∧ ∀ u : ℝ, t₁ ≤ u →
      let L := Real.log u
      let ell := Real.log L
      let R := (ell / (B * L)) ^ (1 / a)
      let δ := R / (V * ell)
      2 ≤ L ∧ 1 ≤ ell ∧ B ≤ ell ∧ Real.log (2 * V) ≤ ell ∧
        max t₀ 2 + R ≤ u ∧ 0 < R ∧ R ≤ 1 / 4 ∧
        0 < δ ∧ δ ≤ 1 / 4 ∧ Real.log (1 + 1 / δ) ≤ 3 * ell := by
  have ha0 : 0 < a := by linarith
  have hia0 : 0 < 1 / a := one_div_pos.mpr ha0
  have heps : 0 < B * (1 / 4 : ℝ) ^ a := by positivity
  have hlo := Real.isLittleO_log_id_atTop.def heps
  rw [Filter.eventually_atTop] at hlo
  obtain ⟨w₀, hw₀⟩ := hlo
  let C : ℝ := max 1 (max B (Real.log (2 * V)))
  let W : ℝ := max w₀ (Real.exp C)
  let t₁ : ℝ := max (max t₀ 8) (max (2 * (max t₀ 2 + 1)) (Real.exp W))
  refine ⟨t₁, le_trans (le_max_left _ _) (le_max_left _ _),
    le_trans (le_max_right t₀ 8) (le_max_left _ _), ?_⟩
  intro u hu
  dsimp only
  have htExp : Real.exp W ≤ u :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hu)
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos W) htExp
  have hLW : W ≤ Real.log u := (Real.le_log_iff_exp_le hu0).mpr htExp
  have hLw₀ : w₀ ≤ Real.log u := le_trans (le_max_left _ _) hLW
  have hLCexp : Real.exp C ≤ Real.log u := le_trans (le_max_right _ _) hLW
  have hL0 : 0 < Real.log u := lt_of_lt_of_le (Real.exp_pos C) hLCexp
  have hellC : C ≤ Real.log (Real.log u) :=
    (Real.le_log_iff_exp_le hL0).mpr hLCexp
  have hell1 : 1 ≤ Real.log (Real.log u) :=
    le_trans (le_max_left _ _) hellC
  have hellB : B ≤ Real.log (Real.log u) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right 1 _)) hellC
  have hellV : Real.log (2 * V) ≤ Real.log (Real.log u) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right 1 _)) hellC
  have hL2 : 2 ≤ Real.log u := by
    have hC1 : 1 ≤ C := le_max_left _ _
    have he2 : 2 ≤ Real.exp C := by
      have hexp1 : Real.exp 1 ≤ Real.exp C := Real.exp_le_exp.mpr hC1
      linarith [Real.add_one_le_exp (1 : ℝ)]
    linarith
  have hsmall := hw₀ (Real.log u) hLw₀
  simp only [id, Real.norm_eq_abs] at hsmall
  rw [abs_of_nonneg (Real.log_nonneg (by linarith)), abs_of_pos hL0] at hsmall
  let q : ℝ := Real.log (Real.log u) / (B * Real.log u)
  let R : ℝ := q ^ (1 / a)
  let δ : ℝ := R / (V * Real.log (Real.log u))
  have hden : 0 < B * Real.log u := mul_pos hB hL0
  have hq0 : 0 < q := by
    dsimp only [q]
    exact div_pos (by linarith) hden
  have hqsmall : q ≤ (1 / 4 : ℝ) ^ a := by
    dsimp only [q]
    rw [div_le_iff₀ hden]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hsmall
  have hquarterPow : 0 ≤ (1 / 4 : ℝ) ^ a := Real.rpow_nonneg (by norm_num) _
  have hR0 : 0 < R := by
    dsimp only [R]
    exact Real.rpow_pos_of_pos hq0 _
  have hRquarter : R ≤ 1 / 4 := by
    have hr := Real.rpow_le_rpow hq0.le hqsmall hia0.le
    have heq : ((1 / 4 : ℝ) ^ a) ^ (1 / a) = 1 / 4 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
      have : a * (1 / a) = 1 := by field_simp
      rw [this, Real.rpow_one]
    simpa only [R, heq] using hr
  have hV0 : 0 < V := lt_of_lt_of_le one_pos hV
  have hδ0 : 0 < δ := by
    dsimp only [δ]
    positivity
  have hVell : 1 ≤ V * Real.log (Real.log u) :=
    one_le_mul_of_one_le_of_one_le hV hell1
  have hδR : δ ≤ R := by
    dsimp only [δ]
    exact div_le_self hR0.le hVell
  have hδquarter : δ ≤ 1 / 4 := le_trans hδR hRquarter
  have hqone : q ≤ 1 := by
    calc
      q ≤ (1 / 4 : ℝ) ^ a := hqsmall
      _ ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) ha0.le
  have hiaOne : 1 / a ≤ 1 := by
    rw [div_le_one ha0]
    linarith
  have hqR : q ≤ R := by
    have := Real.rpow_le_rpow_of_exponent_ge hq0 hqone hiaOne
    simpa only [Real.rpow_one, R] using this
  have hqLower : 1 / Real.log u ≤ q := by
    dsimp only [q]
    rw [div_le_div_iff₀ hL0 hden]
    nlinarith
  have hRLower : 1 / Real.log u ≤ R := le_trans hqLower hqR
  have hinvR : 1 / R ≤ Real.log u := by
    rw [div_le_iff₀ hR0]
    have := mul_le_mul_of_nonneg_right hRLower hR0.le
    field_simp at this
    linarith
  have hmainT : 2 * (max t₀ 2 + 1) ≤ u :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hu)
  have hheight : max t₀ 2 + R ≤ u := by
    nlinarith
  have hinvδ : 1 / δ = V * Real.log (Real.log u) / R := by
    dsimp only [δ]
    field_simp
  have hqprod : 1 ≤ V * Real.log (Real.log u) * Real.log u := by
    have hLone : 1 ≤ Real.log u := by linarith
    nlinarith [hVell]
  have hinvδUpper : 1 / δ ≤
      V * Real.log (Real.log u) * Real.log u := by
    rw [hinvδ]
    have hnonneg : 0 ≤ V * Real.log (Real.log u) := by positivity
    calc
      V * Real.log (Real.log u) / R =
          (V * Real.log (Real.log u)) * (1 / R) := by ring
      _ ≤ (V * Real.log (Real.log u)) * Real.log u :=
        mul_le_mul_of_nonneg_left hinvR hnonneg
      _ = _ := by ring
  have hAupper : 1 + 1 / δ ≤
      2 * V * Real.log (Real.log u) * Real.log u := by
    calc
      1 + 1 / δ ≤ 1 + V * Real.log (Real.log u) * Real.log u :=
        by linarith
      _ ≤ 2 * (V * Real.log (Real.log u) * Real.log u) := by linarith
      _ = 2 * V * Real.log (Real.log u) * Real.log u := by ring
  have hApos : 0 < 1 + 1 / δ := by positivity
  have hprodPos : 0 < 2 * V * Real.log (Real.log u) * Real.log u := by positivity
  have hlogA := Real.log_le_log hApos hAupper
  have hlogProd : Real.log (2 * V * Real.log (Real.log u) * Real.log u) =
      Real.log (2 * V) + Real.log (Real.log (Real.log u)) +
        Real.log (Real.log u) := by
    rw [Real.log_mul
        (by positivity : (2 * V * Real.log (Real.log u) : ℝ) ≠ 0) hL0.ne',
      Real.log_mul (by positivity : (2 * V : ℝ) ≠ 0)
        (by positivity : Real.log (Real.log u) ≠ 0)]
  rw [hlogProd] at hlogA
  have hlogEll : Real.log (Real.log (Real.log u)) ≤ Real.log (Real.log u) := by
    have hle := Real.log_le_sub_one_of_pos (by linarith : 0 < Real.log (Real.log u))
    linarith
  have hlogAFinal : Real.log (1 + 1 / δ) ≤
      3 * Real.log (Real.log u) := by linarith
  simpa only [q, R, δ] using
    ⟨hL2, hell1, hellB, hellV, hheight, hR0, hRquarter,
      hδ0, hδquarter, hlogAFinal⟩

private theorem zetaGrowthLandauBudget_le
    {a B b B₀ R δ τ L ell : ℝ}
    (hB : 0 ≤ B) (hb : 0 ≤ b) (hB₀ : 0 ≤ B₀)
    (hR : 0 ≤ R) (hell : 1 ≤ ell)
    (hlog : Real.log (|τ| + R) ≤ 2 * L)
    (hloglog : Real.log (Real.log (|τ| + R)) ≤ 2 * ell)
    (hloglog2 : Real.log (Real.log |2 * τ|) ≤ 2 * ell)
    (hscale : B * R ^ a * L = ell)
    (hδ : Real.log (1 + 1 / δ) ≤ 3 * ell) :
    zetaGrowthLandauBudget a B b B₀ R δ τ ≤
      (6 + 3 * b + 2 * B₀) * ell := by
  have hfirst : B * R ^ a * Real.log (|τ| + R) ≤ 2 * ell := by
    have hcoef : 0 ≤ B * R ^ a := mul_nonneg hB (Real.rpow_nonneg hR _)
    calc
      B * R ^ a * Real.log (|τ| + R) ≤ B * R ^ a * (2 * L) :=
        mul_le_mul_of_nonneg_left hlog hcoef
      _ = 2 * ell := by rw [← hscale]; ring
  have hraw : B * R ^ a * Real.log (|τ| + R) +
        b * Real.log (Real.log (|τ| + R)) + B₀ +
        (3 * Real.log (1 + 1 / δ) +
          b * Real.log (Real.log |2 * τ|) + B₀) / 4 ≤
      (6 + 3 * b + 2 * B₀) * ell := by
    have hb1 := mul_le_mul_of_nonneg_left hloglog hb
    have hb2 := mul_le_mul_of_nonneg_left hloglog2 hb
    have hB₀ell : B₀ ≤ B₀ * ell := by nlinarith
    have hraw' : B * R ^ a * Real.log (|τ| + R) +
          b * Real.log (Real.log (|τ| + R)) + B₀ +
          (3 * Real.log (1 + 1 / δ) +
            b * Real.log (Real.log |2 * τ|) + B₀) / 4 ≤
        2 * ell + 2 * b * ell + B₀ +
          (9 * ell + 2 * b * ell + B₀) / 4 := by
      linarith
    nlinarith
  have hQ0 : 0 ≤ (6 + 3 * b + 2 * B₀) * ell := by positivity
  exact max_le hraw hQ0

private theorem growth_master_coefficient_le {P Q : ℝ}
    (hP : 0 ≤ P) (hQ : 6 ≤ Q) :
    3 * P + 80 * (Q + 1) ≤ 1000 * (Q + P + 1) / 10 := by
  nlinarith

set_option maxHeartbeats 2000000 in
open ArithmeticFunction in
/-- **V-C4-2.**  A growth estimate with exponent `a > 1` gives the
corresponding Landau--Vinogradov zero-free region.  The harmless sign
normalizations on `b` and `B₀` let one enlarge the supplied growth bound
once and then use a single monotone budget. -/
theorem zeta_zero_free_of_growth
    {t₀ a B b B₀ : ℝ} (h : ZetaGrowthBound t₀ a B b B₀)
    (ha : 1 < a) (hB : 0 < B) (hb : 0 ≤ b) (hB₀ : 0 ≤ B₀) :
    ∃ c t₁ : ℝ, 0 < c ∧ t₀ ≤ t₁ ∧ ∀ β t : ℝ, t₁ ≤ |t| →
      riemannZeta ((β : ℂ) + I * t) = 0 →
      β ≤ 1 - c * (Real.log (Real.log |t|)) ^ (1 / a - 1) /
        (Real.log |t|) ^ (1 / a) := by
  obtain ⟨cp, hcp⟩ := zeta_logDeriv_pole_bound
  let P : ℝ := max cp 0
  let Q : ℝ := 6 + 3 * b + 2 * B₀
  let V : ℝ := 1000 * (Q + P + 1)
  have hP0 : 0 ≤ P := le_max_right _ _
  have hcpP : cp ≤ P := le_max_left _ _
  have hQ6 : 6 ≤ Q := by dsimp only [Q]; nlinarith
  have hV1000 : 1000 ≤ V := by dsimp only [V]; nlinarith
  have hV1 : 1 ≤ V := by linarith
  have hV0 : 0 < V := by linarith
  obtain ⟨t₁, ht₀t₁, ht₁8, ht₁⟩ :=
    exists_zeta_growth_parameter_threshold t₀ a B V ha hB hV1
  let c : ℝ := B ^ (-1 / a) / (9 * V)
  have hc0 : 0 < c := by
    dsimp only [c]
    exact div_pos (Real.rpow_pos_of_pos hB _) (by positivity)
  refine ⟨c, t₁, hc0, ht₀t₁, ?_⟩
  intro β t ht hzero
  let u : ℝ := |t|
  have hu8 : 8 ≤ u := le_trans ht₁8 ht
  have hu0 : 0 < u := by linarith
  have habsu : |u| = u := abs_of_pos hu0
  let L : ℝ := Real.log u
  let ell : ℝ := Real.log L
  let R : ℝ := (ell / (B * L)) ^ (1 / a)
  let δ : ℝ := R / (V * ell)
  have hparams := ht₁ u ht
  dsimp only at hparams
  change 2 ≤ L ∧ 1 ≤ ell ∧ B ≤ ell ∧ Real.log (2 * V) ≤ ell ∧
      max t₀ 2 + R ≤ u ∧ 0 < R ∧ R ≤ 1 / 4 ∧
      0 < δ ∧ δ ≤ 1 / 4 ∧ Real.log (1 + 1 / δ) ≤ 3 * ell at hparams
  obtain ⟨hL2, hell1, hellB, hellV, hheight, hR0, hRquarter,
    hδ0, hδquarter, hlogδ⟩ := hparams
  have hL0 : 0 < L := by linarith
  have hell0 : 0 < ell := by linarith
  have hRhalf : R ≤ 1 / 2 := by linarith
  have hδhalf : δ ≤ 1 / 2 := by linarith
  have huR : R ≤ u := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog3 : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith
  have hlog_uR : Real.log (u + R) ≤ 2 * L := by
    have hsum : u + R ≤ 2 * u := by linarith
    have hlog := Real.log_le_log (by positivity) hsum
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hu0.ne'] at hlog
    dsimp only [L]
    linarith
  have hlog_2uR : Real.log (2 * u + R) ≤ 2 * L := by
    have hsum : 2 * u + R ≤ 3 * u := by linarith
    have hlog := Real.log_le_log (by positivity) hsum
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hu0.ne'] at hlog
    dsimp only [L]
    linarith
  have hloglog_of_le {x : ℝ} (hx : 1 < x)
      (hxl : Real.log x ≤ 2 * L) :
      Real.log (Real.log x) ≤ 2 * ell := by
    have hlogx0 : 0 < Real.log x := Real.log_pos hx
    have h2L0 : 0 < 2 * L := by positivity
    have hh := Real.log_le_log hlogx0 hxl
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hL0.ne'] at hh
    dsimp only [ell]
    linarith
  have hll_uR : Real.log (Real.log (u + R)) ≤ 2 * ell :=
    hloglog_of_le (by linarith) hlog_uR
  have hll_2uR : Real.log (Real.log (2 * u + R)) ≤ 2 * ell :=
    hloglog_of_le (by linarith) hlog_2uR
  have hlog_2u : Real.log (2 * u) ≤ 2 * L := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hu0.ne']
    dsimp only [L]
    linarith
  have hlog_4u : Real.log (4 * u) ≤ 2 * L := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hu0.ne']
    dsimp only [L]
    linarith
  have hll_2u : Real.log (Real.log (2 * u)) ≤ 2 * ell :=
    hloglog_of_le (by nlinarith) hlog_2u
  have hll_4u : Real.log (Real.log (4 * u)) ≤ 2 * ell :=
    hloglog_of_le (by nlinarith) hlog_4u
  have hscale : B * R ^ a * L = ell := by
    let q : ℝ := ell / (B * L)
    have hq0 : 0 < q := by dsimp only [q]; positivity
    have hpow : R ^ a = q := by
      dsimp only [R]
      rw [← Real.rpow_mul hq0.le]
      have : (1 / a) * a = 1 := by field_simp
      rw [this, Real.rpow_one]
    rw [hpow]
    dsimp only [q]
    field_simp
  have habs2t : |2 * t| = 2 * u := by
    dsimp only [u]
    rw [abs_mul, abs_two]
  have habs4t : |4 * t| = 4 * u := by
    dsimp only [u]
    rw [abs_mul, show |(4 : ℝ)| = 4 by norm_num]
  have habsTwoTwoT : |2 * (2 * t)| = 4 * u := by
    rw [show 2 * (2 * t) = 4 * t by ring, habs4t]
  have hbudget1 : zetaGrowthLandauBudget a B b B₀ R δ t ≤ Q * ell := by
    have hnormTop : |t| + R = u + R := by rfl
    have hnormTwice : |2 * t| = 2 * u := habs2t
    dsimp only [Q]
    apply zetaGrowthLandauBudget_le hB.le hb hB₀ hR0.le hell1
    · simpa only [hnormTop] using hlog_uR
    · simpa only [hnormTop] using hll_uR
    · simpa only [hnormTwice] using hll_2u
    · exact hscale
    · exact hlogδ
  have hbudget2 : zetaGrowthLandauBudget a B b B₀ R δ (2 * t) ≤ Q * ell := by
    have hnormTop : |2 * t| + R = 2 * u + R := by rw [habs2t]
    dsimp only [Q]
    apply zetaGrowthLandauBudget_le hB.le hb hB₀ hR0.le hell1
    · simpa only [hnormTop] using hlog_2uR
    · simpa only [hnormTop] using hll_2uR
    · simpa only [habsTwoTwoT] using hll_4u
    · exact hscale
    · exact hlogδ
  have hβ1 : β < 1 := by
    by_contra hnot
    push_neg at hnot
    exact (riemannZeta_ne_zero_of_one_le_re (by simpa using hnot)) hzero
  let x : ℝ := 1 - β
  have hx0 : 0 < x := by dsimp only [x]; linarith
  have hRadiusWidth : R / ell = B ^ (-1 / a) * zetaGrowthWidth a t := by
    have hr := zetaGrowthRadius_div_loglog (t := t) (a := a) (B := B)
      (by linarith) hB (by simpa only [u, L] using hL0)
      (by simpa only [u, L, ell] using hell0)
    simpa only [zetaGrowthRadius, zetaGrowthWidth, u, L, ell, R] using hr
  have hWidth : c * zetaGrowthWidth a t = δ / 9 := by
    dsimp only [c]
    rw [show B ^ (-1 / a) / (9 * V) * zetaGrowthWidth a t =
      (B ^ (-1 / a) * zetaGrowthWidth a t) / (9 * V) by ring,
      ← hRadiusWidth]
    dsimp only [δ]
    field_simp
  rw [show c * (Real.log (Real.log |t|)) ^ (1 / a - 1) /
      (Real.log |t|) ^ (1 / a) = c * zetaGrowthWidth a t by
    rw [zetaGrowthWidth]
    ring]
  by_contra hcon
  push_neg at hcon
  have hxsmall : x < δ / 9 := by
    dsimp only [x]
    rw [hWidth] at hcon
    linarith
  have hVell : 1000 ≤ V * ell := by
    nlinarith [mul_le_mul_of_nonneg_left hell1 (by linarith : 0 ≤ V)]
  have hδmul : δ * (V * ell) = R := by
    dsimp only [δ]
    field_simp
  have hδR : 1000 * δ ≤ R := by
    have := mul_le_mul_of_nonneg_left hVell hδ0.le
    rw [hδmul] at this
    nlinarith
  have hδx0 : 0 < δ + x := by linarith
  have hballSmall : δ + x ≤ R / 4 := by nlinarith
  have hσone : 1 < 1 + δ := by linarith
  have hσthreehalf : 1 + δ ≤ 3 / 2 := by linarith
  have hσtwo : 1 + δ ≤ 2 := by linarith
  let K₁ : ℝ := zetaGrowthLandauBudget a B b B₀ R δ t
  let K₂ : ℝ := zetaGrowthLandauBudget a B b B₀ R δ (2 * t)
  have hK₁0 : 0 ≤ K₁ := by
    dsimp only [K₁, zetaGrowthLandauBudget]
    exact le_max_right _ _
  have hK₂0 : 0 ≤ K₂ := by
    dsimp only [K₂, zetaGrowthLandauBudget]
    exact le_max_right _ _
  have hK₁ : K₁ ≤ Q * ell := hbudget1
  have hK₂ : K₂ ≤ Q * ell := hbudget2
  have hratio1 := zeta_growth_ratio_on_landau_disc h ha hB hb hB₀
    hR0 hRquarter hδ0 hδquarter (by simpa only [u] using hheight)
  have hheight2 : max t₀ 2 + R ≤ |2 * t| := by rw [habs2t]; linarith
  have hratio2 := zeta_growth_ratio_on_landau_disc h ha hB hb hB₀
    hR0 hRquarter hδ0 hδquarter hheight2
  have hτone : 1 ≤ |t| := by dsimp only [u] at hu8; linarith
  have h2τone : 1 ≤ |2 * t| := by rw [habs2t]; linarith
  have hpointDiff :
      (β : ℂ) + I * t - (((1 + δ : ℝ) : ℂ) + I * t) =
        (((β - (1 + δ) : ℝ)) : ℂ) := by
    push_cast
    ring
  have hρball : ((β : ℂ) + I * t) ∈
      Metric.closedBall ((((1 + δ : ℝ) : ℂ) + I * t)) (R / 4) := by
    rw [Metric.mem_closedBall, dist_eq_norm, hpointDiff, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by dsimp only [x] at hx0; linarith : β - (1 + δ) < 0)]
    have : 1 + δ - β = δ + x := by dsimp only [x]; ring
    rw [show -(β - (1 + δ)) = 1 + δ - β by ring, this]
    exact hballSmall
  have hlan1 := (zeta_landau_core_at_radius (1 + δ) t R K₁ hσone
    hσthreehalf hR0 hRhalf hτone hK₁0 (by simpa only [K₁] using hratio1)).1
    ((β : ℂ) + I * t) hρball hzero
  have hlan2 := (zeta_landau_core_at_radius (1 + δ) (2 * t) R K₂ hσone
    hσthreehalf hR0 hRhalf h2τone hK₂0 (by simpa only [K₂] using hratio2)).2
  have hcenterDiff :
      (((1 + δ : ℝ) : ℂ) + I * t) - ((β : ℂ) + I * t) =
        (((δ + x : ℝ)) : ℂ) := by
    dsimp only [x]
    push_cast
    ring
  have hinvCast :
      (1 : ℂ) / (((δ + x : ℝ)) : ℂ) = (((1 / (δ + x) : ℝ)) : ℂ) := by
    push_cast
    ring
  have hReterm :
      (1 / ((((1 + δ : ℝ) : ℂ) + I * t) - ((β : ℂ) + I * t))).re =
        1 / (δ + x) := by
    rw [hcenterDiff, hinvCast]
    exact Complex.ofReal_re _
  rw [hReterm] at hlan1
  have hpole := hcp (1 + δ) hσone hσtwo
  have hδsub : (1 + δ) - 1 = δ := by ring
  rw [hδsub] at hpole
  have hbridge : ∀ s : ℂ, 1 < s.re →
      (LSeries (fun n => (vonMangoldt n : ℂ)) s).re =
        -(deriv riemannZeta s / riemannZeta s).re := by
    intro s hs
    rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_div,
      Complex.neg_re]
  have h341 := vonMangoldt_341_nonneg (1 + δ) t hσone
  have hzeroPoint : ((1 + δ : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I =
      ((1 + δ : ℝ) : ℂ) := by push_cast; ring
  have honePoint : ((1 + δ : ℝ) : ℂ) + (t : ℂ) * I =
      ((1 + δ : ℝ) : ℂ) + I * t := by ring
  have htwoPoint : ((1 + δ : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I =
      ((1 + δ : ℝ) : ℂ) + I * (2 * t) := by push_cast; ring
  rw [hzeroPoint, honePoint, htwoPoint] at h341
  rw [hbridge ((1 + δ : ℝ) : ℂ) (by simp; linarith),
    hbridge (((1 + δ : ℝ) : ℂ) + I * t) (by simp; linarith),
    hbridge (((1 + δ : ℝ) : ℂ) + I * (2 * t)) (by simp; linarith)] at h341
  have hK₁plus : K₁ + 1 ≤ (Q + 1) * ell := by nlinarith
  have hK₂plus : K₂ + 1 ≤ (Q + 1) * ell := by nlinarith
  have hlan1' :
      -(deriv riemannZeta (((1 + δ : ℝ) : ℂ) + I * t) /
          riemannZeta (((1 + δ : ℝ) : ℂ) + I * t)).re ≤
        16 * ((Q + 1) * ell) / R - 1 / (δ + x) := by
    have hmul := mul_le_mul_of_nonneg_left hK₁plus (by norm_num : (0 : ℝ) ≤ 16)
    have hdiv := div_le_div_of_nonneg_right hmul hR0.le
    dsimp only [zetaLandauConstant] at hlan1
    exact le_trans hlan1 (sub_le_sub_right hdiv _)
  have hlan2' :
      -(deriv riemannZeta (((1 + δ : ℝ) : ℂ) + I * (2 * t)) /
          riemannZeta (((1 + δ : ℝ) : ℂ) + I * (2 * t))).re ≤
        16 * ((Q + 1) * ell) / R := by
    have hmul := mul_le_mul_of_nonneg_left hK₂plus (by norm_num : (0 : ℝ) ≤ 16)
    have hdiv := div_le_div_of_nonneg_right hmul hR0.le
    dsimp only [zetaLandauConstant] at hlan2
    have hlan2c :
        -(deriv riemannZeta (((1 + δ : ℝ) : ℂ) + I * (2 * t)) /
            riemannZeta (((1 + δ : ℝ) : ℂ) + I * (2 * t))).re ≤
          16 * (K₂ + 1) / R := by
      convert hlan2 using 1 <;> push_cast <;> ring
    exact le_trans hlan2c hdiv
  have hpole' :
      -(deriv riemannZeta ((1 + δ : ℝ) : ℂ) /
          riemannZeta ((1 + δ : ℝ) : ℂ)).re ≤ 1 / δ + P := by
    calc
      _ ≤ 1 / δ + cp := hpole
      _ = cp + 1 / δ := by ring
      _ ≤ P + 1 / δ := add_le_add_left hcpP _
      _ = 1 / δ + P := by ring
  have h341' :
      -(3 * -(deriv riemannZeta ((1 + δ : ℝ) : ℂ) /
            riemannZeta ((1 + δ : ℝ) : ℂ)).re +
          4 * -(deriv riemannZeta (((1 + δ : ℝ) : ℂ) + I * t) /
            riemannZeta (((1 + δ : ℝ) : ℂ) + I * t)).re +
          -(deriv riemannZeta (((1 + δ : ℝ) : ℂ) + I * (2 * t)) /
            riemannZeta (((1 + δ : ℝ) : ℂ) + I * (2 * t))).re) ≤ 0 := by
    exact neg_nonpos.mpr h341
  have hmaster : 4 / (δ + x) ≤ 3 / δ + 3 * P +
      80 * (Q + 1) * ell / R := by
    linear_combination 3 * hpole' + 4 * hlan1' + hlan2' + h341'
  have hellR : 1 ≤ ell / R := by
    have hRell : R ≤ ell := le_trans hRquarter (by linarith only [hell1])
    calc
      1 = R / R := by field_simp
      _ ≤ ell / R := div_le_div_of_nonneg_right hRell hR0.le
  have hmaster' : 4 / (δ + x) ≤ 3 / δ +
      (3 * P + 80 * (Q + 1)) * (ell / R) := by
    have hPscale : 3 * P ≤ 3 * P * (ell / R) := by
      exact le_mul_of_one_le_right (by positivity) hellR
    calc
      4 / (δ + x) ≤ 3 / δ + 3 * P + 80 * (Q + 1) * ell / R := hmaster
      _ = 3 / δ + 3 * P + 80 * (Q + 1) * (ell / R) := by ring
      _ ≤ 3 / δ + 3 * P * (ell / R) + 80 * (Q + 1) * (ell / R) :=
        by linarith only [hPscale]
      _ = 3 / δ + (3 * P + 80 * (Q + 1)) * (ell / R) := by ring
  have hcoef : 3 * P + 80 * (Q + 1) ≤ V / 10 := by
    dsimp only [V]
    exact growth_master_coefficient_le hP0 hQ6
  have hinvδ : 1 / δ = V * (ell / R) := by
    dsimp only [δ]
    field_simp
  have herr : (3 * P + 80 * (Q + 1)) * (ell / R) ≤ (1 / 10) / δ := by
    have hratio0 : 0 ≤ ell / R := by positivity
    have hm := mul_le_mul_of_nonneg_right hcoef hratio0
    calc
      (3 * P + 80 * (Q + 1)) * (ell / R) ≤ V / 10 * (ell / R) := hm
      _ = (1 / 10) * (V * (ell / R)) := by ring
      _ = (1 / 10) * (1 / δ) := by rw [hinvδ]
      _ = (1 / 10) / δ := by ring
  have hupperFinal : 4 / (δ + x) ≤ (31 / 10) / δ := by
    have hadd : 3 / δ + (3 * P + 80 * (Q + 1)) * (ell / R) ≤
        3 / δ + (1 / 10) / δ := by
      simpa only [add_comm] using add_le_add_left herr (3 / δ)
    calc
      4 / (δ + x) ≤ 3 / δ +
          (3 * P + 80 * (Q + 1)) * (ell / R) := hmaster'
      _ ≤ 3 / δ + (1 / 10) / δ := hadd
      _ = (31 / 10) / δ := by ring
  have hlowerFinal : (18 / 5) / δ < 4 / (δ + x) := by
    rw [div_lt_div_iff₀ hδ0 hδx0]
    nlinarith only [hxsmall, hδ0]
  have hconstants : (31 / 10) / δ < (18 / 5) / δ := by
    exact div_lt_div_of_pos_right (by norm_num) hδ0
  linarith only [hlowerFinal, hupperFinal, hconstants]

end ExpSums

end MoltResearch
