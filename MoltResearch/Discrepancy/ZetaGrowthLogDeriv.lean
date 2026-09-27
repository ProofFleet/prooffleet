import MoltResearch.Discrepancy.ZetaGrowthRegion
import MoltResearch.Discrepancy.PrimeSumZeroFree

/-!
# Logarithmic derivative bounds inside a growth zero-free region

The complex-analytic nucleus is an interior version of the tree's
Borel--Carathéodory estimate.  A ratio bound on one disc controls the
logarithmic derivative at every point in its closed half-disc.  This is the
form needed to cover the near-one part of a contour rectangle.
-/

namespace MoltResearch

namespace ExpSums

open Complex

/-- A capped half-height width used for the logarithmic-derivative disc. -/
noncomputable def zetaGrowthRegionEta (a c t : ℝ) : ℝ :=
  min (1 / 8) ((c / 2) * zetaGrowthWidth a (2 * |t|))

/-- Explicit polynomial-log exponent furnished by the coarse interior-disc
argument. -/
noncomputable def zetaGrowthLogDerivExponent (a : ℝ) : ℝ :=
  2 + 1 / a

private noncomputable def zetaGrowthWidthFromLogs (a L ell : ℝ) : ℝ :=
  ell ^ (1 / a - 1) / L ^ (1 / a)

private theorem zetaGrowthWidthFromLogs_anti
    {a L₁ L₂ ell₁ ell₂ : ℝ} (ha : 1 < a)
    (hL₁ : 0 < L₁) (hL : L₁ ≤ L₂)
    (hell₁ : 0 < ell₁) (hell : ell₁ ≤ ell₂) :
    zetaGrowthWidthFromLogs a L₂ ell₂ ≤
      zetaGrowthWidthFromLogs a L₁ ell₁ := by
  have hp : 0 < 1 / a := one_div_pos.mpr (by linarith)
  have hn : 1 / a - 1 ≤ 0 := by
    have hp1 : 1 / a ≤ 1 := by
      rw [div_le_one (by linarith : 0 < a)]
      linarith
    linarith
  have hL₂ : 0 < L₂ := lt_of_lt_of_le hL₁ hL
  have hell₂ : 0 < ell₂ := lt_of_lt_of_le hell₁ hell
  have hnum : ell₂ ^ (1 / a - 1) ≤ ell₁ ^ (1 / a - 1) :=
    Real.rpow_le_rpow_of_nonpos hell₁ hell hn
  have hden : L₁ ^ (1 / a) ≤ L₂ ^ (1 / a) :=
    (Real.rpow_le_rpow_iff hL₁.le hL₂.le hp).mpr hL
  dsimp only [zetaGrowthWidthFromLogs]
  exact div_le_div₀ (Real.rpow_nonneg hell₁.le _) hnum
    (Real.rpow_pos_of_pos hL₁ _)
    hden

private theorem one_div_log_le_zetaGrowthWidthFromLogs
    {a L ell : ℝ} (ha : 1 < a) (hL : 0 < L)
    (hell1 : 1 ≤ ell) (hellL : ell ≤ L) :
    1 / L ≤ zetaGrowthWidthFromLogs a L ell := by
  have hn : 1 / a - 1 ≤ 0 := by
    have hp1 : 1 / a ≤ 1 := by
      rw [div_le_one (by linarith : 0 < a)]
      linarith
    linarith
  have hell0 : 0 < ell := lt_of_lt_of_le one_pos hell1
  have hnum : L ^ (1 / a - 1) ≤ ell ^ (1 / a - 1) :=
    Real.rpow_le_rpow_of_nonpos hell0 hellL hn
  have hLpow : 0 < L ^ (1 / a) := Real.rpow_pos_of_pos hL _
  have hid : L ^ (1 / a - 1) / L ^ (1 / a) = 1 / L := by
    rw [Real.rpow_sub hL, Real.rpow_one]
    field_simp
  rw [← hid]
  exact div_le_div_of_nonneg_right hnum hLpow.le

/-- Borel--Carathéodory at every point of the closed half-disc. -/
theorem norm_logDeriv_le_on_half_closedBall
    {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : AnalyticOnNhd ℂ g U) {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hball : Metric.ball c R ⊆ U)
    (hne : ∀ z ∈ Metric.ball c R, g z ≠ 0)
    (hratio : ∀ z ∈ Metric.ball c R,
      ‖g z‖ ≤ Real.exp M * ‖g c‖)
    {z : ℂ} (hz : z ∈ Metric.closedBall c (R / 2)) :
    ‖deriv g z / g z‖ ≤ 24 * (M + 1) / R := by
  have hcball : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  have hgc : g c ≠ 0 := hne c hcball
  have hgc0 : 0 < ‖g c‖ := norm_pos_iff.mpr hgc
  have hM0 : 0 ≤ M := by
    have hcenter := hratio c hcball
    by_contra hneg
    push_neg at hneg
    have hexp : Real.exp M < 1 := Real.exp_lt_one_iff.mpr hneg
    nlinarith [mul_lt_mul_of_pos_right hexp hgc0]
  obtain ⟨φ, hφc, hφexp, hφd⟩ := exists_log_branch hU hg hR hball hne
  have hφre : ∀ w ∈ Metric.ball c R, (φ w).re ≤ M := by
    intro w hw
    have hnorm : ‖Complex.exp (φ w)‖ = ‖g w‖ / ‖g c‖ := by
      rw [hφexp w hw, norm_div]
    have hexp : Real.exp ((φ w).re) ≤ Real.exp M := by
      rw [← Complex.norm_exp, hnorm, div_le_iff₀ hgc0]
      exact hratio w hw
    exact Real.exp_le_exp.mp hexp
  let ψ : ℂ → ℂ := fun w => φ (c + w)
  have htrans : ∀ w ∈ Metric.ball (0 : ℂ) R,
      c + w ∈ Metric.ball c R := by
    intro w hw
    rw [Metric.mem_ball] at hw ⊢
    simpa [dist_eq_norm] using hw
  have hψdiff : DifferentiableOn ℂ ψ (Metric.ball (0 : ℂ) R) := by
    intro w hw
    have hd := hφd (c + w) (htrans w hw)
    have hadd : HasDerivAt (fun v : ℂ => c + v) 1 w :=
      (hasDerivAt_id w).const_add c
    exact ((hd.comp w hadd).differentiableAt).differentiableWithinAt
  have hψzero : ψ 0 = 0 := by simp [ψ, hφc]
  have hφbound : ∀ w ∈ Metric.closedBall c (3 * R / 4),
      ‖φ w‖ ≤ 6 * (M + 1) := by
    intro w hw
    let q : ℂ := w - c
    have hqnorm : ‖q‖ ≤ 3 * R / 4 := by
      dsimp only [q]
      rw [← dist_eq_norm]
      exact Metric.mem_closedBall.mp hw
    have hqball : q ∈ Metric.ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    have hmaps : Set.MapsTo ψ (Metric.ball (0 : ℂ) R)
        {v : ℂ | v.re < M + 1} := by
      intro v hv
      have := hφre (c + v) (htrans v hv)
      simp only [Set.mem_setOf_eq, ψ]
      linarith
    -- Mathlib's Borel–Carathéodory now asks for `re ≤ M` rather than `re < M`.
    have hmaps' : Set.MapsTo ψ (Metric.ball (0 : ℂ) R) {v : ℂ | v.re ≤ M + 1} :=
      fun v hv => show (ψ v).re ≤ M + 1 from le_of_lt (show (ψ v).re < M + 1 from hmaps hv)
    have hbc := Complex.borelCaratheodory (M := M + 1) (by linarith)
      hψdiff hmaps' hR hqball
    rw [hψzero, norm_zero, zero_mul, zero_div, add_zero] at hbc
    have hden : R / 4 ≤ R - ‖q‖ := by linarith
    have hden0 : 0 < R - ‖q‖ := by linarith
    have hfrac : 2 * (M + 1) * ‖q‖ / (R - ‖q‖) ≤
        2 * (M + 1) * (3 * R / 4) / (R / 4) := by
      have hnum := mul_le_mul_of_nonneg_left hqnorm (by positivity : 0 ≤ 2 * (M + 1))
      have hnumMax : 0 ≤ 2 * (M + 1) * (3 * R / 4) := by positivity
      exact div_le_div₀ hnumMax hnum (by positivity) hden
    have hvalue : ψ q = φ w := by dsimp only [ψ, q]; congr 1; ring
    rw [hvalue] at hbc
    calc
      ‖φ w‖ ≤ 2 * (M + 1) * ‖q‖ / (R - ‖q‖) := hbc
      _ ≤ 2 * (M + 1) * (3 * R / 4) / (R / 4) := hfrac
      _ = 6 * (M + 1) := by field_simp; ring
  have hR4 : 0 < R / 4 := by linarith
  have hsphere : ∀ w ∈ Metric.sphere z (R / 4),
      ‖φ w‖ ≤ 6 * (M + 1) := by
    intro w hw
    apply hφbound w
    rw [Metric.mem_closedBall]
    have hwz : dist w z = R / 4 := Metric.mem_sphere.mp hw
    have hzc : dist z c ≤ R / 2 := Metric.mem_closedBall.mp hz
    linarith [dist_triangle w z c]
  have hdiff : DiffContOnCl ℂ φ (Metric.ball z (R / 4)) := by
    have hd : DifferentiableOn ℂ φ (Metric.closedBall z (R / 4)) := by
      intro w hw
      have hwz : dist w z ≤ R / 4 := Metric.mem_closedBall.mp hw
      have hzc : dist z c ≤ R / 2 := Metric.mem_closedBall.mp hz
      have hwball : w ∈ Metric.ball c R := by
        rw [Metric.mem_ball]
        linarith [dist_triangle w z c]
      exact (hφd w hwball).differentiableAt.differentiableWithinAt
    rw [← closure_ball z hR4.ne'] at hd
    exact hd.diffContOnCl
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    hR4 hdiff hsphere
  have hzball : z ∈ Metric.ball c R := by
    rw [Metric.mem_ball]
    have := Metric.mem_closedBall.mp hz
    linarith
  have hderiv := hφd z hzball
  rw [hderiv.deriv] at hcauchy
  calc
    ‖deriv g z / g z‖ ≤ 6 * (M + 1) / (R / 4) := hcauchy
    _ = 24 * (M + 1) / R := by field_simp; ring

/-- Absolute convergence gives the norm form of the pole bound throughout
the half-plane to the right of one. -/
theorem exists_norm_zeta_logDeriv_pole_bound :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ (σ t : ℝ), 1 < σ → σ ≤ 2 →
      ‖-deriv riemannZeta ((σ : ℂ) + I * t) /
          riemannZeta ((σ : ℂ) + I * t)‖ ≤ 1 / (σ - 1) + P := by
  open ArithmeticFunction in
    obtain ⟨cp, hcp⟩ := zeta_logDeriv_pole_bound
  let P : ℝ := max cp 0
  refine ⟨P, le_max_right _ _, ?_⟩
  intro σ t hσ hσ2
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let s : ℂ := (σ : ℂ) + I * t
  have hsre : s.re = σ := by simp [s]
  have hsummable : Summable (fun n => ‖LSeries.term f s n‖) :=
    summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt (by
      rw [hsre]
      exact hσ))
  have htermnorm : (∑' n : ℕ, ‖LSeries.term f s n‖) =
      ∑' n : ℕ, ‖LSeries.term f (σ : ℂ) n‖ := by
    apply tsum_congr
    intro n
    simp only [LSeries.norm_term_eq, s, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
  have hreal : (∑' n : ℕ, ‖LSeries.term f (σ : ℂ) n‖) =
      (LSeries f (σ : ℂ)).re := by
    have hr : (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (σ : ℂ)).re = ∑' n : ℕ,
          ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) := by
      simpa using re_LSeries_vonMangoldt σ 0 hσ
    rw [hr]
    apply tsum_congr
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [f]
    · rw [LSeries.norm_term_eq]
      simp [f, Nat.ne_of_gt hn,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have hnormL : ‖LSeries f s‖ ≤ (LSeries f (σ : ℂ)).re := by
    calc
      ‖LSeries f s‖ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ :=
        norm_tsum_le_tsum_norm hsummable
      _ = ∑' n : ℕ, ‖LSeries.term f (σ : ℂ) n‖ := htermnorm
      _ = (LSeries f (σ : ℂ)).re := hreal
  have hpole : (LSeries f (σ : ℂ)).re ≤ 1 / (σ - 1) + P := by
    have hp := hcp σ hσ hσ2
    have hident : LSeries f (σ : ℂ) =
        -(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)) := by
      dsimp only [f]
      rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hσ),
        neg_div]
    rw [hident]
    calc
      _ ≤ 1 / (σ - 1) + cp := hp
      _ = cp + 1 / (σ - 1) := by ring
      _ ≤ P + 1 / (σ - 1) := add_le_add_left (le_max_left cp 0) _
      _ = 1 / (σ - 1) + P := by ring
  have hseries : LSeries f s =
      -deriv riemannZeta s / riemannZeta s := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by
      rw [hsre]
      exact hσ), neg_div]
  simpa only [s, hseries] using le_trans hnormL hpole

/-- Logarithmic form of the `3-4-1` lower bound. -/
theorem neg_log_norm_zeta_le_of_341
    (σ₀ t U : ℝ) (hσ : 1 < σ₀)
    (hU : Real.log ‖riemannZeta ((σ₀ : ℂ) + I * (2 * t))‖ ≤ U) :
    -Real.log ‖riemannZeta ((σ₀ : ℂ) + I * t)‖ ≤
      (3 * Real.log (1 + 1 / (σ₀ - 1)) + U) / 4 := by
  have hcne : riemannZeta ((σ₀ : ℂ) + I * t) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  have hcn : 0 < ‖riemannZeta ((σ₀ : ℂ) + I * t)‖ :=
    norm_pos_iff.mpr hcne
  have hbase : 0 < 1 + 1 / (σ₀ - 1) := by
    have : 0 < σ₀ - 1 := by linarith
    positivity
  have hlower := zeta_norm_lower_341_of_log_upper σ₀ t U hσ hU
  have hden : 0 < (1 + 1 / (σ₀ - 1)) ^ 3 * Real.exp U := by
    positivity
  have hlog := Real.log_le_log (by positivity) hlower
  rw [Real.log_div (by norm_num) hden.ne', Real.log_one,
    Real.log_mul (pow_ne_zero 3 hbase.ne') (Real.exp_ne_zero U),
    Real.log_pow, Real.log_exp, Real.log_pow] at hlog
  push_cast at hlog
  linarith

set_option maxHeartbeats 2000000 in
/-- **V-C4-3.**  In the closed half-width region, the regular part of
`-zeta'/zeta` has polynomial logarithmic size.  The recorded exponent is
`2 + 1/a`; this deliberately coarse exponent keeps the interface independent
of all constants in the growth estimate. -/
theorem zeta_regular_logDeriv_bound_of_growth
    {t₀ a B b B₀ : ℝ} (h : ZetaGrowthBound t₀ a B b B₀)
    (ha : 1 < a) (hB : 0 < B) (hb : 0 ≤ b) (hB₀ : 0 ≤ B₀) :
    ∃ c C t₁ : ℝ, 0 < c ∧ 1 ≤ C ∧ t₀ ≤ t₁ ∧
      ∀ z : ℂ, t₁ ≤ |z.im| →
        1 - zetaGrowthRegionEta a c z.im / 2 ≤ z.re → z.re ≤ 2 →
        z ≠ 1 →
        ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤
          C * (Real.log |z.im|) ^ zetaGrowthLogDerivExponent a := by
  obtain ⟨c₀, tz, hc₀, ht₀tz, hzero⟩ := zeta_zero_free_of_growth h ha hB hb hB₀
  obtain ⟨P, hP0, hpole⟩ := exists_norm_zeta_logDeriv_pole_bound
  let d : ℝ := min (1 / 8) (c₀ / 2)
  have hd0 : 0 < d := lt_min (by norm_num) (by positivity)
  have hdeighth : d ≤ 1 / 8 := min_le_left _ _
  have hdquarter : d ≤ 1 / 4 := by linarith
  have hdcHalf : d ≤ c₀ / 2 := min_le_right _ _
  have hdc : d ≤ c₀ := by linarith
  let A : ℝ := 2 * B + 2 * b + B₀
  let E : ℝ := 2 * b + B₀
  let D : ℝ := A + (3 * (1 + 4 / d) + E) / 4
  let C : ℝ := 100 * (D + P + 1) / d
  have hA0 : 0 ≤ A := by dsimp only [A]; nlinarith
  have hE0 : 0 ≤ E := by dsimp only [E]; nlinarith
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hC1 : 1 ≤ C := by
    dsimp only [C]
    have hdle : d ≤ 1 := le_trans hdquarter (by norm_num)
    rw [le_div_iff₀ hd0]
    nlinarith
  let H : ℝ := max 2 (max t₀ (max tz (max B (max b (max B₀ (1 / d))))))
  let t₁ : ℝ := max (2 * tz + 2) (max (t₀ + 1) (Real.exp (Real.exp H)))
  have hH2 : 2 ≤ H := le_max_left _ _
  have ht₀t₁ : t₀ ≤ t₁ := by
    have : t₀ + 1 ≤ t₁ :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    linarith
  refine ⟨c₀, C, t₁, hc₀, hC1, ht₀t₁, ?_⟩
  intro z hzheight hzre hzre2 hz1
  let u : ℝ := |z.im|
  let L : ℝ := Real.log u
  let ell : ℝ := Real.log L
  have huExp : Real.exp (Real.exp H) ≤ u :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hzheight)
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos _) huExp
  have hLexp : Real.exp H ≤ L := by
    dsimp only [L]
    exact (Real.le_log_iff_exp_le hu0).mpr huExp
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos H) hLexp
  have hellH : H ≤ ell := by
    dsimp only [ell]
    exact (Real.le_log_iff_exp_le hL0).mpr hLexp
  have hell2 : 2 ≤ ell := le_trans hH2 hellH
  have hell0 : 0 < ell := by linarith
  have hL2 : 2 ≤ L := by
    have : Real.exp 2 ≤ L := le_trans (Real.exp_le_exp.mpr hH2) hLexp
    linarith [Real.add_one_le_exp (2 : ℝ)]
  have hexpH3 : 3 ≤ Real.exp H := by
    have := Real.add_one_le_exp H
    linarith
  have huFour : 4 ≤ u := by
    have := Real.add_one_le_exp (Real.exp H)
    exact le_trans (by linarith) huExp
  have hellL : ell ≤ L := by
    have := Real.log_le_sub_one_of_pos hL0
    linarith
  have hutz : tz + 1 ≤ u := by
    have : 2 * tz + 2 ≤ u := le_trans (le_max_left _ _) hzheight
    linarith
  have hut₀ : t₀ + 1 ≤ u := by
    have : t₀ + 1 ≤ u :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hzheight)
    exact this
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  let L₂ : ℝ := Real.log (2 * u)
  let ell₂ : ℝ := Real.log L₂
  have hL₂eq : L₂ = Real.log 2 + L := by
    dsimp only [L₂, L]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hu0.ne']
  have hLL₂ : L ≤ L₂ := by
    rw [hL₂eq]
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hL₂two : L₂ ≤ 2 * L := by rw [hL₂eq]; linarith
  have hL₂0 : 0 < L₂ := lt_of_lt_of_le hL0 hLL₂
  have hellEll₂ : ell ≤ ell₂ := by
    dsimp only [ell, ell₂]
    exact Real.log_le_log hL0 hLL₂
  have hell₂Two : ell₂ ≤ 2 * ell := by
    have hh := Real.log_le_log hL₂0 hL₂two
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hL0.ne'] at hh
    dsimp only [ell, ell₂]
    linarith
  have hell₂one : 1 ≤ ell₂ := by linarith
  have hell₂L₂ : ell₂ ≤ L₂ := by
    have := Real.log_le_sub_one_of_pos hL₂0
    linarith
  have hwidth₂ : zetaGrowthWidth a (2 * u) =
      zetaGrowthWidthFromLogs a L₂ ell₂ := by
    rw [zetaGrowthWidth, zetaGrowthWidthFromLogs]
    have habs : |2 * u| = 2 * u := by rw [abs_of_pos (by positivity)]
    rw [habs]
  let eta : ℝ := zetaGrowthRegionEta a c₀ z.im
  have hetaDef : eta = min (1 / 8) ((c₀ / 2) * zetaGrowthWidth a (2 * u)) := by
    dsimp only [eta, zetaGrowthRegionEta, u]
  have hwidth₂pos : 0 < zetaGrowthWidth a (2 * u) := by
    rw [hwidth₂, zetaGrowthWidthFromLogs]
    positivity
  have heta0 : 0 < eta := by
    rw [hetaDef]
    exact lt_min (by norm_num) (mul_pos (by positivity) hwidth₂pos)
  have hetaEighth : eta ≤ 1 / 8 := by rw [hetaDef]; exact min_le_left _ _
  have hetaQuarter : eta ≤ 1 / 4 := by linarith
  have hetaWidth : eta ≤ c₀ * zetaGrowthWidth a (2 * u) := by
    rw [hetaDef]
    have hm := min_le_right (1 / 8 : ℝ) ((c₀ / 2) * zetaGrowthWidth a (2 * u))
    nlinarith [hwidth₂pos]
  have hetaDoubleWidth : 2 * eta ≤ c₀ * zetaGrowthWidth a (2 * u) := by
    rw [hetaDef]
    have hm := min_le_right (1 / 8 : ℝ) ((c₀ / 2) * zetaGrowthWidth a (2 * u))
    nlinarith
  have hwidthLower : 1 / L₂ ≤ zetaGrowthWidth a (2 * u) := by
    rw [hwidth₂]
    exact one_div_log_le_zetaGrowthWidthFromLogs ha hL₂0 hell₂one hell₂L₂
  have hetaLower : d / L₂ ≤ eta := by
    rw [hetaDef, le_min_iff]
    constructor
    · have hL₂one : 1 ≤ L₂ := by linarith
      have := div_le_self hd0.le hL₂one
      exact le_trans this hdeighth
    · have hdcdiv : d / L₂ ≤ (c₀ / 2) / L₂ :=
        div_le_div_of_nonneg_right hdcHalf hL₂0.le
      have hcwidth := mul_le_mul_of_nonneg_left hwidthLower (by positivity : 0 ≤ c₀ / 2)
      exact le_trans hdcdiv (by simpa [div_eq_mul_inv] using hcwidth)
  have hinvEta : 1 / eta ≤ 2 * L / d := by
    have hinv := one_div_le_one_div_of_le (div_pos hd0 hL₂0) hetaLower
    have hLratio : L₂ / d ≤ 2 * L / d :=
      div_le_div_of_nonneg_right hL₂two hd0.le
    have heq : 1 / (d / L₂) = L₂ / d := by field_simp
    rw [heq] at hinv
    exact le_trans hinv hLratio
  let center : ℂ := (((1 + eta / 2 : ℝ) : ℂ) + I * z.im)
  have himag_bounds : ∀ w ∈ Metric.ball center (2 * eta),
      tz ≤ |w.im| ∧ t₀ ≤ |w.im| ∧ 3 < |w.im| ∧ |w.im| ≤ 2 * u := by
    intro w hw
    have hdist : ‖w - center‖ < 2 * eta := by
      rw [Metric.mem_ball, dist_eq_norm] at hw
      exact hw
    have him : |w.im - z.im| < 2 * eta := by
      calc
        |w.im - z.im| = |(w - center).im| := by simp [center]
        _ ≤ ‖w - center‖ := Complex.abs_im_le_norm _
        _ < 2 * eta := hdist
    have hlower : u < |w.im| + 2 * eta := by
      have habs := abs_sub_abs_le_abs_sub z.im w.im
      have heq : |z.im - w.im| = |w.im - z.im| := by
        rw [show z.im - w.im = -(w.im - z.im) by ring, abs_neg]
      rw [heq] at habs
      dsimp only [u]
      linarith
    have hupper : |w.im| < u + 2 * eta := by
      have := abs_sub_abs_le_abs_sub w.im z.im
      dsimp only [u]
      linarith
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hwidth_mono : ∀ w ∈ Metric.ball center (2 * eta),
      zetaGrowthWidth a (2 * u) ≤ zetaGrowthWidth a w.im := by
    intro w hw
    obtain ⟨_, _, hwthree, hwupper⟩ := himag_bounds w hw
    have hwabs0 : 0 < |w.im| := by linarith
    let Lw : ℝ := Real.log |w.im|
    let ellw : ℝ := Real.log Lw
    have hLw0 : 0 < Lw := by
      dsimp only [Lw]
      exact Real.log_pos (by linarith)
    have hLw : Lw ≤ L₂ := by
      dsimp only [Lw, L₂]
      exact Real.log_le_log hwabs0 hwupper
    have hellw0 : 0 < ellw := by
      dsimp only [ellw]
      apply Real.log_pos
      dsimp only [Lw]
      calc
        1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
        _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
        _ < Real.log |w.im| := Real.log_lt_log (by norm_num) hwthree
    have hellw : ellw ≤ ell₂ := by
      dsimp only [ellw, ell₂]
      exact Real.log_le_log hLw0 hLw
    have haux := zetaGrowthWidthFromLogs_anti ha hLw0 hLw hellw0 hellw
    have hwform : zetaGrowthWidth a w.im =
        zetaGrowthWidthFromLogs a Lw ellw := by
      rfl
    calc
      zetaGrowthWidth a (2 * u) =
          zetaGrowthWidthFromLogs a L₂ ell₂ := hwidth₂
      _ ≤ zetaGrowthWidthFromLogs a Lw ellw := haux
      _ = zetaGrowthWidth a w.im := hwform.symm
  have hne : ∀ w ∈ Metric.ball center (2 * eta), riemannZeta w ≠ 0 := by
    intro w hw hwzero
    obtain ⟨htzw, _, _, _⟩ := himag_bounds w hw
    have hzbound := hzero w.re w.im htzw (by
      have hwform : ((w.re : ℝ) : ℂ) + I * w.im = w := by
        apply Complex.ext <;> simp
      rw [hwform]
      exact hwzero)
    have hwidth := hwidth_mono w hw
    have hetaBig : 2 * eta ≤ c₀ * zetaGrowthWidth a w.im :=
      le_trans hetaDoubleWidth (mul_le_mul_of_nonneg_left hwidth hc₀.le)
    have hwreal : 1 - 3 * eta / 2 < w.re := by
      have hdist : ‖w - center‖ < 2 * eta := by
        rw [Metric.mem_ball, dist_eq_norm] at hw
        exact hw
      have hre : |w.re - (1 + eta / 2)| < 2 * eta := by
        calc
          |w.re - (1 + eta / 2)| = |(w - center).re| := by simp [center]
          _ ≤ ‖w - center‖ := Complex.abs_re_le_norm _
          _ < 2 * eta := hdist
      rw [abs_lt] at hre
      linarith
    have hzbound' : w.re ≤ 1 - c₀ * zetaGrowthWidth a w.im := by
      simpa only [show c₀ * (Real.log (Real.log |w.im|)) ^ (1 / a - 1) /
          (Real.log |w.im|) ^ (1 / a) = c₀ * zetaGrowthWidth a w.im by
        rw [zetaGrowthWidth]
        ring] using hzbound
    linarith
  have hballPole : Metric.ball center (2 * eta) ⊆ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    intro w hw
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hw1
    obtain ⟨_, _, hwthree, _⟩ := himag_bounds w hw
    rw [hw1] at hwthree
    norm_num at hwthree
  have hanalytic : AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ : Set ℂ) := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
    intro w hw
    exact (differentiableAt_riemannZeta
      (Set.mem_compl_singleton_iff.mp hw)).differentiableWithinAt
  have hlogUpper : ∀ w ∈ Metric.ball center (2 * eta),
      Real.log ‖riemannZeta w‖ ≤ A * L := by
    intro w hw
    obtain ⟨_, ht₀w, hwthree, hwupper⟩ := himag_bounds w hw
    have hdist : ‖w - center‖ < 2 * eta := by
      rw [Metric.mem_ball, dist_eq_norm] at hw
      exact hw
    have hre : |w.re - (1 + eta / 2)| < 2 * eta := by
      calc
        |w.re - (1 + eta / 2)| = |(w - center).re| := by simp [center]
        _ ≤ ‖w - center‖ := Complex.abs_re_le_norm _
        _ < 2 * eta := hdist
    rw [abs_lt] at hre
    have hwreLower : 1 - 1 / 4 ≤ w.re := by linarith
    have hwreUpper : w.re ≤ 2 := by linarith
    have hmaxOne : max (1 - w.re) 0 ≤ 1 := by
      rw [max_le_iff]
      constructor <;> linarith
    have hpowOne : (max (1 - w.re) 0) ^ a ≤ 1 :=
      Real.rpow_le_one (by positivity) hmaxOne (by linarith)
    have hwabs0 : 0 < |w.im| := by linarith
    have hlogw0 : 0 ≤ Real.log |w.im| :=
      Real.log_nonneg (by linarith)
    have hlogw : Real.log |w.im| ≤ L₂ := by
      dsimp only [L₂]
      exact Real.log_le_log hwabs0 hwupper
    have hloglogw : Real.log (Real.log |w.im|) ≤ ell₂ := by
      dsimp only [ell₂]
      exact Real.log_le_log (Real.log_pos (by linarith)) hlogw
    have hBterm : B * (max (1 - w.re) 0) ^ a * Real.log |w.im| ≤
        2 * B * L := by
      calc
        B * (max (1 - w.re) 0) ^ a * Real.log |w.im| ≤
            B * 1 * Real.log |w.im| := by gcongr
        _ ≤ B * L₂ := by simpa using mul_le_mul_of_nonneg_left hlogw hB.le
        _ ≤ B * (2 * L) := mul_le_mul_of_nonneg_left hL₂two hB.le
        _ = 2 * B * L := by ring
    have hbterm : b * Real.log (Real.log |w.im|) ≤ 2 * b * L := by
      calc
        b * Real.log (Real.log |w.im|) ≤ b * ell₂ :=
          mul_le_mul_of_nonneg_left hloglogw hb
        _ ≤ b * (2 * ell) := mul_le_mul_of_nonneg_left hell₂Two hb
        _ ≤ b * (2 * L) := mul_le_mul_of_nonneg_left (by linarith) hb
        _ = 2 * b * L := by ring
    have hB₀term : B₀ ≤ B₀ * L := by
      have hLone : 1 ≤ L := by linarith
      nlinarith
    have hgrowth := h.bound w.re w.im ht₀w hwreLower hwreUpper
    have hwform : ((w.re : ℝ) : ℂ) + I * w.im = w := by
      apply Complex.ext <;> simp
    rw [hwform] at hgrowth
    dsimp only [A]
    linarith
  have hcenterGrowthTwice : Real.log
      ‖riemannZeta ((((1 + eta / 2 : ℝ) : ℂ) + I * (2 * z.im)))‖ ≤ E * L := by
    have habsTwice : |2 * z.im| = 2 * u := by
      dsimp only [u]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have ht₀twice : t₀ ≤ |2 * z.im| := by rw [habsTwice]; linarith
    have hgrowth := h.bound (1 + eta / 2) (2 * z.im) ht₀twice
      (by linarith) (by linarith)
    have hzeroPow : (max (1 - (1 + eta / 2)) 0) ^ a = 0 := by
      rw [max_eq_right (by linarith), Real.zero_rpow (by linarith : a ≠ 0)]
    rw [hzeroPow, mul_zero, zero_mul, zero_add] at hgrowth
    have hloglogTwice : Real.log (Real.log |2 * z.im|) = ell₂ := by
      rw [habsTwice]
    rw [hloglogTwice] at hgrowth
    have hbterm : b * ell₂ ≤ 2 * b * L := by
      calc
        b * ell₂ ≤ b * (2 * ell) := mul_le_mul_of_nonneg_left hell₂Two hb
        _ ≤ b * (2 * L) := mul_le_mul_of_nonneg_left (by linarith) hb
        _ = 2 * b * L := by ring
    have hB₀term : B₀ ≤ B₀ * L := by
      have hLone : 1 ≤ L := by linarith
      nlinarith
    dsimp only [E]
    have hscalar : b * ell₂ + B₀ ≤ (2 * b + B₀) * L := by linarith
    have hresult := le_trans hgrowth hscalar
    convert hresult using 1 <;> push_cast <;> ring
  have hInvBase : 1 / (eta / 2) ≤ 4 * L / d := by
    calc
      1 / (eta / 2) = 2 * (1 / eta) := by field_simp
      _ ≤ 2 * (2 * L / d) := mul_le_mul_of_nonneg_left hinvEta (by norm_num)
      _ = 4 * L / d := by ring
  have hlogBase : Real.log (1 + 1 / (eta / 2)) ≤ (1 + 4 / d) * L := by
    have hbase0 : 0 < 1 + 1 / (eta / 2) := by positivity
    have hlog := Real.log_le_sub_one_of_pos hbase0
    calc
      Real.log (1 + 1 / (eta / 2)) ≤ 1 / (eta / 2) := by linarith
      _ ≤ 4 * L / d := hInvBase
      _ ≤ (1 + 4 / d) * L := by
        rw [show (1 + 4 / d) * L = L + 4 * L / d by ring]
        exact le_add_of_nonneg_left hL0.le
  have hcenterLower : -Real.log ‖riemannZeta center‖ ≤
      ((3 * (1 + 4 / d) + E) / 4) * L := by
    have hlower := neg_log_norm_zeta_le_of_341 (1 + eta / 2) z.im (E * L)
      (by linarith) hcenterGrowthTwice
    have hlower' : -Real.log ‖riemannZeta center‖ ≤
        (3 * Real.log (1 + 1 / (eta / 2)) + E * L) / 4 := by
      simpa only [center, show (1 + eta / 2 : ℝ) - 1 = eta / 2 by ring] using hlower
    calc
      -Real.log ‖riemannZeta center‖ ≤
          (3 * Real.log (1 + 1 / (eta / 2)) + E * L) / 4 := hlower'
      _ ≤ (3 * ((1 + 4 / d) * L) + E * L) / 4 := by gcongr
      _ = ((3 * (1 + 4 / d) + E) / 4) * L := by ring
  have hcenterNe : riemannZeta center ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp [center]; linarith)
  have hcenterNorm0 : 0 < ‖riemannZeta center‖ := norm_pos_iff.mpr hcenterNe
  have hratio : ∀ w ∈ Metric.ball center (2 * eta),
      ‖riemannZeta w‖ ≤ Real.exp (D * L) * ‖riemannZeta center‖ := by
    intro w hw
    by_cases hwzero : riemannZeta w = 0
    · rw [hwzero, norm_zero]
      positivity
    · have hwnorm0 : 0 < ‖riemannZeta w‖ := norm_pos_iff.mpr hwzero
      have hlogratio : Real.log ‖riemannZeta w‖ ≤
          D * L + Real.log ‖riemannZeta center‖ := by
        have hupper := hlogUpper w hw
        dsimp only [D]
        linarith
      have hexp := Real.exp_le_exp.mpr hlogratio
      rw [Real.exp_add, Real.exp_log hwnorm0, Real.exp_log hcenterNorm0] at hexp
      exact hexp
  have hm2 : 2 ≤ zetaGrowthLogDerivExponent a := by
    dsimp only [zetaGrowthLogDerivExponent]
    have : 0 < 1 / a := one_div_pos.mpr (by linarith)
    linarith
  have hLsq : L ^ 2 ≤ L ^ zetaGrowthLogDerivExponent a := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) hm2
  have hLsqOne : 1 ≤ L ^ 2 := by nlinarith
  have hC0 : 0 ≤ C := le_trans zero_le_one hC1
  have hrecipOne : ‖(1 : ℂ) / (z - 1)‖ ≤ 1 := by
    have hnormIm : u ≤ ‖z - 1‖ := by
      dsimp only [u]
      calc
        |z.im| = |(z - 1).im| := by simp
        _ ≤ ‖z - 1‖ := Complex.abs_im_le_norm _
    have hnormOne : 1 ≤ ‖z - 1‖ := le_trans (by linarith) hnormIm
    rw [norm_div, norm_one]
    simpa using one_div_le_one_div_of_le one_pos hnormOne
  have hcoefNear : 48 * (D + 1) / d + 1 ≤ C := by
    dsimp only [C]
    rw [le_div_iff₀ hd0]
    field_simp
    nlinarith
  have hcoefRight : 4 / d + P ≤ C := by
    dsimp only [C]
    rw [le_div_iff₀ hd0]
    field_simp
    nlinarith
  by_cases hzNear : z.re ≤ 1 + eta
  · have hzreEta : 1 - eta / 2 ≤ z.re := by
      simpa only [eta] using hzre
    have hzclosed : z ∈ Metric.closedBall center eta := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hdiff : z - center = ((z.re - (1 + eta / 2) : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [center]
      rw [hdiff, norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hzclosed' : z ∈ Metric.closedBall center (2 * eta / 2) := by
      simpa using hzclosed
    have hbc := norm_logDeriv_le_on_half_closedBall isOpen_compl_singleton
      hanalytic (by positivity : 0 < 2 * eta) hballPole hne hratio hzclosed'
    have hbcEta : ‖deriv riemannZeta z / riemannZeta z‖ ≤
        24 * (D * L + 1) / eta := by
      calc
        ‖deriv riemannZeta z / riemannZeta z‖ ≤
            24 * (D * L + 1) / (2 * eta) := hbc
        _ ≤ 24 * (D * L + 1) / eta := by
          have hnum0 : 0 ≤ 24 * (D * L + 1) := by positivity
          exact div_le_div_of_nonneg_left hnum0 heta0 (by linarith)
    have hbcEtaNeg : ‖-deriv riemannZeta z / riemannZeta z‖ ≤
        24 * (D * L + 1) / eta := by
      simpa only [neg_div, norm_neg] using hbcEta
    have hDL : D * L + 1 ≤ (D + 1) * L := by
      nlinarith
    have hbcCoarse : 24 * (D * L + 1) / eta ≤
        (48 * (D + 1) / d) * L ^ 2 := by
      calc
        24 * (D * L + 1) / eta =
            24 * (D * L + 1) * (1 / eta) := by ring
        _ ≤ 24 * ((D + 1) * L) * (2 * L / d) := by
          gcongr
        _ = (48 * (D + 1) / d) * L ^ 2 := by ring
    have hregular : ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤
        24 * (D * L + 1) / eta + 1 := by
      calc
        ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤
            ‖-deriv riemannZeta z / riemannZeta z‖ + ‖(1 : ℂ) / (z - 1)‖ :=
          norm_sub_le _ _
        _ ≤ 24 * (D * L + 1) / eta + 1 := by
          exact add_le_add hbcEtaNeg hrecipOne
    calc
      ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤
          24 * (D * L + 1) / eta + 1 := hregular
      _ ≤ (48 * (D + 1) / d) * L ^ 2 + 1 := by linarith
      _ ≤ (48 * (D + 1) / d + 1) * L ^ 2 := by
        have hcoef0 : 0 ≤ 48 * (D + 1) / d := by positivity
        nlinarith
      _ ≤ C * L ^ 2 := mul_le_mul_of_nonneg_right hcoefNear (sq_nonneg L)
      _ ≤ C * L ^ zetaGrowthLogDerivExponent a :=
        mul_le_mul_of_nonneg_left hLsq hC0
      _ = C * (Real.log |z.im|) ^ zetaGrowthLogDerivExponent a := by rfl
  · have hzRight : 1 + eta < z.re := lt_of_not_ge hzNear
    have hzform : ((z.re : ℝ) : ℂ) + I * z.im = z := by
      apply Complex.ext <;> simp
    have hp := hpole z.re z.im (by linarith) hzre2
    rw [hzform] at hp
    have hnormReal : z.re - 1 ≤ ‖z - 1‖ := by
      calc
        z.re - 1 = |z.re - 1| := (abs_of_pos (by linarith)).symm
        _ = |(z - 1).re| := by simp
        _ ≤ ‖z - 1‖ := Complex.abs_re_le_norm _
    have hrecipReal : ‖(1 : ℂ) / (z - 1)‖ ≤ 1 / (z.re - 1) := by
      rw [norm_div, norm_one]
      exact one_div_le_one_div_of_le (by linarith) hnormReal
    have hrecipEta : 1 / (z.re - 1) ≤ 1 / eta :=
      one_div_le_one_div_of_le heta0 (by linarith)
    have hregular : ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤
        2 * (1 / eta) + P := by
      calc
        ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤
            ‖-deriv riemannZeta z / riemannZeta z‖ + ‖(1 : ℂ) / (z - 1)‖ :=
          norm_sub_le _ _
        _ ≤ (1 / (z.re - 1) + P) + 1 / (z.re - 1) :=
          add_le_add hp hrecipReal
        _ ≤ (1 / eta + P) + 1 / eta := by
          have hfirst : 1 / (z.re - 1) + P ≤ 1 / eta + P := by gcongr
          exact add_le_add hfirst hrecipEta
        _ = 2 * (1 / eta) + P := by ring
    have hcoarse : 2 * (1 / eta) + P ≤ (4 / d + P) * L := by
      have hLone : 1 ≤ L := by linarith only [hL2]
      have hPin : P ≤ P * L := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hLone hP0
      have hmain : 2 * (1 / eta) ≤ (4 / d) * L := by
        calc
          2 * (1 / eta) ≤ 2 * (2 * L / d) :=
            mul_le_mul_of_nonneg_left hinvEta (by norm_num)
          _ = (4 / d) * L := by ring
      calc
        2 * (1 / eta) + P ≤ (4 / d) * L + P * L := add_le_add hmain hPin
        _ = (4 / d + P) * L := by ring
    have hLleSq : L ≤ L ^ 2 := by
      calc
        L = L * 1 := by ring
        _ ≤ L * L := mul_le_mul_of_nonneg_left (by linarith only [hL2]) hL0.le
        _ = L ^ 2 := by ring
    calc
      ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤
          2 * (1 / eta) + P := hregular
      _ ≤ (4 / d + P) * L := hcoarse
      _ ≤ C * L := mul_le_mul_of_nonneg_right hcoefRight hL0.le
      _ ≤ C * L ^ 2 := mul_le_mul_of_nonneg_left hLleSq hC0
      _ ≤ C * L ^ zetaGrowthLogDerivExponent a :=
        mul_le_mul_of_nonneg_left hLsq hC0
      _ = C * (Real.log |z.im|) ^ zetaGrowthLogDerivExponent a := by rfl

end ExpSums

end MoltResearch
