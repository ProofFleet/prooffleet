import MoltResearch.Discrepancy.ZetaGrowthLogDeriv

/-!
# Sharpened logarithmic derivative bound from zeta growth

This leaf keeps the logarithmic growth term on the Borel--Carathéodory disc
at its natural `log log |t|` size.  Together with the true reciprocal
zero-free width, this gives

`(log |t|) ^ (1 / a) * (log log |t|) ^ 2`,

and the two iterated-log factors are absorbed by an extra exponent `1/10`.
-/

namespace MoltResearch

namespace ExpSums

open Complex

/-- The logarithmic exponent recorded by the sharpened regular-part bound. -/
noncomputable def zetaGrowthLogDerivExponentSharp (a : ℝ) : ℝ :=
  1 / a + 1 / 10

private noncomputable def zetaGrowthWidthFromLogsSharp
    (a L ell : ℝ) : ℝ :=
  ell ^ (1 / a - 1) / L ^ (1 / a)

private theorem zetaGrowthWidthFromLogsSharp_anti
    {a L₁ L₂ ell₁ ell₂ : ℝ} (ha : 1 < a)
    (hL₁ : 0 < L₁) (hL : L₁ ≤ L₂)
    (hell₁ : 0 < ell₁) (hell : ell₁ ≤ ell₂) :
    zetaGrowthWidthFromLogsSharp a L₂ ell₂ ≤
      zetaGrowthWidthFromLogsSharp a L₁ ell₁ := by
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
  dsimp only [zetaGrowthWidthFromLogsSharp]
  exact div_le_div₀ (Real.rpow_nonneg hell₁.le _) hnum
    (Real.rpow_pos_of_pos hL₁ _) hden

private theorem zetaGrowthWidthFromLogsSharp_le_one
    {a L ell : ℝ} (ha : 1 < a) (hL : 1 ≤ L) (hell : 1 ≤ ell) :
    zetaGrowthWidthFromLogsSharp a L ell ≤ 1 := by
  have hexp : 1 / a - 1 ≤ 0 := by
    have ha0 : 0 < a := by linarith
    have hi : 1 / a ≤ 1 := (div_le_one ha0).2 (by linarith)
    linarith
  have hnum : ell ^ (1 / a - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hell hexp
  have hden : 1 ≤ L ^ (1 / a) := by
    have hp : 0 ≤ 1 / a := (one_div_pos.mpr (by linarith)).le
    calc
      1 = (1 : ℝ) ^ (1 / a) := (Real.one_rpow _).symm
      _ ≤ L ^ (1 / a) := Real.rpow_le_rpow (by norm_num) hL hp
  dsimp only [zetaGrowthWidthFromLogsSharp]
  exact (div_le_one (Real.rpow_pos_of_pos (by linarith) _)).2
    (le_trans hnum hden)

private theorem zetaGrowthWidthFromLogsSharp_lower
    {a L ell : ℝ} (ha : 1 < a) (hL : 0 < L) (hell : 1 ≤ ell) :
    1 / (ell * L ^ (1 / a)) ≤
      zetaGrowthWidthFromLogsSharp a L ell := by
  have hell0 : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hpow : ell ^ (-1 : ℝ) ≤ ell ^ (1 / a - 1) :=
    Real.rpow_le_rpow_of_exponent_le hell (by
      have : 0 < 1 / a := one_div_pos.mpr (by linarith)
      linarith)
  have hden : 0 < L ^ (1 / a) := Real.rpow_pos_of_pos hL _
  rw [Real.rpow_neg_one, inv_eq_one_div] at hpow
  dsimp only [zetaGrowthWidthFromLogsSharp]
  convert div_le_div_of_nonneg_right hpow hden.le using 1 <;> field_simp

set_option maxHeartbeats 10000000 in
/-- **V-C4-3′.**  The regular part has exponent `1/a + 1/10` once the
growth bound is used at the actual width of the zero-free disc. -/
theorem zeta_regular_logDeriv_bound_of_growth_sharp
    {t₀ a B b B₀ : ℝ} (h : ZetaGrowthBound t₀ a B b B₀)
    (ha : 1 < a) (hB : 0 < B) (hb : 0 ≤ b) (hB₀ : 0 ≤ B₀) :
    ∃ c C t₁ : ℝ, 0 < c ∧ 1 ≤ C ∧ t₀ ≤ t₁ ∧
      ∀ z : ℂ, t₁ ≤ |z.im| →
        1 - zetaGrowthRegionEta a c z.im / 2 ≤ z.re → z.re ≤ 2 →
        z ≠ 1 →
        ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤
          C * (Real.log |z.im|) ^ zetaGrowthLogDerivExponentSharp a := by
  obtain ⟨c₀, tz, hc₀, ht₀tz, hzero⟩ := zeta_zero_free_of_growth h ha hB hb hB₀
  obtain ⟨P, hP0, hpole⟩ := exists_norm_zeta_logDeriv_pole_bound
  let d : ℝ := min (1 / 8) (c₀ / 2)
  have hd0 : 0 < d := lt_min (by norm_num) (by positivity)
  have hdeighth : d ≤ 1 / 8 := min_le_left _ _
  have hdcHalf : d ≤ c₀ / 2 := min_le_right _ _
  let A : ℝ := B * c₀ ^ a + 2 * b + B₀
  let E : ℝ := 2 * b + B₀
  let D : ℝ := A + (3 * (2 + 8 / d) + E) / 4
  let C : ℝ := 100000 * (D + P + 1) / d ^ 2
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hC1 : 1 ≤ C := by
    dsimp only [C]
    have hdle : d ≤ 1 := le_trans hdeighth (by norm_num)
    rw [le_div_iff₀ (sq_pos_of_pos hd0)]
    nlinarith [sq_nonneg d]
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
  have huFour : 4 ≤ u := by
    have hexpH3 : 3 ≤ Real.exp H := by
      have := Real.add_one_le_exp H
      linarith
    have := Real.add_one_le_exp (Real.exp H)
    exact le_trans (by linarith) huExp
  have hellL : ell ≤ L := by
    have := Real.log_le_sub_one_of_pos hL0
    linarith
  have hutz : tz + 1 ≤ u := by
    have : 2 * tz + 2 ≤ u := le_trans (le_max_left _ _) hzheight
    linarith
  have hut₀ : t₀ + 1 ≤ u := by
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hzheight)
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
  have hL₂one : 1 ≤ L₂ := by linarith
  have hwidth₂ : zetaGrowthWidth a (2 * u) =
      zetaGrowthWidthFromLogsSharp a L₂ ell₂ := by
    rw [zetaGrowthWidth, zetaGrowthWidthFromLogsSharp]
    have habs : |2 * u| = 2 * u := by rw [abs_of_pos (by positivity)]
    rw [habs]
  let eta : ℝ := zetaGrowthRegionEta a c₀ z.im
  have hetaDef : eta = min (1 / 8) ((c₀ / 2) * zetaGrowthWidth a (2 * u)) := by
    dsimp only [eta, zetaGrowthRegionEta, u]
  have hwidth₂pos : 0 < zetaGrowthWidth a (2 * u) := by
    rw [hwidth₂, zetaGrowthWidthFromLogsSharp]
    positivity
  have hwidth₂le : zetaGrowthWidth a (2 * u) ≤ 1 := by
    rw [hwidth₂]
    exact zetaGrowthWidthFromLogsSharp_le_one ha hL₂one hell₂one
  have heta0 : 0 < eta := by
    rw [hetaDef]
    exact lt_min (by norm_num) (mul_pos (by positivity) hwidth₂pos)
  have hetaEighth : eta ≤ 1 / 8 := by rw [hetaDef]; exact min_le_left _ _
  have hetaDoubleWidth : 2 * eta ≤ c₀ * zetaGrowthWidth a (2 * u) := by
    rw [hetaDef]
    have hm := min_le_right (1 / 8 : ℝ) ((c₀ / 2) * zetaGrowthWidth a (2 * u))
    nlinarith
  have hetaWidthLower : d * zetaGrowthWidth a (2 * u) ≤ eta := by
    rw [hetaDef, le_min_iff]
    constructor
    · calc
        d * zetaGrowthWidth a (2 * u) ≤ d * 1 :=
          mul_le_mul_of_nonneg_left hwidth₂le hd0.le
        _ ≤ 1 / 8 := by simpa using hdeighth
    · exact mul_le_mul_of_nonneg_right hdcHalf hwidth₂pos.le
  have hwidthLower : 1 / (ell₂ * L₂ ^ (1 / a)) ≤
      zetaGrowthWidth a (2 * u) := by
    rw [hwidth₂]
    exact zetaGrowthWidthFromLogsSharp_lower ha hL₂0 hell₂one
  have hetaLower : d / (ell₂ * L₂ ^ (1 / a)) ≤ eta := by
    calc
      d / (ell₂ * L₂ ^ (1 / a)) =
          d * (1 / (ell₂ * L₂ ^ (1 / a))) := by ring
      _ ≤ d * zetaGrowthWidth a (2 * u) :=
        mul_le_mul_of_nonneg_left hwidthLower hd0.le
      _ ≤ eta := hetaWidthLower
  have hia0 : 0 < 1 / a := one_div_pos.mpr (by linarith)
  have hia1 : 1 / a ≤ 1 := by
    rw [div_le_one (by linarith : 0 < a)]
    linarith
  have hL₂pow : L₂ ^ (1 / a) ≤ 2 * L ^ (1 / a) := by
    have hmono := Real.rpow_le_rpow hL₂0.le hL₂two hia0.le
    have hmul : (2 * L) ^ (1 / a) = 2 ^ (1 / a) * L ^ (1 / a) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hL0.le]
    have htwo : (2 : ℝ) ^ (1 / a) ≤ 2 := by
      calc
        2 ^ (1 / a) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hia1
        _ = 2 := Real.rpow_one (2 : ℝ)
    rw [hmul] at hmono
    exact le_trans hmono (mul_le_mul_of_nonneg_right htwo
      (Real.rpow_nonneg hL0.le _))
  have hinvEta : 1 / eta ≤ (4 / d) * ell * L ^ (1 / a) := by
    have hlower0 : 0 < d / (ell₂ * L₂ ^ (1 / a)) := by positivity
    have hinv := one_div_le_one_div_of_le hlower0 hetaLower
    have heq : 1 / (d / (ell₂ * L₂ ^ (1 / a))) =
        ell₂ * L₂ ^ (1 / a) / d := by field_simp
    rw [heq] at hinv
    calc
      1 / eta ≤ ell₂ * L₂ ^ (1 / a) / d := hinv
      _ ≤ (2 * ell) * (2 * L ^ (1 / a)) / d := by gcongr
      _ = (4 / d) * ell * L ^ (1 / a) := by ring

  -- The remainder of the proof constructs the zero-free disc and applies
  -- Borel--Carathéodory with an `O(ell)` ratio budget.
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
    have hLw0 : 0 < Lw := Real.log_pos (by linarith)
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
    have haux := zetaGrowthWidthFromLogsSharp_anti ha hLw0 hLw hellw0 hellw
    have hwform : zetaGrowthWidth a w.im =
        zetaGrowthWidthFromLogsSharp a Lw ellw := by rfl
    calc
      zetaGrowthWidth a (2 * u) =
          zetaGrowthWidthFromLogsSharp a L₂ ell₂ := hwidth₂
      _ ≤ zetaGrowthWidthFromLogsSharp a Lw ellw := haux
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

  -- Honest disc growth: the power-type term is bounded, not `O(L)`.
  have hwidthPow : (zetaGrowthWidth a (2 * u)) ^ a * L₂ ≤ 1 := by
    rw [hwidth₂, zetaGrowthWidthFromLogsSharp]
    have hell₂0 : 0 < ell₂ := by linarith
    have hpowEq :
        (ell₂ ^ (1 / a - 1) / L₂ ^ (1 / a)) ^ a * L₂ =
          ell₂ ^ (1 - a) := by
      rw [Real.div_rpow (Real.rpow_nonneg hell₂0.le _)
          (Real.rpow_nonneg hL₂0.le _),
        ← Real.rpow_mul hell₂0.le, ← Real.rpow_mul hL₂0.le]
      have ha0 : a ≠ 0 := ne_of_gt (by linarith : 0 < a)
      have hnumexp : (1 / a - 1) * a = 1 - a := by field_simp
      have hdenexp : (1 / a) * a = 1 := by field_simp
      rw [hnumexp, hdenexp, Real.rpow_one]
      field_simp
    rw [hpowEq]
    exact Real.rpow_le_one_of_one_le_of_nonpos hell₂one (by linarith)

  have hlogUpper : ∀ w ∈ Metric.ball center (2 * eta),
      Real.log ‖riemannZeta w‖ ≤ A * ell := by
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
    have hmaxEta : max (1 - w.re) 0 ≤ 2 * eta := by
      rw [max_le_iff]
      constructor <;> linarith
    have hmaxWidth : max (1 - w.re) 0 ≤
        c₀ * zetaGrowthWidth a (2 * u) :=
      le_trans hmaxEta hetaDoubleWidth
    have hpowWidth : (max (1 - w.re) 0) ^ a ≤
        (c₀ * zetaGrowthWidth a (2 * u)) ^ a :=
      Real.rpow_le_rpow (by positivity) hmaxWidth (by linarith)
    have hwabs0 : 0 < |w.im| := by linarith
    have hlogw0 : 0 ≤ Real.log |w.im| := Real.log_nonneg (by linarith)
    have hlogw : Real.log |w.im| ≤ L₂ := by
      dsimp only [L₂]
      exact Real.log_le_log hwabs0 hwupper
    have hloglogw : Real.log (Real.log |w.im|) ≤ ell₂ := by
      dsimp only [ell₂]
      exact Real.log_le_log (Real.log_pos (by linarith)) hlogw
    have hpowerTerm : B * (max (1 - w.re) 0) ^ a * Real.log |w.im| ≤
        B * c₀ ^ a := by
      calc
        B * (max (1 - w.re) 0) ^ a * Real.log |w.im| ≤
            B * (c₀ * zetaGrowthWidth a (2 * u)) ^ a * L₂ := by gcongr
        _ = B * c₀ ^ a *
            ((zetaGrowthWidth a (2 * u)) ^ a * L₂) := by
          rw [Real.mul_rpow hc₀.le hwidth₂pos.le]
          ring
        _ ≤ B * c₀ ^ a * 1 := by gcongr
        _ = B * c₀ ^ a := by ring
    have hbterm : b * Real.log (Real.log |w.im|) ≤ 2 * b * ell := by
      calc
        b * Real.log (Real.log |w.im|) ≤ b * ell₂ :=
          mul_le_mul_of_nonneg_left hloglogw hb
        _ ≤ b * (2 * ell) := mul_le_mul_of_nonneg_left hell₂Two hb
        _ = 2 * b * ell := by ring
    have hconst : B * c₀ ^ a + B₀ ≤ (B * c₀ ^ a + B₀) * ell := by
      have : 1 ≤ ell := by linarith
      have hc : 0 ≤ B * c₀ ^ a + B₀ := by positivity
      nlinarith
    have hgrowth := h.bound w.re w.im ht₀w hwreLower hwreUpper
    have hwform : ((w.re : ℝ) : ℂ) + I * w.im = w := by
      apply Complex.ext <;> simp
    rw [hwform] at hgrowth
    dsimp only [A]
    linarith

  have hcenterGrowthTwice : Real.log
      ‖riemannZeta ((((1 + eta / 2 : ℝ) : ℂ) + I * (2 * z.im)))‖ ≤ E * ell := by
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
    have hbterm : b * ell₂ ≤ 2 * b * ell := by
      calc
        b * ell₂ ≤ b * (2 * ell) := mul_le_mul_of_nonneg_left hell₂Two hb
        _ = 2 * b * ell := by ring
    have hB₀term : B₀ ≤ B₀ * ell := by
      have : 1 ≤ ell := by linarith
      nlinarith
    dsimp only [E]
    have hscalar : b * ell₂ + B₀ ≤ (2 * b + B₀) * ell := by linarith
    have hresult := le_trans hgrowth hscalar
    convert hresult using 1 <;> push_cast <;> ring

  have hInvBase : 1 / (eta / 2) ≤
      (8 / d) * ell * L ^ (1 / a) := by
    calc
      1 / (eta / 2) = 2 * (1 / eta) := by field_simp
      _ ≤ 2 * ((4 / d) * ell * L ^ (1 / a)) :=
        mul_le_mul_of_nonneg_left hinvEta (by norm_num)
      _ = (8 / d) * ell * L ^ (1 / a) := by ring

  have hlogBase : Real.log (1 + 1 / (eta / 2)) ≤ (2 + 8 / d) * ell := by
    have hbase0 : 0 < 1 + 1 / (eta / 2) := by positivity
    have hfactor0 : 0 < 1 + 8 / d := by positivity
    have hLpowLeL : L ^ (1 / a) ≤ L := by
      calc
        L ^ (1 / a) ≤ L ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hia1
        _ = L := Real.rpow_one L
    have hprod : ell * L ^ (1 / a) ≤ L ^ 2 := by
      calc
        ell * L ^ (1 / a) ≤ L * L ^ (1 / a) :=
          mul_le_mul_of_nonneg_right hellL (Real.rpow_nonneg hL0.le _)
        _ ≤ L * L := mul_le_mul_of_nonneg_left hLpowLeL hL0.le
        _ = L ^ 2 := by ring
    have hbaseBound : 1 + 1 / (eta / 2) ≤ (1 + 8 / d) * L ^ 2 := by
      have hLone : 1 ≤ L := by linarith
      calc
        1 + 1 / (eta / 2) ≤ 1 + (8 / d) * (ell * L ^ (1 / a)) := by
          linarith [hInvBase]
        _ ≤ 1 + (8 / d) * L ^ 2 := by gcongr
        _ ≤ (1 + 8 / d) * L ^ 2 := by nlinarith [sq_nonneg L]
    have hlog := Real.log_le_log hbase0 hbaseBound
    rw [Real.log_mul hfactor0.ne' (pow_ne_zero 2 hL0.ne'), Real.log_pow] at hlog
    push_cast at hlog
    have hconst : Real.log (1 + 8 / d) ≤ (8 / d) * ell := by
      have hh := Real.log_le_sub_one_of_pos hfactor0
      have hellOne : 1 ≤ ell := by linarith
      have hddiv : 0 ≤ 8 / d := by positivity
      nlinarith
    linarith

  have hcenterLower : -Real.log ‖riemannZeta center‖ ≤
      ((3 * (2 + 8 / d) + E) / 4) * ell := by
    have hlower := neg_log_norm_zeta_le_of_341 (1 + eta / 2) z.im (E * ell)
      (by linarith) hcenterGrowthTwice
    have hlower' : -Real.log ‖riemannZeta center‖ ≤
        (3 * Real.log (1 + 1 / (eta / 2)) + E * ell) / 4 := by
      simpa only [center, show (1 + eta / 2 : ℝ) - 1 = eta / 2 by ring] using hlower
    calc
      -Real.log ‖riemannZeta center‖ ≤
          (3 * Real.log (1 + 1 / (eta / 2)) + E * ell) / 4 := hlower'
      _ ≤ (3 * ((2 + 8 / d) * ell) + E * ell) / 4 := by gcongr
      _ = ((3 * (2 + 8 / d) + E) / 4) * ell := by ring

  have hcenterNe : riemannZeta center ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp [center]; linarith)
  have hcenterNorm0 : 0 < ‖riemannZeta center‖ := norm_pos_iff.mpr hcenterNe
  have hratio : ∀ w ∈ Metric.ball center (2 * eta),
      ‖riemannZeta w‖ ≤ Real.exp (D * ell) * ‖riemannZeta center‖ := by
    intro w hw
    by_cases hwzero : riemannZeta w = 0
    · rw [hwzero, norm_zero]
      positivity
    · have hwnorm0 : 0 < ‖riemannZeta w‖ := norm_pos_iff.mpr hwzero
      have hlogratio : Real.log ‖riemannZeta w‖ ≤
          D * ell + Real.log ‖riemannZeta center‖ := by
        have hupper := hlogUpper w hw
        dsimp only [D]
        linarith
      have hexp := Real.exp_le_exp.mpr hlogratio
      rw [Real.exp_add, Real.exp_log hwnorm0, Real.exp_log hcenterNorm0] at hexp
      exact hexp

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
  have hellSq : ell ^ 2 ≤ 400 * L ^ (1 / 10 : ℝ) := by
    have hlogPow := Real.log_le_rpow_div (x := L) hL0.le
      (show (0 : ℝ) < 1 / 20 by norm_num)
    have hellBound : ell ≤ 20 * L ^ (1 / 20 : ℝ) := by
      calc
        ell = Real.log L := rfl
        _ ≤ L ^ (1 / 20 : ℝ) / (1 / 20) := hlogPow
        _ = 20 * L ^ (1 / 20 : ℝ) := by ring
    have hsquare := (sq_le_sq₀ hell0.le (by positivity)).mpr hellBound
    have hp : (L ^ (1 / 20 : ℝ)) ^ (2 : ℕ) =
        L ^ (1 / 10 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      norm_num
    calc
      ell ^ 2 ≤ (20 * L ^ (1 / 20 : ℝ)) ^ 2 := hsquare
      _ = 400 * L ^ (1 / 10 : ℝ) := by
        rw [mul_pow, hp]
        norm_num
  have hpowCombine : L ^ (1 / a) * L ^ (1 / 10 : ℝ) =
      L ^ zetaGrowthLogDerivExponentSharp a := by
    rw [← Real.rpow_add hL0]
    rfl
  have hcoefNear : 400 * (96 * (D + 1) / d + 1) ≤ C := by
    dsimp only [C]
    rw [le_div_iff₀ (sq_pos_of_pos hd0)]
    have hdle : d ≤ 1 := le_trans hdeighth (by norm_num)
    have hdsq : d ^ 2 ≤ 1 := by nlinarith [sq_nonneg d]
    have hmul : (400 * (96 * (D + 1) / d + 1)) * d ^ 2 =
        400 * (96 * (D + 1) * d + d ^ 2) := by field_simp
    rw [hmul]
    nlinarith [mul_le_mul_of_nonneg_left hdle (by positivity : 0 ≤ D + 1)]
  have hcoefRight : 20 * (8 / d + P) ≤ C := by
    dsimp only [C]
    rw [le_div_iff₀ (sq_pos_of_pos hd0)]
    have hdle : d ≤ 1 := le_trans hdeighth (by norm_num)
    have hmul : (20 * (8 / d + P)) * d ^ 2 =
        20 * (8 * d + P * d ^ 2) := by field_simp
    rw [hmul]
    have hPd : P * d ^ 2 ≤ P := by
      have hdsq : d ^ 2 ≤ 1 := by nlinarith [sq_nonneg d]
      simpa using mul_le_mul_of_nonneg_left hdsq hP0
    nlinarith

  by_cases hzNear : z.re ≤ 1 + eta
  · have hzreEta : 1 - eta / 2 ≤ z.re := by simpa only [eta] using hzre
    have hzclosed : z ∈ Metric.closedBall center eta := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hdiff : z - center = ((z.re - (1 + eta / 2) : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [center]
      rw [hdiff, norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hzclosed' : z ∈ Metric.closedBall center (2 * eta / 2) := by simpa using hzclosed
    have hbc := norm_logDeriv_le_on_half_closedBall isOpen_compl_singleton
      hanalytic (by positivity : 0 < 2 * eta) hballPole hne hratio hzclosed'
    have hbcEta : ‖deriv riemannZeta z / riemannZeta z‖ ≤
        24 * (D * ell + 1) / eta := by
      calc
        ‖deriv riemannZeta z / riemannZeta z‖ ≤
            24 * (D * ell + 1) / (2 * eta) := hbc
        _ ≤ 24 * (D * ell + 1) / eta := by
          have hnum0 : 0 ≤ 24 * (D * ell + 1) := by positivity
          exact div_le_div_of_nonneg_left hnum0 heta0 (by linarith)
    have hbcEtaNeg : ‖-deriv riemannZeta z / riemannZeta z‖ ≤
        24 * (D * ell + 1) / eta := by
      simpa only [neg_div, norm_neg] using hbcEta
    have hDell : D * ell + 1 ≤ (D + 1) * ell := by nlinarith
    have hbcSharp : 24 * (D * ell + 1) / eta ≤
        (96 * (D + 1) / d) * L ^ (1 / a) * ell ^ 2 := by
      calc
        24 * (D * ell + 1) / eta =
            24 * (D * ell + 1) * (1 / eta) := by ring
        _ ≤ 24 * ((D + 1) * ell) *
            ((4 / d) * ell * L ^ (1 / a)) := by gcongr
        _ = (96 * (D + 1) / d) * L ^ (1 / a) * ell ^ 2 := by ring
    have hregular : ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤
        24 * (D * ell + 1) / eta + 1 := by
      calc
        _ ≤ ‖-deriv riemannZeta z / riemannZeta z‖ + ‖(1 : ℂ) / (z - 1)‖ :=
          norm_sub_le _ _
        _ ≤ 24 * (D * ell + 1) / eta + 1 := add_le_add hbcEtaNeg hrecipOne
    calc
      _ ≤ 24 * (D * ell + 1) / eta + 1 := hregular
      _ ≤ (96 * (D + 1) / d) * L ^ (1 / a) * ell ^ 2 + 1 := by linarith
      _ ≤ (96 * (D + 1) / d + 1) * L ^ (1 / a) * ell ^ 2 := by
        have hbase : 1 ≤ L ^ (1 / a) * ell ^ 2 := by
          have hLp : 1 ≤ L ^ (1 / a) := by
            simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
              (by linarith : (1 : ℝ) ≤ L) hia0.le
          have hellsq : 1 ≤ ell ^ 2 := by nlinarith
          exact one_le_mul_of_one_le_of_one_le hLp hellsq
        calc
          (96 * (D + 1) / d) * L ^ (1 / a) * ell ^ 2 + 1 ≤
              (96 * (D + 1) / d) * L ^ (1 / a) * ell ^ 2 +
                L ^ (1 / a) * ell ^ 2 := by
            exact add_le_add (le_refl _) hbase
          _ = _ := by ring
      _ ≤ (400 * (96 * (D + 1) / d + 1)) *
          (L ^ (1 / a) * L ^ (1 / 10 : ℝ)) := by
        have hcoef0 : 0 ≤ 96 * (D + 1) / d + 1 := by positivity
        calc
          (96 * (D + 1) / d + 1) * L ^ (1 / a) * ell ^ 2 ≤
              (96 * (D + 1) / d + 1) * L ^ (1 / a) *
                (400 * L ^ (1 / 10 : ℝ)) :=
            mul_le_mul_of_nonneg_left hellSq
              (mul_nonneg hcoef0 (Real.rpow_nonneg hL0.le _))
          _ = _ := by ring
      _ ≤ C * (L ^ (1 / a) * L ^ (1 / 10 : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hcoefNear (by positivity)
      _ = C * (Real.log |z.im|) ^ zetaGrowthLogDerivExponentSharp a := by
        rw [hpowCombine]
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
        _ ≤ ‖-deriv riemannZeta z / riemannZeta z‖ + ‖(1 : ℂ) / (z - 1)‖ :=
          norm_sub_le _ _
        _ ≤ (1 / (z.re - 1) + P) + 1 / (z.re - 1) := add_le_add hp hrecipReal
        _ ≤ (1 / eta + P) + 1 / eta := by gcongr
        _ = 2 * (1 / eta) + P := by ring
    have hboundSharp : 2 * (1 / eta) + P ≤
        (8 / d + P) * L ^ (1 / a) * ell := by
      have hbase : 1 ≤ L ^ (1 / a) * ell := by
        have hLp : 1 ≤ L ^ (1 / a) := by
          simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
            (by linarith : (1 : ℝ) ≤ L) hia0.le
        exact one_le_mul_of_one_le_of_one_le hLp (by linarith)
      calc
        2 * (1 / eta) + P ≤
            (8 / d) * ell * L ^ (1 / a) + P := by
          have hh := mul_le_mul_of_nonneg_left hinvEta (by norm_num : (0 : ℝ) ≤ 2)
          convert add_le_add_right hh P using 1 <;> ring
        _ ≤ (8 / d + P) * L ^ (1 / a) * ell := by
          calc
            (8 / d) * ell * L ^ (1 / a) + P =
                (8 / d) * (L ^ (1 / a) * ell) + P := by ring
            _ ≤ (8 / d) * (L ^ (1 / a) * ell) +
                P * (L ^ (1 / a) * ell) := by
              have hPbase : P ≤ P * (L ^ (1 / a) * ell) := by
                simpa only [mul_one] using mul_le_mul_of_nonneg_left hbase hP0
              exact add_le_add (le_refl _) hPbase
            _ = (8 / d + P) * L ^ (1 / a) * ell := by ring
    have hellBound : ell ≤ 20 * L ^ (1 / 20 : ℝ) := by
      have hh := Real.log_le_rpow_div (x := L) hL0.le
        (show (0 : ℝ) < 1 / 20 by norm_num)
      calc
        ell = Real.log L := rfl
        _ ≤ L ^ (1 / 20 : ℝ) / (1 / 20) := hh
        _ = 20 * L ^ (1 / 20 : ℝ) := by ring
    have hsmallPower : L ^ (1 / 20 : ℝ) ≤ L ^ (1 / 10 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    calc
      _ ≤ 2 * (1 / eta) + P := hregular
      _ ≤ (8 / d + P) * L ^ (1 / a) * ell := hboundSharp
      _ ≤ 20 * (8 / d + P) *
          (L ^ (1 / a) * L ^ (1 / 20 : ℝ)) := by
        have hc : 0 ≤ 8 / d + P := by positivity
        have hfac0 : 0 ≤ (8 / d + P) * L ^ (1 / a) :=
          mul_nonneg hc (Real.rpow_nonneg hL0.le (1 / a))
        have hh : ((8 / d + P) * L ^ (1 / a)) * ell ≤
            ((8 / d + P) * L ^ (1 / a)) *
              (20 * L ^ (1 / 20 : ℝ)) :=
          mul_le_mul_of_nonneg_left hellBound hfac0
        convert hh using 1 <;> ring
      _ ≤ (20 * (8 / d + P)) *
          (L ^ (1 / a) * L ^ (1 / 10 : ℝ)) := by
        have hpow0 : 0 ≤ L ^ (1 / a) := Real.rpow_nonneg hL0.le _
        have hpow20 : 0 ≤ L ^ (1 / 20 : ℝ) := Real.rpow_nonneg hL0.le _
        have hfactor := mul_le_mul_of_nonneg_left hsmallPower hpow0
        exact mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ ≤ C * (L ^ (1 / a) * L ^ (1 / 10 : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hcoefRight (by positivity)
      _ = C * (Real.log |z.im|) ^ zetaGrowthLogDerivExponentSharp a := by
        rw [hpowCombine]

set_option maxHeartbeats 10000000 in
/-- **V-C4-3′ half-slack strengthening.**  The regular part has exponent `1/a + 1/20` once the
growth bound is used at the actual width, retaining half of the spare power. -/
theorem zeta_regular_logDeriv_bound_of_growth_half
    {t₀ a B b B₀ : ℝ} (h : ZetaGrowthBound t₀ a B b B₀)
    (ha : 1 < a) (hB : 0 < B) (hb : 0 ≤ b) (hB₀ : 0 ≤ B₀) :
    ∃ c C t₁ : ℝ, 0 < c ∧ 1 ≤ C ∧ t₀ ≤ t₁ ∧
      ∀ z : ℂ, t₁ ≤ |z.im| →
        1 - zetaGrowthRegionEta a c z.im / 2 ≤ z.re → z.re ≤ 2 →
        z ≠ 1 →
        ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤
          C * (Real.log |z.im|) ^ (1 / a + 1 / 20) := by
  obtain ⟨c₀, tz, hc₀, ht₀tz, hzero⟩ := zeta_zero_free_of_growth h ha hB hb hB₀
  obtain ⟨P, hP0, hpole⟩ := exists_norm_zeta_logDeriv_pole_bound
  let d : ℝ := min (1 / 8) (c₀ / 2)
  have hd0 : 0 < d := lt_min (by norm_num) (by positivity)
  have hdeighth : d ≤ 1 / 8 := min_le_left _ _
  have hdcHalf : d ≤ c₀ / 2 := min_le_right _ _
  let A : ℝ := B * c₀ ^ a + 2 * b + B₀
  let E : ℝ := 2 * b + B₀
  let D : ℝ := A + (3 * (2 + 8 / d) + E) / 4
  let C : ℝ := 100000 * (D + P + 1) / d ^ 2
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hC1 : 1 ≤ C := by
    dsimp only [C]
    have hdle : d ≤ 1 := le_trans hdeighth (by norm_num)
    rw [le_div_iff₀ (sq_pos_of_pos hd0)]
    nlinarith [sq_nonneg d]
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
  have huFour : 4 ≤ u := by
    have hexpH3 : 3 ≤ Real.exp H := by
      have := Real.add_one_le_exp H
      linarith
    have := Real.add_one_le_exp (Real.exp H)
    exact le_trans (by linarith) huExp
  have hellL : ell ≤ L := by
    have := Real.log_le_sub_one_of_pos hL0
    linarith
  have hutz : tz + 1 ≤ u := by
    have : 2 * tz + 2 ≤ u := le_trans (le_max_left _ _) hzheight
    linarith
  have hut₀ : t₀ + 1 ≤ u := by
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hzheight)
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
  have hL₂one : 1 ≤ L₂ := by linarith
  have hwidth₂ : zetaGrowthWidth a (2 * u) =
      zetaGrowthWidthFromLogsSharp a L₂ ell₂ := by
    rw [zetaGrowthWidth, zetaGrowthWidthFromLogsSharp]
    have habs : |2 * u| = 2 * u := by rw [abs_of_pos (by positivity)]
    rw [habs]
  let eta : ℝ := zetaGrowthRegionEta a c₀ z.im
  have hetaDef : eta = min (1 / 8) ((c₀ / 2) * zetaGrowthWidth a (2 * u)) := by
    dsimp only [eta, zetaGrowthRegionEta, u]
  have hwidth₂pos : 0 < zetaGrowthWidth a (2 * u) := by
    rw [hwidth₂, zetaGrowthWidthFromLogsSharp]
    positivity
  have hwidth₂le : zetaGrowthWidth a (2 * u) ≤ 1 := by
    rw [hwidth₂]
    exact zetaGrowthWidthFromLogsSharp_le_one ha hL₂one hell₂one
  have heta0 : 0 < eta := by
    rw [hetaDef]
    exact lt_min (by norm_num) (mul_pos (by positivity) hwidth₂pos)
  have hetaEighth : eta ≤ 1 / 8 := by rw [hetaDef]; exact min_le_left _ _
  have hetaDoubleWidth : 2 * eta ≤ c₀ * zetaGrowthWidth a (2 * u) := by
    rw [hetaDef]
    have hm := min_le_right (1 / 8 : ℝ) ((c₀ / 2) * zetaGrowthWidth a (2 * u))
    nlinarith
  have hetaWidthLower : d * zetaGrowthWidth a (2 * u) ≤ eta := by
    rw [hetaDef, le_min_iff]
    constructor
    · calc
        d * zetaGrowthWidth a (2 * u) ≤ d * 1 :=
          mul_le_mul_of_nonneg_left hwidth₂le hd0.le
        _ ≤ 1 / 8 := by simpa using hdeighth
    · exact mul_le_mul_of_nonneg_right hdcHalf hwidth₂pos.le
  have hwidthLower : 1 / (ell₂ * L₂ ^ (1 / a)) ≤
      zetaGrowthWidth a (2 * u) := by
    rw [hwidth₂]
    exact zetaGrowthWidthFromLogsSharp_lower ha hL₂0 hell₂one
  have hetaLower : d / (ell₂ * L₂ ^ (1 / a)) ≤ eta := by
    calc
      d / (ell₂ * L₂ ^ (1 / a)) =
          d * (1 / (ell₂ * L₂ ^ (1 / a))) := by ring
      _ ≤ d * zetaGrowthWidth a (2 * u) :=
        mul_le_mul_of_nonneg_left hwidthLower hd0.le
      _ ≤ eta := hetaWidthLower
  have hia0 : 0 < 1 / a := one_div_pos.mpr (by linarith)
  have hia1 : 1 / a ≤ 1 := by
    rw [div_le_one (by linarith : 0 < a)]
    linarith
  have hL₂pow : L₂ ^ (1 / a) ≤ 2 * L ^ (1 / a) := by
    have hmono := Real.rpow_le_rpow hL₂0.le hL₂two hia0.le
    have hmul : (2 * L) ^ (1 / a) = 2 ^ (1 / a) * L ^ (1 / a) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hL0.le]
    have htwo : (2 : ℝ) ^ (1 / a) ≤ 2 := by
      calc
        2 ^ (1 / a) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hia1
        _ = 2 := Real.rpow_one (2 : ℝ)
    rw [hmul] at hmono
    exact le_trans hmono (mul_le_mul_of_nonneg_right htwo
      (Real.rpow_nonneg hL0.le _))
  have hinvEta : 1 / eta ≤ (4 / d) * ell * L ^ (1 / a) := by
    have hlower0 : 0 < d / (ell₂ * L₂ ^ (1 / a)) := by positivity
    have hinv := one_div_le_one_div_of_le hlower0 hetaLower
    have heq : 1 / (d / (ell₂ * L₂ ^ (1 / a))) =
        ell₂ * L₂ ^ (1 / a) / d := by field_simp
    rw [heq] at hinv
    calc
      1 / eta ≤ ell₂ * L₂ ^ (1 / a) / d := hinv
      _ ≤ (2 * ell) * (2 * L ^ (1 / a)) / d := by gcongr
      _ = (4 / d) * ell * L ^ (1 / a) := by ring

  -- The remainder of the proof constructs the zero-free disc and applies
  -- Borel--Carathéodory with an `O(ell)` ratio budget.
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
    have hLw0 : 0 < Lw := Real.log_pos (by linarith)
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
    have haux := zetaGrowthWidthFromLogsSharp_anti ha hLw0 hLw hellw0 hellw
    have hwform : zetaGrowthWidth a w.im =
        zetaGrowthWidthFromLogsSharp a Lw ellw := by rfl
    calc
      zetaGrowthWidth a (2 * u) =
          zetaGrowthWidthFromLogsSharp a L₂ ell₂ := hwidth₂
      _ ≤ zetaGrowthWidthFromLogsSharp a Lw ellw := haux
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

  -- Honest disc growth: the power-type term is bounded, not `O(L)`.
  have hwidthPow : (zetaGrowthWidth a (2 * u)) ^ a * L₂ ≤ 1 := by
    rw [hwidth₂, zetaGrowthWidthFromLogsSharp]
    have hell₂0 : 0 < ell₂ := by linarith
    have hpowEq :
        (ell₂ ^ (1 / a - 1) / L₂ ^ (1 / a)) ^ a * L₂ =
          ell₂ ^ (1 - a) := by
      rw [Real.div_rpow (Real.rpow_nonneg hell₂0.le _)
          (Real.rpow_nonneg hL₂0.le _),
        ← Real.rpow_mul hell₂0.le, ← Real.rpow_mul hL₂0.le]
      have ha0 : a ≠ 0 := ne_of_gt (by linarith : 0 < a)
      have hnumexp : (1 / a - 1) * a = 1 - a := by field_simp
      have hdenexp : (1 / a) * a = 1 := by field_simp
      rw [hnumexp, hdenexp, Real.rpow_one]
      field_simp
    rw [hpowEq]
    exact Real.rpow_le_one_of_one_le_of_nonpos hell₂one (by linarith)

  have hlogUpper : ∀ w ∈ Metric.ball center (2 * eta),
      Real.log ‖riemannZeta w‖ ≤ A * ell := by
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
    have hmaxEta : max (1 - w.re) 0 ≤ 2 * eta := by
      rw [max_le_iff]
      constructor <;> linarith
    have hmaxWidth : max (1 - w.re) 0 ≤
        c₀ * zetaGrowthWidth a (2 * u) :=
      le_trans hmaxEta hetaDoubleWidth
    have hpowWidth : (max (1 - w.re) 0) ^ a ≤
        (c₀ * zetaGrowthWidth a (2 * u)) ^ a :=
      Real.rpow_le_rpow (by positivity) hmaxWidth (by linarith)
    have hwabs0 : 0 < |w.im| := by linarith
    have hlogw0 : 0 ≤ Real.log |w.im| := Real.log_nonneg (by linarith)
    have hlogw : Real.log |w.im| ≤ L₂ := by
      dsimp only [L₂]
      exact Real.log_le_log hwabs0 hwupper
    have hloglogw : Real.log (Real.log |w.im|) ≤ ell₂ := by
      dsimp only [ell₂]
      exact Real.log_le_log (Real.log_pos (by linarith)) hlogw
    have hpowerTerm : B * (max (1 - w.re) 0) ^ a * Real.log |w.im| ≤
        B * c₀ ^ a := by
      calc
        B * (max (1 - w.re) 0) ^ a * Real.log |w.im| ≤
            B * (c₀ * zetaGrowthWidth a (2 * u)) ^ a * L₂ := by gcongr
        _ = B * c₀ ^ a *
            ((zetaGrowthWidth a (2 * u)) ^ a * L₂) := by
          rw [Real.mul_rpow hc₀.le hwidth₂pos.le]
          ring
        _ ≤ B * c₀ ^ a * 1 := by gcongr
        _ = B * c₀ ^ a := by ring
    have hbterm : b * Real.log (Real.log |w.im|) ≤ 2 * b * ell := by
      calc
        b * Real.log (Real.log |w.im|) ≤ b * ell₂ :=
          mul_le_mul_of_nonneg_left hloglogw hb
        _ ≤ b * (2 * ell) := mul_le_mul_of_nonneg_left hell₂Two hb
        _ = 2 * b * ell := by ring
    have hconst : B * c₀ ^ a + B₀ ≤ (B * c₀ ^ a + B₀) * ell := by
      have : 1 ≤ ell := by linarith
      have hc : 0 ≤ B * c₀ ^ a + B₀ := by positivity
      nlinarith
    have hgrowth := h.bound w.re w.im ht₀w hwreLower hwreUpper
    have hwform : ((w.re : ℝ) : ℂ) + I * w.im = w := by
      apply Complex.ext <;> simp
    rw [hwform] at hgrowth
    dsimp only [A]
    linarith

  have hcenterGrowthTwice : Real.log
      ‖riemannZeta ((((1 + eta / 2 : ℝ) : ℂ) + I * (2 * z.im)))‖ ≤ E * ell := by
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
    have hbterm : b * ell₂ ≤ 2 * b * ell := by
      calc
        b * ell₂ ≤ b * (2 * ell) := mul_le_mul_of_nonneg_left hell₂Two hb
        _ = 2 * b * ell := by ring
    have hB₀term : B₀ ≤ B₀ * ell := by
      have : 1 ≤ ell := by linarith
      nlinarith
    dsimp only [E]
    have hscalar : b * ell₂ + B₀ ≤ (2 * b + B₀) * ell := by linarith
    have hresult := le_trans hgrowth hscalar
    convert hresult using 1 <;> push_cast <;> ring

  have hInvBase : 1 / (eta / 2) ≤
      (8 / d) * ell * L ^ (1 / a) := by
    calc
      1 / (eta / 2) = 2 * (1 / eta) := by field_simp
      _ ≤ 2 * ((4 / d) * ell * L ^ (1 / a)) :=
        mul_le_mul_of_nonneg_left hinvEta (by norm_num)
      _ = (8 / d) * ell * L ^ (1 / a) := by ring

  have hlogBase : Real.log (1 + 1 / (eta / 2)) ≤ (2 + 8 / d) * ell := by
    have hbase0 : 0 < 1 + 1 / (eta / 2) := by positivity
    have hfactor0 : 0 < 1 + 8 / d := by positivity
    have hLpowLeL : L ^ (1 / a) ≤ L := by
      calc
        L ^ (1 / a) ≤ L ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hia1
        _ = L := Real.rpow_one L
    have hprod : ell * L ^ (1 / a) ≤ L ^ 2 := by
      calc
        ell * L ^ (1 / a) ≤ L * L ^ (1 / a) :=
          mul_le_mul_of_nonneg_right hellL (Real.rpow_nonneg hL0.le _)
        _ ≤ L * L := mul_le_mul_of_nonneg_left hLpowLeL hL0.le
        _ = L ^ 2 := by ring
    have hbaseBound : 1 + 1 / (eta / 2) ≤ (1 + 8 / d) * L ^ 2 := by
      have hLone : 1 ≤ L := by linarith
      calc
        1 + 1 / (eta / 2) ≤ 1 + (8 / d) * (ell * L ^ (1 / a)) := by
          linarith [hInvBase]
        _ ≤ 1 + (8 / d) * L ^ 2 := by gcongr
        _ ≤ (1 + 8 / d) * L ^ 2 := by nlinarith [sq_nonneg L]
    have hlog := Real.log_le_log hbase0 hbaseBound
    rw [Real.log_mul hfactor0.ne' (pow_ne_zero 2 hL0.ne'), Real.log_pow] at hlog
    push_cast at hlog
    have hconst : Real.log (1 + 8 / d) ≤ (8 / d) * ell := by
      have hh := Real.log_le_sub_one_of_pos hfactor0
      have hellOne : 1 ≤ ell := by linarith
      have hddiv : 0 ≤ 8 / d := by positivity
      nlinarith
    linarith

  have hcenterLower : -Real.log ‖riemannZeta center‖ ≤
      ((3 * (2 + 8 / d) + E) / 4) * ell := by
    have hlower := neg_log_norm_zeta_le_of_341 (1 + eta / 2) z.im (E * ell)
      (by linarith) hcenterGrowthTwice
    have hlower' : -Real.log ‖riemannZeta center‖ ≤
        (3 * Real.log (1 + 1 / (eta / 2)) + E * ell) / 4 := by
      simpa only [center, show (1 + eta / 2 : ℝ) - 1 = eta / 2 by ring] using hlower
    calc
      -Real.log ‖riemannZeta center‖ ≤
          (3 * Real.log (1 + 1 / (eta / 2)) + E * ell) / 4 := hlower'
      _ ≤ (3 * ((2 + 8 / d) * ell) + E * ell) / 4 := by gcongr
      _ = ((3 * (2 + 8 / d) + E) / 4) * ell := by ring

  have hcenterNe : riemannZeta center ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp [center]; linarith)
  have hcenterNorm0 : 0 < ‖riemannZeta center‖ := norm_pos_iff.mpr hcenterNe
  have hratio : ∀ w ∈ Metric.ball center (2 * eta),
      ‖riemannZeta w‖ ≤ Real.exp (D * ell) * ‖riemannZeta center‖ := by
    intro w hw
    by_cases hwzero : riemannZeta w = 0
    · rw [hwzero, norm_zero]
      positivity
    · have hwnorm0 : 0 < ‖riemannZeta w‖ := norm_pos_iff.mpr hwzero
      have hlogratio : Real.log ‖riemannZeta w‖ ≤
          D * ell + Real.log ‖riemannZeta center‖ := by
        have hupper := hlogUpper w hw
        dsimp only [D]
        linarith
      have hexp := Real.exp_le_exp.mpr hlogratio
      rw [Real.exp_add, Real.exp_log hwnorm0, Real.exp_log hcenterNorm0] at hexp
      exact hexp

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
  have hellSq : ell ^ 2 ≤ 1600 * L ^ (1 / 20 : ℝ) := by
    have hlogPow := Real.log_le_rpow_div (x := L) hL0.le
      (show (0 : ℝ) < 1 / 40 by norm_num)
    have hellBound : ell ≤ 40 * L ^ (1 / 40 : ℝ) := by
      calc
        ell = Real.log L := rfl
        _ ≤ L ^ (1 / 40 : ℝ) / (1 / 40) := hlogPow
        _ = 40 * L ^ (1 / 40 : ℝ) := by ring
    have hsquare := (sq_le_sq₀ hell0.le (by positivity)).mpr hellBound
    have hp : (L ^ (1 / 40 : ℝ)) ^ (2 : ℕ) =
        L ^ (1 / 20 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      norm_num
    calc
      ell ^ 2 ≤ (40 * L ^ (1 / 40 : ℝ)) ^ 2 := hsquare
      _ = 1600 * L ^ (1 / 20 : ℝ) := by
        rw [mul_pow, hp]
        norm_num
  have hpowCombine : L ^ (1 / a) * L ^ (1 / 20 : ℝ) =
      L ^ (1 / a + 1 / 20) := by
    rw [← Real.rpow_add hL0]
  have hcoefNear : 1600 * (96 * (D + 1) / d + 1) ≤ C := by
    dsimp only [C]
    rw [le_div_iff₀ (sq_pos_of_pos hd0)]
    have hdle : d ≤ 1 := le_trans hdeighth (by norm_num)
    have hdsq : d ^ 2 ≤ 1 := by nlinarith [sq_nonneg d]
    have hmul : (1600 * (96 * (D + 1) / d + 1)) * d ^ 2 =
        1600 * (96 * (D + 1) * d + d ^ 2) := by field_simp
    rw [hmul]
    nlinarith [mul_le_mul_of_nonneg_left hdle (by positivity : 0 ≤ D + 1)]
  have hcoefRight : 40 * (8 / d + P) ≤ C := by
    dsimp only [C]
    rw [le_div_iff₀ (sq_pos_of_pos hd0)]
    have hdle : d ≤ 1 := le_trans hdeighth (by norm_num)
    have hmul : (40 * (8 / d + P)) * d ^ 2 =
        40 * (8 * d + P * d ^ 2) := by field_simp
    rw [hmul]
    have hPd : P * d ^ 2 ≤ P := by
      have hdsq : d ^ 2 ≤ 1 := by nlinarith [sq_nonneg d]
      simpa using mul_le_mul_of_nonneg_left hdsq hP0
    nlinarith

  by_cases hzNear : z.re ≤ 1 + eta
  · have hzreEta : 1 - eta / 2 ≤ z.re := by simpa only [eta] using hzre
    have hzclosed : z ∈ Metric.closedBall center eta := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hdiff : z - center = ((z.re - (1 + eta / 2) : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [center]
      rw [hdiff, norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hzclosed' : z ∈ Metric.closedBall center (2 * eta / 2) := by simpa using hzclosed
    have hbc := norm_logDeriv_le_on_half_closedBall isOpen_compl_singleton
      hanalytic (by positivity : 0 < 2 * eta) hballPole hne hratio hzclosed'
    have hbcEta : ‖deriv riemannZeta z / riemannZeta z‖ ≤
        24 * (D * ell + 1) / eta := by
      calc
        ‖deriv riemannZeta z / riemannZeta z‖ ≤
            24 * (D * ell + 1) / (2 * eta) := hbc
        _ ≤ 24 * (D * ell + 1) / eta := by
          have hnum0 : 0 ≤ 24 * (D * ell + 1) := by positivity
          exact div_le_div_of_nonneg_left hnum0 heta0 (by linarith)
    have hbcEtaNeg : ‖-deriv riemannZeta z / riemannZeta z‖ ≤
        24 * (D * ell + 1) / eta := by
      simpa only [neg_div, norm_neg] using hbcEta
    have hDell : D * ell + 1 ≤ (D + 1) * ell := by nlinarith
    have hbcSharp : 24 * (D * ell + 1) / eta ≤
        (96 * (D + 1) / d) * L ^ (1 / a) * ell ^ 2 := by
      calc
        24 * (D * ell + 1) / eta =
            24 * (D * ell + 1) * (1 / eta) := by ring
        _ ≤ 24 * ((D + 1) * ell) *
            ((4 / d) * ell * L ^ (1 / a)) := by gcongr
        _ = (96 * (D + 1) / d) * L ^ (1 / a) * ell ^ 2 := by ring
    have hregular : ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤
        24 * (D * ell + 1) / eta + 1 := by
      calc
        _ ≤ ‖-deriv riemannZeta z / riemannZeta z‖ + ‖(1 : ℂ) / (z - 1)‖ :=
          norm_sub_le _ _
        _ ≤ 24 * (D * ell + 1) / eta + 1 := add_le_add hbcEtaNeg hrecipOne
    calc
      _ ≤ 24 * (D * ell + 1) / eta + 1 := hregular
      _ ≤ (96 * (D + 1) / d) * L ^ (1 / a) * ell ^ 2 + 1 := by linarith
      _ ≤ (96 * (D + 1) / d + 1) * L ^ (1 / a) * ell ^ 2 := by
        have hbase : 1 ≤ L ^ (1 / a) * ell ^ 2 := by
          have hLp : 1 ≤ L ^ (1 / a) := by
            simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
              (by linarith : (1 : ℝ) ≤ L) hia0.le
          have hellsq : 1 ≤ ell ^ 2 := by nlinarith
          exact one_le_mul_of_one_le_of_one_le hLp hellsq
        calc
          (96 * (D + 1) / d) * L ^ (1 / a) * ell ^ 2 + 1 ≤
              (96 * (D + 1) / d) * L ^ (1 / a) * ell ^ 2 +
                L ^ (1 / a) * ell ^ 2 := by
            exact add_le_add (le_refl _) hbase
          _ = _ := by ring
      _ ≤ (1600 * (96 * (D + 1) / d + 1)) *
          (L ^ (1 / a) * L ^ (1 / 20 : ℝ)) := by
        have hcoef0 : 0 ≤ 96 * (D + 1) / d + 1 := by positivity
        calc
          (96 * (D + 1) / d + 1) * L ^ (1 / a) * ell ^ 2 ≤
              (96 * (D + 1) / d + 1) * L ^ (1 / a) *
                (1600 * L ^ (1 / 20 : ℝ)) :=
            mul_le_mul_of_nonneg_left hellSq
              (mul_nonneg hcoef0 (Real.rpow_nonneg hL0.le _))
          _ = _ := by ring
      _ ≤ C * (L ^ (1 / a) * L ^ (1 / 20 : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hcoefNear (by positivity)
      _ = C * (Real.log |z.im|) ^ (1 / a + 1 / 20) := by
        rw [hpowCombine]
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
        _ ≤ ‖-deriv riemannZeta z / riemannZeta z‖ + ‖(1 : ℂ) / (z - 1)‖ :=
          norm_sub_le _ _
        _ ≤ (1 / (z.re - 1) + P) + 1 / (z.re - 1) := add_le_add hp hrecipReal
        _ ≤ (1 / eta + P) + 1 / eta := by gcongr
        _ = 2 * (1 / eta) + P := by ring
    have hboundSharp : 2 * (1 / eta) + P ≤
        (8 / d + P) * L ^ (1 / a) * ell := by
      have hbase : 1 ≤ L ^ (1 / a) * ell := by
        have hLp : 1 ≤ L ^ (1 / a) := by
          simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
            (by linarith : (1 : ℝ) ≤ L) hia0.le
        exact one_le_mul_of_one_le_of_one_le hLp (by linarith)
      calc
        2 * (1 / eta) + P ≤
            (8 / d) * ell * L ^ (1 / a) + P := by
          have hh := mul_le_mul_of_nonneg_left hinvEta (by norm_num : (0 : ℝ) ≤ 2)
          convert add_le_add_right hh P using 1 <;> ring
        _ ≤ (8 / d + P) * L ^ (1 / a) * ell := by
          calc
            (8 / d) * ell * L ^ (1 / a) + P =
                (8 / d) * (L ^ (1 / a) * ell) + P := by ring
            _ ≤ (8 / d) * (L ^ (1 / a) * ell) +
                P * (L ^ (1 / a) * ell) := by
              have hPbase : P ≤ P * (L ^ (1 / a) * ell) := by
                simpa only [mul_one] using mul_le_mul_of_nonneg_left hbase hP0
              exact add_le_add (le_refl _) hPbase
            _ = (8 / d + P) * L ^ (1 / a) * ell := by ring
    have hellBound : ell ≤ 40 * L ^ (1 / 40 : ℝ) := by
      have hh := Real.log_le_rpow_div (x := L) hL0.le
        (show (0 : ℝ) < 1 / 40 by norm_num)
      calc
        ell = Real.log L := rfl
        _ ≤ L ^ (1 / 40 : ℝ) / (1 / 40) := hh
        _ = 40 * L ^ (1 / 40 : ℝ) := by ring
    have hsmallPower : L ^ (1 / 40 : ℝ) ≤ L ^ (1 / 20 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    calc
      _ ≤ 2 * (1 / eta) + P := hregular
      _ ≤ (8 / d + P) * L ^ (1 / a) * ell := hboundSharp
      _ ≤ 40 * (8 / d + P) *
          (L ^ (1 / a) * L ^ (1 / 40 : ℝ)) := by
        have hc : 0 ≤ 8 / d + P := by positivity
        have hfac0 : 0 ≤ (8 / d + P) * L ^ (1 / a) :=
          mul_nonneg hc (Real.rpow_nonneg hL0.le (1 / a))
        have hh : ((8 / d + P) * L ^ (1 / a)) * ell ≤
            ((8 / d + P) * L ^ (1 / a)) *
              (40 * L ^ (1 / 40 : ℝ)) :=
          mul_le_mul_of_nonneg_left hellBound hfac0
        convert hh using 1 <;> ring
      _ ≤ (40 * (8 / d + P)) *
          (L ^ (1 / a) * L ^ (1 / 20 : ℝ)) := by
        have hpow0 : 0 ≤ L ^ (1 / a) := Real.rpow_nonneg hL0.le _
        have hpow20 : 0 ≤ L ^ (1 / 40 : ℝ) := Real.rpow_nonneg hL0.le _
        have hfactor := mul_le_mul_of_nonneg_left hsmallPower hpow0
        exact mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ ≤ C * (L ^ (1 / a) * L ^ (1 / 20 : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hcoefRight (by positivity)
      _ = C * (Real.log |z.im|) ^ (1 / a + 1 / 20) := by
        rw [hpowCombine]


end ExpSums

end MoltResearch
