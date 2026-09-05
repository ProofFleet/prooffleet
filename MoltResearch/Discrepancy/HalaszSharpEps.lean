import MoltResearch.Discrepancy.HalaszSharpWindow

/-!
# The sharp Halász budget in `ε`-form

The numerics that turn `halaszBudgetSharp` into a fixed-strength saving:

* `halaszBudgetSharp_le_linear` — for `z ≥ e³⁶`, `A ≥ 0`,
  `Ĥ⁺(A,z) ≤ z·(log z·e^{−A}·((A+1)·Q + 16(e−1)) + c₂·loglog z + c₃)` with the
  absolute constants `Q = 1.06·√((e^π)²10¹⁵)·e⁵ ≈ 1.15·10¹¹`,
  `c₂ = √((e^π)²10¹⁵) + 18 log 4 + 770 + 16 log 2 ≈ 7.3·10⁸`, `c₃ ≈ 1400`;
* `sharpPartialBudget_le`, `sharpTwistedDirichletCost_le` — on a block
  `10¹⁶ ≤ a ≤ b ≤ 3a`, the twisted Dirichlet cost is at most
  `(b/(a+1))·(13·e^{−D}((D+1)Q + 16(e−1))/δ₀ + 12(c₂·loglog(9a) + c₃)/(δ₀·log a) + 2eδ₀) + 2/(a+1)`;
* `exists_exp_decay_le`, `exists_loglog_le_log` — the two thresholds
  (`(D+1)e^{−D}·M ≤ η` for `D ≥ D₀`, `c₂·loglog(9a) + c₃ ≤ η·log a` for `a ≥ x₀`);
* `sharpTwistedDirichletCost_le_eps` — for every `ε > 0` there are a strength
  `D₀` and a scale `x₀` such that, at `δ₀ := ε/(8e)`, every block
  `x₀ ≤ a ≤ b ≤ 3a` costs at most `ε·b/(a+1)` at any strength `D ≥ D₀`,
  **uniformly in the scale** — the fixed-strength Halász saving the `𝒯₀`
  window needs (design report, "The `𝒯₀` leg").
-/

namespace MoltResearch

/-- `√((e^π)²·10¹⁵)`, the shell's absolute constant. -/
noncomputable def sharpRootC : ℝ := Real.sqrt ((Real.exp Real.pi)^2 * 10^15)

/-- The coefficient of `(A+1)·log z·e^{−A}` in the linear bound on `Ĥ⁺`. -/
noncomputable def sharpQualityConst : ℝ := 1.06 * sharpRootC * Real.exp 5

/-- The coefficient of `loglog z` in the linear bound on `Ĥ⁺`. -/
noncomputable def sharpLogLogConst : ℝ :=
  sharpRootC + 18 * Real.log 4 + 770 + 16 * Real.log 2

/-- The constant term in the linear bound on `Ĥ⁺`. -/
noncomputable def sharpFloorConst : ℝ :=
  1192 + 16 * (Real.exp 1 - 1) * (Real.exp 1)^2 * Real.log 2
    + 33 * Real.log 2 + 32 * Real.log 4

theorem sharpRootC_nonneg : 0 ≤ sharpRootC := Real.sqrt_nonneg _

theorem sharpQualityConst_nonneg : 0 ≤ sharpQualityConst := by
  unfold sharpQualityConst
  have := sharpRootC_nonneg
  positivity

theorem sharpLogLogConst_nonneg : 0 ≤ sharpLogLogConst := by
  unfold sharpLogLogConst
  have h4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have := sharpRootC_nonneg
  linarith

theorem sharpFloorConst_nonneg : 0 ≤ sharpFloorConst := by
  unfold sharpFloorConst
  have h2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have he1 : (0:ℝ) ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have : (0:ℝ) ≤ 16 * (Real.exp 1 - 1) * (Real.exp 1)^2 * Real.log 2 := by positivity
  linarith

/-- `e³⁶ ≤ 10¹⁶`. -/
theorem exp_36_le : Real.exp 36 ≤ (10:ℝ)^16 := by
  have he3 : Real.exp (3:ℝ) ≤ 20.1 := by
    have h3 : Real.exp (3:ℝ) = (Real.exp 1)^(3:ℕ) := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h3]
    have hcube : (Real.exp 1)^(3:ℕ) ≤ (2.7182818286:ℝ)^(3:ℕ) :=
      pow_le_pow_left₀ (Real.exp_pos 1).le
        (by linarith [Real.exp_one_lt_d9]) 3
    have hnum : (2.7182818286:ℝ)^(3:ℕ) ≤ 20.1 := by norm_num
    linarith
  have h36e : Real.exp (36:ℝ) = (Real.exp 3)^(12:ℕ) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hp12 : (Real.exp 3)^(12:ℕ) ≤ (20.1:ℝ)^(12:ℕ) :=
    pow_le_pow_left₀ (Real.exp_pos 3).le he3 12
  have hnum12 : (20.1:ℝ)^(12:ℕ) ≤ 10^16 := by norm_num
  rw [h36e]
  linarith

/-- `log 4 ≤ 1.3863` and `log 9 ≤ 2.78` (via `log 9 ≤ log 16 = 4·log 2`). -/
theorem log_four_le : Real.log 4 ≤ 1.3863 := by
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [this]
  linarith [Real.log_two_lt_d9]

theorem log_nine_le : Real.log 9 ≤ 2.78 := by
  have h16 : Real.log 9 ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
  have : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]
    push_cast
    ring
  linarith [Real.log_two_lt_d9]

/-- **The sharp budget, linearised** (Track R, T0-6c): for `z ≥ e³⁶` and
`A ≥ 0`,

  `Ĥ⁺(A,z) ≤ z·(log z·e^{−A}·((A+1)·Q + 16(e−1)) + c₂·loglog z + c₃)`.

Term by term: `2 + log z ≤ 1.06·log z`, `2(z+1)log 4 ≤ 2.8z`, and
`log(2·log²z) = log 2 + 2·loglog z`; nothing else is lost. -/
theorem halaszBudgetSharp_le_linear (A z : ℝ) (hA : 0 ≤ A)
    (hz : Real.exp 36 ≤ z) :
    halaszBudgetSharp A z
      ≤ z * (Real.log z * Real.exp (-A)
            * ((A + 1) * sharpQualityConst + 16 * (Real.exp 1 - 1))
          + sharpLogLogConst * Real.log (Real.log z) + sharpFloorConst) := by
  have hz0 : 0 < z := lt_of_lt_of_le (Real.exp_pos _) hz
  have hL36 : (36:ℝ) ≤ Real.log z := (Real.le_log_iff_exp_le hz0).mpr hz
  have hL0 : 0 < Real.log z := by linarith
  have hLL0 : 0 ≤ Real.log (Real.log z) := Real.log_nonneg (by linarith)
  have hz200 : (200:ℝ) ≤ z := by
    have h1 : Real.exp 36 = (Real.exp 1)^(36:ℕ) := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h2 : (2.7:ℝ)^(36:ℕ) ≤ (Real.exp 1)^(36:ℕ) :=
      pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 36
    have h3 : (200:ℝ) ≤ (2.7:ℝ)^(36:ℕ) := by norm_num
    linarith
  have hlog4 := log_four_le
  have hlog4' : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hsq0 : 0 ≤ Real.sqrt ((Real.exp Real.pi)^2 * 10^15) := Real.sqrt_nonneg _
  have hexpA : 0 < Real.exp (-A) := Real.exp_pos _
  have hlogsq : Real.log (2 * (Real.log z)^2)
      = Real.log 2 + 2 * Real.log (Real.log z) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  have h2L : 2 + Real.log z ≤ 1.06 * Real.log z := by linarith
  have hcoef0 : 0 ≤ (A + 1) * z * sharpRootC * Real.exp 5 * Real.exp (-A) := by
    have := sharpRootC_nonneg
    positivity
  have hterm5 : (A + 1) * (z * (Real.sqrt ((Real.exp Real.pi)^2 * 10^15)
        * (Real.exp 5 * (2 + Real.log z) * Real.exp (-A))))
      ≤ z * (Real.log z * Real.exp (-A) * ((A + 1) * sharpQualityConst)) := by
    have hl : (A + 1) * (z * (Real.sqrt ((Real.exp Real.pi)^2 * 10^15)
          * (Real.exp 5 * (2 + Real.log z) * Real.exp (-A))))
        = ((A + 1) * z * sharpRootC * Real.exp 5 * Real.exp (-A)) * (2 + Real.log z) := by
      unfold sharpRootC
      ring
    have hr : z * (Real.log z * Real.exp (-A) * ((A + 1) * sharpQualityConst))
        = ((A + 1) * z * sharpRootC * Real.exp 5 * Real.exp (-A)) * (1.06 * Real.log z) := by
      unfold sharpQualityConst
      ring
    rw [hl, hr]
    exact mul_le_mul_of_nonneg_left h2L hcoef0
  have hterm3 : 2 * (z + 1) * Real.log 4 ≤ 2.8 * z := by
    have := mul_le_mul_of_nonneg_left hlog4 (by linarith : (0:ℝ) ≤ 2 * (z + 1))
    linarith
  have hR : z * (Real.log z * Real.exp (-A)
            * ((A + 1) * sharpQualityConst + 16 * (Real.exp 1 - 1))
          + sharpLogLogConst * Real.log (Real.log z) + sharpFloorConst)
      = 35*z + z*(Real.log 2 + 2 * Real.log (Real.log z) + 2)
        + 2.8 * z
        + 64 * z * (12 * Real.log (Real.log z) + 18)
        + z * (Real.log z * Real.exp (-A) * ((A + 1) * sharpQualityConst))
        + Real.log (Real.log z)
            * (z * (Real.sqrt ((Real.exp Real.pi)^2 * 10^15) + 2*Real.log 4))
        + 16 * (Real.exp 1 - 1)
            * (z * (Real.exp (-A) * Real.log z + (Real.exp 1)^2 * Real.log 2))
        + (Real.log (Real.log z) + 2)
            * (z * (16 * Real.log 2 + 16 * Real.log 4))
        + 0.2 * z := by
    unfold sharpLogLogConst sharpFloorConst sharpRootC
    ring
  rw [hR]
  unfold halaszBudgetSharp
  rw [hlogsq]
  have h02 : (0:ℝ) ≤ 0.2 * z := by positivity
  linear_combination hterm3 + hterm5 + h02

/-- **The sharp prefix budget on a block `a ≤ b ≤ 3a`** (Track R, T0-6c):
`sharpPartialBudget D δ₀ a b ≤ b·(6.5·e^{−D}((D+1)Q + 16(e−1))/δ₀
  + 6(c₂·loglog(9a) + c₃)/(δ₀·log a) + e·δ₀) + 1`.  Uses `log(3b) ≤ 1.08·log a`
(from `log 9 ≤ 2.78 ≤ 0.08·log a`) and `loglog(3b) ≤ loglog(9a)`. -/
theorem sharpPartialBudget_le (D δ₀ : ℝ) (a b : ℕ) (hD : 0 ≤ D) (hδ₀ : 0 < δ₀)
    (ha : 10^16 ≤ a) (hab : a ≤ b) (hb3 : b ≤ 3 * a) :
    sharpPartialBudget D δ₀ a b
      ≤ (b:ℝ) * (6.5 * (Real.exp (-D)
              * ((D + 1) * sharpQualityConst + 16 * (Real.exp 1 - 1))) / δ₀
          + 6 * (sharpLogLogConst * Real.log (Real.log (9 * (a:ℝ))) + sharpFloorConst)
              / (δ₀ * Real.log (a:ℝ))
          + Real.exp 1 * δ₀) + 1 := by
  unfold sharpPartialBudget
  have haR : (10:ℝ)^16 ≤ (a:ℝ) := by exact_mod_cast ha
  have ha0 : (0:ℝ) < (a:ℝ) := by linarith
  have habR : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast hab
  have hb3R : (b:ℝ) ≤ 3 * (a:ℝ) := by exact_mod_cast hb3
  have hb0 : (0:ℝ) < (b:ℝ) := by linarith
  have he36a : Real.exp 36 ≤ (a:ℝ) := le_trans exp_36_le haR
  have hloga : (36:ℝ) ≤ Real.log (a:ℝ) := (Real.le_log_iff_exp_le ha0).mpr he36a
  have hloga0 : 0 < Real.log (a:ℝ) := by linarith
  have h3b : Real.exp 36 ≤ 3 * (b:ℝ) := by linarith
  have h3b0 : (0:ℝ) < 3 * (b:ℝ) := by linarith
  have hbud := halaszBudgetSharp_le_linear D (3 * (b:ℝ)) hD h3b
  have hlog3b : Real.log (3 * (b:ℝ)) ≤ 1.08 * Real.log (a:ℝ) := by
    have h1 : Real.log (3 * (b:ℝ)) ≤ Real.log (9 * (a:ℝ)) :=
      Real.log_le_log h3b0 (by linarith)
    have h2 : Real.log (9 * (a:ℝ)) = Real.log 9 + Real.log (a:ℝ) :=
      Real.log_mul (by norm_num) ha0.ne'
    linarith [log_nine_le]
  have hlog3b0 : 0 < Real.log (3 * (b:ℝ)) := by
    have : Real.exp 36 ≤ 3 * (b:ℝ) := h3b
    have h36 : (36:ℝ) ≤ Real.log (3 * (b:ℝ)) := (Real.le_log_iff_exp_le h3b0).mpr this
    linarith
  have hLL3b : Real.log (Real.log (3 * (b:ℝ))) ≤ Real.log (Real.log (9 * (a:ℝ))) :=
    Real.log_le_log hlog3b0 (Real.log_le_log h3b0 (by linarith))
  have hK0 : 0 ≤ Real.exp (-D) * ((D + 1) * sharpQualityConst + 16 * (Real.exp 1 - 1)) := by
    have := sharpQualityConst_nonneg
    have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
    positivity
  have hc2 := sharpLogLogConst_nonneg
  -- the numerator bound: `2Ĥ⁺(D,3b) ≤ b·(6.5·K·log a + 6·(c₂ loglog(9a) + c₃))`
  have hnum : 2 * halaszBudgetSharp D (3 * (b:ℝ))
      ≤ (b:ℝ) * (6.5 * (Real.exp (-D)
            * ((D + 1) * sharpQualityConst + 16 * (Real.exp 1 - 1))) * Real.log (a:ℝ)
          + 6 * (sharpLogLogConst * Real.log (Real.log (9 * (a:ℝ))) + sharpFloorConst)) := by
    have h1 : Real.log (3 * (b:ℝ)) * Real.exp (-D)
          * ((D + 1) * sharpQualityConst + 16 * (Real.exp 1 - 1))
        ≤ 1.08 * Real.log (a:ℝ) * (Real.exp (-D)
          * ((D + 1) * sharpQualityConst + 16 * (Real.exp 1 - 1))) := by
      have := mul_le_mul_of_nonneg_right hlog3b hK0
      linarith [this]
    have h2 : sharpLogLogConst * Real.log (Real.log (3 * (b:ℝ)))
        ≤ sharpLogLogConst * Real.log (Real.log (9 * (a:ℝ))) :=
      mul_le_mul_of_nonneg_left hLL3b hc2
    have hinner : Real.log (3 * (b:ℝ)) * Real.exp (-D)
            * ((D + 1) * sharpQualityConst + 16 * (Real.exp 1 - 1))
          + sharpLogLogConst * Real.log (Real.log (3 * (b:ℝ))) + sharpFloorConst
        ≤ 1.08 * Real.log (a:ℝ) * (Real.exp (-D)
            * ((D + 1) * sharpQualityConst + 16 * (Real.exp 1 - 1)))
          + sharpLogLogConst * Real.log (Real.log (9 * (a:ℝ))) + sharpFloorConst := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hinner h3b0.le
    have hXL0 : (0:ℝ) ≤ 0.02 * ((b:ℝ) * (Real.log (a:ℝ) * (Real.exp (-D)
        * ((D + 1) * sharpQualityConst + 16 * (Real.exp 1 - 1))))) := by
      have := mul_nonneg hb0.le (mul_nonneg hloga0.le hK0)
      linarith
    linear_combination 2 * hbud + 2 * hmul + hXL0
  have hden : 0 < δ₀ * Real.log (a:ℝ) := by positivity
  have hdiv : 2 * halaszBudgetSharp D (3 * (b:ℝ)) / (δ₀ * Real.log (a:ℝ))
      ≤ (b:ℝ) * (6.5 * (Real.exp (-D)
            * ((D + 1) * sharpQualityConst + 16 * (Real.exp 1 - 1))) * Real.log (a:ℝ)
          + 6 * (sharpLogLogConst * Real.log (Real.log (9 * (a:ℝ))) + sharpFloorConst))
          / (δ₀ * Real.log (a:ℝ)) :=
    div_le_div_of_nonneg_right hnum hden.le
  have hsplit : (b:ℝ) * (6.5 * (Real.exp (-D)
            * ((D + 1) * sharpQualityConst + 16 * (Real.exp 1 - 1))) * Real.log (a:ℝ)
          + 6 * (sharpLogLogConst * Real.log (Real.log (9 * (a:ℝ))) + sharpFloorConst))
          / (δ₀ * Real.log (a:ℝ))
      = (b:ℝ) * (6.5 * (Real.exp (-D)
              * ((D + 1) * sharpQualityConst + 16 * (Real.exp 1 - 1))) / δ₀
          + 6 * (sharpLogLogConst * Real.log (Real.log (9 * (a:ℝ))) + sharpFloorConst)
              / (δ₀ * Real.log (a:ℝ))) := by
    field_simp
  rw [hsplit] at hdiv
  have hedge : Real.exp 1 * (b:ℝ) * δ₀ = (b:ℝ) * (Real.exp 1 * δ₀) := by ring
  linear_combination hdiv + hedge

/-- **The sharp twisted Dirichlet cost on a block `a ≤ b ≤ 3a`** (Track R,
T0-6c): `sharpTwistedDirichletCost D δ₀ a b ≤ (b/(a+1))·(13·e^{−D}((D+1)Q + 16(e−1))/δ₀
+ 12(c₂·loglog(9a) + c₃)/(δ₀·log a) + 2e·δ₀) + 2/(a+1)`. -/
theorem sharpTwistedDirichletCost_le (D δ₀ : ℝ) (a b : ℕ) (hD : 0 ≤ D) (hδ₀ : 0 < δ₀)
    (ha : 10^16 ≤ a) (hab : a ≤ b) (hb3 : b ≤ 3 * a) :
    sharpTwistedDirichletCost D δ₀ a b
      ≤ (b:ℝ) / ((a + 1 : ℕ):ℝ)
          * (13 * (Real.exp (-D)
              * ((D + 1) * sharpQualityConst + 16 * (Real.exp 1 - 1))) / δ₀
            + 12 * (sharpLogLogConst * Real.log (Real.log (9 * (a:ℝ))) + sharpFloorConst)
                / (δ₀ * Real.log (a:ℝ))
            + 2 * Real.exp 1 * δ₀)
        + 2 / ((a + 1 : ℕ):ℝ) := by
  unfold sharpTwistedDirichletCost
  have hbud := sharpPartialBudget_le D δ₀ a b hD hδ₀ ha hab hb3
  have ha1 : (0:ℝ) < ((a + 1 : ℕ):ℝ) := by positivity
  have h2 : 2 * sharpPartialBudget D δ₀ a b
      ≤ (b:ℝ) * (13 * (Real.exp (-D)
              * ((D + 1) * sharpQualityConst + 16 * (Real.exp 1 - 1))) / δ₀
            + 12 * (sharpLogLogConst * Real.log (Real.log (9 * (a:ℝ))) + sharpFloorConst)
                / (δ₀ * Real.log (a:ℝ))
            + 2 * Real.exp 1 * δ₀) + 2 := by
    have : (b:ℝ) * (13 * (Real.exp (-D)
              * ((D + 1) * sharpQualityConst + 16 * (Real.exp 1 - 1))) / δ₀
            + 12 * (sharpLogLogConst * Real.log (Real.log (9 * (a:ℝ))) + sharpFloorConst)
                / (δ₀ * Real.log (a:ℝ))
            + 2 * Real.exp 1 * δ₀) + 2
        = 2 * ((b:ℝ) * (6.5 * (Real.exp (-D)
              * ((D + 1) * sharpQualityConst + 16 * (Real.exp 1 - 1))) / δ₀
          + 6 * (sharpLogLogConst * Real.log (Real.log (9 * (a:ℝ))) + sharpFloorConst)
              / (δ₀ * Real.log (a:ℝ))
          + Real.exp 1 * δ₀) + 1) := by ring
    rw [this]
    linarith
  calc 2 * sharpPartialBudget D δ₀ a b / ((a + 1 : ℕ):ℝ)
      ≤ ((b:ℝ) * (13 * (Real.exp (-D)
              * ((D + 1) * sharpQualityConst + 16 * (Real.exp 1 - 1))) / δ₀
            + 12 * (sharpLogLogConst * Real.log (Real.log (9 * (a:ℝ))) + sharpFloorConst)
                / (δ₀ * Real.log (a:ℝ))
            + 2 * Real.exp 1 * δ₀) + 2) / ((a + 1 : ℕ):ℝ) :=
        div_le_div_of_nonneg_right h2 ha1.le
    _ = (b:ℝ) / ((a + 1 : ℕ):ℝ)
          * (13 * (Real.exp (-D)
              * ((D + 1) * sharpQualityConst + 16 * (Real.exp 1 - 1))) / δ₀
            + 12 * (sharpLogLogConst * Real.log (Real.log (9 * (a:ℝ))) + sharpFloorConst)
                / (δ₀ * Real.log (a:ℝ))
            + 2 * Real.exp 1 * δ₀)
        + 2 / ((a + 1 : ℕ):ℝ) := by ring

/-- **The exponential-decay threshold** (Track R, T0-6c): for `M, η > 0`
there is `D₀ ≥ 1` with `(D+1)·e^{−D}·M ≤ η` for every `D ≥ D₀`. -/
theorem exists_exp_decay_le (M η : ℝ) (hM : 0 < M) (hη : 0 < η) :
    ∃ D₀ : ℝ, 1 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D → (D + 1) * Real.exp (-D) * M ≤ η := by
  have h2 : Filter.Tendsto (fun x : ℝ => x ^ (1:ℕ) * Real.exp (-x))
      Filter.atTop (nhds 0) := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hc : (0:ℝ) < η / (2 * M) := by positivity
  have h3 : ∀ᶠ x : ℝ in Filter.atTop, x ^ (1:ℕ) * Real.exp (-x) < η / (2 * M) :=
    h2.eventually_lt_const hc
  rw [Filter.eventually_atTop] at h3
  obtain ⟨x₀, hx₀⟩ := h3
  refine ⟨max x₀ 1, le_max_right _ _, fun D hD => ?_⟩
  have hD1 : (1:ℝ) ≤ D := le_trans (le_max_right _ _) hD
  have hDx := hx₀ D (le_trans (le_max_left _ _) hD)
  rw [pow_one] at hDx
  have hexp0 : 0 < Real.exp (-D) := Real.exp_pos _
  have h4 : D * Real.exp (-D) * (2 * M) < η := by
    have := mul_lt_mul_of_pos_right hDx (by positivity : (0:ℝ) < 2 * M)
    rwa [div_mul_cancel₀ _ (by positivity : (2 * M : ℝ) ≠ 0)] at this
  have h5 : (D + 1) * Real.exp (-D) * M ≤ D * Real.exp (-D) * (2 * M) := by
    have : (D + 1) * Real.exp (-D) * M = (D + 1) * (Real.exp (-D) * M) := by ring
    have h' : D * Real.exp (-D) * (2 * M) = (2 * D) * (Real.exp (-D) * M) := by ring
    rw [this, h']
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  linarith

/-- **The `loglog/log` threshold** (Track R, T0-6c): for `c₂, c₃ ≥ 0` and
`η > 0` there is `x₀ ≥ 10¹⁶` with `c₂·loglog(9a) + c₃ ≤ η·log a` for every
natural `a ≥ x₀`. -/
theorem exists_loglog_le_log (c₂ c₃ η : ℝ) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hη : 0 < η) :
    ∃ x₀ : ℕ, 10^16 ≤ x₀ ∧ ∀ a : ℕ, x₀ ≤ a →
      c₂ * Real.log (Real.log (9 * (a:ℝ))) + c₃ ≤ η * Real.log (a:ℝ) := by
  have hε : (0:ℝ) < η / (4 * (c₂ + 1)) := by positivity
  have hlo := Real.isLittleO_log_id_atTop.def hε
  rw [Filter.eventually_atTop] at hlo
  obtain ⟨w₀, hw₀⟩ := hlo
  -- thresholds: `log a ≥ w₀ ∨ 1`, `log a ≥ 2c₃/η`, `a ≥ 10¹⁶`
  refine ⟨max (max ⌈Real.exp (max w₀ 1)⌉₊ ⌈Real.exp (2 * c₃ / η)⌉₊) (10^16),
    le_max_right _ _, fun a ha => ?_⟩
  have ha16 : 10^16 ≤ a := le_trans (le_max_right _ _) ha
  have haR : (10:ℝ)^16 ≤ (a:ℝ) := by exact_mod_cast ha16
  have ha0 : (0:ℝ) < (a:ℝ) := by linarith
  have hexpw : Real.exp (max w₀ 1) ≤ (a:ℝ) := by
    have h1 : (⌈Real.exp (max w₀ 1)⌉₊ : ℝ) ≤ (a:ℝ) := by
      exact_mod_cast le_trans (le_max_left _ _) (le_trans (le_max_left _ _) ha)
    linarith [Nat.le_ceil (Real.exp (max w₀ 1))]
  have hexpc : Real.exp (2 * c₃ / η) ≤ (a:ℝ) := by
    have h1 : (⌈Real.exp (2 * c₃ / η)⌉₊ : ℝ) ≤ (a:ℝ) := by
      exact_mod_cast le_trans (le_max_right _ _) (le_trans (le_max_left _ _) ha)
    linarith [Nat.le_ceil (Real.exp (2 * c₃ / η))]
  have hloga_w : max w₀ 1 ≤ Real.log (a:ℝ) := (Real.le_log_iff_exp_le ha0).mpr hexpw
  have hloga_c : 2 * c₃ / η ≤ Real.log (a:ℝ) := (Real.le_log_iff_exp_le ha0).mpr hexpc
  have hloga1 : 1 ≤ Real.log (a:ℝ) := le_trans (le_max_right _ _) hloga_w
  have hloga0 : 0 < Real.log (a:ℝ) := by linarith
  have h36 : (36:ℝ) ≤ Real.log (a:ℝ) :=
    (Real.le_log_iff_exp_le ha0).mpr (le_trans exp_36_le haR)
  -- `log(9a) = log 9 + log a ≤ 1.08·log a`, and `w := log(9a) ≥ w₀`
  have hlog9a : Real.log (9 * (a:ℝ)) = Real.log 9 + Real.log (a:ℝ) :=
    Real.log_mul (by norm_num) ha0.ne'
  have hlog9a_le : Real.log (9 * (a:ℝ)) ≤ 1.08 * Real.log (a:ℝ) := by
    rw [hlog9a]
    linarith [log_nine_le]
  have hlog9a_ge : Real.log (a:ℝ) ≤ Real.log (9 * (a:ℝ)) := by
    rw [hlog9a]
    linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 9)]
  have hw : w₀ ≤ Real.log (9 * (a:ℝ)) :=
    le_trans (le_trans (le_max_left _ _) hloga_w) hlog9a_ge
  have hw1 : (1:ℝ) ≤ Real.log (9 * (a:ℝ)) := le_trans hloga1 hlog9a_ge
  have hbound := hw₀ (Real.log (9 * (a:ℝ))) hw
  simp only [id, Real.norm_eq_abs] at hbound
  rw [abs_of_nonneg (Real.log_nonneg hw1), abs_of_pos (by linarith)] at hbound
  -- `c₂·loglog(9a) ≤ c₂·(η/(4(c₂+1)))·1.08·log a ≤ (η/2)·log a`
  have h1 : c₂ * Real.log (Real.log (9 * (a:ℝ)))
      ≤ c₂ * (η / (4 * (c₂ + 1)) * (1.08 * Real.log (a:ℝ))) := by
    refine mul_le_mul_of_nonneg_left ?_ hc₂
    calc Real.log (Real.log (9 * (a:ℝ)))
        ≤ η / (4 * (c₂ + 1)) * Real.log (9 * (a:ℝ)) := hbound
      _ ≤ η / (4 * (c₂ + 1)) * (1.08 * Real.log (a:ℝ)) :=
          mul_le_mul_of_nonneg_left hlog9a_le hε.le
  have h1' : c₂ * (η / (4 * (c₂ + 1)) * (1.08 * Real.log (a:ℝ)))
      ≤ η / 2 * Real.log (a:ℝ) := by
    have hfrac : c₂ / (c₂ + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have : c₂ * (η / (4 * (c₂ + 1)) * (1.08 * Real.log (a:ℝ)))
        = (c₂ / (c₂ + 1)) * (0.27 * η * Real.log (a:ℝ)) := by
      field_simp
      ring
    rw [this]
    have hpos : 0 ≤ 0.27 * η * Real.log (a:ℝ) := by positivity
    calc (c₂ / (c₂ + 1)) * (0.27 * η * Real.log (a:ℝ))
        ≤ 1 * (0.27 * η * Real.log (a:ℝ)) := mul_le_mul_of_nonneg_right hfrac hpos
      _ ≤ η / 2 * Real.log (a:ℝ) := by nlinarith
  -- `c₃ ≤ (η/2)·log a`
  have h2 : c₃ ≤ η / 2 * Real.log (a:ℝ) := by
    have := mul_le_mul_of_nonneg_left hloga_c (by linarith : (0:ℝ) ≤ η / 2)
    have hc : η / 2 * (2 * c₃ / η) = c₃ := by
      field_simp
    linarith
  linarith

/-- **The fixed-strength `ε`-form of the sharp twisted Dirichlet cost**
(Track R, T0-6c): for every `ε > 0` there are a strength `D₀ ≥ 1` and a scale
`x₀ ≥ 10¹⁶` such that at `δ₀ := ε/(8e)`, for every `D ≥ D₀` and every block
`x₀ ≤ a ≤ b ≤ 3a`,

  `sharpTwistedDirichletCost D (ε/(8e)) a b ≤ ε·b/(a+1)`

— uniformly in the scale.  The three quarters of `ε`: the quality term
`13·e^{−D}((D+1)Q + 16(e−1))/δ₀ ≤ ε/4` (`exists_exp_decay_le`), the
`loglog/log` term `12(c₂ loglog(9a) + c₃)/(δ₀ log a) ≤ ε/4`
(`exists_loglog_le_log`), the edge `2eδ₀ = ε/4`; and the constant `2/(a+1)`
is at most `εb/(4(a+1))` once `b ≥ 8/ε`. -/
theorem sharpTwistedDirichletCost_le_eps (ε : ℝ) (hε : 0 < ε) :
    ∃ (D₀ : ℝ) (x₀ : ℕ), 1 ≤ D₀ ∧ 10^16 ≤ x₀ ∧
      ∀ D : ℝ, D₀ ≤ D → ∀ a b : ℕ, x₀ ≤ a → a ≤ b → b ≤ 3 * a →
        sharpTwistedDirichletCost D (ε / (8 * Real.exp 1)) a b
          ≤ ε * (b:ℝ) / ((a + 1 : ℕ):ℝ) := by
  have he0 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  set δ₀ : ℝ := ε / (8 * Real.exp 1) with hδ₀_def
  have hδ₀ : 0 < δ₀ := by positivity
  have hM : (0:ℝ) < sharpQualityConst + 16 * (Real.exp 1 - 1) := by
    have := sharpQualityConst_nonneg
    have he1 : 0 < Real.exp 1 - 1 := by linarith [Real.exp_one_gt_d9]
    linarith
  -- the quality threshold: `(D+1)e^{−D}·M ≤ ε·δ₀/52`
  obtain ⟨D₀, hD₀1, hDdecay⟩ := exists_exp_decay_le
    (sharpQualityConst + 16 * (Real.exp 1 - 1)) (ε * δ₀ / 52) hM (by positivity)
  -- the `loglog/log` threshold: `c₂·loglog(9a) + c₃ ≤ (ε·δ₀/48)·log a`
  obtain ⟨x₁, hx₁16, hx₁⟩ := exists_loglog_le_log sharpLogLogConst sharpFloorConst
    (ε * δ₀ / 48) sharpLogLogConst_nonneg sharpFloorConst_nonneg (by positivity)
  refine ⟨D₀, max x₁ ⌈8 / ε⌉₊, hD₀1, le_trans hx₁16 (le_max_left _ _), ?_⟩
  intro D hD a b ha hab hb3
  have hax₁ : x₁ ≤ a := le_trans (le_max_left _ _) ha
  have ha16 : 10^16 ≤ a := le_trans hx₁16 hax₁
  have hD0 : 0 ≤ D := by linarith
  have hcost := sharpTwistedDirichletCost_le D δ₀ a b hD0 hδ₀ ha16 hab hb3
  -- the three pieces
  have haR : (10:ℝ)^16 ≤ (a:ℝ) := by exact_mod_cast ha16
  have ha0 : (0:ℝ) < (a:ℝ) := by linarith
  have ha1 : (0:ℝ) < ((a + 1 : ℕ):ℝ) := by positivity
  have hbR : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast hab
  have hb0 : (0:ℝ) < (b:ℝ) := by linarith
  have hba : 0 ≤ (b:ℝ) / ((a + 1 : ℕ):ℝ) := by positivity
  have hloga0 : 0 < Real.log (a:ℝ) := by
    have h36 : (36:ℝ) ≤ Real.log (a:ℝ) :=
      (Real.le_log_iff_exp_le ha0).mpr (le_trans exp_36_le haR)
    linarith
  -- (i) quality: `13·e^{−D}((D+1)Q + 16(e−1))/δ₀ ≤ ε/4`
  have hq : 13 * (Real.exp (-D)
        * ((D + 1) * sharpQualityConst + 16 * (Real.exp 1 - 1))) / δ₀ ≤ ε / 4 := by
    have hdec := hDdecay D hD
    have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
    have hexp0 : 0 < Real.exp (-D) := Real.exp_pos _
    have hK : Real.exp (-D) * ((D + 1) * sharpQualityConst + 16 * (Real.exp 1 - 1))
        ≤ (D + 1) * Real.exp (-D) * (sharpQualityConst + 16 * (Real.exp 1 - 1)) := by
      have : (D + 1) * Real.exp (-D) * (sharpQualityConst + 16 * (Real.exp 1 - 1))
          - Real.exp (-D) * ((D + 1) * sharpQualityConst + 16 * (Real.exp 1 - 1))
          = D * Real.exp (-D) * (16 * (Real.exp 1 - 1)) := by ring
      have h0 : 0 ≤ D * Real.exp (-D) * (16 * (Real.exp 1 - 1)) := by positivity
      linarith
    rw [div_le_iff₀ hδ₀]
    linarith [hK, hdec]
  -- (ii) `loglog/log`: `12(c₂ loglog(9a) + c₃)/(δ₀ log a) ≤ ε/4`
  have hl : 12 * (sharpLogLogConst * Real.log (Real.log (9 * (a:ℝ))) + sharpFloorConst)
        / (δ₀ * Real.log (a:ℝ)) ≤ ε / 4 := by
    have h1 := hx₁ a hax₁
    rw [div_le_iff₀ (by positivity)]
    linear_combination 12 * h1
  -- (iii) the edge: `2eδ₀ = ε/4`
  have hedge : 2 * Real.exp 1 * δ₀ = ε / 4 := by
    rw [hδ₀_def]
    field_simp
    ring
  -- (iv) the constant: `2/(a+1) ≤ ε·b/(4(a+1))`
  have hb8 : 8 / ε ≤ (b:ℝ) := by
    have h1 : (⌈8 / ε⌉₊ : ℝ) ≤ (a:ℝ) := by
      exact_mod_cast le_trans (le_max_right _ _) ha
    linarith [Nat.le_ceil (8 / ε)]
  have hconst : 2 / ((a + 1 : ℕ):ℝ) ≤ ε * (b:ℝ) / (4 * ((a + 1 : ℕ):ℝ)) := by
    rw [div_le_div_iff₀ ha1 (by positivity)]
    have h8 : 8 ≤ ε * (b:ℝ) := by
      have := mul_le_mul_of_nonneg_left hb8 hε.le
      rwa [mul_div_cancel₀ _ hε.ne'] at this
    have := mul_le_mul_of_nonneg_right h8 ha1.le
    linarith
  -- assemble
  have hsum : (b:ℝ) / ((a + 1 : ℕ):ℝ)
        * (13 * (Real.exp (-D)
            * ((D + 1) * sharpQualityConst + 16 * (Real.exp 1 - 1))) / δ₀
          + 12 * (sharpLogLogConst * Real.log (Real.log (9 * (a:ℝ))) + sharpFloorConst)
              / (δ₀ * Real.log (a:ℝ))
          + 2 * Real.exp 1 * δ₀)
      ≤ (b:ℝ) / ((a + 1 : ℕ):ℝ) * (3 * ε / 4) := by
    refine mul_le_mul_of_nonneg_left ?_ hba
    linarith [hq, hl, hedge]
  have hfinal : (b:ℝ) / ((a + 1 : ℕ):ℝ) * (3 * ε / 4) + ε * (b:ℝ) / (4 * ((a + 1 : ℕ):ℝ))
      = ε * (b:ℝ) / ((a + 1 : ℕ):ℝ) := by
    field_simp
    ring
  linarith [hcost, hsum, hconst, hfinal]

end MoltResearch
