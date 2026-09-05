import MoltResearch.Discrepancy.HalaszSharpWindow

/-!
# The frequency-windowed sharp Halász chain, and the twist bridge

`NonPretentiousAt f A x` bundles a distance floor with the frequency range
`|t| ≤ A·x`, centred at `0`.  The Halász capstone uses far less: the band
sup `hBu` of the smooth phase sum is taken over `|t| ≤ halaszM x + 1 ≈ log⁴x`,
and `norm_phase_euler_prod_le_of_nonPretentious` consumes the hypothesis at
exactly one twist per frequency.  For the *twisted* function `g(n)·n^{−iξ}`
that matters: its distance to `n^{2πit}` is the distance of `g` to
`n^{i(2πt+ξ)}`, so `NonPretentiousAt (g·n^{−iξ}) A x` needs `|2πt + ξ| ≤ A·x`
for every `|t| ≤ A·x` — i.e. `|ξ| ≤ (A − A')·x`
(`nonPretentiousAt_archTwist`).  The exceptional-cell leg applies the
twisted bound at quotient scales `x = A_scale/(q·n₁)` and frequencies
`|t| ≤ T ≍ A_scale/H`, where `2π|t| ≫ x` as soon as `q·n₁ ≫ H` — so every
twisted block bound stated with `|2πt| ≤ (D/2)·a` (VI-9e, T0-5) is
inapplicable there (design report, "The `𝒯₀` leg", finding on the twist
range).  In `[mrt]` there is no such constraint: `M(f;X)` is the infimum over
*all* `|t| ≤ X`, and Halász is applied at scale `X/p` with twists up to `X`.

This leaf states the sharp chain on the hypothesis it actually uses,

  `HalaszWindowAt f A x := ∀ t, |t| ≤ halaszM x + 1 → A ≤ 𝔻(f, n^{2πit}; x)²`,

a *window* of width `≈ log⁴x` around frequency `0` in the twisted variable —
i.e. around `ξ` for `g` — with no constraint tying `ξ` to `x`; and proves the
bridge `halaszWindowAt_archTwist_of_nonPretentiousAt`: from
`NonPretentiousAt g A N` at a top scale `N` (range `|s| ≤ A·N`, which
contains `ξ ± 2π(halaszM u + 1)` for every `|ξ| ≤ T ≪ N`), the window at any
scale `u ≤ N` holds at strength `A − 2(loglog N − loglog u + 12)`
(`pretentiousDistSq_le_add_mass` + `mertens_mass_diff_le`), so at
`u ≥ N^{1/2}` the loss is `≤ 2·log 2 + 24`.  The windowed prefix bound and
the windowed sharp twisted Dirichlet block are the mirrors of T0-5 with
`HalaszWindowAt` in place of `NonPretentiousAt`; these are the forms the
exceptional recut consumes.
-/

namespace MoltResearch

open ExpSums

/-- **The frequency-windowed distance floor** the Halász capstone uses: at
scale `x`, every archimedean twist of frequency `|t| ≤ halaszM x + 1` is at
squared pretentious distance `≥ A` from `f`. -/
def HalaszWindowAt (f : ℕ → ℂ) (A : ℝ) (x : ℕ) : Prop :=
  ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
    A ≤ pretentiousDistSq f (charTwist 1 1 (2 * Real.pi * t)) x

theorem HalaszWindowAt.mono {f : ℕ → ℂ} {A A' : ℝ} {x : ℕ}
    (h : HalaszWindowAt f A x) (hA' : A' ≤ A) : HalaszWindowAt f A' x :=
  fun t ht => le_trans hA' (h t ht)

/-- `NonPretentiousAt` on the full range implies the window whenever the
band fits, `7·(halaszM x + 1) ≤ A·x` (using `2π < 7`). -/
theorem halaszWindowAt_of_nonPretentiousAt {f : ℕ → ℂ} {A : ℝ} {x : ℕ}
    (hA : NonPretentiousAt f A x) (h1A : 1 ≤ A)
    (hband : 7 * (((halaszM x : ℕ):ℝ) + 1) ≤ A * (x:ℝ)) :
    HalaszWindowAt f A x := by
  intro t ht
  refine hA 1 1 (2 * Real.pi * t) (by exact_mod_cast h1A) ?_
  have hpi7 : 2 * Real.pi ≤ 7 := by
    have := Real.pi_lt_d2
    linarith
  rw [abs_mul, abs_of_pos Real.two_pi_pos]
  calc 2 * Real.pi * |t| ≤ 7 * |t| :=
        mul_le_mul_of_nonneg_right hpi7 (abs_nonneg t)
    _ ≤ 7 * (((halaszM x : ℕ):ℝ) + 1) :=
        mul_le_mul_of_nonneg_left ht (by norm_num)
    _ ≤ A * (x:ℝ) := hband

/-- **The band sup of the truncated Euler product from one distance floor**
(Track R, T0-6): `norm_phase_euler_prod_le_of_nonPretentious` with its only
use of `NonPretentiousAt` — the level-one twist at the frequency in hand —
made the hypothesis. -/
theorem norm_phase_euler_prod_le_of_distSq (f : ℕ → ℂ)
    (hb : ∀ n, ‖f n‖ ≤ 1) (x : ℕ) (hx : 3 ≤ x)
    (A ξ : ℝ)
    (hdist : A ≤ pretentiousDistSq f (charTwist 1 1 (2 * Real.pi * ξ)) x) :
    ‖∏ p ∈ x.primesBelow,
        (1 - f p * ((p : ℕ) : ℂ)⁻¹
            * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))⁻¹‖
      ≤ Real.exp 5 * (2 + Real.log x) * Real.exp (-A) := by
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hlogx : (0 : ℝ) < Real.log x :=
    Real.log_pos (by linarith)
  have hmass := sum_one_div_primesBelow_le_log_log x hx
  have hprod := norm_phase_euler_prod_le f hb x ξ
  have hre := sum_re_phase_eq_mass_sub_distSq f x ξ 1
  refine le_trans hprod ?_
  rw [hre]
  have hexp : (∑ p ∈ x.primesBelow, (1 : ℝ)/(p : ℝ))
      - pretentiousDistSq f (charTwist 1 1 (2*Real.pi*ξ)) x + 2
      ≤ Real.log (2 + Real.log x) + 5 - A := by
    linarith
  refine le_trans (Real.exp_le_exp.mpr hexp) ?_
  rw [show Real.log (2 + Real.log x) + 5 - A
      = Real.log (2 + Real.log x) + 5 + -A by ring,
    Real.exp_add, Real.exp_add, Real.exp_log (by linarith)]
  ring_nf
  exact le_refl _

/-- The log-free band sup of the smooth phase sum from one distance floor. -/
theorem norm_smoothPhaseSum_le_of_distSq (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (hb : ∀ n, ‖f n‖ ≤ 1) (x : ℕ) (hx : 3 ≤ x)
    (A ξ : ℝ)
    (hdist : A ≤ pretentiousDistSq f (charTwist 1 1 (2 * Real.pi * ξ)) x) :
    ‖smoothPhaseSum f x ξ‖
      ≤ Real.exp 5 * (2 + Real.log (x:ℝ)) * Real.exp (-A) := by
  rw [smoothPhaseSum_eq_prod f hcm h1 hb x ξ]
  exact norm_phase_euler_prod_le_of_distSq f hb x hx A ξ hdist

open Real Finset in
/-- **The sharp Halász Riesz mean at a free split, windowed hypothesis**
(Track R, T0-6): the `b`-instantiation of the sharp §3 assembly at
`b := e⁵(2+log x)e^{−A}` from `HalaszWindowAt f A x` alone — no
`NonPretentiousAt`, no band condition `7(halaszM x + 1) ≤ A·x`. -/
theorem rieszMeanC_log_le_sharp_halasz_of_window (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hcm : CompletelyMultiplicativeC f)
    (h1 : f 1 = 1)
    (x y K₀ K₁ : ℕ) (hx : 10^16 ≤ x) (hy2 : 2 ≤ y) (hyx : 2*y ≤ x)
    (hy : (Real.log (x:ℝ))^2 ≤ (y:ℝ))
    (hK₀1 : 1 ≤ K₀)
    (hK₀low : Real.exp 1 * Real.log 2
      ≤ Real.exp (-(K₀:ℝ)) * Real.log (x:ℝ))
    (hK₀max : Real.exp (-((K₀:ℝ)+1)) * Real.log (x:ℝ)
      < Real.exp 1 * Real.log 2)
    (hK₁ : K₁ ≤ K₀)
    (A : ℝ) (hwin : HalaszWindowAt f A x) :
    ‖(∑ n ∈ Finset.Icc 1 x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
        * ((Real.log (x:ℝ) : ℝ) : ℂ)‖
      ≤ 35*(x:ℝ) + (x:ℝ)*(Real.log (y:ℝ) + 2) + 2*((x:ℝ)+1)*Real.log 4
        + 64 * (x:ℝ) * (12 * Real.log (Real.log (x:ℝ)) + 18)
        + ((K₁:ℝ) * ((x:ℝ) * Real.sqrt ((Real.exp π)^2 * 10^15
              * ((Real.exp 5 * (2 + Real.log (x:ℝ))
                  * Real.exp (-A))^2 + 1))
            + 2*(x:ℝ)*Real.log 4)
          + (16 * (Real.exp 1 - 1) * (x:ℝ) * Real.log (x:ℝ) * Real.exp (-(K₁:ℝ))
            + ((K₀ + 2 - K₁ : ℕ):ℝ)
              * ((x:ℝ) * (16 * Real.log 2 + 16 * Real.log 4)))) := by
  classical
  have hx3 : (3:ℕ) ≤ x := le_trans (by norm_num) hx
  have hb0 : (0:ℝ) ≤ Real.exp 5 * (2 + Real.log (x:ℝ)) * Real.exp (-A) := by
    have h2L : (0:ℝ) ≤ 2 + Real.log (x:ℝ) := by
      have := Real.log_natCast_nonneg x
      linarith
    exact mul_nonneg (mul_nonneg (Real.exp_pos 5).le h2L)
      (Real.exp_pos (-A)).le
  have hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖ExpSums.smoothPhaseSum f x t‖
        ≤ Real.exp 5 * (2 + Real.log (x:ℝ)) * Real.exp (-A) :=
    fun t ht => norm_smoothPhaseSum_le_of_distSq f hcm h1 hf x hx3 A t (hwin t ht)
  exact rieszMeanC_log_le_sharp_of_nonPretentious f hf hcm h1 x y K₀ K₁ hx hy2
    hyx hy hK₀1 hK₀low hK₀max hK₁
    (three_le_div_blockLo x K₀ hx hK₀low)
    (Real.exp 5 * (2 + Real.log (x:ℝ)) * Real.exp (-A)) hb0 hBu

open Real Finset in
/-- **The sharp Halász Riesz mean from the window** (Track R, T0-6):
`‖R(x)·log x‖ ≤ Ĥ⁺(A, x)` under `HalaszWindowAt f A x`, `A ≥ 1`. -/
theorem rieszMeanC_log_sharp_le_window (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (x : ℕ) (hx : 10^16 ≤ x)
    (A : ℝ) (h1A : 1 ≤ A) (hwin : HalaszWindowAt f A x) :
    ‖(∑ n ∈ Finset.Icc 1 x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
        * ((Real.log (x:ℝ) : ℝ) : ℂ)‖
      ≤ halaszBudgetSharp A (x:ℝ) := by
  classical
  obtain ⟨y, K₀, hy2, hyx, hy, hylog, hK₀1, hK₀low, hK₀max⟩ :=
    exists_section3_window_shell x hx
  have hK₁ : min K₀ ⌈A⌉₊ ≤ K₀ := min_le_left _ _
  have hcap := rieszMeanC_log_le_sharp_halasz_of_window f hf hcm h1
    x y K₀ (min K₀ ⌈A⌉₊) hx hy2 hyx hy hK₀1 hK₀low hK₀max hK₁ A hwin
  exact le_trans hcap (sharp_survivor_price x y K₀ hx hy2 hylog hK₀low hK₀max A h1A)

open Real Finset in
/-- **The sharp plain-sum Halász bound from the window** (Track R, T0-6). -/
theorem plain_sumC_le_halaszBudgetSharp_window (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hcm : CompletelyMultiplicativeC f)
    (h1 : f 1 = 1)
    (x X : ℕ) (hx : 10^16 ≤ x) (hxX : x ≤ X)
    (A : ℝ) (h1A : 1 ≤ A)
    (hwx : HalaszWindowAt f A x) (hwX : HalaszWindowAt f A X) :
    ‖∑ n ∈ Finset.Icc 1 x, f n‖ * (Real.log (X:ℝ) - Real.log (x:ℝ))
      ≤ halaszBudgetSharp A (X:ℝ) / Real.log (X:ℝ)
        + halaszBudgetSharp A (x:ℝ) / Real.log (x:ℝ)
        + ((X:ℝ) - (x:ℝ)) * (Real.log (X:ℝ) - Real.log (x:ℝ)) := by
  have hX : 10^16 ≤ X := le_trans hx hxX
  have hx2 : 2 ≤ x := le_trans (by norm_num) hx
  have hRx := rieszMeanC_log_sharp_le_window f hf hcm h1 x hx A h1A hwx
  have hRX := rieszMeanC_log_sharp_le_window f hf hcm h1 X hX A h1A hwX
  exact plain_sumC_le_of_riesz_bounds f hf x X hx2 hxX _ _ hRx hRX

open Real Finset in
/-- **The divided sharp capstone from the window** (Track R, T0-6). -/
theorem plain_sumC_le_halaszBudgetSharp_window_div (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hcm : CompletelyMultiplicativeC f)
    (h1 : f 1 = 1)
    (x X : ℕ) (hx : 10^16 ≤ x) (hxX : x ≤ X)
    (A : ℝ) (h1A : 1 ≤ A)
    (hwx : HalaszWindowAt f A x) (hwX : HalaszWindowAt f A X)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hδX : δ₀ ≤ Real.log (X:ℝ) - Real.log (x:ℝ)) :
    ‖∑ n ∈ Finset.Icc 1 x, f n‖
      ≤ (halaszBudgetSharp A (X:ℝ) / Real.log (X:ℝ)
          + halaszBudgetSharp A (x:ℝ) / Real.log (x:ℝ)) / δ₀
        + ((X:ℝ) - (x:ℝ)) := by
  have h := plain_sumC_le_halaszBudgetSharp_window f hf hcm h1 x X hx hxX A h1A hwx hwX
  have hA0 : (0:ℝ) ≤ A := by linarith
  have hD : (0:ℝ) < Real.log (X:ℝ) - Real.log (x:ℝ) :=
    lt_of_lt_of_le hδ₀ hδX
  have hxR : (Real.exp 1) ≤ (x:ℝ) := by
    have h3 : (3:ℝ) ≤ (x:ℝ) := by
      have : (3:ℕ) ≤ x := le_trans (by norm_num) hx
      exact_mod_cast this
    linarith [Real.exp_one_lt_d9.le]
  have hXR : (Real.exp 1) ≤ (X:ℝ) := by
    have : (x:ℝ) ≤ (X:ℝ) := by exact_mod_cast hxX
    linarith
  have hlogx : (0:ℝ) < Real.log (x:ℝ) := by
    have hx1 : (1:ℝ) < (x:ℝ) := by
      have : (2:ℕ) ≤ x := le_trans (by norm_num) hx
      exact_mod_cast lt_of_lt_of_le (by norm_num : (1:ℕ) < 2) this
    exact Real.log_pos hx1
  have hlogX : (0:ℝ) < Real.log (X:ℝ) := by
    have : Real.log (x:ℝ) ≤ Real.log (X:ℝ) := by
      have hxx : (x:ℝ) ≤ (X:ℝ) := by exact_mod_cast hxX
      exact Real.log_le_log (by positivity) hxx
    linarith
  have hE0 : (0:ℝ) ≤ halaszBudgetSharp A (X:ℝ) / Real.log (X:ℝ)
      + halaszBudgetSharp A (x:ℝ) / Real.log (x:ℝ) := by
    have hEX := halaszBudgetSharp_nonneg A (X:ℝ) hA0 hXR
    have hEx := halaszBudgetSharp_nonneg A (x:ℝ) hA0 hxR
    have d1 : (0:ℝ) ≤ halaszBudgetSharp A (X:ℝ) / Real.log (X:ℝ) :=
      div_nonneg hEX hlogX.le
    have d2 : (0:ℝ) ≤ halaszBudgetSharp A (x:ℝ) / Real.log (x:ℝ) :=
      div_nonneg hEx hlogx.le
    linarith
  have hkey : (‖∑ n ∈ Finset.Icc 1 x, f n‖ - ((X:ℝ) - (x:ℝ)))
      * (Real.log (X:ℝ) - Real.log (x:ℝ))
      ≤ halaszBudgetSharp A (X:ℝ) / Real.log (X:ℝ)
        + halaszBudgetSharp A (x:ℝ) / Real.log (x:ℝ) := by
    nlinarith [h]
  have h2 : ‖∑ n ∈ Finset.Icc 1 x, f n‖ - ((X:ℝ) - (x:ℝ))
      ≤ (halaszBudgetSharp A (X:ℝ) / Real.log (X:ℝ)
          + halaszBudgetSharp A (x:ℝ) / Real.log (x:ℝ))
        / (Real.log (X:ℝ) - Real.log (x:ℝ)) :=
    (le_div_iff₀ hD).mpr hkey
  have h3 : (halaszBudgetSharp A (X:ℝ) / Real.log (X:ℝ)
        + halaszBudgetSharp A (x:ℝ) / Real.log (x:ℝ))
        / (Real.log (X:ℝ) - Real.log (x:ℝ))
      ≤ (halaszBudgetSharp A (X:ℝ) / Real.log (X:ℝ)
          + halaszBudgetSharp A (x:ℝ) / Real.log (x:ℝ)) / δ₀ := by
    gcongr
  linarith

set_option maxHeartbeats 1600000 in
open Real Finset in
/-- **The block-uniform prefix bound from the window** (Track R, T0-6):
`prefix_le_sharpPartialBudget` with `HalaszWindowAt f A u` at every scale
`u ∈ [a, 3B']` in place of `NonPretentiousAt`. -/
theorem prefix_le_sharpPartialBudget_window (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hcm : CompletelyMultiplicativeC f)
    (h1 : f 1 = 1)
    (a B' : ℕ) (ha : 10^16 ≤ a) (haB : a ≤ B')
    (A : ℝ) (h1A : 1 ≤ A)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₁ : δ₀ ≤ 1)
    (hwin : ∀ u : ℕ, a ≤ u → u ≤ 3*B' → HalaszWindowAt f A u) :
    ∀ u : ℕ, a ≤ u → u ≤ B' →
      ‖∑ k ∈ Finset.Icc 1 u, f k‖ ≤ sharpPartialBudget A δ₀ a B' := by
  intro u hau hu
  have hbig : 10^16 ≤ u := le_trans ha hau
  have hB' : 10^16 ≤ B' := le_trans ha haB
  have hB'R : (10:ℝ)^16 ≤ (B':ℝ) := by exact_mod_cast hB'
  have hA0 : (0:ℝ) ≤ A := by linarith
  have he272 : Real.exp 1 ≤ (2.72:ℝ) := by
    have := Real.exp_one_lt_d9
    linarith
  have hbudget0 : (0:ℝ) ≤ halaszBudgetSharp A (3*(B':ℝ)) := by
    refine halaszBudgetSharp_nonneg A _ hA0 ?_
    linarith [he272]
  have huR : (10:ℝ)^16 ≤ (u:ℝ) := by exact_mod_cast hbig
  have hu0 : (0:ℝ) < (u:ℝ) := by linarith
  set X : ℕ := ⌈(u:ℝ) * Real.exp δ₀⌉₊ with hX_def
  have hXreal : (u:ℝ) * Real.exp δ₀ ≤ (X:ℝ) := Nat.le_ceil _
  have hexpδ1 : (1:ℝ) ≤ Real.exp δ₀ := by
    rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr hδ₀.le
  have hexpδe : Real.exp δ₀ ≤ Real.exp 1 := Real.exp_le_exp.mpr hδ₁
  have huX : u ≤ X := by
    have h1' : (u:ℝ) ≤ (X:ℝ) := by nlinarith [hXreal, hu0]
    exact_mod_cast h1'
  have hXle : (X:ℝ) ≤ (u:ℝ) * Real.exp δ₀ + 1 := by
    have := Nat.ceil_lt_add_one
      (by positivity : (0:ℝ) ≤ (u:ℝ) * Real.exp δ₀)
    linarith
  have hX3B : X ≤ 3*B' := by
    have hc : (X:ℝ) ≤ 3*(B':ℝ) := by
      have huB : (u:ℝ) ≤ (B':ℝ) := by exact_mod_cast hu
      nlinarith [hXle, hexpδe, he272, hB'R]
    exact_mod_cast hc
  have hX16 : 10^16 ≤ X := le_trans hbig huX
  -- the two nonpretentiousness instances
  have hNPu := hwin u hau (by omega)
  have hNPX := hwin X (le_trans hau huX) hX3B
  -- the log-gap
  have hgap : δ₀ ≤ Real.log (X:ℝ) - Real.log (u:ℝ) := by
    have h1' : Real.log ((u:ℝ) * Real.exp δ₀) ≤ Real.log (X:ℝ) :=
      Real.log_le_log (by positivity) hXreal
    rw [Real.log_mul (ne_of_gt hu0) (ne_of_gt (Real.exp_pos _)),
      Real.log_exp] at h1'
    linarith
  -- the divided capstone
  have hdiv := plain_sumC_le_halaszBudgetSharp_window_div f hf hcm h1 u X hbig huX
    A h1A hNPu hNPX δ₀ hδ₀ hgap
  have h36 : ∀ z : ℕ, 10^16 ≤ z → (36:ℝ) ≤ Real.log (z:ℝ) := by
    intro z hz
    have hz0 : (0:ℝ) < (z:ℝ) := by
      have : (0:ℕ) < z := by omega
      exact_mod_cast this
    rw [Real.le_log_iff_exp_le hz0]
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
    have hzR : (10:ℝ)^16 ≤ (z:ℝ) := by exact_mod_cast hz
    rw [h36e]
    linarith
  have h36a := h36 a ha
  -- both denominators are at least `log a`
  have haR : (0:ℝ) < (a:ℝ) := by
    have : (0:ℕ) < a := by omega
    exact_mod_cast this
  have hloga0 : (0:ℝ) < Real.log (a:ℝ) := by linarith
  have hlogau : Real.log (a:ℝ) ≤ Real.log (u:ℝ) :=
    Real.log_le_log haR (by exact_mod_cast hau)
  have hlogaX : Real.log (a:ℝ) ≤ Real.log (X:ℝ) :=
    Real.log_le_log haR (by exact_mod_cast (le_trans hau huX))
  -- lift both numerators to the top scale
  have hmonoX : halaszBudgetSharp A (X:ℝ)
      ≤ halaszBudgetSharp A (3*(B':ℝ)) := by
    refine halaszBudgetSharp_mono A _ _ hA0 ?_ ?_
    · have : (10:ℝ)^16 ≤ (X:ℝ) := by exact_mod_cast hX16
      linarith [he272]
    · have hc : (X:ℝ) ≤ ((3*B' : ℕ):ℝ) := by exact_mod_cast hX3B
      push_cast at hc
      linarith
  have hmonou : halaszBudgetSharp A (u:ℝ)
      ≤ halaszBudgetSharp A (3*(B':ℝ)) := by
    refine halaszBudgetSharp_mono A _ _ hA0 ?_ ?_
    · linarith [he272]
    · have huB : (u:ℝ) ≤ (B':ℝ) := by exact_mod_cast hu
      linarith [hB'R]
  have hquotX : halaszBudgetSharp A (X:ℝ) / Real.log (X:ℝ)
      ≤ halaszBudgetSharp A (3*(B':ℝ)) / Real.log (a:ℝ) :=
    div_le_div₀ hbudget0 hmonoX hloga0 hlogaX
  have hquotu : halaszBudgetSharp A (u:ℝ) / Real.log (u:ℝ)
      ≤ halaszBudgetSharp A (3*(B':ℝ)) / Real.log (a:ℝ) :=
    div_le_div₀ hbudget0 hmonou hloga0 hlogau
  have hsum : halaszBudgetSharp A (X:ℝ)/Real.log (X:ℝ)
      + halaszBudgetSharp A (u:ℝ)/Real.log (u:ℝ)
      ≤ 2 * halaszBudgetSharp A (3*(B':ℝ)) / Real.log (a:ℝ) := by
    have h2 : halaszBudgetSharp A (3*(B':ℝ)) / Real.log (a:ℝ)
        + halaszBudgetSharp A (3*(B':ℝ)) / Real.log (a:ℝ)
        = 2 * halaszBudgetSharp A (3*(B':ℝ)) / Real.log (a:ℝ) := by ring
    linarith [hquotX, hquotu]
  have hsumδ : (halaszBudgetSharp A (X:ℝ)/Real.log (X:ℝ)
      + halaszBudgetSharp A (u:ℝ)/Real.log (u:ℝ)) / δ₀
      ≤ 2 * halaszBudgetSharp A (3*(B':ℝ)) / (δ₀ * Real.log (a:ℝ)) := by
    rw [show 2 * halaszBudgetSharp A (3*(B':ℝ)) / (δ₀ * Real.log (a:ℝ))
      = (2 * halaszBudgetSharp A (3*(B':ℝ)) / Real.log (a:ℝ)) / δ₀ from by
        rw [div_div, mul_comm δ₀]]
    gcongr
  -- the edge term
  have hedge : (X:ℝ) - (u:ℝ) ≤ Real.exp 1 * (B':ℝ) * δ₀ + 1 := by
    have hexp1 : Real.exp δ₀ - 1 ≤ δ₀ * Real.exp δ₀ := by
      have h := Real.add_one_le_exp (-δ₀)
      have hprod : Real.exp δ₀ * Real.exp (-δ₀) = 1 := by
        rw [← Real.exp_add]
        simp
      nlinarith [Real.exp_pos δ₀]
    have huB : (u:ℝ) ≤ (B':ℝ) := by exact_mod_cast hu
    have hstep : (u:ℝ) * (Real.exp δ₀ - 1)
        ≤ (B':ℝ) * (δ₀ * Real.exp 1) := by
      have h1' : (u:ℝ) * (Real.exp δ₀ - 1)
          ≤ (u:ℝ) * (δ₀ * Real.exp δ₀) := by
        refine mul_le_mul_of_nonneg_left hexp1 hu0.le
      have h2' : (u:ℝ) * (δ₀ * Real.exp δ₀)
          ≤ (B':ℝ) * (δ₀ * Real.exp 1) := by
        have hδe0 : (0:ℝ) ≤ δ₀ * Real.exp δ₀ := by positivity
        have hδe : δ₀ * Real.exp δ₀ ≤ δ₀ * Real.exp 1 :=
          mul_le_mul_of_nonneg_left hexpδe hδ₀.le
        nlinarith [hu0.le, huB, hδe0]
      linarith
    nlinarith [hXle, hstep]
  unfold sharpPartialBudget
  linarith [hdiv, hsumδ, hedge]

/-- **The twist bridge** (Track R, T0-6): from `NonPretentiousAt g A N` at a
top scale `N` — a distance floor for every twist of frequency `|s| ≤ A·N` —
the twisted function `g(n)·n^{−iξ}` satisfies the Halász window at any scale
`4 ≤ u ≤ N` whose band `ξ ± 2π(halaszM u + 1)` fits inside `A·N`, at the
strength `A − 2(loglog N − loglog u + 12)`.  The distance is transferred down
from `N` to `u` by `pretentiousDistSq_le_add_mass` (at most twice the prime
mass in between) and the mass by `mertens_mass_diff_le`.  No constraint ties
`ξ` to `u`. -/
theorem halaszWindowAt_archTwist_of_nonPretentiousAt {g : ℕ → ℂ}
    (hg : ∀ n, ‖g n‖ ≤ 1) {A : ℝ} {N u : ℕ}
    (hNP : NonPretentiousAt g A N) (h1A : 1 ≤ A)
    (hu4 : 4 ≤ u) (huN : u ≤ N) (ξ : ℝ)
    (hrange : |ξ| + 2 * Real.pi * (((halaszM u : ℕ):ℝ) + 1) ≤ A * (N:ℝ))
    (A' : ℝ)
    (hA' : A' ≤ A - 2 * (Real.log (Real.log (N:ℝ)) - Real.log (Real.log (u:ℝ)) + 12)) :
    HalaszWindowAt (fun n => g n * (n:ℂ)^(Complex.I*((-ξ : ℝ):ℂ))) A' u := by
  intro t ht
  rw [pretentiousDistSq_archTwist g 1 1 ξ (2 * Real.pi * t) u]
  have hfreq : |2 * Real.pi * t + ξ| ≤ A * (N:ℝ) := by
    have h1' : |2 * Real.pi * t| = 2 * Real.pi * |t| := by
      rw [abs_mul, abs_of_pos Real.two_pi_pos]
    have h2' : 2 * Real.pi * |t| ≤ 2 * Real.pi * (((halaszM u : ℕ):ℝ) + 1) :=
      mul_le_mul_of_nonneg_left ht Real.two_pi_pos.le
    calc |2 * Real.pi * t + ξ| ≤ |2 * Real.pi * t| + |ξ| := abs_add_le _ _
      _ ≤ A * (N:ℝ) := by rw [h1']; linarith
  have htop := hNP 1 1 (2 * Real.pi * t + ξ) (by exact_mod_cast h1A) hfreq
  have htrans := pretentiousDistSq_le_add_mass g
    (charTwist 1 1 (2 * Real.pi * t + ξ)) hg
    (fun p => charTwist_norm_le_one 1 1 _ p) huN
  have hmert := mertens_mass_diff_le u N hu4 huN
  linarith

open Real Finset in
/-- **The sharp twisted Halász bound on a Dirichlet block, windowed**
(Track R, T0-6): for `g` completely multiplicative, `1`-bounded, and any
frequency `t` such that the twisted function `g(n)·n^{−2πit}` satisfies the
Halász window at strength `D ≥ 1` at every scale of `[a, 3b]`
(`10¹⁶ ≤ a < b`),

  `‖∑_{a<n≤b} g(n)·n⁻¹·e(−t·log n)‖ ≤ sharpTwistedDirichletCost D δ₀ a b`.

The window hypothesis is supplied from a top-scale `NonPretentiousAt` by
`halaszWindowAt_archTwist_of_nonPretentiousAt`; unlike
`sharp_halasz_twisted_dirichlet_block`, no condition `|2πt| ≤ (D/2)·a` ties the
frequency to the block. -/
theorem sharp_halasz_twisted_dirichlet_block_window
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg1 : g 1 = 1)
    (hgb : ∀ n, ‖g n‖ ≤ 1)
    (a b : ℕ) (hxa : 10^16 ≤ a) (hab : a < b)
    (D : ℝ) (hD : 1 ≤ D) (t : ℝ)
    (hwin : ∀ u : ℕ, a ≤ u → u ≤ 3 * b →
      HalaszWindowAt (fun n => g n * (n:ℂ)^(Complex.I*((-(2 * Real.pi * t) : ℝ):ℂ))) D u)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₁ : δ₀ ≤ 1) :
    ‖∑ n ∈ Finset.Ioc a b, (g n / (n : ℂ)) *
        ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
      ≤ sharpTwistedDirichletCost D δ₀ a b := by
  classical
  let h : ℕ → ℂ := fun n =>
    g n * (n:ℂ)^(Complex.I*((-(2 * Real.pi * t) : ℝ):ℂ))
  have hcmh : CompletelyMultiplicativeC h :=
    hcm.mul (completelyMultiplicativeC_natCast_cpow _)
  have h1h : h 1 = 1 := by
    show g 1 * ((1:ℕ):ℂ)^(Complex.I*((-(2 * Real.pi * t) : ℝ):ℂ)) = 1
    rw [hg1, Nat.cast_one, Complex.one_cpow, mul_one]
  have hbh : ∀ n, ‖h n‖ ≤ 1 := by
    intro n
    show ‖g n * ((n:ℕ):ℂ)^(Complex.I*((-(2 * Real.pi * t) : ℝ):ℂ))‖ ≤ 1
    rw [norm_mul]
    calc ‖g n‖ * ‖((n:ℕ):ℂ)^(Complex.I*((-(2 * Real.pi * t) : ℝ):ℂ))‖
        ≤ 1 * 1 := mul_le_mul (hgb n) (norm_natCast_cpow_I_mul_le_one _ _)
          (norm_nonneg _) zero_le_one
      _ = 1 := mul_one 1
  have hpre := prefix_le_sharpPartialBudget_window h hbh hcmh h1h a b hxa hab.le
    D hD δ₀ hδ₀ hδ₁ hwin
  have ha1 : 1 ≤ a + 1 := Nat.succ_pos _
  have hab1 : a + 1 ≤ b := by omega
  have hpartial : ∀ u : ℕ, a + 1 ≤ u → u ≤ b →
      ‖∑ n ∈ Finset.Icc (a + 1) u, h n‖
        ≤ 2 * sharpPartialBudget D δ₀ a b := by
    intro u hau hub
    have hset : Finset.Icc (a + 1) u = Finset.Ioc a u := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hset]
    exact norm_sum_Ioc_le_two_prefix h a u (by omega) _
      (hpre a le_rfl hab.le) (hpre u (by omega) hub)
  have habSum := norm_sum_div_le_of_partial h (a + 1) b ha1 hab1
    (2 * sharpPartialBudget D δ₀ a b) hpartial
  have hrewrite : ∑ n ∈ Finset.Ioc a b,
      (g n / (n : ℂ)) *
        ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ) =
      ∑ n ∈ Finset.Icc (a + 1) b, h n / (n : ℂ) := by
    rw [show Finset.Ioc a b = Finset.Icc (a + 1) b by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    rw [archTwist_phase_eq t n hn0]
    dsimp [h]
    ring
  rw [hrewrite]
  unfold sharpTwistedDirichletCost
  exact habSum

end MoltResearch
