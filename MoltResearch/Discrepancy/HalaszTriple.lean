import MoltResearch.Discrepancy.PlancherelHarness
import MoltResearch.Discrepancy.MultiplicativeC

/-!
# Track C: the Halász triple convolution, frequency side (Track R, M0R)

The log-free Halász route (GHS, "A more intuitive proof of a sharp
version of Halász's theorem"): the Riesz triple convolution of
`SmoothRankin` is paired against the exact Riesz window, with the inner
index extended from `Icc 1 x` to a countable family so that the phase
polynomial becomes the truncated Euler product `F_x` rather than a
partial sum.  This module holds the frequency-side bricks.

`tsum_translates_eq_integral_char` is the countable-family form of the
character-pairing identity `sum_translates_eq_integral_char'`: for an
absolutely summable weight family and a bounded window with Fourier
inversion,

  `∑'ₙ wₙ·F(y − sₙ) = ∫_ℝ e(ξy)·(∑'ₙ wₙ·e(−sₙξ))·𝓕F(ξ) dξ`.

The point of the extension: on the time side the extra terms are killed
by the window's support, so the identity is free — but on the frequency
side the phase sum becomes an *infinite* Dirichlet series, which for a
completely multiplicative weight family factors as an Euler product.
That factorisation is what the smooth-restriction route (`bandSup_*`,
`rankin_*`) paid a three-scale loss to approximate, and here costs
nothing.
-/

namespace MoltResearch

namespace ExpSums

open Real MeasureTheory Filter
open scoped FourierTransform

/-- **The translate sum as a character pairing, countable family**
(Track R, M0R-1):

  `∑'ₙ wₙ·F(y − sₙ) = ∫_ℝ e(ξy)·(∑'ₙ wₙ·e(−sₙξ))·𝓕F(ξ) dξ`

for absolutely summable weights `w` and a bounded continuous integrable
window `F` with integrable transform.

The finite-family identity is `sum_translates_eq_integral_char'`; this
is its limit along `Finset.range`.  The left side converges because the
window is bounded; the right side converges by dominated convergence,
with dominating function `(∑'‖wₙ‖)·‖𝓕F‖` — the phase factors are
unimodular, so the partial phase sums are uniformly bounded by the
total weight mass. -/
theorem tsum_translates_eq_integral_char (F : ℝ → ℂ)
    (hFcont : Continuous F) (hFi : Integrable F) (hFFi : Integrable (𝓕 F))
    (C : ℝ) (hFC : ∀ v, ‖F v‖ ≤ C)
    (w : ℕ → ℂ) (s : ℕ → ℝ) (hw : Summable (fun n => ‖w n‖)) (y : ℝ) :
    ∑' n : ℕ, w n * F (y - s n)
      = ∫ ξ, (𝐞 (ξ * y) : Circle)
          • ((∑' n : ℕ, w n * ((𝐞 (-(s n * ξ)) : Circle) : ℂ)) * 𝓕 F ξ) := by
  classical
  -- the translate sum converges absolutely: the window is bounded
  have hsum1 : Summable (fun n => w n * F (y - s n)) := by
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) (hw.mul_right C)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hFC _) (norm_nonneg _)
  -- the phase sum converges absolutely at every frequency
  have hphase : ∀ ξ : ℝ,
      Summable (fun n => w n * ((𝐞 (-(s n * ξ)) : Circle) : ℂ)) := by
    intro ξ
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) hw
    rw [norm_mul, norm_eq_of_mem_sphere]
    simp
  -- the transform is continuous, being the transform of an `L¹` window
  have hcontF : Continuous (𝓕 F) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by fun_prop) hFi
  -- partial phase sums are continuous in the frequency
  have hpc : ∀ k : ℕ, Continuous fun ξ : ℝ =>
      ∑ n ∈ Finset.range k, w n * ((𝐞 (-(s n * ξ)) : Circle) : ℂ) := by
    intro k
    refine continuous_finset_sum _ fun n _ => ?_
    refine continuous_const.mul ?_
    exact Continuous.comp continuous_subtype_val
      (Real.continuous_fourierChar.comp (by fun_prop))
  -- and uniformly bounded by the total weight mass
  have hpoly : ∀ (k : ℕ) (ξ : ℝ),
      ‖∑ n ∈ Finset.range k, w n * ((𝐞 (-(s n * ξ)) : Circle) : ℂ)‖
        ≤ ∑' n : ℕ, ‖w n‖ := by
    intro k ξ
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun n _ => ?_)
      (hw.sum_le_tsum (Finset.range k) fun n _ => norm_nonneg _)
    rw [norm_mul, norm_eq_of_mem_sphere]
    simp
  -- the left side is the limit of the partial translate sums
  have hL : Tendsto (fun k => ∑ n ∈ Finset.range k, w n * F (y - s n))
      atTop (nhds (∑' n : ℕ, w n * F (y - s n))) :=
    hsum1.hasSum.tendsto_sum_nat
  -- the right side is the limit of the partial pairings, by domination
  have hR : Tendsto (fun k => ∫ ξ,
        ((𝐞 (ξ * y) : Circle) : ℂ)
          * ((∑ n ∈ Finset.range k, w n * ((𝐞 (-(s n * ξ)) : Circle) : ℂ))
            * 𝓕 F ξ))
      atTop (nhds (∫ ξ, ((𝐞 (ξ * y) : Circle) : ℂ)
          * ((∑' n : ℕ, w n * ((𝐞 (-(s n * ξ)) : Circle) : ℂ))
            * 𝓕 F ξ))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun ξ => (∑' n : ℕ, ‖w n‖) * ‖𝓕 F ξ‖) (fun k => ?_)
      (hFFi.norm.const_mul _) (fun k => ?_) ?_
    · -- measurability of each partial pairing
      refine Continuous.aestronglyMeasurable ?_
      refine Continuous.mul ?_ ((hpc k).mul hcontF)
      exact Continuous.comp continuous_subtype_val
        (Real.continuous_fourierChar.comp (by fun_prop))
    · -- the uniform domination
      refine Eventually.of_forall fun ξ => ?_
      rw [norm_mul, norm_mul, norm_eq_of_mem_sphere, one_mul]
      exact mul_le_mul_of_nonneg_right (hpoly k ξ) (norm_nonneg _)
    · -- pointwise convergence of the integrands
      refine Eventually.of_forall fun ξ => ?_
      exact (((hphase ξ).hasSum.tendsto_sum_nat).mul_const
        (𝓕 F ξ)).const_mul _
  -- identify the two limits through the finite-family identity
  have hid : ∀ k : ℕ,
      ∑ n ∈ Finset.range k, w n * F (y - s n)
        = ∫ ξ, ((𝐞 (ξ * y) : Circle) : ℂ)
            * ((∑ n ∈ Finset.range k,
                w n * ((𝐞 (-(s n * ξ)) : Circle) : ℂ)) * 𝓕 F ξ) := by
    intro k
    rw [sum_translates_eq_integral_char' F hFcont hFi hFFi
      (Finset.range k) w s y]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [Circle.smul_def, smul_eq_mul]
  have hgoal : ∑' n : ℕ, w n * F (y - s n)
      = ∫ ξ, ((𝐞 (ξ * y) : Circle) : ℂ)
          * ((∑' n : ℕ, w n * ((𝐞 (-(s n * ξ)) : Circle) : ℂ)) * 𝓕 F ξ) :=
    tendsto_nhds_unique (hL.congr fun k => hid k) hR
  rw [hgoal]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [Circle.smul_def, smul_eq_mul]

/-- **The phase-twisted Dirichlet weight, bundled** (Track R, M0R-2):
for a completely multiplicative `f`, the family

  `n ↦ f(n)·n⁻¹·e(−ξ·log n)`

is multiplicative as a map of monoids `ℕ →* ℂ`.  The value at `0` is
`0` because `(0 : ℂ)⁻¹ = 0`, so no case split is needed in the
definition; multiplicativity at `0` is `0 = 0`.

This is the weight family whose sum over `x`-smooth numbers is the
truncated Euler product `F_x(1 + 2πiξ)` — the object §4 of the GHS
argument takes a supremum of.  Bundling it is what Mathlib's
`EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric`
consumes. -/
noncomputable def phaseHom (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1) (ξ : ℝ) : ℕ →* ℂ where
  toFun n := f n * ((n : ℕ) : ℂ)⁻¹ * ((𝐞 (-(Real.log n * ξ)) : Circle) : ℂ)
  map_one' := by
    simp [h1]
  map_mul' m n := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    have hm0 : ((m : ℕ) : ℝ) ≠ 0 := by positivity
    have hn0 : ((n : ℕ) : ℝ) ≠ 0 := by positivity
    have hlog : Real.log ((m * n : ℕ) : ℝ)
        = Real.log ((m : ℕ) : ℝ) + Real.log ((n : ℕ) : ℝ) := by
      push_cast
      exact Real.log_mul hm0 hn0
    have hchar : ((𝐞 (-(Real.log ((m * n : ℕ) : ℝ) * ξ)) : Circle) : ℂ)
        = ((𝐞 (-(Real.log ((m : ℕ) : ℝ) * ξ)) : Circle) : ℂ)
          * ((𝐞 (-(Real.log ((n : ℕ) : ℝ) * ξ)) : Circle) : ℂ) := by
      rw [show -(Real.log ((m * n : ℕ) : ℝ) * ξ)
          = -(Real.log ((m : ℕ) : ℝ) * ξ) + -(Real.log ((n : ℕ) : ℝ) * ξ) by
        rw [hlog]; ring]
      rw [AddChar.map_add_eq_mul]
      simp
    have hf : f (m * n) = f m * f n := hcm m n (by omega) (by omega)
    have hcast : ((m * n : ℕ) : ℂ)⁻¹ = ((m : ℕ) : ℂ)⁻¹ * ((n : ℕ) : ℂ)⁻¹ := by
      push_cast
      rw [mul_inv]
    rw [hf, hcast, hchar]
    ring

/-- **The phase weight is small at every prime** (Track R, M0R-2):
`‖f(p)·p⁻¹·e(−ξ·log p)‖ ≤ 1/p < 1` — the hypothesis of the geometric
Euler product. -/
theorem norm_phaseHom_prime_lt_one (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (hb : ∀ n, ‖f n‖ ≤ 1) (ξ : ℝ) {p : ℕ} (hp : p.Prime) :
    ‖phaseHom f hcm h1 ξ p‖ < 1 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hval : ‖phaseHom f hcm h1 ξ p‖
      = ‖f p‖ * ((p : ℝ))⁻¹ := by
    show ‖f p * ((p : ℕ) : ℂ)⁻¹ * ((𝐞 (-(Real.log p * ξ)) : Circle) : ℂ)‖
      = ‖f p‖ * ((p : ℝ))⁻¹
    rw [norm_mul, norm_mul, norm_eq_of_mem_sphere, mul_one, norm_inv,
      Complex.norm_natCast]
  rw [hval]
  calc ‖f p‖ * ((p : ℝ))⁻¹ ≤ 1 * ((p : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right (hb p) (by positivity)
    _ = ((p : ℝ))⁻¹ := one_mul _
    _ < 1 := by
        rw [inv_lt_one_iff₀]
        right
        linarith

/-- **The smooth phase sum is absolutely summable** (Track R, M0R-2):
over the `x`-smooth numbers, `∑ ‖f(n)·n⁻¹·e(−ξ·log n)‖` converges — the
weight at a prime has norm at most `1/p < 1`, which is all the geometric
Euler-product machinery asks. -/
theorem summable_norm_smooth_phase (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (hb : ∀ n, ‖f n‖ ≤ 1) (x : ℕ) (ξ : ℝ) :
    Summable (fun m : (Nat.smoothNumbers x) =>
      ‖f m * ((m : ℕ) : ℂ)⁻¹ * ((𝐞 (-(Real.log m * ξ)) : Circle) : ℂ)‖) :=
  (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := phaseHom f hcm h1 ξ)
    (norm_phaseHom_prime_lt_one f hcm h1 hb ξ) x).1

/-- **The smooth phase sum is the truncated Euler product** (Track R,
M0R-2):

  `∑_{n x-smooth} f(n)·n⁻¹·e(−ξ·log n)
     = ∏_{p < x} (1 − f(p)·p⁻¹·e(−ξ·log p))⁻¹`.

This is the identity that replaces the smooth-restriction detour: the
phase polynomial that the triple-convolution pairing produces *is*
`F_x(1 + 2πiξ)`, exactly, with no Rankin term and no second scale. -/
theorem hasSum_smooth_phase_prod (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (hb : ∀ n, ‖f n‖ ≤ 1) (x : ℕ) (ξ : ℝ) :
    HasSum (fun m : (Nat.smoothNumbers x) =>
        f m * ((m : ℕ) : ℂ)⁻¹ * ((𝐞 (-(Real.log m * ξ)) : Circle) : ℂ))
      (∏ p ∈ x.primesBelow,
        (1 - f p * ((p : ℕ) : ℂ)⁻¹
            * ((𝐞 (-(Real.log p * ξ)) : Circle) : ℂ))⁻¹) :=
  (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := phaseHom f hcm h1 ξ)
    (norm_phaseHom_prime_lt_one f hcm h1 hb ξ) x).2

/-- **The Euler factor, priced by its real part** (Track R, M0R-3):
for `‖z‖ ≤ 1/2`,

  `‖(1 − z)⁻¹‖ ≤ exp(Re z + 2‖z‖²)`.

The factor-level input to the band bound: taking the product over
`p < x` at `z = f(p)·p⁻¹·e(−ξ·log p)` turns the truncated Euler product
into `exp(∑_p Re(f(p)e(−ξ·log p))/p + 2∑_p 1/p²)`, whose exponent is
the prime mass minus the pretentious distance.

The proof runs on squares.  The core is the one-variable inequality
`e^{−(u+2u²)} ≤ 1 − u` for `u = Re z ∈ [−1/2, 1/2]`, which needs no
sign split: `(1−u)(1+u+2u²) = 1 + u²(1−2u) ≥ 1`, and `1+x ≤ eˣ` does
the rest.  Squaring and using `Re² ≤ ‖·‖²` twice gives
`e^{−2(u+2‖z‖²)} ≤ 1 − 2u + ‖z‖² = ‖1−z‖²`. -/
theorem norm_one_sub_inv_le_exp {z : ℂ} (hz : ‖z‖ ≤ 1/2) :
    ‖(1 - z)⁻¹‖ ≤ Real.exp (z.re + 2*‖z‖^2) := by
  set u : ℝ := z.re with hu_def
  set v : ℝ := ‖z‖^2 with hv_def
  have hu2v : u^2 ≤ v := by
    have h1 := Complex.abs_re_le_norm z
    have h3 : |z.re|^2 ≤ ‖z‖^2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs] at h3
    exact h3
  have huhalf : |u| ≤ 1/2 := le_trans (Complex.abs_re_le_norm z) hz
  have hub := abs_le.mp huhalf
  -- the one-variable core: `e^{−(u+2u²)} ≤ 1 − u`
  have hcore : Real.exp (-(u + 2*u^2)) ≤ 1 - u := by
    have hx : 1 + (u + 2*u^2) ≤ Real.exp (u + 2*u^2) := by
      linarith [Real.add_one_le_exp (u + 2*u^2)]
    have h1u : (0:ℝ) ≤ 1 - u := by linarith [hub.2]
    have hprod : (1:ℝ) ≤ (1 - u) * (1 + (u + 2*u^2)) := by nlinarith [hub.2]
    have h1 : (1:ℝ) ≤ (1 - u) * Real.exp (u + 2*u^2) :=
      le_trans hprod (mul_le_mul_of_nonneg_left hx h1u)
    have h2 := mul_le_mul_of_nonneg_right h1
      (Real.exp_pos (-(u + 2*u^2))).le
    rw [one_mul, mul_assoc, ← Real.exp_add,
      show (u + 2*u^2) + -(u + 2*u^2) = 0 by ring,
      Real.exp_zero, mul_one] at h2
    exact h2
  -- the squared form, with `u² ≤ v` feeding both slots
  have hnormsq : ‖(1:ℂ) - z‖^2 = 1 - 2*u + v := by
    rw [hu_def, hv_def, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]
    ring
  have hsq : Real.exp (-(u + 2*v))^2 ≤ ‖(1:ℂ) - z‖^2 := by
    calc Real.exp (-(u + 2*v))^2
        = Real.exp (-(u + 2*v) + -(u + 2*v)) := by
          rw [pow_two (Real.exp (-(u + 2*v))), ← Real.exp_add]
      _ ≤ Real.exp (-(u + 2*u^2) + -(u + 2*u^2)) := by
          refine Real.exp_le_exp.mpr ?_
          linarith [hu2v]
      _ = Real.exp (-(u + 2*u^2))^2 := by
          rw [pow_two (Real.exp (-(u + 2*u^2))), ← Real.exp_add]
      _ ≤ (1 - u)^2 :=
          pow_le_pow_left₀ (Real.exp_pos _).le hcore 2
      _ = 1 - 2*u + u^2 := by ring
      _ ≤ 1 - 2*u + v := by linarith [hu2v]
      _ = ‖(1:ℂ) - z‖^2 := hnormsq.symm
  -- undo the squares and invert
  have hZ : Real.exp (-(u + 2*v)) ≤ ‖(1:ℂ) - z‖ := by
    calc Real.exp (-(u + 2*v))
        = Real.sqrt (Real.exp (-(u + 2*v))^2) :=
          (Real.sqrt_sq (Real.exp_pos _).le).symm
      _ ≤ Real.sqrt (‖(1:ℂ) - z‖^2) := Real.sqrt_le_sqrt hsq
      _ = ‖(1:ℂ) - z‖ := Real.sqrt_sq (norm_nonneg _)
  rw [norm_inv]
  have h3 : 1/‖(1:ℂ) - z‖ ≤ 1/Real.exp (-(u + 2*v)) :=
    one_div_le_one_div_of_le (Real.exp_pos _) hZ
  rw [one_div, one_div, Real.exp_neg, inv_inv] at h3
  exact h3

end ExpSums

end MoltResearch
