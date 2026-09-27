import MoltResearch.Discrepancy.PlancherelHarness
import MoltResearch.Discrepancy.MultiplicativeC
import MoltResearch.Discrepancy.BrunTitchmarsh
import MoltResearch.Discrepancy.PretentiousDist
import MoltResearch.Discrepancy.PrimeSumBounds

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
    rw [norm_mul, Circle.norm_coe]
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
    rw [norm_mul, Circle.norm_coe]
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
      rw [norm_mul, norm_mul, Circle.norm_coe, one_mul]
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
    rw [norm_mul, norm_mul, Circle.norm_coe, mul_one, norm_inv,
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

/-- **The truncated Euler product, priced by the prime phase mass**
(Track R, M0R-3b):

  `‖∏_{p<x} (1 − f(p)p⁻¹e(−ξ·log p))⁻¹‖
     ≤ exp(∑_{p<x} Re(f(p)e(−ξ·log p))/p + 2)`.

`norm_one_sub_inv_le_exp` at every factor — `‖z_p‖ ≤ 1/p ≤ 1/2` — and
the quadratic overhead is absolute: `2∑_p 1/p² ≤ 2∑_{m≥2} 1/m² ≤ 2`.

The exponent is `mass − 𝔻²`: adding and subtracting `∑ 1/p` writes it
as the prime mass minus the squared pretentious distance to the
archimedean twist `e(ξ·log ·)`, which is how `NonPretentiousAt` prices
the band sup of `F_x` at a single scale. -/
theorem norm_phase_euler_prod_le (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1)
    (x : ℕ) (ξ : ℝ) :
    ‖∏ p ∈ x.primesBelow,
        (1 - f p * ((p : ℕ) : ℂ)⁻¹
            * ((𝐞 (-(Real.log p * ξ)) : Circle) : ℂ))⁻¹‖
      ≤ Real.exp ((∑ p ∈ x.primesBelow,
          (f p * ((𝐞 (-(Real.log p * ξ)) : Circle) : ℂ)).re / (p : ℝ)) + 2) := by
  classical
  rw [norm_prod]
  -- the factor bound, with the weight split off the phase
  have hfac : ∀ p ∈ x.primesBelow,
      ‖(1 - f p * ((p : ℕ) : ℂ)⁻¹
          * ((𝐞 (-(Real.log p * ξ)) : Circle) : ℂ))⁻¹‖
        ≤ Real.exp ((f p * ((𝐞 (-(Real.log p * ξ)) : Circle) : ℂ)).re / (p : ℝ)
            + 2 * (1/((p : ℝ))^2)) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primesBelow hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    set z : ℂ := f p * ((p : ℕ) : ℂ)⁻¹
        * ((𝐞 (-(Real.log p * ξ)) : Circle) : ℂ) with hz_def
    have hznorm : ‖z‖ ≤ 1/(p : ℝ) := by
      rw [hz_def, norm_mul, norm_mul, Circle.norm_coe, mul_one,
        norm_inv, Complex.norm_natCast, ← one_div]
      calc ‖f p‖ * (1/(p : ℝ))
          ≤ 1 * (1/(p : ℝ)) :=
            mul_le_mul_of_nonneg_right (hb p) (by positivity)
        _ = 1/(p : ℝ) := one_mul _
    have hzhalf : ‖z‖ ≤ 1/2 :=
      le_trans hznorm (one_div_le_one_div_of_le (by norm_num) hp2)
    refine le_trans (norm_one_sub_inv_le_exp hzhalf) ?_
    refine Real.exp_le_exp.mpr ?_
    have hre : z.re = (f p * ((𝐞 (-(Real.log p * ξ)) : Circle) : ℂ)).re
        / (p : ℝ) := by
      have hswap : z = (f p * ((𝐞 (-(Real.log p * ξ)) : Circle) : ℂ))
          * ((((p : ℝ))⁻¹ : ℝ) : ℂ) := by
        rw [hz_def]
        push_cast
        ring
      rw [hswap, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, div_eq_mul_inv]
    have hsq : ‖z‖^2 ≤ 1/((p : ℝ))^2 := by
      have h1 := pow_le_pow_left₀ (norm_nonneg z) hznorm 2
      calc ‖z‖^2 ≤ (1/(p : ℝ))^2 := h1
        _ = 1/((p : ℝ))^2 := by ring
    linarith [hre.le, hre.ge]
  refine le_trans (Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) hfac) ?_
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.mpr ?_
  rw [Finset.sum_add_distrib]
  -- the quadratic overhead is at most `2`, from the telescoping bound
  have htail : ∑ p ∈ x.primesBelow, 2 * (1/((p : ℝ))^2) ≤ 2 := by
    have hsub : x.primesBelow ⊆ Finset.Icc 2 x := by
      intro p hp
      rw [Nat.mem_primesBelow] at hp
      rw [Finset.mem_Icc]
      exact ⟨hp.2.two_le, by omega⟩
    have h1 : ∑ p ∈ x.primesBelow, (1 : ℝ)/((p : ℝ))^2
        ≤ ∑ m ∈ Finset.Icc 2 x, (1 : ℝ)/((m : ℝ))^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun m _ _ => by positivity)
    have h2 : ∑ m ∈ Finset.Icc 2 x, (1 : ℝ)/((m : ℝ))^2 ≤ 1 := by
      rcases Nat.lt_or_ge x 2 with hx2 | hx2
      · rw [Finset.Icc_eq_empty_of_lt hx2, Finset.sum_empty]
        norm_num
      · have hsplit : Finset.Icc 1 x = insert 1 (Finset.Icc 2 x) := by
          ext m
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        have hbig := MoltResearch.sum_one_div_sq_Icc_le_two x
        rw [hsplit, Finset.sum_insert (by
          rw [Finset.mem_Icc]
          omega)] at hbig
        have hone : (1 : ℝ)/((1 : ℕ) : ℝ)^2 = 1 := by norm_num
        have hcongr : ∑ m ∈ Finset.Icc 2 x, (1 : ℝ)/((m : ℝ))^2
            = ∑ m ∈ Finset.Icc 2 x, (1 : ℝ)/((m : ℝ)^2) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          ring
        rw [hcongr]
        push_cast at hbig
        linarith
    calc ∑ p ∈ x.primesBelow, 2 * (1/((p : ℝ))^2)
        = 2 * ∑ p ∈ x.primesBelow, (1 : ℝ)/((p : ℝ))^2 := by
          rw [Finset.mul_sum]
      _ ≤ 2 * 1 := by linarith
      _ = 2 := mul_one 2
  linarith

/-- **The phase mass is the prime mass minus the pretentious distance**
(Track R, M0R-3c):

  `∑_{p<x} Re(f(p)e(−ξ·log p))/p
     = ∑_{p<x} 1/p − 𝔻(f, n^{i·2πξ}; x)²`,

with the comparison point written as the level-one character twist —
the exact shape `NonPretentiousAt` quantifies over at `q = 1`.

Per prime, `conj(charTwist 1 χ (2πξ) p) = e(−ξ·log p)`: the character
factor is `1` (level one is a subsingleton), and conjugating
`p^{i·2πξ}` flips the phase.  So the summand of `pretentiousDistSq` is
`(1 − Re(f(p)e(−ξ·log p)))/p`, and the sum telescopes against the
mass. -/
theorem sum_re_phase_eq_mass_sub_distSq (f : ℕ → ℂ) (x : ℕ) (ξ : ℝ)
    (χ : DirichletCharacter ℂ 1) :
    ∑ p ∈ x.primesBelow,
        (f p * ((𝐞 (-(Real.log p * ξ)) : Circle) : ℂ)).re / (p : ℝ)
      = (∑ p ∈ x.primesBelow, (1 : ℝ)/(p : ℝ))
        - pretentiousDistSq f (charTwist 1 χ (2*Real.pi*ξ)) x := by
  classical
  rw [pretentiousDistSq, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpp := Nat.prime_of_mem_primesBelow hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
  have hpc0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  -- the conjugated twist is the phase factor
  have hkey : (starRingEnd ℂ) (charTwist 1 χ (2*Real.pi*ξ) p)
      = ((𝐞 (-(Real.log p * ξ)) : Circle) : ℂ) := by
    rw [charTwist]
    have hχ : χ ((p : ℕ) : ZMod 1) = 1 := by
      rw [Subsingleton.elim χ 1]
      exact MulChar.one_apply (isUnit_of_subsingleton _)
    rw [hχ, one_mul]
    have hlog : Complex.log ((p : ℕ) : ℂ) = ((Real.log p : ℝ) : ℂ) := by
      rw [show ((p : ℕ) : ℂ) = (((p : ℝ) : ℝ) : ℂ) by push_cast; rfl]
      exact (Complex.ofReal_log hp0.le).symm
    rw [Complex.cpow_def_of_ne_zero hpc0, ← Complex.exp_conj]
    rw [Real.fourierChar_apply]
    congr 1
    rw [map_mul, hlog, Complex.conj_ofReal, map_mul, Complex.conj_I,
      Complex.conj_ofReal]
    push_cast
    ring
  rw [hkey]
  ring

/-- **The zeta weight, bundled** (Track R, M0R-3c): the family
`n ↦ n^{−(1+1/log x)}` as a map of monoids `ℕ →* ℝ` — `rpow` is
multiplicative on nonnegative reals, and the value at `0` is `0`
because the exponent is nonzero. -/
noncomputable def zetaAbscissaHom (x : ℕ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-(1 + 1/Real.log x))
  map_one' := by
    rw [Nat.cast_one, Real.one_rpow]
  map_mul' m n := by
    push_cast
    exact Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)

/-- **The partial zeta Euler product is at most the zeta mass**
(Track R, M0R-3c):

  `∏_{p<x} (1 − p^{−(1+1/log x)})⁻¹ ≤ 2 + log x`.

The geometric Euler product over the `x`-smooth numbers evaluates the
product as `∑_{n x-smooth} n^{−σ}`, which is at most the full zeta mass
`tsum_one_div_rpow_le_two_add_log` prices. -/
theorem prod_one_sub_rpow_inv_le (x : ℕ) (hx : 3 ≤ x) :
    ∏ p ∈ x.primesBelow, (1 - (p : ℝ) ^ (-(1 + 1/Real.log x)))⁻¹
      ≤ 2 + Real.log x := by
  classical
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hlog1 : (1 : ℝ) < Real.log x := by
    have he : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) he
      _ ≤ Real.log x := Real.log_le_log (by norm_num) hxR
  have hσ1 : (1 : ℝ) < 1 + 1/Real.log x := by
    have : (0 : ℝ) < 1/Real.log x := by positivity
    linarith
  -- the prime weights are strictly inside the unit ball
  have hprime : ∀ {p : ℕ}, p.Prime → ‖zetaAbscissaHom x p‖ < 1 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
    have hmono : (p : ℝ) ^ (1:ℝ) ≤ (p : ℝ) ^ (1 + 1/Real.log x) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    have hpσ : (2 : ℝ) ≤ (p : ℝ) ^ (1 + 1/Real.log x) := by
      rw [Real.rpow_one] at hmono
      linarith
    show |(p : ℝ) ^ (-(1 + 1/Real.log x))| < 1
    rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
      Real.rpow_neg (by positivity)]
    have hh : 1/((p : ℝ) ^ (1 + 1/Real.log x)) ≤ 1/2 :=
      one_div_le_one_div_of_le (by norm_num) hpσ
    rw [one_div] at hh
    exact lt_of_le_of_lt hh (by norm_num)
  obtain ⟨hsummable, hhassum⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      (f := zetaAbscissaHom x) hprime x
  -- the product is the smooth zeta sum
  have hval : ∏ p ∈ x.primesBelow, (1 - (p : ℝ) ^ (-(1 + 1/Real.log x)))⁻¹
      = ∑' m : x.smoothNumbers, ((m : ℕ) : ℝ) ^ (-(1 + 1/Real.log x)) :=
    hhassum.tsum_eq.symm
  rw [hval]
  -- and the smooth sum is at most the full one
  have hfull : Summable (fun n : ℕ => 1/(n : ℝ) ^ (1 + 1/Real.log x)) :=
    Real.summable_one_div_nat_rpow.mpr hσ1
  have hform : ∀ n : ℕ, (n : ℝ) ^ (-(1 + 1/Real.log x))
      = 1/(n : ℝ) ^ (1 + 1/Real.log x) := by
    intro n
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
    exact (one_div _).symm
  have hind : ∀ n : ℕ,
      (Nat.smoothNumbers x).indicator
        (fun n : ℕ => (n : ℝ) ^ (-(1 + 1/Real.log x))) n
        ≤ 1/(n : ℝ) ^ (1 + 1/Real.log x) := by
    intro n
    refine le_trans (Set.indicator_le_self' (fun m _ =>
      Real.rpow_nonneg (Nat.cast_nonneg _) _) n) (le_of_eq (hform n))
  have hle : ∑' m : x.smoothNumbers, ((m : ℕ) : ℝ) ^ (-(1 + 1/Real.log x))
      ≤ ∑' n : ℕ, 1/(n : ℝ) ^ (1 + 1/Real.log x) := by
    rw [tsum_subtype (Nat.smoothNumbers x)
      (fun n : ℕ => (n : ℝ) ^ (-(1 + 1/Real.log x)))]
    refine Summable.tsum_le_tsum hind ?_ hfull
    refine Summable.of_nonneg_of_le (fun n => ?_) hind hfull
    exact Set.indicator_nonneg
      (fun m _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) n
  exact le_trans hle (tsum_one_div_rpow_le_two_add_log hxR)

/-- **The prime mass at the shifted abscissa** (Track R, M0R-3c):

  `∑_{p<x} p^{−(1+1/log x)} ≤ log(2 + log x)`.

Exponentiate: `e^{∑} = ∏ e^{p^{−σ}} ≤ ∏ (1−p^{−σ})⁻¹ ≤ 2 + log x`,
the middle step being `eᵘ ≤ (1−u)⁻¹` per factor. -/
theorem sum_rpow_primesBelow_le_log (x : ℕ) (hx : 3 ≤ x) :
    ∑ p ∈ x.primesBelow, (p : ℝ) ^ (-(1 + 1/Real.log x))
      ≤ Real.log (2 + Real.log x) := by
  classical
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hlog1 : (1 : ℝ) < Real.log x := by
    have he : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) he
      _ ≤ Real.log x := Real.log_le_log (by norm_num) hxR
  -- each factor: `eᵘ ≤ (1−u)⁻¹` at `u = p^{−σ} ≤ 1/2`
  have hfac : ∀ p ∈ x.primesBelow,
      Real.exp ((p : ℝ) ^ (-(1 + 1/Real.log x)))
        ≤ (1 - (p : ℝ) ^ (-(1 + 1/Real.log x)))⁻¹ := by
    intro p hp
    have hpp := Nat.prime_of_mem_primesBelow hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    set u : ℝ := (p : ℝ) ^ (-(1 + 1/Real.log x)) with hu_def
    have hu0 : 0 ≤ u := Real.rpow_nonneg (by positivity) _
    have huhalf : u ≤ 1/2 := by
      rw [hu_def, Real.rpow_neg (by positivity)]
      have hmono : (p : ℝ) ^ (1:ℝ) ≤ (p : ℝ) ^ (1 + 1/Real.log x) := by
        refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
        have h5 : (0 : ℝ) < 1/Real.log x := by positivity
        linarith
      rw [Real.rpow_one] at hmono
      have h2σ : (2 : ℝ) ≤ (p : ℝ) ^ (1 + 1/Real.log x) := by linarith
      have hh : 1/((p : ℝ) ^ (1 + 1/Real.log x)) ≤ 1/2 :=
        one_div_le_one_div_of_le (by norm_num) h2σ
      rw [one_div] at hh
      exact hh
    have h1u : (0 : ℝ) < 1 - u := by linarith
    -- `(1−u)·eᵘ ≤ 1` from `1+(−u) ≤ e^{−u}`
    have h2 : (1 - u) * Real.exp u ≤ 1 := by
      have h3 : 1 - u ≤ Real.exp (-u) := by
        linarith [Real.add_one_le_exp (-u)]
      have h4 := mul_le_mul_of_nonneg_right h3 (Real.exp_pos u).le
      rw [← Real.exp_add, show -u + u = 0 by ring, Real.exp_zero] at h4
      exact h4
    rw [inv_eq_one_div, le_div_iff₀ h1u]
    linarith [h2]
  have hexp : Real.exp (∑ p ∈ x.primesBelow,
      (p : ℝ) ^ (-(1 + 1/Real.log x))) ≤ 2 + Real.log x := by
    rw [Real.exp_sum]
    exact le_trans
      (Finset.prod_le_prod₀ (fun p _ => (Real.exp_pos _).le) hfac)
      (prod_one_sub_rpow_inv_le x hx)
  have hlog := Real.log_le_log (Real.exp_pos _) hexp
  rwa [Real.log_exp] at hlog

/-- **The prime mass on the 1-line** (Track R, M0R-3c):

  `∑_{p<x} 1/p ≤ log(2 + log x) + 3`   for `x ≥ 3`.

Split each term against the shifted abscissa:
`1/p − p^{−(1+1/log x)} = (1/p)(1 − e^{−log p/log x}) ≤ (log p/p)/log x`,
so the difference sums to at most `(log x + 2)/log x ≤ 3` by the sharp
Mertens bound, and the shifted mass is `sum_rpow_primesBelow_le_log`.

Leading coefficient exactly `1` — this is what keeps the Halász band
sup at a single power of `log x`, where the crude `4·loglog + 13`
Mertens bound would cost `log⁴x`. -/
theorem sum_one_div_primesBelow_le_log_log (x : ℕ) (hx : 3 ≤ x) :
    ∑ p ∈ x.primesBelow, (1 : ℝ)/(p : ℝ)
      ≤ Real.log (2 + Real.log x) + 3 := by
  classical
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hlog1 : (1 : ℝ) < Real.log x := by
    have he : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) he
      _ ≤ Real.log x := Real.log_le_log (by norm_num) hxR
  -- termwise comparison with the shifted abscissa
  have hsplit : ∀ p ∈ x.primesBelow,
      (1 : ℝ)/(p : ℝ) ≤ (p : ℝ) ^ (-(1 + 1/Real.log x))
        + (Real.log p/(p : ℝ))/Real.log x := by
    intro p hp
    have hpp := Nat.prime_of_mem_primesBelow hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hexp : (p : ℝ) ^ (-(1 + 1/Real.log x))
        = (1/(p : ℝ)) * Real.exp (-(Real.log p/Real.log x)) := by
      rw [Real.rpow_def_of_pos hp0,
        show Real.log (p : ℝ) * -(1 + 1/Real.log x)
          = -Real.log (p : ℝ) + -(Real.log p/Real.log x) by ring,
        Real.exp_add, Real.exp_neg, Real.exp_log hp0, one_div]
    have hbound : 1 - Real.exp (-(Real.log p/Real.log x))
        ≤ Real.log p/Real.log x := by
      linarith [Real.add_one_le_exp (-(Real.log p/Real.log x))]
    have h2 : (1 : ℝ)/(p : ℝ) - (p : ℝ) ^ (-(1 + 1/Real.log x))
        ≤ (Real.log p/(p : ℝ))/Real.log x := by
      rw [hexp,
        show (1 : ℝ)/(p : ℝ) - (1/(p : ℝ))
            * Real.exp (-(Real.log p/Real.log x))
          = (1/(p : ℝ)) * (1 - Real.exp (-(Real.log p/Real.log x)))
          by ring]
      calc (1/(p : ℝ)) * (1 - Real.exp (-(Real.log p/Real.log x)))
          ≤ (1/(p : ℝ)) * (Real.log p/Real.log x) :=
            mul_le_mul_of_nonneg_left hbound (by positivity)
        _ = (Real.log p/(p : ℝ))/Real.log x := by ring
    linarith
  have hsum := Finset.sum_le_sum hsplit
  rw [Finset.sum_add_distrib] at hsum
  have hshift := sum_rpow_primesBelow_le_log x hx
  have hmertens := sum_log_div_primesBelow_le_sharp x (by omega)
  have hdiv : ∑ p ∈ x.primesBelow, (Real.log p/(p : ℝ))/Real.log x
      = (∑ p ∈ x.primesBelow, Real.log p/(p : ℝ))/Real.log x :=
    (Finset.sum_div _ _ _).symm
  have h5 : (∑ p ∈ x.primesBelow, Real.log p/(p : ℝ))/Real.log x ≤ 3 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hmertens]
  rw [hdiv] at hsum
  linarith

/-- **The band sup of the truncated Euler product, under
non-pretentiousness** (Track R, M0R-3d):

  `‖F_x(1 + 2πiξ)‖ ≤ e⁵·(2 + log x)·e^{−A}`,

for any frequency with `|2πξ| ≤ A·x`.  The full M0R-3 chain: the
product is `exp(mass − 𝔻² + 2)` (M0R-3a/b/c-i), the mass is at most
`log(2 + log x) + 3` (M0R-3c-ii/iii), and `NonPretentiousAt` supplies
`𝔻² ≥ A` at the level-one twist.

This is the log-free replacement for the `bandSup_*` smooth-restriction
route: one scale, an absolute constant, and the full strength of the
distance hypothesis — where the three-scale transfer retained only
`A − 2(mass(x) − mass(y₂))` and a Rankin remainder. -/
theorem norm_phase_euler_prod_le_of_nonPretentious (f : ℕ → ℂ)
    (hb : ∀ n, ‖f n‖ ≤ 1) (x : ℕ) (hx : 3 ≤ x)
    (A : ℝ) (h1A : 1 ≤ A) (hA : NonPretentiousAt f A x)
    (ξ : ℝ) (hξ : |2*Real.pi*ξ| ≤ A * x) :
    ‖∏ p ∈ x.primesBelow,
        (1 - f p * ((p : ℕ) : ℂ)⁻¹
            * ((𝐞 (-(Real.log p * ξ)) : Circle) : ℂ))⁻¹‖
      ≤ Real.exp 5 * (2 + Real.log x) * Real.exp (-A) := by
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hlogx : (0 : ℝ) < Real.log x :=
    Real.log_pos (by linarith)
  have hdist := hA 1 1 (2*Real.pi*ξ) (by exact_mod_cast h1A) hξ
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

end ExpSums

end MoltResearch
