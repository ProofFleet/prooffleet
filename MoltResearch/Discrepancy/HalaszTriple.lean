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

end ExpSums

end MoltResearch
