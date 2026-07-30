import MoltResearch.Discrepancy.ZeroFreeRegion
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Track C: the Plancherel harness (Track R, campaign #3044, phase C2)

The L² identity at the heart of the "cheap" Matomäki–Radziwiłł frame
(Tao, 254A Supplement 6): for a smooth compactly supported `F` and a
finite family of weighted translates,
`∫ ‖∑ᵢ wᵢ·F(y − sᵢ)‖² dy = ∫ ‖∑ᵢ wᵢ·e(−sᵢξ)‖²·‖𝓕F(ξ)‖² dξ` —
Plancherel plus translation↔modulation, with no measure convolution:
the prime measure `μ = ∑ (1/p)·δ_{log p}` is finitely supported, so its
convolution with `F` is literally this translate sum, and `μ̂` is the
phase sum on the right.

Everything runs in the Schwartz layer: `F` smooth compactly supported
makes the translate sum a Schwartz function, and
`SchwartzMap.integral_norm_sq_fourier` is Plancherel in integral form.
-/

namespace MoltResearch

namespace ExpSums

open Real MeasureTheory SchwartzMap LineDeriv
open scoped FourierTransform ContDiff

/-- Finite sums of compactly supported functions have compact support. -/
theorem hasCompactSupport_finset_sum {ι : Type*} {S : Finset ι}
    {f : ι → ℝ → ℂ} (h : ∀ i ∈ S, HasCompactSupport (f i)) :
    HasCompactSupport (fun y => ∑ i ∈ S, f i y) := by
  classical
  induction S using Finset.cons_induction with
  | empty => simpa using HasCompactSupport.zero
  | cons a T ha ih =>
    have h1 : (fun y => ∑ i ∈ Finset.cons a T ha, f i y)
        = (fun y => f a y + ∑ i ∈ T, f i y) := by
      funext y
      rw [Finset.sum_cons]
    rw [h1]
    exact (h a (Finset.mem_cons_self a T)).add
      (ih fun i hi => h i (Finset.mem_cons_of_mem hi))

/-- **Translation ↦ modulation**: `𝓕(F(· − s))(ξ) = e(−sξ)·𝓕F(ξ)`. -/
theorem fourier_translate (f : ℝ → ℂ) (s : ℝ) (ξ : ℝ) :
    𝓕 (fun y => f (y - s)) ξ = (𝐞 (-(s * ξ)) : Circle) • 𝓕 f ξ := by
  have h := VectorFourier.fourierIntegral_comp_add_right 𝐞
    (volume : Measure ℝ) (innerₗ ℝ) f (-s)
  have h2 : (fun y => f (y - s)) = (f ∘ fun v => v + (-s)) := by
    funext y
    simp [sub_eq_add_neg]
  rw [h2]
  have h3 := congrFun h ξ
  have h4 : ((innerₗ ℝ) (-s)) ξ = -(s * ξ) := by
    have h5 : ((innerₗ ℝ) s) ξ = s * ξ := by
      rw [innerₗ_apply_apply, RCLike.inner_apply]
      simp only [starRingEnd_apply, star_trivial]
      ring
    have h6 : ((innerₗ ℝ) (-s)) ξ = -(((innerₗ ℝ) s) ξ) := by
      rw [map_neg, LinearMap.neg_apply]
    rw [h6, h5]
  rw [h4] at h3
  exact h3

/-- **The Fourier transform of a finite weighted translate sum**:
`𝓕(∑ᵢ wᵢ·F(· − sᵢ))(ξ) = (∑ᵢ wᵢ·e(−sᵢξ))·𝓕F(ξ)`. -/
theorem fourier_sum_translates (F : ℝ → ℂ) (hFc : HasCompactSupport F)
    (hFs : Continuous F) {ι : Type*} (S : Finset ι) (w : ι → ℂ) (s : ι → ℝ)
    (ξ : ℝ) :
    𝓕 (fun y => ∑ i ∈ S, w i * F (y - s i)) ξ
      = (∑ i ∈ S, w i * ((𝐞 (-(s i * ξ)) : Circle) : ℂ)) * 𝓕 F ξ := by
  classical
  have hFi : Integrable F := hFs.integrable_of_hasCompactSupport hFc
  have hint : ∀ i : ι, Integrable (fun y => w i * F (y - s i)) := by
    intro i
    exact ((hFi.comp_sub_right (s i)).const_mul (w i))
  have hunfold : 𝓕 (fun y => ∑ i ∈ S, w i * F (y - s i)) ξ
      = ∫ v, (𝐞 (-((innerₗ ℝ) v ξ)) : Circle)
          • (∑ i ∈ S, w i * F (v - s i)) := rfl
  rw [hunfold]
  have hsplit : ∀ v : ℝ,
      (𝐞 (-((innerₗ ℝ) v ξ)) : Circle) • (∑ i ∈ S, w i * F (v - s i))
        = ∑ i ∈ S, (𝐞 (-((innerₗ ℝ) v ξ)) : Circle)
            • (w i * F (v - s i)) := by
    intro v
    exact Finset.smul_sum
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit)]
  rw [integral_finset_sum]
  · have hterm : ∀ i ∈ S,
        ∫ v, (𝐞 (-((innerₗ ℝ) v ξ)) : Circle) • (w i * F (v - s i))
          = w i * ((𝐞 (-(s i * ξ)) : Circle) : ℂ) * 𝓕 F ξ := by
      intro i _
      have h1 : (∫ v, (𝐞 (-((innerₗ ℝ) v ξ)) : Circle)
            • (w i * F (v - s i)))
          = 𝓕 (fun y => w i * F (y - s i)) ξ := rfl
      rw [h1]
      have h2 : (fun y => w i * F (y - s i))
          = w i • (fun y => F (y - s i)) := by
        funext y
        simp [smul_eq_mul]
      rw [h2]
      have h3 := congrFun (VectorFourier.fourierIntegral_const_smul 𝐞
        (volume : Measure ℝ) (innerₗ ℝ) (fun y => F (y - s i)) (w i)) ξ
      rw [show (𝓕 (w i • fun y => F (y - s i)) ξ)
          = VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ)
              (w i • fun y => F (y - s i)) ξ from rfl]
      rw [h3, Pi.smul_apply]
      have h4 := fourier_translate F (s i) ξ
      rw [show VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ)
            (fun y => F (y - s i)) ξ = 𝓕 (fun y => F (y - s i)) ξ from rfl,
        h4]
      simp only [Circle.smul_def, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_mul]
  · intro i _
    have hL : Continuous fun p : ℝ × ℝ => ((innerₗ ℝ) p.1) p.2 :=
      continuous_inner
    exact (VectorFourier.fourierIntegral_convergent_iff
      (Real.continuous_fourierChar) hL ξ).2 (hint i)

/-- **The Plancherel harness** (C2-ii): for smooth compactly supported `F`,
`∫ ‖∑ᵢ wᵢ·F(y − sᵢ)‖² dy = ∫ ‖∑ᵢ wᵢ·e(−sᵢξ)‖² · ‖𝓕F(ξ)‖² dξ` — the
convolution square against a finitely supported measure factorizes into
the phase sum (the measure's Fourier transform) against `‖𝓕F‖²`. -/
theorem integral_norm_sq_sum_translates (F : ℝ → ℂ)
    (hFc : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) {ι : Type*}
    (S : Finset ι) (w : ι → ℂ) (s : ι → ℝ) :
    ∫ y, ‖∑ i ∈ S, w i * F (y - s i)‖^2
      = ∫ ξ, ‖∑ i ∈ S, w i * ((𝐞 (-(s i * ξ)) : Circle) : ℂ)‖^2
          * ‖𝓕 F ξ‖^2 := by
  classical
  have hGs : ContDiff ℝ ∞ (fun y => ∑ i ∈ S, w i * F (y - s i)) := by
    refine ContDiff.sum fun i _ => ?_
    exact contDiff_const.mul (hFs.comp (contDiff_id.sub contDiff_const))
  have hGc : HasCompactSupport (fun y => ∑ i ∈ S, w i * F (y - s i)) := by
    refine hasCompactSupport_finset_sum fun i _ => ?_
    have h1 : HasCompactSupport (fun y => F (y - s i)) := by
      have h2 := hFc.comp_homeomorph (Homeomorph.subRight (s i))
      exact h2
    exact h1.mul_left
  set G : SchwartzMap ℝ ℂ := hGc.toSchwartzMap hGs with hG_def
  have hGcoe : ∀ y : ℝ, G y = ∑ i ∈ S, w i * F (y - s i) := fun y => rfl
  have h1 : ∫ ξ, ‖𝓕 G ξ‖^2 = ∫ x, ‖G x‖^2 :=
    SchwartzMap.integral_norm_sq_fourier G
  have h2 : ∫ x, ‖G x‖^2 = ∫ y, ‖∑ i ∈ S, w i * F (y - s i)‖^2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [hGcoe]
  have h3 : ∀ ξ : ℝ, 𝓕 G ξ
      = (∑ i ∈ S, w i * ((𝐞 (-(s i * ξ)) : Circle) : ℂ)) * 𝓕 F ξ := by
    intro ξ
    have h4 : 𝓕 G ξ = 𝓕 (G : ℝ → ℂ) ξ := by
      rw [SchwartzMap.fourier_coe]
    rw [h4]
    have h5 : (G : ℝ → ℂ) = (fun y => ∑ i ∈ S, w i * F (y - s i)) := rfl
    rw [h5]
    exact fourier_sum_translates F hFc (hFs.continuous) S w s ξ
  have h6 : ∫ ξ, ‖𝓕 G ξ‖^2
      = ∫ ξ, ‖∑ i ∈ S, w i * ((𝐞 (-(s i * ξ)) : Circle) : ℂ)‖^2
          * ‖𝓕 F ξ‖^2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    dsimp only
    rw [h3, norm_mul, mul_pow]
  rw [← h2, ← h1, h6]


/-- **The Fourier transform of the line derivative, pointwise**:
`𝓕(∂₁f)(ξ) = 2πi·ξ·𝓕f(ξ)`. -/
theorem fourier_lineDeriv_apply (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (∂_{(1:ℝ)} f) ξ = (2 * π * Complex.I) * ξ * 𝓕 f ξ := by
  have h := SchwartzMap.fourier_lineDerivOp_eq f (1:ℝ)
  have h2 := DFunLike.congr_fun h ξ
  simp at h2
  rw [h2]
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (Function.HasTemperateGrowth.id')]
  rw [Complex.real_smul]
  ring

/-- **The derivative Plancherel identity** (C2-iii):
`4π²·∫ ξ²‖𝓕f(ξ)‖² dξ = ∫ ‖f'(y)‖² dy` — the frequency-weighted energy is
the energy of the derivative. -/
theorem integral_sq_mul_norm_fourier_sq (f : 𝓢(ℝ, ℂ)) :
    (4*π^2) * ∫ ξ, ξ^2 * ‖𝓕 f ξ‖^2 = ∫ y, ‖(∂_{(1:ℝ)} f) y‖^2 := by
  have hpt : ∀ ξ : ℝ, ‖(𝓕 (∂_{(1:ℝ)} f)) ξ‖^2
      = 4*π^2 * (ξ^2 * ‖(𝓕 f) ξ‖^2) := by
    intro ξ
    rw [fourier_lineDeriv_apply]
    rw [norm_mul, norm_mul, mul_pow, mul_pow]
    have h1 : ‖(2 * (π:ℂ) * Complex.I)‖ = 2*π := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have h2 : ‖((ξ:ℝ):ℂ)‖ = |ξ| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [h1, h2, sq_abs]
    ring
  have h1 : ∫ ξ, 4*π^2 * (ξ^2 * ‖(𝓕 f) ξ‖^2)
      = ∫ ξ, ‖(𝓕 (∂_{(1:ℝ)} f)) ξ‖^2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    dsimp only
    rw [hpt]
  have h2 := SchwartzMap.integral_norm_sq_fourier (∂_{(1:ℝ)} f)
  rw [← integral_const_mul, h1, h2]

/-- **The high-frequency tail kill** (C2-iii): the tail `|ξ| ≥ K` of the
Fourier energy is at most `K⁻²` times the frequency-weighted energy. -/
theorem setIntegral_norm_fourier_sq_le (f : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    ∫ ξ in {ξ : ℝ | K ≤ |ξ|}, ‖𝓕 f ξ‖^2
      ≤ (1/K^2) * ∫ ξ, ξ^2 * ‖𝓕 f ξ‖^2 := by
  set g : 𝓢(ℝ, ℂ) := 𝓕 f with hg_def
  -- integrability of the two weights
  have hgbd : ∃ C : ℝ, ∀ ξ : ℝ, ‖g ξ‖ ≤ C := by
    obtain ⟨C, hC⟩ := g.decay' 0 0
    exact ⟨C, fun ξ => by
      have := hC ξ
      simpa using this⟩
  obtain ⟨C, hC⟩ := hgbd
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  have hint1 : Integrable (fun ξ : ℝ => ‖g ξ‖^2) := by
    refine (g.integrable.norm.const_mul C).mono' ?_ ?_
    · exact (g.continuous.norm.pow 2).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ξ => ?_
      have h1 : ‖g ξ‖^2 = ‖g ξ‖ * ‖g ξ‖ := sq (‖g ξ‖) ▸ by ring
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ‖g ξ‖^2 = ‖g ξ‖ * ‖g ξ‖ := by ring
        _ ≤ C * ‖g ξ‖ := by
            refine mul_le_mul_of_nonneg_right (hC ξ) (norm_nonneg _)
  have hint2 : Integrable (fun ξ : ℝ => ξ^2 * ‖g ξ‖^2) := by
    refine ((g.integrable_pow_mul volume 2).const_mul C).mono' ?_ ?_
    · exact ((continuous_id.pow 2).mul (g.continuous.norm.pow 2)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ξ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ξ^2 * ‖g ξ‖^2 = (‖g ξ‖ * ξ^2) * ‖g ξ‖ := by ring
        _ ≤ (C * ξ^2) * ‖g ξ‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            refine mul_le_mul_of_nonneg_right (hC ξ) (by positivity)
        _ = C * (ξ^2 * ‖g ξ‖) := by ring
        _ = C * (‖ξ‖^2 * ‖g ξ‖) := by rw [Real.norm_eq_abs, sq_abs]
  -- pointwise domination on the tail set
  have hmono : ∫ ξ in {ξ : ℝ | K ≤ |ξ|}, ‖g ξ‖^2
      ≤ ∫ ξ in {ξ : ℝ | K ≤ |ξ|}, (1/K^2) * (ξ^2 * ‖g ξ‖^2) := by
    refine setIntegral_mono_on hint1.integrableOn
      ((hint2.const_mul (1/K^2)).integrableOn) ?_ ?_
    · exact measurableSet_le measurable_const continuous_abs.measurable
    · intro ξ hξ
      have h1 : K ≤ |ξ| := hξ
      have h2 : K^2 ≤ ξ^2 := by
        rw [← sq_abs ξ]
        exact pow_le_pow_left₀ hK.le h1 2
      have h3 : (0:ℝ) < K^2 := by positivity
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ h3]
      calc ‖g ξ‖^2 * K^2 ≤ ‖g ξ‖^2 * ξ^2 :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = ξ^2 * ‖g ξ‖^2 := by ring
  refine le_trans hmono ?_
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine setIntegral_le_integral hint2 ?_
  refine Filter.Eventually.of_forall fun ξ => ?_
  positivity

end ExpSums

end MoltResearch
