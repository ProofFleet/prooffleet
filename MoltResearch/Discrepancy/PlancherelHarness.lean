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

open Real MeasureTheory SchwartzMap
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

end ExpSums

end MoltResearch
