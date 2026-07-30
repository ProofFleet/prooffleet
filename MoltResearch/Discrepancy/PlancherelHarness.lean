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

/-- The `+1`-free harmonic window, inclusive form:
`∑_{a ≤ m ≤ b} 1/m ≤ 1/a + log b − log a`. -/
theorem sum_one_div_Ico_succ_window_le (a : ℕ) (ha : 1 ≤ a) :
    ∀ b : ℕ, a ≤ b →
      ∑ m ∈ Finset.Ico a (b+1), (1:ℝ)/m ≤ 1/a + Real.log b - Real.log a := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base =>
    have h1 : Finset.Ico a (a+1) = {a} := by
      ext m
      rw [Finset.mem_Ico, Finset.mem_singleton]
      omega
    rw [h1, Finset.sum_singleton]
    simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    have hb1 : (0:ℝ) < b := by
      have : 1 ≤ b := le_trans ha hab
      exact_mod_cast this
    have hstep : (1:ℝ)/(b+1) ≤ Real.log (b+1) - Real.log b := by
      have h1 : Real.log ((b:ℝ)/(b+1)) ≤ (b:ℝ)/(b+1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h2 : Real.log ((b:ℝ)/(b+1)) = Real.log b - Real.log (b+1) :=
        Real.log_div (ne_of_gt hb1) (by positivity)
      have h3 : (b:ℝ)/(b+1) - 1 = -(1/(b+1)) := by
        field_simp
        ring
      rw [h2, h3] at h1
      linarith
    push_cast
    push_cast at ih
    linarith

/-- The `+1`-free harmonic window: `∑_{a ≤ m < b} 1/m ≤ 1/a + log b − log a`
for `1 ≤ a ≤ b`. -/
theorem sum_one_div_Ico_window_le (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ m ∈ Finset.Ico a b, (1:ℝ)/m ≤ 1/a + Real.log b - Real.log a := by
  rcases Nat.eq_or_lt_of_le hab with rfl | hlt
  · rw [Finset.Ico_self, Finset.sum_empty]
    have h1 : (0:ℝ) < 1/a := by positivity
    linarith
  · have h1 : b = (b - 1) + 1 := by omega
    rw [h1]
    refine le_trans (sum_one_div_Ico_succ_window_le a ha (b-1) (by omega)) ?_
    have h2 : Real.log ((b - 1 : ℕ)) ≤ Real.log (((b - 1) + 1 : ℕ)) := by
      have h3 : 1 ≤ b - 1 ∨ b - 1 = 0 := by omega
      rcases h3 with h3 | h3
      · refine Real.log_le_log (by exact_mod_cast h3) ?_
        exact_mod_cast Nat.le_succ _
      · rw [h3, Nat.cast_zero, Real.log_zero]
        exact Real.log_natCast_nonneg _
    push_cast at h2 ⊢
    linarith


/-- **The pointwise bound for the smoothed logarithmic sum** (C2-i): with
bounded coefficients `‖a m‖ ≤ 1`, a window `η` supported in `[-2,2]` and
bounded by `B`, and block start `M₁ ≥ T`, the smoothed sum
`T·∑_{m ∈ S} (a m/m)·η(T(y − log m))` is uniformly `≤ 5B`: at each `y`
only `m` in a multiplicative `e^{±2/T}`-window contribute, and the
harmonic window sum is `≤ 5/T` — the window endpoints are read off the
contributing set's own min/max, so no exponentials appear. -/
theorem norm_smoothed_sum_le (T : ℝ) (hT : 1 ≤ T) (η : ℝ → ℝ)
    (hηsupp : ∀ u : ℝ, η u ≠ 0 → |u| ≤ 2) (B : ℝ) (hηbd : ∀ u, |η u| ≤ B)
    (a : ℕ → ℂ) (ha : ∀ m, ‖a m‖ ≤ 1) (S : Finset ℕ) (M₁ : ℕ)
    (hS : ∀ m ∈ S, M₁ ≤ m) (hM₁ : 1 ≤ M₁) (hTM : T ≤ M₁) (y : ℝ) :
    ‖(T:ℂ) * ∑ m ∈ S, (a m / m) * ((η (T*(y - Real.log m)) : ℝ) : ℂ)‖
      ≤ 5 * B := by
  classical
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hηbd 0)
  have hT0 : (0:ℝ) < T := by linarith
  set W : Finset ℕ := S.filter (fun m => η (T*(y - Real.log m)) ≠ 0)
    with hW_def
  have hsum : ∑ m ∈ S, (a m / m) * ((η (T*(y - Real.log m)) : ℝ) : ℂ)
      = ∑ m ∈ W, (a m / m) * ((η (T*(y - Real.log m)) : ℝ) : ℂ) := by
    rw [hW_def]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro m _ hne
    intro h0
    refine hne ?_
    rw [h0]
    push_cast
    ring
  rw [hsum]
  have hwin : ∀ m ∈ W, y - 2/T ≤ Real.log m ∧ Real.log m ≤ y + 2/T := by
    intro m hm
    rw [hW_def, Finset.mem_filter] at hm
    have h1 := hηsupp _ hm.2
    have h2 := abs_le.mp h1
    have hTT : T * (2/T) = 2 := by field_simp
    constructor
    · have h4 : T * (y - Real.log m) ≤ T * (2/T) := by
        rw [hTT]
        exact h2.2
      have h5 := le_of_mul_le_mul_left h4 hT0
      linarith
    · have h4 : T * (-(2/T)) ≤ T * (y - Real.log m) := by
        rw [show T * (-(2/T)) = -2 from by rw [mul_neg, hTT]]
        exact h2.1
      have h5 := le_of_mul_le_mul_left h4 hT0
      linarith
  rcases Finset.eq_empty_or_nonempty W with hWe | hWne
  · rw [hWe, Finset.sum_empty, mul_zero, norm_zero]
    positivity
  · have hmn_mem := W.min'_mem hWne
    have hmx_mem := W.max'_mem hWne
    have hmnM : M₁ ≤ W.min' hWne := by
      refine hS _ ?_
      exact Finset.mem_of_mem_filter _ hmn_mem
    have hmn1 : 1 ≤ W.min' hWne := le_trans hM₁ hmnM
    have hmnmx : W.min' hWne ≤ W.max' hWne := W.min'_le _ hmx_mem
    have hsub : W ⊆ Finset.Ico (W.min' hWne) (W.max' hWne + 1) := by
      intro m hm
      rw [Finset.mem_Ico]
      exact ⟨W.min'_le m hm, Nat.lt_succ_of_le (W.le_max' m hm)⟩
    have hharm : ∑ m ∈ W, (1:ℝ)/m
        ≤ 1/(W.min' hWne) + Real.log (W.max' hWne)
          - Real.log (W.min' hWne) := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) ?_
      · intro m _ _
        positivity
      · exact sum_one_div_Ico_succ_window_le _ hmn1 _ hmnmx
    have hspread : Real.log (W.max' hWne) - Real.log (W.min' hWne)
        ≤ 4/T := by
      have h1 := (hwin _ hmn_mem).1
      have h2 := (hwin _ hmx_mem).2
      have h3 : (2:ℝ)/T + 2/T = 4/T := by ring
      linarith
    have hedge : (1:ℝ)/(W.min' hWne) ≤ 1/T := by
      refine one_div_le_one_div_of_le hT0 ?_
      calc T ≤ (M₁:ℝ) := hTM
        _ ≤ (W.min' hWne : ℝ) := by exact_mod_cast hmnM
    have hnorm : ‖(T:ℂ) * ∑ m ∈ W,
          (a m / m) * ((η (T*(y - Real.log m)) : ℝ) : ℂ)‖
        ≤ T * ((∑ m ∈ W, (1:ℝ)/m) * B) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
      refine mul_le_mul_of_nonneg_left ?_ hT0.le
      refine le_trans (norm_sum_le _ _) ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun m hm => ?_
      have hm1 : 1 ≤ m := by
        refine le_trans hM₁ (hS m ?_)
        exact Finset.mem_of_mem_filter _ hm
      have hm0 : (0:ℝ) < m := by exact_mod_cast hm1
      rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs]
      calc ‖a m‖ / m * |η (T*(y - Real.log m))|
          ≤ 1 / m * B := by
            refine mul_le_mul ?_ (hηbd _) (abs_nonneg _) (by positivity)
            exact div_le_div_of_nonneg_right (ha m) hm0.le
        _ = (1:ℝ)/m * B := rfl
    refine le_trans hnorm ?_
    have hfinal : T * ((∑ m ∈ W, (1:ℝ)/m) * B) ≤ 5 * B := by
      have h1 : ∑ m ∈ W, (1:ℝ)/m ≤ 1/T + 4/T := by
        linarith
      have h2 : T * (∑ m ∈ W, (1:ℝ)/m) ≤ 5 := by
        have h3 : T * (1/T + 4/T) = 5 := by field_simp; ring
        have h4 := mul_le_mul_of_nonneg_left h1 hT0.le
        rw [h3] at h4
        exact h4
      have h5 : (0:ℝ) ≤ ∑ m ∈ W, (1:ℝ)/m :=
        Finset.sum_nonneg fun m _ => by positivity
      calc T * ((∑ m ∈ W, (1:ℝ)/m) * B)
          = (T * (∑ m ∈ W, (1:ℝ)/m)) * B := by ring
        _ ≤ 5 * B := mul_le_mul_of_nonneg_right h2 hB0
    exact hfinal

end ExpSums

end MoltResearch
