import MoltResearch.Discrepancy.ZeroFreeRegion
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Complex.RealDeriv

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

/-- The smoothed logarithmic sum of the cheap-MR frame. -/
noncomputable def smoothedLogSum (T : ℝ) (η : ℝ → ℝ) (a : ℕ → ℂ)
    (S : Finset ℕ) : ℝ → ℂ :=
  fun y => (T:ℂ) * ∑ m ∈ S, (a m / m) * ((η (T*(y - Real.log m)) : ℝ) : ℂ)

theorem smoothedLogSum_contDiff (T : ℝ) (η : ℝ → ℝ)
    (hηs : ContDiff ℝ ∞ η) (a : ℕ → ℂ) (S : Finset ℕ) :
    ContDiff ℝ ∞ (smoothedLogSum T η a S) := by
  unfold smoothedLogSum
  refine ContDiff.mul contDiff_const ?_
  refine ContDiff.sum fun m _ => ?_
  refine ContDiff.mul contDiff_const ?_
  have h1 : ContDiff ℝ ∞ (fun y : ℝ => T*(y - Real.log m)) :=
    contDiff_const.mul (contDiff_id.sub contDiff_const)
  exact Complex.ofRealCLM.contDiff.comp (hηs.comp h1)

theorem smoothedLogSum_hasCompactSupport (T : ℝ) (hT : 0 < T)
    (η : ℝ → ℝ) (hηc : HasCompactSupport η) (a : ℕ → ℂ) (S : Finset ℕ) :
    HasCompactSupport (smoothedLogSum T η a S) := by
  unfold smoothedLogSum
  have h1 : HasCompactSupport (fun y : ℝ =>
      ∑ m ∈ S, (a m / m) * ((η (T*(y - Real.log m)) : ℝ) : ℂ)) := by
    refine hasCompactSupport_finset_sum fun m _ => ?_
    have h2 : HasCompactSupport (fun y : ℝ => η (T*(y - Real.log m))) := by
      have h3 : (fun y : ℝ => η (T*(y - Real.log m)))
          = η ∘ ((Homeomorph.mulLeft₀ T (ne_of_gt hT)).trans
              (Homeomorph.subRight (T * Real.log m))) := by
        funext y
        simp [Homeomorph.mulLeft₀, Homeomorph.subRight, mul_sub]
      rw [h3]
      exact hηc.comp_homeomorph _
    have h4 : HasCompactSupport (fun y : ℝ =>
        ((η (T*(y - Real.log m)) : ℝ) : ℂ)) := by
      have h5 : (fun y : ℝ => ((η (T*(y - Real.log m)) : ℝ) : ℂ))
          = (fun x : ℝ => (x : ℂ)) ∘ (fun y : ℝ => η (T*(y - Real.log m))) := rfl
      rw [h5]
      exact HasCompactSupport.comp_left h2 Complex.ofReal_zero
    exact h4.mul_left
  exact h1.mul_left

/-- The pointwise bound, stated at `smoothedLogSum`. -/
theorem norm_smoothedLogSum_le (T : ℝ) (hT : 1 ≤ T) (η : ℝ → ℝ)
    (hηsupp : ∀ u : ℝ, η u ≠ 0 → |u| ≤ 2) (B : ℝ) (hηbd : ∀ u, |η u| ≤ B)
    (a : ℕ → ℂ) (ha : ∀ m, ‖a m‖ ≤ 1) (S : Finset ℕ) (M₁ : ℕ)
    (hS : ∀ m ∈ S, M₁ ≤ m) (hM₁ : 1 ≤ M₁) (hTM : T ≤ M₁) (y : ℝ) :
    ‖smoothedLogSum T η a S y‖ ≤ 5 * B :=
  norm_smoothed_sum_le T hT η hηsupp B hηbd a ha S M₁ hS hM₁ hTM y


/-- **The three-regime split** (C2-vi, the phase closer): the translate-sum
energy decomposes against the frequency regimes — an explicit
low-frequency piece (`|ξ| < K`, C4's territory), a middle piece
controlled by the mid-range sup `Mmid` of the phase sum (Phase V's
territory via the ζ'/ζ sub-log bound), and a high piece controlled by
the derivative energy through `Mtot²/L²`. Unconditional: the regime
hypotheses are parameters, not frozen interfaces. -/
theorem integral_norm_sq_sum_translates_regime_split
    (F : ℝ → ℂ) (hFc : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    {ι : Type*} (S : Finset ι) (w : ι → ℂ) (s : ι → ℝ)
    (K L Mmid Mtot : ℝ) (hL : 0 < L) (hMmid0 : 0 ≤ Mmid)
    (hmid : ∀ ξ : ℝ, K ≤ |ξ| → |ξ| ≤ L →
      ‖∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖ ≤ Mmid)
    (htot : ∀ ξ : ℝ,
      ‖∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖ ≤ Mtot) :
    ∫ y, ‖∑ i ∈ S, w i * F (y - s i)‖^2
      ≤ (∫ ξ in {ξ : ℝ | |ξ| < K},
            ‖∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖^2
              * ‖𝓕 F ξ‖^2)
        + Mmid^2 * (∫ ξ, ‖𝓕 F ξ‖^2)
        + Mtot^2 * ((1/L^2) * ∫ ξ, ξ^2 * ‖𝓕 F ξ‖^2) := by
  classical
  have hMtot0 : 0 ≤ Mtot := le_trans (norm_nonneg _) (htot 0)
  set G : SchwartzMap ℝ ℂ := hFc.toSchwartzMap hFs with hG_def
  have hbase := integral_norm_sq_sum_translates F hFc hFs S w s
  rw [hbase]
  set φ : ℝ → ℝ := fun ξ =>
    ‖∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖^2
      * ‖𝓕 F ξ‖^2 with hφ_def
  -- sup bound for `𝓕 G`
  obtain ⟨C, hC⟩ := (𝓕 G).decay' 0 0
  have hC' : ∀ ξ : ℝ, ‖(𝓕 G) ξ‖ ≤ C := fun ξ => by
    have := hC ξ
    simpa using this
  -- integrability of `‖𝓕F‖²`
  have hFG : (fun ξ : ℝ => ‖𝓕 F ξ‖^2) = (fun ξ : ℝ => ‖(𝓕 G) ξ‖^2) := rfl
  have hFhat_int : Integrable (fun ξ : ℝ => ‖𝓕 F ξ‖^2) := by
    rw [hFG]
    refine ((𝓕 G).integrable.norm.const_mul C).mono' ?_ ?_
    · exact ((𝓕 G).continuous.norm.pow 2).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ξ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ‖(𝓕 G) ξ‖^2 = ‖(𝓕 G) ξ‖ * ‖(𝓕 G) ξ‖ := by ring
        _ ≤ C * ‖(𝓕 G) ξ‖ :=
            mul_le_mul_of_nonneg_right (hC' ξ) (norm_nonneg _)
  -- integrability of `ξ²‖𝓕F‖²`
  have hFGpt : ∀ ξ : ℝ, ‖𝓕 F ξ‖ = ‖(𝓕 G) ξ‖ := fun _ => rfl
  have hxi_int : Integrable (fun ξ : ℝ => ξ^2 * ‖𝓕 F ξ‖^2) := by
    simp only [hFGpt]
    refine (((𝓕 G).integrable_pow_mul volume 2).const_mul C).mono' ?_ ?_
    · exact ((continuous_id.pow 2).mul
        ((𝓕 G).continuous.norm.pow 2)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ξ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ξ^2 * ‖(𝓕 G) ξ‖^2 = (‖(𝓕 G) ξ‖ * ξ^2) * ‖(𝓕 G) ξ‖ := by ring
        _ ≤ (C * ξ^2) * ‖(𝓕 G) ξ‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            exact mul_le_mul_of_nonneg_right (hC' ξ) (by positivity)
        _ = C * (ξ^2 * ‖(𝓕 G) ξ‖) := by ring
        _ = C * (‖ξ‖^2 * ‖(𝓕 G) ξ‖) := by rw [Real.norm_eq_abs, sq_abs]
  -- continuity/measurability and integrability of `φ`
  have hphase_cont : Continuous fun ξ : ℝ =>
      ∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ) := by
    refine continuous_finset_sum _ fun i _ => ?_
    refine Continuous.mul continuous_const ?_
    refine Continuous.comp continuous_subtype_val ?_
    exact Real.continuous_fourierChar.comp (by fun_prop)
  have hφ_int : Integrable φ := by
    refine (hFhat_int.const_mul (Mtot^2)).mono' ?_ ?_
    · rw [hφ_def]
      simp only [hFGpt]
      exact ((hphase_cont.norm.pow 2).mul
        ((𝓕 G).continuous.norm.pow 2)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ξ => ?_
      rw [hφ_def, Real.norm_eq_abs]
      dsimp only
      rw [abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have h1 := htot ξ
      nlinarith [norm_nonneg (∑ i ∈ S, w i
        * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ))]
  -- the majorant on the high-frequency complement
  set ψ : ℝ → ℝ := fun ξ =>
    Mmid^2 * ‖𝓕 F ξ‖^2 + Mtot^2 * ((1/L^2) * (ξ^2 * ‖𝓕 F ξ‖^2)) with hψ_def
  have hψ_int : Integrable ψ := by
    refine Integrable.add (hFhat_int.const_mul _) ?_
    exact (hxi_int.const_mul _).const_mul _
  have hmeas : MeasurableSet {ξ : ℝ | |ξ| < K} :=
    measurableSet_lt continuous_abs.measurable measurable_const
  -- split the frequency integral
  have hsplit := (integral_add_compl hmeas hφ_int).symm
  rw [hsplit]
  -- bound the complement by the majorant
  have hpt : ∀ ξ ∈ {ξ : ℝ | |ξ| < K}ᶜ, φ ξ ≤ ψ ξ := by
    intro ξ hξ
    have hKξ : K ≤ |ξ| := by
      rw [Set.mem_compl_iff, Set.mem_setOf_eq] at hξ
      linarith [not_lt.mp hξ]
    rw [hφ_def, hψ_def]
    dsimp only
    rcases le_or_gt |ξ| L with hξL | hξL
    · have h1 := hmid ξ hKξ hξL
      have h2 : ‖∑ i ∈ S, w i
            * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖^2 ≤ Mmid^2 := by
        nlinarith [norm_nonneg (∑ i ∈ S, w i
          * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ))]
      have h3 : (0:ℝ) ≤ Mtot^2 * ((1/L^2) * (ξ^2 * ‖𝓕 F ξ‖^2)) := by
        positivity
      nlinarith [sq_nonneg (‖𝓕 F ξ‖), mul_le_mul_of_nonneg_right h2
        (sq_nonneg (‖𝓕 F ξ‖))]
    · have h1 := htot ξ
      have h2 : ‖∑ i ∈ S, w i
            * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖^2 ≤ Mtot^2 := by
        nlinarith [norm_nonneg (∑ i ∈ S, w i
          * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ))]
      have h3 : (1:ℝ) ≤ ξ^2 / L^2 := by
        rw [le_div_iff₀ (by positivity)]
        have h4 : L^2 ≤ ξ^2 := by
          rw [← sq_abs ξ]
          exact pow_le_pow_left₀ hL.le hξL.le 2
        linarith
      have h4 : ‖𝓕 F ξ‖^2 ≤ (1/L^2) * (ξ^2 * ‖𝓕 F ξ‖^2) := by
        have h5 : (1/L^2) * (ξ^2 * ‖𝓕 F ξ‖^2) = (ξ^2/L^2) * ‖𝓕 F ξ‖^2 := by
          ring
        rw [h5]
        nlinarith [sq_nonneg (‖𝓕 F ξ‖)]
      have h5 : (0:ℝ) ≤ Mmid^2 * ‖𝓕 F ξ‖^2 := by positivity
      nlinarith [sq_nonneg (‖𝓕 F ξ‖), mul_le_mul_of_nonneg_right h2
        (sq_nonneg (‖𝓕 F ξ‖)), mul_le_mul_of_nonneg_left h4 (sq_nonneg Mtot)]
  have hcompl : ∫ ξ in {ξ : ℝ | |ξ| < K}ᶜ, φ ξ
      ≤ ∫ ξ in {ξ : ℝ | |ξ| < K}ᶜ, ψ ξ :=
    setIntegral_mono_on hφ_int.integrableOn hψ_int.integrableOn
      hmeas.compl hpt
  have hfull : ∫ ξ in {ξ : ℝ | |ξ| < K}ᶜ, ψ ξ ≤ ∫ ξ, ψ ξ := by
    refine setIntegral_le_integral hψ_int ?_
    refine Filter.Eventually.of_forall fun ξ => ?_
    rw [hψ_def]
    dsimp only
    positivity
  have hψ_val : ∫ ξ, ψ ξ
      = Mmid^2 * (∫ ξ, ‖𝓕 F ξ‖^2)
        + Mtot^2 * ((1/L^2) * ∫ ξ, ξ^2 * ‖𝓕 F ξ‖^2) := by
    rw [hψ_def]
    rw [integral_add (hFhat_int.const_mul _)
      ((hxi_int.const_mul _).const_mul _)]
    rw [integral_const_mul, integral_const_mul, integral_const_mul]
  linarith [hcompl, hfull, hψ_val.le, hψ_val.ge]

/-- **The smoothed-sum derivative** (Track R, B3-v-a): the
`smoothedLogSum` differentiates under the finite sum, and its
derivative is `T` times the smoothed sum at `η'` — so the harness's
window sup-bound applies verbatim to the derivative. -/
theorem hasDerivAt_smoothedLogSum (T : ℝ) (η : ℝ → ℝ)
    (hηs : ContDiff ℝ ∞ η) (a : ℕ → ℂ) (S : Finset ℕ) (y : ℝ) :
    HasDerivAt (smoothedLogSum T η a S)
      ((T:ℂ) * smoothedLogSum T (deriv η) a S y) y := by
  classical
  have hterm : ∀ m ∈ S,
      HasDerivAt (fun y : ℝ => (a m / m) * ((η (T*(y - Real.log m)) : ℝ) : ℂ))
        ((a m / m) * (((deriv η (T*(y - Real.log m)) * T : ℝ)) : ℂ)) y := by
    intro m _
    refine HasDerivAt.const_mul _ ?_
    have hinner : HasDerivAt (fun y : ℝ => T*(y - Real.log m)) T y := by
      simpa using ((hasDerivAt_id y).sub_const (Real.log m)).const_mul T
    have houter : HasDerivAt η (deriv η (T*(y - Real.log m)))
        (T*(y - Real.log m)) :=
      ((hηs.differentiable (by norm_num)).differentiableAt).hasDerivAt
    have hcomp := HasDerivAt.comp y houter hinner
    exact hcomp.ofReal_comp
  have hsum := HasDerivAt.fun_sum hterm
  have hmul := hsum.const_mul (T:ℂ)
  have hval : (T:ℂ) * ∑ m ∈ S, (a m / m)
        * (((deriv η (T*(y - Real.log m)) * T : ℝ)) : ℂ)
      = (T:ℂ) * smoothedLogSum T (deriv η) a S y := by
    have hpt : ∀ m ∈ S, (a m / m)
          * (((deriv η (T*(y - Real.log m)) * T : ℝ)) : ℂ)
        = (T:ℂ) * ((a m / m) * ((deriv η (T*(y - Real.log m)) : ℝ) : ℂ)) := by
      intro m _
      push_cast
      ring
    rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum]
    unfold smoothedLogSum
    ring
  rw [← hval]
  exact hmul


/-- **The smoothed-window Lipschitz bound** (Track R, B3-v-b): the
squared norm of the smoothed log sum is `50BB′T`-Lipschitz — the
sup bound at `η` and at `η′` through the mean value inequality. This
is the `Λ` the B4 scaffold's Riemann step consumes. -/
theorem abs_norm_sq_smoothedLogSum_sub_le (T : ℝ) (hT : 1 ≤ T)
    (η : ℝ → ℝ) (hηs : ContDiff ℝ ∞ η)
    (hηsupp : ∀ u : ℝ, η u ≠ 0 → |u| ≤ 2) (B : ℝ) (hηbd : ∀ u, |η u| ≤ B)
    (hη'supp : ∀ u : ℝ, deriv η u ≠ 0 → |u| ≤ 2) (B' : ℝ)
    (hη'bd : ∀ u, |deriv η u| ≤ B')
    (a : ℕ → ℂ) (ha : ∀ m, ‖a m‖ ≤ 1) (S : Finset ℕ) (M₁ : ℕ)
    (hS : ∀ m ∈ S, M₁ ≤ m) (hM₁ : 1 ≤ M₁) (hTM : T ≤ M₁) (y z : ℝ) :
    |‖smoothedLogSum T η a S y‖^2 - ‖smoothedLogSum T η a S z‖^2|
      ≤ (50*B*B'*T) * |y - z| := by
  have hB0 : (0:ℝ) ≤ B := le_trans (abs_nonneg _) (hηbd 0)
  have hB'0 : (0:ℝ) ≤ B' := le_trans (abs_nonneg _) (hη'bd 0)
  have hT0 : (0:ℝ) < T := by linarith
  -- the sup bounds
  have hsupG : ∀ w : ℝ, ‖smoothedLogSum T η a S w‖ ≤ 5*B :=
    fun w => norm_smoothedLogSum_le T hT η hηsupp B hηbd a ha S M₁ hS hM₁ hTM w
  have hsupG' : ∀ w : ℝ, ‖(T:ℂ) * smoothedLogSum T (deriv η) a S w‖
      ≤ 5*B'*T := by
    intro w
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
    calc T * ‖smoothedLogSum T (deriv η) a S w‖
        ≤ T * (5*B') := by
          refine mul_le_mul_of_nonneg_left ?_ hT0.le
          exact norm_smoothedLogSum_le T hT (deriv η) hη'supp B' hη'bd
            a ha S M₁ hS hM₁ hTM w
      _ = 5*B'*T := by ring
  -- the mean value inequality
  have hMVT : ‖smoothedLogSum T η a S y - smoothedLogSum T η a S z‖
      ≤ (5*B'*T) * |y - z| := by
    have hderiv : ∀ x ∈ Set.univ, HasDerivWithinAt (smoothedLogSum T η a S)
        ((T:ℂ) * smoothedLogSum T (deriv η) a S x) Set.univ x :=
      fun x _ => (hasDerivAt_smoothedLogSum T η hηs a S x).hasDerivWithinAt
    have hbound : ∀ x ∈ Set.univ,
        ‖(T:ℂ) * smoothedLogSum T (deriv η) a S x‖ ≤ 5*B'*T :=
      fun x _ => hsupG' x
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hbound convex_univ (Set.mem_univ z) (Set.mem_univ y)
    rw [Real.norm_eq_abs] at this
    exact this
  -- the square difference
  have hfac : ‖smoothedLogSum T η a S y‖^2 - ‖smoothedLogSum T η a S z‖^2
      = (‖smoothedLogSum T η a S y‖ - ‖smoothedLogSum T η a S z‖)
        * (‖smoothedLogSum T η a S y‖ + ‖smoothedLogSum T η a S z‖) := by
    ring
  rw [hfac, abs_mul]
  have h1 : |‖smoothedLogSum T η a S y‖ - ‖smoothedLogSum T η a S z‖|
      ≤ ‖smoothedLogSum T η a S y - smoothedLogSum T η a S z‖ :=
    abs_norm_sub_norm_le _ _
  have h2 : |‖smoothedLogSum T η a S y‖ + ‖smoothedLogSum T η a S z‖|
      ≤ 10*B := by
    rw [abs_of_nonneg (by positivity)]
    linarith [hsupG y, hsupG z]
  calc |‖smoothedLogSum T η a S y‖ - ‖smoothedLogSum T η a S z‖|
        * |‖smoothedLogSum T η a S y‖ + ‖smoothedLogSum T η a S z‖|
      ≤ ((5*B'*T) * |y - z|) * (10*B) := by
        refine mul_le_mul (le_trans h1 hMVT) h2 (abs_nonneg _) ?_
        positivity
    _ = (50*B*B'*T) * |y - z| := by ring


/-- **The pointwise Fourier inversion for translate sums** (Track R,
M2-d): the smoothed sum at a point is the integral of the phase
polynomial against the window transform — the Perron-by-smoothing
identity of the cheap Halász argument. -/
theorem sum_translates_eq_integral_char (F : ℝ → ℂ)
    (hFc : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) {ι : Type*}
    (S : Finset ι) (w : ι → ℂ) (s : ι → ℝ) (y : ℝ) :
    ∑ i ∈ S, w i * F (y - s i)
      = ∫ ξ, (𝐞 (ξ * y) : Circle)
          • ((∑ i ∈ S, w i * ((𝐞 (-(s i * ξ)) : Circle) : ℂ)) * 𝓕 F ξ) := by
  classical
  set G : ℝ → ℂ := fun y => ∑ i ∈ S, w i * F (y - s i) with hG_def
  have hGc : HasCompactSupport G := by
    refine hasCompactSupport_finset_sum fun i _ => ?_
    have h2 : HasCompactSupport (fun y : ℝ => F (y - s i)) :=
      hFc.comp_homeomorph (Homeomorph.subRight (s i))
    exact h2.mul_left
  have hGs : Continuous G := by
    refine continuous_finset_sum _ fun i _ => ?_
    exact continuous_const.mul
      ((hFs.continuous).comp (continuous_id.sub continuous_const))
  have hGi : Integrable G := hGs.integrable_of_hasCompactSupport hGc
  -- 𝓕 G is integrable: it is the phase polynomial times the Schwartz 𝓕
  have hGsm : ContDiff ℝ ∞ G := by
    refine ContDiff.sum fun i _ => ?_
    exact contDiff_const.mul
      (hFs.comp (contDiff_id.sub contDiff_const))
  set Gs : 𝓢(ℝ, ℂ) := hGc.toSchwartzMap hGsm with hGs_def
  have hGeq : G = (Gs : ℝ → ℂ) := rfl
  have hFGi : Integrable (𝓕 G) := by
    rw [hGeq]
    exact (𝓕 Gs).integrable
  have hinv := hGs.fourierInv_fourier_eq hGi hFGi
  have hy := congrFun hinv y
  have hval : 𝓕⁻ (𝓕 G) y
      = ∫ ξ, (𝐞 (ξ * y) : Circle) • (𝓕 G ξ) := by
    rw [Real.fourierIntegralInv_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    norm_num
    rw [mul_comm y ξ]
  rw [show (∑ i ∈ S, w i * F (y - s i)) = G y from rfl, ← hy, hval]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  dsimp only
  congr 1
  exact fourier_sum_translates F hFc hFs.continuous S w s ξ

/-- **The Perron-by-smoothing bound** (Track R, M2-d corollary): the
smoothed sum is at most the `L¹` pairing of the phase polynomial with
the window transform. -/
theorem norm_sum_translates_le_integral_char (F : ℝ → ℂ)
    (hFc : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) {ι : Type*}
    (S : Finset ι) (w : ι → ℂ) (s : ι → ℝ) (y : ℝ) :
    ‖∑ i ∈ S, w i * F (y - s i)‖
      ≤ ∫ ξ, ‖∑ i ∈ S, w i * ((𝐞 (-(s i * ξ)) : Circle) : ℂ)‖ * ‖𝓕 F ξ‖ := by
  rw [sum_translates_eq_integral_char F hFc hFs S w s y]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ξ => norm_nonneg _)
    ?_ (Filter.Eventually.of_forall fun ξ => ?_)
  · -- integrability of the majorant
    set Fs : 𝓢(ℝ, ℂ) := hFc.toSchwartzMap hFs with hFs_def
    have hFeq : ∀ ξ, ‖𝓕 F ξ‖ = ‖(𝓕 Fs) ξ‖ := fun _ => rfl
    have hpoly : ∀ ξ : ℝ,
        ‖∑ i ∈ S, w i * ((𝐞 (-(s i * ξ)) : Circle) : ℂ)‖
          ≤ ∑ i ∈ S, ‖w i‖ := by
      intro ξ
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul, norm_eq_of_mem_sphere]
      simp
    refine (((𝓕 Fs).integrable.norm).const_mul (∑ i ∈ S, ‖w i‖)).mono'
      ?_ ?_
    · have hpc : Continuous fun ξ : ℝ =>
          ∑ i ∈ S, w i * ((𝐞 (-(s i * ξ)) : Circle) : ℂ) := by
        refine continuous_finset_sum _ fun i _ => ?_
        refine continuous_const.mul ?_
        exact Continuous.comp continuous_subtype_val
          (Real.continuous_fourierChar.comp (by fun_prop))
      exact (hpc.norm.mul ((𝓕 Fs).continuous.norm)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ξ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)), hFeq]
      exact mul_le_mul_of_nonneg_right (hpoly ξ) (norm_nonneg _)
  · dsimp only
    simp only [Circle.smul_def, smul_eq_mul, norm_mul]
    have h1 : ‖((𝐞 (ξ * y) : Circle) : ℂ)‖ = 1 := norm_eq_of_mem_sphere _
    rw [h1, one_mul]

set_option maxHeartbeats 1600000 in
/-- **The three-regime split at moment `2k`** (Track R, W2-高): the
`ξ²`-tail of `integral_norm_sq_sum_translates_regime_split` sharpened
to any even moment.  The high-frequency piece is priced by
`Mtot²/L^{2k}·∫ξ^{2k}‖𝓕F‖²`, so a smooth window — whose Fourier
transform decays faster than every polynomial — makes the tail beyond
`L` negligible at a cost of `k` derivatives instead of one. -/
theorem integral_norm_sq_sum_translates_regime_split_pow
    (F : ℝ → ℂ) (hFc : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    {ι : Type*} (S : Finset ι) (w : ι → ℂ) (s : ι → ℝ)
    (K L Mmid Mtot : ℝ) (k : ℕ) (hL : 0 < L) (hMmid0 : 0 ≤ Mmid)
    (hmid : ∀ ξ : ℝ, K ≤ |ξ| → |ξ| ≤ L →
      ‖∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖ ≤ Mmid)
    (htot : ∀ ξ : ℝ,
      ‖∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖ ≤ Mtot) :
    ∫ y, ‖∑ i ∈ S, w i * F (y - s i)‖^2
      ≤ (∫ ξ in {ξ : ℝ | |ξ| < K},
            ‖∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖^2
              * ‖𝓕 F ξ‖^2)
        + Mmid^2 * (∫ ξ, ‖𝓕 F ξ‖^2)
        + Mtot^2 * ((1/L^(2*k)) * ∫ ξ, ξ^(2*k) * ‖𝓕 F ξ‖^2) := by
  classical
  have hev : Even (2*k) := even_two_mul k
  have hxinn : ∀ ξ : ℝ, (0:ℝ) ≤ ξ^(2*k) := fun ξ => hev.pow_nonneg ξ
  have hxabs : ∀ ξ : ℝ, |ξ|^(2*k) = ξ^(2*k) := fun ξ => hev.pow_abs ξ
  have hMtot0 : 0 ≤ Mtot := le_trans (norm_nonneg _) (htot 0)
  set G : SchwartzMap ℝ ℂ := hFc.toSchwartzMap hFs with hG_def
  have hbase := integral_norm_sq_sum_translates F hFc hFs S w s
  rw [hbase]
  set φ : ℝ → ℝ := fun ξ =>
    ‖∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖^2
      * ‖𝓕 F ξ‖^2 with hφ_def
  obtain ⟨C, hC⟩ := (𝓕 G).decay' 0 0
  have hC' : ∀ ξ : ℝ, ‖(𝓕 G) ξ‖ ≤ C := fun ξ => by
    have := hC ξ
    simpa using this
  have hFG : (fun ξ : ℝ => ‖𝓕 F ξ‖^2) = (fun ξ : ℝ => ‖(𝓕 G) ξ‖^2) := rfl
  have hFhat_int : Integrable (fun ξ : ℝ => ‖𝓕 F ξ‖^2) := by
    rw [hFG]
    refine ((𝓕 G).integrable.norm.const_mul C).mono' ?_ ?_
    · exact ((𝓕 G).continuous.norm.pow 2).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ξ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ‖(𝓕 G) ξ‖^2 = ‖(𝓕 G) ξ‖ * ‖(𝓕 G) ξ‖ := by ring
        _ ≤ C * ‖(𝓕 G) ξ‖ :=
            mul_le_mul_of_nonneg_right (hC' ξ) (norm_nonneg _)
  have hFGpt : ∀ ξ : ℝ, ‖𝓕 F ξ‖ = ‖(𝓕 G) ξ‖ := fun _ => rfl
  have hxi_int : Integrable (fun ξ : ℝ => ξ^(2*k) * ‖𝓕 F ξ‖^2) := by
    simp only [hFGpt]
    refine (((𝓕 G).integrable_pow_mul volume (2*k)).const_mul C).mono' ?_ ?_
    · exact (((continuous_id.pow (2*k))).mul
        ((𝓕 G).continuous.norm.pow 2)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ξ => ?_
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (hxinn ξ) (by positivity))]
      calc ξ^(2*k) * ‖(𝓕 G) ξ‖^2
          = (‖(𝓕 G) ξ‖ * ξ^(2*k)) * ‖(𝓕 G) ξ‖ := by ring
        _ ≤ (C * ξ^(2*k)) * ‖(𝓕 G) ξ‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            exact mul_le_mul_of_nonneg_right (hC' ξ) (hxinn ξ)
        _ = C * (ξ^(2*k) * ‖(𝓕 G) ξ‖) := by ring
        _ = C * (‖ξ‖^(2*k) * ‖(𝓕 G) ξ‖) := by
            rw [Real.norm_eq_abs, hxabs]
  have hphase_cont : Continuous fun ξ : ℝ =>
      ∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ) := by
    refine continuous_finset_sum _ fun i _ => ?_
    refine Continuous.mul continuous_const ?_
    refine Continuous.comp continuous_subtype_val ?_
    exact Real.continuous_fourierChar.comp (by fun_prop)
  have hφ_int : Integrable φ := by
    refine (hFhat_int.const_mul (Mtot^2)).mono' ?_ ?_
    · rw [hφ_def]
      simp only [hFGpt]
      exact ((hphase_cont.norm.pow 2).mul
        ((𝓕 G).continuous.norm.pow 2)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ξ => ?_
      rw [hφ_def, Real.norm_eq_abs]
      dsimp only
      rw [abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have h1 := htot ξ
      nlinarith [norm_nonneg (∑ i ∈ S, w i
        * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ))]
  set ψ : ℝ → ℝ := fun ξ =>
    Mmid^2 * ‖𝓕 F ξ‖^2
      + Mtot^2 * ((1/L^(2*k)) * (ξ^(2*k) * ‖𝓕 F ξ‖^2)) with hψ_def
  have hψ_int : Integrable ψ := by
    refine Integrable.add (hFhat_int.const_mul _) ?_
    exact (hxi_int.const_mul _).const_mul _
  have hmeas : MeasurableSet {ξ : ℝ | |ξ| < K} :=
    measurableSet_lt continuous_abs.measurable measurable_const
  have hsplit := (integral_add_compl hmeas hφ_int).symm
  rw [hsplit]
  have hpt : ∀ ξ ∈ {ξ : ℝ | |ξ| < K}ᶜ, φ ξ ≤ ψ ξ := by
    intro ξ hξ
    have hKξ : K ≤ |ξ| := by
      rw [Set.mem_compl_iff, Set.mem_setOf_eq] at hξ
      linarith [not_lt.mp hξ]
    rw [hφ_def, hψ_def]
    dsimp only
    rcases le_or_gt |ξ| L with hξL | hξL
    · have h1 := hmid ξ hKξ hξL
      have h2 : ‖∑ i ∈ S, w i
            * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖^2 ≤ Mmid^2 := by
        nlinarith [norm_nonneg (∑ i ∈ S, w i
          * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ))]
      have h3 : (0:ℝ) ≤ Mtot^2 * ((1/L^(2*k)) * (ξ^(2*k) * ‖𝓕 F ξ‖^2)) := by
        have := hxinn ξ
        positivity
      nlinarith [sq_nonneg (‖𝓕 F ξ‖), mul_le_mul_of_nonneg_right h2
        (sq_nonneg (‖𝓕 F ξ‖))]
    · have h1 := htot ξ
      have h2 : ‖∑ i ∈ S, w i
            * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖^2 ≤ Mtot^2 := by
        nlinarith [norm_nonneg (∑ i ∈ S, w i
          * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ))]
      have hLpow : (0:ℝ) < L^(2*k) := by positivity
      have h3 : (1:ℝ) ≤ ξ^(2*k) / L^(2*k) := by
        rw [le_div_iff₀ hLpow]
        have h4 : L^(2*k) ≤ ξ^(2*k) := by
          rw [← hxabs ξ]
          exact pow_le_pow_left₀ hL.le hξL.le _
        linarith
      have h4 : ‖𝓕 F ξ‖^2 ≤ (1/L^(2*k)) * (ξ^(2*k) * ‖𝓕 F ξ‖^2) := by
        have h5 : (1/L^(2*k)) * (ξ^(2*k) * ‖𝓕 F ξ‖^2)
            = (ξ^(2*k)/L^(2*k)) * ‖𝓕 F ξ‖^2 := by ring
        rw [h5]
        nlinarith [sq_nonneg (‖𝓕 F ξ‖)]
      have h5 : (0:ℝ) ≤ Mmid^2 * ‖𝓕 F ξ‖^2 := by positivity
      nlinarith [sq_nonneg (‖𝓕 F ξ‖), mul_le_mul_of_nonneg_right h2
        (sq_nonneg (‖𝓕 F ξ‖)), mul_le_mul_of_nonneg_left h4 (sq_nonneg Mtot)]
  have hcompl : ∫ ξ in {ξ : ℝ | |ξ| < K}ᶜ, φ ξ
      ≤ ∫ ξ in {ξ : ℝ | |ξ| < K}ᶜ, ψ ξ :=
    setIntegral_mono_on hφ_int.integrableOn hψ_int.integrableOn
      hmeas.compl hpt
  have hfull : ∫ ξ in {ξ : ℝ | |ξ| < K}ᶜ, ψ ξ ≤ ∫ ξ, ψ ξ := by
    refine setIntegral_le_integral hψ_int ?_
    refine Filter.Eventually.of_forall fun ξ => ?_
    rw [hψ_def]
    dsimp only
    have := hxinn ξ
    positivity
  have hψ_val : ∫ ξ, ψ ξ
      = Mmid^2 * (∫ ξ, ‖𝓕 F ξ‖^2)
        + Mtot^2 * ((1/L^(2*k)) * ∫ ξ, ξ^(2*k) * ‖𝓕 F ξ‖^2) := by
    rw [hψ_def]
    rw [integral_add (hFhat_int.const_mul _)
      ((hxi_int.const_mul _).const_mul _)]
    rw [integral_const_mul, integral_const_mul, integral_const_mul]
  linarith [hcompl, hfull, hψ_val.le, hψ_val.ge]

end ExpSums

end MoltResearch
