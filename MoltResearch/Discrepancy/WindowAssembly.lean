import MoltResearch.Discrepancy.ParsevalBridge
import MoltResearch.Discrepancy.TypicalFactorization
import MoltResearch.Discrepancy.HalaszComplex

/-!
# Track C: the window assembly (Track R, A.2 leg, G-ladder)

The end-to-end assembly of the log-averaged window bound
`∑_{n ∈ (x/w, x]} ‖W_n‖/(H·n) ≤ ε·log w` from the in-tree pieces: the
Parseval bridge's time side (`slice_time_side`), the Plancherel
harness's regime split, the `𝒰`-recursion band energies, the typical
factorization density, and the ℂ-valued plain-sum Halász.  Units are
the G-ladder of the A2-II/III design (state file): G1–G5 glue the
frequency side, G6 expands the major arc, G7 supplies the Halász sup,
G8–G10 aggregate and close.
-/

namespace MoltResearch

namespace ExpSums

open Real MeasureTheory
open scoped FourierTransform ContDiff

/-- **G1**: an interval energy is at most the line energy, for a
nonnegative-integrand shape (norm-squared of a continuous compactly
supported profile). -/
theorem intervalIntegral_norm_sq_le_integral (G : ℝ → ℂ)
    (hGc : Continuous G) (hGs : HasCompactSupport G) (a b : ℝ) :
    ∫ y in a..b, ‖G y‖^2 ≤ ∫ y, ‖G y‖^2 := by
  have hint : Integrable (fun y => ‖G y‖^2) :=
    ((hGc.norm.pow 2)).integrable_of_hasCompactSupport
      (hGs.comp_left (g := fun z : ℂ => ‖z‖^2) (by simp))
  rcases le_total a b with hab | hab
  · rw [intervalIntegral.integral_of_le hab]
    refine le_trans (le_of_eq (integral_Ioc_eq_integral_Ioo)) ?_
    exact setIntegral_le_integral hint
      (Filter.Eventually.of_forall fun y => by positivity)
  · rw [intervalIntegral.integral_of_ge hab]
    have h0 : (0:ℝ) ≤ ∫ y in Set.Ioc b a, ‖G y‖^2 :=
      setIntegral_nonneg measurableSet_Ioc fun y _ => by positivity
    have h1 : (0:ℝ) ≤ ∫ y, ‖G y‖^2 :=
      integral_nonneg fun y => by positivity
    linarith

/-- **G2**: the open-ball low band is at most the closed interval
band, for a nonnegative integrand. -/
theorem setIntegral_ball_le_intervalIntegral (φ : ℝ → ℝ)
    (hφ : Integrable φ) (hφ0 : ∀ ξ, 0 ≤ φ ξ) (K : ℝ) (hK : 0 ≤ K) :
    ∫ ξ in {ξ : ℝ | |ξ| < K}, φ ξ ≤ ∫ ξ in (-K)..K, φ ξ := by
  have hset : {ξ : ℝ | |ξ| < K} = Set.Ioo (-K) K := by
    ext ξ
    simp [abs_lt]
  rw [hset, intervalIntegral.integral_of_le (by linarith),
    ← integral_Ioc_eq_integral_Ioo]


open MeasureTheory in
/-- **G3a: the slice-window transform sup** (Track R, A2-II): the
profile `v ↦ η(Tv)` (values in `[0,1]`, support of `η` in `[−2,2]`)
has `‖𝓕F‖ ≤ 4/T` uniformly — the `L¹` mass of the window. -/
theorem norm_fourier_slice_window_le (T : ℝ) (hT : 0 < T) (η : ℝ → ℝ)
    (hηc : Continuous η)
    (hη01 : ∀ u, 0 ≤ η u ∧ η u ≤ 1) (hη2 : ∀ u, η u ≠ 0 → |u| ≤ 2)
    (ξ : ℝ) :
    ‖𝓕 (fun v => ((η (T*v) : ℝ) : ℂ)) ξ‖ ≤ 4/T := by
  refine le_trans
    (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _) ?_
  have hsupp : ∀ v : ℝ, v ∉ Set.Icc (-(2/T)) (2/T) →
      ((η (T*v) : ℝ) : ℂ) = 0 := by
    intro v hv
    rw [Set.mem_Icc, not_and_or] at hv
    have hz : η (T*v) = 0 := by
      by_contra hne
      have h2 := hη2 _ hne
      rw [abs_le] at h2
      have hid : T * (2/T) = 2 := by field_simp
      rcases hv with h | h
      · push_neg at h
        have := mul_lt_mul_of_pos_left h hT
        nlinarith [h2.1]
      · push_neg at h
        have := mul_lt_mul_of_pos_left h hT
        nlinarith [h2.2]
    rw [hz, Complex.ofReal_zero]
  have hnorm_le : ∀ v ∈ Set.Icc (-(2/T)) (2/T),
      ‖((η (T*v) : ℝ) : ℂ)‖ ≤ 1 := by
    intro v _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hη01 _).1]
    exact (hη01 _).2
  have hc : Continuous (fun v : ℝ => ((η (T*v) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (hηc.comp (continuous_const.mul continuous_id))
  have hcs : HasCompactSupport (fun v : ℝ => ((η (T*v) : ℝ) : ℂ)) :=
    HasCompactSupport.intro (isCompact_Icc (a := -(2/T)) (b := 2/T)) hsupp
  have hint : Integrable (fun v : ℝ => ‖((η (T*v) : ℝ) : ℂ)‖) :=
    hc.norm.integrable_of_hasCompactSupport hcs.norm
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Set.Icc (-(2/T)) (2/T))
    (fun v hv => by rw [hsupp v hv]; simp)]
  calc ∫ v in Set.Icc (-(2/T)) (2/T), ‖((η (T*v) : ℝ) : ℂ)‖
      ≤ ∫ _ in Set.Icc (-(2/T)) (2/T), (1:ℝ) := by
        refine setIntegral_mono_on hint.integrableOn
          (integrableOn_const measure_Icc_lt_top.ne) measurableSet_Icc hnorm_le
    _ = 4/T := by
        rw [setIntegral_const, smul_eq_mul, mul_one,
          MeasureTheory.measureReal_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (by
            have h4 : (0:ℝ) < 2/T := by positivity
            linarith : (0:ℝ) ≤ 2/T - (-(2/T)))]
        ring

open MeasureTheory in
/-- **G3b: the slice-window transform energy** (Track R, A2-II):
`∫‖𝓕F‖² ≤ 4/T` — Plancherel plus the same `L^∞`/support bound. -/
theorem integral_norm_sq_fourier_slice_window_le (T : ℝ) (hT : 0 < T)
    (η : ℝ → ℝ) (hηs : ContDiff ℝ ∞ η)
    (hη01 : ∀ u, 0 ≤ η u ∧ η u ≤ 1) (hη2 : ∀ u, η u ≠ 0 → |u| ≤ 2) :
    ∫ ξ, ‖𝓕 (fun v => ((η (T*v) : ℝ) : ℂ)) ξ‖^2 ≤ 4/T := by
  obtain ⟨hcs, hcd⟩ := window_profile_props T hT η hηs hη2
  have hsupp : ∀ v : ℝ, v ∉ Set.Icc (-(2/T)) (2/T) →
      ((η (T*v) : ℝ) : ℂ) = 0 := by
    intro v hv
    rw [Set.mem_Icc, not_and_or] at hv
    have hz : η (T*v) = 0 := by
      by_contra hne
      have h2 := hη2 _ hne
      rw [abs_le] at h2
      have hid : T * (2/T) = 2 := by field_simp
      rcases hv with h | h
      · push_neg at h
        have := mul_lt_mul_of_pos_left h hT
        nlinarith [h2.1]
      · push_neg at h
        have := mul_lt_mul_of_pos_left h hT
        nlinarith [h2.2]
    rw [hz, Complex.ofReal_zero]
  set G : SchwartzMap ℝ ℂ := hcs.toSchwartzMap hcd with hG_def
  have hGcoe : ∀ y : ℝ, G y = ((η (T*y) : ℝ) : ℂ) := fun y => rfl
  have h1 : ∫ ξ, ‖𝓕 (⇑G) ξ‖^2 = ∫ x, ‖G x‖^2 :=
    SchwartzMap.integral_norm_sq_fourier G
  have h2 : (fun v : ℝ => ((η (T*v) : ℝ) : ℂ)) = ⇑G := by
    funext y
    rw [hGcoe]
  rw [h2, h1]
  -- the time-side energy over the support interval
  have hc : Continuous (fun v : ℝ => ‖G v‖^2) :=
    (G.continuous.norm.pow 2)
  have hint : Integrable (fun v : ℝ => ‖G v‖^2) :=
    hc.integrable_of_hasCompactSupport
      (hcs.comp_left (g := fun z : ℂ => ‖z‖^2) (by simp))
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Set.Icc (-(2/T)) (2/T))
    (fun v hv => by
      show ‖G v‖^2 = 0
      rw [hGcoe, hsupp v hv]
      simp)]
  have hnorm_le : ∀ v ∈ Set.Icc (-(2/T)) (2/T), ‖G v‖^2 ≤ 1 := by
    intro v _
    rw [hGcoe, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hη01 _).1]
    nlinarith [(hη01 (T*v)).1, (hη01 (T*v)).2]
  calc ∫ v in Set.Icc (-(2/T)) (2/T), ‖G v‖^2
      ≤ ∫ _ in Set.Icc (-(2/T)) (2/T), (1:ℝ) := by
        refine setIntegral_mono_on hint.integrableOn
          (integrableOn_const measure_Icc_lt_top.ne) measurableSet_Icc hnorm_le
    _ = 4/T := by
        rw [setIntegral_const, smul_eq_mul, mul_one,
          MeasureTheory.measureReal_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (by
            have h4 : (0:ℝ) < 2/T := by positivity
            linarith : (0:ℝ) ≤ 2/T - (-(2/T)))]
        ring

end ExpSums

end MoltResearch
