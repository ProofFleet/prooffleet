import MoltResearch.Discrepancy.SliceA2
import MoltResearch.Discrepancy.ExplicitSliceEnergy

/-!
# Frequency bands for the explicit slice window

This leaf repeats the four-slot slice accounting with the explicit window.
Consequently the transform derivative envelope is the concrete quantity
`explicitSliceWindowDerivBound epsGeom`, rather than an abstract bump constant.
-/

namespace MoltResearch

open Real Finset MeasureTheory SchwartzMap ExpSums
open scoped FourierTransform ContDiff

set_option maxHeartbeats 800000 in
/-- Per-slice energy from the low, inner, outer, and tail frequency slots,
using the polynomially controlled explicit window. -/
theorem slice_energy_le_of_explicit_bands
    (h : ℕ → ℂ) (hb : ∀ m, ‖h m‖ ≤ 1)
    (A s U H : ℕ) (hA : 1 ≤ A) (hs : 1 ≤ s) (hsA : s ≤ A)
    (hU : 0 < U) (hUH : 2 * U ≤ H) (h3H : 3 * H ≤ A)
    (hplat : ((U : ℝ) + 1) * ((A : ℝ) + s) ≤ (A : ℝ) * H)
    (hΔA : s + 2 * H + 4 * U ≤ A)
    (hs30 : 30 * s ≤ A)
    (epsGeom : ℝ) (heps : 0 < epsGeom) (heps1 : epsGeom ≤ 1)
    (hU100 : epsGeom * (H : ℝ) ≤ 100 * U)
    (hU50 : 50 * (U : ℝ) ≤ epsGeom * H)
    (K K₂ L Mtot : ℝ) (hKK₂ : K ≤ K₂) (hK₂ : 0 < K₂)
    (hK₂L : K₂ ≤ L) (J : ℕ) (hJ : L < 2 ^ J * K₂)
    (htot : ∀ ξ : ℝ,
      ‖∑ m ∈ Finset.Ioc A (A + s + 2 * H + 4 * U),
        h m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖ ≤ Mtot)
    (Elow Einner : ℝ)
    (hlow : (∫ ξ in {ξ : ℝ | |ξ| < K},
        ‖∑ m ∈ Finset.Ioc A (A + s + 2 * H + 4 * U),
          h m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖ ^ 2) ≤ Elow)
    (hinner : ∀ w : ℝ → ℝ, Measurable w → (∀ ξ, 0 ≤ w ξ) →
      (∀ ξ, w ξ ≤ (4 * (H : ℝ) / A) ^ 2) →
      (∫ ξ in {ξ : ℝ | K ≤ |ξ| ∧ |ξ| ≤ K₂},
        ‖∑ m ∈ Finset.Ioc A (A + s + 2 * H + 4 * U),
          h m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖ ^ 2 * w ξ)
        ≤ Einner) :
    ∑ n ∈ Finset.Ioc A (A + s), ‖∑ m ∈ Finset.Ioc n (n + H), h m‖ ^ 2 / n
      ≤ 6 * ((4 * (H : ℝ) / A) ^ 2 * Elow + Einner
            + (4 * explicitSliceWindowDerivBound epsGeom ^ 2 / π ^ 2) *
                ((2 * (A : ℝ) + 1) ^ 2 *
                  (Real.exp Real.pi * ((4 / (K₂ * (A : ℝ))) + (6 / K₂ ^ 2)) *
                    (∑ n ∈ Finset.Ioc A (A + s + 2 * H + 4 * U), (1 : ℝ) / n)))
            + Mtot ^ 2 * ((1 / L ^ 2) *
                ((A : ℝ) / H * explicitSliceWindowDerivBound epsGeom ^ 2 / π ^ 2)))
        + (3 * (U : ℝ) ^ 2 +
            3 * (6 * (U : ℝ) + (H : ℝ) * s / A + 2) ^ 2) *
            (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n)
        + 6 * (800 * (H : ℝ) * (A : ℝ) *
          explicitSliceWindowDerivBound epsGeom) / A := by
  classical
  have hH : 0 < H := by omega
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hT : (0 : ℝ) < (A : ℝ) / H := by positivity
  have hL : 0 < L := lt_of_lt_of_le hK₂ hK₂L
  have hKL : K ≤ L := le_trans hKK₂ hK₂L
  have hB0 : 0 ≤ explicitSliceWindowDerivBound epsGeom := by
    unfold explicitSliceWindowDerivBound
    positivity [one_le_explicitSliceWindowConstant]
  set P : ℝ → ℂ := fun ξ => ∑ m ∈ Finset.Ioc A (A + s + 2 * H + 4 * U),
      h m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) with hP_def
  have hPcont : Continuous P := continuous_char_poly _ _ _
  refine slice_energy_le_of_explicit_window_energy h hb A s U H hA hs hsA
    hU hUH h3H hplat hs30 epsGeom heps heps1 hU100 hU50 _ ?_
  intro eta hηs hη01 hη2 hderiv
  obtain ⟨B₂, hB₂0, hB₂, hd2⟩ := exists_deriv_bound eta hηs hη2
  have hG3c := integral_sq_norm_fourier_slice_window_le ((A : ℝ) / H) hT eta
    hηs hη2 (explicitSliceWindowDerivBound epsGeom) hB0 hderiv hd2
  set w : ℝ → ℝ := fun ξ =>
    ‖𝓕 (fun v => ((eta (((A : ℝ) / H) * v) : ℝ) : ℂ)) ξ‖ ^ 2 with hw_def
  have hw0 : ∀ ξ, 0 ≤ w ξ := fun ξ => by positivity
  have hwC : ∀ ξ, w ξ ≤ (4 * (H : ℝ) / A) ^ 2 := by
    intro ξ
    have h1 := norm_fourier_slice_window_le ((A : ℝ) / H) hT eta hηs.continuous
      hη01 hη2 ξ
    have h2 : (4 : ℝ) / ((A : ℝ) / H) = 4 * (H : ℝ) / A := by field_simp
    rw [h2] at h1
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hwdecay : ∀ ξ : ℝ, ξ ≠ 0 →
      w ξ ≤ (2 * explicitSliceWindowDerivBound epsGeom / (π * |ξ|)) ^ 2 := by
    intro ξ hξ
    have h1 := norm_fourier_slice_window_decay ((A : ℝ) / H) hT eta hηs hη2
      (explicitSliceWindowDerivBound epsGeom) hB0 hderiv hd2 ξ hξ
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  obtain ⟨hcs, hcd⟩ := window_profile_props ((A : ℝ) / H) hT eta hηs hη2
  set G : SchwartzMap ℝ ℂ := hcs.toSchwartzMap hcd with hG_def
  have hwG : w = fun ξ => ‖(𝓕 G) ξ‖ ^ 2 := rfl
  have hwm : Measurable w := by
    rw [hwG]
    exact ((𝓕 G).continuous.norm.pow 2).measurable
  have hwC' : ∀ ξ, ‖w ξ‖ ≤ (4 * (H : ℝ) / A) ^ 2 := by
    intro ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (hw0 ξ)]
    exact hwC ξ
  have hint : IntegrableOn (fun ξ => ‖P ξ‖ ^ 2 * w ξ) {ξ : ℝ | |ξ| ≤ L} := by
    refine integrableOn_norm_sq_mul_inner_band P hPcont w hwm
      ((4 * (H : ℝ) / A) ^ 2) hwC' 0 L _ ?_
    intro ξ hξ
    exact ⟨abs_nonneg ξ, hξ⟩
  have hintLow : IntegrableOn (fun ξ => ‖P ξ‖ ^ 2) {ξ : ℝ | |ξ| < K} := by
    refine integrableOn_norm_sq_inner_band P hPcont 0 K _ ?_
    intro ξ hξ
    exact ⟨abs_nonneg ξ, le_of_lt hξ⟩
  have hf0 : ∀ ξ, 0 ≤ ‖P ξ‖ ^ 2 * w ξ :=
    fun ξ => mul_nonneg (by positivity) (hw0 ξ)
  have hmeasO : MeasurableSet {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L} :=
    measurableSet_inner_band K₂ L
  have hmeasO' : MeasurableSet {ξ : ℝ | K₂ < |ξ| ∧ |ξ| ≤ L} :=
    (measurableSet_lt measurable_const measurable_abs).inter
      (measurableSet_le measurable_abs measurable_const)
  have hintI : IntegrableOn (fun ξ => ‖P ξ‖ ^ 2 * w ξ)
      {ξ : ℝ | K ≤ |ξ| ∧ |ξ| ≤ K₂} :=
    hint.mono_set (fun ξ hξ => le_trans hξ.2 hK₂L)
  have hintO' : IntegrableOn (fun ξ => ‖P ξ‖ ^ 2 * w ξ)
      {ξ : ℝ | K₂ < |ξ| ∧ |ξ| ≤ L} :=
    hint.mono_set (fun ξ hξ => hξ.2)
  have hintO : IntegrableOn (fun ξ => ‖P ξ‖ ^ 2 * w ξ)
      {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L} :=
    hint.mono_set (fun ξ hξ => hξ.2)
  have hsplit :
      (∫ ξ in {ξ : ℝ | K ≤ |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖ ^ 2 * w ξ) ≤
        (∫ ξ in {ξ : ℝ | K ≤ |ξ| ∧ |ξ| ≤ K₂}, ‖P ξ‖ ^ 2 * w ξ) +
          ∫ ξ in {ξ : ℝ | K₂ < |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖ ^ 2 * w ξ := by
    have hcover : {ξ : ℝ | K ≤ |ξ| ∧ |ξ| ≤ L} ⊆
        {ξ : ℝ | K ≤ |ξ| ∧ |ξ| ≤ K₂} ∪
          {ξ : ℝ | K₂ < |ξ| ∧ |ξ| ≤ L} := by
      intro ξ hξ
      rcases le_or_gt |ξ| K₂ with h1 | h1
      · exact Or.inl ⟨hξ.1, h1⟩
      · exact Or.inr ⟨h1, hξ.2⟩
    have hdisj : Disjoint {ξ : ℝ | K ≤ |ξ| ∧ |ξ| ≤ K₂}
        {ξ : ℝ | K₂ < |ξ| ∧ |ξ| ≤ L} := by
      rw [Set.disjoint_left]
      intro ξ h1 h2
      exact absurd h1.2 (not_le.mpr h2.1)
    calc
      (∫ ξ in {ξ : ℝ | K ≤ |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖ ^ 2 * w ξ)
          ≤ ∫ ξ in {ξ : ℝ | K ≤ |ξ| ∧ |ξ| ≤ K₂} ∪
              {ξ : ℝ | K₂ < |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖ ^ 2 * w ξ :=
        setIntegral_mono_set (hintI.union hintO')
          (Filter.Eventually.of_forall hf0) hcover.eventuallyLE
      _ = _ := setIntegral_union hdisj hmeasO' hintI hintO'
  have houter :
      (∫ ξ in {ξ : ℝ | K₂ < |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖ ^ 2 * w ξ) ≤
        (4 * explicitSliceWindowDerivBound epsGeom ^ 2 / π ^ 2) *
          ((2 * (A : ℝ) + 1) ^ 2 *
            (Real.exp Real.pi * ((4 / (K₂ * (A : ℝ))) + (6 / K₂ ^ 2)) *
              (∑ n ∈ Finset.Ioc A (A + s + 2 * H + 4 * U), (1 : ℝ) / n))) := by
    have h1 :
        (∫ ξ in {ξ : ℝ | K₂ < |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖ ^ 2 * w ξ) ≤
          ∫ ξ in {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖ ^ 2 * w ξ :=
      setIntegral_mono_set hintO (Filter.Eventually.of_forall hf0)
        (Filter.Eventually.of_forall fun ξ hξ => ⟨le_of_lt hξ.1, hξ.2⟩)
    set w₂ : ℝ → ℝ := fun ξ =>
      (2 * explicitSliceWindowDerivBound epsGeom / (π * max |ξ| K₂)) ^ 2 with hw₂_def
    have hw₂m : Measurable w₂ := by
      apply Measurable.pow_const
      apply Measurable.div measurable_const
      exact measurable_const.mul (measurable_abs.max measurable_const)
    have hw₂bdd : ∀ ξ,
        ‖w₂ ξ‖ ≤ (2 * explicitSliceWindowDerivBound epsGeom / (π * K₂)) ^ 2 := by
      intro ξ
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hmax : K₂ ≤ max |ξ| K₂ := le_max_right _ _
      have hpos : 0 < π * K₂ := by positivity
      have hle : 2 * explicitSliceWindowDerivBound epsGeom / (π * max |ξ| K₂) ≤
          2 * explicitSliceWindowDerivBound epsGeom / (π * K₂) := by
        apply div_le_div_of_nonneg_left (by positivity) hpos
        exact mul_le_mul_of_nonneg_left hmax Real.pi_pos.le
      exact pow_le_pow_left₀ (by positivity) hle 2
    have hint₂ : IntegrableOn (fun ξ => ‖P ξ‖ ^ 2 * w₂ ξ)
        {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L} :=
      integrableOn_norm_sq_mul_inner_band P hPcont w₂ hw₂m _ hw₂bdd K₂ L _
        (Set.Subset.refl _)
    have h2 :
        (∫ ξ in {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖ ^ 2 * w ξ) ≤
          ∫ ξ in {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖ ^ 2 * w₂ ξ := by
      refine setIntegral_weight_mono (fun ξ => ‖P ξ‖ ^ 2) w w₂
        (fun ξ => by positivity) _ hmeasO ?_ hintO hint₂
      intro ξ hξ
      have hξ0 : ξ ≠ 0 := by
        intro h0
        have hk : K₂ ≤ |ξ| := hξ.1
        rw [h0, abs_zero] at hk
        exact absurd hk (not_le.mpr hK₂)
      have hd := hwdecay ξ hξ0
      have hmax : max |ξ| K₂ = |ξ| := max_eq_left hξ.1
      simp only [hw₂_def, hmax]
      exact hd
    have h3 :
        (∫ ξ in {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖ ^ 2 * w₂ ξ) =
          ∫ ξ in {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L},
            ‖P ξ‖ ^ 2 *
              (2 * explicitSliceWindowDerivBound epsGeom / (π * |ξ|)) ^ 2 := by
      refine setIntegral_congr_fun hmeasO ?_
      intro ξ hξ
      simp only [hw₂_def, max_eq_left hξ.1]
    have h4 := band_energy_outer_le A (s + 2 * H + 4 * U) (by omega) hΔA
      (Finset.Ioc A (A + (s + 2 * H + 4 * U))) (Finset.Subset.refl _) h hb
      (explicitSliceWindowDerivBound epsGeom) K₂ L hB0 hK₂ J hJ
    have hIoc : A + (s + 2 * H + 4 * U) = A + s + 2 * H + 4 * U := by omega
    simp only [hIoc] at h4
    calc
      (∫ ξ in {ξ : ℝ | K₂ < |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖ ^ 2 * w ξ)
          ≤ ∫ ξ in {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖ ^ 2 * w ξ := h1
      _ ≤ ∫ ξ in {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖ ^ 2 * w₂ ξ := h2
      _ = ∫ ξ in {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L},
            ‖P ξ‖ ^ 2 *
              (2 * explicitSliceWindowDerivBound epsGeom / (π * |ξ|)) ^ 2 := h3
      _ ≤ _ := h4
  have hmid :
      (∫ ξ in {ξ : ℝ | K ≤ |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖ ^ 2 * w ξ) ≤
        Einner + (4 * explicitSliceWindowDerivBound epsGeom ^ 2 / π ^ 2) *
          ((2 * (A : ℝ) + 1) ^ 2 *
            (Real.exp Real.pi * ((4 / (K₂ * (A : ℝ))) + (6 / K₂ ^ 2)) *
              (∑ n ∈ Finset.Ioc A (A + s + 2 * H + 4 * U), (1 : ℝ) / n))) :=
    hsplit.trans (add_le_add (hinner w hwm hw0 hwC) houter)
  have hwin := window_energy_le_of_low_mid h A s H U hA hH eta hηs hη2 K L Mtot
    ((A : ℝ) / H * explicitSliceWindowDerivBound epsGeom ^ 2 / π ^ 2)
    ((4 * (H : ℝ) / A) ^ 2) Elow _ hL hKL (by positivity)
    htot hG3c hwC hint hintLow hlow hmid
  linarith [hwin]

end MoltResearch
