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


open MeasureTheory in
/-- **G4, the pivot** (Track R, A2-II): the slice frequency energy
through the regime split — for `1`-bounded-in-norm `h` on the slice
index range `S`, the smoothed-window line energy is priced by the
low-band interval energy of the *plain* phase polynomial (the weight
identity `4H·(A/H)·(h·m/(4A))/m = h`), the mid-regime sup, and the
derivative-energy tail:

  `∫‖4H·sLS‖² ≤ (4H/A)²·∫_{−K}^{K}‖P‖² + Mmid²·(4H/A) + Mtot²·Eder/L²`.

`smoothedLogSum_eq_sum_translates` + `window_profile_props` put the
integrand in the harness's translate class; `regime_split` does the
work; G3 supplies the window constants. -/
theorem window_energy_regime_le (h : ℕ → ℂ)
    (A s H U : ℕ) (hA : 1 ≤ A) (hH : 0 < H)
    (η : ℝ → ℝ) (hηs : ContDiff ℝ ∞ η)
    (hη01 : ∀ u, 0 ≤ η u ∧ η u ≤ 1) (hη2 : ∀ u, η u ≠ 0 → |u| ≤ 2)
    (K L Mmid Mtot Eder : ℝ) (hK : 0 ≤ K) (hL : 0 < L)
    (hMmid0 : 0 ≤ Mmid)
    (hmid : ∀ ξ : ℝ, K ≤ |ξ| → |ξ| ≤ L →
      ‖∑ m ∈ Finset.Ioc A (A+s+2*H+4*U),
        h m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖ ≤ Mmid)
    (htot : ∀ ξ : ℝ,
      ‖∑ m ∈ Finset.Ioc A (A+s+2*H+4*U),
        h m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖ ≤ Mtot)
    (hder : ∫ ξ, ξ^2 * ‖𝓕 (fun v =>
        ((η (((A:ℝ)/H)*v) : ℝ) : ℂ)) ξ‖^2 ≤ Eder) :
    ∫ y, ‖(4*(H:ℂ)) * smoothedLogSum ((A:ℝ)/H) η
        (fun m => if m ∈ Finset.Ioc A (A+s+2*H+4*U)
          then h m * (m:ℂ)/(4*(A:ℂ)) else 0)
        (Finset.Ioc A (A+s+2*H+4*U)) y‖^2
      ≤ (4*(H:ℝ)/A)^2
          * (∫ ξ in (-K)..K, ‖∑ m ∈ Finset.Ioc A (A+s+2*H+4*U),
              h m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2)
        + Mmid^2 * (4*(H:ℝ)/A) + Mtot^2 * ((1/L^2) * Eder) := by
  classical
  have hAR : (0:ℝ) < (A:ℝ) := by exact_mod_cast (by omega : 0 < A)
  have hHR : (0:ℝ) < (H:ℝ) := by exact_mod_cast hH
  set T : ℝ := (A:ℝ)/H with hT_def
  have hT : 0 < T := by positivity
  set S : Finset ℕ := Finset.Ioc A (A+s+2*H+4*U) with hS_def
  set F : ℝ → ℂ := fun v => ((η (T*v) : ℝ) : ℂ) with hF_def
  obtain ⟨hFc, hFs⟩ := window_profile_props T hT η hηs hη2
  -- the weight identity: the translate weights are the raw `h`
  have htrans : ∀ y : ℝ, (4*(H:ℂ)) * smoothedLogSum T η
      (fun m => if m ∈ S then h m * (m:ℂ)/(4*(A:ℂ)) else 0) S y
      = ∑ m ∈ S, h m * F (y - Real.log m) := by
    intro y
    rw [smoothedLogSum_eq_sum_translates, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [if_pos hm]
    have hm1 : 1 ≤ m := by
      rw [hS_def, Finset.mem_Ioc] at hm
      omega
    have hmC : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hAC : ((A:ℕ):ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hHC : ((H:ℕ):ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hTC : ((T:ℝ):ℂ) = ((A:ℕ):ℂ)/((H:ℕ):ℂ) := by
      rw [hT_def]
      push_cast
      ring
    rw [hF_def, hTC]
    field_simp
  have hcongr : ∫ y, ‖(4*(H:ℂ)) * smoothedLogSum T η
      (fun m => if m ∈ S then h m * (m:ℂ)/(4*(A:ℂ)) else 0) S y‖^2
      = ∫ y, ‖∑ m ∈ S, h m * F (y - Real.log m)‖^2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => by
      simpa using congrArg (fun z : ℂ => ‖z‖^2) (htrans y))
  rw [hcongr]
  -- the regime split
  have hsplit := integral_norm_sq_sum_translates_regime_split F hFc hFs
    S h (fun m => Real.log m) K L Mmid Mtot hL hMmid0
    (fun ξ h1 h2 => hmid ξ h1 h2) (fun ξ => htot ξ)
  refine le_trans hsplit ?_
  -- the phase polynomial and its continuity
  set P : ℝ → ℂ := fun ξ => ∑ m ∈ S,
      h m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)
    with hP_def
  have hPc : Continuous P := by
    rw [hP_def]
    refine continuous_finset_sum _ fun m _ => ?_
    exact continuous_const.mul
      (Continuous.comp continuous_subtype_val
        (Real.continuous_fourierChar.comp (by fun_prop)))
  -- low band: sup out the window transform, then close the ball
  have hFsup : ∀ ξ : ℝ, ‖𝓕 F ξ‖ ≤ 4/T := by
    intro ξ
    rw [hF_def]
    exact norm_fourier_slice_window_le T hT η hηs.continuous hη01 hη2 ξ
  have hFF : Continuous (𝓕 F) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by fun_prop) (hFs.continuous.integrable_of_hasCompactSupport hFc)
  have hlow : ∫ ξ in {ξ : ℝ | |ξ| < K}, ‖P ξ‖^2 * ‖𝓕 F ξ‖^2
      ≤ (4/T)^2 * ∫ ξ in (-K)..K, ‖P ξ‖^2 := by
    have hball : {ξ : ℝ | |ξ| < K} = Set.Ioo (-K) K := by
      ext ξ
      simp [abs_lt]
    have hint1 : IntegrableOn (fun ξ => ‖P ξ‖^2 * ‖𝓕 F ξ‖^2)
        (Set.Ioo (-K) K) :=
      (((hPc.norm.pow 2).mul (hFF.norm.pow 2)).integrableOn_Icc).mono_set
        Set.Ioo_subset_Icc_self
    have hint2 : IntegrableOn (fun ξ => (4/T)^2 * ‖P ξ‖^2)
        (Set.Ioo (-K) K) :=
      ((continuous_const.mul (hPc.norm.pow 2)).integrableOn_Icc).mono_set
        Set.Ioo_subset_Icc_self
    have hmono : ∫ ξ in Set.Ioo (-K) K, ‖P ξ‖^2 * ‖𝓕 F ξ‖^2
        ≤ ∫ ξ in Set.Ioo (-K) K, (4/T)^2 * ‖P ξ‖^2 := by
      refine setIntegral_mono_on hint1 hint2 measurableSet_Ioo fun ξ _ => ?_
      have h1 := hFsup ξ
      have h2 : ‖𝓕 F ξ‖^2 ≤ (4/T)^2 := by
        have h40 : (0:ℝ) ≤ 4/T := by positivity
        nlinarith [norm_nonneg (𝓕 F ξ)]
      nlinarith [sq_nonneg ‖P ξ‖, norm_nonneg (P ξ)]
    have hIoo_le : ∫ ξ in Set.Ioo (-K) K, (4/T)^2 * ‖P ξ‖^2
        ≤ (4/T)^2 * ∫ ξ in (-K)..K, ‖P ξ‖^2 := by
      rw [intervalIntegral.integral_of_le (by linarith),
        ← integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
    rw [hball]
    linarith [hmono, hIoo_le]
  -- middle: the window mass
  have hmidE : Mmid^2 * (∫ ξ, ‖𝓕 F ξ‖^2) ≤ Mmid^2 * (4/T) := by
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg Mmid)
    rw [hF_def]
    exact integral_norm_sq_fourier_slice_window_le T hT η hηs hη01 hη2
  -- tail: the derivative energy
  have htailE : Mtot^2 * ((1/L^2) * ∫ ξ, ξ^2 * ‖𝓕 F ξ‖^2)
      ≤ Mtot^2 * ((1/L^2) * Eder) := by
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg Mtot)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hF_def, hT_def]
    exact hder
  -- the T-arithmetic and assembly
  have hTid : 4/T = 4*(H:ℝ)/A := by
    rw [hT_def]
    field_simp
  rw [hTid] at hlow hmidE
  linarith [hlow, hmidE, htailE]

end ExpSums

end MoltResearch
