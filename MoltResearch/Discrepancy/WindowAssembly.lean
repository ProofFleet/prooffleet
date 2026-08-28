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


open MeasureTheory in
/-- **G5: the plain band energy through the `𝒰`-recursion** (Track R,
A2-II): the plain phase polynomial of a `1`-bounded `h` on a
near-dyadic range rescales into the Ramaré multi-level energy —

  `∫_{−K}^{K} ‖∑_{m∈S} h(m)e(−ξ log m)‖² ≤ (2a+1)²·uBound K levels a b`,

by `c(m) := m·h(m)/(2a+1)` (still `1`-bounded on the range) and
`intervalIntegral_norm_sq_subset_le`. -/
theorem intervalIntegral_norm_sq_plain_le (K : ℝ) (hK : 0 ≤ K)
    (levels : List (Finset ℕ)) (hlv : ∀ P ∈ levels, ∀ q ∈ P, q.Prime)
    (a b : ℕ) (hab : b ≤ 2*a+1)
    (S : Finset ℕ) (hS : S ⊆ Finset.Ioc a b)
    (h : ℕ → ℂ) (hb : ∀ m, ‖h m‖ ≤ 1) :
    ∫ ξ in (-K)..K, ‖∑ m ∈ S,
        h m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
      ≤ (2*(a:ℝ)+1)^2 * uBound K levels a b := by
  classical
  set c : ℕ → ℂ := fun m => if m ≤ 2*a+1
      then (m:ℂ) * h m / (2*(a:ℕ)+1 : ℕ) else 0 with hc_def
  have hcb : ∀ m, ‖c m‖ ≤ 1 := by
    intro m
    simp only [hc_def]
    by_cases hm : m ≤ 2*a+1
    · rw [if_pos hm, norm_div, norm_mul, Complex.norm_natCast,
        Complex.norm_natCast]
      have hden : (0:ℝ) < ((2*a+1 : ℕ):ℝ) := by
        exact_mod_cast (by omega : 0 < 2*a+1)
      rw [div_le_one hden]
      have h1 : (m:ℝ) ≤ ((2*a+1 : ℕ):ℝ) := by exact_mod_cast hm
      have h2 := hb m
      nlinarith [norm_nonneg (h m), Nat.cast_nonneg (α := ℝ) m]
    · rw [if_neg hm]
      simp
  have hpoint : ∀ ξ : ℝ, ‖∑ m ∈ S,
      h m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
      = (2*(a:ℝ)+1)^2 * ‖∑ m ∈ S, (c m/(m:ℂ))
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2 := by
    intro ξ
    have hfac : ∑ m ∈ S,
        h m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)
        = ((2*(a:ℕ)+1 : ℕ):ℂ) * ∑ m ∈ S, (c m/(m:ℂ))
            * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hmIoc := hS hm
      rw [Finset.mem_Ioc] at hmIoc
      have hmle : m ≤ 2*a+1 := by omega
      have hm0 : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hden : ((2*(a:ℕ)+1 : ℕ):ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (by omega)
      simp only [hc_def, if_pos hmle]
      field_simp
    rw [hfac, norm_mul, Complex.norm_natCast, mul_pow]
    congr 2
    push_cast
    ring
  rw [intervalIntegral.integral_congr
    (fun ξ _ => hpoint ξ), intervalIntegral.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact intervalIntegral_norm_sq_subset_le K hK levels hlv a b hab S hS c hcb


/-- **G7-i: the phase weight is the archimedean twist** (Track R,
A2-III): `e(−ξ·log m) = m^{−2πiξ·i}` — the band polynomial's weight is
a completely multiplicative unimodular twist, so the block sum is a
difference of prefix sums of a twisted multiplicative function. -/
theorem archTwist_phase_eq (ξ : ℝ) (m : ℕ) (hm : m ≠ 0) :
    ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)
      = (m:ℂ)^(Complex.I*((-(2*Real.pi*ξ) : ℝ):ℂ)) := by
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hmc : ((m:ℕ):ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hlog : Complex.log ((m:ℕ):ℂ) = ((Real.log m : ℝ) : ℂ) := by
    rw [show ((m:ℕ):ℂ) = (((m:ℝ) : ℝ) : ℂ) by push_cast; rfl]
    exact (Complex.ofReal_log hm0.le).symm
  rw [Real.fourierChar_apply, Complex.cpow_def_of_ne_zero hmc, hlog]
  congr 1
  push_cast
  ring

open Finset in
/-- **G7-ii: non-pretentiousness transfers down in scale** (Track R,
A2-III): an `A`-floor at truncation `x` gives an `A′`-floor at any
truncation `z ≤ x`, at the price of twice the prime-mass difference —
`pretentiousDistSq_le_add_mass` read backwards. -/
theorem nonPretentiousAt_scale_transfer {g : ℕ → ℂ}
    (hg : ∀ p, ‖g p‖ ≤ 1) {A A' : ℝ} {x z : ℕ}
    (h : NonPretentiousAt g A x) (hzx : z ≤ x) (hA'0 : 0 ≤ A')
    (hA' : A' ≤ A - 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
      - (∑ p ∈ z.primesBelow, (1:ℝ)/p))) :
    NonPretentiousAt g A' z := by
  intro q χ t hq ht
  have hΔ0 : (0:ℝ) ≤ (∑ p ∈ x.primesBelow, (1:ℝ)/p)
      - ∑ p ∈ z.primesBelow, (1:ℝ)/p := by
    have hsub : z.primesBelow ⊆ x.primesBelow := by
      intro p hp
      rw [Nat.mem_primesBelow] at hp ⊢
      exact ⟨lt_of_lt_of_le hp.1 hzx, hp.2⟩
    have hmono : ∑ p ∈ z.primesBelow, (1:ℝ)/p
        ≤ ∑ p ∈ x.primesBelow, (1:ℝ)/p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun p _ _ => div_nonneg zero_le_one (Nat.cast_nonneg p))
    linarith
  have hq' : (q:ℝ) ≤ A := le_trans hq (by linarith)
  have hzr : (z:ℝ) ≤ (x:ℝ) := by exact_mod_cast hzx
  have ht' : |t| ≤ A*(x:ℝ) := by
    have hz0 : (0:ℝ) ≤ (z:ℝ) := Nat.cast_nonneg _
    have hAA' : A' ≤ A := by linarith
    calc |t| ≤ A'*(z:ℝ) := ht
      _ ≤ A*(x:ℝ) := by nlinarith
  have hx := h q χ t hq' ht'
  have htrans := pretentiousDistSq_le_add_mass g (charTwist q χ t)
    (fun p => hg p) (fun p => charTwist_norm_le_one q χ t p) hzx
  linarith

open Finset in
/-- **G7-iii: a block sum is two prefix sums** (Track R, A2-III): if
both prefix sums of `f` are at most `E`, the block sum is at most
`2E` — the mid-regime sup from the plain-sum Halász, no partial
summation needed. -/
theorem norm_sum_Ioc_le_two_prefix (f : ℕ → ℂ) (a b : ℕ) (hab : a ≤ b)
    (E : ℝ)
    (hEa : ‖∑ m ∈ Finset.Icc 1 a, f m‖ ≤ E)
    (hEb : ‖∑ m ∈ Finset.Icc 1 b, f m‖ ≤ E) :
    ‖∑ m ∈ Finset.Ioc a b, f m‖ ≤ 2*E := by
  classical
  have hunion : Finset.Icc 1 a ∪ Finset.Ioc a b = Finset.Icc 1 b := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 a) (Finset.Ioc a b) := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_Ioc] at hn'
    omega
  have hsplit : ∑ m ∈ Finset.Icc 1 b, f m
      = (∑ m ∈ Finset.Icc 1 a, f m) + ∑ m ∈ Finset.Ioc a b, f m := by
    rw [← hunion, Finset.sum_union hdisj]
  have hdiff : ∑ m ∈ Finset.Ioc a b, f m
      = (∑ m ∈ Finset.Icc 1 b, f m) - ∑ m ∈ Finset.Icc 1 a, f m := by
    rw [hsplit]
    ring
  rw [hdiff]
  calc ‖(∑ m ∈ Finset.Icc 1 b, f m) - ∑ m ∈ Finset.Icc 1 a, f m‖
      ≤ ‖∑ m ∈ Finset.Icc 1 b, f m‖ + ‖∑ m ∈ Finset.Icc 1 a, f m‖ :=
        norm_sub_le _ _
    _ ≤ 2*E := by linarith


open Finset in
/-- **G8: slice aggregation** (Track R, A2-III): per-slice bounds sum
over the `B2′` slice partition to a bound on the full range. -/
theorem sum_Ioc_le_of_slice_bounds (A s J : ℕ) (f : ℕ → ℝ) (B : ℕ → ℝ)
    (hslice : ∀ j ∈ Finset.range J,
      ∑ n ∈ Finset.Ioc (A + j*s) (A + (j+1)*s), f n ≤ B j) :
    ∑ n ∈ Finset.Ioc A (A + J*s), f n ≤ ∑ j ∈ Finset.range J, B j := by
  rw [← sum_range_sum_Ioc_slices]
  exact Finset.sum_le_sum hslice

open Finset in
/-- **G8, uniform form** (Track R, A2-III): a uniform per-slice budget
costs `J` times itself. -/
theorem sum_Ioc_le_of_slice_bounds_const (A s J : ℕ) (f : ℕ → ℝ) (B : ℝ)
    (hslice : ∀ j ∈ Finset.range J,
      ∑ n ∈ Finset.Ioc (A + j*s) (A + (j+1)*s), f n ≤ B) :
    ∑ n ∈ Finset.Ioc A (A + J*s), f n ≤ (J:ℝ) * B := by
  refine le_trans (sum_Ioc_le_of_slice_bounds A s J f (fun _ => B) hslice) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]


open MeasureTheory SchwartzMap LineDeriv in
/-- **G3c: the slice-window derivative energy** (Track R, A2-II): the
frequency-weighted transform energy of the profile `v ↦ η(Tv)` is
priced by the derivative bound —

  `∫ ξ²‖𝓕F‖² ≤ T·B′²/π²`,

via the derivative Plancherel identity, the chain rule
(`∂F = T·η′(T·)`), and the support/sup argument.  `B′` and the
derivative support come from `exists_deriv_bound`. -/
theorem integral_sq_norm_fourier_slice_window_le (T : ℝ) (hT : 0 < T)
    (η : ℝ → ℝ) (hηs : ContDiff ℝ ∞ η)
    (hη2 : ∀ u, η u ≠ 0 → |u| ≤ 2)
    (B' : ℝ) (hB'0 : 0 ≤ B') (hB' : ∀ u, |deriv η u| ≤ B')
    (hd2 : ∀ u, deriv η u ≠ 0 → |u| ≤ 2) :
    ∫ ξ, ξ^2 * ‖𝓕 (fun v => ((η (T*v) : ℝ) : ℂ)) ξ‖^2
      ≤ T * B'^2 / π^2 := by
  obtain ⟨hcs, hcd⟩ := window_profile_props T hT η hηs hη2
  set G : SchwartzMap ℝ ℂ := hcs.toSchwartzMap hcd with hG_def
  have hfun : (fun v : ℝ => ((η (T*v) : ℝ) : ℂ)) = ⇑G := funext fun y => rfl
  rw [hfun]
  have hid := integral_sq_mul_norm_fourier_sq G
  -- pointwise derivative of the profile
  have hderiv : ∀ y : ℝ, (∂_{(1:ℝ)} G) y
      = ((T * deriv η (T*y) : ℝ) : ℂ) := by
    intro y
    rw [lineDerivOp_apply_eq_fderiv]
    have hηd : HasDerivAt η (deriv η (T*y)) (T*y) :=
      ((hηs.differentiable (by norm_num)) (T*y)).hasDerivAt
    have hTd : HasDerivAt (fun v : ℝ => T*v) T y := by
      simpa using (hasDerivAt_id y).const_mul T
    have hcomp : HasDerivAt (fun v : ℝ => η (T*v))
        (deriv η (T*y) * T) y := hηd.comp y hTd
    have hC : HasDerivAt (fun v : ℝ => ((η (T*v) : ℝ) : ℂ))
        ((deriv η (T*y) * T : ℝ) : ℂ) y := hcomp.ofReal_comp
    have hfd : fderiv ℝ (⇑G) y 1 = deriv (⇑G) y := fderiv_deriv
    rw [hfd]
    have hdG : deriv (⇑G) y = ((deriv η (T*y) * T : ℝ) : ℂ) := by
      rw [← hfun]
      exact hC.deriv
    rw [hdG]
    push_cast
    ring
  -- the derivative vanishes off the support window
  have hsupp : ∀ y : ℝ, y ∉ Set.Icc (-(2/T)) (2/T) →
      (∂_{(1:ℝ)} G) y = 0 := by
    intro y hy
    rw [hderiv y]
    have hzero : deriv η (T*y) = 0 := by
      by_contra hne
      have h2 := hd2 _ hne
      rw [abs_le] at h2
      rw [Set.mem_Icc, not_and_or] at hy
      have hid2 : T * (2/T) = 2 := by field_simp
      rcases hy with h | h
      · push_neg at h
        have := mul_lt_mul_of_pos_left h hT
        nlinarith [h2.1]
      · push_neg at h
        have := mul_lt_mul_of_pos_left h hT
        nlinarith [h2.2]
    rw [hzero]
    simp
  -- the derivative energy
  have hcont : Continuous (fun y : ℝ => ‖(∂_{(1:ℝ)} G) y‖^2) :=
    ((∂_{(1:ℝ)} G).continuous.norm.pow 2)
  have hcsD : HasCompactSupport (fun y : ℝ => ‖(∂_{(1:ℝ)} G) y‖^2) := by
    refine HasCompactSupport.intro
      (isCompact_Icc (a := -(2/T)) (b := 2/T)) ?_
    intro y hy
    rw [hsupp y hy]
    simp
  have hint : Integrable (fun y : ℝ => ‖(∂_{(1:ℝ)} G) y‖^2) :=
    hcont.integrable_of_hasCompactSupport hcsD
  have hE : ∫ y, ‖(∂_{(1:ℝ)} G) y‖^2 ≤ (4/T) * (T*B')^2 := by
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Set.Icc (-(2/T)) (2/T))
      (fun y hy => by rw [hsupp y hy]; simp)]
    have hnorm_le : ∀ y ∈ Set.Icc (-(2/T)) (2/T),
        ‖(∂_{(1:ℝ)} G) y‖^2 ≤ (T*B')^2 := by
      intro y _
      rw [hderiv y, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos hT]
      have h1 := hB' (T*y)
      have h2 : (0:ℝ) ≤ |deriv η (T*y)| := abs_nonneg _
      have h3 : T * |deriv η (T*y)| ≤ T*B' :=
        mul_le_mul_of_nonneg_left h1 hT.le
      have h4 : (0:ℝ) ≤ T * |deriv η (T*y)| := mul_nonneg hT.le h2
      exact pow_le_pow_left₀ h4 h3 2
    calc ∫ y in Set.Icc (-(2/T)) (2/T), ‖(∂_{(1:ℝ)} G) y‖^2
        ≤ ∫ _ in Set.Icc (-(2/T)) (2/T), (T*B')^2 := by
          refine setIntegral_mono_on hint.integrableOn
            (integrableOn_const measure_Icc_lt_top.ne)
            measurableSet_Icc hnorm_le
      _ = (4/T) * (T*B')^2 := by
          rw [setIntegral_const, smul_eq_mul,
            MeasureTheory.measureReal_def, Real.volume_Icc,
            ENNReal.toReal_ofReal (by
              have h4 : (0:ℝ) < 2/T := by positivity
              linarith : (0:ℝ) ≤ 2/T - (-(2/T)))]
          ring
  have hπ2 : (0:ℝ) < π^2 := by positivity
  have hgoal : (4*π^2) * (∫ ξ, ξ^2 * ‖𝓕 (⇑G) ξ‖^2) ≤ 4*(T*B'^2) := by
    have hid' : (4*π^2) * (∫ ξ, ξ^2 * ‖𝓕 (⇑G) ξ‖^2)
        = ∫ y, ‖(∂_{(1:ℝ)} G) y‖^2 := hid
    rw [hid']
    calc ∫ y, ‖(∂_{(1:ℝ)} G) y‖^2 ≤ (4/T) * (T*B')^2 := hE
      _ = 4*(T*B'^2) := by field_simp
  rw [le_div_iff₀ hπ2]
  linarith [hgoal]


open Metric in
/-- **The bump window with exported radii** (Track R, A2): the variant
of `exists_bump_window` exposing the `ContDiffBump` structure and its
exact radii — `rIn = T(t₂−t₁)/2`, `rOut − rIn = T·min(t₁−t₀, t₃−t₂)` —
so the uniform derivative bound (`exists_bump_deriv_bound`) can price
the window's Lipschitz data explicitly. -/
theorem exists_bump_window' (T t₀ t₁ t₂ t₃ : ℝ) (hT : 0 < T) (h0 : 0 < t₀)
    (h01 : t₀ < t₁) (h12 : t₁ < t₂) (h23 : t₂ < t₃) (h3 : T * t₃ ≤ 2) :
    ∃ (c : ℝ) (f : ContDiffBump c),
      f.rIn = T*(t₂-t₁)/2
      ∧ f.rOut = T*(t₂-t₁)/2 + T*(min (t₁-t₀) (t₃-t₂))
      ∧ ContDiff ℝ ∞ (⇑f) ∧ (∀ u, 0 ≤ f u ∧ f u ≤ 1)
      ∧ (∀ u, -(T*t₂) ≤ u → u ≤ -(T*t₁) → f u = 1)
      ∧ (∀ u, f u ≠ 0 → -(T*t₃) < u ∧ u < -(T*t₀))
      ∧ (∀ u, f u ≠ 0 → |u| ≤ 2) := by
  classical
  set c : ℝ := -(T*(t₁+t₂)/2) with hc_def
  set rIn : ℝ := T*(t₂-t₁)/2 with hrIn_def
  set rOut : ℝ := rIn + T*(min (t₁-t₀) (t₃-t₂)) with hrOut_def
  have hrIn_pos : 0 < rIn := by
    rw [hrIn_def]
    nlinarith
  have hmin_pos : 0 < min (t₁-t₀) (t₃-t₂) := by
    rw [lt_min_iff]
    constructor <;> linarith
  have hrlt : rIn < rOut := by
    rw [hrOut_def]
    nlinarith
  set f : ContDiffBump c := ⟨rIn, rOut, hrIn_pos, hrlt⟩ with hf_def
  refine ⟨c, f, rfl, by rw [hrOut_def, hrIn_def], f.contDiff,
    fun u => ⟨f.nonneg, f.le_one⟩, ?_, ?_, ?_⟩
  · -- the plateau
    intro u h1 h2
    refine f.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, Real.dist_eq]
    show |u - c| ≤ rIn
    rw [abs_le]
    have hcv : c = -(T*(t₁+t₂)/2) := hc_def
    have hrv : rIn = T*(t₂-t₁)/2 := hrIn_def
    constructor <;> nlinarith [hcv, hrv]
  · -- the support
    intro u hne
    have hmem : u ∈ Function.support (fun u => f u) := hne
    rw [f.support_eq, Metric.mem_ball, Real.dist_eq] at hmem
    have hmem' : |u - c| < rOut := hmem
    rw [abs_lt] at hmem'
    have hmin1 : min (t₁-t₀) (t₃-t₂) ≤ t₁-t₀ := min_le_left _ _
    have hmin2 : min (t₁-t₀) (t₃-t₂) ≤ t₃-t₂ := min_le_right _ _
    have hcv : c = -(T*(t₁+t₂)/2) := hc_def
    have hrv : rOut = T*(t₂-t₁)/2 + T*(min (t₁-t₀) (t₃-t₂)) := by
      rw [hrOut_def, hrIn_def]
    constructor
    · nlinarith [hmem'.1, hcv, hrv]
    · nlinarith [hmem'.2, hcv, hrv]
  · -- the support is within [−2, 2]
    intro u hne
    have hmem : u ∈ Function.support (fun u => f u) := hne
    rw [f.support_eq, Metric.mem_ball, Real.dist_eq] at hmem
    have hmem' : |u - c| < rOut := hmem
    rw [abs_lt] at hmem'
    have hmin1 : min (t₁-t₀) (t₃-t₂) ≤ t₁-t₀ := min_le_left _ _
    have hmin2 : min (t₁-t₀) (t₃-t₂) ≤ t₃-t₂ := min_le_right _ _
    have hcv : c = -(T*(t₁+t₂)/2) := hc_def
    have hrv : rOut = T*(t₂-t₁)/2 + T*(min (t₁-t₀) (t₃-t₂)) := by
      rw [hrOut_def, hrIn_def]
    rw [abs_le]
    constructor
    · nlinarith [hmem'.1, hcv, hrv]
    · nlinarith [hmem'.2, hcv, hrv, mul_pos hT h0]


open Real in
/-- **The slice window with exported bump data** (Track R, A2, W1d″):
`exists_slice_window` re-run through `exists_bump_window'` — the same
collar bound, with the `ContDiffBump` structure and its radii exposed
so the uniform derivative bound prices the window's Lipschitz data
explicitly.  The radii are the `T`-scaled slice log-edges. -/
theorem exists_slice_window' (h : ℕ → ℂ) (hb : ∀ m, ‖h m‖ ≤ 1)
    (A s U H : ℕ) (hA : 1 ≤ A) (hs : 1 ≤ s) (hsA : s ≤ A) (hU : 0 < U)
    (hUH : 2*U ≤ H) (hplat : ((U:ℝ)+1)*((A:ℝ)+s) ≤ (A:ℝ)*H) :
    ∃ (c : ℝ) (f : ContDiffBump c),
      f.rIn = ((A:ℝ)/H)*(Real.log (1 + (H:ℝ)/((A:ℝ)+s))
          - Real.log (1 + (U:ℝ)/A))/2
      ∧ f.rOut - f.rIn = ((A:ℝ)/H)
          * (min (Real.log (1 + (U:ℝ)/A)
              - Real.log (1 + (U:ℝ)/(4*((A:ℝ)+s))))
            (Real.log (1 + ((H:ℝ)+2*U)/A)
              - Real.log (1 + (H:ℝ)/((A:ℝ)+s))))
      ∧ ContDiff ℝ ∞ (⇑f) ∧ (∀ u, 0 ≤ f u ∧ f u ≤ 1)
      ∧ (∀ u, f u ≠ 0 → |u| ≤ 2)
      ∧ ∀ n ∈ Finset.Ioc A (A+s),
          ‖((1/(U:ℂ)) * ∑ u ∈ Finset.range U,
                ∑ m ∈ Finset.Ioc (n+u) (n+u+H), h m)
              - ∑ m ∈ Finset.Ioc A (A+s+2*H+4*U),
                  h m * ((f (((A:ℝ)/H)*(Real.log n - Real.log m)) : ℝ) : ℂ)‖
            ≤ 6*(U:ℝ) + (H:ℝ)*s/A + 2 := by
  classical
  have hA0 : (0:ℝ) < A := by exact_mod_cast hA
  have hH0 : (0:ℝ) < H := by
    have h1 : 0 < H := by omega
    exact_mod_cast h1
  have hAs0 : (0:ℝ) < (A:ℝ)+s := by
    have : (0:ℝ) < s := by exact_mod_cast hs
    linarith
  have hT : (0:ℝ) < (A:ℝ)/H := by positivity
  obtain ⟨hg0, hg1, hg2, hg3, hg4⟩ :=
    slice_edge_geometry A s U H hA hs hsA hU hUH hplat
  obtain ⟨c, f, hrIn, hrOut, hηs, hη01, hηplat, hηsupp, hη2⟩ :=
    exists_bump_window' ((A:ℝ)/H)
      (Real.log (1 + (U:ℝ)/(4*((A:ℝ)+s)))) (Real.log (1 + (U:ℝ)/A))
      (Real.log (1 + (H:ℝ)/((A:ℝ)+s))) (Real.log (1 + ((H:ℝ)+2*U)/A))
      hT hg0 hg1 hg2 hg3 hg4
  refine ⟨c, f, ?_, ?_, hηs, hη01, hη2, ?_⟩
  · rw [hrIn]
  · rw [hrOut, hrIn]
    ring
  intro n hn
  rw [Finset.mem_Ioc] at hn
  obtain ⟨hn1, hn2⟩ := hn
  have hr₀0 : (0:ℝ) < (U:ℝ)/(4*((A:ℝ)+s)) := by positivity
  have hr01 : (U:ℝ)/(4*((A:ℝ)+s)) ≤ (U:ℝ)/A := by
    refine div_le_div_of_nonneg_left (by positivity) hA0 ?_
    linarith
  have hr12 : (U:ℝ)/A ≤ (H:ℝ)/((A:ℝ)+s) := by
    rw [div_le_div_iff₀ hA0 hAs0]
    have hU0 : (0:ℝ) < U := by exact_mod_cast hU
    have hs0 : (0:ℝ) < s := by exact_mod_cast hs
    have hUH' : 2*(U:ℝ) ≤ H := by exact_mod_cast hUH
    have hsA' : (s:ℝ) ≤ A := by exact_mod_cast hsA
    nlinarith
  have hr23 : (H:ℝ)/((A:ℝ)+s) ≤ ((H:ℝ)+2*U)/A := by
    rw [div_le_div_iff₀ hAs0 hA0]
    have hU0 : (0:ℝ) < U := by exact_mod_cast hU
    have hsA' : (s:ℝ) ≤ A := by exact_mod_cast hsA
    nlinarith
  obtain ⟨hψplat, hψsupp⟩ := psi_transfer A n hA hn1 ((A:ℝ)/H) hT
    ((U:ℝ)/(4*((A:ℝ)+s))) ((U:ℝ)/A) ((H:ℝ)/((A:ℝ)+s)) (((H:ℝ)+2*U)/A)
    hr₀0 hr01 hr12 hr23 (⇑f) hηplat hηsupp
  obtain ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩ :=
    slice_cut_points A s U H n hA hs hsA hU hUH hplat hn1 hn2
  have hMsub : Finset.Ioc n (max ⌊(n:ℝ)*(1+((H:ℝ)+2*U)/A)⌋₊ (n+U+H))
      ⊆ Finset.Ioc A (A+s+2*H+4*U) := by
    intro k hk
    rw [Finset.mem_Ioc] at hk ⊢
    have hfl : ⌊(n:ℝ)*(1+((H:ℝ)+2*U)/A)⌋₊ ≤ A+s+2*H+4*U := by
      refine Nat.floor_le_of_le ?_
      have hn2' : (n:ℝ) ≤ (A:ℝ)+s := by exact_mod_cast hn2
      have hx : (n:ℝ)*(1+((H:ℝ)+2*U)/A) ≤ ((A:ℝ)+s)*(1+((H:ℝ)+2*U)/A) := by
        refine mul_le_mul_of_nonneg_right hn2' ?_
        positivity
      have hy : ((A:ℝ)+s)*(((H:ℝ)+2*U)/A) ≤ 2*((H:ℝ)+2*U) := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ hA0]
        have hsA' : (s:ℝ) ≤ A := by exact_mod_cast hsA
        nlinarith
      push_cast
      nlinarith [hx, hy]
    constructor
    · omega
    · have := hk.2
      have h2 : max ⌊(n:ℝ)*(1+((H:ℝ)+2*U)/A)⌋₊ (n+U+H) ≤ A+s+2*H+4*U := by
        rw [max_le_iff]
        constructor
        · exact hfl
        · omega
      omega
  have hmain := norm_shift_avg_sub_smooth_le_of_cuts h hb n U H hU
    ((n:ℝ)*(1+(U:ℝ)/(4*((A:ℝ)+s)))) ((n:ℝ)*(1+(U:ℝ)/A))
    ((n:ℝ)*(1+(H:ℝ)/((A:ℝ)+s))) ((n:ℝ)*(1+((H:ℝ)+2*U)/A))
    hc1 hc2 hc3 hc4 hc5 hc0
    (Finset.Ioc A (A+s+2*H+4*U)) hMsub
    (fun m => f (((A:ℝ)/H)*(Real.log n - Real.log m)))
    (fun m => hη01 _) hψplat hψsupp
  exact le_trans hmain hc6

end ExpSums

end MoltResearch
