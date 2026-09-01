import MoltResearch.Discrepancy.ParsevalBridge
import MoltResearch.Discrepancy.TypicalFactorization
import MoltResearch.Discrepancy.HalaszComplex
import MoltResearch.Discrepancy.HalaszAssembly

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


open MeasureTheory Real in
/-- **G10a: the per-slice energy, fully composed** (Track R, A2-III):
the slice mean square priced end-to-end — the exported slice window,
the explicit derivative slots (`C₀`/`B′`, discharged by
`exists_bump_deriv_bound` at the schedule's ratio window), the
collar/Lipschitz/Riemann costs, the regime split (G4) with the
derivative energy (G3c), and the `𝒰`-band energy (G5).  Only
`Mmid`/`Mtot` and the ratio-window data remain parametric — the
schedule's business. -/
theorem slice_energy_le (h : ℕ → ℂ) (hb : ∀ m, ‖h m‖ ≤ 1)
    (A s U H : ℕ) (hA : 1 ≤ A) (hs : 1 ≤ s) (hsA : s ≤ A) (hU : 0 < U)
    (hUH : 2*U ≤ H) (h3H : 3*H ≤ A)
    (hplat : ((U:ℝ)+1)*((A:ℝ)+s) ≤ (A:ℝ)*H)
    (hfit : A + s + 2*H + 4*U ≤ 2*A + 1)
    (C₀ B' : ℝ) (hB'0 : 0 ≤ B')
    (hC₀ : ∀ (c : ℝ) (f : ContDiffBump c),
      f.rIn = ((A:ℝ)/H)*(Real.log (1 + (H:ℝ)/((A:ℝ)+s))
          - Real.log (1 + (U:ℝ)/A))/2 →
      f.rOut - f.rIn = ((A:ℝ)/H)
          * (min (Real.log (1 + (U:ℝ)/A)
              - Real.log (1 + (U:ℝ)/(4*((A:ℝ)+s))))
            (Real.log (1 + ((H:ℝ)+2*U)/A)
              - Real.log (1 + (H:ℝ)/((A:ℝ)+s)))) →
      ∀ u : ℝ, |deriv (⇑f) u| ≤ C₀/f.rIn)
    (hB' : C₀/(((A:ℝ)/H)*(Real.log (1 + (H:ℝ)/((A:ℝ)+s))
        - Real.log (1 + (U:ℝ)/A))/2) ≤ B')
    (K L Mmid Mtot : ℝ) (hK : 0 ≤ K) (hL : 0 < L) (hMmid0 : 0 ≤ Mmid)
    (hmid : ∀ ξ : ℝ, K ≤ |ξ| → |ξ| ≤ L →
      ‖∑ m ∈ Finset.Ioc A (A+s+2*H+4*U),
        h m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖ ≤ Mmid)
    (htot : ∀ ξ : ℝ,
      ‖∑ m ∈ Finset.Ioc A (A+s+2*H+4*U),
        h m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖ ≤ Mtot)
    (levels : List (Finset ℕ)) (hlv : ∀ P ∈ levels, ∀ q ∈ P, q.Prime) :
    ∑ n ∈ Finset.Ioc A (A+s), ‖∑ m ∈ Finset.Ioc n (n+H), h m‖^2/n
      ≤ 6*((4*(H:ℝ)/A)^2*((2*(A:ℝ)+1)^2
            * uBound K levels A (A+s+2*H+4*U))
          + Mmid^2*(4*(H:ℝ)/A)
          + Mtot^2*((1/L^2)*((A:ℝ)/H*B'^2/π^2)))
        + (3*(U:ℝ)^2 + 3*(6*(U:ℝ)+(H:ℝ)*s/A+2)^2)
            * (∑ n ∈ Finset.Ioc A (A+s), (1:ℝ)/n)
        + 6*(800*(H:ℝ)*(A:ℝ)*B')/A := by
  classical
  have hH : 0 < H := by omega
  have hA0 : (0:ℝ) < A := by exact_mod_cast hA
  have hH0 : (0:ℝ) < H := by exact_mod_cast hH
  have hT : (0:ℝ) < (A:ℝ)/H := by positivity
  have hT1 : (1:ℝ) ≤ (A:ℝ)/H := by
    rw [le_div_iff₀ hH0]
    have h3 : (3:ℝ)*H ≤ A := by exact_mod_cast h3H
    linarith
  obtain ⟨c, f, hrIn, hrOutsub, hηs, hη01, hη2, hcollar⟩ :=
    exists_slice_window' h hb A s U H hA hs hsA hU hUH hplat
  obtain ⟨B₂, hB₂0, hB₂, hd2⟩ := exists_deriv_bound (⇑f) hηs hη2
  have hderiv : ∀ u : ℝ, |deriv (⇑f) u| ≤ B' := by
    intro u
    refine le_trans (hC₀ c f hrIn hrOutsub u) ?_
    rw [hrIn]
    exact hB'
  have hf1 : ∀ u, |(⇑f) u| ≤ 1 := by
    intro u
    rw [abs_le]
    exact ⟨by linarith [(hη01 u).1], (hη01 u).2⟩
  have hS'pos : ∀ m ∈ Finset.Ioc A (A+s+2*H+4*U), 0 < m := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    omega
  have hS'A : ∀ m ∈ Finset.Ioc A (A+s+2*H+4*U), A ≤ m := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    omega
  have ha1 : ∀ m, ‖(fun m => if m ∈ Finset.Ioc A (A+s+2*H+4*U)
      then h m * (m:ℂ)/(4*(A:ℂ)) else 0) m‖ ≤ 1 := by
    intro m
    refine norm_truncated_weight_le h hb A (by omega) _ ?_ m
    intro k hk
    rw [Finset.mem_Ioc] at hk
    omega
  set G : ℝ → ℂ := fun y => (4*(H:ℂ)) * smoothedLogSum ((A:ℝ)/H) (⇑f)
      (fun m => if m ∈ Finset.Ioc A (A+s+2*H+4*U)
        then h m * (m:ℂ)/(4*(A:ℂ)) else 0)
      (Finset.Ioc A (A+s+2*H+4*U)) y
    with hG_def
  have hGcont : Continuous G := by
    rw [hG_def]
    exact continuous_const.mul
      ((smoothedLogSum_contDiff ((A:ℝ)/H) (⇑f) hηs _ _).continuous)
  -- the collar at the smoothed form
  have hcollar' : ∀ n ∈ Finset.Ioc A (A+s),
      ‖((1/(U:ℂ)) * ∑ u ∈ Finset.range U,
          ∑ m ∈ Finset.Ioc (n+u) (n+u+H), h m) - G (Real.log n)‖
        ≤ 6*(U:ℝ) + (H:ℝ)*s/A + 2 := by
    intro n hn
    have hcn := hcollar n hn
    have hid := window_sum_eq_smoothedLogSum h A H (by omega) hH (⇑f)
      (Finset.Ioc A (A+s+2*H+4*U)) hS'pos (Real.log n)
    rw [hG_def]
    dsimp only
    rw [← hid]
    exact hcn
  -- the Lipschitz data
  have hLip : ∀ y z : ℝ, |‖G y‖^2 - ‖G z‖^2|
      ≤ (800*(H:ℝ)*(A:ℝ)*B') * |y - z| := by
    intro y z
    have hbase := abs_norm_sq_smoothedLogSum_sub_le ((A:ℝ)/H) hT1 (⇑f) hηs
      hη2 1 hf1 hd2 B' hderiv _ ha1
      (Finset.Ioc A (A+s+2*H+4*U)) A hS'A hA
      (by
        rw [div_le_iff₀ hH0]
        have h1H : (1:ℝ) ≤ H := by exact_mod_cast hH
        nlinarith) y z
    have hGsq : ∀ w : ℝ, ‖G w‖^2
        = 16*(H:ℝ)^2 * ‖smoothedLogSum ((A:ℝ)/H) (⇑f)
            (fun m => if m ∈ Finset.Ioc A (A+s+2*H+4*U)
              then h m * (m:ℂ)/(4*(A:ℂ)) else 0)
            (Finset.Ioc A (A+s+2*H+4*U)) w‖^2 := by
      intro w
      rw [hG_def]
      dsimp only
      rw [norm_mul]
      have h4H : ‖(4*(H:ℂ) : ℂ)‖ = 4*(H:ℝ) := by
        rw [norm_mul, Complex.norm_natCast]
        norm_num
      rw [h4H, mul_pow]
      ring
    rw [hGsq y, hGsq z, ← mul_sub, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 16*(H:ℝ)^2)]
    calc 16*(H:ℝ)^2 * |‖smoothedLogSum ((A:ℝ)/H) (⇑f)
          (fun m => if m ∈ Finset.Ioc A (A+s+2*H+4*U)
            then h m * (m:ℂ)/(4*(A:ℂ)) else 0)
          (Finset.Ioc A (A+s+2*H+4*U)) y‖^2
        - ‖smoothedLogSum ((A:ℝ)/H) (⇑f)
          (fun m => if m ∈ Finset.Ioc A (A+s+2*H+4*U)
            then h m * (m:ℂ)/(4*(A:ℂ)) else 0)
          (Finset.Ioc A (A+s+2*H+4*U)) z‖^2|
        ≤ 16*(H:ℝ)^2 * ((50*1*B'*((A:ℝ)/H)) * |y - z|) :=
          mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = (800*(H:ℝ)*(A:ℝ)*B') * |y - z| := by
          field_simp
          ring
  -- the scaffold
  have hmean := slice_window_mean_sq_le h hb A s H U hA hU (by omega)
    G hGcont (6*(U:ℝ) + (H:ℝ)*s/A + 2) (by positivity) hcollar'
    (800*(H:ℝ)*(A:ℝ)*B') (by positivity) hLip
  -- interval energy → line energy
  have hGcs : HasCompactSupport G := by
    rw [hG_def]
    have hfcs : HasCompactSupport (⇑f) := by
      refine HasCompactSupport.intro
        (isCompact_Icc (a := (-2:ℝ)) (b := 2)) ?_
      intro u hu
      by_contra hne
      have h2 := hη2 u hne
      rw [Set.mem_Icc, not_and_or] at hu
      rw [abs_le] at h2
      rcases hu with h | h
      · push_neg at h
        linarith [h2.1]
      · push_neg at h
        linarith [h2.2]
    have := smoothedLogSum_hasCompactSupport ((A:ℝ)/H) hT (⇑f) hfcs
      (fun m => if m ∈ Finset.Ioc A (A+s+2*H+4*U)
        then h m * (m:ℂ)/(4*(A:ℂ)) else 0)
      (Finset.Ioc A (A+s+2*H+4*U))
    exact this.mul_left
  have hG1 := intervalIntegral_norm_sq_le_integral G hGcont hGcs
    (Real.log A) (Real.log (((A+s : ℕ):ℝ)+1))
  -- the regime split with the derivative energy
  have hG3c := integral_sq_norm_fourier_slice_window_le ((A:ℝ)/H) hT (⇑f)
    hηs hη2 B' hB'0 hderiv hd2
  have hG4 := window_energy_regime_le h A s H U hA hH (⇑f) hηs hη01 hη2
    K L Mmid Mtot ((A:ℝ)/H*B'^2/π^2) hK hL hMmid0 hmid htot hG3c
  -- the band energy through the 𝒰-recursion
  have hG5 := intervalIntegral_norm_sq_plain_le K hK levels hlv
    A (A+s+2*H+4*U) hfit (Finset.Ioc A (A+s+2*H+4*U))
    (Finset.Subset.refl _) h hb
  -- assemble
  have hint : ∫ y, ‖G y‖^2
      ≤ (4*(H:ℝ)/A)^2*((2*(A:ℝ)+1)^2
          * uBound K levels A (A+s+2*H+4*U))
        + Mmid^2*(4*(H:ℝ)/A)
        + Mtot^2*((1/L^2)*((A:ℝ)/H*B'^2/π^2)) := by
    have hG4' : ∫ y, ‖G y‖^2
        ≤ (4*(H:ℝ)/A)^2
            * (∫ ξ in (-K)..K, ‖∑ m ∈ Finset.Ioc A (A+s+2*H+4*U),
                h m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2)
          + Mmid^2*(4*(H:ℝ)/A) + Mtot^2*((1/L^2)*((A:ℝ)/H*B'^2/π^2)) := hG4
    refine le_trans hG4' ?_
    have := mul_le_mul_of_nonneg_left hG5
      (by positivity : (0:ℝ) ≤ (4*(H:ℝ)/A)^2)
    linarith
  have hstep : ∫ y in (Real.log A)..(Real.log (((A+s : ℕ):ℝ)+1)), ‖G y‖^2
      ≤ (4*(H:ℝ)/A)^2*((2*(A:ℝ)+1)^2
          * uBound K levels A (A+s+2*H+4*U))
        + Mmid^2*(4*(H:ℝ)/A)
        + Mtot^2*((1/L^2)*((A:ℝ)/H*B'^2/π^2)) := le_trans hG1 hint
  have h6 := mul_le_mul_of_nonneg_left hstep (by norm_num : (0:ℝ) ≤ 6)
  linarith [hmean, h6]


open Real Finset in
/-- **G10b: the log-averaged window bound from slice energies** (Track
R, A2-III): aggregate per-slice mean-square bounds over the slice
partition and close with the outer Cauchy–Schwarz —

  `∑_{n∈(A, A+Js]} ‖W_n‖/(H·n) ≤ √(∑ 1/n)·√(∑_j B_j)/H`.

`slice_energy_le` supplies the `B_j`; the harmonic factor is priced by
the consumer's `log w`. -/
theorem window_logavg_le_of_slice_bounds (h : ℕ → ℂ)
    (A s J H : ℕ) (hH : 0 < H) (B : ℕ → ℝ)
    (hB0 : ∀ j ∈ Finset.range J, 0 ≤ B j)
    (hslice : ∀ j ∈ Finset.range J,
      ∑ n ∈ Finset.Ioc (A + j*s) (A + (j+1)*s),
        ‖∑ m ∈ Finset.Ioc n (n+H), h m‖^2/n ≤ B j) :
    ∑ n ∈ Finset.Ioc A (A + J*s),
        ‖∑ m ∈ Finset.Ioc n (n+H), h m‖/((H:ℝ)*n)
      ≤ Real.sqrt (∑ n ∈ Finset.Ioc A (A + J*s), (1:ℝ)/n)
        * Real.sqrt (∑ j ∈ Finset.range J, B j) / H := by
  classical
  have hH0 : (0:ℝ) < H := by exact_mod_cast hH
  -- the mean square over the full range
  have hagg := sum_Ioc_le_of_slice_bounds A s J
    (fun n => ‖∑ m ∈ Finset.Ioc n (n+H), h m‖^2/n) B hslice
  -- the outer Cauchy–Schwarz
  have hcs := sum_div_le_sqrt_mul_sqrt A (A + J*s)
    (fun n => ‖∑ m ∈ Finset.Ioc n (n+H), h m‖)
    (fun n => norm_nonneg _)
  -- rescale by `1/H`
  have hfactor : ∑ n ∈ Finset.Ioc A (A + J*s),
      ‖∑ m ∈ Finset.Ioc n (n+H), h m‖/((H:ℝ)*n)
      = (1/(H:ℝ)) * ∑ n ∈ Finset.Ioc A (A + J*s),
          ‖∑ m ∈ Finset.Ioc n (n+H), h m‖/n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    field_simp
  rw [hfactor]
  have hsq_mono : Real.sqrt (∑ n ∈ Finset.Ioc A (A + J*s),
      ‖∑ m ∈ Finset.Ioc n (n+H), h m‖^2/n)
      ≤ Real.sqrt (∑ j ∈ Finset.range J, B j) :=
    Real.sqrt_le_sqrt hagg
  have hsqrt1 : (0:ℝ) ≤ Real.sqrt (∑ n ∈ Finset.Ioc A (A + J*s), (1:ℝ)/n) :=
    Real.sqrt_nonneg _
  calc (1/(H:ℝ)) * ∑ n ∈ Finset.Ioc A (A + J*s),
        ‖∑ m ∈ Finset.Ioc n (n+H), h m‖/n
      ≤ (1/(H:ℝ)) * (Real.sqrt (∑ n ∈ Finset.Ioc A (A + J*s), (1:ℝ)/n)
          * Real.sqrt (∑ n ∈ Finset.Ioc A (A + J*s),
              ‖∑ m ∈ Finset.Ioc n (n+H), h m‖^2/n)) := by
        refine mul_le_mul_of_nonneg_left hcs (by positivity)
    _ ≤ (1/(H:ℝ)) * (Real.sqrt (∑ n ∈ Finset.Ioc A (A + J*s), (1:ℝ)/n)
          * Real.sqrt (∑ j ∈ Finset.range J, B j)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hsq_mono hsqrt1
    _ = Real.sqrt (∑ n ∈ Finset.Ioc A (A + J*s), (1:ℝ)/n)
        * Real.sqrt (∑ j ∈ Finset.range J, B j) / H := by
        field_simp


open Real Finset in
/-- **G10c-0: the ε-form closer** (Track R, A2-III): a total slice
budget of `ε²H²·(range harmonic)` closes the log-averaged window bound
at `ε` times the harmonic mass — the quantitative target the schedule
prices everything against. -/
theorem window_logavg_eps_of_slice_budget (h : ℕ → ℂ)
    (A s J H : ℕ) (hH : 0 < H) (ε : ℝ) (hε : 0 ≤ ε) (B : ℕ → ℝ)
    (hB0 : ∀ j ∈ Finset.range J, 0 ≤ B j)
    (hslice : ∀ j ∈ Finset.range J,
      ∑ n ∈ Finset.Ioc (A + j*s) (A + (j+1)*s),
        ‖∑ m ∈ Finset.Ioc n (n+H), h m‖^2/n ≤ B j)
    (hbudget : ∑ j ∈ Finset.range J, B j
      ≤ ε^2 * H^2 * ∑ n ∈ Finset.Ioc A (A + J*s), (1:ℝ)/n) :
    ∑ n ∈ Finset.Ioc A (A + J*s),
        ‖∑ m ∈ Finset.Ioc n (n+H), h m‖/((H:ℝ)*n)
      ≤ ε * ∑ n ∈ Finset.Ioc A (A + J*s), (1:ℝ)/n := by
  classical
  have hH0 : (0:ℝ) < H := by exact_mod_cast hH
  have hharm0 : (0:ℝ) ≤ ∑ n ∈ Finset.Ioc A (A + J*s), (1:ℝ)/n :=
    Finset.sum_nonneg fun n _ => by positivity
  refine le_trans (window_logavg_le_of_slice_bounds h A s J H hH B hB0
    hslice) ?_
  have hsqB : Real.sqrt (∑ j ∈ Finset.range J, B j)
      ≤ ε * H * Real.sqrt (∑ n ∈ Finset.Ioc A (A + J*s), (1:ℝ)/n) := by
    have hsq : (Real.sqrt (∑ n ∈ Finset.Ioc A (A + J*s), (1:ℝ)/n))^2
        = ∑ n ∈ Finset.Ioc A (A + J*s), (1:ℝ)/n :=
      Real.sq_sqrt hharm0
    have h1 : ∑ j ∈ Finset.range J, B j
        ≤ (ε * H * Real.sqrt (∑ n ∈ Finset.Ioc A
            (A + J*s), (1:ℝ)/n))^2 := by
      calc ∑ j ∈ Finset.range J, B j
          ≤ ε^2 * H^2 * ∑ n ∈ Finset.Ioc A (A + J*s), (1:ℝ)/n := hbudget
        _ = (ε * H * Real.sqrt (∑ n ∈ Finset.Ioc A
            (A + J*s), (1:ℝ)/n))^2 := by
            rw [mul_pow, mul_pow, hsq]
    calc Real.sqrt (∑ j ∈ Finset.range J, B j)
        ≤ Real.sqrt ((ε * H * Real.sqrt (∑ n ∈ Finset.Ioc A
            (A + J*s), (1:ℝ)/n))^2) := Real.sqrt_le_sqrt h1
      _ = ε * H * Real.sqrt (∑ n ∈ Finset.Ioc A (A + J*s), (1:ℝ)/n) := by
          rw [Real.sqrt_sq (by positivity)]
  calc Real.sqrt (∑ n ∈ Finset.Ioc A (A + J*s), (1:ℝ)/n)
        * Real.sqrt (∑ j ∈ Finset.range J, B j) / H
      ≤ Real.sqrt (∑ n ∈ Finset.Ioc A (A + J*s), (1:ℝ)/n)
        * (ε * H * Real.sqrt (∑ n ∈ Finset.Ioc A
            (A + J*s), (1:ℝ)/n)) / H := by
        refine div_le_div_of_nonneg_right ?_ hH0.le
        exact mul_le_mul_of_nonneg_left hsqB (Real.sqrt_nonneg _)
    _ = ε * ((Real.sqrt (∑ n ∈ Finset.Ioc A (A + J*s), (1:ℝ)/n))^2) := by
        field_simp
    _ = ε * ∑ n ∈ Finset.Ioc A (A + J*s), (1:ℝ)/n := by
        rw [Real.sq_sqrt hharm0]


open Real in
/-- **Upper log-difference quotient** (Track R, A2-III schedule
geometry): for `0 ≤ y ≤ x`,

  `log(1+x) − log(1+y) ≤ (x−y)/(1+y)`.

With its partner `le_log_one_add_sub_log_one_add` this brackets every
slice-window edge difference between explicit rational functions —
the whole G10c radii/ratio arithmetic prices against this pair. -/
theorem log_one_add_sub_log_one_add_le (x y : ℝ)
    (hy : 0 ≤ y) (hxy : y ≤ x) :
    Real.log (1+x) - Real.log (1+y) ≤ (x-y)/(1+y) := by
  have h1y : (0:ℝ) < 1+y := by linarith
  have h1x : (0:ℝ) < 1+x := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos h1x h1y)
  rw [Real.log_div h1x.ne' h1y.ne'] at hlog
  have hq : (1+x)/(1+y) - 1 = (x-y)/(1+y) := by field_simp; ring
  linarith [hlog, hq.le, hq.ge]

open Real in
/-- **Lower log-difference quotient** (Track R, A2-III schedule
geometry): for `0 ≤ y ≤ x`,

  `(x−y)/(1+x) ≤ log(1+x) − log(1+y)`.

Proof: apply `log z ≤ z − 1` at the reciprocal ratio `(1+y)/(1+x)`
and negate — no second transcendental input needed. -/
theorem le_log_one_add_sub_log_one_add (x y : ℝ)
    (hy : 0 ≤ y) (hxy : y ≤ x) :
    (x-y)/(1+x) ≤ Real.log (1+x) - Real.log (1+y) := by
  have h1y : (0:ℝ) < 1+y := by linarith
  have h1x : (0:ℝ) < 1+x := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos h1y h1x)
  rw [Real.log_div h1y.ne' h1x.ne'] at hlog
  have hq : (1+y)/(1+x) - 1 = -((x-y)/(1+x)) := by field_simp; ring
  linarith [hlog, hq.le, hq.ge]


open Real in
/-- **The slice window's inner radius is at least `1/3`** (Track R,
A2-III schedule geometry, G10c-1): under the schedule constraints
`30s ≤ A`, `3H ≤ A`, `50U ≤ εH`, `ε ≤ 1`, the `exists_slice_window'`
bump's inner radius `(A/H)·(log(1+H/(A+s)) − log(1+U/A))/2` is at
least `1/3` — so the uniform derivative bound `C₀/rIn` from
`exists_bump_deriv_bound` is at most `3C₀`, pricing
`slice_energy_le`'s `B′`-slot by an absolute constant. -/
theorem slice_rIn_lower (A s U H : ℕ) (ε : ℝ)
    (hA : 1 ≤ A) (hH : 0 < H) (hs30 : 30*s ≤ A) (h3H : 3*H ≤ A)
    (hε1 : ε ≤ 1) (hU50 : 50*(U:ℝ) ≤ ε*H) :
    (1:ℝ)/3 ≤ ((A:ℝ)/H)*(Real.log (1 + (H:ℝ)/((A:ℝ)+s))
        - Real.log (1 + (U:ℝ)/A))/2 := by
  have ha0 : (0:ℝ) < A := by exact_mod_cast hA
  have hh0 : (0:ℝ) < H := by exact_mod_cast hH
  have hs0 : (0:ℝ) ≤ s := Nat.cast_nonneg s
  have hu0 : (0:ℝ) ≤ U := Nat.cast_nonneg U
  have hs30' : 30*(s:ℝ) ≤ A := by exact_mod_cast hs30
  have h3H' : 3*(H:ℝ) ≤ A := by exact_mod_cast h3H
  have huh : 50*(U:ℝ) ≤ H := by nlinarith
  have hD0 : (0:ℝ) < (A:ℝ)+s := by linarith
  have hx1x2 : (U:ℝ)/A ≤ (H:ℝ)/((A:ℝ)+s) := by
    rw [div_le_div_iff₀ ha0 hD0]
    nlinarith [mul_nonneg (sub_nonneg.2 huh) hD0.le,
      mul_nonneg hh0.le (sub_nonneg.2 hs30'),
      mul_nonneg hh0.le ha0.le]
  have hkey := le_log_one_add_sub_log_one_add ((H:ℝ)/((A:ℝ)+s))
    ((U:ℝ)/A) (by positivity) hx1x2
  have hAH0 : (0:ℝ) ≤ (A:ℝ)/H := by positivity
  have hmono : ((A:ℝ)/H)*(((H:ℝ)/((A:ℝ)+s) - (U:ℝ)/A)
        /(1 + (H:ℝ)/((A:ℝ)+s)))/2
      ≤ ((A:ℝ)/H)*(Real.log (1 + (H:ℝ)/((A:ℝ)+s))
          - Real.log (1 + (U:ℝ)/A))/2 :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hkey hAH0) (by norm_num)
  refine le_trans ?_ hmono
  have hEq : ((A:ℝ)/H)*(((H:ℝ)/((A:ℝ)+s) - (U:ℝ)/A)
        /(1 + (H:ℝ)/((A:ℝ)+s)))/2
      = ((H:ℝ)*A - (U:ℝ)*((A:ℝ)+s))/(2*(H:ℝ)*(((A:ℝ)+s)+H)) := by
    field_simp
  rw [hEq, le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 huh) hD0.le,
    mul_nonneg hh0.le (sub_nonneg.2 hs30'),
    mul_nonneg hh0.le (sub_nonneg.2 h3H'),
    mul_nonneg hh0.le ha0.le]


open Real in
/-- **Slice ratio window, upper edge** (Track R, A2-III schedule
geometry, G10c-1): under the schedule `30s ≤ A`, `3H ≤ A`,
`50U ≤ εH ≤ H`, the `exists_slice_window'` bump's radius gap
`(A/H)·min(t₁−t₀, t₃−t₂)` is at most `ε/20` times the inner radius
`(A/H)·(t₂−t₁)/2` — the upper half of the `[1+ε/600, 1+ε/20]`
ratio-window membership that `exists_bump_deriv_bound` prices `C₀`
against. -/
theorem slice_ratio_upper (A s U H : ℕ) (ε : ℝ)
    (hA : 1 ≤ A) (hH : 0 < H) (hs30 : 30*s ≤ A) (h3H : 3*H ≤ A)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hU50 : 50*(U:ℝ) ≤ ε*H) :
    ((A:ℝ)/H) * (min (Real.log (1 + (U:ℝ)/A)
          - Real.log (1 + (U:ℝ)/(4*((A:ℝ)+s))))
        (Real.log (1 + ((H:ℝ)+2*U)/A)
          - Real.log (1 + (H:ℝ)/((A:ℝ)+s))))
      ≤ (ε/20) * (((A:ℝ)/H)*(Real.log (1 + (H:ℝ)/((A:ℝ)+s))
          - Real.log (1 + (U:ℝ)/A))/2) := by
  have ha0 : (0:ℝ) < A := by exact_mod_cast hA
  have hh0 : (0:ℝ) < H := by exact_mod_cast hH
  have hs0 : (0:ℝ) ≤ s := Nat.cast_nonneg s
  have hu0 : (0:ℝ) ≤ U := Nat.cast_nonneg U
  have hs30' : 30*(s:ℝ) ≤ A := by exact_mod_cast hs30
  have h3H' : 3*(H:ℝ) ≤ A := by exact_mod_cast h3H
  have huh : 50*(U:ℝ) ≤ H := by nlinarith
  have hD0 : (0:ℝ) < (A:ℝ)+s := by linarith
  have hεh0 : (0:ℝ) ≤ ε*H := le_trans (by positivity) hU50
  have hAH0 : (0:ℝ) ≤ (A:ℝ)/H := by positivity
  have hx01 : (U:ℝ)/(4*((A:ℝ)+s)) ≤ (U:ℝ)/A := by
    rw [div_le_div_iff₀ (by positivity) ha0]
    nlinarith [mul_nonneg hu0 hs0, mul_nonneg hu0 ha0.le]
  have hx12 : (U:ℝ)/A ≤ (H:ℝ)/((A:ℝ)+s) := by
    rw [div_le_div_iff₀ ha0 hD0]
    nlinarith [mul_nonneg (sub_nonneg.2 huh) hD0.le,
      mul_nonneg hh0.le (sub_nonneg.2 hs30'),
      mul_nonneg hh0.le ha0.le]
  have hL10 := log_one_add_sub_log_one_add_le ((U:ℝ)/A)
    ((U:ℝ)/(4*((A:ℝ)+s))) (by positivity) hx01
  have hL21 := le_log_one_add_sub_log_one_add ((H:ℝ)/((A:ℝ)+s))
    ((U:ℝ)/A) (by positivity) hx12
  -- scalar bound 1: `(A/H)·(x₁−x₀)/(1+x₀) ≤ (47/3000)·ε`
  have hs1 : ((A:ℝ)/H) * (((U:ℝ)/A - (U:ℝ)/(4*((A:ℝ)+s)))
        /(1 + (U:ℝ)/(4*((A:ℝ)+s)))) ≤ (47/3000)*ε := by
    have hden : (1:ℝ) ≤ 1 + (U:ℝ)/(4*((A:ℝ)+s)) :=
      le_add_of_nonneg_right (by positivity)
    have hq : ((U:ℝ)/A - (U:ℝ)/(4*((A:ℝ)+s)))
          /(1 + (U:ℝ)/(4*((A:ℝ)+s)))
        ≤ (U:ℝ)/A - (U:ℝ)/(4*((A:ℝ)+s)) :=
      div_le_self (sub_nonneg.2 hx01) hden
    have hstep : ((A:ℝ)/H) * ((U:ℝ)/A - (U:ℝ)/(4*((A:ℝ)+s)))
        ≤ (47/3000)*ε := by
      have heq : ((A:ℝ)/H) * ((U:ℝ)/A - (U:ℝ)/(4*((A:ℝ)+s)))
          = (U:ℝ)*(3*(A:ℝ)+4*s)/(4*(H:ℝ)*((A:ℝ)+s)) := by
        field_simp
        ring
      rw [heq, div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.2 hU50)
          (by linarith : (0:ℝ) ≤ 3*(A:ℝ)+4*s),
        mul_nonneg hεh0 (sub_nonneg.2 (by linarith : 13*(s:ℝ) ≤ 2*A))]
    exact le_trans (mul_le_mul_of_nonneg_left hq hAH0) hstep
  -- scalar bound 2: `4407/6200 ≤ (A/H)·(x₂−x₁)/(1+x₂)`
  have hs2 : (4407/6200 : ℝ) ≤ ((A:ℝ)/H)
      * (((H:ℝ)/((A:ℝ)+s) - (U:ℝ)/A)/(1 + (H:ℝ)/((A:ℝ)+s))) := by
    have heq : ((A:ℝ)/H)
        * (((H:ℝ)/((A:ℝ)+s) - (U:ℝ)/A)/(1 + (H:ℝ)/((A:ℝ)+s)))
        = ((H:ℝ)*A - (U:ℝ)*((A:ℝ)+s))/((H:ℝ)*(((A:ℝ)+s)+H)) := by
      field_simp
    rw [heq, le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.2 huh) hD0.le,
      mul_nonneg hh0.le (sub_nonneg.2 hs30'),
      mul_nonneg hh0.le (sub_nonneg.2 h3H'),
      mul_nonneg hh0.le ha0.le]
  -- assemble
  have t1 : ((A:ℝ)/H) * (min (Real.log (1 + (U:ℝ)/A)
          - Real.log (1 + (U:ℝ)/(4*((A:ℝ)+s))))
        (Real.log (1 + ((H:ℝ)+2*U)/A)
          - Real.log (1 + (H:ℝ)/((A:ℝ)+s))))
      ≤ (47/3000)*ε :=
    le_trans (mul_le_mul_of_nonneg_left
      (le_trans (min_le_left _ _) hL10) hAH0) hs1
  have t2 : (ε/40)*(4407/6200 : ℝ)
      ≤ (ε/40)*(((A:ℝ)/H)*(Real.log (1 + (H:ℝ)/((A:ℝ)+s))
          - Real.log (1 + (U:ℝ)/A))) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact le_trans hs2 (mul_le_mul_of_nonneg_left hL21 hAH0)
  have t3 : (47/3000)*ε ≤ (ε/40)*(4407/6200 : ℝ) := by nlinarith
  linarith [t1, t2, t3]


set_option maxHeartbeats 1600000 in
open Real in
/-- **Slice ratio window, lower edge** (Track R, A2-III schedule
geometry, G10c-1): under the schedule `30s ≤ A`, `3H ≤ A`,
`εH ≤ 100U`, `50U ≤ εH ≤ H`, the radius gap `(A/H)·min(t₁−t₀, t₃−t₂)`
is at least `ε/600` times the inner radius `(A/H)·(t₂−t₁)/2` — the
lower half of the ratio-window membership, keeping the pinned
`R₀ = 1+ε/600` below the actual bump ratio so
`exists_bump_deriv_bound`'s compact window contains it. -/
theorem slice_ratio_lower (A s U H : ℕ) (ε : ℝ)
    (hA : 1 ≤ A) (hH : 0 < H) (hs30 : 30*s ≤ A) (h3H : 3*H ≤ A)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hU100 : ε*(H:ℝ) ≤ 100*U) (hU50 : 50*(U:ℝ) ≤ ε*H) :
    (ε/600) * (((A:ℝ)/H)*(Real.log (1 + (H:ℝ)/((A:ℝ)+s))
        - Real.log (1 + (U:ℝ)/A))/2)
      ≤ ((A:ℝ)/H) * (min (Real.log (1 + (U:ℝ)/A)
            - Real.log (1 + (U:ℝ)/(4*((A:ℝ)+s))))
          (Real.log (1 + ((H:ℝ)+2*U)/A)
            - Real.log (1 + (H:ℝ)/((A:ℝ)+s)))) := by
  have ha0 : (0:ℝ) < A := by exact_mod_cast hA
  have hh0 : (0:ℝ) < H := by exact_mod_cast hH
  have hs0 : (0:ℝ) ≤ s := Nat.cast_nonneg s
  have hu0 : (0:ℝ) ≤ U := Nat.cast_nonneg U
  have hs30' : 30*(s:ℝ) ≤ A := by exact_mod_cast hs30
  have h3H' : 3*(H:ℝ) ≤ A := by exact_mod_cast h3H
  have huh : 50*(U:ℝ) ≤ H := by nlinarith
  have hu150 : 150*(U:ℝ) ≤ A := by linarith
  have hD0 : (0:ℝ) < (A:ℝ)+s := by linarith
  have hεh0 : (0:ℝ) ≤ ε*H := le_trans (by positivity) hU50
  have hAH0 : (0:ℝ) ≤ (A:ℝ)/H := by positivity
  have hx01 : (U:ℝ)/(4*((A:ℝ)+s)) ≤ (U:ℝ)/A := by
    rw [div_le_div_iff₀ (by positivity) ha0]
    nlinarith [mul_nonneg hu0 hs0, mul_nonneg hu0 ha0.le]
  have hx12 : (U:ℝ)/A ≤ (H:ℝ)/((A:ℝ)+s) := by
    rw [div_le_div_iff₀ ha0 hD0]
    nlinarith [mul_nonneg (sub_nonneg.2 huh) hD0.le,
      mul_nonneg hh0.le (sub_nonneg.2 hs30'),
      mul_nonneg hh0.le ha0.le]
  have hx23 : (H:ℝ)/((A:ℝ)+s) ≤ ((H:ℝ)+2*U)/A := by
    rw [div_le_div_iff₀ hD0 ha0]
    nlinarith [mul_nonneg hh0.le hs0, mul_nonneg hu0 hD0.le]
  have hL10 := le_log_one_add_sub_log_one_add ((U:ℝ)/A)
    ((U:ℝ)/(4*((A:ℝ)+s))) (by positivity) hx01
  have hL32 := le_log_one_add_sub_log_one_add (((H:ℝ)+2*U)/A)
    ((H:ℝ)/((A:ℝ)+s)) (by positivity) hx23
  have hL21 := log_one_add_sub_log_one_add_le ((H:ℝ)/((A:ℝ)+s))
    ((U:ℝ)/A) (by positivity) hx12
  -- the (t₂−t₁)-side is at most `1` after the `A/H`-scaling
  have t_up : ((A:ℝ)/H) * (((H:ℝ)/((A:ℝ)+s) - (U:ℝ)/A)
        /(1 + (U:ℝ)/A)) ≤ 1 := by
    have heq : ((A:ℝ)/H) * (((H:ℝ)/((A:ℝ)+s) - (U:ℝ)/A)
          /(1 + (U:ℝ)/A))
        = ((A:ℝ)*((H:ℝ)*A - (U:ℝ)*((A:ℝ)+s)))
            /((H:ℝ)*(((A:ℝ)+s)*((A:ℝ)+U))) := by
      field_simp
    rw [heq, div_le_one (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hh0.le ha0.le) hu0,
      mul_nonneg (mul_nonneg hh0.le hs0) ha0.le,
      mul_nonneg (mul_nonneg hh0.le hs0) hu0,
      mul_nonneg (mul_nonneg hu0 ha0.le) hD0.le]
  -- lower-bounding the first min-branch: `ε/1200 ≤ (A/H)·(t₁−t₀)`-side
  have b_left : ε/1200 ≤ ((A:ℝ)/H) * (((U:ℝ)/A
        - (U:ℝ)/(4*((A:ℝ)+s)))/(1 + (U:ℝ)/A)) := by
    have heq : ((A:ℝ)/H) * (((U:ℝ)/A - (U:ℝ)/(4*((A:ℝ)+s)))
          /(1 + (U:ℝ)/A))
        = ((A:ℝ)*((U:ℝ)*(3*(A:ℝ)+4*s)))
            /((H:ℝ)*(4*(((A:ℝ)+s)*((A:ℝ)+U)))) := by
      field_simp
      ring
    rw [heq, le_div_iff₀ (by positivity)]
    have hX0 : (0:ℝ) ≤ 4*(((A:ℝ)+s)*((A:ℝ)+U)) := by positivity
    have hstep1 : ε/1200 * ((H:ℝ)*(4*(((A:ℝ)+s)*((A:ℝ)+U))))
        ≤ (U:ℝ)/12 * (4*(((A:ℝ)+s)*((A:ℝ)+U))) := by
      nlinarith [mul_le_mul_of_nonneg_right hU100 hX0]
    have hsa : (s:ℝ) ≤ A := by linarith
    have hua : (U:ℝ) ≤ A := by linarith
    have hprod : ((A:ℝ)+s)*((A:ℝ)+U) ≤ 9*(A:ℝ)^2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hsa) (sub_nonneg.2 hua),
        mul_nonneg hs0 hu0]
    have hstep2 : (U:ℝ)/12 * (4*(((A:ℝ)+s)*((A:ℝ)+U)))
        ≤ (A:ℝ)*((U:ℝ)*(3*(A:ℝ)+4*s)) := by
      nlinarith [mul_le_mul_of_nonneg_left hprod (by positivity : (0:ℝ) ≤ (U:ℝ)/3),
        mul_nonneg (mul_nonneg ha0.le hs0) hu0]
    linarith [hstep1, hstep2]
  -- lower-bounding the second min-branch: `ε/1200 ≤ (A/H)·(t₃−t₂)`-side
  have b_right : ε/1200 ≤ ((A:ℝ)/H) * ((((H:ℝ)+2*U)/A
        - (H:ℝ)/((A:ℝ)+s))/(1 + ((H:ℝ)+2*U)/A)) := by
    have heq : ((A:ℝ)/H) * ((((H:ℝ)+2*U)/A - (H:ℝ)/((A:ℝ)+s))
          /(1 + ((H:ℝ)+2*U)/A))
        = ((A:ℝ)*((H:ℝ)*s + 2*(U:ℝ)*((A:ℝ)+s)))
            /((H:ℝ)*(((A:ℝ)+s)*((A:ℝ)+((H:ℝ)+2*U)))) := by
      field_simp
      ring
    rw [heq, le_div_iff₀ (by positivity)]
    have hX0 : (0:ℝ) ≤ ((A:ℝ)+s)*((A:ℝ)+((H:ℝ)+2*U)) := by positivity
    have hstep1 : ε/1200 * ((H:ℝ)*(((A:ℝ)+s)*((A:ℝ)+((H:ℝ)+2*U))))
        ≤ (U:ℝ)/12 * (((A:ℝ)+s)*((A:ℝ)+((H:ℝ)+2*U))) := by
      nlinarith [mul_le_mul_of_nonneg_right hU100 hX0]
    have h24 : ((A:ℝ)+((H:ℝ)+2*U)) ≤ 24*(A:ℝ) := by linarith
    have hstep2 : (U:ℝ)/12 * (((A:ℝ)+s)*((A:ℝ)+((H:ℝ)+2*U)))
        ≤ (A:ℝ)*((H:ℝ)*s + 2*(U:ℝ)*((A:ℝ)+s)) := by
      nlinarith [mul_le_mul_of_nonneg_left h24
          (by positivity : (0:ℝ) ≤ (U:ℝ)/12*(((A:ℝ)+s))),
        mul_nonneg (mul_nonneg hh0.le hs0) ha0.le]
    linarith [hstep1, hstep2]
  -- assemble through the min
  have hminlift : ε/1200 ≤ ((A:ℝ)/H) * (min (Real.log (1 + (U:ℝ)/A)
        - Real.log (1 + (U:ℝ)/(4*((A:ℝ)+s))))
      (Real.log (1 + ((H:ℝ)+2*U)/A)
        - Real.log (1 + (H:ℝ)/((A:ℝ)+s)))) := by
    rcases le_total (Real.log (1 + (U:ℝ)/A)
        - Real.log (1 + (U:ℝ)/(4*((A:ℝ)+s))))
      (Real.log (1 + ((H:ℝ)+2*U)/A)
        - Real.log (1 + (H:ℝ)/((A:ℝ)+s))) with hc | hc
    · rw [min_eq_left hc]
      exact le_trans b_left (mul_le_mul_of_nonneg_left hL10 hAH0)
    · rw [min_eq_right hc]
      exact le_trans b_right (mul_le_mul_of_nonneg_left hL32 hAH0)
  have hchain : (ε/600) * (((A:ℝ)/H)*(Real.log (1 + (H:ℝ)/((A:ℝ)+s))
      - Real.log (1 + (U:ℝ)/A))/2) ≤ ε/1200 := by
    have h1 : ((A:ℝ)/H)*(Real.log (1 + (H:ℝ)/((A:ℝ)+s))
        - Real.log (1 + (U:ℝ)/A)) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left hL21 hAH0) t_up
    nlinarith [mul_le_mul_of_nonneg_left h1 hε0]
  linarith [hchain, hminlift]


/-- **The Mertens mass difference is a log-ratio** (Track R, A2-III,
G10c-2): for `4 ≤ z ≤ x`, the prime harmonic mass between the two
scales is at most `log log x − log log z + 12` — the sharp upper
Mertens bound at `x` against the elementary Mertens floor at `z`.
Feeds `nonPretentiousAt_scale_transfer`: transferring strength from
scale `x` down to `z` costs `2·(loglog-gap) + 24` of the
non-pretentiousness budget. -/
theorem mertens_mass_diff_le (z x : ℕ) (hz : 4 ≤ z) (hzx : z ≤ x) :
    (∑ p ∈ x.primesBelow, (1:ℝ)/p) - (∑ p ∈ z.primesBelow, (1:ℝ)/p)
      ≤ Real.log (Real.log x) - Real.log (Real.log z) + 12 := by
  have hx4 : 4 ≤ x := le_trans hz hzx
  have hupper := sum_one_div_primesBelow_le_sharp x hx4
  have hlower := log_log_le_sum_one_div_primesBelow
    (le_trans (by norm_num) hz)
  linarith


open Finset in
/-- **G10c-2: the low-band block sup** (Track R, A2-III): for every
`ε′ > 0` there are `x₀, W` such that any completely multiplicative
`1`-bounded `g`, non-pretentious at strength `A′ ≥ 2` at both block
endpoints `x₀ ≤ n₁ ≤ n₂`, has

  `‖∑_{n₁<m≤n₂} g(m)·e(−ξ·log m)‖ ≤ 2n₂(ε′ + e^{W loglog n₂ + W − A′/2})`

for every low frequency `|2πξ| ≤ (A′/2)·n₁`.  The phase is the
archimedean cpow twist (`archTwist_phase_eq`), the block is a prefix
difference (`norm_sum_Ioc_le_two_prefix`), and each prefix is priced
by `cheap_halasz_twisted` at its own scale — this is the sup `M_low`
that the trivial low-band energy estimate consumes. -/
theorem low_band_block_sup (ε' : ℝ) (hε' : 0 < ε') :
    ∃ (x₀ : ℕ) (W : ℝ), 0 < W ∧
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → g 1 = 1 →
        (∀ n, ‖g n‖ ≤ 1) →
      ∀ n₁ n₂ : ℕ, x₀ ≤ n₁ → n₁ ≤ n₂ →
      ∀ A' : ℝ, 2 ≤ A' →
        NonPretentiousAt g A' n₁ → NonPretentiousAt g A' n₂ →
      ∀ ξ : ℝ, |2*Real.pi*ξ| ≤ (A'/2)*n₁ →
        ‖∑ m ∈ Finset.Ioc n₁ n₂,
            g m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖
          ≤ 2*((n₂:ℝ)*(ε' + Real.exp (W*Real.log (Real.log n₂)
              + W - A'/2))) := by
  obtain ⟨x₀, W, hW0, hb⟩ := cheap_halasz_twisted ε' hε'
  refine ⟨max x₀ 3, W, hW0, ?_⟩
  intro g hcm hg1 hgb n₁ n₂ hx₀ h12 A' hA' hnp1 hnp2 ξ hξ
  have hn₁3 : 3 ≤ n₁ := le_trans (le_max_right _ _) hx₀
  have hn₁x₀ : x₀ ≤ n₁ := le_trans (le_max_left _ _) hx₀
  have hA'0 : (0:ℝ) ≤ A'/2 := by linarith
  -- the phase is the archimedean cpow twist
  have hrw : ∑ m ∈ Finset.Ioc n₁ n₂,
      g m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)
      = ∑ m ∈ Finset.Ioc n₁ n₂,
          g m * (m:ℂ)^(Complex.I*((-(2*Real.pi*ξ) : ℝ):ℂ)) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Ioc] at hm
    rw [archTwist_phase_eq ξ m (by omega)]
  rw [hrw]
  -- both endpoint prefixes obey the cheap twisted bound at scale n₂
  have hend : ∀ n : ℕ, x₀ ≤ n → 3 ≤ n → n₁ ≤ n → n ≤ n₂ →
      NonPretentiousAt g A' n →
      ‖∑ m ∈ Finset.Icc 1 n,
          g m * (m:ℂ)^(Complex.I*((-(2*Real.pi*ξ) : ℝ):ℂ))‖
        ≤ (n₂:ℝ)*(ε' + Real.exp (W*Real.log (Real.log n₂)
            + W - A'/2)) := by
    intro n hn hn3 hn1n hn2 hnp
    have hn0 : (0:ℝ) < n := by
      have : (0:ℕ) < n := by omega
      exact_mod_cast this
    have hncast : (n:ℝ) ≤ n₂ := by exact_mod_cast hn2
    have hξn : |2*Real.pi*ξ| ≤ (A'/2)*n := by
      refine le_trans hξ (mul_le_mul_of_nonneg_left ?_ hA'0)
      exact_mod_cast hn1n
    have hcheap := hb n hn A' hA' g hcm hg1 hgb hnp (2*Real.pi*ξ) hξn
    rw [div_le_iff₀ hn0] at hcheap
    have hlog_pos : (0:ℝ) < Real.log n :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hll : Real.log (Real.log n) ≤ Real.log (Real.log n₂) :=
      Real.log_le_log hlog_pos (Real.log_le_log hn0 hncast)
    have hexp : Real.exp (W*Real.log (Real.log n) + W - A'/2)
        ≤ Real.exp (W*Real.log (Real.log n₂) + W - A'/2) := by
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left hll hW0.le
      linarith
    calc ‖∑ m ∈ Finset.Icc 1 n,
        g m * (m:ℂ)^(Complex.I*((-(2*Real.pi*ξ) : ℝ):ℂ))‖
        ≤ (ε' + Real.exp (W*Real.log (Real.log n) + W - A'/2))*(n:ℝ) :=
          hcheap
      _ ≤ (ε' + Real.exp (W*Real.log (Real.log n₂) + W - A'/2))*(n₂:ℝ) := by
          refine mul_le_mul (by linarith) hncast hn0.le (by positivity)
      _ = (n₂:ℝ)*(ε' + Real.exp (W*Real.log (Real.log n₂)
            + W - A'/2)) := by ring
  have hE1 := hend n₁ hn₁x₀ hn₁3 le_rfl h12 hnp1
  have hE2 := hend n₂ (le_trans hn₁x₀ h12) (le_trans hn₁3 h12) h12
    le_rfl hnp2
  exact norm_sum_Ioc_le_two_prefix _ n₁ n₂ h12 _ hE1 hE2


open MeasureTheory SchwartzMap LineDeriv in
/-- **N3-a: the slice-window kernel decay** (Track R, A2-III): the
transform of the profile `v ↦ η(Tv)` decays like the inverse
frequency —

  `‖𝓕F(ξ)‖ ≤ 2B′/(π|ξ|)`,

via `𝓕(∂F) = 2πiξ·𝓕F` and the `L¹` mass of the derivative
(`∂F = T·η′(T·)`, support of length `4/T`, sup `T·B′`).  The band
estimate prices the outer mid-band frequencies against exactly this
decay instead of the flat `4/T` sup. -/
theorem norm_fourier_slice_window_decay (T : ℝ) (hT : 0 < T)
    (η : ℝ → ℝ) (hηs : ContDiff ℝ ∞ η)
    (hη2 : ∀ u, η u ≠ 0 → |u| ≤ 2)
    (B' : ℝ) (hB'0 : 0 ≤ B') (hB' : ∀ u, |deriv η u| ≤ B')
    (hd2 : ∀ u, deriv η u ≠ 0 → |u| ≤ 2)
    (ξ : ℝ) (hξ : ξ ≠ 0) :
    ‖𝓕 (fun v => ((η (T*v) : ℝ) : ℂ)) ξ‖ ≤ 2*B'/(π*|ξ|) := by
  obtain ⟨hcs, hcd⟩ := window_profile_props T hT η hηs hη2
  set G : SchwartzMap ℝ ℂ := hcs.toSchwartzMap hcd with hG_def
  have hfun : (fun v : ℝ => ((η (T*v) : ℝ) : ℂ)) = ⇑G := funext fun y => rfl
  rw [hfun]
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
  -- the `L¹` mass of the derivative
  have hcont : Continuous (fun y : ℝ => ‖(∂_{(1:ℝ)} G) y‖) :=
    (∂_{(1:ℝ)} G).continuous.norm
  have hcsD : HasCompactSupport (fun y : ℝ => ‖(∂_{(1:ℝ)} G) y‖) := by
    refine HasCompactSupport.intro
      (isCompact_Icc (a := -(2/T)) (b := 2/T)) ?_
    intro y hy
    rw [hsupp y hy]
    simp
  have hint : Integrable (fun y : ℝ => ‖(∂_{(1:ℝ)} G) y‖) :=
    hcont.integrable_of_hasCompactSupport hcsD
  have hL1 : ∫ y, ‖(∂_{(1:ℝ)} G) y‖ ≤ 4*B' := by
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Set.Icc (-(2/T)) (2/T))
      (fun y hy => by rw [hsupp y hy]; simp)]
    have hnorm_le : ∀ y ∈ Set.Icc (-(2/T)) (2/T),
        ‖(∂_{(1:ℝ)} G) y‖ ≤ T*B' := by
      intro y _
      rw [hderiv y, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos hT]
      exact mul_le_mul_of_nonneg_left (hB' (T*y)) hT.le
    calc ∫ y in Set.Icc (-(2/T)) (2/T), ‖(∂_{(1:ℝ)} G) y‖
        ≤ ∫ _ in Set.Icc (-(2/T)) (2/T), T*B' := by
          refine setIntegral_mono_on hint.integrableOn
            (integrableOn_const measure_Icc_lt_top.ne)
            measurableSet_Icc hnorm_le
      _ = 4*B' := by
          rw [setIntegral_const, smul_eq_mul,
            MeasureTheory.measureReal_def, Real.volume_Icc,
            ENNReal.toReal_ofReal (by
              have h4 : (0:ℝ) < 2/T := by positivity
              linarith : (0:ℝ) ≤ 2/T - (-(2/T)))]
          field_simp
          ring
  -- the derivative identity turns decay into the `L¹` bound
  have hFbound : ‖𝓕 (∂_{(1:ℝ)} G) ξ‖ ≤ ∫ y, ‖(∂_{(1:ℝ)} G) y‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  have hnorm : ‖𝓕 (∂_{(1:ℝ)} G) ξ‖ = 2*π*|ξ| * ‖𝓕 (⇑G) ξ‖ := by
    have h1 : ‖(2 * (π:ℂ) * Complex.I)‖ = 2*π := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have h2 : ‖((ξ:ℝ):ℂ)‖ = |ξ| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have hraw : ‖𝓕 (∂_{(1:ℝ)} G) ξ‖ = 2*π*|ξ| * ‖𝓕 G ξ‖ := by
      rw [fourier_lineDeriv_apply, norm_mul, norm_mul, h1, h2]
    exact hraw
  have hξ0 : (0:ℝ) < |ξ| := abs_pos.mpr hξ
  have hchain : 2*π*|ξ| * ‖𝓕 (⇑G) ξ‖ ≤ 4*B' := by
    rw [← hnorm]
    exact le_trans hFbound hL1
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hchain, Real.pi_pos]


open MeasureTheory in
/-- **N3-c1: one dyadic ring of the outer band** (Track R, A2-III):
on the ring `a ≤ |ξ| ≤ 2a`, the kernel decay is flat at the inner
edge and the ring energy embeds into the `±2a` window, where the
plain-weight rescale and the short-interval MVT price it —

  `∫_ring ‖P(ξ)‖²·(2B′/(π|ξ|))² ≤ (2B′/(πa))²·(2A+1)²·(4a·Σ1/n² + (log Δ+1)·Σ1/n)`.

The dyadic ring sum over these closes the outer mid-band with no
number theory. -/
theorem ring_energy_decay_le (A Δ : ℕ) (hΔ : 1 ≤ Δ) (hΔA : Δ ≤ A)
    (S : Finset ℕ) (hS : S ⊆ Finset.Ioc A (A+Δ))
    (h : ℕ → ℂ) (hb : ∀ m, ‖h m‖ ≤ 1)
    (B' a : ℝ) (hB' : 0 ≤ B') (ha : 0 < a) :
    ∫ ξ in {ξ : ℝ | a ≤ |ξ| ∧ |ξ| ≤ 2*a},
        ‖∑ m ∈ S, h m
            * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
          * (2*B'/(π*|ξ|))^2
      ≤ (2*B'/(π*a))^2 * ((2*(A:ℝ)+1)^2
          * (Real.exp Real.pi * (2*a/(A:ℝ) + 4)
              * (∑ n ∈ S, (1:ℝ)/n))) := by
  classical
  have hA : 1 ≤ A := le_trans hΔ hΔA
  have hS2A : S ⊆ Finset.Ioc A (2*A) := by
    refine hS.trans (Finset.Ioc_subset_Ioc_right ?_)
    omega
  have hphase_cont : Continuous fun ξ : ℝ =>
      ∑ m ∈ S, h m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) := by
    refine continuous_finset_sum _ fun m _ => ?_
    refine Continuous.mul continuous_const ?_
    refine Continuous.comp continuous_subtype_val ?_
    exact Real.continuous_fourierChar.comp (by fun_prop)
  have hPc : Continuous fun ξ : ℝ =>
      ‖∑ m ∈ S, h m
        * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2 :=
    hphase_cont.norm.pow 2
  -- ring geometry
  have hclosed : IsClosed {ξ : ℝ | a ≤ |ξ| ∧ |ξ| ≤ 2*a} :=
    (isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const)
  have hsubIcc : {ξ : ℝ | a ≤ |ξ| ∧ |ξ| ≤ 2*a}
      ⊆ Set.Icc (-(2*a)) (2*a) := by
    rintro ξ ⟨_, h2⟩
    exact abs_le.mp h2
  have hcomp : IsCompact {ξ : ℝ | a ≤ |ξ| ∧ |ξ| ≤ 2*a} :=
    (isCompact_Icc (a := -(2*a)) (b := 2*a)).of_isClosed_subset
      hclosed hsubIcc
  have hmeas : MeasurableSet {ξ : ℝ | a ≤ |ξ| ∧ |ξ| ≤ 2*a} :=
    hclosed.measurableSet
  -- flatten the decay on the ring
  have hint1 : IntegrableOn (fun ξ : ℝ =>
      ‖∑ m ∈ S, h m
        * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
        * (2*B'/(π*|ξ|))^2) {ξ : ℝ | a ≤ |ξ| ∧ |ξ| ≤ 2*a} := by
    refine ContinuousOn.integrableOn_compact hcomp ?_
    refine ContinuousOn.mul hPc.continuousOn ?_
    refine ContinuousOn.pow ?_ 2
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact (continuous_const.mul continuous_abs).continuousOn
    · rintro ξ ⟨h1, _⟩
      have : (0:ℝ) < |ξ| := lt_of_lt_of_le ha h1
      positivity
  have hint2 : IntegrableOn (fun ξ : ℝ =>
      (2*B'/(π*a))^2 * ‖∑ m ∈ S, h m
        * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2)
      {ξ : ℝ | a ≤ |ξ| ∧ |ξ| ≤ 2*a} :=
    (hPc.continuousOn.integrableOn_compact hcomp).const_mul _
  have hstep1 : ∫ ξ in {ξ : ℝ | a ≤ |ξ| ∧ |ξ| ≤ 2*a},
      ‖∑ m ∈ S, h m
        * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
        * (2*B'/(π*|ξ|))^2
      ≤ ∫ ξ in {ξ : ℝ | a ≤ |ξ| ∧ |ξ| ≤ 2*a},
        (2*B'/(π*a))^2 * ‖∑ m ∈ S, h m
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2 := by
    refine setIntegral_mono_on hint1 hint2 hmeas ?_
    rintro ξ ⟨h1, _⟩
    have hξ0 : (0:ℝ) < |ξ| := lt_of_lt_of_le ha h1
    have hdec : (2*B'/(π*|ξ|))^2 ≤ (2*B'/(π*a))^2 := by
      have hle : 2*B'/(π*|ξ|) ≤ 2*B'/(π*a) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left h1 Real.pi_pos.le
      have h0 : (0:ℝ) ≤ 2*B'/(π*|ξ|) := by positivity
      exact pow_le_pow_left₀ h0 hle 2
    calc ‖∑ m ∈ S, h m
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
          * (2*B'/(π*|ξ|))^2
        ≤ ‖∑ m ∈ S, h m
            * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
            * (2*B'/(π*a))^2 :=
          mul_le_mul_of_nonneg_left hdec (by positivity)
      _ = (2*B'/(π*a))^2 * ‖∑ m ∈ S, h m
            * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2 := by
          ring
  -- pull the constant, embed the ring into the window
  have hstep2 : ∫ ξ in {ξ : ℝ | a ≤ |ξ| ∧ |ξ| ≤ 2*a},
      (2*B'/(π*a))^2 * ‖∑ m ∈ S, h m
        * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
      = (2*B'/(π*a))^2 * ∫ ξ in {ξ : ℝ | a ≤ |ξ| ∧ |ξ| ≤ 2*a},
        ‖∑ m ∈ S, h m
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2 :=
    integral_const_mul _ _
  have hstep3 : ∫ ξ in {ξ : ℝ | a ≤ |ξ| ∧ |ξ| ≤ 2*a},
      ‖∑ m ∈ S, h m
        * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
      ≤ ∫ ξ in (-(2*a))..(2*a),
        ‖∑ m ∈ S, h m
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2 := by
    have hIccInt : IntegrableOn (fun ξ : ℝ =>
        ‖∑ m ∈ S, h m
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2)
        (Set.Icc (-(2*a)) (2*a)) :=
      hPc.continuousOn.integrableOn_compact isCompact_Icc
    have h1 : ∫ ξ in {ξ : ℝ | a ≤ |ξ| ∧ |ξ| ≤ 2*a},
        ‖∑ m ∈ S, h m
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
        ≤ ∫ ξ in Set.Icc (-(2*a)) (2*a),
          ‖∑ m ∈ S, h m
            * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2 := by
      refine setIntegral_mono_set hIccInt ?_ ?_
      · exact Filter.Eventually.of_forall fun ξ => by positivity
      · exact HasSubset.Subset.eventuallyLE hsubIcc
    rw [intervalIntegral.integral_of_le (by linarith)]
    calc ∫ ξ in {ξ : ℝ | a ≤ |ξ| ∧ |ξ| ≤ 2*a},
        ‖∑ m ∈ S, h m
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
        ≤ ∫ ξ in Set.Icc (-(2*a)) (2*a),
          ‖∑ m ∈ S, h m
            * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2 := h1
      _ = ∫ ξ in Set.Ioc (-(2*a)) (2*a),
          ‖∑ m ∈ S, h m
            * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2 :=
          integral_Icc_eq_integral_Ioc
  -- the plain rescale into the short MVT
  have hstep4 : ∫ ξ in (-(2*a))..(2*a),
      ‖∑ m ∈ S, h m
        * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
      ≤ (2*(A:ℝ)+1)^2
        * (Real.exp Real.pi * (2*a/(A:ℝ) + 4)
            * (∑ n ∈ S, (1:ℝ)/n)) := by
    set c : ℕ → ℂ := fun m => if m ≤ 2*A+1
        then (m:ℂ) * h m / (2*(A:ℕ)+1 : ℕ) else 0 with hc_def
    have hcb : ∀ m, ‖c m‖ ≤ 1 := by
      intro m
      simp only [hc_def]
      by_cases hm : m ≤ 2*A+1
      · rw [if_pos hm, norm_div, norm_mul, Complex.norm_natCast,
          Complex.norm_natCast]
        have hden : (0:ℝ) < ((2*A+1 : ℕ):ℝ) := by
          exact_mod_cast (by omega : 0 < 2*A+1)
        rw [div_le_one hden]
        have h1 : (m:ℝ) ≤ ((2*A+1 : ℕ):ℝ) := by exact_mod_cast hm
        have h2 := hb m
        nlinarith [norm_nonneg (h m), Nat.cast_nonneg (α := ℝ) m]
      · rw [if_neg hm]
        simp
    have hpoint : ∀ ξ : ℝ, ‖∑ m ∈ S,
        h m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
        = (2*(A:ℝ)+1)^2 * ‖∑ m ∈ S, (c m/(m:ℂ))
            * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2 := by
      intro ξ
      have hfac : ∑ m ∈ S,
          h m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)
          = ((2*(A:ℕ)+1 : ℕ):ℂ) * ∑ m ∈ S, (c m/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hmIoc := hS hm
        rw [Finset.mem_Ioc] at hmIoc
        have hmle : m ≤ 2*A+1 := by omega
        have hm0 : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hden : ((2*(A:ℕ)+1 : ℕ):ℂ) ≠ 0 :=
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
    have hsharp := intervalIntegral_norm_sq_short_poly_le_sharp_of_bound
      A hA S hS2A c 1 (by norm_num) hcb (2*a) (by linarith)
    simpa using hsharp
  calc ∫ ξ in {ξ : ℝ | a ≤ |ξ| ∧ |ξ| ≤ 2*a},
      ‖∑ m ∈ S, h m
        * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
        * (2*B'/(π*|ξ|))^2
      ≤ _ := hstep1
    _ = _ := hstep2
    _ ≤ (2*B'/(π*a))^2 * ((2*(A:ℝ)+1)^2
        * (Real.exp Real.pi * (2*a/(A:ℝ) + 4)
            * (∑ n ∈ S, (1:ℝ)/n))) := by
      refine mul_le_mul_of_nonneg_left (le_trans hstep3 hstep4)
        (by positivity)


open MeasureTheory in
/-- **N3-c2a: a band is covered by its dyadic rings** (Track R,
A2-III): for a nonnegative integrand, the band `a ≤ |ξ| < 2^J·a`
splits into the `J` half-open dyadic rings, each dominated by its
closed ring — the covering step of the outer-band estimate. -/
theorem setIntegral_band_le_sum_rings (f : ℝ → ℝ) (hf0 : ∀ ξ, 0 ≤ f ξ)
    (a : ℝ) (ha : 0 < a) (J : ℕ)
    (hint : ∀ j : ℕ, IntegrableOn f
      {ξ : ℝ | 2^j*a ≤ |ξ| ∧ |ξ| ≤ 2^(j+1)*a}) :
    ∫ ξ in {ξ : ℝ | a ≤ |ξ| ∧ |ξ| < 2^J*a}, f ξ
      ≤ ∑ j ∈ Finset.range J,
          ∫ ξ in {ξ : ℝ | 2^j*a ≤ |ξ| ∧ |ξ| ≤ 2^(j+1)*a}, f ξ := by
  classical
  -- the half-open rings sit inside the closed ones
  have hsub : ∀ j : ℕ, {ξ : ℝ | 2^j*a ≤ |ξ| ∧ |ξ| < 2^(j+1)*a}
      ⊆ {ξ : ℝ | 2^j*a ≤ |ξ| ∧ |ξ| ≤ 2^(j+1)*a} := by
    rintro j ξ ⟨h1, h2⟩
    exact ⟨h1, h2.le⟩
  have hmeasHalf : ∀ c d : ℝ,
      MeasurableSet {ξ : ℝ | c ≤ |ξ| ∧ |ξ| < d} :=
    fun c d => (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  have hintHalf : ∀ j : ℕ, IntegrableOn f
      {ξ : ℝ | 2^j*a ≤ |ξ| ∧ |ξ| < 2^(j+1)*a} :=
    fun j => (hint j).mono_set (hsub j)
  -- the growing band is integrable
  have hband : ∀ K : ℕ, IntegrableOn f
      {ξ : ℝ | a ≤ |ξ| ∧ |ξ| < 2^K*a} := by
    intro K
    induction K with
    | zero =>
        have hempty : {ξ : ℝ | a ≤ |ξ| ∧ |ξ| < 2^(0:ℕ)*a} = ∅ := by
          ext ξ
          simp only [pow_zero, one_mul, Set.mem_setOf_eq,
            Set.mem_empty_iff_false, iff_false, not_and, not_lt]
          exact fun h => h
        rw [hempty]
        exact integrableOn_empty
    | succ K ih =>
        have hsplit : {ξ : ℝ | a ≤ |ξ| ∧ |ξ| < 2^(K+1)*a}
            = {ξ : ℝ | a ≤ |ξ| ∧ |ξ| < 2^K*a}
              ∪ {ξ : ℝ | 2^K*a ≤ |ξ| ∧ |ξ| < 2^(K+1)*a} := by
          have h1 : (1:ℝ) ≤ 2^K := one_le_pow₀ (by norm_num)
          have haK : a ≤ 2^K*a := by nlinarith
          ext ξ
          simp only [Set.mem_setOf_eq, Set.mem_union]
          constructor
          · rintro ⟨h1', h2'⟩
            rcases lt_or_ge |ξ| (2^K*a) with h | h
            · exact Or.inl ⟨h1', h⟩
            · exact Or.inr ⟨h, h2'⟩
          · rintro (⟨h1', h2'⟩ | ⟨h1', h2'⟩)
            · refine ⟨h1', lt_of_lt_of_le h2' ?_⟩
              rw [pow_succ]
              nlinarith
            · exact ⟨le_trans haK h1', h2'⟩
        rw [hsplit]
        exact ih.union (hintHalf K)
  -- the main induction
  induction J with
  | zero =>
      have hempty : {ξ : ℝ | a ≤ |ξ| ∧ |ξ| < 2^(0:ℕ)*a} = ∅ := by
        ext ξ
        simp only [pow_zero, one_mul, Set.mem_setOf_eq,
          Set.mem_empty_iff_false, iff_false, not_and, not_lt]
        exact fun h => h
      rw [hempty]
      simp
  | succ J ih =>
      have h1 : (1:ℝ) ≤ 2^J := one_le_pow₀ (by norm_num)
      have haJ : a ≤ 2^J*a := by nlinarith
      have hsplit : {ξ : ℝ | a ≤ |ξ| ∧ |ξ| < 2^(J+1)*a}
          = {ξ : ℝ | a ≤ |ξ| ∧ |ξ| < 2^J*a}
            ∪ {ξ : ℝ | 2^J*a ≤ |ξ| ∧ |ξ| < 2^(J+1)*a} := by
        ext ξ
        simp only [Set.mem_setOf_eq, Set.mem_union]
        constructor
        · rintro ⟨h1', h2'⟩
          rcases lt_or_ge |ξ| (2^J*a) with h | h
          · exact Or.inl ⟨h1', h⟩
          · exact Or.inr ⟨h, h2'⟩
        · rintro (⟨h1', h2'⟩ | ⟨h1', h2'⟩)
          · refine ⟨h1', lt_of_lt_of_le h2' ?_⟩
            rw [pow_succ]
            nlinarith
          · exact ⟨le_trans haJ h1', h2'⟩
      have hdisj : Disjoint {ξ : ℝ | a ≤ |ξ| ∧ |ξ| < 2^J*a}
          {ξ : ℝ | 2^J*a ≤ |ξ| ∧ |ξ| < 2^(J+1)*a} := by
        rw [Set.disjoint_left]
        rintro ξ ⟨_, h2⟩ ⟨h3, _⟩
        linarith
      rw [hsplit, setIntegral_union hdisj (hmeasHalf _ _)
        (hband J) (hintHalf J), Finset.sum_range_succ]
      have hlast : ∫ ξ in {ξ : ℝ | 2^J*a ≤ |ξ| ∧ |ξ| < 2^(J+1)*a}, f ξ
          ≤ ∫ ξ in {ξ : ℝ | 2^J*a ≤ |ξ| ∧ |ξ| ≤ 2^(J+1)*a}, f ξ := by
        refine setIntegral_mono_set (hint J)
          (Filter.Eventually.of_forall fun ξ => hf0 ξ) ?_
        exact HasSubset.Subset.eventuallyLE (hsub J)
      linarith [ih, hlast]


/-- Finite geometric sums are at most `1/(1 − x)` on `[0, 1)` (the
copy in `MertensFloor` is private). -/
private theorem geom_sum_le_one_div' (K : ℕ) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x < 1) :
    ∑ k ∈ Finset.range K, x ^ k ≤ 1 / (1 - x) := by
  have h1x : (0 : ℝ) < 1 - x := by linarith
  have h := geom_sum_mul x K
  have hpow : (0 : ℝ) ≤ x ^ K := pow_nonneg hx0 K
  rw [le_div_iff₀ h1x]
  nlinarith [h, hpow]

open MeasureTheory in
/-- **N3-c2b: the outer band closes with no number theory** (Track R,
A2-III): summing the dyadic ring estimate over `K₂ ≤ |ξ| ≤ L`, the
geometric gains `∑ 2^{-j} ≤ 2` and `∑ 4^{-j} ≤ 4/3` give

  `∫ ≤ (4B′²/π²)·(2A+1)²·((8/K₂)·∑1/n² + (2/K₂²)·(log Δ+1)·∑1/n)`

for any `J` with `L < 2^J·K₂` — kernel decay and the short-interval
mean value theorem only.  The `[MR]` 𝒰-machinery is needed strictly
below `K₂`. -/
theorem band_energy_outer_le (A Δ : ℕ) (hΔ : 1 ≤ Δ) (hΔA : Δ ≤ A)
    (S : Finset ℕ) (hS : S ⊆ Finset.Ioc A (A+Δ))
    (h : ℕ → ℂ) (hb : ∀ m, ‖h m‖ ≤ 1)
    (B' K₂ L : ℝ) (hB' : 0 ≤ B') (hK₂ : 0 < K₂)
    (J : ℕ) (hJ : L < 2^J*K₂) :
    ∫ ξ in {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L},
        ‖∑ m ∈ S, h m
            * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
          * (2*B'/(π*|ξ|))^2
      ≤ (4*B'^2/π^2) * ((2*(A:ℝ)+1)^2
          * (Real.exp Real.pi * ((4/(K₂*(A:ℝ))) + (6/K₂^2))
              * (∑ n ∈ S, (1:ℝ)/n))) := by
  classical
  set f : ℝ → ℝ := fun ξ =>
    ‖∑ m ∈ S, h m
      * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
      * (2*B'/(π*|ξ|))^2 with hf_def
  have hf0 : ∀ ξ, 0 ≤ f ξ := fun ξ => by
    rw [hf_def]
    positivity
  have hphase_cont : Continuous fun ξ : ℝ =>
      ∑ m ∈ S, h m
        * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) := by
    refine continuous_finset_sum _ fun m _ => ?_
    refine Continuous.mul continuous_const ?_
    refine Continuous.comp continuous_subtype_val ?_
    exact Real.continuous_fourierChar.comp (by fun_prop)
  -- `f` is integrable on any closed annulus away from the origin
  have hintAnn : ∀ c d : ℝ, 0 < c →
      IntegrableOn f {ξ : ℝ | c ≤ |ξ| ∧ |ξ| ≤ d} := by
    intro c d hc
    have hclosed : IsClosed {ξ : ℝ | c ≤ |ξ| ∧ |ξ| ≤ d} :=
      (isClosed_le continuous_const continuous_abs).inter
        (isClosed_le continuous_abs continuous_const)
    have hsubIcc : {ξ : ℝ | c ≤ |ξ| ∧ |ξ| ≤ d} ⊆ Set.Icc (-d) d := by
      rintro ξ ⟨_, h2⟩
      exact abs_le.mp h2
    have hcomp : IsCompact {ξ : ℝ | c ≤ |ξ| ∧ |ξ| ≤ d} :=
      (isCompact_Icc (a := -d) (b := d)).of_isClosed_subset hclosed
        hsubIcc
    refine ContinuousOn.integrableOn_compact hcomp ?_
    rw [hf_def]
    refine ContinuousOn.mul (hphase_cont.norm.pow 2).continuousOn ?_
    refine ContinuousOn.pow ?_ 2
    refine ContinuousOn.div continuousOn_const
      (continuous_const.mul continuous_abs).continuousOn ?_
    rintro ξ ⟨h1, _⟩
    have : (0:ℝ) < |ξ| := lt_of_lt_of_le hc h1
    positivity
  -- the band embeds in the dyadic sweep
  have hsubBand : {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L}
      ⊆ {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| < 2^J*K₂} := by
    rintro ξ ⟨h1, h2⟩
    exact ⟨h1, lt_of_le_of_lt h2 hJ⟩
  have hstep0 : ∫ ξ in {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L}, f ξ
      ≤ ∫ ξ in {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| < 2^J*K₂}, f ξ := by
    have hbandInt : IntegrableOn f
        {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| < 2^J*K₂} := by
      refine (hintAnn K₂ (2^J*K₂) hK₂).mono_set ?_
      rintro ξ ⟨h1, h2⟩
      exact ⟨h1, h2.le⟩
    refine setIntegral_mono_set hbandInt
      (Filter.Eventually.of_forall fun ξ => hf0 ξ) ?_
    exact HasSubset.Subset.eventuallyLE hsubBand
  -- the ring cover
  have hrings := setIntegral_band_le_sum_rings f hf0 K₂ hK₂ J
    (fun j => hintAnn (2^j*K₂) (2^(j+1)*K₂) (by positivity))
  -- each ring by the dyadic ring estimate
  have hring : ∀ j ∈ Finset.range J,
      ∫ ξ in {ξ : ℝ | 2^j*K₂ ≤ |ξ| ∧ |ξ| ≤ 2^(j+1)*K₂}, f ξ
        ≤ (4*B'^2/π^2) * ((2*(A:ℝ)+1)^2
            * (Real.exp Real.pi
                * ((2/(2^j*K₂*(A:ℝ))) + (4/(2^j*K₂)^2))
                * (∑ n ∈ S, (1:ℝ)/n))) := by
    intro j _
    have hj0 : (0:ℝ) < 2^j*K₂ := by positivity
    have hpow : (2:ℝ)^(j+1)*K₂ = 2*(2^j*K₂) := by
      rw [pow_succ]
      ring
    have hbase := ring_energy_decay_le A Δ hΔ hΔA S hS h hb B'
      (2^j*K₂) hB' hj0
    rw [hpow]
    refine le_trans hbase (le_of_eq ?_)
    have hne : (2:ℝ)^j*K₂ ≠ 0 := ne_of_gt hj0
    have hπ : (π:ℝ) ≠ 0 := ne_of_gt Real.pi_pos
    field_simp
    ring
  -- collect the geometric sums
  have hgeo2 : ∑ j ∈ Finset.range J, ((1:ℝ)/2)^j ≤ 2 :=
    sum_geometric_two_le J
  have hgeo4 : ∑ j ∈ Finset.range J, ((1:ℝ)/4)^j ≤ 4/3 := by
    have := geom_sum_le_one_div' J (x := (1:ℝ)/4) (by norm_num)
      (by norm_num)
    norm_num at this
    linarith
  have hKne : (K₂:ℝ) ≠ 0 := ne_of_gt hK₂
  have hA0 : (0:ℝ) < A := by
    have : 1 ≤ A := le_trans hΔ hΔA
    exact_mod_cast this
  -- the dyadic weights sum geometrically
  have hXsum : ∑ j ∈ Finset.range J,
      ((2/(2^j*K₂*(A:ℝ))) + (4/(2^j*K₂)^2))
      ≤ (4/(K₂*(A:ℝ))) + (6/K₂^2) := by
    have hterm : ∀ j ∈ Finset.range J,
        ((2/(2^j*K₂*(A:ℝ))) + (4/(2^j*K₂)^2))
        = (2/(K₂*(A:ℝ))) * ((1:ℝ)/2)^j + (4/K₂^2) * ((1:ℝ)/4)^j := by
      intro j _
      have hne : ((2:ℝ)^j) ≠ 0 := by positivity
      have h2 : ((1:ℝ)/2)^j = 1/((2:ℝ)^j) := by
        rw [div_pow, one_pow]
      have h4 : ((1:ℝ)/4)^j = 1/(((2:ℝ)^j)^2) := by
        rw [div_pow, one_pow, show (4:ℝ) = 2^2 by norm_num,
          ← pow_mul, ← pow_mul, Nat.mul_comm]
      rw [h2, h4]
      field_simp
    calc ∑ j ∈ Finset.range J, ((2/(2^j*K₂*(A:ℝ))) + (4/(2^j*K₂)^2))
        = ∑ j ∈ Finset.range J,
            ((2/(K₂*(A:ℝ))) * ((1:ℝ)/2)^j + (4/K₂^2) * ((1:ℝ)/4)^j) :=
          Finset.sum_congr rfl hterm
      _ = (2/(K₂*(A:ℝ))) * (∑ j ∈ Finset.range J, ((1:ℝ)/2)^j)
            + (4/K₂^2) * ∑ j ∈ Finset.range J, ((1:ℝ)/4)^j := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ (4/(K₂*(A:ℝ))) + (6/K₂^2) := by
          have hc2 : (0:ℝ) ≤ 2/(K₂*(A:ℝ)) := by positivity
          have hc4 : (0:ℝ) ≤ 4/K₂^2 := by positivity
          have hb2 : (2/(K₂*(A:ℝ))) * (∑ j ∈ Finset.range J, ((1:ℝ)/2)^j)
              ≤ 4/(K₂*(A:ℝ)) := by
            calc (2/(K₂*(A:ℝ))) * (∑ j ∈ Finset.range J, ((1:ℝ)/2)^j)
                ≤ (2/(K₂*(A:ℝ))) * 2 :=
                  mul_le_mul_of_nonneg_left hgeo2 hc2
              _ = 4/(K₂*(A:ℝ)) := by ring
          have hb4 : (4/K₂^2) * (∑ j ∈ Finset.range J, ((1:ℝ)/4)^j)
              ≤ 6/K₂^2 := by
            calc (4/K₂^2) * (∑ j ∈ Finset.range J, ((1:ℝ)/4)^j)
                ≤ (4/K₂^2) * (4/3) :=
                  mul_le_mul_of_nonneg_left hgeo4 hc4
              _ = (16/3)/K₂^2 := by ring
              _ ≤ 6/K₂^2 :=
                  div_le_div_of_nonneg_right (by norm_num)
                    (by positivity)
          linarith
  -- assemble
  have hmass : (0:ℝ) ≤ ∑ n ∈ S, (1:ℝ)/n :=
    Finset.sum_nonneg fun n _ => by positivity
  have hconst : (0:ℝ) ≤ (4*B'^2/π^2) * ((2*(A:ℝ)+1)^2
      * (Real.exp Real.pi * (∑ n ∈ S, (1:ℝ)/n))) := by positivity
  have hfactor : ∀ j : ℕ,
      (4*B'^2/π^2) * ((2*(A:ℝ)+1)^2
        * (Real.exp Real.pi
            * ((2/(2^j*K₂*(A:ℝ))) + (4/(2^j*K₂)^2))
            * (∑ n ∈ S, (1:ℝ)/n)))
      = ((4*B'^2/π^2) * ((2*(A:ℝ)+1)^2
          * (Real.exp Real.pi * (∑ n ∈ S, (1:ℝ)/n))))
        * ((2/(2^j*K₂*(A:ℝ))) + (4/(2^j*K₂)^2)) := by
    intro j
    ring
  calc ∫ ξ in {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L}, f ξ
      ≤ ∫ ξ in {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| < 2^J*K₂}, f ξ := hstep0
    _ ≤ ∑ j ∈ Finset.range J,
          ∫ ξ in {ξ : ℝ | 2^j*K₂ ≤ |ξ| ∧ |ξ| ≤ 2^(j+1)*K₂}, f ξ :=
        hrings
    _ ≤ ∑ j ∈ Finset.range J,
          ((4*B'^2/π^2) * ((2*(A:ℝ)+1)^2
            * (Real.exp Real.pi
                * ((2/(2^j*K₂*(A:ℝ))) + (4/(2^j*K₂)^2))
                * (∑ n ∈ S, (1:ℝ)/n)))) :=
        Finset.sum_le_sum hring
    _ = ∑ j ∈ Finset.range J,
          (((4*B'^2/π^2) * ((2*(A:ℝ)+1)^2
              * (Real.exp Real.pi * (∑ n ∈ S, (1:ℝ)/n))))
            * ((2/(2^j*K₂*(A:ℝ))) + (4/(2^j*K₂)^2))) :=
        Finset.sum_congr rfl fun j _ => hfactor j
    _ = ((4*B'^2/π^2) * ((2*(A:ℝ)+1)^2
          * (Real.exp Real.pi * (∑ n ∈ S, (1:ℝ)/n))))
        * ∑ j ∈ Finset.range J,
            ((2/(2^j*K₂*(A:ℝ))) + (4/(2^j*K₂)^2)) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ ((4*B'^2/π^2) * ((2*(A:ℝ)+1)^2
          * (Real.exp Real.pi * (∑ n ∈ S, (1:ℝ)/n))))
        * ((4/(K₂*(A:ℝ))) + (6/K₂^2)) :=
        mul_le_mul_of_nonneg_left hXsum hconst
    _ = (4*B'^2/π^2) * ((2*(A:ℝ)+1)^2
          * (Real.exp Real.pi * ((4/(K₂*(A:ℝ))) + (6/K₂^2))
              * (∑ n ∈ S, (1:ℝ)/n))) := by
        ring


open Finset in
/-- **Geometric decay over an e-adic index range** (Track R, A2-III,
II-5a): a sum of `e^{−αv/N}` over `v ∈ [v₀, v₁]` is at most its first
term times `N/α + 1`.

The `[MR]` level estimates sum exactly such series over the e-adic
cell indices — the cell at index `v` contributes `e^{−αv/N}` from the
pointwise smallness hypothesis, and this is the resulting geometric
total.  The factor `N/α + 1` comes from `1/(1 − e^{−x}) ≤ 1/x + 1`,
i.e. from `1 + x ≤ eˣ`. -/
theorem sum_exp_neg_index_le (α : ℝ) (hα : 0 < α) (N : ℕ) (hN : 0 < N)
    (v₀ v₁ : ℕ) :
    ∑ v ∈ Finset.Ico v₀ (v₁+1), Real.exp (-(α*(v:ℝ)/N))
      ≤ Real.exp (-(α*(v₀:ℝ)/N)) * ((N:ℝ)/α + 1) := by
  classical
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  set x : ℝ := α/(N:ℝ) with hx_def
  have hx0 : 0 < x := by
    rw [hx_def]
    positivity
  set r : ℝ := Real.exp (-x) with hr_def
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr_def]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  -- reindex from `v₀` and factor out the first term
  have hshift : ∑ v ∈ Finset.Ico v₀ (v₁+1), Real.exp (-(α*(v:ℝ)/N))
      = Real.exp (-(α*(v₀:ℝ)/N))
          * ∑ j ∈ Finset.range (v₁+1-v₀), r^j := by
    rw [Finset.mul_sum]
    rw [show Finset.Ico v₀ (v₁+1)
        = (Finset.range (v₁+1-v₀)).image (fun j => v₀ + j) by
      ext v
      simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨v - v₀, by omega, by omega⟩
      · rintro ⟨j, hj, rfl⟩
        omega]
    rw [Finset.sum_image (by intro a _ b _ hab; simpa using hab)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hr_def, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    rw [hx_def]
    push_cast
    field_simp
    ring
  rw [hshift]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  -- the geometric total, and `1/(1 − e^{−x}) ≤ 1/x + 1`
  refine le_trans (geom_sum_le_one_div' (v₁+1-v₀) hr0 hr1) ?_
  have hxe : Real.exp (-x) ≤ 1/(1+x) := by
    have h1 : 1 + x ≤ Real.exp x := by
      have := Real.add_one_le_exp x
      linarith
    have h2 : (0:ℝ) < 1 + x := by linarith
    rw [Real.exp_neg, inv_eq_one_div]
    rw [div_le_div_iff₀ (Real.exp_pos x) h2]
    linarith
  have hden : x/(1+x) ≤ 1 - r := by
    have h2 : (0:ℝ) < 1 + x := by linarith
    have : r ≤ 1/(1+x) := by
      rw [hr_def]
      exact hxe
    have heq : 1 - 1/(1+x) = x/(1+x) := by
      field_simp
      ring
    linarith [this, heq.le, heq.ge]
  have h1r : (0:ℝ) < 1 - r := by linarith
  have hxx : (0:ℝ) < x/(1+x) := by positivity
  rw [div_le_iff₀ h1r]
  have hgoal : (1:ℝ) ≤ ((N:ℝ)/α + 1) * (x/(1+x)) := by
    have heq : ((N:ℝ)/α + 1) * (x/(1+x)) = 1 := by
      rw [hx_def]
      field_simp
    linarith [heq.le, heq.ge]
  calc (1:ℝ) ≤ ((N:ℝ)/α + 1) * (x/(1+x)) := hgoal
    _ ≤ ((N:ℝ)/α + 1) * (1 - r) := by
        refine mul_le_mul_of_nonneg_left hden ?_
        positivity


open Finset in
/-- **Geometric growth over an e-adic index range** (Track R, A2-III,
II-5b-0): a sum of `e^{βv/N}` over `v ∈ [v₀, v₁]` is at most
`e^{β(v₁+1)/N}·(N/β + 1)` — its last term, inflated by one step, times
the same factor `N/β + 1` that `sum_exp_neg_index_le` pays.

The increasing companion of `sum_exp_neg_index_le`, and the `[MR]`
level estimates need both at once.  At e-adic index `v` the cell scale
is `A e^{−v/N}`, so the mean value theorem charges `T e^{v/N}/A`, which
*grows* in `v`, while the pointwise cell smallness contributes
`e^{−2αv/N}`, which *decays*.  The product runs at exponent `1 − 2α`:
one geometric series each way, this lemma for the `1 − 2α > 0` half and
`sum_exp_neg_index_le` for the `2α > 0` half.

Proved by induction on `v₁` rather than by reindexing, on the one-step
inequality `N/β + 2 ≤ e^{β/N}(N/β + 1)` — which is just
`(1+x)² ≥ 1 + 2x` after `1 + x ≤ eˣ`. -/
theorem sum_exp_index_le (β : ℝ) (hβ : 0 < β) (N : ℕ) (hN : 0 < N)
    (v₀ v₁ : ℕ) :
    ∑ v ∈ Finset.Ico v₀ (v₁+1), Real.exp (β*(v:ℝ)/N)
      ≤ Real.exp (β*((v₁:ℝ)+1)/N) * ((N:ℝ)/β + 1) := by
  classical
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hc0 : (0:ℝ) < (N:ℝ)/β := by positivity
  -- the one-step inequality, at an arbitrary base exponent
  have hstep : ∀ y : ℝ, Real.exp y * ((N:ℝ)/β + 2)
      ≤ Real.exp (y + β/(N:ℝ)) * ((N:ℝ)/β + 1) := by
    intro y
    set x : ℝ := β/(N:ℝ) with hx_def
    have hx0 : 0 < x := by rw [hx_def]; positivity
    have hinv : (N:ℝ)/β = 1/x := by
      rw [hx_def]
      field_simp
    have hex : 1 + x ≤ Real.exp x := by
      have := Real.add_one_le_exp x
      linarith
    -- `eˣ(1/x + 1) ≥ (1+x)²/x ≥ 1/x + 2`
    have hkey : (1:ℝ)/x + 2 ≤ Real.exp x * (1/x + 1) := by
      have h1 : (1:ℝ)/x + 1 = (1+x)/x := by field_simp
      have h2 : (1+x)/x * (1+x) ≤ (1+x)/x * Real.exp x := by
        refine mul_le_mul_of_nonneg_left hex ?_
        positivity
      have h3 : (1:ℝ)/x + 2 ≤ (1+x)/x * (1+x) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hx0]
        have hxe : (1/x + 2) * x = 1 + 2*x := by
          field_simp
        rw [hxe]
        nlinarith [sq_nonneg x]
      rw [h1]
      nlinarith [h2, h3]
    rw [Real.exp_add, hinv]
    calc Real.exp y * (1/x + 2) ≤ Real.exp y * (Real.exp x * (1/x + 1)) := by
          refine mul_le_mul_of_nonneg_left hkey (Real.exp_pos y).le
      _ = Real.exp y * Real.exp x * (1/x + 1) := by ring
  induction v₁ with
  | zero =>
      rcases Nat.eq_zero_or_pos v₀ with rfl | hv₀
      · have hIco : Finset.Ico 0 1 = {0} := rfl
        rw [hIco, Finset.sum_singleton]
        have h1 : Real.exp (β*((0:ℕ):ℝ)/N) = 1 := by norm_num
        have h2 : (1:ℝ) ≤ Real.exp (β*(((0:ℕ):ℝ)+1)/N) := by
          refine Real.one_le_exp ?_
          positivity
        rw [h1]
        nlinarith [h2, hc0]
      · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
        positivity
  | succ n ih =>
      rcases Nat.lt_or_ge (n+1) v₀ with hlt | hle
      · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
        positivity
      · rw [Finset.sum_Ico_succ_top (by omega)]
        have hlast : Real.exp (β*((n+1 : ℕ):ℝ)/N)
            = Real.exp (β*((n:ℝ)+1)/N) := by
          push_cast
          ring_nf
        have hnext : β*(((n+1 : ℕ):ℝ)+1)/N = β*((n:ℝ)+1)/N + β/(N:ℝ) := by
          push_cast
          field_simp
        rw [hlast, hnext]
        calc (∑ v ∈ Finset.Ico v₀ (n+1), Real.exp (β*(v:ℝ)/N))
              + Real.exp (β*((n:ℝ)+1)/N)
            ≤ Real.exp (β*((n:ℝ)+1)/N) * ((N:ℝ)/β + 1)
                + Real.exp (β*((n:ℝ)+1)/N) := by linarith [ih]
          _ = Real.exp (β*((n:ℝ)+1)/N) * ((N:ℝ)/β + 2) := by ring
          _ ≤ Real.exp (β*((n:ℝ)+1)/N + β/(N:ℝ)) * ((N:ℝ)/β + 1) :=
                hstep (β*((n:ℝ)+1)/N)


open MeasureTheory in
/-- **The level-sum band energy, from per-level smallness** (Track R,
A2-III, II-5a′): for families `Q v`, `R v` of continuous polynomials and
a measurable `G ⊆ (−T, T]` on which every `‖Q v‖ ≤ s v`,

  `∫_G ‖∑_{v ∈ I} Q v · R v‖² ≤ #I · ∑_{v ∈ I} (s v)²·M v`

whenever `∫_{−T}^{T} ‖R v‖² ≤ M v` for each `v`.

The two steps of `[MR]`'s level-1 band estimate, and nothing else:
Cauchy–Schwarz over the levels — which is what the factor `#I` is, and
it is unavoidable because the `Q v` are not orthogonal on `G` — and then,
per level, the pointwise trade `‖Q v ξ‖²‖R v ξ‖² ≤ (s v)²‖R v ξ‖²`
followed by enlarging `G` to the full window so a mean value theorem can
see `R v`.

Everything schedule-dependent is a parameter.  `s` and `M` are arbitrary
real families, so the caller supplies the `e`-adic smallness
`s v = e^{−αv/N}` and the mean value bound `M v` at the cell scale, and
the two geometric series that then appear are already in tree
(`sum_exp_neg_index_le` for the decaying half, `sum_exp_index_le` for the
growing one).  Note that `0 ≤ s v` is *not* assumed: it is only ever used
squared, and where it is used at all it comes for free from
`‖Q v ξ‖ ≤ s v`. -/
theorem setIntegral_norm_sq_sum_mul_le_of_small (Q R : ℕ → ℝ → ℂ) (I : Finset ℕ)
    (hQ : ∀ v ∈ I, Continuous (Q v)) (hR : ∀ v ∈ I, Continuous (R v))
    (T : ℝ) (hT : 0 < T) (G : Set ℝ) (hGm : MeasurableSet G)
    (hGT : G ⊆ Set.Ioc (-T) T) (s M : ℕ → ℝ)
    (hsmall : ∀ v ∈ I, ∀ ξ ∈ G, ‖Q v ξ‖ ≤ s v)
    (hmom : ∀ v ∈ I, (∫ ξ in (-T)..T, ‖R v ξ‖^2) ≤ M v) :
    (∫ ξ in G, ‖∑ v ∈ I, Q v ξ * R v ξ‖^2)
      ≤ (I.card : ℝ) * ∑ v ∈ I, (s v)^2 * M v := by
  classical
  have hTT : -T ≤ T := by linarith
  have hprodc : ∀ v ∈ I, Continuous fun ξ => ‖Q v ξ * R v ξ‖^2 := fun v hv =>
    (((hQ v hv).mul (hR v hv)).norm.pow 2)
  have hprodi : ∀ v ∈ I, IntegrableOn (fun ξ => ‖Q v ξ * R v ξ‖^2) G := fun v hv =>
    ((hprodc v hv).integrableOn_Ioc (a := -T) (b := T)).mono_set hGT
  have hsumc : Continuous fun ξ => ‖∑ v ∈ I, Q v ξ * R v ξ‖^2 :=
    ((continuous_finset_sum I fun v hv => (hQ v hv).mul (hR v hv)).norm.pow 2)
  have hsumi : IntegrableOn (fun ξ => ‖∑ v ∈ I, Q v ξ * R v ξ‖^2) G :=
    (hsumc.integrableOn_Ioc (a := -T) (b := T)).mono_set hGT
  -- per level: pointwise smallness on `G`, then enlarge `G` to the window
  have hlevel : ∀ v ∈ I, (∫ ξ in G, ‖Q v ξ * R v ξ‖^2) ≤ (s v)^2 * M v := by
    intro v hv
    have hRc : Continuous fun ξ => ‖R v ξ‖^2 := ((hR v hv).norm.pow 2)
    have hRi : IntegrableOn (fun ξ => ‖R v ξ‖^2) (Set.Ioc (-T) T) :=
      hRc.integrableOn_Ioc
    have hRiG : IntegrableOn (fun ξ => ‖R v ξ‖^2) G := hRi.mono_set hGT
    have hpt : ∀ ξ ∈ G, ‖Q v ξ * R v ξ‖^2 ≤ (s v)^2 * ‖R v ξ‖^2 := by
      intro ξ hξ
      have h1 : ‖Q v ξ * R v ξ‖^2 = ‖Q v ξ‖^2 * ‖R v ξ‖^2 := by
        rw [norm_mul, mul_pow]
      have h2 : ‖Q v ξ‖^2 ≤ (s v)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hsmall v hv ξ hξ) 2
      rw [h1]
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    calc (∫ ξ in G, ‖Q v ξ * R v ξ‖^2)
        ≤ ∫ ξ in G, (s v)^2 * ‖R v ξ‖^2 :=
          setIntegral_mono_on (hprodi v hv) (hRiG.const_mul _) hGm hpt
      _ = (s v)^2 * ∫ ξ in G, ‖R v ξ‖^2 := integral_const_mul _ _
      _ ≤ (s v)^2 * ∫ ξ in Set.Ioc (-T) T, ‖R v ξ‖^2 := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          exact setIntegral_mono_set hRi
            (Filter.Eventually.of_forall fun ξ => by positivity) hGT.eventuallyLE
      _ = (s v)^2 * ∫ ξ in (-T)..T, ‖R v ξ‖^2 := by
          rw [intervalIntegral.integral_of_le hTT]
      _ ≤ (s v)^2 * M v := mul_le_mul_of_nonneg_left (hmom v hv) (sq_nonneg _)
  -- Cauchy–Schwarz over the levels, then integrate termwise
  calc (∫ ξ in G, ‖∑ v ∈ I, Q v ξ * R v ξ‖^2)
      ≤ ∫ ξ in G, (I.card : ℝ) * ∑ v ∈ I, ‖Q v ξ * R v ξ‖^2 := by
        refine setIntegral_mono_on hsumi
          ((integrable_finset_sum I fun v hv => hprodi v hv).const_mul _)
          hGm (fun ξ _ => norm_sum_sq_le_card_mul I (fun v => Q v ξ * R v ξ))
    _ = (I.card : ℝ) * ∑ v ∈ I, ∫ ξ in G, ‖Q v ξ * R v ξ‖^2 := by
        rw [integral_const_mul, integral_finset_sum I (fun v hv => hprodi v hv)]
    _ ≤ (I.card : ℝ) * ∑ v ∈ I, (s v)^2 * M v := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum hlevel) ?_
        positivity


open Finset in
/-- **The level total** (Track R, A2-III, II-5b-1): the two geometric
series of the `[MR]` level-1 estimate, summed —

  `∑_{v=v₀}^{v₁} (e^{−αv/N})²·e^π(T e^{v/N}/A + K)·C
     ≤ e^π·C·[ (T/A)e^{(1−2α)(v₁+1)/N}(N/(1−2α)+1)
                + K e^{−2αv₀/N}(N/(2α)+1) ]`.

The summand is exactly what `setIntegral_norm_sq_sum_mul_le_of_small`
leaves behind once the caller supplies the `e`-adic smallness
`s v = e^{−αv/N}` and the mean value bound at the cell scale
`A e^{−v/N}`, which charges `T e^{v/N}/A`.  The mean value theorem's
additive ratio term `K` and its coefficient mass `C` are left free
rather than fixed at the dyadic `2`: the level-1 block lives at the
*quotient* scale, and `ℕ`-division does not preserve block ratios, so
the caller pays a ratio it does not get to choose.  The point is that
the two
factors pull in opposite directions: smallness decays at rate `2α`, the
mean value error grows at rate `1`, so the product runs at exponent
`1 − 2α` and the sum only converges because `2α < 1`.  That is the one
place the `[MR]` schedule's constraint on `α` is actually used, and it
is why the hypothesis is `2α < 1` rather than `α < 1`.

Both halves are already in tree — `sum_exp_index_le` for the growing
`1 − 2α` half, `sum_exp_neg_index_le` for the decaying `2α` half — so
this unit is only the algebra that separates them: `(e^{−αv/N})² =
e^{−2αv/N}` and `e^{−2αv/N}e^{v/N} = e^{(1−2α)v/N}`. -/
theorem sum_level_energy_le (α : ℝ) (hα : 0 < α) (hα2 : 2*α < 1)
    (N : ℕ) (hN : 0 < N) (v₀ v₁ : ℕ) (A T K C : ℝ) (hA : 0 < A)
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hC : 0 ≤ C) :
    ∑ v ∈ Finset.Ico v₀ (v₁+1),
        (Real.exp (-(α*(v:ℝ)/N)))^2
          * (Real.exp Real.pi * (T*Real.exp ((v:ℝ)/N)/A + K) * C)
      ≤ Real.exp Real.pi * C
          * ( (T/A) * Real.exp ((1-2*α)*((v₁:ℝ)+1)/N) * ((N:ℝ)/(1-2*α) + 1)
            + K * Real.exp (-(2*α*(v₀:ℝ)/N)) * ((N:ℝ)/(2*α) + 1) ) := by
  classical
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hβ : (0:ℝ) < 1 - 2*α := by linarith
  have hcnn : (0:ℝ) ≤ Real.exp Real.pi * C := by positivity
  -- rewrite each term into the two pure exponentials
  have hterm : ∀ v : ℕ,
      (Real.exp (-(α*(v:ℝ)/N)))^2
          * (Real.exp Real.pi * (T*Real.exp ((v:ℝ)/N)/A + K) * C)
        = Real.exp Real.pi * C
            * ((T/A) * Real.exp ((1-2*α)*(v:ℝ)/N)
                + K * Real.exp (-(2*α*(v:ℝ)/N))) := by
    intro v
    have h1 : (Real.exp (-(α*(v:ℝ)/N)))^2 = Real.exp (-(2*α*(v:ℝ)/N)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have h2 : Real.exp (-(2*α*(v:ℝ)/N)) * Real.exp ((v:ℝ)/N)
        = Real.exp ((1-2*α)*(v:ℝ)/N) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    rw [h1]
    calc Real.exp (-(2*α*(v:ℝ)/N))
          * (Real.exp Real.pi * (T*Real.exp ((v:ℝ)/N)/A + K) * C)
        = Real.exp Real.pi * C
            * ((T/A) * (Real.exp (-(2*α*(v:ℝ)/N)) * Real.exp ((v:ℝ)/N))
                + K * Real.exp (-(2*α*(v:ℝ)/N))) := by
          field_simp
      _ = Real.exp Real.pi * C
            * ((T/A) * Real.exp ((1-2*α)*(v:ℝ)/N)
                + K * Real.exp (-(2*α*(v:ℝ)/N))) := by rw [h2]
  rw [Finset.sum_congr rfl (fun v _ => hterm v), ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hcnn
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hgrow : ∑ v ∈ Finset.Ico v₀ (v₁+1), Real.exp ((1-2*α)*(v:ℝ)/N)
      ≤ Real.exp ((1-2*α)*((v₁:ℝ)+1)/N) * ((N:ℝ)/(1-2*α) + 1) :=
    sum_exp_index_le (1-2*α) hβ N hN v₀ v₁
  have hdecay : ∑ v ∈ Finset.Ico v₀ (v₁+1), Real.exp (-(2*α*(v:ℝ)/N))
      ≤ Real.exp (-(2*α*(v₀:ℝ)/N)) * ((N:ℝ)/(2*α) + 1) :=
    sum_exp_neg_index_le (2*α) (by linarith) N hN v₀ v₁
  have h1 : (T/A) * ∑ v ∈ Finset.Ico v₀ (v₁+1), Real.exp ((1-2*α)*(v:ℝ)/N)
      ≤ (T/A) * (Real.exp ((1-2*α)*((v₁:ℝ)+1)/N) * ((N:ℝ)/(1-2*α) + 1)) :=
    mul_le_mul_of_nonneg_left hgrow (by positivity)
  have h2 : K * ∑ v ∈ Finset.Ico v₀ (v₁+1), Real.exp (-(2*α*(v:ℝ)/N))
      ≤ K * (Real.exp (-(2*α*(v₀:ℝ)/N)) * ((N:ℝ)/(2*α) + 1)) :=
    mul_le_mul_of_nonneg_left hdecay hK
  linarith


/-- **The block ratio survives `ℕ`-division** (Track R, A2-III, II-5b-2):
for `1 ≤ q ≤ A` and a block `(A, B]` of ratio `B ≤ R·A`,

  `(A/q, B/q] ⊆ (A/q, 2R·(A/q)]`.

`[MR]`'s decomposition replaces each prime's own fibre window by the
reference window at the *quotient* scale `A/q`, and the mean value
theorem then has to be applied there.  The sharp mean value theorem
charges `T/A' + 2R'` on a range `(A', R'A']`, so what it needs is the
ratio of the divided block — and ratios are *not* preserved by
`ℕ`-division: `A = 3`, `B = 6`, `R = 2`, `q = 2` already gives
`B/q = 3 > 2 = R·(A/q)`.

Doubling the ratio absorbs the loss exactly.  The floor costs less than
one unit of `A/q`, and `1 ≤ A/q` — which is where `q ≤ A` is used —
makes that unit cheaper than the ratio already being paid: `B/q ≤ RA/q
< R(A/q + 1) ≤ 2R·(A/q)`.  Since the mean value theorem's dependence on
the ratio is linear and every downstream constant is absolute, paying
`2R` instead of `R` is free. -/
theorem Ioc_div_subset_Ioc_two_mul_ratio (A B R q : ℕ) (hq : 1 ≤ q)
    (hqA : q ≤ A) (hR : 1 ≤ R) (hB : B ≤ R * A) :
    Finset.Ioc (A/q) (B/q) ⊆ Finset.Ioc (A/q) (2*R*(A/q)) := by
  intro n hn
  rw [Finset.mem_Ioc] at hn ⊢
  refine ⟨hn.1, hn.2.trans ((Nat.div_le_div_right hB).trans ?_)⟩
  have hq0 : 0 < q := hq
  have ha : 1 ≤ A/q := (Nat.one_le_div_iff hq0).mpr hqA
  have hmod : A % q < q := Nat.mod_lt _ hq0
  have key : R*A < (2*R*(A/q) + 1) * q := by
    have e1 : R*A = R*q*(A/q) + R*(A%q) := by
      conv_lhs => rw [← Nat.div_add_mod A q]
      ring
    have e2 : R*(A%q) < R*q := by
      have := Nat.mul_lt_mul_of_lt_of_le hmod (le_refl R) (by omega : 0 < R)
      calc R*(A%q) = (A%q)*R := by ring
        _ < q*R := this
        _ = R*q := by ring
    have e3 : R*q ≤ R*q*(A/q) := Nat.le_mul_of_pos_right _ ha
    nlinarith [e1, e2, e3]
  exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hq0).mpr key)


open MeasureTheory Finset ExpSums in
/-- **The level-1 band energy at the cell/block shapes** (Track R,
A2-III, II-5b-3): `setIntegral_norm_sq_sum_mul_le_of_small` instantiated
at exactly the two polynomials `[MR]`'s decomposition lemma leaves
behind.  For a measurable `G ⊆ (−T, T]` on which the level-`v` *cell*
polynomial is `s v`-small,

  `∫_G ‖∑_v (∑_{p∈𝒞_v} (g p/p)e(−ξ log p))·(∑_{A/q_v < m ≤ B/q_v} (c m/m)e(−ξ log m))‖²
     ≤ #I·∑_v (s v)²·e^π(T/(A/q_v) + 4R)·∑_{A/q_v < m ≤ B/q_v} ‖c m‖²/m`.

**What supplies each factor.**  The cell polynomial is small on `G` by
hypothesis — that is the *definition* of `[MR]`'s level set `𝒯_v`, and
nothing about cells is used to prove it here.  The block polynomial is
priced by the sharp mean value theorem at the quotient scale `A/q_v`,
which is legitimate because `Ioc (A/q_v) (B/q_v)` has ratio at most
`2R` by `Ioc_div_subset_Ioc_two_mul_ratio` — the only genuinely new
content, since `ℕ`-division does not preserve ratios.

**Why `q` is an arbitrary family.**  In the application `q v` is the
least member of `eadicCell P (2N) v`, which is what makes the reference
window uniform across the cell (II-2e,
`intervalIntegral_norm_sq_cell_replace_le`).  But minimality plays no
part in *this* estimate: all that is needed is `1 ≤ q v ≤ A`, so it is
left free and the caller supplies whichever representative the
decomposition produced.

**Why `s` stays free.**  The `e`-adic schedule `s v = e^{−αv/N}` is not
imposed here; feeding it in and summing the resulting two geometric
series is `sum_level_energy_le` (II-5b-1), a separate and purely
real-analytic step.  Keeping them apart means the schedule's constraint
`2α < 1` never has to be carried through the measure theory. -/
theorem setIntegral_norm_sq_cell_block_sum_le
    (P : Finset ℕ) (N v₀ v₁ : ℕ) (q : ℕ → ℕ)
    (A B R : ℕ) (hR : 1 ≤ R) (hB : B ≤ R * A)
    (hq1 : ∀ v, 1 ≤ q v) (hqA : ∀ v, q v ≤ A)
    (g c : ℕ → ℂ) (T : ℝ) (hT : 0 < T)
    (G : Set ℝ) (hGm : MeasurableSet G) (hGT : G ⊆ Set.Ioc (-T) T)
    (s : ℕ → ℝ)
    (hsmall : ∀ v ∈ Finset.Ico v₀ (v₁+1), ∀ ξ ∈ G,
      ‖∑ p ∈ eadicCell P (2*N) v, (g p/(p:ℂ))
          * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖ ≤ s v) :
    (∫ ξ in G, ‖∑ v ∈ Finset.Ico v₀ (v₁+1),
        (∑ p ∈ eadicCell P (2*N) v, (g p/(p:ℂ))
            * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))
          * (∑ m ∈ Finset.Ioc (A/(q v)) (B/(q v)), (c m/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))‖^2)
      ≤ ((Finset.Ico v₀ (v₁+1)).card : ℝ)
          * ∑ v ∈ Finset.Ico v₀ (v₁+1), (s v)^2
              * (Real.exp Real.pi * (T/((A/(q v) : ℕ):ℝ) + 4*(R:ℝ))
                  * ∑ m ∈ Finset.Ioc (A/(q v)) (B/(q v)), ‖c m‖^2/(m:ℝ)) := by
  classical
  have hchar : ∀ w : ℝ, Continuous fun ξ : ℝ =>
      ((Real.fourierChar (-(w * ξ)) : Circle) : ℂ) := fun w =>
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  refine setIntegral_norm_sq_sum_mul_le_of_small
    (fun v ξ => ∑ p ∈ eadicCell P (2*N) v, (g p/(p:ℂ))
        * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))
    (fun v ξ => ∑ m ∈ Finset.Ioc (A/(q v)) (B/(q v)), (c m/(m:ℂ))
        * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
    (Finset.Ico v₀ (v₁+1))
    (fun v _ => continuous_finset_sum _ fun p _ =>
      continuous_const.mul (hchar (Real.log p)))
    (fun v _ => continuous_finset_sum _ fun m _ =>
      continuous_const.mul (hchar (Real.log m)))
    T hT G hGm hGT s _ hsmall ?_
  intro v _
  have hq0 : 0 < q v := hq1 v
  have ha : 1 ≤ A/(q v) := (Nat.one_le_div_iff hq0).mpr (hqA v)
  have hsub : Finset.Ioc (A/(q v)) (B/(q v))
      ⊆ Finset.Ioc (A/(q v)) ((2*R)*(A/(q v))) :=
    Ioc_div_subset_Ioc_two_mul_ratio A B R (q v) hq0 (hqA v) hR hB
  refine (intervalIntegral_norm_sq_poly_le_sharp_ratio (A/(q v)) (2*R) ha
    (by omega) _ hsub c T hT).trans ?_
  have hcast : ((2*R : ℕ):ℝ) = 2*(R:ℝ) := by push_cast; ring
  rw [hcast]
  refine le_of_eq ?_
  ring

open Finset in
/-- **The quotient scale is the cell scale** (Track R, A2-III, II-5b-3):
for `q` in the `e`-adic cell of index `v` at resolution `2N`, with
`2q ≤ A`,

  `T/⌊A/q⌋ ≤ 2T·e^{(v+1)/(2N)}/A`.

The sharp mean value theorem charges `T/A′` at the scale `A′` it is
applied at, and `[MR]`'s decomposition applies it at the *quotient*
scale `A′ = ⌊A/q⌋`.  What the level sum needs is that charge expressed
in `v`, so that it can be matched against the `e`-adic smallness
`e^{−αv/N}` and the pair summed as a geometric series
(`sum_level_energy_le`).  This is that conversion, and it is where the
two halves of the level estimate are finally put on the same scale.

Two separate losses, both absorbed into the factor `2`.  The floor costs
a factor `2` — `⌊A/q⌋ > A/q − 1 ≥ A/(2q)` exactly when `2q ≤ A`, which
is the hypothesis — and the cell costs `e^{1/(2N)}`, since a cell pins
`q` only to within one step of the ladder.  The second is kept as the
explicit `e^{(v+1)/(2N)}` rather than folded into a constant, because
the consumer sums over `v` and needs the exponent, not its bound.

Only the *upper* half of `eadicCell_bounds` is used: a lower bound on
`q` would bound `T/⌊A/q⌋` from below, which no consumer wants. -/
theorem quotient_scale_le_cell_scale {P : Finset ℕ} {N v : ℕ} (hN : 0 < N)
    {q : ℕ} (hq : q ∈ eadicCell P (2*N) v) (hq1 : 1 ≤ q)
    (A : ℕ) (hqA : 2*q ≤ A) (T : ℝ) (hT : 0 ≤ T) :
    T/((A/q : ℕ):ℝ) ≤ 2*T*Real.exp (((v:ℝ)+1)/(2*(N:ℝ)))/(A:ℝ) := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq1
  have hA1 : 2 ≤ A := le_trans (by omega) hqA
  have hA0 : (0:ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  -- the floor loses at most a factor `2`
  have hmod : ((A % q : ℕ):ℝ) < (q:ℝ) := by
    exact_mod_cast Nat.mod_lt _ (by omega : 0 < q)
  have hdm : (q:ℝ) * ((A/q : ℕ):ℝ) + ((A % q : ℕ):ℝ) = (A:ℝ) := by
    exact_mod_cast Nat.div_add_mod A q
  have hqhalf : 2*(q:ℝ) ≤ (A:ℝ) := by exact_mod_cast hqA
  have hfloor : (A:ℝ)/(2*(q:ℝ)) ≤ ((A/q : ℕ):ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hdm, hmod, hqhalf]
  have hfl0 : (0:ℝ) < ((A/q : ℕ):ℝ) :=
    lt_of_lt_of_le (by positivity) hfloor
  -- the cell pins `q` to within one step of the ladder
  have hcell : (q:ℝ) < Real.exp (((v:ℝ)+1)/((2*N : ℕ):ℝ)) :=
    (eadicCell_bounds (by omega : 0 < 2*N) hq hq1).2
  have hcell' : (q:ℝ) ≤ Real.exp (((v:ℝ)+1)/(2*(N:ℝ))) := by
    refine le_of_lt (lt_of_lt_of_le hcell (le_of_eq ?_))
    congr 1
    push_cast
    ring
  calc T/((A/q : ℕ):ℝ) ≤ T/((A:ℝ)/(2*(q:ℝ))) := by
        gcongr
    _ = 2*T*(q:ℝ)/(A:ℝ) := by field_simp
    _ ≤ 2*T*Real.exp (((v:ℝ)+1)/(2*(N:ℝ)))/(A:ℝ) := by
        gcongr

open MeasureTheory Finset ExpSums in
/-- **`E₁`, the level-1 band energy in closed form** (Track R, A2-III,
II-5b): the whole level-1 leg of `[MR]`'s inner-band estimate, with
every scale eliminated.  On a measurable `G ⊆ (−T, T]` where the
level-`v` cell polynomial obeys the `e`-adic smallness
`e^{−αv/(2N)}`,

  `∫_G ‖∑_v (∑_{p∈𝒞_v} (g p/p)e(−ξ log p))·(∑_{A/q_v<m≤B/q_v} (c m/m)e(−ξ log m))‖²`
  `  ≤ #I·e^π·C·[ (2Te^{1/(2N)}/A)·e^{(1−2α)(v₁+1)/(2N)}·(2N/(1−2α)+1)`
  `               + 4R·e^{−2αv₀/(2N)}·(2N/(2α)+1) ]`.

Three units, composed, and no scale survives:
`setIntegral_norm_sq_cell_block_sum_le` turns the band integral into a
sum over levels of (smallness)²×(mean value at the quotient scale);
`quotient_scale_le_cell_scale` rewrites that quotient scale `⌊A/q_v⌋` as
the cell scale `e^{(v+1)/(2N)}`; and `sum_level_energy_le` sums the
resulting geometric series.

**Where each constant comes from.**  The `4R` is the doubled block
ratio of `Ioc_div_subset_Ioc_two_mul_ratio` — `ℕ`-division does not
preserve ratios — and the `2e^{1/(2N)}` is the doubled scale of
`quotient_scale_le_cell_scale` times the one ladder step a cell fails to
pin down.  Both are the same `ℕ`-division friction in its two guises,
and both are absolutely bounded, so neither enters the schedule.

**`2α < 1` is the only schedule constraint used.**  Smallness decays at
rate `2α` and the mean value error grows at rate `1`, so the product
runs at exponent `1 − 2α` and the level sum converges precisely when
`2α < 1`.  Everything else — `α`, `N`, `R`, the level range, the
coefficient mass `C` — is free.

The factor `#I` is Cauchy–Schwarz over the levels and is not removable:
the cell polynomials are not orthogonal on `G`. -/
theorem band_energy_level_one_le
    (P : Finset ℕ) (N : ℕ) (hN : 0 < N) (v₀ v₁ : ℕ) (q : ℕ → ℕ)
    (A B R : ℕ) (hR : 1 ≤ R) (hB : B ≤ R * A)
    (hq1 : ∀ v, 1 ≤ q v) (hqA : ∀ v, 2 * q v ≤ A)
    (hqcell : ∀ v ∈ Finset.Ico v₀ (v₁+1), q v ∈ eadicCell P (2*N) v)
    (g c : ℕ → ℂ) (T : ℝ) (hT : 0 < T)
    (G : Set ℝ) (hGm : MeasurableSet G) (hGT : G ⊆ Set.Ioc (-T) T)
    (α : ℝ) (hα : 0 < α) (hα2 : 2*α < 1) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ v ∈ Finset.Ico v₀ (v₁+1),
      ∑ m ∈ Finset.Ioc (A/(q v)) (B/(q v)), ‖c m‖^2/(m:ℝ) ≤ C)
    (hsmall : ∀ v ∈ Finset.Ico v₀ (v₁+1), ∀ ξ ∈ G,
      ‖∑ p ∈ eadicCell P (2*N) v, (g p/(p:ℂ))
          * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖
        ≤ Real.exp (-(α*(v:ℝ)/((2*N : ℕ):ℝ)))) :
    (∫ ξ in G, ‖∑ v ∈ Finset.Ico v₀ (v₁+1),
        (∑ p ∈ eadicCell P (2*N) v, (g p/(p:ℂ))
            * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))
          * (∑ m ∈ Finset.Ioc (A/(q v)) (B/(q v)), (c m/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))‖^2)
      ≤ ((Finset.Ico v₀ (v₁+1)).card : ℝ)
          * (Real.exp Real.pi * C
              * ( (2*T*Real.exp (1/((2*N : ℕ):ℝ))/(A:ℝ))
                    * Real.exp ((1-2*α)*((v₁:ℝ)+1)/((2*N : ℕ):ℝ))
                    * (((2*N : ℕ):ℝ)/(1-2*α) + 1)
                + 4*(R:ℝ) * Real.exp (-(2*α*(v₀:ℝ)/((2*N : ℕ):ℝ)))
                    * (((2*N : ℕ):ℝ)/(2*α) + 1) )) := by
  classical
  have hA2 : 2 ≤ A := le_trans (by have := hq1 v₀; omega) (hqA v₀)
  have hA0 : (0:ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hN2 : 0 < 2*N := by omega
  have hcast : ((2*N : ℕ):ℝ) = 2*(N:ℝ) := by push_cast; ring
  refine le_trans (setIntegral_norm_sq_cell_block_sum_le P N v₀ v₁ q A B R hR hB
    hq1 (fun v => le_trans (by omega) (hqA v)) g c T hT G hGm hGT _ hsmall) ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine le_trans (Finset.sum_le_sum ?_)
    (sum_level_energy_le α hα hα2 (2*N) hN2 v₀ v₁ (A:ℝ)
      (2*T*Real.exp (1/((2*N : ℕ):ℝ))) (4*(R:ℝ)) C hA0
      (by positivity) (by positivity) hC0)
  intro v hv
  have hCv0 : (0:ℝ) ≤ ∑ m ∈ Finset.Ioc (A/(q v)) (B/(q v)), ‖c m‖^2/(m:ℝ) :=
    Finset.sum_nonneg fun m _ => by positivity
  -- the quotient scale is the cell scale, then split off the ladder step
  have hscale : T/((A/(q v) : ℕ):ℝ)
      ≤ (2*T*Real.exp (1/((2*N : ℕ):ℝ)))
          * Real.exp ((v:ℝ)/((2*N : ℕ):ℝ))/(A:ℝ) := by
    refine le_trans (quotient_scale_le_cell_scale hN (hqcell v hv) (hq1 v) A
      (hqA v) T hT.le) (le_of_eq ?_)
    rw [hcast]
    have hsplit : Real.exp (((v:ℝ)+1)/(2*(N:ℝ)))
        = Real.exp (1/(2*(N:ℝ))) * Real.exp ((v:ℝ)/(2*(N:ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [div_eq_div_iff (by positivity) (by positivity), hsplit]
    ring
  gcongr
  exact hC v hv

/-- **The Dirichlet kernel's derivative in the scale variable** (Track R,
A2-III, IV-0a): for `t > 0`,

  `d/dt [ t^{-1}e(−ξ log t) ] = −t^{-2}(1 + 2πiξ)·e(−ξ log t)`,

hence `‖·‖ ≤ (1 + 2π|ξ|)/t²`.

**Why the scale variable.**  `V-2` differentiates a Dirichlet polynomial
in the *frequency* `ξ`, which is what the large-values leg needs.  This
is the other derivative: `[MR]`'s short-sum Halász step (IV-0) reduces
`∑_{A<m≤A+Δ} (c m/m)e(−ξ log m)` to initial-segment sums by Abel
summation, and Abel summation integrates against `d/dt` of the *kernel*.
Mathlib's `sum_mul_eq_sub_integral_mul₀` supplies the summation; this
supplies the `hf_diff` and the bound on `deriv f` that it needs.

**The shape of the answer is the whole point.**  The `1` comes from
differentiating `t^{-1}` and the `2πiξ` from the phase, and they appear
*added*, not multiplied — so the total variation of the kernel over
`(A, A+Δ]` is `(1 + 2π|ξ|)(1/A − 1/(A+Δ)) ≤ (1 + 2π|ξ|)/A`.  That is why
the short-sum reduction costs a factor `(1 + |ξ|)` and no more, and
therefore why it is usable up to `|ξ| ≍ T` with only a polynomial loss.

Stated at `1/(u:ℂ)` rather than `(u:ℂ)⁻¹` so that it matches the
Dirichlet-polynomial normal form `c n/n` used throughout the tree. -/
theorem hasDerivAt_dirichlet_kernel (ξ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => (1/(u:ℂ))
        * Complex.exp (((-(2*Real.pi*ξ*Real.log u) : ℝ) : ℂ) * Complex.I))
      (-(1/(t:ℂ)^2) * (1 + 2*(Real.pi:ℂ)*(ξ:ℂ)*Complex.I)
        * Complex.exp (((-(2*Real.pi*ξ*Real.log t) : ℝ) : ℂ) * Complex.I)) t := by
  have ht0 : (t:ℂ) ≠ 0 := by
    simpa using (Complex.ofReal_ne_zero.mpr ht.ne')
  -- the reciprocal
  have hre : HasDerivAt (fun u : ℝ => (u:ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have hinvR : HasDerivAt (fun u : ℝ => u⁻¹) (-(t^2)⁻¹) t := hasDerivAt_inv ht.ne'
  have hinvC : HasDerivAt (fun u : ℝ => ((u⁻¹ : ℝ) : ℂ)) (((-(t^2)⁻¹ : ℝ) : ℂ)) t :=
    hinvR.ofReal_comp
  have hinv : HasDerivAt (fun u : ℝ => 1/(u:ℂ)) (-(1/(t:ℂ)^2)) t := by
    have hfun : (fun u : ℝ => 1/(u:ℂ)) = (fun u : ℝ => ((u⁻¹ : ℝ) : ℂ)) := by
      funext u
      simp [one_div]
    rw [hfun]
    convert hinvC using 1
    push_cast
    field_simp
  -- the phase
  have hlog : HasDerivAt (fun u : ℝ => Real.log u) (1/t) t := by
    simpa [one_div] using Real.hasDerivAt_log ht.ne'
  have hph : HasDerivAt
      (fun u : ℝ => ((-(2*Real.pi*ξ*Real.log u) : ℝ) : ℂ))
      ((-(2*Real.pi*ξ*(1/t)) : ℝ) : ℂ) t := by
    have := ((hlog.const_mul (2*Real.pi*ξ)).neg).ofReal_comp
    simpa using this
  have hphI : HasDerivAt
      (fun u : ℝ => ((-(2*Real.pi*ξ*Real.log u) : ℝ) : ℂ) * Complex.I)
      (((-(2*Real.pi*ξ*(1/t)) : ℝ) : ℂ) * Complex.I) t := hph.mul_const _
  have hexp := hphI.cexp
  -- product rule
  have hprod := hinv.mul hexp
  refine hprod.congr_deriv ?_
  have hc : ((-(2*Real.pi*ξ*(1/t)) : ℝ) : ℂ) = -(2*(Real.pi:ℂ)*(ξ:ℂ)*(1/(t:ℂ))) := by
    push_cast
    ring
  rw [hc]
  field_simp
  ring


/-- **The Dirichlet kernel's total variation weight** (Track R, A2-III,
IV-0a′): the derivative of `t ↦ t^{-1}e(−ξ log t)` obeys

  `‖f′(t)‖ ≤ (1 + 2π|ξ|)/t²`.

The `1` is the reciprocal's contribution and the `2π|ξ|` the phase's,
and they are **added**: integrating over `(A, A+Δ]` gives a total
variation `(1 + 2π|ξ|)(1/A − 1/(A+Δ)) ≤ (1 + 2π|ξ|)/A`.  That linear —
not exponential — dependence on `ξ` is what makes `[MR]`'s short-sum
reduction usable across the whole band `|ξ| ≤ T`, at a cost of one
factor of `T` rather than a factor the schedule could not absorb.

Paired with `hasDerivAt_dirichlet_kernel` this supplies both hypotheses
of Mathlib's `sum_mul_eq_sub_integral_mul₀` — differentiability on
`[1, b]` and a dominating function for `deriv f`. -/
theorem norm_deriv_dirichlet_kernel_le (ξ : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖-(1/(t:ℂ)^2) * (1 + 2*(Real.pi:ℂ)*(ξ:ℂ)*Complex.I)
        * Complex.exp (((-(2*Real.pi*ξ*Real.log t) : ℝ) : ℂ) * Complex.I)‖
      ≤ (1 + 2*Real.pi*|ξ|)/t^2 := by
  have ht0 : (t:ℂ) ≠ 0 := by
    simpa using (Complex.ofReal_ne_zero.mpr ht.ne')
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have h1 : ‖-(1/(t:ℂ)^2)‖ = 1/t^2 := by
    rw [norm_neg, norm_div, norm_one, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht]
  have h2 : ‖(1 : ℂ) + 2*(Real.pi:ℂ)*(ξ:ℂ)*Complex.I‖ ≤ 1 + 2*Real.pi*|ξ| := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_one]
    have : ‖2*(Real.pi:ℂ)*(ξ:ℂ)*Complex.I‖ = 2*Real.pi*|ξ| := by
      rw [norm_mul, Complex.norm_I, mul_one, norm_mul, norm_mul,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      norm_num
    linarith [this.le, this.ge]
  rw [h1]
  calc 1/t^2 * ‖(1 : ℂ) + 2*(Real.pi:ℂ)*(ξ:ℂ)*Complex.I‖
      ≤ 1/t^2 * (1 + 2*Real.pi*|ξ|) := by
        refine mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (1 + 2*Real.pi*|ξ|)/t^2 := by ring


end ExpSums

end MoltResearch
