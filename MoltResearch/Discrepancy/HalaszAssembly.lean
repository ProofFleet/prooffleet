/-
# Discrepancy: the cheap Halász assembly

The composition layer of the Track R cheap-Halász build (Tao 2015,
Part E): the two class band-energy instances feeding the band/tail
Hölder split, and the pairing theorem `cheap_halasz_pairing` — the
Cesàro mean of a 1-bounded completely multiplicative function under a
band-uniform pretentious-distance floor, bounded by the three-scale
error counts, the Perron edge, the band term, and the window tail,
with every constant explicit and all parameters free for tuning.

The chain: `norm_cesaro_sub_main_le` (the three-scale split) →
`perron_sandwich` (the window sandwich, applied to the main-term
indicator) → `sum_main_eq_sum_box` (the box bridge) →
`norm_sum_translates_le_integral_char` (the Plancherel pairing at the
triple index) → `sum_triple_char_eq_mul` (the box factorization) →
`pairing_band_tail_split` (the band/tail Hölder split) with the
`Bband`-instance `norm_smooth_poly_band_le`, the class band energies
below, the trivial harmonic sups, `MV ≤ 1`, and `fourier_tail_le`.
-/
import MoltResearch.Discrepancy.ThreeScale
import MoltResearch.Discrepancy.PerronWindow
import MoltResearch.Discrepancy.PlancherelHarness
import MoltResearch.Discrepancy.HalaszEuler
import MoltResearch.Discrepancy.ParsevalBridge

namespace MoltResearch

open Finset ExpSums MeasureTheory Real
open scoped FourierTransform ContDiff

set_option maxHeartbeats 1600000 in
/-- **The medium-class band energy** (Track R, M2-i4c1b): the
`1/n`-weighted phase polynomial over the medium class — numbers up to
`x` that are `y₁`-smooth and free of primes below `y₂` — has band
`L²`-mass at most `1024·e¹²·log y₁/log y₂` plus the sieve remainder.
The `E₂`-instance of the band/tail Hölder split. -/
theorem medium_class_band_energy_le (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1)
    (y₂ y₁ x : ℕ) (hy₂ : 2 ≤ y₂) (h12 : y₂ ≤ y₁) (hy₁ : 4 ≤ y₁)
    (L : ℝ) (hL : 1 ≤ L) :
    ∫ ξ in (-L)..L,
        ‖∑ n ∈ (Finset.Icc 1 x).filter (fun b => b ≠ 1
            ∧ b ∈ Nat.smoothNumbers y₁
            ∧ Nat.Coprime b (primorial (y₂-1))),
          (f n/(n:ℂ))
            * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2
      ≤ 1024*(Real.exp 12 * Real.log y₁)/Real.log y₂
        + 512*L*(12/Real.log y₂ + 2*(((y₂:ℝ)-1)^4)^2) := by
  classical
  set S := (Finset.Icc 1 x).filter (fun b => b ≠ 1
    ∧ b ∈ Nat.smoothNumbers y₁
    ∧ Nat.Coprime b (primorial (y₂-1))) with hS_def
  have hz : 1 ≤ y₂ - 1 := by omega
  have hrough : ∀ n ∈ S, Nat.Coprime n (primorial (y₂-1)) := by
    intro n hn
    rw [hS_def, Finset.mem_filter] at hn
    exact hn.2.2.2
  have hS2 : ∀ n ∈ S, 2 ≤ n := by
    intro n hn
    rw [hS_def, Finset.mem_filter, Finset.mem_Icc] at hn
    have h1 := hn.1.1
    have h2 := hn.2.1
    omega
  have hw : ∀ n ∈ S, ‖f n/(n:ℂ)‖ ≤ 1/(n:ℝ) := by
    intro n hn
    have hn2 := hS2 n hn
    rw [norm_div, Complex.norm_natCast]
    gcongr
    exact hb n
  have hsub : S ⊆ Nat.smoothNumbersUpTo x y₁ := by
    intro n hn
    rw [hS_def, Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Nat.mem_smoothNumbersUpTo]
    exact ⟨hn.1.2, hn.2.2.1⟩
  have hH : ∑ n ∈ S, (1:ℝ)/n ≤ Real.exp 12 * Real.log y₁ := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_)
      (sum_smooth_one_div_le y₁ x hy₁)
    intro n _ _
    positivity
  have hmain := ExpSums.class_band_energy_le S (y₂-1) hz hrough hS2
    (fun n => f n/(n:ℂ)) hw L hL (Real.exp 12 * Real.log y₁) hH
  refine le_trans hmain (le_of_eq ?_)
  rw [show ((y₂-1 : ℕ):ℝ) = (y₂:ℝ)-1 from by
    push_cast [Nat.cast_sub (by omega : 1 ≤ y₂)]
    ring]
  rw [show (y₂:ℝ)-1+1 = (y₂:ℝ) from by ring]

set_option maxHeartbeats 1600000 in
/-- **The large-class band energy** (Track R, M2-i4c1c): the
`1/n`-weighted phase polynomial over the large class — numbers up to
`x` free of primes below `y₁` — has band `L²`-mass at most
`1024·(log x + 1)/log y₁` plus the sieve remainder. The
`E₃`-instance of the band/tail Hölder split. -/
theorem large_class_band_energy_le (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1)
    (y₁ x : ℕ) (hy₁ : 2 ≤ y₁) (hx : 1 ≤ x)
    (L : ℝ) (hL : 1 ≤ L) :
    ∫ ξ in (-L)..L,
        ‖∑ n ∈ (Finset.Icc 1 x).filter (fun c => c ≠ 1
            ∧ Nat.Coprime c (primorial (y₁-1))),
          (f n/(n:ℂ))
            * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2
      ≤ 1024*(Real.log x + 1)/Real.log y₁
        + 512*L*(12/Real.log y₁ + 2*(((y₁:ℝ)-1)^4)^2) := by
  classical
  set S := (Finset.Icc 1 x).filter (fun c => c ≠ 1
    ∧ Nat.Coprime c (primorial (y₁-1))) with hS_def
  have hz : 1 ≤ y₁ - 1 := by omega
  have hrough : ∀ n ∈ S, Nat.Coprime n (primorial (y₁-1)) := by
    intro n hn
    rw [hS_def, Finset.mem_filter] at hn
    exact hn.2.2
  have hS2 : ∀ n ∈ S, 2 ≤ n := by
    intro n hn
    rw [hS_def, Finset.mem_filter, Finset.mem_Icc] at hn
    have h1 := hn.1.1
    have h2 := hn.2.1
    omega
  have hw : ∀ n ∈ S, ‖f n/(n:ℂ)‖ ≤ 1/(n:ℝ) := by
    intro n hn
    have hn2 := hS2 n hn
    rw [norm_div, Complex.norm_natCast]
    gcongr
    exact hb n
  have hH : ∑ n ∈ S, (1:ℝ)/n ≤ Real.log x + 1 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) ?_) (sum_one_div_Icc_le_log x hx)
    intro n _ _
    positivity
  have hmain := ExpSums.class_band_energy_le S (y₁-1) hz hrough hS2
    (fun n => f n/(n:ℂ)) hw L hL (Real.log x + 1) hH
  refine le_trans hmain (le_of_eq ?_)
  rw [show ((y₁-1 : ℕ):ℝ) = (y₁:ℝ)-1 from by
    push_cast [Nat.cast_sub (by omega : 1 ≤ y₁)]
    ring]
  rw [show (y₁:ℝ)-1+1 = (y₁:ℝ) from by ring]

set_option maxHeartbeats 3200000 in
/-- **The cheap Halász pairing bound** (Track R, M2-i4c1d): for a
`1`-bounded completely multiplicative `f` whose pretentious distance
to every twist `n^{2πiξ}`, `|ξ| ≤ L`, is at least `M` at scale `x`,
the Cesàro mean is controlled by the three-scale error counts, the
Perron edge, the band term — the 1-line Euler bound times the two
class band energies met by parametrized AM-GM — and the Fourier tail
of the Perron window. Every constant is explicit; the parameters
`y₂ ≤ y₁`, `ρ`, `L`, `t`, `δ` are free for tuning. -/
theorem cheap_halasz_pairing (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (hb : ∀ n, ‖f n‖ ≤ 1)
    (σ : ℝ → ℝ) (C : ℝ) (hσs : ContDiff ℝ ∞ σ)
    (hσ01 : ∀ v, 0 ≤ σ v ∧ σ v ≤ 1)
    (hσ0 : ∀ v, v ≤ 0 → σ v = 0) (hσ1 : ∀ v, 1 ≤ v → σ v = 1)
    (hC0 : 0 ≤ C) (hC1 : ∀ v, |deriv σ v| ≤ C)
    (hC2 : ∀ v, |deriv (deriv σ) v| ≤ C)
    (x y₂ y₁ : ℕ) (hy₂ : 4 ≤ y₂) (h12 : y₂ ≤ y₁) (hy₁x : y₁ ≤ x)
    (hx : 4 ≤ x)
    (ρ L t M δ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 1 ≤ L)
    (ht : 0 < t) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hM : ∀ ξ : ℝ, |ξ| ≤ L → M ≤ pretentiousDistSq f
      (fun n => (n:ℂ)^(Complex.I*((2*Real.pi*ξ : ℝ):ℂ))) x) :
    ‖∑ n ∈ Finset.Icc 1 x, f n‖/(x:ℝ)
      ≤ (((Nat.smoothNumbersUpTo x y₁).card : ℝ)
          + ((((Finset.Icc 1 x).filter (fun n =>
              roughPart y₂ n ≠ 1
                ∧ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1)))).card
            : ℝ)))/(x:ℝ)
        + (2*ρ + 2/(x:ℝ))
        + (1 * (Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - M
              + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
                - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
            + (x:ℝ)^(-δ) * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹)
          * (t*(1024*(Real.exp 12 * Real.log y₁)/Real.log y₂
              + 512*L*(12/Real.log y₂ + 2*(((y₂:ℝ)-1)^4)^2))
            + (1024*(Real.log x + 1)/Real.log y₁
              + 512*L*(12/Real.log y₁ + 2*(((y₁:ℝ)-1)^4)^2))/t)/2
          + (Real.exp 12 * Real.log y₂) * (Real.exp 12 * Real.log y₁)
            * (Real.log x + 1) * (9*(C+1)^2/ρ^2/(2*Real.pi^2*L))) := by
  classical
  have hx0 : (0:ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hL0 : (0:ℝ) < L := by linarith
  have hY : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have h4 : (4:ℝ) ≤ x := by exact_mod_cast hx
    linarith [Real.exp_one_lt_d9]
  -- the Perron window at Y = log x
  obtain ⟨V, hVs, hVsupp, hV0, hVend, hVplat, hVnn, hVle, hVone, hVM₂⟩ :=
    exists_perron_window σ C hσs hσ01 hσ0 hσ1 hC0 hC1 hC2
      ρ (Real.log x) hρ0 hρ1 hY
  have hVcs : ContDiff ℝ ∞ (fun v => ((V v : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hVs
  have hVcc : HasCompactSupport (fun v => ((V v : ℝ) : ℂ)) :=
    HasCompactSupport.comp_left hVsupp Complex.ofReal_zero
  -- weight and continuity generics
  have hwnorm : ∀ n : ℕ, 1 ≤ n → ‖f n/(n:ℂ)‖ ≤ 1/(n:ℝ) := by
    intro n hn
    rw [norm_div, Complex.norm_natCast]
    gcongr
    exact hb n
  have hchar_cont : ∀ (S : Finset ℕ), Continuous (fun ξ : ℝ =>
      ∑ n ∈ S, (f n/(n:ℂ))
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)) := by
    intro S
    refine continuous_finset_sum _ fun n _ => ?_
    refine Continuous.mul continuous_const ?_
    exact continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (by fun_prop))
  -- the trivial sups
  have hB1conv : (Finset.Icc 1 x).filter (· ∈ Nat.smoothNumbers y₂)
      = Nat.smoothNumbersUpTo x y₂ := by
    ext n
    rw [Finset.mem_filter, Finset.mem_Icc, Nat.mem_smoothNumbersUpTo]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨h2, h3⟩
    · rintro ⟨h2, h3⟩
      exact ⟨⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers h3),
        h2⟩, h3⟩
  have hB1sup : ∀ ξ : ℝ,
      ‖∑ n ∈ (Finset.Icc 1 x).filter (· ∈ Nat.smoothNumbers y₂),
        (f n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖
        ≤ Real.exp 12 * Real.log y₂ := by
    intro ξ
    refine le_trans (norm_char_poly_le_harmonic _ _ ?_
      (fun n => Real.log n) ξ) ?_
    · intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      exact hwnorm n hn.1.1
    · rw [hB1conv]
      exact sum_smooth_one_div_le y₂ x hy₂
  have hB2sup : ∀ ξ : ℝ,
      ‖∑ n ∈ (Finset.Icc 1 x).filter (fun b => b ≠ 1
          ∧ b ∈ Nat.smoothNumbers y₁
          ∧ Nat.Coprime b (primorial (y₂-1))),
        (f n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖
        ≤ Real.exp 12 * Real.log y₁ := by
    intro ξ
    refine le_trans (norm_char_poly_le_harmonic _ _ ?_
      (fun n => Real.log n) ξ) ?_
    · intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      exact hwnorm n hn.1.1
    · refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
        (sum_smooth_one_div_le y₁ x (by omega))
      · intro n hn
        rw [Finset.mem_filter, Finset.mem_Icc] at hn
        rw [Nat.mem_smoothNumbersUpTo]
        exact ⟨hn.1.2, hn.2.2.1⟩
      · intro n _ _
        positivity
  have hB3sup : ∀ ξ : ℝ,
      ‖∑ n ∈ (Finset.Icc 1 x).filter (fun c => c ≠ 1
          ∧ Nat.Coprime c (primorial (y₁-1))),
        (f n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖
        ≤ Real.log x + 1 := by
    intro ξ
    refine le_trans (norm_char_poly_le_harmonic _ _ ?_
      (fun n => Real.log n) ξ) ?_
    · intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      exact hwnorm n hn.1.1
    · refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) ?_) (sum_one_div_Icc_le_log x (by omega))
      intro n _ _
      positivity
  -- nonnegativity side conditions
  have hB₂0 : (0:ℝ) ≤ Real.exp 12 * Real.log y₁ :=
    mul_nonneg (Real.exp_pos _).le
      (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ y₁)))
  have hB₃0 : (0:ℝ) ≤ Real.log x + 1 := by linarith
  have hBb0 : (0:ℝ) ≤ Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - M
        + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
          - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
      + (x:ℝ)^(-δ) * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹ := by
    have hprod0 : (0:ℝ) ≤ ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹ := by
      refine Finset.prod_nonneg fun p hp => ?_
      have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesBelow hp).two_le
      have hple : (p:ℝ)^(δ-1) ≤ 1 := by
        refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (by linarith)
        exact_mod_cast (by omega : 1 ≤ p)
      have h0 : (0:ℝ) ≤ 1 - (p:ℝ)^(δ-1) := by linarith
      exact inv_nonneg.mpr h0
    exact add_nonneg (Real.exp_pos _).le
      (mul_nonneg (Real.rpow_nonneg hx0.le _) hprod0)
  -- the analytic instances
  have hMV : ∀ ξ : ℝ, ‖𝓕 (fun v => ((V v : ℝ) : ℂ)) ξ‖ ≤ 1 := fun ξ =>
    norm_fourier_window_le_one V hVs.continuous hVsupp hV0 hVnn hVle ξ
  have hMtail := fourier_tail_le V hVs hVsupp (9*(C+1)^2/ρ^2) hVM₂ L hL0
  have hBband : ∀ ξ : ℝ, |ξ| ≤ L →
      ‖∑ n ∈ (Finset.Icc 1 x).filter (· ∈ Nat.smoothNumbers y₂),
        (f n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖
        ≤ Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - M
              + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
                - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
          + (x:ℝ)^(-δ) * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹ :=
    fun ξ hξ => norm_smooth_poly_band_le f hcm h1 hb y₂ x (by omega)
      (le_trans h12 hy₁x) (by omega) ξ M δ hδ0 hδ1 (hM ξ hξ)
  have hE₂ := medium_class_band_energy_le f hb y₂ y₁ x (by omega) h12
    (by omega) L hL
  have hE₃ := large_class_band_energy_le f hb y₁ x (by omega) (by omega)
    L hL
  -- the band/tail split of the pairing
  have hsplit := pairing_band_tail_split
    (fun ξ => ∑ n ∈ (Finset.Icc 1 x).filter (· ∈ Nat.smoothNumbers y₂),
      (f n/(n:ℂ))
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ))
    (fun ξ => ∑ n ∈ (Finset.Icc 1 x).filter (fun b => b ≠ 1
        ∧ b ∈ Nat.smoothNumbers y₁
        ∧ Nat.Coprime b (primorial (y₂-1))),
      (f n/(n:ℂ))
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ))
    (fun ξ => ∑ n ∈ (Finset.Icc 1 x).filter (fun c => c ≠ 1
        ∧ Nat.Coprime c (primorial (y₁-1))),
      (f n/(n:ℂ))
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ))
    (hchar_cont _) (hchar_cont _) (hchar_cont _)
    (fun v => ((V v : ℝ) : ℂ)) hVcc hVcs
    L t (Real.exp 12 * Real.log y₂) (Real.exp 12 * Real.log y₁)
    (Real.log x + 1)
    (Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - M
        + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
          - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
      + (x:ℝ)^(-δ) * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹)
    1
    (1024*(Real.exp 12 * Real.log y₁)/Real.log y₂
      + 512*L*(12/Real.log y₂ + 2*(((y₂:ℝ)-1)^4)^2))
    (1024*(Real.log x + 1)/Real.log y₁
      + 512*L*(12/Real.log y₁ + 2*(((y₁:ℝ)-1)^4)^2))
    (9*(C+1)^2/ρ^2/(2*Real.pi^2*L))
    hL0 ht (by norm_num) hBb0 hB₂0 hB₃0
    hB1sup hB2sup hB3sup hBband hE₂ hE₃ hMV hMtail
  -- the pairing at the triple box, factorized
  have hpair := norm_sum_translates_le_integral_char
    (fun v => ((V v : ℝ) : ℂ)) hVcc hVcs
    (((Finset.Icc 1 x).filter (· ∈ Nat.smoothNumbers y₂)) ×ˢ
      (((Finset.Icc 1 x).filter (fun b => b ≠ 1
          ∧ b ∈ Nat.smoothNumbers y₁
          ∧ Nat.Coprime b (primorial (y₂-1)))) ×ˢ
       ((Finset.Icc 1 x).filter (fun c => c ≠ 1
          ∧ Nat.Coprime c (primorial (y₁-1))))))
    (fun t => f t.1/(t.1:ℂ) * (f t.2.1/(t.2.1:ℂ) * (f t.2.2/(t.2.2:ℂ))))
    (fun t => Real.log t.1 + (Real.log t.2.1 + Real.log t.2.2))
    (Real.log x)
  have hfact : ∀ ξ : ℝ,
      ∑ t ∈ (((Finset.Icc 1 x).filter (· ∈ Nat.smoothNumbers y₂)) ×ˢ
        (((Finset.Icc 1 x).filter (fun b => b ≠ 1
            ∧ b ∈ Nat.smoothNumbers y₁
            ∧ Nat.Coprime b (primorial (y₂-1)))) ×ˢ
         ((Finset.Icc 1 x).filter (fun c => c ≠ 1
            ∧ Nat.Coprime c (primorial (y₁-1)))))),
          (f t.1/(t.1:ℂ) * (f t.2.1/(t.2.1:ℂ) * (f t.2.2/(t.2.2:ℂ))))
            * ((Real.fourierChar
              (-((Real.log t.1 + (Real.log t.2.1 + Real.log t.2.2)) * ξ))
                : Circle) : ℂ)
        = (∑ n ∈ (Finset.Icc 1 x).filter (· ∈ Nat.smoothNumbers y₂),
            (f n/(n:ℂ))
              * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ))
          * ((∑ n ∈ (Finset.Icc 1 x).filter (fun b => b ≠ 1
              ∧ b ∈ Nat.smoothNumbers y₁
              ∧ Nat.Coprime b (primorial (y₂-1))),
            (f n/(n:ℂ))
              * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ))
          * (∑ n ∈ (Finset.Icc 1 x).filter (fun c => c ≠ 1
              ∧ Nat.Coprime c (primorial (y₁-1))),
            (f n/(n:ℂ))
              * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ))) :=
    fun ξ => sum_triple_char_eq_mul _ _ _
      (fun n => f n/(n:ℂ)) (fun n => f n/(n:ℂ)) (fun n => f n/(n:ℂ)) ξ
  -- the sandwich with the main-term indicator
  have hg : ∀ n : ℕ, ‖(if roughPart y₁ n ≠ 1
      ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))
        then f n else 0 : ℂ)‖ ≤ 1 := by
    intro n
    by_cases hp : roughPart y₁ n ≠ 1
      ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))
    · rw [if_pos hp]
      exact hb n
    · rw [if_neg hp]
      simp
  have hsand := perron_sandwich
    (fun n => if roughPart y₁ n ≠ 1
      ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))
        then f n else 0) hg V ρ x hx hρ0 hρ1 hVplat hV0 hVle hVnn
    (Finset.Icc 1 x) (subset_refl _)
    (fun n hn => (Finset.mem_Icc.mp hn).1)
  dsimp only at hsand
  -- collapse the indicator sums to the main set
  have hgV : ∑ n ∈ Finset.Icc 1 x,
      ((if roughPart y₁ n ≠ 1
        ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))
          then f n else 0)/(n:ℂ))
        * ((V (Real.log x - Real.log n) : ℝ) : ℂ)
      = ∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
          roughPart y₁ n ≠ 1
            ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))),
          (f n/(n:ℂ)) * ((V (Real.log x - Real.log n) : ℝ) : ℂ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hp : roughPart y₁ n ≠ 1
      ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))
    · rw [if_pos hp, if_pos hp]
    · rw [if_neg hp, if_neg hp, zero_div, zero_mul]
  have hgT : ∑ n ∈ Finset.Icc 1 x,
      (if roughPart y₁ n ≠ 1
        ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))
          then f n else 0)
      = ∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
          roughPart y₁ n ≠ 1
            ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))), f n := by
    rw [Finset.sum_filter]
  rw [hgV, hgT] at hsand
  -- the box bridge
  have hbridge := sum_main_eq_sum_box f hcm y₂ y₁ x (by omega) h12
    (by omega) V hV0
  -- chain: main V-sum ≤ split bound
  have hVbound : ‖∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
      roughPart y₁ n ≠ 1
        ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))),
      (f n/(n:ℂ)) * ((V (Real.log x - Real.log n) : ℝ) : ℂ)‖
      ≤ 1 * (Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - M
            + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
              - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
          + (x:ℝ)^(-δ) * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹)
        * (t*(1024*(Real.exp 12 * Real.log y₁)/Real.log y₂
            + 512*L*(12/Real.log y₂ + 2*(((y₂:ℝ)-1)^4)^2))
          + (1024*(Real.log x + 1)/Real.log y₁
            + 512*L*(12/Real.log y₁ + 2*(((y₁:ℝ)-1)^4)^2))/t)/2
        + (Real.exp 12 * Real.log y₂) * (Real.exp 12 * Real.log y₁)
          * (Real.log x + 1) * (9*(C+1)^2/ρ^2/(2*Real.pi^2*L)) := by
    calc ‖∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
        roughPart y₁ n ≠ 1
          ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))),
        (f n/(n:ℂ)) * ((V (Real.log x - Real.log n) : ℝ) : ℂ)‖
        = ‖∑ t ∈ (((Finset.Icc 1 x).filter (· ∈ Nat.smoothNumbers y₂)) ×ˢ
            (((Finset.Icc 1 x).filter (fun b => b ≠ 1
                ∧ b ∈ Nat.smoothNumbers y₁
                ∧ Nat.Coprime b (primorial (y₂-1)))) ×ˢ
             ((Finset.Icc 1 x).filter (fun c => c ≠ 1
                ∧ Nat.Coprime c (primorial (y₁-1)))))),
            (f t.1/(t.1:ℂ) * (f t.2.1/(t.2.1:ℂ) * (f t.2.2/(t.2.2:ℂ))))
              * ((V (Real.log x
                - (Real.log t.1 + (Real.log t.2.1 + Real.log t.2.2)))
                  : ℝ) : ℂ)‖ := congrArg norm hbridge
      _ ≤ ∫ ξ, ‖(∑ n ∈ (Finset.Icc 1 x).filter
              (· ∈ Nat.smoothNumbers y₂),
            (f n/(n:ℂ))
              * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ))
            * (∑ n ∈ (Finset.Icc 1 x).filter (fun b => b ≠ 1
                ∧ b ∈ Nat.smoothNumbers y₁
                ∧ Nat.Coprime b (primorial (y₂-1))),
              (f n/(n:ℂ))
                * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ))
            * (∑ n ∈ (Finset.Icc 1 x).filter (fun c => c ≠ 1
                ∧ Nat.Coprime c (primorial (y₁-1))),
              (f n/(n:ℂ))
                * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ))‖
            * ‖𝓕 (fun v => ((V v : ℝ) : ℂ)) ξ‖ := by
          refine le_trans hpair (le_of_eq ?_)
          refine MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall fun ξ => ?_)
          dsimp only
          rw [hfact ξ, ← mul_assoc]
      _ ≤ _ := hsplit
  -- the three-scale split and the Perron edge
  have ha3 := norm_cesaro_sub_main_le f hb y₂ y₁ x (by omega) h12
  have hstep1 : ‖∑ n ∈ Finset.Icc 1 x, f n‖
      ≤ ‖∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
          roughPart y₁ n ≠ 1
            ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))), f n‖
        + (((Nat.smoothNumbersUpTo x y₁).card : ℝ)
          + ((((Finset.Icc 1 x).filter (fun n =>
              roughPart y₂ n ≠ 1
                ∧ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1)))).card
            : ℝ))) := by
    have htri : ‖∑ n ∈ Finset.Icc 1 x, f n‖
        ≤ ‖∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
            roughPart y₁ n ≠ 1
              ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))), f n‖
          + ‖(∑ n ∈ Finset.Icc 1 x, f n)
            - ∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
                roughPart y₁ n ≠ 1
                  ∧ ¬ Nat.Coprime (roughPart y₂ n)
                    (primorial (y₁-1))), f n‖ := by
      calc ‖∑ n ∈ Finset.Icc 1 x, f n‖
          = ‖(∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
              roughPart y₁ n ≠ 1
                ∧ ¬ Nat.Coprime (roughPart y₂ n)
                  (primorial (y₁-1))), f n)
            + ((∑ n ∈ Finset.Icc 1 x, f n)
              - ∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
                  roughPart y₁ n ≠ 1
                    ∧ ¬ Nat.Coprime (roughPart y₂ n)
                      (primorial (y₁-1))), f n)‖ := by
            congr 1
            ring
        _ ≤ _ := norm_add_le _ _
    linarith [htri, ha3]
  -- the sandwich triangle
  have hsand2 : ‖∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
      roughPart y₁ n ≠ 1
        ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))), f n‖/(x:ℝ)
      ≤ ‖∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
          roughPart y₁ n ≠ 1
            ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))),
          (f n/(n:ℂ)) * ((V (Real.log x - Real.log n) : ℝ) : ℂ)‖
        + (2*ρ + 2/(x:ℝ)) := by
    have h0 : ‖∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
        roughPart y₁ n ≠ 1
          ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))),
          f n‖/(x:ℝ)
        = ‖(∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
            roughPart y₁ n ≠ 1
              ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))),
            f n)/(x:ℂ)‖ := by
      rw [norm_div, Complex.norm_natCast]
    rw [h0]
    have htri : ‖(∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
        roughPart y₁ n ≠ 1
          ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))),
          f n)/(x:ℂ)‖
        ≤ ‖∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
            roughPart y₁ n ≠ 1
              ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))),
            (f n/(n:ℂ)) * ((V (Real.log x - Real.log n) : ℝ) : ℂ)‖
          + ‖(∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
              roughPart y₁ n ≠ 1
                ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))),
              (f n/(n:ℂ)) * ((V (Real.log x - Real.log n) : ℝ) : ℂ))
            - (∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
                roughPart y₁ n ≠ 1
                  ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))),
                f n)/(x:ℂ)‖ := by
      calc ‖(∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
          roughPart y₁ n ≠ 1
            ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))),
            f n)/(x:ℂ)‖
          = ‖(∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
              roughPart y₁ n ≠ 1
                ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))),
              (f n/(n:ℂ)) * ((V (Real.log x - Real.log n) : ℝ) : ℂ))
            - ((∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
                roughPart y₁ n ≠ 1
                  ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))),
                (f n/(n:ℂ)) * ((V (Real.log x - Real.log n) : ℝ) : ℂ))
              - (∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
                  roughPart y₁ n ≠ 1
                    ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))),
                  f n)/(x:ℂ))‖ := by
            congr 1
            ring
        _ ≤ _ := norm_sub_le _ _
    linarith [htri, hsand]
  -- final assembly
  calc ‖∑ n ∈ Finset.Icc 1 x, f n‖/(x:ℝ)
      ≤ (‖∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
          roughPart y₁ n ≠ 1
            ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))), f n‖
        + (((Nat.smoothNumbersUpTo x y₁).card : ℝ)
          + ((((Finset.Icc 1 x).filter (fun n =>
              roughPart y₂ n ≠ 1
                ∧ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1)))).card
            : ℝ))))/(x:ℝ) := by
        gcongr
    _ = ‖∑ n ∈ (Finset.Icc 1 x).filter (fun n =>
          roughPart y₁ n ≠ 1
            ∧ ¬ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1))),
          f n‖/(x:ℝ)
        + (((Nat.smoothNumbersUpTo x y₁).card : ℝ)
          + ((((Finset.Icc 1 x).filter (fun n =>
              roughPart y₂ n ≠ 1
                ∧ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1)))).card
            : ℝ)))/(x:ℝ) := by
        ring
    _ ≤ _ := by
        linarith [hsand2, hVbound]

end MoltResearch
