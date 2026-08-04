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

The tuning tail of the file: `cheap_halasz_tuned` (the pairing at
`y₁ = y₂^B`, `t = 1`, `δ = 1/2`), the threshold lemmas
(`one_add_log_div_le`, `exp_neg_half_kill`, `log_pow_le_self`), the
term-by-term collapses (`rankin_tail_collapse`, `energy_sum_le`,
`head_exp_le`, `tail_energy_le`, `window_tail_le`) assembled by
`cheap_halasz_collapse`, and finally `cheap_halasz_eps` — **the cheap
Halász theorem** in ε-form: `‖∑_{n≤x} f‖/x ≤ ε + e^{W loglog x + W − M}`
at the cut `y₂ = ⌊log x⌋₊`, `B = ⌈16e¹²/ε⌉₊ + 1`, `ρ = ε/8`,
`L = (log x)⁴`.
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

/-- **The smooth-count ratio bound** (Track R, M2-i4c2a): the density
of `y`-smooth numbers up to `x` is at most `(1 + 8 log y)/log x`. -/
theorem smooth_count_div_le (y x : ℕ) (hy : 2 ≤ y) (hx : 2 ≤ x) :
    ((Nat.smoothNumbersUpTo x y).card : ℝ)/x
      ≤ (1 + 8*Real.log y)/Real.log x := by
  have h := smoothNumbersUpTo_card_mul_log_le y x hy
  have hlogx : (0:ℝ) < Real.log x :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hx0 : (0:ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  rw [div_le_div_iff₀ hx0 hlogx]
  calc ((Nat.smoothNumbersUpTo x y).card : ℝ) * Real.log x
      ≤ x + 8 * Real.log y * x := h
    _ = (1 + 8*Real.log y) * x := by ring

/-- **The Rankin count bound** (Track R, M2-i4c2a): the `y`-smooth
count up to `x` is at most `√x` times the Rankin product at
exponent `1/2`. -/
theorem smoothNumbersUpTo_card_le_sqrt_mul (y x : ℕ) (hx : 1 ≤ x) :
    ((Nat.smoothNumbersUpTo x y).card : ℝ)
      ≤ (x:ℝ)^((1:ℝ)/2)
        * ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(-(1/2:ℝ)))⁻¹ := by
  have hx0 : (0:ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hsum := sum_rpow_smoothNumbersUpTo_le (1/2) (by norm_num) y x
  have hterm : ∀ n ∈ Nat.smoothNumbersUpTo x y,
      (x:ℝ)^(-(1/2:ℝ)) ≤ (n:ℝ)^(-(1/2:ℝ)) := by
    intro n hn
    rw [Nat.mem_smoothNumbersUpTo] at hn
    have hn0 : n ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hn.2
    exact Real.rpow_le_rpow_of_nonpos
      (by exact_mod_cast Nat.pos_of_ne_zero hn0)
      (by exact_mod_cast hn.1) (by norm_num)
  have hcard : ((Nat.smoothNumbersUpTo x y).card : ℝ) * (x:ℝ)^(-(1/2:ℝ))
      ≤ ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(-(1/2:ℝ)))⁻¹ := by
    refine le_trans ?_ hsum
    calc ((Nat.smoothNumbersUpTo x y).card : ℝ) * (x:ℝ)^(-(1/2:ℝ))
        = ∑ _n ∈ Nat.smoothNumbersUpTo x y, (x:ℝ)^(-(1/2:ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ Nat.smoothNumbersUpTo x y, (n:ℝ)^(-(1/2:ℝ)) :=
          Finset.sum_le_sum hterm
  calc ((Nat.smoothNumbersUpTo x y).card : ℝ)
      = ((Nat.smoothNumbersUpTo x y).card : ℝ) * (x:ℝ)^(-(1/2:ℝ))
        * (x:ℝ)^((1:ℝ)/2) := by
        rw [mul_assoc, ← Real.rpow_add hx0]
        norm_num
    _ ≤ (∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(-(1/2:ℝ)))⁻¹)
        * (x:ℝ)^((1:ℝ)/2) :=
        mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hx0.le _)
    _ = (x:ℝ)^((1:ℝ)/2)
        * ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(-(1/2:ℝ)))⁻¹ := mul_comm _ _

/-- **The square-root telescope** (Track R, M2-i4c2a):
`∑_{n ≤ N} n^{-1/2} ≤ 2√N`. -/
theorem sum_rpow_neg_half_Icc_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n:ℝ)^(-(1/2:ℝ)) ≤ 2*Real.sqrt N := by
  induction N with
  | zero =>
    rw [show Finset.Icc 1 0 = ∅ from rfl]
    simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k+1)]
    have hstep : ((k+1:ℕ):ℝ)^(-(1/2:ℝ))
        ≤ 2*(Real.sqrt ((k:ℝ)+1) - Real.sqrt (k:ℝ)) := by
      have hcast : ((k+1:ℕ):ℝ) = (k:ℝ)+1 := by push_cast; ring
      have hval : ((k+1:ℕ):ℝ)^(-(1/2:ℝ))
          = (Real.sqrt ((k:ℝ)+1))⁻¹ := by
        rw [hcast, Real.rpow_neg (by positivity), Real.sqrt_eq_rpow]
      rw [hval]
      have ha0 : 0 ≤ Real.sqrt (k:ℝ) := Real.sqrt_nonneg _
      have hb0 : (0:ℝ) < Real.sqrt ((k:ℝ)+1) :=
        Real.sqrt_pos.mpr (by positivity)
      have ha2 : Real.sqrt (k:ℝ) * Real.sqrt (k:ℝ) = (k:ℝ) :=
        Real.mul_self_sqrt (by positivity)
      have hb2 : Real.sqrt ((k:ℝ)+1) * Real.sqrt ((k:ℝ)+1) = (k:ℝ)+1 :=
        Real.mul_self_sqrt (by positivity)
      rw [inv_eq_one_div, div_le_iff₀ hb0]
      nlinarith [sq_nonneg (Real.sqrt (k:ℝ) - Real.sqrt ((k:ℝ)+1)),
        ha2, hb2, ha0, hb0]
    push_cast at hstep ⊢
    linarith [ih]

/-- Prime version of the telescope. -/
theorem sum_rpow_neg_half_primesBelow_le (y : ℕ) :
    ∑ p ∈ y.primesBelow, (p:ℝ)^(-(1/2:ℝ)) ≤ 2*Real.sqrt y := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
    (sum_rpow_neg_half_Icc_le y)
  · intro p hp
    have hpp := Nat.prime_of_mem_primesBelow hp
    have hlt := Nat.lt_of_mem_primesBelow hp
    rw [Finset.mem_Icc]
    exact ⟨hpp.one_lt.le, by omega⟩
  · intro n _ _
    positivity

/-- **The Rankin product bound** (Track R, M2-i4c2a): the exponent
`1/2` Rankin product over primes below `y` is at most `e^{8√y}`. -/
theorem rankin_prod_le_exp_sqrt (y : ℕ) :
    ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(-(1/2:ℝ)))⁻¹
      ≤ Real.exp (8*Real.sqrt y) := by
  have hv : ∀ p ∈ y.primesBelow,
      0 ≤ (p:ℝ)^(-(1/2:ℝ)) ∧ ((p:ℝ)^(-(1/2:ℝ)))*((p:ℝ)^(-(1/2:ℝ))) ≤ 1/2 := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesBelow hp).two_le
    have hp0 : (0:ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    constructor
    · positivity
    · rw [← Real.rpow_add hp0]
      rw [show -(1/2:ℝ) + -(1/2:ℝ) = -1 from by norm_num, Real.rpow_neg_one]
      rw [inv_le_comm₀ hp0 (by norm_num)]
      norm_num
      exact_mod_cast (by omega : 2 ≤ p)
  have hfac : ∀ p ∈ y.primesBelow,
      (1 - (p:ℝ)^(-(1/2:ℝ)))⁻¹ ≤ Real.exp (4*(p:ℝ)^(-(1/2:ℝ))) := by
    intro p hp
    obtain ⟨hv0, hv2⟩ := hv p hp
    set v : ℝ := (p:ℝ)^(-(1/2:ℝ)) with hv_def
    have h1v : (0:ℝ) < 1 - v := by nlinarith
    have hquad : (1 - v)⁻¹ ≤ 1 + 4*v + 4*v^2 := by
      rw [inv_eq_one_div, div_le_iff₀ h1v]
      nlinarith
    refine le_trans hquad ?_
    have hexp : 1+2*v ≤ Real.exp (2*v) := by
      linarith [Real.add_one_le_exp (2*v)]
    have hsq : (1+2*v)*(1+2*v) ≤ Real.exp (2*v) * Real.exp (2*v) :=
      mul_le_mul hexp hexp (by linarith) (Real.exp_pos _).le
    have h4 : Real.exp (4*v) = Real.exp (2*v) * Real.exp (2*v) := by
      rw [← Real.exp_add]
      ring_nf
    rw [h4]
    nlinarith [hsq]
  calc ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(-(1/2:ℝ)))⁻¹
      ≤ ∏ p ∈ y.primesBelow, Real.exp (4*(p:ℝ)^(-(1/2:ℝ))) := by
        refine Finset.prod_le_prod ?_ hfac
        intro p hp
        obtain ⟨hv0, hv2⟩ := hv p hp
        have h1v : (0:ℝ) < 1 - (p:ℝ)^(-(1/2:ℝ)) := by nlinarith
        positivity
    _ = Real.exp (∑ p ∈ y.primesBelow, 4*(p:ℝ)^(-(1/2:ℝ))) := by
        rw [Real.exp_sum]
    _ ≤ Real.exp (8*Real.sqrt y) := by
        rw [Real.exp_le_exp, ← Finset.mul_sum]
        linarith [sum_rpow_neg_half_primesBelow_le y]

/-- **The medium-free count ratio** (Track R, M2-i4c2a): the density
of numbers with a large part but no medium part is at most the
Mertens ratio plus a superpolynomially small Rankin remainder. -/
theorem medfree_large_count_div_le (y₂ y₁ x : ℕ) (h2 : 4 ≤ y₂)
    (h12 : y₂ ≤ y₁) (hx : 1 ≤ x) :
    ((((Finset.Icc 1 x).filter (fun n =>
        roughPart y₂ n ≠ 1
          ∧ Nat.Coprime (roughPart y₂ n) (primorial (y₁-1)))).card : ℝ))/x
      ≤ 2*(Real.exp 12 * Real.log y₂)/Real.log y₁
        + (x:ℝ)^(-(1/2:ℝ)) * Real.exp (8*Real.sqrt y₂) * ((y₁:ℝ)^4)^2 := by
  have hx0 : (0:ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hcount := card_medfree_large_le y₂ y₁ x h2 h12
  have hrankin := smoothNumbersUpTo_card_le_sqrt_mul y₂ x hx
  have hprod := rankin_prod_le_exp_sqrt y₂
  have hpow0 : (0:ℝ) ≤ ((y₁:ℝ)^4)^2 := by positivity
  have hΨ : ((Nat.smoothNumbersUpTo x y₂).card : ℝ)
      ≤ (x:ℝ)^((1:ℝ)/2) * Real.exp (8*Real.sqrt y₂) := by
    refine le_trans hrankin ?_
    refine mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hx0.le _)
  rw [div_le_iff₀ hx0]
  refine le_trans hcount ?_
  have h1 : (2*(x:ℝ)/Real.log y₁) * (Real.exp 12 * Real.log y₂)
      = (2*(Real.exp 12 * Real.log y₂)/Real.log y₁) * x := by
    ring
  have hxsplit : (x:ℝ)^((1:ℝ)/2) = (x:ℝ)^(-(1/2:ℝ)) * x := by
    have h : (x:ℝ)^(-(1/2:ℝ)) * (x:ℝ)^((1:ℝ)) = (x:ℝ)^((1:ℝ)/2) := by
      rw [← Real.rpow_add hx0]
      norm_num
    rw [Real.rpow_one] at h
    exact h.symm
  have h2' : ((Nat.smoothNumbersUpTo x y₂).card : ℝ) * ((y₁:ℝ)^4)^2
      ≤ ((x:ℝ)^(-(1/2:ℝ)) * Real.exp (8*Real.sqrt y₂) * ((y₁:ℝ)^4)^2)
        * x := by
    calc ((Nat.smoothNumbersUpTo x y₂).card : ℝ) * ((y₁:ℝ)^4)^2
        ≤ ((x:ℝ)^((1:ℝ)/2) * Real.exp (8*Real.sqrt y₂)) * ((y₁:ℝ)^4)^2 :=
          mul_le_mul_of_nonneg_right hΨ hpow0
      _ = ((x:ℝ)^(-(1/2:ℝ)) * Real.exp (8*Real.sqrt y₂) * ((y₁:ℝ)^4)^2)
          * x := by
          rw [hxsplit]
          ring
  linarith [h1.le, h1.ge, h2']

/-- **The band-exponent collection** (Track R, M2-i4c2a): the head
exponent of the band sup — prime mass at the small cut, minus the
floor, plus twice the mass difference — is at most
`10 loglog x + 42 - M`. -/
theorem bband_exponent_le (y₂ x : ℕ) (hy₂ : 4 ≤ y₂) (hyx : y₂ ≤ x)
    (M : ℝ) :
    (∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - M
      + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
        - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1
    ≤ 10*Real.log (Real.log x) + 42 - M := by
  have h1 := sum_one_div_primesBelow_le_sharp y₂ hy₂
  have h2 := mass_diff_le y₂ x hy₂ hyx
  have h3 : 0 ≤ Real.log (Real.log y₂) := by
    refine Real.log_nonneg ?_
    rw [Real.le_log_iff_exp_le (by exact_mod_cast (by omega : 0 < y₂))]
    have h4 : (4:ℝ) ≤ y₂ := by exact_mod_cast hy₂
    linarith [Real.exp_one_lt_d9]
  linarith

set_option maxHeartbeats 3200000 in
/-- **The tuned cheap Halász bound** (Track R, M2-i4c2b-i): the
pairing bound at the tuned parameters `y₁ = y₂^B`, `t = 1`,
`δ = 1/2`, with the head exponent collapsed by the mass lemmas and
the Rankin tails collapsed by the `e^{8√y₂}` product bound. Pure
algebra over the assembly; the asymptotic collapse is the next
stage. -/
theorem cheap_halasz_tuned (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (hb : ∀ n, ‖f n‖ ≤ 1)
    (σ : ℝ → ℝ) (C : ℝ) (hσs : ContDiff ℝ ∞ σ)
    (hσ01 : ∀ v, 0 ≤ σ v ∧ σ v ≤ 1)
    (hσ0 : ∀ v, v ≤ 0 → σ v = 0) (hσ1 : ∀ v, 1 ≤ v → σ v = 1)
    (hC0 : 0 ≤ C) (hC1 : ∀ v, |deriv σ v| ≤ C)
    (hC2 : ∀ v, |deriv (deriv σ) v| ≤ C)
    (x y₂ B : ℕ) (hy₂ : 4 ≤ y₂) (hB : 1 ≤ B) (hy₁x : y₂^B ≤ x)
    (hx : 4 ≤ x)
    (ρ L M : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 1 ≤ L)
    (hM : ∀ ξ : ℝ, |ξ| ≤ L → M ≤ pretentiousDistSq f
      (fun n => (n:ℂ)^(Complex.I*((2*Real.pi*ξ : ℝ):ℂ))) x) :
    ‖∑ n ∈ Finset.Icc 1 x, f n‖/(x:ℝ)
      ≤ (1 + 8*(B*Real.log y₂))/Real.log x
        + (2*(Real.exp 12 * Real.log y₂)/(B*Real.log y₂)
          + (x:ℝ)^(-(1/2:ℝ)) * Real.exp (8*Real.sqrt y₂)
            * (((y₂:ℝ)^B)^4)^2)
        + (2*ρ + 2/(x:ℝ))
        + (Real.exp (10*Real.log (Real.log x) + 42 - M)
            + (x:ℝ)^(-(1/2:ℝ)) * Real.exp (8*Real.sqrt y₂))
          * ((1024*(Real.exp 12 * (B*Real.log y₂))/Real.log y₂
              + 512*L*(12/Real.log y₂ + 2*(((y₂:ℝ)-1)^4)^2))
            + (1024*(Real.log x + 1)/(B*Real.log y₂)
              + 512*L*(12/(B*Real.log y₂) + 2*(((y₂:ℝ)^B-1)^4)^2)))/2
        + (Real.exp 12 * Real.log y₂) * (Real.exp 12 * (B*Real.log y₂))
          * (Real.log x + 1) * (9*(C+1)^2/ρ^2/(2*Real.pi^2*L)) := by
  classical
  have hx0 : (0:ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hy₂0 : (0:ℝ) < y₂ := by exact_mod_cast (by omega : 0 < y₂)
  have hy₂x : y₂ ≤ x := le_trans (Nat.le_self_pow (by omega) y₂) hy₁x
  have hy₁4 : 4 ≤ y₂^B := le_trans hy₂ (Nat.le_self_pow (by omega) y₂)
  have hcast : ((y₂^B : ℕ):ℝ) = (y₂:ℝ)^B := by push_cast; ring
  have hlogy₁ : Real.log ((y₂^B : ℕ):ℝ) = B*Real.log y₂ := by
    rw [hcast, Real.log_pow]
  have hlogy₂1 : 1 ≤ Real.log y₂ := by
    rw [Real.le_log_iff_exp_le hy₂0]
    have h4 : (4:ℝ) ≤ y₂ := by exact_mod_cast hy₂
    linarith [Real.exp_one_lt_d9]
  have hlogy₂0 : (0:ℝ) < Real.log y₂ := by linarith
  -- the raw pairing bound at y₁ = y₂^B, t = 1, δ = 1/2
  have hraw := cheap_halasz_pairing f hcm h1 hb σ C hσs hσ01 hσ0 hσ1
    hC0 hC1 hC2 x y₂ (y₂^B) hy₂ (Nat.le_self_pow (by omega) y₂) hy₁x hx
    ρ L 1 M (1/2) hρ0 hρ1 hL (by norm_num) (by norm_num) (by norm_num) hM
  refine le_trans hraw ?_
  -- piecewise domination
  have hE₁ : (((Nat.smoothNumbersUpTo x (y₂^B)).card : ℝ)
      + ((((Finset.Icc 1 x).filter (fun n =>
          roughPart y₂ n ≠ 1
            ∧ Nat.Coprime (roughPart y₂ n) (primorial (y₂^B-1)))).card
        : ℝ)))/(x:ℝ)
      ≤ (1 + 8*(B*Real.log y₂))/Real.log x
        + (2*(Real.exp 12 * Real.log y₂)/(B*Real.log y₂)
          + (x:ℝ)^(-(1/2:ℝ)) * Real.exp (8*Real.sqrt y₂)
            * (((y₂:ℝ)^B)^4)^2) := by
    rw [add_div]
    refine add_le_add ?_ ?_
    · have h := smooth_count_div_le (y₂^B) x (by omega) (by omega)
      rw [hlogy₁] at h
      exact h
    · have h := medfree_large_count_div_le y₂ (y₂^B) x hy₂
        (Nat.le_self_pow (by omega) y₂) (by omega)
      rw [hlogy₁, hcast] at h
      exact h
  -- the band factor: exponent collapse + Rankin collapse
  have hhead : Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - M
        + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
          - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
      ≤ Real.exp (10*Real.log (Real.log x) + 42 - M) := by
    rw [Real.exp_le_exp]
    exact bband_exponent_le y₂ x hy₂ hy₂x M
  have hconv : ∀ p : ℕ, ((p:ℝ))^((1/2:ℝ)-1) = (p:ℝ)^(-(1/2:ℝ)) := by
    intro p
    rw [show (1/2:ℝ)-1 = -(1/2:ℝ) from by norm_num]
  have hprodeq : ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^((1/2:ℝ)-1))⁻¹
      = ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(-(1/2:ℝ)))⁻¹ := by
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [hconv p]
  have htailprod : (x:ℝ)^(-(1/2:ℝ))
      * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^((1/2:ℝ)-1))⁻¹
      ≤ (x:ℝ)^(-(1/2:ℝ)) * Real.exp (8*Real.sqrt y₂) := by
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hx0.le _)
    rw [hprodeq]
    exact rankin_prod_le_exp_sqrt y₂
  have hBlog0 : (0:ℝ) ≤ (B:ℝ)*Real.log y₂ :=
    mul_nonneg (by positivity) hlogy₂0.le
  have hL0' : (0:ℝ) ≤ L := by linarith
  have hlogx0 : (0:ℝ) ≤ Real.log x :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
  have hE20 : (0:ℝ) ≤ 1024*(Real.exp 12 * ((B:ℝ)*Real.log y₂))/Real.log y₂
      + 512*L*(12/Real.log y₂ + 2*(((y₂:ℝ)-1)^4)^2) := by
    have t2 : (0:ℝ) ≤ 12/Real.log y₂ := div_nonneg (by norm_num) hlogy₂0.le
    have t3 : (0:ℝ) ≤ 2*(((y₂:ℝ)-1)^4)^2 := by positivity
    have t4 : (0:ℝ) ≤ 512*L*(12/Real.log y₂ + 2*(((y₂:ℝ)-1)^4)^2) :=
      mul_nonneg (mul_nonneg (by norm_num) hL0') (by linarith)
    have t5 : (0:ℝ) ≤ 1024*(Real.exp 12 * ((B:ℝ)*Real.log y₂))/Real.log y₂ :=
      div_nonneg (mul_nonneg (by norm_num)
        (mul_nonneg (Real.exp_pos _).le hBlog0)) hlogy₂0.le
    linarith
  have hE30 : (0:ℝ) ≤ 1024*(Real.log x + 1)/((B:ℝ)*Real.log y₂)
      + 512*L*(12/((B:ℝ)*Real.log y₂) + 2*(((y₂:ℝ)^B-1)^4)^2) := by
    have t2 : (0:ℝ) ≤ 12/((B:ℝ)*Real.log y₂) :=
      div_nonneg (by norm_num) hBlog0
    have t3 : (0:ℝ) ≤ 2*(((y₂:ℝ)^B-1)^4)^2 := by positivity
    have t4 : (0:ℝ) ≤ 512*L*(12/((B:ℝ)*Real.log y₂)
        + 2*(((y₂:ℝ)^B-1)^4)^2) :=
      mul_nonneg (mul_nonneg (by norm_num) hL0') (by linarith)
    have t5 : (0:ℝ) ≤ 1024*(Real.log x + 1)/((B:ℝ)*Real.log y₂) :=
      div_nonneg (mul_nonneg (by norm_num) (by linarith)) hBlog0
    linarith
  -- collapse the head exponent and the two Rankin tails, then dominate
  rw [hlogy₁, hcast]
  have hheadsum : Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - M
        + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
          - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
      + (x:ℝ)^(-(1/2:ℝ))
        * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^((1/2:ℝ)-1))⁻¹
      ≤ Real.exp (10*Real.log (Real.log x) + 42 - M)
        + (x:ℝ)^(-(1/2:ℝ)) * Real.exp (8*Real.sqrt y₂) :=
    add_le_add hhead htailprod
  have hheadsum0 : (0:ℝ) ≤ Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - M
        + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
          - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
      + (x:ℝ)^(-(1/2:ℝ))
        * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^((1/2:ℝ)-1))⁻¹ := by
    have hp0 : (0:ℝ) ≤ ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^((1/2:ℝ)-1))⁻¹ := by
      refine Finset.prod_nonneg fun p hp => ?_
      have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesBelow hp).two_le
      have hple : (p:ℝ)^((1/2:ℝ)-1) ≤ 1 := by
        refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (by norm_num)
        exact_mod_cast (by omega : 1 ≤ p)
      have h0 : (0:ℝ) ≤ 1 - (p:ℝ)^((1/2:ℝ)-1) := by linarith
      exact inv_nonneg.mpr h0
    have := (Real.exp_pos ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - M
        + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
          - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)).le
    have h2 := mul_nonneg (Real.rpow_nonneg hx0.le (-(1/2:ℝ))) hp0
    linarith
  simp only [one_mul, div_one]
  have hE0sum : (0:ℝ) ≤ (1024*(Real.exp 12 * ((B:ℝ)*Real.log y₂))/Real.log y₂
        + 512*L*(12/Real.log y₂ + 2*(((y₂:ℝ)-1)^4)^2))
      + (1024*(Real.log x + 1)/((B:ℝ)*Real.log y₂)
        + 512*L*(12/((B:ℝ)*Real.log y₂) + 2*(((y₂:ℝ)^B-1)^4)^2)) := by
    linarith [hE20, hE30]
  have hmul := mul_le_mul_of_nonneg_right hheadsum hE0sum
  linarith [hE₁, hmul]

/-- `log u ≤ 2√u` for `u ≥ 0`. -/
theorem log_le_two_sqrt_of_nonneg {u : ℝ} (hu : 0 ≤ u) :
    Real.log u ≤ 2*Real.sqrt u := by
  have h := Real.log_le_rpow_div hu (by norm_num : (0:ℝ) < 1/2)
  rw [Real.sqrt_eq_rpow]
  calc Real.log u ≤ u^((1:ℝ)/2)/(1/2) := h
    _ = 2*u^((1:ℝ)/2) := by ring

/-- `√u ≤ u/c` for `c > 0` once `u ≥ c²`. -/
theorem sqrt_le_div {u c : ℝ} (hc : 0 < c) (hu : c^2 ≤ u) :
    Real.sqrt u ≤ u/c := by
  have hu0 : (0:ℝ) ≤ u := le_trans (by positivity) hu
  have hcs : c ≤ Real.sqrt u := by
    rw [show c = Real.sqrt (c^2) from (Real.sqrt_sq hc.le).symm]
    exact Real.sqrt_le_sqrt hu
  have hs0 : 0 < Real.sqrt u := lt_of_lt_of_le hc hcs
  rw [le_div_iff₀ hc]
  calc Real.sqrt u * c ≤ Real.sqrt u * Real.sqrt u :=
        mul_le_mul_of_nonneg_left hcs hs0.le
    _ = u := Real.mul_self_sqrt hu0

/-- **Threshold A** (Track R, M2-i4c2c): the ratio `(1 + b log u)/u`
drops below any `ε` once `u ≥ max 1 ((2(1+2b)/ε)²)`. -/
theorem one_add_log_div_le {ε b : ℝ} (hε : 0 < ε) (hb : 0 ≤ b) :
    ∀ u : ℝ, max 1 ((2*(1+2*b)/ε)^2) ≤ u → (1 + b*Real.log u)/u ≤ ε := by
  intro u hu
  have hu1 : (1:ℝ) ≤ u := le_trans (le_max_left _ _) hu
  have hu0 : (0:ℝ) < u := by linarith
  have hs1 : (1:ℝ) ≤ Real.sqrt u := by
    rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hu1
  have hlog : Real.log u ≤ 2*Real.sqrt u := log_le_two_sqrt_of_nonneg hu0.le
  have hnum : 1 + b*Real.log u ≤ (1+2*b)*Real.sqrt u := by
    have h1 : b*Real.log u ≤ 2*b*Real.sqrt u := by
      calc b*Real.log u ≤ b*(2*Real.sqrt u) :=
            mul_le_mul_of_nonneg_left hlog hb
        _ = 2*b*Real.sqrt u := by ring
    nlinarith [hs1]
  have hc0 : (0:ℝ) < 2*(1+2*b)/ε := by positivity
  have hsq : Real.sqrt u ≤ u/(2*(1+2*b)/ε) :=
    sqrt_le_div hc0 (le_trans (le_max_right _ _) hu)
  have h1b : (0:ℝ) < 1+2*b := by linarith
  rw [div_le_iff₀ hu0]
  calc 1 + b*Real.log u ≤ (1+2*b)*Real.sqrt u := hnum
    _ ≤ (1+2*b)*(u/(2*(1+2*b)/ε)) :=
        mul_le_mul_of_nonneg_left hsq h1b.le
    _ = (ε/2)*u := by
        field_simp
    _ ≤ ε*u := by nlinarith [hu0]

/-- **Threshold B, the super-kill** (Track R, M2-i4c2c): the
`e^{-u/2}`-decay beats `e^{8√u}`, any log-power, and any constant. -/
theorem exp_neg_half_kill {ε c k : ℝ} (hε : 0 < ε) (hc : 0 ≤ c)
    (hk : 0 ≤ k) :
    ∀ u : ℝ, max (max 4096 (256*(k+1)^2)) (4*Real.log ((c+1)/ε) + 1) ≤ u →
      c * Real.exp (-(u/2) + 8*Real.sqrt u + k*Real.log u) ≤ ε := by
  intro u hu
  have hu4096 : (4096:ℝ) ≤ u :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu
  have hu0 : (0:ℝ) < u := by linarith
  have huk : 256*(k+1)^2 ≤ u :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu
  have hulog : 4*Real.log ((c+1)/ε) + 1 ≤ u :=
    le_trans (le_max_right _ _) hu
  -- 8√u ≤ u/8
  have h8 : 8*Real.sqrt u ≤ u/8 := by
    have h := sqrt_le_div (by norm_num : (0:ℝ) < 64)
      (by nlinarith : (64:ℝ)^2 ≤ u)
    calc 8*Real.sqrt u ≤ 8*(u/64) := by
          linarith [h]
      _ = u/8 := by ring
  -- k log u ≤ u/8
  have hklog : k*Real.log u ≤ u/8 := by
    have hlog : Real.log u ≤ 2*Real.sqrt u := log_le_two_sqrt_of_nonneg hu0.le
    have hsq : Real.sqrt u ≤ u/(16*(k+1)) := by
      refine sqrt_le_div (by positivity) ?_
      nlinarith
    calc k*Real.log u ≤ k*(2*Real.sqrt u) := by
          refine mul_le_mul_of_nonneg_left hlog hk
      _ ≤ (k+1)*(2*(u/(16*(k+1)))) := by
          have h2s : 2*Real.sqrt u ≤ 2*(u/(16*(k+1))) := by linarith
          refine mul_le_mul (by linarith) h2s (by positivity) (by linarith)
      _ = u/8 := by
          field_simp
          ring
  -- the exponent is at most −u/4
  have hexp : -(u/2) + 8*Real.sqrt u + k*Real.log u ≤ -(u/4) := by
    linarith
  -- finish: c·e^{−u/4} ≤ ε
  have hfin : c * Real.exp (-(u/4)) ≤ ε := by
    have hlogc : Real.log ((c+1)/ε) ≤ u/4 := by linarith
    have hexp2 : (c+1)/ε ≤ Real.exp (u/4) := by
      calc (c+1)/ε = Real.exp (Real.log ((c+1)/ε)) := by
            rw [Real.exp_log (by positivity)]
        _ ≤ Real.exp (u/4) := Real.exp_le_exp.mpr hlogc
    have hpos : (0:ℝ) < Real.exp (u/4) := Real.exp_pos _
    rw [show Real.exp (-(u/4)) = (Real.exp (u/4))⁻¹ from Real.exp_neg _]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < ε)] at hexp2
    have h1 : c * (Real.exp (u/4))⁻¹ ≤ (ε * Real.exp (u/4) - 1) * (Real.exp (u/4))⁻¹ := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      linarith
    calc c * (Real.exp (u/4))⁻¹
        ≤ (ε * Real.exp (u/4) - 1) * (Real.exp (u/4))⁻¹ := h1
      _ = ε - (Real.exp (u/4))⁻¹ := by
          field_simp
      _ ≤ ε := by
          have : (0:ℝ) < (Real.exp (u/4))⁻¹ := by positivity
          linarith
  calc c * Real.exp (-(u/2) + 8*Real.sqrt u + k*Real.log u)
      ≤ c * Real.exp (-(u/4)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hc
    _ ≤ ε := hfin

/-- **Threshold D** (Track R, M2-i4c2c): `(log x)^B ≤ x` once
`x ≥ ((2B)^B)²`. -/
theorem log_pow_le_self {B : ℕ} (hB : 1 ≤ B) :
    ∀ x : ℝ, max 1 (((2*(B:ℝ))^B)^2) ≤ x → (Real.log x)^B ≤ x := by
  intro x hx
  have hx1 : (1:ℝ) ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : (0:ℝ) < x := by linarith
  have hB0 : (0:ℝ) < 2*(B:ℝ) := by
    have : (1:ℝ) ≤ (B:ℝ) := by exact_mod_cast hB
    linarith
  have hlog : Real.log x ≤ 2*(B:ℝ)*x^(1/(2*(B:ℝ))) := by
    have h := Real.log_le_rpow_div hx0.le
      (by positivity : (0:ℝ) < 1/(2*(B:ℝ)))
    calc Real.log x ≤ x^(1/(2*(B:ℝ)))/(1/(2*(B:ℝ))) := h
      _ = 2*(B:ℝ)*x^(1/(2*(B:ℝ))) := by
          field_simp
  have hlog0 : (0:ℝ) ≤ Real.log x := Real.log_nonneg hx1
  have hpow : (Real.log x)^B ≤ (2*(B:ℝ))^B * (x^(1/(2*(B:ℝ))))^B := by
    calc (Real.log x)^B ≤ (2*(B:ℝ)*x^(1/(2*(B:ℝ))))^B :=
          pow_le_pow_left₀ hlog0 hlog B
      _ = (2*(B:ℝ))^B * (x^(1/(2*(B:ℝ))))^B := mul_pow _ _ _
  have hxhalf : (x^(1/(2*(B:ℝ))))^B = x^((1:ℝ)/2) := by
    rw [← Real.rpow_natCast (x^(1/(2*(B:ℝ)))) B, ← Real.rpow_mul hx0.le]
    congr 1
    have hBne : (B:ℝ) ≠ 0 := by positivity
    field_simp
  have hfinal : (2*(B:ℝ))^B * x^((1:ℝ)/2) ≤ x := by
    have hbig : ((2*(B:ℝ))^B)^2 ≤ x := le_trans (le_max_right _ _) hx
    have hsx : x^((1:ℝ)/2) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm
    rw [hsx]
    have hs2 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    have hple : (2*(B:ℝ))^B ≤ Real.sqrt x := by
      rw [show (2*(B:ℝ))^B = Real.sqrt (((2*(B:ℝ))^B)^2) from
        (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt hbig
    calc (2*(B:ℝ))^B * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
          mul_le_mul_of_nonneg_right hple (Real.sqrt_nonneg _)
      _ = x := hs2
  calc (Real.log x)^B ≤ (2*(B:ℝ))^B * (x^(1/(2*(B:ℝ))))^B := hpow
    _ = (2*(B:ℝ))^B * x^((1:ℝ)/2) := by rw [hxhalf]
    _ ≤ x := hfinal

/-- A two-term product split: the shape of the band term in the
cheap-Halász collapse. -/
theorem prod_split_le {a b E c P Q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hEc : E/2 ≤ c) (hac : a*c ≤ P) (hbc : b*c ≤ Q) :
    (a + b)*E/2 ≤ P + Q := by
  have h1 : a*(E/2) ≤ a*c := mul_le_mul_of_nonneg_left hEc ha
  have h2 : b*(E/2) ≤ b*c := mul_le_mul_of_nonneg_left hEc hb
  linarith [h1, h2, hac, hbc]

/-- **The Rankin remainder collapse** (Track R, M2-i4c2c): the
`x^{−1/2}e^{8√y₂}·y₁⁸`-remainder of the medium-class count, absorbed
by the `e^{−u/2}`-kill at the cut `y₂ ≤ u`, `y₁ = y₂^B`. -/
theorem rankin_tail_collapse {B : ℕ} {ε u Y R : ℝ} (hY1 : 1 ≤ Y)
    (hYu : Y ≤ u) (hu0 : 0 < u) (hR : R ≤ Real.exp (-(u/2)))
    (hK1 : (1:ℝ) * Real.exp (-(u/2) + 8*Real.sqrt u
      + 8*(B:ℝ)*Real.log u) ≤ ε/8) :
    R * Real.exp (8*Real.sqrt Y) * ((Y^B)^4)^2 ≤ ε/8 := by
  have hpow : ((Y^B)^4)^2 ≤ u^(8*B) := by
    rw [← pow_mul, ← pow_mul, show B*(4*2) = 8*B from by ring]
    exact pow_le_pow_left₀ (by linarith) hYu _
  have hpowexp : u^(8*B) = Real.exp (8*(B:ℝ)*Real.log u) := by
    rw [show 8*(B:ℝ) = ((8*B : ℕ):ℝ) from by push_cast; ring,
      ← Real.log_pow, Real.exp_log (pow_pos hu0 _)]
  have hsqmono : Real.sqrt Y ≤ Real.sqrt u := Real.sqrt_le_sqrt hYu
  calc R * Real.exp (8*Real.sqrt Y) * ((Y^B)^4)^2
      ≤ Real.exp (-(u/2)) * Real.exp (8*Real.sqrt u)
        * Real.exp (8*(B:ℝ)*Real.log u) := by
        refine mul_le_mul ?_ (le_trans hpow hpowexp.le) (by positivity)
          (by positivity)
        refine mul_le_mul hR ?_ (Real.exp_pos _).le (Real.exp_pos _).le
        exact Real.exp_le_exp.mpr (by linarith)
    _ = 1 * Real.exp (-(u/2) + 8*Real.sqrt u + 8*(B:ℝ)*Real.log u) := by
        rw [← Real.exp_add, ← Real.exp_add, one_mul]
    _ ≤ ε/8 := hK1

/-- **The band energy in closed form** (Track R, M2-i4c2c): the two
class band energies of the tuned bound, at the cut `y₂ ≤ u`,
`y₁ = y₂^B` and window width `L = u⁴`, are at most
`2c₃u^{8B+12}` for `c₃ ≥ 1024e¹²B + 20000`. -/
theorem energy_sum_le {B : ℕ} {c₃ u Y : ℝ} (hu1 : 1 ≤ u) (hY1 : 1 ≤ Y)
    (hYu : Y ≤ u) (hlogY1 : 1 ≤ Real.log Y)
    (hBlogY1 : 1 ≤ (B:ℝ)*Real.log Y)
    (hc₃ : 1024*Real.exp 12*(B:ℝ) + 20000 ≤ c₃) :
    ((1024*(Real.exp 12 * ((B:ℝ)*Real.log Y))/Real.log Y
        + 512*(u^4)*(12/Real.log Y + 2*((Y-1)^4)^2))
      + (1024*(u + 1)/((B:ℝ)*Real.log Y)
        + 512*(u^4)*(12/((B:ℝ)*Real.log Y) + 2*((Y^B-1)^4)^2)))/2
      ≤ c₃*u^(8*B+12) := by
  have hu0 : (0:ℝ) < u := by linarith
  have hlogY0 : (0:ℝ) < Real.log Y := by linarith
  have hBlog0 : (0:ℝ) < (B:ℝ)*Real.log Y := by linarith
  have hup : (0:ℝ) ≤ u^(8*B+12) := (pow_pos hu0 _).le
  have hupowP : ∀ k : ℕ, k ≤ 8*B+12 → u^k ≤ u^(8*B+12) :=
    fun k hk => pow_le_pow_right₀ hu1 hk
  have hcanc2 : 1024*(Real.exp 12 * ((B:ℝ)*Real.log Y))/Real.log Y
      = 1024*Real.exp 12*(B:ℝ) := by
    field_simp
  have h12a : 12/Real.log Y ≤ 12 := by
    rw [div_le_iff₀ hlogY0]
    nlinarith [hlogY1]
  have h12b : 12/((B:ℝ)*Real.log Y) ≤ 12 := by
    rw [div_le_iff₀ hBlog0]
    nlinarith [hBlogY1]
  have hy8 : ((Y-1)^4)^2 ≤ u^8 := by
    rw [← pow_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hyB8 : ((Y^B-1)^4)^2 ≤ u^(8*B) := by
    rw [← pow_mul]
    have h1' : (0:ℝ) ≤ Y^B - 1 := by
      have := one_le_pow₀ hY1 (n := B)
      linarith
    have h2' : Y^B - 1 ≤ u^B := by
      have := pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ Y) hYu B
      linarith
    calc (Y^B-1)^(4*2) ≤ (u^B)^(4*2) := pow_le_pow_left₀ h1' h2' _
      _ = u^(8*B) := by rw [← pow_mul, show B*(4*2) = 8*B from by ring]
  have hA1 : 1024*Real.exp 12*(B:ℝ)
      ≤ 1024*Real.exp 12*(B:ℝ)*u^(8*B+12) :=
    le_mul_of_one_le_right (by positivity) (one_le_pow₀ hu1)
  have hA2 : 512*u^4*(12/Real.log Y + 2*((Y-1)^4)^2)
      ≤ 7168*u^(8*B+12) := by
    have hin : 12/Real.log Y + 2*((Y-1)^4)^2 ≤ 12 + 2*u^8 := by
      linarith [h12a, hy8]
    calc 512*u^4*(12/Real.log Y + 2*((Y-1)^4)^2)
        ≤ 512*u^4*(12 + 2*u^8) :=
          mul_le_mul_of_nonneg_left hin (by positivity)
      _ = 6144*u^4 + 1024*u^12 := by ring
      _ ≤ 6144*u^(8*B+12) + 1024*u^(8*B+12) := by
          have h1' := hupowP 4 (by omega)
          have h2' := hupowP 12 (by omega)
          linarith
      _ = 7168*u^(8*B+12) := by ring
  have hA3 : 1024*(u + 1)/((B:ℝ)*Real.log Y) ≤ 2048*u^(8*B+12) := by
    calc 1024*(u + 1)/((B:ℝ)*Real.log Y) ≤ 1024*(u + 1) :=
          div_le_self (by linarith) hBlogY1
      _ ≤ 2048*u := by linarith
      _ ≤ 2048*u^(8*B+12) := by
          have h := hupowP 1 (by omega)
          rw [pow_one] at h
          linarith
  have hA4 : 512*u^4*(12/((B:ℝ)*Real.log Y) + 2*((Y^B-1)^4)^2)
      ≤ 6144*u^(8*B+12) + 1024*u^(8*B+12) := by
    have hin : 12/((B:ℝ)*Real.log Y) + 2*((Y^B-1)^4)^2
        ≤ 12 + 2*u^(8*B) := by
      linarith [h12b, hyB8]
    calc 512*u^4*(12/((B:ℝ)*Real.log Y) + 2*((Y^B-1)^4)^2)
        ≤ 512*u^4*(12 + 2*u^(8*B)) :=
          mul_le_mul_of_nonneg_left hin (by positivity)
      _ = 6144*u^4 + 1024*u^(4+8*B) := by
          rw [pow_add]
          ring
      _ ≤ 6144*u^(8*B+12) + 1024*u^(8*B+12) := by
          have h1' := hupowP 4 (by omega)
          have h2' := hupowP (4+8*B) (by omega)
          linarith
  have hkey : (1024*Real.exp 12*(B:ℝ) + 20000)*u^(8*B+12)
      ≤ c₃*u^(8*B+12) := mul_le_mul_of_nonneg_right hc₃ hup
  have h1024 : (0:ℝ) ≤ 1024*Real.exp 12*(B:ℝ)*u^(8*B+12) := by positivity
  rw [hcanc2]
  linarith [hA1, hA2, hA3, hA4, hkey, h1024]

/-- **The head collapse** (Track R, M2-i4c2c): the scheduled head
exponential times the polynomial energy is again a single exponential,
at the tuned constant `W ≥ max (8B+22) (42 + log c₃)`. -/
theorem head_exp_le {B : ℕ} {c₃ W M u : ℝ} (hu1 : 1 ≤ u) (hc₃0 : 0 < c₃)
    (hW1 : 8*(B:ℝ) + 22 ≤ W) (hW2 : 42 + Real.log c₃ ≤ W) :
    Real.exp (10*Real.log u + 42 - M) * (c₃*u^(8*B+12))
      ≤ Real.exp (W*Real.log u + W - M) := by
  have hu0 : (0:ℝ) < u := by linarith
  have hllu0 : (0:ℝ) ≤ Real.log u := Real.log_nonneg hu1
  have hc₃exp : c₃ = Real.exp (Real.log c₃) := (Real.exp_log hc₃0).symm
  have hpowexp2 : u^(8*B+12) = Real.exp (((8*B+12 : ℕ):ℝ)*Real.log u) := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hu0 _)]
  calc Real.exp (10*Real.log u + 42 - M) * (c₃*u^(8*B+12))
      = Real.exp (10*Real.log u + 42 - M + Real.log c₃
          + ((8*B+12 : ℕ):ℝ)*Real.log u) := by
        rw [hc₃exp, hpowexp2, ← Real.exp_add, ← Real.exp_add]
        congr 1
        rw [Real.log_exp]
        ring
    _ ≤ Real.exp (W*Real.log u + W - M) := by
        refine Real.exp_le_exp.mpr ?_
        push_cast
        linarith [mul_le_mul_of_nonneg_right hW1 hllu0, hW2]

/-- **The tail-energy collapse** (Track R, M2-i4c2c): the Rankin edge
of the band factor times the polynomial energy, killed by
`e^{−u/2}`. -/
theorem tail_energy_le {B : ℕ} {c₃ ε u Y R : ℝ}
    (hYu : Y ≤ u) (hu0 : 0 < u) (hR : R ≤ Real.exp (-(u/2)))
    (hc₃0 : 0 ≤ c₃)
    (hK2 : c₃ * Real.exp (-(u/2) + 8*Real.sqrt u
      + (8*(B:ℝ)+12)*Real.log u) ≤ ε/8) :
    R * Real.exp (8*Real.sqrt Y) * (c₃*u^(8*B+12)) ≤ ε/8 := by
  have hsqmono : Real.sqrt Y ≤ Real.sqrt u := Real.sqrt_le_sqrt hYu
  have hpowexp3 : u^(8*B+12) = Real.exp ((8*(B:ℝ)+12)*Real.log u) := by
    rw [show (8*(B:ℝ)+12) = ((8*B+12 : ℕ):ℝ) from by push_cast; ring,
      ← Real.log_pow, Real.exp_log (pow_pos hu0 _)]
  calc R * Real.exp (8*Real.sqrt Y) * (c₃*u^(8*B+12))
      ≤ Real.exp (-(u/2)) * Real.exp (8*Real.sqrt u)
        * (c₃*Real.exp ((8*(B:ℝ)+12)*Real.log u)) := by
        rw [hpowexp3]
        refine mul_le_mul ?_ le_rfl (by positivity) (by positivity)
        refine mul_le_mul hR ?_ (Real.exp_pos _).le (Real.exp_pos _).le
        exact Real.exp_le_exp.mpr (by linarith)
    _ = c₃ * Real.exp (-(u/2) + 8*Real.sqrt u
          + (8*(B:ℝ)+12)*Real.log u) := by
        conv_rhs => rw [Real.exp_add, Real.exp_add]
        ring
    _ ≤ ε/8 := hK2

/-- **The window-tail collapse** (Track R, M2-i4c2c): the
`M₂/(2π|ξ|)²`-tail of the Perron window, at `ρ = ε/8` and `L = u⁴`,
is `O(1/u)` — the last term to vanish. -/
theorem window_tail_le {B : ℕ} {C ε u Y : ℝ} (hε : 0 < ε)
    (hBR : 1 ≤ (B:ℝ)) (hu1 : 1 ≤ u) (hlogY0 : 0 < Real.log Y)
    (hlogYu : Real.log Y ≤ u)
    (hT5 : Real.exp 24*(B:ℝ)*576*(C+1)^2/ε^2/u ≤ ε/8) :
    (Real.exp 12 * Real.log Y) * (Real.exp 12 * ((B:ℝ)*Real.log Y))
      * (u + 1) * (9*(C+1)^2/(ε/8)^2/(2*Real.pi^2*(u^4))) ≤ ε/8 := by
  have hu0 : (0:ℝ) < u := by linarith
  have hu4 : (0:ℝ) < u^4 := pow_pos hu0 4
  have hπ : (1:ℝ) ≤ Real.pi^2 := by
    have h3 : (3:ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
    calc (1:ℝ) ≤ 3^2 := by norm_num
      _ ≤ Real.pi^2 := pow_le_pow_left₀ (by norm_num) h3 2
  have hfr : 9*(C+1)^2/(ε/8)^2/(2*Real.pi^2*(u^4))
      ≤ 576*(C+1)^2/ε^2/(2*u^4) := by
    have h1 : 9*(C+1)^2/(ε/8)^2 = 576*(C+1)^2/ε^2 := by
      field_simp
      ring
    rw [h1]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    have h2 : (1:ℝ)*(u^4) ≤ Real.pi^2*(u^4) :=
      mul_le_mul_of_nonneg_right hπ hu4.le
    linarith [h2]
  have hfr0 : (0:ℝ) ≤ 9*(C+1)^2/(ε/8)^2/(2*Real.pi^2*(u^4)) := by
    positivity
  have hfac : (Real.exp 12 * Real.log Y)
      * (Real.exp 12 * ((B:ℝ)*Real.log Y)) * (u + 1)
      ≤ (Real.exp 12 * u) * (Real.exp 12 * ((B:ℝ)*u)) * (2*u) := by
    have e1 : Real.exp 12 * Real.log Y ≤ Real.exp 12 * u :=
      mul_le_mul_of_nonneg_left hlogYu (Real.exp_pos _).le
    have e2 : Real.exp 12 * ((B:ℝ)*Real.log Y)
        ≤ Real.exp 12 * ((B:ℝ)*u) := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left hlogYu (by linarith)
    have e3 : u + 1 ≤ 2*u := by linarith
    have p2 : (0:ℝ) ≤ Real.exp 12 * ((B:ℝ)*Real.log Y) :=
      mul_nonneg (Real.exp_pos _).le (by positivity)
    have p3 : (0:ℝ) ≤ Real.exp 12 * u := by positivity
    have p4 : (0:ℝ) ≤ Real.exp 12 * ((B:ℝ)*u) := by positivity
    exact mul_le_mul (mul_le_mul e1 e2 p2 p3) e3 (by linarith)
      (mul_nonneg p3 p4)
  calc (Real.exp 12 * Real.log Y)
        * (Real.exp 12 * ((B:ℝ)*Real.log Y)) * (u + 1)
        * (9*(C+1)^2/(ε/8)^2/(2*Real.pi^2*(u^4)))
      ≤ ((Real.exp 12 * u) * (Real.exp 12 * ((B:ℝ)*u)) * (2*u))
        * (576*(C+1)^2/ε^2/(2*u^4)) := by
        refine mul_le_mul hfac hfr hfr0 ?_
        positivity
    _ = Real.exp 24*(B:ℝ)*576*(C+1)^2/ε^2/u := by
        rw [show Real.exp 24 = Real.exp 12 * Real.exp 12 from by
          rw [← Real.exp_add]; norm_num]
        field_simp
    _ ≤ ε/8 := hT5

set_option maxHeartbeats 1600000 in
/-- **The cheap-Halász collapse** (Track R, M2-i4c2c): the five-term
tuned bound, at `ρ = ε/8` and `L = u⁴`, collapses to `ε` plus the
single head exponential — every term priced by one smallness
hypothesis (`hA`, `hK1`, `hK2`, `hX`, `hT5`, `hT2a`) supplied by the
threshold lemmas.  Stated over opaque reals (`u = log x`, `Y = y₂`,
`R = x^{−1/2}`, `X = x`) so no parameter can unfold. -/
theorem cheap_halasz_collapse (ε : ℝ) (hε : 0 < ε)
    (B : ℕ) (hB1 : 1 ≤ B) (C c₃ W M u Y R X : ℝ)
    (hY4 : 4 ≤ Y) (hYu : Y ≤ u) (hu5 : 5 ≤ u)
    (hR0 : 0 ≤ R) (hR : R ≤ Real.exp (-(u/2))) (hX : 2/X ≤ ε/8)
    (hc₃ : 1024*Real.exp 12*(B:ℝ) + 20000 ≤ c₃)
    (hW1 : 8*(B:ℝ) + 22 ≤ W) (hW2 : 42 + Real.log c₃ ≤ W)
    (hT2a : 2*Real.exp 12/(B:ℝ) ≤ ε/8)
    (hA : (1 + 8*(B:ℝ)*Real.log u)/u ≤ ε/8)
    (hK1 : (1:ℝ) * Real.exp (-(u/2) + 8*Real.sqrt u
      + 8*(B:ℝ)*Real.log u) ≤ ε/8)
    (hK2 : c₃ * Real.exp (-(u/2) + 8*Real.sqrt u
      + (8*(B:ℝ)+12)*Real.log u) ≤ ε/8)
    (hT5 : Real.exp 24*(B:ℝ)*576*(C+1)^2/ε^2/u ≤ ε/8) :
    (1 + 8*((B:ℝ)*Real.log Y))/u
      + (2*(Real.exp 12 * Real.log Y)/((B:ℝ)*Real.log Y)
        + R * Real.exp (8*Real.sqrt Y) * ((Y^B)^4)^2)
      + (2*(ε/8) + 2/X)
      + (Real.exp (10*Real.log u + 42 - M) + R * Real.exp (8*Real.sqrt Y))
        * ((1024*(Real.exp 12 * ((B:ℝ)*Real.log Y))/Real.log Y
            + 512*(u^4)*(12/Real.log Y + 2*((Y-1)^4)^2))
          + (1024*(u + 1)/((B:ℝ)*Real.log Y)
            + 512*(u^4)*(12/((B:ℝ)*Real.log Y) + 2*((Y^B-1)^4)^2)))/2
      + (Real.exp 12 * Real.log Y) * (Real.exp 12 * ((B:ℝ)*Real.log Y))
        * (u + 1) * (9*(C+1)^2/(ε/8)^2/(2*Real.pi^2*(u^4)))
      ≤ ε + Real.exp (W*Real.log u + W - M) := by
  have hBR : (1:ℝ) ≤ (B:ℝ) := by exact_mod_cast hB1
  have hu1 : (1:ℝ) ≤ u := by linarith
  have hu0 : (0:ℝ) < u := by linarith
  have hY1 : (1:ℝ) ≤ Y := by linarith
  have hY0 : (0:ℝ) < Y := by linarith
  have hlogY1 : (1:ℝ) ≤ Real.log Y := by
    rw [Real.le_log_iff_exp_le hY0]
    linarith [Real.exp_one_lt_d9]
  have hlogY0 : (0:ℝ) < Real.log Y := by linarith
  have hlogYu : Real.log Y ≤ Real.log u := Real.log_le_log hY0 hYu
  have hlogYu' : Real.log Y ≤ u := by
    linarith [Real.log_le_sub_one_of_pos hu0]
  have hBlogY1 : (1:ℝ) ≤ (B:ℝ)*Real.log Y := by nlinarith
  have hBlog0 : (0:ℝ) < (B:ℝ)*Real.log Y := by linarith
  have hexp12 : (0:ℝ) < Real.exp 12 * (B:ℝ) :=
    mul_pos (Real.exp_pos 12) (by linarith)
  have hc₃1 : (1:ℝ) ≤ c₃ := by linarith
  have hc₃0 : (0:ℝ) < c₃ := by linarith
  -- T1 : the Perron edge
  have hT1 : (1 + 8*((B:ℝ)*Real.log Y))/u ≤ ε/8 := by
    refine le_trans ?_ hA
    have hnum : 1 + 8*((B:ℝ)*Real.log Y) ≤ 1 + 8*(B:ℝ)*Real.log u := by
      linarith [mul_le_mul_of_nonneg_left hlogYu
        (by positivity : (0:ℝ) ≤ 8*(B:ℝ))]
    rw [div_le_div_iff₀ hu0 hu0]
    exact mul_le_mul_of_nonneg_right hnum hu0.le
  -- T2a : the medium-class count
  have hT2a' : 2*(Real.exp 12 * Real.log Y)/((B:ℝ)*Real.log Y) ≤ ε/8 := by
    have hcanc : 2*(Real.exp 12 * Real.log Y)/((B:ℝ)*Real.log Y)
        = 2*Real.exp 12/(B:ℝ) := by
      field_simp
    rw [hcanc]
    exact hT2a
  -- T2b : the Rankin remainder
  have hT2b := rankin_tail_collapse (B := B) (ε := ε) hY1 hYu hu0 hR hK1
  -- T4 : the band term
  have hT4 := prod_split_le (Real.exp_pos (10*Real.log u + 42 - M)).le
    (mul_nonneg hR0 (Real.exp_pos (8*Real.sqrt Y)).le)
    (energy_sum_le (B := B) (c₃ := c₃) hu1 hY1 hYu hlogY1 hBlogY1 hc₃)
    (head_exp_le (B := B) (W := W) (M := M) hu1 hc₃0 hW1 hW2)
    (tail_energy_le (B := B) (ε := ε) hYu hu0 hR hc₃0.le hK2)
  -- T5 : the window tail
  have hT5' := window_tail_le (B := B) (C := C) hε hBR hu1 hlogY0 hlogYu' hT5
  -- assembly : 6·(ε/8) + ε/4 = ε
  linarith [hT1, hT2a', hT2b, hX, hT4, hT5']

/-- From `⌈t⌉₊ + 1 ≤ x` to `t ≤ x`: the threshold-transfer step of the
cheap-Halász ε-form. -/
theorem le_of_ceil_succ_le {t : ℝ} {x : ℕ} (h : ⌈t⌉₊ + 1 ≤ x) :
    t ≤ (x:ℝ) := by
  have h1 : ((⌈t⌉₊ : ℕ):ℝ) ≤ (x:ℝ) := by
    exact_mod_cast (by omega : ⌈t⌉₊ ≤ x)
  linarith [Nat.le_ceil t]

set_option maxHeartbeats 1600000 in
/-- **The cheap Halász theorem, ε-form** (Track R, M2-i4c2): for every
`ε > 0` there are a threshold `x₀` and a constant `W > 0`, uniform in
`f` and `M`, such that every `1`-bounded completely multiplicative `f`
whose pretentious distance to each archimedean twist `n^{2πiξ}`,
`|ξ| ≤ (log x)⁴`, is at least `M` at scale `x ≥ x₀` satisfies
`‖∑_{n ≤ x} f(n)‖/x ≤ ε + e^{W loglog x + W − M}`. -/
theorem cheap_halasz_eps (ε : ℝ) (hε : 0 < ε) :
    ∃ (x₀ : ℕ) (W : ℝ), 0 < W ∧
      ∀ x : ℕ, x₀ ≤ x → ∀ f : ℕ → ℂ, CompletelyMultiplicativeC f →
        f 1 = 1 → (∀ n, ‖f n‖ ≤ 1) → ∀ M : ℝ,
        (∀ ξ : ℝ, |ξ| ≤ (Real.log x)^4 → M ≤ pretentiousDistSq f
          (fun n => (n:ℂ)^(Complex.I*((2*Real.pi*ξ : ℝ):ℂ))) x) →
        ‖∑ n ∈ Finset.Icc 1 x, f n‖/(x:ℝ)
          ≤ ε + Real.exp (W*Real.log (Real.log x) + W - M) := by
  classical
  by_cases hε1 : 1 < ε
  · -- trivial regime: the mean never exceeds `1`
    refine ⟨1, 1, by norm_num, ?_⟩
    intro x hx f hcm h1 hb M hM
    have hx0 : (0:ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    have htriv : ‖∑ n ∈ Finset.Icc 1 x, f n‖ ≤ (x:ℝ) := by
      refine le_trans (norm_sum_le _ _) ?_
      calc ∑ n ∈ Finset.Icc 1 x, ‖f n‖
          ≤ ∑ _n ∈ Finset.Icc 1 x, (1:ℝ) :=
            Finset.sum_le_sum fun n _ => hb n
        _ = ((Finset.Icc 1 x).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ = (x:ℝ) := by
            rw [Nat.card_Icc, Nat.add_sub_cancel]
    have hexp0 : (0:ℝ) < Real.exp (1*Real.log (Real.log x) + 1 - M) :=
      Real.exp_pos _
    rw [div_le_iff₀ hx0]
    nlinarith [htriv, hexp0, hx0]
  · push_neg at hε1
    obtain ⟨σ, C, hσs, hσ01, hσ0, hσ1, hC0, hC1, hC2⟩ :=
      exists_master_transition
    -- the cut exponent
    obtain ⟨B, hB1, hT2a⟩ :
        ∃ B : ℕ, 1 ≤ B ∧ 2*Real.exp 12/(B:ℝ) ≤ ε/8 := by
      refine ⟨⌈(16:ℝ)*Real.exp 12/ε⌉₊ + 1, by omega, ?_⟩
      have hceil : (16:ℝ)*Real.exp 12/ε
          ≤ ((⌈(16:ℝ)*Real.exp 12/ε⌉₊ + 1 : ℕ):ℝ) := by
        push_cast
        linarith [Nat.le_ceil ((16:ℝ)*Real.exp 12/ε)]
      have hb0 : (0:ℝ) < 16*Real.exp 12/ε := by positivity
      have hbpos : (0:ℝ) < ((⌈(16:ℝ)*Real.exp 12/ε⌉₊ + 1 : ℕ):ℝ) :=
        lt_of_lt_of_le hb0 hceil
      rw [div_le_div_iff₀ hbpos (by norm_num : (0:ℝ) < 8)]
      have hmul := mul_le_mul_of_nonneg_left hceil hε.le
      have hcanc : ε*(16*Real.exp 12/ε) = 16*Real.exp 12 := by
        field_simp
      nlinarith [hmul, hcanc]
    have hBR : (1:ℝ) ≤ (B:ℝ) := by exact_mod_cast hB1
    -- the energy constant and the head constant
    obtain ⟨c₃, hc₃⟩ :
        ∃ c₃ : ℝ, c₃ = 1024*Real.exp 12*(B:ℝ) + 20000 := ⟨_, rfl⟩
    have hexp12 : (0:ℝ) < Real.exp 12 * (B:ℝ) :=
      mul_pos (Real.exp_pos 12) (by linarith)
    have hc₃1 : (1:ℝ) ≤ c₃ := by rw [hc₃]; nlinarith [hexp12]
    have hlogc₃0 : (0:ℝ) ≤ Real.log c₃ := Real.log_nonneg hc₃1
    obtain ⟨W, hW0, hW1, hW2⟩ :
        ∃ W : ℝ, 0 < W ∧ 8*(B:ℝ) + 22 ≤ W ∧ 42 + Real.log c₃ ≤ W :=
      ⟨8*(B:ℝ) + 64 + Real.log c₃, by nlinarith, by nlinarith, by nlinarith⟩
    -- the window constant
    obtain ⟨c₅, hc₅⟩ :
        ∃ c₅ : ℝ, c₅ = Real.exp 24*(B:ℝ)*576*(C+1)^2/ε^2 := ⟨_, rfl⟩
    have hc₅0 : (0:ℝ) ≤ c₅ := by rw [hc₅]; positivity
    -- one scale threshold for all five collapses
    obtain ⟨v, hvA, hvB1, hvB2, hvT5, hv5⟩ :
        ∃ v : ℝ, max 1 ((2*(1+2*(8*(B:ℝ)))/(ε/8))^2) ≤ v
          ∧ max (max 4096 (256*((8*(B:ℝ))+1)^2))
              (4*Real.log (((1:ℝ)+1)/(ε/8)) + 1) ≤ v
          ∧ max (max 4096 (256*((8*(B:ℝ)+12)+1)^2))
              (4*Real.log ((c₃+1)/(ε/8)) + 1) ≤ v
          ∧ 8*c₅/ε ≤ v ∧ (5:ℝ) ≤ v :=
      ⟨max (max (max (max 1 ((2*(1+2*(8*(B:ℝ)))/(ε/8))^2))
            (max (max 4096 (256*((8*(B:ℝ))+1)^2))
              (4*Real.log (((1:ℝ)+1)/(ε/8)) + 1)))
          (max (max (max 4096 (256*((8*(B:ℝ)+12)+1)^2))
              (4*Real.log ((c₃+1)/(ε/8)) + 1)) (8*c₅/ε))) 5,
        le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
          (le_max_left _ _),
        le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
          (le_max_left _ _),
        le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
          (le_max_left _ _),
        le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
          (le_max_left _ _),
        le_max_right _ _⟩
    -- the scale threshold
    refine ⟨max (max (⌈Real.exp v⌉₊ + 1) (⌈(16:ℝ)/ε⌉₊ + 1))
      (⌈((2*(B:ℝ))^B)^2⌉₊ + 1), W, hW0, ?_⟩
    intro x hxx₀ f hcm h1 hb M hM
    have hxv : Real.exp v ≤ (x:ℝ) := le_of_ceil_succ_le (by omega)
    have hx16 : (16:ℝ)/ε ≤ (x:ℝ) := le_of_ceil_succ_le (by omega)
    have hxD : ((2*(B:ℝ))^B)^2 ≤ (x:ℝ) := le_of_ceil_succ_le (by omega)
    have hx1 : 1 ≤ x := by omega
    have hx0R : (0:ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    have hxR1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx1
    have hv : v ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le hx0R]
      exact hxv
    have hu5 : (5:ℝ) ≤ Real.log x := le_trans hv5 hv
    have hu1 : (1:ℝ) ≤ Real.log x := by linarith
    have hu0 : (0:ℝ) < Real.log x := by linarith
    -- the small cut
    have hy₂4 : 4 ≤ ⌊Real.log x⌋₊ := Nat.le_floor (by exact_mod_cast (by
      linarith : (4:ℝ) ≤ Real.log x))
    have hy₂u : ((⌊Real.log x⌋₊ : ℕ):ℝ) ≤ Real.log x := Nat.floor_le hu0.le
    have hy₂4R : (4:ℝ) ≤ ((⌊Real.log x⌋₊ : ℕ):ℝ) := by exact_mod_cast hy₂4
    have hupow : (Real.log x)^B ≤ (x:ℝ) :=
      log_pow_le_self hB1 (x:ℝ) (max_le hxR1 hxD)
    have hy₂B : (⌊Real.log x⌋₊)^B ≤ x := by
      have hcast : (((⌊Real.log x⌋₊)^B : ℕ):ℝ) ≤ (x:ℝ) := by
        push_cast
        calc ((⌊Real.log x⌋₊ : ℕ):ℝ)^B ≤ (Real.log x)^B :=
              pow_le_pow_left₀ (by linarith) hy₂u B
          _ ≤ (x:ℝ) := hupow
      exact_mod_cast hcast
    have hx4 : 4 ≤ x := by
      have h6 : (6:ℝ) ≤ Real.exp v := by
        linarith [Real.add_one_le_exp v]
      have hx6 : (6:ℝ) ≤ (x:ℝ) := le_trans h6 hxv
      exact_mod_cast le_trans (by norm_num : (4:ℝ) ≤ 6) hx6
    -- the tuned bound
    have htuned := cheap_halasz_tuned f hcm h1 hb σ C hσs hσ01 hσ0 hσ1
      hC0 hC1 hC2 x (⌊Real.log x⌋₊) B hy₂4 hB1 hy₂B hx4 (ε/8)
      ((Real.log x)^4) M (by positivity) (by linarith)
      (one_le_pow₀ hu1) hM
    refine le_trans htuned ?_
    -- the five collapses
    have hA := one_add_log_div_le (show (0:ℝ) < ε/8 by positivity)
      (show (0:ℝ) ≤ 8*(B:ℝ) by positivity) (Real.log x) (le_trans hvA hv)
    have hK1 := exp_neg_half_kill (show (0:ℝ) < ε/8 by positivity)
      (by norm_num : (0:ℝ) ≤ 1) (show (0:ℝ) ≤ 8*(B:ℝ) by positivity)
      (Real.log x) (le_trans hvB1 hv)
    have hK2 := exp_neg_half_kill (show (0:ℝ) < ε/8 by positivity)
      (by linarith : (0:ℝ) ≤ c₃) (show (0:ℝ) ≤ 8*(B:ℝ)+12 by positivity)
      (Real.log x) (le_trans hvB2 hv)
    have hT5 : Real.exp 24*(B:ℝ)*576*(C+1)^2/ε^2/Real.log x ≤ ε/8 := by
      rw [← hc₅, div_le_iff₀ hu0]
      have h8 : 8*c₅/ε ≤ Real.log x := le_trans hvT5 hv
      rw [div_le_iff₀ hε] at h8
      nlinarith [h8]
    have hR : (x:ℝ)^(-(1/2:ℝ)) = Real.exp (-(Real.log x/2)) := by
      rw [Real.rpow_def_of_pos hx0R]
      congr 1
      ring
    have hX : 2/(x:ℝ) ≤ ε/8 := by
      rw [div_le_iff₀ hx0R]
      have hm : ε/8 * ((16:ℝ)/ε) ≤ ε/8 * (x:ℝ) :=
        mul_le_mul_of_nonneg_left hx16 (by positivity)
      have hcalc : ε/8 * ((16:ℝ)/ε) = 2 := by
        field_simp
        norm_num
      linarith
    exact cheap_halasz_collapse ε hε B hB1 C c₃ W M (Real.log x)
      ((⌊Real.log x⌋₊ : ℕ):ℝ) ((x:ℝ)^(-(1/2:ℝ))) (x:ℝ) hy₂4R hy₂u hu5
      (by positivity) (le_of_eq hR) hX (le_of_eq hc₃.symm) hW1 hW2 hT2a
      hA hK1 hK2 hT5

/-- **Level-one twists are archimedean** (Track R, M2-j): modulo `1`
every Dirichlet character is trivial, so `charTwist 1 χ t` is the bare
twist `n ↦ n^{it}` — the bridge between the `NonPretentiousAt`
character-twist family and the archimedean band hypothesis of the
cheap Halász theorem. -/
theorem charTwist_level_one (χ : DirichletCharacter ℂ 1) (t : ℝ) (m : ℕ) :
    charTwist 1 χ t m = (m:ℂ)^(Complex.I*(t:ℂ)) := by
  simp only [charTwist, Subsingleton.elim ((m : ℕ) : ZMod 1) 1, map_one,
    one_mul]

/-- **The band radius fits the scale** (Track R, M2-j): once
`x ≥ e⁸` and `(log x)⁵ ≤ x`, the frequency radius `2π(log x)⁴` of the
cheap-Halász band is below `x`, so it is inside every
`NonPretentiousAt`-range `|t| ≤ A·x` with `A ≥ 1`. -/
theorem two_pi_log_pow_le_self {x : ℝ} (hx : Real.exp 8 ≤ x)
    (h5 : (Real.log x)^5 ≤ x) : 2*Real.pi*(Real.log x)^4 ≤ x := by
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le (Real.exp_pos 8) hx
  have hlog8 : (8:ℝ) ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    exact hx
  have hπ : 2*Real.pi ≤ 8 := by
    linarith [Real.pi_le_four]
  have hp4 : (0:ℝ) ≤ (Real.log x)^4 := by positivity
  calc 2*Real.pi*(Real.log x)^4 ≤ 8*(Real.log x)^4 :=
        mul_le_mul_of_nonneg_right hπ hp4
    _ ≤ Real.log x*(Real.log x)^4 :=
        mul_le_mul_of_nonneg_right hlog8 hp4
    _ = (Real.log x)^5 := by ring
    _ ≤ x := h5

set_option maxHeartbeats 800000 in
/-- **The cheap Halász theorem under non-pretentiousness** (Track R,
M2-j): the twist-uniform corollary.  A `1`-bounded completely
multiplicative `g` that is `A`-non-pretentious at scale `x` — no
Dirichlet twist `χ(n)n^{it}` with `q ≤ A`, `|t| ≤ A·x` comes within
squared pretentious distance `A` — has Cesàro mean at most
`ε + e^{W loglog x + W − A}`.  The band hypothesis of
`cheap_halasz_eps` is the `q = 1` slice of `NonPretentiousAt`, and its
frequency radius `2π(log x)⁴` fits inside `A·x` for `x ≥ x₀`. -/
theorem cheap_halasz_nonpretentious (ε : ℝ) (hε : 0 < ε) :
    ∃ (x₀ : ℕ) (W : ℝ), 0 < W ∧
      ∀ x : ℕ, x₀ ≤ x → ∀ A : ℝ, 1 ≤ A → ∀ g : ℕ → ℂ,
        CompletelyMultiplicativeC g → g 1 = 1 → (∀ n, ‖g n‖ ≤ 1) →
        NonPretentiousAt g A x →
        ‖∑ n ∈ Finset.Icc 1 x, g n‖/(x:ℝ)
          ≤ ε + Real.exp (W*Real.log (Real.log x) + W - A) := by
  obtain ⟨x₁, W, hW0, hmain⟩ := cheap_halasz_eps ε hε
  refine ⟨max x₁ (max (⌈Real.exp 8⌉₊ + 1) (⌈((2*(5:ℝ))^5)^2⌉₊ + 1)), W,
    hW0, ?_⟩
  intro x hx A hA g hcm h1 hb hnp
  have hx1 : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hexp8 : Real.exp 8 ≤ (x:ℝ) := le_of_ceil_succ_le (by omega)
  have hxD : ((2*(5:ℝ))^5)^2 ≤ (x:ℝ) := le_of_ceil_succ_le (by omega)
  have hx0R : (0:ℝ) < (x:ℝ) := lt_of_lt_of_le (Real.exp_pos 8) hexp8
  have hxR1 : (1:ℝ) ≤ (x:ℝ) := by
    have h1' : (1:ℝ) ≤ Real.exp 8 := by
      linarith [Real.add_one_le_exp (8:ℝ)]
    linarith
  have h5 : (Real.log x)^5 ≤ (x:ℝ) :=
    log_pow_le_self (by norm_num) (x:ℝ) (max_le hxR1 hxD)
  have hrange : 2*Real.pi*(Real.log x)^4 ≤ (x:ℝ) :=
    two_pi_log_pow_le_self hexp8 h5
  refine hmain x hx1 g hcm h1 hb A ?_
  intro ξ hξ
  have hq : ((1:ℕ):ℝ) ≤ A := by exact_mod_cast hA
  have ht : |2*Real.pi*ξ| ≤ A*(x:ℝ) := by
    have habs : |2*Real.pi*ξ| = 2*Real.pi*|ξ| := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)]
    have hmono : 2*Real.pi*|ξ| ≤ 2*Real.pi*(Real.log x)^4 :=
      mul_le_mul_of_nonneg_left hξ (by positivity)
    have hAx : (x:ℝ) ≤ A*(x:ℝ) := by nlinarith [hx0R, hA]
    rw [habs]
    linarith
  have hnp' := hnp 1 (1 : DirichletCharacter ℂ 1) (2*Real.pi*ξ) hq ht
  have heq : charTwist 1 (1 : DirichletCharacter ℂ 1) (2*Real.pi*ξ)
      = fun n : ℕ => (n:ℂ)^(Complex.I*((2*Real.pi*ξ : ℝ):ℂ)) :=
    funext (charTwist_level_one _ _)
  rw [heq] at hnp'
  exact hnp'

end MoltResearch
