import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.BigOperators

/-!
# Discrepancy: the `φ(r')`-normalized principal Euler factor is `1 + O(log(dr')/L)`

κ-calculus step for the Tao 2015 §4 analysis (arXiv:1509.05363,
`Problems/tao2015_derivation_c.md`, issue #2907): with `σ = 1 + 1/L` (in the paper
`L = log X`), the scaled principal Euler factor

`κ = (d·r') · d^{−σ} · φ(r')⁻¹ · ∏_{p ∣ r'} (1 − p^{−σ})`

satisfies `|κ − 1| ≤ 2·log(d·r')/L` as soon as `2 ≤ L` and `2·log(d·r') ≤ L`
(`abs_scaled_euler_prod_sub_one_le`).

Route: by Euler's product formula for the totient (`Nat.totient_eq_mul_prod_factors`),
`κ = d^{−1/L} · ∏_{p ∣ r'} (1 − p^{−σ})/(1 − p^{−1})` (`scaled_euler_eq`).

* **Lower bound**: every ratio is `≥ 1` (`p^{−σ} ≤ p^{−1}`), and
  `d^{−1/L} = exp(−log d/L) ≥ 1 − log d/L` (`Real.add_one_le_exp`).
* **Upper bound**: `d^{−1/L} ≤ 1`, and each ratio is `≤ 1 + log p/L`
  (from `1 − e^{−y} ≤ y` at `y = log p/L`, and `p^{−1} ≤ 1 − p^{−1}` for `p ≥ 2`), so
  the product is at most `exp(∑_{p ∣ r'} log p/L) = exp(log(∏_{p ∣ r'} p)/L)
  ≤ exp(log r'/L)` (the radical divides `r'`), and `e^x ≤ 1/(1−x) ≤ 1 + 2x` on
  `[0, 1/2]` finishes.

Consumer: the `hkappa` hypothesis of the residue-class equidistribution step in the
Track C Stage 5 (jock)→(contra) chain
(`Conjectures/C0002_erdos_discrepancy/src/TrackCStage5JockChain.lean`).

This module is deliberately dependency-light: it imports only Mathlib (no MoltResearch
modules), and is intended to be used via the stable surface `MoltResearch.Discrepancy`.
-/

namespace MoltResearch

open Finset

/-- For `p ≥ 2` the Euler factor `1 − 1/p` is at least `1/2` (in particular positive). -/
private lemma half_le_one_sub_inv {p : ℕ} (hp : 2 ≤ p) : (1 : ℝ) / 2 ≤ 1 - 1 / (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  linarith

/-- Monotonicity in the exponent: for `p ≥ 2` and `σ ≥ 1`, `1 − 1/p ≤ 1 − 1/p^σ`. -/
private lemma one_sub_inv_le_one_sub_inv_rpow {p : ℕ} (hp : 2 ≤ p) {σ : ℝ} (hσ : 1 ≤ σ) :
    1 - 1 / (p : ℝ) ≤ 1 - 1 / (p : ℝ) ^ σ := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.one_le_of_lt hp
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le one_pos hp1
  have hpow : (p : ℝ) ≤ (p : ℝ) ^ σ := by
    calc (p : ℝ) = (p : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (p : ℝ) ^ σ := Real.rpow_le_rpow_of_exponent_le hp1 hσ
  have h := one_div_le_one_div_of_le hp0 hpow
  linarith

/-- Per-prime κ-factor bound: for `p ≥ 2` and `L > 0`,
`1 − 1/p^{1+1/L} ≤ (1 − 1/p)·(1 + log p/L)`.

From `1/p^{1+1/L} = (1/p)·e^{−y}` at `y = log p/L`, the tangent-line bound
`1 − e^{−y} ≤ y`, and `1/p ≤ 1 − 1/p` for `p ≥ 2`. -/
private lemma one_sub_inv_rpow_le {p : ℕ} (hp : 2 ≤ p) {L : ℝ} (hL : 0 < L) :
    1 - 1 / (p : ℝ) ^ (1 + 1 / L) ≤ (1 - 1 / (p : ℝ)) * (1 + Real.log p / L) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.one_le_of_lt hp
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le one_pos hp1
  have hy0 : 0 ≤ Real.log p / L := div_nonneg (Real.log_nonneg hp1) hL.le
  have hpow : (p : ℝ) ^ (1 + 1 / L) = (p : ℝ) * Real.exp (Real.log p / L) := by
    rw [Real.rpow_add hp0, Real.rpow_one, Real.rpow_def_of_pos hp0, mul_one_div]
  have hinv : 1 / (p : ℝ) ^ (1 + 1 / L) = (1 / (p : ℝ)) * Real.exp (-(Real.log p / L)) := by
    rw [hpow, Real.exp_neg, one_div, mul_inv, one_div]
  rw [hinv]
  have hexp : 1 - Real.log p / L ≤ Real.exp (-(Real.log p / L)) := by
    have h := Real.add_one_le_exp (-(Real.log p / L)); linarith
  have hhalf : 1 / (p : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp)
  have hq0 : (0 : ℝ) < 1 / (p : ℝ) := by positivity
  have h1 : (1 / (p : ℝ)) * (1 - Real.log p / L)
      ≤ (1 / (p : ℝ)) * Real.exp (-(Real.log p / L)) :=
    mul_le_mul_of_nonneg_left hexp hq0.le
  nlinarith [mul_nonneg hy0 (by linarith : (0 : ℝ) ≤ 1 - 2 * (1 / (p : ℝ)))]

/-- `e^x ≤ 1 + 2x` on `[0, 1/2]`, via `e^x ≤ 1/(1−x) ≤ 1 + 2x`. -/
private lemma exp_le_one_add_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp x ≤ 1 + 2 * x := by
  have hx1 : (0 : ℝ) < 1 - x := by linarith
  have hE : Real.exp x * (1 - x) ≤ 1 := by
    have h := Real.add_one_le_exp (-x)
    have h2 := mul_le_mul_of_nonneg_left h (Real.exp_pos x).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, neg_add_eq_sub] at h2
    exact h2
  have h1 : Real.exp x ≤ 1 / (1 - x) := by rw [le_div_iff₀ hx1]; exact hE
  have h2 : 1 / (1 - x) ≤ 1 + 2 * x := by
    rw [div_le_iff₀ hx1]
    nlinarith [mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ 1 - 2 * x)]
  linarith

/-- The product of the per-prime gains over the prime factors of `r'` is controlled by
the radical: `∏_{p ∣ r'} (1 + log p/L) ≤ exp(log r'/L)`. -/
private lemma prod_one_add_log_div_le_exp {r' : ℕ} (hr' : 1 ≤ r') {L : ℝ} (hL : 0 < L) :
    ∏ p ∈ r'.primeFactors, (1 + Real.log p / L) ≤ Real.exp (Real.log r' / L) := by
  have h1 : ∏ p ∈ r'.primeFactors, (1 + Real.log p / L)
      ≤ ∏ p ∈ r'.primeFactors, Real.exp (Real.log p / L) := by
    refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
    · have h0 : (0 : ℝ) ≤ Real.log p := Real.log_nonneg
        (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
      positivity
    · have h := Real.add_one_le_exp (Real.log p / L); linarith
  rw [← Real.exp_sum] at h1
  refine h1.trans (Real.exp_le_exp.mpr ?_)
  have hne : ∀ p ∈ r'.primeFactors, ((p : ℝ)) ≠ 0 := fun p hp =>
    Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hsum : ∑ p ∈ r'.primeFactors, Real.log p ≤ Real.log r' := by
    rw [← Real.log_prod hne, ← Nat.cast_prod]
    have hle : (∏ p ∈ r'.primeFactors, p) ≤ r' :=
      Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd r')
    have hpos : 0 < ∏ p ∈ r'.primeFactors, p :=
      Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
    exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)
  calc ∑ p ∈ r'.primeFactors, Real.log p / L
      = (∑ p ∈ r'.primeFactors, Real.log p) / L := by
        simp [div_eq_mul_inv, ← Finset.sum_mul]
    _ ≤ Real.log r' / L := by
        rw [div_le_div_iff₀ hL hL]
        exact mul_le_mul_of_nonneg_right hsum hL.le

/-- Euler-product form of the scaled principal factor: the `κ` of the paper is
`d^{−1/L}` times the product of the per-prime ratios `(1 − p^{−σ})/(1 − p^{−1})`. -/
private lemma scaled_euler_eq {d r' : ℕ} (hd : 1 ≤ d) (hr' : 1 ≤ r') {L : ℝ}
    (hL0 : 0 < L) :
    ((d : ℝ) * (r' : ℝ))
        * ((1 / (d : ℝ) ^ (1 + 1 / L)) * (1 / (r'.totient : ℝ))
            * ∏ p ∈ r'.primeFactors, (1 - 1 / (p : ℝ) ^ (1 + 1 / L)))
      = (1 / (d : ℝ) ^ (1 / L : ℝ))
          * ∏ p ∈ r'.primeFactors,
              ((1 - 1 / (p : ℝ) ^ (1 + 1 / L)) / (1 - 1 / (p : ℝ))) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hr'0 : (0 : ℝ) < (r' : ℝ) := Nat.cast_pos.mpr (by omega)
  have hprime : ∀ p ∈ r'.primeFactors, 2 ≤ p := fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).two_le
  have hfac0 : ∀ p ∈ r'.primeFactors, (0 : ℝ) < 1 - 1 / (p : ℝ) := fun p hp => by
    have := half_le_one_sub_inv (hprime p hp); linarith
  have hP0 : (0 : ℝ) < ∏ p ∈ r'.primeFactors, (1 - 1 / (p : ℝ)) :=
    Finset.prod_pos hfac0
  -- Euler's product formula for the totient, over `ℝ`.
  have htot : (r'.totient : ℝ) = (r' : ℝ) * ∏ p ∈ r'.primeFactors, (1 - 1 / (p : ℝ)) := by
    have h : ((r'.totient : ℚ) : ℝ)
        = (((r' : ℚ) * ∏ p ∈ r'.primeFactors, (1 - (p : ℚ)⁻¹) : ℚ) : ℝ) :=
      congrArg _ (Nat.totient_eq_mul_prod_factors r')
    push_cast at h
    simpa [one_div] using h
  -- Split off the `(1 − 1/p)` factors from the numerator product.
  have hA : ∏ p ∈ r'.primeFactors, (1 - 1 / (p : ℝ) ^ (1 + 1 / L))
      = (∏ p ∈ r'.primeFactors, ((1 - 1 / (p : ℝ) ^ (1 + 1 / L)) / (1 - 1 / (p : ℝ))))
          * ∏ p ∈ r'.primeFactors, (1 - 1 / (p : ℝ)) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p hp => (div_mul_cancel₀ _ (hfac0 p hp).ne').symm
  have hdpow : (d : ℝ) ^ (1 + 1 / L) = (d : ℝ) * (d : ℝ) ^ (1 / L : ℝ) := by
    rw [Real.rpow_add hd0, Real.rpow_one]
  have hdL0 : (0 : ℝ) < (d : ℝ) ^ (1 / L : ℝ) := Real.rpow_pos_of_pos hd0 _
  rw [htot, hA, hdpow]
  have h1 : (d : ℝ) ≠ 0 := hd0.ne'
  have h2 : (r' : ℝ) ≠ 0 := hr'0.ne'
  have h3 : (∏ p ∈ r'.primeFactors, (1 - 1 / (p : ℝ))) ≠ 0 := hP0.ne'
  have h4 : (d : ℝ) ^ (1 / L : ℝ) ≠ 0 := hdL0.ne'
  field_simp

/-- **The `φ(r')`-normalized principal Euler factor is `1 + O(log(dr')/L)`**
(Tao 2015 §4, the κ-calculus): with `σ = 1 + 1/L`,

`|(d·r')·d^{−σ}·φ(r')⁻¹·∏_{p ∣ r'}(1 − p^{−σ}) − 1| ≤ 2·log(d·r')/L`

whenever `d, r' ≥ 1`, `2 ≤ L`, and `2·log(d·r') ≤ L`.  This discharges the `hkappa`
hypothesis of the residue-class equidistribution step in the (jock)→(contra) chain. -/
theorem abs_scaled_euler_prod_sub_one_le {d r' : ℕ} (hd : 1 ≤ d) (hr' : 1 ≤ r')
    {L : ℝ} (hL2 : 2 ≤ L) (hLr : 2 * Real.log ((d : ℝ) * (r' : ℝ)) ≤ L) :
    |((d : ℝ) * (r' : ℝ))
        * ((1 / (d : ℝ) ^ (1 + 1 / L)) * (1 / (r'.totient : ℝ))
            * ∏ p ∈ r'.primeFactors, (1 - 1 / (p : ℝ) ^ (1 + 1 / L))) - 1|
      ≤ 2 * Real.log ((d : ℝ) * (r' : ℝ)) / L := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hr'1 : (1 : ℝ) ≤ (r' : ℝ) := by exact_mod_cast hr'
  have hd0 : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le one_pos hd1
  have hr'0 : (0 : ℝ) < (r' : ℝ) := lt_of_lt_of_le one_pos hr'1
  have hdr1 : (1 : ℝ) ≤ (d : ℝ) * (r' : ℝ) := by nlinarith
  have hlogdr : 0 ≤ Real.log ((d : ℝ) * (r' : ℝ)) := Real.log_nonneg hdr1
  have hlogd : Real.log (d : ℝ) ≤ Real.log ((d : ℝ) * (r' : ℝ)) :=
    Real.log_le_log hd0 (by nlinarith)
  have hlogr' : Real.log (r' : ℝ) ≤ Real.log ((d : ℝ) * (r' : ℝ)) :=
    Real.log_le_log hr'0 (by nlinarith)
  have hprime : ∀ p ∈ r'.primeFactors, 2 ≤ p := fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).two_le
  have hfac0 : ∀ p ∈ r'.primeFactors, (0 : ℝ) < 1 - 1 / (p : ℝ) := fun p hp => by
    have := half_le_one_sub_inv (hprime p hp); linarith
  have hσ1 : (1 : ℝ) ≤ 1 + 1 / L := le_add_of_nonneg_right (by positivity)
  -- Bounds on the ratio product `R`.
  have hR1 : (1 : ℝ) ≤ ∏ p ∈ r'.primeFactors,
      ((1 - 1 / (p : ℝ) ^ (1 + 1 / L)) / (1 - 1 / (p : ℝ))) := by
    calc (1 : ℝ) = ∏ _p ∈ r'.primeFactors, (1 : ℝ) := by rw [Finset.prod_const_one]
      _ ≤ _ := by
          refine Finset.prod_le_prod₀ (fun p hp => zero_le_one) fun p hp => ?_
          rw [one_le_div (hfac0 p hp)]
          exact one_sub_inv_le_one_sub_inv_rpow (hprime p hp) hσ1
  have hRup : ∏ p ∈ r'.primeFactors,
        ((1 - 1 / (p : ℝ) ^ (1 + 1 / L)) / (1 - 1 / (p : ℝ)))
      ≤ 1 + 2 * (Real.log (r' : ℝ) / L) := by
    have hstep : ∏ p ∈ r'.primeFactors,
          ((1 - 1 / (p : ℝ) ^ (1 + 1 / L)) / (1 - 1 / (p : ℝ)))
        ≤ ∏ p ∈ r'.primeFactors, (1 + Real.log p / L) := by
      refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
      · refine div_nonneg ?_ (hfac0 p hp).le
        have h := (half_le_one_sub_inv (hprime p hp)).trans
          (one_sub_inv_le_one_sub_inv_rpow (hprime p hp) hσ1)
        linarith
      · rw [div_le_iff₀ (hfac0 p hp)]
        exact (one_sub_inv_rpow_le (hprime p hp) hL0).trans_eq (mul_comm _ _)
    refine hstep.trans ((prod_one_add_log_div_le_exp hr' hL0).trans ?_)
    have hx0 : 0 ≤ Real.log (r' : ℝ) / L := div_nonneg (Real.log_nonneg hr'1) hL0.le
    have hx : Real.log (r' : ℝ) / L ≤ 1 / 2 := by
      rw [div_le_iff₀ hL0]; linarith
    have := exp_le_one_add_two_mul hx0 hx
    linarith
  -- Bounds on the archimedean-free part `d^{−1/L}`.
  have hdinv_low : (1 : ℝ) - Real.log (d : ℝ) / L ≤ 1 / (d : ℝ) ^ (1 / L : ℝ) := by
    rw [one_div, ← Real.rpow_neg hd0.le, Real.rpow_def_of_pos hd0]
    have harg : Real.log (d : ℝ) * -(1 / L) = -(Real.log (d : ℝ) / L) := by ring
    rw [harg]
    have h := Real.add_one_le_exp (-(Real.log (d : ℝ) / L))
    linarith
  have hdinv_up : 1 / (d : ℝ) ^ (1 / L : ℝ) ≤ 1 := by
    rw [one_div, ← Real.rpow_neg hd0.le]
    exact Real.rpow_le_one_of_one_le_of_nonpos hd1 (neg_nonpos.mpr (by positivity))
  have hdinv0 : (0 : ℝ) ≤ 1 / (d : ℝ) ^ (1 / L : ℝ) := by positivity
  rw [scaled_euler_eq hd hr' hL0, abs_le]
  constructor
  · -- Lower bound: `κ ≥ d^{−1/L} ≥ 1 − log d/L ≥ 1 − 2·log(dr')/L`.
    have h1 : (1 - Real.log (d : ℝ) / L) * 1
        ≤ (1 / (d : ℝ) ^ (1 / L : ℝ)) * ∏ p ∈ r'.primeFactors,
            ((1 - 1 / (p : ℝ) ^ (1 + 1 / L)) / (1 - 1 / (p : ℝ))) :=
      mul_le_mul hdinv_low hR1 zero_le_one hdinv0
    have hkey : Real.log (d : ℝ) / L ≤ 2 * Real.log ((d : ℝ) * (r' : ℝ)) / L := by
      rw [div_le_div_iff₀ hL0 hL0]
      exact mul_le_mul_of_nonneg_right (by linarith) hL0.le
    linarith
  · -- Upper bound: `κ ≤ R ≤ 1 + 2·log r'/L ≤ 1 + 2·log(dr')/L`.
    have hR0 : (0 : ℝ) ≤ ∏ p ∈ r'.primeFactors,
        ((1 - 1 / (p : ℝ) ^ (1 + 1 / L)) / (1 - 1 / (p : ℝ))) := by linarith
    have h1 : (1 / (d : ℝ) ^ (1 / L : ℝ)) * ∏ p ∈ r'.primeFactors,
          ((1 - 1 / (p : ℝ) ^ (1 + 1 / L)) / (1 - 1 / (p : ℝ)))
        ≤ 1 * ∏ p ∈ r'.primeFactors,
            ((1 - 1 / (p : ℝ) ^ (1 + 1 / L)) / (1 - 1 / (p : ℝ))) :=
      mul_le_mul_of_nonneg_right hdinv_up hR0
    have hkey : 2 * (Real.log (r' : ℝ) / L) ≤ 2 * Real.log ((d : ℝ) * (r' : ℝ)) / L := by
      rw [mul_div_assoc]
      have h' : Real.log (r' : ℝ) / L ≤ Real.log ((d : ℝ) * (r' : ℝ)) / L := by
        rw [div_le_div_iff₀ hL0 hL0]
        exact mul_le_mul_of_nonneg_right hlogr' hL0.le
      linarith
    linarith

end MoltResearch
