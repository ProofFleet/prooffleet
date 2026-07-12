import MoltResearch.Discrepancy.AdditiveCharCancellation
import Mathlib.Analysis.Fourier.ZMod

/-!
# Discrepancy: perfect cancellation for primitive-character cutoffs (Tao 2015 §4, eq. (perf))

Nucleus module for the Tao 2015 §4 analysis (arXiv:1509.05363, issue #2871, PR I2): the
**Granville perfect cancellation**, paper equation (perf). For a primitive Dirichlet character
`χ` mod `q > 1` and *distinct* divisors `d₁ ≠ d₂` of `q^{k-1}`, the two arithmetic cutoffs
`a ↦ 1_{d₁ ∣ a+m₁}·χ((a+m₁)/d₁)` and `a ↦ 1_{d₂ ∣ a+m₂}·χ((a+m₂)/d₂)` are *exactly*
orthogonal over a full period `a ∈ [0, q^k)`:

`∑_{a < q^k} 1_{d₁ ∣ a+m₁}·χ((a+m₁)/d₁) · conj(1_{d₂ ∣ a+m₂}·χ((a+m₂)/d₂)) = 0`

("if `d₁ ≠ d₂`, then the frequencies involved here are distinct", Tao 2015 §4). Layers:

* `stdAddChar_natCast` — `e(j/q)` bookkeeping for natural arguments.
* `natCast_mul_char_apply_eq_sum` — Fourier inversion for a primitive character:
  `q·χ(x) = ∑_u χ⁻¹(−u)·τ(χ)·e(ux/q)`, from the `ZMod.dft` inversion together with
  `DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`; the coefficients are
  supported on units `u` (`MulChar.map_nonunit`), which drives all coprimality downstream.
* `sum_range_exp_intCast_mul_eq_ite` — the divisor indicator as a full additive-character
  block: `∑_{v<d} e(nv/d) = d·1_{d ∣ n}`.
* `mul_ite_dvd_char_eq_sum` / `mul_conj_ite_dvd_char_eq_sum` — the combined Granville
  expansion of one cutoff: `dq·1_{d∣n}·χ(n/d) = ∑_u ∑_{v<d} χ⁻¹(−u)·τ(χ)·e((u.val+vq)·n/(dq))`
  (and its complex conjugate).
* `isCoprime_val_add_mul` — the combined frequencies `u.val + vq` are coprime to `dq` for
  unit `u`: every prime of `d ∣ q^{k-1}` divides `q`.
* `sum_exp_shifted_mul_conj_exp_eq_zero` — the inner `a`-average of one cross-frequency pair
  vanishes, by factoring out the constant phase and invoking
  `sum_exp_sub_eq_zero_of_divisor_ne` (the elementary (perf) core).
* `sum_indicator_char_mul_conj_eq_zero` — the assembled eq. (perf): expand both cutoffs,
  interchange the finite sums, and kill every cross term.
-/

namespace MoltResearch

open Finset

section StdAddCharFacts

variable {q : ℕ} [NeZero q]

/-- The standard additive character of `ZMod q` at a natural argument, as an explicit
exponential: `e(j/q) = exp(2πi·j/q)` (Tao 2015 §4 bookkeeping). -/
theorem stdAddChar_natCast (j : ℕ) :
    ZMod.stdAddChar ((j : ℕ) : ZMod q)
      = Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) / (q : ℂ)) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_natCast]

/-- **Fourier inversion for a primitive Dirichlet character** (Tao 2015 §4, toward eq. (perf)):
`q·χ(x) = ∑_u χ⁻¹(−u)·τ(χ)·e(ux/q)`. The coefficient `χ⁻¹(−u)` vanishes off the units of
`ZMod q`, which is what makes the combined Granville frequencies coprime to the modulus. -/
theorem natCast_mul_char_apply_eq_sum {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (x : ZMod q) :
    (q : ℂ) * χ x
      = ∑ u : ZMod q,
          χ⁻¹ (-u) * gaussSum χ ZMod.stdAddChar * ZMod.stdAddChar (u * x) := by
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have h1 := ZMod.invDFT_apply (ZMod.dft (⇑χ : ZMod q → ℂ)) x
  rw [LinearEquiv.symm_apply_apply] at h1
  rw [h1, smul_eq_mul, mul_inv_cancel_left₀ hq']
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [smul_eq_mul, hχ.fourierTransform_eq_inv_mul_gaussSum u]
  ring

end StdAddCharFacts

/-- **Divisor indicator as a full additive-character block** (Tao 2015 §4, toward eq. (perf)):
`∑_{v<d} e(nv/d) = d` if `d ∣ n` and `0` otherwise. -/
theorem sum_range_exp_intCast_mul_eq_ite {d : ℕ} (hd : d ≠ 0) (n : ℕ) :
    ∑ v ∈ Finset.range d,
        Complex.exp (2 * Real.pi * Complex.I * ((n : ℤ) : ℂ) * (v : ℂ) / (d : ℂ))
      = if d ∣ n then (d : ℂ) else 0 := by
  have hd' : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  by_cases hdn : d ∣ n
  · rw [if_pos hdn]
    obtain ⟨t, rfl⟩ := hdn
    have h1 : ∀ v ∈ Finset.range d,
        Complex.exp (2 * Real.pi * Complex.I * (((d * t : ℕ) : ℤ) : ℂ) * (v : ℂ) / (d : ℂ))
          = 1 := by
      intro v _
      have harg : 2 * Real.pi * Complex.I * (((d * t : ℕ) : ℤ) : ℂ) * (v : ℂ) / (d : ℂ)
          = (((t * v : ℕ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast
        field_simp
      rw [harg, Complex.exp_int_mul_two_pi_mul_I]
    trans (∑ _v ∈ Finset.range d, (1 : ℂ))
    · exact Finset.sum_congr rfl h1
    · simp
  · rw [if_neg hdn]
    have hξ : ¬((d : ℤ) ∣ ((n : ℕ) : ℤ)) := by exact_mod_cast hdn
    exact sum_exp_two_pi_mul_eq_zero hd hξ

/-- Complex conjugation flips the sign of a purely imaginary exponent `2πi·ξ·n/M`. -/
private lemma conj_exp_nat_frac (ξ n M : ℕ) :
    (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (n : ℂ) / (M : ℂ)))
      = Complex.exp (-(2 * Real.pi * Complex.I * (ξ : ℂ) * (n : ℂ) / (M : ℂ))) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]
  ring

section GranvilleExpansion

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- **Granville expansion of a single cutoff** (Tao 2015 §4, toward eq. (perf)): for a
primitive `χ` mod `q` and `d ≠ 0`,

`dq · 1_{d ∣ n} · χ(n/d) = ∑_{u mod q} ∑_{v < d} χ⁻¹(−u)·τ(χ)·e((u.val + vq)·n/(dq))`.

The divisor indicator and the character are jointly expanded into additive characters at the
combined frequencies `u.val + vq`, whose coefficients are supported on units `u`. -/
theorem mul_ite_dvd_char_eq_sum (hχ : χ.IsPrimitive) {d : ℕ} (hd : d ≠ 0) (n : ℕ) :
    ((d : ℂ) * q) * (if d ∣ n then χ ((n / d : ℕ) : ZMod q) else 0)
      = ∑ u : ZMod q, ∑ v ∈ Finset.range d,
          χ⁻¹ (-u) * gaussSum χ ZMod.stdAddChar
            * Complex.exp (2 * Real.pi * Complex.I * ((ZMod.val u + v * q : ℕ) : ℂ) * (n : ℂ)
                / ((d * q : ℕ) : ℂ)) := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have hd' : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq0
  -- split each combined exponential into its `u`-part and its `v`-part
  have hsplit : ∀ (u : ZMod q) (v : ℕ),
      Complex.exp (2 * Real.pi * Complex.I * ((ZMod.val u + v * q : ℕ) : ℂ) * (n : ℂ)
          / ((d * q : ℕ) : ℂ))
        = Complex.exp (2 * Real.pi * Complex.I * ((ZMod.val u * n : ℕ) : ℂ)
            / ((d * q : ℕ) : ℂ))
          * Complex.exp (2 * Real.pi * Complex.I * ((n : ℤ) : ℂ) * (v : ℂ) / (d : ℂ)) := by
    intro u v
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp
  -- collapse the inner `v`-sum into the divisor indicator
  have hv : ∀ u : ZMod q,
      (∑ v ∈ Finset.range d, χ⁻¹ (-u) * gaussSum χ ZMod.stdAddChar
          * Complex.exp (2 * Real.pi * Complex.I * ((ZMod.val u + v * q : ℕ) : ℂ) * (n : ℂ)
              / ((d * q : ℕ) : ℂ)))
        = (χ⁻¹ (-u) * gaussSum χ ZMod.stdAddChar
            * Complex.exp (2 * Real.pi * Complex.I * ((ZMod.val u * n : ℕ) : ℂ)
                / ((d * q : ℕ) : ℂ)))
          * (if d ∣ n then (d : ℂ) else 0) := by
    intro u
    rw [← sum_range_exp_intCast_mul_eq_ite hd n, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hsplit u v]
    ring
  rw [Finset.sum_congr rfl fun u _ => hv u]
  by_cases hdn : d ∣ n
  · simp only [if_pos hdn]
    -- rewrite the `u`-part exponential as the additive character at `u * (n/d)`
    have hE : ∀ u : ZMod q,
        Complex.exp (2 * Real.pi * Complex.I * ((ZMod.val u * n : ℕ) : ℂ) / ((d * q : ℕ) : ℂ))
          = ZMod.stdAddChar (u * ((n / d : ℕ) : ZMod q)) := by
      intro u
      have hu : u * ((n / d : ℕ) : ZMod q) = ((ZMod.val u * (n / d) : ℕ) : ZMod q) := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val]
      rw [hu, stdAddChar_natCast]
      congr 1
      obtain ⟨t, rfl⟩ := hdn
      rw [Nat.mul_div_cancel_left t (Nat.pos_of_ne_zero hd)]
      push_cast
      field_simp
    calc ((d : ℂ) * q) * χ ((n / d : ℕ) : ZMod q)
        = ((q : ℂ) * χ ((n / d : ℕ) : ZMod q)) * d := by ring
      _ = (∑ u : ZMod q, χ⁻¹ (-u) * gaussSum χ ZMod.stdAddChar
            * ZMod.stdAddChar (u * ((n / d : ℕ) : ZMod q))) * d := by
          rw [natCast_mul_char_apply_eq_sum hχ]
      _ = ∑ u : ZMod q, (χ⁻¹ (-u) * gaussSum χ ZMod.stdAddChar
            * Complex.exp (2 * Real.pi * Complex.I * ((ZMod.val u * n : ℕ) : ℂ)
                / ((d * q : ℕ) : ℂ))) * (d : ℂ) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [hE u]
  · simp only [if_neg hdn, mul_zero, Finset.sum_const_zero]

/-- Conjugated form of `mul_ite_dvd_char_eq_sum`, with the exponentials at negated
frequencies (Tao 2015 §4, the `conj` factor of eq. (perf)). -/
theorem mul_conj_ite_dvd_char_eq_sum (hχ : χ.IsPrimitive) {d : ℕ} (hd : d ≠ 0) (n : ℕ) :
    ((d : ℂ) * q) * (starRingEnd ℂ) (if d ∣ n then χ ((n / d : ℕ) : ZMod q) else 0)
      = ∑ u : ZMod q, ∑ v ∈ Finset.range d,
          (starRingEnd ℂ) (χ⁻¹ (-u) * gaussSum χ ZMod.stdAddChar)
            * Complex.exp (-(2 * Real.pi * Complex.I * ((ZMod.val u + v * q : ℕ) : ℂ) * (n : ℂ)
                / ((d * q : ℕ) : ℂ))) := by
  have h0 : ((d : ℂ) * q) * (starRingEnd ℂ) (if d ∣ n then χ ((n / d : ℕ) : ZMod q) else 0)
      = (starRingEnd ℂ) (((d : ℂ) * q) * (if d ∣ n then χ ((n / d : ℕ) : ZMod q) else 0)) := by
    rw [map_mul, map_mul, map_natCast (starRingEnd ℂ) d, map_natCast (starRingEnd ℂ) q]
  rw [h0, mul_ite_dvd_char_eq_sum hχ hd n, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_mul]
  congr 1
  exact conj_exp_nat_frac _ _ _

end GranvilleExpansion

/-- **Coprimality of the combined Granville frequencies** (Tao 2015 §4): for a unit
`u mod q` and `d ∣ q^{k-1}`, the combined frequency `u.val + vq` is coprime to `dq`
(every prime of `d` divides `q`). -/
theorem isCoprime_val_add_mul {q k : ℕ} {d : ℕ} (hdvd : d ∣ q ^ (k - 1))
    {u : ZMod q} (hu : IsUnit u) (v : ℕ) :
    IsCoprime ((ZMod.val u + v * q : ℕ) : ℤ) ((d * q : ℕ) : ℤ) := by
  rw [Nat.isCoprime_iff_coprime]
  have hval : Nat.Coprime (ZMod.val u) q := by
    obtain ⟨w, rfl⟩ := hu
    exact ZMod.val_coe_unit_coprime w
  have h1 : Nat.Coprime (ZMod.val u + v * q) q :=
    (Nat.coprime_add_mul_right_left (ZMod.val u) q v).mpr hval
  have h2 : Nat.Coprime (ZMod.val u + v * q) d :=
    Nat.Coprime.coprime_dvd_right hdvd (h1.pow_right (k - 1))
  exact h2.mul_right h1

/-- **Vanishing of one cross-frequency pair** (Tao 2015 §4, eq. (perf) inner average): for
`d₁ ≠ d₂` dividing `q^{k-1}` and frequencies `ξᵢ` coprime to `dᵢq`, the full-period average
of `e(ξ₁(a+m₁)/(d₁q))·e(−ξ₂(a+m₂)/(d₂q))` vanishes: the constant phases factor out and the
remaining pure two-frequency average is `sum_exp_sub_eq_zero_of_divisor_ne`. -/
theorem sum_exp_shifted_mul_conj_exp_eq_zero {q k : ℕ} (hq : 1 < q) (hk : 1 ≤ k)
    {d₁ d₂ : ℕ} (h₁ : d₁ ∣ q ^ (k - 1)) (h₂ : d₂ ∣ q ^ (k - 1)) (hne : d₁ ≠ d₂)
    {ξ₁ ξ₂ : ℕ} (hcop₁ : IsCoprime ((ξ₁ : ℕ) : ℤ) ((d₁ * q : ℕ) : ℤ))
    (hcop₂ : IsCoprime ((ξ₂ : ℕ) : ℤ) ((d₂ * q : ℕ) : ℤ)) (m₁ m₂ : ℕ) :
    ∑ a ∈ Finset.range (q ^ k),
        Complex.exp (2 * Real.pi * Complex.I * (ξ₁ : ℂ) * ((a + m₁ : ℕ) : ℂ)
            / ((d₁ * q : ℕ) : ℂ))
          * Complex.exp (-(2 * Real.pi * Complex.I * (ξ₂ : ℂ) * ((a + m₂ : ℕ) : ℂ)
            / ((d₂ * q : ℕ) : ℂ)))
      = 0 := by
  have hq0 : q ≠ 0 := by omega
  have hd₁0 : d₁ ≠ 0 := ne_zero_of_dvd_ne_zero (pow_ne_zero _ hq0) h₁
  have hd₂0 : d₂ ≠ 0 := ne_zero_of_dvd_ne_zero (pow_ne_zero _ hq0) h₂
  have hd₁' : (d₁ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd₁0
  have hd₂' : (d₂ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd₂0
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq0
  have hcop₁' : IsCoprime ((ξ₁ : ℤ)) ((d₁ : ℤ) * (q : ℤ)) := by
    push_cast at hcop₁
    exact hcop₁
  have hcop₂' : IsCoprime ((ξ₂ : ℤ)) ((d₂ : ℤ) * (q : ℤ)) := by
    push_cast at hcop₂
    exact hcop₂
  have key : ∀ a : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * (ξ₁ : ℂ) * ((a + m₁ : ℕ) : ℂ)
          / ((d₁ * q : ℕ) : ℂ))
        * Complex.exp (-(2 * Real.pi * Complex.I * (ξ₂ : ℂ) * ((a + m₂ : ℕ) : ℂ)
          / ((d₂ * q : ℕ) : ℂ)))
      = (Complex.exp (2 * Real.pi * Complex.I * (ξ₁ : ℂ) * (m₁ : ℂ) / ((d₁ * q : ℕ) : ℂ))
          * Complex.exp (-(2 * Real.pi * Complex.I * (ξ₂ : ℂ) * (m₂ : ℂ)
            / ((d₂ * q : ℕ) : ℂ))))
        * Complex.exp (2 * Real.pi * Complex.I
            * (((ξ₁ : ℤ) : ℂ) * (a : ℂ) / ((d₁ * q : ℕ) : ℂ)
              - ((ξ₂ : ℤ) : ℂ) * (a : ℂ) / ((d₂ * q : ℕ) : ℂ))) := by
    intro a
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  calc ∑ a ∈ Finset.range (q ^ k),
        Complex.exp (2 * Real.pi * Complex.I * (ξ₁ : ℂ) * ((a + m₁ : ℕ) : ℂ)
            / ((d₁ * q : ℕ) : ℂ))
          * Complex.exp (-(2 * Real.pi * Complex.I * (ξ₂ : ℂ) * ((a + m₂ : ℕ) : ℂ)
            / ((d₂ * q : ℕ) : ℂ)))
      = ∑ a ∈ Finset.range (q ^ k),
          (Complex.exp (2 * Real.pi * Complex.I * (ξ₁ : ℂ) * (m₁ : ℂ) / ((d₁ * q : ℕ) : ℂ))
              * Complex.exp (-(2 * Real.pi * Complex.I * (ξ₂ : ℂ) * (m₂ : ℂ)
                / ((d₂ * q : ℕ) : ℂ))))
            * Complex.exp (2 * Real.pi * Complex.I
                * (((ξ₁ : ℤ) : ℂ) * (a : ℂ) / ((d₁ * q : ℕ) : ℂ)
                  - ((ξ₂ : ℤ) : ℂ) * (a : ℂ) / ((d₂ * q : ℕ) : ℂ))) :=
        Finset.sum_congr rfl fun a _ => key a
    _ = (Complex.exp (2 * Real.pi * Complex.I * (ξ₁ : ℂ) * (m₁ : ℂ) / ((d₁ * q : ℕ) : ℂ))
            * Complex.exp (-(2 * Real.pi * Complex.I * (ξ₂ : ℂ) * (m₂ : ℂ)
              / ((d₂ * q : ℕ) : ℂ))))
          * ∑ a ∈ Finset.range (q ^ k),
              Complex.exp (2 * Real.pi * Complex.I
                * (((ξ₁ : ℤ) : ℂ) * (a : ℂ) / ((d₁ * q : ℕ) : ℂ)
                  - ((ξ₂ : ℤ) : ℂ) * (a : ℂ) / ((d₂ * q : ℕ) : ℂ))) := by
        rw [Finset.mul_sum]
    _ = 0 := by
        rw [sum_exp_sub_eq_zero_of_divisor_ne hq hk h₁ h₂ hne hcop₁' hcop₂', mul_zero]

/-- **Perfect cancellation** (Tao 2015 §4, eq. (perf); Granville's argument): for a
*primitive* Dirichlet character `χ` mod `q > 1` and *distinct* `d₁ ≠ d₂` dividing `q^{k-1}`,
the two cutoffs `1_{dᵢ ∣ a+mᵢ}·χ((a+mᵢ)/dᵢ)` are exactly orthogonal over a full period
`a ∈ [0, q^k)`. Expand both factors by `mul_ite_dvd_char_eq_sum` /
`mul_conj_ite_dvd_char_eq_sum`; each cross term carries frequencies coprime to `d₁q` resp.
`d₂q` (`isCoprime_val_add_mul`), so its full-period average vanishes
(`sum_exp_shifted_mul_conj_exp_eq_zero`) — "the frequencies involved here are distinct". -/
theorem sum_indicator_char_mul_conj_eq_zero {q k : ℕ} (hq : 1 < q) (hk : 1 ≤ k)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {d₁ d₂ : ℕ} (h₁ : d₁ ∣ q ^ (k - 1)) (h₂ : d₂ ∣ q ^ (k - 1)) (hne : d₁ ≠ d₂)
    (m₁ m₂ : ℕ) :
    ∑ a ∈ Finset.range (q ^ k),
        (if d₁ ∣ (a + m₁) then χ (((a + m₁) / d₁ : ℕ) : ZMod q) else 0)
      * (starRingEnd ℂ) (if d₂ ∣ (a + m₂) then χ (((a + m₂) / d₂ : ℕ) : ZMod q) else 0)
      = 0 := by
  haveI : NeZero q := ⟨by omega⟩
  have hq0 : q ≠ 0 := by omega
  have hd₁0 : d₁ ≠ 0 := ne_zero_of_dvd_ne_zero (pow_ne_zero _ hq0) h₁
  have hd₂0 : d₂ ≠ 0 := ne_zero_of_dvd_ne_zero (pow_ne_zero _ hq0) h₂
  have hscale : (((d₁ : ℂ) * q) * ((d₂ : ℂ) * q)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr hd₁0) (Nat.cast_ne_zero.mpr hq0))
      (mul_ne_zero (Nat.cast_ne_zero.mpr hd₂0) (Nat.cast_ne_zero.mpr hq0))
  -- it suffices to kill the sum scaled by the nonzero factor `(d₁q)·(d₂q)`
  have main : (((d₁ : ℂ) * q) * ((d₂ : ℂ) * q))
      * (∑ a ∈ Finset.range (q ^ k),
          (if d₁ ∣ (a + m₁) then χ (((a + m₁) / d₁ : ℕ) : ZMod q) else 0)
        * (starRingEnd ℂ) (if d₂ ∣ (a + m₂) then χ (((a + m₂) / d₂ : ℕ) : ZMod q) else 0))
      = 0 := by
    rw [Finset.mul_sum]
    have hterm : ∀ a ∈ Finset.range (q ^ k),
        (((d₁ : ℂ) * q) * ((d₂ : ℂ) * q))
            * ((if d₁ ∣ (a + m₁) then χ (((a + m₁) / d₁ : ℕ) : ZMod q) else 0)
              * (starRingEnd ℂ) (if d₂ ∣ (a + m₂) then χ (((a + m₂) / d₂ : ℕ) : ZMod q) else 0))
          = (∑ u : ZMod q, ∑ v ∈ Finset.range d₁,
              χ⁻¹ (-u) * gaussSum χ ZMod.stdAddChar
                * Complex.exp (2 * Real.pi * Complex.I * ((ZMod.val u + v * q : ℕ) : ℂ)
                    * ((a + m₁ : ℕ) : ℂ) / ((d₁ * q : ℕ) : ℂ)))
            * (∑ u : ZMod q, ∑ v ∈ Finset.range d₂,
              (starRingEnd ℂ) (χ⁻¹ (-u) * gaussSum χ ZMod.stdAddChar)
                * Complex.exp (-(2 * Real.pi * Complex.I * ((ZMod.val u + v * q : ℕ) : ℂ)
                    * ((a + m₂ : ℕ) : ℂ) / ((d₂ * q : ℕ) : ℂ)))) := by
      intro a _
      rw [show (((d₁ : ℂ) * q) * ((d₂ : ℂ) * q))
            * ((if d₁ ∣ (a + m₁) then χ (((a + m₁) / d₁ : ℕ) : ZMod q) else 0)
              * (starRingEnd ℂ) (if d₂ ∣ (a + m₂) then χ (((a + m₂) / d₂ : ℕ) : ZMod q) else 0))
          = (((d₁ : ℂ) * q) * (if d₁ ∣ (a + m₁) then χ (((a + m₁) / d₁ : ℕ) : ZMod q) else 0))
            * (((d₂ : ℂ) * q)
              * (starRingEnd ℂ)
                  (if d₂ ∣ (a + m₂) then χ (((a + m₂) / d₂ : ℕ) : ZMod q) else 0)) from by
        ring]
      rw [mul_ite_dvd_char_eq_sum hχ hd₁0 (a + m₁),
        mul_conj_ite_dvd_char_eq_sum hχ hd₂0 (a + m₂)]
    rw [Finset.sum_congr rfl hterm]
    -- expand the product of the two double sums and pull the `a`-average innermost
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun u₂ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun v₂ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun u₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun v₁ _ => ?_
    -- one cross term: coefficients vanish off units, and for units the average is zero
    by_cases hu₁ : IsUnit u₁
    · by_cases hu₂ : IsUnit u₂
      · have hcop₁ := isCoprime_val_add_mul h₁ hu₁ v₁
        have hcop₂ := isCoprime_val_add_mul h₂ hu₂ v₂
        have hzero := sum_exp_shifted_mul_conj_exp_eq_zero hq hk h₁ h₂ hne hcop₁ hcop₂ m₁ m₂
        calc ∑ a ∈ Finset.range (q ^ k),
              (χ⁻¹ (-u₁) * gaussSum χ ZMod.stdAddChar
                  * Complex.exp (2 * Real.pi * Complex.I * ((ZMod.val u₁ + v₁ * q : ℕ) : ℂ)
                      * ((a + m₁ : ℕ) : ℂ) / ((d₁ * q : ℕ) : ℂ)))
                * ((starRingEnd ℂ) (χ⁻¹ (-u₂) * gaussSum χ ZMod.stdAddChar)
                  * Complex.exp (-(2 * Real.pi * Complex.I * ((ZMod.val u₂ + v₂ * q : ℕ) : ℂ)
                      * ((a + m₂ : ℕ) : ℂ) / ((d₂ * q : ℕ) : ℂ))))
            = (χ⁻¹ (-u₁) * gaussSum χ ZMod.stdAddChar
                * (starRingEnd ℂ) (χ⁻¹ (-u₂) * gaussSum χ ZMod.stdAddChar))
              * ∑ a ∈ Finset.range (q ^ k),
                  Complex.exp (2 * Real.pi * Complex.I * ((ZMod.val u₁ + v₁ * q : ℕ) : ℂ)
                      * ((a + m₁ : ℕ) : ℂ) / ((d₁ * q : ℕ) : ℂ))
                    * Complex.exp (-(2 * Real.pi * Complex.I * ((ZMod.val u₂ + v₂ * q : ℕ) : ℂ)
                      * ((a + m₂ : ℕ) : ℂ) / ((d₂ * q : ℕ) : ℂ))) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun a _ => by ring
          _ = 0 := by rw [hzero, mul_zero]
      · have h0 : χ⁻¹ (-u₂) = 0 :=
          MulChar.map_nonunit _ (fun h => hu₂ (by simpa using h.neg))
        refine Finset.sum_eq_zero fun a _ => ?_
        rw [h0, zero_mul, map_zero, zero_mul, mul_zero]
    · have h0 : χ⁻¹ (-u₁) = 0 :=
        MulChar.map_nonunit _ (fun h => hu₁ (by simpa using h.neg))
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [h0, zero_mul, zero_mul, zero_mul]
  rcases mul_eq_zero.mp main with h | h
  · exact absurd h hscale
  · exact h

end MoltResearch
