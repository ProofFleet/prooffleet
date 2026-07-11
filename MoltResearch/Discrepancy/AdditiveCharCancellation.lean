import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Discrepancy: additive-character cancellation (Granville perfect cancellation, elementary core)

Nucleus module for the Tao 2015 §4 analysis (arXiv:1509.05363, issue #2871, PR I prep):
the elementary additive core of the **perfect cancellation** (paper eq. (perf)) in
Granville's argument. There, two Fourier expansions of cutoffs to residue classes mod
`d₁ q` and `d₂ q` (with `d₁, d₂ ∣ q^{k-1}`, `d₁ ≠ d₂`) are multiplied and averaged over a
full period `a ∈ [0, q^k)`; the off-diagonal terms vanish *exactly* because the two
expansions live at distinct frequencies — "if `d₁ ≠ d₂`, then the frequencies involved
here are distinct" (Tao 2015 §4).

Layers, bottom-up:
* `sum_zmod_unit_pow_eq_zero` — a nontrivial `M`-th root of unity sums to zero over a
  full period (geometric series).
* `sum_exp_two_pi_mul_eq_zero` — the additive-character form: `∑_{a<M} e(ξa/M) = 0`
  when `M ∤ ξ`.
* `sum_exp_sub_eq_zero` — the two-frequency orthogonality that eq. (perf) reduces to:
  `∑_{a<M} e(ξ₁a/d₁ − ξ₂a/d₂) = 0` when the combined frequency
  `ξ₁·(M/d₁) − ξ₂·(M/d₂)` is nonzero mod `M`.
* `freq_ne_of_divisor_ne` — the frequency-distinctness arithmetic: for `d₁ ≠ d₂` both
  dividing `q^{k-1}` and `ξᵢ` coprime to `dᵢq`, the combined frequency is *not*
  divisible by `q^k`. Elementary divisibility proof (no valuations): from
  `q^k ∣ ξ₁e₁ − ξ₂e₂` (`eᵢ = q^{k-1}/dᵢ`), multiplying by `d₁` and using
  `gcd(ξ₂, q^{k-1}) = 1` forces `d₂ ∣ d₁`, and symmetrically `d₁ ∣ d₂`.
* `sum_exp_sub_eq_zero_of_divisor_ne` — the assembled eq. (perf) core: the full-period
  average of `e(ξ₁a/(d₁q) − ξ₂a/(d₂q))` vanishes outright when `d₁ ≠ d₂`.

For the full eq. (perf) one also needs the primitive-character Fourier expansion; the
Mathlib support (recorded here for the PR I assembly) is:
`ZMod.stdAddChar` / `ZMod.stdAddChar_coe` (`Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar`),
`ZMod.dft` + inversion `ZMod.dft_dft` (`Mathlib.Analysis.Fourier.ZMod`), and crucially
`DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`
(`𝓕 χ k = χ⁻¹(−k)·τ(χ)`, same file), backed by
`DirichletCharacter.gaussSum_mulShift_of_isPrimitive`
(`Mathlib.NumberTheory.DirichletCharacter.GaussSum`) and
`gaussSum_mul_gaussSum_eq_card` (`Mathlib.NumberTheory.GaussSum`).
-/

namespace MoltResearch

open Finset

set_option linter.unusedVariables false in
/-- **Roots-of-unity cancellation** (Tao 2015 §4, toward eq. (perf)): a nontrivial
`M`-th root of unity sums to zero over a full period. The hypothesis `hM` is not needed
by the proof (for `M = 0` the sum is empty) but is kept for interface parity with the
downstream (perf) assembly. -/
theorem sum_zmod_unit_pow_eq_zero {M : ℕ} (hM : M ≠ 0) {ζ : ℂ} (hζ : ζ ^ M = 1)
    (hζ1 : ζ ≠ 1) : ∑ a ∈ Finset.range M, ζ ^ a = 0 := by
  rw [geom_sum_eq hζ1, hζ, sub_self, zero_div]

/-- **Additive-character orthogonality** (Tao 2015 §4, eq. (perf) input): the sum of
`e(ξa/M) = exp(2πiξa/M)` over a full period `a ∈ [0, M)` vanishes whenever the frequency
`ξ` is not divisible by `M`. -/
theorem sum_exp_two_pi_mul_eq_zero {M : ℕ} (hM : M ≠ 0) {ξ : ℤ} (hξ : ¬((M : ℤ) ∣ ξ)) :
    ∑ a ∈ Finset.range M, Complex.exp (2 * Real.pi * Complex.I * ξ * a / M) = 0 := by
  have hM' : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  -- `ζ = e(ξ/M)` is an `M`-th root of unity …
  have hζM : Complex.exp (2 * Real.pi * Complex.I * ξ / M) ^ M = 1 := by
    rw [← Complex.exp_nat_mul]
    refine Complex.exp_eq_one_iff.mpr ⟨ξ, ?_⟩
    field_simp
  -- … and a nontrivial one: `e(ξ/M) = 1` would force `M ∣ ξ`.
  have hζ1 : Complex.exp (2 * Real.pi * Complex.I * ξ / M) ≠ 1 := by
    intro h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
    rw [div_eq_iff hM'] at hn
    refine hξ ⟨n, ?_⟩
    have hℂ : (ξ : ℂ) = ((M * n : ℤ) : ℂ) := by
      refine mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_
      push_cast
      rw [hn]
      ring
    exact_mod_cast hℂ
  calc ∑ a ∈ Finset.range M, Complex.exp (2 * Real.pi * Complex.I * ξ * a / M)
      = ∑ a ∈ Finset.range M, Complex.exp (2 * Real.pi * Complex.I * ξ / M) ^ a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Complex.exp_nat_mul]
        congr 1
        ring
    _ = 0 := sum_zmod_unit_pow_eq_zero hM hζM hζ1

/-- **Two-frequency perfect cancellation** (Tao 2015 §4, eq. (perf)): the average of
`e(ξ₁a/d₁ − ξ₂a/d₂)` over a full period `a ∈ [0, M)` (with `d₁, d₂ ∣ M`) vanishes as
soon as the combined frequency `ξ₁·(M/d₁) − ξ₂·(M/d₂)` is nonzero mod `M`. This is the
orthogonality to which the off-diagonal terms of Granville's expansion reduce. -/
theorem sum_exp_sub_eq_zero {M : ℕ} (hM : M ≠ 0) {ξ₁ ξ₂ : ℤ} {d₁ d₂ : ℕ}
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) (hdvd₁ : d₁ ∣ M) (hdvd₂ : d₂ ∣ M)
    (hfreq : ¬((M : ℤ) ∣ (ξ₁ * (M / d₁ : ℕ) - ξ₂ * (M / d₂ : ℕ)))) :
    ∑ a ∈ Finset.range M,
      Complex.exp (2 * Real.pi * Complex.I * (ξ₁ * a / d₁ - ξ₂ * a / d₂)) = 0 := by
  have hM' : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have hd₁' : (d₁ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd₁
  have hd₂' : (d₂ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd₂
  have hc₁ : ((M / d₁ : ℕ) : ℂ) = (M : ℂ) / (d₁ : ℂ) := Nat.cast_div hdvd₁ hd₁'
  have hc₂ : ((M / d₂ : ℕ) : ℂ) = (M : ℂ) / (d₂ : ℂ) := Nat.cast_div hdvd₂ hd₂'
  calc ∑ a ∈ Finset.range M,
        Complex.exp (2 * Real.pi * Complex.I * (ξ₁ * a / d₁ - ξ₂ * a / d₂))
      = ∑ a ∈ Finset.range M, Complex.exp
          (2 * Real.pi * Complex.I * ((ξ₁ * (M / d₁ : ℕ) - ξ₂ * (M / d₂ : ℕ) : ℤ)) * a / M) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        congr 1
        -- expand the `ℤ → ℂ` cast by hand (`push_cast` would introduce `ℤ`-division)
        simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, hc₁, hc₂]
        field_simp
    _ = 0 := sum_exp_two_pi_mul_eq_zero hM hfreq

/-- Core divisibility step for the frequency-distinctness argument: if `d₁e₁ = d₂e₂ = Q`
with `e₂ ≠ 0`, `ξ₂` is coprime to `Q`, and `Q ∣ ξ₁e₁ − ξ₂e₂`, then `d₂ ∣ d₁`.
(Multiply the divisibility by `d₁`, subtract `ξ₁Q`, and cancel `ξ₂`, then `e₂`.) -/
private lemma dvd_of_dvd_freq_sub {Q d₁ e₁ d₂ e₂ : ℕ} (h₁ : d₁ * e₁ = Q)
    (h₂ : d₂ * e₂ = Q) (he₂ : e₂ ≠ 0) {ξ₁ ξ₂ : ℤ} (hcop : IsCoprime ξ₂ (Q : ℤ))
    (hdvd : (Q : ℤ) ∣ ξ₁ * (e₁ : ℤ) - ξ₂ * (e₂ : ℤ)) : d₂ ∣ d₁ := by
  have h₁' : (d₁ : ℤ) * (e₁ : ℤ) = (Q : ℤ) := by exact_mod_cast h₁
  have key : (Q : ℤ) ∣ ξ₂ * ((e₂ : ℤ) * (d₁ : ℤ)) := by
    have h4 : (Q : ℤ) ∣ (d₁ : ℤ) * (ξ₁ * (e₁ : ℤ) - ξ₂ * (e₂ : ℤ)) := hdvd.mul_left _
    have h5 : ξ₂ * ((e₂ : ℤ) * (d₁ : ℤ))
        = ξ₁ * (Q : ℤ) - (d₁ : ℤ) * (ξ₁ * (e₁ : ℤ) - ξ₂ * (e₂ : ℤ)) := by
      rw [← h₁']; ring
    rw [h5]
    exact dvd_sub (dvd_mul_left _ _) h4
  have key' : Q ∣ e₂ * d₁ := by exact_mod_cast hcop.symm.dvd_of_dvd_mul_left key
  have h6 : e₂ * d₂ ∣ e₂ * d₁ := by
    rw [mul_comm e₂ d₂, h₂]
    exact key'
  exact (mul_dvd_mul_iff_left he₂).mp h6

/-- **Frequency distinctness** (Tao 2015 §4: "if `d₁ ≠ d₂`, then the frequencies
involved here are distinct"): for `d₁ ≠ d₂` both dividing `q^{k-1}` and `ξᵢ` coprime to
`dᵢq`, the combined frequency `ξ₁·q^k/(d₁q) − ξ₂·q^k/(d₂q)` is not divisible by `q^k` —
so the off-diagonal `(perf)` sums vanish by `sum_exp_sub_eq_zero`.

Elementary proof, valuation-free: assume `q^k ∣ ξ₁e₁ − ξ₂e₂` where `eᵢ = q^{k-1}/dᵢ`;
multiplying by `d₁` (resp. `d₂`) and cancelling the unit `ξ₂` (resp. `ξ₁`) mod `q^{k-1}`
gives `d₂ ∣ d₁` and `d₁ ∣ d₂`, hence `d₁ = d₂`. -/
theorem freq_ne_of_divisor_ne {q k : ℕ} (hq : 1 < q) (hk : 1 ≤ k) {d₁ d₂ : ℕ}
    (h₁ : d₁ ∣ q ^ (k - 1)) (h₂ : d₂ ∣ q ^ (k - 1)) (hne : d₁ ≠ d₂)
    {ξ₁ ξ₂ : ℤ} (hcop₁ : IsCoprime ξ₁ (d₁ * q : ℤ)) (hcop₂ : IsCoprime ξ₂ (d₂ * q : ℤ)) :
    ¬((q ^ k : ℤ) ∣ (ξ₁ * (q ^ k / (d₁ * q) : ℕ) - ξ₂ * (q ^ k / (d₂ * q) : ℕ))) := by
  intro hdvd
  apply hne
  have hq0 : q ≠ 0 := by omega
  have hQ0 : q ^ (k - 1) ≠ 0 := pow_ne_zero _ hq0
  have hd₁0 : d₁ ≠ 0 := ne_zero_of_dvd_ne_zero hQ0 h₁
  have hd₂0 : d₂ ≠ 0 := ne_zero_of_dvd_ne_zero hQ0 h₂
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₂, he₂⟩ := h₂
  have he₁0 : e₁ ≠ 0 := fun h => hQ0 (by rw [he₁, h, mul_zero])
  have he₂0 : e₂ ≠ 0 := fun h => hQ0 (by rw [he₂, h, mul_zero])
  have hqk : q ^ k = q ^ (k - 1) * q := by
    rw [← pow_succ]
    congr 1
    omega
  -- identify the exact quotients: `q^k/(dᵢq) = eᵢ`
  have hdiv₁ : q ^ k / (d₁ * q) = e₁ :=
    Nat.div_eq_of_eq_mul_left (mul_pos (Nat.pos_of_ne_zero hd₁0) (by omega))
      (by rw [hqk, he₁]; ring)
  have hdiv₂ : q ^ k / (d₂ * q) = e₂ :=
    Nat.div_eq_of_eq_mul_left (mul_pos (Nat.pos_of_ne_zero hd₂0) (by omega))
      (by rw [hqk, he₂]; ring)
  rw [hdiv₁, hdiv₂] at hdvd
  -- descend the divisibility from `q^k` to `Q = q^{k-1}`
  have hdvd' : ((q ^ (k - 1) : ℕ) : ℤ) ∣ ξ₁ * (e₁ : ℤ) - ξ₂ * (e₂ : ℤ) := by
    push_cast
    exact dvd_trans (pow_dvd_pow (q : ℤ) (Nat.sub_le k 1)) hdvd
  -- `ξᵢ` is a unit mod `Q` (coprime to `q`, hence to `q^{k-1}`)
  have hcopQ₁ : IsCoprime ξ₁ ((q ^ (k - 1) : ℕ) : ℤ) := by
    push_cast
    exact hcop₁.of_mul_right_right.pow_right
  have hcopQ₂ : IsCoprime ξ₂ ((q ^ (k - 1) : ℕ) : ℤ) := by
    push_cast
    exact hcop₂.of_mul_right_right.pow_right
  exact Nat.dvd_antisymm
    (dvd_of_dvd_freq_sub he₂.symm he₁.symm he₁0 hcopQ₁ (dvd_sub_comm.mp hdvd'))
    (dvd_of_dvd_freq_sub he₁.symm he₂.symm he₂0 hcopQ₂ hdvd')

/-- **Perfect cancellation, assembled** (Tao 2015 §4, eq. (perf)): in the Granville
argument mod `q^k`, the full-period average of `e(ξ₁a/(d₁q) − ξ₂a/(d₂q))` vanishes
outright whenever `d₁ ≠ d₂` (both dividing `q^{k-1}`) and `ξᵢ` is coprime to `dᵢq`. -/
theorem sum_exp_sub_eq_zero_of_divisor_ne {q k : ℕ} (hq : 1 < q) (hk : 1 ≤ k)
    {d₁ d₂ : ℕ} (h₁ : d₁ ∣ q ^ (k - 1)) (h₂ : d₂ ∣ q ^ (k - 1)) (hne : d₁ ≠ d₂)
    {ξ₁ ξ₂ : ℤ} (hcop₁ : IsCoprime ξ₁ (d₁ * q : ℤ)) (hcop₂ : IsCoprime ξ₂ (d₂ * q : ℤ)) :
    ∑ a ∈ Finset.range (q ^ k), Complex.exp
      (2 * Real.pi * Complex.I * (ξ₁ * a / (d₁ * q : ℕ) - ξ₂ * a / (d₂ * q : ℕ))) = 0 := by
  have hq0 : q ≠ 0 := by omega
  have hQ0 : q ^ (k - 1) ≠ 0 := pow_ne_zero _ hq0
  have hd₁0 : d₁ ≠ 0 := ne_zero_of_dvd_ne_zero hQ0 h₁
  have hd₂0 : d₂ ≠ 0 := ne_zero_of_dvd_ne_zero hQ0 h₂
  have hqk : q ^ k = q ^ (k - 1) * q := by
    rw [← pow_succ]
    congr 1
    omega
  have hdvd₁ : d₁ * q ∣ q ^ k := by
    rw [hqk]
    exact mul_dvd_mul h₁ dvd_rfl
  have hdvd₂ : d₂ * q ∣ q ^ k := by
    rw [hqk]
    exact mul_dvd_mul h₂ dvd_rfl
  have hfreq : ¬(((q ^ k : ℕ) : ℤ)
      ∣ (ξ₁ * (q ^ k / (d₁ * q) : ℕ) - ξ₂ * (q ^ k / (d₂ * q) : ℕ))) := by
    rw [Nat.cast_pow]
    exact freq_ne_of_divisor_ne hq hk h₁ h₂ hne hcop₁ hcop₂
  exact sum_exp_sub_eq_zero (pow_ne_zero _ hq0) (mul_ne_zero hd₁0 hq0)
    (mul_ne_zero hd₂0 hq0) hdvd₁ hdvd₂ hfreq

end MoltResearch
