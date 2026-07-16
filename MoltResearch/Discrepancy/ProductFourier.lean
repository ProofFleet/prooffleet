import Mathlib.Analysis.Fourier.ZMod

/-!
# Discrepancy: scalar Fourier analysis on `(ι' → ZMod M)`

Finitary substrate for the Tao 2015 §2 Fourier reduction (arXiv:1509.05363,
`Problems/tao2015_derivation_c.md`, issue #2920): the discrete Fourier transform on the
product group `ι' → ZMod M` for `ℂ`-valued functions, with exactly the identities the
reduction consumes.

* `prodChar x ξ = ∏ i, e(xᵢξᵢ/M)` — the product pairing character (symmetric in `x, ξ`).
* `sum_prodChar` — orthogonality: `∑_x prodChar x ξ = M^r·1_{ξ=0}`.
* `prodDFT F ξ = M^{−r}·∑_x F(x)·conj (prodChar x ξ)` — the normalized DFT.
* `sum_normSq_prodDFT` — Plancherel: `∑_ξ ‖F̂(ξ)‖² = M^{−r}·∑_x ‖F(x)‖²`.
* `avg_normSq_shift_sum_eq` — the **windowed Plancherel identity** of §2:

  `M^{−r}·∑_x ‖∑_{j ∈ s} F(x + π j)‖² = ∑_ξ ‖F̂(ξ)‖²·‖∑_{j ∈ s} prodChar (π j) ξ‖²`

  (the left side is eq. (fpi)'s average, the right side the spectral form feeding the
  random-frequency construction).

The `1`-dimensional orthogonality input is `AddChar.sum_eq_zero_of_ne_one` at the
primitive standard character (`ZMod.isPrimitive_stdAddChar`).
-/

namespace MoltResearch

open Finset

variable {M : ℕ} [NeZero M] {ι' : Type*} [Fintype ι'] [DecidableEq ι']

/-- The product pairing character on `ι' → ZMod M`: `∏ i, e(xᵢ·ξᵢ/M)`. -/
noncomputable def prodChar (x ξ : ι' → ZMod M) : ℂ :=
  ∏ i, ZMod.stdAddChar (x i * ξ i)

/-- One-dimensional orthogonality at the standard character. -/
private lemma sum_stdAddChar_mul (t : ZMod M) :
    ∑ a : ZMod M, ZMod.stdAddChar (t * a) = if t = 0 then (M : ℂ) else 0 := by
  split_ifs with h
  · simp only [h, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, mul_one]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar M h)

/-- The pairing is symmetric. -/
theorem prodChar_comm (x ξ : ι' → ZMod M) : prodChar x ξ = prodChar ξ x := by
  unfold prodChar
  exact Finset.prod_congr rfl fun i _ => by rw [mul_comm]

/-- The pairing is additive in the first slot. -/
theorem prodChar_add_left (x y ξ : ι' → ZMod M) :
    prodChar (x + y) ξ = prodChar x ξ * prodChar y ξ := by
  unfold prodChar
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.add_apply, add_mul, AddChar.map_add_eq_mul]

/-- The pairing at the zero frequency is `1`. -/
@[simp] theorem prodChar_zero_right (x : ι' → ZMod M) : prodChar x 0 = 1 := by
  unfold prodChar
  simp

/-- The pairing at the zero shift is `1`. -/
@[simp] theorem prodChar_zero_left (ξ : ι' → ZMod M) : prodChar 0 ξ = 1 := by
  rw [prodChar_comm]
  exact prodChar_zero_right ξ

/-- The pairing values are unimodular. -/
theorem norm_prodChar (x ξ : ι' → ZMod M) : ‖prodChar x ξ‖ = 1 := by
  unfold prodChar
  rw [norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- Conjugation negates the first slot. -/
theorem conj_prodChar (x ξ : ι' → ZMod M) :
    (starRingEnd ℂ) (prodChar x ξ) = prodChar (-x) ξ := by
  unfold prodChar
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hinv : ZMod.stdAddChar (-(x i * ξ i)) * ZMod.stdAddChar (x i * ξ i) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hnorm : ‖ZMod.stdAddChar (x i * ξ i)‖ = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  have hmc := Complex.mul_conj (ZMod.stdAddChar (x i * ξ i))
  rw [Complex.normSq_eq_norm_sq, hnorm] at hmc
  -- conj ψ = ψ⁻¹ = ψ(−a); both are the unique inverse of ψ(a)
  have hψ0 : ZMod.stdAddChar (x i * ξ i) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    norm_num at hnorm
  have h1 : (starRingEnd ℂ) (ZMod.stdAddChar (x i * ξ i))
      = (ZMod.stdAddChar (x i * ξ i))⁻¹ := by
    field_simp
    rw [mul_comm]
    rw [hmc]
    norm_num
  rw [Pi.neg_apply, neg_mul, h1]
  exact inv_eq_of_mul_eq_one_left hinv

/-- **Orthogonality**: the pairing sums to `M^r` at the zero frequency and to `0`
elsewhere. -/
theorem sum_prodChar (ξ : ι' → ZMod M) :
    ∑ x : ι' → ZMod M, prodChar x ξ = if ξ = 0 then ((M : ℂ)) ^ Fintype.card ι' else 0 := by
  unfold prodChar
  rw [← Fintype.piFinset_univ,
    ← Finset.prod_univ_sum (fun _ : ι' => (Finset.univ : Finset (ZMod M)))
      (fun i a => ZMod.stdAddChar (a * ξ i))]
  have hfac : ∀ i : ι', ∑ a : ZMod M, ZMod.stdAddChar (a * ξ i)
      = if ξ i = 0 then (M : ℂ) else 0 := by
    intro i
    rw [← sum_stdAddChar_mul (ξ i)]
    exact Finset.sum_congr rfl fun a _ => by rw [mul_comm]
  rw [Finset.prod_congr rfl fun i _ => hfac i]
  by_cases hξ : ξ = 0
  · subst hξ
    simp
  · rw [if_neg hξ]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hξ
    have hi' : ξ i ≠ 0 := by simpa using hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi')

/-- The normalized discrete Fourier coefficient. -/
noncomputable def prodDFT (F : (ι' → ZMod M) → ℂ) (ξ : ι' → ZMod M) : ℂ :=
  (1 / (M : ℂ) ^ Fintype.card ι') * ∑ x : ι' → ZMod M, F x * (starRingEnd ℂ) (prodChar x ξ)

/-- Cardinality of the product group, as a complex number. -/
private lemma card_pi_eq : (Fintype.card (ι' → ZMod M) : ℂ) = ((M : ℂ)) ^ Fintype.card ι' := by
  rw [Fintype.card_fun]
  push_cast
  simp [ZMod.card]

private lemma Mr_ne_zero : ((M : ℂ)) ^ Fintype.card ι' ≠ 0 :=
  pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne M))

/-- **Shifted-window Plancherel** (Tao 2015 §2, the (fpi) ↔ spectral identity): for any
finite window `s` and shift data `π`, the average of `‖∑_{j ∈ s} F(x + π j)‖²` over the
group equals the spectral average `∑_ξ ‖F̂(ξ)‖²·‖∑_{j ∈ s} prodChar (π j) ξ‖²`. -/
theorem avg_normSq_shift_sum_eq {ι : Type*} (s : Finset ι) (π : ι → ι' → ZMod M)
    (F : (ι' → ZMod M) → ℂ) :
    (1 / ((M : ℝ)) ^ Fintype.card ι') * ∑ x : ι' → ZMod M, ‖∑ j ∈ s, F (x + π j)‖ ^ 2
      = ∑ ξ : ι' → ZMod M,
          ‖prodDFT F ξ‖ ^ 2 * ‖∑ j ∈ s, prodChar (π j) ξ‖ ^ 2 := by
  classical
  -- the windowed function and its Fourier coefficients
  set G : (ι' → ZMod M) → ℂ := fun x => ∑ j ∈ s, F (x + π j) with hGdef
  have hGhat : ∀ ξ : ι' → ZMod M,
      prodDFT G ξ = prodDFT F ξ * ∑ j ∈ s, prodChar (π j) ξ := by
    intro ξ
    unfold prodDFT
    rw [hGdef]
    calc (1 / (M : ℂ) ^ Fintype.card ι') * ∑ x : ι' → ZMod M,
          (∑ j ∈ s, F (x + π j)) * (starRingEnd ℂ) (prodChar x ξ)
        = (1 / (M : ℂ) ^ Fintype.card ι') * ∑ j ∈ s, ∑ x : ι' → ZMod M,
            F (x + π j) * (starRingEnd ℂ) (prodChar x ξ) := by
          rw [Finset.sum_comm]
          rw [Finset.sum_congr rfl fun x _ => Finset.sum_mul _ _ _]
      _ = (1 / (M : ℂ) ^ Fintype.card ι') * ∑ j ∈ s, (∑ u : ι' → ZMod M,
            F u * (starRingEnd ℂ) (prodChar u ξ)) * prodChar (π j) ξ := by
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          have hunit : prodChar (π j) ξ * (starRingEnd ℂ) (prodChar (π j) ξ) = 1 := by
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_prodChar]
            norm_num
          -- reindex `u := x + π j`
          have hre : ∑ x : ι' → ZMod M, F (x + π j) * (starRingEnd ℂ) (prodChar x ξ)
              = ∑ u : ι' → ZMod M,
                  F u * (starRingEnd ℂ) (prodChar (u - π j) ξ) := by
            refine Fintype.sum_equiv (Equiv.addRight (π j)) _ _ fun x => ?_
            simp only [Equiv.coe_addRight]
            rw [add_sub_cancel_right]
          rw [hre, Finset.sum_mul]
          refine Finset.sum_congr rfl fun u _ => ?_
          -- conj ψ_{u−πj} = conj ψ_u · ψ_πj
          have hsplit : prodChar u ξ = prodChar (u - π j) ξ * prodChar (π j) ξ := by
            rw [← prodChar_add_left, sub_add_cancel]
          have hkey : (starRingEnd ℂ) (prodChar (u - π j) ξ)
              = (starRingEnd ℂ) (prodChar u ξ) * prodChar (π j) ξ := by
            rw [hsplit, map_mul]
            calc (starRingEnd ℂ) (prodChar (u - π j) ξ)
                = (starRingEnd ℂ) (prodChar (u - π j) ξ)
                  * ((starRingEnd ℂ) (prodChar (π j) ξ) * prodChar (π j) ξ) := by
                  rw [mul_comm ((starRingEnd ℂ) (prodChar (π j) ξ)), hunit, mul_one]
              _ = (starRingEnd ℂ) (prodChar (u - π j) ξ)
                  * (starRingEnd ℂ) (prodChar (π j) ξ) * prodChar (π j) ξ := by ring
          rw [hkey]
          ring
      _ = prodDFT F ξ * ∑ j ∈ s, prodChar (π j) ξ := by
          unfold prodDFT
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
  -- Plancherel for `G`
  have hPlan : ∑ ξ : ι' → ZMod M, ‖prodDFT G ξ‖ ^ 2
      = (1 / ((M : ℝ)) ^ Fintype.card ι') * ∑ x : ι' → ZMod M, ‖G x‖ ^ 2 := by
    -- expand `‖·‖²` as `z·conj z` and use orthogonality
    have hkey : ((∑ ξ : ι' → ZMod M, ‖prodDFT G ξ‖ ^ 2 : ℝ) : ℂ)
        = (1 / (M : ℂ) ^ Fintype.card ι') * ∑ x : ι' → ZMod M, ((‖G x‖ ^ 2 : ℝ) : ℂ) := by
      have hconj : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := fun z => by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      calc ∑ ξ : ι' → ZMod M, (‖prodDFT G ξ‖ : ℂ) ^ 2
          = ∑ ξ : ι' → ZMod M, prodDFT G ξ * (starRingEnd ℂ) (prodDFT G ξ) := by
            refine Finset.sum_congr rfl fun ξ _ => ?_
            rw [← hconj]
            norm_cast
        _ = ∑ ξ : ι' → ZMod M, (1 / (M : ℂ) ^ Fintype.card ι') * (1 / (M : ℂ) ^ Fintype.card ι')
              * ∑ y : ι' → ZMod M, ∑ z : ι' → ZMod M,
                G y * (starRingEnd ℂ) (G z)
                  * ((starRingEnd ℂ) (prodChar y ξ) * prodChar z ξ) := by
            refine Finset.sum_congr rfl fun ξ _ => ?_
            have hconjDFT : (starRingEnd ℂ) (prodDFT G ξ)
                = (1 / (M : ℂ) ^ Fintype.card ι') * ∑ z : ι' → ZMod M,
                    (starRingEnd ℂ) (G z) * prodChar z ξ := by
              unfold prodDFT
              rw [map_mul, map_sum]
              congr 1
              · rw [map_div₀, map_one, map_pow, Complex.conj_natCast]
              · refine Finset.sum_congr rfl fun z _ => ?_
                rw [map_mul, Complex.conj_conj]
            rw [hconjDFT]
            unfold prodDFT
            rw [show ∀ A B : ℂ, (1 / (M : ℂ) ^ Fintype.card ι' * A) * (1 / (M : ℂ) ^ Fintype.card ι' * B)
                = 1 / (M : ℂ) ^ Fintype.card ι' * (1 / (M : ℂ) ^ Fintype.card ι') * (A * B) from fun A B => by ring]
            rw [Finset.sum_mul_sum Finset.univ Finset.univ
              (fun y => G y * (starRingEnd ℂ) (prodChar y ξ))
              (fun z => (starRingEnd ℂ) (G z) * prodChar z ξ)]
            simp only [Finset.mul_sum]
            refine Finset.sum_congr rfl fun y _ => ?_
            refine Finset.sum_congr rfl fun z _ => ?_
            ring
        _ = (1 / (M : ℂ) ^ Fintype.card ι') * (1 / (M : ℂ) ^ Fintype.card ι')
              * ∑ y : ι' → ZMod M, ∑ z : ι' → ZMod M,
                G y * (starRingEnd ℂ) (G z)
                  * ∑ ξ : ι' → ZMod M, prodChar (z - y) ξ := by
            rw [← Finset.mul_sum]
            congr 1
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [← Finset.mul_sum]
            congr 1
            refine Finset.sum_congr rfl fun ξ _ => ?_
            rw [conj_prodChar, ← prodChar_add_left]
            congr 1
            abel
        _ = (1 / (M : ℂ) ^ Fintype.card ι') * ∑ x : ι' → ZMod M, G x * (starRingEnd ℂ) (G x) := by
            have hortho : ∀ y z : ι' → ZMod M,
                (∑ ξ : ι' → ZMod M, prodChar (z - y) ξ)
                  = if z = y then ((M : ℂ)) ^ Fintype.card ι' else 0 := by
              intro y z
              have hsym : ∑ ξ : ι' → ZMod M, prodChar (z - y) ξ
                  = ∑ ξ : ι' → ZMod M, prodChar ξ (z - y) :=
                Finset.sum_congr rfl fun ξ _ => prodChar_comm _ _
              rw [hsym, sum_prodChar]
              by_cases h : z = y
              · rw [if_pos (sub_eq_zero_of_eq h), if_pos h]
              · rw [if_neg (fun hc => h (sub_eq_zero.mp hc)), if_neg h]
            calc (1 / (M : ℂ) ^ Fintype.card ι') * (1 / (M : ℂ) ^ Fintype.card ι')
                  * ∑ y : ι' → ZMod M, ∑ z : ι' → ZMod M,
                    G y * (starRingEnd ℂ) (G z) * ∑ ξ : ι' → ZMod M, prodChar (z - y) ξ
                = (1 / (M : ℂ) ^ Fintype.card ι') * (1 / (M : ℂ) ^ Fintype.card ι')
                  * ∑ y : ι' → ZMod M, G y * (starRingEnd ℂ) (G y) * ((M : ℂ)) ^ Fintype.card ι' := by
                  congr 1
                  refine Finset.sum_congr rfl fun y _ => ?_
                  rw [Finset.sum_eq_single_of_mem y (Finset.mem_univ y)]
                  · rw [hortho y y, if_pos rfl]
                  · intro z _ hzy
                    rw [hortho y z, if_neg hzy, mul_zero]
              _ = (1 / (M : ℂ) ^ Fintype.card ι') * ∑ x : ι' → ZMod M, G x * (starRingEnd ℂ) (G x) := by
                  rw [← Finset.sum_mul]
                  have hne := Mr_ne_zero (M := M) (ι' := ι')
                  field_simp
        _ = (1 / (M : ℂ) ^ Fintype.card ι') * ∑ x : ι' → ZMod M, ((‖G x‖ : ℂ)) ^ 2 := by
            congr 1
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [← hconj]
            norm_cast
    -- return to `ℝ`
    have h2 := hkey
    rw [show (1 / (M : ℂ) ^ Fintype.card ι') = (((1 / (M : ℝ) ^ Fintype.card ι') : ℝ) : ℂ) from by push_cast; ring,
      ← Complex.ofReal_sum, ← Complex.ofReal_mul] at h2
    exact Complex.ofReal_inj.mp h2
  -- assemble
  calc (1 / ((M : ℝ)) ^ Fintype.card ι') * ∑ x : ι' → ZMod M, ‖∑ j ∈ s, F (x + π j)‖ ^ 2
      = ∑ ξ : ι' → ZMod M, ‖prodDFT G ξ‖ ^ 2 := by
        rw [hPlan, hGdef]
    _ = ∑ ξ : ι' → ZMod M, ‖prodDFT F ξ‖ ^ 2 * ‖∑ j ∈ s, prodChar (π j) ξ‖ ^ 2 := by
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [hGhat ξ, norm_mul, mul_pow]

/-- **Plancherel**: total spectral mass equals the average square mass. -/
theorem sum_normSq_prodDFT (F : (ι' → ZMod M) → ℂ) :
    ∑ ξ : ι' → ZMod M, ‖prodDFT F ξ‖ ^ 2
      = (1 / ((M : ℝ)) ^ Fintype.card ι') * ∑ x : ι' → ZMod M, ‖F x‖ ^ 2 := by
  classical
  have h := avg_normSq_shift_sum_eq (s := ({0} : Finset ℕ)) (π := fun _ => 0) F
  simp only [Finset.sum_singleton, add_zero, prodChar_zero_left, norm_one, one_pow,
    mul_one] at h
  exact h.symm

end MoltResearch
