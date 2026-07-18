import Mathlib.Analysis.Fourier.ZMod

/-!
# Discrepancy: the circle method on `ZMod H`

Track C, Elliott campaign (`Problems/tao2015_derivation_c.md`, issue #2946, E6f-3):
the scalar Fourier substrate for the paper's Lemma (cap) — pairing character,
normalized DFT, inversion, Plancherel, the shift-correlation identity, and the
bilinear bound splitting frequencies at a threshold on the prime exponential sum.

* `zChar x ξ = e(xξ/H)`; `zDFT F ξ = H⁻¹·∑_x F(x)·conj(zChar x ξ)`.
* `sum_mul_shift_eq` — `∑_j x₁(j)x₂(j+s) = H·∑_ξ ẑ₁(−ξ)ẑ₂(ξ)e(sξ/H)`.
* `norm_block_bilinear_le` — Lemma (cap): the weighted shift-correlation sum is
  at most `θ·H` (minor frequencies, via Plancherel and AM–GM) plus
  `H·κ·∑_{ξ ∈ Ξ} ‖ẑ₁(−ξ)‖` (major frequencies `Ξ`).
-/

namespace MoltResearch

open Finset

variable {H : ℕ} [NeZero H]

/-- The scalar pairing character `e(xξ/H)`. -/
noncomputable def zChar (x ξ : ZMod H) : ℂ := ZMod.stdAddChar (x * ξ)

private lemma sum_zChar_aux (t : ZMod H) :
    ∑ a : ZMod H, ZMod.stdAddChar (t * a) = if t = 0 then (H : ℂ) else 0 := by
  split_ifs with h
  · simp only [h, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const,
      Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar H h)

theorem norm_zChar (x ξ : ZMod H) : ‖zChar x ξ‖ = 1 := by
  rw [zChar, ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

theorem zChar_zero_left (ξ : ZMod H) : zChar 0 ξ = 1 := by
  rw [zChar, zero_mul, AddChar.map_zero_eq_one]

theorem zChar_add_left (x y ξ : ZMod H) :
    zChar (x + y) ξ = zChar x ξ * zChar y ξ := by
  rw [zChar, zChar, zChar, add_mul, AddChar.map_add_eq_mul]

theorem zChar_ne_zero (x ξ : ZMod H) : zChar x ξ ≠ 0 := by
  intro h0
  have h1 := norm_zChar x ξ
  rw [h0, norm_zero] at h1
  norm_num at h1

theorem conj_zChar (x ξ : ZMod H) :
    (starRingEnd ℂ) (zChar x ξ) = zChar (-x) ξ := by
  have hmc := Complex.mul_conj (zChar x ξ)
  rw [Complex.normSq_eq_norm_sq, norm_zChar] at hmc
  have hmc' : zChar x ξ * (starRingEnd ℂ) (zChar x ξ) = 1 := by
    rw [hmc]
    norm_num
  have hinv : zChar x ξ * zChar (-x) ξ = 1 := by
    rw [← zChar_add_left, add_neg_cancel, zChar_zero_left]
  exact mul_left_cancel₀ (zChar_ne_zero x ξ) (hmc'.trans hinv.symm)

/-- The negated pairing collapses: `zChar (−j) (−ξ) = zChar j ξ`. -/
theorem zChar_neg_neg (j ξ : ZMod H) : zChar (-j) (-ξ) = zChar j ξ := by
  rw [zChar, zChar, neg_mul_neg]

/-- The normalized discrete Fourier coefficient on `ZMod H`. -/
noncomputable def zDFT (F : ZMod H → ℂ) (ξ : ZMod H) : ℂ :=
  (1 / (H : ℂ)) * ∑ x, F x * (starRingEnd ℂ) (zChar x ξ)

private lemma HC_ne_zero : ((H : ℂ)) ≠ 0 :=
  Nat.cast_ne_zero.mpr (NeZero.ne H)

theorem norm_zDFT_le (F : ZMod H → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1) (ξ : ZMod H) :
    ‖zDFT F ξ‖ ≤ 1 := by
  rw [zDFT]
  have hHpos : (0 : ℝ) < (H : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne H)
  calc ‖(1 / (H : ℂ)) * ∑ x, F x * (starRingEnd ℂ) (zChar x ξ)‖
      = (1 / (H : ℝ)) * ‖∑ x, F x * (starRingEnd ℂ) (zChar x ξ)‖ := by
        rw [norm_mul]
        congr 1
        rw [norm_div, norm_one, Complex.norm_natCast]
    _ ≤ (1 / (H : ℝ)) * ∑ x : ZMod H, 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun x _ => ?_)
        rw [norm_mul, RCLike.norm_conj, norm_zChar, mul_one]
        exact hF x
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
          mul_one, one_div, inv_mul_cancel₀ (ne_of_gt hHpos)]

/-- **Fourier inversion** on `ZMod H`. -/
theorem sum_zDFT_mul_zChar (F : ZMod H → ℂ) (x : ZMod H) :
    ∑ ξ, zDFT F ξ * zChar x ξ = F x := by
  have hstep : ∀ ξ, zDFT F ξ * zChar x ξ
      = (1 / (H : ℂ)) * ∑ u, F u * zChar (x + -u) ξ := by
    intro ξ
    rw [zDFT, mul_assoc, mul_comm (∑ u, F u * (starRingEnd ℂ) (zChar u ξ))
      (zChar x ξ), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [conj_zChar, zChar_add_left]
    ring
  rw [Finset.sum_congr rfl fun ξ _ => hstep ξ, ← Finset.mul_sum,
    Finset.sum_comm]
  have hinner : ∀ u, ∑ ξ, F u * zChar (x + -u) ξ
      = F u * (if x + -u = 0 then (H : ℂ) else 0) := by
    intro u
    rw [← Finset.mul_sum]
    congr 1
    rw [show (∑ ξ, zChar (x + -u) ξ)
        = ∑ ξ, ZMod.stdAddChar ((x + -u) * ξ) from rfl]
    exact sum_zChar_aux (x + -u)
  rw [Finset.sum_congr rfl fun u _ => hinner u]
  rw [show (∑ u, F u * (if x + -u = 0 then (H : ℂ) else 0))
      = ∑ u, (if u = x then F u * (H : ℂ) else 0) from
    Finset.sum_congr rfl fun u _ => by
      by_cases hu : u = x
      · subst hu
        rw [if_pos (add_neg_cancel u), if_pos rfl]
      · rw [if_neg (fun h0 => hu (add_neg_eq_zero.mp h0).symm), if_neg hu,
          mul_zero]]
  rw [Finset.sum_ite_eq' Finset.univ x (fun u => F u * (H : ℂ)),
    if_pos (Finset.mem_univ x)]
  rw [one_div, mul_comm (F x)]
  rw [← mul_assoc, inv_mul_cancel₀ HC_ne_zero, one_mul]

/-- The un-normalized transform in terms of the DFT. -/
theorem sum_mul_zChar_eq (F : ZMod H → ℂ) (ξ : ZMod H) :
    ∑ j, F j * zChar j ξ = (H : ℂ) * zDFT F (-ξ) := by
  rw [zDFT, ← mul_assoc, mul_one_div, div_self HC_ne_zero, one_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [conj_zChar, zChar_neg_neg]

/-- **The shift-correlation identity**: correlations diagonalize in frequency. -/
theorem sum_mul_shift_eq (x₁ x₂ : ZMod H → ℂ) (s : ZMod H) :
    ∑ j, x₁ j * x₂ (j + s)
      = (H : ℂ) * ∑ ξ, zDFT x₁ (-ξ) * zDFT x₂ ξ * zChar s ξ := by
  have hexp : ∀ j, x₂ (j + s) = ∑ ξ, zDFT x₂ ξ * zChar j ξ * zChar s ξ := by
    intro j
    rw [← sum_zDFT_mul_zChar x₂ (j + s)]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [zChar_add_left]
    ring
  rw [Finset.sum_congr rfl fun j _ => by rw [hexp j]]
  rw [show (∑ j, x₁ j * ∑ ξ, zDFT x₂ ξ * zChar j ξ * zChar s ξ)
      = ∑ ξ, (zDFT x₂ ξ * zChar s ξ) * ∑ j, x₁ j * zChar j ξ from by
    rw [Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [sum_mul_zChar_eq]
  ring

/-- **Plancherel** on `ZMod H`. -/
theorem sum_normSq_zDFT (F : ZMod H → ℂ) :
    ∑ ξ, ‖zDFT F ξ‖ ^ 2 = (1 / (H : ℝ)) * ∑ x, ‖F x‖ ^ 2 := by
  have hkey : ∑ ξ, zDFT F ξ * (starRingEnd ℂ) (zDFT F ξ)
      = (1 / (H : ℂ)) * ∑ x, F x * (starRingEnd ℂ) (F x) := by
    have hterm : ∀ ξ, zDFT F ξ * (starRingEnd ℂ) (zDFT F ξ)
        = (1 / (H : ℂ)) * (1 / (H : ℂ))
          * ∑ u, ∑ v, F u * (starRingEnd ℂ) (F v)
            * (zChar v ξ * (starRingEnd ℂ) (zChar u ξ)) := by
      intro ξ
      rw [zDFT, map_mul, map_sum]
      rw [show ((starRingEnd ℂ) (1 / (H : ℂ))) = 1 / (H : ℂ) from by
        rw [map_div₀, map_one, Complex.conj_natCast]]
      rw [show (∑ x, (starRingEnd ℂ) (F x * (starRingEnd ℂ) (zChar x ξ)))
          = ∑ v, (starRingEnd ℂ) (F v) * zChar v ξ from
        Finset.sum_congr rfl fun v _ => by
          rw [map_mul, RingHomInvPair.comp_apply_eq]]
      rw [mul_mul_mul_comm]
      congr 1
      rw [Finset.sum_mul_sum Finset.univ Finset.univ
        (fun x => F x * (starRingEnd ℂ) (zChar x ξ))
        (fun v => (starRingEnd ℂ) (F v) * zChar v ξ)]
      refine Finset.sum_congr rfl fun u _ => ?_
      refine Finset.sum_congr rfl fun v _ => ?_
      ring
    rw [Finset.sum_congr rfl fun ξ _ => hterm ξ]
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hswap : ∀ u, ∑ ξ, ∑ v, F u * (starRingEnd ℂ) (F v)
        * (zChar v ξ * (starRingEnd ℂ) (zChar u ξ))
        = ∑ v, F u * (starRingEnd ℂ) (F v)
            * (if v + -u = 0 then (H : ℂ) else 0) := by
      intro u
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [← Finset.mul_sum]
      congr 1
      rw [show (∑ ξ, zChar v ξ * (starRingEnd ℂ) (zChar u ξ))
          = ∑ ξ, ZMod.stdAddChar ((v + -u) * ξ) from
        Finset.sum_congr rfl fun ξ _ => by
          rw [conj_zChar, ← zChar_add_left]
          rfl]
      exact sum_zChar_aux (v + -u)
    rw [Finset.sum_congr rfl fun u _ => hswap u]
    have hpick : ∀ u, ∑ v, F u * (starRingEnd ℂ) (F v)
        * (if v + -u = 0 then (H : ℂ) else 0)
        = F u * (starRingEnd ℂ) (F u) * (H : ℂ) := by
      intro u
      rw [show (∑ v, F u * (starRingEnd ℂ) (F v)
          * (if v + -u = 0 then (H : ℂ) else 0))
          = ∑ v, (if v = u then F u * (starRingEnd ℂ) (F v) * (H : ℂ) else 0)
          from Finset.sum_congr rfl fun v _ => by
            by_cases hv : v = u
            · subst hv
              rw [if_pos (add_neg_cancel v), if_pos rfl]
            · rw [if_neg (fun h0 => hv (add_neg_eq_zero.mp h0)), if_neg hv,
                mul_zero]]
      rw [Finset.sum_ite_eq' Finset.univ u
        (fun v => F u * (starRingEnd ℂ) (F v) * (H : ℂ)),
        if_pos (Finset.mem_univ u)]
    rw [Finset.sum_congr rfl fun u _ => hpick u]
    rw [show (∑ u, F u * (starRingEnd ℂ) (F u) * (H : ℂ))
        = (H : ℂ) * ∑ u, F u * (starRingEnd ℂ) (F u) from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by ring]
    have hHne : ((H : ℂ)) ≠ 0 := HC_ne_zero
    field_simp
  have hL : ∑ ξ, zDFT F ξ * (starRingEnd ℂ) (zDFT F ξ)
      = ((∑ ξ, ‖zDFT F ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hR : (1 / (H : ℂ)) * ∑ x, F x * (starRingEnd ℂ) (F x)
      = (((1 / (H : ℝ)) * ∑ x, ‖F x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_sum]
    congr 1
    · rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hL, hR] at hkey
  exact_mod_cast hkey

/-- **Lemma (cap)**, abstract form: the weighted shift-correlation bilinear sum
splits into a minor-frequency part `≤ θ·H` (Plancherel + AM–GM) and a
major-frequency part carried by the large values of the weight exponential sum. -/
theorem norm_block_bilinear_le {ι : Type*} (Pb : Finset ι) (w : ι → ℝ)
    (sh : ι → ZMod H) (x₁ x₂ : ZMod H → ℂ)
    (h₁ : ∀ j, ‖x₁ j‖ ≤ 1) (h₂ : ∀ j, ‖x₂ j‖ ≤ 1)
    (hw0 : ∀ p ∈ Pb, 0 ≤ w p) {κ θ : ℝ}
    (hκ : ∑ p ∈ Pb, w p ≤ κ) (hθ : 0 ≤ θ) :
    ‖∑ p ∈ Pb, (w p : ℂ) * ∑ j, x₁ j * x₂ (j + sh p)‖
      ≤ θ * H + (H : ℝ) * κ * ∑ ξ ∈ Finset.univ.filter (fun ξ : ZMod H =>
          θ ≤ ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖),
          ‖zDFT x₁ (-ξ)‖ := by
  classical
  have hHpos : (0 : ℝ) < (H : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne H)
  have hκ0 : 0 ≤ κ := le_trans (Finset.sum_nonneg hw0) hκ
  -- diagonalize
  have hdiag : ∑ p ∈ Pb, (w p : ℂ) * ∑ j, x₁ j * x₂ (j + sh p)
      = (H : ℂ) * ∑ ξ, zDFT x₁ (-ξ) * zDFT x₂ ξ
          * ∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ := by
    rw [Finset.sum_congr rfl fun p _ => by rw [sum_mul_shift_eq x₁ x₂ (sh p)]]
    rw [show (∑ p ∈ Pb, (w p : ℂ)
        * ((H : ℂ) * ∑ ξ, zDFT x₁ (-ξ) * zDFT x₂ ξ * zChar (sh p) ξ))
        = ∑ p ∈ Pb, ∑ ξ, (H : ℂ) * ((w p : ℂ)
            * (zDFT x₁ (-ξ) * zDFT x₂ ξ * zChar (sh p) ξ)) from
      Finset.sum_congr rfl fun p _ => by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun ξ _ => by ring]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [show zDFT x₁ (-ξ) * zDFT x₂ ξ * ∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ
        = ∑ p ∈ Pb, zDFT x₁ (-ξ) * zDFT x₂ ξ * ((w p : ℂ) * zChar (sh p) ξ)
        from Finset.mul_sum _ _ _]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hdiag, norm_mul, Complex.norm_natCast]
  have htri : ‖∑ ξ, zDFT x₁ (-ξ) * zDFT x₂ ξ
      * ∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖
      ≤ ∑ ξ, ‖zDFT x₁ (-ξ)‖ * ‖zDFT x₂ ξ‖
          * ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun ξ _ => ?_)
    rw [norm_mul, norm_mul]
  have hS : ∀ ξ : ZMod H, ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖ ≤ κ := by
    intro ξ
    refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum
      fun p hp => ?_) hκ)
    rw [norm_mul, norm_zChar, mul_one, Complex.norm_real]
    exact le_of_eq (abs_of_nonneg (hw0 p hp))
  -- split at the threshold
  have hsplit : (∑ ξ, ‖zDFT x₁ (-ξ)‖ * ‖zDFT x₂ ξ‖
        * ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖)
      = (∑ ξ ∈ Finset.univ.filter (fun ξ : ZMod H =>
          θ ≤ ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖),
          ‖zDFT x₁ (-ξ)‖ * ‖zDFT x₂ ξ‖
            * ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖)
        + ∑ ξ ∈ Finset.univ.filter (fun ξ : ZMod H =>
            ¬ θ ≤ ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖),
            ‖zDFT x₁ (-ξ)‖ * ‖zDFT x₂ ξ‖
              * ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖ :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm
  have hmajor : ∑ ξ ∈ Finset.univ.filter (fun ξ : ZMod H =>
      θ ≤ ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖),
      ‖zDFT x₁ (-ξ)‖ * ‖zDFT x₂ ξ‖
        * ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖
      ≤ κ * ∑ ξ ∈ Finset.univ.filter (fun ξ : ZMod H =>
          θ ≤ ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖),
          ‖zDFT x₁ (-ξ)‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ξ _ => ?_
    have hb2 : ‖zDFT x₂ ξ‖ ≤ 1 := norm_zDFT_le x₂ h₂ ξ
    have hb1 : 0 ≤ ‖zDFT x₁ (-ξ)‖ := norm_nonneg _
    calc ‖zDFT x₁ (-ξ)‖ * ‖zDFT x₂ ξ‖
          * ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖
        ≤ ‖zDFT x₁ (-ξ)‖ * 1 * κ := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hb2 hb1) (hS ξ)
            (norm_nonneg _) (by positivity)
      _ = κ * ‖zDFT x₁ (-ξ)‖ := by ring
  have hminor : ∑ ξ ∈ Finset.univ.filter (fun ξ : ZMod H =>
      ¬ θ ≤ ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖),
      ‖zDFT x₁ (-ξ)‖ * ‖zDFT x₂ ξ‖
        * ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖
      ≤ θ := by
    have hstep : ∑ ξ ∈ Finset.univ.filter (fun ξ : ZMod H =>
        ¬ θ ≤ ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖),
        ‖zDFT x₁ (-ξ)‖ * ‖zDFT x₂ ξ‖
          * ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖
        ≤ ∑ ξ ∈ Finset.univ.filter (fun ξ : ZMod H =>
          ¬ θ ≤ ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖),
          ‖zDFT x₁ (-ξ)‖ * ‖zDFT x₂ ξ‖ * θ := by
      refine Finset.sum_le_sum fun ξ hξ => ?_
      rw [Finset.mem_filter] at hξ
      exact mul_le_mul_of_nonneg_left (not_le.mp hξ.2).le
        (by positivity)
    refine le_trans hstep ?_
    have hAMGM : ∑ ξ ∈ Finset.univ.filter (fun ξ : ZMod H =>
        ¬ θ ≤ ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖),
        ‖zDFT x₁ (-ξ)‖ * ‖zDFT x₂ ξ‖ ≤ 1 := by
      have hsub : ∑ ξ ∈ Finset.univ.filter (fun ξ : ZMod H =>
          ¬ θ ≤ ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖),
          ‖zDFT x₁ (-ξ)‖ * ‖zDFT x₂ ξ‖
          ≤ ∑ ξ : ZMod H, ‖zDFT x₁ (-ξ)‖ * ‖zDFT x₂ ξ‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun ξ _ _ => by positivity
      have hAM : ∑ ξ : ZMod H, ‖zDFT x₁ (-ξ)‖ * ‖zDFT x₂ ξ‖
          ≤ (∑ ξ : ZMod H, ‖zDFT x₁ (-ξ)‖ ^ 2 / 2)
            + ∑ ξ : ZMod H, ‖zDFT x₂ ξ‖ ^ 2 / 2 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun ξ _ => ?_
        nlinarith [sq_nonneg (‖zDFT x₁ (-ξ)‖ - ‖zDFT x₂ ξ‖)]
      have hneg : ∑ ξ : ZMod H, ‖zDFT x₁ (-ξ)‖ ^ 2
          = ∑ ξ : ZMod H, ‖zDFT x₁ ξ‖ ^ 2 :=
        Fintype.sum_equiv (Equiv.neg (ZMod H)) _ _ fun ξ => rfl
      have hP1 := sum_normSq_zDFT x₁
      have hP2 := sum_normSq_zDFT x₂
      have hbound : ∀ (F : ZMod H → ℂ), (∀ j, ‖F j‖ ≤ 1) →
          (1 / (H : ℝ)) * ∑ x, ‖F x‖ ^ 2 ≤ 1 := by
        intro F hF
        have hs : ∑ x : ZMod H, ‖F x‖ ^ 2 ≤ ∑ _x : ZMod H, 1 :=
          Finset.sum_le_sum fun x _ => by
            have := hF x
            nlinarith [norm_nonneg (F x)]
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
          mul_one] at hs
        rw [one_div]
        calc (H : ℝ)⁻¹ * ∑ x, ‖F x‖ ^ 2 ≤ (H : ℝ)⁻¹ * (H : ℝ) :=
              mul_le_mul_of_nonneg_left hs (by positivity)
          _ = 1 := inv_mul_cancel₀ (ne_of_gt hHpos)
      have h1 : ∑ ξ : ZMod H, ‖zDFT x₁ ξ‖ ^ 2 ≤ 1 := by
        rw [hP1]
        exact hbound x₁ h₁
      have h2 : ∑ ξ : ZMod H, ‖zDFT x₂ ξ‖ ^ 2 ≤ 1 := by
        rw [hP2]
        exact hbound x₂ h₂
      have hhalf1 : ∑ ξ : ZMod H, ‖zDFT x₁ (-ξ)‖ ^ 2 / 2 ≤ 1 / 2 := by
        rw [← Finset.sum_div, hneg]
        linarith
      have hhalf2 : ∑ ξ : ZMod H, ‖zDFT x₂ ξ‖ ^ 2 / 2 ≤ 1 / 2 := by
        rw [← Finset.sum_div]
        linarith
      have hfinal : ∑ ξ : ZMod H, ‖zDFT x₁ (-ξ)‖ ^ 2 / 2
          + ∑ ξ : ZMod H, ‖zDFT x₂ ξ‖ ^ 2 / 2 ≤ 1 := by
        linarith
      linarith [le_trans hsub (le_trans hAM hfinal)]
    calc ∑ ξ ∈ Finset.univ.filter (fun ξ : ZMod H =>
          ¬ θ ≤ ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖),
          ‖zDFT x₁ (-ξ)‖ * ‖zDFT x₂ ξ‖ * θ
        = (∑ ξ ∈ Finset.univ.filter (fun ξ : ZMod H =>
            ¬ θ ≤ ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖),
            ‖zDFT x₁ (-ξ)‖ * ‖zDFT x₂ ξ‖) * θ := by
          rw [Finset.sum_mul]
      _ ≤ 1 * θ := mul_le_mul_of_nonneg_right hAMGM hθ
      _ = θ := one_mul θ
  calc (H : ℝ) * ‖∑ ξ, zDFT x₁ (-ξ) * zDFT x₂ ξ
        * ∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖
      ≤ (H : ℝ) * (κ * ∑ ξ ∈ Finset.univ.filter (fun ξ : ZMod H =>
          θ ≤ ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖),
          ‖zDFT x₁ (-ξ)‖ + θ) := by
        refine mul_le_mul_of_nonneg_left ?_ hHpos.le
        linarith [htri, hsplit, hmajor, hminor]
    _ = θ * H + (H : ℝ) * κ * ∑ ξ ∈ Finset.univ.filter (fun ξ : ZMod H =>
          θ ≤ ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖),
          ‖zDFT x₁ (-ξ)‖ := by ring

section L4

variable {ι : Type*}

/-- The square of a weighted character sum is the pair-indexed character sum. -/
private lemma sq_sum_zChar (Pb : Finset ι) (w : ι → ℝ) (sh : ι → ZMod H)
    (ξ : ZMod H) :
    (∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ) ^ 2
      = ∑ q ∈ Pb ×ˢ Pb, ((w q.1 : ℂ) * (w q.2 : ℂ))
          * zChar (sh q.1 + sh q.2) ξ := by
  rw [sq, Finset.sum_mul_sum Pb Pb (fun p => (w p : ℂ) * zChar (sh p) ξ)
    (fun p => (w p : ℂ) * zChar (sh p) ξ), Finset.sum_product]
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [zChar_add_left]
  ring

/-- **The `L⁴` identity**: the fourth moment of the weight exponential sum
counts weighted shift-congruent quadruples. -/
theorem sum_normPow4_zCharSum (Pb : Finset ι) (w : ι → ℝ) (sh : ι → ZMod H) :
    ∑ ξ : ZMod H, ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖ ^ 4
      = (H : ℝ) * ∑ x ∈ Pb ×ˢ Pb, ∑ y ∈ Pb ×ˢ Pb,
          (if sh x.1 + sh x.2 = sh y.1 + sh y.2
            then w x.1 * w x.2 * w y.1 * w y.2 else 0) := by
  classical
  have hkey : ∑ ξ : ZMod H, (∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ) ^ 2
        * (starRingEnd ℂ) ((∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ) ^ 2)
      = (H : ℂ) * ∑ x ∈ Pb ×ˢ Pb, ∑ y ∈ Pb ×ˢ Pb,
          (if sh x.1 + sh x.2 = sh y.1 + sh y.2
            then ((w x.1 * w x.2 * w y.1 * w y.2 : ℝ) : ℂ) else 0) := by
    have hterm : ∀ ξ : ZMod H,
        (∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ) ^ 2
          * (starRingEnd ℂ) ((∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ) ^ 2)
        = ∑ x ∈ Pb ×ˢ Pb, ∑ y ∈ Pb ×ˢ Pb,
            ((w x.1 * w x.2 * w y.1 * w y.2 : ℝ) : ℂ)
              * (zChar (sh x.1 + sh x.2) ξ
                * zChar (-(sh y.1 + sh y.2)) ξ) := by
      intro ξ
      rw [sq_sum_zChar, map_sum]
      rw [show (∑ q ∈ Pb ×ˢ Pb, (starRingEnd ℂ)
          (((w q.1 : ℂ) * (w q.2 : ℂ)) * zChar (sh q.1 + sh q.2) ξ))
          = ∑ q ∈ Pb ×ˢ Pb, ((w q.1 : ℂ) * (w q.2 : ℂ))
              * zChar (-(sh q.1 + sh q.2)) ξ from
        Finset.sum_congr rfl fun q _ => by
          rw [map_mul, conj_zChar, map_mul, Complex.conj_ofReal,
            Complex.conj_ofReal]]
      rw [Finset.sum_mul_sum (Pb ×ˢ Pb) (Pb ×ˢ Pb)
        (fun q => ((w q.1 : ℂ) * (w q.2 : ℂ)) * zChar (sh q.1 + sh q.2) ξ)
        (fun q => ((w q.1 : ℂ) * (w q.2 : ℂ)) * zChar (-(sh q.1 + sh q.2)) ξ)]
      refine Finset.sum_congr rfl fun x _ => ?_
      refine Finset.sum_congr rfl fun y _ => ?_
      push_cast
      ring
    rw [Finset.sum_congr rfl fun ξ _ => hterm ξ, Finset.sum_comm]
    rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm]
    have hpick : ∀ x ∈ Pb ×ˢ Pb, ∀ y ∈ Pb ×ˢ Pb,
        ∑ ξ : ZMod H, ((w x.1 * w x.2 * w y.1 * w y.2 : ℝ) : ℂ)
            * (zChar (sh x.1 + sh x.2) ξ * zChar (-(sh y.1 + sh y.2)) ξ)
        = (if sh x.1 + sh x.2 = sh y.1 + sh y.2
            then ((w x.1 * w x.2 * w y.1 * w y.2 : ℝ) : ℂ) else 0)
          * (H : ℂ) := by
      intro x _ y _
      rw [show (∑ ξ : ZMod H, ((w x.1 * w x.2 * w y.1 * w y.2 : ℝ) : ℂ)
          * (zChar (sh x.1 + sh x.2) ξ * zChar (-(sh y.1 + sh y.2)) ξ))
          = ((w x.1 * w x.2 * w y.1 * w y.2 : ℝ) : ℂ)
            * ∑ ξ : ZMod H, ZMod.stdAddChar
              ((sh x.1 + sh x.2 + -(sh y.1 + sh y.2)) * ξ) from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [← zChar_add_left]
        rfl]
      rw [sum_zChar_aux]
      by_cases hq : sh x.1 + sh x.2 = sh y.1 + sh y.2
      · rw [if_pos (by rw [hq, add_neg_cancel]), if_pos hq]
      · rw [if_neg (fun h0 => hq (add_neg_eq_zero.mp h0)), if_neg hq,
          mul_zero, zero_mul]
    rw [Finset.sum_congr rfl fun x hx =>
      Finset.sum_congr rfl fun y hy => hpick x hx y hy]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  have hL : ∑ ξ : ZMod H, (∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ) ^ 2
        * (starRingEnd ℂ) ((∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ) ^ 2)
      = ((∑ ξ : ZMod H, ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖ ^ 4 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [Complex.mul_conj, map_pow, Complex.normSq_eq_norm_sq]
    rw [show ((‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖ ^ 2) ^ 2 : ℝ)
        = ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖ ^ 4 from by ring]
  have hR : (H : ℂ) * ∑ x ∈ Pb ×ˢ Pb, ∑ y ∈ Pb ×ˢ Pb,
        (if sh x.1 + sh x.2 = sh y.1 + sh y.2
          then ((w x.1 * w x.2 * w y.1 * w y.2 : ℝ) : ℂ) else 0)
      = (((H : ℝ) * ∑ x ∈ Pb ×ˢ Pb, ∑ y ∈ Pb ×ˢ Pb,
          (if sh x.1 + sh x.2 = sh y.1 + sh y.2
            then w x.1 * w x.2 * w y.1 * w y.2 else 0) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs
    · rfl
    · exact Complex.ofReal_zero.symm
  rw [hL, hR] at hkey
  exact_mod_cast hkey

/-- **Markov for the major frequencies**: the count of frequencies where the
weight sum exceeds `θ` is at most `θ⁻⁴` times its fourth moment. -/
theorem card_filter_le_sum_normPow4 (Pb : Finset ι) (w : ι → ℝ)
    (sh : ι → ZMod H) {θ : ℝ} (hθ : 0 < θ) :
    ((Finset.univ.filter (fun ξ : ZMod H =>
        θ ≤ ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖)).card : ℝ) * θ ^ 4
      ≤ ∑ ξ : ZMod H, ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖ ^ 4 := by
  classical
  have hper : ∀ ξ ∈ Finset.univ.filter (fun ξ : ZMod H =>
      θ ≤ ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖),
      θ ^ 4 ≤ ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖ ^ 4 := by
    intro ξ hξ
    rw [Finset.mem_filter] at hξ
    exact pow_le_pow_left₀ hθ.le hξ.2 4
  have hsum := Finset.card_nsmul_le_sum
    (Finset.univ.filter (fun ξ : ZMod H =>
      θ ≤ ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖))
    (fun ξ => ‖∑ p ∈ Pb, (w p : ℂ) * zChar (sh p) ξ‖ ^ 4) (θ ^ 4) hper
  rw [nsmul_eq_mul] at hsum
  refine le_trans hsum ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun ξ _ _ => by positivity

end L4

/-- **Wrap control**: when the window exceeds the block reach, the `ZMod H`
congruence between shift sums is genuine equality of the prime sums. -/
theorem zmod_shift_congr_iff {H h n₀ : ℕ} (hh : 1 ≤ h)
    {p₁ p₂ p₃ p₄ : ℕ} (h₁ : p₁ ≤ 2 * n₀) (h₂ : p₂ ≤ 2 * n₀)
    (h₃ : p₃ ≤ 2 * n₀) (h₄ : p₄ ≤ 2 * n₀) (hH : 4 * n₀ * h < H) :
    (((p₁ * h : ℕ) : ZMod H) + ((p₂ * h : ℕ) : ZMod H)
        = ((p₃ * h : ℕ) : ZMod H) + ((p₄ * h : ℕ) : ZMod H))
      ↔ p₁ + p₂ = p₃ + p₄ := by
  constructor
  · intro hcast
    have hsum : (((p₁ * h + p₂ * h : ℕ)) : ZMod H)
        = ((p₃ * h + p₄ * h : ℕ) : ZMod H) := by
      push_cast
      exact_mod_cast hcast
    have hlt₁ : p₁ * h + p₂ * h < H := by nlinarith
    have hlt₂ : p₃ * h + p₄ * h < H := by nlinarith
    have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp hsum
    have heq : p₁ * h + p₂ * h = p₃ * h + p₄ * h := by
      have := hmod
      unfold Nat.ModEq at this
      rwa [Nat.mod_eq_of_lt hlt₁, Nat.mod_eq_of_lt hlt₂] at this
    have hmul : (p₁ + p₂) * h = (p₃ + p₄) * h := by
      rw [add_mul, add_mul]
      exact heq
    exact Nat.eq_of_mul_eq_mul_right (by omega) hmul
  · intro hnat
    have heq : p₁ * h + p₂ * h = p₃ * h + p₄ * h := by
      have := congrArg (· * h) hnat
      simpa [add_mul] using this
    have hc := congrArg (fun n : ℕ => (n : ZMod H)) heq
    push_cast at hc
    exact_mod_cast hc

end MoltResearch
