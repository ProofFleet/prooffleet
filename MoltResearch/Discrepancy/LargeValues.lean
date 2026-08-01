import MoltResearch.Discrepancy.PlancherelHarness
import MoltResearch.Discrepancy.BrunTitchmarsh
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Track C: large values of prime-block phase sums (Track R, C4a)

The kernel toolkit for the C4a window-energy bound: the oscillation kernel
`‖∫_{-L}^{L} e(−sξ) dξ‖ ≤ 1/(π|s|)`, the phase-product law
`e(−uξ)·conj(e(−vξ)) = e(−((u−v)ξ))`, the interval real-part commute, and
the log-separation `log q − log p ≥ (q−p)/q`.

The window-energy expansion (next unit) combines these with the
reciprocal prime-gap sum of `BrunTitchmarsh.lean`: the energy of
`S(ξ) = ∑_{p∈P} (a_p/p)·e(−ξ·log p)` over `[−L, L]` is at most
`2L·∑ 1/p² + (∑ 1/p)·O(loglog P₊)`, which caps the number of
`1`-separated `δE`-large values at `O_δ(1)` — the first leg of the C4
dichotomy.
-/

namespace MoltResearch

namespace ExpSums

open Real MeasureTheory

/-- The oscillation kernel: `‖∫_{-L}^{L} e(−sξ) dξ‖ ≤ 1/(π|s|)`. -/
theorem norm_intervalIntegral_char_le {s : ℝ} (hs : s ≠ 0) (L : ℝ) :
    ‖∫ ξ in (-L)..L, ((Real.fourierChar (-(s * ξ)) : Circle) : ℂ)‖
      ≤ 1/(Real.pi * |s|) := by
  set c : ℂ := (((-(2*Real.pi*s) : ℝ)) : ℂ) * Complex.I with hc_def
  have hc : c ≠ 0 := by
    rw [hc_def]
    simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false,
      Complex.ofReal_eq_zero]
    intro h
    have := Real.pi_ne_zero
    rcases mul_eq_zero.mp (by linarith [h] : (2*Real.pi)*s = 0) with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · norm_num at h2
      · exact this h2
    · exact hs h1
  have hchar : ∀ ξ : ℝ, ((Real.fourierChar (-(s * ξ)) : Circle) : ℂ)
      = Complex.exp (c * ξ) := by
    intro ξ
    rw [Real.fourierChar_apply, hc_def]
    congr 1
    push_cast
    ring
  rw [intervalIntegral.integral_congr (fun ξ _ => hchar ξ)]
  rw [integral_exp_mul_complex hc]
  rw [norm_div]
  have hre : ∀ x : ℝ, (c * (x:ℂ)).re = 0 := by
    intro x
    rw [hc_def]
    simp [Complex.mul_re, Complex.mul_im]
  have h1 : ‖Complex.exp (c * (L:ℂ))‖ = 1 := by
    rw [Complex.norm_exp, hre, Real.exp_zero]
  have h2 : ‖Complex.exp (c * ((-L:ℝ):ℂ))‖ = 1 := by
    rw [Complex.norm_exp, hre, Real.exp_zero]
  have hnum : ‖Complex.exp (c * (L:ℂ)) - Complex.exp (c * ((-L:ℝ):ℂ))‖
      ≤ 2 := by
    calc ‖Complex.exp (c * (L:ℂ)) - Complex.exp (c * ((-L:ℝ):ℂ))‖
        ≤ ‖Complex.exp (c * (L:ℂ))‖ + ‖Complex.exp (c * ((-L:ℝ):ℂ))‖ :=
          norm_sub_le _ _
      _ = 2 := by rw [h1, h2]; norm_num
  have hden : ‖c‖ = 2*Real.pi*|s| := by
    rw [hc_def, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_neg, abs_mul]
    rw [abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)]
  rw [hden]
  have hs0 : (0:ℝ) < |s| := abs_pos.mpr hs
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc ‖Complex.exp (c * (L:ℂ)) - Complex.exp (c * ((-L:ℝ):ℂ))‖
        * (Real.pi * |s|)
      ≤ 2 * (Real.pi * |s|) :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = 1 * (2*Real.pi*|s|) := by ring

/-- Phase products combine: `e(−uξ)·conj(e(−vξ)) = e(−((u−v)ξ))`. -/
theorem char_mul_conj_char (u v ξ : ℝ) :
    ((Real.fourierChar (-(u * ξ)) : Circle) : ℂ)
      * (starRingEnd ℂ) ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ)
      = ((Real.fourierChar (-((u - v) * ξ)) : Circle) : ℂ) := by
  rw [Real.fourierChar_apply, Real.fourierChar_apply, Real.fourierChar_apply]
  rw [← Complex.exp_conj]
  rw [← Complex.exp_add]
  congr 1
  have h1 : (starRingEnd ℂ) ((((2*Real.pi*(-(v*ξ)) : ℝ)):ℂ) * Complex.I)
      = -((((2*Real.pi*(-(v*ξ)) : ℝ)):ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [h1]
  push_cast
  ring

/-- The real part commutes with the interval integral. -/
theorem intervalIntegral_re (g : ℝ → ℂ) {a b : ℝ}
    (hg : IntervalIntegrable g MeasureTheory.volume a b) :
    ∫ ξ in a..b, (g ξ).re = (∫ ξ in a..b, g ξ).re := by
  rcases le_total a b with hab | hab
  · rw [intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_of_le hab]
    exact integral_re hg.1
  · rw [intervalIntegral.integral_of_ge hab,
      intervalIntegral.integral_of_ge hab]
    rw [Complex.neg_re]
    exact congrArg Neg.neg (integral_re hg.2)

/-- `log` separates naturals: `log q − log p ≥ (q−p)/q` for `1 ≤ p < q`. -/
theorem log_sub_log_ge (p q : ℕ) (hp : 1 ≤ p) (hpq : p < q) :
    ((q:ℝ) - p)/q ≤ Real.log q - Real.log p := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  have hq0 : (0:ℝ) < q := by
    have : (0:ℕ) < q := by omega
    exact_mod_cast this
  -- `log(p/q) ≤ p/q − 1` gives `log q − log p ≥ 1 − p/q = (q−p)/q`
  have h1 : Real.log ((p:ℝ)/q) ≤ (p:ℝ)/q - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log ((p:ℝ)/q) = Real.log p - Real.log q :=
    Real.log_div (ne_of_gt hp0) (ne_of_gt hq0)
  have h3 : ((q:ℝ) - p)/q = 1 - (p:ℝ)/q := by
    field_simp
  rw [h3]
  rw [h2] at h1
  linarith

/-- The diagonal pair integral: value `≤ 2L/p²`. -/
theorem pair_integral_diag_le (a : ℕ → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1)
    (p : ℕ) (hp : 1 ≤ p) (L : ℝ) (hL : 0 ≤ L) :
    (∫ ξ in (-L)..L, ((a p/(p:ℂ)) * (starRingEnd ℂ) (a p/(p:ℂ))
        * ((Real.fourierChar (-((Real.log p - Real.log p) * ξ)) : Circle) : ℂ))).re
      ≤ 2*L*(1/(p:ℝ)^2) := by
  have hchar : ∀ ξ : ℝ,
      ((Real.fourierChar (-((Real.log p - Real.log p) * ξ)) : Circle) : ℂ) = 1 := by
    intro ξ
    rw [sub_self, zero_mul, neg_zero]
    simp
  have hcongr : ∀ ξ : ℝ, (a p/(p:ℂ)) * (starRingEnd ℂ) (a p/(p:ℂ))
      * ((Real.fourierChar (-((Real.log p - Real.log p) * ξ)) : Circle) : ℂ)
      = (a p/(p:ℂ)) * (starRingEnd ℂ) (a p/(p:ℂ)) := by
    intro ξ
    rw [hchar, mul_one]
  rw [intervalIntegral.integral_congr (fun ξ _ => hcongr ξ)]
  rw [intervalIntegral.integral_const]
  have hzz : (a p/(p:ℂ)) * (starRingEnd ℂ) (a p/(p:ℂ))
      = ((Complex.normSq (a p/(p:ℂ)) : ℝ) : ℂ) := Complex.mul_conj _
  rw [hzz]
  have h1 : ((L - -L) • (((Complex.normSq (a p/(p:ℂ)) : ℝ) : ℂ))).re
      = (L - -L) * Complex.normSq (a p/(p:ℂ)) := by
    rw [Complex.real_smul, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [h1]
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  have h3 : ‖a p/(p:ℂ)‖ ≤ 1/p := by
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (ha p) hp0.le
  have h4 : Complex.normSq (a p/(p:ℂ)) = ‖a p/(p:ℂ)‖^2 :=
    Complex.normSq_eq_norm_sq _
  have h2 : Complex.normSq (a p/(p:ℂ)) ≤ 1/(p:ℝ)^2 := by
    rw [h4]
    have h5 := norm_nonneg (a p/(p:ℂ))
    have h6 : (1/(p:ℝ))^2 = 1/(p:ℝ)^2 := by ring
    nlinarith [h3]
  have hnn : 0 ≤ Complex.normSq (a p/(p:ℂ)) := Complex.normSq_nonneg _
  nlinarith [h2, hL]

/-- The off-diagonal pair integral: `≤ 1/(π·p·(q−p))` for `p < q` — the
`q` from the log-separation cancels the `1/q` of the coefficient. -/
theorem pair_integral_offdiag_le (a : ℕ → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1)
    (p q : ℕ) (hp : 1 ≤ p) (hpq : p < q) (L : ℝ) :
    |(∫ ξ in (-L)..L, ((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ))
        * ((Real.fourierChar (-((Real.log p - Real.log q) * ξ)) : Circle)
          : ℂ))).re|
      ≤ 1/(Real.pi * p * ((q:ℝ) - p)) := by
  have hq1 : 1 ≤ q := by omega
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  have hq0 : (0:ℝ) < q := by
    have : (0:ℕ) < q := by omega
    exact_mod_cast this
  have hqp0 : (0:ℝ) < (q:ℝ) - p := by
    have : ((p:ℝ)) < q := by exact_mod_cast hpq
    linarith
  have hπ := Real.pi_pos
  have hslt : Real.log p - Real.log q < 0 := by
    have := Real.log_lt_log hp0 (show (p:ℝ) < q by exact_mod_cast hpq)
    linarith
  have hs0 : Real.log p - Real.log q ≠ 0 := ne_of_lt hslt
  rw [intervalIntegral.integral_const_mul]
  have habs : |((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ))
      * ∫ ξ in (-L)..L, ((Real.fourierChar
          (-((Real.log p - Real.log q) * ξ)) : Circle) : ℂ)).re|
      ≤ (‖a p/(p:ℂ)‖ * ‖a q/(q:ℂ)‖) * ‖∫ ξ in (-L)..L,
          ((Real.fourierChar (-((Real.log p - Real.log q) * ξ)) : Circle)
            : ℂ)‖ := by
    refine le_trans (Complex.abs_re_le_norm _) ?_
    rw [norm_mul, norm_mul, RCLike.norm_conj]
  refine le_trans habs ?_
  have hker := norm_intervalIntegral_char_le hs0 L
  have hcp : ‖a p/(p:ℂ)‖ ≤ 1/p := by
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (ha p) hp0.le
  have hcq : ‖a q/(q:ℂ)‖ ≤ 1/q := by
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (ha q) hq0.le
  have hsabs : ((q:ℝ) - p)/q ≤ |Real.log p - Real.log q| := by
    rw [abs_of_neg hslt]
    have := log_sub_log_ge p q hp hpq
    linarith
  have hker2 : ‖∫ ξ in (-L)..L, ((Real.fourierChar
        (-((Real.log p - Real.log q) * ξ)) : Circle) : ℂ)‖
      ≤ (q:ℝ)/(Real.pi * ((q:ℝ) - p)) := by
    refine le_trans hker ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (0:ℝ) < |Real.log p - Real.log q| :=
      abs_pos.mpr hs0
    calc 1 * (Real.pi * ((q:ℝ) - p))
        = Real.pi * ((q:ℝ) - p) := by ring
      _ ≤ Real.pi * ((q:ℝ) * |Real.log p - Real.log q|) := by
          refine mul_le_mul_of_nonneg_left ?_ hπ.le
          calc (q:ℝ) - p = q * (((q:ℝ) - p)/q) := by field_simp
            _ ≤ q * |Real.log p - Real.log q| := by
                refine mul_le_mul_of_nonneg_left ?_ hq0.le
                have h2 := log_sub_log_ge p q hp hpq
                rw [abs_of_neg hslt]
                linarith
      _ = (q:ℝ) * (Real.pi * |Real.log p - Real.log q|) := by ring
  calc (‖a p/(p:ℂ)‖ * ‖a q/(q:ℂ)‖) * ‖∫ ξ in (-L)..L,
        ((Real.fourierChar (-((Real.log p - Real.log q) * ξ)) : Circle)
          : ℂ)‖
      ≤ ((1/(p:ℝ)) * (1/(q:ℝ))) * ((q:ℝ)/(Real.pi * ((q:ℝ) - p))) := by
        refine mul_le_mul ?_ hker2 (norm_nonneg _) (by positivity)
        exact mul_le_mul hcp hcq (norm_nonneg _) (by positivity)
    _ = 1/(Real.pi * p * ((q:ℝ) - p)) := by
        field_simp

/-- Conjugating a character coordinate flips the frequency. -/
theorem conj_char (u : ℝ) :
    (starRingEnd ℂ) ((Real.fourierChar u : Circle) : ℂ)
      = ((Real.fourierChar (-u) : Circle) : ℂ) := by
  rw [Real.fourierChar_apply, Real.fourierChar_apply, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- `‖z‖² = (z·conj z).re`. -/
theorem norm_sq_eq_mul_conj_re (z : ℂ) :
    ‖z‖^2 = (z * (starRingEnd ℂ) z).re := by
  rw [Complex.mul_conj, Complex.ofReal_re]
  exact (Complex.normSq_eq_norm_sq z).symm

/-- **The window energy of a prime-block phase sum** (C4a-1): with
coefficients `‖a p‖ ≤ 1` over a prime set `P ⊆ [1, P₂]`,
`∫_{−L}^{L} ‖∑_{p∈P} (a_p/p)·e(−ξ·log p)‖² dξ` is at most the diagonal
`2L·∑ 1/p²` plus the near-diagonal `O(loglog P₂)·∑ 1/p` — the block-length
never enters. -/
theorem intervalIntegral_norm_sq_phase_sum_le (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (P₂ : ℕ) (hP₂ : ∀ p ∈ P, p ≤ P₂)
    (h16 : 16 ≤ P₂) (a : ℕ → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1)
    (L : ℝ) (hL : 0 ≤ L) :
    ∫ ξ in (-L)..L,
        ‖∑ p ∈ P, (a p/(p:ℂ))
          * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖^2
      ≤ 2*L*(∑ p ∈ P, (1:ℝ)/(p:ℝ)^2)
        + (742 + 370*Real.log (Real.log P₂)) * (∑ p ∈ P, (1:ℝ)/p) := by
  classical
  have hp1 : ∀ p ∈ P, 1 ≤ p := fun p hp => (hP p hp).one_lt.le
  -- Stage A: the pointwise expansion
  have hexpand : ∀ ξ : ℝ,
      ‖∑ p ∈ P, (a p/(p:ℂ))
        * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖^2
      = ∑ p ∈ P, ∑ q ∈ P, (((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ)))
          * ((Real.fourierChar (-((Real.log p - Real.log q) * ξ)) : Circle)
            : ℂ)).re := by
    intro ξ
    rw [norm_sq_eq_mul_conj_re, map_sum, Finset.sum_mul_sum,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    rw [map_mul, mul_mul_mul_comm]
    congr 1
    exact char_mul_conj_char (Real.log p) (Real.log q) ξ
  -- Stage B: integrate and swap
  have hcont : ∀ p q : ℕ, Continuous (fun ξ : ℝ =>
      (((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ)))
        * ((Real.fourierChar (-((Real.log p - Real.log q) * ξ)) : Circle)
          : ℂ))) := by
    intro p q
    refine Continuous.mul continuous_const ?_
    exact continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (by fun_prop))
  have hcontre : ∀ p q : ℕ, Continuous (fun ξ : ℝ =>
      (((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ)))
        * ((Real.fourierChar (-((Real.log p - Real.log q) * ξ)) : Circle)
          : ℂ)).re) := fun p q => Complex.continuous_re.comp (hcont p q)
  rw [intervalIntegral.integral_congr (fun ξ _ => hexpand ξ)]
  rw [intervalIntegral.integral_finset_sum (fun p _ =>
    (continuous_finset_sum _ (fun q _ => hcontre p q)).intervalIntegrable
      _ _)]
  have hswap2 : ∀ p ∈ P, (∫ ξ in (-L)..L, ∑ q ∈ P,
        (((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ)))
          * ((Real.fourierChar (-((Real.log p - Real.log q) * ξ)) : Circle)
            : ℂ)).re)
      = ∑ q ∈ P, (∫ ξ in (-L)..L,
          (((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ)))
            * ((Real.fourierChar (-((Real.log p - Real.log q) * ξ)) : Circle)
              : ℂ))).re := by
    intro p _
    rw [intervalIntegral.integral_finset_sum (fun q _ =>
      (hcontre p q).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl fun q _ => ?_
    exact intervalIntegral_re _ ((hcont p q).intervalIntegrable _ _)
  rw [Finset.sum_congr rfl hswap2]
  -- Stage C: the pair symmetry for `q < p`
  have hsym : ∀ p q : ℕ, (∫ ξ in (-L)..L,
        (((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ)))
          * ((Real.fourierChar (-((Real.log p - Real.log q) * ξ)) : Circle)
            : ℂ))).re
      = (∫ ξ in (-L)..L,
        (((a q/(q:ℂ)) * (starRingEnd ℂ) (a p/(p:ℂ)))
          * ((Real.fourierChar (-((Real.log q - Real.log p) * ξ)) : Circle)
            : ℂ))).re := by
    intro p q
    rw [← intervalIntegral_re _ ((hcont p q).intervalIntegrable _ _),
      ← intervalIntegral_re _ ((hcont q p).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr (fun ξ _ => ?_)
    dsimp only
    have h1 : (((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ)))
        * ((Real.fourierChar (-((Real.log p - Real.log q) * ξ)) : Circle)
          : ℂ))
        = (starRingEnd ℂ) (((a q/(q:ℂ)) * (starRingEnd ℂ) (a p/(p:ℂ)))
          * ((Real.fourierChar (-((Real.log q - Real.log p) * ξ)) : Circle)
            : ℂ)) := by
      rw [map_mul, map_mul, Complex.conj_conj, conj_char]
      rw [show -(-((Real.log q - Real.log p) * ξ))
          = -((Real.log p - Real.log q) * ξ) from by ring]
      ring
    rw [h1, Complex.conj_re]
  -- Stage D: split and bound
  have hbound : ∀ p ∈ P, ∑ q ∈ P, (∫ ξ in (-L)..L,
        (((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ)))
          * ((Real.fourierChar (-((Real.log p - Real.log q) * ξ)) : Circle)
            : ℂ))).re
      ≤ 2*L*(1/(p:ℝ)^2)
        + (∑ q ∈ P.filter (fun q => q < p), 1/(Real.pi * q * ((p:ℝ) - q))
          + ∑ q ∈ P.filter (fun q => p < q), 1/(Real.pi * p * ((q:ℝ) - p))) := by
    intro p hp
    rw [← Finset.add_sum_erase P (fun q => (∫ ξ in (-L)..L,
      (((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ)))
        * ((Real.fourierChar (-((Real.log p - Real.log q) * ξ)) : Circle)
          : ℂ))).re) hp]
    have hdiag := pair_integral_diag_le a ha p (hp1 p hp) L hL
    have herase : ∑ q ∈ P.erase p, (∫ ξ in (-L)..L,
        (((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ)))
          * ((Real.fourierChar (-((Real.log p - Real.log q) * ξ)) : Circle)
            : ℂ))).re
        ≤ ∑ q ∈ P.filter (fun q => q < p), 1/(Real.pi * q * ((p:ℝ) - q))
          + ∑ q ∈ P.filter (fun q => p < q), 1/(Real.pi * p * ((q:ℝ) - p)) := by
      have hsplit : P.erase p
          = P.filter (fun q => q < p) ∪ P.filter (fun q => p < q) := by
        ext q
        simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro ⟨hne, hq⟩
          rcases lt_or_gt_of_ne hne with h | h
          · exact Or.inl ⟨hq, h⟩
          · exact Or.inr ⟨hq, h⟩
        · rintro (⟨hq, h⟩ | ⟨hq, h⟩) <;> exact ⟨by omega, hq⟩
      have hdisj : Disjoint (P.filter (fun q => q < p))
          (P.filter (fun q => p < q)) := by
        refine Finset.disjoint_left.mpr fun q hq1 hq2 => ?_
        rw [Finset.mem_filter] at hq1 hq2
        omega
      rw [hsplit, Finset.sum_union hdisj]
      refine add_le_add ?_ ?_
      · refine Finset.sum_le_sum fun q hq => ?_
        rw [Finset.mem_filter] at hq
        rw [hsym p q]
        calc (∫ ξ in (-L)..L,
              (((a q/(q:ℂ)) * (starRingEnd ℂ) (a p/(p:ℂ)))
                * ((Real.fourierChar (-((Real.log q - Real.log p) * ξ))
                  : Circle) : ℂ))).re
            ≤ |(∫ ξ in (-L)..L,
              (((a q/(q:ℂ)) * (starRingEnd ℂ) (a p/(p:ℂ)))
                * ((Real.fourierChar (-((Real.log q - Real.log p) * ξ))
                  : Circle) : ℂ))).re| := le_abs_self _
          _ ≤ 1/(Real.pi * q * ((p:ℝ) - q)) :=
              pair_integral_offdiag_le a ha q p (hp1 q hq.1) hq.2 L
      · refine Finset.sum_le_sum fun q hq => ?_
        rw [Finset.mem_filter] at hq
        calc (∫ ξ in (-L)..L,
              (((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ)))
                * ((Real.fourierChar (-((Real.log p - Real.log q) * ξ))
                  : Circle) : ℂ))).re
            ≤ |(∫ ξ in (-L)..L,
              (((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ)))
                * ((Real.fourierChar (-((Real.log p - Real.log q) * ξ))
                  : Circle) : ℂ))).re| := le_abs_self _
          _ ≤ 1/(Real.pi * p * ((q:ℝ) - p)) :=
              pair_integral_offdiag_le a ha p q (hp1 p hp) hq.2 L
    linarith [hdiag, herase]
  refine le_trans (Finset.sum_le_sum hbound) ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- the diagonal totals
  have hdiagtot : ∑ p ∈ P, 2*L*(1/(p:ℝ)^2) = 2*L*(∑ p ∈ P, (1:ℝ)/(p:ℝ)^2) := by
    rw [Finset.mul_sum]
  -- the gap sums: right halves
  have hgap : ∀ p ∈ P, ∑ q ∈ P.filter (fun q => p < q),
      1/(Real.pi * p * ((q:ℝ) - p))
      ≤ (1/(Real.pi * p)) * (742 + 370*Real.log (Real.log P₂)) := by
    intro p hp
    have h1 : ∑ q ∈ P.filter (fun q => p < q), 1/(Real.pi * p * ((q:ℝ) - p))
        = (1/(Real.pi * p)) * ∑ q ∈ P.filter (fun q => p < q),
            (1:ℝ)/((q:ℝ) - p) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [Finset.mem_filter] at hq
      have hqp : ((p:ℝ)) < q := by exact_mod_cast hq.2
      have hπ := Real.pi_pos
      have hp0 : (0:ℝ) < p := by exact_mod_cast hp1 p hp
      field_simp
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ (by
      have hπ := Real.pi_pos
      have hp0 : (0:ℝ) < p := by exact_mod_cast hp1 p hp
      positivity)
    have hsub : P.filter (fun q => p < q)
        ⊆ (Finset.Ioc p (p + P₂)).filter Nat.Prime := by
      intro q hq
      rw [Finset.mem_filter] at hq
      rw [Finset.mem_filter, Finset.mem_Ioc]
      have h2 := hP₂ q hq.1
      exact ⟨⟨hq.2, by omega⟩, hP q hq.1⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) ?_
    · intro q hq _
      rw [Finset.mem_filter, Finset.mem_Ioc] at hq
      have h3 : ((p:ℝ)) < q := by exact_mod_cast hq.1.1
      have h4 : (0:ℝ) < (q:ℝ) - p := by linarith
      positivity
    · exact sum_one_div_gap_le p P₂ h16
  -- the left halves: swap to right form via ite + sum_comm
  have hleft : ∑ p ∈ P, ∑ q ∈ P.filter (fun q => q < p),
      1/(Real.pi * q * ((p:ℝ) - q))
      = ∑ q ∈ P, ∑ p ∈ P.filter (fun p => q < p),
          1/(Real.pi * q * ((p:ℝ) - q)) := by
    have h1 : ∀ p ∈ P, ∑ q ∈ P.filter (fun q => q < p),
        1/(Real.pi * (q:ℝ) * ((p:ℝ) - q))
        = ∑ q ∈ P, if q < p then
            1/(Real.pi * (q:ℝ) * ((p:ℝ) - q)) else 0 := by
      intro p _
      rw [Finset.sum_filter]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_filter]
  rw [hdiagtot, hleft]
  -- both ordered halves obey the gap bound
  have htotal : ∀ S : ℝ, S = (742 + 370*Real.log (Real.log P₂)) → 
      (∑ q ∈ P, ∑ p ∈ P.filter (fun p => q < p),
          1/(Real.pi * q * ((p:ℝ) - q)))
        + ∑ p ∈ P, ∑ q ∈ P.filter (fun q => p < q),
            1/(Real.pi * p * ((q:ℝ) - p))
      ≤ S * (∑ p ∈ P, (1:ℝ)/p) := by
    intro S hS
    have hπ3 : (3:ℝ) ≤ Real.pi := by
      have := Real.pi_gt_three
      linarith
    have hG0 : (0:ℝ) ≤ 742 + 370*Real.log (Real.log P₂) := by
      have h1 : (1:ℝ) ≤ Real.log P₂ := by
        have h2 : Real.exp 1 ≤ 16 := by
          have := Real.exp_one_lt_d9
          linarith
        have h3 : ((16:ℕ):ℝ) ≤ P₂ := by exact_mod_cast h16
        calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
          _ ≤ Real.log P₂ := Real.log_le_log (Real.exp_pos 1) (by
              calc Real.exp 1 ≤ 16 := h2
                _ ≤ (P₂:ℝ) := by exact_mod_cast h16)
      have h4 : (0:ℝ) ≤ Real.log (Real.log P₂) := by
        rcases le_or_gt (Real.log (Real.log P₂)) 0 with h5 | h5
        · -- log(log P₂) with log P₂ ≥ 1: log ≥ 0
          have h6 := Real.log_nonneg h1
          linarith [h6]
        · linarith
      linarith
    have hhalf : ∀ r ∈ P, ∑ x ∈ P.filter (fun x => r < x),
        1/(Real.pi * r * ((x:ℝ) - r))
        ≤ (1/(Real.pi * r)) * (742 + 370*Real.log (Real.log P₂)) :=
      fun r hr => hgap r hr
    have hsum1 : ∑ q ∈ P, ∑ p ∈ P.filter (fun p => q < p),
        1/(Real.pi * q * ((p:ℝ) - q))
        ≤ ∑ q ∈ P, (1/(Real.pi * q)) * (742 + 370*Real.log (Real.log P₂)) :=
      Finset.sum_le_sum hhalf
    have hsum2 : ∑ p ∈ P, ∑ q ∈ P.filter (fun q => p < q),
        1/(Real.pi * p * ((q:ℝ) - p))
        ≤ ∑ p ∈ P, (1/(Real.pi * p)) * (742 + 370*Real.log (Real.log P₂)) :=
      Finset.sum_le_sum hhalf
    have hconv : ∑ r ∈ P, (1/(Real.pi * (r:ℝ)))
          * (742 + 370*Real.log (Real.log P₂))
        ≤ (1/2) * ((742 + 370*Real.log (Real.log P₂))
            * (∑ p ∈ P, (1:ℝ)/p)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun r hr => ?_
      have hr0 : (0:ℝ) < r := by exact_mod_cast hp1 r hr
      have h7 : 1/(Real.pi * (r:ℝ)) ≤ (1/2) * (1/r) := by
        rw [div_le_iff₀ (by positivity), mul_comm]
        rw [show Real.pi * (r:ℝ) * (1/2 * (1/(r:ℝ))) = Real.pi/2 from by
          field_simp]
        linarith
      calc 1/(Real.pi * (r:ℝ)) * (742 + 370*Real.log (Real.log P₂))
          ≤ ((1/2) * (1/r)) * (742 + 370*Real.log (Real.log P₂)) :=
            mul_le_mul_of_nonneg_right h7 hG0
        _ = (1/2) * ((742 + 370*Real.log (Real.log P₂)) * (1/r)) := by ring
    rw [hS]
    have h8 : (0:ℝ) ≤ ∑ p ∈ P, (1:ℝ)/p :=
      Finset.sum_nonneg fun p _ => by positivity
    nlinarith [hsum1, hsum2, hconv]
  have := htotal (742 + 370*Real.log (Real.log P₂)) rfl
  linarith [this]

end ExpSums

end MoltResearch
