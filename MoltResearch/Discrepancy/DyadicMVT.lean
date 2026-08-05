import MoltResearch.Discrepancy.LargeValues
import MoltResearch.Discrepancy.TuranKubilius
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Track C: the dyadic mean value theorem (Track R, C4d-1)

The `[MR]`-Lemma-14-style mean value theorem for `1`-bounded Dirichlet
polynomials with **integer** (not prime) support on a dyadic range: for
any `S ⊆ [N, 2N]`,

  `∫_{−L}^{L} ‖∑_{n∈S} (a_n/n)·e(−ξ log n)‖² dξ
     ≤ 2L·∑ 1/n² + (log N + 1)·∑ 1/n`

— diagonal plus one harmonic log. Runs on the same oscillation-kernel
toolkit as the C4a window energy (`pair_integral_diag_le`,
`pair_integral_offdiag_le`, which need only `1 ≤ n`); the off-diagonal
gap sums are harmonic (`k ↦ p ± k` reindexed into `[1, N]`) rather than
Brun–Titchmarsh, because integer support is dense.

This is the `∫|Q|²`-leg of the `𝒰`-moment machinery: in the `𝒯₁`
assembly (C4e) the short block-polynomial gets this MVT while the long
factor gets the pointwise Halász ratio bound (`HalaszEuler.lean`).
-/

open Finset

namespace MoltResearch

namespace ExpSums

/-- Harmonic gap sum, left half: for `S` with values `≥ N` and `p ≤ 2N`,
`∑_{q ∈ S, q < p} 1/(p − q) ≤ log N + 1`. -/
theorem sum_one_div_sub_filter_lt_le (N : ℕ) (S : Finset ℕ)
    (hSlow : ∀ n ∈ S, N ≤ n) (p : ℕ) (hp2N : p ≤ 2*N) :
    ∑ q ∈ S.filter (fun q => q < p), (1:ℝ)/((p:ℝ) - q)
      ≤ Real.log N + 1 := by
  classical
  set T := S.filter (fun q => q < p) with hT
  have hmem : ∀ q ∈ T, N ≤ q ∧ q < p := by
    intro q hq
    rw [hT, Finset.mem_filter] at hq
    exact ⟨hSlow q hq.1, hq.2⟩
  have hcast : ∀ q ∈ T, (1:ℝ)/((p:ℝ) - q) = (1:ℝ)/((p - q : ℕ) : ℝ) := by
    intro q hq
    congr 1
    rw [Nat.cast_sub (hmem q hq).2.le]
  rw [Finset.sum_congr rfl hcast]
  have hinj : Set.InjOn (fun q => p - q) ↑T := by
    intro q₁ h₁ q₂ h₂ h
    have m₁ := (hmem q₁ (Finset.mem_coe.mp h₁)).2
    have m₂ := (hmem q₂ (Finset.mem_coe.mp h₂)).2
    simp only at h
    omega
  have himg : ∑ q ∈ T, (1:ℝ)/((p - q : ℕ):ℝ)
      = ∑ k ∈ T.image (fun q => p - q), (1:ℝ)/(k:ℝ) :=
    (Finset.sum_image (f := fun k : ℕ => (1:ℝ)/(k:ℝ)) hinj).symm
  have hsub : T.image (fun q => p - q) ⊆ Finset.Ico 1 (N + 1) := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨q, hq, rfl⟩ := hk
    have h := hmem q hq
    rw [Finset.mem_Ico]
    omega
  calc ∑ q ∈ T, (1:ℝ)/((p - q : ℕ):ℝ)
      = ∑ k ∈ T.image (fun q => p - q), (1:ℝ)/(k:ℝ) := himg
    _ ≤ ∑ k ∈ Finset.Ico 1 (N + 1), (1:ℝ)/(k:ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun k _ _ => by positivity)
    _ ≤ Real.log N + 1 := sum_one_div_Ico_succ_le_log_add_one N

/-- Harmonic gap sum, right half: for `S` with values `≤ 2N` and `p ≥ N`,
`∑_{q ∈ S, p < q} 1/(q − p) ≤ log N + 1`. -/
theorem sum_one_div_sub_filter_gt_le (N : ℕ) (S : Finset ℕ)
    (hShigh : ∀ n ∈ S, n ≤ 2*N) (p : ℕ) (hpN : N ≤ p) :
    ∑ q ∈ S.filter (fun q => p < q), (1:ℝ)/((q:ℝ) - p)
      ≤ Real.log N + 1 := by
  classical
  set T := S.filter (fun q => p < q) with hT
  have hmem : ∀ q ∈ T, p < q ∧ q ≤ 2*N := by
    intro q hq
    rw [hT, Finset.mem_filter] at hq
    exact ⟨hq.2, hShigh q hq.1⟩
  have hcast : ∀ q ∈ T, (1:ℝ)/((q:ℝ) - p) = (1:ℝ)/((q - p : ℕ) : ℝ) := by
    intro q hq
    congr 1
    rw [Nat.cast_sub (hmem q hq).1.le]
  rw [Finset.sum_congr rfl hcast]
  have hinj : Set.InjOn (fun q => q - p) ↑T := by
    intro q₁ h₁ q₂ h₂ h
    have m₁ := (hmem q₁ (Finset.mem_coe.mp h₁)).1
    have m₂ := (hmem q₂ (Finset.mem_coe.mp h₂)).1
    simp only at h
    omega
  have himg : ∑ q ∈ T, (1:ℝ)/((q - p : ℕ):ℝ)
      = ∑ k ∈ T.image (fun q => q - p), (1:ℝ)/(k:ℝ) :=
    (Finset.sum_image (f := fun k : ℕ => (1:ℝ)/(k:ℝ)) hinj).symm
  have hsub : T.image (fun q => q - p) ⊆ Finset.Ico 1 (N + 1) := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨q, hq, rfl⟩ := hk
    have h := hmem q hq
    rw [Finset.mem_Ico]
    omega
  calc ∑ q ∈ T, (1:ℝ)/((q - p : ℕ):ℝ)
      = ∑ k ∈ T.image (fun q => q - p), (1:ℝ)/(k:ℝ) := himg
    _ ≤ ∑ k ∈ Finset.Ico 1 (N + 1), (1:ℝ)/(k:ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun k _ _ => by positivity)
    _ ≤ Real.log N + 1 := sum_one_div_Ico_succ_le_log_add_one N

/-- **The dyadic mean value theorem** (C4d-1): the window energy of a
`1`-bounded Dirichlet polynomial supported on any subset of `[N, 2N]`
is diagonal plus one harmonic log — the `[MR]`-Lemma-14-style MVT with
integer (not prime) support, on the same kernel toolkit as the C4a
window energy. -/
theorem intervalIntegral_norm_sq_dyadic_poly_le (N : ℕ) (hN : 1 ≤ N)
    (S : Finset ℕ) (hSlow : ∀ n ∈ S, N ≤ n) (hShigh : ∀ n ∈ S, n ≤ 2*N)
    (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (L : ℝ) (hL : 0 ≤ L) :
    ∫ ξ in (-L)..L,
        ‖∑ n ∈ S, (a n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2
      ≤ 2*L*(∑ n ∈ S, (1:ℝ)/(n:ℝ)^2)
        + (Real.log N + 1) * (∑ n ∈ S, (1:ℝ)/n) := by
  classical
  have hp1 : ∀ n ∈ S, 1 ≤ n := fun n hn => le_trans hN (hSlow n hn)
  -- Stage A: the pointwise expansion
  have hexpand : ∀ ξ : ℝ,
      ‖∑ p ∈ S, (a p/(p:ℂ))
        * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖^2
      = ∑ p ∈ S, ∑ q ∈ S, (((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ)))
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
  have hswap2 : ∀ p ∈ S, (∫ ξ in (-L)..L, ∑ q ∈ S,
        (((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ)))
          * ((Real.fourierChar (-((Real.log p - Real.log q) * ξ)) : Circle)
            : ℂ)).re)
      = ∑ q ∈ S, (∫ ξ in (-L)..L,
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
  -- Stage D: split and bound per row
  have hbound : ∀ p ∈ S, ∑ q ∈ S, (∫ ξ in (-L)..L,
        (((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ)))
          * ((Real.fourierChar (-((Real.log p - Real.log q) * ξ)) : Circle)
            : ℂ))).re
      ≤ 2*L*(1/(p:ℝ)^2)
        + (∑ q ∈ S.filter (fun q => q < p), 1/(Real.pi * q * ((p:ℝ) - q))
          + ∑ q ∈ S.filter (fun q => p < q), 1/(Real.pi * p * ((q:ℝ) - p))) := by
    intro p hp
    rw [← Finset.add_sum_erase S (fun q => (∫ ξ in (-L)..L,
      (((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ)))
        * ((Real.fourierChar (-((Real.log p - Real.log q) * ξ)) : Circle)
          : ℂ))).re) hp]
    have hdiag := pair_integral_diag_le a ha p (hp1 p hp) L hL
    have herase : ∑ q ∈ S.erase p, (∫ ξ in (-L)..L,
        (((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ)))
          * ((Real.fourierChar (-((Real.log p - Real.log q) * ξ)) : Circle)
            : ℂ))).re
        ≤ ∑ q ∈ S.filter (fun q => q < p), 1/(Real.pi * q * ((p:ℝ) - q))
          + ∑ q ∈ S.filter (fun q => p < q), 1/(Real.pi * p * ((q:ℝ) - p)) := by
      have hsplit : S.erase p
          = S.filter (fun q => q < p) ∪ S.filter (fun q => p < q) := by
        ext q
        simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro ⟨hne, hq⟩
          rcases lt_or_gt_of_ne hne with h | h
          · exact Or.inl ⟨hq, h⟩
          · exact Or.inr ⟨hq, h⟩
        · rintro (⟨hq, h⟩ | ⟨hq, h⟩) <;> exact ⟨by omega, hq⟩
      have hdisj : Disjoint (S.filter (fun q => q < p))
          (S.filter (fun q => p < q)) := by
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
  rw [Finset.sum_add_distrib]
  -- the gap halves, per row
  have hgaps : ∀ p ∈ S,
      (∑ q ∈ S.filter (fun q => q < p), 1/(Real.pi * q * ((p:ℝ) - q))
        + ∑ q ∈ S.filter (fun q => p < q), 1/(Real.pi * p * ((q:ℝ) - p)))
      ≤ (Real.log N + 1) * (1/(p:ℝ)) := by
    intro p hp
    have hpN := hSlow p hp
    have hp2N := hShigh p hp
    have hppos : (0:ℝ) < p := by
      have := hp1 p hp
      exact_mod_cast this
    have hπ := Real.pi_gt_three
    have hlogN : (0:ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
    -- left half: 1/q ≤ 2/p
    have hleft : ∑ q ∈ S.filter (fun q => q < p), 1/(Real.pi * q * ((p:ℝ) - q))
        ≤ (2/(Real.pi * p)) * (Real.log N + 1) := by
      have hpt : ∀ q ∈ S.filter (fun q => q < p),
          1/(Real.pi * q * ((p:ℝ) - q))
            ≤ 2/(Real.pi * p * ((p:ℝ) - q)) := by
        intro q hq
        rw [Finset.mem_filter] at hq
        have hqN := hSlow q hq.1
        have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hp1 q hq.1
        have hgap : (0:ℝ) < (p:ℝ) - q := by
          have h' : q < p := hq.2
          have h'' : (q:ℝ) < p := by exact_mod_cast h'
          linarith
        have hp2q : (p:ℝ) ≤ 2*q := by
          have h1 : p ≤ 2*N := hp2N
          have h2 : N ≤ q := hqN
          have h3 : (p:ℕ) ≤ 2*q := by omega
          exact_mod_cast h3
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ Real.pi) hgap.le)
          (by linarith : (0:ℝ) ≤ 2*(q:ℝ) - p)]
      calc ∑ q ∈ S.filter (fun q => q < p), 1/(Real.pi * q * ((p:ℝ) - q))
          ≤ ∑ q ∈ S.filter (fun q => q < p), 2/(Real.pi * p * ((p:ℝ) - q)) :=
            Finset.sum_le_sum hpt
        _ = (2/(Real.pi * p)) * ∑ q ∈ S.filter (fun q => q < p), (1:ℝ)/((p:ℝ) - q) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun q hq => ?_
            rw [div_mul_div_comm, mul_one]
        _ ≤ (2/(Real.pi * p)) * (Real.log N + 1) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact sum_one_div_sub_filter_lt_le N S hSlow p hp2N
    -- right half: direct factor
    have hright : ∑ q ∈ S.filter (fun q => p < q), 1/(Real.pi * p * ((q:ℝ) - p))
        ≤ (1/(Real.pi * p)) * (Real.log N + 1) := by
      have heq : ∑ q ∈ S.filter (fun q => p < q), 1/(Real.pi * p * ((q:ℝ) - p))
          = (1/(Real.pi * p)) * ∑ q ∈ S.filter (fun q => p < q), (1:ℝ)/((q:ℝ) - p) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q hq => ?_
        rw [div_mul_div_comm, mul_one]
      rw [heq]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact sum_one_div_sub_filter_gt_le N S hShigh p hpN
    calc (∑ q ∈ S.filter (fun q => q < p), 1/(Real.pi * q * ((p:ℝ) - q))
          + ∑ q ∈ S.filter (fun q => p < q), 1/(Real.pi * p * ((q:ℝ) - p)))
        ≤ (2/(Real.pi * p)) * (Real.log N + 1)
          + (1/(Real.pi * p)) * (Real.log N + 1) := add_le_add hleft hright
      _ = (3/(Real.pi * p)) * (Real.log N + 1) := by ring
      _ ≤ (1/(p:ℝ)) * (Real.log N + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [div_le_div_iff₀ (by positivity) hppos]
          nlinarith [hπ]
      _ = (Real.log N + 1) * (1/(p:ℝ)) := by ring
  -- total
  have hdiagtot : ∑ p ∈ S, 2*L*(1/(p:ℝ)^2) = 2*L*(∑ p ∈ S, (1:ℝ)/(p:ℝ)^2) := by
    rw [Finset.mul_sum]
  have hgaptot : ∑ p ∈ S,
      (∑ q ∈ S.filter (fun q => q < p), 1/(Real.pi * q * ((p:ℝ) - q))
        + ∑ q ∈ S.filter (fun q => p < q), 1/(Real.pi * p * ((q:ℝ) - p)))
      ≤ (Real.log N + 1) * (∑ p ∈ S, (1:ℝ)/p) := by
    calc ∑ p ∈ S, (∑ q ∈ S.filter (fun q => q < p), 1/(Real.pi * q * ((p:ℝ) - q))
          + ∑ q ∈ S.filter (fun q => p < q), 1/(Real.pi * p * ((q:ℝ) - p)))
        ≤ ∑ p ∈ S, (Real.log N + 1) * (1/(p:ℝ)) := Finset.sum_le_sum hgaps
      _ = (Real.log N + 1) * (∑ p ∈ S, (1:ℝ)/p) := by rw [Finset.mul_sum]
  linarith [hgaptot, le_of_eq hdiagtot]

/-- **The block Cauchy–Schwarz** (C4e-7): the squared norm of a
`w`-weighted combination of block values is at most the total weight
times the `w`-weighted energy — the pointwise splitting step that turns
`‖∑_p g(p)·G_p(ξ)‖²` into `(∑_p ‖g p‖)·∑_p ‖g p‖·‖G_p(ξ)‖²`, ready for
termwise integration against the dyadic MVT. -/
theorem norm_sq_sum_mul_le_sum_mul_sum (P : Finset ℕ) (w z : ℕ → ℂ) :
    ‖∑ p ∈ P, w p * z p‖^2
      ≤ (∑ p ∈ P, ‖w p‖) * (∑ p ∈ P, ‖w p‖ * ‖z p‖^2) := by
  have h1 : ‖∑ p ∈ P, w p * z p‖ ≤ ∑ p ∈ P, ‖w p‖ * ‖z p‖ := by
    refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
    exact Finset.sum_congr rfl fun p _ => norm_mul _ _
  have h2 : (∑ p ∈ P, ‖w p‖ * ‖z p‖)^2
      ≤ (∑ p ∈ P, ‖w p‖) * (∑ p ∈ P, ‖w p‖ * ‖z p‖^2) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq P
      (fun p => Real.sqrt ‖w p‖) (fun p => Real.sqrt ‖w p‖ * ‖z p‖)
    have hL : ∀ p ∈ P, Real.sqrt ‖w p‖ * (Real.sqrt ‖w p‖ * ‖z p‖)
        = ‖w p‖ * ‖z p‖ := by
      intro p _
      rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
    have hf : ∀ p ∈ P, Real.sqrt ‖w p‖ ^ 2 = ‖w p‖ := by
      intro p _
      exact Real.sq_sqrt (norm_nonneg _)
    have hg : ∀ p ∈ P, (Real.sqrt ‖w p‖ * ‖z p‖) ^ 2 = ‖w p‖ * ‖z p‖^2 := by
      intro p _
      rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
    rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hf,
      Finset.sum_congr rfl hg] at hcs
    exact hcs
  calc ‖∑ p ∈ P, w p * z p‖^2
      ≤ (∑ p ∈ P, ‖w p‖ * ‖z p‖)^2 := by
        have hnn : (0:ℝ) ≤ ‖∑ p ∈ P, w p * z p‖ := norm_nonneg _
        nlinarith [h1, hnn]
    _ ≤ (∑ p ∈ P, ‖w p‖) * (∑ p ∈ P, ‖w p‖ * ‖z p‖^2) := h2


/-- **The weighted-blocks window energy** (C4e-8): the window energy of a
`w`-weighted combination of `1`-bounded dyadic block polynomials is at
most the total weight times the weighted sum of the per-block MVT
bounds — C4e-7 pointwise under the integral, then the dyadic MVT on
each block. -/
theorem intervalIntegral_norm_sq_weighted_blocks_le (P : Finset ℕ) (w : ℕ → ℂ)
    (S : ℕ → Finset ℕ) (Nf : ℕ → ℕ) (a : ℕ → ℕ → ℂ)
    (hN : ∀ p ∈ P, 1 ≤ Nf p)
    (hSlow : ∀ p ∈ P, ∀ m ∈ S p, Nf p ≤ m)
    (hShigh : ∀ p ∈ P, ∀ m ∈ S p, m ≤ 2 * Nf p)
    (ha : ∀ p m, ‖a p m‖ ≤ 1) (L : ℝ) (hL : 0 ≤ L) :
    ∫ ξ in (-L)..L, ‖∑ p ∈ P, w p * ∑ m ∈ S p,
        (a p m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
      ≤ (∑ p ∈ P, ‖w p‖) * ∑ p ∈ P, ‖w p‖ *
          (2*L*(∑ m ∈ S p, (1:ℝ)/(m:ℝ)^2)
            + (Real.log (Nf p) + 1) * (∑ m ∈ S p, (1:ℝ)/m)) := by
  classical
  -- continuity of the block polynomials
  have hcontG : ∀ p : ℕ, Continuous (fun ξ : ℝ => ∑ m ∈ S p,
      (a p m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)) := by
    intro p
    refine continuous_finset_sum _ fun m _ => ?_
    refine Continuous.mul continuous_const ?_
    exact continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (by fun_prop))
  have hcontF : Continuous (fun ξ : ℝ => ‖∑ p ∈ P, w p * ∑ m ∈ S p,
      (a p m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2) := by
    refine Continuous.pow ?_ 2
    refine Continuous.norm ?_
    exact continuous_finset_sum _ fun p _ => (continuous_const.mul (hcontG p))
  have hcontR : Continuous (fun ξ : ℝ => ∑ p ∈ P, ‖w p‖ * ‖∑ m ∈ S p,
      (a p m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2) :=
    continuous_finset_sum _ fun p _ =>
      continuous_const.mul ((hcontG p).norm.pow 2)
  -- pointwise Cauchy–Schwarz
  have hpt : ∀ ξ ∈ Set.uIcc (-L) L, ‖∑ p ∈ P, w p * ∑ m ∈ S p,
      (a p m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
      ≤ (∑ p ∈ P, ‖w p‖) * ∑ p ∈ P, ‖w p‖ * ‖∑ m ∈ S p,
          (a p m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2 :=
    fun ξ _ => norm_sq_sum_mul_le_sum_mul_sum P w _
  -- integrate the pointwise bound
  have hstep1 : ∫ ξ in (-L)..L, ‖∑ p ∈ P, w p * ∑ m ∈ S p,
      (a p m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
      ≤ ∫ ξ in (-L)..L, (∑ p ∈ P, ‖w p‖) * ∑ p ∈ P, ‖w p‖ * ‖∑ m ∈ S p,
          (a p m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2 := by
    refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ ?_
    · exact hcontF.intervalIntegrable _ _
    · exact (continuous_const.mul hcontR).intervalIntegrable _ _
    · intro ξ hξ
      exact hpt ξ (Set.mem_uIcc_of_le hξ.1 hξ.2)
  refine le_trans hstep1 ?_
  -- pull the constant and split the sum
  rw [intervalIntegral.integral_const_mul]
  have hsum_nonneg : (0:ℝ) ≤ ∑ p ∈ P, ‖w p‖ :=
    Finset.sum_nonneg fun p _ => norm_nonneg _
  refine mul_le_mul_of_nonneg_left ?_ hsum_nonneg
  rw [intervalIntegral.integral_finset_sum (fun p _ =>
    (continuous_const.mul ((hcontG p).norm.pow 2)).intervalIntegrable _ _)]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [intervalIntegral.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact intervalIntegral_norm_sq_dyadic_poly_le (Nf p) (hN p hp) (S p)
    (hSlow p hp) (hShigh p hp) (a p) (ha p) L hL


/-- **The window sup-bound** (C4e-9): the energy of a continuous function
over an interval is at most the length times the squared sup — the
`𝒯₀`-leg's integral step: on the one window around the minimizing
frequency, the pointwise Halász ratio bound (`HalaszEuler.lean`) turns
into an energy bound at cost `(window length)`. -/
theorem intervalIntegral_norm_sq_le_of_bound (f : ℝ → ℂ) (c d M : ℝ)
    (hcd : c ≤ d) (hf : Continuous f)
    (hM : ∀ t ∈ Set.uIcc c d, ‖f t‖ ≤ M) :
    ∫ t in c..d, ‖f t‖^2 ≤ (d - c) * M^2 := by
  have hM0 : (0:ℝ) ≤ M := le_trans (norm_nonneg _) (hM c Set.left_mem_uIcc)
  calc ∫ t in c..d, ‖f t‖^2
      ≤ ∫ t in c..d, M^2 := by
        refine intervalIntegral.integral_mono_on hcd
          ((hf.norm.pow 2).intervalIntegrable _ _)
          intervalIntegrable_const fun t ht => ?_
        have hb := hM t (Set.mem_uIcc_of_le ht.1 ht.2)
        have hn : (0:ℝ) ≤ ‖f t‖ := norm_nonneg _
        nlinarith
    _ = (d - c) * M^2 := by
        rw [intervalIntegral.integral_const, smul_eq_mul]


/-- **The frequency-weighted blocks energy** (Track R, W2c-vi-a2): the
window energy of a combination of `1`-bounded dyadic block polynomials
with frequency-dependent weights of uniform size `v p` is at most the
total weight times the weighted per-block MVT bounds — C4e-8 with the
`char(p)/p`-type weights of the 𝒰-phase decomposition. -/
theorem intervalIntegral_norm_sq_freq_weighted_blocks_le (P : Finset ℕ)
    (w : ℕ → ℝ → ℂ) (v : ℕ → ℝ) (hw : ∀ p ξ, ‖w p ξ‖ ≤ v p)
    (hwcont : ∀ p, Continuous (w p))
    (S : ℕ → Finset ℕ) (Nf : ℕ → ℕ) (a : ℕ → ℕ → ℂ)
    (hN : ∀ p ∈ P, 1 ≤ Nf p)
    (hSlow : ∀ p ∈ P, ∀ m ∈ S p, Nf p ≤ m)
    (hShigh : ∀ p ∈ P, ∀ m ∈ S p, m ≤ 2 * Nf p)
    (ha : ∀ p m, ‖a p m‖ ≤ 1) (L : ℝ) (hL : 0 ≤ L) :
    ∫ ξ in (-L)..L, ‖∑ p ∈ P, w p ξ * ∑ m ∈ S p,
        (a p m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
      ≤ (∑ p ∈ P, v p) * ∑ p ∈ P, v p *
          (2*L*(∑ m ∈ S p, (1:ℝ)/(m:ℝ)^2)
            + (Real.log (Nf p) + 1) * (∑ m ∈ S p, (1:ℝ)/m)) := by
  classical
  have hv0 : ∀ p, 0 ≤ v p := fun p => le_trans (norm_nonneg _) (hw p 0)
  have hcontG : ∀ p : ℕ, Continuous (fun ξ : ℝ => ∑ m ∈ S p,
      (a p m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)) := by
    intro p
    refine continuous_finset_sum _ fun m _ => ?_
    refine Continuous.mul continuous_const ?_
    exact continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (by fun_prop))
  have hcontF : Continuous (fun ξ : ℝ => ‖∑ p ∈ P, w p ξ * ∑ m ∈ S p,
      (a p m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2) := by
    refine Continuous.pow ?_ 2
    refine Continuous.norm ?_
    exact continuous_finset_sum _ fun p _ => ((hwcont p).mul (hcontG p))
  have hcontR : Continuous (fun ξ : ℝ => ∑ p ∈ P, v p * ‖∑ m ∈ S p,
      (a p m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2) :=
    continuous_finset_sum _ fun p _ =>
      continuous_const.mul ((hcontG p).norm.pow 2)
  -- pointwise CS with the uniform weight sizes
  have hpt : ∀ ξ : ℝ, ‖∑ p ∈ P, w p ξ * ∑ m ∈ S p,
      (a p m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
      ≤ (∑ p ∈ P, v p) * ∑ p ∈ P, v p * ‖∑ m ∈ S p,
          (a p m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2 := by
    intro ξ
    have hcs := norm_sq_sum_mul_le_sum_mul_sum P (fun p => w p ξ)
      (fun p => ∑ m ∈ S p,
        (a p m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
    refine le_trans hcs ?_
    refine mul_le_mul (Finset.sum_le_sum fun p _ => hw p ξ)
      (Finset.sum_le_sum fun p _ => ?_)
      (Finset.sum_nonneg fun p _ => by positivity)
      (Finset.sum_nonneg fun p _ => hv0 p)
    exact mul_le_mul_of_nonneg_right (hw p ξ) (by positivity)
  have hstep1 : ∫ ξ in (-L)..L, ‖∑ p ∈ P, w p ξ * ∑ m ∈ S p,
      (a p m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
      ≤ ∫ ξ in (-L)..L, (∑ p ∈ P, v p) * ∑ p ∈ P, v p * ‖∑ m ∈ S p,
          (a p m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2 := by
    refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ ?_
    · exact hcontF.intervalIntegrable _ _
    · exact (continuous_const.mul hcontR).intervalIntegrable _ _
    · intro ξ _
      exact hpt ξ
  refine le_trans hstep1 ?_
  rw [intervalIntegral.integral_const_mul]
  have hsum_nonneg : (0:ℝ) ≤ ∑ p ∈ P, v p :=
    Finset.sum_nonneg fun p _ => hv0 p
  refine mul_le_mul_of_nonneg_left ?_ hsum_nonneg
  rw [intervalIntegral.integral_finset_sum (fun p _ =>
    (continuous_const.mul ((hcontG p).norm.pow 2)).intervalIntegrable _ _)]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [intervalIntegral.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (hv0 p)
  exact intervalIntegral_norm_sq_dyadic_poly_le (Nf p) (hN p hp) (S p)
    (hSlow p hp) (hShigh p hp) (a p) (ha p) L hL


/-- **The symbolic-fibres energy** (Track R, W2c-vii-a): the window
energy of a weighted combination of arbitrary continuous fibre
functions is at most the total weight times the weighted fibre
energies — the Cauchy–Schwarz half of the blocks energy with the fibre
integrals left symbolic, so the `J`-level recursion can bound them by
induction instead of the MVT. -/
theorem intervalIntegral_norm_sq_freq_weighted_sum_le (P : Finset ℕ)
    (w : ℕ → ℝ → ℂ) (v : ℕ → ℝ) (hw : ∀ p ξ, ‖w p ξ‖ ≤ v p)
    (hwcont : ∀ p, Continuous (w p))
    (z : ℕ → ℝ → ℂ) (hzcont : ∀ p, Continuous (z p))
    (L : ℝ) (hL : 0 ≤ L) :
    ∫ ξ in (-L)..L, ‖∑ p ∈ P, w p ξ * z p ξ‖^2
      ≤ (∑ p ∈ P, v p) * ∑ p ∈ P, v p * ∫ ξ in (-L)..L, ‖z p ξ‖^2 := by
  classical
  have hv0 : ∀ p, 0 ≤ v p := fun p => le_trans (norm_nonneg _) (hw p 0)
  have hcontF : Continuous (fun ξ : ℝ => ‖∑ p ∈ P, w p ξ * z p ξ‖^2) := by
    refine Continuous.pow ?_ 2
    refine Continuous.norm ?_
    exact continuous_finset_sum _ fun p _ => ((hwcont p).mul (hzcont p))
  have hcontR : Continuous (fun ξ : ℝ => ∑ p ∈ P, v p * ‖z p ξ‖^2) :=
    continuous_finset_sum _ fun p _ =>
      continuous_const.mul ((hzcont p).norm.pow 2)
  have hpt : ∀ ξ : ℝ, ‖∑ p ∈ P, w p ξ * z p ξ‖^2
      ≤ (∑ p ∈ P, v p) * ∑ p ∈ P, v p * ‖z p ξ‖^2 := by
    intro ξ
    have hcs := norm_sq_sum_mul_le_sum_mul_sum P (fun p => w p ξ)
      (fun p => z p ξ)
    refine le_trans hcs ?_
    refine mul_le_mul (Finset.sum_le_sum fun p _ => hw p ξ)
      (Finset.sum_le_sum fun p _ => ?_)
      (Finset.sum_nonneg fun p _ => by positivity)
      (Finset.sum_nonneg fun p _ => hv0 p)
    exact mul_le_mul_of_nonneg_right (hw p ξ) (by positivity)
  have hstep1 : ∫ ξ in (-L)..L, ‖∑ p ∈ P, w p ξ * z p ξ‖^2
      ≤ ∫ ξ in (-L)..L, (∑ p ∈ P, v p) * ∑ p ∈ P, v p * ‖z p ξ‖^2 := by
    refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ ?_
    · exact hcontF.intervalIntegrable _ _
    · exact (continuous_const.mul hcontR).intervalIntegrable _ _
    · intro ξ _
      exact hpt ξ
  refine le_trans hstep1 ?_
  rw [intervalIntegral.integral_const_mul]
  have hsum_nonneg : (0:ℝ) ≤ ∑ p ∈ P, v p :=
    Finset.sum_nonneg fun p _ => hv0 p
  refine mul_le_mul_of_nonneg_left ?_ hsum_nonneg
  rw [intervalIntegral.integral_finset_sum (fun p _ =>
    (continuous_const.mul ((hzcont p).norm.pow 2)).intervalIntegrable _ _)]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [intervalIntegral.integral_const_mul]


/-- **The general-support pair mean value** (Track R, M2-e): the
window energy of any `1`-bounded logarithmic Dirichlet polynomial is
at most the diagonal `2L·∑ 1/n²` plus the resolved off-diagonal pair
kernels `1/(π·min·gap)` — the dyadic MVT's stages with the support
left free, feeding the sieve-counted close-pair bounds of the cheap
Halász `L²` factors. -/
theorem intervalIntegral_norm_sq_poly_pairs_le
    (S : Finset ℕ) (hp1 : ∀ n ∈ S, 1 ≤ n)
    (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (L : ℝ) (hL : 0 ≤ L) :
    ∫ ξ in (-L)..L,
        ‖∑ n ∈ S, (a n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2
      ≤ 2*L*(∑ n ∈ S, (1:ℝ)/(n:ℝ)^2)
        + ∑ p ∈ S,
            (∑ q ∈ S.filter (fun q => q < p), 1/(Real.pi * q * ((p:ℝ) - q))
              + ∑ q ∈ S.filter (fun q => p < q), 1/(Real.pi * p * ((q:ℝ) - p))) := by
  classical
  -- Stage A: the pointwise expansion
  have hexpand : ∀ ξ : ℝ,
      ‖∑ p ∈ S, (a p/(p:ℂ))
        * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖^2
      = ∑ p ∈ S, ∑ q ∈ S, (((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ)))
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
  have hswap2 : ∀ p ∈ S, (∫ ξ in (-L)..L, ∑ q ∈ S,
        (((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ)))
          * ((Real.fourierChar (-((Real.log p - Real.log q) * ξ)) : Circle)
            : ℂ)).re)
      = ∑ q ∈ S, (∫ ξ in (-L)..L,
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
  -- Stage D: split and bound per row
  have hbound : ∀ p ∈ S, ∑ q ∈ S, (∫ ξ in (-L)..L,
        (((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ)))
          * ((Real.fourierChar (-((Real.log p - Real.log q) * ξ)) : Circle)
            : ℂ))).re
      ≤ 2*L*(1/(p:ℝ)^2)
        + (∑ q ∈ S.filter (fun q => q < p), 1/(Real.pi * q * ((p:ℝ) - q))
          + ∑ q ∈ S.filter (fun q => p < q), 1/(Real.pi * p * ((q:ℝ) - p))) := by
    intro p hp
    rw [← Finset.add_sum_erase S (fun q => (∫ ξ in (-L)..L,
      (((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ)))
        * ((Real.fourierChar (-((Real.log p - Real.log q) * ξ)) : Circle)
          : ℂ))).re) hp]
    have hdiag := pair_integral_diag_le a ha p (hp1 p hp) L hL
    have herase : ∑ q ∈ S.erase p, (∫ ξ in (-L)..L,
        (((a p/(p:ℂ)) * (starRingEnd ℂ) (a q/(q:ℂ)))
          * ((Real.fourierChar (-((Real.log p - Real.log q) * ξ)) : Circle)
            : ℂ))).re
        ≤ ∑ q ∈ S.filter (fun q => q < p), 1/(Real.pi * q * ((p:ℝ) - q))
          + ∑ q ∈ S.filter (fun q => p < q), 1/(Real.pi * p * ((q:ℝ) - p)) := by
      have hsplit : S.erase p
          = S.filter (fun q => q < p) ∪ S.filter (fun q => p < q) := by
        ext q
        simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro ⟨hne, hq⟩
          rcases lt_or_gt_of_ne hne with h | h
          · exact Or.inl ⟨hq, h⟩
          · exact Or.inr ⟨hq, h⟩
        · rintro (⟨hq, h⟩ | ⟨hq, h⟩) <;> exact ⟨by omega, hq⟩
      have hdisj : Disjoint (S.filter (fun q => q < p))
          (S.filter (fun q => p < q)) := by
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
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- **The large-values split, pointwise** (Track R, R2a): a value
threshold `V` converts a second moment against a bounded weight into a
`V²`-term plus a *fourth* moment.  For `u ≤ V` the first term already
dominates; for `u > V` the ratio `u²/V² > 1` upgrades the square to a
fourth power.  This is the measure-free form of the large-values
dichotomy — no set of large values is ever constructed. -/
theorem sq_mul_split (u v Sup V : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hvS : v ≤ Sup) (hV : 0 < V) :
    u^2*v^2 ≤ V^2*v^2 + (Sup^2/V^2)*u^4 := by
  have hSup0 : (0:ℝ) ≤ Sup := le_trans hv hvS
  rcases le_or_gt u V with h | h
  · have h1 : u^2*v^2 ≤ V^2*v^2 := by
      have : u^2 ≤ V^2 := by nlinarith
      nlinarith [sq_nonneg v]
    have h2 : (0:ℝ) ≤ (Sup^2/V^2)*u^4 := by positivity
    linarith
  · have hV2 : (0:ℝ) < V^2 := by positivity
    have hratio : V^2 ≤ u^2 := by nlinarith
    have hvs2 : v^2 ≤ Sup^2 := by nlinarith
    have hkey : u^2*v^2 ≤ (Sup^2/V^2)*u^4 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hV2]
      calc u^2*v^2*V^2 ≤ u^2*Sup^2*V^2 := by
            nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hvs2)
              (sq_nonneg u)) (sq_nonneg V)]
        _ ≤ Sup^2*u^4 := by
            nlinarith [mul_nonneg (mul_nonneg (sq_nonneg Sup) (sq_nonneg u))
              (sub_nonneg.mpr hratio)]
    nlinarith [sq_nonneg v, mul_nonneg (sq_nonneg V) (sq_nonneg v)]

/-- **The large-values split, integrated** (Track R, R2a): against a
uniformly bounded weight `g`, the weighted second moment of `f` splits
into a `V²`-multiple of the weight mass plus `Sup²/V²` times the
fourth moment of `f`.  Choosing `V` trades the two — the moment-method
form of Halász–Montgomery. -/
theorem intervalIntegral_sq_mul_split (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (a b Sup V : ℝ) (hab : a ≤ b)
    (hgS : ∀ ξ, ‖g ξ‖ ≤ Sup) (hV : 0 < V) :
    ∫ ξ in a..b, ‖f ξ‖^2*‖g ξ‖^2
      ≤ V^2*(∫ ξ in a..b, ‖g ξ‖^2)
        + (Sup^2/V^2)*(∫ ξ in a..b, ‖f ξ‖^4) := by
  have hint1 : IntervalIntegrable (fun ξ => ‖f ξ‖^2*‖g ξ‖^2) MeasureTheory.volume a b :=
    ((hf.norm.pow 2).mul (hg.norm.pow 2)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun ξ => ‖g ξ‖^2) MeasureTheory.volume a b :=
    (hg.norm.pow 2).intervalIntegrable _ _
  have hint3 : IntervalIntegrable (fun ξ => ‖f ξ‖^4) MeasureTheory.volume a b :=
    (hf.norm.pow 4).intervalIntegrable _ _
  have hmono : ∫ ξ in a..b, ‖f ξ‖^2*‖g ξ‖^2
      ≤ ∫ ξ in a..b, (V^2*‖g ξ‖^2 + (Sup^2/V^2)*‖f ξ‖^4) := by
    refine intervalIntegral.integral_mono_on hab hint1 ?_ ?_
    · exact ((hint2.const_mul _).add (hint3.const_mul _))
    · intro ξ _
      exact sq_mul_split (‖f ξ‖) (‖g ξ‖) Sup V (norm_nonneg _)
        (norm_nonneg _) (hgS ξ) hV
  calc ∫ ξ in a..b, ‖f ξ‖^2*‖g ξ‖^2
      ≤ ∫ ξ in a..b, (V^2*‖g ξ‖^2 + (Sup^2/V^2)*‖f ξ‖^4) := hmono
    _ = V^2*(∫ ξ in a..b, ‖g ξ‖^2)
        + (Sup^2/V^2)*(∫ ξ in a..b, ‖f ξ‖^4) := by
        rw [intervalIntegral.integral_add (hint2.const_mul _)
          (hint3.const_mul _), intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]

/-- **The large-values split at order `2k`** (Track R, R2b): the
value threshold `V` trades the weighted second moment for the
`2k`-th moment, at the cost of `V^{2k-2}` in the denominator.  For
`k = 1` this is trivial and for `k = 2` it is `sq_mul_split`; larger
`k` buys a stronger trade when higher moments of the polynomial are
available. -/
theorem sq_mul_split_pow (u v Sup V : ℝ) (k : ℕ) (hk : 1 ≤ k) (hu : 0 ≤ u)
    (hv : 0 ≤ v) (hvS : v ≤ Sup) (hV : 0 < V) :
    u^2*v^2 ≤ V^2*v^2 + (Sup^2/V^(2*k-2))*u^(2*k) := by
  have hSup0 : (0:ℝ) ≤ Sup := le_trans hv hvS
  have hVk : (0:ℝ) < V^(2*k-2) := by positivity
  rcases le_or_gt u V with h | h
  · have h1 : u^2*v^2 ≤ V^2*v^2 := by
      have h2 : u^2 ≤ V^2 := by nlinarith
      nlinarith [sq_nonneg v]
    have h2 : (0:ℝ) ≤ (Sup^2/V^(2*k-2))*u^(2*k) := by positivity
    linarith
  · -- above the threshold the ratio `u/V ≥ 1` upgrades the exponent
    have hV0 : (0:ℝ) < u := lt_of_lt_of_le hV h.le
    have hpow : V^(2*k-2)*u^2 ≤ u^(2*k) := by
      have hsplit : u^(2*k) = u^(2*k-2)*u^2 := by
        rw [← pow_add]
        congr 1
        omega
      rw [hsplit]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg u)
      exact pow_le_pow_left₀ hV.le h.le _
    have hvs2 : v^2 ≤ Sup^2 := by nlinarith
    have hkey : u^2*v^2 ≤ (Sup^2/V^(2*k-2))*u^(2*k) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hVk]
      calc u^2*v^2*V^(2*k-2) ≤ u^2*Sup^2*V^(2*k-2) := by
            nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hvs2)
              (sq_nonneg u)) hVk.le]
        _ = Sup^2*(V^(2*k-2)*u^2) := by ring
        _ ≤ Sup^2*u^(2*k) :=
            mul_le_mul_of_nonneg_left hpow (sq_nonneg Sup)
    nlinarith [sq_nonneg v, mul_nonneg (sq_nonneg V) (sq_nonneg v)]

/-- **The dyadic mean value theorem, weighted** (Track R, R2b): the
`1`-bounded hypothesis of `intervalIntegral_norm_sq_dyadic_poly_le`
relaxed to any uniform coefficient bound `B`, which the bound pays for
by `B²`.  The factored polynomials of the Ramaré decomposition carry
divisor-type coefficients, so the unnormalised form is the one the
large-values leg consumes. -/
theorem intervalIntegral_norm_sq_dyadic_poly_le_of_bound (N : ℕ) (hN : 1 ≤ N)
    (S : Finset ℕ) (hSlow : ∀ n ∈ S, N ≤ n) (hShigh : ∀ n ∈ S, n ≤ 2*N)
    (a : ℕ → ℂ) (B : ℝ) (hB : 0 < B) (ha : ∀ n, ‖a n‖ ≤ B)
    (L : ℝ) (hL : 0 ≤ L) :
    ∫ ξ in (-L)..L,
        ‖∑ n ∈ S, (a n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2
      ≤ B^2*(2*L*(∑ n ∈ S, (1:ℝ)/(n:ℝ)^2)
        + (Real.log N + 1) * (∑ n ∈ S, (1:ℝ)/n)) := by
  classical
  have hBne : (B:ℂ) ≠ 0 := by
    simpa using (ne_of_gt hB)
  -- normalise the coefficients
  have hnorm : ∀ n : ℕ, ‖(fun m => a m/(B:ℂ)) n‖ ≤ 1 := by
    intro n
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB,
      div_le_one hB]
    exact ha n
  have hbase := intervalIntegral_norm_sq_dyadic_poly_le N hN S hSlow hShigh
    (fun m => a m/(B:ℂ)) hnorm L hL
  have hpt : ∀ ξ : ℝ, ‖∑ n ∈ S, (a n/(n:ℂ))
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2
      = B^2 * ‖∑ n ∈ S, ((a n/(B:ℂ))/(n:ℂ))
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2 := by
    intro ξ
    have hfac : ∑ n ∈ S, (a n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)
        = (B:ℂ) * ∑ n ∈ S, ((a n/(B:ℂ))/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      field_simp
    rw [hfac, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hB]
  calc ∫ ξ in (-L)..L, ‖∑ n ∈ S, (a n/(n:ℂ))
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2
      = ∫ ξ in (-L)..L, B^2 * ‖∑ n ∈ S, ((a n/(B:ℂ))/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2 := by
        exact intervalIntegral.integral_congr (fun ξ _ => hpt ξ)
    _ = B^2 * ∫ ξ in (-L)..L, ‖∑ n ∈ S, ((a n/(B:ℂ))/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2 :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ B^2*(2*L*(∑ n ∈ S, (1:ℝ)/(n:ℝ)^2)
        + (Real.log N + 1) * (∑ n ∈ S, (1:ℝ)/n)) := by
        refine mul_le_mul_of_nonneg_left hbase (by positivity)

/-- **Abel summation on a block** (Track R, M0-b): the `1/n`-weighted
sum expressed through the partial sums — a boundary term at the top
and the telescoping weight `1/n − 1/(n+1)` inside. -/
theorem sum_div_eq_partial (c : ℕ → ℂ) (a : ℕ) (ha : 1 ≤ a) :
    ∀ b : ℕ, a ≤ b →
      ∑ n ∈ Finset.Icc a b, c n/(n:ℂ)
        = (∑ n ∈ Finset.Icc a b, c n)/(b:ℂ)
          + ∑ n ∈ Finset.Ico a b, (∑ m ∈ Finset.Icc a n, c m)
              * ((1:ℂ)/(n:ℂ) - (1:ℂ)/((n:ℂ)+1)) := by
  intro b hb
  induction b with
  | zero => omega
  | succ b ih =>
    rcases eq_or_lt_of_le hb with heq | hlt
    · subst heq
      simp
    · have hab : a ≤ b := by omega
      rw [Finset.sum_Icc_succ_top (by omega : a ≤ b + 1),
        Finset.sum_Icc_succ_top (by omega : a ≤ b + 1),
        Finset.sum_Ico_succ_top hab, ih hab]
      push_cast
      ring

/-- The telescoping weight sums to `1/a − 1/b`. -/
theorem sum_Ico_one_div_sub (a : ℕ) (ha : 1 ≤ a) :
    ∀ b : ℕ, a ≤ b →
      ∑ n ∈ Finset.Ico a b, ((1:ℝ)/(n:ℝ) - (1:ℝ)/((n:ℝ)+1))
        = (1:ℝ)/(a:ℝ) - (1:ℝ)/(b:ℝ) := by
  intro b hb
  induction b with
  | zero => omega
  | succ b ih =>
    rcases eq_or_lt_of_le hb with heq | hlt
    · subst heq
      simp
    · have hab : a ≤ b := by omega
      rw [Finset.sum_Ico_succ_top hab, ih hab]
      push_cast
      ring

/-- **The plain-to-logarithmic transfer** (Track R, M0-b): if every
partial sum of `c` over the block `[a, b]` has norm at most `B`, then
the `1/n`-weighted sum over that block has norm at most `B/a`.  This is
the step that hands a plain-sum Halász bound to the consumer, whose
object is the logarithmically weighted block sum: over a dyadic block
`1/n ≈ 1/a`, so no logarithm is lost. -/
theorem norm_sum_div_le_of_partial (c : ℕ → ℂ) (a b : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ b) (B : ℝ)
    (hB : ∀ u : ℕ, a ≤ u → u ≤ b → ‖∑ n ∈ Finset.Icc a u, c n‖ ≤ B) :
    ‖∑ n ∈ Finset.Icc a b, c n/(n:ℂ)‖ ≤ B/(a:ℝ) := by
  have ha0 : (0:ℝ) < a := by exact_mod_cast ha
  have hb0 : (0:ℝ) < b := by
    have h1 : 1 ≤ b := le_trans ha hab
    exact_mod_cast h1
  have hB0 : (0:ℝ) ≤ B := le_trans (norm_nonneg _) (hB a le_rfl hab)
  rw [sum_div_eq_partial c a ha b hab]
  refine le_trans (norm_add_le _ _) ?_
  have hhead : ‖(∑ n ∈ Finset.Icc a b, c n)/(b:ℂ)‖ ≤ B/(b:ℝ) := by
    rw [norm_div, Complex.norm_natCast]
    rw [div_le_div_iff₀ hb0 hb0]
    nlinarith [hB b hab le_rfl, hb0]
  have hstep : ∀ n ∈ Finset.Ico a b,
      ‖(∑ m ∈ Finset.Icc a n, c m) * ((1:ℂ)/(n:ℂ) - (1:ℂ)/((n:ℂ)+1))‖
        ≤ B * ((1:ℝ)/(n:ℝ) - (1:ℝ)/((n:ℝ)+1)) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn1 : 1 ≤ n := le_trans ha hn.1
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn1
    have hwnn : (0:ℝ) ≤ (1:ℝ)/(n:ℝ) - (1:ℝ)/((n:ℝ)+1) := by
      have h1 : (1:ℝ)/((n:ℝ)+1) ≤ (1:ℝ)/(n:ℝ) :=
        one_div_le_one_div_of_le hn0 (by linarith)
      linarith
    have hval : ((1:ℂ)/(n:ℂ) - (1:ℂ)/((n:ℂ)+1))
        = (((1:ℝ)/(n:ℝ) - (1:ℝ)/((n:ℝ)+1) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hval, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hwnn]
    exact mul_le_mul_of_nonneg_right (hB n hn.1 (le_of_lt hn.2)) hwnn
  have htail : ‖∑ n ∈ Finset.Ico a b, (∑ m ∈ Finset.Icc a n, c m)
        * ((1:ℂ)/(n:ℂ) - (1:ℂ)/((n:ℂ)+1))‖
      ≤ ∑ n ∈ Finset.Ico a b, B * ((1:ℝ)/(n:ℝ) - (1:ℝ)/((n:ℝ)+1)) :=
    le_trans (norm_sum_le _ _) (Finset.sum_le_sum hstep)
  have htel : ∑ n ∈ Finset.Ico a b, B * ((1:ℝ)/(n:ℝ) - (1:ℝ)/((n:ℝ)+1))
      = B * ((1:ℝ)/(a:ℝ) - (1:ℝ)/(b:ℝ)) := by
    rw [← Finset.mul_sum, sum_Ico_one_div_sub a ha b hab]
  rw [htel] at htail
  have hsplit : B/(a:ℝ) = B/(b:ℝ) + B * ((1:ℝ)/(a:ℝ) - (1:ℝ)/(b:ℝ)) := by
    field_simp
    ring
  rw [hsplit]
  linarith [hhead, htail]

open MeasureTheory Real in
/-- **The Gaussian majorant** (Track R, M0-f): `e^{π}e^{−πt²} ≥ 1`
exactly on `[−1,1]`.  This is the majorant of GHS Lemma 2.6 — they use
a Fejér-type `Φ` with compactly supported transform, but only rapid
decay of `𝓕Φ` is actually needed, and the Gaussian is its own
transform (`fourierIntegral_gaussian_pi`), which Mathlib supplies. -/
theorem one_le_gaussian_majorant {t : ℝ} (ht : |t| ≤ 1) :
    1 ≤ Real.exp π * Real.exp (-(π*t^2)) := by
  rw [← Real.exp_add]
  refine Real.one_le_exp ?_
  have h1 : t^2 ≤ 1 := by
    have := abs_le.mp ht
    nlinarith [this.1, this.2]
  nlinarith [Real.pi_pos]

open MeasureTheory Real in
/-- **The majorant step of GHS Lemma 2.6** (Track R, M0-f): a sharp
interval integral is dominated by the Gaussian-weighted integral over
the whole line.  The weight is `≥ 1` on `[−T,T]` and the integrand is
non-negative, so no cancellation is lost; on the frequency side the
Gaussian's own transform then localises the off-diagonal. -/
theorem intervalIntegral_norm_sq_le_gaussian (D : ℝ → ℂ) (hD : Continuous D)
    (C : ℝ) (hC : ∀ t, ‖D t‖ ≤ C) (T : ℝ) (hT : 0 < T) :
    ∫ t in (-T)..T, ‖D t‖^2
      ≤ ∫ t, ‖D t‖^2 * (Real.exp π * Real.exp (-(π*(t/T)^2))) := by
  have hC0 : (0:ℝ) ≤ C := le_trans (norm_nonneg _) (hC 0)
  -- the Gaussian weight is integrable
  have hgauss : Integrable (fun t : ℝ => Real.exp (-(π/T^2) * t^2)) := by
    refine integrable_exp_neg_mul_sq ?_
    positivity
  have hweight : ∀ t : ℝ, Real.exp (-(π*(t/T)^2)) = Real.exp (-(π/T^2) * t^2) := by
    intro t
    congr 1
    field_simp
  have hmajint : Integrable
      (fun t : ℝ => ‖D t‖^2 * (Real.exp π * Real.exp (-(π*(t/T)^2)))) := by
    refine Integrable.mono' ((hgauss.const_mul (C^2 * Real.exp π))) ?_ ?_
    · exact ((hD.norm.pow 2).mul
        (continuous_const.mul (by fun_prop))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hweight t]
      have hsq : ‖D t‖^2 ≤ C^2 := by
        have := hC t
        nlinarith [norm_nonneg (D t)]
      calc ‖D t‖^2 * (Real.exp π * Real.exp (-(π/T^2) * t^2))
          ≤ C^2 * (Real.exp π * Real.exp (-(π/T^2) * t^2)) := by
            refine mul_le_mul_of_nonneg_right hsq (by positivity)
        _ = C^2 * Real.exp π * Real.exp (-(π/T^2) * t^2) := by ring
  -- on the interval the weight is at least one
  have hstep : ∀ t ∈ Set.uIcc (-T) T, ‖D t‖^2
      ≤ ‖D t‖^2 * (Real.exp π * Real.exp (-(π*(t/T)^2))) := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    have habs : |t/T| ≤ 1 := by
      rw [abs_div, abs_of_pos hT, div_le_one hT]
      rcases abs_le.mp (abs_le.mpr ⟨ht.1, ht.2⟩) with ⟨h1, h2⟩
      exact abs_le.mpr ⟨h1, h2⟩
    have h1 := one_le_gaussian_majorant habs
    nlinarith [sq_nonneg ‖D t‖, norm_nonneg (D t)]
  have hle1 : ∫ t in (-T)..T, ‖D t‖^2
      ≤ ∫ t in (-T)..T, ‖D t‖^2 * (Real.exp π * Real.exp (-(π*(t/T)^2))) := by
    refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ ?_
    · exact ((hD.norm.pow 2)).intervalIntegrable _ _
    · exact hmajint.intervalIntegrable
    · intro t ht
      exact hstep t (by rw [Set.uIcc_of_le (by linarith)]; exact ht)
  refine le_trans hle1 ?_
  rw [intervalIntegral.integral_of_le (by linarith)]
  refine setIntegral_le_integral hmajint ?_
  refine Filter.Eventually.of_forall fun t => ?_
  positivity

open MeasureTheory Real Complex in
open scoped FourierTransform in
/-- **The scaled Gaussian transform** (Track R, M0-g): the Fourier
transform of the width-`T` Gaussian is the width-`1/T` Gaussian, with
the explicit factor `T`.  This is the frequency side of the majorant
`e^{π}e^{−π(t/T)²}` of `intervalIntegral_norm_sq_le_gaussian`: the
transform decays like `e^{−πT²ξ²}`, which is what localises the
off-diagonal of the mean value theorem to `|log(n/m)| ≲ 1/T`. -/
theorem fourier_gaussian_scaled {T : ℝ} (hT : 0 < T) :
    (𝓕 fun x : ℝ => ((Real.exp (-(π*(x/T)^2)) : ℝ) : ℂ))
      = fun ξ : ℝ => ((T : ℝ) : ℂ) * ((Real.exp (-(π*T^2*ξ^2)) : ℝ) : ℂ) := by
  have hTne : (T:ℝ) ≠ 0 := ne_of_gt hT
  set b : ℂ := ((1/T^2 : ℝ) : ℂ) with hb_def
  have hbre : 0 < b.re := by
    rw [hb_def, Complex.ofReal_re]
    positivity
  have hfun : (fun x : ℝ => ((Real.exp (-(π*(x/T)^2)) : ℝ) : ℂ))
      = fun x : ℝ => Complex.exp (-π * b * (x:ℂ)^2) := by
    funext x
    rw [Complex.ofReal_exp]
    congr 1
    rw [hb_def]
    push_cast
    field_simp
  have hbhalf : b^(1/2 : ℂ) = ((1/T : ℝ) : ℂ) := by
    have h1 : ((1/T^2 : ℝ)) ^ ((1/2 : ℝ)) = (1/T : ℝ) := by
      rw [show (1/T^2 : ℝ) = (1/T)^2 from by field_simp]
      rw [← Real.rpow_natCast (1/T) 2, ← Real.rpow_mul (by positivity)]
      norm_num
    calc b^(1/2 : ℂ) = ((1/T^2 : ℝ) : ℂ)^((((1/2 : ℝ)) : ℝ) : ℂ) := by
          rw [hb_def]
          congr 1
          push_cast
          ring
      _ = (((1/T^2 : ℝ) ^ ((1/2 : ℝ)) : ℝ) : ℂ) :=
          (Complex.ofReal_cpow (by positivity) _).symm
      _ = ((1/T : ℝ) : ℂ) := by rw [h1]
  rw [hfun, fourier_gaussian_pi hbre]
  funext ξ
  rw [hbhalf]
  have h2 : (1:ℂ)/((1/T : ℝ) : ℂ) = ((T:ℝ):ℂ) := by
    push_cast
    field_simp
  rw [h2]
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  rw [hb_def]
  push_cast
  field_simp

open MeasureTheory in
/-- **The weighted double-sum expansion** (Track R, M0-i): the
weighted mean square of a Dirichlet polynomial is the double sum of
its pair correlations against the weight.  This is the step of GHS
Lemma 2.6 that turns the Gaussian-majorised integral into an
arithmetic double sum; evaluating each pair integral as `𝓕W` at
`log m − log n` is the next step, and the Gaussian's transform is what
then localises the off-diagonal. -/
theorem integral_norm_sq_poly_weight_eq (S : Finset ℕ) (c : ℕ → ℂ)
    (W : ℝ → ℝ) (hWc : Continuous W) (hWi : Integrable W) :
    ∫ ξ, ‖∑ n ∈ S, c n
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2 * W ξ
      = ∑ m ∈ S, ∑ n ∈ S, ∫ ξ, (((c m * (starRingEnd ℂ) (c n))
          * ((Real.fourierChar (-((Real.log m - Real.log n) * ξ)) : Circle)
            : ℂ)).re) * W ξ := by
  classical
  -- the pointwise expansion, as in the dyadic mean value theorem
  have hexpand : ∀ ξ : ℝ,
      ‖∑ n ∈ S, c n
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2
      = ∑ m ∈ S, ∑ n ∈ S, ((c m * (starRingEnd ℂ) (c n))
          * ((Real.fourierChar (-((Real.log m - Real.log n) * ξ)) : Circle)
            : ℂ)).re := by
    intro ξ
    rw [norm_sq_eq_mul_conj_re, map_sum, Finset.sum_mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    rw [map_mul, mul_mul_mul_comm]
    congr 1
    exact char_mul_conj_char (Real.log m) (Real.log n) ξ
  -- each pair term is integrable against the weight
  have hterm : ∀ m n : ℕ, Integrable (fun ξ : ℝ =>
      (((c m * (starRingEnd ℂ) (c n))
        * ((Real.fourierChar (-((Real.log m - Real.log n) * ξ)) : Circle)
          : ℂ)).re) * W ξ) := by
    intro m n
    refine ((hWi.abs).const_mul (‖c m‖ * ‖c n‖)).mono' ?_ ?_
    · refine (Complex.continuous_re.comp ?_).mul hWc |>.aestronglyMeasurable
      refine continuous_const.mul ?_
      exact continuous_subtype_val.comp
        (Real.continuous_fourierChar.comp (by fun_prop))
    · refine Filter.Eventually.of_forall fun ξ => ?_
      set z : ℂ := (c m * (starRingEnd ℂ) (c n))
        * ((Real.fourierChar (-((Real.log m - Real.log n) * ξ)) : Circle) : ℂ)
        with hz_def
      have h1 : |z.re| ≤ ‖c m‖ * ‖c n‖ := by
        refine le_trans (Complex.abs_re_le_norm _) ?_
        rw [hz_def, norm_mul, norm_mul, norm_eq_of_mem_sphere, mul_one,
          RCLike.norm_conj]
      rw [Real.norm_eq_abs, abs_mul]
      calc |z.re| * |W ξ| ≤ (‖c m‖ * ‖c n‖) * |W ξ| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = ‖c m‖ * ‖c n‖ * |W ξ| := by ring
  -- expand, then exchange the finite sums with the integral
  have hpt : ∀ ξ : ℝ, ‖∑ n ∈ S, c n
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2 * W ξ
      = ∑ m ∈ S, ∑ n ∈ S, (((c m * (starRingEnd ℂ) (c n))
          * ((Real.fourierChar (-((Real.log m - Real.log n) * ξ)) : Circle)
            : ℂ)).re) * W ξ := by
    intro ξ
    rw [hexpand ξ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by rw [Finset.sum_mul]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [MeasureTheory.integral_finset_sum _ (fun m _ =>
    MeasureTheory.integrable_finset_sum _ (fun n _ => hterm m n))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MeasureTheory.integral_finset_sum _ (fun n _ => hterm m n)]

open MeasureTheory in
/-- **The pair integral is a transform value** (Track R, M0-j): each
pair term of the weighted double-sum expansion is the real part of the
coefficient product against `𝓕W` at the log-difference.  With the
Gaussian weight of `intervalIntegral_norm_sq_le_gaussian` this is
where the localisation enters: `𝓕W` at `log m − log n` decays like
`e^{−πT²(log m − log n)²}`, so only `|n − m| ≪ m/T` survives. -/
theorem integral_re_char_mul_weight (z : ℂ) (v : ℝ) (W : ℝ → ℝ)
    (hWc : Continuous W) (hWi : Integrable W) :
    ∫ ξ, ((z * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ)).re) * W ξ
      = (z * ∫ ξ, ((W ξ : ℝ) : ℂ)
          * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ)).re := by
  classical
  have hchar : Continuous fun ξ : ℝ =>
      ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ) :=
    continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (by fun_prop))
  -- the complex integrand is integrable: the character has modulus one
  have hint : Integrable fun ξ : ℝ => ((W ξ : ℝ) : ℂ)
      * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ) := by
    refine ((hWi.abs).const_mul 1).mono' ?_ ?_
    · exact ((Complex.continuous_ofReal.comp hWc).mul hchar).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ξ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_eq_of_mem_sphere,
        mul_one, one_mul]
  have hintz : Integrable fun ξ : ℝ => z * (((W ξ : ℝ) : ℂ)
      * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ)) := hint.const_mul z
  -- the integrands agree pointwise, then `re` exchanges with the integral
  have hpt : ∀ ξ : ℝ,
      ((z * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ)).re) * W ξ
      = (z * (((W ξ : ℝ) : ℂ)
          * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ))).re := by
    intro ξ
    rw [show z * (((W ξ : ℝ) : ℂ)
          * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ))
        = (z * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ))
          * ((W ξ : ℝ) : ℂ) from by ring]
    conv_rhs => rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  calc ∫ ξ, ((z * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ)).re) * W ξ
      = ∫ ξ, (z * (((W ξ : ℝ) : ℂ)
          * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ))).re :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ ξ, z * (((W ξ : ℝ) : ℂ)
          * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ))).re :=
        integral_re hintz
    _ = (z * ∫ ξ, ((W ξ : ℝ) : ℂ)
          * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ)).re := by
        rw [MeasureTheory.integral_const_mul]

/-- **The symmetric pair bound** (Track R, M0-k): against a
non-negative symmetric kernel, the double sum of pair correlations
collapses to a diagonal sum.  This is the `2|a(m)a(n)| ≤ |a(m)|² +
|a(n)|²` step of GHS Lemma 2.6: the cross terms are traded for squares
and the symmetry of the kernel folds the two halves together, leaving
one factor free for the Brun–Titchmarsh count. -/
theorem sum_pair_re_le_of_symm (S : Finset ℕ) (c : ℕ → ℂ) (K : ℕ → ℕ → ℝ)
    (hK0 : ∀ m n, 0 ≤ K m n) (hKsymm : ∀ m n, K m n = K n m) :
    ∑ m ∈ S, ∑ n ∈ S, (c m * (starRingEnd ℂ) (c n)).re * K m n
      ≤ ∑ m ∈ S, ‖c m‖^2 * ∑ n ∈ S, K m n := by
  classical
  -- the cross term is at most the average of the squares
  have hstep : ∀ m n : ℕ, (c m * (starRingEnd ℂ) (c n)).re * K m n
      ≤ ((‖c m‖^2 + ‖c n‖^2)/2) * K m n := by
    intro m n
    refine mul_le_mul_of_nonneg_right ?_ (hK0 m n)
    have h1 : (c m * (starRingEnd ℂ) (c n)).re ≤ ‖c m‖ * ‖c n‖ := by
      refine le_trans (Complex.re_le_norm _) ?_
      rw [norm_mul, RCLike.norm_conj]
    nlinarith [sq_nonneg (‖c m‖ - ‖c n‖), h1]
  refine le_trans (Finset.sum_le_sum fun m _ =>
    Finset.sum_le_sum fun n _ => hstep m n) ?_
  -- split the average into the two halves
  have hsplit : ∑ m ∈ S, ∑ n ∈ S, ((‖c m‖^2 + ‖c n‖^2)/2) * K m n
      = (∑ m ∈ S, ∑ n ∈ S, (‖c m‖^2/2) * K m n)
        + ∑ m ∈ S, ∑ n ∈ S, (‖c n‖^2/2) * K m n := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  -- the second half is the first, after exchanging the indices
  have hswap : ∑ m ∈ S, ∑ n ∈ S, (‖c n‖^2/2) * K m n
      = ∑ m ∈ S, ∑ n ∈ S, (‖c m‖^2/2) * K m n := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hKsymm n m]
  rw [hsplit, hswap]
  have hcollect : (∑ m ∈ S, ∑ n ∈ S, (‖c m‖^2/2) * K m n)
      + ∑ m ∈ S, ∑ n ∈ S, (‖c m‖^2/2) * K m n
      = ∑ m ∈ S, ‖c m‖^2 * ∑ n ∈ S, K m n := by
    rw [← two_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hcollect]

open Real in
/-- **Gaussian decay from an integer gap** (Track R, M0-l): if `n` lies
in the dyadic window `(m, 2m]` and is at least `d` away from `m`, the
Gaussian factor at the log-difference already decays like
`e^{−πT²d²/(4m²)}`.  This is the shell estimate of GHS Lemma 2.6: with
`d = 2^{j}·m/T` the exponent is `π4^{j}/4`, so the shells are killed
super-exponentially and only `|n − m| ≪ m/T` contributes. -/
theorem gaussian_decay_of_gap (T : ℝ) (m n : ℕ) (hm : 1 ≤ m) (hmn : m < n)
    (hn2 : n ≤ 2*m) (d : ℝ) (hd0 : 0 ≤ d) (hd : d ≤ (n:ℝ) - m) :
    Real.exp (-(π*T^2*(Real.log n - Real.log m)^2))
      ≤ Real.exp (-(π*T^2*d^2/(4*(m:ℝ)^2))) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hn0 : (0:ℝ) < n := by
    have : (0:ℕ) < n := by omega
    exact_mod_cast this
  have hn2R : (n:ℝ) ≤ 2*m := by exact_mod_cast hn2
  -- the log-difference dominates the normalised gap
  have hlog : ((n:ℝ) - m)/n ≤ Real.log n - Real.log m :=
    log_sub_log_ge m n hm hmn
  have hgap : d/(2*(m:ℝ)) ≤ Real.log n - Real.log m := by
    refine le_trans ?_ hlog
    rw [div_le_div_iff₀ (by positivity) hn0]
    nlinarith [hd, hn2R, hm0, hd0]
  have hlog0 : (0:ℝ) ≤ Real.log n - Real.log m :=
    le_trans (by positivity) hgap
  -- squaring is monotone on the non-negatives
  have hsq : (d/(2*(m:ℝ)))^2 ≤ (Real.log n - Real.log m)^2 := by
    refine pow_le_pow_left₀ (by positivity) hgap 2
  refine Real.exp_le_exp.mpr ?_
  have hkey : π*T^2*d^2/(4*(m:ℝ)^2) ≤ π*T^2*(Real.log n - Real.log m)^2 := by
    have hd2 : d^2/(4*(m:ℝ)^2) = (d/(2*(m:ℝ)))^2 := by
      field_simp
      ring
    have hpi : (0:ℝ) ≤ π*T^2 := by positivity
    calc π*T^2*d^2/(4*(m:ℝ)^2) = (π*T^2)*(d^2/(4*(m:ℝ)^2)) := by ring
      _ = (π*T^2)*((d/(2*(m:ℝ)))^2) := by rw [hd2]
      _ ≤ (π*T^2)*((Real.log n - Real.log m)^2) :=
          mul_le_mul_of_nonneg_left hsq hpi
      _ = π*T^2*(Real.log n - Real.log m)^2 := by ring
  linarith

open Finset Real in
/-- **The shell series converges** (Track R, M0-m): the dyadic shell
count `2^j` against the Gaussian shell decay `e^{−(π/4)4^j}` sums to at
most `1`, uniformly in the number of shells.  Each term is already
below `2^{−j−1}`, because `(π/4)·4^j ≥ (2j+1)·log 2` — the quadratic
Gaussian exponent beats the linear count. -/
theorem sum_shell_series_le (J : ℕ) :
    ∑ j ∈ Finset.range J, (2:ℝ)^j * Real.exp (-(π/4 * 4^j)) ≤ 1 := by
  classical
  have hlog2 : Real.log 2 < 0.6932 := by
    have := Real.log_two_lt_d9
    linarith
  have hpi : (3:ℝ) < π := Real.pi_gt_three
  have hbern : ∀ j : ℕ, (1:ℝ) + 3*j ≤ (4:ℝ)^j := by
    intro j
    have h := one_add_mul_le_pow (a := (3:ℝ)) (by norm_num) j
    calc (1:ℝ) + 3*j = 1 + j*3 := by ring
      _ ≤ (1+3)^j := h
      _ = (4:ℝ)^j := by norm_num
  have hstep : ∀ j : ℕ,
      (2:ℝ)^j * Real.exp (-(π/4 * 4^j)) ≤ (1/2:ℝ)^(j+1) := by
    intro j
    have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    have hexp : (2*(j:ℝ)+1) * Real.log 2 ≤ π/4 * 4^j := by
      have h1 : (2*(j:ℝ)+1) * Real.log 2 ≤ (2*(j:ℝ)+1) * 0.6932 :=
        mul_le_mul_of_nonneg_left hlog2.le (by linarith)
      have h2 : (2*(j:ℝ)+1) * 0.6932 ≤ (3/4 : ℝ) * (1 + 3*(j:ℝ)) := by
        nlinarith [hj0]
      have h3 : (3/4 : ℝ) * (1 + 3*(j:ℝ)) ≤ (π/4) * (1 + 3*(j:ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have h4 : (π/4) * (1 + 3*(j:ℝ)) ≤ (π/4) * (4:ℝ)^j :=
        mul_le_mul_of_nonneg_left (hbern j) (by positivity)
      linarith
    have hval : (1/2:ℝ)^(2*j+1) = Real.exp (-((2*(j:ℝ)+1) * Real.log 2)) := by
      have h1 : ((1:ℝ)/2)^(2*j+1) = Real.exp (Real.log (((1:ℝ)/2)^(2*j+1))) :=
        (Real.exp_log (by positivity)).symm
      rw [h1, Real.log_pow, Real.log_div one_ne_zero two_ne_zero, Real.log_one]
      congr 1
      push_cast
      ring
    have hpow : Real.exp (-(π/4 * 4^j)) ≤ (1/2:ℝ)^(2*j+1) := by
      rw [hval]
      exact Real.exp_le_exp.mpr (by linarith)
    have hcollapse : (2:ℝ)^j * (1/2:ℝ)^(2*j+1) = (1/2:ℝ)^(j+1) := by
      have e1 : (2:ℝ)^(2*j+1) = (2:ℝ)^j * (2:ℝ)^(j+1) := by
        rw [← pow_add]
        congr 1
        omega
      rw [one_div, inv_pow, inv_pow, e1]
      field_simp
    calc (2:ℝ)^j * Real.exp (-(π/4 * 4^j))
        ≤ (2:ℝ)^j * (1/2:ℝ)^(2*j+1) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (1/2:ℝ)^(j+1) := hcollapse
  refine le_trans (Finset.sum_le_sum fun j _ => hstep j) ?_
  have hgeom : ∑ j ∈ Finset.range J, (1/2:ℝ)^(j+1)
      = (1/2:ℝ) * ∑ j ∈ Finset.range J, (1/2:ℝ)^j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ]
    ring
  rw [hgeom]
  have h2 : ∑ j ∈ Finset.range J, (1/2:ℝ)^j ≤ 2 := sum_geometric_two_le J
  linarith

/-- **The shell split** (Track R, M0-n): a sum over `(m, m + a J]`
breaks into the shells `(m + a j, m + a (j+1)]`.  This is the skeleton
of the dyadic decomposition in GHS Lemma 2.6, where `a j = 2^j·⌈m/T⌉`:
the Gaussian decay is estimated once per shell (`gaussian_decay_of_gap`)
and the count once per shell (`sum_log_primes_Ioc_le`), then the shells
are summed by `sum_shell_series_le`. -/
theorem sum_Ioc_shell_split {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (m : ℕ) (a : ℕ → ℕ) (ha0 : a 0 = 0) (hmono : Monotone a) :
    ∀ J : ℕ, ∑ n ∈ Finset.Ioc m (m + a J), f n
      = ∑ j ∈ Finset.range J,
          ∑ n ∈ Finset.Ioc (m + a j) (m + a (j+1)), f n := by
  intro J
  induction J with
  | zero => simp [ha0]
  | succ J ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact (Finset.sum_Ioc_consecutive f
      (by omega : m ≤ m + a J)
      (by
        have h := hmono (show J ≤ J + 1 by omega)
        omega : m + a J ≤ m + a (J+1))).symm

open Finset Real in
/-- **The single-shell bound** (Track R, M0-o): on a shell
`(u, v] ⊆ (m, 2m]`, the Gaussian-weighted prime log-mass is at most the
shell's decay factor times its Brun–Titchmarsh count.  This is the atom
of the dyadic sum in GHS Lemma 2.6: the decay is uniform over the shell
because the gap `u − m` is a lower bound for every `p` in it, and the
count is `#{p ∈ (u,v]}·log` from the sieve. -/
theorem shell_gaussian_count_le (T : ℝ) (m u v : ℕ) (hm : 1 ≤ m)
    (hmu : m ≤ u) (huv : u < v) (hv : v ≤ 2*m) (hK : 2 ≤ v - u) :
    ∑ p ∈ (Finset.Ioc u v).filter Nat.Prime,
        Real.log p * Real.exp (-(π*T^2*(Real.log p - Real.log m)^2))
      ≤ Real.exp (-(π*T^2*((u:ℝ) - m)^2/(4*(m:ℝ)^2)))
        * (256*((v:ℝ)-(u:ℝ))*Real.log ((u:ℝ) + ((v:ℝ)-(u:ℝ)) + 2)
            /Real.log ((v:ℝ)-(u:ℝ))) := by
  classical
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  -- the shell's decay factor dominates every term
  have hdecay : ∀ p ∈ (Finset.Ioc u v).filter Nat.Prime,
      Real.log p * Real.exp (-(π*T^2*(Real.log p - Real.log m)^2))
        ≤ Real.exp (-(π*T^2*((u:ℝ) - m)^2/(4*(m:ℝ)^2))) * Real.log p := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    have hmp : m < p := lt_of_le_of_lt hmu hp.1.1
    have hp2m : p ≤ 2*m := le_trans hp.1.2 hv
    have hdle : ((u:ℝ) - m) ≤ (p:ℝ) - m := by
      have : (u:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.1.1.le
      linarith
    have hd0 : (0:ℝ) ≤ (u:ℝ) - m := by
      have : (m:ℝ) ≤ (u:ℝ) := by exact_mod_cast hmu
      linarith
    have hg := gaussian_decay_of_gap T m p hm hmp hp2m ((u:ℝ) - m) hd0 hdle
    have hlogp : (0:ℝ) ≤ Real.log p := by
      refine Real.log_nonneg ?_
      have : (1:ℕ) ≤ p := hp.2.one_lt.le
      exact_mod_cast this
    calc Real.log p * Real.exp (-(π*T^2*(Real.log p - Real.log m)^2))
        ≤ Real.log p * Real.exp (-(π*T^2*((u:ℝ) - m)^2/(4*(m:ℝ)^2))) :=
          mul_le_mul_of_nonneg_left hg hlogp
      _ = Real.exp (-(π*T^2*((u:ℝ) - m)^2/(4*(m:ℝ)^2))) * Real.log p := by
          ring
  refine le_trans (Finset.sum_le_sum hdecay) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  -- the sieve count on the shell
  have hvu : v = u + (v - u) := by omega
  have hcount := sum_log_primes_Ioc_le u (v - u) hK
  have hcast : ((v - u : ℕ) : ℝ) = (v:ℝ) - (u:ℝ) := by
    have : u ≤ v := huv.le
    push_cast [Nat.cast_sub this]
    ring
  rw [← hvu] at hcount
  rw [hcast] at hcount
  exact hcount

open Real in
/-- **The shell exponent meets the series** (Track R, M0-p): at the
dyadic scale `h ≥ 2m/T`, the shell-`j` decay of `gaussian_decay_of_gap`
is at least the `e^{−(π/4)4^j}` demanded by `sum_shell_series_le`.  The
two halves of the shell estimate are calibrated by this one inequality:
`(2^j − 1)² ≥ 4^{j−1}` for `j ≥ 1`, and the scale condition supplies the
remaining factor `4`. -/
theorem shell_exponent_le (T m h : ℝ) (hm : 0 < m) (hh : 0 ≤ h)
    (hhT : 2*m ≤ h*T) {j : ℕ} (hj : 1 ≤ j) :
    Real.exp (-(π*T^2*((2^j - 1)*h)^2/(4*m^2)))
      ≤ Real.exp (-(π/4 * 4^j)) := by
  have hm2 : (0:ℝ) < m^2 := by positivity
  have hT0 : (0:ℝ) < T := by
    by_contra hT
    push_neg at hT
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hh hT]
  -- `2^j − 1 ≥ 2^{j−1}` for `j ≥ 1`
  have hhalf : (2:ℝ)^(j-1) ≤ (2:ℝ)^j - 1 := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have h1 : (1:ℝ) ≤ (2:ℝ)^i := one_le_pow₀ (by norm_num)
    calc (2:ℝ)^i = 2*(2:ℝ)^i - (2:ℝ)^i := by ring
      _ ≤ 2*(2:ℝ)^i - 1 := by linarith
      _ = (2:ℝ)^(i+1) - 1 := by rw [pow_succ]; ring
  have hpow0 : (0:ℝ) ≤ (2:ℝ)^(j-1) := by positivity
  -- so `(2^j − 1)² ≥ 4^{j−1}`, and the scale condition gives the factor 4
  have h4sq : ((2:ℝ)^(j-1))^2 = (4:ℝ)^(j-1) := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hsq : (4:ℝ)^(j-1) ≤ ((2:ℝ)^j - 1)^2 := by
    rw [← h4sq]
    exact pow_le_pow_left₀ hpow0 hhalf 2
  have h4j : (4:ℝ)^j = 4 * (4:ℝ)^(j-1) := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [pow_succ]
    ring
  refine Real.exp_le_exp.mpr ?_
  have hstep : (4:ℝ)^j * m^2 ≤ T^2*((2^j-1)*h)^2 := by
    have hscale : 4*m^2 ≤ (h*T)^2 := by nlinarith [hhT, hm]
    calc (4:ℝ)^j * m^2 = 4*(4:ℝ)^(j-1) * m^2 := by rw [h4j]
      _ ≤ 4*((2:ℝ)^j-1)^2 * m^2 := by nlinarith [hsq, hm2]
      _ = ((2:ℝ)^j-1)^2 * (4*m^2) := by ring
      _ ≤ ((2:ℝ)^j-1)^2 * (h*T)^2 :=
          mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = T^2*((2^j-1)*h)^2 := by ring
  have hkey : π/4 * 4^j ≤ π*T^2*((2^j - 1)*h)^2/(4*m^2) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 4*m^2)]
    nlinarith [hstep, Real.pi_pos]
  linarith

open Finset Real in
/-- **The shell sum** (Track R, M0-q): summing the single-shell bound
over a nested family of shells.  Each shell contributes its decay — set
by the distance `a j` from the centre — times its Brun–Titchmarsh
count, with the log-ratio bounded uniformly by `L`.  Stated for
abstract cut points `a` and widths `w`, so the dyadic instance
`a j = (2^j − 1)h`, `w j = 2^j h` is a substitution at the call site
and no power arithmetic enters the proof. -/
theorem shell_sum_le (T : ℝ) (m J : ℕ) (a w : ℕ → ℕ) (hm : 1 ≤ m)
    (ha0 : a 0 = 0) (hamono : Monotone a) (hdiff : ∀ j, a (j+1) = a j + w j)
    (hfit : m + a J ≤ 2*m) (hw : ∀ j < J, 2 ≤ w j)
    (L : ℝ)
    (hLbound : ∀ j < J,
      Real.log (((m + a j : ℕ):ℝ) + ((w j : ℕ):ℝ) + 2)
          / Real.log ((w j : ℕ):ℝ) ≤ L) :
    ∑ p ∈ (Finset.Ioc m (m + a J)).filter Nat.Prime,
        Real.log p * Real.exp (-(π*T^2*(Real.log p - Real.log m)^2))
      ≤ ∑ j ∈ Finset.range J,
          Real.exp (-(π*T^2*((a j : ℕ):ℝ)^2/(4*(m:ℝ)^2)))
            * (256*((w j : ℕ):ℝ)*L) := by
  classical
  have hsplit := sum_Ioc_shell_split
    (fun p => if p.Prime then
      Real.log p * Real.exp (-(π*T^2*(Real.log p - Real.log m)^2)) else 0)
    m a ha0 hamono J
  rw [Finset.sum_filter, hsplit]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [← Finset.sum_filter]
  have hmu : m ≤ m + a j := by omega
  have hvfit : m + a (j+1) ≤ 2*m := by
    have h1 : a (j+1) ≤ a J := hamono (by omega)
    omega
  have hwj : 2 ≤ w j := hw j hj
  have hd := hdiff j
  have huv : m + a j < m + a (j+1) := by omega
  have hKshell : 2 ≤ (m + a (j+1)) - (m + a j) := by omega
  have hbound := shell_gaussian_count_le T m (m + a j) (m + a (j+1))
    hm hmu huv hvfit hKshell
  refine le_trans hbound ?_
  have hwidth : ((m + a (j+1) : ℕ):ℝ) - ((m + a j : ℕ):ℝ) = ((w j : ℕ):ℝ) := by
    rw [hd]
    push_cast
    ring
  have hu : ((m + a j : ℕ):ℝ) - (m:ℝ) = ((a j : ℕ):ℝ) := by
    push_cast
    ring
  rw [hwidth, hu]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hpos : (0:ℝ) ≤ 256*((w j : ℕ):ℝ) := by positivity
  calc 256*((w j : ℕ):ℝ)
        * Real.log (((m + a j : ℕ):ℝ) + ((w j : ℕ):ℝ) + 2)
        / Real.log ((w j : ℕ):ℝ)
      = 256*((w j : ℕ):ℝ)
        * (Real.log (((m + a j : ℕ):ℝ) + ((w j : ℕ):ℝ) + 2)
            / Real.log ((w j : ℕ):ℝ)) := by ring
    _ ≤ 256*((w j : ℕ):ℝ) * L :=
        mul_le_mul_of_nonneg_left (hLbound j hj) hpos
    _ = 256*((w j : ℕ):ℝ)*L := by ring

/-- **The dyadic cut points** (Track R, M0-s): `a j = (2^j − 1)h` with
widths `w j = 2^j h` satisfies the structural hypotheses of
`shell_sum_le` — it starts at `0`, is monotone, and each shell width is
the successive difference.  The `−1` is what makes `a 0 = 0`; the
shells are then `(m + (2^j−1)h, m + (2^{j+1}−1)h]`, of width `2^j h`
and at distance `(2^j−1)h` from the centre, which is exactly the
calibration `shell_exponent_le` expects. -/
theorem dyadic_cut_zero (h : ℕ) : (2^0 - 1)*h = 0 := by
  simp

theorem dyadic_cut_monotone (h : ℕ) :
    Monotone (fun j : ℕ => (2^j - 1)*h) := by
  intro i j hij
  have h2 : (2:ℕ)^i ≤ 2^j := Nat.pow_le_pow_right (by norm_num) hij
  have h1 : (1:ℕ) ≤ 2^i := Nat.one_le_two_pow
  exact Nat.mul_le_mul_right h (by omega)

theorem dyadic_cut_succ (h j : ℕ) :
    (2^(j+1) - 1)*h = (2^j - 1)*h + 2^j*h := by
  have h1 : (1:ℕ) ≤ 2^j := Nat.one_le_two_pow
  have h2 : (2:ℕ)^(j+1) = 2*2^j := by rw [pow_succ]; ring
  rw [h2, ← Nat.add_mul]
  congr 1
  omega

open Real in
/-- **The shell log-ratio is uniform** (Track R, M0-t): across the
dyadic shells inside `(m, 2m]`, the Brun–Titchmarsh log-ratio is
bounded by the single constant `log(4m+2)/log h`.  The numerator never
exceeds `log(4m+2)` because every shell sits inside `(m, 2m]`, and the
denominator never falls below `log h` because every shell has width at
least `h`.  This is the uniform `L` that `shell_sum_le` takes as a
hypothesis. -/
theorem shell_log_ratio_le (m h : ℕ) (hh : 2 ≤ h) (j : ℕ)
    (haj : (2^j - 1)*h ≤ m) (hwj : 2^j*h ≤ 2*m) :
    Real.log (((m + (2^j - 1)*h : ℕ):ℝ) + ((2^j*h : ℕ):ℝ) + 2)
        / Real.log ((2^j*h : ℕ):ℝ)
      ≤ Real.log (4*(m:ℝ) + 2) / Real.log ((h:ℕ):ℝ) := by
  have hh2 : (2:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hlogh : (0:ℝ) < Real.log ((h:ℕ):ℝ) := by
    refine Real.log_pos ?_
    linarith
  -- every shell is at least as wide as `h`
  have hwh : (h:ℕ) ≤ 2^j*h := by
    have h1 : (1:ℕ) ≤ 2^j := Nat.one_le_two_pow
    calc (h:ℕ) = 1*h := by ring
      _ ≤ 2^j*h := Nat.mul_le_mul_right h h1
  have hwhR : ((h:ℕ):ℝ) ≤ ((2^j*h : ℕ):ℝ) := by exact_mod_cast hwh
  have hlogw : (0:ℝ) < Real.log ((2^j*h : ℕ):ℝ) :=
    lt_of_lt_of_le hlogh (Real.log_le_log (by linarith) hwhR)
  -- and sits inside `(m, 2m]`
  have hnum : ((m + (2^j - 1)*h : ℕ):ℝ) + ((2^j*h : ℕ):ℝ) + 2
      ≤ 4*(m:ℝ) + 2 := by
    have h1 : ((m + (2^j - 1)*h : ℕ):ℝ) ≤ 2*(m:ℝ) := by
      have : m + (2^j - 1)*h ≤ 2*m := by omega
      exact_mod_cast this
    have h2 : ((2^j*h : ℕ):ℝ) ≤ 2*(m:ℝ) := by exact_mod_cast hwj
    linarith
  rw [div_le_div_iff₀ hlogw hlogh]
  have h1 : Real.log (((m + (2^j - 1)*h : ℕ):ℝ) + ((2^j*h : ℕ):ℝ) + 2)
      ≤ Real.log (4*(m:ℝ) + 2) := by
    refine Real.log_le_log ?_ hnum
    have hm0 : (0:ℝ) ≤ (m:ℝ) := by positivity
    have hw0 : (0:ℝ) ≤ ((2^j*h : ℕ):ℝ) := by positivity
    have ha0 : (0:ℝ) ≤ ((m + (2^j - 1)*h : ℕ):ℝ) := by positivity
    linarith
  have h2 : Real.log ((h:ℕ):ℝ) ≤ Real.log ((2^j*h : ℕ):ℝ) :=
    Real.log_le_log (by linarith) hwhR
  have h3 : (0:ℝ) ≤ Real.log (((m + (2^j - 1)*h : ℕ):ℝ)
      + ((2^j*h : ℕ):ℝ) + 2) := by
    refine Real.log_nonneg ?_
    have hm0 : (0:ℝ) ≤ (m:ℝ) := by positivity
    have hw0 : (0:ℝ) ≤ ((2^j*h : ℕ):ℝ) := by positivity
    have ha0 : (0:ℝ) ≤ ((m + (2^j - 1)*h : ℕ):ℝ) := by positivity
    linarith
  nlinarith [h1, h2, h3, hlogh.le]

open Finset Real in
/-- **The inner sum** (Track R, M0-u): the Gaussian-weighted prime
log-mass around `m` is `≪ h·log(4m+2)/log h`, where `h ≈ 2m/T` is the
dyadic scale.  This is the payoff of the shell chain: the shells are
instantiated at `(2^j−1)h`, each decays by `shell_exponent_le`, and
`sum_shell_series_le` collapses the geometric count against the
Gaussian decay to an absolute constant. -/
theorem inner_sum_le (T : ℝ) (m h J : ℕ) (hm : 1 ≤ m) (hh : 2 ≤ h)
    (hscale : 2*(m:ℝ) ≤ (h:ℝ)*T) (hfit : (2^J - 1)*h ≤ m)
    (hwfit : ∀ j < J, 2^j*h ≤ 2*m) :
    ∑ p ∈ (Finset.Ioc m (m + (2^J - 1)*h)).filter Nat.Prime,
        Real.log p * Real.exp (-(π*T^2*(Real.log p - Real.log m)^2))
      ≤ 512*(h:ℝ)*(Real.log (4*(m:ℝ)+2)/Real.log ((h:ℕ):ℝ)) := by
  classical
  set L : ℝ := Real.log (4*(m:ℝ)+2)/Real.log ((h:ℕ):ℝ) with hL_def
  have hh2 : (2:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hlogh : (0:ℝ) < Real.log ((h:ℕ):ℝ) := Real.log_pos (by linarith)
  have hL0 : (0:ℝ) ≤ L := by
    rw [hL_def]
    refine div_nonneg (Real.log_nonneg ?_) hlogh.le
    have : (0:ℝ) ≤ (m:ℝ) := by positivity
    linarith
  -- the shell sum, at the dyadic cut points
  have hstep := shell_sum_le T m J (fun j => (2^j - 1)*h) (fun j => 2^j*h)
    hm (dyadic_cut_zero h) (dyadic_cut_monotone h)
    (fun j => dyadic_cut_succ h j) (by simp only; omega)
    (fun j _ => by
      have h1 : (1:ℕ) ≤ 2^j := Nat.one_le_two_pow
      calc (2:ℕ) ≤ h := hh
        _ = 1*h := by ring
        _ ≤ 2^j*h := Nat.mul_le_mul_right h h1)
    L (fun j hj => shell_log_ratio_le m h hh j (by
        have := dyadic_cut_monotone h (show j ≤ J by omega)
        simp only at this
        omega) (hwfit j hj))
  refine le_trans hstep ?_
  -- collapse the shells: `j = 0` is trivial, `j ≥ 1` is the series
  have hterm : ∀ j ∈ Finset.range J,
      Real.exp (-(π*T^2*(((2^j - 1)*h : ℕ):ℝ)^2/(4*(m:ℝ)^2)))
          * (256*((2^j*h : ℕ):ℝ)*L)
        ≤ 256*(h:ℝ)*L * ((2:ℝ)^j * Real.exp (-(π/4 * 4^j)) + if j = 0 then 1 else 0) := by
    intro j _
    have hcast : (((2^j - 1)*h : ℕ):ℝ) = ((2:ℝ)^j - 1)*(h:ℝ) := by
      have h1 : (1:ℕ) ≤ 2^j := Nat.one_le_two_pow
      push_cast [Nat.cast_sub h1]
      ring
    have hcastw : ((2^j*h : ℕ):ℝ) = (2:ℝ)^j*(h:ℝ) := by push_cast; ring
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · subst hj0
      rw [hcast, hcastw, if_pos rfl]
      have hz : ((2:ℝ)^0 - 1)*(h:ℝ) = 0 := by norm_num
      rw [hz]
      have hz2 : -(π*T^2*(0:ℝ)^2/(4*(m:ℝ)^2)) = 0 := by ring
      rw [hz2, Real.exp_zero, one_mul, pow_zero, one_mul]
      have hpos : (0:ℝ) ≤ 256*(h:ℝ)*L := by positivity
      nlinarith [Real.exp_pos (-(π/4 * (4:ℝ)^0)), hpos]
    · have hj1' : 1 ≤ j := hj1
      rw [if_neg (by omega), add_zero, hcast, hcastw]
      have hdecay := shell_exponent_le T (m:ℝ) (h:ℝ)
        (by exact_mod_cast hm) (by positivity) hscale hj1'
      calc Real.exp (-(π*T^2*(((2:ℝ)^j - 1)*(h:ℝ))^2/(4*(m:ℝ)^2)))
            * (256*((2:ℝ)^j*(h:ℝ))*L)
          ≤ Real.exp (-(π/4 * 4^j)) * (256*((2:ℝ)^j*(h:ℝ))*L) := by
            refine mul_le_mul_of_nonneg_right hdecay (by positivity)
        _ = 256*(h:ℝ)*L * ((2:ℝ)^j * Real.exp (-(π/4 * 4^j))) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hsum : ∑ j ∈ Finset.range J,
      ((2:ℝ)^j * Real.exp (-(π/4 * 4^j)) + if j = 0 then 1 else 0) ≤ 2 := by
    rw [Finset.sum_add_distrib]
    have h1 := sum_shell_series_le J
    have h2 : ∑ j ∈ Finset.range J, (if j = 0 then (1:ℝ) else 0) ≤ 1 := by
      rcases Nat.eq_zero_or_pos J with hJ | hJ
      · subst hJ; simp
      · rw [Finset.sum_ite_eq' (Finset.range J) 0 (fun _ => (1:ℝ))]
        rw [if_pos (Finset.mem_range.mpr hJ)]
    linarith
  have hcoef : (0:ℝ) ≤ 256*(h:ℝ)*L := by positivity
  calc 256*(h:ℝ)*L * ∑ j ∈ Finset.range J,
        ((2:ℝ)^j * Real.exp (-(π/4 * 4^j)) + if j = 0 then 1 else 0)
      ≤ 256*(h:ℝ)*L * 2 := mul_le_mul_of_nonneg_left hsum hcoef
    _ = 512*(h:ℝ)*L := by ring

open MeasureTheory Real Complex in
open scoped FourierTransform in
/-- **The Gaussian pair bound** (Track R, M0-v): the sharp window
energy of a Dirichlet polynomial is dominated by the double sum of its
pair correlations against the Gaussian kernel
`e^{π}·T·e^{−πT²(log m − log n)²}`.  This is the whole outer chain of
GHS Lemma 2.6 in one step — majorise by the Gaussian
(`intervalIntegral_norm_sq_le_gaussian`), expand into pairs
(`integral_norm_sq_poly_weight_eq`), evaluate each pair integral as a
transform value (`integral_re_char_mul_weight`), and read that value
off the Gaussian's self-duality (`fourier_gaussian_scaled`).  What
remains is arithmetic: the kernel is symmetric and non-negative, so
`sum_pair_re_le_of_symm` folds it onto the diagonal and `inner_sum_le`
counts the surviving primes. -/
theorem intervalIntegral_norm_sq_gaussian_pairs_le (S : Finset ℕ) (c : ℕ → ℂ)
    (T : ℝ) (hT : 0 < T) :
    (∫ ξ in (-T)..T, ‖∑ n ∈ S, c n
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
      ≤ ∑ m ∈ S, ∑ n ∈ S, (c m * (starRingEnd ℂ) (c n)).re
          * (Real.exp π * T
              * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2))) := by
  classical
  -- the Gaussian weight is continuous and integrable
  have hWc : Continuous
      (fun ξ : ℝ => Real.exp π * Real.exp (-(π*(ξ/T)^2))) := by fun_prop
  have hweight : ∀ ξ : ℝ,
      Real.exp (-(π*(ξ/T)^2)) = Real.exp (-(π/T^2) * ξ^2) := by
    intro ξ
    congr 1
    field_simp
  have hWi : Integrable
      (fun ξ : ℝ => Real.exp π * Real.exp (-(π*(ξ/T)^2))) := by
    have hfun : (fun ξ : ℝ => Real.exp π * Real.exp (-(π*(ξ/T)^2)))
        = fun ξ : ℝ => Real.exp π * Real.exp (-(π/T^2) * ξ^2) := by
      funext ξ
      rw [hweight ξ]
    rw [hfun]
    exact (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  -- the polynomial is continuous and bounded, so the majorant applies
  have hchar : ∀ v : ℝ, Continuous fun ξ : ℝ =>
      ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ) := fun v =>
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hDc : Continuous fun ξ : ℝ => ∑ n ∈ S, c n
      * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ) :=
    continuous_finset_sum _ fun n _ => continuous_const.mul (hchar (Real.log n))
  have hDbound : ∀ ξ : ℝ, ‖∑ n ∈ S, c n
      * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖
        ≤ ∑ n ∈ S, ‖c n‖ := by
    intro ξ
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n _ => ?_)
    rw [norm_mul, norm_eq_of_mem_sphere, mul_one]
  -- the transform of the weight, at the log-difference
  have hFourier : ∀ v : ℝ,
      (∫ ξ : ℝ, ((Real.exp π * Real.exp (-(π*(ξ/T)^2)) : ℝ) : ℂ)
          * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ))
        = ((Real.exp π * T * Real.exp (-(π*T^2*v^2)) : ℝ) : ℂ) := by
    intro v
    have hg : (𝓕 fun x : ℝ => ((Real.exp (-(π*(x/T)^2)) : ℝ) : ℂ)) v
        = ((T : ℝ) : ℂ) * ((Real.exp (-(π*T^2*v^2)) : ℝ) : ℂ) :=
      congrFun (fourier_gaussian_scaled hT) v
    simp only [fourier_real_eq] at hg
    have hcomm : (∫ ξ : ℝ, ((Real.exp π * Real.exp (-(π*(ξ/T)^2)) : ℝ) : ℂ)
          * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ))
        = ((Real.exp π : ℝ) : ℂ) * ∫ ξ : ℝ,
            (Real.fourierChar (-(ξ * v)) : Circle)
              • ((Real.exp (-(π*(ξ/T)^2)) : ℝ) : ℂ) := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun ξ => ?_)
      simp only [Circle.smul_def, smul_eq_mul]
      rw [mul_comm ξ v, Complex.ofReal_mul]
      ring
    rw [hcomm, hg, Complex.ofReal_mul, Complex.ofReal_mul]
    ring
  calc (∫ ξ in (-T)..T, ‖∑ n ∈ S, c n
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
      ≤ ∫ ξ : ℝ, ‖∑ n ∈ S, c n
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2
            * (Real.exp π * Real.exp (-(π*(ξ/T)^2))) :=
        intervalIntegral_norm_sq_le_gaussian _ hDc _ hDbound T hT
    _ = ∑ m ∈ S, ∑ n ∈ S, ∫ ξ : ℝ, (((c m * (starRingEnd ℂ) (c n))
          * ((Real.fourierChar (-((Real.log m - Real.log n) * ξ)) : Circle)
            : ℂ)).re) * (Real.exp π * Real.exp (-(π*(ξ/T)^2))) :=
        integral_norm_sq_poly_weight_eq S c _ hWc hWi
    _ = ∑ m ∈ S, ∑ n ∈ S, ((c m * (starRingEnd ℂ) (c n))
          * ((Real.exp π * T
              * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2)) : ℝ) : ℂ)).re := by
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
        have h1 : (∫ ξ : ℝ, (((c m * (starRingEnd ℂ) (c n))
                * ((Real.fourierChar (-((Real.log m - Real.log n) * ξ)) : Circle)
                  : ℂ)).re) * (Real.exp π * Real.exp (-(π*(ξ/T)^2))))
              = ((c m * (starRingEnd ℂ) (c n)) * ∫ ξ : ℝ,
                  ((Real.exp π * Real.exp (-(π*(ξ/T)^2)) : ℝ) : ℂ)
                    * ((Real.fourierChar (-((Real.log m - Real.log n) * ξ))
                        : Circle) : ℂ)).re :=
          integral_re_char_mul_weight _ _ _ hWc hWi
        rw [h1, hFourier]
    _ = ∑ m ∈ S, ∑ n ∈ S, (c m * (starRingEnd ℂ) (c n)).re
          * (Real.exp π * T
              * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2))) := by
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        ring

open MeasureTheory Real Complex in
/-- **The Gaussian diagonal bound** (Track R, M0-w): for a Dirichlet
polynomial whose coefficients carry a **non-negative real weight** `r`,
the window energy collapses onto the diagonal with `r` moved into the
kernel:

  `∫_{−T}^{T}‖∑ a(n)r(n)n^{−iξ}‖² ≤ ∑ₘ |a(m)|²r(m)·∑ₙ r(n)K(m,n)`.

Carrying `r` in the kernel rather than in the coefficients is the whole
point.  Applying `sum_pair_re_le_of_symm` directly to `c = a·r` would
produce `|a(m)|²r(m)²` on the diagonal — with `r = Λ` that is one
logarithm worse than GHS Lemma 2.6 allows.  Splitting the pair as
`a(m)·conj a(n)` against the weighted kernel `r(m)r(n)K(m,n)` leaves
exactly one `r(m)` outside, which is the `Λ(n)` of `∑ n|a(n)|²Λ(n)`. -/
theorem intervalIntegral_norm_sq_gaussian_diag_le (S : Finset ℕ) (a : ℕ → ℂ)
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n) (T : ℝ) (hT : 0 < T) :
    (∫ ξ in (-T)..T, ‖∑ n ∈ S, (a n * ((r n : ℝ) : ℂ))
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
      ≤ ∑ m ∈ S, ‖a m‖^2 * r m
          * ∑ n ∈ S, r n * (Real.exp π * T
              * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2))) := by
  classical
  -- the weighted kernel is non-negative and symmetric
  have hK0 : ∀ m n : ℕ, 0 ≤ r m * r n
      * (Real.exp π * T
          * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2))) := by
    intro m n
    refine mul_nonneg (mul_nonneg (hr m) (hr n)) ?_
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le hT.le) (Real.exp_pos _).le
  have hKsymm : ∀ m n : ℕ, r m * r n
      * (Real.exp π * T
          * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2)))
      = r n * r m
      * (Real.exp π * T
          * Real.exp (-(π*T^2*(Real.log n - Real.log m)^2))) := by
    intro m n
    have hsq : (Real.log m - Real.log n)^2 = (Real.log n - Real.log m)^2 := by
      ring
    rw [hsq]
    ring
  -- the weight is real, so it passes through the real part
  have hpair : ∀ m n : ℕ,
      ((a m * ((r m : ℝ) : ℂ)) * (starRingEnd ℂ) (a n * ((r n : ℝ) : ℂ))).re
          * (Real.exp π * T
              * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2)))
        = (a m * (starRingEnd ℂ) (a n)).re
          * (r m * r n * (Real.exp π * T
              * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2)))) := by
    intro m n
    have hz : (a m * ((r m : ℝ) : ℂ))
          * (starRingEnd ℂ) (a n * ((r n : ℝ) : ℂ))
        = (a m * (starRingEnd ℂ) (a n)) * (((r m * r n : ℝ)) : ℂ) := by
      rw [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
      ring
    rw [hz, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  calc (∫ ξ in (-T)..T, ‖∑ n ∈ S, (a n * ((r n : ℝ) : ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
      ≤ ∑ m ∈ S, ∑ n ∈ S, ((a m * ((r m : ℝ) : ℂ))
          * (starRingEnd ℂ) (a n * ((r n : ℝ) : ℂ))).re
            * (Real.exp π * T
                * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2))) :=
        intervalIntegral_norm_sq_gaussian_pairs_le S _ T hT
    _ = ∑ m ∈ S, ∑ n ∈ S, (a m * (starRingEnd ℂ) (a n)).re
          * (r m * r n * (Real.exp π * T
              * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2)))) :=
        Finset.sum_congr rfl fun m _ =>
          Finset.sum_congr rfl fun n _ => hpair m n
    _ ≤ ∑ m ∈ S, ‖a m‖^2
          * ∑ n ∈ S, (r m * r n * (Real.exp π * T
              * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2)))) :=
        sum_pair_re_le_of_symm S a
          (fun m n => r m * r n * (Real.exp π * T
              * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2)))) hK0 hKsymm
    _ = ∑ m ∈ S, ‖a m‖^2 * r m
          * ∑ n ∈ S, r n * (Real.exp π * T
              * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2))) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        have hfac : ∑ n ∈ S, (r m * r n * (Real.exp π * T
              * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2))))
            = r m * ∑ n ∈ S, r n * (Real.exp π * T
                * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2))) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun n _ => by ring
        rw [hfac, ← mul_assoc]

open Real in
/-- **Gaussian decay from an integer gap, on the left** (Track R,
M0-x): the mirror of `gaussian_decay_of_gap` for `n < m`.  Here the
estimate is *unconditional* — no dyadic hypothesis `m ≤ 2n` is needed,
because `log(m/n) ≥ 1 − n/m = (m − n)/m` already beats the required
`(m − n)/(2m)` outright, whereas on the right `log(n/m) ≥ (n − m)/n`
only gives `(n − m)/(2m)` after using `n ≤ 2m`.  The factor `4m²` is
kept (rather than the sharper `m²` the left side would allow) so that
the shell calibration of `shell_exponent_le` transfers verbatim. -/
theorem gaussian_decay_of_gap_left (T : ℝ) (m n : ℕ) (hn : 1 ≤ n)
    (hnm : n < m) (d : ℝ) (hd0 : 0 ≤ d) (hd : d ≤ (m:ℝ) - n) :
    Real.exp (-(π*T^2*(Real.log n - Real.log m)^2))
      ≤ Real.exp (-(π*T^2*d^2/(4*(m:ℝ)^2))) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hm0 : (0:ℝ) < m := by
    have : (0:ℕ) < m := by omega
    exact_mod_cast this
  -- the log-difference dominates the normalised gap
  have hlog : ((m:ℝ) - n)/m ≤ Real.log m - Real.log n :=
    log_sub_log_ge n m hn hnm
  have hgap : d/(2*(m:ℝ)) ≤ Real.log m - Real.log n := by
    refine le_trans ?_ hlog
    rw [div_le_div_iff₀ (by positivity) hm0]
    nlinarith [hd, hd0, hm0]
  have hsq : (d/(2*(m:ℝ)))^2 ≤ (Real.log m - Real.log n)^2 :=
    pow_le_pow_left₀ (by positivity) hgap 2
  refine Real.exp_le_exp.mpr ?_
  have hflip : (Real.log n - Real.log m)^2 = (Real.log m - Real.log n)^2 := by
    ring
  rw [hflip]
  have hd2 : d^2/(4*(m:ℝ)^2) = (d/(2*(m:ℝ)))^2 := by
    field_simp
    ring
  have hpi : (0:ℝ) ≤ π*T^2 := by positivity
  have hkey : π*T^2*d^2/(4*(m:ℝ)^2)
      ≤ π*T^2*(Real.log m - Real.log n)^2 := by
    calc π*T^2*d^2/(4*(m:ℝ)^2) = (π*T^2)*(d^2/(4*(m:ℝ)^2)) := by ring
      _ = (π*T^2)*((d/(2*(m:ℝ)))^2) := by rw [hd2]
      _ ≤ (π*T^2)*((Real.log m - Real.log n)^2) :=
          mul_le_mul_of_nonneg_left hsq hpi
      _ = π*T^2*(Real.log m - Real.log n)^2 := by ring
  linarith

open Finset Real in
/-- **The single-shell bound, on the left** (Track R, M0-x): on a shell
`(u, v]` lying entirely below `m`, the Gaussian-weighted prime log-mass
is at most the shell's decay factor times its Brun–Titchmarsh count.
The mirror of `shell_gaussian_count_le`, and strictly cheaper: the
uniform gap is `m − v` (attained at the shell's *right* endpoint, the
one nearest `m`), and no `v ≤ 2m` hypothesis is required because
`gaussian_decay_of_gap_left` needs none. -/
theorem shell_gaussian_count_le_left (T : ℝ) (m u v : ℕ) (hvm : v < m)
    (huv : u < v) (hK : 2 ≤ v - u) :
    ∑ p ∈ (Finset.Ioc u v).filter Nat.Prime,
        Real.log p * Real.exp (-(π*T^2*(Real.log p - Real.log m)^2))
      ≤ Real.exp (-(π*T^2*((m:ℝ) - (v:ℝ))^2/(4*(m:ℝ)^2)))
        * (256*((v:ℝ)-(u:ℝ))*Real.log ((u:ℝ) + ((v:ℝ)-(u:ℝ)) + 2)
            /Real.log ((v:ℝ)-(u:ℝ))) := by
  classical
  have hvmR : (v:ℝ) < (m:ℝ) := by exact_mod_cast hvm
  -- the shell's decay factor dominates every term
  have hdecay : ∀ p ∈ (Finset.Ioc u v).filter Nat.Prime,
      Real.log p * Real.exp (-(π*T^2*(Real.log p - Real.log m)^2))
        ≤ Real.exp (-(π*T^2*((m:ℝ) - (v:ℝ))^2/(4*(m:ℝ)^2)))
            * Real.log p := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    have hp1 : 1 ≤ p := hp.2.one_lt.le
    have hpm : p < m := lt_of_le_of_lt hp.1.2 hvm
    have hpR : (p:ℝ) ≤ (v:ℝ) := by exact_mod_cast hp.1.2
    have hdle : ((m:ℝ) - (v:ℝ)) ≤ (m:ℝ) - p := by linarith
    have hd0 : (0:ℝ) ≤ (m:ℝ) - (v:ℝ) := by linarith
    have hg := gaussian_decay_of_gap_left T m p hp1 hpm
      ((m:ℝ) - (v:ℝ)) hd0 hdle
    have hlogp : (0:ℝ) ≤ Real.log p := by
      refine Real.log_nonneg ?_
      exact_mod_cast hp1
    calc Real.log p * Real.exp (-(π*T^2*(Real.log p - Real.log m)^2))
        ≤ Real.log p
            * Real.exp (-(π*T^2*((m:ℝ) - (v:ℝ))^2/(4*(m:ℝ)^2))) :=
          mul_le_mul_of_nonneg_left hg hlogp
      _ = Real.exp (-(π*T^2*((m:ℝ) - (v:ℝ))^2/(4*(m:ℝ)^2)))
            * Real.log p := by ring
  refine le_trans (Finset.sum_le_sum hdecay) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  -- the sieve count on the shell
  have hvu : v = u + (v - u) := by omega
  have hcount := sum_log_primes_Ioc_le u (v - u) hK
  have hcast : ((v - u : ℕ) : ℝ) = (v:ℝ) - (u:ℝ) := by
    have : u ≤ v := huv.le
    push_cast [Nat.cast_sub this]
    ring
  rw [← hvu] at hcount
  rw [hcast] at hcount
  exact hcount

/-- **The shell split, downward** (Track R, M0-y): a sum over
`(c J, c 0]` breaks into the shells `(c (j+1), c j]` for an *antitone*
cut sequence.  The mirror of `sum_Ioc_shell_split`: on the left of the
Gaussian's centre the shells march away from `m` as `j` grows, so the
cut points decrease and the shell nearest `m` is `j = 0` — exactly as
on the right, which is what lets the two sides share
`sum_shell_series_le` and hence the same constant. -/
theorem sum_Ioc_shell_split_down {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (c : ℕ → ℕ) (hanti : Antitone c) :
    ∀ J : ℕ, ∑ n ∈ Finset.Ioc (c J) (c 0), f n
      = ∑ j ∈ Finset.range J,
          ∑ n ∈ Finset.Ioc (c (j+1)) (c j), f n := by
  intro J
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ← ih]
    have h1 : c (J+1) ≤ c J := hanti (by omega)
    have h2 : c J ≤ c 0 := hanti (by omega)
    rw [← Finset.sum_Ioc_consecutive f h1 h2]
    exact add_comm _ _

open Finset Real in
/-- **The shell sum, on the left** (Track R, M0-y): summing the
single-shell bound over a nested family of shells lying below `m`.  The
mirror of `shell_sum_le`, stated for an abstract antitone cut sequence
`c` so that the dyadic instance `c j = m − 1 − (2^j − 1)h` is a
substitution at the call site.  Shell `j` sits at distance `m − c j`
from the centre, which is what its decay factor is measured against. -/
theorem shell_sum_le_left (T : ℝ) (m J : ℕ) (c : ℕ → ℕ) (hanti : Antitone c)
    (hc0 : c 0 < m) (hw : ∀ j < J, 2 ≤ c j - c (j+1))
    (L : ℝ)
    (hLbound : ∀ j < J,
      Real.log (((c (j+1) : ℕ):ℝ) + ((c j - c (j+1) : ℕ):ℝ) + 2)
          / Real.log ((c j - c (j+1) : ℕ):ℝ) ≤ L) :
    ∑ p ∈ (Finset.Ioc (c J) (c 0)).filter Nat.Prime,
        Real.log p * Real.exp (-(π*T^2*(Real.log p - Real.log m)^2))
      ≤ ∑ j ∈ Finset.range J,
          Real.exp (-(π*T^2*((m:ℝ) - ((c j : ℕ):ℝ))^2/(4*(m:ℝ)^2)))
            * (256*((c j - c (j+1) : ℕ):ℝ)*L) := by
  classical
  have hsplit := sum_Ioc_shell_split_down
    (fun p => if p.Prime then
      Real.log p * Real.exp (-(π*T^2*(Real.log p - Real.log m)^2)) else 0)
    c hanti J
  rw [Finset.sum_filter, hsplit]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [← Finset.sum_filter]
  have hwj : 2 ≤ c j - c (j+1) := hw j hj
  have huv : c (j+1) < c j := by omega
  have hvm : c j < m := lt_of_le_of_lt (hanti (Nat.zero_le j)) hc0
  have hbound := shell_gaussian_count_le_left T m (c (j+1)) (c j) hvm huv hwj
  refine le_trans hbound ?_
  have hwidth : ((c j : ℕ):ℝ) - ((c (j+1) : ℕ):ℝ)
      = ((c j - c (j+1) : ℕ):ℝ) := by
    have hle : c (j+1) ≤ c j := huv.le
    push_cast [Nat.cast_sub hle]
    ring
  rw [hwidth]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hpos : (0:ℝ) ≤ 256*((c j - c (j+1) : ℕ):ℝ) := by positivity
  calc 256*((c j - c (j+1) : ℕ):ℝ)
        * Real.log (((c (j+1) : ℕ):ℝ) + ((c j - c (j+1) : ℕ):ℝ) + 2)
        / Real.log ((c j - c (j+1) : ℕ):ℝ)
      = 256*((c j - c (j+1) : ℕ):ℝ)
        * (Real.log (((c (j+1) : ℕ):ℝ) + ((c j - c (j+1) : ℕ):ℝ) + 2)
            / Real.log ((c j - c (j+1) : ℕ):ℝ)) := by ring
    _ ≤ 256*((c j - c (j+1) : ℕ):ℝ) * L :=
        mul_le_mul_of_nonneg_left (hLbound j hj) hpos
    _ = 256*((c j - c (j+1) : ℕ):ℝ)*L := by ring

open Finset Real in
/-- **The log-ratio, uniformly** (Track R, M0-z): whenever a shell
`(u, u+w]` sits inside `(0, 2m]` and is at least `h` wide, its
Brun–Titchmarsh log-ratio is bounded by the single constant
`log(4m+2)/log h`.  This is `shell_log_ratio_le` with the dyadic
parametrisation stripped out, so that the same lemma serves the shells
on *both* sides of the Gaussian's centre. -/
theorem log_ratio_le_of_le (m u w h : ℕ) (hh : 2 ≤ h) (hw : h ≤ w)
    (huw : u + w ≤ 2*m) :
    Real.log ((u:ℝ) + (w:ℝ) + 2)/Real.log ((w:ℕ):ℝ)
      ≤ Real.log (4*(m:ℝ) + 2)/Real.log ((h:ℕ):ℝ) := by
  have hh2 : (2:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hlogh : (0:ℝ) < Real.log ((h:ℕ):ℝ) := Real.log_pos (by linarith)
  have hwR : ((h:ℕ):ℝ) ≤ ((w:ℕ):ℝ) := by exact_mod_cast hw
  have hlogw : (0:ℝ) < Real.log ((w:ℕ):ℝ) :=
    lt_of_lt_of_le hlogh (Real.log_le_log (by linarith) hwR)
  have hu0 : (0:ℝ) ≤ (u:ℝ) := by positivity
  have hw0 : (0:ℝ) ≤ (w:ℝ) := by positivity
  have hnum : (u:ℝ) + (w:ℝ) + 2 ≤ 4*(m:ℝ) + 2 := by
    have hc : ((u + w : ℕ):ℝ) ≤ ((2*m : ℕ):ℝ) := by exact_mod_cast huw
    push_cast at hc
    linarith
  rw [div_le_div_iff₀ hlogw hlogh]
  have h1 : Real.log ((u:ℝ) + (w:ℝ) + 2) ≤ Real.log (4*(m:ℝ) + 2) :=
    Real.log_le_log (by linarith) hnum
  have h2 : Real.log ((h:ℕ):ℝ) ≤ Real.log ((w:ℕ):ℝ) :=
    Real.log_le_log (by linarith) hwR
  have h3 : (0:ℝ) ≤ Real.log ((u:ℝ) + (w:ℝ) + 2) :=
    Real.log_nonneg (by linarith)
  nlinarith [h1, h2, h3, hlogh.le]

open Finset Real in
/-- **The inner sum, on the left** (Track R, M0-z): the mirror of
`inner_sum_le`.  The cut points are `c j = m − 1 − (2^j − 1)h`, marching
*down* from `m − 1`; the `−1` keeps `p = m` out of the range, which is
what `shell_gaussian_count_le_left` requires and which leaves the
diagonal term `p = m` to be handled once at the top level.  Shell `j`
sits at distance `1 + (2^j − 1)h` from the centre, so the same
`shell_exponent_le` calibration applies and the constant `512` is the
same as on the right. -/
theorem inner_sum_le_left (T : ℝ) (m h J : ℕ) (hh : 2 ≤ h)
    (hscale : 2*(m:ℝ) ≤ (h:ℝ)*T) (hfit : (2^J - 1)*h + 1 ≤ m) :
    ∑ p ∈ (Finset.Ioc (m - 1 - (2^J - 1)*h) (m - 1)).filter Nat.Prime,
        Real.log p * Real.exp (-(π*T^2*(Real.log p - Real.log m)^2))
      ≤ 512*(h:ℝ)*(Real.log (4*(m:ℝ)+2)/Real.log ((h:ℕ):ℝ)) := by
  classical
  set L : ℝ := Real.log (4*(m:ℝ)+2)/Real.log ((h:ℕ):ℝ) with hL_def
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  have hh2 : (2:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hlogh : (0:ℝ) < Real.log ((h:ℕ):ℝ) := Real.log_pos (by linarith)
  have hL0 : (0:ℝ) ≤ L := by
    rw [hL_def]
    exact div_nonneg (Real.log_nonneg (by linarith)) hlogh.le
  -- every shell fits below `m`
  have hfitj : ∀ j ≤ J, (2^j - 1)*h + 1 ≤ m := by
    intro j hj
    have h2 : (2:ℕ)^j ≤ 2^J := Nat.pow_le_pow_right (by norm_num) hj
    have h1 : (1:ℕ) ≤ 2^j := Nat.one_le_two_pow
    have hmul : (2^j - 1)*h ≤ (2^J - 1)*h := Nat.mul_le_mul_right h (by omega)
    omega
  have hcast : ∀ j ≤ J, (((m - 1 - (2^j - 1)*h : ℕ)):ℝ)
      = (m:ℝ) - 1 - ((2:ℝ)^j - 1)*(h:ℝ) := by
    intro j hj
    have hf := hfitj j hj
    have h1 : (1:ℕ) ≤ 2^j := Nat.one_le_two_pow
    have hsub1 : ((2^j - 1 : ℕ):ℝ) = (2:ℝ)^j - 1 := by
      push_cast [Nat.cast_sub h1]
      ring
    rw [Nat.cast_sub (by omega : (2^j - 1)*h ≤ m - 1),
      Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_mul, hsub1]
    push_cast
    ring
  have hwidthN : ∀ j < J,
      (m - 1 - (2^j - 1)*h) - (m - 1 - (2^(j+1) - 1)*h) = 2^j*h := by
    intro j hj
    have hsucc := dyadic_cut_succ h j
    have hf := hfitj (j+1) (by omega)
    omega
  -- the cut sequence is antitone and stays below `m`
  have hanti : Antitone (fun j : ℕ => m - 1 - (2^j - 1)*h) := by
    intro i j hij
    simp only
    have h2 : (2:ℕ)^i ≤ 2^j := Nat.pow_le_pow_right (by norm_num) hij
    have h1 : (1:ℕ) ≤ 2^i := Nat.one_le_two_pow
    have hmul : (2^i - 1)*h ≤ (2^j - 1)*h := Nat.mul_le_mul_right h (by omega)
    omega
  have hc0v : (fun j : ℕ => m - 1 - (2^j - 1)*h) 0 = m - 1 := by norm_num
  have hc0 : (fun j : ℕ => m - 1 - (2^j - 1)*h) 0 < m := by
    rw [hc0v]
    omega
  have hwN : ∀ j < J, 2 ≤ (fun j : ℕ => m - 1 - (2^j - 1)*h) j
      - (fun j : ℕ => m - 1 - (2^j - 1)*h) (j+1) := by
    intro j hj
    simp only
    rw [hwidthN j hj]
    have h1 : (1:ℕ) ≤ 2^j := Nat.one_le_two_pow
    calc (2:ℕ) ≤ h := hh
      _ = 1*h := by ring
      _ ≤ 2^j*h := Nat.mul_le_mul_right h h1
  have hLb : ∀ j < J,
      Real.log ((((fun j : ℕ => m - 1 - (2^j - 1)*h) (j+1) : ℕ):ℝ)
          + (((fun j : ℕ => m - 1 - (2^j - 1)*h) j
              - (fun j : ℕ => m - 1 - (2^j - 1)*h) (j+1) : ℕ):ℝ) + 2)
        / Real.log ((((fun j : ℕ => m - 1 - (2^j - 1)*h) j
            - (fun j : ℕ => m - 1 - (2^j - 1)*h) (j+1) : ℕ)):ℝ) ≤ L := by
    intro j hj
    simp only
    rw [hwidthN j hj, hL_def]
    refine log_ratio_le_of_le m (m - 1 - (2^(j+1) - 1)*h) (2^j*h) h hh ?_ ?_
    · have h1 : (1:ℕ) ≤ 2^j := Nat.one_le_two_pow
      calc h = 1*h := by ring
        _ ≤ 2^j*h := Nat.mul_le_mul_right h h1
    · have hsucc := dyadic_cut_succ h j
      have hf := hfitj (j+1) (by omega)
      omega
  have hstep := shell_sum_le_left T m J (fun j : ℕ => m - 1 - (2^j - 1)*h)
    hanti hc0 hwN L hLb
  rw [hc0v] at hstep
  refine le_trans hstep ?_
  simp only
  -- collapse the shells: `j = 0` is trivial, `j ≥ 1` is the series
  have hterm : ∀ j ∈ Finset.range J,
      Real.exp (-(π*T^2*((m:ℝ) - ((m - 1 - (2^j - 1)*h : ℕ):ℝ))^2
          /(4*(m:ℝ)^2)))
        * (256*(((m - 1 - (2^j - 1)*h)
            - (m - 1 - (2^(j+1) - 1)*h) : ℕ):ℝ)*L)
      ≤ 256*(h:ℝ)*L
          * ((2:ℝ)^j * Real.exp (-(π/4 * 4^j)) + if j = 0 then 1 else 0) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [hcast j hj.le, hwidthN j hj]
    have hcw : ((2^j*h : ℕ):ℝ) = (2:ℝ)^j*(h:ℝ) := by push_cast; ring
    rw [hcw]
    have hgap : (m:ℝ) - ((m:ℝ) - 1 - ((2:ℝ)^j - 1)*(h:ℝ))
        = 1 + ((2:ℝ)^j - 1)*(h:ℝ) := by ring
    rw [hgap]
    have hh0 : (0:ℝ) ≤ (h:ℝ) := by linarith
    have hp1 : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
    have hbase : (0:ℝ) ≤ ((2:ℝ)^j - 1)*(h:ℝ) := mul_nonneg (by linarith) hh0
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · subst hj0
      rw [if_pos rfl, pow_zero, one_mul]
      have hz : ((1:ℝ) - 1)*(h:ℝ) = 0 := by ring
      rw [hz]
      have hdec : Real.exp (-(π*T^2*(1 + (0:ℝ))^2/(4*(m:ℝ)^2))) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        have : (0:ℝ) ≤ π*T^2*(1 + (0:ℝ))^2/(4*(m:ℝ)^2) := by positivity
        linarith
      have hpos : (0:ℝ) ≤ 256*(h:ℝ)*L := by positivity
      nlinarith [Real.exp_pos (-(π/4 * (4:ℝ)^0)), hpos, hdec]
    · have hj1' : 1 ≤ j := hj1
      rw [if_neg (by omega), add_zero]
      -- the extra `+1` in the gap only helps
      have hmono : Real.exp (-(π*T^2*(1 + ((2:ℝ)^j - 1)*(h:ℝ))^2/(4*(m:ℝ)^2)))
          ≤ Real.exp (-(π*T^2*(((2:ℝ)^j - 1)*(h:ℝ))^2/(4*(m:ℝ)^2))) := by
        refine Real.exp_le_exp.mpr ?_
        have hpi : (0:ℝ) ≤ π*T^2 := by positivity
        have hsq : (((2:ℝ)^j - 1)*(h:ℝ))^2
            ≤ (1 + ((2:ℝ)^j - 1)*(h:ℝ))^2 := by nlinarith [hbase]
        have h4m : (0:ℝ) < 4*(m:ℝ)^2 := by positivity
        rw [neg_le_neg_iff, div_le_div_iff₀ h4m h4m]
        have hprod : (0:ℝ) ≤ π*T^2*(4*(m:ℝ)^2) := mul_nonneg hpi h4m.le
        nlinarith [mul_le_mul_of_nonneg_left hsq hprod]
      have hdecay := shell_exponent_le T (m:ℝ) (h:ℝ) hm0 hh0 hscale hj1'
      calc Real.exp (-(π*T^2*(1 + ((2:ℝ)^j - 1)*(h:ℝ))^2/(4*(m:ℝ)^2)))
            * (256*((2:ℝ)^j*(h:ℝ))*L)
          ≤ Real.exp (-(π*T^2*(((2:ℝ)^j - 1)*(h:ℝ))^2/(4*(m:ℝ)^2)))
              * (256*((2:ℝ)^j*(h:ℝ))*L) :=
            mul_le_mul_of_nonneg_right hmono (by positivity)
        _ ≤ Real.exp (-(π/4 * 4^j)) * (256*((2:ℝ)^j*(h:ℝ))*L) :=
            mul_le_mul_of_nonneg_right hdecay (by positivity)
        _ = 256*(h:ℝ)*L * ((2:ℝ)^j * Real.exp (-(π/4 * 4^j))) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hsum : ∑ j ∈ Finset.range J,
      ((2:ℝ)^j * Real.exp (-(π/4 * 4^j)) + if j = 0 then 1 else 0) ≤ 2 := by
    rw [Finset.sum_add_distrib]
    have h1 := sum_shell_series_le J
    have h2 : ∑ j ∈ Finset.range J, (if j = 0 then (1:ℝ) else 0) ≤ 1 := by
      rcases Nat.eq_zero_or_pos J with hJ | hJ
      · subst hJ; simp
      · rw [Finset.sum_ite_eq' (Finset.range J) 0 (fun _ => (1:ℝ))]
        rw [if_pos (Finset.mem_range.mpr hJ)]
    linarith
  have hcoef : (0:ℝ) ≤ 256*(h:ℝ)*L := by positivity
  calc 256*(h:ℝ)*L * ∑ j ∈ Finset.range J,
        ((2:ℝ)^j * Real.exp (-(π/4 * 4^j)) + if j = 0 then 1 else 0)
      ≤ 256*(h:ℝ)*L * 2 := mul_le_mul_of_nonneg_left hsum hcoef
    _ = 512*(h:ℝ)*L := by ring

open Finset Real in
/-- **The two-sided inner sum** (Track R, M0-aa): the full
Gaussian-weighted prime log-mass around `m`, on both sides of the
centre.  The range `(m − 1 − a_J, m + a_J]` splits at `m − 1` and at
`m` into the left shells (`inner_sum_le_left`), the single diagonal
term `p = m`, and the right shells (`inner_sum_le`).  The diagonal is
exactly what the `−1` in the left cut points was reserving: it carries
no Gaussian decay at all (`e^0 = 1`), so it contributes a bare
`log m` — harmless beside the main term, but it cannot be swept into
either shell family, since both require a strictly positive gap. -/
theorem inner_sum_two_sided_le (T : ℝ) (m h J : ℕ) (hh : 2 ≤ h)
    (hscale : 2*(m:ℝ) ≤ (h:ℝ)*T) (hfit : (2^J - 1)*h + 1 ≤ m)
    (hwfit : ∀ j < J, 2^j*h ≤ 2*m) :
    ∑ p ∈ (Finset.Ioc (m - 1 - (2^J - 1)*h)
        (m + (2^J - 1)*h)).filter Nat.Prime,
        Real.log p * Real.exp (-(π*T^2*(Real.log p - Real.log m)^2))
      ≤ 1024*(h:ℝ)*(Real.log (4*(m:ℝ)+2)/Real.log ((h:ℕ):ℝ))
          + Real.log (m:ℝ) := by
  classical
  have hm1 : 1 ≤ m := by omega
  have hfitR : (2^J - 1)*h ≤ m := by omega
  have hleAB : m - 1 - (2^J - 1)*h ≤ m - 1 := by omega
  have hleBD : m - 1 ≤ m + (2^J - 1)*h := by omega
  have hleBC : m - 1 ≤ m := by omega
  have hleCD : m ≤ m + (2^J - 1)*h := by omega
  -- the diagonal term carries no decay
  have hmid : ∑ p ∈ (Finset.Ioc (m - 1) m).filter Nat.Prime,
      Real.log p * Real.exp (-(π*T^2*(Real.log p - Real.log m)^2))
      ≤ Real.log (m:ℝ) := by
    have hsub : (Finset.Ioc (m - 1) m).filter Nat.Prime ⊆ {m} := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Ioc] at hp
      rw [Finset.mem_singleton]
      omega
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) ?_
    · intro i _ _
      have h0 : (0:ℝ) ≤ Real.log i := Real.log_natCast_nonneg i
      exact mul_nonneg h0 (Real.exp_pos _).le
    · rw [Finset.sum_singleton]
      have hz : Real.exp (-(π*T^2*(Real.log (m:ℝ) - Real.log (m:ℝ))^2)) = 1 := by
        simp
      rw [hz, mul_one]
  have hright := inner_sum_le T m h J hm1 hh hscale hfitR hwfit
  have hleft := inner_sum_le_left T m h J hh hscale hfit
  calc ∑ p ∈ (Finset.Ioc (m - 1 - (2^J - 1)*h)
          (m + (2^J - 1)*h)).filter Nat.Prime,
          Real.log p * Real.exp (-(π*T^2*(Real.log p - Real.log m)^2))
      = (∑ p ∈ (Finset.Ioc (m - 1 - (2^J - 1)*h) (m - 1)).filter Nat.Prime,
            Real.log p * Real.exp (-(π*T^2*(Real.log p - Real.log m)^2)))
          + (∑ p ∈ (Finset.Ioc (m - 1) m).filter Nat.Prime,
              Real.log p * Real.exp (-(π*T^2*(Real.log p - Real.log m)^2)))
          + (∑ p ∈ (Finset.Ioc m (m + (2^J - 1)*h)).filter Nat.Prime,
              Real.log p
                * Real.exp (-(π*T^2*(Real.log p - Real.log m)^2))) := by
        rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
          Finset.sum_filter,
          ← Finset.sum_Ioc_consecutive _ hleAB hleBD,
          ← Finset.sum_Ioc_consecutive _ hleBC hleCD]
        ring
    _ ≤ 512*(h:ℝ)*(Real.log (4*(m:ℝ)+2)/Real.log ((h:ℕ):ℝ))
          + Real.log (m:ℝ)
          + 512*(h:ℝ)*(Real.log (4*(m:ℝ)+2)/Real.log ((h:ℕ):ℝ)) := by
        have := add_le_add (add_le_add hleft hmid) hright
        linarith
    _ = 1024*(h:ℝ)*(Real.log (4*(m:ℝ)+2)/Real.log ((h:ℕ):ℝ))
          + Real.log (m:ℝ) := by ring

open Finset Real in
/-- **The log-gap inside a dyadic block** (Track R, M0-bb): two points
of `(N, 2N]` separated by at least `A` are separated multiplicatively
by at least `A/(2N)`.  This is what makes the tail of the mean value
theorem harmless: the shells of `inner_sum_two_sided_le` reach only to
`a_J ≈ N/2` (they cannot reach `2N`, since `inner_sum_le` needs
`a_J ≤ m`), so everything beyond them is at multiplicative distance
`≳ 1/4` from the centre — a *fixed* gap, not a shrinking one, which the
Gaussian kills super-exponentially in `T`. -/
theorem log_gap_of_dyadic (N n m : ℕ) (hn : N < n) (hn2 : n ≤ 2*N)
    (hm : N < m) (hm2 : m ≤ 2*N) (A : ℝ) (hA : 0 ≤ A)
    (hgap : A ≤ |(n:ℝ) - (m:ℝ)|) :
    A/(2*(N:ℝ)) ≤ |Real.log (n:ℝ) - Real.log (m:ℝ)| := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN1
  have hn1 : 1 ≤ n := by omega
  have hm1 : 1 ≤ m := by omega
  -- the ordered case, applied to whichever of `n`, `m` is larger
  have key : ∀ u v : ℕ, 1 ≤ u → u < v → v ≤ 2*N → A ≤ (v:ℝ) - (u:ℝ) →
      A/(2*(N:ℝ)) ≤ Real.log (v:ℝ) - Real.log (u:ℝ) := by
    intro u v hu huv hv2 hA'
    have hlog := log_sub_log_ge u v hu huv
    refine le_trans ?_ hlog
    have hv1 : 1 ≤ v := by omega
    have hv0 : (0:ℝ) < (v:ℝ) := by exact_mod_cast hv1
    have hv2R : (v:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast hv2
    have huvR : (u:ℝ) ≤ (v:ℝ) := by exact_mod_cast huv.le
    rw [div_le_div_iff₀ (by positivity) hv0]
    nlinarith [hA', hv2R, huvR, hN0]
  rcases lt_trichotomy n m with hlt | heq | hgt
  · have hnm : (n:ℝ) ≤ (m:ℝ) := by exact_mod_cast hlt.le
    have habs : |(n:ℝ) - (m:ℝ)| = (m:ℝ) - (n:ℝ) := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (by linarith)
    rw [habs] at hgap
    rw [abs_sub_comm]
    exact le_trans (key n m hn1 hlt hm2 hgap) (le_abs_self _)
  · subst heq
    have hA0 : A = 0 := by
      have hz : |(n:ℝ) - (n:ℝ)| = 0 := by simp
      rw [hz] at hgap
      linarith
    rw [hA0]
    simp
  · have hmn : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hgt.le
    have habs : |(n:ℝ) - (m:ℝ)| = (n:ℝ) - (m:ℝ) :=
      abs_of_nonneg (by linarith)
    rw [habs] at hgap
    exact le_trans (key m n hm1 hgt hn2 hgap) (le_abs_self _)

open Finset Real in
/-- **The Gaussian tail** (Track R, M0-bb): a sum whose every term sits
at multiplicative distance at least `g` from the centre is damped by the
single factor `e^{−πT²g²}`.  Together with `log_gap_of_dyadic` this
disposes of everything the shells of `inner_sum_two_sided_le` do not
reach: there `g` is bounded below by a constant, so the factor decays
super-exponentially in `T` and beats the trivial count `∑ log n`. -/
theorem gaussian_tail_sum_le (T : ℝ) (S : Finset ℕ) (m : ℕ) (g : ℝ)
    (hg : 0 ≤ g)
    (hgap : ∀ n ∈ S, g ≤ |Real.log (n:ℝ) - Real.log (m:ℝ)|)
    (B : ℝ) (hB : ∑ n ∈ S, Real.log (n:ℝ) ≤ B) :
    ∑ n ∈ S, Real.log (n:ℝ)
        * Real.exp (-(π*T^2*(Real.log (n:ℝ) - Real.log (m:ℝ))^2))
      ≤ Real.exp (-(π*T^2*g^2)) * B := by
  classical
  have hterm : ∀ n ∈ S, Real.log (n:ℝ)
      * Real.exp (-(π*T^2*(Real.log (n:ℝ) - Real.log (m:ℝ))^2))
      ≤ Real.exp (-(π*T^2*g^2)) * Real.log (n:ℝ) := by
    intro n hn
    have hlog0 : (0:ℝ) ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
    have hsq : g^2 ≤ (Real.log (n:ℝ) - Real.log (m:ℝ))^2 := by
      have h1 := hgap n hn
      calc g^2 ≤ |Real.log (n:ℝ) - Real.log (m:ℝ)|^2 :=
            pow_le_pow_left₀ hg h1 2
        _ = (Real.log (n:ℝ) - Real.log (m:ℝ))^2 := sq_abs _
    have hexp : Real.exp (-(π*T^2*(Real.log (n:ℝ) - Real.log (m:ℝ))^2))
        ≤ Real.exp (-(π*T^2*g^2)) := by
      refine Real.exp_le_exp.mpr ?_
      have hpi : (0:ℝ) ≤ π*T^2 := by positivity
      nlinarith [hsq, hpi]
    calc Real.log (n:ℝ)
          * Real.exp (-(π*T^2*(Real.log (n:ℝ) - Real.log (m:ℝ))^2))
        ≤ Real.log (n:ℝ) * Real.exp (-(π*T^2*g^2)) :=
          mul_le_mul_of_nonneg_left hexp hlog0
      _ = Real.exp (-(π*T^2*g^2)) * Real.log (n:ℝ) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le

open Finset Real in
/-- **The scale is admissible** (Track R, M0-cc): the dyadic scale
`h = ⌈2m/T⌉` satisfies the calibration `2m ≤ hT` that
`shell_exponent_le` demands.  This is the whole reason the ceiling is
taken upward. -/
theorem ceil_scale_mul_le (T : ℝ) (m : ℕ) (hT : 0 < T) :
    2*(m:ℝ) ≤ ((⌈2*(m:ℝ)/T⌉₊ : ℕ):ℝ) * T := by
  have hle : 2*(m:ℝ)/T ≤ ((⌈2*(m:ℝ)/T⌉₊ : ℕ):ℝ) := Nat.le_ceil _
  rw [div_le_iff₀ hT] at hle
  exact hle

open Finset Real in
/-- **The scale is at least two** (Track R, M0-cc): `⌈2m/T⌉ ≥ 2`, which
is what the Brun–Titchmarsh count needs (`log h` must be positive).
Uses only `T ≥ 2` and `T² ≤ m`, which together give `m ≥ 2T > T`. -/
theorem two_le_ceil_scale (T : ℝ) (m : ℕ) (hT : 2 ≤ T) (hTm : T^2 ≤ (m:ℝ)) :
    2 ≤ ⌈2*(m:ℝ)/T⌉₊ := by
  have hT0 : (0:ℝ) < T := by linarith
  have hm : (2:ℝ) ≤ (m:ℝ) := by nlinarith [hTm, hT]
  have hlt : (1:ℝ) < 2*(m:ℝ)/T := by
    rw [lt_div_iff₀ hT0]
    nlinarith [hTm, hT, hm]
  have h1 : 1 < ⌈2*(m:ℝ)/T⌉₊ := by
    rw [Nat.lt_ceil]
    exact_mod_cast hlt
  omega

open Finset Real in
/-- **The log-ratio at the dyadic scale** (Track R, M0-cc): with
`h = ⌈2m/T⌉` and `T² ≤ m`, the Brun–Titchmarsh ratio
`log(4m+2)/log h` is bounded by the absolute constant `6`.

The mechanism is that `h` is *polynomially large* in `m`: from
`h ≥ 2m/T` and `T² ≤ m` we get `h² ≥ 4m²/T² ≥ 4m ≥ m`, so
`log h ≥ ½·log m` — no square roots needed, just squaring the scale.
Against `log(4m+2) ≤ 3·log m` this gives `6`.  This is the step that
turns the inner sum's `h·log(4m+2)/log h` into a clean `O(h)`, and
hence — after the factor `T` from the Gaussian transform — into the
`O(m)` that GHS Lemma 2.6 requires. -/
theorem log_ratio_ceil_scale_le (T : ℝ) (m : ℕ) (hT : 2 ≤ T)
    (hTm : T^2 ≤ (m:ℝ)) :
    Real.log (4*(m:ℝ)+2)/Real.log ((⌈2*(m:ℝ)/T⌉₊ : ℕ):ℝ) ≤ 6 := by
  have hT0 : (0:ℝ) < T := by linarith
  have hm4 : (4:ℝ) ≤ (m:ℝ) := by nlinarith [hTm, hT]
  have hm0 : (0:ℝ) < (m:ℝ) := by linarith
  -- the scale is polynomially large: `h² ≥ m`
  have hge : 2*(m:ℝ)/T ≤ ((⌈2*(m:ℝ)/T⌉₊ : ℕ):ℝ) := Nat.le_ceil _
  have hh0 : (0:ℝ) ≤ ((⌈2*(m:ℝ)/T⌉₊ : ℕ):ℝ) := Nat.cast_nonneg _
  have hdiv : (0:ℝ) < 2*(m:ℝ)/T := by positivity
  have hsq : (m:ℝ) ≤ ((⌈2*(m:ℝ)/T⌉₊ : ℕ):ℝ)^2 := by
    have hstep : (2*(m:ℝ)/T)^2 ≤ ((⌈2*(m:ℝ)/T⌉₊ : ℕ):ℝ)^2 :=
      pow_le_pow_left₀ hdiv.le hge 2
    have hexp : (2*(m:ℝ)/T)^2 = 4*(m:ℝ)^2/T^2 := by
      field_simp
      ring
    rw [hexp] at hstep
    have hT2 : (0:ℝ) < T^2 := by positivity
    have hfrac : (m:ℝ) ≤ 4*(m:ℝ)^2/T^2 := by
      rw [le_div_iff₀ hT2]
      nlinarith [hTm, hm0]
    linarith
  -- hence `log h ≥ ½ log m`
  have hlogm : (0:ℝ) < Real.log (m:ℝ) := Real.log_pos (by linarith)
  have hlogsq : Real.log (m:ℝ)
      ≤ 2 * Real.log ((⌈2*(m:ℝ)/T⌉₊ : ℕ):ℝ) := by
    have h1 : Real.log (m:ℝ)
        ≤ Real.log (((⌈2*(m:ℝ)/T⌉₊ : ℕ):ℝ)^2) := Real.log_le_log hm0 hsq
    rwa [Real.log_pow] at h1
  have hlogh : (0:ℝ) < Real.log ((⌈2*(m:ℝ)/T⌉₊ : ℕ):ℝ) := by linarith
  -- and the numerator is at most `3 log m`
  have hnum : Real.log (4*(m:ℝ)+2) ≤ 3 * Real.log (m:ℝ) := by
    have hcube : 4*(m:ℝ)+2 ≤ (m:ℝ)^3 := by
      have h2 : (0:ℝ) ≤ (m:ℝ)^2 * ((m:ℝ) - 4) :=
        mul_nonneg (sq_nonneg _) (by linarith)
      have h3 : (0:ℝ) ≤ (m:ℝ) * ((m:ℝ) - 4) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [h2, h3, hm4]
    have h1 : Real.log (4*(m:ℝ)+2) ≤ Real.log ((m:ℝ)^3) :=
      Real.log_le_log (by linarith) hcube
    rwa [Real.log_pow] at h1
  rw [div_le_iff₀ hlogh]
  linarith

open Finset Real in
/-- **The shell count exists** (Track R, M0-dd): for any centre `m` and
scale `h` there is a number of shells `J` reaching as far as possible
without overshooting — `a_J = (2^J − 1)h` stays strictly below `m`,
while one more shell would reach `m`.

Both bounds are needed downstream and for opposite reasons.  `a_J < m`
is the fitting hypothesis of `inner_sum_two_sided_le` (the shells must
stay inside `(m/2, 2m]`, and on the left they must not run past `0`).
`m ≤ a_{J+1} = 2a_J + h` is what makes the shells *reach*: it forces
`a_J ≥ (m − h)/2`, so everything the shells miss is at additive
distance `≳ m/2` and hence — by `log_gap_of_dyadic` — at a fixed
multiplicative distance, where the Gaussian tail takes over.  The two
together are exactly the maximality of `J`. -/
theorem exists_shell_count (m h : ℕ) (hm : 1 ≤ m) (hh : 1 ≤ h) :
    ∃ J, (2^J - 1)*h + 1 ≤ m ∧ m ≤ (2^(J+1) - 1)*h
      ∧ ∀ j < J, 2^j*h ≤ 2*m := by
  classical
  -- some shell count overshoots, so there is a least one
  have hex : ∃ K, m ≤ (2^K - 1)*h := by
    refine ⟨m + 1, ?_⟩
    have hpow : m + 1 < 2^(m+1) := Nat.lt_two_pow_self
    have h1 : m + 1 ≤ (2^(m+1) - 1) := by omega
    calc m ≤ m + 1 := by omega
      _ = (m+1)*1 := by ring
      _ ≤ (2^(m+1) - 1)*h := Nat.mul_le_mul h1 hh
  set K := Nat.find hex with hK_def
  have hKspec : m ≤ (2^K - 1)*h := Nat.find_spec hex
  -- the least overshooting count is not `0`, since `a_0 = 0 < m`
  have hK0 : K ≠ 0 := by
    intro h0
    rw [h0] at hKspec
    simp at hKspec
    omega
  obtain ⟨J, hJ⟩ : ∃ J, K = J + 1 := ⟨K - 1, by omega⟩
  refine ⟨J, ?_, ?_, ?_⟩
  · -- `J` itself does not overshoot, by minimality
    have hnot : ¬ (m ≤ (2^J - 1)*h) := Nat.find_min hex (by omega)
    omega
  · rw [← hJ]
    exact hKspec
  · intro j hj
    have hnot : ¬ (m ≤ (2^J - 1)*h) := Nat.find_min hex (by omega)
    have hlt : (2:ℕ)^j < 2^J := Nat.pow_lt_pow_right (by norm_num) hj
    have hle : (2:ℕ)^j ≤ 2^J - 1 := by omega
    have hmul : 2^j*h ≤ (2^J - 1)*h := Nat.mul_le_mul_right h hle
    omega

end ExpSums

end MoltResearch
