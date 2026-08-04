import MoltResearch.Discrepancy.LargeValues
import MoltResearch.Discrepancy.TuranKubilius

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

end ExpSums

end MoltResearch
