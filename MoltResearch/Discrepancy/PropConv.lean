import MoltResearch.Discrepancy.LogUniform
import MoltResearch.Discrepancy.ChebyshevBlock

/-!
# Discrepancy: Proposition conv

Track C, Elliott campaign (`Problems/tao2015_derivation_c.md`, issue #2946, E5 capstone):
the medium-prime double sum is large whenever the base conjugate-pair correlation is —
assembled from the per-`(p,j)` toc estimate, the Chebyshev block mass, and explicit
error aggregation.
-/

namespace MoltResearch

open Finset

set_option maxHeartbeats 1600000 in
/-- **Proposition `conv`** (arXiv:1509.05422, unit-dilation conjugate-pair form): if
the base correlation is large, then the medium-prime double sum — the object the
entropy decrement argument evaluates through `F(X_H, Y_H)` — is large: the main term
is `J·(∑_{p ∈ block} 1/p)·‖S₀‖`, the block mass is at least `(log 4/12)/log(2n₀)`
(Chebyshev), and the aggregated toc errors are explicit. -/
theorem prop_conv {g : ℕ → ℂ} (hcm : CompletelyMultiplicativeC g)
    (huni : Unimodular g) {n₀ h J A B : ℕ} (hn₀ : 2 ^ 28 ≤ n₀)
    (hA : 2 * n₀ ≤ A) (hpB : 2 * n₀ * A ≤ B) {X : ℝ}
    (hface : X ≤ ‖∑ m ∈ Finset.Ioc A B,
      g m * (starRingEnd ℂ) (g (m + h)) / (m : ℂ)‖) :
    (J : ℝ) * (Real.log 4 / 12 / Real.log (2 * (n₀ : ℝ))) * X
      - 3 * (J : ℝ) ^ 2 * (n₀ : ℝ) / A
      - (J : ℝ) * (2 * Real.log (2 * (n₀ : ℝ)) + 2)
      ≤ ‖∑ p ∈ (2 * n₀ + 1).primesBelow.filter (fun p => n₀ < p),
          ∑ j ∈ Finset.Icc 1 J, ∑ n ∈ Finset.Ioc A B,
            (if (n + j) % p = 0
              then g (n + j) * (starRingEnd ℂ) (g (n + j + p * h)) else 0)
              / (n : ℂ)‖ := by
  classical
  set P := (2 * n₀ + 1).primesBelow.filter (fun p => n₀ < p) with hP
  set S₀ : ℂ := ∑ m ∈ Finset.Ioc A B,
    g m * (starRingEnd ℂ) (g (m + h)) / (m : ℂ) with hS₀
  have hn₀1 : 1 ≤ n₀ := le_trans (by norm_num) hn₀
  have hn₀R : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀1
  have hA1 : 1 ≤ A := by omega
  have hAR : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA1
  have hblock : ∀ p ∈ P, 2 ≤ p ∧ n₀ < p ∧ p ≤ 2 * n₀ := by
    intro p hp
    rw [hP, Finset.mem_filter] at hp
    have hpp := Nat.prime_of_mem_primesBelow hp.1
    have hlt := Nat.lt_of_mem_primesBelow hp.1
    exact ⟨hpp.two_le, hp.2, by omega⟩
  have hcardP : (P.card : ℝ) ≤ (n₀ : ℝ) := by
    have hsub : P ⊆ Finset.Ioc n₀ (2 * n₀) := by
      intro p hp
      obtain ⟨-, h1, h2⟩ := hblock p hp
      rw [Finset.mem_Ioc]
      exact ⟨h1, h2⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Ioc] at this
    have h2 : P.card ≤ n₀ := by omega
    exact_mod_cast h2
  -- the per-pair toc bounds, aggregated
  have htoc : ∀ p ∈ P, ∀ j ∈ Finset.Icc 1 J,
      ‖(∑ n ∈ Finset.Ioc A B,
          (if (n + j) % p = 0
            then g (n + j) * (starRingEnd ℂ) (g (n + j + p * h)) else 0) / (n : ℂ))
        - (1 / (p : ℂ)) * S₀‖
      ≤ 3 * (j : ℝ) / A + (2 * Real.log (2 * (n₀ : ℝ)) + 2) / p := by
    intro p hp j _
    obtain ⟨hp2, hpn₀, hp2n₀⟩ := hblock p hp
    have hbase := norm_toc_sub_le hcm huni hp2 (h := h) (j := j)
      (le_trans hp2n₀ hA) (le_trans (Nat.mul_le_mul_right A hp2n₀) hpB)
    refine le_trans hbase ?_
    have hp0R : (0 : ℝ) < (p : ℝ) := by
      have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      linarith
    have hlogmono : Real.log p ≤ Real.log (2 * (n₀ : ℝ)) := by
      refine Real.log_le_log hp0R ?_
      have : (p : ℝ) ≤ 2 * (n₀ : ℝ) := by exact_mod_cast hp2n₀
      linarith
    have hmono2 : (2 * Real.log p + 2) / (p : ℝ)
        ≤ (2 * Real.log (2 * (n₀ : ℝ)) + 2) / (p : ℝ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by linarith [hlogmono]) (by positivity)
    linarith [hmono2]
  -- decompose: double sum = (count-weighted mass)·S₀ + error
  set T : ℕ → ℕ → ℂ := fun p j => ∑ n ∈ Finset.Ioc A B,
    (if (n + j) % p = 0
      then g (n + j) * (starRingEnd ℂ) (g (n + j + p * h)) else 0) / (n : ℂ) with hT
  have hdecomp : ∑ p ∈ P, ∑ j ∈ Finset.Icc 1 J, T p j
      = (∑ p ∈ P, ∑ j ∈ Finset.Icc 1 J, (1 / (p : ℂ))) * S₀
        + ∑ p ∈ P, ∑ j ∈ Finset.Icc 1 J, (T p j - (1 / (p : ℂ)) * S₀) := by
    rw [Finset.sum_mul]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- the error sum
  have herr : ‖∑ p ∈ P, ∑ j ∈ Finset.Icc 1 J, (T p j - (1 / (p : ℂ)) * S₀)‖
      ≤ 3 * (J : ℝ) ^ 2 * (n₀ : ℝ) / A
        + (J : ℝ) * (2 * Real.log (2 * (n₀ : ℝ)) + 2) := by
    refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum
      (fun p hp => norm_sum_le _ _)) ?_)
    have hinner : ∀ p ∈ P, ∑ j ∈ Finset.Icc 1 J,
        ‖T p j - (1 / (p : ℂ)) * S₀‖
          ≤ 3 * (J : ℝ) ^ 2 / A + (J : ℝ) * ((2 * Real.log (2 * (n₀ : ℝ)) + 2) / p) := by
      intro p hp
      have hstep := Finset.sum_le_sum (fun j hj => htoc p hp j hj)
      refine le_trans hstep ?_
      rw [Finset.sum_add_distrib]
      have hj1 : ∑ j ∈ Finset.Icc 1 J, 3 * (j : ℝ) / A ≤ 3 * (J : ℝ) ^ 2 / A := by
        have hterm : ∀ j ∈ Finset.Icc 1 J, 3 * (j : ℝ) / A ≤ 3 * (J : ℝ) / A := by
          intro j hj
          rw [Finset.mem_Icc] at hj
          have : (j : ℝ) ≤ (J : ℝ) := by exact_mod_cast hj.2
          have hA0 : (0 : ℝ) < (A : ℝ) := by linarith
          gcongr
        refine le_trans (Finset.sum_le_sum hterm) ?_
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        have hcard : ((J + 1 - 1 : ℕ) : ℝ) = (J : ℝ) := by
          rw [Nat.add_sub_cancel]
        rw [hcard]
        rw [show 3 * (J : ℝ) ^ 2 / A = (J : ℝ) * (3 * (J : ℝ) / A) from by ring]
      have hj2 : ∑ _j ∈ Finset.Icc 1 J, (2 * Real.log (2 * (n₀ : ℝ)) + 2) / (p : ℝ)
          = (J : ℝ) * ((2 * Real.log (2 * (n₀ : ℝ)) + 2) / p) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
      rw [hj2]
      linarith [hj1]
    refine le_trans (Finset.sum_le_sum hinner) ?_
    rw [Finset.sum_add_distrib]
    have h1 : ∑ _p ∈ P, 3 * (J : ℝ) ^ 2 / A ≤ 3 * (J : ℝ) ^ 2 * (n₀ : ℝ) / A := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hA0 : (0 : ℝ) < (A : ℝ) := by linarith
      have hJ0 : (0 : ℝ) ≤ 3 * (J : ℝ) ^ 2 / A := by positivity
      calc (P.card : ℝ) * (3 * (J : ℝ) ^ 2 / A)
          ≤ (n₀ : ℝ) * (3 * (J : ℝ) ^ 2 / A) := by nlinarith [hcardP]
        _ = 3 * (J : ℝ) ^ 2 * (n₀ : ℝ) / A := by ring
    have h2 : ∑ p ∈ P, (J : ℝ) * ((2 * Real.log (2 * (n₀ : ℝ)) + 2) / p)
        ≤ (J : ℝ) * (2 * Real.log (2 * (n₀ : ℝ)) + 2) := by
      have hppos : ∀ p ∈ P, (1 : ℝ) / (p : ℝ) ≤ 1 / (n₀ : ℝ) := by
        intro p hp
        obtain ⟨-, h1', -⟩ := hblock p hp
        have hn₀0 : (0 : ℝ) < (n₀ : ℝ) := by linarith
        have : (n₀ : ℝ) ≤ (p : ℝ) := by exact_mod_cast le_of_lt h1'
        gcongr
      have hlogpos : (0 : ℝ) ≤ 2 * Real.log (2 * (n₀ : ℝ)) + 2 := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (n₀ : ℝ) by linarith)
        linarith
      have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
      have hstep : ∀ p ∈ P, (J : ℝ) * ((2 * Real.log (2 * (n₀ : ℝ)) + 2) / p)
          ≤ (J : ℝ) * ((2 * Real.log (2 * (n₀ : ℝ)) + 2) / n₀) := by
        intro p hp
        have h3 := hppos p hp
        have h4 : (2 * Real.log (2 * (n₀ : ℝ)) + 2) / (p : ℝ)
            ≤ (2 * Real.log (2 * (n₀ : ℝ)) + 2) / (n₀ : ℝ) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, ← one_div, ← one_div]
          nlinarith [h3, hlogpos]
        nlinarith [h4, hJ0]
      refine le_trans (Finset.sum_le_sum hstep) ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hn₀0 : (0 : ℝ) < (n₀ : ℝ) := by linarith
      calc (P.card : ℝ) * ((J : ℝ) * ((2 * Real.log (2 * (n₀ : ℝ)) + 2) / n₀))
          ≤ (n₀ : ℝ) * ((J : ℝ) * ((2 * Real.log (2 * (n₀ : ℝ)) + 2) / n₀)) := by
            have hpos : (0 : ℝ) ≤ (J : ℝ) * ((2 * Real.log (2 * (n₀ : ℝ)) + 2) / n₀) := by
              positivity
            nlinarith [hcardP]
        _ = (J : ℝ) * (2 * Real.log (2 * (n₀ : ℝ)) + 2) := by
            have hne : (n₀ : ℝ) ≠ 0 := by linarith
            field_simp
    linarith
  -- the main term
  have hmass : Real.log 4 / 12 / Real.log (2 * (n₀ : ℝ)) ≤ ∑ p ∈ P, (1 : ℝ) / p := by
    have hraw := sum_one_div_prime_block_ge (n := n₀) hn₀
    rw [hP]
    exact hraw
  have hcount : ∑ p ∈ P, ∑ _j ∈ Finset.Icc 1 J, (1 / (p : ℂ))
      = (((J : ℝ) * ∑ p ∈ P, (1 : ℝ) / p : ℝ) : ℂ) := by
    have hper : ∀ p ∈ P, ∑ _j ∈ Finset.Icc 1 J, (1 / (p : ℂ))
        = (J : ℂ) * (1 / (p : ℂ)) := by
      intro p _
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
    rw [Finset.sum_congr rfl hper]
    push_cast
    rw [Finset.mul_sum]
  have hmain : ‖(∑ p ∈ P, ∑ j ∈ Finset.Icc 1 J, (1 / (p : ℂ))) * S₀‖
      = ((J : ℝ) * ∑ p ∈ P, (1 : ℝ) / p) * ‖S₀‖ := by
    rw [hcount, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hnn : (0 : ℝ) ≤ (J : ℝ) * ∑ p ∈ P, (1 : ℝ) / p := by
      have : (0 : ℝ) ≤ ∑ p ∈ P, (1 : ℝ) / p :=
        Finset.sum_nonneg fun p _ => by positivity
      positivity
    rw [abs_of_nonneg hnn]
  -- assemble: reverse triangle
  have hrev : ‖(∑ p ∈ P, ∑ j ∈ Finset.Icc 1 J, (1 / (p : ℂ))) * S₀‖
      - ‖∑ p ∈ P, ∑ j ∈ Finset.Icc 1 J, (T p j - (1 / (p : ℂ)) * S₀)‖
      ≤ ‖∑ p ∈ P, ∑ j ∈ Finset.Icc 1 J, T p j‖ := by
    have hme : (∑ p ∈ P, ∑ j ∈ Finset.Icc 1 J, (1 / (p : ℂ))) * S₀
        = (∑ p ∈ P, ∑ j ∈ Finset.Icc 1 J, T p j)
          - ∑ p ∈ P, ∑ j ∈ Finset.Icc 1 J, (T p j - (1 / (p : ℂ)) * S₀) := by
      rw [hdecomp]
      ring
    have h := norm_sub_le
      (∑ p ∈ P, ∑ j ∈ Finset.Icc 1 J, T p j)
      (∑ p ∈ P, ∑ j ∈ Finset.Icc 1 J, (T p j - (1 / (p : ℂ)) * S₀))
    rw [← hme] at h
    linarith
  have hS₀X : X ≤ ‖S₀‖ := hface
  have hmasspos : (0 : ℝ) ≤ Real.log 4 / 12 / Real.log (2 * (n₀ : ℝ)) := by
    have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have h2n : (0 : ℝ) < Real.log (2 * (n₀ : ℝ)) := by
      refine Real.log_pos ?_
      linarith
    positivity
  have hfinal : ((J : ℝ) * (Real.log 4 / 12 / Real.log (2 * (n₀ : ℝ)))) * X
      ≤ ((J : ℝ) * ∑ p ∈ P, (1 : ℝ) / p) * ‖S₀‖ := by
    have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
    have hsum0 : (0 : ℝ) ≤ ∑ p ∈ P, (1 : ℝ) / p :=
      Finset.sum_nonneg fun p _ => by positivity
    have hnorm0 : (0 : ℝ) ≤ ‖S₀‖ := norm_nonneg _
    calc ((J : ℝ) * (Real.log 4 / 12 / Real.log (2 * (n₀ : ℝ)))) * X
        ≤ ((J : ℝ) * (Real.log 4 / 12 / Real.log (2 * (n₀ : ℝ)))) * ‖S₀‖ := by
          nlinarith [mul_nonneg (mul_nonneg hJ0 hmasspos) (sub_nonneg.mpr hS₀X)]
      _ ≤ ((J : ℝ) * ∑ p ∈ P, (1 : ℝ) / p) * ‖S₀‖ := by
          nlinarith [mul_nonneg (mul_nonneg hJ0 (sub_nonneg.mpr hmass)) hnorm0]
  linarith [hrev, herr, hmain.symm.le, hmain.le, hfinal]

end MoltResearch
