import MoltResearch.Discrepancy.SelbergGFloor
import Mathlib.NumberTheory.Primorial

/-!
# Discrepancy: the Selberg sieve at the primorial modulus

Track S of the EDP-unconditional campaign (`Problems/tao2015_derivation_c.md`,
issue #3004): the per-target master bound. With the sifting modulus
`P := primorial z` and the Selberg weights truncated at `z`, for any even
target `s`:

  `#{n ∈ (a, a+N] : ∀ p ≤ z, p ∤ n(s−n)} ≤ N/G(z) + z⁸`.

The primorial layer (`squarefree_primorial`, `primeFactors_primorial`,
`sieveRootCard_lt_of_even` — evenness of `s` kills the `ρ(2) = 2`
degeneracy) feeds the S3–S5 structural chain; the error term is the crude
`|λ_d| ≤ 3^ω(d) ≤ d²`, `ρ(d) ≤ d` estimate over `d ≤ z`
(`three_pow_mul_rootCard_le`), which the polynomially small sift level
absorbs. Combined with the `G`-floor chain (S6) and the coprime harmonic
floor (S7), this yields the per-target bound
`≪ N·∏_{p∣2s}(1−1/p)⁻²/log²z + z⁸` that the additive-quadruple count
consumes.
-/

namespace MoltResearch

open Finset

/-- The primorial is squarefree. -/
theorem squarefree_primorial (z : ℕ) : Squarefree (primorial z) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro p hp q hq hpq
    rw [Finset.mem_coe, Finset.mem_filter] at hp hq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes hp.2 hq.2).mpr hpq)
  · intro p hp
    rw [Finset.mem_filter] at hp
    exact hp.2.squarefree

/-- The prime factors of the primorial: exactly the primes up to `z`. -/
theorem primeFactors_primorial (z : ℕ) :
    (primorial z).primeFactors
      = (Finset.range (z + 1)).filter Nat.Prime := by
  refine Nat.primeFactors_prod fun p hp => ?_
  rw [Finset.mem_filter] at hp
  exact hp.2

/-- Membership in the primorial's prime factors. -/
theorem mem_primeFactors_primorial {z p : ℕ} :
    p ∈ (primorial z).primeFactors ↔ p.Prime ∧ p ≤ z := by
  rw [primeFactors_primorial, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, by omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h1⟩

/-- For an even sift target, every primorial prime removes fewer residues
than its size: the nondegeneracy hypothesis of the Selberg weights. -/
theorem sieveRootCard_lt_of_even {s z : ℕ} (hs : 2 ∣ s) :
    ∀ p ∈ (primorial z).primeFactors, sieveRootCard s p < p := by
  intro p hp
  rw [primeFactors_primorial, Finset.mem_filter] at hp
  have hpp := hp.2
  rw [sieveRootCard_prime hpp]
  by_cases hps : p ∣ s
  · rw [if_pos hps]
    exact hpp.one_lt
  · rw [if_neg hps]
    have hp2 : p ≠ 2 := by
      intro hc
      subst hc
      exact hps hs
    have := hpp.two_le
    omega

/-- The crude weight-times-density bound: `3^ω(d)·ρ(d) ≤ d³`. -/
theorem three_pow_mul_rootCard_le {s d : ℕ} (hd : 0 < d) :
    (3 : ℝ) ^ d.primeFactors.card * (sieveRootCard s d : ℝ)
      ≤ (d : ℝ) ^ 3 := by
  have h1 : (3 : ℝ) ^ d.primeFactors.card ≤ (d : ℝ) ^ 2 := by
    have h2 : (3 : ℝ) ^ d.primeFactors.card
        ≤ ∏ p ∈ d.primeFactors, (p : ℝ) ^ 2 := by
      rw [← Finset.prod_const]
      refine Finset.prod_le_prod₀ (fun p _ => by norm_num) ?_
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have h3 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      nlinarith
    have h4 : ∏ p ∈ d.primeFactors, (p : ℝ) ^ 2
        = ((radN d : ℕ) : ℝ) ^ 2 := by
      rw [radN]
      push_cast
      rw [← Finset.prod_pow]
    have h5 : ((radN d : ℕ) : ℝ) ≤ (d : ℝ) := by
      exact_mod_cast Nat.le_of_dvd hd radN_dvd
    have h6 : (0 : ℝ) ≤ ((radN d : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [h2, h4.le, h4.ge]
  have h7 : (sieveRootCard s d : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast sieveRootCard_le s d
  have h8 : (0 : ℝ) ≤ (3 : ℝ) ^ d.primeFactors.card := by positivity
  have h9 : (0 : ℝ) ≤ (sieveRootCard s d : ℝ) := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  calc (3 : ℝ) ^ d.primeFactors.card * (sieveRootCard s d : ℝ)
      ≤ (d : ℝ) ^ 2 * (d : ℝ) :=
        mul_le_mul h1 h7 h9 (by positivity)
    _ = (d : ℝ) ^ 3 := by ring

/-- **The per-target sift master**: with the primorial modulus at sift level
`z` and the Selberg weights truncated at `z`, the sifted window count is at
most `N/G(z) + z⁸`. -/
theorem card_sift_le_primorial_master {s z N a : ℕ} (hs : 2 ∣ s)
    (hz : 1 ≤ z) :
    ((((Finset.Ioc a (a + N)).filter (fun n : ℕ =>
        ∀ p ∈ (primorial z).primeFactors,
          ¬ ((p : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ))))).card : ℝ))
      ≤ (N : ℝ) / selbergG s (primorial z) z + ((z : ℝ) ^ 4) ^ 2 := by
  classical
  have hP := squarefree_primorial z
  have hρlt := sieveRootCard_lt_of_even (z := z) hs
  have hquad := card_sift_le_quadratic (a := a) (b := a + N) (s := s) hP
    (Nat.le_add_right a N) (selbergLambda s (primorial z) z)
    (selbergLambda_one hP hz hρlt)
  have hQ := quadratic_selbergLambda_eq (R := z) hP hz hρlt
  rw [hQ] at hquad
  have hlen : ((a + N : ℕ) : ℝ) - (a : ℝ) = (N : ℝ) := by
    push_cast
    ring
  rw [hlen] at hquad
  have hG1 : (1 : ℝ) ≤ selbergG s (primorial z) z :=
    one_le_selbergG hP hz hρlt
  have hG0 : (0 : ℝ) < selbergG s (primorial z) z := by linarith
  have hNdiv : (N : ℝ) * (1 / selbergG s (primorial z) z)
      = (N : ℝ) / selbergG s (primorial z) z := by
    ring
  rw [hNdiv] at hquad
  refine le_trans hquad ?_
  -- bound the error sum by z⁴
  have herr : ∑ d ∈ (primorial z).divisors,
      |selbergLambda s (primorial z) z d| * (sieveRootCard s d : ℝ)
      ≤ (z : ℝ) ^ 4 := by
    have hsplit : ∀ d ∈ (primorial z).divisors,
        |selbergLambda s (primorial z) z d| * (sieveRootCard s d : ℝ)
        ≤ if d ≤ z then (z : ℝ) ^ 3 else 0 := by
      intro d hd
      by_cases hdz : d ≤ z
      · rw [if_pos hdz]
        have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
        have habs := abs_selbergLambda_le (R := z) hP hρlt hd
        have h3 := three_pow_mul_rootCard_le (s := s) hd0
        have hρ0 : (0 : ℝ) ≤ (sieveRootCard s d : ℝ) := Nat.cast_nonneg _
        have hdz3 : (d : ℝ) ^ 3 ≤ (z : ℝ) ^ 3 := by
          have h11 : (d : ℝ) ≤ (z : ℝ) := by exact_mod_cast hdz
          exact pow_le_pow_left₀ (Nat.cast_nonneg _) h11 3
        have hstep : |selbergLambda s (primorial z) z d|
            * (sieveRootCard s d : ℝ)
            ≤ (3 : ℝ) ^ d.primeFactors.card * (sieveRootCard s d : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hρ0
          calc |selbergLambda s (primorial z) z d|
              ≤ ((3 : ℕ) ^ d.primeFactors.card : ℝ) := by
                exact_mod_cast habs
            _ = (3 : ℝ) ^ d.primeFactors.card := by push_cast; rfl
        linarith [hstep, h3, hdz3]
      · rw [if_neg hdz, selbergLambda_eq_zero_of_gt (by omega), abs_zero,
          zero_mul]
    refine le_trans (Finset.sum_le_sum hsplit) ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul]
    have hcard : (((primorial z).divisors.filter (fun d => d ≤ z)).card : ℝ)
        ≤ (z : ℝ) := by
      have hsub : ((primorial z).divisors.filter (fun d => d ≤ z))
          ⊆ Finset.Icc 1 z := by
        intro d hd
        rw [Finset.mem_filter] at hd
        rw [Finset.mem_Icc]
        exact ⟨Nat.pos_of_mem_divisors hd.1, hd.2⟩
      have h1 := Finset.card_le_card hsub
      rw [Nat.card_Icc] at h1
      exact_mod_cast le_trans h1 (by omega)
    have hz3 : (0 : ℝ) ≤ (z : ℝ) ^ 3 := by positivity
    calc (((primorial z).divisors.filter (fun d => d ≤ z)).card : ℝ)
        * (z : ℝ) ^ 3
        ≤ (z : ℝ) * (z : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hcard hz3
      _ = (z : ℝ) ^ 4 := by ring
  have herr0 : (0 : ℝ) ≤ ∑ d ∈ (primorial z).divisors,
      |selbergLambda s (primorial z) z d| * (sieveRootCard s d : ℝ) := by
    refine Finset.sum_nonneg fun d _ => ?_
    exact mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
  have hsq : (∑ d ∈ (primorial z).divisors,
      |selbergLambda s (primorial z) z d| * (sieveRootCard s d : ℝ)) ^ 2
      ≤ ((z : ℝ) ^ 4) ^ 2 := by
    exact pow_le_pow_left₀ herr0 herr 2
  linarith [hsq]

end MoltResearch
