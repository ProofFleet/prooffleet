import MoltResearch.Discrepancy.SelbergQuadratic
import Mathlib.Tactic.LinearCombination

/-!
# Discrepancy: diagonalizing the Selberg quadratic form

Track S of the EDP-unconditional campaign (`Problems/tao2015_derivation_c.md`,
issue #3004): the diagonalization

  `Q(λ) = ∑_{k ∣ P} w(k) · (∑_{k ∣ d ∣ P} λ_d g(d))²`,
  `w(k) = ∏_{p ∣ k} (p − ρ(p))/ρ(p)`,  `g(d) = ρ(d)/d`,

turning the Selberg quadratic form into a nonnegatively-weighted sum of
squares. En route, reusable structure theory: the squarefree divisor-sum
dictionary (divisors ↔ subset products of primes, the Euler expansion
`∑_{k ∣ m} ∏_{p ∣ k} v(p) = ∏_{p ∣ m} (1 + v(p))` — the same expansion the
singular-series second moment consumes), prime factors of lcm/gcd as
union/intersection, squarefreeness of the lcm, the lcm·gcd root-count
multiplicativity, and the inverse-`g` identity `∑_{k ∣ m} w(k) = m/ρ(m)`.
-/

namespace MoltResearch

open Finset

/-- Divisors of a squarefree number are the subset products of its primes. -/
theorem sum_divisors_squarefree_eq_powerset {m : ℕ} (hm : Squarefree m)
    (f : ℕ → ℝ) :
    ∑ k ∈ m.divisors, f k
      = ∑ T ∈ m.primeFactors.powerset, f (∏ p ∈ T, p) := by
  classical
  refine Finset.sum_nbij' (fun k => k.primeFactors) (fun T => ∏ p ∈ T, p)
    ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_powerset]
    exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hk) hm.ne_zero
  · intro T hT
    rw [Finset.mem_powerset] at hT
    have hTp : ∀ p ∈ T, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors (hT hp)
    rw [Nat.mem_divisors]
    refine ⟨Finset.prod_primes_dvd m
      (fun p hp => (hTp p hp).prime)
      (fun p hp => Nat.dvd_of_mem_primeFactors (hT hp)), hm.ne_zero⟩
  · intro k hk
    exact Nat.prod_primeFactors_of_squarefree
      (hm.squarefree_of_dvd (Nat.dvd_of_mem_divisors hk))
  · intro T hT
    rw [Finset.mem_powerset] at hT
    exact Nat.primeFactors_prod (fun p hp =>
      Nat.prime_of_mem_primeFactors (hT hp))
  · intro k hk
    rw [Nat.prod_primeFactors_of_squarefree
      (hm.squarefree_of_dvd (Nat.dvd_of_mem_divisors hk))]

/-- **The Euler expansion over a squarefree modulus**. -/
theorem sum_divisors_prodPrimeFactors {m : ℕ} (hm : Squarefree m)
    (v : ℕ → ℝ) :
    ∑ k ∈ m.divisors, ∏ p ∈ k.primeFactors, v p
      = ∏ p ∈ m.primeFactors, (1 + v p) := by
  classical
  rw [sum_divisors_squarefree_eq_powerset hm]
  have hcong : ∀ T ∈ m.primeFactors.powerset,
      ∏ p ∈ (∏ p ∈ T, p).primeFactors, v p = ∏ p ∈ T, v p := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    rw [Nat.primeFactors_prod (fun p hp =>
      Nat.prime_of_mem_primeFactors (hT hp))]
  rw [Finset.sum_congr rfl hcong]
  have hpa := Finset.prod_add v (fun _ => (1 : ℝ)) m.primeFactors
  have h1 : ∀ T ∈ m.primeFactors.powerset,
      (∏ p ∈ T, v p) * ∏ _p ∈ m.primeFactors \ T, (1 : ℝ)
      = ∏ p ∈ T, v p := by
    intro T _
    rw [Finset.prod_const_one, mul_one]
  rw [Finset.sum_congr rfl h1] at hpa
  rw [← hpa]
  refine Finset.prod_congr rfl fun p _ => ?_
  ring

-- ===== S4b: lcm/gcd prime-factor identities =====

/-- Prime factors of the lcm: the union. -/
theorem primeFactors_lcm {d₁ d₂ : ℕ} (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    (Nat.lcm d₁ d₂).primeFactors = d₁.primeFactors ∪ d₂.primeFactors := by
  ext p
  rw [Finset.mem_union, Nat.mem_primeFactors, Nat.mem_primeFactors,
    Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hdvd, -⟩
    have hd12 : p ∣ d₁ * d₂ :=
      hdvd.trans (Nat.lcm_dvd (dvd_mul_right d₁ d₂) (dvd_mul_left d₂ d₁))
    rcases (Nat.Prime.dvd_mul hp).mp hd12 with h | h
    · exact Or.inl ⟨hp, h, h₁.ne'⟩
    · exact Or.inr ⟨hp, h, h₂.ne'⟩
  · rintro (⟨hp, hdvd, -⟩ | ⟨hp, hdvd, -⟩)
    · exact ⟨hp, hdvd.trans (Nat.dvd_lcm_left d₁ d₂),
        Nat.lcm_ne_zero h₁.ne' h₂.ne'⟩
    · exact ⟨hp, hdvd.trans (Nat.dvd_lcm_right d₁ d₂),
        Nat.lcm_ne_zero h₁.ne' h₂.ne'⟩

/-- Prime factors of the gcd: the intersection. -/
theorem primeFactors_gcd {d₁ d₂ : ℕ} (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    (Nat.gcd d₁ d₂).primeFactors = d₁.primeFactors ∩ d₂.primeFactors := by
  ext p
  rw [Finset.mem_inter, Nat.mem_primeFactors, Nat.mem_primeFactors,
    Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hdvd, -⟩
    rw [Nat.dvd_gcd_iff] at hdvd
    exact ⟨⟨hp, hdvd.1, h₁.ne'⟩, ⟨hp, hdvd.2, h₂.ne'⟩⟩
  · rintro ⟨⟨hp, hdvd₁, -⟩, ⟨-, hdvd₂, -⟩⟩
    exact ⟨hp, Nat.dvd_gcd_iff.mpr ⟨hdvd₁, hdvd₂⟩,
      Nat.pos_iff_ne_zero.mp (Nat.gcd_pos_of_pos_left d₂ h₁)⟩

/-- The lcm of squarefree numbers is squarefree. -/
theorem squarefree_lcm {d₁ d₂ : ℕ} (hsq₁ : Squarefree d₁)
    (hsq₂ : Squarefree d₂) : Squarefree (Nat.lcm d₁ d₂) := by
  have h₁ := hsq₁.ne_zero
  have h₂ := hsq₂.ne_zero
  rw [Nat.squarefree_iff_factorization_le_one (Nat.lcm_ne_zero h₁ h₂)]
  intro p
  rw [Nat.factorization_lcm h₁ h₂]
  have e1 : (d₁.factorization ⊔ d₂.factorization) p
      = d₁.factorization p ⊔ d₂.factorization p := rfl
  rw [e1]
  exact sup_le ((Nat.squarefree_iff_factorization_le_one h₁).mp hsq₁ p)
    ((Nat.squarefree_iff_factorization_le_one h₂).mp hsq₂ p)

/-- **Root-count multiplicativity across lcm/gcd** for squarefree arguments. -/
theorem sieveRootCard_lcm_mul_gcd {d₁ d₂ : ℕ} (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    (hsq₁ : Squarefree d₁) (hsq₂ : Squarefree d₂) (s : ℕ) :
    sieveRootCard s (Nat.lcm d₁ d₂) * sieveRootCard s (Nat.gcd d₁ d₂)
      = sieveRootCard s d₁ * sieveRootCard s d₂ := by
  have hsqL : Squarefree (Nat.lcm d₁ d₂) := squarefree_lcm hsq₁ hsq₂
  have hsqG : Squarefree (Nat.gcd d₁ d₂) :=
    Squarefree.squarefree_of_dvd (Nat.gcd_dvd_left d₁ d₂) hsq₁
  rw [sieveRootCard_squarefree s _ hsqL, sieveRootCard_squarefree s _ hsqG,
    sieveRootCard_squarefree s _ hsq₁, sieveRootCard_squarefree s _ hsq₂,
    primeFactors_lcm h₁ h₂, primeFactors_gcd h₁ h₂]
  exact Finset.prod_union_inter

/-- The inverse-`g` identity: over a squarefree modulus, the divisor sum of
`∏ (p−ρ)/ρ` is `m/ρ(m)`. -/
theorem sum_divisors_w_eq {m s : ℕ} (hm : Squarefree m) :
    ∑ k ∈ m.divisors,
        ∏ p ∈ k.primeFactors,
          (((p : ℝ) - sieveRootCard s p) / sieveRootCard s p)
      = (m : ℝ) / (sieveRootCard s m : ℝ) := by
  rw [sum_divisors_prodPrimeFactors hm]
  have hper : ∀ p ∈ m.primeFactors,
      1 + (((p : ℝ) - sieveRootCard s p) / sieveRootCard s p)
      = (p : ℝ) / sieveRootCard s p := by
    intro p hp
    have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
    have hρ : (0 : ℝ) < (sieveRootCard s p : ℝ) := by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one
        (one_le_sieveRootCard hp0 s)
    field_simp
    ring
  rw [Finset.prod_congr rfl hper, Finset.prod_div_distrib]
  have hnum : ∏ p ∈ m.primeFactors, (p : ℝ) = (m : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hm]
  have hden : ∏ p ∈ m.primeFactors, (sieveRootCard s p : ℝ)
      = (sieveRootCard s m : ℝ) := by
    rw [← Nat.cast_prod, ← sieveRootCard_squarefree s m hm]
  rw [hnum, hden]

/-- **Diagonalization of the Selberg quadratic form**: over the divisors of a
squarefree modulus, the quadratic form is a nonnegatively-weighted sum of
squares of the transformed weights. -/
theorem selberg_quadratic_diagonalize {P : ℕ} (hP : Squarefree P)
    (s : ℕ) (lam : ℕ → ℝ) :
    ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors, lam d₁ * lam d₂
        * ((sieveRootCard s (Nat.lcm d₁ d₂) : ℝ) / (Nat.lcm d₁ d₂))
      = ∑ k ∈ P.divisors,
          (∏ p ∈ k.primeFactors,
            (((p : ℝ) - sieveRootCard s p) / sieveRootCard s p))
          * (∑ d ∈ P.divisors.filter (fun d => k ∣ d),
              lam d * ((sieveRootCard s d : ℝ) / d)) ^ 2 := by
  classical
  have hP0 := hP.ne_zero
  -- the per-pair rewrite: main quotient = product of weights times a k-sum
  have hpair : ∀ d₁ ∈ P.divisors, ∀ d₂ ∈ P.divisors,
      lam d₁ * lam d₂
        * ((sieveRootCard s (Nat.lcm d₁ d₂) : ℝ) / (Nat.lcm d₁ d₂))
      = ∑ k ∈ P.divisors,
          (if k ∣ d₁ ∧ k ∣ d₂ then
            (∏ p ∈ k.primeFactors,
              (((p : ℝ) - sieveRootCard s p) / sieveRootCard s p))
            * ((lam d₁ * ((sieveRootCard s d₁ : ℝ) / d₁))
              * (lam d₂ * ((sieveRootCard s d₂ : ℝ) / d₂)))
          else 0) := by
    intro d₁ hd₁ d₂ hd₂
    have h₁0 : 0 < d₁ := Nat.pos_of_mem_divisors hd₁
    have h₂0 : 0 < d₂ := Nat.pos_of_mem_divisors hd₂
    have hsq₁ : Squarefree d₁ :=
      hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd₁)
    have hsq₂ : Squarefree d₂ :=
      hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd₂)
    have hG0 : 0 < Nat.gcd d₁ d₂ := Nat.gcd_pos_of_pos_left d₂ h₁0
    have hL0 : 0 < Nat.lcm d₁ d₂ :=
      Nat.pos_of_ne_zero (Nat.lcm_ne_zero h₁0.ne' h₂0.ne')
    have hsqG : Squarefree (Nat.gcd d₁ d₂) :=
      Squarefree.squarefree_of_dvd (Nat.gcd_dvd_left d₁ d₂) hsq₁
    have hρpos : ∀ m : ℕ, 0 < m → (0 : ℝ) < (sieveRootCard s m : ℝ) := by
      intro m hm
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one
        (one_le_sieveRootCard hm s)
    -- the gcd-divisor sum as a filtered sum over `P.divisors`
    have hgdvd : (Nat.gcd d₁ d₂).divisors
        = P.divisors.filter (fun k => k ∣ d₁ ∧ k ∣ d₂) := by
      ext k
      rw [Nat.mem_divisors, Finset.mem_filter, Nat.mem_divisors,
        Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨hk₁, hk₂⟩, -⟩
        exact ⟨⟨hk₁.trans (Nat.dvd_of_mem_divisors hd₁), hP0⟩, hk₁, hk₂⟩
      · rintro ⟨-, hk₁, hk₂⟩
        exact ⟨⟨hk₁, hk₂⟩, hG0.ne'⟩
    -- the analytic pair identity
    have hA : ((sieveRootCard s (Nat.lcm d₁ d₂) : ℝ) / (Nat.lcm d₁ d₂))
        = ((sieveRootCard s d₁ : ℝ) / d₁) * ((sieveRootCard s d₂ : ℝ) / d₂)
          * (((Nat.gcd d₁ d₂ : ℕ) : ℝ)
            / (sieveRootCard s (Nat.gcd d₁ d₂) : ℝ)) := by
      have hmR : (sieveRootCard s (Nat.lcm d₁ d₂) : ℝ)
          * (sieveRootCard s (Nat.gcd d₁ d₂) : ℝ)
          = (sieveRootCard s d₁ : ℝ) * (sieveRootCard s d₂ : ℝ) := by
        exact_mod_cast sieveRootCard_lcm_mul_gcd h₁0 h₂0 hsq₁ hsq₂ s
      have hlgR : ((Nat.gcd d₁ d₂ : ℕ) : ℝ) * ((Nat.lcm d₁ d₂ : ℕ) : ℝ)
          = (d₁ : ℝ) * (d₂ : ℝ) := by
        exact_mod_cast Nat.gcd_mul_lcm d₁ d₂
      have hLR : (0 : ℝ) < ((Nat.lcm d₁ d₂ : ℕ) : ℝ) := by exact_mod_cast hL0
      have hGR : (0 : ℝ) < ((Nat.gcd d₁ d₂ : ℕ) : ℝ) := by exact_mod_cast hG0
      have hd₁R : (0 : ℝ) < (d₁ : ℝ) := by exact_mod_cast h₁0
      have hd₂R : (0 : ℝ) < (d₂ : ℝ) := by exact_mod_cast h₂0
      have hρG := hρpos _ hG0
      have hLne : ((Nat.lcm d₁ d₂ : ℕ) : ℝ) ≠ 0 := hLR.ne'
      have hρGne : (sieveRootCard s (Nat.gcd d₁ d₂) : ℝ) ≠ 0 := hρG.ne'
      have hd₁ne : (d₁ : ℝ) ≠ 0 := hd₁R.ne'
      have hd₂ne : (d₂ : ℝ) ≠ 0 := hd₂R.ne'
      field_simp
      linear_combination ((d₁ : ℝ) * (d₂ : ℝ)) * hmR - ((sieveRootCard s d₁ : ℝ) * (sieveRootCard s d₂ : ℝ)) * hlgR
    rw [hA, ← sum_divisors_w_eq (s := s) hsqG, hgdvd, Finset.sum_filter,
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k ∣ d₁ ∧ k ∣ d₂
    · rw [if_pos hk, if_pos hk]
      ring
    · rw [if_neg hk, if_neg hk, mul_zero, mul_zero]
  rw [Finset.sum_congr rfl fun d₁ hd₁ =>
    Finset.sum_congr rfl fun d₂ hd₂ => hpair d₁ hd₁ d₂ hd₂]
  -- swap the k-sum outside
  rw [Finset.sum_congr rfl fun d₁ _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  -- factor the per-k double sum into the square
  have hsplit : ∀ d₁ d₂ : ℕ,
      (if k ∣ d₁ ∧ k ∣ d₂ then
        (∏ p ∈ k.primeFactors,
          (((p : ℝ) - sieveRootCard s p) / sieveRootCard s p))
        * ((lam d₁ * ((sieveRootCard s d₁ : ℝ) / d₁))
          * (lam d₂ * ((sieveRootCard s d₂ : ℝ) / d₂)))
      else 0)
      = (∏ p ∈ k.primeFactors,
          (((p : ℝ) - sieveRootCard s p) / sieveRootCard s p))
        * ((if k ∣ d₁ then lam d₁ * ((sieveRootCard s d₁ : ℝ) / d₁) else 0)
          * (if k ∣ d₂ then lam d₂ * ((sieveRootCard s d₂ : ℝ) / d₂) else 0)) := by
    intro d₁ d₂
    by_cases h₁ : k ∣ d₁
    · by_cases h₂ : k ∣ d₂
      · rw [if_pos ⟨h₁, h₂⟩, if_pos h₁, if_pos h₂]
      · rw [if_neg (fun hc => h₂ hc.2), if_neg h₂, mul_zero, mul_zero]
    · rw [if_neg (fun hc => h₁ hc.1), if_neg h₁, zero_mul, mul_zero]
  calc ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
      (if k ∣ d₁ ∧ k ∣ d₂ then
        (∏ p ∈ k.primeFactors,
          (((p : ℝ) - sieveRootCard s p) / sieveRootCard s p))
        * ((lam d₁ * ((sieveRootCard s d₁ : ℝ) / d₁))
          * (lam d₂ * ((sieveRootCard s d₂ : ℝ) / d₂)))
      else 0)
      = ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
          (∏ p ∈ k.primeFactors,
            (((p : ℝ) - sieveRootCard s p) / sieveRootCard s p))
          * ((if k ∣ d₁ then lam d₁ * ((sieveRootCard s d₁ : ℝ) / d₁) else 0)
            * (if k ∣ d₂ then lam d₂ * ((sieveRootCard s d₂ : ℝ) / d₂) else 0)) := by
        refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => ?_
        exact hsplit d₁ d₂
    _ = (∏ p ∈ k.primeFactors,
          (((p : ℝ) - sieveRootCard s p) / sieveRootCard s p))
        * (∑ d ∈ P.divisors.filter (fun d => k ∣ d),
            lam d * ((sieveRootCard s d : ℝ) / d)) ^ 2 := by
        rw [sq, Finset.sum_filter, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d₁ _ => ?_
        rw [Finset.mul_sum]

end MoltResearch
