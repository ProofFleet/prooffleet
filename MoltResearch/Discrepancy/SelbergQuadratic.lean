import MoltResearch.Discrepancy.SieveResidues

/-!
# Discrepancy: the Selberg quadratic form

Track S of the EDP-unconditional campaign (`Problems/tao2015_derivation_c.md`,
issue #3004): the Λ² step of the upper-bound sieve for the twin-type sift
`n ↦ n(s−n)`.

For any weights `λ` with `λ₁ = 1`, the count of `n ∈ (a, b]` free of sifting
primes (the prime factors of a squarefree modulus `P`) is at most

  `(b − a) · Q(λ) + (∑_{d ∣ P} |λ_d| ρ(d))²`,

where `Q(λ) = ∑_{d₁, d₂ ∣ P} λ_{d₁} λ_{d₂} ρ(lcm)/lcm` is the Selberg
quadratic form. En route: positivity and trivial bounds for the root count,
the lcm divisibility split, congruence to the lcm, and submultiplicativity
`ρ(lcm d₁ d₂) ≤ ρ(d₁)ρ(d₂)` by injecting roots into pairs of roots — no
coprimality needed. The diagonalization of `Q` is the next unit.
-/

namespace MoltResearch

open Finset

/-- `0` is always a root: the count is positive. -/
theorem one_le_sieveRootCard {d : ℕ} (hd : 0 < d) (s : ℕ) :
    1 ≤ sieveRootCard s d := by
  rw [sieveRootCard, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero,
    Finset.card_pos]
  refine ⟨0, ?_⟩
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨hd, ?_⟩
  simp only [Nat.cast_zero, zero_mul, dvd_zero]

/-- The trivial upper bound. -/
theorem sieveRootCard_le (s d : ℕ) : sieveRootCard s d ≤ d := by
  rw [sieveRootCard]
  calc ((Finset.range d).filter
      (fun x : ℕ => (d : ℤ) ∣ (x : ℤ) * ((s : ℤ) - (x : ℤ)))).card
      ≤ (Finset.range d).card := Finset.card_filter_le _ _
    _ = d := Finset.card_range d

/-- Integer divisibility by a `Nat.lcm` splits. -/
theorem natCast_lcm_dvd_iff {d₁ d₂ : ℕ} {w : ℤ} :
    ((Nat.lcm d₁ d₂ : ℕ) : ℤ) ∣ w ↔ (d₁ : ℤ) ∣ w ∧ (d₂ : ℤ) ∣ w := by
  rw [Int.natCast_dvd, Int.natCast_dvd, Int.natCast_dvd]
  exact ⟨fun h => ⟨(Nat.dvd_lcm_left _ _).trans h,
      (Nat.dvd_lcm_right _ _).trans h⟩,
    fun h => Nat.lcm_dvd h.1 h.2⟩

/-- Congruence mod both moduli gives congruence mod the lcm. -/
theorem modEq_lcm {d₁ d₂ x y : ℕ} (h₁ : x ≡ y [MOD d₁]) (h₂ : x ≡ y [MOD d₂]) :
    x ≡ y [MOD Nat.lcm d₁ d₂] := by
  rw [← Int.natCast_modEq_iff] at h₁ h₂ ⊢
  rw [Int.modEq_iff_dvd] at h₁ h₂ ⊢
  exact natCast_lcm_dvd_iff.mpr ⟨h₁, h₂⟩

/-- **Submultiplicativity at the lcm**: roots mod `lcm d₁ d₂` inject into
pairs of roots — no coprimality needed. -/
theorem sieveRootCard_lcm_le {d₁ d₂ : ℕ} (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    (s : ℕ) :
    sieveRootCard s (Nat.lcm d₁ d₂) ≤ sieveRootCard s d₁ * sieveRootCard s d₂ := by
  classical
  have hl : 0 < Nat.lcm d₁ d₂ := Nat.pos_of_ne_zero
    (Nat.lcm_ne_zero h₁.ne' h₂.ne')
  rw [sieveRootCard, sieveRootCard, sieveRootCard, ← Finset.card_product]
  have hcond : ∀ (d : ℕ) (x : ℕ), 0 < d → Nat.lcm d₁ d₂ % d = 0 →
      (((Nat.lcm d₁ d₂ : ℕ) : ℤ) ∣ (x : ℤ) * ((s : ℤ) - (x : ℤ))) →
      (d : ℤ) ∣ ((x % d : ℕ) : ℤ) * ((s : ℤ) - ((x % d : ℕ) : ℤ)) := by
    intro d x hd hdvd hroot
    have hddvd : (d : ℤ) ∣ ((Nat.lcm d₁ d₂ : ℕ) : ℤ) := by
      exact_mod_cast Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero hdvd)
    have h1 : (d : ℤ) ∣ (x : ℤ) * ((s : ℤ) - (x : ℤ)) := hddvd.trans hroot
    have hcong : ((x : ℤ)) ≡ ((x % d : ℕ) : ℤ) [ZMOD (d : ℤ)] :=
      Int.natCast_modEq_iff.mpr (Nat.mod_modEq x d).symm
    exact (sieve_dvd_congr hcong s).mp h1
  refine Finset.card_le_card_of_injOn (fun x => (x % d₁, x % d₂)) ?_ ?_
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_filter,
      Finset.mem_filter, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨Nat.mod_lt x h₁,
        hcond d₁ x h₁ (Nat.mod_eq_zero_of_dvd (Nat.dvd_lcm_left _ _)) hx.2⟩,
      ⟨Nat.mod_lt x h₂,
        hcond d₂ x h₂ (Nat.mod_eq_zero_of_dvd (Nat.dvd_lcm_right _ _)) hx.2⟩⟩
  · intro x hx y hy heq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hy
    have he1 : x % d₁ = y % d₁ := congrArg Prod.fst heq
    have he2 : x % d₂ = y % d₂ := congrArg Prod.snd heq
    have hmod : x ≡ y [MOD Nat.lcm d₁ d₂] := modEq_lcm he1 he2
    rw [Nat.ModEq, Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] at hmod
    exact hmod

/-- **The Λ² expansion**: for any weights with `λ₁ = 1` supported on the
divisors of the squarefree sifting modulus `P`, the sifted count is bounded by
the quadratic form plus the aggregated rounding error. -/
theorem card_sift_le_quadratic {P a b s : ℕ} (hP : Squarefree P)
    (hab : a ≤ b) (lam : ℕ → ℝ) (hlam1 : lam 1 = 1) :
    ((((Finset.Ioc a b).filter (fun n : ℕ =>
        ∀ p ∈ P.primeFactors, ¬ ((p : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ))))).card : ℝ))
      ≤ ((b : ℝ) - a) * (∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
          lam d₁ * lam d₂
            * ((sieveRootCard s (Nat.lcm d₁ d₂) : ℝ) / (Nat.lcm d₁ d₂)))
        + (∑ d ∈ P.divisors, |lam d| * (sieveRootCard s d : ℝ)) ^ 2 := by
  classical
  have hP0 : P ≠ 0 := hP.ne_zero
  -- Step 1: on the sifted set, the divisor-restricted weight sum is exactly 1
  have hpoint : ∀ n ∈ (Finset.Ioc a b).filter (fun n : ℕ =>
      ∀ p ∈ P.primeFactors, ¬ ((p : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ)))),
      (∑ d ∈ P.divisors,
        if (d : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ)) then lam d else 0) = 1 := by
    intro n hn
    rw [Finset.mem_filter] at hn
    have honly : ∀ d ∈ P.divisors, d ≠ 1 →
        ¬ ((d : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ))) := by
      intro d hd hd1 hc
      have hddvd := Nat.dvd_of_mem_divisors hd
      have hpprime := Nat.minFac_prime hd1
      have hpP : d.minFac ∈ P.primeFactors := by
        rw [Nat.mem_primeFactors]
        exact ⟨hpprime, (d.minFac_dvd).trans hddvd, hP0⟩
      refine hn.2 d.minFac hpP ?_
      exact (Int.natCast_dvd_natCast.mpr d.minFac_dvd).trans hc
    have hone : (1 : ℕ) ∈ P.divisors := Nat.one_mem_divisors.mpr hP0
    rw [Finset.sum_eq_single 1]
    · rw [if_pos (by exact_mod_cast one_dvd ((n : ℤ) * ((s : ℤ) - (n : ℤ)))),
        hlam1]
    · intro d hd hd1
      rw [if_neg (honly d hd hd1)]
    · intro hno
      exact absurd hone hno
  -- Step 2: dominate by the quadratic sum over the whole window
  have hstep2 : ((((Finset.Ioc a b).filter (fun n : ℕ =>
      ∀ p ∈ P.primeFactors, ¬ ((p : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ))))).card : ℝ))
      ≤ ∑ n ∈ Finset.Ioc a b,
          (∑ d ∈ P.divisors,
            if (d : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ)) then lam d else 0) ^ 2 := by
    rw [Finset.card_eq_sum_ones]
    push_cast
    calc ∑ n ∈ (Finset.Ioc a b).filter (fun n : ℕ =>
        ∀ p ∈ P.primeFactors, ¬ ((p : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ)))),
        (1 : ℝ)
        = ∑ n ∈ (Finset.Ioc a b).filter (fun n : ℕ =>
            ∀ p ∈ P.primeFactors, ¬ ((p : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ)))),
          (∑ d ∈ P.divisors,
            if (d : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ)) then lam d else 0) ^ 2 := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [hpoint n hn, one_pow]
      _ ≤ ∑ n ∈ Finset.Ioc a b,
          (∑ d ∈ P.divisors,
            if (d : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ)) then lam d else 0) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun n _ _ => sq_nonneg _)
  -- Step 3: expand the square into lcm-conditioned pair terms
  have hexpand : ∀ n : ℕ,
      (∑ d ∈ P.divisors,
        if (d : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ)) then lam d else 0) ^ 2
      = ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
          (if ((Nat.lcm d₁ d₂ : ℕ) : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ))
            then lam d₁ * lam d₂ else 0) := by
    intro n
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => ?_
    by_cases h₁ : (d₁ : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ))
    · by_cases h₂ : (d₂ : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ))
      · rw [if_pos h₁, if_pos h₂, if_pos (natCast_lcm_dvd_iff.mpr ⟨h₁, h₂⟩)]
      · rw [if_pos h₁, if_neg h₂, mul_zero,
          if_neg (fun hc => h₂ (natCast_lcm_dvd_iff.mp hc).2)]
    · rw [if_neg h₁, zero_mul,
        if_neg (fun hc => h₁ (natCast_lcm_dvd_iff.mp hc).1)]
  -- Step 4: swap the sums; the inner sum is a sifted count at the lcm
  have hswap : ∑ n ∈ Finset.Ioc a b,
      (∑ d ∈ P.divisors,
        if (d : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ)) then lam d else 0) ^ 2
      = ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors, lam d₁ * lam d₂
          * ((((Finset.Ioc a b).filter (fun n : ℕ =>
              ((Nat.lcm d₁ d₂ : ℕ) : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ)))).card : ℝ)) := by
    rw [Finset.sum_congr rfl fun n _ => hexpand n, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d₂ _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- Step 5: per-pair, split into the main term and the bounded error
  have hper : ∀ d₁ ∈ P.divisors, ∀ d₂ ∈ P.divisors,
      lam d₁ * lam d₂
        * ((((Finset.Ioc a b).filter (fun n : ℕ =>
            ((Nat.lcm d₁ d₂ : ℕ) : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ)))).card : ℝ))
      ≤ lam d₁ * lam d₂ * ((sieveRootCard s (Nat.lcm d₁ d₂) : ℝ)
          * (((b : ℝ) - a) / (Nat.lcm d₁ d₂)))
        + |lam d₁| * (sieveRootCard s d₁ : ℝ)
          * (|lam d₂| * (sieveRootCard s d₂ : ℝ)) := by
    intro d₁ hd₁ d₂ hd₂
    have hd₁0 : 0 < d₁ := Nat.pos_of_mem_divisors hd₁
    have hd₂0 : 0 < d₂ := Nat.pos_of_mem_divisors hd₂
    have hl0 : 0 < Nat.lcm d₁ d₂ :=
      Nat.pos_of_ne_zero (Nat.lcm_ne_zero hd₁0.ne' hd₂0.ne')
    have hX := abs_card_sift_sub_le hl0 hab s
    have hlcm : ((sieveRootCard s (Nat.lcm d₁ d₂) : ℕ) : ℝ)
        ≤ ((sieveRootCard s d₁ : ℕ) : ℝ) * ((sieveRootCard s d₂ : ℕ) : ℝ) := by
      exact_mod_cast sieveRootCard_lcm_le hd₁0 hd₂0 s
    set cnt : ℝ := (((Finset.Ioc a b).filter (fun n : ℕ =>
        ((Nat.lcm d₁ d₂ : ℕ) : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ)))).card : ℝ)
      with hcnt_def
    set mn : ℝ := (sieveRootCard s (Nat.lcm d₁ d₂) : ℝ)
        * (((b : ℝ) - a) / (Nat.lcm d₁ d₂)) with hmn_def
    have h2 : lam d₁ * lam d₂ * cnt - lam d₁ * lam d₂ * mn
        = lam d₁ * lam d₂ * (cnt - mn) := by ring
    have h3 : lam d₁ * lam d₂ * (cnt - mn)
        ≤ |lam d₁ * lam d₂ * (cnt - mn)| := le_abs_self _
    have h4 : |lam d₁ * lam d₂ * (cnt - mn)|
        = |lam d₁| * |lam d₂| * |cnt - mn| := by
      rw [abs_mul, abs_mul]
    have h5 : |lam d₁| * |lam d₂| * |cnt - mn|
        ≤ |lam d₁| * |lam d₂| * (sieveRootCard s (Nat.lcm d₁ d₂) : ℝ) :=
      mul_le_mul_of_nonneg_left hX (by positivity)
    have h6 : |lam d₁| * |lam d₂| * (sieveRootCard s (Nat.lcm d₁ d₂) : ℝ)
        ≤ |lam d₁| * |lam d₂|
          * ((sieveRootCard s d₁ : ℝ) * (sieveRootCard s d₂ : ℝ)) :=
      mul_le_mul_of_nonneg_left hlcm (by positivity)
    have h7 : |lam d₁| * |lam d₂|
        * ((sieveRootCard s d₁ : ℝ) * (sieveRootCard s d₂ : ℝ))
        = |lam d₁| * (sieveRootCard s d₁ : ℝ)
          * (|lam d₂| * (sieveRootCard s d₂ : ℝ)) := by ring
    linarith only [h2.le, h2.ge, h3, h4.le, h4.ge, h5, h6, h7.le, h7.ge]
  -- assemble
  have hmain_eq : ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
      lam d₁ * lam d₂ * ((sieveRootCard s (Nat.lcm d₁ d₂) : ℝ)
        * (((b : ℝ) - a) / (Nat.lcm d₁ d₂)))
      = ((b : ℝ) - a) * (∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
          lam d₁ * lam d₂
            * ((sieveRootCard s (Nat.lcm d₁ d₂) : ℝ) / (Nat.lcm d₁ d₂))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d₂ _ => ?_
    ring
  have herr_eq : ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
      |lam d₁| * (sieveRootCard s d₁ : ℝ)
        * (|lam d₂| * (sieveRootCard s d₂ : ℝ))
      = (∑ d ∈ P.divisors, |lam d| * (sieveRootCard s d : ℝ)) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  calc ((((Finset.Ioc a b).filter (fun n : ℕ =>
      ∀ p ∈ P.primeFactors, ¬ ((p : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ))))).card : ℝ))
      ≤ ∑ n ∈ Finset.Ioc a b,
          (∑ d ∈ P.divisors,
            if (d : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ)) then lam d else 0) ^ 2 :=
        hstep2
    _ = ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors, lam d₁ * lam d₂
          * ((((Finset.Ioc a b).filter (fun n : ℕ =>
              ((Nat.lcm d₁ d₂ : ℕ) : ℤ) ∣ (n : ℤ) * ((s : ℤ) - (n : ℤ)))).card : ℝ)) :=
        hswap
    _ ≤ ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
          (lam d₁ * lam d₂ * ((sieveRootCard s (Nat.lcm d₁ d₂) : ℝ)
              * (((b : ℝ) - a) / (Nat.lcm d₁ d₂)))
            + |lam d₁| * (sieveRootCard s d₁ : ℝ)
              * (|lam d₂| * (sieveRootCard s d₂ : ℝ))) := by
        refine Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ => ?_
        exact hper d₁ hd₁ d₂ hd₂
    _ = (∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
          lam d₁ * lam d₂ * ((sieveRootCard s (Nat.lcm d₁ d₂) : ℝ)
            * (((b : ℝ) - a) / (Nat.lcm d₁ d₂))))
        + ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
            |lam d₁| * (sieveRootCard s d₁ : ℝ)
              * (|lam d₂| * (sieveRootCard s d₂ : ℝ)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun d₁ _ => ?_
        rw [← Finset.sum_add_distrib]
    _ = ((b : ℝ) - a) * (∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
          lam d₁ * lam d₂
            * ((sieveRootCard s (Nat.lcm d₁ d₂) : ℝ) / (Nat.lcm d₁ d₂)))
        + (∑ d ∈ P.divisors, |lam d| * (sieveRootCard s d : ℝ)) ^ 2 := by
        rw [hmain_eq, herr_eq]

end MoltResearch
