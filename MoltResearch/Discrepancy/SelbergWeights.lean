import MoltResearch.Discrepancy.SelbergDiagonal
import Mathlib.Algebra.BigOperators.Field

/-!
# Discrepancy: the truncated Selberg weights

Track S of the EDP-unconditional campaign (`Problems/tao2015_derivation_c.md`,
issue #3004): the explicit weights that optimize the Selberg quadratic form.

Over a squarefree sifting modulus `P` with truncation level `R`, the weights
`selbergLambda s P R` are defined by Möbius inversion from the optimal
diagonal values `y_k = μ(k) h(k)/G(R)`, where `h(k) = ∏_{p∣k} ρ/(p−ρ)` and
`G(R) = ∑_{k ∣ P, k ≤ R} h(k)`. The unit proves the three facts the sieve
consumes:

- `selbergLambda_one` — the normalization `λ₁ = 1`;
- `abs_selbergLambda_le` — the crude bound `|λ_d| ≤ 3^ω(d)` (with
  `selbergLambda_eq_zero_of_gt` for support in `d ≤ R`), which controls the
  Λ² error term after shrinking the sift level;
- `quadratic_selbergLambda_eq` — the optimal value `Q(λ) = 1/G(R)`.

The engine is the real Möbius layer over the squarefree divisor dictionary:
`μℝ = (−1)^ω`, the divisor-sum evaluation `∑_{e∣m} μℝ(e) = [m = 1]`, and the
interval evaluation `∑_{k∣d∣k'} μℝ(k'/d) = [k = k']`.
-/

namespace MoltResearch

open Finset

/-- The real Möbius weight of a squarefree modulus: `(−1)^ω`. -/
noncomputable def muR (d : ℕ) : ℝ := (-1 : ℝ) ^ d.primeFactors.card

theorem muR_one : muR 1 = 1 := by
  rw [muR, Nat.primeFactors_one, Finset.card_empty, pow_zero]

theorem muR_sq (d : ℕ) : muR d * muR d = 1 := by
  rw [muR, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

theorem muR_mul_coprime {d m : ℕ} (hcop : Nat.Coprime d m) :
    muR (d * m) = muR d * muR m := by
  rw [muR, muR, muR, Nat.Coprime.primeFactors_mul hcop,
    Finset.card_union_of_disjoint (Nat.Coprime.disjoint_primeFactors hcop),
    pow_add]

/-- **The Möbius divisor sum** over a squarefree modulus: `[m = 1]`. -/
theorem sum_divisors_muR {m : ℕ} (hm : Squarefree m) :
    ∑ e ∈ m.divisors, muR e = if m = 1 then 1 else 0 := by
  classical
  rw [sum_divisors_squarefree_eq_powerset hm]
  have hcong : ∀ T ∈ m.primeFactors.powerset,
      muR (∏ p ∈ T, p) = (-1 : ℝ) ^ T.card := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    rw [muR, Nat.primeFactors_prod
      (fun p hp => Nat.prime_of_mem_primeFactors (hT hp))]
  rw [Finset.sum_congr rfl hcong]
  have hZ := Finset.sum_powerset_neg_one_pow_card (x := m.primeFactors)
  have hR : ∑ T ∈ m.primeFactors.powerset, (-1 : ℝ) ^ T.card
      = (((∑ T ∈ m.primeFactors.powerset, (-1 : ℤ) ^ T.card) : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [hR, hZ]
  by_cases h1 : m.primeFactors = ∅
  · rw [if_pos h1]
    have hm1 : m = 1 := by
      rcases Nat.primeFactors_eq_empty.mp h1 with h | h
      · exact absurd h hm.ne_zero
      · exact h
    rw [if_pos hm1]
    norm_num
  · rw [if_neg h1]
    have hm1 : m ≠ 1 := fun hc => h1 (by rw [hc]; exact Nat.primeFactors_one)
    rw [if_neg hm1]
    norm_num

/-- Reindexing a divisor interval `[k, k']` by the quotient. -/
theorem sum_interval_divisors {k k' : ℕ} (hk' : k' ≠ 0) (hkk' : k ∣ k')
    (f : ℕ → ℝ) :
    ∑ d ∈ k'.divisors.filter (fun d => k ∣ d), f d
      = ∑ e ∈ (k' / k).divisors, f (k * e) := by
  classical
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hk' (zero_dvd_iff.mp hkk')
  refine Finset.sum_nbij' (fun d => d / k) (fun e => k * e) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨⟨c, hc⟩, -⟩, hkd⟩ := hd
    obtain ⟨e, he⟩ := hkd
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    rw [Nat.mem_divisors]
    beta_reduce
    constructor
    · refine ⟨c, ?_⟩
      rw [hc, he, mul_assoc, Nat.mul_div_cancel_left (e * c) hkpos,
        Nat.mul_div_cancel_left e hkpos]
    · have hkle : k ≤ k' := Nat.le_of_dvd (Nat.pos_of_ne_zero hk') hkk'
      exact (Nat.div_pos hkle hkpos).ne'
  · intro e he
    rw [Nat.mem_divisors] at he
    rw [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, hk'⟩, Dvd.intro e rfl⟩
    calc k * e ∣ k * (k' / k) := mul_dvd_mul_left k he.1
      _ = k' := Nat.mul_div_cancel' hkk'
  · intro d hd
    rw [Finset.mem_filter] at hd
    exact Nat.mul_div_cancel' hd.2
  · intro e _
    exact Nat.mul_div_cancel_left e (Nat.pos_of_ne_zero hk0)
  · intro d hd
    rw [Finset.mem_filter] at hd
    rw [Nat.mul_div_cancel' hd.2]

/-- **The interval Möbius evaluation**: over a squarefree `k'`, summing
`μ(k'/d)` over the divisor interval `k ∣ d ∣ k'` detects `k = k'`. -/
theorem sum_interval_muR {k k' : ℕ} (hk' : Squarefree k') (hkk' : k ∣ k') :
    ∑ d ∈ k'.divisors.filter (fun d => k ∣ d), muR (k' / d)
      = if k = k' then 1 else 0 := by
  classical
  rw [sum_interval_divisors hk'.ne_zero hkk']
  have hcong : ∀ e ∈ (k' / k).divisors, muR (k' / (k * e))
      = muR ((k' / k) / e) := by
    intro e _
    rw [Nat.div_div_eq_div_mul]
  rw [Finset.sum_congr rfl hcong, Nat.sum_div_divisors (k' / k) muR,
    sum_divisors_muR (hk'.squarefree_of_dvd (Nat.div_dvd_of_dvd hkk'))]
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hk'.ne_zero (zero_dvd_iff.mp hkk')
  by_cases heq : k = k'
  · rw [if_pos (by rw [heq, Nat.div_self (Nat.pos_of_ne_zero hk'.ne_zero)]),
      if_pos heq]
  · rw [if_neg ?_, if_neg heq]
    intro hc
    have h1 : k * (k' / k) = k' := Nat.mul_div_cancel' hkk'
    rw [hc, mul_one] at h1
    exact heq h1

-- ===== S5b: the truncated Selberg weights =====

/-- The truncated `G`-sum: `G(R) = ∑_{k ∣ P, k ≤ R} h(k)`,
`h(k) = ∏_{p∣k} ρ/(p−ρ)`. -/
noncomputable def selbergG (s P R : ℕ) : ℝ :=
  ∑ k ∈ P.divisors.filter (fun k => k ≤ R),
    ∏ p ∈ k.primeFactors,
      ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p))

/-- The truncated Selberg weights, by explicit Möbius inversion from the
optimal diagonal values `y_k = μ(k) h(k)/G`. -/
noncomputable def selbergLambda (s P R : ℕ) (d : ℕ) : ℝ :=
  ((d : ℝ) / (sieveRootCard s d : ℝ))
    * ∑ k ∈ (P.divisors.filter (fun k => k ≤ R)).filter (fun k => d ∣ k),
        muR (k / d) * (muR k
          * (∏ p ∈ k.primeFactors,
              ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
          / selbergG s P R)

/-- `h` is positive at every squarefree divisor when `ρ(p) < p`. -/
theorem selberg_h_pos {s P : ℕ} (hP : Squarefree P)
    (hρlt : ∀ p ∈ P.primeFactors, sieveRootCard s p < p) :
    ∀ k ∈ P.divisors, (0 : ℝ)
      < ∏ p ∈ k.primeFactors,
          ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)) := by
  intro k hk
  refine Finset.prod_pos fun p hp => ?_
  have hpP : p ∈ P.primeFactors :=
    Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hk) hP.ne_zero hp
  have hpp := Nat.prime_of_mem_primeFactors hpP
  have hρ1 : (0 : ℝ) < (sieveRootCard s p : ℝ) := by
    have h1 : 1 ≤ sieveRootCard s p := one_le_sieveRootCard hpp.pos s
    have h2 : 0 < sieveRootCard s p := Nat.lt_of_lt_of_le Nat.zero_lt_one h1
    exact_mod_cast h2
  have hlt : (sieveRootCard s p : ℝ) < (p : ℝ) := by
    exact_mod_cast hρlt p hpP
  exact div_pos hρ1 (by linarith)

/-- `G(R) ≥ 1`: the `k = 1` term alone contributes the empty product. -/
theorem one_le_selbergG {s P R : ℕ} (hP : Squarefree P) (hR : 1 ≤ R)
    (hρlt : ∀ p ∈ P.primeFactors, sieveRootCard s p < p) :
    (1 : ℝ) ≤ selbergG s P R := by
  classical
  rw [selbergG]
  have h1mem : (1 : ℕ) ∈ P.divisors.filter (fun k => k ≤ R) := by
    rw [Finset.mem_filter]
    exact ⟨Nat.one_mem_divisors.mpr hP.ne_zero, hR⟩
  have hterm : ∏ p ∈ (1 : ℕ).primeFactors,
      ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)) = 1 := by
    rw [Nat.primeFactors_one, Finset.prod_empty]
  calc (1 : ℝ) = ∏ p ∈ (1 : ℕ).primeFactors,
      ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)) := hterm.symm
    _ ≤ ∑ k ∈ P.divisors.filter (fun k => k ≤ R),
        ∏ p ∈ k.primeFactors,
          ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)) := by
        refine Finset.single_le_sum (f := fun k => ∏ p ∈ k.primeFactors,
          ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
          (fun k hk => ?_) h1mem
        exact (selberg_h_pos hP hρlt k
          (Finset.mem_filter.mp hk).1).le

/-- The weights vanish beyond the truncation. -/
theorem selbergLambda_eq_zero_of_gt {s P R d : ℕ} (hd : R < d) :
    selbergLambda s P R d = 0 := by
  classical
  rw [selbergLambda]
  have hempty : (P.divisors.filter (fun k => k ≤ R)).filter
      (fun k => d ∣ k) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro k hk
    rw [Finset.mem_filter] at hk
    intro hdvd
    have hk0 : 0 < k := Nat.pos_of_mem_divisors hk.1
    have := Nat.le_of_dvd hk0 hdvd
    omega
  rw [hempty, Finset.sum_empty, mul_zero]

/-- **The normalization**: the Selberg weight at 1 is 1. -/
theorem selbergLambda_one {s P R : ℕ} (hP : Squarefree P) (hR : 1 ≤ R)
    (hρlt : ∀ p ∈ P.primeFactors, sieveRootCard s p < p) :
    selbergLambda s P R 1 = 1 := by
  classical
  have hG1 := one_le_selbergG (s := s) (R := R) hP hR hρlt
  have hG0 : selbergG s P R ≠ 0 := by linarith
  rw [selbergLambda, sieveRootCard_one,
    Finset.filter_true_of_mem (fun k _ => one_dvd k)]
  have hcong : ∀ k ∈ P.divisors.filter (fun k => k ≤ R),
      muR (k / 1) * (muR k * (∏ p ∈ k.primeFactors,
          ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
        / selbergG s P R)
      = (∏ p ∈ k.primeFactors,
          ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
        / selbergG s P R := by
    intro k _
    rw [Nat.div_one, ← mul_div_assoc, ← mul_assoc, muR_sq k, one_mul]
  rw [Finset.sum_congr rfl hcong, ← Finset.sum_div, ← selbergG,
    div_self hG0]
  norm_num

/-- The Möbius weight has unit absolute value. -/
theorem abs_muR (d : ℕ) : |muR d| = 1 := by
  rw [muR, abs_pow, abs_neg, abs_one, one_pow]

/-- `h` is multiplicative across coprime moduli. -/
theorem selberg_h_mul_coprime {s d m : ℕ} (hcop : Nat.Coprime d m) :
    ∏ p ∈ (d * m).primeFactors,
        ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p))
      = (∏ p ∈ d.primeFactors,
          ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
        * ∏ p ∈ m.primeFactors,
            ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)) := by
  rw [Nat.Coprime.primeFactors_mul hcop,
    Finset.prod_union (Nat.Coprime.disjoint_primeFactors hcop)]

/-- A divisor of a squarefree number is coprime to the complementary factor. -/
theorem coprime_div_of_squarefree {d k : ℕ} (hk : Squarefree k)
    (hdk : d ∣ k) : Nat.Coprime d (k / d) := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hk.ne_zero (zero_dvd_iff.mp hdk)
  by_contra hnc
  set g := Nat.gcd d (k / d) with hg_def
  have hg1 : g ≠ 1 := hnc
  have hgg : g * g ∣ k := by
    have h1 : g ∣ d := Nat.gcd_dvd_left _ _
    have h2 : g ∣ (k / d) := Nat.gcd_dvd_right _ _
    have h3 : g * g ∣ d * (k / d) := mul_dvd_mul h1 h2
    rwa [Nat.mul_div_cancel' hdk] at h3
  have := hk g hgg
  rw [Nat.isUnit_iff] at this
  exact hg1 this

/-- **The crude weight bound**: `|λ_d| ≤ 3^ω(d)` on the divisors of `P`. -/
theorem abs_selbergLambda_le {s P R : ℕ} (hP : Squarefree P)
    (hρlt : ∀ p ∈ P.primeFactors, sieveRootCard s p < p)
    {d : ℕ} (hd : d ∈ P.divisors) :
    |selbergLambda s P R d| ≤ 3 ^ d.primeFactors.card := by
  classical
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hsqd : Squarefree d :=
    hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
  rcases Nat.eq_zero_or_pos R with hR0 | hR1
  · subst hR0
    rw [selbergLambda_eq_zero_of_gt hd0, abs_zero]
    positivity
  have hG1 : (1 : ℝ) ≤ selbergG s P R := one_le_selbergG hP hR1 hρlt
  have hG0 : (0 : ℝ) < selbergG s P R := by linarith
  have hρd1 : 1 ≤ sieveRootCard s d := one_le_sieveRootCard hd0 s
  have hρdR : (0 : ℝ) < (sieveRootCard s d : ℝ) := by
    have h2 : 0 < sieveRootCard s d := Nat.lt_of_lt_of_le Nat.zero_lt_one hρd1
    exact_mod_cast h2
  have hdRpos : (0 : ℝ) ≤ (d : ℝ) / (sieveRootCard s d : ℝ) := by positivity
  rw [selbergLambda, abs_mul, abs_of_nonneg hdRpos]
  -- the h-values are nonnegative on the truncated divisor set
  have hmem : ∀ k ∈ (P.divisors.filter (fun k => k ≤ R)).filter
      (fun k => d ∣ k), k ∈ P.divisors := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_filter] at hk
    exact hk.1.1
  have hh0 : ∀ k ∈ (P.divisors.filter (fun k => k ≤ R)).filter
      (fun k => d ∣ k), (0 : ℝ)
      ≤ ∏ p ∈ k.primeFactors,
          ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)) := by
    intro k hk
    exact (selberg_h_pos hP hρlt k (hmem k hk)).le
  -- bound the absolute sum by the h-mass
  have habs : |∑ k ∈ (P.divisors.filter (fun k => k ≤ R)).filter
      (fun k => d ∣ k),
        muR (k / d) * (muR k * (∏ p ∈ k.primeFactors,
            ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
          / selbergG s P R)|
      ≤ (∑ k ∈ (P.divisors.filter (fun k => k ≤ R)).filter
          (fun k => d ∣ k),
          ∏ p ∈ k.primeFactors,
            ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
        / selbergG s P R := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [abs_mul, abs_muR, one_mul, abs_div, abs_mul, abs_muR, one_mul,
      abs_of_nonneg (hh0 k hk), abs_of_nonneg hG0.le]
  refine le_trans (mul_le_mul_of_nonneg_left habs hdRpos) ?_
  -- split `h(k) = h(d)·h(k/d)` and dominate the quotient mass by `G`
  have hsplit : ∀ k ∈ (P.divisors.filter (fun k => k ≤ R)).filter
      (fun k => d ∣ k),
      ∏ p ∈ k.primeFactors,
          ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p))
      = (∏ p ∈ d.primeFactors,
          ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
        * ∏ p ∈ (k / d).primeFactors,
            ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    have hdvd := hk.2
    have hsqk : Squarefree k :=
      hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors (hmem k (by
        rw [Finset.mem_filter]; exact hk)))
    conv_lhs => rw [← Nat.mul_div_cancel' hdvd]
    exact selberg_h_mul_coprime (coprime_div_of_squarefree hsqk hdvd)
  have himg : ∑ k ∈ (P.divisors.filter (fun k => k ≤ R)).filter
      (fun k => d ∣ k),
      ∏ p ∈ (k / d).primeFactors,
        ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p))
      ≤ selbergG s P R := by
    rw [← Finset.sum_image (f := fun m : ℕ => ∏ p ∈ m.primeFactors,
        ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
      (g := fun k => k / d) ?_]
    · rw [selbergG]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro m hm
        rw [Finset.mem_image] at hm
        obtain ⟨k, hk, hkm⟩ := hm
        rw [Finset.mem_filter, Finset.mem_filter, Nat.mem_divisors] at hk
        rw [Finset.mem_filter, Nat.mem_divisors]
        have hkd_dvd_k : k / d ∣ k := ⟨d, (Nat.div_mul_cancel hk.2).symm⟩
        subst hkm
        exact ⟨⟨hkd_dvd_k.trans hk.1.1.1, hP.ne_zero⟩,
          le_trans (Nat.div_le_self k d) hk.1.2⟩
      · intro m hm _
        rw [Finset.mem_filter] at hm
        exact (selberg_h_pos hP hρlt m hm.1).le
    · intro k hk k' hk' heq
      rw [Finset.mem_coe, Finset.mem_filter] at hk hk'
      have heq' : k / d = k' / d := heq
      have h1 : d * (k / d) = k := Nat.mul_div_cancel' hk.2
      have h2 : d * (k' / d) = k' := Nat.mul_div_cancel' hk'.2
      rw [← h1, ← h2, heq']
  -- assemble
  have hcomb : (∑ k ∈ (P.divisors.filter (fun k => k ≤ R)).filter
      (fun k => d ∣ k),
      ∏ p ∈ k.primeFactors,
        ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
      ≤ (∏ p ∈ d.primeFactors,
          ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
        * selbergG s P R := by
    rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left himg
      (selberg_h_pos hP hρlt d hd).le
  have hstep : (d : ℝ) / (sieveRootCard s d : ℝ)
      * ((∑ k ∈ (P.divisors.filter (fun k => k ≤ R)).filter
          (fun k => d ∣ k),
          ∏ p ∈ k.primeFactors,
            ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
        / selbergG s P R)
      ≤ (d : ℝ) / (sieveRootCard s d : ℝ)
        * ∏ p ∈ d.primeFactors,
            ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)) := by
    refine mul_le_mul_of_nonneg_left ?_ hdRpos
    rw [div_le_iff₀ hG0]
    calc (∑ k ∈ (P.divisors.filter (fun k => k ≤ R)).filter
        (fun k => d ∣ k),
        ∏ p ∈ k.primeFactors,
          ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
        ≤ (∏ p ∈ d.primeFactors,
            ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
          * selbergG s P R := hcomb
      _ = (∏ p ∈ d.primeFactors,
            ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
          * selbergG s P R := rfl
  refine le_trans hstep ?_
  -- the closed form `(d/ρ_d)·h(d) = ∏ p/(p−ρ)` and the per-prime bound
  have hd_eq : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsqd]
  have hρd_eq : (sieveRootCard s d : ℝ)
      = ∏ p ∈ d.primeFactors, (sieveRootCard s p : ℝ) := by
    rw [← Nat.cast_prod, ← sieveRootCard_squarefree s d hsqd]
  have hfinal : (d : ℝ) / (sieveRootCard s d : ℝ)
      * ∏ p ∈ d.primeFactors,
          ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p))
      = ∏ p ∈ d.primeFactors, ((p : ℝ) / ((p : ℝ) - sieveRootCard s p)) := by
    rw [hd_eq, hρd_eq, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpP : p ∈ P.primeFactors :=
      Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hP.ne_zero hp
    have hpp := Nat.prime_of_mem_primeFactors hpP
    have hρp1 : 1 ≤ sieveRootCard s p := one_le_sieveRootCard hpp.pos s
    have hρpR : (0 : ℝ) < (sieveRootCard s p : ℝ) := by
      have h2 : 0 < sieveRootCard s p :=
        Nat.lt_of_lt_of_le Nat.zero_lt_one hρp1
      exact_mod_cast h2
    field_simp
  rw [hfinal]
  have hper3 : ∀ p ∈ d.primeFactors,
      (p : ℝ) / ((p : ℝ) - sieveRootCard s p) ≤ 3 := by
    intro p hp
    have hpP : p ∈ P.primeFactors :=
      Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hP.ne_zero hp
    have hpp := Nat.prime_of_mem_primeFactors hpP
    have hρp1 : 1 ≤ sieveRootCard s p := one_le_sieveRootCard hpp.pos s
    have hρp2 : sieveRootCard s p ≤ 2 := by
      rw [sieveRootCard_prime hpp]
      split_ifs <;> norm_num
    have hρplt : sieveRootCard s p < p := hρlt p hpP
    have hρp2R : (sieveRootCard s p : ℝ) ≤ 2 := by exact_mod_cast hρp2
    have hρpltR : (sieveRootCard s p : ℝ) + 1 ≤ (p : ℝ) := by
      exact_mod_cast hρplt
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) - sieveRootCard s p)]
    linarith
  calc ∏ p ∈ d.primeFactors, ((p : ℝ) / ((p : ℝ) - sieveRootCard s p))
      ≤ ∏ _p ∈ d.primeFactors, (3 : ℝ) := by
        refine Finset.prod_le_prod (fun p hp => ?_) hper3
        have hpP : p ∈ P.primeFactors :=
          Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hP.ne_zero hp
        have hpp := Nat.prime_of_mem_primeFactors hpP
        have hρp1 : 1 ≤ sieveRootCard s p := one_le_sieveRootCard hpp.pos s
        have hρpR : (0 : ℝ) < (sieveRootCard s p : ℝ) := by
          have h2 : 0 < sieveRootCard s p :=
            Nat.lt_of_lt_of_le Nat.zero_lt_one hρp1
          exact_mod_cast h2
        have hρplt : (sieveRootCard s p : ℝ) < (p : ℝ) := by
          exact_mod_cast hρlt p hpP
        exact div_nonneg (Nat.cast_nonneg p) (by linarith)
    _ = 3 ^ d.primeFactors.card := by
        rw [Finset.prod_const]
    _ ≤ 3 ^ d.primeFactors.card := le_rfl

/-- `w · h = 1` on the divisors of `P`: the diagonal weights invert `h`. -/
theorem selberg_w_mul_h {s P : ℕ} (hP : Squarefree P)
    (hρlt : ∀ p ∈ P.primeFactors, sieveRootCard s p < p) :
    ∀ k ∈ P.divisors,
      (∏ p ∈ k.primeFactors,
        (((p : ℝ) - sieveRootCard s p) / sieveRootCard s p))
      * (∏ p ∈ k.primeFactors,
          ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p))) = 1 := by
  intro k hk
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun p hp => ?_
  have hpP : p ∈ P.primeFactors :=
    Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hk) hP.ne_zero hp
  have hpp := Nat.prime_of_mem_primeFactors hpP
  have hρp1 : 1 ≤ sieveRootCard s p := one_le_sieveRootCard hpp.pos s
  have hρpR : (0 : ℝ) < (sieveRootCard s p : ℝ) := by
    have h2 : 0 < sieveRootCard s p :=
      Nat.lt_of_lt_of_le Nat.zero_lt_one hρp1
    exact_mod_cast h2
  have hlt : (sieveRootCard s p : ℝ) < (p : ℝ) := by
    exact_mod_cast hρlt p hpP
  have hne : (p : ℝ) - sieveRootCard s p ≠ 0 := by linarith
  rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hρpR.ne' hne)]
  ring

/-- **The optimal value**: the Selberg weights realize `Q(λ) = 1/G(R)`. -/
theorem quadratic_selbergLambda_eq {s P R : ℕ} (hP : Squarefree P)
    (hR : 1 ≤ R)
    (hρlt : ∀ p ∈ P.primeFactors, sieveRootCard s p < p) :
    ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
        selbergLambda s P R d₁ * selbergLambda s P R d₂
        * ((sieveRootCard s (Nat.lcm d₁ d₂) : ℝ) / (Nat.lcm d₁ d₂))
      = 1 / selbergG s P R := by
  classical
  have hG1 : (1 : ℝ) ≤ selbergG s P R := one_le_selbergG hP hR hρlt
  have hG0 : (0 : ℝ) < selbergG s P R := by linarith
  rw [selberg_quadratic_diagonalize hP s (selbergLambda s P R)]
  have habstract : ∀ (a b S : ℝ), a ≠ 0 → b ≠ 0 →
      a / b * S * (b / a) = S := by
    intro a b S ha hb
    field_simp
  -- ================= the y-computation =================
  have hy : ∀ k ∈ P.divisors,
      (∑ d ∈ P.divisors.filter (fun d => k ∣ d),
        selbergLambda s P R d * ((sieveRootCard s d : ℝ) / d))
      = if k ≤ R then
          muR k * (∏ p ∈ k.primeFactors,
            ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
          / selbergG s P R
        else 0 := by
    intro k hk
    have hcancel : ∀ d ∈ P.divisors,
        selbergLambda s P R d * ((sieveRootCard s d : ℝ) / d)
        = ∑ k' ∈ (P.divisors.filter (fun k' => k' ≤ R)).filter
            (fun k' => d ∣ k'),
            muR (k' / d) * (muR k' * (∏ p ∈ k'.primeFactors,
                ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
              / selbergG s P R) := by
      intro d hd
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
      have hρd1 : 1 ≤ sieveRootCard s d := one_le_sieveRootCard hd0 s
      have hρdR : (0 : ℝ) < (sieveRootCard s d : ℝ) := by
        have h2 : 0 < sieveRootCard s d :=
          Nat.lt_of_lt_of_le Nat.zero_lt_one hρd1
        exact_mod_cast h2
      rw [selbergLambda]
      exact habstract _ _ _ hdR.ne' hρdR.ne'
    rw [Finset.sum_congr rfl (fun d hd =>
      hcancel d (Finset.mem_filter.mp hd).1)]
    have hinner : ∀ d ∈ P.divisors.filter (fun d => k ∣ d),
        (∑ k' ∈ (P.divisors.filter (fun k' => k' ≤ R)).filter
            (fun k' => d ∣ k'),
            muR (k' / d) * (muR k' * (∏ p ∈ k'.primeFactors,
                ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
              / selbergG s P R))
        = ∑ k' ∈ P.divisors, (if k' ≤ R then (if d ∣ k' then
            muR (k' / d) * (muR k' * (∏ p ∈ k'.primeFactors,
                ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
              / selbergG s P R) else 0) else 0) := by
      intro d _
      rw [Finset.sum_filter, Finset.sum_filter]
    rw [Finset.sum_congr rfl hinner, Finset.sum_filter]
    have hpush : ∀ d : ℕ,
        (if k ∣ d then (∑ k' ∈ P.divisors, (if k' ≤ R then (if d ∣ k' then
            muR (k' / d) * (muR k' * (∏ p ∈ k'.primeFactors,
                ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
              / selbergG s P R) else 0) else 0)) else 0)
        = ∑ k' ∈ P.divisors, (if k ∣ d then (if k' ≤ R then (if d ∣ k' then
            muR (k' / d) * (muR k' * (∏ p ∈ k'.primeFactors,
                ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
              / selbergG s P R) else 0) else 0) else 0) := by
      intro d
      by_cases hc : k ∣ d
      · rw [if_pos hc]
        exact Finset.sum_congr rfl fun k' _ => (if_pos hc).symm
      · rw [if_neg hc]
        exact (Finset.sum_eq_zero fun k' _ => if_neg hc).symm
    rw [Finset.sum_congr rfl fun d _ => hpush d, Finset.sum_comm]
    have hcol : ∀ k' ∈ P.divisors,
        (∑ d ∈ P.divisors, (if k ∣ d then (if k' ≤ R then (if d ∣ k' then
            muR (k' / d) * (muR k' * (∏ p ∈ k'.primeFactors,
                ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
              / selbergG s P R) else 0) else 0) else 0))
        = if k' ≤ R then (if k = k' then
            muR k' * (∏ p ∈ k'.primeFactors,
                ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
              / selbergG s P R else 0) else 0 := by
      intro k' hk'
      by_cases hR' : k' ≤ R
      · simp only [if_pos hR']
        have hsq' : Squarefree k' :=
          hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hk')
        have hconv : (∑ d ∈ P.divisors, (if k ∣ d then (if d ∣ k' then
            muR (k' / d) * (muR k' * (∏ p ∈ k'.primeFactors,
                ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
              / selbergG s P R) else 0) else 0))
            = ∑ d ∈ k'.divisors.filter (fun d => k ∣ d),
                muR (k' / d) * (muR k' * (∏ p ∈ k'.primeFactors,
                    ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
                  / selbergG s P R) := by
          rw [Finset.sum_filter]
          have hsub : k'.divisors ⊆ P.divisors := by
            intro d hd
            rw [Nat.mem_divisors] at hd ⊢
            exact ⟨hd.1.trans (Nat.dvd_of_mem_divisors hk'), hP.ne_zero⟩
          rw [← Finset.sum_subset hsub (fun d _ hnd => ?_)]
          · refine Finset.sum_congr rfl fun d hd => ?_
            rw [Nat.mem_divisors] at hd
            by_cases h1 : k ∣ d
            · rw [if_pos h1, if_pos hd.1, if_pos h1]
            · rw [if_neg h1, if_neg h1]
          · by_cases h1 : k ∣ d
            · rw [if_pos h1, if_neg (fun hc =>
                hnd (Nat.mem_divisors.mpr ⟨hc, hsq'.ne_zero⟩))]
            · rw [if_neg h1]
        rw [hconv, ← Finset.sum_mul]
        by_cases hkk' : k ∣ k'
        · rw [sum_interval_muR hsq' hkk']
          by_cases heq : k = k'
          · rw [if_pos heq, if_pos heq, one_mul]
          · rw [if_neg heq, if_neg heq, zero_mul]
        · have hempty : k'.divisors.filter (fun d => k ∣ d) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro d hd hkd
            exact hkk' (hkd.trans (Nat.dvd_of_mem_divisors hd))
          have hne : k ≠ k' := fun hc => hkk' (hc ▸ dvd_refl k)
          rw [hempty, Finset.sum_empty, zero_mul, if_neg hne]
      · refine Eq.trans (Finset.sum_eq_zero fun d _ => ?_) (if_neg hR').symm
        by_cases h1 : k ∣ d
        · rw [if_pos h1, if_neg hR']
        · rw [if_neg h1]
    rw [Finset.sum_congr rfl hcol,
      Finset.sum_eq_single_of_mem k hk (fun k' _ hne => ?_), if_pos rfl]
    by_cases hR' : k' ≤ R
    · rw [if_pos hR', if_neg (fun hc : k = k' => hne hc.symm)]
    · rw [if_neg hR']
  -- ================= the sum of squares =================
  rw [Finset.sum_congr rfl fun k hk => by rw [hy k hk]]
  have hterm : ∀ k ∈ P.divisors,
      (∏ p ∈ k.primeFactors,
        (((p : ℝ) - sieveRootCard s p) / sieveRootCard s p))
      * ((if k ≤ R then
          muR k * (∏ p ∈ k.primeFactors,
            ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
          / selbergG s P R
        else 0)) ^ 2
      = if k ≤ R then
          (∏ p ∈ k.primeFactors,
            ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
          / selbergG s P R ^ 2
        else 0 := by
    intro k hk
    by_cases hkR : k ≤ R
    · rw [if_pos hkR, if_pos hkR]
      have hμ := muR_sq k
      have hwh := selberg_w_mul_h hP hρlt k hk
      have h1 : (muR k * (∏ p ∈ k.primeFactors,
          ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
          / selbergG s P R) ^ 2
          = (muR k * muR k) * ((∏ p ∈ k.primeFactors,
              ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p))) ^ 2
            / selbergG s P R ^ 2) := by
        ring
      rw [h1, hμ, one_mul]
      have h2 : (∏ p ∈ k.primeFactors,
          (((p : ℝ) - sieveRootCard s p) / sieveRootCard s p))
          * ((∏ p ∈ k.primeFactors,
              ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p))) ^ 2
            / selbergG s P R ^ 2)
          = ((∏ p ∈ k.primeFactors,
              (((p : ℝ) - sieveRootCard s p) / sieveRootCard s p))
            * (∏ p ∈ k.primeFactors,
              ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p))))
            * ((∏ p ∈ k.primeFactors,
              ((sieveRootCard s p : ℝ) / ((p : ℝ) - sieveRootCard s p)))
              / selbergG s P R ^ 2) := by
        ring
      rw [h2, hwh, one_mul]
    · rw [if_neg hkR, if_neg hkR]
      rw [zero_pow (two_ne_zero), mul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, ← Finset.sum_div,
    ← selbergG, sq, ← div_div, div_self hG0.ne']

end MoltResearch
