import MoltResearch.Discrepancy.SelbergPrimorial
import MoltResearch.Discrepancy.TuranKubilius

/-!
# Discrepancy: Brun–Titchmarsh, the linear-sieve floor (Track R, C4a-0)

The `s = 0` specialization of the Track-S Selberg machinery: the sieve
polynomial `n(0−n) = −n²` sifts exactly the multiples of each prime
(`sieveRootCard_zero_prime`), so `card_sift_le_primorial_master` at `s = 0`
is the linear sieve for a plain interval. This file supplies its `G`-floor:
the squarefree harmonic floor `log z ≤ 2·∑_{k ≤ z squarefree} 1/k` (via the
`n = b²a` decomposition) gives `selbergG 0 (primorial z) z ≥ ½·log z`.

The next unit assembles these into the Brun–Titchmarsh interval bound
`#{p prime : a < p ≤ a+K} ≤ 256·K/log K`, the prime-gap-thinning input of
the C4a large-values count (campaign #3044).
-/

namespace MoltResearch

open Finset

/-- At `s = 0` the sieve polynomial is `-n²`: one root per prime. -/
theorem sieveRootCard_zero_prime {p : ℕ} (hp : p.Prime) :
    sieveRootCard 0 p = 1 := by
  rw [sieveRootCard_prime hp 0, if_pos (dvd_zero p)]

/-- Squared reciprocals over `[1, z]` sum to less than `2` (telescoping). -/
theorem sum_one_div_sq_Icc_le_two (z : ℕ) :
    ∑ m ∈ Finset.Icc 1 z, (1:ℝ)/(m^2) ≤ 2 := by
  have hstrong : ∀ z : ℕ, 1 ≤ z →
      ∑ m ∈ Finset.Icc 1 z, (1:ℝ)/(m^2) ≤ 2 - 1/z := by
    intro z hz
    induction z, hz using Nat.le_induction with
    | base =>
      have h1 : Finset.Icc 1 1 = {1} := rfl
      rw [h1, Finset.sum_singleton]
      norm_num
    | succ n hn ih =>
      have h1 : Finset.Icc 1 (n+1) = Finset.Ico 1 (n+2) := by
        ext m
        rw [Finset.mem_Icc, Finset.mem_Ico]
        omega
      have h2 : Finset.Icc 1 n = Finset.Ico 1 (n+1) := by
        ext m
        rw [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [h1, Finset.sum_Ico_succ_top (by omega), ← h2]
      have hn0 : (0:ℝ) < n := by exact_mod_cast hn
      have hstep : (1:ℝ)/((n+1)^2) ≤ 1/n - 1/(n+1) := by
        rw [div_sub_div _ _ (ne_of_gt hn0) (by positivity)]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        push_cast
        nlinarith
      push_cast
      push_cast at ih
      linarith
  rcases Nat.eq_zero_or_pos z with rfl | hz
  · simp
  · have h1 := hstrong z hz
    have h2 : (0:ℝ) < 1/(z:ℝ) := by
      have : (0:ℝ) < z := by exact_mod_cast hz
      positivity
    linarith

/-- **The squarefree harmonic floor**: `log z ≤ 2·∑_{k ≤ z squarefree} 1/k`,
by covering the harmonic sum through `n = b²·a` with `a` squarefree. -/
theorem log_le_two_mul_sum_one_div_squarefree (z : ℕ) (hz : 1 ≤ z) :
    Real.log z ≤ 2 * ∑ k ∈ (Finset.Icc 1 z).filter Squarefree, (1:ℝ)/k := by
  classical
  -- total decomposition function
  have hdec : ∀ n : ℕ, ∃ ab : ℕ × ℕ, 0 < n → n ≤ z →
      (ab ∈ ((Finset.Icc 1 z).filter Squarefree) ×ˢ Finset.Icc 1 z
        ∧ ab.2^2 * ab.1 = n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · exact ⟨(1,1), fun h _ => absurd h (lt_irrefl 0)⟩
    rcases le_or_gt n z with hnz | hnz
    · obtain ⟨a, b, ha0, hb0, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos hn0
      refine ⟨(a, b), fun _ _ => ?_⟩
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc,
        Finset.mem_Icc]
      have hb2 : 1 ≤ b^2 := Nat.one_le_pow 2 b hb0
      have han : a ≤ n := by
        calc a = 1 * a := (one_mul a).symm
          _ ≤ b^2 * a := Nat.mul_le_mul_right a hb2
          _ = n := hab
      have hbn : b ≤ n := by
        calc b ≤ b^2 := Nat.le_self_pow two_ne_zero b
          _ = b^2 * 1 := (mul_one _).symm
          _ ≤ b^2 * a := Nat.mul_le_mul_left (b^2) ha0
          _ = n := hab
      exact ⟨⟨⟨⟨ha0, by omega⟩, hsq⟩, ⟨hb0, by omega⟩⟩, hab⟩
    · exact ⟨(1,1), fun _ h => absurd h (by omega)⟩
  choose dec hdecspec using hdec
  have hmem : ∀ n ∈ Finset.Icc 1 z,
      dec n ∈ ((Finset.Icc 1 z).filter Squarefree) ×ˢ Finset.Icc 1 z := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    exact (hdecspec n (by omega) hn.2).1
  have hval : ∀ n ∈ Finset.Icc 1 z, (dec n).2^2 * (dec n).1 = n := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    exact (hdecspec n (by omega) hn.2).2
  have hinj : Set.InjOn dec (Finset.Icc 1 z) := by
    intro n₁ h₁ n₂ h₂ heq
    have hv₁ := hval n₁ h₁
    have hv₂ := hval n₂ h₂
    rw [← hv₁, ← hv₂, heq]
  -- cover the harmonic sum
  have hcover : ∑ n ∈ Finset.Icc 1 z, (1:ℝ)/n
      ≤ ∑ p ∈ ((Finset.Icc 1 z).filter Squarefree) ×ˢ Finset.Icc 1 z,
          (1:ℝ)/(p.2^2 * p.1) := by
    rw [show ∑ n ∈ Finset.Icc 1 z, (1:ℝ)/n
        = ∑ n ∈ Finset.Icc 1 z, (1:ℝ)/((dec n).2^2 * (dec n).1) from
        Finset.sum_congr rfl fun n hn => by
          rw [show ((n:ℝ)) = (((dec n).2^2*(dec n).1 : ℕ) : ℝ) from by
              exact_mod_cast (hval n hn).symm]
          push_cast
          ring]
    have himg : ∑ p ∈ (Finset.Icc 1 z).image dec,
          (1:ℝ)/((p.2:ℝ)^2 * (p.1:ℝ))
        = ∑ n ∈ Finset.Icc 1 z, (1:ℝ)/(((dec n).2:ℝ)^2 * ((dec n).1:ℝ)) :=
      Finset.sum_image (fun n hn m hm => hinj hn hm)
    rw [← himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      rw [Finset.mem_image] at hp
      obtain ⟨n, hn, rfl⟩ := hp
      exact hmem n hn
    · intro p _ _
      positivity
  -- factor the product sum
  have hfactor : ∑ p ∈ ((Finset.Icc 1 z).filter Squarefree) ×ˢ Finset.Icc 1 z,
        (1:ℝ)/(p.2^2 * p.1)
      = (∑ k ∈ (Finset.Icc 1 z).filter Squarefree, (1:ℝ)/k)
        * (∑ m ∈ Finset.Icc 1 z, (1:ℝ)/(m^2)) := by
    rw [Finset.sum_mul_sum]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun m _ => ?_
    push_cast
    rw [one_div, one_div, one_div, mul_inv]
    ring
  -- assemble
  have hlog : Real.log z ≤ ∑ n ∈ Finset.Icc 1 z, (1:ℝ)/n := by
    have h1 : Finset.Icc 1 z = Finset.Ico 1 (z+1) := by
      ext m
      rw [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [h1]
    refine le_trans ?_ (MoltResearch.log_le_sum_one_div_Ico (z+1))
    refine Real.log_le_log (by exact_mod_cast hz) ?_
    exact_mod_cast Nat.le_succ z
  have hsq2 := sum_one_div_sq_Icc_le_two z
  have hS0 : (0:ℝ) ≤ ∑ k ∈ (Finset.Icc 1 z).filter Squarefree, (1:ℝ)/k :=
    Finset.sum_nonneg fun k _ => by positivity
  calc Real.log z ≤ ∑ n ∈ Finset.Icc 1 z, (1:ℝ)/n := hlog
    _ ≤ (∑ k ∈ (Finset.Icc 1 z).filter Squarefree, (1:ℝ)/k)
        * (∑ m ∈ Finset.Icc 1 z, (1:ℝ)/(m^2)) := by
        rw [← hfactor]
        exact hcover
    _ ≤ (∑ k ∈ (Finset.Icc 1 z).filter Squarefree, (1:ℝ)/k) * 2 :=
        mul_le_mul_of_nonneg_left hsq2 hS0
    _ = 2 * ∑ k ∈ (Finset.Icc 1 z).filter Squarefree, (1:ℝ)/k := by ring

/-- **The `G`-floor at `s = 0`**: the linear-sieve Selberg mass at the
primorial modulus dominates half the logarithm — each squarefree `k ≤ z`
divides the primorial and contributes `∏ 1/(p−1) ≥ 1/k`. -/
theorem le_selbergG_zero (z : ℕ) (hz : 1 ≤ z) :
    (1/2 : ℝ) * Real.log z ≤ selbergG 0 (primorial z) z := by
  classical
  have hP := squarefree_primorial z
  have hP0 : primorial z ≠ 0 := hP.ne_zero
  -- squarefree k ≤ z divide the primorial
  have hsub : (Finset.Icc 1 z).filter Squarefree
      ⊆ (primorial z).divisors.filter (· ≤ z) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk1, hkz⟩, hsq⟩ := hk
    rw [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, hP0⟩, hkz⟩
    have h1 : k = ∏ p ∈ k.primeFactors, p :=
      (Nat.prod_primeFactors_of_squarefree hsq).symm
    rw [h1, primorial]
    refine Finset.prod_dvd_prod_of_subset _ _ _ ?_
    intro p hp
    have h2 := Nat.prime_of_mem_primeFactors hp
    have h3 := Nat.le_of_mem_primeFactors hp
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, h2⟩
  -- each Selberg factor is nonnegative on the primorial's divisors
  have hnonneg : ∀ k ∈ (primorial z).divisors.filter (· ≤ z),
      (0:ℝ) ≤ ∏ p ∈ k.primeFactors,
        ((sieveRootCard 0 p : ℝ) / ((p : ℝ) - sieveRootCard 0 p)) := by
    intro k hk
    rw [Finset.mem_filter, Nat.mem_divisors] at hk
    refine Finset.prod_nonneg fun p hp => ?_
    have hprime := Nat.prime_of_mem_primeFactors hp
    rw [sieveRootCard_zero_prime hprime]
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast hprime.two_le
    refine div_nonneg (by norm_num) ?_
    push_cast
    linarith
  -- per-term floor `1/k`
  have hterm : ∀ k ∈ (Finset.Icc 1 z).filter Squarefree,
      (1:ℝ)/k ≤ ∏ p ∈ k.primeFactors,
        ((sieveRootCard 0 p : ℝ) / ((p : ℝ) - sieveRootCard 0 p)) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk1, hkz⟩, hsq⟩ := hk
    have hprod : ∀ p ∈ k.primeFactors,
        ((sieveRootCard 0 p : ℝ) / ((p : ℝ) - sieveRootCard 0 p))
          = 1/((p:ℝ) - 1) := by
      intro p hp
      rw [sieveRootCard_zero_prime (Nat.prime_of_mem_primeFactors hp)]
      norm_num
    rw [Finset.prod_congr rfl hprod]
    have hk_eq : (k:ℝ) = ∏ p ∈ k.primeFactors, (p:ℝ) := by
      rw [show (k:ℝ) = ((∏ p ∈ k.primeFactors, p : ℕ) : ℝ) from by
          rw [Nat.prod_primeFactors_of_squarefree hsq]]
      push_cast
      rfl
    rw [show (1:ℝ)/k = ∏ p ∈ k.primeFactors, (1:ℝ)/p from by
        rw [Finset.prod_div_distrib, Finset.prod_const_one, ← hk_eq]]
    refine Finset.prod_le_prod ?_ ?_
    · intro p hp
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      have h1 : (0:ℝ) < p := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two this
      positivity
    · intro p hp
      have h2 : (2:ℝ) ≤ p := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      linarith
  -- assemble
  have hfloor := log_le_two_mul_sum_one_div_squarefree z hz
  have hchain : ∑ k ∈ (Finset.Icc 1 z).filter Squarefree, (1:ℝ)/k
      ≤ selbergG 0 (primorial z) z := by
    rw [selbergG]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro k hk _
    exact hnonneg k hk
  linarith

end MoltResearch
