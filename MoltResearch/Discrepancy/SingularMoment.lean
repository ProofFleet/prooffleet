import MoltResearch.Discrepancy.SelbergPrimorial
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Discrepancy: the singular-series second moment

Track S of the EDP-unconditional campaign (`Problems/tao2015_derivation_c.md`,
issue #3004): the fourth moment of the Euler factor over the dyadic sum
window has linear mass —

  `∑_{t ∈ (2n₀, 4n₀]} (∏_{p ∣ 2t} (1 − 1/p)⁻¹)⁴ ≤ 12·e³⁰·n₀`.

The chain: `(1−1/p)⁻⁴ ≤ 1 + 30/p` per prime; the Euler expansion over the
radical (S4's divisor dictionary); the swap onto the divisors of
`primorial (8n₀)` with the exact multiple count `#{t : k ∣ 2t} = ⌊8n₀/k⌋ −
⌊4n₀/k⌋`; and the key identity `∏_{p∣k} 30/p = k·∏_{p∣k} 30/p²` for
squarefree `k`, which folds both the density and the boundary terms into the
single convergent product `∏_p (1 + 30/p²) ≤ e^{30·∑ 1/p²} ≤ e³⁰` (the
square-harmonic tail `∑_{n≥2} 1/n² ≤ 1` is proved by telescoping). This is
the second-moment input that turns the per-target Selberg bound into the
additive-quadruple count.
-/

namespace MoltResearch

open Finset

/-- The fourth power of the Euler factor: `(1−1/p)⁻⁴ ≤ 1 + 30/p` for `p ≥ 2`. -/
theorem euler_factor_pow_four_le {p : ℕ} (hp : 2 ≤ p) :
    ((1 - 1 / (p : ℝ))⁻¹) ^ 4 ≤ 1 + 30 / (p : ℝ) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have h1 : (1 - 1 / (p : ℝ))⁻¹ ≤ 1 + 2 / (p : ℝ) := by
    have h2 : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
      rw [sub_pos, div_lt_one hp0]
      linarith
    rw [inv_le_iff_one_le_mul₀ h2]
    have h3 : (1 + 2 / (p : ℝ)) * (1 - 1 / (p : ℝ))
        = 1 + 1 / (p : ℝ) - 2 / (p : ℝ) ^ 2 := by
      field_simp
      ring
    rw [h3]
    have h4 : 2 / (p : ℝ) ^ 2 ≤ 1 / (p : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hp0]
      nlinarith
    linarith
  have h0 : (0 : ℝ) ≤ (1 - 1 / (p : ℝ))⁻¹ := by
    have h2 : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
      rw [sub_pos, div_lt_one hp0]
      linarith
    positivity
  have h5 : ((1 - 1 / (p : ℝ))⁻¹) ^ 4 ≤ (1 + 2 / (p : ℝ)) ^ 4 :=
    pow_le_pow_left₀ h0 h1 4
  refine le_trans h5 ?_
  have hx : 0 < 2 / (p : ℝ) := by positivity
  have hx1 : 2 / (p : ℝ) ≤ 1 := by
    rw [div_le_one hp0]
    linarith
  have hexp : (1 + 2 / (p : ℝ)) ^ 4
      = 1 + 8 / (p : ℝ) + 6 * (2 / (p : ℝ)) ^ 2
        + 4 * (2 / (p : ℝ)) ^ 3 + (2 / (p : ℝ)) ^ 4 := by
    field_simp
    ring
  rw [hexp]
  have h6 : (2 / (p : ℝ)) ^ 2 ≤ 2 / (p : ℝ) := by nlinarith
  have h7 : (2 / (p : ℝ)) ^ 3 ≤ 2 / (p : ℝ) := by nlinarith
  have h8 : (2 / (p : ℝ)) ^ 4 ≤ 2 / (p : ℝ) := by nlinarith
  have h9 : (8 : ℝ) / (p : ℝ) + 6 * (2 / (p : ℝ)) + 4 * (2 / (p : ℝ))
      + 2 / (p : ℝ) = 30 / (p : ℝ) := by
    ring
  linarith

/-- The square-harmonic partial sum: `∑_{2 ≤ n ≤ y} 1/n² ≤ 1`. -/
theorem sum_Icc_one_div_sq_le (y : ℕ) :
    ∑ n ∈ Finset.Icc 2 y, (1 / (n : ℝ)) ^ 2 ≤ 1 := by
  have hstrong : ∀ y : ℕ, 1 ≤ y →
      ∑ n ∈ Finset.Icc 2 y, (1 / (n : ℝ)) ^ 2 ≤ 1 - 1 / (y : ℝ) := by
    intro y
    induction y with
    | zero => omega
    | succ m ih =>
      intro _
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        norm_num
      · have hmy : Finset.Icc 2 (m + 1) = insert (m + 1) (Finset.Icc 2 m) := by
          ext x
          rw [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Icc]
          omega
        rw [hmy, Finset.sum_insert (by
          rw [Finset.mem_Icc]
          omega)]
        have hih := ih hm
        have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
        have hkey : (1 / ((m + 1 : ℕ) : ℝ)) ^ 2
            ≤ 1 / (m : ℝ) - 1 / ((m : ℝ) + 1) := by
          push_cast
          rw [div_sub_div _ _ hm0.ne' hm1.ne']
          rw [div_pow, one_pow, div_le_div_iff₀ (by positivity)
            (by positivity)]
          ring_nf
          nlinarith [hm0]
        push_cast
        push_cast at hih hkey
        linarith
  rcases Nat.lt_or_ge y 2 with hy | hy
  · have hempty : Finset.Icc 2 y = ∅ := by
      rw [Finset.Icc_eq_empty]
      omega
    rw [hempty, Finset.sum_empty]
    norm_num
  · have h1 := hstrong y (by omega)
    have hy0 : (0 : ℝ) < (y : ℝ) := by
      exact_mod_cast (by omega : 0 < y)
    have : (0 : ℝ) < 1 / (y : ℝ) := by positivity
    linarith

/-- Multiples of `k` in `(a, b]`: exactly `b/k − a/k` of them. -/
theorem card_Ioc_filter_dvd {a b k : ℕ} (hk : 0 < k) :
    ((Finset.Ioc a b).filter (fun t => k ∣ t)).card = b / k - a / k := by
  classical
  have hbij : ((Finset.Ioc a b).filter (fun t => k ∣ t)).card
      = (Finset.Ioc (a / k) (b / k)).card := by
    refine Finset.card_nbij' (fun t => t / k) (fun m => k * m) ?_ ?_ ?_ ?_
    · intro t ht
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at ht
      obtain ⟨⟨hat, htb⟩, m, hm⟩ := ht
      beta_reduce
      rw [Finset.mem_coe, Finset.mem_Ioc]
      constructor
      · rw [hm, Nat.mul_div_cancel_left m hk]
        by_contra hc
        push_neg at hc
        have h2 : k * m ≤ k * (a / k) := Nat.mul_le_mul_left k hc
        have h3 : k * (a / k) ≤ a := Nat.mul_div_le a k
        omega
      · exact Nat.div_le_div_right htb
    · intro m hm
      beta_reduce
      rw [Finset.mem_coe, Finset.mem_Ioc] at hm
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨?_, ?_⟩, Dvd.intro m rfl⟩
      · by_contra hc
        push_neg at hc
        have h2 : m ≤ a / k := (Nat.le_div_iff_mul_le hk).mpr
          (le_of_eq_of_le (Nat.mul_comm m k) hc)
        exact absurd hm.1 (Nat.not_lt.mpr h2)
      · have := (Nat.le_div_iff_mul_le hk).mp hm.2
        have h4 : k * m ≤ b := by
          calc k * m ≤ k * (b / k) := Nat.mul_le_mul_left k hm.2
            _ ≤ b := Nat.mul_div_le b k
        exact h4
    · intro t ht
      rw [Finset.mem_coe, Finset.mem_filter] at ht
      obtain ⟨-, m, hm⟩ := ht
      beta_reduce
      rw [hm, Nat.mul_div_cancel_left m hk]
    · intro m _
      beta_reduce
      exact Nat.mul_div_cancel_left m hk
  rw [hbij, Nat.card_Ioc]

/-- The radical is squarefree. -/
theorem radN_squarefree (n : ℕ) : Squarefree (radN n) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro p hp q hq hpq
    rw [Finset.mem_coe] at hp hq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).squarefree

/-- Squarefree numbers divide iff they divide the radical. -/
theorem squarefree_dvd_radN_iff {k n : ℕ} (hk : Squarefree k) (hn : n ≠ 0) :
    k ∣ radN n ↔ k ∣ n := by
  constructor
  · intro h
    exact h.trans radN_dvd
  · intro h
    have h1 : ∀ p ∈ k.primeFactors, p ∣ radN n := by
      intro p hp
      have hpn : p ∈ n.primeFactors := by
        rw [Nat.mem_primeFactors]
        exact ⟨Nat.prime_of_mem_primeFactors hp,
          (Nat.dvd_of_mem_primeFactors hp).trans h, hn⟩
      rw [← primeFactors_radN] at hpn
      exact Nat.dvd_of_mem_primeFactors hpn
    calc k = ∏ p ∈ k.primeFactors, p :=
        (Nat.prod_primeFactors_of_squarefree hk).symm
      _ ∣ radN n := Finset.prod_primes_dvd _
          (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) h1

/-- For squarefree `k`: `∏_{p∣k} 30/p = k · ∏_{p∣k} 30/p²`. -/
theorem prod_ratio_eq {k : ℕ} (hk : Squarefree k) :
    ∏ p ∈ k.primeFactors, (30 / (p : ℝ))
      = (k : ℝ) * ∏ p ∈ k.primeFactors, (30 / (p : ℝ) ^ 2) := by
  have hkeq : (k : ℝ) = ∏ p ∈ k.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hk]
  rw [hkeq, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  field_simp

/-- **The convergent Euler bound**: the square-weighted divisor mass of the
primorial is at most `e³⁰`. -/
theorem sum_divisors_primorial_le (y : ℕ) :
    ∑ k ∈ (primorial y).divisors,
        ∏ p ∈ k.primeFactors, (30 / (p : ℝ) ^ 2)
      ≤ Real.exp 30 := by
  rw [sum_divisors_prodPrimeFactors (squarefree_primorial y)]
  calc ∏ p ∈ (primorial y).primeFactors, (1 + 30 / (p : ℝ) ^ 2)
      ≤ ∏ p ∈ (primorial y).primeFactors, Real.exp (30 / (p : ℝ) ^ 2) := by
        refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
        · have hpp := Nat.prime_of_mem_primeFactors hp
          have h2 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
          positivity
        · have h3 := Real.add_one_le_exp (30 / (p : ℝ) ^ 2)
          linarith
    _ = Real.exp (∑ p ∈ (primorial y).primeFactors, 30 / (p : ℝ) ^ 2) :=
        (Real.exp_sum _ _).symm
    _ ≤ Real.exp 30 := by
        rw [Real.exp_le_exp]
        have hsub : (primorial y).primeFactors ⊆ Finset.Icc 2 y := by
          intro p hp
          rw [mem_primeFactors_primorial] at hp
          rw [Finset.mem_Icc]
          exact ⟨hp.1.two_le, hp.2⟩
        have h4 : ∑ p ∈ (primorial y).primeFactors, 30 / (p : ℝ) ^ 2
            ≤ ∑ n ∈ Finset.Icc 2 y, 30 / (n : ℝ) ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
          intro n _ _
          positivity
        have h5 : ∑ n ∈ Finset.Icc 2 y, 30 / (n : ℝ) ^ 2
            = 30 * ∑ n ∈ Finset.Icc 2 y, (1 / (n : ℝ)) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [div_pow, one_pow]
          ring
        have h6 := sum_Icc_one_div_sq_le y
        linarith

/-- **The singular-series second moment**: over the dyadic sum window, the
fourth power of the Euler factor of `2t` has linear mass. -/
theorem sum_singular_pow_four_le (n₀ : ℕ) :
    ∑ t ∈ Finset.Ioc (2 * n₀) (4 * n₀),
        (∏ p ∈ (2 * t).primeFactors, (1 - 1 / (p : ℝ))⁻¹) ^ 4
      ≤ 12 * Real.exp 30 * (n₀ : ℝ) := by
  classical
  have hP8sq := squarefree_primorial (8 * n₀)
  -- per-t: expand into the primorial-divisor ite sum
  have hper : ∀ t ∈ Finset.Ioc (2 * n₀) (4 * n₀),
      (∏ p ∈ (2 * t).primeFactors, (1 - 1 / (p : ℝ))⁻¹) ^ 4
      ≤ ∑ k ∈ (primorial (8 * n₀)).divisors,
          (if k ∣ 2 * t then ∏ p ∈ k.primeFactors, (30 / (p : ℝ)) else 0) := by
    intro t ht
    rw [Finset.mem_Ioc] at ht
    have h2t0 : 2 * t ≠ 0 := by omega
    have hrad0 : radN (2 * t) ≠ 0 :=
      (Finset.prod_pos fun p hp =>
        (Nat.prime_of_mem_primeFactors hp).pos).ne'
    have h1 : (∏ p ∈ (2 * t).primeFactors, (1 - 1 / (p : ℝ))⁻¹) ^ 4
        = ∏ p ∈ (2 * t).primeFactors, ((1 - 1 / (p : ℝ))⁻¹) ^ 4 := by
      rw [Finset.prod_pow]
    have h2 : ∏ p ∈ (2 * t).primeFactors, ((1 - 1 / (p : ℝ))⁻¹) ^ 4
        ≤ ∏ p ∈ (2 * t).primeFactors, (1 + 30 / (p : ℝ)) := by
      refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
      · have hpp := Nat.prime_of_mem_primeFactors hp
        have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
        have h0 : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
          rw [sub_pos, div_lt_one (by linarith)]
          linarith
        positivity
      · exact euler_factor_pow_four_le
          (Nat.prime_of_mem_primeFactors hp).two_le
    have h3 : ∏ p ∈ (2 * t).primeFactors, (1 + 30 / (p : ℝ))
        = ∑ k ∈ (radN (2 * t)).divisors,
            ∏ p ∈ k.primeFactors, (30 / (p : ℝ)) := by
      rw [← primeFactors_radN (2 * t)]
      exact (sum_divisors_prodPrimeFactors (radN_squarefree (2 * t)) _).symm
    have hsub : (radN (2 * t)).divisors ⊆ (primorial (8 * n₀)).divisors := by
      intro k hk
      rw [Nat.mem_divisors] at hk ⊢
      have hksq : Squarefree k :=
        (radN_squarefree (2 * t)).squarefree_of_dvd hk.1
      refine ⟨?_, (primorial_pos (8 * n₀)).ne'⟩
      calc k = ∏ p ∈ k.primeFactors, p :=
          (Nat.prod_primeFactors_of_squarefree hksq).symm
        _ ∣ primorial (8 * n₀) := by
          refine Finset.prod_primes_dvd _
            (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime)
            (fun p hp => ?_)
          have hp1 : p ∣ 2 * t :=
            ((Nat.dvd_of_mem_primeFactors hp).trans hk.1).trans radN_dvd
          have hp2 : p ≤ 8 * n₀ :=
            le_trans (Nat.le_of_dvd (by omega) hp1) (by omega)
          exact Nat.dvd_of_mem_primeFactors
            (mem_primeFactors_primorial.mpr
              ⟨Nat.prime_of_mem_primeFactors hp, hp2⟩)
    have h4 : ∑ k ∈ (radN (2 * t)).divisors,
        ∏ p ∈ k.primeFactors, (30 / (p : ℝ))
        = ∑ k ∈ (primorial (8 * n₀)).divisors,
            (if k ∣ 2 * t then ∏ p ∈ k.primeFactors, (30 / (p : ℝ))
              else 0) := by
      rw [← Finset.sum_subset hsub (fun k hk hnk => ?_)]
      · refine Finset.sum_congr rfl fun k hk => ?_
        rw [Nat.mem_divisors] at hk
        rw [if_pos (hk.1.trans radN_dvd)]
      · rw [Nat.mem_divisors] at hk
        have hksq : Squarefree k := hP8sq.squarefree_of_dvd hk.1
        rw [if_neg ?_]
        intro hdvd
        exact hnk (Nat.mem_divisors.mpr
          ⟨(squarefree_dvd_radN_iff hksq h2t0).mpr hdvd, hrad0⟩)
    calc (∏ p ∈ (2 * t).primeFactors, (1 - 1 / (p : ℝ))⁻¹) ^ 4
        = ∏ p ∈ (2 * t).primeFactors, ((1 - 1 / (p : ℝ))⁻¹) ^ 4 := h1
      _ ≤ ∏ p ∈ (2 * t).primeFactors, (1 + 30 / (p : ℝ)) := h2
      _ = ∑ k ∈ (radN (2 * t)).divisors,
            ∏ p ∈ k.primeFactors, (30 / (p : ℝ)) := h3
      _ = ∑ k ∈ (primorial (8 * n₀)).divisors,
            (if k ∣ 2 * t then ∏ p ∈ k.primeFactors, (30 / (p : ℝ))
              else 0) := h4
  -- sum over the window, swap, and count
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [Finset.sum_comm]
  -- per k: the t-sum is the multiple count times the weight
  have hcount : ∀ k ∈ (primorial (8 * n₀)).divisors,
      ∑ t ∈ Finset.Ioc (2 * n₀) (4 * n₀),
        (if k ∣ 2 * t then ∏ p ∈ k.primeFactors, (30 / (p : ℝ)) else 0)
      ≤ (4 * (n₀ : ℝ) / k + (if k ≤ 8 * n₀ then 1 else 0))
        * ∏ p ∈ k.primeFactors, (30 / (p : ℝ)) := by
    intro k hk
    have hk0 : 0 < k := Nat.pos_of_mem_divisors hk
    have hprod0 : (0 : ℝ) ≤ ∏ p ∈ k.primeFactors, (30 / (p : ℝ)) := by
      refine Finset.prod_nonneg fun p hp => ?_
      have := (Nat.prime_of_mem_primeFactors hp).pos
      positivity
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hprod0
    -- the count of window elements with k ∣ 2t
    have hinj : ((Finset.Ioc (2 * n₀) (4 * n₀)).filter
        (fun t => k ∣ 2 * t)).card
        ≤ ((Finset.Ioc (4 * n₀) (8 * n₀)).filter (fun u => k ∣ u)).card := by
      refine Finset.card_le_card_of_injOn (fun t => 2 * t) ?_ ?_
      · intro t ht
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at ht
        show 2 * t ∈ ↑((Finset.Ioc (4 * n₀) (8 * n₀)).filter
          (fun u => k ∣ u))
        rw [Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨by omega, by omega⟩, ht.2⟩
      · intro t _ t' _ heq
        have h5 : 2 * t = 2 * t' := heq
        omega
    rw [card_Ioc_filter_dvd hk0] at hinj
    have hdivle : 4 * n₀ / k ≤ 8 * n₀ / k :=
      Nat.div_le_div_right (by omega)
    by_cases hk8 : k ≤ 8 * n₀
    · rw [if_pos hk8]
      have hc1 : (((8 * n₀) / k : ℕ) : ℝ) ≤ 8 * (n₀ : ℝ) / (k : ℝ) := by
        have := Nat.cast_div_le (α := ℝ) (m := 8 * n₀) (n := k)
        push_cast at this ⊢
        linarith
      have hc2 : 4 * (n₀ : ℝ) / (k : ℝ) - 1 ≤ (((4 * n₀) / k : ℕ) : ℝ) := by
        have hdm := Nat.div_add_mod (4 * n₀) k
        have hmlt : (4 * n₀) % k < k := Nat.mod_lt _ hk0
        have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
        have hcast : (4 : ℝ) * n₀ = (k : ℝ) * (((4 * n₀) / k : ℕ) : ℝ)
            + (((4 * n₀) % k : ℕ) : ℝ) := by
          exact_mod_cast congrArg (fun x : ℕ => (x : ℝ)) hdm.symm
        have hmR : (((4 * n₀) % k : ℕ) : ℝ) < (k : ℝ) := by
          exact_mod_cast hmlt
        rw [div_sub_one hkR.ne', div_le_iff₀ hkR]
        nlinarith
      have hcast3 : ((((8 * n₀) / k - (4 * n₀) / k : ℕ)) : ℝ)
          = (((8 * n₀) / k : ℕ) : ℝ) - (((4 * n₀) / k : ℕ) : ℝ) :=
        Nat.cast_sub hdivle
      have hinjR : ((((Finset.Ioc (2 * n₀) (4 * n₀)).filter
          (fun t => k ∣ 2 * t)).card : ℕ) : ℝ)
          ≤ ((((8 * n₀) / k - (4 * n₀) / k : ℕ)) : ℝ) := by
        exact_mod_cast hinj
      rw [hcast3] at hinjR
      have hbridge : 8 * (n₀ : ℝ) / (k : ℝ) = 2 * (4 * (n₀ : ℝ) / (k : ℝ)) := by
        ring
      linarith [hinjR, hc1, hc2, hbridge]
    · rw [if_neg hk8]
      have hz : (8 * n₀) / k = 0 := Nat.div_eq_of_lt (by omega)
      have hz2 : (8 * n₀) / k - (4 * n₀) / k = 0 := by
        rw [hz]
        exact Nat.zero_sub _
      rw [hz2] at hinj
      have hcard0 : ((Finset.Ioc (2 * n₀) (4 * n₀)).filter
          (fun t => k ∣ 2 * t)).card = 0 := by omega
      rw [hcard0]
      have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
      have : (0 : ℝ) ≤ 4 * (n₀ : ℝ) / (k : ℝ) := by positivity
      push_cast
      linarith
  refine le_trans (Finset.sum_le_sum hcount) ?_
  -- expand the per-k bound into the two convergent pieces
  have hsplit : ∀ k ∈ (primorial (8 * n₀)).divisors,
      (4 * (n₀ : ℝ) / k + (if k ≤ 8 * n₀ then 1 else 0))
        * ∏ p ∈ k.primeFactors, (30 / (p : ℝ))
      ≤ 12 * (n₀ : ℝ) * ∏ p ∈ k.primeFactors, (30 / (p : ℝ) ^ 2) := by
    intro k hk
    have hk0 : 0 < k := Nat.pos_of_mem_divisors hk
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
    have hksq : Squarefree k := hP8sq.squarefree_of_dvd
      (Nat.dvd_of_mem_divisors hk)
    have hprodeq := prod_ratio_eq hksq
    have hprod20 : (0 : ℝ) ≤ ∏ p ∈ k.primeFactors, (30 / (p : ℝ) ^ 2) := by
      refine Finset.prod_nonneg fun p hp => ?_
      have := (Nat.prime_of_mem_primeFactors hp).pos
      positivity
    by_cases hk8 : k ≤ 8 * n₀
    · rw [if_pos hk8, hprodeq]
      have hkn : (k : ℝ) ≤ 8 * (n₀ : ℝ) := by exact_mod_cast hk8
      have h6 : (4 * (n₀ : ℝ) / k + 1) * ((k : ℝ)
          * ∏ p ∈ k.primeFactors, (30 / (p : ℝ) ^ 2))
          = (4 * (n₀ : ℝ) + (k : ℝ))
            * ∏ p ∈ k.primeFactors, (30 / (p : ℝ) ^ 2) := by
        field_simp
      rw [h6]
      refine mul_le_mul_of_nonneg_right ?_ hprod20
      linarith
    · rw [if_neg hk8, hprodeq]
      have h7 : (4 * (n₀ : ℝ) / k + 0) * ((k : ℝ)
          * ∏ p ∈ k.primeFactors, (30 / (p : ℝ) ^ 2))
          = 4 * (n₀ : ℝ) * ∏ p ∈ k.primeFactors, (30 / (p : ℝ) ^ 2) := by
        field_simp
        ring
      rw [h7]
      refine mul_le_mul_of_nonneg_right ?_ hprod20
      have : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg _
      linarith
  refine le_trans (Finset.sum_le_sum hsplit) ?_
  rw [← Finset.mul_sum]
  have hEuler := sum_divisors_primorial_le (8 * n₀)
  have h12 : (0 : ℝ) ≤ 12 * (n₀ : ℝ) := by positivity
  calc 12 * (n₀ : ℝ) * ∑ k ∈ (primorial (8 * n₀)).divisors,
      ∏ p ∈ k.primeFactors, (30 / (p : ℝ) ^ 2)
      ≤ 12 * (n₀ : ℝ) * Real.exp 30 :=
        mul_le_mul_of_nonneg_left hEuler h12
    _ = 12 * Real.exp 30 * (n₀ : ℝ) := by ring

end MoltResearch
