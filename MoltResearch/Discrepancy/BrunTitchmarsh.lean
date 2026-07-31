import MoltResearch.Discrepancy.SelbergPrimorial
import MoltResearch.Discrepancy.TuranKubilius
import Mathlib.Analysis.Complex.ExponentialBounds

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

/-- Primes above the sift level survive the `s = 0` sift. -/
theorem primes_gt_subset_sift (a K z : ℕ) :
    (Finset.Ioc a (a + K)).filter (fun q => Nat.Prime q ∧ z < q)
      ⊆ (Finset.Ioc a (a + K)).filter (fun n : ℕ =>
          ∀ p ∈ (primorial z).primeFactors,
            ¬ ((p : ℤ) ∣ (n : ℤ) * ((0 : ℤ) - (n : ℤ)))) := by
  intro q hq
  rw [Finset.mem_filter] at hq ⊢
  obtain ⟨hmem, hqprime, hzq⟩ := hq
  refine ⟨hmem, fun p hp hdvd => ?_⟩
  rw [mem_primeFactors_primorial] at hp
  obtain ⟨hpprime, hpz⟩ := hp
  have h1 : (p:ℤ) ∣ (q:ℤ)^2 := by
    have h2 : (q:ℤ) * ((0:ℤ) - q) = -(q:ℤ)^2 := by ring
    rw [h2] at hdvd
    exact (dvd_neg).mp hdvd
  have h3 : p ∣ q^2 := by exact_mod_cast h1
  have h4 : p ∣ q := hpprime.dvd_of_dvd_pow h3
  have h5 : p = q := (Nat.prime_dvd_prime_iff_eq hpprime hqprime).mp h4
  omega

/-- The prime count splits into the small primes and the sifted survivors. -/
theorem card_primes_le_sift_add (a K z : ℕ) :
    (((Finset.Ioc a (a + K)).filter Nat.Prime).card : ℝ)
      ≤ (z : ℝ) + (((Finset.Ioc a (a + K)).filter (fun n : ℕ =>
          ∀ p ∈ (primorial z).primeFactors,
            ¬ ((p : ℤ) ∣ (n : ℤ) * ((0 : ℤ) - (n : ℤ))))).card : ℝ) := by
  classical
  have hsplit : (Finset.Ioc a (a + K)).filter Nat.Prime
      ⊆ ((Finset.Ioc a (a + K)).filter (fun q => Nat.Prime q ∧ q ≤ z))
        ∪ ((Finset.Ioc a (a + K)).filter (fun q => Nat.Prime q ∧ z < q)) := by
    intro q hq
    rw [Finset.mem_filter] at hq
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases le_or_gt q z with h | h
    · exact Or.inl ⟨hq.1, hq.2, h⟩
    · exact Or.inr ⟨hq.1, hq.2, h⟩
  have hsmall : ((Finset.Ioc a (a + K)).filter
      (fun q => Nat.Prime q ∧ q ≤ z)).card ≤ z := by
    have hsub : (Finset.Ioc a (a + K)).filter (fun q => Nat.Prime q ∧ q ≤ z)
        ⊆ Finset.Icc 1 z := by
      intro q hq
      rw [Finset.mem_filter] at hq
      rw [Finset.mem_Icc]
      exact ⟨hq.2.1.one_lt.le, hq.2.2⟩
    calc ((Finset.Ioc a (a + K)).filter (fun q => Nat.Prime q ∧ q ≤ z)).card
        ≤ (Finset.Icc 1 z).card := Finset.card_le_card hsub
      _ = z := by rw [Nat.card_Icc]; omega
  have hbig := Finset.card_le_card (primes_gt_subset_sift a K z)
  have hcard := Finset.card_union_le
    ((Finset.Ioc a (a + K)).filter (fun q => Nat.Prime q ∧ q ≤ z))
    ((Finset.Ioc a (a + K)).filter (fun q => Nat.Prime q ∧ z < q))
  have h1 := Finset.card_le_card hsplit
  have hnat : ((Finset.Ioc a (a + K)).filter Nat.Prime).card
      ≤ z + (((Finset.Ioc a (a + K)).filter (fun n : ℕ =>
          ∀ p ∈ (primorial z).primeFactors,
            ¬ ((p : ℤ) ∣ (n : ℤ) * ((0 : ℤ) - (n : ℤ))))).card) := by
    have h2 := le_trans h1 hcard
    have h3 := Nat.add_le_add hsmall hbig
    omega
  exact_mod_cast hnat

-- (nucleus copies of the Track-S numerics pair, TrackCStage5QuadrupleSieveProof)
/-- The logarithmic floor of the natural square root:
`log n / 2 − log 2 ≤ log ⌊√n⌋` for `n ≥ 4`. -/
theorem log_nat_sqrt_ge {n : ℕ} (hn : 4 ≤ n) :
    Real.log n / 2 - Real.log 2 ≤ Real.log (Nat.sqrt n) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (by omega : 0 < n)
  have h4 : (2 : ℝ) ≤ Real.sqrt n := by
    have h1 : ((4 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 := Real.sqrt_le_sqrt h1
    have h3 : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
      rw [show (((4 : ℕ) : ℝ)) = (2 : ℝ) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    linarith
  have hlt : Real.sqrt n < (Nat.sqrt n : ℝ) + 1 := by
    have h1 : (n : ℝ) < ((Nat.sqrt n : ℝ) + 1) ^ 2 := by
      have h2 := Nat.lt_succ_sqrt n
      have h3 : (n : ℝ) < ((Nat.succ (Nat.sqrt n) : ℕ) : ℝ)
          * ((Nat.succ (Nat.sqrt n) : ℕ) : ℝ) := by
        exact_mod_cast h2
      push_cast at h3
      nlinarith [h3]
    have h4' := Real.sqrt_lt_sqrt (Nat.cast_nonneg n) h1
    rwa [Real.sqrt_sq (by positivity)] at h4'
  have hs : Real.sqrt n / 2 ≤ ((Nat.sqrt n : ℕ) : ℝ) := by
    linarith
  have hsq0 : (0 : ℝ) < Real.sqrt n / 2 := by
    have := Real.sqrt_pos.mpr hn0
    linarith
  calc Real.log n / 2 - Real.log 2
      = Real.log (Real.sqrt n / 2) := by
        rw [Real.log_div (by positivity) (by norm_num),
          Real.log_sqrt (Nat.cast_nonneg n)]
    _ ≤ Real.log ((Nat.sqrt n : ℕ) : ℝ) :=
        Real.log_le_log hsq0 hs

/-- The five-fold square-root iterate keeps a `1/64` share of the logarithm
and stays above `2¹⁰`, beyond the threshold `2³²⁰`. -/
theorem log_iter_sqrt_bounds {n₀ : ℕ} (hn₀ : 2 ^ 320 ≤ n₀) :
    1024 ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))))
    ∧ Real.log n₀ / 64
      ≤ Real.log (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))))) := by
  have hstep : ∀ (m k : ℕ), 2 ^ (2 * k) ≤ m → 2 ^ k ≤ Nat.sqrt m := by
    intro m k h
    refine Nat.le_sqrt.mpr ?_
    have he : 2 ^ k * 2 ^ k = 2 ^ (2 * k) := by
      rw [← pow_add, ← Nat.two_mul]
    rw [he]
    exact h
  have h1 : 2 ^ 160 ≤ Nat.sqrt n₀ := hstep n₀ 160 (by omega)
  have h2 : 2 ^ 80 ≤ Nat.sqrt (Nat.sqrt n₀) := hstep _ 80 (by
    calc 2 ^ (2 * 80) = 2 ^ 160 := by norm_num
      _ ≤ Nat.sqrt n₀ := h1)
  have h3 : 2 ^ 40 ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)) := hstep _ 40 (by
    calc 2 ^ (2 * 40) = 2 ^ 80 := by norm_num
      _ ≤ Nat.sqrt (Nat.sqrt n₀) := h2)
  have h4 : 2 ^ 20 ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))) :=
    hstep _ 20 (by
      calc 2 ^ (2 * 20) = 2 ^ 40 := by norm_num
        _ ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)) := h3)
  have h5 : 2 ^ 10 ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))) :=
    hstep _ 10 (by
      calc 2 ^ (2 * 10) = 2 ^ 20 := by norm_num
        _ ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))) := h4)
  refine ⟨by norm_num at h5 ⊢; omega, ?_⟩
  -- the log chain
  have hL1 := log_nat_sqrt_ge (n := n₀) (by omega)
  have hL2 := log_nat_sqrt_ge (n := Nat.sqrt n₀) (by
    have := h1
    omega)
  have hL3 := log_nat_sqrt_ge (n := Nat.sqrt (Nat.sqrt n₀)) (by
    have := h2
    omega)
  have hL4 := log_nat_sqrt_ge (n := Nat.sqrt (Nat.sqrt (Nat.sqrt n₀))) (by
    have := h3
    omega)
  have hL5 := log_nat_sqrt_ge
    (n := Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt n₀)))) (by
    have := h4
    omega)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : 320 * Real.log 2 ≤ Real.log n₀ := by
    have h6 : ((2 ^ 320 : ℕ) : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀
    have h7 := Real.log_le_log (by positivity) h6
    rw [show ((2 ^ 320 : ℕ) : ℝ) = (2 : ℝ) ^ 320 by push_cast; ring,
      Real.log_pow] at h7
    push_cast at h7
    linarith
  linarith

/-- **The sieve step**: for any sift level `2 ≤ z`,
`#{p prime ∈ (a, a+K]} ≤ z + 2K/log z + z⁸`. -/
theorem card_primes_le_sieve (a K z : ℕ) (hz : 2 ≤ z) :
    (((Finset.Ioc a (a + K)).filter Nat.Prime).card : ℝ)
      ≤ (z:ℝ) + 2 * K / Real.log z + (z:ℝ)^8 := by
  have hlogz : (0:ℝ) < Real.log z := Real.log_pos (by exact_mod_cast hz)
  have hmaster := card_sift_le_primorial_master (s := 0) (z := z) (N := K)
    (a := a) (by norm_num) (by omega)
  have hG := le_selbergG_zero z (by omega)
  have hG0 : (0:ℝ) < selbergG 0 (primorial z) z := by linarith
  have hKG : (K:ℝ) / selbergG 0 (primorial z) z ≤ 2*K/Real.log z := by
    rw [div_le_div_iff₀ hG0 hlogz]
    have hK0 : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
    nlinarith
  have hz8 : (((z:ℝ))^4)^2 = (z:ℝ)^8 := by ring
  have hstep := card_primes_le_sift_add a K z
  calc (((Finset.Ioc a (a + K)).filter Nat.Prime).card : ℝ)
      ≤ (z : ℝ) + (((Finset.Ioc a (a + K)).filter (fun n : ℕ =>
          ∀ p ∈ (primorial z).primeFactors,
            ¬ ((p : ℤ) ∣ (n : ℤ) * ((0 : ℤ) - (n : ℤ))))).card : ℝ) := hstep
    _ ≤ (z : ℝ) + ((K : ℝ) / selbergG 0 (primorial z) z + ((z:ℝ)^4)^2) := by
        linarith [hmaster]
    _ ≤ (z:ℝ) + 2 * K / Real.log z + (z:ℝ)^8 := by
        rw [← hz8]
        linarith [hKG]

/-- One square root halves the logarithm: `log ⌊√m⌋ ≤ log m / 2`. -/
theorem log_nat_sqrt_le {m : ℕ} (hm : 1 ≤ m) :
    Real.log (Nat.sqrt m) ≤ Real.log m / 2 := by
  have hs1 : 1 ≤ Nat.sqrt m := by
    have := Nat.sqrt_pos.mpr (show 0 < m by omega)
    omega
  have h1 : Nat.sqrt m * Nat.sqrt m ≤ m := by
    have h := Nat.sqrt_le' m
    rwa [sq] at h
  have hs0 : (0:ℝ) < (Nat.sqrt m : ℝ) := by exact_mod_cast hs1
  have h2 : Real.log ((Nat.sqrt m : ℝ) * (Nat.sqrt m : ℝ)) ≤ Real.log m := by
    refine Real.log_le_log (by positivity) ?_
    exact_mod_cast h1
  rw [Real.log_mul (ne_of_gt hs0) (ne_of_gt hs0)] at h2
  linarith

/-- Five square roots: `log z ≤ log K / 32`. -/
theorem log_iter_sqrt_le {K : ℕ} (hK : 1 ≤ K) :
    Real.log (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt K)))))
      ≤ Real.log K / 32 := by
  have hp : ∀ m : ℕ, 1 ≤ m → 1 ≤ Nat.sqrt m := by
    intro m hm
    have := Nat.sqrt_pos.mpr (show 0 < m by omega)
    omega
  have h1 : 1 ≤ Nat.sqrt K := hp K hK
  have h2 : 1 ≤ Nat.sqrt (Nat.sqrt K) := hp _ h1
  have h3 : 1 ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt K)) := hp _ h2
  have h4 : 1 ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt K))) := hp _ h3
  have hL1 := log_nat_sqrt_le hK
  have hL2 := log_nat_sqrt_le h1
  have hL3 := log_nat_sqrt_le h2
  have hL4 := log_nat_sqrt_le h3
  have hL5 := log_nat_sqrt_le h4
  linarith

/-- **Brun–Titchmarsh, crude form** (C4a-0): the number of primes in any
interval `(a, a+K]` is at most `256·K/log K` for `K ≥ 2` — the linear
Selberg sieve at sift level `K^{1/32}`, with the trivial bound below the
`2³²⁰` threshold. -/
theorem card_primes_Ioc_le (a K : ℕ) (hK : 2 ≤ K) :
    (((Finset.Ioc a (a + K)).filter Nat.Prime).card : ℝ)
      ≤ 256 * K / Real.log K := by
  have hK1 : (1:ℝ) < K := by exact_mod_cast hK
  have hlogK : (0:ℝ) < Real.log K := Real.log_pos hK1
  have hK0 : (0:ℝ) < K := by linarith
  rcases lt_or_ge K (2^320) with hsmall | hbig
  · -- trivial regime: `log K < 222 < 256`
    have hcard : (((Finset.Ioc a (a + K)).filter Nat.Prime).card : ℝ) ≤ K := by
      have h1 : ((Finset.Ioc a (a + K)).filter Nat.Prime).card ≤ K := by
        calc ((Finset.Ioc a (a + K)).filter Nat.Prime).card
            ≤ (Finset.Ioc a (a + K)).card := Finset.card_filter_le _ _
          _ = K := by rw [Nat.card_Ioc]; omega
      exact_mod_cast h1
    have hlog222 : Real.log K < 222 := by
      have h1 : (K:ℝ) < 2^320 := by exact_mod_cast hsmall
      have h2 : Real.log K < Real.log (2^320) :=
        Real.log_lt_log hK0 h1
      rw [Real.log_pow] at h2
      have h3 := Real.log_two_lt_d9
      push_cast at h2
      nlinarith
    rw [le_div_iff₀ hlogK]
    nlinarith
  · -- sieve regime
    set z := Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt K)))) with hz_def
    obtain ⟨hz1024, hzlog⟩ := log_iter_sqrt_bounds hbig
    rw [← hz_def] at hz1024 hzlog
    have hz2 : 2 ≤ z := by omega
    have hzK : 1 ≤ K := by omega
    have hsieve := card_primes_le_sieve a K z hz2
    have hlogz0 : (0:ℝ) < Real.log z :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < z))
    have hlogK222 : (221:ℝ) ≤ Real.log K := by
      have h1 : ((2:ℝ))^320 ≤ K := by exact_mod_cast hbig
      have h2 := Real.log_le_log (by positivity) h1
      rw [Real.log_pow] at h2
      have h3 := Real.log_two_gt_d9
      push_cast at h2
      nlinarith
    -- (i) `2K/log z ≤ 128K/log K`
    have hterm1 : 2 * (K:ℝ) / Real.log z ≤ 128 * K / Real.log K := by
      rw [div_le_div_iff₀ hlogz0 hlogK]
      have h1 : Real.log K / 64 ≤ Real.log z := hzlog
      nlinarith [hK0.le]
    -- (ii)+(iii): `z + z⁸ ≤ 2·z⁸ ≤ 2K/log K` via logs
    have hzlogup := log_iter_sqrt_le hzK
    rw [← hz_def] at hzlogup
    have hloglog : Real.log (Real.log K) ≤ Real.log K / 64 + 5 := by
      have h1 : Real.log (Real.log K)
          = Real.log (Real.log K / 64) + Real.log 64 := by
        rw [← Real.log_mul (by linarith) (by norm_num)]
        congr 1
        field_simp
      have h2 : Real.log (Real.log K / 64) ≤ Real.log K / 64 - 1 :=
        Real.log_le_sub_one_of_pos (by linarith)
      have h3 : Real.log 64 ≤ 5 := by
        have h4 : (64:ℝ) = 2^6 := by norm_num
        rw [h4, Real.log_pow]
        have := Real.log_two_lt_d9
        push_cast
        nlinarith
      linarith
    have hz8K : (z:ℝ)^8 * Real.log K ≤ K := by
      have hz0 : (0:ℝ) < (z:ℝ) := by
        exact_mod_cast (by omega : 0 < z)
      have h1 : Real.log ((z:ℝ)^8 * Real.log K)
          = 8 * Real.log z + Real.log (Real.log K) := by
        rw [Real.log_mul (by positivity) (ne_of_gt hlogK), Real.log_pow]
        push_cast
        ring
      have h2 : 8 * Real.log z + Real.log (Real.log K) ≤ Real.log K := by
        have h3 : 8 * Real.log z ≤ Real.log K / 4 := by linarith
        linarith
      have h4 : Real.log ((z:ℝ)^8 * Real.log K) ≤ Real.log K := by
        rw [h1]; exact h2
      have h7 := Real.exp_le_exp.mpr h4
      rw [Real.exp_log (show (0:ℝ) < (z:ℝ)^8 * Real.log K by positivity)] at h7
      rw [Real.exp_log hK0] at h7
      exact h7
    have hterm23 : (z:ℝ) + (z:ℝ)^8 ≤ 128 * K / Real.log K := by
      have hz1 : (1:ℝ) ≤ (z:ℝ) := by exact_mod_cast (by omega : 1 ≤ z)
      have h1 : (z:ℝ) ≤ (z:ℝ)^8 := by
        have h := pow_le_pow_right₀ hz1 (show 1 ≤ 8 by omega)
        rwa [pow_one] at h
      have h2 : (z:ℝ)^8 ≤ K / Real.log K := by
        rw [div_eq_mul_inv]
        rw [show (z:ℝ)^8 = (z:ℝ)^8 * Real.log K * (Real.log K)⁻¹ from by
            field_simp]
        exact mul_le_mul_of_nonneg_right hz8K (by positivity)
      have h3 : (K:ℝ)/Real.log K ≤ 64 * K / Real.log K := by
        rw [div_le_div_iff₀ hlogK hlogK]
        nlinarith [hK0.le, hlogK.le]
      calc (z:ℝ) + (z:ℝ)^8 ≤ 2 * ((z:ℝ)^8) := by linarith
        _ ≤ 2 * ((K:ℝ)/Real.log K) := by linarith
        _ = 2*(K:ℝ)/Real.log K := by ring
        _ ≤ 128 * K / Real.log K :=
            div_le_div_of_nonneg_right (by linarith) hlogK.le
    have hbridge : 256 * (K:ℝ) / Real.log K
        = 128*(K:ℝ)/Real.log K + 128*(K:ℝ)/Real.log K := by ring
    linarith [hsieve, hterm1, hterm23, hbridge]

/-- **The dyadic gap sum**: primes within `2^j` of `p` contribute at most
`2 + 370·∑_{1≤i<j} 1/i` to the reciprocal-gap sum — each dyadic shell
`(2^i, 2^{i+1}]` holds at most `256·2^i/(i·log 2)` primes, each with gap
`> 2^i`. -/
theorem sum_one_div_gap_shell_le (p : ℕ) :
    ∀ j : ℕ, 1 ≤ j →
    ∑ q ∈ (Finset.Ioc p (p + 2^j)).filter Nat.Prime, (1:ℝ)/(q - p)
      ≤ 2 + 370 * ∑ i ∈ Finset.Ico 1 j, (1:ℝ)/i := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    -- `(p, p+2]`: at most two terms, each `≤ 1`
    have hcard : ((Finset.Ioc p (p + 2^1)).filter Nat.Prime).card ≤ 2 := by
      calc ((Finset.Ioc p (p + 2^1)).filter Nat.Prime).card
          ≤ (Finset.Ioc p (p + 2^1)).card := Finset.card_filter_le _ _
        _ = 2 := by rw [Nat.card_Ioc]; omega
    have hterm : ∀ q ∈ (Finset.Ioc p (p + 2^1)).filter Nat.Prime,
        (1:ℝ)/(q - p) ≤ 1 := by
      intro q hq
      rw [Finset.mem_filter, Finset.mem_Ioc] at hq
      have h1 : p + 1 ≤ q := hq.1.1
      have h2 : (1:ℝ) ≤ (q:ℝ) - p := by
        have h3 : ((p:ℝ)) + 1 ≤ q := by exact_mod_cast h1
        linarith
      rw [div_le_one (by linarith)]
      linarith
    have hsum := Finset.sum_le_card_nsmul
      ((Finset.Ioc p (p + 2^1)).filter Nat.Prime)
      (fun q => (1:ℝ)/((q:ℝ) - p)) 1 hterm
    rw [nsmul_eq_mul, mul_one] at hsum
    have hfin : (((Finset.Ioc p (p + 2^1)).filter Nat.Prime).card : ℝ)
        ≤ 2 := by exact_mod_cast hcard
    refine le_trans (le_trans hsum hfin) ?_
    rw [Finset.Ico_self, Finset.sum_empty]
    norm_num
  | succ j hj1 ih =>
    -- split `(p, p+2^{j+1}] = (p, p+2^j] ∪ (p+2^j, p+2^{j+1}]`
    have hsplit : Finset.Ioc p (p + 2^(j+1))
        = Finset.Ioc p (p + 2^j) ∪ Finset.Ioc (p + 2^j) (p + 2^(j+1)) := by
      rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.le_add_right p (2^j)) (by
        have h := Nat.pow_le_pow_right (show 0 < 2 by norm_num)
          (Nat.le_succ j)
        exact Nat.add_le_add_left h p)]
    have hdisj : Disjoint
        ((Finset.Ioc p (p + 2^j)).filter Nat.Prime)
        ((Finset.Ioc (p + 2^j) (p + 2^(j+1))).filter Nat.Prime) := by
      refine Finset.disjoint_filter_filter ?_
      refine Finset.disjoint_left.mpr fun q hq1 hq2 => ?_
      rw [Finset.mem_Ioc] at hq1 hq2
      omega
    have hfilter_union : (Finset.Ioc p (p + 2^(j+1))).filter Nat.Prime
        = ((Finset.Ioc p (p + 2^j)).filter Nat.Prime)
          ∪ ((Finset.Ioc (p + 2^j) (p + 2^(j+1))).filter Nat.Prime) := by
      rw [hsplit, Finset.filter_union]
    rw [hfilter_union, Finset.sum_union hdisj]
    -- the new shell: count ≤ 256·2^j/(j·log 2), gaps > 2^j
    have hshell : ∑ q ∈ (Finset.Ioc (p + 2^j) (p + 2^(j+1))).filter
          Nat.Prime, (1:ℝ)/(q - p)
        ≤ 370 / j := by
      have hK2 : 2 ≤ 2^j := by
        calc 2 = 2^1 := by norm_num
          _ ≤ 2^j := Nat.pow_le_pow_right (by norm_num) hj1
      have hcard := card_primes_Ioc_le (p + 2^j) (2^j) hK2
      rw [show p + 2^j + 2^j = p + 2^(j+1) from by rw [pow_succ]; ring]
        at hcard
      have hterm : ∀ q ∈ (Finset.Ioc (p + 2^j) (p + 2^(j+1))).filter
          Nat.Prime, (1:ℝ)/(q - p) ≤ ((2:ℝ)^j)⁻¹ := by
        intro q hq
        rw [Finset.mem_filter, Finset.mem_Ioc] at hq
        have h1 : p + 2^j + 1 ≤ q := hq.1.1
        have h2 : ((2:ℝ))^j < (q:ℝ) - p := by
          have h3 : ((p:ℝ)) + 2^j + 1 ≤ q := by exact_mod_cast h1
          linarith
        rw [show ((2:ℝ)^j)⁻¹ = 1/((2:ℝ)^j) from (one_div _).symm]
        exact one_div_le_one_div_of_le (by positivity) h2.le
      have hlog2j : Real.log ((2:ℝ)^j) = j * Real.log 2 := by
        rw [Real.log_pow]
      have hlogpos : (0:ℝ) < j * Real.log 2 := by
        have h3 := Real.log_two_gt_d9
        have h4 : (1:ℝ) ≤ j := by exact_mod_cast hj1
        nlinarith
      calc ∑ q ∈ (Finset.Ioc (p + 2^j) (p + 2^(j+1))).filter Nat.Prime,
            (1:ℝ)/(q - p)
          ≤ ∑ _q ∈ (Finset.Ioc (p + 2^j) (p + 2^(j+1))).filter Nat.Prime,
              ((2:ℝ)^j)⁻¹ := Finset.sum_le_sum hterm
        _ = (((Finset.Ioc (p + 2^j) (p + 2^(j+1))).filter Nat.Prime).card
              : ℝ) * ((2:ℝ)^j)⁻¹ := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (256 * (2^j : ℕ) / Real.log ((2^j : ℕ) : ℝ)) * ((2:ℝ)^j)⁻¹ := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact hcard
        _ ≤ 370 / j := by
            rw [show (((2^j : ℕ) : ℝ)) = (2:ℝ)^j from by push_cast; ring]
            rw [hlog2j]
            rw [div_mul_eq_mul_div, div_le_div_iff₀ (by nlinarith) (by
              have h4 : (1:ℝ) ≤ j := by exact_mod_cast hj1
              linarith)]
            have h3 := Real.log_two_gt_d9
            have hp2 : (0:ℝ) < (2:ℝ)^j := by positivity
            have h5 : 256 * (2:ℝ)^j * ((2:ℝ)^j)⁻¹ * (j:ℝ)
                = 256 * (j:ℝ) := by
              field_simp
            nlinarith [mul_pos hp2 hlogpos]
    -- the harmonic increment
    have hharm : ∑ i ∈ Finset.Ico 1 (j+1), (1:ℝ)/i
        = ∑ i ∈ Finset.Ico 1 j, (1:ℝ)/i + 1/j := by
      rw [Finset.sum_Ico_succ_top (by omega)]
    rw [hharm]
    have hj0 : (0:ℝ) < j := by exact_mod_cast hj1
    have h370 : 370 / (j:ℝ) = 370 * (1/j) := by ring
    linarith [ih, hshell]

/-- **The reciprocal prime-gap sum**: `∑_{q prime, p < q ≤ p+H} 1/(q−p)` is
`O(loglog H)` — Brun–Titchmarsh on dyadic shells plus the harmonic ceiling
on the shell indices. This is the near-diagonal thinning of the C4a
window-energy bound. -/
theorem sum_one_div_gap_le (p H : ℕ) (hH : 16 ≤ H) :
    ∑ q ∈ (Finset.Ioc p (p + H)).filter Nat.Prime, (1:ℝ)/((q:ℝ) - p)
      ≤ 742 + 370 * Real.log (Real.log H) := by
  set J := Nat.log 2 H with hJ_def
  have hJ4 : 4 ≤ J := by
    rw [hJ_def]
    calc 4 = Nat.log 2 16 := by
          rw [show (16:ℕ) = 2^4 from by norm_num, Nat.log_pow (by norm_num)]
      _ ≤ Nat.log 2 H := Nat.log_mono_right hH
  have hHJ : H < 2^(J+1) := Nat.lt_pow_succ_log_self (by norm_num) H
  have hsub : (Finset.Ioc p (p + H)).filter Nat.Prime
      ⊆ (Finset.Ioc p (p + 2^(J+1))).filter Nat.Prime := by
    refine Finset.filter_subset_filter _ ?_
    intro q hq
    rw [Finset.mem_Ioc] at hq ⊢
    omega
  have hnonneg : ∀ q ∈ (Finset.Ioc p (p + 2^(J+1))).filter Nat.Prime,
      (0:ℝ) ≤ (1:ℝ)/((q:ℝ) - p) := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_Ioc] at hq
    have h1 : ((p:ℝ)) + 1 ≤ q := by exact_mod_cast hq.1.1
    have h2 : (0:ℝ) < (q:ℝ) - p := by linarith
    positivity
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun q hq _ => hnonneg q hq)
  have hshell := sum_one_div_gap_shell_le p (J+1) (by omega)
  -- the harmonic ceiling on the shell indices
  have hharm : ∑ i ∈ Finset.Ico 1 (J+1), (1:ℝ)/i ≤ Real.log J + 1 :=
    sum_one_div_Ico_succ_le_log_add_one J
  -- `log J ≤ 1 + loglog H`
  have hJlog : Real.log J ≤ 1 + Real.log (Real.log H) := by
    have h2 : (2:ℕ)^J ≤ H := Nat.pow_log_le_self 2 (by omega)
    have h3 : (J:ℝ) * Real.log 2 ≤ Real.log H := by
      have h4 : ((2:ℝ))^(J:ℕ) ≤ (H:ℝ) := by exact_mod_cast h2
      have h5 := Real.log_le_log (by positivity) h4
      rw [Real.log_pow] at h5
      push_cast at h5
      linarith
    have h6 := Real.log_two_gt_d9
    have h7 : (J:ℝ) ≤ 2 * Real.log H := by nlinarith
    have hJ0 : (0:ℝ) < J := by
      have : (0:ℕ) < J := by omega
      exact_mod_cast this
    have hlogH0 : (0:ℝ) < Real.log H := by
      have h8 : (J:ℝ) * Real.log 2 ≤ Real.log H := h3
      nlinarith
    calc Real.log J ≤ Real.log (2 * Real.log H) :=
          Real.log_le_log hJ0 h7
      _ = Real.log 2 + Real.log (Real.log H) := by
          rw [Real.log_mul (by norm_num) (ne_of_gt hlogH0)]
      _ ≤ 1 + Real.log (Real.log H) := by
          have h9 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
          linarith
  calc ∑ q ∈ (Finset.Ioc p (p + H)).filter Nat.Prime, (1:ℝ)/((q:ℝ) - p)
      ≤ ∑ q ∈ (Finset.Ioc p (p + 2^(J+1))).filter Nat.Prime,
          (1:ℝ)/((q:ℝ) - p) := hmono
    _ ≤ 2 + 370 * ∑ i ∈ Finset.Ico 1 (J+1), (1:ℝ)/i := hshell
    _ ≤ 2 + 370 * (Real.log J + 1) := by linarith
    _ ≤ 2 + 370 * (1 + Real.log (Real.log H) + 1) := by linarith
    _ = 742 + 370 * Real.log (Real.log H) := by ring

end MoltResearch
