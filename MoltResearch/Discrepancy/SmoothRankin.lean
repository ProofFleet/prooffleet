import MoltResearch.Discrepancy.RamareIdentity
import MoltResearch.Discrepancy.MertensFirst
import Mathlib.NumberTheory.SmoothNumbers

/-!
# Track R: smooth numbers — Rankin majorization and elementary counts

The smooth-number substrate of the cheap Halász factorization
(campaign #3044, M2-b): the `δ`-damped sum over `k`-smooth numbers is
majorized by the finite Euler product (Rankin's device, exact and
finite), and the smooth counting function obeys the Chebyshev-type
bound `Ψ(x,y)·log x ≤ x + 8·x·log y`, which at `y = x^ε` makes the
`x^ε`-smooth numbers an `O(ε)`-fraction — uniformly in `x`, the form
the three-scale factorization consumes.
-/

namespace MoltResearch

open Finset

/-- Geometric tail: `∑_{e<E} r^e ≤ 1/(1−r)` for `0 ≤ r < 1`. -/
theorem sum_pow_le_one_div (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (E : ℕ) :
    ∑ e ∈ Finset.range E, r^e ≤ 1/(1-r) := by
  have h1r : (0:ℝ) < 1 - r := by linarith
  rw [geom_sum_eq (ne_of_lt hr1)]
  rw [show (r^E - 1)/(r - 1) = (1 - r^E)/(1 - r) from by
    rw [← neg_sub (r^E) 1, ← neg_sub r 1, neg_div_neg_eq]]
  gcongr
  linarith [pow_nonneg hr0 E]

/-- **The Rankin majorization** (Track R, M2-b1): the `δ`-damped sum
over `k`-smooth numbers up to `N` is at most the finite Euler product
`∏_{p<k} (1−p^{−δ})^{−1}` — induction on `k` through the
prime-power split `Nat.equivProdNatSmoothNumbers`. The master input
for smooth-number counts and tails. -/
theorem sum_rpow_smoothNumbersUpTo_le (δ : ℝ) (hδ : 0 < δ) :
    ∀ k N : ℕ, ∑ n ∈ Nat.smoothNumbersUpTo N k, (n:ℝ)^(-δ)
      ≤ ∏ p ∈ k.primesBelow, (1 - (p:ℝ)^(-δ))⁻¹ := by
  intro k
  induction k with
  | zero =>
    intro N
    rw [Nat.primesBelow_zero, Finset.prod_empty]
    have hsub : Nat.smoothNumbersUpTo N 0 ⊆ {1} := by
      intro n hn
      rw [Nat.mem_smoothNumbersUpTo] at hn
      rcases hn with ⟨-, hs⟩
      rw [Nat.smoothNumbers] at hs
      rcases hs with ⟨h0, hall⟩
      rw [Finset.mem_singleton]
      by_contra hne
      obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hne
      have := hall p (Nat.mem_primeFactorsList h0 |>.mpr ⟨hp, hdvd⟩)
      omega
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)) ?_
    rw [Finset.sum_singleton]
    rw [Nat.cast_one, Real.one_rpow]
  | succ k ih =>
    intro N
    by_cases hk : k.Prime
    · -- prime step: split off the k-power
      rw [Nat.primesBelow_succ, if_pos hk,
        Finset.prod_insert (Nat.notMem_primesBelow k)]
      have hk1 : (1:ℕ) < k := hk.one_lt
      have hkr : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk.pos
      have hrpos : 0 < (k:ℝ)^(-δ) := Real.rpow_pos_of_pos hkr _
      have hrlt : (k:ℝ)^(-δ) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hk1)
          (by linarith)
      set E : ℕ := Nat.log k N + 1 with hE_def
      -- the image covering
      have hcover : Nat.smoothNumbersUpTo N (k+1)
          ⊆ Finset.image (fun em : ℕ × ℕ => k^em.1 * em.2)
              ((Finset.range E) ×ˢ (Nat.smoothNumbersUpTo N k)) := by
        intro n hn
        rw [Nat.mem_smoothNumbersUpTo] at hn
        rcases hn with ⟨hnN, hs⟩
        obtain ⟨⟨e, m⟩, hem⟩ :=
          (Nat.equivProdNatSmoothNumbers hk).surjective ⟨n, hs⟩
        have hval : k^e * (m:ℕ) = n := by
          have := congrArg Subtype.val hem
          rwa [Nat.equivProdNatSmoothNumbers_apply' hk] at this
        have hm0 : (m:ℕ) ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers m.2
        have hn0 : n ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hs
        rw [Finset.mem_image]
        refine ⟨(e, m), ?_, hval⟩
        rw [Finset.mem_product, Finset.mem_range, Nat.mem_smoothNumbersUpTo]
        refine ⟨?_, ?_, m.2⟩
        · rw [hE_def]
          have hke : k^e ≤ N := by
            calc k^e ≤ k^e * m := Nat.le_mul_of_pos_right _ (by omega)
              _ = n := hval
              _ ≤ N := hnN
          have := (Nat.pow_le_iff_le_log hk1 (by omega : N ≠ 0)).mp hke
          omega
        · calc (m:ℕ) ≤ k^e * m := Nat.le_mul_of_pos_left _ (pow_pos hk.pos e)
            _ = n := hval
            _ ≤ N := hnN
      have hinj : Set.InjOn (fun em : ℕ × ℕ => k^em.1 * em.2)
          (((Finset.range E) ×ˢ (Nat.smoothNumbersUpTo N k) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
        intro a ha b hb hab
        rw [Finset.mem_coe, Finset.mem_product] at ha hb
        have ham : a.2 ∈ Nat.smoothNumbers k := by
          have := ha.2
          rw [Nat.mem_smoothNumbersUpTo] at this
          exact this.2
        have hbm : b.2 ∈ Nat.smoothNumbers k := by
          have := hb.2
          rw [Nat.mem_smoothNumbersUpTo] at this
          exact this.2
        have heq : (Nat.equivProdNatSmoothNumbers hk) (a.1, ⟨a.2, ham⟩)
            = (Nat.equivProdNatSmoothNumbers hk) (b.1, ⟨b.2, hbm⟩) := by
          rw [Subtype.ext_iff]
          rw [Nat.equivProdNatSmoothNumbers_apply' hk,
            Nat.equivProdNatSmoothNumbers_apply' hk]
          exact hab
        have := (Nat.equivProdNatSmoothNumbers hk).injective heq
        rw [Prod.ext_iff] at this ⊢
        exact ⟨this.1, congrArg Subtype.val this.2⟩
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hcover
        (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)) ?_
      rw [Finset.sum_image hinj]
      have hsplit : ∀ em : ℕ × ℕ, em ∈ (Finset.range E) ×ˢ (Nat.smoothNumbersUpTo N k) →
          ((k^em.1 * em.2 : ℕ) : ℝ)^(-δ)
            = ((k:ℝ)^(-δ))^em.1 * ((em.2:ℕ):ℝ)^(-δ) := by
        intro em hem
        rw [Finset.mem_product, Nat.mem_smoothNumbersUpTo] at hem
        have hm0 : 0 < em.2 := Nat.pos_of_ne_zero
          (Nat.ne_zero_of_mem_smoothNumbers hem.2.2)
        push_cast
        rw [Real.mul_rpow (by positivity) (by exact_mod_cast hm0.le)]
        congr 1
        rw [← Real.rpow_natCast ((k:ℝ)^(-δ)) em.1, ← Real.rpow_mul hkr.le,
          ← Real.rpow_natCast (k:ℝ) em.1, ← Real.rpow_mul hkr.le]
        congr 1
        ring
      rw [Finset.sum_congr rfl hsplit, Finset.sum_product]
      have hfactor : ∑ e ∈ Finset.range E, ∑ m ∈ Nat.smoothNumbersUpTo N k,
          ((k:ℝ)^(-δ))^e * ((m:ℕ):ℝ)^(-δ)
            = (∑ e ∈ Finset.range E, ((k:ℝ)^(-δ))^e)
              * ∑ m ∈ Nat.smoothNumbersUpTo N k, ((m:ℕ):ℝ)^(-δ) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.mul_sum]
      rw [hfactor]
      have hgeom := sum_pow_le_one_div ((k:ℝ)^(-δ)) hrpos.le hrlt E
      have hsmooth_nonneg : (0:ℝ) ≤ ∑ m ∈ Nat.smoothNumbersUpTo N k,
          ((m:ℕ):ℝ)^(-δ) :=
        Finset.sum_nonneg fun m _ => Real.rpow_nonneg (Nat.cast_nonneg m) _
      calc (∑ e ∈ Finset.range E, ((k:ℝ)^(-δ))^e)
            * ∑ m ∈ Nat.smoothNumbersUpTo N k, ((m:ℕ):ℝ)^(-δ)
          ≤ (1/(1-(k:ℝ)^(-δ)))
              * ∑ m ∈ Nat.smoothNumbersUpTo N k, ((m:ℕ):ℝ)^(-δ) :=
            mul_le_mul_of_nonneg_right hgeom hsmooth_nonneg
        _ ≤ (1/(1-(k:ℝ)^(-δ))) * ∏ p ∈ k.primesBelow, (1 - (p:ℝ)^(-δ))⁻¹ := by
            refine mul_le_mul_of_nonneg_left (ih N) ?_
            exact le_of_lt (one_div_pos.mpr (by linarith))
        _ = (1 - (k:ℝ)^(-δ))⁻¹ * ∏ p ∈ k.primesBelow, (1 - (p:ℝ)^(-δ))⁻¹ := by
            rw [one_div]
    · -- non-prime step: nothing changes
      rw [Nat.primesBelow_succ, if_neg hk]
      have hsm : Nat.smoothNumbersUpTo N (k+1) = Nat.smoothNumbersUpTo N k := by
        ext n
        rw [Nat.mem_smoothNumbersUpTo, Nat.mem_smoothNumbersUpTo,
          Nat.smoothNumbers_succ hk]
      rw [hsm]
      exact ih N

open ArithmeticFunction in
/-- **The smooth von Mangoldt mass** (Track R, M2-b2-i): the `Λ/d`
mass carried by `y`-smooth numbers up to any `x` is at most `8 log y`
— prime-power box covering plus Mertens' first theorem. -/
theorem sum_vonMangoldt_div_smooth_le (y x : ℕ) (hy : 2 ≤ y) :
    ∑ d ∈ (Finset.Ioc 0 x).filter (· ∈ Nat.smoothNumbers y),
        vonMangoldt d / d
      ≤ 8 * Real.log y := by
  classical
  set S := (Finset.Ioc 0 x).filter (· ∈ Nat.smoothNumbers y) with hS_def
  set K : ℕ := Nat.log 2 x + 1 with hK_def
  -- restrict to prime powers
  have hzero : ∀ d ∈ S.filter (fun d => ¬ IsPrimePow d),
      vonMangoldt d / d = 0 := by
    intro d hd
    rw [Finset.mem_filter] at hd
    rw [vonMangoldt_eq_zero_iff.mpr hd.2, zero_div]
  have hsplit : ∑ d ∈ S, vonMangoldt d / d
      = ∑ d ∈ S.filter (fun d => IsPrimePow d), vonMangoldt d / d := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun d => IsPrimePow d)]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, add_zero]
  rw [hsplit]
  -- box covering
  have hcover : S.filter (fun d => IsPrimePow d)
      ⊆ Finset.image (fun pk : ℕ × ℕ => pk.1 ^ pk.2)
          (y.primesBelow ×ˢ Finset.Icc 1 K) := by
    intro d hd
    rw [Finset.mem_filter] at hd
    have hdS : d ∈ (Finset.Ioc 0 x).filter (· ∈ Nat.smoothNumbers y) := hd.1
    have hpp := hd.2
    rw [Finset.mem_filter, Finset.mem_Ioc] at hdS
    obtain ⟨⟨hd0, hdx'⟩, hds⟩ := hdS
    obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff d).mp hpp
    rw [Finset.mem_image]
    refine ⟨(p, k), ?_, hpk⟩
    rw [Finset.mem_product, Nat.mem_primesBelow, Finset.mem_Icc]
    have hpd : p ∣ d := hpk ▸ dvd_pow_self p (by omega)
    have hpy : p < y := Nat.mem_smoothNumbers'.mp hds p hp hpd
    have hdx : d ≤ x := hdx'
    have hkK : k ≤ K := by
      have hpk_le : p^k ≤ x := hpk ▸ hdx
      have h2k : 2^k ≤ x := le_trans
        (Nat.pow_le_pow_left hp.two_le k) hpk_le
      have := (Nat.pow_le_iff_le_log (by norm_num)
        (by omega : x ≠ 0)).mp h2k
      omega
    exact ⟨⟨hpy, hp⟩, by omega, hkK⟩
  have hinj : Set.InjOn (fun pk : ℕ × ℕ => pk.1 ^ pk.2)
      ((y.primesBelow ×ˢ Finset.Icc 1 K : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    dsimp only at hab
    rw [Finset.mem_coe, Finset.mem_product, Nat.mem_primesBelow,
      Finset.mem_Icc] at ha hb
    have hpa := ha.1.2
    have hpb := hb.1.2
    have hpq : a.1 = b.1 := by
      have hdvd : a.1 ∣ b.1 ^ b.2 := by
        rw [← hab]
        exact dvd_pow_self a.1 (by have := ha.2.1; omega)
      have := hpa.dvd_of_dvd_pow (n := b.2) hdvd
      exact (Nat.prime_dvd_prime_iff_eq hpa hpb).mp this
    have hexp : a.2 = b.2 := by
      rw [hpq] at hab
      exact Nat.pow_right_injective hpb.two_le hab
    exact Prod.ext hpq hexp
  have hfinal : ∑ pk ∈ y.primesBelow ×ˢ Finset.Icc 1 K,
      vonMangoldt (pk.1 ^ pk.2) / ((pk.1 ^ pk.2 : ℕ)) ≤ 8 * Real.log y := by
    rw [Finset.sum_product]
    have hterm : ∀ p ∈ y.primesBelow,
        ∑ k ∈ Finset.Icc 1 K, vonMangoldt (p ^ k) / (p ^ k : ℕ)
          ≤ 2 * (Real.log p / p) := by
      intro p hp
      have hpp := Nat.prime_of_mem_primesBelow hp
      have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hpp.two_le
      have hval : ∀ k ∈ Finset.Icc 1 K,
          vonMangoldt (p ^ k) / (p ^ k : ℕ)
            = Real.log p * (1/(p:ℝ))^k := by
        intro k hk
        rw [Finset.mem_Icc] at hk
        rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hpp]
        rw [div_pow, one_pow]
        push_cast
        rw [div_eq_mul_one_div]
      rw [Finset.sum_congr rfl hval, ← Finset.mul_sum]
      have hgeom : ∑ k ∈ Finset.Icc 1 K, (1/(p:ℝ))^k ≤ 2/(p:ℝ) := by
        have hshift : ∑ k ∈ Finset.Icc 1 K, (1/(p:ℝ))^k
            = (1/(p:ℝ)) * ∑ j ∈ Finset.range K, (1/(p:ℝ))^j := by
          rw [Finset.mul_sum]
          rw [show Finset.Icc 1 K = Finset.map
            ⟨fun j => j + 1, fun a b h => by simpa using h⟩ (Finset.range K) from ?_]
          · rw [Finset.sum_map]
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [Function.Embedding.coeFn_mk]
            rw [pow_succ]
            ring
          · ext j
            rw [Finset.mem_Icc, Finset.mem_map]
            simp only [Function.Embedding.coeFn_mk]
            constructor
            · rintro ⟨h1, h2⟩
              exact ⟨j - 1, by rw [Finset.mem_range]; omega, by omega⟩
            · rintro ⟨i, hi, rfl⟩
              rw [Finset.mem_range] at hi
              omega
        rw [hshift]
        have hr1 : 1/(p:ℝ) < 1 := by
          rw [div_lt_one (by linarith)]
          linarith
        have hgs := sum_pow_le_one_div (1/(p:ℝ)) (by positivity) hr1 K
        have hbound : (1:ℝ)/(1 - 1/(p:ℝ)) ≤ 2 := by
          rw [div_le_iff₀ (by rw [sub_pos, div_lt_one (by linarith)]; linarith)]
          have : (1:ℝ)/(p:ℝ) ≤ 1/2 := by
            rw [div_le_div_iff₀ (by linarith) (by norm_num)]
            linarith
          linarith
        calc (1/(p:ℝ)) * ∑ j ∈ Finset.range K, (1/(p:ℝ))^j
            ≤ (1/(p:ℝ)) * (1/(1 - 1/(p:ℝ))) :=
              mul_le_mul_of_nonneg_left hgs (by positivity)
          _ ≤ (1/(p:ℝ)) * 2 :=
              mul_le_mul_of_nonneg_left hbound (by positivity)
          _ = 2/(p:ℝ) := by ring
      have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
      calc Real.log p * ∑ k ∈ Finset.Icc 1 K, (1/(p:ℝ))^k
          ≤ Real.log p * (2/(p:ℝ)) :=
            mul_le_mul_of_nonneg_left hgeom hlogp
        _ = 2 * (Real.log p / p) := by ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hM := sum_log_div_primesBelow_le y
    linarith [hM]

  calc ∑ d ∈ S.filter (fun d => IsPrimePow d), vonMangoldt d / d
      ≤ ∑ d ∈ Finset.image (fun pk : ℕ × ℕ => pk.1 ^ pk.2)
          (y.primesBelow ×ˢ Finset.Icc 1 K), vonMangoldt d / d :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover
          (fun d _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg d))
    _ = ∑ pk ∈ y.primesBelow ×ˢ Finset.Icc 1 K,
          vonMangoldt (pk.1 ^ pk.2) / ((pk.1 ^ pk.2 : ℕ)) := by
        rw [Finset.sum_image hinj]
    _ ≤ 8 * Real.log y := hfinal
/-- The smooth indicator is completely multiplicative. -/
theorem completelyMultiplicativeC_smooth_indicator (y : ℕ) :
    CompletelyMultiplicativeC
      (fun n => if n ∈ Nat.smoothNumbers y then (1:ℂ) else 0) := by
  classical
  intro a b ha hb
  dsimp only
  by_cases hab : a * b ∈ Nat.smoothNumbers y
  · have haS : a ∈ Nat.smoothNumbers y :=
      Nat.mem_smoothNumbers_of_dvd hab ⟨b, rfl⟩
    have hbS : b ∈ Nat.smoothNumbers y :=
      Nat.mem_smoothNumbers_of_dvd hab ⟨a, mul_comm a b⟩
    rw [if_pos hab, if_pos haS, if_pos hbS, one_mul]
  · rw [if_neg hab]
    by_cases haS : a ∈ Nat.smoothNumbers y
    · by_cases hbS : b ∈ Nat.smoothNumbers y
      · exact absurd (Nat.mul_mem_smoothNumbers haS hbS) hab
      · rw [if_neg hbS, mul_zero]
    · rw [if_neg haS, zero_mul]

open ArithmeticFunction in
/-- **The elementary smooth-number count** (Track R, M2-b2): the
Chebyshev-type bound `Ψ(x,y)·log x ≤ x + 8·x·log y` — the Cesàro
von Mangoldt convolution at the smooth indicator, with the `Λ`-mass
restricted to smooth prime powers by `sum_vonMangoldt_div_smooth_le`.
At `y = x^ε` this makes the smooth error an `O(ε)`-fraction — the
first error term of the cheap Halász factorization. -/
theorem smoothNumbersUpTo_card_mul_log_le (y x : ℕ) (hy : 2 ≤ y) :
    ((Nat.smoothNumbersUpTo x y).card : ℝ) * Real.log x
      ≤ x + 8 * Real.log y * x := by
  classical
  set f : ℕ → ℂ := fun n => if n ∈ Nat.smoothNumbers y then (1:ℂ) else 0
    with hf_def
  have hcm := completelyMultiplicativeC_smooth_indicator y
  have hfb : ∀ m, ‖f m‖ ≤ 1 := by
    intro m
    rw [hf_def]
    dsimp only
    split <;> simp
  have hfilter : ∀ v : ℕ,
      (Finset.Ioc 0 v).filter (· ∈ Nat.smoothNumbers y)
        = Nat.smoothNumbersUpTo v y := by
    intro v
    ext n
    rw [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_smoothNumbersUpTo]
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩
      exact ⟨h2, h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers h2), h1⟩,
        h2⟩
  have hcard_eq : ∀ v : ℕ, ∑ n ∈ Finset.Ioc 0 v, f n
      = ((Nat.smoothNumbersUpTo v y).card : ℂ) := by
    intro v
    rw [hf_def]
    calc ∑ n ∈ Finset.Ioc 0 v,
          (if n ∈ Nat.smoothNumbers y then (1:ℂ) else 0)
        = ∑ n ∈ (Finset.Ioc 0 v).filter (· ∈ Nat.smoothNumbers y), (1:ℂ) :=
          (Finset.sum_filter _ _).symm
      _ = (((Finset.Ioc 0 v).filter (· ∈ Nat.smoothNumbers y)).card : ℂ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ((Nat.smoothNumbersUpTo v y).card : ℂ) := by rw [hfilter]
  have hcard_le : ∀ v : ℕ, (Nat.smoothNumbersUpTo v y).card ≤ v := by
    intro v
    calc (Nat.smoothNumbersUpTo v y).card
        = ((Finset.Ioc 0 v).filter (· ∈ Nat.smoothNumbers y)).card := by
          rw [hfilter]
      _ ≤ (Finset.Ioc 0 v).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = v := by rw [Nat.card_Ioc, Nat.sub_zero]
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx
    have h0 := hcard_le 0
    have : (Nat.smoothNumbersUpTo 0 y).card = 0 := by omega
    rw [this]
    have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg (by
      have : (2:ℝ) ≤ y := by exact_mod_cast hy
      linarith)
    push_cast
    nlinarith
  -- the identity split
  have hsplit : (∑ n ∈ Finset.Ioc 0 x, f n) * ((Real.log x : ℝ) : ℂ)
      = (∑ n ∈ Finset.Ioc 0 x, f n * (((Real.log x - Real.log n : ℝ)) : ℂ))
        + ∑ n ∈ Finset.Ioc 0 x, f n * ((Real.log n : ℝ) : ℂ) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    ring
  have hlhs : ((Nat.smoothNumbersUpTo x y).card : ℝ) * Real.log x
      = ‖(∑ n ∈ Finset.Ioc 0 x, f n) * ((Real.log x : ℝ) : ℂ)‖ := by
    rw [norm_mul, hcard_eq, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hx))]
  rw [hlhs, hsplit, cesaro_mul_log_eq_vonMangoldt_conv f hcm x]
  refine le_trans (norm_add_le _ _) ?_
  have hmesh : ‖∑ n ∈ Finset.Ioc 0 x, f n * (((Real.log x - Real.log n : ℝ)) : ℂ)‖
      ≤ (x : ℝ) - 1 := by
    refine le_trans (norm_sum_le _ _) ?_
    have hbd : ∀ n ∈ Finset.Ioc 0 x,
        ‖f n * (((Real.log x - Real.log n : ℝ)) : ℂ)‖
          ≤ Real.log x - Real.log n := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hΔ : (0:ℝ) ≤ Real.log x - Real.log n := by
        have := Real.log_le_log (by exact_mod_cast hn.1 : (0:ℝ) < n)
          (by exact_mod_cast hn.2 : (n:ℝ) ≤ x)
        linarith
      rw [abs_of_nonneg hΔ]
      calc ‖f n‖ * (Real.log x - Real.log n)
          ≤ 1 * (Real.log x - Real.log n) :=
            mul_le_mul_of_nonneg_right (hfb n) hΔ
        _ = Real.log x - Real.log n := one_mul _
    refine le_trans (Finset.sum_le_sum hbd) ?_
    exact sum_log_ratio_le x hx
  have hconv : ‖∑ d ∈ Finset.Ioc 0 x, ((vonMangoldt d : ℝ) : ℂ) * f d
        * ∑ m ∈ Finset.Ioc 0 (x/d), f m‖
      ≤ 8 * Real.log y * x := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ d ∈ Finset.Ioc 0 x,
        ‖((vonMangoldt d : ℝ) : ℂ) * f d * ∑ m ∈ Finset.Ioc 0 (x/d), f m‖
          ≤ (if d ∈ Nat.smoothNumbers y then vonMangoldt d / d else 0)
            * x := by
      intro d hd
      rw [Finset.mem_Ioc] at hd
      have hd0 : (0:ℝ) < d := by exact_mod_cast hd.1
      have hΛ0 : (0:ℝ) ≤ vonMangoldt d := vonMangoldt_nonneg
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hΛ0, hcard_eq, Complex.norm_natCast]
      by_cases hds : d ∈ Nat.smoothNumbers y
      · rw [if_pos hds, hf_def]
        dsimp only
        rw [if_pos hds, norm_one, mul_one]
        have h1 : ((Nat.smoothNumbersUpTo (x/d) y).card : ℝ) ≤ (x:ℝ)/d := by
          calc ((Nat.smoothNumbersUpTo (x/d) y).card : ℝ)
              ≤ ((x/d : ℕ) : ℝ) := by exact_mod_cast hcard_le (x/d)
            _ ≤ (x:ℝ)/d := Nat.cast_div_le
        calc vonMangoldt d * ((Nat.smoothNumbersUpTo (x/d) y).card : ℝ)
            ≤ vonMangoldt d * ((x:ℝ)/d) :=
              mul_le_mul_of_nonneg_left h1 hΛ0
          _ = vonMangoldt d / d * x := by ring
      · rw [if_neg hds, hf_def]
        dsimp only
        rw [if_neg hds, norm_zero, mul_zero, zero_mul, zero_mul]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_mul]
    have hmass : ∑ d ∈ Finset.Ioc 0 x,
        (if d ∈ Nat.smoothNumbers y then vonMangoldt d / d else 0)
          = ∑ d ∈ (Finset.Ioc 0 x).filter (· ∈ Nat.smoothNumbers y),
              vonMangoldt d / d := (Finset.sum_filter _ _).symm
    rw [hmass]
    have hb2i := sum_vonMangoldt_div_smooth_le y x hy
    have hx0 : (0:ℝ) ≤ x := Nat.cast_nonneg x
    exact mul_le_mul_of_nonneg_right hb2i hx0
  have hx1 : (1:ℝ) ≤ x := by exact_mod_cast hx
  linarith [hmesh, hconv]



end MoltResearch
