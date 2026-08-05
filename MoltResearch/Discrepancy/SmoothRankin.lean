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



/-- Telescoped square-ish tail on an integer interval. -/
theorem sum_Icc_inv_mul_pred_le (y : ℕ) (hy : 1 ≤ y) :
    ∑ n ∈ Finset.Icc 2 y, 1/((n:ℝ)*((n:ℝ)-1)) ≤ 1 - 1/(y:ℝ) := by
  induction y with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      norm_num
    · rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ k+1)]
      have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
      have hid : 1/(((k+1:ℕ):ℝ)*(((k+1:ℕ):ℝ)-1))
          = 1/(k:ℝ) - 1/((k:ℝ)+1) := by
        push_cast
        rw [div_sub_div _ _ (by linarith) (by linarith)]
        congr 1
        · ring
        · ring
      rw [hid]
      have := ih hk
      push_cast
      linarith

/-- The prime tail `∑_{p<y} 1/(p(p−1)) ≤ 1`. -/
theorem sum_one_div_mul_pred_primesBelow_le (y : ℕ) :
    ∑ p ∈ y.primesBelow, 1/((p:ℝ)*((p:ℝ)-1)) ≤ 1 := by
  classical
  rcases Nat.lt_or_ge y 1 with hy | hy
  · have : y.primesBelow = ∅ := by
      ext p
      rw [Nat.mem_primesBelow]
      simp only [Finset.notMem_empty, iff_false, not_and]
      intro h
      omega
    rw [this]
    simp
  have hsub : y.primesBelow ⊆ (Finset.Icc 2 y) := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    rw [Finset.mem_Icc]
    exact ⟨hp.2.two_le, by omega⟩
  have hnn : ∀ n ∈ Finset.Icc 2 y, (0:ℝ) ≤ 1/((n:ℝ)*((n:ℝ)-1)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have h2 : (2:ℝ) ≤ n := by exact_mod_cast hn.1
    have : (0:ℝ) < (n:ℝ)*((n:ℝ)-1) := by nlinarith
    positivity
  have hy0 : (0:ℝ) < y := by exact_mod_cast hy
  calc ∑ p ∈ y.primesBelow, 1/((p:ℝ)*((p:ℝ)-1))
      ≤ ∑ n ∈ Finset.Icc 2 y, 1/((n:ℝ)*((n:ℝ)-1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => hnn n hn)
    _ ≤ 1 - 1/(y:ℝ) := sum_Icc_inv_mul_pred_le y hy
    _ ≤ 1 := by
        have : (0:ℝ) ≤ 1/(y:ℝ) := by positivity
        linarith

/-- **The Mertens product bound** (Track R, E2-iii): the harmonic Euler
product over primes below `y` is a single power of `log` —
`∏_{p<y}(1−1/p)⁻¹ ≤ e¹²·log y` for `y ≥ 4`, from the sharp mass bound
with the telescoped tail. -/
theorem prod_one_sub_inv_primesBelow_le (y : ℕ) (hy : 4 ≤ y) :
    ∏ p ∈ y.primesBelow, (1 - 1/(p:ℝ))⁻¹ ≤ Real.exp 12 * Real.log y := by
  classical
  have hp_pos : ∀ p ∈ y.primesBelow, (0:ℝ) < 1 - 1/(p:ℝ) := by
    intro p hp
    have hp2 : (2:ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have : 1/(p:ℝ) ≤ 1/2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    linarith
  have hfac : ∀ p ∈ y.primesBelow, (1 - 1/(p:ℝ))⁻¹
      = Real.exp (Real.log ((1 - 1/(p:ℝ))⁻¹)) := by
    intro p hp
    rw [Real.exp_log (by
      have := hp_pos p hp
      positivity)]
  rw [Finset.prod_congr rfl hfac, ← Real.exp_sum]
  have hterm : ∀ p ∈ y.primesBelow,
      Real.log ((1 - 1/(p:ℝ))⁻¹) ≤ 1/(p:ℝ) + 1/((p:ℝ)*((p:ℝ)-1)) := by
    intro p hp
    have hpp := hp_pos p hp
    have hp2 : (2:ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have hlog := Real.log_le_sub_one_of_pos
      (show (0:ℝ) < (1 - 1/(p:ℝ))⁻¹ from by positivity)
    have hp1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
    have hinv : (1 - 1/(p:ℝ))⁻¹ - 1 = 1/((p:ℝ)-1) := by
      have h1 : (1 - 1/(p:ℝ))⁻¹ = (p:ℝ)/((p:ℝ)-1) := by
        rw [inv_eq_one_div]
        rw [div_eq_div_iff (by linarith) (by linarith)]
        field_simp
      rw [h1, div_sub_one (by linarith : ((p:ℝ)-1) ≠ 0)]
      congr 1
      ring
    have hsplit : 1/((p:ℝ)-1) = 1/(p:ℝ) + 1/((p:ℝ)*((p:ℝ)-1)) := by
      rw [div_add_div _ _ (by linarith : (p:ℝ) ≠ 0)
        (by positivity : (p:ℝ)*((p:ℝ)-1) ≠ 0)]
      rw [div_eq_div_iff (by linarith) (by positivity)]
      ring
    linarith [hlog, hinv ▸ hlog]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib] at hsum
  have hmass := sum_one_div_primesBelow_le_sharp y hy
  have htail := sum_one_div_mul_pred_primesBelow_le y
  have hlogy : (1:ℝ) < Real.log y := by
    have h4 : Real.log 4 ≤ Real.log y :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hy)
    rw [show (4:ℝ) = 2^2 from by norm_num, Real.log_pow] at h4
    have := Real.log_two_gt_d9
    push_cast at h4
    nlinarith
  calc Real.exp (∑ p ∈ y.primesBelow, Real.log ((1 - 1/(p:ℝ))⁻¹))
      ≤ Real.exp (Real.log (Real.log y) + 12) := by
        rw [Real.exp_le_exp]
        have hone : ∑ p ∈ y.primesBelow, 1/(p:ℝ)
            = ∑ p ∈ y.primesBelow, (1:ℝ)/p := rfl
        linarith [hsum, hmass, htail]
    _ = Real.exp 12 * Real.log y := by
        rw [Real.exp_add, Real.exp_log (by linarith)]
        ring

/-- **The smooth harmonic bound** (E2-iii corollary): the harmonic mass
of `y`-smooth numbers is a single power of `log`. -/
theorem sum_smooth_one_div_le (y N : ℕ) (hy : 4 ≤ y) :
    ∑ n ∈ Nat.smoothNumbersUpTo N y, (1:ℝ)/n
      ≤ Real.exp 12 * Real.log y := by
  have hrankin := sum_rpow_smoothNumbersUpTo_le 1 (by norm_num) y N
  have hconv1 : ∀ n : ℕ, (n:ℝ)^(-(1:ℝ)) = 1/(n:ℝ) := by
    intro n
    rw [Real.rpow_neg_one, one_div]
  have hconv2 : ∀ p : ℕ, (1 - (p:ℝ)^(-(1:ℝ)))⁻¹ = (1 - 1/(p:ℝ))⁻¹ := by
    intro p
    rw [hconv1]
  calc ∑ n ∈ Nat.smoothNumbersUpTo N y, (1:ℝ)/n
      = ∑ n ∈ Nat.smoothNumbersUpTo N y, (n:ℝ)^(-(1:ℝ)) := by
        refine Finset.sum_congr rfl fun n _ => (hconv1 n).symm
    _ ≤ ∏ p ∈ y.primesBelow, (1 - (p:ℝ)^(-(1:ℝ)))⁻¹ := hrankin
    _ = ∏ p ∈ y.primesBelow, (1 - 1/(p:ℝ))⁻¹ :=
        Finset.prod_congr rfl fun p _ => hconv2 p
    _ ≤ Real.exp 12 * Real.log y := prod_one_sub_inv_primesBelow_le y hy

open ArithmeticFunction in
/-- **The von Mangoldt mass** (Track R, M0-e): the unrestricted
`Λ/d`-mass up to `z` is at most `8·log(z+2)`.  Every `d ≤ z` is
`(z+2)`-smooth, so this is the smooth mass bound at the trivial cut. -/
theorem sum_vonMangoldt_div_le (z : ℕ) :
    ∑ d ∈ Finset.Ioc 0 z, vonMangoldt d / d ≤ 8 * Real.log (z+2) := by
  classical
  have hsmooth : ∀ d ∈ Finset.Ioc 0 z, d ∈ Nat.smoothNumbers (z+2) := by
    intro d hd
    rw [Finset.mem_Ioc] at hd
    rw [Nat.mem_smoothNumbers]
    refine ⟨by omega, fun p hp => ?_⟩
    have hple : p ≤ d :=
      Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactorsList hp)
    omega
  have hfilter : (Finset.Ioc 0 z).filter (· ∈ Nat.smoothNumbers (z+2))
      = Finset.Ioc 0 z := Finset.filter_true_of_mem hsmooth
  have h := sum_vonMangoldt_div_smooth_le (z+2) z (by omega)
  rw [hfilter] at h
  refine le_trans h ?_
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine Real.log_le_log (by positivity) ?_
  push_cast
  linarith

open ArithmeticFunction in
/-- **The shifted von Mangoldt mass** (Track R, M0-e, GHS (2.6)): for
any real shift `λ`, the `Λ(m)m^λ/m`-mass over a block `(y, z]` is at
most `max 1 (z^λ)` times the unshifted mass.  The `max` is the two
regimes of GHS's `(x/y)^{max(λ,0)}`: for `λ ≥ 0` the largest term sits
at the top of the block, for `λ < 0` at the bottom. -/
theorem sum_vonMangoldt_rpow_div_le (y z : ℕ) (lam : ℝ) :
    ∑ m ∈ Finset.Ioc y z, vonMangoldt m * (m:ℝ)^lam/m
      ≤ max 1 ((z:ℝ)^lam) * (8 * Real.log (z+2)) := by
  classical
  have hstep : ∀ m ∈ Finset.Ioc y z,
      vonMangoldt m * (m:ℝ)^lam/m
        ≤ max 1 ((z:ℝ)^lam) * (vonMangoldt m / m) := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    have hm1 : 1 ≤ m := by omega
    have hm1R : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
    have hmz : (m:ℝ) ≤ (z:ℝ) := by exact_mod_cast hm.2
    have hpow : (m:ℝ)^lam ≤ max 1 ((z:ℝ)^lam) := by
      rcases le_or_gt 0 lam with hlam | hlam
      · refine le_trans (Real.rpow_le_rpow (by linarith) hmz hlam) ?_
        exact le_max_right _ _
      · refine le_trans ?_ (le_max_left _ _)
        exact Real.rpow_le_one_of_one_le_of_nonpos hm1R (by linarith)
    have hΛ : (0:ℝ) ≤ vonMangoldt m := vonMangoldt_nonneg
    have hm0 : (0:ℝ) < (m:ℝ) := by linarith
    have heq : vonMangoldt m * (m:ℝ)^lam/m
        = (vonMangoldt m/m) * (m:ℝ)^lam := by ring
    rw [heq, mul_comm (max 1 ((z:ℝ)^lam))]
    exact mul_le_mul_of_nonneg_left hpow (div_nonneg hΛ hm0.le)
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (le_trans zero_le_one (le_max_left _ _))
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
    (sum_vonMangoldt_div_le z)
  · intro m hm
    rw [Finset.mem_Ioc] at hm ⊢
    exact ⟨by omega, hm.2⟩
  · intro m _ _
    exact div_nonneg vonMangoldt_nonneg (by positivity)

open ArithmeticFunction Finset in
/-- **The prime-power correction** (Track R, M0-r): the `Λ`-mass
carried by proper prime powers up to `N` is `≪ √N·log₂N·log N`.  Every
such `n = p^k` has `k ≥ 2`, hence `p ≤ √N`, so the whole set injects
into `primesBelow (√N+1) ×ˢ Icc 2 (log₂ N)`.  This is the lower-order
term separating the prime count of Brun–Titchmarsh from the full von
Mangoldt weight of GHS Lemma 2.6. -/
theorem sum_vonMangoldt_properPrimePow_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
        vonMangoldt n
      ≤ ((Nat.sqrt N + 1 : ℕ) : ℝ) * ((Nat.log 2 N : ℕ) : ℝ)
          * Real.log (N : ℝ) := by
  classical
  set S := (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ ¬ n.Prime) with hS_def
  set K : ℕ := Nat.log 2 N with hK_def
  -- every element is a proper prime power, so `p ≤ √N` and `k ≤ log₂ N`
  have hcover : S ⊆ Finset.image (fun pk : ℕ × ℕ => pk.1 ^ pk.2)
      ((Nat.sqrt N + 1).primesBelow ×ˢ Finset.Icc 2 K) := by
    intro n hn
    rw [hS_def, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hpp, hnp⟩ := hn
    obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff n).mp hpp
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with hk1 | hk2
      · interval_cases k
        exact absurd (by rw [← hpk, pow_one]; exact hp) hnp
      · exact hk2
    have hpsq : p^2 ≤ n := by
      calc p^2 ≤ p^k := Nat.pow_le_pow_right hp.one_lt.le hk2
        _ = n := hpk
    have hpsqrt : p ≤ Nat.sqrt N := by
      refine Nat.le_sqrt.mpr ?_
      calc p*p = p^2 := by ring
        _ ≤ n := hpsq
        _ ≤ N := hnN
    have hkK : k ≤ K := by
      have h2k : 2^k ≤ N := by
        calc 2^k ≤ p^k := Nat.pow_le_pow_left hp.two_le k
          _ = n := hpk
          _ ≤ N := hnN
      rw [hK_def]
      exact (Nat.le_log_iff_pow_le (by norm_num) (by omega : N ≠ 0)).mpr h2k
    rw [Finset.mem_image]
    refine ⟨(p, k), ?_, hpk⟩
    rw [Finset.mem_product, Nat.mem_primesBelow, Finset.mem_Icc]
    exact ⟨⟨by omega, hp⟩, hk2, hkK⟩
  -- bound each term by `log N`, then count
  have hterm : ∀ n ∈ S, vonMangoldt n ≤ Real.log (N:ℝ) := by
    intro n hn
    rw [hS_def, Finset.mem_filter, Finset.mem_Icc] at hn
    refine le_trans vonMangoldt_le_log ?_
    refine Real.log_le_log ?_ ?_
    · have : (1:ℕ) ≤ n := hn.1.1
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    · exact_mod_cast hn.1.2
  have hcard : (S.card : ℝ)
      ≤ ((Nat.sqrt N + 1 : ℕ) : ℝ) * ((K : ℕ) : ℝ) := by
    have h1 : S.card ≤ ((Nat.sqrt N + 1).primesBelow ×ˢ Finset.Icc 2 K).card :=
      le_trans (Finset.card_le_card hcover) (Finset.card_image_le)
    have h2 : ((Nat.sqrt N + 1).primesBelow ×ˢ Finset.Icc 2 K).card
        = (Nat.sqrt N + 1).primesBelow.card * (Finset.Icc 2 K).card :=
      Finset.card_product _ _
    have h3 : (Nat.sqrt N + 1).primesBelow.card ≤ Nat.sqrt N + 1 := by
      have hsub : (Nat.sqrt N + 1).primesBelow ⊆ Finset.range (Nat.sqrt N + 1) := by
        rw [Nat.primesBelow]
        exact Finset.filter_subset _ _
      calc (Nat.sqrt N + 1).primesBelow.card
          ≤ (Finset.range (Nat.sqrt N + 1)).card := Finset.card_le_card hsub
        _ = Nat.sqrt N + 1 := Finset.card_range _
    have h4 : (Finset.Icc 2 K).card ≤ K := by
      rw [Nat.card_Icc]
      omega
    have h5 : S.card ≤ (Nat.sqrt N + 1) * K := by
      refine le_trans h1 ?_
      rw [h2]
      exact Nat.mul_le_mul h3 h4
    exact_mod_cast h5
  have hlogN : (0:ℝ) ≤ Real.log (N:ℝ) := by
    refine Real.log_nonneg ?_
    exact_mod_cast hN
  calc ∑ n ∈ S, vonMangoldt n
      ≤ ∑ _n ∈ S, Real.log (N:ℝ) := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * Real.log (N:ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((Nat.sqrt N + 1 : ℕ) : ℝ) * ((K : ℕ) : ℝ)) * Real.log (N:ℝ) :=
        mul_le_mul_of_nonneg_right hcard hlogN

open ArithmeticFunction Finset in
/-- **Splitting the von Mangoldt weight** (Track R, M0-ee): a
`Λ`-weighted sum splits into its prime part, where `Λ(p) = log p`
exactly, and its proper prime-power part.  Only prime powers contribute
at all, so the two pieces are the whole sum.

This is the step that lets the Brun–Titchmarsh shell machinery — which
counts *primes* — be applied to a `Λ`-weighted sum.  The prime-power
remainder is genuinely lower order (`sum_vonMangoldt_properPrimePow_le`
bounds it by `√N·log₂N·log N`), but it cannot simply be dropped: `Λ`
is supported on prime powers, not on primes. -/
theorem sum_vonMangoldt_split (S : Finset ℕ) (g : ℕ → ℝ) :
    ∑ n ∈ S, vonMangoldt n * g n
      = (∑ p ∈ S.filter Nat.Prime, Real.log p * g p)
        + ∑ n ∈ S.filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
            vonMangoldt n * g n := by
  classical
  -- only prime powers contribute
  have hzero : ∀ n ∈ S, n ∉ S.filter IsPrimePow → vonMangoldt n * g n = 0 := by
    intro n hn hnot
    rw [Finset.mem_filter] at hnot
    have hnp : ¬ IsPrimePow n := fun hpp => hnot ⟨hn, hpp⟩
    rw [vonMangoldt_eq_zero_iff.mpr hnp, zero_mul]
  rw [← Finset.sum_subset (Finset.filter_subset IsPrimePow S) hzero,
    ← Finset.sum_filter_add_sum_filter_not (S.filter IsPrimePow) Nat.Prime]
  congr 1
  · -- on the primes the weight is exactly `log p`
    have hset : (S.filter IsPrimePow).filter Nat.Prime = S.filter Nat.Prime := by
      ext p
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hS, _⟩, hp⟩
        exact ⟨hS, hp⟩
      · rintro ⟨hS, hp⟩
        exact ⟨⟨hS, hp.isPrimePow⟩, hp⟩
    rw [hset]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    rw [vonMangoldt_apply_prime hp.2]
  · -- the rest is the proper prime powers
    rw [Finset.filter_filter]

open ArithmeticFunction Finset Real in
/-- **The inner sum of GHS Lemma 2.6** (Track R, M0-hh): over a dyadic
block, the full `Λ`-weighted Gaussian mass around a centre `m` is
bounded by the shells, the undecayed diagonal, the Gaussian tail, and a
prime-power remainder.

The remainder is the price of `Λ` being supported on prime powers
rather than primes.  It is genuinely lower order — `√(2N)·log₂(2N)·log(2N)`
against a main term of size `h ≈ 2m/T` — but it cannot be dropped,
only bounded, since the Brun–Titchmarsh machinery underneath counts
primes and says nothing about higher powers.  Each such term carries a
Gaussian factor `≤ 1`, so the crude bound of
`sum_vonMangoldt_properPrimePow_le` suffices. -/
theorem vonMangoldt_gaussian_block_le (T : ℝ) (N m h J : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioc N (2*N)) (hmS : m ∈ S) (hN : 1 ≤ N)
    (hh : 2 ≤ h) (hscale : 2*(m:ℝ) ≤ (h:ℝ)*T)
    (hfit : (2^J - 1)*h + 1 ≤ m) (hwfit : ∀ j < J, 2^j*h ≤ 2*m)
    (hreach : N ≤ 4*((2^J - 1)*h))
    (L : ℝ) (hL : Real.log (4*(m:ℝ)+2)/Real.log ((h:ℕ):ℝ) ≤ L)
    (B : ℝ) (hB : ∑ n ∈ S, Real.log (n:ℝ) ≤ B) :
    ∑ n ∈ S, vonMangoldt n
        * Real.exp (-(π*T^2*(Real.log (n:ℝ) - Real.log (m:ℝ))^2))
      ≤ 1024*(h:ℝ)*L + Real.log (m:ℝ) + Real.exp (-(π*T^2/64)) * B
        + ((Nat.sqrt (2*N) + 1 : ℕ):ℝ) * ((Nat.log 2 (2*N) : ℕ):ℝ)
            * Real.log ((2*N : ℕ):ℝ) := by
  classical
  rw [sum_vonMangoldt_split S
    (fun n => Real.exp (-(π*T^2*(Real.log (n:ℝ) - Real.log (m:ℝ))^2)))]
  have hprime := ExpSums.prime_gaussian_block_le T N m h J S hS hmS hN hh
    hscale hfit hwfit hreach L hL B hB
  -- the prime-power remainder: every Gaussian factor is at most one
  have hpp : ∑ n ∈ S.filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
      vonMangoldt n
        * Real.exp (-(π*T^2*(Real.log (n:ℝ) - Real.log (m:ℝ))^2))
      ≤ ((Nat.sqrt (2*N) + 1 : ℕ):ℝ) * ((Nat.log 2 (2*N) : ℕ):ℝ)
          * Real.log ((2*N : ℕ):ℝ) := by
    have hstep : ∀ n ∈ S.filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
        vonMangoldt n
            * Real.exp (-(π*T^2*(Real.log (n:ℝ) - Real.log (m:ℝ))^2))
          ≤ vonMangoldt n := by
      intro n _
      have h1 : Real.exp (-(π*T^2*(Real.log (n:ℝ) - Real.log (m:ℝ))^2))
          ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        have hnn : (0:ℝ)
            ≤ π*T^2*(Real.log (n:ℝ) - Real.log (m:ℝ))^2 := by positivity
        linarith
      calc vonMangoldt n
            * Real.exp (-(π*T^2*(Real.log (n:ℝ) - Real.log (m:ℝ))^2))
          ≤ vonMangoldt n * 1 :=
            mul_le_mul_of_nonneg_left h1 vonMangoldt_nonneg
        _ = vonMangoldt n := mul_one _
    refine le_trans (Finset.sum_le_sum hstep) ?_
    have hsub : S.filter (fun n => IsPrimePow n ∧ ¬ n.Prime)
        ⊆ (Finset.Icc 1 (2*N)).filter (fun n => IsPrimePow n ∧ ¬ n.Prime) := by
      intro n hn
      simp only [Finset.mem_filter] at hn ⊢
      have hmem := hS hn.1
      rw [Finset.mem_Ioc] at hmem
      exact ⟨Finset.mem_Icc.mpr ⟨by omega, hmem.2⟩, hn.2⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => vonMangoldt_nonneg)) ?_
    exact sum_vonMangoldt_properPrimePow_le (2*N) (by omega)
  linarith

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **The sharp mean value theorem, in terms of the inner sum**
(Track R, M0-ii): the window energy of a `Λ`-weighted Dirichlet
polynomial is bounded by the diagonal `∑ |a(m)|²Λ(m)`, with constant
`e^π·T·Q` where `Q` is any uniform bound on the Gaussian inner sum.

This is GHS Lemma 2.6 (equivalently Lemma 1 of the `κ = 1` paper) with
the arithmetic factored out into `Q`.  The point of the factoring is
that `Q ≪ m` is what the whole shell-and-tail apparatus establishes,
and once it is in hand this lemma delivers the theorem: the weight `Λ`
appears to the *first* power on the right, not the second, because
`intervalIntegral_norm_sq_gaussian_diag_le` carries it in the kernel
rather than in the coefficients. -/
theorem intervalIntegral_vonMangoldt_mvt_le (T : ℝ) (hT : 0 < T)
    (S : Finset ℕ) (a : ℕ → ℂ) (Q : ℝ)
    (hQ : ∀ m ∈ S, ∑ n ∈ S, vonMangoldt n
        * Real.exp (-(π*T^2*(Real.log (m:ℝ) - Real.log (n:ℝ))^2)) ≤ Q) :
    (∫ ξ in (-T)..T, ‖∑ n ∈ S, (a n * ((vonMangoldt n : ℝ) : ℂ))
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
      ≤ Real.exp π * T * Q * ∑ m ∈ S, ‖a m‖^2 * vonMangoldt m := by
  classical
  have hexpT : (0:ℝ) ≤ Real.exp π * T :=
    mul_nonneg (Real.exp_pos _).le hT.le
  -- the weight is non-negative, so the diagonal collapse applies
  refine le_trans (ExpSums.intervalIntegral_norm_sq_gaussian_diag_le S a
    (fun n => vonMangoldt n) (fun n => vonMangoldt_nonneg) T hT) ?_
  -- each inner sum is at most `e^π·T·Q`
  have hinner : ∀ m ∈ S, ∑ n ∈ S, (vonMangoldt n : ℝ)
      * (Real.exp π * T
          * Real.exp (-(π*T^2*(Real.log (m:ℝ) - Real.log (n:ℝ))^2)))
      ≤ Real.exp π * T * Q := by
    intro m hm
    have heq : ∑ n ∈ S, (vonMangoldt n : ℝ)
        * (Real.exp π * T
            * Real.exp (-(π*T^2*(Real.log (m:ℝ) - Real.log (n:ℝ))^2)))
        = Real.exp π * T * ∑ n ∈ S, (vonMangoldt n : ℝ)
            * Real.exp (-(π*T^2*(Real.log (m:ℝ) - Real.log (n:ℝ))^2)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left (hQ m hm) hexpT
  have hmid : ∑ m ∈ S, ‖a m‖^2 * (vonMangoldt m : ℝ)
        * ∑ n ∈ S, (vonMangoldt n : ℝ)
            * (Real.exp π * T
                * Real.exp (-(π*T^2*(Real.log (m:ℝ) - Real.log (n:ℝ))^2)))
      ≤ ∑ m ∈ S, ‖a m‖^2 * (vonMangoldt m : ℝ) * (Real.exp π * T * Q) := by
    refine Finset.sum_le_sum fun m hm => ?_
    exact mul_le_mul_of_nonneg_left (hinner m hm)
      (mul_nonneg (sq_nonneg _) vonMangoldt_nonneg)
  refine le_trans hmid ?_
  rw [← Finset.sum_mul]
  exact le_of_eq (mul_comm _ _)

open ArithmeticFunction Finset Real in
/-- **The inner sum at the canonical scale** (Track R, M0-jj): with the
free parameters fixed — `h = ⌈2m/T⌉` and `J` maximal — the Gaussian
inner sum over a dyadic block is bounded by `6144·h` plus three lower
order terms: the undecayed diagonal `log m`, the Gaussian tail, and the
prime-power remainder.

The `6144 = 1024·6` is where `log_ratio_ceil_scale_le` pays off: the
Brun–Titchmarsh ratio is an absolute constant at this scale, so the
main term is a clean multiple of `h ≈ 2m/T`.  Multiplied by the `T`
that the Gaussian transform contributes, that is `O(m)` — which is
exactly the shape GHS Lemma 2.6 needs.

The hypothesis `2h ≤ N` is what makes the shells reach a quarter of the
block: from maximality `m ≤ 2a_J + h`, so `4a_J ≥ 2m − 2h > 2N − N = N`.
It is mild — `h ≈ 2m/T ≤ 4N/T`, so it holds once `T` is a large
constant. -/
theorem inner_sum_block_le (T : ℝ) (N m : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioc N (2*N)) (hmS : m ∈ S) (hN : 1 ≤ N)
    (hT : 2 ≤ T) (hTm : T^2 ≤ (m:ℝ))
    (hsmall : 2*(⌈2*(m:ℝ)/T⌉₊) ≤ N)
    (B : ℝ) (hB : ∑ n ∈ S, Real.log (n:ℝ) ≤ B) :
    ∑ n ∈ S, vonMangoldt n
        * Real.exp (-(π*T^2*(Real.log (m:ℝ) - Real.log (n:ℝ))^2))
      ≤ 6144*((⌈2*(m:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log (m:ℝ)
        + Real.exp (-(π*T^2/64)) * B
        + ((Nat.sqrt (2*N) + 1 : ℕ):ℝ) * ((Nat.log 2 (2*N) : ℕ):ℝ)
            * Real.log ((2*N : ℕ):ℝ) := by
  classical
  set h : ℕ := ⌈2*(m:ℝ)/T⌉₊ with hh_def
  have hT0 : (0:ℝ) < T := by linarith
  have hm4 : (4:ℝ) ≤ (m:ℝ) := by nlinarith [hTm, hT]
  have hm1 : 1 ≤ m := by
    have : (1:ℝ) ≤ (m:ℝ) := by linarith
    exact_mod_cast this
  have hh2 : 2 ≤ h := ExpSums.two_le_ceil_scale T m hT hTm
  have hscale : 2*(m:ℝ) ≤ (h:ℝ)*T := ExpSums.ceil_scale_mul_le T m hT0
  have hL : Real.log (4*(m:ℝ)+2)/Real.log ((h:ℕ):ℝ) ≤ 6 :=
    ExpSums.log_ratio_ceil_scale_le T m hT hTm
  -- the maximal shell count, and the reach it guarantees
  obtain ⟨J, hfit, hmax, hwfit⟩ :=
    ExpSums.exists_shell_count m h hm1 (by omega)
  have hmIoc := hS hmS
  rw [Finset.mem_Ioc] at hmIoc
  have hsucc : (2^(J+1) - 1)*h = (2^J - 1)*h + 2^J*h :=
    ExpSums.dyadic_cut_succ h J
  have hJh : (2:ℕ)^J*h = (2^J - 1)*h + h := by
    have h1 : (1:ℕ) ≤ 2^J := Nat.one_le_two_pow
    have h2 : (2:ℕ)^J = (2^J - 1) + 1 := by omega
    calc (2:ℕ)^J*h = ((2^J - 1) + 1)*h := by rw [← h2]
      _ = (2^J - 1)*h + h := by ring
  have hreach : N ≤ 4*((2^J - 1)*h) := by omega
  -- flip the kernel to the orientation of `vonMangoldt_gaussian_block_le`
  have hflip : ∑ n ∈ S, vonMangoldt n
        * Real.exp (-(π*T^2*(Real.log (m:ℝ) - Real.log (n:ℝ))^2))
      = ∑ n ∈ S, vonMangoldt n
        * Real.exp (-(π*T^2*(Real.log (n:ℝ) - Real.log (m:ℝ))^2)) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 2
    ring
  rw [hflip]
  refine le_trans (vonMangoldt_gaussian_block_le T N m h J S hS hmS hN hh2
    hscale hfit hwfit hreach 6 hL B hB) ?_
  have hh0 : (0:ℝ) ≤ (h:ℝ) := Nat.cast_nonneg _
  have : 1024*(h:ℝ)*6 = 6144*(h:ℝ) := by ring
  linarith [this]

open ArithmeticFunction Finset Real in
/-- **The inner sum, uniformly over the block** (Track R, M0-kk): the
bound of `inner_sum_block_le` made independent of the centre `m`.

`intervalIntegral_vonMangoldt_mvt_le` needs a *single* `Q` valid for
every `m ∈ S` — the diagonal collapse produces one inner sum per centre
and they must all be bounded together.  Replacing `⌈2m/T⌉` by
`⌈4N/T⌉` and `log m` by `log 2N` costs only a factor of two in the main
term, since every centre lies in `(N, 2N]`, so the block is dyadic
precisely to make this uniformity cheap. -/
theorem inner_sum_block_uniform_le (T : ℝ) (N : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioc N (2*N)) (hN : 1 ≤ N)
    (hT : 2 ≤ T) (hTN : T^2 ≤ (N:ℝ))
    (hsmall : 2*(⌈4*(N:ℝ)/T⌉₊) ≤ N)
    (B : ℝ) (hB : ∑ n ∈ S, Real.log (n:ℝ) ≤ B) :
    ∀ m ∈ S, ∑ n ∈ S, vonMangoldt n
        * Real.exp (-(π*T^2*(Real.log (m:ℝ) - Real.log (n:ℝ))^2))
      ≤ 6144*((⌈4*(N:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log ((2*N : ℕ):ℝ)
        + Real.exp (-(π*T^2/64)) * B
        + ((Nat.sqrt (2*N) + 1 : ℕ):ℝ) * ((Nat.log 2 (2*N) : ℕ):ℝ)
            * Real.log ((2*N : ℕ):ℝ) := by
  classical
  intro m hmS
  have hT0 : (0:ℝ) < T := by linarith
  have hmIoc := hS hmS
  rw [Finset.mem_Ioc] at hmIoc
  have hNm : (N:ℝ) < (m:ℝ) := by exact_mod_cast hmIoc.1
  have hm2N : (m:ℝ) ≤ ((2*N : ℕ):ℝ) := by exact_mod_cast hmIoc.2
  have hTm : T^2 ≤ (m:ℝ) := by linarith
  -- the centre's scale is dominated by the block's
  have h2NR : ((2*N : ℕ):ℝ) = 2*(N:ℝ) := by push_cast; ring
  have h2N : (m:ℝ) ≤ 2*(N:ℝ) := by rw [← h2NR]; exact hm2N
  have hdiv : 2*(m:ℝ)/T ≤ 4*(N:ℝ)/T := by
    rw [div_le_div_iff₀ hT0 hT0]
    nlinarith [h2N, hT0]
  have hceil : (⌈2*(m:ℝ)/T⌉₊ : ℕ) ≤ ⌈4*(N:ℝ)/T⌉₊ := Nat.ceil_mono hdiv
  have hsmallm : 2*(⌈2*(m:ℝ)/T⌉₊) ≤ N := by omega
  refine le_trans (inner_sum_block_le T N m S hS hmS hN hT hTm hsmallm B hB) ?_
  -- upgrade the two `m`-dependent terms to their block-wide values
  have hceilR : ((⌈2*(m:ℝ)/T⌉₊ : ℕ):ℝ) ≤ ((⌈4*(N:ℝ)/T⌉₊ : ℕ):ℝ) := by
    exact_mod_cast hceil
  have hlogm : Real.log (m:ℝ) ≤ Real.log ((2*N : ℕ):ℝ) := by
    refine Real.log_le_log ?_ hm2N
    have : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg _
    linarith
  linarith

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **GHS Lemma 2.6 over a dyadic block** (Track R, M0-ll): the mean
value theorem with the inner sum discharged.

`intervalIntegral_vonMangoldt_mvt_le` reduced the analysis to a uniform
inner-sum bound `Q`; `inner_sum_block_uniform_le` supplies one.  The
composite constant `e^π·T·Q` has main term `e^π·T·6144·⌈4N/T⌉ ≈
24576·e^π·N`, which is `O(N)` — the `T` cancels against the `1/T` in the
scale, and that cancellation is the whole point of taking
`h = ⌈2m/T⌉`.  The remaining three terms are lower order.

With the coefficients `a(n)/n` this is Lemma 1 of the `κ = 1` paper,
whose right-hand side is `∑ |a(n)|²Λ(n)/n`. -/
theorem intervalIntegral_vonMangoldt_mvt_block_le (T : ℝ) (N : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (hS : S ⊆ Finset.Ioc N (2*N)) (hN : 1 ≤ N)
    (hT : 2 ≤ T) (hTN : T^2 ≤ (N:ℝ))
    (hsmall : 2*(⌈4*(N:ℝ)/T⌉₊) ≤ N)
    (B : ℝ) (hB : ∑ n ∈ S, Real.log (n:ℝ) ≤ B) :
    (∫ ξ in (-T)..T, ‖∑ n ∈ S, (a n * ((vonMangoldt n : ℝ) : ℂ))
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
      ≤ Real.exp π * T
          * (6144*((⌈4*(N:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log ((2*N : ℕ):ℝ)
              + Real.exp (-(π*T^2/64)) * B
              + ((Nat.sqrt (2*N) + 1 : ℕ):ℝ) * ((Nat.log 2 (2*N) : ℕ):ℝ)
                  * Real.log ((2*N : ℕ):ℝ))
        * ∑ m ∈ S, ‖a m‖^2 * vonMangoldt m :=
  intervalIntegral_vonMangoldt_mvt_le T (by linarith) S a _
    (inner_sum_block_uniform_le T N S hS hN hT hTN hsmall B hB)

open Finset in
/-- **The divisor swap** (Track R, N1): the hyperbola reindexing
`∑_{n≤x} ∑_{d ∣ n} = ∑_{d≤x} ∑_{m ≤ x/d}`, with `n = dm`.

This is the entry point to §3 of the `κ = 1` Halász paper, where
`log n = ∑_{d ∣ n} Λ(d)` is turned into a convolution over `(d, m)`.
Mathlib has the divisor identity but not this swap — `Nat.sum_div_divisors`
is the reflection `d ↔ n/d` *within a single* `n`, a different thing.

Natural-number division is exactly right on the right-hand side, since
`d·m ≤ x ↔ m ≤ x/d` for `d ≥ 1`. -/
theorem sum_divisors_swap {M : Type*} [AddCommMonoid M] (x : ℕ)
    (g : ℕ → ℕ → M) :
    ∑ n ∈ Finset.Icc 1 x, ∑ d ∈ n.divisors, g d n
      = ∑ d ∈ Finset.Icc 1 x, ∑ m ∈ Finset.Icc 1 (x/d), g d (d*m) := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => Sigma.mk p.2 (p.1 / p.2))
    (fun q => Sigma.mk (q.1 * q.2) q.1) ?_ ?_ ?_ ?_ ?_
  · -- the forward map lands in the target
    rintro ⟨n, d⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp
    obtain ⟨⟨hn1, hnx⟩, hdvd, hn0⟩ := hp
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
    have hdn : d ≤ n := Nat.le_of_dvd (by omega) hdvd
    simp only [Finset.mem_sigma, Finset.mem_Icc]
    exact ⟨⟨hd0, by omega⟩, (Nat.one_le_div_iff hd0).mpr hdn,
      Nat.div_le_div_right hnx⟩
  · -- and the backward map lands in the source
    rintro ⟨d, m⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hq
    obtain ⟨⟨hd1, hdx⟩, hm1, hmx⟩ := hq
    have hd0 : 0 < d := hd1
    have hdm : d * m ≤ x := by
      rw [mul_comm]
      exact (Nat.le_div_iff_mul_le hd0).mp hmx
    have hdm0 : 0 < d * m := Nat.mul_pos hd0 hm1
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
    exact ⟨⟨hdm0, hdm⟩, dvd_mul_right d m, by omega⟩
  · -- the two maps are mutually inverse
    rintro ⟨n, d⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp
    obtain ⟨⟨hn1, hnx⟩, hdvd, hn0⟩ := hp
    simp only [Nat.mul_div_cancel' hdvd]
  · rintro ⟨d, m⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hq
    obtain ⟨⟨hd1, hdx⟩, hm1, hmx⟩ := hq
    have hd0 : 0 < d := hd1
    simp only [Nat.mul_div_cancel_left m hd0]
  · -- and the summand is carried across
    rintro ⟨n, d⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp
    obtain ⟨⟨hn1, hnx⟩, hdvd, hn0⟩ := hp
    simp only [Nat.mul_div_cancel' hdvd]

open ArithmeticFunction Finset in
/-- **The log-weighted convolution** (Track R, N2): weighting by `log n`
turns any sum into a `Λ`-convolution,

  `∑_{n≤x} f(n)·log n = ∑_{d≤x} Λ(d)·∑_{m≤x/d} f(dm)`.

This is the first move of §3 of the `κ = 1` Halász paper, and the reason
the whole argument is driven by `log`: the identity
`log n = ∑_{d∣n} Λ(d)` is what converts a plain mean value into
something with arithmetic structure to exploit.  Restricting `d` to
primes (at a cost of `O(x)`) then produces the double convolution, and
iterating produces the triple one. -/
theorem sum_mul_log_eq (f : ℕ → ℝ) (x : ℕ) :
    ∑ n ∈ Finset.Icc 1 x, f n * Real.log (n:ℝ)
      = ∑ d ∈ Finset.Icc 1 x, vonMangoldt d
          * ∑ m ∈ Finset.Icc 1 (x/d), f (d*m) := by
  classical
  have hstep : ∀ n ∈ Finset.Icc 1 x, f n * Real.log (n:ℝ)
      = ∑ d ∈ n.divisors, f n * vonMangoldt d := by
    intro n _
    rw [← Finset.mul_sum, vonMangoldt_sum]
  rw [Finset.sum_congr rfl hstep,
    sum_divisors_swap x (fun d n => f n * vonMangoldt d)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

open Finset in
/-- **The log-over-square sum is bounded** (Track R, N3a):
`∑_{2≤n≤N} log n / n² ≤ 4`, uniformly in `N`.

This is what makes the prime-power error in §3 genuinely `O(x)` rather
than `O(x log x)`.  Bounding `Λ(d) ≤ log x` and counting proper prime
powers loses a logarithm and is fatal — the main term is itself
`O(x log x)`.  The convergent sum is needed, and it is available over
*all* integers, so no prime counting is required at all.

The proof telescopes: `log n ≤ 2(√n − 1)` from `log t ≤ t − 1` at
`t = √n`, and then `1/(n√n) ≤ 2(1/√(n−1) − 1/√n)` — which reduces,
after clearing denominators with `√n − √(n−1) = 1/(√n + √(n−1))`, to
`a² + ab ≤ 2b²` with `a² = b² − 1`. -/
theorem sum_log_div_sq_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 2 N, Real.log (n:ℝ) / (n:ℝ)^2
      ≤ 4 - 4/Real.sqrt (N:ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    set a : ℝ := Real.sqrt (N:ℝ) with ha_def
    set b : ℝ := Real.sqrt ((N:ℝ)+1) with hb_def
    have ha0 : (0:ℝ) < a := Real.sqrt_pos.mpr hN0
    have hb0 : (0:ℝ) < b := Real.sqrt_pos.mpr (by linarith)
    have hasq : a^2 = (N:ℝ) := Real.sq_sqrt hN0.le
    have hbsq : b^2 = (N:ℝ)+1 := Real.sq_sqrt (by linarith)
    have hab : a ≤ b := by nlinarith [hasq, hbsq, ha0, hb0]
    -- `log(N+1) ≤ 2b − 2`
    have hlogb : Real.log b ≤ b - 1 := Real.log_le_sub_one_of_pos hb0
    have hlogsplit : Real.log b = Real.log ((N:ℝ)+1) / 2 := by
      rw [hb_def]
      exact Real.log_sqrt (by linarith)
    have hlog : Real.log ((N:ℝ)+1) ≤ 2*b - 2 := by linarith
    -- the telescoping step
    have hkey : a^2 + a*b ≤ 2*b^2 := by nlinarith [hasq, hbsq, hab, ha0, hb0]
    have hprod : (b - a)*(a + b) = 1 := by nlinarith [hasq, hbsq]
    have hnum : Real.log ((N:ℝ)+1) / ((N:ℝ)+1)^2 ≤ 2/b^3 := by
      have hb4 : ((N:ℝ)+1)^2 = b^3*b := by
        have hbb : b^3*b = (b^2)^2 := by ring
        rw [hbb, hbsq]
      rw [hb4, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hlog, hb0, pow_pos hb0 3]
    have hrhs : 2/b^3 ≤ 4/a - 4/b := by
      have heq : 4/a - 4/b = 4*(b-a)/(a*b) := by field_simp
      rw [heq, div_le_div_iff₀ (by positivity) (by positivity)]
      have hab0 : (0:ℝ) < a + b := by linarith
      have h4 : (2*(a*b))*(a+b) ≤ (4*(b-a)*b^3)*(a+b) := by
        have hre : (4*(b-a)*b^3)*(a+b) = 4*b^3*((b-a)*(a+b)) := by ring
        rw [hre, hprod]
        nlinarith [mul_le_mul_of_nonneg_left hkey
          (show (0:ℝ) ≤ 2*b by positivity)]
      exact le_of_mul_le_mul_right h4 hab0
    have hstep : Real.log ((N:ℝ)+1) / ((N:ℝ)+1)^2 ≤ 4/a - 4/b := by
      linarith [hnum, hrhs]
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ N + 1)]
    have hcast2 : (((N+1 : ℕ)):ℝ) = (N:ℝ) + 1 := by push_cast; ring
    rw [hcast2]
    linarith [ih, hstep]

open ArithmeticFunction Finset in
/-- **The proper prime-power mass is bounded** (Track R, N3b):
`∑_{d ≤ x, d a proper prime power} Λ(d)/d ≤ 8`, uniformly in `x`.

This is what makes the first error term of §3 `O(x)` rather than
`O(x log x)` — and the latter would be fatal, since the main term is
itself of size `x log x`.

It cannot be obtained termwise from `sum_log_div_sq_le`: the summand is
`log p/p^k`, not `log d/d²`, and `d ↦ p` is far from injective.  The sum
must be regrouped over pairs `(p, k)` — the map `(p,k) ↦ p^k` *is*
injective on primes with `k ≥ 2`, by unique factorisation — after which
the geometric tail `∑_{k≥2} p^{−k} ≤ 2p^{−2}` reduces everything to
`∑_p log p/p²`, dominated by the integer sum. -/
theorem sum_vonMangoldt_div_properPrimePow_le (x : ℕ) :
    ∑ d ∈ (Finset.Icc 1 x).filter (fun d => IsPrimePow d ∧ ¬ d.Prime),
        vonMangoldt d / (d:ℝ) ≤ 8 := by
  classical
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  set K : ℕ := Nat.log 2 x + 1 with hK_def
  set Y : ℕ := Nat.sqrt x + 1 with hY_def
  set D : Finset (ℕ × ℕ) := Y.primesBelow ×ˢ Finset.Icc 2 K with hD_def
  set S := (Finset.Icc 1 x).filter (fun d => IsPrimePow d ∧ ¬ d.Prime)
    with hS_def
  have hnn : ∀ d : ℕ, (0:ℝ) ≤ vonMangoldt d / (d:ℝ) :=
    fun d => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
  -- every proper prime power is `p^k` with `p ≤ √x` and `2 ≤ k ≤ log₂x + 1`
  have hcover : S ⊆ Finset.image (fun pk : ℕ × ℕ => pk.1 ^ pk.2) D := by
    intro n hn
    rw [hS_def, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnx⟩, hpp, hnp⟩ := hn
    obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff n).mp hpp
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with hk1 | hk2
      · interval_cases k
        exact absurd (by rw [← hpk, pow_one]; exact hp) hnp
      · exact hk2
    have hpsqrt : p ≤ Nat.sqrt x := by
      refine Nat.le_sqrt.mpr ?_
      calc p*p = p^2 := by ring
        _ ≤ p^k := Nat.pow_le_pow_right hp.one_lt.le hk2
        _ = n := hpk
        _ ≤ x := hnx
    have hkK : k ≤ K := by
      have h2k : 2^k ≤ x := by
        calc 2^k ≤ p^k := Nat.pow_le_pow_left hp.two_le k
          _ = n := hpk
          _ ≤ x := hnx
      have hle : k ≤ Nat.log 2 x :=
        (Nat.le_log_iff_pow_le (by norm_num) (by omega : x ≠ 0)).mpr h2k
      omega
    rw [Finset.mem_image]
    refine ⟨(p, k), ?_, hpk⟩
    rw [hD_def, Finset.mem_product, Nat.mem_primesBelow, Finset.mem_Icc]
    exact ⟨⟨by omega, hp⟩, hk2, hkK⟩
  -- the parametrisation is injective, by unique factorisation
  have hinj : Set.InjOn (fun pk : ℕ × ℕ => pk.1 ^ pk.2) ↑D := by
    rintro ⟨p, k⟩ hu ⟨q, j⟩ hv heq
    simp only [hD_def, Finset.coe_product, Set.mem_prod, Finset.mem_coe,
      Nat.mem_primesBelow, Finset.mem_Icc] at hu hv
    obtain ⟨⟨_, hp⟩, hk2, _⟩ := hu
    obtain ⟨⟨_, hq⟩, hj2, _⟩ := hv
    simp only at heq
    have hpq : p = q := by
      have hdvd : p ∣ q ^ j := by
        rw [← heq]
        exact dvd_pow_self p (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd)
    subst hpq
    have hkj : k = j := Nat.pow_right_injective hp.two_le heq
    simp [hkj]
  -- pass to the pair sum
  have hstep : ∑ d ∈ S, vonMangoldt d / (d:ℝ)
      ≤ ∑ pk ∈ D, vonMangoldt (pk.1 ^ pk.2) / ((pk.1 ^ pk.2 : ℕ):ℝ) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hcover
      (fun i _ _ => hnn i)) ?_
    exact le_of_eq (Finset.sum_image hinj)
  refine le_trans hstep ?_
  rw [hD_def, Finset.sum_product]
  -- each prime contributes at most `2·log p/p²`
  have hrow : ∀ p ∈ Y.primesBelow,
      ∑ k ∈ Finset.Icc 2 K, vonMangoldt (p ^ k) / ((p ^ k : ℕ):ℝ)
        ≤ 2 * (Real.log (p:ℝ) / (p:ℝ)^2) := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.2.two_le
    have hp0 : (0:ℝ) < (p:ℝ) := by linarith
    have hr0 : (0:ℝ) ≤ 1/(p:ℝ) := by positivity
    have hr1 : 1/(p:ℝ) ≤ 1/2 := by
      rw [div_le_div_iff₀ hp0 (by norm_num)]
      linarith
    have hterm : ∀ k ∈ Finset.Icc 2 K,
        vonMangoldt (p ^ k) / ((p ^ k : ℕ):ℝ)
          = Real.log (p:ℝ) * ((1/(p:ℝ))^2 * (1/(p:ℝ))^(k-2)) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [vonMangoldt_apply_pow (by omega : k ≠ 0),
        vonMangoldt_apply_prime hp.2]
      have hcast : ((p ^ k : ℕ):ℝ) = (p:ℝ)^k := by push_cast; ring
      rw [hcast, ← pow_add]
      have hk2 : 2 + (k - 2) = k := by omega
      rw [hk2, div_pow, one_pow]
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.mul_sum]
    -- the geometric tail
    have hgeom : ∑ k ∈ Finset.Icc 2 K, (1/(p:ℝ))^(k-2) ≤ 2 := by
      have hinj2 : Set.InjOn (fun k => k - 2) ↑(Finset.Icc 2 K) := by
        intro a ha b hb h
        simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
        simp only at h
        omega
      have himg : (Finset.Icc 2 K).image (fun k => k - 2)
          ⊆ Finset.range (K+1) := by
        intro j hj
        rw [Finset.mem_image] at hj
        obtain ⟨k, hk, rfl⟩ := hj
        rw [Finset.mem_Icc] at hk
        exact Finset.mem_range.mpr (by omega)
      calc ∑ k ∈ Finset.Icc 2 K, (1/(p:ℝ))^(k-2)
          = ∑ j ∈ (Finset.Icc 2 K).image (fun k => k - 2), (1/(p:ℝ))^j :=
            (Finset.sum_image hinj2).symm
        _ ≤ ∑ j ∈ Finset.range (K+1), (1/(p:ℝ))^j :=
            Finset.sum_le_sum_of_subset_of_nonneg himg
              (fun i _ _ => by positivity)
        _ ≤ 2 := by
            have hg := geom_sum_mul (1/(p:ℝ)) (K+1)
            have hpow : (0:ℝ) ≤ (1/(p:ℝ))^(K+1) := by positivity
            have hS0 : (0:ℝ) ≤ ∑ j ∈ Finset.range (K+1), (1/(p:ℝ))^j :=
              Finset.sum_nonneg fun i _ => pow_nonneg hr0 i
            nlinarith [hg, hpow, hr1, hS0]
    have hlog0 : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_nonneg (by linarith)
    have hsq0 : (0:ℝ) ≤ (1/(p:ℝ))^2 := by positivity
    calc Real.log (p:ℝ) * ((1/(p:ℝ))^2
            * ∑ k ∈ Finset.Icc 2 K, (1/(p:ℝ))^(k-2))
        ≤ Real.log (p:ℝ) * ((1/(p:ℝ))^2 * 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hlog0
          exact mul_le_mul_of_nonneg_left hgeom hsq0
      _ = 2 * (Real.log (p:ℝ) / (p:ℝ)^2) := by
          field_simp
  refine le_trans (Finset.sum_le_sum hrow) ?_
  -- and the prime sum is dominated by the integer sum
  rw [← Finset.mul_sum]
  have hsub : Y.primesBelow ⊆ Finset.Icc 2 Y := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    rw [Finset.mem_Icc]
    exact ⟨hp.2.two_le, by omega⟩
  have h1 : ∑ p ∈ Y.primesBelow, Real.log (p:ℝ)/(p:ℝ)^2
      ≤ ∑ n ∈ Finset.Icc 2 Y, Real.log (n:ℝ)/(n:ℝ)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => div_nonneg (Real.log_natCast_nonneg i) (by positivity))
  have h2 := sum_log_div_sq_le Y (by omega)
  have h3 : (0:ℝ) ≤ 4/Real.sqrt (Y:ℝ) := by positivity
  linarith

open ArithmeticFunction Finset in
/-- **The convolution restricted to primes** (Track R, N3): for
`1`-bounded `f`,

  `∑_{n≤x} f(n)·log n = ∑_{p≤x} log p·∑_{m≤x/p} f(pm) + O(x)`,

with the error at most `8x`.

This is the first displayed identity of §3 of the `κ = 1` Halász paper.
The `Λ`-convolution of `sum_mul_log_eq` is supported on prime powers;
discarding the proper ones is what turns it into a genuine double
convolution over `(p, m)`.  The discard is affordable exactly because
`sum_vonMangoldt_div_properPrimePow_le` is `O(1)` — the inner sum is
trivially `≤ x/d` in absolute value, so the whole error is
`x·∑_{d proper} Λ(d)/d`. -/
theorem sum_mul_log_prime_restrict (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (x : ℕ) :
    |∑ n ∈ Finset.Icc 1 x, f n * Real.log (n:ℝ)
        - ∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime,
            Real.log (p:ℝ) * ∑ m ∈ Finset.Icc 1 (x/p), f (p*m)|
      ≤ 8 * (x:ℝ) := by
  classical
  rw [sum_mul_log_eq f x]
  -- split the convolution at the primes
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 x) Nat.Prime
    (fun d => vonMangoldt d * ∑ m ∈ Finset.Icc 1 (x/d), f (d*m))]
  have hprime : ∑ d ∈ (Finset.Icc 1 x).filter Nat.Prime,
        vonMangoldt d * ∑ m ∈ Finset.Icc 1 (x/d), f (d*m)
      = ∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime,
          Real.log (p:ℝ) * ∑ m ∈ Finset.Icc 1 (x/p), f (p*m) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    rw [vonMangoldt_apply_prime hp.2]
  rw [hprime, add_sub_cancel_left]
  -- what remains is supported on the proper prime powers
  have hsupp : ∑ d ∈ (Finset.Icc 1 x).filter (fun d => ¬ d.Prime),
        vonMangoldt d * ∑ m ∈ Finset.Icc 1 (x/d), f (d*m)
      = ∑ d ∈ (Finset.Icc 1 x).filter (fun d => IsPrimePow d ∧ ¬ d.Prime),
          vonMangoldt d * ∑ m ∈ Finset.Icc 1 (x/d), f (d*m) := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro d hd
      simp only [Finset.mem_filter] at hd ⊢
      exact ⟨hd.1, hd.2.2⟩
    · intro d hd hnot
      simp only [Finset.mem_filter] at hd hnot
      have hnp : ¬ IsPrimePow d := fun hpp => hnot ⟨hd.1, hpp, hd.2⟩
      rw [vonMangoldt_eq_zero_iff.mpr hnp, zero_mul]
  rw [hsupp]
  -- each inner sum is at most `x/d` in absolute value
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ d ∈ (Finset.Icc 1 x).filter
      (fun d => IsPrimePow d ∧ ¬ d.Prime),
      |vonMangoldt d * ∑ m ∈ Finset.Icc 1 (x/d), f (d*m)|
        ≤ (x:ℝ) * (vonMangoldt d / (d:ℝ)) := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hd1, hdx⟩, _, _⟩ := hd
    have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd1
    have hinner : |∑ m ∈ Finset.Icc 1 (x/d), f (d*m)| ≤ ((x/d : ℕ):ℝ) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      calc ∑ m ∈ Finset.Icc 1 (x/d), |f (d*m)|
          ≤ ∑ _m ∈ Finset.Icc 1 (x/d), (1:ℝ) :=
            Finset.sum_le_sum fun m _ => hf (d*m)
        _ = ((Finset.Icc 1 (x/d)).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ = ((x/d : ℕ):ℝ) := by rw [Nat.card_Icc]; norm_num
    have hcast : ((x/d : ℕ):ℝ) ≤ (x:ℝ)/(d:ℝ) := Nat.cast_div_le
    rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
    calc vonMangoldt d * |∑ m ∈ Finset.Icc 1 (x/d), f (d*m)|
        ≤ vonMangoldt d * ((x:ℝ)/(d:ℝ)) :=
          mul_le_mul_of_nonneg_left (le_trans hinner hcast) vonMangoldt_nonneg
      _ = (x:ℝ) * (vonMangoldt d / (d:ℝ)) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hx0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
  have hmass := sum_vonMangoldt_div_properPrimePow_le x
  nlinarith [hmass, hx0]

end MoltResearch
