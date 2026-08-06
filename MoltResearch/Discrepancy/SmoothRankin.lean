import MoltResearch.Discrepancy.RamareIdentity
import MoltResearch.Discrepancy.MertensFirst
import MoltResearch.Discrepancy.LogUniform
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

open Finset in
/-- **A Stirling-type lower bound** (Track R, N4a):
`∑_{n≤x} log n ≥ x·log x − x`.

The induction step is exactly `x·log(1 + 1/x) ≤ 1`, which is
`log t ≤ t − 1` at `t = (x+1)/x`.  No Stirling series is needed — only
the concavity of `log` in the crudest available form. -/
theorem sum_log_ge (x : ℕ) (hx : 1 ≤ x) :
    (x:ℝ) * Real.log (x:ℝ) - (x:ℝ)
      ≤ ∑ n ∈ Finset.Icc 1 x, Real.log (n:ℝ) := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih =>
    have hx0 : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ x + 1)]
    have hcast : (((x+1 : ℕ)):ℝ) = (x:ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hlog : Real.log ((x:ℝ)+1) - Real.log (x:ℝ) ≤ 1/(x:ℝ) := by
      have h1 : Real.log (((x:ℝ)+1)/(x:ℝ)) ≤ ((x:ℝ)+1)/(x:ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (by linarith) (by linarith)] at h1
      have h2 : ((x:ℝ)+1)/(x:ℝ) - 1 = 1/(x:ℝ) := by
        field_simp
        ring
      linarith [h1, h2]
    have hmul : (x:ℝ) * (Real.log ((x:ℝ)+1) - Real.log (x:ℝ)) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hlog hx0.le
      rwa [mul_one_div, div_self (ne_of_gt hx0)] at h
    nlinarith [ih, hmul]

open Finset in
/-- **The log-ratio mass** (Track R, N4b): `∑_{n≤x} log(x/n) ≤ x`.

This is what lets `log n` be traded for `log x` inside the mean value:
`S(x)·log x = ∑_{n≤x} f(n)·log n + ∑_{n≤x} f(n)·log(x/n)`, and the
second sum is `O(x)` regardless of `f`, since `|f| ≤ 1`. -/
theorem sum_log_ratio_mass_le (x : ℕ) (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 x, (Real.log (x:ℝ) - Real.log (n:ℝ)) ≤ (x:ℝ) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
  simp only [Nat.add_sub_cancel]
  linarith [sum_log_ge x hx]

open ArithmeticFunction Finset in
/-- **The mean value as a double convolution** (Track R, N5): for
`1`-bounded `f`,

  `S(x)·log x = ∑_{p≤x} log p·∑_{m≤x/p} f(pm) + O(x)`,

with error at most `9x`, where `S(x) = ∑_{n≤x} f(n)`.

This is the second displayed identity of §3 of the `κ = 1` Halász
paper, and the form the argument actually iterates.  Dividing by
`log x` gives `S(x) = (1/log x)·∑_{mp≤x} f(m)f(p)·log p + O(x/log x)`
— the mean value expressed as a convolution, at the cost of a factor
`log x` in the error.

The trade of `log n` for `log x` is free up to `O(x)`: the discrepancy
is `∑_{n≤x} f(n)·log(x/n)`, and `|f| ≤ 1` makes it at most
`∑_{n≤x} log(x/n) ≤ x` regardless of `f`. -/
theorem sum_mul_log_x_prime_restrict (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (x : ℕ) (hx : 1 ≤ x) :
    |(∑ n ∈ Finset.Icc 1 x, f n) * Real.log (x:ℝ)
        - ∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime,
            Real.log (p:ℝ) * ∑ m ∈ Finset.Icc 1 (x/p), f (p*m)|
      ≤ 9 * (x:ℝ) := by
  classical
  -- split `log x = log n + log(x/n)`
  have hsplit : (∑ n ∈ Finset.Icc 1 x, f n) * Real.log (x:ℝ)
      = (∑ n ∈ Finset.Icc 1 x, f n * Real.log (n:ℝ))
        + ∑ n ∈ Finset.Icc 1 x, f n * (Real.log (x:ℝ) - Real.log (n:ℝ)) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  -- the traded part is `O(x)` regardless of `f`
  have htail : |∑ n ∈ Finset.Icc 1 x,
      f n * (Real.log (x:ℝ) - Real.log (n:ℝ))| ≤ (x:ℝ) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ n ∈ Finset.Icc 1 x,
        |f n * (Real.log (x:ℝ) - Real.log (n:ℝ))|
          ≤ Real.log (x:ℝ) - Real.log (n:ℝ) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn.1
      have hnx : (n:ℝ) ≤ (x:ℝ) := by exact_mod_cast hn.2
      have hpos : (0:ℝ) ≤ Real.log (x:ℝ) - Real.log (n:ℝ) := by
        linarith [Real.log_le_log hn0 hnx]
      rw [abs_mul, abs_of_nonneg hpos]
      calc |f n| * (Real.log (x:ℝ) - Real.log (n:ℝ))
          ≤ 1 * (Real.log (x:ℝ) - Real.log (n:ℝ)) :=
            mul_le_mul_of_nonneg_right (hf n) hpos
        _ = Real.log (x:ℝ) - Real.log (n:ℝ) := one_mul _
    exact le_trans (Finset.sum_le_sum hterm) (sum_log_ratio_mass_le x hx)
  have hmain := sum_mul_log_prime_restrict f hf x
  rw [hsplit]
  have hre : (∑ n ∈ Finset.Icc 1 x, f n * Real.log (n:ℝ))
        + (∑ n ∈ Finset.Icc 1 x, f n * (Real.log (x:ℝ) - Real.log (n:ℝ)))
        - ∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime,
            Real.log (p:ℝ) * ∑ m ∈ Finset.Icc 1 (x/p), f (p*m)
      = ((∑ n ∈ Finset.Icc 1 x, f n * Real.log (n:ℝ))
          - ∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime,
              Real.log (p:ℝ) * ∑ m ∈ Finset.Icc 1 (x/p), f (p*m))
        + ∑ n ∈ Finset.Icc 1 x,
            f n * (Real.log (x:ℝ) - Real.log (n:ℝ)) := by ring
  rw [hre]
  refine le_trans (abs_add_le _ _) ?_
  linarith [hmain, htail]

open ArithmeticFunction Finset in
/-- **Discarding the small primes** (Track R, N6a): the part of the
double convolution with `p < y` costs only `x·(log y + 2)`.

§3 of the `κ = 1` paper drops the primes below `log⁴x` before iterating,
because the inner sum `∑_{m≤x/p}` must be long enough for the second
application of the identity to be meaningful.  The cost is
`x·∑_{p<y} log p/p`, which Mertens' first theorem keeps at
`x·(log y + 2)` — at `y ≈ log⁴x` that is `O(x·loglog x)`, and after the
division by `log x` it is the `O(x·loglog x/log x)` error of (3.1). -/
theorem prime_head_sum_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (x y : ℕ)
    (hy : 2 ≤ y) :
    |∑ p ∈ ((Finset.Icc 1 x).filter Nat.Prime).filter (fun p => p < y),
        Real.log (p:ℝ) * ∑ m ∈ Finset.Icc 1 (x/p), f (p*m)|
      ≤ (x:ℝ) * (Real.log (y:ℝ) + 2) := by
  classical
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ p ∈ ((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => p < y),
      |Real.log (p:ℝ) * ∑ m ∈ Finset.Icc 1 (x/p), f (p*m)|
        ≤ (x:ℝ) * (Real.log (p:ℝ) / (p:ℝ)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hp1, hpx⟩, hpp⟩, hpy⟩ := hp
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp1
    have hlog0 : (0:ℝ) ≤ Real.log (p:ℝ) :=
      Real.log_natCast_nonneg p
    have hinner : |∑ m ∈ Finset.Icc 1 (x/p), f (p*m)| ≤ ((x/p : ℕ):ℝ) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      calc ∑ m ∈ Finset.Icc 1 (x/p), |f (p*m)|
          ≤ ∑ _m ∈ Finset.Icc 1 (x/p), (1:ℝ) :=
            Finset.sum_le_sum fun m _ => hf (p*m)
        _ = ((Finset.Icc 1 (x/p)).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ = ((x/p : ℕ):ℝ) := by rw [Nat.card_Icc]; norm_num
    have hcast : ((x/p : ℕ):ℝ) ≤ (x:ℝ)/(p:ℝ) := Nat.cast_div_le
    rw [abs_mul, abs_of_nonneg hlog0]
    calc Real.log (p:ℝ) * |∑ m ∈ Finset.Icc 1 (x/p), f (p*m)|
        ≤ Real.log (p:ℝ) * ((x:ℝ)/(p:ℝ)) :=
          mul_le_mul_of_nonneg_left (le_trans hinner hcast) hlog0
      _ = (x:ℝ) * (Real.log (p:ℝ) / (p:ℝ)) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hsub : ((Finset.Icc 1 x).filter Nat.Prime).filter (fun p => p < y)
      ⊆ y.primesBelow := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    rw [Nat.mem_primesBelow]
    exact ⟨hp.2, hp.1.2⟩
  have hmass : ∑ p ∈ ((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => p < y), Real.log (p:ℝ) / (p:ℝ) ≤ Real.log (y:ℝ) + 2 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => div_nonneg (Real.log_natCast_nonneg i)
        (Nat.cast_nonneg _))) ?_
    exact sum_log_div_primesBelow_le_sharp y hy
  have hx0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_left hmass hx0

open ArithmeticFunction Finset in
/-- **Discarding the large primes** (Track R, N6b): the part with
`2p > x` costs only `(x+1)·log 4`.

Here the saving is structural rather than analytic: for `x/2 < p ≤ x`
the natural-number quotient `x/p` is exactly `1`, so each inner sum has
a single term and contributes at most `log p`.  What remains is
Chebyshev's `θ`-bound. -/
theorem prime_tail_sum_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (x : ℕ) :
    |∑ p ∈ ((Finset.Icc 1 x).filter Nat.Prime).filter (fun p => x < 2*p),
        Real.log (p:ℝ) * ∑ m ∈ Finset.Icc 1 (x/p), f (p*m)|
      ≤ ((x:ℝ)+1) * Real.log 4 := by
  classical
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ p ∈ ((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => x < 2*p),
      |Real.log (p:ℝ) * ∑ m ∈ Finset.Icc 1 (x/p), f (p*m)|
        ≤ Real.log (p:ℝ) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hp1, hpx⟩, hpp⟩, hpt⟩ := hp
    have hp0 : 0 < p := by omega
    have hge : 1 ≤ x / p := (Nat.one_le_div_iff hp0).mpr hpx
    have hlt : x / p < 2 := (Nat.div_lt_iff_lt_mul hp0).mpr (by omega)
    have hq : x / p = 1 := by omega
    have hlog0 : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
    rw [hq, abs_mul, abs_of_nonneg hlog0]
    have hone : |∑ m ∈ Finset.Icc 1 1, f (p*m)| ≤ 1 := by
      rw [show Finset.Icc 1 1 = ({1} : Finset ℕ) by rfl, Finset.sum_singleton]
      exact hf (p*1)
    calc Real.log (p:ℝ) * |∑ m ∈ Finset.Icc 1 1, f (p*m)|
        ≤ Real.log (p:ℝ) * 1 := mul_le_mul_of_nonneg_left hone hlog0
      _ = Real.log (p:ℝ) := mul_one _
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hsub : ((Finset.Icc 1 x).filter Nat.Prime).filter (fun p => x < 2*p)
      ⊆ (x+1).primesBelow := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    rw [Nat.mem_primesBelow]
    exact ⟨by omega, hp.1.2⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ => Real.log_natCast_nonneg i)) ?_
  have h := sum_log_primesBelow_le (x+1)
  have hcast : (((x+1 : ℕ)):ℝ) = (x:ℝ) + 1 := by push_cast; ring
  rwa [hcast] at h

open ArithmeticFunction Finset in
/-- **Factoring the convolution** (Track R, N7): for completely
multiplicative `f`, the inner sum of the double convolution splits,

  `∑_p log p·∑_{m≤x/p} f(pm) = ∑_p (log p·f(p))·∑_{m≤x/p} f(m)`.

This is what makes the convolution *iterable*: the inner sum is now a
mean value of `f` in its own right, over the shorter range `x/p`, so
the identity of `sum_mul_log_x_prime_restrict` can be applied to it a
second time to reach the triple convolution of §3.

For merely multiplicative `f` the same split holds up to the terms with
`p ∣ m`, of which there are at most `x/p²`; the resulting error is
`2x·∑_p log p/p²`, which `sum_log_div_sq_le` bounds by `8x` — the same
order as the discards already made. -/
theorem sum_prime_conv_factor (f : ℕ → ℝ) (hmul : ∀ a b, f (a*b) = f a * f b)
    (x : ℕ) :
    ∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime,
        Real.log (p:ℝ) * ∑ m ∈ Finset.Icc 1 (x/p), f (p*m)
      = ∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime,
          (Real.log (p:ℝ) * f p) * ∑ m ∈ Finset.Icc 1 (x/p), f m := by
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [hmul]; ring

open Finset in
/-- **A dyadic block of the prime log-harmonic mass** (Track R, N8a-i):
`∑_{2^i ≤ p < 2^{i+1}} log p/p ≤ 2·log 4`, an absolute constant.

Only Chebyshev's `θ`-bound is used: on the block `1/p ≤ 2^{−i}` while
`∑_{p<2^{i+1}} log p ≤ 2^{i+1}·log 4`, and the two powers cancel.  This
is what lets a *difference* of Mertens masses be bounded from above
without a matching lower bound for Mertens — which the repository does
not have. -/
theorem sum_log_div_dyadic_block_le (i : ℕ) :
    ∑ p ∈ (Finset.Ico (2^i) (2^(i+1))).filter Nat.Prime,
        Real.log (p:ℝ) / (p:ℝ) ≤ 2 * Real.log 4 := by
  classical
  have h2i : (0:ℝ) < (2:ℝ)^i := by positivity
  -- on the block, `1/p ≤ 2^{-i}`
  have hterm : ∀ p ∈ (Finset.Ico (2^i) (2^(i+1))).filter Nat.Prime,
      Real.log (p:ℝ) / (p:ℝ) ≤ Real.log (p:ℝ) / (2:ℝ)^i := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ico] at hp
    obtain ⟨⟨hlo, hhi⟩, hpp⟩ := hp
    have hpR : (2:ℝ)^i ≤ (p:ℝ) := by exact_mod_cast hlo
    refine div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) h2i hpR
  refine le_trans (Finset.sum_le_sum hterm) ?_
  -- and Chebyshev bounds the numerator
  rw [← Finset.sum_div]
  have hsub : (Finset.Ico (2^i) (2^(i+1))).filter Nat.Prime
      ⊆ (2^(i+1)).primesBelow := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ico] at hp
    rw [Nat.mem_primesBelow]
    exact ⟨hp.1.2, hp.2⟩
  have hcheb : ∑ p ∈ (Finset.Ico (2^i) (2^(i+1))).filter Nat.Prime,
      Real.log (p:ℝ) ≤ ((2^(i+1) : ℕ):ℝ) * Real.log 4 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun j _ _ => Real.log_natCast_nonneg j)) ?_
    exact sum_log_primesBelow_le (2^(i+1))
  rw [div_le_iff₀ h2i]
  have hcast : ((2^(i+1) : ℕ):ℝ) = 2 * (2:ℝ)^i := by push_cast; ring
  rw [hcast] at hcheb
  nlinarith [hcheb, h2i, Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)]

open Finset in
/-- **The prime log-harmonic mass over a range** (Track R, N8b):
`∑_{A ≤ p < B} log p/p` is at most `2·log 4` times the number of dyadic
blocks the range meets.

Fibering the primes over `i = ⌊log₂ p⌋` puts each fibre inside
`[2^i, 2^{i+1})`, where `sum_log_div_dyadic_block_le` gives an absolute
constant; the range meets at most `⌊log₂B⌋ − ⌊log₂A⌋ + 1` such blocks,
so the whole mass is `≪ log B − log A`.

This is a Mertens *difference* bound proved from an upper bound alone —
no lower bound for Mertens is needed, which matters because the
repository has none. -/
theorem sum_log_div_Ico_le (A B : ℕ) :
    ∑ p ∈ (Finset.Ico A B).filter Nat.Prime, Real.log (p:ℝ) / (p:ℝ)
      ≤ 2 * Real.log 4
          * (((Finset.Icc (Nat.log 2 A) (Nat.log 2 B)).card : ℕ) : ℝ) := by
  classical
  have hmaps : ∀ p ∈ (Finset.Ico A B).filter Nat.Prime,
      Nat.log 2 p ∈ Finset.Icc (Nat.log 2 A) (Nat.log 2 B) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ico] at hp
    rw [Finset.mem_Icc]
    exact ⟨Nat.log_mono_right hp.1.1, Nat.log_mono_right (le_of_lt hp.1.2)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ i ∈ Finset.Icc (Nat.log 2 A) (Nat.log 2 B),
      ∑ p ∈ ((Finset.Ico A B).filter Nat.Prime).filter
          (fun p => Nat.log 2 p = i), Real.log (p:ℝ) / (p:ℝ)
        ≤ 2 * Real.log 4 := by
    intro i _
    have hsub : ((Finset.Ico A B).filter Nat.Prime).filter
        (fun p => Nat.log 2 p = i)
        ⊆ (Finset.Ico (2^i) (2^(i+1))).filter Nat.Prime := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Ico] at hp ⊢
      obtain ⟨⟨⟨hA', hB'⟩, hpp⟩, hlog⟩ := hp
      have hp0 : p ≠ 0 := by
        have := hpp.one_lt
        omega
      refine ⟨⟨?_, ?_⟩, hpp⟩
      · rw [← hlog]
        exact Nat.pow_log_le_self 2 hp0
      · rw [← hlog]
        exact Nat.lt_pow_succ_log_self (by norm_num) p
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun j _ _ => div_nonneg (Real.log_natCast_nonneg j)
        (Nat.cast_nonneg _))) ?_
    exact sum_log_div_dyadic_block_le i
  refine le_trans (Finset.sum_le_sum hfib) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact le_of_eq (mul_comm _ _)

open Finset in
/-- **The Mertens difference bound** (Track R, N8c):
`∑_{A ≤ p < B} log p/p ≤ 4·(log B − log A) + 4·log 4`.

The block count of `sum_log_div_Ico_le` is turned into a logarithm by
the two defining inequalities of `Nat.log`: `2^{⌊log₂n⌋} ≤ n` bounds it
above and `n < 2^{⌊log₂n⌋+1}` bounds it below, so the count is
`(log B − log A)/log 2 + 2`, and `2·log 4/log 2 = 4`.

This is the Mertens difference in the form §3 uses it — for the
`loglog x` error of the iteration, and for `∑_{p ∈ P_k} log p/p ≪
e^{−k}·log x` in the trivial bound on `S_k`.  It is derived from
Chebyshev alone; no lower bound for Mertens is involved. -/
theorem sum_log_div_Ico_le_log (A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B) :
    ∑ p ∈ (Finset.Ico A B).filter Nat.Prime, Real.log (p:ℝ) / (p:ℝ)
      ≤ 4 * (Real.log (B:ℝ) - Real.log (A:ℝ)) + 4 * Real.log 4 := by
  classical
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hA0 : (0:ℝ) < (A:ℝ) := by exact_mod_cast hA
  have hB1 : 1 ≤ B := le_trans hA hAB
  have hB0 : (0:ℝ) < (B:ℝ) := by exact_mod_cast hB1
  have hmono : Nat.log 2 A ≤ Nat.log 2 B := Nat.log_mono_right hAB
  -- the number of dyadic blocks met
  have hcard : (((Finset.Icc (Nat.log 2 A) (Nat.log 2 B)).card : ℕ) : ℝ)
      = (Nat.log 2 B : ℝ) + 1 - (Nat.log 2 A : ℝ) := by
    rw [Nat.card_Icc, Nat.cast_sub (by omega)]
    push_cast
    ring
  -- `⌊log₂B⌋·log 2 ≤ log B`
  have hupper : (Nat.log 2 B : ℝ) * Real.log 2 ≤ Real.log (B:ℝ) := by
    have h1 : (2:ℕ)^(Nat.log 2 B) ≤ B := Nat.pow_log_le_self 2 (by omega)
    have h2 : ((2:ℝ))^(Nat.log 2 B) ≤ (B:ℝ) := by exact_mod_cast h1
    have h3 := Real.log_le_log (by positivity) h2
    rwa [Real.log_pow] at h3
  -- `log A ≤ (⌊log₂A⌋ + 1)·log 2`
  have hlower : Real.log (A:ℝ) ≤ ((Nat.log 2 A : ℝ) + 1) * Real.log 2 := by
    have h1 : A < 2^(Nat.log 2 A + 1) := Nat.lt_pow_succ_log_self (by norm_num) A
    have h2 : (A:ℝ) ≤ ((2:ℝ))^(Nat.log 2 A + 1) := by exact_mod_cast h1.le
    have h3 := Real.log_le_log hA0 h2
    rw [Real.log_pow] at h3
    push_cast at h3
    linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    have h : (4:ℝ) = 2^(2:ℕ) := by norm_num
    rw [h, Real.log_pow]
    push_cast
    ring
  refine le_trans (sum_log_div_Ico_le A B) ?_
  rw [hcard, hlog4]
  nlinarith [hupper, hlower, hlog2]

open Finset in
/-- **A block of the iteration error** (Track R, N9a): the primes with
`x/p` in a fixed dyadic range carry log-harmonic mass at most
`12·log 2`, an absolute constant.

The block is `(x/2^{j+1}, x/2^j]`, whose endpoints differ by a factor
of two — and, pleasingly, natural-number division only helps: since
`x/2^{j+1} = (x/2^j)/2`, the shifted endpoints satisfy
`x/2^j + 1 ≤ 2·(x/2^{j+1} + 1)` exactly, so the log difference is at
most `log 2` with no error term at all.  `sum_log_div_Ico_le_log` then
gives `4·log 2 + 4·log 4 = 12·log 2`. -/
theorem block_mass_le (x j : ℕ) :
    ∑ p ∈ (Finset.Ico (x/2^(j+1) + 1) (x/2^j + 1)).filter Nat.Prime,
        Real.log (p:ℝ) / (p:ℝ) ≤ 12 * Real.log 2 := by
  classical
  have hdiv : x/2^(j+1) = (x/2^j)/2 := by
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
  rw [hdiv]
  generalize hq : x/2^j = q
  have hAB : q/2 + 1 ≤ q + 1 := by omega
  have hfac : q + 1 ≤ 2*(q/2 + 1) := by omega
  refine le_trans (sum_log_div_Ico_le_log (q/2 + 1) (q + 1) (by omega) hAB) ?_
  -- the endpoints differ by at most a factor of two
  have hpos : (0:ℝ) < ((q/2 + 1 : ℕ):ℝ) := by
    have : (0:ℕ) < q/2 + 1 := by omega
    exact_mod_cast this
  have hcast : ((q + 1 : ℕ):ℝ) ≤ 2 * ((q/2 + 1 : ℕ):ℝ) := by
    have h : ((q + 1 : ℕ):ℝ) ≤ ((2*(q/2 + 1) : ℕ):ℝ) := by exact_mod_cast hfac
    push_cast at h ⊢
    linarith
  have hlogdiff : Real.log ((q + 1 : ℕ):ℝ) - Real.log ((q/2 + 1 : ℕ):ℝ)
      ≤ Real.log 2 := by
    have h1 : Real.log ((q + 1 : ℕ):ℝ) ≤ Real.log (2 * ((q/2 + 1 : ℕ):ℝ)) :=
      Real.log_le_log (by positivity) hcast
    rw [Real.log_mul (by norm_num) (ne_of_gt hpos)] at h1
    linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    have h : (4:ℝ) = 2^(2:ℕ) := by norm_num
    rw [h, Real.log_pow]
    push_cast
    ring
  rw [hlog4]
  linarith

open Finset in
/-- **The iteration error, fibered** (Track R, N9b):

  `∑_{p ≤ x/2} log p/(p·log(x/p)) ≤ 12·∑_{1 ≤ j ≤ ⌊log₂x⌋} 1/j`.

Fibering over `j = ⌊log₂(x/p)⌋` sends each prime into the dyadic block
of `block_mass_le`, where the mass is `12·log 2`, while the denominator
is at least `j·log 2` — so block `j` contributes `12/j` and the total is
a harmonic sum, i.e. `O(log log x)`.

Restricting to `p ≤ x/2` does double duty: it is what §3 needs
mathematically, and it forces `x/p ≥ 2`, hence `j ≥ 1`, so the weights
`1/(j·log 2)` never divide by zero.

The harmonic sum is left symbolic; bounding it by `1 + log⌊log₂x⌋` is a
separate step. -/
theorem sum_log_div_mul_log_ratio_le (x : ℕ) :
    ∑ p ∈ (Finset.Icc 1 (x/2)).filter Nat.Prime,
        Real.log (p:ℝ) / ((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ)))
      ≤ 12 * ∑ j ∈ Finset.Icc 1 (Nat.log 2 x), 1/(j:ℝ) := by
  classical
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- every prime in range lands in a block with `1 ≤ j ≤ ⌊log₂x⌋`
  have hmaps : ∀ p ∈ (Finset.Icc 1 (x/2)).filter Nat.Prime,
      Nat.log 2 (x/p) ∈ Finset.Icc 1 (Nat.log 2 x) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hp1, hpx⟩, hpp⟩ := hp
    have hp0 : 0 < p := by omega
    have h2 : 2 ≤ x/p := by
      rw [Nat.le_div_iff_mul_le hp0]
      have : p * 2 ≤ x := by
        have := Nat.le_div_iff_mul_le (k := 2) (by norm_num) |>.mp hpx
        omega
      omega
    rw [Finset.mem_Icc]
    refine ⟨Nat.log_pos (by norm_num) h2, ?_⟩
    exact Nat.log_mono_right (Nat.div_le_self x p)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hmid : ∀ j ∈ Finset.Icc 1 (Nat.log 2 x),
      ∑ p ∈ ((Finset.Icc 1 (x/2)).filter Nat.Prime).filter
          (fun p => Nat.log 2 (x/p) = j),
          Real.log (p:ℝ) / ((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ)))
        ≤ 12 * (1/(j:ℝ)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hj0 : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj.1
    have hjlog : (0:ℝ) < (j:ℝ) * Real.log 2 := by positivity
    have hsub : ((Finset.Icc 1 (x/2)).filter Nat.Prime).filter
        (fun p => Nat.log 2 (x/p) = j)
        ⊆ (Finset.Ico (x/2^(j+1) + 1) (x/2^j + 1)).filter Nat.Prime := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico] at hp ⊢
      obtain ⟨⟨⟨hp1, hpx⟩, hpp⟩, hlogeq⟩ := hp
      have hp0 : 0 < p := by omega
      have hlo : 2^j ≤ x/p := by
        rw [← hlogeq]
        exact Nat.pow_log_le_self 2 (by
          intro h
          rw [h] at hlogeq
          simp at hlogeq
          omega)
      have hhi : x/p < 2^(j+1) := by
        rw [← hlogeq]
        exact Nat.lt_pow_succ_log_self (by norm_num) _
      refine ⟨⟨?_, ?_⟩, hpp⟩
      · -- `x/2^{j+1} < p`
        by_contra hcon
        push_neg at hcon
        have hple : p ≤ x/2^(j+1) := by omega
        have hmul := (Nat.le_div_iff_mul_le (k := 2^(j+1)) (by positivity)).mp hple
        have hcontra : 2^(j+1) ≤ x/p := by
          rw [Nat.le_div_iff_mul_le hp0, mul_comm]
          exact hmul
        omega
      · -- `p ≤ x/2^j`
        have hmul2 := (Nat.le_div_iff_mul_le hp0).mp hlo
        have hle : p ≤ x/2^j := by
          rw [Nat.le_div_iff_mul_le (by positivity), mul_comm]
          exact hmul2
        omega
    have hterm : ∀ p ∈ ((Finset.Icc 1 (x/2)).filter Nat.Prime).filter
        (fun p => Nat.log 2 (x/p) = j),
        Real.log (p:ℝ) / ((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ)))
          ≤ (Real.log (p:ℝ) / (p:ℝ)) * (1/((j:ℝ) * Real.log 2)) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨⟨⟨hp1, hpx⟩, hpp⟩, hlogeq⟩ := hp
      have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp1
      have hlo : 2^j ≤ x/p := by
        rw [← hlogeq]
        refine Nat.pow_log_le_self 2 ?_
        intro h
        rw [h] at hlogeq
        simp at hlogeq
        omega
      -- `(x:ℝ)/p ≥ (x/p : ℕ) ≥ 2^j`
      have hcast : ((x/p : ℕ):ℝ) ≤ (x:ℝ)/(p:ℝ) := Nat.cast_div_le
      have hpow : ((2:ℝ))^j ≤ ((x/p : ℕ):ℝ) := by exact_mod_cast hlo
      have hden : (j:ℝ) * Real.log 2 ≤ Real.log ((x:ℝ)/(p:ℝ)) := by
        have h1 : Real.log (((2:ℝ))^j) ≤ Real.log ((x:ℝ)/(p:ℝ)) :=
          Real.log_le_log (by positivity) (le_trans hpow hcast)
        rwa [Real.log_pow] at h1
      have hlogp : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
      have hlogpos : (0:ℝ) < Real.log ((x:ℝ)/(p:ℝ)) := lt_of_lt_of_le hjlog hden
      have heq : Real.log (p:ℝ) / ((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ)))
          = (Real.log (p:ℝ)/(p:ℝ)) * (1/Real.log ((x:ℝ)/(p:ℝ))) := by
        field_simp
      rw [heq]
      refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hlogp hp0.le)
      rw [div_le_div_iff₀ hlogpos hjlog]
      linarith [hden]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_mul]
    have hmass := block_mass_le x j
    have hblock : ∑ p ∈ ((Finset.Icc 1 (x/2)).filter Nat.Prime).filter
        (fun p => Nat.log 2 (x/p) = j), Real.log (p:ℝ) / (p:ℝ)
        ≤ 12 * Real.log 2 := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun i _ _ => div_nonneg (Real.log_natCast_nonneg i)
          (Nat.cast_nonneg _))) hmass
    have hinv : (0:ℝ) ≤ 1/((j:ℝ) * Real.log 2) := by positivity
    calc (∑ p ∈ ((Finset.Icc 1 (x/2)).filter Nat.Prime).filter
            (fun p => Nat.log 2 (x/p) = j), Real.log (p:ℝ) / (p:ℝ))
          * (1/((j:ℝ) * Real.log 2))
        ≤ (12 * Real.log 2) * (1/((j:ℝ) * Real.log 2)) :=
          mul_le_mul_of_nonneg_right hblock hinv
      _ = 12 * (1/(j:ℝ)) := by field_simp
  refine le_trans (Finset.sum_le_sum hmid) ?_
  rw [Finset.mul_sum]

open Finset in
/-- **The inner Mertens cancellation** (Track R, N10): the inner prime
sum of the triple convolution cancels the `1/log(x/p)` weight,

  `(log p/(p·log(x/p)))·∑_{q ≤ x/p} log q/q ≤ 4·log p/p`.

This is the step that makes the trivial bound on `S_k` come out at
`e^{−k}·x·log x`.  The inner sum is `≪ log(x/p)` by Mertens, exactly
matching the denominator produced when the convolution was iterated, so
what survives is a bare `∑_{p ∈ P_k} log p/p` — which
`sum_log_div_Ico_le_log` then bounds by the length of the range in
logarithmic scale, and `P_k` was chosen to make that `e^{−k}·log x`. -/
theorem inner_mertens_cancel (x p : ℕ) (hp : 1 ≤ p) (h2 : 2*p ≤ x) :
    (Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
        * (∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ))
      ≤ 4 * (Real.log (p:ℝ)/(p:ℝ)) := by
  classical
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
  have hquot : (2:ℝ) ≤ (x:ℝ)/(p:ℝ) := by
    rw [le_div_iff₀ hp0]
    have : ((2*p : ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast h2
    push_cast at this
    linarith
  have hlogpos : (0:ℝ) < Real.log ((x:ℝ)/(p:ℝ)) :=
    Real.log_pos (by linarith)
  -- Mertens on the inner range, then compare with the real quotient
  have hcast : ((x/p : ℕ):ℝ) ≤ (x:ℝ)/(p:ℝ) := Nat.cast_div_le
  have hinner : ∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ)
      ≤ 4 * Real.log ((x:ℝ)/(p:ℝ)) := by
    refine le_trans (sum_log_div_primesBelow_le (x/p)) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rcases Nat.eq_zero_or_pos (x/p) with h0 | h0
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      linarith
    · refine Real.log_le_log ?_ hcast
      exact_mod_cast h0
  have hlogp : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
  have hcoef : (0:ℝ) ≤ Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))) :=
    div_nonneg hlogp (by positivity)
  calc (Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
        * (∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ))
      ≤ (Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
          * (4 * Real.log ((x:ℝ)/(p:ℝ))) :=
        mul_le_mul_of_nonneg_left hinner hcoef
    _ = 4 * (Real.log (p:ℝ)/(p:ℝ)) := by
        field_simp

open Finset in
/-- **The `S_k` trivial mass** (Track R, N11): summing the inner
cancellation over a prime range,

  `∑_{A ≤ p < B} (log p/(p·log(x/p)))·∑_{q ≤ x/p} log q/q
     ≤ 16·(log B − log A) + 16·log 4`.

This is the trivial bound on `S_k` reduced to its arithmetic core.
`inner_mertens_cancel` removes the `1/log(x/p)` weight the iteration
left behind, and `sum_log_div_Ico_le_log` measures what survives by the
logarithmic length of the range.

At `P_k = (x^{1−e^{1−k}}, x^{1−e^{−k}}]` the length is
`(e^{1−k} − e^{−k})·log x = (e−1)·e^{−k}·log x`, so the bound is
`≪ e^{−k}·log x` — which, against the `x` from the innermost count, is
the `|S_k| ≪ e^{−k}·x·log x` of §3.  Summing over `k` then converges
geometrically, which is what lets all but `O(log(log x/L))` of the
blocks be discarded. -/
theorem Sk_trivial_mass_le (x A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B)
    (hB : 2*B ≤ x) :
    ∑ p ∈ (Finset.Ico A B).filter Nat.Prime,
        (Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
          * (∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ))
      ≤ 16 * (Real.log (B:ℝ) - Real.log (A:ℝ)) + 16 * Real.log 4 := by
  classical
  have hterm : ∀ p ∈ (Finset.Ico A B).filter Nat.Prime,
      (Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
          * (∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ))
        ≤ 4 * (Real.log (p:ℝ)/(p:ℝ)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ico] at hp
    obtain ⟨⟨hAp, hpB⟩, hpp⟩ := hp
    have hp1 : 1 ≤ p := hpp.one_lt.le
    exact inner_mertens_cancel x p hp1 (by omega)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hmass := sum_log_div_Ico_le_log A B hA hAB
  linarith [hmass]

open Finset in
/-- **The triple convolution** (Track R, N12): the object §3 of the
`κ = 1` Halász paper arrives at after applying the log-identity twice,

  `∑_{p ∈ P} (f(p)·log p/log(x/p))·∑_{q < x/p} f(q)·log q·∑_{n ≤ x/pq} f(n)`.

The outer weight `1/log(x/p)` is what the second application produces;
the inner double sum is a mean value of `f` over the shorter range
`x/p`.  Restricting `p` to a block `P` is how §3 splits the sum before
bounding each piece. -/
noncomputable def tripleConv (f : ℕ → ℝ) (x : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
    * ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
        * ∑ n ∈ Finset.Icc 1 (x/(p*q)), f n

open Finset in
/-- **The trivial bound on a block** (Track R, N12): bounding every
factor by its modulus turns the triple convolution into `x` times the
arithmetic mass of `Sk_trivial_mass_le`,

  `|tripleConv f x P| ≤ x·(16·(log B − log A) + 16·log 4)`.

This is §3's trivial estimate on `S_k`.  At `P_k` the logarithmic
length is `(e−1)·e^{−k}·log x`, so the bound is `≪ e^{−k}·x·log x` and
summing over `k` converges geometrically — which is what allows all but
boundedly many blocks to be discarded. -/
theorem norm_tripleConv_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (x A B : ℕ)
    (hA : 1 ≤ A) (hAB : A ≤ B) (hB : 2*B ≤ x) :
    |tripleConv f x ((Finset.Ico A B).filter Nat.Prime)|
      ≤ (x:ℝ) * (16 * (Real.log (B:ℝ) - Real.log (A:ℝ)) + 16 * Real.log 4) := by
  classical
  have hx0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
  rw [tripleConv]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  -- each outer term is at most `x` times its arithmetic weight
  have hterm : ∀ p ∈ (Finset.Ico A B).filter Nat.Prime,
      |(Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
        * ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
            * ∑ n ∈ Finset.Icc 1 (x/(p*q)), f n|
      ≤ (x:ℝ) * ((Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
          * ∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ico] at hp
    obtain ⟨⟨hAp, hpB⟩, hpp⟩ := hp
    have hp1 : 1 ≤ p := hpp.one_lt.le
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp1
    have h2p : 2*p ≤ x := by omega
    have hquot : (2:ℝ) ≤ (x:ℝ)/(p:ℝ) := by
      rw [le_div_iff₀ hp0]
      have hc : ((2*p : ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast h2p
      push_cast at hc
      linarith
    have hlogpos : (0:ℝ) < Real.log ((x:ℝ)/(p:ℝ)) := Real.log_pos (by linarith)
    have hlogp : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
    -- the innermost sum is at most the length of its range
    have hinner : ∀ q : ℕ, |∑ n ∈ Finset.Icc 1 (x/(p*q)), f n|
        ≤ ((x/(p*q) : ℕ):ℝ) := by
      intro q
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      calc ∑ n ∈ Finset.Icc 1 (x/(p*q)), |f n|
          ≤ ∑ _n ∈ Finset.Icc 1 (x/(p*q)), (1:ℝ) :=
            Finset.sum_le_sum fun n _ => hf n
        _ = ((Finset.Icc 1 (x/(p*q))).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ = ((x/(p*q) : ℕ):ℝ) := by rw [Nat.card_Icc]; norm_num
    -- so the middle sum is at most `(x/p)·∑ log q/q`
    have hmid : |∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
          * ∑ n ∈ Finset.Icc 1 (x/(p*q)), f n|
        ≤ ((x:ℝ)/(p:ℝ)) * ∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun q hq => ?_
      rw [Nat.mem_primesBelow] at hq
      have hq1 : 1 ≤ q := hq.2.one_lt.le
      have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq1
      have hlogq : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_natCast_nonneg q
      have hcastq : ((x/(p*q) : ℕ):ℝ) ≤ (x:ℝ)/((p:ℝ)*(q:ℝ)) := by
        have h := Nat.cast_div_le (α := ℝ) (m := x) (n := p*q)
        push_cast at h
        exact h
      rw [abs_mul, abs_mul, abs_of_nonneg hlogq]
      calc Real.log (q:ℝ) * |f q| * |∑ n ∈ Finset.Icc 1 (x/(p*q)), f n|
          ≤ Real.log (q:ℝ) * 1 * ((x:ℝ)/((p:ℝ)*(q:ℝ))) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left (hf q) hlogq)
              (le_trans (hinner q) hcastq) (abs_nonneg _) (by positivity)
        _ = (x:ℝ)/(p:ℝ) * (Real.log (q:ℝ)/(q:ℝ)) := by
            field_simp
    rw [abs_mul]
    have houter : |Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ))|
        ≤ Real.log (p:ℝ) / Real.log ((x:ℝ)/(p:ℝ)) := by
      rw [abs_div, abs_mul, abs_of_nonneg hlogp,
        abs_of_nonneg hlogpos.le]
      refine div_le_div_of_nonneg_right ?_ hlogpos.le
      calc Real.log (p:ℝ) * |f p| ≤ Real.log (p:ℝ) * 1 :=
            mul_le_mul_of_nonneg_left (hf p) hlogp
        _ = Real.log (p:ℝ) := mul_one _
    have hsum0 : (0:ℝ) ≤ ∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ) :=
      Finset.sum_nonneg fun q _ =>
        div_nonneg (Real.log_natCast_nonneg q) (Nat.cast_nonneg _)
    calc |Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ))|
          * |∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
              * ∑ n ∈ Finset.Icc 1 (x/(p*q)), f n|
        ≤ (Real.log (p:ℝ) / Real.log ((x:ℝ)/(p:ℝ)))
            * (((x:ℝ)/(p:ℝ)) * ∑ q ∈ (x/p).primesBelow,
                Real.log (q:ℝ)/(q:ℝ)) := by
          refine mul_le_mul houter hmid (abs_nonneg _) ?_
          exact div_nonneg hlogp hlogpos.le
      _ = (x:ℝ) * ((Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
            * ∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ)) := by
          field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (Sk_trivial_mass_le x A B hA hAB hB) hx0

open Finset in
/-- **The geometric tail of the block decomposition** (Track R, N13):
`∑_{k > K} e^{−k} ≤ e^{−K}`.

§3 bounds block `k` of the triple convolution by `≪ e^{−k}·x·log x`, so
discarding every block beyond `K` costs `≪ e^{−K}·x·log x`.  This is
what makes the decomposition finite in practice: only
`O(log(log x/L))` blocks need to be treated analytically, and the rest
vanish geometrically.

The constant works out because `e^{−1} < 1/2`, so the tail
`e^{−(K+1)}/(1 − e^{−1}) = e^{−K}/(e−1)` is already below `e^{−K}`. -/
theorem sum_exp_neg_tail_le (K M : ℕ) :
    ∑ k ∈ Finset.Icc (K+1) M, Real.exp (-(k:ℝ)) ≤ Real.exp (-(K:ℝ)) := by
  classical
  set r : ℝ := Real.exp (-1) with hr_def
  have hr0 : (0:ℝ) < r := Real.exp_pos _
  have hrhalf : r ≤ 1/2 := by
    have he : (2:ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hkey : r * Real.exp 1 = 1 := by
      rw [hr_def, ← Real.exp_add]
      norm_num
    nlinarith [hkey, he, hr0]
  have hr1 : (0:ℝ) < 1 - r := by linarith
  -- rewrite each term as a power of `r`
  have hpow : ∀ k : ℕ, Real.exp (-(k:ℝ)) = r^k := by
    intro k
    rw [hr_def, ← Real.exp_nat_mul]
    congr 1
    ring
  simp only [hpow]
  -- factor out `r^(K+1)` and bound the remaining geometric sum
  have hsplit : ∑ k ∈ Finset.Icc (K+1) M, r^k
      = r^(K+1) * ∑ k ∈ Finset.Icc (K+1) M, r^(k-(K+1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    rw [← pow_add]
    congr 1
    omega
  have hinj : Set.InjOn (fun k => k - (K+1)) ↑(Finset.Icc (K+1) M) := by
    intro a ha b hb h
    simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
    simp only at h
    omega
  have himg : (Finset.Icc (K+1) M).image (fun k => k - (K+1))
      ⊆ Finset.range (M+1) := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨k, hk, rfl⟩ := hj
    rw [Finset.mem_Icc] at hk
    exact Finset.mem_range.mpr (by omega)
  have hgeom : ∑ k ∈ Finset.Icc (K+1) M, r^(k-(K+1)) ≤ 1/(1-r) := by
    calc ∑ k ∈ Finset.Icc (K+1) M, r^(k-(K+1))
        = ∑ j ∈ (Finset.Icc (K+1) M).image (fun k => k - (K+1)), r^j :=
          (Finset.sum_image hinj).symm
      _ ≤ ∑ j ∈ Finset.range (M+1), r^j :=
          Finset.sum_le_sum_of_subset_of_nonneg himg
            (fun i _ _ => by positivity)
      _ ≤ 1/(1-r) := by
          have hg := geom_sum_mul r (M+1)
          have hpw : (0:ℝ) ≤ r^(M+1) := by positivity
          have hS0 : (0:ℝ) ≤ ∑ j ∈ Finset.range (M+1), r^j :=
            Finset.sum_nonneg fun i _ => pow_nonneg hr0.le i
          rw [le_div_iff₀ hr1]
          nlinarith [hg, hpw, hS0]
  rw [hsplit]
  have hpK : r^(K+1) = r^K * r := by ring
  calc r^(K+1) * ∑ k ∈ Finset.Icc (K+1) M, r^(k-(K+1))
      ≤ r^(K+1) * (1/(1-r)) :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = r^K * (r/(1-r)) := by rw [hpK]; ring
    _ ≤ r^K * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [div_le_one hr1]
        linarith
    _ = r^K := mul_one _

/-- The lower endpoint of §3's `k`-th prime block, `⌈x^{1−e^{1−k}}⌉`. -/
noncomputable def blockLo (x k : ℕ) : ℕ :=
  ⌈(x:ℝ) ^ (1 - Real.exp (1 - (k:ℝ)))⌉₊

/-- The upper endpoint of §3's `k`-th prime block, `⌈x^{1−e^{−k}}⌉`. -/
noncomputable def blockHi (x k : ℕ) : ℕ :=
  ⌈(x:ℝ) ^ (1 - Real.exp (-(k:ℝ)))⌉₊

open Finset in
/-- **The block endpoints are ordered and non-degenerate** (Track R,
N14): `1 ≤ blockLo x k ≤ blockHi x k`.

The exponents `1 − e^{1−k} ≤ 1 − e^{−k}` are increasing in `k`, and
`x ≥ 1` makes `rpow` monotone in the exponent. -/
theorem blockLo_le_blockHi (x k : ℕ) (hx : 1 ≤ x) :
    1 ≤ blockLo x k ∧ blockLo x k ≤ blockHi x k := by
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hexp : Real.exp (-(k:ℝ)) ≤ Real.exp (1 - (k:ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hmono : (x:ℝ) ^ (1 - Real.exp (1 - (k:ℝ)))
      ≤ (x:ℝ) ^ (1 - Real.exp (-(k:ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  constructor
  · rw [blockLo, Nat.one_le_ceil_iff]
    exact Real.rpow_pos_of_pos (by linarith) _
  · rw [blockLo, blockHi]
    exact Nat.ceil_mono hmono

open Finset in
/-- **The block has logarithmic length `(e−1)e^{−k}·log x`** (Track R,
N14):

  `log(blockHi x k) − log(blockLo x k) ≤ (e−1)·e^{−k}·log x + log 2`.

This is the geometry that makes §3's partition work.  Fed to
`norm_tripleConv_le`, it turns the trivial bound into
`≪ e^{−k}·x·log x` — geometric in `k`, so `sum_exp_neg_tail_le`
discards all but boundedly many blocks.

The ceilings cost only `log 2`: `⌈y⌉ ≤ y + 1 ≤ 2y` once `y ≥ 1`, and
the lower endpoint is bounded below by the power itself. -/
theorem log_blockHi_sub_log_blockLo_le (x k : ℕ) (hx : 2 ≤ x) (hk : 1 ≤ k) :
    Real.log (blockHi x k : ℝ) - Real.log (blockLo x k : ℝ)
      ≤ (Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
          + Real.log 2 := by
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by
    have : (1:ℕ) ≤ x := by omega
    exact_mod_cast this
  have hlogx : (0:ℝ) ≤ Real.log (x:ℝ) := Real.log_nonneg hx1
  set a : ℝ := (x:ℝ) ^ (1 - Real.exp (1 - (k:ℝ))) with ha_def
  set b : ℝ := (x:ℝ) ^ (1 - Real.exp (-(k:ℝ))) with hb_def
  have ha1 : (1:ℝ) ≤ a := by
    rw [ha_def]
    refine Real.one_le_rpow hx1 ?_
    have : Real.exp (1 - (k:ℝ)) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
      linarith
    linarith
  have hb1 : (1:ℝ) ≤ b := by
    rw [hb_def]
    refine Real.one_le_rpow hx1 ?_
    have : Real.exp (-(k:ℝ)) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg _
      linarith
    linarith
  -- the ceiling costs at most a factor two
  have hceil : ((blockHi x k : ℕ):ℝ) ≤ 2 * b := by
    have h1 : ((blockHi x k : ℕ):ℝ) < b + 1 := by
      rw [blockHi, ← hb_def]
      exact Nat.ceil_lt_add_one (by linarith)
    linarith
  have hfloor : a ≤ ((blockLo x k : ℕ):ℝ) := by
    rw [blockLo, ← ha_def]
    exact Nat.le_ceil _
  -- compare logarithms
  have hHi1 : 1 ≤ blockHi x k := by
    rw [blockHi, Nat.one_le_ceil_iff]
    exact lt_of_lt_of_le (by norm_num) hb1
  have hHi0 : (0:ℝ) < ((blockHi x k : ℕ):ℝ) := by
    have : (0:ℕ) < blockHi x k := by omega
    exact_mod_cast this
  have hlogHi : Real.log ((blockHi x k : ℕ):ℝ) ≤ Real.log 2 + Real.log b := by
    have h := Real.log_le_log hHi0 hceil
    rwa [Real.log_mul (by norm_num) (by linarith)] at h
  have hlogLo : Real.log a ≤ Real.log ((blockLo x k : ℕ):ℝ) :=
    Real.log_le_log (by linarith) hfloor
  -- and evaluate the two powers
  have hla : Real.log a = (1 - Real.exp (1 - (k:ℝ))) * Real.log (x:ℝ) := by
    rw [ha_def, Real.log_rpow (by linarith)]
  have hlb : Real.log b = (1 - Real.exp (-(k:ℝ))) * Real.log (x:ℝ) := by
    rw [hb_def, Real.log_rpow (by linarith)]
  have hsplit : Real.exp (1 - (k:ℝ)) = Real.exp 1 * Real.exp (-(k:ℝ)) := by
    rw [← Real.exp_add]
    congr 1
  have hdiff : Real.log b - Real.log a
      = (Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ) := by
    rw [hla, hlb, hsplit]
    ring
  linarith [hlogHi, hlogLo, hdiff]

open Finset in
/-- **Real quotient versus natural quotient** (Track R, N15a): for
`2p ≤ x`,

  `log(x/p) ≤ 2·log⌊x/p⌋`.

The two are not interchangeable and the direction matters.  The
iteration of §3 applies the log-identity at the *natural number*
`⌊x/p⌋`, so it produces `log⌊x/p⌋` in the denominator; but
`tripleConv` and the mass bounds are stated with the real quotient
`log(x/p)`.  Since these sit in a denominator, replacing one by the
other weakens or strengthens a bound depending on the direction, and
`log⌊x/p⌋ ≤ log(x/p)` is the *wrong* way round for transferring an
upper bound.

This supplies the missing direction, at the cost of a factor two:
`x/p < ⌊x/p⌋ + 1 ≤ 2⌊x/p⌋`, and `⌊x/p⌋ ≥ 2` makes `log 2 ≤ log⌊x/p⌋`,
so `log(x/p) < log 2 + log⌊x/p⌋ ≤ 2·log⌊x/p⌋`. -/
theorem log_div_le_two_mul_log_natDiv (x p : ℕ) (hp : 1 ≤ p) (h2 : 2*p ≤ x) :
    Real.log ((x:ℝ)/(p:ℝ)) ≤ 2 * Real.log ((x/p : ℕ):ℝ) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
  -- the natural quotient is at least two
  have hN2 : 2 ≤ x/p := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    omega
  have hN2R : (2:ℝ) ≤ ((x/p : ℕ):ℝ) := by exact_mod_cast hN2
  have hlogN : Real.log 2 ≤ Real.log ((x/p : ℕ):ℝ) :=
    Real.log_le_log (by norm_num) hN2R
  -- the real quotient is below twice the natural one
  have hlt : (x:ℝ)/(p:ℝ) < ((x/p : ℕ):ℝ) + 1 := by
    rw [div_lt_iff₀ hp0]
    have hnat : x < (x/p + 1) * p := by
      have hlt' : x < p * (x/p + 1) := Nat.lt_mul_div_succ x (by omega)
      rwa [mul_comm] at hlt'
    have hc : (x:ℝ) < (((x/p + 1) * p : ℕ):ℝ) := by exact_mod_cast hnat
    push_cast at hc
    linarith
  have hdouble : (x:ℝ)/(p:ℝ) ≤ 2 * ((x/p : ℕ):ℝ) := by linarith
  have hpos : (0:ℝ) < (x:ℝ)/(p:ℝ) := by
    have : (0:ℝ) < (x:ℝ) := by
      have : 0 < x := by omega
      exact_mod_cast this
    positivity
  calc Real.log ((x:ℝ)/(p:ℝ))
      ≤ Real.log (2 * ((x/p : ℕ):ℝ)) := Real.log_le_log hpos hdouble
    _ = Real.log 2 + Real.log ((x/p : ℕ):ℝ) := by
        rw [Real.log_mul (by norm_num) (by linarith)]
    _ ≤ 2 * Real.log ((x/p : ℕ):ℝ) := by linarith

open Finset in
/-- **The two prime ranges agree, off by one** (Track R, N15b):

  `(Icc 1 X).filter Nat.Prime = (X+1).primesBelow`.

`sum_mul_log_x_prime_restrict` produces its primes as
`(Icc 1 X).filter Nat.Prime` — the primes `≤ X` — whereas `tripleConv`
and the mass bounds are written with `X.primesBelow`, the primes
`< X`.  The two differ by the single endpoint `X`, and this identity
pins the relationship exactly rather than leaving it to be rediscovered
at the point of use.

The `1 ≤ q` side condition is free: it follows from primality. -/
theorem Icc_filter_prime_eq_primesBelow (X : ℕ) :
    (Finset.Icc 1 X).filter Nat.Prime = (X+1).primesBelow := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨_, hqX⟩, hq⟩
    exact ⟨by omega, hq⟩
  · rintro ⟨hqX, hq⟩
    exact ⟨⟨hq.one_lt.le, by omega⟩, hq⟩

open Finset in
/-- **The endpoint term of the inner prime range** (Track R, N15c): the
two prime ranges of `Icc_filter_prime_eq_primesBelow` differ by at most
one summand, of size `≤ 2·log⌊x/p⌋`.

`sum_mul_log_x_prime_restrict` applied at `⌊x/p⌋` produces primes
`≤ ⌊x/p⌋`; `tripleConv` consumes primes `< ⌊x/p⌋`.  The gap is the
single term `q = ⌊x/p⌋`, and its innermost range has at most two
elements because `p·⌊x/p⌋ > x − p ≥ x/2`.  So the whole discrepancy is
`≤ 2·log⌊x/p⌋`. -/
theorem inner_endpoint_diff_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (x p : ℕ) (hp : 1 ≤ p) (h2 : 2*p ≤ x) :
    |(∑ q ∈ ((x/p)+1).primesBelow, (Real.log (q:ℝ) * f q)
          * ∑ n ∈ Finset.Icc 1 (x/(p*q)), f n)
        - ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
            * ∑ n ∈ Finset.Icc 1 (x/(p*q)), f n|
      ≤ 2 * Real.log ((x/p : ℕ):ℝ) := by
  classical
  have hp0 : 0 < p := by omega
  have hsub : (x/p).primesBelow ⊆ ((x/p)+1).primesBelow := by
    intro q hq
    rw [Nat.mem_primesBelow] at hq ⊢
    exact ⟨by omega, hq.2⟩
  have hdiff : ((x/p)+1).primesBelow \ (x/p).primesBelow ⊆ {x/p} := by
    intro q hq
    rw [Finset.mem_sdiff, Nat.mem_primesBelow, Nat.mem_primesBelow] at hq
    rw [Finset.mem_singleton]
    by_contra hne
    exact hq.2 ⟨by omega, hq.1.2⟩
  -- the difference collapses to the sdiff
  have hsd := Finset.sum_sdiff (f := fun q : ℕ => (Real.log (q:ℝ) * f q)
      * ∑ n ∈ Finset.Icc 1 (x/(p*q)), f n) hsub
  have hsplit : (∑ q ∈ ((x/p)+1).primesBelow, (Real.log (q:ℝ) * f q)
        * ∑ n ∈ Finset.Icc 1 (x/(p*q)), f n)
      - ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
          * ∑ n ∈ Finset.Icc 1 (x/(p*q)), f n
      = ∑ q ∈ ((x/p)+1).primesBelow \ (x/p).primesBelow,
          (Real.log (q:ℝ) * f q) * ∑ n ∈ Finset.Icc 1 (x/(p*q)), f n := by
    linarith [hsd]
  rw [hsplit]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  -- the single surviving term is small
  have hterm : ∀ q ∈ ((x/p)+1).primesBelow \ (x/p).primesBelow,
      |(Real.log (q:ℝ) * f q) * ∑ n ∈ Finset.Icc 1 (x/(p*q)), f n|
        ≤ 2 * Real.log ((x/p : ℕ):ℝ) := by
    intro q hq
    have hqX : q = x/p := Finset.mem_singleton.mp (hdiff hq)
    have hq0 : 0 < q := by
      rw [hqX]
      rw [Nat.lt_div_iff_mul_lt hp0]
      omega
    -- `p·q > x − p`, so the innermost range has at most two elements
    have hexp : p * (x/p + 1) = p * (x/p) + p := by ring
    have hlt := Nat.lt_mul_div_succ x hp0
    have hpq_lb : x < p * q + p := by
      rw [hqX]
      omega
    have hpq_ub : p * q ≤ x := by
      rw [hqX]
      exact Nat.mul_div_le x p
    have hcard : x/(p*q) ≤ 2 := by
      rw [Nat.div_le_iff_le_mul_add_pred (by positivity)]
      omega
    have hinner : |∑ n ∈ Finset.Icc 1 (x/(p*q)), f n| ≤ 2 := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      calc ∑ n ∈ Finset.Icc 1 (x/(p*q)), |f n|
          ≤ ∑ _n ∈ Finset.Icc 1 (x/(p*q)), (1:ℝ) :=
            Finset.sum_le_sum fun n _ => hf n
        _ = ((Finset.Icc 1 (x/(p*q))).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ 2 := by
            rw [Nat.card_Icc, Nat.add_sub_cancel]
            exact_mod_cast hcard
    have hlogq : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_natCast_nonneg q
    have hlogeq : Real.log (q:ℝ) = Real.log ((x/p : ℕ):ℝ) := by rw [hqX]
    rw [abs_mul, abs_mul, abs_of_nonneg hlogq]
    calc Real.log (q:ℝ) * |f q| * |∑ n ∈ Finset.Icc 1 (x/(p*q)), f n|
        ≤ Real.log (q:ℝ) * 1 * 2 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (hf q) hlogq) hinner
            (abs_nonneg _) (by positivity)
      _ = 2 * Real.log (q:ℝ) := by ring
      _ = 2 * Real.log ((x/p : ℕ):ℝ) := by rw [hlogeq]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hcard1 : (((x/p)+1).primesBelow \ (x/p).primesBelow).card ≤ 1 := by
    have h := Finset.card_le_card hdiff
    simpa using h
  have hlogX : (0:ℝ) ≤ Real.log ((x/p : ℕ):ℝ) := Real.log_natCast_nonneg _
  rw [Finset.sum_const, nsmul_eq_mul]
  calc ((((x/p)+1).primesBelow \ (x/p).primesBelow).card : ℝ)
        * (2 * Real.log ((x/p : ℕ):ℝ))
      ≤ 1 * (2 * Real.log ((x/p : ℕ):ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast hcard1
    _ = 2 * Real.log ((x/p : ℕ):ℝ) := one_mul _

open Finset in
/-- **The iteration, one prime at a time** (Track R, N15d): replacing
the inner mean value `∑_{m ≤ x/p} f(m)` by the double convolution it
expands into costs

  `≤ 10·x·(log p/(p·log(x/p))) + 2·log p`.

This is §3's second application of the log-identity, done at `⌊x/p⌋`
and then reconciled with the shape `tripleConv` expects.  Three
separate reconciliations are needed and each contributes:

* `sum_mul_log_x_prime_restrict` at `⌊x/p⌋` gives `9·⌊x/p⌋`;
* the identity's `log⌊x/p⌋` must become `log(x/p)`, costing `|A|·log 2`
  — another `⌊x/p⌋·log 2`, which is why the constant is `10` and not `9`;
* the prime ranges differ by an endpoint (`inner_endpoint_diff_le`),
  contributing `2·log⌊x/p⌋ ≤ 2·log(x/p)` and hence the `2·log p`. -/
theorem iteration_term_diff_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (hmul : ∀ a b, f (a*b) = f a * f b) (x p : ℕ) (hp : p.Prime)
    (h2 : 2*p ≤ x) :
    |(Real.log (p:ℝ) * f p) * (∑ m ∈ Finset.Icc 1 (x/p), f m)
        - (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
          * (∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
              * ∑ n ∈ Finset.Icc 1 (x/(p*q)), f n)|
      ≤ 10 * (x:ℝ) * (Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
        + 2 * Real.log (p:ℝ) := by
  classical
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp1
  have hx0 : (0:ℝ) < (x:ℝ) := by
    have : 0 < x := by omega
    exact_mod_cast this
  have hX2 : 2 ≤ x/p := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    omega
  have hX1 : 1 ≤ x/p := by omega
  have hXR : (2:ℝ) ≤ ((x/p : ℕ):ℝ) := by exact_mod_cast hX2
  have hLX : (0:ℝ) < Real.log ((x/p : ℕ):ℝ) := Real.log_pos (by linarith)
  have hcast : ((x/p : ℕ):ℝ) ≤ (x:ℝ)/(p:ℝ) := Nat.cast_div_le
  have hL : (0:ℝ) < Real.log ((x:ℝ)/(p:ℝ)) :=
    lt_of_lt_of_le hLX (Real.log_le_log (by linarith) hcast)
  have hLXL : Real.log ((x/p : ℕ):ℝ) ≤ Real.log ((x:ℝ)/(p:ℝ)) :=
    Real.log_le_log (by linarith) hcast
  -- the identity at `⌊x/p⌋`, reconciled to the shape `tripleConv` uses
  have hN5 := sum_mul_log_x_prime_restrict f hf (x/p) hX1
  have hN7 := sum_prime_conv_factor f hmul (x/p)
  rw [hN7] at hN5
  rw [Icc_filter_prime_eq_primesBelow] at hN5
  have hinner : ∀ q : ℕ, (x/p)/q = x/(p*q) := by
    intro q
    rw [Nat.div_div_eq_div_mul]
  simp only [hinner] at hN5
  -- the endpoint discrepancy between the two prime ranges
  have hEnd := inner_endpoint_diff_le f hf x p hp1 h2
  -- the inner mean value is bounded by the length of its range
  have hA : |∑ m ∈ Finset.Icc 1 (x/p), f m| ≤ ((x/p : ℕ):ℝ) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc ∑ m ∈ Finset.Icc 1 (x/p), |f m|
        ≤ ∑ _m ∈ Finset.Icc 1 (x/p), (1:ℝ) :=
          Finset.sum_le_sum fun m _ => hf m
      _ = ((Finset.Icc 1 (x/p)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ((x/p : ℕ):ℝ) := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  -- swapping `log⌊x/p⌋` for `log(x/p)` costs `|A|·log 2`
  have hLgap : Real.log ((x:ℝ)/(p:ℝ)) - Real.log ((x/p : ℕ):ℝ) ≤ Real.log 2 := by
    have hlt : (x:ℝ)/(p:ℝ) ≤ 2 * ((x/p : ℕ):ℝ) := by
      have hnat : x < p * (x/p) + p := by
        have hexp : p * (x/p + 1) = p * (x/p) + p := by ring
        have := Nat.lt_mul_div_succ x (show 0 < p by omega)
        omega
      have hc : (x:ℝ) < ((p * (x/p) + p : ℕ):ℝ) := by exact_mod_cast hnat
      push_cast at hc
      rw [div_le_iff₀ hp0]
      nlinarith [hc, hp0, hXR]
    have h := Real.log_le_log (by positivity : (0:ℝ) < (x:ℝ)/(p:ℝ)) hlt
    rw [Real.log_mul (by norm_num) (by linarith)] at h
    linarith
  -- assemble the three reconciliations
  set A : ℝ := ∑ m ∈ Finset.Icc 1 (x/p), f m with hA_def
  set C : ℝ := ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
      * ∑ n ∈ Finset.Icc 1 (x/(p*q)), f n with hC_def
  set C' : ℝ := ∑ q ∈ ((x/p)+1).primesBelow, (Real.log (q:ℝ) * f q)
      * ∑ n ∈ Finset.Icc 1 (x/(p*q)), f n with hC'_def
  have hkey : |Real.log ((x:ℝ)/(p:ℝ)) * A - C|
      ≤ ((x/p : ℕ):ℝ) * (9 + Real.log 2) + 2 * Real.log ((x/p : ℕ):ℝ) := by
    have h1 : |A * Real.log ((x/p : ℕ):ℝ) - C'| ≤ 9 * ((x/p : ℕ):ℝ) := hN5
    have h2' : |C' - C| ≤ 2 * Real.log ((x/p : ℕ):ℝ) := hEnd
    have h3 : |Real.log ((x:ℝ)/(p:ℝ)) * A - A * Real.log ((x/p : ℕ):ℝ)|
        ≤ ((x/p : ℕ):ℝ) * Real.log 2 := by
      have heq : Real.log ((x:ℝ)/(p:ℝ)) * A - A * Real.log ((x/p : ℕ):ℝ)
          = A * (Real.log ((x:ℝ)/(p:ℝ)) - Real.log ((x/p : ℕ):ℝ)) := by ring
      rw [heq, abs_mul]
      refine mul_le_mul hA ?_ (abs_nonneg _) (by positivity)
      rw [abs_of_nonneg (by linarith)]
      exact hLgap
    have htri : |Real.log ((x:ℝ)/(p:ℝ)) * A - C|
        ≤ |Real.log ((x:ℝ)/(p:ℝ)) * A - A * Real.log ((x/p : ℕ):ℝ)|
            + |A * Real.log ((x/p : ℕ):ℝ) - C'| + |C' - C| := by
      have e1 : Real.log ((x:ℝ)/(p:ℝ)) * A - C
          = (Real.log ((x:ℝ)/(p:ℝ)) * A - A * Real.log ((x/p : ℕ):ℝ))
            + ((A * Real.log ((x/p : ℕ):ℝ) - C') + (C' - C)) := by ring
      rw [e1]
      refine le_trans (abs_add_le _ _) ?_
      linarith [abs_add_le (A * Real.log ((x/p : ℕ):ℝ) - C') (C' - C)]
    have hfin : ((x/p : ℕ):ℝ) * (9 + Real.log 2) + 2 * Real.log ((x/p : ℕ):ℝ)
        = ((x/p : ℕ):ℝ) * Real.log 2 + 9 * ((x/p : ℕ):ℝ)
          + 2 * Real.log ((x/p : ℕ):ℝ) := by ring
    rw [hfin]
    linarith [htri, h1, h2', h3]
  -- divide through by `log(x/p)`
  have hfactor : (Real.log (p:ℝ) * f p) * A
      - (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ))) * C
      = (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
        * (Real.log ((x:ℝ)/(p:ℝ)) * A - C) := by
    field_simp
  rw [hfactor, abs_mul]
  have hlogp : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
  have hcoef : |Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ))|
      ≤ Real.log (p:ℝ) / Real.log ((x:ℝ)/(p:ℝ)) := by
    rw [abs_div, abs_mul, abs_of_nonneg hlogp, abs_of_nonneg hL.le]
    refine div_le_div_of_nonneg_right ?_ hL.le
    calc Real.log (p:ℝ) * |f p| ≤ Real.log (p:ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (hf p) hlogp
      _ = Real.log (p:ℝ) := mul_one _
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  have hstep : (Real.log (p:ℝ) / Real.log ((x:ℝ)/(p:ℝ)))
      * (((x/p : ℕ):ℝ) * (9 + Real.log 2) + 2 * Real.log ((x/p : ℕ):ℝ))
      ≤ 10 * (x:ℝ) * (Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
        + 2 * Real.log (p:ℝ) := by
    have hd : (0:ℝ) < Real.log ((x:ℝ)/(p:ℝ)) := hL
    have hq : ((x/p : ℕ):ℝ) ≤ (x:ℝ)/(p:ℝ) := hcast
    have hmain : (Real.log (p:ℝ) / Real.log ((x:ℝ)/(p:ℝ)))
        * (((x/p : ℕ):ℝ) * (9 + Real.log 2))
        ≤ 10 * (x:ℝ) * (Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ)))) := by
      have hQ0 : (0:ℝ) ≤ ((x/p : ℕ):ℝ) := Nat.cast_nonneg _
      have hQR : ((x/p : ℕ):ℝ) * (9 + Real.log 2) ≤ ((x:ℝ)/(p:ℝ)) * 10 := by
        nlinarith [hq, hlog2, hQ0]
      have hL0 : (0:ℝ) ≤ Real.log (p:ℝ) / Real.log ((x:ℝ)/(p:ℝ)) :=
        div_nonneg hlogp hd.le
      calc (Real.log (p:ℝ) / Real.log ((x:ℝ)/(p:ℝ)))
            * (((x/p : ℕ):ℝ) * (9 + Real.log 2))
          ≤ (Real.log (p:ℝ) / Real.log ((x:ℝ)/(p:ℝ))) * (((x:ℝ)/(p:ℝ)) * 10) :=
            mul_le_mul_of_nonneg_left hQR hL0
        _ = 10 * (x:ℝ) * (Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ)))) := by
            field_simp
    have htail : (Real.log (p:ℝ) / Real.log ((x:ℝ)/(p:ℝ)))
        * (2 * Real.log ((x/p : ℕ):ℝ)) ≤ 2 * Real.log (p:ℝ) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hd]
      nlinarith [hLXL, hlogp, hd]
    linarith [hmain, htail]
  calc |Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ))|
        * |Real.log ((x:ℝ)/(p:ℝ)) * A - C|
      ≤ (Real.log (p:ℝ) / Real.log ((x:ℝ)/(p:ℝ)))
          * (((x/p : ℕ):ℝ) * (9 + Real.log 2)
              + 2 * Real.log ((x/p : ℕ):ℝ)) := by
        refine mul_le_mul hcoef hkey (abs_nonneg _) ?_
        exact div_nonneg hlogp hL.le
    _ ≤ 10 * (x:ℝ) * (Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
          + 2 * Real.log (p:ℝ) := hstep

open Finset in
/-- **The iteration, over a whole block** (Track R, N15e): summing
`iteration_term_diff_le`,

  `|∑_{p∈P} (log p·f(p))·∑_{m ≤ x/p} f(m) − tripleConv f x P|
     ≤ 10·x·∑_{p∈P} log p/(p·log(x/p)) + 2·∑_{p∈P} log p`.

This completes §3's second application of the log-identity.  Both error
terms are already controlled: the first is the harmonic sum bounded by
`sum_log_div_mul_log_ratio_le` (`O(log log x)` after the dyadic split),
and the second is Chebyshev's `θ`-bound over the block.

With this, the passage from the mean value to the triple convolution is
complete, and what remains of §3 is choosing the blocks. -/
theorem iteration_diff_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (hmul : ∀ a b, f (a*b) = f a * f b) (x : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 2*p ≤ x) :
    |∑ p ∈ P, (Real.log (p:ℝ) * f p) * (∑ m ∈ Finset.Icc 1 (x/p), f m)
        - tripleConv f x P|
      ≤ 10 * (x:ℝ)
          * (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
        + 2 * ∑ p ∈ P, Real.log (p:ℝ) := by
  classical
  rw [tripleConv, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ p ∈ P,
      |(Real.log (p:ℝ) * f p) * (∑ m ∈ Finset.Icc 1 (x/p), f m)
          - (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
            * (∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
                * ∑ n ∈ Finset.Icc 1 (x/(p*q)), f n)|
        ≤ 10 * (x:ℝ) * (Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
          + 2 * Real.log (p:ℝ) := by
    intro p hp
    obtain ⟨hpp, h2p⟩ := hP p hp
    exact iteration_term_diff_le f hf hmul x p hpp h2p
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

open Finset in
/-- **The trivial bound at the `k`-th block** (Track R, N16): combining
the modulus bound with the block geometry,

  `|tripleConv f x P_k| ≤ x·(16·((e−1)·e^{−k}·log x + log 2) + 16·log 4)`,

i.e. `≪ e^{−k}·x·log x`.  This is §3's trivial estimate in the form it
is actually used, and its geometric decay in `k` is what
`sum_exp_neg_tail_le` then exploits to discard all but boundedly many
blocks.

The hypothesis `2·blockHi x k ≤ x` is not an artifact: the upper
endpoint is `⌈x^{1−e^{−k}}⌉`, which approaches `x` as `k` grows, so the
blocks only fit inside the range while `k ≲ log log x`.  That is exactly
the cutoff §3 imposes, and it is the caller's job to supply it. -/
theorem tripleConv_block_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (x k : ℕ)
    (hx : 2 ≤ x) (hk : 1 ≤ k) (hfit : 2 * blockHi x k ≤ x) :
    |tripleConv f x
        ((Finset.Ico (blockLo x k) (blockHi x k)).filter Nat.Prime)|
      ≤ (x:ℝ) * (16 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
          + Real.log 2) + 16 * Real.log 4) := by
  have hx1 : 1 ≤ x := by omega
  obtain ⟨hlo1, hlohi⟩ := blockLo_le_blockHi x k hx1
  have hx0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
  refine le_trans (norm_tripleConv_le f hf x (blockLo x k) (blockHi x k)
    hlo1 hlohi hfit) ?_
  refine mul_le_mul_of_nonneg_left ?_ hx0
  have hgeom := log_blockHi_sub_log_blockLo_le x k hx hk
  linarith [hgeom]

open Finset in
/-- **Factoring over an arbitrary prime set** (Track R, N17):
`sum_prime_conv_factor` holds over any finset, not only
`(Icc 1 x).filter Nat.Prime`.

§3 discards the extreme primes *before* factoring — the discard bounds
(`prime_head_sum_le`, `prime_tail_sum_le`) are stated for the
unfactored form `log p · ∑ f(pm)` — so the factoring has to be applied
afterwards to whatever survives.  The proof is termwise and never used
the shape of the index set, so the generalisation is free. -/
theorem sum_prime_conv_factor' (f : ℕ → ℝ)
    (hmul : ∀ a b, f (a*b) = f a * f b) (x : ℕ) (P : Finset ℕ) :
    ∑ p ∈ P, Real.log (p:ℝ) * ∑ m ∈ Finset.Icc 1 (x/p), f (p*m)
      = ∑ p ∈ P, (Real.log (p:ℝ) * f p) * ∑ m ∈ Finset.Icc 1 (x/p), f m := by
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [hmul]; ring

open Finset in
/-- **The mean value after the discards** (Track R, N18): combining the
log-identity at `x` with both extreme-prime discards,

  `|S(x)·log x − ∑_{y ≤ p, 2p ≤ x} (log p·f(p))·∑_{m ≤ x/p} f(m)|
     ≤ 9x + x·(log y + 2) + (x+1)·log 4`.

**The two discarded ranges are disjoint once `2y ≤ x`** — a prime with
`p < y` and `x < 2p` would force `x < 2y`.  That is what lets
`prime_head_sum_le` and `prime_tail_sum_le` be applied exactly as
stated, with no subset-generalisation: the prime range splits cleanly
into three parts.  The hypothesis is harmless, since §3 takes
`y ≈ log⁴x`.

The factoring is applied last, via `sum_prime_conv_factor'`, because
the discard bounds are stated for the unfactored summand. -/
theorem sum_after_discards (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (hmul : ∀ a b, f (a*b) = f a * f b) (x y : ℕ) (hx : 1 ≤ x) (hy : 2 ≤ y)
    (hyx : 2*y ≤ x) :
    |(∑ n ∈ Finset.Icc 1 x, f n) * Real.log (x:ℝ)
        - ∑ p ∈ (((Finset.Icc 1 x).filter Nat.Prime).filter
            (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p),
            (Real.log (p:ℝ) * f p) * ∑ m ∈ Finset.Icc 1 (x/p), f m|
      ≤ 9*(x:ℝ) + (x:ℝ)*(Real.log (y:ℝ) + 2) + ((x:ℝ)+1)*Real.log 4 := by
  classical
  set S : Finset ℕ := (Finset.Icc 1 x).filter Nat.Prime with hS_def
  -- the two discarded ranges are disjoint, so the tail filter simplifies
  have hfe : ((S.filter (fun p => ¬ p < y)).filter (fun p => x < 2*p))
      = S.filter (fun p => x < 2*p) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hS, _⟩, h2⟩
      exact ⟨hS, h2⟩
    · rintro ⟨hS, h2⟩
      exact ⟨⟨hS, by omega⟩, h2⟩
  -- split the prime range into head, tail and survivors
  have hsplit1 := Finset.sum_filter_add_sum_filter_not S (fun p => p < y)
    (fun p => Real.log (p:ℝ) * ∑ m ∈ Finset.Icc 1 (x/p), f (p*m))
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    (S.filter (fun p => ¬ p < y)) (fun p => x < 2*p)
    (fun p => Real.log (p:ℝ) * ∑ m ∈ Finset.Icc 1 (x/p), f (p*m))
  rw [hfe] at hsplit2
  -- the identity, and the two discard bounds
  have hN5 := sum_mul_log_x_prime_restrict f hf x hx
  have hHead := prime_head_sum_le f hf x y hy
  have hTail := prime_tail_sum_le f hf x
  -- factor the survivors
  have hfact := sum_prime_conv_factor' f hmul x
    ((S.filter (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p))
  rw [← hfact]
  -- assemble
  have hchain : (∑ n ∈ Finset.Icc 1 x, f n) * Real.log (x:ℝ)
      - ∑ p ∈ (S.filter (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p),
          Real.log (p:ℝ) * ∑ m ∈ Finset.Icc 1 (x/p), f (p*m)
      = ((∑ n ∈ Finset.Icc 1 x, f n) * Real.log (x:ℝ)
          - ∑ p ∈ S, Real.log (p:ℝ) * ∑ m ∈ Finset.Icc 1 (x/p), f (p*m))
        + (∑ p ∈ S.filter (fun p => p < y),
            Real.log (p:ℝ) * ∑ m ∈ Finset.Icc 1 (x/p), f (p*m))
        + (∑ p ∈ S.filter (fun p => x < 2*p),
            Real.log (p:ℝ) * ∑ m ∈ Finset.Icc 1 (x/p), f (p*m)) := by
    linarith [hsplit1, hsplit2]
  rw [hchain]
  refine le_trans (abs_add_le _ _) ?_
  have h1 : |((∑ n ∈ Finset.Icc 1 x, f n) * Real.log (x:ℝ)
          - ∑ p ∈ S, Real.log (p:ℝ) * ∑ m ∈ Finset.Icc 1 (x/p), f (p*m))
        + (∑ p ∈ S.filter (fun p => p < y),
            Real.log (p:ℝ) * ∑ m ∈ Finset.Icc 1 (x/p), f (p*m))|
      ≤ 9*(x:ℝ) + (x:ℝ)*(Real.log (y:ℝ) + 2) := by
    refine le_trans (abs_add_le _ _) ?_
    linarith [hN5, hHead]
  linarith [h1, hTail]

/-- **The blocks tile** (Track R, N19): `blockLo x (k+1) = blockHi x k`.

Consecutive blocks of §3 abut exactly — the upper endpoint of block `k`
*is* the lower endpoint of block `k+1`, because
`1 − e^{1−(k+1)} = 1 − e^{−k}` on the nose.  So the blocks
`[blockLo x k, blockHi x k)` for `k = 1, …, K` partition
`[blockLo x 1, blockHi x K)` with no gaps and no overlaps, which is what
lets the mean value be reassembled from them.

`blockLo x 1 = ⌈x⁰⌉ = 1`, so the tiling starts at the bottom of the
prime range. -/
theorem blockLo_succ_eq_blockHi (x k : ℕ) :
    blockLo x (k+1) = blockHi x k := by
  rw [blockLo, blockHi]
  congr 2
  push_cast
  norm_num

open Finset in
/-- **The upper endpoints increase** (Track R, N20): `blockHi x` is
monotone in `k`, since `1 − e^{−k}` is and `x ≥ 1` makes `rpow`
monotone in the exponent. -/
theorem blockHi_mono (x : ℕ) (hx : 1 ≤ x) {k l : ℕ} (hkl : k ≤ l) :
    blockHi x k ≤ blockHi x l := by
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hexp : Real.exp (-(l:ℝ)) ≤ Real.exp (-(k:ℝ)) := by
    refine Real.exp_le_exp.mpr ?_
    have : (k:ℝ) ≤ (l:ℝ) := by exact_mod_cast hkl
    linarith
  rw [blockHi, blockHi]
  exact Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))

open Finset in
/-- **The block decomposition of a prime sum** (Track R, N20): the
primes of `[blockLo x 1, blockHi x K)` split as the disjoint union of
the blocks,

  `∑_{p ∈ [blockLo x 1, blockHi x K)} g(p) = ∑_{k=1}^{K} ∑_{p ∈ block k} g(p)`.

This is `blockLo_succ_eq_blockHi` in the form §3 uses it: the survivor
range is exactly the union of the blocks, so the mean value can be
reassembled from the per-block estimates.  Note `blockHi x 0 = ⌈x⁰⌉ = 1
= blockLo x 1`, which makes the empty case degenerate correctly. -/
theorem sum_block_split {M : Type*} [AddCommMonoid M] (g : ℕ → M) (x : ℕ)
    (hx : 1 ≤ x) :
    ∀ K : ℕ,
      ∑ p ∈ (Finset.Ico (blockLo x 1) (blockHi x K)).filter Nat.Prime, g p
        = ∑ k ∈ Finset.Icc 1 K,
            ∑ p ∈ (Finset.Ico (blockLo x k) (blockHi x k)).filter Nat.Prime,
              g p := by
  classical
  intro K
  induction K with
  | zero =>
    have h0 : blockHi x 0 = blockLo x 1 := (blockLo_succ_eq_blockHi x 0).symm
    rw [h0]
    simp
  | succ K ih =>
    have hlo : blockLo x 1 ≤ blockHi x K := by
      have h1 : blockLo x 1 = blockHi x 0 := blockLo_succ_eq_blockHi x 0
      rw [h1]
      exact blockHi_mono x hx (Nat.zero_le K)
    have hhi : blockHi x K ≤ blockHi x (K+1) :=
      blockHi_mono x hx (Nat.le_succ K)
    have hstep : blockLo x (K+1) = blockHi x K := blockLo_succ_eq_blockHi x K
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), ← ih, hstep]
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
    exact (Finset.sum_Ico_consecutive
      (fun p => if p.Prime then g p else 0) hlo hhi).symm

open Finset in
/-- **The `S_k` mass over an arbitrary sub-collection** (Track R, N21):
`Sk_trivial_mass_le` for any prime set contained in `[A, B)`, not only
for the whole of `(Ico A B).filter Nat.Prime`.

§3's blocks have to be intersected with the survivor range: the
partition `blockLo x k … blockHi x k` starts at `blockLo x 1 = 1`,
whereas the discards leave only the primes with `y ≤ p` and `2p ≤ x`.
So the sets that actually appear are sub-collections of the blocks, and
the block estimates must accept them.

As with `sum_prime_conv_factor'`, the original proof was termwise and
the index set only entered through a monotone sum, so the
generalisation costs nothing. -/
theorem Sk_trivial_mass_le' (x A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B)
    (hB : 2*B ≤ x) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ A ≤ p ∧ p < B) :
    ∑ p ∈ P, (Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
        * (∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ))
      ≤ 16 * (Real.log (B:ℝ) - Real.log (A:ℝ)) + 16 * Real.log 4 := by
  classical
  have hterm : ∀ p ∈ P,
      (Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
          * (∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ))
        ≤ 4 * (Real.log (p:ℝ)/(p:ℝ)) := by
    intro p hp
    obtain ⟨hpp, hAp, hpB⟩ := hP p hp
    have hp1 : 1 ≤ p := hpp.one_lt.le
    exact inner_mertens_cancel x p hp1 (by omega)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  -- the index set embeds in the full block
  have hsub : P ⊆ (Finset.Ico A B).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpp, hAp, hpB⟩ := hP p hp
    simp only [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨hAp, hpB⟩, hpp⟩
  have hmono : ∑ p ∈ P, Real.log (p:ℝ)/(p:ℝ)
      ≤ ∑ p ∈ (Finset.Ico A B).filter Nat.Prime, Real.log (p:ℝ)/(p:ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => div_nonneg (Real.log_natCast_nonneg i) (Nat.cast_nonneg _))
  have hmass := sum_log_div_Ico_le_log A B hA hAB
  linarith [hmono, hmass]

open Finset in
/-- **The trivial bound over an arbitrary sub-collection** (Track R,
N22): `norm_tripleConv_le` for any prime set contained in `[A, B)`.

Needed for the same reason as `Sk_trivial_mass_le'`: §3's blocks are
intersected with the survivor range, so the sets that appear are
sub-collections.  Because `tripleConv` is a *signed* sum, passing to a
subset is not a monotonicity step — the estimate genuinely has to be
restated, though its termwise proof makes that free. -/
theorem norm_tripleConv_le' (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (x A B : ℕ)
    (hA : 1 ≤ A) (hAB : A ≤ B) (hB : 2*B ≤ x)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ A ≤ p ∧ p < B) :
    |tripleConv f x P|
      ≤ (x:ℝ) * (16 * (Real.log (B:ℝ) - Real.log (A:ℝ)) + 16 * Real.log 4) := by
  classical
  have hx0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
  rw [tripleConv]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ p ∈ P,
      |(Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
        * ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
            * ∑ n ∈ Finset.Icc 1 (x/(p*q)), f n|
      ≤ (x:ℝ) * ((Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
          * ∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ)) := by
    intro p hp
    obtain ⟨hpp, hAp, hpB⟩ := hP p hp
    have hp1 : 1 ≤ p := hpp.one_lt.le
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp1
    have h2p : 2*p ≤ x := by omega
    have hquot : (2:ℝ) ≤ (x:ℝ)/(p:ℝ) := by
      rw [le_div_iff₀ hp0]
      have hc : ((2*p : ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast h2p
      push_cast at hc
      linarith
    have hlogpos : (0:ℝ) < Real.log ((x:ℝ)/(p:ℝ)) := Real.log_pos (by linarith)
    have hlogp : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
    have hinner : ∀ q : ℕ, |∑ n ∈ Finset.Icc 1 (x/(p*q)), f n|
        ≤ ((x/(p*q) : ℕ):ℝ) := by
      intro q
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      calc ∑ n ∈ Finset.Icc 1 (x/(p*q)), |f n|
          ≤ ∑ _n ∈ Finset.Icc 1 (x/(p*q)), (1:ℝ) :=
            Finset.sum_le_sum fun n _ => hf n
        _ = ((Finset.Icc 1 (x/(p*q))).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ = ((x/(p*q) : ℕ):ℝ) := by rw [Nat.card_Icc]; norm_num
    have hmid : |∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
          * ∑ n ∈ Finset.Icc 1 (x/(p*q)), f n|
        ≤ ((x:ℝ)/(p:ℝ)) * ∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun q hq => ?_
      rw [Nat.mem_primesBelow] at hq
      have hq1 : 1 ≤ q := hq.2.one_lt.le
      have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq1
      have hlogq : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_natCast_nonneg q
      have hcastq : ((x/(p*q) : ℕ):ℝ) ≤ (x:ℝ)/((p:ℝ)*(q:ℝ)) := by
        have h := Nat.cast_div_le (α := ℝ) (m := x) (n := p*q)
        push_cast at h
        exact h
      rw [abs_mul, abs_mul, abs_of_nonneg hlogq]
      calc Real.log (q:ℝ) * |f q| * |∑ n ∈ Finset.Icc 1 (x/(p*q)), f n|
          ≤ Real.log (q:ℝ) * 1 * ((x:ℝ)/((p:ℝ)*(q:ℝ))) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left (hf q) hlogq)
              (le_trans (hinner q) hcastq) (abs_nonneg _) (by positivity)
        _ = (x:ℝ)/(p:ℝ) * (Real.log (q:ℝ)/(q:ℝ)) := by field_simp
    rw [abs_mul]
    have houter : |Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ))|
        ≤ Real.log (p:ℝ) / Real.log ((x:ℝ)/(p:ℝ)) := by
      rw [abs_div, abs_mul, abs_of_nonneg hlogp, abs_of_nonneg hlogpos.le]
      refine div_le_div_of_nonneg_right ?_ hlogpos.le
      calc Real.log (p:ℝ) * |f p| ≤ Real.log (p:ℝ) * 1 :=
            mul_le_mul_of_nonneg_left (hf p) hlogp
        _ = Real.log (p:ℝ) := mul_one _
    have hsum0 : (0:ℝ) ≤ ∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ) :=
      Finset.sum_nonneg fun q _ =>
        div_nonneg (Real.log_natCast_nonneg q) (Nat.cast_nonneg _)
    calc |Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ))|
          * |∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
              * ∑ n ∈ Finset.Icc 1 (x/(p*q)), f n|
        ≤ (Real.log (p:ℝ) / Real.log ((x:ℝ)/(p:ℝ)))
            * (((x:ℝ)/(p:ℝ)) * ∑ q ∈ (x/p).primesBelow,
                Real.log (q:ℝ)/(q:ℝ)) := by
          refine mul_le_mul houter hmid (abs_nonneg _) ?_
          exact div_nonneg hlogp hlogpos.le
      _ = (x:ℝ) * ((Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
            * ∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ)) := by field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (Sk_trivial_mass_le' x A B hA hAB hB P hP) hx0

open Finset in
/-- **The block bound over an arbitrary sub-collection** (Track R,
N22): `tripleConv_block_le` for any prime set inside the `k`-th block.
This is the form §3's capstone consumes, since the blocks are
intersected with the survivor range. -/
theorem tripleConv_block_le' (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (x k : ℕ)
    (hx : 2 ≤ x) (hk : 1 ≤ k) (hfit : 2 * blockHi x k ≤ x)
    (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k) :
    |tripleConv f x P|
      ≤ (x:ℝ) * (16 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
          + Real.log 2) + 16 * Real.log 4) := by
  have hx1 : 1 ≤ x := by omega
  obtain ⟨hlo1, hlohi⟩ := blockLo_le_blockHi x k hx1
  have hx0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
  refine le_trans (norm_tripleConv_le' f hf x (blockLo x k) (blockHi x k)
    hlo1 hlohi hfit P hP) ?_
  refine mul_le_mul_of_nonneg_left ?_ hx0
  have hgeom := log_blockHi_sub_log_blockLo_le x k hx hk
  linarith [hgeom]

/-- **The tiling starts at 1** (Track R, N23): `blockLo x 1 = 1`, since
`1 − e^{1−1} = 0` and `x⁰ = 1`.  So the blocks reach down to the bottom
of the prime range and the survivor set needs no lower-end coverage
argument. -/
theorem blockLo_one (x : ℕ) : blockLo x 1 = 1 := by
  rw [blockLo]
  norm_num

open Finset in
/-- **The block decomposition survives a filter** (Track R, N23): for any
predicate `sv`,

  `∑_{p ∈ [1, blockHi x K), prime, sv p} g p
     = ∑_{k=1}^{K} ∑_{p ∈ block k, prime, sv p} g p`.

This is `sum_block_split` in the form the §3 capstone needs.  The
survivors are cut out of the prime range by the discards of N18, so what
gets decomposed is never a whole block — it is a block intersected with
the survivor condition.  Pushing the predicate through costs nothing:
apply the unfiltered split to `fun p => if sv p then g p else 0`. -/
theorem sum_block_split_filter {M : Type*} [AddCommMonoid M] (g : ℕ → M)
    (sv : ℕ → Prop) [DecidablePred sv] (x : ℕ) (hx : 1 ≤ x) (K : ℕ) :
    ∑ p ∈ ((Finset.Ico (blockLo x 1) (blockHi x K)).filter Nat.Prime).filter sv,
        g p
      = ∑ k ∈ Finset.Icc 1 K,
          ∑ p ∈ ((Finset.Ico (blockLo x k) (blockHi x k)).filter
            Nat.Prime).filter sv, g p := by
  classical
  have h := sum_block_split (fun p => if sv p then g p else 0) x hx K
  simp only [Finset.sum_filter] at h ⊢
  exact h

/-- **The tiling reaches the survivors** (Track R, N24): if
`e^{−K}·log x < log 2` then every `p` with `2p ≤ x` satisfies
`p < blockHi x K`.

The discards of N18 leave only primes with `2p ≤ x`, so this is exactly
the condition under which the blocks `k = 1, …, K` cover what is left.
The computation is `x^{1−e^{−K}} = x / x^{e^{−K}}` together with
`x^{e^{−K}} = exp(e^{−K}·log x) < 2`.

The hypothesis is strict because the conclusion is: `2p ≤ x` allows
`p = x/2` exactly, and a non-strict bound would only give
`p ≤ blockHi x K`, putting `p` outside the half-open block. -/
theorem lt_blockHi_of_two_mul_le (x K p : ℕ) (hx : 2 ≤ x) (hp : 2*p ≤ x)
    (hK : Real.exp (-(K:ℝ)) * Real.log (x:ℝ) < Real.log 2) :
    p < blockHi x K := by
  have hxR : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hx0 : (0:ℝ) < (x:ℝ) := by linarith
  set t := Real.exp (-(K:ℝ)) with ht_def
  have ht0 : 0 < t := Real.exp_pos _
  have hxt : (x:ℝ) ^ t < 2 := by
    rw [Real.rpow_def_of_pos hx0, mul_comm]
    calc Real.exp (t * Real.log (x:ℝ)) < Real.exp (Real.log 2) :=
          Real.exp_lt_exp.mpr hK
      _ = 2 := Real.exp_log (by norm_num)
  have hxt0 : (0:ℝ) < (x:ℝ) ^ t := Real.rpow_pos_of_pos hx0 t
  have hkey : (x:ℝ)/2 < (x:ℝ) ^ (1 - t) := by
    rw [Real.rpow_sub hx0, Real.rpow_one, div_lt_div_iff₀ (by norm_num) hxt0]
    nlinarith
  have hpR : (p:ℝ) ≤ (x:ℝ)/2 := by
    have hc : ((2*p : ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast hp
    push_cast at hc
    linarith
  rw [blockHi]
  exact Nat.lt_ceil.mpr (by linarith)

/-- **A covering depth always exists** (Track R, N24): for every `x`
there is a `K` with `e^{−K}·log x < log 2`, so the block tiling can
always be taken deep enough to contain every survivor.

`K ≍ log log x` is the honest size — the witness here is any natural
above `log x / log 2`, via `K < K + 1 ≤ e^K`. §3 pays for the depth
through the `∑_k e^{−k}` factor of `tripleConv_block_le'`, which is why
the blocks are geometric rather than dyadic. -/
theorem exists_block_cover (x : ℕ) :
    ∃ K : ℕ, Real.exp (-(K:ℝ)) * Real.log (x:ℝ) < Real.log 2 := by
  obtain ⟨K, hK⟩ := exists_nat_gt (Real.log (x:ℝ) / Real.log 2)
  refine ⟨K, ?_⟩
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hexpK : (K:ℝ) < Real.exp (K:ℝ) := by
    have := Real.add_one_le_exp (K:ℝ)
    linarith
  have hlt : Real.log (x:ℝ) < (K:ℝ) * Real.log 2 := by
    rw [div_lt_iff₀ hlog2] at hK
    linarith
  rw [Real.exp_neg, inv_mul_eq_div, div_lt_iff₀ (Real.exp_pos _)]
  nlinarith [Real.exp_pos (K:ℝ)]

open Finset in
/-- **The survivors are exactly the tiled range** (Track R, N25): once
the depth `K` covers `x/2`,

  `(((Icc 1 x).filter prime).filter (y ≤ ·)).filter (2· ≤ x)
     = ((Ico (blockLo x 1) (blockHi x K)).filter prime).filter (survivor)`.

Both inclusions are cheap but neither is free.  Forwards needs
`lt_blockHi_of_two_mul_le` — a survivor has `2p ≤ x`, which is what puts
it strictly below the top block.  Backwards needs only `2p ≤ x ⟹ p ≤ x`,
since `blockLo x 1 = 1` already supplies the lower bound.

This is the join between N18 (which produces the survivor set) and
`sum_block_split_filter` (which consumes a tiled one). -/
theorem survivor_eq_blocks (x y K : ℕ)
    (hK : Real.exp (-(K:ℝ)) * Real.log (x:ℝ) < Real.log 2) :
    (((Finset.Icc 1 x).filter Nat.Prime).filter (fun p => ¬ p < y)).filter
        (fun p => ¬ x < 2*p)
      = ((Finset.Ico (blockLo x 1) (blockHi x K)).filter Nat.Prime).filter
          (fun p => ¬ p < y ∧ ¬ x < 2*p) := by
  classical
  rw [blockLo_one]
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨⟨⟨hp1, hpx⟩, hpp⟩, hyp⟩, h2p⟩
    have hp2 : 2 ≤ p := hpp.two_le
    have hx2 : 2 ≤ x := by omega
    exact ⟨⟨⟨by omega, lt_blockHi_of_two_mul_le x K p hx2 (by omega) hK⟩, hpp⟩,
      hyp, h2p⟩
  · rintro ⟨⟨⟨hp1, _⟩, hpp⟩, hyp, h2p⟩
    exact ⟨⟨⟨⟨by omega, by omega⟩, hpp⟩, hyp⟩, h2p⟩

open Finset in
/-- **The survivor sum decomposes over blocks** (Track R, N25): N25's
set identity fed through `sum_block_split_filter`.  This is the shape
§3's capstone consumes — the mean value, after the discards, is a sum of
`K` per-block contributions, each of which `iteration_diff_le` and
`tripleConv_block_le'` can then bound. -/
theorem survivor_sum_split {M : Type*} [AddCommMonoid M] (g : ℕ → M)
    (x y K : ℕ) (hx : 1 ≤ x)
    (hK : Real.exp (-(K:ℝ)) * Real.log (x:ℝ) < Real.log 2) :
    ∑ p ∈ (((Finset.Icc 1 x).filter Nat.Prime).filter
        (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p), g p
      = ∑ k ∈ Finset.Icc 1 K,
          ∑ p ∈ ((Finset.Ico (blockLo x k) (blockHi x k)).filter
            Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p), g p := by
  classical
  rw [survivor_eq_blocks x y K hK]
  exact sum_block_split_filter g _ x hx K

open Finset in
/-- **The mean value, block by block** (Track R, N26): N18's discard
estimate with its survivor sum tiled,

  `|S(x)·log x − ∑_{k=1}^{K} ∑_{p ∈ block k, survivor} (log p·f p)·∑_{m ≤ x/p} f(m)|
     ≤ 9x + x·(log y + 2) + (x+1)·log 4`.

This is §3's mean value in the form the per-block machinery consumes:
`iteration_diff_le` replaces each inner sum by its iterated form, and
`tripleConv_block_le'` then bounds the result on each block, with the
`k`-sum converging by `sum_exp_neg_tail_le`.

The rewrite is free — all the content is in N18 and `survivor_sum_split`;
the point is that the two fit together with no residue. -/
theorem sum_after_discards_blocks (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (hmul : ∀ a b, f (a*b) = f a * f b) (x y K : ℕ) (hx : 1 ≤ x) (hy : 2 ≤ y)
    (hyx : 2*y ≤ x)
    (hK : Real.exp (-(K:ℝ)) * Real.log (x:ℝ) < Real.log 2) :
    |(∑ n ∈ Finset.Icc 1 x, f n) * Real.log (x:ℝ)
        - ∑ k ∈ Finset.Icc 1 K,
            ∑ p ∈ ((Finset.Ico (blockLo x k) (blockHi x k)).filter
              Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p),
              (Real.log (p:ℝ) * f p) * ∑ m ∈ Finset.Icc 1 (x/p), f m|
      ≤ 9*(x:ℝ) + (x:ℝ)*(Real.log (y:ℝ) + 2) + ((x:ℝ)+1)*Real.log 4 := by
  classical
  rw [← survivor_sum_split
    (fun p => (Real.log (p:ℝ) * f p) * ∑ m ∈ Finset.Icc 1 (x/p), f m)
    x y K hx hK]
  exact sum_after_discards f hf hmul x y hx hy hyx

open Finset in
/-- **Survivors sit below `x/2`** (Track R, N27): the discard
`¬ x < 2p` puts every survivor in `[1, x/2]`, so the global mass
estimates apply to them. -/
theorem survivor_subset_half (x y : ℕ) :
    (((Finset.Icc 1 x).filter Nat.Prime).filter (fun p => ¬ p < y)).filter
        (fun p => ¬ x < 2*p)
      ⊆ (Finset.Icc 1 (x/2)).filter Nat.Prime := by
  classical
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  obtain ⟨⟨⟨⟨hp1, _⟩, hpp⟩, _⟩, h2p⟩ := hp
  exact ⟨⟨hp1, Nat.le_div_iff_mul_le (by norm_num) |>.mpr (by omega)⟩, hpp⟩

open Finset in
/-- **The blocks reassemble** (Track R, N27):
`∑_{k=1}^{K} tripleConv f x (block k ∩ survivors) = tripleConv f x survivors`.

`tripleConv` is a sum over its index set, so the tiling passes straight
through it.  Worth stating separately because it is what shows the block
decomposition is *lossless*: §4 will estimate the blocks one at a time,
and this is the identity that puts them back together. -/
theorem sum_tripleConv_blocks_eq (f : ℕ → ℝ) (x y K : ℕ) (hx : 1 ≤ x)
    (hK : Real.exp (-(K:ℝ)) * Real.log (x:ℝ) < Real.log 2) :
    ∑ k ∈ Finset.Icc 1 K,
        tripleConv f x (((Finset.Ico (blockLo x k) (blockHi x k)).filter
          Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p))
      = tripleConv f x ((((Finset.Icc 1 x).filter Nat.Prime).filter
          (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p)) := by
  classical
  rw [tripleConv]
  rw [survivor_sum_split
    (fun p => (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
      * ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
          * ∑ n ∈ Finset.Icc 1 (x/(p*q)), f n) x y K hx hK]
  rfl

open Finset in
/-- **The iteration difference, over the survivors** (Track R, N27):

  `|∑_{surv} (log p·f p)·∑_{m ≤ x/p} f(m) − tripleConv f x surv|
     ≤ 120·x·∑_{j ≤ log₂ x} 1/j + 2·∑_{surv} log p`.

`iteration_diff_le` applied to the survivor set, with its first error
term discharged by `sum_log_div_mul_log_ratio_le`.  The blocks are not
needed here — the difference is bounded globally, and the tiling is only
required later, for the `L`-series estimate of §4.

The `∑_j 1/j` is `≍ log log x`, so this whole term is
`O(x·log log x)` — negligible against the `x·log x` the identity
produces. -/
theorem iteration_diff_survivors_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (hmul : ∀ a b, f (a*b) = f a * f b) (x y : ℕ) :
    |∑ p ∈ (((Finset.Icc 1 x).filter Nat.Prime).filter
          (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p),
          (Real.log (p:ℝ) * f p) * (∑ m ∈ Finset.Icc 1 (x/p), f m)
        - tripleConv f x ((((Finset.Icc 1 x).filter Nat.Prime).filter
            (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p))|
      ≤ 120 * (x:ℝ) * (∑ j ∈ Finset.Icc 1 (Nat.log 2 x), 1/(j:ℝ))
          + 2 * ∑ p ∈ (((Finset.Icc 1 x).filter Nat.Prime).filter
              (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p),
              Real.log (p:ℝ) := by
  classical
  set S : Finset ℕ := (((Finset.Icc 1 x).filter Nat.Prime).filter
    (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p) with hS_def
  have hmem : ∀ p ∈ S, p.Prime ∧ 2*p ≤ x := by
    intro p hp
    rw [hS_def] at hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨_, hpp⟩, _⟩, h2p⟩ := hp
    exact ⟨hpp, by omega⟩
  have hx0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
  -- the mass term, bounded globally
  have hnn : ∀ p ∈ (Finset.Icc 1 (x/2)).filter Nat.Prime,
      (0:ℝ) ≤ Real.log (p:ℝ) / ((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hp1, hph⟩, hpp⟩ := hp
    have h2p : 2*p ≤ x := by
      have := Nat.div_mul_le_self x 2
      omega
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp1
    have hquot : (2:ℝ) ≤ (x:ℝ)/(p:ℝ) := by
      rw [le_div_iff₀ hp0]
      have hc : ((2*p : ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast h2p
      push_cast at hc; linarith
    have hlogpos : (0:ℝ) < Real.log ((x:ℝ)/(p:ℝ)) := Real.log_pos (by linarith)
    exact div_nonneg (Real.log_natCast_nonneg p) (by positivity)
  have hmass : ∑ p ∈ S, Real.log (p:ℝ) / ((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ)))
      ≤ 12 * ∑ j ∈ Finset.Icc 1 (Nat.log 2 x), 1/(j:ℝ) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (survivor_subset_half x y) (fun i hi _ => hnn i hi)) ?_
    exact sum_log_div_mul_log_ratio_le x
  refine le_trans (iteration_diff_le f hf hmul x S hmem) ?_
  have hstep : 10 * (x:ℝ)
      * (∑ p ∈ S, Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
      ≤ 10 * (x:ℝ) * (12 * ∑ j ∈ Finset.Icc 1 (Nat.log 2 x), 1/(j:ℝ)) := by
    refine mul_le_mul_of_nonneg_left hmass (by linarith)
  linarith [hstep]

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **Lemma 1 of GHS κ=1, in the `n^{−1−it}` normalisation** (Track R,
N28): for coefficients supported above `N`,

  `∫_{−T}^{T} |∑ b(n)Λ(n)·n^{−1}·e(−ξ log n)|² dξ
     ≤ (e^π·T·Q/N)·∑ ‖b(m)‖²Λ(m)/m`.

`intervalIntegral_vonMangoldt_mvt_le` with `a n := b n / n`.  The
substitution alone gives `∑ ‖b(m)‖²Λ(m)/m²`; the paper's shape has a
single power of `m`, and the missing factor is recovered from
`N < m`, which turns `1/m² ≤ 1/(N·m)`.

So this is *not* a free rewrite of Lemma 2.6 — it needs the support
restriction, which is why GHS state their Lemma 1 with the range
`T² ≤ n ≤ x` rather than for arbitrary coefficients.  On a dyadic block
the `N` here cancels against the `Q ≍ N/T` of
`intervalIntegral_vonMangoldt_mvt_block_le`, reproducing the paper's
constant. -/
theorem intervalIntegral_vonMangoldt_inv_mvt_le (T : ℝ) (hT : 0 < T)
    (N : ℕ) (hN : 1 ≤ N) (S : Finset ℕ) (hS : ∀ m ∈ S, N < m) (b : ℕ → ℂ)
    (Q : ℝ) (hQ0 : 0 ≤ Q)
    (hQ : ∀ m ∈ S, ∑ n ∈ S, vonMangoldt n
        * Real.exp (-(π*T^2*(Real.log (m:ℝ) - Real.log (n:ℝ))^2)) ≤ Q) :
    (∫ ξ in (-T)..T, ‖∑ n ∈ S, ((b n / (n:ℂ)) * ((vonMangoldt n : ℝ) : ℂ))
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
      ≤ Real.exp π * T * Q / (N:ℝ)
          * ∑ m ∈ S, ‖b m‖^2 * vonMangoldt m / (m:ℝ) := by
  classical
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hcoef : (0:ℝ) ≤ Real.exp π * T * Q := by positivity
  have hinner : ∑ m ∈ S, ‖b m / (m:ℂ)‖^2 * vonMangoldt m
      ≤ (1/(N:ℝ)) * ∑ m ∈ S, ‖b m‖^2 * vonMangoldt m / (m:ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    have hmN : N < m := hS m hm
    have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hmR : (N:ℝ) ≤ (m:ℝ) := by exact_mod_cast hmN.le
    have hL : (0:ℝ) ≤ vonMangoldt m := vonMangoldt_nonneg
    have hnorm : ‖b m / (m:ℂ)‖^2 = ‖b m‖^2 / (m:ℝ)^2 := by
      rw [norm_div, div_pow, Complex.norm_natCast]
    rw [hnorm, div_mul_eq_mul_div, one_div, inv_mul_eq_div, div_div]
    have hA : (0:ℝ) ≤ ‖b m‖^2 * vonMangoldt m := mul_nonneg (sq_nonneg _) hL
    have hpos1 : (0:ℝ) < (m:ℝ)^2 := by positivity
    have hpos2 : (0:ℝ) < (m:ℝ)*(N:ℝ) := by positivity
    rw [div_le_div_iff₀ hpos1 hpos2]
    nlinarith [hA, mul_le_mul_of_nonneg_left hmR hm0.le]
  refine le_trans
    (intervalIntegral_vonMangoldt_mvt_le T hT S (fun n => b n / (n:ℂ)) Q hQ) ?_
  calc Real.exp π * T * Q * ∑ m ∈ S, ‖b m / (m:ℂ)‖^2 * vonMangoldt m
      ≤ Real.exp π * T * Q
          * ((1/(N:ℝ)) * ∑ m ∈ S, ‖b m‖^2 * vonMangoldt m / (m:ℝ)) :=
        mul_le_mul_of_nonneg_left hinner hcoef
    _ = Real.exp π * T * Q / (N:ℝ)
          * ∑ m ∈ S, ‖b m‖^2 * vonMangoldt m / (m:ℝ) := by ring

open Finset Real in
/-- **The frequency range of Halász's `L(x)`** (Track R, N29): the
integers `N` with `|N| ≤ log²x + 1`, over which the unit-interval
suprema of `|F_x(1+it)|` are weighted. -/
noncomputable def halaszRange (x : ℕ) : Finset ℤ :=
  Finset.Icc (-(⌈(Real.log (x:ℝ))^2⌉ + 1)) (⌈(Real.log (x:ℝ))^2⌉ + 1)

open Finset Real in
/-- **`L(x)²`, parametrised by a dominating function** (Track R, N29):

  `L(x)² = ∑_{|N| ≤ log²x+1} B(N)²/(N²+1)`.

GHS define this with `B N = sup_{|t−N| ≤ 1/2} |F_x(1+it)|`.  Taking `B`
as a parameter instead of a supremum is deliberate: every use of `L(x)`
in the argument is an *upper* bound on the Cauchy–Schwarz factor `I₂`,
so any dominating `B` suffices, and the supremum is merely the least
such.  This avoids carrying `BddAbove` and measurability side conditions
through the whole of §4 for no gain.

`halaszLSq_mono` is what makes the parametrisation sound: a smaller
dominating function gives a smaller `L`. -/
noncomputable def halaszLSq (B : ℤ → ℝ) (x : ℕ) : ℝ :=
  ∑ N ∈ halaszRange x, (B N)^2 / ((N:ℝ)^2 + 1)

open Finset Real in
/-- `L(x)² ≥ 0` (Track R, N29): each weight `1/(N²+1)` is positive. -/
theorem halaszLSq_nonneg (B : ℤ → ℝ) (x : ℕ) : 0 ≤ halaszLSq B x := by
  refine Finset.sum_nonneg fun N _ => ?_
  have : (0:ℝ) < (N:ℝ)^2 + 1 := by positivity
  positivity

open Finset Real in
/-- **`L` is monotone in the dominating function** (Track R, N29).  This
is the lemma that justifies parametrising by `B` rather than taking a
supremum: a bound proved for any dominating `B` transfers to the
smallest one. -/
theorem halaszLSq_mono (B₁ B₂ : ℤ → ℝ) (x : ℕ) (h : ∀ N, |B₁ N| ≤ |B₂ N|) :
    halaszLSq B₁ x ≤ halaszLSq B₂ x := by
  refine Finset.sum_le_sum fun N _ => ?_
  have hden : (0:ℝ) < (N:ℝ)^2 + 1 := by positivity
  refine div_le_div_of_nonneg_right ?_ hden.le
  calc (B₁ N)^2 = |B₁ N|^2 := (sq_abs _).symm
    _ ≤ |B₂ N|^2 := by nlinarith [abs_nonneg (B₁ N), abs_nonneg (B₂ N), h N]
    _ = (B₂ N)^2 := sq_abs _

open Finset Real in
/-- **The Halász weights have bounded total mass** (Track R, N30):

  `∑_{|N| ≤ M} 1/(N²+1) ≤ 6`,  uniformly in `M`.

This is what makes `L(x)` a genuine `ℓ²` quantity rather than a
`log`-growing one: the number of frequencies is `≍ log²x`, but their
weights sum to `O(1)`, so a uniform bound on the suprema gives a uniform
bound on `L(x)`.

The proof fibres `[−M, M] ∩ ℤ` over `|N|`: each fibre is contained in
`{n, −n}`, so has at most two elements, and `1/(N²+1)` is constant on
it.  The resulting `∑_{n ≤ M} 2/(n²+1)` splits as the `n = 0` term plus
`2·∑_{n ≥ 1} 1/n² ≤ 4`. -/
theorem sum_inv_sq_add_one_Icc_le (M : ℕ) :
    ∑ N ∈ Finset.Icc (-(M:ℤ)) (M:ℤ), 1/((N:ℝ)^2+1) ≤ 6 := by
  classical
  have hmaps : ∀ N ∈ Finset.Icc (-(M:ℤ)) (M:ℤ), N.natAbs ∈ Finset.Icc 0 M := by
    intro N hN
    simp only [Finset.mem_Icc] at hN ⊢
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hinner : ∀ n ∈ Finset.Icc 0 M,
      ∑ N ∈ (Finset.Icc (-(M:ℤ)) (M:ℤ)).filter (fun N => N.natAbs = n),
          1/((N:ℝ)^2+1)
        ≤ 2 * (1/((n:ℝ)^2+1)) := by
    intro n _
    have heq : ∀ N ∈ (Finset.Icc (-(M:ℤ)) (M:ℤ)).filter (fun N => N.natAbs = n),
        1/((N:ℝ)^2+1) = 1/((n:ℝ)^2+1) := by
      intro N hN
      simp only [Finset.mem_filter] at hN
      rcases Int.natAbs_eq_iff.mp hN.2 with h | h <;> subst h <;> push_cast <;>
        ring
    rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul]
    have hsub : (Finset.Icc (-(M:ℤ)) (M:ℤ)).filter (fun N => N.natAbs = n)
        ⊆ ({(n:ℤ), -(n:ℤ)} : Finset ℤ) := by
      intro N hN
      simp only [Finset.mem_filter] at hN
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Int.natAbs_eq_iff.mp hN.2
    have hcard : (((Finset.Icc (-(M:ℤ)) (M:ℤ)).filter
        (fun N => N.natAbs = n)).card : ℝ) ≤ 2 := by
      have h1 := Finset.card_le_card hsub
      have h2 : ({(n:ℤ), -(n:ℤ)} : Finset ℤ).card ≤ 2 :=
        le_trans (Finset.card_insert_le _ _) (by simp)
      have : ((Finset.Icc (-(M:ℤ)) (M:ℤ)).filter
        (fun N => N.natAbs = n)).card ≤ 2 := le_trans h1 h2
      exact_mod_cast this
    have hpos : (0:ℝ) < (n:ℝ)^2+1 := by positivity
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  refine le_trans (Finset.sum_le_sum hinner) ?_
  -- split off n = 0 and telescope the rest
  have h0 : Finset.Icc 0 M = insert 0 (Finset.Icc 1 M) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hsplit : ∑ n ∈ Finset.Icc 0 M, 2 * (1/((n:ℝ)^2+1))
      = 2 + ∑ n ∈ Finset.Icc 1 M, 2 * (1/((n:ℝ)^2+1)) := by
    rw [h0, Finset.sum_insert (by simp)]
    norm_num
  rw [hsplit]
  have htail : ∑ n ∈ Finset.Icc 1 M, 2 * (1/((n:ℝ)^2+1))
      ≤ 2 * ∑ n ∈ Finset.Icc 1 M, (1:ℝ)/(n:ℝ)^2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    simp only [Finset.mem_Icc] at hn
    have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn.1
    have h1 : (0:ℝ) < (n:ℝ)^2 := by positivity
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [div_le_div_iff₀ (by positivity) h1]
    nlinarith
  have hbase := sum_one_div_sq_le_two (Finset.Icc 1 M)
  linarith [htail, hbase]

open Finset Real in
/-- **The Perron weight is comparable to the Halász weight** (Track R,
N31): if `|t − N| ≤ 1/2` then `1/(1+t²) ≤ 5/(N²+1)`.

§4's factor `I₂` carries `|ds|/|s|²` with `s = 1+it`, so `|s|² = 1+t²`;
`L(x)` carries `1/(N²+1)`.  This is the comparison that lets the
integral over the unit interval around `N` be charged to the `N`-th
Halász weight.

The constant `5` is not optimal but is uniform, which is all that is
needed: the worst case is `|N| = 1`, where `1+t²` can be as small as
`5/4` while `(N²+1) = 2`. -/
theorem inv_one_add_sq_le_halasz_weight (t : ℝ) (N : ℤ) (h : |t - (N:ℝ)| ≤ 1/2) :
    1/(1+t^2) ≤ 5/((N:ℝ)^2+1) := by
  have hd : (t - (N:ℝ))^2 ≤ 1/4 := by
    have := abs_nonneg (t - (N:ℝ))
    nlinarith [sq_abs (t - (N:ℝ))]
  have h1 : (0:ℝ) < 1 + t^2 := by positivity
  have h2 : (0:ℝ) < (N:ℝ)^2 + 1 := by positivity
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [hd, sq_nonneg (3*t - (N:ℝ)), sq_nonneg t, sq_nonneg (t - (N:ℝ))]

open Finset Real in
/-- **A uniform bound on the suprema bounds `L`** (Track R, N31): if
`|B N| ≤ C` throughout the Halász range then `L(x)² ≤ 6C²`.

This is the payoff of `sum_inv_sq_add_one_Icc_le`.  The range has
`≍ log²x` frequencies, so a naive termwise bound would give
`L(x)² ≪ C²log²x`; because the weights have total mass `O(1)`, the
`log` disappears entirely and `L(x) ≪ C`.  That is exactly what makes
Halász's theorem sharp rather than log-lossy. -/
theorem halaszLSq_le_of_bound (B : ℤ → ℝ) (x : ℕ) (C : ℝ)
    (hB : ∀ N ∈ halaszRange x, |B N| ≤ C) :
    halaszLSq B x ≤ 6 * C^2 := by
  classical
  have hc0 : (0:ℤ) ≤ ⌈(Real.log (x:ℝ))^2⌉ := Int.ceil_nonneg (sq_nonneg _)
  set M : ℕ := (⌈(Real.log (x:ℝ))^2⌉ + 1).toNat with hM_def
  have hMcast : ((M:ℕ):ℤ) = ⌈(Real.log (x:ℝ))^2⌉ + 1 := by
    rw [hM_def]; exact Int.toNat_of_nonneg (by omega)
  have hrange : halaszRange x = Finset.Icc (-(M:ℤ)) (M:ℤ) := by
    rw [halaszRange, hMcast]
  -- termwise: B(N)²/(N²+1) ≤ C²·(1/(N²+1))
  have hterm : ∀ N ∈ halaszRange x,
      (B N)^2 / ((N:ℝ)^2 + 1) ≤ C^2 * (1/((N:ℝ)^2+1)) := by
    intro N hN
    have hden : (0:ℝ) < (N:ℝ)^2 + 1 := by positivity
    have hsq : (B N)^2 ≤ C^2 := by
      have h1 := hB N hN
      have h2 : (0:ℝ) ≤ |B N| := abs_nonneg _
      nlinarith [sq_abs (B N)]
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right hsq hden.le
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum, hrange]
  have hC2 : (0:ℝ) ≤ C^2 := sq_nonneg C
  have hw := sum_inv_sq_add_one_Icc_le M
  nlinarith [hw, hC2]

open MeasureTheory Real Complex Finset in
/-- **The unit-interval estimate** (Track R, N32): on an interval where
`‖F‖ ≤ b`,

  `∫ G·‖F‖² ≤ b²·∫ G`,

for any nonnegative `G`.

This is the step in §4 that replaces `|F_x(1+it)|²` by its supremum over
the unit interval around `N` — the move that turns the Perron integral
into the `ℓ²` quantity `L(x)`.  Stating it for a *bound* `b` rather than
a supremum is what keeps `L(x)`'s parametrisation by a dominating
function usable here.

Integrability is taken as a hypothesis rather than derived: the
integrand's regularity comes from whichever Dirichlet polynomial is
substituted for `F` downstream, and proving it once there is cheaper
than carrying a continuity assumption through the whole section. -/
theorem integral_unit_interval_le (G : ℝ → ℝ) (F : ℝ → ℂ) (N : ℤ) (b : ℝ)
    (hG : ∀ t, 0 ≤ G t) (hb : 0 ≤ b)
    (hF : ∀ t ∈ Set.Icc ((N:ℝ) - 1/2) ((N:ℝ) + 1/2), ‖F t‖ ≤ b)
    (hint1 : IntervalIntegrable (fun t => G t * ‖F t‖^2) volume
      ((N:ℝ) - 1/2) ((N:ℝ) + 1/2))
    (hint2 : IntervalIntegrable G volume ((N:ℝ) - 1/2) ((N:ℝ) + 1/2)) :
    (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), G t * ‖F t‖^2)
      ≤ b^2 * ∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), G t := by
  have hle : ((N:ℝ) - 1/2) ≤ ((N:ℝ) + 1/2) := by linarith
  have hmono : ∀ t ∈ Set.Icc ((N:ℝ) - 1/2) ((N:ℝ) + 1/2),
      G t * ‖F t‖^2 ≤ b^2 * G t := by
    intro t ht
    have h1 : ‖F t‖ ≤ b := hF t ht
    have h2 : (0:ℝ) ≤ ‖F t‖ := norm_nonneg _
    have h3 : ‖F t‖^2 ≤ b^2 := by nlinarith
    have h4 : (0:ℝ) ≤ G t := hG t
    nlinarith [h3, h4]
  have hcm : IntervalIntegrable (fun t => b^2 * G t) volume
      ((N:ℝ) - 1/2) ((N:ℝ) + 1/2) := hint2.const_mul _
  refine le_trans (intervalIntegral.integral_mono_on hle hint1 hcm hmono) ?_
  rw [intervalIntegral.integral_const_mul]

open MeasureTheory Real Complex Finset in
/-- **The Cauchy–Schwarz factor `I₂`, bounded by `L(x)`** (Track R, N33):

  `∑_{N} ∫_{N−1/2}^{N+1/2} (‖D(t)‖²/(1+t²))·‖F(t)‖² dt ≤ 5·V·L(x)²`,

where `V` bounds `∫ ‖D‖²` on each unit interval and `B` dominates `‖F‖`
on it.

This is the heart of §4's `I₂` estimate.  Three things combine: `F` is
replaced by its bound on each unit interval (`integral_unit_interval_le`),
the Perron weight `1/(1+t²)` is charged to the Halász weight
`1/(N²+1)` (`inv_one_add_sq_le_halasz_weight`), and what remains is
exactly `∑ B(N)²/(N²+1) = L(x)²`.

Downstream `V` comes from Lemma 1 — for `D` a prime-supported Dirichlet
polynomial over `q ≤ x^{e^{1−k}}` it is `≪ ∑_{q} log q/q ≪ e^{−k}log x`,
which is where the `e^{−k}` that cancels against `I₁` is produced. -/
theorem sum_unit_interval_halasz_le (D Fn : ℝ → ℂ) (B : ℤ → ℝ) (x : ℕ)
    (V : ℝ)
    (hB : ∀ N ∈ halaszRange x, ∀ t ∈ Set.Icc ((N:ℝ) - 1/2) ((N:ℝ) + 1/2),
      ‖Fn t‖ ≤ B N)
    (hB0 : ∀ N, 0 ≤ B N)
    (hV : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), ‖D t‖^2) ≤ V)
    (hi1 : ∀ N ∈ halaszRange x, IntervalIntegrable
      (fun t => (‖D t‖^2/(1+t^2)) * ‖Fn t‖^2) volume
      ((N:ℝ) - 1/2) ((N:ℝ) + 1/2))
    (hi2 : ∀ N ∈ halaszRange x, IntervalIntegrable
      (fun t => ‖D t‖^2/(1+t^2)) volume ((N:ℝ) - 1/2) ((N:ℝ) + 1/2))
    (hi3 : ∀ N ∈ halaszRange x, IntervalIntegrable
      (fun t => ‖D t‖^2) volume ((N:ℝ) - 1/2) ((N:ℝ) + 1/2)) :
    ∑ N ∈ halaszRange x,
        (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), (‖D t‖^2/(1+t^2)) * ‖Fn t‖^2)
      ≤ 5 * V * halaszLSq B x := by
  classical
  have hterm : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), (‖D t‖^2/(1+t^2)) * ‖Fn t‖^2)
        ≤ 5 * V * ((B N)^2 / ((N:ℝ)^2 + 1)) := by
    intro N hN
    have hle : ((N:ℝ) - 1/2) ≤ ((N:ℝ) + 1/2) := by linarith
    have hden : (0:ℝ) < (N:ℝ)^2 + 1 := by positivity
    -- (1) replace ‖Fn‖ by its bound on the interval
    have hstep1 := integral_unit_interval_le
      (fun t => ‖D t‖^2/(1+t^2)) Fn N (B N)
      (fun t => by positivity) (hB0 N) (hB N hN) (hi1 N hN) (hi2 N hN)
    -- (2) charge the Perron weight to the Halász weight
    have hpt : ∀ t ∈ Set.Icc ((N:ℝ) - 1/2) ((N:ℝ) + 1/2),
        ‖D t‖^2/(1+t^2) ≤ (5/((N:ℝ)^2+1)) * ‖D t‖^2 := by
      intro t ht
      have habs : |t - (N:ℝ)| ≤ 1/2 :=
        abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hw := inv_one_add_sq_le_halasz_weight t N habs
      have hD : (0:ℝ) ≤ ‖D t‖^2 := by positivity
      have ht2 : (0:ℝ) < 1 + t^2 := by positivity
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hw hD |>.trans_eq (by ring)
    have hcm : IntervalIntegrable (fun t => (5/((N:ℝ)^2+1)) * ‖D t‖^2) volume
        ((N:ℝ) - 1/2) ((N:ℝ) + 1/2) := (hi3 N hN).const_mul _
    have hstep2 : (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), ‖D t‖^2/(1+t^2))
        ≤ (5/((N:ℝ)^2+1)) * V := by
      refine le_trans (intervalIntegral.integral_mono_on hle (hi2 N hN) hcm hpt) ?_
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hV N hN) (by positivity)
    -- combine
    have hBsq : (0:ℝ) ≤ (B N)^2 := sq_nonneg _
    calc (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), (‖D t‖^2/(1+t^2)) * ‖Fn t‖^2)
        ≤ (B N)^2 * ∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), ‖D t‖^2/(1+t^2) :=
          hstep1
      _ ≤ (B N)^2 * ((5/((N:ℝ)^2+1)) * V) :=
          mul_le_mul_of_nonneg_left hstep2 hBsq
      _ = 5 * V * ((B N)^2 / ((N:ℝ)^2 + 1)) := by field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  exact le_of_eq rfl

open Finset Real in
/-- **`log(x/p)` is bounded below on a block** (Track R, N34): for
`p < blockHi x k`,

  `e^{−k}·log x ≤ log(x/p)`.

This is the inequality the whole block decomposition exists to provide.
Across `P_k` the quantity `log(x/p)` is essentially constant — bounded
below here and above by `e·e^{−k}·log x` at the other endpoint — so the
factor `1/log(x/p)` appearing in the Ramaré/Halász identity can be
pulled out of the `p`-sum at a bounded cost.  Without the blocks it
varies over the whole range `[1, log x]` and no such extraction is
possible.

Note that `p < blockHi x k` is exactly `(p:ℝ) < x^{1−e^{−k}}` via
`Nat.lt_ceil`, which is why the blocks are defined with `⌈·⌉₊` and
half-open intervals. -/
theorem exp_neg_mul_log_le_log_ratio (x k p : ℕ) (hx : 2 ≤ x) (hp : 1 ≤ p)
    (hpk : p < blockHi x k) :
    Real.exp (-(k:ℝ)) * Real.log (x:ℝ) ≤ Real.log ((x:ℝ)/(p:ℝ)) := by
  have hx0 : (0:ℝ) < (x:ℝ) := by
    have : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
    linarith
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
  have hlt : (p:ℝ) < (x:ℝ) ^ (1 - Real.exp (-(k:ℝ))) := by
    rw [blockHi] at hpk
    exact Nat.lt_ceil.mp hpk
  have hlog : Real.log (p:ℝ) ≤ (1 - Real.exp (-(k:ℝ))) * Real.log (x:ℝ) := by
    have h1 : Real.log (p:ℝ) ≤ Real.log ((x:ℝ) ^ (1 - Real.exp (-(k:ℝ)))) :=
      Real.log_le_log hp0 hlt.le
    rwa [Real.log_rpow hx0] at h1
  rw [Real.log_div (ne_of_gt hx0) (ne_of_gt hp0)]
  nlinarith [hlog]

open Finset in
/-- **The `I₁` mass over a block** (Track R, N34):

  `∑_{p ∈ P} log p/(p·log²(x/p)) ≤ (e^{2k}/log²x)·∑_{p ∈ P} log p/p`

for any set of primes inside the `k`-th block.  Squaring the previous
lemma turns the `log²(x/p)` in the denominator into the constant
`e^{-2k}·log²x`, leaving a plain Mertens mass — which
`sum_log_div_Ico_le_log` bounds by `≍ e^{−k}·log x`, giving
`I₁ ≪ e^{k}/log x` overall.

Against `I₂ ≪ L(x)²·e^{−k}·log x` the `e^{±k}` and `log x` both cancel
in `√(I₁·I₂)`, which is why §4 produces `L(x)` with no residual `k`. -/
theorem sum_log_div_sq_ratio_block_le (x k : ℕ) (hx : 2 ≤ x) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p < blockHi x k) :
    ∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * (Real.log ((x:ℝ)/(p:ℝ)))^2)
      ≤ (Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
          * ∑ p ∈ P, Real.log (p:ℝ)/(p:ℝ) := by
  classical
  have hxR : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hlogx : (0:ℝ) < Real.log (x:ℝ) := Real.log_pos (by linarith)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨hpp, hpk⟩ := hP p hp
  have hp1 : 1 ≤ p := hpp.one_lt.le
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp1
  have hlogp : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
  have hlow := exp_neg_mul_log_le_log_ratio x k p hx hp1 hpk
  have hepos : (0:ℝ) < Real.exp (-(k:ℝ)) := Real.exp_pos _
  have hratio0 : (0:ℝ) < Real.exp (-(k:ℝ)) * Real.log (x:ℝ) := by positivity
  have hsq : (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))^2
      ≤ (Real.log ((x:ℝ)/(p:ℝ)))^2 := by nlinarith [hlow, hratio0]
  have hden0 : (0:ℝ) < (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))^2 := by positivity
  have hkey : Real.log (p:ℝ)/((p:ℝ) * (Real.log ((x:ℝ)/(p:ℝ)))^2)
      ≤ Real.log (p:ℝ)/((p:ℝ) * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))^2) := by
    refine div_le_div_of_nonneg_left hlogp (by positivity) ?_
    nlinarith [hsq, hp0]
  refine le_trans hkey (le_of_eq ?_)
  rw [Real.exp_neg]
  field_simp
  congr 1
  rw [sq, ← Real.exp_add]
  ring_nf

open Finset in
/-- **The `I₁` estimate** (Track R, N35): for any set of primes inside
the `k`-th block,

  `∑_{p ∈ P} log p/(p·log²(x/p))
     ≤ (e^{2k}/log²x)·(4·((e−1)e^{−k}·log x + log 2) + 4·log 4)`,

whose leading term is `4(e−1)·e^{k}/log x`.

This is GHS §4's `I₁ ≪ e^{k}/log x`.  Two ingredients: the block lower
bound on `log(x/p)` (`sum_log_div_sq_ratio_block_le`) converts the
squared denominator into the constant `e^{−2k}log²x`, and the remaining
Mertens mass over the block is `≍ (e−1)e^{−k}·log x`.

The additive `4·log 4` is an artifact of the elementary Mertens bound —
the paper absorbs it into `≍`.  It survives here as a term
`≪ e^{2k}/log²x`, which against `I₂ ≪ L(x)²e^{−k}log x` contributes
`≪ L(x)²·e^{k}/log x` to `I₁·I₂`; on the range `k ≤ log(100 log x/L(x))`
where §4 is applied this is `≪ L(x)`, so `√(I₁I₂) ≪ L(x) + 1`.  That is
exactly the shape (3.2) allows, so the constant costs nothing. -/
theorem sum_log_div_sq_ratio_block_mass_le (x k : ℕ) (hx : 2 ≤ x) (hk : 1 ≤ k)
    (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k) :
    ∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * (Real.log ((x:ℝ)/(p:ℝ)))^2)
      ≤ (Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
          * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
              + Real.log 2) + 4 * Real.log 4) := by
  classical
  have hx1 : 1 ≤ x := by omega
  have hxR : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hlogx : (0:ℝ) < Real.log (x:ℝ) := Real.log_pos (by linarith)
  obtain ⟨hlo1, hlohi⟩ := blockLo_le_blockHi x k hx1
  -- the squared-denominator step
  have hstep := sum_log_div_sq_ratio_block_le x k hx P
    (fun p hp => ⟨(hP p hp).1, (hP p hp).2.2⟩)
  refine le_trans hstep ?_
  -- the block Mertens mass
  have hsub : P ⊆ (Finset.Ico (blockLo x k) (blockHi x k)).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpp, hlo, hhi⟩ := hP p hp
    simp only [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨hlo, hhi⟩, hpp⟩
  have hmono : ∑ p ∈ P, Real.log (p:ℝ)/(p:ℝ)
      ≤ ∑ p ∈ (Finset.Ico (blockLo x k) (blockHi x k)).filter Nat.Prime,
          Real.log (p:ℝ)/(p:ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => div_nonneg (Real.log_natCast_nonneg i) (Nat.cast_nonneg _))
  have hmass := sum_log_div_Ico_le_log (blockLo x k) (blockHi x k) hlo1 hlohi
  have hgeom := log_blockHi_sub_log_blockLo_le x k hx hk
  have hcoef : (0:ℝ) ≤ Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2 := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hcoef
  linarith [hmono, hmass, hgeom]

open MeasureTheory Real Finset in
/-- **The Cauchy–Schwarz step, in parametrised form** (Track R, N36):
for `λ > 0` and *any* real `A`, `G`,

  `∫ A·G ≤ (λ/2)·∫A² + (1/(2λ))·∫G²`.

GHS §4 bounds the Perron integral by `√(I₁·I₂)`.  That is this
inequality at the optimal `λ = √(I₂/I₁)`; keeping `λ` free instead is a
deliberate choice.

Mathlib's Hölder inequality is stated for `lintegral` over `ℝ≥0∞`, and
routing a Bochner interval integral through it costs far more than the
`√` is worth — especially since §4 never needs the optimal constant.
The final bound only has to reach `≪ L(x) + 1`, so a concrete `λ`
substituted downstream does the same work.

The pointwise inequality is `λA² + G²/λ − 2AG = (λA − G)²/λ ≥ 0`, which
needs no sign condition on `A` or `G` — only `λ > 0`. -/
theorem integral_mul_le_param (A G : ℝ → ℝ) (lam a b : ℝ) (hlam : 0 < lam)
    (hab : a ≤ b)
    (hi1 : IntervalIntegrable (fun t => A t * G t) volume a b)
    (hi2 : IntervalIntegrable (fun t => (A t)^2) volume a b)
    (hi3 : IntervalIntegrable (fun t => (G t)^2) volume a b) :
    (∫ t in a..b, A t * G t)
      ≤ (lam/2) * (∫ t in a..b, (A t)^2)
        + (1/(2*lam)) * (∫ t in a..b, (G t)^2) := by
  have hpt : ∀ t ∈ Set.Icc a b,
      A t * G t ≤ (lam/2) * (A t)^2 + (1/(2*lam)) * (G t)^2 := by
    intro t _
    have h2l : (0:ℝ) < 2*lam := by linarith
    rw [← sub_nonneg]
    have hexp : (lam/2) * (A t)^2 + (1/(2*lam)) * (G t)^2 - A t * G t
        = (lam * A t - G t)^2 / (2*lam) := by
      field_simp
      ring
    rw [hexp]
    positivity
  have hsum : IntervalIntegrable
      (fun t => (lam/2) * (A t)^2 + (1/(2*lam)) * (G t)^2) volume a b :=
    (hi2.const_mul _).add (hi3.const_mul _)
  refine le_trans (intervalIntegral.integral_mono_on hab hi1 hsum hpt) ?_
  rw [intervalIntegral.integral_add (hi2.const_mul _) (hi3.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

open MeasureTheory Real Complex Finset in
/-- **The `I₂` estimate against an abstract Perron weight** (Track R,
N39): if `W(t) ≤ C/(1+t²)` then

  `∑_N ∫_{N−1/2}^{N+1/2} ‖D(t)‖²·W(t)·‖F(t)‖² dt ≤ 5·C·V·L(x)²`.

`sum_unit_interval_halasz_le` with the contour weight `1/(1+t²)`
replaced by anything dominated by it.

Parametrising by `W` rather than by `‖𝓕V‖` is the same choice made for
`L(x)` itself: the estimate only ever needs an upper bound on the
weight, so the Fourier machinery stays out of the statement and the
caller supplies `W := ‖𝓕V‖` through
`ExpSums.fourier_window_le_inv_one_add_sq`.  It also means the lemma is
equally usable with the genuine contour kernel, should that ever be
preferred. -/
theorem sum_unit_interval_weight_halasz_le (D Fn : ℝ → ℂ) (W : ℝ → ℝ)
    (B : ℤ → ℝ) (x : ℕ) (C V : ℝ) (hC0 : 0 ≤ C)
    (hWle : ∀ t, W t ≤ C/(1+t^2))
    (hB : ∀ N ∈ halaszRange x, ∀ t ∈ Set.Icc ((N:ℝ) - 1/2) ((N:ℝ) + 1/2),
      ‖Fn t‖ ≤ B N)
    (hB0 : ∀ N, 0 ≤ B N)
    (hV : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), ‖D t‖^2) ≤ V)
    (hj : ∀ N ∈ halaszRange x, IntervalIntegrable
      (fun t => ‖D t‖^2 * W t * ‖Fn t‖^2) volume
      ((N:ℝ) - 1/2) ((N:ℝ) + 1/2))
    (hi1 : ∀ N ∈ halaszRange x, IntervalIntegrable
      (fun t => (‖D t‖^2/(1+t^2)) * ‖Fn t‖^2) volume
      ((N:ℝ) - 1/2) ((N:ℝ) + 1/2))
    (hi2 : ∀ N ∈ halaszRange x, IntervalIntegrable
      (fun t => ‖D t‖^2/(1+t^2)) volume ((N:ℝ) - 1/2) ((N:ℝ) + 1/2))
    (hi3 : ∀ N ∈ halaszRange x, IntervalIntegrable
      (fun t => ‖D t‖^2) volume ((N:ℝ) - 1/2) ((N:ℝ) + 1/2)) :
    ∑ N ∈ halaszRange x,
        (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), ‖D t‖^2 * W t * ‖Fn t‖^2)
      ≤ 5 * C * V * halaszLSq B x := by
  classical
  have hstep : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), ‖D t‖^2 * W t * ‖Fn t‖^2)
        ≤ C * ∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2),
            (‖D t‖^2/(1+t^2)) * ‖Fn t‖^2 := by
    intro N hN
    have hle : ((N:ℝ) - 1/2) ≤ ((N:ℝ) + 1/2) := by linarith
    have hpt : ∀ t ∈ Set.Icc ((N:ℝ) - 1/2) ((N:ℝ) + 1/2),
        ‖D t‖^2 * W t * ‖Fn t‖^2
          ≤ C * ((‖D t‖^2/(1+t^2)) * ‖Fn t‖^2) := by
      intro t _
      have hD : (0:ℝ) ≤ ‖D t‖^2 := by positivity
      have hF : (0:ℝ) ≤ ‖Fn t‖^2 := by positivity
      have hw := hWle t
      have heq : C * ((‖D t‖^2/(1+t^2)) * ‖Fn t‖^2)
          = ‖D t‖^2 * (C/(1+t^2)) * ‖Fn t‖^2 := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hw hD) hF
    have hcm : IntervalIntegrable
        (fun t => C * ((‖D t‖^2/(1+t^2)) * ‖Fn t‖^2)) volume
        ((N:ℝ) - 1/2) ((N:ℝ) + 1/2) := (hi1 N hN).const_mul _
    refine le_trans
      (intervalIntegral.integral_mono_on hle (hj N hN) hcm hpt) ?_
    rw [intervalIntegral.integral_const_mul]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  have hmain := sum_unit_interval_halasz_le D Fn B x V hB hB0 hV hi1 hi2 hi3
  calc C * ∑ N ∈ halaszRange x,
        (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), (‖D t‖^2/(1+t^2)) * ‖Fn t‖^2)
      ≤ C * (5 * V * halaszLSq B x) := mul_le_mul_of_nonneg_left hmain hC0
    _ = 5 * C * V * halaszLSq B x := by ring

open MeasureTheory Real Finset in
/-- **The unit-interval cover of a symmetric range** (Track R, N40):

  `∑_{|N| ≤ M} ∫_{N−1/2}^{N+1/2} g = ∫_{−M−1/2}^{M+1/2} g`.

The integers `N ∈ [−M, M]` have unit intervals that tile
`[−M−1/2, M+1/2]` exactly, so the decomposition is an identity, not an
estimate.

This is the join between the Perron pairing integral — produced over a
whole range by `norm_sum_translates_le_integral_char` — and the
per-interval estimates `sum_unit_interval_weight_halasz_le` consumes.
Without it the `ℓ²`-weighted argument has nothing to attach to.

`intervalIntegral.sum_integral_adjacent_intervals` supplies the tiling
over `Finset.range (2M+1)`; the work here is the reindexing to `ℤ`,
where the frequency `N` naturally lives. -/
theorem sum_unit_intervals_eq (g : ℝ → ℝ) (M : ℕ)
    (hint : ∀ i : ℕ, i < 2*M+1 → IntervalIntegrable g volume
      (-(M:ℝ) - 1/2 + i) (-(M:ℝ) - 1/2 + (i+1))) :
    ∑ N ∈ Finset.Icc (-(M:ℤ)) (M:ℤ),
        (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), g t)
      = ∫ t in (-(M:ℝ) - 1/2)..((M:ℝ) + 1/2), g t := by
  classical
  set a : ℕ → ℝ := fun i => -(M:ℝ) - 1/2 + i with ha_def
  have hadj := intervalIntegral.sum_integral_adjacent_intervals
    (a := a) (f := g) (μ := volume) (n := 2*M+1)
    (fun i hi => by simpa [ha_def, Nat.cast_add, Nat.cast_one] using hint i hi)
  have haend : a (2*M+1) = (M:ℝ) + 1/2 := by
    simp only [ha_def]
    push_cast
    ring
  have ha0 : a 0 = -(M:ℝ) - 1/2 := by simp [ha_def]
  rw [ha0, haend] at hadj
  rw [← hadj]
  refine Finset.sum_nbij' (i := fun N => (N + (M:ℤ)).toNat)
    (j := fun i => (i:ℤ) - (M:ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro N hN
    simp only [Finset.mem_Icc] at hN
    simp only [Finset.mem_range]
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Icc]
    omega
  · intro N hN
    simp only [Finset.mem_Icc] at hN
    show ((N + (M:ℤ)).toNat : ℤ) - (M:ℤ) = N
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    show ((((i:ℕ):ℤ) - (M:ℤ)) + (M:ℤ)).toNat = i
    omega
  · intro N hN
    simp only [Finset.mem_Icc] at hN
    have hcast : (((N + (M:ℤ)).toNat : ℕ) : ℝ) = (N:ℝ) + (M:ℝ) := by
      have : ((N + (M:ℤ)).toNat : ℤ) = N + (M:ℤ) :=
        Int.toNat_of_nonneg (by omega)
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
    have h1 : a ((N + (M:ℤ)).toNat) = (N:ℝ) - 1/2 := by
      simp only [ha_def, hcast]; ring
    have h2 : a ((N + (M:ℤ)).toNat + 1) = (N:ℝ) + 1/2 := by
      simp only [ha_def]
      push_cast [hcast]
      ring
    rw [h1, h2]

open Finset Real in
/-- **The half-width of the Halász range** (Track R, N41): the natural
number `M` with `halaszRange x = [−M, M] ∩ ℤ`, namely
`⌈log²x⌉ + 1`. -/
noncomputable def halaszM (x : ℕ) : ℕ := (⌈(Real.log (x:ℝ))^2⌉ + 1).toNat

open Finset Real in
/-- **The Halász range is a symmetric integer interval** (Track R,
N41): `halaszRange x = Finset.Icc (−halaszM x) (halaszM x)`.

`⌈log²x⌉ ≥ 0` always — including at `x = 0`, where `log 0 = 0` — so the
`toNat` is faithful and the range really is symmetric about the origin.

The fact was previously available only inside `halaszLSq_le_of_bound`'s
proof; stating it is what lets `sum_unit_intervals_eq` be applied to
the Halász range, which is the form §4 needs. -/
theorem halaszRange_eq_Icc (x : ℕ) :
    halaszRange x = Finset.Icc (-(halaszM x : ℤ)) ((halaszM x : ℤ)) := by
  have hc0 : (0:ℤ) ≤ ⌈(Real.log (x:ℝ))^2⌉ := Int.ceil_nonneg (sq_nonneg _)
  have hM : ((halaszM x : ℕ) : ℤ) = ⌈(Real.log (x:ℝ))^2⌉ + 1 := by
    rw [halaszM]
    exact Int.toNat_of_nonneg (by omega)
  rw [halaszRange, hM]

open MeasureTheory Real Finset in
/-- **The Halász range tiles an interval** (Track R, N41): combining
`halaszRange_eq_Icc` with `sum_unit_intervals_eq`,

  `∑_{N ∈ halaszRange x} ∫_{N−1/2}^{N+1/2} g = ∫_{−M−1/2}^{M+1/2} g`.

This is the identity that attaches the `ℓ²`-weighted per-interval
estimates to a single Perron integral over a range — the last
structural join in §4's `I₂` chain. -/
theorem sum_halaszRange_integral_eq (g : ℝ → ℝ) (x : ℕ)
    (hint : ∀ i : ℕ, i < 2*(halaszM x)+1 → IntervalIntegrable g volume
      (-((halaszM x : ℕ):ℝ) - 1/2 + i) (-((halaszM x : ℕ):ℝ) - 1/2 + (i+1))) :
    ∑ N ∈ halaszRange x, (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), g t)
      = ∫ t in (-((halaszM x : ℕ):ℝ) - 1/2)..(((halaszM x : ℕ):ℝ) + 1/2), g t := by
  rw [halaszRange_eq_Icc]
  exact sum_unit_intervals_eq g (halaszM x) hint

open MeasureTheory Real Finset in
/-- **Band/tail decomposition of a line integral** (Track R, N42):

  `∫_ℝ h = ∫_{−a}^{a} h + ∫_{|ξ| > a} h`.

An identity: `[−a, a]` and `{|ξ| > a}` are exactly complementary, since
`ξ ∈ [−a, a] ↔ |ξ| ≤ a`. -/
theorem integral_eq_band_add_tail (h : ℝ → ℝ) (hint : Integrable h) (a : ℝ)
    (ha : 0 ≤ a) :
    ∫ ξ, h ξ = (∫ ξ in (-a)..a, h ξ) + ∫ ξ in {ξ : ℝ | a < |ξ|}, h ξ := by
  have hset : {ξ : ℝ | a < |ξ|} = (Set.Icc (-a) a)ᶜ := by
    ext ξ
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_Icc, ← abs_le,
      not_le]
  rw [hset, ← MeasureTheory.integral_add_compl measurableSet_Icc hint]
  congr 1
  rw [intervalIntegral.integral_of_le (by linarith : (-a:ℝ) ≤ a)]
  exact MeasureTheory.integral_Icc_eq_integral_Ioc

open MeasureTheory Real Finset in
/-- **The band/tail split, as an estimate** (Track R, N42): with the
tail priced by `Mtail`,

  `∫_ℝ h ≤ ∫_{−a}^{a} h + Mtail`.

This is the sharp route's analogue of the split inside
`pairing_band_tail_split`.  The difference is what happens to the band:
there it is bounded by a *uniform sup* of the `L∞` factor over
`|ξ| ≤ a`, which is the cheap Halász shape; here the band is left as an
integral, to be tiled by `sum_halaszRange_integral_eq` and charged
frequency by frequency to the `ℓ²` weights of `L(x)`.  That single
difference is the whole cheap/sharp gap.

Downstream `Mtail` comes from `ExpSums.fourier_tail_le`
(`≤ M₂/(2π²·a)`), so taking `a` a power of `log x` makes it negligible. -/
theorem integral_le_band_add_tail (h : ℝ → ℝ) (hint : Integrable h) (a : ℝ)
    (ha : 0 ≤ a) (Mtail : ℝ)
    (htail : (∫ ξ in {ξ : ℝ | a < |ξ|}, h ξ) ≤ Mtail) :
    ∫ ξ, h ξ ≤ (∫ ξ in (-a)..a, h ξ) + Mtail := by
  rw [integral_eq_band_add_tail h hint a ha]
  linarith

end MoltResearch
