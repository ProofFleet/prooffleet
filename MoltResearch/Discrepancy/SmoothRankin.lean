import MoltResearch.Discrepancy.RamareIdentity
import MoltResearch.Discrepancy.MertensFirst
import MoltResearch.Discrepancy.LogUniform
import MoltResearch.Discrepancy.PerronWindow
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
/-- **The telescoping step of the log-over-square sum** (Track R, N155):

  `log(n+1)/(n+1)² ≤ 4/√n − 4/√(n+1)`,  for `n ≥ 1`.

`sum_log_div_sq_le`'s inductive step, extracted so that partial sums
can be bounded as well as the whole.  The proof is the one that was
inline there: `log(n+1) ≤ 2√(n+1) − 2` from `log t ≤ t − 1` at
`t = √(n+1)`, then `2/b³ ≤ 4/a − 4/b` after clearing denominators with
`(b−a)(a+b) = 1`, which reduces to `a² + ab ≤ 2b²` with `a² = b² − 1`.

Having it separately is what makes `sum_log_div_sq_tail_le` free: the
same telescoping run from any starting point bounds the tail by its
first term's `4/√a`, and *that* is what distinguishes a mass of
`O(1/log²x)` from a mass of `O(1)` in `block_masses_le`. -/
theorem log_div_sq_le_sqrt_diff (N : ℕ) (hN : 1 ≤ N) :
    Real.log ((N:ℝ)+1) / ((N:ℝ)+1)^2
      ≤ 4/Real.sqrt (N:ℝ) - 4/Real.sqrt ((N:ℝ)+1) := by
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
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
  linarith [hnum, hrhs]

open ArithmeticFunction Finset in
/-- **The Riesz identity closes** (Track R, N160): for completely
multiplicative `f` and `y > 0`, with `R(y) = ∑_{n≤y} f(n)·log(y/n)` and
`R₂(y) = ∑_{n≤y} f(n)·log²(y/n)`,

  `R(y)·log y = ∑_{d≤y} f(d)·Λ(d)·R(y/d) + R₂(y)`.

**The fact the whole Riesz route rests on.**  Iterating this produces
only Riesz means: the right-hand side is again `R` at a smaller scale,
so the sharp sum `∑_{n≤y} f(n)` never reappears and nothing is ever
differenced back.  That was the open question when the route was
chosen, and this is its affirmative answer.

Compare the sharp-sum identity, where `S(y)·log y` picks up
`∑_{n≤y} f(n)·log(y/n)` — an object of a *different* kind — so each
iteration alternates between two shapes and the differencing that
converts one to the other costs `≍ h·y` every time round.  Under the
`1/s²` kernel the two shapes coincide, because
`log n·log(y/n) = log y·log(y/n) − log²(y/n)` sends the diagonal into
the same family.

Three ingredients: `vonMangoldt_sum` (`∑_{d ∣ n} Λ(d) = log n`),
`sum_divisors_swap` for the reindex, and complete multiplicativity to
factor `f(dm) = f(d)f(m)` — after which `log y − log(dm)` is
`log(y/d) − log m` and the inner sum is `R(y/d)` verbatim, its range
`⌊y⌋/d = ⌊y/d⌋` by `Nat.floor_div_natCast`.

`R₂` is the order-2 Riesz mean up to the factorial: with
`R_k(y) = ∑_{n≤y} f(n)log^k(y/n)/k!` the statement reads
`R₁·log y = ∑ Λ_f·R₁(y/d) + 2R₂`. -/
theorem rieszMean_log_identity (f : ℕ → ℝ)
    (hmul : ∀ a b, f (a*b) = f a * f b) (y : ℝ) (hy : 0 < y) :
    (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, f n * (Real.log y - Real.log (n:ℝ)))
        * Real.log y
      = (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, f d * vonMangoldt d
            * ∑ m ∈ Finset.Icc 1 ⌊y/(d:ℝ)⌋₊, f m
                * (Real.log (y/(d:ℝ)) - Real.log (m:ℝ)))
        + ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, f n * (Real.log y - Real.log (n:ℝ))^2 := by
  classical
  set N : ℕ := ⌊y⌋₊ with hN_def
  -- Step 1: the two `R`-terms combine into the diagonal `log n`
  have hsplit : (∑ n ∈ Finset.Icc 1 N, f n * (Real.log y - Real.log (n:ℝ)))
        * Real.log y
      - ∑ n ∈ Finset.Icc 1 N, f n * (Real.log y - Real.log (n:ℝ))^2
      = ∑ n ∈ Finset.Icc 1 N,
          f n * Real.log (n:ℝ) * (Real.log y - Real.log (n:ℝ)) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  -- Step 2: `log n = ∑_{d ∣ n} Λ(d)`
  have hlog : ∀ n ∈ Finset.Icc 1 N,
      f n * Real.log (n:ℝ) * (Real.log y - Real.log (n:ℝ))
        = ∑ d ∈ n.divisors,
            vonMangoldt d * (f n * (Real.log y - Real.log (n:ℝ))) := by
    intro n _
    rw [← Finset.sum_mul, vonMangoldt_sum]
    ring
  -- Step 3: swap the order of summation
  have hswap := sum_divisors_swap N
    (fun d n => vonMangoldt d * (f n * (Real.log y - Real.log (n:ℝ))))
  -- Step 4: complete multiplicativity and the log split
  have hinner : ∀ d ∈ Finset.Icc 1 N,
      (∑ m ∈ Finset.Icc 1 (N/d),
          vonMangoldt d * (f (d*m) * (Real.log y - Real.log ((d*m : ℕ):ℝ))))
        = f d * vonMangoldt d
            * ∑ m ∈ Finset.Icc 1 ⌊y/(d:ℝ)⌋₊, f m
                * (Real.log (y/(d:ℝ)) - Real.log (m:ℝ)) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd1 : 1 ≤ d := hd.1
    have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd1
    have hfloor : N/d = ⌊y/(d:ℝ)⌋₊ := by
      rw [hN_def, Nat.floor_div_natCast]
    rw [← hfloor, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    have hm1 : 1 ≤ m := hm.1
    have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
    have hcast : (((d*m : ℕ)):ℝ) = (d:ℝ) * (m:ℝ) := by push_cast; ring
    rw [hmul d m, hcast, Real.log_mul (ne_of_gt hd0) (ne_of_gt hm0),
      Real.log_div (ne_of_gt hy) (ne_of_gt hd0)]
    ring
  -- assemble
  have hchain : ∑ n ∈ Finset.Icc 1 N,
      f n * Real.log (n:ℝ) * (Real.log y - Real.log (n:ℝ))
      = ∑ d ∈ Finset.Icc 1 N, f d * vonMangoldt d
          * ∑ m ∈ Finset.Icc 1 ⌊y/(d:ℝ)⌋₊, f m
              * (Real.log (y/(d:ℝ)) - Real.log (m:ℝ)) := by
    rw [Finset.sum_congr rfl hlog, hswap, Finset.sum_congr rfl hinner]
  linarith [hsplit, hchain]

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
    have hstep := log_div_sq_le_sqrt_diff N hN
    have hcast : (((N+1 : ℕ)):ℝ) = (N:ℝ) + 1 := by push_cast; ring
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ N + 1), hcast]
    linarith [ih, hstep]

open Finset in
/-- **The tail of the log-over-square sum** (Track R, N155):

  `∑_{a<n≤N} log n / n² ≤ 4/√a`,  for `a ≥ 1`, uniformly in `N`.

`sum_log_div_sq_le` telescoped from `a` instead of from `1`.  The full
sum is the case `a = 1`; what is new is that the *tail* decays, and
that is what the sum needs to be useful beyond "it converges".

The application is `sum_log_div_sq_ratio_sq_le`: the primes above `√x`
in `∑_p log p/(p² log²(x/p))` cannot be handled by the `log(x/p) ≥ log 2`
bound alone, because that bound is `O(1)` where the truth is
`O(1/log²x)`.  They are instead discarded against this tail, at a cost
of `4/x^{1/4}` — which is smaller than any power of `1/log x`. -/
theorem sum_log_div_sq_tail_le (a N : ℕ) (ha : 1 ≤ a) :
    ∑ n ∈ Finset.Icc (a+1) N, Real.log (n:ℝ)/(n:ℝ)^2
      ≤ 4/Real.sqrt (a:ℝ) := by
  have ha0 : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have hsa : (0:ℝ) < Real.sqrt (a:ℝ) := Real.sqrt_pos.mpr ha0
  rcases le_or_gt a N with hN | hN
  · have key : ∀ M : ℕ, a ≤ M →
        ∑ n ∈ Finset.Icc (a+1) M, Real.log (n:ℝ)/(n:ℝ)^2
          ≤ 4/Real.sqrt (a:ℝ) - 4/Real.sqrt (M:ℝ) := by
      intro M hM
      induction M, hM using Nat.le_induction with
      | base => simp
      | succ M hM ih =>
        have hM1 : 1 ≤ M := le_trans ha hM
        have hstep := log_div_sq_le_sqrt_diff M hM1
        rw [Finset.sum_Icc_succ_top (by omega : a + 1 ≤ M + 1)]
        have hcast : (((M+1 : ℕ)):ℝ) = (M:ℝ) + 1 := by push_cast; ring
        rw [hcast]
        linarith [ih, hstep]
    have hpos : (0:ℝ) ≤ 4/Real.sqrt (N:ℝ) := by positivity
    linarith [key N hN]
  · rw [Finset.Icc_eq_empty (by omega)]
    simp
    positivity

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
/-- **The Riesz triple convolution** (Track R, N171): `tripleConv` with
the inner sharp sum replaced by a Riesz mean,

  `∑_{p ∈ P} (f(p)·log p/log(x/p))·∑_{q < x/p} f(q)·log q·R_f(x/pq)`,
  `R_f(y) = ∑_{n≤y} f(n)·log(y/n)`.

The object §3 works with on the Riesz path.  Two things differ from
`tripleConv` besides the kernel, and both are what make the Perron step
exact:

* the innermost range is `⌊x/pq⌋` at the **real** scale, not the
  integer quotient `⌊x/(pq)⌋` of `ℕ`-division — so no scale swap is
  needed later;
* the mean itself is the Riesz mean, whose window realisation
  (`rieszMean_eq_window_sum`) is an identity rather than a sandwich.

`tripleConv`'s two error steps therefore have no counterpart here.
Only the third — widening the inner prime range from `(x/p).primesBelow`
to a fixed `Q` — survives, because §4 needs one `ghsPrimePoly` for all
`p`. -/
noncomputable def tripleConvR (f : ℕ → ℝ) (x : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
    * ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
        * ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
            f n * (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ))

open Real Finset in
/-- **The Riesz triple convolution, realised** (Track R, N171):

  `tripleConvR f x P
     = ∑_p A(p)·∑_q B(q)·((x/pq)·∑_{n≤x} (f(n)/n)·V(log(x/pq) − log n))`,

with `V = rieszWindow`.

Termwise `rieszMean_eq_window_sum` at `y = x/pq` and `N = x`; the
hypothesis `y ≤ x` is `pq ≥ 1`.  **An identity**, with no `ρ` and no
edge budget.

This is `tripleConv_sub_ghs_le`'s chain with its first two links
removed.  There, `tripleConv → B` paid for the Perron substitution
(`perron_sandwich_uniform_real`, `2ρ⌊y⌋ + 6` per term) and `B → C` paid
for the scale swap between `⌊x/(pq)⌋` and `x/pq`.  Here the right-hand
side *is* `C`, reached in one step and for free, and what remains
before `ghs_reindex` applies is only the range enlargement. -/
theorem tripleConvR_eq_scaled (f : ℕ → ℝ) (x : ℕ) (hx : 0 < x)
    (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) :
    tripleConvR f x P
      = ∑ p ∈ P, (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
          * ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
              * (((x:ℝ)/((p:ℝ)*(q:ℝ)))
                * ∑ n ∈ Finset.Icc 1 x, (f n/(n:ℝ))
                    * ExpSums.rieszWindow
                        (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ))) := by
  classical
  have hxR : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx
  rw [tripleConvR]
  refine Finset.sum_congr rfl fun p hp => ?_
  refine congrArg _ (Finset.sum_congr rfl fun q hq => ?_)
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hP p hp
  have hqp : q.Prime := (Nat.mem_primesBelow.mp hq).2
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hqp.pos
  have hy0 : (0:ℝ) < (x:ℝ)/((p:ℝ)*(q:ℝ)) := by positivity
  have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hP p hp
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hqp.one_lt.le
  have hyx : (x:ℝ)/((p:ℝ)*(q:ℝ)) ≤ (x:ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have hpq1 : (1:ℝ) ≤ (p:ℝ)*(q:ℝ) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hpq1 hxR.le]
  refine congrArg _ ?_
  exact ExpSums.rieszMean_eq_window_sum f ((x:ℝ)/((p:ℝ)*(q:ℝ))) hy0 x hyx

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
integers `N` with `|N| ≤ log⁴x + 1`, over which the unit-interval
suprema of `|F_x(1+it)|` are weighted.

The half-width is `log⁴x` rather than `log²x` (Track R, N162).  Widening
it is **free**: `halaszLSq_le_of_bound` collapses `L(x)²` to `6C²`
through `sum_inv_sq_add_one_Icc_le`, whose bound `6` does not depend on
the half-width at all, and the `hV`/`hB` hypotheses of the pairing
estimate are uniform in the frequency.  So the half-width survives only
in the domain of the window tail `hWtail`, where wider is strictly
better.

That is what lets a **second-order** window tail be used.
`fourier_rieszWindow_tail_le` gives `≤ 1/(2π²L)`, and §4 needs
`Wtail ≲ e^{k}/(C·log³x)`; at `L ≍ log²x` that fails by a factor of
`log x`, at `L ≍ log⁴x` it clears with room.  The smoothed window could
not make this trade — its `M₂` and `M₃` grew like `ρ^{−2}` and `ρ^{−3}`
— which is why `fourier_tail_cube_le` exists to buy the same factor by
one more integration by parts instead. -/
noncomputable def halaszRange (x : ℕ) : Finset ℤ :=
  Finset.Icc (-(⌈(Real.log (x:ℝ))^4⌉ + 1)) (⌈(Real.log (x:ℝ))^4⌉ + 1)

open Finset Real in
/-- **`L(x)²`, parametrised by a dominating function** (Track R, N29):

  `L(x)² = ∑_{|N| ≤ log⁴x+1} B(N)²/(N²+1)`.

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
`log`-growing one: the number of frequencies is `≍ log⁴x`, but their
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
`≍ log⁴x` frequencies, so a naive termwise bound would give
`L(x)² ≪ C²log⁴x`; because the weights have total mass `O(1)`, the
`log` disappears entirely and `L(x) ≪ C`.  That is exactly what makes
Halász's theorem sharp rather than log-lossy.

The bound `6` holds for **every** half-width —
`sum_inv_sq_add_one_Icc_le` is uniform in `M` — which is what makes the
band width a free parameter of the argument rather than a quantity to
be balanced against anything. -/
theorem halaszLSq_le_of_bound (B : ℤ → ℝ) (x : ℕ) (C : ℝ)
    (hB : ∀ N ∈ halaszRange x, |B N| ≤ C) :
    halaszLSq B x ≤ 6 * C^2 := by
  classical
  have hc0 : (0:ℤ) ≤ ⌈(Real.log (x:ℝ))^4⌉ := Int.ceil_nonneg (by positivity)
  set M : ℕ := (⌈(Real.log (x:ℝ))^4⌉ + 1).toNat with hM_def
  have hMcast : ((M:ℕ):ℤ) = ⌈(Real.log (x:ℝ))^4⌉ + 1 := by
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
number `M` with `halaszRange x = [−M, M] ∩ ℤ`, namely `⌈log⁴x⌉ + 1`.
See `halaszRange` for why the fourth power costs nothing. -/
noncomputable def halaszM (x : ℕ) : ℕ := (⌈(Real.log (x:ℝ))^4⌉ + 1).toNat

open Finset Real in
/-- **The Halász range is a symmetric integer interval** (Track R,
N41): `halaszRange x = Finset.Icc (−halaszM x) (halaszM x)`.

`⌈log⁴x⌉ ≥ 0` always — including at `x = 0`, where `log 0 = 0` — so the
`toNat` is faithful and the range really is symmetric about the origin.

The fact was previously available only inside `halaszLSq_le_of_bound`'s
proof; stating it is what lets `sum_unit_intervals_eq` be applied to
the Halász range, which is the form §4 needs. -/
theorem halaszRange_eq_Icc (x : ℕ) :
    halaszRange x = Finset.Icc (-(halaszM x : ℤ)) ((halaszM x : ℤ)) := by
  have hc0 : (0:ℤ) ≤ ⌈(Real.log (x:ℝ))^4⌉ := Int.ceil_nonneg (by positivity)
  have hM : ((halaszM x : ℕ) : ℤ) = ⌈(Real.log (x:ℝ))^4⌉ + 1 := by
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

open MeasureTheory Real Complex Finset in
/-- **The `I₂` estimate over the whole line** (Track R, N43):

  `∫_ℝ ‖D‖²·W·‖F‖² ≤ 5·C·V·L(x)² + Mtail`.

The composition of §4's `I₂` chain: `integral_le_band_add_tail` splits
off the tail, `sum_halaszRange_integral_eq` tiles the band into the unit
intervals around the integers of the Halász range, and
`sum_unit_interval_weight_halasz_le` charges each to its weight.

This is the form the Perron pairing produces — `∫` over the whole line,
from `norm_sum_translates_le_integral_char` — bounded by `L(x)²` with
only a tail remainder, which `ExpSums.fourier_tail_le` prices at
`M₂/(2π²a)`.

The band is never bounded by a uniform supremum.  That is the single
difference from `pairing_band_tail_split`, and it is the whole of the
cheap/sharp gap. -/
theorem integral_line_halasz_le (D Fn : ℝ → ℂ) (W : ℝ → ℝ) (B : ℤ → ℝ)
    (x : ℕ) (C V Mtail : ℝ) (hC0 : 0 ≤ C) (hWle : ∀ t, W t ≤ C/(1+t^2))
    (hB : ∀ N ∈ halaszRange x, ∀ t ∈ Set.Icc ((N:ℝ) - 1/2) ((N:ℝ) + 1/2),
      ‖Fn t‖ ≤ B N)
    (hB0 : ∀ N, 0 ≤ B N)
    (hV : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), ‖D t‖^2) ≤ V)
    (hintg : Integrable (fun t => ‖D t‖^2 * W t * ‖Fn t‖^2))
    (htail : (∫ ξ in {ξ : ℝ | ((halaszM x : ℕ):ℝ) + 1/2 < |ξ|},
        ‖D ξ‖^2 * W ξ * ‖Fn ξ‖^2) ≤ Mtail)
    (htile : ∀ i : ℕ, i < 2*(halaszM x)+1 → IntervalIntegrable
      (fun t => ‖D t‖^2 * W t * ‖Fn t‖^2) volume
      (-((halaszM x : ℕ):ℝ) - 1/2 + i) (-((halaszM x : ℕ):ℝ) - 1/2 + (i+1)))
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
    (∫ ξ, ‖D ξ‖^2 * W ξ * ‖Fn ξ‖^2) ≤ 5 * C * V * halaszLSq B x + Mtail := by
  classical
  set h : ℝ → ℝ := fun t => ‖D t‖^2 * W t * ‖Fn t‖^2 with hh_def
  set a : ℝ := ((halaszM x : ℕ):ℝ) + 1/2 with ha_def
  have ha0 : (0:ℝ) ≤ a := by
    have : (0:ℝ) ≤ ((halaszM x : ℕ):ℝ) := Nat.cast_nonneg _
    simp only [ha_def]; linarith
  -- split off the tail
  have hsplit := integral_le_band_add_tail h hintg a ha0 Mtail htail
  refine le_trans hsplit ?_
  -- the band tiles into unit intervals
  have hneg : -a = -((halaszM x : ℕ):ℝ) - 1/2 := by simp only [ha_def]; ring
  have hband : (∫ ξ in (-a)..a, h ξ)
      = ∑ N ∈ halaszRange x, (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), h t) := by
    rw [hneg, ha_def]
    exact (sum_halaszRange_integral_eq h x htile).symm
  rw [hband]
  -- charge each interval to its Halász weight
  have hmain := sum_unit_interval_weight_halasz_le D Fn W B x C V hC0 hWle
    hB hB0 hV hj hi1 hi2 hi3
  linarith [hmain]

open MeasureTheory Real Complex Finset in
/-- **The pairing splits into `I₁` and `I₂`** (Track R, N44): for
`λ > 0` and a nonnegative weight `w`,

  `∫ ‖P₁·P₂·P₃‖·w ≤ (λ/2)·∫‖P₂‖²·w + (1/(2λ))·∫‖P₁‖²‖P₃‖²·w`.

GHS §4 writes this as `√(I₁·I₂)`; keeping `λ` free avoids the square
root, and §4 never needs the optimal constant — only `≪ L(x) + 1`.

The grouping is what matters: `P₂` (the `P_k` polynomial) alone on one
side, and `P₁·P₃` (the Euler product together with the `q`-polynomial)
on the other.  The first integral is then `I₁`, bounded by
`sum_log_div_sq_ratio_block_mass_le`; the second is exactly the shape of
`integral_line_halasz_le`, which returns `L(x)²`.  Pairing `P₁` with
`P₃` rather than with `P₂` is the choice that makes both sides land on
lemmas that already exist.

No square roots appear anywhere, and `w` needs only nonnegativity. -/
theorem pairing_le_amgm (P₁ P₂ P₃ : ℝ → ℂ) (w : ℝ → ℝ) (lam : ℝ)
    (hlam : 0 < lam) (hw0 : ∀ t, 0 ≤ w t)
    (hi0 : Integrable (fun ξ => ‖P₁ ξ * P₂ ξ * P₃ ξ‖ * w ξ))
    (hi1 : Integrable (fun ξ => ‖P₂ ξ‖^2 * w ξ))
    (hi2 : Integrable (fun ξ => ‖P₃ ξ‖^2 * w ξ * ‖P₁ ξ‖^2)) :
    (∫ ξ, ‖P₁ ξ * P₂ ξ * P₃ ξ‖ * w ξ)
      ≤ (lam/2) * (∫ ξ, ‖P₂ ξ‖^2 * w ξ)
        + (1/(2*lam)) * (∫ ξ, ‖P₃ ξ‖^2 * w ξ * ‖P₁ ξ‖^2) := by
  have hpt : ∀ ξ, ‖P₁ ξ * P₂ ξ * P₃ ξ‖ * w ξ
      ≤ (lam/2) * (‖P₂ ξ‖^2 * w ξ)
        + (1/(2*lam)) * (‖P₃ ξ‖^2 * w ξ * ‖P₁ ξ‖^2) := by
    intro ξ
    have hw := hw0 ξ
    have hamgm : ‖P₂ ξ‖ * (‖P₁ ξ‖ * ‖P₃ ξ‖)
        ≤ (lam/2) * ‖P₂ ξ‖^2 + (1/(2*lam)) * (‖P₁ ξ‖^2 * ‖P₃ ξ‖^2) := by
      rw [← sub_nonneg]
      have hexp : (lam/2) * ‖P₂ ξ‖^2
            + (1/(2*lam)) * (‖P₁ ξ‖^2 * ‖P₃ ξ‖^2)
            - ‖P₂ ξ‖ * (‖P₁ ξ‖ * ‖P₃ ξ‖)
          = (lam * ‖P₂ ξ‖ - ‖P₁ ξ‖ * ‖P₃ ξ‖)^2 / (2*lam) := by
        field_simp
        ring
      rw [hexp]
      positivity
    have heq : ‖P₁ ξ * P₂ ξ * P₃ ξ‖ = ‖P₂ ξ‖ * (‖P₁ ξ‖ * ‖P₃ ξ‖) := by
      rw [norm_mul, norm_mul]; ring
    rw [heq]
    calc ‖P₂ ξ‖ * (‖P₁ ξ‖ * ‖P₃ ξ‖) * w ξ
        ≤ ((lam/2) * ‖P₂ ξ‖^2
            + (1/(2*lam)) * (‖P₁ ξ‖^2 * ‖P₃ ξ‖^2)) * w ξ :=
          mul_le_mul_of_nonneg_right hamgm hw
      _ = (lam/2) * (‖P₂ ξ‖^2 * w ξ)
            + (1/(2*lam)) * (‖P₃ ξ‖^2 * w ξ * ‖P₁ ξ‖^2) := by ring
  have hsum : Integrable (fun ξ => (lam/2) * (‖P₂ ξ‖^2 * w ξ)
      + (1/(2*lam)) * (‖P₃ ξ‖^2 * w ξ * ‖P₁ ξ‖^2)) :=
    (hi1.const_mul _).add (hi2.const_mul _)
  refine le_trans (MeasureTheory.integral_mono hi0 hsum hpt) ?_
  rw [MeasureTheory.integral_add (hi1.const_mul _) (hi2.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

open MeasureTheory Real Complex Finset in
/-- **The §4 pairing estimate** (Track R, N45):

  `∫ ‖P₁·P₂·P₃‖·w ≤ (λ/2)·E₁ + (1/(2λ))·(5·C·V·L(x)² + Mtail)`.

This is GHS §4's `√(I₁·I₂)`, with `λ` free in place of the optimiser.
`E₁` bounds `I₁` — for the `P_k` polynomial,
`sum_log_div_sq_ratio_block_mass_le` gives `≪ e^{k}/log x` — and the
second factor is `I₂`, which `integral_line_halasz_le` returns as
`L(x)²` with `V ≪ e^{−k}·log x` from Lemma 1.

The `e^{±k}` cancel between the two, which is why §4 produces `L(x)`
with no residual `k`; choosing `λ` to balance them is the last
arithmetic step.

Everything here is abstract in the three polynomials: instantiating
`P₁ := F_x`, `P₂ := ∑_{p ∈ P_k}`, `P₃ := ∑_q` is what remains of §4. -/
theorem pairing_halasz_le (P₁ P₂ P₃ : ℝ → ℂ) (w : ℝ → ℝ) (B : ℤ → ℝ)
    (x : ℕ) (lam C V Mtail E₁ : ℝ) (hlam : 0 < lam) (hC0 : 0 ≤ C)
    (hw0 : ∀ t, 0 ≤ w t) (hwle : ∀ t, w t ≤ C/(1+t^2))
    (hE₁ : (∫ ξ, ‖P₂ ξ‖^2 * w ξ) ≤ E₁)
    (hB : ∀ N ∈ halaszRange x, ∀ t ∈ Set.Icc ((N:ℝ) - 1/2) ((N:ℝ) + 1/2),
      ‖P₁ t‖ ≤ B N)
    (hB0 : ∀ N, 0 ≤ B N)
    (hV : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), ‖P₃ t‖^2) ≤ V)
    (hg0 : Integrable (fun ξ => ‖P₁ ξ * P₂ ξ * P₃ ξ‖ * w ξ))
    (hg1 : Integrable (fun ξ => ‖P₂ ξ‖^2 * w ξ))
    (hg2 : Integrable (fun ξ => ‖P₃ ξ‖^2 * w ξ * ‖P₁ ξ‖^2))
    (htail : (∫ ξ in {ξ : ℝ | ((halaszM x : ℕ):ℝ) + 1/2 < |ξ|},
        ‖P₃ ξ‖^2 * w ξ * ‖P₁ ξ‖^2) ≤ Mtail)
    (htile : ∀ i : ℕ, i < 2*(halaszM x)+1 → IntervalIntegrable
      (fun t => ‖P₃ t‖^2 * w t * ‖P₁ t‖^2) volume
      (-((halaszM x : ℕ):ℝ) - 1/2 + i) (-((halaszM x : ℕ):ℝ) - 1/2 + (i+1)))
    (hj : ∀ N ∈ halaszRange x, IntervalIntegrable
      (fun t => ‖P₃ t‖^2 * w t * ‖P₁ t‖^2) volume
      ((N:ℝ) - 1/2) ((N:ℝ) + 1/2))
    (hk1 : ∀ N ∈ halaszRange x, IntervalIntegrable
      (fun t => (‖P₃ t‖^2/(1+t^2)) * ‖P₁ t‖^2) volume
      ((N:ℝ) - 1/2) ((N:ℝ) + 1/2))
    (hk2 : ∀ N ∈ halaszRange x, IntervalIntegrable
      (fun t => ‖P₃ t‖^2/(1+t^2)) volume ((N:ℝ) - 1/2) ((N:ℝ) + 1/2))
    (hk3 : ∀ N ∈ halaszRange x, IntervalIntegrable
      (fun t => ‖P₃ t‖^2) volume ((N:ℝ) - 1/2) ((N:ℝ) + 1/2)) :
    (∫ ξ, ‖P₁ ξ * P₂ ξ * P₃ ξ‖ * w ξ)
      ≤ (lam/2) * E₁
        + (1/(2*lam)) * (5 * C * V * halaszLSq B x + Mtail) := by
  classical
  have hsplit := pairing_le_amgm P₁ P₂ P₃ w lam hlam hw0 hg0 hg1 hg2
  refine le_trans hsplit ?_
  have hI2 := integral_line_halasz_le P₃ P₁ w B x C V Mtail hC0 hwle
    hB hB0 hV hg2 htail htile hj hk1 hk2 hk3
  have hlam0 : (0:ℝ) ≤ lam/2 := by linarith
  have hlam1 : (0:ℝ) ≤ 1/(2*lam) := by positivity
  have h1 : (lam/2) * (∫ ξ, ‖P₂ ξ‖^2 * w ξ) ≤ (lam/2) * E₁ :=
    mul_le_mul_of_nonneg_left hE₁ hlam0
  have h2 : (1/(2*lam)) * (∫ ξ, ‖P₃ ξ‖^2 * w ξ * ‖P₁ ξ‖^2)
      ≤ (1/(2*lam)) * (5 * C * V * halaszLSq B x + Mtail) :=
    mul_le_mul_of_nonneg_left hI2 hlam1
  linarith [h1, h2]

open Real in
/-- **The Cauchy–Schwarz optimiser** (Track R, N46): for `P, Q > 0`,

  `(√(Q/P)/2)·P + (1/(2√(Q/P)))·Q = √(P·Q)`.

At `λ = √(Q/P)` the free-parameter form `pairing_le_amgm` collapses
exactly to GHS's `√(I₁·I₂)` — the two halves contribute `√(PQ)/2`
apiece.

Keeping `λ` free through the whole of §4 and only balancing here is what
kept `Real.sqrt` out of every intermediate statement.  The square root
is intrinsic to Cauchy–Schwarz and has to appear somewhere; this is the
one place it does.

With `P ≍ e^{k}/log x` and `Q ≍ L(x)²·e^{−k}·log x` the product is
`≍ L(x)²`, so `√(P·Q) ≍ L(x)` — the `e^{±k}` and `log x` cancelling is
what leaves no residual `k`. -/
theorem pairing_optimal_lambda (P Q : ℝ) (hP : 0 < P) (hQ : 0 < Q) :
    (Real.sqrt (Q/P)/2) * P + (1/(2*Real.sqrt (Q/P))) * Q
      = Real.sqrt (P*Q) := by
  have hsp : 0 < Real.sqrt P := Real.sqrt_pos.mpr hP
  have hsq : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hP' : Real.sqrt P ^ 2 = P := Real.sq_sqrt hP.le
  have hQ' : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ.le
  have hdiv : Real.sqrt (Q/P) = Real.sqrt Q / Real.sqrt P := by
    rw [show Q/P = (Real.sqrt Q / Real.sqrt P)^2 by rw [div_pow, hP', hQ']]
    exact Real.sqrt_sq (by positivity)
  have hmul : Real.sqrt (P*Q) = Real.sqrt P * Real.sqrt Q :=
    Real.sqrt_mul hP.le Q
  rw [hdiv, hmul]
  field_simp
  rw [hP', hQ']
  ring

open MeasureTheory Real Complex Finset in
/-- **The pairing estimate at the optimal `λ`** (Track R, N46): with
`E₁ > 0` and the `I₂` bound positive,

  `∫ ‖P₁·P₂·P₃‖·w ≤ √(E₁ · (5·C·V·L(x)² + Mtail))`.

`pairing_halasz_le` balanced by `pairing_optimal_lambda`.  This is GHS
§4's estimate in its published form. -/
theorem pairing_halasz_sqrt_le (P₁ P₂ P₃ : ℝ → ℂ) (w : ℝ → ℝ) (B : ℤ → ℝ)
    (x : ℕ) (C V Mtail E₁ : ℝ) (hE₁0 : 0 < E₁) (hC0 : 0 ≤ C)
    (hQ0 : 0 < 5 * C * V * halaszLSq B x + Mtail)
    (hw0 : ∀ t, 0 ≤ w t) (hwle : ∀ t, w t ≤ C/(1+t^2))
    (hE₁ : (∫ ξ, ‖P₂ ξ‖^2 * w ξ) ≤ E₁)
    (hB : ∀ N ∈ halaszRange x, ∀ t ∈ Set.Icc ((N:ℝ) - 1/2) ((N:ℝ) + 1/2),
      ‖P₁ t‖ ≤ B N)
    (hB0 : ∀ N, 0 ≤ B N)
    (hV : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), ‖P₃ t‖^2) ≤ V)
    (hg0 : Integrable (fun ξ => ‖P₁ ξ * P₂ ξ * P₃ ξ‖ * w ξ))
    (hg1 : Integrable (fun ξ => ‖P₂ ξ‖^2 * w ξ))
    (hg2 : Integrable (fun ξ => ‖P₃ ξ‖^2 * w ξ * ‖P₁ ξ‖^2))
    (htail : (∫ ξ in {ξ : ℝ | ((halaszM x : ℕ):ℝ) + 1/2 < |ξ|},
        ‖P₃ ξ‖^2 * w ξ * ‖P₁ ξ‖^2) ≤ Mtail)
    (htile : ∀ i : ℕ, i < 2*(halaszM x)+1 → IntervalIntegrable
      (fun t => ‖P₃ t‖^2 * w t * ‖P₁ t‖^2) volume
      (-((halaszM x : ℕ):ℝ) - 1/2 + i) (-((halaszM x : ℕ):ℝ) - 1/2 + (i+1)))
    (hj : ∀ N ∈ halaszRange x, IntervalIntegrable
      (fun t => ‖P₃ t‖^2 * w t * ‖P₁ t‖^2) volume
      ((N:ℝ) - 1/2) ((N:ℝ) + 1/2))
    (hk1 : ∀ N ∈ halaszRange x, IntervalIntegrable
      (fun t => (‖P₃ t‖^2/(1+t^2)) * ‖P₁ t‖^2) volume
      ((N:ℝ) - 1/2) ((N:ℝ) + 1/2))
    (hk2 : ∀ N ∈ halaszRange x, IntervalIntegrable
      (fun t => ‖P₃ t‖^2/(1+t^2)) volume ((N:ℝ) - 1/2) ((N:ℝ) + 1/2))
    (hk3 : ∀ N ∈ halaszRange x, IntervalIntegrable
      (fun t => ‖P₃ t‖^2) volume ((N:ℝ) - 1/2) ((N:ℝ) + 1/2)) :
    (∫ ξ, ‖P₁ ξ * P₂ ξ * P₃ ξ‖ * w ξ)
      ≤ Real.sqrt (E₁ * (5 * C * V * halaszLSq B x + Mtail)) := by
  classical
  set Q : ℝ := 5 * C * V * halaszLSq B x + Mtail with hQ_def
  have hlam : 0 < Real.sqrt (Q/E₁) := Real.sqrt_pos.mpr (by positivity)
  have hmain := pairing_halasz_le P₁ P₂ P₃ w B x (Real.sqrt (Q/E₁)) C V
    Mtail E₁ hlam hC0 hw0 hwle hE₁ hB hB0 hV hg0 hg1 hg2 htail htile
    hj hk1 hk2 hk3
  rw [← pairing_optimal_lambda E₁ Q hE₁0 hQ0]
  exact hmain

open Finset Real Complex in
/-- **The `P_k` polynomial** (Track R, N48): GHS §4's
`∑_{p ∈ P_k} f(p)·log p/(p^s·log(x/p))` on the `1`-line. -/
noncomputable def ghsBlockPoly (f : ℕ → ℂ) (x : ℕ) (P : Finset ℕ) : ℝ → ℂ :=
  fun ξ => ∑ p ∈ P,
    (((Real.log (p:ℝ) : ℂ) * f p)
        / ((p:ℂ) * ((Real.log ((x:ℝ)/(p:ℝ)) : ℝ) : ℂ)))
      * ((Real.fourierChar (-(Real.log (p:ℝ) * ξ)) : Circle) : ℂ)

open Finset Real Complex in
/-- **The `q` polynomial** (Track R, N48): GHS §4's
`∑_{q ≤ x^{e^{1−k}}} f(q)·log q/q^s`, `q` prime. -/
noncomputable def ghsPrimePoly (f : ℕ → ℂ) (Q : Finset ℕ) : ℝ → ℂ :=
  fun ξ => ∑ q ∈ Q, (((Real.log (q:ℝ) : ℂ) * f q) / (q:ℂ))
      * ((Real.fourierChar (-(Real.log (q:ℝ) * ξ)) : Circle) : ℂ)

open Finset Real Complex in
/-- **The main Dirichlet polynomial** (Track R, N48): `∑_{n} f(n)/n^s`,
which plays the role of GHS's truncated Euler product `F_x` — it is the
factor bounded in `L∞`, and whose unit-interval suprema define `L(x)`. -/
noncomputable def ghsMainPoly (f : ℕ → ℂ) (S : Finset ℕ) : ℝ → ℂ :=
  fun ξ => ∑ n ∈ S, (f n / (n:ℂ))
      * ((Real.fourierChar (-(Real.log (n:ℝ) * ξ)) : Circle) : ℂ)

open Finset Real Complex in
/-- The three §4 polynomials are continuous (Track R, N48) — the
regularity that discharges the integrability side conditions of
`pairing_halasz_sqrt_le`. -/
theorem continuous_ghsBlockPoly (f : ℕ → ℂ) (x : ℕ) (P : Finset ℕ) :
    Continuous (ghsBlockPoly f x P) :=
  ExpSums.continuous_char_poly P _ _

open Finset Real Complex in
theorem continuous_ghsPrimePoly (f : ℕ → ℂ) (Q : Finset ℕ) :
    Continuous (ghsPrimePoly f Q) :=
  ExpSums.continuous_char_poly Q _ _

open Finset Real Complex in
theorem continuous_ghsMainPoly (f : ℕ → ℂ) (S : Finset ℕ) :
    Continuous (ghsMainPoly f S) :=
  ExpSums.continuous_char_poly S _ _

open Finset Real Complex in
/-- **The trivial sup of the `q` polynomial** (Track R, N48): for
`‖f‖ ≤ 1`,

  `‖P₃(ξ)‖ ≤ ∑_{q ∈ Q} log q/q`,  uniformly in `ξ`.

Mertens' first theorem bounds the right side by `log(max Q) + O(1)`,
which is the `e^{−k}·log x` that `I₂` needs. -/
theorem norm_ghsPrimePoly_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (Q : Finset ℕ) (ξ : ℝ) :
    ‖ghsPrimePoly f Q ξ‖ ≤ ∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ) := by
  refine le_trans (ExpSums.norm_char_poly_le_sum Q _ _ ξ) ?_
  refine Finset.sum_le_sum fun q _ => ?_
  rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_natCast,
    Real.norm_eq_abs]
  have hq : ‖f q‖ ≤ 1 := hf q
  have hlog : |Real.log (q:ℝ)| = Real.log (q:ℝ) :=
    abs_of_nonneg (Real.log_natCast_nonneg q)
  rw [hlog]
  have hq0 : (0:ℝ) ≤ (q:ℝ) := Nat.cast_nonneg _
  have hlog0 : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_natCast_nonneg q
  rcases eq_or_lt_of_le hq0 with h | h
  · rw [← h]; simp
  · refine div_le_div_of_nonneg_right ?_ h.le
    nlinarith [hq, hlog0]

open Finset Real Complex in
/-- **The trivial sup of the main polynomial** (Track R, N49): for
`‖f‖ ≤ 1`,

  `‖P₁(ξ)‖ ≤ ∑_{n ∈ S} 1/n`,  uniformly in `ξ`.

This is the crude `L∞` bound, `≍ log x` over `[1, x]`.  It is *not* what
`L(x)` uses — that takes the supremum on each unit interval separately
and weights it — but it is the bound that prices the tail, where no
cancellation is available. -/
theorem norm_ghsMainPoly_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (S : Finset ℕ) (ξ : ℝ) :
    ‖ghsMainPoly f S ξ‖ ≤ ∑ n ∈ S, (1:ℝ)/(n:ℝ) := by
  refine le_trans (ExpSums.norm_char_poly_le_sum S _ _ ξ) ?_
  refine Finset.sum_le_sum fun n _ => ?_
  rw [norm_div, Complex.norm_natCast]
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg _
  rcases eq_or_lt_of_le hn0 with h | h
  · rw [← h]; simp
  · exact div_le_div_of_nonneg_right (hf n) h.le

open Finset Real Complex in
/-- **The trivial sup of the `P_k` polynomial** (Track R, N49): for
`‖f‖ ≤ 1`,

  `‖P₂(ξ)‖ ≤ ∑_{p ∈ P} log p/(p·|log(x/p)|)`.

Over a block this is `≍ e^{k}·(e−1)e^{−k} = O(1)` by
`sum_log_div_sq_ratio_block_le`'s companion — the same mass that feeds
`I₁`, which is why `E₁` and this sup are controlled by one estimate. -/
theorem norm_ghsBlockPoly_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (x : ℕ)
    (P : Finset ℕ) (ξ : ℝ) :
    ‖ghsBlockPoly f x P ξ‖
      ≤ ∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|) := by
  refine le_trans (ExpSums.norm_char_poly_le_sum P _ _ ξ) ?_
  refine Finset.sum_le_sum fun p _ => ?_
  rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Complex.norm_natCast, Real.norm_eq_abs, Real.norm_eq_abs]
  have hlog : |Real.log (p:ℝ)| = Real.log (p:ℝ) :=
    abs_of_nonneg (Real.log_natCast_nonneg p)
  rw [hlog]
  have hp0 : (0:ℝ) ≤ (p:ℝ) := Nat.cast_nonneg _
  have hlog0 : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
  have hden : (0:ℝ) ≤ (p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))| :=
    mul_nonneg hp0 (abs_nonneg _)
  rcases eq_or_lt_of_le hden with h | h
  · rw [← h]; simp
  · refine div_le_div_of_nonneg_right ?_ h.le
    nlinarith [hf p, hlog0]

open MeasureTheory Real Complex Finset in
/-- **The weighted energy, reduced to a band integral** (Track R, N50):
for `0 ≤ w ≤ C` and `‖P‖ ≤ Bsup`,

  `∫_ℝ ‖P‖²·w ≤ C·∫_{−T}^{T} ‖P‖² + Bsup²·Wtail`.

This is what turns `E₁` — the whole-line weighted energy that
`pairing_halasz_le` consumes — into the plain band integral that the
mean value theorem bounds.  On the band the weight is discarded against
its sup `C`; beyond it the polynomial is discarded against its own sup
and the weight's tail mass pays.

Both discards are lossless where it matters: `C` is `O(1)` for a
normalised window, and the tail mass is `O(1/T)` by
`ExpSums.fourier_tail_le`, so with `T` a power of `log x` the second
term is negligible against the first even at the crude sup `Bsup`.

Applied to `ghsBlockPoly` the band integral is Lemma 1's, landing on
`∑_p log p/(p·log²(x/p))` — the `I₁` mass of
`sum_log_div_sq_ratio_block_mass_le`. -/
theorem integral_sq_weight_le (P : ℝ → ℂ) (w : ℝ → ℝ) (T C Bsup Wtail : ℝ)
    (hT : 0 ≤ T) (hC : ∀ ξ, w ξ ≤ C) (hw0 : ∀ ξ, 0 ≤ w ξ)
    (hB : ∀ ξ, ‖P ξ‖ ≤ Bsup)
    (hWtail : (∫ ξ in {ξ : ℝ | T < |ξ|}, w ξ) ≤ Wtail)
    (hint : Integrable (fun ξ => ‖P ξ‖^2 * w ξ))
    (hband : IntervalIntegrable (fun ξ => ‖P ξ‖^2 * w ξ) volume (-T) T)
    (hband2 : IntervalIntegrable (fun ξ => ‖P ξ‖^2) volume (-T) T)
    (htailP : IntegrableOn (fun ξ => ‖P ξ‖^2 * w ξ) {ξ : ℝ | T < |ξ|})
    (htailw : IntegrableOn w {ξ : ℝ | T < |ξ|}) :
    (∫ ξ, ‖P ξ‖^2 * w ξ)
      ≤ C * (∫ ξ in (-T)..T, ‖P ξ‖^2) + Bsup^2 * Wtail := by
  classical
  have hB0 : (0:ℝ) ≤ Bsup := le_trans (norm_nonneg _) (hB 0)
  rw [integral_eq_band_add_tail _ hint T hT]
  -- on the band: discard the weight against its sup
  have hb : (∫ ξ in (-T)..T, ‖P ξ‖^2 * w ξ)
      ≤ C * ∫ ξ in (-T)..T, ‖P ξ‖^2 := by
    have hle : (-T) ≤ T := by linarith
    have hpt : ∀ ξ ∈ Set.Icc (-T) T, ‖P ξ‖^2 * w ξ ≤ C * ‖P ξ‖^2 := by
      intro ξ _
      have hP2 : (0:ℝ) ≤ ‖P ξ‖^2 := by positivity
      nlinarith [hC ξ, hP2]
    have hcm : IntervalIntegrable (fun ξ => C * ‖P ξ‖^2) volume (-T) T :=
      hband2.const_mul _
    refine le_trans (intervalIntegral.integral_mono_on hle hband hcm hpt) ?_
    rw [intervalIntegral.integral_const_mul]
  -- beyond it: discard the polynomial against its sup
  have ht : (∫ ξ in {ξ : ℝ | T < |ξ|}, ‖P ξ‖^2 * w ξ) ≤ Bsup^2 * Wtail := by
    have hpt : ∀ ξ, ‖P ξ‖^2 * w ξ ≤ Bsup^2 * w ξ := by
      intro ξ
      have h1 : ‖P ξ‖^2 ≤ Bsup^2 := by nlinarith [hB ξ, norm_nonneg (P ξ)]
      exact mul_le_mul_of_nonneg_right h1 (hw0 ξ)
    have hmono : (∫ ξ in {ξ : ℝ | T < |ξ|}, ‖P ξ‖^2 * w ξ)
        ≤ ∫ ξ in {ξ : ℝ | T < |ξ|}, Bsup^2 * w ξ :=
      MeasureTheory.setIntegral_mono htailP (htailw.const_mul _) hpt
    refine le_trans hmono ?_
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hWtail (by positivity)
  linarith [hb, ht]

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **The mean value theorem with a pointwise majorant** (Track R,
N54): if the Gaussian pair sum at `m` is at most `Q m` — a bound
allowed to depend on `m` — then

  `∫_{−T}^{T} ‖∑ a(n)Λ(n)·𝐞(−ξ log n)‖² dξ
     ≤ e^π·T·∑_m Q(m)·‖a(m)‖²·Λ(m)`.

`intervalIntegral_vonMangoldt_mvt_le` takes `Q` uniform over `S`, which
forces the coefficients to live on a dyadic block: the pair sum at `m`
is `≍ m·log m/T`, so a uniform `Q` is the value at the top of the range
and is lossy everywhere below it.  Decomposing a long range into dyadic
blocks recovers sharpness only at the cost of a factor equal to the
number of blocks — a `log`, which is exactly what this argument cannot
afford.

A pointwise `Q` avoids both.  The proof needs nothing new: the uniform
version already ends in a `Finset.sum_le_sum` over `m`, so the majorant
may as well vary with `m`.

This is what puts GHS's Lemma 1 in reach for the full range: their
right-hand side `∑ n·|a(n)|²·Λ(n)` is precisely this statement with
`Q(m) ≍ m`, and no dyadic decomposition anywhere. -/
theorem intervalIntegral_vonMangoldt_mvt_pointwise_le (T : ℝ) (hT : 0 < T)
    (S : Finset ℕ) (a : ℕ → ℂ) (Q : ℕ → ℝ)
    (hQ : ∀ m ∈ S, ∑ n ∈ S, vonMangoldt n
        * Real.exp (-(π*T^2*(Real.log (m:ℝ) - Real.log (n:ℝ))^2)) ≤ Q m) :
    (∫ ξ in (-T)..T, ‖∑ n ∈ S, (a n * ((vonMangoldt n : ℝ) : ℂ))
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
      ≤ Real.exp π * T * ∑ m ∈ S, Q m * (‖a m‖^2 * vonMangoldt m) := by
  classical
  have hexpT : (0:ℝ) ≤ Real.exp π * T :=
    mul_nonneg (Real.exp_pos _).le hT.le
  refine le_trans (ExpSums.intervalIntegral_norm_sq_gaussian_diag_le S a
    (fun n => vonMangoldt n) (fun n => vonMangoldt_nonneg) T hT) ?_
  have hinner : ∀ m ∈ S, ∑ n ∈ S, (vonMangoldt n : ℝ)
      * (Real.exp π * T
          * Real.exp (-(π*T^2*(Real.log (m:ℝ) - Real.log (n:ℝ))^2)))
      ≤ Real.exp π * T * Q m := by
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
      ≤ ∑ m ∈ S, ‖a m‖^2 * (vonMangoldt m : ℝ) * (Real.exp π * T * Q m) := by
    refine Finset.sum_le_sum fun m hm => ?_
    exact mul_le_mul_of_nonneg_left (hinner m hm)
      (mul_nonneg (sq_nonneg _) vonMangoldt_nonneg)
  refine le_trans hmid (le_of_eq ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **The sharp mean value theorem on a block** (Track R, N55): with
the pointwise majorant,

  `∫_{−T}^{T}‖∑ a(n)Λ(n)𝐞(−ξ log n)‖²
     ≤ e^π·T·∑_m (6144⌈2m/T⌉ + log m + …)·‖a(m)‖²Λ(m)`.

The leading term is `≍ ∑_m m·‖a(m)‖²·Λ(m)/T`, which is GHS's Lemma 1
shape — the weight `m` appearing on each coefficient rather than the
top of the range appearing on all of them.

`inner_sum_block_le` was already stated with an `m`-dependent leading
term `6144⌈2m/T⌉`; only `intervalIntegral_vonMangoldt_mvt_le`'s uniform
`Q` was discarding that dependence.  With
`intervalIntegral_vonMangoldt_mvt_pointwise_le` it survives, and the
composition is immediate. -/
theorem intervalIntegral_vonMangoldt_mvt_block_pointwise_le (T : ℝ) (N : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (hS : S ⊆ Finset.Ioc N (2*N)) (hN : 1 ≤ N)
    (hT : 2 ≤ T) (hTm : ∀ m ∈ S, T^2 ≤ (m:ℝ))
    (hsmall : ∀ m ∈ S, 2*(⌈2*(m:ℝ)/T⌉₊) ≤ N)
    (B : ℝ) (hB : ∑ n ∈ S, Real.log (n:ℝ) ≤ B) :
    (∫ ξ in (-T)..T, ‖∑ n ∈ S, (a n * ((vonMangoldt n : ℝ) : ℂ))
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
      ≤ Real.exp π * T * ∑ m ∈ S,
          (6144*((⌈2*(m:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log (m:ℝ)
            + Real.exp (-(π*T^2/64)) * B
            + ((Nat.sqrt (2*N) + 1 : ℕ):ℝ) * ((Nat.log 2 (2*N) : ℕ):ℝ)
                * Real.log ((2*N : ℕ):ℝ))
          * (‖a m‖^2 * vonMangoldt m) := by
  refine intervalIntegral_vonMangoldt_mvt_pointwise_le T (by linarith) S a _ ?_
  intro m hm
  exact inner_sum_block_le T N m S hS hm hN hT (hTm m hm) (hsmall m hm) B hB

open ArithmeticFunction Finset Real in
/-- **The inner sum over an arbitrary range** (Track R, N58):
`vonMangoldt_gaussian_block_le` with the block hypothesis replaced by
`S ⊆ [1, X]` and the reach condition `m ≤ 4·(2^J−1)h`.

  `∑_{n ∈ S} Λ(n)·e^{−πT²(log n − log m)²}
     ≤ 1024·h·L + log m + e^{−πT²/64}·B + (√X + 1)·log₂X·log X`.

Two changes from the block version, both mechanical.  The prime part is
`prime_gaussian_long_le`.  The proper-prime-power remainder is bounded
over `[1, X]` rather than `[1, 2N]` — every Gaussian factor is at most
one there, so only the range matters.

The remainder is `O(√X·log²X)`, which is why it never competes with the
main term even for `X` as large as `x`: the mean value theorem's
leading term is of size `h ≍ m/T`. -/
theorem vonMangoldt_gaussian_long_le (T : ℝ) (X m h J : ℕ) (S : Finset ℕ)
    (hS1 : ∀ n ∈ S, 1 ≤ n) (hSX : ∀ n ∈ S, n ≤ X) (hX : 1 ≤ X)
    (hm1 : 1 ≤ m) (hh : 2 ≤ h) (hscale : 2*(m:ℝ) ≤ (h:ℝ)*T)
    (hfit : (2^J - 1)*h + 1 ≤ m) (hwfit : ∀ j < J, 2^j*h ≤ 2*m)
    (hreach : m ≤ 4*((2^J - 1)*h))
    (L : ℝ) (hL : Real.log (4*(m:ℝ)+2)/Real.log ((h:ℕ):ℝ) ≤ L)
    (B : ℝ) (hB : ∑ n ∈ S, Real.log (n:ℝ) ≤ B) :
    ∑ n ∈ S, vonMangoldt n
        * Real.exp (-(π*T^2*(Real.log (n:ℝ) - Real.log (m:ℝ))^2))
      ≤ 1024*(h:ℝ)*L + Real.log (m:ℝ) + Real.exp (-(π*T^2/64)) * B
        + ((Nat.sqrt X + 1 : ℕ):ℝ) * ((Nat.log 2 X : ℕ):ℝ)
            * Real.log ((X : ℕ):ℝ) := by
  classical
  rw [sum_vonMangoldt_split S
    (fun n => Real.exp (-(π*T^2*(Real.log (n:ℝ) - Real.log (m:ℝ))^2)))]
  have hprime := ExpSums.prime_gaussian_long_le T m h J S hS1 hm1 hh
    hscale hfit hwfit hreach L hL B hB
  have hpp : ∑ n ∈ S.filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
      vonMangoldt n
        * Real.exp (-(π*T^2*(Real.log (n:ℝ) - Real.log (m:ℝ))^2))
      ≤ ((Nat.sqrt X + 1 : ℕ):ℝ) * ((Nat.log 2 X : ℕ):ℝ)
          * Real.log ((X : ℕ):ℝ) := by
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
        ⊆ (Finset.Icc 1 X).filter (fun n => IsPrimePow n ∧ ¬ n.Prime) := by
      intro n hn
      simp only [Finset.mem_filter] at hn ⊢
      exact ⟨Finset.mem_Icc.mpr ⟨hS1 n hn.1, hSX n hn.1⟩, hn.2⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => vonMangoldt_nonneg)) ?_
    exact sum_vonMangoldt_properPrimePow_le X hX
  linarith

open ArithmeticFunction Finset Real in
/-- **The inner sum at the canonical scale, over an arbitrary range**
(Track R, N59): `inner_sum_block_le` with the block replaced by
`S ⊆ [1, X]` and the smallness condition stated in terms of `m` alone.

  `∑_{n ∈ S} Λ(n)·e^{−πT²(log m − log n)²}
     ≤ 6144·⌈2m/T⌉ + log m + e^{−πT²/64}·B + (√X + 1)·log₂X·log X`.

The reach condition of `prime_gaussian_long_le` is what `2h ≤ m`
delivers.  Maximality of the shell count gives `m ≤ 2·a_J + h`; with
`h ≤ m/2` that forces `a_J ≥ m/4`, which is exactly `m ≤ 4·a_J`.  In
the block version the same role is played by `2h ≤ N` — the hypothesis
is no stronger here, only stated about the centre rather than the
block.

With this the mean value theorem applies to any finite set of integers,
which is what GHS's Lemma 1 asks for. -/
theorem inner_sum_long_le (T : ℝ) (X m : ℕ) (S : Finset ℕ)
    (hS1 : ∀ n ∈ S, 1 ≤ n) (hSX : ∀ n ∈ S, n ≤ X) (hX : 1 ≤ X)
    (hT : 2 ≤ T) (hTm : T^2 ≤ (m:ℝ))
    (hsmall : 2*(⌈2*(m:ℝ)/T⌉₊) ≤ m)
    (B : ℝ) (hB : ∑ n ∈ S, Real.log (n:ℝ) ≤ B) :
    ∑ n ∈ S, vonMangoldt n
        * Real.exp (-(π*T^2*(Real.log (m:ℝ) - Real.log (n:ℝ))^2))
      ≤ 6144*((⌈2*(m:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log (m:ℝ)
        + Real.exp (-(π*T^2/64)) * B
        + ((Nat.sqrt X + 1 : ℕ):ℝ) * ((Nat.log 2 X : ℕ):ℝ)
            * Real.log ((X : ℕ):ℝ) := by
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
  obtain ⟨J, hfit, hmax, hwfit⟩ :=
    ExpSums.exists_shell_count m h hm1 (by omega)
  have hsucc : (2^(J+1) - 1)*h = (2^J - 1)*h + 2^J*h :=
    ExpSums.dyadic_cut_succ h J
  have hJh : (2:ℕ)^J*h = (2^J - 1)*h + h := by
    have h1 : (1:ℕ) ≤ 2^J := Nat.one_le_two_pow
    have h2 : (2:ℕ)^J = (2^J - 1) + 1 := by omega
    calc (2:ℕ)^J*h = ((2^J - 1) + 1)*h := by rw [← h2]
      _ = (2^J - 1)*h + h := by ring
  have hreach : m ≤ 4*((2^J - 1)*h) := by omega
  have hflip : ∑ n ∈ S, vonMangoldt n
        * Real.exp (-(π*T^2*(Real.log (m:ℝ) - Real.log (n:ℝ))^2))
      = ∑ n ∈ S, vonMangoldt n
        * Real.exp (-(π*T^2*(Real.log (n:ℝ) - Real.log (m:ℝ))^2)) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 2
    ring
  rw [hflip]
  refine le_trans (vonMangoldt_gaussian_long_le T X m h J S hS1 hSX hX hm1
    hh2 hscale hfit hwfit hreach 6 hL B hB) ?_
  have hh0 : (0:ℝ) ≤ (h:ℝ) := Nat.cast_nonneg _
  have hcalc : 1024*(h:ℝ)*6 = 6144*(h:ℝ) := by ring
  linarith [hcalc]

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **GHS Lemma 1, over the full range** (Track R, N60): for any finite
set of integers in `[1, X]`,

  `∫_{−T}^{T}‖∑ a(n)Λ(n)·𝐞(−ξ log n)‖² dξ
     ≤ e^π·T·∑_m (6144·⌈2m/T⌉ + log m + e^{−πT²/64}·B + (√X+1)log₂X·log X)
              ·‖a(m)‖²·Λ(m)`.

The leading term is `≍ ∑_m m·‖a(m)‖²·Λ(m)`, which is exactly the shape
of GHS's Lemma 1 — and no dyadic decomposition appears anywhere.

Two things were needed to get here.  The mean value theorem had to
accept a majorant depending on `m`
(`intervalIntegral_vonMangoldt_mvt_pointwise_le`), since a uniform one
is the value at the top of the range and is lossy below it.  And the
inner sum had to be bounded without a block hypothesis
(`inner_sum_long_le`), which followed once the `1/8` multiplicative gap
was derived from the reach condition `m ≤ 4a_J` alone rather than from
`(N, 2N]`.

This is what §4 applies to `q ≤ x^{e^{1−k}}` and to `P_k`, neither of
which is dyadic.

**Superseded for §4 by `intervalIntegral_vonMangoldt_mvt_prime_le`.**
The statement is correct, but the two *additive* bracket terms —
`e^{−πT²/64}·B` and `(√X+1)·log₂X·log X` — are multiplied by
`∑_m ‖a(m)‖²Λ(m)` when summed.  For coefficients that decay like
`log q/q` that sum is `O(1)` while the leading term is only `≍ log⁴X`,
so the additive terms dominate by `≍ X/log⁴X` and the bound says
nothing.  On a *prime* set the `√X` term is identically zero, and the
`B` term is killed by taking `T ≍ √(log X)` rather than `8` — free,
since `T·⌈2m/T⌉ ≍ m` is `T`-independent. -/
theorem intervalIntegral_vonMangoldt_mvt_long_le (T : ℝ) (X : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ)
    (hS1 : ∀ n ∈ S, 1 ≤ n) (hSX : ∀ n ∈ S, n ≤ X) (hX : 1 ≤ X)
    (hT : 2 ≤ T) (hTm : ∀ m ∈ S, T^2 ≤ (m:ℝ))
    (hsmall : ∀ m ∈ S, 2*(⌈2*(m:ℝ)/T⌉₊) ≤ m)
    (B : ℝ) (hB : ∑ n ∈ S, Real.log (n:ℝ) ≤ B) :
    (∫ ξ in (-T)..T, ‖∑ n ∈ S, (a n * ((vonMangoldt n : ℝ) : ℂ))
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
      ≤ Real.exp π * T * ∑ m ∈ S,
          (6144*((⌈2*(m:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log (m:ℝ)
            + Real.exp (-(π*T^2/64)) * B
            + ((Nat.sqrt X + 1 : ℕ):ℝ) * ((Nat.log 2 X : ℕ):ℝ)
                * Real.log ((X : ℕ):ℝ))
          * (‖a m‖^2 * vonMangoldt m) := by
  refine intervalIntegral_vonMangoldt_mvt_pointwise_le T (by linarith) S a _ ?_
  intro m hm
  exact inner_sum_long_le T X m S hS1 hSX hX hT (hTm m hm) (hsmall m hm) B hB

open MeasureTheory Real Finset in
/-- **Widening a symmetric window** (Track R, N61): for `g ≥ 0` and
`0 ≤ a ≤ T`,

  `∫_{−a}^{a} g ≤ ∫_{−T}^{T} g`.

Needed because the two halves of §4's `I₂` estimate are stated at
different widths.  `integral_unit_sq_le_of_centred` asks for the energy
on `[−1/2, 1/2]`, while the mean value theorem
(`intervalIntegral_vonMangoldt_mvt_long_le`) is stated for `T ≥ 2` — its
shell construction needs `T` large enough that `⌈2m/T⌉` is small
compared with `m`.

Since the integrand is a squared norm, widening the window only adds
non-negative mass, so the mismatch costs nothing: apply the mean value
theorem at a suitable `T` and restrict.

`T = 2` will not do: `inner_sum_long_le` needs `2·⌈2m/T⌉ ≤ m`, which at
`T = 2` reads `2m ≤ m`.  `T = 8` gives `2·⌈m/4⌉ ≤ m/2 + 2 ≤ m` for
`m ≥ 4`. -/
theorem integral_symm_widen (g : ℝ → ℝ) (hg : ∀ t, 0 ≤ g t) (a T : ℝ)
    (ha : 0 ≤ a) (haT : a ≤ T)
    (hint : IntervalIntegrable g volume (-T) T) :
    (∫ t in (-a)..a, g t) ≤ ∫ t in (-T)..T, g t := by
  have hle : (-T) ≤ T := by linarith
  have hsub : Set.uIcc (-a) a ⊆ Set.uIcc (-T) T := by
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le hle]
    exact Set.Icc_subset_Icc (by linarith) haT
  have hnonneg : ∀ t ∈ Set.Icc (-T) T, 0 ≤ g t := fun t _ => hg t
  have hia : IntervalIntegrable g volume (-a) a :=
    hint.mono_set hsub
  rw [intervalIntegral.integral_of_le (by linarith : (-a:ℝ) ≤ a),
    intervalIntegral.integral_of_le hle]
  refine MeasureTheory.setIntegral_mono_set (hint.1) ?_ ?_
  · exact Filter.Eventually.of_forall fun t => hg t
  · exact Filter.Eventually.of_forall
      (fun x hx => Set.Ioc_subset_Ioc (by linarith) haT hx)

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **The `q`-polynomial is a von Mangoldt polynomial** (Track R, N62):
for `Q` a set of primes,

  `P₃(ξ) = ∑_{q ∈ Q} ((f(q)/q)·Λ(q))·𝐞(−ξ log q)`.

`Λ(q) = log q` on primes, so GHS's `∑ f(q)log q/q^s` is literally the
shape the mean value theorem is stated for, with coefficients
`a(q) = f(q)/q`.  No rearrangement is needed beyond commuting a product.

This is the join between §4's polynomials and Lemma 1: with it,
`intervalIntegral_vonMangoldt_mvt_long_le` applies to `ghsPrimePoly`
directly. -/
theorem ghsPrimePoly_eq_vonMangoldt_poly (f : ℕ → ℂ) (Q : Finset ℕ)
    (hQp : ∀ q ∈ Q, q.Prime) (ξ : ℝ) :
    ghsPrimePoly f Q ξ
      = ∑ q ∈ Q, ((f q / (q:ℂ)) * ((vonMangoldt q : ℝ) : ℂ))
          * ((Real.fourierChar (-(Real.log (q:ℝ) * ξ)) : Circle) : ℂ) := by
  rw [ghsPrimePoly]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hΛ : vonMangoldt q = Real.log (q:ℝ) :=
    ArithmeticFunction.vonMangoldt_apply_prime (hQp q hq)
  rw [hΛ]
  congr 1
  field_simp

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **The coefficients of the `q`-polynomial are small** (Track R,
N62): for `‖f‖ ≤ 1` and `q` prime,

  `‖f(q)/q‖²·Λ(q) ≤ log q / q²`.

This is what the mean value theorem's right-hand side becomes.  Against
its leading factor `≍ m`, the product is `≍ log q/q`, whose sum over
`q ≤ Q` is `≍ log Q` by Mertens — the `e^{−k}·log x` that `I₂` needs. -/
theorem norm_ghsPrime_coeff_sq_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (q : ℕ) (hq : q.Prime) :
    ‖f q / (q:ℂ)‖^2 * vonMangoldt q ≤ Real.log (q:ℝ) / (q:ℝ)^2 := by
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq.pos
  have hΛ : vonMangoldt q = Real.log (q:ℝ) :=
    ArithmeticFunction.vonMangoldt_apply_prime hq
  have hnorm : ‖f q / (q:ℂ)‖^2 = ‖f q‖^2 / (q:ℝ)^2 := by
    rw [norm_div, div_pow, Complex.norm_natCast]
  have hlog0 : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_natCast_nonneg q
  have hf2 : ‖f q‖^2 ≤ 1 := by nlinarith [hf q, norm_nonneg (f q)]
  rw [hΛ, hnorm, div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  nlinarith [hf2, hlog0]

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **Recovering von Mangoldt coefficients** (Track R, N63): for `q`
prime and any `w`,

  `(w/Λ(q))·Λ(q) = w`  and  `‖w/Λ(q)‖ = ‖w‖/log q`.

`integral_unit_sq_le_of_centred` quantifies over *every* coefficient
vector of the same moduli as the original, so the bound has to be
supplied for an arbitrary such `w'` rather than for the specific
coefficients of `P₃`.  This is the step that puts an arbitrary `w'`
into the mean value theorem's shape `a(q)·Λ(q)`: divide by `Λ(q)`,
which is legitimate since `Λ(q) = log q ≥ log 2 > 0` on primes.

The second identity is what makes the transfer free: the recovered
`a(q)` has modulus `‖w'(q)‖/log q`, which depends on `w'` only through
its modulus — so `norm_ghsPrime_coeff_sq_le`, stated on moduli,
applies to every member of the equal-modulus family at once. -/
theorem vonMangoldt_coeff_recover (q : ℕ) (hq : q.Prime) (w : ℂ) :
    (w / ((vonMangoldt q : ℝ):ℂ)) * ((vonMangoldt q : ℝ):ℂ) = w
      ∧ ‖w / ((vonMangoldt q : ℝ):ℂ)‖ = ‖w‖ / Real.log (q:ℝ) := by
  have hΛ : vonMangoldt q = Real.log (q:ℝ) :=
    ArithmeticFunction.vonMangoldt_apply_prime hq
  have hq2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq.two_le
  have hlogpos : (0:ℝ) < Real.log (q:ℝ) := by
    have : (1:ℝ) < (q:ℝ) := by linarith
    exact Real.log_pos this
  have hne : ((vonMangoldt q : ℝ):ℂ) ≠ 0 := by
    rw [hΛ]
    exact Complex.ofReal_ne_zero.mpr hlogpos.ne'
  refine ⟨div_mul_cancel₀ w hne, ?_⟩
  rw [norm_div, hΛ, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlogpos.le]

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **The recovered coefficients are small** (Track R, N63): if `w` has
the modulus of one of `P₃`'s coefficients, then

  `‖w/Λ(q)‖²·Λ(q) ≤ log q / q²`.

The modulus computation collapses exactly: `‖w/Λ(q)‖ = ‖w‖/log q =
(log q·‖f(q)‖/q)/log q = ‖f(q)/q‖`, so the recovered coefficient has
*precisely* the modulus of `f(q)/q` and
`norm_ghsPrime_coeff_sq_le` applies unchanged.

This is the whole content of the equal-modulus quantifier in
`integral_unit_sq_le_of_centred`: the bound never saw the phases, so
shifting them costs nothing. -/
theorem recovered_coeff_sq_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (q : ℕ)
    (hq : q.Prime) (w : ℂ)
    (hw : ‖w‖ = ‖(((Real.log (q:ℝ) : ℝ):ℂ) * f q) / (q:ℂ)‖) :
    ‖w / ((vonMangoldt q : ℝ):ℂ)‖^2 * vonMangoldt q
      ≤ Real.log (q:ℝ) / (q:ℝ)^2 := by
  have hq2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq.two_le
  have hlogpos : (0:ℝ) < Real.log (q:ℝ) := Real.log_pos (by linarith)
  have hq0 : (0:ℝ) < (q:ℝ) := by linarith
  obtain ⟨-, hmod⟩ := vonMangoldt_coeff_recover q hq w
  have hwval : ‖w‖ = Real.log (q:ℝ) * ‖f q‖ / (q:ℝ) := by
    rw [hw, norm_div, norm_mul, Complex.norm_real, Complex.norm_natCast,
      Real.norm_eq_abs, abs_of_nonneg hlogpos.le]
  have hkey : ‖w / ((vonMangoldt q : ℝ):ℂ)‖ = ‖f q / (q:ℂ)‖ := by
    rw [hmod, hwval, norm_div, Complex.norm_natCast]
    field_simp
  rw [hkey]
  exact norm_ghsPrime_coeff_sq_le f hf q hq

open Real Finset in
/-- **The `I₂` summand splits into Mertens plus a convergent tail**
(Track R, N64): for `q ≥ 2` and any `R`,

  `(6144·⌈2q/8⌉ + log q + R)·(log q/q²)
     ≤ 1536·(log q/q) + (6144 + R)·(log q/q²)`.

This is what the mean value theorem's right-hand side becomes once the
coefficients of `P₃` are substituted.  The leading factor `⌈2m/T⌉` at
`T = 8` is `⌈q/4⌉ ≤ q/4 + 1`, and multiplying by `log q/q²` turns the
`q/4` into `log q/q` — the Mertens sum, which is `≍ log Q` — while
everything else lands on `log q/q²`, which converges.

So `V ≍ ∑_{q ≤ Q} log q/q ≍ log Q`, and with `Q = x^{e^{1−k}}` that is
the `e^{−k}·log x` the `I₂` estimate needs. -/
theorem ghsPrime_mvt_summand_le (q : ℕ) (hq : 2 ≤ q) (R : ℝ) :
    (6144*((⌈2*(q:ℝ)/8⌉₊ : ℕ):ℝ) + Real.log (q:ℝ) + R)
        * (Real.log (q:ℝ)/(q:ℝ)^2)
      ≤ 1536 * (Real.log (q:ℝ)/(q:ℝ))
        + (6144 + R + Real.log (q:ℝ)) * (Real.log (q:ℝ)/(q:ℝ)^2) := by
  have hq0 : (0:ℝ) < (q:ℝ) := by
    have : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    linarith
  have hlog0 : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_natCast_nonneg q
  -- the ceiling is at most q/4 + 1
  have hceil : ((⌈2*(q:ℝ)/8⌉₊ : ℕ):ℝ) ≤ (q:ℝ)/4 + 1 := by
    have h1 : ((⌈2*(q:ℝ)/8⌉₊ : ℕ):ℝ) ≤ 2*(q:ℝ)/8 + 1 :=
      Nat.ceil_lt_add_one (by positivity) |>.le
    linarith
  have hmass : (0:ℝ) ≤ Real.log (q:ℝ)/(q:ℝ)^2 := by positivity
  -- 6144·⌈q/4⌉·(log q/q²) ≤ 1536·(log q/q) + 6144·(log q/q²)
  have hlead : 6144*((⌈2*(q:ℝ)/8⌉₊ : ℕ):ℝ) * (Real.log (q:ℝ)/(q:ℝ)^2)
      ≤ 1536 * (Real.log (q:ℝ)/(q:ℝ)) + 6144 * (Real.log (q:ℝ)/(q:ℝ)^2) := by
    have hstep : 6144*((⌈2*(q:ℝ)/8⌉₊ : ℕ):ℝ) * (Real.log (q:ℝ)/(q:ℝ)^2)
        ≤ 6144*((q:ℝ)/4 + 1) * (Real.log (q:ℝ)/(q:ℝ)^2) := by
      refine mul_le_mul_of_nonneg_right ?_ hmass
      linarith [hceil]
    refine le_trans hstep (le_of_eq ?_)
    field_simp
    ring
  nlinarith [hlead, hmass, hlog0]

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **An arbitrary prime-supported polynomial is a von Mangoldt one**
(Track R, N65): for `Q` a set of primes and any coefficients `w`,

  `∑_q w(q)·𝐞(−u log q) = ∑_q ((w(q)/Λ(q))·Λ(q))·𝐞(−u log q)`.

Trivial as an identity — it is `vonMangoldt_coeff_recover` applied
termwise — but it is the step that lets the mean value theorem be used
on the coefficient vectors that `integral_unit_sq_le_of_centred`
quantifies over, which are *not* `P₃`'s own.

Kept separate from the estimate that follows: the rewrite is exact, and
isolating it means the inequality chain never has to carry a division
that might be undefined. -/
theorem prime_poly_as_vonMangoldt (Q : Finset ℕ) (hQp : ∀ q ∈ Q, q.Prime)
    (w : ℕ → ℂ) (u : ℝ) :
    (∑ q ∈ Q, w q
        * ((Real.fourierChar (-(Real.log (q:ℝ) * u)) : Circle) : ℂ))
      = ∑ q ∈ Q, ((w q / ((vonMangoldt q : ℝ):ℂ)) * ((vonMangoldt q : ℝ):ℂ))
          * ((Real.fourierChar (-(Real.log (q:ℝ) * u)) : Circle) : ℂ) := by
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [(vonMangoldt_coeff_recover q (hQp q hq) (w q)).1]

open Real Finset in
/-- **The smallness condition at `T = 8`** (Track R, N65):
`2·⌈2m/8⌉ ≤ m` for `m ≥ 4`.

`inner_sum_long_le` needs the shells' step `h = ⌈2m/T⌉` to be at most
half the centre, so that the reach `a_J ≥ m/4` follows from maximality.
At `T = 8` this is `2·⌈m/4⌉ ≤ m/2 + 2 ≤ m`, which holds from `m ≥ 4` on
— so it imposes nothing beyond what `T² ≤ m` already demands. -/
theorem two_mul_ceil_quarter_le (m : ℕ) (hm : 4 ≤ m) :
    2*(⌈2*(m:ℝ)/8⌉₊) ≤ m := by
  have hmR : (4:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hceil : ((⌈2*(m:ℝ)/8⌉₊ : ℕ):ℝ) < 2*(m:ℝ)/8 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hreal : ((2*(⌈2*(m:ℝ)/8⌉₊) : ℕ):ℝ) ≤ (m:ℝ) := by
    push_cast
    linarith
  exact_mod_cast hreal

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **The centred energy of the `q`-polynomial** (Track R, N65): for any
coefficients of the right moduli,

  `∫_{−8}^{8} ‖∑_q w(q)·𝐞(−u log q)‖² du
     ≤ e^π·8·∑_q (6144·⌈2q/8⌉ + log q + e^{−π}·B + (√X+1)log₂X·log X)·(log q/q²)`.

This is GHS's Lemma 1 applied to `P₃`, at `T = 8` and for an arbitrary
member of the equal-modulus family that
`integral_unit_sq_le_of_centred` ranges over.

`T = 8` is forced from both sides: `inner_sum_long_le` needs
`T² ≤ q`, so `q ≥ 64` — which is GHS's own `T² ≤ n ≤ x` — while
`2·⌈2q/8⌉ ≤ q` costs nothing beyond that.  Smaller `T` fails the
smallness condition; larger `T` would raise the threshold on `q`
without benefit.

By `ghsPrime_mvt_summand_le` the right side is
`≍ ∑_q log q/q`, which Mertens makes `≍ log Q` — **but only for the
`6144·⌈2q/8⌉` term.**  The additive `e^{−π}·B` and
`(√X+1)log₂X·log X` are multiplied by `∑_q log q/q² = O(1)` and
contribute `≍ X` and `≍ √X log²X`, so they dominate the `≍ log Q` they
are compared against.  **Use `ghsPrime_centred_energy_free_le`**, which
removes the first identically (prime support) and the second by leaving
`T` free. -/
theorem ghsPrime_centred_energy_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (Q : Finset ℕ) (X : ℕ) (hX : 1 ≤ X)
    (hQp : ∀ q ∈ Q, q.Prime) (hQ64 : ∀ q ∈ Q, 64 ≤ q) (hQX : ∀ q ∈ Q, q ≤ X)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∑ q ∈ Q, Real.log (q:ℝ) ≤ B)
    (w : ℕ → ℂ)
    (hw : ∀ q ∈ Q, ‖w q‖ = ‖(((Real.log (q:ℝ) : ℝ):ℂ) * f q) / (q:ℂ)‖) :
    (∫ u in (-(8:ℝ))..(8:ℝ),
        ‖∑ q ∈ Q, w q
          * ((Real.fourierChar (-(Real.log (q:ℝ) * u)) : Circle) : ℂ)‖^2)
      ≤ Real.exp π * 8 * ∑ q ∈ Q,
          (6144*((⌈2*(q:ℝ)/8⌉₊ : ℕ):ℝ) + Real.log (q:ℝ)
            + Real.exp (-(π*(8:ℝ)^2/64)) * B
            + ((Nat.sqrt X + 1 : ℕ):ℝ) * ((Nat.log 2 X : ℕ):ℝ)
                * Real.log ((X:ℕ):ℝ))
          * (Real.log (q:ℝ)/(q:ℝ)^2) := by
  classical
  -- rewrite into von Mangoldt shape
  have hrw : (∫ u in (-(8:ℝ))..(8:ℝ),
      ‖∑ q ∈ Q, w q
        * ((Real.fourierChar (-(Real.log (q:ℝ) * u)) : Circle) : ℂ)‖^2)
      = ∫ u in (-(8:ℝ))..(8:ℝ),
        ‖∑ q ∈ Q, ((w q / ((vonMangoldt q : ℝ):ℂ))
            * ((vonMangoldt q : ℝ):ℂ))
          * ((Real.fourierChar (-(Real.log (q:ℝ) * u)) : Circle) : ℂ)‖^2 := by
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [prime_poly_as_vonMangoldt Q hQp w u]
  rw [hrw]
  -- the mean value theorem at T = 8
  have hmvt := intervalIntegral_vonMangoldt_mvt_long_le (8:ℝ) X Q
    (fun q => w q / ((vonMangoldt q : ℝ):ℂ))
    (fun q hq => by have := hQ64 q hq; omega)
    hQX hX (by norm_num)
    (fun m hm => by
      have h64 : (64:ℝ) ≤ (m:ℝ) := by exact_mod_cast hQ64 m hm
      have hsq : ((8:ℝ))^2 = 64 := by norm_num
      rw [hsq]
      exact h64)
    (fun m hm => two_mul_ceil_quarter_le m (by have := hQ64 m hm; omega))
    B hB
  refine le_trans hmvt ?_
  -- replace the coefficient energy by its bound
  have hcoef : ∀ q ∈ Q,
      (6144*((⌈2*(q:ℝ)/8⌉₊ : ℕ):ℝ) + Real.log (q:ℝ)
        + Real.exp (-(π*(8:ℝ)^2/64)) * B
        + ((Nat.sqrt X + 1 : ℕ):ℝ) * ((Nat.log 2 X : ℕ):ℝ)
            * Real.log ((X:ℕ):ℝ))
      * (‖w q / ((vonMangoldt q : ℝ):ℂ)‖^2 * vonMangoldt q)
      ≤ (6144*((⌈2*(q:ℝ)/8⌉₊ : ℕ):ℝ) + Real.log (q:ℝ)
          + Real.exp (-(π*(8:ℝ)^2/64)) * B
          + ((Nat.sqrt X + 1 : ℕ):ℝ) * ((Nat.log 2 X : ℕ):ℝ)
              * Real.log ((X:ℕ):ℝ))
        * (Real.log (q:ℝ)/(q:ℝ)^2) := by
    intro q hq
    have hbig : (0:ℝ) ≤ 6144*((⌈2*(q:ℝ)/8⌉₊ : ℕ):ℝ) + Real.log (q:ℝ)
        + Real.exp (-(π*(8:ℝ)^2/64)) * B
        + ((Nat.sqrt X + 1 : ℕ):ℝ) * ((Nat.log 2 X : ℕ):ℝ)
            * Real.log ((X:ℕ):ℝ) := by
      have h1 : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_natCast_nonneg q
      have h2 : (0:ℝ) ≤ Real.exp (-(π*(8:ℝ)^2/64)) * B :=
        mul_nonneg (Real.exp_pos _).le hB0
      have h3 : (0:ℝ) ≤ ((Nat.sqrt X + 1 : ℕ):ℝ) * ((Nat.log 2 X : ℕ):ℝ)
          * Real.log ((X:ℕ):ℝ) := by
        have := Real.log_natCast_nonneg X
        positivity
      positivity
    refine mul_le_mul_of_nonneg_left ?_ hbig
    exact recovered_coeff_sq_le f hf q (hQp q hq) (w q) (hw q hq)
  have hstep := Finset.sum_le_sum hcoef
  have hexp0 : (0:ℝ) ≤ Real.exp π * 8 := by positivity
  exact mul_le_mul_of_nonneg_left hstep hexp0

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **The per-frequency energy of `P₃`** (Track R, N66): for every
frequency `N`,

  `∫_{N−1/2}^{N+1/2} ‖P₃(t)‖² dt
     ≤ e^π·8·∑_q (6144·⌈2q/8⌉ + log q + e^{−π}·B + (√X+1)log₂X·log X)·(log q/q²)`.

This is `integral_line_halasz_le`'s `hV`, in the form it asks for: a
bound uniform in `N`.

Three facts combine.  `integral_unit_sq_le_of_centred` reduces the
frequency `N` to the origin, at the cost of quantifying over every
coefficient vector of the same moduli.  `integral_symm_widen` opens the
window from `[−1/2, 1/2]` to `[−8, 8]`, free because the integrand is a
squared norm.  And `ghsPrime_centred_energy_le` bounds the widened
integral for the whole equal-modulus family at once — which is exactly
why the quantifier costs nothing. -/
theorem ghsPrimePoly_unit_energy_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (Q : Finset ℕ) (X : ℕ) (hX : 1 ≤ X)
    (hQp : ∀ q ∈ Q, q.Prime) (hQ64 : ∀ q ∈ Q, 64 ≤ q) (hQX : ∀ q ∈ Q, q ≤ X)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∑ q ∈ Q, Real.log (q:ℝ) ≤ B)
    (hwide : ∀ w : ℕ → ℂ, IntervalIntegrable
      (fun u => ‖∑ q ∈ Q, w q
        * ((Real.fourierChar (-(Real.log (q:ℝ) * u)) : Circle) : ℂ)‖^2)
      volume (-(8:ℝ)) (8:ℝ))
    (N : ℝ) :
    (∫ t in (N - 1/2)..(N + 1/2), ‖ghsPrimePoly f Q t‖^2)
      ≤ Real.exp π * 8 * ∑ q ∈ Q,
          (6144*((⌈2*(q:ℝ)/8⌉₊ : ℕ):ℝ) + Real.log (q:ℝ)
            + Real.exp (-(π*(8:ℝ)^2/64)) * B
            + ((Nat.sqrt X + 1 : ℕ):ℝ) * ((Nat.log 2 X : ℕ):ℝ)
                * Real.log ((X:ℕ):ℝ))
          * (Real.log (q:ℝ)/(q:ℝ)^2) := by
  classical
  set V : ℝ := Real.exp π * 8 * ∑ q ∈ Q,
      (6144*((⌈2*(q:ℝ)/8⌉₊ : ℕ):ℝ) + Real.log (q:ℝ)
        + Real.exp (-(π*(8:ℝ)^2/64)) * B
        + ((Nat.sqrt X + 1 : ℕ):ℝ) * ((Nat.log 2 X : ℕ):ℝ)
            * Real.log ((X:ℕ):ℝ))
      * (Real.log (q:ℝ)/(q:ℝ)^2) with hV_def
  -- the coefficients of P₃
  set c : ℕ → ℂ := fun q =>
    (((Real.log (q:ℝ) : ℝ):ℂ) * f q) / (q:ℂ) with hc_def
  have hpoly : ∀ t : ℝ, ghsPrimePoly f Q t
      = ∑ q ∈ Q, c q
        * ((Real.fourierChar (-(Real.log (q:ℝ) * t)) : Circle) : ℂ) := by
    intro t
    rw [ghsPrimePoly]
  simp only [hpoly]
  refine ExpSums.integral_unit_sq_le_of_centred Q c
    (fun q => Real.log (q:ℝ)) V ?_ N
  intro w' hw'
  -- widen the window, then apply the centred estimate
  have hb : (-(1:ℝ)/2) = -((1:ℝ)/2) := by ring
  rw [hb]
  refine le_trans (integral_symm_widen
    (fun u => ‖∑ q ∈ Q, w' q
      * ((Real.fourierChar (-(Real.log (q:ℝ) * u)) : Circle) : ℂ)‖^2)
    (fun t => by positivity) ((1:ℝ)/2) 8 (by norm_num) (by norm_num)
    (hwide w')) ?_
  exact ghsPrime_centred_energy_le f hf Q X hX hQp hQ64 hQX B hB0 hB w'
    (fun q _ => hw' q)

open Finset Real in
/-- **The two prime masses over `Q`** (Track R, N67): for a set of
primes in `[2, X]`,

  `∑_q log q/q ≤ log X + 2`  and  `∑_q log q/q² ≤ 4`.

Both are already available and need no new analysis: the first is
`MertensFirst.sum_log_div_primesBelow_le_sharp`, whose leading constant
is `1`; the second is `sum_log_div_sq_le`, proved over the *integers*,
so it covers any set of primes for free.

These are the two masses `ghsPrime_mvt_summand_le` produces — the
Mertens sum, which carries the `log X`, and the convergent tail, which
contributes `O(1)`.  So `V ≍ log X`, and with `X = x^{e^{1−k}}` that is
`≍ e^{−k}·log x`: the factor whose cancellation against `I₁`'s `e^{k}`
leaves `L(x)` with no residual `k`. -/
theorem prime_masses_le (Q : Finset ℕ) (X : ℕ) (hX : 2 ≤ X)
    (hQp : ∀ q ∈ Q, q.Prime) (hQ2 : ∀ q ∈ Q, 2 ≤ q) (hQX : ∀ q ∈ Q, q ≤ X) :
    (∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ) ≤ Real.log ((X+1 : ℕ):ℝ) + 2)
      ∧ (∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ)^2 ≤ 4) := by
  classical
  constructor
  · -- Mertens, sharp form
    have hsub : Q ⊆ (X+1).primesBelow := by
      intro q hq
      rw [Nat.mem_primesBelow]
      exact ⟨by have := hQX q hq; omega, hQp q hq⟩
    have hmono : ∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ)
        ≤ ∑ p ∈ (X+1).primesBelow, Real.log (p:ℝ)/(p:ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun i _ _ => div_nonneg (Real.log_natCast_nonneg i) (Nat.cast_nonneg _))
    exact le_trans hmono
      (sum_log_div_primesBelow_le_sharp (X+1) (by omega))
  · -- the convergent tail, over the integers
    have hsub : Q ⊆ Finset.Icc 2 X := by
      intro q hq
      exact Finset.mem_Icc.mpr ⟨hQ2 q hq, hQX q hq⟩
    have hmono : ∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ)^2
        ≤ ∑ n ∈ Finset.Icc 2 X, Real.log (n:ℝ)/(n:ℝ)^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun i _ _ => by positivity)
    refine le_trans hmono ?_
    have hbase := sum_log_div_sq_le X (by omega)
    have hsqrt : (0:ℝ) ≤ 4/Real.sqrt (X:ℝ) := by positivity
    linarith

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **The `P_k` polynomial is a von Mangoldt polynomial** (Track R,
N68): for `P` a set of primes,

  `P₂(ξ) = ∑_p ((f(p)/(p·log(x/p)))·Λ(p))·𝐞(−ξ log p)`.

The same match as for `P₃`, with the extra `1/log(x/p)` absorbed into
the coefficient: `Λ(p) = log p` on primes, so GHS's
`∑ f(p)log p/(p^s log(x/p))` is again literally the mean value
theorem's shape, now with `a(p) = f(p)/(p·log(x/p))`. -/
theorem ghsBlockPoly_eq_vonMangoldt_poly (f : ℕ → ℂ) (x : ℕ) (P : Finset ℕ)
    (hPp : ∀ p ∈ P, p.Prime) (ξ : ℝ) :
    ghsBlockPoly f x P ξ
      = ∑ p ∈ P, ((f p / ((p:ℂ) * ((Real.log ((x:ℝ)/(p:ℝ)) : ℝ):ℂ)))
            * ((vonMangoldt p : ℝ):ℂ))
          * ((Real.fourierChar (-(Real.log (p:ℝ) * ξ)) : Circle) : ℂ) := by
  rw [ghsBlockPoly]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hΛ : vonMangoldt p = Real.log (p:ℝ) :=
    ArithmeticFunction.vonMangoldt_apply_prime (hPp p hp)
  rw [hΛ]
  congr 1
  ring

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **The coefficients of the `P_k` polynomial are small** (Track R,
N68): for `‖f‖ ≤ 1`, `p` prime and `2p ≤ x`,

  `‖f(p)/(p·log(x/p))‖²·Λ(p) ≤ log p / (p²·log²(x/p))`.

Against the mean value theorem's leading factor `≍ p` this becomes
`log p/(p·log²(x/p))`, which is exactly the mass
`sum_log_div_sq_ratio_block_mass_le` bounds by `≍ e^{k}/log x` — the
`I₁` estimate.

`2p ≤ x` is what makes `log(x/p) ≥ log 2 > 0`, so the coefficient is
defined; on a block it holds because the discards already imposed it. -/
theorem norm_ghsBlock_coeff_sq_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x p : ℕ) (hp : p.Prime) (h2p : 2*p ≤ x) :
    ‖f p / ((p:ℂ) * ((Real.log ((x:ℝ)/(p:ℝ)) : ℝ):ℂ))‖^2 * vonMangoldt p
      ≤ Real.log (p:ℝ) / ((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
  have hquot : (2:ℝ) ≤ (x:ℝ)/(p:ℝ) := by
    rw [le_div_iff₀ hp0]
    have hc : ((2*p : ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast h2p
    push_cast at hc; linarith
  have hlogpos : (0:ℝ) < Real.log ((x:ℝ)/(p:ℝ)) := Real.log_pos (by linarith)
  have hΛ : vonMangoldt p = Real.log (p:ℝ) :=
    ArithmeticFunction.vonMangoldt_apply_prime hp
  have hnorm : ‖f p / ((p:ℂ) * ((Real.log ((x:ℝ)/(p:ℝ)) : ℝ):ℂ))‖^2
      = ‖f p‖^2 / ((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2) := by
    rw [norm_div, div_pow, norm_mul, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hlogpos.le, mul_pow]
  have hlog0 : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
  have hf2 : ‖f p‖^2 ≤ 1 := by nlinarith [hf p, norm_nonneg (f p)]
  rw [hΛ, hnorm, div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  nlinarith [hf2, hlog0]

open Real Finset in
/-- **The `E₁` summand splits into the `I₁` mass plus a convergent tail**
(Track R, N69): for `p ≥ 2`, any `R`, and any `D ≥ 0`,

  `(6144·⌈2p/8⌉ + log p + R)·(log p/(p²·D))
     ≤ 1536·(log p/(p·D)) + (6144 + R + log p)·(log p/(p²·D))`.

The `E₁` analogue of `ghsPrime_mvt_summand_le`.  It is that lemma
divided by `D`: the mean value theorem's leading factor `⌈2m/T⌉` at
`T = 8` is `⌈p/4⌉ ≤ p/4 + 1`, and multiplying by `log p/(p²·D)` turns
the `p/4` into `log p/(p·D)`, leaving everything else on the
convergent `log p/(p²·D)`.

At `D = log²(x/p)` the leading mass is `∑_p log p/(p·log²(x/p))` —
exactly `sum_log_div_sq_ratio_block_mass_le`, GHS §4's `I₁ ≪ e^{k}/log x`
— while the tail is dominated by `∑_p log p/p² ≤ 4` up to the factor
`1/log²2`.  Keeping `D` abstract is what lets the same statement serve
both the block form and any later reweighting. -/
theorem ghsBlock_mvt_summand_le (p : ℕ) (hp : 2 ≤ p) (R D : ℝ) (hD : 0 ≤ D) :
    (6144*((⌈2*(p:ℝ)/8⌉₊ : ℕ):ℝ) + Real.log (p:ℝ) + R)
        * (Real.log (p:ℝ)/((p:ℝ)^2 * D))
      ≤ 1536 * (Real.log (p:ℝ)/((p:ℝ) * D))
        + (6144 + R + Real.log (p:ℝ)) * (Real.log (p:ℝ)/((p:ℝ)^2 * D)) := by
  have hkey := ghsPrime_mvt_summand_le p hp R
  have hL : (6144*((⌈2*(p:ℝ)/8⌉₊ : ℕ):ℝ) + Real.log (p:ℝ) + R)
        * (Real.log (p:ℝ)/((p:ℝ)^2 * D))
      = ((6144*((⌈2*(p:ℝ)/8⌉₊ : ℕ):ℝ) + Real.log (p:ℝ) + R)
          * (Real.log (p:ℝ)/(p:ℝ)^2)) / D := by
    rw [div_mul_eq_div_div]; ring
  have hR : 1536 * (Real.log (p:ℝ)/((p:ℝ) * D))
        + (6144 + R + Real.log (p:ℝ)) * (Real.log (p:ℝ)/((p:ℝ)^2 * D))
      = (1536 * (Real.log (p:ℝ)/(p:ℝ))
          + (6144 + R + Real.log (p:ℝ)) * (Real.log (p:ℝ)/(p:ℝ)^2)) / D := by
    rw [div_mul_eq_div_div, div_mul_eq_div_div]; ring
  rw [hL, hR]
  exact div_le_div_of_nonneg_right hkey hD

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **The band energy of the `P_k` polynomial** (Track R, N70): for `P`
a set of primes in `[64, X]` with `2p ≤ x`,

  `∫_{−8}^{8} ‖P₂(ξ)‖² dξ
     ≤ e^π·8·∑_p (6144·⌈2p/8⌉ + log p + e^{−π}·B + (√X+1)log₂X·log X)
              ·(log p/(p²·log²(x/p)))`.

GHS's Lemma 1 applied to `P₂`, at `T = 8`.  Unlike `P₃`'s route this
needs no equal-modulus family: `E₁` is a *whole-line weighted* energy,
so `integral_sq_weight_le` asks for the band integral of `P₂` itself
rather than a per-frequency bound, and the mean value theorem applies
to the polynomial directly.

`T = 8` is forced exactly as before — `inner_sum_long_le` needs
`T² ≤ p`, so `p ≥ 64`, which is GHS's own `T² ≤ n ≤ x`, and
`2·⌈2p/8⌉ ≤ p` costs nothing beyond that.

By `ghsBlock_mvt_summand_le` the right side is
`≍ ∑_p log p/(p·log²(x/p))`, which
`sum_log_div_sq_ratio_block_mass_le` makes `≍ e^{k}/log x` — **for the
leading term only.**  As in `ghsPrime_centred_energy_le`, the additive
`e^{−π}·B` and `(√X+1)log₂X·log X` are multiplied by an `O(1)` mass and
swamp it.  **Use `ghsBlock_centred_energy_free_le`.** -/
theorem ghsBlock_centred_energy_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x : ℕ) (P : Finset ℕ) (X : ℕ) (hX : 1 ≤ X)
    (hPp : ∀ p ∈ P, p.Prime) (hP64 : ∀ p ∈ P, 64 ≤ p) (hPX : ∀ p ∈ P, p ≤ X)
    (h2p : ∀ p ∈ P, 2*p ≤ x)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∑ p ∈ P, Real.log (p:ℝ) ≤ B) :
    (∫ ξ in (-(8:ℝ))..(8:ℝ), ‖ghsBlockPoly f x P ξ‖^2)
      ≤ Real.exp π * 8 * ∑ p ∈ P,
          (6144*((⌈2*(p:ℝ)/8⌉₊ : ℕ):ℝ) + Real.log (p:ℝ)
            + Real.exp (-(π*(8:ℝ)^2/64)) * B
            + ((Nat.sqrt X + 1 : ℕ):ℝ) * ((Nat.log 2 X : ℕ):ℝ)
                * Real.log ((X:ℕ):ℝ))
          * (Real.log (p:ℝ)/((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2)) := by
  classical
  -- rewrite into von Mangoldt shape
  have hrw : (∫ ξ in (-(8:ℝ))..(8:ℝ), ‖ghsBlockPoly f x P ξ‖^2)
      = ∫ ξ in (-(8:ℝ))..(8:ℝ),
        ‖∑ p ∈ P, ((f p / ((p:ℂ) * ((Real.log ((x:ℝ)/(p:ℝ)) : ℝ):ℂ)))
            * ((vonMangoldt p : ℝ):ℂ))
          * ((Real.fourierChar (-(Real.log (p:ℝ) * ξ)) : Circle) : ℂ)‖^2 := by
    refine intervalIntegral.integral_congr fun ξ _ => ?_
    rw [ghsBlockPoly_eq_vonMangoldt_poly f x P hPp ξ]
  rw [hrw]
  -- the mean value theorem at T = 8
  have hmvt := intervalIntegral_vonMangoldt_mvt_long_le (8:ℝ) X P
    (fun p => f p / ((p:ℂ) * ((Real.log ((x:ℝ)/(p:ℝ)) : ℝ):ℂ)))
    (fun p hp => by have := hP64 p hp; omega)
    hPX hX (by norm_num)
    (fun m hm => by
      have h64 : (64:ℝ) ≤ (m:ℝ) := by exact_mod_cast hP64 m hm
      have hsq : ((8:ℝ))^2 = 64 := by norm_num
      rw [hsq]
      exact h64)
    (fun m hm => two_mul_ceil_quarter_le m (by have := hP64 m hm; omega))
    B hB
  refine le_trans hmvt ?_
  -- replace the coefficient energy by its bound
  have hcoef : ∀ p ∈ P,
      (6144*((⌈2*(p:ℝ)/8⌉₊ : ℕ):ℝ) + Real.log (p:ℝ)
        + Real.exp (-(π*(8:ℝ)^2/64)) * B
        + ((Nat.sqrt X + 1 : ℕ):ℝ) * ((Nat.log 2 X : ℕ):ℝ)
            * Real.log ((X:ℕ):ℝ))
      * (‖f p / ((p:ℂ) * ((Real.log ((x:ℝ)/(p:ℝ)) : ℝ):ℂ))‖^2 * vonMangoldt p)
      ≤ (6144*((⌈2*(p:ℝ)/8⌉₊ : ℕ):ℝ) + Real.log (p:ℝ)
          + Real.exp (-(π*(8:ℝ)^2/64)) * B
          + ((Nat.sqrt X + 1 : ℕ):ℝ) * ((Nat.log 2 X : ℕ):ℝ)
              * Real.log ((X:ℕ):ℝ))
        * (Real.log (p:ℝ)/((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2)) := by
    intro p hp
    have hbig : (0:ℝ) ≤ 6144*((⌈2*(p:ℝ)/8⌉₊ : ℕ):ℝ) + Real.log (p:ℝ)
        + Real.exp (-(π*(8:ℝ)^2/64)) * B
        + ((Nat.sqrt X + 1 : ℕ):ℝ) * ((Nat.log 2 X : ℕ):ℝ)
            * Real.log ((X:ℕ):ℝ) := by
      have h1 : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
      have h2 : (0:ℝ) ≤ Real.exp (-(π*(8:ℝ)^2/64)) * B :=
        mul_nonneg (Real.exp_pos _).le hB0
      have h3 : (0:ℝ) ≤ ((Nat.sqrt X + 1 : ℕ):ℝ) * ((Nat.log 2 X : ℕ):ℝ)
          * Real.log ((X:ℕ):ℝ) := by
        have := Real.log_natCast_nonneg X
        positivity
      positivity
    refine mul_le_mul_of_nonneg_left ?_ hbig
    exact norm_ghsBlock_coeff_sq_le f hf x p (hPp p hp) (h2p p hp)
  have hstep := Finset.sum_le_sum hcoef
  have hexp0 : (0:ℝ) ≤ Real.exp π * 8 := by positivity
  exact mul_le_mul_of_nonneg_left hstep hexp0

open Real Finset in
/-- **The honest second block mass** (Track R, N157): for `P` a set of
primes with `2p ≤ x`,

  `∑_{p∈P} log p/(p²·log²(x/p)) ≤ 16/log²x + 4/(√⌊√x⌋·log²2)`.

`block_masses_le`'s second component is `4/log²2 ≈ 8.3`, obtained by
discarding `log²(x/p) ≥ log²2`.  That is `O(1)` where the truth is
`O(1/log²x)`, and the slack is fatal downstream: in
`ghsBlock_E1_free_le` this mass multiplies a **forced** `T ≍ √(log x)`,
so an `O(1)` bound gives `E₁ ≍ √(log x)` rather than `≍ e^{k}/log x`
and the final estimate overshoots `x·L(x)` by `(log x)^{3/4}`.

The `log²2` bound is tight only at `p ≈ x/2`, where `log p/p²` is
negligible — so splitting at `√x` recovers everything:

* `p ≤ ⌊√x⌋` gives `p² ≤ x`, hence `x ≤ (x/p)²` and
  `log x ≤ 2·log(x/p)`; the term is then `≤ log p/(p²·(log²x/4))`, and
  `sum_log_div_sq_le`'s `∑ log n/n² ≤ 4` closes the half at `16/log²x`.
* `p > ⌊√x⌋` keeps only `log(x/p) ≥ log 2`, and the primes are
  discarded wholesale against `sum_log_div_sq_tail_le`, costing
  `4/(√⌊√x⌋·log²2)` — smaller than any power of `1/log x`.

No block hypothesis is used: the bound holds for any set of primes
below `x/2`, which is why it is stated separately from
`block_masses_le` rather than inside it. -/
theorem sum_log_div_sq_ratio_sq_le (x : ℕ) (hx : 2 ≤ x) (P : Finset ℕ)
    (hPp : ∀ p ∈ P, p.Prime) (h2p : ∀ p ∈ P, 2*p ≤ x) :
    ∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2)
      ≤ 16/(Real.log (x:ℝ))^2
        + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2) := by
  classical
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hxR : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hlogx : (0:ℝ) < Real.log (x:ℝ) := Real.log_pos (by linarith)
  have hs1 : 1 ≤ Nat.sqrt x := Nat.sqrt_pos.mpr (by omega)
  have hsR : (0:ℝ) < Real.sqrt ((Nat.sqrt x : ℕ):ℝ) := by
    refine Real.sqrt_pos.mpr ?_
    exact_mod_cast hs1
  rw [← Finset.sum_filter_add_sum_filter_not P (fun p => p ≤ Nat.sqrt x)]
  refine add_le_add ?_ ?_
  · -- small primes: `x/p ≥ √x`, so `log(x/p) ≥ ½·log x`
    have hterm : ∀ p ∈ P.filter (fun p => p ≤ Nat.sqrt x),
        Real.log (p:ℝ)/((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2)
          ≤ 4 * (Real.log (p:ℝ)/(p:ℝ)^2) / (Real.log (x:ℝ))^2 := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hpp : p.Prime := hPp p hp.1
      have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
      have hpsq : (p:ℝ)^2 ≤ (x:ℝ) := by
        have hsq : Nat.sqrt x * Nat.sqrt x ≤ x := by
          simpa [pow_two] using Nat.sqrt_le' x
        have h1 : p * p ≤ x := le_trans (Nat.mul_le_mul hp.2 hp.2) hsq
        have h2 : ((p*p : ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast h1
        push_cast at h2; nlinarith
      have hhalf : Real.log (x:ℝ) ≤ 2 * Real.log ((x:ℝ)/(p:ℝ)) := by
        have hxq : (x:ℝ) ≤ ((x:ℝ)/(p:ℝ))^2 := by
          rw [div_pow, le_div_iff₀ (by positivity)]
          nlinarith [hpsq, hxR]
        calc Real.log (x:ℝ) ≤ Real.log (((x:ℝ)/(p:ℝ))^2) :=
              Real.log_le_log (by linarith) hxq
          _ = 2 * Real.log ((x:ℝ)/(p:ℝ)) := by
              rw [Real.log_pow]; push_cast; ring
      have hlogp : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
      have hq4 : (Real.log (x:ℝ))^2/4 ≤ (Real.log ((x:ℝ)/(p:ℝ)))^2 := by
        nlinarith [hhalf, hlogx]
      have hrw : 4 * (Real.log (p:ℝ)/(p:ℝ)^2) / (Real.log (x:ℝ))^2
          = Real.log (p:ℝ)/((p:ℝ)^2 * ((Real.log (x:ℝ))^2/4)) := by
        field_simp
      rw [hrw]
      refine div_le_div_of_nonneg_left hlogp (by positivity) ?_
      exact mul_le_mul_of_nonneg_left hq4 (sq_nonneg (p:ℝ))
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_div, ← Finset.mul_sum]
    have hsub : P.filter (fun p => p ≤ Nat.sqrt x) ⊆ Finset.Icc 2 x := by
      intro p hp
      rw [Finset.mem_filter] at hp
      refine Finset.mem_Icc.mpr ⟨(hPp p hp.1).two_le, ?_⟩
      have := h2p p hp.1; omega
    have hmono : ∑ p ∈ P.filter (fun p => p ≤ Nat.sqrt x),
          Real.log (p:ℝ)/(p:ℝ)^2
        ≤ ∑ n ∈ Finset.Icc 2 x, Real.log (n:ℝ)/(n:ℝ)^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    have hmass : ∑ p ∈ P.filter (fun p => p ≤ Nat.sqrt x),
        Real.log (p:ℝ)/(p:ℝ)^2 ≤ 4 := by
      have hfull := sum_log_div_sq_le x (by omega)
      have h4 : (0:ℝ) ≤ 4/Real.sqrt (x:ℝ) := by positivity
      linarith
    have h16 : 4 * ∑ p ∈ P.filter (fun p => p ≤ Nat.sqrt x),
        Real.log (p:ℝ)/(p:ℝ)^2 ≤ 16 := by linarith
    gcongr
  · -- large primes: `log(x/p) ≥ log 2`, discarded against the tail
    have hterm : ∀ p ∈ P.filter (fun p => ¬ (p ≤ Nat.sqrt x)),
        Real.log (p:ℝ)/((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2)
          ≤ (Real.log (p:ℝ)/(p:ℝ)^2) / (Real.log 2)^2 := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hpp : p.Prime := hPp p hp.1
      have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
      have hquot : (2:ℝ) ≤ (x:ℝ)/(p:ℝ) := by
        rw [le_div_iff₀ hp0]
        have hc : ((2*p : ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast h2p p hp.1
        push_cast at hc; linarith
      have hlogle : Real.log 2 ≤ Real.log ((x:ℝ)/(p:ℝ)) :=
        Real.log_le_log (by norm_num) hquot
      have hsq : (Real.log 2)^2 ≤ (Real.log ((x:ℝ)/(p:ℝ)))^2 := by nlinarith
      have hlogp : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
      rw [div_div]
      refine div_le_div_of_nonneg_left hlogp (by positivity) ?_
      exact mul_le_mul_of_nonneg_left hsq (sq_nonneg (p:ℝ))
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_div]
    have hsub : P.filter (fun p => ¬ (p ≤ Nat.sqrt x))
        ⊆ Finset.Icc (Nat.sqrt x + 1) x := by
      intro p hp
      rw [Finset.mem_filter] at hp
      refine Finset.mem_Icc.mpr ⟨by omega, ?_⟩
      have := h2p p hp.1; omega
    have hmono : ∑ p ∈ P.filter (fun p => ¬ (p ≤ Nat.sqrt x)),
          Real.log (p:ℝ)/(p:ℝ)^2
        ≤ ∑ n ∈ Finset.Icc (Nat.sqrt x + 1) x, Real.log (n:ℝ)/(n:ℝ)^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    have hchain : ∑ p ∈ P.filter (fun p => ¬ (p ≤ Nat.sqrt x)),
        Real.log (p:ℝ)/(p:ℝ)^2
          ≤ 4/Real.sqrt ((Nat.sqrt x : ℕ):ℝ) :=
      le_trans hmono (sum_log_div_sq_tail_le (Nat.sqrt x) x hs1)
    have hfin : 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)
        = (4/Real.sqrt ((Nat.sqrt x : ℕ):ℝ))/(Real.log 2)^2 := by
      rw [div_div]
    rw [hfin]
    gcongr

open Real Finset in
/-- **The two block masses** (Track R, N71): for `P` a set of primes in
the `k`-th block of `x` with `2p ≤ x` and `p ≤ X`,

  `∑_p log p/(p·log²(x/p)) ≤ (e^{2k}/log²x)·(4((e−1)e^{−k}log x + log 2) + 4log 4)`
  `∑_p log p/(p²·log²(x/p)) ≤ 4/log²2`.

The `E₁` analogue of `prime_masses_le`, and again no new analysis: the
first conjunct *is* `sum_log_div_sq_ratio_block_mass_le`, and the second
is `prime_masses_le`'s convergent tail divided by `log²2`, since
`2p ≤ x` forces `log(x/p) ≥ log 2`.

These are the two masses `ghsBlock_mvt_summand_le` produces.  The first
carries the whole `e^{k}/log x` — GHS §4's `I₁` — and the second is
`O(1)`, so it is dominated once the leading term is multiplied by the
mean value theorem's `p`. -/
theorem block_masses_le (x k : ℕ) (hx : 2 ≤ x) (hk : 1 ≤ k) (X : ℕ) (hX : 2 ≤ X)
    (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k)
    (h2p : ∀ p ∈ P, 2*p ≤ x) (hPX : ∀ p ∈ P, p ≤ X) :
    (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * (Real.log ((x:ℝ)/(p:ℝ)))^2)
        ≤ (Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
            * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
                + Real.log 2) + 4 * Real.log 4))
      ∧ (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2)
        ≤ 4/(Real.log 2)^2) := by
  classical
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨sum_log_div_sq_ratio_block_mass_le x k hx hk P hP, ?_⟩
  -- the squared denominator is at least `log²2` on the block
  have hterm : ∀ p ∈ P, Real.log (p:ℝ)/((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2)
      ≤ (Real.log (p:ℝ)/(p:ℝ)^2)/(Real.log 2)^2 := by
    intro p hp
    have hpp : p.Prime := (hP p hp).1
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
    have hquot : (2:ℝ) ≤ (x:ℝ)/(p:ℝ) := by
      rw [le_div_iff₀ hp0]
      have hc : ((2*p : ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast h2p p hp
      push_cast at hc; linarith
    have hlogle : Real.log 2 ≤ Real.log ((x:ℝ)/(p:ℝ)) :=
      Real.log_le_log (by norm_num) hquot
    have hsq : (Real.log 2)^2 ≤ (Real.log ((x:ℝ)/(p:ℝ)))^2 := by nlinarith
    have hlog0 : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
    rw [div_div]
    refine div_le_div_of_nonneg_left hlog0 (by positivity) ?_
    exact mul_le_mul_of_nonneg_left hsq (sq_nonneg (p:ℝ))
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_div]
  have htail := (prime_masses_le P X hX (fun p hp => (hP p hp).1)
    (fun p hp => (hP p hp).1.two_le) hPX).2
  exact div_le_div_of_nonneg_right htail (by positivity)

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **`E₁`, the whole-line weighted energy of `P_k`** (Track R, N72):
with `S := ∑_p log p/(p·|log(x/p)|)` the trivial sup of `P₂`,

  `∫_ℝ ‖P₂(ξ)‖²·w(ξ) dξ
     ≤ C·e^π·8·∑_p (6144·⌈2p/8⌉ + log p + e^{−π}B + (√X+1)log₂X·log X)
              ·(log p/(p²·log²(x/p)))
       + S²·Wtail`.

This is the quantity `pairing_halasz_le` consumes as `hE₁`, in the form
it asks for.  Two facts compose: `integral_sq_weight_le` reduces the
whole line to the band `[−8, 8]` (weight discarded against its sup `C`)
plus a tail (polynomial discarded against its own sup `S`, paid for by
the weight's tail mass `Wtail`), and `ghsBlock_centred_energy_le` is
Lemma 1 on the band.

The band width is `8` because that is where Lemma 1 lives — `T² ≤ p`
forces `p ≥ 64`, GHS's own `T² ≤ n ≤ x` — and the tail mass is
`O(1/T)` for a normalised window, so the split costs nothing.

The integrability side conditions stay as hypotheses: they concern the
window `w`, which §4 has not yet fixed.  `P₂` itself is continuous
(`continuous_ghsBlockPoly`), so nothing is hidden on that side. -/
theorem ghsBlock_weighted_energy_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x : ℕ) (P : Finset ℕ) (X : ℕ) (hX : 1 ≤ X)
    (hPp : ∀ p ∈ P, p.Prime) (hP64 : ∀ p ∈ P, 64 ≤ p) (hPX : ∀ p ∈ P, p ≤ X)
    (h2p : ∀ p ∈ P, 2*p ≤ x)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∑ p ∈ P, Real.log (p:ℝ) ≤ B)
    (w : ℝ → ℝ) (C Wtail : ℝ)
    (hC : ∀ ξ, w ξ ≤ C) (hw0 : ∀ ξ, 0 ≤ w ξ)
    (hWtail : (∫ ξ in {ξ : ℝ | (8:ℝ) < |ξ|}, w ξ) ≤ Wtail)
    (hint : Integrable (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ))
    (hband : IntervalIntegrable (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ)
      volume (-(8:ℝ)) (8:ℝ))
    (hband2 : IntervalIntegrable (fun ξ => ‖ghsBlockPoly f x P ξ‖^2)
      volume (-(8:ℝ)) (8:ℝ))
    (htailP : IntegrableOn (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ)
      {ξ : ℝ | (8:ℝ) < |ξ|})
    (htailw : IntegrableOn w {ξ : ℝ | (8:ℝ) < |ξ|}) :
    (∫ ξ, ‖ghsBlockPoly f x P ξ‖^2 * w ξ)
      ≤ C * (Real.exp π * 8 * ∑ p ∈ P,
          (6144*((⌈2*(p:ℝ)/8⌉₊ : ℕ):ℝ) + Real.log (p:ℝ)
            + Real.exp (-(π*(8:ℝ)^2/64)) * B
            + ((Nat.sqrt X + 1 : ℕ):ℝ) * ((Nat.log 2 X : ℕ):ℝ)
                * Real.log ((X:ℕ):ℝ))
          * (Real.log (p:ℝ)/((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2)))
        + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
            * Wtail := by
  classical
  have hC0 : (0:ℝ) ≤ C := le_trans (hw0 0) (hC 0)
  have hsplit := integral_sq_weight_le (ghsBlockPoly f x P) w (8:ℝ) C
    (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|)) Wtail
    (by norm_num) hC hw0 (norm_ghsBlockPoly_le f hf x P) hWtail
    hint hband hband2 htailP htailw
  refine le_trans hsplit ?_
  have hband_le := ghsBlock_centred_energy_le f hf x P X hX hPp hP64 hPX h2p
    B hB0 hB
  have := mul_le_mul_of_nonneg_left hband_le hC0
  linarith

open Real Finset in
/-- **The `E₁` energy sum over a block** (Track R, N73): for `P` a set of
primes in the `k`-th block of `x` with `2p ≤ x` and `p ≤ X`, and any
`R ≥ 0`,

  `∑_p (6144·⌈2p/8⌉ + log p + R)·(log p/(p²·log²(x/p)))
     ≤ 1536·(e^{2k}/log²x)·(4((e−1)e^{−k}log x + log 2) + 4log 4)
       + (6144 + R + log X)·(4/log²2)`.

This is what `ghsBlock_centred_energy_le`'s right-hand side becomes on a
block.  The leading term is `≍ e^{k}/log x` — GHS §4's `I₁` — and the
remainder is `O(R + log X)`, which the mean value theorem's `p` has
already paid for.

Three facts compose and nothing new is proved: `ghsBlock_mvt_summand_le`
splits each summand at `D = log²(x/p)`, and the two halves land exactly
on the two masses of `block_masses_le`.  The only extra step is
`log p ≤ log X`, which pulls the varying `log p` out of the convergent
half. -/
theorem ghsBlock_energy_sum_le (x k X : ℕ) (hx : 2 ≤ x) (hk : 1 ≤ k)
    (hX : 2 ≤ X) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k)
    (h2p : ∀ p ∈ P, 2*p ≤ x) (hPX : ∀ p ∈ P, p ≤ X)
    (R : ℝ) (hR : 0 ≤ R) :
    ∑ p ∈ P, (6144*((⌈2*(p:ℝ)/8⌉₊ : ℕ):ℝ) + Real.log (p:ℝ) + R)
        * (Real.log (p:ℝ)/((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2))
      ≤ 1536 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
            * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
                + Real.log 2) + 4 * Real.log 4))
        + (6144 + R + Real.log (X:ℝ)) * (4/(Real.log 2)^2) := by
  classical
  obtain ⟨hmass1, hmass2⟩ := block_masses_le x k hx hk X hX P hP h2p hPX
  -- split each summand at `D = log²(x/p)`
  have hterm : ∀ p ∈ P,
      (6144*((⌈2*(p:ℝ)/8⌉₊ : ℕ):ℝ) + Real.log (p:ℝ) + R)
          * (Real.log (p:ℝ)/((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2))
        ≤ 1536 * (Real.log (p:ℝ)/((p:ℝ) * (Real.log ((x:ℝ)/(p:ℝ)))^2))
          + (6144 + R + Real.log (X:ℝ))
              * (Real.log (p:ℝ)/((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2)) := by
    intro p hp
    have hpp : p.Prime := (hP p hp).1
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
    have hsplit := ghsBlock_mvt_summand_le p hpp.two_le R
      ((Real.log ((x:ℝ)/(p:ℝ)))^2) (sq_nonneg _)
    -- replace the varying `log p` by `log X`
    have hlogX : Real.log (p:ℝ) ≤ Real.log (X:ℝ) := by
      have hpX : (p:ℝ) ≤ (X:ℝ) := by exact_mod_cast hPX p hp
      exact Real.log_le_log hp0 hpX
    have hmass : (0:ℝ)
        ≤ Real.log (p:ℝ)/((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2) := by
      have := Real.log_natCast_nonneg p
      positivity
    nlinarith [hsplit, hmass, hlogX]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hRX : (0:ℝ) ≤ 6144 + R + Real.log (X:ℝ) := by
    have := Real.log_natCast_nonneg X
    linarith
  have h1 : 1536 * (∑ p ∈ P,
      Real.log (p:ℝ)/((p:ℝ) * (Real.log ((x:ℝ)/(p:ℝ)))^2))
      ≤ 1536 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
          * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
              + Real.log 2) + 4 * Real.log 4)) :=
    mul_le_mul_of_nonneg_left hmass1 (by norm_num)
  have h2 : (6144 + R + Real.log (X:ℝ)) * (∑ p ∈ P,
      Real.log (p:ℝ)/((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2))
      ≤ (6144 + R + Real.log (X:ℝ)) * (4/(Real.log 2)^2) :=
    mul_le_mul_of_nonneg_left hmass2 hRX
  linarith

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **`E₁ ≪ e^{k}/log x`** (Track R, N74): the `hE₁` that
`pairing_halasz_le` consumes, for `P` a set of primes in the `k`-th
block of `x`.  With
`R := e^{−π}·B + (√X+1)·log₂X·log X` and `S` the trivial sup of `P₂`,

  `∫_ℝ ‖P₂‖²·w
     ≤ C·e^π·8·(1536·(e^{2k}/log²x)(4((e−1)e^{−k}log x + log 2) + 4log 4)
                 + (6144 + R + log X)·(4/log²2))
       + S²·Wtail`,

whose leading term is `≍ C·e^{k}/log x`.

The `E₁` sub-chain closes here.  `ghsBlock_weighted_energy_le` reduces
the whole line to Lemma 1 on `[−8, 8]`, and `ghsBlock_energy_sum_le`
evaluates Lemma 1's right-hand side on a block.  Nothing else is
needed: the two were built to meet.

Against `V ≍ e^{−k}·log x` the product `E₁·V` is `≍ 1`, with the `k`
cancelling — which is what leaves `L(x)` in §4's final bound with no
residual dependence on the block index.

**The `≍ e^{k}/log x` reading holds only for the leading term.**  This
routes through `ghsBlock_centred_energy_le`, whose additive `e^{−π}·B`
and `(√X+1)log₂X·log X` are multiplied by an `O(1)` mass and dominate
at `≍ X`.  Re-derive through `ghsBlock_centred_energy_free_le` at
`T ≍ √(log X)` for a bound that delivers the stated magnitude. -/
theorem ghsBlock_E1_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x k X : ℕ) (hx : 2 ≤ x) (hk : 1 ≤ k) (hX : 2 ≤ X) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k)
    (hP64 : ∀ p ∈ P, 64 ≤ p) (hPX : ∀ p ∈ P, p ≤ X)
    (h2p : ∀ p ∈ P, 2*p ≤ x)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∑ p ∈ P, Real.log (p:ℝ) ≤ B)
    (w : ℝ → ℝ) (C Wtail : ℝ)
    (hC : ∀ ξ, w ξ ≤ C) (hw0 : ∀ ξ, 0 ≤ w ξ)
    (hWtail : (∫ ξ in {ξ : ℝ | (8:ℝ) < |ξ|}, w ξ) ≤ Wtail)
    (hint : Integrable (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ))
    (hband : IntervalIntegrable (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ)
      volume (-(8:ℝ)) (8:ℝ))
    (hband2 : IntervalIntegrable (fun ξ => ‖ghsBlockPoly f x P ξ‖^2)
      volume (-(8:ℝ)) (8:ℝ))
    (htailP : IntegrableOn (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ)
      {ξ : ℝ | (8:ℝ) < |ξ|})
    (htailw : IntegrableOn w {ξ : ℝ | (8:ℝ) < |ξ|}) :
    (∫ ξ, ‖ghsBlockPoly f x P ξ‖^2 * w ξ)
      ≤ C * (Real.exp π * 8 *
          (1536 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
              * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
                  + Real.log 2) + 4 * Real.log 4))
            + (6144 + (Real.exp (-(π*(8:ℝ)^2/64)) * B
                + ((Nat.sqrt X + 1 : ℕ):ℝ) * ((Nat.log 2 X : ℕ):ℝ)
                    * Real.log ((X:ℕ):ℝ))
              + Real.log (X:ℝ)) * (4/(Real.log 2)^2)))
        + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
            * Wtail := by
  classical
  have hC0 : (0:ℝ) ≤ C := le_trans (hw0 0) (hC 0)
  have hX1 : 1 ≤ X := by omega
  have hband_le := ghsBlock_weighted_energy_le f hf x P X hX1
    (fun p hp => (hP p hp).1) hP64 hPX h2p B hB0 hB w C Wtail hC hw0 hWtail
    hint hband hband2 htailP htailw
  refine le_trans hband_le ?_
  -- the residue `R` collected from Lemma 1's additive terms
  set R : ℝ := Real.exp (-(π*(8:ℝ)^2/64)) * B
      + ((Nat.sqrt X + 1 : ℕ):ℝ) * ((Nat.log 2 X : ℕ):ℝ)
          * Real.log ((X:ℕ):ℝ) with hR_def
  have hR : (0:ℝ) ≤ R := by
    have h1 : (0:ℝ) ≤ Real.exp (-(π*(8:ℝ)^2/64)) * B :=
      mul_nonneg (Real.exp_pos _).le hB0
    have h2 : (0:ℝ) ≤ ((Nat.sqrt X + 1 : ℕ):ℝ) * ((Nat.log 2 X : ℕ):ℝ)
        * Real.log ((X:ℕ):ℝ) := by
      have := Real.log_natCast_nonneg X
      positivity
    rw [hR_def]; linarith
  -- reassociate Lemma 1's coefficient into `(… + log p + R)`
  have hcongr : (∑ p ∈ P,
      (6144*((⌈2*(p:ℝ)/8⌉₊ : ℕ):ℝ) + Real.log (p:ℝ)
        + Real.exp (-(π*(8:ℝ)^2/64)) * B
        + ((Nat.sqrt X + 1 : ℕ):ℝ) * ((Nat.log 2 X : ℕ):ℝ)
            * Real.log ((X:ℕ):ℝ))
      * (Real.log (p:ℝ)/((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2)))
      = ∑ p ∈ P, (6144*((⌈2*(p:ℝ)/8⌉₊ : ℕ):ℝ) + Real.log (p:ℝ) + R)
          * (Real.log (p:ℝ)/((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2)) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hR_def]; ring
  rw [hcongr]
  have hsum := ghsBlock_energy_sum_le x k X hx hk hX P hP h2p hPX R hR
  have hexp0 : (0:ℝ) ≤ Real.exp π * 8 := by positivity
  have hstep := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hsum hexp0) hC0
  linarith

open MeasureTheory Real Finset in
/-- **The integrability workhorse for §4** (Track R, N76): a continuous
non-negative `g` with `g ξ ≤ K/(1+ξ²)` is integrable on `ℝ`, on every
interval, and on every tail set.

Every integrability side condition of `pairing_halasz_sqrt_le` and of
`integral_sq_weight_le` has this shape.  The three §4 polynomials are
continuous (`continuous_ghsBlockPoly` and companions) and uniformly
bounded (`norm_ghsBlockPoly_le` and companions), and the window obeys
`w ξ ≤ C/(1+ξ²)` by hypothesis — so every product of them is dominated
by a constant multiple of `(1+ξ²)⁻¹`, whose integral is `π`.

Stated as one lemma with three conclusions because the side conditions
always arrive together, and separating them would mean re-deriving the
same domination three times. -/
theorem integrable_of_le_const_div_one_add_sq (g : ℝ → ℝ) (hg : Continuous g)
    (hg0 : ∀ ξ, 0 ≤ g ξ) (K : ℝ) (hK : ∀ ξ, g ξ ≤ K/(1+ξ^2)) :
    Integrable g
      ∧ (∀ a b : ℝ, IntervalIntegrable g volume a b)
      ∧ (∀ s : Set ℝ, IntegrableOn g s) := by
  have hdom : ∀ ξ : ℝ, ‖g ξ‖ ≤ K * (1+ξ^2)⁻¹ := by
    intro ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 ξ)]
    have hpos : (0:ℝ) < 1 + ξ^2 := by positivity
    rw [← div_eq_mul_inv]
    exact hK ξ
  have hint : Integrable g := by
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul K)
      hg.aestronglyMeasurable ?_
    filter_upwards with ξ using hdom ξ
  exact ⟨hint, fun a b => hint.intervalIntegrable,
    fun s => hint.integrableOn⟩

open MeasureTheory Real Complex Finset in
/-- **`E₁`'s side conditions, discharged** (Track R, N77): for a
continuous window with `0 ≤ w ≤ C/(1+ξ²)`, every integrability
hypothesis of `ghsBlock_weighted_energy_le` holds.

`P₂` is continuous (`continuous_ghsBlockPoly`) and uniformly bounded by
`S := ∑_p log p/(p·|log(x/p)|)` (`norm_ghsBlockPoly_le`), so
`‖P₂‖²·w ≤ S²·C/(1+ξ²)` and `integrable_of_le_const_div_one_add_sq`
applies to it and to `w` alike.  The one condition that is not of that
shape — `‖P₂‖²` alone on a bounded interval — is continuous, hence
interval-integrable outright.

With this, `ghsBlock_weighted_energy_le` needs nothing of the caller but
the window's shape: `E₁` is discharged for any admissible `w`. -/
theorem ghsBlock_energy_integrability (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x : ℕ) (P : Finset ℕ) (w : ℝ → ℝ) (hw : Continuous w) (C : ℝ)
    (hw0 : ∀ ξ, 0 ≤ w ξ) (hwle : ∀ ξ, w ξ ≤ C/(1+ξ^2)) :
    Integrable (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ)
      ∧ (∀ a b : ℝ, IntervalIntegrable
          (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ) volume a b)
      ∧ (∀ a b : ℝ, IntervalIntegrable
          (fun ξ => ‖ghsBlockPoly f x P ξ‖^2) volume a b)
      ∧ (∀ s : Set ℝ, IntegrableOn
          (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ) s)
      ∧ (∀ s : Set ℝ, IntegrableOn w s) := by
  classical
  set S : ℝ := ∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|)
    with hS_def
  have hS0 : (0:ℝ) ≤ S := by
    refine Finset.sum_nonneg fun p _ => ?_
    have := Real.log_natCast_nonneg p
    positivity
  have hcont : Continuous (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ) :=
    (((continuous_ghsBlockPoly f x P).norm).pow 2).mul hw
  have hcont2 : Continuous (fun ξ => ‖ghsBlockPoly f x P ξ‖^2) :=
    ((continuous_ghsBlockPoly f x P).norm).pow 2
  -- the product is dominated by `S²C/(1+ξ²)`
  have hdom : ∀ ξ, ‖ghsBlockPoly f x P ξ‖^2 * w ξ ≤ (S^2*C)/(1+ξ^2) := by
    intro ξ
    have hb : ‖ghsBlockPoly f x P ξ‖ ≤ S := norm_ghsBlockPoly_le f hf x P ξ
    have hsq : ‖ghsBlockPoly f x P ξ‖^2 ≤ S^2 := by
      nlinarith [norm_nonneg (ghsBlockPoly f x P ξ), hb, hS0]
    have h1 : ‖ghsBlockPoly f x P ξ‖^2 * w ξ ≤ S^2 * w ξ :=
      mul_le_mul_of_nonneg_right hsq (hw0 ξ)
    have h2 : S^2 * w ξ ≤ S^2 * (C/(1+ξ^2)) :=
      mul_le_mul_of_nonneg_left (hwle ξ) (sq_nonneg S)
    have h3 : S^2 * (C/(1+ξ^2)) = (S^2*C)/(1+ξ^2) := by ring
    linarith [h1, h2, h3.le, h3.ge]
  have hprod0 : ∀ ξ, (0:ℝ) ≤ ‖ghsBlockPoly f x P ξ‖^2 * w ξ :=
    fun ξ => mul_nonneg (by positivity) (hw0 ξ)
  obtain ⟨hint, hitv, hon⟩ :=
    integrable_of_le_const_div_one_add_sq _ hcont hprod0 (S^2*C) hdom
  obtain ⟨-, -, honw⟩ :=
    integrable_of_le_const_div_one_add_sq w hw hw0 C hwle
  exact ⟨hint, hitv, fun a b => hcont2.intervalIntegrable a b, hon, honw⟩

open MeasureTheory Real Complex Finset in
/-- **§4's side conditions, discharged** (Track R, N78): for a
continuous window with `0 ≤ w ≤ C/(1+ξ²)`, every integrability
hypothesis of `pairing_halasz_sqrt_le` holds at the three GHS
polynomials.

Seven conclusions cover all eight hypotheses (`hj` and `htile` differ
only in which interval they name, so one `∀ a b` serves both), and they
split into two kinds:

* `hg0`, `hg1`, `hg2` are whole-line integrals, so they need the
  domination: each polynomial is bounded by its trivial sup
  (`norm_ghsMainPoly_le` and companions), so every product is at most a
  constant times `C/(1+ξ²)` and
  `integrable_of_le_const_div_one_add_sq` applies.
* `hj`, `htile`, `hk1`, `hk2`, `hk3` are *interval* integrals, and the
  integrands are continuous — so they need no domination at all, only
  `Continuous.intervalIntegrable`.  The `1/(1+t²)` that `hk1` and `hk2`
  carry is harmless: its denominator never vanishes.

Recognising the second group for what it is, is what keeps this one
lemma rather than a stack of them.  Only `htail` — an *estimate*, not
an integrability fact — is left to the caller. -/
theorem ghs_pairing_integrability (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x : ℕ) (S P Q : Finset ℕ) (w : ℝ → ℝ) (hw : Continuous w) (C : ℝ)
    (hw0 : ∀ ξ, 0 ≤ w ξ) (hwle : ∀ ξ, w ξ ≤ C/(1+ξ^2)) :
    Integrable (fun ξ => ‖ghsMainPoly f S ξ * ghsBlockPoly f x P ξ
          * ghsPrimePoly f Q ξ‖ * w ξ)
      ∧ Integrable (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ)
      ∧ Integrable (fun ξ => ‖ghsPrimePoly f Q ξ‖^2 * w ξ
          * ‖ghsMainPoly f S ξ‖^2)
      ∧ (∀ a b : ℝ, IntervalIntegrable
          (fun t => ‖ghsPrimePoly f Q t‖^2 * w t * ‖ghsMainPoly f S t‖^2)
          volume a b)
      ∧ (∀ a b : ℝ, IntervalIntegrable
          (fun t => (‖ghsPrimePoly f Q t‖^2/(1+t^2)) * ‖ghsMainPoly f S t‖^2)
          volume a b)
      ∧ (∀ a b : ℝ, IntervalIntegrable
          (fun t => ‖ghsPrimePoly f Q t‖^2/(1+t^2)) volume a b)
      ∧ (∀ a b : ℝ, IntervalIntegrable
          (fun t => ‖ghsPrimePoly f Q t‖^2) volume a b) := by
  classical
  -- the three trivial sups
  set S₁ : ℝ := ∑ n ∈ S, (1:ℝ)/(n:ℝ) with hS₁_def
  set S₂ : ℝ := ∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|)
    with hS₂_def
  set S₃ : ℝ := ∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ) with hS₃_def
  have hb₁ : ∀ ξ, ‖ghsMainPoly f S ξ‖ ≤ S₁ := norm_ghsMainPoly_le f hf S
  have hb₂ : ∀ ξ, ‖ghsBlockPoly f x P ξ‖ ≤ S₂ := norm_ghsBlockPoly_le f hf x P
  have hb₃ : ∀ ξ, ‖ghsPrimePoly f Q ξ‖ ≤ S₃ := norm_ghsPrimePoly_le f hf Q
  have hS₁0 : (0:ℝ) ≤ S₁ := le_trans (norm_nonneg _) (hb₁ 0)
  have hS₂0 : (0:ℝ) ≤ S₂ := le_trans (norm_nonneg _) (hb₂ 0)
  have hS₃0 : (0:ℝ) ≤ S₃ := le_trans (norm_nonneg _) (hb₃ 0)
  -- continuity of the three polynomials
  have hc₁ : Continuous (fun ξ => ‖ghsMainPoly f S ξ‖) :=
    (continuous_ghsMainPoly f S).norm
  have hc₂ : Continuous (fun ξ => ‖ghsBlockPoly f x P ξ‖) :=
    (continuous_ghsBlockPoly f x P).norm
  have hc₃ : Continuous (fun ξ => ‖ghsPrimePoly f Q ξ‖) :=
    (continuous_ghsPrimePoly f Q).norm
  have hden : Continuous (fun t : ℝ => 1 + t^2) := by continuity
  have hden0 : ∀ t : ℝ, (1:ℝ) + t^2 ≠ 0 := fun t => by positivity
  -- `hg0`
  have hg0 : Integrable (fun ξ => ‖ghsMainPoly f S ξ * ghsBlockPoly f x P ξ
      * ghsPrimePoly f Q ξ‖ * w ξ) := by
    have hcont : Continuous (fun ξ => ‖ghsMainPoly f S ξ
        * ghsBlockPoly f x P ξ * ghsPrimePoly f Q ξ‖ * w ξ) :=
      (((continuous_ghsMainPoly f S).mul (continuous_ghsBlockPoly f x P)).mul
        (continuous_ghsPrimePoly f Q)).norm.mul hw
    have hnn : ∀ ξ, (0:ℝ) ≤ ‖ghsMainPoly f S ξ * ghsBlockPoly f x P ξ
        * ghsPrimePoly f Q ξ‖ * w ξ :=
      fun ξ => mul_nonneg (norm_nonneg _) (hw0 ξ)
    have hdom : ∀ ξ, ‖ghsMainPoly f S ξ * ghsBlockPoly f x P ξ
        * ghsPrimePoly f Q ξ‖ * w ξ ≤ (S₁*S₂*S₃*C)/(1+ξ^2) := by
      intro ξ
      rw [norm_mul, norm_mul]
      have hprod : ‖ghsMainPoly f S ξ‖ * ‖ghsBlockPoly f x P ξ‖
          * ‖ghsPrimePoly f Q ξ‖ ≤ S₁ * S₂ * S₃ := by
        gcongr <;> [exact hb₁ ξ; exact hb₂ ξ; exact hb₃ ξ]
      have h1 : ‖ghsMainPoly f S ξ‖ * ‖ghsBlockPoly f x P ξ‖
          * ‖ghsPrimePoly f Q ξ‖ * w ξ ≤ (S₁*S₂*S₃) * w ξ :=
        mul_le_mul_of_nonneg_right hprod (hw0 ξ)
      have h2 : (S₁*S₂*S₃) * w ξ ≤ (S₁*S₂*S₃) * (C/(1+ξ^2)) :=
        mul_le_mul_of_nonneg_left (hwle ξ) (by positivity)
      have h3 : (S₁*S₂*S₃) * (C/(1+ξ^2)) = (S₁*S₂*S₃*C)/(1+ξ^2) := by ring
      linarith [h1, h2, h3.le, h3.ge]
    exact (integrable_of_le_const_div_one_add_sq _ hcont hnn _ hdom).1
  -- `hg1`
  have hg1 : Integrable (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ) := by
    have hcont : Continuous (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ) :=
      (hc₂.pow 2).mul hw
    have hnn : ∀ ξ, (0:ℝ) ≤ ‖ghsBlockPoly f x P ξ‖^2 * w ξ :=
      fun ξ => mul_nonneg (by positivity) (hw0 ξ)
    have hdom : ∀ ξ, ‖ghsBlockPoly f x P ξ‖^2 * w ξ ≤ (S₂^2*C)/(1+ξ^2) := by
      intro ξ
      have hsq : ‖ghsBlockPoly f x P ξ‖^2 ≤ S₂^2 := by
        nlinarith [norm_nonneg (ghsBlockPoly f x P ξ), hb₂ ξ, hS₂0]
      have h1 : ‖ghsBlockPoly f x P ξ‖^2 * w ξ ≤ S₂^2 * w ξ :=
        mul_le_mul_of_nonneg_right hsq (hw0 ξ)
      have h2 : S₂^2 * w ξ ≤ S₂^2 * (C/(1+ξ^2)) :=
        mul_le_mul_of_nonneg_left (hwle ξ) (sq_nonneg S₂)
      have h3 : S₂^2 * (C/(1+ξ^2)) = (S₂^2*C)/(1+ξ^2) := by ring
      linarith [h1, h2, h3.le, h3.ge]
    exact (integrable_of_le_const_div_one_add_sq _ hcont hnn _ hdom).1
  -- `hg2`
  have hg2 : Integrable (fun ξ => ‖ghsPrimePoly f Q ξ‖^2 * w ξ
      * ‖ghsMainPoly f S ξ‖^2) := by
    have hcont : Continuous (fun ξ => ‖ghsPrimePoly f Q ξ‖^2 * w ξ
        * ‖ghsMainPoly f S ξ‖^2) := ((hc₃.pow 2).mul hw).mul (hc₁.pow 2)
    have hnn : ∀ ξ, (0:ℝ) ≤ ‖ghsPrimePoly f Q ξ‖^2 * w ξ
        * ‖ghsMainPoly f S ξ‖^2 :=
      fun ξ => mul_nonneg (mul_nonneg (by positivity) (hw0 ξ)) (by positivity)
    have hdom : ∀ ξ, ‖ghsPrimePoly f Q ξ‖^2 * w ξ * ‖ghsMainPoly f S ξ‖^2
        ≤ (S₃^2*S₁^2*C)/(1+ξ^2) := by
      intro ξ
      have hsq₃ : ‖ghsPrimePoly f Q ξ‖^2 ≤ S₃^2 := by
        nlinarith [norm_nonneg (ghsPrimePoly f Q ξ), hb₃ ξ, hS₃0]
      have hsq₁ : ‖ghsMainPoly f S ξ‖^2 ≤ S₁^2 := by
        nlinarith [norm_nonneg (ghsMainPoly f S ξ), hb₁ ξ, hS₁0]
      have hw' : w ξ ≤ C/(1+ξ^2) := hwle ξ
      have hn₁ : (0:ℝ) ≤ ‖ghsMainPoly f S ξ‖^2 := by positivity
      have hCq : (0:ℝ) ≤ C/(1+ξ^2) := le_trans (hw0 ξ) hw'
      -- peel the factors one at a time; `nlinarith` will not do a triple
      have hstep : ‖ghsPrimePoly f Q ξ‖^2 * w ξ ≤ S₃^2 * (C/(1+ξ^2)) :=
        le_trans (mul_le_mul_of_nonneg_right hsq₃ (hw0 ξ))
          (mul_le_mul_of_nonneg_left hw' (sq_nonneg S₃))
      have h1 : ‖ghsPrimePoly f Q ξ‖^2 * w ξ * ‖ghsMainPoly f S ξ‖^2
          ≤ S₃^2 * (C/(1+ξ^2)) * S₁^2 :=
        le_trans (mul_le_mul_of_nonneg_right hstep hn₁)
          (mul_le_mul_of_nonneg_left hsq₁ (by positivity))
      have h3 : S₃^2 * (C/(1+ξ^2)) * S₁^2 = (S₃^2*S₁^2*C)/(1+ξ^2) := by ring
      linarith [h1, h3.le, h3.ge]
    exact (integrable_of_le_const_div_one_add_sq _ hcont hnn _ hdom).1
  -- the interval conditions: continuity is enough
  refine ⟨hg0, hg1, hg2, fun a b => ?_, fun a b => ?_, fun a b => ?_,
    fun a b => ?_⟩
  · exact (((hc₃.pow 2).mul hw).mul (hc₁.pow 2)).intervalIntegrable a b
  · exact (((hc₃.pow 2).div hden hden0).mul (hc₁.pow 2)).intervalIntegrable a b
  · exact ((hc₃.pow 2).div hden hden0).intervalIntegrable a b
  · exact (hc₃.pow 2).intervalIntegrable a b

open MeasureTheory Real Complex Finset in
/-- **§4's `Mtail`** (Track R, N79): on any set, the pairing tail is the
window's mass there, priced at the two trivial sups —

  `∫_{ξ ∈ s} ‖P₃‖²·w·‖P₁‖² ≤ (∑_q log q/q)²·(∑_n 1/n)²·Wtail`

whenever `∫_{ξ ∈ s} w ≤ Wtail`.

This is the last hypothesis of `pairing_halasz_sqrt_le` that is not an
integrability fact, and it is deliberately left parametric in `Wtail`,
exactly as `ghsBlock_weighted_energy_le` leaves it: beyond the band no
cancellation is available, so the polynomials are discarded against
their sups and the window's tail mass pays for everything.  What that
mass actually is depends on the window §4 chooses, and that choice is
not made here.

The two sups are the crude `L∞` bounds `norm_ghsPrimePoly_le` and
`norm_ghsMainPoly_le` — `≍ log X` and `≍ log x` — which is why the
window must be chosen with enough decay for `Mtail` to stay below
`C·V·L(x)²`.  Recording that as a parameter rather than a number keeps
the dependence visible. -/
theorem ghs_pairing_tail_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x : ℕ) (S P Q : Finset ℕ) (w : ℝ → ℝ) (hw : Continuous w) (C : ℝ)
    (hw0 : ∀ ξ, 0 ≤ w ξ) (hwle : ∀ ξ, w ξ ≤ C/(1+ξ^2))
    (s : Set ℝ) (Wtail : ℝ) (hWtail : (∫ ξ in s, w ξ) ≤ Wtail) :
    (∫ ξ in s, ‖ghsPrimePoly f Q ξ‖^2 * w ξ * ‖ghsMainPoly f S ξ‖^2)
      ≤ (∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ))^2
          * (∑ n ∈ S, (1:ℝ)/(n:ℝ))^2 * Wtail := by
  classical
  set S₁ : ℝ := ∑ n ∈ S, (1:ℝ)/(n:ℝ) with hS₁_def
  set S₃ : ℝ := ∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ) with hS₃_def
  have hb₁ : ∀ ξ, ‖ghsMainPoly f S ξ‖ ≤ S₁ := norm_ghsMainPoly_le f hf S
  have hb₃ : ∀ ξ, ‖ghsPrimePoly f Q ξ‖ ≤ S₃ := norm_ghsPrimePoly_le f hf Q
  have hS₁0 : (0:ℝ) ≤ S₁ := le_trans (norm_nonneg _) (hb₁ 0)
  have hS₃0 : (0:ℝ) ≤ S₃ := le_trans (norm_nonneg _) (hb₃ 0)
  obtain ⟨-, -, hg2, -, -, -, -⟩ :=
    ghs_pairing_integrability f hf x S P Q w hw C hw0 hwle
  obtain ⟨-, -, honw⟩ :=
    integrable_of_le_const_div_one_add_sq w hw hw0 C hwle
  -- discard both polynomials against their sups
  have hpt : ∀ ξ, ‖ghsPrimePoly f Q ξ‖^2 * w ξ * ‖ghsMainPoly f S ξ‖^2
      ≤ (S₃^2 * S₁^2) * w ξ := by
    intro ξ
    have hsq₃ : ‖ghsPrimePoly f Q ξ‖^2 ≤ S₃^2 := by
      nlinarith [norm_nonneg (ghsPrimePoly f Q ξ), hb₃ ξ, hS₃0]
    have hsq₁ : ‖ghsMainPoly f S ξ‖^2 ≤ S₁^2 := by
      nlinarith [norm_nonneg (ghsMainPoly f S ξ), hb₁ ξ, hS₁0]
    have hn₁ : (0:ℝ) ≤ ‖ghsMainPoly f S ξ‖^2 := by positivity
    -- peel one factor at a time
    have hstep : ‖ghsPrimePoly f Q ξ‖^2 * w ξ ≤ (S₃^2) * w ξ :=
      mul_le_mul_of_nonneg_right hsq₃ (hw0 ξ)
    have h1 : ‖ghsPrimePoly f Q ξ‖^2 * w ξ * ‖ghsMainPoly f S ξ‖^2
        ≤ (S₃^2 * w ξ) * S₁^2 :=
      le_trans (mul_le_mul_of_nonneg_right hstep hn₁)
        (mul_le_mul_of_nonneg_left hsq₁ (mul_nonneg (sq_nonneg S₃) (hw0 ξ)))
    have h2 : (S₃^2 * w ξ) * S₁^2 = (S₃^2 * S₁^2) * w ξ := by ring
    linarith [h1, h2.le, h2.ge]
  have hmono : (∫ ξ in s, ‖ghsPrimePoly f Q ξ‖^2 * w ξ
        * ‖ghsMainPoly f S ξ‖^2)
      ≤ ∫ ξ in s, (S₃^2 * S₁^2) * w ξ :=
    MeasureTheory.setIntegral_mono hg2.integrableOn
      ((honw s).const_mul _) hpt
  refine le_trans hmono ?_
  rw [MeasureTheory.integral_const_mul]
  exact mul_le_mul_of_nonneg_left hWtail (by positivity)

open MeasureTheory Real Complex Finset in
/-- **§4's pairing estimate, assembled** (Track R, N81): for the three
GHS polynomials and any continuous window with `0 ≤ w ≤ C/(1+t²)`,

  `∫_ℝ ‖P₁·P₂·P₃‖·w ≤ √(E₁·(5·C·V·L(x)² + Mtail))`.

`pairing_halasz_sqrt_le` with **every side condition discharged**.  Of
its twenty hypotheses only the four estimates survive — `hE₁`, `hB`,
`hV`, and the window's tail mass — because the eight integrability
conditions come from `ghs_pairing_integrability` and `htail` from
`ghs_pairing_tail_le`.  That is what makes this the form §4 can
actually consume.

`Mtail` is supplied through the window's tail mass `Wtail`, priced at
the two trivial sups, and it is **not** derived from `hwle`: the crude
`∫_ℝ C/(1+ξ²) = πC` — and even the second-order window bound
`M₂/(2π²L)` — are too weak by a factor of `log x` once `E₁ ≍ C·e^{k}/log x`
and `Mtail ≍ (e^{−k}log x)²(log x)²·Wtail` are put together.  The
third-order bound `fourier_tail_cube_le` is what clears it.  Keeping
`Wtail` a parameter is what lets the caller make that choice explicitly.

`0 ≤ C` is not a hypothesis: it follows from `0 ≤ w 0 ≤ C/(1+0²)`. -/
theorem ghs_pairing_estimate (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x : ℕ) (S P Q : Finset ℕ) (w : ℝ → ℝ) (hw : Continuous w)
    (B : ℤ → ℝ) (C V Mtail E₁ Wtail : ℝ)
    (hE₁0 : 0 < E₁) (hQ0 : 0 < 5 * C * V * halaszLSq B x + Mtail)
    (hw0 : ∀ t, 0 ≤ w t) (hwle : ∀ t, w t ≤ C/(1+t^2))
    (hE₁ : (∫ ξ, ‖ghsBlockPoly f x P ξ‖^2 * w ξ) ≤ E₁)
    (hB : ∀ N ∈ halaszRange x, ∀ t ∈ Set.Icc ((N:ℝ) - 1/2) ((N:ℝ) + 1/2),
      ‖ghsMainPoly f S t‖ ≤ B N)
    (hB0 : ∀ N, 0 ≤ B N)
    (hV : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), ‖ghsPrimePoly f Q t‖^2) ≤ V)
    (hWtail : (∫ ξ in {ξ : ℝ | ((halaszM x : ℕ):ℝ) + 1/2 < |ξ|}, w ξ)
      ≤ Wtail)
    (hMtail : (∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ))^2
        * (∑ n ∈ S, (1:ℝ)/(n:ℝ))^2 * Wtail ≤ Mtail) :
    (∫ ξ, ‖ghsMainPoly f S ξ * ghsBlockPoly f x P ξ
        * ghsPrimePoly f Q ξ‖ * w ξ)
      ≤ Real.sqrt (E₁ * (5 * C * V * halaszLSq B x + Mtail)) := by
  classical
  have hC0 : (0:ℝ) ≤ C := by
    have h0 := hwle 0
    have hw00 := hw0 0
    norm_num at h0
    linarith
  obtain ⟨hg0, hg1, hg2, hjt, hk1, hk2, hk3⟩ :=
    ghs_pairing_integrability f hf x S P Q w hw C hw0 hwle
  -- the tail estimate: the window's mass, priced at the two trivial sups
  have htail : (∫ ξ in {ξ : ℝ | ((halaszM x : ℕ):ℝ) + 1/2 < |ξ|},
      ‖ghsPrimePoly f Q ξ‖^2 * w ξ * ‖ghsMainPoly f S ξ‖^2) ≤ Mtail :=
    le_trans (ghs_pairing_tail_le f hf x S P Q w hw C hw0 hwle _ Wtail hWtail)
      hMtail
  exact pairing_halasz_sqrt_le (ghsMainPoly f S) (ghsBlockPoly f x P)
    (ghsPrimePoly f Q) w B x C V Mtail E₁ hE₁0 hC0 hQ0 hw0 hwle hE₁ hB hB0 hV
    hg0 hg1 hg2 htail (fun i _ => hjt _ _) (fun N _ => hjt _ _)
    (fun N _ => hk1 _ _) (fun N _ => hk2 _ _) (fun N _ => hk3 _ _)

open MeasureTheory Real Complex Finset in
/-- **§4's pairing estimate at a uniform band sup** (Track R, N82): if
`‖P₁‖ ≤ b` on the whole line then

  `∫_ℝ ‖P₁·P₂·P₃‖·w ≤ √(E₁·(30·C·V·b² + Mtail))`.

The form §4 actually meets, because `norm_ghsMainPoly_smooth_band_le`
is **uniform in the frequency**: the Halász Euler-product bound does not
vary from one unit interval to the next, so `halaszLSq`'s dominating
function may be taken constant and `halaszLSq_le_of_bound` collapses
`L(x)²` to `6b²`.  The `≍ log⁴x` frequencies in `halaszRange` cost
nothing — that is what makes Halász sharp rather than log-lossy.

`0 < Mtail` is what supplies `pairing_halasz_sqrt_le`'s positivity
side condition: the `5·C·V·L(x)²` term is only known to be non-negative
(`halaszLSq_nonneg`), so strict positivity has to come from the tail,
which is a genuine positive bound in any application. -/
theorem ghs_pairing_estimate_uniform (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x : ℕ) (S P Q : Finset ℕ) (w : ℝ → ℝ) (hw : Continuous w)
    (C V Mtail E₁ Wtail b : ℝ)
    (hE₁0 : 0 < E₁) (hb0 : 0 ≤ b) (hV0 : 0 ≤ V) (hMtail0 : 0 < Mtail)
    (hw0 : ∀ t, 0 ≤ w t) (hwle : ∀ t, w t ≤ C/(1+t^2))
    (hE₁ : (∫ ξ, ‖ghsBlockPoly f x P ξ‖^2 * w ξ) ≤ E₁)
    (hBu : ∀ t : ℝ, ‖ghsMainPoly f S t‖ ≤ b)
    (hV : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), ‖ghsPrimePoly f Q t‖^2) ≤ V)
    (hWtail : (∫ ξ in {ξ : ℝ | ((halaszM x : ℕ):ℝ) + 1/2 < |ξ|}, w ξ)
      ≤ Wtail)
    (hMtail : (∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ))^2
        * (∑ n ∈ S, (1:ℝ)/(n:ℝ))^2 * Wtail ≤ Mtail) :
    (∫ ξ, ‖ghsMainPoly f S ξ * ghsBlockPoly f x P ξ
        * ghsPrimePoly f Q ξ‖ * w ξ)
      ≤ Real.sqrt (E₁ * (5 * C * V * (6*b^2) + Mtail)) := by
  classical
  have hC0 : (0:ℝ) ≤ C := by
    have h0 := hwle 0
    have hw00 := hw0 0
    norm_num at h0
    linarith
  -- the constant dominating function
  have hLSq : halaszLSq (fun _ => b) x ≤ 6*b^2 :=
    halaszLSq_le_of_bound (fun _ => b) x b
      (fun N _ => by rw [abs_of_nonneg hb0])
  have hLSq0 : (0:ℝ) ≤ halaszLSq (fun _ => b) x := halaszLSq_nonneg _ _
  have hcoef : (0:ℝ) ≤ 5 * C * V := by positivity
  have hQ0 : 0 < 5 * C * V * halaszLSq (fun _ => b) x + Mtail := by
    nlinarith [hcoef, hLSq0, hMtail0]
  have hmain := ghs_pairing_estimate f hf x S P Q w hw (fun _ => b)
    C V Mtail E₁ Wtail hE₁0 hQ0 hw0 hwle hE₁
    (fun N _ t _ => hBu t) (fun _ => hb0) hV hWtail hMtail
  refine le_trans hmain ?_
  refine Real.sqrt_le_sqrt ?_
  have hstep : 5 * C * V * halaszLSq (fun _ => b) x ≤ 5 * C * V * (6*b^2) :=
    mul_le_mul_of_nonneg_left hLSq hcoef
  exact mul_le_mul_of_nonneg_left (by linarith) hE₁0.le

open MeasureTheory Real Complex ArithmeticFunction Finset in
open scoped FourierTransform in
/-- **§4's pairing estimate at the Riesz weight** (Track R, N165):

  `∫_ℝ ‖P₁·P₂·P₃‖·‖𝓕V‖ ≤ √(E₁·(5·V₃·6b² + Mtail))`,

with `V = rieszWindow` and

  `Mtail ≥ (∑_q log q/q)²·(∑_{n∈S} 1/n)²·1/(2π²(halaszM x + ½))`.

`ghs_pairing_estimate_uniform` with the weight fixed.  The constant `C`
has left the main term entirely — it was `2M_V + M₂/(2π²)` for a
smoothed window, and the N148 audit showed that quantity is `≳ 1/ρ` for
*every* admissible window, so it could not be held bounded while the
Perron error `≍ ρ·(trivial bound)` was held small.  Here it is `1`.

`Wtail` is `1/(2π²(halaszM x + ½))` from `fourier_rieszWindow_tail_le`,
which at the widened band `halaszM x ≍ log⁴x` is `≍ log^{−4}x` — below
the `≲ e^{k}/log³x` that `E₁·Mtail ≲ (main term)²` demands, with a
factor of `log x` in hand.

Together with `ghsBlock_E1_riesz_le` for `E₁`,
`ghsPrimePoly_unit_energy_final_le` for `V₃` (both uniform in the
frequency, hence unaffected by the band width), and
`norm_ghsMainPoly_smooth_band_le` for `b`, this is §4's half of the
argument at the Riesz window, with no free window parameters left. -/
theorem ghs_riesz_pairing_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x : ℕ) (S P Q : Finset ℕ)
    (V Mtail E₁ b : ℝ)
    (hE₁0 : 0 < E₁) (hb0 : 0 ≤ b) (hV0 : 0 ≤ V) (hMtail0 : 0 < Mtail)
    (hE₁ : (∫ ξ, ‖ghsBlockPoly f x P ξ‖^2
        * ‖𝓕 (fun v => ((ExpSums.rieszWindow v : ℝ) : ℂ)) ξ‖) ≤ E₁)
    (hBu : ∀ t : ℝ, ‖ghsMainPoly f S t‖ ≤ b)
    (hV : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), ‖ghsPrimePoly f Q t‖^2) ≤ V)
    (hMtail : (∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ))^2
        * (∑ n ∈ S, (1:ℝ)/(n:ℝ))^2
        * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2))) ≤ Mtail) :
    (∫ ξ, ‖ghsMainPoly f S ξ * ghsBlockPoly f x P ξ * ghsPrimePoly f Q ξ‖
        * ‖𝓕 (fun v => ((ExpSums.rieszWindow v : ℝ) : ℂ)) ξ‖)
      ≤ Real.sqrt (E₁ * (5 * V * (6*b^2) + Mtail)) := by
  classical
  have hL0 : (0:ℝ) < ((halaszM x : ℕ):ℝ) + 1/2 := by positivity
  have h := ghs_pairing_estimate_uniform f hf x S P Q
    (fun ξ => ‖𝓕 (fun v => ((ExpSums.rieszWindow v : ℝ) : ℂ)) ξ‖)
    ExpSums.continuous_norm_fourier_rieszWindow
    1 V Mtail E₁ (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2))) b
    hE₁0 hb0 hV0 hMtail0
    (fun t => norm_nonneg _)
    ExpSums.norm_fourier_rieszWindow_le
    hE₁ hBu hV
    (ExpSums.fourier_rieszWindow_tail_le _ hL0)
    hMtail
  simpa using h

open MeasureTheory Real Complex Finset in
open scoped FourierTransform ContDiff in
/-- **§4's pairing estimate at a Perron window** (Track R, N83): for any
smooth compactly supported `V`, with `w := ‖𝓕V‖`,

  `∫_ℝ ‖P₁·P₂·P₃‖·‖𝓕V‖
     ≤ √(E₁·(30·(2M_V + M₂/2π²)·V₃·b² + Mtail))`.

`ghs_pairing_estimate_uniform` with the window's own hypotheses
discharged.  Nothing about the window survives except three of its
norms:

* `hwle` is `fourier_window_le_inv_one_add_sq`, which turns the sup
  `M_V` and the second-derivative mass `M₂` into GHS's contour weight
  `C/(1+ξ²)` with `C = 2M_V + M₂/(2π²)` — no contour required;
* `hWtail` is `fourier_tail_cube_le` at `L = halaszM x + 1/2`, giving
  `Wtail = M₃/(8π³(halaszM x + 1/2)²)` — the **third**-derivative mass,
  because the second-order tail is a factor of `log x` short of what
  `Mtail` can afford;
* `hw0` and continuity are free, `w` being the norm of a Schwartz
  function's transform.

So §4 needs no *particular* window: it needs one whose second and third
derivative masses and transform sup are controlled, and the estimate is
uniform over that class.  Choosing the window is therefore a §3
decision, not a §4 one. -/
theorem ghs_pairing_estimate_window (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x : ℕ) (S P Q : Finset ℕ)
    (V : ℝ → ℝ) (hVs : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (M₂ M₃ MV : ℝ)
    (hM₂ : ∫ v, |iteratedDeriv 2 V v| ≤ M₂)
    (hM₃ : ∫ v, |iteratedDeriv 3 V v| ≤ M₃)
    (hMV : ∀ ξ, ‖𝓕 (fun v => ((V v : ℝ) : ℂ)) ξ‖ ≤ MV)
    (V₃ Mtail E₁ b : ℝ)
    (hE₁0 : 0 < E₁) (hb0 : 0 ≤ b) (hV₃0 : 0 ≤ V₃) (hMtail0 : 0 < Mtail)
    (hE₁ : (∫ ξ, ‖ghsBlockPoly f x P ξ‖^2
        * ‖𝓕 (fun v => ((V v : ℝ) : ℂ)) ξ‖) ≤ E₁)
    (hBu : ∀ t : ℝ, ‖ghsMainPoly f S t‖ ≤ b)
    (hV : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), ‖ghsPrimePoly f Q t‖^2) ≤ V₃)
    (hMtail : (∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ))^2
        * (∑ n ∈ S, (1:ℝ)/(n:ℝ))^2
        * (M₃/(8*Real.pi^3*(((halaszM x : ℕ):ℝ) + 1/2)^2)) ≤ Mtail) :
    (∫ ξ, ‖ghsMainPoly f S ξ * ghsBlockPoly f x P ξ
        * ghsPrimePoly f Q ξ‖ * ‖𝓕 (fun v => ((V v : ℝ) : ℂ)) ξ‖)
      ≤ Real.sqrt (E₁ * (5 * (2*MV + M₂/(2*Real.pi^2)) * V₃ * (6*b^2)
          + Mtail)) := by
  classical
  set Vc : ℝ → ℂ := fun v => ((V v : ℝ) : ℂ) with hVc_def
  have hVcs : ContDiff ℝ ∞ Vc := Complex.ofRealCLM.contDiff.comp hVs
  have hVcc : HasCompactSupport Vc :=
    HasCompactSupport.comp_left hVc Complex.ofReal_zero
  set G : SchwartzMap ℝ ℂ := hVcc.toSchwartzMap hVcs with hG_def
  -- the window is continuous and non-negative
  have hw : Continuous (fun ξ => ‖𝓕 Vc ξ‖) := ((𝓕 G).continuous).norm
  have hw0 : ∀ t : ℝ, 0 ≤ ‖𝓕 Vc t‖ := fun t => norm_nonneg _
  -- GHS's contour weight, from the sup and the second-derivative mass
  have hwle : ∀ t : ℝ, ‖𝓕 Vc t‖ ≤ (2*MV + M₂/(2*Real.pi^2))/(1+t^2) :=
    fun t => ExpSums.fourier_window_le_inv_one_add_sq V hVs hVc M₂ MV
      hM₂ hMV t
  -- the tail, at third order
  have hL0 : (0:ℝ) < ((halaszM x : ℕ):ℝ) + 1/2 := by positivity
  have hWtail : (∫ ξ in {ξ : ℝ | ((halaszM x : ℕ):ℝ) + 1/2 < |ξ|},
      ‖𝓕 Vc ξ‖)
      ≤ M₃/(8*Real.pi^3*(((halaszM x : ℕ):ℝ) + 1/2)^2) :=
    ExpSums.fourier_tail_cube_le V hVs hVc M₃ hM₃ _ hL0
  exact ghs_pairing_estimate_uniform f hf x S P Q (fun ξ => ‖𝓕 Vc ξ‖) hw
    (2*MV + M₂/(2*Real.pi^2)) V₃ Mtail E₁
    (M₃/(8*Real.pi^3*(((halaszM x : ℕ):ℝ) + 1/2)^2)) b
    hE₁0 hb0 hV₃0 hMtail0 hw0 hwle hE₁ hBu hV hWtail hMtail

open MeasureTheory Real Complex Finset in
/-- **The three §4 polynomials multiply into one** (Track R, N85):

  `P₁(ξ)·P₂(ξ)·P₃(ξ)
     = ∑_{(n,p,q)} (f(n)/n)·(log p·f(p)/(p·log(x/p)))·(log q·f(q)/q)
                    ·𝐞(−log(npq)·ξ)`.

`char_poly_mul_log` applied twice, then `char_poly_mul` to append the
third factor (its intermediate index set is a product, not `ℕ`, so the
`log`-specialised form no longer applies and the general one is used).

**This is what makes §4 a bound on §3's object.**  The coefficient
attached to `npq` is exactly `tripleConv`'s summand divided by `npq` —
the `1/npq` being the Dirichlet normalisation that the three
polynomials carry on the `1`-line, and that the Perron step restores.
So the triple product is the phase polynomial of the smoothed triple
convolution, and `norm_sum_translates_le_integral_char` bounds that
convolution by an integral of exactly the shape
`ghs_pairing_estimate_window` estimates. -/
theorem ghs_triple_product (f : ℕ → ℂ) (x : ℕ) (S P Q : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) (hP : ∀ p ∈ P, 0 < p) (hQ : ∀ q ∈ Q, 0 < q)
    (ξ : ℝ) :
    ghsMainPoly f S ξ * ghsBlockPoly f x P ξ * ghsPrimePoly f Q ξ
      = ∑ r ∈ (S ×ˢ P) ×ˢ Q,
          ((f r.1.1 / (r.1.1:ℂ))
            * (((Real.log (r.1.2:ℝ) : ℂ) * f r.1.2)
                / ((r.1.2:ℂ) * ((Real.log ((x:ℝ)/(r.1.2:ℝ)) : ℝ):ℂ)))
            * (((Real.log (r.2:ℝ) : ℂ) * f r.2) / (r.2:ℂ)))
          * ((Real.fourierChar
              (-(Real.log ((r.1.1 * r.1.2 * r.2 : ℕ):ℝ) * ξ)) : Circle) : ℂ) := by
  classical
  rw [ghsMainPoly, ghsBlockPoly, ghsPrimePoly]
  -- first two factors: the `log`-specialised product
  rw [ExpSums.char_poly_mul_log S P (fun n => f n / (n:ℂ))
    (fun p => ((Real.log (p:ℝ) : ℂ) * f p)
      / ((p:ℂ) * ((Real.log ((x:ℝ)/(p:ℝ)) : ℝ):ℂ))) hS hP ξ]
  -- third factor: the general product, the index set now being a pair
  rw [ExpSums.char_poly_mul (S ×ˢ P) Q
    (fun r => (f r.1 / (r.1:ℂ))
      * (((Real.log (r.2:ℝ) : ℂ) * f r.2)
        / ((r.2:ℂ) * ((Real.log ((x:ℝ)/(r.2:ℝ)) : ℝ):ℂ))))
    (fun q => ((Real.log (q:ℝ) : ℂ) * f q) / (q:ℂ))
    (fun r => Real.log ((r.1 * r.2 : ℕ):ℝ))
    (fun q => Real.log (q:ℝ)) ξ]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_product] at hr
  obtain ⟨hr1, hr2⟩ := hr
  rw [Finset.mem_product] at hr1
  have hn : (0:ℝ) < (r.1.1:ℝ) := by exact_mod_cast hS r.1.1 hr1.1
  have hp : (0:ℝ) < (r.1.2:ℝ) := by exact_mod_cast hP r.1.2 hr1.2
  have hq : (0:ℝ) < (r.2:ℝ) := by exact_mod_cast hQ r.2 hr2
  have hlog : Real.log ((r.1.1 * r.1.2 * r.2 : ℕ):ℝ)
      = Real.log ((r.1.1 * r.1.2 : ℕ):ℝ) + Real.log (r.2:ℝ) := by
    push_cast
    rw [Real.log_mul (by positivity) (ne_of_gt hq)]
  rw [hlog]

open MeasureTheory Real Complex Finset in
open scoped FourierTransform ContDiff in
/-- **The smoothed triple convolution, bounded by §4** (Track R, N86):

  `‖∑_{(n,p,q)} (f(n)/n)(log p·f(p)/(p log(x/p)))(log q·f(q)/q)·V(y − log(npq))‖
     ≤ √(E₁·(30·(2M_V + M₂/2π²)·V₃·b² + Mtail))`.

§3 meets §4 here.  Three facts compose and nothing new is proved:

* `norm_sum_translates_le_integral_char` (the Perron-by-smoothing
  bound) turns the smoothed sum into the `L¹` pairing of its phase
  polynomial with `𝓕V`;
* `ghs_triple_product` identifies that polynomial as `P₁·P₂·P₃` — the
  step that needs the coefficients to be the Dirichlet convolution of
  the three, which they are;
* `ghs_pairing_estimate_window` estimates the pairing.

What remains between this and §3's `S_k` is the *truncated Perron*
step: this sum is smoothed and carries the Dirichlet weight `1/npq`,
whereas `tripleConv` has a sharp cutoff and no weight.  That
conversion is `perron_sandwich`, and it is not done here. -/
theorem ghs_smoothed_triple_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x : ℕ) (S P Q : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) (hP : ∀ p ∈ P, 0 < p) (hQ : ∀ q ∈ Q, 0 < q)
    (V : ℝ → ℝ) (hVs : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (M₂ M₃ MV : ℝ)
    (hM₂ : ∫ v, |iteratedDeriv 2 V v| ≤ M₂)
    (hM₃ : ∫ v, |iteratedDeriv 3 V v| ≤ M₃)
    (hMV : ∀ ξ, ‖𝓕 (fun v => ((V v : ℝ) : ℂ)) ξ‖ ≤ MV)
    (V₃ Mtail E₁ b : ℝ)
    (hE₁0 : 0 < E₁) (hb0 : 0 ≤ b) (hV₃0 : 0 ≤ V₃) (hMtail0 : 0 < Mtail)
    (hE₁ : (∫ ξ, ‖ghsBlockPoly f x P ξ‖^2
        * ‖𝓕 (fun v => ((V v : ℝ) : ℂ)) ξ‖) ≤ E₁)
    (hBu : ∀ t : ℝ, ‖ghsMainPoly f S t‖ ≤ b)
    (hV : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), ‖ghsPrimePoly f Q t‖^2) ≤ V₃)
    (hMtail : (∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ))^2
        * (∑ n ∈ S, (1:ℝ)/(n:ℝ))^2
        * (M₃/(8*Real.pi^3*(((halaszM x : ℕ):ℝ) + 1/2)^2)) ≤ Mtail)
    (y : ℝ) :
    ‖∑ r ∈ (S ×ˢ P) ×ˢ Q,
        ((f r.1.1 / (r.1.1:ℂ))
          * (((Real.log (r.1.2:ℝ) : ℂ) * f r.1.2)
              / ((r.1.2:ℂ) * ((Real.log ((x:ℝ)/(r.1.2:ℝ)) : ℝ):ℂ)))
          * (((Real.log (r.2:ℝ) : ℂ) * f r.2) / (r.2:ℂ)))
        * ((fun v => ((V v : ℝ) : ℂ))
            (y - Real.log ((r.1.1 * r.1.2 * r.2 : ℕ):ℝ)))‖
      ≤ Real.sqrt (E₁ * (5 * (2*MV + M₂/(2*Real.pi^2)) * V₃ * (6*b^2)
          + Mtail)) := by
  classical
  set Vc : ℝ → ℂ := fun v => ((V v : ℝ) : ℂ) with hVc_def
  have hVcs : ContDiff ℝ ∞ Vc := Complex.ofRealCLM.contDiff.comp hVs
  have hVcc : HasCompactSupport Vc :=
    HasCompactSupport.comp_left hVc Complex.ofReal_zero
  -- Perron by smoothing: the sum is the L¹ pairing of its polynomial
  refine le_trans (ExpSums.norm_sum_translates_le_integral_char Vc hVcc hVcs
    ((S ×ˢ P) ×ˢ Q)
    (fun r => (f r.1.1 / (r.1.1:ℂ))
      * (((Real.log (r.1.2:ℝ) : ℂ) * f r.1.2)
          / ((r.1.2:ℂ) * ((Real.log ((x:ℝ)/(r.1.2:ℝ)) : ℝ):ℂ)))
      * (((Real.log (r.2:ℝ) : ℂ) * f r.2) / (r.2:ℂ)))
    (fun r => Real.log ((r.1.1 * r.1.2 * r.2 : ℕ):ℝ)) y) ?_
  -- that polynomial is the triple product
  have hcongr : (∫ ξ, ‖∑ r ∈ (S ×ˢ P) ×ˢ Q,
        ((f r.1.1 / (r.1.1:ℂ))
          * (((Real.log (r.1.2:ℝ) : ℂ) * f r.1.2)
              / ((r.1.2:ℂ) * ((Real.log ((x:ℝ)/(r.1.2:ℝ)) : ℝ):ℂ)))
          * (((Real.log (r.2:ℝ) : ℂ) * f r.2) / (r.2:ℂ)))
        * ((Real.fourierChar
            (-(Real.log ((r.1.1 * r.1.2 * r.2 : ℕ):ℝ) * ξ)) : Circle) : ℂ)‖
        * ‖𝓕 Vc ξ‖)
      = ∫ ξ, ‖ghsMainPoly f S ξ * ghsBlockPoly f x P ξ
          * ghsPrimePoly f Q ξ‖ * ‖𝓕 Vc ξ‖ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    dsimp only
    rw [← ghs_triple_product f x S P Q hS hP hQ ξ]
  rw [hcongr]
  exact ghs_pairing_estimate_window f hf x S P Q V hVs hVc M₂ M₃ MV
    hM₂ hM₃ hMV V₃ Mtail E₁ b hE₁0 hb0 hV₃0 hMtail0 hE₁ hBu hV hMtail

open Real Finset in
/-- **The Perron error over the inner prime range** (Track R, N90): for
`1`-bounded `g` and any `ρ ≥ 0`,

  `∑_{q < y} |log q·g(q)|·(2ρ⌊y/q⌋ + 6) ≤ 2ρ·y·(log y + 2) + 6·y·log 4`.

The error `perron_sandwich_uniform_real` leaves behind, summed over
`tripleConv`'s inner prime range.  Both halves are already on main and
neither needs new analysis: the `2ρ` half is `2ρy·∑_q log q/q`, bounded
by Mertens' sharp form (`sum_log_div_primesBelow_le_sharp`), and the
constant half is `6·∑_q log q`, bounded by Chebyshev's θ-bound
(`sum_log_primesBelow_le`).

The floor matters and is handled rather than ignored: the sandwich is
applied at the *integer* scale `⌊x/(pq)⌋`, not at `x/(pq)`, so the
bound goes through `Nat.cast_div_le` before Mertens is reached.

Against `tripleConv`'s outer weight this contributes `O(ρ·x·log x)`
from the first half and `O(x)` from the second — the second is what
(3.2) already allows, and the first is what the choice of `ρ` has to
control. -/
theorem perron_error_inner_le (g : ℕ → ℝ) (hg : ∀ n, |g n| ≤ 1) (y : ℕ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∑ q ∈ y.primesBelow,
        |Real.log (q:ℝ) * g q| * (2*ρ*(((y/q : ℕ)):ℝ) + 6)
      ≤ 2*ρ*(y:ℝ)*(Real.log (y:ℝ) + 2) + 6*(y:ℝ)*Real.log 4 := by
  classical
  have hy0 : (0:ℝ) ≤ (y:ℝ) := Nat.cast_nonneg _
  -- termwise: drop `g`, and the floor against the true quotient
  have hterm : ∀ q ∈ y.primesBelow,
      |Real.log (q:ℝ) * g q| * (2*ρ*(((y/q : ℕ)):ℝ) + 6)
        ≤ 2*ρ*(y:ℝ) * (Real.log (q:ℝ)/(q:ℝ)) + 6*Real.log (q:ℝ) := by
    intro q hq
    have hqp : q.Prime := (Nat.mem_primesBelow.mp hq).2
    have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hqp.pos
    have hlog0 : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_natCast_nonneg q
    have habs : |Real.log (q:ℝ) * g q| ≤ Real.log (q:ℝ) := by
      rw [abs_mul, abs_of_nonneg hlog0]
      nlinarith [hg q, abs_nonneg (g q), hlog0]
    have hfloor : (((y/q : ℕ)):ℝ) ≤ (y:ℝ)/(q:ℝ) := Nat.cast_div_le
    have hbig : (0:ℝ) ≤ 2*ρ*(((y/q : ℕ)):ℝ) + 6 := by positivity
    have hstep : |Real.log (q:ℝ) * g q| * (2*ρ*(((y/q : ℕ)):ℝ) + 6)
        ≤ Real.log (q:ℝ) * (2*ρ*((y:ℝ)/(q:ℝ)) + 6) := by
      refine le_trans (mul_le_mul_of_nonneg_right habs hbig) ?_
      refine mul_le_mul_of_nonneg_left ?_ hlog0
      have : 2*ρ*(((y/q : ℕ)):ℝ) ≤ 2*ρ*((y:ℝ)/(q:ℝ)) :=
        mul_le_mul_of_nonneg_left hfloor (by positivity)
      linarith
    refine le_trans hstep (le_of_eq ?_)
    field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- Chebyshev's θ-bound
  have hcheb : ∑ q ∈ y.primesBelow, Real.log (q:ℝ) ≤ (y:ℝ) * Real.log 4 :=
    sum_log_primesBelow_le y
  -- Mertens, sharp form (vacuous below `2`)
  have hmert : ∑ q ∈ y.primesBelow, Real.log (q:ℝ)/(q:ℝ)
      ≤ Real.log (y:ℝ) + 2 := by
    rcases lt_or_ge y 2 with hy | hy
    · have hempty : y.primesBelow = ∅ := by interval_cases y <;> decide
      rw [hempty, Finset.sum_empty]
      have hlog : (0:ℝ) ≤ Real.log (y:ℝ) := Real.log_natCast_nonneg y
      linarith
    · exact sum_log_div_primesBelow_le_sharp y hy
  have hc1 : (0:ℝ) ≤ 2*ρ*(y:ℝ) := by positivity
  nlinarith [hmert, hcheb, hc1, Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)]

open Real Finset in
/-- **The Perron error over the outer prime range** (Track R, N91):
with the two block masses supplied,

  `∑_{p∈P} |log p·f(p)/log(x/p)|·(2ρ⌊x/p⌋(log⌊x/p⌋ + 2) + 6⌊x/p⌋log 4)`
  `  ≤ 2ρ·x·Mass₁ + 4ρ·x·Mass₂ + 6·x·log 4·Mass₂`,

where `Mass₁ ≥ ∑_p log p/p` and `Mass₂ ≥ ∑_p log p/(p·log(x/p))`.

`perron_error_inner_le` summed over the outer range.  Each term
contributes three pieces once `⌊x/p⌋ ≤ x/p` and `log⌊x/p⌋ ≤ log(x/p)`
are applied:
`2ρx·(log p/p)` from the leading `log(x/p)`, and `4ρx` and `6x·log 4`
times `log p/(p·log(x/p))` from the `+2` and the θ-term.

The two masses are left as parameters, as `Wtail` was: on a block the
first is Mertens (`≍ log x`) and the second is `≍ e^{k}/log x`, both
already on main, but which block is a §3 decision.  So the `2ρ` half is
`≍ ρ·x·log x` — **this is exactly what the choice of `ρ` must
control** — and the constant half is `O(x)`, which (3.2) already
allows.

`2p ≤ x` is what makes `log(x/p) > 0`, so the outer weight is defined
and `⌊x/p⌋ ≥ 2`. -/
theorem perron_error_outer_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (x : ℕ) (P : Finset ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hPp : ∀ p ∈ P, p.Prime) (h2p : ∀ p ∈ P, 2*p ≤ x)
    (Mass₁ Mass₂ : ℝ)
    (h1 : ∑ p ∈ P, Real.log (p:ℝ)/(p:ℝ) ≤ Mass₁)
    (h2 : ∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ)))
      ≤ Mass₂) :
    ∑ p ∈ P, |Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ))|
        * (2*ρ*(((x/p : ℕ)):ℝ)*(Real.log (((x/p : ℕ)):ℝ) + 2)
           + 6*(((x/p : ℕ)):ℝ)*Real.log 4)
      ≤ 2*ρ*(x:ℝ)*Mass₁ + 4*ρ*(x:ℝ)*Mass₂
        + 6*(x:ℝ)*Real.log 4*Mass₂ := by
  classical
  have hlog4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hterm : ∀ p ∈ P,
      |Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ))|
        * (2*ρ*(((x/p : ℕ)):ℝ)*(Real.log (((x/p : ℕ)):ℝ) + 2)
           + 6*(((x/p : ℕ)):ℝ)*Real.log 4)
      ≤ 2*ρ*(x:ℝ) * (Real.log (p:ℝ)/(p:ℝ))
        + (4*ρ*(x:ℝ) + 6*(x:ℝ)*Real.log 4)
            * (Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ)))) := by
    intro p hp
    have hpp : p.Prime := hPp p hp
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
    have hquot : (2:ℝ) ≤ (x:ℝ)/(p:ℝ) := by
      rw [le_div_iff₀ hp0]
      have hc : ((2*p : ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast h2p p hp
      push_cast at hc; linarith
    have hL : (0:ℝ) < Real.log ((x:ℝ)/(p:ℝ)) := Real.log_pos (by linarith)
    have hlog0 : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
    -- the outer weight
    have hw : |Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ))|
        ≤ Real.log (p:ℝ)/Real.log ((x:ℝ)/(p:ℝ)) := by
      rw [abs_div, abs_mul, abs_of_pos hL, abs_of_nonneg hlog0]
      refine div_le_div_of_nonneg_right ?_ hL.le
      nlinarith [hf p, abs_nonneg (f p), hlog0]
    -- the floor, and its logarithm
    have hfl : (((x/p : ℕ)):ℝ) ≤ (x:ℝ)/(p:ℝ) := Nat.cast_div_le
    have hfl0 : (0:ℝ) ≤ (((x/p : ℕ)):ℝ) := Nat.cast_nonneg _
    have hlogfl : Real.log (((x/p : ℕ)):ℝ) ≤ Real.log ((x:ℝ)/(p:ℝ)) := by
      rcases eq_or_lt_of_le hfl0 with h | h
      · rw [← h]; simpa using hL.le
      · exact Real.log_le_log h hfl
    -- the bracket, bounded by the true quotient
    have hbr : 2*ρ*(((x/p : ℕ)):ℝ)*(Real.log (((x/p : ℕ)):ℝ) + 2)
          + 6*(((x/p : ℕ)):ℝ)*Real.log 4
        ≤ 2*ρ*((x:ℝ)/(p:ℝ))*(Real.log ((x:ℝ)/(p:ℝ)) + 2)
          + 6*((x:ℝ)/(p:ℝ))*Real.log 4 := by
      have hlpos : (0:ℝ) ≤ Real.log (((x/p : ℕ)):ℝ) + 2 := by
        nlinarith [Real.log_natCast_nonneg (x/p)]
      have hQ0 : (0:ℝ) ≤ (x:ℝ)/(p:ℝ) := by positivity
      have h2ρ : (0:ℝ) ≤ 2*ρ := by linarith
      have hs1 : (((x/p : ℕ)):ℝ)*(Real.log (((x/p : ℕ)):ℝ) + 2)
          ≤ ((x:ℝ)/(p:ℝ))*(Real.log (((x/p : ℕ)):ℝ) + 2) :=
        mul_le_mul_of_nonneg_right hfl hlpos
      have hs2 : ((x:ℝ)/(p:ℝ))*(Real.log (((x/p : ℕ)):ℝ) + 2)
          ≤ ((x:ℝ)/(p:ℝ))*(Real.log ((x:ℝ)/(p:ℝ)) + 2) :=
        mul_le_mul_of_nonneg_left (by linarith [hlogfl]) hQ0
      have hA : 2*ρ*(((x/p : ℕ)):ℝ)*(Real.log (((x/p : ℕ)):ℝ) + 2)
          ≤ 2*ρ*((x:ℝ)/(p:ℝ))*(Real.log ((x:ℝ)/(p:ℝ)) + 2) := by
        calc 2*ρ*(((x/p : ℕ)):ℝ)*(Real.log (((x/p : ℕ)):ℝ) + 2)
            = 2*ρ*((((x/p : ℕ)):ℝ)*(Real.log (((x/p : ℕ)):ℝ) + 2)) := by ring
          _ ≤ 2*ρ*(((x:ℝ)/(p:ℝ))*(Real.log ((x:ℝ)/(p:ℝ)) + 2)) :=
              mul_le_mul_of_nonneg_left (le_trans hs1 hs2) h2ρ
          _ = 2*ρ*((x:ℝ)/(p:ℝ))*(Real.log ((x:ℝ)/(p:ℝ)) + 2) := by ring
      have hB : 6*(((x/p : ℕ)):ℝ)*Real.log 4
          ≤ 6*((x:ℝ)/(p:ℝ))*Real.log 4 := by
        calc 6*(((x/p : ℕ)):ℝ)*Real.log 4
            = 6*((((x/p : ℕ)):ℝ)*Real.log 4) := by ring
          _ ≤ 6*(((x:ℝ)/(p:ℝ))*Real.log 4) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hfl hlog4) (by norm_num)
          _ = 6*((x:ℝ)/(p:ℝ))*Real.log 4 := by ring
      linarith
    have hbr0 : (0:ℝ) ≤ 2*ρ*(((x/p : ℕ)):ℝ)*(Real.log (((x/p : ℕ)):ℝ) + 2)
        + 6*(((x/p : ℕ)):ℝ)*Real.log 4 := by
      have hlpos : (0:ℝ) ≤ Real.log (((x/p : ℕ)):ℝ) + 2 := by
        nlinarith [Real.log_natCast_nonneg (x/p)]
      have : (0:ℝ) ≤ 2*ρ*(((x/p : ℕ)):ℝ) := by positivity
      nlinarith [hfl0, hlog4]
    -- combine, then expand
    have hstep : |Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ))|
        * (2*ρ*(((x/p : ℕ)):ℝ)*(Real.log (((x/p : ℕ)):ℝ) + 2)
           + 6*(((x/p : ℕ)):ℝ)*Real.log 4)
        ≤ (Real.log (p:ℝ)/Real.log ((x:ℝ)/(p:ℝ)))
            * (2*ρ*((x:ℝ)/(p:ℝ))*(Real.log ((x:ℝ)/(p:ℝ)) + 2)
              + 6*((x:ℝ)/(p:ℝ))*Real.log 4) := by
      refine le_trans (mul_le_mul_of_nonneg_right hw hbr0) ?_
      refine mul_le_mul_of_nonneg_left hbr ?_
      positivity
    refine le_trans hstep (le_of_eq ?_)
    field_simp
    ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hc1 : (0:ℝ) ≤ 2*ρ*(x:ℝ) := by positivity
  have hc2 : (0:ℝ) ≤ 4*ρ*(x:ℝ) + 6*(x:ℝ)*Real.log 4 := by positivity
  nlinarith [h1, h2, hc1, hc2]

open Real Finset in
/-- **`tripleConv` is its smoothed form, up to the Perron error**
(Track R, N93): with the two block masses supplied,

  `|tripleConv f x P − ∑_p A(p)∑_q B(q)·⌊x/pq⌋·∑_n (f(n)/n)V(log⌊x/pq⌋ − log n)|`
  `  ≤ 2ρ·x·Mass₁ + 4ρ·x·Mass₂ + 6·x·log 4·Mass₂`.

The substitution §3 needs, assembled.  `perron_sandwich_uniform_real`
replaces `tripleConv`'s innermost sum — the only one of the three
factors whose coefficients are `1`-bounded — and the error it leaves
is summed by `perron_error_inner_le` over `q` and
`perron_error_outer_le` over `p`.

Three earlier checks are what make this a composition rather than an
argument: the sandwich holds at *every* scale (so the `pq > x/4` range
needs no separate treatment), it holds for *real* `g` (so `tripleConv`
needs no complex detour), and `⌊x/(pq)⌋ = ⌊⌊x/p⌋/q⌋` lets the inner
error be summed at `y = ⌊x/p⌋`.

The window's plateau is required only out to `2 log x + 1`; each
application needs it out to `2 log⌊x/(pq)⌋ + 1`, which is shorter.

`S := Icc 1 x` serves every scale at once, since `⌊x/(pq)⌋ ≤ x`. -/
theorem tripleConv_sub_smoothed_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (x : ℕ) (P : Finset ℕ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hPp : ∀ p ∈ P, p.Prime) (h2p : ∀ p ∈ P, 2*p ≤ x)
    (V : ℝ → ℝ)
    (hVplat : ∀ v, ρ ≤ v → v ≤ 2*Real.log (x:ℝ) + 1 → V v = Real.exp (-v))
    (hV0 : ∀ v, v ≤ 0 → V v = 0)
    (hVle : ∀ v, V v ≤ Real.exp (-v)) (hVnn : ∀ v, 0 ≤ V v)
    (Mass₁ Mass₂ : ℝ)
    (h1 : ∑ p ∈ P, Real.log (p:ℝ)/(p:ℝ) ≤ Mass₁)
    (h2 : ∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ)))
      ≤ Mass₂) :
    |tripleConv f x P
        - ∑ p ∈ P, (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
            * ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
                * ((((x/(p*q) : ℕ)):ℝ)
                  * ∑ n ∈ Finset.Icc 1 x, (f n/(n:ℝ))
                      * V (Real.log (((x/(p*q) : ℕ)):ℝ) - Real.log (n:ℝ)))|
      ≤ 2*ρ*(x:ℝ)*Mass₁ + 4*ρ*(x:ℝ)*Mass₂
        + 6*(x:ℝ)*Real.log 4*Mass₂ := by
  classical
  -- the per-(p,q) sandwich, at `S = Icc 1 x`
  have hsand : ∀ p ∈ P, ∀ q ∈ (x/p).primesBelow,
      |(∑ n ∈ Finset.Icc 1 (x/(p*q)), f n)
          - (((x/(p*q) : ℕ)):ℝ) * ∑ n ∈ Finset.Icc 1 x, (f n/(n:ℝ))
              * V (Real.log (((x/(p*q) : ℕ)):ℝ) - Real.log (n:ℝ))|
        ≤ 2*ρ*(((x/(p*q) : ℕ)):ℝ) + 6 := by
    intro p hp q hq
    set M : ℕ := x/(p*q) with hM_def
    have hMx : M ≤ x := by
      rw [hM_def]; exact Nat.div_le_self _ _
    have hM1 : 1 ≤ M := by
      have hqlt : q < x/p := (Nat.mem_primesBelow.mp hq).1
      have hq0 : 0 < q := (Nat.mem_primesBelow.mp hq).2.pos
      rw [hM_def, ← Nat.div_div_eq_div_mul]
      exact (Nat.one_le_div_iff hq0).mpr hqlt.le
    have hsub : Finset.Icc 1 M ⊆ Finset.Icc 1 x := by
      intro n hn
      rw [Finset.mem_Icc] at hn ⊢
      exact ⟨hn.1, le_trans hn.2 hMx⟩
    have hplat : ∀ v, ρ ≤ v → v ≤ 2*Real.log (M:ℝ) + 1 →
        V v = Real.exp (-v) := by
      intro v hv1 hv2
      refine hVplat v hv1 (le_trans hv2 ?_)
      have hMR : (M:ℝ) ≤ (x:ℝ) := by exact_mod_cast hMx
      have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM1
      have := Real.log_le_log hM0 hMR
      linarith
    exact ExpSums.perron_sandwich_uniform_real f hf V ρ M hM1 hρ0 hρ1
      hplat hV0 hVle hVnn (Finset.Icc 1 x) hsub
      (fun n hn => (Finset.mem_Icc.mp hn).1)
  -- collect over `q`, then over `p`
  rw [tripleConv, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hstep : ∀ p ∈ P,
      |(Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
          * ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
              * ∑ n ∈ Finset.Icc 1 (x/(p*q)), f n
        - (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
          * ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
              * ((((x/(p*q) : ℕ)):ℝ)
                * ∑ n ∈ Finset.Icc 1 x, (f n/(n:ℝ))
                    * V (Real.log (((x/(p*q) : ℕ)):ℝ) - Real.log (n:ℝ)))|
      ≤ |Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ))|
          * (2*ρ*(((x/p : ℕ)):ℝ)*(Real.log (((x/p : ℕ)):ℝ) + 2)
             + 6*(((x/p : ℕ)):ℝ)*Real.log 4) := by
    intro p hp
    rw [← mul_sub, abs_mul, ← Finset.sum_sub_distrib]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    -- per `q`: pull out `B(q)` and apply the sandwich
    have hq : ∀ q ∈ (x/p).primesBelow,
        |(Real.log (q:ℝ) * f q) * (∑ n ∈ Finset.Icc 1 (x/(p*q)), f n)
          - (Real.log (q:ℝ) * f q)
            * ((((x/(p*q) : ℕ)):ℝ)
              * ∑ n ∈ Finset.Icc 1 x, (f n/(n:ℝ))
                  * V (Real.log (((x/(p*q) : ℕ)):ℝ) - Real.log (n:ℝ)))|
          ≤ |Real.log (q:ℝ) * f q|
              * (2*ρ*((((x/p : ℕ)/q : ℕ)):ℝ) + 6) := by
      intro q hqm
      rw [← mul_sub, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have hdd : ((x/p : ℕ)/q : ℕ) = x/(p*q) := Nat.div_div_eq_div_mul x p q
      rw [hdd]
      exact hsand p hp q hqm
    refine le_trans (Finset.sum_le_sum hq) ?_
    exact perron_error_inner_le f hf (x/p) ρ hρ0.le
  refine le_trans (Finset.sum_le_sum hstep) ?_
  exact perron_error_outer_le f hf x P ρ hρ0.le hPp h2p Mass₁ Mass₂ h1 h2

open Real Finset in
/-- **§3's summand is `x` times §4's** (Track R, N99): for every
`(n, p, q)`,

  `(log p·f(p)/log(x/p)) · (log q·f(q)) · (x/pq) · (f(n)/n)`
  `  = x · ((f(n)/n) · (log p·f(p)/(p·log(x/p))) · (log q·f(q)/q))`.

The last unchecked conversion between §3 and §4, and it is exact.

`tripleConv`'s weights carry no `1/pq` — the inner sum is unnormalized —
while §4's polynomials are Dirichlet, carrying `1/p`, `1/q`, `1/n` on
the `1`-line.  Once the Perron substitution has produced the factor
`x/pq` (`perron_sandwich_uniform_real` at scale `x/pq`), the two agree:
the `x/pq` splits as `x` out front and `1/p`, `1/q` into the
coefficients, which is precisely `ghs_triple_product`'s summand.

The window arguments already match without any rewriting, since
`log(x/pq) − log n = log x − log(npq)`.

A field identity, so no positivity is needed: division is total, and
both sides normalise to `x·log p·f(p)·log q·f(q)·f(n) / (p·q·n·log(x/p))`. -/
theorem ghs_summand_regroup (f : ℕ → ℝ) (x p q n : ℕ) :
    (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
        * (Real.log (q:ℝ) * f q)
        * ((x:ℝ)/((p:ℝ)*(q:ℝ)))
        * (f n/(n:ℝ))
      = (x:ℝ) * ((f n/(n:ℝ))
          * (Real.log (p:ℝ) * f p / ((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
          * (Real.log (q:ℝ) * f q / (q:ℝ))) := by
  ring

open Real Finset in
/-- **The survivor's scale is bounded** (Track R, N102): for `2p ≤ x`,

  `x / (p·⌊x/p⌋) ≤ 2`.

The one arithmetic fact the range-enlargement discard needs.  When the
inner `q`-range is widened to a fixed set, every added prime with
`pq > x` dies (`smoothed_vanishes_of_lt_mul`); the single survivor is
`q = ⌊x/p⌋`, and its Perron scale is `x/(p·⌊x/p⌋)` — which is *not*
`1`, because the floor loses up to `p`.

It is at most `2`: `p·⌊x/p⌋ = x − (x mod p) ≥ x − p ≥ x/2` under
`2p ≤ x`.  That is what makes the survivor's contribution
`≤ 2·log⌊x/p⌋ ≤ 2·log(x/p)`, so against the outer weight
`|log p·f(p)/log(x/p)|` the `log(x/p)` cancels and the term costs
`≤ 2 log p` — summing to `O(x)` by Chebyshev's θ-bound, which `(3.2)`
allows.

Without the cancellation the discard would carry a `log x` and not
close, so the factor `2` here is doing real work. -/
theorem x_div_mul_floor_le_two (x p : ℕ) (hp : 0 < p) (h2p : 2*p ≤ x) :
    (x:ℝ)/((p:ℝ) * (((x/p : ℕ)):ℝ)) ≤ 2 := by
  have hx0 : (0:ℝ) < (x:ℝ) := by
    have : 0 < x := by omega
    exact_mod_cast this
  have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
  have h2pR : 2*(p:ℝ) ≤ (x:ℝ) := by exact_mod_cast h2p
  -- `p·⌊x/p⌋ = x − (x mod p)`
  have hdm : (p:ℝ) * (((x/p : ℕ)):ℝ) = (x:ℝ) - ((x % p : ℕ):ℝ) := by
    have h := Nat.div_add_mod x p
    have : ((p * (x/p) + x % p : ℕ):ℝ) = ((x:ℕ):ℝ) := by exact_mod_cast h
    push_cast at this
    linarith
  have hmod : ((x % p : ℕ):ℝ) < (p:ℝ) := by
    have : x % p < p := Nat.mod_lt _ hp
    exact_mod_cast this
  have hden : (x:ℝ)/2 ≤ (p:ℝ) * (((x/p : ℕ)):ℝ) := by
    rw [hdm]; linarith
  have hden0 : (0:ℝ) < (p:ℝ) * (((x/p : ℕ)):ℝ) := by
    have : (0:ℝ) < (x:ℝ)/2 := by linarith
    linarith
  rw [div_le_iff₀ hden0]
  linarith

open Real Finset in
/-- **The range enlargement costs one term** (Track R, N104): for
`2p ≤ x` and any set of primes `Q`,

  `|∑_{q ∈ Q \ (x/p).primesBelow} (log q·f(q))·((x/pq)·Smoothed(p,q))|`
  `  ≤ 2·log⌊x/p⌋`.

§3 sums `q` over `(x/p).primesBelow`, a range that moves with `p`;
§4 wants one fixed index set.  Widening to a fixed `Q` adds the primes
`q ≥ ⌊x/p⌋`, and this bounds what that costs.

Every added prime except one dies: `q ∉ (x/p).primesBelow` and `q`
prime give `q ≥ ⌊x/p⌋`, so `q ≠ ⌊x/p⌋` forces `q > ⌊x/p⌋`, hence
`p·q ≥ p·⌊x/p⌋ + p = (x − x mod p) + p > x`, and
`smoothed_vanishes_of_lt_mul` zeroes the whole inner sum.

The survivor is `q = ⌊x/p⌋` alone — a set of cardinality at most one,
**possibly empty**, since `⌊x/p⌋` need not be prime.  Its size is
`log⌊x/p⌋` from the coefficient, times `x/(p⌊x/p⌋) ≤ 2`
(`x_div_mul_floor_le_two`) times `≤ 1` from
`smoothed_sum_le_one_real`.

Against the outer weight `|log p·f(p)/log(x/p)|` the `log⌊x/p⌋ ≤
log(x/p)` cancels the denominator, leaving `≤ 2 log p` per `p` — so the
enlargement costs `O(x)` overall by Chebyshev, which `(3.2)` allows. -/
theorem enlargement_discard_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (V : ℝ → ℝ) (hV0 : ∀ v, v ≤ 0 → V v = 0)
    (hVle : ∀ v, V v ≤ Real.exp (-v)) (hVnn : ∀ v, 0 ≤ V v)
    (x p : ℕ) (hp : 0 < p) (h2p : 2*p ≤ x)
    (S : Finset ℕ) (hS1 : ∀ n ∈ S, 1 ≤ n)
    (Q : Finset ℕ) (hQp : ∀ q ∈ Q, q.Prime) :
    |∑ q ∈ Q \ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
        * (((x:ℝ)/((p:ℝ)*(q:ℝ)))
          * ∑ n ∈ S, (f n/(n:ℝ))
              * V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ)))|
      ≤ 2 * Real.log (((x/p : ℕ)):ℝ) := by
  classical
  set A : Finset ℕ := Q \ (x/p).primesBelow with hA_def
  set m : ℕ := x/p with hm_def
  have hm2 : 2 ≤ m := by
    rw [hm_def]
    exact Nat.le_div_iff_mul_le hp |>.mpr (by omega)
  have hmR : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm2
  have hlogm : (0:ℝ) ≤ Real.log (m:ℝ) := Real.log_natCast_nonneg m
  -- every added prime but `m` zeroes the inner sum
  have hvanish : ∀ q ∈ A, q ∉ A.filter (fun q : ℕ => q = m) →
      |(Real.log (q:ℝ) * f q)
        * (((x:ℝ)/((p:ℝ)*(q:ℝ)))
          * ∑ n ∈ S, (f n/(n:ℝ))
              * V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ)))| = 0 := by
    intro q hq hnot
    simp only [Finset.mem_filter, not_and] at hnot
    have hqne : q ≠ m := hnot hq
    rw [hA_def, Finset.mem_sdiff] at hq
    have hqp : q.Prime := hQp q hq.1
    have hqm : m ≤ q := by
      by_contra hcon
      push_neg at hcon
      exact hq.2 (Nat.mem_primesBelow.mpr ⟨hcon, hqp⟩)
    have hqgt : m < q := lt_of_le_of_ne hqm (Ne.symm hqne)
    -- `p·q > x`
    have hpq : x < p*q := by
      have hdm : p*m + x % p = x := by rw [hm_def]; exact Nat.div_add_mod x p
      have hmod : x % p < p := Nat.mod_lt _ hp
      have h1 : p*(m+1) ≤ p*q := Nat.mul_le_mul_left p hqgt
      have h2 : p*(m+1) = p*m + p := by ring
      omega
    rw [ExpSums.smoothed_vanishes_of_lt_mul V hV0 f x p q hp hqp.pos hpq S,
      mul_zero, mul_zero, abs_zero]
  have hrestrict : (∑ q ∈ A, |(Real.log (q:ℝ) * f q)
        * (((x:ℝ)/((p:ℝ)*(q:ℝ)))
          * ∑ n ∈ S, (f n/(n:ℝ))
              * V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ)))|)
      = ∑ q ∈ A.filter (fun q : ℕ => q = m), |(Real.log (q:ℝ) * f q)
          * (((x:ℝ)/((p:ℝ)*(q:ℝ)))
            * ∑ n ∈ S, (f n/(n:ℝ))
                * V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ)))| :=
    (Finset.sum_subset (Finset.filter_subset _ _)
      (fun q hq hnot => hvanish q hq hnot)).symm
  -- the survivor's size
  have hterm : ∀ q ∈ A.filter (fun q : ℕ => q = m),
      |(Real.log (q:ℝ) * f q)
        * (((x:ℝ)/((p:ℝ)*(q:ℝ)))
          * ∑ n ∈ S, (f n/(n:ℝ))
              * V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ)))|
      ≤ 2 * Real.log (m:ℝ) := by
    intro q hq
    simp only [Finset.mem_filter] at hq
    obtain ⟨-, hqm⟩ := hq
    rw [hqm]
    have hm0 : (0:ℝ) < (m:ℝ) := by linarith
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
    have hscale : (0:ℝ) < (x:ℝ)/((p:ℝ)*(m:ℝ)) := by
      have hx0 : (0:ℝ) < (x:ℝ) := by
        have : 0 < x := by omega
        exact_mod_cast this
      positivity
    have hcoef : |Real.log (m:ℝ) * f m| ≤ Real.log (m:ℝ) := by
      rw [abs_mul, abs_of_nonneg (Real.log_natCast_nonneg m)]
      nlinarith [hf m, abs_nonneg (f m), Real.log_natCast_nonneg m]
    have hsm := ExpSums.smoothed_sum_le_one_real f hf V _ hscale hV0 hVle
      hVnn S hS1
    have hsc2 : (x:ℝ)/((p:ℝ)*(m:ℝ)) ≤ 2 := x_div_mul_floor_le_two x p hp h2p
    have hinner : |((x:ℝ)/((p:ℝ)*(m:ℝ)))
        * ∑ n ∈ S, (f n/(n:ℝ))
            * V (Real.log ((x:ℝ)/((p:ℝ)*(m:ℝ))) - Real.log (n:ℝ))| ≤ 2 := by
      rw [abs_mul, abs_of_pos hscale]
      calc (x:ℝ)/((p:ℝ)*(m:ℝ)) * |∑ n ∈ S, (f n/(n:ℝ))
              * V (Real.log ((x:ℝ)/((p:ℝ)*(m:ℝ))) - Real.log (n:ℝ))|
          ≤ (x:ℝ)/((p:ℝ)*(m:ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left hsm hscale.le
        _ ≤ 2 := by linarith
    rw [abs_mul]
    calc |Real.log (m:ℝ) * f m| * |((x:ℝ)/((p:ℝ)*(m:ℝ)))
            * ∑ n ∈ S, (f n/(n:ℝ))
                * V (Real.log ((x:ℝ)/((p:ℝ)*(m:ℝ))) - Real.log (n:ℝ))|
        ≤ Real.log (m:ℝ) * 2 :=
          mul_le_mul hcoef hinner (abs_nonneg _)
            (Real.log_natCast_nonneg m)
      _ = 2 * Real.log (m:ℝ) := by ring
  -- at most one survivor
  have hcard : (A.filter (fun q : ℕ => q = m)).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    simp only [Finset.mem_filter] at ha hb
    rw [ha.2, hb.2]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [hrestrict]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hc : ((A.filter (fun q : ℕ => q = m)).card : ℝ) ≤ 1 := by
    exact_mod_cast hcard
  nlinarith [hc, hlogm]

open Real Finset in
/-- **The two window arguments agree** (Track R, N105): for
`x, n, p, q > 0`,

  `log(x/pq) − log n = log x − log(npq)`.

§3 and §4 write the window's argument differently.  After the scale
swap, §3's smoothed sum carries `V(log(x/pq) − log n)` — the Perron
scale minus the summation variable — while `ghs_smoothed_triple_le`
carries `V(y − log(npq))` at `y = log x`, the abscissa minus the whole
product.  They are the same real number, but not the same *term*, so
the reindex cannot proceed without this.

Positivity of all four is needed and is not a formality: at `x = 0` the
two sides are `−log n` and `−log(npq)`, which differ.  Lean's
`log 0 = 0` makes the statement silently false rather than
undefined. -/
theorem log_scale_sub_eq (x n p q : ℕ) (hx : 0 < x) (hn : 0 < n)
    (hp : 0 < p) (hq : 0 < q) :
    Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ)
      = Real.log (x:ℝ) - Real.log (((n*p*q : ℕ)):ℝ) := by
  have hxR : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hpq : ((p:ℝ)*(q:ℝ)) ≠ 0 := by positivity
  rw [Real.log_div (ne_of_gt hxR) hpq, Real.log_mul (ne_of_gt hpR) (ne_of_gt hqR)]
  push_cast
  rw [Real.log_mul (by positivity) (ne_of_gt hqR),
    Real.log_mul (ne_of_gt hnR) (ne_of_gt hpR)]
  ring

open Finset in
/-- **Flattening §4's index set** (Track R, N106): for any `g`,

  `∑_{r ∈ (S ×ˢ P) ×ˢ Q} g(r.1.1, r.1.2, r.2) = ∑_{n∈S} ∑_{p∈P} ∑_{q∈Q} g(n,p,q)`.

`Finset.sum_product` twice.  `ghs_triple_product` and
`ghs_smoothed_triple_le` index the triple convolution by
`(S ×ˢ P) ×ˢ Q` — a single `Finset` of nested pairs, which is what the
Plancherel pairing needs, since it takes one index set.  §3 instead
writes three nested sums, `p` outermost.

This is the structural half of the reindex between them.  What is left
after it is a transposition (§3's order is `p, q, n`; this produces
`n, p, q`) and the termwise rewriting supplied by
`ghs_summand_regroup` and `log_scale_sub_eq`.

Kept separate and fully general in `g` because the flattening is
purely combinatorial — it holds for any summand, with no positivity or
primality — whereas the two rewrites need `x, n, p, q > 0`.  Mixing
them would attach those hypotheses to a step that does not use
them. -/
theorem sum_triple_product_eq {M : Type*} [AddCommMonoid M]
    (g : ℕ → ℕ → ℕ → M) (S P Q : Finset ℕ) :
    (∑ r ∈ (S ×ˢ P) ×ˢ Q, g r.1.1 r.1.2 r.2)
      = ∑ n ∈ S, ∑ p ∈ P, ∑ q ∈ Q, g n p q := by
  rw [Finset.sum_product, Finset.sum_product]

open Finset in
/-- **§4's index set, in §3's order** (Track R, N107): for any `g`,

  `∑_{r ∈ (S ×ˢ P) ×ˢ Q} g(r.1.1, r.1.2, r.2) = ∑_{p∈P} ∑_{q∈Q} ∑_{n∈S} g(n,p,q)`.

`sum_triple_product_eq` followed by two transpositions.

The two sections disagree on more than bracketing.  §4 indexes the
triple convolution by `(S ×ˢ P) ×ˢ Q` with `n` innermost in the pair
structure, because the Plancherel pairing takes one index set and the
polynomial `P₁` (the `n`-sum) is its first factor.  §3 sums `p`
outermost — the block variable — then `q < x/p`, then `n ≤ x/pq`,
because that is the order the two applications of the log-identity
produce.

Flattening alone lands on `n, p, q`; getting to `p, q, n` needs
`Finset.sum_comm` twice, once at the outer level and once under the
`p`-binder.

Still general in `g` and hypothesis-free, for the same reason as the
flattening: reordering is combinatorial, and attaching the positivity
that the termwise rewrites need would misplace it. -/
theorem sum_triple_transpose {M : Type*} [AddCommMonoid M]
    (g : ℕ → ℕ → ℕ → M) (S P Q : Finset ℕ) :
    (∑ r ∈ (S ×ˢ P) ×ˢ Q, g r.1.1 r.1.2 r.2)
      = ∑ p ∈ P, ∑ q ∈ Q, ∑ n ∈ S, g n p q := by
  rw [sum_triple_product_eq, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]

open Real Finset in
/-- **§3's triple sum is `x` times §4's** (Track R, N108): for
`x, n, p, q > 0` throughout,

  `∑_p A(p)·∑_q B(q)·((x/pq)·∑_n (f(n)/n)·V(log(x/pq) − log n))`
  `  = x · ∑_{r ∈ (S ×ˢ P) ×ˢ Q} (c·a·b)·V(log x − log(npq))`.

The reindex, assembled.  `sum_triple_transpose` puts §4's index set in
§3's order, `Finset.mul_sum` distributes the outer weights inward, and
then each term is matched by `log_scale_sub_eq` (the window argument)
and pure field algebra (the coefficients).

The coefficient step needs no lemma: with the window factor opaque and
identical on both sides, `ring` normalises straight through
`ghs_summand_regroup`'s identity, since that is a field identity with
no side conditions.  Only the window argument has to be rewritten
first, and that is where the positivity hypotheses are spent.

This is the last purely structural step between `tripleConv` and §4's
estimate; what remains is the `ℝ`-to-`ℂ` coercion and the final
assembly. -/
theorem ghs_reindex (f : ℕ → ℝ) (V : ℝ → ℝ) (x : ℕ) (hx : 0 < x)
    (S P Q : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) (hP : ∀ p ∈ P, 0 < p)
    (hQ : ∀ q ∈ Q, 0 < q) :
    (∑ p ∈ P, (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
        * ∑ q ∈ Q, (Real.log (q:ℝ) * f q)
            * (((x:ℝ)/((p:ℝ)*(q:ℝ)))
              * ∑ n ∈ S, (f n/(n:ℝ))
                  * V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ))))
      = (x:ℝ) * ∑ r ∈ (S ×ˢ P) ×ˢ Q,
          ((f r.1.1/(r.1.1:ℝ))
            * (Real.log (r.1.2:ℝ) * f r.1.2
                / ((r.1.2:ℝ) * Real.log ((x:ℝ)/(r.1.2:ℝ))))
            * (Real.log (r.2:ℝ) * f r.2 / (r.2:ℝ)))
          * V (Real.log (x:ℝ) - Real.log (((r.1.1 * r.1.2 * r.2 : ℕ)):ℝ)) := by
  classical
  rw [sum_triple_transpose
    (fun n p q => ((f n/(n:ℝ))
        * (Real.log (p:ℝ) * f p / ((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
        * (Real.log (q:ℝ) * f q / (q:ℝ)))
      * V (Real.log (x:ℝ) - Real.log (((n * p * q : ℕ)):ℝ))) S P Q]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  refine Finset.sum_congr rfl fun q hq => ?_
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [← log_scale_sub_eq x n p q hx (hS n hn) (hP p hp) (hQ q hq)]
  ring

open Real Complex Finset in
/-- **§4's triple sum at a real coefficient sequence** (Track R, N109):
for real `f`, the `ℂ`-valued sum `ghs_smoothed_triple_le` bounds is the
coercion of the `ℝ`-valued one `ghs_reindex` produces.

`ghs_smoothed_triple_le` is stated for `f : ℕ → ℂ`, because §4's
polynomials are `ℂ`-valued phase sums; `tripleConv` and the whole of §3
are real.  Every factor is the coercion of a real one, so the two sums
agree under `Complex.ofReal` — but they are not the same *term*, and
the assembly has to move between them.

This is the third type mismatch on the path from `tripleConv` to §4's
estimate, after the sandwich's `ℝ`/`ℂ` (`perron_sandwich_uniform_real`)
and the scale's `ℕ`/`ℝ` (`smoothed_sum_le_one_real`).  All three were
cheap to fix at the source and would have been expensive to meet inside
the assembly, which is why each is its own lemma rather than an inline
`push_cast`. -/
theorem ghs_triple_sum_ofReal (f : ℕ → ℝ) (V : ℝ → ℝ) (x : ℕ)
    (S P Q : Finset ℕ) (y : ℝ) :
    (∑ r ∈ (S ×ˢ P) ×ˢ Q,
        ((((f r.1.1 : ℝ):ℂ) / (r.1.1:ℂ))
          * (((Real.log (r.1.2:ℝ) : ℂ) * ((f r.1.2 : ℝ):ℂ))
              / ((r.1.2:ℂ) * ((Real.log ((x:ℝ)/(r.1.2:ℝ)) : ℝ):ℂ)))
          * (((Real.log (r.2:ℝ) : ℂ) * ((f r.2 : ℝ):ℂ)) / (r.2:ℂ)))
        * ((((V (y - Real.log (((r.1.1 * r.1.2 * r.2 : ℕ)):ℝ)) : ℝ)):ℂ)))
      = (((∑ r ∈ (S ×ˢ P) ×ˢ Q,
          ((f r.1.1/(r.1.1:ℝ))
            * (Real.log (r.1.2:ℝ) * f r.1.2
                / ((r.1.2:ℝ) * Real.log ((x:ℝ)/(r.1.2:ℝ))))
            * (Real.log (r.2:ℝ) * f r.2 / (r.2:ℝ)))
          * V (y - Real.log (((r.1.1 * r.1.2 * r.2 : ℕ)):ℝ)) : ℝ)) : ℂ) := by
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  push_cast
  ring

open MeasureTheory Real Complex Finset in
open scoped FourierTransform ContDiff in
/-- **§4's bound, real-valued** (Track R, N110): for real `1`-bounded
`f`,

  `|∑_{r ∈ (S ×ˢ P) ×ˢ Q} (c·a·b)·V(log x − log(npq))|`
  `  ≤ √(E₁·(30·(2M_V + M₂/2π²)·V₃·b² + Mtail))`.

`ghs_smoothed_triple_le` at the coerced coefficients, read back through
`ghs_triple_sum_ofReal`.

This is the half of §3's assembly that carries no error terms: §4's
estimate applies to the reindexed sum verbatim once the coefficients
are real.  The other half — collecting the Perron error, the scale
swap and the range discard — shares no machinery with it and is
separate.

`‖(r : ℂ)‖ = |r|` is what makes the two bounds the same statement; the
`ℂ` norm on the left of `ghs_smoothed_triple_le` and the `ℝ` absolute
value here are not interchangeable by notation, only by that
lemma. -/
theorem ghs_smoothed_triple_le_real (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (x : ℕ) (S P Q : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) (hP : ∀ p ∈ P, 0 < p) (hQ : ∀ q ∈ Q, 0 < q)
    (V : ℝ → ℝ) (hVs : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (M₂ M₃ MV : ℝ)
    (hM₂ : ∫ v, |iteratedDeriv 2 V v| ≤ M₂)
    (hM₃ : ∫ v, |iteratedDeriv 3 V v| ≤ M₃)
    (hMV : ∀ ξ, ‖𝓕 (fun v => ((V v : ℝ) : ℂ)) ξ‖ ≤ MV)
    (V₃ Mtail E₁ b : ℝ)
    (hE₁0 : 0 < E₁) (hb0 : 0 ≤ b) (hV₃0 : 0 ≤ V₃) (hMtail0 : 0 < Mtail)
    (hE₁ : (∫ ξ, ‖ghsBlockPoly (fun n => ((f n : ℝ) : ℂ)) x P ξ‖^2
        * ‖𝓕 (fun v => ((V v : ℝ) : ℂ)) ξ‖) ≤ E₁)
    (hBu : ∀ t : ℝ, ‖ghsMainPoly (fun n => ((f n : ℝ) : ℂ)) S t‖ ≤ b)
    (hV : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2),
        ‖ghsPrimePoly (fun n => ((f n : ℝ) : ℂ)) Q t‖^2) ≤ V₃)
    (hMtail : (∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ))^2
        * (∑ n ∈ S, (1:ℝ)/(n:ℝ))^2
        * (M₃/(8*Real.pi^3*(((halaszM x : ℕ):ℝ) + 1/2)^2)) ≤ Mtail) :
    |∑ r ∈ (S ×ˢ P) ×ˢ Q,
        ((f r.1.1/(r.1.1:ℝ))
          * (Real.log (r.1.2:ℝ) * f r.1.2
              / ((r.1.2:ℝ) * Real.log ((x:ℝ)/(r.1.2:ℝ))))
          * (Real.log (r.2:ℝ) * f r.2 / (r.2:ℝ)))
        * V (Real.log (x:ℝ) - Real.log (((r.1.1 * r.1.2 * r.2 : ℕ)):ℝ))|
      ≤ Real.sqrt (E₁ * (5 * (2*MV + M₂/(2*Real.pi^2)) * V₃ * (6*b^2)
          + Mtail)) := by
  classical
  have hfc : ∀ n, ‖((f n : ℝ) : ℂ)‖ ≤ 1 := by
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hf n
  have h86 := ghs_smoothed_triple_le (fun n => ((f n : ℝ) : ℂ)) hfc
    x S P Q hS hP hQ V hVs hVc M₂ M₃ MV hM₂ hM₃ hMV V₃ Mtail E₁ b
    hE₁0 hb0 hV₃0 hMtail0 hE₁ hBu hV hMtail (Real.log (x:ℝ))
  rw [ghs_triple_sum_ofReal f V x S P Q (Real.log (x:ℝ)),
    Complex.norm_real, Real.norm_eq_abs] at h86
  exact h86

open Real Finset in
/-- **The scale swap at §3's own quotient** (Track R, N111): for
`1 ≤ ⌊x/pq⌋`,

  `|∑_{n∈S} (f(n)/n)·(⌊x/pq⌋·V(log⌊x/pq⌋ − log n) − (x/pq)·V(log(x/pq) − log n))|`
  `  ≤ 2ρ·⌊x/pq⌋ + 2`.

`scale_diff_le` with the two scales it is actually used at, so the
floor relations are discharged once here rather than at every call.

Three hypotheses of the general form become facts about `ℕ`-division:
`⌊x/pq⌋ ≤ x/pq` is `Nat.cast_div_le`, `x/pq < ⌊x/pq⌋ + 1` is
`Nat.lt_div_add_one_mul_self`, and the plateau reach
`log(x/pq) ≤ 2 log x + 1` follows from `x/pq ≤ x`.

The resulting `2ρ⌊x/pq⌋ + 2` is below the `2ρ⌊x/pq⌋ + 6` that
`perron_sandwich_uniform_real` already produces, so
`perron_error_inner_le` and `perron_error_outer_le` absorb it over `q`
and `p` with no new machinery — the scale swap costs the same order as
the Perron error it sits beside. -/
theorem scale_diff_at_quotient_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (V : ℝ → ℝ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (x p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hM1 : 1 ≤ x/(p*q))
    (hplat : ∀ v, ρ ≤ v → v ≤ 2*Real.log (x:ℝ) + 1 → V v = Real.exp (-v))
    (hV0 : ∀ v, v ≤ 0 → V v = 0) (hVle : ∀ v, V v ≤ Real.exp (-v))
    (hVnn : ∀ v, 0 ≤ V v)
    (S : Finset ℕ) (hS1 : ∀ n ∈ S, 1 ≤ n) :
    |∑ n ∈ S, (f n/(n:ℝ))
        * ((((x/(p*q) : ℕ)):ℝ)
            * V (Real.log ((((x/(p*q) : ℕ)):ℝ)) - Real.log (n:ℝ))
          - ((x:ℝ)/((p:ℝ)*(q:ℝ)))
            * V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ)))|
      ≤ 2*ρ*((((x/(p*q) : ℕ)):ℝ)) + 2 := by
  classical
  have hpq0 : 0 < p*q := Nat.mul_pos hp hq
  have hpqR : (0:ℝ) < (p:ℝ)*(q:ℝ) := by
    have h1 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
    have h2 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
    positivity
  have hx1 : 1 ≤ x := by
    have := Nat.div_le_self x (p*q)
    omega
  have hxR : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx1
  -- the floor sits below the quotient
  have hMQ : (((x/(p*q) : ℕ)):ℝ) ≤ (x:ℝ)/((p:ℝ)*(q:ℝ)) := by
    have h := Nat.cast_div_le (α := ℝ) (m := x) (n := p*q)
    push_cast at h
    exact h
  -- and the quotient below the next integer
  have hQM : (x:ℝ)/((p:ℝ)*(q:ℝ)) < (((x/(p*q) : ℕ)):ℝ) + 1 := by
    have hlt : x < (x/(p*q) + 1) * (p*q) := by
      have hdm := Nat.div_add_mod x (p*q)
      have hmod : x % (p*q) < p*q := Nat.mod_lt _ hpq0
      have hexp : (x/(p*q) + 1) * (p*q) = (p*q) * (x/(p*q)) + (p*q) := by ring
      omega
    have hltR : (x:ℝ) < ((((x/(p*q) : ℕ)):ℝ) + 1) * ((p:ℝ)*(q:ℝ)) := by
      have : ((x:ℕ):ℝ) < (((x/(p*q) + 1) * (p*q) : ℕ):ℝ) := by exact_mod_cast hlt
      push_cast at this
      linarith
    rw [div_lt_iff₀ hpqR]
    exact hltR
  -- the plateau reaches the quotient
  have hB : Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) ≤ 2*Real.log (x:ℝ) + 1 := by
    have hle : (x:ℝ)/((p:ℝ)*(q:ℝ)) ≤ (x:ℝ) := by
      rw [div_le_iff₀ hpqR]
      have h1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
      have h2 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
      have hpq1 : (1:ℝ) ≤ (p:ℝ)*(q:ℝ) := by nlinarith
      nlinarith [hxR, hpq1]
    have hpos : (0:ℝ) < (x:ℝ)/((p:ℝ)*(q:ℝ)) := by
      have hM0 : (0:ℝ) < (((x/(p*q) : ℕ)):ℝ) := by
        have : (1:ℝ) ≤ (((x/(p*q) : ℕ)):ℝ) := by exact_mod_cast hM1
        linarith
      linarith
    have hmono := Real.log_le_log hpos hle
    have hlogx : (0:ℝ) ≤ Real.log (x:ℝ) := Real.log_nonneg hxR
    linarith
  exact ExpSums.scale_diff_le f hf V ρ (2*Real.log (x:ℝ) + 1) hρ0
    (x/(p*q)) ((x:ℝ)/((p:ℝ)*(q:ℝ))) hM1 hMQ hQM hplat hV0 hVle hVnn hB S hS1

open Real Finset in
/-- **The scale swap, summed** (Track R, N112): with the two block
masses supplied,

  `|∑_p A(p)·∑_q B(q)·∑_n (f(n)/n)·(⌊x/pq⌋·V(log⌊x/pq⌋ − log n) − (x/pq)·V(log(x/pq) − log n))|`
  `  ≤ 2ρ·x·Mass₁ + 4ρ·x·Mass₂ + 6·x·log 4·Mass₂`.

`scale_diff_at_quotient_le` summed by `perron_error_inner_le` over `q`
and `perron_error_outer_le` over `p` — **the same two lemmas, with the
same bound, that already absorb the Perron error itself**.

That is the economy the constants bought: the per-pair scale cost
`2ρ⌊x/pq⌋ + 2` sits under the `2ρ⌊x/pq⌋ + 6` those lemmas are stated
for, so trading §3's integer scale for §4's real one is free of new
machinery and costs the same order as the substitution it accompanies.

`⌊(x/p)/q⌋ = ⌊x/pq⌋` (`Nat.div_div_eq_div_mul`) is what lets the inner
summation happen at `y = ⌊x/p⌋`, which is the range `q` actually runs
over. -/
theorem scale_swap_error_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (V : ℝ → ℝ) (ρ : ℝ) (hρ0 : 0 < ρ)
    (x : ℕ) (P : Finset ℕ) (hPp : ∀ p ∈ P, p.Prime) (h2p : ∀ p ∈ P, 2*p ≤ x)
    (hplat : ∀ v, ρ ≤ v → v ≤ 2*Real.log (x:ℝ) + 1 → V v = Real.exp (-v))
    (hV0 : ∀ v, v ≤ 0 → V v = 0) (hVle : ∀ v, V v ≤ Real.exp (-v))
    (hVnn : ∀ v, 0 ≤ V v)
    (S : Finset ℕ) (hS1 : ∀ n ∈ S, 1 ≤ n)
    (Mass₁ Mass₂ : ℝ)
    (h1 : ∑ p ∈ P, Real.log (p:ℝ)/(p:ℝ) ≤ Mass₁)
    (h2 : ∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ)))
      ≤ Mass₂) :
    |∑ p ∈ P, (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
        * ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
            * ∑ n ∈ S, (f n/(n:ℝ))
                * ((((x/(p*q) : ℕ)):ℝ)
                    * V (Real.log ((((x/(p*q) : ℕ)):ℝ)) - Real.log (n:ℝ))
                  - ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                    * V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ)))|
      ≤ 2*ρ*(x:ℝ)*Mass₁ + 4*ρ*(x:ℝ)*Mass₂
        + 6*(x:ℝ)*Real.log 4*Mass₂ := by
  classical
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hstep : ∀ p ∈ P,
      |(Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
        * ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
            * ∑ n ∈ S, (f n/(n:ℝ))
                * ((((x/(p*q) : ℕ)):ℝ)
                    * V (Real.log ((((x/(p*q) : ℕ)):ℝ)) - Real.log (n:ℝ))
                  - ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                    * V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ)))|
      ≤ |Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ))|
          * (2*ρ*(((x/p : ℕ)):ℝ)*(Real.log (((x/p : ℕ)):ℝ) + 2)
             + 6*(((x/p : ℕ)):ℝ)*Real.log 4) := by
    intro p hp
    have hp0 : 0 < p := (hPp p hp).pos
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hq : ∀ q ∈ (x/p).primesBelow,
        |(Real.log (q:ℝ) * f q)
          * ∑ n ∈ S, (f n/(n:ℝ))
              * ((((x/(p*q) : ℕ)):ℝ)
                  * V (Real.log ((((x/(p*q) : ℕ)):ℝ)) - Real.log (n:ℝ))
                - ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                  * V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ)))|
          ≤ |Real.log (q:ℝ) * f q|
              * (2*ρ*((((x/p : ℕ)/q : ℕ)):ℝ) + 6) := by
      intro q hqm
      have hq0 : 0 < q := (Nat.mem_primesBelow.mp hqm).2.pos
      have hM1 : 1 ≤ x/(p*q) := by
        have hqlt : q < x/p := (Nat.mem_primesBelow.mp hqm).1
        rw [← Nat.div_div_eq_div_mul]
        exact (Nat.one_le_div_iff hq0).mpr hqlt.le
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have hdd : ((x/p : ℕ)/q : ℕ) = x/(p*q) := Nat.div_div_eq_div_mul x p q
      rw [hdd]
      refine le_trans (scale_diff_at_quotient_le f hf V ρ hρ0.le x p q hp0 hq0
        hM1 hplat hV0 hVle hVnn S hS1) ?_
      linarith
    refine le_trans (Finset.sum_le_sum hq) ?_
    exact perron_error_inner_le f hf (x/p) ρ hρ0.le
  refine le_trans (Finset.sum_le_sum hstep) ?_
  exact perron_error_outer_le f hf x P ρ hρ0.le hPp h2p Mass₁ Mass₂ h1 h2

open Real Finset in
/-- **The discard's `log` cancels** (Track R, N113): for `p` prime with
`2p ≤ x`,

  `|log p·f(p)/log(x/p)| · (2·log⌊x/p⌋) ≤ 2·log p`.

The step that keeps the range enlargement affordable.
`enlargement_discard_le` costs `2 log⌊x/p⌋` per `p`, and the outer
weight carries `1/log(x/p)`; since `⌊x/p⌋ ≤ x/p` the two logs cancel
and only `2 log p` survives — which Chebyshev's `θ`-bound sums to
`O(x)`, within what `(3.2)` allows.

Bounding `log⌊x/p⌋` by `log x` instead would leave
`2 log p·log x/log(x/p)`, whose sum carries a `log x`; on the top block
(`p ≍ x/e`) the ratio `log x/log(x/p)` is itself of size `log x`, so
this is not a slack estimate but the difference between closing and
not.

`2p ≤ x` gives `log(x/p) ≥ log 2 > 0`, so the division is safe, and
`⌊x/p⌋ ≥ 2`, so `log⌊x/p⌋ ≥ 0`. -/
theorem discard_weight_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (x p : ℕ) (hp : p.Prime) (h2p : 2*p ≤ x) :
    |Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ))|
        * (2 * Real.log (((x/p : ℕ)):ℝ))
      ≤ 2 * Real.log (p:ℝ) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
  have hquot : (2:ℝ) ≤ (x:ℝ)/(p:ℝ) := by
    rw [le_div_iff₀ hp0]
    have hc : ((2*p : ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast h2p
    push_cast at hc; linarith
  have hL : (0:ℝ) < Real.log ((x:ℝ)/(p:ℝ)) := Real.log_pos (by linarith)
  have hlogp : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
  -- the floor's log is at most the quotient's
  have hfl : (((x/p : ℕ)):ℝ) ≤ (x:ℝ)/(p:ℝ) := Nat.cast_div_le
  have hfl0 : (0:ℝ) ≤ Real.log (((x/p : ℕ)):ℝ) :=
    Real.log_natCast_nonneg (x/p)
  have hlogfl : Real.log (((x/p : ℕ)):ℝ) ≤ Real.log ((x:ℝ)/(p:ℝ)) := by
    rcases eq_or_lt_of_le (Nat.cast_nonneg (α := ℝ) (x/p)) with h | h
    · rw [← h]; simpa using hL.le
    · exact Real.log_le_log h hfl
  -- the outer weight
  have hw : |Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ))|
      ≤ Real.log (p:ℝ)/Real.log ((x:ℝ)/(p:ℝ)) := by
    rw [abs_div, abs_mul, abs_of_pos hL, abs_of_nonneg hlogp]
    refine div_le_div_of_nonneg_right ?_ hL.le
    nlinarith [hf p, abs_nonneg (f p), hlogp]
  calc |Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ))|
        * (2 * Real.log (((x/p : ℕ)):ℝ))
      ≤ (Real.log (p:ℝ)/Real.log ((x:ℝ)/(p:ℝ)))
          * (2 * Real.log (((x/p : ℕ)):ℝ)) := by
        refine mul_le_mul_of_nonneg_right hw (by linarith)
    _ ≤ (Real.log (p:ℝ)/Real.log ((x:ℝ)/(p:ℝ)))
          * (2 * Real.log ((x:ℝ)/(p:ℝ))) := by
        refine mul_le_mul_of_nonneg_left (by linarith) ?_
        positivity
    _ = 2 * Real.log (p:ℝ) := by
        field_simp

open Real Finset in
/-- **The range enlargement, summed** (Track R, N114): for `P` a set of
primes with `2p ≤ x`,

  `|∑_p A(p)·∑_{q ∈ Q \ (x/p).primesBelow} B(q)·((x/pq)·Smoothed(p,q))|`
  `  ≤ 2·x·log 4`.

The last of §3's three error terms, and the only one that is `O(x)`
outright rather than `O(ρ·x·log x)`.

Three facts compose.  `enlargement_discard_le` bounds the added range
at `2 log⌊x/p⌋` per `p`; `discard_weight_le` cancels that against the
outer weight's `1/log(x/p)`, leaving `2 log p`; and Chebyshev's
`θ`-bound sums `∑_p 2 log p` over primes below `x` to `2x·log 4`.

`P ⊆ x.primesBelow` is what the last step needs, and it comes from
`2p ≤ x` — the same hypothesis that makes the outer weight defined.
So the enlargement is affordable for exactly the reason the weight is
well-formed. -/
theorem enlargement_error_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (V : ℝ → ℝ) (hV0 : ∀ v, v ≤ 0 → V v = 0)
    (hVle : ∀ v, V v ≤ Real.exp (-v)) (hVnn : ∀ v, 0 ≤ V v)
    (x : ℕ) (P : Finset ℕ) (hPp : ∀ p ∈ P, p.Prime) (h2p : ∀ p ∈ P, 2*p ≤ x)
    (S : Finset ℕ) (hS1 : ∀ n ∈ S, 1 ≤ n)
    (Q : Finset ℕ) (hQp : ∀ q ∈ Q, q.Prime) :
    |∑ p ∈ P, (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
        * ∑ q ∈ Q \ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
            * (((x:ℝ)/((p:ℝ)*(q:ℝ)))
              * ∑ n ∈ S, (f n/(n:ℝ))
                  * V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ)))|
      ≤ 2 * (x:ℝ) * Real.log 4 := by
  classical
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  -- per `p`: the discard, then the cancellation
  have hstep : ∀ p ∈ P,
      |(Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
        * ∑ q ∈ Q \ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
            * (((x:ℝ)/((p:ℝ)*(q:ℝ)))
              * ∑ n ∈ S, (f n/(n:ℝ))
                  * V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ)))|
      ≤ 2 * Real.log (p:ℝ) := by
    intro p hp
    have hpp : p.Prime := hPp p hp
    rw [abs_mul]
    refine le_trans (mul_le_mul_of_nonneg_left
      (enlargement_discard_le f hf V hV0 hVle hVnn x p hpp.pos (h2p p hp)
        S hS1 Q hQp) (abs_nonneg _)) ?_
    exact discard_weight_le f hf x p hpp (h2p p hp)
  refine le_trans (Finset.sum_le_sum hstep) ?_
  -- Chebyshev over the primes below `x`
  rw [← Finset.mul_sum]
  have hsub : P ⊆ x.primesBelow := by
    intro p hp
    have hpp : p.Prime := hPp p hp
    have h2 := h2p p hp
    have hp2 : 2 ≤ p := hpp.two_le
    exact Nat.mem_primesBelow.mpr ⟨by omega, hpp⟩
  have hmono : ∑ p ∈ P, Real.log (p:ℝ)
      ≤ ∑ p ∈ x.primesBelow, Real.log (p:ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => Real.log_natCast_nonneg i)
  have hcheb : ∑ p ∈ x.primesBelow, Real.log (p:ℝ) ≤ (x:ℝ) * Real.log 4 :=
    sum_log_primesBelow_le x
  linarith [hmono, hcheb]

open Real Finset in
/-- **Extending the inner range** (Track R, N115): when every
`(x/p).primesBelow` sits inside a fixed `Q`,

  `|∑_p A(p)·∑_{q∈Q} T(p,q) − ∑_p A(p)·∑_{q<x/p} T(p,q)| ≤ 2·x·log 4`.

`enlargement_error_le` in the form the assembly consumes: a *difference*
between §3's `p`-dependent inner range and §4's fixed one, rather than a
bound on the added terms.

The two are the same statement only because `Finset.sum_sdiff` makes the
added terms exactly `Q \ (x/p).primesBelow`; that identity needs the
inclusion, which is why it appears here and not in
`enlargement_error_le`.  Taking `Q := x.primesBelow` discharges it, since
`⌊x/p⌋ ≤ x`.

This is the third and last of the three differences the error half
chains through — after the Perron substitution and the scale swap — and
the only one whose statement had to be reshaped to fit. -/
theorem enlargement_extend_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (V : ℝ → ℝ) (hV0 : ∀ v, v ≤ 0 → V v = 0)
    (hVle : ∀ v, V v ≤ Real.exp (-v)) (hVnn : ∀ v, 0 ≤ V v)
    (x : ℕ) (P : Finset ℕ) (hPp : ∀ p ∈ P, p.Prime) (h2p : ∀ p ∈ P, 2*p ≤ x)
    (S : Finset ℕ) (hS1 : ∀ n ∈ S, 1 ≤ n)
    (Q : Finset ℕ) (hQp : ∀ q ∈ Q, q.Prime)
    (hQsub : ∀ p ∈ P, (x/p).primesBelow ⊆ Q) :
    |(∑ p ∈ P, (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
        * ∑ q ∈ Q, (Real.log (q:ℝ) * f q)
            * (((x:ℝ)/((p:ℝ)*(q:ℝ)))
              * ∑ n ∈ S, (f n/(n:ℝ))
                  * V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ))))
      - (∑ p ∈ P, (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
        * ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
            * (((x:ℝ)/((p:ℝ)*(q:ℝ)))
              * ∑ n ∈ S, (f n/(n:ℝ))
                  * V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ))))|
      ≤ 2 * (x:ℝ) * Real.log 4 := by
  classical
  -- the two `p`-sums differ termwise by the added inner range
  have hsplit : (∑ p ∈ P, (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
        * ∑ q ∈ Q, (Real.log (q:ℝ) * f q)
            * (((x:ℝ)/((p:ℝ)*(q:ℝ)))
              * ∑ n ∈ S, (f n/(n:ℝ))
                  * V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ))))
      - (∑ p ∈ P, (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
        * ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
            * (((x:ℝ)/((p:ℝ)*(q:ℝ)))
              * ∑ n ∈ S, (f n/(n:ℝ))
                  * V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ))))
      = ∑ p ∈ P, (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
          * ∑ q ∈ Q \ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
              * (((x:ℝ)/((p:ℝ)*(q:ℝ)))
                * ∑ n ∈ S, (f n/(n:ℝ))
                    * V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                      - Real.log (n:ℝ))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← mul_sub]
    congr 1
    rw [sub_eq_iff_eq_add]
    exact (Finset.sum_sdiff (hQsub p hp)).symm
  rw [hsplit]
  exact enlargement_error_le f hf V hV0 hVle hVnn x P hPp h2p S hS1 Q hQp

open Real Finset in
/-- **`tripleConv` is `x` times §4's sum, up to the three errors**
(Track R, N116):

  `|tripleConv f x P − x·∑_{r ∈ (Finset.Icc 1 x ×ˢ P) ×ˢ Q} (c·a·b)·V(log x − log(npq))|`
  `  ≤ 2·(2ρx·Mass₁ + 4ρx·Mass₂ + 6x·log 4·Mass₂) + 2x·log 4`.

The error half of §3's assembly.  Three differences chain by the
triangle inequality, and the fourth step is an equality:

* `tripleConv` → the smoothed form at the integer scale — the Perron
  substitution, `tripleConv_sub_smoothed_le`;
* → the same at the real scale `x/pq` — the scale swap,
  `scale_swap_error_le`;
* → the same over the fixed inner range `Q` — the enlargement,
  `enlargement_extend_le`;
* → `x` times §4's product-indexed sum — `ghs_reindex`, **exact**.

The order is forced: the substitution lands on `(x/p).primesBelow` at
the integer scale, the swap changes the scale on that same range, and
only then can the range be widened.  Each intermediate form is the
next step's left-hand side, which is why the three error lemmas were
shaped as differences rather than as bounds on their own terms. -/
theorem tripleConv_sub_ghs_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (V : ℝ → ℝ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (x : ℕ) (hx : 0 < x) (P : Finset ℕ)
    (hPp : ∀ p ∈ P, p.Prime) (h2p : ∀ p ∈ P, 2*p ≤ x)
    (hplat : ∀ v, ρ ≤ v → v ≤ 2*Real.log (x:ℝ) + 1 → V v = Real.exp (-v))
    (hV0 : ∀ v, v ≤ 0 → V v = 0)
    (hVle : ∀ v, V v ≤ Real.exp (-v)) (hVnn : ∀ v, 0 ≤ V v)
    (Q : Finset ℕ) (hQp : ∀ q ∈ Q, q.Prime) (hQ : ∀ q ∈ Q, 0 < q)
    (hQsub : ∀ p ∈ P, (x/p).primesBelow ⊆ Q)
    (Mass₁ Mass₂ : ℝ)
    (h1 : ∑ p ∈ P, Real.log (p:ℝ)/(p:ℝ) ≤ Mass₁)
    (h2 : ∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ)))
      ≤ Mass₂) :
    |tripleConv f x P
        - (x:ℝ) * ∑ r ∈ (Finset.Icc 1 x ×ˢ P) ×ˢ Q,
            ((f r.1.1/(r.1.1:ℝ))
              * (Real.log (r.1.2:ℝ) * f r.1.2
                  / ((r.1.2:ℝ) * Real.log ((x:ℝ)/(r.1.2:ℝ))))
              * (Real.log (r.2:ℝ) * f r.2 / (r.2:ℝ)))
            * V (Real.log (x:ℝ)
              - Real.log (((r.1.1 * r.1.2 * r.2 : ℕ)):ℝ))|
      ≤ 2*(2*ρ*(x:ℝ)*Mass₁ + 4*ρ*(x:ℝ)*Mass₂ + 6*(x:ℝ)*Real.log 4*Mass₂)
        + 2*(x:ℝ)*Real.log 4 := by
  classical
  -- the three intermediate forms
  set B : ℝ := ∑ p ∈ P, (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
      * ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
          * ((((x/(p*q) : ℕ)):ℝ)
            * ∑ n ∈ Finset.Icc 1 x, (f n/(n:ℝ))
                * V (Real.log ((((x/(p*q) : ℕ)):ℝ)) - Real.log (n:ℝ)))
    with hB_def
  set C : ℝ := ∑ p ∈ P, (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
      * ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
          * (((x:ℝ)/((p:ℝ)*(q:ℝ)))
            * ∑ n ∈ Finset.Icc 1 x, (f n/(n:ℝ))
                * V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ)))
    with hC_def
  set D : ℝ := ∑ p ∈ P, (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
      * ∑ q ∈ Q, (Real.log (q:ℝ) * f q)
          * (((x:ℝ)/((p:ℝ)*(q:ℝ)))
            * ∑ n ∈ Finset.Icc 1 x, (f n/(n:ℝ))
                * V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ)))
    with hD_def
  -- the last step is the reindex, exactly
  have hDeq : D = (x:ℝ) * ∑ r ∈ (Finset.Icc 1 x ×ˢ P) ×ˢ Q,
      ((f r.1.1/(r.1.1:ℝ))
        * (Real.log (r.1.2:ℝ) * f r.1.2
            / ((r.1.2:ℝ) * Real.log ((x:ℝ)/(r.1.2:ℝ))))
        * (Real.log (r.2:ℝ) * f r.2 / (r.2:ℝ)))
      * V (Real.log (x:ℝ) - Real.log (((r.1.1 * r.1.2 * r.2 : ℕ)):ℝ)) := by
    rw [hD_def]
    exact ghs_reindex f V x hx (Finset.Icc 1 x) P Q
      (fun n hn => (Finset.mem_Icc.mp hn).1) (fun p hp => (hPp p hp).pos) hQ
  rw [← hDeq]
  -- chain the three differences
  have hAB : |tripleConv f x P - B|
      ≤ 2*ρ*(x:ℝ)*Mass₁ + 4*ρ*(x:ℝ)*Mass₂ + 6*(x:ℝ)*Real.log 4*Mass₂ := by
    rw [hB_def]
    exact tripleConv_sub_smoothed_le f hf x P ρ hρ0 hρ1 hPp h2p V hplat hV0
      hVle hVnn Mass₁ Mass₂ h1 h2
  have hBC : |B - C|
      ≤ 2*ρ*(x:ℝ)*Mass₁ + 4*ρ*(x:ℝ)*Mass₂ + 6*(x:ℝ)*Real.log 4*Mass₂ := by
    have hswap := scale_swap_error_le f hf V ρ hρ0 x P hPp h2p hplat hV0
      hVle hVnn (Finset.Icc 1 x) (fun n hn => (Finset.mem_Icc.mp hn).1)
      Mass₁ Mass₂ h1 h2
    have heq : B - C = ∑ p ∈ P,
        (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
          * ∑ q ∈ (x/p).primesBelow, (Real.log (q:ℝ) * f q)
              * ∑ n ∈ Finset.Icc 1 x, (f n/(n:ℝ))
                  * ((((x/(p*q) : ℕ)):ℝ)
                      * V (Real.log ((((x/(p*q) : ℕ)):ℝ)) - Real.log (n:ℝ))
                    - ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                      * V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                        - Real.log (n:ℝ))) := by
      rw [hB_def, hC_def, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← mul_sub]
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    rw [heq]
    exact hswap
  have hCD : |C - D| ≤ 2*(x:ℝ)*Real.log 4 := by
    have hext := enlargement_extend_le f hf V hV0 hVle hVnn x P hPp h2p
      (Finset.Icc 1 x) (fun n hn => (Finset.mem_Icc.mp hn).1) Q hQp hQsub
    rw [hC_def, hD_def, ← abs_neg]
    simpa [neg_sub] using hext
  calc |tripleConv f x P - D|
      ≤ |tripleConv f x P - B| + |B - D| := abs_sub_le _ _ _
    _ ≤ |tripleConv f x P - B| + (|B - C| + |C - D|) := by
        have := abs_sub_le B C D
        linarith
    _ ≤ 2*(2*ρ*(x:ℝ)*Mass₁ + 4*ρ*(x:ℝ)*Mass₂ + 6*(x:ℝ)*Real.log 4*Mass₂)
        + 2*(x:ℝ)*Real.log 4 := by linarith [hAB, hBC, hCD]

open MeasureTheory Real Complex Finset in
open scoped FourierTransform ContDiff in
/-- **§3's bound on the triple convolution** (Track R, N117):

  `|tripleConv f x P|`
  `  ≤ x·√(E₁·(30·(2M_V + M₂/2π²)·V₃·b² + Mtail))`
  `    + 2·(2ρx·Mass₁ + 4ρx·Mass₂ + 6x·log 4·Mass₂) + 2x·log 4`.

The two halves meet.  `tripleConv_sub_ghs_le` bounds the distance from
`tripleConv` to `x` times §4's sum by the three errors, and
`ghs_smoothed_triple_le_real` bounds that sum by Halász's estimate —
so the triangle inequality finishes it.

This is GHS §3's `S_k` bound with every constant explicit and nothing
assumed: the Perron substitution, the scale swap, the range
enlargement and the reindex are all discharged, and the analytic input
is exactly §4's pairing estimate.

What it is *not* yet is `(3.2)`.  The leading term is `≍ x·L(x)` only
once the window is chosen and `ρ` is fixed — the errors carry
`ρ·x·log x`, and the `Mtail` inside the square root carries `M₃`, so
the two must be balanced against each other.  That balance is the next
step, and it is where the choice of `V` finally gets made. -/
theorem tripleConv_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (V : ℝ → ℝ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (x : ℕ) (hx : 0 < x) (P : Finset ℕ)
    (hPp : ∀ p ∈ P, p.Prime) (h2p : ∀ p ∈ P, 2*p ≤ x)
    (hVs : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (hplat : ∀ v, ρ ≤ v → v ≤ 2*Real.log (x:ℝ) + 1 → V v = Real.exp (-v))
    (hV0 : ∀ v, v ≤ 0 → V v = 0)
    (hVle : ∀ v, V v ≤ Real.exp (-v)) (hVnn : ∀ v, 0 ≤ V v)
    (Q : Finset ℕ) (hQp : ∀ q ∈ Q, q.Prime) (hQ : ∀ q ∈ Q, 0 < q)
    (hQsub : ∀ p ∈ P, (x/p).primesBelow ⊆ Q)
    (Mass₁ Mass₂ : ℝ)
    (h1 : ∑ p ∈ P, Real.log (p:ℝ)/(p:ℝ) ≤ Mass₁)
    (h2 : ∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ)))
      ≤ Mass₂)
    (M₂ M₃ MV : ℝ)
    (hM₂ : ∫ v, |iteratedDeriv 2 V v| ≤ M₂)
    (hM₃ : ∫ v, |iteratedDeriv 3 V v| ≤ M₃)
    (hMV : ∀ ξ, ‖𝓕 (fun v => ((V v : ℝ) : ℂ)) ξ‖ ≤ MV)
    (V₃ Mtail E₁ b : ℝ)
    (hE₁0 : 0 < E₁) (hb0 : 0 ≤ b) (hV₃0 : 0 ≤ V₃) (hMtail0 : 0 < Mtail)
    (hE₁ : (∫ ξ, ‖ghsBlockPoly (fun n => ((f n : ℝ) : ℂ)) x P ξ‖^2
        * ‖𝓕 (fun v => ((V v : ℝ) : ℂ)) ξ‖) ≤ E₁)
    (hBu : ∀ t : ℝ,
      ‖ghsMainPoly (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 x) t‖ ≤ b)
    (hV : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2),
        ‖ghsPrimePoly (fun n => ((f n : ℝ) : ℂ)) Q t‖^2) ≤ V₃)
    (hMtail : (∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ))^2
        * (∑ n ∈ Finset.Icc 1 x, (1:ℝ)/(n:ℝ))^2
        * (M₃/(8*Real.pi^3*(((halaszM x : ℕ):ℝ) + 1/2)^2)) ≤ Mtail) :
    |tripleConv f x P|
      ≤ (x:ℝ) * Real.sqrt (E₁ * (5 * (2*MV + M₂/(2*Real.pi^2)) * V₃ * (6*b^2)
            + Mtail))
        + (2*(2*ρ*(x:ℝ)*Mass₁ + 4*ρ*(x:ℝ)*Mass₂
              + 6*(x:ℝ)*Real.log 4*Mass₂)
          + 2*(x:ℝ)*Real.log 4) := by
  classical
  set G : ℝ := ∑ r ∈ (Finset.Icc 1 x ×ˢ P) ×ˢ Q,
      ((f r.1.1/(r.1.1:ℝ))
        * (Real.log (r.1.2:ℝ) * f r.1.2
            / ((r.1.2:ℝ) * Real.log ((x:ℝ)/(r.1.2:ℝ))))
        * (Real.log (r.2:ℝ) * f r.2 / (r.2:ℝ)))
      * V (Real.log (x:ℝ) - Real.log (((r.1.1 * r.1.2 * r.2 : ℕ)):ℝ))
    with hG_def
  have hxR : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
  -- the error half
  have herr := tripleConv_sub_ghs_le f hf V ρ hρ0 hρ1 x hx P hPp h2p hplat
    hV0 hVle hVnn Q hQp hQ hQsub Mass₁ Mass₂ h1 h2
  rw [← hG_def] at herr
  -- §4's estimate on the sum itself
  have hmain : |G| ≤ Real.sqrt (E₁ * (5 * (2*MV + M₂/(2*Real.pi^2)) * V₃
      * (6*b^2) + Mtail)) := by
    rw [hG_def]
    exact ghs_smoothed_triple_le_real f hf x (Finset.Icc 1 x) P Q
      (fun n hn => (Finset.mem_Icc.mp hn).1)
      (fun p hp => (hPp p hp).pos) hQ V hVs hVc M₂ M₃ MV hM₂ hM₃ hMV
      V₃ Mtail E₁ b hE₁0 hb0 hV₃0 hMtail0 hE₁ hBu hV hMtail
  -- combine
  have hsplit : |tripleConv f x P|
      ≤ |tripleConv f x P - (x:ℝ) * G| + |(x:ℝ) * G| := by
    calc |tripleConv f x P|
        = |(tripleConv f x P - (x:ℝ) * G) + (x:ℝ) * G| := by ring_nf
      _ ≤ |tripleConv f x P - (x:ℝ) * G| + |(x:ℝ) * G| := abs_add_le _ _
  have hxG : |(x:ℝ) * G| ≤ (x:ℝ) * Real.sqrt (E₁
      * (5 * (2*MV + M₂/(2*Real.pi^2)) * V₃ * (6*b^2) + Mtail)) := by
    rw [abs_mul, abs_of_nonneg hxR]
    exact mul_le_mul_of_nonneg_left hmain hxR
  linarith [hsplit, herr, hxG]

open Real Finset in
/-- **The discarded blocks cost `e^{−K}·x·log x`** (Track R, N118):
for any family of block-supported prime sets,

  `∑_{k = K+1}^{M} |tripleConv f x (P k)|`
  `  ≤ x·(16(e−1)·e^{−K}·log x + (M−K)·(16 log 2 + 16 log 4))`.

The half of §3's `k`-split that needs no analysis.  Each block is
bounded trivially by `tripleConv_block_le'`, whose leading term
`16(e−1)e^{−k}·x·log x` is geometric in `k`; `sum_exp_neg_tail_le`
collapses the tail to `e^{−K}`.

So all blocks past `K` together contribute `≍ e^{−K}·x·log x`, and at
`K = log(100 log x/L)` that is `x·L/100` — the shape `(3.2)` allows.
The remaining `O(1)` per block is what forces `K` to be counted: the
additive `16 log 2 + 16 log 4` does not decay, so the split has to be
made at a `K` that is `O(log(log x/L))`, not merely large.

Stated with the block count `M − K` explicit rather than absorbed, so
that the caller can see exactly what the non-decaying part costs. -/
theorem tripleConv_tail_blocks_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (x : ℕ) (hx : 2 ≤ x) (K M : ℕ) (Pk : ℕ → Finset ℕ)
    (hk1 : ∀ k ∈ Finset.Icc (K+1) M, 1 ≤ k)
    (hfit : ∀ k ∈ Finset.Icc (K+1) M, 2 * blockHi x k ≤ x)
    (hP : ∀ k ∈ Finset.Icc (K+1) M, ∀ p ∈ Pk k,
      p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k) :
    ∑ k ∈ Finset.Icc (K+1) M, |tripleConv f x (Pk k)|
      ≤ (x:ℝ) * (16 * (Real.exp 1 - 1) * Real.exp (-(K:ℝ)) * Real.log (x:ℝ))
        + ((Finset.Icc (K+1) M).card : ℝ)
            * ((x:ℝ) * (16 * Real.log 2 + 16 * Real.log 4)) := by
  classical
  have hx0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
  -- termwise: the trivial block bound
  have hterm : ∀ k ∈ Finset.Icc (K+1) M, |tripleConv f x (Pk k)|
      ≤ (x:ℝ) * (16 * (Real.exp 1 - 1) * Real.log (x:ℝ))
          * Real.exp (-(k:ℝ))
        + (x:ℝ) * (16 * Real.log 2 + 16 * Real.log 4) := by
    intro k hk
    refine le_trans (tripleConv_block_le' f hf x k hx (hk1 k hk) (hfit k hk)
      (Pk k) (hP k hk)) ?_
    have hexp : (0:ℝ) ≤ Real.exp (-(k:ℝ)) := (Real.exp_pos _).le
    nlinarith [hx0, hexp]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  -- the geometric tail
  have hgeo := sum_exp_neg_tail_le K M
  have hcoef : (0:ℝ) ≤ (x:ℝ) * (16 * (Real.exp 1 - 1) * Real.log (x:ℝ)) := by
    have h1 : (0:ℝ) ≤ Real.log (x:ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
    have h2 : (0:ℝ) ≤ Real.exp 1 - 1 := by
      have := Real.add_one_le_exp (1:ℝ)
      linarith
    positivity
  have hmain : (x:ℝ) * (16 * (Real.exp 1 - 1) * Real.log (x:ℝ))
      * (∑ k ∈ Finset.Icc (K+1) M, Real.exp (-(k:ℝ)))
      ≤ (x:ℝ) * (16 * (Real.exp 1 - 1) * Real.exp (-(K:ℝ))
          * Real.log (x:ℝ)) := by
    refine le_trans (mul_le_mul_of_nonneg_left hgeo hcoef) (le_of_eq ?_)
    ring
  simp only [Finset.sum_const, nsmul_eq_mul]
  linarith [hmain]

open Real Finset in
/-- **The fit condition caps the block index** (Track R, N119): if
`2·blockHi x k ≤ x` and `x ≥ 2` then

  `log 2 ≤ e^{−k}·log x`,

i.e. `e^k ≤ log x/log 2`, so `k ≤ log(log x/log 2) ≍ log log x`.

This is what bounds the *number* of blocks, and the count matters:
`tripleConv_tail_blocks_le` carries a non-decaying `O(1)` per block, so
the trivial half of §3's `k`-split costs `(#blocks)·x·O(1)`.  Were the
decomposition to run to `k ≍ log x` that would be `x·log x` and `(3.2)`
would fail.

It does not, and the reason is already in the hypothesis rather than in
any extra argument: `blockHi x k = ⌈x^{1−e^{−k}}⌉ ≥ x^{1−e^{−k}}`, so
`2·blockHi ≤ x` forces `2 ≤ x^{e^{−k}}`.  The blocks that satisfy the
fit condition are exactly those with `e^k ≲ log x`, of which there are
`≍ log log x`.

That `x·log log x` is not slack either — it is precisely the second
term of GHS's Theorem 1, `x·loglog x/log x` after the outer weight. -/
theorem block_index_le_of_fit (x k : ℕ) (hx : 2 ≤ x)
    (hfit : 2 * blockHi x k ≤ x) :
    Real.log 2 ≤ Real.exp (-(k:ℝ)) * Real.log (x:ℝ) := by
  have hx1 : (1:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hx0 : (0:ℝ) < (x:ℝ) := by linarith
  have hlogx : (0:ℝ) < Real.log (x:ℝ) := Real.log_pos hx1
  -- the ceiling dominates the power
  have hceil : (x:ℝ) ^ (1 - Real.exp (-(k:ℝ))) ≤ ((blockHi x k : ℕ):ℝ) := by
    rw [blockHi]
    exact Nat.le_ceil _
  have hfitR : 2 * ((blockHi x k : ℕ):ℝ) ≤ (x:ℝ) := by
    have : ((2 * blockHi x k : ℕ):ℝ) ≤ ((x:ℕ):ℝ) := by exact_mod_cast hfit
    push_cast at this
    linarith
  -- so `2·x^{1−e^{−k}} ≤ x`, i.e. `2 ≤ x^{e^{−k}}`
  have hstep : 2 * (x:ℝ) ^ (1 - Real.exp (-(k:ℝ))) ≤ (x:ℝ) := by
    linarith [hceil, hfitR]
  have hsplit : (x:ℝ) = (x:ℝ) ^ (1 - Real.exp (-(k:ℝ)))
      * (x:ℝ) ^ (Real.exp (-(k:ℝ))) := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hpow0 : (0:ℝ) < (x:ℝ) ^ (1 - Real.exp (-(k:ℝ))) :=
    Real.rpow_pos_of_pos hx0 _
  have hge : (2:ℝ) ≤ (x:ℝ) ^ (Real.exp (-(k:ℝ))) := by
    rw [hsplit] at hstep
    nlinarith [hstep, hpow0]
  -- take logs
  have hlog := Real.log_le_log (by norm_num) hge
  rw [Real.log_rpow hx0] at hlog
  linarith

open Real Finset in
/-- **§3's `k`-split** (Track R, N120): if every block up to `K` obeys
the analytic bound `A` and the blocks past `K` obey the trivial one,

  `∑_{k ∈ [1, M]} |tripleConv f x (P k)| ≤ (K:ℝ)·A + T`,

where `T` is `tripleConv_tail_blocks_le`'s bound.

The split itself, stated with both halves as parameters.  Splitting
`Icc 1 M` at `K` is `Finset.sum_Icc_consecutive`-style bookkeeping; what
matters is that the two halves are bounded by different mechanisms —
the head by §4's pairing estimate through `tripleConv_le`, the tail by
the geometric trivial bound — and that neither is assumed of the other.

Left parametric in `A` deliberately.  `tripleConv_le` still carries the
window `V` and the Perron parameter `ρ` as free choices, and the whole
point of the design has been to strike that balance once, in the open,
rather than bake it into the split.  Substituting the concrete `A` is
the next step, and it is where `V` finally gets chosen. -/
theorem tripleConv_ksplit_le (f : ℕ → ℝ) (x : ℕ) (K M : ℕ) (hKM : K ≤ M)
    (Pk : ℕ → Finset ℕ) (A T : ℝ)
    (hhead : ∀ k ∈ Finset.Icc 1 K, |tripleConv f x (Pk k)| ≤ A)
    (htail : ∑ k ∈ Finset.Icc (K+1) M, |tripleConv f x (Pk k)| ≤ T) :
    ∑ k ∈ Finset.Icc 1 M, |tripleConv f x (Pk k)| ≤ (K:ℝ) * A + T := by
  classical
  -- split the index range at `K`
  have hsplit : Finset.Icc 1 M
      = Finset.Icc 1 K ∪ Finset.Icc (K+1) M := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 K) (Finset.Icc (K+1) M) := by
    refine Finset.disjoint_left.mpr fun k hk1 hk2 => ?_
    rw [Finset.mem_Icc] at hk1 hk2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  -- the head: at most `K` terms, each at most `A`
  have hhead' : ∑ k ∈ Finset.Icc 1 K, |tripleConv f x (Pk k)| ≤ (K:ℝ) * A := by
    refine le_trans (Finset.sum_le_sum hhead) ?_
    simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
    have hcard : ((K + 1 - 1 : ℕ):ℝ) = (K:ℝ) := by
      simp
    rw [hcard]
  linarith [hhead', htail]

open Real Finset ArithmeticFunction in
/-- **The Gaussian pair sum over a prime set** (Track R, N133): if every
element of `S` is prime then

  `∑_{n∈S} Λ(n)·e^{−πT²(log n − log m)²} ≤ 1024·h·L + log m + e^{−πT²/64}·B`,

with **no `√X` term**.

`vonMangoldt_gaussian_long_le` carries an extra
`(√X+1)·log₂X·log X`, which bounds the *proper prime power* branch of
`sum_vonMangoldt_split`.  On a set of primes that branch is empty, so
the term is not merely small — it is identically zero.

This matters because the term is additive in the bracket and therefore
gets multiplied by `∑_m ‖a_m‖²Λ(m)` when the mean value theorem is
applied.  For §4's polynomials the coefficients decay like `log q/q`,
so that sum is `O(1)` while the intended main term is `≍ log⁴X`; a
`√X·log²X` additive error then dominates by `≍ √X/log²X` and the bound
says nothing.  `P₂` and `P₃` are prime-supported, so restricting here
removes it at no cost.

The `X` parameter disappears entirely, which is the point: the bound no
longer degrades with the *range*, only with the coefficients. -/
theorem vonMangoldt_gaussian_prime_le (T : ℝ) (m h J : ℕ) (S : Finset ℕ)
    (hSp : ∀ n ∈ S, n.Prime) (hS1 : ∀ n ∈ S, 1 ≤ n) (hm1 : 1 ≤ m)
    (hh : 2 ≤ h) (hscale : 2*(m:ℝ) ≤ (h:ℝ)*T)
    (hfit : (2^J - 1)*h + 1 ≤ m) (hwfit : ∀ j < J, 2^j*h ≤ 2*m)
    (hreach : m ≤ 4*((2^J - 1)*h))
    (L : ℝ) (hL : Real.log (4*(m:ℝ)+2)/Real.log ((h:ℕ):ℝ) ≤ L)
    (B : ℝ) (hB : ∑ n ∈ S, Real.log (n:ℝ) ≤ B) :
    ∑ n ∈ S, vonMangoldt n
        * Real.exp (-(π*T^2*(Real.log (n:ℝ) - Real.log (m:ℝ))^2))
      ≤ 1024*(h:ℝ)*L + Real.log (m:ℝ) + Real.exp (-(π*T^2/64)) * B := by
  classical
  -- on a prime set the filter is everything, and `Λ = log`
  have hfil : S.filter Nat.Prime = S := Finset.filter_true_of_mem hSp
  have hrw : ∑ n ∈ S, vonMangoldt n
      * Real.exp (-(π*T^2*(Real.log (n:ℝ) - Real.log (m:ℝ))^2))
      = ∑ p ∈ S.filter Nat.Prime,
          Real.log p * Real.exp (-(π*T^2*(Real.log p - Real.log m)^2)) := by
    rw [hfil]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [ArithmeticFunction.vonMangoldt_apply_prime (hSp n hn)]
  rw [hrw]
  exact ExpSums.prime_gaussian_long_le T m h J S hS1 hm1 hh hscale hfit
    hwfit hreach L hL B hB

open Real Finset ArithmeticFunction in
/-- **The inner pair sum over a prime set** (Track R, N134): for `S` a
set of primes and `T² ≤ m`,

  `∑_{n∈S} Λ(n)·e^{−πT²(log n − log m)²}
     ≤ 6144·⌈2m/T⌉ + log m + e^{−πT²/64}·B`.

`inner_sum_long_le` with the `√X` term removed, by
`vonMangoldt_gaussian_prime_le`.  The shell construction is unchanged —
only the prime-power branch it never needed is gone.

Two consequences for the mean value theorem this feeds:

* the bound no longer mentions the *range* `X` at all, so it does not
  degrade as the prime set grows;
* the only surviving additive term is `e^{−πT²/64}·B`, and that one is
  killed by taking `T` large rather than fixed — at `T ≍ √(log X)` it
  is `O(1)` while the leading `6144·⌈2m/T⌉` still gives `≍ m` after the
  mean value theorem's factor `T`, since `T·⌈2m/T⌉ ≍ m` is
  `T`-independent.

That second point is what the original `T = 8` choice missed: `T` was
fixed at the smallest value satisfying the shell conditions, on the
grounds that larger `T` only raises the threshold `T² ≤ m`.  It also
damps `B`, which is the difference between a usable bound and a
vacuous one. -/
theorem inner_sum_prime_le (T : ℝ) (m : ℕ) (S : Finset ℕ)
    (hSp : ∀ n ∈ S, n.Prime) (hS1 : ∀ n ∈ S, 1 ≤ n)
    (hT : 2 ≤ T) (hTm : T^2 ≤ (m:ℝ))
    (hsmall : 2*(⌈2*(m:ℝ)/T⌉₊) ≤ m)
    (B : ℝ) (hB : ∑ n ∈ S, Real.log (n:ℝ) ≤ B) :
    ∑ n ∈ S, vonMangoldt n
        * Real.exp (-(π*T^2*(Real.log (m:ℝ) - Real.log (n:ℝ))^2))
      ≤ 6144*((⌈2*(m:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log (m:ℝ)
        + Real.exp (-(π*T^2/64)) * B := by
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
  obtain ⟨J, hfit, hmax, hwfit⟩ :=
    ExpSums.exists_shell_count m h hm1 (by omega)
  have hsucc : (2^(J+1) - 1)*h = (2^J - 1)*h + 2^J*h :=
    ExpSums.dyadic_cut_succ h J
  have hJh : (2:ℕ)^J*h = (2^J - 1)*h + h := by
    have h1 : (1:ℕ) ≤ 2^J := Nat.one_le_two_pow
    have h2 : (2:ℕ)^J = (2^J - 1) + 1 := by omega
    calc (2:ℕ)^J*h = ((2^J - 1) + 1)*h := by rw [← h2]
      _ = (2^J - 1)*h + h := by ring
  have hreach : m ≤ 4*((2^J - 1)*h) := by omega
  -- the pair sum, with the arguments in the order the prime lemma wants
  have hsym : ∀ n : ℕ, Real.exp (-(π*T^2*(Real.log (m:ℝ) - Real.log (n:ℝ))^2))
      = Real.exp (-(π*T^2*(Real.log (n:ℝ) - Real.log (m:ℝ))^2)) := by
    intro n
    congr 2
    ring
  simp only [hsym]
  refine le_trans (vonMangoldt_gaussian_prime_le T m h J S hSp hS1 hm1 hh2
    hscale hfit hwfit hreach 6 hL B hB) ?_
  have hh0 : (0:ℝ) ≤ (h:ℝ) := Nat.cast_nonneg _
  have hcalc : 1024*(h:ℝ)*6 = 6144*(h:ℝ) := by ring
  linarith [hcalc]

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **GHS Lemma 1 on a prime set, at any `T`** (Track R, N135): for `S`
a set of primes with `T² ≤ m` throughout,

  `∫_{−T}^{T}‖∑ a(n)Λ(n)·𝐞(−ξ log n)‖² dξ
     ≤ e^π·T·∑_m (6144·⌈2m/T⌉ + log m + e^{−πT²/64}·B)·‖a(m)‖²·Λ(m)`.

`intervalIntegral_vonMangoldt_mvt_long_le` with the `√X` term gone
(`inner_sum_prime_le`) and `T` left free rather than instantiated at
`8`.

**Both changes matter, and the second only became visible once the
first was made.**  The leading term is `T·⌈2m/T⌉ ≍ m`, *independent of
`T`* — so raising `T` costs nothing on the main term while damping
`e^{−πT²/64}·B` exponentially.  With `B ≥ ∑_{q≤X} log q ≍ X` and
`T = 8` the damping factor is only `e^{−π} ≈ 0.043`, leaving `≍ X`;
at `T ≍ √(log X)` it is `O(1)`.

The price is the threshold `T² ≤ m`, which discards primes below
`≍ log X`.  Against §4's coefficients their mass is `≍ log⁴log X`,
negligible beside the `≍ log⁴X` main term.

This is the statement §4 should have been using: no `X`-dependence, and
the one remaining additive term under the caller's control. -/
theorem intervalIntegral_vonMangoldt_mvt_prime_le (T : ℝ)
    (S : Finset ℕ) (a : ℕ → ℂ)
    (hSp : ∀ n ∈ S, n.Prime) (hS1 : ∀ n ∈ S, 1 ≤ n)
    (hT : 2 ≤ T) (hTm : ∀ m ∈ S, T^2 ≤ (m:ℝ))
    (hsmall : ∀ m ∈ S, 2*(⌈2*(m:ℝ)/T⌉₊) ≤ m)
    (B : ℝ) (hB : ∑ n ∈ S, Real.log (n:ℝ) ≤ B) :
    (∫ ξ in (-T)..T, ‖∑ n ∈ S, (a n * ((vonMangoldt n : ℝ) : ℂ))
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
      ≤ Real.exp π * T * ∑ m ∈ S,
          (6144*((⌈2*(m:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log (m:ℝ)
            + Real.exp (-(π*T^2/64)) * B)
          * (‖a m‖^2 * vonMangoldt m) := by
  refine intervalIntegral_vonMangoldt_mvt_pointwise_le T (by linarith) S a _ ?_
  intro m hm
  exact inner_sum_prime_le T m S hSp hS1 hT (hTm m hm) (hsmall m hm) B hB

open Real Finset in
/-- **The smallness condition follows from the threshold** (Track R,
N136): for `5 ≤ T` and `T² ≤ m`,

  `2·⌈2m/T⌉ ≤ m`.

`two_mul_ceil_quarter_le` proves this at `T = 8` from `4 ≤ m`; at
general `T` the threshold `T² ≤ m` already gives it, so the mean value
theorem's two side conditions collapse into one.

The computation: `2⌈2m/T⌉ ≤ 4m/T + 2 ≤ m` iff `m(T−4)/T ≥ 2`, and
`m ≥ T²` makes the left side at least `T(T−4)`, which exceeds `2` from
`T ≥ 5` on.

This is what lets `T` be raised without carrying a second hypothesis.
It matters because raising `T` is the fix for the mean value theorem's
`e^{−πT²/64}·B` term — free on the main term, since `T·⌈2m/T⌉ ≍ m` —
and a `T`-dependent smallness condition would have made that
re-parametrisation cost a lemma at every call site. -/
theorem two_mul_ceil_scale_le_of_sq_le (T : ℝ) (m : ℕ) (hT : 5 ≤ T)
    (hTm : T^2 ≤ (m:ℝ)) :
    2*(⌈2*(m:ℝ)/T⌉₊) ≤ m := by
  have hT0 : (0:ℝ) < T := by linarith
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg _
  -- `m ≥ T²  ⟹  m ≥ 25`
  have hm25 : (25:ℝ) ≤ (m:ℝ) := by nlinarith [hTm, hT]
  -- name the quotient: `linarith` will not identify `4m/T` with `2*(2m/T)`
  set u : ℝ := (m:ℝ)/T with hu_def
  have h2u : 2*(m:ℝ)/T = 2*u := by rw [hu_def]; ring
  have h4u : 4*(m:ℝ)/T = 4*u := by rw [hu_def]; ring
  have hceil : ((⌈2*(m:ℝ)/T⌉₊ : ℕ):ℝ) < 2*u + 1 := by
    rw [← h2u]
    exact Nat.ceil_lt_add_one (by positivity)
  -- `4u + 2 ≤ m` since `m(T−4) ≥ T²(T−4) ≥ 2T`
  have hkey : 4*u + 2 ≤ (m:ℝ) := by
    rw [← h4u, div_add' _ _ _ (ne_of_gt hT0), div_le_iff₀ hT0]
    nlinarith [hTm, hT, hm25, hT0]
  have hreal : ((2*(⌈2*(m:ℝ)/T⌉₊) : ℕ):ℝ) ≤ (m:ℝ) := by
    push_cast
    linarith [hceil, hkey]
  exact_mod_cast hreal

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **The centred energy of the `q`-polynomial, at free `T`** (Track R,
N137): for `Q` a set of primes with `T² ≤ q` throughout,

  `∫_{−T}^{T}‖∑_q w(q)·𝐞(−u log q)‖² du
     ≤ e^π·T·∑_q (6144·⌈2q/T⌉ + log q + e^{−πT²/64}·B)·(log q/q²)`.

`ghsPrime_centred_energy_le` re-derived through
`intervalIntegral_vonMangoldt_mvt_prime_le`, with **no `√X` term** and
`T` left free.

The two changes are what make the bound say something.  Summed against
`∑_q log q/q² = O(1)`, the old `(√X+1)log₂X·logX` contributed
`≍ √X·log²X` and `e^{−π}·B` contributed `≍ X`, while the intended main
term is `≍ log X` — so the old statement was true but vacuous.  Here
the first is gone identically, and the second is `e^{−πT²/64}·B`, which
the caller kills by taking `T ≍ √(log X)`.

`T` does not appear in the leading term's size: `T·⌈2q/T⌉ ≍ q`, so the
prefactor `e^π·T` and the `1/T` inside cancel, and the main term stays
`≍ ∑_q log q/q ≍ log X` at every `T`.  Raising `T` is therefore free,
and `two_mul_ceil_scale_le_of_sq_le` supplies the shell condition from
the threshold alone. -/
theorem ghsPrime_centred_energy_free_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (Q : Finset ℕ) (T : ℝ) (hT : 5 ≤ T)
    (hQp : ∀ q ∈ Q, q.Prime) (hQT : ∀ q ∈ Q, T^2 ≤ (q:ℝ))
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∑ q ∈ Q, Real.log (q:ℝ) ≤ B)
    (w : ℕ → ℂ)
    (hw : ∀ q ∈ Q, ‖w q‖ = ‖(((Real.log (q:ℝ) : ℝ):ℂ) * f q) / (q:ℂ)‖) :
    (∫ u in (-T)..T,
        ‖∑ q ∈ Q, w q
          * ((Real.fourierChar (-(Real.log (q:ℝ) * u)) : Circle) : ℂ)‖^2)
      ≤ Real.exp π * T * ∑ q ∈ Q,
          (6144*((⌈2*(q:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log (q:ℝ)
            + Real.exp (-(π*T^2/64)) * B)
          * (Real.log (q:ℝ)/(q:ℝ)^2) := by
  classical
  -- rewrite into von Mangoldt shape
  have hrw : (∫ u in (-T)..T,
      ‖∑ q ∈ Q, w q
        * ((Real.fourierChar (-(Real.log (q:ℝ) * u)) : Circle) : ℂ)‖^2)
      = ∫ u in (-T)..T,
        ‖∑ q ∈ Q, ((w q / ((vonMangoldt q : ℝ):ℂ))
            * ((vonMangoldt q : ℝ):ℂ))
          * ((Real.fourierChar (-(Real.log (q:ℝ) * u)) : Circle) : ℂ)‖^2 := by
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [prime_poly_as_vonMangoldt Q hQp w u]
  rw [hrw]
  -- the mean value theorem, prime-restricted, at this `T`
  have hmvt := intervalIntegral_vonMangoldt_mvt_prime_le T Q
    (fun q => w q / ((vonMangoldt q : ℝ):ℂ)) hQp
    (fun q hq => (hQp q hq).one_lt.le) (by linarith)
    hQT
    (fun m hm => two_mul_ceil_scale_le_of_sq_le T m hT (hQT m hm))
    B hB
  refine le_trans hmvt ?_
  -- replace the coefficient energy by its bound
  have hcoef : ∀ q ∈ Q,
      (6144*((⌈2*(q:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log (q:ℝ)
        + Real.exp (-(π*T^2/64)) * B)
      * (‖w q / ((vonMangoldt q : ℝ):ℂ)‖^2 * vonMangoldt q)
      ≤ (6144*((⌈2*(q:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log (q:ℝ)
          + Real.exp (-(π*T^2/64)) * B)
        * (Real.log (q:ℝ)/(q:ℝ)^2) := by
    intro q hq
    have hbig : (0:ℝ) ≤ 6144*((⌈2*(q:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log (q:ℝ)
        + Real.exp (-(π*T^2/64)) * B := by
      have h1 : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_natCast_nonneg q
      have h2 : (0:ℝ) ≤ Real.exp (-(π*T^2/64)) * B :=
        mul_nonneg (Real.exp_pos _).le hB0
      positivity
    refine mul_le_mul_of_nonneg_left ?_ hbig
    exact recovered_coeff_sq_le f hf q (hQp q hq) (w q) (hw q hq)
  have hstep := Finset.sum_le_sum hcoef
  have hexp0 : (0:ℝ) ≤ Real.exp π * T := by positivity
  exact mul_le_mul_of_nonneg_left hstep hexp0

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **The per-frequency energy of `P₃`, at free `T`** (Track R, N140):
for every frequency `N`, with `Q` a set of primes and `T² ≤ q`
throughout,

  `∫_{N−1/2}^{N+1/2} ‖P₃(t)‖² dt
     ≤ e^π·T·∑_q (6144·⌈2q/T⌉ + log q + e^{−πT²/64}·B)·(log q/q²)`.

`ghsPrimePoly_unit_energy_le` re-derived through
`ghsPrime_centred_energy_free_le`.  The three-step structure is
unchanged — `integral_unit_sq_le_of_centred` moves `N` to the origin,
`integral_symm_widen` opens `[−1/2, 1/2]` to `[−T, T]`, the centred
estimate closes it — and `integral_symm_widen` never cared what `T`
was, only that `1/2 ≤ T`, which `5 ≤ T` gives.

This is the `V₃` half of the repair.  With the `√X` term gone and `T`
free, `V₃ ≍ ∑_q log q/q ≍ log X` at `T ≍ √(log X)` — the magnitude
`ghsPrimePoly_unit_energy_le`'s docstring claimed but did not
deliver. -/
theorem ghsPrimePoly_unit_energy_free_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (Q : Finset ℕ) (T : ℝ) (hT : 5 ≤ T)
    (hQp : ∀ q ∈ Q, q.Prime) (hQT : ∀ q ∈ Q, T^2 ≤ (q:ℝ))
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∑ q ∈ Q, Real.log (q:ℝ) ≤ B)
    (hwide : ∀ w : ℕ → ℂ, IntervalIntegrable
      (fun u => ‖∑ q ∈ Q, w q
        * ((Real.fourierChar (-(Real.log (q:ℝ) * u)) : Circle) : ℂ)‖^2)
      volume (-T) T)
    (N : ℝ) :
    (∫ t in (N - 1/2)..(N + 1/2), ‖ghsPrimePoly f Q t‖^2)
      ≤ Real.exp π * T * ∑ q ∈ Q,
          (6144*((⌈2*(q:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log (q:ℝ)
            + Real.exp (-(π*T^2/64)) * B)
          * (Real.log (q:ℝ)/(q:ℝ)^2) := by
  classical
  set V : ℝ := Real.exp π * T * ∑ q ∈ Q,
      (6144*((⌈2*(q:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log (q:ℝ)
        + Real.exp (-(π*T^2/64)) * B)
      * (Real.log (q:ℝ)/(q:ℝ)^2) with hV_def
  set c : ℕ → ℂ := fun q =>
    (((Real.log (q:ℝ) : ℝ):ℂ) * f q) / (q:ℂ) with hc_def
  have hpoly : ∀ t : ℝ, ghsPrimePoly f Q t
      = ∑ q ∈ Q, c q
        * ((Real.fourierChar (-(Real.log (q:ℝ) * t)) : Circle) : ℂ) := by
    intro t
    rw [ghsPrimePoly]
  simp only [hpoly]
  refine ExpSums.integral_unit_sq_le_of_centred Q c
    (fun q => Real.log (q:ℝ)) V ?_ N
  intro w' hw'
  have hb : (-(1:ℝ)/2) = -((1:ℝ)/2) := by ring
  rw [hb]
  refine le_trans (integral_symm_widen
    (fun u => ‖∑ q ∈ Q, w' q
      * ((Real.fourierChar (-(Real.log (q:ℝ) * u)) : Circle) : ℂ)‖^2)
    (fun t => by positivity) ((1:ℝ)/2) T (by norm_num) (by linarith)
    (hwide w')) ?_
  exact ghsPrime_centred_energy_free_le f hf Q T hT hQp hQT B hB0 hB w'
    (fun q _ => hw' q)

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **The band energy of `P_k` at free `T`** (Track R, N138): for `P` a
set of primes with `T² ≤ p` throughout and `2p ≤ x`,

  `∫_{−T}^{T}‖P₂(ξ)‖² dξ
     ≤ e^π·T·∑_p (6144·⌈2p/T⌉ + log p + e^{−πT²/64}·B)
              ·(log p/(p²·log²(x/p)))`.

The `E₁` counterpart of `ghsPrime_centred_energy_free_le`: GHS's
Lemma 1 applied to `P₂` through the prime-restricted mean value theorem,
with no `√X` term and `T` free.

Same repair, same reason.  Against `∑_p log p/(p²log²(x/p)) = O(1)` the
old statement's `√X`- and `B`-terms contributed `≍ √X log²X` and `≍ X`
while the intended main term is `≍ e^{k}/log x`, so `ghsBlock_E1_le`'s
docstring claim was not what the formal bound gave.  With both removed,
`E₁ ≍ e^{k}/log x` is what the statement actually delivers at
`T ≍ √(log X)`.

`P₂` is prime-supported for the same reason `P₃` is — the block is a
set of primes — so the restriction costs nothing here either. -/
theorem ghsBlock_centred_energy_free_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x : ℕ) (P : Finset ℕ) (T : ℝ) (hT : 5 ≤ T)
    (hPp : ∀ p ∈ P, p.Prime) (hPT : ∀ p ∈ P, T^2 ≤ (p:ℝ))
    (h2p : ∀ p ∈ P, 2*p ≤ x)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∑ p ∈ P, Real.log (p:ℝ) ≤ B) :
    (∫ ξ in (-T)..T, ‖ghsBlockPoly f x P ξ‖^2)
      ≤ Real.exp π * T * ∑ p ∈ P,
          (6144*((⌈2*(p:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log (p:ℝ)
            + Real.exp (-(π*T^2/64)) * B)
          * (Real.log (p:ℝ)/((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2)) := by
  classical
  -- rewrite into von Mangoldt shape
  have hrw : (∫ ξ in (-T)..T, ‖ghsBlockPoly f x P ξ‖^2)
      = ∫ ξ in (-T)..T,
        ‖∑ p ∈ P, ((f p / ((p:ℂ) * ((Real.log ((x:ℝ)/(p:ℝ)) : ℝ):ℂ)))
            * ((vonMangoldt p : ℝ):ℂ))
          * ((Real.fourierChar (-(Real.log (p:ℝ) * ξ)) : Circle) : ℂ)‖^2 := by
    refine intervalIntegral.integral_congr fun ξ _ => ?_
    rw [ghsBlockPoly_eq_vonMangoldt_poly f x P hPp ξ]
  rw [hrw]
  -- the prime-restricted mean value theorem at this `T`
  have hmvt := intervalIntegral_vonMangoldt_mvt_prime_le T P
    (fun p => f p / ((p:ℂ) * ((Real.log ((x:ℝ)/(p:ℝ)) : ℝ):ℂ))) hPp
    (fun p hp => (hPp p hp).one_lt.le) (by linarith)
    hPT
    (fun m hm => two_mul_ceil_scale_le_of_sq_le T m hT (hPT m hm))
    B hB
  refine le_trans hmvt ?_
  -- replace the coefficient energy by its bound
  have hcoef : ∀ p ∈ P,
      (6144*((⌈2*(p:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log (p:ℝ)
        + Real.exp (-(π*T^2/64)) * B)
      * (‖f p / ((p:ℂ) * ((Real.log ((x:ℝ)/(p:ℝ)) : ℝ):ℂ))‖^2 * vonMangoldt p)
      ≤ (6144*((⌈2*(p:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log (p:ℝ)
          + Real.exp (-(π*T^2/64)) * B)
        * (Real.log (p:ℝ)/((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2)) := by
    intro p hp
    have hbig : (0:ℝ) ≤ 6144*((⌈2*(p:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log (p:ℝ)
        + Real.exp (-(π*T^2/64)) * B := by
      have h1 : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
      have h2 : (0:ℝ) ≤ Real.exp (-(π*T^2/64)) * B :=
        mul_nonneg (Real.exp_pos _).le hB0
      positivity
    refine mul_le_mul_of_nonneg_left ?_ hbig
    exact norm_ghsBlock_coeff_sq_le f hf x p (hPp p hp) (h2p p hp)
  have hstep := Finset.sum_le_sum hcoef
  have hexp0 : (0:ℝ) ≤ Real.exp π * T := by positivity
  exact mul_le_mul_of_nonneg_left hstep hexp0

open Real in
/-- **The mean value theorem's summand, at free `T`** (Track R, N142):
for `2 ≤ q`, `0 < T`, any `R`, and any weight `D ≥ 0`,

  `(6144·⌈2q/T⌉ + log q + R)·(log q/(q²D))
     ≤ (12288/T)·(log q/(qD)) + (6144 + R + log q)·(log q/(q²D))`.

`ghsPrime_mvt_summand_le` and `ghsBlock_mvt_summand_le` at once, with
`8` replaced by a free `T`.  The single change is arithmetic:
`⌈2q/T⌉ ≤ 2q/T + 1`, so the leading constant is `6144·2/T = 12288/T`
rather than the `1536` that `T = 8` produced.

That `1/T` is the whole reason raising `T` is free.  The mean value
theorem carries a prefactor `T`, so `T·(12288/T) = 12288` — the leading
term does not move.  The additive `e^{−πT²/64}·B`, which is what forced
this repair, is damped by `T` with nothing to pay for it.

`D` is carried as a parameter so that both call sites use this: `D = 1`
for `P₃`'s `log q/q²`, and `D = log²(x/p)` for `P₂`'s. -/
theorem mvt_summand_free_le (q : ℕ) (hq : 2 ≤ q) (T : ℝ) (hT : 0 < T)
    (R D : ℝ) (hD : 0 ≤ D) :
    (6144*((⌈2*(q:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log (q:ℝ) + R)
        * (Real.log (q:ℝ)/((q:ℝ)^2 * D))
      ≤ (12288/T) * (Real.log (q:ℝ)/((q:ℝ) * D))
        + (6144 + R + Real.log (q:ℝ)) * (Real.log (q:ℝ)/((q:ℝ)^2 * D)) := by
  have hq0 : (0:ℝ) < (q:ℝ) := by
    have : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    linarith
  have hlog0 : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_natCast_nonneg q
  -- the ceiling is at most `2q/T + 1`
  have hceil : ((⌈2*(q:ℝ)/T⌉₊ : ℕ):ℝ) ≤ 2*(q:ℝ)/T + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hmass : (0:ℝ) ≤ Real.log (q:ℝ)/((q:ℝ)^2 * D) := by positivity
  -- the leading piece, where the `1/T` and one power of `q` cancel
  have hlead : 6144*((⌈2*(q:ℝ)/T⌉₊ : ℕ):ℝ)
        * (Real.log (q:ℝ)/((q:ℝ)^2 * D))
      ≤ (12288/T) * (Real.log (q:ℝ)/((q:ℝ) * D))
        + 6144 * (Real.log (q:ℝ)/((q:ℝ)^2 * D)) := by
    have hstep : 6144*((⌈2*(q:ℝ)/T⌉₊ : ℕ):ℝ)
          * (Real.log (q:ℝ)/((q:ℝ)^2 * D))
        ≤ 6144*(2*(q:ℝ)/T + 1) * (Real.log (q:ℝ)/((q:ℝ)^2 * D)) := by
      refine mul_le_mul_of_nonneg_right ?_ hmass
      linarith [hceil]
    refine le_trans hstep (le_of_eq ?_)
    rcases eq_or_lt_of_le hD with hD0 | hDpos
    · simp [← hD0]
    · field_simp
      ring
  nlinarith [hlead, hmass, hlog0]

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **`E₁`, the whole-line weighted energy of `P_k`, at free `T`**
(Track R, N141): with `S := ∑_p log p/(p·|log(x/p)|)` the trivial sup
of `P₂`,

  `∫_ℝ ‖P₂(ξ)‖²·w(ξ) dξ
     ≤ C·e^π·T·∑_p (6144·⌈2p/T⌉ + log p + e^{−πT²/64}·B)
              ·(log p/(p²·log²(x/p)))
       + S²·Wtail`.

`ghsBlock_weighted_energy_le` re-derived through
`ghsBlock_centred_energy_free_le`.  `integral_sq_weight_le` was already
stated at a free band width, so the split needs nothing new: only the
band estimate changes.

The band width now carries the threshold `T² ≤ p`, which is why `hP64`
is gone — `64 ≤ p` was exactly that condition frozen at `T = 8`, and
at free `T` the caller supplies it directly.  `X` disappears with the
`√X` term it existed to name.

The `Wtail` hypothesis moves with the band: the tail mass is measured
beyond `T`, not beyond `8`.  For a normalised window that mass is
`O(1/T)`, so widening the band makes this term *smaller* — the split
keeps costing nothing. -/
theorem ghsBlock_weighted_energy_free_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x : ℕ) (P : Finset ℕ) (T : ℝ) (hT : 5 ≤ T)
    (hPp : ∀ p ∈ P, p.Prime) (hPT : ∀ p ∈ P, T^2 ≤ (p:ℝ))
    (h2p : ∀ p ∈ P, 2*p ≤ x)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∑ p ∈ P, Real.log (p:ℝ) ≤ B)
    (w : ℝ → ℝ) (C Wtail : ℝ)
    (hC : ∀ ξ, w ξ ≤ C) (hw0 : ∀ ξ, 0 ≤ w ξ)
    (hWtail : (∫ ξ in {ξ : ℝ | T < |ξ|}, w ξ) ≤ Wtail)
    (hint : Integrable (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ))
    (hband : IntervalIntegrable (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ)
      volume (-T) T)
    (hband2 : IntervalIntegrable (fun ξ => ‖ghsBlockPoly f x P ξ‖^2)
      volume (-T) T)
    (htailP : IntegrableOn (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ)
      {ξ : ℝ | T < |ξ|})
    (htailw : IntegrableOn w {ξ : ℝ | T < |ξ|}) :
    (∫ ξ, ‖ghsBlockPoly f x P ξ‖^2 * w ξ)
      ≤ C * (Real.exp π * T * ∑ p ∈ P,
          (6144*((⌈2*(p:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log (p:ℝ)
            + Real.exp (-(π*T^2/64)) * B)
          * (Real.log (p:ℝ)/((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2)))
        + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
            * Wtail := by
  classical
  have hC0 : (0:ℝ) ≤ C := le_trans (hw0 0) (hC 0)
  have hsplit := integral_sq_weight_le (ghsBlockPoly f x P) w T C
    (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|)) Wtail
    (by linarith) hC hw0 (norm_ghsBlockPoly_le f hf x P) hWtail
    hint hband hband2 htailP htailw
  refine le_trans hsplit ?_
  have hband_le := ghsBlock_centred_energy_free_le f hf x P T hT hPp hPT h2p
    B hB0 hB
  have := mul_le_mul_of_nonneg_left hband_le hC0
  linarith

open Real in
/-- **The diagonal term is absorbed by the leading one** (Track R,
N143): for `0 < T` and `T² ≤ m`,

  `log m ≤ 2m/T`.

Small, but it is what keeps the free-`T` repair from trading one
vacuous bound for another.  The mean value theorem's bracket is
`6144·⌈2m/T⌉ + log m + e^{−πT²/64}·B`, and it is multiplied by the
prefactor `T`.  The first term is `T`-free after that multiplication
(`T·⌈2m/T⌉ ≍ m`), but `log m` is *not*: against the convergent mass
`∑_q log q/q² = O(1)` it contributes `≍ T·log Q`, which at
`T ≍ √(log X)` overshoots the intended `≍ log Q` by `√(log X)`.

Raising `T` to kill `e^{−πT²/64}·B` would therefore have re-broken the
bound through a different term — the same failure mode as the one being
repaired, one term over.

It does not, because the threshold `T² ≤ m` that raising `T` imposes is
itself what absorbs the diagonal: `T ≤ √m` gives `2m/T ≥ 2√m ≥ log m`.
The hypothesis introduced by the fix pays for the fix.  So
`log m ≤ 6144·⌈2m/T⌉` and the bracket collapses to
`2·6144·⌈2m/T⌉ + e^{−πT²/64}·B`, both terms behaving as intended. -/
theorem log_le_two_mul_div_of_sq_le (T : ℝ) (m : ℕ) (hT : 0 < T)
    (hTm : T^2 ≤ (m:ℝ)) :
    Real.log (m:ℝ) ≤ 2*(m:ℝ)/T := by
  have hm0 : (0:ℝ) < (m:ℝ) := lt_of_lt_of_le (by positivity) hTm
  have hs0 : (0:ℝ) < Real.sqrt (m:ℝ) := Real.sqrt_pos.mpr hm0
  have hss : Real.sqrt (m:ℝ) * Real.sqrt (m:ℝ) = (m:ℝ) :=
    Real.mul_self_sqrt hm0.le
  -- `T ≤ √m` is the threshold, restated
  have hTs : T ≤ Real.sqrt (m:ℝ) := by
    have h := Real.sqrt_le_sqrt hTm
    rwa [Real.sqrt_sq hT.le] at h
  -- `log m = 2 log √m ≤ 2(√m − 1)`
  have hhalf : Real.log (Real.sqrt (m:ℝ)) = Real.log (m:ℝ) / 2 :=
    Real.log_sqrt hm0.le
  have hlogs : Real.log (Real.sqrt (m:ℝ)) ≤ Real.sqrt (m:ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hs0
  have hlog2 : Real.log (m:ℝ) ≤ 2*Real.sqrt (m:ℝ) - 2 := by
    rw [hhalf] at hlogs; linarith
  have hlog0 : (0:ℝ) ≤ Real.log (m:ℝ) := Real.log_natCast_nonneg m
  rw [le_div_iff₀ hT]
  nlinarith [hlog2, hTs, hlog0, hs0, hss]

open Real in
/-- **The summand with the diagonal absorbed** (Track R, N144): for
`2 ≤ q`, `0 < T`, `T² ≤ q`, any `R`, and any `D ≥ 0`,

  `(6144·⌈2q/T⌉ + log q + R)·(log q/(q²D))
     ≤ (12290/T)·(log q/(qD)) + (6144 + R)·(log q/(q²D))`.

`mvt_summand_free_le` with the leftover `log q` moved into the leading
term by `log_le_two_mul_div_of_sq_le`, at a cost of `2/T` on the
constant `12288 → 12290`.

This is the form the energy sums want.  Both surviving masses are then
`T`-free after the mean value theorem's prefactor `T`:

* `T·(12290/T)·∑_q log q/q = 12290·∑_q log q/q ≍ log Q`, and
* `T·(6144 + R)·∑_q log q/q² ≍ T·(6144 + R)`,

so the whole bound is `≍ log Q + T·R`, with `R = e^{−πT²/64}·B`.  At
`T ≍ 5√(log X)` the second is `o(1)` and the first is the intended
`≍ log Q`.  Nothing left carries a hidden `T`.

That is the point of doing the absorption here rather than leaving
`log q` to be summed on its own: `∑_q log²q/q²` converges, but it is
multiplied by the prefactor `T`, so on its own it would have
reintroduced a `T·log Q`. -/
theorem mvt_summand_absorbed_le (q : ℕ) (hq : 2 ≤ q) (T : ℝ) (hT : 0 < T)
    (hTq : T^2 ≤ (q:ℝ)) (R D : ℝ) (hD : 0 ≤ D) :
    (6144*((⌈2*(q:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log (q:ℝ) + R)
        * (Real.log (q:ℝ)/((q:ℝ)^2 * D))
      ≤ (12290/T) * (Real.log (q:ℝ)/((q:ℝ) * D))
        + (6144 + R) * (Real.log (q:ℝ)/((q:ℝ)^2 * D)) := by
  have hq0 : (0:ℝ) < (q:ℝ) := by
    have : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    linarith
  have hlog0 : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_natCast_nonneg q
  have hmass : (0:ℝ) ≤ Real.log (q:ℝ)/((q:ℝ)^2 * D) := by positivity
  have hbase := mvt_summand_free_le q hq T hT R D hD
  -- move the leftover `log q` into the leading term
  have habs : Real.log (q:ℝ) * (Real.log (q:ℝ)/((q:ℝ)^2 * D))
      ≤ (2/T) * (Real.log (q:ℝ)/((q:ℝ) * D)) := by
    have hlq := log_le_two_mul_div_of_sq_le T q hT hTq
    have hstep : Real.log (q:ℝ) * (Real.log (q:ℝ)/((q:ℝ)^2 * D))
        ≤ (2*(q:ℝ)/T) * (Real.log (q:ℝ)/((q:ℝ)^2 * D)) :=
      mul_le_mul_of_nonneg_right hlq hmass
    refine le_trans hstep (le_of_eq ?_)
    rcases eq_or_lt_of_le hD with hD0 | hDpos
    · simp [← hD0]
    · field_simp
  -- and reassociate
  have hexp : (6144 + R + Real.log (q:ℝ)) * (Real.log (q:ℝ)/((q:ℝ)^2 * D))
      = (6144 + R) * (Real.log (q:ℝ)/((q:ℝ)^2 * D))
        + Real.log (q:ℝ) * (Real.log (q:ℝ)/((q:ℝ)^2 * D)) := by ring
  have hlead : (12288/T) * (Real.log (q:ℝ)/((q:ℝ) * D))
      + (2/T) * (Real.log (q:ℝ)/((q:ℝ) * D))
      = (12290/T) * (Real.log (q:ℝ)/((q:ℝ) * D)) := by ring
  rw [hexp] at hbase
  linarith [hbase, habs, hlead]

open Real Finset in
/-- **The `V₃` energy sum, at free `T`** (Track R, N146): for `Q` a set
of primes in `[2, X]` with `T² ≤ q`, and any `R ≥ 0`,

  `∑_q (6144·⌈2q/T⌉ + log q + R)·(log q/q²)
     ≤ (12290/T)·(log(X+1) + 2) + (6144 + R)·4`.

The `V₃` counterpart of `ghsBlock_energy_sum_free_le`, and the point at
which `V₃`'s magnitude finally reads off correctly.  After the mean
value theorem's prefactor `T`,

  `T·[(12290/T)(log(X+1) + 2) + (6144 + R)·4]
     = 12290·(log(X+1) + 2) + 4T·(6144 + R)`,

so `V₃ ≍ log X + T·R` with `R = e^{−πT²/64}·B`.  Taking `T = 5√(log X)`
makes `πT²/64 = (25π/64)log X` and `B ≍ X`, so `T·R ≍ X^{−0.22}√(log X)
→ 0`, leaving `V₃ ≍ log X` — which at `X = x^{e^{1−k}}` is the
`≍ e^{−k}log x` whose cancellation against `E₁`'s `e^{k}` leaves `L(x)`
with no residual `k`.

That is the magnitude `ghsPrimePoly_unit_energy_le`'s docstring claimed
from the start.  It is true here and was not true there: at `T = 8` the
`e^{−π}·B ≍ 0.043X` term alone exceeded it by `≍ X/log X`. -/
theorem ghsPrime_energy_sum_free_le (Q : Finset ℕ) (X : ℕ) (hX : 2 ≤ X)
    (T : ℝ) (hT : 0 < T)
    (hQp : ∀ q ∈ Q, q.Prime) (hQX : ∀ q ∈ Q, q ≤ X)
    (hQT : ∀ q ∈ Q, T^2 ≤ (q:ℝ)) (R : ℝ) (hR : 0 ≤ R) :
    ∑ q ∈ Q, (6144*((⌈2*(q:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log (q:ℝ) + R)
        * (Real.log (q:ℝ)/(q:ℝ)^2)
      ≤ (12290/T) * (Real.log ((X+1 : ℕ):ℝ) + 2) + (6144 + R) * 4 := by
  classical
  obtain ⟨hmass1, hmass2⟩ := prime_masses_le Q X hX hQp
    (fun q hq => (hQp q hq).two_le) hQX
  -- the absorbed summand at `D = 1`
  have hterm : ∀ q ∈ Q,
      (6144*((⌈2*(q:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log (q:ℝ) + R)
          * (Real.log (q:ℝ)/(q:ℝ)^2)
        ≤ (12290/T) * (Real.log (q:ℝ)/(q:ℝ))
          + (6144 + R) * (Real.log (q:ℝ)/(q:ℝ)^2) := by
    intro q hq
    have h := mvt_summand_absorbed_le q (hQp q hq).two_le T hT (hQT q hq)
      R 1 zero_le_one
    simpa using h
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hR6 : (0:ℝ) ≤ 6144 + R := by linarith
  have hT0 : (0:ℝ) ≤ 12290/T := by positivity
  have h1 := mul_le_mul_of_nonneg_left hmass1 hT0
  have h2 := mul_le_mul_of_nonneg_left hmass2 hR6
  linarith

open Real Finset in
/-- **The `E₁` energy sum over a block, at free `T`** (Track R, N145):
for `P` a set of primes in the `k`-th block of `x` with `2p ≤ x` and
`T² ≤ p`, and any `R ≥ 0`,

  `∑_p (6144·⌈2p/T⌉ + log p + R)·(log p/(p²·log²(x/p)))
     ≤ (12290/T)·(e^{2k}/log²x)(4((e−1)e^{−k}log x + log 2) + 4log 4)
       + (6144 + R)·SqMass`,

where `SqMass` is any bound on `∑_p log p/(p²·log²(x/p))`.

`ghsBlock_energy_sum_le` re-derived through `mvt_summand_absorbed_le`.
Two things changed and both matter.

The leading constant is `12290/T` rather than `1536`, which is what
makes the mean value theorem's prefactor `T` cancel: the product is
`12290`, independent of `T`.

And the residue is `6144 + R`, not `6144 + R + log X`.  The `log X`
came from bounding the diagonal `log p` by its largest value over the
whole range; multiplied by `T` it was the term that would have
reintroduced a `√(log X)` loss.  `mvt_summand_absorbed_le` sends it
into the leading term instead, where the threshold `T² ≤ p` pays for
it.  `X` therefore disappears from the statement — this bound no longer
degrades as the range grows.

`SqMass` is a parameter rather than `block_masses_le`'s `4/log²2`, and
that is the third change.  `4/log²2 ≈ 8.3` is `O(1)` where the truth is
`O(1/log²x)`: it discards `log²(x/p) ≥ log²2`, tight only at `p ≈ x/2`,
where `log p/p²` is negligible anyway.  The slack is not harmless —
downstream in `ghsBlock_E1_free_le` this factor multiplies a **forced**
`T ≍ √(log x)`, so an `O(1)` bound makes `E₁ ≍ √(log x)` instead of
`≍ e^{k}/log x`.  `sum_log_div_sq_ratio_sq_le` supplies the honest
`16/log²x + 4/(√⌊√x⌋·log²2)`; keeping the parameter free is what lets
that substitution be made at the call site rather than fixed here.

The first mass still comes from `block_masses_le`, whose `hPX` is
discharged from `2p ≤ x`. -/
theorem ghsBlock_energy_sum_free_le (x k : ℕ) (hx : 2 ≤ x) (hk : 1 ≤ k)
    (P : Finset ℕ) (T : ℝ) (hT : 0 < T)
    (hP : ∀ p ∈ P, p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k)
    (hPT : ∀ p ∈ P, T^2 ≤ (p:ℝ)) (h2p : ∀ p ∈ P, 2*p ≤ x)
    (R : ℝ) (hR : 0 ≤ R) (SqMass : ℝ)
    (hSqMass : ∑ p ∈ P,
      Real.log (p:ℝ)/((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2) ≤ SqMass) :
    ∑ p ∈ P, (6144*((⌈2*(p:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log (p:ℝ) + R)
        * (Real.log (p:ℝ)/((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2))
      ≤ (12290/T) * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
            * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
                + Real.log 2) + 4 * Real.log 4))
        + (6144 + R) * SqMass := by
  classical
  have hPx : ∀ p ∈ P, p ≤ x := fun p hp => by
    have := h2p p hp; omega
  obtain ⟨hmass1, -⟩ := block_masses_le x k hx hk x hx P hP h2p hPx
  have hmass2 := hSqMass
  -- the absorbed summand, at `D = log²(x/p)`
  have hterm : ∀ p ∈ P,
      (6144*((⌈2*(p:ℝ)/T⌉₊ : ℕ):ℝ) + Real.log (p:ℝ) + R)
          * (Real.log (p:ℝ)/((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2))
        ≤ (12290/T)
            * (Real.log (p:ℝ)/((p:ℝ) * (Real.log ((x:ℝ)/(p:ℝ)))^2))
          + (6144 + R)
            * (Real.log (p:ℝ)/((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2)) :=
    fun p hp => mvt_summand_absorbed_le p (hP p hp).1.two_le T hT (hPT p hp)
      R ((Real.log ((x:ℝ)/(p:ℝ)))^2) (sq_nonneg _)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hR6 : (0:ℝ) ≤ 6144 + R := by linarith
  have hT0 : (0:ℝ) ≤ 12290/T := by positivity
  have h1 := mul_le_mul_of_nonneg_left hmass1 hT0
  have h2 := mul_le_mul_of_nonneg_left hmass2 hR6
  linarith

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **`E₁ ≪ e^{k}/log x`, and this time it is true** (Track R, N147):
the `hE₁` that `pairing_halasz_le` consumes, for `P` a set of primes in
the `k`-th block of `x` with `T² ≤ p`.  With `S` the trivial sup of
`P₂`,

  `∫_ℝ ‖P₂‖²·w
     ≤ C·e^π·(12290·(e^{2k}/log²x)(4((e−1)e^{−k}log x + log 2) + 4log 4)
               + T·(6144 + e^{−πT²/64}·B)·SqMass)
       + S²·Wtail`,

where `SqMass ≥ ∑_p log p/(p²·log²(x/p))`.

`ghsBlock_E1_le` re-derived through the free-`T` chain
(`ghsBlock_weighted_energy_free_le` + `ghsBlock_energy_sum_free_le`),
closing the `E₁` half of the N132 repair.

**The prefactor `T` has been distributed and cancelled in the leading
term**, which is the whole content of the repair made visible in the
statement: `T·(12290/T) = 12290`, so the first term is `≍ e^{k}/log x`
at every `T`.  Only the second carries `T`, and it carries it against
`e^{−πT²/64}·B`, which `T` damps far faster than it grows.

At `T = 5√(log X)` and `B ≍ X` the damped part vanishes:
`T·e^{−πT²/64}B ≍ X^{−0.22}√(log X) → 0`.  What is left is `T·6144·SqMass`,
and **that term decides the whole estimate**.  `T` is not free —
`πT²/64 ≳ log B ≍ log x` is exactly what kills the damped part — so
`T ≍ √(log x)` is forced.  At `block_masses_le`'s `SqMass = 4/log²2`, an
absolute constant, that term is `≍ √(log x)` and **dominates**
`≍ e^{k}/log x` for every `k` once `log x ≳ 10³`, and the final estimate
overshoots `x·L(x)` by `(log x)^{3/4}`.  At the honest
`SqMass ≍ 16/log²x` (`sum_log_div_sq_ratio_sq_le`) it is
`≍ (log x)^{−3/2}`, genuinely negligible, and `E₁ ≍ e^{k}/log x` holds —
the magnitude `ghsBlock_E1_le` asserted, `ghsBlock_E1_free_le` freed
from `B` (the old chain's `e^{−π}B ≍ 0.043X` exceeded it by `≍ X·log x`),
and only a free `SqMass` actually delivers.

Against `V₃ ≍ e^{−k}log x` (`ghsPrime_energy_sum_free_le`) the product
`E₁·V₃` is `≍ 1` with the `k` cancelling, exactly as §4 needs. -/
theorem ghsBlock_E1_free_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x k : ℕ) (hx : 2 ≤ x) (hk : 1 ≤ k) (P : Finset ℕ)
    (T : ℝ) (hT : 5 ≤ T)
    (hP : ∀ p ∈ P, p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k)
    (hPT : ∀ p ∈ P, T^2 ≤ (p:ℝ)) (h2p : ∀ p ∈ P, 2*p ≤ x)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∑ p ∈ P, Real.log (p:ℝ) ≤ B)
    (SqMass : ℝ)
    (hSqMass : ∑ p ∈ P,
      Real.log (p:ℝ)/((p:ℝ)^2 * (Real.log ((x:ℝ)/(p:ℝ)))^2) ≤ SqMass)
    (w : ℝ → ℝ) (C Wtail : ℝ)
    (hC : ∀ ξ, w ξ ≤ C) (hw0 : ∀ ξ, 0 ≤ w ξ)
    (hWtail : (∫ ξ in {ξ : ℝ | T < |ξ|}, w ξ) ≤ Wtail)
    (hint : Integrable (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ))
    (hband : IntervalIntegrable (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ)
      volume (-T) T)
    (hband2 : IntervalIntegrable (fun ξ => ‖ghsBlockPoly f x P ξ‖^2)
      volume (-T) T)
    (htailP : IntegrableOn (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ)
      {ξ : ℝ | T < |ξ|})
    (htailw : IntegrableOn w {ξ : ℝ | T < |ξ|}) :
    (∫ ξ, ‖ghsBlockPoly f x P ξ‖^2 * w ξ)
      ≤ C * (Real.exp π *
          (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
              * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
                  + Real.log 2) + 4 * Real.log 4))
            + T * (6144 + Real.exp (-(π*T^2/64)) * B) * SqMass))
        + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
            * Wtail := by
  classical
  have hT0 : (0:ℝ) < T := by linarith
  have hC0 : (0:ℝ) ≤ C := le_trans (hw0 0) (hC 0)
  have hband_le := ghsBlock_weighted_energy_free_le f hf x P T hT
    (fun p hp => (hP p hp).1) hPT h2p B hB0 hB w C Wtail hC hw0 hWtail
    hint hband hband2 htailP htailw
  refine le_trans hband_le ?_
  -- the residue collected from Lemma 1's one remaining additive term
  set R : ℝ := Real.exp (-(π*T^2/64)) * B with hR_def
  have hR : (0:ℝ) ≤ R := mul_nonneg (Real.exp_pos _).le hB0
  have hsum := ghsBlock_energy_sum_free_le x k hx hk P T hT0 hP hPT h2p R hR
    SqMass hSqMass
  have hexp0 : (0:ℝ) ≤ Real.exp π * T := by positivity
  have hstep := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hsum hexp0) hC0
  -- distribute the prefactor `T`; it cancels against `12290/T`
  refine add_le_add (le_trans hstep (le_of_eq ?_)) le_rfl
  have hTne : T ≠ 0 := ne_of_gt hT0
  field_simp

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **`E₁ ≪ e^{k}/log x`, honestly** (Track R, N158):
`ghsBlock_E1_free_le` at the mass `sum_log_div_sq_ratio_sq_le` actually
supplies,

  `∫_ℝ ‖P₂‖²·w
     ≤ C·e^π·(12290·(e^{2k}/log²x)(4((e−1)e^{−k}log x + log 2) + 4log 4)
               + T·(6144 + e^{−πT²/64}·B)·(16/log²x + 4/(√⌊√x⌋·log²2)))
       + S²·Wtail`.

The statement with no free mass left in it, and the first form of `E₁`
in this campaign whose asserted magnitude survives measurement.

Both terms of the bracket are now `≪ e^{k}/log x`.  The first is that
size by `T·(12290/T) = 12290` (N147's repair).  The second, at the
forced `T ≍ √(log x)`, is `≍ √(log x)·(16/log²x) ≍ (log x)^{−3/2}` —
where `block_masses_le`'s `4/log²2` gave `≍ √(log x)` and swamped it.

Against `V₃ ≍ e^{−k}log x` (`ghsPrime_energy_sum_free_le`, whose own
`∑_q log q/q² ≤ 4` carries no `1/log²` factor and is therefore honest as
it stands) the product `E₁·V₃` is `≍ 1`, with the `k` cancelling.  The
pairing estimate's main term `√(E₁·5C·V₃·6b²)` is then `≍ C·b`, and with
`b` the Halász sup that is `≍ C·L(x)`: §3's target shape.  Measured over
`log x ∈ [10⁴, 10¹⁶]`, the local exponent of `√(E₁·30·C·V₃)` in `log x`
is `0.0000` and the constant settles at `≈ 4.1×10⁶`. -/
theorem ghsBlock_E1_sharp_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x k : ℕ) (hx : 2 ≤ x) (hk : 1 ≤ k) (P : Finset ℕ)
    (T : ℝ) (hT : 5 ≤ T)
    (hP : ∀ p ∈ P, p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k)
    (hPT : ∀ p ∈ P, T^2 ≤ (p:ℝ)) (h2p : ∀ p ∈ P, 2*p ≤ x)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∑ p ∈ P, Real.log (p:ℝ) ≤ B)
    (w : ℝ → ℝ) (C Wtail : ℝ)
    (hC : ∀ ξ, w ξ ≤ C) (hw0 : ∀ ξ, 0 ≤ w ξ)
    (hWtail : (∫ ξ in {ξ : ℝ | T < |ξ|}, w ξ) ≤ Wtail)
    (hint : Integrable (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ))
    (hband : IntervalIntegrable (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ)
      volume (-T) T)
    (hband2 : IntervalIntegrable (fun ξ => ‖ghsBlockPoly f x P ξ‖^2)
      volume (-T) T)
    (htailP : IntegrableOn (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ)
      {ξ : ℝ | T < |ξ|})
    (htailw : IntegrableOn w {ξ : ℝ | T < |ξ|}) :
    (∫ ξ, ‖ghsBlockPoly f x P ξ‖^2 * w ξ)
      ≤ C * (Real.exp π *
          (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
              * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
                  + Real.log 2) + 4 * Real.log 4))
            + T * (6144 + Real.exp (-(π*T^2/64)) * B) 
                * (16/(Real.log (x:ℝ))^2
                + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2))))
        + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
            * Wtail := by
  refine ghsBlock_E1_free_le f hf x k hx hk P T hT hP hPT h2p B hB0 hB _
    (sum_log_div_sq_ratio_sq_le x hx P (fun p hp => (hP p hp).1) h2p)
    w C Wtail hC hw0 hWtail hint hband hband2 htailP htailw

open MeasureTheory Real Complex ArithmeticFunction Finset in
open scoped FourierTransform in
/-- **`E₁` at the Riesz weight** (Track R, N164): `ghsBlock_E1_sharp_le`
with `w = ‖𝓕(rieszWindow)‖`, all side conditions discharged,

  `∫_ℝ ‖P₂‖²·‖𝓕V‖
     ≤ e^π·(12290·(e^{2k}/log²x)(4((e−1)e^{−k}log x + log 2) + 4log 4)
             + T·(6144 + e^{−πT²/64}·B)·(16/log²x + 4/(√⌊√x⌋·log²2)))
       + S²/(2π²T)`.

The `C` has gone, because it is `1`: `norm_fourier_rieszWindow_le_one`
is sharp, the transform attaining `1` at the origin.  And `Wtail` has
gone, because `fourier_rieszWindow_tail_le` names it — `1/(2π²T)`, in
closed form, with no derivative mass anywhere.

The five integrability hypotheses come from the weight's own regularity
(N163) and `ghs_pairing_integrability`, which already accepts any
continuous `w` with `0 ≤ w ≤ C/(1+ξ²)`; `norm_fourier_rieszWindow_le`
supplies that at `C = 1` directly.  Nothing here needs `rieszWindow` to
be smooth or compactly supported, which is the point — it is neither. -/
theorem ghsBlock_E1_riesz_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x k : ℕ) (hx : 2 ≤ x) (hk : 1 ≤ k) (P : Finset ℕ)
    (T : ℝ) (hT : 5 ≤ T)
    (hP : ∀ p ∈ P, p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k)
    (hPT : ∀ p ∈ P, T^2 ≤ (p:ℝ)) (h2p : ∀ p ∈ P, 2*p ≤ x)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∑ p ∈ P, Real.log (p:ℝ) ≤ B) :
    (∫ ξ, ‖ghsBlockPoly f x P ξ‖^2
        * ‖𝓕 (fun v => ((ExpSums.rieszWindow v : ℝ) : ℂ)) ξ‖)
      ≤ Real.exp π *
          (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
              * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
                  + Real.log 2) + 4 * Real.log 4))
            + T * (6144 + Real.exp (-(π*T^2/64)) * B)
                * (16/(Real.log (x:ℝ))^2
                    + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
        + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
            * (1/(2*Real.pi^2*T)) := by
  classical
  have hT0 : (0:ℝ) < T := by linarith
  set w : ℝ → ℝ :=
    fun ξ => ‖𝓕 (fun v => ((ExpSums.rieszWindow v : ℝ) : ℂ)) ξ‖ with hw_def
  have hwcont : Continuous w := ExpSums.continuous_norm_fourier_rieszWindow
  have hwint : Integrable w := ExpSums.integrable_norm_fourier_rieszWindow
  have hw0 : ∀ ξ, 0 ≤ w ξ := fun ξ => norm_nonneg _
  have hwle : ∀ ξ, w ξ ≤ 1/(1+ξ^2) := ExpSums.norm_fourier_rieszWindow_le
  have hC : ∀ ξ, w ξ ≤ 1 := ExpSums.norm_fourier_rieszWindow_le_one
  have hWtail : (∫ ξ in {ξ : ℝ | T < |ξ|}, w ξ) ≤ 1/(2*Real.pi^2*T) :=
    ExpSums.fourier_rieszWindow_tail_le T hT0
  -- integrability, all from the closed form
  obtain ⟨-, hint, -, -, -, -, -⟩ :=
    ghs_pairing_integrability f hf x ∅ P ∅ w hwcont 1 hw0 hwle
  have hband : IntervalIntegrable (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ)
      volume (-T) T := hint.intervalIntegrable
  have hband2 : IntervalIntegrable (fun ξ => ‖ghsBlockPoly f x P ξ‖^2)
      volume (-T) T :=
    (((continuous_ghsBlockPoly f x P).norm.pow 2)).intervalIntegrable _ _
  have htailP : IntegrableOn (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ)
      {ξ : ℝ | T < |ξ|} := hint.integrableOn
  have htailw : IntegrableOn w {ξ : ℝ | T < |ξ|} := hwint.integrableOn
  have h := ghsBlock_E1_sharp_le f hf x k hx hk P T hT hP hPT h2p B hB0 hB
    w 1 (1/(2*Real.pi^2*T)) hC hw0 hWtail hint hband hband2 htailP htailw
  simpa using h

open MeasureTheory Real Complex ArithmeticFunction Finset in
/-- **`V₃ ≪ log X`, and this time it is true** (Track R, N149): the
`hV` that `pairing_halasz_le` consumes, for `Q` a set of primes in
`[2, X]` with `T² ≤ q`.  For every frequency `N`,

  `∫_{N−1/2}^{N+1/2} ‖P₃(t)‖² dt
     ≤ e^π·(12290·(log(X+1) + 2) + 4T·(6144 + e^{−πT²/64}·B))`.

`ghsPrimePoly_unit_energy_le` re-derived through the free-`T` chain,
closing the `V₃` half of the N132 repair as `ghsBlock_E1_free_le`
closes the `E₁` half.

As there, the prefactor `T` is distributed and cancels in the leading
term — `T·(12290/T) = 12290` — so `V₃ ≍ log X` at every `T`, and only
the second term carries `T`, against the `e^{−πT²/64}` that outruns it.
At `T = 5√(log X)` with `B ≍ X`, that term is `≍ √(log X)`, so
`V₃ ≍ log X`; with `X = x^{e^{1−k}}` this is `≍ e^{−k}·log x`.

**The two halves now meet as intended.**  `E₁·V₃ ≍ (e^{k}/log x)·
(e^{−k}log x) = O(1)` with the block index cancelling — which is what
leaves `L(x)` in §4's bound with no residual `k`.  Both factors were
vacuous before the repair, and the cancellation could not have been
read off either of them. -/
theorem ghsPrimePoly_unit_energy_final_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (Q : Finset ℕ) (X : ℕ) (hX : 2 ≤ X) (T : ℝ) (hT : 5 ≤ T)
    (hQp : ∀ q ∈ Q, q.Prime) (hQX : ∀ q ∈ Q, q ≤ X)
    (hQT : ∀ q ∈ Q, T^2 ≤ (q:ℝ))
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∑ q ∈ Q, Real.log (q:ℝ) ≤ B)
    (hwide : ∀ w : ℕ → ℂ, IntervalIntegrable
      (fun u => ‖∑ q ∈ Q, w q
        * ((Real.fourierChar (-(Real.log (q:ℝ) * u)) : Circle) : ℂ)‖^2)
      volume (-T) T)
    (N : ℝ) :
    (∫ t in (N - 1/2)..(N + 1/2), ‖ghsPrimePoly f Q t‖^2)
      ≤ Real.exp π * (12290 * (Real.log ((X+1 : ℕ):ℝ) + 2)
          + 4*T * (6144 + Real.exp (-(π*T^2/64)) * B)) := by
  classical
  have hT0 : (0:ℝ) < T := by linarith
  refine le_trans (ghsPrimePoly_unit_energy_free_le f hf Q T hT hQp hQT
    B hB0 hB hwide N) ?_
  set R : ℝ := Real.exp (-(π*T^2/64)) * B with hR_def
  have hR : (0:ℝ) ≤ R := mul_nonneg (Real.exp_pos _).le hB0
  have hsum := ghsPrime_energy_sum_free_le Q X hX T hT0 hQp hQX hQT R hR
  have hexp0 : (0:ℝ) ≤ Real.exp π * T := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left hsum hexp0) (le_of_eq ?_)
  have hTne : T ≠ 0 := ne_of_gt hT0
  field_simp

end MoltResearch
