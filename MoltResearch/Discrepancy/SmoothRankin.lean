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

end MoltResearch
