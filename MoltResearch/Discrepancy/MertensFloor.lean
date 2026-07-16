import MoltResearch.Discrepancy.DilationCover
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Discrepancy: the Mertens floor

Track C, VK/Littlewood campaign (`Problems/tao2015_derivation_c.md`, issue #2935, W1):
the lower bound of Mertens' second theorem,

  `log log y ≤ ∑_{p < y} 1/p + 1`,

by the elementary smooth-number argument — no zeta asymptotics: every `1 ≤ n < y` is
`y`-smooth with exponents at most `log₂ y` (`factorization_le_log`), so the harmonic sum
below `y` is dominated by the product over primes `p < y` of finite geometric series;
`log t ≤ t − 1` and the telescoping bound `∑_{m≤y} 1/(m(m−1)) ≤ 1` finish.

This is the first input to discharging `VinogradovKorobovAssumption`: the pretentious
distance `∑_{p<y} (1 − Re χ(p)p^{−is})/p` splits as this floor minus the Euler-product
bridge term (issue #2935, W2).
-/

namespace MoltResearch

open Finset

/-- The harmonic floor: `log y ≤ ∑_{1 ≤ n < y} 1/n` (telescoping `log(1 + 1/n) ≤ 1/n`). -/
theorem log_le_sum_one_div_Ico (y : ℕ) :
    Real.log y ≤ ∑ n ∈ Finset.Ico 1 y, (1 : ℝ) / n := by
  induction y with
  | zero => simp
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    rw [Finset.sum_Ico_succ_top (by omega)]
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hstep : Real.log (m + 1) - Real.log m ≤ 1 / m := by
      rw [← Real.log_div (by positivity) (ne_of_gt hm0)]
      have h1 : ((m : ℝ) + 1) / m = 1 + 1 / m := by field_simp
      have h2 := Real.log_le_sub_one_of_pos (x := ((m : ℝ) + 1) / m) (by positivity)
      rw [h1] at h2 ⊢
      linarith
    push_cast
    linarith

/-- Finite geometric sums are at most `1/(1 − x)` on `[0, 1)`. -/
private theorem geom_sum_le_one_div (K : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∑ k ∈ Finset.range K, x ^ k ≤ 1 / (1 - x) := by
  have h1x : (0 : ℝ) < 1 - x := by linarith
  have h := geom_sum_mul x K
  have hpow : (0 : ℝ) ≤ x ^ K := pow_nonneg hx0 K
  rw [le_div_iff₀ h1x]
  nlinarith [h, hpow]

/-- A number `1 ≤ n < y` written through its prime data below `y`: the real product
form of `Nat.factorization_prod_pow_eq_self`, extended from the prime factors of `n` to
all primes below `y` (the extra exponents vanish). -/
private theorem one_div_eq_prod_primesBelow {y n : ℕ} (hn : n ∈ Finset.Ico 1 y) :
    (1 : ℝ) / n = ∏ p ∈ y.primesBelow, ((1 : ℝ) / p) ^ n.factorization p := by
  rw [Finset.mem_Ico] at hn
  have hn0 : n ≠ 0 := by omega
  have hsub : n.primeFactors ⊆ y.primesBelow := by
    intro p hp
    exact Nat.mem_primesBelow.mpr
      ⟨lt_of_le_of_lt (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)) hn.2,
        Nat.prime_of_mem_primeFactors hp⟩
  have hext : ∏ p ∈ y.primesBelow, ((1 : ℝ) / p) ^ n.factorization p
      = ∏ p ∈ n.primeFactors, ((1 : ℝ) / p) ^ n.factorization p := by
    refine (Finset.prod_subset hsub fun p _ hp => ?_).symm
    have h0 : n.factorization p = 0 := by
      by_contra h
      exact hp (by
        rw [← Nat.support_factorization]
        exact Finsupp.mem_support_iff.mpr h)
    rw [h0, pow_zero]
  have hnat : ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p = n := by
    rw [show ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p
        = ((∏ p ∈ n.primeFactors, p ^ n.factorization p : ℕ) : ℝ) from by push_cast; rfl]
    exact_mod_cast congrArg Nat.cast (Nat.factorization_prod_pow_eq_self hn0)
  rw [hext]
  rw [show ∀ s : Finset ℕ, ∏ p ∈ s, ((1 : ℝ) / p) ^ n.factorization p
      = (∏ p ∈ s, (p : ℝ) ^ n.factorization p)⁻¹ from fun s => by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun p _ => by rw [one_div, inv_pow]]
  rw [hnat, one_div]

/-- **The smooth-number expansion**: the harmonic sum below `y` is dominated by the
product over primes `p < y` of the geometric sums `∑_{k ≤ log₂ y} (1/p)^k` — every
`1 ≤ n < y` factors through the product with exponents at most `log₂ y`. -/
theorem sum_one_div_Ico_le_prod_geom (y : ℕ) :
    ∑ n ∈ Finset.Ico 1 y, (1 : ℝ) / n
      ≤ ∏ p ∈ y.primesBelow,
          ∑ k ∈ Finset.range (Nat.log 2 y + 1), ((1 : ℝ) / p) ^ k := by
  classical
  -- rewrite the product over the subtype and expand it as a sum over exponent vectors
  rw [← Finset.prod_attach y.primesBelow
    (fun p => ∑ k ∈ Finset.range (Nat.log 2 y + 1), ((1 : ℝ) / p) ^ k),
    show (y.primesBelow.attach : Finset {p // p ∈ y.primesBelow}) = Finset.univ from
      (Finset.univ_eq_attach _).symm,
    Finset.prod_univ_sum]
  set F : ℕ → ({p // p ∈ y.primesBelow} → ℕ) := fun n p => n.factorization p.1 with hF
  -- each harmonic term is the vector product of its encoding
  have hval : ∀ n ∈ Finset.Ico 1 y,
      (1 : ℝ) / n = ∏ p : {p // p ∈ y.primesBelow}, ((1 : ℝ) / p.1) ^ F n p := by
    intro n hn
    rw [one_div_eq_prod_primesBelow hn, ← Finset.prod_attach y.primesBelow
      (fun p => ((1 : ℝ) / p) ^ n.factorization p), Finset.univ_eq_attach]
  -- the encoding is injective: the vector reconstructs n
  have hrecon : ∀ n ∈ Finset.Ico 1 y,
      n = ∏ p : {p // p ∈ y.primesBelow}, p.1 ^ F n p := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn0 : n ≠ 0 := by omega
    have hsub : n.primeFactors ⊆ y.primesBelow := by
      intro p hp
      exact Nat.mem_primesBelow.mpr
        ⟨lt_of_le_of_lt (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)) hn.2,
          Nat.prime_of_mem_primeFactors hp⟩
    rw [Finset.univ_eq_attach, Finset.prod_attach y.primesBelow
      (fun p => p ^ n.factorization p)]
    rw [show ∏ p ∈ y.primesBelow, p ^ n.factorization p
        = ∏ p ∈ n.primeFactors, p ^ n.factorization p from
      (Finset.prod_subset hsub fun p _ hp => by
        have h0 : n.factorization p = 0 := by
          by_contra h
          exact hp (by
        rw [← Nat.support_factorization]
        exact Finsupp.mem_support_iff.mpr h)
        rw [h0, pow_zero]).symm]
    exact (Nat.factorization_prod_pow_eq_self hn0).symm
  have hinj : Set.InjOn F (Finset.Ico 1 y) := by
    intro n hn m hm hnm
    rw [hrecon n hn, hrecon m hm]
    exact Finset.prod_congr rfl fun p _ => by rw [hnm]
  -- the image lands in the bounded exponent vectors
  have himg : (Finset.Ico 1 y).image F
      ⊆ Fintype.piFinset fun _ : {p // p ∈ y.primesBelow} =>
          Finset.range (Nat.log 2 y + 1) := by
    intro g hg
    rw [Finset.mem_image] at hg
    obtain ⟨n, hn, rfl⟩ := hg
    rw [Finset.mem_Ico] at hn
    rw [Fintype.mem_piFinset]
    intro p
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact factorization_le_log (X := y) hn.1 (le_of_lt hn.2) p.1
  -- assemble
  calc ∑ n ∈ Finset.Ico 1 y, (1 : ℝ) / n
      = ∑ n ∈ Finset.Ico 1 y,
          ∏ p : {p // p ∈ y.primesBelow}, ((1 : ℝ) / p.1) ^ F n p :=
        Finset.sum_congr rfl hval
    _ = ∑ g ∈ (Finset.Ico 1 y).image F,
          ∏ p : {p // p ∈ y.primesBelow}, ((1 : ℝ) / p.1) ^ g p :=
        by rw [Finset.sum_image fun n hn m hm h => hinj hn hm h]
    _ ≤ ∑ g ∈ Fintype.piFinset
            (fun _ : {p // p ∈ y.primesBelow} => Finset.range (Nat.log 2 y + 1)),
          ∏ p : {p // p ∈ y.primesBelow}, ((1 : ℝ) / p.1) ^ g p := by
        refine Finset.sum_le_sum_of_subset_of_nonneg himg fun g _ _ => ?_
        exact Finset.prod_nonneg fun p _ => by positivity

/-- Telescoping bound: `∑_{2 ≤ m ≤ y} 1/(m(m−1)) ≤ 1`. -/
private theorem sum_one_div_mul_sub_one_le (y : ℕ) :
    ∑ m ∈ Finset.Icc 2 y, (1 : ℝ) / (m * (m - 1)) ≤ 1 := by
  have key : ∀ z : ℕ, 1 ≤ z → ∑ m ∈ Finset.Icc 2 z, (1 : ℝ) / (m * (m - 1))
      = 1 - 1 / z := by
    intro z hz
    induction z with
    | zero => omega
    | succ w ih =>
      rcases Nat.eq_zero_or_pos w with rfl | hw
      · norm_num
      rw [Finset.sum_Icc_succ_top (by omega), ih hw]
      have hw0 : (0 : ℝ) < w := by exact_mod_cast hw
      have hw0' : (w : ℝ) ≠ 0 := ne_of_gt hw0
      have hw1 : (w : ℝ) + 1 ≠ 0 := by positivity
      push_cast
      rw [show (w : ℝ) + 1 - 1 = (w : ℝ) from by ring]
      field_simp
      ring
  rcases Nat.lt_or_ge y 1 with hy | hy
  · rw [show y = 0 by omega]
    norm_num
  · rw [key y hy]
    have : (0 : ℝ) < y := by exact_mod_cast hy
    have : 0 < 1 / (y : ℝ) := by positivity
    linarith

/-- **The Mertens floor** (lower bound of Mertens' second theorem, elementary form):
`log log y ≤ ∑_{p < y} 1/p + 1`. -/
theorem log_log_le_sum_one_div_primesBelow {y : ℕ} (hy : 2 ≤ y) :
    Real.log (Real.log y) ≤ (∑ p ∈ y.primesBelow, (1 : ℝ) / p) + 1 := by
  have hy1 : (1 : ℝ) < y := by exact_mod_cast hy
  -- facts about each prime factor
  have hp2 : ∀ p ∈ y.primesBelow, (2 : ℝ) ≤ p := fun p hp => by
    exact_mod_cast (Nat.mem_primesBelow.mp hp).2.two_le
  have hgeom_pos : ∀ p ∈ y.primesBelow,
      0 < ∑ k ∈ Finset.range (Nat.log 2 y + 1), ((1 : ℝ) / p) ^ k := by
    intro p hp
    have h2 := hp2 p hp
    refine Finset.sum_pos (fun k _ => by positivity) ⟨0, by simp⟩
  -- log of the harmonic sum is below the sum of logs of the geometric factors
  have hH : Real.log y ≤ ∑ n ∈ Finset.Ico 1 y, (1 : ℝ) / n := log_le_sum_one_div_Ico y
  have hHpos : 0 < Real.log y := Real.log_pos hy1
  have hlog1 : Real.log (Real.log y)
      ≤ Real.log (∏ p ∈ y.primesBelow,
          ∑ k ∈ Finset.range (Nat.log 2 y + 1), ((1 : ℝ) / p) ^ k) := by
    refine Real.log_le_log hHpos (le_trans hH (sum_one_div_Ico_le_prod_geom y))
  rw [Real.log_prod (fun p hp => ne_of_gt (hgeom_pos p hp))] at hlog1
  -- each log factor is at most 1/(p − 1) = 1/p + 1/(p(p−1))
  have hfac : ∀ p ∈ y.primesBelow,
      Real.log (∑ k ∈ Finset.range (Nat.log 2 y + 1), ((1 : ℝ) / p) ^ k)
        ≤ 1 / p + 1 / (p * ((p : ℝ) - 1)) := by
    intro p hp
    have h2 := hp2 p hp
    have hx0 : (0 : ℝ) ≤ 1 / p := by positivity
    have hx1 : (1 : ℝ) / p < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    have hlogle := Real.log_le_sub_one_of_pos (hgeom_pos p hp)
    -- the geometric sum minus 1 is the tail, bounded by (1/p)/(1 − 1/p)
    have htail : (∑ k ∈ Finset.range (Nat.log 2 y + 1), ((1 : ℝ) / p) ^ k) - 1
        ≤ (1 / p) / (1 - 1 / p) := by
      rw [Finset.sum_range_succ' (fun k => ((1 : ℝ) / p) ^ k) (Nat.log 2 y)]
      have hmul : ∑ k ∈ Finset.range (Nat.log 2 y), ((1 : ℝ) / p) ^ (k + 1)
          = (1 / p) * ∑ k ∈ Finset.range (Nat.log 2 y), ((1 : ℝ) / p) ^ k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [pow_zero, add_sub_cancel_right, hmul]
      have hgle := geom_sum_le_one_div (Nat.log 2 y) hx0 hx1
      calc (1 / p) * ∑ k ∈ Finset.range (Nat.log 2 y), ((1 : ℝ) / p) ^ k
          ≤ (1 / p) * (1 / (1 - 1 / p)) := by
            exact mul_le_mul_of_nonneg_left hgle hx0
        _ = (1 / p) / (1 - 1 / p) := by ring
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hpm1 : (p : ℝ) - 1 ≠ 0 := by
      intro h
      have : (p : ℝ) = 1 := by linarith
      linarith
    have hsimp : (1 / (p : ℝ)) / (1 - 1 / p) = 1 / ((p : ℝ) - 1) := by
      rw [show 1 - 1 / (p : ℝ) = ((p : ℝ) - 1) / p from by field_simp,
        div_div_div_cancel_right₀]
      exact hp0
    have hsplit : 1 / ((p : ℝ) - 1) = 1 / p + 1 / (p * ((p : ℝ) - 1)) := by
      field_simp
      ring
    rw [hsimp, hsplit] at htail
    linarith
  -- sum the per-prime bounds and close with the telescope
  have hsum : ∑ p ∈ y.primesBelow,
      Real.log (∑ k ∈ Finset.range (Nat.log 2 y + 1), ((1 : ℝ) / p) ^ k)
        ≤ (∑ p ∈ y.primesBelow, (1 : ℝ) / p)
          + ∑ p ∈ y.primesBelow, 1 / (p * ((p : ℝ) - 1)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hfac
  have htel : ∑ p ∈ y.primesBelow, 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (fun p hp => ?_) (fun m hm _ => ?_)) (sum_one_div_mul_sub_one_le y)
    · rw [Finset.mem_Icc]
      have h := Nat.mem_primesBelow.mp hp
      exact ⟨h.2.two_le, le_of_lt h.1⟩
    · rw [Finset.mem_Icc] at hm
      have h2 : (2 : ℝ) ≤ m := by exact_mod_cast hm.1
      have : (0 : ℝ) < m * ((m : ℝ) - 1) := by nlinarith
      positivity
  linarith

end MoltResearch
