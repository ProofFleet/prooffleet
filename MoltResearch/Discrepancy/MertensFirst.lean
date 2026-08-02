import MoltResearch.Discrepancy.MertensFloor
import Mathlib.Data.Nat.Choose.Factorization
import MoltResearch.Discrepancy.ChebyshevTail

/-!
# Discrepancy: Mertens' first theorem, upper form

Track C, VK/Littlewood campaign (`Problems/tao2015_derivation_c.md`, issue #2935, W2b):

  `∑_{p < y} log p / p ≤ 4 log y`,

by the classical factorial double count: Legendre's formula gives
`⌊y/p⌋ ≤ ν_p(y!)`, so `∑_p (⌊y/p⌋ + 1) log p ≤ 2 log (y!) ≤ 2 y log y`, and
`y/p ≤ ⌊y/p⌋ + 1` transfers this to the real weights.

This is the weight-comparison input for the truncation step (W2c): replacing the
`p^{−1−1/log y}` weights of the Euler-product bridge (W2a) by `1/p` on `p < y` costs
`(1/log y)·∑_{p<y} log p/p ≤ 2` — an absolute constant.
-/

namespace MoltResearch

open Finset

/-- `log(y!)` as the prime decomposition `∑ ν_p(y!) log p`. -/
private theorem log_factorial_eq (y : ℕ) :
    Real.log (y.factorial)
      = ∑ p ∈ (y.factorial).primeFactors,
          ((y.factorial).factorization p : ℝ) * Real.log p := by
  have h0 : y.factorial ≠ 0 := y.factorial_ne_zero
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self h0]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  rw [show ((∏ p ∈ (y.factorial).primeFactors, p ^ (y.factorial).factorization p : ℕ) : ℝ)
      = ∏ p ∈ (y.factorial).primeFactors, ((p : ℝ)) ^ (y.factorial).factorization p from by
    push_cast; rfl]
  rw [Real.log_prod (fun p hp => by
    have hpp := Nat.prime_of_mem_primeFactors hp
    have : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    positivity)]
  exact Finset.sum_congr rfl fun p _ => by rw [Real.log_pow]

/-- The factorial log is at most `y log y`. -/
private theorem log_factorial_le (y : ℕ) :
    Real.log (y.factorial) ≤ y * Real.log y := by
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp
  rw [show (y.factorial : ℝ) = ∏ i ∈ Finset.range y, ((i : ℝ) + 1) from by
    rw [show ∏ i ∈ Finset.range y, ((i : ℝ) + 1)
        = ((∏ i ∈ Finset.range y, (i + 1) : ℕ) : ℝ) from by
      push_cast; rfl, Finset.prod_range_add_one_eq_factorial]]
  rw [Real.log_prod (fun i _ => by positivity)]
  calc ∑ i ∈ Finset.range y, Real.log ((i : ℝ) + 1)
      ≤ ∑ _i ∈ Finset.range y, Real.log y := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [Finset.mem_range] at hi
        refine Real.log_le_log (by positivity) ?_
        have : (i : ℝ) + 1 ≤ y := by exact_mod_cast Nat.succ_le_of_lt hi
        linarith
    _ = y * Real.log y := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Legendre floor: `⌊y/p⌋ ≤ ν_p(y!)` for primes `p ≤ y`. -/
private theorem div_le_factorization_factorial {y p : ℕ} (hp : p.Prime) (hpy : p ≤ y) :
    y / p ≤ (y.factorial).factorization p := by
  rw [Nat.factorization_factorial hp (Nat.lt_succ_self _)]
  have h1mem : 1 ∈ Finset.Ico 1 (Nat.log p y + 1) := by
    rw [Finset.mem_Ico]
    have : 1 ≤ Nat.log p y := by
      rw [Nat.le_log_iff_pow_le hp.one_lt (by have := hp.two_le; omega)]
      simpa using hpy
    omega
  calc y / p = y / p ^ 1 := by rw [pow_one]
    _ ≤ ∑ i ∈ Finset.Ico 1 (Nat.log p y + 1), y / p ^ i :=
        Finset.single_le_sum (f := fun i => y / p ^ i)
          (fun i _ => Nat.zero_le _) h1mem

/-- The weighted prime count `∑_{p<y} (⌊y/p⌋ + 1) log p` is at most `2 log(y!)`. -/
private theorem sum_div_succ_mul_log_le (y : ℕ) :
    ∑ p ∈ y.primesBelow, ((y / p : ℕ) + 1 : ℝ) * Real.log p
      ≤ 2 * Real.log (y.factorial) := by
  have hsub : y.primesBelow ⊆ (y.factorial).primeFactors := by
    intro p hp
    have h := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primeFactors.mpr
      ⟨h.2, Nat.dvd_factorial h.2.pos (le_of_lt h.1), y.factorial_ne_zero⟩
  have hnonneg : ∀ p ∈ (y.factorial).primeFactors,
      0 ≤ ((y.factorial).factorization p : ℝ) * Real.log p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have := Real.log_nonneg h1
    positivity
  have hterm : ∀ p ∈ y.primesBelow, ((y / p : ℕ) + 1 : ℝ) * Real.log p
      ≤ 2 * (((y.factorial).factorization p : ℝ) * Real.log p) := by
    intro p hp
    have h := Nat.mem_primesBelow.mp hp
    have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast h.2.one_lt.le)
    have hdiv := div_le_factorization_factorial h.2 (le_of_lt h.1)
    have hpos : 1 ≤ (y.factorial).factorization p := by
      rw [← Nat.Prime.dvd_iff_one_le_factorization h.2 y.factorial_ne_zero]
      exact Nat.dvd_factorial h.2.pos (le_of_lt h.1)
    have hcast1 : ((y / p : ℕ) : ℝ) ≤ ((y.factorial).factorization p : ℝ) := by
      exact_mod_cast hdiv
    have hcast2 : (1 : ℝ) ≤ ((y.factorial).factorization p : ℝ) := by
      exact_mod_cast hpos
    nlinarith
  calc ∑ p ∈ y.primesBelow, ((y / p : ℕ) + 1 : ℝ) * Real.log p
      ≤ ∑ p ∈ y.primesBelow,
          2 * (((y.factorial).factorization p : ℝ) * Real.log p) :=
        Finset.sum_le_sum hterm
    _ = 2 * ∑ p ∈ y.primesBelow,
          ((y.factorial).factorization p : ℝ) * Real.log p := by
        rw [Finset.mul_sum]
    _ ≤ 2 * ∑ p ∈ (y.factorial).primeFactors,
          ((y.factorial).factorization p : ℝ) * Real.log p := by
        have := Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun p hp _ => hnonneg p hp)
        linarith
    _ = 2 * Real.log (y.factorial) := by rw [log_factorial_eq y]

/-- **Mertens' first theorem, upper form**: `∑_{p<y} log p / p ≤ 4 log y`. -/
theorem sum_log_div_primesBelow_le (y : ℕ) :
    ∑ p ∈ y.primesBelow, Real.log p / p ≤ 4 * Real.log y := by
  rcases Nat.lt_or_ge y 2 with hy | hy
  · have hempty : y.primesBelow = ∅ := by
      ext p
      simp only [Nat.mem_primesBelow, Finset.notMem_empty, iff_false, not_and]
      intro hlt hpp
      have := hpp.two_le
      omega
    rw [hempty]
    simp only [Finset.sum_empty]
    rcases Nat.lt_or_ge y 1 with h0 | h1
    · rw [show y = 0 by omega]
      norm_num
    · have : (1 : ℝ) ≤ y := by exact_mod_cast h1
      have := Real.log_nonneg this
      linarith
  -- main case y ≥ 2
  have hy0 : (0 : ℝ) < y := by
    have : (2 : ℝ) ≤ y := by exact_mod_cast hy
    linarith
  -- real floor bound: y/p ≤ ⌊y/p⌋ + 1
  have hfloor : ∀ p ∈ y.primesBelow, (y : ℝ) / p ≤ ((y / p : ℕ) : ℝ) + 1 := by
    intro p hp
    have h := Nat.mem_primesBelow.mp hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast h.2.pos
    rw [div_le_iff₀ hp0]
    have hmod := Nat.div_add_mod y p
    have hlt : y % p < p := Nat.mod_lt _ h.2.pos
    have : (y : ℝ) = (p : ℝ) * ((y / p : ℕ) : ℝ) + ((y % p : ℕ) : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hmod.symm
    have hmodR : ((y % p : ℕ) : ℝ) < p := by exact_mod_cast hlt
    have hq0 : (0 : ℝ) ≤ ((y / p : ℕ) : ℝ) := Nat.cast_nonneg _
    have hr0 : (0 : ℝ) ≤ ((y % p : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  -- multiply out by y and use the factorial double count
  have hmain : ∑ p ∈ y.primesBelow, (y : ℝ) / p * Real.log p
      ≤ 2 * ((y : ℝ) * Real.log y) := by
    have hle : ∑ p ∈ y.primesBelow, (y : ℝ) / p * Real.log p
        ≤ ∑ p ∈ y.primesBelow, ((y / p : ℕ) + 1 : ℝ) * Real.log p := by
      refine Finset.sum_le_sum fun p hp => ?_
      have h := Nat.mem_primesBelow.mp hp
      have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast h.2.one_lt.le)
      exact mul_le_mul_of_nonneg_right (hfloor p hp) hlog0
    refine le_trans hle (le_trans (sum_div_succ_mul_log_le y) ?_)
    have := log_factorial_le y
    linarith
  -- divide by y
  have hdiv : ∑ p ∈ y.primesBelow, Real.log p / p
      = (1 / y) * ∑ p ∈ y.primesBelow, (y : ℝ) / p * Real.log p := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have h := Nat.mem_primesBelow.mp hp
    have hp0 : (p : ℝ) ≠ 0 := by
      have : (0 : ℝ) < p := by exact_mod_cast h.2.pos
      linarith
    field_simp
  rw [hdiv]
  calc (1 / (y : ℝ)) * ∑ p ∈ y.primesBelow, (y : ℝ) / p * Real.log p
      ≤ (1 / (y : ℝ)) * (2 * ((y : ℝ) * Real.log y)) :=
        mul_le_mul_of_nonneg_left hmain (by positivity : (0 : ℝ) ≤ 1 / (y : ℝ))
    _ = 2 * Real.log y := by
        rw [show (1 / (y : ℝ)) * (2 * ((y : ℝ) * Real.log y))
            = 2 * Real.log y * ((y : ℝ) / (y : ℝ)) from by ring,
          div_self (ne_of_gt hy0), mul_one]
    _ ≤ 4 * Real.log y := by
        have h1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (by omega : 1 ≤ y)
        have h2 := Real.log_nonneg h1
        linarith

/-- **Mertens' first theorem, sharp upper form** (Track R, E2-i):
`∑_{p<y} log p/p ≤ log y + 2` — the Legendre double count kept at
factor one, with the `+1`-floor cost priced by Chebyshev's θ-bound.
The constant-`1` leading term is what keeps the smooth-harmonic Euler
product at a single power of `log`. -/
theorem sum_log_div_primesBelow_le_sharp (y : ℕ) (hy : 2 ≤ y) :
    ∑ p ∈ y.primesBelow, Real.log p / p ≤ Real.log y + 2 := by
  classical
  have hy0 : (0:ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  -- floor sum against the factorial
  have hsub : y.primesBelow ⊆ (y.factorial).primeFactors := by
    intro p hp
    have h := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primeFactors.mpr
      ⟨h.2, Nat.dvd_factorial h.2.pos (le_of_lt h.1), y.factorial_ne_zero⟩
  have hnonneg : ∀ p ∈ (y.factorial).primeFactors,
      0 ≤ ((y.factorial).factorization p : ℝ) * Real.log p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have := Real.log_nonneg h1
    positivity
  have hfloor : ∑ p ∈ y.primesBelow, ((y / p : ℕ) : ℝ) * Real.log p
      ≤ Real.log (y.factorial) := by
    have hterm : ∀ p ∈ y.primesBelow, ((y / p : ℕ) : ℝ) * Real.log p
        ≤ ((y.factorial).factorization p : ℝ) * Real.log p := by
      intro p hp
      have h := Nat.mem_primesBelow.mp hp
      have hlog0 : 0 ≤ Real.log p :=
        Real.log_nonneg (by exact_mod_cast h.2.one_lt.le)
      have hdiv := div_le_factorization_factorial h.2 (le_of_lt h.1)
      have hcast : ((y / p : ℕ) : ℝ) ≤ ((y.factorial).factorization p : ℝ) := by
        exact_mod_cast hdiv
      exact mul_le_mul_of_nonneg_right hcast hlog0
    calc ∑ p ∈ y.primesBelow, ((y / p : ℕ) : ℝ) * Real.log p
        ≤ ∑ p ∈ y.primesBelow,
            ((y.factorial).factorization p : ℝ) * Real.log p :=
          Finset.sum_le_sum hterm
      _ ≤ ∑ p ∈ (y.factorial).primeFactors,
            ((y.factorial).factorization p : ℝ) * Real.log p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun p hp _ => hnonneg p hp)
      _ = Real.log (y.factorial) := (log_factorial_eq y).symm
  -- real division against the floor
  have hpt : ∀ p ∈ y.primesBelow, (y:ℝ) * (Real.log p / p)
      ≤ ((y / p : ℕ) : ℝ) * Real.log p + Real.log p := by
    intro p hp
    have h := Nat.mem_primesBelow.mp hp
    have hp0 : (0:ℝ) < p := by exact_mod_cast h.2.pos
    have hlog0 : 0 ≤ Real.log p :=
      Real.log_nonneg (by exact_mod_cast h.2.one_lt.le)
    have hfl : (y:ℝ)/p ≤ ((y / p : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hp0]
      have hdm := Nat.div_add_mod y p
      have hm := Nat.mod_lt y h.2.pos
      have hnat : y < (y/p + 1) * p := by
        have hdm := Nat.div_add_mod y p
        have hm : y % p < p := Nat.mod_lt y h.2.pos
        calc y = p * (y/p) + y % p := hdm.symm
          _ < p * (y/p) + p := by omega
          _ = (y/p + 1) * p := by ring
      have hcast : (y:ℝ) < (((y/p : ℕ) : ℝ) + 1) * p := by
        exact_mod_cast hnat
      linarith
    calc (y:ℝ) * (Real.log p / p) = ((y:ℝ)/p) * Real.log p := by ring
      _ ≤ (((y / p : ℕ) : ℝ) + 1) * Real.log p :=
          mul_le_mul_of_nonneg_right hfl hlog0
      _ = ((y / p : ℕ) : ℝ) * Real.log p + Real.log p := by ring
  have hθ := sum_log_primesBelow_le y
  have hfac := log_factorial_le y
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4:ℝ) = 2^2 from by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    linarith
  have hsum : (y:ℝ) * ∑ p ∈ y.primesBelow, Real.log p / p
      ≤ (y:ℝ) * Real.log y + (y:ℝ) * Real.log 4 := by
    calc (y:ℝ) * ∑ p ∈ y.primesBelow, Real.log p / p
        = ∑ p ∈ y.primesBelow, (y:ℝ) * (Real.log p / p) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ p ∈ y.primesBelow,
            (((y / p : ℕ) : ℝ) * Real.log p + Real.log p) :=
          Finset.sum_le_sum hpt
      _ = (∑ p ∈ y.primesBelow, ((y / p : ℕ) : ℝ) * Real.log p)
            + ∑ p ∈ y.primesBelow, Real.log p := by
          rw [Finset.sum_add_distrib]
      _ ≤ Real.log (y.factorial) + (y:ℝ) * Real.log 4 := by
          have := hθ
          linarith [hfloor]
      _ ≤ (y:ℝ) * Real.log y + (y:ℝ) * Real.log 4 := by
          linarith [hfac]
  have hfinal : ∑ p ∈ y.primesBelow, Real.log p / p
      ≤ Real.log y + Real.log 4 := by
    have h1 := hsum
    have h2 : (y:ℝ) * (Real.log y + Real.log 4)
        = (y:ℝ) * Real.log y + (y:ℝ) * Real.log 4 := by ring
    nlinarith [hy0]
  linarith [hlog4, hfinal,
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ y) : (1:ℝ) ≤ y)]


end MoltResearch
