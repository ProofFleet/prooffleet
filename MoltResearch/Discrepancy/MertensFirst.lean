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


/-- **The linear-weight Abel bound** (Track R, E2-ii-a): for a
monotone sequence `A` with `A j ≤ (5+j)` along the way, the
`1/(2+j)`-weighted increment sum is controlled by the endpoint plus
the split harmonic remainders — summation by parts as an induction
invariant. -/
theorem sum_increment_div_le (A : ℕ → ℝ) (hmono : ∀ j, A j ≤ A (j+1))
    (hb : ∀ j, A j ≤ (5:ℝ) + j) (J : ℕ) :
    ∑ j ∈ Finset.range J, (A (j+1) - A j)/(2 + (j:ℝ))
      ≤ A J/(1 + (J:ℝ)) - A 0
        + ∑ j ∈ Finset.range J,
            (1/(1 + (j:ℝ)) + 3/((1 + (j:ℝ))*(2 + (j:ℝ)))) := by
  induction J with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hK0 : (0:ℝ) < 1 + (K:ℝ) := by positivity
    have hK2 : (0:ℝ) < 2 + (K:ℝ) := by positivity
    have hstep : (A (K+1) - A K)/(2 + (K:ℝ)) + A K/(1 + (K:ℝ))
        ≤ A (K+1)/(1 + ((K:ℕ)+1 : ℝ))
          + (1/(1 + (K:ℝ)) + 3/((1 + (K:ℝ))*(2 + (K:ℝ)))) := by
      have hcast : (1 + ((K:ℕ)+1 : ℝ)) = 2 + (K:ℝ) := by push_cast; ring
      rw [hcast]
      have hAK := hb K
      -- (A(K+1) − AK)/(2+K) + AK/(1+K) − A(K+1)/(2+K)
      --   = AK/(1+K) − AK/(2+K) = AK/((1+K)(2+K)) ≤ (5+K)/((1+K)(2+K))
      --   = 1/(1+K) + 3/((1+K)(2+K))
      have hkey : (A (K+1) - A K)/(2 + (K:ℝ)) + A K/(1 + (K:ℝ))
            - A (K+1)/(2 + (K:ℝ))
          = A K * (1/((1 + (K:ℝ))*(2 + (K:ℝ)))) := by
        field_simp
        ring
      have hsplit : ((5:ℝ) + K) * (1/((1 + (K:ℝ))*(2 + (K:ℝ))))
          = 1/(1 + (K:ℝ)) + 3/((1 + (K:ℝ))*(2 + (K:ℝ))) := by
        field_simp
        ring
      have hAKb : A K * (1/((1 + (K:ℝ))*(2 + (K:ℝ))))
          ≤ ((5:ℝ) + K) * (1/((1 + (K:ℝ))*(2 + (K:ℝ)))) := by
        refine mul_le_mul_of_nonneg_right hAK ?_
        positivity
      linarith [hkey, hsplit, hAKb]
    push_cast
    push_cast at ih
    linarith [ih, hstep]


/-- Per-block mass against the Mertens increment: exact weight
comparison, no θ-bound. -/
theorem sum_block_le_increment (T : ℕ) (hT : 2 ≤ T) :
    ∑ p ∈ (2*T).primesBelow \ T.primesBelow, (1:ℝ)/p
      ≤ ((∑ p ∈ (2*T).primesBelow, Real.log p/p)
          - ∑ p ∈ T.primesBelow, Real.log p/p) / Real.log T := by
  classical
  have hT0 : (0:ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hlogT : (0:ℝ) < Real.log T := by
    refine Real.log_pos ?_
    exact_mod_cast (by omega : 1 < T)
  have hsub : T.primesBelow ⊆ (2*T).primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hdiff : (∑ p ∈ (2*T).primesBelow, Real.log p/p)
        - ∑ p ∈ T.primesBelow, Real.log p/p
      = ∑ p ∈ (2*T).primesBelow \ T.primesBelow, Real.log p/p :=
    (Finset.sum_sdiff_eq_sub hsub).symm
  rw [hdiff, Finset.sum_div]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [Finset.mem_sdiff, Nat.mem_primesBelow] at hp
  have hpT : T ≤ p := by
    by_contra h
    exact hp.2 (Nat.mem_primesBelow.mpr ⟨by omega, hp.1.2⟩)
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.1.2.pos
  have hlogp : Real.log T ≤ Real.log p :=
    Real.log_le_log hT0 (by exact_mod_cast hpT)
  rw [div_div, div_le_div_iff₀ hp0 (by positivity)]
  calc (1:ℝ) * (p * Real.log T) = p * Real.log T := by ring
    _ ≤ p * Real.log p := mul_le_mul_of_nonneg_left hlogp hp0.le
    _ = Real.log p * p := by ring


/-- **The sharp Mertens mass bound** (Track R, E2-ii): the prime
harmonic mass has leading constant one — `∑_{p<y} 1/p ≤ loglog y + 11`
for `y ≥ 4`. Dyadic blocks against the sharp first Mertens theorem
through the linear-weight Abel bound. -/
theorem sum_one_div_primesBelow_le_sharp (y : ℕ) (hy : 4 ≤ y) :
    ∑ p ∈ y.primesBelow, (1:ℝ)/p ≤ Real.log (Real.log y) + 11 := by
  classical
  set J : ℕ := Nat.log 2 y with hJ_def
  have hJ2 : 2 ≤ J := by
    rw [hJ_def]
    have := (Nat.le_log_iff_pow_le (by norm_num) (by omega : y ≠ 0)).mpr
      (by omega : 2^2 ≤ y)
    omega
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lb : (0.6:ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlog2_ub : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  -- the Mertens partial sums on the block scale, normalized
  set A : ℕ → ℝ := fun j => ∑ p ∈ (4*2^j).primesBelow,
      (fun n : ℕ => Real.log n / n) p
    with hA_def
  set At : ℕ → ℝ := fun j => A j / Real.log 2 with hAt_def
  have hT4 : ∀ j : ℕ, 4 ≤ 4*2^j := by
    intro j
    have : 1 ≤ 2^j := Nat.one_le_pow j 2 (by norm_num)
    nlinarith
  have hlogT : ∀ j : ℕ, Real.log ((4*2^j : ℕ):ℝ) = Real.log 2 * (2 + j) := by
    intro j
    push_cast
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
      show (4:ℝ) = 2^2 from by norm_num, Real.log_pow]
    push_cast
    ring
  -- monotone and bounded (sharp Mertens)
  have hAmono : ∀ j, At j ≤ At (j+1) := by
    intro j
    have hsub : (4*2^j).primesBelow ⊆ (4*2^(j+1)).primesBelow := by
      intro p hp
      rw [Nat.mem_primesBelow] at hp ⊢
      refine ⟨?_, hp.2⟩
      have h1 : (4*2^j) ≤ 4*2^(j+1) := by
        have : 2^j ≤ 2^(j+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      omega
    have hAj : A j ≤ A (j+1) := by
      rw [hA_def]
      dsimp only
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_
      have hpp := Nat.prime_of_mem_primesBelow hp
      have h1 : (1:ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
      have := Real.log_nonneg h1
      positivity
    rw [hAt_def]
    exact div_le_div_of_nonneg_right hAj hlog2pos.le
  have hAbd : ∀ j, At j ≤ (5:ℝ) + j := by
    intro j
    rw [hAt_def, div_le_iff₀ hlog2pos]
    have hsharp := sum_log_div_primesBelow_le_sharp (4*2^j) (by
      have := hT4 j
      omega)
    rw [hA_def]
    dsimp only
    refine le_trans hsharp ?_
    rw [hlogT j]
    have hd9 := Real.log_two_gt_d9
    have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    nlinarith
  -- cover the tail by blocks and apply the increment bound
  have hcover_bound : ∑ p ∈ y.primesBelow \ (4:ℕ).primesBelow, (1:ℝ)/p
      ≤ ∑ j ∈ Finset.range J, (At (j+1) - At j)/(2 + (j:ℝ)) := by
    have hstep1 : y.primesBelow \ (4:ℕ).primesBelow
        ⊆ (Finset.range J).biUnion
            (fun j => (4*2^(j+1)).primesBelow \ (4*2^j).primesBelow) := by
      intro p hp
      rw [Finset.mem_sdiff, Nat.mem_primesBelow] at hp
      have hp4 : 4 ≤ p := by
        by_contra h
        exact hp.2 (Nat.mem_primesBelow.mpr ⟨by omega, hp.1.2⟩)
      set j : ℕ := Nat.log 2 (p/4) with hj_def
      have hlow : 4*2^j ≤ p := by
        have h1 : 2^j ≤ p/4 := Nat.pow_log_le_self 2 (by
          have : 1 ≤ p/4 := (Nat.one_le_div_iff (by norm_num)).mpr hp4
          omega)
        calc 4*2^j ≤ 4*(p/4) := Nat.mul_le_mul_left 4 h1
          _ ≤ p := Nat.mul_div_le p 4
      have hhigh : p < 4*2^(j+1) := by
        have h1 : p/4 < 2^(j+1) := Nat.lt_pow_succ_log_self (by norm_num) _
        have h2 : p < 4*(p/4) + 4 := by
          have := Nat.div_add_mod p 4
          have : p % 4 < 4 := Nat.mod_lt p (by norm_num)
          omega
        have h3 : 4*(p/4) + 4 = 4*(p/4 + 1) := by ring
        calc p < 4*(p/4) + 4 := h2
          _ = 4*(p/4 + 1) := h3
          _ ≤ 4*2^(j+1) := Nat.mul_le_mul_left 4 (by omega)
      have hjJ : j < J := by
        rw [hJ_def, hj_def]
        have h1 : Nat.log 2 (p/4) ≤ Nat.log 2 (y/4) :=
          Nat.log_mono_right (Nat.div_le_div_right (by omega))
        have h2 : Nat.log 2 (y/4) + 2 ≤ Nat.log 2 y := by
          have h3 : 2^(Nat.log 2 (y/4) + 2) ≤ y := by
            have h4 : 2^(Nat.log 2 (y/4)) ≤ y/4 :=
              Nat.pow_log_le_self 2 (by
                have : 1 ≤ y/4 := (Nat.one_le_div_iff (by norm_num)).mpr hy
                omega)
            calc 2^(Nat.log 2 (y/4) + 2) = 4 * 2^(Nat.log 2 (y/4)) := by ring
              _ ≤ 4 * (y/4) := Nat.mul_le_mul_left 4 h4
              _ ≤ y := Nat.mul_div_le y 4
          exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr h3
        omega
      rw [Finset.mem_biUnion]
      refine ⟨j, Finset.mem_range.mpr hjJ, ?_⟩
      rw [Finset.mem_sdiff, Nat.mem_primesBelow]
      refine ⟨⟨hhigh, hp.1.2⟩, ?_⟩
      intro hmem
      rw [Nat.mem_primesBelow] at hmem
      omega
    have hdisj_aux : ∀ j k : ℕ, j < k →
        Disjoint ((4*2^(j+1)).primesBelow \ (4*2^j).primesBelow)
          ((4*2^(k+1)).primesBelow \ (4*2^k).primesBelow) := by
      intro j k hjk
      refine Finset.disjoint_left.mpr fun p hpj hpk => ?_
      rw [Finset.mem_sdiff, Nat.mem_primesBelow] at hpj hpk
      have h1 : p < 4*2^(j+1) := hpj.1.1
      have h2 : 4*2^k ≤ p := by
        by_contra h
        exact hpk.2 (Nat.mem_primesBelow.mpr ⟨by omega, hpk.1.2⟩)
      have h3 : 4*2^(j+1) ≤ 4*2^k :=
        Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by norm_num) (by omega))
      omega
    have hdisj : Set.PairwiseDisjoint ↑(Finset.range J)
        (fun j => (4*2^(j+1)).primesBelow \ (4*2^j).primesBelow) := by
      intro j _ k _ hjk
      rcases lt_or_gt_of_ne hjk with h | h
      · exact hdisj_aux j k h
      · exact (hdisj_aux k j h).symm
    refine le_trans (le_trans (Finset.sum_le_sum_of_subset_of_nonneg hstep1
      (fun p _ _ => by positivity)) (le_of_eq (Finset.sum_biUnion hdisj))) ?_
    refine Finset.sum_le_sum fun j _ => ?_
    have hblock := sum_block_le_increment (4*2^j) (by
      have := hT4 j
      omega)
    have heq2 : 2*(4*2^j) = 4*2^(j+1) := by ring
    rw [heq2, hlogT j] at hblock
    refine le_trans hblock (le_of_eq ?_)
    rw [hAt_def]
    dsimp only
    rw [div_sub_div_same, div_div]
  -- assemble
  have h4sub : (4:ℕ).primesBelow ⊆ y.primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hsplit : ∑ p ∈ y.primesBelow, (1:ℝ)/p
      = (∑ p ∈ (4:ℕ).primesBelow, (1:ℝ)/p)
        + ∑ p ∈ y.primesBelow \ (4:ℕ).primesBelow, (1:ℝ)/p := by
    rw [← Finset.sum_sdiff h4sub]
    ring
  have hmass4 : ∑ p ∈ (4:ℕ).primesBelow, (1:ℝ)/p ≤ 1 := by
    have h4 : (4:ℕ).primesBelow = {2, 3} := by decide
    rw [h4, Finset.sum_insert (by norm_num), Finset.sum_singleton]
    norm_num
  have habel := sum_increment_div_le At hAmono hAbd J
  have hAt0 : (0:ℝ) ≤ At 0 := by
    rw [hAt_def]
    dsimp only
    refine div_nonneg ?_ hlog2pos.le
    rw [hA_def]
    dsimp only
    refine Finset.sum_nonneg fun p hp => ?_
    have hpp := Nat.prime_of_mem_primesBelow hp
    have h1 : (1:ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have := Real.log_nonneg h1
    positivity
  have hend : At J/(1 + (J:ℝ)) ≤ 5 := by
    have hJ0 : (0:ℝ) < 1 + (J:ℝ) := by positivity
    have h1 : At J ≤ (5:ℝ) + J := hAbd J
    rw [div_le_iff₀ hJ0]
    have hJc : (0:ℝ) ≤ (J:ℝ) := Nat.cast_nonneg J
    nlinarith
  have hharm : ∑ j ∈ Finset.range J, 1/(1 + (j:ℝ))
      ≤ 1 + Real.log J := by
    have hJeq : J = (J-1) + 1 := by omega
    have hJsplit : ∑ j ∈ Finset.range J, 1/(1 + (j:ℝ))
        = 1 + ∑ i ∈ Finset.range (J-1), 1/(2 + (i:ℝ)) := by
      conv_lhs => rw [hJeq, Finset.sum_range_succ']
      have hterm : ∀ i ∈ Finset.range (J-1),
          1/(1 + ((i+1 : ℕ):ℝ)) = 1/(2 + (i:ℝ)) := by
        intro i _
        push_cast
        ring_nf
      rw [Finset.sum_congr rfl hterm]
      norm_num
      ring
    rw [hJsplit]
    have htel := sum_one_div_add_le_log 2 (le_refl 2) (J-1)
    have hcast : (2:ℝ) + ((J-1 : ℕ):ℝ) - 1 = (J:ℝ) := by
      have : ((J-1 : ℕ):ℝ) = (J:ℝ) - 1 := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ J)]
        ring
      rw [this]
      ring
    rw [hcast] at htel
    have hlog1 : Real.log (2 - 1 : ℝ) = 0 := by norm_num
    rw [hlog1] at htel
    linarith
  have htele : ∑ j ∈ Finset.range J, 3/((1 + (j:ℝ))*(2 + (j:ℝ))) ≤ 3 := by
    have hpt : ∀ j ∈ Finset.range J,
        3/((1 + (j:ℝ))*(2 + (j:ℝ)))
          = 3 * ((fun k : ℕ => 1/(1 + (k:ℝ))) j
              - (fun k : ℕ => 1/(1 + (k:ℝ))) (j+1)) := by
      intro j _
      dsimp only
      have h1 : (0:ℝ) < 1 + (j:ℝ) := by positivity
      have h2 : (0:ℝ) < 2 + (j:ℝ) := by positivity
      push_cast
      field_simp
      ring
    rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum,
      Finset.sum_range_sub' (fun k : ℕ => 1/(1 + (k:ℝ)))]
    have hJ0 : (0:ℝ) < 1 + (J:ℝ) := by positivity
    have : (0:ℝ) ≤ 1/(1 + (J:ℝ)) := by positivity
    norm_num
    linarith
  have hlogy_pos : (1:ℝ) < Real.log y := by
    have h4 : Real.log 4 ≤ Real.log y :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hy)
    rw [show (4:ℝ) = 2^2 from by norm_num, Real.log_pow] at h4
    push_cast at h4
    nlinarith
  have hlogJ : Real.log J ≤ 1 + Real.log (Real.log y) := by
    have hJle : (J:ℝ) ≤ 2*Real.log y := by
      have h1 : (2:ℕ)^J ≤ y := by
        rw [hJ_def]
        exact Nat.pow_log_le_self 2 (by omega)
      have h2 : (J:ℝ) * Real.log 2 ≤ Real.log y := by
        have h3 : Real.log ((2:ℕ)^J : ℕ) ≤ Real.log y :=
          Real.log_le_log (by positivity) (by exact_mod_cast h1)
        rw [show (((2:ℕ)^J : ℕ):ℝ) = (2:ℝ)^J from by push_cast; ring,
          Real.log_pow] at h3
        push_cast at h3
        linarith
      nlinarith
    have hJpos : (0:ℝ) < J := by
      have : (2:ℝ) ≤ J := by exact_mod_cast hJ2
      linarith
    calc Real.log J ≤ Real.log (2*Real.log y) :=
          Real.log_le_log hJpos hJle
      _ = Real.log 2 + Real.log (Real.log y) := by
          rw [Real.log_mul (by norm_num) (by linarith)]
      _ ≤ 1 + Real.log (Real.log y) := by linarith
  -- total
  have hsum_split : ∑ j ∈ Finset.range J,
      (1/(1 + (j:ℝ)) + 3/((1 + (j:ℝ))*(2 + (j:ℝ))))
        = (∑ j ∈ Finset.range J, 1/(1 + (j:ℝ)))
          + ∑ j ∈ Finset.range J, 3/((1 + (j:ℝ))*(2 + (j:ℝ))) :=
    Finset.sum_add_distrib
  rw [hsplit]
  have hchain := le_trans hcover_bound habel
  rw [hsum_split] at hchain
  linarith [hmass4, hchain, hend, hAt0, hharm, htele, hlogJ]




end MoltResearch
