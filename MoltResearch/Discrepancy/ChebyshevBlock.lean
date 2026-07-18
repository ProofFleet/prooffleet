import MoltResearch.Discrepancy.ChebyshevTail
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Central

/-!
# Discrepancy: the Chebyshev block lower bound

Track C, Elliott campaign (`Problems/tao2015_derivation_c.md`, issue #2946, E5-pre):
primes in a dyadic block carry substantial log-mass —

  `θ(2n) − θ(n) ≥ (log 4 / 6) · n`  for `n ≥ 2²⁸`,

hence `∑_{n < p ≤ 2n} 1/p ≥ (log 4 / 12)/log(2n)`. This is the prime-counting **lower**
bound that Proposition `conv` of arXiv:1509.05422 consumes (`∑_{p ∈ P_H} 1/p ≫ 1/log H`);
Mathlib has Bertrand's postulate and Chebyshev upper bounds, but no lower bound.

The proof is Erdős's central-binomial decomposition, fully elementary: every prime
factor of `C(2n,n)` is at most `2n`; factors `p ≤ √(2n)` contribute at most `log (2n)`
each; factors `√(2n) < p ≤ 2n/3` appear at most once and are controlled by the
Chebyshev upper bound `θ ≤ y log 4`; factors `2n/3 < p ≤ n` do not appear at all; what
remains is the block. The lower bound `4ⁿ < n·C(2n,n)` and the calculus-free estimate
`log x ≤ 4·x^{1/4}` close the ledger with room to spare at `n ≥ 2²⁸`.
-/

namespace MoltResearch

open Finset

/-- Calculus-free logarithm bound: `log x ≤ 4·x^{1/4}` for `x ≥ 1`
(from `log t ≤ t − 1` at `t = x^{1/4}`). -/
theorem log_le_four_mul_rpow {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 4 * x ^ ((1 : ℝ) / 4) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hq : x ^ ((1 : ℝ) / 4) > 0 := Real.rpow_pos_of_pos hx0 _
  have hlog : Real.log (x ^ ((1 : ℝ) / 4)) = (1 / 4) * Real.log x :=
    Real.log_rpow hx0 _
  have hle := Real.log_le_sub_one_of_pos hq
  have h4 : Real.log x = 4 * Real.log (x ^ ((1 : ℝ) / 4)) := by
    rw [hlog]
    ring
  rw [h4]
  nlinarith [hq]

/-- The log-mass of the primes in the dyadic block `(n, 2n]`. -/
noncomputable def blockLog (n : ℕ) : ℝ :=
  ∑ p ∈ (2 * n + 1).primesBelow.filter (fun p => n < p), Real.log p

set_option maxHeartbeats 1600000 in
/-- **The Chebyshev block lower bound**: `θ(2n) − θ(n) ≥ (log 4 / 6)·n` for
`n ≥ 2²⁸` — Erdős's central-binomial decomposition, fully elementary. -/
theorem blockLog_ge {n : ℕ} (hn : 2 ^ 28 ≤ n) :
    (n : ℝ) * Real.log 4 / 6 ≤ blockLog n := by
  classical
  have hn2 : 2 < n := lt_of_lt_of_le (by norm_num) hn
  have hn0 : 0 < n := by omega
  have hn0R : (0 : ℝ) < n := by exact_mod_cast hn0
  have h2n0 : 0 < 2 * n := by omega
  set C : ℕ := Nat.centralBinom n with hC
  have hC0 : C ≠ 0 := Nat.centralBinom_ne_zero n
  -- the log of the central binomial as a prime decomposition below 2n+1
  have hsupp : ∀ p ∉ (2 * n + 1).primesBelow, p.Prime → C.factorization p = 0 := by
    intro p hp hpp
    have h2n : 2 * n < p := by
      by_contra hle
      push_neg at hle
      exact hp (Nat.mem_primesBelow.mpr ⟨by omega, hpp⟩)
    rw [hC, Nat.centralBinom_eq_two_mul_choose]
    exact Nat.factorization_choose_eq_zero_of_lt (by omega)
  have hlogC : Real.log C
      = ∑ p ∈ (2 * n + 1).primesBelow, (C.factorization p : ℝ) * Real.log p := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hC0]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
    rw [show ((∏ p ∈ C.primeFactors, p ^ C.factorization p : ℕ) : ℝ)
        = ∏ p ∈ C.primeFactors, ((p : ℝ)) ^ C.factorization p from by push_cast; rfl]
    rw [Real.log_prod (fun p hp => by
      have hpp := Nat.prime_of_mem_primeFactors hp
      have : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      positivity)]
    rw [show ∀ s : Finset ℕ, (∑ p ∈ s, Real.log ((p : ℝ) ^ C.factorization p))
        = ∑ p ∈ s, (C.factorization p : ℝ) * Real.log p from fun s =>
      Finset.sum_congr rfl fun p _ => by rw [Real.log_pow]]
    refine Finset.sum_subset ?_ ?_
    · intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      by_contra hnot
      have h0 := hsupp p hnot hpp
      rw [← Nat.support_factorization] at hp
      exact (Finsupp.mem_support_iff.mp hp) h0
    · intro p _ hp
      have h0 : C.factorization p = 0 := by
        by_contra hne
        have : p ∈ C.primeFactors := by
          rw [← Nat.support_factorization]
          exact Finsupp.mem_support_iff.mpr hne
        exact hp this
      rw [h0]
      simp
  -- lower bound on log C from 4^n < n · C
  have h4pow : (n : ℝ) * Real.log 4 - Real.log n ≤ Real.log C := by
    have h := Nat.four_pow_lt_mul_centralBinom n (by omega)
    have hlt : ((4 : ℕ) ^ n : ℝ) ≤ ((n * C : ℕ) : ℝ) := by exact_mod_cast h.le
    have hlog := Real.log_le_log (by positivity) hlt
    rw [show ((4 : ℕ) ^ n : ℝ) = (4 : ℝ) ^ n from by push_cast; rfl,
      Real.log_pow] at hlog
    rw [show ((n * C : ℕ) : ℝ) = (n : ℝ) * (C : ℝ) from by push_cast; rfl,
      Real.log_mul (ne_of_gt hn0R) (by exact_mod_cast hC0)] at hlog
    linarith
  -- split the decomposition at the three cuts
  set P := (2 * n + 1).primesBelow with hP
  set s : ℕ := Nat.sqrt (2 * n) with hs
  have hsplit4 : ∑ p ∈ P.filter (fun p => n < p),
      (C.factorization p : ℝ) * Real.log p ≤ blockLog n := by
    rw [blockLog, ← hP]
    refine Finset.sum_le_sum fun p hp => ?_
    rw [Finset.mem_filter] at hp
    have hpp := Nat.prime_of_mem_primesBelow hp.1
    have hnu : C.factorization p ≤ 1 := by
      rw [hC, Nat.centralBinom_eq_two_mul_choose]
      refine Nat.factorization_choose_le_one ?_
      nlinarith [hp.2, hn2]
    have hlogp : (0 : ℝ) ≤ Real.log p :=
      Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have : (C.factorization p : ℝ) ≤ 1 := by exact_mod_cast hnu
    nlinarith
  have hsplit3 : ∀ p ∈ P.filter (fun p => 2 * n / 3 < p ∧ p ≤ n),
      (C.factorization p : ℝ) * Real.log p = 0 := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have h0 : C.factorization p = 0 := by
      rw [hC]
      exact Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul
        hn2 hp.2.2 (by omega)
    rw [h0]
    simp
  have hsplit2 : ∑ p ∈ P.filter (fun p => s < p ∧ p ≤ 2 * n / 3),
      (C.factorization p : ℝ) * Real.log p
        ≤ (2 * (n : ℝ) / 3 + 1) * Real.log 4 := by
    have hle1 : ∀ p ∈ P.filter (fun p => s < p ∧ p ≤ 2 * n / 3),
        (C.factorization p : ℝ) * Real.log p ≤ Real.log p := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hpp := Nat.prime_of_mem_primesBelow hp.1
      have hnu : C.factorization p ≤ 1 := by
        rw [hC, Nat.centralBinom_eq_two_mul_choose]
        refine Nat.factorization_choose_le_one ?_
        have := Nat.lt_succ_sqrt (2 * n)
        have hsq : s + 1 ≤ p := hp.2.1
        nlinarith [hp.2.1]
      have hlogp : (0 : ℝ) ≤ Real.log p :=
        Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
      have : (C.factorization p : ℝ) ≤ 1 := by exact_mod_cast hnu
      nlinarith
    refine le_trans (Finset.sum_le_sum hle1) ?_
    have hsub : P.filter (fun p => s < p ∧ p ≤ 2 * n / 3)
        ⊆ (2 * n / 3 + 1).primesBelow := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_of_mem_primesBelow hp.1⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
      Real.log_nonneg (by
        exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt.le)) ?_
    refine le_trans (sum_log_primesBelow_le (2 * n / 3 + 1)) ?_
    have hcast : ((2 * n / 3 + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) / 3 + 1 := by
      have h1 : (2 * n / 3 : ℕ) ≤ 2 * n / 3 := le_refl _
      have h2 : ((2 * n / 3 : ℕ) : ℝ) ≤ (2 * n : ℕ) / 3 := by
        rw [show ((2 * n : ℕ) : ℝ) / 3 = ((2 * n : ℕ) : ℝ) / ((3 : ℕ) : ℝ) from by
          norm_num]
        exact Nat.cast_div_le
      push_cast at h2 ⊢
      linarith
    have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    nlinarith
  have hsplit1 : ∑ p ∈ P.filter (fun p => p ≤ s),
      (C.factorization p : ℝ) * Real.log p
        ≤ 2 * Real.sqrt (2 * n) * Real.log (2 * n) := by
    have hterm : ∀ p ∈ P.filter (fun p => p ≤ s),
        (C.factorization p : ℝ) * Real.log p ≤ Real.log (2 * n) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hpp := Nat.prime_of_mem_primesBelow hp.1
      have hpow : p ^ C.factorization p ≤ 2 * n := by
        rw [hC, Nat.centralBinom_eq_two_mul_choose]
        exact Nat.pow_factorization_choose_le h2n0
      have hcast : ((p : ℝ)) ^ C.factorization p ≤ (2 * (n : ℝ)) := by
        rw [show ((p : ℝ)) ^ C.factorization p = ((p ^ C.factorization p : ℕ) : ℝ)
          from by push_cast; rfl]
        exact_mod_cast hpow
      have hlogpow := Real.log_le_log (by
        have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
        positivity) hcast
      rw [Real.log_pow] at hlogpow
      linarith
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
    rw [nsmul_eq_mul]
    have hcard : ((P.filter (fun p => p ≤ s)).card : ℝ) ≤ 2 * Real.sqrt (2 * n) := by
      have hsub : P.filter (fun p => p ≤ s) ⊆ Finset.Icc 2 s := by
        intro p hp
        rw [Finset.mem_filter] at hp
        rw [Finset.mem_Icc]
        exact ⟨(Nat.prime_of_mem_primesBelow hp.1).two_le, hp.2⟩
      have h1 : (P.filter (fun p => p ≤ s)).card ≤ s := by
        calc (P.filter (fun p => p ≤ s)).card ≤ (Finset.Icc 2 s).card :=
              Finset.card_le_card hsub
          _ ≤ s := by rw [Nat.card_Icc]; omega
      have h2 : ((s : ℕ) : ℝ) ≤ Real.sqrt (2 * n) := by
        rw [hs]
        have hle : ((Nat.sqrt (2 * n) : ℕ) : ℝ) ^ 2 ≤ ((2 * n : ℕ) : ℝ) := by
          exact_mod_cast Nat.sqrt_le' (2 * n)
        have h0 : (0 : ℝ) ≤ ((Nat.sqrt (2 * n) : ℕ) : ℝ) := Nat.cast_nonneg _
        calc ((Nat.sqrt (2 * n) : ℕ) : ℝ)
            = Real.sqrt (((Nat.sqrt (2 * n) : ℕ) : ℝ) ^ 2) := (Real.sqrt_sq h0).symm
          _ ≤ Real.sqrt ((2 * n : ℕ) : ℝ) := Real.sqrt_le_sqrt hle
          _ = Real.sqrt (2 * (n : ℝ)) := by push_cast; rfl
      have h3 : (0 : ℝ) ≤ Real.sqrt (2 * n) := Real.sqrt_nonneg _
      calc ((P.filter (fun p => p ≤ s)).card : ℝ) ≤ (s : ℝ) := by exact_mod_cast h1
        _ ≤ Real.sqrt (2 * n) := h2
        _ ≤ 2 * Real.sqrt (2 * n) := by linarith
    have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
    have hlog2n : (0 : ℝ) ≤ Real.log (2 * (n : ℝ)) := by
      refine Real.log_nonneg ?_
      linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hcard) hlog2n]
  -- the four-way partition of the decomposition sum
  have hpartition : ∑ p ∈ P, (C.factorization p : ℝ) * Real.log p
      ≤ 2 * Real.sqrt (2 * n) * Real.log (2 * n)
        + (2 * (n : ℝ) / 3 + 1) * Real.log 4 + blockLog n := by
    have hnonneg : ∀ p ∈ P, (0 : ℝ) ≤ (C.factorization p : ℝ) * Real.log p := by
      intro p hp
      have hpp := Nat.prime_of_mem_primesBelow hp
      have := Real.log_nonneg (show (1:ℝ) ≤ p by exact_mod_cast hpp.one_lt.le)
      positivity
    -- classify each prime into one of the four ranges
    have hcover : ∀ p ∈ P, (p ≤ s) ∨ (s < p ∧ p ≤ 2 * n / 3)
        ∨ (2 * n / 3 < p ∧ p ≤ n) ∨ (n < p) := by
      intro p _
      omega
    -- three successive filter splits
    rw [← Finset.sum_filter_add_sum_filter_not P (fun p => n < p)]
    have hrest : ∑ p ∈ P.filter (fun p => ¬ n < p),
        (C.factorization p : ℝ) * Real.log p
          ≤ 2 * Real.sqrt (2 * n) * Real.log (2 * n)
            + (2 * (n : ℝ) / 3 + 1) * Real.log 4 := by
      rw [← Finset.sum_filter_add_sum_filter_not (P.filter (fun p => ¬ n < p))
        (fun p => p ≤ s)]
      have hA : (P.filter (fun p => ¬ n < p)).filter (fun p => p ≤ s)
          ⊆ P.filter (fun p => p ≤ s) := by
        intro p hp
        rw [Finset.mem_filter] at hp ⊢
        rw [Finset.mem_filter] at hp
        exact ⟨hp.1.1, hp.2⟩
      have hA2 : ∑ p ∈ (P.filter (fun p => ¬ n < p)).filter (fun p => p ≤ s),
          (C.factorization p : ℝ) * Real.log p
            ≤ 2 * Real.sqrt (2 * n) * Real.log (2 * n) := by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hA fun p hp _ =>
          hnonneg p (Finset.mem_filter.mp hp).1) hsplit1
      have hB : ∑ p ∈ (P.filter (fun p => ¬ n < p)).filter (fun p => ¬ p ≤ s),
          (C.factorization p : ℝ) * Real.log p
            ≤ (2 * (n : ℝ) / 3 + 1) * Real.log 4 := by
        have hBsub : (P.filter (fun p => ¬ n < p)).filter (fun p => ¬ p ≤ s)
            ⊆ (P.filter (fun p => s < p ∧ p ≤ 2 * n / 3))
              ∪ (P.filter (fun p => 2 * n / 3 < p ∧ p ≤ n)) := by
          intro p hp
          rw [Finset.mem_filter, Finset.mem_filter] at hp
          rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
          rcases Nat.lt_or_ge (2 * n / 3) p with h | h
          · exact Or.inr ⟨hp.1.1, h, by omega⟩
          · exact Or.inl ⟨hp.1.1, by omega, h⟩
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hBsub fun p hp _ => by
          rw [Finset.mem_union] at hp
          rcases hp with hp | hp
          · exact hnonneg p (Finset.mem_filter.mp hp).1
          · exact hnonneg p (Finset.mem_filter.mp hp).1) ?_
        have hdisj : Disjoint (P.filter (fun p => s < p ∧ p ≤ 2 * n / 3))
            (P.filter (fun p => 2 * n / 3 < p ∧ p ≤ n)) := by
          refine Finset.disjoint_left.mpr fun p hpA hpB => ?_
          rw [Finset.mem_filter] at hpA hpB
          omega
        rw [Finset.sum_union hdisj]
        rw [show ∑ p ∈ P.filter (fun p => 2 * n / 3 < p ∧ p ≤ n),
            (C.factorization p : ℝ) * Real.log p = 0 from
          Finset.sum_eq_zero hsplit3]
        linarith [hsplit2]
      linarith
    linarith [hsplit4, hrest]
  -- assemble the error ledger at n ≥ 2^28
  have hkey : (n : ℝ) * Real.log 4 - Real.log n
      ≤ 2 * Real.sqrt (2 * n) * Real.log (2 * n)
        + (2 * (n : ℝ) / 3 + 1) * Real.log 4 + blockLog n :=
    le_trans h4pow (by rw [hlogC]; exact hpartition)
  -- error bounds via log x ≤ 4 x^{1/4}
  have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
  have hnq : (0 : ℝ) < 2 * (n : ℝ) := by linarith
  have hlog2n_le : Real.log (2 * (n : ℝ)) ≤ 4 * (2 * (n : ℝ)) ^ ((1 : ℝ) / 4) :=
    log_le_four_mul_rpow (by linarith)
  have hsqrt_eq : Real.sqrt (2 * (n : ℝ)) = (2 * (n : ℝ)) ^ ((1 : ℝ) / 2) :=
    Real.sqrt_eq_rpow _
  have herr1 : 2 * Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ))
      ≤ 8 * (2 * (n : ℝ)) ^ ((3 : ℝ) / 4) := by
    rw [hsqrt_eq]
    have hq0 : (0 : ℝ) ≤ (2 * (n : ℝ)) ^ ((1 : ℝ) / 2) := by positivity
    have hmul : (2 * (n : ℝ)) ^ ((1 : ℝ) / 2) * (2 * (n : ℝ)) ^ ((1 : ℝ) / 4)
        = (2 * (n : ℝ)) ^ ((3 : ℝ) / 4) := by
      rw [← Real.rpow_add hnq]
      norm_num
    calc 2 * (2 * (n : ℝ)) ^ ((1 : ℝ) / 2) * Real.log (2 * (n : ℝ))
        ≤ 2 * (2 * (n : ℝ)) ^ ((1 : ℝ) / 2) * (4 * (2 * (n : ℝ)) ^ ((1 : ℝ) / 4)) := by
          have h2q : (0 : ℝ) ≤ 2 * (2 * (n : ℝ)) ^ ((1 : ℝ) / 2) := by positivity
          nlinarith [hlog2n_le]
      _ = 8 * ((2 * (n : ℝ)) ^ ((1 : ℝ) / 2) * (2 * (n : ℝ)) ^ ((1 : ℝ) / 4)) := by ring
      _ = 8 * (2 * (n : ℝ)) ^ ((3 : ℝ) / 4) := by rw [hmul]
  -- (2n)^{3/4} ≤ 2 n^{3/4} and n^{3/4} ≤ n/128 for n ≥ 2^28
  have hn34 : (2 * (n : ℝ)) ^ ((3 : ℝ) / 4) ≤ 2 * (n : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [Real.mul_rpow (by norm_num) hn0R.le]
    have h2r : (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 := by
      calc (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ (2 : ℝ) ^ ((1 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hpos : (0 : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 4) := by positivity
    nlinarith
  have hquarter : (2 : ℝ) ^ ((7 : ℝ)) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := by
    have hcast : ((2 : ℝ) ^ (28 : ℕ)) ≤ (n : ℝ) := by exact_mod_cast hn
    calc (2 : ℝ) ^ ((7 : ℝ)) = ((2 : ℝ) ^ (28 : ℕ)) ^ ((1 : ℝ) / 4) := by
          rw [← Real.rpow_natCast (2 : ℝ) 28, ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ (n : ℝ) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow (by positivity) hcast (by norm_num)
  have hn34_le : (n : ℝ) ^ ((3 : ℝ) / 4) ≤ (n : ℝ) / 128 := by
    have hsplit : (n : ℝ) = (n : ℝ) ^ ((3 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_add hn0R]
      norm_num
    have h34pos : (0 : ℝ) < (n : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hn0R _
    have h128 : (128 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := by
      have h27 : (2 : ℝ) ^ ((7 : ℝ)) = 128 := by
        rw [show ((7 : ℝ)) = ((7 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
        norm_num
      linarith [hquarter]
    have hmul : (n : ℝ) ^ ((3 : ℝ) / 4) * 128 ≤ (n : ℝ) := by
      calc (n : ℝ) ^ ((3 : ℝ) / 4) * 128
          ≤ (n : ℝ) ^ ((3 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4) := by nlinarith
        _ = (n : ℝ) := hsplit.symm
    linarith
  -- log n ≤ 4 n^{1/4} ≤ n/2^{19} (crude)
  have hlogn : Real.log (n : ℝ) ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4) :=
    log_le_four_mul_rpow (by exact_mod_cast Nat.one_le_of_lt hn2)
  have hn14_small : 4 * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ (n : ℝ) / 128 := by
    have hsplit : (n : ℝ) = (n : ℝ) ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((3 : ℝ) / 4) := by
      rw [← Real.rpow_add hn0R]
      norm_num
    have h34 : (2 : ℝ) ^ ((21 : ℝ)) ≤ (n : ℝ) ^ ((3 : ℝ) / 4) := by
      have hcast : ((2 : ℝ) ^ (28 : ℕ)) ≤ (n : ℝ) := by exact_mod_cast hn
      calc (2 : ℝ) ^ ((21 : ℝ)) = ((2 : ℝ) ^ (28 : ℕ)) ^ ((3 : ℝ) / 4) := by
            rw [← Real.rpow_natCast (2 : ℝ) 28, ← Real.rpow_mul (by norm_num)]
            norm_num
        _ ≤ (n : ℝ) ^ ((3 : ℝ) / 4) :=
            Real.rpow_le_rpow (by positivity) hcast (by norm_num)
    have h21 : (2 : ℝ) ^ ((21 : ℝ)) = 2097152 := by
      rw [show ((21 : ℝ)) = ((21 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
      norm_num
    have h14pos : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hn0R _
    have hbig : 512 ≤ (n : ℝ) ^ ((3 : ℝ) / 4) := by linarith
    have : 4 * (n : ℝ) ^ ((1 : ℝ) / 4) * 128
        ≤ (n : ℝ) ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((3 : ℝ) / 4) := by nlinarith
    rw [← hsplit] at this
    linarith
  -- numeric close: log 4 bounds
  have hlog4_lb : (1.386 : ℝ) ≤ Real.log 4 := by
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]
      push_cast
      ring
    have := Real.log_two_gt_d9
    rw [h2]
    linarith
  have hlog4_ub : Real.log 4 ≤ (1.39 : ℝ) := by
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]
      push_cast
      ring
    have := Real.log_two_lt_d9
    rw [h2]
    linarith
  -- final ledger
  have herr_total : 2 * Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ))
      + Real.log (n : ℝ) + Real.log 4
      ≤ (n : ℝ) * Real.log 4 / 6 := by
    have h1 : 2 * Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ))
        ≤ 16 * ((n : ℝ) / 128) := by
      calc 2 * Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ))
          ≤ 8 * (2 * (n : ℝ)) ^ ((3 : ℝ) / 4) := herr1
        _ ≤ 8 * (2 * (n : ℝ) ^ ((3 : ℝ) / 4)) := by linarith [hn34]
        _ = 16 * (n : ℝ) ^ ((3 : ℝ) / 4) := by ring
        _ ≤ 16 * ((n : ℝ) / 128) := by linarith [hn34_le]
    have h2 : Real.log (n : ℝ) ≤ (n : ℝ) / 128 := le_trans hlogn hn14_small
    have h3 : Real.log 4 ≤ (n : ℝ) / 128 := by
      have : (1.39 : ℝ) ≤ (n : ℝ) / 128 := by
        have hcast : ((2 : ℝ) ^ (28 : ℕ)) ≤ (n : ℝ) := by exact_mod_cast hn
        have : (2 : ℝ) ^ (28 : ℕ) = 268435456 := by norm_num
        linarith
      linarith [hlog4_ub]
    -- total ≤ 18n/128 = 0.1406n ≤ n·1.386/6 = 0.231n
    have hsum : 2 * Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ))
        + Real.log (n : ℝ) + Real.log 4 ≤ 18 * ((n : ℝ) / 128) := by linarith
    refine le_trans hsum ?_
    have : 18 / 128 * (n : ℝ) ≤ 1.386 / 6 * (n : ℝ) := by nlinarith
    calc 18 * ((n : ℝ) / 128) = 18 / 128 * (n : ℝ) := by ring
      _ ≤ 1.386 / 6 * (n : ℝ) := this
      _ ≤ (n : ℝ) * Real.log 4 / 6 := by nlinarith [hlog4_lb]
  -- put everything together: hkey's (2n/3 + 1)·log4 splits as (2n/3)·log4 + log4, and
  -- the ledger absorbs √-error + log n + log 4 into n·log4/6
  have hfinal : (n : ℝ) * Real.log 4
      ≤ (n : ℝ) * Real.log 4 / 6 + (2 * (n : ℝ) / 3) * Real.log 4 + blockLog n := by
    nlinarith [herr_total, hkey]
  -- n·log4·(1 − 1/6 − 2/3) = n·log4/6
  nlinarith [hfinal]

set_option maxHeartbeats 800000 in
/-- **The block reciprocal bound**: `∑_{n < p ≤ 2n} 1/p ≥ (log 4 / 12)/log(2n)` for
`n ≥ 2²⁸` — the prime-counting lower input of Proposition `conv`
(arXiv:1509.05422): `∑_{p ∈ P_H} 1/p ≫ 1/log H`. -/
theorem sum_one_div_prime_block_ge {n : ℕ} (hn : 2 ^ 28 ≤ n) :
    Real.log 4 / 12 / Real.log (2 * (n : ℝ))
      ≤ ∑ p ∈ (2 * n + 1).primesBelow.filter (fun p => n < p), (1 : ℝ) / p := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
  have hlog2n : (0 : ℝ) < Real.log (2 * (n : ℝ)) := by
    refine Real.log_pos ?_
    linarith
  -- per-term: log p / (2n · log 2n) ≤ 1/p on the block
  have hterm : ∀ p ∈ (2 * n + 1).primesBelow.filter (fun p => n < p),
      Real.log p / (2 * (n : ℝ) * Real.log (2 * (n : ℝ))) ≤ 1 / p := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hpp := Nat.prime_of_mem_primesBelow hp.1
    have hp2n : p ≤ 2 * n := by
      have := Nat.lt_of_mem_primesBelow hp.1
      omega
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hp2nR : (p : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hp2n
    have hlogp : Real.log p ≤ Real.log (2 * (n : ℝ)) :=
      Real.log_le_log hp0 hp2nR
    have hlogp0 : (0 : ℝ) ≤ Real.log p :=
      Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    rw [div_le_div_iff₀ (by positivity) hp0]
    calc Real.log (p : ℝ) * (p : ℝ)
        ≤ Real.log (2 * (n : ℝ)) * (2 * (n : ℝ)) := by nlinarith
      _ = 1 * (2 * (n : ℝ) * Real.log (2 * (n : ℝ))) := by ring
  have hsum : blockLog n / (2 * (n : ℝ) * Real.log (2 * (n : ℝ)))
      ≤ ∑ p ∈ (2 * n + 1).primesBelow.filter (fun p => n < p), (1 : ℝ) / p := by
    have hrw : blockLog n / (2 * (n : ℝ) * Real.log (2 * (n : ℝ)))
        = ∑ p ∈ (2 * n + 1).primesBelow.filter (fun p => n < p),
            Real.log p / (2 * (n : ℝ) * Real.log (2 * (n : ℝ))) := by
      rw [blockLog, div_eq_mul_inv, Finset.sum_mul]
      exact Finset.sum_congr rfl fun p _ => by rw [div_eq_mul_inv]
    rw [hrw]
    exact Finset.sum_le_sum hterm
  have hblock := blockLog_ge hn
  refine le_trans ?_ hsum
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  -- goal: (log4/12)·(2n·log2n) ≤ blockLog·log2n, from blockLog ≥ n·log4/6
  have hexp : Real.log 4 / 12 * (2 * (n : ℝ) * Real.log (2 * (n : ℝ)))
      = ((n : ℝ) * Real.log 4 / 6) * Real.log (2 * (n : ℝ)) := by ring
  rw [hexp]
  exact mul_le_mul_of_nonneg_right hblock hlog2n.le

/-- The block product divides the primorial. -/
theorem prod_block_dvd_primorial (n : ℕ) :
    ∏ p ∈ (2 * n + 1).primesBelow.filter (fun p => n < p), p
      ∣ primorial (2 * n) := by
  rw [primorial]
  refine Finset.prod_dvd_prod_of_subset _ _ _ ?_
  intro p hp
  rw [Finset.mem_filter] at hp
  have hpp := Nat.prime_of_mem_primesBelow hp.1
  have hlt := Nat.lt_of_mem_primesBelow hp.1
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr hlt, hpp⟩

/-- **The conditioning budget**: the log of the block product is at most
`2n·log 4` (Erdős's primorial bound). -/
theorem log_prod_block_le (n : ℕ) :
    Real.log ((∏ p ∈ (2 * n + 1).primesBelow.filter (fun p => n < p), p : ℕ) : ℝ)
      ≤ 2 * (n : ℝ) * Real.log 4 := by
  have hpos : 0 < ∏ p ∈ (2 * n + 1).primesBelow.filter (fun p => n < p), p :=
    Finset.prod_pos fun p hp => by
      rw [Finset.mem_filter] at hp
      exact (Nat.prime_of_mem_primesBelow hp.1).pos
  have hle : (∏ p ∈ (2 * n + 1).primesBelow.filter (fun p => n < p), p)
      ≤ 4 ^ (2 * n) :=
    le_trans (Nat.le_of_dvd (primorial_pos _) (prod_block_dvd_primorial n))
      (primorial_le_4_pow _)
  have hlog := Real.log_le_log (by exact_mod_cast hpos)
    (by exact_mod_cast hle :
      ((∏ p ∈ (2 * n + 1).primesBelow.filter (fun p => n < p), p : ℕ) : ℝ)
        ≤ ((4 : ℝ)) ^ (2 * n))
  rw [Real.log_pow] at hlog
  calc Real.log ((∏ p ∈ (2 * n + 1).primesBelow.filter (fun p => n < p), p :
        ℕ) : ℝ)
      ≤ ((2 * n : ℕ) : ℝ) * Real.log 4 := hlog
    _ = 2 * (n : ℝ) * Real.log 4 := by push_cast; ring

/-- **The block cardinality bound**: at most `2·log 4·n/log n` primes in the
block — the Chebyshev upper bound the Hoeffding variance needs. -/
theorem card_block_le {n : ℕ} (hn : 2 ≤ n) :
    (((2 * n + 1).primesBelow.filter (fun p => n < p)).card : ℝ)
      ≤ 2 * n * Real.log 4 / Real.log n := by
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn)
  have hper : ∀ p ∈ (2 * n + 1).primesBelow.filter (fun p => n < p),
      Real.log (n : ℝ) ≤ Real.log (p : ℝ) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < n))
      (by exact_mod_cast hp.2.le)
  have hsum : (((2 * n + 1).primesBelow.filter (fun p => n < p)).card : ℝ)
      * Real.log (n : ℝ)
      ≤ ∑ p ∈ (2 * n + 1).primesBelow.filter (fun p => n < p),
          Real.log (p : ℝ) := by
    have h := Finset.card_nsmul_le_sum
      ((2 * n + 1).primesBelow.filter (fun p => n < p))
      (fun p => Real.log (p : ℝ)) (Real.log (n : ℝ)) hper
    rwa [nsmul_eq_mul] at h
  have hprod : ∑ p ∈ (2 * n + 1).primesBelow.filter (fun p => n < p),
      Real.log (p : ℝ)
      = Real.log ((∏ p ∈ (2 * n + 1).primesBelow.filter (fun p => n < p), p :
          ℕ) : ℝ) := by
    rw [show ((∏ p ∈ (2 * n + 1).primesBelow.filter (fun p => n < p), p :
        ℕ) : ℝ) = ∏ p ∈ (2 * n + 1).primesBelow.filter (fun p => n < p),
        (p : ℝ) from by push_cast; rfl]
    rw [Real.log_prod]
    intro p hp
    rw [Finset.mem_filter] at hp
    exact Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primesBelow hp.1).pos.ne'
  rw [le_div_iff₀ hlogn]
  calc (((2 * n + 1).primesBelow.filter (fun p => n < p)).card : ℝ)
      * Real.log (n : ℝ)
      ≤ ∑ p ∈ (2 * n + 1).primesBelow.filter (fun p => n < p),
          Real.log (p : ℝ) := hsum
    _ = Real.log ((∏ p ∈ (2 * n + 1).primesBelow.filter (fun p => n < p), p :
          ℕ) : ℝ) := hprod
    _ ≤ 2 * (n : ℝ) * Real.log 4 := log_prod_block_le n
    _ = 2 * n * Real.log 4 := by ring

end MoltResearch
