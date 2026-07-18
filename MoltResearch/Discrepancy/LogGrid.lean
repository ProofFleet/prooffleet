import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Discrepancy: the decrement grid arithmetic

Track C, Elliott campaign (`Problems/tao2015_derivation_c.md`, issue #2946,
E6d-5c-iii): the pure-arithmetic engine of the entropy decrement's scale
selection — the telescoping-chain budget, its pigeonhole, and the dyadic
divergence of `∑ 1/(j·log j)` that makes the budget explode.
-/

namespace MoltResearch

open Finset

/-- **Telescoping budget**: a nonnegative chain that decrements by `d j` at each
step spends at most its initial value. -/
theorem sum_le_of_chain {J : ℕ} {r d : ℕ → ℝ} {C : ℝ}
    (hrJ : 0 ≤ r J) (hr0 : r 0 ≤ C)
    (hchain : ∀ j < J, r (j + 1) ≤ r j - d j) :
    ∑ j ∈ Finset.range J, d j ≤ C := by
  have key : ∀ m, m ≤ J → r m + ∑ j ∈ Finset.range m, d j ≤ r 0 := by
    intro m
    induction m with
    | zero => simp
    | succ n ihn =>
      intro hm
      have hn := ihn (by omega)
      have hc := hchain n (by omega)
      rw [Finset.sum_range_succ]
      linarith
  have hJ := key J le_rfl
  linarith

/-- **The decrement pigeonhole**: if the claimed decrements `t j` exceed the
budget in total, some actual decrement `d j` falls short of its claim. -/
theorem exists_lt_of_chain_budget {J : ℕ} {r d t : ℕ → ℝ} {C : ℝ}
    (hrJ : 0 ≤ r J) (hr0 : r 0 ≤ C)
    (hchain : ∀ j < J, r (j + 1) ≤ r j - d j)
    (hbudget : C < ∑ j ∈ Finset.range J, t j) :
    ∃ j < J, d j < t j := by
  by_contra hcon
  push_neg at hcon
  have hge : ∑ j ∈ Finset.range J, t j ≤ ∑ j ∈ Finset.range J, d j :=
    Finset.sum_le_sum fun j hj => hcon j (Finset.mem_range.mp hj)
  have hle := sum_le_of_chain hrJ hr0 hchain
  linarith

/-- Each dyadic block of `∑ 1/(j·log j)` carries at least `1/(2(i+1)·log 2)`. -/
theorem one_div_le_sum_Ioc_pow (i : ℕ) :
    1 / (2 * ((i : ℝ) + 1) * Real.log 2)
      ≤ ∑ j ∈ Finset.Ioc ((2 : ℕ) ^ i) (2 ^ (i + 1)), 1 / ((j : ℝ) * Real.log j) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hper : ∀ j ∈ Finset.Ioc ((2 : ℕ) ^ i) (2 ^ (i + 1)),
      1 / ((2 : ℝ) ^ (i + 1) * (((i : ℝ) + 1) * Real.log 2))
        ≤ 1 / ((j : ℝ) * Real.log j) := by
    intro j hj
    rw [Finset.mem_Ioc] at hj
    have hj2 : 2 ≤ j := by
      have h1 : (1 : ℕ) ≤ 2 ^ i := Nat.one_le_two_pow
      omega
    have hjR : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj2
    have hjpos : (0 : ℝ) < (j : ℝ) := by linarith
    have hlogj : Real.log 2 ≤ Real.log j := Real.log_le_log (by norm_num) hjR
    have hjle : (j : ℝ) ≤ (2 : ℝ) ^ (i + 1) := by
      exact_mod_cast hj.2
    have hlogle : Real.log j ≤ ((i : ℝ) + 1) * Real.log 2 := by
      have h := Real.log_le_log hjpos hjle
      rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at h
    have hprod : (j : ℝ) * Real.log j
        ≤ (2 : ℝ) ^ (i + 1) * (((i : ℝ) + 1) * Real.log 2) := by
      have hlogj0 : (0 : ℝ) ≤ Real.log j := le_trans hlog2.le hlogj
      have hpow0 : (0 : ℝ) ≤ (2 : ℝ) ^ (i + 1) := by positivity
      exact mul_le_mul hjle hlogle hlogj0 hpow0
    have hjlpos : (0 : ℝ) < (j : ℝ) * Real.log j := by
      have : (0 : ℝ) < Real.log j := lt_of_lt_of_le hlog2 hlogj
      positivity
    exact one_div_le_one_div_of_le hjlpos hprod
  have hcard : (Finset.Ioc ((2 : ℕ) ^ i) (2 ^ (i + 1))).card = 2 ^ i := by
    rw [Nat.card_Ioc]
    have h2 : 2 ^ (i + 1) = 2 * 2 ^ i := by ring
    omega
  have hsum := Finset.card_nsmul_le_sum (Finset.Ioc ((2 : ℕ) ^ i) (2 ^ (i + 1)))
    (fun j => 1 / ((j : ℝ) * Real.log j))
    (1 / ((2 : ℝ) ^ (i + 1) * (((i : ℝ) + 1) * Real.log 2))) hper
  rw [hcard, nsmul_eq_mul] at hsum
  have hid : ((2 ^ i : ℕ) : ℝ)
      * (1 / ((2 : ℝ) ^ (i + 1) * (((i : ℝ) + 1) * Real.log 2)))
      = 1 / (2 * ((i : ℝ) + 1) * Real.log 2) := by
    have hpow : (2 : ℝ) ^ (i + 1) = 2 * 2 ^ i := by ring
    have hpow0 : ((2 ^ i : ℕ) : ℝ) = (2 : ℝ) ^ i := by push_cast; ring
    rw [hpow0, hpow]
    have h2i : (2 : ℝ) ^ i ≠ 0 := by positivity
    have hi1 : ((i : ℝ) + 1) ≠ 0 := by positivity
    have hl2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    field_simp
  rw [hid] at hsum
  exact hsum

/-- The dyadic decomposition of the `(1, 2^M]` partial sum. -/
theorem sum_Ioc_pow_eq (M : ℕ) :
    ∑ j ∈ Finset.Ioc (1 : ℕ) ((2 : ℕ) ^ M), 1 / ((j : ℝ) * Real.log j)
      = ∑ i ∈ Finset.range M,
          ∑ j ∈ Finset.Ioc ((2 : ℕ) ^ i) (2 ^ (i + 1)), 1 / ((j : ℝ) * Real.log j) := by
  induction M with
  | zero => simp
  | succ N ih =>
    have h1 : (1 : ℕ) ≤ 2 ^ N := Nat.one_le_two_pow
    have h2 : 2 ^ N ≤ 2 ^ (N + 1) := by
      have : 2 ^ (N + 1) = 2 * 2 ^ N := by ring
      omega
    rw [Finset.sum_range_succ, ← ih,
      ← Finset.sum_Ioc_consecutive (fun j => 1 / ((j : ℝ) * Real.log j)) h1 h2]

/-- **Dyadic divergence**: the partial sums of `∑ 1/(j·log j)` are unbounded —
the (barely divergent) budget series of the entropy decrement argument. -/
theorem exists_sum_one_div_mul_log_gt (C : ℝ) :
    ∃ J : ℕ, 2 ≤ J ∧ C < ∑ j ∈ Finset.Ioc 1 J, 1 / ((j : ℝ) * Real.log j) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨M, hM⟩ := (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop
    (2 * Real.log 2 * C)).exists
  refine ⟨2 ^ (M + 1), ?_, ?_⟩
  · have : 2 ^ (M + 1) = 2 * 2 ^ M := by ring
    have h1 : (1 : ℕ) ≤ 2 ^ M := Nat.one_le_two_pow
    omega
  · rw [sum_Ioc_pow_eq]
    have hblocks : ∑ i ∈ Finset.range (M + 1),
        1 / (2 * ((i : ℝ) + 1) * Real.log 2)
        ≤ ∑ i ∈ Finset.range (M + 1),
            ∑ j ∈ Finset.Ioc ((2 : ℕ) ^ i) (2 ^ (i + 1)),
              1 / ((j : ℝ) * Real.log j) :=
      Finset.sum_le_sum fun i _ => one_div_le_sum_Ioc_pow i
    have hharm : ∑ i ∈ Finset.range (M + 1), 1 / (2 * ((i : ℝ) + 1) * Real.log 2)
        = (∑ i ∈ Finset.range (M + 1), (1 / ((i : ℝ) + 1)))
            * (1 / (2 * Real.log 2)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi1 : ((i : ℝ) + 1) ≠ 0 := by positivity
      have hl2 : Real.log 2 ≠ 0 := ne_of_gt hlog2
      field_simp
    have hMstep : ∑ i ∈ Finset.range M, (1 / ((i : ℝ) + 1))
        ≤ ∑ i ∈ Finset.range (M + 1), (1 / ((i : ℝ) + 1)) := by
      rw [Finset.sum_range_succ]
      have : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1) := by positivity
      linarith
    have hgt : 2 * Real.log 2 * C
        < ∑ i ∈ Finset.range (M + 1), (1 / ((i : ℝ) + 1)) := lt_of_lt_of_le hM hMstep
    have hpos : (0 : ℝ) < 1 / (2 * Real.log 2) := by positivity
    have := mul_lt_mul_of_pos_right hgt hpos
    have hC : 2 * Real.log 2 * C * (1 / (2 * Real.log 2)) = C := by
      field_simp
    rw [hC] at this
    rw [hharm] at hblocks
    linarith


/-- **Shifted Markov inequality**: the mass above threshold `τ'` of a family
whose shifted values are pointwise nonnegative is controlled by the shifted
average. The decrement uses it to bound the bad-`x` mass. -/
theorem sum_filter_le_of_avg_le {α : Type*} [Fintype α] {p v : α → ℝ}
    {θ τ τ' : ℝ} (hp0 : ∀ x, 0 ≤ p x) (hshift : ∀ x, 0 ≤ p x * (v x + θ))
    (havg : ∑ x, p x * v x ≤ τ) (hsum : ∑ x, p x = 1) (hτ' : 0 < τ' + θ) :
    ∑ x ∈ Finset.univ.filter (fun x => τ' ≤ v x), p x ≤ (τ + θ) / (τ' + θ) := by
  classical
  have htot : ∑ x, p x * (v x + θ) ≤ τ + θ := by
    have hexp : ∑ x, p x * (v x + θ)
        = (∑ x, p x * v x) + (∑ x, p x) * θ := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hexp, hsum]
    linarith
  have hfilter : (∑ x ∈ Finset.univ.filter (fun x => τ' ≤ v x), p x)
      * (τ' + θ)
      ≤ ∑ x ∈ Finset.univ.filter (fun x => τ' ≤ v x), p x * (v x + θ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun x hx => ?_
    rw [Finset.mem_filter] at hx
    exact mul_le_mul_of_nonneg_left (by linarith [hx.2]) (hp0 x)
  have hsub : ∑ x ∈ Finset.univ.filter (fun x => τ' ≤ v x), p x * (v x + θ)
      ≤ ∑ x, p x * (v x + θ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun x _ _ => hshift x
  rw [le_div_iff₀ hτ']
  linarith
