import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Discrepancy: prime-sum bounds at the zeta weight `1 + 1/log X`

Nucleus toolbox for the Tao 2015 §4 analysis (`Problems/tao2015_derivation_c.md`, issue
#2871, PR D2): the elementary-but-quantitative prime and integer sums at the exponent
`σ = 1 + 1/log X` that control the singular series `𝔖 = ∑ h(n)/n^σ`:

- `log_div_three_le_tsum_one_div_rpow` / `tsum_one_div_rpow_le_two_add_log`: the zeta mass
  `∑_n 1/n^σ` is `≍ log X` (two-sided, explicit constants). Lower bound via the harmonic
  comparison `n^{1/log X} ≤ e ≤ 3` for `n ≤ X`; upper bound via the Bernoulli telescoping
  `1/n^{1+β} ≤ (1/β)(1/(n−1)^β − 1/n^β)`.
- `sum_primes_Ioc_one_div_rpow_le` / `tsum_primes_tail_one_div_rpow_le`: the prime tail
  `∑_{p > X} 1/p^σ ≤ 8` — this is where prime sparseness enters, via Chebyshev's bound
  `θ(x) ≤ (log 4)·x` (`Chebyshev.theta_le_log4_mul_x`) on dyadic blocks
  `(X·2^j, X·2^{j+1}]`: each block contributes `≲ (2 log 4/log X)·2^{−jβ}`, and the
  geometric series sums to `≲ log X/β⁻¹`-free `O(1)` because `1 − 2^{−β} ≥ β/2`
  (Bernoulli) and `X^{−β} = e^{−1}` exactly.

All constants are explicit and deliberately crude (the §4 endgame only consumes `O(1)`
and `≍ log X` facts), which keeps every proof elementary — no Abel summation, no
improper integrals.
-/

namespace MoltResearch

open Finset

private lemma one_lt_log {X : ℝ} (hX : 3 ≤ X) : 1 < Real.log X := by
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    _ ≤ Real.log X := Real.log_le_log (by norm_num) hX

/-- For `1 ≤ n ≤ X`, the zeta weight loses at most a factor `3`:
`n^{1 + 1/log X} ≤ 3n` (since `n^{1/log X} ≤ e < 3`). -/
private lemma rpow_le_three_mul {X : ℝ} (hX : 3 ≤ X) {n : ℕ} (hn1 : 1 ≤ n)
    (hnX : (n : ℝ) ≤ X) :
    (n : ℝ) ^ (1 + 1 / Real.log X) ≤ 3 * n := by
  have hlog1 : 1 < Real.log X := one_lt_log hX
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [Real.rpow_add hn0, Real.rpow_one]
  have h2 : (n : ℝ) ^ (1 / Real.log X : ℝ) ≤ 3 := by
    rw [Real.rpow_def_of_pos hn0]
    have hexp : Real.log (n : ℝ) * (1 / Real.log X) ≤ 1 := by
      rw [mul_one_div, div_le_one (by linarith)]
      exact Real.log_le_log hn0 hnX
    calc Real.exp (Real.log (n : ℝ) * (1 / Real.log X))
        ≤ Real.exp 1 := Real.exp_le_exp.mpr hexp
      _ ≤ 3 := Real.exp_one_lt_three.le
  calc (n : ℝ) * (n : ℝ) ^ (1 / Real.log X : ℝ) ≤ (n : ℝ) * 3 :=
        mul_le_mul_of_nonneg_left h2 hn0.le
    _ = 3 * n := mul_comm _ _

/-- **Zeta-mass lower bound** (Tao 2015 §4, half of eq. (1s) input): at the weight
`σ = 1 + 1/log X` the full zeta mass dominates `(log X)/3` — via the harmonic sum over
`n ≤ X`, where the weight costs at most the factor `n^{1/log X} ≤ e < 3`. -/
theorem log_div_three_le_tsum_one_div_rpow {X : ℝ} (hX : 3 ≤ X) :
    Real.log X / 3 ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / Real.log X) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hlog1 : 1 < Real.log X := one_lt_log hX
  have hσ1 : 1 < 1 + 1 / Real.log X := by
    have : 0 < 1 / Real.log X := by positivity
    linarith
  have hsum : Summable fun n : ℕ => 1 / (n : ℝ) ^ (1 + 1 / Real.log X) :=
    Real.summable_one_div_nat_rpow.mpr hσ1
  have hpart : ∑ n ∈ Icc 1 ⌊X⌋₊, 1 / (n : ℝ) ^ (1 + 1 / Real.log X)
      ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / Real.log X) :=
    Summable.sum_le_tsum _ (fun n _ => by positivity) hsum
  have hpt : ∀ n ∈ Icc 1 ⌊X⌋₊, 1 / (3 * (n : ℝ)) ≤ 1 / (n : ℝ) ^ (1 + 1 / Real.log X) := by
    intro n hn
    rw [mem_Icc] at hn
    have hnX : (n : ℝ) ≤ X := by
      calc (n : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hn.2
        _ ≤ X := Nat.floor_le hX0.le
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    exact one_div_le_one_div_of_le (by positivity) (rpow_le_three_mul hX hn.1 hnX)
  have hharm : Real.log X ≤ ∑ n ∈ Icc 1 ⌊X⌋₊, (1 : ℝ) / n := by
    have h1 : (harmonic ⌊X⌋₊ : ℝ) = ∑ n ∈ Icc 1 ⌊X⌋₊, (1 : ℝ) / n := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp [one_div]
    have h2 := log_add_one_le_harmonic ⌊X⌋₊
    have h3 : Real.log X ≤ Real.log ((⌊X⌋₊ : ℝ) + 1) := by
      refine Real.log_le_log hX0 ?_
      exact (Nat.lt_floor_add_one X).le
    rw [← h1]
    push_cast at h2
    linarith
  calc Real.log X / 3 ≤ (∑ n ∈ Icc 1 ⌊X⌋₊, (1 : ℝ) / n) / 3 := by linarith
    _ = ∑ n ∈ Icc 1 ⌊X⌋₊, 1 / (3 * (n : ℝ)) := by
        rw [sum_div]
        refine sum_congr rfl fun n _ => ?_
        rw [div_div]
        ring_nf
    _ ≤ ∑ n ∈ Icc 1 ⌊X⌋₊, 1 / (n : ℝ) ^ (1 + 1 / Real.log X) := sum_le_sum hpt
    _ ≤ _ := hpart

/-- Bernoulli telescoping step: for `0 < β ≤ 1` and `n ≥ 2`,
`1/n^{1+β} ≤ (1/β)·(1/(n−1)^β − 1/n^β)`. -/
private lemma one_div_rpow_le_telescope {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {n : ℕ} (hn : 2 ≤ n) :
    1 / (n : ℝ) ^ (1 + β) ≤ (1 / β) * (1 / ((n : ℝ) - 1) ^ β - 1 / (n : ℝ) ^ β) := by
  have hb2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hb0 : (0 : ℝ) < n := by linarith
  have ha0 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  set a : ℝ := (n : ℝ) - 1 with ha
  set b : ℝ := (n : ℝ) with hb
  have hA0 : (0 : ℝ) < a ^ β := Real.rpow_pos_of_pos ha0 β
  have hB0 : (0 : ℝ) < b ^ β := Real.rpow_pos_of_pos hb0 β
  have hAB : a ^ β ≤ b ^ β := Real.rpow_le_rpow ha0.le (by rw [ha]; linarith) hβ0.le
  -- Bernoulli: (a/b)^β = (1 − 1/b)^β ≤ 1 − β/b
  have hbern : (a / b) ^ β ≤ 1 - β / b := by
    have hs : -1 ≤ -(1 / b) := by
      have : 1 / b ≤ 1 := by
        rw [div_le_one hb0]
        linarith
      linarith
    have h := rpow_one_add_le_one_add_mul_self hs hβ0.le hβ1
    have hab : a / b = 1 + -(1 / b) := by
      field_simp
      linarith
    rw [hab]
    calc (1 + -(1 / b)) ^ β ≤ 1 + β * -(1 / b) := h
      _ = 1 - β / b := by ring
  -- clear denominators: β·(a^β) ≤ b·(b^β − a^β)
  have hkey : β * a ^ β ≤ b * (b ^ β - a ^ β) := by
    have hdiv : (a / b) ^ β = a ^ β / b ^ β := Real.div_rpow ha0.le hb0.le β
    rw [hdiv] at hbern
    have h1 : a ^ β ≤ (1 - β / b) * b ^ β := (div_le_iff₀ hB0).mp hbern
    have h2 : b * a ^ β ≤ (b - β) * b ^ β := by
      have := mul_le_mul_of_nonneg_left h1 hb0.le
      calc b * a ^ β ≤ b * ((1 - β / b) * b ^ β) := this
        _ = (b - β) * b ^ β := by field_simp
    nlinarith [hAB, hβ0, hB0]
  -- convert back to the divided form
  have hb1β : b ^ (1 + β) = b * b ^ β := Real.rpow_one_add' hb0.le (by positivity)
  rw [hb1β, div_sub_div 1 1 hA0.ne' hB0.ne', one_mul, mul_one, div_mul_div_comm,
    one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hkey, hB0, hA0]

/-- **Zeta-mass upper bound** (Tao 2015 §4, half of eq. (1s) input): at the weight
`σ = 1 + 1/log X` the full zeta mass is at most `2 + log X` — Bernoulli telescoping,
no integrals. -/
theorem tsum_one_div_rpow_le_two_add_log {X : ℝ} (hX : 3 ≤ X) :
    ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / Real.log X) ≤ 2 + Real.log X := by
  have hlog1 : 1 < Real.log X := one_lt_log hX
  have hβ0 : 0 < 1 / Real.log X := by positivity
  have hβ1 : 1 / Real.log X ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hσ1 : 1 < 1 + 1 / Real.log X := by linarith
  have hsum : Summable fun n : ℕ => 1 / (n : ℝ) ^ (1 + 1 / Real.log X) :=
    Real.summable_one_div_nat_rpow.mpr hσ1
  refine Real.tsum_le_of_sum_le (fun n => by positivity) fun s => ?_
  obtain ⟨B, hB⟩ := s.exists_nat_subset_range
  calc ∑ n ∈ s, 1 / (n : ℝ) ^ (1 + 1 / Real.log X)
      ≤ ∑ n ∈ range B, 1 / (n : ℝ) ^ (1 + 1 / Real.log X) :=
        sum_le_sum_of_subset_of_nonneg hB fun n _ _ => by positivity
    _ ≤ 2 + Real.log X := ?_
  by_cases hB2 : B ≤ 2
  · -- tiny ranges: at most the terms n = 0, 1
    have h0 : ∀ n ∈ range B, 1 / (n : ℝ) ^ (1 + 1 / Real.log X) ≤ 1 := by
      intro n hn
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · rw [Nat.cast_zero, Real.zero_rpow (by positivity), div_zero]
        norm_num
      · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
        rw [div_le_one (Real.rpow_pos_of_pos (by linarith) _)]
        exact Real.one_le_rpow hn1 (by positivity)
    calc ∑ n ∈ range B, 1 / (n : ℝ) ^ (1 + 1 / Real.log X)
        ≤ ∑ _n ∈ range B, (1 : ℝ) := sum_le_sum h0
      _ = B := by simp
      _ ≤ 2 := by exact_mod_cast hB2
      _ ≤ 2 + Real.log X := by linarith
  · -- main case: split off n = 0, 1 and telescope the rest
    push_neg at hB2
    have hsplit : range B = range 2 ∪ Ico 2 B := by
      rw [range_eq_Ico, Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
    rw [hsplit, sum_union (by
      rw [range_eq_Ico]
      exact Finset.Ico_disjoint_Ico_consecutive 0 2 B)]
    have hfirst : ∑ n ∈ range 2, 1 / (n : ℝ) ^ (1 + 1 / Real.log X) ≤ 1 := by
      rw [sum_range_succ, sum_range_one, Nat.cast_zero,
        Real.zero_rpow (by positivity), div_zero, zero_add, Nat.cast_one,
        Real.one_rpow]
      norm_num
    have htele : ∑ n ∈ Ico 2 B, 1 / (n : ℝ) ^ (1 + 1 / Real.log X) ≤ Real.log X := by
      have hstep : ∀ n ∈ Ico 2 B, 1 / (n : ℝ) ^ (1 + 1 / Real.log X)
          ≤ (1 / (1 / Real.log X)) * (1 / ((n : ℝ) - 1) ^ (1 / Real.log X)
              - 1 / (n : ℝ) ^ (1 / Real.log X)) := by
        intro n hn
        rw [mem_Ico] at hn
        exact one_div_rpow_le_telescope hβ0 hβ1 hn.1
      calc ∑ n ∈ Ico 2 B, 1 / (n : ℝ) ^ (1 + 1 / Real.log X)
          ≤ ∑ n ∈ Ico 2 B, (1 / (1 / Real.log X)) * (1 / ((n : ℝ) - 1) ^ (1 / Real.log X)
              - 1 / (n : ℝ) ^ (1 / Real.log X)) := sum_le_sum hstep
        _ = Real.log X * ∑ n ∈ Ico 2 B, (1 / ((n : ℝ) - 1) ^ (1 / Real.log X)
              - 1 / (n : ℝ) ^ (1 / Real.log X)) := by
            rw [← mul_sum, one_div_one_div]
        _ ≤ Real.log X * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (by linarith)
            -- telescoping: reindex to `range (B - 2)` and collapse
            have hre : ∑ n ∈ Ico 2 B, (1 / ((n : ℝ) - 1) ^ (1 / Real.log X)
                - 1 / (n : ℝ) ^ (1 / Real.log X))
                = ∑ i ∈ range (B - 2), (1 / (((i + 1) : ℕ) : ℝ) ^ (1 / Real.log X)
                    - 1 / (((i + 1 + 1) : ℕ) : ℝ) ^ (1 / Real.log X)) := by
              rw [Finset.sum_Ico_eq_sum_range]
              refine sum_congr rfl fun i _ => ?_
              have h1 : ((2 + i : ℕ) : ℝ) - 1 = ((i + 1 : ℕ) : ℝ) := by push_cast; ring
              have h2 : ((2 + i : ℕ) : ℝ) = ((i + 1 + 1 : ℕ) : ℝ) := by push_cast; ring
              rw [h1, h2]
            have htel := Finset.sum_range_sub'
              (f := fun i => 1 / (((i + 1) : ℕ) : ℝ) ^ (1 / Real.log X)) (n := B - 2)
            rw [hre, htel]
            have h01 : ((0 + 1 : ℕ) : ℝ) = 1 := by norm_num
            rw [h01, Real.one_rpow]
            have hlast : 0 ≤ 1 / (((B - 2 + 1 : ℕ)) : ℝ) ^ (1 / Real.log X) := by positivity
            linarith
        _ = Real.log X := mul_one _
    linarith

/-! ### The prime tail at the zeta weight

`∑_{p > X} 1/p^{1+1/log X} = O(1)`: prime sparseness via Chebyshev's `θ(x) ≤ (log 4)·x`
on dyadic blocks. This is the one place in the §4 toolbox where prime counting is
essential — over all integers the corresponding tail is `≍ log X`, not `O(1)`. -/

open scoped Chebyshev in
/-- One dyadic block `(Y, 2Y]` of the prime tail: at most
`(2 log 4 / log X) · (1/Y^{1/log X})` — the prime count via `θ(2Y) ≤ (log 4)·2Y`, each
`log p ≥ log X`, each `1/p^σ ≤ 1/Y^σ`, and `Y^σ = Y·Y^{1/log X}`. -/
private lemma block_bound {X Y : ℝ} (hX : 3 ≤ X) (hXY : X ≤ Y) :
    ∑ p ∈ (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter Nat.Prime,
        1 / (p : ℝ) ^ (1 + 1 / Real.log X)
      ≤ 2 * Real.log 4 / Real.log X * (1 / Y ^ (1 / Real.log X : ℝ)) := by
  have hlog1 : 1 < Real.log X := one_lt_log hX
  have hY0 : (0 : ℝ) < Y := by linarith
  have hσ0 : (0 : ℝ) < 1 + 1 / Real.log X := by positivity
  -- pointwise: `1/p^σ ≤ log p · (1/(log X · Y^σ))`
  have hpt : ∀ p ∈ (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter Nat.Prime,
      1 / (p : ℝ) ^ (1 + 1 / Real.log X)
        ≤ Real.log p * (1 / (Real.log X * Y ^ (1 + 1 / Real.log X))) := by
    intro p hp
    rw [mem_filter, mem_Ioc] at hp
    have hpY : Y < (p : ℝ) := by
      rw [← Nat.floor_lt hY0.le]
      exact_mod_cast hp.1.1
    have hp0 : (0 : ℝ) < p := by linarith
    have hlogp : Real.log X ≤ Real.log p :=
      Real.log_le_log (by linarith) (by linarith)
    have hYp : Y ^ (1 + 1 / Real.log X : ℝ) ≤ (p : ℝ) ^ (1 + 1 / Real.log X : ℝ) :=
      Real.rpow_le_rpow hY0.le hpY.le hσ0.le
    have h1 : 1 / (p : ℝ) ^ (1 + 1 / Real.log X) ≤ 1 / Y ^ (1 + 1 / Real.log X : ℝ) :=
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos hY0 _) hYp
    have h2 : (1 : ℝ) ≤ Real.log p / Real.log X := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    calc 1 / (p : ℝ) ^ (1 + 1 / Real.log X)
        = 1 * (1 / (p : ℝ) ^ (1 + 1 / Real.log X)) := (one_mul _).symm
      _ ≤ (Real.log p / Real.log X) * (1 / Y ^ (1 + 1 / Real.log X : ℝ)) := by
          refine mul_le_mul h2 h1 (by positivity) ?_
          positivity
      _ = Real.log p * (1 / (Real.log X * Y ^ (1 + 1 / Real.log X))) := by
          field_simp
  -- Chebyshev: the block's log-mass is at most `θ(2Y) ≤ (log 4)·2Y`
  have htheta : ∑ p ∈ (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter Nat.Prime, Real.log p
      ≤ Real.log 4 * (2 * Y) := by
    have hsub : (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter Nat.Prime
        ⊆ (Finset.Ioc 0 ⌊2 * Y⌋₊).filter Nat.Prime :=
      Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc (Nat.zero_le _) le_rfl)
    have hmono : ∑ p ∈ (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter Nat.Prime, Real.log p
        ≤ ∑ p ∈ (Finset.Ioc 0 ⌊2 * Y⌋₊).filter Nat.Prime, Real.log p := by
      refine sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_
      rw [mem_filter] at hp
      exact Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
    calc ∑ p ∈ (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter Nat.Prime, Real.log p
        ≤ ∑ p ∈ (Finset.Ioc 0 ⌊2 * Y⌋₊).filter Nat.Prime, Real.log p := hmono
      _ = θ (2 * Y) := rfl
      _ ≤ Real.log 4 * (2 * Y) := Chebyshev.theta_le_log4_mul_x (by linarith)
  -- combine and reduce `Y/(Y^σ)` to `1/Y^{1/log X}`
  have hY1β : Y ^ (1 + 1 / Real.log X : ℝ) = Y * Y ^ (1 / Real.log X : ℝ) :=
    Real.rpow_one_add' hY0.le (by positivity)
  calc ∑ p ∈ (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter Nat.Prime, 1 / (p : ℝ) ^ (1 + 1 / Real.log X)
      ≤ ∑ p ∈ (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter Nat.Prime,
          Real.log p * (1 / (Real.log X * Y ^ (1 + 1 / Real.log X))) := sum_le_sum hpt
    _ = (∑ p ∈ (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter Nat.Prime, Real.log p)
          * (1 / (Real.log X * Y ^ (1 + 1 / Real.log X))) := by
        rw [sum_mul]
    _ ≤ (Real.log 4 * (2 * Y)) * (1 / (Real.log X * Y ^ (1 + 1 / Real.log X))) := by
        refine mul_le_mul_of_nonneg_right htheta ?_
        positivity
    _ = 2 * Real.log 4 / Real.log X * (1 / Y ^ (1 / Real.log X : ℝ)) := by
        rw [hY1β]
        have hY0' : Y ≠ 0 := hY0.ne'
        have hlog0 : Real.log X ≠ 0 := by linarith
        have hrY : Y ^ (1 / Real.log X : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hY0 _).ne'
        field_simp

/-- **Prime tail at the zeta weight** (Tao 2015 §4 toolbox, finite form):
`∑_{X < p ≤ B, p prime} 1/p^{1 + 1/log X} ≤ 8`, uniformly in `B` — Chebyshev's
`θ ≤ (log 4)·x` on dyadic blocks, `X^{−1/log X} = e^{−1}`, and the Bernoulli bound
`1 − 2^{−1/log X} ≥ 1/(2 log X)` for the geometric series. -/
theorem sum_primes_Ioc_one_div_rpow_le {X : ℝ} (hX : 3 ≤ X) (B : ℕ) :
    ∑ p ∈ (Finset.Ioc ⌊X⌋₊ B).filter Nat.Prime, 1 / (p : ℝ) ^ (1 + 1 / Real.log X) ≤ 8 := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hlog1 : 1 < Real.log X := one_lt_log hX
  have hβ0 : 0 < 1 / Real.log X := by positivity
  have hβ1 : 1 / Real.log X ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  classical
  set g : ℕ → ℝ := fun p => if p.Prime then 1 / (p : ℝ) ^ (1 + 1 / Real.log X) else 0
    with hgdef
  have hg0 : ∀ p, 0 ≤ g p := fun p => by
    rw [hgdef]
    dsimp only
    split <;> positivity
  rw [Finset.sum_filter]
  -- cover `(⌊X⌋, B]` by `B` dyadic blocks
  have hBJ : B ≤ ⌊X * 2 ^ B⌋₊ := by
    refine Nat.le_floor ?_
    calc (B : ℝ) ≤ 2 ^ B := by
          exact_mod_cast Nat.lt_two_pow_self.le
      _ = 1 * 2 ^ B := (one_mul _).symm
      _ ≤ X * 2 ^ B := by
          refine mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hsub : ∑ p ∈ Finset.Ioc ⌊X⌋₊ B, g p ≤ ∑ p ∈ Finset.Ioc ⌊X⌋₊ ⌊X * 2 ^ B⌋₊, g p :=
    sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc le_rfl hBJ)
      fun p _ _ => hg0 p
  -- consecutive-block decomposition
  have hfloormono : ∀ j : ℕ, ⌊X * 2 ^ j⌋₊ ≤ ⌊X * 2 ^ (j + 1)⌋₊ := by
    intro j
    refine Nat.floor_le_floor ?_
    have h2 : (2 : ℝ) ^ j ≤ 2 ^ (j + 1) := by
      rw [pow_succ]
      nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) j]
    nlinarith
  have hfloor0 : ∀ j : ℕ, ⌊X⌋₊ ≤ ⌊X * 2 ^ j⌋₊ := by
    intro j
    refine Nat.floor_le_floor ?_
    have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    nlinarith
  have hdecomp : ∀ J : ℕ, ∑ p ∈ Finset.Ioc ⌊X⌋₊ ⌊X * 2 ^ J⌋₊, g p
      = ∑ j ∈ range J, ∑ p ∈ Finset.Ioc ⌊X * 2 ^ j⌋₊ ⌊X * 2 ^ (j + 1)⌋₊, g p := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
        rw [sum_range_succ, ← ih]
        exact (Finset.sum_Ioc_consecutive g (hfloor0 J) (hfloormono J)).symm
  -- per-block bound in geometric form
  have hexp : (1 : ℝ) / X ^ (1 / Real.log X : ℝ) = Real.exp (-1) := by
    rw [Real.rpow_def_of_pos hX0, mul_one_div,
      div_self (show Real.log X ≠ 0 by linarith), Real.exp_neg, one_div]
  have hblock : ∀ j : ℕ, ∑ p ∈ Finset.Ioc ⌊X * 2 ^ j⌋₊ ⌊X * 2 ^ (j + 1)⌋₊, g p
      ≤ 2 * Real.log 4 / Real.log X * Real.exp (-1)
          * (((2 : ℝ) ^ (1 / Real.log X : ℝ))⁻¹) ^ j := by
    intro j
    have h2j0 : (0 : ℝ) < 2 ^ j := by positivity
    have hXY : X ≤ X * 2 ^ j := by
      have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      nlinarith
    have h2Y : X * 2 ^ (j + 1) = 2 * (X * 2 ^ j) := by
      rw [pow_succ]
      ring
    have hb := block_bound hX hXY
    rw [← h2Y] at hb
    have hgsum : ∑ p ∈ Finset.Ioc ⌊X * 2 ^ j⌋₊ ⌊X * 2 ^ (j + 1)⌋₊, g p
        = ∑ p ∈ (Finset.Ioc ⌊X * 2 ^ j⌋₊ ⌊X * 2 ^ (j + 1)⌋₊).filter Nat.Prime,
            1 / (p : ℝ) ^ (1 + 1 / Real.log X) := by
      rw [Finset.sum_filter]
    rw [hgsum]
    refine le_trans hb ?_
    -- `(X·2^j)^β = X^β · (2^β)^j`
    have hsplitpow : (X * 2 ^ j : ℝ) ^ (1 / Real.log X : ℝ)
        = X ^ (1 / Real.log X : ℝ) * ((2 : ℝ) ^ (1 / Real.log X : ℝ)) ^ j := by
      rw [Real.mul_rpow hX0.le h2j0.le]
      congr 1
      rw [← Real.rpow_natCast (2 : ℝ) j,
        ← Real.rpow_natCast ((2 : ℝ) ^ (1 / Real.log X : ℝ)) j,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), mul_comm]
    have h2β0 : (0 : ℝ) < (2 : ℝ) ^ (1 / Real.log X : ℝ) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hXβ0 : (0 : ℝ) < X ^ (1 / Real.log X : ℝ) := Real.rpow_pos_of_pos hX0 _
    rw [hsplitpow]
    rw [show (1 : ℝ) / (X ^ (1 / Real.log X : ℝ) * ((2 : ℝ) ^ (1 / Real.log X : ℝ)) ^ j)
        = (1 / X ^ (1 / Real.log X : ℝ)) * (((2 : ℝ) ^ (1 / Real.log X : ℝ))⁻¹) ^ j by
      simp only [one_div, mul_inv, inv_pow]]
    rw [hexp, ← mul_assoc]
  -- geometric series: ratio `r = 2^{−β}` with `1 − r ≥ β/2`
  set r : ℝ := ((2 : ℝ) ^ (1 / Real.log X : ℝ))⁻¹ with hrdef
  have h2β1 : (1 : ℝ) < (2 : ℝ) ^ (1 / Real.log X : ℝ) :=
    Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr (Or.inl ⟨by norm_num, hβ0⟩)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hrdef, inv_lt_one_iff₀]
    right
    exact h2β1
  have hrber : r ≤ 1 - 1 / Real.log X / 2 := by
    have hb := rpow_one_add_le_one_add_mul_self
      (show (-1 : ℝ) ≤ -(2⁻¹ : ℝ) by norm_num) hβ0.le hβ1
    have hhalf : (1 : ℝ) + -(2⁻¹ : ℝ) = 2⁻¹ := by norm_num
    rw [hhalf] at hb
    have hinv : r = ((2 : ℝ)⁻¹) ^ (1 / Real.log X : ℝ) := by
      rw [hrdef, Real.inv_rpow (by norm_num : (0:ℝ) ≤ 2)]
    rw [hinv]
    calc ((2 : ℝ)⁻¹) ^ (1 / Real.log X : ℝ) ≤ 1 + 1 / Real.log X * -(2⁻¹) := hb
      _ = 1 - 1 / Real.log X / 2 := by ring
  have hgeom : ∑ j ∈ range B, r ^ j ≤ 2 * Real.log X := by
    have hone_sub : 1 / Real.log X / 2 ≤ 1 - r := by linarith
    have hpos : (0 : ℝ) < 1 / Real.log X / 2 := by positivity
    have hsum_le : ∑ j ∈ range B, r ^ j ≤ 1 / (1 - r) := by
      rw [geom_sum_eq hr1.ne B,
        show (r ^ B - 1) / (r - 1) = (1 - r ^ B) / (1 - r) by
          rw [div_eq_div_iff (by linarith) (by linarith)]
          ring]
      refine div_le_div_of_nonneg_right ?_ (by linarith)
      have hrB : (0 : ℝ) ≤ r ^ B := by positivity
      linarith
    calc ∑ j ∈ range B, r ^ j ≤ 1 / (1 - r) := hsum_le
      _ ≤ 1 / (1 / Real.log X / 2) := one_div_le_one_div_of_le hpos hone_sub
      _ = 2 * Real.log X := by
          field_simp
  -- assemble, with the crude numeric endgame `4·log 4·e^{−1} ≤ 8`
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have := Real.log_two_lt_d9
    linarith
  have hexpneg : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) Real.exp_one_gt_two.le
  have hlog40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hexp0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  calc ∑ p ∈ Finset.Ioc ⌊X⌋₊ B, g p
      ≤ ∑ p ∈ Finset.Ioc ⌊X⌋₊ ⌊X * 2 ^ B⌋₊, g p := hsub
    _ = ∑ j ∈ range B, ∑ p ∈ Finset.Ioc ⌊X * 2 ^ j⌋₊ ⌊X * 2 ^ (j + 1)⌋₊, g p := hdecomp B
    _ ≤ ∑ j ∈ range B, 2 * Real.log 4 / Real.log X * Real.exp (-1) * r ^ j :=
        sum_le_sum fun j _ => hblock j
    _ = 2 * Real.log 4 / Real.log X * Real.exp (-1) * ∑ j ∈ range B, r ^ j := by
        rw [← mul_sum]
    _ ≤ 2 * Real.log 4 / Real.log X * Real.exp (-1) * (2 * Real.log X) := by
        refine mul_le_mul_of_nonneg_left hgeom ?_
        positivity
    _ = 4 * Real.log 4 * Real.exp (-1) := by
        field_simp
        ring
    _ ≤ 8 := by nlinarith [hlog4, hexpneg, hlog40, hexp0]

/-- **Prime tail at the zeta weight** (tsum form over `Nat.Primes`): the total mass of
primes beyond `X` is at most `8`. -/
theorem tsum_primes_tail_one_div_rpow_le {X : ℝ} (hX : 3 ≤ X) :
    ∑' p : Nat.Primes,
        (if X < ((p : ℕ) : ℝ) then 1 / ((p : ℕ) : ℝ) ^ (1 + 1 / Real.log X) else 0) ≤ 8 := by
  classical
  have hX0 : (0 : ℝ) < X := by linarith
  refine Real.tsum_le_of_sum_le (fun p => by dsimp only; split <;> positivity) fun s => ?_
  set t : Finset ℕ := s.image (fun p : Nat.Primes => (p : ℕ)) with htdef
  have himg : ∑ p ∈ s, (if X < ((p : ℕ) : ℝ) then 1 / ((p : ℕ) : ℝ) ^ (1 + 1 / Real.log X)
      else 0)
      = ∑ n ∈ t, (if X < (n : ℝ) then 1 / (n : ℝ) ^ (1 + 1 / Real.log X) else 0) := by
    rw [htdef, Finset.sum_image]
    intro a _ b _ h
    exact Subtype.ext h
  rw [himg, ← Finset.sum_filter]
  obtain ⟨B, hB⟩ := t.exists_nat_subset_range
  have hsub : t.filter (fun n : ℕ => X < (n : ℝ)) ⊆ (Finset.Ioc ⌊X⌋₊ B).filter Nat.Prime := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (Nat.floor_lt hX0.le).mpr hn.2
    · have hnB := hB hn.1
      rw [Finset.mem_range] at hnB
      exact hnB.le
    · rw [htdef] at hn
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hn.1
      exact p.prop
  calc ∑ n ∈ t.filter (fun n : ℕ => X < (n : ℝ)), 1 / (n : ℝ) ^ (1 + 1 / Real.log X)
      ≤ ∑ p ∈ (Finset.Ioc ⌊X⌋₊ B).filter Nat.Prime, 1 / (p : ℝ) ^ (1 + 1 / Real.log X) :=
        sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity
    _ ≤ 8 := sum_primes_Ioc_one_div_rpow_le hX B

/-! ### Crude Mertens upper bound

`∑_{p < N} 1/p ≤ 4·log log N + 13` — the same dyadic-block/Chebyshev argument as the tail
bound, but with unit weights: block `(2^j, 2^{j+1}]` contributes at most `4/j` exactly
(`2·log 4/log 2 = 4`), and the block index runs only to `Nat.log 2 N ≍ log N`, so the
harmonic sum of block bounds is `≲ log log N`. The constant `4` (vs the true Mertens `1`)
is harmless: the §4 consumer exponentiates `O(√(B₀ · log log X))`. -/

open scoped Chebyshev in
/-- One dyadic block of the Mertens sum: primes in `(2^{i+1}, 2^{i+2}]` contribute at most
`4/(i+1)`. -/
private lemma mertens_block_bound (i : ℕ) :
    ∑ p ∈ (Finset.Ioc (2 ^ (i + 1)) (2 ^ (i + 2))).filter Nat.Prime, (1 : ℝ) / p
      ≤ 4 / (i + 1) := by
  have h2i : (0 : ℝ) < 2 ^ (i + 1) := by positivity
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogblock : (0 : ℝ) < ((i : ℝ) + 1) * Real.log 2 := by positivity
  -- pointwise: `1/p ≤ log p / (2^{i+1} · (i+1) · log 2)`
  have hpt : ∀ p ∈ (Finset.Ioc (2 ^ (i + 1)) (2 ^ (i + 2))).filter Nat.Prime,
      (1 : ℝ) / p ≤ Real.log p * (1 / (2 ^ (i + 1) * (((i : ℝ) + 1) * Real.log 2))) := by
    intro p hp
    rw [mem_filter, mem_Ioc] at hp
    have hplo : (2 : ℝ) ^ (i + 1) < (p : ℕ) := by exact_mod_cast hp.1.1
    have hp0 : (0 : ℝ) < p := lt_trans h2i hplo
    have hlogp : ((i : ℝ) + 1) * Real.log 2 ≤ Real.log p := by
      have h1 : Real.log ((2 : ℝ) ^ (i + 1)) ≤ Real.log p :=
        Real.log_le_log (by positivity) hplo.le
      rw [Real.log_pow] at h1
      push_cast at h1
      linarith
    have h2 : (1 : ℝ) ≤ Real.log p / (((i : ℝ) + 1) * Real.log 2) := by
      rw [le_div_iff₀ hlogblock]
      linarith
    have h3 : (1 : ℝ) / p ≤ 1 / 2 ^ (i + 1) := one_div_le_one_div_of_le h2i hplo.le
    calc (1 : ℝ) / p = 1 * (1 / p) := (one_mul _).symm
      _ ≤ (Real.log p / (((i : ℝ) + 1) * Real.log 2)) * (1 / 2 ^ (i + 1)) := by
          refine mul_le_mul h2 h3 (by positivity) ?_
          positivity
      _ = Real.log p * (1 / (2 ^ (i + 1) * (((i : ℝ) + 1) * Real.log 2))) := by
          field_simp
  -- Chebyshev on the block
  have htheta : ∑ p ∈ (Finset.Ioc (2 ^ (i + 1)) (2 ^ (i + 2))).filter Nat.Prime, Real.log p
      ≤ Real.log 4 * 2 ^ (i + 2) := by
    have hsub : (Finset.Ioc (2 ^ (i + 1)) (2 ^ (i + 2))).filter Nat.Prime
        ⊆ (Finset.Ioc 0 ⌊((2 ^ (i + 2) : ℕ) : ℝ)⌋₊).filter Nat.Prime := by
      rw [Nat.floor_natCast]
      exact Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc (Nat.zero_le _) le_rfl)
    have hmono : ∑ p ∈ (Finset.Ioc (2 ^ (i + 1)) (2 ^ (i + 2))).filter Nat.Prime, Real.log p
        ≤ ∑ p ∈ (Finset.Ioc 0 ⌊((2 ^ (i + 2) : ℕ) : ℝ)⌋₊).filter Nat.Prime, Real.log p := by
      refine sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_
      rw [mem_filter] at hp
      exact Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
    calc ∑ p ∈ (Finset.Ioc (2 ^ (i + 1)) (2 ^ (i + 2))).filter Nat.Prime, Real.log p
        ≤ θ ((2 ^ (i + 2) : ℕ) : ℝ) := hmono
      _ ≤ Real.log 4 * 2 ^ (i + 2) := by
          have := Chebyshev.theta_le_log4_mul_x
            (show (0 : ℝ) ≤ ((2 ^ (i + 2) : ℕ) : ℝ) by positivity)
          calc θ ((2 ^ (i + 2) : ℕ) : ℝ)
              ≤ Real.log 4 * ((2 ^ (i + 2) : ℕ) : ℝ) := this
            _ = Real.log 4 * 2 ^ (i + 2) := by push_cast; ring
  -- combine with `log 4 = 2 log 2`
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  calc ∑ p ∈ (Finset.Ioc (2 ^ (i + 1)) (2 ^ (i + 2))).filter Nat.Prime, (1 : ℝ) / p
      ≤ ∑ p ∈ (Finset.Ioc (2 ^ (i + 1)) (2 ^ (i + 2))).filter Nat.Prime,
          Real.log p * (1 / (2 ^ (i + 1) * (((i : ℝ) + 1) * Real.log 2))) := sum_le_sum hpt
    _ = (∑ p ∈ (Finset.Ioc (2 ^ (i + 1)) (2 ^ (i + 2))).filter Nat.Prime, Real.log p)
          * (1 / (2 ^ (i + 1) * (((i : ℝ) + 1) * Real.log 2))) := by rw [sum_mul]
    _ ≤ (Real.log 4 * 2 ^ (i + 2)) * (1 / (2 ^ (i + 1) * (((i : ℝ) + 1) * Real.log 2))) := by
        refine mul_le_mul_of_nonneg_right htheta ?_
        positivity
    _ = 4 / (i + 1) := by
        rw [hlog4, show (2 : ℝ) ^ (i + 2) = 2 ^ (i + 1) * 2 by rw [pow_succ]]
        field_simp
        ring

/-- **Crude Mertens upper bound**: `∑_{p < N} 1/p ≤ 4·log(log N) + 13`.

The constant `4` (the sharp bound has `1`) is all the §4 Cauchy–Schwarz step needs: it
enters as `exp(O(√(B₀·log log X)))`. -/
theorem sum_primesBelow_one_div_le {N : ℕ} (hN : 3 ≤ N) :
    ∑ p ∈ N.primesBelow, (1 : ℝ) / p ≤ 4 * Real.log (Real.log N) + 13 := by
  classical
  set J : ℕ := Nat.log 2 N with hJdef
  have hJ1 : 1 ≤ J := by
    rw [hJdef]
    exact Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hNJ : N ≤ 2 ^ (J + 1) := (Nat.lt_pow_succ_log_self (by norm_num) N).le
  set g : ℕ → ℝ := fun p => if p.Prime then (1 : ℝ) / p else 0 with hgdef
  have hg0 : ∀ p, 0 ≤ g p := fun p => by
    rw [hgdef]
    dsimp only
    split <;> positivity
  -- move to the dyadic cover `Ioc 1 2^{J+1}`
  have hcover : ∑ p ∈ N.primesBelow, (1 : ℝ) / p ≤ ∑ p ∈ Finset.Ioc 1 (2 ^ (J + 1)), g p := by
    have hsub : N.primesBelow ⊆ Finset.Ioc 1 (2 ^ (J + 1)) := by
      intro p hp
      rw [Nat.mem_primesBelow] at hp
      rw [Finset.mem_Ioc]
      exact ⟨hp.2.one_lt, by omega⟩
    calc ∑ p ∈ N.primesBelow, (1 : ℝ) / p = ∑ p ∈ N.primesBelow, g p := by
          refine sum_congr rfl fun p hp => ?_
          rw [hgdef]
          simp [(Nat.mem_primesBelow.mp hp).2]
      _ ≤ ∑ p ∈ Finset.Ioc 1 (2 ^ (J + 1)), g p :=
          sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hg0 p
  -- consecutive dyadic decomposition
  have hdecomp : ∀ K : ℕ, ∑ p ∈ Finset.Ioc 1 (2 ^ K), g p
      = ∑ j ∈ range K, ∑ p ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), g p := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
        rw [sum_range_succ, ← ih]
        refine (Finset.sum_Ioc_consecutive g ?_ ?_).symm
        · exact Nat.one_le_two_pow
        · exact Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hdecomp (J + 1), sum_range_succ'] at hcover
  -- block 0 is `{2}`; blocks `i+1` are bounded by `4/(i+1)`
  have hblock0 : ∑ p ∈ Finset.Ioc (2 ^ 0) (2 ^ (0 + 1)), g p ≤ 1 := by
    rw [show (2 : ℕ) ^ (0 + 1) = 2 ^ 0 + 1 by norm_num, Nat.Ioc_succ_singleton,
      Finset.sum_singleton]
    rw [hgdef]
    norm_num [Nat.prime_two]
  have hblocks : ∑ i ∈ range J, ∑ p ∈ Finset.Ioc (2 ^ (i + 1)) (2 ^ (i + 1 + 1)), g p
      ≤ 4 * (1 + Real.log J) := by
    have hstep : ∀ i ∈ range J, ∑ p ∈ Finset.Ioc (2 ^ (i + 1)) (2 ^ (i + 1 + 1)), g p
        ≤ 4 * (1 / ((i : ℝ) + 1)) := by
      intro i _
      rw [show ∑ p ∈ Finset.Ioc (2 ^ (i + 1)) (2 ^ (i + 1 + 1)), g p
          = ∑ p ∈ (Finset.Ioc (2 ^ (i + 1)) (2 ^ (i + 2))).filter Nat.Prime, (1 : ℝ) / p by
        rw [Finset.sum_filter]]
      calc ∑ p ∈ (Finset.Ioc (2 ^ (i + 1)) (2 ^ (i + 2))).filter Nat.Prime, (1 : ℝ) / p
          ≤ 4 / (i + 1) := mertens_block_bound i
        _ = 4 * (1 / ((i : ℝ) + 1)) := by rw [mul_one_div]
    calc ∑ i ∈ range J, ∑ p ∈ Finset.Ioc (2 ^ (i + 1)) (2 ^ (i + 1 + 1)), g p
        ≤ ∑ i ∈ range J, 4 * (1 / ((i : ℝ) + 1)) := sum_le_sum hstep
      _ = 4 * ∑ i ∈ range J, 1 / ((i : ℝ) + 1) := by rw [← mul_sum]
      _ ≤ 4 * (1 + Real.log J) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          have hharm : (harmonic J : ℝ) = ∑ i ∈ range J, 1 / ((i : ℝ) + 1) := by
            rw [harmonic]
            push_cast
            refine sum_congr rfl fun i _ => ?_
            rw [one_div]
          rw [← hharm]
          exact harmonic_le_one_add_log J
    -- `log J ≤ 1 + log log N`
  have hJlog : Real.log J ≤ 1 + Real.log (Real.log N) := by
    have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have hlogN : 1 < Real.log N := one_lt_log hN3
    have hJle : (J : ℝ) ≤ 2 * Real.log N := by
      have h2J : (2 : ℝ) ^ J ≤ N := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
      have hlog2J : (J : ℝ) * Real.log 2 ≤ Real.log N := by
        have := Real.log_le_log (by positivity) h2J
        rwa [Real.log_pow] at this
      have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
        have h := Real.log_two_gt_d9
        linarith
      nlinarith [hlog2J, hlog2, Nat.cast_nonneg (α := ℝ) J]
    have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ1
    calc Real.log J ≤ Real.log (2 * Real.log N) := Real.log_le_log hJ0 hJle
      _ = Real.log 2 + Real.log (Real.log N) := by
          rw [Real.log_mul (by norm_num) (by linarith)]
      _ ≤ 1 + Real.log (Real.log N) := by
          have h := Real.log_two_lt_d9
          linarith
  calc ∑ p ∈ N.primesBelow, (1 : ℝ) / p
      ≤ (∑ i ∈ range J, ∑ p ∈ Finset.Ioc (2 ^ (i + 1)) (2 ^ (i + 1 + 1)), g p)
          + ∑ p ∈ Finset.Ioc (2 ^ 0) (2 ^ (0 + 1)), g p := hcover
    _ ≤ 4 * (1 + Real.log J) + 1 := by linarith [hblocks, hblock0]
    _ ≤ 4 * (1 + (1 + Real.log (Real.log N))) + 1 := by nlinarith [hJlog]
    _ ≤ 4 * Real.log (Real.log N) + 13 := by nlinarith

end MoltResearch
