import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import MoltResearch.Discrepancy.ExpSums

/-!
# The unit-difference calculus and iterated differences of `log` (Track L of #3020)

The quantitative core of the van der Corput cascade: two-sided bounds on
iterated unit differences of the logarithm, with the factorially exact
constants the `k`-th derivative tests consume.

* `dOp`, `dIter` — the forward unit difference and its iterates;
* `diff_shift_eq_sum` — a multi-step difference decomposes into shifted
  unit differences (how arbitrary-step Weyl data reduces to unit-step data);
* `dIter_inv_shift` — **the exact shifted-reciprocal identity**
  `Δᵏ(1/(m+x)) = (−1)^k k! / ((n+x)(n+1+x)⋯(n+k+x))` — pure telescoping
  algebra, no analysis;
* `dIter_log_eq_integral` — iterated log differences in closed integral
  form: `Δ^{k+1} log(n) = ∫₀¹ (−1)^k k!/∏(n+i+x) dx` (the integral is an
  exact summation device — no derivatives, no mean value theorem);
* `dIter_log_sandwich` — **the two-sided sandwich**
  `k!/(n+k+1)^{k+1} ≤ (−1)^k·Δ^{k+1} log(n) ≤ k!/n^{k+1}`.

Downstream, the log-phase `−(t/2π)·log n` inherits `k`-th difference
control at every scale, powering the cascade of derivative tests behind
the Weyl-strength zeta bound.

The cascade transfer layer: `dIter_neg` and `norm_sum_e_neg` (sign flips
are free), `dIter_diff_comm`/`dIter_diff_eq_sum` (differences of the
`g`-differenced phase are `g`-fold sums of one-deeper differences — how
each Weyl step hands its sandwich to the next level), and
`dIter_diff_sandwich` (the two-sided bounds transfer with `[μ, gν]`).
-/

namespace MoltResearch

namespace ExpSums

open Finset

/-- The forward unit difference. -/
def dOp (f : ℕ → ℝ) : ℕ → ℝ := fun n => f (n + 1) - f n

/-- Iterated unit differences. -/
def dIter (k : ℕ) (f : ℕ → ℝ) : ℕ → ℝ := dOp^[k] f

@[simp] theorem dIter_zero (f : ℕ → ℝ) : dIter 0 f = f := rfl

theorem dIter_succ (k : ℕ) (f : ℕ → ℝ) :
    dIter (k + 1) f = dOp (dIter k f) := by
  rw [dIter, dIter, Function.iterate_succ_apply']

theorem dIter_succ' (k : ℕ) (f : ℕ → ℝ) :
    dIter (k + 1) f = dIter k (dOp f) := by
  rw [dIter, dIter, Function.iterate_succ_apply]

/-- A multi-step difference decomposes into shifted unit differences. -/
theorem diff_shift_eq_sum (f : ℕ → ℝ) (g n : ℕ) :
    f (n + g) - f n = ∑ m ∈ Finset.range g, dOp f (n + m) := by
  have h := Finset.sum_range_sub (fun m => f (n + m)) g
  simp only [Nat.add_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [dOp]
  congr 1 <;> omega

/-- **The exact shifted-reciprocal identity**: unit `k`-th differences of
`1/(m+x)` are `(−1)^k k!` over the sliding product. -/
theorem dIter_inv_shift (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ∀ n : ℕ, 1 ≤ n →
      dIter k (fun m : ℕ => 1 / ((m : ℝ) + x)) n
        = (-1) ^ k * (k.factorial : ℝ)
          / ∏ i ∈ Finset.range (k + 1), ((n : ℝ) + i + x) := by
  induction k with
  | zero =>
    intro n hn
    simp [dIter]
  | succ k ih =>
    intro n hn
    rw [dIter_succ, dOp]
    rw [ih (n + 1) (by omega), ih n hn]
    have hpos : ∀ (m : ℕ), 1 ≤ m →
        (0 : ℝ) < ∏ i ∈ Finset.range (k + 1), ((m : ℝ) + i + x) := by
      intro m hm
      refine Finset.prod_pos fun i _ => ?_
      have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      positivity
    have h1 := hpos n hn
    have h2 := hpos (n + 1) (by omega)
    have hshift : ∏ i ∈ Finset.range (k + 1), (((n + 1 : ℕ) : ℝ) + i + x)
        = ∏ i ∈ Finset.range (k + 1), (((n : ℝ) + i + 1) + x) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      push_cast
      ring
    rw [hshift]
    have hA : (0 : ℝ) < ∏ i ∈ Finset.range (k + 1), (((n : ℝ) + i + 1) + x) := by
      refine Finset.prod_pos fun i _ => ?_
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      positivity
    have hP1 : ∏ i ∈ Finset.range (k + 2), ((n : ℝ) + i + x)
        = (∏ i ∈ Finset.range (k + 1), (((n : ℝ) + i + 1) + x))
          * ((n : ℝ) + x) := by
      have h3 := Finset.prod_range_succ' (fun i => (n : ℝ) + i + x) (k + 1)
      push_cast at h3 ⊢
      rw [h3]
      congr 1
      · exact Finset.prod_congr rfl fun i _ => by ring
      · ring
    have hP2 : ∏ i ∈ Finset.range (k + 2), ((n : ℝ) + i + x)
        = (∏ i ∈ Finset.range (k + 1), ((n : ℝ) + i + x))
          * ((n : ℝ) + (k + 1) + x) := by
      have h3 := Finset.prod_range_succ (fun i => (n : ℝ) + i + x) (k + 1)
      push_cast at h3 ⊢
      rw [h3]
    have hAB : (∏ i ∈ Finset.range (k + 1), (((n : ℝ) + i + 1) + x))
          * ((n : ℝ) + x)
        = (∏ i ∈ Finset.range (k + 1), ((n : ℝ) + i + x))
          * ((n : ℝ) + (k + 1) + x) := by
      rw [← hP1, ← hP2]
    have hnx : (0 : ℝ) < (n : ℝ) + x := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hnkx : (0 : ℝ) < (n : ℝ) + (k + 1) + x := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      positivity
    have hfac : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hP1, hfac, pow_succ]
    have hB : ∏ i ∈ Finset.range (k + 1), ((n : ℝ) + i + x)
        = (∏ i ∈ Finset.range (k + 1), (((n : ℝ) + i + 1) + x))
          * ((n : ℝ) + x) / ((n : ℝ) + (k + 1) + x) := by
      rw [eq_div_iff (ne_of_gt hnkx)]
      linarith [hAB]
    rw [hB]
    field_simp
    ring

/-- The logarithmic increment as an exact integral. -/
theorem dOp_log_eq_integral (m : ℕ) (hm : 1 ≤ m) :
    dOp (fun j : ℕ => Real.log j) m = ∫ x in (0:ℝ)..1, 1 / ((m : ℝ) + x) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h1 : ∫ x in (0:ℝ)..1, 1 / ((m : ℝ) + x)
      = ∫ x in (0:ℝ)..1, (fun y : ℝ => 1 / y) (x + (m : ℝ)) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring_nf
  rw [h1, intervalIntegral.integral_comp_add_right (fun y : ℝ => 1 / y)
    ((m : ℝ))]
  rw [integral_one_div ?_]
  · rw [dOp]
    rw [Real.log_div (by linarith) (by linarith)]
    push_cast
    ring_nf
  · intro hc
    rw [Set.mem_uIcc] at hc
    rcases hc with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> linarith

/-- The closed-form pointwise value is interval-integrable. -/
theorem closedForm_intervalIntegrable (k n : ℕ) (hn : 1 ≤ n) :
    IntervalIntegrable
      (fun x : ℝ => (-1) ^ k * (k.factorial : ℝ)
        / ∏ i ∈ Finset.range (k + 1), ((n : ℝ) + i + x))
      MeasureTheory.volume 0 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  refine ContinuousOn.div continuousOn_const ?_ ?_
  · refine Continuous.continuousOn ?_
    exact continuous_finset_prod _ fun i _ => by continuity
  · intro x hx
    rw [Set.mem_uIcc] at hx
    have hx0 : (0 : ℝ) ≤ x := by
      rcases hx with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> linarith
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    refine ne_of_gt (Finset.prod_pos fun i _ => ?_)
    positivity

/-- **Iterated log differences in closed integral form**. -/
theorem dIter_log_eq_integral (k : ℕ) :
    ∀ n : ℕ, 1 ≤ n →
      dIter (k + 1) (fun j : ℕ => Real.log j) n
        = ∫ x in (0:ℝ)..1,
            (-1) ^ k * (k.factorial : ℝ)
              / ∏ i ∈ Finset.range (k + 1), ((n : ℝ) + i + x) := by
  induction k with
  | zero =>
    intro n hn
    rw [show dIter 1 (fun j : ℕ => Real.log j) = dOp (fun j : ℕ => Real.log j)
        from dIter_succ 0 _, dOp_log_eq_integral n hn]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [Finset.prod_range_one]
    push_cast
    ring_nf
  | succ k ih =>
    intro n hn
    rw [dIter_succ, dOp, ih (n + 1) (by omega), ih n hn,
      ← intervalIntegral.integral_sub
        (closedForm_intervalIntegrable k (n + 1) (by omega))
        (closedForm_intervalIntegrable k n hn)]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Icc] at hx
    -- chain the exact identity at (k+1) and at k
    have h1 := dIter_inv_shift (k + 1) x hx.1 n hn
    rw [dIter_succ, dOp, dIter_inv_shift k x hx.1 (n + 1) (by omega),
      dIter_inv_shift k x hx.1 n hn] at h1
    convert h1 using 2

/-- **The two-sided sandwich for iterated log differences**: the
`(k+1)`-st unit difference alternates in sign with magnitude between
`k!/(n+k+1)^{k+1}` and `k!/n^{k+1}`. -/
theorem dIter_log_sandwich (k n : ℕ) (hn : 1 ≤ n) :
    (k.factorial : ℝ) / ((n : ℝ) + k + 1) ^ (k + 1)
      ≤ (-1) ^ k * dIter (k + 1) (fun j : ℕ => Real.log j) n
    ∧ (-1) ^ k * dIter (k + 1) (fun j : ℕ => Real.log j) n
      ≤ (k.factorial : ℝ) / (n : ℝ) ^ (k + 1) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [dIter_log_eq_integral k n hn,
    ← intervalIntegral.integral_const_mul]
  have hpt : ∀ x ∈ Set.Icc (0:ℝ) 1,
      (-1 : ℝ) ^ k * ((-1) ^ k * (k.factorial : ℝ)
        / ∏ i ∈ Finset.range (k + 1), ((n : ℝ) + i + x))
      = (k.factorial : ℝ)
        / ∏ i ∈ Finset.range (k + 1), ((n : ℝ) + i + x) := by
    intro x hx
    have hs : ((-1 : ℝ)) ^ k * (-1) ^ k = 1 := by
      rw [← mul_pow]
      norm_num
    rw [← mul_div_assoc, ← mul_assoc, hs, one_mul]
  have hconstL : ∫ _x in (0:ℝ)..1,
      (k.factorial : ℝ) / ((n : ℝ) + k + 1) ^ (k + 1)
      = (k.factorial : ℝ) / ((n : ℝ) + k + 1) ^ (k + 1) := by
    simp
  have hconstU : ∫ _x in (0:ℝ)..1, (k.factorial : ℝ) / (n : ℝ) ^ (k + 1)
      = (k.factorial : ℝ) / (n : ℝ) ^ (k + 1) := by
    simp
  have hint : IntervalIntegrable
      (fun x : ℝ => (-1 : ℝ) ^ k * ((-1) ^ k * (k.factorial : ℝ)
        / ∏ i ∈ Finset.range (k + 1), ((n : ℝ) + i + x)))
      MeasureTheory.volume 0 1 :=
    (closedForm_intervalIntegrable k n hn).const_mul _
  have hPbounds : ∀ x ∈ Set.Icc (0:ℝ) 1,
      (0 : ℝ) < ∏ i ∈ Finset.range (k + 1), ((n : ℝ) + i + x)
      ∧ (n : ℝ) ^ (k + 1) ≤ ∏ i ∈ Finset.range (k + 1), ((n : ℝ) + i + x)
      ∧ ∏ i ∈ Finset.range (k + 1), ((n : ℝ) + i + x)
        ≤ ((n : ℝ) + k + 1) ^ (k + 1) := by
    intro x hx
    rw [Set.mem_Icc] at hx
    obtain ⟨hx0, hx1⟩ := hx
    refine ⟨Finset.prod_pos fun i _ => by positivity, ?_, ?_⟩
    · calc (n : ℝ) ^ (k + 1)
          = ∏ _i ∈ Finset.range (k + 1), (n : ℝ) := by
            rw [Finset.prod_const, Finset.card_range]
        _ ≤ ∏ i ∈ Finset.range (k + 1), ((n : ℝ) + i + x) := by
            refine Finset.prod_le_prod (fun i _ => by positivity)
              (fun i _ => ?_)
            have h2 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
            linarith
    · calc ∏ i ∈ Finset.range (k + 1), ((n : ℝ) + i + x)
          ≤ ∏ _i ∈ Finset.range (k + 1), ((n : ℝ) + k + 1) := by
            refine Finset.prod_le_prod (fun i _ => by positivity)
              (fun i hi => ?_)
            rw [Finset.mem_range] at hi
            have h2 : (i : ℝ) ≤ (k : ℝ) := by
              exact_mod_cast (by omega : i ≤ k)
            linarith
        _ = ((n : ℝ) + k + 1) ^ (k + 1) := by
            rw [Finset.prod_const, Finset.card_range]
  constructor
  · rw [← hconstL]
    refine intervalIntegral.integral_mono_on (by norm_num)
      (by apply intervalIntegral.intervalIntegrable_const) hint ?_
    intro x hx
    rw [hpt x hx]
    obtain ⟨hP0, hPl, hPu⟩ := hPbounds x hx
    have hfac0 : (0 : ℝ) ≤ (k.factorial : ℝ) := Nat.cast_nonneg _
    have hq0 : (0 : ℝ) < ((n : ℝ) + k + 1) ^ (k + 1) := by positivity
    rw [div_le_div_iff₀ hq0 hP0]
    exact mul_le_mul_of_nonneg_left hPu hfac0
  · rw [← hconstU]
    refine intervalIntegral.integral_mono_on (by norm_num) hint
      (by apply intervalIntegral.intervalIntegrable_const) ?_
    intro x hx
    rw [hpt x hx]
    obtain ⟨hP0, hPl, hPu⟩ := hPbounds x hx
    have hfac0 : (0 : ℝ) ≤ (k.factorial : ℝ) := Nat.cast_nonneg _
    have hn0 : (0 : ℝ) < (n : ℝ) ^ (k + 1) := by
      have hn1' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      positivity
    rw [div_le_div_iff₀ hP0 hn0]
    exact mul_le_mul_of_nonneg_left hPl hfac0

/-- Iterated differences of a negated phase. -/
theorem dIter_neg (k : ℕ) (f : ℕ → ℝ) :
    dIter k (fun n => -(f n)) = fun n => -(dIter k f n) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext n
    rw [dIter_succ, dOp, ih, dIter_succ, dOp]
    ring

/-- Negating the phase conjugates the sum: same norm. -/
theorem norm_sum_e_neg (W : Finset ℕ) (ψ : ℕ → ℝ) :
    ‖∑ n ∈ W, e (-(ψ n))‖ = ‖∑ n ∈ W, e (ψ n)‖ := by
  have h1 : ∑ n ∈ W, e (-(ψ n)) = (starRingEnd ℂ) (∑ n ∈ W, e (ψ n)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun n _ => (e_conj (ψ n)).symm
  rw [h1, RCLike.norm_conj]

/-- Iterated differences commute with the `g`-step difference. -/
theorem dIter_diff_comm (j g : ℕ) (ψ : ℕ → ℝ) :
    dIter j (fun m => ψ (m + g) - ψ m)
      = fun n => dIter j ψ (n + g) - dIter j ψ n := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext n
    have h1 : dIter (j + 1) (fun m => ψ (m + g) - ψ m) n
        = (dIter j ψ (n + 1 + g) - dIter j ψ (n + 1))
          - (dIter j ψ (n + g) - dIter j ψ n) := by
      simp only [dIter_succ, dOp, ih]
    have h2 : dIter (j + 1) ψ (n + g) - dIter (j + 1) ψ n
        = (dIter j ψ (n + g + 1) - dIter j ψ (n + g))
          - (dIter j ψ (n + 1) - dIter j ψ n) := by
      simp only [dIter_succ, dOp]
    have hng : n + 1 + g = n + g + 1 := by omega
    rw [h1, h2, hng]
    ring

/-- **The cascade transfer**: `j`-th differences of the `g`-differenced
phase are `g`-fold sums of `(j+1)`-st differences of the original. -/
theorem dIter_diff_eq_sum (j g : ℕ) (ψ : ℕ → ℝ) (n : ℕ) :
    dIter j (fun m => ψ (m + g) - ψ m) n
      = ∑ m ∈ Finset.range g, dIter (j + 1) ψ (n + m) := by
  rw [dIter_diff_comm]
  beta_reduce
  have h := diff_shift_eq_sum (dIter j ψ) g n
  rw [h]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [dIter_succ]

/-- The sandwich transfers to differenced phases. -/
theorem dIter_diff_sandwich {ψ : ℕ → ℝ} {j g : ℕ} {μ ν : ℝ} {M N n : ℕ}
    (hg : 1 ≤ g) (hμpos : 0 ≤ μ)
    (hsand : ∀ m, M ≤ m → m ≤ N → μ ≤ dIter (j + 1) ψ m
      ∧ dIter (j + 1) ψ m ≤ ν)
    (hn : M ≤ n) (hng : n + g - 1 ≤ N) :
    μ ≤ dIter j (fun m => ψ (m + g) - ψ m) n
    ∧ dIter j (fun m => ψ (m + g) - ψ m) n ≤ (g : ℝ) * ν := by
  rw [dIter_diff_eq_sum]
  have hμ0 : ∀ m ∈ Finset.range g, μ / g ≤ dIter (j + 1) ψ (n + m) := by
    intro m hm
    rw [Finset.mem_range] at hm
    have h1 := (hsand (n + m) (by omega) (by omega)).1
    have hg1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    have h2 : μ / (g : ℝ) ≤ μ := div_le_self hμpos hg1
    linarith
  constructor
  · have h2 : ∑ m ∈ Finset.range g, μ / (g : ℝ)
        ≤ ∑ m ∈ Finset.range g, dIter (j + 1) ψ (n + m) :=
      Finset.sum_le_sum hμ0
    have h3 : ∑ _m ∈ Finset.range g, μ / (g : ℝ) = μ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    linarith
  · have h2 : ∑ m ∈ Finset.range g, dIter (j + 1) ψ (n + m)
        ≤ ∑ _m ∈ Finset.range g, ν := by
      refine Finset.sum_le_sum fun m hm => ?_
      rw [Finset.mem_range] at hm
      exact (hsand (n + m) (by omega) (by omega)).2
    have h3 : ∑ _m ∈ Finset.range g, ν = (g : ℝ) * ν := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    linarith

end ExpSums

end MoltResearch
