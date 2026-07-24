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

The cascade itself: `cascadeBound` (the recursive bound — base the
second-derivative test at separation `√μ/2`, step one Weyl differencing
with the crude power-mean split) and **`vdck_pow`**, the abstract `k`-th
derivative test in power form: a phase whose `(j+2)`-nd unit differences
lie in `[μ, ν]` over the window (with budget `j·H` beyond) satisfies
`‖∑ e(ψ(n))‖^{2^j} ≤ cascadeBound j L H μ ν` — natural-number powers
throughout, no `rpow`.
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

/-- The recursive bound for the derivative-test cascade: base = the
second-derivative test at separation `√μ/2`, step = one Weyl differencing
with the crude power-mean split. -/
noncomputable def cascadeBound : ℕ → ℝ → ℝ → ℝ → ℝ → ℝ
  | 0, L, _H, μ, ν => (ν * L + 2) * (3 / Real.sqrt μ + 1)
  | (j + 1), L, H, μ, ν =>
      ((L + H) / H) ^ (2 ^ j)
        * (2 ^ (2 ^ j) * L ^ (2 ^ j)
          + 4 ^ (2 ^ j) * H ^ (2 ^ j) * cascadeBound j L H μ (H * ν))

theorem cascadeBound_nonneg (j : ℕ) {L H μ ν : ℝ} (hL : 0 ≤ L)
    (hH : 1 ≤ H) (hμ : 0 < μ) (hν : 0 ≤ ν) :
    0 ≤ cascadeBound j L H μ ν := by
  have hH0 : (0:ℝ) < H := by linarith
  induction j generalizing ν with
  | zero =>
    rw [cascadeBound]
    have h1 : (0:ℝ) ≤ Real.sqrt μ := Real.sqrt_nonneg _
    have h2 : (0:ℝ) ≤ 3 / Real.sqrt μ := by positivity
    have h3 : (0:ℝ) ≤ ν * L := mul_nonneg hν hL
    nlinarith [mul_nonneg h3 h2]
  | succ j ih =>
    rw [cascadeBound]
    have h1 := ih (ν := H * ν) (mul_nonneg hH0.le hν)
    have h2 : (0:ℝ) ≤ (L + H) / H := div_nonneg (by linarith) hH0.le
    have h3 : (0:ℝ) ≤ L ^ (2 ^ j) := pow_nonneg hL _
    have h4 : (0:ℝ) ≤ (2:ℝ) ^ (2 ^ j) := by positivity
    have h4' : (0:ℝ) ≤ (4:ℝ) ^ (2 ^ j) := by positivity
    have h5 : (0:ℝ) ≤ H ^ (2 ^ j) := pow_nonneg hH0.le _
    have h6 : (0:ℝ) ≤ ((L + H) / H) ^ (2 ^ j) := pow_nonneg h2 _
    nlinarith [mul_nonneg h6 (add_nonneg (mul_nonneg h4 h3)
      (mul_nonneg (mul_nonneg h4' h5) h1))]

theorem cascadeBound_mono (j : ℕ) {L L' H μ ν ν' : ℝ}
    (hL : 0 ≤ L) (hLL : L ≤ L') (hH : 1 ≤ H) (hμ : 0 < μ)
    (hν : 0 ≤ ν) (hνν : ν ≤ ν') :
    cascadeBound j L H μ ν ≤ cascadeBound j L' H μ ν' := by
  have hH0 : (0:ℝ) < H := by linarith
  induction j generalizing ν ν' with
  | zero =>
    rw [cascadeBound, cascadeBound]
    have h1 : (0:ℝ) ≤ 3 / Real.sqrt μ + 1 := by positivity
    have h2 : ν * L + 2 ≤ ν' * L' + 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right h2 h1
  | succ j ih =>
    rw [cascadeBound, cascadeBound]
    have hb0 := cascadeBound_nonneg j hL hH hμ
      (ν := H * ν) (mul_nonneg hH0.le hν)
    have hb1 := ih (ν := H * ν) (ν' := H * ν') (mul_nonneg hH0.le hν)
      (by nlinarith)
    have h2 : ((L + H) / H) ^ (2 ^ j) ≤ ((L' + H) / H) ^ (2 ^ j) := by
      refine pow_le_pow_left₀ (div_nonneg (by linarith) hH0.le) ?_ _
      exact div_le_div_of_nonneg_right (by linarith) hH0.le
    have h3 : L ^ (2 ^ j) ≤ L' ^ (2 ^ j) :=
      pow_le_pow_left₀ hL hLL _
    have h4 : (0:ℝ) ≤ ((L + H) / H) ^ (2 ^ j) :=
      pow_nonneg (div_nonneg (by linarith) hH0.le) _
    have h5 : (0:ℝ) ≤ H ^ (2 ^ j) := pow_nonneg hH0.le _
    have h6 : 2 ^ (2 ^ j) * L ^ (2 ^ j)
          + 4 ^ (2 ^ j) * H ^ (2 ^ j) * cascadeBound j L H μ (H * ν)
        ≤ 2 ^ (2 ^ j) * L' ^ (2 ^ j)
          + 4 ^ (2 ^ j) * H ^ (2 ^ j)
            * cascadeBound j L' H μ (H * ν') := by
      have h7 : (0:ℝ) ≤ (2:ℝ) ^ (2 ^ j) := by positivity
      have h7' : (0:ℝ) ≤ (4:ℝ) ^ (2 ^ j) := by positivity
      have h5' : (0:ℝ) ≤ H ^ (2 ^ j) := pow_nonneg hH0.le _
      nlinarith [mul_le_mul_of_nonneg_left hb1 (mul_nonneg h7' h5'),
        mul_le_mul_of_nonneg_left h3 h7]
    have h8 : (0:ℝ) ≤ 2 ^ (2 ^ j) * L ^ (2 ^ j)
        + 4 ^ (2 ^ j) * H ^ (2 ^ j) * cascadeBound j L H μ (H * ν) := by
      have h7 : (0:ℝ) ≤ (2:ℝ) ^ (2 ^ j) := by positivity
      have h7' : (0:ℝ) ≤ (4:ℝ) ^ (2 ^ j) := by positivity
      have h7'' : (0:ℝ) ≤ L ^ (2 ^ j) := pow_nonneg hL _
      have h5' : (0:ℝ) ≤ H ^ (2 ^ j) := pow_nonneg hH0.le _
      nlinarith [mul_nonneg h7 h7'', mul_nonneg (mul_nonneg h7' h5') hb0]
    have h9 : (0:ℝ) ≤ ((L' + H) / H) ^ (2 ^ j) :=
      pow_nonneg (div_nonneg (by linarith) hH0.le) _
    nlinarith [mul_le_mul h2 h6 h8 h9]

/-- Unfolding the second difference. -/
theorem dIter_two (ψ : ℕ → ℝ) (n : ℕ) :
    dIter 2 ψ n = (ψ (n + 2) - ψ (n + 1)) - (ψ (n + 1) - ψ n) := by
  have e1 : (2 : ℕ) = 1 + 1 := rfl
  rw [e1, dIter_succ, dOp]
  have e2 : (1 : ℕ) = 0 + 1 := rfl
  rw [e2, dIter_succ, dIter_zero, dOp, dOp]

/-- Two-term power mean, crude form. -/
theorem add_pow_le_two_pow_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (q : ℕ) :
    (a + b) ^ q ≤ 2 ^ q * (a ^ q + b ^ q) := by
  rcases le_total a b with h | h
  · have h1 : (a + b) ^ q ≤ (2 * b) ^ q :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have h2 : (2 * b : ℝ) ^ q = 2 ^ q * b ^ q := mul_pow 2 b q
    have h3 : (0:ℝ) ≤ a ^ q := pow_nonneg ha _
    have h4 : (0:ℝ) ≤ (2:ℝ) ^ q := by positivity
    nlinarith
  · have h1 : (a + b) ^ q ≤ (2 * a) ^ q :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have h2 : (2 * a : ℝ) ^ q = 2 ^ q * a ^ q := mul_pow 2 a q
    have h3 : (0:ℝ) ≤ b ^ q := pow_nonneg hb _
    have h4 : (0:ℝ) ≤ (2:ℝ) ^ q := by positivity
    nlinarith

/-- Sum-power against the termwise powers, crude form. -/
theorem sum_pow_le_card_pow_mul {s : Finset ℕ} {f : ℕ → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (q : ℕ) (hq : 1 ≤ q) :
    (∑ i ∈ s, f i) ^ q ≤ (s.card : ℝ) ^ (q - 1) * ∑ i ∈ s, f i ^ q := by
  rcases Finset.eq_empty_or_nonempty s with hs | hs
  · subst hs
    rw [Finset.sum_empty, Finset.sum_empty,
      zero_pow (show q ≠ 0 by omega), mul_zero]
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have hcard : (0:ℝ) < (s.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hs
    have h1 := pow_sum_div_card_le_sum_pow (s := s) (f := f) hf q'
    rw [div_le_iff₀ (pow_pos hcard q')] at h1
    have h2 : q' + 1 - 1 = q' := by omega
    rw [h2]
    calc (∑ i ∈ s, f i) ^ (q' + 1)
        ≤ (∑ i ∈ s, f i ^ (q' + 1)) * (s.card : ℝ) ^ q' := h1
      _ = (s.card : ℝ) ^ q' * ∑ i ∈ s, f i ^ (q' + 1) := mul_comm _ _

/-- **The abstract derivative-test cascade** (power form): phases with
two-sided `(j+2)`-difference sandwiches obey the `2^j`-th-power bound. -/
theorem vdck_pow (j : ℕ) :
    ∀ (ψ : ℕ → ℝ) (M N H : ℕ) (μ ν : ℝ),
      0 < μ → μ ≤ ν → 1 ≤ H → H ≤ M → M ≤ N →
      (∀ n, M ≤ n → n ≤ N + j * H →
        μ ≤ dIter (j + 2) ψ n ∧ dIter (j + 2) ψ n ≤ ν) →
      ‖∑ n ∈ Finset.Ico M (N + 1), e (ψ n)‖ ^ (2 ^ j)
        ≤ cascadeBound j ((N + 1 - M : ℕ) : ℝ) (H : ℝ) μ ν := by
  induction j with
  | zero =>
    intro ψ M N H μ ν hμ hμν hH hHM hMN hsand
    simp only [Nat.zero_add, Nat.zero_mul, Nat.add_zero] at hsand
    have hpow : (2 : ℕ) ^ 0 = 1 := rfl
    rw [hpow, pow_one, cascadeBound]
    have hsqrt : (0:ℝ) < Real.sqrt μ := Real.sqrt_pos.mpr hμ
    have hθ : (0:ℝ) < Real.sqrt μ / 2 := by linarith
    have hν0 : (0:ℝ) < ν := lt_of_lt_of_le hμ hμν
    have hmono : ∀ n, M ≤ n → n < N →
        ψ (n + 1) - ψ n ≤ ψ (n + 2) - ψ (n + 1) := by
      intro n h1 h2
      have h3 := (hsand n h1 (by omega)).1
      rw [dIter_two] at h3
      linarith
    have hsec : ∀ n, M ≤ n → n < N →
        μ ≤ (ψ (n + 2) - ψ (n + 1)) - (ψ (n + 1) - ψ n) := by
      intro n h1 h2
      have h3 := (hsand n h1 (by omega)).1
      rw [dIter_two] at h3
      exact h3
    have hD : (ψ (N + 1) - ψ N) - (ψ (M + 1) - ψ M)
        ≤ ν * ((N + 1 - M : ℕ) : ℝ) := by
      have h5 := diff_shift_eq_sum (dOp ψ) (N - M) M
      have h6 : M + (N - M) = N := by omega
      rw [h6] at h5
      have h7 : ∑ m ∈ Finset.range (N - M), dOp (dOp ψ) (M + m)
          ≤ ∑ _m ∈ Finset.range (N - M), ν := by
        refine Finset.sum_le_sum fun m hm => ?_
        rw [Finset.mem_range] at hm
        have h8 := (hsand (M + m) (by omega) (by omega)).2
        rw [dIter_two] at h8
        simp only [dOp]
        linarith
      have h10 : ∑ _m ∈ Finset.range (N - M), ν
          = ((N - M : ℕ) : ℝ) * ν := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      simp only [dOp] at h5 h7
      have h11 : ((N - M : ℕ) : ℝ) ≤ ((N + 1 - M : ℕ) : ℝ) := by
        exact_mod_cast (by omega : N - M ≤ N + 1 - M)
      rw [h10] at h7
      nlinarith [h7, mul_le_mul_of_nonneg_right h11 hν0.le]
    have hvdc := vdc2 (φ := ψ) (θ := Real.sqrt μ / 2) (r := μ)
      (D := ν * ((N + 1 - M : ℕ) : ℝ)) hθ hμ hMN hmono hsec hD
    refine le_trans hvdc (le_of_eq ?_)
    have hself : Real.sqrt μ * Real.sqrt μ = μ := Real.mul_self_sqrt hμ.le
    have key : (2 * (Real.sqrt μ / 2) / μ + 1) + 1 / (Real.sqrt μ / 2)
        = 3 / Real.sqrt μ + 1 := by
      set sq := Real.sqrt μ with hsq
      rw [← hself]
      field_simp
      ring
    rw [key]
  | succ j ih =>
    intro ψ M N H μ ν hμ hμν hH hHM hMN hsand
    have hHR : (0:ℝ) < (H:ℝ) := by exact_mod_cast hH
    have hL0 : (0:ℝ) ≤ ((N + 1 - M : ℕ) : ℝ) := Nat.cast_nonneg _
    have hν0 : (0:ℝ) < ν := lt_of_lt_of_le hμ hμν
    have hq1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have hexp : ‖∑ n ∈ Finset.Ico M (N + 1), e (ψ n)‖ ^ 2 ^ (j + 1)
        = (‖∑ n ∈ Finset.Ico M (N + 1), e (ψ n)‖ ^ 2) ^ 2 ^ j := by
      rw [← pow_mul]
      congr 1
      rw [pow_succ']
    rw [hexp]
    have hweyl := weyl_differencing (φ := ψ) (H := H) hH hHM hMN
    have hs1 := pow_le_pow_left₀ (by positivity) hweyl (2 ^ j)
    refine le_trans hs1 ?_
    rw [mul_pow, cascadeBound]
    refine mul_le_mul_of_nonneg_left ?_
      (pow_nonneg (div_nonneg (by linarith) hHR.le) _)
    -- the per-difference bound
    have hper : ∀ g ∈ Finset.Ico 1 H,
        ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (ψ (m + g) - ψ m)‖ ^ 2 ^ j
          ≤ cascadeBound j ((N + 1 - M : ℕ) : ℝ) (H:ℝ) μ ((H:ℝ) * ν) := by
      intro g hg
      rw [Finset.mem_Ico] at hg
      have hBnn := cascadeBound_nonneg j hL0
        (show (1:ℝ) ≤ (H:ℝ) by exact_mod_cast hH) hμ
        (ν := (H:ℝ) * ν) (mul_nonneg hHR.le hν0.le)
      by_cases hempty : N + 1 - g ≤ M
      · have he : Finset.Ico M (N + 1 - g) = ∅ :=
          Finset.Ico_eq_empty (by omega)
        rw [he, Finset.sum_empty, norm_zero,
          zero_pow (Nat.two_pow_pos j).ne']
        exact hBnn
      · have hne : M < N + 1 - g := by omega
        have hgN : g ≤ N := by omega
        have hN' : N + 1 - g = (N - g) + 1 := by omega
        rw [hN']
        have hsand' : ∀ n, M ≤ n → n ≤ (N - g) + j * H →
            μ ≤ dIter (j + 2) (fun m => ψ (m + g) - ψ m) n
            ∧ dIter (j + 2) (fun m => ψ (m + g) - ψ m) n
              ≤ (H:ℝ) * ν := by
          intro n h1 h2
          have h3 := dIter_diff_sandwich (ψ := ψ) (j := j + 2) (g := g)
            (μ := μ) (ν := ν) (M := M) (N := N + (j + 1) * H)
            hg.1 hμ.le
            (fun m hm1 hm2 => hsand m hm1 (by omega))
            h1 (by
              have hjH : j * H + H = (j + 1) * H := by ring
              omega)
          refine ⟨h3.1, le_trans h3.2 ?_⟩
          have h4 : (g : ℝ) ≤ (H : ℝ) := by
            exact_mod_cast hg.2.le
          exact mul_le_mul_of_nonneg_right h4 hν0.le
        have hIH := ih (fun m => ψ (m + g) - ψ m) M (N - g) H μ
          ((H:ℝ) * ν) hμ
          (le_trans hμν (le_mul_of_one_le_left hν0.le
            (show (1:ℝ) ≤ (H:ℝ) by exact_mod_cast hH)))
          hH hHM (by omega) hsand'
        refine le_trans hIH (cascadeBound_mono j (Nat.cast_nonneg _)
          ?_ (show (1:ℝ) ≤ (H:ℝ) by exact_mod_cast hH) hμ
          (mul_nonneg hHR.le hν0.le) le_rfl)
        exact_mod_cast (by omega : (N - g) + 1 - M ≤ N + 1 - M)
    -- assemble the inner inequality
    set B := cascadeBound j ((N + 1 - M : ℕ) : ℝ) (H:ℝ) μ ((H:ℝ) * ν)
      with hBdef
    have hBnn : (0:ℝ) ≤ B := by
      rw [hBdef]
      exact cascadeBound_nonneg j hL0
        (show (1:ℝ) ≤ (H:ℝ) by exact_mod_cast hH) hμ
        (mul_nonneg hHR.le hν0.le)
    have hX0 : (0:ℝ) ≤ ∑ g ∈ Finset.Ico 1 H,
        ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (ψ (m + g) - ψ m)‖ :=
      Finset.sum_nonneg fun g _ => norm_nonneg _
    have hA := add_pow_le_two_pow_mul (a := ((N + 1 - M : ℕ) : ℝ))
      (b := 2 * ∑ g ∈ Finset.Ico 1 H,
        ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (ψ (m + g) - ψ m)‖)
      hL0 (by linarith) (2 ^ j)
    have hsumB : ∑ g ∈ Finset.Ico 1 H,
        ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (ψ (m + g) - ψ m)‖ ^ 2 ^ j
        ≤ ((H : ℝ) - 1) * B := by
      have h5 : ∑ g ∈ Finset.Ico 1 H,
          ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (ψ (m + g) - ψ m)‖ ^ 2 ^ j
          ≤ ∑ _g ∈ Finset.Ico 1 H, B := Finset.sum_le_sum hper
      have h6 : ∑ _g ∈ Finset.Ico 1 H, B
          = (((Finset.Ico 1 H).card : ℕ) : ℝ) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have h7 : (((Finset.Ico 1 H).card : ℕ) : ℝ) = (H : ℝ) - 1 := by
        rw [Nat.card_Ico]
        have h8 : H - 1 + 1 = H := by omega
        have h9 := congrArg (fun k : ℕ => (k : ℝ)) h8
        push_cast at h9
        linarith
      rw [h6, h7] at h5
      exact h5
    have hXq := sum_pow_le_card_pow_mul (s := Finset.Ico 1 H)
      (f := fun g => ‖∑ m ∈ Finset.Ico M (N + 1 - g),
        e (ψ (m + g) - ψ m)‖)
      (fun i _ => norm_nonneg _) (2 ^ j) hq1
    have hcard : (((Finset.Ico 1 H).card : ℕ) : ℝ) ^ (2 ^ j - 1)
        ≤ (H : ℝ) ^ (2 ^ j - 1) := by
      refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _
      rw [Nat.card_Ico]
      exact_mod_cast (by omega : H - 1 ≤ H)
    -- chain everything
    have hXfin : (∑ g ∈ Finset.Ico 1 H,
        ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (ψ (m + g) - ψ m)‖) ^ 2 ^ j
        ≤ (H : ℝ) ^ 2 ^ j * B := by
      have h10 : (0:ℝ) ≤ ∑ g ∈ Finset.Ico 1 H,
          ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (ψ (m + g) - ψ m)‖ ^ 2 ^ j :=
        Finset.sum_nonneg fun g _ => pow_nonneg (norm_nonneg _) _
      have h11 : (0:ℝ) ≤ (H:ℝ) ^ (2 ^ j - 1) := pow_nonneg hHR.le _
      have h12 : (((Finset.Ico 1 H).card : ℕ) : ℝ) ^ (2 ^ j - 1)
            * ∑ g ∈ Finset.Ico 1 H,
              ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (ψ (m + g) - ψ m)‖ ^ 2 ^ j
          ≤ (H:ℝ) ^ (2 ^ j - 1) * (((H : ℝ) - 1) * B) := by
        refine mul_le_mul hcard hsumB h10 h11
      have h13 : (H:ℝ) ^ (2 ^ j - 1) * (((H : ℝ) - 1) * B)
          ≤ (H:ℝ) ^ (2 ^ j - 1) * ((H : ℝ) * B) := by
        refine mul_le_mul_of_nonneg_left ?_ h11
        nlinarith
      have h14 : (H:ℝ) ^ (2 ^ j - 1) * ((H : ℝ) * B)
          = (H:ℝ) ^ 2 ^ j * B := by
        have h15 : (H:ℝ) ^ (2 ^ j - 1) * (H:ℝ) = (H:ℝ) ^ 2 ^ j := by
          rw [← pow_succ]
          congr 1
          omega
        calc (H:ℝ) ^ (2 ^ j - 1) * ((H : ℝ) * B)
            = ((H:ℝ) ^ (2 ^ j - 1) * (H:ℝ)) * B := by ring
          _ = (H:ℝ) ^ 2 ^ j * B := by rw [h15]
      linarith [le_trans hXq (le_trans h12 h13), h14.symm.le,
        le_trans (le_trans hXq h12) (le_trans h13 h14.le)]
    -- final
    have h2q : (0:ℝ) ≤ (2:ℝ) ^ 2 ^ j := by positivity
    have hLq : (0:ℝ) ≤ ((N + 1 - M : ℕ) : ℝ) ^ 2 ^ j := pow_nonneg hL0 _
    have hmp : ((2:ℝ) * ∑ g ∈ Finset.Ico 1 H,
        ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (ψ (m + g) - ψ m)‖) ^ 2 ^ j
        = 2 ^ 2 ^ j * (∑ g ∈ Finset.Ico 1 H,
          ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (ψ (m + g) - ψ m)‖) ^ 2 ^ j :=
      mul_pow 2 _ _
    have hfour : (2:ℝ) ^ 2 ^ j * 2 ^ 2 ^ j = 4 ^ 2 ^ j := by
      rw [← mul_pow]
      norm_num
    have hstep2 : (2:ℝ) ^ 2 ^ j * ((2 * ∑ g ∈ Finset.Ico 1 H,
        ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (ψ (m + g) - ψ m)‖) ^ 2 ^ j)
        = 4 ^ 2 ^ j * (∑ g ∈ Finset.Ico 1 H,
          ‖∑ m ∈ Finset.Ico M (N + 1 - g),
            e (ψ (m + g) - ψ m)‖) ^ 2 ^ j := by
      rw [hmp, ← mul_assoc, hfour]
    have hstep3 : (4:ℝ) ^ 2 ^ j * (∑ g ∈ Finset.Ico 1 H,
        ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (ψ (m + g) - ψ m)‖) ^ 2 ^ j
        ≤ 4 ^ 2 ^ j * ((H:ℝ) ^ 2 ^ j * B) :=
      mul_le_mul_of_nonneg_left hXfin (by positivity)
    nlinarith [hA, hstep2, hstep3]

end ExpSums

end MoltResearch
