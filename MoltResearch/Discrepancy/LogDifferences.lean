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

The instantiation: `log_phase_block_bound` — the cascade applied to the
zeta phase `−(t/2π)·log n` on a near-dyadic window, with the sandwich
supplied by `dIter_log_sandwich` at `μ = (t/2π)(j+1)!/(4M)^{j+2}`,
`ν = (t/2π)(j+1)!/M^{j+2}`, and the alternating sign of `Δ^{j+2}log`
absorbed by parity (`j` even: the phase itself is positive-form; `j` odd:
conjugate via `norm_sum_e_neg`).
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

/-- Iterated differences are homogeneous. -/
theorem dIter_const_mul (k : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    dIter k (fun n => c * f n) = fun n => c * dIter k f n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext n
    rw [dIter_succ, dOp, ih, dIter_succ, dOp]
    ring

/-- **The log-phase block bound**: the cascade applied to `−(t/2π)·log n`,
with the sandwich supplied by the factorially exact bounds. -/
theorem log_phase_block_bound (j M N H : ℕ) (t : ℝ)
    (ht : 0 < t) (hH : 1 ≤ H) (hHM : H ≤ M) (hMN : M ≤ N)
    (hwin : N + j * H + j + 2 ≤ 4 * M) :
    ‖∑ n ∈ Finset.Ico M (N + 1),
        e (-(t / (2 * Real.pi) * Real.log n))‖ ^ (2 ^ j)
      ≤ cascadeBound j ((N + 1 - M : ℕ) : ℝ) (H : ℝ)
          (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
            / ((4 * M : ℕ) : ℝ) ^ (j + 2))
          (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
            / ((M : ℕ) : ℝ) ^ (j + 2)) := by
  have hM1 : 1 ≤ M := le_trans hH hHM
  set μ := t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
    / ((4 * M : ℕ) : ℝ) ^ (j + 2) with hμdef
  set ν := t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
    / ((M : ℕ) : ℝ) ^ (j + 2) with hνdef
  have hπ : (0:ℝ) < 2 * Real.pi := by positivity
  have hc : (0:ℝ) < t / (2 * Real.pi) := by positivity
  have hM0 : (0:ℝ) < ((M : ℕ) : ℝ) := by exact_mod_cast hM1
  have h4M0 : (0:ℝ) < ((4 * M : ℕ) : ℝ) := by
    have : 1 ≤ 4 * M := by omega
    exact_mod_cast this
  have hμ0 : (0:ℝ) < t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
      / ((4 * M : ℕ) : ℝ) ^ (j + 2) := by
    have hf : (0:ℝ) < ((j + 1).factorial : ℝ) := by
      exact_mod_cast (j + 1).factorial_pos
    positivity
  have hμν : t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
      / ((4 * M : ℕ) : ℝ) ^ (j + 2)
      ≤ t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
        / ((M : ℕ) : ℝ) ^ (j + 2) := by
    have hf : (0:ℝ) ≤ t / (2 * Real.pi) * ((j + 1).factorial : ℝ) := by
      have : (0:ℝ) ≤ ((j + 1).factorial : ℝ) := Nat.cast_nonneg _
      positivity
    have hle : ((M : ℕ) : ℝ) ^ (j + 2) ≤ ((4 * M : ℕ) : ℝ) ^ (j + 2) := by
      refine pow_le_pow_left₀ hM0.le ?_ _
      exact_mod_cast (by omega : M ≤ 4 * M)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul_of_nonneg_left hle hf
  -- the sandwich for the (parity-corrected) phase
  have hsand_core : ∀ n : ℕ, M ≤ n → n ≤ N + j * H →
      t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
        / ((4 * M : ℕ) : ℝ) ^ (j + 2)
      ≤ t / (2 * Real.pi)
          * ((-1 : ℝ) ^ (j + 1) * dIter (j + 2) (fun m : ℕ => Real.log m) n)
      ∧ t / (2 * Real.pi)
          * ((-1 : ℝ) ^ (j + 1) * dIter (j + 2) (fun m : ℕ => Real.log m) n)
        ≤ t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
          / ((M : ℕ) : ℝ) ^ (j + 2) := by
    intro n h1 h2
    have hn1 : 1 ≤ n := le_trans hM1 h1
    have hsw := dIter_log_sandwich (j + 1) n hn1
    have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn1
    constructor
    · -- lower: c·(j+1)!/(4M)^{j+2} ≤ c·[(−1)^{j+1}Δ] since (n+(j+1)+1) ≤ 4M
      have h3 : ((j + 1).factorial : ℝ) / ((4 * M : ℕ) : ℝ) ^ (j + 2)
          ≤ ((j + 1).factorial : ℝ) / ((n : ℝ) + (j + 1) + 1) ^ (j + 2) := by
        have h4 : ((n : ℝ) + (j + 1) + 1) ^ (j + 2)
            ≤ ((4 * M : ℕ) : ℝ) ^ (j + 2) := by
          refine pow_le_pow_left₀ (by positivity) ?_ _
          have h5 : (n : ℝ) + (j + 1) + 1 ≤ ((4 * M : ℕ) : ℝ) := by
            have h6 : n + (j + 1) + 1 ≤ 4 * M := by omega
            have h7 := congrArg (fun k : ℕ => (k : ℝ))
              (rfl : n + (j + 1) + 1 = n + (j + 1) + 1)
            push_cast
            exact_mod_cast h6
          exact h5
        have hf : (0:ℝ) ≤ ((j + 1).factorial : ℝ) := Nat.cast_nonneg _
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        exact mul_le_mul_of_nonneg_left h4 hf
      have h8 := hsw.1
      have h9 : t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
            / ((4 * M : ℕ) : ℝ) ^ (j + 2)
          = t / (2 * Real.pi) * (((j + 1).factorial : ℝ)
            / ((4 * M : ℕ) : ℝ) ^ (j + 2)) := by ring
      rw [h9]
      refine mul_le_mul_of_nonneg_left ?_ hc.le
      -- chain: (j+1)!/(4M)^{j+2} ≤ (j+1)!/(n+j+2)^{j+2} ≤ (−1)^{j+1}Δ
      have h10 : ((n : ℝ) + (j + 1) + 1) = (n : ℝ) + (j + 1 : ℕ) + 1 := by
        push_cast
        ring
      calc ((j + 1).factorial : ℝ) / ((4 * M : ℕ) : ℝ) ^ (j + 2)
          ≤ ((j + 1).factorial : ℝ)
            / ((n : ℝ) + (j + 1) + 1) ^ (j + 2) := h3
        _ ≤ (-1 : ℝ) ^ (j + 1)
            * dIter (j + 1 + 1) (fun m : ℕ => Real.log m) n := by
            have h11 := hsw.1
            convert h11 using 3 <;> push_cast <;> ring
    · have h8 := hsw.2
      have h9 : t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
            / ((M : ℕ) : ℝ) ^ (j + 2)
          = t / (2 * Real.pi) * (((j + 1).factorial : ℝ)
            / ((M : ℕ) : ℝ) ^ (j + 2)) := by ring
      rw [h9]
      refine mul_le_mul_of_nonneg_left ?_ hc.le
      have h12 : ((j + 1).factorial : ℝ) / ((n : ℝ)) ^ (j + 2)
          ≤ ((j + 1).factorial : ℝ) / ((M : ℕ) : ℝ) ^ (j + 2) := by
        have h13 : ((M : ℕ) : ℝ) ^ (j + 2) ≤ ((n : ℝ)) ^ (j + 2) := by
          refine pow_le_pow_left₀ hM0.le ?_ _
          exact_mod_cast h1
        have hf : (0:ℝ) ≤ ((j + 1).factorial : ℝ) := Nat.cast_nonneg _
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        exact mul_le_mul_of_nonneg_left h13 hf
      calc (-1 : ℝ) ^ (j + 1)
            * dIter (j + 1 + 1) (fun m : ℕ => Real.log m) n
          ≤ ((j + 1).factorial : ℝ) / (n : ℝ) ^ (j + 1 + 1) := hsw.2
        _ ≤ ((j + 1).factorial : ℝ) / ((M : ℕ) : ℝ) ^ (j + 2) := by
            convert h12 using 2
  -- parity split: the sign of Δ^{j+2}log decides which phase is positive-form
  rcases Nat.even_or_odd j with hpar | hpar
  · -- j even: the goal phase itself is positive-form
    have hneg1 : (-1 : ℝ) ^ (j + 1) = -1 := Odd.neg_one_pow hpar.add_one
    have hsand : ∀ n, M ≤ n → n ≤ N + j * H →
        μ ≤ dIter (j + 2)
            (fun m : ℕ => -(t / (2 * Real.pi) * Real.log m)) n
        ∧ dIter (j + 2)
            (fun m : ℕ => -(t / (2 * Real.pi) * Real.log m)) n ≤ ν := by
      intro n h1 h2
      have h3 := hsand_core n h1 h2
      rw [hneg1] at h3
      have h4a := congrFun (dIter_neg (j + 2)
        (fun m : ℕ => t / (2 * Real.pi) * Real.log m)) n
      have h4b := congrFun (dIter_const_mul (j + 2) (t / (2 * Real.pi))
        (fun m : ℕ => Real.log m)) n
      have heq : dIter (j + 2)
          (fun m : ℕ => -(t / (2 * Real.pi) * Real.log m)) n
          = t / (2 * Real.pi)
            * (-1 * dIter (j + 2) (fun m : ℕ => Real.log m) n) := by
        rw [h4a, h4b]
        ring
      rw [heq]
      exact h3
    exact vdck_pow j (fun m : ℕ => -(t / (2 * Real.pi) * Real.log m))
      M N H μ ν hμ0 hμν hH hHM hMN hsand
  · -- j odd: conjugate to the un-negated phase
    have hneg1 : (-1 : ℝ) ^ (j + 1) = 1 := Even.neg_one_pow hpar.add_one
    have hnorm : ‖∑ n ∈ Finset.Ico M (N + 1),
        e (-(t / (2 * Real.pi) * Real.log n))‖
        = ‖∑ n ∈ Finset.Ico M (N + 1),
            e (t / (2 * Real.pi) * Real.log n)‖ :=
      norm_sum_e_neg (Finset.Ico M (N + 1))
        (fun m : ℕ => t / (2 * Real.pi) * Real.log m)
    rw [hnorm]
    have hsand : ∀ n, M ≤ n → n ≤ N + j * H →
        μ ≤ dIter (j + 2)
            (fun m : ℕ => t / (2 * Real.pi) * Real.log m) n
        ∧ dIter (j + 2)
            (fun m : ℕ => t / (2 * Real.pi) * Real.log m) n ≤ ν := by
      intro n h1 h2
      have h3 := hsand_core n h1 h2
      rw [hneg1] at h3
      have h4b := congrFun (dIter_const_mul (j + 2) (t / (2 * Real.pi))
        (fun m : ℕ => Real.log m)) n
      have heq : dIter (j + 2)
          (fun m : ℕ => t / (2 * Real.pi) * Real.log m) n
          = t / (2 * Real.pi)
            * (1 * dIter (j + 2) (fun m : ℕ => Real.log m) n) := by
        rw [h4b]
        ring
      rw [heq]
      exact h3
    exact vdck_pow j (fun m : ℕ => t / (2 * Real.pi) * Real.log m)
      M N H μ ν hμ0 hμν hH hHM hMN hsand

/-- The cascade bound is at least one (needed to fold `1 + B ≤ 2B`). -/
theorem one_le_cascadeBound (j : ℕ) {L H μ ν : ℝ} (hL : 1 ≤ L)
    (hH : 1 ≤ H) (hμ : 0 < μ) (hν : 0 ≤ ν) :
    1 ≤ cascadeBound j L H μ ν := by
  induction j generalizing ν with
  | zero =>
    rw [cascadeBound]
    have h1 : (0:ℝ) ≤ 3 / Real.sqrt μ := by positivity
    have h2 : (0:ℝ) ≤ ν * L := mul_nonneg hν (by linarith)
    nlinarith
  | succ j ih =>
    rw [cascadeBound]
    have hH0 : (0:ℝ) < H := by linarith
    have h1 := ih (ν := H * ν) (mul_nonneg hH0.le hν)
    have h2 : (1:ℝ) ≤ (L + H) / H := by
      rw [le_div_iff₀ hH0]
      linarith
    have h3 : (1:ℝ) ≤ ((L + H) / H) ^ (2 ^ j) := one_le_pow₀ h2
    have h4 : (1:ℝ) ≤ (2:ℝ) ^ (2 ^ j) := one_le_pow₀ (by norm_num)
    have h5 : (1:ℝ) ≤ L ^ (2 ^ j) := one_le_pow₀ hL
    have h6 : (0:ℝ) ≤ (4:ℝ) ^ (2 ^ j) * H ^ (2 ^ j)
        * cascadeBound j L H μ (H * ν) := by
      have h7 : (0:ℝ) ≤ (4:ℝ) ^ (2 ^ j) := by positivity
      have h8 : (0:ℝ) ≤ H ^ (2 ^ j) := pow_nonneg hH0.le _
      exact mul_nonneg (mul_nonneg h7 h8) (by linarith)
    have h7 : (1:ℝ) ≤ 2 ^ 2 ^ j * L ^ 2 ^ j := by nlinarith
    have h8 : (1:ℝ) ≤ 2 ^ 2 ^ j * L ^ 2 ^ j
        + 4 ^ 2 ^ j * H ^ 2 ^ j * cascadeBound j L H μ (H * ν) := by
      linarith
    nlinarith [mul_le_mul h3 h8 (by norm_num)
      (le_trans (by norm_num) h3)]

/-- **The cascade unwind at `H = L`**: the recursion collapses to a single
closed form. -/
theorem cascadeBound_unwind (j : ℕ) {L μ ν : ℝ} (hL : 1 ≤ L)
    (hμ : 0 < μ) (hν : 0 ≤ ν) :
    cascadeBound j L L μ ν
      ≤ 16 ^ (2 ^ j) * L ^ (2 ^ j)
        * ((ν * L ^ (j + 1) + 2) * (3 / Real.sqrt μ + 1)) := by
  induction j generalizing ν with
  | zero =>
    rw [cascadeBound]
    have h1 : (0:ℝ) ≤ (ν * L ^ (0 + 1) + 2) * (3 / Real.sqrt μ + 1) := by
      have h2 : (0:ℝ) ≤ 3 / Real.sqrt μ := by positivity
      have h3 : (0:ℝ) ≤ ν * L ^ (0 + 1) := by
        have : (0:ℝ) ≤ L ^ (0 + 1) := by positivity
        exact mul_nonneg hν this
      exact mul_nonneg (by linarith) (by linarith)
    have h4 : ν * L + 2 = ν * L ^ (0 + 1) + 2 := by ring
    rw [h4]
    nlinarith [h1, mul_nonneg
      (by linarith : (0:ℝ) ≤ 16 * L - 1) h1]
  | succ j ih =>
    rw [cascadeBound]
    have hL0 : (0:ℝ) < L := by linarith
    have hIH := ih (ν := L * ν) (mul_nonneg hL0.le hν)
    have hone := one_le_cascadeBound j (H := L) hL hL hμ
      (ν := L * ν) (mul_nonneg hL0.le hν)
    have h2 : (L + L) / L = 2 := by
      field_simp
      ring
    rw [h2]
    have hq1 : (1:ℝ) ≤ (2:ℝ) ^ (2 ^ j) := one_le_pow₀ (by norm_num)
    have hLq : (1:ℝ) ≤ L ^ (2 ^ j) := one_le_pow₀ hL
    have hBnn : (0:ℝ) ≤ cascadeBound j L L μ (L * ν) := by linarith
    -- fold: 2^q·L^q + 4^q·L^q·B ≤ 2·4^q·L^q·B  (since 2^q·L^q ≤ 4^q·L^q·B)
    have hfold : (2:ℝ) ^ 2 ^ j * L ^ 2 ^ j
          + 4 ^ 2 ^ j * L ^ 2 ^ j * cascadeBound j L L μ (L * ν)
        ≤ 2 * (4 ^ 2 ^ j * L ^ 2 ^ j * cascadeBound j L L μ (L * ν)) := by
      have h5 : (2:ℝ) ^ 2 ^ j ≤ 4 ^ 2 ^ j := by
        refine pow_le_pow_left₀ (by norm_num) (by norm_num) _
      have h6 : (0:ℝ) ≤ L ^ 2 ^ j := by positivity
      nlinarith [mul_le_mul_of_nonneg_right h5 h6,
        mul_le_mul_of_nonneg_left hone
          (mul_nonneg (by positivity : (0:ℝ) ≤ (4:ℝ) ^ 2 ^ j) h6)]
    calc (2:ℝ) ^ 2 ^ j * (2 ^ 2 ^ j * L ^ 2 ^ j
          + 4 ^ 2 ^ j * L ^ 2 ^ j * cascadeBound j L L μ (L * ν))
        ≤ (2:ℝ) ^ 2 ^ j * (2 * (4 ^ 2 ^ j * L ^ 2 ^ j
            * cascadeBound j L L μ (L * ν))) := by
          exact mul_le_mul_of_nonneg_left hfold (by positivity)
      _ = 2 * 8 ^ 2 ^ j * L ^ 2 ^ j
            * cascadeBound j L L μ (L * ν) := by
          rw [show (8:ℝ) ^ 2 ^ j = 2 ^ 2 ^ j * 4 ^ 2 ^ j by
            rw [← mul_pow]
            norm_num]
          ring
      _ ≤ 16 ^ 2 ^ j * L ^ 2 ^ j * cascadeBound j L L μ (L * ν) := by
          have h8 : 2 * (8:ℝ) ^ 2 ^ j ≤ 16 ^ 2 ^ j := by
            have h9 : (16:ℝ) ^ 2 ^ j = 2 ^ 2 ^ j * 8 ^ 2 ^ j := by
              rw [← mul_pow]
              norm_num
            have h10 : (2:ℝ) ≤ 2 ^ 2 ^ j := by
              calc (2:ℝ) = 2 ^ 1 := (pow_one 2).symm
                _ ≤ 2 ^ 2 ^ j :=
                  pow_le_pow_right₀ (by norm_num) Nat.one_le_two_pow
            nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 8) (2 ^ j)]
          have h11 : (0:ℝ) ≤ L ^ 2 ^ j * cascadeBound j L L μ (L * ν) :=
            mul_nonneg (by positivity) hBnn
          nlinarith [mul_le_mul_of_nonneg_right h8 h11]
      _ ≤ 16 ^ 2 ^ j * L ^ 2 ^ j * (16 ^ 2 ^ j * L ^ 2 ^ j
            * ((L * ν * L ^ (j + 1) + 2) * (3 / Real.sqrt μ + 1))) := by
          exact mul_le_mul_of_nonneg_left hIH (by positivity)
      _ = 16 ^ 2 ^ (j + 1) * L ^ 2 ^ (j + 1)
            * ((ν * L ^ (j + 1 + 1) + 2) * (3 / Real.sqrt μ + 1)) := by
          have e0 : (2:ℕ) ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
          have e1 : (16:ℝ) ^ 2 ^ (j + 1) = 16 ^ 2 ^ j * 16 ^ 2 ^ j := by
            rw [e0, pow_mul]
            ring
          have e2 : L ^ 2 ^ (j + 1) = L ^ 2 ^ j * L ^ 2 ^ j := by
            rw [e0, pow_mul]
            ring
          rw [e1, e2]
          ring

/-- **The log-phase block bound**: the cascade applied to `−(t/2π)·log n`,
with the sandwich supplied by the factorially exact bounds. -/
theorem log_phase_block_bound_cap (j M N H W : ℕ) (t : ℝ)
    (ht : 0 < t) (hH : 1 ≤ H) (hHM : H ≤ M) (hMN : M ≤ N)
    (hwin : N + j * H + j + 2 ≤ W) :
    ‖∑ n ∈ Finset.Ico M (N + 1),
        e (-(t / (2 * Real.pi) * Real.log n))‖ ^ (2 ^ j)
      ≤ cascadeBound j ((N + 1 - M : ℕ) : ℝ) (H : ℝ)
          (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
            / ((W : ℕ) : ℝ) ^ (j + 2))
          (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
            / ((M : ℕ) : ℝ) ^ (j + 2)) := by
  have hM1 : 1 ≤ M := le_trans hH hHM
  set μ := t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
    / ((W : ℕ) : ℝ) ^ (j + 2) with hμdef
  set ν := t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
    / ((M : ℕ) : ℝ) ^ (j + 2) with hνdef
  have hπ : (0:ℝ) < 2 * Real.pi := by positivity
  have hc : (0:ℝ) < t / (2 * Real.pi) := by positivity
  have hM0 : (0:ℝ) < ((M : ℕ) : ℝ) := by exact_mod_cast hM1
  have h4M0 : (0:ℝ) < ((W : ℕ) : ℝ) := by
    have : 1 ≤ W := by omega
    exact_mod_cast this
  have hμ0 : (0:ℝ) < t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
      / ((W : ℕ) : ℝ) ^ (j + 2) := by
    have hf : (0:ℝ) < ((j + 1).factorial : ℝ) := by
      exact_mod_cast (j + 1).factorial_pos
    positivity
  have hμν : t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
      / ((W : ℕ) : ℝ) ^ (j + 2)
      ≤ t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
        / ((M : ℕ) : ℝ) ^ (j + 2) := by
    have hf : (0:ℝ) ≤ t / (2 * Real.pi) * ((j + 1).factorial : ℝ) := by
      have : (0:ℝ) ≤ ((j + 1).factorial : ℝ) := Nat.cast_nonneg _
      positivity
    have hle : ((M : ℕ) : ℝ) ^ (j + 2) ≤ ((W : ℕ) : ℝ) ^ (j + 2) := by
      refine pow_le_pow_left₀ hM0.le ?_ _
      exact_mod_cast (by omega : M ≤ W)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul_of_nonneg_left hle hf
  -- the sandwich for the (parity-corrected) phase
  have hsand_core : ∀ n : ℕ, M ≤ n → n ≤ N + j * H →
      t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
        / ((W : ℕ) : ℝ) ^ (j + 2)
      ≤ t / (2 * Real.pi)
          * ((-1 : ℝ) ^ (j + 1) * dIter (j + 2) (fun m : ℕ => Real.log m) n)
      ∧ t / (2 * Real.pi)
          * ((-1 : ℝ) ^ (j + 1) * dIter (j + 2) (fun m : ℕ => Real.log m) n)
        ≤ t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
          / ((M : ℕ) : ℝ) ^ (j + 2) := by
    intro n h1 h2
    have hn1 : 1 ≤ n := le_trans hM1 h1
    have hsw := dIter_log_sandwich (j + 1) n hn1
    have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn1
    constructor
    · -- lower: c·(j+1)!/(4M)^{j+2} ≤ c·[(−1)^{j+1}Δ] since (n+(j+1)+1) ≤ 4M
      have h3 : ((j + 1).factorial : ℝ) / ((W : ℕ) : ℝ) ^ (j + 2)
          ≤ ((j + 1).factorial : ℝ) / ((n : ℝ) + (j + 1) + 1) ^ (j + 2) := by
        have h4 : ((n : ℝ) + (j + 1) + 1) ^ (j + 2)
            ≤ ((W : ℕ) : ℝ) ^ (j + 2) := by
          refine pow_le_pow_left₀ (by positivity) ?_ _
          have h5 : (n : ℝ) + (j + 1) + 1 ≤ ((W : ℕ) : ℝ) := by
            have h6 : n + (j + 1) + 1 ≤ W := by omega
            have h7 := congrArg (fun k : ℕ => (k : ℝ))
              (rfl : n + (j + 1) + 1 = n + (j + 1) + 1)
            push_cast
            exact_mod_cast h6
          exact h5
        have hf : (0:ℝ) ≤ ((j + 1).factorial : ℝ) := Nat.cast_nonneg _
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        exact mul_le_mul_of_nonneg_left h4 hf
      have h8 := hsw.1
      have h9 : t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
            / ((W : ℕ) : ℝ) ^ (j + 2)
          = t / (2 * Real.pi) * (((j + 1).factorial : ℝ)
            / ((W : ℕ) : ℝ) ^ (j + 2)) := by ring
      rw [h9]
      refine mul_le_mul_of_nonneg_left ?_ hc.le
      -- chain: (j+1)!/(4M)^{j+2} ≤ (j+1)!/(n+j+2)^{j+2} ≤ (−1)^{j+1}Δ
      have h10 : ((n : ℝ) + (j + 1) + 1) = (n : ℝ) + (j + 1 : ℕ) + 1 := by
        push_cast
        ring
      calc ((j + 1).factorial : ℝ) / ((W : ℕ) : ℝ) ^ (j + 2)
          ≤ ((j + 1).factorial : ℝ)
            / ((n : ℝ) + (j + 1) + 1) ^ (j + 2) := h3
        _ ≤ (-1 : ℝ) ^ (j + 1)
            * dIter (j + 1 + 1) (fun m : ℕ => Real.log m) n := by
            have h11 := hsw.1
            convert h11 using 3 <;> push_cast <;> ring
    · have h8 := hsw.2
      have h9 : t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
            / ((M : ℕ) : ℝ) ^ (j + 2)
          = t / (2 * Real.pi) * (((j + 1).factorial : ℝ)
            / ((M : ℕ) : ℝ) ^ (j + 2)) := by ring
      rw [h9]
      refine mul_le_mul_of_nonneg_left ?_ hc.le
      have h12 : ((j + 1).factorial : ℝ) / ((n : ℝ)) ^ (j + 2)
          ≤ ((j + 1).factorial : ℝ) / ((M : ℕ) : ℝ) ^ (j + 2) := by
        have h13 : ((M : ℕ) : ℝ) ^ (j + 2) ≤ ((n : ℝ)) ^ (j + 2) := by
          refine pow_le_pow_left₀ hM0.le ?_ _
          exact_mod_cast h1
        have hf : (0:ℝ) ≤ ((j + 1).factorial : ℝ) := Nat.cast_nonneg _
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        exact mul_le_mul_of_nonneg_left h13 hf
      calc (-1 : ℝ) ^ (j + 1)
            * dIter (j + 1 + 1) (fun m : ℕ => Real.log m) n
          ≤ ((j + 1).factorial : ℝ) / (n : ℝ) ^ (j + 1 + 1) := hsw.2
        _ ≤ ((j + 1).factorial : ℝ) / ((M : ℕ) : ℝ) ^ (j + 2) := by
            convert h12 using 2
  -- parity split: the sign of Δ^{j+2}log decides which phase is positive-form
  rcases Nat.even_or_odd j with hpar | hpar
  · -- j even: the goal phase itself is positive-form
    have hneg1 : (-1 : ℝ) ^ (j + 1) = -1 := Odd.neg_one_pow hpar.add_one
    have hsand : ∀ n, M ≤ n → n ≤ N + j * H →
        μ ≤ dIter (j + 2)
            (fun m : ℕ => -(t / (2 * Real.pi) * Real.log m)) n
        ∧ dIter (j + 2)
            (fun m : ℕ => -(t / (2 * Real.pi) * Real.log m)) n ≤ ν := by
      intro n h1 h2
      have h3 := hsand_core n h1 h2
      rw [hneg1] at h3
      have h4a := congrFun (dIter_neg (j + 2)
        (fun m : ℕ => t / (2 * Real.pi) * Real.log m)) n
      have h4b := congrFun (dIter_const_mul (j + 2) (t / (2 * Real.pi))
        (fun m : ℕ => Real.log m)) n
      have heq : dIter (j + 2)
          (fun m : ℕ => -(t / (2 * Real.pi) * Real.log m)) n
          = t / (2 * Real.pi)
            * (-1 * dIter (j + 2) (fun m : ℕ => Real.log m) n) := by
        rw [h4a, h4b]
        ring
      rw [heq]
      exact h3
    exact vdck_pow j (fun m : ℕ => -(t / (2 * Real.pi) * Real.log m))
      M N H μ ν hμ0 hμν hH hHM hMN hsand
  · -- j odd: conjugate to the un-negated phase
    have hneg1 : (-1 : ℝ) ^ (j + 1) = 1 := Even.neg_one_pow hpar.add_one
    have hnorm : ‖∑ n ∈ Finset.Ico M (N + 1),
        e (-(t / (2 * Real.pi) * Real.log n))‖
        = ‖∑ n ∈ Finset.Ico M (N + 1),
            e (t / (2 * Real.pi) * Real.log n)‖ :=
      norm_sum_e_neg (Finset.Ico M (N + 1))
        (fun m : ℕ => t / (2 * Real.pi) * Real.log m)
    rw [hnorm]
    have hsand : ∀ n, M ≤ n → n ≤ N + j * H →
        μ ≤ dIter (j + 2)
            (fun m : ℕ => t / (2 * Real.pi) * Real.log m) n
        ∧ dIter (j + 2)
            (fun m : ℕ => t / (2 * Real.pi) * Real.log m) n ≤ ν := by
      intro n h1 h2
      have h3 := hsand_core n h1 h2
      rw [hneg1] at h3
      have h4b := congrFun (dIter_const_mul (j + 2) (t / (2 * Real.pi))
        (fun m : ℕ => Real.log m)) n
      have heq : dIter (j + 2)
          (fun m : ℕ => t / (2 * Real.pi) * Real.log m) n
          = t / (2 * Real.pi)
            * (1 * dIter (j + 2) (fun m : ℕ => Real.log m) n) := by
        rw [h4b]
        ring
      rw [heq]
      exact h3
    exact vdck_pow j (fun m : ℕ => t / (2 * Real.pi) * Real.log m)
      M N H μ ν hμ0 hμν hH hHM hMN hsand

/-- **The cascade unwind at `L = 2H`**: the closed form for sub-block
partial sums. -/
theorem cascadeBound_unwind₂ (j : ℕ) {H μ ν : ℝ} (hH : 1 ≤ H)
    (hμ : 0 < μ) (hν : 0 ≤ ν) :
    cascadeBound j (2 * H) H μ ν
      ≤ 48 ^ (2 ^ j) * H ^ (2 ^ j)
        * ((2 * ν * H ^ (j + 1) + 2) * (3 / Real.sqrt μ + 1)) := by
  induction j generalizing ν with
  | zero =>
    rw [cascadeBound]
    have h1 : (0:ℝ) ≤ (2 * ν * H ^ (0 + 1) + 2) * (3 / Real.sqrt μ + 1) := by
      have h2 : (0:ℝ) ≤ 3 / Real.sqrt μ := by positivity
      have h3 : (0:ℝ) ≤ 2 * ν * H ^ (0 + 1) := by
        have : (0:ℝ) ≤ H ^ (0 + 1) := by positivity
        positivity
      exact mul_nonneg (by linarith) (by linarith)
    have h4 : ν * (2 * H) + 2 = 2 * ν * H ^ (0 + 1) + 2 := by ring
    rw [h4]
    nlinarith [h1, mul_nonneg
      (by linarith : (0:ℝ) ≤ 48 * H - 1) h1]
  | succ j ih =>
    rw [cascadeBound]
    have hH0 : (0:ℝ) < H := by linarith
    have hIH := ih (ν := H * ν) (mul_nonneg hH0.le hν)
    have hone := one_le_cascadeBound j (L := 2 * H) (H := H)
      (by linarith) hH hμ (ν := H * ν) (mul_nonneg hH0.le hν)
    have h2 : (2 * H + H) / H = 3 := by
      field_simp
      ring
    rw [h2]
    have hBnn : (0:ℝ) ≤ cascadeBound j (2 * H) H μ (H * ν) := by linarith
    have hfold : (2:ℝ) ^ 2 ^ j * (2 * H) ^ 2 ^ j
          + 4 ^ 2 ^ j * H ^ 2 ^ j * cascadeBound j (2 * H) H μ (H * ν)
        ≤ 2 * (4 ^ 2 ^ j * H ^ 2 ^ j
            * cascadeBound j (2 * H) H μ (H * ν)) := by
      have h5 : (2:ℝ) ^ 2 ^ j * (2 * H) ^ 2 ^ j = 4 ^ 2 ^ j * H ^ 2 ^ j := by
        rw [mul_pow, ← mul_assoc, ← mul_pow]
        norm_num
      have h6 : (0:ℝ) ≤ H ^ 2 ^ j := by positivity
      have h8 : (0:ℝ) ≤ (4:ℝ) ^ 2 ^ j * H ^ 2 ^ j := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hone h8]
    calc (3:ℝ) ^ 2 ^ j * ((2:ℝ) ^ 2 ^ j * (2 * H) ^ 2 ^ j
          + 4 ^ 2 ^ j * H ^ 2 ^ j * cascadeBound j (2 * H) H μ (H * ν))
        ≤ (3:ℝ) ^ 2 ^ j * (2 * (4 ^ 2 ^ j * H ^ 2 ^ j
            * cascadeBound j (2 * H) H μ (H * ν))) := by
          exact mul_le_mul_of_nonneg_left hfold (by positivity)
      _ = 2 * 12 ^ 2 ^ j * H ^ 2 ^ j
            * cascadeBound j (2 * H) H μ (H * ν) := by
          rw [show (12:ℝ) ^ 2 ^ j = 3 ^ 2 ^ j * 4 ^ 2 ^ j by
            rw [← mul_pow]
            norm_num]
          ring
      _ ≤ 48 ^ 2 ^ j * H ^ 2 ^ j
            * cascadeBound j (2 * H) H μ (H * ν) := by
          have h8 : 2 * (12:ℝ) ^ 2 ^ j ≤ 48 ^ 2 ^ j := by
            have h9 : (48:ℝ) ^ 2 ^ j = 4 ^ 2 ^ j * 12 ^ 2 ^ j := by
              rw [← mul_pow]
              norm_num
            have h10 : (2:ℝ) ≤ 4 ^ 2 ^ j := by
              calc (2:ℝ) ≤ 4 ^ 1 := by norm_num
                _ ≤ 4 ^ 2 ^ j :=
                  pow_le_pow_right₀ (by norm_num) Nat.one_le_two_pow
            nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 12) (2 ^ j)]
          have h11 : (0:ℝ) ≤ H ^ 2 ^ j
              * cascadeBound j (2 * H) H μ (H * ν) :=
            mul_nonneg (by positivity) hBnn
          nlinarith [mul_le_mul_of_nonneg_right h8 h11]
      _ ≤ 48 ^ 2 ^ j * H ^ 2 ^ j * (48 ^ 2 ^ j * H ^ 2 ^ j
            * ((2 * (H * ν) * H ^ (j + 1) + 2)
              * (3 / Real.sqrt μ + 1))) := by
          exact mul_le_mul_of_nonneg_left hIH (by positivity)
      _ = 48 ^ 2 ^ (j + 1) * H ^ 2 ^ (j + 1)
            * ((2 * ν * H ^ (j + 1 + 1) + 2) * (3 / Real.sqrt μ + 1)) := by
          have e0 : (2:ℕ) ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
          have e1 : (48:ℝ) ^ 2 ^ (j + 1) = 48 ^ 2 ^ j * 48 ^ 2 ^ j := by
            rw [e0, pow_mul]
            ring
          have e2 : H ^ 2 ^ (j + 1) = H ^ 2 ^ j * H ^ 2 ^ j := by
            rw [e0, pow_mul]
            ring
          rw [e1, e2]
          ring

/-- **The zeta-block partial bound**: every partial sum of the zeta phase
over a dyadic block obeys the closed cascade form, with `H = M` and the
window capped at `(j+4)M`. -/
theorem zeta_block_partial_bound (j M P : ℕ) (t : ℝ) (ht : 0 < t)
    (hM : 1 ≤ M) (hMP : M ≤ P) (hP : P ≤ 2 * M)
    (hj2 : j + 2 ≤ 2 * M) :
    ‖∑ n ∈ Finset.Ico M (P + 1),
        e (-(t / (2 * Real.pi) * Real.log n))‖ ^ (2 ^ j)
      ≤ 48 ^ (2 ^ j) * (M : ℝ) ^ (2 ^ j)
        * ((2 * (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
              / ((M : ℕ) : ℝ) ^ (j + 2)) * (M : ℝ) ^ (j + 1) + 2)
          * (3 / Real.sqrt (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
              / (((j + 4) * M : ℕ) : ℝ) ^ (j + 2)) + 1)) := by
  have hwin : P + j * M + j + 2 ≤ (j + 4) * M := by nlinarith
  have hcap := log_phase_block_bound_cap j M P M ((j + 4) * M) t ht
    hM le_rfl hMP hwin
  have hM0 : (0:ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hf : (0:ℝ) < ((j + 1).factorial : ℝ) := by
    exact_mod_cast (j + 1).factorial_pos
  have hμ0 : (0:ℝ) < t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
      / (((j + 4) * M : ℕ) : ℝ) ^ (j + 2) := by
    have h1 : (0:ℝ) < (((j + 4) * M : ℕ) : ℝ) := by
      have : 1 ≤ (j + 4) * M := by nlinarith
      exact_mod_cast this
    have hπ : (0:ℝ) < Real.pi := Real.pi_pos
    positivity
  have hν0 : (0:ℝ) ≤ t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
      / ((M : ℕ) : ℝ) ^ (j + 2) := by
    have hπ : (0:ℝ) < Real.pi := Real.pi_pos
    positivity
  have hmono := cascadeBound_mono j
    (L := ((P + 1 - M : ℕ) : ℝ)) (L' := 2 * (M : ℝ))
    (H := (M : ℝ))
    (Nat.cast_nonneg _)
    (by
      have h2 : (P + 1 - M : ℕ) ≤ 2 * M := by omega
      have h3 : ((P + 1 - M : ℕ) : ℝ) ≤ ((2 * M : ℕ) : ℝ) := by
        exact_mod_cast h2
      push_cast at h3
      linarith)
    (show (1:ℝ) ≤ (M:ℝ) by exact_mod_cast hM) hμ0 hν0 le_rfl
  have hunwind := cascadeBound_unwind₂ j
    (H := (M : ℝ))
    (show (1:ℝ) ≤ (M:ℝ) by exact_mod_cast hM) hμ0 hν0
  calc ‖∑ n ∈ Finset.Ico M (P + 1),
        e (-(t / (2 * Real.pi) * Real.log n))‖ ^ (2 ^ j)
      ≤ cascadeBound j ((P + 1 - M : ℕ) : ℝ) ((M : ℕ) : ℝ)
          (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
            / (((j + 4) * M : ℕ) : ℝ) ^ (j + 2))
          (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
            / ((M : ℕ) : ℝ) ^ (j + 2)) := hcap
    _ ≤ cascadeBound j (2 * (M : ℝ)) ((M : ℕ) : ℝ)
          (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
            / (((j + 4) * M : ℕ) : ℝ) ^ (j + 2))
          (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
            / ((M : ℕ) : ℝ) ^ (j + 2)) := hmono
    _ ≤ 48 ^ (2 ^ j) * (M : ℝ) ^ (2 ^ j)
          * ((2 * (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
                / ((M : ℕ) : ℝ) ^ (j + 2)) * (M : ℝ) ^ (j + 1) + 2)
            * (3 / Real.sqrt (t / (2 * Real.pi)
                * ((j + 1).factorial : ℝ)
                / (((j + 4) * M : ℕ) : ℝ) ^ (j + 2)) + 1)) := hunwind

/-- Root extraction: a `q`-th power bound yields an `rpow` bound — the
single `rpow` site of the campaign. -/
theorem le_rpow_inv_of_pow_le {X B : ℝ} {q : ℕ} (hq : q ≠ 0)
    (hX : 0 ≤ X) (hB : X ^ q ≤ B) :
    X ≤ B ^ ((q : ℝ)⁻¹) := by
  have h1 : (X ^ q) ^ ((q : ℝ)⁻¹) ≤ B ^ ((q : ℝ)⁻¹) :=
    Real.rpow_le_rpow (pow_nonneg hX q) hB (by positivity)
  rwa [← Real.rpow_natCast X q, ← Real.rpow_mul hX,
    mul_inv_cancel₀ (by exact_mod_cast hq), Real.rpow_one] at h1

/-- **The per-block partial-sum estimate in root form**: `48·M` times the
`2^j`-th root of the main factor. -/
theorem zeta_block_E (j M P : ℕ) (t : ℝ) (ht : 0 < t) (hM : 1 ≤ M)
    (hMP : M ≤ P) (hP : P ≤ 2 * M) (hj2 : j + 2 ≤ 2 * M) :
    ‖∑ n ∈ Finset.Ico M (P + 1),
        e (-(t / (2 * Real.pi) * Real.log n))‖
      ≤ 48 * (M : ℝ)
        * ((2 * (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
              / ((M : ℕ) : ℝ) ^ (j + 2)) * (M : ℝ) ^ (j + 1) + 2)
          * (3 / Real.sqrt (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
              / (((j + 4) * M : ℕ) : ℝ) ^ (j + 2)) + 1))
          ^ (((2 ^ j : ℕ) : ℝ)⁻¹) := by
  have hq : (2 : ℕ) ^ j ≠ 0 := (Nat.two_pow_pos j).ne'
  have h1 := zeta_block_partial_bound j M P t ht hM hMP hP hj2
  have hM0 : (0:ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hBnn : (0:ℝ)
      ≤ (2 * (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
            / ((M : ℕ) : ℝ) ^ (j + 2)) * (M : ℝ) ^ (j + 1) + 2)
        * (3 / Real.sqrt (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
            / (((j + 4) * M : ℕ) : ℝ) ^ (j + 2)) + 1) := by
    have h2 : (0:ℝ) ≤ t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
        / ((M : ℕ) : ℝ) ^ (j + 2) := by positivity
    have h3 : (0:ℝ) ≤ 3 / Real.sqrt (t / (2 * Real.pi)
        * ((j + 1).factorial : ℝ)
        / (((j + 4) * M : ℕ) : ℝ) ^ (j + 2)) := by positivity
    have h4 : (0:ℝ) ≤ 2 * (t / (2 * Real.pi)
        * ((j + 1).factorial : ℝ) / ((M : ℕ) : ℝ) ^ (j + 2))
        * (M : ℝ) ^ (j + 1) := by positivity
    nlinarith
  have h2 := le_rpow_inv_of_pow_le (q := 2 ^ j) hq (norm_nonneg _) h1
  have h3 : ((48 : ℝ) ^ 2 ^ j * (M : ℝ) ^ 2 ^ j
        * ((2 * (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
              / ((M : ℕ) : ℝ) ^ (j + 2)) * (M : ℝ) ^ (j + 1) + 2)
          * (3 / Real.sqrt (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
              / (((j + 4) * M : ℕ) : ℝ) ^ (j + 2)) + 1)))
        ^ (((2 ^ j : ℕ) : ℝ)⁻¹)
      = 48 * (M : ℝ)
        * ((2 * (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
              / ((M : ℕ) : ℝ) ^ (j + 2)) * (M : ℝ) ^ (j + 1) + 2)
          * (3 / Real.sqrt (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
              / (((j + 4) * M : ℕ) : ℝ) ^ (j + 2)) + 1))
          ^ (((2 ^ j : ℕ) : ℝ)⁻¹) := by
    rw [Real.mul_rpow (by positivity) hBnn,
      Real.mul_rpow (by positivity) (by positivity),
      Real.pow_rpow_inv_natCast (by norm_num) hq,
      Real.pow_rpow_inv_natCast hM0 hq]
  rw [h3] at h2
  exact h2

/-- **The weighted zeta block**: with any decreasing weight below `1/M`,
the block's `M`-factor cancels — each dyadic block costs `48·(main)^{1/2^j}`. -/
theorem zeta_block_weighted (j M N : ℕ) (t : ℝ) (w : ℕ → ℝ)
    (ht : 0 < t) (hM : 1 ≤ M) (hMN : M ≤ N) (hN : N + 1 ≤ 2 * M)
    (hj2 : j + 2 ≤ 2 * M)
    (hw0 : ∀ n, M ≤ n → n ≤ N → 0 ≤ w n)
    (hwd : ∀ n, M ≤ n → n < N → w (n + 1) ≤ w n)
    (hwM : w M ≤ 1 / M) :
    ‖∑ n ∈ Finset.Ico M (N + 1),
        w n • e (-(t / (2 * Real.pi) * Real.log n))‖
      ≤ 48 * ((2 * (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
              / ((M : ℕ) : ℝ) ^ (j + 2)) * (M : ℝ) ^ (j + 1) + 2)
          * (3 / Real.sqrt (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
              / (((j + 4) * M : ℕ) : ℝ) ^ (j + 2)) + 1))
          ^ (((2 ^ j : ℕ) : ℝ)⁻¹) := by
  have hM0 : (0:ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hE := abel_weight_bound (w := w)
    (a := fun n => e (-(t / (2 * Real.pi) * Real.log n)))
    (M := M) (N := N)
    (E := 48 * (M : ℝ)
      * ((2 * (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
            / ((M : ℕ) : ℝ) ^ (j + 2)) * (M : ℝ) ^ (j + 1) + 2)
        * (3 / Real.sqrt (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
            / (((j + 4) * M : ℕ) : ℝ) ^ (j + 2)) + 1))
        ^ (((2 ^ j : ℕ) : ℝ)⁻¹))
    hMN hw0 hwd ?_
  · refine le_trans hE ?_
    have hπ : (0:ℝ) < Real.pi := Real.pi_pos
    have hBr : (0:ℝ)
        ≤ ((2 * (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
              / ((M : ℕ) : ℝ) ^ (j + 2)) * (M : ℝ) ^ (j + 1) + 2)
          * (3 / Real.sqrt (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
              / (((j + 4) * M : ℕ) : ℝ) ^ (j + 2)) + 1))
          ^ (((2 ^ j : ℕ) : ℝ)⁻¹) := by
      refine Real.rpow_nonneg ?_ _
      have h2 : (0:ℝ) ≤ t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
          / ((M : ℕ) : ℝ) ^ (j + 2) := by positivity
      have h3 : (0:ℝ) ≤ 3 / Real.sqrt (t / (2 * Real.pi)
          * ((j + 1).factorial : ℝ)
          / (((j + 4) * M : ℕ) : ℝ) ^ (j + 2)) := by positivity
      have h4 : (0:ℝ) ≤ 2 * (t / (2 * Real.pi)
          * ((j + 1).factorial : ℝ) / ((M : ℕ) : ℝ) ^ (j + 2))
          * (M : ℝ) ^ (j + 1) := by positivity
      nlinarith
    have h5 : w M * (48 * (M : ℝ) * ((2 * (t / (2 * Real.pi)
            * ((j + 1).factorial : ℝ) / ((M : ℕ) : ℝ) ^ (j + 2))
            * (M : ℝ) ^ (j + 1) + 2)
          * (3 / Real.sqrt (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
              / (((j + 4) * M : ℕ) : ℝ) ^ (j + 2)) + 1))
          ^ (((2 ^ j : ℕ) : ℝ)⁻¹))
        ≤ (1 / (M : ℝ)) * (48 * (M : ℝ) * ((2 * (t / (2 * Real.pi)
            * ((j + 1).factorial : ℝ) / ((M : ℕ) : ℝ) ^ (j + 2))
            * (M : ℝ) ^ (j + 1) + 2)
          * (3 / Real.sqrt (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
              / (((j + 4) * M : ℕ) : ℝ) ^ (j + 2)) + 1))
          ^ (((2 ^ j : ℕ) : ℝ)⁻¹)) := by
      refine mul_le_mul_of_nonneg_right hwM ?_
      positivity
    have h6 : (1 / (M : ℝ)) * (48 * (M : ℝ)) = 48 := by
      field_simp
    nlinarith [h5, hBr, mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 48) hM0.le) hBr]
  · intro P hP1 hP2
    rcases Nat.eq_or_lt_of_le hP1 with hPM | hPM
    · rw [← hPM, Finset.Ico_self, Finset.sum_empty, norm_zero]
      have hπ : (0:ℝ) < Real.pi := Real.pi_pos
      positivity
    · obtain ⟨P', rfl⟩ : ∃ P', P = P' + 1 := ⟨P - 1, by omega⟩
      exact zeta_block_E j M P' t ht hM (by omega) (by omega) hj2

/-- **The honest transfer**: both sandwich bounds scale with the step. -/
theorem dIter_diff_sandwich' {ψ : ℕ → ℝ} {j g : ℕ} {μ ν : ℝ} {M N n : ℕ}
    (hsand : ∀ m, M ≤ m → m ≤ N → μ ≤ dIter (j + 1) ψ m
      ∧ dIter (j + 1) ψ m ≤ ν)
    (hn : M ≤ n) (hng : n + g - 1 ≤ N) :
    (g : ℝ) * μ ≤ dIter j (fun m => ψ (m + g) - ψ m) n
    ∧ dIter j (fun m => ψ (m + g) - ψ m) n ≤ (g : ℝ) * ν := by
  rw [dIter_diff_eq_sum]
  constructor
  · have h2 : ∑ _m ∈ Finset.range g, μ
        ≤ ∑ m ∈ Finset.range g, dIter (j + 1) ψ (n + m) := by
      refine Finset.sum_le_sum fun m hm => ?_
      rw [Finset.mem_range] at hm
      exact (hsand (n + m) (by omega) (by omega)).1
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    exact h2
  · have h2 : ∑ m ∈ Finset.range g, dIter (j + 1) ψ (n + m)
        ≤ ∑ _m ∈ Finset.range g, ν := by
      refine Finset.sum_le_sum fun m hm => ?_
      rw [Finset.mem_range] at hm
      exact (hsand (n + m) (by omega) (by omega)).2
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    exact h2

/-- The trivial cap: an exponential sum is at most its length. -/
theorem norm_sum_e_le_card (W : Finset ℕ) (ψ : ℕ → ℝ) :
    ‖∑ n ∈ W, e (ψ n)‖ ≤ (W.card : ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_congr rfl (fun n _ => norm_e (ψ n)), Finset.sum_const,
    nsmul_eq_mul, mul_one]

/-- **The per-`g` cascade bound with trivial caps** — the exact object the
end-to-end numerical check validated. -/
noncomputable def cascadeBound' : ℕ → ℝ → ℕ → ℝ → ℝ → ℝ
  | 0, L, _H, μ, ν => min L ((ν * L + 2) * (3 / Real.sqrt μ + 1))
  | (j + 1), L, H, μ, ν =>
      min (L ^ 2 ^ (j + 1))
        (((L + H) / H) ^ 2 ^ j
          * (2 ^ 2 ^ j * L ^ 2 ^ j
            + 4 ^ 2 ^ j * (H : ℝ) ^ (2 ^ j - 1)
              * ∑ g ∈ Finset.Ico 1 H,
                  cascadeBound' j L H ((g : ℝ) * μ) ((g : ℝ) * ν)))

theorem cascadeBound'_nonneg (j : ℕ) {L : ℝ} {H : ℕ} {μ ν : ℝ}
    (hL : 0 ≤ L) (hH : 1 ≤ H) (hμ : 0 < μ) (hν : 0 ≤ ν) :
    0 ≤ cascadeBound' j L H μ ν := by
  induction j generalizing μ ν with
  | zero =>
    rw [cascadeBound']
    refine le_min hL ?_
    have h1 : (0:ℝ) ≤ 3 / Real.sqrt μ := by positivity
    have h2 : (0:ℝ) ≤ ν * L := mul_nonneg hν hL
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ ν * L + 2) h1]
  | succ j ih =>
    rw [cascadeBound']
    have hHR : (0:ℝ) < (H:ℝ) := by exact_mod_cast hH
    refine le_min (pow_nonneg hL _) ?_
    have h1 : (0:ℝ) ≤ ∑ g ∈ Finset.Ico 1 H,
        cascadeBound' j L H ((g : ℝ) * μ) ((g : ℝ) * ν) := by
      refine Finset.sum_nonneg fun g hg => ?_
      rw [Finset.mem_Ico] at hg
      have hg0 : (0:ℝ) < (g:ℝ) := by exact_mod_cast hg.1
      exact ih (mul_pos hg0 hμ) (mul_nonneg hg0.le hν)
    have h2 : (0:ℝ) ≤ (L + H) / H := div_nonneg (by linarith) hHR.le
    have h3 : (0:ℝ) ≤ (2:ℝ) ^ 2 ^ j * L ^ 2 ^ j :=
      mul_nonneg (by positivity) (pow_nonneg hL _)
    have h4 : (0:ℝ) ≤ (4:ℝ) ^ 2 ^ j * (H:ℝ) ^ (2 ^ j - 1) := by positivity
    have h5 : (0:ℝ) ≤ ((L + H) / H) ^ 2 ^ j := pow_nonneg h2 _
    nlinarith [mul_nonneg h5 (add_nonneg h3 (mul_nonneg h4 h1))]

theorem cascadeBound'_mono_L (j : ℕ) {L L' : ℝ} {H : ℕ} {μ ν : ℝ}
    (hL : 0 ≤ L) (hLL : L ≤ L') (hH : 1 ≤ H) (hμ : 0 < μ) (hν : 0 ≤ ν) :
    cascadeBound' j L H μ ν ≤ cascadeBound' j L' H μ ν := by
  induction j generalizing μ ν with
  | zero =>
    rw [cascadeBound', cascadeBound']
    refine min_le_min hLL ?_
    have h1 : (0:ℝ) ≤ 3 / Real.sqrt μ + 1 := by positivity
    have h2 : ν * L + 2 ≤ ν * L' + 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right h2 h1
  | succ j ih =>
    rw [cascadeBound', cascadeBound']
    have hHR : (0:ℝ) < (H:ℝ) := by exact_mod_cast hH
    refine min_le_min (pow_le_pow_left₀ hL hLL _) ?_
    have hsum : ∑ g ∈ Finset.Ico 1 H,
        cascadeBound' j L H ((g : ℝ) * μ) ((g : ℝ) * ν)
        ≤ ∑ g ∈ Finset.Ico 1 H,
          cascadeBound' j L' H ((g : ℝ) * μ) ((g : ℝ) * ν) := by
      refine Finset.sum_le_sum fun g hg => ?_
      rw [Finset.mem_Ico] at hg
      have hg0 : (0:ℝ) < (g:ℝ) := by exact_mod_cast hg.1
      exact ih (mul_pos hg0 hμ) (mul_nonneg hg0.le hν)
    have hsum0 : (0:ℝ) ≤ ∑ g ∈ Finset.Ico 1 H,
        cascadeBound' j L H ((g : ℝ) * μ) ((g : ℝ) * ν) := by
      refine Finset.sum_nonneg fun g hg => ?_
      rw [Finset.mem_Ico] at hg
      have hg0 : (0:ℝ) < (g:ℝ) := by exact_mod_cast hg.1
      exact cascadeBound'_nonneg j hL hH (mul_pos hg0 hμ)
        (mul_nonneg hg0.le hν)
    have h2 : (0:ℝ) ≤ (L + H) / H := div_nonneg (by linarith) hHR.le
    have h5 : ((L + H) / H) ^ 2 ^ j ≤ ((L' + H) / H) ^ 2 ^ j := by
      refine pow_le_pow_left₀ h2 ?_ _
      exact div_le_div_of_nonneg_right (by linarith) hHR.le
    have h3 : (0:ℝ) ≤ (2:ℝ) ^ 2 ^ j := by positivity
    have h4 : (0:ℝ) ≤ (4:ℝ) ^ 2 ^ j * (H:ℝ) ^ (2 ^ j - 1) := by positivity
    have hL3 : L ^ 2 ^ j ≤ L' ^ 2 ^ j := pow_le_pow_left₀ hL hLL _
    have hinner : 2 ^ 2 ^ j * L ^ 2 ^ j
          + 4 ^ 2 ^ j * (H:ℝ) ^ (2 ^ j - 1)
            * ∑ g ∈ Finset.Ico 1 H,
                cascadeBound' j L H ((g : ℝ) * μ) ((g : ℝ) * ν)
        ≤ 2 ^ 2 ^ j * L' ^ 2 ^ j
          + 4 ^ 2 ^ j * (H:ℝ) ^ (2 ^ j - 1)
            * ∑ g ∈ Finset.Ico 1 H,
                cascadeBound' j L' H ((g : ℝ) * μ) ((g : ℝ) * ν) := by
      have h6 := mul_le_mul_of_nonneg_left hsum h4
      nlinarith [mul_le_mul_of_nonneg_left hL3 h3]
    have hinner0 : (0:ℝ) ≤ 2 ^ 2 ^ j * L ^ 2 ^ j
          + 4 ^ 2 ^ j * (H:ℝ) ^ (2 ^ j - 1)
            * ∑ g ∈ Finset.Ico 1 H,
                cascadeBound' j L H ((g : ℝ) * μ) ((g : ℝ) * ν) := by
      have h7 : (0:ℝ) ≤ L ^ 2 ^ j := pow_nonneg hL _
      nlinarith [mul_nonneg h4 hsum0]
    have h8 : (0:ℝ) ≤ ((L' + H) / H) ^ 2 ^ j :=
      pow_nonneg (div_nonneg (by linarith) hHR.le) _
    nlinarith [mul_le_mul h5 hinner hinner0 h8]

/-- **The per-`g` cascade** (honest transfer, trivial caps): the refined
form of `vdck_pow` that the end-to-end check validated. -/
theorem vdck_pow' (j : ℕ) :
    ∀ (ψ : ℕ → ℝ) (M N H : ℕ) (μ ν : ℝ),
      0 < μ → μ ≤ ν → 1 ≤ H → H ≤ M → M ≤ N →
      (∀ n, M ≤ n → n ≤ N + j * H →
        μ ≤ dIter (j + 2) ψ n ∧ dIter (j + 2) ψ n ≤ ν) →
      ‖∑ n ∈ Finset.Ico M (N + 1), e (ψ n)‖ ^ (2 ^ j)
        ≤ cascadeBound' j ((N + 1 - M : ℕ) : ℝ) H μ ν := by
  induction j with
  | zero =>
    intro ψ M N H μ ν hμ hμν hH hHM hMN hsand
    simp only [Nat.zero_add, Nat.zero_mul, Nat.add_zero] at hsand
    have hpow : (2 : ℕ) ^ 0 = 1 := rfl
    rw [hpow, pow_one, cascadeBound']
    refine le_min ?_ ?_
    · have h1 := norm_sum_e_le_card (Finset.Ico M (N + 1)) ψ
      rwa [Nat.card_Ico] at h1
    · have hsqrt : (0:ℝ) < Real.sqrt μ := Real.sqrt_pos.mpr hμ
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
    rw [cascadeBound']
    refine le_min ?_ ?_
    · refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
      have h1 := norm_sum_e_le_card (Finset.Ico M (N + 1)) ψ
      rwa [Nat.card_Ico] at h1
    · have hexp : ‖∑ n ∈ Finset.Ico M (N + 1), e (ψ n)‖ ^ 2 ^ (j + 1)
          = (‖∑ n ∈ Finset.Ico M (N + 1), e (ψ n)‖ ^ 2) ^ 2 ^ j := by
        rw [← pow_mul]
        congr 1
        rw [pow_succ']
      rw [hexp]
      have hweyl := weyl_differencing (φ := ψ) (H := H) hH hHM hMN
      have hs1 := pow_le_pow_left₀ (by positivity) hweyl (2 ^ j)
      refine le_trans hs1 ?_
      rw [mul_pow]
      refine mul_le_mul_of_nonneg_left ?_
        (pow_nonneg (div_nonneg (by linarith) hHR.le) _)
      -- per-g bounds
      have hper : ∀ g ∈ Finset.Ico 1 H,
          ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (ψ (m + g) - ψ m)‖ ^ 2 ^ j
            ≤ cascadeBound' j ((N + 1 - M : ℕ) : ℝ) H
                ((g : ℝ) * μ) ((g : ℝ) * ν) := by
        intro g hg
        rw [Finset.mem_Ico] at hg
        have hg0 : (0:ℝ) < (g:ℝ) := by exact_mod_cast hg.1
        have hBnn := cascadeBound'_nonneg j hL0 hH
          (mul_pos hg0 hμ) (mul_nonneg hg0.le hν0.le)
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
              (g:ℝ) * μ ≤ dIter (j + 2) (fun m => ψ (m + g) - ψ m) n
              ∧ dIter (j + 2) (fun m => ψ (m + g) - ψ m) n
                ≤ (g:ℝ) * ν := by
            intro n h1 h2
            exact dIter_diff_sandwich' (ψ := ψ) (j := j + 2) (g := g)
              (μ := μ) (ν := ν) (M := M) (N := N + (j + 1) * H)
              (fun m hm1 hm2 => hsand m hm1 (by omega))
              h1 (by
                have hjH : j * H + H = (j + 1) * H := by ring
                omega)
          have hIH := ih (fun m => ψ (m + g) - ψ m) M (N - g) H
            ((g:ℝ) * μ) ((g:ℝ) * ν) (mul_pos hg0 hμ)
            (mul_le_mul_of_nonneg_left hμν hg0.le)
            hH hHM (by omega) hsand'
          refine le_trans hIH (cascadeBound'_mono_L j (Nat.cast_nonneg _)
            ?_ hH (mul_pos hg0 hμ) (mul_nonneg hg0.le hν0.le))
          exact_mod_cast (by omega : (N - g) + 1 - M ≤ N + 1 - M)
      -- assemble: (L + 2X)^q ≤ 2^q L^q + 4^q H^{q-1} ∑_g (per-g)
      have hX0 : (0:ℝ) ≤ ∑ g ∈ Finset.Ico 1 H,
          ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (ψ (m + g) - ψ m)‖ :=
        Finset.sum_nonneg fun g _ => norm_nonneg _
      have hA := add_pow_le_two_pow_mul (a := ((N + 1 - M : ℕ) : ℝ))
        (b := 2 * ∑ g ∈ Finset.Ico 1 H,
          ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (ψ (m + g) - ψ m)‖)
        hL0 (by linarith) (2 ^ j)
      have hXq := sum_pow_le_card_pow_mul (s := Finset.Ico 1 H)
        (f := fun g => ‖∑ m ∈ Finset.Ico M (N + 1 - g),
          e (ψ (m + g) - ψ m)‖)
        (fun i _ => norm_nonneg _) (2 ^ j) hq1
      have hsum_per := Finset.sum_le_sum hper
      have hcard : (((Finset.Ico 1 H).card : ℕ) : ℝ) ^ (2 ^ j - 1)
          ≤ (H : ℝ) ^ (2 ^ j - 1) := by
        refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _
        rw [Nat.card_Ico]
        exact_mod_cast (by omega : H - 1 ≤ H)
      have hSnn : (0:ℝ) ≤ ∑ g ∈ Finset.Ico 1 H,
          ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (ψ (m + g) - ψ m)‖ ^ 2 ^ j :=
        Finset.sum_nonneg fun g _ => pow_nonneg (norm_nonneg _) _
      have hcnn : (0:ℝ) ≤ (((Finset.Ico 1 H).card : ℕ) : ℝ) ^ (2 ^ j - 1) :=
        pow_nonneg (Nat.cast_nonneg _) _
      have hXfin : (∑ g ∈ Finset.Ico 1 H,
          ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (ψ (m + g) - ψ m)‖) ^ 2 ^ j
          ≤ (H : ℝ) ^ (2 ^ j - 1) * ∑ g ∈ Finset.Ico 1 H,
              cascadeBound' j ((N + 1 - M : ℕ) : ℝ) H
                ((g : ℝ) * μ) ((g : ℝ) * ν) := by
        calc (∑ g ∈ Finset.Ico 1 H,
              ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (ψ (m + g) - ψ m)‖) ^ 2 ^ j
            ≤ (((Finset.Ico 1 H).card : ℕ) : ℝ) ^ (2 ^ j - 1)
                * ∑ g ∈ Finset.Ico 1 H,
                  ‖∑ m ∈ Finset.Ico M (N + 1 - g),
                    e (ψ (m + g) - ψ m)‖ ^ 2 ^ j := hXq
          _ ≤ (H : ℝ) ^ (2 ^ j - 1) * ∑ g ∈ Finset.Ico 1 H,
                cascadeBound' j ((N + 1 - M : ℕ) : ℝ) H
                  ((g : ℝ) * μ) ((g : ℝ) * ν) := by
              exact mul_le_mul hcard hsum_per hSnn
                (pow_nonneg hHR.le _)
      have h2q : (0:ℝ) ≤ (2:ℝ) ^ 2 ^ j := by positivity
      have hmp : ((2:ℝ) * ∑ g ∈ Finset.Ico 1 H,
          ‖∑ m ∈ Finset.Ico M (N + 1 - g), e (ψ (m + g) - ψ m)‖) ^ 2 ^ j
          = 2 ^ 2 ^ j * (∑ g ∈ Finset.Ico 1 H,
            ‖∑ m ∈ Finset.Ico M (N + 1 - g),
              e (ψ (m + g) - ψ m)‖) ^ 2 ^ j :=
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
          ≤ 4 ^ 2 ^ j * ((H : ℝ) ^ (2 ^ j - 1)
            * ∑ g ∈ Finset.Ico 1 H,
                cascadeBound' j ((N + 1 - M : ℕ) : ℝ) H
                  ((g : ℝ) * μ) ((g : ℝ) * ν)) :=
        mul_le_mul_of_nonneg_left hXfin (by positivity)
      nlinarith [hA, hstep2, hstep3]

/-- **Dyadic decomposition** of an initial segment: blocks `[2^i, 2^{i+1})`
plus the final partial block. -/
theorem sum_dyadic_decomp (f : ℕ → ℂ) (T K : ℕ)
    (hK : 2 ^ K ≤ T + 1) :
    ∑ n ∈ Finset.Ico 1 (T + 1), f n
      = (∑ i ∈ Finset.range K,
          ∑ n ∈ Finset.Ico (2 ^ i) (2 ^ (i + 1)), f n)
        + ∑ n ∈ Finset.Ico (2 ^ K) (T + 1), f n := by
  induction K with
  | zero =>
    simp
  | succ K ih =>
    have h1 : 2 ^ K ≤ T + 1 := le_trans (by
      have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
        (Nat.le_succ K)
      exact this) hK
    rw [ih h1, Finset.sum_range_succ]
    have h2 : ∑ n ∈ Finset.Ico (2 ^ K) (T + 1), f n
        = (∑ n ∈ Finset.Ico (2 ^ K) (2 ^ (K + 1)), f n)
          + ∑ n ∈ Finset.Ico (2 ^ (K + 1)) (T + 1), f n := by
      rw [Finset.sum_Ico_consecutive]
      · exact Nat.pow_le_pow_right (by norm_num) (Nat.le_succ K)
      · exact hK
    rw [h2]
    ring

/-- The head norm against per-block bounds. -/
theorem norm_head_le_of_blocks (f : ℕ → ℂ) (T K : ℕ) (σ : ℕ → ℝ) (R : ℝ)
    (hK : 2 ^ K ≤ T + 1)
    (hσ : ∀ i, i < K →
      ‖∑ n ∈ Finset.Ico (2 ^ i) (2 ^ (i + 1)), f n‖ ≤ σ i)
    (hR : ‖∑ n ∈ Finset.Ico (2 ^ K) (T + 1), f n‖ ≤ R) :
    ‖∑ n ∈ Finset.Ico 1 (T + 1), f n‖
      ≤ (∑ i ∈ Finset.range K, σ i) + R := by
  rw [sum_dyadic_decomp f T K hK]
  refine le_trans (norm_add_le _ _) ?_
  refine add_le_add ?_ hR
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun i hi => ?_
  rw [Finset.mem_range] at hi
  exact hσ i hi

/-- **The class-zero savings lemma**: in the regime `ν ≤ 1 ≤ νL`, the base
cascade bound saves the factor `12·ν/√μ`. -/
theorem cascadeBound'_class_zero {L : ℝ} {H : ℕ} {μ ν : ℝ}
    (hμ : 0 < μ) (hμν : μ ≤ ν) (hν1 : ν ≤ 1) (hνL : 1 ≤ ν * L) :
    cascadeBound' 0 L H μ ν ≤ 12 * (ν / Real.sqrt μ) * L := by
  have hL0 : (0:ℝ) < L := by nlinarith
  have hν0 : (0:ℝ) < ν := lt_of_lt_of_le hμ hμν
  have hsμ : (0:ℝ) < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hμ1 : μ ≤ 1 := le_trans hμν hν1
  have hsμ1 : Real.sqrt μ ≤ 1 := by
    rw [show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt hμ1
  have hsμν : Real.sqrt μ ≤ ν * L := by
    nlinarith
  rw [cascadeBound']
  refine le_trans (min_le_right _ _) ?_
  -- expand: 3νL/√μ + νL + 6/√μ + 2 ≤ 12(ν/√μ)L
  have hkey : (ν * L + 2) * (3 / Real.sqrt μ + 1)
      = 3 * (ν / Real.sqrt μ) * L + ν * L + 6 / Real.sqrt μ + 2 := by
    field_simp
    ring
  rw [hkey]
  have h1 : ν * L ≤ (ν / Real.sqrt μ) * L := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hsμ]
    nlinarith
  have h2 : 6 / Real.sqrt μ ≤ 6 * ((ν / Real.sqrt μ) * L) := by
    rw [div_le_iff₀ hsμ] at *
    have h3 : (ν / Real.sqrt μ) * L * Real.sqrt μ = ν * L := by
      field_simp
    nlinarith [hνL]
  have h4 : (2:ℝ) ≤ 2 * ((ν / Real.sqrt μ) * L) := by
    have h5 : (1:ℝ) ≤ (ν / Real.sqrt μ) * L := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hsμ]
      nlinarith
    linarith
  nlinarith [h1, h2, h4]

/-- **The class-one savings lemma**: one Weyl unfold in the uncapped regime
`Hν ≤ 1` — the `√g`-sum delivers the `√H`-trade. -/
theorem cascadeBound'_class_one {L : ℝ} {H : ℕ} {μ ν : ℝ}
    (hμ : 0 < μ) (hμν : μ ≤ ν) (hH : 1 ≤ H) (hHL : (H:ℝ) ≤ L)
    (hHν : (H:ℝ) * ν ≤ 1) (hνL : 1 ≤ ν * L) :
    cascadeBound' 1 L H μ ν
      ≤ (4 / H + 96 * (ν / Real.sqrt μ) * Real.sqrt H) * L ^ 2 := by
  have hHR : (0:ℝ) < (H:ℝ) := by exact_mod_cast hH
  have hν0 : (0:ℝ) < ν := lt_of_lt_of_le hμ hμν
  have hH1 : (1:ℝ) ≤ (H:ℝ) := by exact_mod_cast hH
  have hν1 : ν ≤ 1 := by
    have h0 := mul_le_mul_of_nonneg_right hH1 hν0.le
    nlinarith
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le hHR hHL
  have hsμ : (0:ℝ) < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hsH : (0:ℝ) < Real.sqrt H := Real.sqrt_pos.mpr hHR
  rw [cascadeBound']
  refine le_trans (min_le_right _ _) ?_
  have hpow0 : (2:ℕ) ^ 0 = 1 := rfl
  rw [hpow0]
  rw [show (1:ℕ) - 1 = 0 from rfl]
  simp only [pow_one, pow_zero, mul_one]
  -- per-g: class zero at (gμ, gν)
  have hper : ∀ g ∈ Finset.Ico 1 H,
      cascadeBound' 0 L H ((g:ℝ) * μ) ((g:ℝ) * ν)
        ≤ 12 * (ν / Real.sqrt μ) * Real.sqrt g * L := by
    intro g hg
    rw [Finset.mem_Ico] at hg
    have hg0 : (0:ℝ) < (g:ℝ) := by exact_mod_cast hg.1
    have hgH : (g:ℝ) ≤ (H:ℝ) := by exact_mod_cast hg.2.le
    have hga : (1:ℝ) ≤ (g:ℝ) := by exact_mod_cast hg.1
    have hgν1 : (g:ℝ) * ν ≤ 1 := by
      have h0 := mul_le_mul_of_nonneg_right hgH hν0.le
      nlinarith
    have hgνL : 1 ≤ (g:ℝ) * ν * L := by
      have h0 : (0:ℝ) ≤ ν * L := by positivity
      have h1 := mul_le_mul_of_nonneg_right hga h0
      nlinarith
    have h1 := cascadeBound'_class_zero (L := L) (H := H)
      (μ := (g:ℝ) * μ) (ν := (g:ℝ) * ν)
      (mul_pos hg0 hμ) (mul_le_mul_of_nonneg_left hμν hg0.le)
      hgν1 hgνL
    refine le_trans h1 (le_of_eq ?_)
    have h2 : Real.sqrt ((g:ℝ) * μ) = Real.sqrt g * Real.sqrt μ :=
      Real.sqrt_mul hg0.le μ
    rw [h2]
    have h3 : Real.sqrt g > 0 := Real.sqrt_pos.mpr hg0
    have h4 : (g:ℝ) = Real.sqrt g * Real.sqrt g :=
      (Real.mul_self_sqrt hg0.le).symm
    field_simp
    nlinarith [h4]
  -- sum: crude √g ≤ √H
  have hsum : ∑ g ∈ Finset.Ico 1 H,
      cascadeBound' 0 L H ((g:ℝ) * μ) ((g:ℝ) * ν)
      ≤ 12 * (ν / Real.sqrt μ) * Real.sqrt H * L * H := by
    have h5 : ∀ g ∈ Finset.Ico 1 H,
        cascadeBound' 0 L H ((g:ℝ) * μ) ((g:ℝ) * ν)
          ≤ 12 * (ν / Real.sqrt μ) * Real.sqrt H * L := by
      intro g hg
      refine le_trans (hper g hg) ?_
      rw [Finset.mem_Ico] at hg
      have hgH : (g:ℝ) ≤ (H:ℝ) := by exact_mod_cast hg.2.le
      have h6 : Real.sqrt g ≤ Real.sqrt H := Real.sqrt_le_sqrt hgH
      have h7 : (0:ℝ) ≤ 12 * (ν / Real.sqrt μ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right h6 hL0.le]
    refine le_trans (Finset.sum_le_sum h5) ?_
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
    have h8 : ((H - 1 : ℕ) : ℝ) ≤ (H : ℝ) := by
      exact_mod_cast (by omega : H - 1 ≤ H)
    have h9 : (0:ℝ) ≤ 12 * (ν / Real.sqrt μ) * Real.sqrt H * L := by
      positivity
    nlinarith [mul_le_mul_of_nonneg_right h8 h9]
  -- assemble
  have hLH2 : (L + (H:ℝ)) / H ≤ 2 * L / H := by
    refine div_le_div_of_nonneg_right ?_ hHR.le
    linarith
  have hinner : 2 * L + 4 * ∑ g ∈ Finset.Ico 1 H,
      cascadeBound' 0 L H ((g:ℝ) * μ) ((g:ℝ) * ν)
      ≤ 2 * L + 48 * (ν / Real.sqrt μ) * Real.sqrt H * L * H := by
    nlinarith [hsum]
  have hinner0 : (0:ℝ) ≤ 2 * L + 4 * ∑ g ∈ Finset.Ico 1 H,
      cascadeBound' 0 L H ((g:ℝ) * μ) ((g:ℝ) * ν) := by
    have h10 : (0:ℝ) ≤ ∑ g ∈ Finset.Ico 1 H,
        cascadeBound' 0 L H ((g:ℝ) * μ) ((g:ℝ) * ν) := by
      refine Finset.sum_nonneg fun g hg => ?_
      rw [Finset.mem_Ico] at hg
      have hg0 : (0:ℝ) < (g:ℝ) := by exact_mod_cast hg.1
      exact cascadeBound'_nonneg 0 hL0.le hH
        (mul_pos hg0 hμ) (mul_nonneg hg0.le hν0.le)
    linarith
  have hLH0 : (0:ℝ) ≤ (L + (H:ℝ)) / H :=
    div_nonneg (by linarith) hHR.le
  calc (L + (H:ℝ)) / H * (2 * L + 4 * ∑ g ∈ Finset.Ico 1 H,
        cascadeBound' 0 L H ((g:ℝ) * μ) ((g:ℝ) * ν))
      ≤ (2 * L / H) * (2 * L + 48 * (ν / Real.sqrt μ)
          * Real.sqrt H * L * H) := by
        refine mul_le_mul hLH2 hinner hinner0 ?_
        positivity
    _ = 4 * L ^ 2 / H + 96 * (ν / Real.sqrt μ)
          * (Real.sqrt H * Real.sqrt H) * Real.sqrt H * L ^ 2 / H := by
        rw [Real.mul_self_sqrt hHR.le]
        field_simp
        ring
    _ = (4 / H + 96 * (ν / Real.sqrt μ) * Real.sqrt H) * L ^ 2 := by
        have h11 : Real.sqrt H * Real.sqrt H = (H:ℝ) :=
          Real.mul_self_sqrt hHR.le
        rw [h11]
        field_simp

set_option maxHeartbeats 800000 in
/-- **The class-two savings lemma**: two Weyl unfolds in the regime
`H²ν ≤ 1` — the `√H`-trade iterates to the `H`-trade. -/
theorem cascadeBound'_class_two {L : ℝ} {H : ℕ} {μ ν : ℝ}
    (hμ : 0 < μ) (hμν : μ ≤ ν) (hH : 1 ≤ H) (hHL : (H:ℝ) ≤ L)
    (hH2ν : (H:ℝ) ^ 2 * ν ≤ 1) (hνL : 1 ≤ ν * L) :
    cascadeBound' 2 L H μ ν
      ≤ (272 / H + 6144 * (ν / Real.sqrt μ) * (H:ℝ)) * L ^ 4 := by
  have hHR : (0:ℝ) < (H:ℝ) := by exact_mod_cast hH
  have hH1 : (1:ℝ) ≤ (H:ℝ) := by exact_mod_cast hH
  have hν0 : (0:ℝ) < ν := lt_of_lt_of_le hμ hμν
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le hHR hHL
  have hsμ : (0:ℝ) < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hsH : (0:ℝ) < Real.sqrt H := Real.sqrt_pos.mpr hHR
  have hHH : Real.sqrt H * Real.sqrt H = (H:ℝ) :=
    Real.mul_self_sqrt hHR.le
  rw [show (2:ℕ) = 1 + 1 from rfl, cascadeBound']
  refine le_trans (min_le_right _ _) ?_
  rw [show (2:ℕ) ^ 1 = 2 from rfl, show (2:ℕ) - 1 = 1 from rfl,
    pow_one]
  -- per-g: class one at (gμ, gν)
  have hper : ∀ g ∈ Finset.Ico 1 H,
      cascadeBound' 1 L H ((g:ℝ) * μ) ((g:ℝ) * ν)
        ≤ (4 / H + 96 * (ν / Real.sqrt μ) * (H:ℝ)) * L ^ 2 := by
    intro g hg
    rw [Finset.mem_Ico] at hg
    have hg0 : (0:ℝ) < (g:ℝ) := by exact_mod_cast hg.1
    have hga : (1:ℝ) ≤ (g:ℝ) := by exact_mod_cast hg.1
    have hgH : (g:ℝ) ≤ (H:ℝ) := by exact_mod_cast hg.2.le
    have hgHν : (H:ℝ) * ((g:ℝ) * ν) ≤ 1 := by
      have h0 : (H:ℝ) * ((g:ℝ) * ν) ≤ (H:ℝ) * ((H:ℝ) * ν) := by
        have := mul_le_mul_of_nonneg_right hgH hν0.le
        nlinarith
      nlinarith
    have hgνL : 1 ≤ (g:ℝ) * ν * L := by
      have h0 : (0:ℝ) ≤ ν * L := by positivity
      have h1 := mul_le_mul_of_nonneg_right hga h0
      nlinarith
    have h1 := cascadeBound'_class_one (L := L) (H := H)
      (μ := (g:ℝ) * μ) (ν := (g:ℝ) * ν)
      (mul_pos hg0 hμ) (mul_le_mul_of_nonneg_left hμν hg0.le)
      hH hHL hgHν hgνL
    refine le_trans h1 ?_
    -- (gν)/√(gμ) = √g·(ν/√μ) ≤ √H·(ν/√μ); then √g-free bound with √H·√H = H
    have h2 : Real.sqrt ((g:ℝ) * μ) = Real.sqrt g * Real.sqrt μ :=
      Real.sqrt_mul hg0.le μ
    have hsg : (0:ℝ) < Real.sqrt g := Real.sqrt_pos.mpr hg0
    have h3 : (g:ℝ) * ν / Real.sqrt ((g:ℝ) * μ)
        = Real.sqrt g * (ν / Real.sqrt μ) := by
      rw [h2]
      have h4 : (g:ℝ) = Real.sqrt g * Real.sqrt g :=
        (Real.mul_self_sqrt hg0.le).symm
      field_simp
      nlinarith [h4]
    rw [h3]
    have h5 : Real.sqrt g ≤ Real.sqrt H := Real.sqrt_le_sqrt hgH
    have h6 : Real.sqrt g * (ν / Real.sqrt μ) * Real.sqrt H
        ≤ (ν / Real.sqrt μ) * (H:ℝ) := by
      have h7 : Real.sqrt g * Real.sqrt H ≤ (H:ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_right h5 hsH.le]
      have h8 : (0:ℝ) ≤ ν / Real.sqrt μ := by positivity
      nlinarith [mul_le_mul_of_nonneg_right h7 h8]
    have h9 : (0:ℝ) ≤ L ^ 2 := by positivity
    refine mul_le_mul_of_nonneg_right ?_ h9
    nlinarith [h6]
  -- sum over g
  have hsum : ∑ g ∈ Finset.Ico 1 H,
      cascadeBound' 1 L H ((g:ℝ) * μ) ((g:ℝ) * ν)
      ≤ (4 + 96 * (ν / Real.sqrt μ) * (H:ℝ) ^ 2) * L ^ 2 := by
    refine le_trans (Finset.sum_le_sum hper) ?_
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
    have h8 : ((H - 1 : ℕ) : ℝ) ≤ (H : ℝ) := by
      exact_mod_cast (by omega : H - 1 ≤ H)
    have h9 : (0:ℝ) ≤ (4 / H + 96 * (ν / Real.sqrt μ) * (H:ℝ)) * L ^ 2 := by
      positivity
    calc ((H - 1 : ℕ) : ℝ)
          * ((4 / H + 96 * (ν / Real.sqrt μ) * (H:ℝ)) * L ^ 2)
        ≤ (H:ℝ) * ((4 / H + 96 * (ν / Real.sqrt μ) * (H:ℝ)) * L ^ 2) :=
          mul_le_mul_of_nonneg_right h8 h9
      _ = (4 + 96 * (ν / Real.sqrt μ) * (H:ℝ) ^ 2) * L ^ 2 := by
          field_simp
  -- assemble
  have hLH2 : (L + (H:ℝ)) / H ≤ 2 * L / H := by
    refine div_le_div_of_nonneg_right ?_ hHR.le
    linarith
  have hLH0 : (0:ℝ) ≤ (L + (H:ℝ)) / H := div_nonneg (by linarith) hHR.le
  have hsum0 : (0:ℝ) ≤ ∑ g ∈ Finset.Ico 1 H,
      cascadeBound' 1 L H ((g:ℝ) * μ) ((g:ℝ) * ν) := by
    refine Finset.sum_nonneg fun g hg => ?_
    rw [Finset.mem_Ico] at hg
    have hg0 : (0:ℝ) < (g:ℝ) := by exact_mod_cast hg.1
    exact cascadeBound'_nonneg 1 hL0.le hH
      (mul_pos hg0 hμ) (mul_nonneg hg0.le hν0.le)
  have hinner : 2 ^ 2 * L ^ 2 + 4 ^ 2 * (H:ℝ)
        * ∑ g ∈ Finset.Ico 1 H,
            cascadeBound' 1 L H ((g:ℝ) * μ) ((g:ℝ) * ν)
      ≤ (68 * (H:ℝ) + 1536 * (ν / Real.sqrt μ) * (H:ℝ) ^ 3) * L ^ 2 := by
    have h11 := mul_le_mul_of_nonneg_left hsum
      (show (0:ℝ) ≤ 4 ^ 2 * (H:ℝ) by positivity)
    have h12 : (4:ℝ) ^ 2 * (H:ℝ)
          * ((4 + 96 * (ν / Real.sqrt μ) * (H:ℝ) ^ 2) * L ^ 2)
        = (64 * (H:ℝ) + 1536 * (ν / Real.sqrt μ) * (H:ℝ) ^ 3) * L ^ 2 := by
      ring
    have h13 : (2:ℝ) ^ 2 * L ^ 2 ≤ 4 * (H:ℝ) * L ^ 2 := by
      nlinarith [sq_nonneg L]
    nlinarith [h11, h13]
  have hinner0 : (0:ℝ) ≤ 2 ^ 2 * L ^ 2 + 4 ^ 2 * (H:ℝ)
        * ∑ g ∈ Finset.Ico 1 H,
            cascadeBound' 1 L H ((g:ℝ) * μ) ((g:ℝ) * ν) := by
    have h14 : (0:ℝ) ≤ (4:ℝ) ^ 2 * (H:ℝ) := by positivity
    nlinarith [mul_nonneg h14 hsum0, sq_nonneg L]
  have hpre : ((L + (H:ℝ)) / H) ^ 2 ≤ (2 * L / H) ^ 2 :=
    pow_le_pow_left₀ hLH0 hLH2 2
  have hpre0 : (0:ℝ) ≤ ((L + (H:ℝ)) / H) ^ 2 := pow_nonneg hLH0 2
  calc ((L + (H:ℝ)) / H) ^ 2 * (2 ^ 2 * L ^ 2 + 4 ^ 2 * (H:ℝ)
        * ∑ g ∈ Finset.Ico 1 H,
            cascadeBound' 1 L H ((g:ℝ) * μ) ((g:ℝ) * ν))
      ≤ (2 * L / H) ^ 2
        * ((68 * (H:ℝ) + 1536 * (ν / Real.sqrt μ) * (H:ℝ) ^ 3) * L ^ 2) := by
        refine mul_le_mul hpre hinner hinner0 (pow_nonneg ?_ 2)
        positivity
    _ = (272 / H + 6144 * (ν / Real.sqrt μ) * (H:ℝ)) * L ^ 4 := by
        field_simp
        ring

end ExpSums

end MoltResearch
