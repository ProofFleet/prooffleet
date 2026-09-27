import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import MoltResearch.Discrepancy.ExpSums
import Mathlib.Analysis.Real.Pi.Bounds

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
            refine Finset.prod_le_prod₀ (fun i _ => by positivity)
              (fun i _ => ?_)
            have h2 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
            linarith
    · calc ∏ i ∈ Finset.range (k + 1), ((n : ℝ) + i + x)
          ≤ ∏ _i ∈ Finset.range (k + 1), ((n : ℝ) + k + 1) := by
            refine Finset.prod_le_prod₀ (fun i _ => by positivity)
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
      (by apply intervalIntegrable_const) hint ?_
    intro x hx
    rw [hpt x hx]
    obtain ⟨hP0, hPl, hPu⟩ := hPbounds x hx
    have hfac0 : (0 : ℝ) ≤ (k.factorial : ℝ) := Nat.cast_nonneg _
    have hq0 : (0 : ℝ) < ((n : ℝ) + k + 1) ^ (k + 1) := by positivity
    rw [div_le_div_iff₀ hq0 hP0]
    exact mul_le_mul_of_nonneg_left hPu hfac0
  · rw [← hconstU]
    refine intervalIntegral.integral_mono_on (by norm_num) hint
      (by apply intervalIntegrable_const) ?_
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

/-- The floor constants of the class invariant. -/
noncomputable def classA : ℕ → ℝ
  | 0 => 4
  | (j + 1) => 8 ^ 2 ^ j * (1 + classA j)

/-- The main-term constants of the class invariant. -/
noncomputable def classB : ℕ → ℝ
  | 0 => 12
  | (j + 1) => 8 ^ 2 ^ j * classB j

theorem classA_pos (j : ℕ) : 0 < classA j := by
  induction j with
  | zero => rw [classA]; norm_num
  | succ j ih =>
    rw [classA]
    have h1 : (0:ℝ) < 8 ^ 2 ^ j := by positivity
    nlinarith

theorem classB_pos (j : ℕ) : 0 < classB j := by
  induction j with
  | zero => rw [classB]; norm_num
  | succ j ih =>
    rw [classB]
    have h1 : (0:ℝ) < 8 ^ 2 ^ j := by positivity
    nlinarith

set_option maxHeartbeats 1600000 in
/-- **The general class lemma**: the savings invariant of the honest
cascade, by induction — the shape confirmed by classes zero, one, two. -/
theorem cascadeBound'_class (j : ℕ) :
    ∀ {L : ℝ} {H : ℕ} {μ ν : ℝ},
      0 < μ → μ ≤ ν → 1 ≤ H → (H:ℝ) ≤ L →
      (H:ℝ) ^ j * ν ≤ 1 → 1 ≤ ν * L →
      cascadeBound' j L H μ ν
        ≤ (classA j / H + classB j * (Real.sqrt H) ^ j
            * (ν / Real.sqrt μ)) * L ^ 2 ^ j := by
  induction j with
  | zero =>
    intro L H μ ν hμ hμν hH hHL hHν hνL
    rw [pow_zero, one_mul] at hHν
    have hHR : (0:ℝ) < (H:ℝ) := by exact_mod_cast hH
    have hL0 : (0:ℝ) < L := lt_of_lt_of_le hHR hHL
    have h1 := cascadeBound'_class_zero (L := L) (H := H)
      hμ hμν hHν hνL
    refine le_trans h1 ?_
    rw [classA, classB, pow_zero, mul_one, pow_zero, pow_one]
    have h2 : (0:ℝ) ≤ 4 / H * L := by positivity
    nlinarith [h2]
  | succ j ih =>
    intro L H μ ν hμ hμν hH hHL hHν hνL
    have hHR : (0:ℝ) < (H:ℝ) := by exact_mod_cast hH
    have hH1 : (1:ℝ) ≤ (H:ℝ) := by exact_mod_cast hH
    have hν0 : (0:ℝ) < ν := lt_of_lt_of_le hμ hμν
    have hL0 : (0:ℝ) < L := lt_of_lt_of_le hHR hHL
    have hsμ : (0:ℝ) < Real.sqrt μ := Real.sqrt_pos.mpr hμ
    have hsH : (0:ℝ) < Real.sqrt H := Real.sqrt_pos.mpr hHR
    have hA := classA_pos j
    have hB := classB_pos j
    have hHj0 : (0:ℝ) ≤ (H:ℝ) ^ j := by positivity
    rw [cascadeBound']
    refine le_trans (min_le_right _ _) ?_
    -- the per-g bound
    set PB : ℝ := (classA j / H + classB j * (Real.sqrt H) ^ (j + 1)
      * (ν / Real.sqrt μ)) * L ^ 2 ^ j with hPBdef
    have hPB0 : (0:ℝ) ≤ PB := by
      rw [hPBdef]
      positivity
    have hper : ∀ g ∈ Finset.Ico 1 H,
        cascadeBound' j L H ((g:ℝ) * μ) ((g:ℝ) * ν) ≤ PB := by
      intro g hg
      rw [Finset.mem_Ico] at hg
      have hg0 : (0:ℝ) < (g:ℝ) := by exact_mod_cast hg.1
      have hga : (1:ℝ) ≤ (g:ℝ) := by exact_mod_cast hg.1
      have hgH : (g:ℝ) ≤ (H:ℝ) := by exact_mod_cast hg.2.le
      have hgHν : (H:ℝ) ^ j * ((g:ℝ) * ν) ≤ 1 := by
        have h0 : (H:ℝ) ^ j * ((g:ℝ) * ν)
            ≤ (H:ℝ) ^ j * ((H:ℝ) * ν) := by
          have h1 := mul_le_mul_of_nonneg_right hgH hν0.le
          nlinarith
        have h2 : (H:ℝ) ^ j * ((H:ℝ) * ν) = (H:ℝ) ^ (j + 1) * ν := by
          rw [pow_succ]
          ring
        nlinarith [hHν, h2 ▸ h0]
      have hgνL : 1 ≤ (g:ℝ) * ν * L := by
        have h0 : (0:ℝ) ≤ ν * L := by positivity
        have h1 := mul_le_mul_of_nonneg_right hga h0
        nlinarith
      have h1 := ih (L := L) (H := H) (μ := (g:ℝ) * μ) (ν := (g:ℝ) * ν)
        (mul_pos hg0 hμ) (mul_le_mul_of_nonneg_left hμν hg0.le)
        hH hHL hgHν hgνL
      refine le_trans h1 ?_
      -- √-split and fold
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
      rw [h3, hPBdef]
      have h5 : Real.sqrt g ≤ Real.sqrt H := Real.sqrt_le_sqrt hgH
      have h6 : (Real.sqrt H) ^ j * (Real.sqrt g * (ν / Real.sqrt μ))
          ≤ (Real.sqrt H) ^ (j + 1) * (ν / Real.sqrt μ) := by
        have h7 : (0:ℝ) ≤ ν / Real.sqrt μ := by positivity
        have h8 : (0:ℝ) ≤ (Real.sqrt H) ^ j := by positivity
        have h9 : (Real.sqrt H) ^ j * Real.sqrt g
            ≤ (Real.sqrt H) ^ (j + 1) := by
          rw [pow_succ]
          exact mul_le_mul_of_nonneg_left h5 h8
        nlinarith [mul_le_mul_of_nonneg_right h9 h7]
      have h10 : (0:ℝ) ≤ L ^ 2 ^ j := by positivity
      refine mul_le_mul_of_nonneg_right ?_ h10
      nlinarith [h6]
    -- sum
    have hsum : ∑ g ∈ Finset.Ico 1 H,
        cascadeBound' j L H ((g:ℝ) * μ) ((g:ℝ) * ν) ≤ (H:ℝ) * PB := by
      refine le_trans (Finset.sum_le_sum hper) ?_
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
      have h8 : ((H - 1 : ℕ) : ℝ) ≤ (H : ℝ) := by
        exact_mod_cast (by omega : H - 1 ≤ H)
      exact mul_le_mul_of_nonneg_right h8 hPB0
    have hsum0 : (0:ℝ) ≤ ∑ g ∈ Finset.Ico 1 H,
        cascadeBound' j L H ((g:ℝ) * μ) ((g:ℝ) * ν) := by
      refine Finset.sum_nonneg fun g hg => ?_
      rw [Finset.mem_Ico] at hg
      have hg0 : (0:ℝ) < (g:ℝ) := by exact_mod_cast hg.1
      exact cascadeBound'_nonneg j hL0.le hH
        (mul_pos hg0 hμ) (mul_nonneg hg0.le hν0.le)
    -- H-power algebra
    have hHpow : (H:ℝ) ^ (2 ^ j - 1) * (H:ℝ) = (H:ℝ) ^ 2 ^ j := by
      rw [← pow_succ]
      congr 1
      have := Nat.one_le_two_pow (n := j)
      omega
    -- inner fold
    have hinner : 2 ^ 2 ^ j * L ^ 2 ^ j
          + 4 ^ 2 ^ j * (H:ℝ) ^ (2 ^ j - 1)
            * ∑ g ∈ Finset.Ico 1 H,
                cascadeBound' j L H ((g:ℝ) * μ) ((g:ℝ) * ν)
        ≤ 2 ^ 2 ^ j * L ^ 2 ^ j
          + 4 ^ 2 ^ j * (H:ℝ) ^ 2 ^ j * PB := by
      have h11 : (0:ℝ) ≤ (4:ℝ) ^ 2 ^ j * (H:ℝ) ^ (2 ^ j - 1) := by
        positivity
      have h12 := mul_le_mul_of_nonneg_left hsum h11
      have h13 : (4:ℝ) ^ 2 ^ j * (H:ℝ) ^ (2 ^ j - 1) * ((H:ℝ) * PB)
          = 4 ^ 2 ^ j * (H:ℝ) ^ 2 ^ j * PB := by
        rw [← hHpow]
        ring
      nlinarith [h12, h13.ge, h13.le]
    have hinner0 : (0:ℝ) ≤ 2 ^ 2 ^ j * L ^ 2 ^ j
          + 4 ^ 2 ^ j * (H:ℝ) ^ (2 ^ j - 1)
            * ∑ g ∈ Finset.Ico 1 H,
                cascadeBound' j L H ((g:ℝ) * μ) ((g:ℝ) * ν) := by
      have h14 : (0:ℝ) ≤ (4:ℝ) ^ 2 ^ j * (H:ℝ) ^ (2 ^ j - 1) := by
        positivity
      have h15 : (0:ℝ) ≤ (2:ℝ) ^ 2 ^ j * L ^ 2 ^ j := by positivity
      nlinarith [mul_nonneg h14 hsum0]
    -- prefactor
    have hLH2 : (L + (H:ℝ)) / H ≤ 2 * L / H := by
      refine div_le_div_of_nonneg_right ?_ hHR.le
      linarith
    have hLH0 : (0:ℝ) ≤ (L + (H:ℝ)) / H :=
      div_nonneg (by linarith) hHR.le
    have hpre : ((L + (H:ℝ)) / H) ^ 2 ^ j ≤ (2 * L / H) ^ 2 ^ j :=
      pow_le_pow_left₀ hLH0 hLH2 _
    -- multiply out (small pieces, single denominators)
    have hq := Nat.one_le_two_pow (n := j)
    have hE0 : (0:ℝ) < (H:ℝ) ^ 2 ^ j := by positivity
    have hEne : ((H:ℝ)) ^ 2 ^ j ≠ 0 := ne_of_gt hE0
    have e1 : (2 * L / (H:ℝ)) ^ 2 ^ j
        = 2 ^ 2 ^ j * L ^ 2 ^ j / (H:ℝ) ^ 2 ^ j := by
      rw [div_pow, mul_pow]
    have hDD : L ^ 2 ^ j * L ^ 2 ^ j = L ^ 2 ^ (j + 1) := by
      rw [← pow_add]
      congr 1
      omega
    have e2 : 2 ^ 2 ^ j * L ^ 2 ^ j / (H:ℝ) ^ 2 ^ j
          * (2 ^ 2 ^ j * L ^ 2 ^ j)
        = 4 ^ 2 ^ j * L ^ 2 ^ (j + 1) / (H:ℝ) ^ 2 ^ j := by
      rw [← hDD, show (4:ℝ) ^ 2 ^ j = 2 ^ 2 ^ j * 2 ^ 2 ^ j by
        rw [← mul_pow]; norm_num]
      field_simp
    have e3 : 2 ^ 2 ^ j * L ^ 2 ^ j / (H:ℝ) ^ 2 ^ j
          * (4 ^ 2 ^ j * (H:ℝ) ^ 2 ^ j * PB)
        = 8 ^ 2 ^ j * L ^ 2 ^ j * PB := by
      rw [show (8:ℝ) ^ 2 ^ j = 2 ^ 2 ^ j * 4 ^ 2 ^ j by
        rw [← mul_pow]; norm_num]
      field_simp
    have h16 : (4:ℝ) ^ 2 ^ j * L ^ 2 ^ (j + 1) / (H:ℝ) ^ 2 ^ j
        ≤ 8 ^ 2 ^ j * L ^ 2 ^ (j + 1) / H := by
      have h17 : (H:ℝ) ≤ (H:ℝ) ^ 2 ^ j := by
        calc (H:ℝ) = (H:ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (H:ℝ) ^ 2 ^ j := pow_le_pow_right₀ hH1 hq
      have h18 : (4:ℝ) ^ 2 ^ j ≤ 8 ^ 2 ^ j :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) _
      have h20 : (0:ℝ) ≤ L ^ 2 ^ (j + 1) := by positivity
      rw [div_le_div_iff₀ hE0 hHR]
      have h19 := mul_le_mul h18 h17 hHR.le
        (pow_nonneg (by norm_num : (0:ℝ) ≤ 8) _)
      nlinarith [mul_le_mul_of_nonneg_left h19 h20]
    have e4 : 8 ^ 2 ^ j * L ^ 2 ^ j * PB
        = (8 ^ 2 ^ j * classA j / H
          + 8 ^ 2 ^ j * classB j * (Real.sqrt H) ^ (j + 1)
            * (ν / Real.sqrt μ)) * L ^ 2 ^ (j + 1) := by
      rw [hPBdef, ← hDD]
      field_simp
    calc ((L + (H:ℝ)) / H) ^ 2 ^ j * (2 ^ 2 ^ j * L ^ 2 ^ j
          + 4 ^ 2 ^ j * (H:ℝ) ^ (2 ^ j - 1)
            * ∑ g ∈ Finset.Ico 1 H,
                cascadeBound' j L H ((g:ℝ) * μ) ((g:ℝ) * ν))
        ≤ (2 * L / H) ^ 2 ^ j * (2 ^ 2 ^ j * L ^ 2 ^ j
            + 4 ^ 2 ^ j * (H:ℝ) ^ 2 ^ j * PB) := by
          refine mul_le_mul hpre hinner hinner0 (pow_nonneg ?_ _)
          positivity
      _ = 4 ^ 2 ^ j * L ^ 2 ^ (j + 1) / (H:ℝ) ^ 2 ^ j
            + (8 ^ 2 ^ j * classA j / H
              + 8 ^ 2 ^ j * classB j * (Real.sqrt H) ^ (j + 1)
                * (ν / Real.sqrt μ)) * L ^ 2 ^ (j + 1) := by
          rw [e1, mul_add, e2, e3, e4]
      _ ≤ (8 ^ 2 ^ j * L ^ 2 ^ (j + 1) / H)
            + (8 ^ 2 ^ j * classA j / H
              + 8 ^ 2 ^ j * classB j * (Real.sqrt H) ^ (j + 1)
                * (ν / Real.sqrt μ)) * L ^ 2 ^ (j + 1) := by
          linarith [h16]
      _ = (classA (j + 1) / H + classB (j + 1)
            * (Real.sqrt H) ^ (j + 1) * (ν / Real.sqrt μ))
            * L ^ 2 ^ (j + 1) := by
          rw [classA, classB]
          field_simp
          ring

/-- The primed log-phase block bound: the honest cascade on the zeta
phase. -/
theorem log_phase_block_bound' (j M N H W : ℕ) (t : ℝ)
    (ht : 0 < t) (hH : 1 ≤ H) (hHM : H ≤ M) (hMN : M ≤ N)
    (hwin : N + j * H + j + 2 ≤ W) :
    ‖∑ n ∈ Finset.Ico M (N + 1),
        e (-(t / (2 * Real.pi) * Real.log n))‖ ^ (2 ^ j)
      ≤ cascadeBound' j ((N + 1 - M : ℕ) : ℝ) H
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
    exact vdck_pow' j (fun m : ℕ => -(t / (2 * Real.pi) * Real.log m))
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
    exact vdck_pow' j (fun m : ℕ => t / (2 * Real.pi) * Real.log m)
      M N H μ ν hμ0 hμν hH hHM hMN hsand


set_option maxHeartbeats 800000 in
/-- **The per-block head estimate**: under the class conditions, a
weighted zeta block costs `2·(saving)^{1/2^j}` — the `M` cancels against
the Abel factor. -/
theorem zeta_block_class_bound (j M N H W : ℕ) (t : ℝ) (w : ℕ → ℝ)
    (ht : 0 < t) (hH : 1 ≤ H) (hHM : H ≤ M) (hMN : M ≤ N)
    (hN2 : N + 1 ≤ 2 * M)
    (hwin : N + j * H + j + 2 ≤ W)
    (hcond1 : (H:ℝ) ^ j * (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
      / ((M : ℕ) : ℝ) ^ (j + 2)) ≤ 1)
    (hcond2 : 1 ≤ (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
      / ((M : ℕ) : ℝ) ^ (j + 2)) * (2 * (M:ℝ)))
    (hw0 : ∀ n, M ≤ n → n ≤ N → 0 ≤ w n)
    (hwd : ∀ n, M ≤ n → n < N → w (n + 1) ≤ w n)
    (hwM : w M ≤ 1 / M) :
    ‖∑ n ∈ Finset.Ico M (N + 1),
        w n • e (-(t / (2 * Real.pi) * Real.log n))‖
      ≤ 2 * (classA j / H + classB j * (Real.sqrt H) ^ j
          * ((t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
              / ((M : ℕ) : ℝ) ^ (j + 2))
            / Real.sqrt (t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
              / ((W : ℕ) : ℝ) ^ (j + 2))))
          ^ (((2 ^ j : ℕ) : ℝ)⁻¹) := by
  have hM1 : 1 ≤ M := le_trans hH hHM
  have hMR : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM1
  have hW1 : 1 ≤ W := by omega
  have hWR : (0:ℝ) < ((W:ℕ):ℝ) := by exact_mod_cast hW1
  have hMW : M ≤ W := by omega
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hf : (0:ℝ) < ((j + 1).factorial : ℝ) := by
    exact_mod_cast (j + 1).factorial_pos
  set ν := t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
    / ((M : ℕ) : ℝ) ^ (j + 2) with hνdef
  set μ := t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
    / ((W : ℕ) : ℝ) ^ (j + 2) with hμdef
  have hμ0 : (0:ℝ) < μ := by rw [hμdef]; positivity
  have hν0 : (0:ℝ) < ν := by rw [hνdef]; positivity
  have hμν : μ ≤ ν := by
    rw [hμdef, hνdef]
    have hle : ((M:ℕ):ℝ) ^ (j + 2) ≤ ((W:ℕ):ℝ) ^ (j + 2) := by
      refine pow_le_pow_left₀ hMR.le ?_ _
      exact_mod_cast hMW
    have hnum : (0:ℝ) ≤ t / (2 * Real.pi) * ((j + 1).factorial : ℝ) := by
      positivity
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul_of_nonneg_left hle hnum
  set pb := classA j / H + classB j * (Real.sqrt H) ^ j * (ν / Real.sqrt μ)
    with hpbdef
  have hpb0 : (0:ℝ) ≤ pb := by
    rw [hpbdef]
    have hA := classA_pos j
    have hB := classB_pos j
    have hHR : (0:ℝ) < (H:ℝ) := by exact_mod_cast hH
    positivity
  have hq : (2:ℕ) ^ j ≠ 0 := (Nat.two_pow_pos j).ne'
  have hE0 : (0:ℝ) ≤ pb ^ (((2 ^ j : ℕ) : ℝ)⁻¹) := Real.rpow_nonneg hpb0 _
  -- uniform partial bound
  have hE : ∀ P, M ≤ P → P ≤ N + 1 →
      ‖∑ n ∈ Finset.Ico M P, e (-(t / (2 * Real.pi) * Real.log n))‖
        ≤ pb ^ (((2 ^ j : ℕ) : ℝ)⁻¹) * (2 * (M:ℝ)) := by
    intro P hP1 hP2
    rcases Nat.eq_or_lt_of_le hP1 with hPM | hPM
    · rw [← hPM, Finset.Ico_self, Finset.sum_empty, norm_zero]
      positivity
    · obtain ⟨P', rfl⟩ : ∃ P', P = P' + 1 := ⟨P - 1, by omega⟩
      have hMP' : M ≤ P' := by omega
      have h1 := log_phase_block_bound' j M P' H W t ht hH hHM hMP'
        (by omega)
      rw [← hνdef, ← hμdef] at h1
      have h2 := cascadeBound'_mono_L j (L := ((P' + 1 - M : ℕ) : ℝ))
        (L' := 2 * (M:ℝ)) (H := H) (Nat.cast_nonneg _)
        (by
          have h3 : P' + 1 - M ≤ 2 * M := by omega
          have h4 : ((P' + 1 - M : ℕ) : ℝ) ≤ ((2 * M : ℕ) : ℝ) := by
            exact_mod_cast h3
          push_cast at h4
          linarith)
        hH hμ0 hν0.le
      have h5 := cascadeBound'_class j (L := 2 * (M:ℝ)) (H := H)
        (μ := μ) (ν := ν) hμ0 hμν hH
        (by
          have h6 : (H:ℝ) ≤ (M:ℝ) := by exact_mod_cast hHM
          linarith)
        hcond1 hcond2
      have h7 := le_trans h1 (le_trans h2 h5)
      have h8 := le_rpow_inv_of_pow_le (q := 2 ^ j) hq
        (norm_nonneg _) h7
      refine le_trans h8 (le_of_eq ?_)
      rw [Real.mul_rpow hpb0 (by positivity),
        Real.pow_rpow_inv_natCast (by positivity) hq]
  -- Abel with the abstract weight
  have habel := abel_weight_bound (w := w)
    (a := fun n => e (-(t / (2 * Real.pi) * Real.log n)))
    (M := M) (N := N)
    (E := pb ^ (((2 ^ j : ℕ) : ℝ)⁻¹) * (2 * (M:ℝ)))
    hMN hw0 hwd hE
  refine le_trans habel ?_
  have h9 : w M * (pb ^ (((2 ^ j : ℕ) : ℝ)⁻¹) * (2 * (M:ℝ)))
      ≤ (1 / M) * (pb ^ (((2 ^ j : ℕ) : ℝ)⁻¹) * (2 * (M:ℝ))) := by
    refine mul_le_mul_of_nonneg_right hwM ?_
    positivity
  refine le_trans h9 (le_of_eq ?_)
  rw [hpbdef]
  field_simp

/-- The floor constants are dyadically bounded. -/
theorem classA_le (j : ℕ) : classA j ≤ 2 ^ (4 * 2 ^ j) := by
  induction j with
  | zero =>
    rw [classA]
    norm_num
  | succ j ih =>
    rw [classA]
    have h1 : (8:ℝ) ^ 2 ^ j = 2 ^ (3 * 2 ^ j) := by
      rw [show (8:ℝ) = 2 ^ 3 by norm_num, ← pow_mul]
    have h2 : (1:ℝ) + classA j ≤ 2 ^ (4 * 2 ^ j + 1) := by
      have h3 : (1:ℝ) ≤ 2 ^ (4 * 2 ^ j) := one_le_pow₀ (by norm_num)
      have h4 : (2:ℝ) ^ (4 * 2 ^ j + 1) = 2 * 2 ^ (4 * 2 ^ j) := by
        rw [pow_succ]
        ring
      nlinarith [ih]
    calc (8:ℝ) ^ 2 ^ j * (1 + classA j)
        ≤ 2 ^ (3 * 2 ^ j) * 2 ^ (4 * 2 ^ j + 1) := by
          rw [← h1]
          refine mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 ^ (3 * 2 ^ j + (4 * 2 ^ j + 1)) := by rw [← pow_add]
      _ ≤ 2 ^ (4 * 2 ^ (j + 1)) := by
          refine pow_le_pow_right₀ (by norm_num) ?_
          have h5 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
          omega

/-- The main-term constants are dyadically bounded. -/
theorem classB_le (j : ℕ) : classB j ≤ 2 ^ (4 * 2 ^ j) := by
  induction j with
  | zero =>
    rw [classB]
    norm_num
  | succ j ih =>
    rw [classB]
    have h1 : (8:ℝ) ^ 2 ^ j = 2 ^ (3 * 2 ^ j) := by
      rw [show (8:ℝ) = 2 ^ 3 by norm_num, ← pow_mul]
    calc (8:ℝ) ^ 2 ^ j * classB j
        ≤ 2 ^ (3 * 2 ^ j) * 2 ^ (4 * 2 ^ j) := by
          rw [← h1]
          refine mul_le_mul_of_nonneg_left ih (by positivity)
      _ = 2 ^ (3 * 2 ^ j + 4 * 2 ^ j) := by rw [← pow_add]
      _ ≤ 2 ^ (4 * 2 ^ (j + 1)) := by
          refine pow_le_pow_right₀ (by norm_num) ?_
          have h5 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
          omega

/-- Factorials are dyadically bounded: `(j+1)! ≤ 2^{(j+1)²}`. -/
theorem factorial_le_two_pow_sq (j : ℕ) :
    ((j + 1).factorial : ℝ) ≤ 2 ^ ((j + 1) ^ 2) := by
  induction j with
  | zero => simp [Nat.factorial]
  | succ j ih =>
    have h1 : ((j + 2).factorial : ℝ)
        = ((j + 2 : ℕ) : ℝ) * ((j + 1).factorial : ℝ) := by
      rw [show j + 2 = (j + 1) + 1 from rfl, Nat.factorial_succ]
      push_cast
      ring
    rw [show j + 1 + 1 = j + 2 from rfl, h1]
    have h2 : ((j + 2 : ℕ) : ℝ) ≤ 2 ^ (j + 2) := by
      have h3 : j + 2 ≤ 2 ^ (j + 2) := Nat.lt_two_pow_self.le
      exact_mod_cast h3
    calc ((j + 2 : ℕ) : ℝ) * ((j + 1).factorial : ℝ)
        ≤ 2 ^ (j + 2) * 2 ^ ((j + 1) ^ 2) := by
          refine mul_le_mul h2 ih (by positivity) (by positivity)
      _ = 2 ^ ((j + 2) + (j + 1) ^ 2) := by rw [← pow_add]
      _ ≤ 2 ^ ((j + 2) ^ 2) := by
          refine pow_le_pow_right₀ (by norm_num) ?_
          nlinarith
/-- The trivial weighted block: total mass at most one. -/
theorem zeta_block_trivial (M N : ℕ) (w : ℕ → ℝ) (a : ℕ → ℂ)
    (hM : 1 ≤ M) (hN2 : N + 1 ≤ 2 * M)
    (ha : ∀ n, ‖a n‖ ≤ 1)
    (hw0 : ∀ n, M ≤ n → n ≤ N → 0 ≤ w n)
    (hwd : ∀ n, M ≤ n → n < N → w (n + 1) ≤ w n)
    (hwM : w M ≤ 1 / M) :
    ‖∑ n ∈ Finset.Ico M (N + 1), w n • a n‖ ≤ 1 := by
  rcases Nat.lt_or_ge N M with hNM | hNM
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, norm_zero]
    norm_num
  · have hMR : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
    have hE : ∀ P, M ≤ P → P ≤ N + 1 →
        ‖∑ n ∈ Finset.Ico M P, a n‖ ≤ (M:ℝ) := by
      intro P h1 h2
      refine le_trans (norm_sum_le _ _) ?_
      refine le_trans (Finset.sum_le_sum fun n _ => ha n) ?_
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Ico]
      exact_mod_cast (by omega : P - M ≤ M)
    have h := abel_weight_bound (w := w) (a := a) (M := M) (N := N)
      (E := (M:ℝ)) hNM hw0 hwd hE
    refine le_trans h ?_
    calc w M * (M:ℝ)
        ≤ 1 / M * (M:ℝ) := mul_le_mul_of_nonneg_right hwM hMR.le
      _ = 1 := by field_simp

set_option maxHeartbeats 1600000 in
/-- **The block dispatch**: with valid schedule data `(j, h', u, m)`, a
weighted zeta block over `[2^i, N]` saves the integer factor `(1/2)^m`. -/
theorem zeta_block_saving (i j h' u m d N : ℕ) (t : ℝ) (w : ℕ → ℝ)
    (ht1 : (2:ℝ) ^ d ≤ t) (ht2 : t ≤ 2 ^ (d + 1))
    (hij : i * (j + 1) + 2 ≤ d)
    (hu : 2 * u + d + 1 + (j + 1) ^ 2 ≤ i * (j + 2))
    (hh' : h' * (j + 2) + j + 2 ≤ u)
    (hm : m * 2 ^ j + 4 * 2 ^ j + 1 ≤ 2 * h')
    (hwin : j * 4 ^ h' + j + 2 ≤ 2 ^ (i + 1))
    (hMN : 2 ^ i ≤ N) (hN2 : N + 1 ≤ 2 * 2 ^ i)
    (hw0 : ∀ n, 2 ^ i ≤ n → n ≤ N → 0 ≤ w n)
    (hwd : ∀ n, 2 ^ i ≤ n → n < N → w (n + 1) ≤ w n)
    (hwM : w (2 ^ i) ≤ 1 / ((2 ^ i : ℕ) : ℝ)) :
    ‖∑ n ∈ Finset.Ico (2 ^ i) (N + 1),
        w n • e (-(t / (2 * Real.pi) * Real.log n))‖
      ≤ 2 * (1 / 2 : ℝ) ^ m := by
  have ht0 : (0:ℝ) < t := lt_of_lt_of_le (by positivity) ht1
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hπ4 : Real.pi ≤ 4 := by nlinarith [Real.pi_le_four]
  have hf1 : (1:ℝ) ≤ ((j + 1).factorial : ℝ) := by
    exact_mod_cast (j + 1).factorial_pos
  -- derived schedule facts
  have h2h'i : 2 * h' < i := by
    by_contra hc
    push_neg at hc
    have h1 : i * (j + 2) ≤ 2 * h' * (j + 2) :=
      Nat.mul_le_mul_right _ hc
    have hb : 2 * h' * (j + 2) = 2 * (h' * (j + 2)) := by ring
    omega
  have hi1 : 1 ≤ i := by omega
  -- exponent inequalities
  have hexp1 : 2 * h' * j + d + 1 + (j + 1) ^ 2 ≤ i * (j + 2) := by
    have h1 : h' * j + h' * 2 = h' * (j + 2) := by ring
    have hb : 2 * h' * j = 2 * (h' * j) := by ring
    omega
  -- the ν bounds
  have hν2M : (2:ℝ) * Real.pi * 2 ^ (i * (j + 2))
      ≤ t * ((j + 1).factorial : ℝ) * (2 * 2 ^ i) := by
    have h1 : (2:ℝ) * Real.pi * 2 ^ (i * (j + 2))
        ≤ 8 * 2 ^ (i * (j + 2)) := by
      nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) (i * (j + 2))]
    have h2 : (8:ℝ) * 2 ^ (i * (j + 2)) = 2 ^ (i * (j + 2) + 3) := by
      rw [pow_add]
      ring
    have h3 : i * (j + 2) + 3 ≤ d + i + 1 := by
      have h4 : i * (j + 2) = i * (j + 1) + i := by ring
      omega
    have h5 : (2:ℝ) ^ (i * (j + 2) + 3) ≤ 2 ^ (d + i + 1) :=
      pow_le_pow_right₀ (by norm_num) h3
    have h6 : (2:ℝ) ^ (d + i + 1) = 2 ^ d * (2 * 2 ^ i) := by
      rw [pow_add, pow_add]
      ring
    have h7 : (2:ℝ) ^ d * (2 * 2 ^ i)
        ≤ t * ((j + 1).factorial : ℝ) * (2 * 2 ^ i) := by
      have h8 : (2:ℝ) ^ d ≤ t * ((j + 1).factorial : ℝ) := by
        nlinarith
      nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) i]
    linarith [h1, h2.le, h2.ge, h5, h6.le, h6.ge, h7]
  -- instantiate the class machinery at M := 2^i, W := 2^(i+2), H := 4^h'
  have hMcast : (((2 ^ i : ℕ) : ℝ)) = 2 ^ i := by push_cast; ring
  have hWcast : (((2 ^ (i + 2) : ℕ) : ℝ)) = 2 ^ (i + 2) := by
    push_cast; ring
  have hHcast : (((4 ^ h' : ℕ) : ℝ)) = 2 ^ (2 * h') := by
    push_cast
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  set ν := t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
    / (((2 ^ i : ℕ) : ℝ)) ^ (j + 2) with hνdef
  set μ := t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
    / (((2 ^ (i + 2) : ℕ) : ℝ)) ^ (j + 2) with hμdef
  have hν0 : (0:ℝ) < ν := by rw [hνdef]; positivity
  have hμ0 : (0:ℝ) < μ := by rw [hμdef]; positivity
  have hpowM : (((2 ^ i : ℕ) : ℝ)) ^ (j + 2) = 2 ^ (i * (j + 2)) := by
    rw [hMcast, ← pow_mul]
  -- hcond2
  have hcond2 : 1 ≤ ν * (2 * (((2 ^ i : ℕ) : ℝ))) := by
    rw [hνdef, hpowM, hMcast]
    have h20 : t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
          / 2 ^ (i * (j + 2)) * (2 * 2 ^ i)
        = t * ((j + 1).factorial : ℝ) * (2 * 2 ^ i)
          / (2 * Real.pi * 2 ^ (i * (j + 2))) := by
      field_simp
    rw [h20, le_div_iff₀ (by positivity)]
    linarith [hν2M]
  -- hcond1
  have hνle : ν * (2:ℝ) ^ (i * (j + 2))
      ≤ 2 ^ (d + 1) * 2 ^ ((j + 1) ^ 2) := by
    rw [hνdef, hpowM]
    have h21 : t / (2 * Real.pi) * ((j + 1).factorial : ℝ)
          / 2 ^ (i * (j + 2)) * 2 ^ (i * (j + 2))
        = t / (2 * Real.pi) * ((j + 1).factorial : ℝ) := by
      field_simp
    rw [h21]
    have h22 : t / (2 * Real.pi) ≤ 2 ^ (d + 1) := by
      have h23 : (1:ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      calc t / (2 * Real.pi) ≤ t / 1 := by
            refine div_le_div_of_nonneg_left ht0.le (by norm_num) h23
        _ = t := by ring
        _ ≤ 2 ^ (d + 1) := ht2
    have h24 := factorial_le_two_pow_sq j
    have h25 : (0:ℝ) ≤ t / (2 * Real.pi) := by positivity
    nlinarith [mul_le_mul h22 h24 (by linarith) (by positivity :
      (0:ℝ) ≤ (2:ℝ) ^ (d + 1))]
  have hcond1 : (((4 ^ h' : ℕ) : ℝ)) ^ j * ν ≤ 1 := by
    rw [hHcast, ← pow_mul]
    have h26 : (2:ℝ) ^ (2 * h' * j) * ν * 2 ^ (i * (j + 2))
        ≤ 2 ^ (2 * h' * j) * (2 ^ (d + 1) * 2 ^ ((j + 1) ^ 2)) := by
      have h27 := mul_le_mul_of_nonneg_left hνle
        (by positivity : (0:ℝ) ≤ (2:ℝ) ^ (2 * h' * j))
      nlinarith [h27]
    have h28 : (2:ℝ) ^ (2 * h' * j) * (2 ^ (d + 1) * 2 ^ ((j + 1) ^ 2))
        = 2 ^ (2 * h' * j + (d + 1) + (j + 1) ^ 2) := by
      rw [pow_add, pow_add]
      ring
    have h29 : (2:ℝ) ^ (2 * h' * j + (d + 1) + (j + 1) ^ 2)
        ≤ 2 ^ (i * (j + 2)) := by
      refine pow_le_pow_right₀ (by norm_num) ?_
      omega
    have h30 : (0:ℝ) < (2:ℝ) ^ (i * (j + 2)) := by positivity
    nlinarith [h26, h28.le, h28.ge, h29]
  -- apply the class block bound
  have hH1 : 1 ≤ 4 ^ h' := Nat.one_le_pow _ _ (by norm_num)
  have hHM : 4 ^ h' ≤ 2 ^ i := by
    have h31 : 4 ^ h' = 2 ^ (2 * h') := by
      rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    rw [h31]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hwin' : N + j * 4 ^ h' + j + 2 ≤ 2 ^ (i + 2) := by
    have h32 : 2 ^ (i + 2) = 2 ^ (i + 1) + 2 ^ (i + 1) := by ring
    omega
  have hblock := zeta_block_class_bound j (2 ^ i) N (4 ^ h')
    (2 ^ (i + 2)) t w ht0 hH1 hHM hMN hN2 hwin' hcond1 hcond2
    hw0 hwd hwM
  rw [← hνdef, ← hμdef] at hblock
  refine le_trans hblock ?_
  -- evaluate the saving: pb ≤ ((1/2)^m)^(2^j)
  have hq : (2:ℕ) ^ j ≠ 0 := (Nat.two_pow_pos j).ne'
  have hsqH : Real.sqrt (((4 ^ h' : ℕ) : ℝ)) = 2 ^ h' := by
    rw [hHcast, show (2:ℝ) ^ (2 * h') = (2 ^ h') ^ 2 by
      rw [← pow_mul]; ring_nf]
    exact Real.sqrt_sq (by positivity)
  -- μ = ν/4^(j+2), so ν/√μ = 2^(j+2)·√ν
  have hμν4 : μ = ν / 4 ^ (j + 2) := by
    rw [hμdef, hνdef, hWcast, hMcast]
    have h33 : ((2:ℝ) ^ (i + 2)) ^ (j + 2)
        = 4 ^ (j + 2) * (2 ^ i) ^ (j + 2) := by
      rw [show (2:ℝ) ^ (i + 2) = 2 ^ i * 4 by rw [pow_add]; norm_num,
        mul_pow]
      ring
    rw [h33]
    field_simp
  have hdivsqrt : ν / Real.sqrt μ = 2 ^ (j + 2) * Real.sqrt ν := by
    rw [hμν4,
      show (4:ℝ) ^ (j + 2) = (2 ^ (j + 2)) ^ 2 by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul,
          Nat.mul_comm 2 (j + 2)],
      Real.sqrt_div hν0.le, Real.sqrt_sq (by positivity),
      div_div_eq_mul_div, mul_comm ν ((2:ℝ) ^ (j + 2)),
      mul_div_assoc, Real.div_sqrt]
  -- √ν ≤ (1/2)^u
  have hν2u : ν * (2:ℝ) ^ (2 * u) ≤ 1 := by
    have h40 : (2:ℝ) ^ (2 * u) * (2 ^ (d + 1) * 2 ^ ((j + 1) ^ 2))
        ≤ 2 ^ (i * (j + 2)) := by
      rw [← pow_add, ← pow_add]
      refine pow_le_pow_right₀ (by norm_num) ?_
      omega
    have h41 := mul_le_mul_of_nonneg_left hνle
      (by positivity : (0:ℝ) ≤ (2:ℝ) ^ (2 * u))
    have h42 : (0:ℝ) < (2:ℝ) ^ (i * (j + 2)) := by positivity
    nlinarith [h41, h40]
  have hsqν : Real.sqrt ν ≤ (1 / 2 : ℝ) ^ u := by
    have h44 : ((1 / 2 : ℝ) ^ u) ^ 2 * 2 ^ (2 * u) = 1 := by
      rw [← pow_mul, div_pow, one_pow]
      field_simp
      congr 1
      omega
    have h43 : ν ≤ ((1 / 2 : ℝ) ^ u) ^ 2 := by
      have h45 : (0:ℝ) < (2:ℝ) ^ (2 * u) := by positivity
      nlinarith [hν2u]
    calc Real.sqrt ν ≤ Real.sqrt (((1 / 2 : ℝ) ^ u) ^ 2) :=
        Real.sqrt_le_sqrt h43
      _ = (1 / 2 : ℝ) ^ u := Real.sqrt_sq (by positivity)
  -- the pb evaluation
  have hpb : classA j / (((4 ^ h' : ℕ) : ℝ))
        + classB j * (Real.sqrt (((4 ^ h' : ℕ) : ℝ))) ^ j
          * (ν / Real.sqrt μ)
      ≤ ((1 / 2 : ℝ) ^ m) ^ (2 ^ j) := by
    rw [hsqH, hdivsqrt, hHcast]
    have hA := classA_le j
    have hB := classB_le j
    have hA0 := classA_pos j
    have hB0 := classB_pos j
    have h50 : (0:ℝ) < (2:ℝ) ^ (2 * h') := by positivity
    have h53 : ((2:ℝ) ^ h') ^ j = 2 ^ (h' * j) := by rw [← pow_mul]
    have h54 : (0:ℝ) ≤ Real.sqrt ν := Real.sqrt_nonneg _
    -- term 1: classA j/2^(2h') ≤ (1/2)^(2h' - 4·2^j)-form via mult
    have hterm1 : classA j / 2 ^ (2 * h') * 2 ^ (2 * h')
        ≤ 2 ^ (4 * 2 ^ j) := by
      have h51 : classA j / 2 ^ (2 * h') * 2 ^ (2 * h') = classA j := by
        field_simp
      rw [h51]
      exact hA
    -- term 2 · 2^(2h') ≤ 2^(4·2^j)
    have hterm2 : classB j * (2 ^ h') ^ j
          * (2 ^ (j + 2) * Real.sqrt ν) * 2 ^ (2 * h')
        ≤ 2 ^ (4 * 2 ^ j) := by
      rw [h53]
      have h55 : (2:ℝ) ^ (h' * j) * 2 ^ (j + 2) * 2 ^ (2 * h')
          ≤ 2 ^ u := by
        rw [← pow_add, ← pow_add]
        refine pow_le_pow_right₀ (by norm_num) ?_
        have hb : h' * j + 2 * h' = h' * (j + 2) := by ring
        omega
      have h56 : (2:ℝ) ^ u * (1 / 2 : ℝ) ^ u = 1 := by
        rw [div_pow, one_pow]
        field_simp
      have h57 : Real.sqrt ν * ((2:ℝ) ^ (h' * j) * 2 ^ (j + 2)
            * 2 ^ (2 * h'))
          ≤ (1 / 2 : ℝ) ^ u * 2 ^ u := by
        have h58 := mul_le_mul hsqν h55 (by positivity) (by positivity)
        nlinarith [h58]
      calc classB j * (2:ℝ) ^ (h' * j)
            * (2 ^ (j + 2) * Real.sqrt ν) * 2 ^ (2 * h')
          = classB j * (Real.sqrt ν * ((2:ℝ) ^ (h' * j) * 2 ^ (j + 2)
              * 2 ^ (2 * h'))) := by ring
        _ ≤ classB j * ((1 / 2 : ℝ) ^ u * 2 ^ u) := by
            exact mul_le_mul_of_nonneg_left h57 hB0.le
        _ = classB j := by
            rw [mul_comm ((1 / 2 : ℝ) ^ u) ((2:ℝ) ^ u), h56, mul_one]
        _ ≤ 2 ^ (4 * 2 ^ j) := hB
    -- combine: (LHS)·2^(2h') ≤ 2^(4·2^j + 1) ≤ RHS·2^(2h')
    have hcomb : (classA j / 2 ^ (2 * h')
          + classB j * ((2:ℝ) ^ h') ^ j * (2 ^ (j + 2) * Real.sqrt ν))
          * 2 ^ (2 * h')
        ≤ 2 ^ (4 * 2 ^ j + 1) := by
      have h59 : (2:ℝ) ^ (4 * 2 ^ j + 1) = 2 ^ (4 * 2 ^ j) + 2 ^ (4 * 2 ^ j) := by
        rw [pow_succ]
        ring
      nlinarith [hterm1, hterm2]
    have hRHS : (2:ℝ) ^ (4 * 2 ^ j + 1)
        ≤ ((1 / 2 : ℝ) ^ m) ^ (2 ^ j) * 2 ^ (2 * h') := by
      have h60 : ((1 / 2 : ℝ) ^ m) ^ (2 ^ j) = (1 / 2 : ℝ) ^ (m * 2 ^ j) := by
        rw [← pow_mul]
      rw [h60]
      have h61 : (1 / 2 : ℝ) ^ (m * 2 ^ j) * 2 ^ (m * 2 ^ j) = 1 := by
        rw [div_pow, one_pow]
        field_simp
      have h62 : (2:ℝ) ^ (4 * 2 ^ j + 1) * 2 ^ (m * 2 ^ j)
          ≤ 2 ^ (2 * h') := by
        rw [← pow_add]
        refine pow_le_pow_right₀ (by norm_num) ?_
        omega
      have h63 : (0:ℝ) < (2:ℝ) ^ (m * 2 ^ j) := by positivity
      nlinarith [h62, h61]
    have h64 : (0:ℝ) ≤ classA j / 2 ^ (2 * h')
        + classB j * ((2:ℝ) ^ h') ^ j * (2 ^ (j + 2) * Real.sqrt ν) := by
      positivity
    nlinarith [hcomb, hRHS, h50]
  -- root and finish
  have hq : (2:ℕ) ^ j ≠ 0 := (Nat.two_pow_pos j).ne'
  have hpb0 : (0:ℝ) ≤ classA j / (((4 ^ h' : ℕ) : ℝ))
      + classB j * (Real.sqrt (((4 ^ h' : ℕ) : ℝ))) ^ j
        * (ν / Real.sqrt μ) := by
    have hA0 := classA_pos j
    have hB0 := classB_pos j
    have h65 : (0:ℝ) < (((4 ^ h' : ℕ) : ℝ)) := by
      have : 1 ≤ 4 ^ h' := Nat.one_le_pow _ _ (by norm_num)
      exact_mod_cast this
    positivity
  have hroot : (classA j / (((4 ^ h' : ℕ) : ℝ))
        + classB j * (Real.sqrt (((4 ^ h' : ℕ) : ℝ))) ^ j
          * (ν / Real.sqrt μ)) ^ (((2 ^ j : ℕ) : ℝ)⁻¹)
      ≤ (1 / 2 : ℝ) ^ m := by
    have h66 := Real.rpow_le_rpow hpb0 hpb
      (by positivity : (0:ℝ) ≤ (((2 ^ j : ℕ) : ℝ))⁻¹)
    rwa [Real.pow_rpow_inv_natCast (by positivity) hq] at h66
  calc 2 * (classA j / (((4 ^ h' : ℕ) : ℝ))
        + classB j * (Real.sqrt (((4 ^ h' : ℕ) : ℝ))) ^ j
          * (ν / Real.sqrt μ)) ^ (((2 ^ j : ℕ) : ℝ)⁻¹)
      ≤ 2 * (1 / 2 : ℝ) ^ m := by
        nlinarith [hroot]

/-- The class of a block. -/
def schedJ (d i : ℕ) : ℕ := (d - 2) / i - 1

/-- The slack budget of a block. -/
def schedU (d i : ℕ) : ℕ :=
  (i * (schedJ d i + 2) - (d + 1 + (schedJ d i + 1) ^ 2)) / 2

/-- The differencing log-length of a block. -/
def schedH (d i : ℕ) : ℕ :=
  (schedU d i - (schedJ d i + 2)) / (schedJ d i + 2)

/-- The integer saving of a block. -/
def schedM (d i : ℕ) : ℕ :=
  (2 * schedH d i - (4 * 2 ^ schedJ d i + 1)) / 2 ^ schedJ d i

/-- A block is good when the schedule data satisfies every dispatch
condition with genuine saving. -/
def goodBlock (d i : ℕ) : Prop :=
  1 ≤ i ∧ i * (schedJ d i + 1) + 2 ≤ d
  ∧ d + 1 + (schedJ d i + 1) ^ 2 + 2 * (schedJ d i + 2) + 2
      ≤ i * (schedJ d i + 2)
  ∧ 4 * 2 ^ schedJ d i + 1 + 2 ^ schedJ d i ≤ 2 * schedH d i
  ∧ schedJ d i * 4 ^ schedH d i + schedJ d i + 2 ≤ 2 ^ (i + 1)

instance (d i : ℕ) : Decidable (goodBlock d i) := by
  unfold goodBlock
  infer_instance

/-- **The dispatch bridge**: a good block satisfies every hypothesis of
`zeta_block_saving` at its schedule data. -/
theorem goodBlock_dispatch {d i : ℕ} (hg : goodBlock d i) :
    i * (schedJ d i + 1) + 2 ≤ d
    ∧ 2 * schedU d i + d + 1 + (schedJ d i + 1) ^ 2
        ≤ i * (schedJ d i + 2)
    ∧ schedH d i * (schedJ d i + 2) + schedJ d i + 2 ≤ schedU d i
    ∧ schedM d i * 2 ^ schedJ d i + 4 * 2 ^ schedJ d i + 1
        ≤ 2 * schedH d i
    ∧ schedJ d i * 4 ^ schedH d i + schedJ d i + 2 ≤ 2 ^ (i + 1)
    ∧ 1 ≤ schedM d i := by
  obtain ⟨hi1, hij, hslack, hsave, hwin⟩ := hg
  set j := schedJ d i with hj
  -- u-facts
  have hu1 : 2 * schedU d i
      ≤ i * (j + 2) - (d + 1 + (j + 1) ^ 2) := by
    rw [schedU, ← hj]
    omega
  have hu2 : d + 1 + (j + 1) ^ 2 ≤ i * (j + 2) := by omega
  -- u lower bound: schedU ≥ (j + 2) + 1
  have hu3 : (j + 2) + 1 ≤ schedU d i := by
    rw [schedU, ← hj]
    have h1 : 2 * ((j + 2) + 1) ≤ i * (j + 2) - (d + 1 + (j + 1) ^ 2) := by
      omega
    omega
  -- h'-facts
  have hh1 : schedH d i * (j + 2) ≤ schedU d i - (j + 2) := by
    rw [schedH, ← hj]
    exact Nat.div_mul_le_self _ _
  -- m-facts
  have hm1 : schedM d i * 2 ^ j ≤ 2 * schedH d i - (4 * 2 ^ j + 1) := by
    rw [schedM, ← hj]
    exact Nat.div_mul_le_self _ _
  have hm2 : 1 ≤ schedM d i := by
    rw [schedM, ← hj]
    refine (Nat.le_div_iff_mul_le (Nat.two_pow_pos j)).mpr ?_
    omega
  refine ⟨hij, by omega, by omega, by omega, hwin, hm2⟩

/-- **The geometric fiber sum**: halving powers of a floored quotient sum
to at most `2q`. -/
theorem sum_half_pow_div_le (W q : ℕ) (hq : 1 ≤ q) :
    ∑ x ∈ Finset.range W, (1 / 2 : ℝ) ^ (x / q) ≤ 2 * q := by
  classical
  have hmaps : ∀ x ∈ Finset.range W, x / q ∈ Finset.range (W / q + 1) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    have h1 : x / q ≤ W / q := Nat.div_le_div_right hx.le
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun x => (1 / 2 : ℝ) ^ (x / q))]
  have hfiber : ∀ k ∈ Finset.range (W / q + 1),
      ∑ x ∈ (Finset.range W).filter (fun x => x / q = k),
        (1 / 2 : ℝ) ^ (x / q)
      ≤ (q : ℝ) * (1 / 2 : ℝ) ^ k := by
    intro k hk
    have h2 : ∀ x ∈ (Finset.range W).filter (fun x => x / q = k),
        (1 / 2 : ℝ) ^ (x / q) = (1 / 2 : ℝ) ^ k := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [hx.2]
    rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have h3 : (Finset.range W).filter (fun x => x / q = k)
        ⊆ Finset.Ico (k * q) ((k + 1) * q) := by
      intro x hx
      rw [Finset.mem_filter, Finset.mem_range] at hx
      rw [Finset.mem_Ico]
      constructor
      · rw [← hx.2]
        exact Nat.div_mul_le_self x q
      · have h4a := Nat.div_add_mod x q
        have h4b : x % q < q := Nat.mod_lt _ (by omega)
        rw [hx.2] at h4a
        have hb : (k + 1) * q = q * k + q := by ring
        omega
    have h5 := Finset.card_le_card h3
    rw [Nat.card_Ico] at h5
    have h6 : (k + 1) * q - k * q = q := by
      have : (k + 1) * q = k * q + q := by ring
      omega
    rw [h6] at h5
    exact_mod_cast h5
  refine le_trans (Finset.sum_le_sum hfiber) ?_
  rw [← Finset.mul_sum]
  have hgeom : ∑ k ∈ Finset.range (W / q + 1), (1 / 2 : ℝ) ^ k ≤ 2 := by
    have h7 := geom_sum_eq (show (1 / 2 : ℝ) ≠ 1 by norm_num)
      (W / q + 1)
    rw [h7]
    have h8 : (0:ℝ) < (1 / 2 : ℝ) ^ (W / q + 1) := by positivity
    rw [div_le_iff_of_neg (by norm_num : (1 / 2 : ℝ) - 1 < 0)]
    nlinarith
  have hq0 : (0:ℝ) ≤ (q:ℝ) := Nat.cast_nonneg _
  calc (q:ℝ) * ∑ k ∈ Finset.range (W / q + 1), (1 / 2 : ℝ) ^ k
      ≤ (q:ℝ) * 2 := mul_le_mul_of_nonneg_left hgeom hq0
    _ = 2 * q := by ring

/-- Division lower bound under an additive shift. -/
theorem nat_div_add_le {x y k c : ℕ} (hc : 0 < c) (h : x + k * c ≤ y) :
    x / c + k ≤ y / c := by
  have h1 : (x + k * c) / c ≤ y / c := Nat.div_le_div_right h
  rw [Nat.add_mul_div_right _ _ hc] at h1
  omega

/-- **The saving increment**: within a class, `2^{j+3}` block-steps force
the saving up by one (on good blocks). -/
theorem schedM_increment {d i i' : ℕ}
    (hslack : d + 1 + (schedJ d i + 1) ^ 2 + 2 * (schedJ d i + 2) + 2
      ≤ i * (schedJ d i + 2))
    (hj : schedJ d i' = schedJ d i)
    (hstep : i + 2 ^ (schedJ d i + 4) ≤ i') :
    schedM d i + 1 ≤ schedM d i' := by
  set j := schedJ d i with hjdef
  set A := d + 1 + (j + 1) ^ 2 with hAdef
  have hstep' : i * (j + 2) + 2 ^ (j + 4) * (j + 2) ≤ i' * (j + 2) := by
    have h1a := Nat.mul_le_mul_right (j + 2) hstep
    have h1b : (i + 2 ^ (j + 4)) * (j + 2)
        = i * (j + 2) + 2 ^ (j + 4) * (j + 2) := by ring
    omega
  have hAX : A + 2 * (j + 2) + 2 ≤ i * (j + 2) := hslack
  -- u increases by at least 2^{j+2}(j+2) − 1
  have hu : schedU d i + (2 ^ (j + 3) * (j + 2) - 1) ≤ schedU d i' := by
    rw [schedU, schedU, hj, ← hjdef, ← hAdef]
    have h5 : 2 ^ (j + 4) * (j + 2) = 2 ^ (j + 3) * (j + 2) * 2 := by
      rw [pow_succ]
      ring
    have h2 : (i * (j + 2) - A) + (2 ^ (j + 3) * (j + 2) * 2 - 2)
        ≤ i' * (j + 2) - A := by omega
    have h6 := nat_div_add_le (show 0 < 2 by norm_num)
      (x := i * (j + 2) - A)
      (k := 2 ^ (j + 3) * (j + 2) - 1)
      (y := i' * (j + 2) - A) (by
        have h7 : 1 ≤ 2 ^ (j + 3) * (j + 2) := by
          have := Nat.one_le_two_pow (n := j + 3)
          nlinarith
        omega)
    omega
  -- h' increases by at least 2^{j+2} − 3
  have hh' : schedH d i + (2 ^ (j + 3) - 3) ≤ schedH d i' := by
    rw [schedH, schedH, hj, ← hjdef]
    have h8 : 1 ≤ 2 ^ (j + 3) := Nat.one_le_two_pow
    have h9 : (schedU d i - (j + 2))
          + (2 ^ (j + 3) - 3) * (j + 2)
        ≤ schedU d i' - (j + 2) := by
      have h10 : (2 ^ (j + 3) - 3) * (j + 2)
          ≤ 2 ^ (j + 3) * (j + 2) - 3 * (j + 2) := by
        have h12 : (2 ^ (j + 3) - 3) * (j + 2)
            = 2 ^ (j + 3) * (j + 2) - 3 * (j + 2) := by
          rw [Nat.sub_mul]
        have h13 : 4 ≤ 2 ^ (j + 3) := by
          calc (4:ℕ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (j + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      omega
    have h14 := nat_div_add_le (show 0 < j + 2 by omega)
      (x := schedU d i - (j + 2)) (k := 2 ^ (j + 3) - 3)
      (y := schedU d i' - (j + 2)) (by omega)
    omega
  -- m increases by at least 1
  rw [schedM, schedM, hj, ← hjdef]
  have h16 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have h17 : (2 * schedH d i - (4 * 2 ^ j + 1)) + 1 * 2 ^ j
      ≤ 2 * schedH d i' - (4 * 2 ^ j + 1) := by
    have h18 : 2 ^ (j + 3) = 8 * 2 ^ j := by
      rw [pow_add]
      ring
    omega
  have h19 := nat_div_add_le (Nat.two_pow_pos j)
    (x := 2 * schedH d i - (4 * 2 ^ j + 1)) (k := 1)
    (y := 2 * schedH d i' - (4 * 2 ^ j + 1)) h17
  omega

/-- Schedule saving is monotone within a class (given slack at the left). -/
theorem schedM_mono {d i i' : ℕ}
    (hj : schedJ d i' = schedJ d i) (hii : i ≤ i') :
    schedM d i ≤ schedM d i' := by
  set j := schedJ d i with hjdef
  have hu : schedU d i ≤ schedU d i' := by
    rw [schedU, schedU, hj, ← hjdef]
    refine Nat.div_le_div_right (Nat.sub_le_sub_right ?_ _)
    exact Nat.mul_le_mul_right _ hii
  have hh' : schedH d i ≤ schedH d i' := by
    rw [schedH, schedH, hj, ← hjdef]
    exact Nat.div_le_div_right (Nat.sub_le_sub_right hu _)
  rw [schedM, schedM, hj, ← hjdef]
  exact Nat.div_le_div_right (by omega)

/-- **The affine saving bound**: within a same-class interval with slack
at its base, the saving grows linearly at rate `2^{-(j+3)}`. -/
theorem schedM_affine {d i₀ : ℕ}
    (hslack : d + 1 + (schedJ d i₀ + 1) ^ 2 + 2 * (schedJ d i₀ + 2) + 2
      ≤ i₀ * (schedJ d i₀ + 2)) :
    ∀ q i, i₀ ≤ i →
      (∀ i'', i₀ ≤ i'' → i'' ≤ i → schedJ d i'' = schedJ d i₀) →
      (i - i₀) / 2 ^ (schedJ d i₀ + 4) ≤ q →
      schedM d i₀ + (i - i₀) / 2 ^ (schedJ d i₀ + 4) ≤ schedM d i := by
  intro q
  induction q with
  | zero =>
    intro i hi hcl hq
    have h1 : (i - i₀) / 2 ^ (schedJ d i₀ + 4) = 0 := Nat.le_zero.mp hq
    rw [h1, Nat.add_zero]
    exact schedM_mono (hcl i hi le_rfl) hi
  | succ q ih =>
    intro i hi hcl hq
    by_cases h2 : (i - i₀) / 2 ^ (schedJ d i₀ + 4) ≤ q
    · exact ih i hi hcl h2
    · push_neg at h2
      have hs1 : 1 ≤ 2 ^ (schedJ d i₀ + 4) := Nat.one_le_two_pow
      have h3 : 2 ^ (schedJ d i₀ + 4) ≤ i - i₀ := by
        by_contra h4
        push_neg at h4
        have h5 : (i - i₀) / 2 ^ (schedJ d i₀ + 4) = 0 :=
          Nat.div_eq_of_lt h4
        omega
      set i₁ := i - 2 ^ (schedJ d i₀ + 4) with hi₁
      have hi₁0 : i₀ ≤ i₁ := by omega
      have hcl₁ : ∀ i'', i₀ ≤ i'' → i'' ≤ i₁ → schedJ d i'' = schedJ d i₀ :=
        fun i'' h1' h2' => hcl i'' h1' (by omega)
      have hq₁ : (i₁ - i₀) / 2 ^ (schedJ d i₀ + 4) ≤ q := by
        have h6 : i - i₀ = (i₁ - i₀) + 2 ^ (schedJ d i₀ + 4) := by omega
        have h7 := Nat.add_div_right (i₁ - i₀)
          (Nat.two_pow_pos (schedJ d i₀ + 4))
        rw [h6] at hq
        omega
      have hIH := ih i₁ hi₁0 hcl₁ hq₁
      have hslack₁ : d + 1 + (schedJ d i₁ + 1) ^ 2
          + 2 * (schedJ d i₁ + 2) + 2 ≤ i₁ * (schedJ d i₁ + 2) := by
        rw [hcl i₁ hi₁0 (by omega)]
        have h8 : i₀ * (schedJ d i₀ + 2) ≤ i₁ * (schedJ d i₀ + 2) :=
          Nat.mul_le_mul_right _ hi₁0
        exact le_trans hslack h8
      have hinc := schedM_increment hslack₁
        (show schedJ d i = schedJ d i₁ by
          rw [hcl i₁ hi₁0 (by omega), hcl i hi le_rfl])
        (by rw [hcl i₁ hi₁0 (by omega)]; omega)
      have h9 : i - i₀ = (i₁ - i₀) + 2 ^ (schedJ d i₀ + 4) := by omega
      have h10 := Nat.add_div_right (i₁ - i₀)
        (Nat.two_pow_pos (schedJ d i₀ + 4))
      rw [h9, h10]
      omega

/-- The class is antitone in the block index. -/
theorem schedJ_anti (d : ℕ) {i i' : ℕ} (h : i ≤ i') (hi : 1 ≤ i) :
    schedJ d i' ≤ schedJ d i := by
  rw [schedJ, schedJ]
  have h1 : (d - 2) / i' ≤ (d - 2) / i := Nat.div_le_div_left h hi
  omega

/-- **The class sum**: good same-class blocks have geometrically summable
savings. -/
theorem class_sum_le (d j : ℕ) (S : Finset ℕ)
    (hS : ∀ i ∈ S, goodBlock d i ∧ schedJ d i = j ∧ i ≤ d) :
    ∑ i ∈ S, (1 / 2 : ℝ) ^ (schedM d i) ≤ 2 ^ (j + 4) := by
  classical
  rcases S.eq_empty_or_nonempty with hE | hne
  · subst hE
    simp only [Finset.sum_empty]
    positivity
  · obtain ⟨i₀, hi₀S, hi₀min⟩ : ∃ i₀ ∈ S, ∀ i ∈ S, i₀ ≤ i :=
      ⟨S.min' hne, S.min'_mem hne, fun i => S.min'_le i⟩
    obtain ⟨hg₀, hj₀, hd₀⟩ := hS i₀ hi₀S
    have hi₀1 : 1 ≤ i₀ := hg₀.1
    have hm₀ : 1 ≤ schedM d i₀ := (goodBlock_dispatch hg₀).2.2.2.2.2
    have hslack₀ : d + 1 + (schedJ d i₀ + 1) ^ 2
        + 2 * (schedJ d i₀ + 2) + 2 ≤ i₀ * (schedJ d i₀ + 2) :=
      hg₀.2.2.1
    -- pointwise affine bound
    have hpt : ∀ i ∈ S, (1 / 2 : ℝ) ^ (schedM d i)
        ≤ (1 / 2 : ℝ) ^ (1 + (i - i₀) / 2 ^ (j + 4)) := by
      intro i hiS
      obtain ⟨hg, hj, hd⟩ := hS i hiS
      have hi₀i : i₀ ≤ i := hi₀min i hiS
      have hcl : ∀ i'', i₀ ≤ i'' → i'' ≤ i → schedJ d i'' = schedJ d i₀ := by
        intro i'' h1 h2
        have h3 := schedJ_anti d h1 hi₀1
        have h4 := schedJ_anti d h2 (by omega : 1 ≤ i'')
        omega
      have haff := schedM_affine hslack₀ ((i - i₀) / 2 ^ (schedJ d i₀ + 4))
        i hi₀i hcl le_rfl
      refine pow_le_pow_of_le_one (by norm_num) (by norm_num) ?_
      rw [hj₀] at haff
      omega
    refine le_trans (Finset.sum_le_sum hpt) ?_
    -- reindex to shifted range
    have himg : ∑ i ∈ S, (1 / 2 : ℝ) ^ (1 + (i - i₀) / 2 ^ (j + 4))
        = ∑ x ∈ S.image (· - i₀),
            (1 / 2 : ℝ) ^ (1 + x / 2 ^ (j + 4)) := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      have h5 : i₀ ≤ a := hi₀min a ha
      have h6 : i₀ ≤ b := hi₀min b hb
      have hab' : a - i₀ = b - i₀ := hab
      omega
    rw [himg]
    have hsub : S.image (· - i₀) ⊆ Finset.range (d + 1) := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, hiS, rfl⟩ := hx
      rw [Finset.mem_range]
      have := (hS i hiS).2.2
      omega
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun x _ _ => by positivity)) ?_
    have hsplit : ∀ x ∈ Finset.range (d + 1),
        (1 / 2 : ℝ) ^ (1 + x / 2 ^ (j + 4))
        = (1 / 2) * (1 / 2 : ℝ) ^ (x / 2 ^ (j + 4)) := by
      intro x _
      rw [pow_add, pow_one]
    rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum]
    have hgeo := sum_half_pow_div_le (d + 1) (2 ^ (j + 4))
      Nat.one_le_two_pow
    have h7 : ((2 ^ (j + 4) : ℕ) : ℝ) = 2 ^ (j + 4) := by push_cast; ring
    rw [h7] at hgeo
    calc (1 / 2 : ℝ) * ∑ x ∈ Finset.range (d + 1),
          (1 / 2 : ℝ) ^ (x / 2 ^ (j + 4))
        ≤ (1 / 2 : ℝ) * (2 * 2 ^ (j + 4)) := by
          refine mul_le_mul_of_nonneg_left hgeo (by norm_num)
      _ = 2 ^ (j + 4) := by ring

/-- Quadratic-plus-linear growth is dominated by `2^{j+5}`. -/
theorem sq_lin_le_two_pow (j : ℕ) : (j + 1) ^ 2 + 3 * j + 12 ≤ 2 ^ (j + 5) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    have hb : (j + 1 + 1) ^ 2 = (j + 1) ^ 2 + 2 * j + 3 := by ring
    have hp : (2:ℕ) ^ (j + 1 + 5) = 2 * 2 ^ (j + 5) := by ring
    omega

/-- `2j + 2 ≤ 2^{j+2}`. -/
theorem two_succ_le_two_pow (j : ℕ) : 2 * j + 2 ≤ 2 ^ (j + 2) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    have hp : (2:ℕ) ^ (j + 1 + 2) = 2 * 2 ^ (j + 2) := by ring
    omega

/-- **The goodness threshold**: a class-`j` block at distance `2^{j+5}`
past the class floor is good. -/
theorem good_of_range {d j i : ℕ}
    (hj : schedJ d i = j) (hi1 : 1 ≤ i) (hile : i ≤ d - 2)
    (hlo : (d - 2) / (j + 2) + 2 ^ (j + 5) ≤ i) :
    goodBlock d i := by
  have hd2 : 2 ≤ d := by omega
  have hdiv1 : 1 ≤ (d - 2) / i := (Nat.one_le_div_iff (by omega)).mpr hile
  have hdiv : (d - 2) / i = j + 1 := by
    rw [schedJ] at hj
    omega
  -- pointwise class bounds
  have hup : i * (j + 1) ≤ d - 2 := by
    have h1 := Nat.div_mul_le_self (d - 2) i
    rw [hdiv] at h1
    have hb : (j + 1) * i = i * (j + 1) := by ring
    omega
  -- floor-shifted product lower bound
  have hmod := Nat.div_add_mod (d - 2) (j + 2)
  have hmlt : (d - 2) % (j + 2) < j + 2 := Nat.mod_lt _ (by omega)
  have hiprod : ((d - 2) / (j + 2) + 2 ^ (j + 5)) * (j + 2) ≤ i * (j + 2) :=
    Nat.mul_le_mul_right _ hlo
  have hbrid : ((d - 2) / (j + 2) + 2 ^ (j + 5)) * (j + 2)
      = (j + 2) * ((d - 2) / (j + 2)) + 2 ^ (j + 5) * (j + 2) := by ring
  have hkey : d - 2 + 2 ^ (j + 5) * (j + 2) ≤ i * (j + 2) + j + 1 := by omega
  have hsq := sq_lin_le_two_pow j
  have hP3 : 2 ^ (j + 5) * 2 ≤ 2 ^ (j + 5) * (j + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  -- the slack conjunct
  have hslack : d + 1 + (j + 1) ^ 2 + 2 * (j + 2) + 2 ≤ i * (j + 2) := by
    omega
  have hc2 : i * (j + 1) + 2 ≤ d := by omega
  -- u lower bound
  have hu_lb : (3 * 2 ^ j + 1) * (j + 2) ≤ schedU d i := by
    rw [schedU, hj]
    refine (Nat.le_div_iff_mul_le (by norm_num)).mpr ?_
    have hb2 : (3 * 2 ^ j + 1) * (j + 2) * 2
        = 6 * (2 ^ j * (j + 2)) + 2 * (j + 2) := by ring
    have hb3 : 2 ^ (j + 5) * (j + 2) = 32 * (2 ^ j * (j + 2)) := by ring
    have hb5 : (2:ℕ) ^ (j + 5) = 32 * 2 ^ j := by ring
    have hQ2 : 2 ^ j * 2 ≤ 2 ^ j * (j + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  -- h' lower bound
  have hh_lb : 3 * 2 ^ j ≤ schedH d i := by
    rw [schedH, hj]
    refine (Nat.le_div_iff_mul_le (by omega)).mpr ?_
    have hb6 : (3 * 2 ^ j + 1) * (j + 2)
        = 3 * 2 ^ j * (j + 2) + (j + 2) := by ring
    omega
  -- the save conjunct
  have hc4 : 4 * 2 ^ j + 1 + 2 ^ j ≤ 2 * schedH d i := by
    have h1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    omega
  -- u upper bound
  have hu_ub : 2 * schedU d i ≤ i - 3 - (j + 1) ^ 2 := by
    rw [schedU, hj]
    have h1 : 2 * ((i * (j + 2) - (d + 1 + (j + 1) ^ 2)) / 2)
        ≤ i * (j + 2) - (d + 1 + (j + 1) ^ 2) := by omega
    have hb7 : i * (j + 2) = i * (j + 1) + i := by ring
    omega
  -- h' upper bound
  have hh_ub : 2 * schedH d i ≤ schedU d i := by
    rw [schedH, hj]
    have h1 : (schedU d i - (j + 2)) / (j + 2)
        ≤ (schedU d i - (j + 2)) / 2 :=
      Nat.div_le_div_left (by omega) (by norm_num)
    have h2 : 2 * ((schedU d i - (j + 2)) / 2)
        ≤ schedU d i - (j + 2) := by omega
    omega
  -- exponent chain for the window
  have hexp : j + 2 + 2 * schedH d i ≤ i + 1 := by
    have hb8 : (j + 1) ^ 2 = j * j + 2 * j + 1 := by ring
    omega
  -- the window conjunct
  have hc5 : j * 4 ^ schedH d i + j + 2 ≤ 2 ^ (i + 1) := by
    have h4h : (4:ℕ) ^ schedH d i = 2 ^ (2 * schedH d i) := by
      rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    have h1 : 1 ≤ 4 ^ schedH d i := Nat.one_le_pow _ _ (by norm_num)
    have h2 : j * 4 ^ schedH d i + j + 2
        ≤ (2 * j + 2) * 4 ^ schedH d i := by
      have h3 : (j + 2) * 1 ≤ (j + 2) * 4 ^ schedH d i :=
        Nat.mul_le_mul_left _ h1
      have hb9 : (2 * j + 2) * 4 ^ schedH d i
          = j * 4 ^ schedH d i + (j + 2) * 4 ^ schedH d i := by ring
      omega
    have h4 : (2 * j + 2) * 4 ^ schedH d i
        ≤ 2 ^ (j + 2) * 4 ^ schedH d i :=
      Nat.mul_le_mul_right _ (two_succ_le_two_pow j)
    have h5 : 2 ^ (j + 2) * 4 ^ schedH d i
        = 2 ^ (j + 2 + 2 * schedH d i) := by
      rw [h4h, ← pow_add]
    have h6 : (2:ℕ) ^ (j + 2 + 2 * schedH d i) ≤ 2 ^ (i + 1) :=
      Nat.pow_le_pow_right (by norm_num) hexp
    omega
  refine ⟨hi1, ?_, ?_, ?_, ?_⟩ <;> rw [hj]
  · exact hc2
  · exact hslack
  · exact hc4
  · exact hc5

/-- Dyadic partial sums are dominated by the next power. -/
theorem sum_pow_le (n c : ℕ) :
    ∑ j ∈ Finset.range n, 2 ^ (j + c) ≤ 2 ^ (n + c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hp : (2:ℕ) ^ (n + 1 + c) = 2 * 2 ^ (n + c) := by ring
    omega

set_option maxHeartbeats 1600000 in
/-- **The zeta head bound**: dispatching every dyadic block through the
schedule, the weighted head sum is bounded by the bad-block count plus
geometrically summable class savings. -/
theorem zeta_head_bound (d K : ℕ) (t : ℝ) (w : ℕ → ℝ)
    (ht1 : (2:ℝ) ^ d ≤ t) (ht2 : t ≤ 2 ^ (d + 1))
    (hw0 : ∀ n, 1 ≤ n → 0 ≤ w n)
    (hwd : ∀ n, 1 ≤ n → w (n + 1) ≤ w n)
    (hwM : ∀ n, 1 ≤ n → w n ≤ 1 / (n : ℝ)) :
    ‖∑ n ∈ Finset.Ico 1 (2 ^ (d + 1)),
        w n • e (-(t / (2 * Real.pi) * Real.log n))‖
      ≤ (((d - 2) / (K + 2) + 2 ^ (K + 7) + 3 : ℕ) : ℝ) := by
  classical
  set T : ℕ := 2 ^ (d + 1) - 1 with hT
  have hT1 : T + 1 = 2 ^ (d + 1) := by
    have := Nat.one_le_two_pow (n := d + 1)
    omega
  -- per-block dispatch
  have hblock : ∀ i, i < d + 1 →
      ‖∑ n ∈ Finset.Ico (2 ^ i) (2 ^ (i + 1)),
          w n • e (-(t / (2 * Real.pi) * Real.log n))‖
        ≤ (if goodBlock d i ∧ schedJ d i ≤ K
            then 2 * (1 / 2 : ℝ) ^ (schedM d i) else 1) := by
    intro i _
    have h2i : (1:ℕ) ≤ 2 ^ i := Nat.one_le_two_pow
    have h2i1 : (2:ℕ) ^ (i + 1) = 2 * 2 ^ i := by ring
    have hNe : (2:ℕ) ^ (i + 1) = (2 ^ (i + 1) - 1) + 1 := by omega
    have hw0' : ∀ n, 2 ^ i ≤ n → n ≤ 2 ^ (i + 1) - 1 → 0 ≤ w n :=
      fun n h1 _ => hw0 n (le_trans h2i h1)
    have hwd' : ∀ n, 2 ^ i ≤ n → n < 2 ^ (i + 1) - 1 → w (n + 1) ≤ w n :=
      fun n h1 _ => hwd n (le_trans h2i h1)
    have hwM' : w (2 ^ i) ≤ 1 / ((2 ^ i : ℕ) : ℝ) := hwM _ h2i
    by_cases hP : goodBlock d i ∧ schedJ d i ≤ K
    · have hg := hP.1
      obtain ⟨hij, hu, hh', hm, hwin, _⟩ := goodBlock_dispatch hg
      have hs := zeta_block_saving i (schedJ d i) (schedH d i) (schedU d i)
        (schedM d i) d (2 ^ (i + 1) - 1) t w ht1 ht2 hij hu hh' hm hwin
        (by omega) (by omega) hw0' hwd' hwM'
      rw [if_pos hP, hNe]
      exact hs
    · have hs := zeta_block_trivial (2 ^ i) (2 ^ (i + 1) - 1) w
        (fun n => e (-(t / (2 * Real.pi) * Real.log n)))
        h2i (by omega) (fun n => (norm_e _).le) hw0' hwd' hwM'
      rw [if_neg hP, hNe]
      exact hs
  -- the bad-block count
  have hcard : ((Finset.range (d + 1)).filter
      (fun i => ¬(goodBlock d i ∧ schedJ d i ≤ K))).card
      ≤ (d - 2) / (K + 2) + 2 ^ (K + 6) + 3 := by
    have hsub : (Finset.range (d + 1)).filter
        (fun i => ¬(goodBlock d i ∧ schedJ d i ≤ K))
        ⊆ (Finset.range ((d - 2) / (K + 2) + 1) ∪ Finset.Ioc (d - 2) d)
          ∪ (Finset.range (K + 1)).biUnion (fun j =>
              Finset.Ico ((d - 2) / (j + 2) + 1)
                ((d - 2) / (j + 2) + 2 ^ (j + 5))) := by
      intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨hid, hnP⟩ := hi
      rw [Finset.mem_union, Finset.mem_union]
      by_cases hi0 : i = 0
      · exact Or.inl (Or.inl (Finset.mem_range.mpr
          (by rw [hi0]; exact Nat.succ_pos _)))
      by_cases hup : d - 2 < i
      · exact Or.inl (Or.inr (Finset.mem_Ioc.mpr ⟨hup, by omega⟩))
      push_neg at hup
      set j := schedJ d i with hjdef
      have hdiv1 : 1 ≤ (d - 2) / i := (Nat.one_le_div_iff (by omega)).mpr hup
      have hdiv : (d - 2) / i = j + 1 := by
        rw [hjdef, schedJ]
        omega
      by_cases hjK : K + 1 ≤ j
      · refine Or.inl (Or.inl (Finset.mem_range.mpr ?_))
        have h2 := Nat.div_mul_le_self (d - 2) i
        rw [hdiv] at h2
        have h3 : i * (K + 2) ≤ i * (j + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        have hb : (j + 1) * i = i * (j + 1) := by ring
        have h5 : i ≤ (d - 2) / (K + 2) :=
          (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
        omega
      · push_neg at hjK
        have hng : ¬ goodBlock d i := fun hg => hnP ⟨hg, by omega⟩
        have hlt : i < (d - 2) / (j + 2) + 2 ^ (j + 5) := by
          by_contra hge
          push_neg at hge
          exact hng (good_of_range hjdef.symm (by omega) hup hge)
        have hgt : (d - 2) / (j + 2) < i := by
          by_contra hle
          push_neg at hle
          have h2 : i * (j + 2) ≤ (d - 2) / (j + 2) * (j + 2) :=
            Nat.mul_le_mul_right _ hle
          have h3 := Nat.div_mul_le_self (d - 2) (j + 2)
          have h4 : j + 2 ≤ (d - 2) / i :=
            (Nat.le_div_iff_mul_le (by omega)).mpr (by
              have hb : (j + 2) * i = i * (j + 2) := by ring
              omega)
          omega
        exact Or.inr (Finset.mem_biUnion.mpr
          ⟨j, Finset.mem_range.mpr (by omega),
            Finset.mem_Ico.mpr ⟨by omega, by omega⟩⟩)
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_union_le _ _) ?_
    have h1 := Finset.card_union_le
      (Finset.range ((d - 2) / (K + 2) + 1)) (Finset.Ioc (d - 2) d)
    have h2 := Finset.card_biUnion_le (s := Finset.range (K + 1))
      (t := fun j => Finset.Ico ((d - 2) / (j + 2) + 1)
        ((d - 2) / (j + 2) + 2 ^ (j + 5)))
    have h3 : ∑ j ∈ Finset.range (K + 1),
        (Finset.Ico ((d - 2) / (j + 2) + 1)
          ((d - 2) / (j + 2) + 2 ^ (j + 5))).card ≤ 2 ^ (K + 6) := by
      have h4 : ∀ j ∈ Finset.range (K + 1),
          (Finset.Ico ((d - 2) / (j + 2) + 1)
            ((d - 2) / (j + 2) + 2 ^ (j + 5))).card ≤ 2 ^ (j + 5) := by
        intro j _
        rw [Nat.card_Ico]
        have h1 : 1 ≤ 2 ^ (j + 5) := Nat.one_le_two_pow
        omega
      refine le_trans (Finset.sum_le_sum h4) ?_
      refine le_trans (sum_pow_le (K + 1) 5) ?_
      exact le_of_eq (by ring)
    rw [Finset.card_range] at h1
    have h6 : (Finset.Ioc (d - 2) d).card ≤ 2 := by
      rw [Nat.card_Ioc]
      omega
    omega
  -- the good-class sums
  have hgood : ∑ i ∈ (Finset.range (d + 1)).filter
      (fun i => goodBlock d i ∧ schedJ d i ≤ K),
      (if goodBlock d i ∧ schedJ d i ≤ K
        then 2 * (1 / 2 : ℝ) ^ (schedM d i) else 1)
      ≤ (2:ℝ) ^ (K + 6) := by
    rw [Finset.sum_congr rfl
      (fun i hi => if_pos (Finset.mem_filter.mp hi).2)]
    have hmaps : ∀ i ∈ (Finset.range (d + 1)).filter
        (fun i => goodBlock d i ∧ schedJ d i ≤ K),
        schedJ d i ∈ Finset.range (K + 1) := by
      intro i hi
      rw [Finset.mem_filter] at hi
      exact Finset.mem_range.mpr (by omega)
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun i => 2 * (1 / 2 : ℝ) ^ (schedM d i))]
    have hinner : ∀ j ∈ Finset.range (K + 1),
        ∑ i ∈ ((Finset.range (d + 1)).filter
          (fun i => goodBlock d i ∧ schedJ d i ≤ K)).filter
            (fun i => schedJ d i = j),
          2 * (1 / 2 : ℝ) ^ (schedM d i) ≤ 2 * 2 ^ (j + 4) := by
      intro j _
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine class_sum_le d j _ ?_
      intro i hi
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hi
      exact ⟨hi.1.2.1, hi.2, by omega⟩
    refine le_trans (Finset.sum_le_sum hinner) ?_
    have h2 : ∀ j ∈ Finset.range (K + 1),
        2 * (2:ℝ) ^ (j + 4) = ((2 ^ (j + 5) : ℕ) : ℝ) := by
      intro j _
      push_cast
      ring
    rw [Finset.sum_congr rfl h2, ← Nat.cast_sum]
    have h5 := sum_pow_le (K + 1) 5
    have hb : (2:ℕ) ^ (K + 1 + 5) = 2 ^ (K + 6) := by ring
    calc ((∑ j ∈ Finset.range (K + 1), 2 ^ (j + 5) : ℕ) : ℝ)
        ≤ ((2 ^ (K + 6) : ℕ) : ℝ) := Nat.cast_le.mpr (by omega)
      _ = (2:ℝ) ^ (K + 6) := by push_cast; ring
  -- assemble
  have hmain := norm_head_le_of_blocks
    (fun n => w n • e (-(t / (2 * Real.pi) * Real.log n)))
    T (d + 1)
    (fun i => if goodBlock d i ∧ schedJ d i ≤ K
      then 2 * (1 / 2 : ℝ) ^ (schedM d i) else 1)
    0 (by omega) hblock
    (by rw [hT1, Finset.Ico_self, Finset.sum_empty, norm_zero])
  rw [hT1, add_zero] at hmain
  refine le_trans hmain ?_
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (d + 1))
    (fun i => goodBlock d i ∧ schedJ d i ≤ K)]
  have hbad : ∑ i ∈ (Finset.range (d + 1)).filter
      (fun i => ¬(goodBlock d i ∧ schedJ d i ≤ K)),
      (if goodBlock d i ∧ schedJ d i ≤ K
        then 2 * (1 / 2 : ℝ) ^ (schedM d i) else 1)
      ≤ (((d - 2) / (K + 2) + 2 ^ (K + 6) + 3 : ℕ) : ℝ) := by
    rw [Finset.sum_congr rfl
      (fun i hi => if_neg (Finset.mem_filter.mp hi).2)]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast Nat.cast_le.mpr hcard
  have hfin : (2:ℝ) ^ (K + 6)
      + (((d - 2) / (K + 2) + 2 ^ (K + 6) + 3 : ℕ) : ℝ)
      = (((d - 2) / (K + 2) + 2 ^ (K + 7) + 3 : ℕ) : ℝ) := by
    push_cast
    ring
  calc ∑ i ∈ (Finset.range (d + 1)).filter
        (fun i => goodBlock d i ∧ schedJ d i ≤ K),
        (if goodBlock d i ∧ schedJ d i ≤ K
          then 2 * (1 / 2 : ℝ) ^ (schedM d i) else 1)
      + ∑ i ∈ (Finset.range (d + 1)).filter
          (fun i => ¬(goodBlock d i ∧ schedJ d i ≤ K)),
          (if goodBlock d i ∧ schedJ d i ≤ K
            then 2 * (1 / 2 : ℝ) ^ (schedM d i) else 1)
      ≤ (2:ℝ) ^ (K + 6)
        + (((d - 2) / (K + 2) + 2 ^ (K + 6) + 3 : ℕ) : ℝ) :=
        add_le_add hgood hbad
    _ = (((d - 2) / (K + 2) + 2 ^ (K + 7) + 3 : ℕ) : ℝ) := hfin

end ExpSums

end MoltResearch
