import MoltResearch.Discrepancy.TruncatedBridge
import MoltResearch.Discrepancy.ZetaBound

/-!
# Track C: the archimedean repulsion core (Track R, C4c-ii)

The `𝒯₁`-leg of the C4 dichotomy: away from the minimizing frequency,
the pretentious distance to *any* archimedean twist `n^{iu}` is almost
the full prime mass. The engine is the minorant `1 − cos θ ≥ 0` summed
against the Euler bridge: the cosine-twisted prime sum
`∑ cos(u log p)/p` is controlled by `log‖ζ(1 + 1/log y − iu)‖`, and the
Littlewood-quality bound of `ZetaBound.lean` caps that by
`loglog(|u|+2) + O(1)` — no zero-free region enters.

Consumed by the C4c-iii distance lower bound (via
`pretentiousDistSq_mul_weight_ge` for Ramaré-weight robustness) and by
the C4e Halász assembly.
-/

open Finset

namespace MoltResearch

/-- **The archimedean repulsion core** (C4c-ii): at any frequency
`|u| ≥ 6`, the cosine-twisted prime mass retains all but
`loglog(|u|+2) + 24` of the full mass — the trivial-character Euler
bridge against the Littlewood zeta bound. No zero-free region needed. -/
theorem sum_one_sub_cos_div_ge (u : ℝ) (y : ℕ) (hy : 3 ≤ y)
    (hu : 6 ≤ |u|) :
    (∑ p ∈ y.primesBelow, (1:ℝ)/p)
        - Real.log (Real.log (|u| + 2)) - 24
      ≤ ∑ p ∈ y.primesBelow, (1 - Real.cos (u * Real.log p))/p := by
  classical
  have hu1 : 1 ≤ |u| := by linarith
  -- the twisted sum is the cosine sum
  have hsummand : ∀ p ∈ y.primesBelow,
      (((1 : DirichletCharacter ℂ 1) p * (p : ℂ) ^ (Complex.I * (u:ℝ))).re) / p
        = Real.cos (u * Real.log p) / p := by
    intro p hp
    have hp2 := (Nat.prime_of_mem_primesBelow hp).two_le
    have hχ : (1 : DirichletCharacter ℂ 1) p = 1 :=
      congrFun (DirichletCharacter.modOne_eq_one
        (χ := (1 : DirichletCharacter ℂ 1))) p
    rw [hχ, one_mul]
    congr 1
    have hcpow : ((p:ℕ):ℂ) ^ (Complex.I * (u:ℂ))
        = Complex.exp (((u * Real.log p : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.cpow_def_of_ne_zero
        (by exact_mod_cast (by omega : p ≠ 0))]
      congr 1
      push_cast
      ring
    rw [hcpow, Complex.exp_ofReal_mul_I_re]
  -- the bridge
  have hbridge := sum_re_twist_div_le_log_norm_LSeries
    (N := 1) (1 : DirichletCharacter ℂ 1) hy u
  rw [Finset.sum_congr rfl hsummand] at hbridge
  -- identify the L-series with the constant-one series
  have hLconv : LSeries (fun n => (1 : DirichletCharacter ℂ 1) n)
      = LSeries (fun _ => 1) := by
    congr 1
    funext n
    exact congrFun (DirichletCharacter.modOne_eq_one
      (χ := (1 : DirichletCharacter ℂ 1))) n
  rw [hLconv] at hbridge
  -- the Littlewood bound at σ = 1 + 1/log y
  have hlogy1 : (1:ℝ) ≤ Real.log y := by
    have h2 : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9
      linarith
    have h3 : (3:ℝ) ≤ y := by exact_mod_cast hy
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log y := Real.log_le_log (Real.exp_pos 1) (by linarith)
  have hσ1 : (1:ℝ) < 1 + 1/Real.log y := by
    have h1 : (0:ℝ) < 1/Real.log y := by positivity
    linarith
  have hσ2 : (1:ℝ) + 1/Real.log y ≤ 2 := by
    have h4 : 1/Real.log y ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hlogy1
    linarith
  have hzeta := ExpSums.zeta_LSeries_bound (1 + 1/Real.log y) u hσ1 hσ2 hu1
  -- log-numerics
  have hA1 : (2:ℝ) ≤ Real.log (|u| + 2) := by
    have h1 : (8:ℝ) ≤ |u| + 2 := by linarith
    have h2 : Real.log 8 ≤ Real.log (|u| + 2) :=
      Real.log_le_log (by norm_num) h1
    have h3 : (2:ℝ) ≤ Real.log 8 := by
      rw [show (8:ℝ) = 2^3 from by norm_num, Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast
      linarith
    linarith
  have hA0 : (0:ℝ) < Real.log (|u| + 2) := by linarith
  have hB : Real.log 2 ≤ Real.log (Real.log (|u| + 2)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hB0 : (0:ℝ) < Real.log (Real.log (|u| + 2)) := by
    have := Real.log_two_gt_d9
    linarith
  have hlogB_low : (-1:ℝ) ≤ Real.log (Real.log (Real.log (|u| + 2))) := by
    have h1 : Real.log (Real.log 2) ≤ Real.log (Real.log (Real.log (|u|+2))) := by
      refine Real.log_le_log ?_ hB
      have := Real.log_two_gt_d9
      linarith
    have h3 := Real.log_two_gt_d9
    have h4 : (0.69:ℝ) < Real.log 2 := by linarith
    have h5 : Real.log 0.69 ≤ Real.log (Real.log 2) :=
      Real.log_le_log (by norm_num) h4.le
    have h6 : Real.log (100/69 : ℝ) ≤ 100/69 - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    have h7 : Real.log (0.69:ℝ) = -Real.log (100/69 : ℝ) := by
      rw [← Real.log_inv]
      norm_num
    have h8 : (100:ℝ)/69 - 1 ≤ 1/2 := by norm_num
    linarith
  -- log L ≤ log(8192·A/B), even when the norm degenerates
  have hnn : (0:ℝ) ≤ ‖LSeries (fun _ => (1:ℂ))
      (((1 + 1/Real.log y : ℝ) : ℂ) - Complex.I * u)‖ := norm_nonneg _
  have hlogL : Real.log ‖LSeries (fun _ => (1:ℂ))
        (((1 + 1/Real.log y : ℝ) : ℂ) - Complex.I * u)‖
      ≤ Real.log (8192 * Real.log (|u| + 2)
          / Real.log (Real.log (|u| + 2))) := by
    rcases eq_or_lt_of_le hnn with h0 | h0
    · rw [← h0, Real.log_zero]
      apply Real.log_nonneg
      rw [le_div_iff₀ hB0]
      have hBA : Real.log (Real.log (|u| + 2)) ≤ Real.log (|u| + 2) := by
        have := Real.log_le_sub_one_of_pos hA0
        linarith
      nlinarith
    · exact Real.log_le_log h0 hzeta
  have hexpand : Real.log (8192 * Real.log (|u| + 2)
        / Real.log (Real.log (|u| + 2)))
      = Real.log 8192 + Real.log (Real.log (|u| + 2))
        - Real.log (Real.log (Real.log (|u| + 2))) := by
    rw [Real.log_div (by positivity) hB0.ne', Real.log_mul (by norm_num) hA0.ne']
  have h8192 : Real.log 8192 ≤ 10 := by
    rw [show (8192:ℝ) = 2^13 from by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    linarith
  -- split and close
  have hsplit : ∑ p ∈ y.primesBelow, (1 - Real.cos (u * Real.log p))/p
      = (∑ p ∈ y.primesBelow, (1:ℝ)/p)
        - ∑ p ∈ y.primesBelow, Real.cos (u * Real.log p)/p := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsplit]
  linarith [hbridge, hlogL, hexpand, h8192, hlogB_low]

end MoltResearch
