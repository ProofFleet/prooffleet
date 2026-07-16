import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Discrepancy: Shannon entropy of finite discrete distributions

Track C, Elliott campaign (`Problems/tao2015_derivation_c.md`, issue #2946, E1a): the
entropy layer that the entropy decrement argument (arXiv:1509.05422 §3) rests on,
starting from the bottom — the Shannon entropy of a finite discrete distribution,
presented as a weight function `w : α → ℝ` on a `Fintype` (nonnegative, summing to `1`).

* `shannonEntropy w = ∑ x, negMulLog (w x)` — zero-weight points contribute `0`, so the
  sum silently restricts to the support (the paper's "essential range" convention).
* `shannonEntropy_nonneg` — entropy is nonnegative.
* `shannonEntropy_le_log_card` — Jensen at the uniform distribution: `H ≤ log N` when
  the distribution takes at most `N = card α` values (eq. (jens) of the paper).

Joint/conditional entropy, the chain rule, subadditivity, and mutual information are
the next stages (E1b, E1c); Mathlib has no Shannon entropy of any form (only the scalar
`negMulLog`/`binEntropy` functions), so this small library is also an upstreaming
candidate.
-/

namespace MoltResearch

open Finset

variable {α : Type*} [Fintype α]

/-- The Shannon entropy of a finite discrete distribution, presented as a weight
function: `H(w) = ∑ x, −w x · log (w x)`. Zero-weight points contribute `0`
(`negMulLog 0 = 0`), matching the "essential range" convention. -/
noncomputable def shannonEntropy (w : α → ℝ) : ℝ :=
  ∑ x, Real.negMulLog (w x)

/-- Entropy is nonnegative for subprobability weights. -/
theorem shannonEntropy_nonneg {w : α → ℝ} (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) :
    0 ≤ shannonEntropy w :=
  Finset.sum_nonneg fun x _ => Real.negMulLog_nonneg (hw0 x) (hw1 x)

/-- Entropy vanishes on deterministic distributions (a point mass). -/
@[simp] theorem shannonEntropy_single [DecidableEq α] (x₀ : α) :
    shannonEntropy (fun x => if x = x₀ then (1 : ℝ) else 0) = 0 := by
  rw [shannonEntropy]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases h : x = x₀ <;> simp [h]

/-- **Jensen at the uniform distribution**: a distribution on `α` has entropy at most
`log (card α)` — eq. (jens) of arXiv:1509.05422 §3. -/
theorem shannonEntropy_le_log_card {w : α → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    (hsum : ∑ x, w x = 1) :
    shannonEntropy w ≤ Real.log (Fintype.card α) := by
  classical
  set S : Finset α := Finset.univ.filter (fun x => w x ≠ 0) with hS
  have hSsum : ∑ x ∈ S, w x = 1 := by
    rw [hS, Finset.sum_filter_ne_zero]
    exact hsum
  have hSpos : ∀ x ∈ S, 0 < w x := by
    intro x hx
    rw [hS, Finset.mem_filter] at hx
    exact lt_of_le_of_ne (hw0 x) (Ne.symm hx.2)
  -- restrict the entropy sum to the support and rewrite as an average of logs
  have hrestrict : shannonEntropy w = ∑ x ∈ S, w x • Real.log (w x)⁻¹ := by
    have hfilter : ∑ x ∈ S, Real.negMulLog (w x) = ∑ x, Real.negMulLog (w x) := by
      rw [hS]
      refine Finset.sum_filter_of_ne fun x _ h => ?_
      by_contra h0
      rw [h0] at h
      exact h Real.negMulLog_zero
    rw [shannonEntropy, ← hfilter]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx0 := hSpos x hx
    rw [Real.negMulLog, Real.log_inv, smul_eq_mul]
    ring
  rw [hrestrict]
  -- Jensen for the concave log
  have hmem : ∀ x ∈ S, (w x)⁻¹ ∈ Set.Ioi (0 : ℝ) := fun x hx =>
    Set.mem_Ioi.mpr (by have := hSpos x hx; positivity)
  have hjensen := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum
    (fun x hx => (hSpos x hx).le) hSsum hmem
  have hinner : ∑ x ∈ S, w x • (w x)⁻¹ = (S.card : ℝ) := by
    rw [show ∑ x ∈ S, w x • (w x)⁻¹ = ∑ _x ∈ S, (1 : ℝ) from
      Finset.sum_congr rfl fun x hx => by
        rw [smul_eq_mul, mul_inv_cancel₀ (ne_of_gt (hSpos x hx))]]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hinner] at hjensen
  refine le_trans hjensen (Real.log_le_log ?_ ?_)
  · have hne : S.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h, Finset.sum_empty] at hSsum
      norm_num at hSsum
    exact_mod_cast Finset.card_pos.mpr hne
  · exact_mod_cast Finset.card_le_univ S

end MoltResearch
