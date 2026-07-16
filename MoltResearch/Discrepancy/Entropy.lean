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

section Joint

variable {α β : Type*} [Fintype α] [Fintype β]

/-- First marginal of a joint distribution on `α × β`. -/
noncomputable def marginal₁ (w : α × β → ℝ) : α → ℝ :=
  fun a => ∑ b, w (a, b)

/-- Second marginal of a joint distribution on `α × β`. -/
noncomputable def marginal₂ (w : α × β → ℝ) : β → ℝ :=
  fun b => ∑ a, w (a, b)

theorem marginal₁_nonneg {w : α × β → ℝ} (hw0 : ∀ x, 0 ≤ w x) (a : α) :
    0 ≤ marginal₁ w a :=
  Finset.sum_nonneg fun b _ => hw0 (a, b)

theorem marginal₂_nonneg {w : α × β → ℝ} (hw0 : ∀ x, 0 ≤ w x) (b : β) :
    0 ≤ marginal₂ w b :=
  Finset.sum_nonneg fun a _ => hw0 (a, b)

theorem sum_marginal₁ {w : α × β → ℝ} (hsum : ∑ x, w x = 1) :
    ∑ a, marginal₁ w a = 1 := by
  rw [← hsum, Fintype.sum_prod_type]
  rfl

theorem sum_marginal₂ {w : α × β → ℝ} (hsum : ∑ x, w x = 1) :
    ∑ b, marginal₂ w b = 1 := by
  rw [← hsum, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- The joint weight is dominated by each marginal. -/
theorem le_marginal₁ {w : α × β → ℝ} (hw0 : ∀ x, 0 ≤ w x) (a : α) (b : β) :
    w (a, b) ≤ marginal₁ w a :=
  Finset.single_le_sum (f := fun b => w (a, b)) (fun b _ => hw0 (a, b))
    (Finset.mem_univ b)

theorem le_marginal₂ {w : α × β → ℝ} (hw0 : ∀ x, 0 ≤ w x) (a : α) (b : β) :
    w (a, b) ≤ marginal₂ w b :=
  Finset.single_le_sum (f := fun a => w (a, b)) (fun a _ => hw0 (a, b))
    (Finset.mem_univ a)

/-- **Subadditivity of Shannon entropy** (eq. (subadd) of arXiv:1509.05422 §3):
`H(X,Y) ≤ H(X) + H(Y)`, by the finite Gibbs inequality (`log t ≤ t − 1`, no Jensen
needed). -/
theorem shannonEntropy_le_add_marginals {w : α × β → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    (hsum : ∑ x, w x = 1) :
    shannonEntropy w
      ≤ shannonEntropy (marginal₁ w) + shannonEntropy (marginal₂ w) := by
  classical
  -- distribute the marginal entropies over the joint weights
  have hm1 : shannonEntropy (marginal₁ w)
      = ∑ x : α × β, -(w x * Real.log (marginal₁ w x.1)) := by
    rw [shannonEntropy, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    calc Real.negMulLog (marginal₁ w a)
        = -((∑ b, w (a, b)) * Real.log (marginal₁ w a)) := by
          rw [Real.negMulLog, neg_mul]
          rfl
      _ = ∑ b, -(w (a, b) * Real.log (marginal₁ w a)) := by
          rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  have hm2 : shannonEntropy (marginal₂ w)
      = ∑ x : α × β, -(w x * Real.log (marginal₂ w x.2)) := by
    rw [shannonEntropy, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    calc Real.negMulLog (marginal₂ w b)
        = -((∑ a, w (a, b)) * Real.log (marginal₂ w b)) := by
          rw [Real.negMulLog, neg_mul]
          rfl
      _ = ∑ a, -(w (a, b) * Real.log (marginal₂ w b)) := by
          rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  -- reduce to the Gibbs sum over the support
  rw [hm1, hm2, shannonEntropy]
  rw [← sub_nonneg, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  set S : Finset (α × β) := Finset.univ.filter (fun x => w x ≠ 0) with hS
  have hterm0 : ∀ x ∈ (Finset.univ : Finset (α × β)), x ∉ S →
      -(w x * Real.log (marginal₁ w x.1)) + -(w x * Real.log (marginal₂ w x.2))
        - Real.negMulLog (w x) = 0 := by
    intro x _ hx
    rw [hS, Finset.mem_filter] at hx
    push_neg at hx
    have h0 : w x = 0 := hx (Finset.mem_univ x)
    rw [h0]
    simp [Real.negMulLog_zero]
  rw [← Finset.sum_subset (Finset.subset_univ S) hterm0]
  -- per-term: w·log(m₁·m₂/w) bounded by m₁·m₂ − w via log t ≤ t − 1
  have hpos : ∀ x ∈ S, 0 < w x := by
    intro x hx
    rw [hS, Finset.mem_filter] at hx
    exact lt_of_le_of_ne (hw0 x) (Ne.symm hx.2)
  have hkey : ∀ x ∈ S,
      w x - marginal₁ w x.1 * marginal₂ w x.2
        ≤ -(w x * Real.log (marginal₁ w x.1)) + -(w x * Real.log (marginal₂ w x.2))
          - Real.negMulLog (w x) := by
    intro x hx
    have hw := hpos x hx
    have hm1p : 0 < marginal₁ w x.1 := lt_of_lt_of_le hw (le_marginal₁ hw0 x.1 x.2)
    have hm2p : 0 < marginal₂ w x.2 := lt_of_lt_of_le hw (le_marginal₂ hw0 x.1 x.2)
    have hlog := Real.log_le_sub_one_of_pos
      (show 0 < marginal₁ w x.1 * marginal₂ w x.2 / w x by positivity)
    have hexpand : Real.log (marginal₁ w x.1 * marginal₂ w x.2 / w x)
        = Real.log (marginal₁ w x.1) + Real.log (marginal₂ w x.2)
          - Real.log (w x) := by
      rw [Real.log_div (by positivity) (ne_of_gt hw),
        Real.log_mul (ne_of_gt hm1p) (ne_of_gt hm2p)]
    rw [hexpand] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hw.le
    have hdiv : w x * (marginal₁ w x.1 * marginal₂ w x.2 / w x - 1)
        = marginal₁ w x.1 * marginal₂ w x.2 - w x := by
      field_simp
    have hexp2 : w x * (Real.log (marginal₁ w x.1) + Real.log (marginal₂ w x.2)
          - Real.log (w x))
        = w x * Real.log (marginal₁ w x.1) + w x * Real.log (marginal₂ w x.2)
          - w x * Real.log (w x) := by ring
    have hneg : Real.negMulLog (w x) = -(w x * Real.log (w x)) := by
      rw [Real.negMulLog, neg_mul]
    rw [hdiv, hexp2] at hmul
    rw [hneg]
    linarith
  -- sum the per-term bounds; the product marginals sum to at most 1
  have hsum_ge : ∑ x ∈ S, (w x - marginal₁ w x.1 * marginal₂ w x.2)
      ≤ ∑ x ∈ S,
        (-(w x * Real.log (marginal₁ w x.1)) + -(w x * Real.log (marginal₂ w x.2))
          - Real.negMulLog (w x)) :=
    Finset.sum_le_sum fun x hx => hkey x hx
  have hprod_le : ∑ x ∈ S, marginal₁ w x.1 * marginal₂ w x.2 ≤ 1 := by
    have h1 : ∑ x ∈ S, marginal₁ w x.1 * marginal₂ w x.2
        ≤ ∑ x : α × β, marginal₁ w x.1 * marginal₂ w x.2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        fun x _ _ => ?_
      have := marginal₁_nonneg hw0 x.1
      have := marginal₂_nonneg hw0 x.2
      positivity
    have h2 : ∑ x : α × β, marginal₁ w x.1 * marginal₂ w x.2 = 1 := by
      rw [Fintype.sum_prod_type]
      rw [show ∑ a, ∑ b, marginal₁ w a * marginal₂ w b
          = (∑ a, marginal₁ w a) * (∑ b, marginal₂ w b) from by
        rw [Finset.sum_mul_sum]]
      rw [sum_marginal₁ hsum, sum_marginal₂ hsum, one_mul]
    linarith
  have h3 : ∑ x ∈ S, w x = 1 := by
    rw [hS, Finset.sum_filter_ne_zero]
    exact hsum
  have h0 : (0 : ℝ) ≤ ∑ x ∈ S, (w x - marginal₁ w x.1 * marginal₂ w x.2) := by
    rw [Finset.sum_sub_distrib, h3]
    linarith
  linarith [hsum_ge, h0]

/-- **Conditional entropy** `H(X|Y)`, defined through the chain rule
(eq. (haxy) of arXiv:1509.05422 §3): `H(X|Y) = H(X,Y) − H(Y)`. -/
noncomputable def condEntropy (w : α × β → ℝ) : ℝ :=
  shannonEntropy w - shannonEntropy (marginal₂ w)

/-- The chain rule `H(X,Y) = H(X|Y) + H(Y)` — definitional. -/
theorem shannonEntropy_eq_condEntropy_add (w : α × β → ℝ) :
    shannonEntropy w = condEntropy w + shannonEntropy (marginal₂ w) := by
  rw [condEntropy]
  ring

/-- **Conditioning reduces entropy** (eq. (hyx) of arXiv:1509.05422 §3):
`H(X|Y) ≤ H(X)`. -/
theorem condEntropy_le_shannonEntropy_marginal₁ {w : α × β → ℝ}
    (hw0 : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1) :
    condEntropy w ≤ shannonEntropy (marginal₁ w) := by
  have := shannonEntropy_le_add_marginals hw0 hsum
  rw [condEntropy]
  linarith

/-- **Mutual information** `I(X;Y) = H(X) + H(Y) − H(X,Y)`
(eq. (mutual) of arXiv:1509.05422 §3). -/
noncomputable def mutualInfo (w : α × β → ℝ) : ℝ :=
  shannonEntropy (marginal₁ w) + shannonEntropy (marginal₂ w) - shannonEntropy w

/-- Mutual information is nonnegative. -/
theorem mutualInfo_nonneg {w : α × β → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    (hsum : ∑ x, w x = 1) : 0 ≤ mutualInfo w := by
  have := shannonEntropy_le_add_marginals hw0 hsum
  rw [mutualInfo]
  linarith

/-- Mutual information as an entropy drop: `I(X;Y) = H(X) − H(X|Y)` (up to the
symmetric pairing). -/
theorem mutualInfo_eq_sub_condEntropy (w : α × β → ℝ) :
    mutualInfo w = shannonEntropy (marginal₁ w) - condEntropy w := by
  rw [mutualInfo, condEntropy]
  ring

end Joint

section Fibers

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The conditional distribution on the fiber over `b` (junk `0` off the support of
the conditioning marginal). -/
noncomputable def fiber (w : α × β → ℝ) (b : β) : α → ℝ :=
  fun a => if marginal₂ w b = 0 then 0 else w (a, b) / marginal₂ w b

theorem fiber_nonneg {w : α × β → ℝ} (hw0 : ∀ x, 0 ≤ w x) (b : β) (a : α) :
    0 ≤ fiber w b a := by
  rw [show fiber w b a
      = if marginal₂ w b = 0 then 0 else w (a, b) / marginal₂ w b from rfl]
  split_ifs with h
  · exact le_refl 0
  · have hm : 0 < marginal₂ w b :=
      lt_of_le_of_ne (marginal₂_nonneg hw0 b) (Ne.symm h)
    have := hw0 (a, b)
    positivity

theorem sum_fiber {w : α × β → ℝ} {b : β} (hb : marginal₂ w b ≠ 0) :
    ∑ a, fiber w b a = 1 := by
  have hfe : ∀ a, fiber w b a = w (a, b) / marginal₂ w b := fun a => by
    rw [show fiber w b a
        = if marginal₂ w b = 0 then 0 else w (a, b) / marginal₂ w b from rfl,
      if_neg hb]
  rw [Finset.sum_congr rfl fun a _ => hfe a,
    Finset.sum_congr rfl fun a _ => div_eq_mul_inv (w (a, b)) _, ← Finset.sum_mul,
    ← div_eq_mul_inv]
  exact div_self hb

/-- The joint weight recombines from the fiber and the conditioning marginal. -/
theorem fiber_mul {w : α × β → ℝ} (hw0 : ∀ x, 0 ≤ w x) (a : α) (b : β) :
    marginal₂ w b * fiber w b a = w (a, b) := by
  rw [show fiber w b a
      = if marginal₂ w b = 0 then 0 else w (a, b) / marginal₂ w b from rfl]
  split_ifs with h
  · rw [mul_zero]
    have h1 := le_marginal₂ hw0 a b
    have h2 := hw0 (a, b)
    rw [h] at h1
    linarith
  · field_simp

/-- **The fiber decomposition of conditional entropy** (eq. (xy) of arXiv:1509.05422
§3): `H(X|Y) = ∑_y P(Y=y)·H(X | Y=y)`. -/
theorem condEntropy_eq_sum_fiber {w : α × β → ℝ} (hw0 : ∀ x, 0 ≤ w x) :
    condEntropy w = ∑ b, marginal₂ w b * shannonEntropy (fiber w b) := by
  rw [condEntropy]
  have hjoint : shannonEntropy w
      = shannonEntropy (marginal₂ w)
        + ∑ b, marginal₂ w b * shannonEntropy (fiber w b) := by
    have hL : shannonEntropy w = ∑ b, ∑ a, Real.negMulLog (w (a, b)) := by
      rw [shannonEntropy, Fintype.sum_prod_type, Finset.sum_comm]
    rw [hL]
    have hper : ∀ b, ∑ a, Real.negMulLog (w (a, b))
        = Real.negMulLog (marginal₂ w b)
          + marginal₂ w b * shannonEntropy (fiber w b) := by
      intro b
      have hsplit : ∀ a, Real.negMulLog (w (a, b))
          = fiber w b a * Real.negMulLog (marginal₂ w b)
            + marginal₂ w b * Real.negMulLog (fiber w b a) := by
        intro a
        rw [← fiber_mul hw0 a b, Real.negMulLog_mul]
      rw [Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_add_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum]
      by_cases hb : marginal₂ w b = 0
      · rw [hb]
        have hfz : ∀ a, fiber w b a = 0 := fun a => by
          rw [show fiber w b a
              = if marginal₂ w b = 0 then 0 else w (a, b) / marginal₂ w b from rfl,
            if_pos hb]
        rw [Finset.sum_congr rfl fun a _ => hfz a]
        simp [Real.negMulLog_zero]
      · rw [sum_fiber hb, one_mul, shannonEntropy]
    rw [Finset.sum_congr rfl fun b _ => hper b, Finset.sum_add_distrib]
    rfl
  rw [hjoint]
  ring

end Fibers

section Relative

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- The `(α, γ)`-marginal of a triple distribution on `(α × β) × γ`. -/
noncomputable def margAC (w : (α × β) × γ → ℝ) : α × γ → ℝ :=
  fun x => ∑ b, w ((x.1, b), x.2)

/-- The `(β, γ)`-marginal of a triple distribution on `(α × β) × γ`. -/
noncomputable def margBC (w : (α × β) × γ → ℝ) : β × γ → ℝ :=
  fun x => ∑ a, w ((a, x.1), x.2)

theorem margAC_nonneg {w : (α × β) × γ → ℝ} (hw0 : ∀ x, 0 ≤ w x) (x : α × γ) :
    0 ≤ margAC w x :=
  Finset.sum_nonneg fun b _ => hw0 ((x.1, b), x.2)

theorem margBC_nonneg {w : (α × β) × γ → ℝ} (hw0 : ∀ x, 0 ≤ w x) (x : β × γ) :
    0 ≤ margBC w x :=
  Finset.sum_nonneg fun a _ => hw0 ((a, x.1), x.2)

/-- The conditioning marginals of the projected distributions agree with the original. -/
theorem marginal₂_margAC (w : (α × β) × γ → ℝ) (c : γ) :
    marginal₂ (margAC w) c = marginal₂ w c := by
  show ∑ a, ∑ b, w ((a, b), c) = ∑ x : α × β, w (x, c)
  rw [Fintype.sum_prod_type]

theorem marginal₂_margBC (w : (α × β) × γ → ℝ) (c : γ) :
    marginal₂ (margBC w) c = marginal₂ w c := by
  show ∑ b, ∑ a, w ((a, b), c) = ∑ x : α × β, w (x, c)
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- Marginalizing the fiber is the fiber of the marginal. -/
theorem marginal₁_fiber (w : (α × β) × γ → ℝ) (c : γ) :
    marginal₁ (fiber w c) = fiber (margAC w) c := by
  funext a
  show ∑ b, fiber w c (a, b) = fiber (margAC w) c a
  rw [show fiber (margAC w) c a
      = if marginal₂ (margAC w) c = 0 then 0
        else margAC w (a, c) / marginal₂ (margAC w) c from rfl,
    marginal₂_margAC]
  by_cases hc : marginal₂ w c = 0
  · rw [if_pos hc]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [show fiber w c (a, b)
        = if marginal₂ w c = 0 then 0 else w ((a, b), c) / marginal₂ w c from rfl,
      if_pos hc]
  · rw [if_neg hc]
    rw [Finset.sum_congr rfl fun b _ => show fiber w c (a, b)
        = w ((a, b), c) / marginal₂ w c from by
      rw [show fiber w c (a, b)
          = if marginal₂ w c = 0 then 0 else w ((a, b), c) / marginal₂ w c from rfl,
        if_neg hc]]
    rw [Finset.sum_congr rfl fun b _ => div_eq_mul_inv (w ((a, b), c)) _,
      ← Finset.sum_mul, ← div_eq_mul_inv]
    rfl

theorem marginal₂_fiber (w : (α × β) × γ → ℝ) (c : γ) :
    marginal₂ (fiber w c) = fiber (margBC w) c := by
  funext b
  show ∑ a, fiber w c (a, b) = fiber (margBC w) c b
  rw [show fiber (margBC w) c b
      = if marginal₂ (margBC w) c = 0 then 0
        else margBC w (b, c) / marginal₂ (margBC w) c from rfl,
    marginal₂_margBC]
  by_cases hc : marginal₂ w c = 0
  · rw [if_pos hc]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [show fiber w c (a, b)
        = if marginal₂ w c = 0 then 0 else w ((a, b), c) / marginal₂ w c from rfl,
      if_pos hc]
  · rw [if_neg hc]
    rw [Finset.sum_congr rfl fun a _ => show fiber w c (a, b)
        = w ((a, b), c) / marginal₂ w c from by
      rw [show fiber w c (a, b)
          = if marginal₂ w c = 0 then 0 else w ((a, b), c) / marginal₂ w c from rfl,
        if_neg hc]]
    rw [Finset.sum_congr rfl fun a _ => div_eq_mul_inv (w ((a, b), c)) _,
      ← Finset.sum_mul, ← div_eq_mul_inv]
    rfl

/-- **Relative subadditivity of entropy** (eq. (subadd-rel) of arXiv:1509.05422 §3,
= submodularity): `H(X,Y|Z) ≤ H(X|Z) + H(Y|Z)` — per-fiber subadditivity, averaged
over the conditioning variable. -/
theorem condEntropy_le_add_condEntropy {w : (α × β) × γ → ℝ} (hw0 : ∀ x, 0 ≤ w x) :
    condEntropy w ≤ condEntropy (margAC w) + condEntropy (margBC w) := by
  rw [condEntropy_eq_sum_fiber hw0, condEntropy_eq_sum_fiber (margAC_nonneg hw0),
    condEntropy_eq_sum_fiber (margBC_nonneg hw0)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [marginal₂_margAC, marginal₂_margBC, ← marginal₁_fiber, ← marginal₂_fiber]
  by_cases hc : marginal₂ w c = 0
  · rw [hc]
    ring_nf
    exact le_refl 0
  · have hm : 0 < marginal₂ w c :=
      lt_of_le_of_ne (Finset.sum_nonneg fun x _ => hw0 (x, c)) (Ne.symm hc)
    have hsub := shannonEntropy_le_add_marginals
      (w := fiber w c) (fiber_nonneg hw0 c) (sum_fiber hc)
    nlinarith [hsub, hm]

end Relative

end MoltResearch
