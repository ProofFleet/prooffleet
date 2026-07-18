import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

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

/-- Shannon entropy is invariant under relabeling the alphabet. -/
theorem shannonEntropy_comp_equiv {β : Type*} [Fintype β] (v : α → ℝ) (e : β ≃ α) :
    shannonEntropy (fun b => v (e b)) = shannonEntropy v := by
  rw [shannonEntropy, shannonEntropy]
  exact Fintype.sum_equiv e _ _ fun b => rfl

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

section Events

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Support-refined Jensen**: a distribution vanishing off `E` has entropy at most
`log |E|`. -/
theorem shannonEntropy_le_log_card_of_support {w : α → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    (hsum : ∑ x, w x = 1) {E : Finset α} (hsupp : ∀ x ∉ E, w x = 0) :
    shannonEntropy w ≤ Real.log E.card := by
  classical
  set S : Finset α := Finset.univ.filter (fun x => w x ≠ 0) with hS
  have hSE : S ⊆ E := by
    intro x hx
    rw [hS, Finset.mem_filter] at hx
    by_contra hxE
    exact hx.2 (hsupp x hxE)
  have hSsum : ∑ x ∈ S, w x = 1 := by
    rw [hS, Finset.sum_filter_ne_zero]
    exact hsum
  have hSpos : ∀ x ∈ S, 0 < w x := by
    intro x hx
    rw [hS, Finset.mem_filter] at hx
    exact lt_of_le_of_ne (hw0 x) (Ne.symm hx.2)
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
  · exact_mod_cast Finset.card_le_card hSE

/-- The event-restricted renormalization (junk `0` at zero mass and off the event). -/
noncomputable def eventCond (v : α → ℝ) (E : Finset α) : α → ℝ :=
  fun y => if y ∈ E then v y / (∑ z ∈ E, v z) else 0

/-- **Entropy forces spread** (the core of arXiv:1509.05422 §3, Lemma weak-unif):
splitting a distribution across an event `E` costs at most one bit, so
`H(v) ≤ log 2 + P(E)·log|E| + (1 − P(E))·log|univ|`. Rearranged, high entropy forces
small mass on small events. -/
theorem shannonEntropy_le_event_split {v : α → ℝ} (hv0 : ∀ x, 0 ≤ v x)
    (hsum : ∑ x, v x = 1) (E : Finset α) :
    shannonEntropy v
      ≤ Real.log 2 + (∑ y ∈ E, v y) * Real.log E.card
        + (1 - ∑ y ∈ E, v y) * Real.log (Fintype.card α) := by
  classical
  set q : ℝ := ∑ y ∈ E, v y with hq
  have hq0 : 0 ≤ q := Finset.sum_nonneg fun y _ => hv0 y
  have hq1 : q ≤ 1 := by
    rw [hq, ← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
      fun y _ _ => hv0 y
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogcard : shannonEntropy v ≤ Real.log (Fintype.card α) :=
    shannonEntropy_le_log_card hv0 hsum
  have hlogcard0 : (0 : ℝ) ≤ Real.log (Fintype.card α) := by
    have hne : (Finset.univ : Finset α).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [show ∑ x, v x = ∑ x ∈ (Finset.univ : Finset α), v x from rfl, h,
        Finset.sum_empty] at hsum
      norm_num at hsum
    have hcard : 1 ≤ Fintype.card α := Finset.card_pos.mpr hne
    exact Real.log_nonneg (by exact_mod_cast hcard)
  -- degenerate masses: fall back to the coarse bound
  rcases eq_or_lt_of_le hq0 with hq0' | hq0'
  · -- q = 0
    rw [← hq0']
    have : (1 - (0:ℝ)) * Real.log (Fintype.card α) = Real.log (Fintype.card α) := by ring
    rw [zero_mul, this]
    linarith
  rcases eq_or_lt_of_le hq1 with hq1' | hq1'
  · -- q = 1: v is supported in E
    have hsupp : ∀ y ∉ E, v y = 0 := by
      intro y hyE
      by_contra hne
      have hpos : 0 < v y := lt_of_le_of_ne (hv0 y) (Ne.symm hne)
      have hsplit : ∑ x, v x = q + ∑ y ∈ Finset.univ \ E, v y := by
        rw [hq, ← Finset.sum_sdiff (Finset.subset_univ E)]
        ring
      have hin : v y ≤ ∑ y ∈ Finset.univ \ E, v y :=
        Finset.single_le_sum (f := v) (fun z _ => hv0 z)
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hyE⟩)
      rw [hsum, ← hq1'] at hsplit
      linarith
    have hE := shannonEntropy_le_log_card_of_support hv0 hsum hsupp
    rw [hq1', sub_self, zero_mul, one_mul, add_zero]
    linarith
  -- interior case: the exact decomposition through the two restrictions
  have hqne : q ≠ 0 := ne_of_gt hq0'
  have hq1ne : 1 - q ≠ 0 := by
    intro h
    have hq1'' : q = 1 := by linarith
    exact absurd hq1'' (ne_of_lt hq1')
  set r : α → ℝ := eventCond v E with hr
  set r' : α → ℝ := eventCond v (Finset.univ \ E) with hr'
  have hmassE : ∑ z ∈ Finset.univ \ E, v z = 1 - q := by
    have h0 : ∑ z ∈ Finset.univ \ E, v z + ∑ z ∈ E, v z = ∑ z, v z :=
      Finset.sum_sdiff (Finset.subset_univ E)
    rw [hsum] at h0
    linarith
  -- decomposition of the E-part
  have hpartE : ∑ y ∈ E, Real.negMulLog (v y)
      = Real.negMulLog q + q * shannonEntropy r := by
    have hvy : ∀ y ∈ E, v y = q * r y := by
      intro y hy
      rw [hr, show eventCond v E y = if y ∈ E then v y / (∑ z ∈ E, v z) else 0 from rfl,
        if_pos hy, ← hq]
      field_simp
    have hsplit : ∀ y ∈ E, Real.negMulLog (v y)
        = r y * Real.negMulLog q + q * Real.negMulLog (r y) := by
      intro y hy
      rw [hvy y hy, Real.negMulLog_mul]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum]
    have hrsum : ∑ y ∈ E, r y = 1 := by
      have : ∀ y ∈ E, r y = v y / q := fun y hy => by
        rw [hr, show eventCond v E y
            = if y ∈ E then v y / (∑ z ∈ E, v z) else 0 from rfl, if_pos hy, ← hq]
      rw [Finset.sum_congr rfl this,
        Finset.sum_congr rfl fun y _ => div_eq_mul_inv (v y) q, ← Finset.sum_mul,
        ← hq, ← div_eq_mul_inv]
      exact div_self hqne
    have hHr : ∑ y ∈ E, Real.negMulLog (r y) = shannonEntropy r := by
      rw [shannonEntropy]
      refine Finset.sum_subset (Finset.subset_univ E) fun y _ hyE => ?_
      rw [hr, show eventCond v E y
          = if y ∈ E then v y / (∑ z ∈ E, v z) else 0 from rfl, if_neg hyE]
      exact Real.negMulLog_zero
    rw [hrsum, hHr, one_mul]
  -- decomposition of the complement part
  have hpartEc : ∑ y ∈ Finset.univ \ E, Real.negMulLog (v y)
      = Real.negMulLog (1 - q) + (1 - q) * shannonEntropy r' := by
    have hvy : ∀ y ∈ Finset.univ \ E, v y = (1 - q) * r' y := by
      intro y hy
      rw [hr', show eventCond v (Finset.univ \ E) y
          = if y ∈ Finset.univ \ E then v y / (∑ z ∈ Finset.univ \ E, v z) else 0
        from rfl, if_pos hy, hmassE]
      field_simp
    have hsplit : ∀ y ∈ Finset.univ \ E, Real.negMulLog (v y)
        = r' y * Real.negMulLog (1 - q) + (1 - q) * Real.negMulLog (r' y) := by
      intro y hy
      rw [hvy y hy, Real.negMulLog_mul]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum]
    have hrsum : ∑ y ∈ Finset.univ \ E, r' y = 1 := by
      have hthis : ∀ y ∈ Finset.univ \ E, r' y = v y / (1 - q) := fun y hy => by
        rw [hr', show eventCond v (Finset.univ \ E) y
            = if y ∈ Finset.univ \ E then v y / (∑ z ∈ Finset.univ \ E, v z) else 0
          from rfl, if_pos hy, hmassE]
      rw [Finset.sum_congr rfl hthis,
        Finset.sum_congr rfl fun y _ => div_eq_mul_inv (v y) (1 - q), ← Finset.sum_mul,
        hmassE, ← div_eq_mul_inv]
      exact div_self hq1ne
    have hHr : ∑ y ∈ Finset.univ \ E, Real.negMulLog (r' y) = shannonEntropy r' := by
      rw [shannonEntropy]
      refine Finset.sum_subset (Finset.subset_univ _) fun y _ hyE => ?_
      rw [hr', show eventCond v (Finset.univ \ E) y
          = if y ∈ Finset.univ \ E then v y / (∑ z ∈ Finset.univ \ E, v z) else 0
        from rfl, if_neg hyE]
      exact Real.negMulLog_zero
    rw [hrsum, hHr, one_mul]
  -- assemble: H(v) = binary entropy + mixture of restricted entropies
  have hHv : shannonEntropy v
      = (Real.negMulLog q + Real.negMulLog (1 - q))
        + (q * shannonEntropy r + (1 - q) * shannonEntropy r') := by
    rw [shannonEntropy, ← Finset.sum_sdiff (Finset.subset_univ E) (f := fun y =>
      Real.negMulLog (v y)), hpartE, hpartEc]
    ring
  -- binary entropy is at most log 2
  have hbin : Real.negMulLog q + Real.negMulLog (1 - q) ≤ Real.log 2 := by
    have := Real.binEntropy_le_log_two (p := q)
    rwa [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub] at this
  -- restricted entropies against their supports
  have hr0 : ∀ y, 0 ≤ r y := by
    intro y
    rw [hr, show eventCond v E y = if y ∈ E then v y / (∑ z ∈ E, v z) else 0 from rfl]
    split_ifs with h
    · rw [← hq]
      have := hv0 y
      positivity
    · exact le_refl 0
  have hrsum1 : ∑ y, r y = 1 := by
    rw [show ∑ y, r y = ∑ y ∈ E, r y from (Finset.sum_subset (Finset.subset_univ E)
      fun y _ hyE => by
        rw [hr, show eventCond v E y
            = if y ∈ E then v y / (∑ z ∈ E, v z) else 0 from rfl, if_neg hyE]).symm]
    have hthis : ∀ y ∈ E, r y = v y / q := fun y hy => by
      rw [hr, show eventCond v E y
          = if y ∈ E then v y / (∑ z ∈ E, v z) else 0 from rfl, if_pos hy, ← hq]
    rw [Finset.sum_congr rfl hthis,
      Finset.sum_congr rfl fun y _ => div_eq_mul_inv (v y) q, ← Finset.sum_mul,
      ← hq, ← div_eq_mul_inv]
    exact div_self hqne
  have hHrE : shannonEntropy r ≤ Real.log E.card := by
    refine shannonEntropy_le_log_card_of_support hr0 hrsum1 fun y hyE => ?_
    rw [hr, show eventCond v E y = if y ∈ E then v y / (∑ z ∈ E, v z) else 0 from rfl,
      if_neg hyE]
  have hr'0 : ∀ y, 0 ≤ r' y := by
    intro y
    rw [hr', show eventCond v (Finset.univ \ E) y
        = if y ∈ Finset.univ \ E then v y / (∑ z ∈ Finset.univ \ E, v z) else 0
      from rfl]
    split_ifs with h
    · rw [hmassE]
      exact div_nonneg (hv0 y) (by linarith)
    · exact le_refl 0
  have hr'sum1 : ∑ y, r' y = 1 := by
    rw [show ∑ y, r' y = ∑ y ∈ Finset.univ \ E, r' y from
      (Finset.sum_subset (Finset.subset_univ _) fun y _ hyE => by
        rw [hr', show eventCond v (Finset.univ \ E) y
            = if y ∈ Finset.univ \ E then v y / (∑ z ∈ Finset.univ \ E, v z) else 0
          from rfl, if_neg hyE]).symm]
    have hthis : ∀ y ∈ Finset.univ \ E, r' y = v y / (1 - q) := fun y hy => by
      rw [hr', show eventCond v (Finset.univ \ E) y
          = if y ∈ Finset.univ \ E then v y / (∑ z ∈ Finset.univ \ E, v z) else 0
        from rfl, if_pos hy, hmassE]
    rw [Finset.sum_congr rfl hthis,
      Finset.sum_congr rfl fun y _ => div_eq_mul_inv (v y) (1 - q), ← Finset.sum_mul,
      hmassE, ← div_eq_mul_inv]
    exact div_self hq1ne
  have hHrEc : shannonEntropy r' ≤ Real.log (Fintype.card α) := by
    exact shannonEntropy_le_log_card hr'0 hr'sum1
  -- combine
  rw [hHv]
  have h1 : q * shannonEntropy r ≤ q * Real.log E.card :=
    mul_le_mul_of_nonneg_left hHrE hq0
  have h2 : (1 - q) * shannonEntropy r' ≤ (1 - q) * Real.log (Fintype.card α) :=
    mul_le_mul_of_nonneg_left hHrEc (by linarith)
  linarith

omit [DecidableEq α] in
/-- **Entropy floor from a pointwise mass bound**: if every point carries mass at
most `c`, the entropy is at least `−log c` — the mechanism by which near-uniformity
forces near-full entropy (eq. (hayah) of arXiv:1509.05422 §3). -/
theorem le_shannonEntropy_of_forall_le {w : α → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    (hsum : ∑ x, w x = 1) {c : ℝ} (hc : 0 < c) (hwc : ∀ x, w x ≤ c) :
    -Real.log c ≤ shannonEntropy w := by
  have hterm : ∀ x, w x * (-Real.log c) ≤ Real.negMulLog (w x) := by
    intro x
    rcases eq_or_lt_of_le (hw0 x) with h0 | h0
    · rw [← h0]
      simp [Real.negMulLog_zero]
    · rw [Real.negMulLog, neg_mul]
      have hlog : Real.log (w x) ≤ Real.log c := Real.log_le_log h0 (hwc x)
      nlinarith [hlog]
  calc -Real.log c = (∑ x, w x) * (-Real.log c) := by rw [hsum]; ring
    _ = ∑ x, w x * (-Real.log c) := by rw [Finset.sum_mul]
    _ ≤ ∑ x, Real.negMulLog (w x) := Finset.sum_le_sum fun x _ => hterm x
    _ = shannonEntropy w := rfl

/-- **Weak uniform distribution** (Lemma weak-unif of arXiv:1509.05422 §3): a
near-full-entropy law cannot concentrate on an exponentially small event — if
`H(v) ≥ log|α| − θ` and `log|E| ≤ log|α| − δ`, then `v(E) ≤ (θ + log 2)/δ`. -/
theorem sum_mem_le_of_le_shannonEntropy {v : α → ℝ} (hv0 : ∀ x, 0 ≤ v x)
    (hsum : ∑ x, v x = 1) (E : Finset α) {θ δ : ℝ} (hδ : 0 < δ)
    (hH : Real.log (Fintype.card α) - θ ≤ shannonEntropy v)
    (hE : Real.log E.card ≤ Real.log (Fintype.card α) - δ) :
    ∑ y ∈ E, v y ≤ (θ + Real.log 2) / δ := by
  have hsplit := shannonEntropy_le_event_split hv0 hsum E
  have hq0 : 0 ≤ ∑ y ∈ E, v y := Finset.sum_nonneg fun y _ => hv0 y
  have hring : (∑ y ∈ E, v y)
      * (Real.log (Fintype.card α) - Real.log E.card)
      = (∑ y ∈ E, v y) * Real.log (Fintype.card α)
        - (∑ y ∈ E, v y) * Real.log E.card := by
    ring
  have h1 : (∑ y ∈ E, v y)
      * (Real.log (Fintype.card α) - Real.log E.card)
      ≤ θ + Real.log 2 := by
    rw [hring]
    nlinarith [hsplit, hH]
  have h2 : δ ≤ Real.log (Fintype.card α) - Real.log E.card := by linarith
  have hkey : (∑ y ∈ E, v y) * δ ≤ θ + Real.log 2 :=
    le_trans (mul_le_mul_of_nonneg_left h2 hq0) h1
  exact (le_div_iff₀ hδ).mpr hkey

end Events

section TV

variable {α : Type*} [Fintype α]

/-- Total-variation distance between two finite weight functions. -/
noncomputable def tvDist (v w : α → ℝ) : ℝ :=
  ∑ x, |v x - w x|

theorem tvDist_nonneg (v w : α → ℝ) : 0 ≤ tvDist v w :=
  Finset.sum_nonneg fun x _ => abs_nonneg _

theorem tvDist_comm (v w : α → ℝ) : tvDist v w = tvDist w v := by
  rw [tvDist, tvDist]
  exact Finset.sum_congr rfl fun x _ => abs_sub_comm _ _

/-! Fannes-type continuity: Shannon entropy is continuous in total variation, with
the elementary modulus `2·|α|·√T + T`. This is weaker than the sharp Fannes
inequality but suffices for the entropy decrement, where the pattern alphabet is
fixed while the total variation tends to zero. -/

theorem negMulLog_le_two_mul_sqrt {a : ℝ} (ha : 0 ≤ a) :
    Real.negMulLog a ≤ 2 * Real.sqrt a := by
  rcases ha.eq_or_lt with h0 | h0
  · simp [← h0]
  · have hkey : Real.negMulLog a = 2 * a * Real.log (1 / Real.sqrt a) := by
      rw [one_div, Real.log_inv, Real.log_sqrt ha, Real.negMulLog]
      ring
    have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr h0
    have hlog : Real.log (1 / Real.sqrt a) ≤ 1 / Real.sqrt a - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    calc Real.negMulLog a = 2 * a * Real.log (1 / Real.sqrt a) := hkey
      _ ≤ 2 * a * (1 / Real.sqrt a - 1) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 2 * (a / Real.sqrt a) - 2 * a := by ring
      _ ≤ 2 * Real.sqrt a := by rw [Real.div_sqrt]; linarith

theorem negMulLog_add_le {a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) :
    Real.negMulLog (a + d) ≤ Real.negMulLog a + Real.negMulLog d := by
  have h1 : -(a * Real.log (a + d)) ≤ Real.negMulLog a := by
    rcases ha.eq_or_lt with h0 | h0
    · simp [← h0]
    · rw [Real.negMulLog, neg_mul]
      exact neg_le_neg (mul_le_mul_of_nonneg_left
        (Real.log_le_log h0 (by linarith)) ha)
  have h2 : -(d * Real.log (a + d)) ≤ Real.negMulLog d := by
    rcases hd.eq_or_lt with h0 | h0
    · simp [← h0]
    · rw [Real.negMulLog, neg_mul]
      exact neg_le_neg (mul_le_mul_of_nonneg_left
        (Real.log_le_log h0 (by linarith)) hd)
  have hsplit : Real.negMulLog (a + d)
      = -(a * Real.log (a + d)) + -(d * Real.log (a + d)) := by
    rw [Real.negMulLog]
    ring
  rw [hsplit]
  exact add_le_add h1 h2

theorem negMulLog_sub_le_of_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    Real.negMulLog a - Real.negMulLog b ≤ b - a := by
  rcases ha.eq_or_lt with h0 | h0
  · have hnn : 0 ≤ Real.negMulLog b :=
      Real.negMulLog_nonneg (by linarith) hb1
    rw [← h0, Real.negMulLog_zero]
    linarith
  · have hba : 0 < b := lt_of_lt_of_le h0 hab
    have hlog1 : Real.log b - Real.log a ≤ b / a - 1 := by
      have h := Real.log_le_sub_one_of_pos (show 0 < b / a by positivity)
      rwa [Real.log_div hba.ne' h0.ne'] at h
    have hterm1 : (b - a) * Real.log b ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith)
        (Real.log_nonpos (by linarith) hb1)
    have ha' : a ≠ 0 := h0.ne'
    have hcancel : a * (b / a - 1) = b - a := by
      field_simp
    have hterm2 : a * (Real.log b - Real.log a) ≤ b - a := by
      have h := mul_le_mul_of_nonneg_left hlog1 ha
      rw [hcancel] at h
      exact h
    have hid : b * Real.log b - a * Real.log a
        = (b - a) * Real.log b + a * (Real.log b - Real.log a) := by
      ring
    rw [Real.negMulLog, Real.negMulLog]
    nlinarith [hid, hterm1, hterm2]

theorem abs_negMulLog_sub_le_of_le {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hb1 : b ≤ 1) :
    |Real.negMulLog a - Real.negMulLog b| ≤ 2 * Real.sqrt (b - a) + (b - a) := by
  have hd0 : (0 : ℝ) ≤ b - a := by linarith
  have hs0 : 0 ≤ Real.sqrt (b - a) := Real.sqrt_nonneg _
  have hup : Real.negMulLog a - Real.negMulLog b ≤ b - a :=
    negMulLog_sub_le_of_le ha0 hab hb1
  have hdn : Real.negMulLog b - Real.negMulLog a ≤ 2 * Real.sqrt (b - a) := by
    have hsub := negMulLog_add_le ha0 hd0
    have heq : a + (b - a) = b := by ring
    rw [heq] at hsub
    have h2 := negMulLog_le_two_mul_sqrt hd0
    linarith
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

theorem abs_negMulLog_sub_le {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) :
    |Real.negMulLog a - Real.negMulLog b| ≤ 2 * Real.sqrt |a - b| + |a - b| := by
  rcases le_total a b with hab | hab
  · have hd0 : (0 : ℝ) ≤ b - a := by linarith
    rw [abs_sub_comm a b, abs_of_nonneg hd0]
    exact abs_negMulLog_sub_le_of_le ha0 hab hb1
  · have hd0 : (0 : ℝ) ≤ a - b := by linarith
    rw [abs_of_nonneg hd0, abs_sub_comm (Real.negMulLog a)]
    exact abs_negMulLog_sub_le_of_le hb0 hab ha1

/-- **Fannes-type continuity** of Shannon entropy in total variation:
`|H(v) − H(w)| ≤ 2·|α|·√(tvDist v w) + tvDist v w` for `[0,1]`-valued weights. -/
theorem abs_shannonEntropy_sub_le {v w : α → ℝ} (hv0 : ∀ x, 0 ≤ v x)
    (hv1 : ∀ x, v x ≤ 1) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1) :
    |shannonEntropy v - shannonEntropy w|
      ≤ 2 * (Fintype.card α : ℝ) * Real.sqrt (tvDist v w) + tvDist v w := by
  have hstep : |shannonEntropy v - shannonEntropy w|
      ≤ ∑ x, (2 * Real.sqrt |v x - w x| + |v x - w x|) := by
    rw [shannonEntropy, shannonEntropy, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum fun x _ =>
      abs_negMulLog_sub_le (hv0 x) (hv1 x) (hw0 x) (hw1 x)
  have hper : ∀ x : α, |v x - w x| ≤ tvDist v w := fun x =>
    Finset.single_le_sum (f := fun y => |v y - w y|)
      (fun y _ => abs_nonneg _) (Finset.mem_univ x)
  refine le_trans hstep ?_
  rw [Finset.sum_add_distrib]
  have h1 : ∑ x : α, 2 * Real.sqrt |v x - w x|
      ≤ (Fintype.card α : ℝ) * (2 * Real.sqrt (tvDist v w)) := by
    calc ∑ x : α, 2 * Real.sqrt |v x - w x|
        ≤ ∑ _x : α, 2 * Real.sqrt (tvDist v w) :=
          Finset.sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hper x)) (by norm_num)
      _ = (Fintype.card α : ℝ) * (2 * Real.sqrt (tvDist v w)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h2 : ∑ x : α, |v x - w x| = tvDist v w := rfl
  rw [h2]
  linarith

/-- `negMulLog` is superadditive on nonnegative families: `η(∑f) ≤ ∑η(f)`. -/
theorem negMulLog_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    Real.negMulLog (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Real.negMulLog (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 := negMulLog_add_le (hf a (Finset.mem_insert_self a t))
      (Finset.sum_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    linarith

/-- **Marginalizing loses entropy**: `H(X) ≤ H(X,Y)` for nonnegative weights. -/
theorem shannonEntropy_marginal₁_le {β : Type*} [Fintype β] {w : α × β → ℝ}
    (hw0 : ∀ x, 0 ≤ w x) :
    shannonEntropy (marginal₁ w) ≤ shannonEntropy w := by
  rw [shannonEntropy, shannonEntropy, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun a _ => ?_
  exact negMulLog_sum_le Finset.univ (fun b => w (a, b)) fun b _ => hw0 (a, b)

end TV

section Pigeonhole

/-- **Average pigeonhole**: if `N` nonnegative terms total at most `C`, some term is
at most `C/N` — the engine of the entropy decrement's scale selection. -/
theorem exists_le_div_card_of_sum_le {N : ℕ} (hN : 0 < N) {f : ℕ → ℝ}
    (hf : ∀ i ∈ Finset.range N, 0 ≤ f i) {C : ℝ}
    (hsum : ∑ i ∈ Finset.range N, f i ≤ C) :
    ∃ i ∈ Finset.range N, f i ≤ C / N := by
  by_contra hcon
  push_neg at hcon
  have hstrict : (N : ℝ) * (C / N) < ∑ i ∈ Finset.range N, f i := by
    have h1 : ∑ _i ∈ Finset.range N, C / N < ∑ i ∈ Finset.range N, f i :=
      Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr hN⟩ hcon
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    exact h1
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcalc : (N : ℝ) * (C / N) = C := by
    field_simp
  rw [hcalc] at hstrict
  linarith

end Pigeonhole

end MoltResearch
