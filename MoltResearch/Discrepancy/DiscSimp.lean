import MoltResearch.Discrepancy.EndpointSimp
import MoltResearch.Discrepancy.DiscOffsetSimp
import MoltResearch.Discrepancy.StepOneSimp

/-!
# `DiscSimp`: opt-in simp rules for the discrepancy normal-form pipeline

This module is **opt-in**. It collects a small set of `[simp]` rules that are useful when you want a
`simp`-first normalization workflow for the discrepancy API, combining:

- endpoint cleanup (`Nat.succ` wrappers),
- step-one normalization (`… d …` ↦ `… 1 …` with the step pushed into the summand), and
- start-shift normalization for offset sums (push `m ↦ m + k` into the summand translation).

The stable surface (`import MoltResearch.Discrepancy`) does **not** enable these simp rules by
default, since they can change global simp normal forms.

Design constraint: all simp rules in this module are oriented so that they should not create simp
loops on their own; this file merely opts into a directed normal form.
-/

namespace MoltResearch

/-! ## Start-shift normalization (opt-in `[simp]`) -/

-- Prefer pushing a start-index shift into the summand translation.
attribute [simp] apSumOffset_shift_start_add
attribute [simp] apSumOffset_shift_start_add_left
attribute [simp] apSumOffset_shift_start_add_mul_left

/-- `discOffset` analogue of `apSumOffset_shift_start_add` (opt-in simp rule).

Orientation note: we rewrite **toward** the translated-summand normal form.
-/
@[simp] lemma discOffset_shift_start_add (f : ℕ → ℤ) (d m k n : ℕ) :
    discOffset f d (m + k) n = discOffset (fun t => f (t + k * d)) d m n := by
  -- `discOffset` is a wrapper around `Int.natAbs (apSumOffset …)`.
  simp [discOffset]

/-- `mul_left`-friendly variant of `discOffset_shift_start_add`.

This avoids commuting multiplication in downstream developments that prefer the `d * k` convention.
-/
@[simp] lemma discOffset_shift_start_add_mul_left (f : ℕ → ℤ) (d m k n : ℕ) :
    discOffset f d (m + k) n = discOffset (fun t => f (t + d * k)) d m n := by
  simpa [Nat.mul_comm] using
    (discOffset_shift_start_add (f := f) (d := d) (m := m) (k := k) (n := n))

end MoltResearch
