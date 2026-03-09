import MoltResearch.Discrepancy

/-!
# Tao 2015: Erdős discrepancy theorem (proof skeleton)

This module is **Conjectures-only**: it may contain `sorry`.

Goal: turn the Tao 2015 proof into an explicit chain of named intermediate lemmas so we can
fill it in incrementally, while keeping the main theorem statement in
`Conjectures/C0002_erdos_discrepancy/src/ErdosDiscrepancy.lean` a clean composition.

Nothing in this file should be imported from `MoltResearch/` (verified substrate).
-/

namespace MoltResearch

/-!
## High-level plan (names match future lemma stubs)

Tao’s proof is nontrivial; the point of this skeleton is to make the *shape* of the argument
machine-checkable even before we have the details.

We target the boundedness normal form:

`¬ BoundedDiscrepancy f`

where `BoundedDiscrepancy f := ∃ B, ∀ d n, d>0 → |apSum f d n| ≤ B`.

The eventual development will likely introduce auxiliary notions (log-averages, multiplicative
models, etc.) in `Conjectures/` first, and only move stable definitions to `MoltResearch/` once
we’re confident they are reusable.
-/

namespace Tao2015

/-!
### Small helper API: sign sequences are stable under shifts

These lemmas are intentionally tiny, but they reduce friction when constructing reduction
interfaces: many steps define a new sequence by shifting the old one.
-/
namespace IsSignSequence

/-- Shifting the index preserves the sign-sequence property. -/
theorem shift_add {f : ℕ → ℤ} (hf : IsSignSequence f) (a : ℕ) :
    IsSignSequence (fun k => f (k + a)) := by
  intro k
  simpa using hf (k + a)

/-- A common special case: shift by a multiple `m*d`. -/
theorem shift_add_mul {f : ℕ → ℤ} (hf : IsSignSequence f) (m d : ℕ) :
    IsSignSequence (fun k => f (k + m * d)) := by
  simpa using (shift_add (f := f) hf (a := m * d))

end IsSignSequence

/-!
### Bridge lemmas: shifting ↔ offset sums

`apSumOffset` is defined in terms of shifting by a multiple of `d`.  Downstream steps often want
these rewrite rules in the *forward* direction (from shifted sums to offset sums).

We keep them in `Conjectures/` because they are part of the “proof pipeline ergonomics”, not the
verified substrate.
-/

/-- A shifted AP sum is an offset AP sum. -/
theorem apSum_shift_add_mul_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSum (fun k => f (k + m * d)) d n = apSumOffset f d m n := by
  simpa using (apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n))

/-- The reverse orientation of `apSum_shift_add_mul_eq_apSumOffset`. -/
theorem apSumOffset_eq_apSum_shift_add_mul (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSum (fun k => f (k + m * d)) d n := by
  simpa using (apSum_shift_add_mul_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)).symm

/-!
### Bridge lemmas: `apSumOffset` ↔ `apSumFrom`

Track B treats `apSumFrom` as the canonical nucleus for affine progressions.
In Track C we often want to move between the “offset” normal form and the affine normal form
without importing additional files or redoing endpoint arithmetic.

These wrappers specialize the general bridge lemma
`apSumOffset_shift_add_eq_apSumFrom_bridge` to the common case `a = 0`.
-/

/-- Offset AP sum as an affine AP sum starting at `m*d`.

Concretely, this rewrites the offset family
`apSumOffset f d m n = ∑ i < n, f ((m+i+1)*d)`
into the affine nucleus
`apSumFrom f (m*d) d n = ∑ i < n, f (m*d + (i+1)*d)`.
-/
theorem apSumOffset_eq_apSumFrom_mul (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSumFrom f (m * d) d n := by
  -- Specialize the bridge lemma with `a = 0`.
  simpa using
    (apSumOffset_shift_add_eq_apSumFrom_bridge (f := f) (a := 0) (d := d) (m := m) (n := n))

/-- Reverse orientation of `apSumOffset_eq_apSumFrom_mul`. -/
theorem apSumFrom_mul_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSumFrom f (m * d) d n = apSumOffset f d m n := by
  simpa using (apSumOffset_eq_apSumFrom_mul (f := f) (d := d) (m := m) (n := n)).symm

/-!
### Combined bridge lemmas: shift ↔ affine AP sums

Many Track C reductions define a derived sequence by the literal shift
`g k := f (k + m*d)` and then want to speak directly in terms of the affine nucleus
`apSumFrom f (m*d) d`.

The following tiny wrappers package the common two-step rewrite:

`apSum (shift f) = apSumOffset f = apSumFrom f (m*d)`.
-/

/-- A shifted homogeneous AP sum is an affine AP sum starting at `m*d`. -/
theorem apSum_shift_add_mul_eq_apSumFrom_mul (f : ℕ → ℤ) (d m n : ℕ) :
    apSum (fun k => f (k + m * d)) d n = apSumFrom f (m * d) d n := by
  -- First rewrite the shift as an offset sum, then rewrite the offset sum as an affine sum.
  simpa [apSumOffset_eq_apSumFrom_mul] using
    (apSum_shift_add_mul_eq_apSumOffset (f := f) (d := d) (m := m) (n := n))

/-- Reverse orientation of `apSum_shift_add_mul_eq_apSumFrom_mul`.

This is convenient when a reduction step naturally produces an affine-tail statement but the
next stage expects a shifted-homogeneous `apSum`.
-/
theorem apSumFrom_mul_eq_apSum_shift_add_mul (f : ℕ → ℤ) (d m n : ℕ) :
    apSumFrom f (m * d) d n = apSum (fun k => f (k + m * d)) d n := by
  simpa using (apSum_shift_add_mul_eq_apSumFrom_mul (f := f) (d := d) (m := m) (n := n)).symm

/-- `Int.natAbs` form of `apSum_shift_add_mul_eq_apSumFrom_mul`. -/
theorem natAbs_apSum_shift_add_mul_eq_natAbs_apSumFrom_mul (f : ℕ → ℤ) (d m n : ℕ) :
    Int.natAbs (apSum (fun k => f (k + m * d)) d n) =
      Int.natAbs (apSumFrom f (m * d) d n) := by
  simp [apSum_shift_add_mul_eq_apSumFrom_mul]

/-- Discrepancy form of `apSum_shift_add_mul_eq_apSumFrom_mul`. -/
theorem discrepancy_shift_add_mul_eq_natAbs_apSumFrom_mul (f : ℕ → ℤ) (d m n : ℕ) :
    discrepancy (fun k => f (k + m * d)) d n =
      Int.natAbs (apSumFrom f (m * d) d n) := by
  -- `discrepancy = natAbs(apSum ...)`.
  simp [discrepancy, apSum_shift_add_mul_eq_apSumFrom_mul]

/-- `Int.natAbs` form of `apSumOffset_eq_apSumFrom_mul`. -/
theorem natAbs_apSumOffset_eq_natAbs_apSumFrom_mul (f : ℕ → ℤ) (d m n : ℕ) :
    Int.natAbs (apSumOffset f d m n) = Int.natAbs (apSumFrom f (m * d) d n) := by
  simp [apSumOffset_eq_apSumFrom_mul]

/-- Rewrite `discOffset` in terms of the affine AP-sum nucleus `apSumFrom`.

This is just the definitional wrapper `discOffset = natAbs(apSumOffset …)` combined with
`apSumOffset_eq_apSumFrom_mul`.
-/
theorem discOffset_eq_natAbs_apSumFrom_mul (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset f d m n = Int.natAbs (apSumFrom f (m * d) d n) := by
  simp [discOffset, apSumOffset_eq_apSumFrom_mul]

/-- Reverse orientation of `discOffset_eq_natAbs_apSumFrom_mul`. -/
theorem natAbs_apSumFrom_mul_eq_discOffset (f : ℕ → ℤ) (d m n : ℕ) :
    Int.natAbs (apSumFrom f (m * d) d n) = discOffset f d m n := by
  simpa using (discOffset_eq_natAbs_apSumFrom_mul (f := f) (d := d) (m := m) (n := n)).symm

/-- Discrepancy version of `apSum_shift_add_mul_eq_apSumOffset`. -/
theorem discrepancy_shift_add_mul_eq_discOffset (f : ℕ → ℤ) (d m n : ℕ) :
    discrepancy (fun k => f (k + m * d)) d n = discOffset f d m n := by
  -- Both sides are definitional wrappers around `Int.natAbs`.
  simp [discrepancy, discOffset, apSum_shift_add_mul_eq_apSumOffset]

/-- Reverse orientation of `discrepancy_shift_add_mul_eq_discOffset`. -/
theorem discOffset_eq_discrepancy_shift_add_mul (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset f d m n = discrepancy (fun k => f (k + m * d)) d n := by
  simpa using (discrepancy_shift_add_mul_eq_discOffset (f := f) (d := d) (m := m) (n := n)).symm

/-!
### Re-associating offsets

When building a multi-stage reduction, we frequently accumulate offsets of the form
`(m₁ + m₂) * d`.  It is convenient to be able to “peel off” an initial offset `m₁*d` by shifting
the underlying sequence.

The discrepancy analogue (`discOffset_add`) lives in the verified substrate.  Here we record the
AP-sum-level statement, which is often the first thing a reduction step needs.
-/

/-- Re-associate offsets at the AP-sum level.

This is the `apSum` analogue of `discOffset_add`.
-/
theorem apSumOffset_add (f : ℕ → ℤ) (d m₁ m₂ n : ℕ) :
    apSumOffset f d (m₁ + m₂) n = apSumOffset (fun k => f (k + m₁ * d)) d m₂ n := by
  -- Expand both sides to AP sums of shifted sequences.
  -- LHS: shift by `(m₁+m₂)*d`.
  -- RHS: first shift by `m₁*d`, then shift again by `m₂*d`.
  simp [apSumOffset_eq_apSum_shift_add, Nat.add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm, Nat.mul_assoc, Nat.left_distrib]

/-- Reverse orientation of `apSumOffset_add`.

We do not mark either direction `[simp]` to avoid rewriting loops.
-/
theorem apSumOffset_shift_add (f : ℕ → ℤ) (d m₁ m₂ n : ℕ) :
    apSumOffset (fun k => f (k + m₁ * d)) d m₂ n = apSumOffset f d (m₁ + m₂) n := by
  simpa using (apSumOffset_add (f := f) (d := d) (m₁ := m₁) (m₂ := m₂) (n := n)).symm

/-- `Int.natAbs` form of `apSumOffset_add`.

This is a lightweight helper for passing offset reassociations through the discrepancy wrappers.
-/
theorem natAbs_apSumOffset_add (f : ℕ → ℤ) (d m₁ m₂ n : ℕ) :
    Int.natAbs (apSumOffset f d (m₁ + m₂) n) =
      Int.natAbs (apSumOffset (fun k => f (k + m₁ * d)) d m₂ n) := by
  simp [apSumOffset_add]

/-- `discOffset` form of `apSumOffset_add`.

This is the natural “offset reassociation” normal form at the discrepancy level.
-/
theorem discOffset_add (f : ℕ → ℤ) (d m₁ m₂ n : ℕ) :
    discOffset f d (m₁ + m₂) n = discOffset (fun k => f (k + m₁ * d)) d m₂ n := by
  -- `discOffset` is definitional wrapper around `Int.natAbs (apSumOffset ...)`.
  simp [discOffset, natAbs_apSumOffset_add]

/-- Package the *assumption* of bounded discrepancy as data (`B` plus the bound lemma).

This is a Lean-friendly normal form: instead of passing around an existential hypothesis
`BoundedDiscrepancy f`, downstream steps can take a single `Context f`.

Note: this structure lives in `Conjectures/` because we may want to revise it as the proof
strategy evolves.
-/
structure Context (f : ℕ → ℤ) : Type where
  B : ℕ
  bound : ∀ d n : ℕ, d > 0 → Int.natAbs (apSum f d n) ≤ B

/-- Extract a `Context` from a boundedness hypothesis.

Noncomputable because we use classical choice to pick the witness `B`.
-/
noncomputable def Context.ofBoundedDiscrepancy {f : ℕ → ℤ} (hb : BoundedDiscrepancy f) :
    Context f := by
  classical
  refine ⟨Classical.choose hb, ?_⟩
  simpa using (Classical.choose_spec hb)

namespace Context

/-- Turn `Context f` back into the existential boundedness statement `BoundedDiscrepancy f`. -/
theorem toBoundedDiscrepancy (ctx : Context f) : BoundedDiscrepancy f := by
  refine ⟨ctx.B, ?_⟩
  intro d n hd
  exact ctx.bound d n hd

/-- The bound lemma, as a convenience. -/
theorem bound_apSum (ctx : Context f) (d n : ℕ) (hd : d > 0) :
    Int.natAbs (apSum f d n) ≤ ctx.B :=
  ctx.bound d n hd

/-- A paper-notation wrapper: boundedness for `∑ i∈Icc 1 n, f (i*d)`. -/
theorem bound_sum_Icc_mul (ctx : Context f) (d n : ℕ) (hd : d > 0) :
    Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) ≤ ctx.B := by
  -- rewrite to the nucleus sum `apSum`.
  simpa [apSum_eq_sum_Icc] using (ctx.bound_apSum (f := f) (d := d) (n := n) hd)

/-- Derived bound for offset sums.

This is a basic “boundedness is stable under taking tails” lemma: from boundedness of prefix sums
(`apSum`) we get boundedness of offset sums (`apSumOffset`) with a factor 2.
-/
theorem bound_apSumOffset (ctx : Context f) (d m n : ℕ) (hd : d > 0) :
    Int.natAbs (apSumOffset f d m n) ≤ ctx.B + ctx.B := by
  -- `apSumOffset = apSum (m+n) - apSum m`.
  calc
    Int.natAbs (apSumOffset f d m n)
        = Int.natAbs (apSum f d (m + n) - apSum f d m) := by
          simp [apSumOffset_eq_sub]
    _ ≤ Int.natAbs (apSum f d (m + n)) + Int.natAbs (apSum f d m) := by
          simpa using (Int.natAbs_sub_le (apSum f d (m + n)) (apSum f d m))
    _ ≤ ctx.B + ctx.B := by
          exact Nat.add_le_add (ctx.bound_apSum (f := f) (d := d) (n := m + n) hd)
            (ctx.bound_apSum (f := f) (d := d) (n := m) hd)

/-- Variant of `bound_apSumOffset` with the right-hand side written as `2 * B`.

This is occasionally more convenient when downstream stages track constants multiplicatively.
-/
theorem bound_apSumOffset_two_mul (ctx : Context f) (d m n : ℕ) (hd : d > 0) :
    Int.natAbs (apSumOffset f d m n) ≤ 2 * ctx.B := by
  -- `2 * B = B + B`.
  simpa [two_mul] using (ctx.bound_apSumOffset (f := f) (d := d) (m := m) (n := n) hd)

/-- Offset-sum bound in terms of the discrepancy wrapper `discOffset`. -/
theorem bound_discOffset (ctx : Context f) (d m n : ℕ) (hd : d > 0) :
    discOffset f d m n ≤ ctx.B + ctx.B := by
  simpa [discOffset] using (ctx.bound_apSumOffset (f := f) (d := d) (m := m) (n := n) hd)

/-- Variant of `bound_discOffset` with right-hand side written as `2 * B`. -/
theorem bound_discOffset_two_mul (ctx : Context f) (d m n : ℕ) (hd : d > 0) :
    discOffset f d m n ≤ 2 * ctx.B := by
  simpa [two_mul] using (ctx.bound_discOffset (f := f) (d := d) (m := m) (n := n) hd)

/-- Uniform version of `bound_discOffset`. -/
theorem bound_discOffset_forall (ctx : Context f) (d m : ℕ) (hd : d > 0) :
    ∀ n : ℕ, discOffset f d m n ≤ ctx.B + ctx.B := by
  intro n
  exact ctx.bound_discOffset (f := f) (d := d) (m := m) (n := n) hd

/-- Bound a shifted homogeneous AP sum by reducing it to an offset sum.

This is the “translation by a multiple of `d`” normal form.
-/
theorem bound_apSum_shift_add (ctx : Context f) (d m n : ℕ) (hd : d > 0) :
    Int.natAbs (apSum (fun k => f (k + m * d)) d n) ≤ ctx.B + ctx.B := by
  -- `apSumOffset f d m n = apSum (fun k => f (k + m*d)) d n`.
  simpa [apSumOffset_eq_apSum_shift_add] using
    (ctx.bound_apSumOffset (f := f) (d := d) (m := m) (n := n) hd)

/-- Bound a tail sum `apSumFrom f (m*d) d n` using the `Context` for prefix sums.

This is just `bound_apSum_shift_add` rewritten through `apSumFrom_eq_apSum_shift_add`.
-/
theorem bound_apSumFrom_mul (ctx : Context f) (d m n : ℕ) (hd : d > 0) :
    Int.natAbs (apSumFrom f (m * d) d n) ≤ ctx.B + ctx.B := by
  -- Rewrite to a shifted homogeneous AP sum, then use `bound_apSum_shift_add`.
  simpa [apSumFrom_eq_apSum_shift_add] using
    (ctx.bound_apSum_shift_add (f := f) (d := d) (m := m) (n := n) hd)

/-- Uniform version of `bound_apSumFrom_mul`. -/
theorem bound_apSumFrom_mul_forall (ctx : Context f) (d m : ℕ) (hd : d > 0) :
    ∀ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) ≤ ctx.B + ctx.B := by
  intro n
  exact ctx.bound_apSumFrom_mul (f := f) (d := d) (m := m) (n := n) hd

/-- The discrepancy bound corresponding to `bound_apSum`. -/
theorem bound_discrepancy (ctx : Context f) (d n : ℕ) (hd : d > 0) :
    discrepancy f d n ≤ ctx.B := by
  simpa [discrepancy] using (ctx.bound_apSum (f := f) (d := d) (n := n) hd)

/-- Uniform version of `bound_discrepancy`. -/
theorem bound_discrepancy_forall (ctx : Context f) (d : ℕ) (hd : d > 0) :
    ∀ n : ℕ, discrepancy f d n ≤ ctx.B := by
  intro n
  exact ctx.bound_discrepancy (f := f) (d := d) (n := n) hd

/-- Discrepancy bound for shifted AP sums (as in `bound_apSum_shift_add`). -/
theorem bound_discrepancy_shift_add (ctx : Context f) (d m n : ℕ) (hd : d > 0) :
    discrepancy (fun k => f (k + m * d)) d n ≤ ctx.B + ctx.B := by
  simpa [discrepancy] using (ctx.bound_apSum_shift_add (f := f) (d := d) (m := m) (n := n) hd)

/-- Uniform version of `bound_discrepancy_shift_add`. -/
theorem bound_discrepancy_shift_add_forall (ctx : Context f) (d m : ℕ) (hd : d > 0) :
    ∀ n : ℕ, discrepancy (fun k => f (k + m * d)) d n ≤ ctx.B + ctx.B := by
  intro n
  exact ctx.bound_discrepancy_shift_add (f := f) (d := d) (m := m) (n := n) hd

end Context

/-!
### A tiny “fixed-step” discrepancy context

Many intermediate reductions in Tao 2015 work along a *single* step size `d`.
`BoundedDiscrepancyAlong` packages this as an existential, but it is often convenient to pass the
witness `B` and the bound lemma together as a single record.

This is the fixed-step analogue of `Tao2015.Context`.
-/

structure ContextAlong (f : ℕ → ℤ) (d : ℕ) : Type where
  B : ℕ
  bound : ∀ n : ℕ, discrepancy f d n ≤ B

namespace ContextAlong

/-- Build a `ContextAlong` from the existential boundedness statement. -/
theorem ofBoundedDiscrepancyAlong {f : ℕ → ℤ} {d : ℕ} (hb : BoundedDiscrepancyAlong f d) :
    ContextAlong f d := by
  classical
  refine ⟨Classical.choose hb, ?_⟩
  simpa using (Classical.choose_spec hb)

/-- Turn `ContextAlong` back into the existential boundedness statement. -/
theorem toBoundedDiscrepancyAlong (ctx : ContextAlong f d) : BoundedDiscrepancyAlong f d := by
  refine ⟨ctx.B, ?_⟩
  intro n
  exact ctx.bound n

/-- Convenience lemma: the bound, as a named theorem. -/
theorem bound_discrepancy (ctx : ContextAlong f d) (n : ℕ) : discrepancy f d n ≤ ctx.B :=
  ctx.bound n

/-- `Int.natAbs` (sum-level) version of `bound_discrepancy`.

Downstream stages sometimes prefer to work with the nucleus `apSum` directly rather than the
wrapper `discrepancy`. This lemma lets them extract the underlying sum bound in one step.
-/
theorem bound_natAbs_apSum (ctx : ContextAlong f d) (n : ℕ) :
    Int.natAbs (apSum f d n) ≤ ctx.B := by
  simpa [discrepancy] using (ctx.bound_discrepancy (f := f) (d := d) n)

/-- `Int.natAbs` (sum-level) bound for offset sums.

This is the nucleus-level statement underlying `bound_discOffset`.
We prove it directly (rather than deriving it from `bound_discOffset`) to avoid a forward
reference.
-/
theorem bound_natAbs_apSumOffset (ctx : ContextAlong f d) (m n : ℕ) :
    Int.natAbs (apSumOffset f d m n) ≤ ctx.B + ctx.B := by
  -- `apSumOffset` is a difference of two homogeneous partial sums.
  calc
    Int.natAbs (apSumOffset f d m n)
        = Int.natAbs (apSum f d (m + n) - apSum f d m) := by
            simp [apSumOffset_eq_sub]
    _ ≤ Int.natAbs (apSum f d (m + n)) + Int.natAbs (apSum f d m) := by
            simpa using (Int.natAbs_sub_le (apSum f d (m + n)) (apSum f d m))
    _ ≤ ctx.B + ctx.B := by
            exact Nat.add_le_add (ctx.bound_natAbs_apSum (f := f) (d := d) (n := m + n))
              (ctx.bound_natAbs_apSum (f := f) (d := d) (n := m))

/-- If the discrepancies along a fixed step `d` are uniformly bounded by `B`, then the corresponding
*offset* discrepancies are uniformly bounded by `2*B`.

This is the fixed-step analogue of `Tao2015.Context.bound_discOffset`.
-/
theorem bound_discOffset (ctx : ContextAlong f d) (m n : ℕ) :
    discOffset f d m n ≤ ctx.B + ctx.B := by
  -- `discOffset` is `natAbs (apSumOffset ...)`, and `apSumOffset` is a difference of partial sums.
  -- Then apply the triangle inequality and the fixed-step bound.
  have h₁ : discrepancy f d (m + n) ≤ ctx.B := ctx.bound_discrepancy (f := f) (d := d) (n := m + n)
  have h₂ : discrepancy f d m ≤ ctx.B := ctx.bound_discrepancy (f := f) (d := d) (n := m)
  -- Expand `discOffset` and `apSumOffset`.
  -- Note: `discrepancy` is definitional wrapper `natAbs (apSum ...)`.
  calc
    discOffset f d m n
        = Int.natAbs (apSum f d (m + n) - apSum f d m) := by
            simp [discOffset, apSumOffset_eq_sub]
    _ ≤ Int.natAbs (apSum f d (m + n)) + Int.natAbs (apSum f d m) := by
            simpa using (Int.natAbs_sub_le (apSum f d (m + n)) (apSum f d m))
    _ ≤ ctx.B + ctx.B := by
            -- Rewrite the hypotheses `h₁,h₂` into `natAbs (apSum ...) ≤ B` form.
            simpa [discrepancy] using Nat.add_le_add h₁ h₂

end ContextAlong

/-!
### A tiny “fixed-step” unboundedness predicate

Track C routinely wants to talk about *unbounded discrepancy along a fixed step size*.
The verified substrate expresses boundedness via `BoundedDiscrepancyAlong`; its negation is the
correct logical form, but it is often more convenient to carry the explicit witness form
`∀ B, ∃ n, B < discrepancy …`.

We record that witness form here as lightweight pipeline glue.
-/

def UnboundedDiscrepancyAlong (f : ℕ → ℤ) (d : ℕ) : Prop :=
  ∀ B : ℕ, ∃ n : ℕ, B < discrepancy f d n

namespace UnboundedDiscrepancyAlong

/-- Definitional symmetry: `B < …` vs `… > B`. -/
theorem iff_forall_exists_discrepancy_gt (f : ℕ → ℤ) (d : ℕ) :
    UnboundedDiscrepancyAlong f d ↔ (∀ B : ℕ, ∃ n : ℕ, discrepancy f d n > B) := by
  -- `a > b` is notation for `b < a`.
  simp [UnboundedDiscrepancyAlong, gt_iff_lt]

/-- Unboundedness witness form is equivalent to the negation of `BoundedDiscrepancyAlong`. -/
theorem iff_not_boundedDiscrepancyAlong (f : ℕ → ℤ) (d : ℕ) :
    UnboundedDiscrepancyAlong f d ↔ ¬ BoundedDiscrepancyAlong f d := by
  -- Use the standard negated-boundedness equivalence, and unfold the witness predicate.
  simpa [UnboundedDiscrepancyAlong] using
    (Tao2015.not_boundedDiscrepancyAlong_iff_forall_exists_discrepancy_gt (g := f) (d := d)).symm

/-- Forward direction of `iff_not_boundedDiscrepancyAlong`. -/
theorem not_boundedDiscrepancyAlong {f : ℕ → ℤ} {d : ℕ} (h : UnboundedDiscrepancyAlong f d) :
    ¬ BoundedDiscrepancyAlong f d :=
  (iff_not_boundedDiscrepancyAlong (f := f) (d := d)).1 h

/-- Backward direction of `iff_not_boundedDiscrepancyAlong`. -/
theorem of_not_boundedDiscrepancyAlong {f : ℕ → ℤ} {d : ℕ} (h : ¬ BoundedDiscrepancyAlong f d) :
    UnboundedDiscrepancyAlong f d :=
  (iff_not_boundedDiscrepancyAlong (f := f) (d := d)).2 h

end UnboundedDiscrepancyAlong

/-!
### A tiny “offset discrepancy” unboundedness predicate

Stage 2 of Track C is naturally phrased in terms of the *offset discrepancy family*
`discOffset f d m n` associated to a reduction output `(d,m)`.

The verified substrate expresses boundedness for this family via `BoundedDiscOffset f d m`.
As with `UnboundedDiscrepancyAlong`, it is often more convenient to carry the explicit witness
normal form `∀ B, ∃ n, B < discOffset …`.

We record that witness form here as lightweight pipeline glue.
-/

def UnboundedDiscOffset (f : ℕ → ℤ) (d m : ℕ) : Prop :=
  ∀ B : ℕ, ∃ n : ℕ, B < discOffset f d m n

namespace UnboundedDiscOffset

/-- Definitional symmetry: `B < …` vs `… > B`. -/
theorem iff_forall_exists_discOffset_gt (f : ℕ → ℤ) (d m : ℕ) :
    UnboundedDiscOffset f d m ↔ (∀ B : ℕ, ∃ n : ℕ, discOffset f d m n > B) := by
  simp [UnboundedDiscOffset, gt_iff_lt]

/-- Unbounded offset-discrepancy witness form is equivalent to the negation of `BoundedDiscOffset`. -/
theorem iff_not_boundedDiscOffset (f : ℕ → ℤ) (d m : ℕ) :
    UnboundedDiscOffset f d m ↔ ¬ BoundedDiscOffset f d m := by
  -- Use the standard negated-boundedness equivalence from the verified substrate.
  simpa [UnboundedDiscOffset] using
    (not_boundedDiscOffset_iff_forall_exists_discOffset_gt (f := f) (d := d) (m := m)).symm

/-- Forward direction of `iff_not_boundedDiscOffset`. -/
theorem not_boundedDiscOffset {f : ℕ → ℤ} {d m : ℕ} (h : UnboundedDiscOffset f d m) :
    ¬ BoundedDiscOffset f d m :=
  (iff_not_boundedDiscOffset (f := f) (d := d) (m := m)).1 h

/-- Backward direction of `iff_not_boundedDiscOffset`. -/
theorem of_not_boundedDiscOffset {f : ℕ → ℤ} {d m : ℕ} (h : ¬ BoundedDiscOffset f d m) :
    UnboundedDiscOffset f d m :=
  (iff_not_boundedDiscOffset (f := f) (d := d) (m := m)).2 h

end UnboundedDiscOffset

/-!
### A tiny “fixed-step” discrepancy predicate

`HasDiscrepancyAtLeast` quantifies over the step size `d`.  Many intermediate reductions in
Tao 2015 produce information at a *specific* step size (or a small set of step sizes).

To avoid fighting the existential quantifier prematurely, we introduce a local predicate
for “large discrepancy along a fixed `d`”.  Downstream stages can later upgrade it back to
`HasDiscrepancyAtLeast` once they manage the `d`-quantifier.

This lives in `Conjectures/` because it is proof-pipeline glue rather than stable substrate.
-/

def HasDiscrepancyAtLeastAlong (f : ℕ → ℤ) (d C : ℕ) : Prop :=
  ∃ n : ℕ, Int.natAbs (apSum f d n) > C

namespace HasDiscrepancyAtLeastAlong

lemma mono {f : ℕ → ℤ} {d C₁ C₂ : ℕ}
    (h : HasDiscrepancyAtLeastAlong f d C₂) (hC : C₁ ≤ C₂) :
    HasDiscrepancyAtLeastAlong f d C₁ := by
  rcases h with ⟨n, hn⟩
  exact ⟨n, lt_of_le_of_lt hC hn⟩

lemma of_succ {f : ℕ → ℤ} {d C : ℕ} (h : HasDiscrepancyAtLeastAlong f d (C + 1)) :
    HasDiscrepancyAtLeastAlong f d C :=
  mono (f := f) (d := d) (C₁ := C) (C₂ := C + 1) h (Nat.le_succ C)

/-- Promote a fixed-step discrepancy witness to the standard `HasDiscrepancyAtLeast` predicate.

This is just a small packaging lemma: `HasDiscrepancyAtLeastAlong` fixes `d`, while
`HasDiscrepancyAtLeast` existentially quantifies over `d`.
-/
lemma toHasDiscrepancyAtLeast {f : ℕ → ℤ} {d C : ℕ} (hd : d > 0)
    (h : HasDiscrepancyAtLeastAlong f d C) :
    HasDiscrepancyAtLeast f C := by
  rcases h with ⟨n, hn⟩
  exact ⟨d, n, hd, hn⟩

/-- `HasDiscrepancyAtLeastAlong` is just the definitional `discrepancy` wrapper form.

This lemma is convenient because many later stages talk in terms of `discrepancy` rather than
raw `Int.natAbs (apSum …)`.
-/
lemma iff_exists_discrepancy_gt (f : ℕ → ℤ) (d C : ℕ) :
    HasDiscrepancyAtLeastAlong f d C ↔ (∃ n : ℕ, discrepancy f d n > C) := by
  simp [HasDiscrepancyAtLeastAlong, discrepancy]

/-- Forward direction of `iff_exists_discrepancy_gt`. -/
lemma exists_discrepancy_gt {f : ℕ → ℤ} {d C : ℕ} (h : HasDiscrepancyAtLeastAlong f d C) :
    ∃ n : ℕ, discrepancy f d n > C :=
  (iff_exists_discrepancy_gt (f := f) (d := d) (C := C)).1 h

/-- Backward direction of `iff_exists_discrepancy_gt`. -/
lemma of_exists_discrepancy_gt {f : ℕ → ℤ} {d C : ℕ} (h : ∃ n : ℕ, discrepancy f d n > C) :
    HasDiscrepancyAtLeastAlong f d C :=
  (iff_exists_discrepancy_gt (f := f) (d := d) (C := C)).2 h

/-- Unboundedness along a fixed `d`, phrased using `HasDiscrepancyAtLeastAlong`.

This is a convenient repackaging of
`not_boundedDiscrepancyAlong_iff_forall_exists_discrepancy_gt`.
-/
theorem forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscrepancyAlong (g : ℕ → ℤ) (d : ℕ) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong g d C) ↔ ¬ BoundedDiscrepancyAlong g d := by
  -- Rewrite `HasDiscrepancyAtLeastAlong` to the `discrepancy`-wrapper witness form.
  -- Then apply the standard “not bounded ↔ ∀ B, ∃ n, B < ...” lemma.
  calc
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong g d C)
        ↔ (∀ B : ℕ, ∃ n : ℕ, B < discrepancy g d n) := by
          -- `a > b` is notation for `b < a`.
          simpa [HasDiscrepancyAtLeastAlong.iff_exists_discrepancy_gt, gt_iff_lt]
    _ ↔ ¬ BoundedDiscrepancyAlong g d := by
          simpa using
            (Tao2015.not_boundedDiscrepancyAlong_iff_forall_exists_discrepancy_gt (g := g) (d := d)).symm

@[deprecated (since := "2026-03-07")]
theorem forall_iff_not_boundedDiscrepancyAlong (g : ℕ → ℤ) (d : ℕ) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong g d C) ↔ ¬ BoundedDiscrepancyAlong g d := by
  simpa using (forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscrepancyAlong (g := g) (d := d))

/-- Having arbitrarily large fixed-step discrepancy witnesses is the same as unbounded discrepancy
along that step size.

This lemma is pure “pipeline glue”: it lets later stages switch between the witness-style predicate
`HasDiscrepancyAtLeastAlong` and the unboundedness predicate `UnboundedDiscrepancyAlong` with a
single `simp`.
-/
theorem forall_hasDiscrepancyAtLeastAlong_iff_unboundedDiscrepancyAlong (g : ℕ → ℤ) (d : ℕ) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong g d C) ↔ Tao2015.UnboundedDiscrepancyAlong g d := by
  -- `UnboundedDiscrepancyAlong` uses the `B < discrepancy ...` witness form.
  -- `HasDiscrepancyAtLeastAlong` uses the equivalent `∃ n, discrepancy ... > C` form.
  simpa [Tao2015.UnboundedDiscrepancyAlong, HasDiscrepancyAtLeastAlong.iff_exists_discrepancy_gt,
    gt_iff_lt]

end HasDiscrepancyAtLeastAlong

/-!
### A common special case: fixed-step discrepancy of a shifted sequence

Many pipeline steps define a new sequence by shifting the original one by a multiple of the
common difference `d`.  The following lemmas let us immediately rewrite the resulting
`HasDiscrepancyAtLeastAlong` statements into `discOffset` / `apSumOffset` witnesses.
-/

/-- Fixed-step discrepancy for a shifted sequence is the same as an offset-discrepancy witness.

This is a convenience lemma combining
`HasDiscrepancyAtLeastAlong.iff_exists_discrepancy_gt` with the rewrite
`discrepancy_shift_add_mul_eq_discOffset`.
-/
theorem hasDiscrepancyAtLeastAlong_shift_add_mul_iff_exists_discOffset_gt
    (f : ℕ → ℤ) (d m C : ℕ) :
    HasDiscrepancyAtLeastAlong (fun k => f (k + m * d)) d C ↔
      (∃ n : ℕ, discOffset f d m n > C) := by
  -- First rewrite `HasDiscrepancyAtLeastAlong` into the `discrepancy` wrapper form.
  -- Then rewrite `discrepancy (shift f)` into `discOffset f`.
  constructor
  · intro h
    rcases (HasDiscrepancyAtLeastAlong.iff_exists_discrepancy_gt
        (f := fun k => f (k + m * d)) (d := d) (C := C)).1 h with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [discrepancy_shift_add_mul_eq_discOffset (f := f) (d := d) (m := m) (n := n)] using hn
  · rintro ⟨n, hn⟩
    have : discrepancy (fun k => f (k + m * d)) d n > C := by
      simpa [discrepancy_shift_add_mul_eq_discOffset (f := f) (d := d) (m := m) (n := n)] using hn
    exact (HasDiscrepancyAtLeastAlong.iff_exists_discrepancy_gt
        (f := fun k => f (k + m * d)) (d := d) (C := C)).2 ⟨n, this⟩

/-- `natAbs` (sum-level) version of `hasDiscrepancyAtLeastAlong_shift_add_mul_iff_exists_discOffset_gt`. -/
theorem hasDiscrepancyAtLeastAlong_shift_add_mul_iff_exists_natAbs_apSumOffset_gt
    (f : ℕ → ℤ) (d m C : ℕ) :
    HasDiscrepancyAtLeastAlong (fun k => f (k + m * d)) d C ↔
      (∃ n : ℕ, Int.natAbs (apSumOffset f d m n) > C) := by
  -- `discOffset` is definitional.
  simpa [discOffset] using
    (hasDiscrepancyAtLeastAlong_shift_add_mul_iff_exists_discOffset_gt (f := f) (d := d) (m := m) (C := C))

/-- Fixed-step discrepancy for a shifted sequence rewritten into an affine-tail (`apSumFrom`) witness.

This is occasionally cleaner than the offset form when downstream stages want to work with the
canonical affine nucleus `apSumFrom`.
-/
theorem hasDiscrepancyAtLeastAlong_shift_add_mul_iff_exists_natAbs_apSumFrom_mul_gt
    (f : ℕ → ℤ) (d m C : ℕ) :
    HasDiscrepancyAtLeastAlong (fun k => f (k + m * d)) d C ↔
      (∃ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  -- Unfold the fixed-step predicate and rewrite the shifted homogeneous AP sum into `apSumFrom`.
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- `natAbs (apSum (shift f)) = natAbs (apSumFrom f (m*d) ...)`.
    simpa [natAbs_apSum_shift_add_mul_eq_natAbs_apSumFrom_mul (f := f) (d := d) (m := m) (n := n)] using hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- Rewrite `natAbs (apSumFrom ...)` back to `natAbs (apSum (shift f) ...)`.
    simpa [natAbs_apSum_shift_add_mul_eq_natAbs_apSumFrom_mul (f := f) (d := d) (m := m) (n := n)] using hn

/-- `<`-oriented version of `hasDiscrepancyAtLeastAlong_shift_add_mul_iff_exists_natAbs_apSumFrom_mul_gt`. -/
theorem hasDiscrepancyAtLeastAlong_shift_add_mul_iff_exists_natAbs_apSumFrom_mul_lt
    (f : ℕ → ℤ) (d m C : ℕ) :
    HasDiscrepancyAtLeastAlong (fun k => f (k + m * d)) d C ↔
      (∃ n : ℕ, C < Int.natAbs (apSumFrom f (m * d) d n)) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using
    (hasDiscrepancyAtLeastAlong_shift_add_mul_iff_exists_natAbs_apSumFrom_mul_gt (f := f) (d := d) (m := m) (C := C))

/-- A further convenience: rewrite the shifted fixed-step predicate into a `discOffset` witness
with the inequality oriented as `C < ...`.
-/
theorem hasDiscrepancyAtLeastAlong_shift_add_mul_iff_exists_discOffset_lt
    (f : ℕ → ℤ) (d m C : ℕ) :
    HasDiscrepancyAtLeastAlong (fun k => f (k + m * d)) d C ↔
      (∃ n : ℕ, C < discOffset f d m n) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using
    (hasDiscrepancyAtLeastAlong_shift_add_mul_iff_exists_discOffset_gt (f := f) (d := d) (m := m) (C := C))

/-- Output of the first major reduction stage of Tao 2015.

This is the first **nontrivial interface** we want downstream steps to consume.

It packages:
- an auxiliary sign sequence `g`
- some numeric parameters `d,m`
- a rewrite rule relating `apSum g d` to an `apSumOffset` of the original sequence
- a small “discrepancy transfers” contract, so downstream steps can treat `g` as a
  faithful proxy for the offset sequence of `f`.

This lives in `Conjectures/` so we can iterate on the interface without destabilizing
the verified `MoltResearch/` substrate.
-/
structure ReductionOutput (f : ℕ → ℤ) : Type where
  /-- Common difference of the affine transform. -/
  d : ℕ
  /-- Offset multiplier: we shift by `m*d`. -/
  m : ℕ
  hd : d > 0
  /-- The derived sign sequence. -/
  g : ℕ → ℤ
  hg : IsSignSequence g
  /-- `g` is the shift of `f` by the multiple `m*d`. -/
  g_eq : g = fun k => f (k + m * d)
  /-- Main bridge rule: rewrite `apSum g d` as an offset AP sum of `f`. -/
  apSum_contract : ∀ n : ℕ, apSum g d n = apSumOffset f d m n
  /-- Transfer contract (consumer-friendly form): any uniform bound on the offset discrepancy
  transfers to a uniform bound on the discrepancy of `g`. -/
  contract_discrepancy_le : ∀ B : ℕ, (∀ n, discOffset f d m n ≤ B) → ∀ n, discrepancy g d n ≤ B

namespace ReductionOutput

variable {f : ℕ → ℤ}

/-!
### Tiny contract consequences

The record field `apSum_contract` is the *core* stage-1 bridge.  Most consumer-facing rewrite
lemmas are just wrappers around it (plus definitional unfoldings of `discrepancy` / `discOffset`).

We record a few of these wrappers here because they are extremely common in later pipeline stages
and keeping them named avoids repeated `simp` arguments.
-/

/-- `Int.natAbs` form of the stage-1 AP-sum contract. -/
theorem natAbs_apSum_eq_natAbs_apSumOffset (out : ReductionOutput f) (n : ℕ) :
    Int.natAbs (apSum out.g out.d n) = Int.natAbs (apSumOffset f out.d out.m n) := by
  simpa [out.apSum_contract n]

/-- Definitional wrapper: rewrite discrepancy of `out.g` to the bundled offset discrepancy.

This lemma is derived purely from `out.apSum_contract`; it does not use `out.g_eq`.
-/
theorem discrepancy_eq_discOffset_via_contract (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n = discOffset f out.d out.m n := by
  -- Both sides are `Int.natAbs` wrappers around the AP sums.
  simp [discrepancy, discOffset, out.apSum_contract]

/-- A strict inequality witness for the reduced discrepancy transfers to the bundled offset family.

This is the `∃`-packaged form of `discrepancy_eq_discOffset_via_contract`.
-/
theorem exists_discOffset_gt_of_exists_discrepancy_gt_via_contract (out : ReductionOutput f) (C : ℕ)
    (h : ∃ n : ℕ, discrepancy out.g out.d n > C) :
    ∃ n : ℕ, discOffset f out.d out.m n > C := by
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [out.discrepancy_eq_discOffset_via_contract (f := f) (n := n)] using hn

/-- Reverse direction of `exists_discOffset_gt_of_exists_discrepancy_gt_via_contract`. -/
theorem exists_discrepancy_gt_of_exists_discOffset_gt_via_contract (out : ReductionOutput f) (C : ℕ)
    (h : ∃ n : ℕ, discOffset f out.d out.m n > C) :
    ∃ n : ℕ, discrepancy out.g out.d n > C := by
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [out.discrepancy_eq_discOffset_via_contract (f := f) (n := n)] using hn

/-!
### Canonical constructor: the literal shift reduction

Many Track C reductions begin by defining the reduced sequence as the literal shift
`g k := f (k + m*d)`.

The record `ReductionOutput` is *more general* (it allows a definitional equality `g_eq` rather
than forcing `g` to be syntactically that lambda), but it's convenient to have a one-line
constructor for the common case.
-/

/-- Canonical `ReductionOutput` where the reduced sequence is the literal shift
`g k := f (k + m*d)`.

This constructor is intentionally lightweight: it just packages the basic rewrite contract
`apSum (shift f) = apSumOffset f` and the corresponding discrepancy transfer.
-/
def ofShift (f : ℕ → ℤ) (hf : IsSignSequence f) (d m : ℕ) (hd : d > 0) :
    ReductionOutput f := by
  refine
    { d := d
      m := m
      hd := hd
      g := fun k => f (k + m * d)
      hg := IsSignSequence.shift_add_mul (f := f) hf m d
      g_eq := rfl
      apSum_contract := ?_
      contract_discrepancy_le := ?_ }
  · intro n
    simpa using (Tao2015.apSum_shift_add_mul_eq_apSumOffset (f := f) (d := d) (m := m) (n := n))
  · intro B hB n
    -- Rewrite `discOffset` into `discrepancy` using the contract.
    simpa [discOffset, discrepancy, Tao2015.apSum_shift_add_mul_eq_apSumOffset] using hB n

/-!
### `simp` lemmas for `ReductionOutput.ofShift`

These are tiny definitional helpers: `ofShift` is the most common way later stages construct a
stage-1 reduction output, so it’s convenient to have its basic fields available to `simp`.
-/

@[simp] theorem ofShift_d (f : ℕ → ℤ) (hf : IsSignSequence f) (d m : ℕ) (hd : d > 0) :
    (ReductionOutput.ofShift (f := f) hf d m hd).d = d := by
  rfl

@[simp] theorem ofShift_m (f : ℕ → ℤ) (hf : IsSignSequence f) (d m : ℕ) (hd : d > 0) :
    (ReductionOutput.ofShift (f := f) hf d m hd).m = m := by
  rfl

@[simp] theorem ofShift_g (f : ℕ → ℤ) (hf : IsSignSequence f) (d m : ℕ) (hd : d > 0) :
    (ReductionOutput.ofShift (f := f) hf d m hd).g = (fun k => f (k + m * d)) := by
  rfl

@[simp] theorem ofShift_g_apply (f : ℕ → ℤ) (hf : IsSignSequence f) (d m : ℕ) (hd : d > 0) (k : ℕ) :
    (ReductionOutput.ofShift (f := f) hf d m hd).g k = f (k + m * d) := by
  rfl

@[simp] theorem ofShift_apSum_eq_apSumOffset (f : ℕ → ℤ) (hf : IsSignSequence f) (d m n : ℕ) (hd : d > 0) :
    apSum (ReductionOutput.ofShift (f := f) hf d m hd).g d n = apSumOffset f d m n := by
  -- This is exactly the stored contract.
  simpa using (ReductionOutput.ofShift (f := f) hf d m hd).apSum_contract n

@[simp] theorem ofShift_discrepancy_eq_discOffset (f : ℕ → ℤ) (hf : IsSignSequence f)
    (d m n : ℕ) (hd : d > 0) :
    discrepancy (ReductionOutput.ofShift (f := f) hf d m hd).g d n = discOffset f d m n := by
  -- Reduce to the AP-sum contract and unfold wrappers.
  simp [discrepancy, discOffset, ofShift_apSum_eq_apSumOffset (f := f) (hf := hf) (d := d) (m := m)
    (n := n) hd]

/-- `apSum` form of the stage-1 contract for the canonical shift reduction, rewritten into the
canonical affine-tail nucleus `apSumFrom`.

This is a small `simp`-friendly wrapper around `Tao2015.apSum_shift_add_mul_eq_apSumFrom_mul`.
-/
@[simp] theorem ofShift_apSum_eq_apSumFrom_mul (f : ℕ → ℤ) (hf : IsSignSequence f)
    (d m n : ℕ) (hd : d > 0) :
    apSum (ReductionOutput.ofShift (f := f) hf d m hd).g d n = apSumFrom f (m * d) d n := by
  -- Rewrite `g` to the literal shift and apply the general shift→affine bridge.
  simpa [ofShift_g (f := f) (hf := hf) (d := d) (m := m) hd] using
    (Tao2015.apSum_shift_add_mul_eq_apSumFrom_mul (f := f) (d := d) (m := m) (n := n))

/-- `discrepancy` form of the stage-1 contract for the canonical shift reduction, rewritten into
`Int.natAbs (apSumFrom ...)`.

This is often the cleanest “nucleus-level” normal form for consumers.
-/
@[simp] theorem ofShift_discrepancy_eq_natAbs_apSumFrom_mul (f : ℕ → ℤ) (hf : IsSignSequence f)
    (d m n : ℕ) (hd : d > 0) :
    discrepancy (ReductionOutput.ofShift (f := f) hf d m hd).g d n =
      Int.natAbs (apSumFrom f (m * d) d n) := by
  -- Rewrite `g` to the literal shift and apply the general shift→affine discrepancy bridge.
  simpa [ofShift_g (f := f) (hf := hf) (d := d) (m := m) hd] using
    (Tao2015.discrepancy_shift_add_mul_eq_natAbs_apSumFrom_mul (f := f) (d := d) (m := m) (n := n))

/-!
### Stage-1 regression examples

These `example` blocks are intentionally tiny: they serve as compile-time checks that the
consumer-facing rewrite/transfer API for `ReductionOutput` keeps working as we refactor the file.

They are not meant to be mathematically deep; they just pin down the *intended usage pattern*.
-/

section Stage1RegressionExamples

variable (f : ℕ → ℤ) (hf : IsSignSequence f) (d m : ℕ) (hd : d > 0)

/-- `ofShift` exposes the stage-1 discrepancy contract in the expected orientation. -/
example (n : ℕ) :
    discrepancy (ReductionOutput.ofShift (f := f) hf d m hd).g d n = discOffset f d m n := by
  simp

/-- A uniform bound on the offset discrepancy family transfers to the reduced sequence. -/
example (B : ℕ)
    (hB : ∀ n : ℕ, discOffset f d m n ≤ B) :
    ∀ n : ℕ, discrepancy (ReductionOutput.ofShift (f := f) hf d m hd).g d n ≤ B := by
  intro n
  -- This is exactly the stored transfer contract.
  simpa using (ReductionOutput.ofShift (f := f) hf d m hd).contract_discrepancy_le B hB n

/-- Fixed-step large discrepancy for the reduced sequence rewrites to an affine-tail witness. -/
example (C : ℕ) :
    HasDiscrepancyAtLeastAlong (ReductionOutput.ofShift (f := f) hf d m hd).g d C ↔
      (∃ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  -- This is the consumer-facing witness normal form.
  simpa using
    (ReductionOutput.hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_mul_gt
      (f := f) (out := ReductionOutput.ofShift (f := f) hf d m hd) C)

end Stage1RegressionExamples

/-!
### Basic accessors

These are tiny one-liners that make it easier for downstream stages to use a
`ReductionOutput` without constantly rewriting via the record fields.
-/

/-- Explicit pointwise form of `out.g_eq`.

We intentionally do *not* mark this lemma `[simp]`: rewriting `out.g` into a shifted `f` is often
helpful, but can also cause large proofs to expand aggressively. Prefer `simp [ReductionOutput.g_apply]`
(or `simp [out.g_eq]`) at the specific call sites that want this rewrite.
-/
theorem g_apply (out : ReductionOutput f) (k : ℕ) :
    out.g k = f (k + out.m * out.d) := by
  simpa [out.g_eq]

/-- Rewrite `apSum out.g out.d` into the literal shifted form.

This is occasionally useful when a downstream step wants to apply lemmas stated specifically for
shifts of the form `fun k => f (k + m*d)` (rather than the abstract `out.g`).
-/
theorem apSum_eq_apSum_shift (out : ReductionOutput f) (n : ℕ) :
    apSum out.g out.d n = apSum (fun k => f (k + out.m * out.d)) out.d n := by
  simp [out.g_eq]

/-- Rewrite `discrepancy out.g out.d` into the literal shifted form.

This is the discrepancy-wrapper analogue of `apSum_eq_apSum_shift`.
-/
theorem discrepancy_eq_discrepancy_shift (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n =
      discrepancy (fun k => f (k + out.m * out.d)) out.d n := by
  simp [out.g_eq]

/-- The “literal shift” discrepancy rewrite specialized to the parameters bundled in `out`.

This lemma does *not* mention `out.g`; it is useful when a downstream stage wants to talk about
`fun k => f (k + out.m*out.d)` directly, but still reuse `out.d,out.m` consistently.
-/
theorem discrepancy_shift_eq_discOffset (out : ReductionOutput f) (n : ℕ) :
    discrepancy (fun k => f (k + out.m * out.d)) out.d n = discOffset f out.d out.m n := by
  simpa using
    (Tao2015.discrepancy_shift_add_mul_eq_discOffset (f := f) (d := out.d) (m := out.m) (n := n))

/-- The “literal shift” AP-sum rewrite specialized to the parameters bundled in `out`.

As with `discrepancy_shift_eq_discOffset`, this lemma does not mention `out.g`.
-/
theorem apSum_shift_eq_apSumOffset (out : ReductionOutput f) (n : ℕ) :
    apSum (fun k => f (k + out.m * out.d)) out.d n = apSumOffset f out.d out.m n := by
  simpa using
    (Tao2015.apSum_shift_add_mul_eq_apSumOffset (f := f) (d := out.d) (m := out.m) (n := n))

/-!
### Small nucleus rewrites specialized to `out`

Downstream stages often prefer the affine-tail nucleus `apSumFrom` over the offset form.
These wrappers let Track C steps rewrite everything using the *parameters* bundled in a
`ReductionOutput` without having to restate `out.m,out.d` each time.
-/

/-- Affine-tail AP sum at `out.m*out.d` rewritten into the bundled offset sum.

This lemma does not mention `out.g`; it is purely about relating the two nuclei for the original
sequence `f`.
-/
theorem apSumFrom_mul_eq_apSumOffset (out : ReductionOutput f) (n : ℕ) :
    apSumFrom f (out.m * out.d) out.d n = apSumOffset f out.d out.m n := by
  simpa using
    (Tao2015.apSumFrom_mul_eq_apSumOffset (f := f) (d := out.d) (m := out.m) (n := n))

/-- Reverse orientation of `apSumFrom_mul_eq_apSumOffset`. -/
theorem apSumOffset_eq_apSumFrom_mul (out : ReductionOutput f) (n : ℕ) :
    apSumOffset f out.d out.m n = apSumFrom f (out.m * out.d) out.d n := by
  simpa using (out.apSumFrom_mul_eq_apSumOffset (f := f) (n := n)).symm

/-- Rewrite the affine-tail nucleus `apSumFrom` into the reduced AP sum `apSum out.g`.

This is the consumer-friendly “stage-1 contract” in the `apSumFrom` normal form.
-/
theorem apSumFrom_mul_eq_apSum (out : ReductionOutput f) (n : ℕ) :
    apSumFrom f (out.m * out.d) out.d n = apSum out.g out.d n := by
  -- `apSumFrom = apSumOffset` and `apSum out.g = apSumOffset`.
  calc
    apSumFrom f (out.m * out.d) out.d n = apSumOffset f out.d out.m n := by
      simpa using (out.apSumFrom_mul_eq_apSumOffset (f := f) (n := n))
    _ = apSum out.g out.d n := by
      -- This is the record field `out.apSum_contract`.
      simpa using (out.apSum_contract n).symm

/-- Reverse orientation of `apSumFrom_mul_eq_apSum`. -/
theorem apSum_eq_apSumFrom_mul (out : ReductionOutput f) (n : ℕ) :
    apSum out.g out.d n = apSumFrom f (out.m * out.d) out.d n := by
  simpa using (out.apSumFrom_mul_eq_apSum (f := f) (n := n)).symm

/-- `discOffset` rewritten into `Int.natAbs (apSumFrom ...)` using the parameters in `out`. -/
theorem discOffset_eq_natAbs_apSumFrom_mul (out : ReductionOutput f) (n : ℕ) :
    discOffset f out.d out.m n = Int.natAbs (apSumFrom f (out.m * out.d) out.d n) := by
  simpa using
    (Tao2015.discOffset_eq_natAbs_apSumFrom_mul (f := f) (d := out.d) (m := out.m) (n := n))

/-- Discrepancy of the reduced sequence rewritten to the affine-tail nucleus `apSumFrom`.

This is often the most compact “consumer” form of the stage-1 contract.
-/
theorem discrepancy_eq_natAbs_apSumFrom_mul (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n = Int.natAbs (apSumFrom f (out.m * out.d) out.d n) := by
  -- First rewrite `out.g` to the literal shift of `f`, then rewrite discrepancy to `apSumFrom`.
  simpa [out.g_eq] using
    (Tao2015.discrepancy_shift_add_mul_eq_natAbs_apSumFrom_mul
      (f := f) (d := out.d) (m := out.m) (n := n))

/-!
### Congruence helpers for the reduced sequence

Even though `out.g` is definitionally equal to the shift `fun k => f (k + out.m*out.d)` via
`out.g_eq`, it is often useful to have *named* `↔` lemmas that let downstream stages rewrite whole
predicates (boundedness/unboundedness/witness forms) without manually unfolding.

These are intentionally tiny; they exist purely to reduce proof friction in later stages.
-/

/-- Fixed-step large-discrepancy predicate for `out.g` rewritten to the literal shift of `f`. -/
theorem hasDiscrepancyAtLeastAlong_iff_shift (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔
      HasDiscrepancyAtLeastAlong (fun k => f (k + out.m * out.d)) out.d C := by
  simp [HasDiscrepancyAtLeastAlong, out.g_eq]

/-- Large discrepancy for the reduced sequence is the same as a large *offset* discrepancy witness
for the original sequence.

This is a consumer-facing wrapper around
`Tao2015.hasDiscrepancyAtLeastAlong_shift_add_mul_iff_exists_discOffset_gt` rewritten using
`out.g_eq`.
-/
theorem hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔
      (∃ n : ℕ, discOffset f out.d out.m n > C) := by
  -- Rewrite `out.g` to the literal shift and apply the general shift→offset lemma.
  simpa [out.g_eq] using
    (Tao2015.hasDiscrepancyAtLeastAlong_shift_add_mul_iff_exists_discOffset_gt
      (f := f) (d := out.d) (m := out.m) (C := C))

/-- `natAbs` (sum-level) version of `hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt`. -/
theorem hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔
      (∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > C) := by
  simpa [discOffset] using
    (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) (C := C))

/-- Fixed-step large discrepancy for the reduced sequence rewritten to the affine nucleus `apSumFrom`.

This is the `apSumFrom` analogue of `hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt`.
It is often the cleanest witness form to pass to later stages, since many reductions are stated
in terms of the affine-tail nucleus rather than offsets.
-/
theorem hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_mul_gt (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔
      (∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- Rewrite `apSum out.g` to a shifted sum (via `out.g_eq`), then into `apSumFrom`.
    simpa [HasDiscrepancyAtLeastAlong, out.g_eq,
      Tao2015.apSum_shift_add_mul_eq_apSumFrom_mul (f := f) (d := out.d) (m := out.m) (n := n)] using hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- Reverse direction: rewrite `apSumFrom` back to the shifted sum, then to `out.g`.
    simpa [HasDiscrepancyAtLeastAlong, out.g_eq,
      Tao2015.apSum_shift_add_mul_eq_apSumFrom_mul (f := f) (d := out.d) (m := out.m) (n := n)] using hn

/-- Promote a fixed-step discrepancy witness for the reduced sequence to the global predicate
`HasDiscrepancyAtLeast`.

This is just `HasDiscrepancyAtLeastAlong.toHasDiscrepancyAtLeast` specialized to the step size
`out.d` bundled in the reduction output.
-/
theorem hasDiscrepancyAtLeast_of_hasDiscrepancyAtLeastAlong (out : ReductionOutput f) (C : ℕ)
    (h : HasDiscrepancyAtLeastAlong out.g out.d C) :
    HasDiscrepancyAtLeast out.g C := by
  exact HasDiscrepancyAtLeastAlong.toHasDiscrepancyAtLeast (f := out.g) (d := out.d) (C := C)
    out.hd h

/-- Extract an explicit `apSumOffset` witness from a fixed-step discrepancy witness for `out.g`.

This is a convenience wrapper around
`hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt`.
-/
theorem exists_natAbs_apSumOffset_gt_of_hasDiscrepancyAtLeastAlong (out : ReductionOutput f) (C : ℕ)
    (h : HasDiscrepancyAtLeastAlong out.g out.d C) :
    ∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > C :=
  (out.hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt (f := f) (C := C)).1 h

/-- Build a fixed-step discrepancy witness for `out.g` from an explicit `apSumOffset` witness.

This is the reverse direction of `exists_natAbs_apSumOffset_gt_of_hasDiscrepancyAtLeastAlong`.
-/
theorem hasDiscrepancyAtLeastAlong_of_exists_natAbs_apSumOffset_gt (out : ReductionOutput f) (C : ℕ)
    (h : ∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > C) :
    HasDiscrepancyAtLeastAlong out.g out.d C :=
  (out.hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt (f := f) (C := C)).2 h

/-- Inequality-orientation convenience: rewrite large discrepancy for `out.g` into a witness of the
form `C < discOffset …`.
-/
theorem hasDiscrepancyAtLeastAlong_iff_exists_discOffset_lt (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔ (∃ n : ℕ, C < discOffset f out.d out.m n) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using
    (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) (C := C))

/-- Named forward direction of `hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt`. -/
theorem exists_discOffset_gt_of_hasDiscrepancyAtLeastAlong (out : ReductionOutput f) (C : ℕ)
    (h : HasDiscrepancyAtLeastAlong out.g out.d C) :
    ∃ n : ℕ, discOffset f out.d out.m n > C :=
  (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) (C := C)).1 h

/-- Named backward direction of `hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt`. -/
theorem hasDiscrepancyAtLeastAlong_of_exists_discOffset_gt (out : ReductionOutput f) (C : ℕ)
    (h : ∃ n : ℕ, discOffset f out.d out.m n > C) :
    HasDiscrepancyAtLeastAlong out.g out.d C :=
  (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) (C := C)).2 h

/-- Rewrite `HasDiscrepancyAtLeastAlong` for the reduced sequence into a `discrepancy` witness.

This is just the generic lemma `HasDiscrepancyAtLeastAlong.iff_exists_discrepancy_gt`
instantiated at `(out.g, out.d)`.
-/
theorem hasDiscrepancyAtLeastAlong_iff_exists_discrepancy_gt (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔ (∃ n : ℕ, discrepancy out.g out.d n > C) := by
  simpa using
    (HasDiscrepancyAtLeastAlong.iff_exists_discrepancy_gt (f := out.g) (d := out.d) (C := C))

/-- Transfer a strict-inequality discrepancy witness for the reduced sequence to an offset-discrepancy
witness for the original sequence.

This is just `out.discrepancy_eq_discOffset` repackaged with `∃`.
-/
theorem exists_discOffset_gt_of_exists_discrepancy_gt (out : ReductionOutput f) (C : ℕ)
    (h : ∃ n : ℕ, discrepancy out.g out.d n > C) :
    ∃ n : ℕ, discOffset f out.d out.m n > C := by
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hn

/-- Transfer a strict-inequality offset-discrepancy witness for the original sequence to a
strict-inequality discrepancy witness for the reduced sequence.

This is the reverse direction of `exists_discOffset_gt_of_exists_discrepancy_gt`.
-/
theorem exists_discrepancy_gt_of_exists_discOffset_gt (out : ReductionOutput f) (C : ℕ)
    (h : ∃ n : ℕ, discOffset f out.d out.m n > C) :
    ∃ n : ℕ, discrepancy out.g out.d n > C := by
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hn

/-- Iff form of `exists_discOffset_gt_of_exists_discrepancy_gt` / `exists_discrepancy_gt_of_exists_discOffset_gt`. -/
theorem exists_discrepancy_gt_iff_exists_discOffset_gt (out : ReductionOutput f) (C : ℕ) :
    (∃ n : ℕ, discrepancy out.g out.d n > C) ↔ (∃ n : ℕ, discOffset f out.d out.m n > C) := by
  constructor
  · intro h
    exact out.exists_discOffset_gt_of_exists_discrepancy_gt (f := f) (C := C) h
  · intro h
    exact out.exists_discrepancy_gt_of_exists_discOffset_gt (f := f) (C := C) h

/-- Iff form of the `<`-oriented witness `∃ n, C < ...`. -/
theorem exists_discrepancy_lt_iff_exists_discOffset_lt (out : ReductionOutput f) (C : ℕ) :
    (∃ n : ℕ, C < discrepancy out.g out.d n) ↔ (∃ n : ℕ, C < discOffset f out.d out.m n) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hn

/-- Uniform “arbitrarily large discrepancy” witness form for the reduced sequence `out.g` rewritten
into the corresponding witness form for the bundled offset discrepancies.

This is a convenience lemma: stage-2 deliverables are often stated as
`∀ B, ∃ n, discOffset ... > B`, while the downstream unboundedness APIs for `out.g` are phrased
in terms of `discrepancy out.g out.d`.
-/
theorem forall_exists_discrepancy_gt_iff_forall_exists_discOffset_gt (out : ReductionOutput f) :
    (∀ B : ℕ, ∃ n : ℕ, discrepancy out.g out.d n > B) ↔
      (∀ B : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > B) := by
  constructor
  · intro h B
    rcases h B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hn
  · intro h B
    rcases h B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hn

/-- `<`-oriented version of `forall_exists_discrepancy_gt_iff_forall_exists_discOffset_gt`. -/
theorem forall_exists_discrepancy_lt_iff_forall_exists_discOffset_lt (out : ReductionOutput f) :
    (∀ B : ℕ, ∃ n : ℕ, B < discrepancy out.g out.d n) ↔
      (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using (out.forall_exists_discrepancy_gt_iff_forall_exists_discOffset_gt (f := f))

/-!
### Unboundedness transport helpers

Later stages of the Tao2015 pipeline often prove (or assume) *unboundedness along a fixed step*.
For the reduced sequence `out.g`, the natural predicate is
`Tao2015.UnboundedDiscrepancyAlong out.g out.d`.

But stage-2 deliverables are frequently expressed in terms of the bundled offset discrepancies
`discOffset f out.d out.m`.  The following tiny lemmas let consumers move between these two
normal forms without redoing the `∀ B, ∃ n` bookkeeping.
-/

/-- Unbounded discrepancy along `out.d` for the reduced sequence rewritten into the corresponding
witness form for the bundled offset discrepancies (using `>` orientation). -/
theorem unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt (out : ReductionOutput f) :
    Tao2015.UnboundedDiscrepancyAlong out.g out.d ↔
      (∀ B : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > B) := by
  -- Unfold unboundedness into the witness form for `discrepancy`, then use the stage-1 rewrite.
  have h₁ :
      Tao2015.UnboundedDiscrepancyAlong out.g out.d ↔
        (∀ B : ℕ, ∃ n : ℕ, discrepancy out.g out.d n > B) := by
    simpa using (Tao2015.UnboundedDiscrepancyAlong.iff_forall_exists_discrepancy_gt
      (f := out.g) (d := out.d))
  -- Now rewrite the witness form using the bundled offset discrepancies.
  simpa [h₁] using (out.forall_exists_discrepancy_gt_iff_forall_exists_discOffset_gt (f := f))

/-- `<`-oriented version of `unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt`. -/
theorem unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (out : ReductionOutput f) :
    Tao2015.UnboundedDiscrepancyAlong out.g out.d ↔
      (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) := by
  -- `a > b` is notation for `b < a`.
  simpa [Tao2015.UnboundedDiscrepancyAlong, gt_iff_lt] using
    (out.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt (f := f))

/-- If the bundled offset discrepancies are unbounded (witness form), then the reduced sequence is
unbounded along the bundled step size.

This is the forward direction of `unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt`,
recorded with a convenient name.
-/
theorem unboundedDiscrepancyAlong_of_forall_exists_discOffset_gt (out : ReductionOutput f)
    (h : ∀ B : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > B) :
    Tao2015.UnboundedDiscrepancyAlong out.g out.d :=
  (out.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt (f := f)).2 h

/-- Conversely, unboundedness of the reduced sequence along `out.d` implies the bundled offset
family has arbitrarily large witnesses.

This is the reverse direction of `unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt`,
recorded with a convenient name.
-/
theorem forall_exists_discOffset_gt_of_unboundedDiscrepancyAlong (out : ReductionOutput f)
    (h : Tao2015.UnboundedDiscrepancyAlong out.g out.d) :
    ∀ B : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > B :=
  (out.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt (f := f)).1 h

/-- Uniform `≤` bounds for discrepancies of `out.g` rewritten to the literal shift of `f`. -/
theorem forall_discrepancy_le_iff_shift (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, discrepancy out.g out.d n ≤ B) ↔
      (∀ n : ℕ, discrepancy (fun k => f (k + out.m * out.d)) out.d n ≤ B) := by
  simp [out.g_eq]

/-- Uniform `<` bounds for discrepancies of `out.g` rewritten to the literal shift of `f`. -/
theorem forall_discrepancy_lt_iff_shift (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, discrepancy out.g out.d n < B) ↔
      (∀ n : ℕ, discrepancy (fun k => f (k + out.m * out.d)) out.d n < B) := by
  simp [out.g_eq]

/-- Uniform `≤` bounds for discrepancies of the reduced sequence rewritten to uniform `≤` bounds
for the bundled offset discrepancies.

This is the most common consumer-facing form: later stages frequently bound the offset discrepancy
family `discOffset f out.d out.m` and want to immediately treat it as a bound on `out.g`.
-/
theorem forall_discrepancy_le_iff_forall_discOffset_le (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, discrepancy out.g out.d n ≤ B) ↔ (∀ n : ℕ, discOffset f out.d out.m n ≤ B) := by
  constructor
  · intro h n
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using h n
  · intro h n
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using h n

/-- Named forward direction of `forall_discrepancy_le_iff_forall_discOffset_le`. -/
theorem forall_discOffset_le_of_forall_discrepancy_le (out : ReductionOutput f) (B : ℕ)
    (h : ∀ n : ℕ, discrepancy out.g out.d n ≤ B) :
    ∀ n : ℕ, discOffset f out.d out.m n ≤ B := by
  intro n
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using h n

/-- Named backward direction of `forall_discrepancy_le_iff_forall_discOffset_le`. -/
theorem forall_discrepancy_le_of_forall_discOffset_le (out : ReductionOutput f) (B : ℕ)
    (h : ∀ n : ℕ, discOffset f out.d out.m n ≤ B) :
    ∀ n : ℕ, discrepancy out.g out.d n ≤ B := by
  intro n
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using h n

/-- Uniform `<` bounds for discrepancies of the reduced sequence rewritten to uniform `<` bounds
for the bundled offset discrepancies. -/
theorem forall_discrepancy_lt_iff_forall_discOffset_lt (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, discrepancy out.g out.d n < B) ↔ (∀ n : ℕ, discOffset f out.d out.m n < B) := by
  constructor
  · intro h n
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using h n
  · intro h n
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using h n

/-- A strict-inequality version of the stage-1 discrepancy contract.

This is derived from the definitional rewrite `out.discrepancy_eq_discOffset`.
-/
theorem contract_discrepancy_lt (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n, discOffset f out.d out.m n < B) :
    ∀ n, discrepancy out.g out.d n < B := by
  intro n
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n

/-- Reverse direction of `contract_discrepancy_lt`: a strict discrepancy bound for the reduced
sequence implies the same strict bound for the bundled offset discrepancies. -/
theorem contract_discOffset_lt (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n, discrepancy out.g out.d n < B) :
    ∀ n, discOffset f out.d out.m n < B := by
  intro n
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n

/-- Iff form of `contract_discrepancy_lt` / `contract_discOffset_lt`. -/
@[deprecated (since := "2026-03-09")]
theorem forall_discrepancy_lt_iff_forall_discOffset_lt' (out : ReductionOutput f) (B : ℕ) :
    (∀ n, discrepancy out.g out.d n < B) ↔ (∀ n, discOffset f out.d out.m n < B) :=
  out.forall_discrepancy_lt_iff_forall_discOffset_lt (f := f) (B := B)

/-!
### Packaging uniform bounds as `ContextAlong`

Downstream reductions often want to treat the reduced sequence `out.g` as a black box that is
known to have bounded discrepancy along the *fixed* step size `out.d`.

The record `ContextAlong` is the fixed-step analogue of `Context`; these helpers let later stages
construct (and deconstruct) a `ContextAlong` using bounds that are naturally stated for the
bundled offset discrepancy family `discOffset f out.d out.m`.
-/

/-- Build a `ContextAlong` for the reduced sequence from a uniform `discOffset` bound.

This is the most common “consumer” packaging step: once a reduction bounds the offset discrepancies
of the original sequence, it can immediately regard the reduced sequence as having bounded
fixed-step discrepancy.
-/
def contextAlong_of_forall_discOffset_le (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, discOffset f out.d out.m n ≤ B) :
    ContextAlong out.g out.d := by
  refine ⟨B, ?_⟩
  intro n
  exact (out.forall_discrepancy_le_of_forall_discOffset_le (f := f) (B := B) hB) n

/-- Build a `ContextAlong` for the reduced sequence `out.g` from a *global* `Context f`.

This is a common situation in the Tao2015 pipeline: a stage assumes bounded discrepancy for the
original sign sequence `f` (in the `Context` normal form), then introduces a shifted reduction
output `out` and immediately needs a fixed-step boundedness record for the reduced sequence.

The bound degrades by a factor 2 because offset sums are differences of two prefix sums.
-/
def contextAlong_of_context (out : ReductionOutput f) (ctx : Context f) :
    ContextAlong out.g out.d := by
  refine ⟨ctx.B + ctx.B, ?_⟩
  intro n
  -- Bound the offset discrepancy using the global context for `f`, then rewrite via the stage-1
  -- discrepancy contract.
  have h := ctx.bound_discOffset (f := f) (d := out.d) (m := out.m) (n := n) out.hd
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using h

/-- A global boundedness `Context f` gives a uniform bound on the offset discrepancy family bundled
in `out`.

This is just `Context.bound_discOffset` specialized to the parameters carried by `out`.
-/
theorem forall_discOffset_le_of_context (out : ReductionOutput f) (ctx : Context f) :
    ∀ n : ℕ, discOffset f out.d out.m n ≤ ctx.B + ctx.B := by
  intro n
  exact ctx.bound_discOffset (f := f) (d := out.d) (m := out.m) (n := n) out.hd

/-- A global boundedness `Context f` gives a uniform bound on fixed-step discrepancies of the
reduced sequence `out.g`.

This is a one-line wrapper around `forall_discOffset_le_of_context` plus the stage-1 discrepancy
contract `out.discrepancy_eq_discOffset`.
-/
theorem forall_discrepancy_le_of_context (out : ReductionOutput f) (ctx : Context f) :
    ∀ n : ℕ, discrepancy out.g out.d n ≤ ctx.B + ctx.B := by
  intro n
  have h : discOffset f out.d out.m n ≤ ctx.B + ctx.B :=
    out.forall_discOffset_le_of_context (f := f) ctx n
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using h

/-- Extract the induced `discOffset` bound from a `ContextAlong` for the reduced sequence. -/
theorem forall_discOffset_le_of_contextAlong (out : ReductionOutput f) (ctx : ContextAlong out.g out.d) :
    ∀ n : ℕ, discOffset f out.d out.m n ≤ ctx.B := by
  intro n
  -- Rewrite `discOffset` to a `discrepancy out.g` statement and apply the context bound.
  have : discrepancy out.g out.d n ≤ ctx.B := ctx.bound_discrepancy (f := out.g) (d := out.d) n
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using this

/-- Existential packaging: a `ContextAlong` for the reduced sequence provides a uniform bound on the
bundled offset discrepancies.

This is a tiny helper (often used with `rcases`) that avoids having to separately write `⟨ctx.B, …⟩`.
-/
theorem exists_forall_discOffset_le_of_contextAlong (out : ReductionOutput f)
    (ctx : ContextAlong out.g out.d) :
    ∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B := by
  refine ⟨ctx.B, ?_⟩
  exact out.forall_discOffset_le_of_contextAlong (f := f) ctx

/-!
### Unboundedness rewrites

Later stages often want to switch between “arbitrarily large discrepancy” phrased for the reduced
sequence `out.g` and the equivalent statements phrased for the bundled offset discrepancy family
`discOffset f out.d out.m`.

These are pure pipeline glue: they just package existing lemmas with the parameters bundled in a
`ReductionOutput`.
-/

/-- Arbitrarily large discrepancy along `out.d` for `out.g` is equivalent to unbounded discrepancy
along that fixed step size.

This is just a specialization of
`HasDiscrepancyAtLeastAlong.forall_hasDiscrepancyAtLeastAlong_iff_unboundedDiscrepancyAlong`.
-/
theorem forall_hasDiscrepancyAtLeastAlong_iff_unboundedDiscrepancyAlong (out : ReductionOutput f) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) ↔
      Tao2015.UnboundedDiscrepancyAlong out.g out.d := by
  simpa using
    (HasDiscrepancyAtLeastAlong.forall_hasDiscrepancyAtLeastAlong_iff_unboundedDiscrepancyAlong
      (g := out.g) (d := out.d))

/-- Arbitrarily large discrepancy along `out.d` for `out.g` rewritten into a family of strict
inequalities for `discOffset f out.d out.m`.
-/
theorem forall_hasDiscrepancyAtLeastAlong_iff_forall_exists_discOffset_gt (out : ReductionOutput f) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) ↔
      (∀ C : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > C) := by
  constructor
  · intro h C
    exact (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) (C := C)).1 (h C)
  · intro h C
    exact (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) (C := C)).2 (h C)

/-- Boundedness along the reduced step size is equivalent to boundedness of the corresponding
offset discrepancy family.

This is the `∃B,∀n` existential form corresponding to
`forall_discrepancy_le_iff_forall_discOffset_le`.
-/
theorem boundedDiscrepancyAlong_iff_boundedDiscOffset (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d ↔ ∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B := by
  constructor
  · intro hb
    rcases hb with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- Convert the bound on `out.g` to a bound on `discOffset`.
    have : discrepancy out.g out.d n ≤ B := hB n
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using this
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    exact out.forall_discrepancy_le_of_forall_discOffset_le (f := f) (B := B) hB

/-- The stage-1 AP-sum contract in the natural consumer-facing form.

This is just the record field `out.apSum_contract` with parameters specialized to `out`.
-/
theorem apSum_eq_apSumOffset (out : ReductionOutput f) (n : ℕ) :
    apSum out.g out.d n = apSumOffset f out.d out.m n := by
  simpa using (out.apSum_contract n)

/-- Unbounded discrepancy along `out.d` rewritten as the *negation* of a uniform offset bound.

This is a convenient normal form for later reductions: to prove unboundedness for the reduced
sequence it suffices to show that the offset discrepancy family `discOffset f out.d out.m` has no
uniform bound.
-/
theorem unboundedDiscrepancyAlong_iff_not_exists_forall_discOffset_le (out : ReductionOutput f) :
    Tao2015.UnboundedDiscrepancyAlong out.g out.d ↔
      ¬ (∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B) := by
  -- Convert unboundedness into a `¬ BoundedDiscrepancyAlong` statement, and rewrite boundedness
  -- using `boundedDiscrepancyAlong_iff_boundedDiscOffset`.
  have h₁ : Tao2015.UnboundedDiscrepancyAlong out.g out.d ↔ ¬ BoundedDiscrepancyAlong out.g out.d :=
    UnboundedDiscrepancyAlong.iff_not_boundedDiscrepancyAlong (f := out.g) (d := out.d)
  have h₂ : (¬ BoundedDiscrepancyAlong out.g out.d) ↔
      ¬ (∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B) := by
    simpa using not_congr (out.boundedDiscrepancyAlong_iff_boundedDiscOffset (f := f))
  exact h₁.trans h₂

/-- Unboundedness along the reduced step `out.d` rewritten to the literal shift of `f`. -/
theorem unboundedDiscrepancyAlong_iff_shift (out : ReductionOutput f) :
    Tao2015.UnboundedDiscrepancyAlong out.g out.d ↔
      Tao2015.UnboundedDiscrepancyAlong (fun k => f (k + out.m * out.d)) out.d := by
  simp [Tao2015.UnboundedDiscrepancyAlong, out.g_eq]

/-- Unbounded discrepancy along the reduced step is equivalent to unbounded *offset* discrepancy
for the original sequence.

This is just `out.discrepancy_eq_discOffset` repackaged under the witness predicate
`UnboundedDiscrepancyAlong`.
-/
theorem unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (out : ReductionOutput f) :
    Tao2015.UnboundedDiscrepancyAlong out.g out.d ↔
      (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) := by
  constructor
  · intro h B
    rcases h B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hn
  · intro h B
    rcases h B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hn

/-- `>`-oriented variant of `unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt`.

This is just a syntactic convenience wrapper: later stages often state unboundedness witnesses
as `discOffset … > B`.
-/
theorem unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt (out : ReductionOutput f) :
    Tao2015.UnboundedDiscrepancyAlong out.g out.d ↔
      (∀ B : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > B) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using
    (out.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (f := f))

/-- Unbounded discrepancy along the reduced step size is equivalent to unbounded offset discrepancy
for the original sequence, stated using the `UnboundedDiscOffset` predicate.

This is a pure “predicate packaging” helper: it just unfolds `UnboundedDiscOffset` and uses
`unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt`.
-/
theorem unboundedDiscrepancyAlong_iff_unboundedDiscOffset (out : ReductionOutput f) :
    Tao2015.UnboundedDiscrepancyAlong out.g out.d ↔ Tao2015.UnboundedDiscOffset f out.d out.m := by
  -- Both sides are the same `∀ B, ∃ n, B < ...` witness form, rewritten via the stage-1 contract.
  simpa [Tao2015.UnboundedDiscOffset] using
    (out.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (f := f))

/-- `>`-oriented witness form of `unboundedDiscrepancyAlong_iff_unboundedDiscOffset`.

This is convenient when stage-2 deliverables are stated as `discOffset … > B`.
-/
theorem unboundedDiscrepancyAlong_iff_unboundedDiscOffset_gt (out : ReductionOutput f) :
    Tao2015.UnboundedDiscrepancyAlong out.g out.d ↔
      (∀ B : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > B) := by
  -- `UnboundedDiscOffset` is defined using `<`, but we can freely swap orientation.
  simpa [Tao2015.UnboundedDiscOffset, gt_iff_lt] using
    (out.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt (f := f))

/-- `>`-oriented variant of unboundedness along the reduced fixed step, stated using
`discrepancy out.g out.d` rather than `discOffset`.

This is occasionally the cleanest interface for downstream stages that do not want to mention
the original sequence `f` at all.
-/
theorem unboundedDiscrepancyAlong_iff_forall_exists_discrepancy_gt (out : ReductionOutput f) :
    Tao2015.UnboundedDiscrepancyAlong out.g out.d ↔
      (∀ B : ℕ, ∃ n : ℕ, discrepancy out.g out.d n > B) := by
  -- This is just the definitional symmetry `B < ...` vs `... > B`.
  simp [Tao2015.UnboundedDiscrepancyAlong, gt_iff_lt]

/-- `Int.natAbs (apSumOffset …)` witness form of
`unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt`.

Downstream stages sometimes work directly with `apSumOffset` bounds before wrapping them into
`discOffset`.
-/
theorem unboundedDiscrepancyAlong_iff_forall_exists_natAbs_apSumOffset_lt (out : ReductionOutput f) :
    Tao2015.UnboundedDiscrepancyAlong out.g out.d ↔
      (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n)) := by
  -- Just unfold `discOffset` in the previous lemma.
  simpa [discOffset] using (out.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (f := f))

/-- Reverse orientation of the AP-sum bridge field `apSum_contract`. -/
theorem apSumOffset_eq_apSum (out : ReductionOutput f) (n : ℕ) :
    apSumOffset f out.d out.m n = apSum out.g out.d n := by
  simpa using (out.apSum_contract n).symm

/-- Reverse orientation of the stage-1 discrepancy contract.

We prove this directly from `out.apSum_contract` to avoid any forward-reference to
`discrepancy_eq_discOffset` (which appears later in the file).
-/
theorem discOffset_eq_discrepancy (out : ReductionOutput f) (n : ℕ) :
    discOffset f out.d out.m n = discrepancy out.g out.d n := by
  -- Both sides are definitional wrappers around `Int.natAbs (apSum ...)`.
  simp [discOffset, discrepancy, out.apSum_contract]

/-- Derived `≤`-contract for discrepancies, proved from `out.apSum_contract`.

This duplicates the intent of the data field `ReductionOutput.contract_discrepancy_le`, but as a
*theorem* so consumers can avoid depending on that field explicitly (useful when constructing
`ReductionOutput`s by hand and later refactoring the record fields).
-/
theorem contract_discrepancy_le_derived (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, discOffset f out.d out.m n ≤ B) :
    ∀ n : ℕ, discrepancy out.g out.d n ≤ B := by
  intro n
  -- Rewrite `discOffset` into `discrepancy` using the stage-1 contract.
  simpa [out.discOffset_eq_discrepancy (f := f) (n := n)] using hB n

/-- Reverse `≤`-contract: a bound on the reduced discrepancies implies a bound on the bundled
offset discrepancies.

This is the converse direction of `contract_discrepancy_le_derived`.
-/
theorem contract_discOffset_le_derived (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, discrepancy out.g out.d n ≤ B) :
    ∀ n : ℕ, discOffset f out.d out.m n ≤ B := by
  intro n
  -- Rewrite `discOffset` to `discrepancy` using the stage-1 contract.
  simpa [out.discOffset_eq_discrepancy (f := f) (n := n)] using hB n

/-- Reverse strict-inequality contract: `discrepancy(out.g)` witnesses transfer back to
`discOffset` witnesses.

This is useful when later stages produce large discrepancy along the reduced sequence and we want
a corresponding offset discrepancy witness for the original sequence.
-/
theorem contract_discOffset_lt_of_forall_discrepancy_lt (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, discrepancy out.g out.d n < B) :
    ∀ n : ℕ, discOffset f out.d out.m n < B := by
  intro n
  simpa [out.discOffset_eq_discrepancy (f := f) (n := n)] using hB n

/-- Sum-level (`Int.natAbs`) discrepancy contract.

This is often the most convenient form for a consumer lemma: it avoids the wrapper
`discOffset` and speaks directly about the nucleus `apSumOffset`.
-/
theorem contract_natAbs_apSumOffset_le (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ B) :
    ∀ n : ℕ, discrepancy out.g out.d n ≤ B := by
  intro n
  -- Rewrite `discrepancy` to the nucleus `natAbs (apSum ...)` and then apply the AP-sum contract.
  -- Finally use the assumed nucleus-level bound.
  simpa [discrepancy, discOffset, out.apSum_contract] using hB n

/-- Strict-inequality version of `contract_natAbs_apSumOffset_le`.

We name it `contract_discrepancy_lt_of_forall_natAbs_apSumOffset_lt` to avoid colliding with the
reverse-direction lemma `contract_natAbs_apSumOffset_lt` later in this file.
-/
theorem contract_discrepancy_lt_of_forall_natAbs_apSumOffset_lt (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) < B) :
    ∀ n : ℕ, discrepancy out.g out.d n < B := by
  intro n
  -- Same proof as the `≤` version; we just keep the strict inequality.
  simpa [discrepancy, discOffset, out.apSum_contract] using hB n

/-!
### Transporting boundedness contexts through a `ReductionOutput`

A common Track C pattern:
- start from a global boundedness hypothesis `BoundedDiscrepancy f` (packaged as `Tao2015.Context f`)
- shift to a derived sequence `out.g`
- continue working along the fixed step size `out.d`.

The next lemma packages that pattern as a one-liner.
-/

/-- If `f` has globally bounded discrepancy (in the `Tao2015.Context` sense), then the reduced
sequence `out.g` has bounded discrepancy along the single step size `out.d`.

The bound constant is the same `2*B` that appears in `Context.bound_discrepancy_shift_add`.
-/
theorem contextAlong_of_context (out : ReductionOutput f) (ctx : Tao2015.Context f) :
    Tao2015.ContextAlong out.g out.d := by
  refine ⟨ctx.B + ctx.B, ?_⟩
  intro n
  -- Reduce to the literal shift form and apply the bound from `ctx`.
  simpa [out.g_eq] using
    (ctx.bound_discrepancy_shift_add (f := f) (d := out.d) (m := out.m) (n := n) out.hd)

/-!
### Re-associating offsets through a `ReductionOutput`

When composing multiple Track C stages, offsets naturally add.
`Tao2015.discOffset_add` lets us peel off a leading offset by shifting the sequence.
The following wrappers specialize this to the shift packaged in `out`.
-/

/-- Re-associate an offset past the reduction output, at the `apSumOffset` level.

This is `Tao2015.apSumOffset_add` rewritten using `out.g_eq`.
-/
theorem apSumOffset_add_out (out : ReductionOutput f) (m₂ n : ℕ) :
    apSumOffset f out.d (out.m + m₂) n = apSumOffset out.g out.d m₂ n := by
  -- Peel off the first offset using the general lemma, then rewrite the shifted sequence to `out.g`.
  simpa [out.g_eq] using
    (Tao2015.apSumOffset_add (f := f) (d := out.d) (m₁ := out.m) (m₂ := m₂) (n := n))

/-- Re-associate an offset past the reduction output, at the `discOffset` level.

This is `Tao2015.discOffset_add` rewritten using `out.g_eq`.
-/
theorem discOffset_add_out (out : ReductionOutput f) (m₂ n : ℕ) :
    discOffset f out.d (out.m + m₂) n = discOffset out.g out.d m₂ n := by
  simpa [out.g_eq] using
    (Tao2015.discOffset_add (f := f) (d := out.d) (m₁ := out.m) (m₂ := m₂) (n := n))

/-- Re-associate an offset past the reduction output, at the nucleus (`Int.natAbs`) level.

This is the `Int.natAbs` analogue of `discOffset_add_out`.
-/
theorem natAbs_apSumOffset_add_out (out : ReductionOutput f) (m₂ n : ℕ) :
    Int.natAbs (apSumOffset f out.d (out.m + m₂) n) =
      Int.natAbs (apSumOffset out.g out.d m₂ n) := by
  -- Peel off the leading offset, then rewrite the shifted sequence to `out.g`.
  simpa [out.g_eq] using
    (Tao2015.natAbs_apSumOffset_add (f := f) (d := out.d) (m₁ := out.m) (m₂ := m₂) (n := n))

/-- Re-associate an affine-tail (`apSumFrom`) past the reduction output.

This is the affine-nucleus analogue of `apSumOffset_add_out`/`discOffset_add_out`.
Informally: tail sums of `out.g` starting at `m₂*out.d` correspond to tail sums of `f`
starting at `(out.m+m₂)*out.d`.
-/
theorem apSumFrom_add_out (out : ReductionOutput f) (m₂ n : ℕ) :
    apSumFrom f ((out.m + m₂) * out.d) out.d n = apSumFrom out.g (m₂ * out.d) out.d n := by
  -- Rewrite both sides as homogeneous AP sums of shifted sequences.
  -- Then use `out.g_eq` and reassociate the addition in the index.
  simp [apSumFrom_eq_apSum_shift_add, out.g_eq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.add_mul, Nat.mul_add, Nat.mul_assoc]

/-- `Int.natAbs` form of `apSumFrom_add_out`. -/
theorem natAbs_apSumFrom_add_out (out : ReductionOutput f) (m₂ n : ℕ) :
    Int.natAbs (apSumFrom f ((out.m + m₂) * out.d) out.d n) =
      Int.natAbs (apSumFrom out.g (m₂ * out.d) out.d n) := by
  simp [out.apSumFrom_add_out (f := f) (m₂ := m₂) (n := n)]

/-!
### Consumer-facing rewrite lemmas

These are tiny wrappers around the fields of `ReductionOutput`. They make the interface feel like
an API rather than a record you have to destructure manually.
-/

/-- Rewrite `apSum` of the reduced sequence in terms of the affine nucleus for the original one. -/
theorem apSum_eq_apSumFrom_mul (out : ReductionOutput f) (n : ℕ) :
    apSum out.g out.d n = apSumFrom f (out.m * out.d) out.d n := by
  -- First use the stage-1 contract to get an offset sum, then rewrite the offset sum as affine.
  simpa [Tao2015.apSumOffset_eq_apSumFrom_mul] using
    (out.apSum_contract n)

/-- `Int.natAbs` form of `apSum_eq_apSumFrom_mul`.

This is a useful nucleus-level rewrite when downstream stages bound the affine-tail sums directly.
-/
theorem natAbs_apSum_eq_natAbs_apSumFrom_mul (out : ReductionOutput f) (n : ℕ) :
    Int.natAbs (apSum out.g out.d n) = Int.natAbs (apSumFrom f (out.m * out.d) out.d n) := by
  simp [out.apSum_eq_apSumFrom_mul (f := f) (n := n)]

/-- Rewrite `discrepancy out.g out.d` into the affine-tail nucleus for the original sequence.

This combines `discrepancy = natAbs(apSum …)` with `apSum_eq_apSumFrom_mul`.
-/
theorem discrepancy_eq_natAbs_apSumFrom_mul (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n = Int.natAbs (apSumFrom f (out.m * out.d) out.d n) := by
  simp [discrepancy, out.apSum_eq_apSumFrom_mul (f := f) (n := n)]

/-- Transfer a uniform nucleus-level bound on the affine-tail sums of `f` into a discrepancy bound
for the reduced sequence `out.g`.

This is the most common “consumer” contract when later stages produce bounds (or unboundedness)
statements formulated in terms of `apSumFrom`.
-/
theorem contract_discrepancy_le_of_forall_natAbs_apSumFrom_mul_le (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) ≤ B) :
    ∀ n : ℕ, discrepancy out.g out.d n ≤ B := by
  intro n
  simpa [out.discrepancy_eq_natAbs_apSumFrom_mul (f := f) (n := n)] using hB n

/-- Rewrite the offset AP sum bundled in `out` into the affine nucleus `apSumFrom`.

This is just `Tao2015.apSumOffset_eq_apSumFrom_mul` with `d,m` taken from `out`.
-/
theorem apSumOffset_eq_apSumFrom_mul (out : ReductionOutput f) (n : ℕ) :
    apSumOffset f out.d out.m n = apSumFrom f (out.m * out.d) out.d n := by
  simpa using (Tao2015.apSumOffset_eq_apSumFrom_mul (f := f) (d := out.d) (m := out.m) (n := n))

/-- `Int.natAbs` form of `apSumOffset_eq_apSumFrom_mul` for `out`.

This wrapper is useful when a later stage has bounds on `apSumFrom` and wants to transport them
back to `apSumOffset` without expanding the intermediate lemmas by hand.
-/
theorem natAbs_apSumOffset_eq_natAbs_apSumFrom_mul (out : ReductionOutput f) (n : ℕ) :
    Int.natAbs (apSumOffset f out.d out.m n) =
      Int.natAbs (apSumFrom f (out.m * out.d) out.d n) := by
  simp [out.apSumOffset_eq_apSumFrom_mul (f := f) (n := n)]

/-- Rewrite `discOffset` (the offset discrepancy wrapper bundled in `out`) into the affine nucleus.

This is the `discOffset` analogue of `apSumOffset_eq_apSumFrom_mul`.
-/
theorem discOffset_eq_natAbs_apSumFrom_mul (out : ReductionOutput f) (n : ℕ) :
    discOffset f out.d out.m n = Int.natAbs (apSumFrom f (out.m * out.d) out.d n) := by
  simp [discOffset, out.apSumOffset_eq_apSumFrom_mul (f := f) (n := n)]

/-- The stage-1 contract rewritten at the discrepancy level. -/
theorem discrepancy_eq_discOffset (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n = discOffset f out.d out.m n := by
  simp [discrepancy, discOffset, out.apSum_contract]

/-- Transfer uniform bounds on the reduced discrepancy back to bounds on the bundled offset discrepancy.

This is the reverse direction of `ReductionOutput.contract_discrepancy_le`.

Even though it is logically trivial (since `discrepancy out.g out.d n = discOffset ...`), having it
as a named lemma avoids repeated rewrites at call sites.
-/
theorem contract_discOffset_le (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, discrepancy out.g out.d n ≤ B) :
    ∀ n : ℕ, discOffset f out.d out.m n ≤ B := by
  intro n
  -- Rewrite `discOffset` into the reduced discrepancy and apply the bound.
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n

/-- Equivalence form of `contract_discrepancy_le` and `contract_discOffset_le`. -/
theorem forall_discrepancy_le_iff_forall_discOffset_le (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, discrepancy out.g out.d n ≤ B) ↔ (∀ n : ℕ, discOffset f out.d out.m n ≤ B) := by
  constructor
  · intro h
    exact out.contract_discOffset_le (f := f) B h
  · intro h
    exact out.contract_discrepancy_le B h

/-!
### Boundedness transfer helpers

The record field `contract_discrepancy_le` is stated in a “consumer-friendly” form:
if you already have *uniform bounds* on the offset discrepancies, you can immediately bound
`discrepancy out.g out.d`.

Often, though, downstream stages naturally speak in terms of the existential predicate
`BoundedDiscrepancyAlong`.  The following tiny lemmas let later stages move between
`BoundedDiscrepancyAlong out.g out.d` and “there exists a uniform bound on `discOffset f out.d out.m`”
without having to unfold wrappers by hand.
-/

/-- Bounded discrepancy along the reduced step is equivalent to bounded *offset* discrepancy
for the original sequence (existential form). -/
theorem boundedDiscrepancyAlong_iff_exists_forall_discOffset_le (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d ↔ (∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B) := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- rewrite the reduced discrepancy to the offset discrepancy
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n

/-- Forward direction of `boundedDiscrepancyAlong_iff_exists_forall_discOffset_le`. -/
theorem exists_forall_discOffset_le_of_boundedDiscrepancyAlong (out : ReductionOutput f)
    (h : BoundedDiscrepancyAlong out.g out.d) :
    ∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B :=
  (out.boundedDiscrepancyAlong_iff_exists_forall_discOffset_le (f := f)).1 h

/-- Backward direction of `boundedDiscrepancyAlong_iff_exists_forall_discOffset_le`. -/
theorem boundedDiscrepancyAlong_of_exists_forall_discOffset_le (out : ReductionOutput f)
    (h : ∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B) :
    BoundedDiscrepancyAlong out.g out.d :=
  (out.boundedDiscrepancyAlong_iff_exists_forall_discOffset_le (f := f)).2 h

/-- Bounded discrepancy along the reduced step rewritten to the affine-tail nucleus `apSumFrom`.

This is the `apSumFrom` analogue of
`boundedDiscrepancyAlong_iff_exists_forall_discOffset_le`, using the bridge lemma
`Tao2015.discOffset_eq_natAbs_apSumFrom_mul`.
-/
theorem boundedDiscrepancyAlong_iff_exists_forall_natAbs_apSumFrom_mul_le (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d ↔
      (∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) ≤ B) := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- Rewrite `discrepancy out.g` to `discOffset f`, then rewrite `discOffset` to the affine nucleus.
    have : discOffset f out.d out.m n ≤ B := by
      simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n
    -- `discOffset = natAbs(apSumFrom ...)`.
    simpa [Tao2015.discOffset_eq_natAbs_apSumFrom_mul] using this
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- Convert the affine-nucleus bound back to `discOffset`, then to `discrepancy out.g`.
    have : discOffset f out.d out.m n ≤ B := by
      simpa [Tao2015.discOffset_eq_natAbs_apSumFrom_mul] using hB n
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using this

/-!
### Building a fixed-step discrepancy context from the reduction output

Downstream stages often prefer to work with the record `ContextAlong` rather than the existential
predicate `BoundedDiscrepancyAlong`.  The following helpers let a consumer build such a context
from a uniform offset-discrepancy bound (and conversely extract an offset bound from a context).

We also provide a common special case: if we start from a global `Context f` (uniform bounds for
all homogeneous AP sums of `f`), then the reduced sequence `out.g` automatically inherits a
fixed-step discrepancy context along `out.d`.

These are pure “pipeline glue”: the proofs are immediate from
`out.discrepancy_eq_discOffset` and the basic bound lemmas in `Tao2015.Context`.
-/

/-- A global `Context f` gives a uniform bound on the offset discrepancy bundled in `out`. -/
theorem forall_discOffset_le_of_context (out : ReductionOutput f) (ctx : Context f) :
    ∀ n : ℕ, discOffset f out.d out.m n ≤ ctx.B + ctx.B := by
  intro n
  exact ctx.bound_discOffset (f := f) (d := out.d) (m := out.m) (n := n) out.hd

/-- Build a fixed-step discrepancy context for `out.g` from a global `Context f`.

Intuitively: bounded discrepancy for *all* steps of `f` implies bounded discrepancy for the
particular step `out.d` of the shifted proxy sequence `out.g`.
-/
def contextAlong_of_context (out : ReductionOutput f) (ctx : Context f) : ContextAlong out.g out.d := by
  refine ⟨ctx.B + ctx.B, ?_⟩
  intro n
  -- Bound the literal shift, then rewrite it to `out.g`.
  have hshift : discrepancy (fun k => f (k + out.m * out.d)) out.d n ≤ ctx.B + ctx.B :=
    ctx.bound_discrepancy_shift_add (f := f) (d := out.d) (m := out.m) (n := n) out.hd
  simpa [out.g_eq] using hshift

/-- Build a `ContextAlong` for the reduced sequence from a uniform `discOffset` bound. -/
noncomputable def contextAlong_of_exists_forall_discOffset_le (out : ReductionOutput f)
    (h : ∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B) :
    ContextAlong out.g out.d := by
  classical
  refine ⟨Classical.choose h, ?_⟩
  intro n
  have hn : discOffset f out.d out.m n ≤ Classical.choose h :=
    Classical.choose_spec h n
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hn

/-- Extract a uniform `discOffset` bound from a `ContextAlong` for the reduced sequence. -/
theorem forall_discOffset_le_of_contextAlong (out : ReductionOutput f)
    (ctx : ContextAlong out.g out.d) :
    ∀ n : ℕ, discOffset f out.d out.m n ≤ ctx.B := by
  intro n
  -- Rewrite `discOffset` to `discrepancy out.g`, then apply the context bound.
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using (ctx.bound_discrepancy n)

/-- `BoundedDiscrepancyAlong` for the reduced sequence gives a `ContextAlong` for the reduced sequence. -/
theorem contextAlong_of_boundedDiscrepancyAlong (out : ReductionOutput f)
    (h : BoundedDiscrepancyAlong out.g out.d) :
    ContextAlong out.g out.d :=
  ContextAlong.ofBoundedDiscrepancyAlong (f := out.g) (d := out.d) h

/-- If the reduced sequence has a `ContextAlong`, then `BoundedDiscrepancyAlong` holds. -/
theorem boundedDiscrepancyAlong_of_contextAlong (out : ReductionOutput f)
    (ctx : ContextAlong out.g out.d) :
    BoundedDiscrepancyAlong out.g out.d :=
  ctx.toBoundedDiscrepancyAlong

/-- Transfer contract, stated directly in terms of `discOffset`.

This lemma is logically redundant (it follows from `discrepancy_eq_discOffset`), but it is a
useful consumer-facing normal form: many downstream stages will naturally produce uniform bounds
on `discOffset f out.d out.m` and want to immediately use them as bounds on the reduced
discrepancies.
-/
theorem contract_discrepancy_le_of_forall_discOffset_le (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, discOffset f out.d out.m n ≤ B) :
    ∀ n : ℕ, discrepancy out.g out.d n ≤ B := by
  intro n
  -- Rewrite to the offset discrepancy bound and apply `hB`.
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n

/-!
### Interop with the global boundedness context

Often we begin with a global boundedness hypothesis `BoundedDiscrepancy f` (or its bundled record
`Tao2015.Context f`) and then want to feed the resulting uniform bounds into a fixed-step
reduction output.

The following tiny lemmas record the common special case: any `Context f` gives a uniform bound on
`discOffset f out.d out.m`, and hence a uniform bound on the reduced discrepancies
`discrepancy out.g out.d`.
-/

/-- A global boundedness context bounds the offset discrepancies appearing in a `ReductionOutput`. -/
theorem forall_discOffset_le_of_context (out : ReductionOutput f) (ctx : Tao2015.Context f) :
    ∀ n : ℕ, discOffset f out.d out.m n ≤ ctx.B + ctx.B := by
  intro n
  exact ctx.bound_discOffset (f := f) (d := out.d) (m := out.m) (n := n) out.hd

/-- A global boundedness context bounds the reduced discrepancies in a `ReductionOutput`. -/
theorem forall_discrepancy_le_of_context (out : ReductionOutput f) (ctx : Tao2015.Context f) :
    ∀ n : ℕ, discrepancy out.g out.d n ≤ ctx.B + ctx.B := by
  intro n
  -- Bound the offset discrepancy using the global context, then transfer via the reduction output.
  have h₁ : discOffset f out.d out.m n ≤ ctx.B + ctx.B :=
    out.forall_discOffset_le_of_context (f := f) ctx n
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using h₁

/-- Bundled fixed-step context for the reduced sequence, built from a global `Context f`. -/
noncomputable def contextAlong_of_context (out : ReductionOutput f) (ctx : Tao2015.Context f) :
    ContextAlong out.g out.d := by
  classical
  refine ⟨ctx.B + ctx.B, ?_⟩
  intro n
  exact out.forall_discrepancy_le_of_context (f := f) ctx n

/-- Strict-inequality version of `contract_discrepancy_le_of_forall_discOffset_le`. -/
theorem contract_discrepancy_lt_of_forall_discOffset_lt (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, discOffset f out.d out.m n < B) :
    ∀ n : ℕ, discrepancy out.g out.d n < B := by
  intro n
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n

/-- Discrepancy of the reduced sequence rewritten as a `natAbs` bound on the original offset sum.

This is just `discrepancy_eq_discOffset` plus the definitional expansion
`discOffset = Int.natAbs (apSumOffset …)`.
-/
theorem discrepancy_eq_natAbs_apSumOffset (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n = Int.natAbs (apSumOffset f out.d out.m n) := by
  simp [out.discrepancy_eq_discOffset (f := f) (n := n), discOffset]

/-- Transfer contract in the `Int.natAbs (apSumOffset …)` normal form.

Downstream steps often prove bounds on `apSumOffset` first (before wrapping in `discOffset`).
This lemma lets them consume a `ReductionOutput` without doing the wrapper bookkeeping by hand.
-/
theorem contract_discrepancy_le_of_forall_natAbs_apSumOffset_le (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ B) :
    ∀ n : ℕ, discrepancy out.g out.d n ≤ B := by
  intro n
  -- Rewrite the target discrepancy to the underlying `Int.natAbs (apSum …)` bound.
  -- Then rewrite `apSum out.g` to `apSumOffset f` using the stage-1 contract.
  have hn : Int.natAbs (apSum out.g out.d n) ≤ B := by
    simpa [out.apSum_contract n] using hB n
  simpa [discrepancy] using hn

/-- Strict-inequality version of `contract_discrepancy_le_of_forall_natAbs_apSumOffset_le`. -/
theorem contract_discrepancy_lt_of_forall_natAbs_apSumOffset_lt (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) < B) :
    ∀ n : ℕ, discrepancy out.g out.d n < B := by
  intro n
  have hn : Int.natAbs (apSum out.g out.d n) < B := by
    simpa [out.apSum_contract n] using hB n
  simpa [discrepancy] using hn

/-- Transfer contract in the affine-tail (`apSumFrom`) normal form.

This is the `apSumFrom` analogue of `contract_discrepancy_le_of_forall_natAbs_apSumOffset_le`.
It is often the cleanest way to consume a `ReductionOutput`, since many later stages are
formulated directly in terms of the nucleus `apSumFrom`.
-/
theorem contract_discrepancy_le_of_forall_natAbs_apSumFrom_mul_le (out : ReductionOutput f)
    (B : ℕ)
    (hB : ∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) ≤ B) :
    ∀ n : ℕ, discrepancy out.g out.d n ≤ B := by
  intro n
  have hn : Int.natAbs (apSum out.g out.d n) ≤ B := by
    -- Rewrite the affine-tail bound into a bound on the reduced homogeneous AP sum.
    simpa [out.apSum_eq_apSumFrom_mul (f := f) (n := n)] using hB n
  simpa [discrepancy] using hn

/-- Strict-inequality version of `contract_discrepancy_le_of_forall_natAbs_apSumFrom_mul_le`. -/
theorem contract_discrepancy_lt_of_forall_natAbs_apSumFrom_mul_lt (out : ReductionOutput f)
    (B : ℕ)
    (hB : ∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) < B) :
    ∀ n : ℕ, discrepancy out.g out.d n < B := by
  intro n
  have hn : Int.natAbs (apSum out.g out.d n) < B := by
    simpa [out.apSum_eq_apSumFrom_mul (f := f) (n := n)] using hB n
  simpa [discrepancy] using hn

/-- Discrepancy of the reduced sequence rewritten in terms of `apSumFrom` for the original one. -/
theorem discrepancy_eq_natAbs_apSumFrom_mul (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n = Int.natAbs (apSumFrom f (out.m * out.d) out.d n) := by
  -- Combine `discrepancy_eq_discOffset` with the offset→affine bridge.
  calc
    discrepancy out.g out.d n = discOffset f out.d out.m n := out.discrepancy_eq_discOffset (f := f) n
    _ = Int.natAbs (apSumFrom f (out.m * out.d) out.d n) :=
      Tao2015.discOffset_eq_natAbs_apSumFrom_mul (f := f) (d := out.d) (m := out.m) (n := n)

/-- Uniform discrepancy bounds for the reduced sequence rewritten to the affine nucleus `apSumFrom`.

This is the `∀ n, … ≤ B` form corresponding to `discrepancy_eq_natAbs_apSumFrom_mul`.
-/
theorem forall_discrepancy_le_iff_forall_natAbs_apSumFrom_mul_le (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, discrepancy out.g out.d n ≤ B) ↔
      (∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) ≤ B) := by
  constructor <;> intro h n
  · simpa [out.discrepancy_eq_natAbs_apSumFrom_mul (f := f) (n := n)] using h n
  · -- Reverse direction: rewrite the affine nucleus back into the discrepancy wrapper.
    simpa [out.discrepancy_eq_natAbs_apSumFrom_mul (f := f) (n := n)] using h n

/-- Strict uniform discrepancy bounds rewritten to the affine nucleus `apSumFrom`. -/
theorem forall_discrepancy_lt_iff_forall_natAbs_apSumFrom_mul_lt (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, discrepancy out.g out.d n < B) ↔
      (∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) < B) := by
  constructor <;> intro h n
  · simpa [out.discrepancy_eq_natAbs_apSumFrom_mul (f := f) (n := n)] using h n
  · simpa [out.discrepancy_eq_natAbs_apSumFrom_mul (f := f) (n := n)] using h n

/-- Existential large-discrepancy witnesses rewritten to the affine nucleus `apSumFrom`. -/
theorem exists_discrepancy_gt_iff_exists_natAbs_apSumFrom_mul_gt (out : ReductionOutput f) (C : ℕ) :
    (∃ n : ℕ, discrepancy out.g out.d n > C) ↔
      (∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.discrepancy_eq_natAbs_apSumFrom_mul (f := f) (n := n)] using hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.discrepancy_eq_natAbs_apSumFrom_mul (f := f) (n := n)] using hn

/-- Reverse orientation of `discrepancy_eq_natAbs_apSumFrom_mul`.

This is occasionally convenient when a later stage produces a statement about the affine nucleus
`apSumFrom` but wants to rewrite it back into the `discrepancy` wrapper form.
-/
theorem natAbs_apSumFrom_mul_eq_discrepancy (out : ReductionOutput f) (n : ℕ) :
    Int.natAbs (apSumFrom f (out.m * out.d) out.d n) = discrepancy out.g out.d n := by
  simpa using (out.discrepancy_eq_natAbs_apSumFrom_mul (f := f) (n := n)).symm

/-- Reverse orientation of `apSum_eq_apSumFrom_mul`.

We keep this as a separate lemma (rather than making `apSum_eq_apSumFrom_mul` `[simp]` both ways)
so that `simp` does not accidentally create rewriting loops.
-/
theorem apSumFrom_mul_eq_apSum (out : ReductionOutput f) (n : ℕ) :
    apSumFrom f (out.m * out.d) out.d n = apSum out.g out.d n := by
  simpa using (out.apSum_eq_apSumFrom_mul (f := f) (n := n)).symm

/-- If discrepancies of the reduced sequence are uniformly bounded, then offset discrepancies of
`f` are uniformly bounded (same bound). -/
theorem contract_discOffset_le (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n, discrepancy out.g out.d n ≤ B) :
    ∀ n, discOffset f out.d out.m n ≤ B := by
  intro n
  -- Rewrite `discOffset` to `discrepancy` using the stage-1 contract, then apply the bound.
  simpa [(out.discrepancy_eq_discOffset (f := f) n).symm] using hB n

/-- Sum-level (`Int.natAbs`) consequence of `contract_discOffset_le`.

This is occasionally more convenient than working through the `discOffset` wrapper.
-/
theorem contract_natAbs_apSumOffset_le (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n, discrepancy out.g out.d n ≤ B) :
    ∀ n, Int.natAbs (apSumOffset f out.d out.m n) ≤ B := by
  intro n
  -- `discOffset = natAbs (apSumOffset ...)`.
  simpa [discOffset] using (out.contract_discOffset_le (f := f) (B := B) hB n)

/-- Strict-inequality version of `contract_natAbs_apSumOffset_le`. -/
theorem contract_natAbs_apSumOffset_lt (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n, discrepancy out.g out.d n < B) :
    ∀ n, Int.natAbs (apSumOffset f out.d out.m n) < B := by
  intro n
  -- Rewrite `discrepancy` through the stage-1 contract and expand `discOffset`.
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n), discOffset, discrepancy] using hB n

/-- Transfer a uniform discrepancy bound for the reduced sequence to a uniform nucleus-level
bound on the affine-tail sums of the original sequence.

This is the `apSumFrom` analogue of `contract_natAbs_apSumOffset_le`.  It is often the most useful
form when later stages phrase their reductions in terms of the affine nucleus `apSumFrom`.
-/
theorem contract_natAbs_apSumFrom_mul_le (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n, discrepancy out.g out.d n ≤ B) :
    ∀ n, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) ≤ B := by
  intro n
  simpa [out.discrepancy_eq_natAbs_apSumFrom_mul (f := f) (n := n)] using hB n

/-- Strict-inequality version of `contract_natAbs_apSumFrom_mul_le`. -/
theorem contract_natAbs_apSumFrom_mul_lt (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n, discrepancy out.g out.d n < B) :
    ∀ n, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) < B := by
  intro n
  simpa [out.discrepancy_eq_natAbs_apSumFrom_mul (f := f) (n := n)] using hB n

/-!
### Boundedness along the reduced step, transported to `discOffset`

These small lemmas let a downstream stage switch between:
- bounded discrepancy along the reduced step for `out.g`, and
- a uniform bound on the offset discrepancies `discOffset f out.d out.m`.

They are pure “pipeline glue”: the content is obvious, but having them as named lemmas avoids
repetitive `∃`-unpacking and rewriting.
-/

/-- Bounded discrepancy along the reduced step, rewritten as a uniform `discOffset` bound. -/
theorem boundedDiscrepancyAlong_iff_exists_forall_discOffset_le (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d ↔ (∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B) := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    exact out.contract_discOffset_le (f := f) B hB
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    -- Transfer the `discOffset` bound to a discrepancy bound for the reduced sequence.
    exact out.contract_discrepancy_le_of_forall_discOffset_le (f := f) B hB

/-- Negated boundedness along the reduced step, rewritten as an explicit witness form on `discOffset`.

This is the `ReductionOutput`-specialized version of the standard equivalence
`¬ BoundedDiscrepancyAlong g d ↔ ∀ B, ∃ n, B < discrepancy g d n`, rewritten via
`out.discrepancy_eq_discOffset`.
-/
theorem not_boundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (out : ReductionOutput f) :
    (¬ BoundedDiscrepancyAlong out.g out.d) ↔ (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) := by
  -- Use the witness-form predicate `UnboundedDiscrepancyAlong` as a bridge.
  calc
    (¬ BoundedDiscrepancyAlong out.g out.d)
        ↔ Tao2015.UnboundedDiscrepancyAlong out.g out.d := by
            simpa using (Tao2015.UnboundedDiscrepancyAlong.iff_not_boundedDiscrepancyAlong
              (f := out.g) (d := out.d)).symm
    _ ↔ (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) :=
          out.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (f := f)

/-!
### Small `ContextAlong` helpers

Later Track C stages often pass around a fixed-step boundedness context
`ctx : Tao2015.ContextAlong out.g out.d` for the reduced sequence.
Since the reduction output is *morally* an offset view of the original sequence,
we frequently want to convert between:
- a bound on `discrepancy out.g out.d`, and
- a bound on `discOffset f out.d out.m`.

These are tiny wrappers around the earlier transfer lemmas.
-/

/-- Build a fixed-step discrepancy context for the reduced sequence from a uniform offset bound.

This is a convenience packaging of `out.contract_discrepancy_le`.
-/
theorem contextAlong_of_forall_discOffset_le (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, discOffset f out.d out.m n ≤ B) :
    Tao2015.ContextAlong out.g out.d := by
  refine ⟨B, ?_⟩
  intro n
  exact out.contract_discrepancy_le B hB n

/-- Build a fixed-step discrepancy context for the reduced sequence from the global boundedness
context of the original sequence.

If `ctx : Tao2015.Context f` bounds all homogeneous AP sums of `f` by `ctx.B`, then the reduced
sequence `out.g` (a shift of `f` by `out.m*out.d`) has discrepancy uniformly bounded by
`ctx.B + ctx.B` along the fixed step size `out.d`.

This is a tiny but frequently-used “stage-0” helper: it lets later stages assume a
`ContextAlong out.g out.d` without having to re-prove the tail bound each time.
-/
theorem contextAlong_ofContext (out : ReductionOutput f) (ctx : Tao2015.Context f) :
    Tao2015.ContextAlong out.g out.d := by
  refine ⟨ctx.B + ctx.B, ?_⟩
  intro n
  -- Reduce to the literal shift form and apply the generic shift-bound lemma from `Context`.
  simpa [out.g_eq] using
    (ctx.bound_discrepancy_shift_add (f := f) (d := out.d) (m := out.m) (n := n) out.hd)

/-- Extract a uniform offset-discrepancy bound from a fixed-step discrepancy context on the
reduced sequence.

This is the “reverse direction” counterpart to `contextAlong_of_forall_discOffset_le`.
-/
theorem forall_discOffset_le_ofContextAlong (out : ReductionOutput f)
    (ctx : Tao2015.ContextAlong out.g out.d) :
    ∀ n : ℕ, discOffset f out.d out.m n ≤ ctx.B := by
  -- Use the previously packaged contract `contract_discOffset_le`.
  exact out.contract_discOffset_le ctx.B (fun n => ctx.bound_discrepancy (f := out.g) (d := out.d) n)

/-- Strict inequality version of `contextAlong_of_forall_discOffset_le`. -/
theorem contextAlong_of_forall_discOffset_lt (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, discOffset f out.d out.m n < B) :
    Tao2015.ContextAlong out.g out.d := by
  refine ⟨B, ?_⟩
  intro n
  exact out.contract_discrepancy_lt B hB n

/-- Strict inequality version of `forall_discOffset_le_ofContextAlong`. -/
theorem forall_discOffset_lt_ofContextAlong (out : ReductionOutput f)
    (ctx : Tao2015.ContextAlong out.g out.d) :
    ∀ n : ℕ, discOffset f out.d out.m n < ctx.B + 1 := by
  intro n
  -- A `≤ ctx.B` bound implies a `< ctx.B+1` bound.
  have hn : discOffset f out.d out.m n ≤ ctx.B :=
    (out.forall_discOffset_le_ofContextAlong (f := f) ctx) n
  exact lt_of_le_of_lt hn (Nat.lt_succ_self _)

/-- Pointwise transfer (`≤`) between the reduced discrepancy and the original offset discrepancy. -/
theorem discrepancy_le_iff_discOffset_le (out : ReductionOutput f) (n B : ℕ) :
    discrepancy out.g out.d n ≤ B ↔ discOffset f out.d out.m n ≤ B := by
  -- Just rewrite via `discrepancy_eq_discOffset`.
  simp [out.discrepancy_eq_discOffset (f := f) (n := n)]

/-- Pointwise transfer (`<`) between the reduced discrepancy and the original offset discrepancy. -/
theorem discrepancy_lt_iff_discOffset_lt (out : ReductionOutput f) (n B : ℕ) :
    discrepancy out.g out.d n < B ↔ discOffset f out.d out.m n < B := by
  simp [out.discrepancy_eq_discOffset (f := f) (n := n)]

/-- (Reviewer) Removed duplicate uniform-transfer lemmas here; keep the earlier canonical versions. -/

/-!
### Interop with `Tao2015.Context`

A typical Track C pipeline stage starts with a global boundedness context
`ctx : Tao2015.Context f` and then constructs a `ReductionOutput f` describing some derived
sequence `out.g`.

The following lemma is the basic ergonomic bridge: it immediately produces a fixed-step
boundedness statement for `out.g` from the global `ctx`.
-/

/-- If `f` has a global boundedness context `ctx`, then the reduced sequence `out.g` has bounded
fixed-step discrepancy along `out.d`, with bound `2*ctx.B`.

This is just `ctx.bound_discOffset` transported through `out.contract_discrepancy_le`.
-/
/-- (Removed: `discrepancy_le_two_mul_B_ofContext` was redundant with `contextAlong_ofContext`.) -/

-- (Removed duplicate transfer lemmas: see earlier `discrepancy_lt_iff_discOffset_lt` and
-- `forall_discrepancy_le_iff_forall_discOffset_le` in this namespace.)

/-- Convert a uniform discrepancy bound on the reduced sequence into a uniform bound on
`Int.natAbs (apSumOffset ...)` for the original sequence.

This is a small convenience wrapper around `out.discrepancy_eq_natAbs_apSumOffset`.
-/
theorem forall_natAbs_apSumOffset_le_of_forall_discrepancy_le (out : ReductionOutput f) (B : ℕ)
    (h : ∀ n : ℕ, discrepancy out.g out.d n ≤ B) :
    ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ B := by
  intro n
  -- Rewrite `natAbs (apSumOffset ...)` into `discrepancy out.g ...`.
  simpa [out.discrepancy_eq_natAbs_apSumOffset (f := f) (n := n)] using h n

/-- Convert a uniform discrepancy bound on the reduced sequence into a uniform bound on
`Int.natAbs (apSumFrom ...)` for the original sequence.

This is the affine-tail analogue of `forall_natAbs_apSumOffset_le_of_forall_discrepancy_le`.
-/
theorem forall_natAbs_apSumFrom_mul_le_of_forall_discrepancy_le (out : ReductionOutput f) (B : ℕ)
    (h : ∀ n : ℕ, discrepancy out.g out.d n ≤ B) :
    ∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) ≤ B := by
  intro n
  -- Rewrite `natAbs (apSumFrom ...)` into `discrepancy out.g ...`.
  -- (We use the reverse orientation to keep `simp` predictable.)
  have : discrepancy out.g out.d n ≤ B := h n
  -- `discrepancy = natAbs(apSumFrom ...)` by the stage-1 contract.
  simpa [out.discrepancy_eq_natAbs_apSumFrom_mul (f := f) (n := n)] using this

/-- Strict-inequality version of `forall_natAbs_apSumOffset_le_of_forall_discrepancy_le`. -/
theorem forall_natAbs_apSumOffset_lt_of_forall_discrepancy_lt (out : ReductionOutput f) (B : ℕ)
    (h : ∀ n : ℕ, discrepancy out.g out.d n < B) :
    ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) < B := by
  intro n
  simpa [out.discrepancy_eq_natAbs_apSumOffset (f := f) (n := n)] using h n

/-- Strict-inequality version of `forall_natAbs_apSumFrom_mul_le_of_forall_discrepancy_le`. -/
theorem forall_natAbs_apSumFrom_mul_lt_of_forall_discrepancy_lt (out : ReductionOutput f) (B : ℕ)
    (h : ∀ n : ℕ, discrepancy out.g out.d n < B) :
    ∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) < B := by
  intro n
  simpa [out.discrepancy_eq_natAbs_apSumFrom_mul (f := f) (n := n)] using h n

-- (Removed duplicate: `forall_discrepancy_lt_iff_forall_discOffset_lt` is proved earlier
-- in this namespace.)

/-!
### Extra transfer helpers

These are small wrappers that come up frequently when later stages want to move boundedness/
(unboundedness) statements back and forth between the reduced sequence `out.g` and the offset view
`discOffset f out.d out.m`.
-/

/-- If all offset discrepancies are *strictly* bounded by `B`, then so are the reduced fixed-step
(discrepancy) values.

This is the strict-inequality analogue of `out.contract_discrepancy_le`.
-/
theorem contract_discrepancy_lt (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n, discOffset f out.d out.m n < B) :
    ∀ n, discrepancy out.g out.d n < B := by
  intro n
  -- Rewrite the goal via the stage-1 discrepancy bridge.
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n

/-- If reduced discrepancies are strictly bounded by `B`, then offset discrepancies are strictly
bounded by `B`.

This is the strict-inequality analogue of `out.contract_discOffset_le`.
-/
theorem contract_discOffset_lt (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n, discrepancy out.g out.d n < B) :
    ∀ n, discOffset f out.d out.m n < B := by
  intro n
  simpa [(out.discrepancy_eq_discOffset (f := f) (n := n)).symm] using hB n

/-- Unbounded discrepancy along the reduced fixed step `out.d` transfers to an unbounded offset
view for the original sequence.

Concretely, this is a witness-form repackaging of the rewrite
`discrepancy out.g out.d n = discOffset f out.d out.m n`.
-/
theorem unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt (out : ReductionOutput f) :
    Tao2015.UnboundedDiscrepancyAlong out.g out.d ↔
      (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) := by
  -- Unfold the witness predicate, then rewrite the discrepancy term.
  constructor
  · intro h B
    rcases h B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hn
  · intro h B
    rcases h B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hn

/-!
### Basic derived boundedness contexts

A common way to *consume* a stage-1 reduction is:
- assume the original sequence has bounded discrepancy (globally),
- instantiate the reduction `out : ReductionOutput f`,
- immediately get a boundedness context along the fixed step `out.d` for the reduced sequence
  `out.g`.

These small wrappers keep later stages from having to manually rewrite `out.g` to a literal shift
and re-prove the same bound each time.
-/

/-- Turn a global boundedness context for `f` into a fixed-step boundedness context for `out.g`.

The output bound is `ctx.B + ctx.B` (i.e. `2*B`) because offset/tail sums can differ from prefix
sums by a subtraction.
-/
/-- Reuse `contextAlong_ofContext` above (defined in the ContextAlong helper section). -/

/-- Variant of `contextAlong_ofContext` with the bound written as `2 * ctx.B`.

This is occasionally convenient when downstream stages track constants multiplicatively.
-/
theorem contextAlong_ofContext_two_mul (out : ReductionOutput f) (ctx : Tao2015.Context f) :
    Tao2015.ContextAlong out.g out.d := by
  -- Reuse `contextAlong_ofContext`, then rewrite `ctx.B + ctx.B` as `2 * ctx.B`.
  refine ⟨2 * ctx.B, ?_⟩
  intro n
  have h := (Tao2015.ContextAlong.bound_discrepancy (f := out.g) (d := out.d)
    (ctx := out.contextAlong_ofContext (f := f) ctx) n)
  simpa [two_mul] using h

/-- If `f` has bounded discrepancy (globally), then the reduced sequence `out.g` has bounded
fixed-step discrepancy along `out.d`.

This is the `BoundedDiscrepancy`-to-`BoundedDiscrepancyAlong` specialization of
`contextAlong_ofContext`.
-/
theorem boundedDiscrepancyAlong_ofBoundedDiscrepancy (out : ReductionOutput f)
    (hb : BoundedDiscrepancy f) :
    BoundedDiscrepancyAlong out.g out.d := by
  -- Package the existential bound as a convenient context.
  let ctx : Tao2015.Context f := Tao2015.Context.ofBoundedDiscrepancy (f := f) hb
  -- Then use the derived fixed-step context.
  refine (Tao2015.ContextAlong.toBoundedDiscrepancyAlong (f := out.g) (d := out.d)
    (ctx := out.contextAlong_ofContext (f := f) ctx))

/-!
### Bounding the reduced sequence from offset bounds

While `contextAlong_ofContext` derives boundedness for `out.g` from a *global* boundedness context
for `f`, some later stages produce bounds directly in the “offset view”
`discOffset f out.d out.m`.

The following tiny wrappers package these bounds into the convenient fixed-step record
`ContextAlong out.g out.d` (and the existential `BoundedDiscrepancyAlong`).
-/

/-- Build a fixed-step discrepancy context for the reduced sequence from a uniform bound on the
corresponding offset discrepancies of the original sequence.

This is the most direct way to consume the transfer contract `out.contract_discrepancy_le`.
-/
theorem contextAlong_ofBound_discOffset (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, discOffset f out.d out.m n ≤ B) :
    Tao2015.ContextAlong out.g out.d := by
  refine ⟨B, ?_⟩
  intro n
  exact out.contract_discrepancy_le B hB n

/-- Existential boundedness (`BoundedDiscrepancyAlong`) for the reduced sequence, derived from a
uniform bound on `discOffset` for the original sequence.
-/
theorem boundedDiscrepancyAlong_ofBound_discOffset (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, discOffset f out.d out.m n ≤ B) :
    BoundedDiscrepancyAlong out.g out.d := by
  refine ⟨B, ?_⟩
  intro n
  exact out.contract_discrepancy_le B hB n

/-!
### Boundedness equivalences

These lemmas package the stage-1 transfer contracts into “existential boundedness” statements.
They are small, but they show up constantly when later reductions want to move between:
- bounded discrepancy of the reduced sequence `out.g` along the fixed step `out.d`, and
- bounded offset discrepancy of the original sequence `f` at parameters `(out.d, out.m)`.
-/

/-- Fixed-step boundedness for `out.g` implies a uniform bound on the corresponding offset
(discrepancy) family for `f`.

This is just `out.contract_discOffset_le` packaged under an existential.
-/
theorem exists_bound_discOffset_of_boundedDiscrepancyAlong (out : ReductionOutput f)
    (hb : BoundedDiscrepancyAlong out.g out.d) :
    ∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B := by
  rcases hb with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  exact out.contract_discOffset_le (f := f) B hB

/-- A convenience equivalence: bounded fixed-step discrepancy for `out.g` is the same as a
uniform bound on the offset discrepancy family `discOffset f out.d out.m`.
-/
theorem boundedDiscrepancyAlong_iff_exists_bound_discOffset (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d ↔ ∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B := by
  constructor
  · intro hb
    exact out.exists_bound_discOffset_of_boundedDiscrepancyAlong (f := f) hb
  · rintro ⟨B, hB⟩
    exact out.boundedDiscrepancyAlong_ofBound_discOffset (f := f) B hB

/-- `apSumOffset`-level reformulation of `boundedDiscrepancyAlong_iff_exists_bound_discOffset`. -/
theorem boundedDiscrepancyAlong_iff_exists_bound_natAbs_apSumOffset (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d ↔
      ∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ B := by
  -- `discOffset` is a wrapper around `Int.natAbs (apSumOffset ...)`.
  simpa [discOffset] using
    (out.boundedDiscrepancyAlong_iff_exists_bound_discOffset (f := f))

/-- `apSumFrom`-level reformulation of `boundedDiscrepancyAlong_iff_exists_bound_discOffset`.

This is convenient because many later stages work directly with the affine-tail nucleus
`apSumFrom f (m*d) d`.
-/
theorem boundedDiscrepancyAlong_iff_exists_bound_natAbs_apSumFrom_mul (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d ↔
      ∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) ≤ B := by
  -- Rewrite the `discOffset` bound into an `apSumFrom` bound via the offset→affine bridge.
  constructor
  · intro hb
    rcases (out.boundedDiscrepancyAlong_iff_exists_bound_discOffset (f := f)).1 hb with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- `discOffset f d m n = natAbs (apSumFrom f (m*d) d n)`.
    simpa [Tao2015.discOffset_eq_natAbs_apSumFrom_mul] using hB n
  · rintro ⟨B, hB⟩
    -- Convert the affine bound back into an offset-discrepancy bound, then apply the previous iff.
    refine (out.boundedDiscrepancyAlong_iff_exists_bound_discOffset (f := f)).2 ?_
    refine ⟨B, ?_⟩
    intro n
    -- `discOffset = natAbs(apSumFrom ...)`.
    simpa [Tao2015.discOffset_eq_natAbs_apSumFrom_mul] using hB n

/-- Extract an offset-discrepancy bound from a fixed-step discrepancy context for `out.g`.

This is a one-liner, but it avoids repeating the “rewrite then apply the context bound” pattern.
-/
theorem bound_discOffset_ofContextAlong (out : ReductionOutput f)
    (ctx : Tao2015.ContextAlong out.g out.d) :
    ∀ n : ℕ, discOffset f out.d out.m n ≤ ctx.B := by
  -- Use the `ContextAlong` bound on `out.g`, then transfer it back to the offset view.
  exact out.contract_discOffset_le (f := f) ctx.B (by intro n; exact ctx.bound_discrepancy (f := out.g) (d := out.d) n)

/-- Extract a *sum-level* (`Int.natAbs`) offset bound from a fixed-step discrepancy context.

This is a lightweight variant of `bound_discOffset_ofContextAlong` that avoids the `discOffset`
wrapper when later stages want to reason directly about the underlying AP sum.
-/
theorem bound_natAbs_apSumOffset_ofContextAlong (out : ReductionOutput f)
    (ctx : Tao2015.ContextAlong out.g out.d) :
    ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ ctx.B := by
  intro n
  -- `discOffset` is definitional.
  simpa [discOffset] using out.bound_discOffset_ofContextAlong (f := f) ctx n

/-- Extract a *sum-level* affine-tail bound (`apSumFrom`) from a fixed-step discrepancy context.

This is the `apSumFrom` analogue of `bound_natAbs_apSumOffset_ofContextAlong`.
-/
theorem bound_natAbs_apSumFrom_mul_ofContextAlong (out : ReductionOutput f)
    (ctx : Tao2015.ContextAlong out.g out.d) :
    ∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) ≤ ctx.B := by
  intro n
  -- `apSumFrom` bound is just the `apSum` bound for `out.g` rewritten via the stage-1 contract.
  have hn : Int.natAbs (apSum out.g out.d n) ≤ ctx.B :=
    ctx.bound_natAbs_apSum (f := out.g) (d := out.d) n
  simpa [out.apSum_eq_apSumFrom_mul (f := f) (n := n)] using hn

/-- Existential offset boundedness derived from a `ContextAlong` for the reduced sequence.

This is the `ContextAlong` analogue of
`exists_bound_discOffset_of_boundedDiscrepancyAlong`.
-/
theorem exists_bound_discOffset_ofContextAlong (out : ReductionOutput f)
    (ctx : Tao2015.ContextAlong out.g out.d) :
    ∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B := by
  refine ⟨ctx.B, out.bound_discOffset_ofContextAlong (f := f) ctx⟩

/-- A one-line bound lemma extracted from `contextAlong_ofContext`.

This can be handy in later reductions that want the bound but do not want to carry around the
entire `ContextAlong` record.
-/
theorem bound_discrepancy_ofContext (out : ReductionOutput f) (ctx : Tao2015.Context f) (n : ℕ) :
    discrepancy out.g out.d n ≤ ctx.B + ctx.B := by
  -- Use the `ContextAlong` produced by `contextAlong_ofContext`.
  simpa using (Tao2015.ContextAlong.bound_discrepancy (f := out.g) (d := out.d)
    (ctx := out.contextAlong_ofContext (f := f) ctx) n)

/-!
### Discrepancy witnesses transfer

Later Track C steps frequently pass around “there exists a large discrepancy” witnesses at the
fixed step `out.d`.  The reduced sequence `out.g` is meant to serve as a proxy for the offset view
`discOffset f out.d out.m`, so we provide a few one-line equivalences that let downstream code move
between these forms without redoing wrapper algebra.
-/

/-- Fixed-step discrepancy witness for `out.g` ↔ offset discrepancy witness for `f` (`>` form). -/
theorem hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔ (∃ n : ℕ, discOffset f out.d out.m n > C) := by
  -- Unfold `HasDiscrepancyAtLeastAlong` into a `discrepancy` witness, then rewrite using
  -- `out.discrepancy_eq_discOffset`.
  simpa [HasDiscrepancyAtLeastAlong.iff_exists_discrepancy_gt, out.discrepancy_eq_discOffset]

/-- Fixed-step discrepancy witness for `out.g` ↔ offset discrepancy witness for `f` (`<`-oriented). -/
theorem hasDiscrepancyAtLeastAlong_iff_exists_discOffset_lt (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔ (∃ n : ℕ, C < discOffset f out.d out.m n) := by
  simpa [gt_iff_lt] using (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) C)

/-- `natAbs (apSumOffset ...)` witness normal form corresponding to
`hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt`. -/
theorem hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt (out : ReductionOutput f)
    (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔
      (∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > C) := by
  -- `discOffset` is definitional.
  simpa [discOffset] using (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) C)

/-- `natAbs (apSumFrom ...)` witness normal form for the stage-1 reduction.

This is the affine-tail version of `hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt`.
It avoids the `discOffset`/`apSumOffset` wrappers entirely, which can be convenient if a later
stage is formulated directly in terms of the nucleus `apSumFrom`.
-/
theorem hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_mul_gt (out : ReductionOutput f)
    (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔
      (∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C) := by
  -- Rewrite the fixed-step predicate to a `discrepancy` witness, then rewrite `discrepancy out.g`
  -- via `out.discrepancy_eq_natAbs_apSumFrom_mul`.
  simpa [HasDiscrepancyAtLeastAlong.iff_exists_discrepancy_gt,
    out.discrepancy_eq_natAbs_apSumFrom_mul]

/-- `<`-oriented version of `hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_mul_gt`.

This is occasionally the more convenient inequality orientation for `linarith`/`omega`-style
pipelines.
-/
theorem hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_mul_lt (out : ReductionOutput f)
    (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔
      (∃ n : ℕ, C < Int.natAbs (apSumFrom f (out.m * out.d) out.d n)) := by
  simpa [gt_iff_lt] using
    (out.hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_mul_gt (f := f) C)

/-- Uniform “large discrepancy exists” witnesses transfer from `out.g` to the offset view.

This is just `hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt` lifted under `∀ C`.
-/
theorem forall_hasDiscrepancyAtLeastAlong_iff_forall_exists_discOffset_gt (out : ReductionOutput f) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) ↔
      (∀ C : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > C) := by
  -- Push the pointwise equivalence through `∀`.
  constructor
  · intro h C
    exact (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) C).1 (h C)
  · intro h C
    exact (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) C).2 (h C)

/-- If `out.g` has unbounded discrepancy along the fixed step `out.d`, then the offset view
`discOffset f out.d out.m` is unbounded (witness form). -/
theorem forall_exists_discOffset_gt_of_unboundedDiscrepancyAlong (out : ReductionOutput f)
    (h : Tao2015.UnboundedDiscrepancyAlong out.g out.d) :
    ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n := by
  -- Use the witness-form transfer lemma and unfold `UnboundedDiscrepancyAlong`.
  have h' := (out.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt (f := f)).1 h
  -- Just rewrite `discOffset > B` as `B < discOffset`.
  simpa [Tao2015.UnboundedDiscrepancyAlong, gt_iff_lt] using h'

/-!
### Constructors

The first reduction interface in Track C is deliberately verbose, because we want later stages to
*consume* a well-typed record instead of rebuilding rewrite lemmas each time.

To make it easy to produce a `ReductionOutput` in early stages, we provide a small constructor for
the common case where the reduced sequence is literally a shift of the input sequence.
-/

/-- Build a `ReductionOutput` from the literal shift `g k := f (k + m*d)`.

This is the intended “default constructor” for stage-1 reductions.

Note: the `apSum_contract` and discrepancy-transfer contracts are derived automatically from the
shift definition, so a user of this lemma only needs to supply:
- the parameters `d,m` and proof `d>0`, and
- a proof that `f` is a sign sequence.
-/
theorem mk_of_shift (f : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (hf : IsSignSequence f) :
    ReductionOutput f := by
  -- Delegate to the canonical constructor `ReductionOutput.ofShift`.
  exact ReductionOutput.ofShift (f := f) hf d m hd

/-- Build a `ReductionOutput` from an explicit derived sequence `g` together with the defining
rewrite `g = fun k => f (k + m*d)`.

This is a slightly more flexible constructor than `mk_of_shift`: it lets a stage-1 reduction pick
a *named* `g` while still deriving the bridge and transfer contracts automatically.
-/
theorem mk_of_g_eq (f g : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (hg : IsSignSequence g)
    (hgEq : g = fun k => f (k + m * d)) :
    ReductionOutput f := by
  classical
  refine
    { d := d
      m := m
      hd := hd
      g := g
      hg := hg
      g_eq := hgEq
      apSum_contract := ?_
      contract_discrepancy_le := ?_ }
  · exact Tao2015.apSum_contract_of_g_eq (f := f) (g := g) (d := d) (m := m) hgEq
  · intro B hB
    exact
      Tao2015.contract_discrepancy_le_of_apSum_contract (f := f) (g := g) (d := d) (m := m) (B := B)
        (Tao2015.apSum_contract_of_g_eq (f := f) (g := g) (d := d) (m := m) hgEq) hB

/-- Build a `ReductionOutput` from an explicit AP-sum bridge `apSum g d = apSumOffset f d m`.

This constructor is useful when a stage-1 reduction produces a *named* derived sequence `g` and a
clean bridge lemma at the `apSum` level, but does not want to separately prove the discrepancy
transfer contract.

The discrepancy transfer contract is derived automatically via the generic lemma
`contract_discrepancy_le_of_apSum_contract`.
-/
theorem mk_of_apSum_contract (f g : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (hg : IsSignSequence g)
    (gEq : g = fun k => f (k + m * d))
    (hAp : ∀ n : ℕ, apSum g d n = apSumOffset f d m n) :
    ReductionOutput f := by
  classical
  refine
    { d := d
      m := m
      hd := hd
      g := g
      hg := hg
      g_eq := gEq
      apSum_contract := hAp
      contract_discrepancy_le := ?_ }
  intro B hB
  exact
    Tao2015.contract_discrepancy_le_of_apSum_contract (f := f) (g := g) (d := d) (m := m) (B := B)
      hAp hB

/-!
### `simp` lemmas for the default constructors

These are small quality-of-life lemmas: they let downstream stages treat the constructors
`mk_of_shift`/`mk_of_g_eq` as “transparent” without unfolding their proofs.

We keep the simp set minimal to avoid rewriting loops.
-/

@[simp] theorem mk_of_shift_d (f : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (hf : IsSignSequence f) :
    (mk_of_shift (f := f) (d := d) (m := m) hd hf).d = d := by
  rfl

@[simp] theorem mk_of_shift_m (f : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (hf : IsSignSequence f) :
    (mk_of_shift (f := f) (d := d) (m := m) hd hf).m = m := by
  rfl

@[simp] theorem mk_of_shift_g (f : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (hf : IsSignSequence f) :
    (mk_of_shift (f := f) (d := d) (m := m) hd hf).g = (fun k => f (k + m * d)) := by
  rfl

@[simp] theorem mk_of_shift_g_apply (f : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (hf : IsSignSequence f)
    (k : ℕ) :
    (mk_of_shift (f := f) (d := d) (m := m) hd hf).g k = f (k + m * d) := by
  rfl

/-- `mk_of_shift` exposes the core bridge rule as a simp lemma.

This is a tiny quality-of-life lemma: it lets downstream stages normalize the reduced AP sum
without having to mention `apSum_contract` explicitly.
-/
@[simp] theorem mk_of_shift_apSum_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) (hd : d > 0)
    (hf : IsSignSequence f) :
    apSum (mk_of_shift (f := f) (d := d) (m := m) hd hf).g d n = apSumOffset f d m n := by
  -- `mk_of_shift` defines the `apSum_contract` field using the shift↔offset bridge.
  simp [ReductionOutput.mk_of_shift]

/-- Tail-sum (`apSumFrom`) simp lemma for the default constructor `mk_of_shift`.

This gives a direct rewrite from the affine nucleus `apSumFrom f (m*d) d` into the reduced
homogeneous AP sum `apSum (mk_of_shift ...).g d`.
-/
@[simp] theorem mk_of_shift_apSumFrom_mul_eq_apSum (f : ℕ → ℤ) (d m n : ℕ) (hd : d > 0)
    (hf : IsSignSequence f) :
    apSumFrom f (m * d) d n = apSum (mk_of_shift (f := f) (d := d) (m := m) hd hf).g d n := by
  calc
    apSumFrom f (m * d) d n = apSumOffset f d m n := by
      simpa using (Tao2015.apSumFrom_mul_eq_apSumOffset (f := f) (d := d) (m := m) (n := n))
    _ = apSum (mk_of_shift (f := f) (d := d) (m := m) hd hf).g d n := by
      simpa using
        (mk_of_shift_apSum_eq_apSumOffset (f := f) (d := d) (m := m) (n := n) hd hf).symm

/-- Discrepancy-level simp lemma for the default constructor `mk_of_shift`.

This is the discrepancy wrapper version of `mk_of_shift_apSum_eq_apSumOffset`.
-/
@[simp] theorem mk_of_shift_discrepancy_eq_discOffset (f : ℕ → ℤ) (d m n : ℕ) (hd : d > 0)
    (hf : IsSignSequence f) :
    discrepancy (mk_of_shift (f := f) (d := d) (m := m) hd hf).g d n = discOffset f d m n := by
  -- Reduce to the AP-sum bridge and unfold wrappers.
  simp [discrepancy, discOffset, mk_of_shift_apSum_eq_apSumOffset]

/-- Tail-sum (`apSumFrom`) rewrite for the default constructor `mk_of_shift`.

This packages the two-step bridge
`discrepancy (shift f) = discOffset f = natAbs (apSumFrom f (m*d) d ·)`
into a single simp lemma.
-/
@[simp] theorem mk_of_shift_discrepancy_eq_natAbs_apSumFrom_mul (f : ℕ → ℤ) (d m n : ℕ)
    (hd : d > 0) (hf : IsSignSequence f) :
    discrepancy (mk_of_shift (f := f) (d := d) (m := m) hd hf).g d n =
      Int.natAbs (apSumFrom f (m * d) d n) := by
  -- First rewrite discrepancy to `discOffset`, then rewrite `discOffset` to `apSumFrom`.
  simp [mk_of_shift_discrepancy_eq_discOffset (f := f) (d := d) (m := m) (n := n) hd hf,
    discOffset_eq_natAbs_apSumFrom_mul]

/-- Pointwise transfer wrapper (`≤`) for the default constructor `mk_of_shift`.

This is a tiny convenience lemma: later stages often prove a bound for `discOffset f d m n`
(or assume it) and want to immediately rewrite it into a bound for the reduced discrepancy.
-/
@[simp] theorem mk_of_shift_discrepancy_le_iff_discOffset_le (f : ℕ → ℤ) (d m n B : ℕ)
    (hd : d > 0) (hf : IsSignSequence f) :
    discrepancy (mk_of_shift (f := f) (d := d) (m := m) hd hf).g d n ≤ B ↔
      discOffset f d m n ≤ B := by
  simp [mk_of_shift_discrepancy_eq_discOffset (f := f) (d := d) (m := m) (n := n) hd hf]

/-- Pointwise transfer wrapper (`<`) for the default constructor `mk_of_shift`.

This is the strict-inequality analogue of `mk_of_shift_discrepancy_le_iff_discOffset_le`.
-/
@[simp] theorem mk_of_shift_discrepancy_lt_iff_discOffset_lt (f : ℕ → ℤ) (d m n B : ℕ)
    (hd : d > 0) (hf : IsSignSequence f) :
    discrepancy (mk_of_shift (f := f) (d := d) (m := m) hd hf).g d n < B ↔
      discOffset f d m n < B := by
  simp [mk_of_shift_discrepancy_eq_discOffset (f := f) (d := d) (m := m) (n := n) hd hf]

/-- Uniform transfer contract (`≤`) for the default constructor `mk_of_shift`.

This is the “consumer-facing” packaging: if you have a uniform bound on the offset discrepancy of
`f`, you immediately get the same uniform bound on the fixed-step discrepancies of the reduced
sequence.
-/
theorem mk_of_shift_contract_discrepancy_le (f : ℕ → ℤ) (d m B : ℕ) (hd : d > 0)
    (hf : IsSignSequence f) :
    (∀ n : ℕ, discOffset f d m n ≤ B) →
      (∀ n : ℕ, discrepancy (mk_of_shift (f := f) (d := d) (m := m) hd hf).g d n ≤ B) := by
  intro hB n
  simpa [mk_of_shift_discrepancy_eq_discOffset (f := f) (d := d) (m := m) (n := n) hd hf] using hB n

/-- Uniform transfer contract (`<`) for the default constructor `mk_of_shift`. -/
theorem mk_of_shift_contract_discrepancy_lt (f : ℕ → ℤ) (d m B : ℕ) (hd : d > 0)
    (hf : IsSignSequence f) :
    (∀ n : ℕ, discOffset f d m n < B) →
      (∀ n : ℕ, discrepancy (mk_of_shift (f := f) (d := d) (m := m) hd hf).g d n < B) := by
  intro hB n
  simpa [mk_of_shift_discrepancy_eq_discOffset (f := f) (d := d) (m := m) (n := n) hd hf] using hB n

/-!
### Fixed-step discrepancy witnesses for `mk_of_shift`

These are small wrappers that let downstream stages avoid unfolding
`HasDiscrepancyAtLeastAlong` and the discrepancy wrappers by hand.
-/

/-- A fixed-step discrepancy witness for `mk_of_shift` is the same as an offset-discrepancy witness
for the original sequence.

This is just `HasDiscrepancyAtLeastAlong.iff_exists_discrepancy_gt` combined with the simp lemma
`mk_of_shift_discrepancy_eq_discOffset`.
-/
theorem mk_of_shift_hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f : ℕ → ℤ) (d m C : ℕ)
    (hd : d > 0) (hf : IsSignSequence f) :
    HasDiscrepancyAtLeastAlong (mk_of_shift (f := f) (d := d) (m := m) hd hf).g d C ↔
      (∃ n : ℕ, discOffset f d m n > C) := by
  -- Unfold the fixed-step predicate and rewrite `discrepancy` using the stage-1 simp lemma.
  simpa [HasDiscrepancyAtLeastAlong.iff_exists_discrepancy_gt,
    mk_of_shift_discrepancy_eq_discOffset (f := f) (d := d) (m := m) (hd := hd) (hf := hf)]

/-- `<`-oriented version of `mk_of_shift_hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt`. -/
theorem mk_of_shift_hasDiscrepancyAtLeastAlong_iff_exists_discOffset_lt (f : ℕ → ℤ) (d m C : ℕ)
    (hd : d > 0) (hf : IsSignSequence f) :
    HasDiscrepancyAtLeastAlong (mk_of_shift (f := f) (d := d) (m := m) hd hf).g d C ↔
      (∃ n : ℕ, C < discOffset f d m n) := by
  simpa [gt_iff_lt] using
    (mk_of_shift_hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) (d := d) (m := m)
      (C := C) hd hf)

/-- `natAbs (apSumOffset ...)` witness normal form for `mk_of_shift`.

This can be useful if a downstream stage wants to avoid the `discOffset` wrapper.
-/
theorem mk_of_shift_hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt (f : ℕ → ℤ)
    (d m C : ℕ) (hd : d > 0) (hf : IsSignSequence f) :
    HasDiscrepancyAtLeastAlong (mk_of_shift (f := f) (d := d) (m := m) hd hf).g d C ↔
      (∃ n : ℕ, Int.natAbs (apSumOffset f d m n) > C) := by
  -- `discOffset` is definitional.
  simpa [discOffset] using
    (mk_of_shift_hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) (d := d) (m := m)
      (C := C) hd hf)

/-!
### Derived boundedness contexts for `mk_of_shift`

The general lemmas in `ReductionOutput` let later stages derive a fixed-step boundedness context
for a stage-1 reduction output.

When the reduction output is produced by `mk_of_shift`, it is convenient to have one-line wrappers
that avoid explicitly mentioning the `ReductionOutput` API.
-/

/-- Turn a global boundedness context for `f` into a fixed-step boundedness context for the
`mk_of_shift` reduced sequence.

The bound is `ctx.B + ctx.B` (i.e. `2*B`).
-/
theorem mk_of_shift_contextAlong_ofContext (f : ℕ → ℤ) (d m : ℕ) (hd : d > 0)
    (hf : IsSignSequence f) (ctx : Tao2015.Context f) :
    Tao2015.ContextAlong (mk_of_shift (f := f) (d := d) (m := m) hd hf).g d := by
  -- Just reuse the generic API for `ReductionOutput`.
  simpa [ReductionOutput.mk_of_shift] using
    (ReductionOutput.contextAlong_ofContext (f := f) (out := mk_of_shift (f := f) (d := d) (m := m) hd hf) ctx)

/-- Pointwise bound lemma extracted from `mk_of_shift_contextAlong_ofContext`. -/
theorem mk_of_shift_bound_discrepancy_ofContext (f : ℕ → ℤ) (d m : ℕ) (hd : d > 0)
    (hf : IsSignSequence f) (ctx : Tao2015.Context f) (n : ℕ) :
    discrepancy (mk_of_shift (f := f) (d := d) (m := m) hd hf).g d n ≤ ctx.B + ctx.B := by
  -- Use the `ContextAlong` bound.
  exact (Tao2015.ContextAlong.bound_discrepancy
    (f := (mk_of_shift (f := f) (d := d) (m := m) hd hf).g) (d := d)
    (ctx := mk_of_shift_contextAlong_ofContext (f := f) (d := d) (m := m) hd hf ctx) n)

/-- If `f` has bounded discrepancy globally, then the reduced sequence produced by `mk_of_shift`
has bounded discrepancy along the fixed step `d`.

This is just `ReductionOutput.boundedDiscrepancyAlong_ofBoundedDiscrepancy` specialized to
`mk_of_shift`.
-/
theorem mk_of_shift_boundedDiscrepancyAlong_ofBoundedDiscrepancy (f : ℕ → ℤ) (d m : ℕ) (hd : d > 0)
    (hf : IsSignSequence f) (hb : BoundedDiscrepancy f) :
    BoundedDiscrepancyAlong (mk_of_shift (f := f) (d := d) (m := m) hd hf).g d := by
  simpa [ReductionOutput.mk_of_shift] using
    (ReductionOutput.boundedDiscrepancyAlong_ofBoundedDiscrepancy
      (f := f) (out := mk_of_shift (f := f) (d := d) (m := m) hd hf) hb)

@[simp] theorem mk_of_g_eq_d (f g : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (hg : IsSignSequence g)
    (hgEq : g = fun k => f (k + m * d)) :
    (mk_of_g_eq (f := f) (g := g) (d := d) (m := m) hd hg hgEq).d = d := by
  rfl

@[simp] theorem mk_of_g_eq_m (f g : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (hg : IsSignSequence g)
    (hgEq : g = fun k => f (k + m * d)) :
    (mk_of_g_eq (f := f) (g := g) (d := d) (m := m) hd hg hgEq).m = m := by
  rfl

@[simp] theorem mk_of_g_eq_g (f g : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (hg : IsSignSequence g)
    (hgEq : g = fun k => f (k + m * d)) :
    (mk_of_g_eq (f := f) (g := g) (d := d) (m := m) hd hg hgEq).g = g := by
  rfl

@[simp] theorem mk_of_g_eq_g_apply (f g : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (hg : IsSignSequence g)
    (hgEq : g = fun k => f (k + m * d)) (k : ℕ) :
    (mk_of_g_eq (f := f) (g := g) (d := d) (m := m) hd hg hgEq).g k = g k := by
  rfl

/-- `mk_of_g_eq` exposes the core bridge rule as a simp lemma.

This is the `mk_of_g_eq` analogue of `mk_of_shift_apSum_eq_apSumOffset`.
-/
@[simp] theorem mk_of_g_eq_apSum_eq_apSumOffset (f g : ℕ → ℤ) (d m n : ℕ) (hd : d > 0)
    (hg : IsSignSequence g) (hgEq : g = fun k => f (k + m * d)) :
    apSum (mk_of_g_eq (f := f) (g := g) (d := d) (m := m) hd hg hgEq).g d n =
      apSumOffset f d m n := by
  -- `mk_of_g_eq` uses `Tao2015.apSum_contract_of_g_eq` for its `apSum_contract` field.
  simp [ReductionOutput.mk_of_g_eq, Tao2015.apSum_contract_of_g_eq, hgEq]

/-- Discrepancy-level simp lemma for the default constructor `mk_of_g_eq`. -/
@[simp] theorem mk_of_g_eq_discrepancy_eq_discOffset (f g : ℕ → ℤ) (d m n : ℕ) (hd : d > 0)
    (hg : IsSignSequence g) (hgEq : g = fun k => f (k + m * d)) :
    discrepancy (mk_of_g_eq (f := f) (g := g) (d := d) (m := m) hd hg hgEq).g d n =
      discOffset f d m n := by
  -- Reduce to the AP-sum bridge and unfold wrappers.
  simp [discrepancy, discOffset, mk_of_g_eq_apSum_eq_apSumOffset]

/-- Uniform transfer contract (`≤`) for the default constructor `mk_of_g_eq`. -/
theorem mk_of_g_eq_contract_discrepancy_le (f g : ℕ → ℤ) (d m B : ℕ) (hd : d > 0)
    (hg : IsSignSequence g) (hgEq : g = fun k => f (k + m * d)) :
    (∀ n : ℕ, discOffset f d m n ≤ B) →
      (∀ n : ℕ, discrepancy (mk_of_g_eq (f := f) (g := g) (d := d) (m := m) hd hg hgEq).g d n ≤ B) := by
  intro hB n
  simpa [mk_of_g_eq_discrepancy_eq_discOffset (f := f) (g := g) (d := d) (m := m) (n := n) hd hg hgEq] using hB n

/-- Uniform transfer contract (`<`) for the default constructor `mk_of_g_eq`. -/
theorem mk_of_g_eq_contract_discrepancy_lt (f g : ℕ → ℤ) (d m B : ℕ) (hd : d > 0)
    (hg : IsSignSequence g) (hgEq : g = fun k => f (k + m * d)) :
    (∀ n : ℕ, discOffset f d m n < B) →
      (∀ n : ℕ, discrepancy (mk_of_g_eq (f := f) (g := g) (d := d) (m := m) hd hg hgEq).g d n < B) := by
  intro hB n
  simpa [mk_of_g_eq_discrepancy_eq_discOffset (f := f) (g := g) (d := d) (m := m) (n := n) hd hg hgEq] using hB n

/-- Tail-sum (`apSumFrom`) rewrite for the default constructor `mk_of_g_eq`. -/
@[simp] theorem mk_of_g_eq_discrepancy_eq_natAbs_apSumFrom_mul (f g : ℕ → ℤ) (d m n : ℕ)
    (hd : d > 0) (hg : IsSignSequence g) (hgEq : g = fun k => f (k + m * d)) :
    discrepancy (mk_of_g_eq (f := f) (g := g) (d := d) (m := m) hd hg hgEq).g d n =
      Int.natAbs (apSumFrom f (m * d) d n) := by
  -- First rewrite discrepancy to `discOffset`, then rewrite `discOffset` to `apSumFrom`.
  simp [mk_of_g_eq_discrepancy_eq_discOffset (f := f) (g := g) (d := d) (m := m) (n := n) hd hg hgEq,
    discOffset_eq_natAbs_apSumFrom_mul]

/-- `mk_of_g_eq` stores the equality proof `hgEq` verbatim.

We intentionally do **not** tag this lemma `[simp]`: simp rewriting on proof fields is rarely
useful and can add noise/slowdowns.
-/
 theorem mk_of_g_eq_g_eq (f g : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (hg : IsSignSequence g)
    (hgEq : g = fun k => f (k + m * d)) :
    (mk_of_g_eq (f := f) (g := g) (d := d) (m := m) hd hg hgEq).g_eq = hgEq := by
  rfl

/-!
### `simp` lemmas for `mk_of_apSum_contract`

`mk_of_apSum_contract` is the most flexible stage-1 constructor: you supply an explicit AP-sum
bridge `apSum g d = apSumOffset f d m`, and the discrepancy transfer contract is derived
automatically.

The following tiny lemmas make that constructor pleasant to use downstream.
-/

@[simp] theorem mk_of_apSum_contract_d (f g : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (hg : IsSignSequence g)
    (gEq : g = fun k => f (k + m * d))
    (hAp : ∀ n : ℕ, apSum g d n = apSumOffset f d m n) :
    (mk_of_apSum_contract (f := f) (g := g) (d := d) (m := m) hd hg gEq hAp).d = d := by
  rfl

@[simp] theorem mk_of_apSum_contract_m (f g : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (hg : IsSignSequence g)
    (gEq : g = fun k => f (k + m * d))
    (hAp : ∀ n : ℕ, apSum g d n = apSumOffset f d m n) :
    (mk_of_apSum_contract (f := f) (g := g) (d := d) (m := m) hd hg gEq hAp).m = m := by
  rfl

@[simp] theorem mk_of_apSum_contract_g (f g : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (hg : IsSignSequence g)
    (gEq : g = fun k => f (k + m * d))
    (hAp : ∀ n : ℕ, apSum g d n = apSumOffset f d m n) :
    (mk_of_apSum_contract (f := f) (g := g) (d := d) (m := m) hd hg gEq hAp).g = g := by
  rfl

@[simp] theorem mk_of_apSum_contract_g_apply (f g : ℕ → ℤ) (d m : ℕ) (hd : d > 0)
    (hg : IsSignSequence g) (gEq : g = fun k => f (k + m * d))
    (hAp : ∀ n : ℕ, apSum g d n = apSumOffset f d m n) (k : ℕ) :
    (mk_of_apSum_contract (f := f) (g := g) (d := d) (m := m) hd hg gEq hAp).g k = g k := by
  rfl

/-- `mk_of_apSum_contract` exposes the supplied AP-sum bridge as a simp lemma. -/
@[simp] theorem mk_of_apSum_contract_apSum_eq_apSumOffset (f g : ℕ → ℤ) (d m n : ℕ) (hd : d > 0)
    (hg : IsSignSequence g) (gEq : g = fun k => f (k + m * d))
    (hAp : ∀ n : ℕ, apSum g d n = apSumOffset f d m n) :
    apSum (mk_of_apSum_contract (f := f) (g := g) (d := d) (m := m) hd hg gEq hAp).g d n =
      apSumOffset f d m n := by
  simpa [ReductionOutput.mk_of_apSum_contract] using (hAp n)

/-- Discrepancy-level simp lemma for `mk_of_apSum_contract`. -/
@[simp] theorem mk_of_apSum_contract_discrepancy_eq_discOffset (f g : ℕ → ℤ) (d m n : ℕ)
    (hd : d > 0) (hg : IsSignSequence g) (gEq : g = fun k => f (k + m * d))
    (hAp : ∀ n : ℕ, apSum g d n = apSumOffset f d m n) :
    discrepancy (mk_of_apSum_contract (f := f) (g := g) (d := d) (m := m) hd hg gEq hAp).g d n =
      discOffset f d m n := by
  simp [discrepancy, discOffset, mk_of_apSum_contract_apSum_eq_apSumOffset (f := f) (g := g)
    (d := d) (m := m) (n := n) hd hg gEq hAp]

/-- Tail-sum (`apSumFrom`) rewrite for `mk_of_apSum_contract`. -/
@[simp] theorem mk_of_apSum_contract_discrepancy_eq_natAbs_apSumFrom_mul (f g : ℕ → ℤ)
    (d m n : ℕ) (hd : d > 0) (hg : IsSignSequence g) (gEq : g = fun k => f (k + m * d))
    (hAp : ∀ n : ℕ, apSum g d n = apSumOffset f d m n) :
    discrepancy (mk_of_apSum_contract (f := f) (g := g) (d := d) (m := m) hd hg gEq hAp).g d n =
      Int.natAbs (apSumFrom f (m * d) d n) := by
  simp [mk_of_apSum_contract_discrepancy_eq_discOffset (f := f) (g := g) (d := d) (m := m) (n := n)
    hd hg gEq hAp,
    discOffset_eq_natAbs_apSumFrom_mul]

/-- Uniform transfer contract (`≤`) for `mk_of_apSum_contract`. -/
theorem mk_of_apSum_contract_contract_discrepancy_le (f g : ℕ → ℤ) (d m B : ℕ) (hd : d > 0)
    (hg : IsSignSequence g) (gEq : g = fun k => f (k + m * d))
    (hAp : ∀ n : ℕ, apSum g d n = apSumOffset f d m n) :
    (∀ n : ℕ, discOffset f d m n ≤ B) →
      (∀ n : ℕ, discrepancy (mk_of_apSum_contract (f := f) (g := g) (d := d) (m := m) hd hg gEq hAp).g d n ≤ B) := by
  intro hB n
  simpa [mk_of_apSum_contract_discrepancy_eq_discOffset (f := f) (g := g) (d := d) (m := m)
    (n := n) hd hg gEq hAp] using hB n

/-- Uniform transfer contract (`<`) for `mk_of_apSum_contract`. -/
theorem mk_of_apSum_contract_contract_discrepancy_lt (f g : ℕ → ℤ) (d m B : ℕ) (hd : d > 0)
    (hg : IsSignSequence g) (gEq : g = fun k => f (k + m * d))
    (hAp : ∀ n : ℕ, apSum g d n = apSumOffset f d m n) :
    (∀ n : ℕ, discOffset f d m n < B) →
      (∀ n : ℕ, discrepancy (mk_of_apSum_contract (f := f) (g := g) (d := d) (m := m) hd hg gEq hAp).g d n < B) := by
  intro hB n
  simpa [mk_of_apSum_contract_discrepancy_eq_discOffset (f := f) (g := g) (d := d) (m := m)
    (n := n) hd hg gEq hAp] using hB n

/-!
### Sanity-check examples

These are compile-only usage examples. They act as lightweight regression tests for the stage-1
reduction interface: if we refactor `ReductionOutput` and accidentally break the intended rewrite
contracts, these examples should fail to typecheck.
-/
section ReductionOutputExamples

variable {f : ℕ → ℤ} (out : ReductionOutput f)

/-- The interface fields are enough to rewrite `discrepancy` for the reduced sequence into an
offset discrepancy of the original sequence.

This is the core “IO contract” shape consumers should rely on.
-/
example (n : ℕ) : discrepancy out.g out.d n = discOffset f out.d out.m n := by
  simp [discrepancy, discOffset, out.apSum_contract]

/-- If offset discrepancies of `f` are bounded, then discrepancies of the reduced sequence are
bounded (using the `contract_discrepancy_le` field).
-/
example (B : ℕ) (hB : ∀ n : ℕ, discOffset f out.d out.m n ≤ B) :
    BoundedDiscrepancyAlong out.g out.d := by
  refine ⟨B, ?_⟩
  intro n
  exact out.contract_discrepancy_le B hB n

/-- Fixed-step discrepancy witnesses for `out.g` can be normalized directly into the tail-sum API
`apSumFrom` for `f`.

This is the preferred witness-normal form when downstream stages reason about affine tails.
-/
example (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔
      (∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C) := by
  simpa using (out.hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_gt (f := f) (C := C))

/-- Offsetting the reduced sequence by `m₂` corresponds to offsetting the original by `out.m + m₂`.

This is a basic “offset addition” sanity check for `ReductionOutput.apSumOffset_eq_apSumOffset_add`.
-/
example (m₂ n : ℕ) :
    apSumOffset out.g out.d m₂ n = apSumOffset f out.d (out.m + m₂) n := by
  simpa using (out.apSumOffset_eq_apSumOffset_add (f := f) (m₂ := m₂) (n := n))

/-- The derived reduction `out.shift_add_mul m₂` has the expected combined offset multiplier.
-/
example (m₂ : ℕ) : (out.shift_add_mul (f := f) m₂).m = out.m + m₂ := by
  simp

/-- Discrepancy contract for a composed shift reduction, as a regression test.
-/
example (m₂ n : ℕ) :
    discrepancy (out.shift_add_mul (f := f) m₂).g out.d n = discOffset f out.d (out.m + m₂) n := by
  simpa using (ReductionOutput.shift_add_mul.discrepancy_contract (f := f) out m₂ n)

end ReductionOutputExamples

/-!
### Basic simp-friendly rewrites

These are tiny wrappers around the record fields, but they let downstream stages use `simp` to
normalize expressions involving the reduced sequence `out.g`.

We only add the “forward” directions as simp lemmas, to avoid rewrite loops.
-/

/-- Rewrite the reduced homogeneous AP sum into the offset AP sum of the original sequence. -/
@[simp] theorem apSum_eq_apSumOffset (out : ReductionOutput f) (n : ℕ) :
    apSum out.g out.d n = apSumOffset f out.d out.m n :=
  out.apSum_contract n

/-- Reverse orientation of `apSum_eq_apSumOffset`.

Not marked `[simp]` to avoid rewriting loops.
-/
theorem apSumOffset_eq_apSum (out : ReductionOutput f) (n : ℕ) :
    apSumOffset f out.d out.m n = apSum out.g out.d n := by
  simpa using (out.apSum_eq_apSumOffset (f := f) (n := n)).symm

/-- `Int.natAbs` form of `apSum_eq_apSumOffset`. -/
@[simp] theorem natAbs_apSum_eq_natAbs_apSumOffset (out : ReductionOutput f) (n : ℕ) :
    Int.natAbs (apSum out.g out.d n) = Int.natAbs (apSumOffset f out.d out.m n) := by
  simp [out.apSum_eq_apSumOffset (f := f) (n := n)]

/-- Rewrite the reduced discrepancy as an offset discrepancy of the original sequence.

Marked `[simp]` because it is the main consumer-facing normalization rule for the interface.
-/
@[simp] theorem discrepancy_eq_discOffset (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n = discOffset f out.d out.m n := by
  simp [discrepancy, discOffset]

/-- A `discOffset`-free version of `discrepancy_eq_discOffset`.

This is occasionally convenient when a downstream stage wants to work directly with
`Int.natAbs (apSumOffset ...)` without going through the wrapper definition `discOffset`.

Marked `[simp]` for the same reason as `discrepancy_eq_discOffset`.
-/
@[simp] theorem discrepancy_eq_natAbs_apSumOffset (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n = Int.natAbs (apSumOffset f out.d out.m n) := by
  simp [discrepancy, out.apSum_contract]

/-- Reverse orientation of `discrepancy_eq_discOffset`.

Not marked `[simp]` to avoid rewriting loops.
-/
theorem discOffset_eq_discrepancy (out : ReductionOutput f) (n : ℕ) :
    discOffset f out.d out.m n = discrepancy out.g out.d n := by
  simpa using (out.discrepancy_eq_discOffset (f := f) (n := n)).symm

/-!
### Pointwise transfer wrappers

Downstream stages often want to translate inequalities about the reduced discrepancy into
inequalities about the corresponding offset discrepancy of the original sequence (and vice
versa).  These wrappers let `simp` close those goals immediately.
-/

/-- Pointwise `≤` transfer: `discrepancy out.g` is interchangeable with the corresponding
`discOffset` witness.

Marked `[simp]` because it is a one-step rewrite consequence of `discrepancy_eq_discOffset`.
-/
@[simp] theorem discrepancy_le_iff_discOffset_le (out : ReductionOutput f) (n B : ℕ) :
    discrepancy out.g out.d n ≤ B ↔ discOffset f out.d out.m n ≤ B := by
  simp [out.discrepancy_eq_discOffset (f := f) (n := n)]

/-- Pointwise `<` transfer: strict inequality version of
`discrepancy_le_iff_discOffset_le`.
-/
@[simp] theorem discrepancy_lt_iff_discOffset_lt (out : ReductionOutput f) (n B : ℕ) :
    discrepancy out.g out.d n < B ↔ discOffset f out.d out.m n < B := by
  simp [out.discrepancy_eq_discOffset (f := f) (n := n)]

/-- One-direction pointwise transfer (`≤`), written without `↔`.

Useful when the goal is a bound on the reduced discrepancy and the hypothesis is already a bound
on `discOffset`.
-/
theorem discrepancy_le_of_discOffset_le (out : ReductionOutput f) {n B : ℕ}
    (h : discOffset f out.d out.m n ≤ B) :
    discrepancy out.g out.d n ≤ B := by
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using h

/-- One-direction pointwise transfer (`≤`), from reduced discrepancy to offset discrepancy.

This is a small wrapper around `contract_discOffset_le`.
-/
theorem discOffset_le_of_discrepancy_le (out : ReductionOutput f) {n B : ℕ}
    (h : discrepancy out.g out.d n ≤ B) :
    discOffset f out.d out.m n ≤ B := by
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using h

/-!
### Unboundedness transfer

A later stage often proves that the reduced sequence has unbounded discrepancy along the fixed
step `out.d`, and we want to translate that statement back into the “offset view” of the original
sequence.

These are just repackagings of `out.discrepancy_eq_discOffset`.
-/

/-- Unbounded discrepancy along `out.d` for the reduced sequence is equivalent to unboundedness of
the corresponding offset discrepancies of the original sequence.

This is a consumer-facing normal form: it avoids mentioning `out.g` at all.
-/
theorem unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (out : ReductionOutput f) :
    UnboundedDiscrepancyAlong out.g out.d ↔
      (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) := by
  -- Unfold the witness predicate and rewrite via the stage-1 discrepancy contract.
  simp [UnboundedDiscrepancyAlong, out.discrepancy_eq_discOffset]

/-- `>`-oriented version of `unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt`. -/
theorem unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt (out : ReductionOutput f) :
    UnboundedDiscrepancyAlong out.g out.d ↔
      (∀ B : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > B) := by
  simpa [gt_iff_lt] using (out.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (f := f))

/-- Expand the defining equation of `g`. -/
@[simp] theorem g_apply (out : ReductionOutput f) (k : ℕ) : out.g k = f (k + out.m * out.d) := by
  simpa [out.g_eq]

/-- Convenience rewrite: `out.g` is definitionally the shift of `f` by `out.m*out.d`. -/
@[simp] theorem g_eq_shift (out : ReductionOutput f) : out.g = fun k => f (k + out.m * out.d) :=
  out.g_eq

/-!
### Offset reassociation through a `ReductionOutput`

When chaining reductions it is common to accumulate an offset `(out.m + m₂) * out.d`.
The lemmas in `Tao2015` allow us to peel off the first chunk `out.m*out.d` by shifting the
underlying sequence.

These wrappers specialize the general offset-reassociation lemmas to the particular shift
bundled by `out`.
-/

/-- Peel off the initial offset `out.m*out.d` at the AP-sum level.

This is a `ReductionOutput`-friendly specialization of `Tao2015.apSumOffset_add`.
-/
theorem apSumOffset_add_eq_apSumOffset_g (out : ReductionOutput f) (m₂ n : ℕ) :
    apSumOffset f out.d (out.m + m₂) n = apSumOffset out.g out.d m₂ n := by
  -- Apply the general reassociation lemma, then rewrite the shifted sequence using `out.g_eq`.
  simpa [out.g_eq] using
    (Tao2015.apSumOffset_add (f := f) (d := out.d) (m₁ := out.m) (m₂ := m₂) (n := n))

/-- Peel off the initial offset `out.m*out.d` at the discrepancy level.

This is a `ReductionOutput`-friendly specialization of `Tao2015.discOffset_add`.
-/
theorem discOffset_add_eq_discOffset_g (out : ReductionOutput f) (m₂ n : ℕ) :
    discOffset f out.d (out.m + m₂) n = discOffset out.g out.d m₂ n := by
  -- `discOffset_add` is already at the discrepancy level.
  simpa [out.g_eq] using
    (Tao2015.discOffset_add (f := f) (d := out.d) (m₁ := out.m) (m₂ := m₂) (n := n))

/-- Peel off the initial offset `out.m*out.d` at the affine-tail level (`apSumFrom`).

This is a convenient reformulation of `apSumOffset_add_eq_apSumOffset_g` using the bridge
`apSumOffset_eq_apSumFrom_mul`.
-/
theorem apSumFrom_add_mul_eq_apSumFrom_g (out : ReductionOutput f) (m₂ n : ℕ) :
    apSumFrom f ((out.m + m₂) * out.d) out.d n = apSumFrom out.g (m₂ * out.d) out.d n := by
  -- Rewrite both sides to offset sums, then use `apSumOffset_add_eq_apSumOffset_g`.
  -- LHS: `apSumFrom f ((out.m+m₂)*d) d n = apSumOffset f d (out.m+m₂) n`.
  -- RHS: `apSumFrom out.g (m₂*d) d n = apSumOffset out.g d m₂ n`.
  calc
    apSumFrom f ((out.m + m₂) * out.d) out.d n
        = apSumOffset f out.d (out.m + m₂) n := by
            simpa using (Tao2015.apSumFrom_mul_eq_apSumOffset (f := f) (d := out.d) (m := out.m + m₂) (n := n))
    _ = apSumOffset out.g out.d m₂ n := out.apSumOffset_add_eq_apSumOffset_g (f := f) (m₂ := m₂) (n := n)
    _ = apSumFrom out.g (m₂ * out.d) out.d n := by
            simpa using (Tao2015.apSumOffset_eq_apSumFrom_mul (f := out.g) (d := out.d) (m := m₂) (n := n))

/-- `natAbs`-AP-sum form of `discOffset_add_eq_discOffset_g`.

This is useful when a later stage wants to reason directly about the AP sums rather than the
bundled discrepancy wrappers.
-/
theorem natAbs_apSumOffset_add_eq_natAbs_apSumOffset_g (out : ReductionOutput f) (m₂ n : ℕ) :
    Int.natAbs (apSumOffset f out.d (out.m + m₂) n) =
      Int.natAbs (apSumOffset out.g out.d m₂ n) := by
  -- `discOffset` is definitional.
  simpa [discOffset] using congrArg Int.natAbs (out.apSumOffset_add_eq_apSumOffset_g (f := f) (m₂ := m₂) (n := n))

/-- Pointwise convenience lemma for the discrepancy-transfer contract. -/
theorem contract_discrepancy_le_apply (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n, discOffset f out.d out.m n ≤ B) (n : ℕ) :
    discrepancy out.g out.d n ≤ B :=
  out.contract_discrepancy_le B hB n

/-- `∀`-form convenience lemma for the discrepancy-transfer contract. -/
theorem contract_discrepancy_le_forall (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n, discOffset f out.d out.m n ≤ B) :
    ∀ n, discrepancy out.g out.d n ≤ B :=
  out.contract_discrepancy_le B hB

/-- Reverse transfer (≤): bound on the reduced discrepancy gives a bound on `discOffset`. -/
theorem contract_discOffset_le (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n, discrepancy out.g out.d n ≤ B) :
    ∀ n, discOffset f out.d out.m n ≤ B := by
  intro n
  -- Avoid depending on `discOffset_eq_discrepancy`, since it is derived later from `apSum_contract`.
  -- Both sides are definitional wrappers around `Int.natAbs`.
  simpa [discOffset, discrepancy, out.apSum_contract] using hB n

/-- Uniform discrepancy bounds are equivalent across the reduction interface.

This is often the most convenient contract form for consumers: you can swap between the
"reduced" view (`discrepancy out.g out.d`) and the "offset" view (`discOffset f out.d out.m`)
without mentioning AP sums.
-/
theorem forall_discrepancy_le_iff_forall_discOffset_le (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, discrepancy out.g out.d n ≤ B) ↔ (∀ n : ℕ, discOffset f out.d out.m n ≤ B) := by
  constructor
  · intro h n
    -- rewrite reduced discrepancy to `discOffset`
    simpa [discOffset, discrepancy, out.apSum_contract] using h n
  · intro h n
    -- rewrite `discOffset` to reduced discrepancy
    simpa [discOffset, discrepancy, out.apSum_contract] using h n

/-- Pointwise version of `forall_discrepancy_le_iff_forall_discOffset_le`.

This is handy when a downstream stage produces a bound for a *specific* witness `n`.
-/
theorem discrepancy_le_iff_discOffset_le (out : ReductionOutput f) (B n : ℕ) :
    discrepancy out.g out.d n ≤ B ↔ discOffset f out.d out.m n ≤ B := by
  -- Both sides are definitional wrappers around `Int.natAbs`, connected by `out.apSum_contract`.
  simpa [discOffset, discrepancy, out.apSum_contract]

/-- Pointwise strict-inequality version of `forall_discrepancy_lt_iff_forall_discOffset_lt`.

We keep this as a separate lemma because many reductions naturally phrase witnesses as
`B < ...`/`... > B` instead of a uniform `∀`-bound.
-/
theorem discrepancy_lt_iff_discOffset_lt (out : ReductionOutput f) (B n : ℕ) :
    discrepancy out.g out.d n < B ↔ discOffset f out.d out.m n < B := by
  simpa [discOffset, discrepancy, out.apSum_contract]

/-- `BoundedDiscrepancyAlong` for the reduced sequence `out.g` is equivalent to a uniform bound
on the offset discrepancy `discOffset f out.d out.m`.

This is a small packaging lemma: it eliminates the `out.g`/`discrepancy` view in favor of the
`f`/`discOffset` view, or vice versa.
-/
theorem boundedDiscrepancyAlong_iff_exists_forall_discOffset_le (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d ↔ (∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B) := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    exact (out.forall_discrepancy_le_iff_forall_discOffset_le (f := f) (B := B)).1 hB
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    exact (out.forall_discrepancy_le_iff_forall_discOffset_le (f := f) (B := B)).2 hB

/-- `BoundedDiscrepancyAlong` for the reduced sequence, expressed using the affine nucleus `apSumFrom`.

This is often the cleanest “existential boundedness” contract for later Tao2015 stages:
`apSumFrom` avoids the offset wrapper `discOffset` and lines up with affine AP sums used in the
log-averaging parts of the argument.
-/
theorem boundedDiscrepancyAlong_iff_exists_forall_natAbs_apSumFrom_mul_le (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d ↔
      (∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) ≤ B) := by
  constructor
  · intro h
    rcases (out.boundedDiscrepancyAlong_iff_exists_forall_discOffset_le (f := f)).1 h with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- Rewrite `discOffset` into the affine nucleus.
    simpa [Tao2015.discOffset_eq_natAbs_apSumFrom_mul (f := f) (d := out.d) (m := out.m) (n := n)] using hB n
  · rintro ⟨B, hB⟩
    refine (out.boundedDiscrepancyAlong_iff_exists_forall_discOffset_le (f := f)).2 ?_
    refine ⟨B, ?_⟩
    intro n
    -- Rewrite back from the affine nucleus to `discOffset`.
    simpa [Tao2015.discOffset_eq_natAbs_apSumFrom_mul (f := f) (d := out.d) (m := out.m) (n := n)] using hB n

/-- Strict-inequality version of `forall_discrepancy_le_iff_forall_discOffset_le`. -/
theorem forall_discrepancy_lt_iff_forall_discOffset_lt (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, discrepancy out.g out.d n < B) ↔ (∀ n : ℕ, discOffset f out.d out.m n < B) := by
  constructor
  · intro h n
    simpa [discOffset, discrepancy, out.apSum_contract] using h n
  · intro h n
    simpa [discOffset, discrepancy, out.apSum_contract] using h n

/-- Uniform discrepancy bounds are equivalent to uniform `Int.natAbs (apSumOffset ...)` bounds.

This is the same contract as `forall_discrepancy_le_iff_forall_discOffset_le`, but without going
through the `discOffset` wrapper.
-/
theorem forall_discrepancy_le_iff_forall_natAbs_apSumOffset_le (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, discrepancy out.g out.d n ≤ B) ↔
      (∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ B) := by
  -- `discOffset` is definitional, and `out.discrepancy_eq_discOffset` is simp.
  simpa [discOffset] using (out.forall_discrepancy_le_iff_forall_discOffset_le (f := f) (B := B))

/-- Strict-inequality version of `forall_discrepancy_le_iff_forall_natAbs_apSumOffset_le`. -/
theorem forall_discrepancy_lt_iff_forall_natAbs_apSumOffset_lt (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, discrepancy out.g out.d n < B) ↔
      (∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) < B) := by
  simpa [discOffset] using (out.forall_discrepancy_lt_iff_forall_discOffset_lt (f := f) (B := B))

/-- Uniform discrepancy bounds are equivalent to uniform bounds on the affine nucleus `apSumFrom`.

This is the `apSumFrom` analogue of `forall_discrepancy_le_iff_forall_natAbs_apSumOffset_le`.
It is often the cleanest contract form for later Tao2015 stages, since many reductions speak
naturally in terms of `apSumFrom`.
-/
theorem forall_discrepancy_le_iff_forall_natAbs_apSumFrom_mul_le (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, discrepancy out.g out.d n ≤ B) ↔
      (∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) ≤ B) := by
  constructor
  · intro h n
    -- Rewrite `discrepancy out.g out.d n` into the `apSumFrom` nucleus.
    simpa [out.discrepancy_eq_natAbs_apSumFrom_mul (f := f) (n := n)] using h n
  · intro h n
    -- Rewrite back using the same contract.
    simpa [out.discrepancy_eq_natAbs_apSumFrom_mul (f := f) (n := n)] using h n

/-- Strict-inequality version of `forall_discrepancy_le_iff_forall_natAbs_apSumFrom_mul_le`. -/
theorem forall_discrepancy_lt_iff_forall_natAbs_apSumFrom_mul_lt (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, discrepancy out.g out.d n < B) ↔
      (∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) < B) := by
  constructor
  · intro h n
    simpa [out.discrepancy_eq_natAbs_apSumFrom_mul (f := f) (n := n)] using h n
  · intro h n
    simpa [out.discrepancy_eq_natAbs_apSumFrom_mul (f := f) (n := n)] using h n

/-- `HasDiscrepancyAtLeastAlong` is invariant under rewriting the reduced sequence via `out.g_eq`. -/
theorem hasDiscrepancyAtLeastAlong_congr_shift (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔
      HasDiscrepancyAtLeastAlong (fun k => f (k + out.m * out.d)) out.d C := by
  simpa [out.g_eq]

/-- `apSum` for the reduced sequence is invariant under rewriting `out.g` via `out.g_eq`. -/
theorem apSum_congr_shift (out : ReductionOutput f) (n : ℕ) :
    apSum out.g out.d n = apSum (fun k => f (k + out.m * out.d)) out.d n := by
  simpa [out.g_eq]

/-- `discrepancy` for the reduced sequence is invariant under rewriting `out.g` via `out.g_eq`. -/
theorem discrepancy_congr_shift (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n = discrepancy (fun k => f (k + out.m * out.d)) out.d n := by
  simpa [out.g_eq]

/-- `discOffset` for the reduced sequence is invariant under rewriting `out.g` via `out.g_eq`. -/
theorem discOffset_congr_shift (out : ReductionOutput f) (m n : ℕ) :
    discOffset out.g out.d m n = discOffset (fun k => f (k + out.m * out.d)) out.d m n := by
  simpa [out.g_eq]

/-- `BoundedDiscrepancyAlong` is invariant under rewriting the reduced sequence via `out.g_eq`. -/
theorem boundedDiscrepancyAlong_congr_shift (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d ↔
      BoundedDiscrepancyAlong (fun k => f (k + out.m * out.d)) out.d := by
  simpa [out.g_eq]

/-- Negated form of `boundedDiscrepancyAlong_congr_shift`. -/
theorem not_boundedDiscrepancyAlong_congr_shift (out : ReductionOutput f) :
    (¬ BoundedDiscrepancyAlong out.g out.d) ↔
      (¬ BoundedDiscrepancyAlong (fun k => f (k + out.m * out.d)) out.d) := by
  simpa [out.g_eq]

/-- Rewrite the reduced-step discrepancy predicate into a `discOffset` witness (`C < ...`). -/
theorem hasDiscrepancyAtLeastAlong_iff_exists_discOffset_lt (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔ (∃ n : ℕ, C < discOffset f out.d out.m n) := by
  -- First rewrite `out.g` to the literal shift of `f`, then use the shift→offset bridge lemma.
  simpa [out.g_eq] using
    (Tao2015.hasDiscrepancyAtLeastAlong_shift_add_mul_iff_exists_discOffset_lt
      (f := f) (d := out.d) (m := out.m) (C := C))

/-- A version of `hasDiscrepancyAtLeastAlong_iff_exists_discOffset_lt` with the inequality
oriented as `... > C`.

This can be slightly more convenient when the downstream step naturally produces a strict
inequality in the “greater-than” direction.
-/
theorem hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔ (∃ n : ℕ, discOffset f out.d out.m n > C) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_lt (f := f) (C := C))

/-- Forward direction of `hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt`.

Useful when a downstream reduction produces an explicit `discOffset` witness and wants to
immediately phrase it as a fixed-step discrepancy statement for the reduced sequence.
-/
theorem hasDiscrepancyAtLeastAlong_of_exists_discOffset_gt (out : ReductionOutput f) {C : ℕ}
    (h : ∃ n : ℕ, discOffset f out.d out.m n > C) :
    HasDiscrepancyAtLeastAlong out.g out.d C :=
  (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) (C := C)).2 h

/-- Backward direction of `hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt`.

Useful when a downstream reduction starts from a fixed-step discrepancy hypothesis about the
reduced sequence and wants to normalize it into an offset-discrepancy witness for the original.
-/
theorem exists_discOffset_gt_of_hasDiscrepancyAtLeastAlong (out : ReductionOutput f) {C : ℕ}
    (h : HasDiscrepancyAtLeastAlong out.g out.d C) :
    ∃ n : ℕ, discOffset f out.d out.m n > C :=
  (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) (C := C)).1 h

/-- Witness-contract form: `∃ n, discrepancy out.g out.d n > C` is equivalent to
`∃ n, discOffset f out.d out.m n > C`.

This is a small lemma, but it comes up constantly: many pipeline stages produce a single witness
rather than the bundled predicate `HasDiscrepancyAtLeastAlong`.
-/
theorem exists_discrepancy_gt_iff_exists_discOffset_gt (out : ReductionOutput f) (C : ℕ) :
    (∃ n : ℕ, discrepancy out.g out.d n > C) ↔ (∃ n : ℕ, discOffset f out.d out.m n > C) := by
  -- Both sides are definitional rewrites using the `discrepancy`-level simp contract.
  constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩
  · simpa using hn
  · simpa using hn

/-- `<`-oriented version of `exists_discrepancy_gt_iff_exists_discOffset_gt`. -/
theorem exists_discrepancy_lt_iff_exists_discOffset_lt (out : ReductionOutput f) (C : ℕ) :
    (∃ n : ℕ, discrepancy out.g out.d n < C) ↔ (∃ n : ℕ, discOffset f out.d out.m n < C) := by
  constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩
  · simpa using hn
  · simpa using hn

/-- Sum-level (offset AP sum) witness normal form for `HasDiscrepancyAtLeastAlong out.g out.d C`.

This is the cleanest statement when downstream stages work directly with
`Int.natAbs (apSumOffset ...)` rather than the bundled wrappers `discrepancy`/`discOffset`.
-/
theorem hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔
      (∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > C) := by
  -- Unfold the fixed-step predicate, then rewrite `apSum out.g` to `apSumOffset` via the bridge.
  simp [HasDiscrepancyAtLeastAlong, out.apSum_contract]

/-- Unboundedness along the reduced step, normalized into `discOffset` witnesses.

This is a small convenience lemma: it lets later stages work purely in the “offset view” of the
original sequence `f` while still quantifying over discrepancy thresholds `C`.
-/
theorem forall_hasDiscrepancyAtLeastAlong_iff_forall_exists_discOffset_gt (out : ReductionOutput f) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) ↔
      (∀ C : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > C) := by
  constructor
  · intro h C
    exact (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) (C := C)).1 (h C)
  · intro h C
    exact (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) (C := C)).2 (h C)

/-!
### Convenience rewrites: `apSumOffset` ↔ `apSumFrom` for a `ReductionOutput`

Track C often wants the reduced homogeneous sums `apSum out.g out.d` rewritten into the affine
nucleus `apSumFrom f (out.m*out.d) out.d`.

These lemmas are tiny wrappers around:
- `out.apSum_contract`, and
- `Tao2015.apSumOffset_eq_apSumFrom_mul`.
-/

/-- Rewrite `apSum out.g out.d` to an affine AP sum of `f` starting at `out.m*out.d`.

Note: this lemma is already provided earlier in the file as
`ReductionOutput.apSum_eq_apSumFrom_mul`; we avoid redefining it here.
-/

/-- `simp`-friendly version of `apSum_eq_apSumFrom_mul`.

We intentionally **do not** tag this lemma `[simp]` by default: rewriting `apSum out.g out.d _`
into an `apSumFrom` expression can be convenient, but it can also create large goals if it fires
globally.

If you want this rewrite in a local proof, use:
`simpa using (out.apSum_eq_apSumFrom_mul_simp (f := f) (n := n))` or `simp [out.apSum_eq_apSumFrom_mul_simp]`.
-/
theorem apSum_eq_apSumFrom_mul_simp (out : ReductionOutput f) (n : ℕ) :
    apSum out.g out.d n = apSumFrom f (out.m * out.d) out.d n :=
  out.apSum_eq_apSumFrom_mul (f := f) (n := n)

/-- Reverse orientation of `apSum_eq_apSumFrom_mul`.

Note: this lemma is already provided earlier in the file as
`ReductionOutput.apSumFrom_mul_eq_apSum`; we avoid redefining it here.
-/

/-- `Int.natAbs` form of `apSum_eq_apSumFrom_mul`.

Note: this lemma is already provided earlier in the file as
`ReductionOutput.natAbs_apSum_eq_natAbs_apSumFrom_mul`; we avoid redefining it here.
-/

/-- Reverse orientation of `natAbs_apSum_eq_natAbs_apSumFrom_mul`.

Note: this lemma is already provided earlier in the file as
`ReductionOutput.natAbs_apSumFrom_mul_eq_natAbs_apSum`; we avoid redefining it here.
-/

/-- Rewrite the offset discrepancy bundled by `out` in terms of the affine nucleus `apSumFrom`.

Note: this lemma is already provided earlier in the file as
`ReductionOutput.discOffset_eq_natAbs_apSumFrom_mul`; we avoid redefining it here.
-/

/-- Rewrite `discrepancy out.g out.d` as a `natAbs` affine AP sum of `f`.

Note: this lemma is already provided earlier in the file as
`ReductionOutput.discrepancy_eq_natAbs_apSumFrom_mul`; we avoid redefining it here.
-/

/-- Transfer contract (≤) in affine-nucleus form.

If you can bound the affine nucleus `Int.natAbs (apSumFrom f (out.m*out.d) out.d n)` uniformly,
then you automatically bound the reduced discrepancies `discrepancy out.g out.d n`.

This is often the cleanest interface for later Tao2015 stages that work directly with `apSumFrom`.
-/
theorem contract_discrepancy_le_of_bound_natAbs_apSumFrom_mul (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) ≤ B) :
    ∀ n : ℕ, discrepancy out.g out.d n ≤ B := by
  intro n
  simpa [out.discrepancy_eq_natAbs_apSumFrom_mul (f := f) (n := n)] using hB n

/-- Transfer contract (<) in affine-nucleus form.

A strict-inequality version of `contract_discrepancy_le_of_bound_natAbs_apSumFrom_mul`.
-/
theorem contract_discrepancy_lt_of_bound_natAbs_apSumFrom_mul (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) < B) :
    ∀ n : ℕ, discrepancy out.g out.d n < B := by
  intro n
  simpa [out.discrepancy_eq_natAbs_apSumFrom_mul (f := f) (n := n)] using hB n

/-- Transfer contract (≤) in offset-sum form.

If you can bound `Int.natAbs (apSumOffset f out.d out.m n)` uniformly, then you can bound the
reduced discrepancies `discrepancy out.g out.d n`.

This is a lightweight convenience wrapper around `out.discrepancy_eq_natAbs_apSumOffset`.
-/
theorem contract_discrepancy_le_of_bound_natAbs_apSumOffset (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ B) :
    ∀ n : ℕ, discrepancy out.g out.d n ≤ B := by
  intro n
  simpa [out.discrepancy_eq_natAbs_apSumOffset (f := f) (n := n)] using hB n

/-- Transfer contract (<) in offset-sum form.

Strict-inequality version of `contract_discrepancy_le_of_bound_natAbs_apSumOffset`.
-/
theorem contract_discrepancy_lt_of_bound_natAbs_apSumOffset (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) < B) :
    ∀ n : ℕ, discrepancy out.g out.d n < B := by
  intro n
  simpa [out.discrepancy_eq_natAbs_apSumOffset (f := f) (n := n)] using hB n

/-- Sum-level witness normal form, but phrased using the affine nucleus `apSumFrom`. -/
theorem hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_mul_gt (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔
      (∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C) := by
  -- First use the offset witness normal form, then rewrite `apSumOffset` to `apSumFrom`.
  constructor
  · intro h
    rcases (out.hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt (f := f) (C := C)).1 h with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [Tao2015.apSumOffset_eq_apSumFrom_mul] using hn
  · rintro ⟨n, hn⟩
    refine (out.hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt (f := f) (C := C)).2 ?_
    refine ⟨n, ?_⟩
    simpa [Tao2015.apSumOffset_eq_apSumFrom_mul] using hn

/-- A single-witness form of `hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_mul_gt`.

This is a common consumer pattern: many later reductions produce (or consume) a *single* witness
`∃ n, discrepancy … > C` rather than the bundled predicate `HasDiscrepancyAtLeastAlong …`.
-/
theorem exists_discrepancy_gt_iff_exists_natAbs_apSumFrom_mul_gt (out : ReductionOutput f) (C : ℕ) :
    (∃ n : ℕ, discrepancy out.g out.d n > C) ↔
      (∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C) := by
  constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩
  · simpa [out.discrepancy_eq_natAbs_apSumFrom_mul (f := f) (n := n)] using hn
  · simpa [out.discrepancy_eq_natAbs_apSumFrom_mul (f := f) (n := n)] using hn

/-- A single-witness form of `hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt`. -/
theorem exists_discrepancy_gt_iff_exists_natAbs_apSumOffset_gt (out : ReductionOutput f) (C : ℕ) :
    (∃ n : ℕ, discrepancy out.g out.d n > C) ↔
      (∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > C) := by
  constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩
  · simpa [out.discrepancy_eq_natAbs_apSumOffset (f := f) (n := n)] using hn
  · simpa [out.discrepancy_eq_natAbs_apSumOffset (f := f) (n := n)] using hn

/-- `<`-oriented version of `hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_mul_gt`. -/
theorem hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_mul_lt (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔
      (∃ n : ℕ, C < Int.natAbs (apSumFrom f (out.m * out.d) out.d n)) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using
    (out.hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_mul_gt (f := f) (C := C))

/-- `<`-oriented version of `hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt`. -/
theorem hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_lt (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔
      (∃ n : ℕ, C < Int.natAbs (apSumOffset f out.d out.m n)) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using
    (out.hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt (f := f) (C := C))

/-- Extract a `discOffset` witness from a fixed-step discrepancy statement about `out.g`. -/
theorem exists_discOffset_gt_of_hasDiscrepancyAtLeastAlong (out : ReductionOutput f) {C : ℕ}
    (h : HasDiscrepancyAtLeastAlong out.g out.d C) :
    ∃ n : ℕ, discOffset f out.d out.m n > C :=
  (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) (C := C)).1 h

/-- Build a fixed-step discrepancy statement about `out.g` from a `discOffset` witness. -/
theorem hasDiscrepancyAtLeastAlong_of_exists_discOffset_gt (out : ReductionOutput f) {C : ℕ}
    (h : ∃ n : ℕ, discOffset f out.d out.m n > C) :
    HasDiscrepancyAtLeastAlong out.g out.d C :=
  (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) (C := C)).2 h

/-- `∀ C` fixed-step discrepancy for `out.g` is equivalent to `∀ C` existence of a `discOffset`
  witness for `f`.

This is just the pointwise witness contract
`HasDiscrepancyAtLeastAlong out.g out.d C ↔ ∃ n, C < discOffset f out.d out.m n` packaged under
universal quantification.
-/
theorem forall_hasDiscrepancyAtLeastAlong_iff_forall_exists_discOffset_lt (out : ReductionOutput f) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) ↔
      (∀ C : ℕ, ∃ n : ℕ, C < discOffset f out.d out.m n) := by
  constructor
  · intro h C
    exact (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_lt (f := f) (C := C)).1 (h C)
  · intro h C
    exact (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_lt (f := f) (C := C)).2 (h C)

/-- `¬ BoundedDiscrepancyAlong out.g out.d` rewritten in terms of the `discOffset` witnesses for `f`.

This is the “unbounded along a fixed step” normal form that later reductions typically want.
-/
theorem not_boundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (out : ReductionOutput f) :
    (¬ BoundedDiscrepancyAlong out.g out.d) ↔
      (∀ C : ℕ, ∃ n : ℕ, C < discOffset f out.d out.m n) := by
  -- Use the generic `∀ C, HasDiscrepancyAtLeastAlong ↔ ¬ bounded` equivalence.
  simpa [out.forall_hasDiscrepancyAtLeastAlong_iff_forall_exists_discOffset_lt (f := f)] using
    (HasDiscrepancyAtLeastAlong.forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscrepancyAlong
      (g := out.g) (d := out.d))

/-- A `> C`-oriented version of `not_boundedDiscrepancyAlong_iff_forall_exists_discOffset_lt`. -/
theorem not_boundedDiscrepancyAlong_iff_forall_exists_discOffset_gt (out : ReductionOutput f) :
    (¬ BoundedDiscrepancyAlong out.g out.d) ↔
      (∀ C : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > C) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using
    (out.not_boundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (f := f))

/-- Promote a fixed-step discrepancy statement for `out.g` to the standard discrepancy predicate.

This is a convenience wrapper around `HasDiscrepancyAtLeastAlong.toHasDiscrepancyAtLeast`, using
`out.hd : out.d > 0`.
-/
theorem hasDiscrepancyAtLeast_of_hasDiscrepancyAtLeastAlong (out : ReductionOutput f) {C : ℕ}
    (h : HasDiscrepancyAtLeastAlong out.g out.d C) :
    HasDiscrepancyAtLeast out.g C :=
  HasDiscrepancyAtLeastAlong.toHasDiscrepancyAtLeast (f := out.g) (d := out.d) (C := C) out.hd h

/-- Produce a standard discrepancy witness for the reduced sequence from a `discOffset` witness
for the original sequence.

This is a tiny wrapper that combines:
- the `discOffset` witness contract for `out` (fixed-step), and
- the promotion lemma `hasDiscrepancyAtLeast_of_hasDiscrepancyAtLeastAlong`.
-/
theorem hasDiscrepancyAtLeast_of_exists_discOffset_gt (out : ReductionOutput f) {C : ℕ}
    (h : ∃ n : ℕ, discOffset f out.d out.m n > C) :
    HasDiscrepancyAtLeast out.g C := by
  apply out.hasDiscrepancyAtLeast_of_hasDiscrepancyAtLeastAlong (f := f)
  exact out.hasDiscrepancyAtLeastAlong_of_exists_discOffset_gt (f := f) h

/-- Standard discrepancy witness for the reduced sequence, in `apSumOffset` (sum-level) form. -/
theorem hasDiscrepancyAtLeast_of_exists_natAbs_apSumOffset_gt (out : ReductionOutput f) {C : ℕ}
    (h : ∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > C) :
    HasDiscrepancyAtLeast out.g C := by
  apply out.hasDiscrepancyAtLeast_of_exists_discOffset_gt (f := f)
  -- `discOffset` is definitional.
  simpa [discOffset] using h

/-- Standard discrepancy witness for the reduced sequence, in `apSumFrom` (affine-nucleus) form. -/
theorem hasDiscrepancyAtLeast_of_exists_natAbs_apSumFrom_mul_gt (out : ReductionOutput f) {C : ℕ}
    (h : ∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C) :
    HasDiscrepancyAtLeast out.g C := by
  apply out.hasDiscrepancyAtLeast_of_hasDiscrepancyAtLeastAlong (f := f)
  -- First build a fixed-step witness, then promote.
  exact (out.hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_mul_gt (f := f) (C := C)).2 h

/-- Build a standard discrepancy statement for the *literal shift* `fun k => f (k + out.m*out.d)`
from a `discOffset` witness.

This is a common packaging step: a later stage might produce a `discOffset` witness (about the
original sequence), while the next stage expects a standard `HasDiscrepancyAtLeast` statement
(about the shifted sequence).
-/
theorem hasDiscrepancyAtLeast_shift_of_exists_discOffset_gt (out : ReductionOutput f) {C : ℕ}
    (h : ∃ n : ℕ, discOffset f out.d out.m n > C) :
    HasDiscrepancyAtLeast (fun k => f (k + out.m * out.d)) C := by
  -- First rewrite the `discOffset` witness into a fixed-step discrepancy statement.
  have halong : HasDiscrepancyAtLeastAlong (fun k => f (k + out.m * out.d)) out.d C := by
    exact
      (Tao2015.hasDiscrepancyAtLeastAlong_shift_add_mul_iff_exists_discOffset_gt
        (f := f) (d := out.d) (m := out.m) (C := C)).2 h
  -- Then promote it to the standard `HasDiscrepancyAtLeast` predicate using `out.hd : out.d > 0`.
  exact HasDiscrepancyAtLeastAlong.toHasDiscrepancyAtLeast (f := fun k => f (k + out.m * out.d))
    (d := out.d) (C := C) out.hd halong

/-- Quantified version of `hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt`. -/
theorem forall_hasDiscrepancyAtLeastAlong_iff_forall_exists_discOffset_gt (out : ReductionOutput f) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) ↔
      (∀ C : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > C) := by
  constructor
  · intro h C
    exact (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) (C := C)).1 (h C)
  · intro h C
    exact (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) (C := C)).2 (h C)

/-- Convert an offset-discrepancy witness for `f` into a discrepancy witness for the reduced sequence.

This is the `∃ n` (non-uniform) counterpart of the uniform transfer lemma
`forall_discrepancy_le_iff_forall_discOffset_le`.
-/
theorem exists_discrepancy_gt_of_exists_discOffset_gt (out : ReductionOutput f) {C : ℕ}
    (h : ∃ n : ℕ, discOffset f out.d out.m n > C) :
    ∃ n : ℕ, discrepancy out.g out.d n > C := by
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hn

/-- Convert a discrepancy witness for the reduced sequence into an offset-discrepancy witness for `f`.

This is the reverse direction of `exists_discrepancy_gt_of_exists_discOffset_gt`.
-/
theorem exists_discOffset_gt_of_exists_discrepancy_gt (out : ReductionOutput f) {C : ℕ}
    (h : ∃ n : ℕ, discrepancy out.g out.d n > C) :
    ∃ n : ℕ, discOffset f out.d out.m n > C := by
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hn

/-- Extract an `apSumOffset` witness from a fixed-step discrepancy statement about `out.g`. -/
theorem exists_natAbs_apSumOffset_gt_of_hasDiscrepancyAtLeastAlong (out : ReductionOutput f) {C : ℕ}
    (h : HasDiscrepancyAtLeastAlong out.g out.d C) :
    ∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > C :=
  (out.hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt (f := f) (C := C)).1 h

/-- Quantified version of `hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt`. -/
theorem forall_hasDiscrepancyAtLeastAlong_iff_forall_exists_natAbs_apSumOffset_gt (out : ReductionOutput f) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) ↔
      (∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > C) := by
  constructor
  · intro h C
    exact (out.hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt (f := f) (C := C)).1 (h C)
  · intro h C
    exact (out.hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt (f := f) (C := C)).2 (h C)

/-- Repackage unboundedness along the reduced step size `out.d`.

This is just `HasDiscrepancyAtLeastAlong.forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscrepancyAlong`
specialized to `out.g`.
-/
theorem forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscrepancyAlong (out : ReductionOutput f) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) ↔ ¬ BoundedDiscrepancyAlong out.g out.d := by
  simpa using
    (HasDiscrepancyAtLeastAlong.forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscrepancyAlong
      (g := out.g) (d := out.d))

/-- Unboundedness along `out.d` rewritten as “arbitrarily large offset discrepancy witnesses”. -/
theorem not_boundedDiscrepancyAlong_iff_forall_exists_discOffset_gt (out : ReductionOutput f) :
    (¬ BoundedDiscrepancyAlong out.g out.d) ↔
      (∀ C : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > C) := by
  -- `¬bounded` ↔ `∀ C, HasDiscrepancyAtLeastAlong ... C` ↔ `∀ C, ∃ n, discOffset ... > C`.
  have h₁ : (¬ BoundedDiscrepancyAlong out.g out.d) ↔
      (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) := by
    simpa using (out.forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscrepancyAlong (f := f)).symm
  have h₂ : (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) ↔
      (∀ C : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > C) :=
    out.forall_hasDiscrepancyAtLeastAlong_iff_forall_exists_discOffset_gt (f := f)
  exact Iff.trans h₁ h₂

/-- Unboundedness along `out.d` rewritten as “arbitrarily large offset AP-sum witnesses”. -/
theorem not_boundedDiscrepancyAlong_iff_forall_exists_natAbs_apSumOffset_gt (out : ReductionOutput f) :
    (¬ BoundedDiscrepancyAlong out.g out.d) ↔
      (∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > C) := by
  have h₁ : (¬ BoundedDiscrepancyAlong out.g out.d) ↔
      (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) := by
    simpa using (out.forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscrepancyAlong (f := f)).symm
  have h₂ : (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) ↔
      (∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > C) :=
    out.forall_hasDiscrepancyAtLeastAlong_iff_forall_exists_natAbs_apSumOffset_gt (f := f)
  exact Iff.trans h₁ h₂

/-!
### Boundedness/unboundedness normal forms for a `ReductionOutput`

The stage-1 reduction interface is meant to be consumed as follows:
- if you have an *unboundedness* statement about the reduced sequence `out.g` along the fixed step
  `out.d`, rewrite it into an unboundedness statement about the offset discrepancies
  `discOffset f out.d out.m`.
- if you have a *boundedness* statement about `discOffset f out.d out.m`, transfer it back to a
  boundedness statement about `discrepancy out.g out.d`.

These lemmas are tiny wrappers around the existing rewrite/contract fields, but they are common
entry points for downstream stages.
-/

/-- Boundedness along the reduced step size `out.d`, phrased as a uniform bound on `discOffset`.

This is the “consumer-friendly” packaging: downstream stages typically want to bound or negate
`discOffset f out.d out.m` rather than mention `out.g` explicitly.
-/
theorem boundedDiscrepancyAlong_iff_exists_discOffset_le (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d ↔ (∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B) := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- Rewrite `discOffset` to the discrepancy of `out.g` using the AP-sum contract.
    simpa [discOffset, discrepancy, out.apSum_contract] using hB n
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- Rewrite the discrepancy of `out.g` to `discOffset` using the AP-sum contract.
    simpa [discOffset, discrepancy, out.apSum_contract] using hB n

/-- Convenience lemma: extract a uniform bound on `discOffset` from bounded discrepancy of `out.g`.

This is just the forward direction of `boundedDiscrepancyAlong_iff_exists_discOffset_le`.
-/
theorem exists_bound_discOffset_of_boundedDiscrepancyAlong (out : ReductionOutput f)
    (hb : BoundedDiscrepancyAlong out.g out.d) :
    ∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B :=
  (out.boundedDiscrepancyAlong_iff_exists_discOffset_le (f := f)).1 hb

/-- Convenience lemma: build bounded discrepancy of `out.g` from a uniform `discOffset` bound.

This is just the reverse direction of `boundedDiscrepancyAlong_iff_exists_discOffset_le`.
-/
theorem boundedDiscrepancyAlong_of_bound_discOffset (out : ReductionOutput f)
    (hB : ∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B) :
    BoundedDiscrepancyAlong out.g out.d :=
  (out.boundedDiscrepancyAlong_iff_exists_discOffset_le (f := f)).2 hB

/-!
### Interaction with `Context`

`Context f` packages a global boundedness hypothesis for the *original* sequence `f`.

The stage-1 reduction interface `ReductionOutput f` typically defines a derived sign sequence
`out.g` by shifting `f` by `out.m*out.d` and then focuses on discrepancy along the *single*
step size `out.d`.

The following lemmas let downstream stages quickly move between these two normal forms.
-/

/-- From a global boundedness context for `f`, get bounded discrepancy along the reduced step
size `out.d` for the reduced sequence `out.g`.

Concretely, this is the statement:
`∀ n, discrepancy out.g out.d n ≤ ctx.B + ctx.B`.
-/
theorem boundedDiscrepancyAlong_of_Context (out : ReductionOutput f) (ctx : Context f) :
    BoundedDiscrepancyAlong out.g out.d := by
  refine ⟨ctx.B + ctx.B, ?_⟩
  intro n
  -- Rewrite `out.g` to the literal shift of `f`, then apply the shift-boundedness lemma.
  simpa [out.g_eq] using
    (ctx.bound_discrepancy_shift_add (f := f) (d := out.d) (m := out.m) (n := n) out.hd)

/-- Pointwise `discOffset` bound extracted from `Context f` through a `ReductionOutput`.

This is the consumer-friendly formulation: it bounds the offset discrepancy of the original
sequence rather than mentioning the reduced sequence explicitly.
-/
theorem bound_discOffset_of_Context (out : ReductionOutput f) (ctx : Context f) (n : ℕ) :
    discOffset f out.d out.m n ≤ ctx.B + ctx.B := by
  -- Bound the reduced discrepancy using the previous lemma, then rewrite via the interface.
  have h : discrepancy out.g out.d n ≤ ctx.B + ctx.B := by
    rcases out.boundedDiscrepancyAlong_of_Context (f := f) ctx with ⟨B, hB⟩
    -- Here `B = ctx.B + ctx.B` by construction.
    simpa using hB n
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using h

/-- Uniform `discOffset` bound extracted from `Context f` through a `ReductionOutput`. -/
theorem forall_bound_discOffset_of_Context (out : ReductionOutput f) (ctx : Context f) :
    ∀ n : ℕ, discOffset f out.d out.m n ≤ ctx.B + ctx.B := by
  intro n
  exact out.bound_discOffset_of_Context (f := f) ctx n

/-- Negated form of `boundedDiscrepancyAlong_iff_exists_discOffset_le`.

This is a common normal form for *unboundedness* statements: it says there is **no** uniform
bound on the offset discrepancies.
-/
theorem not_boundedDiscrepancyAlong_iff_not_exists_discOffset_le (out : ReductionOutput f) :
    (¬ BoundedDiscrepancyAlong out.g out.d) ↔
      ¬ (∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B) := by
  simpa using (not_congr (out.boundedDiscrepancyAlong_iff_exists_discOffset_le (f := f)))

/-- Unboundedness along `out.d`, phrased as “no uniform bound on `discOffset`”.

This is just the composition of:
- `out.forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscrepancyAlong`, and
- `out.not_boundedDiscrepancyAlong_iff_not_exists_discOffset_le`.
-/
theorem forall_hasDiscrepancyAtLeastAlong_iff_not_exists_discOffset_le (out : ReductionOutput f) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) ↔
      ¬ (∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B) := by
  -- Rewrite “unbounded along `out.d`” into a `discOffset`-normal form.
  simpa [out.not_boundedDiscrepancyAlong_iff_not_exists_discOffset_le (f := f)] using
    (out.forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscrepancyAlong (f := f))

/-- Same as `forall_hasDiscrepancyAtLeastAlong_iff_not_exists_discOffset_le`, but at the AP-sum level.

This is the `Int.natAbs (apSumOffset ...)` analogue of the previous lemma.
-/
theorem forall_hasDiscrepancyAtLeastAlong_iff_not_exists_natAbs_apSumOffset_le (out : ReductionOutput f) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) ↔
      ¬ (∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ B) := by
  -- `discOffset` is definitional.
  simpa [discOffset] using
    (out.forall_hasDiscrepancyAtLeastAlong_iff_not_exists_discOffset_le (f := f))

/-- Same as `not_boundedDiscrepancyAlong_iff_not_exists_discOffset_le`, but at the AP-sum level.

This is the `Int.natAbs (apSumOffset ...)` analogue of the previous lemma.
-/
theorem not_boundedDiscrepancyAlong_iff_not_exists_natAbs_apSumOffset_le (out : ReductionOutput f) :
    (¬ BoundedDiscrepancyAlong out.g out.d) ↔
      ¬ (∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ B) := by
  -- `discOffset` is definitional.
  simpa [discOffset] using
    (out.not_boundedDiscrepancyAlong_iff_not_exists_discOffset_le (f := f))

/-- A strict-inequality version of `boundedDiscrepancyAlong_iff_exists_discOffset_le`.

This is occasionally more convenient when a downstream stage produces a bound of the form
`discOffset … < B` rather than `≤ B`.
-/
theorem boundedDiscrepancyAlong_iff_exists_discOffset_lt (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d ↔ (∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n < B) := by
  constructor
  · intro hb
    rcases (out.boundedDiscrepancyAlong_iff_exists_discOffset_le (f := f)).1 hb with ⟨B, hB⟩
    refine ⟨B + 1, ?_⟩
    intro n
    exact Nat.lt_succ_of_le (hB n)
  · rintro ⟨B, hB⟩
    refine (out.boundedDiscrepancyAlong_iff_exists_discOffset_le (f := f)).2 ?_
    refine ⟨B, ?_⟩
    intro n
    exact Nat.le_of_lt (hB n)

/-- Same as `boundedDiscrepancyAlong_iff_exists_discOffset_le`, but phrased directly in terms of
`Int.natAbs (apSumOffset ...)`.

This is often the most convenient normal form for later stages that work at the AP-sum level.
-/
theorem boundedDiscrepancyAlong_iff_exists_natAbs_apSumOffset_le (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d ↔
      (∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ B) := by
  -- `discOffset` is definitional.
  simpa [discOffset] using (out.boundedDiscrepancyAlong_iff_exists_discOffset_le (f := f))

/-- Strict-inequality version of `boundedDiscrepancyAlong_iff_exists_natAbs_apSumOffset_le`. -/
theorem boundedDiscrepancyAlong_iff_exists_natAbs_apSumOffset_lt (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d ↔
      (∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) < B) := by
  -- `discOffset` is definitional.
  simpa [discOffset] using (out.boundedDiscrepancyAlong_iff_exists_discOffset_lt (f := f))

/-- Same boundedness interface as `boundedDiscrepancyAlong_iff_exists_natAbs_apSumOffset_le`, but
rewritten to the affine nucleus `apSumFrom`.

This is often the nicest normal form for later Tao2015 stages that operate directly on affine
progressions.
-/
theorem boundedDiscrepancyAlong_iff_exists_natAbs_apSumFrom_mul_le (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d ↔
      (∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) ≤ B) := by
  -- Rewrite the `apSumOffset`-normal form through `apSumOffset_eq_apSumFrom_mul`.
  constructor
  · intro hb
    rcases (out.boundedDiscrepancyAlong_iff_exists_natAbs_apSumOffset_le (f := f)).1 hb with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- `apSumOffset f d m n = apSumFrom f (m*d) d n`.
    simpa [Tao2015.apSumOffset_eq_apSumFrom_mul] using hB n
  · rintro ⟨B, hB⟩
    refine (out.boundedDiscrepancyAlong_iff_exists_natAbs_apSumOffset_le (f := f)).2 ?_
    refine ⟨B, ?_⟩
    intro n
    simpa [Tao2015.apSumOffset_eq_apSumFrom_mul] using hB n

/-- Strict-inequality version of `boundedDiscrepancyAlong_iff_exists_natAbs_apSumFrom_mul_le`. -/
theorem boundedDiscrepancyAlong_iff_exists_natAbs_apSumFrom_mul_lt (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d ↔
      (∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) < B) := by
  -- Derive from the `≤` version by a `+1` trick.
  constructor
  · intro hb
    rcases (out.boundedDiscrepancyAlong_iff_exists_natAbs_apSumFrom_mul_le (f := f)).1 hb with ⟨B, hB⟩
    refine ⟨B + 1, ?_⟩
    intro n
    exact Nat.lt_succ_of_le (hB n)
  · rintro ⟨B, hB⟩
    refine (out.boundedDiscrepancyAlong_iff_exists_natAbs_apSumFrom_mul_le (f := f)).2 ?_
    refine ⟨B, ?_⟩
    intro n
    exact Nat.le_of_lt (hB n)

/-- Unboundedness witness normal form for `out.g` along `out.d`, rewritten to the affine nucleus.

This is the `apSumFrom` analogue of
`not_boundedDiscrepancyAlong_iff_forall_exists_natAbs_apSumOffset_gt`.
-/
theorem not_boundedDiscrepancyAlong_iff_forall_exists_natAbs_apSumFrom_mul_gt (out : ReductionOutput f) :
    (¬ BoundedDiscrepancyAlong out.g out.d) ↔
      (∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > B) := by
  -- Start from the `apSumOffset` witness normal form, then rewrite to `apSumFrom`.
  constructor
  · intro h
    have h' := (out.not_boundedDiscrepancyAlong_iff_forall_exists_natAbs_apSumOffset_gt (f := f)).1 h
    intro B
    rcases h' B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [Tao2015.apSumOffset_eq_apSumFrom_mul] using hn
  · intro h
    refine (out.not_boundedDiscrepancyAlong_iff_forall_exists_natAbs_apSumOffset_gt (f := f)).2 ?_
    intro B
    rcases h B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [Tao2015.apSumOffset_eq_apSumFrom_mul] using hn

/-- Transfer the `Context`-level bound on `f` to a bound on the reduced discrepancy `discrepancy out.g out.d`.

This is a tiny wrapper combining:
- the `Context` bound on offset discrepancies (`Context.bound_discOffset`), and
- the bridge rule `out.apSum_contract`.

It is a common entry point for downstream reduction stages.
-/
theorem bound_discrepancy_of_context (out : ReductionOutput f) (ctx : Context f) :
    ∀ n : ℕ, discrepancy out.g out.d n ≤ ctx.B + ctx.B := by
  intro n
  have h := ctx.bound_discOffset (f := f) (d := out.d) (m := out.m) (n := n) out.hd
  -- Rewrite `discOffset` to `discrepancy out.g`.
  simpa [discOffset, discrepancy, out.apSum_contract] using h

/-- A `Context f` implies a `2 * ctx.B` bound on the reduced discrepancy.

This is just `bound_discrepancy_of_context` with the right-hand side written multiplicatively.
-/
theorem bound_discrepancy_of_context_two_mul (out : ReductionOutput f) (ctx : Context f) :
    ∀ n : ℕ, discrepancy out.g out.d n ≤ 2 * ctx.B := by
  intro n
  simpa [two_mul] using (out.bound_discrepancy_of_context (f := f) ctx n)

/-- Transfer a `Context f` bound to the affine nucleus `apSumFrom f (out.m*out.d) out.d`.

This is a convenient “drop the `discrepancy` wrapper” lemma: many downstream stages want to work
with the affine AP-sum nucleus directly.
-/
theorem bound_natAbs_apSumFrom_mul_of_context (out : ReductionOutput f) (ctx : Context f) :
    ∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) ≤ ctx.B + ctx.B := by
  intro n
  -- Rewrite `discrepancy out.g` as `natAbs (apSumFrom ...)`, then apply `bound_discrepancy_of_context`.
  simpa [out.discrepancy_eq_natAbs_apSumFrom_mul (f := f) (n := n)] using
    (out.bound_discrepancy_of_context (f := f) ctx n)

/-- Multiplicative-normal-form variant of `bound_natAbs_apSumFrom_mul_of_context`. -/
theorem bound_natAbs_apSumFrom_mul_of_context_two_mul (out : ReductionOutput f) (ctx : Context f) :
    ∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) ≤ 2 * ctx.B := by
  intro n
  simpa [two_mul] using (out.bound_natAbs_apSumFrom_mul_of_context (f := f) ctx n)

/-- A `Context f` implies bounded discrepancy along the reduced step size `out.d`.

The resulting bound is `ctx.B + ctx.B`, matching `Context.bound_discOffset`.
-/
theorem boundedDiscrepancyAlong_of_context (out : ReductionOutput f) (ctx : Context f) :
    BoundedDiscrepancyAlong out.g out.d := by
  refine ⟨ctx.B + ctx.B, ?_⟩
  intro n
  exact out.bound_discrepancy_of_context (f := f) ctx n

/-- A `Context f` implies bounded discrepancy along `out.d` with bound `2 * ctx.B`. -/
theorem boundedDiscrepancyAlong_of_context_two_mul (out : ReductionOutput f) (ctx : Context f) :
    BoundedDiscrepancyAlong out.g out.d := by
  refine ⟨2 * ctx.B, ?_⟩
  intro n
  exact out.bound_discrepancy_of_context_two_mul (f := f) ctx n

/-- A boundedness hypothesis about the original sequence `f` implies bounded discrepancy along
`out.d` for the reduced sequence `out.g`.

This is the typical “boundedness survives stage-1 reduction” entry point: we first package the
existential bound `BoundedDiscrepancy f` into a `Context f`, then reuse
`boundedDiscrepancyAlong_of_context`.
-/
theorem boundedDiscrepancyAlong_of_boundedDiscrepancy (out : ReductionOutput f)
    (hb : BoundedDiscrepancy f) :
    BoundedDiscrepancyAlong out.g out.d := by
  -- Pick a witness bound `B` from `hb` and use the `Context` API.
  classical
  simpa using (out.boundedDiscrepancyAlong_of_context (f := f) (Context.ofBoundedDiscrepancy (f := f) hb))

/-- A slightly more explicit variant of `boundedDiscrepancyAlong_of_boundedDiscrepancy`.

This uses the multiplicative normal form `2 * B` for the resulting bound.
-/
theorem boundedDiscrepancyAlong_of_boundedDiscrepancy_two_mul (out : ReductionOutput f)
    (hb : BoundedDiscrepancy f) :
    BoundedDiscrepancyAlong out.g out.d := by
  classical
  simpa using
    (out.boundedDiscrepancyAlong_of_context_two_mul (f := f) (Context.ofBoundedDiscrepancy (f := f) hb))

/-- Unboundedness along the reduced step size `out.d`, rewritten as a witness normal form for
`discOffset`.

This is just `not_boundedDiscrepancyAlong_iff_forall_exists_discrepancy_gt` plus the
`discrepancy ↔ discOffset` rewrite.
-/
theorem not_boundedDiscrepancyAlong_iff_forall_exists_discOffset_gt (out : ReductionOutput f) :
    (¬ BoundedDiscrepancyAlong out.g out.d) ↔ (∀ B : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > B) := by
  -- Start from the standard witness normal form for `¬ BoundedDiscrepancyAlong`.
  -- Then rewrite `discrepancy out.g out.d` into `discOffset f out.d out.m`.
  -- `discOffset` and `discrepancy` are definitional wrappers around `Int.natAbs`.
  simpa [discOffset, discrepancy, out.apSum_contract] using
    (Tao2015.not_boundedDiscrepancyAlong_iff_forall_exists_discrepancy_gt (g := out.g) (d := out.d))

/-- Same as `not_boundedDiscrepancyAlong_iff_forall_exists_discOffset_gt`, but phrased directly in
terms of `Int.natAbs (apSumOffset ...)` witnesses.

This is often the best normal form for later pipeline stages that work at the AP-sum level.
-/
theorem not_boundedDiscrepancyAlong_iff_forall_exists_natAbs_apSumOffset_gt (out : ReductionOutput f) :
    (¬ BoundedDiscrepancyAlong out.g out.d) ↔
      (∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > B) := by
  -- `discOffset` is definitional.
  simpa [discOffset] using (out.not_boundedDiscrepancyAlong_iff_forall_exists_discOffset_gt (f := f))

/-- A slightly more “Tao-style” unboundedness packaging: `∀ B, ∃ n, B < discOffset ...`.

This is the same as `not_boundedDiscrepancyAlong_iff_forall_exists_discOffset_gt`, but with the
inequality oriented as `B < ...`.
-/
theorem not_boundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (out : ReductionOutput f) :
    (¬ BoundedDiscrepancyAlong out.g out.d) ↔ (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using (out.not_boundedDiscrepancyAlong_iff_forall_exists_discOffset_gt (f := f))

/-- Promote a fixed-step discrepancy witness about `out.g` to the standard existential form.

This is just `HasDiscrepancyAtLeastAlong.toHasDiscrepancyAtLeast` specialized to `out.hd`.
-/
theorem hasDiscrepancyAtLeast_of_hasDiscrepancyAtLeastAlong (out : ReductionOutput f) {C : ℕ}
    (h : HasDiscrepancyAtLeastAlong out.g out.d C) :
    HasDiscrepancyAtLeast out.g C := by
  exact HasDiscrepancyAtLeastAlong.toHasDiscrepancyAtLeast (f := out.g) (d := out.d) (C := C) out.hd h

/-- Push `HasDiscrepancyAtLeastAlong` across the discrepancy wrapper.

`HasDiscrepancyAtLeastAlong` is stated using `Int.natAbs (apSum ...)`, while many downstream
arguments prefer the bundled wrapper `discrepancy`.
-/
theorem hasDiscrepancyAtLeastAlong_iff_exists_discrepancy_lt (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔ (∃ n : ℕ, C < discrepancy out.g out.d n) := by
  -- Unfold and normalize `a > b` as `b < a`.
  simp [HasDiscrepancyAtLeastAlong, discrepancy, gt_iff_lt]

/-- `>`-oriented version of `hasDiscrepancyAtLeastAlong_iff_exists_discrepancy_lt`. -/
theorem hasDiscrepancyAtLeastAlong_iff_exists_discrepancy_gt (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔ (∃ n : ℕ, discrepancy out.g out.d n > C) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using (out.hasDiscrepancyAtLeastAlong_iff_exists_discrepancy_lt (f := f) C)

/-- Extract an offset-discrepancy witness (`C < discOffset ...`) from a fixed-step witness about `out.g`. -/
theorem exists_discOffset_lt_of_hasDiscrepancyAtLeastAlong (out : ReductionOutput f) {C : ℕ}
    (h : HasDiscrepancyAtLeastAlong out.g out.d C) :
    ∃ n : ℕ, C < discOffset f out.d out.m n :=
  (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_lt (f := f) C).1 h

/-- Build a fixed-step witness about `out.g` from an offset-discrepancy witness (`C < discOffset ...`). -/
theorem hasDiscrepancyAtLeastAlong_of_exists_discOffset_lt (out : ReductionOutput f) {C : ℕ}
    (h : ∃ n : ℕ, C < discOffset f out.d out.m n) :
    HasDiscrepancyAtLeastAlong out.g out.d C :=
  (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_lt (f := f) C).2 h

/-- If the original sequence `f` is a sign sequence, then so is the derived sequence `out.g`.

This lemma is useful when constructing or refactoring `ReductionOutput`: it shows that the
`hg` field is *logically redundant* given `g_eq` and an external `IsSignSequence f` proof.
-/
theorem hg_derived (out : ReductionOutput f) (hf : IsSignSequence f) : IsSignSequence out.g := by
  simpa [out.g_eq] using (Tao2015.IsSignSequence.shift_add_mul (f := f) hf out.m out.d)

/-- The `hg` field is redundant when `f` is known to be a sign sequence.

Recorded as an extensional equality (proof irrelevance) to make future interface refactors easier.
-/
theorem hg_eq_derived (out : ReductionOutput f) (hf : IsSignSequence f) : out.hg = out.hg_derived (f := f) hf := by
  classical
  exact Subsingleton.elim _ _

/-- Function-extensional form of `apSum_contract`. -/
theorem apSum_contract_funext (out : ReductionOutput f) :
    (fun n => apSum out.g out.d n) = fun n => apSumOffset f out.d out.m n := by
  funext n
  exact out.apSum_contract n

/-- Pointwise form of the AP-sum bridge rule.

Marked `[simp]` because it is the main rewrite rule for moving from the reduced sequence `out.g`
back to the offset-sum family of `f`.
-/
@[simp] theorem apSum_contract_apply (out : ReductionOutput f) (n : ℕ) :
    apSum out.g out.d n = apSumOffset f out.d out.m n :=
  out.apSum_contract n

/-- `Int.natAbs` form of the AP-sum bridge rule.

This is a lightweight helper for pushing inequalities across `apSum_contract_apply`.
-/
theorem natAbs_apSum_contract (out : ReductionOutput f) (n : ℕ) :
    Int.natAbs (apSum out.g out.d n) = Int.natAbs (apSumOffset f out.d out.m n) := by
  simp [out.apSum_contract (f := f) (n := n)]

/-- Reverse orientation of `natAbs_apSum_contract`.

Not marked `[simp]` to avoid rewriting loops.
-/
theorem natAbs_apSumOffset_eq (out : ReductionOutput f) (n : ℕ) :
    Int.natAbs (apSumOffset f out.d out.m n) = Int.natAbs (apSum out.g out.d n) := by
  simpa using (out.natAbs_apSum_contract (f := f) n).symm

/-- Reverse orientation of `apSum_contract_apply`.

Not marked `[simp]` to avoid rewriting loops.
-/
theorem apSumOffset_eq_apSum_apply (out : ReductionOutput f) (n : ℕ) :
    apSumOffset f out.d out.m n = apSum out.g out.d n := by
  simpa using (out.apSum_contract_apply (f := f) (n := n)).symm

/-- Function-extensional form of the discrepancy rewrite rule. -/
theorem discrepancy_contract_funext (out : ReductionOutput f) :
    (fun n => discrepancy out.g out.d n) = fun n => discOffset f out.d out.m n := by
  funext n
  -- Both sides are definitional wrappers around `Int.natAbs`.
  simp [discrepancy, discOffset, out.apSum_contract]

/-- Pointwise form of `discrepancy_contract_funext`.

Marked `[simp]` because it is the main consumer-facing rewrite rule for the reduction output:
`discrepancy out.g out.d` is definitionally `discOffset f out.d out.m`.
-/
@[simp] theorem discrepancy_contract (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n = discOffset f out.d out.m n := by
  -- Both sides are definitional wrappers around `Int.natAbs`.
  simp [discrepancy, discOffset, out.apSum_contract]

/-- Reverse orientation of `discrepancy_contract`.

Not marked `[simp]` to avoid rewriting loops.
-/
theorem discOffset_eq_discrepancy (out : ReductionOutput f) (n : ℕ) :
    discOffset f out.d out.m n = discrepancy out.g out.d n := by
  simpa using (out.discrepancy_contract (f := f) n).symm

/-!
### Offset reassociation for a `ReductionOutput`

A common pattern in multi-stage reductions is that offsets accumulate additively.
The base lemma `Tao2015.discOffset_add` rewrites
`discOffset f d (m₁+m₂)` as a `discOffset` of a shifted sequence.

When `m₁` is the offset packaged in a `ReductionOutput`, the shifted sequence is exactly
`out.g`.  The following helpers record that specialization.
-/

/-- Re-associate an offset past the reduction output: `discOffset f d (out.m + m₂)` is the
same as `discOffset out.g d m₂`.

Intuitively: shifting `f` by `out.m*out.d` is exactly the reduced sequence `out.g`, so any
additional offset can be viewed as an offset of `out.g`.
-/
theorem discOffset_add_eq_discOffset (out : ReductionOutput f) (m₂ n : ℕ) :
    discOffset f out.d (out.m + m₂) n = discOffset out.g out.d m₂ n := by
  -- `discOffset_add` rewrites an accumulated offset into a shift of `f`.
  -- Then `out.g_eq` identifies that shift with `out.g`.
  simpa [out.g_eq, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (Tao2015.discOffset_add (f := f) (d := out.d) (m₁ := out.m) (m₂ := m₂) (n := n))

/-- AP-sum-level analogue of `discOffset_add_eq_discOffset`. -/
theorem apSumOffset_add_eq_apSumOffset (out : ReductionOutput f) (m₂ n : ℕ) :
    apSumOffset f out.d (out.m + m₂) n = apSumOffset out.g out.d m₂ n := by
  -- Same idea as `discOffset_add_eq_discOffset`, but at the `apSumOffset` level.
  simpa [out.g_eq, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (Tao2015.apSumOffset_add (f := f) (d := out.d) (m₁ := out.m) (m₂ := m₂) (n := n))

/-- `Int.natAbs` form of `apSumOffset_add_eq_apSumOffset`. -/
theorem natAbs_apSumOffset_add_eq (out : ReductionOutput f) (m₂ n : ℕ) :
    Int.natAbs (apSumOffset f out.d (out.m + m₂) n) =
      Int.natAbs (apSumOffset out.g out.d m₂ n) := by
  simp [out.apSumOffset_add_eq_apSumOffset (f := f) (m₂ := m₂) (n := n)]

/-- Reverse orientation of `discOffset_add_eq_discOffset`. -/
theorem discOffset_eq_discOffset_add (out : ReductionOutput f) (m₂ n : ℕ) :
    discOffset out.g out.d m₂ n = discOffset f out.d (out.m + m₂) n := by
  simpa using (out.discOffset_add_eq_discOffset (f := f) (m₂ := m₂) (n := n)).symm

/-- Reverse orientation of `apSumOffset_add_eq_apSumOffset`. -/
theorem apSumOffset_eq_apSumOffset_add (out : ReductionOutput f) (m₂ n : ℕ) :
    apSumOffset out.g out.d m₂ n = apSumOffset f out.d (out.m + m₂) n := by
  simpa using (out.apSumOffset_add_eq_apSumOffset (f := f) (m₂ := m₂) (n := n)).symm

/-- Affine-nucleus version of `apSumOffset_add_eq_apSumOffset`.

This rewrites an offset of the reduced sequence `out.g` into an `apSumFrom` of the original
sequence `f` with the accumulated start point `(out.m + m₂) * out.d`.
-/
theorem apSumFrom_add_mul_eq_apSumOffset (out : ReductionOutput f) (m₂ n : ℕ) :
    apSumFrom f ((out.m + m₂) * out.d) out.d n = apSumOffset out.g out.d m₂ n := by
  -- Start from the RHS and rewrite back to an offset sum of `f`.
  -- Then rewrite `apSumOffset` into the affine nucleus `apSumFrom`.
  have h₁ : apSumOffset out.g out.d m₂ n = apSumOffset f out.d (out.m + m₂) n := by
    simpa using (out.apSumOffset_eq_apSumOffset_add (f := f) (m₂ := m₂) (n := n))
  -- Now rewrite the accumulated offset sum to the affine nucleus.
  -- (Note: we keep the final result oriented as stated.)
  simpa [h₁, Tao2015.apSumOffset_eq_apSumFrom_mul, Nat.add_mul] using
    (Tao2015.apSumOffset_eq_apSumFrom_mul (f := f) (d := out.d) (m := out.m + m₂) (n := n)).symm

/-- Same as `apSumFrom_add_mul_eq_apSumOffset`, but oriented to rewrite `apSumOffset` as `apSumFrom`. -/
theorem apSumOffset_eq_apSumFrom_add_mul (out : ReductionOutput f) (m₂ n : ℕ) :
    apSumOffset out.g out.d m₂ n = apSumFrom f ((out.m + m₂) * out.d) out.d n := by
  simpa using (out.apSumFrom_add_mul_eq_apSumOffset (f := f) (m₂ := m₂) (n := n)).symm

/-!
### One-shot witness transport lemmas

These are “micro-API” helpers: they let downstream stages move *existential* discrepancy witnesses
back and forth across the reduction interface without first repackaging them as
`HasDiscrepancyAtLeastAlong`.
-/

/-- Transport a single discrepancy witness for the reduced sequence to an offset-discrepancy witness.

This is just a one-line rewrite using `discrepancy_contract`.
-/
theorem exists_discOffset_gt_of_exists_discrepancy_gt (out : ReductionOutput f) {C : ℕ}
    (h : ∃ n : ℕ, discrepancy out.g out.d n > C) :
    ∃ n : ℕ, discOffset f out.d out.m n > C := by
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [out.discrepancy_contract (f := f) (n := n)] using hn

/-- Transport a single offset-discrepancy witness to a discrepancy witness for the reduced sequence.

This is the reverse direction of `exists_discOffset_gt_of_exists_discrepancy_gt`.
-/
theorem exists_discrepancy_gt_of_exists_discOffset_gt (out : ReductionOutput f) {C : ℕ}
    (h : ∃ n : ℕ, discOffset f out.d out.m n > C) :
    ∃ n : ℕ, discrepancy out.g out.d n > C := by
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [out.discOffset_eq_discrepancy (f := f) (n := n)] using hn

/-- `natAbs(apSumOffset ...)` witness form transported from a reduced-sequence discrepancy witness. -/
theorem exists_natAbs_apSumOffset_gt_of_exists_discrepancy_gt (out : ReductionOutput f) {C : ℕ}
    (h : ∃ n : ℕ, discrepancy out.g out.d n > C) :
    ∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > C := by
  rcases out.exists_discOffset_gt_of_exists_discrepancy_gt (f := f) (C := C) h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [discOffset] using hn

/-- Reduced-sequence discrepancy witness transported from a `natAbs(apSumOffset ...)` witness. -/
theorem exists_discrepancy_gt_of_exists_natAbs_apSumOffset_gt (out : ReductionOutput f) {C : ℕ}
    (h : ∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > C) :
    ∃ n : ℕ, discrepancy out.g out.d n > C := by
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  -- `discrepancy out.g out.d n = discOffset ... = natAbs(apSumOffset ...)`.
  simpa [discOffset, discrepancy, out.apSum_contract (f := f) (n := n)] using hn

/-- Derive the bridge rule `apSum out.g out.d = apSumOffset f out.d out.m` purely from `g_eq`.

This is useful when constructing a `ReductionOutput`: you can often avoid proving
`apSum_contract` by hand.
-/
theorem apSum_contract_derived (out : ReductionOutput f) :
    ∀ n : ℕ, apSum out.g out.d n = apSumOffset f out.d out.m n := by
  intro n
  -- `apSumOffset` is definitionally an AP sum of the shifted sequence.
  simpa [out.g_eq] using
    (apSumOffset_eq_apSum_shift_add (f := f) (d := out.d) (m := out.m) (n := n)).symm

/-- Standalone bridge rule: if `g` is literally a shift of `f` by `m*d`, then `apSum g d` is an
offset AP sum of `f`.

This lemma is useful when *constructing* a `ReductionOutput`: it lets you prove the bridge
property without mentioning the structure.
-/
theorem apSum_contract_of_g_eq (f g : ℕ → ℤ) (d m : ℕ) (hgEq : g = fun k => f (k + m * d)) :
    ∀ n : ℕ, apSum g d n = apSumOffset f d m n := by
  intro n
  -- Expand `apSumOffset` to an `apSum` on the shifted sequence, then rewrite by `hgEq`.
  simpa [hgEq] using
    (apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n)).symm

/-- Affine-nucleus bridge rule: rewrite the reduced homogeneous AP sums directly as `apSumFrom`.

This is a small convenience wrapper around:
- `apSum_contract_of_g_eq`, and
- `apSumOffset_eq_apSumFrom_mul`.

Downstream Tao2015 stages often prefer the affine nucleus `apSumFrom` over the offset form.
-/
theorem apSumFrom_contract_of_g_eq (f g : ℕ → ℤ) (d m : ℕ)
    (hgEq : g = fun k => f (k + m * d)) :
    ∀ n : ℕ, apSum g d n = apSumFrom f (m * d) d n := by
  intro n
  -- First rewrite to `apSumOffset`, then rewrite `apSumOffset` to the affine nucleus `apSumFrom`.
  simpa [apSumOffset_eq_apSumFrom_mul] using
    (apSum_contract_of_g_eq (f := f) (g := g) (d := d) (m := m) hgEq n)

/-- `Int.natAbs` form of `apSumFrom_contract_of_g_eq`. -/
theorem natAbs_apSumFrom_contract_of_g_eq (f g : ℕ → ℤ) (d m : ℕ)
    (hgEq : g = fun k => f (k + m * d)) :
    ∀ n : ℕ, Int.natAbs (apSum g d n) = Int.natAbs (apSumFrom f (m * d) d n) := by
  intro n
  simp [apSumFrom_contract_of_g_eq (f := f) (g := g) (d := d) (m := m) hgEq n]

/-- Discrepancy bridge rule, rewritten to the affine nucleus `apSumFrom`. -/
theorem discrepancy_eq_natAbs_apSumFrom_mul_of_g_eq (f g : ℕ → ℤ) (d m : ℕ)
    (hgEq : g = fun k => f (k + m * d)) :
    ∀ n : ℕ, discrepancy g d n = Int.natAbs (apSumFrom f (m * d) d n) := by
  intro n
  simp [discrepancy, apSumFrom_contract_of_g_eq (f := f) (g := g) (d := d) (m := m) hgEq n]

/-- Fixed-step discrepancy witnesses for a shifted sequence, in affine-nucleus form (`>`-oriented).

This is the witness-level analogue of `discrepancy_eq_natAbs_apSumFrom_mul_of_g_eq`.
-/
theorem hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_mul_gt_of_g_eq
    (f g : ℕ → ℤ) (d m C : ℕ) (hgEq : g = fun k => f (k + m * d)) :
    HasDiscrepancyAtLeastAlong g d C ↔
      (∃ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  -- Rewrite `HasDiscrepancyAtLeastAlong` to a `discrepancy` witness, then use the affine bridge.
  simp [HasDiscrepancyAtLeastAlong.iff_exists_discrepancy_gt,
    discrepancy_eq_natAbs_apSumFrom_mul_of_g_eq (f := f) (g := g) (d := d) (m := m) hgEq]

/-- Fixed-step discrepancy witnesses for a shifted sequence, in affine-nucleus form (`<`-oriented).

This is just the `<`-oriented version of
`hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_mul_gt_of_g_eq`.
-/
theorem hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_mul_lt_of_g_eq
    (f g : ℕ → ℤ) (d m C : ℕ) (hgEq : g = fun k => f (k + m * d)) :
    HasDiscrepancyAtLeastAlong g d C ↔
      (∃ n : ℕ, C < Int.natAbs (apSumFrom f (m * d) d n)) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using
    (hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_mul_gt_of_g_eq
      (f := f) (g := g) (d := d) (m := m) (C := C) hgEq)

/-- Transfer contract (≤) in affine-nucleus form.

If you can bound `Int.natAbs (apSumFrom f (m*d) d n)` uniformly, you can bound the reduced
discrepancy `discrepancy g d n` uniformly.
-/
theorem contract_discrepancy_le_of_apSumFrom_contract (f g : ℕ → ℤ) (d m B : ℕ)
    (h : ∀ n : ℕ, apSum g d n = apSumFrom f (m * d) d n) :
    (∀ n, Int.natAbs (apSumFrom f (m * d) d n) ≤ B) → ∀ n, discrepancy g d n ≤ B := by
  intro hB n
  -- `discrepancy = natAbs(apSum ...)`, then rewrite `apSum` using `h`.
  simpa [discrepancy, h n] using hB n

/-- Transfer contract (<) in affine-nucleus form.

This is the strict-inequality analogue of `contract_discrepancy_le_of_apSumFrom_contract`.
-/
theorem contract_discrepancy_lt_of_apSumFrom_contract (f g : ℕ → ℤ) (d m B : ℕ)
    (h : ∀ n : ℕ, apSum g d n = apSumFrom f (m * d) d n) :
    (∀ n, Int.natAbs (apSumFrom f (m * d) d n) < B) → ∀ n, discrepancy g d n < B := by
  intro hB n
  -- `discrepancy = natAbs(apSum ...)`, then rewrite `apSum` using `h`.
  simpa [discrepancy, h n] using hB n

/-- The same strict-inequality transfer contract as `contract_discrepancy_lt_of_apSumFrom_contract`,
but derived from the shift equation `g = fun k => f (k + m*d)`.
-/
theorem contract_discrepancy_lt_of_g_eq_apSumFrom (f g : ℕ → ℤ) (d m B : ℕ)
    (hgEq : g = fun k => f (k + m * d)) :
    (∀ n, Int.natAbs (apSumFrom f (m * d) d n) < B) → ∀ n, discrepancy g d n < B := by
  -- Reduce to the generic transfer lemma using the derived affine bridge rule.
  exact contract_discrepancy_lt_of_apSumFrom_contract (f := f) (g := g) (d := d) (m := m) (B := B)
    (apSumFrom_contract_of_g_eq (f := f) (g := g) (d := d) (m := m) hgEq)

/-- The same transfer contract as `contract_discrepancy_le_of_apSumFrom_contract`, but derived
from the shift equation `g = fun k => f (k + m*d)`.
-/
theorem contract_discrepancy_le_of_g_eq_apSumFrom (f g : ℕ → ℤ) (d m B : ℕ)
    (hgEq : g = fun k => f (k + m * d)) :
    (∀ n, Int.natAbs (apSumFrom f (m * d) d n) ≤ B) → ∀ n, discrepancy g d n ≤ B := by
  -- Reduce to the generic transfer lemma using the derived affine bridge rule.
  exact contract_discrepancy_le_of_apSumFrom_contract (f := f) (g := g) (d := d) (m := m) (B := B)
    (apSumFrom_contract_of_g_eq (f := f) (g := g) (d := d) (m := m) hgEq)

/-- Standalone discrepancy bridge rule, derived from `apSum_contract_of_g_eq`. -/
theorem discrepancy_contract_of_g_eq (f g : ℕ → ℤ) (d m : ℕ) (hgEq : g = fun k => f (k + m * d)) :
    ∀ n : ℕ, discrepancy g d n = discOffset f d m n := by
  intro n
  -- Both sides are definitional wrappers around `Int.natAbs`.
  simp [discrepancy, discOffset, apSum_contract_of_g_eq (f := f) (g := g) (d := d) (m := m) hgEq]

/-- Discrepancy bridge rule, given a pointwise bridge rule for AP sums.

This is the “interface-free” version of `ReductionOutput.discrepancy_eq_discOffset`.
It is useful when you want to reason about a reduction step *before* packaging it into a
`ReductionOutput`.
-/
theorem discrepancy_contract_of_apSum_contract (f g : ℕ → ℤ) (d m : ℕ)
    (h : ∀ n : ℕ, apSum g d n = apSumOffset f d m n) :
    ∀ n : ℕ, discrepancy g d n = discOffset f d m n := by
  intro n
  -- Both sides are definitional wrappers around `Int.natAbs`.
  simp [discrepancy, discOffset, h n]

/-- `Int.natAbs` bridge rule, given a pointwise bridge rule for AP sums.

This is the sum-level analogue of `discrepancy_contract_of_apSum_contract`.
-/
theorem natAbs_apSum_contract_of_apSum_contract (f g : ℕ → ℤ) (d m : ℕ)
    (h : ∀ n : ℕ, apSum g d n = apSumOffset f d m n) :
    ∀ n : ℕ, Int.natAbs (apSum g d n) = Int.natAbs (apSumOffset f d m n) := by
  intro n
  simp [h n]

/-- Consumer-friendly transfer lemma: a `≤` bound on absolute AP sums transfers across an
AP-sum bridge rule.

This is occasionally more convenient than rewriting `discrepancy`/`discOffset` wrappers.
-/
theorem natAbs_apSum_le_iff_natAbs_apSumOffset_le_of_apSum_contract (f g : ℕ → ℤ) (d m B : ℕ)
    (h : ∀ n : ℕ, apSum g d n = apSumOffset f d m n) (n : ℕ) :
    Int.natAbs (apSum g d n) ≤ B ↔ Int.natAbs (apSumOffset f d m n) ≤ B := by
  simpa [h n]

/-- Reverse orientation of `natAbs_apSum_le_iff_natAbs_apSumOffset_le_of_apSum_contract`. -/
theorem natAbs_apSumOffset_le_iff_natAbs_apSum_le_of_apSum_contract (f g : ℕ → ℤ) (d m B : ℕ)
    (h : ∀ n : ℕ, apSum g d n = apSumOffset f d m n) (n : ℕ) :
    Int.natAbs (apSumOffset f d m n) ≤ B ↔ Int.natAbs (apSum g d n) ≤ B := by
  simpa using (natAbs_apSum_le_iff_natAbs_apSumOffset_le_of_apSum_contract
    (f := f) (g := g) (d := d) (m := m) (B := B) h n).symm

/-- Transfer contract (≤): any uniform bound on the offset discrepancy transfers to a uniform
bound on the discrepancy of `g`.

This is the “interface-free” version of the `contract_discrepancy_le` field.
-/
theorem contract_discrepancy_le_of_apSum_contract (f g : ℕ → ℤ) (d m B : ℕ)
    (h : ∀ n : ℕ, apSum g d n = apSumOffset f d m n) :
    (∀ n, discOffset f d m n ≤ B) → ∀ n, discrepancy g d n ≤ B := by
  intro hB n
  -- Rewrite the discrepancy of `g` to `discOffset` using `h`.
  simpa [discrepancy, discOffset, h n] using hB n

/-- Transfer contract (<): strict-inequality version of `contract_discrepancy_le_of_apSum_contract`. -/
theorem contract_discrepancy_lt_of_apSum_contract (f g : ℕ → ℤ) (d m B : ℕ)
    (h : ∀ n : ℕ, apSum g d n = apSumOffset f d m n) :
    (∀ n, discOffset f d m n < B) → ∀ n, discrepancy g d n < B := by
  intro hB n
  -- Rewrite the discrepancy of `g` to `discOffset` using `h`.
  simpa [discrepancy, discOffset, h n] using hB n

/-- Witness-transport lemma: turn a fixed-step discrepancy witness for `g` into an offset-discrepancy
witness for `f`, using an AP-sum bridge rule.

This is the “interface-free” analogue of
`ReductionOutput.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt`.
-/
theorem hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt_of_apSum_contract
    (f g : ℕ → ℤ) (d m C : ℕ) (h : ∀ n : ℕ, apSum g d n = apSumOffset f d m n) :
    HasDiscrepancyAtLeastAlong g d C ↔ (∃ n : ℕ, discOffset f d m n > C) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- `discOffset` is definitional wrapper around `Int.natAbs (apSumOffset ...)`.
    simpa [HasDiscrepancyAtLeastAlong, discOffset, h n] using hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [HasDiscrepancyAtLeastAlong, discOffset, h n] using hn

/-- `<`-oriented variant of `hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt_of_apSum_contract`. -/
theorem hasDiscrepancyAtLeastAlong_iff_exists_discOffset_lt_of_apSum_contract
    (f g : ℕ → ℤ) (d m C : ℕ) (h : ∀ n : ℕ, apSum g d n = apSumOffset f d m n) :
    HasDiscrepancyAtLeastAlong g d C ↔ (∃ n : ℕ, C < discOffset f d m n) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using
    (hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt_of_apSum_contract
      (f := f) (g := g) (d := d) (m := m) (C := C) h)

/-- Reverse transfer contract (≤): a uniform bound on `discrepancy g d` transfers to a uniform bound
on `discOffset f d m`, derived from an AP-sum bridge rule.
-/
theorem contract_discOffset_le_of_apSum_contract (f g : ℕ → ℤ) (d m B : ℕ)
    (h : ∀ n : ℕ, apSum g d n = apSumOffset f d m n) :
    (∀ n, discrepancy g d n ≤ B) → ∀ n, discOffset f d m n ≤ B := by
  -- Convert the AP-sum bridge into a discrepancy-level bridge, then use the reverse transfer lemma.
  have h' : ∀ n : ℕ, discrepancy g d n = discOffset f d m n :=
    discrepancy_contract_of_apSum_contract (f := f) (g := g) (d := d) (m := m) h
  exact contract_discOffset_le_of_discrepancy_contract (f := f) (g := g) (d := d) (m := m) (B := B) h'

/-- Reverse transfer contract (<): strict version of `contract_discOffset_le_of_apSum_contract`. -/
theorem contract_discOffset_lt_of_apSum_contract (f g : ℕ → ℤ) (d m B : ℕ)
    (h : ∀ n : ℕ, apSum g d n = apSumOffset f d m n) :
    (∀ n, discrepancy g d n < B) → ∀ n, discOffset f d m n < B := by
  have h' : ∀ n : ℕ, discrepancy g d n = discOffset f d m n :=
    discrepancy_contract_of_apSum_contract (f := f) (g := g) (d := d) (m := m) h
  exact contract_discOffset_lt_of_discrepancy_contract (f := f) (g := g) (d := d) (m := m) (B := B) h'

/-- Transfer contract (≤) using a discrepancy-level bridge rule.

This is sometimes the most convenient form: downstream steps can prove an identity about
`discrepancy` directly (instead of going through `apSum`).
-/
theorem contract_discrepancy_le_of_discrepancy_contract (f g : ℕ → ℤ) (d m B : ℕ)
    (h : ∀ n : ℕ, discrepancy g d n = discOffset f d m n) :
    (∀ n, discOffset f d m n ≤ B) → ∀ n, discrepancy g d n ≤ B := by
  intro hB n
  -- Rewrite `discrepancy g d n` to the offset discrepancy using `h`.
  simpa [h n] using hB n

/-- Transfer contract (<) using a discrepancy-level bridge rule.

This is the strict-inequality analogue of `contract_discrepancy_le_of_discrepancy_contract`.
-/
theorem contract_discrepancy_lt_of_discrepancy_contract (f g : ℕ → ℤ) (d m B : ℕ)
    (h : ∀ n : ℕ, discrepancy g d n = discOffset f d m n) :
    (∀ n, discOffset f d m n < B) → ∀ n, discrepancy g d n < B := by
  intro hB n
  -- Rewrite `discrepancy g d n` to the offset discrepancy using `h`.
  simpa [h n] using hB n

/-- Unboundedness along a fixed step transfers across a discrepancy-level bridge.

This is the witness-level analogue of `contract_discrepancy_le_of_discrepancy_contract`.
-/
theorem unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt_of_discrepancy_contract
    (f g : ℕ → ℤ) (d m : ℕ)
    (h : ∀ n : ℕ, discrepancy g d n = discOffset f d m n) :
    UnboundedDiscrepancyAlong g d ↔ (∀ B : ℕ, ∃ n : ℕ, B < discOffset f d m n) := by
  -- Unfold the witness predicate and rewrite pointwise.
  simp [UnboundedDiscrepancyAlong, h]

/-- Unboundedness transfer lemma derived from an AP-sum bridge rule.

This is a convenience wrapper around
`unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt_of_discrepancy_contract`.
-/
theorem unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt_of_apSum_contract
    (f g : ℕ → ℤ) (d m : ℕ)
    (h : ∀ n : ℕ, apSum g d n = apSumOffset f d m n) :
    UnboundedDiscrepancyAlong g d ↔ (∀ B : ℕ, ∃ n : ℕ, B < discOffset f d m n) := by
  have h' : ∀ n : ℕ, discrepancy g d n = discOffset f d m n :=
    discrepancy_contract_of_apSum_contract (f := f) (g := g) (d := d) (m := m) h
  simpa using
    (unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt_of_discrepancy_contract
      (f := f) (g := g) (d := d) (m := m) h')

/-- Reverse transfer contract (≤): a uniform bound on `discrepancy g d` transfers to a uniform bound
on `discOffset f d m`.

This is the converse direction of `contract_discrepancy_le_of_discrepancy_contract`, and is useful
when the pipeline temporarily works with the reduced sequence `g` but later needs to return to the
original offset-discrepancy family.
-/
theorem contract_discOffset_le_of_discrepancy_contract (f g : ℕ → ℤ) (d m B : ℕ)
    (h : ∀ n : ℕ, discrepancy g d n = discOffset f d m n) :
    (∀ n, discrepancy g d n ≤ B) → ∀ n, discOffset f d m n ≤ B := by
  intro hB n
  -- Rewrite `discOffset f d m n` to `discrepancy g d n` using `h`.
  simpa [h n] using hB n

/-- Reverse transfer contract (<): strict version of `contract_discOffset_le_of_discrepancy_contract`. -/
theorem contract_discOffset_lt_of_discrepancy_contract (f g : ℕ → ℤ) (d m B : ℕ)
    (h : ∀ n : ℕ, discrepancy g d n = discOffset f d m n) :
    (∀ n, discrepancy g d n < B) → ∀ n, discOffset f d m n < B := by
  intro hB n
  simpa [h n] using hB n

/-- Derive `contract_discrepancy_le_of_discrepancy_contract` from an AP-sum bridge rule.

This is just a small wrapper around `discrepancy_contract_of_apSum_contract`.
-/
theorem contract_discrepancy_le_of_apSum_contract' (f g : ℕ → ℤ) (d m B : ℕ)
    (h : ∀ n : ℕ, apSum g d n = apSumOffset f d m n) :
    (∀ n, discOffset f d m n ≤ B) → ∀ n, discrepancy g d n ≤ B := by
  -- First convert the AP-sum bridge to a discrepancy bridge, then reuse the discrepancy-level lemma.
  apply contract_discrepancy_le_of_discrepancy_contract (f := f) (g := g) (d := d) (m := m) (B := B)
  · exact discrepancy_contract_of_apSum_contract (f := f) (g := g) (d := d) (m := m) h

/-- The `apSum_contract` field is redundant: it is implied by `g_eq`.

Keeping this lemma around makes it easy to refactor the interface later.
-/
theorem apSum_contract_eq_derived (out : ReductionOutput f) :
    out.apSum_contract = out.apSum_contract_derived (f := f) := by
  classical
  funext n
  -- Both sides are proofs of the same proposition; use proof irrelevance.
  exact Subsingleton.elim _ _

/-- A derived version of the discrepancy transfer contract.

This does not use the `contract_discrepancy_le` field; it only needs the `apSum_contract` bridge.

Useful when *constructing* a `ReductionOutput`: you can often fill the transfer contract
automatically after proving the AP-sum bridge.
-/
theorem contract_discrepancy_le_derived (out : ReductionOutput f) (B : ℕ) :
    (∀ n, discOffset f out.d out.m n ≤ B) → ∀ n, discrepancy out.g out.d n ≤ B := by
  exact
    contract_discrepancy_le_of_apSum_contract (f := f) (g := out.g) (d := out.d) (m := out.m)
      (B := B) (h := out.apSum_contract)

/-- The `contract_discrepancy_le` field is redundant: it is implied by `apSum_contract`.

This lemma is to `contract_discrepancy_le` what `apSum_contract_eq_derived` is to
`apSum_contract`: it makes future interface refactors easier.
-/
theorem contract_discrepancy_le_eq_derived (out : ReductionOutput f) :
    out.contract_discrepancy_le =
      fun B =>
        contract_discrepancy_le_of_apSum_contract (f := f) (g := out.g) (d := out.d) (m := out.m)
          (B := B) (h := out.apSum_contract) := by
  classical
  funext B hB n
  -- Both sides are proofs of the same proposition; use proof irrelevance.
  exact Subsingleton.elim _ _

/-- Derive the discrepancy rewrite rule purely from `g_eq`.

This variant does not rely on the `apSum_contract` field.
-/
theorem discrepancy_eq_discOffset_derived (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n = discOffset f out.d out.m n := by
  -- Both sides are definitional wrappers around `Int.natAbs`.
  simp [discrepancy, discOffset, out.g_eq, apSumOffset_eq_apSum_shift_add]

/-- A derived version of `apSumOffset_eq_apSum` that does not use the `apSum_contract` field.

This is handy when you have a `ReductionOutput` built from a literal `g = shift f` proof but
haven't filled `apSum_contract` yet.
-/
theorem apSumOffset_eq_apSum_derived (out : ReductionOutput f) (n : ℕ) :
    apSumOffset f out.d out.m n = apSum out.g out.d n := by
  -- Expand `apSumOffset` to an `apSum` on the shifted sequence, then rewrite by `out.g_eq`.
  simpa [out.g_eq] using
    (apSumOffset_eq_apSum_shift_add (f := f) (d := out.d) (m := out.m) (n := n))

/-- A derived version of `discOffset_eq_discrepancy` that does not use the `apSum_contract` field. -/
theorem discOffset_eq_discrepancy_derived (out : ReductionOutput f) (n : ℕ) :
    discOffset f out.d out.m n = discrepancy out.g out.d n := by
  -- Both sides are definitional wrappers around `Int.natAbs`.
  simp [discOffset, discrepancy, out.g_eq, apSumOffset_eq_apSum_shift_add]

/-- A derived version of `contract_discrepancy_le_derived` that does not use `apSum_contract`.

It only needs the literal shift equation `g_eq`.
-/
theorem contract_discrepancy_le_derived' (out : ReductionOutput f) (B : ℕ) :
    (∀ n, discOffset f out.d out.m n ≤ B) → ∀ n, discrepancy out.g out.d n ≤ B := by
  intro hB n
  -- Reduce to the rewrite rule from `g_eq`.
  simpa [out.discOffset_eq_discrepancy_derived (f := f) (n := n)] using hB n

/-- Convenience constructor: build a `ReductionOutput` when `g` is literally a shift of `f`.

It fills `apSum_contract` and the discrepancy transfer contract automatically.
-/
noncomputable def mkShift (f : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (g : ℕ → ℤ)
    (hg : IsSignSequence g) (hgEq : g = fun k => f (k + m * d)) :
    ReductionOutput f := by
  refine ⟨d, m, hd, g, hg, hgEq, ?_, ?_⟩
  · intro n
    simpa [hgEq] using
      (apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n)).symm
  · intro B hB n
    -- Rewrite the discrepancy of `g` as the offset discrepancy of `f`.
    simpa [discrepancy, discOffset, hgEq, apSumOffset_eq_apSum_shift_add] using hB n

/-!
### `mkShift` simp API

These small lemmas make it easy to use a `ReductionOutput` produced by `mkShift` without
unfolding the constructor.
-/

@[simp] theorem mkShift_d (f : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (g : ℕ → ℤ)
    (hg : IsSignSequence g) (hgEq : g = fun k => f (k + m * d)) :
    (mkShift (f := f) (d := d) (m := m) hd (g := g) (hg := hg) (hgEq := hgEq)).d = d := by
  simp [mkShift]

@[simp] theorem mkShift_m (f : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (g : ℕ → ℤ)
    (hg : IsSignSequence g) (hgEq : g = fun k => f (k + m * d)) :
    (mkShift (f := f) (d := d) (m := m) hd (g := g) (hg := hg) (hgEq := hgEq)).m = m := by
  simp [mkShift]

@[simp] theorem mkShift_hd (f : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (g : ℕ → ℤ)
    (hg : IsSignSequence g) (hgEq : g = fun k => f (k + m * d)) :
    (mkShift (f := f) (d := d) (m := m) hd (g := g) (hg := hg) (hgEq := hgEq)).hd = hd := by
  simp [mkShift]

@[simp] theorem mkShift_g_eq (f : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (g : ℕ → ℤ)
    (hg : IsSignSequence g) (hgEq : g = fun k => f (k + m * d)) :
    (mkShift (f := f) (d := d) (m := m) hd (g := g) (hg := hg) (hgEq := hgEq)).g = g := by
  simp [mkShift]

@[simp] theorem mkShift_g_eq_shift (f : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (g : ℕ → ℤ)
    (hg : IsSignSequence g) (hgEq : g = fun k => f (k + m * d)) :
    (mkShift (f := f) (d := d) (m := m) hd (g := g) (hg := hg) (hgEq := hgEq)).g =
      fun k => f (k + m * d) := by
  -- `mkShift` stores `g` as a field, and `hgEq` identifies it as the intended shift.
  simpa [mkShift, hgEq]

@[simp] theorem mkShift_apSum_contract (f : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (g : ℕ → ℤ)
    (hg : IsSignSequence g) (hgEq : g = fun k => f (k + m * d)) (n : ℕ) :
    apSum (mkShift (f := f) (d := d) (m := m) hd (g := g) (hg := hg) (hgEq := hgEq)).g d n =
      apSumOffset f d m n := by
  simp [mkShift]

@[simp] theorem mkShift_discrepancy_contract (f : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (g : ℕ → ℤ)
    (hg : IsSignSequence g) (hgEq : g = fun k => f (k + m * d)) (n : ℕ) :
    discrepancy (mkShift (f := f) (d := d) (m := m) hd (g := g) (hg := hg) (hgEq := hgEq)).g d n =
      discOffset f d m n := by
  simp [discrepancy, discOffset, mkShift]

@[simp] theorem mkShift_contract_discrepancy_le (f : ℕ → ℤ) (d m : ℕ) (hd : d > 0) (g : ℕ → ℤ)
    (hg : IsSignSequence g) (hgEq : g = fun k => f (k + m * d)) (B : ℕ)
    (hB : ∀ n : ℕ, discOffset f d m n ≤ B) (n : ℕ) :
    (mkShift (f := f) (d := d) (m := m) hd (g := g) (hg := hg) (hgEq := hgEq)).contract_discrepancy_le B hB n =
      hB n := by
  -- The contract is just rewriting `discrepancy` to `discOffset`.
  simp [mkShift, discrepancy, discOffset]

/-- Convenience constructor: build a `ReductionOutput` from a *shift equation* and `hf`.

This is a common refactor-friendly form: you might define `g` elsewhere and only later
prove it is a shift of `f`. Given `hf : IsSignSequence f`, the sign-sequence proof for `g`
can be derived automatically from `hgEq`.
-/
noncomputable def mkShiftOfEq (f : ℕ → ℤ) (hf : IsSignSequence f) (d m : ℕ) (hd : d > 0)
    (g : ℕ → ℤ) (hgEq : g = fun k => f (k + m * d)) :
    ReductionOutput f := by
  refine mkShift (f := f) (d := d) (m := m) (hd := hd)
    (g := g)
    (hg := ?_)
    (hgEq := hgEq)
  -- transport `IsSignSequence` across the definitional equality
  simpa [hgEq] using (Tao2015.IsSignSequence.shift_add_mul (f := f) hf m d)

/-!
### `mkShiftOfEq` simp API

`mkShiftOfEq` is the most refactor-friendly constructor: you can define an auxiliary sequence `g`
first, and only later prove it is a shift of `f`.

The following tiny lemmas make it convenient to use the resulting `ReductionOutput` without
unfolding `mkShiftOfEq`.
-/

@[simp] theorem mkShiftOfEq_d (f : ℕ → ℤ) (hf : IsSignSequence f) (d m : ℕ) (hd : d > 0)
    (g : ℕ → ℤ) (hgEq : g = fun k => f (k + m * d)) :
    (mkShiftOfEq (f := f) (hf := hf) (d := d) (m := m) hd (g := g) (hgEq := hgEq)).d = d := by
  simp [mkShiftOfEq]

@[simp] theorem mkShiftOfEq_m (f : ℕ → ℤ) (hf : IsSignSequence f) (d m : ℕ) (hd : d > 0)
    (g : ℕ → ℤ) (hgEq : g = fun k => f (k + m * d)) :
    (mkShiftOfEq (f := f) (hf := hf) (d := d) (m := m) hd (g := g) (hgEq := hgEq)).m = m := by
  simp [mkShiftOfEq]

@[simp] theorem mkShiftOfEq_hd (f : ℕ → ℤ) (hf : IsSignSequence f) (d m : ℕ) (hd : d > 0)
    (g : ℕ → ℤ) (hgEq : g = fun k => f (k + m * d)) :
    (mkShiftOfEq (f := f) (hf := hf) (d := d) (m := m) hd (g := g) (hgEq := hgEq)).hd = hd := by
  simp [mkShiftOfEq]

@[simp] theorem mkShiftOfEq_g_eq (f : ℕ → ℤ) (hf : IsSignSequence f) (d m : ℕ) (hd : d > 0)
    (g : ℕ → ℤ) (hgEq : g = fun k => f (k + m * d)) :
    (mkShiftOfEq (f := f) (hf := hf) (d := d) (m := m) hd (g := g) (hgEq := hgEq)).g = g := by
  simp [mkShiftOfEq]

@[simp] theorem mkShiftOfEq_g_eq_shift (f : ℕ → ℤ) (hf : IsSignSequence f) (d m : ℕ) (hd : d > 0)
    (g : ℕ → ℤ) (hgEq : g = fun k => f (k + m * d)) :
    (mkShiftOfEq (f := f) (hf := hf) (d := d) (m := m) hd (g := g) (hgEq := hgEq)).g =
      fun k => f (k + m * d) := by
  -- `mkShiftOfEq` stores `g` as a field, and `hgEq` identifies it as the intended shift.
  simpa [mkShiftOfEq, hgEq]

/-- Convenience rewrite: `apSum` of the shifted output is `apSumOffset`.

Not marked `[simp]` to avoid rewriting loops (and to avoid expanding `apSumOffset`).
-/
theorem mkShiftOfEq_apSum_contract (f : ℕ → ℤ) (hf : IsSignSequence f)
    (d m : ℕ) (hd : d > 0) (g : ℕ → ℤ) (hgEq : g = fun k => f (k + m * d)) (n : ℕ) :
    apSum (mkShiftOfEq (f := f) (hf := hf) (d := d) (m := m) hd (g := g) (hgEq := hgEq)).g d n =
      apSumOffset f d m n := by
  simp [mkShiftOfEq, mkShift]

/-- Convenience rewrite: `discrepancy` of the shifted output is `discOffset`.

Not marked `[simp]` to avoid global simp pulling in `discrepancy`/`discOffset` expansions.
-/
theorem mkShiftOfEq_discrepancy_contract (f : ℕ → ℤ) (hf : IsSignSequence f)
    (d m : ℕ) (hd : d > 0) (g : ℕ → ℤ) (hgEq : g = fun k => f (k + m * d)) (n : ℕ) :
    discrepancy (mkShiftOfEq (f := f) (hf := hf) (d := d) (m := m) hd (g := g) (hgEq := hgEq)).g d n =
      discOffset f d m n := by
  simp [mkShiftOfEq, discrepancy, discOffset, mkShift]

/-- Contract lemma for `mkShiftOfEq`.

Not marked `[simp]` for the same reason as `mkShiftOfEq_discrepancy_contract`.
-/
theorem mkShiftOfEq_contract_discrepancy_le (f : ℕ → ℤ) (hf : IsSignSequence f)
    (d m : ℕ) (hd : d > 0) (g : ℕ → ℤ) (hgEq : g = fun k => f (k + m * d)) (B : ℕ)
    (hB : ∀ n : ℕ, discOffset f d m n ≤ B) (n : ℕ) :
    (mkShiftOfEq (f := f) (hf := hf) (d := d) (m := m) hd (g := g) (hgEq := hgEq)).contract_discrepancy_le B hB n =
      hB n := by
  -- The contract is just rewriting `discrepancy` to `discOffset`.
  simp [mkShiftOfEq, mkShift, discrepancy, discOffset]

/-- Even more convenient constructor: build the shifted reduction output directly from `hf`.

This is the typical situation in the Tao pipeline: the reduced sequence *is* a shift of the
original sign sequence.
-/
noncomputable def mkShiftOfSign (f : ℕ → ℤ) (hf : IsSignSequence f) (d m : ℕ) (hd : d > 0) :
    ReductionOutput f := by
  refine mkShift (f := f) (d := d) (m := m) (hd := hd)
    (g := fun k => f (k + m * d))
    (hg := Tao2015.IsSignSequence.shift_add_mul (f := f) hf m d)
    (hgEq := rfl)

/-!
### `mkShiftOfSign` simp API

These are tiny convenience lemmas: they make it painless to reason about the fields of the
reduction output produced by `mkShiftOfSign` without repeatedly unfolding the constructor.
-/

@[simp] theorem mkShiftOfSign_d (f : ℕ → ℤ) (hf : IsSignSequence f) (d m : ℕ) (hd : d > 0) :
    (mkShiftOfSign (f := f) (hf := hf) (d := d) (m := m) hd).d = d := by
  simp [mkShiftOfSign, mkShift]

/-!
### Composing reductions by additional shifts

A very common “micro-step” in the Tao2015 pipeline is to take an already-reduced sequence and
shift it again by a multiple of the *same* common difference `d`.

At the level of the original sequence `f`, this corresponds to adding offset multipliers.
The following constructor packages that observation as a new `ReductionOutput f`.

This is deliberately small glue, but it is a key ergonomic move: it lets later stages compose
reduction steps without rewriting arithmetic by hand.
-/

/-- Shift the reduced sequence again by a multiple of the same step size.

If `out : ReductionOutput f` corresponds to the shift `f(· + out.m*out.d)`, then
`out.shift_add_mul m₂` corresponds to `f(· + (out.m + m₂) * out.d)`.
-/
noncomputable def shift_add_mul (out : ReductionOutput f) (m₂ : ℕ) : ReductionOutput f := by
  -- Define the twice-shifted reduced sequence.
  let g' : ℕ → ℤ := fun k => out.g (k + m₂ * out.d)
  have hg' : IsSignSequence g' := by
    -- Sign sequences are stable under shifts.
    simpa [g'] using (Tao2015.IsSignSequence.shift_add_mul (f := out.g) out.hg m₂ out.d)
  have hg'Eq : g' = fun k => f (k + (out.m + m₂) * out.d) := by
    funext k
    -- Expand `out.g` as the original shift, then reassociate the arithmetic.
    -- `simp` handles the commutativity/associativity bookkeeping.
    simp [g', out.g_eq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.add_mul, Nat.mul_add,
      Nat.mul_assoc]
  -- Package using `mkShift`, which fills the contracts automatically.
  exact ReductionOutput.mkShift (f := f) (d := out.d) (m := out.m + m₂) (hd := out.hd)
    (g := g') (hg := hg') (hgEq := hg'Eq)

namespace shift_add_mul

@[simp] theorem d (out : ReductionOutput f) (m₂ : ℕ) : (out.shift_add_mul (f := f) m₂).d = out.d := by
  simp [ReductionOutput.shift_add_mul]

@[simp] theorem m (out : ReductionOutput f) (m₂ : ℕ) : (out.shift_add_mul (f := f) m₂).m = out.m + m₂ := by
  simp [ReductionOutput.shift_add_mul]

@[simp] theorem g (out : ReductionOutput f) (m₂ : ℕ) :
    (out.shift_add_mul (f := f) m₂).g = fun k => out.g (k + m₂ * out.d) := by
  simp [ReductionOutput.shift_add_mul]

@[simp] theorem g_apply (out : ReductionOutput f) (m₂ k : ℕ) :
    (out.shift_add_mul (f := f) m₂).g k = out.g (k + m₂ * out.d) := by
  simp

/-- The shifted reduction output satisfies the same `apSum`→`apSumOffset` contract, with the
updated offset multiplier `out.m + m₂`.

This is just a convenience wrapper around the generic simp lemma
`ReductionOutput.apSum_eq_apSumOffset`.
-/
theorem apSum_contract (out : ReductionOutput f) (m₂ n : ℕ) :
    apSum (out.shift_add_mul (f := f) m₂).g out.d n = apSumOffset f out.d (out.m + m₂) n := by
  -- `apSum (out'.g) out'.d = apSumOffset f out'.d out'.m`.
  simpa using (ReductionOutput.apSum_eq_apSumOffset (f := f)
    (out := out.shift_add_mul (f := f) m₂) (n := n))

/-- Discrepancy contract for the shifted reduction output.

Convenience wrapper around `ReductionOutput.discrepancy_eq_discOffset`.
-/
theorem discrepancy_contract (out : ReductionOutput f) (m₂ n : ℕ) :
    discrepancy (out.shift_add_mul (f := f) m₂).g out.d n = discOffset f out.d (out.m + m₂) n := by
  simpa using (ReductionOutput.discrepancy_eq_discOffset (f := f)
    (out := out.shift_add_mul (f := f) m₂) (n := n))

end shift_add_mul

/-!
### Offsets relative to a `ReductionOutput`

When `out : ReductionOutput f` fixes an initial shift by `out.m*out.d`, it is common to take
*further* offset sums of the reduced sequence `out.g`.

The following tiny lemmas normalize these “relative offsets” back to offset sums of the original
sequence `f`, with the combined multiplier `out.m + m₂`.
-/

namespace ReductionOutput

/-- Offset sums of the reduced sequence correspond to offset sums of the original sequence with
combined multiplier `out.m + m₂`.

This is a basic arithmetic reassociation lemma, but it saves downstream stages from repeatedly
expanding `out.g_eq` and fighting `Nat` algebra.
-/
theorem apSumOffset_eq_apSumOffset_add (out : ReductionOutput f) (m₂ n : ℕ) :
    apSumOffset out.g out.d m₂ n = apSumOffset f out.d (out.m + m₂) n := by
  -- Expand both sides to AP sums of shifted sequences.
  -- LHS shifts by `m₂*out.d` and then by `out.m*out.d` via `out.g_eq`.
  -- This is the same as a single shift by `(out.m + m₂) * out.d`.
  simp [apSumOffset_eq_apSum_shift_add, out.g_eq, Nat.add_mul, Nat.mul_add, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm]

/-- Reverse orientation of `apSumOffset_eq_apSumOffset_add`. -/
theorem apSumOffset_add_eq_apSumOffset (out : ReductionOutput f) (m₂ n : ℕ) :
    apSumOffset f out.d (out.m + m₂) n = apSumOffset out.g out.d m₂ n := by
  simpa using (out.apSumOffset_eq_apSumOffset_add (f := f) (m₂ := m₂) (n := n)).symm

/-- Discrepancy version of `apSumOffset_eq_apSumOffset_add`. -/
theorem discOffset_eq_discOffset_add (out : ReductionOutput f) (m₂ n : ℕ) :
    discOffset out.g out.d m₂ n = discOffset f out.d (out.m + m₂) n := by
  -- `discOffset` is definitional wrapper around `Int.natAbs (apSumOffset ...)`.
  simp [discOffset, out.apSumOffset_eq_apSumOffset_add (f := f) (m₂ := m₂) (n := n)]

/-- Reverse orientation of `discOffset_eq_discOffset_add`. -/
theorem discOffset_add_eq_discOffset (out : ReductionOutput f) (m₂ n : ℕ) :
    discOffset f out.d (out.m + m₂) n = discOffset out.g out.d m₂ n := by
  simpa using (out.discOffset_eq_discOffset_add (f := f) (m₂ := m₂) (n := n)).symm

end ReductionOutput

namespace ContextAlong

/-- Transport a fixed-step context across a `ReductionOutput`.

If you have a uniform bound on the *offset* discrepancies `discOffset f out.d out.m`, you can
view it as a fixed-step context for the reduced sequence `out.g` along `out.d`.
-/
theorem of_discOffset_bound (out : ReductionOutput f)
    (hB : ∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B) :
    ContextAlong out.g out.d := by
  rcases hB with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro n
  exact out.contract_discrepancy_le B hB n

/-- Converse transport: a fixed-step context for `out.g` gives a uniform `discOffset` bound. -/
theorem discOffset_bound_of (out : ReductionOutput f) (ctx : ContextAlong out.g out.d) :
    ∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B := by
  refine ⟨ctx.B, ?_⟩
  intro n
  -- Rewrite `discOffset` to the discrepancy of `out.g` using the AP-sum contract.
  simpa [discOffset, discrepancy, out.apSum_contract] using ctx.bound n

/-- Build a fixed-step context for the reduced sequence from a global boundedness context.

If `ctx : Tao2015.Context f` bounds *all* homogeneous AP discrepancies of `f` by `ctx.B`, then the
corresponding offset discrepancies are bounded by `2*ctx.B` (triangle inequality), and hence the
reduced sequence `out.g` has fixed-step discrepancy bounded by `2*ctx.B` along `out.d`.
-/
theorem ofContext (out : ReductionOutput f) (ctx : Tao2015.Context f) :
    ContextAlong out.g out.d := by
  refine ⟨ctx.B + ctx.B, ?_⟩
  intro n
  -- `discrepancy out.g = discOffset f ...`, then apply the global context bound for offset sums.
  have hOff : discOffset f out.d out.m n ≤ ctx.B + ctx.B :=
    ctx.bound_discOffset (f := f) (d := out.d) (m := out.m) (n := n) out.hd
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hOff

end ContextAlong

@[simp] theorem mkShiftOfSign_m (f : ℕ → ℤ) (hf : IsSignSequence f) (d m : ℕ) (hd : d > 0) :
    (mkShiftOfSign (f := f) (hf := hf) (d := d) (m := m) hd).m = m := by
  simp [mkShiftOfSign, mkShift]

@[simp] theorem mkShiftOfSign_g_apply (f : ℕ → ℤ) (hf : IsSignSequence f) (d m : ℕ) (hd : d > 0)
    (k : ℕ) :
    (mkShiftOfSign (f := f) (hf := hf) (d := d) (m := m) hd).g k = f (k + m * d) := by
  simp [mkShiftOfSign, mkShift]

theorem mkShiftOfSign_g_eq (f : ℕ → ℤ) (hf : IsSignSequence f) (d m : ℕ) (hd : d > 0) :
    (mkShiftOfSign (f := f) (hf := hf) (d := d) (m := m) hd).g = fun k => f (k + m * d) := by
  funext k
  simp

@[simp] theorem mkShiftOfSign_apSum_contract (f : ℕ → ℤ) (hf : IsSignSequence f)
    (d m : ℕ) (hd : d > 0) (n : ℕ) :
    apSum (mkShiftOfSign (f := f) (hf := hf) (d := d) (m := m) hd).g d n = apSumOffset f d m n := by
  -- This is definitional: `mkShift` fills the bridge rule by rewriting `apSumOffset`.
  simp [mkShiftOfSign, mkShift]

@[simp] theorem mkShiftOfSign_discrepancy_contract (f : ℕ → ℤ) (hf : IsSignSequence f)
    (d m : ℕ) (hd : d > 0) (n : ℕ) :
    discrepancy (mkShiftOfSign (f := f) (hf := hf) (d := d) (m := m) hd).g d n =
      discOffset f d m n := by
  -- Both sides are definitional wrappers around `Int.natAbs` and `mkShift` fills the AP-sum bridge.
  simp [discrepancy, discOffset, mkShiftOfSign, mkShift]

/-- `mkShiftOfSign` satisfies the discrepancy-transfer contract definitionally.

This is a tiny helper: it lets downstream code *use* the `ReductionOutput` interface without
having to unfold the record fields of `mkShift`.
-/
@[simp] theorem mkShiftOfSign_contract_discrepancy_le (f : ℕ → ℤ) (hf : IsSignSequence f)
    (d m : ℕ) (hd : d > 0) (B : ℕ)
    (hB : ∀ n : ℕ, discOffset f d m n ≤ B) (n : ℕ) :
    (mkShiftOfSign (f := f) (hf := hf) (d := d) (m := m) hd).contract_discrepancy_le B hB n =
      hB n := by
  -- The contract is just rewriting `discrepancy` to `discOffset`.
  simp [mkShiftOfSign, mkShift, discrepancy, discOffset]

/-- Function-extensional version of `mkShiftOfSign_contract_discrepancy_le`. -/
@[simp] theorem mkShiftOfSign_contract_discrepancy_le_funext (f : ℕ → ℤ) (hf : IsSignSequence f)
    (d m : ℕ) (hd : d > 0) (B : ℕ)
    (hB : ∀ n : ℕ, discOffset f d m n ≤ B) :
    (mkShiftOfSign (f := f) (hf := hf) (d := d) (m := m) hd).contract_discrepancy_le B hB = hB := by
  funext n
  simpa using
    (mkShiftOfSign_contract_discrepancy_le (f := f) (hf := hf) (d := d) (m := m) (hd := hd)
      (B := B) (hB := hB) (n := n))

/-- `apSumFrom` rewrite for the reduction output produced by `mkShiftOfSign`.

This is a tiny convenience lemma: it avoids having to explicitly invoke
`ReductionOutput.apSumFrom_eq_apSum` each time.
-/
@[simp] theorem mkShiftOfSign_apSumFrom (f : ℕ → ℤ) (hf : IsSignSequence f) (d m : ℕ) (hd : d > 0)
    (n : ℕ) :
    apSumFrom f (m * d) d n = apSum (mkShiftOfSign (f := f) (hf := hf) (d := d) (m := m) hd).g d n := by
  -- Reduce to the general lemma for `ReductionOutput`.
  simpa using
    (ReductionOutput.apSumFrom_eq_apSum (f := f)
      (out := mkShiftOfSign (f := f) (hf := hf) (d := d) (m := m) hd) (n := n))

/-- `apSumFrom` rewrite for `mkShiftOfSign`, oriented directly as an offset sum. -/
@[simp] theorem mkShiftOfSign_apSumFrom_eq_apSumOffset (f : ℕ → ℤ) (hf : IsSignSequence f)
    (d m : ℕ) (hd : d > 0) (n : ℕ) :
    apSumFrom f (m * d) d n = apSumOffset f d m n := by
  -- This is the bundled `ReductionOutput.apSumFrom_eq_apSumOffset` lemma.
  simpa using
    (ReductionOutput.apSumFrom_eq_apSumOffset (f := f)
      (out := mkShiftOfSign (f := f) (hf := hf) (d := d) (m := m) hd) (n := n))

/-- Reverse orientation of `mkShiftOfSign_discrepancy_contract`.

Not marked `[simp]`: the forward lemma is already `[simp]`, and having both directions in the simp
set can cause nontermination / oscillation.
-/
theorem mkShiftOfSign_discOffset_eq_discrepancy (f : ℕ → ℤ) (hf : IsSignSequence f)
    (d m : ℕ) (hd : d > 0) (n : ℕ) :
    discOffset f d m n = discrepancy (mkShiftOfSign (f := f) (hf := hf) (d := d) (m := m) hd).g d n := by
  simpa using
    (mkShiftOfSign_discrepancy_contract (f := f) (hf := hf) (d := d) (m := m) hd n).symm

/-!
### Composing shift-style reduction outputs (same step size)

A common pattern in the Tao-style pipeline is to define a sequence by *multiple* successive
shifts-by-multiples-of-`d`.  This section packages the simple “offsets add” fact as a compositional
constructor on `ReductionOutput`.

We intentionally only support the case where both reduction stages share the same step size `d`.
That is already enough to let downstream stages build multi-step reductions while keeping the
interface lightweight.
-/

namespace ReductionOutput

/-- Compose two reduction outputs that share the same step size `d`.

If:
- `out₁ : ReductionOutput f` packages `g₁(k) = f(k + m₁*d)` and the bridge
  `apSum g₁ d = apSumOffset f d m₁`, and
- `out₂ : ReductionOutput out₁.g` packages `g₂(k) = out₁.g(k + m₂*d)` and the bridge
  `apSum g₂ d = apSumOffset out₁.g d m₂`,

then the composite packages `g₂(k) = f(k + (m₁+m₂)*d)` with bridge
`apSum g₂ d = apSumOffset f d (m₁+m₂)`.

The proof is just rewriting plus `apSumOffset_add` / `discOffset_add`.
-/
noncomputable def composeShiftSameD {f : ℕ → ℤ} (out₁ : Tao2015.ReductionOutput f)
    (out₂ : Tao2015.ReductionOutput out₁.g) (hdd : out₂.d = out₁.d) :
    Tao2015.ReductionOutput f := by
  classical
  -- We keep `d` and `hd` from `out₁`, since the step sizes agree.
  refine
    { d := out₁.d
      m := out₁.m + out₂.m
      hd := out₁.hd
      g := out₂.g
      hg := out₂.hg
      g_eq := ?_
      apSum_contract := ?_
      contract_discrepancy_le := ?_ }
  · -- Expand `out₂.g` as a shift of `out₁.g`, then expand `out₁.g` as a shift of `f`.
    -- Finally, reassociate the resulting offset.
    --
    -- `out₂.g k = out₁.g (k + out₂.m * out₂.d)`
    --        `= f ((k + out₂.m*out₂.d) + out₁.m*out₁.d)`.
    -- With `out₂.d = out₁.d`, this is `f (k + (out₁.m+out₂.m) * out₁.d)`.
    funext k
    have hk : out₂.g k = out₁.g (k + out₂.m * out₂.d) := by
      simpa [out₂.g_eq]
    -- Rewrite `out₁.g` using `out₁.g_eq`.
    -- Then normalize arithmetic.
    simpa [hk, out₁.g_eq, hdd, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.add_mul,
      Nat.mul_add, Nat.mul_assoc] 
  · intro n
    -- Start from the stage-2 bridge `apSum out₂.g out₂.d = apSumOffset out₁.g out₂.d out₂.m`.
    -- Then rewrite `out₂.d` to `out₁.d` and re-associate offsets.
    have h₂ : apSum out₂.g out₂.d n = apSumOffset out₁.g out₂.d out₂.m n := out₂.apSum_contract n
    -- Re-associate the offsets on the RHS:
    -- `apSumOffset f d (m₁+m₂) = apSumOffset (shift f by m₁*d) d m₂`.
    -- And `shift f by m₁*d` is exactly `out₁.g`.
    --
    -- We use the reverse orientation `apSumOffset_shift_add`.
    simpa [hdd] using
      (show apSum out₂.g out₁.d n = apSumOffset f out₁.d (out₁.m + out₂.m) n by
        -- Rewrite using `h₂`.
        have : apSum out₂.g out₁.d n = apSumOffset out₁.g out₁.d out₂.m n := by
          simpa [hdd] using h₂
        -- Convert `apSumOffset out₁.g ...` to `apSumOffset f ... (m₁+m₂)`.
        -- `out₁.g` is definitionally the shift of `f` by `out₁.m*out₁.d`.
        -- `apSumOffset_add` handles the offset reassociation.
        simpa [out₁.g_eq] using
          (congrArg (fun t => t) (apSumOffset_shift_add (f := f) (d := out₁.d)
            (m₁ := out₁.m) (m₂ := out₂.m) (n := n)))
        |> fun h => by
          -- `h` is an equality of offset sums; use it to rewrite the target.
          -- (This little dance avoids needing `simp` to guess the direction.)
          simpa [h] using this)
  · intro B hB n
    -- Convert the bound hypothesis on `discOffset f out₁.d (out₁.m+out₂.m)` into a bound on
    -- `discOffset out₁.g out₁.d out₂.m` using `discOffset_add` plus `out₁.g_eq`.
    have hB₂ : ∀ n : ℕ, discOffset out₁.g out₁.d out₂.m n ≤ B := by
      intro n
      -- `discOffset_add` says
      --   `discOffset f d (m₁+m₂) = discOffset (shift f by m₁*d) d m₂`.
      -- Here `shift f by m₁*d` is `out₁.g`.
      -- So we can rewrite `hB n` into the desired bound.
      have := hB n
      -- Rewrite the LHS of `this` using `discOffset_add` (symm) and `out₁.g_eq`.
      simpa [out₁.g_eq] using (by
        -- Change the goal by rewriting `discOffset out₁.g ...`.
        -- `discOffset_add` goes the other way, so use `.symm`.
        simpa using (show discOffset out₁.g out₁.d out₂.m n ≤ B from
          (by
            -- Replace `discOffset out₁.g ...` with the corresponding `discOffset f ... (m₁+m₂)`.
            --
            -- `discOffset f d (m₁+m₂) = discOffset (shift f by m₁*d) d m₂`.
            -- So
            -- `discOffset (shift f by m₁*d) d m₂ = discOffset f d (m₁+m₂)`.
            --
            -- Now use `this`.
            simpa [discOffset_add (f := f) (d := out₁.d) (m₁ := out₁.m) (m₂ := out₂.m) (n := n)]
              using this)))
    -- Now apply the stage-2 transfer contract.
    have h := out₂.contract_discrepancy_le B (by
      intro n
      -- `out₂` expects `discOffset out₁.g out₂.d out₂.m`; rewrite `out₂.d` to `out₁.d`.
      simpa [hdd] using hB₂ n)
    -- Again rewrite `out₂.d` to `out₁.d` on the conclusion.
    simpa [hdd] using h n

/-- `composeShiftSameD` preserves the step size `d` (it is taken from `out₁`). -/
@[simp] theorem composeShiftSameD_d {f : ℕ → ℤ} (out₁ : Tao2015.ReductionOutput f)
    (out₂ : Tao2015.ReductionOutput out₁.g) (hdd : out₂.d = out₁.d) :
    (composeShiftSameD (out₁ := out₁) (out₂ := out₂) hdd).d = out₁.d := by
  simp [composeShiftSameD]

/-- `composeShiftSameD` adds the offsets. -/
@[simp] theorem composeShiftSameD_m {f : ℕ → ℤ} (out₁ : Tao2015.ReductionOutput f)
    (out₂ : Tao2015.ReductionOutput out₁.g) (hdd : out₂.d = out₁.d) :
    (composeShiftSameD (out₁ := out₁) (out₂ := out₂) hdd).m = out₁.m + out₂.m := by
  simp [composeShiftSameD]

/-- `composeShiftSameD` keeps the reduced sequence from stage 2. -/
@[simp] theorem composeShiftSameD_g {f : ℕ → ℤ} (out₁ : Tao2015.ReductionOutput f)
    (out₂ : Tao2015.ReductionOutput out₁.g) (hdd : out₂.d = out₁.d) :
    (composeShiftSameD (out₁ := out₁) (out₂ := out₂) hdd).g = out₂.g := by
  simp [composeShiftSameD]

/-- Pointwise formula for the reduced sequence produced by `composeShiftSameD`.

This is the generic (non-`mkShiftOfSign`-specialized) version of the computation lemma
`composeShiftSameD_mkShiftOfSign_g_apply`.
-/
theorem composeShiftSameD_g_apply {f : ℕ → ℤ} (out₁ : Tao2015.ReductionOutput f)
    (out₂ : Tao2015.ReductionOutput out₁.g) (hdd : out₂.d = out₁.d) (k : ℕ) :
    (composeShiftSameD (out₁ := out₁) (out₂ := out₂) hdd).g k = f (k + (out₁.m + out₂.m) * out₁.d) := by
  -- `composeShiftSameD` keeps `g` from stage 2; unfold `out₂.g` then `out₁.g`.
  -- Finally normalize the arithmetic using `hdd : out₂.d = out₁.d`.
  --
  -- `out₂.g k = out₁.g (k + out₂.m*out₂.d)` and `out₁.g t = f (t + out₁.m*out₁.d)`.
  simp [composeShiftSameD, out₂.g_eq, out₁.g_eq, hdd,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.add_mul, Nat.mul_add, Nat.mul_assoc]

/-- `composeShiftSameD` keeps the sign-sequence proof from stage 2. -/
@[simp] theorem composeShiftSameD_hg {f : ℕ → ℤ} (out₁ : Tao2015.ReductionOutput f)
    (out₂ : Tao2015.ReductionOutput out₁.g) (hdd : out₂.d = out₁.d) :
    (composeShiftSameD (out₁ := out₁) (out₂ := out₂) hdd).hg = out₂.hg := by
  classical
  -- Proof irrelevance: both sides are proofs of the same proposition.
  simp [composeShiftSameD]

/-- `composeShiftSameD` keeps the positivity proof `hd` from stage 1. -/
@[simp] theorem composeShiftSameD_hd {f : ℕ → ℤ} (out₁ : Tao2015.ReductionOutput f)
    (out₂ : Tao2015.ReductionOutput out₁.g) (hdd : out₂.d = out₁.d) :
    (composeShiftSameD (out₁ := out₁) (out₂ := out₂) hdd).hd = out₁.hd := by
  simp [composeShiftSameD]

/-- The AP-sum bridge rule for `composeShiftSameD` (pointwise form).

We do **not** mark this lemma `[simp]`: it expands a “semantic” statement about `apSum` into an
offset normal form, and tends to be too aggressive in large proofs.
-/
theorem composeShiftSameD_apSum_contract {f : ℕ → ℤ} (out₁ : Tao2015.ReductionOutput f)
    (out₂ : Tao2015.ReductionOutput out₁.g) (hdd : out₂.d = out₁.d) (n : ℕ) :
    apSum (composeShiftSameD (out₁ := out₁) (out₂ := out₂) hdd).g out₁.d n =
      apSumOffset f out₁.d (out₁.m + out₂.m) n := by
  -- This is exactly the `apSum_contract` field of the composite, with `d = out₁.d`.
  simp [composeShiftSameD]

/-- The discrepancy rewrite rule for `composeShiftSameD` (pointwise form). -/
theorem composeShiftSameD_discrepancy_contract {f : ℕ → ℤ} (out₁ : Tao2015.ReductionOutput f)
    (out₂ : Tao2015.ReductionOutput out₁.g) (hdd : out₂.d = out₁.d) (n : ℕ) :
    discrepancy (composeShiftSameD (out₁ := out₁) (out₂ := out₂) hdd).g out₁.d n =
      discOffset f out₁.d (out₁.m + out₂.m) n := by
  -- Both sides are definitional wrappers around `Int.natAbs`.
  simp [discrepancy, discOffset, composeShiftSameD]

/-- Transfer contract for `composeShiftSameD`: a bound on the *composed* offset discrepancy
transfers to a bound on the reduced discrepancy of the composed output. -/
theorem composeShiftSameD_contract_discrepancy_le {f : ℕ → ℤ} (out₁ : Tao2015.ReductionOutput f)
    (out₂ : Tao2015.ReductionOutput out₁.g) (hdd : out₂.d = out₁.d) (B : ℕ)
    (hB : ∀ n : ℕ, discOffset f out₁.d (out₁.m + out₂.m) n ≤ B) :
    ∀ n : ℕ, discrepancy (composeShiftSameD (out₁ := out₁) (out₂ := out₂) hdd).g out₁.d n ≤ B := by
  intro n
  -- Unfold the composite and use its transfer contract field.
  -- (`simp` handles the bookkeeping for `d`, `m`.)
  simpa [composeShiftSameD] using
    (composeShiftSameD (out₁ := out₁) (out₂ := out₂) hdd).contract_discrepancy_le B hB n

/-- Discrepancy-witness normal form for the composite reduction.

This is a small “pipeline ergonomics” lemma: many later stages prove a fixed-step discrepancy
statement about the reduced sequence. When those reductions are composed, it is useful to get
directly back to a `discOffset` witness about the *original* sequence `f`.
-/
theorem composeShiftSameD_hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt {f : ℕ → ℤ}
    (out₁ : Tao2015.ReductionOutput f) (out₂ : Tao2015.ReductionOutput out₁.g)
    (hdd : out₂.d = out₁.d) (C : ℕ) :
    HasDiscrepancyAtLeastAlong (composeShiftSameD (out₁ := out₁) (out₂ := out₂) hdd).g out₁.d C ↔
      (∃ n : ℕ, discOffset f out₁.d (out₁.m + out₂.m) n > C) := by
  -- This is just `ReductionOutput.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt`
  -- specialized to the composite reduction output.
  simpa using
    (ReductionOutput.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f)
      (out := composeShiftSameD (out₁ := out₁) (out₂ := out₂) hdd) (C := C))

/-- `<`-oriented variant of `composeShiftSameD_hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt`. -/
theorem composeShiftSameD_hasDiscrepancyAtLeastAlong_iff_exists_discOffset_lt {f : ℕ → ℤ}
    (out₁ : Tao2015.ReductionOutput f) (out₂ : Tao2015.ReductionOutput out₁.g)
    (hdd : out₂.d = out₁.d) (C : ℕ) :
    HasDiscrepancyAtLeastAlong (composeShiftSameD (out₁ := out₁) (out₂ := out₂) hdd).g out₁.d C ↔
      (∃ n : ℕ, C < discOffset f out₁.d (out₁.m + out₂.m) n) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using
    (composeShiftSameD_hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt
      (out₁ := out₁) (out₂ := out₂) (hdd := hdd) (C := C))

/-- Sum-level witness normal form for the composite reduction.

This is the `Int.natAbs (apSumOffset ...)` version of
`composeShiftSameD_hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt`.
-/
theorem composeShiftSameD_hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt {f : ℕ → ℤ}
    (out₁ : Tao2015.ReductionOutput f) (out₂ : Tao2015.ReductionOutput out₁.g)
    (hdd : out₂.d = out₁.d) (C : ℕ) :
    HasDiscrepancyAtLeastAlong (composeShiftSameD (out₁ := out₁) (out₂ := out₂) hdd).g out₁.d C ↔
      (∃ n : ℕ, Int.natAbs (apSumOffset f out₁.d (out₁.m + out₂.m) n) > C) := by
  simpa using
    (ReductionOutput.hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt (f := f)
      (out := composeShiftSameD (out₁ := out₁) (out₂ := out₂) hdd) (C := C))

/-- `<`-oriented sum-level witness normal form for the composite reduction. -/
theorem composeShiftSameD_hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_lt {f : ℕ → ℤ}
    (out₁ : Tao2015.ReductionOutput f) (out₂ : Tao2015.ReductionOutput out₁.g)
    (hdd : out₂.d = out₁.d) (C : ℕ) :
    HasDiscrepancyAtLeastAlong (composeShiftSameD (out₁ := out₁) (out₂ := out₂) hdd).g out₁.d C ↔
      (∃ n : ℕ, C < Int.natAbs (apSumOffset f out₁.d (out₁.m + out₂.m) n)) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using
    (composeShiftSameD_hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt
      (out₁ := out₁) (out₂ := out₂) (hdd := hdd) (C := C))

/-- Compute the reduced sequence produced by composing two `mkShiftOfSign` reductions.

This is a common “pipeline ergonomics” lemma: it lets later stages treat successive shifts as a
single shift by the sum of the offsets.
-/
theorem composeShiftSameD_mkShiftOfSign_g_apply (f : ℕ → ℤ) (hf : IsSignSequence f)
    (d m₁ m₂ : ℕ) (hd : d > 0) (k : ℕ) :
    (ReductionOutput.composeShiftSameD
        (out₁ := ReductionOutput.mkShiftOfSign (f := f) (hf := hf) (d := d) (m := m₁) hd)
        (out₂ :=
          ReductionOutput.mkShiftOfSign
            (f := fun k => f (k + m₁ * d))
            (hf := Tao2015.IsSignSequence.shift_add_mul (f := f) hf m₁ d)
            (d := d) (m := m₂) hd)
        rfl).g k = f (k + (m₁ + m₂) * d) := by
  -- `composeShiftSameD` keeps `g` from stage 2; stage 2 is itself a shift of stage 1.
  -- Normalize arithmetic to combine the offsets.
  simp [ReductionOutput.composeShiftSameD, ReductionOutput.mkShiftOfSign, ReductionOutput.mkShift,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.add_mul, Nat.mul_add, Nat.mul_assoc]

/-- Specialized AP-sum bridge for composing two `mkShiftOfSign` reductions. -/
theorem composeShiftSameD_mkShiftOfSign_apSum_contract (f : ℕ → ℤ) (hf : IsSignSequence f)
    (d m₁ m₂ : ℕ) (hd : d > 0) (n : ℕ) :
    apSum
        (ReductionOutput.composeShiftSameD
            (out₁ := ReductionOutput.mkShiftOfSign (f := f) (hf := hf) (d := d) (m := m₁) hd)
            (out₂ :=
              ReductionOutput.mkShiftOfSign
                (f := fun k => f (k + m₁ * d))
                (hf := Tao2015.IsSignSequence.shift_add_mul (f := f) hf m₁ d)
                (d := d) (m := m₂) hd)
            rfl).g d n
      = apSumOffset f d (m₁ + m₂) n := by
  -- This is just the general AP-sum bridge lemma for `composeShiftSameD`.
  simpa using
    (ReductionOutput.composeShiftSameD_apSum_contract
      (f := f)
      (out₁ := ReductionOutput.mkShiftOfSign (f := f) (hf := hf) (d := d) (m := m₁) hd)
      (out₂ :=
        ReductionOutput.mkShiftOfSign
          (f := fun k => f (k + m₁ * d))
          (hf := Tao2015.IsSignSequence.shift_add_mul (f := f) hf m₁ d)
          (d := d) (m := m₂) hd)
      (hdd := rfl) (n := n))

/-- Specialized discrepancy bridge for composing two `mkShiftOfSign` reductions. -/
theorem composeShiftSameD_mkShiftOfSign_discrepancy_contract (f : ℕ → ℤ) (hf : IsSignSequence f)
    (d m₁ m₂ : ℕ) (hd : d > 0) (n : ℕ) :
    discrepancy
        (ReductionOutput.composeShiftSameD
            (out₁ := ReductionOutput.mkShiftOfSign (f := f) (hf := hf) (d := d) (m := m₁) hd)
            (out₂ :=
              ReductionOutput.mkShiftOfSign
                (f := fun k => f (k + m₁ * d))
                (hf := Tao2015.IsSignSequence.shift_add_mul (f := f) hf m₁ d)
                (d := d) (m := m₂) hd)
            rfl).g d n
      = discOffset f d (m₁ + m₂) n := by
  -- This is just the general discrepancy bridge lemma for `composeShiftSameD`.
  simpa using
    (ReductionOutput.composeShiftSameD_discrepancy_contract
      (f := f)
      (out₁ := ReductionOutput.mkShiftOfSign (f := f) (hf := hf) (d := d) (m := m₁) hd)
      (out₂ :=
        ReductionOutput.mkShiftOfSign
          (f := fun k => f (k + m₁ * d))
          (hf := Tao2015.IsSignSequence.shift_add_mul (f := f) hf m₁ d)
          (d := d) (m := m₂) hd)
      (hdd := rfl) (n := n))

/-- Boundedness normal form for the composite reduction.

This is the boundedness analogue of
`composeShiftSameD_hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt`: it lets later stages
move a `BoundedDiscrepancyAlong` statement about the *composed* reduced sequence back to a uniform
bound on the original offset discrepancies.
-/
theorem composeShiftSameD_boundedDiscrepancyAlong_iff_exists_discOffset_le {f : ℕ → ℤ}
    (out₁ : Tao2015.ReductionOutput f) (out₂ : Tao2015.ReductionOutput out₁.g)
    (hdd : out₂.d = out₁.d) :
    BoundedDiscrepancyAlong (composeShiftSameD (out₁ := out₁) (out₂ := out₂) hdd).g out₁.d ↔
      (∃ B : ℕ, ∀ n : ℕ, discOffset f out₁.d (out₁.m + out₂.m) n ≤ B) := by
  -- This is just the general boundedness normal form for `ReductionOutput`, specialized to the
  -- composite reduction output.
  simpa using
    (ReductionOutput.boundedDiscrepancyAlong_iff_exists_discOffset_le (f := f)
      (out := composeShiftSameD (out₁ := out₁) (out₂ := out₂) hdd))

/-!
### A “zero shift” reduction output (right identity for `composeShiftSameD`)

When composing multiple shift-style reductions, it is convenient to have an explicit
"do nothing" stage at the *same* step size `d`.

This is distinct from `Tao2015.id`, which hard-codes `d = 1`.
-/

/-- Trivial reduction output on `out.g`: same `d`, zero offset `m = 0`, and `g` unchanged.

This is the right-identity element for `composeShiftSameD` (up to proof irrelevance).
-/
noncomputable def shift0 {f : ℕ → ℤ} (out : Tao2015.ReductionOutput f) : Tao2015.ReductionOutput out.g := by
  classical
  refine
    { d := out.d
      m := 0
      hd := out.hd
      g := out.g
      hg := out.hg
      g_eq := rfl
      apSum_contract := ?_
      contract_discrepancy_le := ?_ }
  · intro n
    -- `apSumOffset _ _ 0 _ = apSum _ _ _`.
    simpa [Tao2015.apSumOffset_zero]
  · intro B hB n
    -- Rewrite `discOffset _ _ 0 _` to `discrepancy`.
    -- (Both are definitional wrappers around `Int.natAbs`.)
    simpa [discOffset, discrepancy, Tao2015.apSumOffset_zero] using hB n

@[simp] theorem shift0_d {f : ℕ → ℤ} (out : Tao2015.ReductionOutput f) : (shift0 out).d = out.d := rfl

@[simp] theorem shift0_m {f : ℕ → ℤ} (out : Tao2015.ReductionOutput f) : (shift0 out).m = 0 := rfl

@[simp] theorem shift0_g {f : ℕ → ℤ} (out : Tao2015.ReductionOutput f) : (shift0 out).g = out.g := rfl

/-- Composing with `shift0` on the right preserves the offset parameter `m`. -/
theorem composeShiftSameD_shift0_m {f : ℕ → ℤ} (out : Tao2015.ReductionOutput f) :
    (composeShiftSameD (out₁ := out) (out₂ := shift0 out) rfl).m = out.m := by
  simp [composeShiftSameD]

/-- Composing with `shift0` on the right preserves the reduced sequence `g` (definitionally). -/
@[simp] theorem composeShiftSameD_shift0_g {f : ℕ → ℤ} (out : Tao2015.ReductionOutput f) :
    (composeShiftSameD (out₁ := out) (out₂ := shift0 out) rfl).g = out.g := by
  simp [composeShiftSameD]

/-!
### Boundedness transfer helpers

Stage-1 and Stage-2 reductions often begin with a global boundedness hypothesis on the original
sequence `f` (packaged as `Tao2015.Context f`).

Before doing any deeper Tao-style work, it is useful to immediately obtain a *fixed-step* bound
for the reduced sequence `out.g` along the bundled step size `out.d`.

This is intentionally tiny pipeline glue living in `Conjectures/`.
-/

/-- From a global boundedness context for `f`, build a fixed-step boundedness context for the
reduced sequence `out.g` along the reduced step size `out.d`.

The constant is the expected `2*B`: shifting turns the reduced partial sums into offset sums, and
an offset sum is a difference of two prefix sums.
-/
def contextAlong_ofContext {f : ℕ → ℤ} (ctx : Tao2015.Context f) (out : Tao2015.ReductionOutput f) :
    Tao2015.ContextAlong out.g out.d := by
  refine ⟨ctx.B + ctx.B, ?_⟩
  intro n
  -- Reduce to the literal-shift form provided by `out.g_eq`, then apply the shift-bound lemma.
  simpa [out.g_eq] using
    (Tao2015.Context.bound_discrepancy_shift_add (f := f) (ctx := ctx)
      (d := out.d) (m := out.m) (n := n) out.hd)

end ReductionOutput

/-- Identity reduction: take `d = 1` and `m = 0`, so the reduced sequence is literally `f`.

This is occasionally useful as a “do-nothing” reduction step when you want to express later stages
in terms of `ReductionOutput` without committing to a nontrivial stage-1 reduction yet.
-/
noncomputable def id (f : ℕ → ℤ) (hf : IsSignSequence f) : ReductionOutput f :=
  mkShiftOfSign (f := f) (hf := hf) (d := 1) (m := 0) (by decide)

@[simp] theorem id_d (f : ℕ → ℤ) (hf : IsSignSequence f) : (id (f := f) hf).d = 1 := rfl

@[simp] theorem id_m (f : ℕ → ℤ) (hf : IsSignSequence f) : (id (f := f) hf).m = 0 := rfl

@[simp] theorem id_g_apply (f : ℕ → ℤ) (hf : IsSignSequence f) (k : ℕ) :
    (id (f := f) hf).g k = f k := by
  simp [id]

/-!
### A named entry point for the Tao2015 pipeline (Stage 1)

The first “reduction” in the conjectures-only pipeline is currently an identity placeholder.

Why bother naming it?
- downstream stages can be written against a stable symbol (`stage1`), even while we later swap
  in the *real* first reduction step;
- it gives a single place to attach documentation and future refinement lemmas.
-/

/-- Stage 1 reduction (placeholder): currently the identity reduction `d = 1`, `m = 0`.

Later we will replace this with the first genuine Tao-style reduction, but keeping the *name*
stable lets the rest of the pipeline compile unchanged.
-/
noncomputable def stage1 (f : ℕ → ℤ) (hf : IsSignSequence f) : ReductionOutput f :=
  id (f := f) hf

@[simp] theorem stage1_d (f : ℕ → ℤ) (hf : IsSignSequence f) : (stage1 (f := f) hf).d = 1 := by
  simp [stage1]

@[simp] theorem stage1_m (f : ℕ → ℤ) (hf : IsSignSequence f) : (stage1 (f := f) hf).m = 0 := by
  simp [stage1]

@[simp] theorem stage1_hd (f : ℕ → ℤ) (hf : IsSignSequence f) : (stage1 (f := f) hf).hd = (by decide : (1 : ℕ) > 0) := by
  -- `stage1` is the identity reduction with `d = 1`.
  simp [stage1, id]

@[simp] theorem stage1_g_apply (f : ℕ → ℤ) (hf : IsSignSequence f) (k : ℕ) :
    (stage1 (f := f) hf).g k = f k := by
  simp [stage1]

/-- `stage1` satisfies the `apSum` bridge rule definitionally. -/
@[simp] theorem stage1_apSum_contract (f : ℕ → ℤ) (hf : IsSignSequence f) (n : ℕ) :
    apSum (stage1 (f := f) hf).g 1 n = apSumOffset f 1 0 n := by
  simp [stage1, id]

/-- Under the identity reduction, the reduced AP sum is just the original one. -/
@[simp] theorem stage1_apSum_eq (f : ℕ → ℤ) (hf : IsSignSequence f) (n : ℕ) :
    apSum (stage1 (f := f) hf).g 1 n = apSum f 1 n := by
  -- `apSumOffset f 1 0 n = apSum f 1 n` by the zero-offset simp lemma.
  simpa using (stage1_apSum_contract (f := f) (hf := hf) n)

/-- `stage1` satisfies the discrepancy bridge rule definitionally. -/
@[simp] theorem stage1_discrepancy_contract (f : ℕ → ℤ) (hf : IsSignSequence f) (n : ℕ) :
    discrepancy (stage1 (f := f) hf).g 1 n = discOffset f 1 0 n := by
  simp [stage1, id]

/-- Under the identity reduction, the reduced discrepancy is just the original one. -/
@[simp] theorem stage1_discrepancy_eq (f : ℕ → ℤ) (hf : IsSignSequence f) (n : ℕ) :
    discrepancy (stage1 (f := f) hf).g 1 n = discrepancy f 1 n := by
  -- Reduce to the offset form and then use the zero-offset simp lemma.
  simpa using (stage1_discrepancy_contract (f := f) (hf := hf) n)

/-- Convenience: the offset discrepancy wrapper `discOffset f 1 0` is just `discrepancy f 1`. -/
@[simp] theorem discOffset_one_zero_eq_discrepancy (f : ℕ → ℤ) (n : ℕ) :
    discOffset f 1 0 n = discrepancy f 1 n := by
  simp [discOffset, discrepancy]

/-- `stage1` rewrites the tail-sum API `apSumFrom` into an offset sum. -/
@[simp] theorem stage1_apSumFrom_eq_apSumOffset (f : ℕ → ℤ) (hf : IsSignSequence f) (n : ℕ) :
    apSumFrom f 0 1 n = apSumOffset f 1 0 n := by
  simp [stage1, id]

/-- `stage1` rewrites the tail-sum API `apSumFrom` into the reduced AP sum (which is just `apSum f`). -/
@[simp] theorem stage1_apSumFrom_eq_apSum (f : ℕ → ℤ) (hf : IsSignSequence f) (n : ℕ) :
    apSumFrom f 0 1 n = apSum (stage1 (f := f) hf).g 1 n := by
  simp [stage1, id]

/-- Rewrite `apSum out.g out.d` as an offset sum of `f`.

This is the main “bridge” lemma: it lets us convert bounds on `apSumOffset f` into bounds
on the auxiliary AP sums for `g`.

Marked `[simp]` because it is the *canonical* normal form for `apSum` expressions involving
the reduced sequence `out.g`.
-/
@[simp] theorem apSum_eq_apSumOffset (out : ReductionOutput f) (n : ℕ) :
    apSum out.g out.d n = apSumOffset f out.d out.m n :=
  out.apSum_contract n

/-- Reverse orientation of `apSum_eq_apSumOffset` (not marked simp to avoid rewrite loops). -/
theorem apSumOffset_eq_apSum (out : ReductionOutput f) (n : ℕ) :
    apSumOffset f out.d out.m n = apSum out.g out.d n := by
  simpa using (out.apSum_eq_apSumOffset (f := f) (n := n)).symm

/-- Discrepancy rewrite rule induced by `apSum_eq_apSumOffset`.

Marked `[simp]` because it is the canonical normal form for discrepancies of the reduced
sequence `out.g`.
-/
@[simp] theorem discrepancy_eq_discOffset (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n = discOffset f out.d out.m n := by
  -- Both sides are definitional wrappers around `Int.natAbs`.
  simp [discrepancy, discOffset, out.apSum_eq_apSumOffset]

/-- Reverse orientation of `discrepancy_eq_discOffset` (not marked simp to avoid rewrite loops). -/
theorem discOffset_eq_discrepancy (out : ReductionOutput f) (n : ℕ) :
    discOffset f out.d out.m n = discrepancy out.g out.d n := by
  simpa using (out.discrepancy_eq_discOffset (f := f) (n := n)).symm

/-!
### Bound-transfer helper lemmas

These are tiny wrappers that make the `ReductionOutput` interface more ergonomic.
They are deliberately redundant: downstream stages often have a bound in one normal form and want
it in the other without re-running the rewrite steps manually.
-/

/-- Transfer a uniform bound on `discOffset` to a uniform bound on the reduced discrepancy.

This is just the `contract_discrepancy_le` field, exposed under a more discoverable name.
-/
theorem bound_discrepancy_of_bound_discOffset (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, discOffset f out.d out.m n ≤ B) :
    ∀ n : ℕ, discrepancy out.g out.d n ≤ B :=
  out.contract_discrepancy_le B hB

/-- Reverse transfer: a uniform bound on the reduced discrepancy is a uniform bound on `discOffset`.

This does not use the contract field; it is purely the `discOffset ↔ discrepancy` rewrite rule.
-/
theorem bound_discOffset_of_bound_discrepancy (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, discrepancy out.g out.d n ≤ B) :
    ∀ n : ℕ, discOffset f out.d out.m n ≤ B := by
  intro n
  simpa [out.discOffset_eq_discrepancy (f := f) (n := n)] using hB n

/-- Pointwise form of `bound_discrepancy_of_bound_discOffset`. -/
theorem bound_discrepancy_of_bound_discOffset_apply (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, discOffset f out.d out.m n ≤ B) (n : ℕ) :
    discrepancy out.g out.d n ≤ B :=
  (out.bound_discrepancy_of_bound_discOffset (f := f) B hB) n

/-- Pointwise form of `bound_discOffset_of_bound_discrepancy`. -/
theorem bound_discOffset_of_bound_discrepancy_apply (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, discrepancy out.g out.d n ≤ B) (n : ℕ) :
    discOffset f out.d out.m n ≤ B :=
  (out.bound_discOffset_of_bound_discrepancy (f := f) B hB) n

/-- Reverse transfer, in the raw `Int.natAbs (apSumOffset ...)` form.

This is just `bound_discOffset_of_bound_discrepancy` with `discOffset` unfolded.
-/
theorem bound_natAbs_apSumOffset_of_bound_discrepancy (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, discrepancy out.g out.d n ≤ B) :
    ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ B := by
  intro n
  -- `discOffset` is definitionally `Int.natAbs (apSumOffset ...)`.
  simpa [discOffset] using (out.bound_discOffset_of_bound_discrepancy (f := f) B hB n)

/-- Forward transfer, in the raw `Int.natAbs (apSumOffset ...)` form.

This is `bound_discrepancy_of_bound_discOffset` specialized to a bound written directly on
`Int.natAbs (apSumOffset ...)`.
-/
theorem bound_discrepancy_of_bound_natAbs_apSumOffset (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ B) :
    ∀ n : ℕ, discrepancy out.g out.d n ≤ B := by
  -- Rewrite the hypothesis as a bound on `discOffset`, then use the contract field.
  apply out.bound_discrepancy_of_bound_discOffset (f := f) (B := B)
  intro n
  simpa [discOffset] using hB n

/-- Strict-inequality transfer: a uniform *strict* bound on the offset discrepancy transfers to a
strict bound on the reduced discrepancy.

This is the `<` analogue of `bound_discrepancy_of_bound_discOffset`.
-/
theorem bound_discrepancy_lt_of_bound_discOffset (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, discOffset f out.d out.m n < B) :
    ∀ n : ℕ, discrepancy out.g out.d n < B := by
  intro n
  simpa [out.discrepancy_contract (f := f) (n := n)] using hB n

/-- Strict-inequality reverse transfer: a uniform strict bound on the reduced discrepancy transfers
back to a strict bound on `discOffset`.

This is the `<` analogue of `bound_discOffset_of_bound_discrepancy`.
-/
theorem bound_discOffset_lt_of_bound_discrepancy (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, discrepancy out.g out.d n < B) :
    ∀ n : ℕ, discOffset f out.d out.m n < B := by
  intro n
  simpa [out.discOffset_eq_discrepancy (f := f) (n := n)] using hB n

/-- Pointwise form of `bound_discrepancy_lt_of_bound_discOffset`. -/
theorem bound_discrepancy_lt_of_bound_discOffset_apply (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, discOffset f out.d out.m n < B) (n : ℕ) :
    discrepancy out.g out.d n < B :=
  (out.bound_discrepancy_lt_of_bound_discOffset (f := f) B hB) n

/-- Pointwise form of `bound_discOffset_lt_of_bound_discrepancy`. -/
theorem bound_discOffset_lt_of_bound_discrepancy_apply (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n : ℕ, discrepancy out.g out.d n < B) (n : ℕ) :
    discOffset f out.d out.m n < B :=
  (out.bound_discOffset_lt_of_bound_discrepancy (f := f) B hB) n

/-- Rewrite `apSumFrom f (m*d)` as an AP sum of the reduced sequence `out.g`.

This is the most common “start at the affine point” normal form used in Tao-style reductions.
-/
@[simp] theorem apSumFrom_eq_apSum (out : ReductionOutput f) (n : ℕ) :
    apSumFrom f (out.m * out.d) out.d n = apSum out.g out.d n := by
  -- `apSumFrom` is an `apSum` of the shifted sequence; rewrite using `out.g_eq`.
  simpa [out.g_eq] using
    (apSumFrom_eq_apSum_shift_add (f := f) (a := out.m * out.d) (d := out.d) (n := n))

/-- Rewrite `apSumFrom f (m*d)` as an offset AP sum of `f`.

This is a direct bridge between the two “tail sum” APIs in the discrepancy substrate.
-/
@[simp] theorem apSumFrom_eq_apSumOffset (out : ReductionOutput f) (n : ℕ) :
    apSumFrom f (out.m * out.d) out.d n = apSumOffset f out.d out.m n := by
  -- Rewrite both sides to AP sums of the same shifted sequence.
  simp [apSumFrom_eq_apSum_shift_add, apSumOffset_eq_apSum_shift_add]

/-- Reverse orientation of `apSumFrom_eq_apSumOffset`.

We do not mark this `[simp]` to avoid rewriting loops.
-/
theorem apSumOffset_eq_apSumFrom (out : ReductionOutput f) (n : ℕ) :
    apSumOffset f out.d out.m n = apSumFrom f (out.m * out.d) out.d n := by
  simpa using (out.apSumFrom_eq_apSumOffset (f := f) (n := n)).symm

/-- `natAbs` form of `apSumFrom_eq_apSumOffset`.

This is the cleanest way to move between `discOffset` and the “tail sum” API.
-/
theorem natAbs_apSumFrom_eq_natAbs_apSumOffset (out : ReductionOutput f) (n : ℕ) :
    Int.natAbs (apSumFrom f (out.m * out.d) out.d n) = Int.natAbs (apSumOffset f out.d out.m n) := by
  simpa [out.apSumFrom_eq_apSumOffset (f := f) (n := n)]

/-- Rewrite `discOffset` in terms of the tail-sum API `apSumFrom`.

This is just a repackaging of `natAbs_apSumFrom_eq_natAbs_apSumOffset`.
-/
theorem discOffset_eq_natAbs_apSumFrom (out : ReductionOutput f) (n : ℕ) :
    discOffset f out.d out.m n = Int.natAbs (apSumFrom f (out.m * out.d) out.d n) := by
  -- `discOffset` is definitional wrapper around `Int.natAbs (apSumOffset ...)`.
  simpa [discOffset, out.natAbs_apSumFrom_eq_natAbs_apSumOffset (f := f) (n := n)]

/-- `∃`-witness normal form: `discOffset` witnesses are equivalent to tail-sum witnesses.

This is often the cleanest bridge when one stage produces discrepancy witnesses in the
`discOffset` wrapper while the next stage wants to reason directly about `apSumFrom`.
-/
theorem exists_discOffset_gt_iff_exists_natAbs_apSumFrom_gt (out : ReductionOutput f) (C : ℕ) :
    (∃ n : ℕ, discOffset f out.d out.m n > C) ↔
      (∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C) := by
  constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩
  · simpa [out.discOffset_eq_natAbs_apSumFrom (f := f) (n := n)] using hn
  · simpa [out.discOffset_eq_natAbs_apSumFrom (f := f) (n := n)] using hn

/-- `<`-oriented version of `exists_discOffset_gt_iff_exists_natAbs_apSumFrom_gt`. -/
theorem exists_discOffset_lt_iff_exists_natAbs_apSumFrom_lt (out : ReductionOutput f) (C : ℕ) :
    (∃ n : ℕ, discOffset f out.d out.m n < C) ↔
      (∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) < C) := by
  constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩
  · simpa [out.discOffset_eq_natAbs_apSumFrom (f := f) (n := n)] using hn
  · simpa [out.discOffset_eq_natAbs_apSumFrom (f := f) (n := n)] using hn

/-- `∃`-witness normal form: tail-sum witnesses are equivalent to offset-sum witnesses.

This is a tiny helper, but it is convenient when a downstream stage naturally constructs a
witness using `apSumFrom` while an upstream lemma expects the `apSumOffset` normal form (or vice
versa).
-/
theorem exists_natAbs_apSumFrom_gt_iff_exists_natAbs_apSumOffset_gt (out : ReductionOutput f)
    (C : ℕ) :
    (∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C) ↔
      (∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > C) := by
  constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩
  · simpa [out.natAbs_apSumFrom_eq_natAbs_apSumOffset (f := f) (n := n)] using hn
  · simpa [out.natAbs_apSumFrom_eq_natAbs_apSumOffset (f := f) (n := n)] using hn

/-- Rewrite the reduced discrepancy in terms of the tail-sum API.

This is the cleanest “single-line” bridge when a downstream stage naturally produces a bound on
`Int.natAbs (apSumFrom f (m*d) d n)` and wants to interpret it as a statement about
`discrepancy out.g out.d n`.
-/
theorem discrepancy_eq_natAbs_apSumFrom (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n = Int.natAbs (apSumFrom f (out.m * out.d) out.d n) := by
  -- Both sides are definitional wrappers around `Int.natAbs`.
  simp [discrepancy, out.apSumFrom_eq_apSum (f := f) (n := n)]

/-- Reverse orientation of `out.apSumFrom_eq_apSum`.

This is occasionally useful when a downstream stage naturally produces an `apSum` statement about
`out.g` but wants to normalize it into the tail-sum nucleus `apSumFrom` for the original
sequence `f`.
-/
theorem apSum_eq_apSumFrom_contract (out : ReductionOutput f) (n : ℕ) :
    apSum out.g out.d n = apSumFrom f (out.m * out.d) out.d n := by
  -- This is just the existing bridge lemma, stated in the `apSum`-forward orientation.
  simpa using (out.apSum_eq_apSumFrom_mul (f := f) (n := n))

/-- Reverse orientation of `apSum_eq_apSumFrom_contract`.

Not marked `[simp]` to avoid rewriting loops.
-/
theorem apSumFrom_eq_apSum_contract (out : ReductionOutput f) (n : ℕ) :
    apSumFrom f (out.m * out.d) out.d n = apSum out.g out.d n := by
  simpa using (out.apSum_eq_apSumFrom_contract (f := f) (n := n)).symm

/-- `Int.natAbs` form of `apSum_eq_apSumFrom_contract`. -/
theorem natAbs_apSum_eq_natAbs_apSumFrom_contract (out : ReductionOutput f) (n : ℕ) :
    Int.natAbs (apSum out.g out.d n) = Int.natAbs (apSumFrom f (out.m * out.d) out.d n) := by
  simp [out.apSum_eq_apSumFrom_contract (f := f) (n := n)]

/-- A convenient `≤`-transfer wrapper for bounds phrased using the tail-sum nucleus.

This is the pointwise version of the global contract
`forall_discrepancy_le_iff_forall_natAbs_apSumFrom_mul_le`.
-/
theorem discrepancy_le_iff_natAbs_apSumFrom_le_contract (out : ReductionOutput f) (B n : ℕ) :
    discrepancy out.g out.d n ≤ B ↔ Int.natAbs (apSumFrom f (out.m * out.d) out.d n) ≤ B := by
  -- Rewrite `discrepancy` using the tail-sum bridge.
  simpa [out.discrepancy_eq_natAbs_apSumFrom (f := f) (n := n)]

/-- Strict-inequality version of `discrepancy_le_iff_natAbs_apSumFrom_le_contract`. -/
theorem discrepancy_lt_iff_natAbs_apSumFrom_lt_contract (out : ReductionOutput f) (B n : ℕ) :
    discrepancy out.g out.d n < B ↔ Int.natAbs (apSumFrom f (out.m * out.d) out.d n) < B := by
  -- Rewrite `discrepancy` using the same tail-sum bridge.
  simpa [out.discrepancy_eq_natAbs_apSumFrom (f := f) (n := n)]

/-!
### Fixed-step discrepancy witnesses, rewritten through the tail-sum API

Downstream stages of the Tao2015 pipeline often want to talk about sums of the form
`apSumFrom f (m*d) d n` ("start at the affine point") rather than explicitly introducing the
shifted sequence `out.g`.

These lemmas provide the most direct witness-normal-form bridges between:
- `HasDiscrepancyAtLeastAlong out.g out.d C` and
- an `Int.natAbs (apSumFrom ...)` inequality witness.
-/

/-- Rewrite fixed-step discrepancy of the reduced sequence `out.g` into a tail-sum witness for `f`.

This is the cleanest normal form when a downstream stage constructs a large discrepancy witness
using the tail-sum API.
-/
theorem hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_gt (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔
      (∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C) := by
  -- Unfold `HasDiscrepancyAtLeastAlong` and rewrite `apSum out.g` via `apSumFrom_eq_apSum`.
  simp [HasDiscrepancyAtLeastAlong, out.apSumFrom_eq_apSum]

/-- DiscOffset-free witness normal form: rewrite a fixed-step discrepancy witness for `out.g`
into a witness about the raw offset AP sum `apSumOffset` of the original sequence `f`.

This is sometimes preferable to going through the wrapper `discOffset`.
-/
theorem hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt (out : ReductionOutput f)
    (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔
      (∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > C) := by
  -- Unfold the predicate and rewrite `apSum out.g` using the stage-1 contract.
  simp [HasDiscrepancyAtLeastAlong, out.apSum_contract]

/-- `<`-oriented version of `hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt`. -/
theorem hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_lt (out : ReductionOutput f)
    (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔
      (∃ n : ℕ, C < Int.natAbs (apSumOffset f out.d out.m n)) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using
    (out.hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt (f := f) (C := C))

/-- Single-witness normal form: a raw offset AP-sum witness is the same as a discrepancy witness
for the reduced sequence `out.g`.

This is a light wrapper around `out.discrepancy_eq_natAbs_apSumOffset`.
-/
theorem exists_natAbs_apSumOffset_gt_iff_exists_discrepancy_gt (out : ReductionOutput f) (C : ℕ) :
    (∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > C) ↔
      (∃ n : ℕ, discrepancy out.g out.d n > C) := by
  constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩
  · simpa [out.discrepancy_eq_natAbs_apSumOffset (f := f) (n := n)] using hn
  · simpa [out.discrepancy_eq_natAbs_apSumOffset (f := f) (n := n)] using hn

/-- `<`-oriented version of `hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_gt`. -/
theorem hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_lt (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔
      (∃ n : ℕ, C < Int.natAbs (apSumFrom f (out.m * out.d) out.d n)) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using (out.hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_gt (f := f) (C := C))

/-- Single-witness normal form: a tail-sum witness is the same as a discrepancy witness for `out.g`.

This is the `∃ n` (as opposed to `HasDiscrepancyAtLeastAlong`) form of the same contract, and it
shows up often because later stages usually produce one explicit `n`.
-/
theorem exists_natAbs_apSumFrom_gt_iff_exists_discrepancy_gt (out : ReductionOutput f) (C : ℕ) :
    (∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C) ↔
      (∃ n : ℕ, discrepancy out.g out.d n > C) := by
  constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩
  · -- Rewrite the tail sum witness into a discrepancy witness.
    simpa [out.discrepancy_eq_natAbs_apSumFrom (f := f) (n := n)] using hn
  · -- Rewrite back.
    simpa [out.discrepancy_eq_natAbs_apSumFrom (f := f) (n := n)] using hn

/-- `<`-oriented single-witness normal form (`C < ...`). -/
theorem exists_natAbs_apSumFrom_lt_iff_exists_discrepancy_lt (out : ReductionOutput f) (C : ℕ) :
    (∃ n : ℕ, C < Int.natAbs (apSumFrom f (out.m * out.d) out.d n)) ↔
      (∃ n : ℕ, C < discrepancy out.g out.d n) := by
  -- Just rewrite `C < x` as `x > C` and reuse the `> C` lemma.
  simpa [gt_iff_lt] using (out.exists_natAbs_apSumFrom_gt_iff_exists_discrepancy_gt (f := f) (C := C))

/-- `>`-oriented single-witness normal form with the directions swapped.

This is just the symmetric form of `exists_natAbs_apSumFrom_gt_iff_exists_discrepancy_gt`.
-/
theorem exists_discrepancy_gt_iff_exists_natAbs_apSumFrom_gt (out : ReductionOutput f) (C : ℕ) :
    (∃ n : ℕ, discrepancy out.g out.d n > C) ↔
      (∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C) := by
  simpa using (out.exists_natAbs_apSumFrom_gt_iff_exists_discrepancy_gt (f := f) (C := C)).symm

/-- `<`-oriented single-witness normal form with the directions swapped. -/
theorem exists_discrepancy_lt_iff_exists_natAbs_apSumFrom_lt (out : ReductionOutput f) (C : ℕ) :
    (∃ n : ℕ, C < discrepancy out.g out.d n) ↔
      (∃ n : ℕ, C < Int.natAbs (apSumFrom f (out.m * out.d) out.d n)) := by
  simpa using (out.exists_natAbs_apSumFrom_lt_iff_exists_discrepancy_lt (f := f) (C := C)).symm

/-- Unboundedness along the reduced step, expressed directly as tail-sum witnesses for `f`.

This is just `∀ C, HasDiscrepancyAtLeastAlong out.g out.d C` rewritten through the bridge lemma
`hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_gt`.
-/
theorem forall_hasDiscrepancyAtLeastAlong_iff_forall_exists_natAbs_apSumFrom_gt
    (out : ReductionOutput f) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) ↔
      (∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C) := by
  constructor
  · intro h C
    exact (out.hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_gt (f := f) (C := C)).1 (h C)
  · intro h C
    exact (out.hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_gt (f := f) (C := C)).2 (h C)

/-- `<`-oriented version of `forall_hasDiscrepancyAtLeastAlong_iff_forall_exists_natAbs_apSumFrom_gt`. -/
theorem forall_hasDiscrepancyAtLeastAlong_iff_forall_exists_natAbs_apSumFrom_lt
    (out : ReductionOutput f) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) ↔
      (∀ C : ℕ, ∃ n : ℕ, C < Int.natAbs (apSumFrom f (out.m * out.d) out.d n)) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using
    (out.forall_hasDiscrepancyAtLeastAlong_iff_forall_exists_natAbs_apSumFrom_gt (f := f))

/-- A tail-sum witness normal form for `¬ BoundedDiscrepancyAlong out.g out.d`.

This is the standard “not bounded ↔ ∀ C, ∃ witness with discrepancy > C” lemma specialized to the
reduced sequence, with the witness further rewritten to the tail-sum API `apSumFrom` for `f`.
-/
theorem forall_exists_natAbs_apSumFrom_gt_iff_not_boundedDiscrepancyAlong
    (out : ReductionOutput f) :
    (∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C) ↔
      ¬ BoundedDiscrepancyAlong out.g out.d := by
  -- First rewrite `¬ BoundedDiscrepancyAlong` to `∀ C, HasDiscrepancyAtLeastAlong` for the reduced sequence.
  -- Then rewrite the fixed-step predicate to the tail-sum witness normal form.
  calc
    (∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C)
        ↔ (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) := by
          simpa using
            (out.forall_hasDiscrepancyAtLeastAlong_iff_forall_exists_natAbs_apSumFrom_gt (f := f)).symm
    _ ↔ ¬ BoundedDiscrepancyAlong out.g out.d := by
          simpa [HasDiscrepancyAtLeastAlong] using
            (HasDiscrepancyAtLeastAlong.forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscrepancyAlong
              (g := out.g) (d := out.d))

/-!
### Peeling bundled offsets

Many downstream reductions will accumulate offsets of the form `(out.m + m₂) * out.d`.
The next lemmas let you “peel off” the initial `out.m*out.d` shift encoded by
`out.g`, turning an offset sum/discrepancy of `f` into an offset sum/discrepancy of `out.g`.
-/

/-- Peel the bundled offset in `out` at the AP-sum level.

This is `apSumOffset_add` specialized to the shift packed in `out.g`.
-/
theorem apSumOffset_add_eq_apSumOffset_g (out : ReductionOutput f) (m₂ n : ℕ) :
    apSumOffset f out.d (out.m + m₂) n = apSumOffset out.g out.d m₂ n := by
  -- Re-associate the offset, then rewrite the shifted sequence using `out.g_eq`.
  simpa [out.g_eq] using
    (Tao2015.apSumOffset_add (f := f) (d := out.d) (m₁ := out.m) (m₂ := m₂) (n := n))

/-- Peel the bundled offset in `out` at the discrepancy level.

This is the `discOffset` analogue of `apSumOffset_add_eq_apSumOffset_g`.
-/
theorem discOffset_add_eq_discOffset_g (out : ReductionOutput f) (m₂ n : ℕ) :
    discOffset f out.d (out.m + m₂) n = discOffset out.g out.d m₂ n := by
  -- `discOffset` is just `natAbs` of `apSumOffset`.
  simp [discOffset, out.apSumOffset_add_eq_apSumOffset_g (f := f) (m₂ := m₂) (n := n)]

/-- Reverse orientation of `apSumOffset_add_eq_apSumOffset_g`. -/
theorem apSumOffset_g_eq_apSumOffset_add (out : ReductionOutput f) (m₂ n : ℕ) :
    apSumOffset out.g out.d m₂ n = apSumOffset f out.d (out.m + m₂) n := by
  simpa using (out.apSumOffset_add_eq_apSumOffset_g (f := f) (m₂ := m₂) (n := n)).symm

/-- Reverse orientation of `discOffset_add_eq_discOffset_g`. -/
theorem discOffset_g_eq_discOffset_add (out : ReductionOutput f) (m₂ n : ℕ) :
    discOffset out.g out.d m₂ n = discOffset f out.d (out.m + m₂) n := by
  simpa using (out.discOffset_add_eq_discOffset_g (f := f) (m₂ := m₂) (n := n)).symm

/-- Rewrite a shifted AP sum of the reduced sequence into an offset sum of the reduced sequence.

This is just a specialization of `apSum_shift_add_mul_eq_apSumOffset`.
-/
theorem apSum_shiftRight_eq_apSumOffset_g (out : ReductionOutput f) (m₂ n : ℕ) :
    apSum (fun k => out.g (k + m₂ * out.d)) out.d n = apSumOffset out.g out.d m₂ n := by
  simpa using (Tao2015.apSum_shift_add_mul_eq_apSumOffset (f := out.g) (d := out.d) (m := m₂) (n := n))

/-- Rewrite a shifted AP sum of the reduced sequence directly into an offset sum of `f` with the
bundled offset `out.m + m₂`.
-/
theorem apSum_shiftRight_eq_apSumOffset_add (out : ReductionOutput f) (m₂ n : ℕ) :
    apSum (fun k => out.g (k + m₂ * out.d)) out.d n = apSumOffset f out.d (out.m + m₂) n := by
  -- First rewrite to an offset sum of `out.g`, then peel the bundled offset back to `f`.
  simpa [out.apSumOffset_g_eq_apSumOffset_add (f := f) (m₂ := m₂) (n := n)] using
    (out.apSum_shiftRight_eq_apSumOffset_g (f := f) (m₂ := m₂) (n := n))

/-- Discrepancy rewrite: shift `out.g` by `m₂*out.d`, then rewrite as a bundled offset discrepancy of `f`.

This is the discrepancy analogue of `apSum_shiftRight_eq_apSumOffset_add`.
-/
theorem discrepancy_shiftRight_eq_discOffset_add (out : ReductionOutput f) (m₂ n : ℕ) :
    discrepancy (fun k => out.g (k + m₂ * out.d)) out.d n = discOffset f out.d (out.m + m₂) n := by
  -- First rewrite a shifted discrepancy to an offset discrepancy of `out.g`.
  -- Then peel the bundled offset back to `f`.
  calc
    discrepancy (fun k => out.g (k + m₂ * out.d)) out.d n
        = discOffset out.g out.d m₂ n := by
          simpa using
            (Tao2015.discrepancy_shift_add_mul_eq_discOffset (f := out.g) (d := out.d) (m := m₂) (n := n))
    _ = discOffset f out.d (out.m + m₂) n := by
          simpa using (out.discOffset_g_eq_discOffset_add (f := f) (m₂ := m₂) (n := n))

/-- Reverse orientation of `discrepancy_shiftRight_eq_discOffset_add`. -/
theorem discOffset_add_eq_discrepancy_shiftRight (out : ReductionOutput f) (m₂ n : ℕ) :
    discOffset f out.d (out.m + m₂) n = discrepancy (fun k => out.g (k + m₂ * out.d)) out.d n := by
  simpa using (out.discrepancy_shiftRight_eq_discOffset_add (f := f) (m₂ := m₂) (n := n)).symm

/-- Rewrite the discrepancy of a further-shifted reduced sequence into the affine nucleus `apSumFrom`.

This is the “all the way to `apSumFrom`” normal form:

`discrepancy (shift out.g) out.d n = natAbs (apSumFrom f ((out.m+m₂)*out.d) out.d n)`.

It is convenient for downstream stages that operate purely on affine progressions and prefer to
avoid mentioning `discOffset` explicitly.
-/
theorem discrepancy_shiftRight_eq_natAbs_apSumFrom_add_mul (out : ReductionOutput f) (m₂ n : ℕ) :
    discrepancy (fun k => out.g (k + m₂ * out.d)) out.d n =
      Int.natAbs (apSumFrom f ((out.m + m₂) * out.d) out.d n) := by
  calc
    discrepancy (fun k => out.g (k + m₂ * out.d)) out.d n
        = discOffset f out.d (out.m + m₂) n := by
          simpa using
            (out.discrepancy_shiftRight_eq_discOffset_add (f := f) (m₂ := m₂) (n := n))
    _ = Int.natAbs (apSumFrom f ((out.m + m₂) * out.d) out.d n) := by
          simpa using
            (Tao2015.discOffset_eq_natAbs_apSumFrom_mul (f := f) (d := out.d) (m := out.m + m₂) (n := n))

/-- Reverse orientation of `discrepancy_shiftRight_eq_natAbs_apSumFrom_add_mul`. -/
theorem natAbs_apSumFrom_add_mul_eq_discrepancy_shiftRight (out : ReductionOutput f) (m₂ n : ℕ) :
    Int.natAbs (apSumFrom f ((out.m + m₂) * out.d) out.d n) =
      discrepancy (fun k => out.g (k + m₂ * out.d)) out.d n := by
  simpa using (out.discrepancy_shiftRight_eq_natAbs_apSumFrom_add_mul (f := f) (m₂ := m₂) (n := n)).symm

/-- Fixed-step discrepancy for a further-shifted reduced sequence, rewritten as a bundled offset witness.

This is a small convenience lemma: it lets downstream stages immediately move from a statement
about

`HasDiscrepancyAtLeastAlong (shift out.g) out.d C`

to a witness about the original sequence `f` with the accumulated offset `out.m + m₂`.
-/
theorem hasDiscrepancyAtLeastAlong_shiftRight_iff_exists_discOffset_add_gt
    (out : ReductionOutput f) (m₂ C : ℕ) :
    HasDiscrepancyAtLeastAlong (fun k => out.g (k + m₂ * out.d)) out.d C ↔
      (∃ n : ℕ, discOffset f out.d (out.m + m₂) n > C) := by
  -- Rewrite `HasDiscrepancyAtLeastAlong` into the `discrepancy` wrapper form,
  -- then use `discrepancy_shiftRight_eq_discOffset_add`.
  constructor
  · intro h
    rcases (HasDiscrepancyAtLeastAlong.iff_exists_discrepancy_gt
        (f := fun k => out.g (k + m₂ * out.d)) (d := out.d) (C := C)).1 h with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.discrepancy_shiftRight_eq_discOffset_add (f := f) (m₂ := m₂) (n := n)] using hn
  · rintro ⟨n, hn⟩
    have : discrepancy (fun k => out.g (k + m₂ * out.d)) out.d n > C := by
      simpa [out.discrepancy_shiftRight_eq_discOffset_add (f := f) (m₂ := m₂) (n := n)] using hn
    exact (HasDiscrepancyAtLeastAlong.iff_exists_discrepancy_gt
        (f := fun k => out.g (k + m₂ * out.d)) (d := out.d) (C := C)).2 ⟨n, this⟩

/-- `<`-oriented version of `hasDiscrepancyAtLeastAlong_shiftRight_iff_exists_discOffset_add_gt`. -/
theorem hasDiscrepancyAtLeastAlong_shiftRight_iff_exists_discOffset_add_lt
    (out : ReductionOutput f) (m₂ C : ℕ) :
    HasDiscrepancyAtLeastAlong (fun k => out.g (k + m₂ * out.d)) out.d C ↔
      (∃ n : ℕ, C < discOffset f out.d (out.m + m₂) n) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using
    (out.hasDiscrepancyAtLeastAlong_shiftRight_iff_exists_discOffset_add_gt (f := f) (m₂ := m₂) (C := C))

/-!
### Producing a new `ReductionOutput` by shifting the reduced sequence

A very common move in Tao-style reductions is to take an existing reduction output `out :
ReductionOutput f` and then shift the reduced sequence again by an additional multiple `m₂*out.d`.

At the level of offsets, this simply replaces the bundled offset parameter `out.m` by
`out.m + m₂`.

The following constructor packages this into a new `ReductionOutput f` so downstream stages can
stay entirely in the `ReductionOutput` interface.
-/

/-- Shift the reduced sequence `out.g` by an additional multiple `m₂*out.d`, producing a new
reduction output with the bundled offset `out.m + m₂`.

This is a small but useful “interface combinator”: it turns a downstream shift into a first-class
reduction step.
-/
noncomputable def shiftRight (out : ReductionOutput f) (m₂ : ℕ) : ReductionOutput f := by
  classical
  refine
    { d := out.d
      m := out.m + m₂
      hd := out.hd
      g := fun k => out.g (k + m₂ * out.d)
      hg := ?_
      g_eq := ?_
      apSum_contract := ?_
      contract_discrepancy_le := ?_ }
  · -- `IsSignSequence` is stable under shifts.
    exact Tao2015.IsSignSequence.shift_add_mul (f := out.g) out.hg m₂ out.d
  · -- Compute the new `g` as a single shift of `f`.
    funext k
    -- `out.g (k + m₂*out.d) = f (k + (out.m+m₂)*out.d)`.
    simp [out.g_eq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.add_mul, Nat.mul_add,
      Nat.mul_assoc]
  · intro n
    -- Rewrite the shifted AP sum as the bundled offset AP sum of `f`.
    simpa using (out.apSum_shiftRight_eq_apSumOffset_add (f := f) (m₂ := m₂) (n := n))
  · intro B hB n
    -- Transfer the bound using the AP-sum bridge.
    exact
      ReductionOutput.contract_discrepancy_le_of_apSum_contract (f := f)
        (g := fun k => out.g (k + m₂ * out.d)) (d := out.d) (m := out.m + m₂) (B := B)
        (h := fun n => by
          simpa using (out.apSum_shiftRight_eq_apSumOffset_add (f := f) (m₂ := m₂) (n := n)))
        hB n

/-!
### `shiftRight` simp API

These lemmas let downstream stages use `shiftRight` without unfolding its record fields.
-/

@[simp] theorem shiftRight_d (out : ReductionOutput f) (m₂ : ℕ) :
    (shiftRight (f := f) out m₂).d = out.d := by
  simp [shiftRight]

@[simp] theorem shiftRight_m (out : ReductionOutput f) (m₂ : ℕ) :
    (shiftRight (f := f) out m₂).m = out.m + m₂ := by
  simp [shiftRight]

@[simp] theorem shiftRight_hd (out : ReductionOutput f) (m₂ : ℕ) :
    (shiftRight (f := f) out m₂).hd = out.hd := by
  simp [shiftRight]

@[simp] theorem shiftRight_g_apply (out : ReductionOutput f) (m₂ : ℕ) (k : ℕ) :
    (shiftRight (f := f) out m₂).g k = out.g (k + m₂ * out.d) := by
  simp [shiftRight]

theorem shiftRight_g_eq (out : ReductionOutput f) (m₂ : ℕ) :
    (shiftRight (f := f) out m₂).g = fun k => out.g (k + m₂ * out.d) := by
  funext k
  simp

@[simp] theorem shiftRight_apSum_eq_apSumOffset_add (out : ReductionOutput f) (m₂ n : ℕ) :
    apSum (shiftRight (f := f) out m₂).g out.d n = apSumOffset f out.d (out.m + m₂) n := by
  -- `shiftRight` sets `d := out.d` and fills `apSum_contract` with the bundled-offset bridge.
  simp [shiftRight]

/-- Discrepancy rewrite rule for `shiftRight`.

Marked `[simp]` for the same reason as `ReductionOutput.mkShiftOfSign_discrepancy_contract`:
it is the canonical normal form for discrepancies of the shifted reduction output.
-/
@[simp] theorem shiftRight_discrepancy_contract (out : ReductionOutput f) (m₂ n : ℕ) :
    discrepancy (shiftRight (f := f) out m₂).g out.d n = discOffset f out.d (out.m + m₂) n := by
  -- Both sides are definitional wrappers around `Int.natAbs`, and the AP-sum bridge is `[simp]`.
  simp [discrepancy, discOffset]

/-!
### `apSumFrom` API for `shiftRight`

Downstream stages often prefer the tail-sum normal form `apSumFrom f (m*d) d`.
Since `shiftRight` updates the bundled offset from `out.m` to `out.m + m₂`, it is convenient to
have `apSumFrom` rewrite rules that mention the *new* affine start point explicitly.
-/

/-- Rewrite the tail sum starting at `((out.m + m₂) * out.d)` as an AP sum of the shifted reduction output. -/
theorem shiftRight_apSumFrom (out : ReductionOutput f) (m₂ n : ℕ) :
    apSumFrom f ((out.m + m₂) * out.d) out.d n = apSum (shiftRight (f := f) out m₂).g out.d n := by
  -- This is just `ReductionOutput.apSumFrom_eq_apSum` specialized to `out := shiftRight out m₂`.
  simpa [shiftRight] using
    (ReductionOutput.apSumFrom_eq_apSum (f := f) (out := shiftRight (f := f) out m₂) (n := n))

/-- Same as `shiftRight_apSumFrom`, but with the affine start point written additively.

This avoids needing to normalize products of sums (`(out.m + m₂) * out.d`) in downstream steps.
-/
theorem shiftRight_apSumFrom_add (out : ReductionOutput f) (m₂ n : ℕ) :
    apSumFrom f (out.m * out.d + m₂ * out.d) out.d n =
      apSum (shiftRight (f := f) out m₂).g out.d n := by
  -- Rewrite the start point using `Nat.add_mul`, then reuse `shiftRight_apSumFrom`.
  simpa [Nat.add_mul, Nat.mul_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (shiftRight_apSumFrom (f := f) (out := out) (m₂ := m₂) (n := n))

/-- Additive-start-point version of `shiftRight_apSumFrom_eq_apSumOffset`.

This is occasionally the cleanest normal form when offsets are accumulated as sums.
-/
theorem shiftRight_apSumFrom_add_eq_apSumOffset (out : ReductionOutput f) (m₂ n : ℕ) :
    apSumFrom f (out.m * out.d + m₂ * out.d) out.d n = apSumOffset f out.d (out.m + m₂) n := by
  -- Rewrite the LHS start point and then use `shiftRight_apSumFrom_eq_apSumOffset`.
  simpa [Nat.add_mul, Nat.mul_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (shiftRight_apSumFrom_eq_apSumOffset (f := f) (out := out) (m₂ := m₂) (n := n))

/-- Rewrite the tail sum starting at `((out.m + m₂) * out.d)` directly as an offset sum of `f`. -/
theorem shiftRight_apSumFrom_eq_apSumOffset (out : ReductionOutput f) (m₂ n : ℕ) :
    apSumFrom f ((out.m + m₂) * out.d) out.d n = apSumOffset f out.d (out.m + m₂) n := by
  -- This is just `ReductionOutput.apSumFrom_eq_apSumOffset` for `out := shiftRight out m₂`.
  simpa [shiftRight] using
    (ReductionOutput.apSumFrom_eq_apSumOffset (f := f) (out := shiftRight (f := f) out m₂) (n := n))

/-- Rewrite `discOffset` using the tail-sum normal form for the shifted reduction output. -/
theorem shiftRight_discOffset_eq_natAbs_apSumFrom (out : ReductionOutput f) (m₂ n : ℕ) :
    discOffset f out.d (out.m + m₂) n = Int.natAbs (apSumFrom f ((out.m + m₂) * out.d) out.d n) := by
  -- `discOffset` is definitional wrapper around `Int.natAbs (apSumOffset ...)`.
  simp [discOffset, shiftRight_apSumFrom_eq_apSumOffset (f := f) (out := out) (m₂ := m₂) (n := n)]

/-- A `Context f` implies bounded discrepancy along the shifted reduction output.

This is a small wrapper around `ReductionOutput.boundedDiscrepancyAlong_of_context`, specialized to
`shiftRight`.
-/
theorem shiftRight_boundedDiscrepancyAlong_of_context (out : ReductionOutput f) (m₂ : ℕ) (ctx : Context f) :
    BoundedDiscrepancyAlong (shiftRight (f := f) out m₂).g out.d := by
  -- Apply the general lemma to the shifted reduction output.
  have h := (ReductionOutput.boundedDiscrepancyAlong_of_context (f := f)
    (out := shiftRight (f := f) out m₂) ctx)
  -- Normalize the step size.
  simpa [shiftRight_d] using h

/-- `shiftRight` satisfies the discrepancy-transfer contract definitionally.

This is a convenience lemma: downstream steps can use the contract field without unfolding
`shiftRight`.
-/
@[simp] theorem shiftRight_contract_discrepancy_le (out : ReductionOutput f) (m₂ : ℕ) (B : ℕ)
    (hB : ∀ n : ℕ, discOffset f out.d (out.m + m₂) n ≤ B) (n : ℕ) :
    (shiftRight (f := f) out m₂).contract_discrepancy_le B hB n = hB n := by
  -- The contract is just rewriting `discrepancy` to `discOffset` via the bridge rule.
  simp [shiftRight, discrepancy, discOffset]

/-- Function-extensional version of `shiftRight_contract_discrepancy_le`. -/
@[simp] theorem shiftRight_contract_discrepancy_le_funext (out : ReductionOutput f) (m₂ : ℕ) (B : ℕ)
    (hB : ∀ n : ℕ, discOffset f out.d (out.m + m₂) n ≤ B) :
    (shiftRight (f := f) out m₂).contract_discrepancy_le B hB = hB := by
  funext n
  simpa using (shiftRight_contract_discrepancy_le (f := f) (out := out) (m₂ := m₂) (B := B)
    (hB := hB) (n := n))

/-!
### Fixed-step discrepancy rewrites for `shiftRight`

These are small convenience lemmas: they let downstream stages work directly with the shifted
reduction output `(shiftRight out m₂)` without manually normalizing its bundled offset.
-/

/-- `HasDiscrepancyAtLeastAlong` for the shifted reduction output, rewritten as a witness about
`discOffset f` with the accumulated offset `out.m + m₂`.
-/
theorem shiftRight_hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt
    (out : ReductionOutput f) (m₂ C : ℕ) :
    HasDiscrepancyAtLeastAlong (shiftRight (f := f) out m₂).g out.d C ↔
      (∃ n : ℕ, discOffset f out.d (out.m + m₂) n > C) := by
  -- This is just the general `ReductionOutput` lemma, plus normalization of `shiftRight` fields.
  simpa [shiftRight_d, shiftRight_m] using
    (ReductionOutput.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt
      (f := f) (out := shiftRight (f := f) out m₂) (C := C))

/-- `<`-oriented version of `shiftRight_hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt`. -/
theorem shiftRight_hasDiscrepancyAtLeastAlong_iff_exists_discOffset_lt
    (out : ReductionOutput f) (m₂ C : ℕ) :
    HasDiscrepancyAtLeastAlong (shiftRight (f := f) out m₂).g out.d C ↔
      (∃ n : ℕ, C < discOffset f out.d (out.m + m₂) n) := by
  simpa [gt_iff_lt] using
    (shiftRight_hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) (out := out) (m₂ := m₂) (C := C))

/-- Sum-level version: `shiftRight` discrepancy witnesses phrased using `Int.natAbs (apSumOffset ...)`.
-/
theorem shiftRight_hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt
    (out : ReductionOutput f) (m₂ C : ℕ) :
    HasDiscrepancyAtLeastAlong (shiftRight (f := f) out m₂).g out.d C ↔
      (∃ n : ℕ, Int.natAbs (apSumOffset f out.d (out.m + m₂) n) > C) := by
  simpa [shiftRight_d, shiftRight_m] using
    (ReductionOutput.hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumOffset_gt
      (f := f) (out := shiftRight (f := f) out m₂) (C := C))

/-!
### Composition lemmas for `shiftRight`

These are small “algebra” facts: successive `shiftRight` operations add their offsets.
Downstream stages often build multi-step reductions, and these lemmas keep the resulting
expressions from growing unwieldy.
-/

@[simp] theorem shiftRight_shiftRight_m (out : ReductionOutput f) (m₁ m₂ : ℕ) :
    (shiftRight (f := f) (shiftRight (f := f) out m₁) m₂).m = out.m + m₁ + m₂ := by
  -- `shiftRight` adds the new offset to the bundled offset parameter.
  simp [Nat.add_assoc]

@[simp] theorem shiftRight_shiftRight_d (out : ReductionOutput f) (m₁ m₂ : ℕ) :
    (shiftRight (f := f) (shiftRight (f := f) out m₁) m₂).d = out.d := by
  simp [shiftRight]

theorem shiftRight_shiftRight_g_apply (out : ReductionOutput f) (m₁ m₂ k : ℕ) :
    (shiftRight (f := f) (shiftRight (f := f) out m₁) m₂).g k =
      out.g (k + (m₁ + m₂) * out.d) := by
  -- Expand both shifts and re-associate additions/multiplications.
  simp [shiftRight, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.add_mul, Nat.mul_add,
    Nat.mul_assoc]

@[simp] theorem shiftRight_shiftRight_discrepancy_contract (out : ReductionOutput f) (m₁ m₂ n : ℕ) :
    discrepancy (shiftRight (f := f) (shiftRight (f := f) out m₁) m₂).g out.d n =
      discOffset f out.d (out.m + m₁ + m₂) n := by
  -- Use the `[simp]` discrepancy contract for each shift and normalize associativity.
  simp [Nat.add_assoc]

/-!
### Tail-sum (`apSumFrom`) rewrites for shifted reductions

Downstream stages often prefer the “tail sum” API `apSumFrom` (start at a base point `a` and take
an AP with step `d`).  When we shift the reduced sequence `out.g` by an additional multiple
`m₂*out.d`, it is convenient to have ready-made rewrite rules that keep everything in
`apSumFrom` / `apSumOffset` normal forms.
-/

/-- Shifting `out.g` by `m₂*out.d` and taking an AP sum is the same as taking a tail sum of `out.g`.

This is just the definitional bridge `apSumFrom_eq_apSum_shift_add` specialized to the shift
`a = m₂*out.d`.
-/
theorem apSumFrom_shiftRight_eq_apSum (out : ReductionOutput f) (m₂ n : ℕ) :
    apSumFrom out.g (m₂ * out.d) out.d n = apSum (fun k => out.g (k + m₂ * out.d)) out.d n := by
  simpa using
    (apSumFrom_eq_apSum_shift_add (f := out.g) (a := m₂ * out.d) (d := out.d) (n := n))

/-- Tail-sum rewrite: `apSumFrom out.g (m₂*out.d)` is an offset AP sum of `f` with bundled offset
`out.m + m₂`.
-/
theorem apSumFrom_shiftRight_eq_apSumOffset_add (out : ReductionOutput f) (m₂ n : ℕ) :
    apSumFrom out.g (m₂ * out.d) out.d n = apSumOffset f out.d (out.m + m₂) n := by
  -- Rewrite `apSumFrom` to an AP sum of the shifted reduced sequence, then apply the existing bridge.
  simpa [apSumFrom_eq_apSum_shift_add] using
    (out.apSum_shiftRight_eq_apSumOffset_add (f := f) (m₂ := m₂) (n := n))

/-- Reverse orientation of `apSumFrom_shiftRight_eq_apSumOffset_add`.

We keep this around because downstream proofs often start from an offset sum and want to rewrite
it into the tail-sum API.
-/
theorem apSumOffset_add_eq_apSumFrom_shiftRight (out : ReductionOutput f) (m₂ n : ℕ) :
    apSumOffset f out.d (out.m + m₂) n = apSumFrom out.g (m₂ * out.d) out.d n := by
  simpa using (out.apSumFrom_shiftRight_eq_apSumOffset_add (f := f) (m₂ := m₂) (n := n)).symm

/-- `natAbs` reverse orientation of `natAbs_apSumFrom_shiftRight_eq_natAbs_apSumOffset_add`.

We prove this directly from `apSumFrom_shiftRight_eq_apSumOffset_add` to avoid unnecessary
forward references.
-/
theorem natAbs_apSumOffset_add_eq_natAbs_apSumFrom_shiftRight (out : ReductionOutput f) (m₂ n : ℕ) :
    Int.natAbs (apSumOffset f out.d (out.m + m₂) n) =
      Int.natAbs (apSumFrom out.g (m₂ * out.d) out.d n) := by
  -- Take `Int.natAbs` of the AP-sum identity and flip sides.
  have h := congrArg Int.natAbs
    (out.apSumFrom_shiftRight_eq_apSumOffset_add (f := f) (m₂ := m₂) (n := n))
  simpa using h.symm

/-- Reverse orientation of `discOffset_add_eq_natAbs_apSumFrom_shiftRight`.

This is the bundled-offset analogue of `out.discOffset_eq_natAbs_apSumFrom`.
-/
theorem natAbs_apSumFrom_shiftRight_eq_discOffset_add (out : ReductionOutput f) (m₂ n : ℕ) :
    Int.natAbs (apSumFrom out.g (m₂ * out.d) out.d n) = discOffset f out.d (out.m + m₂) n := by
  -- Expand `discOffset` and reuse the tail-sum rewrite.
  simp [discOffset, out.apSumFrom_shiftRight_eq_apSumOffset_add (f := f) (m₂ := m₂) (n := n)]

/-- `natAbs` form of `apSumFrom_shiftRight_eq_apSumOffset_add`.

This is the cleanest bridge when you want to talk about absolute values of tail sums.
-/
theorem natAbs_apSumFrom_shiftRight_eq_natAbs_apSumOffset_add (out : ReductionOutput f) (m₂ n : ℕ) :
    Int.natAbs (apSumFrom out.g (m₂ * out.d) out.d n) =
      Int.natAbs (apSumOffset f out.d (out.m + m₂) n) := by
  -- Take `Int.natAbs` of the AP-sum identity.
  simpa using congrArg Int.natAbs
    (out.apSumFrom_shiftRight_eq_apSumOffset_add (f := f) (m₂ := m₂) (n := n))

/-- `discOffset` rewrite in terms of a tail sum of `out.g`.

This is the bundled-offset analogue of `out.discOffset_eq_natAbs_apSumFrom`.
-/
theorem discOffset_add_eq_natAbs_apSumFrom_shiftRight (out : ReductionOutput f) (m₂ n : ℕ) :
    discOffset f out.d (out.m + m₂) n = Int.natAbs (apSumFrom out.g (m₂ * out.d) out.d n) := by
  -- Expand `discOffset`, then rewrite the offset sum as a tail sum.
  have h := congrArg Int.natAbs
    (out.apSumOffset_add_eq_apSumFrom_shiftRight (f := f) (m₂ := m₂) (n := n))
  simpa [discOffset] using h

/-- `natAbs` form of the AP-sum bridge rule. -/
theorem natAbs_apSum_eq_natAbs_apSumOffset (out : ReductionOutput f) (n : ℕ) :
    Int.natAbs (apSum out.g out.d n) = Int.natAbs (apSumOffset f out.d out.m n) := by
  simpa [out.apSum_eq_apSumOffset (f := f) (n := n)]

/-- Inequality transport across the AP-sum bridge rule (≤). -/
theorem natAbs_apSum_le_iff_natAbs_apSumOffset_le (out : ReductionOutput f) (B : ℕ) (n : ℕ) :
    Int.natAbs (apSum out.g out.d n) ≤ B ↔ Int.natAbs (apSumOffset f out.d out.m n) ≤ B := by
  simpa [out.apSum_eq_apSumOffset (f := f) (n := n)]

/-- Inequality transport across the AP-sum bridge rule (<). -/
theorem natAbs_apSum_lt_iff_natAbs_apSumOffset_lt (out : ReductionOutput f) (B : ℕ) (n : ℕ) :
    Int.natAbs (apSum out.g out.d n) < B ↔ Int.natAbs (apSumOffset f out.d out.m n) < B := by
  simpa [out.apSum_eq_apSumOffset (f := f) (n := n)]

/-- Uniform inequality transport across the AP-sum bridge rule (≤). -/
theorem forall_natAbs_apSum_le_iff_forall_natAbs_apSumOffset_le (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, Int.natAbs (apSum out.g out.d n) ≤ B) ↔
      (∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ B) := by
  constructor
  · intro h n
    simpa [out.apSum_contract] using h n
  · intro h n
    simpa [out.apSum_contract] using h n

/-- Uniform inequality transport across the AP-sum bridge rule (<). -/
theorem forall_natAbs_apSum_lt_iff_forall_natAbs_apSumOffset_lt (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, Int.natAbs (apSum out.g out.d n) < B) ↔
      (∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) < B) := by
  constructor
  · intro h n
    simpa [out.apSum_contract] using h n
  · intro h n
    simpa [out.apSum_contract] using h n

/-- Existence transport across the AP-sum bridge rule (≤). -/
theorem exists_natAbs_apSum_le_iff_exists_natAbs_apSumOffset_le (out : ReductionOutput f) (B : ℕ) :
    (∃ n : ℕ, Int.natAbs (apSum out.g out.d n) ≤ B) ↔
      (∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ B) := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (out.natAbs_apSum_le_iff_natAbs_apSumOffset_le (f := f) (B := B) (n := n)).1 hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (out.natAbs_apSum_le_iff_natAbs_apSumOffset_le (f := f) (B := B) (n := n)).2 hn⟩

/-- Existence transport across the AP-sum bridge rule (<). -/
theorem exists_natAbs_apSum_lt_iff_exists_natAbs_apSumOffset_lt (out : ReductionOutput f) (B : ℕ) :
    (∃ n : ℕ, Int.natAbs (apSum out.g out.d n) < B) ↔
      (∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) < B) := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (out.natAbs_apSum_lt_iff_natAbs_apSumOffset_lt (f := f) (B := B) (n := n)).1 hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (out.natAbs_apSum_lt_iff_natAbs_apSumOffset_lt (f := f) (B := B) (n := n)).2 hn⟩

/-- Transfer a boundedness context for `f` to a bound on `apSum out.g out.d`.

This is intentionally weak (a factor `2B`), but it is enough to make the interface usable
without committing to any deeper part of Tao’s reduction.
-/
theorem bound_apSum (ctx : Context f) (out : ReductionOutput f) (n : ℕ) :
    Int.natAbs (apSum out.g out.d n) ≤ ctx.B + ctx.B := by
  -- Reduce to the already-proved tail bound in `Context`.
  -- First rewrite `out.g` as a shift of `f`.
  have : Int.natAbs (apSum (fun k => f (k + out.m * out.d)) out.d n) ≤ ctx.B + ctx.B := by
    simpa using (ctx.bound_apSum_shift_add (f := f) (d := out.d) (m := out.m) (n := n) out.hd)
  simpa [out.g_eq] using this

/-- Transfer a boundedness context for `f` to a bound on the *offset* AP sum appearing in `out`.

This is just `Context.bound_apSumOffset`, specialized to the parameters bundled in `out`.
-/
theorem bound_apSumOffset (ctx : Context f) (out : ReductionOutput f) (n : ℕ) :
    Int.natAbs (apSumOffset f out.d out.m n) ≤ ctx.B + ctx.B := by
  simpa using (ctx.bound_apSumOffset (f := f) (d := out.d) (m := out.m) (n := n) out.hd)

/-- Discrepancy rewrite rule.

Note: this lemma is already provided earlier in this namespace as
`ReductionOutput.discrepancy_eq_discOffset` and is marked `[simp]`.

We avoid restating it here to keep the namespace free of duplicate declarations.
-/

/-- Strict-inequality transport across the discrepancy bridge rule. -/
theorem discrepancy_lt_iff_discOffset_lt (out : ReductionOutput f) (B : ℕ) (n : ℕ) :
    discrepancy out.g out.d n < B ↔ discOffset f out.d out.m n < B := by
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)]

/-- Strict-inequality transport across the discrepancy bridge rule (the reversed orientation). -/
theorem discOffset_lt_iff_discrepancy_lt (out : ReductionOutput f) (B : ℕ) (n : ℕ) :
    discOffset f out.d out.m n < B ↔ discrepancy out.g out.d n < B := by
  simpa using (out.discrepancy_lt_iff_discOffset_lt (f := f) (B := B) (n := n)).symm

/-- Strict-inequality transfer contract: a uniform bound on offset discrepancy transfers to `out.g`.

This is the strict-inequality analogue of the `contract_discrepancy_le` field.
-/
theorem contract_discrepancy_lt (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, discOffset f out.d out.m n < B) → ∀ n : ℕ, discrepancy out.g out.d n < B := by
  intro hB n
  -- Rewrite `discrepancy out.g` to the offset discrepancy of `f`.
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n

/-- Strict-inequality transfer contract (greater-than form).

This is just `contract_discrepancy_lt` with the inequality rewritten as `B < …`.

Downstream stages often produce “large discrepancy” conclusions in `>`-form.
-/
theorem contract_discrepancy_gt (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, discOffset f out.d out.m n > B) → ∀ n : ℕ, discrepancy out.g out.d n > B := by
  intro hB n
  -- Rewrite `discrepancy out.g` to the offset discrepancy of `f`.
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n

/-!
### Reverse transfer contracts

These are the “backward” forms of the bundled rewrite `discrepancy_eq_discOffset`: if a downstream
stage proves a uniform property about the reduced discrepancy family `discrepancy out.g out.d`, we
can immediately transport it back to the original offset-discrepancy family `discOffset f …`.
-/

/-- Reverse transfer contract (≤): from a uniform bound on `discrepancy out.g out.d` to one on
`discOffset f out.d out.m`.
-/
theorem contract_discOffset_le (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, discrepancy out.g out.d n ≤ B) → ∀ n : ℕ, discOffset f out.d out.m n ≤ B := by
  intro hB n
  -- Rewrite `discOffset` to `discrepancy out.g`.
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n

/-- Reverse transfer contract (<): strict version of `contract_discOffset_le`. -/
theorem contract_discOffset_lt (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, discrepancy out.g out.d n < B) → ∀ n : ℕ, discOffset f out.d out.m n < B := by
  intro hB n
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n

/-- Reverse transfer contract (>): strict `>` version of `contract_discOffset_lt`. -/
theorem contract_discOffset_gt (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, discrepancy out.g out.d n > B) → ∀ n : ℕ, discOffset f out.d out.m n > B := by
  intro hB n
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n

/-- Uniform strict-inequality transport across the discrepancy bridge rule. -/
theorem forall_discrepancy_lt_iff_forall_discOffset_lt (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, discrepancy out.g out.d n < B) ↔ (∀ n : ℕ, discOffset f out.d out.m n < B) := by
  constructor
  · intro h n
    exact (out.discrepancy_lt_iff_discOffset_lt (f := f) (B := B) (n := n)).1 (h n)
  · intro h n
    exact (out.discrepancy_lt_iff_discOffset_lt (f := f) (B := B) (n := n)).2 (h n)

/-- Transfer a boundedness context for `f` to a bound on `discrepancy out.g out.d`.

This is the discrepancy-level analogue of `ReductionOutput.bound_apSum`.
-/
theorem bound_discrepancy (ctx : Context f) (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n ≤ ctx.B + ctx.B := by
  -- Reduce to the already-proved shifted discrepancy bound in `Context`.
  have : discrepancy (fun k => f (k + out.m * out.d)) out.d n ≤ ctx.B + ctx.B := by
    exact ctx.bound_discrepancy_shift_add (f := f) (d := out.d) (m := out.m) (n := n) out.hd
  simpa [out.g_eq] using this

/-- Uniform version of `ReductionOutput.bound_discrepancy`. -/
theorem bound_discrepancy_forall (ctx : Context f) (out : ReductionOutput f) :
    ∀ n : ℕ, discrepancy out.g out.d n ≤ ctx.B + ctx.B := by
  intro n
  exact out.bound_discrepancy (f := f) ctx n

/-- If `f` has bounded discrepancy (globally), then the reduced sequence `out.g` has bounded
(discrepancy) along the fixed step `out.d`.

The bound degrades by at most a factor `2`.
-/
theorem boundedDiscrepancyAlong_of_boundedDiscrepancy (out : ReductionOutput f)
    (hb : BoundedDiscrepancy f) : BoundedDiscrepancyAlong out.g out.d := by
  classical
  let ctx : Context f := Context.ofBoundedDiscrepancy (f := f) hb
  refine ⟨ctx.B + ctx.B, ?_⟩
  intro n
  exact out.bound_discrepancy (f := f) ctx n

/-- A pointwise bound on the reduced discrepancy extracted directly from `hb : BoundedDiscrepancy f`.

This is a small convenience wrapper around `ReductionOutput.bound_discrepancy` and
`Context.ofBoundedDiscrepancy`, with the right-hand side expressed as `2 * B`.
-/
theorem bound_discrepancy_of_boundedDiscrepancy (out : ReductionOutput f) (hb : BoundedDiscrepancy f) :
    ∀ n : ℕ, discrepancy out.g out.d n ≤ 2 * (Context.ofBoundedDiscrepancy (f := f) hb).B := by
  classical
  intro n
  -- First get the additive `B + B` bound, then rewrite it as `2 * B`.
  have h := out.bound_discrepancy (f := f) (Context.ofBoundedDiscrepancy (f := f) hb) n
  simpa [two_mul] using h

/-- `BoundedDiscrepancyAlong` normal form for `out.g`, with an explicit `2 * B` witness.

This is occasionally more convenient than the additive witness `B + B` produced by
`boundedDiscrepancyAlong_of_boundedDiscrepancy`.
-/
theorem boundedDiscrepancyAlong_of_boundedDiscrepancy_two_mul (out : ReductionOutput f)
    (hb : BoundedDiscrepancy f) : BoundedDiscrepancyAlong out.g out.d := by
  classical
  refine ⟨2 * (Context.ofBoundedDiscrepancy (f := f) hb).B, ?_⟩
  intro n
  exact out.bound_discrepancy_of_boundedDiscrepancy (f := f) hb n

/-- A bound on `f`'s discrepancy implies a uniform bound on the offset discrepancy bundled by `out`.

This is the `discOffset`-level analogue of `boundedDiscrepancyAlong_of_boundedDiscrepancy`.
-/
theorem boundedDiscOffset_of_boundedDiscrepancy (out : ReductionOutput f)
    (hb : BoundedDiscrepancy f) : ∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B := by
  classical
  let ctx : Context f := Context.ofBoundedDiscrepancy (f := f) hb
  refine ⟨ctx.B + ctx.B, ?_⟩
  intro n
  exact ctx.bound_discOffset (f := f) (d := out.d) (m := out.m) (n := n) out.hd

/-!
### `discOffset` bounds vs fixed-step bounds on the reduced sequence

`ReductionOutput` is designed so that reasoning about the reduced sequence `out.g` (at the fixed
step `out.d`) is equivalent to reasoning about the corresponding offset sums/discrepancies of the
original sequence `f`.

The next few lemmas make this equivalence explicit in the “boundedness” normal forms that show up
repeatedly throughout the Tao2015 pipeline.
-/

/-- A uniform bound on the offset discrepancy of `f` is the same as bounded discrepancy of `out.g`
along the fixed step `out.d`.

This is a basic “consumer lemma”: it lets later stages choose whichever normal form is more
convenient.
-/
theorem boundedDiscOffset_iff_boundedDiscrepancyAlong (out : ReductionOutput f) :
    (∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B) ↔ BoundedDiscrepancyAlong out.g out.d := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- rewrite `discrepancy out.g` to `discOffset f`.
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- rewrite `discOffset f` to `discrepancy out.g`.
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n

/-- Negated form of `boundedDiscOffset_iff_boundedDiscrepancyAlong`. -/
theorem not_boundedDiscOffset_iff_not_boundedDiscrepancyAlong (out : ReductionOutput f) :
    (¬ ∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B) ↔ ¬ BoundedDiscrepancyAlong out.g out.d := by
  simpa [out.boundedDiscOffset_iff_boundedDiscrepancyAlong (f := f)]

/-- Unbounded offset discrepancy is equivalent to the standard `∀ B, ∃ n, B < ...` normal form.

This is just `BoundedDiscOffset.not_iff_forall_exists_gt` specialized to the parameters bundled in
`out`, and with the definitional expansion of `BoundedDiscOffset`.
-/
theorem not_exists_bound_discOffset_iff_forall_exists_lt (out : ReductionOutput f) :
    (¬ ∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B) ↔
      (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) := by
  -- `BoundedDiscOffset f d m` is definitionally `∃ B, ∀ n, discOffset f d m n ≤ B`.
  simpa [BoundedDiscOffset] using
    (BoundedDiscOffset.not_iff_forall_exists_gt (f := f) (d := out.d) (m := out.m))

/-- Unbounded discrepancy along the fixed step `out.d` is equivalent to the standard
`∀ B, ∃ n, B < discrepancy ...` normal form.

This is a consumer-friendly restatement of
`Tao2015.not_boundedDiscrepancyAlong_iff_forall_exists_discrepancy_gt`.
-/
theorem not_boundedDiscrepancyAlong_iff_forall_exists_lt_discrepancy (out : ReductionOutput f) :
    (¬ BoundedDiscrepancyAlong out.g out.d) ↔ (∀ B : ℕ, ∃ n : ℕ, B < discrepancy out.g out.d n) := by
  -- The library lemma uses the “`B < discrepancy`” orientation already.
  simpa using
    (Tao2015.not_boundedDiscrepancyAlong_iff_forall_exists_discrepancy_gt (g := out.g) (d := out.d))

/-- Unboundedness normal forms are compatible with the stage-1 bridge `discrepancy = discOffset`.

In practice this is what later contradiction stages want: it lets you freely swap between
witnesses for unbounded discrepancy of the reduced sequence and unbounded offset discrepancy of
the original sequence.
-/
theorem not_boundedDiscrepancyAlong_iff_forall_exists_lt_discOffset (out : ReductionOutput f) :
    (¬ BoundedDiscrepancyAlong out.g out.d) ↔ (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) := by
  -- Start from the discrepancy witness normal form, then rewrite the target using the bridge.
  constructor
  · intro h B
    rcases (out.not_boundedDiscrepancyAlong_iff_forall_exists_lt_discrepancy (f := f)).1 h B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hn
  · intro h
    -- Convert to discrepancy witnesses by rewriting `discOffset` back to `discrepancy`.
    refine (out.not_boundedDiscrepancyAlong_iff_forall_exists_lt_discrepancy (f := f)).2 ?_
    intro B
    rcases h B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hn

/-- If `out.g` is bounded along `out.d`, then the bundled offset discrepancy family of `f` is
bounded (with the same constant).

This is just the forward implication of `boundedDiscOffset_iff_boundedDiscrepancyAlong` as a lemma
with a direct statement.
-/
theorem boundedDiscOffset_of_boundedDiscrepancyAlong (out : ReductionOutput f)
    (hb : BoundedDiscrepancyAlong out.g out.d) :
    ∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B :=
  (out.boundedDiscOffset_iff_boundedDiscrepancyAlong (f := f)).2 hb

/-- If the bundled offset discrepancy family of `f` is bounded, then so is the reduced sequence
`out.g` along the fixed step `out.d`.

This is just the reverse implication of `boundedDiscOffset_iff_boundedDiscrepancyAlong` as a lemma
with a direct statement.
-/
theorem boundedDiscrepancyAlong_of_boundedDiscOffset (out : ReductionOutput f)
    (hb : ∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B) :
    BoundedDiscrepancyAlong out.g out.d :=
  (out.boundedDiscOffset_iff_boundedDiscrepancyAlong (f := f)).1 hb

/-- Fixed-step discrepancy transfer (in `natAbs` form).

This is the most direct consumer lemma for our new predicate `HasDiscrepancyAtLeastAlong`.
-/
theorem hasDiscrepancyAtLeastAlong_iff (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔
      (∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > C) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- rewrite `apSum out.g` to `apSumOffset f`
    simpa [out.apSum_contract] using hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- rewrite back using the same bridge rule
    simpa [out.apSum_contract] using hn

/-- Same transfer statement, but phrased using the `discOffset` wrapper. -/
theorem hasDiscrepancyAtLeastAlong_iff_discOffset (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔ (∃ n : ℕ, discOffset f out.d out.m n > C) := by
  -- `discOffset` is definitional wrapper around `Int.natAbs (apSumOffset ...)`.
  simpa [HasDiscrepancyAtLeastAlong, discOffset] using (out.hasDiscrepancyAtLeastAlong_iff (f := f) (C := C))

/-- Unfold `HasDiscrepancyAtLeastAlong` for the reduced sequence, phrased in terms of `discrepancy`. -/
theorem hasDiscrepancyAtLeastAlong_iff_exists_discrepancy_gt (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔ (∃ n : ℕ, discrepancy out.g out.d n > C) := by
  -- This is just the definitional wrapper lemma specialized to `(out.g,out.d)`.
  simpa using (HasDiscrepancyAtLeastAlong.iff_exists_discrepancy_gt (f := out.g) (d := out.d) (C := C))

/-- “Consumer form” of `hasDiscrepancyAtLeastAlong_iff_discOffset`, with the inequality oriented as `C < ...`. -/
theorem hasDiscrepancyAtLeastAlong_iff_exists_discOffset_lt (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔ (∃ n : ℕ, C < discOffset f out.d out.m n) := by
  -- This avoids having to constantly rewrite `C < ...` to `... > C` downstream.
  -- Note: `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using (out.hasDiscrepancyAtLeastAlong_iff_discOffset (f := f) (C := C))

/-!
### Uniform unboundedness packaging

Downstream steps often produce a statement of the form

`∀ C, HasDiscrepancyAtLeastAlong out.g out.d C`.

It is convenient to immediately translate this into either a `¬ BoundedDiscrepancyAlong` statement
(for `out.g`) or into the corresponding uniform family of `discOffset` witnesses for the original
sequence `f`.
-/

/-- Unboundedness along the fixed step `out.d`, in terms of the reduced sequence `out.g`. -/
theorem forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscrepancyAlong (out : ReductionOutput f) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) ↔ ¬ BoundedDiscrepancyAlong out.g out.d := by
  simpa using
    (HasDiscrepancyAtLeastAlong.forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscrepancyAlong
      (g := out.g) (d := out.d))

/-- Translate uniform large-discrepancy-along-`out.d` for `out.g` into uniform `discOffset` witnesses
for `f` (greater-than orientation). -/
theorem forall_hasDiscrepancyAtLeastAlong_iff_forall_exists_discOffset_gt (out : ReductionOutput f) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) ↔
      (∀ C : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > C) := by
  constructor
  · intro h C
    -- Convert the `HasDiscrepancyAtLeastAlong` witness for `out.g` to a `discOffset` witness for `f`.
    simpa using (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) (C := C)).1 (h C)
  · intro h C
    rcases h C with ⟨n, hn⟩
    exact (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) (C := C)).2 ⟨n, hn⟩

/-- Same as `forall_hasDiscrepancyAtLeastAlong_iff_forall_exists_discOffset_gt`, but with the
inequality oriented as `C < ...`. -/
theorem forall_hasDiscrepancyAtLeastAlong_iff_forall_exists_discOffset_lt (out : ReductionOutput f) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) ↔
      (∀ C : ℕ, ∃ n : ℕ, C < discOffset f out.d out.m n) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using (out.forall_hasDiscrepancyAtLeastAlong_iff_forall_exists_discOffset_gt (f := f))

/-- Convenience: if you have uniform `discOffset` witnesses for `f`, then the reduced sequence `out.g`
is unbounded along `out.d`. -/
theorem not_boundedDiscrepancyAlong_of_forall_exists_discOffset_gt (out : ReductionOutput f) :
    (∀ C : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > C) → ¬ BoundedDiscrepancyAlong out.g out.d := by
  intro h
  -- Translate uniform `discOffset` witnesses back to uniform `HasDiscrepancyAtLeastAlong` witnesses.
  have : ∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C :=
    (out.forall_hasDiscrepancyAtLeastAlong_iff_forall_exists_discOffset_gt (f := f)).2 h
  -- Then use the standard equivalence to `¬ BoundedDiscrepancyAlong`.
  exact (out.forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscrepancyAlong (f := f)).1 this

/-- Converse convenience: if `out.g` is unbounded along `out.d`, then we get uniform `discOffset`
witnesses for `f`. -/
theorem forall_exists_discOffset_gt_of_not_boundedDiscrepancyAlong (out : ReductionOutput f) :
    (¬ BoundedDiscrepancyAlong out.g out.d) → (∀ C : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > C) := by
  intro h
  have : ∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C :=
    (out.forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscrepancyAlong (f := f)).2 h
  exact (out.forall_hasDiscrepancyAtLeastAlong_iff_forall_exists_discOffset_gt (f := f)).1 this

/-- `<`-oriented version of `not_boundedDiscrepancyAlong_of_forall_exists_discOffset_gt`. -/
theorem not_boundedDiscrepancyAlong_of_forall_exists_discOffset_lt (out : ReductionOutput f) :
    (∀ C : ℕ, ∃ n : ℕ, C < discOffset f out.d out.m n) → ¬ BoundedDiscrepancyAlong out.g out.d := by
  intro h
  have : ∀ C : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > C := by
    intro C
    rcases h C with ⟨n, hn⟩
    exact ⟨n, by simpa [gt_iff_lt] using hn⟩
  exact out.not_boundedDiscrepancyAlong_of_forall_exists_discOffset_gt (f := f) this

/-- `<`-oriented version of `forall_exists_discOffset_gt_of_not_boundedDiscrepancyAlong`. -/
theorem forall_exists_discOffset_lt_of_not_boundedDiscrepancyAlong (out : ReductionOutput f) :
    (¬ BoundedDiscrepancyAlong out.g out.d) → (∀ C : ℕ, ∃ n : ℕ, C < discOffset f out.d out.m n) := by
  intro h
  have hgt : ∀ C : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > C :=
    out.forall_exists_discOffset_gt_of_not_boundedDiscrepancyAlong (f := f) h
  intro C
  rcases hgt C with ⟨n, hn⟩
  exact ⟨n, by simpa [gt_iff_lt] using hn⟩

/-!
### Shifting the reduced sequence

A common pattern in multi-stage reductions is to shift the already-reduced sequence `out.g` by an
additional multiple `m₂*out.d`.  This corresponds to increasing the bundled offset parameter from
`out.m` to `out.m + m₂`.

The next lemma packages that rewrite at the level of the pipeline-friendly predicate
`HasDiscrepancyAtLeastAlong`.
-/

/-- Fixed-step discrepancy for an additional shift of `out.g` is exactly a `discOffset` witness for
`f` with the *bundled* offset `out.m + m₂`.

This is a convenience lemma combining `out.g_eq` with
`hasDiscrepancyAtLeastAlong_shift_add_mul_iff_exists_discOffset_gt`.
-/
theorem hasDiscrepancyAtLeastAlong_shiftRight_iff_exists_discOffset_gt
    (out : ReductionOutput f) (m₂ C : ℕ) :
    HasDiscrepancyAtLeastAlong (fun k => out.g (k + m₂ * out.d)) out.d C ↔
      (∃ n : ℕ, discOffset f out.d (out.m + m₂) n > C) := by
  -- Rewrite the shifted reduced sequence as a single shift of `f`.
  have hcongr :
      HasDiscrepancyAtLeastAlong (fun k => out.g (k + m₂ * out.d)) out.d C ↔
        HasDiscrepancyAtLeastAlong (fun k => f (k + (out.m + m₂) * out.d)) out.d C := by
    -- `out.g k = f (k + out.m*out.d)`.
    -- So `out.g (k + m₂*out.d) = f (k + (out.m+m₂)*out.d)`.
    -- (Associativity/commutativity of addition handles the rearrangement.)
    simpa [out.g_eq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.add_mul, Nat.mul_add,
      Nat.mul_assoc]
  -- Now apply the generic rewrite lemma for shifts of `f`.
  simpa using
    (hcongr.trans
      (Tao2015.hasDiscrepancyAtLeastAlong_shift_add_mul_iff_exists_discOffset_gt
        (f := f) (d := out.d) (m := out.m + m₂) (C := C)))

/-- Fixed-step discrepancy for an additional shift of `out.g` can be phrased purely using
`discOffset out.g`.

This is just `hasDiscrepancyAtLeastAlong_shift_add_mul_iff_exists_discOffset_gt` specialized to
`out.g`.
-/
theorem hasDiscrepancyAtLeastAlong_shiftRight_iff_exists_discOffset_g_gt
    (out : ReductionOutput f) (m₂ C : ℕ) :
    HasDiscrepancyAtLeastAlong (fun k => out.g (k + m₂ * out.d)) out.d C ↔
      (∃ n : ℕ, discOffset out.g out.d m₂ n > C) := by
  simpa using
    (Tao2015.hasDiscrepancyAtLeastAlong_shift_add_mul_iff_exists_discOffset_gt
      (f := out.g) (d := out.d) (m := m₂) (C := C))

/-- Variant of `hasDiscrepancyAtLeastAlong_shiftRight_iff_exists_discOffset_g_gt` with the
inequality oriented as `C < ...`.
-/
theorem hasDiscrepancyAtLeastAlong_shiftRight_iff_exists_discOffset_g_lt
    (out : ReductionOutput f) (m₂ C : ℕ) :
    HasDiscrepancyAtLeastAlong (fun k => out.g (k + m₂ * out.d)) out.d C ↔
      (∃ n : ℕ, C < discOffset out.g out.d m₂ n) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using
    (out.hasDiscrepancyAtLeastAlong_shiftRight_iff_exists_discOffset_g_gt (f := f) (m₂ := m₂) (C := C))

/-- Variant of `hasDiscrepancyAtLeastAlong_shiftRight_iff_exists_discOffset_gt` with the inequality
oriented as `C < ...`.

This avoids frequent rewriting between `... > C` and `C < ...` in downstream reductions.
-/
theorem hasDiscrepancyAtLeastAlong_shiftRight_iff_exists_discOffset_lt
    (out : ReductionOutput f) (m₂ C : ℕ) :
    HasDiscrepancyAtLeastAlong (fun k => out.g (k + m₂ * out.d)) out.d C ↔
      (∃ n : ℕ, C < discOffset f out.d (out.m + m₂) n) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using
    (out.hasDiscrepancyAtLeastAlong_shiftRight_iff_exists_discOffset_gt (f := f) (m₂ := m₂) (C := C))

/-!
### Shifting a reduction output

Many stages in the Tao pipeline shift the already-reduced sequence `out.g` by an additional
multiple `m₂*out.d`.  This just increases the bundled offset from `out.m` to `out.m + m₂`.

The next definition packages this as a new `ReductionOutput f`.
-/

/-- Shift the reduced sequence `out.g` by an additional multiple `m₂*out.d`.

The resulting reduction output has:
- the same common difference `d := out.d`
- the bundled offset `m := out.m + m₂`
- the reduced sequence `g k := out.g (k + m₂*out.d)`.

It fills the bridge rule and discrepancy-transfer contract automatically via `mkShift`.
-/
noncomputable def shiftRight₀ (out : ReductionOutput f) (m₂ : ℕ) : ReductionOutput f := by
  classical
  -- Define the additionally-shifted reduced sequence.
  let g' : ℕ → ℤ := fun k => out.g (k + m₂ * out.d)
  have hg' : IsSignSequence g' :=
    Tao2015.IsSignSequence.shift_add_mul (f := out.g) out.hg m₂ out.d
  -- Identify `g'` as a single shift of the original `f`.
  have hg'Eq : g' = fun k => f (k + (out.m + m₂) * out.d) := by
    funext k
    -- `out.g (k + m₂*out.d) = f ((k + m₂*out.d) + out.m*out.d)`.
    -- Reassociate to `k + (out.m+m₂)*out.d`.
    simp [g', out.g_eq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
  -- Package as a reduction output with bundled offset `out.m + m₂`.
  exact
    ReductionOutput.mkShift (f := f) (d := out.d) (m := out.m + m₂) (hd := out.hd)
      (g := g') (hg := hg') (hgEq := hg'Eq)

@[simp] theorem shiftRight₀_d (out : ReductionOutput f) (m₂ : ℕ) : (out.shiftRight₀ (f := f) m₂).d = out.d :=
  rfl

@[simp] theorem shiftRight₀_m (out : ReductionOutput f) (m₂ : ℕ) : (out.shiftRight₀ (f := f) m₂).m = out.m + m₂ :=
  rfl

@[simp] theorem shiftRight₀_g_apply (out : ReductionOutput f) (m₂ k : ℕ) :
    (out.shiftRight₀ (f := f) m₂).g k = out.g (k + m₂ * out.d) := by
  rfl

/-- Shifting by `0` does not change the underlying reduced sequence (extensional form). -/
@[simp] theorem shiftRight₀_zero_g (out : ReductionOutput f) :
    (out.shiftRight₀ (f := f) 0).g = out.g := by
  funext k
  simp

/-- Specialized rewrite: `shiftRight₀ 0` does not change AP sums of the reduced sequence. -/
@[simp] theorem shiftRight₀_zero_apSum (out : ReductionOutput f) (n : ℕ) :
    apSum (out.shiftRight₀ (f := f) 0).g out.d n = apSum out.g out.d n := by
  simp [shiftRight₀_zero_g]

/-- Specialized rewrite: `shiftRight₀ 0` does not change discrepancies of the reduced sequence. -/
@[simp] theorem shiftRight₀_zero_discrepancy (out : ReductionOutput f) (n : ℕ) :
    discrepancy (out.shiftRight₀ (f := f) 0).g out.d n = discrepancy out.g out.d n := by
  simp [shiftRight₀_zero_g]

/-!
### Iterating `shiftRight₀`

Many downstream reductions shift the reduced sequence multiple times.
The next lemmas record the algebra of these shifts at the level of the bundled parameters and the
underlying reduced sequence.
-/

@[simp] theorem shiftRight₀_shiftRight₀_d (out : ReductionOutput f) (m₂ m₃ : ℕ) :
    ((out.shiftRight₀ (f := f) m₂).shiftRight₀ (f := f) m₃).d = out.d := by
  rfl

@[simp] theorem shiftRight₀_shiftRight₀_m (out : ReductionOutput f) (m₂ m₃ : ℕ) :
    ((out.shiftRight₀ (f := f) m₂).shiftRight₀ (f := f) m₃).m = out.m + m₂ + m₃ := by
  rfl

@[simp] theorem shiftRight₀_shiftRight₀_g_apply (out : ReductionOutput f) (m₂ m₃ k : ℕ) :
    ((out.shiftRight₀ (f := f) m₂).shiftRight₀ (f := f) m₃).g k =
      out.g (k + (m₂ + m₃) * out.d) := by
  -- Unfold the two shifts and reassociate the accumulated offset.
  simp [ReductionOutput.shiftRight₀, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.add_mul, Nat.mul_add, Nat.mul_assoc]

/-- Convenience rewrite: iterated shifting corresponds to increasing the bundled offset by
`m₂ + m₃` in one go (discrepancy form).
-/
theorem shiftRight₀_shiftRight₀_discrepancy_eq_discOffset (out : ReductionOutput f) (m₂ m₃ n : ℕ) :
    discrepancy ((out.shiftRight₀ (f := f) m₂).shiftRight₀ (f := f) m₃).g out.d n =
      discOffset f out.d (out.m + m₂ + m₃) n := by
  -- Apply the generic `shiftRight₀` discrepancy lemma twice.
  simpa [Nat.add_assoc] using
    (ReductionOutput.shiftRight₀_discrepancy_eq_discOffset_add (f := f)
      (out := out.shiftRight₀ (f := f) m₂) (m₂ := m₃) (n := n))

/-- Convenience rewrite: iterated shifting corresponds to increasing the bundled offset by
`m₂ + m₃` in one go (AP-sum form).
-/
theorem shiftRight₀_shiftRight₀_apSum_eq_apSumOffset (out : ReductionOutput f) (m₂ m₃ n : ℕ) :
    apSum ((out.shiftRight₀ (f := f) m₂).shiftRight₀ (f := f) m₃).g out.d n =
      apSumOffset f out.d (out.m + m₂ + m₃) n := by
  -- Apply the generic `shiftRight₀` AP-sum lemma twice.
  simpa [Nat.add_assoc] using
    (ReductionOutput.shiftRight₀_apSum_eq_apSumOffset_add (f := f)
      (out := out.shiftRight₀ (f := f) m₂) (m₂ := m₃) (n := n))

/-- Reverse orientation of `shiftRight₀_shiftRight₀_apSum_eq_apSumOffset`. -/
theorem apSumOffset_eq_shiftRight₀_shiftRight₀_apSum (out : ReductionOutput f) (m₂ m₃ n : ℕ) :
    apSumOffset f out.d (out.m + m₂ + m₃) n =
      apSum ((out.shiftRight₀ (f := f) m₂).shiftRight₀ (f := f) m₃).g out.d n := by
  simpa using (out.shiftRight₀_shiftRight₀_apSum_eq_apSumOffset (f := f) (m₂ := m₂) (m₃ := m₃) (n := n)).symm

/-- `apSum` rewrite rule for `shiftRight₀`: it is an offset AP sum of `f` with the bundled offset
`out.m + m₂`.

This is mostly a convenience lemma: it avoids having to remember the exact `.m` field of the
shifted output.
-/
@[simp] theorem shiftRight₀_apSum_eq_apSumOffset_add (out : ReductionOutput f) (m₂ n : ℕ) :
    apSum (out.shiftRight₀ (f := f) m₂).g out.d n = apSumOffset f out.d (out.m + m₂) n := by
  -- This is the generic `apSum_eq_apSumOffset` lemma specialized to the shifted output.
  simpa using (ReductionOutput.apSum_eq_apSumOffset (f := f) (out := out.shiftRight₀ (f := f) m₂) (n := n))

/-- Discrepancy rewrite rule for `shiftRight₀`: it is an offset discrepancy of `f` with the bundled
offset `out.m + m₂`.
-/
@[simp] theorem shiftRight₀_discrepancy_eq_discOffset_add (out : ReductionOutput f) (m₂ n : ℕ) :
    discrepancy (out.shiftRight₀ (f := f) m₂).g out.d n = discOffset f out.d (out.m + m₂) n := by
  simpa using (ReductionOutput.discrepancy_eq_discOffset (f := f)
    (out := out.shiftRight₀ (f := f) m₂) (n := n))

/-- `apSum` rewrite rule for `shiftRight₀`, phrased as an offset AP sum of the *already reduced*
sequence `out.g`.
-/
theorem shiftRight₀_apSum_eq_apSumOffset_g (out : ReductionOutput f) (m₂ n : ℕ) :
    apSum (out.shiftRight₀ (f := f) m₂).g out.d n = apSumOffset out.g out.d m₂ n := by
  -- Rewrite to an offset sum of `f` with bundled offset, then peel the original offset `out.m`.
  simpa [out.apSumOffset_add_eq_apSumOffset_g (f := f) (m₂ := m₂) (n := n)] using
    (out.shiftRight₀_apSum_eq_apSumOffset_add (f := f) (m₂ := m₂) (n := n))

/-- Discrepancy rewrite rule for `shiftRight₀`, phrased as an offset discrepancy of `out.g`. -/
theorem shiftRight₀_discrepancy_eq_discOffset_g (out : ReductionOutput f) (m₂ n : ℕ) :
    discrepancy (out.shiftRight₀ (f := f) m₂).g out.d n = discOffset out.g out.d m₂ n := by
  -- Convert both sides to `discOffset f` using the bundled-offset rewrite, then peel.
  simpa [out.discOffset_add_eq_discOffset_g (f := f) (m₂ := m₂) (n := n)] using
    (out.shiftRight₀_discrepancy_eq_discOffset_add (f := f) (m₂ := m₂) (n := n))

/-!
### Fixed-step discrepancy witnesses for `shiftRight₀`

These are small “consumer lemmas” that specialize the generic
`ReductionOutput.hasDiscrepancyAtLeastAlong_iff_discOffset` transfer statement to the
shifted output `out.shiftRight₀ m₂`.

They avoid having to remember that the bundled offset parameter for the shifted output is
`out.m + m₂`.
-/

/-- Fixed-step discrepancy for `out.shiftRight₀ m₂` is exactly a bundled-offset `discOffset` witness
for `f` with offset `out.m + m₂`.
-/
theorem shiftRight₀_hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt
    (out : ReductionOutput f) (m₂ C : ℕ) :
    HasDiscrepancyAtLeastAlong (out.shiftRight₀ (f := f) m₂).g out.d C ↔
      (∃ n : ℕ, discOffset f out.d (out.m + m₂) n > C) := by
  -- This is the generic transfer lemma for the shifted reduction output.
  simpa using
    (ReductionOutput.hasDiscrepancyAtLeastAlong_iff_discOffset
      (f := f) (out := out.shiftRight₀ (f := f) m₂) (C := C))

/-- `C < discOffset ...` version of `shiftRight₀_hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt`. -/
theorem shiftRight₀_hasDiscrepancyAtLeastAlong_iff_exists_discOffset_lt
    (out : ReductionOutput f) (m₂ C : ℕ) :
    HasDiscrepancyAtLeastAlong (out.shiftRight₀ (f := f) m₂).g out.d C ↔
      (∃ n : ℕ, C < discOffset f out.d (out.m + m₂) n) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using
    (out.shiftRight₀_hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt (f := f) (m₂ := m₂) (C := C))

/-- Fixed-step discrepancy for `out.shiftRight₀ m₂` is exactly an offset discrepancy witness for the
already-reduced sequence `out.g`.
-/
theorem shiftRight₀_hasDiscrepancyAtLeastAlong_iff_exists_discOffset_g_gt
    (out : ReductionOutput f) (m₂ C : ℕ) :
    HasDiscrepancyAtLeastAlong (out.shiftRight₀ (f := f) m₂).g out.d C ↔
      (∃ n : ℕ, discOffset out.g out.d m₂ n > C) := by
  -- Combine the generic transfer lemma for `out.shiftRight₀ m₂` with the discrepancy rewrite rule
  -- `shiftRight₀_discrepancy_eq_discOffset_g`.
  constructor
  · intro h
    rcases (HasDiscrepancyAtLeastAlong.iff_exists_discrepancy_gt
      (f := (out.shiftRight₀ (f := f) m₂).g) (d := out.d) (C := C)).1 h with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.shiftRight₀_discrepancy_eq_discOffset_g (f := f) (m₂ := m₂) (n := n)] using hn
  · rintro ⟨n, hn⟩
    have : discrepancy (out.shiftRight₀ (f := f) m₂).g out.d n > C := by
      simpa [out.shiftRight₀_discrepancy_eq_discOffset_g (f := f) (m₂ := m₂) (n := n)] using hn
    exact (HasDiscrepancyAtLeastAlong.iff_exists_discrepancy_gt
      (f := (out.shiftRight₀ (f := f) m₂).g) (d := out.d) (C := C)).2 ⟨n, this⟩

/-- `C < discOffset ...` version of `shiftRight₀_hasDiscrepancyAtLeastAlong_iff_exists_discOffset_g_gt`. -/
theorem shiftRight₀_hasDiscrepancyAtLeastAlong_iff_exists_discOffset_g_lt
    (out : ReductionOutput f) (m₂ C : ℕ) :
    HasDiscrepancyAtLeastAlong (out.shiftRight₀ (f := f) m₂).g out.d C ↔
      (∃ n : ℕ, C < discOffset out.g out.d m₂ n) := by
  simpa [gt_iff_lt] using
    (out.shiftRight₀_hasDiscrepancyAtLeastAlong_iff_exists_discOffset_g_gt (f := f) (m₂ := m₂) (C := C))

/-- A fixed-step discrepancy witness for `out.g` yields a standard discrepancy witness.

This is the bridge from our pipeline-friendly predicate `HasDiscrepancyAtLeastAlong` to the
ambient `HasDiscrepancyAtLeast` predicate used in surface statements.
-/
theorem hasDiscrepancyAtLeast_of_hasDiscrepancyAtLeastAlong (out : ReductionOutput f) (C : ℕ)
    (h : HasDiscrepancyAtLeastAlong out.g out.d C) :
    HasDiscrepancyAtLeast out.g C := by
  exact HasDiscrepancyAtLeastAlong.toHasDiscrepancyAtLeast (f := out.g) (d := out.d) (C := C) out.hd h

/-- A convenient forward direction: a large discrepancy witness for `out.g` produces a large
`discOffset` witness for `f`. -/
theorem exists_discOffset_gt_of_hasDiscrepancyAtLeastAlong (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C → (∃ n : ℕ, discOffset f out.d out.m n > C) := by
  intro h
  exact (out.hasDiscrepancyAtLeastAlong_iff_discOffset (f := f) (C := C)).1 h

/-- A convenient backward direction: a large `discOffset` witness for `f` produces a large
fixed-step discrepancy witness for `out.g`. -/
theorem hasDiscrepancyAtLeastAlong_of_exists_discOffset_gt (out : ReductionOutput f) (C : ℕ) :
    (∃ n : ℕ, discOffset f out.d out.m n > C) → HasDiscrepancyAtLeastAlong out.g out.d C := by
  intro h
  exact (out.hasDiscrepancyAtLeastAlong_iff_discOffset (f := f) (C := C)).2 h

/-- `C < discOffset ...` form of `exists_discOffset_gt_of_hasDiscrepancyAtLeastAlong`. -/
theorem exists_discOffset_lt_of_hasDiscrepancyAtLeastAlong (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C → (∃ n : ℕ, C < discOffset f out.d out.m n) := by
  intro h
  exact (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_lt (f := f) (C := C)).1 h

/-- `C < discOffset ...` form of `hasDiscrepancyAtLeastAlong_of_exists_discOffset_gt`. -/
theorem hasDiscrepancyAtLeastAlong_of_exists_discOffset_lt (out : ReductionOutput f) (C : ℕ) :
    (∃ n : ℕ, C < discOffset f out.d out.m n) → HasDiscrepancyAtLeastAlong out.g out.d C := by
  intro h
  exact (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_lt (f := f) (C := C)).2 h

/-- A `discOffset` witness for `f` yields a standard discrepancy witness for the reduced sequence.

This is the most common “pipeline hop” in later stages: reductions naturally produce offset-sum
witnesses for the original sequence, while contradiction stages tend to consume the ambient
`HasDiscrepancyAtLeast` predicate.
-/
theorem hasDiscrepancyAtLeast_of_exists_discOffset_gt (out : ReductionOutput f) (C : ℕ)
    (h : ∃ n : ℕ, discOffset f out.d out.m n > C) :
    HasDiscrepancyAtLeast out.g C := by
  have halong : HasDiscrepancyAtLeastAlong out.g out.d C :=
    out.hasDiscrepancyAtLeastAlong_of_exists_discOffset_gt (f := f) (C := C) h
  exact out.hasDiscrepancyAtLeast_of_hasDiscrepancyAtLeastAlong (f := f) (C := C) halong

/-- The same rewrite rule, but oriented in the other direction. -/
theorem discOffset_eq_discrepancy (out : ReductionOutput f) (n : ℕ) :
    discOffset f out.d out.m n = discrepancy out.g out.d n := by
  simpa using (out.discrepancy_eq_discOffset (f := f) (n := n)).symm

/-- Pointwise transfer lemma (≤): bounding the discrepancy of `out.g` at `n` is equivalent to
bounding the corresponding offset discrepancy of `f` at `n`. -/
theorem discrepancy_le_iff_discOffset_le (out : ReductionOutput f) (B : ℕ) (n : ℕ) :
    discrepancy out.g out.d n ≤ B ↔ discOffset f out.d out.m n ≤ B := by
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)]

/-- Pointwise transfer lemma (<): strict version of `discrepancy_le_iff_discOffset_le`. -/
theorem discrepancy_lt_iff_discOffset_lt (out : ReductionOutput f) (B : ℕ) (n : ℕ) :
    discrepancy out.g out.d n < B ↔ discOffset f out.d out.m n < B := by
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)]

/-- Symmetric pointwise transfer lemma (≤), oriented from offset discrepancy to discrepancy. -/
theorem discOffset_le_iff_discrepancy_le (out : ReductionOutput f) (B : ℕ) (n : ℕ) :
    discOffset f out.d out.m n ≤ B ↔ discrepancy out.g out.d n ≤ B := by
  simpa using (out.discrepancy_le_iff_discOffset_le (f := f) (B := B) (n := n)).symm

/-- A convenient “forward” transfer lemma, derived from the rewrite rule.

This is logically redundant with `discrepancy_eq_discOffset`, but it is the most common way
consumers will use the interface: reduce a uniform bound on offset discrepancies of `f` to a
uniform bound on discrepancies of `out.g`.
-/
theorem discrepancy_le_of_forall_discOffset_le (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n, discOffset f out.d out.m n ≤ B) :
    ∀ n, discrepancy out.g out.d n ≤ B := by
  intro n
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n

/-- A convenient “backward” transfer lemma, derived from the rewrite rule. -/
theorem discOffset_le_of_forall_discrepancy_le (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n, discrepancy out.g out.d n ≤ B) :
    ∀ n, discOffset f out.d out.m n ≤ B := by
  intro n
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n

/-- Uniform transfer lemma (≤): bounding all offset discrepancies of `f` is equivalent to bounding
all discrepancies of the reduced sequence `out.g` (along `out.d`). -/
theorem forall_discOffset_le_iff_forall_discrepancy_le (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, discOffset f out.d out.m n ≤ B) ↔ (∀ n : ℕ, discrepancy out.g out.d n ≤ B) := by
  constructor
  · intro h
    exact out.discrepancy_le_of_forall_discOffset_le (f := f) (B := B) h
  · intro h
    exact out.discOffset_le_of_forall_discrepancy_le (f := f) (B := B) h

/-- Track-C convenience: the same equivalence, but with the sides swapped.

Some pipeline stages naturally produce a bound for the reduced sequence `out.g`; others naturally
produce a bound for the offset family `discOffset f out.d out.m`.
This lemma avoids repeated `Iff.symm` / `Iff.comm` gymnastics at call sites.
-/
theorem trackC_forall_discrepancy_le_iff_forall_discOffset_le (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, discrepancy out.g out.d n ≤ B) ↔ (∀ n : ℕ, discOffset f out.d out.m n ≤ B) := by
  simpa [Iff.comm] using (out.forall_discOffset_le_iff_forall_discrepancy_le (f := f) (B := B))

/-- Uniform transfer lemma (<): strict version of `forall_discOffset_le_iff_forall_discrepancy_le`. -/
theorem forall_discOffset_lt_iff_forall_discrepancy_lt (out : ReductionOutput f) (B : ℕ) :
    (∀ n : ℕ, discOffset f out.d out.m n < B) ↔ (∀ n : ℕ, discrepancy out.g out.d n < B) := by
  constructor
  · intro h n
    -- rewrite `discrepancy` to `discOffset` and apply the hypothesis
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using h n
  · intro h n
    -- rewrite `discOffset` to `discrepancy` and apply the hypothesis
    simpa [out.discOffset_eq_discrepancy (f := f) (n := n)] using h n

/-- The `ReductionOutput` field `contract_discrepancy_le` is implied by the rewrite rule.

We keep the field for now (it documents intent), but downstream code can rely on this lemma
instead, which will still be available if the structure is simplified later.
-/
theorem contract_discrepancy_le_derived (out : ReductionOutput f) (B : ℕ) :
    (∀ n, discOffset f out.d out.m n ≤ B) → ∀ n, discrepancy out.g out.d n ≤ B :=
  out.discrepancy_le_of_forall_discOffset_le (f := f) (B := B)

/-- The `contract_discrepancy_le` field is redundant: it is implied by the rewrite rule.

This lemma records the redundancy at the level of functions so we can later drop the field
without breaking downstream code.
-/
theorem contract_discrepancy_le_eq_derived (out : ReductionOutput f) :
    out.contract_discrepancy_le = fun B => out.contract_discrepancy_le_derived (f := f) (out := out) B := by
  classical
  funext B
  -- Both sides are proofs of the same proposition; use proof irrelevance.
  exact Subsingleton.elim _ _

/-- Witness transfer: if some discrepancy of `out.g` is large, the corresponding offset discrepancy of `f` is large. -/
theorem exists_discOffset_gt_of_exists_discrepancy_gt (out : ReductionOutput f) (B : ℕ) :
    (∃ n, B < discrepancy out.g out.d n) → (∃ n, B < discOffset f out.d out.m n) := by
  intro h
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hn

/-- Witness transfer: if some offset discrepancy of `f` is large, the corresponding discrepancy of `out.g` is large. -/
theorem exists_discrepancy_gt_of_exists_discOffset_gt (out : ReductionOutput f) (B : ℕ) :
    (∃ n, B < discOffset f out.d out.m n) → (∃ n, B < discrepancy out.g out.d n) := by
  intro h
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hn

/-- Uniform transfer: bounding all discrepancies of `out.g` is equivalent to bounding all offset discrepancies of `f`. -/
theorem forall_discrepancy_le_iff_forall_discOffset_le (out : ReductionOutput f) (B : ℕ) :
    (∀ n, discrepancy out.g out.d n ≤ B) ↔ (∀ n, discOffset f out.d out.m n ≤ B) := by
  constructor
  · intro h n
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using h n
  · intro h n
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using h n

/-- Uniform transfer, strict version (`<`). -/
theorem forall_discrepancy_lt_iff_forall_discOffset_lt (out : ReductionOutput f) (B : ℕ) :
    (∀ n, discrepancy out.g out.d n < B) ↔ (∀ n, discOffset f out.d out.m n < B) := by
  constructor
  · intro h n
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using h n
  · intro h n
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using h n

/-- A convenient forward transfer lemma, strict version (`<`). -/
theorem discrepancy_lt_of_forall_discOffset_lt (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n, discOffset f out.d out.m n < B) :
    ∀ n, discrepancy out.g out.d n < B := by
  intro n
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n

/-- A convenient backward transfer lemma, strict version (`<`). -/
theorem discOffset_lt_of_forall_discrepancy_lt (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n, discrepancy out.g out.d n < B) :
    ∀ n, discOffset f out.d out.m n < B := by
  intro n
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n

/-- Existence transfer: exhibiting an offset discrepancy `> B` is equivalent to exhibiting a discrepancy `> B` for `out.g`. -/
theorem exists_discOffset_gt_iff_exists_discrepancy_gt (out : ReductionOutput f) (B : ℕ) :
    (∃ n, B < discOffset f out.d out.m n) ↔ (∃ n, B < discrepancy out.g out.d n) := by
  constructor
  · exact out.exists_discrepancy_gt_of_exists_discOffset_gt (f := f) (B := B)
  · exact out.exists_discOffset_gt_of_exists_discrepancy_gt (f := f) (B := B)

/-- Same as `exists_discOffset_gt_iff_exists_discrepancy_gt`, but with inequalities oriented as `... > C`.

This form is occasionally more convenient when a downstream lemma naturally produces a `>` inequality.
-/
theorem exists_discOffset_gt_iff_exists_discrepancy_gt' (out : ReductionOutput f) (C : ℕ) :
    (∃ n, discOffset f out.d out.m n > C) ↔ (∃ n, discrepancy out.g out.d n > C) := by
  -- Normalize `a > b` to `b < a`, then use the existing lemma.
  simpa [gt_iff_lt] using (out.exists_discOffset_gt_iff_exists_discrepancy_gt (f := f) (B := C))

/-- Uniform transfer of the unboundedness normal form, stated pointwise in `B`.

This is a tiny lemma, but it's the exact *shape* downstream contradiction stages often output.
-/
theorem forall_exists_discrepancy_gt_iff_forall_exists_discOffset_gt (out : ReductionOutput f) :
    (∀ B : ℕ, ∃ n : ℕ, B < discrepancy out.g out.d n) ↔
      (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) := by
  constructor
  · intro h B
    rcases h B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hn
  · intro h B
    rcases h B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hn

/-- Uniform transfer of the same unboundedness normal form, but phrased using `natAbs` of sums.

This avoids mentioning `discrepancy`/`discOffset` entirely.
-/
theorem forall_exists_natAbs_apSum_gt_iff_forall_exists_natAbs_apSumOffset_gt (out : ReductionOutput f) :
    (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSum out.g out.d n)) ↔
      (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n)) := by
  constructor
  · intro h B
    rcases h B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.apSum_contract] using hn
  · intro h B
    rcases h B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.apSum_contract] using hn

/-!
### Boundedness (along a fixed step) transfers

Many later stages alternate between:
- “bounded discrepancy along a fixed step `d`”, i.e. `BoundedDiscrepancyAlong` for the reduced sequence, and
- uniform bounds on `discOffset` expressions for the original sequence.

The following lemmas package those equivalences.
-/

/-- Bounded discrepancy of the reduced sequence along `out.d` is equivalent to a uniform bound on the
corresponding offset discrepancies of `f`.
-/
theorem boundedDiscrepancyAlong_iff_exists_forall_discOffset_le (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d ↔ (∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B) := by
  -- Unfold `BoundedDiscrepancyAlong` and rewrite `discrepancy out.g` to `discOffset f`.
  simp [BoundedDiscrepancyAlong, out.discrepancy_eq_discOffset]

/-- Negated form of `boundedDiscrepancyAlong_iff_exists_forall_discOffset_le`.

This is often the exact shape a contradiction stage consumes.
-/
theorem not_boundedDiscrepancyAlong_iff_forall_exists_discOffset_gt (out : ReductionOutput f) :
    (¬ BoundedDiscrepancyAlong out.g out.d) ↔ (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) := by
  -- Use the standard characterization of unboundedness along a fixed step, then transfer.
  --
  -- Note: `Tao2015.not_boundedDiscrepancyAlong_iff_forall_exists_discrepancy_gt` lives in the
  -- verified substrate and is the “canonical” unboundedness normal form.
  simpa [out.forall_exists_discrepancy_gt_iff_forall_exists_discOffset_gt (f := f)] using
    (Tao2015.not_boundedDiscrepancyAlong_iff_forall_exists_discrepancy_gt (g := out.g) (d := out.d))

/-- Unbounded discrepancy for the reduced sequence `out.g` (along `out.d`) rewritten into the
corresponding offset-discrepancy witness form for the original sequence.

This is the positive (non-negated) variant of
`not_boundedDiscrepancyAlong_iff_forall_exists_discOffset_gt`.
-/
theorem unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt (out : ReductionOutput f) :
    UnboundedDiscrepancyAlong out.g out.d ↔ (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) := by
  -- `UnboundedDiscrepancyAlong` is definitional in terms of `discrepancy`.
  -- Rewrite `discrepancy out.g` to `discOffset f` using the reduction interface.
  simp [UnboundedDiscrepancyAlong, out.discrepancy_eq_discOffset]

/-- `>`-oriented version of `unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt`.

This is often the more convenient orientation when later stages phrase witnesses as
`discOffset ... n > B`.
-/
theorem unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt' (out : ReductionOutput f) :
    UnboundedDiscrepancyAlong out.g out.d ↔ (∀ B : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > B) := by
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using
    (out.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt (f := f))

/-- Deprecated: this lemma name was misleading (it proves a `>`-shaped conclusion).

Use `unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt'` instead.
-/
@[deprecated unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt' (since := "2026-03-08")]
theorem unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (out : ReductionOutput f) :
    UnboundedDiscrepancyAlong out.g out.d ↔ (∀ B : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > B) := by
  simpa using (out.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt' (f := f))

/-- Unbounded discrepancy for the reduced sequence `out.g` (along `out.d`) rewritten into the
corresponding tail-sum witness form for the original sequence.

This is the `apSumFrom` analogue of `unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt`.
-/
theorem unboundedDiscrepancyAlong_iff_forall_exists_natAbs_apSumFrom_gt (out : ReductionOutput f) :
    UnboundedDiscrepancyAlong out.g out.d ↔
      (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumFrom f (out.m * out.d) out.d n)) := by
  -- `UnboundedDiscrepancyAlong` is definitional in terms of `discrepancy`.
  -- Rewrite `discrepancy out.g` using the reduction contract to the tail-sum nucleus.
  simp [UnboundedDiscrepancyAlong, out.discrepancy_eq_natAbs_apSumFrom_mul]

/-- A slightly more pipeline-friendly repackaging of `not_boundedDiscrepancyAlong_iff_forall_exists_discOffset_gt`
using the predicate `HasDiscrepancyAtLeastAlong`.
-/
theorem forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscrepancyAlong (out : ReductionOutput f) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) ↔ ¬ BoundedDiscrepancyAlong out.g out.d := by
  -- This is just the already-established equivalence for `out.g`, independent of the offset view.
  simpa using
    (HasDiscrepancyAtLeastAlong.forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscrepancyAlong
      (g := out.g) (d := out.d))

/-- Transfer a boundedness context for `f` to a bound on the *offset discrepancy* appearing in `out`.

This is a small convenience lemma: it isolates the parameter bundle `(out.d,out.m)`.
-/
theorem bound_discOffset (ctx : Context f) (out : ReductionOutput f) (n : ℕ) :
    discOffset f out.d out.m n ≤ ctx.B + ctx.B := by
  simpa using (ctx.bound_discOffset (f := f) (d := out.d) (m := out.m) (n := n) out.hd)

/-- Transfer a boundedness context for `f` to a bound on the *discrepancy* of `out.g`.

This is the “consumer-facing” version of `bound_apSum`.
-/
theorem bound_discrepancy (ctx : Context f) (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n ≤ ctx.B + ctx.B := by
  -- `simp` turns `Int.natAbs (apSum …)` into `discrepancy …`.
  simpa [discrepancy] using (bound_apSum (f := f) (ctx := ctx) (out := out) (n := n))

/-- Uniform `∀ n` version of `bound_apSum`. -/
theorem bound_apSum_forall (ctx : Context f) (out : ReductionOutput f) :
    ∀ n : ℕ, Int.natAbs (apSum out.g out.d n) ≤ ctx.B + ctx.B := by
  intro n
  exact out.bound_apSum (f := f) (ctx := ctx) (out := out) n

/-- Uniform `∀ n` version of `bound_apSumOffset`. -/
theorem bound_apSumOffset_forall (ctx : Context f) (out : ReductionOutput f) :
    ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ ctx.B + ctx.B := by
  intro n
  exact out.bound_apSumOffset (f := f) (ctx := ctx) (out := out) n

/-- Uniform `∀ n` version of `bound_discOffset`. -/
theorem bound_discOffset_forall (ctx : Context f) (out : ReductionOutput f) :
    ∀ n : ℕ, discOffset f out.d out.m n ≤ ctx.B + ctx.B := by
  intro n
  exact out.bound_discOffset (f := f) (ctx := ctx) (out := out) n

/-- Uniform `∀ n` version of `bound_discrepancy`. -/
theorem bound_discrepancy_forall (ctx : Context f) (out : ReductionOutput f) :
    ∀ n : ℕ, discrepancy out.g out.d n ≤ ctx.B + ctx.B := by
  intro n
  exact out.bound_discrepancy (f := f) (ctx := ctx) (out := out) n

/-- A lightweight “bounded discrepancy” notion along a *single* common difference `d`.

This is the natural consumer form after applying Tao’s first reduction: downstream steps
work with a fixed `d` bundled into `ReductionOutput`.
-/
def BoundedDiscrepancyAlong (g : ℕ → ℤ) (d : ℕ) : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, discrepancy g d n ≤ B

/-- A lightweight “bounded offset discrepancy” notion for fixed parameters `(d,m)`. -/
def BoundedDiscOffset (f : ℕ → ℤ) (d m : ℕ) : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, discOffset f d m n ≤ B

/-- The offset-boundedness predicate `BoundedDiscOffset` is equivalent to bounded discrepancy along
a fixed step size for the shifted sequence `fun k => f (k + m*d)`.

This is a convenience lemma: many Track C stages naturally produce (or consume) bounds in the
shifted fixed-step normal form, while the pipeline interface prefers the offset normal form.
-/
theorem boundedDiscOffset_iff_boundedDiscrepancyAlong_shift_add_mul (f : ℕ → ℤ) (d m : ℕ) :
    BoundedDiscOffset f d m ↔ BoundedDiscrepancyAlong (fun k => f (k + m * d)) d := by
  -- Unfold both boundedness predicates and rewrite the discrepancy term using the shift→offset bridge.
  simp [BoundedDiscOffset, BoundedDiscrepancyAlong,
    Tao2015.discrepancy_shift_add_mul_eq_discOffset]

namespace BoundedDiscrepancyAlong

/-- Build `BoundedDiscrepancyAlong g d` from an explicit uniform bound. -/
theorem of_bound (g : ℕ → ℤ) (d B : ℕ) (hB : ∀ n : ℕ, discrepancy g d n ≤ B) :
    BoundedDiscrepancyAlong g d :=
  ⟨B, hB⟩

end BoundedDiscrepancyAlong

namespace BoundedDiscOffset

/-- Build `BoundedDiscOffset f d m` from an explicit uniform bound. -/
theorem of_bound (f : ℕ → ℤ) (d m B : ℕ) (hB : ∀ n : ℕ, discOffset f d m n ≤ B) :
    BoundedDiscOffset f d m :=
  ⟨B, hB⟩

/-- Monotonicity in the bound: if `discOffset f d m` is bounded by `B`, it is bounded by any larger `B'`. -/
theorem mono {f : ℕ → ℤ} {d m B B' : ℕ}
    (hB : ∀ n : ℕ, discOffset f d m n ≤ B) (hBB' : B ≤ B') :
    BoundedDiscOffset f d m := by
  exact ⟨B', fun n => le_trans (hB n) hBB'⟩

end BoundedDiscOffset

/-- Unfold `BoundedDiscrepancyAlong` into the raw `Int.natAbs (apSum …)` normal form. -/
theorem boundedDiscrepancyAlong_iff_exists_natAbs_apSum_le (g : ℕ → ℤ) (d : ℕ) :
    BoundedDiscrepancyAlong g d ↔ (∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSum g d n) ≤ B) := by
  -- `discrepancy` is definitional.
  simp [BoundedDiscrepancyAlong, discrepancy]

/-- Unfold `BoundedDiscOffset` into the raw `Int.natAbs (apSumOffset …)` normal form. -/
theorem boundedDiscOffset_iff_exists_natAbs_apSumOffset_le (f : ℕ → ℤ) (d m : ℕ) :
    BoundedDiscOffset f d m ↔ (∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumOffset f d m n) ≤ B) := by
  -- `discOffset` is definitional.
  simp [BoundedDiscOffset, discOffset]

/-- Strict-inequality version of `BoundedDiscOffset`.

This is occasionally more convenient when a downstream stage naturally produces a bound of the form
`discOffset … < B` rather than `≤ B`.
-/
theorem boundedDiscOffset_iff_exists_discOffset_lt (f : ℕ → ℤ) (d m : ℕ) :
    BoundedDiscOffset f d m ↔ (∃ B : ℕ, ∀ n : ℕ, discOffset f d m n < B) := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B + 1, ?_⟩
    intro n
    exact Nat.lt_succ_of_le (hB n)
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    exact Nat.le_of_lt (hB n)

/-- Tail-sum normal form for `BoundedDiscOffset`.

Since `apSumFrom f (m*d) d n` is the tail sum starting at the affine point `m*d`, it is often the
most convenient expression once a stage has fixed the parameters `(d,m)`.

This lemma is just `boundedDiscOffset_iff_exists_natAbs_apSumOffset_le` rewritten using the bridge
`apSumFrom_eq_apSum_shift_add`/`apSumOffset_eq_apSum_shift_add`.
-/
theorem boundedDiscOffset_iff_exists_natAbs_apSumFrom_mul_le (f : ℕ → ℤ) (d m : ℕ) :
    BoundedDiscOffset f d m ↔ (∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) ≤ B) := by
  -- Rewrite `apSumFrom` and `apSumOffset` to the same shifted `apSum` normal form.
  -- Then reuse the existing `apSumOffset`-based lemma.
  simpa [apSumFrom_eq_apSum_shift_add, apSumOffset_eq_apSum_shift_add] using
    (boundedDiscOffset_iff_exists_natAbs_apSumOffset_le (f := f) (d := d) (m := m))

/-- A `Context f` gives bounded discrepancy along the reduced step size `out.d`.

This is a tiny packaging lemma: it turns the pointwise bound `out.bound_discrepancy` into the
existential form `BoundedDiscrepancyAlong` that later reduction stages commonly consume.
-/
theorem boundedDiscrepancyAlong_of_context (ctx : Context f) (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d := by
  refine ⟨ctx.B + ctx.B, ?_⟩
  intro n
  exact out.bound_discrepancy (f := f) (ctx := ctx) (out := out) n

/-- A `Context f` gives bounded offset discrepancy for the parameters bundled in `out`.

This is the offset-discrepancy analogue of `boundedDiscrepancyAlong_of_context`.
-/
theorem boundedDiscOffset_of_context (ctx : Context f) (out : ReductionOutput f) :
    BoundedDiscOffset f out.d out.m := by
  refine ⟨ctx.B + ctx.B, ?_⟩
  intro n
  exact out.bound_discOffset (f := f) (ctx := ctx) (out := out) n

/-- A direct shift-vs-offset boundedness equivalence (interface-free).

This is the “raw” version of `ReductionOutput.boundedDiscrepancyAlong_iff_boundedDiscOffset`.
It is useful when you have not yet packaged a reduction step into a `ReductionOutput`.
-/
theorem boundedDiscrepancyAlong_shift_add_mul_iff_boundedDiscOffset (f : ℕ → ℤ) (d m : ℕ) :
    BoundedDiscrepancyAlong (fun k => f (k + m * d)) d ↔ BoundedDiscOffset f d m := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- Rewrite the discrepancy of the shifted sequence to an offset discrepancy.
    simpa [BoundedDiscOffset, discrepancy_shift_add_mul_eq_discOffset] using hB n
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- Rewrite back in the other direction.
    -- (`simp` uses the reverse orientation of the rewrite lemma.)
    simpa [BoundedDiscrepancyAlong, discrepancy_shift_add_mul_eq_discOffset] using hB n

/-- Convenience: bounded offset discrepancy implies bounded discrepancy along the shifted sequence. -/
theorem boundedDiscrepancyAlong_shift_add_mul_of_boundedDiscOffset (f : ℕ → ℤ) (d m : ℕ)
    (h : BoundedDiscOffset f d m) :
    BoundedDiscrepancyAlong (fun k => f (k + m * d)) d :=
  (boundedDiscrepancyAlong_shift_add_mul_iff_boundedDiscOffset (f := f) (d := d) (m := m)).2 h

/-- Convenience: bounded discrepancy along the shifted sequence implies bounded offset discrepancy. -/
theorem boundedDiscOffset_of_boundedDiscrepancyAlong_shift_add_mul (f : ℕ → ℤ) (d m : ℕ)
    (h : BoundedDiscrepancyAlong (fun k => f (k + m * d)) d) :
    BoundedDiscOffset f d m :=
  (boundedDiscrepancyAlong_shift_add_mul_iff_boundedDiscOffset (f := f) (d := d) (m := m)).1 h

namespace BoundedDiscrepancyAlong

/-- Negating `BoundedDiscrepancyAlong` is equivalent to the usual unboundedness normal form.

This is a tiny lemma, but it is the common *output shape* of many contradiction-style pipeline
stages: they naturally produce witnesses `∀ B, ∃ n, B < discrepancy ...`.
-/
theorem not_iff_forall_exists_gt (g : ℕ → ℤ) (d : ℕ) :
    (¬ BoundedDiscrepancyAlong g d) ↔ (∀ B : ℕ, ∃ n : ℕ, B < discrepancy g d n) := by
  constructor
  · intro h B
    by_contra h'
    -- `h'` says there is no `n` with `B < discrepancy g d n`, so everything is bounded by `B`.
    have hB : ∀ n : ℕ, discrepancy g d n ≤ B := by
      intro n
      have : ¬ B < discrepancy g d n := by
        -- otherwise we'd contradict `h'`.
        intro hn
        exact h' ⟨n, hn⟩
      exact le_of_not_gt this
    exact h ⟨B, hB⟩
  · intro h
    rintro ⟨B, hB⟩
    rcases h B with ⟨n, hn⟩
    exact (not_lt_of_ge (hB n) hn)

end BoundedDiscrepancyAlong

namespace BoundedDiscOffset

/-- Negating bounded offset discrepancy is equivalent to the usual unboundedness normal form.

This is a basic but extremely common shape transformation: downstream contradiction stages tend to
produce witnesses of the form `∀ B, ∃ n, B < ...`.
-/
theorem not_iff_forall_exists_gt (f : ℕ → ℤ) (d m : ℕ) :
    (¬ BoundedDiscOffset f d m) ↔ (∀ B : ℕ, ∃ n : ℕ, B < discOffset f d m n) := by
  simpa using
    (not_boundedDiscOffset_iff_forall_exists_discOffset_gt (f := f) (d := d) (m := m))

/-- Tail-sum normal form of `BoundedDiscOffset.not_iff_forall_exists_gt`.

This is the statement shape most convenient for later Tao2015 stages that reason about affine tails
(`apSumFrom f (m*d) d n`) rather than the bundled wrapper `discOffset`.
-/
theorem not_iff_forall_exists_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ) (d m : ℕ) :
    (¬ BoundedDiscOffset f d m) ↔
      (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumFrom f (m * d) d n)) := by
  -- `discOffset f d m n = natAbs (apSumFrom f (m*d) d n)`.
  simpa [discOffset_eq_natAbs_apSumFrom_mul] using
    (not_iff_forall_exists_gt (f := f) (d := d) (m := m))

end BoundedDiscOffset

namespace ReductionOutput

/-- A global boundedness context for `f` yields bounded *offset* discrepancy for the parameters
bundled in `out`.

This is the most direct way to use `Context f` after the first reduction step: it produces the
exact `∃ B, ∀ n` shape downstream stages typically want.
-/
theorem boundedDiscOffset_ofContext (ctx : Context f) (out : ReductionOutput f) :
    BoundedDiscOffset f out.d out.m := by
  refine ⟨ctx.B + ctx.B, ?_⟩
  intro n
  exact out.bound_discOffset (f := f) (ctx := ctx) (out := out) n

/-- A global boundedness context for `f` yields bounded discrepancy for the reduced sequence
`out.g` along the fixed common difference `out.d`.

This is the `BoundedDiscrepancyAlong` analogue of `boundedDiscOffset_ofContext`.
-/
theorem boundedDiscrepancyAlong_ofContext (ctx : Context f) (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d := by
  refine ⟨ctx.B + ctx.B, ?_⟩
  intro n
  exact out.bound_discrepancy (f := f) (ctx := ctx) (out := out) n

/-- The reduction interface gives an equivalence between bounded discrepancy for `out.g` along
`out.d` and bounded offset discrepancy for `f` at `(out.d,out.m)`.

This is essentially the bundled version of
`boundedDiscrepancyAlong_shift_add_mul_iff_boundedDiscOffset`.
-/
theorem boundedDiscrepancyAlong_iff_boundedDiscOffset (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d ↔ BoundedDiscOffset f out.d out.m := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- rewrite discrepancy of `out.g` to offset discrepancy of `f`
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- rewrite back in the other direction
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n

/-- Alias of `boundedDiscrepancyAlong_iff_boundedDiscOffset` with the sides swapped.

Downstream stages sometimes speak naturally about the offset-boundedness predicate
`BoundedDiscOffset f out.d out.m` and want to convert it into bounded discrepancy along
the reduced step size.
-/
theorem boundedDiscOffset_iff_boundedDiscrepancyAlong (out : ReductionOutput f) :
    BoundedDiscOffset f out.d out.m ↔ BoundedDiscrepancyAlong out.g out.d := by
  simpa using (out.boundedDiscrepancyAlong_iff_boundedDiscOffset (f := f)).symm

/-- Unfold the boundedness interface down to the raw `natAbs (apSumOffset …)` normal form.

This is just `boundedDiscrepancyAlong_iff_boundedDiscOffset` plus the definitional rewrite
`boundedDiscOffset_iff_exists_natAbs_apSumOffset_le`, but it is a very common consumer shape.
-/
theorem boundedDiscrepancyAlong_iff_exists_natAbs_apSumOffset_le (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d ↔ (∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ B) := by
  -- First hop: `BoundedDiscrepancyAlong out.g out.d ↔ BoundedDiscOffset f out.d out.m`.
  -- Second hop: unfold `BoundedDiscOffset` to the `natAbs (apSumOffset …)` normal form.
  simpa [boundedDiscOffset_iff_exists_natAbs_apSumOffset_le] using
    (out.boundedDiscrepancyAlong_iff_boundedDiscOffset (f := f))

/-- Peel the bundled offset in `out` at the level of bounded offset discrepancy.

Bounding `discOffset f out.d (out.m + m₂)` uniformly in `n` is equivalent to bounding
`discOffset out.g out.d m₂` uniformly in `n`.

This is the boundedness analogue of `out.discOffset_add_eq_discOffset_g`.
-/
theorem boundedDiscOffset_add_iff_boundedDiscOffset_g (out : ReductionOutput f) (m₂ : ℕ) :
    BoundedDiscOffset f out.d (out.m + m₂) ↔ BoundedDiscOffset out.g out.d m₂ := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- rewrite a bundled offset discrepancy of `f` to an offset discrepancy of `out.g`
    simpa [out.discOffset_add_eq_discOffset_g (f := f) (m₂ := m₂) (n := n)] using hB n
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- rewrite back in the other direction
    simpa [out.discOffset_add_eq_discOffset_g (f := f) (m₂ := m₂) (n := n)] using hB n

/-- Negated form of `boundedDiscrepancyAlong_iff_boundedDiscOffset`.

This is useful because many “unboundedness” stages in Tao’s pipeline are naturally phrased as
`¬ ∃ B, ∀ n, ...`.
-/
theorem not_boundedDiscrepancyAlong_iff_not_boundedDiscOffset (out : ReductionOutput f) :
    ¬ BoundedDiscrepancyAlong out.g out.d ↔ ¬ BoundedDiscOffset f out.d out.m := by
  simpa using not_congr (out.boundedDiscrepancyAlong_iff_boundedDiscOffset (f := f))

/-- Pipeline-friendly form: `∀ C, HasDiscrepancyAtLeastAlong out.g out.d C` is equivalent to
unbounded offset discrepancy for `f` at `(out.d,out.m)`.

This is a convenient entry point when a downstream stage produces witnesses in the
`HasDiscrepancyAtLeastAlong` form.
-/
theorem forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscOffset (out : ReductionOutput f) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) ↔ ¬ BoundedDiscOffset f out.d out.m := by
  -- First convert `∀ C, HasDiscrepancyAtLeastAlong ...` to a negated boundedness statement for `out.g`.
  -- Then transport across the reduction interface.
  calc
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C)
        ↔ ¬ BoundedDiscrepancyAlong out.g out.d := by
          simpa using
            (HasDiscrepancyAtLeastAlong.forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscrepancyAlong
              (g := out.g) (d := out.d))
    _ ↔ ¬ BoundedDiscOffset f out.d out.m :=
          out.not_boundedDiscrepancyAlong_iff_not_boundedDiscOffset (f := f)

/-- One direction of `forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscOffset`. -/
theorem not_boundedDiscOffset_of_forall_hasDiscrepancyAtLeastAlong (out : ReductionOutput f)
    (h : ∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) :
    ¬ BoundedDiscOffset f out.d out.m :=
  (out.forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscOffset (f := f)).1 h

/-- The other direction of `forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscOffset`. -/
theorem forall_hasDiscrepancyAtLeastAlong_of_not_boundedDiscOffset (out : ReductionOutput f)
    (h : ¬ BoundedDiscOffset f out.d out.m) :
    ∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C :=
  (out.forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscOffset (f := f)).2 h

/-- Convert an `AlongContext` for the reduced sequence into bounded offset discrepancy for `f`.

This is often the *exact* consumer step after you have proved a uniform `apSum`-bound for `out.g`
(along the fixed `out.d`) and want to hand it back to the next pipeline stage as a
`BoundedDiscOffset` hypothesis.
-/
theorem boundedDiscOffset_ofAlongContext (out : ReductionOutput f) (ctx : AlongContext out.g out.d) :
    BoundedDiscOffset f out.d out.m := by
  refine ⟨ctx.B, ?_⟩
  intro n
  -- Rewrite `discOffset` to `discrepancy` and use the discrepancy bound from `ctx`.
  have : discrepancy out.g out.d n ≤ ctx.B := by
    simpa [discrepancy] using ctx.bound n
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using this

/-- Convert bounded offset discrepancy for `f` into an `AlongContext` for the reduced sequence.

This is the “data” version of `boundedDiscrepancyAlong_iff_boundedDiscOffset`, specialized to the
`AlongContext` consumer API.
-/
noncomputable def alongContext_ofBoundedDiscOffset (out : ReductionOutput f)
    (h : BoundedDiscOffset f out.d out.m) : AlongContext out.g out.d := by
  classical
  refine ⟨Classical.choose h, ?_⟩
  intro n
  -- `BoundedDiscOffset` bounds `discOffset`; rewrite to `discrepancy` and unfold.
  have hn : discOffset f out.d out.m n ≤ Classical.choose h := (Classical.choose_spec h) n
  have : discrepancy out.g out.d n ≤ Classical.choose h := by
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hn
  simpa [discrepancy] using this

/-- Transfer lemma: unboundedness (in the `∀ B, ∃ n, B < ...` normal form) is equivalent across
the reduction interface.

This is the strict witness form typically produced by contradiction stages.
-/
theorem forall_exists_discrepancy_gt_iff_forall_exists_discOffset_gt' (out : ReductionOutput f) :
    (∀ B : ℕ, ∃ n : ℕ, B < discrepancy out.g out.d n) ↔
      (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) :=
  out.forall_exists_discrepancy_gt_iff_forall_exists_discOffset_gt (f := f)

end ReductionOutput

/-- If we literally shift the sequence by `m*d`, then bounded discrepancy along `d` is equivalent
to bounded offset discrepancy of the original sequence.

This is an “interface-free” version of `ReductionOutput.boundedDiscrepancyAlong_iff_boundedDiscOffset`:
it is useful before packaging the shift into a `ReductionOutput`.
-/
theorem boundedDiscrepancyAlong_shift_add_mul_iff_boundedDiscOffset (f : ℕ → ℤ) (d m : ℕ) :
    BoundedDiscrepancyAlong (fun k => f (k + m * d)) d ↔ BoundedDiscOffset f d m := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- rewrite discrepancy of the shifted sequence to `discOffset`.
    simpa [discrepancy_shift_add_mul_eq_discOffset (f := f) (d := d) (m := m) (n := n)] using hB n
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- rewrite back in the other direction.
    simpa [discrepancy_shift_add_mul_eq_discOffset (f := f) (d := d) (m := m) (n := n)] using hB n

/-- Re-associate offsets at the level of boundedness: bounding offsets at `m₁+m₂` is equivalent
to bounding offsets at `m₂` after shifting by `m₁*d`.

This is the boundedness analogue of `discOffset_add`.
-/
theorem boundedDiscOffset_add (f : ℕ → ℤ) (d m₁ m₂ : ℕ) :
    BoundedDiscOffset f d (m₁ + m₂) ↔ BoundedDiscOffset (fun k => f (k + m₁ * d)) d m₂ := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- `discOffset f d (m₁+m₂) n = discOffset (shift f m₁) d m₂ n`.
    simpa [discOffset_add (f := f) (d := d) (m₁ := m₁) (m₂ := m₂) (n := n)] using hB n
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- reverse orientation of the same rewrite.
    simpa [discOffset_add (f := f) (d := d) (m₁ := m₁) (m₂ := m₂) (n := n)] using hB n

/-- A Lean-friendly “context” for working with a *single* common difference `d`.

This is the natural consumer interface after Tao’s first reduction step: downstream stages
typically fix `d` (bundled in `ReductionOutput`) and then only need uniform control of
`apSum g d n` over `n`.
-/
structure AlongContext (g : ℕ → ℤ) (d : ℕ) : Type where
  B : ℕ
  bound : ∀ n : ℕ, Int.natAbs (apSum g d n) ≤ B

namespace AlongContext

/-- Turn an `AlongContext` into the propositional boundedness notion `BoundedDiscrepancyAlong`. -/
theorem boundedDiscrepancyAlong (ctx : AlongContext g d) : BoundedDiscrepancyAlong g d := by
  refine ⟨ctx.B, ?_⟩
  intro n
  -- `discrepancy` is just `natAbs (apSum …)`.
  simpa [discrepancy] using ctx.bound n

/-- A convenience lemma: an `AlongContext` gives a pointwise discrepancy bound. -/
theorem bound_discrepancy (ctx : AlongContext g d) (n : ℕ) : discrepancy g d n ≤ ctx.B := by
  -- `discrepancy` is just `natAbs (apSum …)`.
  simpa [discrepancy] using ctx.bound n

/-- Uniform version of `AlongContext.bound_discrepancy`. -/
theorem bound_discrepancy_forall (ctx : AlongContext g d) : ∀ n : ℕ, discrepancy g d n ≤ ctx.B := by
  intro n
  exact ctx.bound_discrepancy (g := g) (d := d) n

/-- Extract an `AlongContext` from the propositional boundedness notion.

Noncomputable because we use classical choice to pick a witness bound `B`.
-/
noncomputable def ofBoundedDiscrepancyAlong (h : BoundedDiscrepancyAlong g d) : AlongContext g d := by
  classical
  refine ⟨Classical.choose h, ?_⟩
  intro n
  -- `BoundedDiscrepancyAlong` bounds `discrepancy`; unfold and rewrite.
  have : discrepancy g d n ≤ Classical.choose h := (Classical.choose_spec h) n
  simpa [discrepancy] using this

/-- If `f` has a global boundedness context, then any reduction output yields an `AlongContext`
for the derived sequence along the bundled `d`.

The bound is the same weak `2B` bound used in `ReductionOutput.bound_apSum`.
-/
theorem ofContext (ctx : Context f) (out : ReductionOutput f) : AlongContext out.g out.d := by
  refine ⟨ctx.B + ctx.B, ?_⟩
  intro n
  exact out.bound_apSum (f := f) (ctx := ctx) (out := out) n

/-!
### Offset / shift bounds from `AlongContext`

Downstream stages frequently work with a fixed common difference `d` and only have an
`AlongContext g d` hypothesis (a uniform bound on `apSum g d n`).

The next lemmas mirror the earlier `Context` API but *do not* require global bounded discrepancy
for all `(d,n)`: they only use the single-`d` bound bundled in the `AlongContext`.
-/

/-- Bound offset AP sums using only a single-`d` uniform bound on prefix sums.

This is the `AlongContext` analogue of `Context.bound_apSumOffset`.
-/
theorem bound_apSumOffset (ctx : AlongContext g d) (m n : ℕ) :
    Int.natAbs (apSumOffset g d m n) ≤ ctx.B + ctx.B := by
  -- `apSumOffset = apSum (m+n) - apSum m`.
  calc
    Int.natAbs (apSumOffset g d m n)
        = Int.natAbs (apSum g d (m + n) - apSum g d m) := by
          simp [apSumOffset_eq_sub]
    _ ≤ Int.natAbs (apSum g d (m + n)) + Int.natAbs (apSum g d m) := by
          simpa using (Int.natAbs_sub_le (apSum g d (m + n)) (apSum g d m))
    _ ≤ ctx.B + ctx.B := by
          exact Nat.add_le_add (ctx.bound (m + n)) (ctx.bound m)

/-- Discrepancy wrapper version of `AlongContext.bound_apSumOffset`. -/
theorem bound_discOffset (ctx : AlongContext g d) (m n : ℕ) :
    discOffset g d m n ≤ ctx.B + ctx.B := by
  simpa [discOffset] using (ctx.bound_apSumOffset (g := g) (d := d) (m := m) (n := n))

/-- Bound AP sums of a shifted sequence (by a multiple `m*d`) in terms of an `AlongContext`.

This is the normal form that comes up when re-centering a reduction step.
-/
theorem bound_apSum_shift_add_mul (ctx : AlongContext g d) (m n : ℕ) :
    Int.natAbs (apSum (fun k => g (k + m * d)) d n) ≤ ctx.B + ctx.B := by
  -- Rewrite the shifted AP sum to an offset sum and use `bound_apSumOffset`.
  simpa [Tao2015.apSum_shift_add_mul_eq_apSumOffset] using
    (ctx.bound_apSumOffset (g := g) (d := d) (m := m) (n := n))

/-- Discrepancy version of `AlongContext.bound_apSum_shift_add_mul`. -/
theorem bound_discrepancy_shift_add_mul (ctx : AlongContext g d) (m n : ℕ) :
    discrepancy (fun k => g (k + m * d)) d n ≤ ctx.B + ctx.B := by
  -- `discrepancy` is just `natAbs` of `apSum`.
  simpa [discrepancy] using (ctx.bound_apSum_shift_add_mul (g := g) (d := d) (m := m) (n := n))

/-- Uniform version of `AlongContext.bound_discrepancy_shift_add_mul`. -/
theorem bound_discrepancy_shift_add_mul_forall (ctx : AlongContext g d) (m : ℕ) :
    ∀ n : ℕ, discrepancy (fun k => g (k + m * d)) d n ≤ ctx.B + ctx.B := by
  intro n
  exact ctx.bound_discrepancy_shift_add_mul (g := g) (d := d) (m := m) (n := n)

/-- Rewrite `discOffset` in terms of the tail-sum API `apSumFrom` for a single fixed `d`.

This is a small ergonomics lemma: many reduction steps naturally talk about tail sums, while the
basic offset-discrepancy interface uses `discOffset`.
-/
theorem discOffset_eq_natAbs_apSumFrom (g : ℕ → ℤ) (d m n : ℕ) :
    discOffset g d m n = Int.natAbs (apSumFrom g (m * d) d n) := by
  -- Both `apSumOffset` and `apSumFrom` are definitional wrappers around the same shifted AP sum.
  simp [discOffset, apSumOffset_eq_apSum_shift_add, apSumFrom_eq_apSum_shift_add, Nat.mul_assoc]

/-- Bound tail sums of the form `apSumFrom g (m*d) d n` using only an `AlongContext g d`.

This is the tail-sum analogue of `bound_apSum_shift_add_mul`.
-/
theorem bound_apSumFrom_mul (ctx : AlongContext g d) (m n : ℕ) :
    Int.natAbs (apSumFrom g (m * d) d n) ≤ ctx.B + ctx.B := by
  -- Rewrite `apSumFrom` to an AP sum of the shifted sequence and use the previous bound.
  simpa [apSumFrom_eq_apSum_shift_add, Nat.mul_assoc] using
    (ctx.bound_apSum_shift_add_mul (g := g) (d := d) (m := m) (n := n))

/-- Bound `discOffset` using the `apSumFrom` normal form.

This is just `bound_apSumFrom_mul`, but packaged in the standard discrepancy wrapper.
-/
theorem bound_discOffset_via_apSumFrom (ctx : AlongContext g d) (m n : ℕ) :
    discOffset g d m n ≤ ctx.B + ctx.B := by
  -- `discOffset` is the `natAbs` wrapper around `apSumOffset`, which equals the corresponding tail sum.
  simpa [discOffset_eq_natAbs_apSumFrom (g := g) (d := d) (m := m) (n := n)] using
    (ctx.bound_apSumFrom_mul (g := g) (d := d) (m := m) (n := n))

/-- Uniform `∀ n` version of `AlongContext.bound_apSumOffset`. -/
theorem bound_apSumOffset_forall (ctx : AlongContext g d) (m : ℕ) :
    ∀ n : ℕ, Int.natAbs (apSumOffset g d m n) ≤ ctx.B + ctx.B := by
  intro n
  exact ctx.bound_apSumOffset (g := g) (d := d) (m := m) (n := n)

/-- Uniform `∀ n` version of `AlongContext.bound_discOffset`. -/
theorem bound_discOffset_forall (ctx : AlongContext g d) (m : ℕ) :
    ∀ n : ℕ, discOffset g d m n ≤ ctx.B + ctx.B := by
  intro n
  exact ctx.bound_discOffset (g := g) (d := d) (m := m) (n := n)

/-- Uniform `∀ n` version of `AlongContext.bound_apSum_shift_add_mul`. -/
theorem bound_apSum_shift_add_mul_forall (ctx : AlongContext g d) (m : ℕ) :
    ∀ n : ℕ, Int.natAbs (apSum (fun k => g (k + m * d)) d n) ≤ ctx.B + ctx.B := by
  intro n
  exact ctx.bound_apSum_shift_add_mul (g := g) (d := d) (m := m) (n := n)

/-- Uniform `∀ n` version of `AlongContext.bound_discrepancy_shift_add_mul`. -/
theorem bound_discrepancy_shift_add_mul_forall (ctx : AlongContext g d) (m : ℕ) :
    ∀ n : ℕ, discrepancy (fun k => g (k + m * d)) d n ≤ ctx.B + ctx.B := by
  intro n
  exact ctx.bound_discrepancy_shift_add_mul (g := g) (d := d) (m := m) (n := n)

/-- Uniform `∀ n` version of `AlongContext.bound_apSumFrom_mul`. -/
theorem bound_apSumFrom_mul_forall (ctx : AlongContext g d) (m : ℕ) :
    ∀ n : ℕ, Int.natAbs (apSumFrom g (m * d) d n) ≤ ctx.B + ctx.B := by
  intro n
  exact ctx.bound_apSumFrom_mul (g := g) (d := d) (m := m) (n := n)

/-- Uniform `∀ n` version of `AlongContext.bound_discOffset_via_apSumFrom`. -/
theorem bound_discOffset_via_apSumFrom_forall (ctx : AlongContext g d) (m : ℕ) :
    ∀ n : ℕ, discOffset g d m n ≤ ctx.B + ctx.B := by
  intro n
  exact ctx.bound_discOffset_via_apSumFrom (g := g) (d := d) (m := m) (n := n)

/-!
### Packaging shifts of an `AlongContext`

Downstream stages often re-center the reduced sequence by shifting it by a multiple of the fixed
common difference `d`.  The lemma `bound_apSum_shift_add_mul` gives the relevant bound, but it is
convenient to repackage it as a new `AlongContext`.
-/

/-- Shift an `AlongContext` by an additional multiple `m*d`.

The bound degrades by a factor `2` (from `B` to `B+B`), matching the estimate in
`AlongContext.bound_apSum_shift_add_mul`.
-/
def shiftRight (ctx : AlongContext g d) (m : ℕ) : AlongContext (fun k => g (k + m * d)) d := by
  refine ⟨ctx.B + ctx.B, ?_⟩
  intro n
  exact ctx.bound_apSum_shift_add_mul (g := g) (d := d) (m := m) (n := n)

/-- The bound used by `AlongContext.shiftRight`. -/
@[simp] theorem shiftRight_B (ctx : AlongContext g d) (m : ℕ) :
    (ctx.shiftRight (g := g) (d := d) m).B = ctx.B + ctx.B := by
  rfl

/-- Discrepancy bound coming from `AlongContext.shiftRight`. -/
theorem shiftRight_bound_discrepancy (ctx : AlongContext g d) (m n : ℕ) :
    discrepancy (fun k => g (k + m * d)) d n ≤ (ctx.shiftRight (g := g) (d := d) m).B := by
  -- Unfold `shiftRight` and reuse `bound_discrepancy_shift_add_mul`.
  simpa [AlongContext.shiftRight] using
    (ctx.bound_discrepancy_shift_add_mul (g := g) (d := d) (m := m) (n := n))

/-- `apSum` bound coming from `AlongContext.shiftRight`.

This is just the `natAbs (apSum …)` form of `shiftRight_bound_discrepancy`.
-/
theorem shiftRight_bound_apSum (ctx : AlongContext g d) (m n : ℕ) :
    Int.natAbs (apSum (fun k => g (k + m * d)) d n) ≤ (ctx.shiftRight (g := g) (d := d) m).B := by
  -- Unfold `shiftRight` and reuse `bound_apSum_shift_add_mul`.
  simpa [discrepancy, AlongContext.shiftRight] using
    (ctx.bound_apSum_shift_add_mul (g := g) (d := d) (m := m) (n := n))

/-- Offset-AP-sum bound coming from `AlongContext.shiftRight`.

Downstream steps often shift `g` first and then take offset sums; this lemma is the direct
packaged estimate.
-/
theorem shiftRight_bound_apSumOffset (ctx : AlongContext g d) (m m₂ n : ℕ) :
    Int.natAbs (apSumOffset (fun k => g (k + m * d)) d m₂ n)
      ≤ (ctx.shiftRight (g := g) (d := d) m).B + (ctx.shiftRight (g := g) (d := d) m).B := by
  -- Use the generic `AlongContext` offset-sum bound on the shifted context.
  simpa using
    ((ctx.shiftRight (g := g) (d := d) m).bound_apSumOffset
      (g := fun k => g (k + m * d)) (d := d) (m := m₂) (n := n))

/-- Discrepancy wrapper version of `shiftRight_bound_apSumOffset`. -/
theorem shiftRight_bound_discOffset (ctx : AlongContext g d) (m m₂ n : ℕ) :
    discOffset (fun k => g (k + m * d)) d m₂ n
      ≤ (ctx.shiftRight (g := g) (d := d) m).B + (ctx.shiftRight (g := g) (d := d) m).B := by
  simpa [discOffset] using (shiftRight_bound_apSumOffset (g := g) (d := d) ctx m m₂ n)

end AlongContext

/-- Unfold `BoundedDiscrepancyAlong` into a uniform bound on absolute AP sums. -/
theorem boundedDiscrepancyAlong_iff_forall_natAbs_apSum_le (g : ℕ → ℤ) (d : ℕ) :
    BoundedDiscrepancyAlong g d ↔ (∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSum g d n) ≤ B) := by
  -- `discrepancy` is just `Int.natAbs (apSum …)`.
  simp [BoundedDiscrepancyAlong, discrepancy]

/-- Unfold `BoundedDiscOffset` into a uniform bound on absolute offset AP sums. -/
theorem boundedDiscOffset_iff_forall_natAbs_apSumOffset_le (f : ℕ → ℤ) (d m : ℕ) :
    BoundedDiscOffset f d m ↔ (∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumOffset f d m n) ≤ B) := by
  -- `discOffset` is just `Int.natAbs (apSumOffset …)`.
  simp [BoundedDiscOffset, discOffset]

/-- For the particular parameters bundled in a `ReductionOutput`, boundedness along the reduced
sequence is equivalent to a uniform bound on the absolute values of the corresponding offset sums.

This is often the most convenient “consumer” statement: it avoids mentioning `discOffset` and
`discrepancy` entirely.
-/
theorem boundedDiscrepancyAlong_iff_forall_natAbs_apSumOffset_le (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d ↔
      (∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ B) := by
  -- Unfold to `natAbs (apSum out.g out.d n)`, then rewrite via the bridge rule.
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- `hB` bounds `discrepancy`; unfold and rewrite `apSum` to `apSumOffset`.
    have : Int.natAbs (apSum out.g out.d n) ≤ B := by
      simpa [discrepancy] using hB n
    simpa [out.apSum_contract] using this
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- Conversely, rewrite `apSum` to `apSumOffset` and fold back into `discrepancy`.
    have : Int.natAbs (apSum out.g out.d n) ≤ B := by
      simpa [out.apSum_contract] using hB n
    simpa [discrepancy] using this

/-- Dually, bounded offset discrepancy for the parameters in `out` is equivalent to a uniform bound
on absolute AP sums for the reduced sequence `out.g`.
-/
theorem boundedDiscOffset_iff_forall_natAbs_apSum_le (out : ReductionOutput f) :
    BoundedDiscOffset f out.d out.m ↔ (∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSum out.g out.d n) ≤ B) := by
  -- Unfold to `natAbs (apSumOffset …)`, then rewrite via the bridge rule.
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    have : Int.natAbs (apSumOffset f out.d out.m n) ≤ B := by
      simpa [discOffset] using hB n
    simpa [out.apSum_contract] using this
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    have : Int.natAbs (apSumOffset f out.d out.m n) ≤ B := by
      simpa [out.apSum_contract] using hB n
    simpa [discOffset] using this

/-- Produce an `AlongContext` from bounded *offset* discrepancy.

This is a common entry point for downstream stages: they only want an `AlongContext` for the
reduced sequence `out.g` (along the fixed `out.d`), and do not care about the intermediate
`discOffset` wrapper.
-/
noncomputable def alongContextOfBoundedDiscOffset (out : ReductionOutput f)
    (h : BoundedDiscOffset f out.d out.m) : AlongContext out.g out.d := by
  classical
  -- Unfold to a uniform `natAbs` bound on `apSum out.g out.d n`, then package it.
  rcases (out.boundedDiscOffset_iff_forall_natAbs_apSum_le (f := f)).1 h with ⟨B, hB⟩
  exact ⟨B, hB⟩

/-- Convert an `AlongContext` for the reduced sequence into a pointwise bound on the corresponding
offset AP sums.

This is often the most direct consumer lemma: downstream stages naturally produce `AlongContext`
facts about `apSum out.g out.d`, and we want to immediately transport them back to the original
sequence `f`.
-/
theorem bound_apSumOffset_of_alongContext (out : ReductionOutput f) (ctx : AlongContext out.g out.d) (n : ℕ) :
    Int.natAbs (apSumOffset f out.d out.m n) ≤ ctx.B := by
  -- Rewrite the offset sum to an AP sum on the reduced sequence.
  simpa [out.apSum_contract] using ctx.bound n

/-- Discrepancy-flavored version of `bound_apSumOffset_of_alongContext`. -/
theorem bound_discOffset_of_alongContext (out : ReductionOutput f) (ctx : AlongContext out.g out.d) (n : ℕ) :
    discOffset f out.d out.m n ≤ ctx.B := by
  -- `discOffset` is definitional.
  simpa [discOffset] using (bound_apSumOffset_of_alongContext (f := f) (out := out) (ctx := ctx) n)

/-- Convert an `AlongContext` for the reduced sequence into bounded *offset* discrepancy for `f`.

This is the “reverse direction” of `alongContextOfBoundedDiscOffset`.

Note: we prove this directly from the bridge rule `out.apSum_contract` rather than appealing to
`boundedDiscrepancyAlong_iff_boundedDiscOffset`, since that equivalence is stated later in the file.
-/
theorem boundedDiscOffset_of_alongContext (out : ReductionOutput f) (ctx : AlongContext out.g out.d) :
    BoundedDiscOffset f out.d out.m := by
  refine ⟨ctx.B, ?_⟩
  intro n
  exact bound_discOffset_of_alongContext (f := f) (out := out) (ctx := ctx) n

/-- Convert an `AlongContext` for the reduced sequence into a uniform bound on `discOffset`.

This is the consumer-friendly form of `boundedDiscOffset_of_alongContext`.
-/
theorem forall_discOffset_le_of_alongContext (out : ReductionOutput f) (ctx : AlongContext out.g out.d) :
    ∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B := by
  -- `BoundedDiscOffset` is already the desired `∃ B, ∀ n` shape.
  simpa [BoundedDiscOffset] using (boundedDiscOffset_of_alongContext (f := f) (out := out) ctx)

/-- A helper to *use* `BoundedDiscrepancyAlong` as a `∀ n` bound on `discrepancy`. -/
theorem BoundedDiscrepancyAlong.exists_bound {g : ℕ → ℤ} {d : ℕ} :
    BoundedDiscrepancyAlong g d → ∃ B : ℕ, ∀ n : ℕ, discrepancy g d n ≤ B := by
  intro h; simpa [BoundedDiscrepancyAlong] using h

/-- A helper to *use* `BoundedDiscOffset` as a `∀ n` bound on `discOffset`. -/
theorem BoundedDiscOffset.exists_bound {f : ℕ → ℤ} {d m : ℕ} :
    BoundedDiscOffset f d m → ∃ B : ℕ, ∀ n : ℕ, discOffset f d m n ≤ B := by
  intro h; simpa [BoundedDiscOffset] using h

/-- Unboundedness normal form for `BoundedDiscrepancyAlong`.

This is the shape downstream contradiction stages usually want: for every proposed bound `B`,
there is some `n` with discrepancy exceeding `B`.
-/
theorem not_boundedDiscrepancyAlong_iff_forall_exists_discrepancy_gt (g : ℕ → ℤ) (d : ℕ) :
    (¬ BoundedDiscrepancyAlong g d) ↔ (∀ B : ℕ, ∃ n : ℕ, B < discrepancy g d n) := by
  classical
  constructor
  · intro h B
    by_contra h'
    -- `h'` says: for this `B`, we do *not* have an `n` with `B < discrepancy g d n`.
    -- Hence all discrepancies are ≤ `B`, contradicting `h`.
    have h_le : ∀ n : ℕ, discrepancy g d n ≤ B := by
      intro n
      -- If `discrepancy g d n ≤ B` failed, we'd have `B < discrepancy g d n`.
      have : ¬ B < discrepancy g d n := by
        intro hn
        exact h' ⟨n, hn⟩
      exact le_of_not_gt this
    exact h ⟨B, h_le⟩
  · intro h
    intro hbd
    rcases hbd with ⟨B, hB⟩
    rcases h B with ⟨n, hn⟩
    exact (not_lt_of_ge (hB n)) hn

/-- The same unboundedness normal form, but phrased using `Int.natAbs (apSum …)`.

This is often more convenient because many reduction steps work with raw AP sums first and only
introduce the `discrepancy` wrapper later.
-/
theorem not_boundedDiscrepancyAlong_iff_forall_exists_natAbs_apSum_gt (g : ℕ → ℤ) (d : ℕ) :
    (¬ BoundedDiscrepancyAlong g d) ↔ (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSum g d n)) := by
  -- `discrepancy` is definitional.
  simpa [discrepancy] using (not_boundedDiscrepancyAlong_iff_forall_exists_discrepancy_gt (g := g) (d := d))

/-- Unboundedness normal form for `BoundedDiscOffset`. -/
theorem not_boundedDiscOffset_iff_forall_exists_discOffset_gt (f : ℕ → ℤ) (d m : ℕ) :
    (¬ BoundedDiscOffset f d m) ↔ (∀ B : ℕ, ∃ n : ℕ, B < discOffset f d m n) := by
  classical
  constructor
  · intro h B
    by_contra h'
    have h_le : ∀ n : ℕ, discOffset f d m n ≤ B := by
      intro n
      have : ¬ B < discOffset f d m n := by
        intro hn
        exact h' ⟨n, hn⟩
      exact le_of_not_gt this
    exact h ⟨B, h_le⟩
  · intro h
    intro hbd
    rcases hbd with ⟨B, hB⟩
    rcases h B with ⟨n, hn⟩
    exact (not_lt_of_ge (hB n)) hn

/-- The same unboundedness normal form, but phrased using `Int.natAbs (apSumOffset …)`.

This version is frequently the tightest statement one gets directly out of a reduction step.
-/
theorem not_boundedDiscOffset_iff_forall_exists_natAbs_apSumOffset_gt (f : ℕ → ℤ) (d m : ℕ) :
    (¬ BoundedDiscOffset f d m) ↔ (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f d m n)) := by
  -- `discOffset` is definitional.
  simpa [discOffset] using (not_boundedDiscOffset_iff_forall_exists_discOffset_gt (f := f) (d := d) (m := m))

/-- `∀B, ∃n` witness normal form: `discOffset` vs raw `natAbs (apSumOffset …)`.

This is a tiny definitional lemma, but it comes up often when a reduction step is proved using
raw sums first and only later wrapped into `discOffset`.
-/
theorem forall_exists_natAbs_apSumOffset_gt_iff_forall_exists_discOffset_gt (f : ℕ → ℤ) (d m : ℕ) :
    (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f d m n)) ↔
      (∀ B : ℕ, ∃ n : ℕ, B < discOffset f d m n) := by
  -- `discOffset` is definitional.
  simp [discOffset]

/-- `∀B, ∃n` witness normal form: `discrepancy` vs raw `natAbs (apSum …)`.

As above, this is just definitional unfolding.
-/
theorem forall_exists_natAbs_apSum_gt_iff_forall_exists_discrepancy_gt (g : ℕ → ℤ) (d : ℕ) :
    (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSum g d n)) ↔
      (∀ B : ℕ, ∃ n : ℕ, B < discrepancy g d n) := by
  simp [discrepancy]

/-- Offset sum with zero offset is just the original AP sum. -/
theorem apSumOffset_zero (f : ℕ → ℤ) (d n : ℕ) : apSumOffset f d 0 n = apSum f d n := by
  -- `apSumOffset` is defined as an `apSum` of a shifted sequence.
  simp [apSumOffset_eq_apSum_shift_add]

/-- Discrepancy form of `apSumOffset_zero`. -/
theorem discOffset_zero (f : ℕ → ℤ) (d n : ℕ) : discOffset f d 0 n = discrepancy f d n := by
  simp [discOffset, discrepancy, apSumOffset_zero]

/-- Zero-offset for a shifted sequence: `apSumOffset (shift f m) d 0 = apSumOffset f d m`.

This is a small convenience lemma that avoids repeatedly unfolding `apSumOffset_zero`.
-/
theorem apSumOffset_shift_zero (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset (fun k => f (k + m * d)) d 0 n = apSumOffset f d m n := by
  -- Left: zero offset is just an AP sum of the shifted sequence; right: definition of `apSumOffset`.
  simp [apSumOffset_zero, apSumOffset_eq_apSum_shift_add]

/-- Discrepancy form of `apSumOffset_shift_zero`. -/
theorem discOffset_shift_zero (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset (fun k => f (k + m * d)) d 0 n = discOffset f d m n := by
  simp [discOffset, apSumOffset_shift_zero]

/-- Bridge lemma: `apSumOffset` can be rewritten to an `apSum` for the derived sequence. -/
theorem apSumOffset_eq_apSum (out : ReductionOutput f) (n : ℕ) :
    apSumOffset f out.d out.m n = apSum out.g out.d n := by
  simpa using (out.apSum_eq_apSumOffset (f := f) (n := n)).symm

/-- Unfold the offset AP sum in `out` as a difference of two prefix sums of the original sequence.

This is just `apSumOffset_eq_sub`, specialized to the parameters bundled in `out`.
-/
theorem apSumOffset_eq_sub_apSum (out : ReductionOutput f) (n : ℕ) :
    apSumOffset f out.d out.m n = apSum f out.d (out.m + n) - apSum f out.d out.m := by
  simp [apSumOffset_eq_sub]

/-- Unfold the *offset discrepancy* in `out` as the absolute value of a difference of prefix sums.

This is the `discOffset` analogue of `apSumOffset_eq_sub_apSum`.
-/
theorem discOffset_eq_natAbs_sub_apSum (out : ReductionOutput f) (n : ℕ) :
    discOffset f out.d out.m n =
      Int.natAbs (apSum f out.d (out.m + n) - apSum f out.d out.m) := by
  -- `discOffset` is definitional, and `apSumOffset_eq_sub_apSum` gives the prefix-sum normal form.
  simp [discOffset, out.apSumOffset_eq_sub_apSum (f := f) (n := n)]

/-- Absolute offset AP sum, unfolded as a `natAbs` of a difference of prefix sums. -/
theorem natAbs_apSumOffset_eq_natAbs_sub_apSum (out : ReductionOutput f) (n : ℕ) :
    Int.natAbs (apSumOffset f out.d out.m n) =
      Int.natAbs (apSum f out.d (out.m + n) - apSum f out.d out.m) := by
  -- Just rewrite by `apSumOffset_eq_sub_apSum`.
  simp [out.apSumOffset_eq_sub_apSum (f := f) (n := n)]

/-- Unfold `apSum out.g out.d` as a difference of two prefix sums of `f`.

This is the common normal form when you want to “push” a statement about the reduced
sequence back to the original one.
-/
theorem apSum_eq_sub_apSum (out : ReductionOutput f) (n : ℕ) :
    apSum out.g out.d n = apSum f out.d (out.m + n) - apSum f out.d out.m := by
  -- First rewrite `apSum out.g` to `apSumOffset`, then unfold.
  simpa [out.apSum_contract] using (out.apSumOffset_eq_sub_apSum (f := f) (n := n)).symm

/-- Discrepancy of the reduced sequence, unfolded as a `natAbs` of a difference of prefix sums.

This is a convenient consumer lemma: downstream steps often reason about differences of
prefix sums directly.
-/
theorem discrepancy_eq_natAbs_sub_apSum (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n =
      Int.natAbs (apSum f out.d (out.m + n) - apSum f out.d out.m) := by
  -- `discrepancy` is `natAbs` of `apSum`; rewrite using `apSum_eq_sub_apSum`.
  simp [discrepancy, out.apSum_eq_sub_apSum]

/-- Re-associate offsets, specialized to the `ReductionOutput` shift.

This is the consumer form of `Tao2015.apSumOffset_add`: shifting `f` by `(out.m+m₂)*d`
can be seen as taking an offset sum of the *already-shifted* sequence `out.g`.
-/
theorem apSumOffset_add_right (out : ReductionOutput f) (m₂ n : ℕ) :
    apSumOffset f out.d (out.m + m₂) n = apSumOffset out.g out.d m₂ n := by
  -- First re-associate offsets on `f`, then rewrite the shifted sequence to `out.g`.
  simpa [Tao2015.apSumOffset_add, out.g_eq]

/-- The reverse orientation of `apSumOffset_add_right`.

This is often convenient when you are *already* working with the reduced sequence `out.g`
but want to phrase an expression back in terms of the original `f`.
-/
theorem apSumOffset_eq_apSumOffset_add_right (out : ReductionOutput f) (m₂ n : ℕ) :
    apSumOffset out.g out.d m₂ n = apSumOffset f out.d (out.m + m₂) n := by
  simpa using (out.apSumOffset_add_right (f := f) (m₂ := m₂) (n := n)).symm

/-- Discrepancy form of `apSumOffset_add_right`. -/
theorem discOffset_add_right (out : ReductionOutput f) (m₂ n : ℕ) :
    discOffset f out.d (out.m + m₂) n = discOffset out.g out.d m₂ n := by
  simp [discOffset, out.apSumOffset_add_right (f := f) (m₂ := m₂) (n := n)]

/-- Reverse orientation of `discOffset_add_right`. -/
theorem discOffset_eq_discOffset_add_right (out : ReductionOutput f) (m₂ n : ℕ) :
    discOffset out.g out.d m₂ n = discOffset f out.d (out.m + m₂) n := by
  simpa using (out.discOffset_add_right (f := f) (m₂ := m₂) (n := n)).symm

/-!
### Zero-offset specializations (add-right form)

The lemmas `apSumOffset_add_right` / `discOffset_add_right` are most often used with `m₂ = 0`.
We record those special cases explicitly, since they become the “one-hop” bridge between
`apSumOffset f out.d out.m` and the offset sums of the reduced sequence `out.g`.
-/

/-- Special case of `apSumOffset_add_right` with `m₂ = 0`. -/
theorem apSumOffset_eq_apSumOffset_reduced_zero (out : ReductionOutput f) (n : ℕ) :
    apSumOffset f out.d out.m n = apSumOffset out.g out.d 0 n := by
  simpa using (out.apSumOffset_add_right (f := f) (m₂ := 0) (n := n))

/-- Reverse orientation of `apSumOffset_eq_apSumOffset_reduced_zero`. -/
theorem apSumOffset_reduced_zero_eq (out : ReductionOutput f) (n : ℕ) :
    apSumOffset out.g out.d 0 n = apSumOffset f out.d out.m n := by
  simpa using (out.apSumOffset_eq_apSumOffset_reduced_zero (f := f) (n := n)).symm

/-- Special case of `discOffset_add_right` with `m₂ = 0`. -/
theorem discOffset_eq_discOffset_reduced_zero (out : ReductionOutput f) (n : ℕ) :
    discOffset f out.d out.m n = discOffset out.g out.d 0 n := by
  simpa using (out.discOffset_add_right (f := f) (m₂ := 0) (n := n))

/-- Reverse orientation of `discOffset_eq_discOffset_reduced_zero`. -/
theorem discOffset_reduced_zero_eq (out : ReductionOutput f) (n : ℕ) :
    discOffset out.g out.d 0 n = discOffset f out.d out.m n := by
  simpa using (out.discOffset_eq_discOffset_reduced_zero (f := f) (n := n)).symm

/-!
### Composing the first reduction with an additional shift

After producing a reduction output `out`, downstream stages often want to “shift again” by a
multiple of the *same* common difference `out.d`.

Instead of manually re-proving the bridge/contract fields each time, we provide a small helper
constructor that composes `out` with a further shift.
-/

/-- Shift the reduced sequence `out.g` by an additional multiple `m₂*out.d`, and repackage it as a
new `ReductionOutput` for the original sequence `f`.

The new parameters are:
- same `d`
- new offset multiplier `m := out.m + m₂`
- derived sequence `g' k := out.g (k + m₂*out.d)`

All interface fields are filled using the existing bridge lemmas in this file.
-/
noncomputable def shiftRight (out : ReductionOutput f) (m₂ : ℕ) : ReductionOutput f := by
  classical
  -- Define the further-shifted reduced sequence.
  let g' : ℕ → ℤ := fun k => out.g (k + m₂ * out.d)
  have hg' : IsSignSequence g' :=
    Tao2015.IsSignSequence.shift_add_mul (f := out.g) out.hg m₂ out.d
  -- `g'` is also a shift of `f` by `(out.m+m₂)*out.d`.
  have hg'_eq : g' = fun k => f (k + (out.m + m₂) * out.d) := by
    funext k
    simp [g', out.g_eq, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm]
  -- Build the new reduction output.
  refine ReductionOutput.mkShift (f := f) (d := out.d) (m := out.m + m₂) (hd := out.hd)
    (g := g') (hg := hg') (hgEq := hg'_eq)

namespace shiftRight

/-- The shifted reduction output has the same `d`. -/
@[simp] theorem d (out : ReductionOutput f) (m₂ : ℕ) : (out.shiftRight (f := f) m₂).d = out.d := by
  rfl

/-- The shifted reduction output's offset multiplier is `out.m + m₂`. -/
@[simp] theorem m (out : ReductionOutput f) (m₂ : ℕ) : (out.shiftRight (f := f) m₂).m = out.m + m₂ := by
  rfl

/-- Pointwise description of the shifted derived sequence. -/
@[simp] theorem g_apply (out : ReductionOutput f) (m₂ k : ℕ) :
    (out.shiftRight (f := f) m₂).g k = out.g (k + m₂ * out.d) := by
  rfl

/-- The key bridge rule for `shiftRight`: it rewrites an offset sum at `out.m+m₂` into an offset sum
of the already-reduced sequence `out.g` at offset `m₂`.
-/
theorem apSumOffset_add_right (out : ReductionOutput f) (m₂ n : ℕ) :
    apSumOffset f out.d (out.m + m₂) n = apSumOffset out.g out.d m₂ n :=
  out.apSumOffset_add_right (f := f) (m₂ := m₂) (n := n)

/-- Discrepancy form of `shiftRight.apSumOffset_add_right`. -/
theorem discOffset_add_right (out : ReductionOutput f) (m₂ n : ℕ) :
    discOffset f out.d (out.m + m₂) n = discOffset out.g out.d m₂ n := by
  simp [discOffset, apSumOffset_add_right (f := f) (out := out) (m₂ := m₂) (n := n)]

/-- The derived sequence of `out.shiftRight m₂` is literally a shift of `out.g` by `m₂*out.d`.

This lemma makes it easy to reuse the basic shift/offset rewrite theorems for the *second* shift.
-/
theorem g_eq_shift (out : ReductionOutput f) (m₂ : ℕ) :
    (out.shiftRight (f := f) m₂).g = fun k => out.g (k + m₂ * out.d) := by
  rfl

/-- The derived sequence of `out.shiftRight m₂`, rewritten directly as a shift of the original
sequence `f` by the *bundled* offset `(out.m + m₂) * out.d`.

This is just the `g_eq` field of the newly constructed `ReductionOutput`, but it’s convenient to
have as a named lemma for downstream reductions.
-/
theorem g_eq_f_shift (out : ReductionOutput f) (m₂ : ℕ) :
    (out.shiftRight (f := f) m₂).g = fun k => f (k + (out.m + m₂) * out.d) := by
  simpa using (out.shiftRight (f := f) m₂).g_eq

/-- Discrepancy of the derived sequence of `out.shiftRight m₂`, rewritten as an offset discrepancy
of the already-reduced sequence `out.g`.

This is the “second-hop” version of the main bridge lemma: it lets later stages talk about
`discOffset out.g out.d m₂` instead of `discrepancy (out.shiftRight m₂).g`.
-/
theorem discrepancy_eq_discOffset (out : ReductionOutput f) (m₂ n : ℕ) :
    discrepancy (out.shiftRight (f := f) m₂).g out.d n = discOffset out.g out.d m₂ n := by
  -- This is the standard shift ↔ offset lemma, applied to the sequence `out.g`.
  simpa [g_eq_shift (f := f) (out := out) (m₂ := m₂)] using
    (Tao2015.discrepancy_shift_add_mul_eq_discOffset (f := out.g) (d := out.d) (m := m₂) (n := n))

/-- AP-sum bridge for `out.shiftRight m₂`, rewritten with the original sequence `f`.

This is just the generic `ReductionOutput.apSum_eq_apSumOffset` lemma applied to
`out.shiftRight m₂`, but it is convenient to have the parameters in “paper form”
(`out.m + m₂`).
-/
@[simp] theorem apSum_eq_apSumOffset_f (out : ReductionOutput f) (m₂ n : ℕ) :
    apSum (out.shiftRight (f := f) m₂).g out.d n = apSumOffset f out.d (out.m + m₂) n := by
  -- Reduce to the bundled bridge lemma of the new reduction output.
  simpa using
    (ReductionOutput.apSum_eq_apSumOffset (f := f) (out := out.shiftRight (f := f) m₂) (n := n))

/-- Discrepancy bridge for `out.shiftRight m₂`, rewritten with the original sequence `f`. -/
@[simp] theorem discrepancy_eq_discOffset_f (out : ReductionOutput f) (m₂ n : ℕ) :
    discrepancy (out.shiftRight (f := f) m₂).g out.d n = discOffset f out.d (out.m + m₂) n := by
  -- Combine the standard `ReductionOutput` discrepancy bridge with the simp facts about `shiftRight`.
  simpa using
    (ReductionOutput.discrepancy_eq_discOffset (f := f) (out := out.shiftRight (f := f) m₂) (n := n))

/-- Fixed-step discrepancy predicate for `out.shiftRight m₂`, phrased as a `discOffset` witness for `f`. -/
theorem hasDiscrepancyAtLeastAlong_iff_exists_discOffset_gt_f (out : ReductionOutput f) (m₂ C : ℕ) :
    HasDiscrepancyAtLeastAlong (out.shiftRight (f := f) m₂).g out.d C ↔
      (∃ n : ℕ, discOffset f out.d (out.m + m₂) n > C) := by
  -- This is the generic `ReductionOutput` lemma, with parameters normalized.
  simpa using
    (ReductionOutput.hasDiscrepancyAtLeastAlong_iff_discOffset (f := f)
      (out := out.shiftRight (f := f) m₂) (C := C))

end shiftRight

/-!
### Boundedness of offset discrepancy across the bundled shift

After producing a reduction output `out`, later stages often want to work with offset sums at
`out.m + m₂` for the original sequence `f`.  The lemma `shiftRight.discOffset_add_right` already
rewrites these pointwise to offset sums of the reduced sequence `out.g`.

The next lemmas package this rewriting at the *boundedness* level (`∃ B, ∀ n`).
-/

theorem boundedDiscOffset_add_right_iff (out : ReductionOutput f) (m₂ : ℕ) :
    BoundedDiscOffset f out.d (out.m + m₂) ↔ BoundedDiscOffset out.g out.d m₂ := by
  -- This is just `boundedDiscOffset_add`, using that `out.g` is the shift of `f` by `out.m*out.d`.
  simpa [out.g_eq] using
    (boundedDiscOffset_add (f := f) (d := out.d) (m₁ := out.m) (m₂ := m₂))

theorem not_boundedDiscOffset_add_right_iff (out : ReductionOutput f) (m₂ : ℕ) :
    (¬ BoundedDiscOffset f out.d (out.m + m₂)) ↔ (¬ BoundedDiscOffset out.g out.d m₂) := by
  simpa [boundedDiscOffset_add_right_iff (f := f) (out := out) (m₂ := m₂)]

/-!
### Boundedness and witness transport across the bundled shift

The lemmas `apSumOffset_add_right` / `discOffset_add_right` rewrite an offset expression of the
original sequence `f` into an offset expression of the reduced sequence `out.g`.

Downstream stages often need this not just pointwise, but at the level of *boundedness* (`∃ B, ∀ n`)
or the explicit *unboundedness witness* normal form (`∀ B, ∃ n`).
-/

/-- Bounding all offset discrepancies of `f` at offset `out.m + m₂` is equivalent to bounding all
offset discrepancies of `out.g` at offset `m₂`.

This is just the `BoundedDiscOffset`-level transport version of `discOffset_add_right`.
-/
theorem boundedDiscOffset_add_right (out : ReductionOutput f) (m₂ : ℕ) :
    BoundedDiscOffset f out.d (out.m + m₂) ↔ BoundedDiscOffset out.g out.d m₂ := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    simpa [out.discOffset_add_right (f := f) (m₂ := m₂) (n := n)] using hB n
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- rewrite in the reverse direction
    simpa [out.discOffset_add_right (f := f) (m₂ := m₂) (n := n)] using hB n

/-- Unboundedness witness transport across the bundled shift (explicit normal form).

This is the “∀B, ∃n, B < …” analogue of `boundedDiscOffset_add_right`.
-/
theorem forall_exists_discOffset_gt_add_right_iff (out : ReductionOutput f) (m₂ : ℕ) :
    (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d (out.m + m₂) n) ↔
      (∀ B : ℕ, ∃ n : ℕ, B < discOffset out.g out.d m₂ n) := by
  constructor
  · intro h B
    rcases h B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.discOffset_add_right (f := f) (m₂ := m₂) (n := n)] using hn
  · intro h B
    rcases h B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- rewrite in the reverse direction
    simpa [out.discOffset_add_right (f := f) (m₂ := m₂) (n := n)] using hn

/-!
### Additional witness-transport lemmas (add-right form)

The preceding lemmas transport *boundedness* (`∃ B, ∀ n`) and its explicit negation normal form
(`∀ B, ∃ n`). In early Tao-pipeline stages we also want to transport the intermediate
“large discrepancy along a fixed step size” predicate `HasDiscrepancyAtLeastAlong`.

These are small glue lemmas, but they let later stages compose reductions without constantly
re-expanding the definitions of `apSumOffset`/`discOffset`.
-/

/-- Existence transport for strict witnesses across the bundled shift (discOffset form). -/
theorem exists_discOffset_gt_add_right_iff (out : ReductionOutput f) (m₂ C : ℕ) :
    (∃ n : ℕ, discOffset f out.d (out.m + m₂) n > C) ↔
      (∃ n : ℕ, discOffset out.g out.d m₂ n > C) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.discOffset_add_right (f := f) (m₂ := m₂) (n := n)] using hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- reverse orientation
    simpa [out.discOffset_add_right (f := f) (m₂ := m₂) (n := n)] using hn

/-- If there is a large offset discrepancy witness for `f` at offset `out.m+m₂`, then there is a
large fixed-step discrepancy witness for the *shifted* reduced sequence.

This is a convenient one-way lemma used when composing reductions.
-/
theorem hasDiscrepancyAtLeastAlong_shifted_of_exists_discOffset_gt_add_right (out : ReductionOutput f)
    (m₂ C : ℕ) :
    (∃ n : ℕ, discOffset f out.d (out.m + m₂) n > C) →
      HasDiscrepancyAtLeastAlong (fun k => out.g (k + m₂ * out.d)) out.d C := by
  intro h
  -- Transport to a witness for `discOffset out.g out.d m₂`.
  have : (∃ n : ℕ, discOffset out.g out.d m₂ n > C) :=
    (out.exists_discOffset_gt_add_right_iff (f := f) (m₂ := m₂) (C := C)).1 h
  rcases this with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  -- Rewrite `discOffset` as discrepancy of a shifted sequence.
  -- `HasDiscrepancyAtLeastAlong` is phrased in terms of `natAbs (apSum …)`.
  have : discrepancy (fun k => out.g (k + m₂ * out.d)) out.d n > C := by
    simpa [Tao2015.discOffset_eq_discrepancy_shift_add_mul (f := out.g) (d := out.d)
      (m := m₂) (n := n)] using hn
  simpa [HasDiscrepancyAtLeastAlong, discrepancy] using this

/-- Reverse direction: a large discrepancy witness for the shifted reduced sequence yields a large
`discOffset` witness for `f` at offset `out.m+m₂`.

This is another common “pipeline hop”: later reductions may naturally produce witnesses for a
shifted version of `out.g`.
-/
theorem exists_discOffset_gt_add_right_of_hasDiscrepancyAtLeastAlong_shifted (out : ReductionOutput f)
    (m₂ C : ℕ) :
    HasDiscrepancyAtLeastAlong (fun k => out.g (k + m₂ * out.d)) out.d C →
      (∃ n : ℕ, discOffset f out.d (out.m + m₂) n > C) := by
  rintro ⟨n, hn⟩
  -- Turn `natAbs (apSum …)` into `discrepancy`.
  have hn' : discrepancy (fun k => out.g (k + m₂ * out.d)) out.d n > C := by
    simpa [HasDiscrepancyAtLeastAlong, discrepancy] using hn
  -- Rewrite to `discOffset out.g out.d m₂ n`.
  have : discOffset out.g out.d m₂ n > C := by
    simpa [Tao2015.discrepancy_shift_add_mul_eq_discOffset (f := out.g) (d := out.d)
      (m := m₂) (n := n)] using hn'
  -- Transport back to `f` using `discOffset_add_right`.
  refine (out.exists_discOffset_gt_add_right_iff (f := f) (m₂ := m₂) (C := C)).2 ⟨n, this⟩

/-!
### Composing shifts

A common pattern in the Tao pipeline is to *shift again* after a first reduction step.

The next definition packages this as a new `ReductionOutput` with the same common difference `d`
but an updated offset multiplier `m := out.m + m₂`.

This lets downstream stages “move the basepoint” without leaving the reduction interface.
-/

/-- Shift the reduced sequence `out.g` by an additional multiple `m₂*out.d`, and repackage the
result as a `ReductionOutput` for the original sequence `f`.

Intuitively: if `out.g k = f (k + out.m*out.d)`, then
`(shiftRight out m₂).g k = f (k + (out.m+m₂)*out.d)`.
-/
noncomputable def shiftRight (out : ReductionOutput f) (m₂ : ℕ) : ReductionOutput f := by
  classical
  -- Define the new reduced sequence as a shift of the old one.
  let g' : ℕ → ℤ := fun k => out.g (k + m₂ * out.d)
  have hg' : IsSignSequence g' := Tao2015.IsSignSequence.shift_add_mul (f := out.g) out.hg m₂ out.d
  have hgEq : g' = fun k => f (k + (out.m + m₂) * out.d) := by
    funext k
    -- Unfold `g'` and the defining equation for `out.g`, then simplify arithmetic.
    simp [g', out.g_eq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_mul]
  -- Use the generic “shift constructor”.
  exact ReductionOutput.mkShift (f := f) (d := out.d) (m := out.m + m₂) (hd := out.hd)
    (g := g') (hg := hg') (hgEq := hgEq)

/-- `shiftRight₀` and `shiftRight` are definitionally the same combinator.

We keep both names for historical reasons; prefer `shiftRight` in new code.
-/
@[simp] theorem shiftRight₀_eq_shiftRight (out : ReductionOutput f) (m₂ : ℕ) :
    out.shiftRight₀ (f := f) m₂ = out.shiftRight (f := f) m₂ := by
  classical
  -- The two definitions package the same shifted sequence; proof fields agree by proof irrelevance.
  ext
  · rfl
  · rfl
  · apply Subsingleton.elim
  · funext k
    rfl
  · apply Subsingleton.elim
  · apply Subsingleton.elim
  · apply Subsingleton.elim
  · apply Subsingleton.elim

/-- The underlying function of `shiftRight` is just an extra shift of `out.g`. -/
@[simp] theorem shiftRight_g (out : ReductionOutput f) (m₂ : ℕ) :
    (out.shiftRight (f := f) m₂).g = fun k => out.g (k + m₂ * out.d) := by
  classical
  -- `shiftRight` was defined via `let g' := ...`.
  rfl

/-- The updated offset multiplier in `shiftRight` is `out.m + m₂`. -/
@[simp] theorem shiftRight_m (out : ReductionOutput f) (m₂ : ℕ) :
    (out.shiftRight (f := f) m₂).m = out.m + m₂ := by
  classical
  rfl

/-- The common difference in `shiftRight` is unchanged. -/
@[simp] theorem shiftRight_d (out : ReductionOutput f) (m₂ : ℕ) :
    (out.shiftRight (f := f) m₂).d = out.d := by
  classical
  rfl

/-- The positivity witness `hd` is unchanged by `shiftRight`. -/
@[simp] theorem shiftRight_hd (out : ReductionOutput f) (m₂ : ℕ) :
    (out.shiftRight (f := f) m₂).hd = out.hd := by
  classical
  rfl

/-!
### Tiny normalization lemmas for `shiftRight`

These are intentionally small, but they eliminate a lot of arithmetic clutter in downstream
stages that repeatedly “move the basepoint”.
-/

/-- Shifting by zero does not change the bundled offset multiplier. -/
@[simp] theorem shiftRight_zero_m (out : ReductionOutput f) :
    (out.shiftRight (f := f) 0).m = out.m := by
  simp

/-- Shifting by zero does not change the reduced sequence. -/
@[simp] theorem shiftRight_zero_g (out : ReductionOutput f) :
    (out.shiftRight (f := f) 0).g = out.g := by
  funext k
  simp [ReductionOutput.shiftRight_g]

/-- Pointwise form of `shiftRight_zero_g`. -/
@[simp] theorem shiftRight_zero_g_apply (out : ReductionOutput f) (k : ℕ) :
    (out.shiftRight (f := f) 0).g k = out.g k := by
  simpa using congrArg (fun g => g k) (out.shiftRight_zero_g (f := f))

/-- Shifting by zero does not change the full `ReductionOutput`. -/
@[simp] theorem shiftRight_zero (out : ReductionOutput f) : out.shiftRight (f := f) 0 = out := by
  -- Prove equality by extensionality on the core data.
  ext
  · simp
  · simp
  · funext k
    simp [ReductionOutput.shiftRight_g]

/-- Shifting twice composes by addition at the level of the underlying function. -/
@[simp] theorem shiftRight_shiftRight_g_apply (out : ReductionOutput f) (m₁ m₂ k : ℕ) :
    ((out.shiftRight (f := f) m₁).shiftRight (f := f) m₂).g k = out.g (k + (m₁ + m₂) * out.d) := by
  -- Unfold each `shiftRight` as an extra shift and simplify arithmetic.
  simp [ReductionOutput.shiftRight_g, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Consequently, the “shift by `m₁` then by `m₂`” function equals the “shift by `m₁+m₂`” function. -/
@[simp] theorem shiftRight_shiftRight_g (out : ReductionOutput f) (m₁ m₂ : ℕ) :
    ((out.shiftRight (f := f) m₁).shiftRight (f := f) m₂).g = fun k => out.g (k + (m₁ + m₂) * out.d) := by
  funext k
  simpa using out.shiftRight_shiftRight_g_apply (f := f) m₁ m₂ k

/-- Shifting twice composes by addition at the level of the bundled offset multiplier. -/
@[simp] theorem shiftRight_shiftRight_m (out : ReductionOutput f) (m₁ m₂ : ℕ) :
    ((out.shiftRight (f := f) m₁).shiftRight (f := f) m₂).m = out.m + m₁ + m₂ := by
  -- `shiftRight_m` computes the bundled offset multiplier.
  simp [Nat.add_assoc]

/-- Shifting twice does not change the common difference. -/
@[simp] theorem shiftRight_shiftRight_d (out : ReductionOutput f) (m₁ m₂ : ℕ) :
    ((out.shiftRight (f := f) m₁).shiftRight (f := f) m₂).d = out.d := by
  simp

/-- `shiftRight` twice exposes the underlying shift from the original sequence `f`. -/
@[simp] theorem shiftRight_shiftRight_g_eq (out : ReductionOutput f) (m₁ m₂ : ℕ) :
    ((out.shiftRight (f := f) m₁).shiftRight (f := f) m₂).g =
      fun k => f (k + (out.m + m₁ + m₂) * out.d) := by
  -- Use the simp-friendly `g_eq` lemma for `shiftRight` and associate additions.
  simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-!
### Associativity helpers for `shiftRight`

Downstream steps often want to treat `shiftRight` as an associative operation on the offset
multiplier.  Proving equality of `ReductionOutput` structures is annoying (proof fields), so we
provide function-level and parameter-level equalities instead.
-/

/-- Shifting by `m₁` then by `m₂` agrees (pointwise) with shifting by `m₁+m₂`. -/
@[simp] theorem shiftRight_add_g_apply (out : ReductionOutput f) (m₁ m₂ k : ℕ) :
    ((out.shiftRight (f := f) m₁).shiftRight (f := f) m₂).g k =
      (out.shiftRight (f := f) (m₁ + m₂)).g k := by
  -- Both sides simplify to `out.g (k + (m₁+m₂)*out.d)`.
  simp [ReductionOutput.shiftRight_g]

/-- Function-extensional form of `shiftRight_add_g_apply`. -/
@[simp] theorem shiftRight_add_g (out : ReductionOutput f) (m₁ m₂ : ℕ) :
    ((out.shiftRight (f := f) m₁).shiftRight (f := f) m₂).g =
      (out.shiftRight (f := f) (m₁ + m₂)).g := by
  funext k
  simpa using out.shiftRight_add_g_apply (f := f) m₁ m₂ k

/-- The bundled offset multipliers agree: “shift by `m₁` then by `m₂`” equals “shift by `m₁+m₂`”. -/
@[simp] theorem shiftRight_add_m (out : ReductionOutput f) (m₁ m₂ : ℕ) :
    ((out.shiftRight (f := f) m₁).shiftRight (f := f) m₂).m =
      (out.shiftRight (f := f) (m₁ + m₂)).m := by
  -- Both sides reduce to `out.m + m₁ + m₂`.
  simp [Nat.add_assoc]

/-- Extensionality for `ReductionOutput`: to prove two outputs equal, it suffices to show the
core data (`d`,`m`,`g`) agree.

All other fields are proofs, hence propositionally irrelevant.
-/
@[ext] theorem ext_dmg (out₁ out₂ : ReductionOutput f)
    (hd : out₁.d = out₂.d) (hm : out₁.m = out₂.m) (hg : out₁.g = out₂.g) : out₁ = out₂ := by
  classical
  -- Unpack both structures; after rewriting the data fields, the remaining proof fields match by
  -- proof irrelevance.
  cases out₁ with
  | mk d₁ m₁ hd₁ g₁ hg₁ g_eq₁ apSum₁ contract₁ =>
    cases out₂ with
    | mk d₂ m₂ hd₂ g₂ hg₂ g_eq₂ apSum₂ contract₂ =>
      -- Rewrite by the data equalities.
      cases hd
      cases hm
      cases hg
      -- Now we are comparing two records whose non-proof fields are definitional equal.
      -- The remaining fields are proofs in `Prop`, so `Subsingleton.elim` closes them.
      simp

/-- `shiftRight` is associative at the level of the full `ReductionOutput` structure.

This is the cleanest consumer-facing lemma: downstream code can rewrite nested `shiftRight`s into a
single shift without manually transporting proof fields.
-/
theorem shiftRight_add (out : ReductionOutput f) (m₁ m₂ : ℕ) :
    (out.shiftRight (f := f) m₁).shiftRight (f := f) m₂ = out.shiftRight (f := f) (m₁ + m₂) := by
  -- Use extensionality on the core data.
  ext
  · simp
  · simp [Nat.add_assoc]
  · -- underlying reduced sequence agrees pointwise
    funext k
    simp [ReductionOutput.shiftRight_g, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- A simp-friendly form of `shiftRight_add`. -/
@[simp] theorem shiftRight_shiftRight (out : ReductionOutput f) (m₁ m₂ : ℕ) :
    (out.shiftRight (f := f) m₁).shiftRight (f := f) m₂ = out.shiftRight (f := f) (m₁ + m₂) := by
  simpa using out.shiftRight_add (f := f) (m₁ := m₁) (m₂ := m₂)

/-- Three successive shifts collapse to a single shift (simp helper). -/
@[simp] theorem shiftRight_shiftRight_shiftRight (out : ReductionOutput f) (m₁ m₂ m₃ : ℕ) :
    (((out.shiftRight (f := f) m₁).shiftRight (f := f) m₂).shiftRight (f := f) m₃) =
      out.shiftRight (f := f) (m₁ + m₂ + m₃) := by
  -- Reassociate using `shiftRight_shiftRight` twice.
  simp [Nat.add_assoc]

/-- Consumer lemma: the AP-sum bridge for the double shift can be stated using the combined shift.

This avoids any dependency on later “bridge” lemmas; it is just congruence along the function-level
associativity lemma `shiftRight_add_g`.
-/
@[simp] theorem apSum_shiftRight_shiftRight_eq_apSum_shiftRight_add (out : ReductionOutput f) (m₁ m₂ n : ℕ) :
    apSum (((out.shiftRight (f := f) m₁).shiftRight (f := f) m₂).g) out.d n =
      apSum ((out.shiftRight (f := f) (m₁ + m₂)).g) out.d n := by
  -- `shiftRight_add_g` identifies the underlying reduced sequences; apply `apSum` congruently.
  simpa using congrArg (fun g => apSum g out.d n) (out.shiftRight_add_g (f := f) (m₁ := m₁) (m₂ := m₂))

/-- Discrepancy analogue of `apSum_shiftRight_shiftRight_eq_apSum_shiftRight_add`.

As above, this is a pure congruence consequence of `shiftRight_add_g`.
-/
@[simp] theorem discrepancy_shiftRight_shiftRight_eq_discrepancy_shiftRight_add (out : ReductionOutput f) (m₁ m₂ n : ℕ) :
    discrepancy (((out.shiftRight (f := f) m₁).shiftRight (f := f) m₂).g) out.d n =
      discrepancy ((out.shiftRight (f := f) (m₁ + m₂)).g) out.d n := by
  simpa using congrArg (fun g => discrepancy g out.d n) (out.shiftRight_add_g (f := f) (m₁ := m₁) (m₂ := m₂))

/-!
### Tiny consumer lemmas for repeated shifts

These lemmas are mechanically derivable from the already-existing simp API, but having them as
named facts helps downstream stages avoid repeated `simp`-based bookkeeping.
-/

/-- Two successive shifts: the resulting AP sums rewrite to an offset sum of the original sequence
with the combined offset multiplier `out.m + m₁ + m₂`.
-/
@[simp] theorem apSum_shiftRight_shiftRight (out : ReductionOutput f) (m₁ m₂ n : ℕ) :
    apSum (((out.shiftRight (f := f) m₁).shiftRight (f := f) m₂).g) out.d n =
      apSumOffset f out.d (out.m + m₁ + m₂) n := by
  -- The generic bridge rule already gives `apSum … = apSumOffset …` for the bundled parameters.
  -- `simp` computes those parameters for the double-shift output.
  simpa [Nat.add_assoc] using
    (ReductionOutput.apSum_eq_apSumOffset (f := f)
      (out := (out.shiftRight (f := f) m₁).shiftRight (f := f) m₂) n)

/-- Two successive shifts: the resulting discrepancies rewrite to an offset discrepancy of the
original sequence with the combined offset multiplier `out.m + m₁ + m₂`.
-/
@[simp] theorem discrepancy_shiftRight_shiftRight (out : ReductionOutput f) (m₁ m₂ n : ℕ) :
    discrepancy (((out.shiftRight (f := f) m₁).shiftRight (f := f) m₂).g) out.d n =
      discOffset f out.d (out.m + m₁ + m₂) n := by
  simpa [Nat.add_assoc] using
    (ReductionOutput.discrepancy_eq_discOffset (f := f)
      (out := (out.shiftRight (f := f) m₁).shiftRight (f := f) m₂) n)

/-- Re-associate offsets across a first shift: an offset by `out.m + m₁ + m₂` for `f` is an offset
by `m₂` for the once-shifted sequence `out.shiftRight m₁`.
-/
@[simp] theorem apSumOffset_eq_apSumOffset_shiftRight (out : ReductionOutput f) (m₁ m₂ n : ℕ) :
    apSumOffset f out.d (out.m + m₁ + m₂) n =
      apSumOffset ((out.shiftRight (f := f) m₁).g) out.d m₂ n := by
  -- This is `apSumOffset_add_right`, but applied to the intermediate reduction output.
  simpa [Nat.add_assoc] using
    ((out.shiftRight (f := f) m₁).apSumOffset_add_right (f := f) (m₂ := m₂) (n := n))

/-- Discrepancy form of `apSumOffset_eq_apSumOffset_shiftRight`. -/
@[simp] theorem discOffset_eq_discOffset_shiftRight (out : ReductionOutput f) (m₁ m₂ n : ℕ) :
    discOffset f out.d (out.m + m₁ + m₂) n =
      discOffset ((out.shiftRight (f := f) m₁).g) out.d m₂ n := by
  -- `discOffset` is definitional; reuse the AP-sum statement.
  simp [discOffset, apSumOffset_eq_apSumOffset_shiftRight (f := f) (out := out) (m₁ := m₁) (m₂ := m₂) (n := n)]

/-- Pointwise form of `shiftRight_g`. -/
@[simp] theorem shiftRight_g_apply (out : ReductionOutput f) (m₂ k : ℕ) :
    (out.shiftRight (f := f) m₂).g k = out.g (k + m₂ * out.d) := by
  classical
  simp [ReductionOutput.shiftRight_g]

/-- `shiftRight` repackages the additional shift as a reduction output for `f`.

This lemma exposes the `g_eq` field of the constructed `ReductionOutput` in a simp-friendly way.
-/
@[simp] theorem shiftRight_g_eq (out : ReductionOutput f) (m₂ : ℕ) :
    (out.shiftRight (f := f) m₂).g = fun k => f (k + (out.m + m₂) * out.d) := by
  -- This is exactly the `g_eq` field of the repackaged output.
  simpa using (out.shiftRight (f := f) m₂).g_eq

/-- `shiftRight` satisfies the reduction bridge rule, stated directly for the repackaged sequence. -/
@[simp] theorem apSum_shiftRight (out : ReductionOutput f) (m₂ n : ℕ) :
    apSum (out.shiftRight (f := f) m₂).g out.d n = apSumOffset f out.d (out.m + m₂) n := by
  -- `ReductionOutput.apSum_eq_apSumOffset` already provides the bridge.
  simpa using (ReductionOutput.apSum_eq_apSumOffset (f := f) (out := out.shiftRight (f := f) m₂) n)

/-- Discrepancy bridge rule for `shiftRight`, stated directly for the repackaged sequence. -/
@[simp] theorem discrepancy_shiftRight (out : ReductionOutput f) (m₂ n : ℕ) :
    discrepancy (out.shiftRight (f := f) m₂).g out.d n = discOffset f out.d (out.m + m₂) n := by
  -- Same idea as `apSum_shiftRight`, but for the `natAbs` wrapper.
  simpa using (ReductionOutput.discrepancy_eq_discOffset (f := f) (out := out.shiftRight (f := f) m₂) n)

/-- `shiftRight` composes offsets at the level of AP sums: it rewrites to `apSumOffset` with the
combined offset multiplier `out.m + m₂`.
-/
@[simp] theorem apSum_shiftRight_eq_apSumOffset (out : ReductionOutput f) (m₂ n : ℕ) :
    apSum (fun k => out.g (k + m₂ * out.d)) out.d n = apSumOffset f out.d (out.m + m₂) n := by
  -- This is exactly the `apSum_contract` field of the constructed reduction output.
  simpa [ReductionOutput.shiftRight_g] using
    (out.shiftRight (f := f) m₂).apSum_contract n

/-- Discrepancy version of `apSum_shiftRight_eq_apSumOffset`. -/
@[simp] theorem discrepancy_shiftRight_eq_discOffset (out : ReductionOutput f) (m₂ n : ℕ) :
    discrepancy (fun k => out.g (k + m₂ * out.d)) out.d n = discOffset f out.d (out.m + m₂) n := by
  -- Both sides are definitional wrappers around `Int.natAbs`.
  simp [discrepancy, discOffset, out.apSum_shiftRight_eq_apSumOffset (f := f) (m₂ := m₂) (n := n)]

/-- Equivalence of boundedness notions across the reduction interface. -/
theorem boundedDiscrepancyAlong_iff_boundedDiscOffset (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d ↔ BoundedDiscOffset f out.d out.m := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- rewrite `discOffset` to the discrepancy of `out.g`
    simpa [out.discOffset_eq_discrepancy (f := f) (n := n)] using hB n
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- rewrite the discrepancy of `out.g` to `discOffset`
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n

/-- Convenience: convert `BoundedDiscOffset` to `BoundedDiscrepancyAlong` using the interface. -/
theorem boundedDiscrepancyAlong_of_boundedDiscOffset (out : ReductionOutput f) :
    BoundedDiscOffset f out.d out.m → BoundedDiscrepancyAlong out.g out.d :=
  (out.boundedDiscrepancyAlong_iff_boundedDiscOffset (f := f)).2

/-- Convenience: convert `BoundedDiscrepancyAlong` to `BoundedDiscOffset` using the interface. -/
theorem boundedDiscOffset_of_boundedDiscrepancyAlong (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d → BoundedDiscOffset f out.d out.m :=
  (out.boundedDiscrepancyAlong_iff_boundedDiscOffset (f := f)).1

/-- Negated form (often what we use to drive contradictions): unboundedness also transfers. -/
theorem not_boundedDiscrepancyAlong_iff_not_boundedDiscOffset (out : ReductionOutput f) :
    (¬ BoundedDiscrepancyAlong out.g out.d) ↔ (¬ BoundedDiscOffset f out.d out.m) := by
  exact not_congr (out.boundedDiscrepancyAlong_iff_boundedDiscOffset (f := f))

/-- Unboundedness normal form, transported across the reduction interface.

This is a consumer-friendly lemma: it produces the `∀ B, ∃ n, B < …` shape directly for the
*offset discrepancy* on the original sequence.
-/
theorem not_boundedDiscrepancyAlong_iff_forall_exists_discOffset_gt (out : ReductionOutput f) :
    (¬ BoundedDiscrepancyAlong out.g out.d) ↔ (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) := by
  have h1 : (¬ BoundedDiscrepancyAlong out.g out.d) ↔ (¬ BoundedDiscOffset f out.d out.m) :=
    out.not_boundedDiscrepancyAlong_iff_not_boundedDiscOffset (f := f)
  have h2 : (¬ BoundedDiscOffset f out.d out.m) ↔ (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) :=
    Tao2015.not_boundedDiscOffset_iff_forall_exists_discOffset_gt (f := f) (d := out.d) (m := out.m)
  exact h1.trans h2

/-- The same unboundedness normal form, but phrased using `Int.natAbs (apSumOffset …)`.

This is often the tightest thing you get from a reduction step: it avoids `discOffset` entirely.
-/
theorem not_boundedDiscrepancyAlong_iff_forall_exists_natAbs_apSumOffset_gt (out : ReductionOutput f) :
    (¬ BoundedDiscrepancyAlong out.g out.d) ↔
      (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n)) := by
  have h1 : (¬ BoundedDiscrepancyAlong out.g out.d) ↔ (¬ BoundedDiscOffset f out.d out.m) :=
    out.not_boundedDiscrepancyAlong_iff_not_boundedDiscOffset (f := f)
  have h2 : (¬ BoundedDiscOffset f out.d out.m) ↔
      (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n)) :=
    Tao2015.not_boundedDiscOffset_iff_forall_exists_natAbs_apSumOffset_gt (f := f) (d := out.d) (m := out.m)
  exact h1.trans h2

/-- `discOffset` is literally the absolute value of `apSumOffset`; this lemma rewrites it
using the reduction interface. -/
theorem natAbs_apSum_eq_discOffset (out : ReductionOutput f) (n : ℕ) :
    Int.natAbs (apSum out.g out.d n) = discOffset f out.d out.m n := by
  -- `discOffset` is definitional; `out.apSum_contract` supplies the bridge.
  simp [discOffset, out.apSum_contract]

/-- The absolute value of the offset AP sum can be rewritten to the discrepancy of `out.g`. -/
theorem natAbs_apSumOffset_eq_discrepancy (out : ReductionOutput f) (n : ℕ) :
    Int.natAbs (apSumOffset f out.d out.m n) = discrepancy out.g out.d n := by
  -- Unfold both wrappers and use the bridge rule.
  simp [discrepancy, out.apSum_contract]

/-!
NOTE: The `HasDiscrepancyAtLeastAlong` ↔ `apSumFrom` witness lemmas are already defined earlier in
this file (in the main `ReductionOutput` API section).  A duplicate copy used to live here; it was
removed to avoid duplicate-declaration errors.
-/

/-- `natAbs` bridge rule: absolute AP sums for `out.g` equal absolute offset AP sums for `f`. -/
theorem natAbs_apSum_eq_natAbs_apSumOffset (out : ReductionOutput f) (n : ℕ) :
    Int.natAbs (apSum out.g out.d n) = Int.natAbs (apSumOffset f out.d out.m n) := by
  simp [out.apSum_contract]

/-- Symmetric `natAbs` bridge rule, oriented from offset sums to reduced sums. -/
theorem natAbs_apSumOffset_eq_natAbs_apSum (out : ReductionOutput f) (n : ℕ) :
    Int.natAbs (apSumOffset f out.d out.m n) = Int.natAbs (apSum out.g out.d n) := by
  simpa using (out.natAbs_apSum_eq_natAbs_apSumOffset (f := f) (n := n)).symm

/-- A consumer-friendly “≤” transfer rule for `natAbs` of sums.

This is the `natAbs` analogue of `discrepancy_le_iff_discOffset_le`.
-/
theorem natAbs_apSum_le_iff_natAbs_apSumOffset_le (out : ReductionOutput f) (B : ℕ) (n : ℕ) :
    Int.natAbs (apSum out.g out.d n) ≤ B ↔ Int.natAbs (apSumOffset f out.d out.m n) ≤ B := by
  simpa [out.apSum_contract]

/-- A consumer-friendly “≤” transfer rule for `natAbs` of sums, in the reverse orientation. -/
theorem natAbs_apSumOffset_le_iff_natAbs_apSum_le (out : ReductionOutput f) (B : ℕ) (n : ℕ) :
    Int.natAbs (apSumOffset f out.d out.m n) ≤ B ↔ Int.natAbs (apSum out.g out.d n) ≤ B := by
  simpa using (out.natAbs_apSum_le_iff_natAbs_apSumOffset_le (f := f) (B := B) (n := n)).symm

/-- Transfer pointwise `natAbs` bounds from offset AP sums of `f` to AP sums of `out.g`. -/
theorem natAbs_apSum_le_of_forall_natAbs_apSumOffset_le (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n, Int.natAbs (apSumOffset f out.d out.m n) ≤ B) :
    ∀ n, Int.natAbs (apSum out.g out.d n) ≤ B := by
  intro n
  simpa [out.apSum_contract] using hB n

/-- Transfer pointwise `natAbs` bounds from AP sums of `out.g` to offset AP sums of `f`. -/
theorem natAbs_apSumOffset_le_of_forall_natAbs_apSum_le (out : ReductionOutput f) (B : ℕ)
    (hB : ∀ n, Int.natAbs (apSum out.g out.d n) ≤ B) :
    ∀ n, Int.natAbs (apSumOffset f out.d out.m n) ≤ B := by
  intro n
  -- Orient the bridge in the other direction.
  simpa [out.apSum_contract] using hB n

/-- Uniform `natAbs` boundedness transfers across the reduction interface (as a propositional equivalence). -/
theorem forall_natAbs_apSum_le_iff_forall_natAbs_apSumOffset_le (out : ReductionOutput f) (B : ℕ) :
    (∀ n, Int.natAbs (apSum out.g out.d n) ≤ B) ↔ (∀ n, Int.natAbs (apSumOffset f out.d out.m n) ≤ B) := by
  constructor
  · exact out.natAbs_apSumOffset_le_of_forall_natAbs_apSum_le (f := f) (B := B)
  · exact out.natAbs_apSum_le_of_forall_natAbs_apSumOffset_le (f := f) (B := B)

/-- Existence transfer for `natAbs` bounds: a large AP sum for the reduced sequence is equivalent
to a large offset AP sum for the original sequence. -/
theorem exists_natAbs_apSum_gt_iff_exists_natAbs_apSumOffset_gt (out : ReductionOutput f) (B : ℕ) :
    (∃ n, B < Int.natAbs (apSum out.g out.d n)) ↔
      (∃ n, B < Int.natAbs (apSumOffset f out.d out.m n)) := by
  constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩
  · simpa [out.apSum_contract] using hn
  · simpa [out.apSum_contract] using hn

/-- As a corollary, if the offset sums are unbounded in `natAbs`, then so are the reduced sums. -/
theorem not_forall_natAbs_apSumOffset_le_of_not_forall_natAbs_apSum_le (out : ReductionOutput f) (B : ℕ) :
    (¬ (∀ n, Int.natAbs (apSum out.g out.d n) ≤ B)) →
      (¬ (∀ n, Int.natAbs (apSumOffset f out.d out.m n) ≤ B)) := by
  intro h h'
  -- Transfer the `∀ n` bound back to `apSum`, contradicting `h`.
  exact h ((out.forall_natAbs_apSum_le_iff_forall_natAbs_apSumOffset_le (f := f) (B := B)).2 h')

/-- Any boundedness context for `f` yields bounded offset discrepancy for the parameters in `out`. -/
theorem boundedDiscOffset_of_context (ctx : Context f) (out : ReductionOutput f) :
    BoundedDiscOffset f out.d out.m := by
  refine ⟨ctx.B + ctx.B, ?_⟩
  intro n
  exact out.bound_discOffset (f := f) (ctx := ctx) (out := out) n

/-- Any boundedness context for `f` yields bounded discrepancy along `out.d` for the derived sequence `out.g`. -/
theorem boundedDiscrepancyAlong_of_context (ctx : Context f) (out : ReductionOutput f) :
    BoundedDiscrepancyAlong out.g out.d := by
  refine ⟨ctx.B + ctx.B, ?_⟩
  intro n
  exact out.bound_discrepancy (f := f) (ctx := ctx) (out := out) n

/-- Global bounded discrepancy for `f` implies bounded offset discrepancy for the parameters bundled in `out`. -/
theorem boundedDiscOffset_of_boundedDiscrepancy (out : ReductionOutput f) (hb : BoundedDiscrepancy f) :
    BoundedDiscOffset f out.d out.m := by
  classical
  -- Turn the existential bound into a `Context`, then apply `boundedDiscOffset_of_context`.
  let ctx : Context f := Context.ofBoundedDiscrepancy (f := f) hb
  exact out.boundedDiscOffset_of_context (f := f) (ctx := ctx)

/-- Global bounded discrepancy for `f` implies bounded discrepancy along `out.d` for `out.g`. -/
theorem boundedDiscrepancyAlong_of_boundedDiscrepancy (out : ReductionOutput f) (hb : BoundedDiscrepancy f) :
    BoundedDiscrepancyAlong out.g out.d := by
  classical
  let ctx : Context f := Context.ofBoundedDiscrepancy (f := f) hb
  exact out.boundedDiscrepancyAlong_of_context (f := f) (ctx := ctx)

/-- The offset-boundedness predicate for `f` is equivalent to boundedness along `out.d` for the
reduced sequence `out.g`.

This is a key *interface hop*: reductions often produce boundedness/unboundedness information
for the offset discrepancy `discOffset f out.d out.m`, while contradiction stages prefer to work
with the simpler `BoundedDiscrepancyAlong out.g out.d` form.
-/
theorem boundedDiscOffset_iff_boundedDiscrepancyAlong (out : ReductionOutput f) :
    BoundedDiscOffset f out.d out.m ↔ BoundedDiscrepancyAlong out.g out.d := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- rewrite `discOffset` to `discrepancy` using the reduction interface
    simpa [out.discOffset_eq_discrepancy (f := f) (n := n)] using hB n
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- rewrite `discrepancy` to `discOffset` using the reduction interface
    simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hB n

/-- Contrapositive convenience: if `out.g` is unbounded along `out.d`, then `f` is globally unbounded.

This is a useful end-user lemma: once the Tao pipeline reduces unboundedness to a single fixed
common difference, we can push the contradiction back to the original statement.
-/
theorem not_boundedDiscrepancy_of_not_boundedDiscrepancyAlong (out : ReductionOutput f) :
    (¬ BoundedDiscrepancyAlong out.g out.d) → (¬ BoundedDiscrepancy f) := by
  intro hAlong hb
  exact hAlong (out.boundedDiscrepancyAlong_of_boundedDiscrepancy (f := f) (out := out) hb)

/-- If the offset discrepancies for the parameters in `out` are unbounded, then `f` is globally unbounded.

This is the same idea as `not_boundedDiscrepancy_of_not_boundedDiscrepancyAlong`, but it avoids
mentioning `BoundedDiscrepancyAlong`: it is phrased purely in terms of `BoundedDiscOffset`.
-/
theorem not_boundedDiscrepancy_of_not_boundedDiscOffset (out : ReductionOutput f) :
    (¬ BoundedDiscOffset f out.d out.m) → (¬ BoundedDiscrepancy f) := by
  intro hOff hb
  exact hOff (out.boundedDiscOffset_of_boundedDiscrepancy (f := f) (out := out) hb)

/-- Consumer wrapper: unboundedness normal form for `discOffset` implies global unbounded discrepancy.

This is a common situation after a reduction: the downstream stage produces the explicit shape
`∀ B, ∃ n, B < discOffset …`, and we want to push it back to the original `¬ BoundedDiscrepancy f`.
-/
theorem not_boundedDiscrepancy_of_forall_exists_discOffset_gt (out : ReductionOutput f) :
    (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) → (¬ BoundedDiscrepancy f) := by
  intro h
  -- Convert the normal form into `¬ BoundedDiscOffset …`, then use the previous lemma.
  have hnot : ¬ BoundedDiscOffset f out.d out.m := by
    -- `BoundedDiscOffset` is `∃ B, ∀ n, … ≤ B`, contradicting `h`.
    intro hbd
    rcases hbd with ⟨B, hB⟩
    rcases h B with ⟨n, hn⟩
    exact (not_lt_of_ge (hB n)) hn
  exact out.not_boundedDiscrepancy_of_not_boundedDiscOffset (f := f) hnot

/-- Same as `not_boundedDiscrepancy_of_forall_exists_discOffset_gt`, but phrased using
`Int.natAbs (apSumOffset …)`.

This avoids mentioning `discOffset` entirely, which is often the tightest statement delivered
by a reduction step.
-/
theorem not_boundedDiscrepancy_of_forall_exists_natAbs_apSumOffset_gt (out : ReductionOutput f) :
    (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n)) → (¬ BoundedDiscrepancy f) := by
  intro h
  -- Translate to the `discOffset` normal form and reuse the previous lemma.
  have h' : ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n := by
    intro B
    rcases h B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [discOffset] using hn
  exact out.not_boundedDiscrepancy_of_forall_exists_discOffset_gt (f := f) h'

/-- If the reduced sequence is unbounded along `out.d` (in the explicit witness normal form),
then the original sequence `f` has unbounded discrepancy.

This is a convenience wrapper around `not_boundedDiscrepancy_of_not_boundedDiscrepancyAlong`.
-/
theorem not_boundedDiscrepancy_of_forall_exists_discrepancy_gt (out : ReductionOutput f) :
    (∀ B : ℕ, ∃ n : ℕ, B < discrepancy out.g out.d n) → (¬ BoundedDiscrepancy f) := by
  intro h
  -- Convert the explicit witness form into `¬ BoundedDiscrepancyAlong`.
  have hnotAlong : ¬ BoundedDiscrepancyAlong out.g out.d := by
    -- This equivalence is already proved earlier in the file.
    exact (Tao2015.not_boundedDiscrepancyAlong_iff_forall_exists_discrepancy_gt (g := out.g) (d := out.d)).2 h
  exact out.not_boundedDiscrepancy_of_not_boundedDiscrepancyAlong (f := f) hnotAlong

/-- `natAbs` analogue of `not_boundedDiscrepancy_of_forall_exists_discrepancy_gt`.

Many reduction stages produce witnesses in terms of absolute values of raw AP sums.
-/
theorem not_boundedDiscrepancy_of_forall_exists_natAbs_apSum_gt (out : ReductionOutput f) :
    (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSum out.g out.d n)) → (¬ BoundedDiscrepancy f) := by
  intro h
  -- Convert to discrepancy witnesses and reuse the previous lemma.
  have h' : ∀ B : ℕ, ∃ n : ℕ, B < discrepancy out.g out.d n := by
    intro B
    rcases h B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [discrepancy] using hn
  exact out.not_boundedDiscrepancy_of_forall_exists_discrepancy_gt (f := f) h'

/-- Fixed-step unboundedness for the reduced sequence `out.g` is equivalent to unboundedness of
(the bundled) offset discrepancy of the original sequence `f`.

This is a key “consumer-facing” bridge: downstream reductions often naturally produce an
unboundedness statement in the `HasDiscrepancyAtLeastAlong` normal form.
-/
theorem forall_hasDiscrepancyAtLeastAlong_iff_forall_exists_discOffset_lt (out : ReductionOutput f) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) ↔
      (∀ C : ℕ, ∃ n : ℕ, C < discOffset f out.d out.m n) := by
  constructor
  · intro h C
    -- specialize the `C`-witness and rewrite to a `discOffset` witness
    exact (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_lt (f := f) (C := C)).1 (h C)
  · intro h C
    -- rewrite the `discOffset` witness back to the reduced fixed-step predicate
    exact (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_lt (f := f) (C := C)).2 (h C)

/-- If `out.g` is unbounded along `out.d` (in the `HasDiscrepancyAtLeastAlong` normal form), then
`f` has unbounded discrepancy.

This is a convenience wrapper around
`not_boundedDiscrepancy_of_not_boundedDiscrepancyAlong` plus the standard
`∀ C, HasDiscrepancyAtLeastAlong ↔ ¬BoundedDiscrepancyAlong` equivalence.
-/
theorem not_boundedDiscrepancy_of_forall_hasDiscrepancyAtLeastAlong (out : ReductionOutput f) :
    (∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) → (¬ BoundedDiscrepancy f) := by
  intro h
  have hnotAlong : ¬ BoundedDiscrepancyAlong out.g out.d := by
    -- This equivalence is proved earlier in the file.
    exact
      (HasDiscrepancyAtLeastAlong.forall_hasDiscrepancyAtLeastAlong_iff_not_boundedDiscrepancyAlong
        (g := out.g) (d := out.d)).1 h
  exact out.not_boundedDiscrepancy_of_not_boundedDiscrepancyAlong (f := f) hnotAlong

/-- Produce an `AlongContext` for `out.g` from a global boundedness context on `f`.

This is a small wrapper around `AlongContext.ofContext` that keeps consumers inside the
`ReductionOutput` namespace.
-/
theorem alongContext_of_context (ctx : Context f) (out : ReductionOutput f) : AlongContext out.g out.d :=
  AlongContext.ofContext (f := f) (ctx := ctx) (out := out)

end ReductionOutput

/-- (Stub) Tao 2015 reduction stage.

Given a sign sequence `f` and a boundedness context, produce a structured object.

For now we instantiate the interface with the trivial choice `d = 1`, `m = 0`, `g = f`.
This is enough to let downstream code *use* the interface immediately.
-/
theorem reduction (f : ℕ → ℤ) (hf : IsSignSequence f) (ctx : Context f) :
    ReductionOutput f := by
  -- (Temporary) trivial instantiation of the interface.
  -- Keeping it factored through `mkShiftOfSign` makes later upgrades less invasive.
  classical
  simpa using (ReductionOutput.mkShiftOfSign (f := f) (hf := hf) (d := 1) (m := 0) (hd := by decide))

/-!
### Reduction stage, trivial instantiation lemmas

These are tiny, but they help downstream code avoid repeatedly unfolding the `reduction` stub
just to extract its bundled parameters.

When `reduction` is upgraded from the trivial `d=1,m=0` instantiation to a real Tao reduction,
these lemmas should be the *only* place that needs to change.
-/

/-- `reduction` is currently implemented by the trivial `mkShiftOfSign` constructor. -/
theorem reduction_eq_mkShiftOfSign (f : ℕ → ℤ) (hf : IsSignSequence f) (ctx : Context f) :
    reduction (f := f) (hf := hf) ctx =
      ReductionOutput.mkShiftOfSign (f := f) (hf := hf) (d := 1) (m := 0) (hd := by decide) := by
  classical
  rfl

@[simp] theorem reduction_d (f : ℕ → ℤ) (hf : IsSignSequence f) (ctx : Context f) :
    (reduction (f := f) (hf := hf) ctx).d = 1 := by
  classical
  -- This reduces to the definitional value inside `mkShiftOfSign`.
  simpa [reduction_eq_mkShiftOfSign (f := f) (hf := hf) (ctx := ctx)]

@[simp] theorem reduction_m (f : ℕ → ℤ) (hf : IsSignSequence f) (ctx : Context f) :
    (reduction (f := f) (hf := hf) ctx).m = 0 := by
  classical
  simpa [reduction_eq_mkShiftOfSign (f := f) (hf := hf) (ctx := ctx)]

/-- The bundled positivity proof in the current stub reduction (`1 > 0`). -/
@[simp] theorem reduction_hd (f : ℕ → ℤ) (hf : IsSignSequence f) (ctx : Context f) :
    (reduction (f := f) (hf := hf) ctx).hd := by
  classical
  -- `reduction` is `mkShiftOfSign` with `d=1`.
  simpa [Tao2015.reduction] using (show (1 : ℕ) > 0 by decide)

/-- The bundled shift equation for the current stub reduction (`g = shift f (0*1)`). -/
@[simp] theorem reduction_g_eq (f : ℕ → ℤ) (hf : IsSignSequence f) (ctx : Context f) :
    (reduction (f := f) (hf := hf) ctx).g = fun k => f (k + 0 * 1) := by
  classical
  -- This keeps the shift shape explicit; downstream rewriting can then simplify the arithmetic.
  funext k
  simp [Tao2015.reduction]

@[simp] theorem reduction_g (f : ℕ → ℤ) (hf : IsSignSequence f) (ctx : Context f) :
    (reduction (f := f) (hf := hf) ctx).g = f := by
  classical
  -- `g := fun k => f (k + 0 * 1)`.
  funext k
  simp [reduction_eq_mkShiftOfSign (f := f) (hf := hf) (ctx := ctx)]

@[simp] theorem reduction_discrepancy (f : ℕ → ℤ) (hf : IsSignSequence f) (ctx : Context f) (n : ℕ) :
    discrepancy (reduction (f := f) (hf := hf) ctx).g (reduction (f := f) (hf := hf) ctx).d n =
      discrepancy f 1 n := by
  classical
  -- In the current stub, `g = f` and `d = 1`.
  simp [Tao2015.reduction]

@[simp] theorem reduction_discOffset (f : ℕ → ℤ) (hf : IsSignSequence f) (ctx : Context f) (n : ℕ) :
    discOffset f (reduction (f := f) (hf := hf) ctx).d (reduction (f := f) (hf := hf) ctx).m n =
      discrepancy f 1 n := by
  classical
  -- In the current stub, `d = 1` and `m = 0`.
  simp [Tao2015.reduction, Tao2015.discOffset_zero]

/-!
Small helper lemmas: `reduction` is currently the trivial `(d,m,g)=(1,0,f)` instantiation,
so many expressions simplify completely.

Downstream code should prefer these lemmas to directly unfolding `reduction`.
-/

@[simp] theorem reduction_apSum (f : ℕ → ℤ) (hf : IsSignSequence f) (ctx : Context f) (n : ℕ) :
    apSum (reduction (f := f) (hf := hf) ctx).g (reduction (f := f) (hf := hf) ctx).d n =
      apSum f 1 n := by
  classical
  -- In the current stub, `g = f` and `d = 1`.
  simp [Tao2015.reduction]

@[simp] theorem reduction_apSumOffset (f : ℕ → ℤ) (hf : IsSignSequence f) (ctx : Context f) (n : ℕ) :
    apSumOffset f (reduction (f := f) (hf := hf) ctx).d (reduction (f := f) (hf := hf) ctx).m n =
      apSum f 1 n := by
  classical
  -- In the current stub, `d = 1` and `m = 0`.
  simp [Tao2015.reduction, Tao2015.apSumOffset_zero]

@[simp] theorem reduction_natAbs_apSumOffset (f : ℕ → ℤ) (hf : IsSignSequence f) (ctx : Context f) (n : ℕ) :
    Int.natAbs (apSumOffset f (reduction (f := f) (hf := hf) ctx).d (reduction (f := f) (hf := hf) ctx).m n) =
      Int.natAbs (apSum f 1 n) := by
  classical
  simp [Tao2015.reduction, Tao2015.apSumOffset_zero]

@[simp] theorem reduction_discOffset' (f : ℕ → ℤ) (hf : IsSignSequence f) (ctx : Context f) (n : ℕ) :
    discOffset f (reduction (f := f) (hf := hf) ctx).d (reduction (f := f) (hf := hf) ctx).m n =
      discOffset f 1 0 n := by
  classical
  -- Sometimes it is convenient to keep `discOffset` rather than rewriting to `discrepancy`.
  simp [Tao2015.reduction]

/-!
### Downstream contradiction stage (still a stub)

The point of the “plane” architecture is that once we have *any* downstream stage that produces
an explicit unboundedness witness for the offset discrepancy bundled in `out`, the rest of the
argument is pure interface plumbing.

So we isolate that future deliverable as a named lemma:
- `stage2_unbounded_discOffset` (currently a stub theorem with one `sorry`)

and make the top-level `contradiction` proof *structural* and `sorry`-free.
-/

/-!
### Small helpers for the stage-2 deliverable

The eventual stage-2 proof will almost certainly proceed by first showing a *negated boundedness*
statement, and only then extracting the explicit `∀ B, ∃ n, B < …` normal form.

We keep these helpers adjacent to the stage-2 stub so the intended proof shape is obvious.
-/

/-- For the parameters bundled in `out`, unpack `¬ BoundedDiscOffset` into the explicit
unboundedness normal form `∀ B, ∃ n, B < discOffset …`.

This is a specialization of `not_boundedDiscOffset_iff_forall_exists_discOffset_gt`.
-/
theorem not_boundedDiscOffset_iff_forall_exists_discOffset_gt' (out : ReductionOutput f) :
    (¬ BoundedDiscOffset f out.d out.m) ↔ (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) := by
  simpa using (Tao2015.not_boundedDiscOffset_iff_forall_exists_discOffset_gt (f := f) (d := out.d) (m := out.m))

/-- Same as `not_boundedDiscOffset_iff_forall_exists_discOffset_gt'`, but phrased using
`Int.natAbs (apSumOffset …)`.

This is often the natural output of a reduction step, before introducing `discOffset`.
-/
theorem not_boundedDiscOffset_iff_forall_exists_natAbs_apSumOffset_gt' (out : ReductionOutput f) :
    (¬ BoundedDiscOffset f out.d out.m) ↔
      (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n)) := by
  simpa using
    (Tao2015.not_boundedDiscOffset_iff_forall_exists_natAbs_apSumOffset_gt (f := f) (d := out.d) (m := out.m))

/-- For the parameters bundled in `out`, the explicit unboundedness normal form implies
`¬ BoundedDiscOffset …`.

This is the direction most downstream contradiction stages want: they produce
`∀ B, ∃ n, B < discOffset …` and immediately need to negate boundedness.
-/
theorem not_boundedDiscOffset_of_forall_exists_discOffset_gt (out : ReductionOutput f)
    (h : ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) :
    ¬ BoundedDiscOffset f out.d out.m := by
  -- Contrapose the `BoundedDiscOffset` witness.
  intro hbd
  rcases hbd with ⟨B, hB⟩
  rcases h B with ⟨n, hn⟩
  exact (not_lt_of_ge (hB n)) hn

/-- `natAbs` variant of `not_boundedDiscOffset_of_forall_exists_discOffset_gt`. -/
theorem not_boundedDiscOffset_of_forall_exists_natAbs_apSumOffset_gt (out : ReductionOutput f)
    (h : ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n)) :
    ¬ BoundedDiscOffset f out.d out.m := by
  -- Convert to the `discOffset` version and reuse the previous lemma.
  apply not_boundedDiscOffset_of_forall_exists_discOffset_gt (f := f) (out := out)
  intro B
  rcases h B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [discOffset] using hn

/-- For the parameters bundled in `out`, the explicit unboundedness normal form is equivalent to
`¬ BoundedDiscOffset …`.

This is just `not_boundedDiscOffset_iff_forall_exists_discOffset_gt'` in the reverse direction,
but it matches the way stage-2 reductions tend to be stated.
-/
theorem forall_exists_discOffset_gt_iff_not_boundedDiscOffset (out : ReductionOutput f) :
    (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) ↔ (¬ BoundedDiscOffset f out.d out.m) := by
  simpa [out.not_boundedDiscOffset_iff_forall_exists_discOffset_gt' (f := f)]

/-- `natAbs` analogue of `forall_exists_discOffset_gt_iff_not_boundedDiscOffset`. -/
theorem forall_exists_natAbs_apSumOffset_gt_iff_not_boundedDiscOffset (out : ReductionOutput f) :
    (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n)) ↔
      (¬ BoundedDiscOffset f out.d out.m) := by
  simpa [out.not_boundedDiscOffset_iff_forall_exists_natAbs_apSumOffset_gt' (f := f)]

/-- For the parameters in `out`, unbounded offset discrepancy implies the reduced sequence
is unbounded along `out.d`.

This is a tiny “interface hop” lemma: it lets a downstream stage stay in the `discOffset` world
(because that is what the reduction naturally produces) but hand a contradiction stage a statement
about `BoundedDiscrepancyAlong out.g out.d`.
-/
theorem not_boundedDiscrepancyAlong_of_forall_exists_discOffset_gt (out : ReductionOutput f)
    (h : ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) :
    ¬ BoundedDiscrepancyAlong out.g out.d := by
  intro hbd
  -- Transfer boundedness along `out.d` to bounded offset discrepancy, contradicting `h`.
  have hOff : BoundedDiscOffset f out.d out.m :=
    out.boundedDiscOffset_of_boundedDiscrepancyAlong (f := f) (out := out) hbd
  exact not_boundedDiscOffset_of_forall_exists_discOffset_gt (f := f) (out := out) h hOff

/-- `natAbs` variant of `not_boundedDiscrepancyAlong_of_forall_exists_discOffset_gt`.

This lets a downstream stage stay at the AP-sum level (often the most natural output), while the
contradiction stage works with the standard boundedness predicate.
-/
theorem not_boundedDiscrepancyAlong_of_forall_exists_natAbs_apSumOffset_gt (out : ReductionOutput f)
    (h : ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n)) :
    ¬ BoundedDiscrepancyAlong out.g out.d := by
  apply not_boundedDiscrepancyAlong_of_forall_exists_discOffset_gt (f := f) (out := out)
  intro B
  rcases h B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [discOffset] using hn

/-- For the parameters in `out`, the explicit unboundedness normal form implies
`¬ BoundedDiscrepancyAlong out.g out.d`.

This is just `not_boundedDiscrepancyAlong_iff_forall_exists_discOffset_gt`, oriented the way
stage-2 reductions naturally output witnesses.
-/
theorem forall_exists_discOffset_gt_iff_not_boundedDiscrepancyAlong (out : ReductionOutput f) :
    (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) ↔ (¬ BoundedDiscrepancyAlong out.g out.d) := by
  simpa using (out.not_boundedDiscrepancyAlong_iff_forall_exists_discOffset_gt (f := f)).symm

/-- `natAbs` analogue of `forall_exists_discOffset_gt_iff_not_boundedDiscrepancyAlong`. -/
theorem forall_exists_natAbs_apSumOffset_gt_iff_not_boundedDiscrepancyAlong (out : ReductionOutput f) :
    (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n)) ↔
      (¬ BoundedDiscrepancyAlong out.g out.d) := by
  -- Convert the `natAbs` normal form to `discOffset`, then use the previous lemma.
  constructor
  · intro h
    -- First convert the witness normal form into `¬ BoundedDiscOffset …`.
    have hnotOff : ¬ BoundedDiscOffset f out.d out.m :=
      (out.forall_exists_natAbs_apSumOffset_gt_iff_not_boundedDiscOffset (f := f)).1 h
    -- Then transfer to `¬ BoundedDiscrepancyAlong …`.
    exact (out.not_boundedDiscrepancyAlong_iff_not_boundedDiscOffset (f := f)).2 hnotOff
  · intro h
    -- Transfer back to `¬ BoundedDiscOffset …`, then unpack to the `natAbs` witness form.
    have hnotOff : ¬ BoundedDiscOffset f out.d out.m :=
      (out.not_boundedDiscrepancyAlong_iff_not_boundedDiscOffset (f := f)).1 h
    exact (out.not_boundedDiscOffset_iff_forall_exists_natAbs_apSumOffset_gt' (f := f)).1 hnotOff

/-!
### Stage-2 statement normal forms

Downstream reduction stages often come in one of two equivalent shapes:

1. an explicit unboundedness witness normal form `∀ B, ∃ n, B < …`
2. a negated boundedness statement `¬ Bounded…`

The helpers below let later files pick the more convenient form without rewriting proofs.
-/

/-- For the parameters bundled in `out`, the stage-2 witness normal form is equivalent to
`¬ BoundedDiscOffset …`.

This is just `forall_exists_discOffset_gt_iff_not_boundedDiscOffset`, but the name makes it
discoverable when searching for “stage2” glue.
-/
theorem stage2_witness_discOffset_iff_not_boundedDiscOffset (out : ReductionOutput f) :
    (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) ↔ (¬ BoundedDiscOffset f out.d out.m) := by
  simpa using (out.forall_exists_discOffset_gt_iff_not_boundedDiscOffset (f := f))

/-- `natAbs` analogue of `stage2_witness_discOffset_iff_not_boundedDiscOffset`. -/
theorem stage2_witness_natAbs_apSumOffset_iff_not_boundedDiscOffset (out : ReductionOutput f) :
    (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n)) ↔ (¬ BoundedDiscOffset f out.d out.m) := by
  simpa using (out.forall_exists_natAbs_apSumOffset_gt_iff_not_boundedDiscOffset (f := f))

/-- For the parameters bundled in `out`, the stage-2 witness normal form is equivalent to
`¬ BoundedDiscrepancyAlong out.g out.d`.

This is the “interface hop” most contradiction stages want: once we have the explicit offset
witnesses, we can view them as unboundedness of the reduced sequence along the fixed `d`.
-/
theorem stage2_witness_discOffset_iff_not_boundedDiscrepancyAlong (out : ReductionOutput f) :
    (∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) ↔ (¬ BoundedDiscrepancyAlong out.g out.d) := by
  simpa using (out.forall_exists_discOffset_gt_iff_not_boundedDiscrepancyAlong (f := f))

/-!
### Stage-2 witness ⇄ fixed-step discrepancy (our local predicate)

A stage-2 reduction naturally produces witnesses about the bundled offset discrepancy
`discOffset f out.d out.m`.  For some downstream steps, it is more convenient to work with the
fixed-step predicate `HasDiscrepancyAtLeastAlong out.g out.d`.

The next lemmas let us move between these views without any extra rewriting.
-/

/-- Convert stage-2 witnesses into the fixed-step predicate `HasDiscrepancyAtLeastAlong`. -/
theorem forall_hasDiscrepancyAtLeastAlong_of_forall_exists_discOffset_gt (out : ReductionOutput f)
    (h : ∀ C : ℕ, ∃ n : ℕ, C < discOffset f out.d out.m n) :
    ∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C := by
  intro C
  -- Use the `HasDiscrepancyAtLeastAlong` ↔ `discOffset` bridge already provided by `ReductionOutput`.
  exact (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_lt (f := f) (C := C)).2 (h C)

/-- Convert fixed-step discrepancy statements into stage-2 witnesses (discOffset form). -/
theorem forall_exists_discOffset_gt_of_forall_hasDiscrepancyAtLeastAlong (out : ReductionOutput f)
    (h : ∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C) :
    ∀ C : ℕ, ∃ n : ℕ, C < discOffset f out.d out.m n := by
  intro C
  exact (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_lt (f := f) (C := C)).1 (h C)

/-!
### Stage-2 interface packaging

Once we start actually implementing Tao’s stage-2 argument, we’ll likely want to *package* its
output (the witness normal form) as a structure so later files can carry it around without
re-quantifying over `B` each time.

This stays in `Conjectures/` since it is proof-pipeline glue.
-/

/-- Stage-2 output: explicit unboundedness witnesses for the bundled offset discrepancies. -/
structure Stage2Output (f : ℕ → ℤ) (out : ReductionOutput f) : Type where
  unbounded_discOffset : ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n

namespace Stage2Output

/-- Constructor helper: package a witness-normal-form function as a `Stage2Output`. -/
def ofUnboundedDiscOffset (h : ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) :
    Stage2Output f out :=
  ⟨h⟩

@[simp] theorem ofUnboundedDiscOffset_unbounded (h : ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n) :
    (ofUnboundedDiscOffset (f := f) (out := out) h).unbounded_discOffset = h := by
  rfl

/-- Constructor helper: package an unboundedness normal form stated using raw offset AP sums.

This is often the natural output of a reduction step that works at the `apSum` level first.
-/
def ofUnboundedNatAbsApSumOffset
    (h : ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n)) :
    Stage2Output f out := by
  refine ofUnboundedDiscOffset (f := f) (out := out) ?_
  intro B
  rcases h B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [discOffset] using hn

theorem ofUnboundedNatAbsApSumOffset_unbounded
    (h : ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n)) :
    (ofUnboundedNatAbsApSumOffset (f := f) (out := out) h).unbounded_discOffset =
      (fun B => by
        rcases h B with ⟨n, hn⟩
        refine ⟨n, ?_⟩
        simpa [discOffset] using hn) := by
  rfl

/-- Build a `Stage2Output` from the negated boundedness form `¬ BoundedDiscOffset …`.

This is the classical “witness extraction” direction of
`not_boundedDiscOffset_iff_forall_exists_discOffset_gt`, packaged as a structure.
-/
noncomputable def ofNotBoundedDiscOffset (h : ¬ BoundedDiscOffset f out.d out.m) :
    Stage2Output f out := by
  classical
  refine ofUnboundedDiscOffset (f := f) (out := out) ?_
  -- Flip `¬ bounded` to the witness normal form.
  exact (not_boundedDiscOffset_iff_forall_exists_discOffset_gt (f := f) (d := out.d) (m := out.m)).1 h

@[simp] theorem ofNotBoundedDiscOffset_unbounded (h : ¬ BoundedDiscOffset f out.d out.m) :
    (ofNotBoundedDiscOffset (f := f) (out := out) h).unbounded_discOffset =
      (not_boundedDiscOffset_iff_forall_exists_discOffset_gt (f := f) (d := out.d) (m := out.m)).1 h := by
  rfl

/-- Extract a single `discOffset` witness from `Stage2Output` (greater-than orientation). -/
theorem exists_discOffset_gt (s2 : Stage2Output f out) (C : ℕ) :
    ∃ n : ℕ, discOffset f out.d out.m n > C := by
  rcases s2.unbounded_discOffset C with ⟨n, hn⟩
  exact ⟨n, by simpa [gt_iff_lt] using hn⟩

/-- Extract a single `discOffset` witness from `Stage2Output` (less-than orientation). -/
theorem exists_discOffset_lt (s2 : Stage2Output f out) (C : ℕ) :
    ∃ n : ℕ, C < discOffset f out.d out.m n := by
  rcases s2.unbounded_discOffset C with ⟨n, hn⟩
  exact ⟨n, hn⟩

/-- Extract a single `natAbs(apSumOffset ...)` witness from `Stage2Output` (less-than orientation). -/
theorem exists_natAbs_apSumOffset_lt (s2 : Stage2Output f out) (C : ℕ) :
    ∃ n : ℕ, C < Int.natAbs (apSumOffset f out.d out.m n) := by
  rcases s2.exists_discOffset_lt (f := f) (out := out) C with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [discOffset] using hn

/-- Extract a single discrepancy witness for the reduced sequence `out.g` (greater-than orientation). -/
theorem exists_discrepancy_gt (s2 : Stage2Output f out) (C : ℕ) :
    ∃ n : ℕ, discrepancy out.g out.d n > C := by
  rcases s2.exists_discOffset_gt (f := f) (out := out) C with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  -- Rewrite the offset discrepancy into the reduced discrepancy.
  simpa [out.discOffset_eq_discrepancy (f := f) (n := n)] using hn

/-!
### Stage-2 regression examples

These compile-time `example` blocks pin down the intended consumer workflow:
- build `Stage2Output` from a negated boundedness statement, and
- extract a fixed-step discrepancy witness for the reduced sequence.

They are deliberately tiny and should remain stable even as we refactor the internal API.
-/

section Stage2RegressionExamples

variable (f : ℕ → ℤ) (out : ReductionOutput f)

/-- From `¬ BoundedDiscOffset`, we can extract the witness-normal-form function. -/
example (h : ¬ BoundedDiscOffset f out.d out.m) :
    ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n := by
  -- `ofNotBoundedDiscOffset` is a packaging constructor; the witnesses are its only payload.
  simpa using (Stage2Output.ofNotBoundedDiscOffset (f := f) (out := out) h).unbounded_discOffset

/-- `Stage2Output` witnesses immediately yield a large-discrepancy witness for the reduced sequence. -/
example (s2 : Stage2Output f out) (C : ℕ) :
    ∃ n : ℕ, discrepancy out.g out.d n > C := by
  simpa using s2.exists_discrepancy_gt (f := f) (out := out) C

end Stage2RegressionExamples

/-- Extract a single discrepancy witness for the reduced sequence `out.g` (less-than orientation). -/
theorem exists_discrepancy_lt (s2 : Stage2Output f out) (C : ℕ) :
    ∃ n : ℕ, C < discrepancy out.g out.d n := by
  rcases s2.exists_discOffset_lt (f := f) (out := out) C with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [out.discOffset_eq_discrepancy (f := f) (n := n)] using hn

/-- Extract a single `natAbs(apSumFrom ...)` witness from `Stage2Output`.

This is the “affine nucleus” normal form: it rewrites the stage-2 witness about `discOffset`
into a witness about the tail-sum nucleus `apSumFrom f (out.m*out.d) out.d`.
-/
theorem exists_natAbs_apSumFrom_mul_lt (s2 : Stage2Output f out) (C : ℕ) :
    ∃ n : ℕ, C < Int.natAbs (apSumFrom f (out.m * out.d) out.d n) := by
  rcases s2.exists_discOffset_lt (f := f) (out := out) C with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  -- Convert `discOffset` to `natAbs (apSumFrom ...)` using the bridge lemma.
  simpa [Tao2015.discOffset_eq_natAbs_apSumFrom_mul] using hn

/-- Extract a single `natAbs(apSumOffset ...)` witness from `Stage2Output` (greater-than orientation). -/
theorem exists_natAbs_apSumOffset_gt (s2 : Stage2Output f out) (C : ℕ) :
    ∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > C := by
  rcases s2.exists_natAbs_apSumOffset_lt (f := f) (out := out) C with ⟨n, hn⟩
  exact ⟨n, by simpa [gt_iff_lt] using hn⟩

/-- (Deprecated) This lemma was a duplicate of `exists_natAbs_apSumFrom_mul_lt`.

Use `exists_natAbs_apSumFrom_mul_lt` instead.
-/
@[deprecated (since := "2026-03-08")]
theorem exists_natAbs_apSumFrom_mul_lt' (s2 : Stage2Output f out) (C : ℕ) :
    ∃ n : ℕ, C < Int.natAbs (apSumFrom f (out.m * out.d) out.d n) :=
  exists_natAbs_apSumFrom_mul_lt (f := f) (out := out) s2 C

/-- Greater-than oriented version of `exists_natAbs_apSumFrom_mul_lt`. -/
theorem exists_natAbs_apSumFrom_mul_gt (s2 : Stage2Output f out) (C : ℕ) :
    ∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C := by
  rcases s2.exists_natAbs_apSumFrom_mul_lt (f := f) (out := out) C with ⟨n, hn⟩
  exact ⟨n, by simpa [gt_iff_lt] using hn⟩

/-- Convert a `Stage2Output` to a fixed-threshold `HasDiscrepancyAtLeastAlong` witness.

This lemma is redundant with the later convenience lemma
`Stage2Output.hasDiscrepancyAtLeastAlong`; we keep it under a more explicit name to avoid
accidental rewriting loops and to document the `discOffset`→`HasDiscrepancyAtLeastAlong` bridge.
-/
theorem hasDiscrepancyAtLeastAlong_of_exists_discOffset_lt (s2 : Stage2Output f out) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C := by
  rcases s2.exists_discOffset_lt (f := f) (out := out) C with ⟨n, hn⟩
  exact (out.hasDiscrepancyAtLeastAlong_iff_exists_discOffset_lt (f := f) (C := C)).2 ⟨n, hn⟩

/-- Build a `Stage2Output` from the negated boundedness form `¬ BoundedDiscrepancyAlong out.g out.d`.

This is a useful alternative entry point for stage 2: some reductions naturally produce
unboundedness of the *reduced* sequence at a fixed step size, and only later want to translate
that back into explicit offset-discrepancy witnesses for the original sequence `f`.
-/
noncomputable def ofNotBoundedDiscrepancyAlong (h : ¬ BoundedDiscrepancyAlong out.g out.d) :
    Stage2Output f out := by
  classical
  refine ofUnboundedDiscOffset (f := f) (out := out) ?_
  intro B
  -- Extract the explicit witness normal form for discrepancies of `out.g`.
  have hdisc : ∃ n : ℕ, B < discrepancy out.g out.d n := by
    exact (Tao2015.not_boundedDiscrepancyAlong_iff_forall_exists_discrepancy_gt (g := out.g) (d := out.d)).1 h B
  rcases hdisc with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  -- Rewrite `discrepancy out.g out.d n` to the bundled offset discrepancy of `f`.
  simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hn

/-- `rfl` expansion for the `unbounded_discOffset` field of `ofNotBoundedDiscrepancyAlong`.

Not marked `[simp]` because it expands to a large witness-producing lambda that tends to make
simp goals noisier rather than shorter.
-/
theorem ofNotBoundedDiscrepancyAlong_unbounded (h : ¬ BoundedDiscrepancyAlong out.g out.d) :
    (ofNotBoundedDiscrepancyAlong (f := f) (out := out) h).unbounded_discOffset =
      (fun B => by
        have hdisc : ∃ n : ℕ, B < discrepancy out.g out.d n :=
          (Tao2015.not_boundedDiscrepancyAlong_iff_forall_exists_discrepancy_gt (g := out.g) (d := out.d)).1 h B
        rcases hdisc with ⟨n, hn⟩
        refine ⟨n, ?_⟩
        simpa [out.discrepancy_eq_discOffset (f := f) (n := n)] using hn) := by
  rfl

/-- Stage-2 output transported to the reduced sequence `out.g` (discrepancy witness form). -/
theorem unbounded_discrepancy (s2 : Stage2Output f out) :
    ∀ B : ℕ, ∃ n : ℕ, B < discrepancy out.g out.d n := by
  intro B
  rcases s2.unbounded_discOffset B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [out.discOffset_eq_discrepancy (f := f) (n := n)] using hn

/-- Greater-than oriented version of `Stage2Output.unbounded_discOffset`. -/
theorem unbounded_discOffset_gt (s2 : Stage2Output f out) :
    ∀ B : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > B := by
  intro B
  rcases s2.unbounded_discOffset B with ⟨n, hn⟩
  exact ⟨n, by simpa [gt_iff_lt] using hn⟩

/-- Greater-than oriented version of `Stage2Output.unbounded_discrepancy`. -/
theorem unbounded_discrepancy_gt (s2 : Stage2Output f out) :
    ∀ B : ℕ, ∃ n : ℕ, discrepancy out.g out.d n > B := by
  intro B
  rcases s2.unbounded_discrepancy (f := f) (out := out) B with ⟨n, hn⟩
  exact ⟨n, by simpa [gt_iff_lt] using hn⟩

/-- `natAbs` witness form for the bundled *offset sums*.

This is just `Stage2Output.unbounded_discOffset` with `discOffset` unfolded.
-/
theorem unbounded_natAbs_apSumOffset (s2 : Stage2Output f out) :
    ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n) := by
  intro B
  rcases s2.unbounded_discOffset B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [discOffset] using hn

/-- Greater-than oriented version of `Stage2Output.unbounded_natAbs_apSumOffset`. -/
theorem unbounded_natAbs_apSumOffset_gt (s2 : Stage2Output f out) :
    ∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > B := by
  intro B
  rcases s2.unbounded_natAbs_apSumOffset (f := f) (out := out) B with ⟨n, hn⟩
  exact ⟨n, by simpa [gt_iff_lt] using hn⟩

/-- `natAbs` witness form for the reduced *AP sums* `apSum out.g out.d`.

This is the most “sum-level” consumer statement: it avoids both `discOffset` and `discrepancy`.
-/
theorem unbounded_natAbs_apSum (s2 : Stage2Output f out) :
    ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSum out.g out.d n) := by
  intro B
  rcases s2.unbounded_discrepancy (f := f) (out := out) B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [discrepancy] using hn

/-- A `Stage2Output` certifies that the bundled offset discrepancy is not bounded. -/
theorem not_boundedDiscOffset (s2 : Stage2Output f out) :
    ¬ BoundedDiscOffset f out.d out.m := by
  intro hbd
  rcases hbd with ⟨B, hB⟩
  rcases s2.unbounded_discOffset B with ⟨n, hn⟩
  exact (Nat.not_lt_of_ge (hB n)) hn

/-- A `Stage2Output` certifies that the reduced sequence has unbounded discrepancy along `out.d`. -/
theorem not_boundedDiscrepancyAlong (s2 : Stage2Output f out) :
    ¬ BoundedDiscrepancyAlong out.g out.d := by
  intro hbd
  rcases hbd with ⟨B, hB⟩
  rcases s2.unbounded_discrepancy (f := f) (out := out) B with ⟨n, hn⟩
  -- `hB` gives `discrepancy ≤ B`, contradicting `B < discrepancy`.
  exact (Nat.not_lt_of_ge (hB n)) hn

/-!
### Convenience consequences: “for every threshold C, there is a large discrepancy”

The stage-2 output is an unboundedness normal form (`∀ B, ∃ n, B < …`).
Downstream stages often want the *existence* form at a particular threshold.
-/

/-- For any threshold `C`, the reduced sequence `out.g` has discrepancy `> C` along `out.d`.

This is a direct consumer lemma for `HasDiscrepancyAtLeastAlong`.
-/
theorem hasDiscrepancyAtLeastAlong (s2 : Stage2Output f out) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C := by
  -- Use the unboundedness normal form at `B = C`.
  rcases s2.unbounded_discrepancy (f := f) (out := out) C with ⟨n, hn⟩
  -- Unfold the predicate (it is stated in terms of `Int.natAbs (apSum …)`).
  refine ⟨n, ?_⟩
  simpa [HasDiscrepancyAtLeastAlong, discrepancy] using hn

/-- Uniform version of `hasDiscrepancyAtLeastAlong`. -/
theorem forall_hasDiscrepancyAtLeastAlong (s2 : Stage2Output f out) :
    ∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C := by
  intro C
  exact s2.hasDiscrepancyAtLeastAlong (f := f) (out := out) C

/-- A `Stage2Output` gives the ambient `HasDiscrepancyAtLeast` predicate for every threshold.

This is just `hasDiscrepancyAtLeastAlong` promoted via the `d`-quantifier.
-/
theorem hasDiscrepancyAtLeast (s2 : Stage2Output f out) (C : ℕ) :
    HasDiscrepancyAtLeast out.g C := by
  -- Promote fixed-step discrepancy witness to the existential-over-`d` form.
  exact HasDiscrepancyAtLeastAlong.toHasDiscrepancyAtLeast (f := out.g) (d := out.d) (C := C)
    out.hd (s2.hasDiscrepancyAtLeastAlong (f := f) (out := out) C)

/-- Uniform version of `hasDiscrepancyAtLeast`. -/
theorem forall_hasDiscrepancyAtLeast (s2 : Stage2Output f out) :
    ∀ C : ℕ, HasDiscrepancyAtLeast out.g C := by
  intro C
  exact s2.hasDiscrepancyAtLeast (f := f) (out := out) C

/-- A `Stage2Output` yields a `discOffset` witness `> C` for the bundled parameters.

This is the “original-sequence” form of `Stage2Output.hasDiscrepancyAtLeastAlong`.
-/
theorem exists_discOffset_gt (s2 : Stage2Output f out) (C : ℕ) :
    ∃ n : ℕ, discOffset f out.d out.m n > C := by
  rcases s2.unbounded_discOffset C with ⟨n, hn⟩
  exact ⟨n, hn⟩

/-- Same as `exists_discOffset_gt`, but with the inequality oriented as `C < ...`.

This avoids frequent `gt_iff_lt` rewriting in downstream stages.
-/
theorem exists_discOffset_lt (s2 : Stage2Output f out) (C : ℕ) :
    ∃ n : ℕ, C < discOffset f out.d out.m n := by
  simpa [gt_iff_lt] using s2.exists_discOffset_gt (f := f) (out := out) C

/-- Uniform version of `exists_discOffset_lt`. -/
theorem forall_exists_discOffset_lt (s2 : Stage2Output f out) :
    ∀ C : ℕ, ∃ n : ℕ, C < discOffset f out.d out.m n := by
  intro C
  exact s2.exists_discOffset_lt (f := f) (out := out) C

/-- A `Stage2Output` yields an `apSumOffset` witness in raw `natAbs` form.

This is sometimes the easiest form to consume when staying at the “sum level”.
-/
theorem exists_natAbs_apSumOffset_gt (s2 : Stage2Output f out) (C : ℕ) :
    ∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > C := by
  rcases s2.exists_discOffset_gt (f := f) (out := out) C with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [discOffset] using hn

/-- A `Stage2Output` yields a discrepancy witness `> C` for the reduced sequence `out.g`. -/
theorem exists_discrepancy_gt (s2 : Stage2Output f out) (C : ℕ) :
    ∃ n : ℕ, discrepancy out.g out.d n > C := by
  rcases s2.unbounded_discrepancy (f := f) (out := out) C with ⟨n, hn⟩
  exact ⟨n, hn⟩

/-- Same as `exists_discrepancy_gt`, but with the inequality oriented as `C < ...`. -/
theorem exists_discrepancy_lt (s2 : Stage2Output f out) (C : ℕ) :
    ∃ n : ℕ, C < discrepancy out.g out.d n := by
  simpa [gt_iff_lt] using s2.exists_discrepancy_gt (f := f) (out := out) C

/-- A `Stage2Output` yields an AP-sum witness `> C` in raw `natAbs` form for the reduced sequence.

This is the `apSum` analogue of `exists_discrepancy_gt`.
-/
theorem exists_natAbs_apSum_gt (s2 : Stage2Output f out) (C : ℕ) :
    ∃ n : ℕ, Int.natAbs (apSum out.g out.d n) > C := by
  rcases s2.exists_discrepancy_gt (f := f) (out := out) C with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [discrepancy] using hn

/-- A `Stage2Output` yields explicit unboundedness of the **offset AP sums** packaged by `out`.

This is the `natAbs(apSumOffset ...)` form of the `discOffset` witnesses.
-/
theorem forall_exists_natAbs_apSumOffset_gt (s2 : Stage2Output f out) :
    ∀ C : ℕ, ∃ n : ℕ, C < Int.natAbs (apSumOffset f out.d out.m n) := by
  intro C
  rcases s2.unbounded_discOffset (f := f) (out := out) C with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [discOffset] using hn

/-- A `Stage2Output` yields the pipeline-friendly `HasDiscrepancyAtLeastAlong` predicate for `out.g`.

This is often the easiest form to feed into later reductions that keep `d` fixed.
-/
theorem forall_hasDiscrepancyAtLeastAlong (s2 : Stage2Output f out) :
    ∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C := by
  intro C
  rcases s2.exists_natAbs_apSum_gt (f := f) (out := out) C with ⟨n, hn⟩
  exact ⟨n, hn⟩

/-- A `Stage2Output` yields unbounded discrepancy along the reduced fixed step `out.d`.

This is the witness predicate `UnboundedDiscrepancyAlong out.g out.d` packaged as a one-liner.
It is frequently the most convenient form for later “contradiction” stages.
-/
theorem unboundedDiscrepancyAlong (s2 : Stage2Output f out) :
    UnboundedDiscrepancyAlong out.g out.d := by
  intro B
  rcases s2.unbounded_discOffset (f := f) (out := out) B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  -- Rewrite the offset discrepancy back to the reduced discrepancy via the stage-1 contract.
  simpa [out.discOffset_eq_discrepancy (f := f) (n := n)] using hn

/-- A `Stage2Output` yields the ambient `HasDiscrepancyAtLeast` predicate for the reduced sequence.

This is a convenient bridge when a later stage expects the standard discrepancy notion.
-/
theorem forall_hasDiscrepancyAtLeast (s2 : Stage2Output f out) :
    ∀ C : ℕ, HasDiscrepancyAtLeast out.g C := by
  intro C
  exact
    HasDiscrepancyAtLeastAlong.toHasDiscrepancyAtLeast (f := out.g) (d := out.d) (C := C) out.hd
      (s2.forall_hasDiscrepancyAtLeastAlong (f := f) (out := out) C)

/-- Convert packaged stage-2 output to the propositional negated boundedness form. -/
theorem not_boundedDiscOffset (s2 : Stage2Output f out) : ¬ BoundedDiscOffset f out.d out.m := by
  exact (stage2_witness_discOffset_iff_not_boundedDiscOffset (f := f) (out := out)).1 s2.unbounded_discOffset

/-- Convert packaged stage-2 output to `¬ BoundedDiscrepancyAlong out.g out.d`. -/
theorem not_boundedDiscrepancyAlong (s2 : Stage2Output f out) : ¬ BoundedDiscrepancyAlong out.g out.d := by
  exact (stage2_witness_discOffset_iff_not_boundedDiscrepancyAlong (f := f) (out := out)).1 s2.unbounded_discOffset

/-- Convert packaged stage-2 output to the witness-style predicate
`Tao2015.UnboundedDiscrepancyAlong out.g out.d`.

This is a one-line interface hop: `Stage2Output` stores witnesses about `discOffset f out.d out.m`,
while `UnboundedDiscrepancyAlong` talks about the discrepancy of the reduced sequence `out.g`.
-/
theorem unboundedDiscrepancyAlong (s2 : Stage2Output f out) : Tao2015.UnboundedDiscrepancyAlong out.g out.d := by
  -- `out` already provides `UnboundedDiscrepancyAlong out.g out.d ↔ ∀ B, ∃ n, B < discOffset ...`.
  exact (out.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (f := f)).2 s2.unbounded_discOffset

/-!
### Stage-2 regression examples

These are compile-time “shape checks”: they assert that the packaged stage-2 interface can be
consumed using the intended one-liner lemmas, without unfolding definitions.

They are intentionally tiny and should remain stable even as we refactor the surrounding code.
-/
section Stage2RegressionExamples

variable (s2 : Stage2Output f out)

/-- Stage-2 output immediately provides the unboundedness predicate along the reduced step. -/
example : Tao2015.UnboundedDiscrepancyAlong out.g out.d := by
  simpa using (Stage2Output.unboundedDiscrepancyAlong (f := f) (out := out) s2)

/-- Stage-2 output gives `∀ C, HasDiscrepancyAtLeastAlong out.g out.d C` in one hop. -/
example : ∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C := by
  simpa using (Stage2Output.forall_hasDiscrepancyAtLeastAlong (f := f) (out := out) s2)

/-- A single-witness extraction pattern (offset discrepancy). -/
example (C : ℕ) : ∃ n : ℕ, C < discOffset f out.d out.m n := by
  simpa using (Stage2Output.exists_discOffset_lt (f := f) (out := out) s2 C)

end Stage2RegressionExamples

/-- Convert packaged stage-2 output to `¬ BoundedDiscrepancy out.g` (global boundedness).

This is the cleanest negated-boundedness form for contradiction stages that do *not* want to
carry a fixed step size around.

We derive it from the already-packaged `∀ C, HasDiscrepancyAtLeast out.g C` witness.
-/
theorem not_boundedDiscrepancy (s2 : Stage2Output f out) : ¬ BoundedDiscrepancy out.g := by
  have hunb : ∀ C : ℕ, HasDiscrepancyAtLeast out.g C :=
    s2.forall_hasDiscrepancyAtLeast (f := f) (out := out)
  exact (forall_hasDiscrepancyAtLeast_iff_not_boundedDiscrepancy (f := out.g)).1 hunb

/-- Convert packaged stage-2 output to `¬ BoundedDiscrepancy f` (global boundedness).

This is the “original sequence” consequence of stage 2: once we can produce explicit unbounded
witnesses for the offset discrepancy bundled in `out`, `f` itself cannot have bounded
discrepancy.

This is the exact statement consumed by the top-level theorem `tao2015_not_boundedDiscrepancy`.
-/
theorem not_boundedDiscrepancy_original (s2 : Stage2Output f out) : ¬ BoundedDiscrepancy f := by
  -- The reduction output `out` provides the interface hop from offset witnesses back to global
  -- unbounded discrepancy of `f`.
  exact out.not_boundedDiscrepancy_of_forall_exists_discOffset_gt (f := f) s2.unbounded_discOffset

end Stage2Output

/-- (Stub) Stage 2 deliverable: from `ctx` + `out`, produce the explicit unboundedness normal form
for the offset discrepancy bundled in `out`.

Downstream Tao steps should aim to prove this without needing to know how `ctx` was constructed.

Implementation note:
We keep this as a `theorem` with a single `sorry` (rather than an `axiom`) so the stub remains
locally visible and easy to remove once Stage 2 is proved.
-/
theorem stage2_unbounded_discOffset (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n := by
  -- TODO (Track C / Tao2015 Stage 2): supply the actual reduction proving unbounded offset
  -- discrepancy from the boundedness context `ctx`.
  --
  -- Until then, we keep the entire pipeline composable (and CI-green) with a single stub.
  sorry

/-- Package the stage-2 deliverable `stage2_unbounded_discOffset` as a `Stage2Output` structure.

This is a small convenience wrapper: it turns the witness-normal-form function produced by stage 2
into a single record that exposes the downstream API in `namespace Stage2Output`.
-/
def stage2Output (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    Stage2Output f out :=
  Stage2Output.ofUnboundedDiscOffset (f := f) (out := out)
    (stage2_unbounded_discOffset (f := f) (hf := hf) (ctx := ctx) (out := out))

/-- Strict-inequality form of `stage2_unbounded_discOffset` (`... > B`).

Downstream lemmas often naturally produce or consume discrepancy witnesses with the inequality
oriented as `>`, so this wrapper avoids repeated `gt_iff_lt` conversions.
-/
theorem stage2_unbounded_discOffset_gt (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ∀ B : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > B := by
  intro B
  rcases stage2_unbounded_discOffset (f := f) (hf := hf) (ctx := ctx) (out := out) B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [gt_iff_lt] using hn

/-- Convert the stage-2 witness normal form into a strict-inequality discrepancy witness for the
reduced sequence `out.g` (along the fixed step size `out.d`). -/
theorem stage2_unbounded_discrepancy_gt (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ∀ B : ℕ, ∃ n : ℕ, discrepancy out.g out.d n > B := by
  intro B
  rcases stage2_unbounded_discOffset_gt (f := f) (hf := hf) (ctx := ctx) (out := out) B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  -- Rewrite `discOffset` to `discrepancy` via the reduction output contract.
  simpa [out.discOffset_eq_discrepancy (f := f) (n := n)] using hn

/-- `<`-oriented version of `stage2_unbounded_discrepancy_gt`.

This is the witness normal form that matches
`not_boundedDiscrepancyAlong_iff_forall_exists_discrepancy_gt`.
-/
theorem stage2_unbounded_discrepancy_lt (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ∀ B : ℕ, ∃ n : ℕ, B < discrepancy out.g out.d n := by
  intro B
  rcases stage2_unbounded_discrepancy_gt (f := f) (hf := hf) (ctx := ctx) (out := out) B with ⟨n, hn⟩
  exact ⟨n, by simpa [gt_iff_lt] using hn⟩

/-- Witness-form unboundedness along the reduced fixed step `out.d`, derived from stage 2.

This is just `stage2_unbounded_discrepancy_gt` repackaged into the predicate
`UnboundedDiscrepancyAlong out.g out.d`.
-/
theorem stage2_unboundedDiscrepancyAlong (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    UnboundedDiscrepancyAlong out.g out.d := by
  intro B
  rcases stage2_unbounded_discrepancy_gt (f := f) (hf := hf) (ctx := ctx) (out := out) B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  -- `a > b` is notation for `b < a`.
  simpa [gt_iff_lt] using hn

/-- Stage-2 deliverable implies the negation of the bounded-offset predicate `BoundedDiscOffset`.

This is just `not_boundedDiscOffset_iff_forall_exists_discOffset_gt` applied to the witness
normal form returned by `stage2_unbounded_discOffset`.
-/
theorem stage2_not_boundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ¬ BoundedDiscOffset f out.d out.m := by
  refine (Tao2015.not_boundedDiscOffset_iff_forall_exists_discOffset_gt
      (f := f) (d := out.d) (m := out.m)).2 ?_
  exact stage2_unbounded_discOffset (f := f) (hf := hf) (ctx := ctx) (out := out)

/-- Stage-2 deliverable implies unbounded discrepancy along the reduced step `out.d`
(in the negated-boundedness normal form).

This is a consumer-friendly wrapper around `stage2_not_boundedDiscOffset` plus the
boundedness equivalence packaged by `ReductionOutput`.
-/
theorem stage2_not_boundedDiscrepancyAlong (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ¬ BoundedDiscrepancyAlong out.g out.d := by
  intro hb
  have hnot : ¬ BoundedDiscOffset f out.d out.m :=
    stage2_not_boundedDiscOffset (f := f) (hf := hf) (ctx := ctx) (out := out)
  apply hnot
  -- Convert bounded discrepancy of the reduced sequence into bounded offset discrepancy of `f`.
  exact (out.boundedDiscOffset_iff_boundedDiscrepancyAlong (f := f)).2 hb

/-!
### Stage-2 regression examples

These `example` blocks are intentionally tiny: they serve as compile-time checks that the
consumer-facing API around `stage2Output` / `Stage2Output` continues to compose.

They are not mathematically deep; they just pin down the intended usage pattern.
-/

section Stage2RegressionExamples

variable (f : ℕ → ℤ) (hf : IsSignSequence f) (ctx : Context f) (out : ReductionOutput f)

/-- `stage2Output` packages the stage-2 deliverable into the `Stage2Output` interface. -/
example : Stage2Output f out :=
  stage2Output (f := f) (hf := hf) (ctx := ctx) (out := out)

/-- From stage 2 we can extract a strict-inequality discrepancy witness for the reduced sequence. -/
example (C : ℕ) : ∃ n : ℕ, discrepancy out.g out.d n > C := by
  -- Use the packaged interface.
  simpa using (stage2Output (f := f) (hf := hf) (ctx := ctx) (out := out)).exists_discrepancy_gt C

/-- Stage 2 implies the original sequence does *not* have bounded discrepancy. -/
example : ¬ BoundedDiscrepancy f := by
  simpa using (stage2Output (f := f) (hf := hf) (ctx := ctx) (out := out)).not_boundedDiscrepancy_original

end Stage2RegressionExamples

/-- Sum-level (`Int.natAbs (apSumOffset ...)`) strict-inequality witness form of stage 2.

This is just `stage2_unbounded_discOffset_gt` unfolded through the definitional wrapper
`discOffset`.
-/
theorem stage2_unbounded_natAbs_apSumOffset_gt (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > B := by
  intro B
  rcases stage2_unbounded_discOffset_gt (f := f) (hf := hf) (ctx := ctx) (out := out) B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [discOffset] using hn

/-- `<`-oriented version of `stage2_unbounded_natAbs_apSumOffset_gt`.

Some later steps prefer to work with bounds of the form `B < ...` rather than `... > B`.
-/
theorem stage2_unbounded_natAbs_apSumOffset_lt (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n) := by
  intro B
  rcases stage2_unbounded_natAbs_apSumOffset_gt (f := f) (hf := hf) (ctx := ctx) (out := out) B with ⟨n, hn⟩
  exact ⟨n, by simpa [gt_iff_lt] using hn⟩

/-- Affine-tail (`apSumFrom`) strict-inequality witness form of stage 2.

This is just `stage2_unbounded_natAbs_apSumOffset_gt` rewritten using the bridge lemma
`apSumOffset_eq_apSumFrom_mul`.
-/
theorem stage2_unbounded_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > B := by
  intro B
  rcases stage2_unbounded_natAbs_apSumOffset_gt (f := f) (hf := hf) (ctx := ctx) (out := out) B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  -- Rewrite the offset AP sum into the affine-tail nucleus.
  simpa [Tao2015.apSumOffset_eq_apSumFrom_mul (f := f) (d := out.d) (m := out.m) (n := n)] using hn

/-- `<`-oriented version of `stage2_unbounded_natAbs_apSumFrom_mul_gt`. -/
theorem stage2_unbounded_natAbs_apSumFrom_mul_lt (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumFrom f (out.m * out.d) out.d n) := by
  intro B
  rcases stage2_unbounded_natAbs_apSumFrom_mul_gt (f := f) (hf := hf) (ctx := ctx) (out := out) B with ⟨n, hn⟩
  exact ⟨n, by simpa [gt_iff_lt] using hn⟩

/-!
### Stage-2 derived consequences (unpackaged)

These lemmas are tiny wrappers that let downstream code use the stage-2 deliverable
`stage2_unbounded_discOffset` *without* first packaging it into a `Stage2Output` record.

They are intentionally “one-line” interface glue:
- witness form (`discOffset`) → discrepancy along the reduced sequence (`out.g`, fixed step `out.d`)
- witness form → negated boundedness forms
- witness form → the original-sequence consequence `¬ BoundedDiscrepancy f`
-/

/-- Stage-2 witness form implies fixed-step unbounded discrepancy for the reduced sequence `out.g`.

This is the canonical consumer-facing normal form for stage 3: we now have explicit witnesses for
arbitrarily large discrepancy along a *fixed* step size `out.d`.
-/
theorem stage2_forall_hasDiscrepancyAtLeastAlong_unpacked (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C := by
  -- This is exactly the `ReductionOutput` witness-transport lemma applied to the stage-2 deliverable.
  apply ReductionOutput.forall_hasDiscrepancyAtLeastAlong_of_forall_exists_discOffset_gt (f := f) (out := out)
  intro C
  -- Stage 2 provides witnesses `C < discOffset ...` for all thresholds `C`.
  rcases stage2_unbounded_discOffset (f := f) (hf := hf) (ctx := ctx) (out := out) C with ⟨n, hn⟩
  exact ⟨n, hn⟩

/-- Stage-2 witness form implies `¬ BoundedDiscrepancyAlong out.g out.d`. -/
theorem stage2_not_boundedDiscrepancyAlong_unpacked (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ¬ BoundedDiscrepancyAlong out.g out.d := by
  -- Use the standard witness normal form for `¬ BoundedDiscrepancyAlong`.
  have hunb : ∀ B : ℕ, ∃ n : ℕ, B < discrepancy out.g out.d n := by
    intro B
    rcases stage2_unbounded_discOffset (f := f) (hf := hf) (ctx := ctx) (out := out) B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [out.discOffset_eq_discrepancy (f := f) (n := n)] using hn
  exact (Tao2015.not_boundedDiscrepancyAlong_iff_forall_exists_discrepancy_gt (g := out.g) (d := out.d)).2 hunb

/-- Stage-2 witness form implies `¬ BoundedDiscrepancy f` for the original sequence. -/
theorem stage2_not_boundedDiscrepancy_original_unpacked (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ¬ BoundedDiscrepancy f := by
  -- The reduction output `out` already knows how to turn unbounded `discOffset` witnesses into global
  -- unbounded discrepancy of `f`.
  exact out.not_boundedDiscrepancy_of_forall_exists_discOffset_lt (f := f)
    (stage2_unbounded_discOffset (f := f) (hf := hf) (ctx := ctx) (out := out))

/-- Package the stage-2 deliverable into a `Stage2Output` record.

This is “pipeline glue”: later stages can be stated to consume `Stage2Output` without caring
whether it came from a constructive stage-2 proof or from a negated boundedness hypothesis.
-/
noncomputable def stage2_output (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) : Stage2Output f out := by
  refine ⟨?_⟩
  exact stage2_unbounded_discOffset (f := f) (hf := hf) (ctx := ctx) (out := out)

@[simp] theorem stage2_output_unbounded_discOffset (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    (stage2_output (f := f) (hf := hf) (ctx := ctx) (out := out)).unbounded_discOffset =
      stage2_unbounded_discOffset (f := f) (hf := hf) (ctx := ctx) (out := out) := by
  rfl

/-- `stage2_output` is definitionally the same packaging as `stage2Output`.

We keep both names because different parts of the file historically used different casing; this
lemma lets downstream code normalize them away with `simp`.
-/
@[simp] theorem stage2_output_eq_stage2Output (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    stage2_output (f := f) (hf := hf) (ctx := ctx) (out := out) =
      stage2Output (f := f) (hf := hf) (ctx := ctx) (out := out) := by
  rfl

/-!
### Stage-2 alternative entry point

While `stage2_unbounded_discOffset` is the intended **constructive** deliverable of stage 2,
we often want to *start* stage-2 reasoning from the negated boundedness form
`¬ BoundedDiscOffset f out.d out.m`.

The next definition packages that hypothesis into a `Stage2Output` using the general-purpose
constructor `Stage2Output.ofNotBoundedDiscOffset`.
-/

/-- Build a `Stage2Output` directly from the negated boundedness form.

This is useful when a downstream reduction produces `¬ BoundedDiscOffset …` first and only later
needs explicit witnesses.
-/
noncomputable def stage2_output_of_not_boundedDiscOffset (f : ℕ → ℤ) (out : ReductionOutput f)
    (h : ¬ BoundedDiscOffset f out.d out.m) : Stage2Output f out :=
  Stage2Output.ofNotBoundedDiscOffset (f := f) (out := out) h

@[simp] theorem stage2_output_of_not_boundedDiscOffset_unbounded (f : ℕ → ℤ) (out : ReductionOutput f)
    (h : ¬ BoundedDiscOffset f out.d out.m) :
    (stage2_output_of_not_boundedDiscOffset (f := f) (out := out) h).unbounded_discOffset =
      (not_boundedDiscOffset_iff_forall_exists_discOffset_gt (f := f) (d := out.d) (m := out.m)).1 h := by
  rfl

/-- Build a `Stage2Output` directly from the negated boundedness form
`¬ BoundedDiscrepancyAlong out.g out.d`.

This is useful when a downstream reduction produces the unboundedness statement in terms of the
*reduced* sequence `out.g`, and only later wants explicit offset-discrepancy witnesses for `f`.
-/
noncomputable def stage2_output_of_not_boundedDiscrepancyAlong (f : ℕ → ℤ) (out : ReductionOutput f)
    (h : ¬ BoundedDiscrepancyAlong out.g out.d) : Stage2Output f out :=
  Stage2Output.ofNotBoundedDiscrepancyAlong (f := f) (out := out) h

/-- `rfl` expansion for the `unbounded_discOffset` field of
`stage2_output_of_not_boundedDiscrepancyAlong`.

Not marked `[simp]`: it expands to a large witness-producing lambda (inherited from
`Stage2Output.ofNotBoundedDiscrepancyAlong`).
-/
theorem stage2_output_of_not_boundedDiscrepancyAlong_unbounded (f : ℕ → ℤ) (out : ReductionOutput f)
    (h : ¬ BoundedDiscrepancyAlong out.g out.d) :
    (stage2_output_of_not_boundedDiscrepancyAlong (f := f) (out := out) h).unbounded_discOffset =
      (Stage2Output.ofNotBoundedDiscrepancyAlong (f := f) (out := out) h).unbounded_discOffset := by
  rfl

/-- Extract the unboundedness witness normal form directly from `¬ BoundedDiscOffset`.

This is a tiny packaging lemma, but it is the most common “first move” when entering stage 2
from a negated boundedness hypothesis.
-/
theorem stage2_unbounded_discOffset_of_not_boundedDiscOffset (f : ℕ → ℤ) (out : ReductionOutput f)
    (h : ¬ BoundedDiscOffset f out.d out.m) :
    ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n := by
  exact (not_boundedDiscOffset_iff_forall_exists_discOffset_gt (f := f) (d := out.d) (m := out.m)).1 h

/-- Extract the unboundedness witness normal form directly from `¬ BoundedDiscrepancyAlong out.g out.d`.

This is the most common entry point when a downstream reduction produces unboundedness for the
*reduced* sequence first, and only later wants to talk about the bundled offset discrepancy of `f`.
-/
theorem stage2_unbounded_discOffset_of_not_boundedDiscrepancyAlong (f : ℕ → ℤ) (out : ReductionOutput f)
    (h : ¬ BoundedDiscrepancyAlong out.g out.d) :
    ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n := by
  exact (out.not_boundedDiscrepancyAlong_iff_forall_exists_discOffset_lt (f := f)).1 h

/-- Extract a single witness `> C` from `¬ BoundedDiscOffset …`.

This is the “one-shot” form of `stage2_unbounded_discOffset_of_not_boundedDiscOffset`.
-/
theorem stage2_exists_discOffset_gt_of_not_boundedDiscOffset (f : ℕ → ℤ) (out : ReductionOutput f)
    (h : ¬ BoundedDiscOffset f out.d out.m) (C : ℕ) :
    ∃ n : ℕ, discOffset f out.d out.m n > C := by
  rcases stage2_unbounded_discOffset_of_not_boundedDiscOffset (f := f) (out := out) h C with ⟨n, hn⟩
  exact ⟨n, hn⟩

/-- `C < discOffset ...` form of `stage2_exists_discOffset_gt_of_not_boundedDiscOffset`. -/
theorem stage2_exists_discOffset_lt_of_not_boundedDiscOffset (f : ℕ → ℤ) (out : ReductionOutput f)
    (h : ¬ BoundedDiscOffset f out.d out.m) (C : ℕ) :
    ∃ n : ℕ, C < discOffset f out.d out.m n := by
  simpa [gt_iff_lt] using
    stage2_exists_discOffset_gt_of_not_boundedDiscOffset (f := f) (out := out) h C

/-- Stage-2 helper: the unboundedness witness normal form implies `¬ BoundedDiscOffset …`.

This is just a packaging lemma, but it is the *exact* consumer statement most later stages want:
we often produce explicit witnesses and then immediately flip to a negated boundedness hypothesis.
-/
theorem stage2_not_boundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ¬ BoundedDiscOffset f out.d out.m := by
  have hwit : ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n :=
    stage2_unbounded_discOffset (f := f) (hf := hf) (ctx := ctx) (out := out)
  -- use the prepackaged equivalence lemma to flip witness-normal-form to `¬ bounded`.
  exact (stage2_witness_discOffset_iff_not_boundedDiscOffset (f := f) (out := out)).1 hwit

/-- Stage-2 contradiction: `Context f` gives bounded offset discrepancy, while stage 2 supplies
unbounded offset-discrepancy witnesses.

This lemma is a small but common “glue step” when a downstream stage wants to derive `False`.
-/
theorem stage2_contradiction (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) : False := by
  have hb : BoundedDiscOffset f out.d out.m :=
    boundedDiscOffset_of_context (f := f) (ctx := ctx) (out := out)
  have hnb : ¬ BoundedDiscOffset f out.d out.m :=
    stage2_not_boundedDiscOffset (f := f) (hf := hf) (ctx := ctx) (out := out)
  exact hnb hb

/-- Stage-2 helper: the same witness normal form implies `¬ BoundedDiscrepancyAlong out.g out.d`.

This is the main “interface hop”: once the reduction has fixed `d`, contradiction stages tend to
reason directly about boundedness along that `d`.
-/
theorem stage2_not_boundedDiscrepancyAlong (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ¬ BoundedDiscrepancyAlong out.g out.d := by
  have hwit : ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n :=
    stage2_unbounded_discOffset (f := f) (hf := hf) (ctx := ctx) (out := out)
  exact (stage2_witness_discOffset_iff_not_boundedDiscrepancyAlong (f := f) (out := out)).1 hwit

/-- Stage-2 helper: the stage-2 output already implies the *global* contradiction target
`¬ BoundedDiscrepancy f`.

This is the final “hop” in the plane: stage 2 produces unbounded offset discrepancy, the
reduction interface converts that to unboundedness along `out.d`, and then `out` upgrades that
to unboundedness of `f` itself.
-/
theorem stage2_not_boundedDiscrepancy (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ¬ BoundedDiscrepancy f := by
  have hnotAlong : ¬ BoundedDiscrepancyAlong out.g out.d :=
    stage2_not_boundedDiscrepancyAlong (f := f) (hf := hf) (ctx := ctx) (out := out)
  exact out.not_boundedDiscrepancy_of_not_boundedDiscrepancyAlong (f := f) hnotAlong

/-- Interface plumbing: convert the stage-2 output to the unboundedness normal form for the
*reduced* sequence discrepancy.

This is a tiny lemma, but it's the canonical consumer statement: downstream stages tend to
produce offset-discrepancy witnesses for the original sequence `f`, while the contradiction stage
often wants witnesses for the reduced sequence `out.g`.
-/
theorem stage2_unbounded_discrepancy (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ∀ B : ℕ, ∃ n : ℕ, B < discrepancy out.g out.d n := by
  intro B
  rcases stage2_unbounded_discOffset (f := f) (hf := hf) (ctx := ctx) (out := out) B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  -- rewrite `discOffset` to `discrepancy` using the reduction interface
  simpa [out.discOffset_eq_discrepancy (f := f) (n := n)] using hn

/-- `natAbs` version of `stage2_unbounded_discrepancy`. -/
theorem stage2_unbounded_natAbs_apSum (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSum out.g out.d n) := by
  intro B
  rcases stage2_unbounded_discrepancy (f := f) (hf := hf) (ctx := ctx) (out := out) B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [discrepancy] using hn

/-- Stage-2 witness normal form rewritten into the affine nucleus `apSumFrom` for the original
sequence `f`.

This is a convenience wrapper around `stage2_unbounded_natAbs_apSum` plus the stage-1 contract
`ReductionOutput.apSum_eq_apSumFrom_mul`.
-/
theorem stage2_unbounded_natAbs_apSumFrom_mul (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumFrom f (out.m * out.d) out.d n) := by
  intro B
  rcases stage2_unbounded_natAbs_apSum (f := f) (hf := hf) (ctx := ctx) (out := out) B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  -- Rewrite the reduced AP sum into the affine nucleus on the original sequence.
  simpa [out.apSum_eq_apSumFrom_mul (f := f) (n := n)] using hn

/-- Strict-inequality (`... > B`) version of `stage2_unbounded_natAbs_apSumFrom_mul`.

This wrapper avoids frequent `gt_iff_lt` rewriting in downstream stages.
-/
theorem stage2_unbounded_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > B := by
  intro B
  rcases stage2_unbounded_natAbs_apSumFrom_mul (f := f) (hf := hf) (ctx := ctx) (out := out) B with ⟨n, hn⟩
  exact ⟨n, by simpa [gt_iff_lt] using hn⟩

/-- Convenience: for each threshold `C`, produce an affine-tail AP-sum witness in the form
`C < Int.natAbs (apSumFrom ...)`.

This is a “one-shot” version of `stage2_unbounded_natAbs_apSumFrom_mul` with a more descriptive
name.
-/
theorem stage2_exists_natAbs_apSumFrom_mul_lt (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) (C : ℕ) :
    ∃ n : ℕ, C < Int.natAbs (apSumFrom f (out.m * out.d) out.d n) := by
  exact stage2_unbounded_natAbs_apSumFrom_mul (f := f) (hf := hf) (ctx := ctx) (out := out) C

/-- `... > C` version of `stage2_exists_natAbs_apSumFrom_mul_lt`. -/
theorem stage2_exists_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) (C : ℕ) :
    ∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C := by
  rcases stage2_exists_natAbs_apSumFrom_mul_lt (f := f) (hf := hf) (ctx := ctx) (out := out) C with ⟨n, hn⟩
  exact ⟨n, by simpa [gt_iff_lt] using hn⟩

/-!
### Stage-2 → pipeline-friendly discrepancy predicates

Downstream stages often want the existential witness form at a particular threshold, or the
`HasDiscrepancyAtLeastAlong` predicate (fixed `d`).

The lemmas below are tiny wrappers around `stage2_unbounded_discrepancy` /
`stage2_unbounded_natAbs_apSum`.
-/

/-- Stage-2 consequence: for every threshold `C`, the reduced sequence `out.g` has a witness
of discrepancy `> C` along `out.d`.

This is the most common consumer statement for fixed-step downstream reductions.
-/
theorem stage2_forall_hasDiscrepancyAtLeastAlong (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C := by
  intro C
  rcases stage2_unbounded_natAbs_apSum (f := f) (hf := hf) (ctx := ctx) (out := out) C with ⟨n, hn⟩
  exact ⟨n, by simpa [HasDiscrepancyAtLeastAlong] using hn⟩

/-- Stage-2 consequence: for every threshold `C`, the reduced sequence `out.g` satisfies the
ambient `HasDiscrepancyAtLeast` predicate.

This is just `stage2_forall_hasDiscrepancyAtLeastAlong` promoted via the `d`-quantifier.
-/
theorem stage2_forall_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast out.g C := by
  intro C
  exact
    HasDiscrepancyAtLeastAlong.toHasDiscrepancyAtLeast (f := out.g) (d := out.d) (C := C) out.hd
      (stage2_forall_hasDiscrepancyAtLeastAlong (f := f) (hf := hf) (ctx := ctx) (out := out) C)

/-- Conversely, if you have unboundedness witnesses for `natAbs (apSum out.g out.d n)`, you also
get witnesses for the discrepancy wrapper.
-/
theorem stage2_unbounded_discrepancy_of_unbounded_natAbs_apSum (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f)
    (h : ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSum out.g out.d n)) :
    ∀ B : ℕ, ∃ n : ℕ, B < discrepancy out.g out.d n := by
  intro B
  rcases h B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [discrepancy] using hn

/-- `natAbs` version of `stage2_unbounded_discOffset`.

This is often the exact statement a downstream reduction stage naturally produces, since it may
work with raw AP sums first and only introduce the `discOffset` wrapper later.
-/
theorem stage2_unbounded_natAbs_apSumOffset (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n) := by
  intro B
  rcases stage2_unbounded_discOffset (f := f) (hf := hf) (ctx := ctx) (out := out) B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [discOffset] using hn

/-- Stage-2 consequence: for every threshold `C`, we have an offset-discrepancy witness
`C < discOffset f out.d out.m n`.

This is the most common “back on the original sequence `f`” form used in later reductions.
-/
theorem stage2_forall_exists_discOffset_lt (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ∀ C : ℕ, ∃ n : ℕ, C < discOffset f out.d out.m n := by
  intro C
  -- `stage2_unbounded_discOffset` already provides the witness form with `<`.
  exact stage2_unbounded_discOffset (f := f) (hf := hf) (ctx := ctx) (out := out) C

/-- Same as `stage2_forall_exists_discOffset_lt`, but with the inequality oriented as `... > C`. -/
theorem stage2_forall_exists_discOffset_gt (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ∀ C : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > C := by
  intro C
  rcases stage2_forall_exists_discOffset_lt (f := f) (hf := hf) (ctx := ctx) (out := out) C with ⟨n, hn⟩
  exact ⟨n, by simpa [gt_iff_lt] using hn⟩

/-- Conversely, an unboundedness normal form in terms of `natAbs (apSumOffset …)` implies the
`discOffset`-wrapper normal form.
-/
theorem stage2_unbounded_discOffset_of_unbounded_natAbs_apSumOffset (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f)
    (h : ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n)) :
    ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n := by
  intro B
  rcases h B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [discOffset] using hn

/-- (Stub) Tao 2015 contradiction stage.

Given the structured output of the reduction stage, a proof of global bounded discrepancy,
derive a contradiction.

This lemma is intentionally *interface-only*: once `stage2_unbounded_discOffset` is filled in,
this proof should require no further changes.
-/
theorem contradiction (f : ℕ → ℤ) (hf : IsSignSequence f)
    (hb : BoundedDiscrepancy f) (ctx : Context f) (out : ReductionOutput f) : False := by
  have hunb : ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n :=
    stage2_unbounded_discOffset (f := f) (hf := hf) (ctx := ctx) (out := out)
  have hnot : ¬ BoundedDiscrepancy f :=
    out.not_boundedDiscrepancy_of_forall_exists_discOffset_gt (f := f) hunb
  exact hnot hb

end Tao2015

/-- Tao 2015: Erdős discrepancy, packaged as a “not bounded discrepancy” statement.

This remains a conjecture stub. The body is written in Lean-friendly stages:

1. convert `BoundedDiscrepancy f` into a `Tao2015.Context f` (choose an explicit bound `B`)
2. run a reduction step producing a structured object
3. run a contradiction step

Keeping the stages typed and named makes it possible to fill in the proof incrementally.
-/
theorem tao2015_not_boundedDiscrepancy (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ BoundedDiscrepancy f := by
  intro hb
  classical
  let ctx : Tao2015.Context f := Tao2015.Context.ofBoundedDiscrepancy (f := f) hb
  let out : Tao2015.ReductionOutput f := Tao2015.reduction (f := f) (hf := hf) ctx
  exact Tao2015.contradiction (f := f) (hf := hf) (hb := hb) (ctx := ctx) (out := out)

end MoltResearch
