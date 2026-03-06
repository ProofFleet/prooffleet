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

/-- Offset-sum bound in terms of the discrepancy wrapper `discOffset`. -/
theorem bound_discOffset (ctx : Context f) (d m n : ℕ) (hd : d > 0) :
    discOffset f d m n ≤ ctx.B + ctx.B := by
  simpa [discOffset] using (ctx.bound_apSumOffset (f := f) (d := d) (m := m) (n := n) hd)

/-- Bound a shifted homogeneous AP sum by reducing it to an offset sum.

This is the “translation by a multiple of `d`” normal form.
-/
theorem bound_apSum_shift_add (ctx : Context f) (d m n : ℕ) (hd : d > 0) :
    Int.natAbs (apSum (fun k => f (k + m * d)) d n) ≤ ctx.B + ctx.B := by
  -- `apSumOffset f d m n = apSum (fun k => f (k + m*d)) d n`.
  simpa [apSumOffset_eq_apSum_shift_add] using
    (ctx.bound_apSumOffset (f := f) (d := d) (m := m) (n := n) hd)

end Context

/-- Output of the first major reduction stage of Tao 2015.

We intentionally keep this opaque at first; the goal is to replace this with the first
*stable* structured object we can state cleanly in Lean.
-/
structure ReductionOutput (f : ℕ → ℤ) : Type where
  dummy : Unit := ()

/-- (Stub) Tao 2015 reduction stage.

Given a sign sequence `f` and a boundedness context, produce a structured object.

In the real proof this will likely involve introducing auxiliary models / averaged objects.
-/
theorem reduction (f : ℕ → ℤ) (hf : IsSignSequence f) (ctx : Context f) :
    ReductionOutput f := by
  sorry

/-- (Stub) Tao 2015 contradiction stage.

Given the structured output of the reduction stage, derive a contradiction.
-/
theorem contradiction (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) : False := by
  sorry

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
  exact Tao2015.contradiction (f := f) (hf := hf) (ctx := ctx) (out := out)

end MoltResearch
