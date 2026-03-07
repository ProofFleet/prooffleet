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
theorem apSumOffset_add_pre (f : ℕ → ℤ) (d m₁ m₂ n : ℕ) :
    apSumOffset f d (m₁ + m₂) n = apSumOffset (fun k => f (k + m₁ * d)) d m₂ n := by
  -- Expand both sides to AP sums of shifted sequences.
  -- LHS: shift by `(m₁+m₂)*d`.
  -- RHS: first shift by `m₁*d`, then shift again by `m₂*d`.
  simp [apSumOffset_eq_apSum_shift_add, Nat.add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm, Nat.mul_assoc, Nat.left_distrib]

/-- Reverse orientation of `apSumOffset_add_pre`.

We do not mark either direction `[simp]` to avoid rewriting loops.
-/
theorem apSumOffset_add_pre' (f : ℕ → ℤ) (d m₁ m₂ n : ℕ) :
    apSumOffset (fun k => f (k + m₁ * d)) d m₂ n = apSumOffset f d (m₁ + m₂) n := by
  simpa using (apSumOffset_add_pre (f := f) (d := d) (m₁ := m₁) (m₂ := m₂) (n := n)).symm

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

/-- Expand the defining equation of `g`. -/
@[simp] theorem g_apply (out : ReductionOutput f) (k : ℕ) : out.g k = f (k + out.m * out.d) := by
  simpa [out.g_eq]

/-- Convenience rewrite: `out.g` is definitionally the shift of `f` by `out.m*out.d`. -/
@[simp] theorem g_eq_shift (out : ReductionOutput f) : out.g = fun k => f (k + out.m * out.d) :=
  out.g_eq

/-- `HasDiscrepancyAtLeastAlong` is invariant under rewriting the reduced sequence via `out.g_eq`. -/
theorem hasDiscrepancyAtLeastAlong_congr_shift (out : ReductionOutput f) (C : ℕ) :
    HasDiscrepancyAtLeastAlong out.g out.d C ↔
      HasDiscrepancyAtLeastAlong (fun k => f (k + out.m * out.d)) out.d C := by
  simpa [out.g_eq]

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

/-- Function-extensional form of the discrepancy rewrite rule. -/
theorem discrepancy_contract_funext (out : ReductionOutput f) :
    (fun n => discrepancy out.g out.d n) = fun n => discOffset f out.d out.m n := by
  funext n
  -- Both sides are definitional wrappers around `Int.natAbs`.
  simp [discrepancy, discOffset, out.apSum_contract]

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

/-- The `apSum_contract` field is redundant: it is implied by `g_eq`.

Keeping this lemma around makes it easy to refactor the interface later.
-/
theorem apSum_contract_eq_derived (out : ReductionOutput f) :
    out.apSum_contract = out.apSum_contract_derived (f := f) := by
  classical
  funext n
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

/-- Rewrite `apSumFrom f (m*d)` as an AP sum of the reduced sequence `out.g`.

This is the most common “start at the affine point” normal form used in Tao-style reductions.
-/
theorem apSumFrom_eq_apSum (out : ReductionOutput f) (n : ℕ) :
    apSumFrom f (out.m * out.d) out.d n = apSum out.g out.d n := by
  -- `apSumFrom` is an `apSum` of the shifted sequence; rewrite using `out.g_eq`.
  simpa [out.g_eq] using
    (apSumFrom_eq_apSum_shift_add (f := f) (a := out.m * out.d) (d := out.d) (n := n))

/-- Rewrite `apSumFrom f (m*d)` as an offset AP sum of `f`.

This is a direct bridge between the two “tail sum” APIs in the discrepancy substrate.
-/
theorem apSumFrom_eq_apSumOffset (out : ReductionOutput f) (n : ℕ) :
    apSumFrom f (out.m * out.d) out.d n = apSumOffset f out.d out.m n := by
  -- Rewrite both sides to AP sums of the same shifted sequence.
  simp [apSumFrom_eq_apSum_shift_add, apSumOffset_eq_apSum_shift_add]

/-!
### Peeling bundled offsets

Many downstream reductions will accumulate offsets of the form `(out.m + m₂) * out.d`.
The next lemmas let you “peel off” the initial `out.m*out.d` shift encoded by
`out.g`, turning an offset sum/discrepancy of `f` into an offset sum/discrepancy of `out.g`.
-/

/-- Peel the bundled offset in `out` at the AP-sum level.

This is `apSumOffset_add_pre` specialized to the shift packed in `out.g`.
-/
theorem apSumOffset_add_eq_apSumOffset_g (out : ReductionOutput f) (m₂ n : ℕ) :
    apSumOffset f out.d (out.m + m₂) n = apSumOffset out.g out.d m₂ n := by
  -- Re-associate the offset, then rewrite the shifted sequence using `out.g_eq`.
  simpa [out.g_eq] using
    (Tao2015.apSumOffset_add_pre (f := f) (d := out.d) (m₁ := out.m) (m₂ := m₂) (n := n))

/-- Peel the bundled offset in `out` at the discrepancy level.

This is the `discOffset` analogue of `apSumOffset_add_eq_apSumOffset_g`.
-/
theorem discOffset_add_eq_discOffset_g (out : ReductionOutput f) (m₂ n : ℕ) :
    discOffset f out.d (out.m + m₂) n = discOffset out.g out.d m₂ n := by
  -- `discOffset` is just `natAbs` of `apSumOffset`.
  simp [discOffset, out.apSumOffset_add_eq_apSumOffset_g (f := f) (m₂ := m₂) (n := n)]

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

/-- Discrepancy rewrite rule: the discrepancy of `out.g` along `out.d` is the offset discrepancy of `f`.

This is just the `natAbs` version of `apSum_eq_apSumOffset`.

Marked `[simp]` because it is the most common consumer rewrite.
-/
@[simp] theorem discrepancy_eq_discOffset (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n = discOffset f out.d out.m n := by
  -- Both sides are definitional wrappers around `Int.natAbs`.
  simp [discrepancy, discOffset, out.apSum_contract]

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

/-- Negated form of `boundedDiscrepancyAlong_iff_boundedDiscOffset`.

This is useful because many “unboundedness” stages in Tao’s pipeline are naturally phrased as
`¬ ∃ B, ∀ n, ...`.
-/
theorem not_boundedDiscrepancyAlong_iff_not_boundedDiscOffset (out : ReductionOutput f) :
    ¬ BoundedDiscrepancyAlong out.g out.d ↔ ¬ BoundedDiscOffset f out.d out.m := by
  simpa using not_congr (out.boundedDiscrepancyAlong_iff_boundedDiscOffset (f := f))

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

/-- Re-associate offsets: shifting by `(m₁+m₂)*d` is the same as shifting by `m₁*d` and then by
`m₂*d`.

This lemma is small but shows up constantly when “chunking” offsets in the Tao pipeline.
-/
theorem apSumOffset_add (f : ℕ → ℤ) (d m₁ m₂ n : ℕ) :
    apSumOffset f d (m₁ + m₂) n =
      apSumOffset (fun k => f (k + m₁ * d)) d m₂ n := by
  -- Expand both sides to `apSum` of a shifted sequence and simplify arithmetic.
  simp [apSumOffset_eq_apSum_shift_add, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm]

/-- The discrepancy form of `apSumOffset_add`. -/
theorem discOffset_add (f : ℕ → ℤ) (d m₁ m₂ n : ℕ) :
    discOffset f d (m₁ + m₂) n =
      discOffset (fun k => f (k + m₁ * d)) d m₂ n := by
  -- `discOffset` is just `Int.natAbs` of `apSumOffset`.
  simp [discOffset, apSumOffset_add]

/-- Re-associate offsets, reverse orientation of `apSumOffset_add`.

This form is often convenient when you are already working with the shifted sequence
`fun k => f (k + m₁*d)`.
-/
theorem apSumOffset_shift_add (f : ℕ → ℤ) (d m₁ m₂ n : ℕ) :
    apSumOffset (fun k => f (k + m₁ * d)) d m₂ n = apSumOffset f d (m₁ + m₂) n := by
  simpa using (apSumOffset_add (f := f) (d := d) (m₁ := m₁) (m₂ := m₂) (n := n)).symm

/-- Discrepancy form of `apSumOffset_shift_add`. -/
theorem discOffset_shift_add (f : ℕ → ℤ) (d m₁ m₂ n : ℕ) :
    discOffset (fun k => f (k + m₁ * d)) d m₂ n = discOffset f d (m₁ + m₂) n := by
  simpa [discOffset] using
    congrArg Int.natAbs (apSumOffset_shift_add (f := f) (d := d) (m₁ := m₁) (m₂ := m₂) (n := n))

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
- `stage2_unbounded_discOffset` (currently `sorry`)

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

/-- Stage-2 output transported to the reduced sequence `out.g` (discrepancy witness form). -/
theorem unbounded_discrepancy (s2 : Stage2Output f out) :
    ∀ B : ℕ, ∃ n : ℕ, B < discrepancy out.g out.d n := by
  intro B
  rcases s2.unbounded_discOffset B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [out.discOffset_eq_discrepancy (f := f) (n := n)] using hn

/-- `natAbs` witness form for the bundled *offset sums*.

This is just `Stage2Output.unbounded_discOffset` with `discOffset` unfolded.
-/
theorem unbounded_natAbs_apSumOffset (s2 : Stage2Output f out) :
    ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n) := by
  intro B
  rcases s2.unbounded_discOffset B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [discOffset] using hn

/-- `natAbs` witness form for the reduced *AP sums* `apSum out.g out.d`.

This is the most “sum-level” consumer statement: it avoids both `discOffset` and `discrepancy`.
-/
theorem unbounded_natAbs_apSum (s2 : Stage2Output f out) :
    ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSum out.g out.d n) := by
  intro B
  rcases s2.unbounded_discrepancy (f := f) (out := out) B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [discrepancy] using hn

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

/-- A `Stage2Output` gives the ambient `HasDiscrepancyAtLeast` predicate for every threshold.

This is just `hasDiscrepancyAtLeastAlong` promoted via the `d`-quantifier.
-/
theorem hasDiscrepancyAtLeast (s2 : Stage2Output f out) (C : ℕ) :
    HasDiscrepancyAtLeast out.g C := by
  -- Promote fixed-step discrepancy witness to the existential-over-`d` form.
  exact HasDiscrepancyAtLeastAlong.toHasDiscrepancyAtLeast (f := out.g) (d := out.d) (C := C)
    out.hd (s2.hasDiscrepancyAtLeastAlong (f := f) (out := out) C)

/-- A `Stage2Output` yields a `discOffset` witness `> C` for the bundled parameters.

This is the “original-sequence” form of `Stage2Output.hasDiscrepancyAtLeastAlong`.
-/
theorem exists_discOffset_gt (s2 : Stage2Output f out) (C : ℕ) :
    ∃ n : ℕ, discOffset f out.d out.m n > C := by
  rcases s2.unbounded_discOffset C with ⟨n, hn⟩
  exact ⟨n, hn⟩

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

/-- A `Stage2Output` yields an AP-sum witness `> C` in raw `natAbs` form for the reduced sequence.

This is the `apSum` analogue of `exists_discrepancy_gt`.
-/
theorem exists_natAbs_apSum_gt (s2 : Stage2Output f out) (C : ℕ) :
    ∃ n : ℕ, Int.natAbs (apSum out.g out.d n) > C := by
  rcases s2.exists_discrepancy_gt (f := f) (out := out) C with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [discrepancy] using hn

/-- Convert packaged stage-2 output to the propositional negated boundedness form. -/
theorem not_boundedDiscOffset (s2 : Stage2Output f out) : ¬ BoundedDiscOffset f out.d out.m := by
  exact (stage2_witness_discOffset_iff_not_boundedDiscOffset (f := f) (out := out)).1 s2.unbounded_discOffset

/-- Convert packaged stage-2 output to `¬ BoundedDiscrepancyAlong out.g out.d`. -/
theorem not_boundedDiscrepancyAlong (s2 : Stage2Output f out) : ¬ BoundedDiscrepancyAlong out.g out.d := by
  exact (stage2_witness_discOffset_iff_not_boundedDiscrepancyAlong (f := f) (out := out)).1 s2.unbounded_discOffset

end Stage2Output

/-- (Stub) Stage 2 deliverable: from `ctx` + `out`, produce the explicit unboundedness normal form
for the offset discrepancy bundled in `out`.

Downstream Tao steps should aim to prove this without needing to know how `ctx` was constructed.
-/
theorem stage2_unbounded_discOffset (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n := by
  sorry

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
