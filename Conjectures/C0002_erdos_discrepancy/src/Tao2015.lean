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
### Downstream contradiction stage (still a stub)

The point of the “plane” architecture is that once we have *any* downstream stage that produces
an explicit unboundedness witness for the offset discrepancy bundled in `out`, the rest of the
argument is pure interface plumbing.

So we isolate that future deliverable as a named lemma:
- `stage2_unbounded_discOffset` (currently `sorry`)

and make the top-level `contradiction` proof *structural* and `sorry`-free.
-/

/-- (Stub) Stage 2 deliverable: from `ctx` + `out`, produce the explicit unboundedness normal form
for the offset discrepancy bundled in `out`.

Downstream Tao steps should aim to prove this without needing to know how `ctx` was constructed.
-/
theorem stage2_unbounded_discOffset (f : ℕ → ℤ) (hf : IsSignSequence f)
    (ctx : Context f) (out : ReductionOutput f) :
    ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n := by
  sorry

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
