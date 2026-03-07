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

/-- The discrepancy bound corresponding to `bound_apSum`. -/
theorem bound_discrepancy (ctx : Context f) (d n : ℕ) (hd : d > 0) :
    discrepancy f d n ≤ ctx.B := by
  simpa [discrepancy] using (ctx.bound_apSum (f := f) (d := d) (n := n) hd)

/-- Discrepancy bound for shifted AP sums (as in `bound_apSum_shift_add`). -/
theorem bound_discrepancy_shift_add (ctx : Context f) (d m n : ℕ) (hd : d > 0) :
    discrepancy (fun k => f (k + m * d)) d n ≤ ctx.B + ctx.B := by
  simpa [discrepancy] using (ctx.bound_apSum_shift_add (f := f) (d := d) (m := m) (n := n) hd)

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
theorem g_apply (out : ReductionOutput f) (k : ℕ) : out.g k = f (k + out.m * out.d) := by
  simpa [out.g_eq]

/-- Rewrite `apSum out.g out.d` as an offset sum of `f`.

This is the main “bridge” lemma: it lets us convert bounds on `apSumOffset f` into bounds
on the auxiliary AP sums for `g`.
-/
theorem apSum_eq_apSumOffset (out : ReductionOutput f) (n : ℕ) :
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

/-- Discrepancy rewrite rule: the discrepancy of `out.g` along `out.d` is the offset discrepancy of `f`.

This is just the `natAbs` version of `apSum_eq_apSumOffset`.
-/
theorem discrepancy_eq_discOffset (out : ReductionOutput f) (n : ℕ) :
    discrepancy out.g out.d n = discOffset f out.d out.m n := by
  -- Both sides are definitional wrappers around `Int.natAbs`.
  simp [discrepancy, discOffset, out.apSum_contract]

/-- The same rewrite rule, but oriented in the other direction. -/
theorem discOffset_eq_discrepancy (out : ReductionOutput f) (n : ℕ) :
    discOffset f out.d out.m n = discrepancy out.g out.d n := by
  simpa using (out.discrepancy_eq_discOffset (f := f) (n := n)).symm

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

end ReductionOutput

/-- (Stub) Tao 2015 reduction stage.

Given a sign sequence `f` and a boundedness context, produce a structured object.

For now we instantiate the interface with the trivial choice `d = 1`, `m = 0`, `g = f`.
This is enough to let downstream code *use* the interface immediately.
-/
theorem reduction (f : ℕ → ℤ) (hf : IsSignSequence f) (ctx : Context f) :
    ReductionOutput f := by
  refine
    ⟨1, 0, by decide, f, hf, (by simp), ?_, ?_⟩
  · intro n
    -- `apSumOffset f 1 0 n` is definitionally the same as `apSum f 1 n`.
    simp [apSumOffset_eq_apSum_shift_add]
  · intro B hB n
    -- Transfer uniform bounds by rewriting to `discOffset`.
    simpa [discrepancy, discOffset, apSumOffset_eq_apSum_shift_add] using hB n

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
