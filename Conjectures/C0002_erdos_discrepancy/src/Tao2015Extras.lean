import Conjectures.C0002_erdos_discrepancy.src.Tao2015

/-!
# Tao 2015 (Track C): small interface extras

This module is **Conjectures-only**: it may contain axiom stubs (and, if needed, `sorry`), but the intent here is to add tiny
helper lemmas that make the stage interfaces easier to consume.

Nothing in this file should edit or depend on implementation details under `MoltResearch/`.
-/

namespace MoltResearch

namespace Tao2015

/-!
## Small nucleus normal forms

These are tiny rewrite lemmas that show up repeatedly when consuming the stage interfaces.
They live in this Conjectures-only file to avoid growing the verified substrate.
-/

/-- Normal form: the affine-tail nucleus at start `m*d` is the bundled offset nucleus. -/
theorem apSumFrom_mul_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSumFrom f (m * d) d n = apSumOffset f d m n := by
  simpa using
    (apSumFrom_tail_eq_apSumOffset_shift_add (f := f) (a := 0) (d := d) (m := m) (n := n))

/-- Normal form: offset discrepancy expressed directly using the affine-tail nucleus.

This avoids having to expand `discOffset` into `apSumOffset` and then rewrite to an `apSumFrom` tail
form by hand.
-/
theorem discOffset_eq_natAbs_apSumFrom_mul (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset f d m n = Int.natAbs (apSumFrom f (m * d) d n) := by
  unfold discOffset
  -- Apply `Int.natAbs` to the `apSumFrom`→`apSumOffset` normal form, then flip the equality.
  exact
    (congrArg Int.natAbs
        (apSumFrom_mul_eq_apSumOffset (f := f) (d := d) (m := m) (n := n))).symm

/-- Normal form: unbounded offset discrepancy expressed directly using the affine-tail nucleus.

This is a small helper for later analytic stages: it avoids repeatedly unfolding `discOffset` and
rewriting `apSumOffset` to `apSumFrom` tails.
-/
theorem unboundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ) (d m : ℕ) :
    UnboundedDiscOffset f d m ↔
      (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumFrom f (m * d) d n)) := by
  constructor
  · intro hunb B
    rcases hunb B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [discOffset_eq_natAbs_apSumFrom_mul (f := f) (d := d) (m := m) (n := n)] using hn
  · intro h B
    rcases h B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [discOffset_eq_natAbs_apSumFrom_mul (f := f) (d := d) (m := m) (n := n)] using hn

namespace ReductionOutput

variable {f : ℕ → ℤ}

/-!
## Transfer helpers: from reduced fixed-step contexts back to bundled offset families

Stage 1 (`ReductionOutput`) packages a *reduced* sign sequence `out.g` along a fixed step `out.d`.
Many downstream stages maintain a `ContextAlong out.g out.d` (uniform bound on `discrepancy` along
that step).

These tiny lemmas let such a reduced context immediately yield bounds on the *bundled offset*
family `discOffset f out.d out.m`, without having to manually rewrite each time.
-/

/-- A fixed-step discrepancy context for the reduced sequence bounds the bundled offset discrepancies.

This is just `ctx.bound` transported via the stage-1 rewrite
`discrepancy out.g out.d n = discOffset f out.d out.m n`.
-/
theorem bound_discOffset_of_contextAlong (out : ReductionOutput f) (ctx : ContextAlong out.g out.d) :
    ∀ n : ℕ, discOffset f out.d out.m n ≤ ctx.B := by
  intro n
  have h : discrepancy out.g out.d n ≤ ctx.B := ctx.bound_discrepancy n
  simpa [out.discrepancy_eq_discOffset_via_contract (f := f) (n := n)] using h

/-- Nucleus-level variant of `bound_discOffset_of_contextAlong`.

This version expands `discOffset` into `Int.natAbs (apSumOffset ...)`.
-/
theorem bound_natAbs_apSumOffset_of_contextAlong (out : ReductionOutput f) (ctx : ContextAlong out.g out.d) :
    ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ ctx.B := by
  intro n
  -- `discOffset` is definitionally `natAbs (apSumOffset ...)`.
  have h : discOffset f out.d out.m n ≤ ctx.B := bound_discOffset_of_contextAlong (f := f) out ctx n
  unfold discOffset at h
  exact h

/-- Tail-nucleus variant of `bound_natAbs_apSumOffset_of_contextAlong`.

This exposes the affine-tail nucleus `apSumFrom f (m*d) d n` rather than the bundled wrapper
`apSumOffset f d m n`.
-/
theorem bound_natAbs_apSumFrom_mul_of_contextAlong (out : ReductionOutput f)
    (ctx : ContextAlong out.g out.d) :
    ∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) ≤ ctx.B := by
  intro n
  have hOffset : Int.natAbs (apSumOffset f out.d out.m n) ≤ ctx.B :=
    bound_natAbs_apSumOffset_of_contextAlong (f := f) out ctx n
  simpa [apSumFrom_mul_eq_apSumOffset (f := f) (d := out.d) (m := out.m) (n := n)] using hOffset

/-- Build a fixed-step discrepancy context for the reduced sequence from a global boundedness context.

This is the most common consumer pattern for Stage 1:
- from `BoundedDiscrepancy f` build `ctx : Tao2015.Context f`,
- then recover a uniform bound on the reduced discrepancy `discrepancy out.g out.d`.

We use the packaged bound `ctx.bound_discOffset_two_mul` together with the Stage-1 transport
contract `out.contract_discrepancy_le`.
-/
def contextAlong_of_context (out : ReductionOutput f) (ctx : Tao2015.Context f) :
    ContextAlong out.g out.d := by
  refine ⟨2 * ctx.B, ?_⟩
  intro n
  have hOffset : ∀ n : ℕ, discOffset f out.d out.m n ≤ 2 * ctx.B := by
    intro n
    simpa using
      (ctx.bound_discOffset_two_mul (f := f) (d := out.d) (m := out.m) (n := n) out.hd)
  exact out.contract_discrepancy_le (B := 2 * ctx.B) hOffset n

/-- If `f` has globally bounded discrepancy, then the reduced sequence `out.g` has bounded
fixed-step discrepancy along `out.d`.

This is a convenience wrapper around `contextAlong_of_context`: it builds a `Context` from
`BoundedDiscrepancy f`, then unwraps the resulting `ContextAlong` into the Prop-style predicate
`BoundedDiscrepancyAlong`.
-/
theorem boundedDiscrepancyAlong_of_boundedDiscrepancy (out : ReductionOutput f)
    (hb : BoundedDiscrepancy f) :
    BoundedDiscrepancyAlong out.g out.d := by
  classical
  let ctx : Tao2015.Context f := Tao2015.Context.ofBoundedDiscrepancy (f := f) hb
  let ctxAlong : ContextAlong out.g out.d := contextAlong_of_context (f := f) out ctx
  exact ⟨ctxAlong.B, ctxAlong.bound_discrepancy⟩

end ReductionOutput

end Tao2015

end MoltResearch
