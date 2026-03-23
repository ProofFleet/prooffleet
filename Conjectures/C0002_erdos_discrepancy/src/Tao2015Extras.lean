import Conjectures.C0002_erdos_discrepancy.src.Tao2015

/-!
# Tao 2015 (Track C): small interface extras

This module is **Conjectures-only**: it may contain `sorry`, but the intent here is to add tiny
helper lemmas that make the stage interfaces easier to consume.

Nothing in this file should edit or depend on implementation details under `MoltResearch/`.
-/

namespace MoltResearch

namespace Tao2015

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
  have h : discrepancy out.g out.d n ≤ ctx.B := ctx.bound_discrepancy (f := out.g) (d := out.d) n
  simpa [out.discrepancy_eq_discOffset_via_contract (f := f) (n := n)] using h

/-- Nucleus-level variant of `bound_discOffset_of_contextAlong`.

This version expands `discOffset` into `Int.natAbs (apSumOffset ...)`.
-/
theorem bound_natAbs_apSumOffset_of_contextAlong (out : ReductionOutput f) (ctx : ContextAlong out.g out.d) :
    ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ ctx.B := by
  intro n
  -- `discOffset` is definitionally `natAbs (apSumOffset ...)`.
  simpa [discOffset] using (bound_discOffset_of_contextAlong (f := f) out ctx n)

/-- Build a fixed-step discrepancy context for the reduced sequence from a global boundedness context.

This is the most common consumer pattern for Stage 1:
- from `BoundedDiscrepancy f` build `ctx : Tao2015.Context f`,
- then recover a uniform bound on the reduced discrepancy `discrepancy out.g out.d`.

We use the packaged bound `ctx.bound_discOffset_two_mul` together with the Stage-1 transport
contract `out.contract_discrepancy_le`.
-/
theorem contextAlong_of_context (out : ReductionOutput f) (ctx : Tao2015.Context f) :
    ContextAlong out.g out.d := by
  refine ⟨2 * ctx.B, ?_⟩
  intro n
  have hOffset : ∀ n : ℕ, discOffset f out.d out.m n ≤ 2 * ctx.B := by
    intro n
    simpa using
      (ctx.bound_discOffset_two_mul (f := f) (d := out.d) (m := out.m) (n := n) out.hd)
  exact out.contract_discrepancy_le (B := 2 * ctx.B) hOffset n

end ReductionOutput

end Tao2015

end MoltResearch
