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

end ReductionOutput

end Tao2015

end MoltResearch
