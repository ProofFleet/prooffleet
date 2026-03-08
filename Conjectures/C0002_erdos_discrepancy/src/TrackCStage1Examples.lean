import Conjectures.C0002_erdos_discrepancy.src.Tao2015

/-!
# Track C examples: Stage 1 (`Tao2015.ReductionOutput`)

This file is **Conjectures-only** glue: small example lemmas showing how to *consume*
`Tao2015.ReductionOutput` as an IO contract.

Nothing here is intended to be part of the verified substrate (`MoltResearch/`).
-/

namespace MoltResearch

namespace Tao2015

namespace Stage1Examples

variable {f : ℕ → ℤ}

/-- Example: bounded global discrepancy implies a uniform bound on any fixed offset discrepancy.

This is a tiny “how to use `Tao2015.Context`” lemma: once you turn
`hb : BoundedDiscrepancy f` into a `Context f`, the rest is a one-liner.
-/
theorem exists_forall_discOffset_le_of_boundedDiscrepancy (hb : BoundedDiscrepancy f)
    (d m : ℕ) (hd : d > 0) :
    ∃ B : ℕ, ∀ n : ℕ, discOffset f d m n ≤ B := by
  classical
  let ctx : Tao2015.Context f := Tao2015.Context.ofBoundedDiscrepancy (f := f) hb
  refine ⟨2 * ctx.B, ?_⟩
  intro n
  simpa using (ctx.bound_discOffset_two_mul (f := f) (d := d) (m := m) (n := n) hd)

/-- Example: bounded global discrepancy transfers to bounded fixed-step discrepancy
for the reduced sequence coming from `ReductionOutput.ofShift`.

This is the canonical Stage-1 consumption pattern:
1. turn `BoundedDiscrepancy f` into a uniform `discOffset` bound (cost: factor `2`), then
2. apply the `ReductionOutput` discrepancy-transfer contract.
-/
theorem boundedDiscrepancyAlong_ofShift_of_boundedDiscrepancy
    (hf : IsSignSequence f) (hb : BoundedDiscrepancy f) (d m : ℕ) (hd : d > 0) :
    BoundedDiscrepancyAlong (ReductionOutput.ofShift f hf d m hd).g d := by
  -- Extract a uniform offset bound from global boundedness.
  rcases
      (exists_forall_discOffset_le_of_boundedDiscrepancy (f := f) hb (d := d) (m := m) hd)
    with ⟨B, hB⟩
  -- Apply the reduction output's transfer contract.
  refine ⟨B, ?_⟩
  intro n
  -- `BoundedDiscrepancyAlong` is stated in terms of `discrepancy`.
  exact (ReductionOutput.ofShift f hf d m hd).contract_discrepancy_le B hB n

/-- Example: consume a fixed-step discrepancy witness for the reduced sequence produced by
`ReductionOutput.ofShift`, and extract an explicit affine-tail witness for the *original* sequence.

Concretely, a witness
`HasDiscrepancyAtLeastAlong out.g d C`
becomes a witness
`∃ n, |apSumFrom f (m*d) d n| > C`.
-/
theorem exists_natAbs_apSumFrom_mul_gt_of_hasDiscrepancyAtLeastAlong_ofShift
    (hf : IsSignSequence f) (d m C : ℕ) (hd : d > 0)
    (h : HasDiscrepancyAtLeastAlong (ReductionOutput.ofShift f hf d m hd).g d C) :
    ∃ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) > C := by
  -- This is exactly the consumer-facing lemma on `ReductionOutput`.
  simpa using
    ((ReductionOutput.ofShift f hf d m hd).hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_mul_gt
      (f := f) (C := C)).1 h

end Stage1Examples

end Tao2015

end MoltResearch
