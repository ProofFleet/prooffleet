import MoltResearch.Discrepancy.Multiplicative
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Core

/-!
# Track C: verified Stage-2 constructors for the completely multiplicative subclass

This file is **Conjectures-only** wiring, but everything in it is **proved** (no axioms): it
turns the verified multiplicative reduction (`MoltResearch/Discrepancy/Multiplicative.lean`)
into concrete `Stage2Output` constructors.

The point: the Stage-2 conjecture stub assumes, for *every* sign sequence, the existence of
parameters `d, m` with unbounded offset discrepancy. For a **completely multiplicative** sign
sequence that assumption collapses to a single reduced hypothesis — unbounded plain partial
sums — and this file packages that collapse as constructors:

- `Stage2Output.ofUnboundedDiscrepancyOne` — any sign sequence with unbounded step-one
  discrepancy yields a Stage-2 output at the deterministic parameters `d = 1`, `m = 0`
  (legitimately: here the `d = 1` witness is *hypothesized*, not asserted axiomatically).
- `Stage2Output.ofCompletelyMultiplicative` — for a completely multiplicative sign sequence,
  the EDP surface statement itself yields a Stage-2 output, via the verified equivalence
  `forall_hasDiscrepancyAtLeast_iff_unboundedDiscrepancy_one`.

Once a future Fourier-reduction stage produces completely multiplicative counterexample
candidates, these constructors are the (already verified) bridge into the Stage 2/3/4 pipeline.
-/

namespace MoltResearch

namespace Tao2015

variable {f : ℕ → ℤ}

/-- Bridge normal form: unbounded step-one discrepancy is exactly unbounded offset discrepancy
at the deterministic parameters `d = 1`, `m = 0`. -/
theorem unboundedDiscOffset_one_zero_of_unboundedDiscrepancy_one
    (h : UnboundedDiscrepancy f 1) : UnboundedDiscOffset f 1 0 := by
  intro B
  rcases h B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [discOffset_zero_start, disc_eq_discrepancy]
  exact hn

/-- Converse bridge, for API symmetry. -/
theorem unboundedDiscrepancy_one_of_unboundedDiscOffset_one_zero
    (h : UnboundedDiscOffset f 1 0) : UnboundedDiscrepancy f 1 := by
  intro B
  rcases h B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [← disc_eq_discrepancy, ← discOffset_zero_start (f := f) (d := 1) (n := n)]
  exact hn

/-- **Verified Stage-2 constructor** (no axioms): a sign sequence with unbounded step-one
discrepancy yields a full Stage-2 output, wired through the identity Stage-1 reduction
(`ReductionOutput.ofShift` at `d = 1`, `m = 0`).

This is the shape the Stage-2 conjecture stub *should* eventually be discharged through on the
completely multiplicative subclass.
-/
noncomputable def Stage2Output.ofUnboundedDiscrepancyOne (hf : IsSignSequence f)
    (h1 : UnboundedDiscrepancy f 1) : Stage2Output f :=
  Stage2Output.ofUnboundedDiscOffset (f := f)
    (ReductionOutput.ofShift (f := f) (hf := hf) (d := 1) (m := 0) (hd := Nat.one_pos))
    (by
      simpa [ReductionOutput.ofShift] using
        (unboundedDiscOffset_one_zero_of_unboundedDiscrepancy_one (f := f) h1))

/-- **Verified Stage-2 constructor for the completely multiplicative subclass** (no axioms):
for a completely multiplicative sign sequence, the EDP surface statement
`∀ C, HasDiscrepancyAtLeast f C` yields a full Stage-2 output.

This composes the verified multiplicative reduction
(`CompletelyMultiplicative.forall_hasDiscrepancyAtLeast_iff_unboundedDiscrepancy_one`) with
`Stage2Output.ofUnboundedDiscrepancyOne`.
-/
noncomputable def Stage2Output.ofCompletelyMultiplicative (hmul : CompletelyMultiplicative f)
    (hf : IsSignSequence f) (h : ∀ C : ℕ, HasDiscrepancyAtLeast f C) : Stage2Output f :=
  Stage2Output.ofUnboundedDiscrepancyOne (f := f) hf
    ((hmul.forall_hasDiscrepancyAtLeast_iff_unboundedDiscrepancy_one hf).1 h)

/-!
## Consumer regression examples (compile-only)

Stage-3-policy style: each constructor comes with a short consumer example showing the
downstream call-site it unlocks, using named boundary lemmas only.
-/

-- A hypothesized step-one witness flows through the whole Stage-2 boundary API.
example (hf : IsSignSequence f) (h1 : UnboundedDiscrepancy f 1) :
    ¬ BoundedDiscrepancy f :=
  (Stage2Output.ofUnboundedDiscrepancyOne (f := f) hf h1).notBoundedOriginal

-- For completely multiplicative sign sequences, the constructors close the loop with the
-- verified reduction: EDP in, Stage-2 output out, EDP back — no axioms anywhere on this path.
example (hmul : CompletelyMultiplicative f) (hf : IsSignSequence f)
    (h : ∀ C : ℕ, HasDiscrepancyAtLeast f C) :
    ¬ BoundedDiscrepancy f :=
  (Stage2Output.ofCompletelyMultiplicative (f := f) hmul hf h).notBoundedOriginal

end Tao2015

end MoltResearch
