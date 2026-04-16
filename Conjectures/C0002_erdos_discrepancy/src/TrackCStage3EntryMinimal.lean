import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Stub

/-!
# Track C: Stage 3 entry point (hard-gate minimal)

This file is **Conjectures-only** glue.

It provides the minimal Stage-3 entry point API needed by the Track-C hard-gate target
`Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy`:

- `stage3` / `stage3Out` : produce a `Stage3Output f` from a sign sequence `f`
- `stage3_notBounded` : close the core goal `¬ BoundedDiscrepancy f`
- `stage3_forall_hasDiscrepancyAtLeast` : the usual surface statement
  `∀ C, HasDiscrepancyAtLeast f C`
- `stage3_hasDiscrepancyAtLeast` : specialization at a fixed threshold `C`

All additional witness-form corollaries live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryCore`.
-/

namespace MoltResearch

namespace Tao2015

/-- Conjectures-only Stage 3 entry point: run Stage 2, then close the global goal via the proved
Stage-3 boundary lemma `Stage3Output.ofStage2Output`.

This is a definition (not an axiom): Stage 3 is non-stub glue on top of the Stage-2 axiom.
-/
noncomputable def stage3 (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage3Output f :=
  Stage3Output.ofStage2Output (f := f) (stage2Out (f := f) (hf := hf))

/-- Deterministic name for the Stage-3 output (useful to keep later statements readable). -/
noncomputable abbrev stage3Out (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage3Output f :=
  stage3 (f := f) (hf := hf)

/-- The Stage-2 output stored inside `stage3Out` is definitionally the Stage-2 output produced by
Stage 2.

This lemma is tiny but useful for rewriting when shuttling statements between Stage 2 and Stage 3.

We keep it in the hard-gate minimal module so `ErdosDiscrepancy.lean` can stay minimal.
-/
@[simp] theorem stage3Out_out2 (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).out2 = stage2Out (f := f) (hf := hf) := by
  rfl

/-- The Stage-1 reduction output stored inside `stage3Out` is definitionally the Stage-1 reduction
output produced by Stage 2.

This lemma is tiny but useful for rewriting when shuttling statements between Stage 1 and Stage 3.

We keep it in the hard-gate minimal module so `ErdosDiscrepancy.lean` can stay minimal.
-/
@[simp] theorem stage3Out_out1 (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).out2.out1 = (stage2Out (f := f) (hf := hf)).out1 := by
  rfl

/-- The Stage-1 reduction output stored inside `stage3Out` can also be accessed through the
convenience projection `Stage3Output.out1`.

This lemma is a tiny wrapper around `stage3Out_out1`.
-/
@[simp] theorem stage3Out_out1' (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).out1 = (stage2Out (f := f) (hf := hf)).out1 := by
  rfl

/-- Track C pipeline witness: Stage 3 yields unbounded fixed-step discrepancy along the reduced
sequence, expressed using the verified core predicate `MoltResearch.UnboundedDiscrepancyAlong`.

This lemma is a small convenience wrapper around the bridge equivalence
`Tao2015.unboundedDiscrepancyAlong_iff_core`.
-/
theorem stage3_unboundedDiscrepancyAlong_core (f : ℕ → ℤ) (hf : IsSignSequence f) :
    MoltResearch.UnboundedDiscrepancyAlong
      (stage3Out (f := f) (hf := hf)).out1.g
      (stage3Out (f := f) (hf := hf)).out1.d := by
  have hunb :
      Tao2015.UnboundedDiscrepancyAlong
        (stage3Out (f := f) (hf := hf)).out1.g
        (stage3Out (f := f) (hf := hf)).out1.d :=
    (stage3Out (f := f) (hf := hf)).out2.unbounded
  exact
    (Tao2015.unboundedDiscrepancyAlong_iff_core
          (g := (stage3Out (f := f) (hf := hf)).out1.g)
          (d := (stage3Out (f := f) (hf := hf)).out1.d)).1
      hunb

/-- Consumer-facing shortcut: the Stage-3 pipeline closes the core goal `¬ BoundedDiscrepancy f`.

We keep this lemma in the hard-gate minimal module so `ErdosDiscrepancy.lean` can remain minimal.
-/
theorem stage3_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  exact (stage3Out (f := f) (hf := hf)).notBounded

/-- Consumer-facing shortcut: the Stage-3 pipeline yields the usual surface statement
`∀ C, HasDiscrepancyAtLeast f C`.

This is a thin wrapper around `Stage3Output.forall_hasDiscrepancyAtLeast`.
-/
theorem stage3_forall_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  exact Stage3Output.forall_hasDiscrepancyAtLeast (f := f) (stage3Out (f := f) (hf := hf))

/-- Specialization of `stage3_forall_hasDiscrepancyAtLeast` at a fixed threshold `C`.

This is a tiny convenience lemma: it avoids an extra application at the call site.
-/
theorem stage3_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) (C : ℕ) :
    HasDiscrepancyAtLeast f C := by
  exact (stage3_forall_hasDiscrepancyAtLeast (f := f) (hf := hf)) C

end Tao2015

end MoltResearch
