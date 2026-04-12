import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryCore

/-!
# Track C — Stage 4 (stub)

Stage 4 is the first place we want to carry a real proof obligation (not just packaging).

Policy:
- This file should stay API + wiring.
- Put any substantial arguments in `TrackCStage4Proof.lean`.
- Stage 4 should consume Stage 3 only through the hard-gate core import above.

Current status: stub interface.

Design tweak (2026-04): Stage 4 output now *carries* the Stage-3 output record.
This keeps traceability (and access to Stage-2 witnesses) without forcing Stage 4 consumers to
re-run earlier stages.
-/

namespace MoltResearch
namespace Tao2015

/-- Stage 4 output (interface stub).

We keep this abstract for now: Stage 4 will eventually package whatever additional structure
(or additional witnesses) the next Tao2015 step requires.

For now, it records the full Stage-3 output.
-/
structure Stage4Output (f : ℕ → ℤ) : Type where
  /-- The Stage-3 output, carried forward as the input to Stage 4. -/
  out3 : Tao2015.Stage3Output f

namespace Stage4Output

variable {f : ℕ → ℤ}

/-- Stage 4 output already carries the Stage-3 conclusion `¬ BoundedDiscrepancy f`. -/
theorem notBounded (out : Stage4Output f) : ¬ BoundedDiscrepancy f :=
  out.out3.notBounded

/-- Stage 4 output implies the usual surface statement `∀ C, HasDiscrepancyAtLeast f C`.

This is the same corollary used in `ErdosDiscrepancy.lean`, but exposed at the Stage-4 boundary so
later stages can consume Stage 4 without re-proving it.
-/
theorem forall_hasDiscrepancyAtLeast (out : Stage4Output f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  -- Reuse the Stage-3 surface lemma rather than unfolding any definitions.
  exact out.out3.forall_hasDiscrepancyAtLeast (f := f)

end Stage4Output

/-- Stage 4 main constructor (stub).

Implementation idea:
- obtain `out3` from `Tao2015.stage3Out` (Stage 3 hard-gate core definition),
- then package any additional structure needed for later stages.

The real obligation will live in `TrackCStage4Proof.lean`.
-/
noncomputable def stage4 (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage4Output f :=
  ⟨Tao2015.stage3Out (f := f) (hf := hf)⟩

/-- Deterministic name for the Stage-4 output (useful to keep later statements readable). -/
noncomputable abbrev stage4Out (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage4Output f :=
  stage4 (f := f) (hf := hf)

/-- Consumer-facing shortcut: Stage 4 closes the core goal `¬ BoundedDiscrepancy f`. -/
theorem stage4_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  exact (stage4Out (f := f) (hf := hf)).notBounded

/-- Consumer-facing shortcut: Stage 4 yields the usual surface statement
`∀ C, HasDiscrepancyAtLeast f C`.

This is a thin wrapper around `Stage4Output.forall_hasDiscrepancyAtLeast`.
-/
theorem stage4_forall_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  exact (stage4Out (f := f) (hf := hf)).forall_hasDiscrepancyAtLeast

end Tao2015
end MoltResearch
