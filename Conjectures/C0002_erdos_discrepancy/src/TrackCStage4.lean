import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryCore

/-!
# Track C — Stage 4 (stub)

Stage 4 is the first place we want to carry a *real proof obligation* (not just packaging).

Policy:
- This file should stay API + wiring.
- Put any substantial arguments in `TrackCStage4Proof.lean`.
- Stage 4 should consume Stage 3 only through the **hard-gate core** import above.

Current status: stub interface.
-/

namespace MoltResearch
namespace Tao2015

/-- Stage 4 output (interface stub).

We keep this abstract for now: Stage 4 will eventually package whatever additional structure
(or additional witnesses) the next Tao2015 step requires.

For now, it only records that the Stage-3 core conclusion is available.
-/
structure Stage4Output (f : ℕ → ℤ) : Type where
  /-- The Stage-3 core conclusion, carried forward as the input to Stage 4. -/
  stage3_notBounded : ¬ BoundedDiscrepancy f

/-- Stage 4 main constructor (stub).

Implementation idea:
- obtain `stage3_notBounded` from `Tao2015.stage3_notBounded` (Stage 3 hard-gate core theorem),
- then package any additional structure needed for later stages.

The *real obligation* will live in `TrackCStage4Proof.lean`.
-/
noncomputable def stage4 (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage4Output f := by
  refine ⟨?_,⟩
  simpa using (Tao2015.stage3_notBounded (f := f) (hf := hf))

end Tao2015
end MoltResearch
