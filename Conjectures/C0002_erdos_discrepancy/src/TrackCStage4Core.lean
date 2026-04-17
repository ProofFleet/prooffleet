import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryCore

/-!
# Track C — Stage 4 (core boundary)

Stage 4 is the first place we want to carry a real proof obligation (not just packaging).

Policy:
- This file should stay API + wiring.
- Put any additional derived lemmas / witness-form wrappers in
  `Conjectures.C0002_erdos_discrepancy.src.TrackCStage4Proof`.
- Stage 4 should consume Stage 3 only through the hard-gate core import above.

Current status: Stage-4 boundary API is still lightweight.

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

/-- Stage 4 carries the full Stage-3 output, hence also carries the underlying Stage-2 output.

This projection is useful for later stages that still need Stage-2 witnesses, without forcing them
to re-run earlier stages.
-/
@[simp] abbrev out2 (out : Stage4Output f) : Tao2015.Stage2Output f :=
  out.out3.out2

/-- Stage 4 carries the full Stage-2 output, hence also carries the underlying Stage-1 reduction output.

This projection is occasionally useful for later stages that want access to the deterministic
parameters `g, d, m` and the Stage-1 transport contracts.
-/
@[simp] abbrev out1 (out : Stage4Output f) : Tao2015.ReductionOutput f :=
  out.out3.out2.out1

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

/-- Specialization of `Stage4Output.forall_hasDiscrepancyAtLeast` at a fixed threshold `C`.

This is a tiny convenience lemma, matching the Stage-2/Stage-3 boundary API style.
-/
theorem hasDiscrepancyAtLeast (out : Stage4Output f) (C : ℕ) : HasDiscrepancyAtLeast f C := by
  exact (out.forall_hasDiscrepancyAtLeast (f := f)) C

/-- Stage 4 output retains the Stage-3 fixed-step unboundedness witness for the reduced sequence,
phrased using the verified core predicate `MoltResearch.UnboundedDiscrepancyAlong`.

This is a thin wrapper around `Stage3Output.unboundedDiscrepancyAlong_core`.
-/
theorem unboundedDiscrepancyAlong_core (out : Stage4Output f) :
    MoltResearch.UnboundedDiscrepancyAlong out.out1.g out.out1.d := by
  simpa [Stage4Output.out1] using out.out3.unboundedDiscrepancyAlong_core (f := f)

end Stage4Output

/-- Stage 4 main constructor (stub).

Implementation idea:
- obtain `out3` from `Tao2015.stage3Out` (Stage 3 hard-gate core definition),
- then package any additional structure needed for later stages.

Any nontrivial obligation should live in `TrackCStage4Proof.lean`.
-/
noncomputable def stage4 (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage4Output f :=
  ⟨Tao2015.stage3Out (f := f) (hf := hf)⟩

/-- Deterministic name for the Stage-4 output (useful to keep later statements readable). -/
noncomputable abbrev stage4Out (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage4Output f :=
  stage4 (f := f) (hf := hf)

/-- The Stage-3 output stored inside `stage4Out` is definitionally the Stage-3 output produced by
Stage 3.

This lemma is tiny but useful for rewriting when shuttling statements between Stage 3 and Stage 4.
-/
@[simp] theorem stage4Out_out3 (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage4Out (f := f) (hf := hf)).out3 = Tao2015.stage3Out (f := f) (hf := hf) := by
  rfl

/-- The Stage-2 output stored inside `stage4Out` is definitionally the Stage-2 output produced by
Stage 2.

This lemma is tiny but useful for rewriting when shuttling statements between Stage 2 and Stage 4,
without importing the larger Stage-3 convenience layer.
-/
@[simp] theorem stage4Out_out2 (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage4Out (f := f) (hf := hf)).out2 = stage2Out (f := f) (hf := hf) := by
  rfl

/-- The Stage-1 reduction output stored inside `stage4Out` is definitionally the Stage-1 reduction
output produced by Stage 2.

This lemma is tiny but useful for rewriting when shuttling statements between Stage 1 and Stage 4.
-/
@[simp] theorem stage4Out_out1 (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage4Out (f := f) (hf := hf)).out1 = (stage2Out (f := f) (hf := hf)).out1 := by
  rfl

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

/-- Specialization of `stage4_forall_hasDiscrepancyAtLeast` at a fixed threshold `C`. -/
theorem stage4_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) (C : ℕ) :
    HasDiscrepancyAtLeast f C := by
  exact (stage4_forall_hasDiscrepancyAtLeast (f := f) (hf := hf)) C

/-- Track C pipeline witness: Stage 4 retains the fixed-step unboundedness witness for the reduced
sequence, phrased using the verified core predicate `MoltResearch.UnboundedDiscrepancyAlong`.

This is a tiny wrapper around `Stage4Output.unboundedDiscrepancyAlong_core`, kept in the Stage-4
core boundary so later stages can consume Stage 4 without importing additional proof files.
-/
theorem stage4_unboundedDiscrepancyAlong_core (f : ℕ → ℤ) (hf : IsSignSequence f) :
    MoltResearch.UnboundedDiscrepancyAlong
      (stage4Out (f := f) (hf := hf)).out1.g
      (stage4Out (f := f) (hf := hf)).out1.d := by
  simpa using (stage4Out (f := f) (hf := hf)).unboundedDiscrepancyAlong_core (f := f)

end Tao2015
end MoltResearch
