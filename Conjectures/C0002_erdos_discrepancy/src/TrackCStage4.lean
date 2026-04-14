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

/-- Stage 4 carries the full Stage-3 output, hence also carries the underlying Stage-2 output.

This projection is useful for later stages that still need Stage-2 witnesses, without forcing them
to re-run earlier stages.
-/
abbrev out2 (out : Stage4Output f) : Tao2015.Stage2Output f :=
  out.out3.out2

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

/-- Stage 4 output implies the nucleus witness form

`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is the most pipeline-friendly surface statement: it avoids `discrepancy` and goes straight to
the nucleus `apSum`.
-/
theorem forall_exists_d_ge_one_witness_pos (out : Stage4Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_d_ge_one_witness_pos f).1
      (out.forall_hasDiscrepancyAtLeast (f := f))

/-- Variant of `forall_exists_d_ge_one_witness_pos` with the step-size condition written as
`d > 0`.

This is sometimes a more convenient normal form when downstream stages naturally assume `d ≠ 0`
(or use lemmas phrased with strict positivity).
-/
theorem forall_exists_d_pos_witness_pos (out : Stage4Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  intro C
  rcases out.forall_exists_d_ge_one_witness_pos (f := f) C with ⟨d, n, hd, hn, hw⟩
  refine ⟨d, n, ?_, hn, hw⟩
  exact lt_of_lt_of_le Nat.zero_lt_one hd

/-- Stage 4 output implies the explicit discrepancy witness normal form

`∀ C, ∃ d n, d > 0 ∧ discrepancy f d n > C`.

This is a thin wrapper around `forall_hasDiscrepancyAtLeast` via
`HasDiscrepancyAtLeast_iff_exists_discrepancy`.
-/
theorem forall_exists_discrepancy_gt (out : Stage4Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ discrepancy f d n > C := by
  intro C
  exact
    (HasDiscrepancyAtLeast_iff_exists_discrepancy (f := f) (C := C)).1
      (out.forall_hasDiscrepancyAtLeast (f := f) C)

/-- Strengthened witness form of `forall_exists_discrepancy_gt` with a positive-length witness.

This is sometimes convenient when downstream stages want to rule out the degenerate case `n = 0`.
-/
theorem forall_exists_discrepancy_gt_witness_pos (out : Stage4Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ discrepancy f d n > C := by
  intro C
  rcases out.forall_exists_d_pos_witness_pos (f := f) C with ⟨d, n, hd, hn, hw⟩
  refine ⟨d, n, hd, hn, ?_⟩
  -- `discrepancy f d n` is definitionally `Int.natAbs (apSum f d n)`.
  change Int.natAbs (apSum f d n) > C
  exact hw

/-- Stage 4 output implies the paper-notation witness form

`∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ Int.natAbs (∑ i ∈ Icc 1 n, f (i*d)) > C`.

This is a thin wrapper around `forall_hasDiscrepancyAtLeast` via
`forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos`.
-/
theorem forall_exists_sum_Icc_witness_pos (out : Stage4Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧
      Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos f).1
      (out.forall_hasDiscrepancyAtLeast (f := f))

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
  -- Expand `stage4Out` to its Stage-3 payload, then use the Stage-3 definitional rewrite.
  simpa [Stage4Output.out2] using (stage3Out_out2 (f := f) (hf := hf))

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

/-- Consumer-facing shortcut: Stage 4 yields the nucleus witness form

`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is the most pipeline-friendly surface statement for consuming Stage 4.
-/
theorem stage4_forall_exists_d_ge_one_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact (stage4Out (f := f) (hf := hf)).forall_exists_d_ge_one_witness_pos (f := f)

/-- Consumer-facing shortcut: Stage 4 yields the nucleus witness form with strict positivity for
`d`.

Normal form:
`∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.
-/
theorem stage4_forall_exists_d_pos_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact (stage4Out (f := f) (hf := hf)).forall_exists_d_pos_witness_pos (f := f)

/-- Consumer-facing shortcut: Stage 4 yields explicit discrepancy witnesses

`∀ C, ∃ d n, d > 0 ∧ discrepancy f d n > C`.

This is the witness-form normal form of `stage4_forall_hasDiscrepancyAtLeast`.
-/
theorem stage4_forall_exists_discrepancy_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ discrepancy f d n > C := by
  exact (stage4Out (f := f) (hf := hf)).forall_exists_discrepancy_gt (f := f)

/-- Strengthened witness form of `stage4_forall_exists_discrepancy_gt` with a positive-length witness.

This is sometimes convenient when downstream stages want to rule out the degenerate case `n = 0`.
-/
theorem stage4_forall_exists_discrepancy_gt_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ discrepancy f d n > C := by
  exact (stage4Out (f := f) (hf := hf)).forall_exists_discrepancy_gt_witness_pos (f := f)

/-- Consumer-facing shortcut: Stage 4 yields the paper-notation witness form

`∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ Int.natAbs (∑ i ∈ Icc 1 n, f (i*d)) > C`.

This is a thin wrapper around `Stage4Output.forall_exists_sum_Icc_witness_pos`.
-/
theorem stage4_forall_exists_sum_Icc_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧
      Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  exact (stage4Out (f := f) (hf := hf)).forall_exists_sum_Icc_witness_pos (f := f)

end Tao2015
end MoltResearch
