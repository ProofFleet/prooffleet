import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryCore
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Output

/-!
# Track C: Stage 3 entry point (Tao 2015 plane)

This file is **Conjectures-only** glue.

- `TrackCStage3EntryCore.lean` contains the minimal Stage-3 API needed by the Track-C hard-gate
  target `Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy`.
- This file keeps additional Stage-3 convenience wrappers available under the traditional import
  `...TrackCStage3Entry` without forcing the hard-gate target to compile them.

Additional convenience lemmas and witness-form wrappers also live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3Proof`.
-/

namespace MoltResearch

namespace Tao2015

-- (core API lives in `TrackCStage3EntryCore.lean`)

-- Note: `stage3_g_eq_fun` now lives in `TrackCStage3EntryCore.lean` so hard-gate consumers
-- can use it without importing this larger convenience-lemma module.

/-- Consumer-facing shortcut: Stage 3 yields the nucleus witness form

`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is a thin wrapper around the proved Stage-2 lemma
`Stage2Output.forall_exists_d_ge_one_witness_pos`.
-/
theorem stage3_forall_exists_d_ge_one_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  -- Stage 3 is just glue on top of Stage 2, so route through the Stage-2 lemma.
  exact
    Stage2Output.forall_exists_d_ge_one_witness_pos (f := f) (stage2Out (f := f) (hf := hf))

/-- Consumer-facing shortcut: Stage 3 yields the nucleus witness form with strict positivity
for the step size:

`∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is a thin wrapper around the proved Stage-2 lemma
`Stage2Output.forall_exists_d_pos_witness_pos`.
-/
theorem stage3_forall_exists_d_pos_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  -- Stage 3 is just glue on top of Stage 2, so route through the Stage-2 lemma.
  exact Stage2Output.forall_exists_d_pos_witness_pos (f := f) (stage2Out (f := f) (hf := hf))

/-- Consumer-facing shortcut: Stage 3 yields the nucleus witness form with the step-size condition
written as `d ≠ 0`:

`∀ C, ∃ d n, d ≠ 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is a thin wrapper around the proved Stage-2 lemma
`Stage2Output.forall_exists_d_ne_zero_witness_pos`.
-/
theorem stage3_forall_exists_d_ne_zero_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≠ 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  -- Stage 3 is just glue on top of Stage 2, so route through the Stage-2 lemma.
  exact
    Stage2Output.forall_exists_d_ne_zero_witness_pos (f := f) (stage2Out (f := f) (hf := hf))

/-- Consumer-facing shortcut: Stage 3 yields the discrepancy witness form

`∀ C, ∃ d n, d > 0 ∧ discrepancy f d n > C`.

This is a thin wrapper around the proved Stage-2 lemma
`Stage2Output.forall_exists_discrepancy_gt_original`.
-/
theorem stage3_forall_exists_discrepancy_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ discrepancy f d n > C := by
  exact
    Stage2Output.forall_exists_discrepancy_gt_original (f := f) (stage2Out (f := f) (hf := hf))

/-- Consumer-facing shortcut: Stage 3 yields unboundedness of the bundled offset discrepancy family
`discOffset f d m` at the deterministic parameters produced by the pipeline.

We keep this lemma in the `...TrackCStage3Entry` import path (rather than in the proof-heavy
wrapper module) so consumers can access the offset witness without importing
`TrackCStage3Proof`.
-/
theorem stage3_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    UnboundedDiscOffset f (stage3_d (f := f) (hf := hf)) (stage3_m (f := f) (hf := hf)) := by
  -- Route through the proved Stage-2 core lemma (a thin wrapper around the Stage-1 transport
  -- contract).
  simpa [stage3_d, stage3_m, stage2_d, stage2_m] using
    (Stage2Output.unboundedDiscOffset (f := f) (stage2Out (f := f) (hf := hf)))

/-- Witness-family form of `stage3_unboundedDiscOffset` (inequality-direction), with a positive-length
witness.

Normal form:
`∀ B, ∃ n, n > 0 ∧ discOffset f (stage3_d ...) (stage3_m ...) n > B`.

This is a thin wrapper around the proved Stage-2 lemma
`Stage2Output.forall_exists_discOffset_gt'_witness_pos`.
-/
theorem stage3_forall_exists_discOffset_gt'_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ,
        n > 0 ∧
          discOffset f (stage3_d (f := f) (hf := hf)) (stage3_m (f := f) (hf := hf)) n > B := by
  simpa [stage3_d, stage3_m, stage2_d, stage2_m] using
    (Stage2Output.forall_exists_discOffset_gt'_witness_pos (f := f) (stage2Out (f := f) (hf := hf)))

/-- Existential packaging: Stage 3 yields concrete parameters `d, m` with `d > 0` such that the
bundled offset discrepancy family `discOffset f d m` is unbounded.

This is a minimal corollary of `stage3_unboundedDiscOffset` for consumers that prefer strict
positivity over `1 ≤ d`.
-/
theorem stage3_exists_params_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ UnboundedDiscOffset f d m := by
  refine ⟨stage3_d (f := f) (hf := hf), stage3_m (f := f) (hf := hf), ?_, ?_⟩
  · exact stage3_d_pos (f := f) (hf := hf)
  · exact stage3_unboundedDiscOffset (f := f) (hf := hf)

/-- Existential packaging: Stage 3 yields concrete parameters `d, m` with `1 ≤ d` such that the
bundled offset discrepancy family `discOffset f d m` is unbounded.

This is a minimal corollary of `stage3_unboundedDiscOffset` that many downstream consumers prefer
when they only need the existence of some unbounded offset family.
-/
theorem stage3_exists_params_one_le_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ UnboundedDiscOffset f d m := by
  refine ⟨stage3_d (f := f) (hf := hf), stage3_m (f := f) (hf := hf), ?_, ?_⟩
  · exact stage3_one_le_d (f := f) (hf := hf)
  · exact stage3_unboundedDiscOffset (f := f) (hf := hf)

end Tao2015

end MoltResearch
