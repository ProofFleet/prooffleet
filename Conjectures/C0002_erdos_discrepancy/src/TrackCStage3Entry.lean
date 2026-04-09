import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryCore
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Core

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

/-- Convenience projection: the affine-tail start index `m*d` bundled in Stage 1 and produced by
Stage 3.

This is intentionally not in the hard-gate core: it is a convenience name used by a few later
lemmas, but it is not needed to state the main theorem.
-/
noncomputable abbrev stage3_start (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  stage3_m (f := f) (hf := hf) * stage3_d (f := f) (hf := hf)

/-- Rewrite for the reduced sequence produced by Stage 3: it is a shift by the deterministic
affine-tail start index `stage3_start = m*d`.
-/
theorem stage3_g_eq_start (f : ℕ → ℤ) (hf : IsSignSequence f) (k : ℕ) :
    stage3_g (f := f) (hf := hf) k = f (k + stage3_start (f := f) (hf := hf)) := by
  -- Stage 3 is just Stage-2 glue, so this is the Stage-2 `g_eq_start` rewrite.
  simpa [stage3_g, stage3_start, stage3_m, stage3_d, stage2_g, stage2_m, stage2_d,
    Stage2Output.start] using
    (Stage2Output.g_eq_start (f := f) (out := stage2Out (f := f) (hf := hf)) k)

/-- Consumer-facing shortcut: Stage 3 yields the nucleus witness form

`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is a thin wrapper around the proved Stage-2 core lemma
`Stage2Output.forall_exists_d_ge_one_witness_pos`.
-/
theorem stage3_forall_exists_d_ge_one_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  -- Stage 3 is just glue on top of Stage 2, so route through the Stage-2 core lemma.
  exact
    Stage2Output.forall_exists_d_ge_one_witness_pos (f := f) (stage2Out (f := f) (hf := hf))

/-- Consumer-facing shortcut: Stage 3 yields the nucleus witness form with strict positivity
for the step size:

`∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is a thin wrapper around the proved Stage-2 core lemma
`Stage2Output.forall_exists_d_pos_witness_pos`.
-/
theorem stage3_forall_exists_d_pos_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  -- Stage 3 is just glue on top of Stage 2, so route through the Stage-2 core lemma.
  exact Stage2Output.forall_exists_d_pos_witness_pos (f := f) (stage2Out (f := f) (hf := hf))

/-- Consumer-facing shortcut: Stage 3 yields the nucleus witness form with the step-size condition
written as `d ≠ 0`:

`∀ C, ∃ d n, d ≠ 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is a thin wrapper around the proved Stage-2 core lemma
`Stage2Output.forall_exists_d_ne_zero_witness_pos`.
-/
theorem stage3_forall_exists_d_ne_zero_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≠ 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  -- Stage 3 is just glue on top of Stage 2, so route through the Stage-2 core lemma.
  exact
    Stage2Output.forall_exists_d_ne_zero_witness_pos (f := f) (stage2Out (f := f) (hf := hf))

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

/-- Existential packaging: Stage 3 yields concrete parameters `d, m` with `1 ≤ d` such that the
bundled offset discrepancy family `discOffset f d m` is unbounded.

This is a minimal corollary of `stage3_unboundedDiscOffset` that many downstream consumers prefer
when they only need the existence of some unbounded offset family.
-/
theorem stage3_exists_params_one_le_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ UnboundedDiscOffset f d m := by
  refine ⟨stage3_d (f := f) (hf := hf), stage3_m (f := f) (hf := hf), ?_, ?_⟩
  · -- The Stage-3 projections route through the Stage-2 output.
    simpa [stage3_d, stage2_d, Stage2Output.d] using
      (Stage2Output.one_le_d (f := f) (stage2Out (f := f) (hf := hf)))
  · exact stage3_unboundedDiscOffset (f := f) (hf := hf)

end Tao2015

end MoltResearch
