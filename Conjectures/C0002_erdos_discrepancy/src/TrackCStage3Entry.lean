import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Core

/-!
# Track C: Stage 3 entry point (Tao 2015 plane)

This file is **Conjectures-only** glue.

It provides the minimal Stage-3 entry point `stage3`: from a sign sequence `f`, produce a
`Stage3Output f`.

Design goal: keep this module thin, so the hard-gate build for
`Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy` does not need to compile additional
wrapper lemmas.

Additional convenience lemmas and witness-form wrappers live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3Proof`.
-/

namespace MoltResearch

namespace Tao2015

/-- Conjectures-only Stage 3 entry point: run Stage 2, then close the global goal via the proved
Stage-3 boundary lemma `Stage3Output.ofStage2Output`.

This is a definition (not an axiom): Stage 3 is non-stub glue on top of the Stage-2 axiom.
-/
noncomputable def stage3 (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage3Output f := by
  exact Stage3Output.ofStage2Output (f := f) (stage2Out (f := f) (hf := hf))

/-- Deterministic name for the Stage-3 output (useful to keep later statements readable). -/
noncomputable abbrev stage3Out (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage3Output f :=
  stage3 (f := f) (hf := hf)

/-- Convenience projection: the reduced step size produced by Stage 3.

We define this in the entry-point module (not in the wrapper-lemma module) so hard-gate consumers
can access it without importing additional convenience lemmas.

Implementation note: Stage 3 is just glue on top of Stage 2, so we route these projections through
the Stage-2 entry-point projections (`stage2_d`, `stage2_g`, `stage2_m`).
-/
noncomputable abbrev stage3_d (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  stage2_d (f := f) (hf := hf)

/-- Convenience projection: the reduced sequence produced by Stage 3. -/
noncomputable abbrev stage3_g (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ → ℤ :=
  stage2_g (f := f) (hf := hf)

/-- Convenience projection: the bundled offset parameter produced by Stage 3. -/
noncomputable abbrev stage3_m (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  stage2_m (f := f) (hf := hf)

/-- Convenience projection: the affine-tail start index `m*d` bundled in Stage 1 and produced by
Stage 3.

We define this in the entry-point module so hard-gate consumers can use it without importing any
additional wrapper-lemma modules.
-/
noncomputable abbrev stage3_start (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  stage3_m (f := f) (hf := hf) * stage3_d (f := f) (hf := hf)

/-- Consumer-facing shortcut: the Stage-3 pipeline closes the core goal `¬ BoundedDiscrepancy f`.

We keep this lemma in the entry-point module so hard-gate consumers can access it without
importing additional wrapper-lemma modules.
-/
theorem stage3_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  -- Prefer consuming the Stage-3 output record API.
  exact (stage3Out (f := f) (hf := hf)).notBounded

/-- Consumer-facing shortcut: the Stage-3 pipeline yields the usual surface statement
`∀ C, HasDiscrepancyAtLeast f C`.

This is a thin wrapper around `Stage3Output.forall_hasDiscrepancyAtLeast`.
-/
theorem stage3_forall_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  simpa using
    (Stage3Output.forall_hasDiscrepancyAtLeast (f := f) (stage3Out (f := f) (hf := hf)))

/-- Consumer-facing shortcut: Stage 3 yields unboundedness of the bundled offset discrepancy family
`discOffset f d m` at the deterministic parameters produced by the pipeline.

We keep this lemma in the entry-point module so hard-gate consumers can access the offset witness
without importing the larger wrapper-lemma module `TrackCStage3Proof`.
-/
theorem stage3_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    UnboundedDiscOffset f (stage3_d (f := f) (hf := hf)) (stage3_m (f := f) (hf := hf)) := by
  -- Route through the proved Stage-2 core lemma (a thin wrapper around the Stage-1 transport
  -- contract).
  simpa [stage3_d, stage3_m, stage2_d, stage2_m] using
    (Stage2Output.unboundedDiscOffset (f := f) (stage2Out (f := f) (hf := hf)))

end Tao2015

end MoltResearch
