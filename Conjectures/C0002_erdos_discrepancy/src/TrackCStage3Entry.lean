import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry

/-!
# Track C: Stage 3 entry point (Tao 2015 plane)

This file is **Conjectures-only** glue.

It provides the minimal Stage-3 entry point `stage3`: from a sign sequence `f`, produce a
`Stage3Output f`.

Design goal: keep this module thin, so the hard-gate build for
`Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy` does not need to compile additional
wrapper lemmas. Consumers should prefer the `Stage3Output` record API.
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
-/
noncomputable abbrev stage3_d (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  (stage3Out (f := f) (hf := hf)).out2.out1.d

/-- Convenience projection: the reduced sequence produced by Stage 3. -/
noncomputable abbrev stage3_g (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ → ℤ :=
  (stage3Out (f := f) (hf := hf)).out2.out1.g

/-- Convenience projection: the bundled offset parameter produced by Stage 3. -/
noncomputable abbrev stage3_m (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  (stage3Out (f := f) (hf := hf)).out2.out1.m

end Tao2015

end MoltResearch
