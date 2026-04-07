import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Boundary
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Core

/-!
# Track C: Stage 2 entry point (Tao 2015 plane)

This file is **Conjectures-only** glue.

It contains only the Stage-2 conjecture stub (axiom) plus the deterministic name `stage2Out`.

Design goal: keep the Track-C hard-gate build (which imports Stage 3) from compiling the larger
collection of Stage-2 wrapper lemmas in `TrackCStage2Proof.lean`.
-/

namespace MoltResearch

namespace Tao2015

/-- **Conjecture stub:** Stage 2 of Tao 2015.

Given a sign sequence `f`, produce a Stage-1 reduction output and show that the reduced sequence
has unbounded discrepancy along its associated fixed step.
-/
axiom stage2 (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage2Output f

/-- Deterministic name for the Stage-2 output (useful to keep later statements readable). -/
noncomputable abbrev stage2Out (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage2Output f :=
  stage2 (f := f) (hf := hf)

/-- Convenience projection: the reduced step size produced by Stage 2.

We define these projections in the entry-point module so consumers can access them without importing
additional wrapper-lemma modules.
-/
noncomputable abbrev stage2_d (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  (stage2Out (f := f) (hf := hf)).out1.d

/-- Convenience lemma: the reduced step size produced by Stage 2 is positive. -/
theorem stage2_d_pos (f : ℕ → ℤ) (hf : IsSignSequence f) : stage2_d (f := f) (hf := hf) > 0 := by
  simpa [stage2_d] using (stage2Out (f := f) (hf := hf)).out1.hd

/-- Convenience projection: the reduced sequence produced by Stage 2. -/
noncomputable abbrev stage2_g (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ → ℤ :=
  (stage2Out (f := f) (hf := hf)).out1.g

/-- Convenience projection: the bundled offset parameter produced by Stage 2. -/
noncomputable abbrev stage2_m (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  (stage2Out (f := f) (hf := hf)).out1.m

/-- Minimal consumer-facing Stage-2 consequence: the original sequence cannot have globally bounded
(discrepancy) once Stage 2 produces an unbounded fixed-step witness along the reduced sequence.

This lemma lives in the entry-point module so consumers who only need the boundedness-negation
normal form can avoid importing the larger Stage-2 wrapper lemma files.
-/
theorem stage2_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  simpa using
    (Stage2Output.notBoundedOriginal (f := f) (out := stage2Out (f := f) (hf := hf)))

/-- Minimal consumer-facing Stage-2 consequence: Stage 2 yields an unbounded bundled offset
  discrepancy family `discOffset f d m` at the deterministic parameters produced by `stage2Out`.

This lemma lives in the entry-point module so consumers can access this key transport consequence
without importing the larger Stage-2 wrapper lemma files.
-/
theorem stage2_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    UnboundedDiscOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) := by
  simpa [stage2_d, stage2_m, Stage2Output.d, Stage2Output.m] using
    (Stage2Output.unboundedDiscOffset (f := f) (out := stage2Out (f := f) (hf := hf)))

end Tao2015

end MoltResearch
