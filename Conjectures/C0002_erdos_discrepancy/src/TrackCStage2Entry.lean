import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Boundary

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
  -- Name the Stage-2 output once, to avoid duplicating the `stage2Out` term.
  set out := stage2Out (f := f) (hf := hf) with hout
  exact
    out.out1.not_boundedDiscrepancy_of_unboundedDiscrepancyAlong (f := f)
      (by simpa [hout] using out.unbounded)

end Tao2015

end MoltResearch
