import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Boundary

/-!
# Track C: Stage 2 entry point (Tao 2015 plane)

This file is **Conjectures-only** glue.

It contains only:
- the Stage-2 conjecture stub (axiom) `stage2`,
- the deterministic name `stage2Out`,
- the lightweight projections `stage2_d`, `stage2_g`, `stage2_m`, `stage2_start`, and
- the tiny projection lemmas `stage2_d_pos`, `stage2_one_le_d`, `stage2_d_ne_zero`.

All other proved convenience lemmas about `stage2Out` live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Proof`.

Design goal: keep the Track-C hard-gate build (which imports Stage 3) from compiling additional
wrapper lemmas when it only needs the Stage-2 stub.
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

/-- Convenience projection: the reduced step size produced by Stage 2. -/
noncomputable abbrev stage2_d (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  (stage2Out (f := f) (hf := hf)).out1.d

/-- Convenience projection lemma: the reduced step size produced by Stage 2 is positive.

We keep this in the entry-point module because most consumers need the side condition `d > 0`,
and it is a zero-cost projection from the Stage-1 reduction output bundled in `stage2Out`.
-/
theorem stage2_d_pos (f : ℕ → ℤ) (hf : IsSignSequence f) : stage2_d (f := f) (hf := hf) > 0 := by
  simpa [stage2_d] using (stage2Out (f := f) (hf := hf)).out1.hd

/-- Convenience lemma: the reduced step size produced by Stage 2 is at least `1`. -/
theorem stage2_one_le_d (f : ℕ → ℤ) (hf : IsSignSequence f) : 1 ≤ stage2_d (f := f) (hf := hf) := by
  exact Nat.succ_le_of_lt (stage2_d_pos (f := f) (hf := hf))

/-- Convenience lemma: the reduced step size produced by Stage 2 is nonzero. -/
theorem stage2_d_ne_zero (f : ℕ → ℤ) (hf : IsSignSequence f) : stage2_d (f := f) (hf := hf) ≠ 0 := by
  exact Nat.ne_of_gt (stage2_d_pos (f := f) (hf := hf))

/-- Convenience projection: the reduced sequence produced by Stage 2. -/
noncomputable abbrev stage2_g (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ → ℤ :=
  (stage2Out (f := f) (hf := hf)).out1.g

/-- Convenience projection: the bundled offset parameter produced by Stage 2. -/
noncomputable abbrev stage2_m (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  (stage2Out (f := f) (hf := hf)).out1.m

/-- Convenience projection: the affine-tail start index `m*d` bundled in Stage 1 and produced by
Stage 2.

We define this in the entry-point module so hard-gate consumers can use it without importing any
additional wrapper-lemma modules.
-/
noncomputable abbrev stage2_start (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  stage2_m (f := f) (hf := hf) * stage2_d (f := f) (hf := hf)

end Tao2015

end MoltResearch
