import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Boundary

/-!
# Track C: Stage 2 entry point (Tao 2015 plane)

This file is **Conjectures-only** glue.

It contains only:
- the Stage-2 conjecture stub (axiom) `stage2`,
- the deterministic name `stage2Out`,
- the lightweight projections `stage2_d`, `stage2_g`, `stage2_m`, `stage2_start`, and
- the tiny projection lemmas `stage2_d_pos`, `stage2_one_le_d`, `stage2_d_ne_zero`, `stage2_hg`,
  `stage2_g_eq`, `stage2_g_eq_fun`.

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

/-- The affine-tail start index `stage2_start` is a multiple of the reduced step size `stage2_d`. -/
theorem stage2_d_dvd_start (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage2_d (f := f) (hf := hf) ∣ stage2_start (f := f) (hf := hf) := by
  refine ⟨stage2_m (f := f) (hf := hf), ?_⟩
  -- `stage2_start = m*d`, so this is just commutativity.
  simpa [stage2_start] using
    (Nat.mul_comm (stage2_m (f := f) (hf := hf)) (stage2_d (f := f) (hf := hf)))

/-- The affine-tail start index `stage2_start` has remainder `0` when reduced modulo `stage2_d`.

This is often the most convenient form of `stage2_d_dvd_start` for arithmetic rewriting.
-/
theorem stage2_start_mod_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage2_start (f := f) (hf := hf) % stage2_d (f := f) (hf := hf) = 0 := by
  exact Nat.mod_eq_zero_of_dvd (stage2_d_dvd_start (f := f) (hf := hf))

/-- The reduced sequence produced by Stage 2 is a sign sequence. -/
theorem stage2_hg (f : ℕ → ℤ) (hf : IsSignSequence f) :
    IsSignSequence (stage2_g (f := f) (hf := hf)) := by
  simpa [stage2_g] using (stage2Out (f := f) (hf := hf)).out1.hg

/-- Rewrite for the reduced sequence produced by Stage 2: it is a shift by `m*d`. -/
theorem stage2_g_eq (f : ℕ → ℤ) (hf : IsSignSequence f) (k : ℕ) :
    stage2_g (f := f) (hf := hf) k = f (k + stage2_start (f := f) (hf := hf)) := by
  -- This is just the Stage-1 reduction contract carried by the Stage-2 output.
  simpa [stage2_g, stage2_start, stage2_m, stage2_d] using
    (stage2Out (f := f) (hf := hf)).out1.g_eq k

/-- Function-level rewrite for `stage2_g`: it is the shifted sequence `fun k => f (k + m*d)`. -/
theorem stage2_g_eq_fun (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage2_g (f := f) (hf := hf) =
      fun k => f (k + stage2_start (f := f) (hf := hf)) := by
  funext k
  simpa using stage2_g_eq (f := f) (hf := hf) k

end Tao2015

end MoltResearch
