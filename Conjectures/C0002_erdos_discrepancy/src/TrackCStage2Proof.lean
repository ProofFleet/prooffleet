import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Output
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry

/-!
# Track C: Stage 2 proof stub (Tao 2015 plane)

This file contains only the Stage-2 convenience projections/wrapper lemmas.

The Stage-2 conjecture stub (axiom) itself lives in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry`.

Everything else should be proved/packaged in `TrackCStage2.lean` (the Stage-2 API surface) as
lemmas about `Stage2Output`, so we avoid a second parallel library of wrapper lemmas here.

Implementation note: this stub imports `TrackCStage2Output` directly (rather than the Stage-2
wiring module `TrackCStage2.lean`) to keep the dependency direction one-way and avoid accidental
import cycles as the pipeline grows.
-/

namespace MoltResearch

namespace Tao2015

/-!
The Stage-2 conjecture stub (axiom) and the deterministic name `stage2Out` live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry`.

This file keeps only the convenience projections/wrapper lemmas.
-/

/-- Convenience projection: the reduced step size produced by Stage 2. -/
noncomputable abbrev stage2_d (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  (stage2Out (f := f) (hf := hf)).d

/-- Convenience projection: the reduced sequence produced by Stage 2. -/
noncomputable abbrev stage2_g (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ → ℤ :=
  (stage2Out (f := f) (hf := hf)).g

/-- Convenience projection: the bundled offset parameter produced by Stage 2. -/
noncomputable abbrev stage2_m (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  (stage2Out (f := f) (hf := hf)).m

/-- The reduced sequence produced by Stage 2 is a sign sequence. -/
theorem stage2_hg (f : ℕ → ℤ) (hf : IsSignSequence f) :
    IsSignSequence (stage2_g (f := f) (hf := hf)) := by
  -- Use only the Stage-2 boundary API, not the internal Stage-1 fields.
  simpa [stage2Out, stage2_g] using
    (Stage2Output.hg (f := f) (stage2Out (f := f) (hf := hf)))

/-- Rewrite for the reduced sequence produced by Stage 2: it is a shift by `m*d`. -/
theorem stage2_g_eq (f : ℕ → ℤ) (hf : IsSignSequence f) (k : ℕ) :
    stage2_g (f := f) (hf := hf) k =
      f (k + (stage2_m (f := f) (hf := hf)) * (stage2_d (f := f) (hf := hf))) := by
  -- Prefer the Stage-2 boundary lemma to avoid exposing Stage-1 internals.
  simpa [stage2Out, stage2_g, stage2_m, stage2_d] using
    (Stage2Output.g_eq (f := f) (stage2Out (f := f) (hf := hf)) k)

/-- Positivity of the reduced step size produced by Stage 2. -/
theorem stage2_hd (f : ℕ → ℤ) (hf : IsSignSequence f) : stage2_d (f := f) (hf := hf) > 0 := by
  -- Prefer the Stage-2 boundary API lemma.
  simpa [stage2Out, stage2_d] using
    (Stage2Output.hd (f := f) (stage2Out (f := f) (hf := hf)))

/-- Convenience lemma: the reduced step size produced by Stage 2 is at least `1`. -/
theorem stage2_one_le_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    1 ≤ stage2_d (f := f) (hf := hf) := by
  -- Delegate to the Stage-2 boundary API lemma.
  simpa [stage2Out, stage2_d] using
    (Stage2Output.one_le_d (f := f) (stage2Out (f := f) (hf := hf)))

/-- Convenience lemma: the reduced step size produced by Stage 2 is nonzero. -/
theorem stage2_d_ne_zero (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage2_d (f := f) (hf := hf) ≠ 0 := by
  -- Delegate to the Stage-2 boundary API lemma.
  simpa [stage2Out, stage2_d] using
    (Stage2Output.d_ne_zero (f := f) (stage2Out (f := f) (hf := hf)))

/-- Consumer-facing shortcut: Stage 2 already closes the core goal `¬ BoundedDiscrepancy f`.

This is a thin wrapper around the proved Stage-2 boundary lemma
`Stage2Output.notBoundedOriginal`.
-/
theorem stage2_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  exact Stage2Output.notBoundedOriginal (f := f) (stage2Out (f := f) (hf := hf))

/-- Consumer-facing shortcut: Stage 2 yields the usual surface statement
`∀ C, HasDiscrepancyAtLeast f C`.

This is a thin wrapper around the proved Stage-2 boundary lemma
`Stage2Output.forall_hasDiscrepancyAtLeast`.
-/
theorem stage2_forall_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  exact Stage2Output.forall_hasDiscrepancyAtLeast (f := f) (stage2Out (f := f) (hf := hf))

/-!
Consumer code should use `stage2Out` together with the general lemmas about `Stage2Output` in
`TrackCStage2.lean` (for example: `Stage2Output.forall_hasDiscrepancyAtLeast`,
`Stage2Output.forall_exists_d_ge_one_witness_pos`).

We intentionally avoid duplicating wrappers here (beyond the single core-goal shortcut above), so
this file remains a pure conjecture stub plus projections.
-/

end Tao2015

end MoltResearch
