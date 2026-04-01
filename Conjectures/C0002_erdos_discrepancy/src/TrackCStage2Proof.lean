import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2

/-!
# Track C: Stage 2 proof stub (Tao 2015 plane)

This file intentionally contains only the Stage-2 conjecture stub (axiom) plus a tiny handful of
convenience projections.

Everything else should be proved/packaged in `TrackCStage2.lean` (the Stage-2 API surface) as
lemmas about `Stage2Output`, so we avoid a second parallel library of wrapper lemmas here.
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

/-- Convenience projection: the reduced sequence produced by Stage 2. -/
noncomputable abbrev stage2_g (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ → ℤ :=
  (stage2Out (f := f) (hf := hf)).out1.g

/-- Convenience projection: the bundled offset parameter produced by Stage 2. -/
noncomputable abbrev stage2_m (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  (stage2Out (f := f) (hf := hf)).out1.m

/-- The reduced sequence produced by Stage 2 is a sign sequence. -/
theorem stage2_hg (f : ℕ → ℤ) (hf : IsSignSequence f) :
    IsSignSequence (stage2_g (f := f) (hf := hf)) := by
  simpa [stage2Out, stage2_g] using (stage2Out (f := f) (hf := hf)).out1.hg

/-- Rewrite for the reduced sequence produced by Stage 2: it is a shift by `m*d`. -/
theorem stage2_g_eq (f : ℕ → ℤ) (hf : IsSignSequence f) (k : ℕ) :
    stage2_g (f := f) (hf := hf) k =
      f (k + (stage2_m (f := f) (hf := hf)) * (stage2_d (f := f) (hf := hf))) := by
  simpa [stage2Out, stage2_g, stage2_m, stage2_d] using
    (stage2Out (f := f) (hf := hf)).out1.g_eq k

/-- Positivity of the reduced step size produced by Stage 2. -/
theorem stage2_hd (f : ℕ → ℤ) (hf : IsSignSequence f) : stage2_d (f := f) (hf := hf) > 0 := by
  simpa [stage2Out, stage2_d] using (stage2Out (f := f) (hf := hf)).out1.hd

/-- Consumer-facing shortcut: Stage 2 already yields the global conclusion `¬ BoundedDiscrepancy f`. -/
theorem stage2_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  simpa [stage2Out] using
    (Stage2Output.notBoundedOriginal (f := f) (stage2Out (f := f) (hf := hf)))

/-- Stage 2 yields the usual surface statement `∀ C, HasDiscrepancyAtLeast f C`. -/
theorem stage2_forall_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  simpa [stage2Out] using
    (Stage2Output.forall_hasDiscrepancyAtLeast (f := f) (stage2Out (f := f) (hf := hf)))

/-- Stage 2 yields the pipeline-friendly nucleus witness form.

`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.
-/
theorem stage2_forall_exists_d_ge_one_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  simpa [stage2Out] using
    (Stage2Output.forall_exists_d_ge_one_witness_pos (f := f) (stage2Out (f := f) (hf := hf)))

/-- Stage 2 yields explicit affine-tail nucleus witnesses at the concrete parameters produced by Stage 1.

Normal form:
`∀ C, ∃ n, Int.natAbs (apSumFrom f (m*d) d n) > C`,
where `d = stage2_d` and `m = stage2_m`.
-/
theorem stage2_forall_exists_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ n : ℕ,
      Int.natAbs
          (apSumFrom f ((stage2_m (f := f) (hf := hf)) * (stage2_d (f := f) (hf := hf)))
            (stage2_d (f := f) (hf := hf)) n) > C := by
  simpa [stage2Out, stage2_m, stage2_d] using
    (Stage2Output.forall_exists_natAbs_apSumFrom_mul_gt (f := f) (stage2Out (f := f) (hf := hf)))

end Tao2015

end MoltResearch
