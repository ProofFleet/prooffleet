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

Implementation note: Stage 3 is just glue on top of Stage 2, so we route these projections through
the Stage-2 entry-point projections (`stage2_d`, `stage2_g`, `stage2_m`).
-/
noncomputable abbrev stage3_d (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  stage2_d (f := f) (hf := hf)

/-- Convenience lemma: the reduced step size produced by Stage 3 is positive. -/
theorem stage3_d_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage3_d (f := f) (hf := hf) > 0 := by
  simpa [stage3_d] using stage2_d_pos (f := f) (hf := hf)

/-- Convenience lemma: the reduced step size produced by Stage 3 is at least `1`. -/
theorem stage3_one_le_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    1 ≤ stage3_d (f := f) (hf := hf) := by
  simpa [stage3_d] using stage2_one_le_d (f := f) (hf := hf)

/-- Convenience lemma: the reduced step size produced by Stage 3 is nonzero. -/
theorem stage3_d_ne_zero (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage3_d (f := f) (hf := hf) ≠ 0 := by
  simpa [stage3_d] using stage2_d_ne_zero (f := f) (hf := hf)

/-- Convenience projection: the reduced sequence produced by Stage 3. -/
noncomputable abbrev stage3_g (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ → ℤ :=
  stage2_g (f := f) (hf := hf)

/-- The reduced sequence produced by Stage 3 is a sign sequence. -/
theorem stage3_hg (f : ℕ → ℤ) (hf : IsSignSequence f) :
    IsSignSequence (stage3_g (f := f) (hf := hf)) := by
  -- Stage 3 is glue on top of the Stage-2 conjecture stub.
  simpa [stage3_g, stage2_g] using (stage2Out (f := f) (hf := hf)).hg

/-- Convenience projection: the bundled offset parameter produced by Stage 3. -/
noncomputable abbrev stage3_m (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  stage2_m (f := f) (hf := hf)

/-- Consumer-facing shortcut: the Stage-3 pipeline closes the core goal `¬ BoundedDiscrepancy f`.

We provide this lemma in the entry-point module so hard-gate consumers can access it without
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

/-- Consumer-facing shortcut: Stage 3 yields the paper-notation witness form

`∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ |∑ i ∈ Icc 1 n, f (i*d)| > C`.

This is a thin wrapper around `stage3_forall_hasDiscrepancyAtLeast` via
`forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos`.
-/
theorem stage3_forall_exists_sum_Icc_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧
      Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos f).1
      (stage3_forall_hasDiscrepancyAtLeast (f := f) (hf := hf))

/-- Consumer-facing shortcut: Stage 3 yields an unbounded bundled offset discrepancy family
`discOffset f d m` at the deterministic parameters `d = stage3_d` and `m = stage3_m`.

This mirrors `stage2_unboundedDiscOffset`, but is phrased at the Stage-3 boundary so consumers who
import only `TrackCStage3Entry` can obtain the Stage-1 transport consequence without reaching into
nested record fields.
-/
theorem stage3_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    UnboundedDiscOffset f (stage3_d (f := f) (hf := hf)) (stage3_m (f := f) (hf := hf)) := by
  simpa [stage3_d, stage3_m] using stage2_unboundedDiscOffset (f := f) (hf := hf)

/-- Positive-length witness form of `stage3_unboundedDiscOffset`.

The witness length `n` cannot be `0`, since `discOffset ... 0 = 0`.
-/
theorem stage3_forall_exists_discOffset_gt'_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ,
        n > 0 ∧
          discOffset f (stage3_d (f := f) (hf := hf)) (stage3_m (f := f) (hf := hf)) n > B := by
  have hunb :
      UnboundedDiscOffset f (stage3_d (f := f) (hf := hf)) (stage3_m (f := f) (hf := hf)) :=
    stage3_unboundedDiscOffset (f := f) (hf := hf)
  simpa using
    (UnboundedDiscOffset.forall_exists_discOffset_gt'_witness_pos (f := f)
      (d := stage3_d (f := f) (hf := hf)) (m := stage3_m (f := f) (hf := hf)) hunb)

end Tao2015

end MoltResearch
