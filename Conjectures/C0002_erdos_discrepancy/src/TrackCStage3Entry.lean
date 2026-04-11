import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryCore

/-!
# Track C: Stage 3 entry point (Tao 2015 plane)

This file is **Conjectures-only** glue.

- `TrackCStage3EntryCore.lean` contains the minimal Stage-3 API needed by the Track-C hard-gate
  target `Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy`.
- This file keeps additional Stage-3 convenience wrappers available under the traditional import
  `...TrackCStage3Entry` without forcing the hard-gate target to compile them.

Design note: this module is intentionally lightweight. Most witness-form corollaries can be
obtained from the hard-gate lemma `stage3_forall_hasDiscrepancyAtLeast` together with global
normal-form equivalences, so we avoid importing the larger Stage-2 convenience-lemma library.

Additional convenience lemmas and witness-form wrappers also live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3Proof`.
-/

namespace MoltResearch

namespace Tao2015

/-!
## Basic Stage-3 projections and rewrites

These are just re-exports of the Stage-2 deterministic projections, since Stage 3 is definitional
glue on top of the Stage-2 output.

We keep them out of `TrackCStage3EntryCore.lean` to minimize the hard-gate compilation surface.
-/

/-- The Stage-2 output stored inside `stage3Out` is definitionally the Stage-2 output produced by
Stage 2.

This lemma is tiny but useful for rewriting when shuttling statements between Stage 2 and Stage 3.
-/
theorem stage3Out_out2 (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).out2 = stage2Out (f := f) (hf := hf) := by
  rfl

/-- Convenience projection: the reduced step size produced by Stage 3. -/
noncomputable abbrev stage3_d (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  stage2_d (f := f) (hf := hf)

/-- Convenience lemma: the reduced step size produced by Stage 3 is positive. -/
theorem stage3_d_pos (f : ℕ → ℤ) (hf : IsSignSequence f) : stage3_d (f := f) (hf := hf) > 0 := by
  simpa [stage3_d] using stage2_d_pos (f := f) (hf := hf)

/-- Convenience lemma: the reduced step size produced by Stage 3 is at least `1`. -/
theorem stage3_one_le_d (f : ℕ → ℤ) (hf : IsSignSequence f) : 1 ≤ stage3_d (f := f) (hf := hf) := by
  simpa [stage3_d] using stage2_one_le_d (f := f) (hf := hf)

/-- Convenience lemma: the reduced step size produced by Stage 3 is nonzero. -/
theorem stage3_d_ne_zero (f : ℕ → ℤ) (hf : IsSignSequence f) : stage3_d (f := f) (hf := hf) ≠ 0 := by
  simpa [stage3_d] using stage2_d_ne_zero (f := f) (hf := hf)

/-- Convenience projection: the reduced sequence produced by Stage 3. -/
noncomputable abbrev stage3_g (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ → ℤ :=
  stage2_g (f := f) (hf := hf)

/-- Convenience projection: the bundled offset parameter produced by Stage 3. -/
noncomputable abbrev stage3_m (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  stage2_m (f := f) (hf := hf)

/-- Convenience projection: the affine-tail start index `m*d` produced by Stage 3.

This is the shift used to define the reduced sequence `stage3_g` as a tail of `f`.
-/
noncomputable abbrev stage3_start (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  stage2_start (f := f) (hf := hf)

/-- Definitional rewrite: the Stage-3 start index is `m*d` for the deterministic parameters
produced by Stage 3.

This lemma is intentionally tiny (and not a simp lemma): it exists mainly to reduce `dsimp` noise
in downstream arithmetic rewrites.
-/
theorem stage3_start_eq_m_mul_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage3_start (f := f) (hf := hf) =
      stage3_m (f := f) (hf := hf) * stage3_d (f := f) (hf := hf) := by
  rfl

/-- The affine-tail start index `stage3_start` is a multiple of the reduced step size `stage3_d`. -/
theorem stage3_d_dvd_start (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage3_d (f := f) (hf := hf) ∣ stage3_start (f := f) (hf := hf) := by
  simpa [stage3_d, stage3_start] using stage2_d_dvd_start (f := f) (hf := hf)

/-- The affine-tail start index `stage3_start` has remainder `0` when reduced modulo `stage3_d`.

This is often the most convenient form of `stage3_d_dvd_start` for arithmetic rewriting.
-/
theorem stage3_start_mod_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage3_start (f := f) (hf := hf) % stage3_d (f := f) (hf := hf) = 0 := by
  simpa [stage3_d, stage3_start] using stage2_start_mod_d (f := f) (hf := hf)

/-- The reduced sequence produced by Stage 3 is a sign sequence. -/
theorem stage3_hg (f : ℕ → ℤ) (hf : IsSignSequence f) :
    IsSignSequence (stage3_g (f := f) (hf := hf)) := by
  simpa [stage3_g] using stage2_hg (f := f) (hf := hf)

/-- Rewrite for the reduced sequence produced by Stage 3: it is a shift by `m*d`. -/
theorem stage3_g_eq (f : ℕ → ℤ) (hf : IsSignSequence f) (k : ℕ) :
    stage3_g (f := f) (hf := hf) k = f (k + stage3_start (f := f) (hf := hf)) := by
  simpa [stage3_g, stage3_start] using stage2_g_eq (f := f) (hf := hf) k

/-- Function-level rewrite for `stage3_g`: it is the shifted sequence
`fun k => f (k + stage3_start)`.
-/
theorem stage3_g_eq_fun (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage3_g (f := f) (hf := hf) =
      fun k => f (k + stage3_start (f := f) (hf := hf)) := by
  funext k
  simpa using stage3_g_eq (f := f) (hf := hf) k

/-!
## Witness-form corollaries

These are intentionally kept out of the hard-gate core module.
-/

/-- Consumer-facing shortcut: Stage 3 yields the nucleus witness form

`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is a thin wrapper around the hard-gate lemma `stage3_forall_hasDiscrepancyAtLeast` via the
global normal form lemma `forall_hasDiscrepancyAtLeast_iff_forall_exists_d_ge_one_witness_pos`.
-/
theorem stage3_forall_exists_d_ge_one_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_d_ge_one_witness_pos f).1
      (stage3_forall_hasDiscrepancyAtLeast (f := f) (hf := hf))

/-- Variant of `stage3_forall_exists_d_ge_one_witness_pos` with strict positivity for the step size.

Normal form:
`∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.
-/
theorem stage3_forall_exists_d_pos_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  intro C
  rcases stage3_forall_exists_d_ge_one_witness_pos (f := f) (hf := hf) C with
    ⟨d, n, hd, hn, hw⟩
  refine ⟨d, n, ?_, hn, hw⟩
  exact lt_of_lt_of_le Nat.zero_lt_one hd

/-- Variant of `stage3_forall_exists_d_pos_witness_pos` with the step-size condition written as
`d ≠ 0`.
-/
theorem stage3_forall_exists_d_ne_zero_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≠ 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  intro C
  rcases stage3_forall_exists_d_pos_witness_pos (f := f) (hf := hf) C with
    ⟨d, n, hd, hn, hw⟩
  exact ⟨d, n, Nat.ne_of_gt hd, hn, hw⟩

/-- Consumer-facing shortcut: Stage 3 yields the discrepancy witness form

`∀ C, ∃ d n, d > 0 ∧ discrepancy f d n > C`.

This is obtained from `stage3_forall_hasDiscrepancyAtLeast` via
`HasDiscrepancyAtLeast_iff_exists_discrepancy`.
-/
theorem stage3_forall_exists_discrepancy_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ discrepancy f d n > C := by
  intro C
  exact
    (HasDiscrepancyAtLeast_iff_exists_discrepancy (f := f) (C := C)).1
      ((stage3_forall_hasDiscrepancyAtLeast (f := f) (hf := hf)) C)

/-- Positive-length witness variant of `stage3_forall_exists_discrepancy_gt`.

Since `discrepancy f d 0 = 0`, any witness with `discrepancy f d n > C` can be taken with `n > 0`.

We prove this by routing through the nucleus witness form
`stage3_forall_exists_d_pos_witness_pos`.
-/
theorem stage3_forall_exists_discrepancy_gt_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ discrepancy f d n > C := by
  intro C
  rcases stage3_forall_exists_d_pos_witness_pos (f := f) (hf := hf) C with ⟨d, n, hd, hn, hw⟩
  refine ⟨d, n, hd, hn, ?_⟩
  -- `discrepancy f d n` is definitionally `Int.natAbs (apSum f d n)`.
  change Int.natAbs (apSum f d n) > C
  exact hw

/-- Consumer-facing shortcut: Stage 3 yields unboundedness of the bundled offset discrepancy family
`discOffset f d m` at the deterministic parameters produced by the pipeline.

We keep this lemma in the `...TrackCStage3Entry` import path so consumers can access the offset
witness without importing `TrackCStage3Proof`.
-/
theorem stage3_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    UnboundedDiscOffset f (stage3_d (f := f) (hf := hf)) (stage3_m (f := f) (hf := hf)) := by
  -- Route through the proved Stage-2 core lemma (a thin wrapper around the Stage-1 transport
  -- contract).
  simpa [stage3_d, stage3_m, stage2_d, stage2_m] using
    (Stage2Output.unboundedDiscOffset (f := f) (stage2Out (f := f) (hf := hf)))

/-- Witness-family form of `stage3_unboundedDiscOffset` (inequality-direction), with a positive-length
witness.

Normal form:
`∀ B, ∃ n, n > 0 ∧ discOffset f (stage3_d ...) (stage3_m ...) n > B`.

This is a thin wrapper around the generic normal-form lemma
`UnboundedDiscOffset.forall_exists_discOffset_gt'_witness_pos`.
-/
theorem stage3_forall_exists_discOffset_gt'_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ,
        n > 0 ∧
          discOffset f (stage3_d (f := f) (hf := hf)) (stage3_m (f := f) (hf := hf)) n > B := by
  have hunb :
      UnboundedDiscOffset f (stage3_d (f := f) (hf := hf)) (stage3_m (f := f) (hf := hf)) :=
    stage3_unboundedDiscOffset (f := f) (hf := hf)
  exact
    UnboundedDiscOffset.forall_exists_discOffset_gt'_witness_pos (f := f)
      (d := stage3_d (f := f) (hf := hf)) (m := stage3_m (f := f) (hf := hf)) hunb

/-- Existential packaging: Stage 3 yields concrete parameters `d, m` with `d > 0` such that the
bundled offset discrepancy family `discOffset f d m` is unbounded.

This is a minimal corollary of `stage3_unboundedDiscOffset` for consumers that prefer strict
positivity over `1 ≤ d`.
-/
theorem stage3_exists_params_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ UnboundedDiscOffset f d m := by
  refine ⟨stage3_d (f := f) (hf := hf), stage3_m (f := f) (hf := hf), ?_, ?_⟩
  · exact stage3_d_pos (f := f) (hf := hf)
  · exact stage3_unboundedDiscOffset (f := f) (hf := hf)

/-- Existential packaging: Stage 3 yields concrete parameters `d, m` with `1 ≤ d` such that the
bundled offset discrepancy family `discOffset f d m` is unbounded.

This is a minimal corollary of `stage3_unboundedDiscOffset` that many downstream consumers prefer
when they only need the existence of some unbounded offset family.
-/
theorem stage3_exists_params_one_le_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ UnboundedDiscOffset f d m := by
  refine ⟨stage3_d (f := f) (hf := hf), stage3_m (f := f) (hf := hf), ?_, ?_⟩
  · exact stage3_one_le_d (f := f) (hf := hf)
  · exact stage3_unboundedDiscOffset (f := f) (hf := hf)

end Tao2015

end MoltResearch
