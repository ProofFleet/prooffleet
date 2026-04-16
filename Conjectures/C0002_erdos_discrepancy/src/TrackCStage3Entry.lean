import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryCore
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry

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

Most of them live outside `TrackCStage3EntryCore.lean` to minimize the hard-gate compilation surface.

(One tiny definitional rewrite lemma, `stage3Out_out2`, lives in the core module so consumers can
access it without importing this larger convenience layer.)
-/

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

/-- Adding the start index does not change residues modulo the step size.

Since `stage3_start` is a multiple of `stage3_d`, we have
`(n + stage3_start) % stage3_d = n % stage3_d`.
-/
theorem stage3_add_start_mod_d (f : ℕ → ℤ) (hf : IsSignSequence f) (n : ℕ) :
    (n + stage3_start (f := f) (hf := hf)) % stage3_d (f := f) (hf := hf) =
      n % stage3_d (f := f) (hf := hf) := by
  simpa [stage3_d, stage3_start] using stage2_add_start_mod_d (f := f) (hf := hf) n

/-- Recover the bundled offset parameter `stage3_m` by dividing the start index `stage3_start`
by the step size `stage3_d`.

This is a tiny arithmetic convenience lemma: `stage3_start = stage3_m * stage3_d` by definition.
-/
theorem stage3_start_div_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage3_start (f := f) (hf := hf) / stage3_d (f := f) (hf := hf) =
      stage3_m (f := f) (hf := hf) := by
  -- Stage 3 is definitional glue on top of the Stage-2 projections.
  simpa [stage3_start, stage3_d, stage3_m] using stage2_start_div_d (f := f) (hf := hf)

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
The lemma `stage3_unboundedDiscrepancyAlong_core` is provided by
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryMinimal` (re-exported by the core import
path), so we do not re-declare it here.
-/

/-!
## Witness-form corollaries

Most of these are intentionally kept out of the hard-gate core module.

(The most pipeline-friendly variant `stage3_forall_exists_d_ge_one_witness_pos` lives in
`TrackCStage3EntryCore.lean` so hard-gate consumers can access it without importing this file.)
-/

-- The hard-gate core module `TrackCStage3EntryCore.lean` already provides the key witness forms
-- (nucleus and discrepancy versions, including witness-positivity variants).
--
-- This file keeps only additional convenience wrappers that are not part of the hard-gate core API.

-- The discrepancy witness normal form `stage3_forall_exists_discrepancy_gt` lives in
-- `TrackCStage3EntryCore.lean` (hard-gate surface).

/-- Variant of `stage3_forall_exists_discrepancy_gt_witness_pos` with the step-size condition
written as `d ≥ 1`.

Normal form:
`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ discrepancy f d n > C`.
-/
theorem stage3_forall_exists_discrepancy_gt_d_ge_one_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ discrepancy f d n > C := by
  intro C
  rcases stage3_forall_exists_d_ge_one_witness_pos (f := f) (hf := hf) C with
    ⟨d, n, hd, hn, hw⟩
  refine ⟨d, n, hd, hn, ?_⟩
  -- `discrepancy f d n` is definitionally `Int.natAbs (apSum f d n)`.
  change Int.natAbs (apSum f d n) > C
  exact hw

-- (moved to `Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryCore`)

-- Note: `stage3_unboundedDiscOffset` and `stage3_not_exists_boundedDiscOffset` live in
-- `Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryMinimal`.

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

/-- Existential packaging version of `stage3_forall_exists_discOffset_gt'_witness_pos`.

Normal form:
`∀ B, ∃ d m n, 1 ≤ d ∧ n > 0 ∧ discOffset f d m n > B`.

This is a lightweight convenience wrapper: it bundles the deterministic parameters produced by the
pipeline (`stage3_d`, `stage3_m`) together with the witness `n`.
-/
theorem stage3_forall_exists_params_one_le_discOffset_gt'_witness_pos
    (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ, ∃ d m n : ℕ, 1 ≤ d ∧ n > 0 ∧ discOffset f d m n > B := by
  intro B
  rcases stage3_forall_exists_discOffset_gt'_witness_pos (f := f) (hf := hf) B with ⟨n, hn, hgt⟩
  refine ⟨stage3_d (f := f) (hf := hf), stage3_m (f := f) (hf := hf), n, ?_, hn, ?_⟩
  · exact stage3_one_le_d (f := f) (hf := hf)
  · simpa using hgt

/-!
The existential packaging lemmas for `UnboundedDiscOffset` are provided by the hard-gate core module
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryCore`.
-/

-- The existential packaging lemma with hypothesis `1 ≤ d`
-- (stage3_exists_params_one_le_unboundedDiscOffset) is provided by
-- `Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryCore`.

end Tao2015

end MoltResearch
