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

(One tiny definitional rewrite lemma, `stage3Out_out2`, lives in the minimal module so consumers can
access it without importing this larger convenience layer.)
-/

/-- Convenience projection: the reduced step size produced by Stage 3. -/
noncomputable abbrev stage3_d (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  stage2_d (f := f) (hf := hf)

/-- Convenience lemma: the reduced step size produced by Stage 3 is positive. -/
theorem stage3_d_pos (f : ℕ → ℤ) (hf : IsSignSequence f) : stage3_d (f := f) (hf := hf) > 0 := by
  simpa [stage3_d] using stage2_d_pos (f := f) (hf := hf)

/-- Convenience lemma: the reduced step size projection `stage3_d` is at least `1`.

Note: the lemma with the canonical name `stage3_one_le_d` lives in the minimal entry-point module
`TrackCStage3EntryMinimal` and states the same inequality for `(stage3Out ...).d`.
-/
theorem stage3_one_le_d_proj (f : ℕ → ℤ) (hf : IsSignSequence f) :
    1 ≤ stage3_d (f := f) (hf := hf) := by
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

/-- Variant of `stage3_add_start_mod_d` with the start index on the left. -/
theorem stage3_start_add_mod_d (f : ℕ → ℤ) (hf : IsSignSequence f) (n : ℕ) :
    (stage3_start (f := f) (hf := hf) + n) % stage3_d (f := f) (hf := hf) =
      n % stage3_d (f := f) (hf := hf) := by
  simpa [Nat.add_comm] using stage3_add_start_mod_d (f := f) (hf := hf) (n := n)

/-- Adding the start index increases quotients by the offset parameter.

Since `stage3_start = stage3_m * stage3_d`, we have
`(n + stage3_start) / stage3_d = n / stage3_d + stage3_m`.
-/
theorem stage3_add_start_div_d (f : ℕ → ℤ) (hf : IsSignSequence f) (n : ℕ) :
    (n + stage3_start (f := f) (hf := hf)) / stage3_d (f := f) (hf := hf) =
      n / stage3_d (f := f) (hf := hf) + stage3_m (f := f) (hf := hf) := by
  -- Stage 3 is definitional glue on top of the Stage-2 projections.
  simpa [stage3_start, stage3_d, stage3_m] using stage2_add_start_div_d (f := f) (hf := hf) (n := n)

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
## Stage-3 output (`stage3Out`) arithmetic conveniences

These lemmas are not needed by the Track-C hard-gate target
`Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy`, so we keep them out of the minimal
entry-point module `TrackCStage3EntryMinimal`.
-/

/-- The Stage-3 start index is a multiple of the Stage-3 reduced step size. -/
theorem stage3Out_d_dvd_start (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).d ∣ (stage3Out (f := f) (hf := hf)).start := by
  exact Stage3Output.d_dvd_start (f := f) (out := stage3Out (f := f) (hf := hf))

/-- The Stage-3 start index has remainder `0` modulo the reduced step size.

This is often the most convenient normal form of `stage3Out_d_dvd_start`.
-/
theorem stage3Out_start_mod_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).start % (stage3Out (f := f) (hf := hf)).d = 0 := by
  exact Nat.mod_eq_zero_of_dvd (stage3Out_d_dvd_start (f := f) (hf := hf))

/-- Adding the start index does not change residues modulo the step size.

Since `stage3Out ... .start` is a multiple of `stage3Out ... .d`, we have
`(n + start) % d = n % d`.
-/
theorem stage3Out_add_start_mod_d (f : ℕ → ℤ) (hf : IsSignSequence f) (n : ℕ) :
    (n + (stage3Out (f := f) (hf := hf)).start) % (stage3Out (f := f) (hf := hf)).d =
      n % (stage3Out (f := f) (hf := hf)).d := by
  exact Stage3Output.add_start_mod_d (f := f) (out := stage3Out (f := f) (hf := hf)) n

/-- Variant of `stage3Out_add_start_mod_d` with the start index on the left. -/
theorem stage3Out_start_add_mod_d (f : ℕ → ℤ) (hf : IsSignSequence f) (n : ℕ) :
    ((stage3Out (f := f) (hf := hf)).start + n) % (stage3Out (f := f) (hf := hf)).d =
      n % (stage3Out (f := f) (hf := hf)).d := by
  exact Stage3Output.start_add_mod_d (f := f) (out := stage3Out (f := f) (hf := hf)) n

/-- Convenience lemma: the Stage-3 reduced sequence is a sign sequence.

This is a tiny wrapper around the Stage-2 core projection lemma `Stage2Output.hg`.
-/
theorem stage3Out_hg (f : ℕ → ℤ) (hf : IsSignSequence f) :
    IsSignSequence (stage3Out (f := f) (hf := hf)).g := by
  exact Stage2Output.hg (out := (stage3Out (f := f) (hf := hf)).out2)

/-- Adding the start index increases quotients by the offset parameter.

Since `start = m*d`, we have
`(n + start) / d = n / d + m`.
-/
theorem stage3Out_add_start_div_d (f : ℕ → ℤ) (hf : IsSignSequence f) (n : ℕ) :
    (n + (stage3Out (f := f) (hf := hf)).start) / (stage3Out (f := f) (hf := hf)).d =
      n / (stage3Out (f := f) (hf := hf)).d + (stage3Out (f := f) (hf := hf)).m := by
  have hd' : 0 < (stage3Out (f := f) (hf := hf)).d := stage3Out_d_pos (f := f) (hf := hf)
  rw [stage3Out_start_eq_m_mul_d (f := f) (hf := hf)]
  simpa using
    (Nat.add_mul_div_right (x := n) (y := (stage3Out (f := f) (hf := hf)).m)
      (z := (stage3Out (f := f) (hf := hf)).d) hd')

/-- Variant of `stage3Out_add_start_div_d` with the start index on the left. -/
theorem stage3Out_start_add_div_d (f : ℕ → ℤ) (hf : IsSignSequence f) (n : ℕ) :
    ((stage3Out (f := f) (hf := hf)).start + n) / (stage3Out (f := f) (hf := hf)).d =
      n / (stage3Out (f := f) (hf := hf)).d + (stage3Out (f := f) (hf := hf)).m := by
  calc
    ((stage3Out (f := f) (hf := hf)).start + n) / (stage3Out (f := f) (hf := hf)).d =
        (n + (stage3Out (f := f) (hf := hf)).start) / (stage3Out (f := f) (hf := hf)).d := by
      simp [Nat.add_comm]
    _ = n / (stage3Out (f := f) (hf := hf)).d + (stage3Out (f := f) (hf := hf)).m := by
      simpa using stage3Out_add_start_div_d (f := f) (hf := hf) (n := n)

/-- Recover the offset parameter `m` by dividing the Stage-3 start index `start` by the step size `d`.

This is a tiny arithmetic convenience lemma: `start = m*d` by definition.
-/
theorem stage3Out_start_div_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).start / (stage3Out (f := f) (hf := hf)).d =
      (stage3Out (f := f) (hf := hf)).m := by
  have hd' : 0 < (stage3Out (f := f) (hf := hf)).d := stage3Out_d_pos (f := f) (hf := hf)
  rw [stage3Out_start_eq_m_mul_d (f := f) (hf := hf)]
  exact Nat.mul_div_left (stage3Out (f := f) (hf := hf)).m hd'

/-- Convenience lemma: the Stage-3 reduced step size is nonzero.

This is sometimes the right normal form for downstream stages that treat `d` as a denominator (or
simply want to avoid rewriting strict inequalities).
-/
theorem stage3Out_d_ne_zero (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).d ≠ 0 := by
  -- Delegate to the Stage-2 core lemma; avoids re-proving arithmetic facts.
  simpa using (Stage2Output.d_ne_zero (out := (stage3Out (f := f) (hf := hf)).out2))

/-!
The lemma `stage3_unboundedDiscrepancyAlong_core` is provided by
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryCore` (re-exported by the core import
path), so we do not re-declare it here.
-/

/-!
## Offset-discrepancy normal forms (affine-tail nuclei)

These are tiny rewrite helpers for the deterministic Stage-3 parameters `(stage3_d, stage3_m)`.
They let downstream stages work directly with the affine-tail nucleus `apSumFrom` without
unfolding `discOffset` or repeatedly rewriting the start index `m*d`.
-/

/-- Normal form: the bundled offset discrepancy wrapper `discOffset` at the deterministic Stage-3
parameters is the absolute value of the affine-tail nucleus `apSumFrom` at the deterministic start
index `stage3_start = stage3_m * stage3_d`.

This is just `Tao2015.discOffset_eq_natAbs_apSumFrom_mul` specialized to the Stage-3 projections.
-/
theorem stage3_discOffset_eq_natAbs_apSumFrom_start (f : ℕ → ℤ) (hf : IsSignSequence f) (n : ℕ) :
    discOffset f (stage3_d (f := f) (hf := hf)) (stage3_m (f := f) (hf := hf)) n =
      Int.natAbs
        (apSumFrom f (stage3_start (f := f) (hf := hf)) (stage3_d (f := f) (hf := hf)) n) := by
  -- Rewrite the start index `stage3_start` to `stage3_m * stage3_d`, then apply the generic lemma.
  simpa [stage3_start_eq_m_mul_d (f := f) (hf := hf)] using
    (discOffset_eq_natAbs_apSumFrom_mul (f := f)
      (d := stage3_d (f := f) (hf := hf)) (m := stage3_m (f := f) (hf := hf)) (n := n))

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

-- The lemma `stage3_forall_exists_discrepancy_gt_d_ge_one_witness_pos` is provided by
-- `Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryCore`.

-- Note: `stage3_unboundedDiscOffset` and `stage3_not_exists_boundedDiscOffset` live in
-- `Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryCore`.

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
  · exact stage3_one_le_d_proj (f := f) (hf := hf)
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
