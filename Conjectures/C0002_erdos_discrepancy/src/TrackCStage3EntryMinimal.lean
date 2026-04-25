import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Stub

/-!
# Track C: Stage 3 entry point (hard-gate minimal)

This file is **Conjectures-only** glue.

It provides the minimal Stage-3 entry point API needed by the Track-C hard-gate target
`Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy`:

- `stage3` / `stage3Out` : produce a `Stage3Output f` from a sign sequence `f`
- `stage3_notBounded` : close the core goal `¬ BoundedDiscrepancy f`
- `stage3_forall_hasDiscrepancyAtLeast` : the usual surface statement
  `∀ C, HasDiscrepancyAtLeast f C`
- `stage3_forall_exists_d_ge_one_witness_pos` : nucleus witness form using `apSum`
  `∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`
- `stage3_forall_exists_discrepancy_gt` : the discrepancy witness form
  `∀ C, ∃ d n, d > 0 ∧ discrepancy f d n > C`
- `stage3_forall_exists_discrepancy_gt_witness_pos` : witness form with `n > 0`
  `∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ discrepancy f d n > C`
- `stage3_hasDiscrepancyAtLeast` : specialization at a fixed threshold `C`
- `stage3_not_exists_boundedDiscOffset` : stable boundedness-negation packaging of the
  Stage-2 offset-discrepancy witness
- `stage3_unboundedDiscOffset` : stable packaging of the Stage-2 offset-discrepancy witness
- `stage3_exists_params_unboundedDiscOffset` : existential packaging of `stage3_unboundedDiscOffset`
- `stage3_exists_params_one_le_unboundedDiscOffset` : existential packaging of
  `stage3_unboundedDiscOffset` with the side condition `1 ≤ d`
- `stage3_exists_params_one_le_not_exists_forall_natAbs_apSumFrom_mul_le` : existential packaging of
  the affine-tail unboundedness normal form at concrete `d, m`
- `stage3_unboundedDiscrepancyAlong_core` : Track-C fixed-step unboundedness witness along the
  reduced sequence, phrased using `MoltResearch.UnboundedDiscrepancyAlong`
- `stage3_exists_params_one_le_not_exists_boundedDiscOffset` : existential packaging of
  `stage3_not_exists_boundedDiscOffset`

All additional projection/rewrite lemmas and most witness-form corollaries live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryCore`.
-/

namespace MoltResearch

namespace Tao2015

/-- Conjectures-only Stage 3 entry point: run Stage 2, then close the global goal via the proved
Stage-3 boundary lemma `Stage3Output.ofStage2Output`.

This is a definition (not an axiom): Stage 3 is non-stub glue on top of the Stage-2 axiom.
-/
noncomputable def stage3 (f : ℕ → ℤ) (hf : IsSignSequence f) [Stage2Assumption] :
    Stage3Output f :=
  Stage3Output.ofStage2Output (f := f) (stage2Out (f := f) (hf := hf))

/-- Non-typeclass entry point: run Stage 3 using an explicit `Stage2Assumption` proof.

This mirrors the Stage-2 helper `stage2OutOf` and is useful in downstream developments that want to
avoid `letI` / typeclass search and pass a verified Stage-2 assumption explicitly.
-/
noncomputable def stage3Of (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    Stage3Output f :=
  Stage3Output.ofStage2Output (f := f) (stage2OutOf inst (f := f) (hf := hf))

/-- Abbreviation wrapper for `stage3Of` (mirrors `stage3Out`). -/
noncomputable abbrev stage3OutOf (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    Stage3Output f :=
  stage3Of inst (f := f) (hf := hf)

/-- Deterministic name for the Stage-3 output (useful to keep later statements readable). -/
noncomputable abbrev stage3Out (f : ℕ → ℤ) (hf : IsSignSequence f) [Stage2Assumption] :
    Stage3Output f :=
  stage3 (f := f) (hf := hf)

/-- Explicit-assumption wrapper around `stage3Out`.

This returns the typeclass-based output `stage3Out` but with the instance `inst` installed locally.
It lets downstream code use lemmas stated in terms of `stage3Out` without writing `letI` at the call
site.
-/
noncomputable abbrev stage3OutWith (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    Stage3Output f :=
  (by
    classical
    letI : Stage2Assumption := inst
    exact stage3Out (f := f) (hf := hf))

/-- `stage3OutOf` agrees definitionally with `stage3OutWith`. -/
theorem stage3OutOf_eq_stage3OutWith (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage3OutOf inst (f := f) (hf := hf) = stage3OutWith inst (f := f) (hf := hf) := by
  classical
  rfl

/-!
## Definitional rewrites

These simp lemmas reduce rewriting noise when shuttling statements between Stage 2 and Stage 3.
They are intentionally kept in the minimal entry-point module.
-/

/-- Definitional rewrite: the Stage-2 output stored inside `stage3OutWith inst` is the Stage-2 output
produced by Stage 2 with the instance `inst` installed locally.

This is the explicit-assumption analogue of `stage3OutWith` itself: it lets consumer code rewrite
`.out2` without switching to the `stage3OutOf` API.
-/
@[simp] theorem stage3OutWith_out2 (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3OutWith inst (f := f) (hf := hf)).out2 = stage2OutWith inst (f := f) (hf := hf) := by
  classical
  simp [stage3OutWith, stage2OutWith, stage3Out, stage3]

/-- Definitional rewrite: the Stage-1 reduction output stored inside `stage3OutWith inst` is the
Stage-1 reduction output stored inside `stage2OutWith inst`.

This is occasionally convenient in downstream stages that want to rewrite `.out1` while still
using the typeclass-based `stage3Out` API.
-/
@[simp] theorem stage3OutWith_out1 (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3OutWith inst (f := f) (hf := hf)).out1 =
      (stage2OutWith inst (f := f) (hf := hf)).out1 := by
  classical
  simp [stage3OutWith, stage2OutWith, stage3Out, stage3]

/-- Definitional rewrite: the reduced step size stored inside `stage3OutWith inst` is the
Stage-2 reduced step size produced under the same explicit assumption.

This is the explicit-assumption analogue of the simp lemma `stage3Out_d`.
-/
@[simp] theorem stage3OutWith_d (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3OutWith inst (f := f) (hf := hf)).d = (stage2OutWith inst (f := f) (hf := hf)).d := by
  classical
  -- Reduce to the Stage-2 projection via the definitional rewrite on `.out2`.
  simpa [Stage3Output.d] using congrArg Stage2Output.d
    (stage3OutWith_out2 (inst := inst) (f := f) (hf := hf))

/-- Definitional rewrite: the bundled offset parameter stored inside `stage3OutWith inst` is the
Stage-2 parameter produced under the same explicit assumption.

This is the explicit-assumption analogue of the simp lemma `stage3Out_m`.
-/
@[simp] theorem stage3OutWith_m (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3OutWith inst (f := f) (hf := hf)).m = (stage2OutWith inst (f := f) (hf := hf)).m := by
  classical
  -- Reduce to the Stage-2 projection via the definitional rewrite on `.out2`.
  simpa [Stage3Output.m] using congrArg Stage2Output.m
    (stage3OutWith_out2 (inst := inst) (f := f) (hf := hf))

/-- Definitional rewrite: the Stage-3 affine-tail start index stored inside `stage3OutWith inst` is
the Stage-2 start index produced under the same explicit assumption.

This lets consumer code rewrite `.start` without reaching through `.out2`.
-/
@[simp] theorem stage3OutWith_start (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3OutWith inst (f := f) (hf := hf)).start =
      (stage2OutWith inst (f := f) (hf := hf)).start := by
  classical
  simp [Stage3Output.start]

/-- The Stage-2 output stored inside `stage3OutOf inst` is definitionally the Stage-2 output
produced by Stage 2 using the explicit assumption `inst`.

This is the explicit-assumption analogue of `stage3Out_out2`.
-/
@[simp] theorem stage3OutOf_out2 (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3OutOf inst (f := f) (hf := hf)).out2 = stage2OutOf inst (f := f) (hf := hf) := by
  rfl

/-- Definitional rewrite: the Stage-1 reduction output stored inside `stage3OutOf inst` is the
Stage-1 reduction output stored inside `stage2OutOf inst`.

This is the explicit-assumption analogue of `stage3Out_out1`.
-/
@[simp] theorem stage3OutOf_out1 (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3OutOf inst (f := f) (hf := hf)).out1 = (stage2OutOf inst (f := f) (hf := hf)).out1 := by
  rfl

/-- Definitional rewrite: the Stage-3 reduced step size stored inside `stage3OutOf inst` is the
Stage-2 reduced step size stored inside `stage2OutOf inst`.
-/
@[simp] theorem stage3OutOf_d (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3OutOf inst (f := f) (hf := hf)).d = (stage2OutOf inst (f := f) (hf := hf)).d := by
  rfl

/-- Definitional rewrite: the Stage-3 bundled offset parameter stored inside `stage3OutOf inst` is
the Stage-2 parameter stored inside `stage2OutOf inst`.
-/
@[simp] theorem stage3OutOf_m (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3OutOf inst (f := f) (hf := hf)).m = (stage2OutOf inst (f := f) (hf := hf)).m := by
  rfl

/-- Definitional rewrite: the Stage-3 reduced sequence stored inside `stage3OutOf inst` is the
Stage-2 reduced sequence stored inside `stage2OutOf inst`.
-/
@[simp] theorem stage3OutOf_g (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3OutOf inst (f := f) (hf := hf)).g = (stage2OutOf inst (f := f) (hf := hf)).g := by
  rfl

/-- Definitional rewrite: the Stage-3 start index stored inside `stage3OutOf inst` is the
Stage-2 start index stored inside `stage2OutOf inst`.
-/
@[simp] theorem stage3OutOf_start (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3OutOf inst (f := f) (hf := hf)).start = (stage2OutOf inst (f := f) (hf := hf)).start := by
  rfl

/-- If we register an explicit assumption `inst` as the local typeclass instance, then the
explicit Stage-3 output `stage3OutOf inst` agrees definitionally with the typeclass-based output
`stage3Out`.

This is useful when consumer code wants to pass `inst` explicitly but also reuse lemmas phrased in
terms of `stage3Out`.
-/
theorem stage3OutOf_eq_stage3Out (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage3OutOf inst (f := f) (hf := hf) =
      (by
        classical
        letI : Stage2Assumption := inst
        exact stage3Out (f := f) (hf := hf)) := by
  classical
  rfl

/-- The Stage-2 output stored inside `stage3Out` is definitionally the Stage-2 output produced by
Stage 2.

This lemma is tiny but useful for rewriting when shuttling statements between Stage 2 and Stage 3.
-/
@[simp] theorem stage3Out_out2 (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).out2 = stage2Out (f := f) (hf := hf) := by
  rfl

/-- The Stage-1 reduction output stored inside `stage3Out` is definitionally the Stage-1 reduction
output produced by Stage 2.
-/
@[simp] theorem stage3Out_out1 (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).out1 = (stage2Out (f := f) (hf := hf)).out1 := by
  rfl

/-- Definitional rewrite: the Stage-3 reduced step size equals the Stage-2 reduced step size. -/
@[simp] theorem stage3Out_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).d = (stage2Out (f := f) (hf := hf)).d := by
  rfl

/-- Definitional rewrite: the Stage-3 bundled offset parameter equals the Stage-2 parameter. -/
@[simp] theorem stage3Out_m (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).m = (stage2Out (f := f) (hf := hf)).m := by
  rfl

/-- Definitional rewrite: the Stage-3 reduced sequence equals the Stage-2 reduced sequence. -/
@[simp] theorem stage3Out_g (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).g = (stage2Out (f := f) (hf := hf)).g := by
  rfl

/-- Definitional rewrite: the Stage-3 start index `m*d` equals the Stage-2 start index. -/
@[simp] theorem stage3Out_start (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).start = (stage2Out (f := f) (hf := hf)).start := by
  rfl

/-- Definitional rewrite: the Stage-3 start index is `m*d` for the bundled Stage-3 parameters.

We keep this lemma (without making it a simp lemma) in the minimal entry-point module so downstream
stages can normalize start-index expressions without importing the larger Stage-3 convenience layer.
-/
theorem stage3Out_start_eq_m_mul_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).start =
      (stage3Out (f := f) (hf := hf)).m * (stage3Out (f := f) (hf := hf)).d := by
  rfl

/-- Explicit-assumption analogue of `stage3Out_start_eq_m_mul_d`. -/
theorem stage3OutOf_start_eq_m_mul_d (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3OutOf inst (f := f) (hf := hf)).start =
      (stage3OutOf inst (f := f) (hf := hf)).m * (stage3OutOf inst (f := f) (hf := hf)).d := by
  rfl

/-- Recover the offset parameter `m` by dividing the Stage-3 start index by the Stage-3 step size.

This is a tiny arithmetic convenience lemma: by definition, `start = m * d`.
-/
theorem stage3Out_start_div_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).start / (stage3Out (f := f) (hf := hf)).d =
      (stage3Out (f := f) (hf := hf)).m := by
  exact Stage3Output.start_div_d (f := f) (out := stage3Out (f := f) (hf := hf))

/-- Explicit-assumption analogue of `stage3Out_start_div_d`. -/
theorem stage3OutOf_start_div_d (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3OutOf inst (f := f) (hf := hf)).start / (stage3OutOf inst (f := f) (hf := hf)).d =
      (stage3OutOf inst (f := f) (hf := hf)).m := by
  exact Stage3Output.start_div_d (f := f) (out := stage3OutOf inst (f := f) (hf := hf))

/-- The affine-tail start index stored in `stage3Out` is a multiple of the reduced step size. -/
theorem stage3Out_d_dvd_start (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).d ∣ (stage3Out (f := f) (hf := hf)).start := by
  exact Stage3Output.d_dvd_start (f := f) (out := stage3Out (f := f) (hf := hf))

/-- Explicit-assumption analogue of `stage3Out_d_dvd_start`. -/
theorem stage3OutOf_d_dvd_start (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3OutOf inst (f := f) (hf := hf)).d ∣ (stage3OutOf inst (f := f) (hf := hf)).start := by
  exact Stage3Output.d_dvd_start (f := f) (out := stage3OutOf inst (f := f) (hf := hf))

/-- The affine-tail start index stored in `stage3Out` has remainder `0` modulo the reduced step size.
-/
theorem stage3Out_start_mod_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).start % (stage3Out (f := f) (hf := hf)).d = 0 := by
  exact Stage3Output.start_mod_d (f := f) (out := stage3Out (f := f) (hf := hf))

/-- Explicit-assumption analogue of `stage3Out_start_mod_d`. -/
theorem stage3OutOf_start_mod_d (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3OutOf inst (f := f) (hf := hf)).start % (stage3OutOf inst (f := f) (hf := hf)).d = 0 := by
  exact Stage3Output.start_mod_d (f := f) (out := stage3OutOf inst (f := f) (hf := hf))

-- Note: additional arithmetic convenience lemmas about `stage3Out` (e.g. reduced-sequence wrappers)
-- live in `Conjectures.C0002_erdos_discrepancy.src.TrackCStage3Entry`.

/-- Convenience lemma: the Stage-3 reduced step size is at least `1`.

This is a tiny wrapper around the Stage-2 projection lemma `Stage2Output.one_le_d`.
-/
theorem stage3_one_le_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    1 ≤ (stage3Out (f := f) (hf := hf)).d := by
  simpa using (Stage2Output.one_le_d (out := (stage3Out (f := f) (hf := hf)).out2))

/-- Convenience lemma: the Stage-3 reduced step size is positive.

This is sometimes the right normal form when downstream stages want to treat `d` as a denominator
(or simply avoid rewriting `1 ≤ d`).

Implementation note: we intentionally avoid `simp` here so the proof does not depend on the
current simp set; we instead transport positivity from the proved lemma `stage3_one_le_d`.
-/
theorem stage3Out_d_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).d > 0 := by
  have h1 : 1 ≤ (stage3Out (f := f) (hf := hf)).d := stage3_one_le_d (f := f) (hf := hf)
  exact lt_of_lt_of_le Nat.zero_lt_one h1

/-- Convenience lemma: the Stage-3 reduced step size is nonzero.

This is a tiny wrapper around `stage3Out_d_pos` since some arithmetic lemmas want the side
condition `d ≠ 0` rather than strict positivity.
-/
theorem stage3Out_d_ne_zero (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).d ≠ 0 := by
  exact Nat.ne_of_gt (stage3Out_d_pos (f := f) (hf := hf))

/-- Convenience lemma: the explicit-assumption Stage-3 reduced step size is at least `1`.

This is the explicit-assumption analogue of `stage3_one_le_d`.
-/
theorem stage3OutOf_one_le_d (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    1 ≤ (stage3OutOf inst (f := f) (hf := hf)).d := by
  simpa using (Stage2Output.one_le_d (out := (stage3OutOf inst (f := f) (hf := hf)).out2))

/-- Convenience lemma: the explicit-assumption Stage-3 reduced step size is positive.

This is the explicit-assumption analogue of `stage3Out_d_pos`.
-/
theorem stage3OutOf_d_pos (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3OutOf inst (f := f) (hf := hf)).d > 0 := by
  have h1 : 1 ≤ (stage3OutOf inst (f := f) (hf := hf)).d :=
    stage3OutOf_one_le_d (inst := inst) (f := f) (hf := hf)
  exact lt_of_lt_of_le Nat.zero_lt_one h1

/-- Convenience lemma: the explicit-assumption Stage-3 reduced step size is nonzero.

This is the explicit-assumption analogue of `stage3Out_d_ne_zero`.
-/
theorem stage3OutOf_d_ne_zero (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3OutOf inst (f := f) (hf := hf)).d ≠ 0 := by
  exact Nat.ne_of_gt (stage3OutOf_d_pos (inst := inst) (f := f) (hf := hf))

-- Note: the simp lemma `stage3Out_out2` is enough to rewrite projections like
-- `(stage3Out ...).out2.d` to `(stage2Out ...).d`, but we also provide `[simp]` lemmas for the
-- common projections `.d/.m/.g` so consumers can rewrite without reaching through `.out2`.

/-- Consumer-facing shortcut: the Stage-3 pipeline closes the core goal `¬ BoundedDiscrepancy f`.

We keep this lemma in the hard-gate minimal module so `ErdosDiscrepancy.lean` can remain minimal.
-/
theorem stage3_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  let out := stage3Out (f := f) (hf := hf)
  exact out.notBounded

/-- Explicit-assumption variant of `stage3_notBounded`. -/
theorem stage3OutOf_notBounded (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ BoundedDiscrepancy f := by
  let out := stage3OutOf inst (f := f) (hf := hf)
  exact out.notBounded

/-- Stable boundedness-negation packaging of the Stage-3 offset-discrepancy witness.

Normal form:
`¬ ∃ B, BoundedDiscOffset f (stage3Out ...).d (stage3Out ...).m B`.

This is a thin wrapper around `Stage3Output.not_exists_boundedDiscOffset`.
-/
theorem stage3_not_exists_boundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ,
      BoundedDiscOffset f
        (stage3Out (f := f) (hf := hf)).d
        (stage3Out (f := f) (hf := hf)).m B := by
  let out := stage3Out (f := f) (hf := hf)
  exact Stage3Output.not_exists_boundedDiscOffset (f := f) out

/-- Explicit-assumption variant of `stage3_not_exists_boundedDiscOffset`. -/
theorem stage3OutOf_not_exists_boundedDiscOffset (inst : Stage2Assumption) (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ,
      BoundedDiscOffset f
        (stage3OutOf inst (f := f) (hf := hf)).d
        (stage3OutOf inst (f := f) (hf := hf)).m B := by
  let out := stage3OutOf inst (f := f) (hf := hf)
  exact Stage3Output.not_exists_boundedDiscOffset (f := f) out

/-- Stable witness packaging of the Stage-3 offset-discrepancy unboundedness statement.

Normal form:
`UnboundedDiscOffset f (stage3Out ...).d (stage3Out ...).m`.

This is a thin wrapper around `Stage3Output.unboundedDiscOffset`.
-/
theorem stage3_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    UnboundedDiscOffset f
      (stage3Out (f := f) (hf := hf)).d
      (stage3Out (f := f) (hf := hf)).m := by
  let out := stage3Out (f := f) (hf := hf)
  exact out.unboundedDiscOffset (f := f)

/-- Explicit-assumption variant of `stage3_unboundedDiscOffset`. -/
theorem stage3OutOf_unboundedDiscOffset (inst : Stage2Assumption) (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    UnboundedDiscOffset f
      (stage3OutOf inst (f := f) (hf := hf)).d
      (stage3OutOf inst (f := f) (hf := hf)).m := by
  let out := stage3OutOf inst (f := f) (hf := hf)
  exact out.unboundedDiscOffset (f := f)

/-- Negation-normal-form packaging of the Stage-3 offset-discrepancy witness family.

Normal form:
`¬ ∃ B, ∀ n, discOffset f (stage3Out ...).d (stage3Out ...).m n ≤ B`.

This is a small convenience wrapper around `stage3_unboundedDiscOffset` and the equivalence
`unboundedDiscOffset_iff_not_exists_forall_discOffset_le`.
-/
theorem stage3_not_exists_forall_discOffset_le_d_m (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ,
        ∀ n : ℕ,
          discOffset f
              (stage3Out (f := f) (hf := hf)).d
              (stage3Out (f := f) (hf := hf)).m n ≤ B := by
  set out := stage3Out (f := f) (hf := hf) with hout
  have hunb : UnboundedDiscOffset f out.d out.m := by
    simpa [hout] using stage3_unboundedDiscOffset (f := f) (hf := hf)
  simpa [hout] using
    (unboundedDiscOffset_iff_not_exists_forall_discOffset_le (f := f) (d := out.d) (m := out.m)).1
      hunb

/-- Consumer-facing normal form: there is no uniform bound on the affine-tail nuclei
`Int.natAbs (apSumFrom f start d n)` at the deterministic Stage-2 parameters stored in `stage3Out`.

Negation normal form:
`¬ ∃ B, ∀ n, Int.natAbs (apSumFrom f start d n) ≤ B`.

This is the `discOffset` boundedness-negation witness `stage3_not_exists_forall_discOffset_le_d_m`
rewritten using the Stage-3 normal form
`discOffset f d m n = Int.natAbs (apSumFrom f (m*d) d n)`.
-/
theorem stage3_not_exists_forall_natAbs_apSumFrom_start_le (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ,
        ∀ n : ℕ,
          Int.natAbs
              (apSumFrom f
                (stage3Out (f := f) (hf := hf)).out2.start
                (stage3Out (f := f) (hf := hf)).out2.d n) ≤ B := by
  set out := stage3Out (f := f) (hf := hf) with hout
  simpa [hout, Stage3Output.start, Stage3Output.d] using
    (Stage3Output.not_exists_forall_natAbs_apSumFrom_start_le (f := f) out)

/-- Variant of `stage3_not_exists_forall_natAbs_apSumFrom_start_le` phrased using the Stage-3
projection names `.start` and `.d` (rather than reaching through `.out2`).

This is purely a rewrite convenience lemma for downstream stages.
-/
theorem stage3_not_exists_forall_natAbs_apSumFrom_start_le' (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ,
        ∀ n : ℕ,
          Int.natAbs
              (apSumFrom f
                (stage3Out (f := f) (hf := hf)).start
                (stage3Out (f := f) (hf := hf)).d n) ≤ B := by
  simpa [Stage3Output.start, Stage3Output.d] using
    (stage3_not_exists_forall_natAbs_apSumFrom_start_le (f := f) (hf := hf))

/-- Tail-nucleus witness form at the deterministic Stage-3 parameters.

Normal form:
`∀ B, ∃ n, n > 0 ∧ Int.natAbs (apSumFrom f start d n) > B`.

This is the witness-form contraposition of
`stage3_not_exists_forall_natAbs_apSumFrom_start_le'`.
-/
theorem stage3_forall_exists_natAbs_apSumFrom_start_gt_witness_pos (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ,
        n > 0 ∧
          Int.natAbs
              (apSumFrom f
                (stage3Out (f := f) (hf := hf)).start
                (stage3Out (f := f) (hf := hf)).d n) > B := by
  classical
  intro B
  set out := stage3Out (f := f) (hf := hf) with hout
  have hnb :
      ¬ ∃ B0 : ℕ, ∀ n : ℕ, Int.natAbs (apSumFrom f out.start out.d n) ≤ B0 := by
    simpa [hout] using
      (stage3_not_exists_forall_natAbs_apSumFrom_start_le' (f := f) (hf := hf))
  have hex : ∃ n : ℕ, Int.natAbs (apSumFrom f out.start out.d n) > B := by
    by_contra h
    have hle : ∀ n : ℕ, Int.natAbs (apSumFrom f out.start out.d n) ≤ B := by
      intro n
      have hnot : ¬ Int.natAbs (apSumFrom f out.start out.d n) > B := by
        intro hn
        exact h ⟨n, hn⟩
      exact le_of_not_gt hnot
    exact hnb ⟨B, hle⟩
  rcases hex with ⟨n, hn⟩
  have hn0 : n ≠ 0 := by
    intro h0
    subst h0
    have hzero : Int.natAbs (apSumFrom f out.start out.d 0) = 0 := by
      simp
    have hn0gt : (0 : ℕ) > B := by
      simpa [hzero] using hn
    have hlt : B < 0 := (gt_iff_lt).1 hn0gt
    exact (Nat.not_lt_zero B) hlt
  refine ⟨n, Nat.pos_of_ne_zero hn0, ?_⟩
  simpa [hout] using hn

/-- Existential packaging: Stage 3 yields concrete parameters `d, m` with `d > 0` such that the
bundled offset discrepancy family `discOffset f d m` is unbounded.

This is a minimal corollary of `stage3_unboundedDiscOffset`; some downstream stages prefer strict
positivity over `1 ≤ d`.
-/
theorem stage3_exists_params_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ UnboundedDiscOffset f d m := by
  let out := stage3Out (f := f) (hf := hf)
  refine ⟨out.d, out.m, ?_, ?_⟩
  · exact stage3Out_d_pos (f := f) (hf := hf)
  · exact stage3_unboundedDiscOffset (f := f) (hf := hf)

/-- Explicit-assumption variant of `stage3_exists_params_unboundedDiscOffset`. -/
theorem stage3OutOf_exists_params_unboundedDiscOffset (inst : Stage2Assumption) (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ UnboundedDiscOffset f d m := by
  let out := stage3OutOf inst (f := f) (hf := hf)
  refine ⟨out.d, out.m, ?_, ?_⟩
  · exact stage3OutOf_d_pos (inst := inst) (f := f) (hf := hf)
  · exact stage3OutOf_unboundedDiscOffset (inst := inst) (f := f) (hf := hf)

/-- Existential packaging: Stage 3 yields concrete parameters `d, m` with `1 ≤ d` such that the
bundled offset discrepancy family `discOffset f d m` is unbounded.

This is a minimal corollary of `stage3_unboundedDiscOffset`; some downstream stages prefer `1 ≤ d`
to avoid rewriting strict positivity.
-/
theorem stage3_exists_params_one_le_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ UnboundedDiscOffset f d m := by
  let out := stage3Out (f := f) (hf := hf)
  refine ⟨out.d, out.m, ?_, ?_⟩
  · exact stage3_one_le_d (f := f) (hf := hf)
  · exact stage3_unboundedDiscOffset (f := f) (hf := hf)

/-- Existential packaging: Stage 3 yields concrete parameters `d, m` with `1 ≤ d` such that there is
no uniform bound on the affine-tail nuclei `Int.natAbs (apSumFrom f (m*d) d n)`.

Normal form:
`∃ d m, 1 ≤ d ∧ ¬ ∃ B, ∀ n, Int.natAbs (apSumFrom f (m*d) d n) ≤ B`.

This is `stage3_exists_params_one_le_unboundedDiscOffset` rewritten using
`Tao2015.UnboundedDiscOffset.iff_not_exists_forall_natAbs_apSumFrom_mul_le`.
-/
theorem stage3_exists_params_one_le_not_exists_forall_natAbs_apSumFrom_mul_le
    (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      ¬ ∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) ≤ B := by
  rcases stage3_exists_params_one_le_unboundedDiscOffset (f := f) (hf := hf) with ⟨d, m, hd, hunb⟩
  refine ⟨d, m, hd, ?_⟩
  exact
    (Tao2015.UnboundedDiscOffset.iff_not_exists_forall_natAbs_apSumFrom_mul_le (f := f)
        (d := d) (m := m)).1
      hunb

/-- Existential packaging: Stage 3 yields concrete parameters `d, m` with `1 ≤ d` such that there is
no bundled offset bound at those parameters.

Normal form: `∃ d m, 1 ≤ d ∧ ¬ ∃ B, BoundedDiscOffset f d m B`.

This is a minimal-entry convenience lemma for downstream stages that prefer not to mention the
record fields of `stage3Out`.
-/
theorem stage3_exists_params_one_le_not_exists_boundedDiscOffset (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ ¬ ∃ B : ℕ, BoundedDiscOffset f d m B := by
  let out := stage3Out (f := f) (hf := hf)
  refine ⟨out.d, out.m, ?_, ?_⟩
  · exact stage3_one_le_d (f := f) (hf := hf)
  · exact stage3_not_exists_boundedDiscOffset (f := f) (hf := hf)

/-- Track-C pipeline witness: Stage 3 yields unbounded discrepancy along the reduced sequence,
phrased using the verified core predicate `MoltResearch.UnboundedDiscrepancyAlong`.

This is a thin wrapper around `Stage3Output.unboundedDiscrepancyAlong_core`.
-/
theorem stage3_unboundedDiscrepancyAlong_core (f : ℕ → ℤ) (hf : IsSignSequence f) :
    MoltResearch.UnboundedDiscrepancyAlong
      (stage3Out (f := f) (hf := hf)).g
      (stage3Out (f := f) (hf := hf)).d := by
  let out := stage3Out (f := f) (hf := hf)
  exact out.unboundedDiscrepancyAlong_core (f := f)

/-- Consumer-facing shortcut: the Stage-3 pipeline yields the usual surface statement
`∀ C, HasDiscrepancyAtLeast f C`.

This is a thin wrapper around `Stage3Output.forall_hasDiscrepancyAtLeast`.
-/
theorem stage3_forall_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  let out := stage3Out (f := f) (hf := hf)
  exact Stage3Output.forall_hasDiscrepancyAtLeast (f := f) out

/-- Explicit-assumption variant of `stage3_forall_hasDiscrepancyAtLeast`. -/
theorem stage3OutOf_forall_hasDiscrepancyAtLeast (inst : Stage2Assumption) (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  let out := stage3OutOf inst (f := f) (hf := hf)
  exact Stage3Output.forall_hasDiscrepancyAtLeast (f := f) out

/-- Consumer-facing nucleus witness form, avoiding the `discrepancy` wrapper.

Normal form:
`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is a thin wrapper around `Stage3Output.forall_exists_d_ge_one_witness_pos`.
-/
theorem stage3_forall_exists_d_ge_one_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  let out := stage3Out (f := f) (hf := hf)
  exact out.forall_exists_d_ge_one_witness_pos (f := f)

/-- Consumer-facing witness form: Stage 3 yields explicit discrepancy witnesses.

Normal form:
`∀ C, ∃ d n, d > 0 ∧ discrepancy f d n > C`.

This is obtained from `stage3_forall_hasDiscrepancyAtLeast` via
`HasDiscrepancyAtLeast_iff_exists_discrepancy`.
-/
theorem stage3_forall_exists_discrepancy_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ discrepancy f d n > C := by
  let out := stage3Out (f := f) (hf := hf)
  exact out.forall_exists_discrepancy_gt (f := f)

/-- Variant of `stage3_forall_exists_discrepancy_gt` with a positive-length witness `n > 0`.

Normal form:
`∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ discrepancy f d n > C`.

This is a thin wrapper around the Stage-3 API lemma
`Stage3Output.forall_exists_discrepancy_gt_witness_pos`.
-/
theorem stage3_forall_exists_discrepancy_gt_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ discrepancy f d n > C := by
  let out := stage3Out (f := f) (hf := hf)
  exact out.forall_exists_discrepancy_gt_witness_pos (f := f)

/-- Specialization of `stage3_forall_hasDiscrepancyAtLeast` at a fixed threshold `C`.

This is a tiny convenience lemma: it avoids an extra application at the call site.
-/
theorem stage3_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) (C : ℕ) :
    HasDiscrepancyAtLeast f C := by
  exact (stage3_forall_hasDiscrepancyAtLeast (f := f) (hf := hf)) C

/-- Explicit-assumption specialization of `stage3OutOf_forall_hasDiscrepancyAtLeast` at `C`. -/
theorem stage3OutOf_hasDiscrepancyAtLeast (inst : Stage2Assumption) (f : ℕ → ℤ)
    (hf : IsSignSequence f) (C : ℕ) :
    HasDiscrepancyAtLeast f C := by
  exact (stage3OutOf_forall_hasDiscrepancyAtLeast (inst := inst) (f := f) (hf := hf)) C

end Tao2015

end MoltResearch
