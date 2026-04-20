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
noncomputable def stage3 (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage3Output f :=
  Stage3Output.ofStage2Output (f := f) (stage2Out (f := f) (hf := hf))

/-- Deterministic name for the Stage-3 output (useful to keep later statements readable). -/
noncomputable abbrev stage3Out (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage3Output f :=
  stage3 (f := f) (hf := hf)

/-!
## Definitional rewrites

These simp lemmas reduce rewriting noise when shuttling statements between Stage 2 and Stage 3.
They are intentionally kept in the minimal entry-point module.
-/

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

/-- Convenience lemma: the Stage-3 reduced sequence is a sign sequence.

This is a tiny wrapper around the Stage-2 core projection lemma `Stage2Output.hg`.
-/
theorem stage3Out_hg (f : ℕ → ℤ) (hf : IsSignSequence f) :
    IsSignSequence (stage3Out (f := f) (hf := hf)).g := by
  simpa using (Stage2Output.hg (out := (stage3Out (f := f) (hf := hf)).out2))

/-- Convenience lemma: the Stage-3 reduced step size is at least `1`.

This is a tiny wrapper around the Stage-2 projection lemma `Stage2Output.one_le_d`.
-/
theorem stage3_one_le_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    1 ≤ (stage3Out (f := f) (hf := hf)).d := by
  simpa using (Stage2Output.one_le_d (out := (stage3Out (f := f) (hf := hf)).out2))

/-- Convenience lemma: the Stage-3 reduced step size is positive.

This is sometimes the right normal form when downstream stages want to treat `d` as a denominator
(or simply avoid rewriting `1 ≤ d`).
-/
theorem stage3Out_d_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).d > 0 := by
  -- Delegate to the Stage-2 core projection lemma (Stage 3 carries a Stage-2 output).
  simp

/-- Convenience lemma: the Stage-3 reduced step size is nonzero.

This is sometimes the right normal form for downstream stages that treat `d` as a denominator (or
simply want to avoid rewriting strict inequalities).
-/
theorem stage3Out_d_ne_zero (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).d ≠ 0 := by
  -- Delegate to the Stage-2 core lemma; avoids re-proving arithmetic facts.
  simpa using (Stage2Output.d_ne_zero (out := (stage3Out (f := f) (hf := hf)).out2))

-- Note: the simp lemma `stage3Out_out2` is enough to rewrite projections like
-- `(stage3Out ...).out2.d` to `(stage2Out ...).d`, but we also provide `[simp]` lemmas for the
-- common projections `.d/.m/.g` so consumers can rewrite without reaching through `.out2`.

/-- Consumer-facing shortcut: the Stage-3 pipeline closes the core goal `¬ BoundedDiscrepancy f`.

We keep this lemma in the hard-gate minimal module so `ErdosDiscrepancy.lean` can remain minimal.
-/
theorem stage3_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  let out := stage3Out (f := f) (hf := hf)
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

/-- Consumer-facing witness form: Stage 3 yields explicit discrepancy witnesses.

Normal form:
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

/-- Variant of `stage3_forall_exists_discrepancy_gt` with a positive-length witness `n > 0`.

Normal form:
`∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ discrepancy f d n > C`.

Implementation note: we use the core witness-normal form lemma
`HasDiscrepancyAtLeast_iff_exists_discrepancy_ge_one_witness_pos` to avoid re-proving that
`discrepancy f d 0 = 0`.
-/
theorem stage3_forall_exists_discrepancy_gt_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ discrepancy f d n > C := by
  intro C
  have hC : HasDiscrepancyAtLeast f C :=
    (stage3_forall_hasDiscrepancyAtLeast (f := f) (hf := hf)) C
  rcases
      (HasDiscrepancyAtLeast_iff_exists_discrepancy_ge_one_witness_pos (f := f) (C := C)).1 hC with
    ⟨d, n, hd, hn, hgt⟩
  refine ⟨d, n, ?_, hn, hgt⟩
  exact lt_of_lt_of_le Nat.zero_lt_one hd

/-- Specialization of `stage3_forall_hasDiscrepancyAtLeast` at a fixed threshold `C`.

This is a tiny convenience lemma: it avoids an extra application at the call site.
-/
theorem stage3_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) (C : ℕ) :
    HasDiscrepancyAtLeast f C := by
  exact (stage3_forall_hasDiscrepancyAtLeast (f := f) (hf := hf)) C

end Tao2015

end MoltResearch
