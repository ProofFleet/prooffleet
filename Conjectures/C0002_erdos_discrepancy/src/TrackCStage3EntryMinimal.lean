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
- `stage3_hasDiscrepancyAtLeast` : specialization at a fixed threshold `C`
- `stage3_not_exists_boundedDiscOffset` : stable boundedness-negation packaging of the
  Stage-2 offset-discrepancy unboundedness witness

All additional projection/rewrite lemmas and witness-form corollaries live in
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

/-- Convenience lemma: the Stage-3 reduced step size is at least `1`.

This is a tiny wrapper around the Stage-2 projection lemma `Stage2Output.one_le_d`.
-/
theorem stage3_one_le_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    1 ≤ (stage3Out (f := f) (hf := hf)).d := by
  simpa using (Stage2Output.one_le_d (out := (stage3Out (f := f) (hf := hf)).out2))

/-- Convenience lemma: the Stage-3 reduced step size is positive.

This is a tiny corollary of `stage3_one_le_d`.
-/
theorem stage3Out_d_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).d > 0 := by
  exact lt_of_lt_of_le Nat.zero_lt_one (stage3_one_le_d (f := f) (hf := hf))

/-- Convenience lemma: the Stage-3 reduced step size is nonzero.

This is a tiny corollary of `stage3Out_d_pos`.
-/
theorem stage3Out_d_ne_zero (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).d ≠ 0 := by
  exact Nat.ne_of_gt (stage3Out_d_pos (f := f) (hf := hf))

-- Note: the simp lemma `stage3Out_out2` is enough to rewrite projections like
-- `(stage3Out ...).out2.d` to `(stage2Out ...).d`, so we avoid duplicating simp lemmas for
-- `.d/.m/.g` here.


/-- Consumer-facing shortcut: the Stage-3 pipeline closes the core goal `¬ BoundedDiscrepancy f`.

We keep this lemma in the hard-gate minimal module so `ErdosDiscrepancy.lean` can remain minimal.
-/
theorem stage3_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  exact (stage3Out (f := f) (hf := hf)).notBounded

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
  simpa using
    (Stage3Output.not_exists_boundedDiscOffset (f := f) (stage3Out (f := f) (hf := hf)))

/-- Stable witness packaging of the Stage-3 offset-discrepancy unboundedness statement.

Normal form:
`UnboundedDiscOffset f (stage3Out ...).d (stage3Out ...).m`.

This is a thin wrapper around `Stage3Output.unboundedDiscOffset`.
-/
theorem stage3_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    UnboundedDiscOffset f
      (stage3Out (f := f) (hf := hf)).d
      (stage3Out (f := f) (hf := hf)).m := by
  exact (stage3Out (f := f) (hf := hf)).unboundedDiscOffset (f := f)

/-- Existential packaging: Stage 3 yields concrete parameters `d, m` with `1 ≤ d` such that the
bundled offset discrepancy family `discOffset f d m` is unbounded.

This is a minimal-entry convenience lemma for downstream stages that prefer not to mention the
record fields of `stage3Out`.
-/
theorem stage3_exists_params_one_le_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ UnboundedDiscOffset f d m := by
  refine ⟨(stage3Out (f := f) (hf := hf)).d, (stage3Out (f := f) (hf := hf)).m, ?_, ?_⟩
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
  refine ⟨(stage3Out (f := f) (hf := hf)).d, (stage3Out (f := f) (hf := hf)).m, ?_, ?_⟩
  · exact stage3_one_le_d (f := f) (hf := hf)
  · simpa using stage3_not_exists_boundedDiscOffset (f := f) (hf := hf)

/-- Track-C pipeline witness: Stage 3 yields unbounded discrepancy along the reduced sequence,
phrased using the verified core predicate `MoltResearch.UnboundedDiscrepancyAlong`.

This is a thin wrapper around `Stage3Output.unboundedDiscrepancyAlong_core`.
-/
theorem stage3_unboundedDiscrepancyAlong_core (f : ℕ → ℤ) (hf : IsSignSequence f) :
    MoltResearch.UnboundedDiscrepancyAlong
      (stage3Out (f := f) (hf := hf)).g
      (stage3Out (f := f) (hf := hf)).d := by
  simpa using (stage3Out (f := f) (hf := hf)).unboundedDiscrepancyAlong_core (f := f)

/-- Consumer-facing shortcut: the Stage-3 pipeline yields the usual surface statement
`∀ C, HasDiscrepancyAtLeast f C`.

This is a thin wrapper around `Stage3Output.forall_hasDiscrepancyAtLeast`.
-/
theorem stage3_forall_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  exact Stage3Output.forall_hasDiscrepancyAtLeast (f := f) (stage3Out (f := f) (hf := hf))

/-- Specialization of `stage3_forall_hasDiscrepancyAtLeast` at a fixed threshold `C`.

This is a tiny convenience lemma: it avoids an extra application at the call site.
-/
theorem stage3_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) (C : ℕ) :
    HasDiscrepancyAtLeast f C := by
  exact (stage3_forall_hasDiscrepancyAtLeast (f := f) (hf := hf)) C

end Tao2015

end MoltResearch
