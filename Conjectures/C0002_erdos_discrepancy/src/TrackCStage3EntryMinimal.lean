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

All additional witness-form corollaries live in
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

/-- The Stage-2 output stored inside `stage3Out` is definitionally the Stage-2 output produced by
Stage 2.

This lemma is tiny but useful for rewriting when shuttling statements between Stage 2 and Stage 3.

We keep it in the hard-gate minimal module so `ErdosDiscrepancy.lean` can stay minimal.
-/
@[simp] theorem stage3Out_out2 (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).out2 = stage2Out (f := f) (hf := hf) := by
  rfl

/-- The Stage-1 reduction output stored inside `stage3Out` is definitionally the Stage-1 reduction
output produced by Stage 2.

This lemma is tiny but useful for rewriting when shuttling statements between Stage 1 and Stage 3.

We keep it in the hard-gate minimal module so `ErdosDiscrepancy.lean` can stay minimal.
-/
@[simp] theorem stage3Out_out1 (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).out1 = (stage2Out (f := f) (hf := hf)).out1 := by
  rfl

/-- Deterministic Stage-2 parameter projections for `stage3Out`.

These simp lemmas reduce rewriting noise when shuttling statements between Stage 2 and Stage 3.
-/
@[simp] theorem stage3Out_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).out2.d = (stage2Out (f := f) (hf := hf)).d := by
  rfl

@[simp] theorem stage3Out_m (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).out2.m = (stage2Out (f := f) (hf := hf)).m := by
  rfl

@[simp] theorem stage3Out_g (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage3Out (f := f) (hf := hf)).out2.g = (stage2Out (f := f) (hf := hf)).g := by
  rfl


/-- Track C pipeline witness: Stage 3 yields unbounded fixed-step discrepancy along the reduced
sequence, expressed using the verified core predicate `MoltResearch.UnboundedDiscrepancyAlong`.

This lemma is a small convenience wrapper around the bridge equivalence
`Tao2015.unboundedDiscrepancyAlong_iff_core`.
-/
theorem stage3_unboundedDiscrepancyAlong_core (f : ℕ → ℤ) (hf : IsSignSequence f) :
    MoltResearch.UnboundedDiscrepancyAlong
      (stage3Out (f := f) (hf := hf)).out1.g
      (stage3Out (f := f) (hf := hf)).out1.d := by
  simpa using (stage3Out (f := f) (hf := hf)).unboundedDiscrepancyAlong_core

/-- Track C pipeline witness: Stage 3 yields an unbounded bundled offset discrepancy family
`discOffset f d m` at the deterministic Stage-2 parameters stored in `stage3Out`.

This is a thin wrapper around the proved Stage-2 core lemma `Stage2Output.unboundedDiscOffset`.
-/
theorem stage3_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    UnboundedDiscOffset f
      (stage3Out (f := f) (hf := hf)).out2.d
      (stage3Out (f := f) (hf := hf)).out2.m := by
  simpa using (stage3Out (f := f) (hf := hf)).out2.unboundedDiscOffset (f := f)

/-- Consumer-facing normal form: there is no bundled offset-discrepancy bound at the deterministic
Stage-2 parameters stored in `stage3Out`.

This is the stable boundedness-negation normal form of `stage3_unboundedDiscOffset`.
-/
theorem stage3_not_exists_boundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ,
      BoundedDiscOffset f
        (stage3Out (f := f) (hf := hf)).out2.d
        (stage3Out (f := f) (hf := hf)).out2.m B := by
  exact (stage3Out (f := f) (hf := hf)).not_exists_boundedDiscOffset (f := f)

/-- Consumer-facing shortcut: the Stage-3 pipeline closes the core goal `¬ BoundedDiscrepancy f`.

We keep this lemma in the hard-gate minimal module so `ErdosDiscrepancy.lean` can remain minimal.
-/
theorem stage3_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  exact (stage3Out (f := f) (hf := hf)).notBounded

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

/-- Existential packaging: Stage 3 yields concrete parameters `d, m` with `d > 0` such that there
is no bound `B` with `BoundedDiscOffset f d m B`.

This is the stable boundedness-negation normal form packaged with explicit parameters.
-/
theorem stage3_exists_params_not_exists_boundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ ¬ ∃ B : ℕ, BoundedDiscOffset f d m B := by
  refine ⟨(stage3Out (f := f) (hf := hf)).out2.d,
    (stage3Out (f := f) (hf := hf)).out2.m,
    (stage3Out (f := f) (hf := hf)).out2.hd, ?_⟩
  simpa using (stage3_not_exists_boundedDiscOffset (f := f) (hf := hf))

/-- Existential packaging: Stage 3 yields concrete parameters `d, m` with `d > 0` such that the
bundled offset discrepancy family `discOffset f d m` is unbounded.

This is a tiny wrapper around `stage3_unboundedDiscOffset`.
-/
theorem stage3_exists_params_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, d > 0 ∧ UnboundedDiscOffset f d m := by
  refine ⟨(stage3Out (f := f) (hf := hf)).out2.d,
    (stage3Out (f := f) (hf := hf)).out2.m,
    (stage3Out (f := f) (hf := hf)).out2.hd, ?_⟩
  simpa using (stage3Out (f := f) (hf := hf)).unboundedDiscOffset (f := f)

/-- Existential packaging: Stage 3 yields concrete parameters `d, m` with `1 ≤ d` such that the
bundled offset discrepancy family `discOffset f d m` is unbounded.

This is a small convenience variant of `stage3_exists_params_unboundedDiscOffset`: many downstream
stages prefer the side condition `1 ≤ d` rather than `d > 0`.
-/
theorem stage3_exists_params_one_le_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ UnboundedDiscOffset f d m := by
  refine ⟨(stage3Out (f := f) (hf := hf)).out2.d,
    (stage3Out (f := f) (hf := hf)).out2.m,
    (stage3Out (f := f) (hf := hf)).out2.one_le_d (f := f), ?_⟩
  simpa using (stage3Out (f := f) (hf := hf)).unboundedDiscOffset (f := f)

end Tao2015

end MoltResearch
