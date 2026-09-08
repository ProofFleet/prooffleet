import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Boundary

/-!
# Track C: Stage 2 assumption interface (Tao 2015 plane)

This file is **Conjectures-only** glue. The historical module name is retained so existing
consumers keep a stable import path, but the former Stage-2 axiom and default instance have been
retired. Consumers of this conditional pipeline must now provide a `Stage2Assumption` explicitly.
-/

namespace MoltResearch

namespace Tao2015

/-- Typeclass packaging of the conditional Stage-2 interface.

We package the input as a `Prop` (existence of a Stage-2 output) rather than committing to a
specific function. The definitional output `stage2`/`stage2Out` is then selected noncomputably via
`Classical.choice`.
-/
class Stage2Assumption : Prop where
  /-- Given a sign sequence `f`, a Stage-2 output exists consisting of a Stage-1 reduction output
  and an unbounded fixed-step discrepancy witness along the reduced sequence. -/
  stage2_nonempty (f : ℕ → ℤ) (hf : IsSignSequence f) : Nonempty (Stage2Output f)

namespace Stage2Assumption

/-- Build a `Stage2Assumption` from an explicit Stage-2 construction function. -/
def ofStage2 (stage2 : ∀ f : ℕ → ℤ, IsSignSequence f → Stage2Output f) : Stage2Assumption :=
  ⟨fun f hf => ⟨stage2 f hf⟩⟩

end Stage2Assumption

/-- Run Stage 2 using an explicit `Stage2Assumption` proof. -/
noncomputable def stage2Of (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    Stage2Output f := by
  classical
  exact Classical.choice (inst.stage2_nonempty (f := f) (hf := hf))

/-- Abbreviation wrapper for `stage2Of` (mirrors `stage2Out`). -/
noncomputable abbrev stage2OutOf (inst : Stage2Assumption) (f : ℕ → ℤ)
    (hf : IsSignSequence f) : Stage2Output f :=
  stage2Of inst (f := f) (hf := hf)

/-- Conditional Stage-2 entry point selected from a caller-supplied assumption. -/
noncomputable def stage2 (f : ℕ → ℤ) (hf : IsSignSequence f) [Stage2Assumption] :
    Stage2Output f :=
  Classical.choice (Stage2Assumption.stage2_nonempty (f := f) (hf := hf))

/-- Deterministic name for the conditional Stage-2 output. -/
noncomputable abbrev stage2Out (f : ℕ → ℤ) (hf : IsSignSequence f) [Stage2Assumption] :
    Stage2Output f :=
  stage2 (f := f) (hf := hf)

/-- Use an explicit assumption as the local typeclass input to `stage2Out`. -/
noncomputable abbrev stage2OutWith (inst : Stage2Assumption) (f : ℕ → ℤ)
    (hf : IsSignSequence f) : Stage2Output f :=
  (by
    classical
    letI : Stage2Assumption := inst
    exact stage2Out (f := f) (hf := hf))

/-- `stage2OutWith` agrees definitionally with `stage2OutOf`. -/
@[simp] theorem stage2OutWith_eq_stage2OutOf (inst : Stage2Assumption) (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    stage2OutWith inst (f := f) (hf := hf) = stage2OutOf inst (f := f) (hf := hf) := by
  classical
  rfl

/-- `stage2OutOf` agrees definitionally with `stage2OutWith`. -/
theorem stage2OutOf_eq_stage2OutWith (inst : Stage2Assumption) (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    stage2OutOf inst (f := f) (hf := hf) = stage2OutWith inst (f := f) (hf := hf) := by
  classical
  rfl

/-- Installing `inst` locally makes `stage2OutOf inst` definitionally equal to `stage2Out`. -/
theorem stage2OutOf_eq_stage2Out (inst : Stage2Assumption) (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    stage2OutOf inst (f := f) (hf := hf) =
      (by
        classical
        letI : Stage2Assumption := inst
        exact stage2Out (f := f) (hf := hf)) := by
  classical
  rfl

end Tao2015

end MoltResearch
