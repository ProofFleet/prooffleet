import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Boundary

/-!
# Track C: Stage 2 conjecture stub (Tao 2015 plane)

This file is **Conjectures-only** glue.

It isolates the single non-verified assumption of Track C: the Stage-2 boundary axiom.

Design goal: downstream hard-gate consumers (Stage 3, `ErdosDiscrepancy.lean`) should only need to
import this stub to access `stage2Out`, avoiding compilation of additional Stage-2 convenience
lemmas.
-/

namespace MoltResearch

namespace Tao2015

/-- Typeclass packaging of the Stage-2 conjecture assumption.

We package the conjecture as a `Prop` (existence of a Stage-2 output) rather than committing to a
specific function. The definitional output `stage2`/`stage2Out` is then selected noncomputably via
`Classical.choice`.

This lets downstream code replace the axiom stub by providing a local instance (e.g. derived from a
verified Stage-2 construction).
-/
class Stage2Assumption : Prop where
  /-- Stage 2 of Tao 2015: given a sign sequence `f`, a Stage-2 output exists consisting of a
  Stage-1 reduction output and an unbounded fixed-step discrepancy witness along the reduced
  sequence. -/
  stage2_nonempty (f : ℕ → ℤ) (hf : IsSignSequence f) : Nonempty (Stage2Output f)

namespace Stage2Assumption

/-- Build a `Stage2Assumption` instance from an explicit Stage-2 construction function.

This is a small convenience constructor for downstream developments: a verified Stage-2 algorithm
(or theorem) usually produces a concrete `Stage2Output f`, and this lemma packages it into the
typeclass form expected by the Track-C pipeline.
-/
def ofStage2 (stage2 : ∀ f : ℕ → ℤ, IsSignSequence f → Stage2Output f) : Stage2Assumption :=
  ⟨fun f hf => ⟨stage2 f hf⟩⟩

end Stage2Assumption

/-- Non-typeclass entry point: run Stage 2 using an explicit `Stage2Assumption` proof.

This is useful in downstream developments that want to avoid `letI` / typeclass search and pass a
verified Stage-2 assumption explicitly.
-/
noncomputable def stage2Of (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    Stage2Output f := by
  classical
  -- Use the explicit assumption directly, avoiding typeclass search.
  exact Classical.choice (inst.stage2_nonempty (f := f) (hf := hf))

/-- Abbreviation wrapper for `stage2Of` (mirrors `stage2Out`). -/
noncomputable abbrev stage2OutOf (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    Stage2Output f :=
  stage2Of inst (f := f) (hf := hf)

/- Default (Conjectures-only) Stage-2 assumption instance.

This replaces the old `axiom instStage2Assumption` with an explicit construction of a
`Stage2Output`, leaving **exactly one** axiom stub for the mathematical core.

This is the intended “first real problem progress” milestone:
- we now *actually* run a concrete Stage‑1 reduction (`ReductionOutput.ofShift`), and
- we isolate the remaining unverified content to the single Stage‑2 unboundedness witness.

Design note: we register this instance at very low priority so downstream developments can provide
(and override with) a verified `Stage2Assumption` instance.
-/

/-- The canonical Stage-1 reduction used by the default Stage-2 conjecture stub.

We keep this as a named definition so later refactors can change the default Stage-1 wiring
without touching the `Stage2Assumption` API.
-/
noncomputable def stage2Stub_out1 (f : ℕ → ℤ) (hf : IsSignSequence f) : Tao2015.ReductionOutput f :=
  Tao2015.ReductionOutput.ofShift (f := f) (hf := hf) (d := 1) (m := 0) (hd := Nat.succ_pos 0)

/-- The single non-verified assumption of Track C (Stage 2 of Tao 2015).

This is stated in terms of the canonical Stage-1 reduction used by `stage2Stub_out1`.
Downstream developments are expected to replace this axiom by providing a verified
`Stage2Assumption` instance.
-/
axiom stage2Stub_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    let out1 := stage2Stub_out1 (f := f) (hf := hf)
    Tao2015.UnboundedDiscOffset f out1.d out1.m

/-- Parameter-normal form of the Stage-2 stub assumption.

Since `stage2Stub_out1` is wired with the deterministic parameters `d = 1` and `m = 0`, the axiom
`stage2Stub_unboundedDiscOffset` immediately implies unboundedness of `discOffset f 1 0`.

This lemma is intentionally tiny: it exists to reduce `let`-binder and projection noise at call
sites.
-/
theorem stage2Stub_unboundedDiscOffset_params (f : ℕ → ℤ) (hf : IsSignSequence f) :
    Tao2015.UnboundedDiscOffset f 1 0 := by
  simpa [stage2Stub_out1] using (stage2Stub_unboundedDiscOffset (f := f) (hf := hf))

/-- Derived form of the Stage-2 stub assumption: unbounded discrepancy along the reduced sequence.

We keep the axiom itself in the bundled offset normal form (`UnboundedDiscOffset`) because it is
stable under changes to the internal definition of the reduced sequence `out1.g`.
-/
theorem stage2Stub_unbounded (f : ℕ → ℤ) (hf : IsSignSequence f) :
    let out1 := stage2Stub_out1 (f := f) (hf := hf)
    Tao2015.UnboundedDiscrepancyAlong out1.g out1.d := by
  classical
  let out1 := stage2Stub_out1 (f := f) (hf := hf)
  have hunbOffset : Tao2015.UnboundedDiscOffset f out1.d out1.m := by
    simpa [out1] using (stage2Stub_unboundedDiscOffset (f := f) (hf := hf))
  have hunbAlong : Tao2015.UnboundedDiscrepancyAlong out1.g out1.d := by
    exact ((out1.unboundedDiscrepancyAlong_iff_unboundedDiscOffset (f := f))).2 hunbOffset
  simpa [out1] using hunbAlong

instance instStage2Assumption : Stage2Assumption where
  stage2_nonempty f hf := by
    classical
    let out1 := stage2Stub_out1 (f := f) (hf := hf)
    refine ⟨{ out1 := out1
              unbounded := ?_ }⟩
    -- TODO (real Tao2015 Stage 2): replace `stage2Stub_unboundedDiscOffset` with the first verified reduction step.
    simpa [out1] using (stage2Stub_unbounded (f := f) (hf := hf))

attribute [instance 10] instStage2Assumption

/-- **Conjecture stub:** Stage 2 of Tao 2015.

Given a sign sequence `f`, choose a Stage-2 output using `Classical.choice` from the existence
statement packaged by `Stage2Assumption`.
-/
noncomputable def stage2 (f : ℕ → ℤ) (hf : IsSignSequence f) [Stage2Assumption] : Stage2Output f :=
  Classical.choice (Stage2Assumption.stage2_nonempty (f := f) (hf := hf))

/-- Deterministic name for the Stage-2 output (useful to keep later statements readable).

Note: the implicit `[Stage2Assumption]` argument is intentionally explicit here so that downstream
developments can override the default conjecture instance by providing a local verified instance.
-/
noncomputable abbrev stage2Out (f : ℕ → ℤ) (hf : IsSignSequence f) [Stage2Assumption] :
    Stage2Output f :=
  stage2 (f := f) (hf := hf)

/-!
## Definitional rewrites

These tiny lemmas let downstream developments freely switch between the explicit-assumption API
(`stage2OutOf`) and the typeclass-based API (`stage2Out`) by introducing a local instance.

They are deliberately kept in the Stage-2 stub so later stages can import them without pulling in
additional convenience layers.
-/

/-- Explicit-assumption wrapper around `stage2Out`.

This returns the typeclass-based output `stage2Out` but with the instance `inst` installed locally.
It lets downstream code use lemmas stated in terms of `stage2Out` without writing `letI` at the call
site.
-/
noncomputable abbrev stage2OutWith (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    Stage2Output f :=
  (by
    classical
    letI : Stage2Assumption := inst
    exact stage2Out (f := f) (hf := hf))

/-- `stage2OutOf` agrees definitionally with `stage2OutWith`. -/
theorem stage2OutOf_eq_stage2OutWith (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage2OutOf inst (f := f) (hf := hf) = stage2OutWith inst (f := f) (hf := hf) := by
  classical
  rfl

/-- If we register an explicit assumption `inst` as the local typeclass instance, then the
explicit Stage-2 output `stage2OutOf inst` agrees definitionally with the typeclass-based output
`stage2Out`.

This is useful when consumer code wants to pass `inst` explicitly but also reuse lemmas phrased in
terms of `stage2Out`.
-/
theorem stage2OutOf_eq_stage2Out (inst : Stage2Assumption) (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage2OutOf inst (f := f) (hf := hf) =
      (by
        classical
        letI : Stage2Assumption := inst
        exact stage2Out (f := f) (hf := hf)) := by
  classical
  rfl

end Tao2015

end MoltResearch
