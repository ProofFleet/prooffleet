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

/-- The single non-verified assumption of Track C (Stage 2 of Tao 2015), in existential
parameter form.

This is the Erdős discrepancy statement in the reduced shape Stage 2 packages: for every sign
sequence there **exist** parameters `d, m` (with `1 ≤ d`) whose bundled offset discrepancy family
is unbounded.

Design note (important): the parameters must be quantified *existentially*, with `d` depending on
`f`. An earlier version of this stub hard-wired `d = 1`, `m = 0`, asserting that every ±1 sequence
has unbounded plain partial sums — which is refutable in-system (the alternating sequence has
partial sums in `{-1, 0}`), making the axiom environment inconsistent and every downstream
conditional theorem vacuous.

Downstream developments are expected to replace this axiom by providing a verified
`Stage2Assumption` instance.
-/
axiom stage2Stub_exists_params_one_le_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ Tao2015.UnboundedDiscOffset f d m

/-- The step size `d` chosen (noncomputably) from the Stage-2 stub assumption. -/
noncomputable def stage2Stub_d (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  (stage2Stub_exists_params_one_le_unboundedDiscOffset (f := f) (hf := hf)).choose

/-- The offset parameter `m` chosen (noncomputably) from the Stage-2 stub assumption. -/
noncomputable def stage2Stub_m (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  (stage2Stub_exists_params_one_le_unboundedDiscOffset (f := f) (hf := hf)).choose_spec.choose

/-- The chosen stub step size satisfies `1 ≤ d`. -/
theorem stage2Stub_one_le_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    1 ≤ stage2Stub_d (f := f) (hf := hf) :=
  (stage2Stub_exists_params_one_le_unboundedDiscOffset (f := f)
      (hf := hf)).choose_spec.choose_spec.1

/-- The chosen stub step size is positive (the form `ReductionOutput.ofShift` expects). -/
theorem stage2Stub_d_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage2Stub_d (f := f) (hf := hf) > 0 :=
  lt_of_lt_of_le Nat.zero_lt_one (stage2Stub_one_le_d (f := f) (hf := hf))

/-- Parameter form of the Stage-2 stub assumption, at the chosen parameters
`stage2Stub_d` / `stage2Stub_m`.

This keeps the name used by the derived normal-form wrappers in
`TrackCStage2StubProof.lean`; it is now a theorem (about the chosen parameters) rather than the
axiom itself.
-/
theorem stage2Stub_unboundedDiscOffset_params (f : ℕ → ℤ) (hf : IsSignSequence f) :
    Tao2015.UnboundedDiscOffset f (stage2Stub_d (f := f) (hf := hf))
      (stage2Stub_m (f := f) (hf := hf)) :=
  (stage2Stub_exists_params_one_le_unboundedDiscOffset (f := f)
      (hf := hf)).choose_spec.choose_spec.2

/-- The canonical Stage-1 reduction used by the default Stage-2 conjecture stub, wired at the
chosen parameters `stage2Stub_d` / `stage2Stub_m`.

We keep this as a named definition so later refactors can change the default Stage-1 wiring
without touching the `Stage2Assumption` API.
-/
noncomputable def stage2Stub_out1 (f : ℕ → ℤ) (hf : IsSignSequence f) : Tao2015.ReductionOutput f :=
  Tao2015.ReductionOutput.ofShift (f := f) (hf := hf)
    (d := stage2Stub_d (f := f) (hf := hf))
    (m := stage2Stub_m (f := f) (hf := hf))
    (hd := stage2Stub_d_pos (f := f) (hf := hf))

/-- Out1-form of the Stage-2 stub assumption.

This is `stage2Stub_unboundedDiscOffset_params` rewritten to mention the projections `out1.d` and
`out1.m` of the canonical stub reduction `stage2Stub_out1`.
-/
theorem stage2Stub_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    Tao2015.UnboundedDiscOffset f
      (stage2Stub_out1 (f := f) (hf := hf)).d
      (stage2Stub_out1 (f := f) (hf := hf)).m := by
  simpa [stage2Stub_out1, Tao2015.ReductionOutput.ofShift] using
    (stage2Stub_unboundedDiscOffset_params (f := f) (hf := hf))

/-!
## Derived normal forms (moved)

The proved normal-form wrappers (fixed-step unboundedness, boundedness-negation normal forms, and
witness-form corollaries at the chosen stub parameters `stage2Stub_d` / `stage2Stub_m`) live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2StubProof`.

We keep `TrackCStage2Stub` minimal so hard-gate consumers only compile the axiom stub and the
construction of `stage2Out`.
-/

/-- Default (Conjectures-only) Stage-2 output produced by the stub assumption.

This is the concrete `Stage2Output` used by the low-priority default instance
`instStage2Assumption`.

It is intentionally factored out as a named definition so downstream refactors can adjust the
default Stage-1 wiring without rewriting the typeclass instance boilerplate.
-/
noncomputable def stage2Stub_out (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage2Output f := by
  classical
  let out1 := stage2Stub_out1 (f := f) (hf := hf)
  have hunbOffset : Tao2015.UnboundedDiscOffset f out1.d out1.m := by
    -- TODO (real Tao2015 Stage 2): replace the axiom stub `stage2Stub_unboundedDiscOffset_params`
    -- (currently accessed via `stage2Stub_unboundedDiscOffset`) with the first verified reduction step.
    simpa [out1] using (stage2Stub_unboundedDiscOffset (f := f) (hf := hf))
  exact Stage2Output.ofUnboundedDiscOffset (f := f) out1 hunbOffset

instance (priority := 10000) instStage2Assumption : Stage2Assumption where
  stage2_nonempty f hf := by
    exact ⟨stage2Stub_out (f := f) (hf := hf)⟩

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

/-- `stage2OutWith` agrees definitionally with the explicit-assumption Stage-2 output `stage2OutOf`.

We register this as a simp lemma so downstream developments can rewrite away `stage2OutWith`
without importing any additional Stage-2 convenience layers.
-/
@[simp] theorem stage2OutWith_eq_stage2OutOf (inst : Stage2Assumption) (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    stage2OutWith inst (f := f) (hf := hf) = stage2OutOf inst (f := f) (hf := hf) := by
  classical
  rfl

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
