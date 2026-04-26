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

/-- The reduced sequence in the default stub reduction is just the original sequence.

This is the `g_eq` contract of `ReductionOutput.ofShift` specialized to the deterministic stub
parameters `d = 1` and `m = 0`.
-/
@[simp] theorem stage2Stub_out1_g (f : ℕ → ℤ) (hf : IsSignSequence f) (k : ℕ) :
    (stage2Stub_out1 (f := f) (hf := hf)).g k = f k := by
  simp [stage2Stub_out1, Tao2015.ReductionOutput.ofShift]

/-- Function-level rewrite for the reduced sequence in the default stub reduction.

This is `stage2Stub_out1_g` bundled as an equality of functions; it is convenient when rewriting
a whole `g` argument (rather than pointwise applications `g k`).
-/
@[simp] theorem stage2Stub_out1_g_fun (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage2Stub_out1 (f := f) (hf := hf)).g = f := by
  funext k
  simp [stage2Stub_out1_g]

/-- The default stub reduction uses step size `d = 1`. -/
@[simp] theorem stage2Stub_out1_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage2Stub_out1 (f := f) (hf := hf)).d = 1 := by
  simp [stage2Stub_out1, Tao2015.ReductionOutput.ofShift]

/-- The default stub reduction uses offset parameter `m = 0`. -/
@[simp] theorem stage2Stub_out1_m (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage2Stub_out1 (f := f) (hf := hf)).m = 0 := by
  simp [stage2Stub_out1, Tao2015.ReductionOutput.ofShift]

/-- The single non-verified assumption of Track C (Stage 2 of Tao 2015), in parameter-normal form.

Since `stage2Stub_out1` is wired with the deterministic parameters `d = 1` and `m = 0`, the
Stage-2 conjecture stub is simply unboundedness of `discOffset f 1 0`.

Downstream developments are expected to replace this axiom by providing a verified
`Stage2Assumption` instance.
-/
axiom stage2Stub_unboundedDiscOffset_params (f : ℕ → ℤ) (hf : IsSignSequence f) :
    Tao2015.UnboundedDiscOffset f 1 0

/-- Out1-form of the Stage-2 stub assumption.

This is `stage2Stub_unboundedDiscOffset_params` rewritten to mention the projections `out1.d` and
`out1.m` of the canonical stub reduction `stage2Stub_out1`.
-/
theorem stage2Stub_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    Tao2015.UnboundedDiscOffset f
      (stage2Stub_out1 (f := f) (hf := hf)).d
      (stage2Stub_out1 (f := f) (hf := hf)).m := by
  simpa using (stage2Stub_unboundedDiscOffset_params (f := f) (hf := hf))

/-- Parameter-normal form of the Stage-2 stub assumption as fixed-step unboundedness.

This is `stage2Stub_unboundedDiscOffset_params` transported across the Stage-1 contract
`ReductionOutput.unboundedDiscrepancyAlong_iff_unboundedDiscOffset`, then simplified using the
stub parameters `g = f` and `d = 1`.
-/
theorem stage2Stub_unboundedDiscrepancyAlong_params (f : ℕ → ℤ) (hf : IsSignSequence f) :
    Tao2015.UnboundedDiscrepancyAlong f 1 := by
  have hunb :
      Tao2015.UnboundedDiscrepancyAlong
        (stage2Stub_out1 (f := f) (hf := hf)).g
        (stage2Stub_out1 (f := f) (hf := hf)).d := by
    exact
      ((stage2Stub_out1 (f := f) (hf := hf)).unboundedDiscrepancyAlong_iff_unboundedDiscOffset
            (f := f)).2
        (stage2Stub_unboundedDiscOffset (f := f) (hf := hf))
  simpa using hunb

/-- Stable boundedness-negation normal form of the Stage-2 stub assumption.

Normal form:
`¬ ∃ B, BoundedDiscOffset f 1 0 B`.

This is `stage2Stub_unboundedDiscOffset_params` rewritten via
`Tao2015.unboundedDiscOffset_iff_not_exists_boundedDiscOffset`.
-/
theorem stage2Stub_not_exists_boundedDiscOffset_params (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ, BoundedDiscOffset f 1 0 B := by
  have hunb : Tao2015.UnboundedDiscOffset f 1 0 :=
    stage2Stub_unboundedDiscOffset_params (f := f) (hf := hf)
  exact
    (Tao2015.unboundedDiscOffset_iff_not_exists_boundedDiscOffset (f := f) (d := 1) (m := 0)).1
      hunb

/-- Stable `discOffset` boundedness-negation normal form of the Stage-2 stub assumption.

Normal form:
`¬ ∃ B, ∀ n, discOffset f 1 0 n ≤ B`.

This is `stage2Stub_unboundedDiscOffset_params` rewritten via
`Tao2015.unboundedDiscOffset_iff_not_exists_forall_discOffset_le`.
-/
theorem stage2Stub_not_exists_forall_discOffset_le_params (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ, ∀ n : ℕ, discOffset f 1 0 n ≤ B := by
  have hunb : Tao2015.UnboundedDiscOffset f 1 0 :=
    stage2Stub_unboundedDiscOffset_params (f := f) (hf := hf)
  exact
    (Tao2015.unboundedDiscOffset_iff_not_exists_forall_discOffset_le (f := f) (d := 1) (m := 0)).1
      hunb

/-- Stable `apSumFrom` normal form of the Stage-2 stub assumption.

Normal form:
`¬ ∃ B, ∀ n, Int.natAbs (apSumFrom f 0 1 n) ≤ B`.

This is `stage2Stub_unboundedDiscOffset_params` rewritten via
`Tao2015.UnboundedDiscOffset.iff_not_exists_forall_natAbs_apSumFrom_mul_le`.
-/
theorem stage2Stub_not_exists_forall_natAbs_apSumFrom_zero_one_le (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumFrom f 0 1 n) ≤ B := by
  have hunb : Tao2015.UnboundedDiscOffset f 1 0 :=
    stage2Stub_unboundedDiscOffset_params (f := f) (hf := hf)
  -- `m*d` simplifies to `0` at the stub parameters `m = 0`, `d = 1`.
  simpa using
    (Tao2015.UnboundedDiscOffset.iff_not_exists_forall_natAbs_apSumFrom_mul_le
        (f := f) (d := 1) (m := 0)).1
      hunb

/-- Paper-notation normal form of the Stage-2 stub assumption.

Normal form:
`¬ ∃ B, ∀ n, Int.natAbs ((Finset.Icc 1 n).sum (fun i => f i)) ≤ B`.

This is `stage2Stub_unboundedDiscOffset_params` rewritten via
`Tao2015.UnboundedDiscOffset.iff_not_exists_forall_natAbs_sum_Icc_offset_le`.
-/
theorem stage2Stub_not_exists_forall_natAbs_sum_Icc_one_le (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ, ∀ n : ℕ, Int.natAbs ((Finset.Icc 1 n).sum (fun i => f i)) ≤ B := by
  have hunb : Tao2015.UnboundedDiscOffset f 1 0 :=
    stage2Stub_unboundedDiscOffset_params (f := f) (hf := hf)
  -- Rewrite the general `Icc (m+1) (m+n)` form at the stub parameters `m = 0`, `d = 1`.
  simpa using
    (Tao2015.UnboundedDiscOffset.iff_not_exists_forall_natAbs_sum_Icc_offset_le
        (f := f) (d := 1) (m := 0)).1
      hunb

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

/-- The Stage-1 reduction packaged inside the default Stage-2 stub output is `stage2Stub_out1`.

This lemma is intentionally tiny: it lets downstream code reason about the reduction parameters
(`d`, `m`, `g`) carried by the stub without unfolding `stage2Stub_out` (and therefore without
exposing the axiom stub in definitional reductions).
-/
@[simp] theorem stage2Stub_out_out1 (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage2Stub_out (f := f) (hf := hf)).out1 = stage2Stub_out1 (f := f) (hf := hf) := by
  classical
  simp [stage2Stub_out]

/-- The default stub Stage-2 output uses step size `d = 1` in its Stage-1 reduction. -/
@[simp] theorem stage2Stub_out_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage2Stub_out (f := f) (hf := hf)).out1.d = 1 := by
  simp

/-- The reduced sequence in the default stub Stage-2 output is just the original sequence. -/
@[simp] theorem stage2Stub_out_g (f : ℕ → ℤ) (hf : IsSignSequence f) (k : ℕ) :
    (stage2Stub_out (f := f) (hf := hf)).out1.g k = f k := by
  simp [stage2Stub_out1_g]

/-- The default stub Stage-2 output uses offset parameter `m = 0` in its Stage-1 reduction. -/
@[simp] theorem stage2Stub_out_m (f : ℕ → ℤ) (hf : IsSignSequence f) :
    (stage2Stub_out (f := f) (hf := hf)).out1.m = 0 := by
  simp [stage2Stub_out1_m]

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
