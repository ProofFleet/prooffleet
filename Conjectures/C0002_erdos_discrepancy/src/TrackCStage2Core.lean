import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Boundary

/-!
# Track C: Stage 2 core lemmas (Tao 2015 plane)

This file is intentionally tiny.

It contains the minimal proved lemmas about `Tao2015.Stage2Output` needed by later hard-gate stages
to close the global goal `¬ BoundedDiscrepancy f` and to expose the small Stage-2 API used by the
Stage-3 hard-gate entry point.

Additional arithmetic/rewrite helpers (e.g. reduced-sequence rewrite lemmas and tail-nucleus normal
forms) live in `Conjectures.C0002_erdos_discrepancy.src.TrackCStage2CoreExtras`.

The start index projection `out.start = out.m * out.d` is part of this core API (it is definitional,
but downstream stages often want a named projection to avoid repeating `out.m * out.d`).

The larger collection of witness-form wrappers lives in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Output`.
-/

namespace MoltResearch

namespace Tao2015

namespace Stage2Output

variable {f : ℕ → ℤ}

/-!
## Stage-2 minimal projections

These are small, proved projections off `Tao2015.Stage2Output` that downstream hard-gate stages use
frequently.
-/

/-- Convenience projection: the reduced step size. -/
@[simp] abbrev d (out : Stage2Output f) : ℕ := out.out1.d

/-- Convenience projection: the reduced sequence. -/
@[simp] abbrev g (out : Stage2Output f) : ℕ → ℤ := out.out1.g

/-- The reduced sequence packaged by Stage 2 is a sign sequence. -/
theorem hg (out : Stage2Output f) : IsSignSequence out.g := by
  simpa using out.out1.hg

/-- Convenience projection: the offset parameter bundled in Stage 1. -/
@[simp] abbrev m (out : Stage2Output f) : ℕ := out.out1.m

/-- Convenience projection: the affine-tail start index `m*d` bundled in Stage 1. -/
abbrev start (out : Stage2Output f) : ℕ := out.m * out.d

/-- Definitional rewrite: the affine-tail start index is `m*d`.

This lemma is intentionally tiny (and not a simp lemma): it exists mainly to reduce `dsimp` noise
in downstream arithmetic rewrites.
-/
theorem start_eq_m_mul_d (out : Stage2Output f) : out.start = out.m * out.d := by
  rfl

/-- The Stage-2 start index is a multiple of the Stage-2 step size. -/
theorem d_dvd_start (out : Stage2Output f) : out.d ∣ out.start := by
  refine ⟨out.m, ?_⟩
  simp [Stage2Output.start, Nat.mul_comm]

/-- The Stage-2 start index has remainder `0` modulo the Stage-2 step size.

This is often the most convenient normal form of `d_dvd_start`.
-/
theorem start_mod_d (out : Stage2Output f) : out.start % out.d = 0 := by
  exact Nat.mod_eq_zero_of_dvd out.d_dvd_start

/-- Convenience projection: positivity of the reduced step size. -/
@[simp] abbrev hd (out : Stage2Output f) : out.d > 0 := out.out1.hd

/-- Convenience lemma: the reduced step size is nonzero. -/
theorem d_ne_zero (out : Stage2Output f) : out.d ≠ 0 := by
  exact Nat.ne_of_gt out.hd

/-- Convenience lemma: the reduced step size is at least `1`. -/
theorem one_le_d (out : Stage2Output f) : 1 ≤ out.d := by
  simpa using (Nat.succ_le_iff).2 out.hd

/-- Stage 2 implies the reduced sequence is not bounded along its fixed step size. -/
theorem notBoundedReducedAlong (out : Stage2Output f) : ¬ BoundedDiscrepancyAlong out.g out.d := by
  exact
    (Tao2015.UnboundedDiscrepancyAlong.iff_not_boundedDiscrepancyAlong
      (g := out.g) (d := out.d)).1
      out.unbounded

/-!
## Stage-2 bridge back to the global statement
-/

/-- Consumer-facing form: Stage 2 implies global unbounded discrepancy for the original sequence.

This is the minimal “bridge back to the main theorem statement” lemma: it packages the fact that
Stage 2 gives unbounded discrepancy along the reduced sequence, and uses the Stage-1 contract
carried by `out.out1` to conclude `¬ BoundedDiscrepancy f`.
-/
theorem notBoundedOriginal (out : Stage2Output f) : ¬ BoundedDiscrepancy f := by
  exact out.out1.not_boundedDiscrepancy_of_unboundedDiscrepancyAlong (f := f) out.unbounded

/-- Stage 2 output implies the usual surface statement `∀ C, HasDiscrepancyAtLeast f C`.

This is a thin wrapper around `notBoundedOriginal`.
-/
theorem forall_hasDiscrepancyAtLeast (out : Stage2Output f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  refine (forall_hasDiscrepancyAtLeast_iff_not_boundedDiscrepancy f).2 ?_
  exact out.notBoundedOriginal (f := f)

/-- Specialization of `forall_hasDiscrepancyAtLeast` at a fixed threshold `C`.

This is a tiny convenience lemma: it avoids an extra application at the call site.
-/
theorem hasDiscrepancyAtLeast (out : Stage2Output f) (C : ℕ) : HasDiscrepancyAtLeast f C := by
  exact (out.forall_hasDiscrepancyAtLeast (f := f)) C

/-!
## Offset-discrepancy normal forms used by Stage 3
-/

/-- Stage 2 output implies unbounded bundled offset discrepancy for the original sequence
at the concrete parameters `out.d` and `out.m`.

This is the Stage-1 transport contract applied to the fixed-step unboundedness witness
`out.unbounded`.
-/
theorem unboundedDiscOffset (out : Stage2Output f) : UnboundedDiscOffset f out.d out.m := by
  simpa using
    ((out.out1.unboundedDiscrepancyAlong_iff_unboundedDiscOffset (f := f))).1 out.unbounded

/-- Stage 2 implies there is no uniform bound on the bundled offset discrepancy family
`discOffset f out.d out.m`.

This is the negation-normal-form version of `unboundedDiscOffset`.
-/
theorem not_exists_boundedDiscOffset (out : Stage2Output f) :
    ¬ ∃ B : ℕ, BoundedDiscOffset f out.d out.m B := by
  have hunb : UnboundedDiscOffset f out.d out.m := out.unboundedDiscOffset (f := f)
  exact
    (Tao2015.unboundedDiscOffset_iff_not_exists_boundedDiscOffset (f := f)
        (d := out.d) (m := out.m)).1
      hunb

-- Note: additional witness-form wrappers (e.g. `forall_exists_discOffset_gt'_witness_pos`,
-- `forall_exists_natAbs_apSumOffset_gt_witness_pos`, and the negation-normal-form
-- `not_exists_forall_discOffset_le`) live in
-- `Conjectures.C0002_erdos_discrepancy.src.TrackCStage2CoreExtras`.

/-!
## Core-predicate bridge
-/

/-- Stage-2 unboundedness, re-expressed using the verified core predicate.

This is a small convenience lemma: many consumers outside the `Tao2015` namespace use the core
predicate `MoltResearch.UnboundedDiscrepancyAlong` rather than the Track-C-local definition.
-/
theorem unboundedDiscrepancyAlong_core (out : Stage2Output f) :
    MoltResearch.UnboundedDiscrepancyAlong out.g out.d := by
  exact (Tao2015.unboundedDiscrepancyAlong_iff_core (g := out.g) (d := out.d)).1 out.unbounded

end Stage2Output

end Tao2015

end MoltResearch
