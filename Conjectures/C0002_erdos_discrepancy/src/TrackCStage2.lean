import Conjectures.C0002_erdos_discrepancy.src.Tao2015

/-!
# Track C: Stage 2 boundary (Tao 2015 plane)

This module is **Conjectures-only** glue: it introduces a *named stage boundary* for the Tao 2015
Erdős discrepancy proof pipeline.

Design goals:
- Keep the interface small and typed (IO contract, not a pile of lemmas).
- Avoid lemma sprawl: downstream work should prove theorems *about this boundary*, rather than
  repeatedly re-stating the same intermediate reductions.

No statements here are intended for the verified substrate (`MoltResearch/`).
-/

namespace MoltResearch

namespace Tao2015

/-!
Stage 1 (`ReductionOutput`) packages a shift reduction from the original sign sequence `f` to an
auxiliary sign sequence `g` together with a step size `d`.

Stage 2 (this file) is the next boundary we want to populate: from the Stage-1 reduced sequence,
produce a fixed-step *unboundedness witness form* (`UnboundedDiscrepancyAlong`).

The point of naming this as a record is so later stages can consume it without depending on the
exact internal path used to obtain unboundedness.
-/

/-- Output of Stage 2 of the Track C pipeline.

This is intentionally minimal:
- we keep the full Stage-1 `ReductionOutput` so later stages have access to `g`, `d`, `m`, and the
  bridge contracts;
- we expose the Stage-2 result as *unbounded discrepancy along the fixed step* `d`.

Downstream stages should treat `out1.g` (at step `out1.d`) as the canonical fixed-step locus.
-/
structure Stage2Output (f : ℕ → ℤ) : Type where
  out1 : Tao2015.ReductionOutput f
  unbounded : Tao2015.UnboundedDiscrepancyAlong out1.g out1.d

namespace Stage2Output

variable {f : ℕ → ℤ}

/-- Convenience projection: the reduced step size. -/
abbrev d (out : Stage2Output f) : ℕ := out.out1.d

/-- Convenience projection: the reduced sequence. -/
abbrev g (out : Stage2Output f) : ℕ → ℤ := out.out1.g

/-- (Deprecated) Unboundedness of the reduced sequence in explicit witness form (`B < discrepancy ...`).

Prefer using the field `out.unbounded` (or the more structured
`forall_hasDiscrepancyAtLeastAlong`) to keep the Stage-2 API surface small.
-/
@[deprecated "Use `out.unbounded` (or `forall_hasDiscrepancyAtLeastAlong`)." (since := "2026-03-24")]
theorem forall_exists_discrepancy_gt (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, B < discrepancy out.g out.d n := by
  -- This is just the definitional witness form for `UnboundedDiscrepancyAlong`.
  simpa [Tao2015.UnboundedDiscrepancyAlong] using out.unbounded

/-- Equivalent packaging: arbitrarily large discrepancy witnesses along `out.d`. -/
theorem forall_hasDiscrepancyAtLeastAlong (out : Stage2Output f) :
    ∀ C : ℕ, HasDiscrepancyAtLeastAlong out.g out.d C := by
  -- `UnboundedDiscrepancyAlong` is definitionally `∀ C, HasDiscrepancyAtLeastAlong ... C`.
  simpa [Tao2015.UnboundedDiscrepancyAlong, HasDiscrepancyAtLeastAlong] using out.unbounded

/-- Stage-2 unboundedness, re-expressed using the verified core predicate.

This is a small convenience lemma: many consumers outside the `Tao2015` namespace use the core
predicate `MoltResearch.UnboundedDiscrepancyAlong` rather than the Track-C-local definition.
-/
theorem unboundedDiscrepancyAlong_core (out : Stage2Output f) :
    MoltResearch.UnboundedDiscrepancyAlong out.g out.d := by
  exact (Tao2015.unboundedDiscrepancyAlong_iff_core (g := out.g) (d := out.d)).1 out.unbounded

/-- Tail-nucleus witness form: Stage 2 yields arbitrarily large affine-tail sums
`apSumFrom f (m*d) d n`.

This is just `forall_hasDiscrepancyAtLeastAlong` transported through the Stage-1 bridge lemma
`ReductionOutput.hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_mul_gt`.
-/
theorem forall_exists_natAbs_apSumFrom_mul_gt (out : Stage2Output f) :
    ∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (out.out1.m * out.out1.d) out.out1.d n) > C := by
  intro C
  have hdisc : HasDiscrepancyAtLeastAlong out.g out.d C :=
    out.forall_hasDiscrepancyAtLeastAlong (f := f) C
  exact
    ((out.out1.hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSumFrom_mul_gt (f := f) (C := C)).1
      hdisc)

/-- Stage 2 implies the reduced sequence is not bounded along its fixed step size. -/
theorem notBoundedReducedAlong (out : Stage2Output f) : ¬ BoundedDiscrepancyAlong out.g out.d := by
  exact (Tao2015.UnboundedDiscrepancyAlong.iff_not_boundedDiscrepancyAlong
    (g := out.g) (d := out.d)).1 out.unbounded

/-- Consumer-facing form: Stage 2 unboundedness transferred back to the original sequence as an
unbounded **offset discrepancy** witness.

This is just a wrapper around
`Tao2015.ReductionOutput.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt`.

Note the inequality direction: this produces witnesses of the form `B < discOffset ...`.
-/
theorem forall_exists_discOffset_gt (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.out1.d out.out1.m n := by
  -- Unfold the Stage-2 witness form and transport it through the Stage-1 contract.
  simpa using
    ((out.out1.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt (f := f)).1 out.unbounded)

/-- Stage 2 implies *unbounded offset discrepancy* for the original sequence, at the bundled
parameters `(out.out1.d, out.out1.m)`.

This is the packaged predicate version of `forall_exists_discOffset_gt`.
-/
theorem unboundedDiscOffset (out : Stage2Output f) :
    Tao2015.UnboundedDiscOffset f out.out1.d out.out1.m := by
  exact (out.out1.unboundedDiscrepancyAlong_iff_unboundedDiscOffset (f := f)).1 out.unbounded

/-- Stage 2 implies there is no uniform bound on the bundled offset discrepancy family
`discOffset f out.out1.d out.out1.m`.

This is the negation-normal-form version of `unboundedDiscOffset`.
-/
theorem not_exists_boundedDiscOffset (out : Stage2Output f) :
    ¬ ∃ B : ℕ, BoundedDiscOffset f out.out1.d out.out1.m B := by
  have hunb : UnboundedDiscOffset f out.out1.d out.out1.m :=
    out.unboundedDiscOffset (f := f)
  exact
    (Tao2015.unboundedDiscOffset_iff_not_exists_boundedDiscOffset (f := f)
        (d := out.out1.d) (m := out.out1.m)).1
      hunb

/-- Existential packaging: Stage 2 already yields concrete parameters `d, m` such that the bundled
offset discrepancy family `discOffset f d m` is unbounded.

This is occasionally a convenient normal form for later stages that prefer not to depend on the
record fields of `Stage2Output`.
-/
theorem exists_params_unboundedDiscOffset (out : Stage2Output f) :
    ∃ d m : ℕ, d > 0 ∧ UnboundedDiscOffset f d m := by
  refine ⟨out.out1.d, out.out1.m, out.out1.hd, ?_⟩
  exact out.unboundedDiscOffset (f := f)

/-- Existential packaging: Stage 2 yields concrete parameters `d, m` such that the affine-tail nucleus
`apSumFrom f (m*d) d n` takes arbitrarily large absolute values.

This is the explicit witness-family form often consumed by later analytic stages.
-/
theorem exists_params_forall_exists_natAbs_apSumFrom_mul_gt (out : Stage2Output f) :
    ∃ d m : ℕ, d > 0 ∧
      (∀ C : ℕ, ∃ n : ℕ, C < Int.natAbs (apSumFrom f (m * d) d n)) := by
  refine ⟨out.out1.d, out.out1.m, out.out1.hd, ?_⟩
  intro C
  rcases out.forall_exists_natAbs_apSumFrom_mul_gt (f := f) C with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [gt_iff_lt] using hn

/-- Backwards-compatible alias for `forall_exists_discOffset_gt`.

Deprecated because the suffix `_lt` was misleading: the statement is `B < ...` (i.e. “greater than B”).
-/
@[deprecated "Use `forall_exists_discOffset_gt` (the statement is `B < discOffset ...`)." (since := "2026-03-08")]
theorem forall_exists_discOffset_lt (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.out1.d out.out1.m n := by
  simpa using out.forall_exists_discOffset_gt (f := f)

/-- Sum-level variant of `forall_exists_discOffset_gt`.

This is occasionally the right normal form for later analytic stages: it exposes the raw nucleus
`apSumOffset` rather than the wrapper `discOffset`.
-/
theorem forall_exists_natAbs_apSumOffset_gt (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.out1.d out.out1.m n) := by
  simpa using
    ((out.out1.unboundedDiscrepancyAlong_iff_forall_exists_natAbs_apSumOffset_gt (f := f)).1
      out.unbounded)

/-- Backwards-compatible alias for `forall_exists_natAbs_apSumOffset_gt`.

Deprecated because the suffix `_lt` was misleading: the statement is `B < ...`.
-/
@[deprecated "Use `forall_exists_natAbs_apSumOffset_gt` (the statement is `B < Int.natAbs ...`)." (since := "2026-03-08")]
theorem forall_exists_natAbs_apSumOffset_lt (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.out1.d out.out1.m n) := by
  simpa using out.forall_exists_natAbs_apSumOffset_gt (f := f)

/-- Consumer-facing form: Stage 2 implies global unbounded discrepancy for the original sequence.

This is the minimal “bridge back to the main theorem statement” lemma: it packages the fact that
Stage 2 gives an explicit unbounded offset-discrepancy family for `f`, and then uses the Stage-1
contract carried by `out.out1` to conclude `¬ BoundedDiscrepancy f`.
-/
theorem notBoundedOriginal (out : Stage2Output f) : ¬ BoundedDiscrepancy f := by
  -- Transport the Stage-2 unboundedness witness back to `f` through the Stage-1 reduction record.
  exact out.out1.not_boundedDiscrepancy_of_unboundedDiscrepancyAlong (f := f) out.unbounded

/-- Stage 2 output implies the usual "∀ C, HasDiscrepancyAtLeast f C" surface statement.

This is a convenience wrapper around `notBoundedOriginal`.
-/
theorem forall_hasDiscrepancyAtLeast (out : Stage2Output f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  refine (forall_hasDiscrepancyAtLeast_iff_not_boundedDiscrepancy f).2 ?_
  exact out.notBoundedOriginal (f := f)

/-- Stage 2 output implies the nucleus witness form

`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is the most pipeline-friendly surface statement for consuming Stage 2 without going through
Stage 3.
-/
theorem forall_exists_d_ge_one_witness_pos (out : Stage2Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_d_ge_one_witness_pos f).1
      (out.forall_hasDiscrepancyAtLeast (f := f))

end Stage2Output

/-!
## Stage 2 conjecture stub

The Stage-2 conjecture/axiom stub lives in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Proof` so that this file remains mostly
“API + wiring”.
-/

end Tao2015

end MoltResearch
