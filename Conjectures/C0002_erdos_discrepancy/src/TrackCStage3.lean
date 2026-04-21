import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Core

/-!
# Track C: Stage 3 boundary (Tao 2015 plane)

This module is **Conjectures-only** glue.

Stage 2 produces a fixed-step unboundedness witness for the reduced sequence `g` (at step `d`),
plus a transport lemma back to an *offset discrepancy* witness for the original sequence `f`.

Stage 3 is the boundary where we finally discharge the global goal `¬ BoundedDiscrepancy f`.

Design goal: keep the hard-gate surface small.

Most convenience lemmas about `Stage3Output` live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3Output`.
-/

namespace MoltResearch

namespace Tao2015

/-- Output of Stage 3 of the Track C pipeline.

We keep the full Stage-2 output for traceability. The global conclusion
`¬ BoundedDiscrepancy f` is derived (as `Stage3Output.notBounded`) from the Stage-2 boundary.
-/
structure Stage3Output (f : ℕ → ℤ) : Type where
  out2 : Tao2015.Stage2Output f

namespace Stage3Output

variable {f : ℕ → ℤ}

/-- Convenience projection: Stage 3 carries the full Stage-2 output, hence also carries the
underlying Stage-1 reduction output.

This is occasionally useful when later stages want access to the deterministic parameters
`g, d, m` and the Stage-1 transport contracts, without reaching through multiple record fields.
-/
@[simp] abbrev out1 (out : Stage3Output f) : Tao2015.ReductionOutput f :=
  out.out2.out1

/-- Convenience projection: the reduced step size packaged in Stage 3. -/
@[simp] abbrev d (out : Stage3Output f) : ℕ :=
  out.out2.d

/-- Convenience projection: the reduced sequence packaged in Stage 3. -/
@[simp] abbrev g (out : Stage3Output f) : ℕ → ℤ :=
  out.out2.g

/-- Convenience projection: the bundled offset parameter packaged in Stage 3. -/
@[simp] abbrev m (out : Stage3Output f) : ℕ :=
  out.out2.m

/-- Convenience projection: the affine-tail start index `m*d` packaged in Stage 3. -/
abbrev start (out : Stage3Output f) : ℕ :=
  out.m * out.d

/-- Definitional rewrite: the affine-tail start index is `m*d`.

This lemma is intentionally tiny (and not a simp lemma): it exists mainly to reduce `dsimp` noise
in downstream arithmetic rewrites.
-/
theorem start_eq_m_mul_d (out : Stage3Output f) : out.start = out.m * out.d := by
  rfl

/-- The affine-tail start index `out.start` is a multiple of the reduced step size `out.d`. -/
theorem d_dvd_start (out : Stage3Output f) : out.d ∣ out.start := by
  refine ⟨out.m, ?_⟩
  simp [Stage3Output.start, Nat.mul_comm]

/-- The affine-tail start index has remainder `0` modulo the reduced step size `out.d`.

This is often the most convenient normal form of `d_dvd_start`.
-/
theorem start_mod_d (out : Stage3Output f) : out.start % out.d = 0 := by
  exact Nat.mod_eq_zero_of_dvd out.d_dvd_start

/-- Stage 3 already closes the global goal `¬ BoundedDiscrepancy f`.

We intentionally do not store this as a field: it is derived from the Stage-2 output.

Implementation note: we delegate to the tiny Stage-2 core bridge lemma `Stage2Output.notBoundedOriginal`.
-/
theorem notBounded (out : Stage3Output f) : ¬ BoundedDiscrepancy f := by
  exact out.out2.notBoundedOriginal (f := f)

/-- Stage 3 output also exposes the Stage-2 offset-discrepancy witness predicate.

This is a thin wrapper around the Stage-2 core lemma `Stage2Output.unboundedDiscOffset`.
-/
theorem unboundedDiscOffset (out : Stage3Output f) :
    UnboundedDiscOffset f out.d out.m := by
  simpa [Stage3Output.d, Stage3Output.m] using out.out2.unboundedDiscOffset (f := f)

/-- Stage 3 output also exposes the Stage-2 fixed-step unboundedness witness (the Tao2015 predicate
`UnboundedDiscrepancyAlong`) along the reduced sequence.

This is just the `unbounded` field of the carried Stage-2 output, rewritten to use the
Stage-3 projections.
-/
theorem unboundedDiscrepancyAlong (out : Stage3Output f) :
    Tao2015.UnboundedDiscrepancyAlong out.g out.d := by
  simpa [Stage3Output.g, Stage3Output.d] using out.out2.unbounded

/-- Stage 3 implies the reduced sequence is not bounded along its fixed step size. -/
theorem notBoundedReducedAlong (out : Stage3Output f) : ¬ BoundedDiscrepancyAlong out.g out.d := by
  -- Delegate to the Stage-2 core boundary lemma carried by Stage 3.
  simpa [Stage3Output.g, Stage3Output.d] using
    (Stage2Output.notBoundedReducedAlong (f := f) (out := out.out2))

/-- Stage 3 output also exposes the Stage-2 fixed-step unboundedness witness, phrased using the
verified core predicate `MoltResearch.UnboundedDiscrepancyAlong`.

This is a thin wrapper around `Stage2Output.unboundedDiscrepancyAlong_core`.
-/
theorem unboundedDiscrepancyAlong_core (out : Stage3Output f) :
    MoltResearch.UnboundedDiscrepancyAlong out.g out.d := by
  simpa [Stage3Output.g, Stage3Output.d] using out.out2.unboundedDiscrepancyAlong_core (f := f)

/-- Stage 3 output implies there is no bundled offset bound at the deterministic Stage-2 parameters.

This is the stable boundedness-negation normal form of `unboundedDiscOffset`.
-/
theorem not_exists_boundedDiscOffset (out : Stage3Output f) :
    ¬ ∃ B : ℕ, BoundedDiscOffset f out.d out.m B := by
  simpa [Stage3Output.d, Stage3Output.m] using out.out2.not_exists_boundedDiscOffset (f := f)

/-- Negation-normal form: there is no uniform bound on the bundled offset discrepancy family
`discOffset f out.d out.m`.

Normal form:
`¬ ∃ B, ∀ n, discOffset f out.d out.m n ≤ B`.

This is `unboundedDiscOffset` rewritten using
`Tao2015.unboundedDiscOffset_iff_not_exists_forall_discOffset_le`.
-/
theorem not_exists_forall_discOffset_le (out : Stage3Output f) :
    ¬ ∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B := by
  have hunb : UnboundedDiscOffset f out.d out.m := out.unboundedDiscOffset (f := f)
  exact
    (Tao2015.unboundedDiscOffset_iff_not_exists_forall_discOffset_le (f := f)
        (d := out.d) (m := out.m)).1
      hunb

/-- Deterministic Stage-3 completion: a Stage-2 output already contains enough information to
contradict any global boundedness hypothesis.

This is the main “stage boundary” lemma: it is proved (no placeholders) and should remain stable.
-/
def ofStage2Output (out2 : Tao2015.Stage2Output f) : Stage3Output f :=
  ⟨out2⟩

/-- The Stage-2 output carried by `ofStage2Output` is definitionally the input `out2`.

This is a tiny simp lemma that reduces rewriting noise when shuttling between Stage 2 and Stage 3.
-/
@[simp] theorem ofStage2Output_out2 (out2 : Tao2015.Stage2Output f) :
    (ofStage2Output (f := f) out2).out2 = out2 := by
  rfl

/-- Stage 3 output implies the usual surface statement `∀ C, HasDiscrepancyAtLeast f C`.

We keep this lemma in the hard-gate module so `ErdosDiscrepancy.lean` can remain minimal.
-/
theorem forall_hasDiscrepancyAtLeast (out : Stage3Output f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  refine (forall_hasDiscrepancyAtLeast_iff_not_boundedDiscrepancy f).2 ?_
  exact out.notBounded (f := f)

/-- Specialization of `forall_hasDiscrepancyAtLeast` at a fixed threshold `C`.

This is a tiny convenience lemma: it avoids an extra application at the call site.
-/
theorem hasDiscrepancyAtLeast (out : Stage3Output f) (C : ℕ) : HasDiscrepancyAtLeast f C := by
  exact (out.forall_hasDiscrepancyAtLeast (f := f)) C

/-- Stage 3 output implies the nucleus witness form

`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is the most pipeline-friendly surface normal form: it avoids `discrepancy` and uses the
nucleus `apSum` directly.

It is a thin wrapper around `forall_hasDiscrepancyAtLeast` via
`forall_hasDiscrepancyAtLeast_iff_forall_exists_d_ge_one_witness_pos`.
-/
theorem forall_exists_d_ge_one_witness_pos (out : Stage3Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_d_ge_one_witness_pos f).1
      (out.forall_hasDiscrepancyAtLeast (f := f))

/-- Variant of `forall_exists_d_ge_one_witness_pos` writing the step-size side condition as `d > 0`.

This is slightly weaker but often matches downstream APIs that prefer `Nat` positivity hypotheses.
-/
theorem forall_exists_d_pos_witness_pos (out : Stage3Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  intro C
  rcases out.forall_exists_d_ge_one_witness_pos (f := f) C with ⟨d, n, hd, hn, hgt⟩
  have hdpos : d > 0 := by
    have h : Nat.succ 0 ≤ d := by
      simpa using hd
    exact (Nat.succ_le_iff).1 h
  exact ⟨d, n, hdpos, hn, hgt⟩

/-- Stage 3 output implies the explicit discrepancy witness normal form with a positive-length witness.

Normal form:
`∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ discrepancy f d n > C`.

This is a thin wrapper around `forall_exists_d_pos_witness_pos`, rewriting `discrepancy` to its
definitional `apSum` form.
-/
theorem forall_exists_discrepancy_gt_witness_pos (out : Stage3Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ discrepancy f d n > C := by
  intro C
  rcases out.forall_exists_d_pos_witness_pos (f := f) C with ⟨d, n, hd, hn, hgt⟩
  refine ⟨d, n, hd, hn, ?_⟩
  -- `discrepancy f d n` is definitionally `Int.natAbs (apSum f d n)`.
  change Int.natAbs (apSum f d n) > C
  exact hgt

end Stage3Output

/-!
## Stage 3 entry point

The Stage-3 entry point `stage3` (a definition, not an axiom) lives in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryMinimal` and is re-exported by
`...TrackCStage3EntryCore` and `...TrackCStage3Entry`, so that this file remains purely “API + wiring”.
-/

end Tao2015

end MoltResearch
