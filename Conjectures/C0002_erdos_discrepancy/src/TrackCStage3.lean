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

/-- Positivity of the reduced step size packaged in Stage 3.

This is just the Stage-2 field `out.out2.hd` rewritten to use the Stage-3 projection `out.d`.
-/
theorem d_pos (out : Stage3Output f) : 0 < out.d := by
  exact out.out2.hd

/-- Convenience projection: the reduced sequence packaged in Stage 3. -/
@[simp] abbrev g (out : Stage3Output f) : ℕ → ℤ :=
  out.out2.g

/-- Convenience projection: the bundled offset parameter packaged in Stage 3. -/
@[simp] abbrev m (out : Stage3Output f) : ℕ :=
  out.out2.m

/-- Convenience projection: the affine-tail start index `m*d` packaged in Stage 3.

Design note: we define this by reusing the Stage-2 start index projection so the arithmetic
normal-form lemmas (`dvd`, `mod`) stay consistent across Stage 2 and Stage 3.
-/
abbrev start (out : Stage3Output f) : ℕ :=
  Stage2Output.start out.out2

/-- Normal form: the affine-tail start index is `m*d`.

This is just the corresponding Stage-2 projection lemma, rewritten to use the Stage-3 projections.
-/
@[simp] theorem start_eq_m_mul_d (out : Stage3Output f) : out.start = out.m * out.d := by
  rfl

/-- Normal form: the affine-tail nucleus at `out.start` is the bundled offset nucleus at `out.m`.

This is the corresponding Stage-2 core rewrite lemma, transported to Stage 3 by rewriting the
projections `out.start`, `out.d`, and `out.m`.
-/
theorem apSumFrom_start_eq_apSumOffset (out : Stage3Output f) (n : ℕ) :
    apSumFrom f out.start out.d n = apSumOffset f out.d out.m n := by
  simpa [Stage3Output.start, Stage3Output.d, Stage3Output.m] using
    (Stage2Output.apSumFrom_start_eq_apSumOffset (f := f) (out := out.out2) (n := n))

/-- Recover the offset parameter `out.m` by dividing the start index `out.start` by the step size
`out.d`.

This is a tiny arithmetic convenience lemma: `out.start = out.m * out.d` by definition (via Stage 2).
-/
theorem start_div_d (out : Stage3Output f) : out.start / out.d = out.m := by
  simp [Stage3Output.start, Stage3Output.d, Stage3Output.m,
    Stage2Output.start_div_d (f := f) (out := out.out2)]

/-- The affine-tail start index `out.start` is a multiple of the reduced step size `out.d`. -/
theorem d_dvd_start (out : Stage3Output f) : out.d ∣ out.start := by
  -- Rewrite to the corresponding Stage-2 normal form.
  change out.out2.d ∣ Stage2Output.start out.out2
  exact Stage2Output.d_dvd_start (f := f) (out := out.out2)

/-- The affine-tail start index has remainder `0` modulo the reduced step size `out.d`.

This is often the most convenient normal form of `d_dvd_start`.
-/
theorem start_mod_d (out : Stage3Output f) : out.start % out.d = 0 := by
  -- Rewrite to the corresponding Stage-2 normal form.
  change Stage2Output.start out.out2 % out.out2.d = 0
  exact Stage2Output.start_mod_d (f := f) (out := out.out2)

/-- Adding the start index does not change residues modulo the step size.

Since `out.start` is a multiple of `out.d`, we have
`(n + out.start) % out.d = n % out.d`.
-/
theorem add_start_mod_d (out : Stage3Output f) (n : ℕ) :
    (n + out.start) % out.d = n % out.d := by
  simp [Stage3Output.start, Stage3Output.d,
    Stage2Output.add_start_mod_d (f := f) (out := out.out2) (n := n)]

/-- Variant of `add_start_mod_d` with the start index on the left. -/
theorem start_add_mod_d (out : Stage3Output f) (n : ℕ) :
    (out.start + n) % out.d = n % out.d := by
  rw [Nat.add_comm]
  exact out.add_start_mod_d (f := f) (n := n)

/-- Adding the start index increases quotients by the offset parameter.

Since `out.start = out.m * out.d`, we have
`(n + out.start) / out.d = n / out.d + out.m`.
-/
theorem add_start_div_d (out : Stage3Output f) (n : ℕ) :
    (n + out.start) / out.d = n / out.d + out.m := by
  -- Delegate to the corresponding Stage-2 arithmetic normalization lemma.
  simpa [Stage3Output.start, Stage3Output.d, Stage3Output.m] using
    (Stage2Output.add_start_div_d (f := f) (out := out.out2) (n := n))

/-- Variant of `add_start_div_d` with the start index on the left. -/
theorem start_add_div_d (out : Stage3Output f) (n : ℕ) :
    (out.start + n) / out.d = n / out.d + out.m := by
  simpa [Nat.add_comm] using out.add_start_div_d (f := f) (n := n)

/-- Normal form: the bundled offset discrepancy wrapper `discOffset f out.d out.m n` is the
absolute value of the affine-tail nucleus `apSumFrom f out.start out.d n`.

This is `discOffset_eq_natAbs_apSumFrom_mul` rewritten using the Stage-3 start index
`out.start = out.m * out.d`.

It is a common analytic normal form for consuming the Stage-3 offset-discrepancy witness.
-/
theorem discOffset_eq_natAbs_apSumFrom_start (out : Stage3Output f) (n : ℕ) :
    discOffset f out.d out.m n = Int.natAbs (apSumFrom f out.start out.d n) := by
  simpa [Stage3Output.start, Stage2Output.start] using
    (discOffset_eq_natAbs_apSumFrom_mul (f := f) (d := out.d) (m := out.m) (n := n))

/-- Reverse-direction normal form: the absolute value of the affine-tail nucleus at the Stage-3
start index is the bundled offset discrepancy wrapper.

This is `discOffset_eq_natAbs_apSumFrom_start` with sides swapped.
-/
theorem natAbs_apSumFrom_start_eq_discOffset (out : Stage3Output f) (n : ℕ) :
    Int.natAbs (apSumFrom f out.start out.d n) = discOffset f out.d out.m n := by
  simpa using (out.discOffset_eq_natAbs_apSumFrom_start (f := f) (n := n)).symm

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

/-- Negation-normal form: there is no uniform bound on the affine-tail nuclei
`Int.natAbs (apSumFrom f (m*d) d n)` at the deterministic Stage-3 parameters `out.d` and `out.m`.

This is `unboundedDiscOffset` rewritten using
`Tao2015.UnboundedDiscOffset.iff_not_exists_forall_natAbs_apSumFrom_mul_le`.
-/
theorem not_exists_forall_natAbs_apSumFrom_mul_le (out : Stage3Output f) :
    ¬ ∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) ≤ B := by
  have hunb : UnboundedDiscOffset f out.d out.m := out.unboundedDiscOffset (f := f)
  exact
    (_root_.MoltResearch.Tao2015.UnboundedDiscOffset.iff_not_exists_forall_natAbs_apSumFrom_mul_le
        (f := f) (d := out.d) (m := out.m)).1
      hunb

/-- Start-index phrasing of `not_exists_forall_natAbs_apSumFrom_mul_le`.

This replaces the explicit arithmetic form `out.m * out.d` with the bundled start index `out.start`
to reduce noise in downstream stages.
-/
theorem not_exists_forall_natAbs_apSumFrom_start_le (out : Stage3Output f) :
    ¬ ∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumFrom f out.start out.d n) ≤ B := by
  simpa [Stage3Output.start, Stage2Output.start] using
    out.not_exists_forall_natAbs_apSumFrom_mul_le (f := f)

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
    exact lt_of_lt_of_le Nat.zero_lt_one hd
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

/-- Stage 3 output implies the explicit discrepancy witness normal form.

Normal form:
`∀ C, ∃ d n, d > 0 ∧ discrepancy f d n > C`.

This is just `forall_exists_discrepancy_gt_witness_pos` with the positivity side condition dropped.
-/
theorem forall_exists_discrepancy_gt (out : Stage3Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ discrepancy f d n > C := by
  intro C
  rcases out.forall_exists_discrepancy_gt_witness_pos (f := f) C with ⟨d, n, hd, _hn, hgt⟩
  exact ⟨d, n, hd, hgt⟩

end Stage3Output

/-!
## Stage 3 entry point

The Stage-3 entry point `stage3` (a definition, not an axiom) lives in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryMinimal` and is re-exported by
`...TrackCStage3EntryCore` and `...TrackCStage3Entry`, so that this file remains purely “API + wiring”.
-/

end Tao2015

end MoltResearch
