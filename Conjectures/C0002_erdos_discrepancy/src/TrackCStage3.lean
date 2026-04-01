import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Proof

/-!
# Track C: Stage 3 boundary (Tao 2015 plane)

This module is **Conjectures-only** glue.

Stage 2 produces a fixed-step unboundedness witness for the reduced sequence `g` (at step `d`),
plus a transport lemma back to an *offset discrepancy* witness for the original sequence `f`.

Stage 3 is the boundary where we finally discharge the global goal `¬ BoundedDiscrepancy f`.

Design goal: keep the interface small and typed; avoid sprinkling ad-hoc “unboundedness → not bounded”
lemmas throughout the codebase.
-/

namespace MoltResearch

namespace Tao2015

/-- Output of Stage 3 of the Track C pipeline.

We keep the full Stage-2 output for traceability, and package the global conclusion
`¬ BoundedDiscrepancy f` as the consumer-facing end of the Conjectures-only plane.
-/
structure Stage3Output (f : ℕ → ℤ) : Type where
  out2 : Tao2015.Stage2Output f
  notBounded : ¬ BoundedDiscrepancy f

namespace Stage3Output

variable {f : ℕ → ℤ}

/-- Convenience projection: the reduced step size packaged in Stage 3. -/
abbrev d (out : Stage3Output f) : ℕ := out.out2.out1.d

/-- Convenience projection: the reduced sequence packaged in Stage 3. -/
abbrev g (out : Stage3Output f) : ℕ → ℤ := out.out2.out1.g

/-- Convenience projection: the bundled offset parameter packaged in Stage 3. -/
abbrev m (out : Stage3Output f) : ℕ := out.out2.out1.m

/-- Convenience projection: positivity of the reduced step size. -/
abbrev hd (out : Stage3Output f) : out.d > 0 := out.out2.out1.hd

/-- Convenience lemma: the reduced step size is nonzero. -/
theorem d_ne_zero (out : Stage3Output f) : out.d ≠ 0 := by
  exact Nat.ne_of_gt out.hd

/-- Convenience lemma: the reduced step size is at least `1`. -/
theorem one_le_d (out : Stage3Output f) : 1 ≤ out.d := by
  simpa using (Nat.succ_le_iff).2 out.hd

/-- Deterministic Stage-3 completion: a Stage-2 output already contains enough information to
contradict any global boundedness hypothesis.

This is the main “stage boundary” lemma: it is *proved* (no `sorry`) and should remain stable.
-/
def ofStage2Output (out2 : Tao2015.Stage2Output f) : Stage3Output f := by
  refine ⟨out2, ?_⟩
  -- Stage 2 already packages the global negation form `¬ BoundedDiscrepancy f`.
  exact Stage2Output.notBoundedOriginal (f := f) out2

/-- Stage 3 output implies the usual "∀ C, HasDiscrepancyAtLeast f C" statement. -/
theorem forall_hasDiscrepancyAtLeast (out : Stage3Output f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  -- Stage 2 already packages this surface statement.
  exact Stage2Output.forall_hasDiscrepancyAtLeast (f := f) out.out2

/-- Stage 3 output implies the nucleus witness form

`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is the most pipeline-friendly surface statement for consuming Stage 3.
-/
theorem forall_exists_d_ge_one_witness_pos (out : Stage3Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  -- Stage 2 already yields this nucleus witness form.
  exact Stage2Output.forall_exists_d_ge_one_witness_pos (f := f) out.out2

/-- Variant of `forall_exists_d_ge_one_witness_pos` with the step-size side condition written as
`d > 0`.

Many consumers prefer the strict-positivity normal form when working with `Nat` step sizes.
-/
theorem forall_exists_d_pos_witness_pos (out : Stage3Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  intro C
  rcases (Stage2Output.forall_exists_d_ge_one_witness_pos (f := f) out.out2) C with ⟨d, n, hd, hn, hC⟩
  have hd' : d > 0 := lt_of_lt_of_le Nat.zero_lt_one hd
  exact ⟨d, n, hd', hn, hC⟩

/-- Stage 3 output yields unboundedness of the bundled offset discrepancy family
`discOffset f d m` at the *concrete* parameters coming from Stage 1.

This is just a thin wrapper around `Stage2Output.unboundedDiscOffset`.
-/
theorem unboundedDiscOffset (out : Stage3Output f) :
    UnboundedDiscOffset f out.out2.out1.d out.out2.out1.m := by
  exact Stage2Output.unboundedDiscOffset (f := f) out.out2

/-- Negation-normal-form boundedness statement for the concrete Stage-1 parameters bundled in
Stage 3.

This is the Prop-style boundedness predicate form of `unboundedDiscOffset`.
-/
theorem not_exists_boundedDiscOffset (out : Stage3Output f) :
    ¬ ∃ B : ℕ, BoundedDiscOffset f out.out2.out1.d out.out2.out1.m B := by
  exact Stage2Output.not_exists_boundedDiscOffset (f := f) out.out2

/-- Nucleus witness form for the concrete Stage-1 parameters bundled in Stage 3.

This is `unboundedDiscOffset` rewritten so consumers can work directly with
`Int.natAbs (apSumOffset f d m n)` without unfolding `discOffset`.
-/
theorem forall_exists_natAbs_apSumOffset_gt (out : Stage3Output f) :
    ∀ B : ℕ, ∃ n : ℕ,
      B < Int.natAbs (apSumOffset f out.out2.out1.d out.out2.out1.m n) := by
  intro B
  rcases out.unboundedDiscOffset (f := f) B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  -- `discOffset` is definitionally `Int.natAbs (apSumOffset ...)`.
  unfold discOffset at hn
  exact hn

/-- Inequality-direction variant of `forall_exists_natAbs_apSumOffset_gt`, written as
`Int.natAbs ... > B`.

Many consumers prefer this normal form so they can `simp [gt_iff_lt]` at the call site.
-/
theorem forall_exists_natAbs_apSumOffset_gt' (out : Stage3Output f) :
    ∀ B : ℕ, ∃ n : ℕ,
      Int.natAbs (apSumOffset f out.out2.out1.d out.out2.out1.m n) > B := by
  intro B
  rcases out.forall_exists_natAbs_apSumOffset_gt (f := f) B with ⟨n, hn⟩
  exact ⟨n, by simpa [gt_iff_lt] using hn⟩

/-- Stage 3 output implies there exist concrete parameters `d, m` such that the bundled offset
  discrepancy family `discOffset f d m` is unbounded.

This is a small convenience wrapper around the Stage-2 packaging.
-/
theorem exists_params_unboundedDiscOffset (out : Stage3Output f) :
    ∃ d m : ℕ, d > 0 ∧ UnboundedDiscOffset f d m := by
  exact Stage2Output.exists_params_unboundedDiscOffset (f := f) out.out2

/-- Variant of `exists_params_unboundedDiscOffset` packaging the step-size side condition as `1 ≤ d`.

Many later stages prefer the normal form `1 ≤ d` rather than `d > 0`.
-/
theorem exists_params_one_le_unboundedDiscOffset (out : Stage3Output f) :
    ∃ d m : ℕ, 1 ≤ d ∧ UnboundedDiscOffset f d m := by
  exact Stage2Output.exists_params_one_le_unboundedDiscOffset (f := f) out.out2

/-- Combined packaging: Stage 3 yields concrete parameters `d, m` such that the bundled offset
  discrepancy family `discOffset f d m` has arbitrarily large values.

This is the explicit witness-family form of `exists_params_unboundedDiscOffset`.
-/
theorem exists_params_forall_exists_discOffset_gt (out : Stage3Output f) :
    ∃ d m : ℕ, d > 0 ∧ (∀ B : ℕ, ∃ n : ℕ, B < discOffset f d m n) := by
  exact Stage2Output.exists_params_forall_exists_discOffset_gt (f := f) out.out2

/-- Variant of `exists_params_forall_exists_discOffset_gt` packaging the step-size side condition as `1 ≤ d`.

Many later stages prefer the normal form `1 ≤ d` rather than `d > 0`.
-/
theorem exists_params_one_le_forall_exists_discOffset_gt (out : Stage3Output f) :
    ∃ d m : ℕ, 1 ≤ d ∧ (∀ B : ℕ, ∃ n : ℕ, B < discOffset f d m n) := by
  exact Stage2Output.exists_params_one_le_forall_exists_discOffset_gt (f := f) out.out2

/-- Existential packaging: Stage 3 yields concrete parameters `d, m` such that the offset nucleus
`apSumOffset f d m n` takes arbitrarily large absolute values.

This is the raw-nucleus form of `exists_params_forall_exists_discOffset_gt`.
-/
theorem exists_params_forall_exists_natAbs_apSumOffset_gt (out : Stage3Output f) :
    ∃ d m : ℕ, d > 0 ∧
      (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f d m n)) := by
  exact Stage2Output.exists_params_forall_exists_natAbs_apSumOffset_gt (f := f) out.out2

/-- Stage 3 output yields bundled offset discrepancy witnesses for the concrete parameters
`d = out.out2.out1.d` and `m = out.out2.out1.m`.

This is a thin wrapper around the Stage-2 lemma `Stage2Output.forall_exists_discOffset_gt`.
-/
theorem forall_exists_discOffset_gt (out : Stage3Output f) :
    ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.out2.out1.d out.out2.out1.m n := by
  exact Stage2Output.forall_exists_discOffset_gt (f := f) out.out2

/-- Inequality-direction variant of `forall_exists_discOffset_gt`, written as `discOffset ... > B`.

Many consumers prefer this normal form so they can `simp [gt_iff_lt]` at the call site.
-/
theorem forall_exists_discOffset_gt' (out : Stage3Output f) :
    ∀ B : ℕ, ∃ n : ℕ, discOffset f out.out2.out1.d out.out2.out1.m n > B := by
  intro B
  rcases out.forall_exists_discOffset_gt (f := f) B with ⟨n, hn⟩
  exact ⟨n, by simpa [gt_iff_lt] using hn⟩

/-- Tail-nucleus witness form for the concrete Stage-1 parameters bundled in Stage 3.

This is just the Stage-2 witness `Stage2Output.forall_exists_natAbs_apSumFrom_mul_gt`, re-expressed
at the Stage-3 boundary.
-/
theorem forall_exists_natAbs_apSumFrom_mul_gt (out : Stage3Output f) :
    ∀ C : ℕ, ∃ n : ℕ,
      Int.natAbs (apSumFrom f (out.out2.out1.m * out.out2.out1.d) out.out2.out1.d n) > C := by
  simpa using (Stage2Output.forall_exists_natAbs_apSumFrom_mul_gt (f := f) out.out2)

/-- Stage 3 output implies there exist concrete parameters `d, m` such that the affine-tail nucleus
`apSumFrom f (m*d) d n` takes arbitrarily large absolute values.

This is a convenience wrapper around the Stage-2 packaging
`Stage2Output.exists_params_forall_exists_natAbs_apSumFrom_mul_gt`.
-/
theorem exists_params_forall_exists_natAbs_apSumFrom_mul_gt (out : Stage3Output f) :
    ∃ d m : ℕ, d > 0 ∧
      (∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  exact
    Stage2Output.exists_params_forall_exists_natAbs_apSumFrom_mul_gt (f := f) out.out2

/-- Variant of `exists_params_forall_exists_natAbs_apSumFrom_mul_gt` packaging the step-size side
condition as `1 ≤ d`.

Many later analytic stages prefer the normal form `1 ≤ d` rather than `d > 0`.
-/
theorem exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt (out : Stage3Output f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  exact
    Stage2Output.exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt (f := f) out.out2

end Stage3Output

/-!
## Stage 3 conjecture stub

This is the “single entry point” version of Stage 3: from a sign sequence, produce a Stage-3
output.

It is still a conjecture stub only because Stage 2 is a conjecture stub.
-/

noncomputable def stage3 (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage3Output f := by
  -- Run Stage 2, then close the global goal via the proved boundary lemma.
  exact (Stage3Output.ofStage2Output (f := f) (Tao2015.stage2 (f := f) (hf := hf)))

/-- Deterministic name for the Stage-3 output (useful to keep later statements readable). -/
noncomputable abbrev stage3Out (f : ℕ → ℤ) (hf : IsSignSequence f) : Stage3Output f :=
  stage3 (f := f) (hf := hf)

/-- Convenience projection: the reduced step size produced by Stage 3. -/
noncomputable abbrev stage3_d (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  (stage3Out (f := f) (hf := hf)).out2.out1.d

/-- Convenience projection: the reduced sequence produced by Stage 3. -/
noncomputable abbrev stage3_g (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ → ℤ :=
  (stage3Out (f := f) (hf := hf)).out2.out1.g

/-- Convenience projection: the bundled offset parameter produced by Stage 3. -/
noncomputable abbrev stage3_m (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  (stage3Out (f := f) (hf := hf)).out2.out1.m

/-- The reduced sequence produced by Stage 3 is a sign sequence. -/
theorem stage3_hg (f : ℕ → ℤ) (hf : IsSignSequence f) :
    IsSignSequence (stage3_g (f := f) (hf := hf)) := by
  simpa [stage3Out, stage3_g] using (stage3Out (f := f) (hf := hf)).out2.out1.hg

/-- Rewrite for the reduced sequence produced by Stage 3: it is a shift by `m*d`. -/
theorem stage3_g_eq (f : ℕ → ℤ) (hf : IsSignSequence f) (k : ℕ) :
    stage3_g (f := f) (hf := hf) k =
      f (k + (stage3_m (f := f) (hf := hf)) * (stage3_d (f := f) (hf := hf))) := by
  simpa [stage3Out, stage3_g, stage3_m, stage3_d] using
    (stage3Out (f := f) (hf := hf)).out2.out1.g_eq k

/-- Positivity of the reduced step size produced by Stage 3. -/
theorem stage3_hd (f : ℕ → ℤ) (hf : IsSignSequence f) : stage3_d (f := f) (hf := hf) > 0 := by
  simpa [stage3Out, stage3_d] using (stage3Out (f := f) (hf := hf)).out2.out1.hd

/-- Convenience lemma: the reduced step size produced by Stage 3 is at least `1`. -/
theorem stage3_one_le_d (f : ℕ → ℤ) (hf : IsSignSequence f) : 1 ≤ stage3_d (f := f) (hf := hf) := by
  simpa [stage3Out, stage3_d, Stage3Output.d] using
    (Stage3Output.one_le_d (f := f) (stage3Out (f := f) (hf := hf)))

/-- Convenience lemma: the reduced step size produced by Stage 3 is nonzero. -/
theorem stage3_d_ne_zero (f : ℕ → ℤ) (hf : IsSignSequence f) : stage3_d (f := f) (hf := hf) ≠ 0 := by
  simpa [stage3Out, stage3_d, Stage3Output.d] using
    (Stage3Output.d_ne_zero (f := f) (stage3Out (f := f) (hf := hf)))

/-- Consumer-facing shortcut: the Stage-3 pipeline closes the core goal `¬ BoundedDiscrepancy f`. -/
theorem stage3_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  exact (stage3Out (f := f) (hf := hf)).notBounded

/-- Consumer-facing shortcut: Stage 3 yields unbounded discrepancy along the reduced sequence,
stated using the verified core predicate `MoltResearch.UnboundedDiscrepancyAlong`.

This is a thin wrapper around `Stage2Output.unboundedDiscrepancyAlong_core`.
-/
theorem stage3_unboundedDiscrepancyAlong_core (f : ℕ → ℤ) (hf : IsSignSequence f) :
    MoltResearch.UnboundedDiscrepancyAlong (stage3_g (f := f) (hf := hf))
      (stage3_d (f := f) (hf := hf)) := by
  simpa [stage3Out, stage3_g, stage3_d, Stage2Output.g, Stage2Output.d] using
    (Stage2Output.unboundedDiscrepancyAlong_core (f := f) (stage3Out (f := f) (hf := hf)).out2)

/-- Consumer-facing shortcut: Stage 3 yields an unbounded bundled offset discrepancy family
`discOffset f d m`, at the concrete parameters produced by the pipeline.

This is a thin wrapper around `Stage3Output.unboundedDiscOffset`.
-/
theorem stage3_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    UnboundedDiscOffset f (stage3_d (f := f) (hf := hf)) (stage3_m (f := f) (hf := hf)) := by
  simpa [stage3Out, stage3_d, stage3_m] using
    (Stage3Output.unboundedDiscOffset (f := f) (stage3Out (f := f) (hf := hf)))

/-- Consumer-facing shortcut: Stage 3 yields the usual surface statement `∀ C, HasDiscrepancyAtLeast f C`.

This is a thin wrapper around `Stage3Output.forall_hasDiscrepancyAtLeast`.
-/
theorem stage3_forall_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  simpa using
    (Stage3Output.forall_hasDiscrepancyAtLeast (f := f) (stage3 (f := f) (hf := hf)))

/-- Consumer-facing shortcut: Stage 3 yields the most pipeline-friendly global witness form:

`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is a thin wrapper around `Stage3Output.forall_exists_d_ge_one_witness_pos`.
-/
theorem stage3_forall_exists_d_ge_one_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  simpa using
    (Stage3Output.forall_exists_d_ge_one_witness_pos (f := f) (stage3 (f := f) (hf := hf)))

/-- Consumer-facing shortcut: Stage 3 yields a global witness form with the step-size condition
written as `d > 0`:

`∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is a thin wrapper around `Stage3Output.forall_exists_d_pos_witness_pos`.
-/
theorem stage3_forall_exists_d_pos_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  simpa using
    (Stage3Output.forall_exists_d_pos_witness_pos (f := f) (stage3 (f := f) (hf := hf)))

/-- Consumer-facing shortcut: Stage 3 yields concrete parameters `d, m` with `1 ≤ d` such that the
affine-tail nucleus `apSumFrom f (m*d) d n` takes arbitrarily large absolute values.

This is a thin wrapper around `Stage3Output.exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt`.
-/
theorem stage3_exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  simpa [stage3Out] using
    (Stage3Output.exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt (f := f)
      (stage3 (f := f) (hf := hf)))

end Tao2015

end MoltResearch
