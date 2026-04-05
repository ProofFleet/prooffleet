import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3Entry
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3Output

/-!
# Track C: Stage 3 conjecture stub (Tao 2015 plane)

This file is **Conjectures-only** glue.

It provides the "single entry point" version of Stage 3: from a sign sequence, produce a Stage-3
output.

It is still a conjecture stub only because Stage 2 is a conjecture stub.

The Stage-3 record interface and its proved boundary lemmas live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage3`.
-/

namespace MoltResearch

namespace Tao2015

-- (Moved to `TrackCStage3Entry.lean` so the hard-gate build can avoid compiling wrapper lemmas.)

/-- Convenience projection: the reduced step size produced by Stage 3. -/
noncomputable abbrev stage3_d (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  (stage3Out (f := f) (hf := hf)).d

/-- Convenience projection: the reduced sequence produced by Stage 3. -/
noncomputable abbrev stage3_g (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ → ℤ :=
  (stage3Out (f := f) (hf := hf)).g

/-- Convenience projection: the bundled offset parameter produced by Stage 3. -/
noncomputable abbrev stage3_m (f : ℕ → ℤ) (hf : IsSignSequence f) : ℕ :=
  (stage3Out (f := f) (hf := hf)).m

/-- The reduced sequence produced by Stage 3 is a sign sequence. -/
theorem stage3_hg (f : ℕ → ℤ) (hf : IsSignSequence f) :
    IsSignSequence (stage3_g (f := f) (hf := hf)) := by
  simpa [stage3_g] using
    (Stage3Output.hg (f := f) (stage3Out (f := f) (hf := hf)))

/-- Rewrite for the reduced sequence produced by Stage 3: it is a shift by `m*d`. -/
theorem stage3_g_eq (f : ℕ → ℤ) (hf : IsSignSequence f) (k : ℕ) :
    stage3_g (f := f) (hf := hf) k =
      f (k + (stage3_m (f := f) (hf := hf)) * (stage3_d (f := f) (hf := hf))) := by
  -- Prefer the Stage-3 boundary lemma.
  simpa [stage3_g, stage3_m, stage3_d] using
    (Stage3Output.g_eq (f := f) (stage3Out (f := f) (hf := hf)) k)

/-- Positivity of the reduced step size produced by Stage 3. -/
theorem stage3_hd (f : ℕ → ℤ) (hf : IsSignSequence f) : stage3_d (f := f) (hf := hf) > 0 := by
  -- Prefer the Stage-3 boundary API lemma.
  simpa [stage3_d] using
    (Stage3Output.hd (f := f) (stage3Out (f := f) (hf := hf)))

/-- Convenience lemma: the reduced step size produced by Stage 3 is at least `1`. -/
theorem stage3_one_le_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    1 ≤ stage3_d (f := f) (hf := hf) := by
  simpa [stage3_d] using
    (Stage3Output.one_le_d (f := f) (stage3Out (f := f) (hf := hf)))

/-- Convenience lemma: the reduced step size produced by Stage 3 is nonzero. -/
theorem stage3_d_ne_zero (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage3_d (f := f) (hf := hf) ≠ 0 := by
  simpa [stage3_d] using
    (Stage3Output.d_ne_zero (f := f) (stage3Out (f := f) (hf := hf)))

/-- Consumer-facing shortcut: the Stage-3 pipeline closes the core goal `¬ BoundedDiscrepancy f`. -/
theorem stage3_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  exact (stage3Out (f := f) (hf := hf)).notBounded

/-- Consumer-facing shortcut: Stage 3 yields unbounded discrepancy along the reduced sequence,
stated using the verified core predicate `MoltResearch.UnboundedDiscrepancyAlong`.

This is a thin wrapper around the proved Stage-3 boundary lemma
`Stage3Output.unboundedDiscrepancyAlong_core`.
-/
theorem stage3_unboundedDiscrepancyAlong_core (f : ℕ → ℤ) (hf : IsSignSequence f) :
    MoltResearch.UnboundedDiscrepancyAlong (stage3_g (f := f) (hf := hf))
      (stage3_d (f := f) (hf := hf)) := by
  simpa [stage3_g, stage3_d] using
    (Stage3Output.unboundedDiscrepancyAlong_core (f := f) (stage3Out (f := f) (hf := hf)))

/-- Consumer-facing shortcut: Stage 3 yields an unbounded bundled offset discrepancy family
`discOffset f d m`, at the concrete parameters produced by the pipeline.

This is a thin wrapper around `Stage3Output.unboundedDiscOffset`.
-/
theorem stage3_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    UnboundedDiscOffset f (stage3_d (f := f) (hf := hf)) (stage3_m (f := f) (hf := hf)) := by
  simpa [stage3_d, stage3_m] using
    (Stage3Output.unboundedDiscOffset (f := f) (stage3Out (f := f) (hf := hf)))

/-- Consumer-facing shortcut: Stage 3 yields raw offset-nucleus witnesses at the concrete
parameters produced by the pipeline.

Normal form:
`∀ B, ∃ n, Int.natAbs (apSumOffset f d m n) > B`,
where `d = stage3_d` and `m = stage3_m`.

This is a thin wrapper around `Stage3Output.forall_exists_natAbs_apSumOffset_gt'`.
-/
theorem stage3_forall_exists_natAbs_apSumOffset_gt' (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ, ∃ n : ℕ,
      Int.natAbs
          (apSumOffset f (stage3_d (f := f) (hf := hf)) (stage3_m (f := f) (hf := hf)) n) > B := by
  simpa [stage3_d, stage3_m] using
    (Stage3Output.forall_exists_natAbs_apSumOffset_gt' (f := f) (stage3Out (f := f) (hf := hf)))

/-- Consumer-facing shortcut: Stage 3 yields explicit affine-tail nucleus witnesses at the
concrete parameters produced by the pipeline.

Normal form:
`∀ C, ∃ n, Int.natAbs (apSumFrom f (m*d) d n) > C`,
where `d = stage3_d` and `m = stage3_m`.

This is a thin wrapper around `Stage3Output.forall_exists_natAbs_apSumFrom_mul_gt`.
-/
theorem stage3_forall_exists_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ n : ℕ,
      Int.natAbs
          (apSumFrom f ((stage3_m (f := f) (hf := hf)) * (stage3_d (f := f) (hf := hf)))
            (stage3_d (f := f) (hf := hf)) n) > C := by
  simpa [stage3_d, stage3_m] using
    (Stage3Output.forall_exists_natAbs_apSumFrom_mul_gt (f := f) (stage3Out (f := f) (hf := hf)))

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

This is a thin wrapper around the Stage-3 boundary API lemma
`Stage3Output.exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt`.
-/
theorem stage3_exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  simpa using
    (Stage3Output.exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt (f := f)
      (stage3Out (f := f) (hf := hf)))

/-- Consumer-facing shortcut: Stage 3 yields concrete parameters `d, m` with `1 ≤ d` such that the
bundled offset nucleus `apSumOffset f d m n` takes arbitrarily large absolute values.

Normal form:
`∃ d m, 1 ≤ d ∧ ∀ B, ∃ n, Int.natAbs (apSumOffset f d m n) > B`.

This is a thin wrapper around the Stage-3 boundary API lemma
`Stage3Output.exists_params_one_le_forall_exists_natAbs_apSumOffset_gt`.
-/
theorem stage3_exists_params_one_le_forall_exists_natAbs_apSumOffset_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumOffset f d m n) > B) := by
  simpa using
    (Stage3Output.exists_params_one_le_forall_exists_natAbs_apSumOffset_gt (f := f)
      (stage3Out (f := f) (hf := hf)))

end Tao2015

end MoltResearch
