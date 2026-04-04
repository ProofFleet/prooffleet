import Conjectures.C0002_erdos_discrepancy.src.TrackCStage3
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Output

/-!
# Track C: Stage 3 output lemmas (Tao 2015 plane)

This file contains the proved convenience lemmas about `Tao2015.Stage3Output`.

We keep `Conjectures.C0002_erdos_discrepancy.src.TrackCStage3` intentionally small so the Track-C
hard-gate build for `Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy` compiles quickly.
-/

namespace MoltResearch

namespace Tao2015

namespace Stage3Output

variable {f : ℕ → ℤ}

/-- Alias for the packaged global conclusion, matching Stage-2 naming.

Stage 2 calls this statement `Stage2Output.notBoundedOriginal`; Stage 3 stores it as a field
`out.notBounded`. This alias lets downstream code use a consistent name at both boundaries.
-/
abbrev notBoundedOriginal (out : Stage3Output f) : ¬ BoundedDiscrepancy f :=
  out.notBounded

/-- Convenience projection: the reduced step size packaged in Stage 3.

We intentionally route this through the Stage-2 boundary API (`Stage2Output.d`) so Stage 3 does not
depend on Stage-1 record fields.
-/
abbrev d (out : Stage3Output f) : ℕ := out.out2.d

/-- Convenience projection: the reduced sequence packaged in Stage 3.

We intentionally route this through the Stage-2 boundary API (`Stage2Output.g`) so Stage 3 does not
depend on Stage-1 record fields.
-/
abbrev g (out : Stage3Output f) : ℕ → ℤ := out.out2.g

/-- The reduced sequence packaged in Stage 3 is a sign sequence. -/
theorem hg (out : Stage3Output f) : IsSignSequence out.g := by
  simpa [Stage3Output.g] using (Stage2Output.hg (f := f) out.out2)

/-- Stage 3 retains the Stage-2 reduced-step unboundedness witness.

This is a tiny convenience projection so consumers of `Stage3Output` do not have to reach into the
nested Stage-2 record field `out.out2.unbounded`.
-/
abbrev unboundedReducedAlong (out : Stage3Output f) :
    Tao2015.UnboundedDiscrepancyAlong out.g out.d :=
  out.out2.unbounded

/-- Convenience projection: the bundled offset parameter packaged in Stage 3. -/
abbrev m (out : Stage3Output f) : ℕ := out.out2.m

/-- Rewrite for the reduced sequence packaged in Stage 3: it is a shift by `m*d`. -/
theorem g_eq (out : Stage3Output f) (k : ℕ) :
    out.g k = f (k + out.m * out.d) := by
  simpa [Stage3Output.g, Stage3Output.m, Stage3Output.d] using
    (Stage2Output.g_eq (f := f) out.out2 k)

/-- Convenience projection: positivity of the reduced step size. -/
abbrev hd (out : Stage3Output f) : out.d > 0 := out.out2.hd

/-- Convenience lemma: the reduced step size is nonzero.

We intentionally delegate this to the Stage-2 boundary API lemma (`Stage2Output.d_ne_zero`), so
Stage 3 doesn't re-prove arithmetic facts about its projections.
-/
theorem d_ne_zero (out : Stage3Output f) : out.d ≠ 0 := by
  simpa [Stage3Output.d] using (Stage2Output.d_ne_zero (f := f) out.out2)

/-- Convenience lemma: the reduced step size is at least `1`.

We intentionally delegate this to the Stage-2 boundary API lemma (`Stage2Output.one_le_d`).
-/
theorem one_le_d (out : Stage3Output f) : 1 ≤ out.d := by
  simpa [Stage3Output.d] using (Stage2Output.one_le_d (f := f) out.out2)

/-- Stage 3 output implies the nucleus witness form

`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is the most pipeline-friendly surface statement for consuming Stage 3.
-/
theorem forall_exists_d_ge_one_witness_pos (out : Stage3Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact Stage2Output.forall_exists_d_ge_one_witness_pos (f := f) out.out2

/-- Variant of `forall_exists_d_ge_one_witness_pos` with the step-size side condition written as
`d > 0`.

Many consumers prefer the strict-positivity normal form when working with `Nat` step sizes.
-/
theorem forall_exists_d_pos_witness_pos (out : Stage3Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact Stage2Output.forall_exists_d_pos_witness_pos (f := f) out.out2

/-- Stage 3 output implies the paper-notation witness form

`∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ Int.natAbs (∑ i ∈ Icc 1 n, f (i*d)) > C`.

This is a thin wrapper around `Stage3Output.forall_hasDiscrepancyAtLeast` via
`forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos`.
-/
theorem forall_exists_sum_Icc_witness_pos (out : Stage3Output f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧
      Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos f).1
      (out.forall_hasDiscrepancyAtLeast (f := f))

/-- Stage 3 yields unbounded fixed-step discrepancy for the reduced sequence, expressed using the
verified core predicate `MoltResearch.UnboundedDiscrepancyAlong`.

This is a small convenience wrapper around the Stage-2 bridge lemma
`Stage2Output.unboundedDiscrepancyAlong_core`.
-/
theorem unboundedDiscrepancyAlong_core (out : Stage3Output f) :
    MoltResearch.UnboundedDiscrepancyAlong out.g out.d := by
  simpa [Stage3Output.g, Stage3Output.d] using
    (Stage2Output.unboundedDiscrepancyAlong_core (f := f) out.out2)

/-- Stage 3 implies the reduced sequence is not bounded along its fixed step size. -/
theorem notBoundedReducedAlong (out : Stage3Output f) : ¬ BoundedDiscrepancyAlong out.g out.d := by
  simpa [Stage3Output.g, Stage3Output.d] using
    (Stage2Output.notBoundedReducedAlong (f := f) out.out2)

/-- Stage 3 output yields unboundedness of the bundled offset discrepancy family
`discOffset f d m` at the concrete parameters coming from Stage 1.

This is a thin wrapper around `Stage2Output.unboundedDiscOffset`.
-/
theorem unboundedDiscOffset (out : Stage3Output f) :
    UnboundedDiscOffset f out.d out.m := by
  simpa [Stage3Output.d, Stage3Output.m] using
    (Stage2Output.unboundedDiscOffset (f := f) out.out2)

/-- Negation-normal-form: there is no uniform bound on the bundled offset discrepancy family
`discOffset f out.d out.m`.

This is a thin wrapper around `Stage2Output.not_exists_boundedDiscOffset`.
-/
theorem not_exists_boundedDiscOffset (out : Stage3Output f) :
    ¬ ∃ B : ℕ, BoundedDiscOffset f out.d out.m B := by
  simpa [Stage3Output.d, Stage3Output.m] using
    (Stage2Output.not_exists_boundedDiscOffset (f := f) out.out2)

/-- Negation-normal-form unboundedness statement for the bundled offset nuclei
`Int.natAbs (apSumOffset f out.d out.m n)`.

This is a thin wrapper around `Stage2Output.not_exists_forall_natAbs_apSumOffset_le`.
-/
theorem not_exists_forall_natAbs_apSumOffset_le (out : Stage3Output f) :
    ¬ ∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ B := by
  simpa [Stage3Output.d, Stage3Output.m] using
    (Stage2Output.not_exists_forall_natAbs_apSumOffset_le (f := f) out.out2)

/-- Nucleus witness form for the concrete Stage-1 parameters bundled in Stage 3.

This is `unboundedDiscOffset` rewritten so consumers can work directly with
`Int.natAbs (apSumOffset f d m n)` without unfolding `discOffset`.
-/
theorem forall_exists_natAbs_apSumOffset_gt (out : Stage3Output f) :
    ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n) := by
  simpa [Stage3Output.d, Stage3Output.m] using
    (Stage2Output.forall_exists_natAbs_apSumOffset_gt (f := f) out.out2)

/-- Inequality-direction variant of `forall_exists_natAbs_apSumOffset_gt`, written as
`Int.natAbs ... > B`.

Many consumers prefer this normal form so they can `simp [gt_iff_lt]` at the call site.
-/
theorem forall_exists_natAbs_apSumOffset_gt' (out : Stage3Output f) :
    ∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) > B := by
  simpa [Stage3Output.d, Stage3Output.m] using
    (Stage2Output.forall_exists_natAbs_apSumOffset_gt' (f := f) out.out2)

/-- Existential packaging: Stage 3 yields concrete parameters `d, m` with `1 ≤ d` such that the
offset nucleus `apSumOffset f d m n` takes arbitrarily large absolute values.

This is a small wrapper around `forall_exists_natAbs_apSumOffset_gt'`.
-/
theorem exists_params_one_le_forall_exists_natAbs_apSumOffset_gt (out : Stage3Output f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumOffset f d m n) > B) := by
  refine ⟨out.d, out.m, out.one_le_d (f := f), ?_⟩
  intro B
  simpa using out.forall_exists_natAbs_apSumOffset_gt' (f := f) B

/-- Tail-nucleus witness form for the concrete Stage-1 parameters bundled in Stage 3.

This is the Stage-2 witness `Stage2Output.forall_exists_natAbs_apSumFrom_mul_gt`, re-expressed
at the Stage-3 boundary.
-/
theorem forall_exists_natAbs_apSumFrom_mul_gt (out : Stage3Output f) :
    ∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > C := by
  simpa [Stage3Output.d, Stage3Output.m] using
    (Stage2Output.forall_exists_natAbs_apSumFrom_mul_gt (f := f) out.out2)

/-- Existential packaging: Stage 3 yields concrete parameters `d, m` with `1 ≤ d` such that the
affine-tail nucleus `apSumFrom f (m*d) d n` takes arbitrarily large absolute values.

This is a thin wrapper around `forall_exists_natAbs_apSumFrom_mul_gt`.
-/
theorem exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt (out : Stage3Output f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  refine ⟨out.d, out.m, out.one_le_d (f := f), ?_⟩
  intro C
  simpa [Stage3Output.d, Stage3Output.m] using out.forall_exists_natAbs_apSumFrom_mul_gt (f := f) C

/-- Negation-normal form of `forall_exists_natAbs_apSumFrom_mul_gt`: there is no uniform bound on
the affine-tail nuclei at the concrete Stage-1 parameters bundled in Stage 3.

This is a thin wrapper around `Stage2Output.not_exists_forall_natAbs_apSumFrom_mul_le`.
-/
theorem not_exists_forall_natAbs_apSumFrom_mul_le (out : Stage3Output f) :
    ¬ ∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) ≤ B := by
  simpa [Stage3Output.d, Stage3Output.m] using
    (Stage2Output.not_exists_forall_natAbs_apSumFrom_mul_le (f := f) out.out2)

end Stage3Output

end Tao2015

end MoltResearch
