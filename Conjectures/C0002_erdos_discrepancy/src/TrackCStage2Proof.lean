import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Core
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry

/-!
# Track C: Stage 2 proof stub (Tao 2015 plane)

This file contains only the Stage-2 convenience projections/wrapper lemmas.

The Stage-2 conjecture stub (axiom) itself lives in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry`.

Implementation note: we intentionally avoid importing the large Stage-2 convenience-lemma library
(`TrackCStage2Output.lean`).  The wrappers here are proved directly from the `Stage2Output` fields
plus the Stage-1 transport lemmas on `ReductionOutput`, and we only depend on the tiny proved core
lemmas in `TrackCStage2Core.lean`.
-/

namespace MoltResearch

namespace Tao2015

/-!
The Stage-2 conjecture stub (axiom) and the deterministic name `stage2Out` live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry`.

This file keeps only the convenience projections/wrapper lemmas.
-/

/-
Note: the basic projections `stage2_d`, `stage2_g`, `stage2_m` are defined in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry` so hard-gate consumers can access them
without importing this wrapper-lemma module.
-/

/-- The reduced sequence produced by Stage 2 is a sign sequence. -/
theorem stage2_hg (f : ℕ → ℤ) (hf : IsSignSequence f) :
    IsSignSequence (stage2_g (f := f) (hf := hf)) := by
  simpa [stage2_g] using (stage2Out (f := f) (hf := hf)).hg

/-- Rewrite for the reduced sequence produced by Stage 2: it is a shift by `m*d`. -/
theorem stage2_g_eq (f : ℕ → ℤ) (hf : IsSignSequence f) (k : ℕ) :
    stage2_g (f := f) (hf := hf) k =
      f (k + (stage2_m (f := f) (hf := hf)) * (stage2_d (f := f) (hf := hf))) := by
  simpa [stage2_g, stage2_m, stage2_d] using (stage2Out (f := f) (hf := hf)).g_eq k

/-- Positivity of the reduced step size produced by Stage 2. -/
theorem stage2_hd (f : ℕ → ℤ) (hf : IsSignSequence f) : stage2_d (f := f) (hf := hf) > 0 := by
  simpa [stage2_d] using (stage2Out (f := f) (hf := hf)).hd

/-- Convenience lemma: the reduced step size produced by Stage 2 is at least `1`. -/
theorem stage2_one_le_d (f : ℕ → ℤ) (hf : IsSignSequence f) :
    1 ≤ stage2_d (f := f) (hf := hf) := by
  simpa [stage2_d] using (stage2Out (f := f) (hf := hf)).one_le_d

/-- Convenience lemma: the reduced step size produced by Stage 2 is nonzero. -/
theorem stage2_d_ne_zero (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage2_d (f := f) (hf := hf) ≠ 0 := by
  simpa [stage2_d] using (stage2Out (f := f) (hf := hf)).d_ne_zero

/-
Note: the boundedness-negation normal form lemma

  stage2_notBounded (f) (hf) : ¬ BoundedDiscrepancy f

is defined in `TrackCStage2Entry.lean` (the entry-point module), so hard-gate consumers can access
it without importing this wrapper-lemma module.
-/

/-- Consumer-facing shortcut: Stage 2 yields the usual surface statement
`∀ C, HasDiscrepancyAtLeast f C`.

This is a thin wrapper around the proved Stage-2 core lemma
`Stage2Output.forall_hasDiscrepancyAtLeast`.
-/
theorem stage2_forall_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  exact Stage2Output.forall_hasDiscrepancyAtLeast (f := f) (stage2Out (f := f) (hf := hf))

/-- Consumer-facing shortcut: Stage 2 yields the most pipeline-friendly global witness form:

`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is a thin wrapper around the proved Stage-2 core lemma
`Stage2Output.forall_exists_d_ge_one_witness_pos`.
-/
theorem stage2_forall_exists_d_ge_one_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact
    Stage2Output.forall_exists_d_ge_one_witness_pos (f := f) (stage2Out (f := f) (hf := hf))

/-- Consumer-facing tail-nucleus witness form: Stage 2 yields arbitrarily large affine-tail nuclei
`apSumFrom f (m*d) d n` at the concrete parameters produced by the conjecture stub `stage2Out`.

We derive this directly from the Stage-1 transport equivalence on the bundled `ReductionOutput`.
-/
theorem stage2_forall_exists_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ,
      ∃ n : ℕ,
        Int.natAbs
            (apSumFrom f
              (stage2_m (f := f) (hf := hf) * stage2_d (f := f) (hf := hf))
              (stage2_d (f := f) (hf := hf)) n) > C := by
  simpa [stage2_m, stage2_d] using
    ((stage2Out (f := f) (hf := hf)).out1.unboundedDiscrepancyAlong_iff_forall_exists_natAbs_apSumFrom_mul_gt
          (f := f)).1
      (stage2Out (f := f) (hf := hf)).unbounded

/- Note: `stage2_unboundedDiscOffset` is defined in `TrackCStage2Entry` so that consumers can
access it without importing this wrapper-lemma module. -/

/-- Positive-length witness form of `stage2_forall_exists_natAbs_apSumFrom_mul_gt`.

The witness length `n` cannot be `0`, since `apSumFrom ... 0 = 0`.

This is a thin wrapper around the Conjectures-only normal-form lemma
`Tao2015.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos`.
-/
theorem stage2_forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∀ C : ℕ,
      ∃ n : ℕ, n > 0 ∧
        Int.natAbs
            (apSumFrom f
              (stage2_m (f := f) (hf := hf) * stage2_d (f := f) (hf := hf))
              (stage2_d (f := f) (hf := hf)) n) > C := by
  have hunb :
      UnboundedDiscOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) :=
    stage2_unboundedDiscOffset (f := f) (hf := hf)
  simpa [stage2_m, stage2_d] using
    (Tao2015.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f := f)
      (d := stage2_d (f := f) (hf := hf)) (m := stage2_m (f := f) (hf := hf)) hunb)

/-- Consumer-facing shortcut: Stage 2 yields raw offset-nucleus witnesses at the concrete
parameters produced by the conjecture stub `stage2Out`.

Normal form:
`∀ B, ∃ n, discOffset f d m n > B`,
where `d = stage2_d` and `m = stage2_m`.

This is a thin wrapper around the Stage-1 transport equivalence
`ReductionOutput.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt'`.
-/
theorem stage2_forall_exists_discOffset_gt' (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ,
        discOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) n > B := by
  simpa [stage2_d, stage2_m] using
    ((stage2Out (f := f) (hf := hf)).out1.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt'
          (f := f)).1
      (stage2Out (f := f) (hf := hf)).unbounded

/-- Positive-length witness form of `stage2_forall_exists_discOffset_gt'`.

The witness length `n` cannot be `0`, since `discOffset ... 0 = 0`.
-/
theorem stage2_forall_exists_discOffset_gt'_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ,
        n > 0 ∧ discOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) n > B := by
  have hunb :
      UnboundedDiscOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) :=
    stage2_unboundedDiscOffset (f := f) (hf := hf)
  simpa using
    (UnboundedDiscOffset.forall_exists_discOffset_gt'_witness_pos (f := f)
      (d := stage2_d (f := f) (hf := hf)) (m := stage2_m (f := f) (hf := hf)) hunb)

/-- Consumer-facing shortcut: Stage 2 yields raw offset-nucleus witnesses at the concrete
parameters produced by the conjecture stub `stage2Out`, stated using the bundled offset nucleus.

Normal form:
`∀ B, ∃ n, Int.natAbs (apSumOffset f d m n) > B`,
where `d = stage2_d` and `m = stage2_m`.

This is a thin wrapper around the normal-form lemma
`UnboundedDiscOffset.iff_forall_exists_natAbs_apSumOffset_gt'`.
-/
theorem stage2_forall_exists_natAbs_apSumOffset_gt' (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ,
        Int.natAbs
            (apSumOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) n) > B := by
  simpa using
    (UnboundedDiscOffset.iff_forall_exists_natAbs_apSumOffset_gt' (f := f)
          (d := stage2_d (f := f) (hf := hf)) (m := stage2_m (f := f) (hf := hf))).1
      (stage2_unboundedDiscOffset (f := f) (hf := hf))

/-- Positive-length witness form of `stage2_forall_exists_natAbs_apSumOffset_gt'`.

The witness length `n` cannot be `0`, since `apSumOffset ... 0 = 0`.
-/
theorem stage2_forall_exists_natAbs_apSumOffset_gt'_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ, n > 0 ∧
        Int.natAbs
            (apSumOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) n) > B := by
  have hunb :
      UnboundedDiscOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) :=
    stage2_unboundedDiscOffset (f := f) (hf := hf)
  simpa using
    (UnboundedDiscOffset.forall_exists_natAbs_apSumOffset_gt_witness_pos (hunb := hunb))

/-!
Consumer code should usually use `stage2Out` together with the general lemmas about `Stage2Output`
(from `TrackCStage2.lean` / `TrackCStage2Output.lean`).

We intentionally avoid duplicating wrapper lemmas here, so this file remains a pure conjecture stub
plus projections.
-/

end Tao2015

end MoltResearch
