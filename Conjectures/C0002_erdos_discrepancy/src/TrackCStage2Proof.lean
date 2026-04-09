import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Output

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

/-!
## Small consumer-facing wrappers about `stage2Out`

We keep `TrackCStage2Entry` minimal (just the axiom stub and projections).  This module provides a
small set of proved, pipeline-friendly convenience lemmas about the deterministic output
`stage2Out`.
-/

/-
Note: the tiny side-condition lemmas `stage2_d_pos`, `stage2_one_le_d`, and `stage2_d_ne_zero` are
defined in `Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry` so hard-gate consumers can
access them without importing this wrapper-lemma module.
-/

/-- Minimal consumer-facing Stage-2 consequence: the original sequence cannot have globally bounded
(discrepancy) once Stage 2 produces an unbounded fixed-step witness along the reduced sequence. -/
theorem stage2_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  exact (stage2Out (f := f) (hf := hf)).notBoundedOriginal

/-- Consumer-facing shortcut: Stage 2 yields the usual surface statement
`∀ C, HasDiscrepancyAtLeast f C`.

This is a thin wrapper around `Stage2Output.forall_hasDiscrepancyAtLeast`.
-/
theorem stage2_forall_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  exact (stage2Out (f := f) (hf := hf)).forall_hasDiscrepancyAtLeast

/-- Minimal consumer-facing Stage-2 consequence: Stage 2 yields an unbounded bundled offset
discrepancy family `discOffset f d m` at the deterministic parameters produced by `stage2Out`. -/
theorem stage2_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    UnboundedDiscOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) := by
  simpa [stage2_d, stage2_m, Stage2Output.d, Stage2Output.m] using
    (stage2Out (f := f) (hf := hf)).unboundedDiscOffset (f := f)

/-- Existential packaging: Stage 2 yields concrete parameters `d, m` with `1 ≤ d` such that the
bundled offset discrepancy family `discOffset f d m` is unbounded. -/
theorem stage2_exists_params_one_le_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ UnboundedDiscOffset f d m := by
  refine ⟨stage2_d (f := f) (hf := hf), stage2_m (f := f) (hf := hf),
    stage2_one_le_d (f := f) (hf := hf), ?_⟩
  exact stage2_unboundedDiscOffset (f := f) (hf := hf)

-- Note: the tiny projection lemmas `stage2_hg` and `stage2_g_eq` live in
-- `Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry` so hard-gate consumers can use them
-- without importing this wrapper-lemma module.

/-- Function-level rewrite for `stage2_g`: it is the shifted sequence `fun k => f (k + m*d)`. -/
theorem stage2_g_eq_fun (f : ℕ → ℤ) (hf : IsSignSequence f) :
    stage2_g (f := f) (hf := hf) =
      fun k => f (k + stage2_start (f := f) (hf := hf)) := by
  funext k
  simpa using stage2_g_eq (f := f) (hf := hf) k

/-!
## Additional witness-form wrappers
-/

/-- Consumer-facing shortcut: Stage 2 yields the most pipeline-friendly global witness form:

`∀ C, ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is a thin wrapper around the proved Stage-2 core lemma
`Stage2Output.forall_exists_d_ge_one_witness_pos`.
-/
theorem stage2_forall_exists_d_ge_one_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact
    Stage2Output.forall_exists_d_ge_one_witness_pos (f := f) (stage2Out (f := f) (hf := hf))

/-- Consumer-facing shortcut: Stage 2 yields a global witness form with the step-size condition
written as `d > 0`:

`∀ C, ∃ d n, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is a thin wrapper around the proved Stage-2 core lemma
`Stage2Output.forall_exists_d_pos_witness_pos`.
-/
theorem stage2_forall_exists_d_pos_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact
    Stage2Output.forall_exists_d_pos_witness_pos (f := f) (stage2Out (f := f) (hf := hf))

/-- Consumer-facing shortcut: Stage 2 yields a global witness form with the step-size condition
written as `d ≠ 0`:

`∀ C, ∃ d n, d ≠ 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C`.

This is a thin wrapper around the proved Stage-2 core lemma
`Stage2Output.forall_exists_d_ne_zero_witness_pos`.
-/
theorem stage2_forall_exists_d_ne_zero_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≠ 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact
    Stage2Output.forall_exists_d_ne_zero_witness_pos (f := f) (stage2Out (f := f) (hf := hf))

/-- Consumer-facing tail-nucleus witness form: Stage 2 yields arbitrarily large affine-tail nuclei
`apSumFrom f (m*d) d n` at the concrete parameters produced by the conjecture stub `stage2Out`.

We derive this directly from the Stage-1 transport equivalence on the bundled `ReductionOutput`.
-/
theorem stage2_forall_exists_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ,
      ∃ n : ℕ,
        Int.natAbs
            (apSumFrom f (stage2_start (f := f) (hf := hf)) (stage2_d (f := f) (hf := hf)) n) > C := by
  simpa [stage2_start, stage2_m, stage2_d] using
    (Stage2Output.forall_exists_natAbs_apSumFrom_mul_gt (f := f)
      (out := stage2Out (f := f) (hf := hf)))

/-- Negation-normal-form tail-nucleus statement: Stage 2 yields no uniform bound on the affine-tail
nuclei `Int.natAbs (apSumFrom f (m*d) d n)` at the concrete parameters produced by `stage2Out`.

This is often the most convenient form for contradiction arguments in later stages.
-/
theorem stage2_not_exists_forall_natAbs_apSumFrom_mul_le (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ,
        ∀ n : ℕ,
          Int.natAbs
              (apSumFrom f (stage2_start (f := f) (hf := hf)) (stage2_d (f := f) (hf := hf)) n) ≤ B := by
  simpa [stage2_start, stage2_m, stage2_d] using
    (Stage2Output.not_exists_forall_natAbs_apSumFrom_mul_le (f := f)
      (out := stage2Out (f := f) (hf := hf)))


/- Note: `stage2_unboundedDiscOffset` is defined in this module as a wrapper around the Stage-2 core lemma `Stage2Output.unboundedDiscOffset`. -/


/-- Positive-length witness form of `stage2_forall_exists_natAbs_apSumFrom_mul_gt`. 

The witness length `n` cannot be `0`, since `apSumFrom ... 0 = 0`.

This is a thin wrapper around the Conjectures-only normal-form lemma
`UnboundedDiscOffset.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos`.
-/
theorem stage2_forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∀ C : ℕ,
      ∃ n : ℕ, n > 0 ∧
        Int.natAbs
            (apSumFrom f (stage2_start (f := f) (hf := hf)) (stage2_d (f := f) (hf := hf)) n) > C := by
  simpa [stage2_start, stage2_m, stage2_d] using
    (Stage2Output.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f := f)
      (out := stage2Out (f := f) (hf := hf)))

/-- Existential packaging: Stage 2 yields concrete parameters `d, m` with `1 ≤ d` such that the
affine-tail nucleus `apSumFrom f (m*d) d n` takes arbitrarily large absolute values.

Normal form:
`∃ d m, 1 ≤ d ∧ ∀ C, ∃ n, Int.natAbs (apSumFrom f (m*d) d n) > C`.

This is a thin wrapper around `stage2_forall_exists_natAbs_apSumFrom_mul_gt`.
-/
theorem stage2_exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ C : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  refine ⟨stage2_d (f := f) (hf := hf), stage2_m (f := f) (hf := hf),
    stage2_one_le_d (f := f) (hf := hf), ?_⟩
  intro C
  simpa using stage2_forall_exists_natAbs_apSumFrom_mul_gt (f := f) (hf := hf) C

/-- Existential packaging: Stage 2 yields concrete parameters `d, m` with `1 ≤ d` such that the
affine-tail nucleus `apSumFrom f (m*d) d n` takes arbitrarily large absolute values, with a
positive-length witness `n > 0`.

Normal form:
`∃ d m, 1 ≤ d ∧ ∀ C, ∃ n, n > 0 ∧ Int.natAbs (apSumFrom f (m*d) d n) > C`.

This is a thin wrapper around `stage2_forall_exists_natAbs_apSumFrom_mul_gt_witness_pos`.
-/
theorem stage2_exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ C : ℕ, ∃ n : ℕ, n > 0 ∧ Int.natAbs (apSumFrom f (m * d) d n) > C) := by
  refine ⟨stage2_d (f := f) (hf := hf), stage2_m (f := f) (hf := hf),
    stage2_one_le_d (f := f) (hf := hf), ?_⟩
  simpa using stage2_forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f := f) (hf := hf)

/-- Consumer-facing shortcut: Stage 2 yields raw offset-nucleus witnesses at the concrete
parameters produced by the conjecture stub `stage2Out`.

Normal form:
`∀ B, ∃ n, B < discOffset f d m n`,
where `d = stage2_d` and `m = stage2_m`.

This is a thin wrapper around the Stage-1 transport equivalence
`ReductionOutput.unboundedDiscrepancyAlong_iff_forall_exists_discOffset_gt`.
-/
theorem stage2_forall_exists_discOffset_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ,
        B < discOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) n := by
  simpa [stage2_d, stage2_m] using
    (Stage2Output.forall_exists_discOffset_gt (f := f)
      (out := stage2Out (f := f) (hf := hf)))

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
    (Stage2Output.forall_exists_discOffset_gt' (f := f)
      (out := stage2Out (f := f) (hf := hf)))

/-- Positive-length witness form of `stage2_forall_exists_discOffset_gt'`.

The witness length `n` cannot be `0`, since `discOffset ... 0 = 0`.
-/
theorem stage2_forall_exists_discOffset_gt'_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ,
        n > 0 ∧ discOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) n > B := by
  simpa [stage2_d, stage2_m] using
    (Stage2Output.forall_exists_discOffset_gt'_witness_pos (f := f)
      (out := stage2Out (f := f) (hf := hf)))

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
  simpa [stage2_d, stage2_m] using
    (Stage2Output.forall_exists_natAbs_apSumOffset_gt' (f := f)
      (out := stage2Out (f := f) (hf := hf)))

/-- Positive-length witness form of `stage2_forall_exists_natAbs_apSumOffset_gt'`.

The witness length `n` cannot be `0`, since `apSumOffset ... 0 = 0`.
-/
theorem stage2_forall_exists_natAbs_apSumOffset_gt'_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ, n > 0 ∧
        Int.natAbs
            (apSumOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) n) > B := by
  simpa [stage2_d, stage2_m] using
    (Stage2Output.forall_exists_natAbs_apSumOffset_gt_witness_pos (f := f)
      (out := stage2Out (f := f) (hf := hf)))

/-- Paper-notation witness form: Stage 2 yields arbitrarily large shifted progression sums
`∑ i ∈ Icc (m+1) (m+n), f (i*d)` at the concrete parameters produced by the conjecture stub
`stage2Out`.

Normal form:
`∀ B, ∃ n, Int.natAbs (∑ i ∈ Icc (m+1) (m+n), f (i*d)) > B`,
where `d = stage2_d` and `m = stage2_m`.

This is just `stage2_forall_exists_natAbs_apSumOffset_gt'` rewritten using the paper-notation lemma
`Tao2015.natAbs_apSumOffset_eq_natAbs_sum_Icc`.
-/
theorem stage2_forall_exists_natAbs_sum_Icc_offset_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ,
        Int.natAbs
            ((Finset.Icc (stage2_m (f := f) (hf := hf) + 1) (stage2_m (f := f) (hf := hf) + n)).sum
              (fun i => f (i * stage2_d (f := f) (hf := hf)))) > B := by
  simpa [stage2_d, stage2_m] using
    (Stage2Output.forall_exists_natAbs_sum_Icc_offset_gt (f := f)
      (out := stage2Out (f := f) (hf := hf)))

/-- Positive-length witness form of `stage2_forall_exists_natAbs_sum_Icc_offset_gt`.

The witness length `n` cannot be `0`, since the interval `Icc (m+1) (m+n)` is empty when `n = 0`.
-/
theorem stage2_forall_exists_natAbs_sum_Icc_offset_gt_witness_pos (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ, n > 0 ∧
        Int.natAbs
            ((Finset.Icc (stage2_m (f := f) (hf := hf) + 1) (stage2_m (f := f) (hf := hf) + n)).sum
              (fun i => f (i * stage2_d (f := f) (hf := hf)))) > B := by
  simpa [stage2_d, stage2_m] using
    (Stage2Output.forall_exists_natAbs_sum_Icc_offset_gt_witness_pos (f := f)
      (out := stage2Out (f := f) (hf := hf)))

/-!
Consumer code should usually use `stage2Out` together with the general lemmas about `Stage2Output`
(from `TrackCStage2.lean` / `TrackCStage2Output.lean`).

We intentionally keep the proofs here as thin wrappers around the general lemmas about
`Stage2Output`, specializing them to the deterministic parameters coming from `stage2Out`.
-/

end Tao2015

end MoltResearch
