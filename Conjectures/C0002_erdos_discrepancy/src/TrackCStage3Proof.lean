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

-- Projections `stage3_d`, `stage3_g`, `stage3_m` live in `TrackCStage3Entry.lean`.


/-
Note: the basic Stage-3 projections/wrappers

  stage3_hg
  stage3_g_eq
  stage3_g_eq_fun

are defined in `TrackCStage3Entry.lean`.

This file imports `TrackCStage3Entry`, so they are available without redeclaration.
-/

/-- Positivity of the reduced step size produced by Stage 3. -/
theorem stage3_hd (f : ℕ → ℤ) (hf : IsSignSequence f) : stage3_d (f := f) (hf := hf) > 0 := by
  -- Prefer the Stage-3 boundary API lemma.
  simpa [stage3_d] using
    (Stage3Output.hd (f := f) (stage3Out (f := f) (hf := hf)))

/-!
The convenience lemma `stage3_one_le_d` lives in `TrackCStage3Entry.lean`.
We intentionally do not redeclare it here (this file imports `TrackCStage3Entry`).
-/

/-
Note: the convenience lemma `stage3_d_ne_zero` lives in `TrackCStage3Entry.lean`.
-/

-- Note: `stage3_unboundedDiscrepancyAlong_core` is already provided by
-- `Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryCore` (imported via
-- `Conjectures.C0002_erdos_discrepancy.src.TrackCStage3Entry`).


/-
Note: `stage3_unboundedDiscOffset` is provided by `TrackCStage3EntryCore.lean` (re-exported by
`TrackCStage3Entry.lean`) so hard-gate consumers can use it without importing this larger
convenience-lemma file.

Since this module imports `TrackCStage3Entry`, that lemma is available automatically here.
-/

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

/-- Positive-length witness form of `stage3_forall_exists_natAbs_apSumOffset_gt'`.

The witness length `n` cannot be `0`, since `apSumOffset ... 0 = 0`.
-/
theorem stage3_forall_exists_natAbs_apSumOffset_gt'_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ, n > 0 ∧
        Int.natAbs
            (apSumOffset f (stage3_d (f := f) (hf := hf)) (stage3_m (f := f) (hf := hf)) n) > B := by
  have hunb :
      UnboundedDiscOffset f (stage3_d (f := f) (hf := hf)) (stage3_m (f := f) (hf := hf)) :=
    stage3_unboundedDiscOffset (f := f) (hf := hf)
  simpa using
    (UnboundedDiscOffset.forall_exists_natAbs_apSumOffset_gt_witness_pos (hunb := hunb))

/-- Consumer-facing shortcut: Stage 3 yields the paper-notation offset witness form:

`∀ B, ∃ n, Int.natAbs (∑ i ∈ Icc (m+1) (m+n), f (i*d)) > B`,
where `d = stage3_d` and `m = stage3_m`.

This is a thin wrapper around `Stage3Output.forall_exists_natAbs_sum_Icc_offset_gt`.
-/
theorem stage3_forall_exists_natAbs_sum_Icc_offset_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ, ∃ n : ℕ,
      Int.natAbs
          ((Finset.Icc ((stage3_m (f := f) (hf := hf)) + 1)
              ((stage3_m (f := f) (hf := hf)) + n)).sum
            (fun i => f (i * (stage3_d (f := f) (hf := hf))))) > B := by
  simpa [stage3_d, stage3_m] using
    (Stage3Output.forall_exists_natAbs_sum_Icc_offset_gt (f := f) (stage3Out (f := f) (hf := hf)))

/-- Positive-length witness form of `stage3_forall_exists_natAbs_sum_Icc_offset_gt`.

The witness length `n` cannot be `0`, since the interval `Icc (m+1) (m+n)` is empty when `n = 0`.
-/
theorem stage3_forall_exists_natAbs_sum_Icc_offset_gt_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ, ∃ n : ℕ, n > 0 ∧
      Int.natAbs
          ((Finset.Icc ((stage3_m (f := f) (hf := hf)) + 1)
              ((stage3_m (f := f) (hf := hf)) + n)).sum
            (fun i => f (i * (stage3_d (f := f) (hf := hf))))) > B := by
  simpa [stage3_d, stage3_m] using
    (Stage3Output.forall_exists_natAbs_sum_Icc_offset_gt_witness_pos (f := f)
      (stage3Out (f := f) (hf := hf)))

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

/-- Positive-length witness form of `stage3_forall_exists_natAbs_apSumFrom_mul_gt`.

The witness length `n` cannot be `0`, since `apSumFrom ... 0 = 0`.

This is a thin wrapper around
`Stage3Output.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos`.
-/
theorem stage3_forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ,
      ∃ n : ℕ, n > 0 ∧
        Int.natAbs
            (apSumFrom f ((stage3_m (f := f) (hf := hf)) * (stage3_d (f := f) (hf := hf)))
              (stage3_d (f := f) (hf := hf)) n) > C := by
  simpa [stage3_d, stage3_m] using
    (Stage3Output.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f := f)
      (stage3Out (f := f) (hf := hf)))

/-!
Note: the lemma

  Tao2015.stage3_forall_hasDiscrepancyAtLeast (f) (hf) : ∀ C, HasDiscrepancyAtLeast f C

is defined in `TrackCStage3EntryCore.lean` so hard-gate consumers can use it without importing
this larger convenience-lemma file.
-/

/-
Note: the global witness-form wrappers

  stage3_forall_exists_d_ge_one_witness_pos
  stage3_forall_exists_d_pos_witness_pos
  stage3_forall_exists_d_ne_zero_witness_pos

are available from `TrackCStage3Entry.lean` (which re-exports the hard-gate core) so consumers can
use them without importing this larger convenience-lemma file.

Since this module imports `TrackCStage3Entry`, those lemmas are available automatically here.
-/

/-
Note: the lemmas

  stage3_exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt
  stage3_exists_params_one_le_forall_exists_natAbs_apSumFrom_mul_gt_witness_pos

live in `TrackCStage3EntryCore.lean` so pipeline consumers can access them without importing this
larger convenience-lemma file.
-/

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

/-- Consumer-facing shortcut: Stage 3 yields concrete parameters `d, m` with `1 ≤ d` such that the
paper-notation offset sum witness `∑ i ∈ Icc (m+1) (m+n), f (i*d)` takes arbitrarily large absolute
values.

This is a thin wrapper around the Stage-3 boundary API lemma
`Stage3Output.exists_params_one_le_forall_exists_natAbs_sum_Icc_offset_gt`.
-/
theorem stage3_exists_params_one_le_forall_exists_natAbs_sum_Icc_offset_gt (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ B : ℕ, ∃ n : ℕ,
        Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) > B) := by
  simpa using
    (Stage3Output.exists_params_one_le_forall_exists_natAbs_sum_Icc_offset_gt (f := f)
      (stage3Out (f := f) (hf := hf)))

/-- Positive-length witness variant of `stage3_exists_params_one_le_forall_exists_natAbs_sum_Icc_offset_gt`.

The witness length `n` cannot be `0`, since the interval `Icc (m+1) (m+n)` is empty when `n = 0`.

This is a thin wrapper around the Stage-3 boundary API lemma
`Stage3Output.exists_params_one_le_forall_exists_natAbs_sum_Icc_offset_gt_witness_pos`.
-/
theorem stage3_exists_params_one_le_forall_exists_natAbs_sum_Icc_offset_gt_witness_pos (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧
      (∀ B : ℕ, ∃ n : ℕ, n > 0 ∧
        Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) > B) := by
  simpa using
    (Stage3Output.exists_params_one_le_forall_exists_natAbs_sum_Icc_offset_gt_witness_pos (f := f)
      (stage3Out (f := f) (hf := hf)))

-- Note: `stage3_exists_params_one_le_forall_exists_natAbs_apSumOffset_gt_witness_pos` is already
-- provided by `Conjectures.C0002_erdos_discrepancy.src.TrackCStage3EntryCore` (imported via
-- `Conjectures.C0002_erdos_discrepancy.src.TrackCStage3Entry`).


end Tao2015

end MoltResearch
