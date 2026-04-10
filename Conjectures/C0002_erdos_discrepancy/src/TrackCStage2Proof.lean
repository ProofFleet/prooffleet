import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry

/-!
# Track C: Stage 2 proof stub (Tao 2015 plane)

This file contains only Stage-2 convenience projections/wrapper lemmas specialized to the
**deterministic** output `stage2Out`.

The Stage-2 conjecture stub (axiom) itself lives in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry`.

Implementation note:
- this module intentionally does **not** import the large Stage-2 convenience-lemma library
  `TrackCStage2Output.lean`.
- instead, we prove the wrappers here directly from:
  - the Stage-2 fields (`out1`, `unbounded`),
  - Stage-1 transport contracts on `ReductionOutput`, and
  - small, generic normal-form lemmas about `UnboundedDiscOffset` from `Tao2015.lean`.

Design goal: keep this file lightweight, while still offering a convenient API surface for
consumers that want to use the named Stage-2 stub `stage2Out`.
-/

namespace MoltResearch

namespace Tao2015

/-!
The Stage-2 conjecture stub (axiom) and the deterministic name `stage2Out` live in
`Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Entry`.

This file keeps only the convenience projections/wrapper lemmas.
-/

/-- Minimal consumer-facing Stage-2 consequence: the original sequence cannot have globally bounded
(discrepancy) once Stage 2 produces an unbounded fixed-step witness along the reduced sequence. -/
theorem stage2_notBounded (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f := by
  exact
    (stage2Out (f := f) (hf := hf)).out1.not_boundedDiscrepancy_of_unboundedDiscrepancyAlong (f := f)
      (stage2Out (f := f) (hf := hf)).unbounded

/-- Consumer-facing shortcut: Stage 2 yields the usual surface statement
`∀ C, HasDiscrepancyAtLeast f C`.

This is a thin wrapper around `stage2_notBounded` via the global normal form lemma
`forall_hasDiscrepancyAtLeast_iff_not_boundedDiscrepancy`.
-/
theorem stage2_forall_hasDiscrepancyAtLeast (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  exact (forall_hasDiscrepancyAtLeast_iff_not_boundedDiscrepancy f).2 (stage2_notBounded (f := f) (hf := hf))

/-- Consumer-facing shortcut: Stage 2 yields unbounded discrepancy along the deterministic reduced
sequence `stage2_g` at the deterministic step size `stage2_d`.

This is just the `unbounded` field of `stage2Out`, rewritten to use the named projections.
-/
theorem stage2_unboundedDiscrepancyAlong (f : ℕ → ℤ) (hf : IsSignSequence f) :
    UnboundedDiscrepancyAlong (stage2_g (f := f) (hf := hf)) (stage2_d (f := f) (hf := hf)) := by
  simpa [stage2_g, stage2_d] using (stage2Out (f := f) (hf := hf)).unbounded

/-- Minimal consumer-facing Stage-2 consequence: Stage 2 yields an unbounded bundled offset
discrepancy family `discOffset f d m` at the deterministic parameters produced by `stage2Out`. -/
theorem stage2_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    UnboundedDiscOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) := by
  simpa [stage2_d, stage2_m] using
    ((stage2Out (f := f) (hf := hf)).out1.unboundedDiscrepancyAlong_iff_unboundedDiscOffset (f := f)).1
      (stage2Out (f := f) (hf := hf)).unbounded

/-- Core-predicate form: Stage 2 yields unbounded fixed-step discrepancy along the reduced sequence,
re-expressed using `MoltResearch.UnboundedDiscrepancyAlong`.

This is a small convenience wrapper around the Track-C-local witness
`(stage2Out ...).unbounded`, using `Tao2015.unboundedDiscrepancyAlong_iff_core`.
-/
theorem stage2_unboundedDiscrepancyAlong_core (f : ℕ → ℤ) (hf : IsSignSequence f) :
    MoltResearch.UnboundedDiscrepancyAlong (stage2_g (f := f) (hf := hf))
      (stage2_d (f := f) (hf := hf)) := by
  exact
    (Tao2015.unboundedDiscrepancyAlong_iff_core (g := stage2_g (f := f) (hf := hf))
        (d := stage2_d (f := f) (hf := hf))).1
      (stage2Out (f := f) (hf := hf)).unbounded

/-- Existential packaging: Stage 2 yields concrete parameters `d, m` with `1 ≤ d` such that the
bundled offset discrepancy family `discOffset f d m` is unbounded. -/
theorem stage2_exists_params_one_le_unboundedDiscOffset (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∃ d m : ℕ, 1 ≤ d ∧ UnboundedDiscOffset f d m := by
  refine ⟨stage2_d (f := f) (hf := hf), stage2_m (f := f) (hf := hf),
    stage2_one_le_d (f := f) (hf := hf), ?_⟩
  exact stage2_unboundedDiscOffset (f := f) (hf := hf)

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

This is a thin wrapper around `stage2_forall_hasDiscrepancyAtLeast` via
`forall_hasDiscrepancyAtLeast_iff_forall_exists_d_ge_one_witness_pos`.
-/
theorem stage2_forall_exists_d_ge_one_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  exact
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_d_ge_one_witness_pos f).1
      (stage2_forall_hasDiscrepancyAtLeast (f := f) (hf := hf))

/-- Variant of `stage2_forall_exists_d_ge_one_witness_pos` with the step-size condition written as
`d > 0`. -/
theorem stage2_forall_exists_d_pos_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  intro C
  rcases stage2_forall_exists_d_ge_one_witness_pos (f := f) (hf := hf) C with ⟨d, n, hd, hn, hw⟩
  refine ⟨d, n, ?_, hn, hw⟩
  exact lt_of_lt_of_le Nat.zero_lt_one hd

/-- Variant of `stage2_forall_exists_d_pos_witness_pos` with the step-size condition written as
`d ≠ 0`. -/
theorem stage2_forall_exists_d_ne_zero_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ, ∃ d n : ℕ, d ≠ 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  intro C
  rcases stage2_forall_exists_d_pos_witness_pos (f := f) (hf := hf) C with ⟨d, n, hd, hn, hw⟩
  exact ⟨d, n, Nat.ne_of_gt hd, hn, hw⟩

/-- Consumer-facing tail-nucleus witness form: Stage 2 yields arbitrarily large affine-tail nuclei
`apSumFrom f (m*d) d n` at the concrete parameters produced by the conjecture stub `stage2Out`.

We derive this directly from the Stage-1 transport equivalence
`ReductionOutput.unboundedDiscrepancyAlong_iff_forall_exists_natAbs_apSumFrom_mul_gt`.
-/
theorem stage2_forall_exists_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ C : ℕ,
      ∃ n : ℕ,
        Int.natAbs
            (apSumFrom f (stage2_start (f := f) (hf := hf)) (stage2_d (f := f) (hf := hf)) n) > C := by
  simpa [stage2_start, stage2_m, stage2_d] using
    ((stage2Out (f := f) (hf := hf)).out1.unboundedDiscrepancyAlong_iff_forall_exists_natAbs_apSumFrom_mul_gt
        (f := f)).1
      (stage2Out (f := f) (hf := hf)).unbounded

/-- Negation-normal-form tail-nucleus statement: Stage 2 yields no uniform bound on the affine-tail
nuclei `Int.natAbs (apSumFrom f (m*d) d n)` at the concrete parameters produced by `stage2Out`.

This is often the most convenient form for contradiction arguments in later stages.
-/
theorem stage2_not_exists_forall_natAbs_apSumFrom_mul_le (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ,
        ∀ n : ℕ,
          Int.natAbs
              (apSumFrom f (stage2_start (f := f) (hf := hf)) (stage2_d (f := f) (hf := hf)) n) ≤ B := by
  have hunb : UnboundedDiscOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) :=
    stage2_unboundedDiscOffset (f := f) (hf := hf)
  simpa [stage2_start, stage2_d, stage2_m] using
    (UnboundedDiscOffset.iff_not_exists_forall_natAbs_apSumFrom_mul_le (f := f)
        (d := stage2_d (f := f) (hf := hf))
        (m := stage2_m (f := f) (hf := hf))).1
      hunb

/-- Positive-length witness form of `stage2_forall_exists_natAbs_apSumFrom_mul_gt`.

The witness length `n` cannot be `0`, since `apSumFrom ... 0 = 0`.

This is a thin wrapper around the Conjectures-only normal-form lemma
`forall_exists_natAbs_apSumFrom_mul_gt_witness_pos`.
-/
theorem stage2_forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f : ℕ → ℤ)
    (hf : IsSignSequence f) :
    ∀ C : ℕ,
      ∃ n : ℕ, n > 0 ∧
        Int.natAbs
            (apSumFrom f (stage2_start (f := f) (hf := hf)) (stage2_d (f := f) (hf := hf)) n) > C := by
  have hunb : UnboundedDiscOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) :=
    stage2_unboundedDiscOffset (f := f) (hf := hf)
  simpa [stage2_start, stage2_d, stage2_m] using
    (UnboundedDiscOffset.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f := f)
      (d := stage2_d (f := f) (hf := hf))
      (m := stage2_m (f := f) (hf := hf))
      hunb)

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
  simpa [stage2_start, stage2_m, stage2_d] using
    stage2_forall_exists_natAbs_apSumFrom_mul_gt (f := f) (hf := hf) C

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
  intro C
  simpa [stage2_start, stage2_m, stage2_d] using
    stage2_forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f := f) (hf := hf) C

/-- Consumer-facing shortcut: Stage 2 yields raw offset-nucleus witnesses at the concrete
parameters produced by the conjecture stub `stage2Out`.

Normal form:
`∀ B, ∃ n, B < discOffset f d m n`,
where `d = stage2_d` and `m = stage2_m`.

This is definitionally just `stage2_unboundedDiscOffset`.
-/
theorem stage2_forall_exists_discOffset_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ,
        B < discOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) n := by
  exact stage2_unboundedDiscOffset (f := f) (hf := hf)

/-- Consumer-facing shortcut: Stage 2 yields raw offset-nucleus witnesses at the concrete
parameters produced by the conjecture stub `stage2Out`.

Normal form:
`∀ B, ∃ n, discOffset f d m n > B`,
where `d = stage2_d` and `m = stage2_m`.
-/
theorem stage2_forall_exists_discOffset_gt' (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ,
        discOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) n > B := by
  intro B
  rcases stage2_forall_exists_discOffset_gt (f := f) (hf := hf) B with ⟨n, hn⟩
  exact ⟨n, (gt_iff_lt).2 hn⟩

/-- Negation-normal form: Stage 2 yields no uniform bound on the offset-nucleus `discOffset` at the
concrete parameters produced by the conjecture stub `stage2Out`.
-/
theorem stage2_not_exists_forall_discOffset_le (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ¬ ∃ B : ℕ,
        ∀ n : ℕ,
          discOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) n ≤ B := by
  rintro ⟨B, hB⟩
  have hunb :
      UnboundedDiscOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) :=
    stage2_unboundedDiscOffset (f := f) (hf := hf)
  rcases hunb B with ⟨n, hn⟩
  exact (not_lt_of_ge (hB n)) hn

/-- Positive-length witness form of `stage2_forall_exists_discOffset_gt'`.

The witness length `n` cannot be `0`, since `discOffset ... 0 = 0`.
-/
theorem stage2_forall_exists_discOffset_gt'_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ,
        n > 0 ∧ discOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) n > B := by
  have hunb : UnboundedDiscOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) :=
    stage2_unboundedDiscOffset (f := f) (hf := hf)
  exact
    UnboundedDiscOffset.forall_exists_discOffset_gt'_witness_pos (f := f)
      (d := stage2_d (f := f) (hf := hf))
      (m := stage2_m (f := f) (hf := hf))
      hunb

/-- Consumer-facing shortcut: Stage 2 yields raw offset-nucleus witnesses at the concrete
parameters produced by the conjecture stub `stage2Out`, stated using the bundled offset nucleus.

Normal form:
`∀ B, ∃ n, Int.natAbs (apSumOffset f d m n) > B`,
where `d = stage2_d` and `m = stage2_m`.

This is a thin wrapper around the normal-form lemma
`iff_forall_exists_natAbs_apSumOffset_gt'`.
-/
theorem stage2_forall_exists_natAbs_apSumOffset_gt' (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ,
        Int.natAbs
            (apSumOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) n) > B := by
  have hunb : UnboundedDiscOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) :=
    stage2_unboundedDiscOffset (f := f) (hf := hf)
  simpa [stage2_d, stage2_m] using
    (UnboundedDiscOffset.iff_forall_exists_natAbs_apSumOffset_gt' (f := f)
      (d := stage2_d (f := f) (hf := hf))
      (m := stage2_m (f := f) (hf := hf))).1
      hunb

/-- Positive-length witness form of `stage2_forall_exists_natAbs_apSumOffset_gt'`.

The witness length `n` cannot be `0`, since `apSumOffset ... 0 = 0`.
-/
theorem stage2_forall_exists_natAbs_apSumOffset_gt'_witness_pos (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ, n > 0 ∧
        Int.natAbs
            (apSumOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) n) > B := by
  have hunb : UnboundedDiscOffset f (stage2_d (f := f) (hf := hf)) (stage2_m (f := f) (hf := hf)) :=
    stage2_unboundedDiscOffset (f := f) (hf := hf)
  simpa [stage2_d, stage2_m] using
    (UnboundedDiscOffset.forall_exists_natAbs_apSumOffset_gt_witness_pos (f := f)
      (d := stage2_d (f := f) (hf := hf))
      (m := stage2_m (f := f) (hf := hf))
      hunb)

/-- Paper-notation witness form: Stage 2 yields arbitrarily large shifted progression sums
`∑ i ∈ Icc (m+1) (m+n), f (i*d)` at the concrete parameters produced by the conjecture stub
`stage2Out`.

Normal form:
`∀ B, ∃ n, Int.natAbs (∑ i ∈ Icc (m+1) (m+n), f (i*d)) > B`,
where `d = stage2_d` and `m = stage2_m`.

This is `stage2_forall_exists_natAbs_apSumOffset_gt'` rewritten using
`natAbs_apSumOffset_eq_natAbs_sum_Icc`.
-/
theorem stage2_forall_exists_natAbs_sum_Icc_offset_gt (f : ℕ → ℤ) (hf : IsSignSequence f) :
    ∀ B : ℕ,
      ∃ n : ℕ,
        Int.natAbs
            ((Finset.Icc (stage2_m (f := f) (hf := hf) + 1) (stage2_m (f := f) (hf := hf) + n)).sum
              (fun i => f (i * stage2_d (f := f) (hf := hf)))) > B := by
  intro B
  rcases stage2_forall_exists_natAbs_apSumOffset_gt' (f := f) (hf := hf) B with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  -- Rewrite `apSumOffset` into paper notation.
  simpa [natAbs_apSumOffset_eq_natAbs_sum_Icc (f := f)
      (d := stage2_d (f := f) (hf := hf))
      (m := stage2_m (f := f) (hf := hf))
      (n := n)] using
    hn

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
  intro B
  rcases stage2_forall_exists_natAbs_apSumOffset_gt'_witness_pos (f := f) (hf := hf) B with
    ⟨n, hnpos, hn⟩
  refine ⟨n, hnpos, ?_⟩
  -- Rewrite `apSumOffset` into paper notation.
  simpa [natAbs_apSumOffset_eq_natAbs_sum_Icc (f := f)
      (d := stage2_d (f := f) (hf := hf))
      (m := stage2_m (f := f) (hf := hf))
      (n := n)] using
    hn

/-!
Consumer code should usually use `stage2Out` together with the general lemmas about `Stage2Output`
(from `TrackCStage2.lean` / `TrackCStage2Output.lean`).

We intentionally keep the proofs here as thin wrappers around Stage-1 transport contracts and
generic normal-form lemmas, specialized to the deterministic parameters coming from `stage2Out`.
-/

end Tao2015

end MoltResearch
