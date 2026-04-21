import Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Core

/-!
# Track C: Stage 2 core extras (Tao 2015 plane)

This file contains additional proved convenience lemmas about `Tao2015.Stage2Output` that are not
needed by the Track-C hard-gate target `Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy`.

Design goal: keep `TrackCStage2Core.lean` as small as possible for the hard-gate build, while still
making these arithmetic and rewrite helpers available to later stages and convenience layers.
-/

namespace MoltResearch

namespace Tao2015

namespace Stage2Output

variable {f : ℕ → ℤ}

/-!
## Start index (`m*d`) helpers
-/

-- Note: `Stage2Output.start` is defined in `Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Core`.

-- Note: the definitional rewrite lemma `Stage2Output.start_eq_m_mul_d` lives in
-- `Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Core` (hard-gate surface).

/-- Normal form: the affine-tail nucleus starting at the bundled start index `out.start`
is the bundled offset nucleus at the bundled offset parameter `out.m`.

This is `Tao2015.apSumFrom_mul_eq_apSumOffset` rewritten using `out.start = out.m * out.d`.
-/
theorem apSumFrom_start_eq_apSumOffset (out : Stage2Output f) (n : ℕ) :
    apSumFrom f out.start out.d n = apSumOffset f out.d out.m n := by
  simpa [Stage2Output.start] using
    (apSumFrom_mul_eq_apSumOffset (f := f) (d := out.d) (m := out.m) (n := n))

/-- Normal form: the bundled offset discrepancy wrapper `discOffset f out.d out.m n` is the
absolute value of the affine-tail nucleus `apSumFrom f out.start out.d n`.

This lets later stages work directly with affine-tail nuclei (a common analytic normal form)
without repeatedly rewriting `apSumOffset` or unfolding `discOffset`.
-/
theorem discOffset_eq_natAbs_apSumFrom_start (out : Stage2Output f) (n : ℕ) :
    discOffset f out.d out.m n = Int.natAbs (apSumFrom f out.start out.d n) := by
  -- Prefer routing through the core normal form lemma `discOffset_eq_natAbs_apSumFrom_mul` so this
  -- interface lemma does not depend on unfolding `discOffset`.
  simpa [Stage2Output.start] using
    (discOffset_eq_natAbs_apSumFrom_mul (f := f) (d := out.d) (m := out.m) (n := n))

/-- Normal form: discrepancy of the reduced sequence is the absolute value of the affine-tail nucleus
`apSumFrom f out.start out.d n`.

This combines the Stage-1 contract rewrite
`ReductionOutput.discrepancy_eq_discOffset_via_contract` with
`discOffset_eq_natAbs_apSumFrom_start`.
-/
theorem discrepancy_eq_natAbs_apSumFrom_start (out : Stage2Output f) (n : ℕ) :
    discrepancy out.g out.d n = Int.natAbs (apSumFrom f out.start out.d n) := by
  calc
    discrepancy out.g out.d n = discOffset f out.d out.m n := by
      simpa [Stage2Output.g, Stage2Output.d, Stage2Output.m] using
        (out.out1.discrepancy_eq_discOffset_via_contract (f := f) (n := n))
    _ = Int.natAbs (apSumFrom f out.start out.d n) := by
      simpa using out.discOffset_eq_natAbs_apSumFrom_start (f := f) (n := n)

/-- Normal form: boundedness of the bundled offset discrepancy family `discOffset f out.d out.m`
expressed directly using affine-tail nuclei `apSumFrom f out.start out.d`.

This is just `BoundedDiscOffset` rewritten using `discOffset_eq_natAbs_apSumFrom_start`.
-/
theorem boundedDiscOffset_iff_forall_natAbs_apSumFrom_start_le (out : Stage2Output f) (B : ℕ) :
    BoundedDiscOffset f out.d out.m B ↔
      ∀ n : ℕ, Int.natAbs (apSumFrom f out.start out.d n) ≤ B := by
  constructor
  · intro h n
    have hn : discOffset f out.d out.m n ≤ B := h n
    simpa [out.discOffset_eq_natAbs_apSumFrom_start (f := f) (n := n)] using hn
  · intro h n
    have hn : Int.natAbs (apSumFrom f out.start out.d n) ≤ B := h n
    simpa [out.discOffset_eq_natAbs_apSumFrom_start (f := f) (n := n)] using hn

-- Note: additional witness/negation-normal-form wrappers for `discOffset` and `apSumOffset`
-- live near the end of this file.

-- Note: `Stage2Output.d_dvd_start` and `Stage2Output.start_mod_d` live in
-- `Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Core` (hard-gate surface).

/-- Adding the start index does not change residues modulo the step size.

Since `out.start` is a multiple of `out.d`, we have
`(n + out.start) % out.d = n % out.d`.
-/
theorem add_start_mod_d (out : Stage2Output f) (n : ℕ) :
    (n + out.start) % out.d = n % out.d := by
  have hstart : out.start % out.d = 0 := out.start_mod_d (f := f)
  simp [Nat.add_mod, hstart]

/-- Variant of `add_start_mod_d` with the start index on the left. -/
theorem start_add_mod_d (out : Stage2Output f) (n : ℕ) :
    (out.start + n) % out.d = n % out.d := by
  simpa [Nat.add_comm] using out.add_start_mod_d (f := f) (n := n)

/-- Adding the start index increases quotients by the offset parameter.

Since `out.start = out.m * out.d`, we have
`(n + out.start) / out.d = n / out.d + out.m`.
-/
theorem add_start_div_d (out : Stage2Output f) (n : ℕ) :
    (n + out.start) / out.d = n / out.d + out.m := by
  have hd : 0 < out.d := out.hd
  simpa [Stage2Output.start] using
    (Nat.add_mul_div_right (x := n) (y := out.m) (z := out.d) hd)

/-- Variant of `add_start_div_d` with the start index on the left. -/
theorem start_add_div_d (out : Stage2Output f) (n : ℕ) :
    (out.start + n) / out.d = n / out.d + out.m := by
  simpa [Nat.add_comm] using out.add_start_div_d (f := f) (n := n)

-- Note: `Stage2Output.start_div_d` lives in
-- `Conjectures.C0002_erdos_discrepancy.src.TrackCStage2Core` (hard-gate surface).

/-!
## Reduced-sequence rewrite helpers
-/

/-- Rewrite for the reduced sequence produced by Stage 2: it is a shift by `m*d`. -/
theorem g_eq (out : Stage2Output f) (k : ℕ) :
    out.g k = f (k + out.m * out.d) := by
  simpa [Stage2Output.g, Stage2Output.m, Stage2Output.d] using out.out1.g_eq k

/-- Rewrite for the reduced sequence produced by Stage 2, phrased using the bundled start index
`out.start = out.m * out.d`. -/
theorem g_eq_start (out : Stage2Output f) (k : ℕ) :
    out.g k = f (k + out.start) := by
  simpa [Stage2Output.start] using (out.g_eq (f := f) k)

/-- Function-level rewrite for the reduced sequence produced by Stage 2: it is the shifted sequence
`fun k => f (k + out.start)`.
-/
theorem g_eq_fun (out : Stage2Output f) :
    out.g = fun k => f (k + out.start) := by
  funext k
  simpa using out.g_eq_start (f := f) k

/-- The reduced-sequence homogeneous nucleus is the original-sequence affine nucleus at the bundled
start index `out.start`.

Concretely, `apSum out.g out.d n` sums `out.g` along `out.d, 2*out.d, …, n*out.d`, and since
`out.g k = f (k + out.start)`, this is exactly `apSumFrom f out.start out.d n`.
-/
theorem apSum_g_eq_apSumFrom_start (out : Stage2Output f) (n : ℕ) :
    apSum out.g out.d n = apSumFrom f out.start out.d n := by
  unfold apSum apSumFrom
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- `out.g` is `f` shifted by `out.start`.
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (out.g_eq_start (f := f) ((i + 1) * out.d))

/-!
## Tail-nucleus unboundedness normal forms (start-index phrasing)
-/

/-- Negation-normal-form unboundedness statement for the affine-tail nuclei
`Int.natAbs (apSumFrom f out.start out.d n)`.

This is `unboundedDiscOffset` rewritten using the generic normal-form lemma
`Tao2015.UnboundedDiscOffset.iff_not_exists_forall_natAbs_apSumFrom_mul_le`.

We phrase this using the bundled start index `out.start = out.m * out.d` to reduce arithmetic noise
in downstream stages.
-/
theorem not_exists_forall_natAbs_apSumFrom_mul_le (out : Stage2Output f) :
    ¬ ∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumFrom f out.start out.d n) ≤ B := by
  have hunb : UnboundedDiscOffset f out.d out.m := out.unboundedDiscOffset (f := f)
  simpa [Stage2Output.start] using
    (Tao2015.UnboundedDiscOffset.iff_not_exists_forall_natAbs_apSumFrom_mul_le
        (f := f) (d := out.d) (m := out.m)).1
      hunb

/-- Tail-nucleus witness form: Stage 2 yields arbitrarily large affine-tail nuclei
`Int.natAbs (apSumFrom f out.start out.d n)`.

This is a small convenience wrapper around the generic normal-form lemma
`Tao2015.UnboundedDiscOffset.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos`, specialized to
the deterministic Stage-2 parameters.

We phrase this using the bundled start index `out.start = out.m * out.d` to reduce arithmetic noise
in downstream stages.
-/
theorem forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ Int.natAbs (apSumFrom f out.start out.d n) > B := by
  have hunb : UnboundedDiscOffset f out.d out.m := out.unboundedDiscOffset (f := f)
  simpa [Stage2Output.start] using
    (Tao2015.UnboundedDiscOffset.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos
      (f := f) (d := out.d) (m := out.m) hunb)

/-- Positive-length tail-nucleus witness form phrased using the bundled start index `out.start`.

This is just `forall_exists_natAbs_apSumFrom_mul_gt_witness_pos` under the more discoverable name
that matches the Stage-3 interface.
-/
theorem forall_exists_natAbs_apSumFrom_start_gt_witness_pos (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ Int.natAbs (apSumFrom f out.start out.d n) > B := by
  simpa using out.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f := f)

/-- Tail-nucleus witness form without the positive-length side condition.

This is a small convenience corollary of
`Stage2Output.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos`.
-/
theorem forall_exists_natAbs_apSumFrom_start_gt (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f out.start out.d n) > B := by
  intro B
  rcases out.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f := f) B with ⟨n, _hnpos, hgt⟩
  exact ⟨n, hgt⟩

/-!
## Offset-discrepancy witness forms (non-hard-gate)

These are convenient witness/negation-normal-form wrappers derived from the proved core lemma
`Stage2Output.unboundedDiscOffset`.

They are intentionally kept out of `TrackCStage2Core.lean` so the Track-C hard-gate build does not
compile them.
-/

/-- Positive-length witness form: Stage 2 yields arbitrarily large bundled offset discrepancies
`discOffset f out.d out.m n`, with witnesses `n > 0`.

This is a thin wrapper around
`Tao2015.UnboundedDiscOffset.forall_exists_discOffset_gt'_witness_pos`.
-/
theorem forall_exists_discOffset_gt'_witness_pos (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ discOffset f out.d out.m n > B := by
  have hunb : UnboundedDiscOffset f out.d out.m := out.unboundedDiscOffset (f := f)
  simpa using
    (Tao2015.UnboundedDiscOffset.forall_exists_discOffset_gt'_witness_pos
      (f := f) (d := out.d) (m := out.m) hunb)

/-- Witness form: Stage 2 yields arbitrarily large bundled offset discrepancies `discOffset ... > B`.

This is just `forall_exists_discOffset_gt'_witness_pos` with the positivity side condition dropped.
-/
theorem forall_exists_discOffset_gt' (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, discOffset f out.d out.m n > B := by
  intro B
  rcases out.forall_exists_discOffset_gt'_witness_pos (f := f) B with ⟨n, _hnpos, hn⟩
  exact ⟨n, hn⟩

/-- Positive-length witness form: Stage 2 yields arbitrarily large bundled offset discrepancies
`discOffset f out.d out.m n`, with witnesses `n > 0`.

This is `forall_exists_discOffset_gt'_witness_pos` rewritten using `gt_iff_lt`.
-/
theorem forall_exists_discOffset_gt_witness_pos (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ B < discOffset f out.d out.m n := by
  intro B
  rcases out.forall_exists_discOffset_gt'_witness_pos (f := f) B with ⟨n, hnpos, hn⟩
  exact ⟨n, hnpos, (gt_iff_lt).1 hn⟩

/-- Witness-family form: Stage 2 yields arbitrarily large bundled offset discrepancies, written as
`B < discOffset ...`.

This is `forall_exists_discOffset_gt_witness_pos` with the positivity side condition dropped.
-/
theorem forall_exists_discOffset_gt (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, B < discOffset f out.d out.m n := by
  intro B
  rcases out.forall_exists_discOffset_gt_witness_pos (f := f) B with ⟨n, _hnpos, hn⟩
  exact ⟨n, hn⟩

/-- Positive-length witness form: Stage 2 yields arbitrarily large bundled offset nuclei
`Int.natAbs (apSumOffset f out.d out.m n)`, with witnesses `n > 0`.

This is a thin wrapper around
`Tao2015.UnboundedDiscOffset.forall_exists_natAbs_apSumOffset_gt_witness_pos`.
-/
theorem forall_exists_natAbs_apSumOffset_gt_witness_pos (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ Int.natAbs (apSumOffset f out.d out.m n) > B := by
  have hunb : UnboundedDiscOffset f out.d out.m := out.unboundedDiscOffset (f := f)
  simpa using
    (Tao2015.UnboundedDiscOffset.forall_exists_natAbs_apSumOffset_gt_witness_pos
      (f := f) (d := out.d) (m := out.m) hunb)

/-- Witness form: Stage 2 yields arbitrarily large bundled offset nuclei
`Int.natAbs (apSumOffset f out.d out.m n)`.

This is `forall_exists_natAbs_apSumOffset_gt_witness_pos` with the positivity side condition
dropped.
-/
theorem forall_exists_natAbs_apSumOffset_gt (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f out.d out.m n) := by
  intro B
  rcases out.forall_exists_natAbs_apSumOffset_gt_witness_pos (f := f) B with ⟨n, _hnpos, hn⟩
  exact ⟨n, (gt_iff_lt).1 hn⟩

/-- Negation-normal-form unboundedness statement for the bundled offset discrepancies
`discOffset f out.d out.m`.

Negation-normal form:
`¬ ∃ B, ∀ n, discOffset f out.d out.m n ≤ B`.

This is a thin wrapper around
`Tao2015.unboundedDiscOffset_iff_not_exists_forall_discOffset_le`.
-/
theorem not_exists_forall_discOffset_le (out : Stage2Output f) :
    ¬ ∃ B : ℕ, ∀ n : ℕ, discOffset f out.d out.m n ≤ B := by
  have hunb : UnboundedDiscOffset f out.d out.m := out.unboundedDiscOffset (f := f)
  exact
    (Tao2015.unboundedDiscOffset_iff_not_exists_forall_discOffset_le (f := f)
        (d := out.d) (m := out.m)).1
      hunb

end Stage2Output

end Tao2015

end MoltResearch
