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

/-- Convenience projection: the affine-tail start index `m*d` bundled in Stage 1. -/
abbrev start (out : Stage2Output f) : ℕ := out.m * out.d

/-- Definitional rewrite: the affine-tail start index is `m*d`.

This lemma is intentionally tiny (and not a simp lemma): it exists mainly to reduce `dsimp` noise
in downstream arithmetic rewrites.
-/
theorem start_eq_m_mul_d (out : Stage2Output f) : out.start = out.m * out.d := by
  rfl

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
  unfold discOffset
  -- Rewrite the bundled offset nucleus `apSumOffset` to the affine-tail nucleus `apSumFrom`.
  rw [← out.apSumFrom_start_eq_apSumOffset (f := f) n]

/-- Positive-length witness form: Stage 2 yields arbitrarily large bundled offset discrepancies
`discOffset f out.d out.m n`, with witnesses `n > 0`.

We keep this lemma in `TrackCStage2CoreExtras.lean` so downstream stages can access it without
importing the large Stage-2 output-lemma library `TrackCStage2Output.lean`.
-/
theorem forall_exists_discOffset_gt_witness_pos (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ B < discOffset f out.d out.m n := by
  have hunb : UnboundedDiscOffset f out.d out.m := out.unboundedDiscOffset (f := f)
  exact UnboundedDiscOffset.forall_exists_discOffset_gt_witness_pos (hunb := hunb)

/-- The affine-tail start index `out.start` is a multiple of the reduced step size `out.d`. -/
theorem d_dvd_start (out : Stage2Output f) : out.d ∣ out.start := by
  -- `out.start` is definitionally `m*d`.
  simp [Stage2Output.start]

/-- The affine-tail start index `out.start` has remainder `0` when reduced modulo `out.d`.

This is often the most convenient form of `d_dvd_start` for arithmetic rewriting.
-/
theorem start_mod_d (out : Stage2Output f) : out.start % out.d = 0 := by
  exact Nat.mod_eq_zero_of_dvd (d_dvd_start (f := f) out)

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

/-- Recover the offset parameter `out.m` by dividing the start index `out.start` by the step size
`out.d`.

This is a tiny arithmetic convenience lemma: `out.start = out.m * out.d` by definition.
-/
theorem start_div_d (out : Stage2Output f) : out.start / out.d = out.m := by
  -- `out.out1.hd` is the only side condition needed for `Nat.mul_div_left`.
  have hd' : 0 < out.d := by
    simpa [Stage2Output.d] using out.out1.hd
  simpa [Stage2Output.start] using (Nat.mul_div_left out.m hd')

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

/-- Tail-nucleus witness form without the positive-length side condition.

This is a small convenience corollary of
`Stage2Output.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos`.
-/
theorem forall_exists_natAbs_apSumFrom_start_gt (out : Stage2Output f) :
    ∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f out.start out.d n) > B := by
  intro B
  rcases out.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f := f) B with ⟨n, _hnpos, hgt⟩
  exact ⟨n, hgt⟩

end Stage2Output

end Tao2015

end MoltResearch
