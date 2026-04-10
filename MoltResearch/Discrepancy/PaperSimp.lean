import MoltResearch.Discrepancy

/-!
# Paper endpoint simp rules

This module opts into a one-line `simp` pipeline for rewriting common “paper” interval sums over
`Finset.Icc` into the nucleus objects (`apSum`, `apSumOffset`, `apSumFrom`) and their associated
`discOffset`/`discrepancy` wrappers.

It is intentionally **opt-in**: enabling these simp rules globally can create simp loops (because
many of the nucleus objects also have lemmas rewriting *back* to `Finset.Icc` sums).

Import this file when you want `simp` to transparently turn a goal/assumption like
`Int.natAbs ((Finset.Icc (m+1) n).sum (fun i => f (a+i*d))) ≤ C`
into the corresponding `discOffset` statement in one line.
-/

namespace MoltResearch

/-!
## Paper `natAbs` goals: `simp` directly to `discOffset`

Making the raw `sum_Icc_eq_apSumOffset*` lemmas simp rules tends to create simp loops because the
nucleus objects are definable in terms of interval sums.

Instead, we provide *targeted* simp lemmas that rewrite the most common paper-level
`Int.natAbs (∑ Icc ...)` expressions directly into `discOffset`.
-/

-- Homogeneous tail: `∑_{i=m+1}^{m+n} f (i*d)`.
lemma natAbs_sum_Icc_eq_discOffset'
    (f : ℕ → ℤ) (d m n : ℕ) :
    Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) = discOffset f d m n := by
  -- The repo's canonical lemma uses `.natAbs`; rewrite via definitional equality.
  simpa using (natAbs_sum_Icc_eq_discOffset (f := f) (d := d) (m := m) (n := n))

-- Affine endpoints (`m ≤ n`): `∑_{i=m+1}^n f (a + i*d)` → translation-friendly `discOffset`.
lemma natAbs_sum_Icc_of_le_affineEndpoints_eq_discOffset'
    (f : ℕ → ℤ) (a d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    Int.natAbs ((Finset.Icc (m + 1) n).sum (fun i => f (a + i * d))) =
        discOffset (fun k => f (a + k)) d m (n - m) := by
  -- Unfold `discOffset` and rewrite the paper sum into `apSumOffset` using the existing bridge.
  rw [discOffset_def]
  have hs :
      (Finset.Icc (m + 1) n).sum (fun i => f (a + i * d)) =
        apSumOffset (fun k => f (a + k)) d m (n - m) := by
    simpa using
      (sum_Icc_eq_apSumOffset_of_le_affineEndpoints (f := f) (a := a) (d := d) (m := m) (n := n)
        hmn)
  simpa [hs]

-- Common paper form: `∑_{i=m+1}^{m+n} f (a + i*d)`.
-- This avoids having to manually provide the inequality `m ≤ m+n` and simplifies `(m+n) - m`.
lemma natAbs_sum_Icc_add_affineEndpoints_eq_discOffset'
    (f : ℕ → ℤ) (a d m n : ℕ) :
    Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d))) =
        discOffset (fun k => f (a + k)) d m n := by
  simpa [Nat.add_sub_cancel_left] using
    (natAbs_sum_Icc_of_le_affineEndpoints_eq_discOffset' (f := f) (a := a) (d := d)
      (m := m) (n := m + n) (Nat.le_add_right m n))

-- Common paper form: normalize all the way to the affine nucleus wrapper.
lemma natAbs_sum_Icc_add_affineEndpoints_eq_affineDiscrepancy'
    (f : ℕ → ℤ) (a d m n : ℕ) :
    Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d))) =
        affineDiscrepancy f (a + m * d) d n := by
  -- First land in `discOffset` via the targeted lemma.
  have h := natAbs_sum_Icc_add_affineEndpoints_eq_discOffset' (f := f) (a := a) (d := d) (m := m)
    (n := n)
  -- Then rewrite the wrapper into the affine nucleus wrapper.
  have h' : discOffset (fun k => f (a + k)) d m n = affineDiscrepancy f (a + m * d) d n := by
    rw [discOffset_def, affineDiscrepancy_def]
    -- Normalize the underlying AP sum.
    simp [apSumOffset_shift_eq_apSumFrom_tail]
  exact h.trans h'

attribute [simp]
  natAbs_sum_Icc_eq_discOffset'
  natAbs_sum_Icc_of_le_affineEndpoints_eq_discOffset'
  natAbs_sum_Icc_add_affineEndpoints_eq_discOffset'
  natAbs_sum_Icc_add_affineEndpoints_eq_affineDiscrepancy'

/-!
## Simp-loop avoidance note

This module is intentionally *targeted*: it adds simp lemmas only for the common paper-level
`Int.natAbs (∑ Icc ...)` shapes, rather than making the raw `… = apSumOffset …` rewrite lemmas simp
rules (which can interact badly with lemmas rewriting the other direction).
-/

end MoltResearch
