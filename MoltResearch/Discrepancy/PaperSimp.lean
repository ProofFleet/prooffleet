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

attribute [simp]
  natAbs_sum_Icc_eq_discOffset'
  natAbs_sum_Icc_of_le_affineEndpoints_eq_discOffset'

/-!
## Disable nucleus → paper rewrites as simp rules (loop avoidance)

These are useful rewrite lemmas, but if both directions are simp rules, `simp` may loop.
We therefore explicitly turn them off in this opt-in simp module.
-/

attribute [-simp]
  apSum_eq_sum_Icc
  apSumOffset_eq_sum_Icc
  apSumFrom_eq_sum_Icc

end MoltResearch
