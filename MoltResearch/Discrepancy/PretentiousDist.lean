import MoltResearch.Discrepancy.LogAvgCorr

/-!
# Discrepancy: pretentious (Granville–Soundararajan) distance, finite-`N` form

Language-layer module for the Tao 2015 analytic core (`Problems/tao2015_analytic_core.md`):
the finite-truncation pretentious distance used to state the non-pretentiousness hypothesis of
the logarithmically averaged Elliott theorem (arXiv:1509.05422):

`𝔻(g, h; N)² = ∑_{p prime, p < N} (1 - Re(g p * conj (h p))) / p`.

Conventions:
- The prime range is `Nat.primesBelow N` (primes strictly below `N`) — the Mathlib-idiomatic
  finite prime truncation; interfaces quantifying over all `N` are insensitive to `< N` vs `≤ N`.
- The **squared** distance `pretentiousDistSq` is the primary definition (the literature works
  with `𝔻²` throughout); `pretentiousDist` is its square root.
- Junk values are embraced: without unimodularity hypotheses the summands can be negative, so
  the order lemmas below carry `Unimodular` hypotheses rather than baking them into the
  definition.

Monotonicity basics (this module deliberately stops here):
- `pretentiousDistSq_summand_nonneg`, `pretentiousDistSq_nonneg` — nonnegativity for unimodular
  arguments.
- `pretentiousDistSq_mono` / `pretentiousDist_mono` — monotone in the truncation `N`.
- `Unimodular.pretentiousDistSq_self` — the diagonal vanishes (each summand is `0`).
-/

namespace MoltResearch

/-- Squared finite-`N` pretentious distance (Granville–Soundararajan):

`pretentiousDistSq g h N = ∑_{p prime, p < N} (1 - Re(g p * conj (h p))) / p`.

The non-pretentiousness hypothesis of the log-Elliott interface says this tends to `∞` with `N`
for every character-modulated comparison `h`.
-/
noncomputable def pretentiousDistSq (g h : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ p ∈ N.primesBelow, (1 - (g p * (starRingEnd ℂ) (h p)).re) / p

/-- Finite-`N` pretentious distance: the square root of `pretentiousDistSq`. -/
noncomputable def pretentiousDist (g h : ℕ → ℂ) (N : ℕ) : ℝ :=
  Real.sqrt (pretentiousDistSq g h N)

/-- Degenerate truncation: no primes below `0`. -/
@[simp] theorem pretentiousDistSq_zero_N (g h : ℕ → ℂ) : pretentiousDistSq g h 0 = 0 := by
  simp [pretentiousDistSq]

variable {g h : ℕ → ℂ}

/-- Each summand of `pretentiousDistSq` is nonnegative for unimodular arguments:
`Re(g p * conj (h p)) ≤ ‖g p * conj (h p)‖ = 1`, and the denominator is a `ℕ`-cast. -/
theorem pretentiousDistSq_summand_nonneg (hg : Unimodular g) (hh : Unimodular h) (p : ℕ) :
    0 ≤ (1 - (g p * (starRingEnd ℂ) (h p)).re) / p := by
  apply div_nonneg
  · have hre : (g p * (starRingEnd ℂ) (h p)).re ≤ 1 := by
      calc (g p * (starRingEnd ℂ) (h p)).re
          ≤ ‖g p * (starRingEnd ℂ) (h p)‖ := Complex.re_le_norm _
        _ = 1 := by rw [norm_mul, hg p, RCLike.norm_conj, hh p, one_mul]
    linarith
  · exact Nat.cast_nonneg p

/-- Nonnegativity of the squared pretentious distance for unimodular arguments. -/
theorem pretentiousDistSq_nonneg (hg : Unimodular g) (hh : Unimodular h) (N : ℕ) :
    0 ≤ pretentiousDistSq g h N :=
  Finset.sum_nonneg fun p _ => pretentiousDistSq_summand_nonneg hg hh p

/-- The squared pretentious distance is monotone in the truncation `N`
(for unimodular arguments, so that the added summands are nonnegative). -/
theorem pretentiousDistSq_mono (hg : Unimodular g) (hh : Unimodular h) {N M : ℕ}
    (hNM : N ≤ M) :
    pretentiousDistSq g h N ≤ pretentiousDistSq g h M := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 hNM, hp.2⟩
  · intro p _ _
    exact pretentiousDistSq_summand_nonneg hg hh p

/-- The pretentious distance is nonnegative (unconditionally: it is a square root). -/
theorem pretentiousDist_nonneg (g h : ℕ → ℂ) (N : ℕ) : 0 ≤ pretentiousDist g h N :=
  Real.sqrt_nonneg _

/-- The pretentious distance is monotone in the truncation `N` (unimodular arguments). -/
theorem pretentiousDist_mono (hg : Unimodular g) (hh : Unimodular h) {N M : ℕ}
    (hNM : N ≤ M) :
    pretentiousDist g h N ≤ pretentiousDist g h M :=
  Real.sqrt_le_sqrt (pretentiousDistSq_mono hg hh hNM)

namespace Unimodular

/-- Diagonal degeneracy: a unimodular sequence is at squared distance `0` from itself
(each summand has `Re(g p * conj (g p)) = 1`). -/
theorem pretentiousDistSq_self (hg : Unimodular g) (N : ℕ) :
    pretentiousDistSq g g N = 0 := by
  unfold pretentiousDistSq
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [hg.mul_conj_self p]
  simp

/-- Diagonal degeneracy for the (unsquared) distance. -/
theorem pretentiousDist_self (hg : Unimodular g) (N : ℕ) :
    pretentiousDist g g N = 0 := by
  rw [pretentiousDist, hg.pretentiousDistSq_self N, Real.sqrt_zero]

end Unimodular

end MoltResearch
