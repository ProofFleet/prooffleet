import MoltResearch.Discrepancy.ExpSums

/-!
# Track R, phase R4v: the linear-phase exponential sum (V1)

The geometric-series bound for the linear phase: away from the integers,
`‖∑_{M ≤ n ≤ N} e(nβ)‖ ≤ 1/‖β‖`, with `‖β‖ = nint β` the distance from
`β` to the nearest integer.  This is `kusmin_landau` at the constant
increment `β − round β`, after the integer part is discarded by
periodicity — the first brick of the Type I/II estimates behind the
Vinogradov classification (`PrimeBlockMajorArcAssumption`).
-/

namespace MoltResearch

namespace ExpSums

open Finset

/-- Periodicity at integer multiples: `e(nβ) = e(n(β − round β))`. -/
theorem e_nat_mul_sub_round (β : ℝ) (n : ℕ) :
    e ((n : ℝ) * β) = e ((n : ℝ) * (β - (round β : ℝ))) := by
  have h : (n : ℝ) * β
      = (n : ℝ) * (β - (round β : ℝ)) + ((n * round β : ℤ) : ℝ) := by
    push_cast
    ring
  rw [h, e_add, e_intCast, mul_one]

/-- **The linear-phase Kusmin–Landau bound** (Track R, V1): for `β` at
distance `nint β > 0` from the integers,
`‖∑_{n ∈ Ico M (N+1)} e(nβ)‖ ≤ 1/nint β`. -/
theorem norm_sum_e_linear_le {β : ℝ} (hβ : 0 < nint β) (M N : ℕ)
    (hMN : M ≤ N) :
    ‖∑ n ∈ Finset.Ico M (N + 1), e ((n : ℝ) * β)‖ ≤ 1 / nint β := by
  have hper : ∑ n ∈ Finset.Ico M (N + 1), e ((n : ℝ) * β)
      = ∑ n ∈ Finset.Ico M (N + 1),
          e ((n : ℝ) * (β - (round β : ℝ))) := by
    exact Finset.sum_congr rfl fun n _ => e_nat_mul_sub_round β n
  rw [hper]
  set γ : ℝ := β - (round β : ℝ) with hγ_def
  have hγ_abs : nint β = |γ| := rfl
  have hγ_half : |γ| ≤ 1 / 2 := by
    rw [← hγ_abs]
    exact nint_le_half β
  have hγ_ne : γ ≠ 0 := by
    intro hc
    rw [hγ_abs, hc, abs_zero] at hβ
    exact lt_irrefl 0 hβ
  rcases lt_or_gt_of_ne hγ_ne with hneg | hpos
  · -- negative increment: conjugate and apply the positive case
    have hconj : ‖∑ n ∈ Finset.Ico M (N + 1), e ((n : ℝ) * γ)‖
        = ‖∑ n ∈ Finset.Ico M (N + 1), e ((n : ℝ) * (-γ))‖ := by
      rw [← RCLike.norm_conj (∑ n ∈ Finset.Ico M (N + 1), e ((n : ℝ) * γ)),
        map_sum]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [e_conj]
      ring_nf
    rw [hconj]
    have h1 : 0 < -γ := by linarith
    have h2 : -γ ≤ 1 - -γ := by
      have : -γ ≤ 1/2 := by
        rw [abs_of_neg hneg] at hγ_half
        linarith
      linarith
    have hkl := kusmin_landau (φ := fun n => (n : ℝ) * (-γ)) (θ := -γ)
      h1 hMN
      (fun n _ _ => by push_cast; ring_nf; linarith)
      (fun n _ _ => by push_cast; ring_nf; linarith [h2])
      (fun n _ _ => by push_cast; ring_nf; linarith)
    refine le_trans hkl ?_
    rw [hγ_abs, abs_of_neg hneg]
  · -- positive increment: apply Kusmin–Landau directly
    have h2 : γ ≤ 1 - γ := by
      have : γ ≤ 1/2 := by
        rw [abs_of_pos hpos] at hγ_half
        linarith
      linarith
    have hkl := kusmin_landau (φ := fun n => (n : ℝ) * γ) (θ := γ)
      hpos hMN
      (fun n _ _ => by push_cast; ring_nf; linarith)
      (fun n _ _ => by push_cast; ring_nf; linarith [h2])
      (fun n _ _ => by push_cast; ring_nf; linarith)
    refine le_trans hkl ?_
    rw [hγ_abs, abs_of_pos hpos]

/-- The trivial companion: the linear sum is at most its length. -/
theorem norm_sum_e_linear_le_card (β : ℝ) (s : Finset ℕ) :
    ‖∑ n ∈ s, e ((n : ℝ) * β)‖ ≤ (s.card : ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  have h : ∀ n ∈ s, ‖e ((n : ℝ) * β)‖ = 1 := fun n _ => norm_e _
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul, mul_one]

end ExpSums

end MoltResearch
