import MoltResearch.Discrepancy.ArchimedeanTaylor

/-!
# Track C: the major-arc phase freeze (Track R, C4e-10)

Opening of the major-arc expansion arc: at `α = a/q + δ` the interface
phase `e(jα)` splits into the progression part `e(ja/q)` and a slowly
varying `δ`-phase. On a block of length `ℓ` the `δ`-phase may be frozen
at the block anchor at cost `2π|δ|ℓ` per term (the chord bound of
`ArchimedeanTaylor`). The block partition of `[1, H]` (next unit)
turns the interface's window sums into frozen progression sums with
total error `O(|δ|·ℓ·H)` — polylog-affordable on the major arcs, where
`|δ| ≤ C(log H)^B/(Hq)`.
-/

open Finset

namespace MoltResearch

/-- **The phase freeze** (C4e-10): on a block of length `ℓ`, a slowly
varying phase `e(jδ)` may be frozen at the block anchor `j₀` at cost
`2π|δ|ℓ` per term — the chord bound applied to the increment. This is
the sub-block step of the major-arc expansion: `α = a/q + δ` splits the
interface phase into the progression part `e(ja/q)` and a `δ`-phase
frozen blockwise. -/
theorem norm_sum_mul_exp_freeze_sub_le (B : Finset ℕ) (j₀ ℓ : ℕ)
    (hB : ∀ j ∈ B, j₀ ≤ j ∧ j < j₀ + ℓ) (h : ℕ → ℂ)
    (hb : ∀ j, ‖h j‖ ≤ 1) (δ : ℝ) :
    ‖(∑ j ∈ B, h j * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (δ : ℂ)))
        - Complex.exp (2 * Real.pi * Complex.I * (j₀ : ℂ) * (δ : ℂ)) * ∑ j ∈ B, h j‖
      ≤ (B.card : ℝ) * (2 * Real.pi * |δ| * ℓ) := by
  classical
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  have hpt : ∀ j ∈ B,
      ‖h j * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (δ : ℂ))
        - Complex.exp (2 * Real.pi * Complex.I * (j₀ : ℂ) * (δ : ℂ)) * h j‖
      ≤ 2 * Real.pi * |δ| * ℓ := by
    intro j hj
    obtain ⟨hj₀, hjℓ⟩ := hB j hj
    have hexp_split : Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (δ : ℂ))
        = Complex.exp (2 * Real.pi * Complex.I * (j₀ : ℂ) * (δ : ℂ))
          * Complex.exp (Complex.I * ((2 * Real.pi * ((j : ℝ) - (j₀ : ℝ)) * δ : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hfactor : h j * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (δ : ℂ))
        - Complex.exp (2 * Real.pi * Complex.I * (j₀ : ℂ) * (δ : ℂ)) * h j
        = h j * Complex.exp (2 * Real.pi * Complex.I * (j₀ : ℂ) * (δ : ℂ))
          * (Complex.exp (Complex.I * ((2 * Real.pi * ((j : ℝ) - (j₀ : ℝ)) * δ : ℝ) : ℂ)) - 1) := by
      rw [hexp_split]
      ring
    rw [hfactor, norm_mul, norm_mul]
    have hnorm_exp : ‖Complex.exp (2 * Real.pi * Complex.I * (j₀ : ℂ) * (δ : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      have : (2 * Real.pi * Complex.I * (j₀ : ℂ) * (δ : ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [this, Real.exp_zero]
    have hchord := norm_exp_I_mul_sub_one_le (2 * Real.pi * ((j : ℝ) - (j₀ : ℝ)) * δ)
    have habs : |2 * Real.pi * ((j : ℝ) - (j₀ : ℝ)) * δ| ≤ 2 * Real.pi * |δ| * ℓ := by
      rw [abs_mul, abs_mul]
      have h2π : |2 * Real.pi| = 2 * Real.pi := abs_of_pos (by positivity)
      have hgap : |(j : ℝ) - (j₀ : ℝ)| ≤ ℓ := by
        rw [abs_of_nonneg (by
          have : (j₀ : ℝ) ≤ j := by exact_mod_cast hj₀
          linarith)]
        have : (j : ℝ) < (j₀ : ℝ) + ℓ := by exact_mod_cast hjℓ
        linarith
      rw [h2π]
      have hδ0 : (0:ℝ) ≤ |δ| := abs_nonneg _
      have hπ0 : (0:ℝ) ≤ 2 * Real.pi := by positivity
      calc 2 * Real.pi * |(j : ℝ) - (j₀ : ℝ)| * |δ|
          ≤ 2 * Real.pi * ℓ * |δ| := by
            refine mul_le_mul_of_nonneg_right ?_ hδ0
            exact mul_le_mul_of_nonneg_left hgap hπ0
        _ = 2 * Real.pi * |δ| * ℓ := by ring
    calc ‖h j‖ * ‖Complex.exp (2 * Real.pi * Complex.I * (j₀ : ℂ) * (δ : ℂ))‖
          * ‖Complex.exp (Complex.I * ((2 * Real.pi * ((j : ℝ) - (j₀ : ℝ)) * δ : ℝ) : ℂ)) - 1‖
        ≤ 1 * 1 * |2 * Real.pi * ((j : ℝ) - (j₀ : ℝ)) * δ| := by
          refine mul_le_mul (by rw [hnorm_exp]; exact mul_le_mul (hb j) le_rfl zero_le_one (by norm_num)) hchord (norm_nonneg _) (by norm_num)
      _ = |2 * Real.pi * ((j : ℝ) - (j₀ : ℝ)) * δ| := by ring
      _ ≤ 2 * Real.pi * |δ| * ℓ := habs
  calc ∑ j ∈ B, ‖h j * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (δ : ℂ))
        - Complex.exp (2 * Real.pi * Complex.I * (j₀ : ℂ) * (δ : ℂ)) * h j‖
      ≤ ∑ j ∈ B, 2 * Real.pi * |δ| * ℓ := Finset.sum_le_sum hpt
    _ = (B.card : ℝ) * (2 * Real.pi * |δ| * ℓ) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end MoltResearch
