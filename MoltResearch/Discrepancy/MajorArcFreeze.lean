import MoltResearch.Discrepancy.ArchimedeanTaylor
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

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

/-- **The block partition** (C4e-11): the `δ`-twisted window sum over
`[1, H]` is bounded by the sum of the untwisted block norms (blocks of
length `ℓ`) plus the total freeze cost `H·2π|δ|ℓ`. Fibrewise partition
by `j ↦ (j−1)/ℓ`, the phase freeze on each block, and the fibre-count
identity. -/
theorem norm_sum_mul_exp_le_sum_blocks_add (H ℓ : ℕ) (hℓ : 0 < ℓ)
    (h : ℕ → ℂ) (hb : ∀ j, ‖h j‖ ≤ 1) (δ : ℝ) :
    ‖∑ j ∈ Finset.Icc 1 H,
        h j * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (δ : ℂ))‖
      ≤ (∑ k ∈ Finset.range (H/ℓ + 1),
          ‖∑ j ∈ (Finset.Icc 1 H).filter (fun j => (j - 1)/ℓ = k), h j‖)
        + (H : ℝ) * (2 * Real.pi * |δ| * ℓ) := by
  classical
  have hmaps : ∀ j ∈ Finset.Icc 1 H, (j - 1)/ℓ ∈ Finset.range (H/ℓ + 1) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Finset.mem_range]
    have hle : (j-1)/ℓ ≤ H/ℓ := Nat.div_le_div_right (by omega)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine le_trans (norm_sum_le _ _) ?_
  have hfib : ∀ k ∈ Finset.range (H/ℓ + 1),
      ‖∑ j ∈ (Finset.Icc 1 H).filter (fun j => (j - 1)/ℓ = k),
          h j * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (δ : ℂ))‖
      ≤ ‖∑ j ∈ (Finset.Icc 1 H).filter (fun j => (j - 1)/ℓ = k), h j‖
        + (((Finset.Icc 1 H).filter (fun j => (j - 1)/ℓ = k)).card : ℝ)
            * (2 * Real.pi * |δ| * ℓ) := by
    intro k _
    have hB : ∀ j ∈ (Finset.Icc 1 H).filter (fun j => (j - 1)/ℓ = k),
        (k*ℓ + 1) ≤ j ∧ j < (k*ℓ + 1) + ℓ := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjH⟩, hdiv⟩ := hj
      have hlow : k*ℓ ≤ j - 1 := by
        rw [← hdiv]
        exact Nat.div_mul_le_self (j-1) ℓ
      have hup : j - 1 < (k+1)*ℓ := by
        have hklt : (j-1)/ℓ < k + 1 := by omega
        exact (Nat.div_lt_iff_lt_mul hℓ).mp hklt
      rw [Nat.succ_mul] at hup
      omega
    have hfreeze := norm_sum_mul_exp_freeze_sub_le
      ((Finset.Icc 1 H).filter (fun j => (j - 1)/ℓ = k)) (k*ℓ + 1) ℓ hB h hb δ
    have hunit : ‖Complex.exp (2 * Real.pi * Complex.I * ((k*ℓ + 1 : ℕ) : ℂ) * (δ : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      have hre : (2 * Real.pi * Complex.I * ((k*ℓ + 1 : ℕ) : ℂ) * (δ : ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hre, Real.exp_zero]
    calc ‖∑ j ∈ (Finset.Icc 1 H).filter (fun j => (j - 1)/ℓ = k),
            h j * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (δ : ℂ))‖
        ≤ ‖Complex.exp (2 * Real.pi * Complex.I * ((k*ℓ + 1 : ℕ) : ℂ) * (δ : ℂ))
              * ∑ j ∈ (Finset.Icc 1 H).filter (fun j => (j - 1)/ℓ = k), h j‖
          + ‖(∑ j ∈ (Finset.Icc 1 H).filter (fun j => (j - 1)/ℓ = k),
                h j * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (δ : ℂ)))
              - Complex.exp (2 * Real.pi * Complex.I * ((k*ℓ + 1 : ℕ) : ℂ) * (δ : ℂ))
                * ∑ j ∈ (Finset.Icc 1 H).filter (fun j => (j - 1)/ℓ = k), h j‖ := by
          exact norm_le_norm_add_norm_sub' _ _
      _ ≤ ‖∑ j ∈ (Finset.Icc 1 H).filter (fun j => (j - 1)/ℓ = k), h j‖
          + (((Finset.Icc 1 H).filter (fun j => (j - 1)/ℓ = k)).card : ℝ)
              * (2 * Real.pi * |δ| * ℓ) := by
          rw [norm_mul, hunit, one_mul]
          push_cast at hfreeze ⊢
          linarith [hfreeze]
  refine le_trans (Finset.sum_le_sum hfib) ?_
  rw [Finset.sum_add_distrib]
  have hcount : ∑ k ∈ Finset.range (H/ℓ + 1),
      (((Finset.Icc 1 H).filter (fun j => (j - 1)/ℓ = k)).card : ℝ) = (H : ℝ) := by
    have hmapsTo : Set.MapsTo (fun j => (j-1)/ℓ)
        ↑(Finset.Icc 1 H) ↑(Finset.range (H/ℓ + 1)) := by
      intro j hj
      exact hmaps j hj
    have := Finset.card_eq_sum_card_fiberwise hmapsTo
    have hcard : (Finset.Icc 1 H).card = H := by
      rw [Nat.card_Icc]
      omega
    rw [hcard] at this
    exact_mod_cast this.symm
  rw [← Finset.sum_mul, hcount]


/-- **The residue-to-character expansion** (C4e-12): a block sum
restricted to a unit residue class `b` mod `q` is the `1/φ(q)`-weighted
character average of the `χ`-twisted full block sums — Dirichlet
orthogonality pointwise; non-coprime `j` vanish automatically since
every `χ` kills them. -/
theorem sum_filter_residue_eq_char_avg (q : ℕ) [NeZero q] (B : Finset ℕ)
    (F : ℕ → ℂ) (b : ZMod q) (hb : IsUnit b) :
    ∑ j ∈ B.filter (fun j : ℕ => ((j : ZMod q)) = b), F j
      = (1/(q.totient : ℂ)) * ∑ χ : DirichletCharacter ℂ q,
          χ b⁻¹ * ∑ j ∈ B, χ j * F j := by
  classical
  have hφ : (q.totient : ℂ) ≠ 0 := by
    have h0 : 0 < q.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
    exact_mod_cast h0.ne'
  have hswap : ∑ χ : DirichletCharacter ℂ q, χ b⁻¹ * ∑ j ∈ B, χ j * F j
      = ∑ j ∈ B, F j * ∑ χ : DirichletCharacter ℂ q, χ b⁻¹ * χ j := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun χ _ => ?_
    ring
  have horth : ∀ j ∈ B, F j * ∑ χ : DirichletCharacter ℂ q, χ b⁻¹ * χ j
      = if ((j : ZMod q)) = b then (q.totient : ℂ) * F j else 0 := by
    intro j _
    rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb ((j : ℕ) : ZMod q)]
    by_cases h : ((j : ZMod q)) = b
    · rw [if_pos h.symm, if_pos h]
      ring
    · rw [if_neg (fun hc => h hc.symm), if_neg h]
      ring
  rw [hswap, Finset.sum_congr rfl horth, ← Finset.sum_filter]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp


end MoltResearch
