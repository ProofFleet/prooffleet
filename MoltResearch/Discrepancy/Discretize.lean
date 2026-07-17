import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Complex.Basic

/-!
# Discrepancy: the coordinate-grid discretization

Track C, Elliott campaign (`Problems/tao2015_derivation_c.md`, issue #2946, E6b): the
paper discretizes `g` to the lattice `ε²·ℤ[i]` so that the pattern variables `X_H`
take `O_ε(1)` values. We round the real and imaginary parts to the `(2/K)`-grid on
`[-1, 1]` — same effect, no trigonometry, no wraparound:

* `roundCoord K x : Fin (K+1)` and `coordVal` — rounding one coordinate; error
  `≤ 2/K` on `[-1, 1]`.
* `roundC K z : Fin (K+1) × Fin (K+1)` and `roundCVal` — rounding a disk element;
  error `≤ 4/K`; the rounded values stay in the closed square (norm `≤ 2`).

`Fin (K+1) × Fin (K+1)` is the finite alphabet whose `H`-fold power carries `X_H`.
-/

namespace MoltResearch

open Finset

/-- Round `x ∈ [-1, 1]` to the `(2/K)`-grid: the index of the grid point. -/
noncomputable def roundCoord (K : ℕ) (x : ℝ) : Fin (K + 1) :=
  ⟨min ⌊(x + 1) * K / 2⌋₊ K, by omega⟩

/-- The grid point with index `j`: `-1 + 2j/K`. -/
noncomputable def coordVal (K : ℕ) (j : Fin (K + 1)) : ℝ :=
  -1 + 2 * (j : ℝ) / K

/-- Rounding a coordinate moves it by at most `2/K` on `[-1, 1]`. -/
theorem abs_sub_coordVal_roundCoord_le {K : ℕ} (hK : 0 < K) {x : ℝ}
    (hx : |x| ≤ 1) :
    |x - coordVal K (roundCoord K x)| ≤ 2 / K := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hx1 : -1 ≤ x := by
    have := abs_le.mp hx
    exact this.1
  have hx2 : x ≤ 1 := (abs_le.mp hx).2
  set t : ℝ := (x + 1) * K / 2 with ht
  have ht0 : 0 ≤ t := by
    rw [ht]
    have : (0 : ℝ) ≤ x + 1 := by linarith
    positivity
  have htK : t ≤ K := by
    rw [ht]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    nlinarith
  -- the index is min ⌊t⌋ K; in both cases |t − j| ≤ 1
  set j : ℕ := min ⌊t⌋₊ K with hj
  have hjt : |t - (j : ℝ)| ≤ 1 := by
    rcases Nat.lt_or_ge K (⌊t⌋₊) with hfl | hfl
    swap
    · have hjeq : j = ⌊t⌋₊ := by rw [hj]; omega
      rw [hjeq]
      have h1 := Nat.floor_le ht0
      have h2 := Nat.lt_floor_add_one t
      rw [abs_le]
      constructor <;> linarith
    · have hjeq : j = K := by rw [hj]; omega
      rw [hjeq]
      have h1 : (K : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast le_of_lt hfl
      have h2 := Nat.floor_le ht0
      rw [abs_le]
      constructor <;> linarith
  -- translate back: x = -1 + 2t/K, val = -1 + 2j/K
  have hxval : x - coordVal K (roundCoord K x) = 2 * (t - (j : ℝ)) / K := by
    rw [coordVal, roundCoord]
    have hcoe : ((⟨min ⌊t⌋₊ K, by omega⟩ : Fin (K + 1)) : ℝ) = (j : ℝ) := by
      rw [hj]
    rw [hcoe, ht]
    field_simp
    ring
  rw [hxval]
  rw [abs_div, abs_of_pos hKR, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [div_le_div_iff₀ hKR hKR]
  nlinarith [hjt]

/-- Round a disk element coordinatewise. -/
noncomputable def roundC (K : ℕ) (z : ℂ) : Fin (K + 1) × Fin (K + 1) :=
  (roundCoord K z.re, roundCoord K z.im)

/-- The grid point of a pair of indices. -/
noncomputable def roundCVal (K : ℕ) (jk : Fin (K + 1) × Fin (K + 1)) : ℂ :=
  ⟨coordVal K jk.1, coordVal K jk.2⟩

/-- Rounding a disk element moves it by at most `4/K`. -/
theorem norm_sub_roundCVal_le {K : ℕ} (hK : 0 < K) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖z - roundCVal K (roundC K z)‖ ≤ 4 / K := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hre : |z.re| ≤ 1 := le_trans (Complex.abs_re_le_norm z) hz
  have him : |z.im| ≤ 1 := le_trans (Complex.abs_im_le_norm z) hz
  have h1 := abs_sub_coordVal_roundCoord_le hK hre
  have h2 := abs_sub_coordVal_roundCoord_le hK him
  have hcomp : z - roundCVal K (roundC K z)
      = ⟨z.re - coordVal K (roundCoord K z.re),
         z.im - coordVal K (roundCoord K z.im)⟩ := by
    rw [roundCVal, roundC]
    rfl
  rw [hcomp]
  refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
  rw [show (Complex.mk (z.re - coordVal K (roundCoord K z.re))
      (z.im - coordVal K (roundCoord K z.im))).re
      = z.re - coordVal K (roundCoord K z.re) from rfl]
  rw [show (Complex.mk (z.re - coordVal K (roundCoord K z.re))
      (z.im - coordVal K (roundCoord K z.im))).im
      = z.im - coordVal K (roundCoord K z.im) from rfl]
  have hsum : 2 / (K : ℝ) + 2 / K = 4 / K := by ring
  linarith [h1, h2]

/-- Grid values stay in the closed unit square: norm at most `2`. -/
theorem norm_roundCVal_le {K : ℕ} (hK : 0 < K) (jk : Fin (K + 1) × Fin (K + 1)) :
    ‖roundCVal K jk‖ ≤ 2 := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hcoord : ∀ j : Fin (K + 1), |coordVal K j| ≤ 1 := by
    intro j
    rw [coordVal, abs_le]
    have hjn : (j : ℕ) ≤ K := by
      have := j.2
      omega
    have hj : (j : ℝ) ≤ (K : ℝ) := by exact_mod_cast hjn
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
    constructor
    · have : (0 : ℝ) ≤ 2 * (j : ℝ) / K := by positivity
      linarith
    · have h2j : 2 * (j : ℝ) / K ≤ 2 := by
        rw [div_le_iff₀ hKR]
        linarith
      linarith
  have h1 := hcoord jk.1
  have h2 := hcoord jk.2
  have habs : ‖roundCVal K jk‖ ≤ |(roundCVal K jk).re| + |(roundCVal K jk).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  have hre : (roundCVal K jk).re = coordVal K jk.1 := rfl
  have him : (roundCVal K jk).im = coordVal K jk.2 := rfl
  rw [hre, him] at habs
  linarith

end MoltResearch
