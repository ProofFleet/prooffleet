import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2WindowErrors

/-!
# Track R A2-V': the explicit-window outer band

The outer transform tail is paid by choosing `K2` proportional to
`B' A/(eps H)`.  The displayed constant `1105920 = 768 * 1440` records all
margins: the enlarged harmonic interval costs four, `2A+1` costs `3A`, and
the two decay fractions cost `10/K2²`.
-/

namespace MoltResearch

namespace Tao2015

open Finset ExpSums

/-- Cross-multiplied sufficient condition for the outer-band slot. -/
theorem sliceA2_outer_slot_fit
    (A s U H : ℕ) (eps epsGeom K2 : ℝ)
    (hA : 1 ≤ A) (hK2 : 0 < K2) (hK2A : K2 ≤ A)
    (henlarged : (s + 2 * H + 4 * U : ℕ) / (A : ℝ) ≤
      4 * ∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n)
    (hfit : 1105920 * Real.exp Real.pi *
        explicitSliceWindowDerivBound epsGeom ^ 2 * (A : ℝ) ^ 2 ≤
      eps ^ 2 * (H : ℝ) ^ 2 * Real.pi ^ 2 * K2 ^ 2) :
    (4 * explicitSliceWindowDerivBound epsGeom ^ 2 / Real.pi ^ 2) *
        ((2 * (A : ℝ) + 1) ^ 2 *
          (Real.exp Real.pi * ((4 / (K2 * (A : ℝ))) + (6 / K2 ^ 2)) *
            (∑ n ∈ Finset.Ioc A (A + s + 2 * H + 4 * U),
              (1 : ℝ) / n))) ≤
      eps ^ 2 * (H : ℝ) ^ 2 *
        (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) / 768 := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hpi : 0 < Real.pi := Real.pi_pos
  have hW0 : 0 ≤ ∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n :=
    Finset.sum_nonneg fun n _ => by positivity
  have hWext0 : 0 ≤
      ∑ n ∈ Finset.Ioc A (A + s + 2 * H + 4 * U), (1 : ℝ) / n :=
    Finset.sum_nonneg fun n _ => by positivity
  have hWext :
      ∑ n ∈ Finset.Ioc A (A + s + 2 * H + 4 * U), (1 : ℝ) / n ≤
        4 * ∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n := by
    have hupp := sliceA2_harmonic_upper A (s + 2 * H + 4 * U) hA
    simpa only [show A + (s + 2 * H + 4 * U) =
      A + s + 2 * H + 4 * U by omega] using hupp.trans henlarged
  have hKsq : 0 < K2 ^ 2 := sq_pos_of_pos hK2
  have hKprod : 0 < K2 * (A : ℝ) := mul_pos hK2 hAR
  have hden : K2 ^ 2 ≤ K2 * (A : ℝ) := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hK2A hK2.le
  have hone : (1 : ℝ) / (K2 * (A : ℝ)) ≤ 1 / K2 ^ 2 :=
    one_div_le_one_div_of_le hKsq hden
  have hfreq : 4 / (K2 * (A : ℝ)) + 6 / K2 ^ 2 ≤ 10 / K2 ^ 2 := by
    have hfour := mul_le_mul_of_nonneg_left hone (by norm_num : (0 : ℝ) ≤ 4)
    calc
      4 / (K2 * (A : ℝ)) + 6 / K2 ^ 2 ≤
          4 / K2 ^ 2 + 6 / K2 ^ 2 := by
        gcongr
      _ = 10 / K2 ^ 2 := by ring
  have hAfac : (2 * (A : ℝ) + 1) ^ 2 ≤ (3 * (A : ℝ)) ^ 2 := by
    have hlin : 2 * (A : ℝ) + 1 ≤ 3 * A := by
      have : (1 : ℝ) ≤ A := by exact_mod_cast hA
      linarith
    exact pow_le_pow_left₀ (by positivity) hlin 2
  have hmain :
      (4 * explicitSliceWindowDerivBound epsGeom ^ 2 / Real.pi ^ 2) *
          ((2 * (A : ℝ) + 1) ^ 2 *
            (Real.exp Real.pi * ((4 / (K2 * (A : ℝ))) + (6 / K2 ^ 2)) *
              (∑ n ∈ Finset.Ioc A (A + s + 2 * H + 4 * U),
                (1 : ℝ) / n))) ≤
        1440 * Real.exp Real.pi * explicitSliceWindowDerivBound epsGeom ^ 2 *
          (A : ℝ) ^ 2 *
            (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) /
              (Real.pi ^ 2 * K2 ^ 2) := by
    calc
      (4 * explicitSliceWindowDerivBound epsGeom ^ 2 / Real.pi ^ 2) *
          ((2 * (A : ℝ) + 1) ^ 2 *
            (Real.exp Real.pi * ((4 / (K2 * (A : ℝ))) + (6 / K2 ^ 2)) *
              (∑ n ∈ Finset.Ioc A (A + s + 2 * H + 4 * U),
                (1 : ℝ) / n))) ≤
        (4 * explicitSliceWindowDerivBound epsGeom ^ 2 / Real.pi ^ 2) *
          ((3 * (A : ℝ)) ^ 2 *
            (Real.exp Real.pi * (10 / K2 ^ 2) *
              (4 * ∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n))) := by
          gcongr
      _ = 1440 * Real.exp Real.pi * explicitSliceWindowDerivBound epsGeom ^ 2 *
          (A : ℝ) ^ 2 *
            (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) /
              (Real.pi ^ 2 * K2 ^ 2) := by field_simp; ring
  have hscaled :
      (1105920 * Real.exp Real.pi *
        explicitSliceWindowDerivBound epsGeom ^ 2 * (A : ℝ) ^ 2) *
          ((∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) /
            (768 * Real.pi ^ 2 * K2 ^ 2)) ≤
      (eps ^ 2 * (H : ℝ) ^ 2 * Real.pi ^ 2 * K2 ^ 2) *
          ((∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) /
            (768 * Real.pi ^ 2 * K2 ^ 2)) :=
    mul_le_mul_of_nonneg_right hfit (by positivity)
  calc
    _ ≤ 1440 * Real.exp Real.pi * explicitSliceWindowDerivBound epsGeom ^ 2 *
          (A : ℝ) ^ 2 *
            (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) /
              (Real.pi ^ 2 * K2 ^ 2) := hmain
    _ = (1105920 * Real.exp Real.pi *
        explicitSliceWindowDerivBound epsGeom ^ 2 * (A : ℝ) ^ 2) *
          ((∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) /
            (768 * Real.pi ^ 2 * K2 ^ 2)) := by
      field_simp
      ring
    _ ≤ (eps ^ 2 * (H : ℝ) ^ 2 * Real.pi ^ 2 * K2 ^ 2) *
          ((∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) /
            (768 * Real.pi ^ 2 * K2 ^ 2)) := hscaled
    _ = eps ^ 2 * (H : ℝ) ^ 2 *
        (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) / 768 := by
      field_simp

end Tao2015

end MoltResearch
