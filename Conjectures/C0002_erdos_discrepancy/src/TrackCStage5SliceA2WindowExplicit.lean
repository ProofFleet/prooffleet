import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2Window
import MoltResearch.Discrepancy.ExplicitSliceBands

/-!
# Track R A2-V': normalized explicit-window accounting

The normalized low- and inner-band inputs are threaded through the explicit
slice window.  Its derivative envelope is now visibly linear in
`1 / epsGeom`, so the eventual lower bound on `H` can be polynomial in the
accuracy.
-/

namespace MoltResearch

namespace Tao2015

open Real Finset MeasureTheory SchwartzMap ExpSums
open scoped FourierTransform ContDiff

/-- Exact final window cost with the explicit derivative envelope. -/
noncomputable def sliceA2ExplicitWindowCost
    (A s U H : ℕ) (epsGeom K2 L ElowNorm EinnerNorm : ℝ) : ℝ :=
  sliceA2WindowCost A s U H (explicitSliceWindowDerivBound epsGeom)
    K2 L ElowNorm EinnerNorm

/-- Normalized band bounds imply the slice mean square through the explicit
window, with no bump-family constant among the hypotheses. -/
theorem slice_meanSquare_typicalS_le_of_explicit_normalized_bands
    (levels : List (Finset ℕ)) (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A s U H : ℕ) (hA : 1 ≤ A) (hs : 1 ≤ s) (hsA : s ≤ A)
    (hU : 0 < U) (hUH : 2 * U ≤ H) (h3H : 3 * H ≤ A)
    (hplat : ((U : ℝ) + 1) * ((A : ℝ) + s) ≤ (A : ℝ) * H)
    (hDeltaA : s + 2 * H + 4 * U ≤ A) (hs30 : 30 * s ≤ A)
    (epsGeom : ℝ) (hepsGeom : 0 < epsGeom) (hepsGeom1 : epsGeom ≤ 1)
    (hU100 : epsGeom * (H : ℝ) ≤ 100 * U)
    (hU50 : 50 * (U : ℝ) ≤ epsGeom * H)
    (K K2 L : ℝ) (hKK2 : K ≤ K2) (hK2 : 0 < K2) (hK2L : K2 ≤ L)
    (Jband : ℕ) (hJband : L < 2 ^ Jband * K2)
    (ElowNorm EinnerNorm : ℝ)
    (hlow : (∫ xi in {xi : ℝ | |xi| < K},
      ‖∑ m ∈ typicalS A (A + s + 2 * H + 4 * U) levels,
          (g m / (m : ℂ)) *
            ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
        ≤ ElowNorm)
    (hinner : ∀ w : ℝ → ℝ, Measurable w → (∀ xi, 0 ≤ w xi) →
      (∀ xi, w xi ≤ (4 * (H : ℝ) / A) ^ 2) →
      (∫ xi in {xi : ℝ | K ≤ |xi| ∧ |xi| ≤ K2},
        ‖∑ m ∈ typicalS A (A + s + 2 * H + 4 * U) levels,
            (g m / (m : ℂ)) *
              ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2 * w xi)
          ≤ EinnerNorm)
    (Etarget : ℝ)
    (haccount : sliceA2ExplicitWindowCost A s U H epsGeom K2 L
      ElowNorm EinnerNorm ≤ Etarget) :
    ∑ n ∈ Finset.Ioc A (A + s),
        ‖∑ m ∈ (Finset.Ioc n (n + H)).filter (HasFactorInAll levels),
          g m‖ ^ 2 / n ≤ Etarget := by
  classical
  have hApos : 0 < A := lt_of_lt_of_le Nat.zero_lt_one hA
  have htot : ∀ xi : ℝ,
      ‖∑ m ∈ Finset.Ioc A (A + s + 2 * H + 4 * U),
        sliceWeightedTypicalCoeff A levels g m *
          ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖
        ≤ ((s + 2 * H + 4 * U : ℕ) : ℝ) := by
    intro xi
    have hlen := norm_sum_sliceWeightedTypicalCoeff_le_length
      A (s + 2 * H + 4 * U) hApos levels g hg xi
    simpa only [show A + (s + 2 * H + 4 * U) =
      A + s + 2 * H + 4 * U by omega] using hlen
  have hlow' : (∫ xi in {xi : ℝ | |xi| < K},
      ‖∑ m ∈ Finset.Ioc A (A + s + 2 * H + 4 * U),
        sliceWeightedTypicalCoeff A levels g m *
          ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
      ≤ (A : ℝ) ^ 2 * ElowNorm := by
    rw [integral_norm_sq_sliceWeightedTypicalCoeff_eq A
      (A + s + 2 * H + 4 * U) levels g
      {xi : ℝ | |xi| < K}
      (measurableSet_lt measurable_abs measurable_const)]
    exact mul_le_mul_of_nonneg_left hlow (sq_nonneg (A : ℝ))
  have hinner' : ∀ w : ℝ → ℝ, Measurable w → (∀ xi, 0 ≤ w xi) →
      (∀ xi, w xi ≤ (4 * (H : ℝ) / A) ^ 2) →
      (∫ xi in {xi : ℝ | K ≤ |xi| ∧ |xi| ≤ K2},
        ‖∑ m ∈ Finset.Ioc A (A + s + 2 * H + 4 * U),
          sliceWeightedTypicalCoeff A levels g m *
            ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2 * w xi)
        ≤ (A : ℝ) ^ 2 * EinnerNorm := by
    intro w hwm hw0 hwsup
    rw [integral_norm_sq_sliceWeightedTypicalCoeff_mul_eq A
      (A + s + 2 * H + 4 * U) levels g w
      {xi : ℝ | K ≤ |xi| ∧ |xi| ≤ K2}
      (measurableSet_inner_band K K2)]
    exact mul_le_mul_of_nonneg_left
      (hinner w hwm hw0 hwsup) (sq_nonneg (A : ℝ))
  have hbands := slice_energy_le_of_explicit_bands
    (sliceWeightedTypicalCoeff A levels g)
    (norm_sliceWeightedTypicalCoeff_le_one A hApos levels g hg)
    A s U H hA hs hsA hU hUH h3H hplat hDeltaA hs30
    epsGeom hepsGeom hepsGeom1 hU100 hU50 K K2 L
    ((s + 2 * H + 4 * U : ℕ) : ℝ) hKK2 hK2 hK2L
    Jband hJband htot ((A : ℝ) ^ 2 * ElowNorm)
    ((A : ℝ) ^ 2 * EinnerNorm) hlow' hinner'
  have hbands' :
      ∑ n ∈ Finset.Ioc A (A + s),
        ‖∑ m ∈ Finset.Ioc n (n + H),
          sliceWeightedTypicalCoeff A levels g m‖ ^ 2 / n
        ≤ sliceA2BandCost A s U H (explicitSliceWindowDerivBound epsGeom)
          K2 L ElowNorm EinnerNorm := by
    simpa only [sliceA2BandCost, Nat.cast_add, Nat.cast_mul] using hbands
  have hweighted :
      (∑ n ∈ Finset.Ioc A (A + s),
        ‖∑ m ∈ Finset.Ioc n (n + H),
          sliceTypicalCoeff levels g m * ((A : ℂ) / (m : ℂ))‖ ^ 2 / n) =
      ∑ n ∈ Finset.Ioc A (A + s),
        ‖∑ m ∈ Finset.Ioc n (n + H),
          sliceWeightedTypicalCoeff A levels g m‖ ^ 2 / n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [sum_sliceWeightedTypicalCoeff_short_eq A n H levels g
      (Finset.mem_Ioc.mp hn).1]
  have hconvert := slice_energy_le_scaled_weighted_energy
    (sliceTypicalCoeff levels g)
    (norm_sliceTypicalCoeff_le_one levels g hg) A s H hApos
  have hconvert' :
      ∑ n ∈ Finset.Ioc A (A + s),
        ‖∑ m ∈ Finset.Ioc n (n + H), sliceTypicalCoeff levels g m‖ ^ 2 / n
        ≤ sliceA2ExplicitWindowCost A s U H epsGeom K2 L
          ElowNorm EinnerNorm := by
    rw [hweighted] at hconvert
    have hfactor : 0 ≤ 2 * (((A + s : ℕ) : ℝ) / (A : ℝ)) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    calc
      ∑ n ∈ Finset.Ioc A (A + s),
          ‖∑ m ∈ Finset.Ioc n (n + H), sliceTypicalCoeff levels g m‖ ^ 2 / n
          ≤ 2 * (((A + s : ℕ) : ℝ) / A) ^ 2 *
              (∑ n ∈ Finset.Ioc A (A + s),
                ‖∑ m ∈ Finset.Ioc n (n + H),
                  sliceWeightedTypicalCoeff A levels g m‖ ^ 2 / n) +
              2 * (H : ℝ) ^ 4 * s / (A : ℝ) ^ 3 := hconvert
      _ ≤ 2 * (((A + s : ℕ) : ℝ) / A) ^ 2 *
              sliceA2BandCost A s U H (explicitSliceWindowDerivBound epsGeom)
                K2 L ElowNorm EinnerNorm +
              2 * (H : ℝ) ^ 4 * s / (A : ℝ) ^ 3 :=
            add_le_add (mul_le_mul_of_nonneg_left hbands' hfactor) le_rfl
      _ = sliceA2ExplicitWindowCost A s U H epsGeom K2 L
          ElowNorm EinnerNorm := rfl
  calc
    ∑ n ∈ Finset.Ioc A (A + s),
        ‖∑ m ∈ (Finset.Ioc n (n + H)).filter (HasFactorInAll levels),
          g m‖ ^ 2 / n
        = ∑ n ∈ Finset.Ioc A (A + s),
            ‖∑ m ∈ Finset.Ioc n (n + H),
              sliceTypicalCoeff levels g m‖ ^ 2 / n := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [sum_sliceTypicalCoeff_eq_filter]
    _ ≤ sliceA2ExplicitWindowCost A s U H epsGeom K2 L
        ElowNorm EinnerNorm := hconvert'
    _ ≤ Etarget := haccount

end Tao2015

end MoltResearch
