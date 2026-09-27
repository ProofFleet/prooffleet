import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5ExceptionalLadderData
import MoltResearch.Discrepancy.SliceWeightConversion

/-!
# Track R A2-IV-3': the slice mean-square window

This file performs the accounting step between the normalized Dirichlet
polynomial controlled by the low- and inner-band estimates and the
unnormalized short sums in `SliceMeanSquareA2`.

The coefficient passed to `slice_energy_le_of_bands` is
`1_S(m) g(m) A/m`, extended by zero below the left endpoint.  The extension
makes it globally `1`-bounded, while on every range used by the harness its
Fourier polynomial is exactly `A` times the normalized typical-set
polynomial.  Thus both supplied Fourier energies acquire exactly one factor
`A^2`; `slice_energy_le_scaled_weighted_energy` then removes the `A/m`
weight from the short sums.
-/

namespace MoltResearch

namespace Tao2015

open Real Finset MeasureTheory SchwartzMap ExpSums
open scoped FourierTransform ContDiff

/-- The `S`-restricted coefficient occurring in the conclusion of A.2. -/
noncomputable def sliceTypicalCoeff
    (levels : List (Finset ℕ)) (g : ℕ → ℂ) (m : ℕ) : ℂ :=
  if HasFactorInAll levels m then g m else 0

/-- The globally bounded `A/m` coefficient used by the Fourier harness. -/
noncomputable def sliceWeightedTypicalCoeff
    (A : ℕ) (levels : List (Finset ℕ)) (g : ℕ → ℂ) (m : ℕ) : ℂ :=
  if A < m then sliceTypicalCoeff levels g m * ((A : ℂ) / (m : ℂ)) else 0

theorem norm_sliceTypicalCoeff_le_one
    (levels : List (Finset ℕ)) (g : ℕ → ℂ)
    (hg : ∀ m, ‖g m‖ ≤ 1) (m : ℕ) :
    ‖sliceTypicalCoeff levels g m‖ ≤ 1 := by
  by_cases hm : HasFactorInAll levels m
  · simpa [sliceTypicalCoeff, hm] using hg m
  · simp [sliceTypicalCoeff, hm]

theorem norm_sliceWeightedTypicalCoeff_le_one
    (A : ℕ) (hA : 0 < A) (levels : List (Finset ℕ)) (g : ℕ → ℂ)
    (hg : ∀ m, ‖g m‖ ≤ 1) (m : ℕ) :
    ‖sliceWeightedTypicalCoeff A levels g m‖ ≤ 1 := by
  by_cases hAm : A < m
  · rw [sliceWeightedTypicalCoeff, if_pos hAm, norm_mul, norm_div,
      Complex.norm_natCast, Complex.norm_natCast]
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_trans hA hAm)
    have hAle : (A : ℝ) ≤ m := by exact_mod_cast hAm.le
    calc
      ‖sliceTypicalCoeff levels g m‖ * ((A : ℝ) / m)
          ≤ 1 * ((A : ℝ) / m) := by
            gcongr
            exact norm_sliceTypicalCoeff_le_one levels g hg m
      _ ≤ 1 := by
        rw [one_mul, div_le_one hm0]
        exact hAle
  · simp [sliceWeightedTypicalCoeff, hAm]

/-- On a range to the right of `A`, the weighted coefficient polynomial is
exactly `A` times the normalized typical-set polynomial. -/
theorem sum_sliceWeightedTypicalCoeff_eq_mul_typicalS
    (A B : ℕ) (levels : List (Finset ℕ)) (g : ℕ → ℂ) (xi : ℝ) :
    ∑ m ∈ Finset.Ioc A B,
        sliceWeightedTypicalCoeff A levels g m *
          ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)
      = (A : ℂ) *
          ∑ m ∈ typicalS A B levels, (g m / (m : ℂ)) *
            ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ) := by
  classical
  rw [typicalS, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hAm : A < m := (Finset.mem_Ioc.mp hm).1
  by_cases hSm : HasFactorInAll levels m
  · simp only [hSm, if_true, sliceWeightedTypicalCoeff, hAm,
      sliceTypicalCoeff]
    ring
  · simp [sliceWeightedTypicalCoeff, sliceTypicalCoeff, hAm, hSm]

/-- On every short interval based inside `(A,A+s]`, the globally bounded
harness coefficient agrees with the weight-conversion coefficient. -/
theorem sum_sliceWeightedTypicalCoeff_short_eq
    (A n H : ℕ) (levels : List (Finset ℕ)) (g : ℕ → ℂ)
    (hn : A < n) :
    ∑ m ∈ Finset.Ioc n (n + H), sliceWeightedTypicalCoeff A levels g m
      = ∑ m ∈ Finset.Ioc n (n + H),
          sliceTypicalCoeff levels g m * ((A : ℂ) / (m : ℂ)) := by
  apply Finset.sum_congr rfl
  intro m hm
  have hAm : A < m := lt_trans hn (Finset.mem_Ioc.mp hm).1
  simp [sliceWeightedTypicalCoeff, hAm]

/-- Filtering a short sum and inserting the indicator coefficient are the
same operation. -/
theorem sum_sliceTypicalCoeff_eq_filter
    (S : Finset ℕ) (levels : List (Finset ℕ)) (g : ℕ → ℂ) :
    ∑ m ∈ S, sliceTypicalCoeff levels g m
      = ∑ m ∈ S.filter (HasFactorInAll levels), g m := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hSm : HasFactorInAll levels m <;>
    simp [sliceTypicalCoeff, hSm]

/-- Squaring the polynomial identity produces exactly the real factor `A^2`. -/
theorem norm_sq_sum_sliceWeightedTypicalCoeff_eq
    (A B : ℕ) (levels : List (Finset ℕ)) (g : ℕ → ℂ) (xi : ℝ) :
    ‖∑ m ∈ Finset.Ioc A B,
        sliceWeightedTypicalCoeff A levels g m *
          ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2
      = (A : ℝ) ^ 2 *
          ‖∑ m ∈ typicalS A B levels, (g m / (m : ℂ)) *
            ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2 := by
  rw [sum_sliceWeightedTypicalCoeff_eq_mul_typicalS,
    norm_mul, Complex.norm_natCast, mul_pow]

/-- The same `A^2` identity after multiplication by an arbitrary real
weight. -/
theorem norm_sq_sum_sliceWeightedTypicalCoeff_mul_eq
    (A B : ℕ) (levels : List (Finset ℕ)) (g : ℕ → ℂ)
    (w : ℝ → ℝ) (xi : ℝ) :
    ‖∑ m ∈ Finset.Ioc A B,
        sliceWeightedTypicalCoeff A levels g m *
          ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2 * w xi
      = (A : ℝ) ^ 2 *
          (‖∑ m ∈ typicalS A B levels, (g m / (m : ℂ)) *
            ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2 * w xi) := by
  rw [norm_sq_sum_sliceWeightedTypicalCoeff_eq]
  ring

/-- The low-band set integral of the harness polynomial is `A^2` times its
normalized counterpart. -/
theorem integral_norm_sq_sliceWeightedTypicalCoeff_eq
    (A B : ℕ) (levels : List (Finset ℕ)) (g : ℕ → ℂ)
    (G : Set ℝ) (hG : MeasurableSet G) :
    (∫ xi in G, ‖∑ m ∈ Finset.Ioc A B,
        sliceWeightedTypicalCoeff A levels g m *
          ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
      = (A : ℝ) ^ 2 *
          ∫ xi in G, ‖∑ m ∈ typicalS A B levels, (g m / (m : ℂ)) *
            ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2 := by
  rw [setIntegral_congr_fun hG
    (fun xi _ => norm_sq_sum_sliceWeightedTypicalCoeff_eq A B levels g xi),
    integral_const_mul]

/-- The weighted inner-band integral has the identical `A^2` scaling. -/
theorem integral_norm_sq_sliceWeightedTypicalCoeff_mul_eq
    (A B : ℕ) (levels : List (Finset ℕ)) (g : ℕ → ℂ)
    (w : ℝ → ℝ) (G : Set ℝ) (hG : MeasurableSet G) :
    (∫ xi in G, ‖∑ m ∈ Finset.Ioc A B,
        sliceWeightedTypicalCoeff A levels g m *
          ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2 * w xi)
      = (A : ℝ) ^ 2 *
          ∫ xi in G, ‖∑ m ∈ typicalS A B levels, (g m / (m : ℂ)) *
            ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2 * w xi := by
  rw [setIntegral_congr_fun hG
    (fun xi _ => norm_sq_sum_sliceWeightedTypicalCoeff_mul_eq A B levels g w xi),
    integral_const_mul]

/-- The pointwise total-polynomial estimate needed by the slice harness. -/
theorem norm_sum_sliceWeightedTypicalCoeff_le_length
    (A R : ℕ) (hA : 0 < A) (levels : List (Finset ℕ)) (g : ℕ → ℂ)
    (hg : ∀ m, ‖g m‖ ≤ 1) (xi : ℝ) :
    ‖∑ m ∈ Finset.Ioc A (A + R),
        sliceWeightedTypicalCoeff A levels g m *
          ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ≤ R := by
  calc
    ‖∑ m ∈ Finset.Ioc A (A + R),
        sliceWeightedTypicalCoeff A levels g m *
          ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖
        ≤ ∑ m ∈ Finset.Ioc A (A + R),
            ‖sliceWeightedTypicalCoeff A levels g m *
              ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Ioc A (A + R), (1 : ℝ) := by
      refine Finset.sum_le_sum fun m hm => ?_
      rw [norm_mul, Circle.norm_coe]
      simpa using norm_sliceWeightedTypicalCoeff_le_one A hA levels g hg m
    _ = R := by
      rw [Finset.sum_const, Nat.card_Ioc, Nat.add_sub_cancel_left,
        nsmul_eq_mul, mul_one]

/-! ## Exact accounting -/

/-- The right-hand side produced by `slice_energy_le_of_bands` after the two
normalized Fourier inputs have been rescaled by `A^2`.  The total-polynomial
bound is the interval length `s + 2H + 4U`. -/
noncomputable def sliceA2BandCost
    (A s U H : ℕ) (B' K2 L ElowNorm EinnerNorm : ℝ) : ℝ :=
  6 * ((4 * (H : ℝ) / A) ^ 2 * ((A : ℝ) ^ 2 * ElowNorm) +
        (A : ℝ) ^ 2 * EinnerNorm +
        (4 * B' ^ 2 / Real.pi ^ 2) *
          ((2 * (A : ℝ) + 1) ^ 2 *
            (Real.exp Real.pi *
              ((4 / (K2 * (A : ℝ))) + (6 / K2 ^ 2)) *
              (∑ n ∈ Finset.Ioc A (A + s + 2 * H + 4 * U),
                (1 : ℝ) / n))) +
        (s + 2 * H + 4 * U : ℕ) ^ 2 *
          ((1 / L ^ 2) * ((A : ℝ) / H * B' ^ 2 / Real.pi ^ 2))) +
    (3 * (U : ℝ) ^ 2 +
        3 * (6 * (U : ℝ) + (H : ℝ) * s / A + 2) ^ 2) *
      (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) +
    6 * (800 * (H : ℝ) * (A : ℝ) * B') / A

/-- The final cost after removal of the `A/m` coefficient. -/
noncomputable def sliceA2WindowCost
    (A s U H : ℕ) (B' K2 L ElowNorm EinnerNorm : ℝ) : ℝ :=
  2 * (((A + s : ℕ) : ℝ) / A) ^ 2 *
      sliceA2BandCost A s U H B' K2 L ElowNorm EinnerNorm +
    2 * (H : ℝ) ^ 4 * s / (A : ℝ) ^ 3

/-- **A2-IV-3' — normalized band bounds imply the slice mean square.**

This theorem is the final parameter-free assembly step.  Its two analytic
inputs are exactly the normalized low-band and inner-band estimates.  Every
other term is displayed in `sliceA2WindowCost`; a later parameter theorem only
has to verify that this explicit expression fits the requested target. -/
theorem slice_meanSquare_typicalS_le_of_normalized_bands
    (levels : List (Finset ℕ)) (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A s U H : ℕ) (hA : 1 ≤ A) (hs : 1 ≤ s) (hsA : s ≤ A) (hU : 0 < U)
    (hUH : 2 * U ≤ H) (h3H : 3 * H ≤ A)
    (hplat : ((U : ℝ) + 1) * ((A : ℝ) + s) ≤ (A : ℝ) * H)
    (hDeltaA : s + 2 * H + 4 * U ≤ A)
    (C0 B' : ℝ) (hB'0 : 0 ≤ B')
    (hC0 : ∀ (c : ℝ) (f : ContDiffBump c),
      f.rIn = ((A : ℝ) / H) *
          (Real.log (1 + (H : ℝ) / ((A : ℝ) + s)) -
            Real.log (1 + (U : ℝ) / A)) / 2 →
      f.rOut - f.rIn = ((A : ℝ) / H) *
          (min (Real.log (1 + (U : ℝ) / A) -
                Real.log (1 + (U : ℝ) / (4 * ((A : ℝ) + s))))
            (Real.log (1 + ((H : ℝ) + 2 * U) / A) -
                Real.log (1 + (H : ℝ) / ((A : ℝ) + s)))) →
      ∀ u : ℝ, |deriv (⇑f) u| ≤ C0 / f.rIn)
    (hB' : C0 / (((A : ℝ) / H) *
        (Real.log (1 + (H : ℝ) / ((A : ℝ) + s)) -
          Real.log (1 + (U : ℝ) / A)) / 2) ≤ B')
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
    (haccount : sliceA2WindowCost A s U H B' K2 L ElowNorm EinnerNorm
      ≤ Etarget) :
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
  have hbands := slice_energy_le_of_bands
    (sliceWeightedTypicalCoeff A levels g)
    (norm_sliceWeightedTypicalCoeff_le_one A hApos levels g hg)
    A s U H hA hs hsA hU hUH h3H hplat hDeltaA
    C0 B' hB'0 hC0 hB' K K2 L
    ((s + 2 * H + 4 * U : ℕ) : ℝ) hKK2 hK2 hK2L
    Jband hJband htot ((A : ℝ) ^ 2 * ElowNorm)
    ((A : ℝ) ^ 2 * EinnerNorm) hlow' hinner'
  have hbands' :
      ∑ n ∈ Finset.Ioc A (A + s),
        ‖∑ m ∈ Finset.Ioc n (n + H),
          sliceWeightedTypicalCoeff A levels g m‖ ^ 2 / n
        ≤ sliceA2BandCost A s U H B' K2 L ElowNorm EinnerNorm := by
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
        ≤ sliceA2WindowCost A s U H B' K2 L ElowNorm EinnerNorm := by
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
              sliceA2BandCost A s U H B' K2 L ElowNorm EinnerNorm +
              2 * (H : ℝ) ^ 4 * s / (A : ℝ) ^ 3 :=
            add_le_add (mul_le_mul_of_nonneg_left hbands' hfactor) le_rfl
      _ = sliceA2WindowCost A s U H B' K2 L ElowNorm EinnerNorm := rfl
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
    _ ≤ sliceA2WindowCost A s U H B' K2 L ElowNorm EinnerNorm := hconvert'
    _ ≤ Etarget := haccount

end Tao2015

end MoltResearch
