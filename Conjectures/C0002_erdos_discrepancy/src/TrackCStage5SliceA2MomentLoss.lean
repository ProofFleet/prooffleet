import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2MomentNumerology

/-!
# Track R A2-V': a coarse exceptional moment loss

All logarithmic factors in the exceptional high moment can be placed under
one nonnegative envelope `Z`.  The complete loss is then at most
`220 (M+1) (Z+1)`, where `M` bounds the adaptive order.  This deliberately
loose constant makes the final scalar comparison transparent.
-/

namespace MoltResearch

namespace Tao2015

/-- A common envelope for the four logarithms in the exceptional moment
controls its complete additive logarithmic loss. -/
theorem sliceA2ExceptionalMoment_logLoss_le
    (A P ell : ℕ) (T M Z : ℝ)
    (hell : (ell : ℝ) ≤ M) (hZ : 0 ≤ Z)
    (hlogell : Real.log (ell : ℝ) ≤ Z)
    (hlogP : Real.log (Real.log (2 * (P : ℝ))) ≤ Z)
    (hlogA : Real.log (Real.log (A : ℝ)) ≤ Z)
    (hlogT : Real.log (Real.log (2 * T)) ≤ Z) :
    Real.pi + ((ell : ℝ) + 2) * Real.log 2 +
          2 * (ell : ℝ) * Real.log (ell : ℝ) +
          2 * (Real.log 9 + Real.log (ell : ℝ) +
            Real.log (Real.log (2 * (P : ℝ)))) +
          200 * (ell : ℝ) * Real.log (Real.log (A : ℝ)) +
          2 * Real.log (Real.log (2 * T)) ≤
        220 * (M + 1) * (Z + 1) := by
  have hell0 : (0 : ℝ) ≤ ell := by positivity
  have hM : 0 ≤ M + 1 := by linarith
  have hZ1 : 0 ≤ Z + 1 := by linarith
  have hpi : Real.pi ≤ 4 := Real.pi_lt_four.le
  have hlog2 : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
  have hlog9 : Real.log 9 ≤ 3 := log_nine_le.trans (by norm_num)
  have hlinear :
      Real.pi + ((ell : ℝ) + 2) * Real.log 2 +
            2 * (ell : ℝ) * Real.log (ell : ℝ) +
            2 * (Real.log 9 + Real.log (ell : ℝ) +
              Real.log (Real.log (2 * (P : ℝ)))) +
            200 * (ell : ℝ) * Real.log (Real.log (A : ℝ)) +
            2 * Real.log (Real.log (2 * T)) ≤
          (ell : ℝ) + 12 + 202 * (ell : ℝ) * Z + 6 * Z := by
    have hmul2 := mul_le_mul_of_nonneg_left hlogell
      (by positivity : 0 ≤ 2 * (ell : ℝ))
    have hmul200 := mul_le_mul_of_nonneg_left hlogA
      (by positivity : 0 ≤ 200 * (ell : ℝ))
    have hmulLog2 := mul_le_mul_of_nonneg_left hlog2
      (by positivity : 0 ≤ (ell : ℝ) + 2)
    nlinarith
  calc
    _ ≤ (ell : ℝ) + 12 + 202 * (ell : ℝ) * Z + 6 * Z := hlinear
    _ ≤ 220 * ((ell : ℝ) + 1) * (Z + 1) := by
      nlinarith [mul_nonneg hell0 hZ]
    _ ≤ 220 * (M + 1) * (Z + 1) := by gcongr

/-- The preceding coarse loss closes the exact damping certificate as soon
as its scalar right-hand side dominates `220 (M+1) (Z+1)`. -/
theorem sliceA2ExceptionalMoment_logCertificate_of_bounds
    (A P ell : ℕ) (T M Z D : ℝ)
    (hell : (ell : ℝ) ≤ M) (hZ : 0 ≤ Z)
    (hlogell : Real.log (ell : ℝ) ≤ Z)
    (hlogP : Real.log (Real.log (2 * (P : ℝ))) ≤ Z)
    (hlogA : Real.log (Real.log (A : ℝ)) ≤ Z)
    (hlogT : Real.log (Real.log (2 * T)) ≤ Z)
    (hscalar : 220 * (M + 1) * (Z + 1) ≤ D) :
    Real.pi + ((ell : ℝ) + 2) * Real.log 2 +
          2 * (ell : ℝ) * Real.log (ell : ℝ) +
          2 * (Real.log 9 + Real.log (ell : ℝ) +
            Real.log (Real.log (2 * (P : ℝ)))) +
          200 * (ell : ℝ) * Real.log (Real.log (A : ℝ)) +
          2 * Real.log (Real.log (2 * T)) ≤ D :=
  (sliceA2ExceptionalMoment_logLoss_le A P ell T M Z hell hZ
    hlogell hlogP hlogA hlogT).trans hscalar

end Tao2015

end MoltResearch
