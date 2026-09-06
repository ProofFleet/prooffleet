import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2WindowExplicit

/-!
# Track R A2-V': the explicit-window budget ledger

The four Fourier slots receive one half of the per-slice allowance, the
collar and Lipschitz errors one eighth each, and weight conversion the final
quarter.  The denominators below include the factor at most eight from
`2 * ((A+s)/A)^2`.
-/

namespace MoltResearch

namespace Tao2015

open Finset ExpSums

/-- Fixed-margin accounting for the explicit slice window. -/
theorem sliceA2ExplicitWindowCost_le_half_target
    (A s U H : ℕ) (eps epsGeom K2 L ElowNorm EinnerNorm : ℝ)
    (hA : 1 ≤ A) (hsA : s ≤ A) (hH : 0 < H)
    (hepsGeom : 0 < epsGeom)
    (hK2 : 0 < K2) (hL : 0 < L)
    (hElow0 : 0 ≤ ElowNorm) (hEinner0 : 0 ≤ EinnerNorm)
    (hlow : (4 * (H : ℝ) / A) ^ 2 * ((A : ℝ) ^ 2 * ElowNorm) ≤
      eps ^ 2 * (H : ℝ) ^ 2 *
        (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) / 768)
    (hinner : (A : ℝ) ^ 2 * EinnerNorm ≤
      eps ^ 2 * (H : ℝ) ^ 2 *
        (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) / 768)
    (houter :
      (4 * explicitSliceWindowDerivBound epsGeom ^ 2 / Real.pi ^ 2) *
          ((2 * (A : ℝ) + 1) ^ 2 *
            (Real.exp Real.pi * ((4 / (K2 * (A : ℝ))) + (6 / K2 ^ 2)) *
              (∑ n ∈ Finset.Ioc A (A + s + 2 * H + 4 * U),
                (1 : ℝ) / n))) ≤
        eps ^ 2 * (H : ℝ) ^ 2 *
          (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) / 768)
    (htail :
      (s + 2 * H + 4 * U : ℕ) ^ 2 *
          ((1 / L ^ 2) * ((A : ℝ) / H *
            explicitSliceWindowDerivBound epsGeom ^ 2 / Real.pi ^ 2)) ≤
        eps ^ 2 * (H : ℝ) ^ 2 *
          (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) / 768)
    (hcollar :
      (3 * (U : ℝ) ^ 2 +
          3 * (6 * (U : ℝ) + (H : ℝ) * s / A + 2) ^ 2) *
          (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) ≤
        eps ^ 2 * (H : ℝ) ^ 2 *
          (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) / 128)
    (hLipschitz :
      6 * (800 * (H : ℝ) * (A : ℝ) *
          explicitSliceWindowDerivBound epsGeom) / A ≤
        eps ^ 2 * (H : ℝ) ^ 2 *
          (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) / 128)
    (hconversion :
      2 * (H : ℝ) ^ 4 * s / (A : ℝ) ^ 3 ≤
        eps ^ 2 * (H : ℝ) ^ 2 *
          (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) / 8) :
    sliceA2ExplicitWindowCost A s U H epsGeom K2 L ElowNorm EinnerNorm ≤
      (eps ^ 2 / 2) * (H : ℝ) ^ 2 *
        ∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hratio : (((A + s : ℕ) : ℝ) / A) ≤ 2 := by
    rw [div_le_iff₀ hA0]
    norm_num
    exact_mod_cast (by omega : A + s ≤ 2 * A)
  have hratio0 : 0 ≤ (((A + s : ℕ) : ℝ) / A) := by positivity
  have hfactor : 2 * (((A + s : ℕ) : ℝ) / A) ^ 2 ≤ 8 := by
    nlinarith [sq_nonneg (2 - (((A + s : ℕ) : ℝ) / A))]
  have hW0 : 0 ≤ ∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n :=
    Finset.sum_nonneg fun n _ => by positivity
  have hB0 : 0 ≤ explicitSliceWindowDerivBound epsGeom := by
    unfold explicitSliceWindowDerivBound
    positivity [one_le_explicitSliceWindowConstant]
  have hlow0 : 0 ≤
      (4 * (H : ℝ) / A) ^ 2 * ((A : ℝ) ^ 2 * ElowNorm) := by
    positivity
  have hinner0 : 0 ≤ (A : ℝ) ^ 2 * EinnerNorm := by positivity
  have houter0 : 0 ≤
      (4 * explicitSliceWindowDerivBound epsGeom ^ 2 / Real.pi ^ 2) *
          ((2 * (A : ℝ) + 1) ^ 2 *
            (Real.exp Real.pi * ((4 / (K2 * (A : ℝ))) + (6 / K2 ^ 2)) *
              (∑ n ∈ Finset.Ioc A (A + s + 2 * H + 4 * U),
                (1 : ℝ) / n))) := by positivity
  have htail0 : 0 ≤
      (s + 2 * H + 4 * U : ℕ) ^ 2 *
          ((1 / L ^ 2) * ((A : ℝ) / H *
            explicitSliceWindowDerivBound epsGeom ^ 2 / Real.pi ^ 2)) := by
    positivity
  have hcollar0 : 0 ≤
      (3 * (U : ℝ) ^ 2 +
          3 * (6 * (U : ℝ) + (H : ℝ) * s / A + 2) ^ 2) *
          (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) := by
    positivity
  have hLip0 : 0 ≤
      6 * (800 * (H : ℝ) * (A : ℝ) *
          explicitSliceWindowDerivBound epsGeom) / A := by positivity
  let X : ℝ := eps ^ 2 * (H : ℝ) ^ 2 *
    ∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n
  have hband :
      6 * ((4 * (H : ℝ) / A) ^ 2 * ((A : ℝ) ^ 2 * ElowNorm) +
        (A : ℝ) ^ 2 * EinnerNorm +
        (4 * explicitSliceWindowDerivBound epsGeom ^ 2 / Real.pi ^ 2) *
          ((2 * (A : ℝ) + 1) ^ 2 *
            (Real.exp Real.pi * ((4 / (K2 * (A : ℝ))) + (6 / K2 ^ 2)) *
              (∑ n ∈ Finset.Ioc A (A + s + 2 * H + 4 * U),
                (1 : ℝ) / n))) +
        (s + 2 * H + 4 * U : ℕ) ^ 2 *
          ((1 / L ^ 2) * ((A : ℝ) / H *
            explicitSliceWindowDerivBound epsGeom ^ 2 / Real.pi ^ 2))) ≤ X / 32 := by
    dsimp only [X]
    linarith
  have hband0 : 0 ≤
      6 * ((4 * (H : ℝ) / A) ^ 2 * ((A : ℝ) ^ 2 * ElowNorm) +
        (A : ℝ) ^ 2 * EinnerNorm +
        (4 * explicitSliceWindowDerivBound epsGeom ^ 2 / Real.pi ^ 2) *
          ((2 * (A : ℝ) + 1) ^ 2 *
            (Real.exp Real.pi * ((4 / (K2 * (A : ℝ))) + (6 / K2 ^ 2)) *
              (∑ n ∈ Finset.Ioc A (A + s + 2 * H + 4 * U),
                (1 : ℝ) / n))) +
        (s + 2 * H + 4 * U : ℕ) ^ 2 *
          ((1 / L ^ 2) * ((A : ℝ) / H *
            explicitSliceWindowDerivBound epsGeom ^ 2 / Real.pi ^ 2))) := by
    positivity
  have hscaled :
      2 * (((A + s : ℕ) : ℝ) / A) ^ 2 *
          sliceA2BandCost A s U H (explicitSliceWindowDerivBound epsGeom)
            K2 L ElowNorm EinnerNorm ≤ 3 * X / 8 := by
    unfold sliceA2BandCost
    have hinside :
        6 * ((4 * (H : ℝ) / A) ^ 2 * ((A : ℝ) ^ 2 * ElowNorm) +
          (A : ℝ) ^ 2 * EinnerNorm +
          (4 * explicitSliceWindowDerivBound epsGeom ^ 2 / Real.pi ^ 2) *
            ((2 * (A : ℝ) + 1) ^ 2 *
              (Real.exp Real.pi * ((4 / (K2 * (A : ℝ))) + (6 / K2 ^ 2)) *
                (∑ n ∈ Finset.Ioc A (A + s + 2 * H + 4 * U),
                  (1 : ℝ) / n))) +
          (s + 2 * H + 4 * U : ℕ) ^ 2 *
            ((1 / L ^ 2) * ((A : ℝ) / H *
              explicitSliceWindowDerivBound epsGeom ^ 2 / Real.pi ^ 2))) +
        (3 * (U : ℝ) ^ 2 +
          3 * (6 * (U : ℝ) + (H : ℝ) * s / A + 2) ^ 2) *
          (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) +
        6 * (800 * (H : ℝ) * (A : ℝ) *
          explicitSliceWindowDerivBound epsGeom) / A ≤ 3 * X / 64 := by
      dsimp only [X]
      linarith
    have hinside0 : 0 ≤
        6 * ((4 * (H : ℝ) / A) ^ 2 * ((A : ℝ) ^ 2 * ElowNorm) +
          (A : ℝ) ^ 2 * EinnerNorm +
          (4 * explicitSliceWindowDerivBound epsGeom ^ 2 / Real.pi ^ 2) *
            ((2 * (A : ℝ) + 1) ^ 2 *
              (Real.exp Real.pi * ((4 / (K2 * (A : ℝ))) + (6 / K2 ^ 2)) *
                (∑ n ∈ Finset.Ioc A (A + s + 2 * H + 4 * U),
                  (1 : ℝ) / n))) +
          (s + 2 * H + 4 * U : ℕ) ^ 2 *
            ((1 / L ^ 2) * ((A : ℝ) / H *
              explicitSliceWindowDerivBound epsGeom ^ 2 / Real.pi ^ 2))) +
        (3 * (U : ℝ) ^ 2 +
          3 * (6 * (U : ℝ) + (H : ℝ) * s / A + 2) ^ 2) *
          (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) +
        6 * (800 * (H : ℝ) * (A : ℝ) *
          explicitSliceWindowDerivBound epsGeom) / A := by positivity
    calc
      2 * (((A + s : ℕ) : ℝ) / A) ^ 2 *
          (6 * ((4 * (H : ℝ) / A) ^ 2 * ((A : ℝ) ^ 2 * ElowNorm) +
            (A : ℝ) ^ 2 * EinnerNorm +
            (4 * explicitSliceWindowDerivBound epsGeom ^ 2 / Real.pi ^ 2) *
              ((2 * (A : ℝ) + 1) ^ 2 *
                (Real.exp Real.pi * ((4 / (K2 * (A : ℝ))) + (6 / K2 ^ 2)) *
                  (∑ n ∈ Finset.Ioc A (A + s + 2 * H + 4 * U),
                    (1 : ℝ) / n))) +
            (s + 2 * H + 4 * U : ℕ) ^ 2 *
              ((1 / L ^ 2) * ((A : ℝ) / H *
                explicitSliceWindowDerivBound epsGeom ^ 2 / Real.pi ^ 2))) +
          (3 * (U : ℝ) ^ 2 +
            3 * (6 * (U : ℝ) + (H : ℝ) * s / A + 2) ^ 2) *
            (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) +
          6 * (800 * (H : ℝ) * (A : ℝ) *
            explicitSliceWindowDerivBound epsGeom) / A)
          ≤ 8 * (3 * X / 64) := by
            exact mul_le_mul hfactor hinside hinside0 (by positivity)
      _ = 3 * X / 8 := by ring
  unfold sliceA2ExplicitWindowCost sliceA2WindowCost
  dsimp only [X] at hscaled ⊢
  linarith

end Tao2015

end MoltResearch
