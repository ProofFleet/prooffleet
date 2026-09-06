import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2WindowNumerology

/-!
# Track R A2-V': explicit-window error margins

This leaf turns simple scale inequalities into the collar, Lipschitz, tail,
and weight-conversion allocations of the fixed budget ledger.
-/

namespace MoltResearch

namespace Tao2015

open Finset ExpSums

/-- Harmonic mass of an interval is at most its length divided by the left
endpoint. -/
theorem sliceA2_harmonic_upper (A R : ℕ) (hA : 1 ≤ A) :
    ∑ n ∈ Finset.Ioc A (A + R), (1 : ℝ) / n ≤ (R : ℝ) / A := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  calc
    ∑ n ∈ Finset.Ioc A (A + R), (1 : ℝ) / n ≤
        ∑ _n ∈ Finset.Ioc A (A + R), (1 : ℝ) / A := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by
        exact_mod_cast (lt_trans (by omega : 0 < A) (Finset.mem_Ioc.mp hn).1)
      apply one_div_le_one_div_of_le hAR
      exact_mod_cast (Finset.mem_Ioc.mp hn).1.le
    _ = (R : ℝ) / A := by
      rw [Finset.sum_const, Nat.card_Ioc, Nat.add_sub_cancel_left,
        nsmul_eq_mul]
      ring

/-- The collar allocation follows once `U`, the relative slice width, and
the additive rounding constant each cost at most one thousandth of
`eps*H`. -/
theorem sliceA2_collar_slot_fit
    (A s U H : ℕ) (eps : ℝ) (hA : 0 < A) (heps : 0 < eps)
    (hH : 0 < H)
    (hU : (U : ℝ) ≤ eps * H / 1000)
    (hs : (H : ℝ) * s / A ≤ eps * H / 1000)
    (hround : (2 : ℝ) ≤ eps * H / 1000) :
    (3 * (U : ℝ) ^ 2 +
        3 * (6 * (U : ℝ) + (H : ℝ) * s / A + 2) ^ 2) *
        (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) ≤
      eps ^ 2 * (H : ℝ) ^ 2 *
        (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) / 128 := by
  let x : ℝ := eps * H
  have hx : 0 < x := by dsimp [x]; positivity
  have hU0 : (0 : ℝ) ≤ U := by positivity
  have hsum0 : 0 ≤ 6 * (U : ℝ) + (H : ℝ) * s / A + 2 := by
    have hAR : (0 : ℝ) < A := by exact_mod_cast hA
    positivity
  have hsum : 6 * (U : ℝ) + (H : ℝ) * s / A + 2 ≤ x / 125 := by
    dsimp only [x]
    linarith
  have hcoef : 3 * (U : ℝ) ^ 2 +
      3 * (6 * (U : ℝ) + (H : ℝ) * s / A + 2) ^ 2 ≤
        eps ^ 2 * (H : ℝ) ^ 2 / 128 := by
    have hU2 := pow_le_pow_left₀ hU0 hU 2
    have hsum2 := pow_le_pow_left₀ hsum0 hsum 2
    dsimp only [x] at hsum2
    have hx2 : (eps * (H : ℝ)) ^ 2 = eps ^ 2 * (H : ℝ) ^ 2 := by ring
    nlinarith [sq_nonneg (eps * (H : ℝ))]
  have hW0 : 0 ≤ ∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n :=
    Finset.sum_nonneg fun n _ => by positivity
  calc
    (3 * (U : ℝ) ^ 2 +
        3 * (6 * (U : ℝ) + (H : ℝ) * s / A + 2) ^ 2) *
        (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) ≤
      (eps ^ 2 * (H : ℝ) ^ 2 / 128) *
        (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) := by gcongr
    _ = _ := by ring

/-- The explicit Lipschitz error fits once `H` clears its polynomial
threshold. -/
theorem sliceA2_lipschitz_slot_fit
    (A s H M : ℕ) (eps epsGeom : ℝ)
    (hA : 0 < A) (hH : 0 < H) (hM : 0 < M)
    (hmass : (1 : ℝ) / (5 * M) ≤
      ∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n)
    (hfit : 3072000 * (M : ℝ) * explicitSliceWindowDerivBound epsGeom ≤
      eps ^ 2 * H) :
    6 * (800 * (H : ℝ) * (A : ℝ) *
        explicitSliceWindowDerivBound epsGeom) / A ≤
      eps ^ 2 * (H : ℝ) ^ 2 *
        (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) / 128 := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hcoef : 0 ≤ eps ^ 2 * (H : ℝ) ^ 2 / 128 := by positivity
  have hraw : 4800 * (H : ℝ) * explicitSliceWindowDerivBound epsGeom ≤
      eps ^ 2 * (H : ℝ) ^ 2 / (640 * M) := by
    have hmul : ((H : ℝ) / (640 * M)) *
          (3072000 * (M : ℝ) * explicitSliceWindowDerivBound epsGeom) ≤
        ((H : ℝ) / (640 * M)) * (eps ^ 2 * H) :=
      mul_le_mul_of_nonneg_left hfit (by positivity)
    calc
      4800 * (H : ℝ) * explicitSliceWindowDerivBound epsGeom =
          (3072000 * (M : ℝ) * explicitSliceWindowDerivBound epsGeom) *
            ((H : ℝ) / (640 * M)) := by field_simp; ring
      _ ≤ (eps ^ 2 * H) * ((H : ℝ) / (640 * M)) := by
        simpa [mul_comm] using hmul
      _ = eps ^ 2 * (H : ℝ) ^ 2 / (640 * M) := by field_simp
  calc
    6 * (800 * (H : ℝ) * (A : ℝ) *
        explicitSliceWindowDerivBound epsGeom) / A =
        4800 * (H : ℝ) * explicitSliceWindowDerivBound epsGeom := by
      field_simp
      ring
    _ ≤ eps ^ 2 * (H : ℝ) ^ 2 / (640 * M) := hraw
    _ = (eps ^ 2 * (H : ℝ) ^ 2 / 128) * ((1 : ℝ) / (5 * M)) := by
      field_simp
      ring
    _ ≤ (eps ^ 2 * (H : ℝ) ^ 2 / 128) *
        (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) := by gcongr
    _ = _ := by ring

/-- A quadratic separation between the slice scale and `H/eps` absorbs the
error from removing the coefficient `A/m`. -/
theorem sliceA2_conversion_slot_fit
    (A s H : ℕ) (eps : ℝ) (hA : 0 < A) (hsA : s ≤ A)
    (hscale : 32 * (H : ℝ) ^ 2 ≤ eps ^ 2 * (A : ℝ) ^ 2) :
    2 * (H : ℝ) ^ 4 * s / (A : ℝ) ^ 3 ≤
      eps ^ 2 * (H : ℝ) ^ 2 *
        (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) / 8 := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hmass0 : (s : ℝ) / (2 * A) ≤
      ∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n := by
    have hlower := sliceA2_harmonic_lower A s (by omega)
    have hAs : (0 : ℝ) < ((A + s : ℕ) : ℝ) := by positivity
    have h2A : (A + s : ℕ) ≤ 2 * A := by omega
    have hratio : (s : ℝ) / (2 * A) ≤ (s : ℝ) / (A + s : ℕ) := by
      apply div_le_div_of_nonneg_left (by positivity) hAs
      exact_mod_cast h2A
    exact hratio.trans hlower
  have hraw : 2 * (H : ℝ) ^ 4 * s / (A : ℝ) ^ 3 ≤
      eps ^ 2 * (H : ℝ) ^ 2 * ((s : ℝ) / (2 * A)) / 8 := by
    have hmul : (32 * (H : ℝ) ^ 2) *
          ((H : ℝ) ^ 2 * s / (16 * (A : ℝ) ^ 3)) ≤
        (eps ^ 2 * (A : ℝ) ^ 2) *
          ((H : ℝ) ^ 2 * s / (16 * (A : ℝ) ^ 3)) :=
      mul_le_mul_of_nonneg_right hscale (by positivity)
    calc
      2 * (H : ℝ) ^ 4 * s / (A : ℝ) ^ 3 =
          (32 * (H : ℝ) ^ 2) *
            ((H : ℝ) ^ 2 * s / (16 * (A : ℝ) ^ 3)) := by ring
      _ ≤ (eps ^ 2 * (A : ℝ) ^ 2) *
          ((H : ℝ) ^ 2 * s / (16 * (A : ℝ) ^ 3)) := hmul
      _ = eps ^ 2 * (H : ℝ) ^ 2 * ((s : ℝ) / (2 * A)) / 8 := by
        field_simp
        ring
  calc
    _ ≤ eps ^ 2 * (H : ℝ) ^ 2 * ((s : ℝ) / (2 * A)) / 8 := hraw
    _ ≤ eps ^ 2 * (H : ℝ) ^ 2 *
        (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) / 8 := by gcongr

/-- The Fourier tail fits under one cross-multiplied polynomial condition.
This form is convenient when `L=A²`. -/
theorem sliceA2_tail_slot_fit
    (A s U H M : ℕ) (eps epsGeom L : ℝ)
    (hA : 0 < A) (hH : 0 < H) (hM : 0 < M)
    (hL : 0 < L)
    (hmass : (1 : ℝ) / (5 * M) ≤
      ∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n)
    (hfit : 3840 * (M : ℝ) * (s + 2 * H + 4 * U : ℕ) ^ 2 *
        (A : ℝ) * explicitSliceWindowDerivBound epsGeom ^ 2 ≤
      eps ^ 2 * (H : ℝ) ^ 3 * Real.pi ^ 2 * L ^ 2) :
    (s + 2 * H + 4 * U : ℕ) ^ 2 *
        ((1 / L ^ 2) * ((A : ℝ) / H *
          explicitSliceWindowDerivBound epsGeom ^ 2 / Real.pi ^ 2)) ≤
      eps ^ 2 * (H : ℝ) ^ 2 *
        (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) / 768 := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcross :
      (s + 2 * H + 4 * U : ℕ) ^ 2 *
          ((1 / L ^ 2) * ((A : ℝ) / H *
            explicitSliceWindowDerivBound epsGeom ^ 2 / Real.pi ^ 2)) ≤
        eps ^ 2 * (H : ℝ) ^ 2 / (3840 * M) := by
    rw [show (s + 2 * H + 4 * U : ℕ) ^ 2 *
        ((1 / L ^ 2) * ((A : ℝ) / H *
          explicitSliceWindowDerivBound epsGeom ^ 2 / Real.pi ^ 2)) =
      ((s + 2 * H + 4 * U : ℕ) ^ 2 * (A : ℝ) *
        explicitSliceWindowDerivBound epsGeom ^ 2) /
          ((H : ℝ) * Real.pi ^ 2 * L ^ 2) by field_simp]
    apply (div_le_div_iff₀
      (show (0 : ℝ) < (H : ℝ) * Real.pi ^ 2 * L ^ 2 by positivity)
      (show (0 : ℝ) < 3840 * M by positivity)).2
    convert hfit using 1 <;> ring
  calc
    _ ≤ eps ^ 2 * (H : ℝ) ^ 2 / (3840 * M) := hcross
    _ = (eps ^ 2 * (H : ℝ) ^ 2 / 768) * ((1 : ℝ) / (5 * M)) := by
      field_simp
      ring
    _ ≤ (eps ^ 2 * (H : ℝ) ^ 2 / 768) *
        (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) := by gcongr
    _ = _ := by ring

end Tao2015

end MoltResearch
