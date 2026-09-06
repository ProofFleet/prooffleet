import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2Accounting
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2Geometry

/-!
# Track R A2-V': harmonic and inner-band window numerology

These estimates compare the enlarged Fourier interval with the harmonic mass
of the original short slice.  The factor four is deliberately crude and
absorbs all natural-number rounding.
-/

namespace MoltResearch

namespace Tao2015

open Finset ExpSums

/-- A short interval contains `s` terms, each at least `1/(X+s)`. -/
theorem sliceA2_harmonic_lower (X s : ℕ) (hX : 1 ≤ X) :
    (s : ℝ) / (X + s : ℕ) ≤
      ∑ n ∈ Finset.Ioc X (X + s), (1 : ℝ) / n := by
  have hden : (0 : ℝ) < (X + s : ℕ) := by positivity
  calc
    (s : ℝ) / (X + s : ℕ) =
        ∑ _n ∈ Finset.Ioc X (X + s), (1 : ℝ) / (X + s : ℕ) := by
      rw [Finset.sum_const, Nat.card_Ioc, Nat.add_sub_cancel_left,
        nsmul_eq_mul]
      ring
    _ ≤ ∑ n ∈ Finset.Ioc X (X + s), (1 : ℝ) / n := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by
        exact_mod_cast (lt_of_lt_of_le (by omega : 0 < X) (Finset.mem_Ioc.mp hn).1.le)
      apply one_div_le_one_div_of_le hn0
      exact_mod_cast (Finset.mem_Ioc.mp hn).2

/-- A floor slice `s=A/M`, started anywhere in `[A,2A]`, has harmonic mass
at least `1/(5M)`. -/
theorem sliceA2_floor_harmonic_lower
    (A X M : ℕ) (hM : 0 < M) (hMA : M ≤ A)
    (hAX : A ≤ X) (hX2A : X ≤ 2 * A) :
    (1 : ℝ) / (5 * M) ≤
      ∑ n ∈ Finset.Ioc X (X + A / M), (1 : ℝ) / n := by
  let s := A / M
  have hs : 1 ≤ s := by
    dsimp [s]
    exact (Nat.one_le_div_iff hM).mpr hMA
  have hA2Ms : A ≤ 2 * M * s := by
    have hdecomp : A = M * s + A % M := by
      dsimp [s]
      exact (Nat.div_add_mod A M).symm
    have hmod : A % M < M := Nat.mod_lt A hM
    have hsM : M ≤ M * s := by
      simpa only [mul_one] using Nat.mul_le_mul_left M hs
    calc
      A = M * s + A % M := hdecomp
      _ ≤ M * s + M := Nat.add_le_add_left hmod.le _
      _ ≤ M * s + M * s := Nat.add_le_add_left hsM _
      _ = 2 * M * s := by ring
  have htop : X + s ≤ 5 * M * s := by
    have hM1 : 1 ≤ M := hM
    have htwice : 2 * A ≤ 4 * M * s := by
      have hraw := Nat.mul_le_mul_left 2 hA2Ms
      nlinarith
    have hsMs : s ≤ M * s := by
      have hraw := Nat.mul_le_mul_right s hM1
      simpa only [one_mul] using hraw
    calc
      X + s ≤ 2 * A + s := Nat.add_le_add_right hX2A s
      _ ≤ 4 * M * s + s := Nat.add_le_add_right htwice s
      _ ≤ 4 * M * s + M * s := Nat.add_le_add_left hsMs _
      _ = 5 * M * s := by ring
  have hX : 1 ≤ X := by omega
  have hden1 : (0 : ℝ) < 5 * M := by positivity
  have hden2 : (0 : ℝ) < ((X + s : ℕ) : ℝ) := by positivity
  have hratio : (1 : ℝ) / (5 * M) ≤ (s : ℝ) / (X + s : ℕ) := by
    apply (div_le_div_iff₀ hden1 hden2).2
    exact_mod_cast (by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using htop)
  exact hratio.trans (sliceA2_harmonic_lower X s hX)

/-- If the two collars total at most the slice width, the enlarged relative
length is at most four times the slice harmonic mass. -/
theorem sliceA2_enlarged_ratio_le_four_harmonic
    (X s Delta : ℕ) (hX : 1 ≤ X) (hsX : s ≤ X)
    (hDelta : Delta ≤ 2 * s) :
    (Delta : ℝ) / X ≤
      4 * ∑ n ∈ Finset.Ioc X (X + s), (1 : ℝ) / n := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hXs : (0 : ℝ) < ((X + s : ℕ) : ℝ) := by positivity
  have hsXR : (s : ℝ) ≤ X := by exact_mod_cast hsX
  have hmass := sliceA2_harmonic_lower X s hX
  have hratio : (s : ℝ) / X ≤ 2 * ((s : ℝ) / (X + s : ℕ)) := by
    rw [div_le_iff₀ hXR, div_eq_mul_inv, mul_assoc]
    have hform : 2 * (((s : ℝ) * ((X + s : ℕ) : ℝ)⁻¹) * X) =
        (2 * (s : ℝ) * X) / ((X + s : ℕ) : ℝ) := by
      rw [div_eq_mul_inv]
      ring
    rw [hform, le_div_iff₀ hXs]
    push_cast
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ s by positivity)
      (sub_nonneg.mpr hsXR)]
  have hDeltaR : (Delta : ℝ) ≤ 2 * s := by exact_mod_cast hDelta
  calc
    (Delta : ℝ) / X ≤ (2 * (s : ℝ)) / X := by gcongr
    _ = 2 * ((s : ℝ) / X) := by ring
    _ ≤ 2 * (2 * ((s : ℝ) / (X + s : ℕ))) := by gcongr
    _ ≤ 4 * ∑ n ∈ Finset.Ioc X (X + s), (1 : ℝ) / n := by
      nlinarith

/-- The normalized low-band allowance needed by the fixed ledger. -/
theorem sliceA2_low_slot_fit
    (A s H : ℕ) (eps ElowNorm : ℝ) (hA : 0 < A)
    (hlow : ElowNorm ≤ eps ^ 2 *
      (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) / 12288) :
    (4 * (H : ℝ) / A) ^ 2 * ((A : ℝ) ^ 2 * ElowNorm) ≤
      eps ^ 2 * (H : ℝ) ^ 2 *
        (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) / 768 := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  calc
    (4 * (H : ℝ) / A) ^ 2 * ((A : ℝ) ^ 2 * ElowNorm) =
        16 * (H : ℝ) ^ 2 * ElowNorm := by field_simp; ring
    _ ≤ 16 * (H : ℝ) ^ 2 *
        (eps ^ 2 * (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) / 12288) := by
      gcongr
    _ = _ := by ring

/-- A capstone budget with `Delta/A ≤ 4W` fits the normalized inner slot
once `6144*c3*epsBand² ≤ eps²`. -/
theorem sliceA2_inner_slot_fit
    (A s Delta H : ℕ) (c3 epsBand eps EinnerNorm : ℝ)
    (hA : 0 < A) (hc3 : 0 ≤ c3)
    (hratio : (Delta : ℝ) / A ≤
      4 * ∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n)
    (henergy : EinnerNorm ≤
      (4 * (H : ℝ) / A) ^ 2 *
        bandBudget c3 epsBand ((Delta : ℝ) / A))
    (hbudget : 6144 * c3 * epsBand ^ 2 ≤ eps ^ 2) :
    (A : ℝ) ^ 2 * EinnerNorm ≤
      eps ^ 2 * (H : ℝ) ^ 2 *
        (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) / 768 := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hscale0 : 0 ≤ c3 * epsBand ^ 2 / 8 := by positivity
  have hband : bandBudget c3 epsBand ((Delta : ℝ) / A) ≤
      c3 * epsBand ^ 2 *
        (4 * ∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) / 8 := by
    unfold bandBudget
    calc
      c3 * epsBand ^ 2 * ((Delta : ℝ) / A) / 8 =
          (c3 * epsBand ^ 2 / 8) * ((Delta : ℝ) / A) := by ring
      _ ≤ (c3 * epsBand ^ 2 / 8) *
          (4 * ∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) :=
        mul_le_mul_of_nonneg_left hratio hscale0
      _ = _ := by ring
  calc
    (A : ℝ) ^ 2 * EinnerNorm ≤
        (A : ℝ) ^ 2 * ((4 * (H : ℝ) / A) ^ 2 *
          bandBudget c3 epsBand ((Delta : ℝ) / A)) := by gcongr
    _ = 16 * (H : ℝ) ^ 2 *
        bandBudget c3 epsBand ((Delta : ℝ) / A) := by field_simp; ring
    _ ≤ 16 * (H : ℝ) ^ 2 *
        (c3 * epsBand ^ 2 *
          (4 * ∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) / 8) := by
      gcongr
    _ ≤ eps ^ 2 * (H : ℝ) ^ 2 *
        (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) / 768 := by
      have hH0 : 0 ≤ (H : ℝ) ^ 2 := sq_nonneg _
      have hW0 : 0 ≤ ∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n :=
        Finset.sum_nonneg fun n _ => by positivity
      nlinarith [mul_nonneg hH0 hW0]

end Tao2015

end MoltResearch
