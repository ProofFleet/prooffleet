import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2Bump

/-!
# Track R A2-V'-8: rounded short-slice geometry

This file fixes the only two integer roundings in the window schedule.  The
collar is the ceiling of `epsGeom*H/100`, and the slice width is `A/M`.
The latter retains the uniform relative budget floor `1/(4M)` even when the
capstone is applied at a later left endpoint `X ∈ [A,2A]`.
-/

namespace MoltResearch

namespace Tao2015

/-- Integer collar used by every small slice. -/
noncomputable def sliceA2Collar (epsGeom : ℝ) (H : ℕ) : ℕ :=
  ⌈epsGeom * H / 100⌉₊

/-- Rounding the collar loses at most a factor two once
`epsGeom*H ≥ 100`. -/
theorem sliceA2Collar_bounds
    (epsGeom : ℝ) (H : ℕ) (heps1 : epsGeom ≤ 1)
    (hlarge : 100 ≤ epsGeom * H) :
    let U := sliceA2Collar epsGeom H
    0 < U ∧ epsGeom * (H : ℝ) ≤ 100 * U ∧
      50 * (U : ℝ) ≤ epsGeom * H ∧ 50 * U ≤ H ∧
      2 * (U + 1) ≤ H := by
  dsimp only [sliceA2Collar]
  let x : ℝ := epsGeom * H / 100
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : 1 ≤ x := by dsimp [x]; nlinarith
  have hlower : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hupp : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hHlarge : (100 : ℝ) ≤ H := by
    have hEH : epsGeom * H ≤ H := by
      have hH0 : (0 : ℝ) ≤ H := by positivity
      nlinarith
    linarith
  have hUpos : 0 < ⌈x⌉₊ := by
    have : (1 : ℝ) ≤ (⌈x⌉₊ : ℝ) := hx1.trans hlower
    exact_mod_cast this
  have hleft : epsGeom * (H : ℝ) ≤ 100 * (⌈x⌉₊ : ℝ) := by
    dsimp [x] at hlower
    nlinarith
  have hright : 50 * (⌈x⌉₊ : ℝ) ≤ epsGeom * H := by
    dsimp [x] at hupp
    nlinarith
  have h50 : 50 * ⌈x⌉₊ ≤ H := by
    have hright' : 50 * (⌈x⌉₊ : ℝ) ≤ H := by
      calc
        _ ≤ epsGeom * H := hright
        _ ≤ H := by
          have hH0 : (0 : ℝ) ≤ H := by positivity
          nlinarith
    exact_mod_cast hright'
  have htwo : 2 * (⌈x⌉₊ + 1) ≤ H := by
    have htwo' : 2 * ((⌈x⌉₊ : ℝ) + 1) ≤ H := by
      have hU : (⌈x⌉₊ : ℝ) ≤ (H : ℝ) / 50 := by
        nlinarith [show (50 : ℝ) * ⌈x⌉₊ ≤ H by exact_mod_cast h50]
      nlinarith
    exact_mod_cast htwo'
  exact ⟨hUpos, hleft, hright, h50, htwo⟩

/-- Complete geometry of one full partition slice.  The capstone interval is
enlarged by its two `H`-collars and four `U`-collars. -/
theorem sliceA2_floor_width_geometry
    (A X H M U : ℕ) (hM : 0 < M) (hM30 : 30 ≤ M) (hMA : M ≤ A)
    (hAX : A ≤ X) (hX2A : X ≤ 2 * A)
    (h3H : 3 * H ≤ A) (hU : 0 < U) (h50U : 50 * U ≤ H)
    (h2U1 : 2 * (U + 1) ≤ H) :
    let s := A / M
    let Delta := s + 2 * H + 4 * U
    1 ≤ s ∧ s ≤ X ∧ 30 * s ≤ X ∧ 3 * H ≤ X ∧
      0 < U ∧ 2 * U ≤ H ∧
      ((U : ℝ) + 1) * ((X : ℝ) + s) ≤ (X : ℝ) * H ∧
      Delta ≤ X ∧
      (1 : ℝ) / (4 * M) ≤ (Delta : ℝ) / X := by
  dsimp only
  have hs : 1 ≤ A / M := (Nat.one_le_div_iff hM).mpr hMA
  have hsA : A / M ≤ A := Nat.div_le_self A M
  have h30sA : 30 * (A / M) ≤ A := by
    calc
      30 * (A / M) ≤ M * (A / M) := Nat.mul_le_mul_right (A / M) hM30
      _ ≤ A := Nat.mul_div_le A M
  have h2U : 2 * U ≤ H := by omega
  have hDeltaA : A / M + 2 * H + 4 * U ≤ A := by
    omega
  have hplat : ((U : ℝ) + 1) * ((X : ℝ) + (A / M : ℕ)) ≤
      (X : ℝ) * H := by
    have hsX : A / M ≤ X := hsA.trans hAX
    have hsum : X + A / M ≤ 2 * X := by omega
    have hprod : (U + 1) * (X + A / M) ≤ H * X := by
      calc
        (U + 1) * (X + A / M) ≤ (U + 1) * (2 * X) :=
          Nat.mul_le_mul_left (U + 1) hsum
        _ = (2 * (U + 1)) * X := by ring
        _ ≤ H * X := Nat.mul_le_mul_right X h2U1
    exact_mod_cast (by simpa [Nat.mul_comm] using hprod)
  have hdivDecomp : A = M * (A / M) + A % M := (Nat.div_add_mod A M).symm
  have hmod : A % M < M := Nat.mod_lt A hM
  have hA2Ms : A ≤ 2 * M * (A / M) := by
    have hsM : M ≤ M * (A / M) := by
      simpa only [mul_one] using Nat.mul_le_mul_left M hs
    calc
      A = M * (A / M) + A % M := hdivDecomp
      _ ≤ M * (A / M) + M := Nat.add_le_add_left hmod.le _
      _ ≤ M * (A / M) + M * (A / M) := Nat.add_le_add_left hsM _
      _ = 2 * M * (A / M) := by ring
  have hcross : X ≤ (A / M + 2 * H + 4 * U) * (4 * M) := by
    have htwice : 2 * A ≤ 4 * M * (A / M) := by
      have := Nat.mul_le_mul_left 2 hA2Ms
      nlinarith
    have hscale : 4 * M * (A / M) ≤
        (A / M + 2 * H + 4 * U) * (4 * M) := by
      have hadd : A / M ≤ A / M + 2 * H + 4 * U := by omega
      have := Nat.mul_le_mul_right (4 * M) hadd
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this
    calc
      X ≤ 2 * A := hX2A
      _ ≤ 4 * M * (A / M) := htwice
      _ ≤ (A / M + 2 * H + 4 * U) * (4 * M) := hscale
  have hdenM : (0 : ℝ) < 4 * M := by positivity
  have hXnat : 0 < X := hM.trans_le (hMA.trans hAX)
  have hdenX : (0 : ℝ) < X := by exact_mod_cast hXnat
  have hrho : (1 : ℝ) / (4 * M) ≤
      ((A / M + 2 * H + 4 * U : ℕ) : ℝ) / X := by
    rw [div_le_div_iff₀ hdenM hdenX]
    exact_mod_cast (by simpa [Nat.mul_comm] using hcross)
  exact ⟨hs, hsA.trans hAX, h30sA.trans hAX, h3H.trans hAX, hU,
    h2U, hplat, hDeltaA.trans hAX, hrho⟩

end Tao2015

end MoltResearch
