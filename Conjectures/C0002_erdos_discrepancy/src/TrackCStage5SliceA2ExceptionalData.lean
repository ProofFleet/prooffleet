import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryZero

/-!
# Track R A2-V': concrete exceptional schedule data

The remote interval receives a cell resolution chosen from the fixed short-
slice budget floor.  This file packages its corrected representatives,
Brun anchors, adaptive moments and collars, and closes the reciprocal-mass
part of the wide exceptional leg.  The remaining scale terms are displayed
separately so they can be discharged by enlarging the window base.
-/

namespace MoltResearch

namespace Tao2015

open Finset ExpSums

/-- The fixed Mertens envelope for the remote power interval. -/
noncomputable def sliceA2ExceptionalMass (A1 : ℕ) (epsc : ℝ) : ℝ :=
  Real.log ((exceptionalIntervalRatio epsc : ℝ) + 1) + 12

theorem sliceA2ExceptionalMass_nonneg (A1 : ℕ) (epsc : ℝ) :
    0 ≤ sliceA2ExceptionalMass A1 epsc := by
  unfold sliceA2ExceptionalMass
  have harg : (1 : ℝ) ≤ (exceptionalIntervalRatio epsc : ℝ) + 1 := by
    have hR : (0 : ℝ) ≤ exceptionalIntervalRatio epsc := by positivity
    linarith
  linarith [Real.log_nonneg harg]

theorem exceptionalPrimes_mass_le_sliceA2ExceptionalMass
    (A1 : ℕ) (epsc : ℝ) :
    ∑ p ∈ exceptionalPrimes A1 epsc, (1 : ℝ) / p ≤
      sliceA2ExceptionalMass A1 epsc := by
  simpa [exceptionalPrimes, exceptionalPrimeUpper, sliceA2ExceptionalMass]
    using prime_power_Ioc_mass_upper (exceptionalPrimeLower A1)
      (exceptionalIntervalRatio epsc) (exceptionalPrimeLower_three_le A1)
      (by
        have := exceptionalIntervalRatio_three_le epsc
        omega)

/-- The exceptional cell resolution.  The coefficient
`73728 = 64 * 1152` assigns half of the wide allowance to the reciprocal
prime mass. -/
noncomputable def sliceA2ExceptionalN
    (A1 : ℕ) (epsc eps rho0 : ℝ) : ℕ :=
  max 2 ⌈73728 * Real.exp Real.pi * sliceA2ExceptionalMass A1 epsc /
    (eps ^ 2 * rho0)⌉₊

theorem sliceA2ExceptionalN_two_le
    (A1 : ℕ) (epsc eps rho0 : ℝ) :
    2 ≤ sliceA2ExceptionalN A1 epsc eps rho0 := by
  unfold sliceA2ExceptionalN
  exact le_max_left _ _

theorem sliceA2ExceptionalN_pos
    (A1 : ℕ) (epsc eps rho0 : ℝ) :
    0 < sliceA2ExceptionalN A1 epsc eps rho0 := by
  have := sliceA2ExceptionalN_two_le A1 epsc eps rho0
  omega

/-- The chosen resolution pays the remote reciprocal-mass contribution. -/
theorem sliceA2ExceptionalN_mass_fit
    (A1 : ℕ) (epsc eps rho0 : ℝ)
    (heps : 0 < eps) (hrho0 : 0 < rho0) :
    1152 * Real.exp Real.pi *
        (sliceA2ExceptionalMass A1 epsc /
          (sliceA2ExceptionalN A1 epsc eps rho0 : ℝ)) ≤
      eps ^ 2 * rho0 / 64 := by
  let E := sliceA2ExceptionalMass A1 epsc
  let budget := eps ^ 2 * rho0
  let C := 73728 * Real.exp Real.pi
  have hE : 0 ≤ E := sliceA2ExceptionalMass_nonneg A1 epsc
  have hbudget : 0 < budget := by dsimp [budget]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hratio0 : 0 ≤ C * E / budget := by positivity
  have hceil : C * E / budget ≤ (⌈C * E / budget⌉₊ : ℕ) :=
    Nat.le_ceil _
  have hNlower : C * E / budget ≤
      (sliceA2ExceptionalN A1 epsc eps rho0 : ℝ) := by
    refine hceil.trans ?_
    exact_mod_cast (le_max_right 2 ⌈C * E / budget⌉₊)
  have hcross : C * E ≤
      budget * (sliceA2ExceptionalN A1 epsc eps rho0 : ℝ) := by
    calc
      C * E = budget * (C * E / budget) := by field_simp
      _ ≤ budget * (sliceA2ExceptionalN A1 epsc eps rho0 : ℝ) :=
        mul_le_mul_of_nonneg_left hNlower hbudget.le
  have hN0 : (0 : ℝ) < sliceA2ExceptionalN A1 epsc eps rho0 := by
    exact_mod_cast sliceA2ExceptionalN_pos A1 epsc eps rho0
  have hdiv : C * E /
      (sliceA2ExceptionalN A1 epsc eps rho0 : ℝ) ≤ budget :=
    (div_le_iff₀ hN0).2 hcross
  dsimp [C, E, budget] at hdiv ⊢
  calc
    1152 * Real.exp Real.pi *
          (sliceA2ExceptionalMass A1 epsc /
            (sliceA2ExceptionalN A1 epsc eps rho0 : ℝ)) =
        (73728 * Real.exp Real.pi * sliceA2ExceptionalMass A1 epsc /
          (sliceA2ExceptionalN A1 epsc eps rho0 : ℝ)) / 64 := by ring
    _ ≤ (eps ^ 2 * rho0) / 64 :=
      div_le_div_of_nonneg_right hdiv (by norm_num)

/-! ## Concrete cells, representatives, anchors and moments -/

noncomputable def sliceA2ExceptionalV0
    (A1 : ℕ) (epsc eps rho0 : ℝ) : ℕ :=
  exceptionalV0 A1 (sliceA2ExceptionalN A1 epsc eps rho0)

noncomputable def sliceA2ExceptionalV1
    (A1 : ℕ) (epsc eps rho0 : ℝ) : ℕ :=
  exceptionalV1 A1 (sliceA2ExceptionalN A1 epsc eps rho0) epsc

noncomputable def sliceA2ExceptionalRepresentative
    (A1 v : ℕ) (epsc eps rho0 : ℝ) : ℕ :=
  exceptionalRepresentative A1
    (sliceA2ExceptionalN A1 epsc eps rho0) v epsc

noncomputable def sliceA2ExceptionalAnchor
    (A1 v : ℕ) (epsc eps rho0 : ℝ) : ℕ :=
  exceptionalCellAnchor (sliceA2ExceptionalN A1 epsc eps rho0) v

noncomputable def sliceA2ExceptionalMoment
    (A1 v : ℕ) (epsc eps rho0 T : ℝ) : ℕ :=
  exceptionalCellMoment (sliceA2ExceptionalN A1 epsc eps rho0) v T

/-- The complete exceptional cell interface in final-schedule notation. -/
theorem sliceA2Exceptional_cell_data
    (A1 : ℕ) (epsc eps rho0 : ℝ) :
    ((Finset.Ico (sliceA2ExceptionalV0 A1 epsc eps rho0)
        (sliceA2ExceptionalV1 A1 epsc eps rho0 + 1)).biUnion
      (eadicCell (exceptionalPrimes A1 epsc)
        (2 * sliceA2ExceptionalN A1 epsc eps rho0)) =
        exceptionalPrimes A1 epsc) ∧
    (∀ v ∈ Finset.Ico (sliceA2ExceptionalV0 A1 epsc eps rho0)
        (sliceA2ExceptionalV1 A1 epsc eps rho0 + 1),
      (sliceA2ExceptionalRepresentative A1 v epsc eps rho0 : ℝ) ≤
        Real.exp (((v : ℝ) + 1) /
          (2 * (sliceA2ExceptionalN A1 epsc eps rho0 : ℝ)))) ∧
    (∀ v, 1 ≤ sliceA2ExceptionalRepresentative A1 v epsc eps rho0) ∧
    (∀ v ∈ Finset.Ico (sliceA2ExceptionalV0 A1 epsc eps rho0)
        (sliceA2ExceptionalV1 A1 epsc eps rho0 + 1),
      ∀ p ∈ eadicCell (exceptionalPrimes A1 epsc)
          (2 * sliceA2ExceptionalN A1 epsc eps rho0) v,
        sliceA2ExceptionalRepresentative A1 v epsc eps rho0 ≤ p) ∧
    (∀ v ∈ Finset.Ico (sliceA2ExceptionalV0 A1 epsc eps rho0)
        (sliceA2ExceptionalV1 A1 epsc eps rho0 + 1),
      ∀ p ∈ eadicCell (exceptionalPrimes A1 epsc)
          (2 * sliceA2ExceptionalN A1 epsc eps rho0) v,
        sliceA2ExceptionalN A1 epsc eps rho0 * p ≤
          (sliceA2ExceptionalN A1 epsc eps rho0 + 1) *
            sliceA2ExceptionalRepresentative A1 v epsc eps rho0) := by
  simpa [sliceA2ExceptionalV0, sliceA2ExceptionalV1,
    sliceA2ExceptionalRepresentative] using
      exceptionalLevel_cell_data A1
        (sliceA2ExceptionalN A1 epsc eps rho0) epsc
        (sliceA2ExceptionalN_pos A1 epsc eps rho0)

/-- The window endpoint guard supplies both exceptional collar families. -/
theorem sliceA2Exceptional_collar_data
    (A1 A Delta : ℕ) (epsc eps rho0 : ℝ)
    (hNuQ : sliceA2ExceptionalN A1 epsc eps rho0 *
      exceptionalPrimeUpper A1 epsc ≤ A) :
    (∀ v ∈ Finset.Ico (sliceA2ExceptionalV0 A1 epsc eps rho0)
        (sliceA2ExceptionalV1 A1 epsc eps rho0 + 1),
      ∀ p ∈ eadicCell (exceptionalPrimes A1 epsc)
          (2 * sliceA2ExceptionalN A1 epsc eps rho0) v,
        A / (sliceA2ExceptionalN A1 epsc eps rho0 * p) + 1 ≤ A / p) ∧
    (∀ v ∈ Finset.Ico (sliceA2ExceptionalV0 A1 epsc eps rho0)
        (sliceA2ExceptionalV1 A1 epsc eps rho0 + 1),
      ∀ p ∈ eadicCell (exceptionalPrimes A1 epsc)
          (2 * sliceA2ExceptionalN A1 epsc eps rho0) v,
        (A + Delta) /
            (sliceA2ExceptionalN A1 epsc eps rho0 * p) + 1 ≤
          (A + Delta) / p) := by
  simpa [sliceA2ExceptionalV0, sliceA2ExceptionalV1] using
    exceptionalLevel_collar_data A1 A Delta
      (sliceA2ExceptionalN A1 epsc eps rho0) epsc
      (sliceA2ExceptionalN_two_le A1 epsc eps rho0) hNuQ

/-- Large enough lower anchors give the capstone's prime-cell data. -/
theorem sliceA2Exceptional_anchor_data
    (A1 : ℕ) (epsc eps rho0 : ℝ)
    (hanchor : ∀ v ∈ Finset.Ico
      (sliceA2ExceptionalV0 A1 epsc eps rho0)
      (sliceA2ExceptionalV1 A1 epsc eps rho0 + 1),
      6 ≤ sliceA2ExceptionalAnchor A1 v epsc eps rho0) :
    (∀ v ∈ Finset.Ico (sliceA2ExceptionalV0 A1 epsc eps rho0)
      (sliceA2ExceptionalV1 A1 epsc eps rho0 + 1),
      2 ≤ sliceA2ExceptionalAnchor A1 v epsc eps rho0) ∧
    (∀ v ∈ Finset.Ico (sliceA2ExceptionalV0 A1 epsc eps rho0)
      (sliceA2ExceptionalV1 A1 epsc eps rho0 + 1),
      ∀ p ∈ eadicCell (exceptionalPrimes A1 epsc)
          (2 * sliceA2ExceptionalN A1 epsc eps rho0) v,
        sliceA2ExceptionalAnchor A1 v epsc eps rho0 < p) ∧
    (∀ v ∈ Finset.Ico (sliceA2ExceptionalV0 A1 epsc eps rho0)
      (sliceA2ExceptionalV1 A1 epsc eps rho0 + 1),
      ∀ p ∈ eadicCell (exceptionalPrimes A1 epsc)
          (2 * sliceA2ExceptionalN A1 epsc eps rho0) v,
        p ≤ 2 * sliceA2ExceptionalAnchor A1 v epsc eps rho0) := by
  simpa [sliceA2ExceptionalV0, sliceA2ExceptionalV1,
    sliceA2ExceptionalAnchor] using
      exceptionalCellAnchor_data A1
        (sliceA2ExceptionalN A1 epsc eps rho0) epsc
        (sliceA2ExceptionalN_two_le A1 epsc eps rho0)
        (by simpa [sliceA2ExceptionalAnchor] using! hanchor)

theorem sliceA2ExceptionalMoment_one_le
    (A1 v : ℕ) (epsc eps rho0 T : ℝ) :
    1 ≤ sliceA2ExceptionalMoment A1 v epsc eps rho0 T := by
  exact exceptionalCellMoment_one_le
    (sliceA2ExceptionalN A1 epsc eps rho0) v T

/-! ## Wide error -/

/-- The remote reciprocal-square mass has no dependence on its upper
endpoint. -/
theorem exceptionalPrimes_sq_mass_le_two_div
    (A1 : ℕ) (epsc : ℝ) :
    ∑ p ∈ exceptionalPrimes A1 epsc,
        (1 : ℝ) / (p : ℝ) ^ 2 ≤
      2 / (exceptionalPrimeLower A1 : ℝ) := by
  let P := exceptionalPrimeLower A1
  let Q := exceptionalPrimeUpper A1 epsc
  have hP2 : 2 ≤ P := by
    simpa [P] using (show 2 ≤ exceptionalPrimeLower A1 by
      have := exceptionalPrimeLower_three_le A1
      omega)
  have hsub : exceptionalPrimes A1 epsc ⊆
      Finset.Ico (P + 1) (Q + 1) := by
    intro p hp
    rw [Finset.mem_Ico]
    have hb := exceptionalPrimes_bounds A1 epsc p hp
    simpa [P, Q] using (show P + 1 ≤ p ∧ p < Q + 1 by omega)
  have hsum :
      ∑ p ∈ exceptionalPrimes A1 epsc, (1 : ℝ) / (p : ℝ) ^ 2 ≤
        ∑ p ∈ Finset.Ico (P + 1) (Q + 1),
          (1 : ℝ) / (p : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
  have htail := sum_inv_sq_Ico_le (P + 1) (Q + 1) (by omega)
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hPP : (P : ℝ) ≤ P + 1 := by push_cast; linarith
  calc
    ∑ p ∈ exceptionalPrimes A1 epsc,
        (1 : ℝ) / (p : ℝ) ^ 2 ≤
      ∑ p ∈ Finset.Ico (P + 1) (Q + 1),
        (1 : ℝ) / (p : ℝ) ^ 2 := hsum
    _ ≤ 2 / (P + 1 : ℕ) := htail
    _ ≤ 2 / P := by
      apply div_le_div_of_nonneg_left (by norm_num) hPpos
      simpa using hPP
    _ = 2 / (exceptionalPrimeLower A1 : ℝ) := by rfl

/-- Four fixed margins close the complete wide exceptional error. -/
theorem sliceA2Exceptional_wide_fit
    (A1 A : ℕ) (epsc eps rho0 T : ℝ)
    (hA : 2 ≤ A) (hTA : T ≤ A) (heps : 0 < eps) (hrho0 : 0 < rho0)
    (hreplacementCard : 1152 * Real.exp Real.pi *
        (((exceptionalPrimes A1 epsc).card : ℝ) / A) ≤
      eps ^ 2 * rho0 / 192)
    (hcollisionPrime : 320 * Real.exp Real.pi /
        (exceptionalPrimeLower A1 : ℝ) ≤ eps ^ 2 * rho0 / 192)
    (hcollisionCard : 80 * Real.exp Real.pi *
        (((exceptionalPrimes A1 epsc).card : ℝ) / A) ≤
      eps ^ 2 * rho0 / 192) :
    2 * (2 * replacementEnergyBoundWide A (exceptionalPrimes A1 epsc)
          (sliceA2ExceptionalN A1 epsc eps rho0) T +
        2 * (4 * collisionEnergyBoundWide A
          (exceptionalPrimes A1 epsc) T)) ≤ eps ^ 2 * rho0 / 32 := by
  have hmass := sliceA2ExceptionalN_mass_fit A1 epsc eps rho0 heps hrho0
  have hsum := add_le_add (add_le_add (add_le_add hmass hreplacementCard)
    hcollisionPrime) hcollisionCard
  have hfit :
      1152 * Real.exp Real.pi *
            (sliceA2ExceptionalMass A1 epsc /
                (sliceA2ExceptionalN A1 epsc eps rho0 : ℝ) +
              ((exceptionalPrimes A1 epsc).card : ℝ) / A) +
          80 * Real.exp Real.pi *
            (2 * (2 / (exceptionalPrimeLower A1 : ℝ)) +
              ((exceptionalPrimes A1 epsc).card : ℝ) / A) ≤
        eps ^ 2 * rho0 / 32 := by
    calc
      _ = 1152 * Real.exp Real.pi *
              (sliceA2ExceptionalMass A1 epsc /
                (sliceA2ExceptionalN A1 epsc eps rho0 : ℝ)) +
          1152 * Real.exp Real.pi *
              (((exceptionalPrimes A1 epsc).card : ℝ) / A) +
          320 * Real.exp Real.pi /
              (exceptionalPrimeLower A1 : ℝ) +
          80 * Real.exp Real.pi *
              (((exceptionalPrimes A1 epsc).card : ℝ) / A) := by ring
      _ ≤ eps ^ 2 * rho0 / 64 + eps ^ 2 * rho0 / 192 +
          eps ^ 2 * rho0 / 192 + eps ^ 2 * rho0 / 192 := hsum
      _ = eps ^ 2 * rho0 / 32 := by ring
  have hwide := exceptional_wide_cost_fit_ratio A
    (sliceA2ExceptionalN A1 epsc eps rho0)
    (exceptionalPrimes A1 epsc) T (sliceA2ExceptionalMass A1 epsc)
    (2 / (exceptionalPrimeLower A1 : ℝ)) 1 eps rho0
    (by omega) (sliceA2ExceptionalN_pos A1 epsc eps rho0) hTA
    (exceptionalPrimes_mass_le_sliceA2ExceptionalMass A1 epsc)
    (exceptionalPrimes_sq_mass_le_two_div A1 epsc) (by simpa using hfit)
  simpa only [one_mul] using hwide

end Tao2015

end MoltResearch
