import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryData

/-!
# Track R A2-V': ordinary wide-leg scale fits

The collision energy must use the reciprocal-square tail, rather than the
cardinality of the entire long prime interval.  This leaf records that
telescope and splits the collision allowance into prime-scale and
cardinality-scale halves.
-/

namespace MoltResearch

namespace Tao2015

open Finset ExpSums

/-- Any prime interval above `P` has reciprocal-square mass at most `2/P`.
The estimate is deliberately independent of its upper endpoint. -/
theorem sliceA2LadderPrimes_sq_mass_le_two_div
    (P0 ratio0 eta j : ℕ) (hP0 : 2 ≤ P0) :
    ∑ p ∈ sliceA2LadderPrimes P0 ratio0 eta j,
        (1 : ℝ) / (p : ℝ) ^ 2 ≤
      2 / (sliceA2LadderP P0 ratio0 eta j : ℝ) := by
  let P := sliceA2LadderP P0 ratio0 eta j
  let Q := sliceA2LadderQ P0 ratio0 eta j
  have hP2 : 2 ≤ P := by
    simpa [P] using sliceA2LadderP_two_le P0 ratio0 eta j hP0
  have hsub : sliceA2LadderPrimes P0 ratio0 eta j ⊆
      Finset.Ico (P + 1) (Q + 1) := by
    intro p hp
    rw [Finset.mem_Ico]
    have hb := sliceA2LadderPrimes_bounds P0 ratio0 eta j p hp
    simpa [P, Q] using (show P + 1 ≤ p ∧ p < Q + 1 by omega)
  have hsum :
      ∑ p ∈ sliceA2LadderPrimes P0 ratio0 eta j,
          (1 : ℝ) / (p : ℝ) ^ 2 ≤
        ∑ p ∈ Finset.Ico (P + 1) (Q + 1),
          (1 : ℝ) / (p : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
  have htail := sum_inv_sq_Ico_le (P + 1) (Q + 1) (by omega)
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hPP : (P : ℝ) ≤ P + 1 := by push_cast; linarith
  calc
    ∑ p ∈ sliceA2LadderPrimes P0 ratio0 eta j,
        (1 : ℝ) / (p : ℝ) ^ 2 ≤
      ∑ p ∈ Finset.Ico (P + 1) (Q + 1),
        (1 : ℝ) / (p : ℝ) ^ 2 := hsum
    _ ≤ 2 / (P + 1 : ℕ) := htail
    _ ≤ 2 / P := by
      apply div_le_div_of_nonneg_left (by norm_num) hPpos
      simpa using hPP
    _ = 2 / (sliceA2LadderP P0 ratio0 eta j : ℝ) := by rfl

/-- Separate prime-scale and finite-cardinality margins imply the complete
wide collision fit. -/
theorem sliceA2Ordinary_collision_fit_of_split
    (P0 ratio0 eta j A : ℕ) (eps rho0 rho T : ℝ)
    (hP0 : 2 ≤ P0) (hA : 2 ≤ A) (hTA : T ≤ A)
    (hratio : rho0 ≤ rho)
    (hprime : 160 * Real.exp Real.pi /
        (sliceA2LadderP P0 ratio0 eta j : ℝ) ≤
      sliceA2KappaCollision j * eps ^ 2 * rho0 / 16)
    (hcard : 40 * Real.exp Real.pi *
        (((sliceA2LadderPrimes P0 ratio0 eta j).card : ℝ) / A) ≤
      sliceA2KappaCollision j * eps ^ 2 * rho0 / 16) :
    8 * collisionEnergyBoundWide A
        (sliceA2LadderPrimes P0 ratio0 eta j) T ≤
      sliceA2KappaCollision j * bandBudget 1 eps rho := by
  apply collisionEnergyBoundWide_fit_of_mass_card_ratio A
    (sliceA2LadderPrimes P0 ratio0 eta j) T
    (2 / (sliceA2LadderP P0 ratio0 eta j : ℝ))
    (sliceA2KappaCollision j) 1 eps rho0 rho hA hTA
    (sliceA2LadderPrimes_sq_mass_le_two_div P0 ratio0 eta j hP0)
  · simpa only [one_mul] using (show
      40 * Real.exp Real.pi *
          (2 * (2 / (sliceA2LadderP P0 ratio0 eta j : ℝ)) +
            ((sliceA2LadderPrimes P0 ratio0 eta j).card : ℝ) / A) ≤
        sliceA2KappaCollision j * (eps ^ 2 * rho0 / 8) by
      have hsum := add_le_add hprime hcard
      calc
        40 * Real.exp Real.pi *
            (2 * (2 / (sliceA2LadderP P0 ratio0 eta j : ℝ)) +
              ((sliceA2LadderPrimes P0 ratio0 eta j).card : ℝ) / A) =
          160 * Real.exp Real.pi /
              (sliceA2LadderP P0 ratio0 eta j : ℝ) +
            40 * Real.exp Real.pi *
              (((sliceA2LadderPrimes P0 ratio0 eta j).card : ℝ) / A) := by ring
        _ ≤ sliceA2KappaCollision j * eps ^ 2 * rho0 / 16 +
            sliceA2KappaCollision j * eps ^ 2 * rho0 / 16 := hsum
        _ = sliceA2KappaCollision j * (eps ^ 2 * rho0 / 8) := by ring)
  · norm_num
  · exact (sliceA2Kappa_nonneg j).2.2
  · exact hratio

/-- One pair of scale margins closes both ordinary wide legs. -/
theorem sliceA2Ordinary_wide_fits
    (P0 ratio0 eta j A : ℕ) (eps rho0 rho T : ℝ)
    (hP0 : 3 ≤ P0) (hA : 2 ≤ A) (hTA : T ≤ A)
    (heps : 0 < eps) (hrho0 : 0 < rho0) (hratio : rho0 ≤ rho)
    (hreplacementCard : 64 * 9 * Real.exp Real.pi *
        (((sliceA2LadderPrimes P0 ratio0 eta j).card : ℝ) / A) ≤
      sliceA2KappaReplacement j * eps ^ 2 * rho0 / 16)
    (hcollisionPrime : 160 * Real.exp Real.pi /
        (sliceA2LadderP P0 ratio0 eta j : ℝ) ≤
      sliceA2KappaCollision j * eps ^ 2 * rho0 / 16)
    (hcollisionCard : 40 * Real.exp Real.pi *
        (((sliceA2LadderPrimes P0 ratio0 eta j).card : ℝ) / A) ≤
      sliceA2KappaCollision j * eps ^ 2 * rho0 / 16) :
    (2 * replacementEnergyBoundWide A
        (sliceA2LadderPrimes P0 ratio0 eta j)
        (sliceA2OrdinaryN P0 ratio0 eta j eps rho0) T ≤
      sliceA2KappaReplacement j * bandBudget 1 eps rho) ∧
    (8 * collisionEnergyBoundWide A
        (sliceA2LadderPrimes P0 ratio0 eta j) T ≤
      sliceA2KappaCollision j * bandBudget 1 eps rho) := by
  constructor
  · exact sliceA2Ordinary_replacement_fit P0 ratio0 eta j A eps rho0 rho T
      hP0 hA hTA heps hrho0 hratio hreplacementCard
  · exact sliceA2Ordinary_collision_fit_of_split P0 ratio0 eta j A eps rho0
      rho T (by omega) hA hTA hratio hcollisionPrime hcollisionCard

end Tao2015

end MoltResearch
