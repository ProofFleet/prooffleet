import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2CutoffGrowth

/-!
# Track R A2-V'-17: the concrete final level list

This leaf specializes the abstract inner-band list to the two-ratio ordinary
ladder and the remote exceptional interval.  It records the structural facts
consumed both by `SliceMeanSquareA2` and by the shifted capstone.
-/

namespace MoltResearch

namespace Tao2015

/-- The final level list chosen at base scale `A1`. -/
noncomputable def sliceA2FinalLevels
    (P0 ratio0 eta A1 : ℕ) (epsc : ℝ) (hP0 : 2 ≤ P0) :
    List (Finset ℕ) :=
  innerBandLevels (sliceA2LadderPrimes P0 ratio0 eta)
    (exceptionalPrimes A1 epsc)
    (sliceA2LadderJ P0 ratio0 eta A1 hP0)

/-- Every member of the final level list is a set of primes. -/
theorem sliceA2FinalLevels_prime
    (P0 ratio0 eta A1 : ℕ) (epsc : ℝ) (hP0 : 2 ≤ P0) :
    ∀ P ∈ sliceA2FinalLevels P0 ratio0 eta A1 epsc hP0,
      ∀ p ∈ P, p.Prime := by
  intro P hP p hp
  unfold sliceA2FinalLevels innerBandLevels at hP
  rw [List.mem_append] at hP
  rcases hP with hordinary | hexceptional
  · rw [List.mem_map] at hordinary
    obtain ⟨j, hj, rfl⟩ := hordinary
    exact sliceA2LadderPrimes_prime P0 ratio0 eta j p hp
  · simp only [List.mem_singleton] at hexceptional
    subst P
    exact exceptionalPrimes_prime A1 epsc p hp

/-- The last scheduled upper endpoint dominates every earlier one. -/
theorem sliceA2LadderQ_le_last
    (P0 ratio0 eta J j : ℕ) (hP0 : 2 ≤ P0)
    (hJ : 0 < J) (hj : j < J) :
    sliceA2LadderQ P0 ratio0 eta j ≤
      sliceA2LadderQ P0 ratio0 eta (J - 1) := by
  by_cases heq : j = J - 1
  · rw [heq]
  · have hjlast : j < J - 1 := by omega
    exact (sliceA2LadderQ_lt_P_of_lt P0 ratio0 eta j (J - 1) hP0
      hjlast).le.trans (sliceA2LadderP_le_Q P0 ratio0 eta (J - 1))

/-- Ordinary levels of the final list are pairwise disjoint. -/
theorem sliceA2FinalLevels_ordinary_disjoint
    (P0 ratio0 eta A1 : ℕ) (hP0 : 2 ≤ P0) :
    ∀ i < sliceA2LadderJ P0 ratio0 eta A1 hP0,
      ∀ j < sliceA2LadderJ P0 ratio0 eta A1 hP0, i ≠ j →
        Disjoint (sliceA2LadderPrimes P0 ratio0 eta i)
          (sliceA2LadderPrimes P0 ratio0 eta j) := by
  intro i hi j hj hij
  exact sliceA2LadderPrimes_disjoint P0 ratio0 eta i j hP0 hij

/-- One last-endpoint inequality separates every ordinary level from the
remote exceptional interval. -/
theorem sliceA2FinalLevels_exceptional_disjoint
    (P0 ratio0 eta A1 : ℕ) (epsc : ℝ) (hP0 : 2 ≤ P0)
    (hsep : sliceA2LadderQ P0 ratio0 eta
        (sliceA2LadderJ P0 ratio0 eta A1 hP0 - 1) ≤
      exceptionalPrimeLower A1) :
    ∀ i < sliceA2LadderJ P0 ratio0 eta A1 hP0,
      Disjoint (sliceA2LadderPrimes P0 ratio0 eta i)
        (exceptionalPrimes A1 epsc) := by
  intro i hi
  apply sliceA2LadderPrimes_disjoint_interval P0 ratio0 eta i
    (exceptionalPrimeLower A1) (exceptionalPrimeUpper A1 epsc)
  exact (sliceA2LadderQ_le_last P0 ratio0 eta
    (sliceA2LadderJ P0 ratio0 eta A1 hP0) i hP0
    (sliceA2LadderJ_pos P0 ratio0 eta A1 hP0) hi).trans hsep

/-- A single bottom threshold puts every prime in every final level above
the requested polylogarithmic cutoff. -/
theorem sliceA2FinalLevels_above_polylog
    (P0 ratio0 eta A1 h B : ℕ) (epsc C : ℝ) (hP0 : 2 ≤ P0)
    (hbottom : C * Real.log h ^ B < P0)
    (hremote : P0 ≤ exceptionalPrimeLower A1) :
    ∀ P ∈ sliceA2FinalLevels P0 ratio0 eta A1 epsc hP0,
      ∀ p ∈ P, C * Real.log h ^ B < p := by
  intro P hP p hp
  unfold sliceA2FinalLevels innerBandLevels at hP
  rw [List.mem_append] at hP
  rcases hP with hordinary | hexceptional
  · rw [List.mem_map] at hordinary
    obtain ⟨j, hj, rfl⟩ := hordinary
    have hP0j : P0 ≤ sliceA2LadderP P0 ratio0 eta j :=
      sliceA2LadderP_mono P0 ratio0 eta hP0 (Nat.zero_le j)
    have hjp := (sliceA2LadderPrimes_bounds P0 ratio0 eta j p hp).1
    exact hbottom.trans (by exact_mod_cast hP0j.trans_lt hjp)
  · simp only [List.mem_singleton] at hexceptional
    subst P
    have hpU := (exceptionalPrimes_bounds A1 epsc p hp).1
    exact hbottom.trans (by exact_mod_cast hremote.trans_lt hpU)

/-- In low-band order the exceptional level sits beside level zero, followed
by the positive ordinary ladder. -/
theorem sliceA2FinalLevels_perm_lowBand
    (P0 ratio0 eta A1 : ℕ) (epsc : ℝ) (hP0 : 2 ≤ P0) :
    (sliceA2FinalLevels P0 ratio0 eta A1 epsc hP0).Perm
      ([sliceA2LadderPrimes P0 ratio0 eta 0, exceptionalPrimes A1 epsc] ++
        (List.range (sliceA2LadderJ P0 ratio0 eta A1 hP0 - 1)).map
          (fun i => sliceA2LadderPrimes P0 ratio0 eta (i + 1))) := by
  unfold sliceA2FinalLevels
  exact innerBandLevels_perm_lowBand
    (sliceA2LadderPrimes P0 ratio0 eta) (exceptionalPrimes A1 epsc)
    (sliceA2LadderJ P0 ratio0 eta A1 hP0)
    (sliceA2LadderJ_pos P0 ratio0 eta A1 hP0)

end Tao2015

end MoltResearch
