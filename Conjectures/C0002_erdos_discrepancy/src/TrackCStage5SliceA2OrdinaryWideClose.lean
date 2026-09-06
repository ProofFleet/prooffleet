import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryLaterClose
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryWide

/-!
# Track R A2-V': simultaneous ordinary wide fits

The last ordinary upper endpoint controls every finite cardinality error.
A single scale inequality at `2^J` therefore closes both wide legs at all
levels, while the collision-prime term is paid by the fixed bottom margin.
-/

namespace MoltResearch

namespace Tao2015

/-- All ordinary replacement and collision legs follow from one last-scale
cardinality margin and one bottom collision margin. -/
theorem sliceA2Ordinary_all_wide_fits
    (P0 ratio0 eta J A : ℕ) (eps rho0 rho T : ℝ)
    (hP0 : 3 ≤ P0) (hJ : 0 < J) (hA : 2 ≤ A) (hTA : T ≤ A)
    (heps : 0 < eps) (hrho0 : 0 < rho0) (hratio : rho0 ≤ rho)
    (hcardScale :
      64 * 9 * Real.exp Real.pi *
          ((sliceA2LadderQ P0 ratio0 eta (J - 1) : ℝ) / A) ≤
        3 * eps ^ 2 * rho0 / (1024 * (2 : ℝ) ^ J))
    (hcollisionBottom :
      (160 * 2048 : ℝ) * Real.exp Real.pi ≤
        3 * eps ^ 2 * rho0 * P0) :
    (∀ j < J,
      2 * replacementEnergyBoundWide A
          (sliceA2LadderPrimes P0 ratio0 eta j)
          (sliceA2OrdinaryN P0 ratio0 eta j eps rho0) T ≤
        sliceA2KappaReplacement j * bandBudget 1 eps rho) ∧
    (∀ j < J,
      8 * collisionEnergyBoundWide A
          (sliceA2LadderPrimes P0 ratio0 eta j) T ≤
        sliceA2KappaCollision j * bandBudget 1 eps rho) := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  constructor
  · intro j hj
    have hQlast := sliceA2LadderQ_le_last P0 ratio0 eta J j (by omega) hJ hj
    have hcardNat := (sliceA2LadderPrimes_card_le_Q P0 ratio0 eta j).trans hQlast
    have hcard :
        ((sliceA2LadderPrimes P0 ratio0 eta j).card : ℝ) / A ≤
          (sliceA2LadderQ P0 ratio0 eta (J - 1) : ℝ) / A := by
      gcongr
    have hjpow : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ J :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hpow0 : (0 : ℝ) < (2 : ℝ) ^ (j + 1) := by positivity
    have hpowJ0 : (0 : ℝ) < (2 : ℝ) ^ J := by positivity
    have hbudget :
        3 * eps ^ 2 * rho0 / (1024 * (2 : ℝ) ^ J) ≤
          sliceA2KappaReplacement j * eps ^ 2 * rho0 / 16 := by
      unfold sliceA2KappaReplacement ordinaryLegShare
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 1024 * (2 : ℝ) ^ J)
        (by positivity : (0 : ℝ) < 16)]
      field_simp
      have hcoef : 0 < 3 * eps ^ 2 * rho0 := by positivity
      nlinarith
    have hreplacementCard :
        64 * 9 * Real.exp Real.pi *
            (((sliceA2LadderPrimes P0 ratio0 eta j).card : ℝ) / A) ≤
          sliceA2KappaReplacement j * eps ^ 2 * rho0 / 16 := by
      exact (mul_le_mul_of_nonneg_left hcard (by positivity)).trans
        (hcardScale.trans hbudget)
    exact (sliceA2Ordinary_wide_fits P0 ratio0 eta j A eps rho0 rho T hP0
      hA hTA heps hrho0 hratio hreplacementCard
      (sliceA2Ordinary_collision_prime_margin P0 ratio0 eta j eps rho0
        (by omega) heps hrho0 hcollisionBottom)
      (by
        have hsmall : (40 : ℝ) ≤ 64 * 9 := by norm_num
        exact (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hsmall (by positivity))
          (by positivity)).trans hreplacementCard)).1
  · intro j hj
    have hQlast := sliceA2LadderQ_le_last P0 ratio0 eta J j (by omega) hJ hj
    have hcardNat := (sliceA2LadderPrimes_card_le_Q P0 ratio0 eta j).trans hQlast
    have hcard :
        ((sliceA2LadderPrimes P0 ratio0 eta j).card : ℝ) / A ≤
          (sliceA2LadderQ P0 ratio0 eta (J - 1) : ℝ) / A := by
      gcongr
    have hjpow : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ J :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hbudget :
        3 * eps ^ 2 * rho0 / (1024 * (2 : ℝ) ^ J) ≤
          sliceA2KappaCollision j * eps ^ 2 * rho0 / 16 := by
      unfold sliceA2KappaCollision ordinaryLegShare
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 1024 * (2 : ℝ) ^ J)
        (by positivity : (0 : ℝ) < 16)]
      field_simp
      have hcoef : 0 < 3 * eps ^ 2 * rho0 := by positivity
      nlinarith
    have hreplacementCard :
        64 * 9 * Real.exp Real.pi *
            (((sliceA2LadderPrimes P0 ratio0 eta j).card : ℝ) / A) ≤
          sliceA2KappaReplacement j * eps ^ 2 * rho0 / 16 := by
      exact (mul_le_mul_of_nonneg_left hcard (by positivity)).trans
        (hcardScale.trans (by simpa [sliceA2KappaReplacement,
          sliceA2KappaCollision] using hbudget))
    have hcollisionCard :
        40 * Real.exp Real.pi *
            (((sliceA2LadderPrimes P0 ratio0 eta j).card : ℝ) / A) ≤
          sliceA2KappaCollision j * eps ^ 2 * rho0 / 16 := by
      have hsmall : (40 : ℝ) ≤ 64 * 9 := by norm_num
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsmall (by positivity))
        (by positivity)).trans
          (by simpa [sliceA2KappaReplacement, sliceA2KappaCollision]
            using hreplacementCard)
    exact (sliceA2Ordinary_wide_fits P0 ratio0 eta j A eps rho0 rho T hP0
      hA hTA heps hrho0 hratio hreplacementCard
      (sliceA2Ordinary_collision_prime_margin P0 ratio0 eta j eps rho0
        (by omega) heps hrho0 hcollisionBottom)
      hcollisionCard).2

end Tao2015

end MoltResearch
