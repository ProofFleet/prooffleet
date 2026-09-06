import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5BandEnergyExceptional
import MoltResearch.Discrepancy.ExceptionalCellCover

/-!
# Track C Stage 5 — the exceptional-frequency re-cut

The old exceptional assembly eliminates the large prime-polynomial set with a
first-moment count, introducing a term of size `T/P`.  The re-cut below keeps
the prime large-values theorem in its native cardinality form and substitutes
the free high-moment count only afterwards.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The fixed threshold used for the large/small split in Phase 0. -/
noncomputable def exceptionalSplitThreshold (A : ℕ) : ℝ :=
  1 / Real.log A ^ 100

/-- The fixed exceptional split threshold is positive above `1`. -/
theorem exceptionalSplitThreshold_pos (A : ℕ) (hA : 1 < A) :
    0 < exceptionalSplitThreshold A := by
  unfold exceptionalSplitThreshold
  have hlog : 0 < Real.log (A : ℝ) := Real.log_pos (by exact_mod_cast hA)
  exact one_div_pos.mpr (pow_pos hlog _)

/-- The explicit high-moment upper bound for the number of large values. -/
noncomputable def primeHighMomentCountCost (P ell : ℕ) (Y : Finset ℕ)
    (T V lam : ℝ) : ℝ :=
  (Real.exp Real.pi
      * ((T + 1) / ((P ^ ell : ℕ) : ℝ) + 2 * ((2 ^ ell : ℕ) : ℝ))
    * ((Nat.factorial ell : ℝ) ^ 2
        * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ)) ^ ell)
    * ((1 + lam) + (1 / lam)
        * (2 * Real.pi * Real.log ((2 * P) ^ ell)) ^ 2)) / V ^ (2 * ell)

/-- **Phase 0 VI-9d — the discrete large/small split with an externally
counted large set.**

Unlike the old cardinality-free wrapper, the prime term contains `CL` directly;
there is no mean-value term `T/P`. -/
theorem sum_prime_integer_energy_large_card_le [HalaszLargeValuesAssumption]
    [PrimeLargeValuesAssumption]
    (P : ℕ) (hP : 2 ≤ P) (Y : Finset ℕ) (hY : ∀ p ∈ Y, p.Prime)
    (hYP : ∀ p ∈ Y, P ≤ p ∧ p ≤ 2 * P) (b : ℕ → ℂ)
    (N : ℕ) (a : ℕ → ℂ)
    (T : ℝ) (hT : 1 ≤ T) (points : Finset ℝ)
    (hmem : ∀ t ∈ points, |t| ≤ T)
    (hsep : ∀ t ∈ points, ∀ u ∈ points, t ≠ u → 1 ≤ |t - u|)
    (V₀ delta CL : ℝ) (hV₀ : 0 ≤ V₀)
    (hlarge : ∀ t ∈ points.filter (fun t =>
      V₀ < ‖∑ p ∈ Y, (b p / (p : ℂ))
        * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖),
      ‖∑ n ∈ Finset.Icc 1 N, (a n / (n : ℂ))
        * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ delta)
    (hcard : ((points.filter (fun t =>
      V₀ < ‖∑ p ∈ Y, (b p / (p : ℂ))
        * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖)).card : ℝ) ≤ CL) :
    ∑ t ∈ points, ‖∑ p ∈ Y, (b p / (p : ℂ))
          * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖ ^ 2
        * ‖∑ n ∈ Finset.Icc 1 N, (a n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ^ 2
      ≤ V₀ ^ 2 * (64 * ((N : ℝ) + (points.card : ℝ) * Real.sqrt T)
            * (Real.log (2 * T) + 1)
            * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2)
        + delta ^ 2 * (64 * (1 + CL
              * Real.exp (-(Real.log P / (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
              * (Real.log (2 * T)) ^ 2)
            * (∑ p ∈ Y, ‖b p‖ ^ 2 / (p : ℝ) ^ 2)
            * (P : ℝ) / Real.log P) := by
  have hbase := sum_prime_integer_energy_le P hP Y hY hYP b N a T hT
    points hmem hsep V₀ delta hV₀ hlarge
  have hlogP : 0 < Real.log (P : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hP))
  have hcoef : 0 ≤ ∑ p ∈ Y, ‖b p‖ ^ 2 / (p : ℝ) ^ 2 :=
    Finset.sum_nonneg fun p _ => by positivity
  refine hbase.trans ?_
  gcongr

-- The expanded high-moment count and the conditional energy bound are both
-- substantial terms, but their composition has no unbounded search.
set_option maxHeartbeats 800000 in
/-- **Phase 0 VI-9d — the `𝒯_S/𝒯_L` split with `𝒯_L` counted at moment
`ell`.**

The only occurrence of the prime scale outside the prime large-values saving is
inside `primeHighMomentCountCost`; in particular the prime term has no `T/P`
summand forced by a first-moment count. -/
theorem sum_prime_integer_energy_high_moment_le [HalaszLargeValuesAssumption]
    [PrimeLargeValuesAssumption]
    (P : ℕ) (hP : 2 ≤ P) (Y : Finset ℕ) (hY : ∀ p ∈ Y, p.Prime)
    (hlo : ∀ p ∈ Y, P < p) (hhi : ∀ p ∈ Y, p ≤ 2 * P)
    (b : ℕ → ℂ) (hb : ∀ p, ‖b p‖ ≤ 1)
    (ell : ℕ) (hell : 1 ≤ ell)
    (N : ℕ) (a : ℕ → ℂ)
    (T : ℝ) (hT : 1 ≤ T) (points : Finset ℝ)
    (hmem : ∀ t ∈ points, |t| ≤ T)
    (hsep : ∀ t ∈ points, ∀ u ∈ points, t ≠ u → 1 ≤ |t - u|)
    (V₀ delta lam : ℝ) (hV₀ : 0 < V₀) (hlam : 0 < lam)
    (hlarge : ∀ t ∈ points.filter (fun t =>
      V₀ < ‖∑ p ∈ Y, (b p / (p : ℂ))
        * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖),
      ‖∑ n ∈ Finset.Icc 1 N, (a n / (n : ℂ))
        * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ delta) :
    ∑ t ∈ points, ‖∑ p ∈ Y, (b p / (p : ℂ))
          * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖ ^ 2
        * ‖∑ n ∈ Finset.Icc 1 N, (a n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ^ 2
      ≤ V₀ ^ 2 * (64 * ((N : ℝ) + (points.card : ℝ) * Real.sqrt T)
            * (Real.log (2 * T) + 1)
            * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2)
        + delta ^ 2 * (64 * (1 + primeHighMomentCountCost P ell Y T V₀ lam
              * Real.exp (-(Real.log P / (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
              * (Real.log (2 * T)) ^ 2)
            * (∑ p ∈ Y, ‖b p‖ ^ 2 / (p : ℝ) ^ 2)
            * (P : ℝ) / Real.log P) := by
  let pointsL := points.filter (fun t =>
    V₀ < ‖∑ p ∈ Y, (b p / (p : ℂ))
      * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖)
  have hsub : pointsL ⊆ points := by
    dsimp [pointsL]
    exact Finset.filter_subset _ _
  have hmemL : ∀ t ∈ pointsL, t ∈ Set.Icc (-T) T := by
    intro t ht
    exact Set.mem_Icc.mpr (abs_le.mp (hmem t (hsub ht)))
  have hsepL : ∀ t ∈ pointsL, ∀ u ∈ pointsL, t ≠ u → 1 ≤ |t - u| :=
    fun t ht u hu => hsep t (hsub ht) u (hsub hu)
  have hlargeL : ∀ t ∈ pointsL, V₀ ≤ ‖∑ p ∈ Y, (b p / (p : ℂ))
      * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖ := by
    intro t ht
    exact (Finset.mem_filter.mp ht).2.le
  have hmoment := card_large_prime_poly_pow_le Y hY P (by omega) hlo hhi b hb
    ell hell pointsL T V₀ lam (zero_le_one.trans hT) hV₀.le hlam hmemL hsepL hlargeL
  have hpowV : 0 < V₀ ^ (2 * ell) := pow_pos hV₀ _
  have hcardL : (pointsL.card : ℝ) ≤ primeHighMomentCountCost P ell Y T V₀ lam := by
    unfold primeHighMomentCountCost
    rw [le_div_iff₀ hpowV]
    exact hmoment
  apply sum_prime_integer_energy_large_card_le P hP Y hY
    (fun p hp => ⟨(hlo p hp).le, hhi p hp⟩) b N a T hT points hmem hsep
    V₀ delta (primeHighMomentCountCost P ell Y T V₀ lam) hV₀.le hlarge
  simpa [pointsL] using hcardL

end Tao2015

end MoltResearch
