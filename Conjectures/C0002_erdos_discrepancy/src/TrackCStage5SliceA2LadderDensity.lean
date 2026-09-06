import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2BrunGrowth

/-!
# Track R A2-V'-33: density of the completed ladder

The initial later-level ratio is the ceiling of
`64 exp(12) / min(eps,epsc)`.  Its geometric multiples pay the first eighth
of the positive-ladder density allocation.  The cutoff-growth margins pay
the finite Brun errors with the second eighth.  Combining this quarter with
the endpoint pair's three quarters closes the exact final level list.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- Initial ratio for the positive ordinary ladder. -/
noncomputable def sliceA2LadderEta (eps epsc : ℝ) : ℕ :=
  max 1 ⌈64 * Real.exp 12 / min eps epsc⌉₊

theorem sliceA2LadderEta_one_le (eps epsc : ℝ) :
    1 ≤ sliceA2LadderEta eps epsc := by
  unfold sliceA2LadderEta
  exact le_max_left _ _

/-- The chosen initial ratio pays the geometric Brun main terms. -/
theorem sliceA2LadderEta_brun_budget
    (eps epsc : ℝ) (heps : 0 < eps) (hepsc : 0 < epsc) :
    64 * Real.exp 12 ≤ epsc * sliceA2LadderEta eps epsc := by
  let d := min eps epsc
  have hd : 0 < d := lt_min heps hepsc
  have hceil : 64 * Real.exp 12 / d ≤
      (⌈64 * Real.exp 12 / d⌉₊ : ℝ) := Nat.le_ceil _
  have heta : 64 * Real.exp 12 / d ≤
      (sliceA2LadderEta eps epsc : ℝ) := by
    exact hceil.trans (by
      exact_mod_cast (le_max_right 1 ⌈64 * Real.exp 12 / d⌉₊))
  have hpay : 64 * Real.exp 12 ≤
      d * sliceA2LadderEta eps epsc := by
    have := mul_le_mul_of_nonneg_left heta hd.le
    have hne : d ≠ 0 := ne_of_gt hd
    field_simp at this
    exact this
  have hdeps : d ≤ epsc := min_le_right _ _
  exact hpay.trans (mul_le_mul_of_nonneg_right hdeps (by positivity))

/-- Uniform one-quarter density allocation for all positive ordinary
levels selected at the base scale. -/
theorem exists_sliceA2PositiveLadder_density
    (P0 ratio0 eta : ℕ) (epsc : ℝ)
    (hP0 : 3 ≤ P0) (hepsc : 0 < epsc) (heta1 : 1 ≤ eta)
    (heta : 64 * Real.exp 12 ≤ epsc * eta) :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 → ∀ A : ℕ, A1 ≤ A →
      ladderSiftedLogMass A (2 * A)
          ((List.range
            (sliceA2LadderJ P0 ratio0 eta A1 (by omega) - 1)).map
            (fun i ↦ sliceA2LadderPrimes P0 ratio0 eta (i + 1))) ≤
        (epsc / 4) * ∑ m ∈ Ioc A (2 * A), (1 : ℝ) / m := by
  obtain ⟨A0, hA0⟩ :=
    exists_sliceA2Ladder_brunGrowthMargins P0 ratio0 eta epsc
      (by omega) heta1
  refine ⟨max A0 1, fun A1 hA1 A hAA1 ↦ ?_⟩
  have hA01 : A0 ≤ A1 := (le_max_left A0 1).trans hA1
  have hA1one : 1 ≤ A1 := (le_max_right A0 1).trans hA1
  obtain ⟨hn, hQ, hK, hmargin⟩ := hA0 A1 hA01
  let J := sliceA2LadderJ P0 ratio0 eta A1 (by omega)
  let n := J - 1
  let X := Real.log (A1 : ℝ)
  let y := X ^ (1 / 3 : ℝ)
  have hA : 1 ≤ A := hA1one.trans hAA1
  have hmain := sliceA2PositiveLadder_brun_le_main_add_errors
    P0 ratio0 eta n A epsc hA hP0 hepsc heta
  have herr := sliceA2PositiveLadder_brunErrors_le_eighth
    P0 ratio0 eta n A1 A epsc y hP0 hA1one hAA1 hepsc
      (by dsimp [y]; positivity)
      (by simpa [n, J, y, X] using hn)
      (by simpa [n, J, y, X] using hQ)
      (by simpa [n, J, y, X] using hK)
      (by simpa [n, J, y, X] using hmargin)
  dsimp [n, J] at hmain herr ⊢
  linarith

/-- The exact final level list satisfies its density clause for every large
base scale and every point of the scale window. -/
theorem exists_sliceA2FinalLevels_density
    (P0 eta : ℕ) (epsc : ℝ)
    (hP0 : 3 ≤ P0) (hepsc : 0 < epsc) (heta1 : 1 ≤ eta)
    (heta : 64 * Real.exp 12 ≤ epsc * eta) :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 → ∀ A : ℕ, A1 ≤ A →
      ∑ n ∈ (Ioc A (2 * A)).filter
          (fun n ↦ ¬ HasFactorInAll
            (sliceA2FinalLevels P0 (exceptionalIntervalRatio epsc) eta
              A1 epsc (by omega)) n),
          (1 : ℝ) / n ≤
        epsc * ∑ n ∈ Ioc A (2 * A), (1 : ℝ) / n := by
  obtain ⟨AE, hAE⟩ :=
    exists_sliceA2FinalLevels_density_of_ladder P0 eta epsc hP0 hepsc
  obtain ⟨AL, hAL⟩ :=
    exists_sliceA2PositiveLadder_density P0
      (exceptionalIntervalRatio epsc) eta epsc
      hP0 hepsc heta1 heta
  refine ⟨max AE AL, fun A1 hA1 A hAA1 ↦ ?_⟩
  apply hAE A1 ((le_max_left AE AL).trans hA1) A hAA1
  exact hAL A1 ((le_max_right AE AL).trans hA1) A hAA1

/-- Specialization to the final ratio chosen from both analytic accuracy
parameters. -/
theorem exists_sliceA2FinalLevels_density_chosen
    (P0 : ℕ) (eps epsc : ℝ)
    (hP0 : 3 ≤ P0) (heps : 0 < eps) (hepsc : 0 < epsc) :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 → ∀ A : ℕ, A1 ≤ A →
      ∑ n ∈ (Ioc A (2 * A)).filter
          (fun n ↦ ¬ HasFactorInAll
            (sliceA2FinalLevels P0 (exceptionalIntervalRatio epsc)
              (sliceA2LadderEta eps epsc) A1 epsc (by omega)) n),
          (1 : ℝ) / n ≤
        epsc * ∑ n ∈ Ioc A (2 * A), (1 : ℝ) / n := by
  exact exists_sliceA2FinalLevels_density P0
    (sliceA2LadderEta eps epsc) epsc hP0 hepsc
    (sliceA2LadderEta_one_le eps epsc)
    (sliceA2LadderEta_brun_budget eps epsc heps hepsc)

end Tao2015

end MoltResearch
