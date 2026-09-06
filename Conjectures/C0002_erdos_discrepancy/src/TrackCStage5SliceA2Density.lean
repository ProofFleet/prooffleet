import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2SmallBudget

/-!
# Track R A2-V'-6: density assembly for the final level list

The bottom and exceptional levels are priced together by the window
Turán--Kubilius estimate.  The intervening ladder is appended afterwards and
is priced by its Brun sifted logarithmic mass.  This is the density analogue
of the low-band split used by the mean-square argument.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The logarithmic mass of integers missing a factor in at least one ladder
level is at most the sum of the individual sifted logarithmic masses. -/
theorem missingFactorInSome_logMass_le_ladderSiftedLogMass
    (a b : ℕ) (ladder : List (Finset ℕ)) :
    ∑ n ∈ (Ioc a b).filter (MissingFactorInSome ladder), (1 : ℝ) / n ≤
      ladderSiftedLogMass a b ladder := by
  classical
  unfold ladderSiftedLogMass
  calc
    ∑ n ∈ (Ioc a b).filter (MissingFactorInSome ladder), (1 : ℝ) / n =
        ∑ n ∈ Ioc a b,
          if MissingFactorInSome ladder n then (1 : ℝ) / n else 0 := by
            rw [sum_filter]
    _ ≤ ∑ n ∈ Ioc a b,
        ∑ L ∈ ladder.toFinset,
          if (∀ p ∈ L, ¬ p ∣ n) then (1 : ℝ) / n else 0 := by
      apply sum_le_sum
      intro n hn
      by_cases hmissing : MissingFactorInSome ladder n
      · rcases hmissing with ⟨L, hL, hno⟩
        rw [if_pos ⟨L, hL, hno⟩]
        have hsingle := Finset.single_le_sum
          (s := ladder.toFinset)
          (f := fun L => if (∀ p ∈ L, ¬ p ∣ n) then (1 : ℝ) / n else 0)
          (fun L _ => by positivity) (by simpa using hL)
        dsimp only at hsingle
        rw [if_pos hno] at hsingle
        exact hsingle
      · rw [if_neg hmissing]
        positivity
    _ = ∑ L ∈ ladder.toFinset,
        ∑ n ∈ Ioc a b,
          if (∀ p ∈ L, ¬ p ∣ n) then (1 : ℝ) / n else 0 := by
      rw [sum_comm]
    _ = ∑ L ∈ ladder.toFinset,
        ∑ n ∈ (Ioc a b).filter (fun n => ∀ p ∈ L, ¬ p ∣ n),
          (1 : ℝ) / n := by
      apply sum_congr rfl
      intro L hL
      rw [sum_filter]

/-- Appending the ordinary ladder costs only its sifted logarithmic mass in
the typical-set complement. -/
theorem typicalS_complement_append_le
    (a b : ℕ) (base ladder : List (Finset ℕ)) :
    ∑ n ∈ (Ioc a b).filter
        (fun n => ¬ HasFactorInAll (base ++ ladder) n), (1 : ℝ) / n ≤
      ∑ n ∈ (Ioc a b).filter
          (fun n => ¬ HasFactorInAll base n), (1 : ℝ) / n +
        ladderSiftedLogMass a b ladder := by
  classical
  let fullBad := (Ioc a b).filter
    (fun n => ¬ HasFactorInAll (base ++ ladder) n)
  let baseBad := (Ioc a b).filter
    (fun n => ¬ HasFactorInAll base n)
  let ladderBad := (Ioc a b).filter (MissingFactorInSome ladder)
  have hsub : fullBad ⊆ baseBad ∪ ladderBad := by
    intro n hn
    rw [mem_union]
    simp only [fullBad, baseBad, ladderBad, mem_filter] at hn ⊢
    have hnot : ¬ (HasFactorInAll base n ∧ HasFactorInAll ladder n) := by
      simpa only [hasFactorInAll_append] using hn.2
    rcases not_and_or.mp hnot with hbase | hladder
    · exact Or.inl ⟨hn.1, hbase⟩
    · exact Or.inr ⟨hn.1,
        not_hasFactorInAll_iff_missingFactorInSome ladder n |>.mp hladder⟩
  have hmono :
      ∑ n ∈ fullBad, (1 : ℝ) / n ≤
        ∑ n ∈ baseBad ∪ ladderBad, (1 : ℝ) / n := by
    exact sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
  have hunion :
      ∑ n ∈ baseBad ∪ ladderBad, (1 : ℝ) / n ≤
        (∑ n ∈ baseBad, (1 : ℝ) / n) +
          ∑ n ∈ ladderBad, (1 : ℝ) / n := by
    have hui := Finset.sum_union_inter
      (s₁ := baseBad) (s₂ := ladderBad) (f := fun n => (1 : ℝ) / n)
    have hint : (0 : ℝ) ≤
        ∑ n ∈ baseBad ∩ ladderBad, (1 : ℝ) / n :=
      Finset.sum_nonneg fun n _ => by positivity
    linarith
  calc
    ∑ n ∈ (Ioc a b).filter
        (fun n => ¬ HasFactorInAll (base ++ ladder) n), (1 : ℝ) / n =
        ∑ n ∈ fullBad, (1 : ℝ) / n := rfl
    _ ≤ ∑ n ∈ baseBad ∪ ladderBad, (1 : ℝ) / n := hmono
    _ ≤ (∑ n ∈ baseBad, (1 : ℝ) / n) +
        ∑ n ∈ ladderBad, (1 : ℝ) / n := hunion
    _ ≤ (∑ n ∈ baseBad, (1 : ℝ) / n) +
        ladderSiftedLogMass a b ladder := by
      gcongr
      exact missingFactorInSome_logMass_le_ladderSiftedLogMass a b ladder
    _ = ∑ n ∈ (Ioc a b).filter
          (fun n => ¬ HasFactorInAll base n), (1 : ℝ) / n +
        ladderSiftedLogMass a b ladder := rfl

/-- Two separately normalized density estimates add after the level-list
split. -/
theorem typicalS_complement_append_le_of_bounds
    (a b : ℕ) (base ladder : List (Finset ℕ))
    (epsBase epsLadder H : ℝ)
    (hbase : ∑ n ∈ (Ioc a b).filter
        (fun n => ¬ HasFactorInAll base n), (1 : ℝ) / n ≤ epsBase * H)
    (hladder : ladderSiftedLogMass a b ladder ≤ epsLadder * H) :
    ∑ n ∈ (Ioc a b).filter
        (fun n => ¬ HasFactorInAll (base ++ ladder) n), (1 : ℝ) / n ≤
      (epsBase + epsLadder) * H := by
  calc
    ∑ n ∈ (Ioc a b).filter
        (fun n => ¬ HasFactorInAll (base ++ ladder) n), (1 : ℝ) / n ≤
      ∑ n ∈ (Ioc a b).filter
          (fun n => ¬ HasFactorInAll base n), (1 : ℝ) / n +
        ladderSiftedLogMass a b ladder :=
      typicalS_complement_append_le a b base ladder
    _ ≤ epsBase * H + epsLadder * H := add_le_add hbase hladder
    _ = (epsBase + epsLadder) * H := by ring

/-- The density expression is invariant under permuting the level list. -/
theorem typicalS_complement_sum_perm
    (a b : ℕ) {levels levels' : List (Finset ℕ)}
    (hperm : levels.Perm levels') :
    ∑ n ∈ (Ioc a b).filter
        (fun n => ¬ HasFactorInAll levels n), (1 : ℝ) / n =
      ∑ n ∈ (Ioc a b).filter
        (fun n => ¬ HasFactorInAll levels' n), (1 : ℝ) / n := by
  apply sum_congr
  · ext n
    simp only [mem_filter, mem_Ioc]
    rw [hasFactorInAll_of_perm hperm]
  · intro n hn
    rfl

end Tao2015

end MoltResearch
