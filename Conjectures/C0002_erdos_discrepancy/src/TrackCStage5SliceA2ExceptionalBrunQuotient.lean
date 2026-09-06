import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalLadderBudget

/-!
# Track R A2-V': Brun remainder on quotient intervals

Natural-number division can extend `(A/q,(A+Delta)/q]` one point beyond
the dyadic interval.  This leaf isolates that rounding point and keeps its
cost explicit.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- Extending a dyadic sifted interval by its next endpoint costs at most
one reciprocal endpoint for each level in the list. -/
theorem ladderSiftedLogMass_dyadic_add_one
    (a n : ℕ) (L : ℕ → Finset ℕ) (ha : 1 ≤ a) :
    ladderSiftedLogMass a (2 * a + 1) ((List.range n).map L) ≤
      ladderSiftedLogMass a (2 * a) ((List.range n).map L) +
        (n : ℝ) / (2 * a + 1 : ℕ) := by
  classical
  let ladder := (List.range n).map L
  have hpoint : ∀ P ∈ ladder.toFinset,
      (∑ m ∈ (Ioc a (2 * a + 1)).filter (fun m => ∀ p ∈ P, ¬p ∣ m),
          (1 : ℝ) / m) ≤
        (∑ m ∈ (Ioc a (2 * a)).filter (fun m => ∀ p ∈ P, ¬p ∣ m),
          (1 : ℝ) / m) + 1 / (2 * a + 1 : ℕ) := by
    intro P hP
    have hle : a ≤ 2 * a := by omega
    rw [← Finset.insert_Ioc_right_eq_Ioc_add_one hle, Finset.filter_insert]
    split_ifs with hpred
    · have hnot : 2 * a + 1 ∉
          (Ioc a (2 * a)).filter (fun m => ∀ p ∈ P, ¬p ∣ m) := by simp
      rw [Finset.sum_insert hnot]
      rw [add_comm]
    · have hnonneg : 0 ≤ (1 : ℝ) / (2 * a + 1 : ℕ) := by positivity
      linarith
  unfold ladderSiftedLogMass
  change (∑ P ∈ ladder.toFinset,
      ∑ m ∈ (Ioc a (2 * a + 1)).filter (fun m => ∀ p ∈ P, ¬p ∣ m),
        (1 : ℝ) / m) ≤ _
  calc
    _ ≤ ∑ P ∈ ladder.toFinset,
        ((∑ m ∈ (Ioc a (2 * a)).filter (fun m => ∀ p ∈ P, ¬p ∣ m),
            (1 : ℝ) / m) + 1 / (2 * a + 1 : ℕ)) := by
      exact Finset.sum_le_sum fun P hP => hpoint P hP
    _ = (∑ P ∈ ladder.toFinset,
          ∑ m ∈ (Ioc a (2 * a)).filter (fun m => ∀ p ∈ P, ¬p ∣ m),
            (1 : ℝ) / m) +
        (ladder.toFinset.card : ℝ) / (2 * a + 1 : ℕ) := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul]
      ring
    _ ≤ (∑ P ∈ ladder.toFinset,
          ∑ m ∈ (Ioc a (2 * a)).filter (fun m => ∀ p ∈ P, ¬p ∣ m),
            (1 : ℝ) / m) +
        (n : ℝ) / (2 * a + 1 : ℕ) := by
      gcongr
      exact_mod_cast (ladder.toFinset_card_le.trans (by simp [ladder]))
    _ = _ := by rfl

/-- The quotient endpoint is contained in the dyadic interval with its one
rounding point. -/
theorem ladderSiftedLogMass_quotient_le_dyadic_add_one
    (A Delta q n : ℕ) (L : ℕ → Finset ℕ)
    (hq : 0 < q) (hDelta : Delta ≤ A) :
    ladderSiftedLogMass (A / q) ((A + Delta) / q)
        ((List.range n).map L) ≤
      ladderSiftedLogMass (A / q) (2 * (A / q) + 1)
        ((List.range n).map L) := by
  apply ladderSiftedLogMass_mono_right
  exact div_le_two_mul_div_add_one A (A + Delta) q hq (by omega)

end Tao2015

end MoltResearch
