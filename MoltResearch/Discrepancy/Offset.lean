import MoltResearch.Discrepancy.Basic

/-!
# Discrepancy: offset sums

Extra lemmas about `apSumOffset` and its relation to differences of `apSum`.
-/

namespace MoltResearch

lemma apSumOffset_eq_sub (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSum f d (m + n) - apSum f d m := by
  have h0 := (apSum_add_length (f := f) (d := d) (m := m) (n := n)).symm
  have h : apSumOffset f d m n + apSum f d m = apSum f d (m + n) := by
    simpa [add_comm] using h0
  exact eq_sub_of_add_eq h

lemma IsSignSequence.natAbs_apSumOffset_le {f : ℕ → ℤ} (hf : IsSignSequence f) (d m n : ℕ) :
    Int.natAbs (apSumOffset f d m n) ≤ n := by
  induction n with
  | zero =>
      simp [apSumOffset]
  | succ n ih =>
      have hsucc := (apSumOffset_succ (f := f) (d := d) (m := m) (n := n))
      have hsucc_natAbs :
          Int.natAbs (apSumOffset f d m (Nat.succ n)) =
            Int.natAbs (apSumOffset f d m n + f ((m + n + 1) * d)) := by
        simpa [Nat.succ_eq_add_one] using congrArg Int.natAbs hsucc
      calc
        Int.natAbs (apSumOffset f d m (Nat.succ n))
            = Int.natAbs (apSumOffset f d m n + f ((m + n + 1) * d)) := by
              simpa using hsucc_natAbs
        _ ≤ Int.natAbs (apSumOffset f d m n) + Int.natAbs (f ((m + n + 1) * d)) := by
              simpa using Int.natAbs_add_le (apSumOffset f d m n) (f ((m + n + 1) * d))
        _ ≤ n + 1 := by
              have h1 := ih
              have h2 : Int.natAbs (f ((m + n + 1) * d)) = 1 := by
                simpa using hf.natAbs_eq_one (n := (m + n + 1) * d)
              have h3 := add_le_add_right h1 (Int.natAbs (f ((m + n + 1) * d)))
              simpa [h2] using h3
        _ = Nat.succ n := rfl

lemma IsSignSequence.natAbs_apSum_sub_le {f : ℕ → ℤ} (hf : IsSignSequence f) (d m n : ℕ) :
    Int.natAbs (apSum f d (m + n) - apSum f d m) ≤ n := by
  have h := hf.natAbs_apSumOffset_le (d := d) (m := m) (n := n)
  simpa [apSumOffset_eq_sub (f := f) (d := d) (m := m) (n := n)] using h

end MoltResearch
