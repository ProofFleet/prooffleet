import MoltResearch.Discrepancy.BrunIntervalSieve

/-!
# Upstreaming slot UP-5: Brun's pure sieve on an interval

Pre-allocated leaf for card item UP-5 of `Problems/nucleus_upstreaming.md`. The claimant of UP-5 fills this file with
the Mathlib-style restatement, proved from the imported tree lemmas; no other file is to be edited.
-/

namespace MoltResearch

namespace Upstream

/-- Brun's pure upper-bound sieve on a finite interval.  This is the
Bonferroni-truncation form introduced in V. Brun, *Über das Goldbachsche
Gesetz und die Anzahl der Primzahlpaare* (1915). -/
theorem brun_sieve_card_Ioc_le (a b : ℕ) (hab : a ≤ b)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (k : ℕ) :
    ((((Finset.Ioc a b).filter (fun m => ∀ p ∈ P, ¬ p ∣ m)).card : ℝ) ≤
      ((b : ℝ) - a) *
        ((∏ p ∈ P, (1 - 1 / (p : ℝ))) +
          (∑ p ∈ P, (1 : ℝ) / p) ^ (2 * k + 1) /
            ((2 * k + 1).factorial : ℝ)) +
        ((P.card : ℝ) + 1) ^ (2 * k)) := by
  exact card_no_factor_Ioc_le_brun a b hab P hP k

/-- The logarithmic-mass corollary of Brun's pure interval sieve: on
`(a, b]`, replace every reciprocal by its upper bound `1 / a`.  The sieve
input is Brun's 1915 Bonferroni method cited above. -/
theorem brun_sieve_sum_one_div_Ioc_le (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (k : ℕ) :
    (∑ m ∈ (Finset.Ioc a b).filter (fun m => ∀ p ∈ P, ¬ p ∣ m),
        (1 : ℝ) / m) ≤
      (1 / (a : ℝ)) *
        (((b : ℝ) - a) *
          ((∏ p ∈ P, (1 - 1 / (p : ℝ))) +
            (∑ p ∈ P, (1 : ℝ) / p) ^ (2 * k + 1) /
              ((2 * k + 1).factorial : ℝ)) +
          ((P.card : ℝ) + 1) ^ (2 * k)) := by
  exact sum_one_div_no_factor_Ioc_le_brun a b ha hab P hP k

/-- The two upstream-facing bounds can be used together with the same
finite prime set and truncation depth. -/
example (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (k : ℕ) :
    let B := ((b : ℝ) - a) *
        ((∏ p ∈ P, (1 - 1 / (p : ℝ))) +
          (∑ p ∈ P, (1 : ℝ) / p) ^ (2 * k + 1) /
            ((2 * k + 1).factorial : ℝ)) +
        ((P.card : ℝ) + 1) ^ (2 * k)
    ((((Finset.Ioc a b).filter (fun m => ∀ p ∈ P, ¬ p ∣ m)).card : ℝ) ≤ B) ∧
      (∑ m ∈ (Finset.Ioc a b).filter (fun m => ∀ p ∈ P, ¬ p ∣ m),
        (1 : ℝ) / m) ≤ (1 / (a : ℝ)) * B := by
  exact ⟨brun_sieve_card_Ioc_le a b hab P hP k,
    brun_sieve_sum_one_div_Ioc_le a b ha hab P hP k⟩

end Upstream

end MoltResearch
