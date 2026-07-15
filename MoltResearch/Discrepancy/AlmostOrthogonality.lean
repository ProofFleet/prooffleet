import MoltResearch.Discrepancy.PerfectCancellation
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Discrepancy: almost orthogonality of divisor-cutoff character windows

Endgame step for the Tao 2015 §4 analysis (arXiv:1509.05363,
`Problems/tao2015_derivation_c.md`, issue #2871): the exact expansion of the windowed
second moment of a divisor-cutoff combination, eq. (stop-2) → eq. (tex).

* `charCutoff χ d n = 1_{d ∣ n}·χ(n/d)` is the Granville cutoff of the §4 endgame.
* `norm_charCutoff_le`: cutoffs are `1`-bounded.
* `sum_normSq_window_charCutoff_comb`: for a *primitive* `χ` mod `q > 1` and any
  divisor-indexed coefficients `c`, over a full period `a ∈ [0, q^k)`,

  `∑_a ‖∑_{m ≤ H'} ∑_{d ∣ q^{k−1}} c(d)·charCutoff χ d (a+m)‖²
     = ∑_{d ∣ q^{k−1}} ‖c(d)‖² · ∑_a ‖∑_{m ≤ H'} charCutoff χ d (a+m)‖²`

  — expanding the square, every cross term `d₁ ≠ d₂` dies by the perfect cancellation
  eq. (perf) (`sum_indicator_char_mul_conj_eq_zero`), leaving the diagonal.

In the endgame the coefficients are `c(d) = χ̃(d)` (unimodular, so `‖c(d)‖² = 1`), the
left side is the good-residue window moment of `χ̃` up to reinstated bad residues, and
the right side is bounded below by the pure-scale terms `d = qⁱ`.
-/

namespace MoltResearch

open Finset

variable {q : ℕ} {χ : DirichletCharacter ℂ q}

/-- The Granville divisor cutoff `1_{d ∣ n}·χ(n/d)` (Tao 2015 §4). -/
noncomputable def charCutoff (χ : DirichletCharacter ℂ q) (d n : ℕ) : ℂ :=
  if d ∣ n then χ ((n / d : ℕ) : ZMod q) else 0

theorem charCutoff_of_dvd {d n : ℕ} (h : d ∣ n) :
    charCutoff χ d n = χ ((n / d : ℕ) : ZMod q) := if_pos h

theorem charCutoff_of_not_dvd {d n : ℕ} (h : ¬ d ∣ n) : charCutoff χ d n = 0 := if_neg h

/-- Cutoffs are `1`-bounded (Dirichlet-character values have norm at most `1`). -/
theorem norm_charCutoff_le (d n : ℕ) : ‖charCutoff χ d n‖ ≤ 1 := by
  unfold charCutoff
  split
  · exact DirichletCharacter.norm_le_one χ _
  · rw [norm_zero]; exact zero_le_one

/-- Cast a sum of squared norms into the complex `z·conj z` form. -/
private lemma ofReal_sum_normSq (s : Finset ℕ) (f : ℕ → ℂ) :
    ((∑ a ∈ s, ‖f a‖ ^ 2 : ℝ) : ℂ) = ∑ a ∈ s, f a * (starRingEnd ℂ) (f a) := by
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- **Almost orthogonality / diagonal expansion** (Tao 2015 §4, eq. (stop-2) → (tex)):
for a primitive Dirichlet character `χ` mod `q > 1` and arbitrary coefficients `c` on the
divisors of `q^{k−1}`, the windowed second moment of the combination
`n ↦ ∑_{d ∣ q^{k−1}} c(d)·1_{d ∣ n}·χ(n/d)` over a full period splits exactly into its
diagonal: every cross pair `d₁ ≠ d₂` cancels perfectly (eq. (perf)). -/
theorem sum_normSq_window_charCutoff_comb {k : ℕ} (hq : 1 < q) (hk : 1 ≤ k)
    (hχ : χ.IsPrimitive) (c : ℕ → ℂ) (H' : ℕ) :
    ∑ a ∈ Finset.range (q ^ k),
        ‖∑ m ∈ Finset.Icc 1 H',
            ∑ d ∈ (q ^ (k - 1)).divisors, c d * charCutoff χ d (a + m)‖ ^ 2
      = ∑ d ∈ (q ^ (k - 1)).divisors, ‖c d‖ ^ 2
          * ∑ a ∈ Finset.range (q ^ k),
              ‖∑ m ∈ Finset.Icc 1 H', charCutoff χ d (a + m)‖ ^ 2 := by
  -- pass to `ℂ` where conjugate expansion is available
  apply Complex.ofReal_injective
  -- window sums for a fixed divisor
  set W : ℕ → ℕ → ℂ := fun d a => ∑ m ∈ Finset.Icc 1 H', charCutoff χ d (a + m) with hW
  -- the combined window is the `c`-combination of the `W d`
  have hS : ∀ a : ℕ,
      (∑ m ∈ Finset.Icc 1 H',
          ∑ d ∈ (q ^ (k - 1)).divisors, c d * charCutoff χ d (a + m))
        = ∑ d ∈ (q ^ (k - 1)).divisors, c d * W d a := by
    intro a
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => (Finset.mul_sum _ _ _).symm
  -- cross terms vanish: eq. (perf) summed over the window pairs
  have hcross : ∀ d₁ ∈ (q ^ (k - 1)).divisors, ∀ d₂ ∈ (q ^ (k - 1)).divisors, d₁ ≠ d₂ →
      ∑ a ∈ Finset.range (q ^ k), W d₁ a * (starRingEnd ℂ) (W d₂ a) = 0 := by
    intro d₁ hd₁ d₂ hd₂ hne
    have h₁ : d₁ ∣ q ^ (k - 1) := (Nat.mem_divisors.mp hd₁).1
    have h₂ : d₂ ∣ q ^ (k - 1) := (Nat.mem_divisors.mp hd₂).1
    have hterm : ∀ a : ℕ, W d₁ a * (starRingEnd ℂ) (W d₂ a)
        = ∑ m₁ ∈ Finset.Icc 1 H', ∑ m₂ ∈ Finset.Icc 1 H',
            charCutoff χ d₁ (a + m₁) * (starRingEnd ℂ) (charCutoff χ d₂ (a + m₂)) := by
      intro a
      rw [hW]
      simp only [map_sum]
      rw [Finset.sum_mul_sum]
    calc ∑ a ∈ Finset.range (q ^ k), W d₁ a * (starRingEnd ℂ) (W d₂ a)
        = ∑ a ∈ Finset.range (q ^ k), ∑ m₁ ∈ Finset.Icc 1 H', ∑ m₂ ∈ Finset.Icc 1 H',
            charCutoff χ d₁ (a + m₁) * (starRingEnd ℂ) (charCutoff χ d₂ (a + m₂)) :=
          Finset.sum_congr rfl fun a _ => hterm a
      _ = ∑ m₁ ∈ Finset.Icc 1 H', ∑ m₂ ∈ Finset.Icc 1 H',
            ∑ a ∈ Finset.range (q ^ k),
              charCutoff χ d₁ (a + m₁) * (starRingEnd ℂ) (charCutoff χ d₂ (a + m₂)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun m₁ _ => Finset.sum_comm
      _ = 0 := by
          refine Finset.sum_eq_zero fun m₁ _ => Finset.sum_eq_zero fun m₂ _ => ?_
          simpa [charCutoff] using
            sum_indicator_char_mul_conj_eq_zero hq hk hχ h₁ h₂ hne m₁ m₂
  -- expand both sides into `z·conj z` form and compare
  rw [ofReal_sum_normSq]
  -- right-hand side: push the cast through the divisor sum
  have hRHS : ((∑ d ∈ (q ^ (k - 1)).divisors, ‖c d‖ ^ 2
        * ∑ a ∈ Finset.range (q ^ k),
            ‖∑ m ∈ Finset.Icc 1 H', charCutoff χ d (a + m)‖ ^ 2 : ℝ) : ℂ)
      = ∑ d ∈ (q ^ (k - 1)).divisors, (c d * (starRingEnd ℂ) (c d))
          * ∑ a ∈ Finset.range (q ^ k), W d a * (starRingEnd ℂ) (W d a) := by
    push_cast
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← ofReal_sum_normSq (Finset.range (q ^ k)) (W d)]
    have hc : ((‖c d‖ : ℂ)) ^ 2 = c d * (starRingEnd ℂ) (c d) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [← hc]
    push_cast
    ring
  rw [hRHS]
  -- main computation in `ℂ`
  calc ∑ a ∈ Finset.range (q ^ k),
        (∑ m ∈ Finset.Icc 1 H',
            ∑ d ∈ (q ^ (k - 1)).divisors, c d * charCutoff χ d (a + m))
          * (starRingEnd ℂ)
              (∑ m ∈ Finset.Icc 1 H',
                ∑ d ∈ (q ^ (k - 1)).divisors, c d * charCutoff χ d (a + m))
      = ∑ a ∈ Finset.range (q ^ k),
          ∑ d₁ ∈ (q ^ (k - 1)).divisors, ∑ d₂ ∈ (q ^ (k - 1)).divisors,
            (c d₁ * (starRingEnd ℂ) (c d₂)) * (W d₁ a * (starRingEnd ℂ) (W d₂ a)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hS a]
        simp only [map_sum, map_mul]
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => by ring
    _ = ∑ d₁ ∈ (q ^ (k - 1)).divisors, ∑ d₂ ∈ (q ^ (k - 1)).divisors,
          (c d₁ * (starRingEnd ℂ) (c d₂))
            * ∑ a ∈ Finset.range (q ^ k), W d₁ a * (starRingEnd ℂ) (W d₂ a) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d₁ _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun d₂ _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ d ∈ (q ^ (k - 1)).divisors, (c d * (starRingEnd ℂ) (c d))
          * ∑ a ∈ Finset.range (q ^ k), W d a * (starRingEnd ℂ) (W d a) := by
        refine Finset.sum_congr rfl fun d₁ hd₁ => ?_
        rw [Finset.sum_eq_single_of_mem d₁ hd₁]
        intro d₂ hd₂ hne
        rw [hcross d₁ hd₁ d₂ hd₂ (Ne.symm hne), mul_zero]

end MoltResearch
