import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Totient

/-!
# Discrepancy: linear growth of the windowed character second moment

Endgame-counting step for the Tao 2015 §4 analysis (arXiv:1509.05363,
`Problems/tao2015_derivation_c.md`, issue #2908): the windowed second moment of a
Dirichlet character mod `q` grows linearly,

`φ(q)·⌊N/q⌋ ≤ ∑_{b ∈ [1,N]} ‖χ(b)‖²` (`totient_mul_le_sum_normSq_dirichletChar`).

Route: `‖χ(b)‖² = 1` when `b` is a unit mod `q` (`DirichletCharacter.unit_norm_eq_one`)
and `= 0` otherwise (`MulChar.map_nonunit`), so the sum dominates the count of `b ≤ N`
coprime to `q`.  Each of the `⌊N/q⌋` full blocks of `q` consecutive integers contains
exactly `φ(q)` such `b` (`Nat.filter_coprime_Ico_eq_totient`).

No `NeZero q` hypothesis is needed: for `q = 0` both `φ(0) = 0` and the claim is trivial.

Consumer: the Borwein–Choi–Coons endgame's counting contradiction — the final step
`∑_{i : q^i < √H} q^i · ∑_{b ≤ q^{k-i}/4} ‖χ(b)‖² ≪ q^k` needs
`∑_{b ≤ M} ‖χ(b)‖² ≥ (φ(q)/q)·M` up to an additive block, which is this bound at
`M = q·⌊N/q⌋`.

This module is deliberately dependency-light: it imports only Mathlib (no MoltResearch
modules), and is intended to be used via the stable surface `MoltResearch.Discrepancy`.
-/

namespace MoltResearch

open Finset

/-- Each window `[1, q·T]` of `T` full blocks contains exactly `φ(q)·T` integers coprime
to `q`, in indicator-sum form. -/
private lemma sum_coprime_indicator_Ico_eq (q T : ℕ) :
    ∑ b ∈ Finset.Ico 1 (1 + q * T), (if q.Coprime b then (1 : ℝ) else 0)
      = (q.totient : ℝ) * (T : ℝ) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have h1 : (1 : ℕ) ≤ 1 + q * T := by omega
    have h2 : 1 + q * T ≤ 1 + q * (T + 1) := by
      have : q * T ≤ q * (T + 1) := Nat.mul_le_mul_left q (by omega)
      omega
    rw [← Finset.sum_Ico_consecutive _ h1 h2, ih]
    have hblock : ∑ b ∈ Finset.Ico (1 + q * T) (1 + q * (T + 1)),
        (if q.Coprime b then (1 : ℝ) else 0) = (q.totient : ℝ) := by
      have harg : 1 + q * (T + 1) = (1 + q * T) + q := by ring
      rw [harg, Finset.sum_boole]
      exact_mod_cast Nat.filter_coprime_Ico_eq_totient q (1 + q * T)
    rw [hblock]
    push_cast
    ring

/-- **Linear growth of the windowed character second moment** (Tao 2015 §4, the endgame
count): for a Dirichlet character `χ` mod `q`,

`φ(q)·⌊N/q⌋ ≤ ∑_{b ∈ [1,N]} ‖χ(b)‖²`.

The summand is `1` at the `φ(q)`-per-block residues coprime to `q` and `0` elsewhere, so
each of the `⌊N/q⌋` full blocks contributes `φ(q)`. -/
theorem totient_mul_le_sum_normSq_dirichletChar {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) :
    (q.totient : ℝ) * ((N / q : ℕ) : ℝ)
      ≤ ∑ b ∈ Finset.Icc 1 N, ‖χ ((b : ℕ) : ZMod q)‖ ^ 2 := by
  have hpoint : ∀ b : ℕ, (if q.Coprime b then (1 : ℝ) else 0)
      ≤ ‖χ ((b : ℕ) : ZMod q)‖ ^ 2 := by
    intro b
    by_cases h : q.Coprime b
    · rw [if_pos h]
      have hu : IsUnit ((b : ℕ) : ZMod q) :=
        (ZMod.isUnit_iff_coprime b q).mpr h.symm
      rw [← hu.unit_spec, DirichletCharacter.unit_norm_eq_one χ hu.unit, one_pow]
    · rw [if_neg h]
      positivity
  have hsubset : Finset.Ico 1 (1 + q * (N / q)) ⊆ Finset.Icc 1 N := by
    intro b hb
    rw [Finset.mem_Ico] at hb
    rw [Finset.mem_Icc]
    have hdiv : N / q * q ≤ N := Nat.div_mul_le_self N q
    have hcomm : q * (N / q) = N / q * q := Nat.mul_comm _ _
    omega
  calc (q.totient : ℝ) * ((N / q : ℕ) : ℝ)
      = ∑ b ∈ Finset.Ico 1 (1 + q * (N / q)), (if q.Coprime b then (1 : ℝ) else 0) :=
        (sum_coprime_indicator_Ico_eq q (N / q)).symm
    _ ≤ ∑ b ∈ Finset.Icc 1 N, (if q.Coprime b then (1 : ℝ) else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun b _ _ => by split <;> norm_num)
    _ ≤ ∑ b ∈ Finset.Icc 1 N, ‖χ ((b : ℕ) : ZMod q)‖ ^ 2 :=
        Finset.sum_le_sum fun b _ => hpoint b

end MoltResearch
