import Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy

/-!
# Erdős Problem 67 bridge

This file bridges the unconditional integer-valued Erdős discrepancy theorem in this tree to
the statement of Erdős Problem 67 used by
[`erdosproblems`](https://github.com/teorth/erdosproblems/blob/master/data/problems.yaml) and
[`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/67.lean).

The statement text was copied verbatim on 2026-09-08 from the `main` branch of
`google-deepmind/formal-conjectures`.
-/

open Filter

namespace MoltResearch.Erdos67

theorem erdos_67 (f : ℕ → ({-1, 1} : Finset ℝ)) (C : ℝ) (hC : 0 < C) : ∃ᵉ (d ≥ 1) (m ≥ 1),
    C < |∑ k ∈ Finset.Icc 1 m, (f (k * d)).1| := by
  classical
  let g : ℕ → ℤ := fun n => if (f n).1 = 1 then 1 else -1
  have hfg (n : ℕ) : (f n).1 = (g n : ℝ) := by
    have hn := (f n).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with hn | hn
    · simp [g, hn]
    · simp [g, hn]
  have hg : IsSignSequence g := by
    intro n
    simp only [g]
    split_ifs <;> simp
  have hnb : ¬ BoundedDiscrepancy g :=
    _root_.MoltResearch.Tao2015.erdos_discrepancy_unconditional g hg
  let B : ℕ := ⌈C⌉₊
  have hBpos : 0 < B := by
    exact_mod_cast hC.trans_le (Nat.le_ceil C)
  have hex : ∃ d n : ℕ, d > 0 ∧ B < Int.natAbs (apSum g d n) := by
    by_contra h
    apply hnb
    refine ⟨B, ?_⟩
    intro d n hd
    by_contra hle
    exact h ⟨d, n, hd, Nat.lt_of_not_ge hle⟩
  obtain ⟨d, n, hd, hlarge⟩ := hex
  have hn : n ≥ 1 := by
    have hsumpos : 0 < Int.natAbs (apSum g d n) := hBpos.trans hlarge
    have hn0 : n ≠ 0 := by
      intro hn0
      subst n
      simp [apSum] at hsumpos
    omega
  refine ⟨d, Nat.succ_le_iff.mpr hd, n, hn, ?_⟩
  have hsum :
      (∑ k ∈ Finset.Icc 1 n, (f (k * d)).1) = ((apSum g d n : ℤ) : ℝ) := by
    rw [apSum_eq_sum_Icc]
    push_cast
    apply Finset.sum_congr rfl
    intro k _hk
    exact hfg (k * d)
  rw [hsum]
  calc
    C ≤ (B : ℝ) := Nat.le_ceil C
    _ < (Int.natAbs (apSum g d n) : ℝ) := by exact_mod_cast hlarge
    _ = ((|apSum g d n| : ℤ) : ℝ) := Nat.cast_natAbs _
    _ = |((apSum g d n : ℤ) : ℝ)| := Int.cast_abs

/-- info: 'MoltResearch.Erdos67.erdos_67' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms erdos_67

end MoltResearch.Erdos67
