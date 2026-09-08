import Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy
import MoltResearch.Discrepancy.Multiplicative

/-!
# Erdős Problem 177: step-dependent arithmetic-progression discrepancy

This file records the open problem and the currently known exponent window as propositions.
Only the final theorem below is proved: Tao's Erdős discrepancy theorem rules out a completely
multiplicative sign sequence as a witness, because such a sequence's discrepancy at every nonzero
step is the same as its discrepancy at step one.
-/

namespace MoltResearch

/-- A real-valued function `h` bounds every finite arithmetic-progression sum of `f`, uniformly
in the start and length but with a bound depending on the positive step.

This is the formulation of Erdős Problem 177 at
<https://www.erdosproblems.com/177>. -/
def APDiscrepancyBoundedBy (f : ℕ → ℤ) (h : ℕ → ℝ) : Prop :=
  ∀ a L d : ℕ, 0 < d →
    |((∑ j ∈ Finset.range L, f (a + j * d) : ℤ) : ℝ)| ≤ h d

/-- The bound `h` is achievable by a single sign sequence on all finite arithmetic progressions.

See Erdős Problem 177: <https://www.erdosproblems.com/177>. -/
def Erdos177Achievable (h : ℕ → ℝ) : Prop :=
  ∃ f : ℕ → ℤ, IsSignSequence f ∧ APDiscrepancyBoundedBy f h

/-- A power exponent is achievable if a constant multiple of that power bounds all progression
sums. Real powers are used, so this definition also expresses nonintegral exponents.

See Erdős Problem 177: <https://www.erdosproblems.com/177>. -/
def Erdos177Exponent (α : ℝ) : Prop :=
  ∃ C : ℝ, Erdos177Achievable (fun d => C * (d : ℝ) ^ α)

/-- Proposition recording Beck's 2017 upper bound: every exponent strictly above `8` is
achievable. This known theorem is recorded as an open proposition here, not proved.

Source: J. Beck, *A Discrepancy Problem: Balancing Infinite Dimensional Vectors* (2017),
<https://doi.org/10.1007/978-3-319-55357-3_3>. -/
def Erdos177BeckUpperBound : Prop :=
  ∀ ε : ℝ, 0 < ε → Erdos177Exponent (8 + ε)

/-- Proposition recording the consequence of Roth's 1964 discrepancy lower bound: some positive
constant multiple of the square-root profile is not achievable. This known result is recorded as
an open proposition here, not proved.

Source: K. F. Roth, *Remark concerning integer sequences*, Acta Arith. 9 (1964), 257–260,
<https://doi.org/10.4064/aa-9-3-257-260>; see also the deduction stated at
<https://www.erdosproblems.com/177>. -/
def Erdos177RothLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ¬ Erdos177Achievable (fun d => c * (d : ℝ) ^ (1 / 2 : ℝ))

/-- A completely multiplicative sign sequence cannot witness any step-dependent bound in Erdős
Problem 177.

Indeed, the bound at step one uniformly bounds the ordinary partial sums. Complete
multiplicativity then identifies the discrepancy at every nonzero step with the step-one
discrepancy, contradicting the proved Erdős discrepancy theorem
`erdos_discrepancy_notBounded`. -/
theorem not_achievable_of_completelyMultiplicative {f : ℕ → ℤ} {h : ℕ → ℝ}
    (hf : IsSignSequence f) (hmul : CompletelyMultiplicative f) :
    ¬ APDiscrepancyBoundedBy f h := by
  intro hbound
  obtain ⟨B, hB⟩ : ∃ B : ℕ, h 1 ≤ B := exists_nat_ge (h 1)
  have hstep : ∀ L : ℕ, Int.natAbs (apSum f 1 L) ≤ B := by
    intro L
    have hreal : |((apSum f 1 L : ℤ) : ℝ)| ≤ (B : ℝ) := by
      calc
        |((apSum f 1 L : ℤ) : ℝ)| ≤ h 1 := by
          simpa [apSum, Nat.add_comm] using hbound 1 L 1 Nat.one_pos
        _ ≤ (B : ℝ) := hB
    have hnatAbsReal : (Int.natAbs (apSum f 1 L) : ℝ) ≤ (B : ℝ) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hreal
    exact_mod_cast hnatAbsReal
  have hbounded : BoundedDiscrepancy f :=
    (hmul.boundedDiscrepancy_iff_exists_forall_natAbs_apSum_one_le hf).2 ⟨B, hstep⟩
  exact erdos_discrepancy_notBounded f hf hbounded

end MoltResearch
