import Conjectures.C0005_erdos177_ap.src.Balancing

/-!
# Erdős 177: milestone decision and exact remaining obstruction

C7 does not supply an unconditional exponent below `8`.  Instead, this file closes the reduction
audit: after the compactness instance in `Compactness.lean`, uniform finite residue-prefix
balancing is equivalent to the original exponent statement.  Thus
`FiniteResiduePrefixBalancingAssumption α` is the exact remaining proposition, while the
barrier-preserving interface from `Balancing.lean` is one sufficient, stronger route to it.

No balancing-assumption instance is declared here.
-/

namespace MoltResearch

/-- Uniform finite residue-prefix balancing is exactly equivalent to the original Erdős 177
exponent statement.

The forward implication restricts a global AP coloring to every finite horizon.  Positivity of
the constant is forced by the one-term progression with step one.  The reverse implication uses
the proved compactness instance and the prefix-to-interval reduction.  Consequently there is no
remaining compactness or normalization gap hidden behind the finite balancing interface. -/
theorem erdos177Exponent_iff_finiteResiduePrefixBalancing (α : ℝ) :
    Erdos177Exponent α ↔ FiniteResiduePrefixBalancingAssumption α := by
  constructor
  · rintro ⟨C, f, hf, hap⟩
    have hC_one : (1 : ℝ) ≤ C := by
      have hone := hap 0 1 1 Nat.one_pos
      rcases hf 0 with h | h <;> simpa [h] using hone
    have hC : 0 < C := zero_lt_one.trans_le hC_one
    have hprefix : ResiduePrefixBoundedBy f α C :=
      residuePrefixBoundedBy_of_apDiscrepancyBoundedBy hap
    refine { holds := ⟨C, hC, ?_⟩ }
    intro N
    exact ⟨f, finiteResiduePrefixWitness_of_global hf hprefix N⟩
  · intro hfinite
    letI : FiniteResiduePrefixBalancingAssumption α := hfinite
    exact erdos177Exponent_of_assumptions α

/-- At the proposed exponent seven, the finite balancing proposition is the exact unresolved
milestone: proving either side proves the other.  This theorem does not inhabit either side. -/
theorem erdos177Exponent_seven_iff_finiteResiduePrefixBalancing :
    Erdos177Exponent (7 : ℝ) ↔ FiniteResiduePrefixBalancingAssumption (7 : ℝ) :=
  erdos177Exponent_iff_finiteResiduePrefixBalancing 7

/--
info: 'MoltResearch.erdos177Exponent_iff_finiteResiduePrefixBalancing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms erdos177Exponent_iff_finiteResiduePrefixBalancing

end MoltResearch
