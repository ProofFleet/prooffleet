import Conjectures.C0005_erdos177_ap.src.Statement

/-!
# Erdős 177: a residue-prefix balancing reduction

This file formalizes the reduction proposed in `Problems/erdos177_approach.md`. The two unproved
nodes are isolated as `*Assumption` classes:

* `FiniteResiduePrefixBalancingAssumption` is the proposed structured vector-balancing input;
* `ResiduePrefixCompactnessAssumption` extracts one infinite coloring from uniformly feasible
  finite prefix problems.

Everything after those interfaces is proved. In particular, an arbitrary arithmetic-progression
interval is the difference of two anchored residue-class prefixes, so the conversion loses only a
factor of two and no power of the step.
-/

namespace MoltResearch

/-- The sum of the first `N` entries in the residue class `r mod d`, anchored at `r`.

The useful calls have `0 < d` and `r < d`. Keeping the definition total avoids side conditions in
the finite-sum algebra. -/
def residuePrefixSum (f : ℕ → ℤ) (d r N : ℕ) : ℤ :=
  (Finset.range N).sum fun j => f (r + j * d)

/-- `f` takes sign values on the finite prefix `[0, N)`. -/
def IsSignSequenceUpTo (f : ℕ → ℤ) (N : ℕ) : Prop :=
  ∀ n : ℕ, n < N → f n = 1 ∨ f n = -1

/-- All anchored residue-class prefix sums obey the power bound `C * d^α`. -/
def ResiduePrefixBoundedBy (f : ℕ → ℤ) (α C : ℝ) : Prop :=
  ∀ d r N : ℕ, 0 < d → r < d →
    |((residuePrefixSum f d r N : ℤ) : ℝ)| ≤ C * (d : ℝ) ^ α

/-- A finite-horizon witness for residue-prefix balancing. Only sign values below `N` and residue
prefixes whose right endpoint is at most `N` are constrained. -/
def FiniteResiduePrefixWitness (f : ℕ → ℤ) (α C : ℝ) (N : ℕ) : Prop :=
  IsSignSequenceUpTo f N ∧
    ∀ d r M : ℕ, 0 < d → r < d → r + M * d ≤ N →
      |((residuePrefixSum f d r M : ℤ) : ℝ)| ≤ C * (d : ℝ) ^ α

/-- **Unproved research node C3-BAL.** Uniform finite residue-prefix balancing with exponent `α`.

The proposed target is `α = 7`. Section 4 of `Problems/erdos177_approach.md` explains how a
structure-sensitive improvement of Beck's countable vector-balancing exponent from `4+ε` to
`7/2` would imply this `d^7` finite statement, because there are quadratically many residue
coordinates through step `d`.

This is an interface, not an instance: the repository does not claim the balancing statement. -/
class FiniteResiduePrefixBalancingAssumption (α : ℝ) : Prop where
  holds : ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, ∃ f : ℕ → ℤ, FiniteResiduePrefixWitness f α C N

/-- **Unproved formalization node C3-COMP.** Compactness for uniformly feasible finite sign
colorings.

Mathematically this is the standard finitely-branching-tree/compact-product extraction, not a new
discrepancy conjecture. It remains an explicit interface so the research reduction does not hide
an unformalized limit argument. See §5 of `Problems/erdos177_approach.md`. -/
class ResiduePrefixCompactnessAssumption (α : ℝ) : Prop where
  limit : ∀ C : ℝ, 0 < C →
    (∀ N : ℕ, ∃ f : ℕ → ℤ, FiniteResiduePrefixWitness f α C N) →
      ∃ f : ℕ → ℤ, IsSignSequence f ∧ ResiduePrefixBoundedBy f α C

/-- A global sign sequence with a residue-prefix bound restricts to a valid witness at every
finite ambient horizon. -/
theorem finiteResiduePrefixWitness_of_global {f : ℕ → ℤ} {α C : ℝ}
    (hf : IsSignSequence f) (hprefix : ResiduePrefixBoundedBy f α C) (N : ℕ) :
    FiniteResiduePrefixWitness f α C N := by
  constructor
  · intro n _hn
    exact hf n
  · intro d r M hd hr _hend
    exact hprefix d r M hd hr

/-- The original AP bound directly controls every anchored residue prefix with the same constant.
Together with `apDiscrepancyBoundedBy_of_residuePrefixBoundedBy`, this shows that the prefix
normal form itself is equivalent to the target up to a factor of two; the research content must
therefore enter in proving the balancing assumption, not in this bookkeeping change. -/
theorem residuePrefixBoundedBy_of_apDiscrepancyBoundedBy {f : ℕ → ℤ} {α C : ℝ}
    (hap : APDiscrepancyBoundedBy f (fun d => C * (d : ℝ) ^ α)) :
    ResiduePrefixBoundedBy f α C := by
  intro d r N hd _hr
  simpa [residuePrefixSum] using hap r N d hd

/-- Splitting an anchored residue prefix at length `m` leaves the requested affine interval as
its tail. This is the finite-sum identity behind the reduction. -/
theorem residuePrefixSum_add_length (f : ℕ → ℤ) (d r m L : ℕ) :
    residuePrefixSum f d r (m + L) =
      residuePrefixSum f d r m +
        (Finset.range L).sum (fun j => f ((r + m * d) + j * d)) := by
  unfold residuePrefixSum
  simpa [Nat.add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (Finset.sum_range_add (f := fun j => f (r + j * d)) m L)

/-- Every affine interval is the difference of two prefixes in its canonical residue class. -/
theorem intervalSum_eq_residuePrefixSum_sub (f : ℕ → ℤ) (a L d : ℕ) :
    (Finset.range L).sum (fun j => f (a + j * d)) =
      residuePrefixSum f d (a % d) (a / d + L) -
        residuePrefixSum f d (a % d) (a / d) := by
  have ha : a % d + a / d * d = a := by
    simpa [Nat.mul_comm] using Nat.mod_add_div a d
  calc
    (Finset.range L).sum (fun j => f (a + j * d)) =
        (Finset.range L).sum (fun j => f (((a % d) + (a / d) * d) + j * d)) := by
          rw [ha]
    _ = residuePrefixSum f d (a % d) (a / d + L) -
          residuePrefixSum f d (a % d) (a / d) := by
          rw [residuePrefixSum_add_length]
          abel

/-- A uniform anchored-prefix bound gives the full interval bound with a factor of two and no
loss in the exponent. -/
theorem apDiscrepancyBoundedBy_of_residuePrefixBoundedBy {f : ℕ → ℤ} {α C : ℝ}
    (hprefix : ResiduePrefixBoundedBy f α C) :
    APDiscrepancyBoundedBy f (fun d => (2 * C) * (d : ℝ) ^ α) := by
  intro a L d hd
  have hr : a % d < d := Nat.mod_lt a hd
  have hright := hprefix d (a % d) (a / d + L) hd hr
  have hleft := hprefix d (a % d) (a / d) hd hr
  rw [intervalSum_eq_residuePrefixSum_sub]
  push_cast
  calc
    |(residuePrefixSum f d (a % d) (a / d + L) : ℝ) -
        (residuePrefixSum f d (a % d) (a / d) : ℝ)|
        ≤ |(residuePrefixSum f d (a % d) (a / d + L) : ℝ)| +
            |(residuePrefixSum f d (a % d) (a / d) : ℝ)| := abs_sub _ _
    _ ≤ C * (d : ℝ) ^ α + C * (d : ℝ) ^ α := add_le_add hright hleft
    _ = (2 * C) * (d : ℝ) ^ α := by ring

/-- The conditional capstone: the finite balancing node plus compactness proves exponent `α`.

No instance of either assumption class is supplied in this file. In particular, the specialization
to `α = 7` below is conditional and does not claim an improvement of Beck's theorem. -/
theorem erdos177Exponent_of_assumptions (α : ℝ)
    [hfinite : FiniteResiduePrefixBalancingAssumption α]
    [hcompact : ResiduePrefixCompactnessAssumption α] :
    Erdos177Exponent α := by
  obtain ⟨C, hC, hwitnesses⟩ := hfinite.holds
  obtain ⟨f, hf, hprefix⟩ := hcompact.limit C hC hwitnesses
  refine ⟨2 * C, f, hf, ?_⟩
  exact apDiscrepancyBoundedBy_of_residuePrefixBoundedBy hprefix

/-- The proposed strict improvement, explicitly conditional on the two exponent-seven
interfaces. -/
theorem erdos177Exponent_seven_of_assumptions
    [FiniteResiduePrefixBalancingAssumption (7 : ℝ)]
    [ResiduePrefixCompactnessAssumption (7 : ℝ)] :
    Erdos177Exponent 7 :=
  erdos177Exponent_of_assumptions 7

/-- The proposed exponent is strictly below Beck's exponent `8`. -/
theorem erdos177_seven_lt_eight : (7 : ℝ) < 8 := by
  norm_num

end MoltResearch
