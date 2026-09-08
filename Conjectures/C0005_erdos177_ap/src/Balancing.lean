import Conjectures.C0005_erdos177_ap.src.Compactness

/-!
# Erdős 177: the barrier-preserving partial-coloring interface

This file isolates the step that is missing from the finite vector-balancing literature surveyed in
`Problems/erdos177_balancing.md`.  A partial coloring uses `0` for an uncolored position.  The new
assumption says that whenever such a coloring lies inside one fixed residue-prefix barrier, at
least one more position can be colored without moving any already colored position or enlarging
the barrier.

The assumption is deliberately stronger than `FiniteResiduePrefixBalancingAssumption`: it must
extend every feasible partial state, not merely produce one full witness.  The proof below is the
finite descent that turns this barrier-preserving step into the existing balancing interface.  No
instance of the new assumption is supplied.
-/

namespace MoltResearch

/-- A partial sign sequence on `[0, N)`, with `0` denoting an uncolored position. -/
def IsPartialSignSequenceUpTo (f : ℕ → ℤ) (N : ℕ) : Prop :=
  ∀ n : ℕ, n < N → f n = 1 ∨ f n = -1 ∨ f n = 0

/-- A partial coloring obeys the same residue-prefix barrier as a full finite witness. -/
def PartialResiduePrefixWitness (f : ℕ → ℤ) (α C : ℝ) (N : ℕ) : Prop :=
  IsPartialSignSequenceUpTo f N ∧
    ∀ d r M : ℕ, 0 < d → r < d → r + M * d ≤ N →
      |((residuePrefixSum f d r M : ℤ) : ℝ)| ≤ C * (d : ℝ) ^ α

/-- `g` preserves every position that was already colored by `f`. -/
def PreservesColoredUpTo (f g : ℕ → ℤ) (N : ℕ) : Prop :=
  ∀ n : ℕ, n < N → f n ≠ 0 → g n = f n

theorem preservesColoredUpTo_refl (f : ℕ → ℤ) (N : ℕ) :
    PreservesColoredUpTo f f N := by
  intro n _hn _hfn
  rfl

theorem PreservesColoredUpTo.trans {f g h : ℕ → ℤ} {N : ℕ}
    (hfg : PreservesColoredUpTo f g N) (hgh : PreservesColoredUpTo g h N) :
    PreservesColoredUpTo f h N := by
  intro n hn hfn
  have hgf : g n = f n := hfg n hn hfn
  calc
    h n = g n := hgh n hn (by simpa [hgf] using hfn)
    _ = f n := hgf

/-- The number of positions in `[0, N)` that remain uncolored. -/
def uncoloredCount (f : ℕ → ℤ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n ↦ f n = 0).card

/-- **Unproved research node C6-BARRIER.** Strict progress inside one fixed barrier.

The constant `C` is uniform in the horizon.  From every feasible partial state with an uncolored
position, the assumption produces another feasible state, fixes all old signs, and strictly
decreases the number of zero entries.  Modern partial-coloring theorems control the increment from
the current state; they do not provide this absolute barrier invariant for the residue-prefix
system.  See `Problems/erdos177_balancing.md` for the quantitative obstruction.

The usual "color a constant fraction" conclusion would be stronger than the strict decrease used
here.  Strict decrease is enough for the finite descent, so the interface records only the logical
content needed downstream. -/
class BarrierPreservingPartialColoringAssumption (α : ℝ) : Prop where
  holds : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (f : ℕ → ℤ), PartialResiduePrefixWitness f α C N →
      0 < uncoloredCount f N →
        ∃ g : ℕ → ℤ,
          PartialResiduePrefixWitness g α C N ∧
          PreservesColoredUpTo f g N ∧
          uncoloredCount g N < uncoloredCount f N

/-- The all-zero partial coloring starts inside every nonnegative barrier. -/
theorem partialResiduePrefixWitness_zero (α C : ℝ) (N : ℕ) (hC : 0 ≤ C) :
    PartialResiduePrefixWitness (fun _ ↦ 0) α C N := by
  constructor
  · intro n _hn
    exact Or.inr (Or.inr rfl)
  · intro d r M _hd _hr _hend
    have hpow : 0 ≤ (d : ℝ) ^ α := by positivity
    simpa [residuePrefixSum] using mul_nonneg hC hpow

/-- A partial sign sequence with no zero entry is a full finite sign sequence. -/
theorem isSignSequenceUpTo_of_uncoloredCount_eq_zero {f : ℕ → ℤ} {N : ℕ}
    (hf : IsPartialSignSequenceUpTo f N) (hzero : uncoloredCount f N = 0) :
    IsSignSequenceUpTo f N := by
  intro n hn
  have hne : f n ≠ 0 := by
    intro hfn
    have hmem : n ∈ (Finset.range N).filter (fun k ↦ f k = 0) := by
      simp [hn, hfn]
    have hpos : 0 < uncoloredCount f N := Finset.card_pos.mpr ⟨n, hmem⟩
    omega
  rcases hf n hn with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (hne h).elim

private theorem exists_complete_partialColoring {α C : ℝ}
    (hstep : ∀ (N : ℕ) (f : ℕ → ℤ), PartialResiduePrefixWitness f α C N →
      0 < uncoloredCount f N →
        ∃ g : ℕ → ℤ,
          PartialResiduePrefixWitness g α C N ∧
          PreservesColoredUpTo f g N ∧
          uncoloredCount g N < uncoloredCount f N)
    (N : ℕ) (f : ℕ → ℤ) (hf : PartialResiduePrefixWitness f α C N) :
    ∃ g : ℕ → ℤ,
      PartialResiduePrefixWitness g α C N ∧
      PreservesColoredUpTo f g N ∧
      uncoloredCount g N = 0 := by
  by_cases hdone : uncoloredCount f N = 0
  · exact ⟨f, hf, preservesColoredUpTo_refl f N, hdone⟩
  · obtain ⟨g, hg, hpreserves, hdecrease⟩ :=
      hstep N f hf (Nat.pos_of_ne_zero hdone)
    obtain ⟨h, hh, hgh, hfull⟩ := exists_complete_partialColoring hstep N g hg
    exact ⟨h, hh, hpreserves.trans hgh, hfull⟩
termination_by uncoloredCount f N

/-- A barrier-preserving partial-coloring step is a sharpening of the finite balancing
assumption: finite descent from the zero state produces a full witness at every horizon. -/
instance finiteResiduePrefixBalancingAssumption_of_barrierPreserving (α : ℝ)
    [hbarrier : BarrierPreservingPartialColoringAssumption α] :
    FiniteResiduePrefixBalancingAssumption α where
  holds := by
    obtain ⟨C, hC, hstep⟩ := hbarrier.holds
    refine ⟨C, hC, ?_⟩
    intro N
    obtain ⟨f, hf, _hpreserves, hfull⟩ := exists_complete_partialColoring hstep N (fun _ ↦ 0)
      (partialResiduePrefixWitness_zero α C N hC.le)
    exact ⟨f, isSignSequenceUpTo_of_uncoloredCount_eq_zero hf.1 hfull, hf.2⟩

/-- The exact conditional route exposed by C6: once the barrier-preserving step is supplied,
compactness and the prefix-to-interval reduction prove exponent `α`. -/
theorem erdos177Exponent_of_barrierPreserving (α : ℝ)
    [BarrierPreservingPartialColoringAssumption α] :
    Erdos177Exponent α :=
  erdos177Exponent_of_assumptions α

/-- Exponent seven follows conditionally from the barrier-preserving step at exponent seven. -/
theorem erdos177Exponent_seven_of_barrierPreserving
    [BarrierPreservingPartialColoringAssumption (7 : ℝ)] :
    Erdos177Exponent 7 :=
  erdos177Exponent_of_barrierPreserving 7

/--
info: 'MoltResearch.erdos177Exponent_of_barrierPreserving' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms erdos177Exponent_of_barrierPreserving

end MoltResearch
