import MoltResearch.Discrepancy.PretentiousBandSplit

/-!
# Track R: the far-frequency repulsion interface

This is the one analytic remainder in the exceptional `t₁` split which is
not present in the verified nucleus.  It records the far-frequency consequence
of the argument preceding Lemma A.4 in Appendix A of Matomäki--Radziwiłł--Tao,
*An averaged form of Chowla's conjecture*, Algebra & Number Theory 9 (2015),
2167--2196.  That argument invokes the standard lower bound for the
pretentious distance between two archimedean twists; in the far regime its
proof runs through equidistribution of `u log p` (Erdős--Turán and zeta
bounds), which has not been formalized at the pinned Mathlib revision.

The statement is restricted to exactly the application range: `t₁` minimizes
the squared distance on `[-y,y]`, both frequencies lie in that band, and their
separation exceeds `(log y)^20`.  The conclusion uses the fixed exponent
`1/6 - 1/(3π)` required downstream.  Constants and the explicit threshold are
weaker than the asymptotic paper statement.

**No instance of this class is or may be declared here.**  Consumers must carry
it as a hypothesis until the equidistribution argument is formalized.
-/

namespace MoltResearch

namespace Tao2015

/-- Far-regime archimedean repulsion, in the minimizer form used by the
exceptional-cell argument.  No instance may be declared; see the module
docstring.

Source: arXiv:1503.05121, Appendix A, proof of Proposition A.3. -/
class FarRegimeRepulsionAssumption : Prop where
  bound : ∃ y0 : ℕ, ∀ (f : ℕ → ℂ) (y : ℕ) (t1 t : ℝ),
    Unimodular f → y0 ≤ y → 3 ≤ y →
    |t1| ≤ y → |t| ≤ y →
    pretentiousDistSq f
        (fun n => (n : ℂ) ^ (-(Complex.I * (t1 : ℂ)))) y ≤
      pretentiousDistSq f
        (fun n => (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) y →
    (Real.log y) ^ (20 : ℕ) < |t - t1| →
    exceptionalRepulsionRho * Real.log (Real.log y) ≤
      pretentiousDistSq f
        (fun n => (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) y

end Tao2015

end MoltResearch
