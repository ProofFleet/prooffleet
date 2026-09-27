import Conjectures.C0002_erdos_discrepancy.src.ErdosDiscrepancy

/-!
# The Erdős discrepancy theorem: proof of the statement of record

`EDP.erdos_discrepancy` below restates, word for word, the theorem of the same name in
`PalomarEDP.Challenge`, and proves it. This module does not import the Challenge (the two
modules must never be imported together, since both declare `EDP.erdos_discrepancy`); Comparator
builds each on its own and checks that the two statements are identical and that this proof uses
only the axioms `propext`, `Quot.sound` and `Classical.choice`.

The proof is the repository's existing public theorem `MoltResearch.erdos_discrepancy`
(`Conjectures/C0002_erdos_discrepancy/src/ErdosDiscrepancy.lean`), which is stated with three
small project definitions from `MoltResearch/Discrepancy/Basic.lean`:

* `IsSignSequence f := ∀ n, f n = 1 ∨ f n = -1`;
* `apSum f d n := (Finset.range n).sum (fun i => f ((i + 1) * d))`;
* `HasDiscrepancyAtLeast f C := ∃ d n : ℕ, d > 0 ∧ Int.natAbs (apSum f d n) > C`.

Unfolding them gives exactly the explicit statement below, so the proof is that theorem applied
to `f` and `hf`, with no further argument. `MoltResearch.erdos_discrepancy` is in turn derived
from `MoltResearch.Tao2015.erdos_discrepancy_unconditional`
(`Conjectures/C0002_erdos_discrepancy/src/TrackCStage5PrimeLargeValuesDischarge.lean`), whose
axiom footprint is pinned in `Conjectures/C0002_erdos_discrepancy/src/TrackCAxiomAudit.lean`;
the pin at the end of this file repeats that audit for the submitted declaration.
-/

namespace EDP

theorem erdos_discrepancy
    (f : ℕ → ℤ)
    (hf : ∀ n : ℕ, f n = 1 ∨ f n = -1) :
    ∀ C : ℕ, ∃ d n : ℕ,
      0 < d ∧
      C < Int.natAbs ((Finset.range n).sum (fun i => f ((i + 1) * d))) :=
  MoltResearch.erdos_discrepancy f hf

end EDP

/--
info: 'EDP.erdos_discrepancy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EDP.erdos_discrepancy
