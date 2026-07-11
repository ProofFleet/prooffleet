import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Derivation
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Core
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Reduction
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5VanDerCorputProof

/-!
# Track C: axiom-footprint audit (machine-checked honesty claims)

This file turns the repo's central honesty claims from docstring assertions into build
failures. Each `#guard_msgs` below pins the exact `#print axioms` output of a flagship
theorem; if anyone's change alters an axiom footprint — e.g. accidentally routing new work
through the Stage-2 stub, or (the good case) retiring the stub — this file stops compiling
and must be updated *consciously*, with the diff visible in review.

Expected footprints (all also include Lean's three standard axioms
`propext`, `Classical.choice`, `Quot.sound`, which every Mathlib-based proof uses):

- `notBounded_of_derivation`, `theorem18`, `stage2StubContent_of_univ_multiplicative`:
  **standard axioms only** — the typed derivation skeleton is honestly conditional (its
  assumptions are hypothesis classes, not axioms).
- `vanDerCorputAssumption_of_logElliottNonasymptotic` (the Prop-1.11 proof) and
  `theorem18_of_logElliottNonasymptotic` (Theorem 1.8 under the new instance chain):
  **standard axioms only** — discharging the van der Corput leg introduced no axiom;
  in particular the Elliott input stays a hypothesis class.
- `stage5_notBounded`: standard axioms **plus the Stage-2 stub axiom** — the documented
  current wiring. The derivation card's endgame box is precisely: flip this footprint to
  standard-only (by re-proving from the interfaces) and delete the stub.
-/

/--
info: 'MoltResearch.Tao2015.notBounded_of_derivation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.notBounded_of_derivation

/--
info: 'MoltResearch.Tao2015.theorem18' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.theorem18

/--
info: 'MoltResearch.Tao2015.stage2StubContent_of_univ_multiplicative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.stage2StubContent_of_univ_multiplicative

/--
info: 'MoltResearch.Tao2015.vanDerCorputAssumption_of_logElliottNonasymptotic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.vanDerCorputAssumption_of_logElliottNonasymptotic

/--
info: 'MoltResearch.Tao2015.theorem18_of_logElliottNonasymptotic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.theorem18_of_logElliottNonasymptotic

/--
info: 'MoltResearch.Tao2015.stage5_notBounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 MoltResearch.Tao2015.stage2Stub_exists_params_one_le_unboundedDiscOffset]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.stage5_notBounded
