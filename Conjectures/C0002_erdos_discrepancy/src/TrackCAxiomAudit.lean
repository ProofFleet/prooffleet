import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Derivation
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Core
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Reduction
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5VanDerCorputProof
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5BCCWrapper
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5FourierProof
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5LittlewoodWrapper
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5EDPMilestone
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5PrimeBlockMajorArcProof
-- For the anti-vacuity witnesses (issue #2879) only.
import Mathlib.NumberTheory.ArithmeticFunction

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
- `stage5_notBounded`: **standard axioms only** (endgame flipped 2026-07-17) — the body
  is now `notBounded_of_derivation` through the honest §2/§3/§4 instances; the Stage-2
  stub no longer feeds Stage 5. (The demoted Stage-2/3/4 stub plane still exists and
  keeps its own footprints until its scheduled deletion.)
- `elliott_master`, `logElliottNonasymptotic_of_matomakiRadziwill_quadrupleSieve`, and
  the milestone `edp_of_matomakiRadziwill_quadrupleSieve_littlewood` (the Elliott
  campaign, issue #2946): **standard axioms only** — the entropy-decrement proof of the
  Elliott estimate consumes exactly the Matomäki–Radziwiłł and prime-quadruple-sieve
  hypothesis classes, and EDP now rests on exactly the three cited-input interfaces.
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
info: 'MoltResearch.Tao2015.theorem18_of_logElliott_vinogradovKorobov' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.theorem18_of_logElliott_vinogradovKorobov

/--
info: 'MoltResearch.Tao2015.instFourierReductionStochasticAssumption' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.instFourierReductionStochasticAssumption

/--
info: 'MoltResearch.Tao2015.edp_of_logElliott_vinogradovKorobov' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.edp_of_logElliott_vinogradovKorobov

/--
info: 'MoltResearch.Tao2015.vinogradovKorobov_of_littlewoodLBound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.vinogradovKorobov_of_littlewoodLBound

/--
info: 'MoltResearch.Tao2015.edp_of_logElliott_littlewood' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.edp_of_logElliott_littlewood

/--
info: 'MoltResearch.Tao2015.elliott_master' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.elliott_master

/--
info: 'MoltResearch.Tao2015.logElliottNonasymptotic_of_matomakiRadziwill_quadrupleSieve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.logElliottNonasymptotic_of_matomakiRadziwill_quadrupleSieve

/--
info: 'MoltResearch.Tao2015.edp_of_matomakiRadziwill_quadrupleSieve_littlewood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.edp_of_matomakiRadziwill_quadrupleSieve_littlewood

/--
info: 'MoltResearch.Tao2015.instPrimeQuadrupleCountAssumption' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.instPrimeQuadrupleCountAssumption

/--
info: 'MoltResearch.Tao2015.edp_of_matomakiRadziwill_littlewood' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.edp_of_matomakiRadziwill_littlewood

/-!
## Anti-vacuity witnesses (issue #2879)

The classes the derivation quantifies over must stay *inhabited by non-degenerate members*,
or every conditional theorem above is silently vacuous — exactly what happened when the
unguarded multiplicativity law collapsed {completely multiplicative, unimodular} to the
constant-1 function (`theorem18` was provable with no assumption classes). These examples
turn that failure mode into a build failure: each exhibits a member taking the value `-1`
at `2`, which no constant-1 collapse can satisfy.
-/

open MeasureTheory in
/-- The stochastic layer is inhabited by a non-degenerate family: the deterministic
embedding of the Liouville-style sequence `n ↦ (−1)^Ω(n)` over the one-point probability
space. Under the pre-#2879 definitions this example was unprovable. -/
example : ∃ G : MoltResearch.StochasticMultiplicative (Measure.dirac ()),
    G.g () 2 = -1 := by
  refine ⟨MoltResearch.StochasticMultiplicative.ofDeterministic _
    (fun n => (-1 : ℂ) ^ (ArithmeticFunction.cardFactors n)) ?_ ?_, ?_⟩
  · intro a b ha hb
    simp only [ArithmeticFunction.cardFactors_mul ha hb, pow_add]
  · intro n
    simp only [norm_pow, norm_neg, norm_one, one_pow]
  · simp only [MoltResearch.StochasticMultiplicative.ofDeterministic,
      ArithmeticFunction.cardFactors_apply_prime Nat.prime_two, pow_one]

/--
info: 'MoltResearch.Tao2015.stage5_notBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.stage5_notBounded

/--
info: 'MoltResearch.Tao2015.edp_of_matomakiRadziwill' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.edp_of_matomakiRadziwill

/--
info: 'MoltResearch.Tao2015.theorem18_of_matomakiRadziwill' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.theorem18_of_matomakiRadziwill

/--
info: 'MoltResearch.Tao2015.elliott_master_majorArc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.elliott_master_majorArc

/--
info: 'MoltResearch.Tao2015.logElliottNonasymptotic_of_majorArc_quadrupleSieve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.logElliottNonasymptotic_of_majorArc_quadrupleSieve

/--
info: 'MoltResearch.Tao2015.edp_of_matomakiRadziwillMajorArc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.edp_of_matomakiRadziwillMajorArc

/--
info: 'MoltResearch.Tao2015.theorem18_of_matomakiRadziwillMajorArc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.theorem18_of_matomakiRadziwillMajorArc

/--
info: 'MoltResearch.Tao2015.instPrimeBlockMajorArcAssumption' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.instPrimeBlockMajorArcAssumption

/--
info: 'MoltResearch.Tao2015.edp_of_majorArcMR' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.edp_of_majorArcMR

/--
info: 'MoltResearch.Tao2015.theorem18_of_majorArcMR' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MoltResearch.Tao2015.theorem18_of_majorArcMR
