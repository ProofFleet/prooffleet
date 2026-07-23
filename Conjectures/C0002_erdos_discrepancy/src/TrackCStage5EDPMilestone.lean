import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Assembly
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5LittlewoodWrapper
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5QuadrupleSieveProof

/-!
# Track C: the EDP milestone on cited-input interfaces (E7 of issue #2946)

The Elliott campaign's finish line: the Erdős discrepancy theorem for all
sign sequences, conditional on exactly the three cited-input interfaces

- `MatomakiRadziwillAssumption` (arXiv:1503.05121, the averaged short-interval
  mean-value theorem in the interface's `ε`-form),
- `PrimeQuadrupleCountAssumption` (the standard upper sieve for prime
  quadruples feeding the circle-method major-frequency count),
- `LittlewoodLBoundAssumption` (the Littlewood-strength character-sum bound
  of the §4 branch),

composing `edp_of_logElliott_littlewood` with the entropy-decrement master
instance of `TrackCStage5Assembly` (issue #2946, M3).

Naming note: the campaign's original milestone name was `edp_of_..._littlewood`
with the Elliott input still an interface; the master theorem replaced that
input by the two interfaces above, hence the widened name.
-/

namespace MoltResearch

namespace Tao2015

/-- **EDP milestone (the Elliott campaign closes)**: the Erdős discrepancy
theorem for all sign sequences, conditional on exactly the Matomäki–Radziwiłł,
prime-quadruple-sieve, and Littlewood interfaces. The Elliott input of
`edp_of_logElliott_littlewood` is discharged by
`logElliottNonasymptotic_of_matomakiRadziwill_quadrupleSieve`. -/
theorem edp_of_matomakiRadziwill_quadrupleSieve_littlewood
    [MatomakiRadziwillAssumption] [PrimeQuadrupleCountAssumption]
    [LittlewoodLBoundAssumption]
    (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f :=
  edp_of_logElliott_littlewood f hf

/-- **EDP on two interfaces (Track S of #3004 closes)**: the prime-quadruple
sieve is discharged unconditionally by `instPrimeQuadrupleCountAssumption`
(the Selberg Λ² upper bound), so the Erdős discrepancy theorem is conditional
on exactly the Matomäki–Radziwiłł and Littlewood interfaces. -/
theorem edp_of_matomakiRadziwill_littlewood
    [MatomakiRadziwillAssumption] [LittlewoodLBoundAssumption]
    (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f :=
  edp_of_matomakiRadziwill_quadrupleSieve_littlewood f hf

end Tao2015

end MoltResearch
