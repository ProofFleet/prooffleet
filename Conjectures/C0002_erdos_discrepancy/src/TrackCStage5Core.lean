import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5FourierProof
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5VanDerCorputProof
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5BCCWrapper
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5LittlewoodWrapper

/-!
# Track C: Stage 5 skeleton — EDP conditional on the analytic core (Tao 2015)

This file is **Conjectures-only** glue: the Stage-5 boundary packaging Tao's two deep inputs —
the stochastic Fourier reduction (A) and the nonasymptotic log-Elliott theorem (B) — and
exposing the conditional target of the analytic-core card (`Problems/tao2015_analytic_core.md`):

`stage5_notBounded [FourierReductionStochasticAssumption] [LogElliottNonasymptoticAssumption] :
  ∀ f, IsSignSequence f → ¬ BoundedDiscrepancy f`.

**Contract migration (one-time, deliberate):** the original skeleton carried the first-cut
classes `FourierReductionAssumption` / `LogElliottAssumption`. Both were later found to be
**stronger than the literature** (see the strength warnings in `TrackCStage5Fourier.lean` /
`TrackCStage5Elliott.lean` and the corrected card records): the paper proves the *stochastic*
reduction and needs the *nonasymptotic* Elliott input. The Stage-5 contract now carries the
faithful pair; this happened while nothing downstream consumed Stage 5, so no migration debt
was incurred. From here on the signature is stable.

**Proof status (endgame, 2026-07-17):** the derivation (C) has landed in full — §2
(`TrackCStage5FourierProof`, `FourierReductionStochasticAssumption` now unconditional),
§3 (`vanDerCorputAssumption_of_logElliottNonasymptotic`), §4 (`BorweinChoiCoonsAssumption`
from `VinogradovKorobovAssumption`, itself reduced to `LittlewoodLBoundAssumption`). The
body is now `notBounded_of_derivation` — **no Stage-2 assumption anywhere on this path** (the
the axiom audit pins the footprint to standard axioms). One deliberate signature amendment:
the honest §4 leg needs `VinogradovKorobovAssumption`, which the original contract did
not carry (its strength was clarified only when §4 was formalized); the redundant-but-
compatible `FourierReductionStochasticAssumption` argument is retained so existing call
shapes still elaborate. The legacy Stage-2/3/4 plane no longer feeds this theorem and is
conditional on an explicit assumption.
-/

namespace MoltResearch

namespace Tao2015

/-- **Stage-5 target, honestly discharged**: EDP for all sign sequences from the full
derivation (C) — the §2 reduction (now unconditional), the §3 van der Corput leg from
`LogElliottNonasymptoticAssumption`, and the §4 Borwein–Choi–Coons leg from
`VinogradovKorobovAssumption`. No axiom anywhere on the path. -/
theorem stage5_notBounded
    [FourierReductionStochasticAssumption] [LogElliottNonasymptoticAssumption]
    [VinogradovKorobovAssumption] :
    ∀ f : ℕ → ℤ, IsSignSequence f → ¬ BoundedDiscrepancy f := by
  intro f hf
  exact notBounded_of_derivation f hf

/-- Stage-5 surface-statement variant: unbounded discrepancy in the
`∀ C, HasDiscrepancyAtLeast f C` normal form, under the same interfaces. -/
theorem stage5_forall_hasDiscrepancyAtLeast
    [FourierReductionStochasticAssumption] [LogElliottNonasymptoticAssumption]
    [VinogradovKorobovAssumption] :
    ∀ f : ℕ → ℤ, IsSignSequence f → ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  intro f hf
  exact (forall_hasDiscrepancyAtLeast_iff_not_boundedDiscrepancy f).mpr
    (stage5_notBounded f hf)

-- Consumer example (compile-only): downstream code consumes the Stage-5 boundary by name,
-- carrying the faithful analytic-core interfaces, without seeing how the target is currently
-- discharged.
example [FourierReductionStochasticAssumption] [LogElliottNonasymptoticAssumption]
    [VinogradovKorobovAssumption]
    (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f :=
  stage5_notBounded f hf

-- Compatibility example (compile-only): the Littlewood interface reaches Stage 5 through
-- `vinogradovKorobov_of_littlewoodLBound`.
example [LogElliottNonasymptoticAssumption] [LittlewoodLBoundAssumption]
    (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f :=
  stage5_notBounded f hf

end Tao2015

end MoltResearch
