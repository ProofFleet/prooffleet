import Conjectures.C0002_erdos_discrepancy.src.TrackCStage4
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Fourier
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Elliott

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

**Current proof status (deliberate, per the card):** the body is wired through the existing
Stage-4 boundary, hence ultimately through the Stage-2 stub axiom — the analytic-core instances
are carried in the *signature* but not yet consumed. The plan of record: when the derivation
(C) lands (van der Corput expansion + pretentious branch, §3–§4 of arXiv:1509.05363), this
theorem is re-proved from `FourierReductionStochasticAssumption.reduce` + Theorem 1.8 built on
`LogElliottNonasymptoticAssumption`, and the Stage-2 stub axiom is retired. Downstream
consumers of `stage5_notBounded` are insulated from that switch — only this file's proof body
changes.
-/

namespace MoltResearch

namespace Tao2015

/-- **Stage-5 conditional target**: EDP for all sign sequences, carried under the faithful
analytic-core interfaces (A) `FourierReductionStochasticAssumption` and
(B) `LogElliottNonasymptoticAssumption`.

Currently wired through the Stage-4 boundary (hence the Stage-2 stub); to be re-proved from
(A) + the derivation (C) when it lands, retiring the stub. The signature — including the two
instance arguments — is the stable Stage-5 contract.
-/
theorem stage5_notBounded
    [FourierReductionStochasticAssumption] [LogElliottNonasymptoticAssumption] :
    ∀ f : ℕ → ℤ, IsSignSequence f → ¬ BoundedDiscrepancy f := by
  intro f hf
  exact stage4_notBounded f hf

/-- Stage-5 surface-statement variant: unbounded discrepancy in the
`∀ C, HasDiscrepancyAtLeast f C` normal form, under the same analytic-core interfaces. -/
theorem stage5_forall_hasDiscrepancyAtLeast
    [FourierReductionStochasticAssumption] [LogElliottNonasymptoticAssumption] :
    ∀ f : ℕ → ℤ, IsSignSequence f → ∀ C : ℕ, HasDiscrepancyAtLeast f C := by
  intro f hf
  exact stage4_forall_hasDiscrepancyAtLeast f hf

-- Consumer example (compile-only): downstream code consumes the Stage-5 boundary by name,
-- carrying the faithful analytic-core interfaces, without seeing how the target is currently
-- discharged.
example [FourierReductionStochasticAssumption] [LogElliottNonasymptoticAssumption]
    (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f :=
  stage5_notBounded f hf

-- Compatibility example (compile-only): holders of the stronger deterministic Fourier
-- first-cut still reach Stage 5 on the (A) side, via the strength-ordering instance
-- `FourierReductionStochasticAssumption.ofDeterministic`.
example [FourierReductionAssumption] [LogElliottNonasymptoticAssumption]
    (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f :=
  stage5_notBounded f hf

end Tao2015

end MoltResearch
