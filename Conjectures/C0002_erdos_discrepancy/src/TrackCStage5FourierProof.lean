import MoltResearch.Discrepancy
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Derivation
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5VanDerCorputProof
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5BCCWrapper

/-!
# Track C: Stage 5 — the §2 Fourier reduction, proved (Tao 2015 §2)

**`FourierReductionStochasticAssumption` is discharged unconditionally** — the §2
reduction of arXiv:1509.05363 is now a theorem, not a hypothesis
(`Problems/tao2015_derivation_c.md`, issue #2920).

Given a bounded-discrepancy sign sequence `f`, the nucleus chain (P1–P8,
`MoltResearch/Discrepancy/`) produces the paper's random completely multiplicative
function: the windowed Plancherel identity converts the discrepancy bound into a
spectral second-moment bound at every scale `X`; the `‖F̂‖²` law is pushed to the
compact space `PrimeData` of unimodular prime data; and an ultrafilter limit
(`exists_limit_law`) yields a single law `ν` with
`∫ ‖∑_{j≤n} toCM ω j‖² dν ≤ B² + 1` for **all** `n`. Packaging `toCM` as a
`StochasticMultiplicative ν` gives the instance.

Consequences recorded here:

- `instance : FourierReductionStochasticAssumption` — the §2 box of the card.
- `edp_of_logElliott_vinogradovKorobov` — **the Erdős discrepancy theorem for all sign
  sequences**, conditional on exactly the two permanent deep inputs
  `{LogElliottNonasymptoticAssumption, VinogradovKorobovAssumption}`: the entire
  derivation (C) of Tao 2015 is now formalized, with the two analytic-number-theory
  black boxes as the only remaining hypotheses.
-/

namespace MoltResearch

namespace Tao2015

open MeasureTheory

/-- **The §2 Fourier reduction, proved** (Tao 2015, arXiv:1509.05363 §2): a
bounded-discrepancy sign sequence yields a stochastic completely multiplicative
unimodular function with uniformly bounded second moment — the limiting spectral law
on the compact space of prime data, carrying the constant `B² + 1`. -/
instance : FourierReductionStochasticAssumption where
  reduce := by
    rintro f hf ⟨B, hB⟩
    obtain ⟨ν, hν⟩ := exists_limit_law f hf hB
    refine ⟨PrimeData, inferInstance, (ν : Measure PrimeData), ν.2,
      ⟨fun ω => toCM ω, fun n => (continuous_toCM_apply n).measurable,
        ae_of_all _ toCM_completelyMultiplicativeC, ae_of_all _ toCM_unimodular⟩,
      (B : ℝ) ^ 2 + 1, fun n => ?_⟩
    exact hν n

/-- **The Erdős discrepancy theorem, conditional on the two deep inputs** (Tao 2015,
derivation (C) complete): every sign sequence has unbounded discrepancy, given the
nonasymptotic Elliott estimate (§3 input) and the Vinogradov–Korobov zero-free region
(§4 input). Every other step of arXiv:1509.05363 — the §2 Fourier reduction, the §3
van der Corput argument, and the §4 Borwein–Choi–Coons branch — is formalized
unconditionally. -/
theorem edp_of_logElliott_vinogradovKorobov
    [LogElliottNonasymptoticAssumption] [VinogradovKorobovAssumption]
    (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f :=
  notBounded_of_derivation f hf

end Tao2015

end MoltResearch
