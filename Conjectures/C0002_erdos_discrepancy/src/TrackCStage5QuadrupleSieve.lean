import MoltResearch.Discrepancy
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Elliott

/-!
# Track C: Stage 5 — the prime-quadruple sieve interface (E6f of issue #2946)

The **second permanent analytic input** of the Elliott campaign, alongside
Matomäki–Radziwiłł: the count of additive prime quadruples in a dyadic block,

  `#{(p₁,p₂,p₃,p₄) ∈ 𝒫(n₀)⁴ : p₁ + p₂ = p₃ + p₄} ≪ n₀³ / (log n₀)⁴`,

where `𝒫(n₀)` is the block of primes in `(n₀, 2n₀]`. The paper (arXiv:1509.05422,
proof of the restriction lemma, footnote) obtains this from a standard upper-bound
sieve (Selberg), or alternatively from the Green–Tao restriction estimate
[gt-selberg, Prop. 4.2]; either route is a cited input exactly like the
Matomäki–Radziwiłł theorem itself. Mathlib's `NumberTheory.SelbergSieve` provides
the sieve framework from which this count should eventually be dischargeable.

Through the `L⁴` identity and Markov (`sum_normPow4_zCharSum`,
`card_filter_le_sum_normPow4`), this bound makes the major-frequency set of the
circle method `H`-independent — which is what lets the Matomäki–Radziwiłł
smallness (fixed before the scale is chosen) win.

No instance of this class is (or may be) declared until the count is actually
formalized; consumers carry it as a hypothesis.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The block of primes in `(n₀, 2n₀]`. -/
noncomputable def primeBlock (n₀ : ℕ) : Finset ℕ :=
  (2 * n₀ + 1).primesBelow.filter (fun p => n₀ < p)

/-- **Prime-quadruple sieve assumption** (arXiv:1509.05422 §3, restriction lemma
footnote; [gt-selberg, Prop. 4.2]): the additive-quadruple count in a dyadic
prime block saves four logarithms. -/
class PrimeQuadrupleCountAssumption : Prop where
  bound : ∃ C : ℝ, 0 < C ∧ ∀ n₀ : ℕ, 2 ≤ n₀ →
    (((((primeBlock n₀ ×ˢ primeBlock n₀) ×ˢ
        (primeBlock n₀ ×ˢ primeBlock n₀)).filter
      (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)).card : ℝ)
      ≤ C * n₀ ^ 3 / Real.log n₀ ^ 4)

/-- Consumer-facing restatement. -/
theorem primeQuadrupleCount_bound [inst : PrimeQuadrupleCountAssumption] :
    ∃ C : ℝ, 0 < C ∧ ∀ n₀ : ℕ, 2 ≤ n₀ →
      (((((primeBlock n₀ ×ˢ primeBlock n₀) ×ˢ
          (primeBlock n₀ ×ˢ primeBlock n₀)).filter
        (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)).card : ℝ)
        ≤ C * n₀ ^ 3 / Real.log n₀ ^ 4) :=
  inst.bound

end Tao2015

end MoltResearch
