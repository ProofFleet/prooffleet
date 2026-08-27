import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5PrimeBlockMajorArc
import MoltResearch.Discrepancy.VinogradovTypeI

/-!
# Track C: the prime-block classification — `PrimeBlockMajorArcAssumption` discharged (Track R of #3044, Leg B)

The R4v campaign, assembled: Vaughan's identity over the dyadic block at the
dyadic cube root `U = V = 2^{⌊log₂n₀⌋/3}`, all three legs priced through the
refined counting lemma (first block de-fanged by coprimality), the coupled
Type II estimate priced per dyadic modulus block, antitone Abel summation at
the weight `1/(p·log p)`, the prime-power remainder counted by `(p,k) ↦ p^k`,
and Dirichlet approximation at `n = ⌊n₀/log²⁰n₀⌋` give the classification
(`primeBlock_classification`): a prime-block exponential sum of size at least
`c/log n₀` forces a major arc of denominator `≤ log²⁰n₀` and width
`≤ log²⁰n₀/(n₀q)`.

This file closes Leg B of the weak interface pair: the block set is the prime
filter of `(n₀, 2n₀]` (`primeBlock_eq_filter`), and the classification
discharges `PrimeBlockMajorArcAssumption` with `B = 20`, `C = 1` — the
assumption holds unconditionally, with standard axioms only (pinned in
`TrackCAxiomAudit`).
-/

namespace MoltResearch

namespace Tao2015

open Finset ExpSums

/-- `primeBlock` is the prime filter of the dyadic block `(n₀, 2n₀]`. -/
theorem primeBlock_eq_filter (n₀ : ℕ) :
    primeBlock n₀ = (Finset.Ioc n₀ (2*n₀)).filter (fun p => p.Prime) := by
  ext p
  simp only [primeBlock, Finset.mem_filter, Nat.mem_primesBelow,
    Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hlt, hp⟩, hgt⟩
    exact ⟨⟨hgt, by omega⟩, hp⟩
  · rintro ⟨⟨hgt, hle⟩, hp⟩
    exact ⟨⟨by omega, hp⟩, hgt⟩

/-- **The prime-block major-arc classification holds unconditionally**
(Track R, #3044): the Vinogradov Type I/II machine discharges the
assumption with `B = 20`, `C = 1`. -/
instance instPrimeBlockMajorArcAssumption : PrimeBlockMajorArcAssumption := by
  refine ⟨fun c hc => ?_⟩
  obtain ⟨N₀, hN₀⟩ := primeBlock_classification c hc
  refine ⟨N₀, 20, 1, one_pos, fun n₀ hn₀ β θ hθ1 hθ2 => ?_⟩
  have hnorm : c / Real.log (n₀:ℝ)
      ≤ ‖∑ p ∈ (Finset.Ioc n₀ (2*n₀)).filter (fun p => p.Prime),
          ((1/(p:ℝ) : ℝ):ℂ) * e ((p:ℝ)*β)‖ := by
    rw [← primeBlock_eq_filter]
    exact le_trans hθ1 hθ2
  obtain ⟨a, q, hq1, hqB, harc⟩ := hN₀ n₀ hn₀ β hnorm
  refine ⟨a, q, hq1, ?_, ?_⟩
  · rw [one_mul]
    exact hqB
  · rw [one_mul]
    exact harc

end Tao2015

end MoltResearch
