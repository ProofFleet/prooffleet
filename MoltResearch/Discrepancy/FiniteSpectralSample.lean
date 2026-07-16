import MoltResearch.Discrepancy.SpectralWindowBound
import MoltResearch.Discrepancy.CMOfPrimes

/-!
# Discrepancy: the finite spectral sample

Tao 2015 §2 (arXiv:1509.05363, `Problems/tao2015_derivation_c.md`, issue #2920): the
finite-scale random completely multiplicative function `g_ξ(p) = e(ξ_p/M)` and its
second-moment bound, in purely finite form (the probability packaging is the
pushforward step of the campaign).

* `spectralSample X M ξ = cmOfPrimes (p ↦ e(ξ_p/M) below the cutoff, 1 above)` — a
  completely multiplicative unimodular function for **every** frequency `ξ`.
* `spectralSample_apply` — on `[1, X]` the sample **is** the pairing character:
  `g_ξ(j) = prodChar (piExp j) ξ` (the factorization product collapses onto the
  exponent vector).
* `weighted_normSq_apSumC_spectralSample_le` — the second moment against the spectral
  weights: `∑_ξ ‖F̂(ξ)‖²·‖∑_{j≤n} g_ξ(j)‖² ≤ B² + 1` for `n ≤ X`, `M ≥ r·log₂X·X²` —
  i.e. `𝔼‖∑_{j≤n} 𝐠(j)‖² ≤ B² + 1` once `‖F̂‖²` is packaged as a law (`P7`).
-/

namespace MoltResearch

open Finset

variable {X M : ℕ} [NeZero M]

/-- The §2 random prime data: `p ↦ e(ξ_p/M)` below the cutoff, `1` above. -/
noncomputable def spectralPrimeData (X M : ℕ) [NeZero M]
    (ξ : PrimeIdx X → ZMod M) : ℕ → ℂ :=
  fun p => if h : p ∈ (X + 1).primesBelow then ZMod.stdAddChar (ξ ⟨p, h⟩) else 1

/-- The finite-scale random completely multiplicative function of §2. -/
noncomputable def spectralSample (X M : ℕ) [NeZero M]
    (ξ : PrimeIdx X → ZMod M) : ℕ → ℂ :=
  cmOfPrimes (spectralPrimeData X M ξ)

/-- Every sample is completely multiplicative. -/
theorem spectralSample_completelyMultiplicativeC (ξ : PrimeIdx X → ZMod M) :
    CompletelyMultiplicativeC (spectralSample X M ξ) :=
  cmOfPrimes_completelyMultiplicativeC _

/-- Every sample is unimodular. -/
theorem spectralSample_unimodular (ξ : PrimeIdx X → ZMod M) :
    Unimodular (spectralSample X M ξ) := by
  refine cmOfPrimes_unimodular fun p _ => ?_
  unfold spectralPrimeData
  split
  · rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  · norm_num

/-- **The sample is the pairing character on `[1, X]`**: the factorization product of
the prime data collapses onto the exponent vector of `j`. -/
theorem spectralSample_apply {j : ℕ} (hj1 : 1 ≤ j) (hjX : j ≤ X)
    (ξ : PrimeIdx X → ZMod M) :
    spectralSample X M ξ j = prodChar (piExp X M j) ξ := by
  unfold spectralSample cmOfPrimes prodChar
  have hsub : j.factorization.support ⊆ (X + 1).primesBelow := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors
      (by rwa [Nat.support_factorization] at hp)
    have hpdvd : p ∣ j := Nat.dvd_of_mem_primeFactors
      (by rwa [Nat.support_factorization] at hp)
    rw [Nat.mem_primesBelow]
    exact ⟨lt_of_le_of_lt (le_trans (Nat.le_of_dvd (by omega) hpdvd) hjX)
      (by omega), hpp⟩
  -- extend the factorization product over all primes below the cutoff
  have hL : j.factorization.prod (fun p k => spectralPrimeData X M ξ p ^ k)
      = ∏ p ∈ (X + 1).primesBelow,
          spectralPrimeData X M ξ p ^ j.factorization p :=
    Finset.prod_subset hsub fun p _ hps => by
      rw [Finsupp.notMem_support_iff.mp hps]
      exact pow_zero _
  rw [hL, Finset.univ_eq_attach, ← Finset.prod_attach ((X + 1).primesBelow)
    (fun p => spectralPrimeData X M ξ p ^ j.factorization p)]
  refine Finset.prod_congr rfl fun p _ => ?_
  have hdata : spectralPrimeData X M ξ p.1 = ZMod.stdAddChar (ξ p) := by
    unfold spectralPrimeData
    rw [dif_pos p.2]
  rw [hdata, ← AddChar.map_nsmul_eq_pow]
  congr 1
  unfold piExp
  rw [nsmul_eq_mul]

/-- **The finite second-moment bound** (Tao 2015 §2): against the spectral weights, the
squared partial sums of the samples average to at most `B² + 1` for `n ≤ X` — the
statement that becomes `𝔼‖∑_{j ≤ n} 𝐠_X(j)‖² ≤ B² + 1` once `‖F̂‖²` is a law. -/
theorem weighted_normSq_apSumC_spectralSample_le {f : ℕ → ℤ} (hs : IsSignSequence f)
    {B : ℕ} (hB : ∀ d n : ℕ, d > 0 → (apSum f d n).natAbs ≤ B)
    {n : ℕ} (hnX : n ≤ X)
    (hM : Fintype.card (PrimeIdx X) * Nat.log 2 X * X ^ 2 ≤ M) :
    ∑ ξ : PrimeIdx X → ZMod M,
        ‖prodDFT (smoothEval f X) ξ‖ ^ 2
          * ‖apSumC (spectralSample X M ξ) 1 n‖ ^ 2
      ≤ (B : ℝ) ^ 2 + 1 := by
  have heq : ∀ ξ : PrimeIdx X → ZMod M,
      apSumC (spectralSample X M ξ) 1 n
        = ∑ j ∈ Finset.Icc 1 n, prodChar (piExp X M j) ξ := by
    intro ξ
    unfold apSumC
    rw [show Finset.Icc 1 n = Finset.Ico 1 (n + 1) from Finset.val_inj.mp rfl]
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, mul_one]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [spectralSample_apply (by omega) (by omega)]
    congr 2
    omega
  calc ∑ ξ : PrimeIdx X → ZMod M,
      ‖prodDFT (smoothEval f X) ξ‖ ^ 2 * ‖apSumC (spectralSample X M ξ) 1 n‖ ^ 2
      = ∑ ξ : PrimeIdx X → ZMod M,
        ‖prodDFT (smoothEval f X) ξ‖ ^ 2
          * ‖∑ j ∈ Finset.Icc 1 n, prodChar (piExp X M j) ξ‖ ^ 2 := by
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [heq ξ]
    _ ≤ (B : ℝ) ^ 2 + 1 := spectral_window_bound hs hB hnX hM

end MoltResearch
