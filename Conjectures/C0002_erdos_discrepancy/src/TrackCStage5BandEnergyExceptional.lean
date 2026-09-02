import Conjectures.C0002_erdos_discrepancy.src.Interfaces.LargeValues
import MoltResearch.DiscrepancyAnalytic

/-!
# Track C: Stage 5 — the `𝒰` band energy (issue #3044, Track R, A2-III IV-3)

The exceptional-frequency leg of the `[mrt]` A.2 band estimate.  Every other
frequency range closes elementarily and unconditionally (`band_energy_outer_le`,
`band_energy_level_one_le`, `band_energy_level_le_of_prev_large`); `𝒰` does not,
and the two large-values classes of `Interfaces/LargeValues.lean` are exactly
what it needs — see that module's docstring for why they are assumptions.

This file carries the *conditional* half of the ladder.  The elementary half
lives in `MoltResearch/`: the threshold split `sum_norm_sq_mul_split_le` (IV-3a)
and, later, the discretisation of `∫_𝒰` against a well-spaced net (IV-3d).  The
split is what makes the two halves separable — it leaves precisely the two
left-hand sides the classes bound, and nothing else.

Units:

* **IV-3b** (`sum_prime_integer_energy_le`, this file) — the discrete `𝒰`
  energy: [MR, Lemma 2] steps 3–5 with both large-values inputs discharged.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- **A2-III IV-3b — the discrete `𝒰` energy, conditional.**

Steps 3–5 of the `𝒰` treatment ([MR, Lemma 2]).  At `1`-separated points of
`[-T, T]`, the energy of a product `Q·R` of a prime-supported Dirichlet
polynomial over `Y ⊆ [P, 2P]` and an integer-supported one of length `N` is cut
at the threshold `V₀` on `Q` (IV-3a, `sum_norm_sq_mul_split_le`) and each half is
then priced by the large-values theorem that matches its support:

* below the threshold `Q` is worth `V₀`, and the surviving `∑_{t ∈ 𝒯} ‖R t‖²`
  goes to `HalaszLargeValuesAssumption` (Iwaniec–Kowalski Thm 9.6);
* above it `R` is worth its pointwise Halász bound `δ` — supplied by the caller
  as `hlarge`, and discharged in the consumer by the in-tree short-sum Halász
  chain (IV-0) — and the surviving `∑_{t ∈ 𝒯_L} ‖Q t‖²` goes to
  `PrimeLargeValuesAssumption` ([MR] Lemma 8).

The asymmetry is the whole point of the split: the integer theorem is applied on
*all* of `𝒯`, the prime theorem only on the large set `𝒯_L`, whose cardinality
the caller controls by the elementary `card_large_prime_poly_le` (V-1c).  It is
the prime theorem's off-diagonal `|𝒯_L|·P·exp(−log P/(log 2T)^{3/4})` — rather
than `|𝒯_L|·√T` — that makes the assembly close; see the design report §5. -/
theorem sum_prime_integer_energy_le [HalaszLargeValuesAssumption]
    [PrimeLargeValuesAssumption]
    (P : ℕ) (hP : 2 ≤ P) (Y : Finset ℕ) (hY : ∀ p ∈ Y, p.Prime)
    (hYP : ∀ p ∈ Y, P ≤ p ∧ p ≤ 2*P) (b : ℕ → ℂ)
    (N : ℕ) (a : ℕ → ℂ)
    (T : ℝ) (hT : 0 < T) (𝒯 : Finset ℝ)
    (hmem : ∀ t ∈ 𝒯, |t| ≤ T)
    (hsep : ∀ t ∈ 𝒯, ∀ u ∈ 𝒯, t ≠ u → 1 ≤ |t - u|)
    (V₀ δ : ℝ) (hV₀ : 0 ≤ V₀)
    (hlarge : ∀ t ∈ 𝒯.filter (fun t => V₀ < ‖∑ p ∈ Y, (b p/(p:ℂ))
        * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖),
      ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
        * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ δ) :
    ∑ t ∈ 𝒯, ‖∑ p ∈ Y, (b p/(p:ℂ))
          * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖^2
        * ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖^2
      ≤ V₀^2 * (64 * ((N:ℝ) + (𝒯.card:ℝ) * Real.sqrt T) * (Real.log (2*T) + 1)
                  * ∑ n ∈ Finset.Icc 1 N, ‖a n‖^2/(n:ℝ)^2)
        + δ^2 * (64 * (1 + ((𝒯.filter (fun t => V₀ < ‖∑ p ∈ Y, (b p/(p:ℂ))
                    * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖)).card : ℝ)
                  * Real.exp (-(Real.log P / (Real.log (2*T))^(3/4:ℝ)))
                  * (Real.log (2*T))^2)
              * (∑ p ∈ Y, ‖b p‖^2/(p:ℝ)^2) * (P:ℝ) / Real.log P) := by
  -- The large set inherits both `𝒯`-side hypotheses by restriction.
  set 𝒯L := 𝒯.filter (fun t => V₀ < ‖∑ p ∈ Y, (b p/(p:ℂ))
      * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖) with h𝒯L
  have hsub : 𝒯L ⊆ 𝒯 := by rw [h𝒯L]; exact Finset.filter_subset _ _
  have hmemL : ∀ t ∈ 𝒯L, |t| ≤ T := fun t ht => hmem t (hsub ht)
  have hsepL : ∀ t ∈ 𝒯L, ∀ u ∈ 𝒯L, t ≠ u → 1 ≤ |t - u| :=
    fun t ht u hu => hsep t (hsub ht) u (hsub hu)
  -- IV-3a: the threshold split.
  have hsplit := MoltResearch.ExpSums.sum_norm_sq_mul_split_le 𝒯
    (fun t => ∑ p ∈ Y, (b p/(p:ℂ))
      * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ))
    (fun t => ∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
      * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)) V₀ δ hV₀ hlarge
  -- IK Thm 9.6 on all of `𝒯`; [MR] Lemma 8 on the large set only.
  have hint := HalaszLargeValuesAssumption.bound N a T 𝒯 hT hmem hsep
  have hpri := PrimeLargeValuesAssumption.bound P Y hY hYP b T 𝒯L hP hT hmemL hsepL
  have hV₀sq : (0:ℝ) ≤ V₀^2 := sq_nonneg _
  have hδsq : (0:ℝ) ≤ δ^2 := sq_nonneg _
  calc ∑ t ∈ 𝒯, ‖∑ p ∈ Y, (b p/(p:ℂ))
            * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖^2
          * ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
            * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖^2
      ≤ V₀^2 * (∑ t ∈ 𝒯, ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
            * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖^2)
          + δ^2 * ∑ t ∈ 𝒯L, ‖∑ p ∈ Y, (b p/(p:ℂ))
            * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖^2 := hsplit
    _ ≤ V₀^2 * (64 * ((N:ℝ) + (𝒯.card:ℝ) * Real.sqrt T) * (Real.log (2*T) + 1)
                  * ∑ n ∈ Finset.Icc 1 N, ‖a n‖^2/(n:ℝ)^2)
        + δ^2 * (64 * (1 + (𝒯L.card : ℝ)
                  * Real.exp (-(Real.log P / (Real.log (2*T))^(3/4:ℝ)))
                  * (Real.log (2*T))^2)
              * (∑ p ∈ Y, ‖b p‖^2/(p:ℝ)^2) * (P:ℝ) / Real.log P) := by
        gcongr

end Tao2015

end MoltResearch
