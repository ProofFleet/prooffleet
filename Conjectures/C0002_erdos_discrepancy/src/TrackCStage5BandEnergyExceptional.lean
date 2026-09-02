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
* **IV-3c** (`sum_prime_integer_energy_card_free_le`, this file) — the same
  bound with the large set's cardinality eliminated by the *elementary* count
  `card_large_prime_poly_le` (V-1c), leaving no free set-theoretic quantity.
* **IV-3e-3** (`setIntegral_band_energy_exceptional_le`, this file) — the
  assembly: the elementary discretisation ladder (IV-3d/IV-3e in `DyadicMVT`)
  composed with IV-3c on each of the two parity families.
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


/-- **A2-III IV-3c — the discrete `𝒰` energy with the large set counted.**

`sum_prime_integer_energy_le` leaves one free set-theoretic quantity, the
cardinality of the large set `𝒯_L = {t ∈ 𝒯 : V₀ < ‖Q t‖}`.  That quantity is
*not* an assumption: it is bounded by the in-tree elementary chain
(Chebyshev on `|Q|^{2ℓ}`, the sharp mean-value theorem, Gallagher), whose
endpoint is `MoltResearch.card_large_prime_poly_le`.  Feeding it in gives a
bound with no residual reference to `𝒯_L`:

```
|𝒯_L| ≤ Cgal / V₀²,   Cgal := e^π·((T+1)/P + 4)·((1+λ) + λ⁻¹(2π log 2P)²)·∑_{p ∈ Y} 1/p.
```

The `1/V₀²` is the honest price of the count, and it is why the threshold `V₀`
cannot simply be sent to zero: shrinking `V₀` cheapens the integer side and
dearens the prime side at exactly the reciprocal rate.  Choosing it is the
consumer's job — [MR] takes `V₀ = (log X)^{−100}`.

`λ > 0` is the free Cauchy–Schwarz dial inherited from Gallagher's Sobolev step
(`integral_gallagher_le_param`); any positive value is admissible.

Note the prime range tightens from `P ≤ p` to `P < p`, which is what the
elementary count requires and what the `𝒰` block `Y ⊆ (P, 2P]` supplies anyway;
the large-values class's weaker `P ≤ p` follows. -/
theorem sum_prime_integer_energy_card_free_le [HalaszLargeValuesAssumption]
    [PrimeLargeValuesAssumption]
    (P : ℕ) (hP : 2 ≤ P) (Y : Finset ℕ) (hY : ∀ p ∈ Y, p.Prime)
    (hlo : ∀ p ∈ Y, P < p) (hhi : ∀ p ∈ Y, p ≤ 2*P)
    (b : ℕ → ℂ) (hb : ∀ p, ‖b p‖ ≤ 1)
    (N : ℕ) (a : ℕ → ℂ)
    (T : ℝ) (hT : 0 < T) (𝒯 : Finset ℝ)
    (hmem : ∀ t ∈ 𝒯, |t| ≤ T)
    (hsep : ∀ t ∈ 𝒯, ∀ u ∈ 𝒯, t ≠ u → 1 ≤ |t - u|)
    (V₀ δ lam : ℝ) (hV₀ : 0 < V₀) (hlam : 0 < lam)
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
        + δ^2 * (64 * (1 + (Real.exp Real.pi * ((T+1)/(P:ℝ) + 2*(2:ℝ))
                      * ((1+lam) + (1/lam)*(2*Real.pi*Real.log (2*(P:ℝ)))^2)
                      * (∑ p ∈ Y, (1:ℝ)/(p:ℝ))) / V₀^2
                  * Real.exp (-(Real.log P / (Real.log (2*T))^(3/4:ℝ)))
                  * (Real.log (2*T))^2)
              * (∑ p ∈ Y, ‖b p‖^2/(p:ℝ)^2) * (P:ℝ) / Real.log P) := by
  set 𝒯L := 𝒯.filter (fun t => V₀ < ‖∑ p ∈ Y, (b p/(p:ℂ))
      * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖) with h𝒯L
  have hsub : 𝒯L ⊆ 𝒯 := by rw [h𝒯L]; exact Finset.filter_subset _ _
  -- IV-3b, with the cardinality still free.
  have hb3 := sum_prime_integer_energy_le P hP Y hY
    (fun p hp => ⟨(hlo p hp).le, hhi p hp⟩) b N a T hT 𝒯 hmem hsep V₀ δ hV₀.le hlarge
  -- V-1c: the elementary count of the large set.
  have hmemL : ∀ t ∈ 𝒯L, t ∈ Set.Icc (-T) T :=
    fun t ht => Set.mem_Icc.mpr (abs_le.mp (hmem t (hsub ht)))
  have hsepL : ∀ t ∈ 𝒯L, ∀ u ∈ 𝒯L, t ≠ u → 1 ≤ |t - u| :=
    fun t ht u hu => hsep t (hsub ht) u (hsub hu)
  have hlargeQ : ∀ t ∈ 𝒯L, V₀ ≤ ‖∑ p ∈ Y, (b p/(p:ℂ))
      * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖ := by
    intro t ht
    rw [h𝒯L] at ht
    exact (Finset.mem_filter.mp ht).2.le
  have hcardV := MoltResearch.card_large_prime_poly_le Y hY P (by omega) hlo hhi
    b hb 𝒯L T V₀ lam hT.le hV₀.le hlam hmemL hsepL hlargeQ
  have hcard : (𝒯L.card : ℝ)
      ≤ (Real.exp Real.pi * ((T+1)/(P:ℝ) + 2*(2:ℝ))
          * ((1+lam) + (1/lam)*(2*Real.pi*Real.log (2*(P:ℝ)))^2)
          * (∑ p ∈ Y, (1:ℝ)/(p:ℝ))) / V₀^2 := by
    rw [le_div_iff₀ (by positivity)]
    exact hcardV
  -- Substituting the count is monotone: `log P > 0` since `2 ≤ P`.
  have hlogP : 0 < Real.log (P:ℝ) := by
    have : (2:ℝ) ≤ (P:ℝ) := by exact_mod_cast hP
    exact Real.log_pos (by linarith)
  have hcoef : (0:ℝ) ≤ ∑ p ∈ Y, ‖b p‖^2/(p:ℝ)^2 :=
    Finset.sum_nonneg fun p _ => by positivity
  refine hb3.trans ?_
  -- `gcongr` discharges the substitution from `hcard` in context.
  gcongr


open MeasureTheory in
/-- **A2-III IV-3e-3 — the `𝒰` band energy, assembled.**

The endpoint of the IV-3 ladder: the band energy over an arbitrary measurable
frequency set `G`, bounded with no residual reference to `G`'s structure beyond
a covering family of integer cells.

The composition is: discretise `G` into two `1`-separated families of sample
points (`setIntegral_norm_sq_mul_le_two_separated`, the elementary ladder), then
price each family by IV-3c.  Both families are bounded by the *same* expression
because the only place a family's cardinality enters is the integer
large-values term, where it is monotone and `|K'.image τ| ≤ |K|` — so the two
bounds collapse to `2 ×` one quantity.

**That factor `2` is `[MR]`'s**, and it is now accounted for honestly: it is not
slack in the paper's `∫_𝒰|QR|² ≤ 2∑_{t∈𝒯}|Q|²|R|²` but the two parity classes
of the cell decomposition, which is the price of covering the frequency line by
cells whose sample points carry no separation of their own.

`hδ` is the pointwise Halász input, and it is the only hypothesis that is not
elementary bookkeeping: on frequencies where the prime factor is large, the
integer factor must be small.  In the consumer it is discharged by the in-tree
short-sum Halász chain (the IV-0 ladder), not assumed.

The frequency bound is taken as `1 ≤ T` rather than `0 < T`: the integer
large-values weight `log(2T) + 1` must be nonnegative for the cardinality
relaxation `|K'.image τ| ≤ |K|` to be monotone, and that is the only place the
size of `T` is used at all.

The derivative `Q'`, `R'` are taken abstractly with their `HasDerivAt`
hypotheses so that a consumer supplies them from `hasDerivAt_dirichlet_poly`;
this keeps the correction term readable rather than spelling out two more
Dirichlet polynomials in the statement. -/
theorem setIntegral_band_energy_exceptional_le [HalaszLargeValuesAssumption]
    [PrimeLargeValuesAssumption]
    (P : ℕ) (hP : 2 ≤ P) (Y : Finset ℕ) (hY : ∀ p ∈ Y, p.Prime)
    (hlo : ∀ p ∈ Y, P < p) (hhi : ∀ p ∈ Y, p ≤ 2*P)
    (b : ℕ → ℂ) (hb : ∀ p, ‖b p‖ ≤ 1)
    (N : ℕ) (a : ℕ → ℂ) (T : ℝ) (hT1 : 1 ≤ T)
    (Q' R' : ℝ → ℂ)
    (hQ' : ∀ u, HasDerivAt (fun ξ => ∑ p ∈ Y, (b p/(p:ℂ))
        * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)) (Q' u) u)
    (hR' : ∀ u, HasDerivAt (fun ξ => ∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)) (R' u) u)
    (hQ'c : Continuous Q') (hR'c : Continuous R')
    (G : Set ℝ) (hGm : MeasurableSet G) (K : Finset ℤ) (τ : ℤ → ℝ)
    (hτ : ∀ k ∈ K, τ k ∈ Set.Icc (k:ℝ) ((k:ℝ)+1))
    (hcover : G ⊆ ⋃ k ∈ K, Set.Ico (k:ℝ) ((k:ℝ)+1))
    (hTmem : ∀ k ∈ K, |τ k| ≤ T)
    (V₀ δ lam : ℝ) (hV₀ : 0 < V₀) (hlam : 0 < lam)
    (hδ : ∀ t : ℝ, |t| ≤ T →
      V₀ < ‖∑ p ∈ Y, (b p/(p:ℂ))
          * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖ →
      ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ δ) :
    (∫ ξ in G, ‖∑ p ∈ Y, (b p/(p:ℂ))
            * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖^2
          * ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
            * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
      ≤ 2 * (V₀^2 * (64 * ((N:ℝ) + (K.card:ℝ) * Real.sqrt T)
                  * (Real.log (2*T) + 1)
                  * ∑ n ∈ Finset.Icc 1 N, ‖a n‖^2/(n:ℝ)^2)
            + δ^2 * (64 * (1 + (Real.exp Real.pi * ((T+1)/(P:ℝ) + 2*(2:ℝ))
                        * ((1+lam) + (1/lam)*(2*Real.pi*Real.log (2*(P:ℝ)))^2)
                        * (∑ p ∈ Y, (1:ℝ)/(p:ℝ))) / V₀^2
                    * Real.exp (-(Real.log P / (Real.log (2*T))^(3/4:ℝ)))
                    * (Real.log (2*T))^2)
                * (∑ p ∈ Y, ‖b p‖^2/(p:ℝ)^2) * (P:ℝ) / Real.log P))
        + ∑ k ∈ K, ∫ v in (k:ℝ)..((k:ℝ)+1),
            2 * ‖(∑ p ∈ Y, (b p/(p:ℂ))
                  * ((Real.fourierChar (-(Real.log p * v)) : Circle) : ℂ))
                * (∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
                  * ((Real.fourierChar (-(Real.log n * v)) : Circle) : ℂ))‖
              * ‖Q' v * (∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
                    * ((Real.fourierChar (-(Real.log n * v)) : Circle) : ℂ))
                + (∑ p ∈ Y, (b p/(p:ℂ))
                    * ((Real.fourierChar (-(Real.log p * v)) : Circle) : ℂ)) * R' v‖ := by
  classical
  have hT : (0:ℝ) < T := by linarith
  -- `1 ≤ T` is what makes the integer large-values weight `log(2T)+1` nonnegative,
  -- which is the only place the frequency bound's size is used.
  have hlog2T : (0:ℝ) ≤ Real.log (2*T) + 1 := by
    have := Real.log_nonneg (by linarith : (1:ℝ) ≤ 2*T)
    linarith
  have hchar : ∀ v : ℝ, Continuous fun ξ : ℝ =>
      ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ) := fun v =>
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hQc : Continuous fun ξ : ℝ => ∑ p ∈ Y, (b p/(p:ℂ))
      * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ) :=
    continuous_finset_sum _ fun p _ => continuous_const.mul (hchar (Real.log p))
  have hRc : Continuous fun ξ : ℝ => ∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
      * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ) :=
    continuous_finset_sum _ fun n _ => continuous_const.mul (hchar (Real.log n))
  -- The elementary discretisation into two `1`-separated parity families.
  have hlad := MoltResearch.ExpSums.setIntegral_norm_sq_mul_le_two_separated
    _ _ Q' R' hQ' hR' hQc hRc hQ'c hR'c G hGm K τ hτ hcover
  -- One family, priced by IV-3c and then card-relaxed to `|K|`.
  have hfam : ∀ K' : Finset ℤ, K' ⊆ K →
      (∀ k ∈ K', ∀ l ∈ K', k ≠ l → k + 2 ≤ l ∨ l + 2 ≤ k) →
      ∑ t ∈ K'.image τ, ‖∑ p ∈ Y, (b p/(p:ℂ))
            * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖^2
          * ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
            * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖^2
        ≤ V₀^2 * (64 * ((N:ℝ) + (K.card:ℝ) * Real.sqrt T)
                * (Real.log (2*T) + 1)
                * ∑ n ∈ Finset.Icc 1 N, ‖a n‖^2/(n:ℝ)^2)
          + δ^2 * (64 * (1 + (Real.exp Real.pi * ((T+1)/(P:ℝ) + 2*(2:ℝ))
                      * ((1+lam) + (1/lam)*(2*Real.pi*Real.log (2*(P:ℝ)))^2)
                      * (∑ p ∈ Y, (1:ℝ)/(p:ℝ))) / V₀^2
                  * Real.exp (-(Real.log P / (Real.log (2*T))^(3/4:ℝ)))
                  * (Real.log (2*T))^2)
              * (∑ p ∈ Y, ‖b p‖^2/(p:ℝ)^2) * (P:ℝ) / Real.log P) := by
    intro K' hK'K hgap
    have hτ' : ∀ k ∈ K', τ k ∈ Set.Icc (k:ℝ) ((k:ℝ)+1) :=
      fun k hk => hτ k (hK'K hk)
    have hmem : ∀ t ∈ K'.image τ, |t| ≤ T := by
      intro t ht
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
      exact hTmem k (hK'K hk)
    have hsep := MoltResearch.ExpSums.separated_of_sample_gap_two K' τ hτ' hgap
    have hlargeF : ∀ t ∈ (K'.image τ).filter (fun t => V₀ < ‖∑ p ∈ Y, (b p/(p:ℂ))
          * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖),
        ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ δ := by
      intro t ht
      obtain ⟨htm, htl⟩ := Finset.mem_filter.mp ht
      exact hδ t (hmem t htm) htl
    have hc3 := sum_prime_integer_energy_card_free_le P hP Y hY hlo hhi b hb N a
      T hT (K'.image τ) hmem hsep V₀ δ lam hV₀ hlam hlargeF
    refine hc3.trans ?_
    have hcard : ((K'.image τ).card : ℝ) ≤ (K.card : ℝ) := by
      exact_mod_cast (Finset.card_image_le).trans (Finset.card_le_card hK'K)
    gcongr
  -- Distinct integers of one parity differ by at least `2`.
  have hgapE : ∀ k ∈ K.filter (fun k => Even k), ∀ l ∈ K.filter (fun k => Even k),
      k ≠ l → k + 2 ≤ l ∨ l + 2 ≤ k := by
    intro k hk l hl hkl
    obtain ⟨m, hm⟩ := (Finset.mem_filter.mp hk).2
    obtain ⟨n, hn⟩ := (Finset.mem_filter.mp hl).2
    omega
  have hgapO : ∀ k ∈ K.filter (fun k => ¬ Even k),
      ∀ l ∈ K.filter (fun k => ¬ Even k), k ≠ l → k + 2 ≤ l ∨ l + 2 ≤ k := by
    intro k hk l hl hkl
    have hke := (Finset.mem_filter.mp hk).2
    have hle := (Finset.mem_filter.mp hl).2
    rw [Int.not_even_iff_odd] at hke hle
    obtain ⟨m, hm⟩ := hke
    obtain ⟨n, hn⟩ := hle
    omega
  have hE := hfam _ (Finset.filter_subset _ _) hgapE
  have hO := hfam _ (Finset.filter_subset _ _) hgapO
  linarith [hlad, hE, hO]

end Tao2015

end MoltResearch
