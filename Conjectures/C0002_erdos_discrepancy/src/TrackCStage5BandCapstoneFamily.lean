import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5BandCapstone

/-!
# The band capstone with the factorisation seam in energy form (Track R, A2-III, VI-1h)

`band_energy_le_budget_of_exceptional` presents the exceptional part's integrand
*pointwise* as one product: a prime polynomial over a single dyadic prime set
`Y ⊆ (P, 2P]` times an integer polynomial.  That is not what `[MR]`'s
decomposition lemma supplies.  II-2 (`intervalIntegral_norm_sq_cell_replace_le`)
is an *energy* statement, cell by cell: after N3-f, II-1 and the cell-uniform
replacement, the typical-set polynomial is `∑_v (cell_v)·Z_{q_v}` plus collars and
a collision term, and only Cauchy–Schwarz over the `e`-adic cells turns that sum
into products the two large-values interfaces can see.  A single `Y` would have
to be one cell, and one cell cannot carry typicality — its prime mass is
`O(1/(N log P))`.

This module re-cuts the seam accordingly.  The exceptional part's energy is
bounded by a constant times a *sum over a cell family* of product energies, plus
an error, and each cell brings its own `𝒰`-leg data.  The single-set statement
is the case of one cell with `C = 1`, `E = 0`.  Kept out of the capstone file so
that the two chains do not serialise on it.
-/

namespace MoltResearch

namespace Tao2015

open MeasureTheory in
/-- **A2-III VI-1h-1 — the band capstone with the factorisation seam over a cell
family.**

`band_energy_le_budget_of_exceptional` with its `𝒰`-leg data indexed by a
finite family `I` of cells.  The factorisation hypothesis is now an energy
inequality,

  `∫_{part u} ‖F‖² ≤ C·∑_{v∈I} ∫_{part u} ‖∑_{p∈Y_v} (b_v p/p)e(−ξ log p)‖²·‖∑_{n≤N_v} (a_v n/n)e(−ξ log n)‖² + E`,

which is the shape the `[MR]` decomposition produces: `C` is the Cauchy–Schwarz
factor over the cells and `E` collects the replacement, collar and collision
energies.  Each cell is priced by `setIntegral_band_energy_exceptional_le_budget`
at its own share `κ' v`, and `hfitU` asks that the weighted total, `C·∑κ'·𝔅 + E`,
fit into the exceptional part's share of the *bare* energy, `κ_u·𝔅/Cw`.

**Two hypotheses of the single-set statement disappear.**  `hintU`, the
integrability of the product on the exceptional part, is no longer needed —
the inequality is the hypothesis, and the cell lemma bounds an integral without
asking it to exist.  And the fit no longer mentions the product's constants at
all: it is stated in the shares, so that a consumer who has priced each cell
composes with one sum.

The per-cell data (`P v`, `Y v`, `b v`, `N v`, `a v`, `δ v`, `lam v`, the three
groups) are quantified over `v ∈ I` only; the frequency cover `K` and the range
`T` are shared, since the cells partition the primes, not the frequencies. -/
theorem band_energy_le_budget_of_exceptional_family [HalaszLargeValuesAssumption]
    [PrimeLargeValuesAssumption] {ι : Type*} [DecidableEq ι] {ι' : Type*}
    (F : ℝ → ℂ) (w : ℝ → ℝ) (hw0 : ∀ ξ, 0 ≤ w ξ)
    (Cw : ℝ) (hCw : 0 < Cw) (hwC : ∀ ξ, w ξ ≤ Cw)
    (G : Set ℝ) (𝒮 : Finset ι) (part : ι → Set ℝ)
    (hmeas : ∀ i ∈ 𝒮, MeasurableSet (part i))
    (hdisj : Set.Pairwise (↑𝒮) (Function.onFun Disjoint part))
    (hcover : G ⊆ ⋃ i ∈ 𝒮, part i)
    (hint : ∀ i ∈ 𝒮, IntegrableOn (fun ξ => ‖F ξ‖^2) (part i))
    (hintw : ∀ i ∈ 𝒮, IntegrableOn (fun ξ => ‖F ξ‖^2 * w ξ) (part i))
    (κ : ι → ℝ) (c₃ ε ρ : ℝ) (hc₃ : 0 ≤ c₃) (hρ : 0 ≤ ρ)
    (hκ : ∑ i ∈ 𝒮, κ i ≤ 1)
    (u : ι) (hu : u ∈ 𝒮)
    (hleg : ∀ i ∈ 𝒮, i ≠ u → Cw * ∫ ξ in part i, ‖F ξ‖^2
      ≤ κ i * bandBudget c₃ ε ρ)
    (I : Finset ι') (P : ι' → ℕ) (hP : ∀ v ∈ I, 2 ≤ P v)
    (Y : ι' → Finset ℕ) (hY : ∀ v ∈ I, ∀ p ∈ Y v, p.Prime)
    (hlo : ∀ v ∈ I, ∀ p ∈ Y v, P v < p) (hhi : ∀ v ∈ I, ∀ p ∈ Y v, p ≤ 2 * P v)
    (b : ι' → ℕ → ℂ) (hb : ∀ v ∈ I, ∀ p, ‖b v p‖ ≤ 1)
    (N : ι' → ℕ) (a : ι' → ℕ → ℂ) (T : ℝ) (hT1 : 1 ≤ T)
    (K : Finset ℤ)
    (hcoverU : part u ⊆ ⋃ k ∈ K, Set.Ico (k:ℝ) ((k:ℝ)+1))
    (hKT : ∀ k ∈ K, -T ≤ (k:ℝ) ∧ (k:ℝ) + 1 ≤ T)
    (δ lam : ι' → ℝ) (hδ0 : ∀ v ∈ I, 0 < δ v) (hlam : ∀ v ∈ I, 0 < lam v)
    (hδ : ∀ v ∈ I, ∀ t : ℝ, |t| ≤ T →
      ‖∑ n ∈ Finset.Icc 1 (N v), (a v n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ δ v)
    (C E : ℝ) (hC0 : 0 ≤ C)
    (hfac : (∫ ξ in part u, ‖F ξ‖^2)
      ≤ C * ∑ v ∈ I, (∫ ξ in part u, ‖∑ p ∈ Y v, (b v p/(p:ℂ))
            * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖^2
          * ‖∑ n ∈ Finset.Icc 1 (N v), (a v n/(n:ℂ))
            * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2) + E)
    (Aint Bpri Γ : ι' → ℝ)
    (hAint : ∀ v ∈ I, Aint v = 64 * ((N v:ℝ) + (K.card:ℝ) * Real.sqrt T)
      * (Real.log (2*T) + 1) * ∑ n ∈ Finset.Icc 1 (N v), ‖a v n‖^2/(n:ℝ)^2)
    (hBpri : ∀ v ∈ I, Bpri v = 64 * (∑ p ∈ Y v, ‖b v p‖^2/(p:ℝ)^2)
      * (P v:ℝ) / Real.log (P v))
    (hΓ : ∀ v ∈ I, Γ v = (Real.exp Real.pi * ((T+1)/(P v:ℝ) + 2*(2:ℝ))
          * ((1+lam v) + (1/lam v)*(2*Real.pi*Real.log (2*(P v:ℝ)))^2)
          * (∑ p ∈ Y v, (1:ℝ)/(p:ℝ)))
        * Real.exp (-(Real.log (P v) / (Real.log (2*T))^(3/4:ℝ)))
        * (Real.log (2*T))^2)
    (hA0 : ∀ v ∈ I, 0 < Aint v) (hB0 : ∀ v ∈ I, 0 < Bpri v)
    (hΓ0 : ∀ v ∈ I, 0 < Γ v)
    (κ' : ι' → ℝ)
    (hfit : ∀ v ∈ I, 2 * ((δ v)^2 * Bpri v
        + 2 * δ v * Real.sqrt (Aint v * (Bpri v * Γ v)))
      ≤ κ' v * bandBudget c₃ ε ρ)
    (hfitU : C * (∑ v ∈ I, κ' v) * bandBudget c₃ ε ρ + E
      ≤ κ u * bandBudget c₃ ε ρ / Cw) :
    (∫ ξ in G, ‖F ξ‖^2 * w ξ) ≤ bandBudget c₃ ε ρ := by
  -- Each cell's product energy meets its share, from the two large-values
  -- interfaces.
  have hcell : ∀ v ∈ I,
      (∫ ξ in part u, ‖∑ p ∈ Y v, (b v p/(p:ℂ))
            * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖^2
          * ‖∑ n ∈ Finset.Icc 1 (N v), (a v n/(n:ℂ))
            * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
        ≤ κ' v * bandBudget c₃ ε ρ := fun v hv =>
    setIntegral_band_energy_exceptional_le_budget (P v) (hP v hv) (Y v) (hY v hv)
      (hlo v hv) (hhi v hv) (b v) (hb v hv) (N v) (a v) T hT1 (part u) K hcoverU
      hKT (δ v) (lam v) (hδ0 v hv) (hlam v hv) (hδ v hv) (Aint v) (Bpri v) (Γ v)
      (hAint v hv) (hBpri v hv) (hΓ v hv) (hA0 v hv) (hB0 v hv) (hΓ0 v hv)
      c₃ ε ρ (κ' v) (hfit v hv)
  -- The exceptional part: the family seam, then the shares summed.
  have hUleg : Cw * ∫ ξ in part u, ‖F ξ‖^2 ≤ κ u * bandBudget c₃ ε ρ := by
    have hsum := Finset.sum_le_sum hcell
    have h1 : (∫ ξ in part u, ‖F ξ‖^2) ≤ κ u * bandBudget c₃ ε ρ / Cw := by
      calc (∫ ξ in part u, ‖F ξ‖^2)
          ≤ C * ∑ v ∈ I, (∫ ξ in part u, ‖∑ p ∈ Y v, (b v p/(p:ℂ))
                * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖^2
              * ‖∑ n ∈ Finset.Icc 1 (N v), (a v n/(n:ℂ))
                * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2) + E :=
            hfac
        _ ≤ C * ∑ v ∈ I, κ' v * bandBudget c₃ ε ρ + E :=
            add_le_add (mul_le_mul_of_nonneg_left hsum hC0) le_rfl
        _ = C * (∑ v ∈ I, κ' v) * bandBudget c₃ ε ρ + E := by
            rw [← Finset.sum_mul, ← mul_assoc]
        _ ≤ κ u * bandBudget c₃ ε ρ / Cw := hfitU
    calc Cw * ∫ ξ in part u, ‖F ξ‖^2
        ≤ Cw * (κ u * bandBudget c₃ ε ρ / Cw) :=
          mul_le_mul_of_nonneg_left h1 hCw.le
      _ = κ u * bandBudget c₃ ε ρ := by field_simp
  -- Every part now meets its share, so the nucleus assembly closes it.
  refine band_energy_le_budget F w hw0 Cw hwC G 𝒮 part hmeas hdisj hcover hint
    hintw κ c₃ ε ρ hc₃ hρ (fun i hi => ?_) hκ
  by_cases hiu : i = u
  · subst hiu; exact hUleg
  · exact hleg i hi hiu

end Tao2015

end MoltResearch
