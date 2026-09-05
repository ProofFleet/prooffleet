import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5BandCapstone
import MoltResearch.Discrepancy.LevelLegs

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


open MeasureTheory in
/-- **A2-III VI-1h-2 — the family seam with every cell's constants instantiated.**

`band_energy_le_budget_of_exceptional_family` composed, cell by cell, with the
instantiation campaign's three bounds — `integer_largeValues_factor_le` (M-5),
`prime_energy_dyadic_le` (M-4) and `exists_lam_exceptional_ratio_le` (M-6) —
exactly as M-8 did for one prime set.  The per-cell Ramaré parameter `lam v`
disappears from the interface; it is exhibited inside, and since M-6's
existence statement is per cell, the family of balanced parameters is built by
choice with a dummy value off the family.

What remains of each cell's `𝒰`-leg arithmetic is `hfit v`: an inequality in
`δ v`, `P v`, `N v`, `T`, `ε` and the cell's share `κ' v` alone.  The family's
total is then priced by `hfitU` as before.  `(Y v).Nonempty` is what makes each
`Γ v` strictly positive, and `hA0`/`hB0` are stated on the literal group
expressions for the reason M-8 gives: a consumer knows its own coefficients and
the tree cannot know that they do not all vanish. -/
theorem band_energy_le_budget_of_exceptional_family_instantiated
    [HalaszLargeValuesAssumption] [PrimeLargeValuesAssumption]
    {ι : Type*} [DecidableEq ι] {ι' : Type*}
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
    (hYne : ∀ v ∈ I, (Y v).Nonempty)
    (hlo : ∀ v ∈ I, ∀ p ∈ Y v, P v < p) (hhi : ∀ v ∈ I, ∀ p ∈ Y v, p ≤ 2 * P v)
    (b : ι' → ℕ → ℂ) (hb : ∀ v ∈ I, ∀ p, ‖b v p‖ ≤ 1)
    (N : ι' → ℕ) (a : ι' → ℕ → ℂ) (ha : ∀ v ∈ I, ∀ n, ‖a v n‖ ≤ 1)
    (T : ℝ) (hT1 : 1 ≤ T)
    (K : Finset ℤ)
    (hcoverU : part u ⊆ ⋃ k ∈ K, Set.Ico (k:ℝ) ((k:ℝ)+1))
    (hKT : ∀ k ∈ K, -T ≤ (k:ℝ) ∧ (k:ℝ) + 1 ≤ T)
    (δ : ι' → ℝ) (hδ0 : ∀ v ∈ I, 0 < δ v)
    (hδ : ∀ v ∈ I, ∀ t : ℝ, |t| ≤ T →
      ‖∑ n ∈ Finset.Icc 1 (N v), (a v n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ δ v)
    (C E : ℝ) (hC0 : 0 ≤ C)
    (hfac : (∫ ξ in part u, ‖F ξ‖^2)
      ≤ C * ∑ v ∈ I, (∫ ξ in part u, ‖∑ p ∈ Y v, (b v p/(p:ℂ))
            * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖^2
          * ‖∑ n ∈ Finset.Icc 1 (N v), (a v n/(n:ℂ))
            * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2) + E)
    (hA0 : ∀ v ∈ I, 0 < 64 * ((N v:ℝ) + (K.card:ℝ) * Real.sqrt T)
      * (Real.log (2*T) + 1) * ∑ n ∈ Finset.Icc 1 (N v), ‖a v n‖^2/(n:ℝ)^2)
    (hB0 : ∀ v ∈ I, 0 < 64 * (∑ p ∈ Y v, ‖b v p‖^2/(p:ℝ)^2)
      * (P v:ℝ) / Real.log (P v))
    (κ' : ι' → ℝ)
    (hfit : ∀ v ∈ I, 2 * ((δ v)^2 * (64 * (256 / (Real.log (P v))^2))
        + 2 * δ v * Real.sqrt
            ((128 * ((N v:ℝ) + 2*T*Real.sqrt T) * (Real.log (2*T) + 1))
              * ((64 * (256 / (Real.log (P v))^2))
                  * (Real.exp Real.pi * ((T+1)/(P v:ℝ) + 4)
                      * (256 / Real.log (P v) + 2048 * Real.pi)
                      * Real.exp (-(Real.log (P v) / (Real.log (2*T))^(3/4:ℝ)))
                      * (Real.log (2*T))^2))))
      ≤ κ' v * bandBudget c₃ ε ρ)
    (hfitU : C * (∑ v ∈ I, κ' v) * bandBudget c₃ ε ρ + E
      ≤ κ u * bandBudget c₃ ε ρ / Cw) :
    (∫ ξ in G, ‖F ξ‖^2 * w ξ) ≤ bandBudget c₃ ε ρ := by
  classical
  have hlog2T : (0:ℝ) < Real.log (2*T) := Real.log_pos (by linarith)
  -- M-6's balanced Ramaré parameter, one per cell (a dummy value off the family)
  have hlamex : ∀ v : ι', ∃ lam : ℝ, 0 < lam ∧ (v ∈ I →
      Real.exp Real.pi * ((T+1)/(P v:ℝ) + 2*(2:ℝ))
          * ((1+lam) + (1/lam)*(2*Real.pi*Real.log (2*(P v:ℝ)))^2)
          * (∑ p ∈ Y v, (1:ℝ)/(p:ℝ))
          * Real.exp (-(Real.log (P v) / (Real.log (2*T))^(3/4:ℝ)))
          * (Real.log (2*T))^2
        ≤ Real.exp Real.pi * ((T+1)/(P v:ℝ) + 4)
          * (256 / Real.log (P v) + 2048 * Real.pi)
          * Real.exp (-(Real.log (P v) / (Real.log (2*T))^(3/4:ℝ)))
          * (Real.log (2*T))^2) := by
    intro v
    by_cases hv : v ∈ I
    · obtain ⟨lam, hlam0, hΓle⟩ := exists_lam_exceptional_ratio_le (P v) (hP v hv)
        (Y v) (hY v hv) (hlo v hv) (hhi v hv) T hT1
      exact ⟨lam, hlam0, fun _ => hΓle⟩
    · exact ⟨1, one_pos, fun h => absurd h hv⟩
  choose lam hlam0 hΓle using hlamex
  -- each cell's `Γ` is strictly positive, through the block's prime mass
  have hΓ0 : ∀ v ∈ I, 0 < (Real.exp Real.pi * ((T+1)/(P v:ℝ) + 2*(2:ℝ))
        * ((1+lam v) + (1/lam v)*(2*Real.pi*Real.log (2*(P v:ℝ)))^2)
        * (∑ p ∈ Y v, (1:ℝ)/(p:ℝ)))
      * Real.exp (-(Real.log (P v) / (Real.log (2*T))^(3/4:ℝ)))
      * (Real.log (2*T))^2 := by
    intro v hv
    have hP0 : (0:ℝ) < (P v:ℝ) := by
      have : 0 < P v := by have := hP v hv; omega
      exact_mod_cast this
    obtain ⟨p₀, hp₀⟩ := hYne v hv
    have hmass0 : (0:ℝ) < ∑ p ∈ Y v, (1:ℝ)/(p:ℝ) := by
      refine Finset.sum_pos' (fun p _ => by positivity) ⟨p₀, hp₀, ?_⟩
      have : (0:ℝ) < (p₀:ℝ) := by exact_mod_cast (hY v hv p₀ hp₀).pos
      positivity
    have hl := hlam0 v
    have hsplit : (0:ℝ) < (1+lam v) + (1/lam v)*(2*Real.pi*Real.log (2*(P v:ℝ)))^2 := by
      have : (0:ℝ) < 1/lam v := by positivity
      nlinarith [sq_nonneg (2*Real.pi*Real.log (2*(P v:ℝ)))]
    have hlead : (0:ℝ) < (T+1)/(P v:ℝ) + 2*(2:ℝ) := by
      have : (0:ℝ) ≤ (T+1)/(P v:ℝ) := by positivity
      linarith
    have hlogsq : (0:ℝ) < (Real.log (2*T))^2 := by positivity
    have := Real.exp_pos Real.pi
    have := Real.exp_pos (-(Real.log (P v) / (Real.log (2*T))^(3/4:ℝ)))
    positivity
  refine band_energy_le_budget_of_exceptional_family F w hw0 Cw hCw hwC G 𝒮 part
    hmeas hdisj hcover hint hintw κ c₃ ε ρ hc₃ hρ hκ u hu hleg I P hP Y hY hlo hhi
    b hb N a T hT1 K hcoverU hKT δ lam hδ0 (fun v _ => hlam0 v) hδ C E hC0 hfac
    (fun v => 64 * ((N v:ℝ) + (K.card:ℝ) * Real.sqrt T)
      * (Real.log (2*T) + 1) * ∑ n ∈ Finset.Icc 1 (N v), ‖a v n‖^2/(n:ℝ)^2)
    (fun v => 64 * (∑ p ∈ Y v, ‖b v p‖^2/(p:ℝ)^2) * (P v:ℝ) / Real.log (P v))
    (fun v => (Real.exp Real.pi * ((T+1)/(P v:ℝ) + 2*(2:ℝ))
        * ((1+lam v) + (1/lam v)*(2*Real.pi*Real.log (2*(P v:ℝ)))^2)
        * (∑ p ∈ Y v, (1:ℝ)/(p:ℝ)))
      * Real.exp (-(Real.log (P v) / (Real.log (2*T))^(3/4:ℝ)))
      * (Real.log (2*T))^2)
    (fun v _ => rfl) (fun v _ => rfl) (fun v _ => rfl) hA0 hB0 hΓ0 κ' ?_ hfitU
  -- the three instantiated bounds, cell by cell, then the seam M-7 provides
  intro v hv
  have hlogP : (0:ℝ) < Real.log (P v) := Real.log_pos (by exact_mod_cast hP v hv)
  have hAle : 64 * ((N v:ℝ) + (K.card:ℝ) * Real.sqrt T)
      * (Real.log (2*T) + 1) * ∑ n ∈ Finset.Icc 1 (N v), ‖a v n‖^2/(n:ℝ)^2
      ≤ 128 * ((N v:ℝ) + 2*T*Real.sqrt T) * (Real.log (2*T) + 1) :=
    integer_largeValues_factor_le (N v) (a v) (ha v hv) T hT1 K hKT
  have hBle : 64 * (∑ p ∈ Y v, ‖b v p‖^2/(p:ℝ)^2) * (P v:ℝ) / Real.log (P v)
      ≤ 64 * (256 / (Real.log (P v))^2) := by
    have := prime_energy_dyadic_le (P v) (hP v hv) (Y v) (hY v hv) (hlo v hv)
      (hhi v hv) (b v) (hb v hv)
    calc 64 * (∑ p ∈ Y v, ‖b v p‖^2/(p:ℝ)^2) * (P v:ℝ) / Real.log (P v)
        = 64 * ((∑ p ∈ Y v, ‖b v p‖^2/(p:ℝ)^2) * (P v:ℝ) / Real.log (P v)) := by
          ring
      _ ≤ 64 * (256 / (Real.log (P v))^2) := by gcongr
  exact exceptional_fit_of_le _ _ _
    (128 * ((N v:ℝ) + 2*T*Real.sqrt T) * (Real.log (2*T) + 1))
    (64 * (256 / (Real.log (P v))^2))
    (Real.exp Real.pi * ((T+1)/(P v:ℝ) + 4)
      * (256 / Real.log (P v) + 2048 * Real.pi)
      * Real.exp (-(Real.log (P v) / (Real.log (2*T))^(3/4:ℝ)))
      * (Real.log (2*T))^2)
    (δ v) c₃ ε ρ (κ' v) (hA0 v hv).le (hB0 v hv).le (hΓ0 v hv).le (hδ0 v hv).le
    hAle hBle (hΓle v hv) (hfit v hv)


open MeasureTheory in
/-- **A2-III VI-1h-3 — the `[mrt]` A.2 inner-band estimate with the factorisation
seam over a cell family.**

`band_energy_typicalS_le_geometric` (VI-1g-1) re-based on the family seam: the
weighted energy of the typical-set polynomial over the inner band, against the
band's share of the slice budget, with the exceptional part presented as
`[MR]`'s decomposition actually presents it.  Everything VI-1e/VI-1f bound stays
bound — `F` is the polynomial (continuity from `ExpSums.continuous_char_poly`),
`Cw = (4H/A)²`, `ρ = Δ/A`, the partition is `bandPartOn Pset J` on the band,
the cells are `bandCells K₂` with `K₂ + 2 ≤ T` the frequency-range seam — and the
shares are geometric, so `hκ` is gone.

**What a consumer now supplies is, for the first time, exactly what the tree
can produce.**  The level legs `hleg` (VI-2, the `LevelLegs` ladder), the
family factorisation `hfac` on the exceptional part with its constant `C` and
error `E` (N3-f → II-1 → II-2e → collars → collision), the per-cell Halász
inputs `δ v`, and the per-cell fits — the last being schedule arithmetic in
`P v`, `N v`, `T`, `ε` and the shares alone. -/
theorem band_energy_typicalS_le_family [HalaszLargeValuesAssumption]
    [PrimeLargeValuesAssumption] {ι' : Type*}
    (g : ℕ → ℂ) (A Δ H : ℕ) (hA : 0 < A) (hH : 0 < H)
    (levels : List (Finset ℕ))
    (w : ℝ → ℝ) (hwm : Measurable w) (hw0 : ∀ ξ, 0 ≤ w ξ)
    (hwsup : ∀ ξ, w ξ ≤ (4*(H:ℝ)/(A:ℝ))^2)
    (K₁ K₂ : ℝ)
    (J : ℕ) (Pset : ℕ → Set ℝ) (hPset : ∀ j, MeasurableSet (Pset j))
    (c₃ ε : ℝ) (hc₃ : 0 ≤ c₃)
    (hleg : ∀ j ∈ Finset.range (J + 1), j ≠ J →
      (4*(H:ℝ)/(A:ℝ))^2
          * ∫ ξ in bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} j,
            ‖∑ m ∈ typicalS A (A+Δ) levels, (g m/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
        ≤ (1 / 2 ^ (j + 1)) * bandBudget c₃ ε ((Δ:ℝ)/(A:ℝ)))
    (I : Finset ι') (P : ι' → ℕ) (hP : ∀ v ∈ I, 2 ≤ P v)
    (Y : ι' → Finset ℕ) (hY : ∀ v ∈ I, ∀ p ∈ Y v, p.Prime)
    (hYne : ∀ v ∈ I, (Y v).Nonempty)
    (hlo : ∀ v ∈ I, ∀ p ∈ Y v, P v < p) (hhi : ∀ v ∈ I, ∀ p ∈ Y v, p ≤ 2 * P v)
    (b : ι' → ℕ → ℂ) (hb : ∀ v ∈ I, ∀ p, ‖b v p‖ ≤ 1)
    (N : ι' → ℕ) (a : ι' → ℕ → ℂ) (ha : ∀ v ∈ I, ∀ n, ‖a v n‖ ≤ 1)
    (T : ℝ) (hT1 : 1 ≤ T) (hTK₂ : K₂ + 2 ≤ T)
    (δ : ι' → ℝ) (hδ0 : ∀ v ∈ I, 0 < δ v)
    (hδ : ∀ v ∈ I, ∀ t : ℝ, |t| ≤ T →
      ‖∑ n ∈ Finset.Icc 1 (N v), (a v n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ δ v)
    (C E : ℝ) (hC0 : 0 ≤ C)
    (hfac : (∫ ξ in bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} J,
        ‖∑ m ∈ typicalS A (A+Δ) levels, (g m/(m:ℂ))
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2)
      ≤ C * ∑ v ∈ I, (∫ ξ in bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} J,
            ‖∑ p ∈ Y v, (b v p/(p:ℂ))
              * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖^2
          * ‖∑ n ∈ Finset.Icc 1 (N v), (a v n/(n:ℂ))
              * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2) + E)
    (hA0 : ∀ v ∈ I, 0 < 64 * ((N v:ℝ) + ((bandCells K₂).card:ℝ) * Real.sqrt T)
      * (Real.log (2*T) + 1) * ∑ n ∈ Finset.Icc 1 (N v), ‖a v n‖^2/(n:ℝ)^2)
    (hB0 : ∀ v ∈ I, 0 < 64 * (∑ p ∈ Y v, ‖b v p‖^2/(p:ℝ)^2)
      * (P v:ℝ) / Real.log (P v))
    (κ' : ι' → ℝ)
    (hfit : ∀ v ∈ I, 2 * ((δ v)^2 * (64 * (256 / (Real.log (P v))^2))
        + 2 * δ v * Real.sqrt
            ((128 * ((N v:ℝ) + 2*T*Real.sqrt T) * (Real.log (2*T) + 1))
              * ((64 * (256 / (Real.log (P v))^2))
                  * (Real.exp Real.pi * ((T+1)/(P v:ℝ) + 4)
                      * (256 / Real.log (P v) + 2048 * Real.pi)
                      * Real.exp (-(Real.log (P v) / (Real.log (2*T))^(3/4:ℝ)))
                      * (Real.log (2*T))^2))))
      ≤ κ' v * bandBudget c₃ ε ((Δ:ℝ)/(A:ℝ)))
    (hfitU : C * (∑ v ∈ I, κ' v) * bandBudget c₃ ε ((Δ:ℝ)/(A:ℝ)) + E
      ≤ (1 / 2 ^ (J + 1)) * bandBudget c₃ ε ((Δ:ℝ)/(A:ℝ)) / (4*(H:ℝ)/(A:ℝ))^2) :
    (∫ ξ in {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂},
        ‖∑ m ∈ typicalS A (A+Δ) levels, (g m/(m:ℂ))
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2 * w ξ)
      ≤ bandBudget c₃ ε ((Δ:ℝ)/(A:ℝ)) := by
  have hA0' : (0:ℝ) < (A:ℝ) := by exact_mod_cast hA
  have hH0' : (0:ℝ) < (H:ℝ) := by exact_mod_cast hH
  have hCw : (0:ℝ) < (4*(H:ℝ)/(A:ℝ))^2 := by positivity
  have hFc : Continuous fun ξ : ℝ => ∑ m ∈ typicalS A (A+Δ) levels, (g m/(m:ℂ))
      * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) :=
    ExpSums.continuous_char_poly (typicalS A (A+Δ) levels)
      (fun m => g m/(m:ℂ)) (fun m => Real.log m)
  have hwnorm : ∀ ξ, ‖w ξ‖ ≤ (4*(H:ℝ)/(A:ℝ))^2 := fun ξ => by
    rw [Real.norm_of_nonneg (hw0 ξ)]; exact hwsup ξ
  exact band_energy_le_budget_of_exceptional_family_instantiated
    (fun ξ => ∑ m ∈ typicalS A (A+Δ) levels, (g m/(m:ℂ))
      * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
    w hw0 ((4*(H:ℝ)/(A:ℝ))^2) hCw hwsup
    {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} (Finset.range (J + 1))
    (bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂})
    (fun j _ => bandPartOn_measurableSet Pset hPset J _
      (measurableSet_inner_band K₁ K₂) j)
    (bandPartOn_pairwiseDisjoint Pset J _)
    (bandPartOn_cover Pset J _)
    (fun j _ => integrableOn_norm_sq_inner_band _ hFc K₁ K₂ _
      (bandPartOn_subset Pset J _ j))
    (fun j _ => integrableOn_norm_sq_mul_inner_band _ hFc w hwm _ hwnorm K₁ K₂ _
      (bandPartOn_subset Pset J _ j))
    (fun j => 1 / 2 ^ (j + 1)) c₃ ε ((Δ:ℝ)/(A:ℝ)) hc₃ (by positivity)
    (geometric_shares_le_one (J + 1))
    J (Finset.mem_range.mpr (Nat.lt_succ_self J)) hleg
    I P hP Y hY hYne hlo hhi b hb N a ha T hT1 (bandCells K₂)
    ((bandPartOn_subset Pset J _ J).trans (inner_band_subset_bandCells K₁ K₂))
    (bandCells_mem_Icc K₂ T hTK₂)
    δ hδ0 hδ C E hC0 hfac hA0 hB0 κ' hfit hfitU


/-! ## From a decomposition to the family seam (Track R, A2-III, VI-3-1) -/

open MeasureTheory in
/-- **A2-III VI-3-1 — the family seam from a pointwise decomposition.**

If on a measurable `G ⊆ (−T, T]` the integrand is `F = ∑_{v∈I} X_v + error`,
then its energy is at most `2·#I·∑_v ∫_G ‖X_v‖² + 2∫_G ‖error‖²`: one `L²`
triangle (`ExpSums.setIntegral_norm_add_sq_le`) and one Cauchy–Schwarz over the
family (`setIntegral_norm_sq_sum_le_card_mul_of_setIntegral`).  Nothing about
the shape of the `X_v` is used, so a consumer that has *exhibited* the `[MR]`
decomposition — cell products plus a combined replacement-and-collision error —
has discharged the seam of `band_energy_le_budget_of_exceptional_family` with
`C = 2·#I` and `E = 2∫_G ‖error‖²`.

The Cauchy–Schwarz is taken on `G` itself and not on the enclosing interval,
because on the exceptional part the cell products are estimated on `G` by the
large-values machinery, and enlarging to `(−T, T)` would discard exactly the
frequency information that machinery uses. -/
theorem setIntegral_norm_sq_le_family_of_decomp (F : ℝ → ℂ) (I : Finset ℕ)
    (X : ℕ → ℝ → ℂ) (error : ℝ → ℂ)
    (hX : ∀ v ∈ I, Continuous (X v)) (herr : Continuous error)
    (T : ℝ) (G : Set ℝ) (hGm : MeasurableSet G) (hGT : G ⊆ Set.Ioc (-T) T)
    (hdecomp : ∀ ξ ∈ G, F ξ = (∑ v ∈ I, X v ξ) + error ξ) :
    (∫ ξ in G, ‖F ξ‖^2)
      ≤ 2 * (I.card : ℝ) * ∑ v ∈ I, (∫ ξ in G, ‖X v ξ‖^2)
        + 2 * ∫ ξ in G, ‖error ξ‖^2 := by
  have hsum : Continuous fun ξ => ∑ v ∈ I, X v ξ := continuous_finset_sum I hX
  have hcs := setIntegral_norm_sq_sum_le_card_mul_of_setIntegral X I hX T G hGm hGT
    (fun v => ∫ ξ in G, ‖X v ξ‖^2) (fun v _ => le_rfl)
  calc (∫ ξ in G, ‖F ξ‖^2)
      = ∫ ξ in G, ‖(∑ v ∈ I, X v ξ) + error ξ‖^2 := by
        refine setIntegral_congr_fun hGm fun ξ hξ => ?_
        rw [hdecomp ξ hξ]
    _ ≤ 2 * (∫ ξ in G, ‖∑ v ∈ I, X v ξ‖^2) + 2 * (∫ ξ in G, ‖error ξ‖^2) :=
        ExpSums.setIntegral_norm_add_sq_le _ _ hsum herr T G hGm hGT
    _ ≤ 2 * ((I.card : ℝ) * ∑ v ∈ I, (∫ ξ in G, ‖X v ξ‖^2))
          + 2 * (∫ ξ in G, ‖error ξ‖^2) :=
        add_le_add (mul_le_mul_of_nonneg_left hcs (by norm_num)) le_rfl
    _ = 2 * (I.card : ℝ) * ∑ v ∈ I, (∫ ξ in G, ‖X v ξ‖^2)
          + 2 * ∫ ξ in G, ‖error ξ‖^2 := by ring

open MeasureTheory in
/-- **A2-III VI-3-1 — the A.2 inner-band estimate from an exhibited
decomposition of the exceptional part.**

`band_energy_typicalS_le_family` with its factorisation seam discharged by
`setIntegral_norm_sq_le_family_of_decomp`: instead of the energy inequality
`hfac`, a consumer supplies the decomposition itself — on the exceptional part,
the typical-set polynomial equals a sum over cells `v ∈ I` of (prime polynomial
over `Y v`) × (integer polynomial with coefficients `a v`), plus a continuous
`error` — and pays `C = 2·#I` and `E = 2∫ ‖error‖²` in the fit.

**This is the statement the discharge ladder has to hit**, and it is what the
tree produces: N3-f gives the polynomial as prime fibres plus a collision term,
II-1 groups the fibres by `e`-adic cells, II-2e replaces each cell's fibres by
the cell-uniform block at the cost of the telescoping energy, and the `error`
slot collects the replacement and collision terms together.  The frequency
range hypothesis `K₂ + 2 ≤ T` already forces the exceptional part inside
`(−T, T]`, which is all the `L²` split needs. -/
theorem band_energy_typicalS_le_of_decomp [HalaszLargeValuesAssumption]
    [PrimeLargeValuesAssumption]
    (g : ℕ → ℂ) (A Δ H : ℕ) (hA : 0 < A) (hH : 0 < H)
    (levels : List (Finset ℕ))
    (w : ℝ → ℝ) (hwm : Measurable w) (hw0 : ∀ ξ, 0 ≤ w ξ)
    (hwsup : ∀ ξ, w ξ ≤ (4*(H:ℝ)/(A:ℝ))^2)
    (K₁ K₂ : ℝ)
    (J : ℕ) (Pset : ℕ → Set ℝ) (hPset : ∀ j, MeasurableSet (Pset j))
    (c₃ ε : ℝ) (hc₃ : 0 ≤ c₃)
    (hleg : ∀ j ∈ Finset.range (J + 1), j ≠ J →
      (4*(H:ℝ)/(A:ℝ))^2
          * ∫ ξ in bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} j,
            ‖∑ m ∈ typicalS A (A+Δ) levels, (g m/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
        ≤ (1 / 2 ^ (j + 1)) * bandBudget c₃ ε ((Δ:ℝ)/(A:ℝ)))
    (I : Finset ℕ) (P : ℕ → ℕ) (hP : ∀ v ∈ I, 2 ≤ P v)
    (Y : ℕ → Finset ℕ) (hY : ∀ v ∈ I, ∀ p ∈ Y v, p.Prime)
    (hYne : ∀ v ∈ I, (Y v).Nonempty)
    (hlo : ∀ v ∈ I, ∀ p ∈ Y v, P v < p) (hhi : ∀ v ∈ I, ∀ p ∈ Y v, p ≤ 2 * P v)
    (b : ℕ → ℕ → ℂ) (hb : ∀ v ∈ I, ∀ p, ‖b v p‖ ≤ 1)
    (N : ℕ → ℕ) (a : ℕ → ℕ → ℂ) (ha : ∀ v ∈ I, ∀ n, ‖a v n‖ ≤ 1)
    (T : ℝ) (hT1 : 1 ≤ T) (hTK₂ : K₂ + 2 ≤ T)
    (δ : ℕ → ℝ) (hδ0 : ∀ v ∈ I, 0 < δ v)
    (hδ : ∀ v ∈ I, ∀ t : ℝ, |t| ≤ T →
      ‖∑ n ∈ Finset.Icc 1 (N v), (a v n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ δ v)
    (error : ℝ → ℂ) (herrc : Continuous error)
    (hdecomp : ∀ ξ ∈ bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} J,
      ∑ m ∈ typicalS A (A+Δ) levels, (g m/(m:ℂ))
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)
        = (∑ v ∈ I, (∑ p ∈ Y v, (b v p/(p:ℂ))
              * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))
            * (∑ n ∈ Finset.Icc 1 (N v), (a v n/(n:ℂ))
              * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)))
          + error ξ)
    (hA0 : ∀ v ∈ I, 0 < 64 * ((N v:ℝ) + ((bandCells K₂).card:ℝ) * Real.sqrt T)
      * (Real.log (2*T) + 1) * ∑ n ∈ Finset.Icc 1 (N v), ‖a v n‖^2/(n:ℝ)^2)
    (hB0 : ∀ v ∈ I, 0 < 64 * (∑ p ∈ Y v, ‖b v p‖^2/(p:ℝ)^2)
      * (P v:ℝ) / Real.log (P v))
    (κ' : ℕ → ℝ)
    (hfit : ∀ v ∈ I, 2 * ((δ v)^2 * (64 * (256 / (Real.log (P v))^2))
        + 2 * δ v * Real.sqrt
            ((128 * ((N v:ℝ) + 2*T*Real.sqrt T) * (Real.log (2*T) + 1))
              * ((64 * (256 / (Real.log (P v))^2))
                  * (Real.exp Real.pi * ((T+1)/(P v:ℝ) + 4)
                      * (256 / Real.log (P v) + 2048 * Real.pi)
                      * Real.exp (-(Real.log (P v) / (Real.log (2*T))^(3/4:ℝ)))
                      * (Real.log (2*T))^2))))
      ≤ κ' v * bandBudget c₃ ε ((Δ:ℝ)/(A:ℝ)))
    (hfitU : 2 * (I.card : ℝ) * (∑ v ∈ I, κ' v) * bandBudget c₃ ε ((Δ:ℝ)/(A:ℝ))
        + 2 * (∫ ξ in bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} J,
            ‖error ξ‖^2)
      ≤ (1 / 2 ^ (J + 1)) * bandBudget c₃ ε ((Δ:ℝ)/(A:ℝ)) / (4*(H:ℝ)/(A:ℝ))^2) :
    (∫ ξ in {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂},
        ‖∑ m ∈ typicalS A (A+Δ) levels, (g m/(m:ℂ))
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2 * w ξ)
      ≤ bandBudget c₃ ε ((Δ:ℝ)/(A:ℝ)) := by
  -- the exceptional part sits inside `(−T, T]`, through the band's range
  have hGT : bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} J
      ⊆ Set.Ioc (-T) T := by
    intro ξ hξ
    have h := inner_band_subset_Icc K₁ K₂ (bandPartOn_subset Pset J _ J hξ)
    rw [Set.mem_Icc] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hGm : MeasurableSet (bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} J) :=
    bandPartOn_measurableSet Pset hPset J _ (measurableSet_inner_band K₁ K₂) J
  -- each cell product is continuous
  have hX : ∀ v ∈ I, Continuous fun ξ : ℝ =>
      (∑ p ∈ Y v, (b v p/(p:ℂ))
          * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))
        * (∑ n ∈ Finset.Icc 1 (N v), (a v n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)) := fun v _ =>
    (ExpSums.continuous_char_poly (Y v) (fun p => b v p/(p:ℂ))
        (fun p => Real.log p)).mul
      (ExpSums.continuous_char_poly (Finset.Icc 1 (N v)) (fun n => a v n/(n:ℂ))
        (fun n => Real.log n))
  have hfac := setIntegral_norm_sq_le_family_of_decomp _ I _ error hX herrc T _
    hGm hGT hdecomp
  simp_rw [norm_mul, mul_pow] at hfac
  exact band_energy_typicalS_le_family g A Δ H hA hH levels w hwm hw0 hwsup K₁ K₂
    J Pset hPset c₃ ε hc₃ hleg I P hP Y hY hYne hlo hhi b hb N a ha T hT1 hTK₂
    δ hδ0 hδ (2 * (I.card : ℝ))
    (2 * ∫ ξ in bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} J, ‖error ξ‖^2)
    (by positivity) hfac hA0 hB0 κ' hfit hfitU


/-! ## The exceptional part from the cell-uniform decomposition
(Track R, A2-III, VI-3-2) -/

/-- The cell's block coefficient, zero-extended to `[1, B/q]`: the `𝒰` leg
consumes integer polynomials over `Icc 1 N`, while the cell-uniform block of
`LevelLegs` lives on `Ioc (A/q) (B/q)`. -/
noncomputable def cellBlockCoeff (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ)) (q m : ℕ) : ℂ :=
  if m ∈ Finset.Ioc (A / q) (B / q) then typicalSQuotCoeff g P (typicalS 0 B rest) m
  else 0

/-- The zero-extended coefficient is still `1`-bounded. -/
theorem norm_cellBlockCoeff_le_one (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A B : ℕ) (P : Finset ℕ) (rest : List (Finset ℕ)) (q m : ℕ) :
    ‖cellBlockCoeff g A B P rest q m‖ ≤ 1 := by
  unfold cellBlockCoeff
  split_ifs
  · exact norm_typicalSQuotCoeff_le_one g hg P _ m
  · simp

/-- The block polynomial over `Icc 1 (B/q)` with the zero-extended coefficient
is the cell-uniform block of `LevelLegs`. -/
theorem sum_cellBlockCoeff_Icc_eq (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ)) (q : ℕ) (ξ : ℝ) :
    ∑ m ∈ Finset.Icc 1 (B / q), (cellBlockCoeff g A B P rest q m/(m:ℂ))
        * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)
      = ∑ m ∈ Finset.Ioc (A / q) (B / q),
          (typicalSQuotCoeff g P (typicalS 0 B rest) m/(m:ℂ))
            * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) := by
  classical
  have hsub : Finset.Ioc (A / q) (B / q) ⊆ Finset.Icc 1 (B / q) := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    rw [Finset.mem_Icc]
    exact ⟨Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le (A / q)) hm.1), hm.2⟩
  rw [← Finset.sum_subset hsub (fun m _ hm => by simp [cellBlockCoeff, hm])]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp [cellBlockCoeff, hm]

open MeasureTheory in
/-- **A2-III VI-3-2 — the A.2 inner-band estimate with the exceptional part
decomposed by the `LevelLegs` ladder.**

`band_energy_typicalS_le_of_decomp` with the decomposition exhibited: on the
exceptional part the typical-set polynomial for `P :: rest` is
`typicalSCellUniformMain` — a sum over the `e`-adic cells `v ∈ [v₀, v₁]` of
`levelCellPoly` (the prime polynomial over the cell) times the cell-uniform
block at the representative `q v` — plus the II-2e replacement and the
adjusted collision (`typicalS_phase_eq_cellUniform_add_errors`, VI-2s).  The
cell family is therefore `Y v = eadicCell P (2N) v`, the prime coefficients are
`g`, the integer polynomials carry `cellBlockCoeff` over `Icc 1 ((A+Δ)/q v)`,
and the error is `typicalSCellReplacement + typicalSAdjustedCollision`.

**What the exceptional part now asks for is exactly what the level legs ask
for.**  The same three energies — cell-uniform main, replacement, adjusted
collision — appear on `𝒯_j` in `typicalS_level_leg_le_budget`; here the main
term is not priced by smallness but handed, cell by cell, to the two
large-values interfaces through the family seam, at `C = 2·#I` with
`#I = v₁ − v₀ + 1`.  The replacement and collision energies on the exceptional
part are the same quantities VI-2t and VI-2ae price, so their fits are shared.

The per-cell dyadic anchor `Pc v` is left to the consumer, as in the capstone:
a cell at resolution `2N` sits in `(q v, q v·e^{1/(2N)})`, so `Pc v = q v − 1`
serves once `q v ≥ 6`, and the first cells of a level are the consumer's to
anchor.  `(Y v).Nonempty` is discharged by the representative itself. -/
theorem band_energy_typicalS_le_of_cellUniform [HalaszLargeValuesAssumption]
    [PrimeLargeValuesAssumption]
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Δ H : ℕ) (hA : 0 < A) (hH : 0 < H)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (rest : List (Finset ℕ))
    (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (hstable : ∀ p ∈ P, ∀ m,
      HasFactorInAll rest (p * m) ↔ HasFactorInAll rest m)
    (q : ℕ → ℕ)
    (hqcell : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), q v ∈ eadicCell P (2 * N) v)
    (w : ℝ → ℝ) (hwm : Measurable w) (hw0 : ∀ ξ, 0 ≤ w ξ)
    (hwsup : ∀ ξ, w ξ ≤ (4*(H:ℝ)/(A:ℝ))^2)
    (K₁ K₂ : ℝ)
    (J : ℕ) (Pset : ℕ → Set ℝ) (hPset : ∀ j, MeasurableSet (Pset j))
    (c₃ ε : ℝ) (hc₃ : 0 ≤ c₃)
    (hleg : ∀ j ∈ Finset.range (J + 1), j ≠ J →
      (4*(H:ℝ)/(A:ℝ))^2
          * ∫ ξ in bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} j,
            ‖∑ m ∈ typicalS A (A+Δ) (P :: rest), (g m/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
        ≤ (1 / 2 ^ (j + 1)) * bandBudget c₃ ε ((Δ:ℝ)/(A:ℝ)))
    (Pc : ℕ → ℕ) (hPc : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), 2 ≤ Pc v)
    (hlo : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), ∀ p ∈ eadicCell P (2 * N) v, Pc v < p)
    (hhi : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), ∀ p ∈ eadicCell P (2 * N) v,
      p ≤ 2 * Pc v)
    (T : ℝ) (hT1 : 1 ≤ T) (hTK₂ : K₂ + 2 ≤ T)
    (δ : ℕ → ℝ) (hδ0 : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), 0 < δ v)
    (hδ : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), ∀ t : ℝ, |t| ≤ T →
      ‖∑ n ∈ Finset.Icc 1 ((A + Δ) / q v),
          (cellBlockCoeff g A (A + Δ) P rest (q v) n/(n:ℂ))
            * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ δ v)
    (hA0 : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      0 < 64 * ((((A + Δ) / q v : ℕ):ℝ) + ((bandCells K₂).card:ℝ) * Real.sqrt T)
        * (Real.log (2*T) + 1)
        * ∑ n ∈ Finset.Icc 1 ((A + Δ) / q v),
            ‖cellBlockCoeff g A (A + Δ) P rest (q v) n‖^2/(n:ℝ)^2)
    (hB0 : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      0 < 64 * (∑ p ∈ eadicCell P (2 * N) v, ‖g p‖^2/(p:ℝ)^2)
        * (Pc v:ℝ) / Real.log (Pc v))
    (κ' : ℕ → ℝ)
    (hfit : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      2 * ((δ v)^2 * (64 * (256 / (Real.log (Pc v))^2))
        + 2 * δ v * Real.sqrt
            ((128 * ((((A + Δ) / q v : ℕ):ℝ) + 2*T*Real.sqrt T)
                * (Real.log (2*T) + 1))
              * ((64 * (256 / (Real.log (Pc v))^2))
                  * (Real.exp Real.pi * ((T+1)/(Pc v:ℝ) + 4)
                      * (256 / Real.log (Pc v) + 2048 * Real.pi)
                      * Real.exp (-(Real.log (Pc v) / (Real.log (2*T))^(3/4:ℝ)))
                      * (Real.log (2*T))^2))))
      ≤ κ' v * bandBudget c₃ ε ((Δ:ℝ)/(A:ℝ)))
    (hfitU : 2 * ((Finset.Ico v₀ (v₁ + 1)).card : ℝ)
          * (∑ v ∈ Finset.Ico v₀ (v₁ + 1), κ' v) * bandBudget c₃ ε ((Δ:ℝ)/(A:ℝ))
        + 2 * (∫ ξ in bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} J,
            ‖typicalSCellReplacement g A (A + Δ) P rest N v₀ v₁ q ξ
              + typicalSAdjustedCollision g A (A + Δ) P rest N v₀ v₁ ξ‖^2)
      ≤ (1 / 2 ^ (J + 1)) * bandBudget c₃ ε ((Δ:ℝ)/(A:ℝ)) / (4*(H:ℝ)/(A:ℝ))^2) :
    (∫ ξ in {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂},
        ‖∑ m ∈ typicalS A (A+Δ) (P :: rest), (g m/(m:ℂ))
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2 * w ξ)
      ≤ bandBudget c₃ ε ((Δ:ℝ)/(A:ℝ)) := by
  refine band_energy_typicalS_le_of_decomp g A Δ H hA hH (P :: rest) w hwm hw0
    hwsup K₁ K₂ J Pset hPset c₃ ε hc₃ hleg (Finset.Ico v₀ (v₁ + 1)) Pc hPc
    (fun v => eadicCell P (2 * N) v)
    (fun v _ p hp => hP p (mem_eadicCell.mp hp).1)
    (fun v hv => ⟨q v, hqcell v hv⟩) hlo hhi
    (fun _ => g) (fun _ _ p => hg p)
    (fun v => (A + Δ) / q v)
    (fun v => cellBlockCoeff g A (A + Δ) P rest (q v))
    (fun v _ n => norm_cellBlockCoeff_le_one g hg A (A + Δ) P rest (q v) n)
    T hT1 hTK₂ δ hδ0 hδ
    (fun ξ => typicalSCellReplacement g A (A + Δ) P rest N v₀ v₁ q ξ
      + typicalSAdjustedCollision g A (A + Δ) P rest N v₀ v₁ ξ)
    ((continuous_typicalSCellReplacement g A (A + Δ) P rest N v₀ v₁ q).add
      (continuous_typicalSAdjustedCollision g A (A + Δ) P rest N v₀ v₁))
    ?_ hA0 hB0 κ' hfit hfitU
  -- the decomposition, from VI-2s, with each block reindexed to `Icc 1 (B/q)`
  intro ξ _
  rw [typicalS_phase_eq_cellUniform_add_errors g hcm A Δ P hP rest N v₀ v₁ hcov
    hstable q ξ]
  congr 1
  unfold typicalSCellUniformMain levelCellPoly
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [sum_cellBlockCoeff_Icc_eq g A (A + Δ) P rest (q v) ξ]


open MeasureTheory in
/-- **A2-III VI-3-3 — the exceptional part's errors priced by the ladder's
envelopes.**

`band_energy_typicalS_le_of_cellUniform` with the error energy in its fit
replaced by the two named quantities the `LevelLegs` ladder prices: the
replacement energy on the exceptional part is at most
`cellReplacementEnergyBound` (`setIntegral_norm_sq_typicalSCellReplacement_le`,
VI-2t), and the adjusted collision's is at most `4·collisionEnergyBound`
(`intervalIntegral_norm_sq_typicalSAdjustedCollision_le`, VI-2ab, after
enlarging the part to `(−T, T)`).  One `L²` triangle separates the two, so the
fit charges `2·(2·replacement + 2·4·collision)`.

**Nothing on the exceptional part is left as an integral.**  After this the
`𝒰` leg's obligations are the per-cell Halász inputs `δ v`, the per-cell fits,
and one numerical inequality in the two envelopes — the same envelopes the
level legs' fits use (`eadic_replacement_error_le_budget`, VI-2k, and the
collision fit of VI-2ae), so the schedule prices them once for both legs.

The hypotheses `hqmin`, `hLA`, `hLB` are II-2e's: the representative is the
cell's least member and every prime's block is wide enough for the collar
argument.  `hPA : p² ≤ A` is the collision estimate's: the repeated prime is
extracted at the quotient scale `A/p²`. -/
theorem band_energy_typicalS_le_of_cellUniform_fit [HalaszLargeValuesAssumption]
    [PrimeLargeValuesAssumption]
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Δ H : ℕ) (hA : 0 < A) (hH : 0 < H) (hΔA : Δ ≤ A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPA : ∀ p ∈ P, p * p ≤ A)
    (rest : List (Finset ℕ))
    (N v₀ v₁ : ℕ) (hN : 0 < N)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (hstable : ∀ p ∈ P, ∀ m,
      HasFactorInAll rest (p * m) ↔ HasFactorInAll rest m)
    (q : ℕ → ℕ)
    (hqcell : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), q v ∈ eadicCell P (2 * N) v)
    (hq1 : ∀ v, 1 ≤ q v)
    (hqmin : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, q v ≤ p)
    (hLA : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, A / (N * p) + 1 ≤ A / p)
    (hLB : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, (A + Δ) / (N * p) + 1 ≤ (A + Δ) / p)
    (w : ℝ → ℝ) (hwm : Measurable w) (hw0 : ∀ ξ, 0 ≤ w ξ)
    (hwsup : ∀ ξ, w ξ ≤ (4*(H:ℝ)/(A:ℝ))^2)
    (K₁ K₂ : ℝ)
    (J : ℕ) (Pset : ℕ → Set ℝ) (hPset : ∀ j, MeasurableSet (Pset j))
    (c₃ ε : ℝ) (hc₃ : 0 ≤ c₃)
    (hleg : ∀ j ∈ Finset.range (J + 1), j ≠ J →
      (4*(H:ℝ)/(A:ℝ))^2
          * ∫ ξ in bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} j,
            ‖∑ m ∈ typicalS A (A+Δ) (P :: rest), (g m/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
        ≤ (1 / 2 ^ (j + 1)) * bandBudget c₃ ε ((Δ:ℝ)/(A:ℝ)))
    (Pc : ℕ → ℕ) (hPc : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), 2 ≤ Pc v)
    (hlo : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), ∀ p ∈ eadicCell P (2 * N) v, Pc v < p)
    (hhi : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), ∀ p ∈ eadicCell P (2 * N) v,
      p ≤ 2 * Pc v)
    (T : ℝ) (hT1 : 1 ≤ T) (hTK₂ : K₂ + 2 ≤ T)
    (δ : ℕ → ℝ) (hδ0 : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), 0 < δ v)
    (hδ : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), ∀ t : ℝ, |t| ≤ T →
      ‖∑ n ∈ Finset.Icc 1 ((A + Δ) / q v),
          (cellBlockCoeff g A (A + Δ) P rest (q v) n/(n:ℂ))
            * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ δ v)
    (hA0 : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      0 < 64 * ((((A + Δ) / q v : ℕ):ℝ) + ((bandCells K₂).card:ℝ) * Real.sqrt T)
        * (Real.log (2*T) + 1)
        * ∑ n ∈ Finset.Icc 1 ((A + Δ) / q v),
            ‖cellBlockCoeff g A (A + Δ) P rest (q v) n‖^2/(n:ℝ)^2)
    (hB0 : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      0 < 64 * (∑ p ∈ eadicCell P (2 * N) v, ‖g p‖^2/(p:ℝ)^2)
        * (Pc v:ℝ) / Real.log (Pc v))
    (κ' : ℕ → ℝ)
    (hfit : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      2 * ((δ v)^2 * (64 * (256 / (Real.log (Pc v))^2))
        + 2 * δ v * Real.sqrt
            ((128 * ((((A + Δ) / q v : ℕ):ℝ) + 2*T*Real.sqrt T)
                * (Real.log (2*T) + 1))
              * ((64 * (256 / (Real.log (Pc v))^2))
                  * (Real.exp Real.pi * ((T+1)/(Pc v:ℝ) + 4)
                      * (256 / Real.log (Pc v) + 2048 * Real.pi)
                      * Real.exp (-(Real.log (Pc v) / (Real.log (2*T))^(3/4:ℝ)))
                      * (Real.log (2*T))^2))))
      ≤ κ' v * bandBudget c₃ ε ((Δ:ℝ)/(A:ℝ)))
    (hfitU : 2 * ((Finset.Ico v₀ (v₁ + 1)).card : ℝ)
          * (∑ v ∈ Finset.Ico v₀ (v₁ + 1), κ' v) * bandBudget c₃ ε ((Δ:ℝ)/(A:ℝ))
        + 2 * (2 * cellReplacementEnergyBound P N v₀ v₁ A (A + Δ) T
            + 2 * (4 * collisionEnergyBound A (A + Δ) P rest T))
      ≤ (1 / 2 ^ (J + 1)) * bandBudget c₃ ε ((Δ:ℝ)/(A:ℝ)) / (4*(H:ℝ)/(A:ℝ))^2) :
    (∫ ξ in {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂},
        ‖∑ m ∈ typicalS A (A+Δ) (P :: rest), (g m/(m:ℂ))
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2 * w ξ)
      ≤ bandBudget c₃ ε ((Δ:ℝ)/(A:ℝ)) := by
  have hT : (0:ℝ) < T := by linarith
  have hGT : bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} J
      ⊆ Set.Ioc (-T) T := by
    intro ξ hξ
    have h := inner_band_subset_Icc K₁ K₂ (bandPartOn_subset Pset J _ J hξ)
    rw [Set.mem_Icc] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hGm : MeasurableSet (bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} J) :=
    bandPartOn_measurableSet Pset hPset J _ (measurableSet_inner_band K₁ K₂) J
  -- the replacement energy on the exceptional part, by II-2e (VI-2t)
  have hrepl : (∫ ξ in bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} J,
        ‖typicalSCellReplacement g A (A + Δ) P rest N v₀ v₁ q ξ‖^2)
      ≤ cellReplacementEnergyBound P N v₀ v₁ A (A + Δ) T :=
    setIntegral_norm_sq_typicalSCellReplacement_le g hg A (A + Δ)
      (Nat.le_add_right A Δ) P rest N v₀ v₁ hN q hqcell hq1 hqmin hLA hLB T hT _
      hGm hGT
  -- the adjusted collision, through the enclosing interval (VI-2ab)
  have hcoll : (∫ ξ in bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} J,
        ‖typicalSAdjustedCollision g A (A + Δ) P rest N v₀ v₁ ξ‖^2)
      ≤ 4 * collisionEnergyBound A (A + Δ) P rest T :=
    (ExpSums.setIntegral_le_intervalIntegral_of_nonneg
      (fun ξ => ‖typicalSAdjustedCollision g A (A + Δ) P rest N v₀ v₁ ξ‖^2)
      ((continuous_typicalSAdjustedCollision g A (A + Δ) P rest N v₀ v₁).norm.pow 2)
      (fun ξ => sq_nonneg _) T hT.le _ hGT).trans
      (intervalIntegral_norm_sq_typicalSAdjustedCollision_le g hg A Δ hΔA P hP hPA
        rest N v₀ v₁ hcov T hT)
  -- one `L²` triangle between the two
  have hsplit : (∫ ξ in bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} J,
        ‖typicalSCellReplacement g A (A + Δ) P rest N v₀ v₁ q ξ
          + typicalSAdjustedCollision g A (A + Δ) P rest N v₀ v₁ ξ‖^2)
      ≤ 2 * (∫ ξ in bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} J,
            ‖typicalSCellReplacement g A (A + Δ) P rest N v₀ v₁ q ξ‖^2)
        + 2 * (∫ ξ in bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} J,
            ‖typicalSAdjustedCollision g A (A + Δ) P rest N v₀ v₁ ξ‖^2) :=
    ExpSums.setIntegral_norm_add_sq_le _ _
      (continuous_typicalSCellReplacement g A (A + Δ) P rest N v₀ v₁ q)
      (continuous_typicalSAdjustedCollision g A (A + Δ) P rest N v₀ v₁) T _ hGm hGT
  refine band_energy_typicalS_le_of_cellUniform g hcm hg A Δ H hA hH P hP rest N
    v₀ v₁ hcov hstable q hqcell w hwm hw0 hwsup K₁ K₂ J Pset hPset c₃ ε hc₃ hleg
    Pc hPc hlo hhi T hT1 hTK₂ δ hδ0 hδ hA0 hB0 κ' hfit ?_
  have hE : (∫ ξ in bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} J,
        ‖typicalSCellReplacement g A (A + Δ) P rest N v₀ v₁ q ξ
          + typicalSAdjustedCollision g A (A + Δ) P rest N v₀ v₁ ξ‖^2)
      ≤ 2 * cellReplacementEnergyBound P N v₀ v₁ A (A + Δ) T
        + 2 * (4 * collisionEnergyBound A (A + Δ) P rest T) := by
    linarith [hsplit, hrepl, hcoll]
  linarith [hE, hfitU]

end Tao2015

end MoltResearch
