import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5BandEnergyExceptional

/-!
# The `[mrt]` A.2 band capstone, conditional half (Track R, A2-III, VI-1d)

The elementary half of the capstone lives in
`MoltResearch/Discrepancy/BandCapstone.lean`: `band_energy_le_budget` covers the
inner band by its parts, relaxes the frequency weight on each, and closes the
argument once every part meets its share of `bandBudget`.  It says nothing about
*how* a part meets its share — every leg is a hypothesis.

For the levels `𝒯₁, …, 𝒯_J` that is right: their legs
(`band_energy_level_one_le`, `band_energy_level_le_of_prev_large`, and the
cell-summed forms `setIntegral_norm_sq_cell_prime_block_le` and
`setIntegral_norm_sq_level_sum_of_prev_large_le`) are elementary and unconditional,
and a consumer discharges them in the nucleus.  The exceptional part `𝒰` is not:
it rests on `HalaszLargeValuesAssumption` (Iwaniec–Kowalski Thm 9.6) and
`PrimeLargeValuesAssumption` ([MR] Lemma 8), and `scripts/check_layering.sh`
forbids `MoltResearch/` from importing the tree those classes live in.

**That layering constraint is the whole reason this module exists**, and it is
the same seam that split IV-3 into an elementary half in the nucleus and a
conditional half here.  This file is where the two halves finally meet: the
partition assembly from the nucleus, with the one part it cannot discharge
discharged.
-/

namespace MoltResearch

namespace Tao2015

open MeasureTheory in
/-- **A2-III VI-1d-6 — the band capstone, conditional.**

The endpoint of the `[mrt]` A.2 band estimate: the weighted band energy is at
most the slice's budget `𝔅 = c₃ε²ρ/8`, conditional on exactly the two
large-values interfaces.

The partition is `𝒮` with one distinguished member `u`, whose part is the
exceptional set `𝒰`.  Every other part is a level `𝒯_j` and comes with its leg
as a hypothesis (`hleg`); the part at `u` has no hypothesis, because it is
discharged here by `setIntegral_band_energy_exceptional_le_budget`.

**Three seams meet in the statement, and each is a real hypothesis rather than a
convention.**

* `hfac` is the **factorisation** seam.  On `𝒰` — and only there — the band
  integrand must be presented as a product of a prime polynomial and an integer
  polynomial, which is what `[MR]`'s decomposition lemma (II-2) supplies and what
  the two large-values interfaces consume.  On a level `𝒯_j` the integrand is a
  cell polynomial against a block, a different factorisation entirely.  It is
  stated as `≤` rather than `=` so that a consumer may discard a harmless factor
  when applying II-2.
* `hfitU` is the **budget** seam, and it carries the weight explicitly: the leg
  bounds the *bare* energy while the capstone measures the *weighted* one, so the
  share available to `𝒰` is `κ u · 𝔅 / Cw`.  Dividing rather than multiplying
  keeps `hfitU` in the exact shape `setIntegral_band_energy_exceptional_le_budget`
  takes, so a consumer composes with nothing.
* `hKT` is the **frequency-range** seam.  The `𝒰` leg needs its sample cells
  inside `[−T, T]`; since VI-1d-2 the cells carry that condition rather than the
  sample points, so a consumer states where its cells are and never has to
  construct a sample family at all.

**What this theorem does not do.**  It does not instantiate the schedule: `Aint`,
`Bpri`, `Γ`, `δ`, the shares `κ`, and the level legs are all supplied.  Binding
those to `S1`–`S7` needs Mertens-type prime inputs and is a separate campaign —
the same one `BandSchedule`'s module note sets aside.  What is closed here is the
*shape*: every part of the band is priced against one budget, in one statement,
with the conditional part conditional on exactly two quotable hypotheses. -/
theorem band_energy_le_budget_of_exceptional [HalaszLargeValuesAssumption]
    [PrimeLargeValuesAssumption] {ι : Type*} [DecidableEq ι]
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
    (P : ℕ) (hP : 2 ≤ P) (Y : Finset ℕ) (hY : ∀ p ∈ Y, p.Prime)
    (hlo : ∀ p ∈ Y, P < p) (hhi : ∀ p ∈ Y, p ≤ 2*P)
    (b : ℕ → ℂ) (hb : ∀ p, ‖b p‖ ≤ 1)
    (N : ℕ) (a : ℕ → ℂ) (T : ℝ) (hT1 : 1 ≤ T)
    (K : Finset ℤ)
    (hcoverU : part u ⊆ ⋃ k ∈ K, Set.Ico (k:ℝ) ((k:ℝ)+1))
    (hKT : ∀ k ∈ K, -T ≤ (k:ℝ) ∧ (k:ℝ) + 1 ≤ T)
    (δ lam : ℝ) (hδ0 : 0 < δ) (hlam : 0 < lam)
    (hδ : ∀ t : ℝ, |t| ≤ T →
      ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ δ)
    (hfac : ∀ ξ ∈ part u, ‖F ξ‖^2
      ≤ ‖∑ p ∈ Y, (b p/(p:ℂ))
            * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖^2
        * ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
            * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
    (hintU : IntegrableOn (fun ξ => ‖∑ p ∈ Y, (b p/(p:ℂ))
          * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖^2
        * ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
            * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2) (part u))
    (Aint Bpri Γ : ℝ)
    (hAint : Aint = 64 * ((N:ℝ) + (K.card:ℝ) * Real.sqrt T)
      * (Real.log (2*T) + 1) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖^2/(n:ℝ)^2)
    (hBpri : Bpri = 64 * (∑ p ∈ Y, ‖b p‖^2/(p:ℝ)^2) * (P:ℝ) / Real.log P)
    (hΓ : Γ = (Real.exp Real.pi * ((T+1)/(P:ℝ) + 2*(2:ℝ))
          * ((1+lam) + (1/lam)*(2*Real.pi*Real.log (2*(P:ℝ)))^2)
          * (∑ p ∈ Y, (1:ℝ)/(p:ℝ)))
        * Real.exp (-(Real.log P / (Real.log (2*T))^(3/4:ℝ)))
        * (Real.log (2*T))^2)
    (hA0 : 0 < Aint) (hB0 : 0 < Bpri) (hΓ0 : 0 < Γ)
    (hfitU : 2 * (δ^2 * Bpri + 2 * δ * Real.sqrt (Aint * (Bpri * Γ)))
      ≤ κ u * bandBudget c₃ ε ρ / Cw) :
    (∫ ξ in G, ‖F ξ‖^2 * w ξ) ≤ bandBudget c₃ ε ρ := by
  -- The exceptional part, discharged from the two large-values interfaces.
  have hU := setIntegral_band_energy_exceptional_le_budget P hP Y hY hlo hhi b hb
    N a T hT1 (part u) K hcoverU hKT δ lam hδ0 hlam hδ Aint Bpri Γ hAint hBpri hΓ
    hA0 hB0 hΓ0 c₃ ε ρ (κ u / Cw) (by rw [div_mul_eq_mul_div]; exact hfitU)
  have hUleg : Cw * ∫ ξ in part u, ‖F ξ‖^2 ≤ κ u * bandBudget c₃ ε ρ := by
    have hmono : (∫ ξ in part u, ‖F ξ‖^2)
        ≤ ∫ ξ in part u, ‖∑ p ∈ Y, (b p/(p:ℂ))
              * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖^2
            * ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
                * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2 :=
      setIntegral_mono_on (hint u hu) hintU (hmeas u hu) hfac
    calc Cw * ∫ ξ in part u, ‖F ξ‖^2
        ≤ Cw * (κ u / Cw * bandBudget c₃ ε ρ) :=
          mul_le_mul_of_nonneg_left (hmono.trans hU) hCw.le
      _ = κ u * bandBudget c₃ ε ρ := by field_simp
  -- Every part now meets its share, so the nucleus assembly closes it.
  refine band_energy_le_budget F w hw0 Cw hwC G 𝒮 part hmeas hdisj hcover hint
    hintw κ c₃ ε ρ hc₃ hρ (fun i hi => ?_) hκ
  by_cases hiu : i = u
  · subst hiu; exact hUleg
  · exact hleg i hi hiu

open MeasureTheory in
/-- **A2-III M-8 — the band capstone with the `𝒰` leg's constants instantiated.**

`band_energy_le_budget_of_exceptional` takes the exceptional leg's three groups
`Aint`, `Bpri`, `Γ` as equations and its fit condition `hfitU` at their *true*
values.  A consumer does not have those in closed form; what it has is the
instantiation campaign's upper bounds, one per group.  This corollary is the
composition, and it removes four arguments (`lam`, `Γ`, and their two side
conditions) while replacing `hfitU` by a condition in `δ`, `P`, `N`, `T`, `ε`
and the share alone.

The three bounds it composes:

* `Aint ≤ 128·(N + 2T^{3/2})·(log 2T + 1)`
  (`integer_largeValues_factor_le`, M-5) — the cover's `#K` is priced by
  `card_cells_le` and the coefficient energy by `integer_energy_le`;
* `Bpri ≤ 64·256/(log P)²` (`prime_energy_dyadic_le`, M-4) — the `P` of the
  prime large-values theorem cancels the block's `1/P` exactly;
* `Γ ≤ e^π((T+1)/P + 4)(256/log P + 2048π)e^{−log P/(log 2T)^{3/4}}(log 2T)²`
  (`exists_lam_exceptional_ratio_le`, M-6), at the balanced Ramaré parameter.

**`lam` disappears rather than being passed through, and that is the point.**
It is the estimate's own parameter, not the consumer's, exactly as `V₀` is; M-6
exhibits the balanced value and this corollary consumes it internally.  What is
left of the `𝒰` leg's arithmetic is `hfit`, whose only non-schedule input is
`δ` — and `δ` comes from the IV-0 Halász chain, not from counting.

`Y.Nonempty` is what makes `Γ` strictly positive (through the block's prime
mass); `hA0` and `hB0` are stated on the literal group expressions because a
consumer knows its own coefficients and the tree cannot know that they do not
all vanish. -/
theorem band_energy_le_budget_of_exceptional_instantiated
    [HalaszLargeValuesAssumption] [PrimeLargeValuesAssumption]
    {ι : Type*} [DecidableEq ι]
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
    (P : ℕ) (hP : 2 ≤ P) (Y : Finset ℕ) (hY : ∀ p ∈ Y, p.Prime)
    (hYne : Y.Nonempty)
    (hlo : ∀ p ∈ Y, P < p) (hhi : ∀ p ∈ Y, p ≤ 2*P)
    (b : ℕ → ℂ) (hb : ∀ p, ‖b p‖ ≤ 1)
    (N : ℕ) (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (T : ℝ) (hT1 : 1 ≤ T)
    (K : Finset ℤ)
    (hcoverU : part u ⊆ ⋃ k ∈ K, Set.Ico (k:ℝ) ((k:ℝ)+1))
    (hKT : ∀ k ∈ K, -T ≤ (k:ℝ) ∧ (k:ℝ) + 1 ≤ T)
    (δ : ℝ) (hδ0 : 0 < δ)
    (hδ : ∀ t : ℝ, |t| ≤ T →
      ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ δ)
    (hfac : ∀ ξ ∈ part u, ‖F ξ‖^2
      ≤ ‖∑ p ∈ Y, (b p/(p:ℂ))
            * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖^2
        * ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
            * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
    (hintU : IntegrableOn (fun ξ => ‖∑ p ∈ Y, (b p/(p:ℂ))
          * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖^2
        * ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
            * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2) (part u))
    (hA0 : 0 < 64 * ((N:ℝ) + (K.card:ℝ) * Real.sqrt T)
      * (Real.log (2*T) + 1) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖^2/(n:ℝ)^2)
    (hB0 : 0 < 64 * (∑ p ∈ Y, ‖b p‖^2/(p:ℝ)^2) * (P:ℝ) / Real.log P)
    (hfit : 2 * (δ^2 * (64 * (256 / (Real.log P)^2))
        + 2 * δ * Real.sqrt
            ((128 * ((N:ℝ) + 2*T*Real.sqrt T) * (Real.log (2*T) + 1))
              * ((64 * (256 / (Real.log P)^2))
                  * (Real.exp Real.pi * ((T+1)/(P:ℝ) + 4)
                      * (256 / Real.log P + 2048 * Real.pi)
                      * Real.exp (-(Real.log P / (Real.log (2*T))^(3/4:ℝ)))
                      * (Real.log (2*T))^2))))
      ≤ κ u * bandBudget c₃ ε ρ / Cw) :
    (∫ ξ in G, ‖F ξ‖^2 * w ξ) ≤ bandBudget c₃ ε ρ := by
  classical
  have hP0 : (0:ℝ) < (P:ℝ) := by
    have : 0 < P := by omega
    exact_mod_cast this
  have hlogP : (0:ℝ) < Real.log P := Real.log_pos (by exact_mod_cast hP)
  have hlog2T : (0:ℝ) < Real.log (2*T) := Real.log_pos (by linarith)
  -- the block's prime mass is strictly positive, which is what makes `Γ` positive
  obtain ⟨p₀, hp₀⟩ := hYne
  have hmass0 : (0:ℝ) < ∑ p ∈ Y, (1:ℝ)/(p:ℝ) := by
    refine Finset.sum_pos' (fun p _ => by positivity) ⟨p₀, hp₀, ?_⟩
    have : (0:ℝ) < (p₀:ℝ) := by exact_mod_cast (hY p₀ hp₀).pos
    positivity
  -- M-6 supplies the balanced Ramaré parameter and the bound on `Γ` at it
  obtain ⟨lam, hlam0, hΓle⟩ :=
    exists_lam_exceptional_ratio_le P hP Y hY hlo hhi T hT1
  set Aint : ℝ := 64 * ((N:ℝ) + (K.card:ℝ) * Real.sqrt T)
      * (Real.log (2*T) + 1) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖^2/(n:ℝ)^2 with hAint
  set Bpri : ℝ := 64 * (∑ p ∈ Y, ‖b p‖^2/(p:ℝ)^2) * (P:ℝ) / Real.log P with hBpri
  set Γ : ℝ := (Real.exp Real.pi * ((T+1)/(P:ℝ) + 2*(2:ℝ))
        * ((1+lam) + (1/lam)*(2*Real.pi*Real.log (2*(P:ℝ)))^2)
        * (∑ p ∈ Y, (1:ℝ)/(p:ℝ)))
      * Real.exp (-(Real.log P / (Real.log (2*T))^(3/4:ℝ)))
      * (Real.log (2*T))^2 with hΓ
  have hΓ0 : 0 < Γ := by
    rw [hΓ]
    have hsplit : (0:ℝ) < (1+lam) + (1/lam)*(2*Real.pi*Real.log (2*(P:ℝ)))^2 := by
      have : (0:ℝ) < 1/lam := by positivity
      nlinarith [sq_nonneg (2*Real.pi*Real.log (2*(P:ℝ)))]
    have hlead : (0:ℝ) < (T+1)/(P:ℝ) + 2*(2:ℝ) := by
      have : (0:ℝ) ≤ (T+1)/(P:ℝ) := by positivity
      linarith
    have hlogsq : (0:ℝ) < (Real.log (2*T))^2 := by positivity
    have := Real.exp_pos Real.pi
    have := Real.exp_pos (-(Real.log P / (Real.log (2*T))^(3/4:ℝ)))
    positivity
  -- the three instantiated bounds, and the seam that lets them discharge `hfitU`
  have hAle : Aint ≤ 128 * ((N:ℝ) + 2*T*Real.sqrt T) * (Real.log (2*T) + 1) := by
    rw [hAint]
    exact integer_largeValues_factor_le N a ha T hT1 K hKT
  have hBle : Bpri ≤ 64 * (256 / (Real.log P)^2) := by
    rw [hBpri]
    have := prime_energy_dyadic_le P hP Y hY hlo hhi b hb
    calc 64 * (∑ p ∈ Y, ‖b p‖^2/(p:ℝ)^2) * (P:ℝ) / Real.log P
        = 64 * ((∑ p ∈ Y, ‖b p‖^2/(p:ℝ)^2) * (P:ℝ) / Real.log P) := by ring
      _ ≤ 64 * (256 / (Real.log P)^2) := by gcongr
  have hfitU : 2 * (δ^2 * Bpri + 2 * δ * Real.sqrt (Aint * (Bpri * Γ)))
      ≤ κ u * bandBudget c₃ ε ρ / Cw := by
    have hrw : κ u * bandBudget c₃ ε ρ / Cw = (κ u / Cw) * bandBudget c₃ ε ρ := by
      rw [div_mul_eq_mul_div]
    rw [hrw] at hfit ⊢
    exact exceptional_fit_of_le Aint Bpri Γ
      (128 * ((N:ℝ) + 2*T*Real.sqrt T) * (Real.log (2*T) + 1))
      (64 * (256 / (Real.log P)^2))
      (Real.exp Real.pi * ((T+1)/(P:ℝ) + 4)
        * (256 / Real.log P + 2048 * Real.pi)
        * Real.exp (-(Real.log P / (Real.log (2*T))^(3/4:ℝ)))
        * (Real.log (2*T))^2)
      δ c₃ ε ρ (κ u / Cw) hA0.le hB0.le hΓ0.le hδ0.le hAle hBle hΓle hfit
  exact band_energy_le_budget_of_exceptional F w hw0 Cw hCw hwC G 𝒮 part hmeas
    hdisj hcover hint hintw κ c₃ ε ρ hc₃ hρ hκ u hu hleg P hP Y hY hlo hhi b hb
    N a T hT1 K hcoverU hKT δ lam hδ0 hlam0 hδ hfac hintU Aint Bpri Γ hAint hBpri
    hΓ hA0 hB0 hΓ0 hfitU


open MeasureTheory in
/-- **A2-III VI-1e-3 — the band capstone on the `[MR]` partition.**

`band_energy_le_budget_of_exceptional_instantiated` with its partition supplied
by the first-index construction (VI-1e-1/VI-1e-2): the exceptional part is
`bandPartOn P J G J`, the levels are `bandPartOn P J G j` for `j < J`, and
`bandPart_pairwiseDisjoint`/`bandPartOn_cover` discharge the set-theoretic
hypotheses.

**Three hypotheses become two, and the two are ones the band already has.**
`hmeas`, `hdisj`, `hcover` and `hcoverU` are replaced by `MeasurableSet G` and a
single cell cover `hGcover : G ⊆ ⋃_{k ∈ K} [k, k+1)` of the band itself.  The
exceptional part's cover comes for free from `bandPartOn_subset`, which is the
reason VI-1e-2's relative partition exists: the absolute one's exceptional part
is a complement, and no finite cell family covers it.

What is left is exactly the analytic content of `[mrt]` A.2's inner band: one
elementary leg per level, the shares, and — for the exceptional part — the
pointwise Halász input `δ` and the instantiated fit.  Nothing set-theoretic
remains, and nothing about the constants: `Aint`, `Bpri`, `Γ` and the Ramaré
parameter were absorbed by M-4…M-8.

The index `u` is `J` rather than an abstract element because the construction
puts the exceptional part at the top index; `hleg` is correspondingly stated for
`j ≠ J`. -/
theorem band_energy_le_budget_of_exceptional_partition
    [HalaszLargeValuesAssumption] [PrimeLargeValuesAssumption]
    (F : ℝ → ℂ) (w : ℝ → ℝ) (hw0 : ∀ ξ, 0 ≤ w ξ)
    (Cw : ℝ) (hCw : 0 < Cw) (hwC : ∀ ξ, w ξ ≤ Cw)
    (G : Set ℝ) (hG : MeasurableSet G)
    (J : ℕ) (Pset : ℕ → Set ℝ) (hPset : ∀ j, MeasurableSet (Pset j))
    (hint : ∀ j ∈ Finset.range (J + 1),
      IntegrableOn (fun ξ => ‖F ξ‖^2) (bandPartOn Pset J G j))
    (hintw : ∀ j ∈ Finset.range (J + 1),
      IntegrableOn (fun ξ => ‖F ξ‖^2 * w ξ) (bandPartOn Pset J G j))
    (κ : ℕ → ℝ) (c₃ ε ρ : ℝ) (hc₃ : 0 ≤ c₃) (hρ : 0 ≤ ρ)
    (hκ : ∑ j ∈ Finset.range (J + 1), κ j ≤ 1)
    (hleg : ∀ j ∈ Finset.range (J + 1), j ≠ J →
      Cw * ∫ ξ in bandPartOn Pset J G j, ‖F ξ‖^2 ≤ κ j * bandBudget c₃ ε ρ)
    (P : ℕ) (hP : 2 ≤ P) (Y : Finset ℕ) (hY : ∀ p ∈ Y, p.Prime)
    (hYne : Y.Nonempty)
    (hlo : ∀ p ∈ Y, P < p) (hhi : ∀ p ∈ Y, p ≤ 2*P)
    (b : ℕ → ℂ) (hb : ∀ p, ‖b p‖ ≤ 1)
    (N : ℕ) (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (T : ℝ) (hT1 : 1 ≤ T)
    (K : Finset ℤ)
    (hGcover : G ⊆ ⋃ k ∈ K, Set.Ico (k:ℝ) ((k:ℝ)+1))
    (hKT : ∀ k ∈ K, -T ≤ (k:ℝ) ∧ (k:ℝ) + 1 ≤ T)
    (δ : ℝ) (hδ0 : 0 < δ)
    (hδ : ∀ t : ℝ, |t| ≤ T →
      ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ δ)
    (hfac : ∀ ξ ∈ bandPartOn Pset J G J, ‖F ξ‖^2
      ≤ ‖∑ p ∈ Y, (b p/(p:ℂ))
            * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖^2
        * ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
            * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
    (hintU : IntegrableOn (fun ξ => ‖∑ p ∈ Y, (b p/(p:ℂ))
          * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖^2
        * ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
            * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
        (bandPartOn Pset J G J))
    (hA0 : 0 < 64 * ((N:ℝ) + (K.card:ℝ) * Real.sqrt T)
      * (Real.log (2*T) + 1) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖^2/(n:ℝ)^2)
    (hB0 : 0 < 64 * (∑ p ∈ Y, ‖b p‖^2/(p:ℝ)^2) * (P:ℝ) / Real.log P)
    (hfit : 2 * (δ^2 * (64 * (256 / (Real.log P)^2))
        + 2 * δ * Real.sqrt
            ((128 * ((N:ℝ) + 2*T*Real.sqrt T) * (Real.log (2*T) + 1))
              * ((64 * (256 / (Real.log P)^2))
                  * (Real.exp Real.pi * ((T+1)/(P:ℝ) + 4)
                      * (256 / Real.log P + 2048 * Real.pi)
                      * Real.exp (-(Real.log P / (Real.log (2*T))^(3/4:ℝ)))
                      * (Real.log (2*T))^2))))
      ≤ κ J * bandBudget c₃ ε ρ / Cw) :
    (∫ ξ in G, ‖F ξ‖^2 * w ξ) ≤ bandBudget c₃ ε ρ :=
  band_energy_le_budget_of_exceptional_instantiated F w hw0 Cw hCw hwC G
    (Finset.range (J + 1)) (bandPartOn Pset J G)
    (fun j _ => bandPartOn_measurableSet Pset hPset J G hG j)
    (bandPartOn_pairwiseDisjoint Pset J G)
    (bandPartOn_cover Pset J G)
    hint hintw κ c₃ ε ρ hc₃ hρ hκ J (Finset.mem_range.mpr (by omega))
    (fun j hj hjJ => hleg j hj hjJ)
    P hP Y hY hYne hlo hhi b hb N a ha T hT1 K
    ((bandPartOn_subset Pset J G J).trans hGcover) hKT δ hδ0 hδ hfac hintU
    hA0 hB0 hfit


open MeasureTheory in
/-- **A2-III VI-1f-3 — the band capstone on the inner band itself.**

`band_energy_le_budget_of_exceptional_partition` with its remaining structural
hypotheses discharged by taking the band to be `{K₁ ≤ |ξ| ≤ K₂}`, the range the
`[mrt]` A.2 estimate is actually stated on.

**Seven hypotheses go, and each was structural rather than analytic.**
`MeasurableSet G` and the `2(J+1)` integrability facts fall to VI-1f-1
(`band_energy_le_budget_inner_band`'s ingredients): the band sits in a compact
interval, so a continuous `F` against a measurable bounded `w` is integrable on
every part at once.  The cell family `K`, its cover `hGcover` and its range
`hKT` fall to VI-1f-2: the cells are `bandCells K₂ = [−⌈K₂⌉, ⌈K₂⌉] ∩ ℤ`, and
nothing in the tree had ever constructed such a family — every consumer of the
exceptional leg took one as a hypothesis.  `hintU` falls to continuity of the
two factors of the `[MR]` decomposition.

**What replaces them is a single numerical condition, `hTK₂ : K₂ + 2 ≤ T`**, and
that is the honest frequency-range seam: the exceptional leg's sample range has
to clear the band's outer cut by two — one for the ceiling, one for the cell's
own width.  Besides continuity of `F` and measurability of `w`, it is all that
is asked in return, and it is a demand on the schedule rather than on the
consumer's set theory.

What is left is exactly `[mrt]` A.2's analytic content: one elementary leg per
level, the shares, the factorisation `hfac` supplied by the `[MR]` decomposition
lemma, and the pointwise Halász input `δ` with the instantiated fit.  `F` and
`w` are continuous and measurable respectively and otherwise still free; binding
`F` to the `typicalS` polynomial is the A.2 statement itself. -/
theorem band_energy_le_budget_of_exceptional_inner_band
    [HalaszLargeValuesAssumption] [PrimeLargeValuesAssumption]
    (F : ℝ → ℂ) (hF : Continuous F)
    (w : ℝ → ℝ) (hwm : Measurable w) (hw0 : ∀ ξ, 0 ≤ w ξ)
    (Cw : ℝ) (hCw : 0 < Cw) (hwC : ∀ ξ, w ξ ≤ Cw)
    (K₁ K₂ : ℝ)
    (J : ℕ) (Pset : ℕ → Set ℝ) (hPset : ∀ j, MeasurableSet (Pset j))
    (κ : ℕ → ℝ) (c₃ ε ρ : ℝ) (hc₃ : 0 ≤ c₃) (hρ : 0 ≤ ρ)
    (hκ : ∑ j ∈ Finset.range (J + 1), κ j ≤ 1)
    (hleg : ∀ j ∈ Finset.range (J + 1), j ≠ J →
      Cw * ∫ ξ in bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} j, ‖F ξ‖^2
        ≤ κ j * bandBudget c₃ ε ρ)
    (P : ℕ) (hP : 2 ≤ P) (Y : Finset ℕ) (hY : ∀ p ∈ Y, p.Prime)
    (hYne : Y.Nonempty)
    (hlo : ∀ p ∈ Y, P < p) (hhi : ∀ p ∈ Y, p ≤ 2*P)
    (b : ℕ → ℂ) (hb : ∀ p, ‖b p‖ ≤ 1)
    (N : ℕ) (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (T : ℝ) (hT1 : 1 ≤ T)
    (hTK₂ : K₂ + 2 ≤ T)
    (δ : ℝ) (hδ0 : 0 < δ)
    (hδ : ∀ t : ℝ, |t| ≤ T →
      ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ δ)
    (hfac : ∀ ξ ∈ bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} J, ‖F ξ‖^2
      ≤ ‖∑ p ∈ Y, (b p/(p:ℂ))
            * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖^2
        * ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
            * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
    (hA0 : 0 < 64 * ((N:ℝ) + ((bandCells K₂).card:ℝ) * Real.sqrt T)
      * (Real.log (2*T) + 1) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖^2/(n:ℝ)^2)
    (hB0 : 0 < 64 * (∑ p ∈ Y, ‖b p‖^2/(p:ℝ)^2) * (P:ℝ) / Real.log P)
    (hfit : 2 * (δ^2 * (64 * (256 / (Real.log P)^2))
        + 2 * δ * Real.sqrt
            ((128 * ((N:ℝ) + 2*T*Real.sqrt T) * (Real.log (2*T) + 1))
              * ((64 * (256 / (Real.log P)^2))
                  * (Real.exp Real.pi * ((T+1)/(P:ℝ) + 4)
                      * (256 / Real.log P + 2048 * Real.pi)
                      * Real.exp (-(Real.log P / (Real.log (2*T))^(3/4:ℝ)))
                      * (Real.log (2*T))^2))))
      ≤ κ J * bandBudget c₃ ε ρ / Cw) :
    (∫ ξ in {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂}, ‖F ξ‖^2 * w ξ)
      ≤ bandBudget c₃ ε ρ := by
  have hwnorm : ∀ ξ, ‖w ξ‖ ≤ Cw := fun ξ => by
    rw [Real.norm_of_nonneg (hw0 ξ)]; exact hwC ξ
  -- the two factors of the `[MR]` decomposition are continuous, hence so is
  -- their energy product, which is all `hintU` needs on a bounded band
  have hprod : Continuous fun ξ : ℝ =>
      ‖∑ p ∈ Y, (b p/(p:ℂ))
          * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖^2
        * ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
            * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2 :=
    ((ExpSums.continuous_char_poly Y (fun p => b p/(p:ℂ))
        (fun p => Real.log p)).norm.pow 2).mul
      ((ExpSums.continuous_char_poly (Finset.Icc 1 N) (fun n => a n/(n:ℂ))
        (fun n => Real.log n)).norm.pow 2)
  exact band_energy_le_budget_of_exceptional_partition F w hw0 Cw hCw hwC
    {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} (measurableSet_inner_band K₁ K₂) J Pset hPset
    (fun j _ => integrableOn_norm_sq_inner_band F hF K₁ K₂ _
      (bandPartOn_subset Pset J _ j))
    (fun j _ => integrableOn_norm_sq_mul_inner_band F hF w hwm Cw hwnorm K₁ K₂ _
      (bandPartOn_subset Pset J _ j))
    κ c₃ ε ρ hc₃ hρ hκ hleg P hP Y hY hYne hlo hhi b hb N a ha T hT1
    (bandCells K₂)
    (inner_band_subset_bandCells K₁ K₂)
    (bandCells_mem_Icc K₂ T hTK₂)
    δ hδ0 hδ hfac
    ((hprod.integrableOn_Icc).mono_set
      ((bandPartOn_subset Pset J _ J).trans (inner_band_subset_Icc K₁ K₂)))
    hA0 hB0 hfit


open MeasureTheory in
/-- **A2-III VI-1f-4 — `band_energy_typicalS_le`, the `[mrt]` A.2 inner-band
estimate.**

The statement A.2 is *about*, named in the design report (§ Phase VI, VI-1) and
until now absent from the tree: the weighted energy of the **typical-set**
polynomial over the inner band, against the band's share of the slice budget.

Everything structural is gone.  `F` is the polynomial itself, so its continuity
is discharged by `ExpSums.continuous_char_poly`; `Cw` is the slice window's
transform sup `(4H/A)²` (`norm_fourier_slice_window_le`), so `hCw` reduces to
`0 < A` and `0 < H`; and the budget's ratio is `ρ = Δ/A`, so `hρ` disappears
outright — a quotient of natural-number casts is nonnegative.

**The window is still only weighted, not fixed**, and that is deliberate.  A.2
needs from it exactly one thing, `hwsup`, and the outer band's decay hypothesis
(`hwdecay` in the report) belongs to a different leg, `outer_le_budget`.  Naming
a bump here would tie the inner band to a construction it never uses.

What a consumer still supplies is exactly `[mrt]` A.2's mathematics: the level
legs, the shares, the factorisation `hfac` that the `[MR]` decomposition lemma
(II-2) produces on the exceptional part, and the pointwise Halász input `δ` with
the instantiated fit. -/
theorem band_energy_typicalS_le [HalaszLargeValuesAssumption]
    [PrimeLargeValuesAssumption]
    (g : ℕ → ℂ) (A Δ H : ℕ) (hA : 0 < A) (hH : 0 < H)
    (levels : List (Finset ℕ))
    (w : ℝ → ℝ) (hwm : Measurable w) (hw0 : ∀ ξ, 0 ≤ w ξ)
    (hwsup : ∀ ξ, w ξ ≤ (4*(H:ℝ)/(A:ℝ))^2)
    (K₁ K₂ : ℝ)
    (J : ℕ) (Pset : ℕ → Set ℝ) (hPset : ∀ j, MeasurableSet (Pset j))
    (κ : ℕ → ℝ) (c₃ ε : ℝ) (hc₃ : 0 ≤ c₃)
    (hκ : ∑ j ∈ Finset.range (J + 1), κ j ≤ 1)
    (hleg : ∀ j ∈ Finset.range (J + 1), j ≠ J →
      (4*(H:ℝ)/(A:ℝ))^2
          * ∫ ξ in bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} j,
            ‖∑ m ∈ typicalS A (A+Δ) levels, (g m/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
        ≤ κ j * bandBudget c₃ ε ((Δ:ℝ)/(A:ℝ)))
    (P : ℕ) (hP : 2 ≤ P) (Y : Finset ℕ) (hY : ∀ p ∈ Y, p.Prime)
    (hYne : Y.Nonempty)
    (hlo : ∀ p ∈ Y, P < p) (hhi : ∀ p ∈ Y, p ≤ 2*P)
    (b : ℕ → ℂ) (hb : ∀ p, ‖b p‖ ≤ 1)
    (N : ℕ) (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (T : ℝ) (hT1 : 1 ≤ T)
    (hTK₂ : K₂ + 2 ≤ T)
    (δ : ℝ) (hδ0 : 0 < δ)
    (hδ : ∀ t : ℝ, |t| ≤ T →
      ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ δ)
    (hfac : ∀ ξ ∈ bandPartOn Pset J {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} J,
      ‖∑ m ∈ typicalS A (A+Δ) levels, (g m/(m:ℂ))
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
      ≤ ‖∑ p ∈ Y, (b p/(p:ℂ))
            * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖^2
        * ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ))
            * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
    (hA0 : 0 < 64 * ((N:ℝ) + ((bandCells K₂).card:ℝ) * Real.sqrt T)
      * (Real.log (2*T) + 1) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖^2/(n:ℝ)^2)
    (hB0 : 0 < 64 * (∑ p ∈ Y, ‖b p‖^2/(p:ℝ)^2) * (P:ℝ) / Real.log P)
    (hfit : 2 * (δ^2 * (64 * (256 / (Real.log P)^2))
        + 2 * δ * Real.sqrt
            ((128 * ((N:ℝ) + 2*T*Real.sqrt T) * (Real.log (2*T) + 1))
              * ((64 * (256 / (Real.log P)^2))
                  * (Real.exp Real.pi * ((T+1)/(P:ℝ) + 4)
                      * (256 / Real.log P + 2048 * Real.pi)
                      * Real.exp (-(Real.log P / (Real.log (2*T))^(3/4:ℝ)))
                      * (Real.log (2*T))^2))))
      ≤ κ J * bandBudget c₃ ε ((Δ:ℝ)/(A:ℝ)) / (4*(H:ℝ)/(A:ℝ))^2) :
    (∫ ξ in {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂},
        ‖∑ m ∈ typicalS A (A+Δ) levels, (g m/(m:ℂ))
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2 * w ξ)
      ≤ bandBudget c₃ ε ((Δ:ℝ)/(A:ℝ)) := by
  have hA0' : (0:ℝ) < (A:ℝ) := by exact_mod_cast hA
  have hH0' : (0:ℝ) < (H:ℝ) := by exact_mod_cast hH
  have hCw : (0:ℝ) < (4*(H:ℝ)/(A:ℝ))^2 := by positivity
  exact band_energy_le_budget_of_exceptional_inner_band
    (fun ξ => ∑ m ∈ typicalS A (A+Δ) levels, (g m/(m:ℂ))
      * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
    (ExpSums.continuous_char_poly (typicalS A (A+Δ) levels)
      (fun m => g m/(m:ℂ)) (fun m => Real.log m))
    w hwm hw0 ((4*(H:ℝ)/(A:ℝ))^2) hCw hwsup K₁ K₂ J Pset hPset κ c₃ ε
    ((Δ:ℝ)/(A:ℝ)) hc₃ (by positivity) hκ hleg P hP Y hY hYne hlo hhi b hb
    N a ha T hT1 hTK₂ δ hδ0 hδ hfac hA0 hB0 hfit


end Tao2015

end MoltResearch
