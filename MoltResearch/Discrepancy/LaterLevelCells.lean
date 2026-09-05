import MoltResearch.Discrepancy.LevelLegs

/-!
# Per-cell later-level estimates

The later-level moment argument is naturally indexed by both the previous
large cell and the current quotient cell.  This leaf keeps the current-cell
quotient interval and moment order explicit, so the subsequent numerology can
sum the resulting `v`-series without replacing it by level endpoints.
-/

namespace MoltResearch

open MeasureTheory Finset ExpSums in
/-- The previous-large-cell estimate summed over current cells, with a
separate quotient interval and moment order in every current cell. -/
theorem setIntegral_norm_sq_level_sum_of_prev_large_le_cells
    (Y : Finset ℕ) (hY : ∀ p ∈ Y, p.Prime) (P : ℕ) (hP : 1 ≤ P)
    (hlo : ∀ p ∈ Y, P < p) (hhi : ∀ p ∈ Y, p ≤ 2 * P)
    (b : ℕ → ℂ) (hb : ∀ p, ‖b p‖ ≤ 1) (ℓ A' Δ' : ℕ → ℕ)
    (I : Finset ℕ) (hℓ : ∀ v ∈ I, 1 ≤ ℓ v)
    (hA' : ∀ v ∈ I, 1 ≤ A' v) (hΔ' : ∀ v ∈ I, Δ' v ≤ A' v)
    (S : ℕ → Finset ℕ)
    (hS : ∀ v ∈ I, S v ⊆ Finset.Ioc (A' v) (A' v + Δ' v))
    (a : ℕ → ℂ) (ha : ∀ m, ‖a m‖ ≤ 1)
    (Q : ℕ → ℝ → ℂ) (hQ : ∀ v ∈ I, Continuous (Q v))
    (T : ℝ) (hT : 0 < T) (G : Set ℝ) (hGm : MeasurableSet G)
    (hGT : G ⊆ Set.Ioc (-T) T)
    (small : ℕ → ℝ) (large : ℝ) (hlarge0 : 0 < large)
    (hsmall : ∀ v ∈ I, ∀ ξ ∈ G, ‖Q v ξ‖ ≤ small v)
    (hlarge : ∀ ξ ∈ G, large ≤ ‖∑ p ∈ Y, (b p / (p : ℂ))
        * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖) :
    (∫ ξ in G, ‖∑ v ∈ I, Q v ξ * (∑ m ∈ S v, (a m / (m : ℂ))
        * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))‖ ^ 2)
      ≤ (I.card : ℝ) * ∑ v ∈ I, (small v) ^ 2 / large ^ (2 * ℓ v)
          * (Real.exp Real.pi
              * (T / ((P ^ ℓ v * A' v : ℕ) : ℝ)
                + 2 * ((2 ^ (ℓ v + 1) : ℕ) : ℝ))
            * ((Nat.factorial (ℓ v) : ℝ) ^ 2
              * (((2 ^ (ℓ v + 1) : ℕ) : ℝ) * ((ℓ v : ℝ) + 1)
                * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ)) ^ ℓ v))) := by
  classical
  have hchar : ∀ w : ℝ, Continuous fun ξ : ℝ =>
      ((Real.fourierChar (-(w * ξ)) : Circle) : ℂ) := fun w =>
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hblk : ∀ v : ℕ, Continuous fun ξ : ℝ =>
      ∑ m ∈ S v, (a m / (m : ℂ))
        * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) := fun v =>
    continuous_finset_sum _ fun m _ => continuous_const.mul (hchar (Real.log m))
  exact setIntegral_norm_sq_sum_le_card_mul_of_setIntegral _ I
    (fun v hv => (hQ v hv).mul (hblk v)) T G hGm hGT _
    (fun v hv => band_energy_level_le_of_prev_large Y hY P hP hlo hhi b hb
      (ℓ v) (hℓ v hv) (A' v) (Δ' v) (hA' v hv) (hΔ' v hv)
      (S v) (hS v hv) a ha (Q v) (hQ v hv) T hT G hGm hGT
      (small v) large hlarge0 (hsmall v hv) hlarge)

open MeasureTheory Finset ExpSums in
/-- The per-cell form of the level-`j` main-term estimate.  The previous-cell
threshold is used exactly as supplied by `hlargeCell`; no level-wide endpoint
lower bound is inserted.  Likewise, the current-cell exponential series is
left explicit for the later ladder numerology instead of being collapsed to
level endpoints. -/
theorem band_energy_later_main_le_budget_cells
    (Pcur Pprev : Finset ℕ) (Ncur Nprev r : ℕ)
    (v₀ v₁ : ℕ) (Sblk : ℕ → Finset ℕ)
    (A' Delta' ell : ℕ → ℕ)
    (hA' : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), 1 ≤ A' v)
    (hDelta' : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), Delta' v ≤ A' v)
    (hSblk : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      Sblk v ⊆ Finset.Ioc (A' v) (A' v + Delta' v))
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1) (Sco : Finset ℕ)
    (Pmom : ℕ) (hPmom : 1 ≤ Pmom)
    (hPprev : ∀ p ∈ Pprev, p.Prime)
    (hlo : ∀ p ∈ eadicCell Pprev (2 * Nprev) r, Pmom < p)
    (hhi : ∀ p ∈ eadicCell Pprev (2 * Nprev) r, p ≤ 2 * Pmom)
    (hell : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), 1 ≤ ell v)
    (T : ℝ) (hT : 0 < T)
    (G : Set ℝ) (hGm : MeasurableSet G) (hGT : G ⊆ Set.Ioc (-T) T)
    (alpha beta : ℝ)
    (hsmall : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), ∀ ξ ∈ G,
      ‖levelCellPoly Pcur Ncur v g ξ‖
        ≤ Real.exp (-(alpha * (v : ℝ) / ((2 * Ncur : ℕ) : ℝ))))
    (hlargeCell : ∀ ξ ∈ G,
      Real.exp (-(beta * (r : ℝ) / ((2 * Nprev : ℕ) : ℝ)))
        ≤ ‖levelCellPoly Pprev Nprev r g ξ‖)
    (c₃ eps rho kappa : ℝ)
    (hfit : ((Finset.Ico v₀ (v₁ + 1)).card : ℝ)
        * ∑ v ∈ Finset.Ico v₀ (v₁ + 1),
          (Real.exp (-(alpha * (v : ℝ) / ((2 * Ncur : ℕ) : ℝ)))) ^ 2
            / (Real.exp (-(beta * (r : ℝ) / ((2 * Nprev : ℕ) : ℝ)))) ^
                (2 * ell v)
            * (Real.exp Real.pi
                * (T / ((Pmom ^ ell v * A' v : ℕ) : ℝ)
                  + 2 * ((2 ^ (ell v + 1) : ℕ) : ℝ))
              * ((Nat.factorial (ell v) : ℝ) ^ 2
                * (((2 ^ (ell v + 1) : ℕ) : ℝ) * ((ell v : ℝ) + 1)
                  * (∑ p ∈ eadicCell Pprev (2 * Nprev) r,
                      (1 : ℝ) / (p : ℝ)) ^ ell v)))
      ≤ kappa * bandBudget c₃ eps rho) :
    (∫ ξ in G, ‖∑ v ∈ Finset.Ico v₀ (v₁ + 1),
        levelCellPoly Pcur Ncur v g ξ
          * (∑ m ∈ Sblk v,
              (typicalSQuotCoeff g Pcur Sco m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))‖ ^ 2)
      ≤ kappa * bandBudget c₃ eps rho := by
  let large : ℝ := Real.exp (-(beta * (r : ℝ) / ((2 * Nprev : ℕ) : ℝ)))
  have hlarge0 : 0 < large := by
    dsimp [large]
    positivity
  have hprime : ∀ p ∈ eadicCell Pprev (2 * Nprev) r, p.Prime :=
    fun p hp => hPprev p (mem_eadicCell.mp hp).1
  have hlarge : ∀ ξ ∈ G, large ≤
      ‖∑ p ∈ eadicCell Pprev (2 * Nprev) r, (g p / (p : ℂ))
        * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖ := by
    intro ξ hξ
    change large ≤ ‖levelCellPoly Pprev Nprev r g ξ‖
    exact hlargeCell ξ hξ
  have hraw := setIntegral_norm_sq_level_sum_of_prev_large_le_cells
    (eadicCell Pprev (2 * Nprev) r) hprime Pmom hPmom hlo hhi g hg
    ell A' Delta' (Finset.Ico v₀ (v₁ + 1)) hell hA' hDelta' Sblk hSblk
    (typicalSQuotCoeff g Pcur Sco)
    (norm_typicalSQuotCoeff_le_one g hg Pcur Sco)
    (fun v ξ => levelCellPoly Pcur Ncur v g ξ)
    (fun v _ => ExpSums.continuous_char_poly (eadicCell Pcur (2 * Ncur) v)
      (fun p => g p / (p : ℂ)) (fun p => Real.log p))
    T hT G hGm hGT
    (fun v => Real.exp (-(alpha * (v : ℝ) / ((2 * Ncur : ℕ) : ℝ))))
    large hlarge0 hsmall hlarge
  exact hraw.trans (by simpa [large] using hfit)

end MoltResearch
