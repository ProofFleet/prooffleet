import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5InnerBandAssembly
import MoltResearch.Discrepancy.LaterLevelCells

/-!
# Per-cell later-level inner-band assembly

The natural quotient data are
`A' r v := A / ql j v` and
`Delta' r v := (A + Delta) / ql j v - A / ql j v`.
The natural-number division guard `Delta + ql j v ≤ A` is a convenient
way to obtain `Delta' r v ≤ A' r v`.  The moment choice used by the ladder
numerology is
`ell r v := ⌈log (2 * ql j v * T / A) / log (Pmom r)⌉₊ + 1`,
so that `Pmom r ^ ell r v * A' r v ≥ T` after the corresponding rounding
and nonzero-denominator guards are supplied.
-/

namespace MoltResearch

namespace Tao2015

open MeasureTheory in
/-- On a fixed later level, assemble the current-cell moment estimates on each
least-large-previous-cell part.  Both the quotient interval and the borrowed
moment order retain their current-cell dependence. -/
theorem innerBand_later_level_main_cells
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta : ℕ) (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ)
    (Nl v₀l v₁l : ℕ → ℕ) (ql : ℕ → ℕ → ℕ) (alpha : ℕ → ℝ)
    (J j : ℕ) (hj0 : 0 < j) (hjJ : j < J)
    (hPprev : ∀ p ∈ Pl (j - 1), p.Prime)
    (A' Delta' ell : ℕ → ℕ → ℕ) (Pmom : ℕ → ℕ)
    (hA' : ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1), 1 ≤ A' r v)
    (hDelta' : ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1), Delta' r v ≤ A' r v)
    (hSblk : ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
        Finset.Ioc (A / ql j v) ((A + Delta) / ql j v) ⊆
          Finset.Ioc (A' r v) (A' r v + Delta' r v))
    (hPmom : ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      1 ≤ Pmom r)
    (hlo : ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      ∀ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r, Pmom r < p)
    (hhi : ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      ∀ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r, p ≤ 2 * Pmom r)
    (hell : ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1), 1 ≤ ell r v)
    (K₁ K₂ T : ℝ) (hT : 0 < T) (hTK₂ : K₂ + 2 ≤ T)
    (kappaCell : ℕ → ℝ) (kappaMain c₃ eps : ℝ) (hc₃ : 0 ≤ c₃)
    (hfit : ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      ((Finset.Ico (v₀l j) (v₁l j + 1)).card : ℝ)
        * ∑ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
          (Real.exp (-(alpha j * (v : ℝ) / ((2 * Nl j : ℕ) : ℝ)))) ^ 2
            / (Real.exp (-(alpha (j - 1) * (r : ℝ) /
                ((2 * Nl (j - 1) : ℕ) : ℝ)))) ^ (2 * ell r v)
            * (Real.exp Real.pi
                * (T / ((Pmom r ^ ell r v * A' r v : ℕ) : ℝ)
                  + 2 * ((2 ^ (ell r v + 1) : ℕ) : ℝ))
              * ((Nat.factorial (ell r v) : ℝ) ^ 2
                * (((2 ^ (ell r v + 1) : ℕ) : ℝ) * ((ell r v : ℝ) + 1)
                  * (∑ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r,
                      (1 : ℝ) / (p : ℝ)) ^ ell r v)))
      ≤ kappaCell r * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hshares : ∑ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      kappaCell r ≤ kappaMain) :
    (∫ ξ in bandPartOn (levelSmallSet Pl Nl v₀l v₁l g alpha) J
        {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂} j,
      ‖typicalSCellUniformMain g A (A + Delta) (Pl j)
        (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j)
        (Nl j) (v₀l j) (v₁l j) (ql j) ξ‖ ^ 2)
      ≤ kappaMain * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
  let band := {ξ : ℝ | K₁ ≤ |ξ| ∧ |ξ| ≤ K₂}
  let Pset := levelSmallSet Pl Nl v₀l v₁l g alpha
  let rest := innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j
  let F := typicalSCellUniformMain g A (A + Delta) (Pl j) rest
    (Nl j) (v₀l j) (v₁l j) (ql j)
  have hbandm : MeasurableSet band := measurableSet_inner_band K₁ K₂
  have hpartT : bandPartOn Pset J band j ⊆ Set.Ioc (-T) T :=
    innerBandPartOn_subset_Ioc Pset J j K₁ K₂ T hTK₂
  have hcell : ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      (∫ ξ in firstPrevLargePart Pl Nl v₀l v₁l g alpha J band j r,
          ‖F ξ‖ ^ 2)
        ≤ kappaCell r * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    intro r hr
    let Gr := firstPrevLargePart Pl Nl v₀l v₁l g alpha J band j r
    have hGrm : MeasurableSet Gr :=
      firstPrevLargePart_measurableSet Pl Nl v₀l v₁l g alpha J band hbandm j r
    have hGrT : Gr ⊆ Set.Ioc (-T) T :=
      (firstPrevLargePart_subset_bandPartOn Pl Nl v₀l v₁l g alpha J band j r).trans
        hpartT
    have hsmall : ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1), ∀ ξ ∈ Gr,
        ‖levelCellPoly (Pl j) (Nl j) v g ξ‖
          ≤ Real.exp (-(alpha j * (v : ℝ) / ((2 * Nl j : ℕ) : ℝ))) := by
      intro v hv ξ hξ
      exact levelSmallSet_small_of_mem_bandPartOn Pl Nl v₀l v₁l g alpha J j band ξ
        hjJ (firstPrevLargePart_subset_bandPartOn
          Pl Nl v₀l v₁l g alpha J band j r hξ) v hv
    have hlarge : ∀ ξ ∈ Gr,
        Real.exp (-(alpha (j - 1) * (r : ℝ) /
            ((2 * Nl (j - 1) : ℕ) : ℝ)))
          ≤ ‖levelCellPoly (Pl (j - 1)) (Nl (j - 1)) r g ξ‖ := by
      intro ξ hξ
      exact (firstPrevLargePart_large Pl Nl v₀l v₁l g alpha J band j r hr hξ).le
    have hraw := band_energy_later_main_le_budget_cells
      (Pl j) (Pl (j - 1)) (Nl j) (Nl (j - 1)) r
      (v₀l j) (v₁l j)
      (fun v => Finset.Ioc (A / ql j v) ((A + Delta) / ql j v))
      (A' r) (Delta' r) (ell r) (hA' r hr) (hDelta' r hr) (hSblk r hr)
      g hg (typicalS 0 (A + Delta) rest) (Pmom r) (hPmom r hr)
      hPprev (hlo r hr) (hhi r hr) (hell r hr) T hT Gr hGrm hGrT
      (alpha j) (alpha (j - 1)) hsmall hlarge
      c₃ eps ((Delta : ℝ) / (A : ℝ)) (kappaCell r) (hfit r hr)
    simpa [F, typicalSCellUniformMain, rest] using hraw
  exact setIntegral_norm_sq_later_le_budget_of_firstPrev Pl Nl v₀l v₁l g alpha
    J band hbandm j hj0 hjJ F
    (continuous_typicalSCellUniformMain g A (A + Delta) (Pl j) rest
      (Nl j) (v₀l j) (v₁l j) (ql j))
    T hpartT kappaCell kappaMain c₃ eps ((Delta : ℝ) / (A : ℝ)) hc₃
    (by positivity) hcell hshares

end Tao2015

end MoltResearch
