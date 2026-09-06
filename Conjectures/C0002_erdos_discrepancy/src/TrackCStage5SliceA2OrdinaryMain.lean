import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2Resolution
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5InnerBandAssemblyCells

/-!
# Track R A2-V'-11: later ordinary main terms

This leaf connects the scale-free L3-1 envelope to the literal summand of
`innerBand_later_level_main_cells`.  The moment is borrowed from the previous
cell, while the quotient interval keeps its exact natural-number endpoints.
-/

namespace MoltResearch

namespace Tao2015

open Finset MeasureTheory ExpSums

/-- The moment used for current cell `v`, borrowing the anchor of previous
cell `r`. -/
noncomputable def sliceA2LaterMoment
    (Pmom t : ℕ → ℕ) (tau : ℝ) (r v : ℕ) : ℕ :=
  ordinaryBorrowMoment (Pmom r) ((t v : ℝ) * tau)

noncomputable def sliceA2LaterTimeTerm
    (A q : ℕ → ℕ) (Pmom t : ℕ → ℕ) (T tau : ℝ)
    (r v : ℕ) : ℝ :=
  T / (((Pmom r) ^ sliceA2LaterMoment Pmom t tau r v * A (q v) : ℕ) : ℝ)

/-- The L3-1 envelope, with a relative budget floor, supplies a complete
later-level main term. -/
theorem innerBand_later_level_main_of_envelope_ratio
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta : ℕ) (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ)
    (Nl v0l v1l : ℕ → ℕ) (ql : ℕ → ℕ → ℕ)
    (J j : ℕ) (hj0 : 0 < j) (hjJ : j < J)
    (hPprev : ∀ p ∈ Pl (j - 1), p.Prime)
    (Pmom : ℕ → ℕ) (t : ℕ → ℕ) (Pcur : ℕ)
    (Qprev tau L T c3 eps rho0 : ℝ)
    (hNcur : 0 < Nl j) (hNprev : 0 < Nl (j - 1))
    (hPmom : ∀ r ∈ Finset.Ico (v0l (j - 1)) (v1l (j - 1) + 1),
      2 ≤ Pmom r)
    (hlo : ∀ r ∈ Finset.Ico (v0l (j - 1)) (v1l (j - 1) + 1),
      ∀ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r, Pmom r < p)
    (hhi : ∀ r ∈ Finset.Ico (v0l (j - 1)) (v1l (j - 1) + 1),
      ∀ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r, p ≤ 2 * Pmom r)
    (hPcur : 1 ≤ Pcur)
    (hPt : ∀ v ∈ Finset.Ico (v0l j) (v1l j + 1), Pcur ≤ t v)
    (hPmomQ : ∀ r ∈ Finset.Ico (v0l (j - 1)) (v1l (j - 1) + 1),
      (Pmom r : ℝ) ≤ Qprev)
    (htop : ∀ v ∈ Finset.Ico (v0l j) (v1l j + 1),
      (t v : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (Nl j : ℝ))))
    (hexpPrev : ∀ r ∈ Finset.Ico (v0l (j - 1)) (v1l (j - 1) + 1),
      Real.exp ((r : ℝ) / (2 * (Nl (j - 1) : ℝ))) ≤ 2 * (Pmom r : ℝ))
    (htauEq : tau = 2 * T / A) (htau0 : 0 ≤ tau) (htau : tau ≤ 1)
    (hx : ∀ v ∈ Finset.Ico (v0l j) (v1l j + 1),
      1 ≤ (t v : ℝ) * tau)
    (hq1 : ∀ v, 1 ≤ ql j v)
    (hqt : ∀ v ∈ Finset.Ico (v0l j) (v1l j + 1), ql j v ≤ t v)
    (hqguard : ∀ v ∈ Finset.Ico (v0l j) (v1l j + 1),
      Delta + ql j v ≤ A)
    (h2qA : ∀ v ∈ Finset.Ico (v0l j) (v1l j + 1), 2 * ql j v ≤ A)
    (hT : 0 < T)
    (hmass : ∑ p ∈ Pl (j - 1), (1 : ℝ) / p ≤ 1)
    (hL : 1 ≤ L)
    (hellL : ∀ r ∈ Finset.Ico (v0l (j - 1)) (v1l (j - 1) + 1),
      ∀ v ∈ Finset.Ico (v0l j) (v1l j + 1),
        (sliceA2LaterMoment Pmom t tau r v : ℝ) ≤ L)
    (hfar : ∀ r ∈ Finset.Ico (v0l (j - 1)) (v1l (j - 1) + 1),
      (2 * Real.log L + 3) / Real.log (Pmom r) ≤
        innerBandScheduleAlpha j - innerBandScheduleAlpha (j - 1))
    (hc3 : 0 ≤ c3) (hratio : rho0 ≤ (Delta : ℝ) / A)
    (hprevCells : (Finset.Ico (v0l (j - 1)) (v1l (j - 1) + 1)).Nonempty)
    (hnumerology : ∀ r ∈ Finset.Ico (v0l (j - 1)) (v1l (j - 1) + 1),
      ((Finset.Ico (v0l j) (v1l j + 1)).card : ℝ) ^ 2 *
          ordinaryLadderCellEnvelope (Nl j) Pcur Qprev tau
            (innerBandScheduleAlpha j) (innerBandScheduleAlpha (j - 1)) L ≤
        ordinaryUniformCellShare j
            (Finset.Ico (v0l (j - 1)) (v1l (j - 1) + 1)) *
          (c3 * eps ^ 2 * rho0 / 8))
    (K1 K2 : ℝ) (hTK2' : K2 + 2 ≤ T) :
    (∫ xi in bandPartOn
        (levelSmallSet Pl Nl v0l v1l g innerBandScheduleAlpha) J
        {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} j,
      ‖typicalSCellUniformMain g A (A + Delta) (Pl j)
        (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j)
        (Nl j) (v0l j) (v1l j) (ql j) xi‖ ^ 2) ≤
      ordinaryLegShare j * bandBudget c3 eps ((Delta : ℝ) / A) := by
  let Icur := Finset.Ico (v0l j) (v1l j + 1)
  let Iprev := Finset.Ico (v0l (j - 1)) (v1l (j - 1) + 1)
  let A' : ℕ → ℕ → ℕ := fun _r v => ordinaryQuotientA A (ql j v)
  let Delta' : ℕ → ℕ → ℕ :=
    fun _r v => ordinaryQuotientDelta A Delta (ql j v)
  let ell : ℕ → ℕ → ℕ := fun r v => sliceA2LaterMoment Pmom t tau r v
  have hquot : ∀ v ∈ Icur,
      1 ≤ ordinaryQuotientA A (ql j v) ∧
      ordinaryQuotientDelta A Delta (ql j v) ≤ ordinaryQuotientA A (ql j v) ∧
      Finset.Ioc (A / ql j v) ((A + Delta) / ql j v) ⊆
        Finset.Ioc (ordinaryQuotientA A (ql j v))
          (ordinaryQuotientA A (ql j v) +
            ordinaryQuotientDelta A Delta (ql j v)) := by
    intro v hv
    have hq := hq1 v
    exact ordinaryQuotient_data A Delta (ql j v) (by omega) (hqguard v hv)
  have halpha := innerBandScheduleAlpha_bounds j
  have hbeta := innerBandScheduleAlpha_bounds (j - 1)
  have hgap0 : 0 ≤ innerBandScheduleAlpha j -
      innerBandScheduleAlpha (j - 1) := by
    rw [innerBandScheduleAlpha_gap j hj0]
    positivity
  have hu0 : ∀ r ∈ Iprev, ∀ v ∈ Icur,
      0 ≤ sliceA2LaterTimeTerm (fun q => A / q) (ql j) Pmom t T tau r v := by
    intro r hr v hv
    unfold sliceA2LaterTimeTerm
    positivity
  have hu : ∀ r ∈ Iprev, ∀ v ∈ Icur,
      sliceA2LaterTimeTerm (fun q => A / q) (ql j) Pmom t T tau r v ≤ 1 := by
    intro r hr v hv
    simpa [sliceA2LaterTimeTerm, sliceA2LaterMoment, htauEq] using
      ordinaryBorrowMoment_time_term_le_one (Pmom r) A (ql j v) (t v) T
        (hPmom r hr) (hq1 v) (hqt v hv) (h2qA v hv) hT
  have hfit : ∀ r ∈ Iprev,
      (Icur.card : ℝ) * ∑ v ∈ Icur,
        ordinaryLadderCellRaw (Nl j) (Nl (j - 1)) v r (Pmom r)
          (innerBandScheduleAlpha j) (innerBandScheduleAlpha (j - 1))
          (∑ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r,
            (1 : ℝ) / p)
          (sliceA2LaterTimeTerm (fun q => A / q) (ql j) Pmom t T tau r v)
          ((t v : ℝ) * tau) ≤
        ordinaryUniformCellShare j Iprev *
          bandBudget c3 eps ((Delta : ℝ) / A) := by
    intro r hr
    have hmass0 : 0 ≤
        ∑ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r,
          (1 : ℝ) / p := by positivity
    have hmassCell :
        ∑ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r,
            (1 : ℝ) / p ≤ 1 := by
      apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg
        (s := eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r)
        (t := Pl (j - 1)) (fun p hp => (mem_eadicCell.mp hp).1)
        (fun p _ _ => by positivity)) hmass
    apply ordinaryLadder_per_previous_cell_fit_of_ratio Icur Iprev j
      (Nl j) (Nl (j - 1)) r (Pmom r) Pcur t
      (fun v => sliceA2LaterTimeTerm (fun q => A / q) (ql j) Pmom t T tau r v)
      Qprev tau (innerBandScheduleAlpha j) (innerBandScheduleAlpha (j - 1))
      (∑ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r,
        (1 : ℝ) / p) L c3 eps rho0
      ((Delta : ℝ) / A) hNcur hNprev (hPmom r hr) hPcur hPt
      (hPmomQ r hr) htop (hexpPrev r hr) htau0 htau hx halpha.1.le
      hbeta.1.le hbeta.2.le hgap0 hmass0 hmassCell (hu0 r hr) (hu r hr) hL
      (hellL r hr) (hfar r hr) hc3 hratio
    simpa [ordinaryUniformCellShare, Icur, Iprev] using hnumerology r hr
  apply innerBand_later_level_main_cells
    (kappaCell := fun _r => ordinaryUniformCellShare j Iprev)
    g hg A Delta Pl Pu Nl v0l v1l ql innerBandScheduleAlpha J j hj0 hjJ
    hPprev A' Delta' ell Pmom
  · intro r hr v hv
    exact (hquot v (by simpa [Icur] using hv)).1
  · intro r hr v hv
    exact (hquot v (by simpa [Icur] using hv)).2.1
  · intro r hr v hv
    exact (hquot v (by simpa [Icur] using hv)).2.2
  · intro r hr
    exact (hPmom r (by simpa [Iprev] using hr)).trans' (by norm_num)
  · exact hlo
  · exact hhi
  · intro r hr v hv
    unfold ell sliceA2LaterMoment
    exact ordinaryBorrowMoment_one_le _ _
  · exact hT
  · exact hTK2'
  · exact hc3
  · intro r hr
    have hr' : r ∈ Iprev := by simpa [Iprev] using hr
    have hraw := hfit r hr'
    simpa only [Icur, Iprev, A', Delta', ell, ordinaryLadderCellRaw_eq,
      ordinaryQuotientA, sliceA2LaterMoment, sliceA2LaterTimeTerm] using hraw
  · have hsum := sum_ordinaryUniformCellShare j Iprev hprevCells
    simpa [Iprev] using hsum.le

end Tao2015

end MoltResearch
