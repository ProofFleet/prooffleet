import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2LowRemainder
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinarySchedule

/-!
# Track R A2-V': aggregate interface to the shifted inner capstone

This leaf combines the ordinary schedule and the corrected actual-cost
exceptional schedule.  In particular, the exceptional cells and both wide
legs are charged to the fixed half-band share, independently of the ladder
height.
-/

namespace MoltResearch

namespace Tao2015

open Real Finset MeasureTheory ExpSums

set_option maxHeartbeats 1000000 in
/-- Ordinary level bounds and the three exceptional aggregate fits imply the
exact shifted-capstone inner-band estimate. -/
theorem sliceA2_inner_band_of_aggregate_fits
    [HalaszLargeValuesAssumption] [PrimeLargeValuesAssumption]
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta H : ℕ) (hA : 0 < A) (hH : 0 < H) (hDeltaA : Delta ≤ A)
    (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ) (J : ℕ) (hJ : 0 < J)
    (hPl : ∀ i < J, ∀ p ∈ Pl i, p.Prime)
    (hPu : ∀ p ∈ Pu, p.Prime)
    (hPAu : ∀ p ∈ Pu, p * p ≤ A)
    (hdisj : ∀ i < J, ∀ k < J, i ≠ k → Disjoint (Pl i) (Pl k))
    (hdisjU : ∀ i < J, Disjoint (Pl i) Pu)
    (Nl v0l v1l : ℕ → ℕ) (ql : ℕ → ℕ → ℕ)
    (hNl : ∀ j < J, 0 < Nl j)
    (hcovl : ∀ j < J, (Finset.Ico (v0l j) (v1l j + 1)).biUnion
      (eadicCell (Pl j) (2 * Nl j)) = Pl j)
    (hqupl : ∀ j < J, ∀ v ∈ Finset.Ico (v0l j) (v1l j + 1),
      (ql j v : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (Nl j : ℝ))))
    (hq1l : ∀ j < J, ∀ v, 1 ≤ ql j v)
    (hqminl : ∀ j < J, ∀ v ∈ Finset.Ico (v0l j) (v1l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v, ql j v ≤ p)
    (hqratiol : ∀ j < J, ∀ v ∈ Finset.Ico (v0l j) (v1l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
        Nl j * p ≤ (Nl j + 1) * ql j v)
    (K1 K2 T eps : ℝ) (hT1 : 1 ≤ T) (hTK2 : K2 + 2 ≤ T)
    (heps : 0 < eps)
    (hzero :
      (∫ xi in bandPartOn
          (levelSmallSet Pl Nl v0l v1l g innerBandScheduleAlpha) J
          {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} 0,
        ‖typicalSCellUniformMain g A (A + Delta) (Pl 0)
          (innerBandLevelsBefore Pl J 0 ++ innerBandLevelsAfter Pl Pu J 0)
          (Nl 0) (v0l 0) (v1l 0) (ql 0) xi‖ ^ 2) ≤
        sliceA2KappaMain 0 *
          bandBudget 1 eps ((Delta : ℝ) / (A : ℝ)))
    (hlater : ∀ j, 0 < j → j < J →
      (∫ xi in bandPartOn
          (levelSmallSet Pl Nl v0l v1l g innerBandScheduleAlpha) J
          {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} j,
        ‖typicalSCellUniformMain g A (A + Delta) (Pl j)
          (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j)
          (Nl j) (v0l j) (v1l j) (ql j) xi‖ ^ 2) ≤
        sliceA2KappaMain j *
          bandBudget 1 eps ((Delta : ℝ) / (A : ℝ)))
    (hreplacement : ∀ j < J,
      2 * replacementEnergyBoundWide A (Pl j) (Nl j) T ≤
        sliceA2KappaReplacement j *
          bandBudget 1 eps ((Delta : ℝ) / (A : ℝ)))
    (hcollision : ∀ j < J,
      8 * collisionEnergyBoundWide A (Pl j) T ≤
        sliceA2KappaCollision j *
          bandBudget 1 eps ((Delta : ℝ) / (A : ℝ)))
    (Nu v0u v1u : ℕ) (hNu : 0 < Nu)
    (hcovU : (Finset.Ico v0u (v1u + 1)).biUnion
      (eadicCell Pu (2 * Nu)) = Pu)
    (qu : ℕ → ℕ)
    (hqupU : ∀ v ∈ Finset.Ico v0u (v1u + 1),
      (qu v : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (Nu : ℝ))))
    (hq1U : ∀ v, 1 ≤ qu v)
    (hqminU : ∀ v ∈ Finset.Ico v0u (v1u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v, qu v ≤ p)
    (hqratioU : ∀ v ∈ Finset.Ico v0u (v1u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v,
        Nu * p ≤ (Nu + 1) * qu v)
    (hLAU : ∀ v ∈ Finset.Ico v0u (v1u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v, A / (Nu * p) + 1 ≤ A / p)
    (hLBU : ∀ v ∈ Finset.Ico v0u (v1u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v,
        (A + Delta) / (Nu * p) + 1 ≤ (A + Delta) / p)
    (w : ℝ → ℝ) (hwm : Measurable w) (hw0 : ∀ xi, 0 ≤ w xi)
    (hwsup : ∀ xi, w xi ≤ (4 * (H : ℝ) / (A : ℝ)) ^ 2)
    (PcU : ℕ → ℕ) (hPcU : ∀ v ∈ Finset.Ico v0u (v1u + 1), 2 ≤ PcU v)
    (hloU : ∀ v ∈ Finset.Ico v0u (v1u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v, PcU v < p)
    (hhiU : ∀ v ∈ Finset.Ico v0u (v1u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v, p ≤ 2 * PcU v)
    (ellU : ℕ → ℕ) (hellU : ∀ v ∈ Finset.Ico v0u (v1u + 1), 1 ≤ ellU v)
    (V0 : ℝ) (hV0 : 0 < V0)
    (x0 : ℕ) (hx0 : cellHalaszThreshold ≤ x0)
    (D delta0 A0 : ℝ) (hD : 1 ≤ D)
    (hdelta0 : 0 < delta0) (hdelta1 : delta0 ≤ 1) (hA0 : 3 ≤ A0)
    (hNPtop : NonPretentiousAt g A0 (2 * A + 1))
    (hrangeSharp :
      2 * Real.pi * T
          + 2 * Real.pi * (((halaszM (3 * (2 * A + 1)) : ℕ) : ℝ) + 1)
        ≤ (A0 / 3) * ((3 * (2 * A + 1) : ℕ) : ℝ))
    (hstrengthSharp :
      2 * D ≤ A0 / 3 - 2 *
        (Real.log (Real.log ((3 * (2 * A + 1) : ℕ) : ℝ)) -
          Real.log (Real.log (x0 : ℝ)) + 12))
    (DeltaU : ℕ → ℝ)
    (hDeltaU0 : ∀ v ∈ Finset.Ico v0u (v1u + 1), 0 ≤ DeltaU v)
    (hDeltaU : ∀ v ∈ Finset.Ico v0u (v1u + 1),
      cellHalaszSharpBound x0 D delta0 (A / qu v) ((A + Delta) / qu v)
          Pu [Pl 0]
        + ladderSiftedLogMass (A / qu v) ((A + Delta) / qu v)
            ((List.range (J - 1)).map (fun i => Pl (i + 1))) ≤ DeltaU v)
    (Bq coeffMass Gamma : ℕ → ℝ) (Kcov L rho0 : ℝ)
    (hBq : ∀ v ∈ Finset.Ico v0u (v1u + 1),
      Bq v = (((A + Delta) / qu v : ℕ) : ℝ))
    (hcoeff : ∀ v ∈ Finset.Ico v0u (v1u + 1),
      coeffMass v = ∑ n ∈ Finset.Icc 1 ((A + Delta) / qu v),
        ‖cellBlockCoeff g A (A + Delta) Pu ((List.range J).map Pl)
          (qu v) n‖ ^ 2 / (n : ℝ) ^ 2)
    (hKcov : Kcov =
      ((cellsMeetingSet (bandCells K2)
        (bandPartOn (levelSmallSet Pl Nl v0l v1l g innerBandScheduleAlpha) J
          {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} J)).card : ℝ))
    (hL : L = Real.log (2 * T) + 1)
    (hGamma : ∀ v ∈ Finset.Ico v0u (v1u + 1),
      Gamma v = primeHighMomentCountCost (PcU v) (ellU v)
          (eadicCell Pu (2 * Nu) v) T V0 1 *
        Real.exp (-(Real.log (PcU v) / (Real.log (2 * T)) ^ (3 / 4 : ℝ))) *
        (Real.log (2 * T)) ^ 2)
    (hrho0 : 0 < rho0) (hratio : rho0 ≤ (Delta : ℝ) / A)
    (hint : 2 * ((Finset.Ico v0u (v1u + 1)).card : ℝ) *
        (∑ v ∈ Finset.Ico v0u (v1u + 1),
          exceptionalIntegerCellCost V0 (Bq v) Kcov T L (coeffMass v)) ≤
      eps ^ 2 * rho0 / 64)
    (hprime : 2 * ((Finset.Ico v0u (v1u + 1)).card : ℝ) *
        (∑ v ∈ Finset.Ico v0u (v1u + 1),
          exceptionalPrimeCellCost (fun v => eadicCell Pu (2 * Nu) v)
            PcU g DeltaU Gamma v) ≤ eps ^ 2 * rho0 / 64)
    (hwide : 2 * (2 * replacementEnergyBoundWide A Pu Nu T +
        2 * (4 * collisionEnergyBoundWide A Pu T)) ≤ eps ^ 2 * rho0 / 32) :
    (∫ xi in {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2},
        ‖∑ m ∈ typicalS A (A + Delta) (innerBandLevels Pl Pu J),
            (g m / (m : ℂ)) *
              ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2 *
          w xi) ≤
      (4 * (H : ℝ) / (A : ℝ)) ^ 2 *
        bandBudget 1 eps ((Delta : ℝ) / (A : ℝ)) := by
  let I := Finset.Ico v0u (v1u + 1)
  let wide := 2 * (2 * replacementEnergyBoundWide A Pu Nu T +
    2 * (4 * collisionEnergyBoundWide A Pu T))
  let cost := fun v =>
    exceptionalIntegerCellCost V0 (Bq v) Kcov T L (coeffMass v) +
      exceptionalPrimeCellCost (fun u => eadicCell Pu (2 * Nu) u)
        PcU g DeltaU Gamma v
  let kappaU := fun v =>
    exceptionalCellKappa (cost v)
      (bandBudget 1 eps ((Delta : ℝ) / (A : ℝ)))
  obtain ⟨hmain, hrepl, hcoll, hshare⟩ := sliceA2_ordinary_schedule
    g A Delta Pl Pu J Nl v0l v1l ql K1 K2 T 1 eps
    hzero hlater hreplacement hcollision
  obtain ⟨hcell, haggregate⟩ := exceptional_exact_cell_schedule_of_ratio_fits
    I Bq coeffMass (fun v => eadicCell Pu (2 * Nu) v) PcU g DeltaU Gamma
    V0 Kcov T L wide 1 eps rho0 ((Delta : ℝ) / A)
    (by norm_num) heps hrho0 hratio
    (by simpa [I] using hint) (by simpa [I] using hprime)
    (by simpa [wide] using hwide)
  apply band_energy_typicalS_le_of_schedule_sharp_cells_wide'
    g hcm hg A Delta H hA hH hDeltaA Pl Pu J hJ hPl hPu hPAu hdisj hdisjU
    Nl v0l v1l ql innerBandScheduleAlpha hNl hcovl hqupl hq1l hqminl
    hqratiol K1 K2 T hT1 hTK2 1 eps (by norm_num)
    sliceA2KappaMain sliceA2KappaReplacement sliceA2KappaCollision
    hmain hrepl hcoll hshare Nu v0u v1u hNu hcovU qu hqupU hq1U hqminU
    hqratioU hLAU hLBU w hwm hw0 hwsup PcU hPcU hloU hhiU ellU hellU
    (fun _ => V0) (fun _ => 1) (fun _ _ => hV0) (fun _ _ => by norm_num)
    x0 hx0 D delta0 A0 hD hdelta0 hdelta1 hA0 hNPtop hrangeSharp
    hstrengthSharp DeltaU hDeltaU0 hDeltaU kappaU
  · intro v hv
    have hc := hcell v (by simpa [I] using hv)
    simpa only [kappaU, cost, hBq v hv, hcoeff v hv, hKcov, hL,
      hGamma v hv, one_pow, mul_one] using hc
  · simpa only [I, kappaU, cost, wide] using haggregate

end Tao2015

end MoltResearch
