import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5InnerBandAssembly
import MoltResearch.Discrepancy.BandScheduleShares
import MoltResearch.Discrepancy.LevelOneSchedule
import MoltResearch.Discrepancy.LaterLevelSchedule
import MoltResearch.Discrepancy.ReplacementSchedule
import MoltResearch.Discrepancy.CollisionSchedule
import MoltResearch.Discrepancy.CellHalaszQuotientSchedule

/-!
# The `[mrt]` A.2 inner band at the S1--S7 schedule

This file replaces the fit hypotheses of
`band_energy_typicalS_le_of_levels` by explicit inequalities in the schedule
parameters.  The level list, e-adic covers, representatives, moment blocks,
window, and the two analytic interfaces remain unchanged.

The ordinary levels in the assembly are zero-indexed, whereas `S5` numbers
the first level by one.  Thus the schedule decay used here is
`scheduleAlpha (1/20) (j+1)`.
-/

namespace MoltResearch

namespace Tao2015

/-- `S5`'s decay exponent in the assembly's zero-based indexing. -/
noncomputable def innerBandScheduleAlpha (j : ℕ) : ℝ :=
  scheduleAlpha (1 / 20) (j + 1)

/-- The Mertens envelope used for the harmonic mass of a prime level. -/
noncomputable def levelPrimeMassBound (b : ℕ) : ℝ :=
  Real.log (Real.log ((b : ℝ) + 1)) + 11

/-- The fully explicit pointwise Halász envelope for exceptional cell `v`. -/
noncomputable def exceptionalDeltaSchedule
    (D delta₀ T : ℝ) (A Delta : ℕ)
    (rest : List (Finset ℕ)) (qu : ℕ → ℕ) (y : ℕ) (v : ℕ) : ℝ :=
  ((2 ^ rest.length : ℕ) : ℝ) * (Real.exp 12 * Real.log y)
    * cellHalaszScheduleQuotientBound D delta₀ T ((A + Delta) / qu v)

/-- The schedule upper bound for the integer large-values group of one
exceptional cell. -/
noncomputable def exceptionalIntegerSchedule (A Delta : ℕ)
    (qu : ℕ → ℕ) (T : ℝ) (v : ℕ) : ℝ :=
  128 * ((((A + Delta) / qu v : ℕ) : ℝ) + 2 * T * Real.sqrt T)
    * (Real.log (2 * T) + 1)

/-- The schedule upper bound for the prime large-values group of one
exceptional cell. -/
noncomputable def exceptionalPrimeSchedule (Cp : ℝ) (PcU : ℕ → ℕ) (v : ℕ) : ℝ :=
  Cp * (256 / (Real.log (PcU v)) ^ 2)

/-- The schedule upper bound for the Ramaré ratio group of one exceptional
cell. -/
noncomputable def exceptionalRatioSchedule (PcU : ℕ → ℕ)
    (T : ℝ) (v : ℕ) : ℝ :=
  Real.exp Real.pi * ((T + 1) / (PcU v : ℝ) + 4)
    * (256 / Real.log (PcU v) + 2048 * Real.pi)
    * Real.exp (-(Real.log (PcU v) /
      (Real.log (2 * T)) ^ primeLargeValuesExponent))
    * (Real.log (2 * T)) ^ 2

/-- A covered e-adic level inherits the common prime interval of its cells. -/
theorem level_subset_primeInterval
    (P : Finset ℕ) (N v₀ v₁ Pb bb : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (hlevel : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      eadicCell P (2 * N) v ⊆ (Finset.Ioc Pb bb).filter Nat.Prime) :
    P ⊆ (Finset.Ioc Pb bb).filter Nat.Prime := by
  intro p hp
  have hp' : p ∈ (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) := by
    rwa [hcov]
  obtain ⟨v, hv, hpv⟩ := Finset.mem_biUnion.mp hp'
  exact hlevel v hv hpv

/-- The harmonic mass of a covered level is bounded by its Mertens envelope. -/
theorem level_primeMass_le
    (P : Finset ℕ) (N v₀ v₁ Pb bb : ℕ)
    (hbb : 3 ≤ bb)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (hlevel : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      eadicCell P (2 * N) v ⊆ (Finset.Ioc Pb bb).filter Nat.Prime) :
    ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ≤ levelPrimeMassBound bb := by
  have hsub := level_subset_primeInterval P N v₀ v₁ Pb bb hcov hlevel
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => by positivity)).trans ?_
  exact sum_one_div_prime_Ioc_le_mertens Pb bb hbb

/-- The three ordinary sublegs use strictly less than one dyadic share before
the Fourier-weight supremum is applied. -/
theorem ordinaryLegShares_fit_honest (j : ℕ) :
    2 * ordinaryLegShare j + 2 * ordinaryLegShare j + 2 * ordinaryLegShare j
      ≤ (1 : ℝ) / 2 ^ (j + 1) := by
  unfold ordinaryLegShare
  have hp : 0 ≤ ((2 : ℝ) ^ (j + 1))⁻¹ := inv_nonneg.mpr (by positivity)
  calc
    2 * (3 / (64 * 2 ^ (j + 1))) + 2 * (3 / (64 * 2 ^ (j + 1)))
        + 2 * (3 / (64 * 2 ^ (j + 1)))
        = (18 / 64) * ((2 : ℝ) ^ (j + 1))⁻¹ := by ring
    _ ≤ 1 * ((2 : ℝ) ^ (j + 1))⁻¹ :=
      mul_le_mul_of_nonneg_right (by norm_num) hp
    _ = 1 / 2 ^ (j + 1) := by ring

open MeasureTheory in
/-- **A2-III VI-8 -- the inner band under explicit schedule inequalities.**

Every hypothesis whose name contains `schedule` is an inequality only in the
named schedule parameters.  In particular there is no occurrence of
`collisionEnergyBound`, `cellReplacementEnergyBound`, a cell prime sum, or a
finite Halász maximum in those hypotheses. -/
theorem band_energy_typicalS_le_of_schedule [HalaszLargeValuesAssumption]
    (Cp : ℝ) (hCp1 : 1 ≤ Cp) (hprime : PrimeLargeValuesBound Cp)
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta H : ℕ) (hA : 0 < A) (hH : 0 < H) (hDeltaA : Delta ≤ A)
    (h3HA : 3 * H ≤ A)
    (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ) (J : ℕ)
    (hPl : ∀ i < J, ∀ p ∈ Pl i, p.Prime)
    (hPu : ∀ p ∈ Pu, p.Prime)
    (hPAl : ∀ i < J, ∀ p ∈ Pl i, p * p ≤ A)
    (hPAu : ∀ p ∈ Pu, p * p ≤ A)
    (hdisj : ∀ i < J, ∀ k < J, i ≠ k → Disjoint (Pl i) (Pl k))
    (hdisjU : ∀ i < J, Disjoint (Pl i) Pu)
    (Nl v₀l v₁l : ℕ → ℕ) (ql : ℕ → ℕ → ℕ)
    (hNl : ∀ j < J, 0 < Nl j)
    (hcovl : ∀ j < J, (Finset.Ico (v₀l j) (v₁l j + 1)).biUnion
      (eadicCell (Pl j) (2 * Nl j)) = Pl j)
    (hqcelll : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ql j v ∈ eadicCell (Pl j) (2 * Nl j) v)
    (hq1l : ∀ j < J, ∀ v, 1 ≤ ql j v)
    (hqAl : ∀ j < J, ∀ v, 2 * ql j v ≤ A)
    (hqminl : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v, ql j v ≤ p)
    (hLAl : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
        A / (Nl j * p) + 1 ≤ A / p)
    (hLBl : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
        (A + Delta) / (Nl j * p) + 1 ≤ (A + Delta) / p)
    (Plo Qhi : ℕ → ℝ)
    (hPlo0 : ∀ j < J, 0 < Plo j) (hQhi0 : ∀ j < J, 0 < Qhi j)
    (hPloQhi : ∀ j < J, Plo j ≤ Qhi j)
    (htop : ∀ j < J,
      (v₁l j : ℝ) ≤ 2 * (Nl j : ℝ) * Real.log (Qhi j))
    (hbot : ∀ j < J,
      2 * (Nl j : ℝ) * Real.log (Plo j) - 1 ≤ (v₀l j : ℝ))
    (R : ℕ) (hR : 1 ≤ R) (hB : A + Delta ≤ R * A)
    (K₁ K₂ T : ℝ) (hT1 : 1 ≤ T) (hTK₂ : K₂ + 2 ≤ T)
    (c₃ eps : ℝ) (hc₃ : 0 ≤ c₃)
    (hscheduleT0 : 0 < J →
      (2 * (Nl 0 : ℝ) * (Real.log (Qhi 0) - Real.log (Plo 0)) + 2)
        * (Real.exp Real.pi * Real.log (2 * (R : ℝ))
          * ((2 * T * Real.exp (1 / ((2 * Nl 0 : ℕ) : ℝ)) / (A : ℝ))
            * ((Qhi 0) ^ (1 - 2 * innerBandScheduleAlpha 0)
              * Real.exp ((1 - 2 * innerBandScheduleAlpha 0) /
                ((2 * Nl 0 : ℕ) : ℝ)))
            * (((2 * Nl 0 : ℕ) : ℝ) / (1 - 2 * innerBandScheduleAlpha 0) + 1)))
      ≤ ordinaryLegShare 0 / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hscheduleP0 : 0 < J →
      (2 * (Nl 0 : ℝ) * (Real.log (Qhi 0) - Real.log (Plo 0)) + 2)
        * (Real.exp Real.pi * Real.log (2 * (R : ℝ))
          * (4 * (R : ℝ)
            * ((Plo 0) ^ (-(2 * innerBandScheduleAlpha 0))
              * Real.exp (2 * innerBandScheduleAlpha 0 /
                ((2 * Nl 0 : ℕ) : ℝ)))
            * (((2 * Nl 0 : ℕ) : ℝ) / (2 * innerBandScheduleAlpha 0) + 1)))
      ≤ ordinaryLegShare 0 / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (A' Delta' Pmom ell : ℕ → ℕ → ℕ)
    (hA' : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1), 1 ≤ A' j r)
    (hDelta' : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
        Delta' j r ≤ A' j r)
    (hSblk : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
        Finset.Ioc (A / ql j v) ((A + Delta) / ql j v) ⊆
          Finset.Ioc (A' j r) (A' j r + Delta' j r))
    (hPmom : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1), 1 ≤ Pmom j r)
    (hPmom2 : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1), 2 ≤ Pmom j r)
    (hlomom : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      ∀ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r, Pmom j r < p)
    (hhimom : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      ∀ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r, p ≤ 2 * Pmom j r)
    (hell : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1), 1 ≤ ell j r)
    (hscheduleLater : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      (2 * (Nl j : ℝ) * (Real.log (Qhi j) - Real.log (Plo j)) + 2)
        * (((Plo j) ^ (-(2 * innerBandScheduleAlpha j))
              * Real.exp (2 * innerBandScheduleAlpha j / ((2 * Nl j : ℕ) : ℝ))
              * (((2 * Nl j : ℕ) : ℝ) / (2 * innerBandScheduleAlpha j) + 1))
          * ((Real.exp Real.pi
                * (T / (((Pmom j r) ^ (ell j r) * A' j r : ℕ) : ℝ)
                  + 2 * ((2 ^ (ell j r + 1) : ℕ) : ℝ)))
            * laterMomentScheduleBound (ell j r) (Pmom j r)
                ((Qhi (j - 1)) ^ (-(innerBandScheduleAlpha (j - 1)))
                  * Real.exp (-(innerBandScheduleAlpha (j - 1) /
                    ((2 * Nl (j - 1) : ℕ) : ℝ))))))
      ≤ geometricCellShare (ordinaryLegShare j) r
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (Pb Kc bb : ℕ → ℕ) (aa : ℕ → ℕ → ℕ)
    (hPb : ∀ j < J, 1 ≤ Pb j) (hKc : ∀ j < J, 2 ≤ Kc j)
    (hbb : ∀ j < J, 3 ≤ bb j)
    (haa : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1), Pb j ≤ aa j v)
    (hcell : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      eadicCell (Pl j) (2 * Nl j) v ⊆
        (Finset.Ioc (aa j v) (aa j v + Kc j)).filter Nat.Prime)
    (hlevel : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      eadicCell (Pl j) (2 * Nl j) v ⊆
        (Finset.Ioc (Pb j) (bb j)).filter Nat.Prime)
    (hNbb : ∀ j < J, Nl j * bb j ≤ A)
    (hrho : eps ≤ (Delta : ℝ) / (A : ℝ))
    (hscheduleReplacement : ∀ j < J,
      64 * ((Finset.Ico (v₀l j) (v₁l j + 1)).card : ℝ)
          * replacementCost A (Nl j) (bb j) T
          * ((256 * (Kc j : ℝ) / ((Pb j : ℝ) * Real.log (Kc j)))
            * levelPrimeMassBound (bb j))
        ≤ ordinaryLegShare j * c₃ * eps ^ 3)
    (hscheduleCollision : ∀ j < J,
      8 * (levelPrimeMassBound (bb j)
        * ((levelPrimeMassBound (bb j) / (Pb j : ℝ) ^ 2)
          * (Real.exp Real.pi * (2 * T * (bb j : ℝ) ^ 2 / (A : ℝ) + 8)
            * Real.log (2 * (R : ℝ)))))
        ≤ ordinaryLegShare j * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (Nu v₀u v₁u : ℕ) (hNu : 0 < Nu)
    (hcovU : (Finset.Ico v₀u (v₁u + 1)).biUnion (eadicCell Pu (2 * Nu)) = Pu)
    (qu : ℕ → ℕ)
    (hqcellU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1), qu v ∈ eadicCell Pu (2 * Nu) v)
    (hq1U : ∀ v, 1 ≤ qu v)
    (hqminU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v, qu v ≤ p)
    (hLAU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v, A / (Nu * p) + 1 ≤ A / p)
    (hLBU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v,
        (A + Delta) / (Nu * p) + 1 ≤ (A + Delta) / p)
    (w : ℝ → ℝ) (hwm : Measurable w) (hw0 : ∀ xi, 0 ≤ w xi)
    (hwsup : ∀ xi, w xi ≤ (4 * (H : ℝ) / (A : ℝ)) ^ 2)
    (PcU : ℕ → ℕ) (hPcU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1), 2 ≤ PcU v)
    (hloU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v, PcU v < p)
    (hhiU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v, p ≤ 2 * PcU v)
    (D delta₀ : ℝ) (hD : 1 ≤ D) (hdelta₀ : 0 < delta₀) (hdelta₁ : delta₀ ≤ 1)
    (yU : ℕ) (hyU : 4 ≤ yU) (hPuy : ∀ p ∈ Pu, p < yU)
    (hBqCutoff : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      cellHalaszThreshold ≤ (A + Delta) / qu v)
    (hNP : ∀ u : ℕ, cellHalaszThreshold ≤ u → u ≤ 3 * (A + Delta) →
      NonPretentiousAt g (2 * D) u)
    (hA0 : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      0 < 64 * ((((A + Delta) / qu v : ℕ) : ℝ)
          + ((bandCells K₂).card : ℝ) * Real.sqrt T)
        * (Real.log (2 * T) + 1)
        * ∑ n ∈ Finset.Icc 1 ((A + Delta) / qu v),
            ‖cellBlockCoeff g A (A + Delta) Pu ((List.range J).map Pl) (qu v) n‖ ^ 2 /
              (n : ℝ) ^ 2)
    (hB0 : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      0 < Cp * (∑ p ∈ eadicCell Pu (2 * Nu) v, ‖g p‖ ^ 2 / (p : ℝ) ^ 2)
        * (PcU v : ℝ) / Real.log (PcU v))
    (kappaU : ℕ → ℝ)
    (hscheduleUCell : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      exceptionalCellScheduleCost
          (exceptionalIntegerSchedule A Delta qu T v)
          (exceptionalPrimeSchedule Cp PcU v)
          (exceptionalRatioSchedule PcU T v)
          (exceptionalDeltaSchedule D delta₀ T A Delta ((List.range J).map Pl) qu yU v)
        ≤ kappaU v * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (PminU QmaxU : ℕ) (hPminU : 1 ≤ PminU) (hQmaxU : 3 ≤ QmaxU)
    (hPulo : ∀ p ∈ Pu, PminU < p) (hPuhi : ∀ p ∈ Pu, p ≤ QmaxU)
    (hNuQ : Nu * QmaxU ≤ A)
    (kappaReplacementU kappaCollisionU : ℝ)
    (hkappaReplacementU : 0 ≤ kappaReplacementU * c₃)
    (hscheduleReplacementU :
      64 * ((Finset.Ico v₀u (v₁u + 1)).card : ℝ)
          * replacementCost A Nu QmaxU T
          * ((256 * (QmaxU : ℝ) / ((PminU : ℝ) * Real.log QmaxU))
            * levelPrimeMassBound QmaxU)
        ≤ kappaReplacementU * c₃ * eps ^ 3)
    (hscheduleCollisionU :
      8 * (levelPrimeMassBound QmaxU
        * ((levelPrimeMassBound QmaxU / (PminU : ℝ) ^ 2)
          * (Real.exp Real.pi * (2 * T * (QmaxU : ℝ) ^ 2 / (A : ℝ) + 8)
            * Real.log (2 * (R : ℝ)))))
        ≤ kappaCollisionU * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hscheduleUShare :
      2 * ((Finset.Ico v₀u (v₁u + 1)).card : ℝ)
          * (∑ v ∈ Finset.Ico v₀u (v₁u + 1), kappaU v)
          + 2 * kappaReplacementU + 2 * kappaCollisionU
        ≤ (1 / 2 ^ (J + 1)) / (4 * (H : ℝ) / (A : ℝ)) ^ 2) :
    (∫ xi in {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂},
        ‖∑ m ∈ typicalS A (A + Delta) (innerBandLevels Pl Pu J),
            (g m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2 * w xi)
      ≤ bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
  have hT0 : 0 ≤ T := zero_le_one.trans hT1
  have hT : 0 < T := zero_lt_one.trans_le hT1
  have hrho0 : 0 ≤ (Delta : ℝ) / (A : ℝ) := by positivity
  have hbudget0 := bandBudget_nonneg c₃ eps ((Delta : ℝ) / (A : ℝ)) hc₃ hrho0
  by_cases hzero : g 1 = 0
  · have hgzero : ∀ n, n ≠ 0 → g n = 0 := by
      intro n hn
      have hmul := hcm 1 n one_ne_zero hn
      simpa [hzero] using hmul
    have hsum : ∀ xi : ℝ,
        ∑ m ∈ typicalS A (A + Delta) (innerBandLevels Pl Pu J),
            (g m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ) = 0 := by
      intro xi
      apply Finset.sum_eq_zero
      intro m hm
      have hmA := (mem_typicalS.mp hm).1.1
      simp [hgzero m (by omega)]
    simp_rw [hsum]
    simpa using hbudget0
  have h1 : g 1 = 1 := by
    have hmul := hcm 1 1 one_ne_zero one_ne_zero
    have hcancel : g 1 * g 1 = g 1 * 1 := by
      simpa using hmul.symm
    exact mul_left_cancel₀ hzero hcancel
  have halpha : ∀ j < J, 0 < innerBandScheduleAlpha j := by
    intro j hj
    unfold innerBandScheduleAlpha
    exact scheduleAlpha_pos (j + 1) (by omega)
  have halpha2 : 0 < J → 2 * innerBandScheduleAlpha 0 < 1 := by
    intro _
    unfold innerBandScheduleAlpha
    exact scheduleAlpha_two_lt_one 1 (by omega)
  have hC0 : 0 ≤ Real.log (2 * (R : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * R))
  have hC : 0 < J → ∀ v ∈ Finset.Ico (v₀l 0) (v₁l 0 + 1),
      ∑ m ∈ Finset.Ioc (A / ql 0 v) ((A + Delta) / ql 0 v),
        (1 : ℝ) / (m : ℝ) ≤ Real.log (2 * (R : ℝ)) := by
    intro hJ v hv
    exact quotient_harmonic_le_log_two_mul A (A + Delta) (ql 0 v) R
      (hq1l 0 hJ v) (by have := hqAl 0 hJ v; omega) hR hB
  have hfit0 : 0 < J →
      (((Finset.Ico (v₀l 0) (v₁l 0 + 1)).card : ℝ)
        * (Real.exp Real.pi * Real.log (2 * (R : ℝ))
          * ((2 * T * Real.exp (1 / ((2 * Nl 0 : ℕ) : ℝ)) / (A : ℝ))
            * ((Qhi 0) ^ (1 - 2 * innerBandScheduleAlpha 0)
              * Real.exp ((1 - 2 * innerBandScheduleAlpha 0) / ((2 * Nl 0 : ℕ) : ℝ)))
            * (((2 * Nl 0 : ℕ) : ℝ) / (1 - 2 * innerBandScheduleAlpha 0) + 1)))
          ≤ ordinaryLegShare 0 / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))) ∧
       (((Finset.Ico (v₀l 0) (v₁l 0 + 1)).card : ℝ)
        * (Real.exp Real.pi * Real.log (2 * (R : ℝ))
          * (4 * (R : ℝ)
            * ((Plo 0) ^ (-(2 * innerBandScheduleAlpha 0))
              * Real.exp (2 * innerBandScheduleAlpha 0 / ((2 * Nl 0 : ℕ) : ℝ)))
            * (((2 * Nl 0 : ℕ) : ℝ) / (2 * innerBandScheduleAlpha 0) + 1)))
          ≤ ordinaryLegShare 0 / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))) := by
    intro hJ
    exact levelOne_fit_pair_of_schedule (Nl 0) R T A (Plo 0) (Qhi 0)
      (innerBandScheduleAlpha 0) c₃ eps ((Delta : ℝ) / (A : ℝ))
      (ordinaryLegShare 0) (hNl 0 hJ) hR hT0 (by exact_mod_cast hA)
      (halpha 0 hJ) (halpha2 hJ) (hPlo0 0 hJ) (hPloQhi 0 hJ)
      (v₀l 0) (v₁l 0) (htop 0 hJ) (hbot 0 hJ)
      (hscheduleT0 hJ) (hscheduleP0 hJ)
  have hfitLater : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      (2 * (Nl j : ℝ) * (Real.log (Qhi j) - Real.log (Plo j)) + 2)
        * (((Plo j) ^ (-(2 * innerBandScheduleAlpha j))
              * Real.exp (2 * innerBandScheduleAlpha j / ((2 * Nl j : ℕ) : ℝ))
              * (((2 * Nl j : ℕ) : ℝ) / (2 * innerBandScheduleAlpha j) + 1))
            * ((Real.exp Real.pi
                  * (T / (((Pmom j r) ^ (ell j r) * A' j r : ℕ) : ℝ)
                    + 2 * ((2 ^ (ell j r + 1) : ℕ) : ℝ)))
              * (((Nat.factorial (ell j r) : ℝ) ^ 2
                * (((2 ^ (ell j r + 1) : ℕ) : ℝ) * ((ell j r : ℝ) + 1)
                  * (∑ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r,
                      (1 : ℝ) / (p : ℝ)) ^ (ell j r)))
                / ((Qhi (j - 1)) ^ (-(innerBandScheduleAlpha (j - 1)))
                    * Real.exp (-(innerBandScheduleAlpha (j - 1) /
                      ((2 * Nl (j - 1) : ℕ) : ℝ)))) ^ (2 * ell j r))))
      ≤ geometricCellShare (ordinaryLegShare j) r
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    intro j hj0 hjJ r hr
    have hjprev : j - 1 < J := by omega
    apply laterLevel_fit_of_schedule (Nl j) (Nl (j - 1)) (v₀l j) (v₁l j)
      (ell j r) (Pmom j r) (A' j r)
      (eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r)
      (Plo j) (Qhi j) (innerBandScheduleAlpha j) (Qhi (j - 1))
      (innerBandScheduleAlpha (j - 1)) T c₃ eps
      ((Delta : ℝ) / (A : ℝ)) (geometricCellShare (ordinaryLegShare j) r)
      (hNl j hjJ) (hNl (j - 1) hjprev) (halpha j hjJ)
      (halpha (j - 1) hjprev).le (hPlo0 j hjJ) (hPloQhi j hjJ)
      (hQhi0 (j - 1) hjprev) (hPmom2 j hj0 hjJ r hr) hT0
    · intro p hp
      exact hPl (j - 1) hjprev p (mem_eadicCell.mp hp).1
    · exact hlomom j hj0 hjJ r hr
    · exact hhimom j hj0 hjJ r hr
    · exact hscheduleLater j hj0 hjJ r hr
  have hlevelSub : ∀ j < J,
      Pl j ⊆ (Finset.Ioc (Pb j) (bb j)).filter Nat.Prime := by
    intro j hj
    exact level_subset_primeInterval (Pl j) (Nl j) (v₀l j) (v₁l j)
      (Pb j) (bb j) (hcovl j hj) (hlevel j hj)
  have hcosts : ∀ j < J,
      (∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
        ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
          Real.exp Real.pi * (T / ((A / p : ℕ) : ℝ) + 4)
              * (((A / (Nl j * p) + 1 : ℕ) : ℝ) / ((A / p : ℕ) : ℝ))
            ≤ replacementCost A (Nl j) (bb j) T) ∧
      (∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
        ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
          Real.exp Real.pi * (T / (((A + Delta) / p : ℕ) : ℝ) + 4)
              * (((((A + Delta) / (Nl j * p)) + 1 : ℕ) : ℝ) /
                (((A + Delta) / p : ℕ) : ℝ))
            ≤ replacementCost A (Nl j) (bb j) T) := by
    intro j hj
    exact eadic_replacement_costs_of_schedule (Pl j) (Nl j) (v₀l j) (v₁l j)
      A (A + Delta) (bb j) T (hNl j hj) hA (Nat.le_add_right A Delta) hT0
      (hPl j hj) (hPAl j hj)
      (fun p hp => (Finset.mem_Ioc.mp
        (Finset.mem_filter.mp (hlevelSub j hj hp)).1).2) (hNbb j hj)
  have hcollisionFit : ∀ j < J,
      8 * collisionEnergyBound A (A + Delta) (Pl j)
          (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j) T
        ≤ ordinaryLegShare j * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    intro j hj
    apply collision_fit_of_schedule A (A + Delta) R (Pl j)
      (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j) T
      (Pb j : ℝ) (bb j : ℝ) (levelPrimeMassBound (bb j)) c₃ eps
      ((Delta : ℝ) / (A : ℝ)) (ordinaryLegShare j) hA hR hB hT0
      (by exact_mod_cast hPb j hj) (by positivity) (hPl j hj) (hPAl j hj)
    · intro p hp
      exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hlevelSub j hj hp)).1).1.le
    · intro p hp
      exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hlevelSub j hj hp)).1).2
    · exact level_primeMass_le (Pl j) (Nl j) (v₀l j) (v₁l j)
        (Pb j) (bb j) (hbb j hj) (hcovl j hj) (hlevel j hj)
    · exact hscheduleCollision j hj
  let restU := (List.range J).map Pl
  let deltaU : ℕ → ℝ := fun v =>
    exceptionalDeltaSchedule D delta₀ T A Delta restU qu yU v
  have hrestPrime : ∀ Q ∈ restU, ∀ p ∈ Q, p.Prime := by
    intro Q hQ p hp
    dsimp [restU] at hQ
    rw [List.mem_map] at hQ
    obtain ⟨j, hj, rfl⟩ := hQ
    exact hPl j (List.mem_range.mp hj) p hp
  have hdeltaU0 : ∀ v ∈ Finset.Ico v₀u (v₁u + 1), 0 < deltaU v := by
    intro v hv
    have hp := cellHalaszPartialBudget_nonneg D delta₀ ((A + Delta) / qu v)
      hdelta₀ (hBqCutoff v hv)
    have hab : 0 ≤ cellHalaszAbelFactor T := by
      unfold cellHalaszAbelFactor
      positivity
    have hlog : 0 < Real.log yU := Real.log_pos (by exact_mod_cast (by omega : 1 < yU))
    have hquot : 0 < cellHalaszScheduleQuotientBound D delta₀ T ((A + Delta) / qu v) := by
      have hBq1 : 1 ≤ (A + Delta) / qu v := by
        have := hBqCutoff v hv
        unfold cellHalaszThreshold at this
        omega
      have hlogBq : 0 ≤ Real.log (((A + Delta) / qu v : ℕ) : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hBq1)
      unfold cellHalaszScheduleQuotientBound
      nlinarith [mul_nonneg hp hab]
    dsimp [deltaU, exceptionalDeltaSchedule]
    positivity
  have hdeltaU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1), ∀ t : ℝ, |t| ≤ T →
      ‖∑ n ∈ Finset.Icc 1 ((A + Delta) / qu v),
          (cellBlockCoeff g A (A + Delta) Pu restU (qu v) n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ deltaU v := by
    intro v hv t ht
    have hraw := norm_cellBlock_poly_le_cellHalaszBound_of_uniform g hcm hg h1
      A Delta (qu v) (hq1U v) hDeltaA Pu hPu restU hrestPrime
      D hD delta₀ hdelta₀ hdelta₁ T t ht hNP
    refine hraw.trans ?_
    dsimp [deltaU]
    apply cellHalaszBound_le_explicit_schedule D delta₀ T (A / qu v)
      ((A + Delta) / qu v) yU Pu restU hdelta₀ hT0 (hBqCutoff v hv)
    · exact div_le_two_mul_div_add_one A (A + Delta) (qu v)
        (by have := hq1U v; omega) (by omega)
    · exact hyU
    · exact hPuy
  have hfitUCell : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      2 * ((deltaU v) ^ 2 * (Cp * (256 / (Real.log (PcU v)) ^ 2))
        + 2 * deltaU v * Real.sqrt
            ((128 * ((((A + Delta) / qu v : ℕ) : ℝ) + 2 * T * Real.sqrt T)
                * (Real.log (2 * T) + 1))
              * ((Cp * (256 / (Real.log (PcU v)) ^ 2))
                  * (Real.exp Real.pi * ((T + 1) / (PcU v : ℝ) + 4)
                    * (256 / Real.log (PcU v) + 2048 * Real.pi)
                    * Real.exp (-(Real.log (PcU v) /
                      (Real.log (2 * T)) ^ primeLargeValuesExponent))
                    * (Real.log (2 * T)) ^ 2))))
        ≤ kappaU v * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    intro v hv
    simpa [deltaU, exceptionalCellScheduleCost, exceptionalIntegerSchedule,
      exceptionalPrimeSchedule, exceptionalRatioSchedule] using hscheduleUCell v hv
  have hPuSub : Pu ⊆ (Finset.Ioc PminU QmaxU).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hPulo p hp, hPuhi p hp⟩, hPu p hp⟩
  have hmassU : ∑ p ∈ Pu, (1 : ℝ) / (p : ℝ) ≤ levelPrimeMassBound QmaxU := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hPuSub
      (fun p _ _ => by positivity)).trans ?_
    exact sum_one_div_prime_Ioc_le_mertens PminU QmaxU hQmaxU
  have hRepU : 2 * cellReplacementEnergyBound Pu Nu v₀u v₁u A (A + Delta) T
      ≤ kappaReplacementU * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    have hraw := eadic_replacement_error_le_budget_of_schedule Pu Nu v₀u v₁u
      A (A + Delta) QmaxU PminU QmaxU QmaxU T c₃ eps
      ((Delta : ℝ) / (A : ℝ)) kappaReplacementU (fun _ => PminU)
      hNu hA (Nat.le_add_right A Delta) hT0 hPu hPAu hPuhi hNuQ
      hPminU (by omega) hQmaxU
      (fun v _ => le_rfl)
      (fun v hv p hp => by
        rw [Finset.mem_filter, Finset.mem_Ioc]
        have hpP := (mem_eadicCell.mp hp).1
        exact ⟨⟨hPulo p hpP, by have := hPuhi p hpP; omega⟩, hPu p hpP⟩)
      (fun v hv p hp => hPuSub (mem_eadicCell.mp hp).1)
      hkappaReplacementU hrho
      hscheduleReplacementU
    simpa [cellReplacementEnergyBound] using hraw
  have hCollU : 8 * collisionEnergyBound A (A + Delta) Pu restU T
      ≤ kappaCollisionU * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    apply collision_fit_of_schedule A (A + Delta) R Pu restU T
      (PminU : ℝ) (QmaxU : ℝ) (levelPrimeMassBound QmaxU)
      c₃ eps ((Delta : ℝ) / (A : ℝ)) kappaCollisionU
      hA hR hB hT0 (by exact_mod_cast hPminU) (by positivity) hPu hPAu
      (fun p hp => by exact_mod_cast (hPulo p hp).le)
      (fun p hp => by exact_mod_cast hPuhi p hp) hmassU hscheduleCollisionU
  have hfitU : 2 * ((Finset.Ico v₀u (v₁u + 1)).card : ℝ)
          * (∑ v ∈ Finset.Ico v₀u (v₁u + 1), kappaU v)
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))
        + 2 * (2 * cellReplacementEnergyBound Pu Nu v₀u v₁u A (A + Delta) T
            + 2 * (4 * collisionEnergyBound A (A + Delta) Pu restU T))
      ≤ (1 / 2 ^ (J + 1)) * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) /
          (4 * (H : ℝ) / (A : ℝ)) ^ 2 := by
    have hshare := mul_le_mul_of_nonneg_right hscheduleUShare hbudget0
    calc
      2 * ((Finset.Ico v₀u (v₁u + 1)).card : ℝ)
            * (∑ v ∈ Finset.Ico v₀u (v₁u + 1), kappaU v)
            * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))
          + 2 * (2 * cellReplacementEnergyBound Pu Nu v₀u v₁u A (A + Delta) T
              + 2 * (4 * collisionEnergyBound A (A + Delta) Pu restU T))
        ≤ (2 * ((Finset.Ico v₀u (v₁u + 1)).card : ℝ)
              * (∑ v ∈ Finset.Ico v₀u (v₁u + 1), kappaU v)
              + 2 * kappaReplacementU + 2 * kappaCollisionU)
            * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
          nlinarith [hRepU, hCollU]
      _ ≤ ((1 / 2 ^ (J + 1)) / (4 * (H : ℝ) / (A : ℝ)) ^ 2)
            * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := hshare
      _ = (1 / 2 ^ (J + 1)) * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) /
            (4 * (H : ℝ) / (A : ℝ)) ^ 2 := by ring
  apply band_energy_typicalS_le_of_levels Cp hCp1 hprime
    (X := fun j => replacementCost A (Nl j) (bb j) T)
    g hcm hg A Delta H hA hH hDeltaA
    Pl Pu J hPl hPu hPAl hPAu hdisj hdisjU Nl v₀l v₁l ql innerBandScheduleAlpha
    hNl hcovl hqcelll hq1l hqAl hqminl hLAl hLBl Plo Qhi halpha halpha2
    hPlo0 hQhi0 hPloQhi htop hbot R hR hB (fun _ => Real.log (2 * (R : ℝ)))
    hC0 hC K₁ K₂ T hT1 hTK₂ c₃ eps hc₃
    (fun j => ordinaryLegShare j) (fun j => ordinaryLegShare j)
    (fun j => ordinaryLegShare j)
    (fun hJ => (hfit0 hJ).1) (fun hJ => (hfit0 hJ).2)
    A' Delta' Pmom ell hA' hDelta' hSblk hPmom hlomom hhimom hell
    (fun j r => geometricCellShare (ordinaryLegShare j) r) hfitLater
  · intro j hj0 hjJ
    exact sum_geometricCellShare_Ico_le (v₀l (j - 1)) (v₁l (j - 1))
      (ordinaryLegShare j) (by unfold ordinaryLegShare; positivity)
  · exact hPb
  · exact hKc
  · exact hbb
  · intro j hj
    unfold replacementCost
    positivity
  · exact fun j hj => (hcosts j hj).1
  · exact fun j hj => (hcosts j hj).2
  · exact haa
  · exact hcell
  · exact hlevel
  · intro j hj
    exact mul_nonneg (by unfold ordinaryLegShare; positivity) hc₃
  · exact hrho
  · intro j hj
    simpa [levelPrimeMassBound] using hscheduleReplacement j hj
  · exact hcollisionFit
  · intro j hj
    exact ordinaryLegShares_fit A H j hA h3HA
  · exact hNu
  · exact hcovU
  · exact hqcellU
  · exact hq1U
  · exact hqminU
  · exact hLAU
  · exact hLBU
  · exact hwm
  · exact hw0
  · exact hwsup
  · exact hPcU
  · exact hloU
  · exact hhiU
  · exact hdeltaU0
  · simpa [restU] using hdeltaU
  · simpa [restU] using hA0
  · exact hB0
  · exact hfitUCell
  · simpa [restU] using hfitU

-- The primed capstone repeats the explicit schedule elaboration with a scaled
-- budget, so allow the same bounded elaboration headroom as the analytic capstones.
set_option maxHeartbeats 800000 in
/-- **Phase 0 VI-9a — the inner band with honest exceptional-leg accounting.**

The ordinary-level fits are unchanged.  The exceptional shares now sum to their
actual dyadic allocation, with no division by the Fourier-weight supremum.  The
factor `(4H/A)²` consequently remains on the final budget, which is the form
consumed by `slice_energy_le_of_bands`. -/
theorem band_energy_typicalS_le_of_schedule' [HalaszLargeValuesAssumption]
    (Cp : ℝ) (hCp1 : 1 ≤ Cp) (hprime : PrimeLargeValuesBound Cp)
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta H : ℕ) (hA : 0 < A) (hH : 0 < H) (hDeltaA : Delta ≤ A)
    (h3HA : 3 * H ≤ A)
    (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ) (J : ℕ)
    (hPl : ∀ i < J, ∀ p ∈ Pl i, p.Prime)
    (hPu : ∀ p ∈ Pu, p.Prime)
    (hPAl : ∀ i < J, ∀ p ∈ Pl i, p * p ≤ A)
    (hPAu : ∀ p ∈ Pu, p * p ≤ A)
    (hdisj : ∀ i < J, ∀ k < J, i ≠ k → Disjoint (Pl i) (Pl k))
    (hdisjU : ∀ i < J, Disjoint (Pl i) Pu)
    (Nl v₀l v₁l : ℕ → ℕ) (ql : ℕ → ℕ → ℕ)
    (hNl : ∀ j < J, 0 < Nl j)
    (hcovl : ∀ j < J, (Finset.Ico (v₀l j) (v₁l j + 1)).biUnion
      (eadicCell (Pl j) (2 * Nl j)) = Pl j)
    (hqcelll : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ql j v ∈ eadicCell (Pl j) (2 * Nl j) v)
    (hq1l : ∀ j < J, ∀ v, 1 ≤ ql j v)
    (hqAl : ∀ j < J, ∀ v, 2 * ql j v ≤ A)
    (hqminl : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v, ql j v ≤ p)
    (hLAl : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
        A / (Nl j * p) + 1 ≤ A / p)
    (hLBl : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
        (A + Delta) / (Nl j * p) + 1 ≤ (A + Delta) / p)
    (Plo Qhi : ℕ → ℝ)
    (hPlo0 : ∀ j < J, 0 < Plo j) (hQhi0 : ∀ j < J, 0 < Qhi j)
    (hPloQhi : ∀ j < J, Plo j ≤ Qhi j)
    (htop : ∀ j < J,
      (v₁l j : ℝ) ≤ 2 * (Nl j : ℝ) * Real.log (Qhi j))
    (hbot : ∀ j < J,
      2 * (Nl j : ℝ) * Real.log (Plo j) - 1 ≤ (v₀l j : ℝ))
    (R : ℕ) (hR : 1 ≤ R) (hB : A + Delta ≤ R * A)
    (K₁ K₂ T : ℝ) (hT1 : 1 ≤ T) (hTK₂ : K₂ + 2 ≤ T)
    (c₃ eps : ℝ) (hc₃ : 0 ≤ c₃)
    (hscheduleT0 : 0 < J →
      (2 * (Nl 0 : ℝ) * (Real.log (Qhi 0) - Real.log (Plo 0)) + 2)
        * (Real.exp Real.pi * Real.log (2 * (R : ℝ))
          * ((2 * T * Real.exp (1 / ((2 * Nl 0 : ℕ) : ℝ)) / (A : ℝ))
            * ((Qhi 0) ^ (1 - 2 * innerBandScheduleAlpha 0)
              * Real.exp ((1 - 2 * innerBandScheduleAlpha 0) /
                ((2 * Nl 0 : ℕ) : ℝ)))
            * (((2 * Nl 0 : ℕ) : ℝ) / (1 - 2 * innerBandScheduleAlpha 0) + 1)))
      ≤ ordinaryLegShare 0 / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hscheduleP0 : 0 < J →
      (2 * (Nl 0 : ℝ) * (Real.log (Qhi 0) - Real.log (Plo 0)) + 2)
        * (Real.exp Real.pi * Real.log (2 * (R : ℝ))
          * (4 * (R : ℝ)
            * ((Plo 0) ^ (-(2 * innerBandScheduleAlpha 0))
              * Real.exp (2 * innerBandScheduleAlpha 0 /
                ((2 * Nl 0 : ℕ) : ℝ)))
            * (((2 * Nl 0 : ℕ) : ℝ) / (2 * innerBandScheduleAlpha 0) + 1)))
      ≤ ordinaryLegShare 0 / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (A' Delta' Pmom ell : ℕ → ℕ → ℕ)
    (hA' : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1), 1 ≤ A' j r)
    (hDelta' : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
        Delta' j r ≤ A' j r)
    (hSblk : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
        Finset.Ioc (A / ql j v) ((A + Delta) / ql j v) ⊆
          Finset.Ioc (A' j r) (A' j r + Delta' j r))
    (hPmom : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1), 1 ≤ Pmom j r)
    (hPmom2 : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1), 2 ≤ Pmom j r)
    (hlomom : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      ∀ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r, Pmom j r < p)
    (hhimom : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      ∀ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r, p ≤ 2 * Pmom j r)
    (hell : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1), 1 ≤ ell j r)
    (hscheduleLater : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      (2 * (Nl j : ℝ) * (Real.log (Qhi j) - Real.log (Plo j)) + 2)
        * (((Plo j) ^ (-(2 * innerBandScheduleAlpha j))
              * Real.exp (2 * innerBandScheduleAlpha j / ((2 * Nl j : ℕ) : ℝ))
              * (((2 * Nl j : ℕ) : ℝ) / (2 * innerBandScheduleAlpha j) + 1))
          * ((Real.exp Real.pi
                * (T / (((Pmom j r) ^ (ell j r) * A' j r : ℕ) : ℝ)
                  + 2 * ((2 ^ (ell j r + 1) : ℕ) : ℝ)))
            * laterMomentScheduleBound (ell j r) (Pmom j r)
                ((Qhi (j - 1)) ^ (-(innerBandScheduleAlpha (j - 1)))
                  * Real.exp (-(innerBandScheduleAlpha (j - 1) /
                    ((2 * Nl (j - 1) : ℕ) : ℝ))))))
      ≤ geometricCellShare (ordinaryLegShare j) r
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (Pb Kc bb : ℕ → ℕ) (aa : ℕ → ℕ → ℕ)
    (hPb : ∀ j < J, 1 ≤ Pb j) (hKc : ∀ j < J, 2 ≤ Kc j)
    (hbb : ∀ j < J, 3 ≤ bb j)
    (haa : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1), Pb j ≤ aa j v)
    (hcell : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      eadicCell (Pl j) (2 * Nl j) v ⊆
        (Finset.Ioc (aa j v) (aa j v + Kc j)).filter Nat.Prime)
    (hlevel : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      eadicCell (Pl j) (2 * Nl j) v ⊆
        (Finset.Ioc (Pb j) (bb j)).filter Nat.Prime)
    (hNbb : ∀ j < J, Nl j * bb j ≤ A)
    (hrho : eps ≤ (Delta : ℝ) / (A : ℝ))
    (hscheduleReplacement : ∀ j < J,
      64 * ((Finset.Ico (v₀l j) (v₁l j + 1)).card : ℝ)
          * replacementCost A (Nl j) (bb j) T
          * ((256 * (Kc j : ℝ) / ((Pb j : ℝ) * Real.log (Kc j)))
            * levelPrimeMassBound (bb j))
        ≤ ordinaryLegShare j * c₃ * eps ^ 3)
    (hscheduleCollision : ∀ j < J,
      8 * (levelPrimeMassBound (bb j)
        * ((levelPrimeMassBound (bb j) / (Pb j : ℝ) ^ 2)
          * (Real.exp Real.pi * (2 * T * (bb j : ℝ) ^ 2 / (A : ℝ) + 8)
            * Real.log (2 * (R : ℝ)))))
        ≤ ordinaryLegShare j * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (Nu v₀u v₁u : ℕ) (hNu : 0 < Nu)
    (hcovU : (Finset.Ico v₀u (v₁u + 1)).biUnion (eadicCell Pu (2 * Nu)) = Pu)
    (qu : ℕ → ℕ)
    (hqcellU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1), qu v ∈ eadicCell Pu (2 * Nu) v)
    (hq1U : ∀ v, 1 ≤ qu v)
    (hqminU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v, qu v ≤ p)
    (hLAU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v, A / (Nu * p) + 1 ≤ A / p)
    (hLBU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v,
        (A + Delta) / (Nu * p) + 1 ≤ (A + Delta) / p)
    (w : ℝ → ℝ) (hwm : Measurable w) (hw0 : ∀ xi, 0 ≤ w xi)
    (hwsup : ∀ xi, w xi ≤ (4 * (H : ℝ) / (A : ℝ)) ^ 2)
    (PcU : ℕ → ℕ) (hPcU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1), 2 ≤ PcU v)
    (hloU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v, PcU v < p)
    (hhiU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      ∀ p ∈ eadicCell Pu (2 * Nu) v, p ≤ 2 * PcU v)
    (D delta₀ : ℝ) (hD : 1 ≤ D) (hdelta₀ : 0 < delta₀) (hdelta₁ : delta₀ ≤ 1)
    (yU : ℕ) (hyU : 4 ≤ yU) (hPuy : ∀ p ∈ Pu, p < yU)
    (hBqCutoff : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      cellHalaszThreshold ≤ (A + Delta) / qu v)
    (hNP : ∀ u : ℕ, cellHalaszThreshold ≤ u → u ≤ 3 * (A + Delta) →
      NonPretentiousAt g (2 * D) u)
    (hA0 : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      0 < 64 * ((((A + Delta) / qu v : ℕ) : ℝ)
          + ((bandCells K₂).card : ℝ) * Real.sqrt T)
        * (Real.log (2 * T) + 1)
        * ∑ n ∈ Finset.Icc 1 ((A + Delta) / qu v),
            ‖cellBlockCoeff g A (A + Delta) Pu ((List.range J).map Pl) (qu v) n‖ ^ 2 /
              (n : ℝ) ^ 2)
    (hB0 : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      0 < Cp * (∑ p ∈ eadicCell Pu (2 * Nu) v, ‖g p‖ ^ 2 / (p : ℝ) ^ 2)
        * (PcU v : ℝ) / Real.log (PcU v))
    (kappaU : ℕ → ℝ)
    (hscheduleUCell : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      exceptionalCellScheduleCost
          (exceptionalIntegerSchedule A Delta qu T v)
          (exceptionalPrimeSchedule Cp PcU v)
          (exceptionalRatioSchedule PcU T v)
          (exceptionalDeltaSchedule D delta₀ T A Delta ((List.range J).map Pl) qu yU v)
        ≤ kappaU v * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (PminU QmaxU : ℕ) (hPminU : 1 ≤ PminU) (hQmaxU : 3 ≤ QmaxU)
    (hPulo : ∀ p ∈ Pu, PminU < p) (hPuhi : ∀ p ∈ Pu, p ≤ QmaxU)
    (hNuQ : Nu * QmaxU ≤ A)
    (kappaReplacementU kappaCollisionU : ℝ)
    (hkappaReplacementU : 0 ≤ kappaReplacementU * c₃)
    (hscheduleReplacementU :
      64 * ((Finset.Ico v₀u (v₁u + 1)).card : ℝ)
          * replacementCost A Nu QmaxU T
          * ((256 * (QmaxU : ℝ) / ((PminU : ℝ) * Real.log QmaxU))
            * levelPrimeMassBound QmaxU)
        ≤ kappaReplacementU * c₃ * eps ^ 3)
    (hscheduleCollisionU :
      8 * (levelPrimeMassBound QmaxU
        * ((levelPrimeMassBound QmaxU / (PminU : ℝ) ^ 2)
          * (Real.exp Real.pi * (2 * T * (QmaxU : ℝ) ^ 2 / (A : ℝ) + 8)
            * Real.log (2 * (R : ℝ)))))
        ≤ kappaCollisionU * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hscheduleUShare :
      2 * ((Finset.Ico v₀u (v₁u + 1)).card : ℝ)
          * (∑ v ∈ Finset.Ico v₀u (v₁u + 1), kappaU v)
          + 2 * kappaReplacementU + 2 * kappaCollisionU
        ≤ 1 / 2 ^ (J + 1)) :
    (∫ xi in {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂},
        ‖∑ m ∈ typicalS A (A + Delta) (innerBandLevels Pl Pu J),
            (g m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2 * w xi)
      ≤ (4 * (H : ℝ) / (A : ℝ)) ^ 2
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
  have hT0 : 0 ≤ T := zero_le_one.trans hT1
  have hT : 0 < T := zero_lt_one.trans_le hT1
  have hrho0 : 0 ≤ (Delta : ℝ) / (A : ℝ) := by positivity
  have hbudget0 := bandBudget_nonneg c₃ eps ((Delta : ℝ) / (A : ℝ)) hc₃ hrho0
  have hscale0 : 0 ≤ (4 * (H : ℝ) / (A : ℝ)) ^ 2 := sq_nonneg _
  by_cases hzero : g 1 = 0
  · have hgzero : ∀ n, n ≠ 0 → g n = 0 := by
      intro n hn
      have hmul := hcm 1 n one_ne_zero hn
      simpa [hzero] using hmul
    have hsum : ∀ xi : ℝ,
        ∑ m ∈ typicalS A (A + Delta) (innerBandLevels Pl Pu J),
            (g m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ) = 0 := by
      intro xi
      apply Finset.sum_eq_zero
      intro m hm
      have hmA := (mem_typicalS.mp hm).1.1
      simp [hgzero m (by omega)]
    simp_rw [hsum]
    simpa using mul_nonneg hscale0 hbudget0
  have h1 : g 1 = 1 := by
    have hmul := hcm 1 1 one_ne_zero one_ne_zero
    have hcancel : g 1 * g 1 = g 1 * 1 := by
      simpa using hmul.symm
    exact mul_left_cancel₀ hzero hcancel
  have halpha : ∀ j < J, 0 < innerBandScheduleAlpha j := by
    intro j hj
    unfold innerBandScheduleAlpha
    exact scheduleAlpha_pos (j + 1) (by omega)
  have halpha2 : 0 < J → 2 * innerBandScheduleAlpha 0 < 1 := by
    intro _
    unfold innerBandScheduleAlpha
    exact scheduleAlpha_two_lt_one 1 (by omega)
  have hC0 : 0 ≤ Real.log (2 * (R : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * R))
  have hC : 0 < J → ∀ v ∈ Finset.Ico (v₀l 0) (v₁l 0 + 1),
      ∑ m ∈ Finset.Ioc (A / ql 0 v) ((A + Delta) / ql 0 v),
        (1 : ℝ) / (m : ℝ) ≤ Real.log (2 * (R : ℝ)) := by
    intro hJ v hv
    exact quotient_harmonic_le_log_two_mul A (A + Delta) (ql 0 v) R
      (hq1l 0 hJ v) (by have := hqAl 0 hJ v; omega) hR hB
  have hfit0 : 0 < J →
      (((Finset.Ico (v₀l 0) (v₁l 0 + 1)).card : ℝ)
        * (Real.exp Real.pi * Real.log (2 * (R : ℝ))
          * ((2 * T * Real.exp (1 / ((2 * Nl 0 : ℕ) : ℝ)) / (A : ℝ))
            * ((Qhi 0) ^ (1 - 2 * innerBandScheduleAlpha 0)
              * Real.exp ((1 - 2 * innerBandScheduleAlpha 0) / ((2 * Nl 0 : ℕ) : ℝ)))
            * (((2 * Nl 0 : ℕ) : ℝ) / (1 - 2 * innerBandScheduleAlpha 0) + 1)))
          ≤ ordinaryLegShare 0 / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))) ∧
       (((Finset.Ico (v₀l 0) (v₁l 0 + 1)).card : ℝ)
        * (Real.exp Real.pi * Real.log (2 * (R : ℝ))
          * (4 * (R : ℝ)
            * ((Plo 0) ^ (-(2 * innerBandScheduleAlpha 0))
              * Real.exp (2 * innerBandScheduleAlpha 0 / ((2 * Nl 0 : ℕ) : ℝ)))
            * (((2 * Nl 0 : ℕ) : ℝ) / (2 * innerBandScheduleAlpha 0) + 1)))
          ≤ ordinaryLegShare 0 / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))) := by
    intro hJ
    exact levelOne_fit_pair_of_schedule (Nl 0) R T A (Plo 0) (Qhi 0)
      (innerBandScheduleAlpha 0) c₃ eps ((Delta : ℝ) / (A : ℝ))
      (ordinaryLegShare 0) (hNl 0 hJ) hR hT0 (by exact_mod_cast hA)
      (halpha 0 hJ) (halpha2 hJ) (hPlo0 0 hJ) (hPloQhi 0 hJ)
      (v₀l 0) (v₁l 0) (htop 0 hJ) (hbot 0 hJ)
      (hscheduleT0 hJ) (hscheduleP0 hJ)
  have hfitLater : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      (2 * (Nl j : ℝ) * (Real.log (Qhi j) - Real.log (Plo j)) + 2)
        * (((Plo j) ^ (-(2 * innerBandScheduleAlpha j))
              * Real.exp (2 * innerBandScheduleAlpha j / ((2 * Nl j : ℕ) : ℝ))
              * (((2 * Nl j : ℕ) : ℝ) / (2 * innerBandScheduleAlpha j) + 1))
            * ((Real.exp Real.pi
                  * (T / (((Pmom j r) ^ (ell j r) * A' j r : ℕ) : ℝ)
                    + 2 * ((2 ^ (ell j r + 1) : ℕ) : ℝ)))
              * (((Nat.factorial (ell j r) : ℝ) ^ 2
                * (((2 ^ (ell j r + 1) : ℕ) : ℝ) * ((ell j r : ℝ) + 1)
                  * (∑ p ∈ eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r,
                      (1 : ℝ) / (p : ℝ)) ^ (ell j r)))
                / ((Qhi (j - 1)) ^ (-(innerBandScheduleAlpha (j - 1)))
                    * Real.exp (-(innerBandScheduleAlpha (j - 1) /
                      ((2 * Nl (j - 1) : ℕ) : ℝ)))) ^ (2 * ell j r))))
      ≤ geometricCellShare (ordinaryLegShare j) r
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    intro j hj0 hjJ r hr
    have hjprev : j - 1 < J := by omega
    apply laterLevel_fit_of_schedule (Nl j) (Nl (j - 1)) (v₀l j) (v₁l j)
      (ell j r) (Pmom j r) (A' j r)
      (eadicCell (Pl (j - 1)) (2 * Nl (j - 1)) r)
      (Plo j) (Qhi j) (innerBandScheduleAlpha j) (Qhi (j - 1))
      (innerBandScheduleAlpha (j - 1)) T c₃ eps
      ((Delta : ℝ) / (A : ℝ)) (geometricCellShare (ordinaryLegShare j) r)
      (hNl j hjJ) (hNl (j - 1) hjprev) (halpha j hjJ)
      (halpha (j - 1) hjprev).le (hPlo0 j hjJ) (hPloQhi j hjJ)
      (hQhi0 (j - 1) hjprev) (hPmom2 j hj0 hjJ r hr) hT0
    · intro p hp
      exact hPl (j - 1) hjprev p (mem_eadicCell.mp hp).1
    · exact hlomom j hj0 hjJ r hr
    · exact hhimom j hj0 hjJ r hr
    · exact hscheduleLater j hj0 hjJ r hr
  have hlevelSub : ∀ j < J,
      Pl j ⊆ (Finset.Ioc (Pb j) (bb j)).filter Nat.Prime := by
    intro j hj
    exact level_subset_primeInterval (Pl j) (Nl j) (v₀l j) (v₁l j)
      (Pb j) (bb j) (hcovl j hj) (hlevel j hj)
  have hcosts : ∀ j < J,
      (∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
        ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
          Real.exp Real.pi * (T / ((A / p : ℕ) : ℝ) + 4)
              * (((A / (Nl j * p) + 1 : ℕ) : ℝ) / ((A / p : ℕ) : ℝ))
            ≤ replacementCost A (Nl j) (bb j) T) ∧
      (∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
        ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
          Real.exp Real.pi * (T / (((A + Delta) / p : ℕ) : ℝ) + 4)
              * (((((A + Delta) / (Nl j * p)) + 1 : ℕ) : ℝ) /
                (((A + Delta) / p : ℕ) : ℝ))
            ≤ replacementCost A (Nl j) (bb j) T) := by
    intro j hj
    exact eadic_replacement_costs_of_schedule (Pl j) (Nl j) (v₀l j) (v₁l j)
      A (A + Delta) (bb j) T (hNl j hj) hA (Nat.le_add_right A Delta) hT0
      (hPl j hj) (hPAl j hj)
      (fun p hp => (Finset.mem_Ioc.mp
        (Finset.mem_filter.mp (hlevelSub j hj hp)).1).2) (hNbb j hj)
  have hcollisionFit : ∀ j < J,
      8 * collisionEnergyBound A (A + Delta) (Pl j)
          (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j) T
        ≤ ordinaryLegShare j * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    intro j hj
    apply collision_fit_of_schedule A (A + Delta) R (Pl j)
      (innerBandLevelsBefore Pl J j ++ innerBandLevelsAfter Pl Pu J j) T
      (Pb j : ℝ) (bb j : ℝ) (levelPrimeMassBound (bb j)) c₃ eps
      ((Delta : ℝ) / (A : ℝ)) (ordinaryLegShare j) hA hR hB hT0
      (by exact_mod_cast hPb j hj) (by positivity) (hPl j hj) (hPAl j hj)
    · intro p hp
      exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hlevelSub j hj hp)).1).1.le
    · intro p hp
      exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hlevelSub j hj hp)).1).2
    · exact level_primeMass_le (Pl j) (Nl j) (v₀l j) (v₁l j)
        (Pb j) (bb j) (hbb j hj) (hcovl j hj) (hlevel j hj)
    · exact hscheduleCollision j hj
  let restU := (List.range J).map Pl
  let deltaU : ℕ → ℝ := fun v =>
    exceptionalDeltaSchedule D delta₀ T A Delta restU qu yU v
  have hrestPrime : ∀ Q ∈ restU, ∀ p ∈ Q, p.Prime := by
    intro Q hQ p hp
    dsimp [restU] at hQ
    rw [List.mem_map] at hQ
    obtain ⟨j, hj, rfl⟩ := hQ
    exact hPl j (List.mem_range.mp hj) p hp
  have hdeltaU0 : ∀ v ∈ Finset.Ico v₀u (v₁u + 1), 0 < deltaU v := by
    intro v hv
    have hp := cellHalaszPartialBudget_nonneg D delta₀ ((A + Delta) / qu v)
      hdelta₀ (hBqCutoff v hv)
    have hab : 0 ≤ cellHalaszAbelFactor T := by
      unfold cellHalaszAbelFactor
      positivity
    have hlog : 0 < Real.log yU := Real.log_pos (by exact_mod_cast (by omega : 1 < yU))
    have hquot : 0 < cellHalaszScheduleQuotientBound D delta₀ T ((A + Delta) / qu v) := by
      have hBq1 : 1 ≤ (A + Delta) / qu v := by
        have := hBqCutoff v hv
        unfold cellHalaszThreshold at this
        omega
      have hlogBq : 0 ≤ Real.log (((A + Delta) / qu v : ℕ) : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hBq1)
      unfold cellHalaszScheduleQuotientBound
      nlinarith [mul_nonneg hp hab]
    dsimp [deltaU, exceptionalDeltaSchedule]
    positivity
  have hdeltaU : ∀ v ∈ Finset.Ico v₀u (v₁u + 1), ∀ t : ℝ, |t| ≤ T →
      ‖∑ n ∈ Finset.Icc 1 ((A + Delta) / qu v),
          (cellBlockCoeff g A (A + Delta) Pu restU (qu v) n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ deltaU v := by
    intro v hv t ht
    have hraw := norm_cellBlock_poly_le_cellHalaszBound_of_uniform g hcm hg h1
      A Delta (qu v) (hq1U v) hDeltaA Pu hPu restU hrestPrime
      D hD delta₀ hdelta₀ hdelta₁ T t ht hNP
    refine hraw.trans ?_
    dsimp [deltaU]
    apply cellHalaszBound_le_explicit_schedule D delta₀ T (A / qu v)
      ((A + Delta) / qu v) yU Pu restU hdelta₀ hT0 (hBqCutoff v hv)
    · exact div_le_two_mul_div_add_one A (A + Delta) (qu v)
        (by have := hq1U v; omega) (by omega)
    · exact hyU
    · exact hPuy
  have hfitUCell : ∀ v ∈ Finset.Ico v₀u (v₁u + 1),
      2 * ((deltaU v) ^ 2 * (Cp * (256 / (Real.log (PcU v)) ^ 2))
        + 2 * deltaU v * Real.sqrt
            ((128 * ((((A + Delta) / qu v : ℕ) : ℝ) + 2 * T * Real.sqrt T)
                * (Real.log (2 * T) + 1))
              * ((Cp * (256 / (Real.log (PcU v)) ^ 2))
                  * (Real.exp Real.pi * ((T + 1) / (PcU v : ℝ) + 4)
                    * (256 / Real.log (PcU v) + 2048 * Real.pi)
                    * Real.exp (-(Real.log (PcU v) /
                      (Real.log (2 * T)) ^ primeLargeValuesExponent))
                    * (Real.log (2 * T)) ^ 2))))
        ≤ kappaU v * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    intro v hv
    simpa [deltaU, exceptionalCellScheduleCost, exceptionalIntegerSchedule,
      exceptionalPrimeSchedule, exceptionalRatioSchedule] using hscheduleUCell v hv
  have hPuSub : Pu ⊆ (Finset.Ioc PminU QmaxU).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hPulo p hp, hPuhi p hp⟩, hPu p hp⟩
  have hmassU : ∑ p ∈ Pu, (1 : ℝ) / (p : ℝ) ≤ levelPrimeMassBound QmaxU := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hPuSub
      (fun p _ _ => by positivity)).trans ?_
    exact sum_one_div_prime_Ioc_le_mertens PminU QmaxU hQmaxU
  have hRepU : 2 * cellReplacementEnergyBound Pu Nu v₀u v₁u A (A + Delta) T
      ≤ kappaReplacementU * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    have hraw := eadic_replacement_error_le_budget_of_schedule Pu Nu v₀u v₁u
      A (A + Delta) QmaxU PminU QmaxU QmaxU T c₃ eps
      ((Delta : ℝ) / (A : ℝ)) kappaReplacementU (fun _ => PminU)
      hNu hA (Nat.le_add_right A Delta) hT0 hPu hPAu hPuhi hNuQ
      hPminU (by omega) hQmaxU
      (fun v _ => le_rfl)
      (fun v hv p hp => by
        rw [Finset.mem_filter, Finset.mem_Ioc]
        have hpP := (mem_eadicCell.mp hp).1
        exact ⟨⟨hPulo p hpP, by have := hPuhi p hpP; omega⟩, hPu p hpP⟩)
      (fun v hv p hp => hPuSub (mem_eadicCell.mp hp).1)
      hkappaReplacementU hrho
      hscheduleReplacementU
    simpa [cellReplacementEnergyBound] using hraw
  have hCollU : 8 * collisionEnergyBound A (A + Delta) Pu restU T
      ≤ kappaCollisionU * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    apply collision_fit_of_schedule A (A + Delta) R Pu restU T
      (PminU : ℝ) (QmaxU : ℝ) (levelPrimeMassBound QmaxU)
      c₃ eps ((Delta : ℝ) / (A : ℝ)) kappaCollisionU
      hA hR hB hT0 (by exact_mod_cast hPminU) (by positivity) hPu hPAu
      (fun p hp => by exact_mod_cast (hPulo p hp).le)
      (fun p hp => by exact_mod_cast hPuhi p hp) hmassU hscheduleCollisionU
  have hfitUHonest : 2 * ((Finset.Ico v₀u (v₁u + 1)).card : ℝ)
          * (∑ v ∈ Finset.Ico v₀u (v₁u + 1), kappaU v)
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))
        + 2 * (2 * cellReplacementEnergyBound Pu Nu v₀u v₁u A (A + Delta) T
            + 2 * (4 * collisionEnergyBound A (A + Delta) Pu restU T))
      ≤ (1 / 2 ^ (J + 1)) * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    have hshare := mul_le_mul_of_nonneg_right hscheduleUShare hbudget0
    calc
      2 * ((Finset.Ico v₀u (v₁u + 1)).card : ℝ)
            * (∑ v ∈ Finset.Ico v₀u (v₁u + 1), kappaU v)
            * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))
          + 2 * (2 * cellReplacementEnergyBound Pu Nu v₀u v₁u A (A + Delta) T
              + 2 * (4 * collisionEnergyBound A (A + Delta) Pu restU T))
        ≤ (2 * ((Finset.Ico v₀u (v₁u + 1)).card : ℝ)
              * (∑ v ∈ Finset.Ico v₀u (v₁u + 1), kappaU v)
              + 2 * kappaReplacementU + 2 * kappaCollisionU)
            * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
          nlinarith [hRepU, hCollU]
      _ ≤ (1 / 2 ^ (J + 1))
            * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := hshare
  let Cw : ℝ := (4 * (H : ℝ) / (A : ℝ)) ^ 2
  have hCwpos : 0 < Cw := by
    dsimp [Cw]
    positivity
  have hbudgetScale :
      bandBudget (Cw * c₃) eps ((Delta : ℝ) / (A : ℝ)) =
        Cw * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    unfold bandBudget
    ring
  have hbudgetCancel (x : ℝ) :
      x / Cw * bandBudget (Cw * c₃) eps ((Delta : ℝ) / (A : ℝ)) =
        x * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    rw [hbudgetScale]
    field_simp
  have hbudgetHalfCancel (x : ℝ) :
      x / Cw / 2 * bandBudget (Cw * c₃) eps ((Delta : ℝ) / (A : ℝ)) =
        x / 2 * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    rw [hbudgetScale]
    field_simp
  have hc₃Cancel (x : ℝ) : x / Cw * (Cw * c₃) = x * c₃ := by
    field_simp
  have hc₃EpsCancel (x : ℝ) :
      x / Cw * (Cw * c₃) * eps ^ 3 = x * c₃ * eps ^ 3 := by
    field_simp
  have hthreeCancel (x : ℝ) :
      Cw * (2 * (x / Cw) + 2 * (x / Cw) + 2 * (x / Cw)) =
        2 * x + 2 * x + 2 * x := by
    field_simp
  change (∫ xi in {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂},
      ‖∑ m ∈ typicalS A (A + Delta) (innerBandLevels Pl Pu J),
          (g m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2 * w xi)
    ≤ Cw * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))
  rw [← hbudgetScale]
  apply band_energy_typicalS_le_of_levels Cp hCp1 hprime
    (X := fun j => replacementCost A (Nl j) (bb j) T)
    g hcm hg A Delta H hA hH hDeltaA
    Pl Pu J hPl hPu hPAl hPAu hdisj hdisjU Nl v₀l v₁l ql innerBandScheduleAlpha
    hNl hcovl hqcelll hq1l hqAl hqminl hLAl hLBl Plo Qhi halpha halpha2
    hPlo0 hQhi0 hPloQhi htop hbot R hR hB (fun _ => Real.log (2 * (R : ℝ)))
    hC0 hC K₁ K₂ T hT1 hTK₂ (Cw * c₃) eps (mul_nonneg hCwpos.le hc₃)
    (fun j => ordinaryLegShare j / Cw) (fun j => ordinaryLegShare j / Cw)
    (fun j => ordinaryLegShare j / Cw)
    (fun hJ => by rw [hbudgetHalfCancel]; exact (hfit0 hJ).1)
    (fun hJ => by rw [hbudgetHalfCancel]; exact (hfit0 hJ).2)
    A' Delta' Pmom ell hA' hDelta' hSblk hPmom hlomom hhimom hell
    (fun j r => geometricCellShare (ordinaryLegShare j) r / Cw)
    (fun j hj0 hjJ r hr => by
      rw [hbudgetCancel]
      exact hfitLater j hj0 hjJ r hr)
  · intro j hj0 hjJ
    change (∑ r ∈ Finset.Ico (v₀l (j - 1)) (v₁l (j - 1) + 1),
      geometricCellShare (ordinaryLegShare j) r / Cw) ≤ ordinaryLegShare j / Cw
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right
      (sum_geometricCellShare_Ico_le (v₀l (j - 1)) (v₁l (j - 1))
        (ordinaryLegShare j) (by unfold ordinaryLegShare; positivity)) hCwpos.le
  · exact hPb
  · exact hKc
  · exact hbb
  · intro j hj
    unfold replacementCost
    positivity
  · exact fun j hj => (hcosts j hj).1
  · exact fun j hj => (hcosts j hj).2
  · exact haa
  · exact hcell
  · exact hlevel
  · intro j hj
    rw [hc₃Cancel]
    exact mul_nonneg (by unfold ordinaryLegShare; positivity) hc₃
  · exact hrho
  · intro j hj
    rw [hc₃EpsCancel]
    simpa [levelPrimeMassBound] using hscheduleReplacement j hj
  · intro j hj
    rw [hbudgetCancel]
    exact hcollisionFit j hj
  · intro j hj
    calc
      Cw * (2 * (ordinaryLegShare j / Cw) + 2 * (ordinaryLegShare j / Cw)
          + 2 * (ordinaryLegShare j / Cw))
          = 2 * ordinaryLegShare j + 2 * ordinaryLegShare j
              + 2 * ordinaryLegShare j := hthreeCancel _
      _ ≤ (1 : ℝ) / 2 ^ (j + 1) := ordinaryLegShares_fit_honest j
  · exact hNu
  · exact hcovU
  · exact hqcellU
  · exact hq1U
  · exact hqminU
  · exact hLAU
  · exact hLBU
  · exact hwm
  · exact hw0
  · exact hwsup
  · exact hPcU
  · exact hloU
  · exact hhiU
  · exact hdeltaU0
  · simpa [restU] using hdeltaU
  · simpa [restU] using hA0
  · exact hB0
  · intro v hv
    rw [hbudgetCancel]
    exact hfitUCell v hv
  · rw [hbudgetScale]
    rw [show (4 * (H : ℝ) / (A : ℝ)) ^ 2 = Cw from rfl]
    convert hfitUHonest using 1 <;> field_simp
    rw [← Finset.sum_div (Finset.Ico v₀u (v₁u + 1)) kappaU Cw]
    dsimp [restU]
    field_simp

end Tao2015

end MoltResearch
