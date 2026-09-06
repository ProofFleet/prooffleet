import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2LevelZeroMain

/-!
# Track R A2-V'-13: exceptional cells at a short budget

The shifted capstone gives the exceptional level one half of the band.  This
file records the three fixed aggregate fits used inside that half and expands
the actual-cost shares back to the exact cell expression expected by the
capstone.
-/

namespace MoltResearch

namespace Tao2015

open Finset MeasureTheory ExpSums

/-- The integer-cell envelope fits its `1/64` allocation at relative scale
`rho0`. -/
theorem exceptional_integer_aggregate_fit_ratio
    (I : Finset ℕ) (A Q : ℕ) (q : ℕ → ℕ)
    (Bq coeffMass : ℕ → ℝ) (V0 Kcov T L c3 eps rho0 : ℝ)
    (hA : 0 < A) (hK : 0 ≤ Kcov) (hL : 0 ≤ L)
    (hq : ∀ v ∈ I, 1 ≤ q v)
    (hqQ : ∀ v ∈ I, q v ≤ Q)
    (h2qA : ∀ v ∈ I, 2 * q v ≤ A)
    (hBq : ∀ v ∈ I, Bq v ≤ 2 * ((A / q v + 1 : ℕ) : ℝ))
    (hcoeff0 : ∀ v ∈ I, 0 ≤ coeffMass v)
    (hcoeff : ∀ v ∈ I,
      coeffMass v ≤ 2 / (((A / q v + 1 : ℕ) : ℝ)))
    (hfit : 1024 * (I.card : ℝ) ^ 2 * V0 ^ 2 * L *
        (1 + Kcov * Real.sqrt T * (Q : ℝ) / (A : ℝ)) ≤
      c3 * eps ^ 2 * rho0 / 64) :
    2 * (I.card : ℝ) *
        (∑ v ∈ I,
          exceptionalIntegerCellCost V0 (Bq v) Kcov T L (coeffMass v)) ≤
      c3 * eps ^ 2 * rho0 / 64 :=
  (exceptionalIntegerAggregate_le I A Q q Bq coeffMass V0 Kcov T L
    hA hK hL hq hqQ h2qA hBq hcoeff0 hcoeff).trans hfit

/-- The Brun--Titchmarsh prime-cell aggregate fits its `1/64` allocation.
The coefficient `32768 = 64 * 512` is independent of the ladder height. -/
theorem exceptional_prime_aggregate_fit_ratio
    (I : Finset ℕ) (Y : ℕ → Finset ℕ) (Pc : ℕ → ℕ)
    (hPc : ∀ v ∈ I, 2 ≤ Pc v) (hlo : ∀ v ∈ I, ∀ p ∈ Y v, Pc v < p)
    (g : ℕ → ℂ) (hg : ∀ p, ‖g p‖ ≤ 1)
    (Delta Gamma : ℕ → ℝ) (d L E N R Ccells c3 eps rho0 : ℝ)
    (hL : 0 < L) (hE : 0 ≤ E)
    (hDelta0 : ∀ v ∈ I, 0 ≤ Delta v)
    (hDelta : ∀ v ∈ I, Delta v ≤ d)
    (hGamma0 : ∀ v ∈ I, 0 ≤ Gamma v)
    (hGamma : ∀ v ∈ I, Gamma v ≤ 1)
    (hlog : ∀ v ∈ I, L ≤ Real.log (Pc v : ℝ))
    (hmass : ∑ v ∈ I, ∑ p ∈ Y v, (1 : ℝ) / p ≤ E)
    (hcard : (I.card : ℝ) ≤ Ccells * N * R * L)
    (hfixed : 32768 * Ccells * N * R * d ^ 2 * E ≤
      c3 * eps ^ 2 * rho0) :
    2 * (I.card : ℝ) *
        (∑ v ∈ I, exceptionalPrimeCellCost Y Pc g Delta Gamma v) ≤
      c3 * eps ^ 2 * rho0 / 64 := by
  have hagg := exceptional_prime_aggregate_le I Y Pc hPc hlo g hg Delta Gamma
    d L E N R Ccells hL hE hDelta0 hDelta hGamma0 hGamma hlog hmass hcard
  calc
    2 * (I.card : ℝ) *
        (∑ v ∈ I, exceptionalPrimeCellCost Y Pc g Delta Gamma v) ≤
      512 * Ccells * N * R * d ^ 2 * E := by
        simpa [exceptionalPrimeCellCost] using hagg
    _ = (32768 * Ccells * N * R * d ^ 2 * E) / 64 := by ring
    _ ≤ c3 * eps ^ 2 * rho0 / 64 := by gcongr

/-- The combined wide exceptional error fits its `1/32` allocation. -/
theorem exceptional_wide_cost_fit_ratio
    (A Nu : ℕ) (P : Finset ℕ) (T E E2 c3 eps rho0 : ℝ)
    (hA : 0 < A) (hNu : 0 < Nu) (hTA : T ≤ A)
    (hmass : ∑ p ∈ P, (1 : ℝ) / p ≤ E)
    (hmass2 : ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2 ≤ E2)
    (hfit : 1152 * Real.exp Real.pi *
          (E / (Nu : ℝ) + (P.card : ℝ) / A) +
        80 * Real.exp Real.pi *
          (2 * E2 + (P.card : ℝ) / A) ≤ c3 * eps ^ 2 * rho0 / 32) :
    2 * (2 * replacementEnergyBoundWide A P Nu T +
        2 * (4 * collisionEnergyBoundWide A P T)) ≤
      c3 * eps ^ 2 * rho0 / 32 :=
  (exceptionalWideCost_le A Nu P T E E2 hA hNu hTA hmass hmass2).trans hfit

/-- Expanding the actual-cost construction supplies both the capstone's
pointwise cell fit and its exceptional half-band aggregate. -/
theorem exceptional_exact_cell_schedule_of_ratio_fits
    (I : Finset ℕ) (Bq coeffMass : ℕ → ℝ)
    (Y : ℕ → Finset ℕ) (Pc : ℕ → ℕ) (g : ℕ → ℂ)
    (Delta Gamma : ℕ → ℝ) (V0 Kcov T L wide c3 eps rho0 rho : ℝ)
    (hc3 : 0 < c3) (heps : 0 < eps) (hrho0 : 0 < rho0)
    (hratio : rho0 ≤ rho)
    (hint : 2 * (I.card : ℝ) *
        (∑ v ∈ I,
          exceptionalIntegerCellCost V0 (Bq v) Kcov T L (coeffMass v)) ≤
      c3 * eps ^ 2 * rho0 / 64)
    (hprime : 2 * (I.card : ℝ) *
        (∑ v ∈ I, exceptionalPrimeCellCost Y Pc g Delta Gamma v) ≤
      c3 * eps ^ 2 * rho0 / 64)
    (hwide : wide ≤ c3 * eps ^ 2 * rho0 / 32) :
    let cost := fun v =>
      exceptionalIntegerCellCost V0 (Bq v) Kcov T L (coeffMass v) +
        exceptionalPrimeCellCost Y Pc g Delta Gamma v
    let kappa := fun v =>
      exceptionalCellKappa (cost v) (bandBudget c3 eps rho)
    (∀ v ∈ I,
      2 * (V0 ^ 2 * (64 * (Bq v + Kcov * Real.sqrt T) * L * coeffMass v) +
          Delta v ^ 2 *
            ((64 * (∑ p ∈ Y v, ‖g p‖ ^ 2 / (p : ℝ) ^ 2) *
              (Pc v : ℝ) / Real.log (Pc v : ℝ)) * (1 + Gamma v))) ≤
        kappa v * bandBudget c3 eps rho) ∧
      2 * (I.card : ℝ) * (∑ v ∈ I, kappa v) * bandBudget c3 eps rho + wide ≤
        (1 / 2) * bandBudget c3 eps rho := by
  dsimp only
  have hs := exceptional_actual_cost_schedule_of_ratio_fits I
    (fun v => exceptionalIntegerCellCost V0 (Bq v) Kcov T L (coeffMass v))
    (fun v => exceptionalPrimeCellCost Y Pc g Delta Gamma v)
    wide c3 eps rho0 rho hc3 heps hrho0 hratio hint hprime hwide
  constructor
  · intro v hv
    convert hs.1 v using 1 <;>
      simp only [exceptionalIntegerCellCost, exceptionalPrimeCellCost] <;> ring
  · convert hs.2 using 1 <;> ring

end Tao2015

end MoltResearch
