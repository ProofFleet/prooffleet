import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2Transfer

/-!
# Track R A2-V'-5: budget bookkeeping for short relative slices

The ladder estimates were first packaged for slices of relative length at
least `1/3`.  The final A2 argument partitions a long slice into pieces whose
relative length has a smaller, but fixed, positive lower bound.  This file
records the corresponding budget lifts without changing the earlier L3
interfaces or their analytic estimates.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- A lower bound for the relative slice length gives the matching lower
bound for the band budget. -/
theorem bandBudget_lower_of_ratio
    (c3 eps rho0 rho : ℝ) (hc3 : 0 ≤ c3) (hratio : rho0 ≤ rho) :
    c3 * eps ^ 2 * rho0 / 8 ≤ bandBudget c3 eps rho := by
  have hscale : 0 ≤ c3 * eps ^ 2 / 8 := by positivity
  unfold bandBudget
  calc
    c3 * eps ^ 2 * rho0 / 8 = (c3 * eps ^ 2 / 8) * rho0 := by ring
    _ ≤ (c3 * eps ^ 2 / 8) * rho :=
      mul_le_mul_of_nonneg_left hratio hscale
    _ = c3 * eps ^ 2 * rho / 8 := by ring

/-- The later-level finite-cell estimate with an arbitrary fixed lower bound
for the relative slice length. -/
theorem ordinaryLadder_per_previous_cell_fit_of_ratio
    (Icur Iprev : Finset ℕ) (j : ℕ)
    (Ncur Nprev r Pmom Pcur : ℕ) (t : ℕ → ℕ) (u : ℕ → ℝ)
    (Qprev tau alpha beta mass L c3 eps rho0 rho : ℝ)
    (hNcur : 0 < Ncur) (hNprev : 0 < Nprev) (hPmom : 2 ≤ Pmom)
    (hPcur : 1 ≤ Pcur)
    (hPt : ∀ v ∈ Icur, Pcur ≤ t v)
    (hPmomQ : (Pmom : ℝ) ≤ Qprev)
    (htop : ∀ v ∈ Icur,
      (t v : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (Ncur : ℝ))))
    (hexpPrev : Real.exp ((r : ℝ) / (2 * (Nprev : ℝ))) ≤
      2 * (Pmom : ℝ))
    (htau0 : 0 ≤ tau) (htau : tau ≤ 1)
    (hx : ∀ v ∈ Icur, 1 ≤ (t v : ℝ) * tau)
    (halpha : 0 ≤ alpha) (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (1 : ℝ) / 5) (hgap : 0 ≤ alpha - beta)
    (hmass0 : 0 ≤ mass) (hmass : mass ≤ 1)
    (hu0 : ∀ v ∈ Icur, 0 ≤ u v) (hu : ∀ v ∈ Icur, u v ≤ 1)
    (hL : 1 ≤ L)
    (hellL : ∀ v ∈ Icur,
      (ordinaryBorrowMoment Pmom ((t v : ℝ) * tau) : ℝ) ≤ L)
    (hfar : (2 * Real.log L + 3) / Real.log Pmom ≤ alpha - beta)
    (hc3 : 0 ≤ c3) (hratio : rho0 ≤ rho)
    (hnumerology :
      (Icur.card : ℝ) ^ 2 *
          ordinaryLadderCellEnvelope Ncur Pcur Qprev tau alpha beta L ≤
        (ordinaryLegShare j / (Iprev.card : ℝ)) *
          (c3 * eps ^ 2 * rho0 / 8)) :
    (Icur.card : ℝ) *
        ∑ v ∈ Icur,
          ordinaryLadderCellRaw Ncur Nprev v r Pmom alpha beta mass (u v)
            ((t v : ℝ) * tau) ≤
      (ordinaryLegShare j / (Iprev.card : ℝ)) *
        bandBudget c3 eps rho := by
  have hsum := sum_ordinaryLadderCellRaw_le Icur Ncur Nprev r Pmom Pcur t u
    Qprev tau alpha beta mass L hNcur hNprev hPmom hPcur hPt hPmomQ htop
    hexpPrev htau0 htau hx halpha hbeta0 hbeta hgap hmass0 hmass hu0 hu hL
    hellL hfar
  have hbudget := bandBudget_lower_of_ratio c3 eps rho0 rho hc3 hratio
  have hshare0 : 0 ≤ ordinaryLegShare j / (Iprev.card : ℝ) := by
    unfold ordinaryLegShare
    positivity
  calc
    (Icur.card : ℝ) *
          ∑ v ∈ Icur,
            ordinaryLadderCellRaw Ncur Nprev v r Pmom alpha beta mass (u v)
              ((t v : ℝ) * tau) ≤
        (Icur.card : ℝ) * ((Icur.card : ℝ) *
          ordinaryLadderCellEnvelope Ncur Pcur Qprev tau alpha beta L) := by
            exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (Icur.card : ℝ) ^ 2 *
          ordinaryLadderCellEnvelope Ncur Pcur Qprev tau alpha beta L := by ring
    _ ≤ (ordinaryLegShare j / (Iprev.card : ℝ)) *
          (c3 * eps ^ 2 * rho0 / 8) := hnumerology
    _ ≤ (ordinaryLegShare j / (Iprev.card : ℝ)) *
        bandBudget c3 eps rho :=
      mul_le_mul_of_nonneg_left hbudget hshare0

/-- The wide replacement leg with an arbitrary fixed lower bound for the
relative slice length. -/
theorem replacementEnergyBoundWide_fit_of_mass_card_ratio
    (A N : ℕ) (P : Finset ℕ) (T E kappa c3 eps rho0 rho : ℝ)
    (hA : 2 ≤ A) (hN : 0 < N) (hTA : T ≤ A)
    (hmass : ∑ p ∈ P, (1 : ℝ) / p ≤ E)
    (hfit : 64 * 9 * Real.exp Real.pi *
        (E / (N : ℝ) + (P.card : ℝ) / A) ≤
      kappa * (c3 * eps ^ 2 * rho0 / 8))
    (hc3 : 0 ≤ c3) (hkappa : 0 ≤ kappa) (hratio : rho0 ≤ rho) :
    2 * replacementEnergyBoundWide A P N T ≤
      kappa * bandBudget c3 eps rho := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hratioTA : T / (A : ℝ) ≤ 1 :=
    (div_le_one hA0).2 (by exact_mod_cast hTA)
  have hinner0 : 0 ≤
      (∑ p ∈ P, (1 : ℝ) / p) / (N : ℝ) + (P.card : ℝ) / A := by
    positivity
  have hEinner :
      (∑ p ∈ P, (1 : ℝ) / p) / (N : ℝ) + (P.card : ℝ) / A ≤
        E / (N : ℝ) + (P.card : ℝ) / A := by gcongr
  have hraw : 2 * replacementEnergyBoundWide A P N T ≤
      64 * 9 * Real.exp Real.pi * (E / (N : ℝ) + (P.card : ℝ) / A) := by
    unfold replacementEnergyBoundWide
    calc
      2 * (Real.exp Real.pi * (T / (A : ℝ) + 8) *
          (32 * ((∑ p ∈ P, (1 : ℝ) / p) / (N : ℝ) +
            (P.card : ℝ) / (A : ℝ)))) =
        64 * Real.exp Real.pi * (T / (A : ℝ) + 8) *
          ((∑ p ∈ P, (1 : ℝ) / p) / (N : ℝ) +
            (P.card : ℝ) / A) := by ring
      _ ≤ 64 * Real.exp Real.pi * 9 *
          ((∑ p ∈ P, (1 : ℝ) / p) / (N : ℝ) +
            (P.card : ℝ) / A) := by gcongr; linarith
      _ = 64 * 9 * Real.exp Real.pi *
          ((∑ p ∈ P, (1 : ℝ) / p) / (N : ℝ) +
            (P.card : ℝ) / A) := by ring
      _ ≤ _ := by gcongr
  have hbudget := bandBudget_lower_of_ratio c3 eps rho0 rho hc3 hratio
  calc
    2 * replacementEnergyBoundWide A P N T ≤ _ := hraw
    _ ≤ kappa * (c3 * eps ^ 2 * rho0 / 8) := hfit
    _ ≤ kappa * bandBudget c3 eps rho :=
      mul_le_mul_of_nonneg_left hbudget hkappa

/-- The wide collision leg with an arbitrary fixed lower bound for the
relative slice length. -/
theorem collisionEnergyBoundWide_fit_of_mass_card_ratio
    (A : ℕ) (P : Finset ℕ) (T E2 kappa c3 eps rho0 rho : ℝ)
    (hA : 2 ≤ A) (hTA : T ≤ A)
    (hmass2 : ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2 ≤ E2)
    (hfit : 40 * Real.exp Real.pi *
        (2 * E2 + (P.card : ℝ) / A) ≤
      kappa * (c3 * eps ^ 2 * rho0 / 8))
    (hc3 : 0 ≤ c3) (hkappa : 0 ≤ kappa) (hratio : rho0 ≤ rho) :
    8 * collisionEnergyBoundWide A P T ≤
      kappa * bandBudget c3 eps rho := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hratioTA : T / (A : ℝ) ≤ 1 :=
    (div_le_one hA0).2 (by exact_mod_cast hTA)
  have hinner0 : 0 ≤
      2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) +
        (P.card : ℝ) / A := by positivity
  have hEinner :
      2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) +
          (P.card : ℝ) / A ≤
        2 * E2 + (P.card : ℝ) / A := by gcongr
  have hraw : 8 * collisionEnergyBoundWide A P T ≤
      40 * Real.exp Real.pi * (2 * E2 + (P.card : ℝ) / A) := by
    unfold collisionEnergyBoundWide
    calc
      8 * (Real.exp Real.pi * (T / (A : ℝ) + 4) *
          (2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) +
            (P.card : ℝ) / (A : ℝ))) =
        8 * Real.exp Real.pi * (T / (A : ℝ) + 4) *
          (2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) +
            (P.card : ℝ) / A) := by ring
      _ ≤ 8 * Real.exp Real.pi * 5 *
          (2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) +
            (P.card : ℝ) / A) := by gcongr; linarith
      _ = 40 * Real.exp Real.pi *
          (2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) +
            (P.card : ℝ) / A) := by ring
      _ ≤ _ := by gcongr
  have hbudget := bandBudget_lower_of_ratio c3 eps rho0 rho hc3 hratio
  calc
    8 * collisionEnergyBoundWide A P T ≤ _ := hraw
    _ ≤ kappa * (c3 * eps ^ 2 * rho0 / 8) := hfit
    _ ≤ kappa * bandBudget c3 eps rho :=
      mul_le_mul_of_nonneg_left hbudget hkappa

/-- Splitting `c3*eps^2*rho0/16` as `1/64 + 1/64 + 1/32`
closes the actual-cost exceptional schedule for any `rho0 ≤ rho`. -/
theorem exceptional_actual_cost_schedule_of_ratio_fits
    (I : Finset ℕ) (integerCost primeCost : ℕ → ℝ)
    (wide c3 eps rho0 rho : ℝ) (hc3 : 0 < c3) (heps : 0 < eps)
    (hrho0 : 0 < rho0) (hratio : rho0 ≤ rho)
    (hint : 2 * (I.card : ℝ) * (∑ v ∈ I, integerCost v) ≤
      c3 * eps ^ 2 * rho0 / 64)
    (hprime : 2 * (I.card : ℝ) * (∑ v ∈ I, primeCost v) ≤
      c3 * eps ^ 2 * rho0 / 64)
    (hwide : wide ≤ c3 * eps ^ 2 * rho0 / 32) :
    let cost := fun v => integerCost v + primeCost v
    (∀ v, cost v ≤ exceptionalCellKappa
        (cost v) (bandBudget c3 eps rho) * bandBudget c3 eps rho) ∧
      2 * (I.card : ℝ) *
          (∑ v ∈ I, exceptionalCellKappa
            (cost v) (bandBudget c3 eps rho)) * bandBudget c3 eps rho + wide ≤
        bandBudget c3 eps rho / 2 := by
  dsimp only
  have hrho : 0 < rho := lt_of_lt_of_le hrho0 hratio
  have hbudget : bandBudget c3 eps rho ≠ 0 := by
    unfold bandBudget
    positivity
  apply exceptional_actual_cost_schedule I
    (fun v => integerCost v + primeCost v) (bandBudget c3 eps rho) wide hbudget
  have hsum :
      2 * (I.card : ℝ) *
          ((∑ v ∈ I, integerCost v) + (∑ v ∈ I, primeCost v)) + wide ≤
        c3 * eps ^ 2 * rho0 / 16 := by
    linarith
  calc
    2 * (I.card : ℝ) *
        (∑ x ∈ I, (integerCost x + primeCost x)) + wide =
        2 * (I.card : ℝ) *
          ((∑ x ∈ I, integerCost x) + (∑ x ∈ I, primeCost x)) + wide := by
      rw [Finset.sum_add_distrib]
    _ ≤ c3 * eps ^ 2 * rho0 / 16 := hsum
    _ ≤ c3 * eps ^ 2 * rho / 16 := by
      have hscale : 0 ≤ c3 * eps ^ 2 / 16 := by positivity
      calc
        c3 * eps ^ 2 * rho0 / 16 = (c3 * eps ^ 2 / 16) * rho0 := by ring
        _ ≤ (c3 * eps ^ 2 / 16) * rho :=
          mul_le_mul_of_nonneg_left hratio hscale
        _ = c3 * eps ^ 2 * rho / 16 := by ring
    _ = bandBudget c3 eps rho / 2 := by
      unfold bandBudget
      ring

end Tao2015

end MoltResearch
