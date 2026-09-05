import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5InnerBandScheduleSharp

/-!
# Track R VI-9g-3': obstruction to the proposed fixed-epsilon S6 fit

The phase-2 schedule asks the exceptional prime term to satisfy

`2 * DeltaU^2 * (64 * (#cell / Pc^2) * Pc / log Pc) * (1 + Gamma)
  <= (kappa / 2) * bandBudget c3 eps (Delta / A)`.

For a nonempty cell, the left side is bounded below by
`128 * DeltaU^2 / (Pc * log Pc)`.  On the long quotient, the definition of
`cellHalaszSharpBound` itself has the scale-independent floor
`DeltaU >= epsilon' / 8` when `delta0 = epsilon' / (8 * exp 1)`.  Consequently
the proposed fit forces the exact necessary condition

`A <= kappa * c3 * eps^2 * Delta * Pc * log Pc / (32 * epsilon'^2)`.

At fixed `eps`, `epsilon'`, and `Delta`, this is incompatible with the proposed
`Pc <= Q_U = ceil(exp((C / eps^3) * (log A)^(49/50)))`: the right side is
`exp(o(log A))`, while the left side is `A`.  Thus the prime fit cannot hold
for every `A >= A0` required by `SliceMeanSquareA2`.  A valid repair needs an
envelope with a `Delta/A` fallback (or strength depending on `A`); the fixed
top-scale strength in the target Prop permits neither the latter nor the
advertised fixed positive `epsilon'` floor.

With `J ≥ A/2` the forced bound is `A ≤ … · (A/2) · …`, i.e. the fixed condition `ε'² ≤ κc₃ε²·Pc·log Pc/64`.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The long-quotient sharp cell envelope retains the positive smoothing
floor `epsilon' / 8`. -/
theorem cellHalaszSharpBound_ge_eps_div_eight
    (epsilon' : ℝ) (hepsilon' : 0 < epsilon')
    (x0 Aq Bq : ℕ) (hx0 : cellHalaszThreshold ≤ x0)
    (hx0Aq : x0 ≤ Aq) (hAqBq : Aq ≤ Bq)
    (D : ℝ) (hD : 0 ≤ D) (P : Finset ℕ) (rest : List (Finset ℕ)) :
    epsilon' / 8 ≤
      cellHalaszSharpBound x0 D (epsilon' / (8 * Real.exp 1)) Aq Bq P rest := by
  let delta0 : ℝ := epsilon' / (8 * Real.exp 1)
  have hdelta0 : 0 < delta0 := by
    dsimp [delta0]
    positivity
  have hthreshold3 : 3 ≤ cellHalaszThreshold := by
    norm_num [cellHalaszThreshold]
  have hAq3 : 3 ≤ Aq := le_trans hthreshold3 (le_trans hx0 hx0Aq)
  have hBq3 : 3 ≤ Bq := le_trans hAq3 hAqBq
  have hlogAq : 0 < Real.log (Aq : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < Aq))
  have hthreeBq : Real.exp 1 ≤ 3 * (Bq : ℝ) := by
    have h3 : (3 : ℝ) ≤ Bq := by exact_mod_cast hBq3
    linarith [Real.exp_one_lt_d9.le]
  have hhalasz : 0 ≤ halaszBudgetSharp D (3 * (Bq : ℝ)) :=
    halaszBudgetSharp_nonneg D _ hD hthreeBq
  have hpartial : Real.exp 1 * (Bq : ℝ) * delta0 ≤
      sharpPartialBudget D delta0 Aq Bq := by
    unfold sharpPartialBudget
    have hden : 0 < delta0 * Real.log (Aq : ℝ) := by positivity
    have hquot : 0 ≤ 2 * halaszBudgetSharp D (3 * (Bq : ℝ)) /
        (delta0 * Real.log (Aq : ℝ)) := div_nonneg (by positivity) hden.le
    linarith
  have hdenAq : 0 < (((Aq + 1 : ℕ) : ℝ)) := by positivity
  have hsmooth : epsilon' / 8 ≤
      2 * (Real.exp 1 * (Bq : ℝ) * delta0) /
        (((Aq + 1 : ℕ) : ℝ)) := by
    have hcancel : Real.exp 1 * (Bq : ℝ) * delta0 =
        epsilon' * (Bq : ℝ) / 8 := by
      dsimp [delta0]
      field_simp
    rw [hcancel]
    apply (le_div_iff₀ hdenAq).2
    have hcast : ((Aq + 1 : ℕ) : ℝ) ≤ 2 * (Bq : ℝ) := by
      exact_mod_cast (by omega : Aq + 1 ≤ 2 * Bq)
    nlinarith
  have hquotient : epsilon' / 8 ≤
      sharpQuotientCost x0 D delta0 Aq Bq := by
    rw [sharpQuotientCost, if_pos hx0Aq]
    unfold sharpTwistedDirichletCost
    exact hsmooth.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpartial (by norm_num : (0 : ℝ) ≤ 2))
      hdenAq.le)
  have hone : 1 ∈ (Finset.Icc 1 Bq).filter (fun n => n.primeFactors ⊆ P) := by
    simp [show 1 ≤ Bq by omega]
  have hterm0 : ∀ n1 ∈ (Finset.Icc 1 Bq).filter (fun n => n.primeFactors ⊆ P),
      0 ≤ (1 : ℝ) / n1 *
        sharpQuotientCost x0 D delta0 (Aq / n1) (Bq / n1) := by
    intro n1 hn1
    have hab : Aq / n1 ≤ Bq / n1 := Nat.div_le_div_right hAqBq
    exact mul_nonneg (by positivity)
      (sharpQuotientCost_nonneg x0 hx0 D delta0 _ _ hD hdelta0 hab)
  have hram : epsilon' / 8 ≤ sharpRamareCost x0 D delta0 Aq Bq P := by
    unfold sharpRamareCost
    calc
      epsilon' / 8 ≤ (1 : ℝ) / 1 * sharpQuotientCost x0 D delta0 Aq Bq := by
        simpa using hquotient
      _ ≤ ∑ n1 ∈ (Finset.Icc 1 Bq).filter (fun n => n.primeFactors ⊆ P),
          (1 : ℝ) / n1 *
            sharpQuotientCost x0 D delta0 (Aq / n1) (Bq / n1) := by
        simpa using Finset.single_le_sum (fun n1 hn1 => hterm0 n1 hn1) hone
  have hram0 : 0 ≤ sharpRamareCost x0 D delta0 Aq Bq P :=
    le_trans (by positivity : (0 : ℝ) ≤ epsilon' / 8) hram
  unfold cellHalaszSharpBound
  calc
    epsilon' / 8 ≤ sharpRamareCost x0 D delta0 Aq Bq P := hram
    _ ≤ ((2 ^ rest.length : ℕ) : ℝ) *
        sharpRamareCost x0 D delta0 Aq Bq P := by
      exact le_mul_of_one_le_left hram0 (by
        exact_mod_cast Nat.one_le_pow rest.length 2 (by norm_num))

/-- A nonempty prime cell and a nonnegative high-moment correction preserve
the fixed positive floor inside the exceptional prime cost. -/
theorem exceptional_prime_term_ge_fixed_floor
    (epsilon' DeltaU cellCard Pc logPc Gamma : ℝ)
    (hepsilon' : 0 < epsilon') (hDeltaU : epsilon' / 8 ≤ DeltaU)
    (hcellCard : 1 ≤ cellCard) (hPc : 0 < Pc) (hlogPc : 0 < logPc)
    (hGamma : 0 ≤ Gamma) :
    128 * (epsilon' / 8) ^ 2 / (Pc * logPc) ≤
      2 * DeltaU ^ 2 * (64 * (cellCard / Pc ^ 2) * Pc / logPc) *
        (1 + Gamma) := by
  have hfloor0 : 0 ≤ epsilon' / 8 := by positivity
  have hDeltaU0 : 0 ≤ DeltaU := le_trans hfloor0 hDeltaU
  have hsquare : (epsilon' / 8) ^ 2 ≤ DeltaU ^ 2 :=
    pow_le_pow_left₀ hfloor0 hDeltaU 2
  have hcard : DeltaU ^ 2 ≤ DeltaU ^ 2 * cellCard := by
    exact le_mul_of_one_le_right (sq_nonneg DeltaU) hcellCard
  have hgamma : DeltaU ^ 2 * cellCard ≤
      DeltaU ^ 2 * cellCard * (1 + Gamma) := by
    exact le_mul_of_one_le_right (mul_nonneg (sq_nonneg DeltaU) (by linarith)) (by linarith)
  have hnum : 128 * (epsilon' / 8) ^ 2 ≤
      128 * (DeltaU ^ 2 * cellCard * (1 + Gamma)) := by
    exact mul_le_mul_of_nonneg_left (hsquare.trans (hcard.trans hgamma)) (by norm_num)
  have hden : 0 ≤ Pc * logPc := mul_nonneg hPc.le hlogPc.le
  calc
    128 * (epsilon' / 8) ^ 2 / (Pc * logPc)
        ≤ 128 * (DeltaU ^ 2 * cellCard * (1 + Gamma)) / (Pc * logPc) :=
          div_le_div_of_nonneg_right hnum hden
    _ = 2 * DeltaU ^ 2 * (64 * (cellCard / Pc ^ 2) * Pc / logPc) *
        (1 + Gamma) := by
      field_simp
      ring

/-- The fixed floor and the proposed half-budget prime fit force an upper
bound on the ambient scale.  This is the exact failed margin of VI-9g-3'. -/
theorem fixed_floor_prime_fit_forces_scale_bound
    (A Delta Pc logPc kappa c3 eps epsilon' : ℝ)
    (hA : 0 < A) (hPc : 0 < Pc) (hlogPc : 0 < logPc)
    (hepsilon' : 0 < epsilon')
    (hfit : 128 * (epsilon' / 8) ^ 2 / (Pc * logPc) ≤
      (kappa / 2) * bandBudget c3 eps (Delta / A)) :
    A ≤ kappa * c3 * eps ^ 2 * Delta * Pc * logPc /
      (32 * epsilon' ^ 2) := by
  have hdenPc : 0 < Pc * logPc := mul_pos hPc hlogPc
  have hdenA : 0 < 16 * A := by positivity
  have hshapeLeft : 128 * (epsilon' / 8) ^ 2 / (Pc * logPc) =
      2 * epsilon' ^ 2 / (Pc * logPc) := by ring
  have hshapeRight : (kappa / 2) * bandBudget c3 eps (Delta / A) =
      (kappa * c3 * eps ^ 2 * Delta) / (16 * A) := by
    unfold bandBudget
    ring
  rw [hshapeLeft, hshapeRight] at hfit
  have hcross : (2 * epsilon' ^ 2) * (16 * A) ≤
      (kappa * c3 * eps ^ 2 * Delta) * (Pc * logPc) :=
    (div_le_div_iff₀ hdenPc hdenA).mp hfit
  apply (le_div_iff₀ (by positivity : 0 < 32 * epsilon' ^ 2)).2
  nlinarith

/-- Combining the two preceding facts gives the scale obstruction directly
from the phase-2 `hfitPri` expression. -/
theorem sharp_exceptional_prime_fit_forces_scale_bound
    (A Delta DeltaU cellCard Pc logPc Gamma kappa c3 eps epsilon' : ℝ)
    (hA : 0 < A) (hPc : 0 < Pc) (hlogPc : 0 < logPc)
    (hepsilon' : 0 < epsilon') (hDeltaU : epsilon' / 8 ≤ DeltaU)
    (hcellCard : 1 ≤ cellCard) (hGamma : 0 ≤ Gamma)
    (hfitPri :
      2 * DeltaU ^ 2 * (64 * (cellCard / Pc ^ 2) * Pc / logPc) *
          (1 + Gamma)
        ≤ (kappa / 2) * bandBudget c3 eps (Delta / A)) :
    A ≤ kappa * c3 * eps ^ 2 * Delta * Pc * logPc /
      (32 * epsilon' ^ 2) := by
  apply fixed_floor_prime_fit_forces_scale_bound A Delta Pc logPc kappa c3 eps epsilon'
    hA hPc hlogPc hepsilon'
  exact (exceptional_prime_term_ge_fixed_floor epsilon' DeltaU cellCard Pc logPc Gamma
    hepsilon' hDeltaU hcellCard hPc hlogPc hGamma).trans hfitPri

/-- Pointwise contradiction form of the failed margin.  Any parameter choice
whose ambient scale exceeds the forced upper bound cannot discharge the
phase-2 exceptional prime fit. -/
theorem not_sharp_exceptional_prime_fit_of_scale_growth
    (A Delta DeltaU cellCard Pc logPc Gamma kappa c3 eps epsilon' : ℝ)
    (hA : 0 < A) (hPc : 0 < Pc) (hlogPc : 0 < logPc)
    (hepsilon' : 0 < epsilon') (hDeltaU : epsilon' / 8 ≤ DeltaU)
    (hcellCard : 1 ≤ cellCard) (hGamma : 0 ≤ Gamma)
    (hgrowth : kappa * c3 * eps ^ 2 * Delta * Pc * logPc <
      32 * epsilon' ^ 2 * A) :
    ¬ (2 * DeltaU ^ 2 * (64 * (cellCard / Pc ^ 2) * Pc / logPc) *
          (1 + Gamma)
        ≤ (kappa / 2) * bandBudget c3 eps (Delta / A)) := by
  intro hfitPri
  have hforced := sharp_exceptional_prime_fit_forces_scale_bound
    A Delta DeltaU cellCard Pc logPc Gamma kappa c3 eps epsilon'
    hA hPc hlogPc hepsilon' hDeltaU hcellCard hGamma hfitPri
  have hden : 0 < 32 * epsilon' ^ 2 := by positivity
  have := (le_div_iff₀ hden).mp hforced
  nlinarith

end Tao2015

end MoltResearch
