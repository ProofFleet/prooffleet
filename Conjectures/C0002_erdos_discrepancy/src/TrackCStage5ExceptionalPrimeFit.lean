import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5ExceptionalIntegerFit
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5ExceptionalSharp
import MoltResearch.Discrepancy.EulerProductSharp

/-!
# Track R L3-5: the exceptional prime-part fit

The exceptional cell shares are their actual costs divided by the band
budget.  Brun--Titchmarsh then lets the prime-cell masses be summed before
the outer Cauchy factor is paid.  The resulting fit is the fixed condition

`98304 * Ccells * Nu * ratio * d^2 * E ≤ c3 * eps^2`,

with no dependence on the number of ordinary ladder levels.  The constant
`98304 = 192 * 512` reserves `1/192` of `c3*eps^2` for this leg.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-! ## A sharper fixed Euler-product constant -/

/-- The sharp cell bound with the smooth harmonic mass estimated by one
linear reciprocal-prime mass plus its quadratic correction. -/
theorem cellHalaszSharpBound_le_explicit_sharpMass (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∃ (D0 : ℝ) (xMin : ℕ), 1 ≤ D0 ∧ 10 ^ 16 ≤ xMin ∧
      ∀ D : ℝ, D0 ≤ D → ∀ x0 : ℕ, xMin ≤ x0 →
      ∀ Aq Bq : ℕ, 1 ≤ Aq → Aq ≤ Bq → Bq ≤ 2 * Aq + 1 →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ∀ s : ℝ, 0 < s → s < 1 →
        (∀ p ∈ P, (p : ℝ) ^ (-(1 - s)) ≤ 1 / 2) →
      ∀ rest : List (Finset ℕ),
        cellHalaszSharpBound x0 D (epsilon / (8 * Real.exp 1)) Aq Bq P rest
          ≤ ((2 ^ rest.length : ℕ) : ℝ) *
            (2 * epsilon *
                Real.exp ((∑ p ∈ P, (1 : ℝ) / p) +
                  2 * ∑ p ∈ P, ((1 : ℝ) / p) ^ 2) +
              (Real.log (Bq : ℝ) + 1) *
                (((Aq : ℝ) / x0) ^ (-s) *
                  Real.exp (2 * ∑ p ∈ P, (p : ℝ) ^ (-(1 - s))))) := by
  obtain ⟨D0, xMin, hD0, hxMin, hram⟩ := sharpRamareCost_le_eps epsilon hepsilon
  refine ⟨D0, xMin, hD0, hxMin, ?_⟩
  intro D hD x0 hx0 Aq Bq hAq hAB hB P hP s hs0 hs1 hhalf rest
  unfold cellHalaszSharpBound
  have hpow : (0 : ℝ) ≤ ((2 ^ rest.length : ℕ) : ℝ) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hpow
  have hram' := hram D hD x0 hx0 Aq Bq hAq hAB hB P hP s hs0 hs1
  have hmass := pSmoothHarmonicMass_le_exp_primeMass_sq Bq P hP
  have hprod := prod_inv_one_sub_le_exp P
    (fun p => (p : ℝ) ^ (-(1 - s)))
    (fun p hp => by positivity) hhalf
  have hlogB : 0 ≤ Real.log (Bq : ℝ) + 1 := by
    have hBq1 : (1 : ℝ) ≤ Bq := by exact_mod_cast le_trans hAq hAB
    linarith [Real.log_nonneg hBq1]
  have hy0 : (0 : ℝ) ≤ ((Aq : ℝ) / x0) ^ (-s) := by positivity
  have htail :
      (Real.log (Bq : ℝ) + 1) *
          (((Aq : ℝ) / x0) ^ (-s) *
            ∏ p ∈ P, (1 - (p : ℝ) ^ (-(1 - s)))⁻¹) ≤
        (Real.log (Bq : ℝ) + 1) *
          (((Aq : ℝ) / x0) ^ (-s) *
            Real.exp (2 * ∑ p ∈ P, (p : ℝ) ^ (-(1 - s)))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod hy0) hlogB
  have hmain :
      2 * epsilon * pSmoothHarmonicMass Bq P ≤
        2 * epsilon *
          Real.exp ((∑ p ∈ P, (1 : ℝ) / p) +
            2 * ∑ p ∈ P, ((1 : ℝ) / p) ^ 2) :=
    mul_le_mul_of_nonneg_left hmass (by positivity)
  linarith

/-- Mertens mass `log NU + 12` and square mass at most `1/2` give the fixed
smooth-number constant `exp(13) * NU`. -/
theorem pSmoothHarmonicMass_le_exp_thirteen_mul
    (B : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (NU : ℝ) (hNU : 0 < NU)
    (hmass : ∑ p ∈ P, (1 : ℝ) / p ≤ Real.log NU + 12)
    (hsq : ∑ p ∈ P, ((1 : ℝ) / p) ^ 2 ≤ 1 / 2) :
    pSmoothHarmonicMass B P ≤ Real.exp 13 * NU := by
  calc
    pSmoothHarmonicMass B P ≤
        Real.exp ((∑ p ∈ P, (1 : ℝ) / p) +
          2 * ∑ p ∈ P, ((1 : ℝ) / p) ^ 2) :=
      pSmoothHarmonicMass_le_exp_primeMass_sq B P hP
    _ ≤ Real.exp (Real.log NU + 13) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = Real.exp 13 * NU := by
      rw [Real.exp_add, Real.exp_log hNU]
      ring

/-- With one base level in `rest`, the sharp cell cost has the fixed main
term `4*epsilon*exp(13)*NU`; the Rankin expression is left as a tail input. -/
theorem cellHalaszSharpBound_le_fixedEnvelope (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∃ (D0 : ℝ) (xMin : ℕ), 1 ≤ D0 ∧ 10 ^ 16 ≤ xMin ∧
      ∀ D : ℝ, D0 ≤ D → ∀ x0 : ℕ, xMin ≤ x0 →
      ∀ Aq Bq : ℕ, 1 ≤ Aq → Aq ≤ Bq → Bq ≤ 2 * Aq + 1 →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ∀ s : ℝ, 0 < s → s < 1 →
        (∀ p ∈ P, (p : ℝ) ^ (-(1 - s)) ≤ 1 / 2) →
      ∀ base : Finset ℕ, ∀ NU tail : ℝ, 0 < NU →
        (∑ p ∈ P, (1 : ℝ) / p ≤ Real.log NU + 12) →
        (∑ p ∈ P, ((1 : ℝ) / p) ^ 2 ≤ 1 / 2) →
        ((Real.log (Bq : ℝ) + 1) *
            (((Aq : ℝ) / x0) ^ (-s) *
              Real.exp (2 * ∑ p ∈ P, (p : ℝ) ^ (-(1 - s)))) ≤ tail) →
        cellHalaszSharpBound x0 D (epsilon / (8 * Real.exp 1)) Aq Bq P [base]
          ≤ 2 * (2 * epsilon * Real.exp 13 * NU + tail) := by
  obtain ⟨D0, xMin, hD0, hxMin, hsharp⟩ :=
    cellHalaszSharpBound_le_explicit_sharpMass epsilon hepsilon
  refine ⟨D0, xMin, hD0, hxMin, ?_⟩
  intro D hD x0 hx0 Aq Bq hAq hAB hB P hP s hs0 hs1 hhalf
    base NU tail hNU hmass hsq htail
  have hs := hsharp D hD x0 hx0 Aq Bq hAq hAB hB P hP s hs0 hs1 hhalf [base]
  have hexp :
      Real.exp ((∑ p ∈ P, (1 : ℝ) / p) +
          2 * ∑ p ∈ P, ((1 : ℝ) / p) ^ 2) ≤
        Real.exp 13 * NU := by
    calc
      _ ≤ Real.exp (Real.log NU + 13) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = Real.exp 13 * NU := by
        rw [Real.exp_add, Real.exp_log hNU]
        ring
  have hmain :
      2 * epsilon *
          Real.exp ((∑ p ∈ P, (1 : ℝ) / p) +
            2 * ∑ p ∈ P, ((1 : ℝ) / p) ^ 2) ≤
        2 * epsilon * Real.exp 13 * NU := by
    calc
      _ ≤ (2 * epsilon) * (Real.exp 13 * NU) :=
        mul_le_mul_of_nonneg_left hexp (by linarith : 0 ≤ 2 * epsilon)
      _ = _ := by ring
  norm_num only [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reducePow, Nat.cast_ofNat] at hs
  exact hs.trans (by nlinarith)

/-! ## Gamma and the fixed aggregate -/

/-- The exponentially damped high-moment correction occurring in the sharp
exceptional cell capstone. -/
noncomputable def exceptionalPrimeGamma (cost Pc T : ℝ) : ℝ :=
  cost * Real.exp (-(Real.log Pc /
    (Real.log (2 * T)) ^ (3 / 4 : ℝ))) * (Real.log (2 * T)) ^ 2

theorem exceptionalPrimeGamma_nonneg
    (cost Pc T : ℝ) (hcost : 0 ≤ cost) :
    0 ≤ exceptionalPrimeGamma cost Pc T := by
  unfold exceptionalPrimeGamma
  positivity

/-- It is enough for the undamped moment cost times `log(2T)^2` to fit below
the reciprocal damping exponential. -/
theorem exceptionalPrimeGamma_le_one
    (cost Pc T : ℝ)
    (hfit : cost * (Real.log (2 * T)) ^ 2 ≤
      Real.exp (Real.log Pc / (Real.log (2 * T)) ^ (3 / 4 : ℝ))) :
    exceptionalPrimeGamma cost Pc T ≤ 1 := by
  let x := Real.log Pc / (Real.log (2 * T)) ^ (3 / 4 : ℝ)
  calc
    exceptionalPrimeGamma cost Pc T = Real.exp (-x) *
        (cost * (Real.log (2 * T)) ^ 2) := by
      unfold exceptionalPrimeGamma x
      ring
    _ ≤ Real.exp (-x) * Real.exp x := by
      exact mul_le_mul_of_nonneg_left hfit (Real.exp_nonneg _)
    _ = 1 := by
      rw [← Real.exp_add]
      simp

/-- The prime-dependent part of one exceptional cell cost. -/
noncomputable def exceptionalPrimeCellCost
    (Y : ℕ → Finset ℕ) (Pc : ℕ → ℕ) (g : ℕ → ℂ)
    (Delta Gamma : ℕ → ℝ) (v : ℕ) : ℝ :=
  2 * Delta v ^ 2 *
    ((64 * (∑ p ∈ Y v, ‖g p‖ ^ 2 / (p : ℝ) ^ 2) *
        (Pc v : ℝ) / Real.log (Pc v : ℝ)) * (1 + Gamma v))

/-- The aggregate prime fit consumes `c3*eps^2/192` under one fixed
inequality.  In particular, it is independent of the ladder height `J`. -/
theorem exceptional_prime_aggregate_fit_fixed
    (I : Finset ℕ) (Y : ℕ → Finset ℕ) (Pc : ℕ → ℕ)
    (hPc : ∀ v ∈ I, 2 ≤ Pc v) (hlo : ∀ v ∈ I, ∀ p ∈ Y v, Pc v < p)
    (g : ℕ → ℂ) (hg : ∀ p, ‖g p‖ ≤ 1)
    (Delta Gamma : ℕ → ℝ) (d L E N R Ccells c3 eps : ℝ)
    (hL : 0 < L) (hE : 0 ≤ E)
    (hDelta0 : ∀ v ∈ I, 0 ≤ Delta v)
    (hDelta : ∀ v ∈ I, Delta v ≤ d)
    (hGamma0 : ∀ v ∈ I, 0 ≤ Gamma v)
    (hGamma : ∀ v ∈ I, Gamma v ≤ 1)
    (hlog : ∀ v ∈ I, L ≤ Real.log (Pc v : ℝ))
    (hmass : ∑ v ∈ I, ∑ p ∈ Y v, (1 : ℝ) / p ≤ E)
    (hcard : (I.card : ℝ) ≤ Ccells * N * R * L)
    (hfixed : 98304 * Ccells * N * R * d ^ 2 * E ≤ c3 * eps ^ 2) :
    2 * (I.card : ℝ) *
        (∑ v ∈ I, exceptionalPrimeCellCost Y Pc g Delta Gamma v) ≤
      c3 * eps ^ 2 / 192 := by
  have hagg := exceptional_prime_aggregate_le I Y Pc hPc hlo g hg Delta Gamma
    d L E N R Ccells hL hE hDelta0 hDelta hGamma0 hGamma hlog hmass hcard
  calc
    2 * (I.card : ℝ) *
        (∑ v ∈ I, exceptionalPrimeCellCost Y Pc g Delta Gamma v) ≤
      512 * Ccells * N * R * d ^ 2 * E := by
        simpa [exceptionalPrimeCellCost] using hagg
    _ = (98304 * Ccells * N * R * d ^ 2 * E) / 192 := by ring
    _ ≤ c3 * eps ^ 2 / 192 := by gcongr

/-! ## The explicit choice of epsilon prime -/

/-- The fixed sharpness parameter.  In applications
`M = 98304*Ccells*Nu*ratio*E`. -/
noncomputable def exceptionalEpsilonPrime
    (eps c3 NU M : ℝ) : ℝ :=
  eps * Real.sqrt c3 /
    (8 * Real.exp 13 * NU * Real.sqrt M)

/-- The main sharp cost is exactly half of the available square-root scale;
another equal half remains for the Rankin tail and the ladder remainder. -/
theorem exceptionalEpsilonPrime_margin
    (eps c3 NU M : ℝ) (hc3 : 0 ≤ c3) (hNU : 0 < NU) (hM : 0 < M) :
    M * (2 * (4 * exceptionalEpsilonPrime eps c3 NU M *
      Real.exp 13 * NU)) ^ 2 = c3 * eps ^ 2 := by
  have hsqrtM : Real.sqrt M ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hM)
  have hinner :
      2 * (4 * (eps * Real.sqrt c3 /
          (8 * Real.exp 13 * NU * Real.sqrt M)) * Real.exp 13 * NU) =
        eps * Real.sqrt c3 / Real.sqrt M := by
    field_simp [hsqrtM, ne_of_gt hNU, Real.exp_ne_zero]
    ring
  unfold exceptionalEpsilonPrime
  rw [hinner]
  field_simp [hsqrtM]
  rw [Real.sq_sqrt hc3, Real.sq_sqrt hM.le]
  ring

/-- The uniform envelope for the sharp cell bound plus its sifted ladder
remainder. -/
noncomputable def exceptionalDeltaEnvelope
    (epsPrime NU tail rem : ℝ) : ℝ :=
  2 * (2 * epsPrime * Real.exp 13 * NU + tail) + rem

theorem exceptionalDeltaEnvelope_nonneg
    (epsPrime NU tail rem : ℝ)
    (hepsPrime : 0 ≤ epsPrime) (hNU : 0 ≤ NU)
    (htail : 0 ≤ tail) (hrem : 0 ≤ rem) :
    0 ≤ exceptionalDeltaEnvelope epsPrime NU tail rem := by
  unfold exceptionalDeltaEnvelope
  positivity

/-- A fixed sharp envelope and a Brun remainder envelope discharge the
capstone's pointwise `hDeltaU` inequality by addition. -/
theorem exceptionalDeltaEnvelope_bounds_sharp_add_remainder
    (sharp remainder epsPrime NU tail rem : ℝ)
    (hsharp : sharp ≤ 2 * (2 * epsPrime * Real.exp 13 * NU + tail))
    (hremainder : remainder ≤ rem) :
    sharp + remainder ≤ exceptionalDeltaEnvelope epsPrime NU tail rem := by
  unfold exceptionalDeltaEnvelope
  linarith

/-- If the doubled Rankin tail plus the ladder remainder is no larger than
the main sharp contribution, the complete sharp envelope meets the fixed
prime condition. -/
theorem exceptional_delta_fixed_condition
    (eps c3 NU M tail rem : ℝ)
    (heps : 0 ≤ eps) (hc3 : 0 ≤ c3) (hNU : 0 < NU) (hM : 0 < M)
    (htail0 : 0 ≤ tail) (hrem0 : 0 ≤ rem)
    (htail : 2 * tail + rem ≤
      4 * exceptionalEpsilonPrime eps c3 NU M * Real.exp 13 * NU) :
    M * exceptionalDeltaEnvelope
      (exceptionalEpsilonPrime eps c3 NU M) NU tail rem ^ 2 ≤
        c3 * eps ^ 2 := by
  have hmain0 : 0 ≤
      4 * exceptionalEpsilonPrime eps c3 NU M * Real.exp 13 * NU := by
    unfold exceptionalEpsilonPrime
    positivity
  have hepsPrime0 : 0 ≤ exceptionalEpsilonPrime eps c3 NU M := by
    unfold exceptionalEpsilonPrime
    positivity
  have hdelta0 : 0 ≤ exceptionalDeltaEnvelope
      (exceptionalEpsilonPrime eps c3 NU M) NU tail rem := by
    unfold exceptionalDeltaEnvelope
    have hexp0 : 0 ≤ Real.exp 13 := Real.exp_nonneg _
    nlinarith [mul_nonneg (mul_nonneg hepsPrime0 hexp0) hNU.le]
  have hdelta : exceptionalDeltaEnvelope
      (exceptionalEpsilonPrime eps c3 NU M) NU tail rem ≤
      2 * (4 * exceptionalEpsilonPrime eps c3 NU M * Real.exp 13 * NU) := by
    unfold exceptionalDeltaEnvelope
    linarith
  have hdeltaSq : exceptionalDeltaEnvelope
      (exceptionalEpsilonPrime eps c3 NU M) NU tail rem ^ 2 ≤
      (2 * (4 * exceptionalEpsilonPrime eps c3 NU M *
        Real.exp 13 * NU)) ^ 2 := pow_le_pow_left₀ hdelta0 hdelta 2
  calc
    M * exceptionalDeltaEnvelope
        (exceptionalEpsilonPrime eps c3 NU M) NU tail rem ^ 2 ≤ M *
        (2 * (4 * exceptionalEpsilonPrime eps c3 NU M *
          Real.exp 13 * NU)) ^ 2 :=
      mul_le_mul_of_nonneg_left hdeltaSq hM.le
    _ = c3 * eps ^ 2 := exceptionalEpsilonPrime_margin eps c3 NU M hc3 hNU hM

/-! ## Closing the half-band aggregate -/

/-- Splitting `c3*eps^2/48` as `1/192 + 1/192 + 1/96` closes the repaired
exceptional schedule whenever `rho ≥ 1/3`. -/
theorem exceptional_actual_cost_schedule_of_fixed_fits
    (I : Finset ℕ) (integerCost primeCost : ℕ → ℝ)
    (wide c3 eps rho : ℝ) (hc3 : 0 < c3) (heps : 0 < eps)
    (hrho : 1 / 3 ≤ rho)
    (hint : 2 * (I.card : ℝ) * (∑ v ∈ I, integerCost v) ≤
      c3 * eps ^ 2 / 192)
    (hprime : 2 * (I.card : ℝ) * (∑ v ∈ I, primeCost v) ≤
      c3 * eps ^ 2 / 192)
    (hwide : wide ≤ c3 * eps ^ 2 / 96) :
    let cost := fun v => integerCost v + primeCost v
    (∀ v, cost v ≤ exceptionalCellKappa
        (cost v) (bandBudget c3 eps rho) * bandBudget c3 eps rho) ∧
      2 * (I.card : ℝ) *
          (∑ v ∈ I, exceptionalCellKappa
            (cost v) (bandBudget c3 eps rho)) * bandBudget c3 eps rho + wide ≤
        bandBudget c3 eps rho / 2 := by
  dsimp only
  have hbudget : bandBudget c3 eps rho ≠ 0 := by
    unfold bandBudget
    have hrho0 : 0 < rho := lt_of_lt_of_le (by norm_num) hrho
    positivity
  apply exceptional_actual_cost_schedule I
    (fun v => integerCost v + primeCost v) (bandBudget c3 eps rho) wide hbudget
  have hsum :
      2 * (I.card : ℝ) *
          ((∑ v ∈ I, integerCost v) + (∑ v ∈ I, primeCost v)) + wide ≤
        c3 * eps ^ 2 / 48 := by
    linarith
  calc
    2 * (I.card : ℝ) *
        (∑ x ∈ I, (integerCost x + primeCost x)) + wide =
        2 * (I.card : ℝ) *
          ((∑ x ∈ I, integerCost x) + (∑ x ∈ I, primeCost x)) + wide := by
      rw [Finset.sum_add_distrib]
    _ ≤ c3 * eps ^ 2 / 48 := hsum
    _ ≤ bandBudget c3 eps rho / 2 := by
      unfold bandBudget
      have hnonneg : 0 ≤ c3 * eps ^ 2 := by positivity
      nlinarith

end Tao2015

end MoltResearch
