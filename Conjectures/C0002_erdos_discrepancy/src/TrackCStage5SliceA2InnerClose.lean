import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryScheduleClose

/-!
# Track R A2-V': concrete shifted inner band

This leaf installs the concrete ordinary ladder and exceptional schedule in
the corrected shifted-share capstone.  Its remaining inputs are elementary
window margins and the nonpretentiousness range conditions.
-/

namespace MoltResearch

namespace Tao2015

open Real Finset MeasureTheory ExpSums

set_option maxHeartbeats 1200000 in
/-- The closed ordinary and exceptional schedules imply the complete inner
Fourier-band estimate for the final level list. -/
theorem sliceA2_inner_band_closed
    [HalaszLargeValuesAssumption]
    (Cp : ℝ) (hCp1 : 1 ≤ Cp) (hprimeBound : PrimeLargeValuesBound Cp)
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta H P0 ratio0 A1 : ℕ)
    (lowBudget epsc eps rho0 K1 K2 T : ℝ)
    (hP0 : 21 ≤ P0) (hA : 0 < A) (hH : 0 < H) (hDelta : Delta ≤ A)
    (hlow : 0 < lowBudget) (heps : 0 < eps) (hrho0 : 0 < rho0)
    (hT1 : 1 ≤ T) (hTK2 : K2 + 2 ≤ T)
    (hratio : rho0 ≤ (Delta : ℝ) / A)
    (hordinary :
      SliceA2OrdinaryScheduleClosed g A Delta (exceptionalPrimes A1 epsc)
        P0 ratio0 (sliceA2ExceptionalLadderEta Cp lowBudget epsc eps rho0)
        (sliceA2LadderJ P0 ratio0
          (sliceA2ExceptionalLadderEta Cp lowBudget epsc eps rho0) A1 (by omega))
        eps rho0 T K1 K2)
    (haggregate :
      SliceA2ExceptionalAggregateClosed Cp g A Delta P0 ratio0 A1
        lowBudget epsc eps rho0 K1 K2 T (by omega))
    (D Apret : ℝ) (hD : 1 ≤ D) (hApret : 3 ≤ Apret)
    (hNP : NonPretentiousAt g Apret (2 * A + 1))
    (hrange :
      2 * Real.pi * T +
          2 * Real.pi *
            (((halaszM (3 * (2 * A + 1)) : ℕ) : ℝ) + 1) ≤
        (Apret / 3) * ((3 * (2 * A + 1) : ℕ) : ℝ))
    (hstrength :
      2 * D ≤ Apret / 3 - 2 *
        (Real.log (Real.log ((3 * (2 * A + 1) : ℕ) : ℝ)) -
          Real.log (Real.log (exceptionalSharpCutoff A : ℝ)) + 12))
    (hx0 : cellHalaszThreshold ≤ exceptionalSharpCutoff A)
    (hdeltaOne :
      sliceA2ExceptionalEpsilonPrime Cp A1 epsc eps rho0 ≤ 8 * Real.exp 1)
    (hQsq : exceptionalPrimeUpper A1 epsc ^ 2 ≤ A)
    (hNuQ : sliceA2ExceptionalN A1 epsc eps rho0 *
      exceptionalPrimeUpper A1 epsc ≤ A)
    (hsep : sliceA2LadderQ P0 ratio0
        (sliceA2ExceptionalLadderEta Cp lowBudget epsc eps rho0)
        (sliceA2LadderJ P0 ratio0
          (sliceA2ExceptionalLadderEta Cp lowBudget epsc eps rho0) A1 (by omega) - 1) ≤
      exceptionalPrimeLower A1)
    (hanchor : ∀ v ∈ sliceA2ExceptionalI A1 epsc eps rho0,
      6 ≤ sliceA2ExceptionalAnchor A1 v epsc eps rho0)
    (hDeltaBound : ∀ v : ℕ,
      let eta := sliceA2ExceptionalLadderEta Cp lowBudget epsc eps rho0
      let J := sliceA2LadderJ P0 ratio0 eta A1 (by omega)
      let tail := sliceA2ExceptionalTailBudget Cp epsc eps rho0
      let rem := sliceA2ExceptionalLadderBudget Cp lowBudget epsc eps rho0 / 4
      cellHalaszSharpBound
            (exceptionalSharpCutoff A) D
            (exceptionalDelta0
              (sliceA2ExceptionalEpsilonPrime Cp A1 epsc eps rho0))
            (A / sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
            ((A + Delta) /
              sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
            (exceptionalPrimes A1 epsc)
            [sliceA2LadderPrimes P0 ratio0 eta 0] +
          ladderSiftedLogMass
            (A / sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
            ((A + Delta) /
              sliceA2ExceptionalRepresentative A1 v epsc eps rho0)
            ((List.range (J - 1)).map
              (fun i => sliceA2LadderPrimes P0 ratio0 eta (i + 1))) ≤
        sliceA2ExceptionalDeltaEnvelope Cp A1 epsc eps rho0 tail rem) :
    ∀ w : ℝ → ℝ, Measurable w → (∀ xi, 0 ≤ w xi) →
      (∀ xi, w xi ≤ (4 * (H : ℝ) / A) ^ 2) →
      (∫ xi in {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2},
          ‖∑ m ∈ typicalS A (A + Delta)
              (sliceA2FinalLevels P0 ratio0
                (sliceA2ExceptionalLadderEta Cp lowBudget epsc eps rho0)
                A1 epsc (by omega)),
              (g m / (m : ℂ)) *
                ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2 *
            w xi) ≤
        (4 * (H : ℝ) / A) ^ 2 *
          bandBudget 1 eps ((Delta : ℝ) / A) := by
  intro w hwm hw0 hwsup
  let eta := sliceA2ExceptionalLadderEta Cp lowBudget epsc eps rho0
  let J := sliceA2LadderJ P0 ratio0 eta A1 (by omega)
  let Pl := sliceA2LadderPrimes P0 ratio0 eta
  let Pu := exceptionalPrimes A1 epsc
  let Nl := fun j => sliceA2OrdinaryN P0 ratio0 eta j eps rho0
  let v0l := fun j => sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0
  let v1l := fun j => sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0
  let ql := fun j => sliceA2OrdinaryRepresentative P0 ratio0 eta j eps rho0
  let Nu := sliceA2ExceptionalN A1 epsc eps rho0
  let v0u := sliceA2ExceptionalV0 A1 epsc eps rho0
  let v1u := sliceA2ExceptionalV1 A1 epsc eps rho0
  let qu := fun v => sliceA2ExceptionalRepresentative A1 v epsc eps rho0
  let PcU := fun v => sliceA2ExceptionalAnchor A1 v epsc eps rho0
  let ellU := fun v => sliceA2ExceptionalMoment A1 v epsc eps rho0 T
  let tail := sliceA2ExceptionalTailBudget Cp epsc eps rho0
  let rem := sliceA2ExceptionalLadderBudget Cp lowBudget epsc eps rho0 / 4
  let d := sliceA2ExceptionalDeltaEnvelope Cp A1 epsc eps rho0 tail rem
  let Bq := fun v => sliceA2ExceptionalBq A Delta A1 v epsc eps rho0
  let coeffMass := fun v =>
    sliceA2ExceptionalCoeffMass g A Delta P0 ratio0 eta J A1 v epsc eps rho0
  let Gamma := fun v => sliceA2ExceptionalGamma A A1 v epsc eps rho0 T
  let Kcov := sliceA2ExceptionalCover g P0 ratio0 eta J A1
    eps epsc rho0 K1 K2
  let L := sliceA2ExceptionalLogFactor T
  have hJ : 0 < J := by
    dsimp [J]
    exact sliceA2LadderJ_pos P0 ratio0 eta A1 (by omega)
  have hPl : ∀ i < J, ∀ p ∈ Pl i, p.Prime := by
    intro i hi p hp
    exact sliceA2LadderPrimes_prime P0 ratio0 eta i p hp
  have hPu : ∀ p ∈ Pu, p.Prime := by
    intro p hp
    exact exceptionalPrimes_prime A1 epsc p hp
  have hA2 : 2 ≤ A := by
    have hQ3 : 3 ≤ exceptionalPrimeUpper A1 epsc :=
      (exceptionalPrimeLower_three_le A1).trans
        (exceptionalPrimeLower_le_upper A1 epsc)
    nlinarith [hQsq]
  have hPAu : ∀ p ∈ Pu, p * p ≤ A := by
    intro p hp
    have hpQ := (exceptionalPrimes_bounds A1 epsc p hp).2
    nlinarith [hQsq]
  have hdisj : ∀ i < J, ∀ k < J, i ≠ k → Disjoint (Pl i) (Pl k) := by
    simpa [Pl] using sliceA2FinalLevels_ordinary_disjoint P0 ratio0 eta A1 (by omega)
  have hdisjU : ∀ i < J, Disjoint (Pl i) Pu := by
    simpa [Pl, Pu, J] using
      sliceA2FinalLevels_exceptional_disjoint P0 ratio0 eta A1 epsc
        (by omega) (by simpa [eta, J] using hsep)
  have hNl : ∀ j < J, 0 < Nl j := by
    intro j hj
    exact sliceA2OrdinaryN_pos P0 ratio0 eta j eps rho0
  have hcells := fun j => sliceA2Ordinary_cell_data
    P0 ratio0 eta j eps rho0 (by omega)
  have hcovl : ∀ j < J, (Finset.Ico (v0l j) (v1l j + 1)).biUnion
      (eadicCell (Pl j) (2 * Nl j)) = Pl j := by
    intro j hj
    simpa [Pl, Nl, v0l, v1l] using (hcells j).1
  have hqupl : ∀ j < J, ∀ v ∈ Finset.Ico (v0l j) (v1l j + 1),
      (ql j v : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (Nl j : ℝ))) := by
    intro j hj v hv
    simpa [Nl, v0l, v1l, ql] using (hcells j).2.1 v (by simpa [v0l, v1l] using hv)
  have hq1l : ∀ j < J, ∀ v, 1 ≤ ql j v := by
    intro j hj v
    exact (hcells j).2.2.1 v
  have hqminl : ∀ j < J, ∀ v ∈ Finset.Ico (v0l j) (v1l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v, ql j v ≤ p := by
    intro j hj v hv p hp
    exact (hcells j).2.2.2.1 v (by simpa [v0l, v1l] using hv) p
      (by simpa [Pl, Nl] using hp)
  have hqratiol : ∀ j < J, ∀ v ∈ Finset.Ico (v0l j) (v1l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
        Nl j * p ≤ (Nl j + 1) * ql j v := by
    intro j hj v hv p hp
    exact (hcells j).2.2.2.2 v (by simpa [v0l, v1l] using hv) p
      (by simpa [Pl, Nl] using hp)
  have hord := hordinary
  dsimp only [SliceA2OrdinaryScheduleClosed] at hord
  rcases hord with ⟨hmain, hreplacement, hcollision, hshare⟩
  have hUcells := sliceA2Exceptional_cell_data A1 epsc eps rho0
  have hcollars := sliceA2Exceptional_collar_data A1 A Delta epsc eps rho0 hNuQ
  have hanchors := sliceA2Exceptional_anchor_data A1 epsc eps rho0 hanchor
  have hep : 0 < sliceA2ExceptionalEpsilonPrime Cp A1 epsc eps rho0 :=
    sliceA2ExceptionalEpsilonPrime_pos Cp A1 epsc eps rho0 heps hrho0
  have htail0 : 0 ≤ tail := by
    dsimp [tail]
    exact (sliceA2ExceptionalTailBudget_pos Cp epsc eps rho0 heps hrho0).le
  have hrem0 : 0 ≤ rem := by
    dsimp [rem]
    exact div_nonneg
      (sliceA2ExceptionalLadderBudget_pos Cp lowBudget epsc eps rho0
        hlow heps hrho0).le (by norm_num)
  have hd0 : 0 ≤ d := by
    dsimp [d, sliceA2ExceptionalDeltaEnvelope]
    exact exceptionalDeltaEnvelope_nonneg _ _ _ _ hep.le (by positivity)
      htail0 hrem0
  have hagg := haggregate
  dsimp only [SliceA2ExceptionalAggregateClosed] at hagg
  rcases hagg with ⟨hint, hprime, hwide⟩
  have hresult := sliceA2_inner_band_of_aggregate_fits
    Cp hCp1 hprimeBound g hcm hg A Delta H hA hH hDelta Pl Pu J hJ hPl hPu hPAu hdisj hdisjU
    Nl v0l v1l ql hNl hcovl hqupl hq1l hqminl hqratiol
    K1 K2 T eps hT1 hTK2 heps
    (by simpa [Pl, Pu, Nl, v0l, v1l, ql, eta, J] using
      hmain 0 (by simpa [J] using hJ))
    (by
      intro j hj0 hjJ
      simpa [Pl, Pu, Nl, v0l, v1l, ql, eta, J] using
        hmain j (by simpa [J] using hjJ))
    (by simpa [Pl, Pu, Nl, v0l, v1l, ql, eta, J] using hreplacement)
    (by simpa [Pl, Pu, Nl, v0l, v1l, ql, eta, J] using hcollision)
    Nu v0u v1u (sliceA2ExceptionalN_pos A1 epsc eps rho0)
    (by simpa [Nu, v0u, v1u, Pu] using hUcells.1) qu
    (by simpa [Nu, v0u, v1u, qu] using hUcells.2.1)
    (by simpa [qu] using hUcells.2.2.1)
    (by simpa [Nu, v0u, v1u, qu, Pu] using hUcells.2.2.2.1)
    (by simpa [Nu, v0u, v1u, qu, Pu] using hUcells.2.2.2.2)
    (by simpa [Nu, v0u, v1u, Pu] using hcollars.1)
    (by simpa [Nu, v0u, v1u, Pu] using hcollars.2)
    w hwm hw0 hwsup PcU
    (by simpa [v0u, v1u, PcU] using hanchors.1)
    (by simpa [Nu, v0u, v1u, PcU, Pu] using hanchors.2.1)
    (by simpa [Nu, v0u, v1u, PcU, Pu] using hanchors.2.2)
    ellU (by
      intro v hv
      exact sliceA2ExceptionalMoment_one_le A1 v epsc eps rho0 T)
    (exceptionalSplitThreshold A) (exceptionalSplitThreshold_pos A (by omega))
    (exceptionalSharpCutoff A) hx0 D
    (exceptionalDelta0 (sliceA2ExceptionalEpsilonPrime Cp A1 epsc eps rho0))
    Apret hD (exceptionalDelta0_pos _ hep)
    (exceptionalDelta0_le_one _ hdeltaOne) hApret hNP hrange hstrength
    (fun _ => d) (by intro v hv; exact hd0)
    (by intro v hv; simpa [eta, J, tail, rem, Pl, Pu, qu, d] using hDeltaBound v)
    Bq coeffMass Gamma Kcov L rho0
    (by intro v hv; rfl) (by intro v hv; rfl) rfl rfl
    (by intro v hv; rfl) hrho0 hratio
    (by simpa [eta, J, tail, rem, d, Bq, coeffMass, Kcov, L,
      v0u, v1u, sliceA2ExceptionalI] using hint)
    (by simpa [eta, J, tail, rem, d, PcU, Gamma, Nu, Pu,
      v0u, v1u, sliceA2ExceptionalI] using hprime)
    (by simpa [eta, J] using hwide)
  simpa [sliceA2FinalLevels, eta, J, Pl, Pu] using hresult

end Tao2015

end MoltResearch
