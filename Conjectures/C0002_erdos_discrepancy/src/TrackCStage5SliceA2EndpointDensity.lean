import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2DensityError

/-!
# Track R A2-V'-24: eventual endpoint density

This leaf closes the finite Turan--Kubilius errors uniformly for every
`A >= A1`.  Level zero has a fixed upper endpoint.  The exceptional endpoint
uses A2-V'-22 with the exact coefficient needed by the common error envelope.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- A convenient one-sixteenth form of the finite TK error bound. -/
theorem sliceA2TKFiniteError_le_eps_div_sixteen
    (A : ℕ) (P : Finset ℕ) (epsc Emax Q : ℝ)
    (hA : 0 < A) (hepsc : 0 < epsc) (hEmax : 0 ≤ Emax)
    (hQ : 1 ≤ Q)
    (hmassLo : 4 / epsc ≤ ∑ p ∈ P, (1 : ℝ) / p)
    (hmassHi : ∑ p ∈ P, (1 : ℝ) / p ≤ Emax)
    (hcard : (P.card : ℝ) ≤ Q)
    (hscale : epsc * (6 + 6 * Emax) * Q ^ 2 ≤ A) :
    sliceA2TKFiniteError A P ≤ epsc / 16 := by
  have henv := sliceA2TKFiniteError_le A P epsc Emax Q
    hA hepsc hEmax hmassLo hmassHi hcard
  have hQ0 : 0 ≤ Q := le_trans (by norm_num) hQ
  have hpoly :
      3 * (Q + Q ^ 2) + 6 * Emax * Q ≤
        (6 + 6 * Emax) * Q ^ 2 := by
    have hQQ : Q ≤ Q ^ 2 := by nlinarith
    have hEQ : Emax * Q ≤ Emax * Q ^ 2 :=
      mul_le_mul_of_nonneg_left hQQ hEmax
    nlinarith
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  calc
    sliceA2TKFiniteError A P ≤
        (epsc ^ 2 / 16) *
          (3 * (Q + Q ^ 2) + 6 * Emax * Q) / A := henv
    _ ≤ (epsc ^ 2 / 16) * ((6 + 6 * Emax) * Q ^ 2) / A := by
      gcongr
    _ ≤ epsc / 16 := by
      rw [div_le_iff₀ hAreal]
      have hepsc0 : 0 ≤ epsc := hepsc.le
      calc
        epsc ^ 2 / 16 * ((6 + 6 * Emax) * Q ^ 2) =
            (epsc / 16) * (epsc * (6 + 6 * Emax) * Q ^ 2) := by ring
        _ ≤ (epsc / 16) * (A : ℝ) :=
          mul_le_mul_of_nonneg_left hscale (by positivity)

/-- The bottom and exceptional pair satisfies its three-quarter density
allocation uniformly throughout every sufficiently large scale window. -/
theorem exists_sliceA2_bottom_exceptional_density
    (P0 eta : ℕ) (epsc : ℝ) (hP0 : 3 ≤ P0) (hepsc : 0 < epsc) :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 → ∀ A : ℕ, A1 ≤ A →
      (∑ n ∈ (Ioc A (2 * A)).filter
          (fun n ↦ ¬ HasFactorInAll
            [sliceA2LadderPrimes P0 (exceptionalIntervalRatio epsc) eta 0,
              exceptionalPrimes A1 epsc] n), (1 : ℝ) / n ≤
        (3 * epsc / 4) * ∑ n ∈ Ioc A (2 * A), (1 : ℝ) / n) ∧
      (∀ p ∈ sliceA2LadderPrimes P0
          (exceptionalIntervalRatio epsc) eta 0,
        ∀ q ∈ sliceA2LadderPrimes P0
          (exceptionalIntervalRatio epsc) eta 0, p * q ≤ A) ∧
      (∀ p ∈ exceptionalPrimes A1 epsc,
        ∀ q ∈ exceptionalPrimes A1 epsc, p * q ≤ A) := by
  let R := exceptionalIntervalRatio epsc
  let Q0 := sliceA2LadderQ P0 R eta 0
  let Emax := Real.log ((R : ℝ) + 1) + 12
  let Cscale : ℝ := max 1 (epsc * (6 + 6 * Emax))
  have hEmax : 0 ≤ Emax := by
    dsimp [Emax, R]
    have hR : (1 : ℝ) ≤ exceptionalIntervalRatio epsc := by
      exact_mod_cast (show 1 ≤ exceptionalIntervalRatio epsc by
        have := exceptionalIntervalRatio_three_le epsc
        omega)
    have : 0 ≤ Real.log ((exceptionalIntervalRatio epsc : ℝ) + 1) :=
      Real.log_nonneg (by linarith)
    linarith
  have hCscale : 0 < Cscale :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 _)
  obtain ⟨AU, hAU⟩ := exists_const_mul_exceptionalPrimeUpper_pow_le
    Cscale 2 epsc hCscale (by norm_num)
  let Afix := ⌈Cscale * (Q0 : ℝ) ^ 2⌉₊ + 1
  let A0 := max AU Afix
  refine ⟨A0, fun A1 hA1 A hAA1 ↦ ?_⟩
  have hAfix : Afix ≤ A1 := (le_max_right AU Afix).trans hA1
  have hAone : 1 ≤ A := by
    have : 1 ≤ Afix := by dsimp [Afix]; omega
    exact this.trans (hAfix.trans hAA1)
  have hbottomScale : Cscale * (Q0 : ℝ) ^ 2 ≤ A := by
    calc
      Cscale * (Q0 : ℝ) ^ 2 ≤
          (⌈Cscale * (Q0 : ℝ) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (A : ℝ) := by
        exact_mod_cast (le_trans (Nat.le_succ _) (hAfix.trans hAA1))
  have hremoteScale :
      Cscale * (exceptionalPrimeUpper A1 epsc : ℝ) ^ 2 ≤ A :=
    (hAU A1 ((le_max_left AU Afix).trans hA1)).trans
      (by exact_mod_cast hAA1)
  have hcoef : epsc * (6 + 6 * Emax) ≤ Cscale := le_max_right _ _
  have hQ0one : 1 ≤ (Q0 : ℝ) := by
    exact_mod_cast (show 1 ≤ Q0 by
      dsimp [Q0]
      exact (sliceA2LadderP_two_le P0 R eta 0 (by omega)).trans'
        (by norm_num) |>.trans (sliceA2LadderP_le_Q P0 R eta 0))
  have hQUone : 1 ≤ (exceptionalPrimeUpper A1 epsc : ℝ) := by
    exact_mod_cast (show 1 ≤ exceptionalPrimeUpper A1 epsc by
      exact (exceptionalPrimeLower_three_le A1).trans'
        (by norm_num) |>.trans (exceptionalPrimeLower_le_upper A1 epsc))
  have hbottomProduct :
      ∀ p ∈ sliceA2LadderPrimes P0 R eta 0,
        ∀ q ∈ sliceA2LadderPrimes P0 R eta 0, p * q ≤ A := by
    intro p hp q hq
    have hpQ := (sliceA2LadderPrimes_bounds P0 R eta 0 p hp).2
    have hqQ := (sliceA2LadderPrimes_bounds P0 R eta 0 q hq).2
    have hQsq : Q0 ^ 2 ≤ A := by
      have hcone : (1 : ℝ) ≤ Cscale := le_max_left _ _
      have : (Q0 : ℝ) ^ 2 ≤ A :=
        by simpa using
          (mul_le_mul_of_nonneg_right hcone (sq_nonneg (Q0 : ℝ))).trans
            hbottomScale
      exact_mod_cast this
    calc
      p * q ≤ Q0 * Q0 := Nat.mul_le_mul hpQ hqQ
      _ = Q0 ^ 2 := by ring
      _ ≤ A := hQsq
  have hremoteProduct :
      ∀ p ∈ exceptionalPrimes A1 epsc,
        ∀ q ∈ exceptionalPrimes A1 epsc, p * q ≤ A := by
    intro p hp q hq
    have hpQ := (exceptionalPrimes_bounds A1 epsc p hp).2
    have hqQ := (exceptionalPrimes_bounds A1 epsc q hq).2
    have hQsq : exceptionalPrimeUpper A1 epsc ^ 2 ≤ A := by
      have hcone : (1 : ℝ) ≤ Cscale := le_max_left _ _
      have : (exceptionalPrimeUpper A1 epsc : ℝ) ^ 2 ≤ A :=
        by simpa using
          (mul_le_mul_of_nonneg_right hcone
            (sq_nonneg (exceptionalPrimeUpper A1 epsc : ℝ))).trans
            hremoteScale
      exact_mod_cast this
    calc
      p * q ≤ exceptionalPrimeUpper A1 epsc *
          exceptionalPrimeUpper A1 epsc := Nat.mul_le_mul hpQ hqQ
      _ = exceptionalPrimeUpper A1 epsc ^ 2 := by ring
      _ ≤ A := hQsq
  have hmassHi0 :
      ∑ p ∈ sliceA2LadderPrimes P0 R eta 0, (1 : ℝ) / p ≤ Emax := by
    have hs := prime_power_Ioc_mass_upper P0 R hP0
      (by have := exceptionalIntervalRatio_three_le epsc; dsimp [R]; omega)
    have hRmax : max 2 R = R :=
      max_eq_right (by have := exceptionalIntervalRatio_three_le epsc; dsimp [R]; omega)
    simpa [sliceA2LadderPrimes, sliceA2LadderQ, sliceA2LadderP,
      sliceA2LadderRatio, hRmax, Emax] using hs
  have hmassHiU :
      ∑ p ∈ exceptionalPrimes A1 epsc, (1 : ℝ) / p ≤ Emax := by
    have hs := prime_power_Ioc_mass_upper (exceptionalPrimeLower A1) R
      (exceptionalPrimeLower_three_le A1)
      (by have := exceptionalIntervalRatio_three_le epsc; dsimp [R]; omega)
    simpa [exceptionalPrimes, exceptionalPrimeUpper, Emax, R] using hs
  have herror0 : sliceA2TKFiniteError A
      (sliceA2LadderPrimes P0 R eta 0) ≤ epsc / 16 := by
    apply sliceA2TKFiniteError_le_eps_div_sixteen A
      (sliceA2LadderPrimes P0 R eta 0) epsc Emax Q0
      (by omega) hepsc hEmax hQ0one
    · simpa [R] using sliceA2BottomPrimes_mass_ge_four_div P0 eta epsc hP0
    · exact hmassHi0
    · exact_mod_cast sliceA2LadderPrimes_card_le_Q P0 R eta 0
    · exact (mul_le_mul_of_nonneg_right hcoef (sq_nonneg (Q0 : ℝ))).trans
        hbottomScale
  have herrorU : sliceA2TKFiniteError A (exceptionalPrimes A1 epsc) ≤
      epsc / 16 := by
    apply sliceA2TKFiniteError_le_eps_div_sixteen A
      (exceptionalPrimes A1 epsc) epsc Emax
      (exceptionalPrimeUpper A1 epsc) (by omega) hepsc hEmax hQUone
    · exact exceptionalPrimes_mass_ge_four_div A1 epsc
    · exact hmassHiU
    · exact_mod_cast exceptionalPrimes_card_le_upper A1 epsc
    · exact (mul_le_mul_of_nonneg_right hcoef
        (sq_nonneg (exceptionalPrimeUpper A1 epsc : ℝ))).trans hremoteScale
  have hH := half_le_sum_one_div_Ioc_dyadic A hAone
  have herror : sliceA2TKFiniteError A
        (sliceA2LadderPrimes P0 R eta 0) +
      sliceA2TKFiniteError A (exceptionalPrimes A1 epsc) ≤
        (epsc / 4) * ∑ n ∈ Ioc A (2 * A), (1 : ℝ) / n := by
    nlinarith
  refine ⟨?_, hbottomProduct, hremoteProduct⟩
  simpa [R] using sliceA2_bottom_exceptional_density
    P0 eta A1 A epsc hP0 hAone hbottomProduct hremoteProduct herror hepsc

end Tao2015

end MoltResearch
