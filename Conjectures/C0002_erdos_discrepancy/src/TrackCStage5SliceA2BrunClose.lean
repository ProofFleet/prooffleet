import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2BrunError

/-!
# Track R A2-V'-29: closing a subpower Brun envelope

This leaf isolates the last analytic calculation in the positive-ladder
density estimate.  If the number of levels, last endpoint, and last Brun
depth are bounded at the quarter-power logarithmic scale, their finite error
is at most `epsc/16`.  The dyadic harmonic mass is at least one half, so this
is precisely the second eighth of the ladder allocation.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The logarithmic subpower margins force the last finite Brun envelope
below the absolute `epsc/16` target. -/
theorem brunLastEnvelope_le_eps_div_sixteen
    (A n Q K : ℕ) (epsc y : ℝ)
    (hA : 1 ≤ A) (hepsc : 0 < epsc) (hy : 0 ≤ y)
    (hn : (n : ℝ) ≤ Real.exp y)
    (hQ : (Q : ℝ) + 1 ≤ Real.exp y)
    (hK : (K : ℝ) ≤ y)
    (hmargin : Real.log (32 / epsc) + y + 2 * y ^ 2 ≤
      Real.log (A : ℝ)) :
    n * (2 * ((Q : ℝ) + 1) ^ (2 * K) / A) ≤ epsc / 16 := by
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hQ0 : (0 : ℝ) ≤ (Q : ℝ) + 1 := by positivity
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have hpowBase : ((Q : ℝ) + 1) ^ (2 * K) ≤
      (Real.exp y) ^ (2 * K) :=
    pow_le_pow_left₀ hQ0 hQ (2 * K)
  have hpowExp : (Real.exp y) ^ (2 * K) ≤
      Real.exp (2 * y ^ 2) := by
    rw [← Real.exp_nat_mul]
    rw [Real.exp_le_exp]
    push_cast
    nlinarith
  have hlogArg : 0 < 32 / epsc := by positivity
  have hscale : 2 * Real.exp (y + 2 * y ^ 2) ≤
      epsc / 16 * A := by
    have hexpMargin := Real.exp_le_exp.mpr hmargin
    rw [Real.exp_log hApos] at hexpMargin
    calc
      2 * Real.exp (y + 2 * y ^ 2) =
          epsc / 16 * Real.exp
            (Real.log (32 / epsc) + y + 2 * y ^ 2) := by
        rw [show Real.log (32 / epsc) + y + 2 * y ^ 2 =
          Real.log (32 / epsc) + (y + 2 * y ^ 2) by ring]
        simp only [Real.exp_add, Real.exp_log hlogArg]
        field_simp
        ring
      _ ≤ epsc / 16 * A :=
        mul_le_mul_of_nonneg_left hexpMargin (by positivity)
  have hnum : (n : ℝ) * (2 * ((Q : ℝ) + 1) ^ (2 * K)) ≤
      epsc / 16 * A := by
    calc
      (n : ℝ) * (2 * ((Q : ℝ) + 1) ^ (2 * K)) ≤
          Real.exp y * (2 * Real.exp (2 * y ^ 2)) := by
        gcongr
        exact hpowBase.trans hpowExp
      _ = 2 * Real.exp (y + 2 * y ^ 2) := by
        rw [Real.exp_add]
        ring
      _ ≤ epsc / 16 * A := hscale
  calc
    (n : ℝ) * (2 * ((Q : ℝ) + 1) ^ (2 * K) / A) =
        ((n : ℝ) * (2 * ((Q : ℝ) + 1) ^ (2 * K))) / A := by ring
    _ ≤ (epsc / 16 * A) / A :=
      div_le_div_of_nonneg_right hnum hApos.le
    _ = epsc / 16 := by field_simp

/-- The harmonic mass of every nonempty dyadic interval is at least one
half. -/
theorem dyadicHarmonicMass_ge_half (A : ℕ) (hA : 1 ≤ A) :
    (1 : ℝ) / 2 ≤ ∑ m ∈ Ioc A (2 * A), (1 : ℝ) / m := by
  have hpoint : ∀ m ∈ Ioc A (2 * A),
      (1 : ℝ) / ((2 * A : ℕ) : ℝ) ≤ (1 : ℝ) / m := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by
      exact_mod_cast (show 0 < m by have := (mem_Ioc.mp hm).1; omega)
    exact one_div_le_one_div_of_le hm0 (by
      exact_mod_cast (mem_Ioc.mp hm).2)
  have hsum := card_nsmul_le_sum _ _ _ hpoint
  rw [Nat.card_Ioc, nsmul_eq_mul] at hsum
  calc
    (1 : ℝ) / 2 = ((2 * A - A : ℕ) : ℝ) *
        (1 / ((2 * A : ℕ) : ℝ)) := by
      have hsub : 2 * A - A = A := by omega
      rw [hsub]
      push_cast
      field_simp
    _ ≤ ∑ m ∈ Ioc A (2 * A), (1 : ℝ) / m := hsum

/-- Quarter-power-logarithmic bounds on the selected ladder data close all
of its finite Brun errors uniformly for every `A` above the base scale. -/
theorem sliceA2PositiveLadder_brunErrors_le_eighth
    (P0 ratio0 eta n A1 A : ℕ) (epsc y : ℝ)
    (hP0 : 3 ≤ P0) (hA1 : 1 ≤ A1) (hAA1 : A1 ≤ A)
    (hepsc : 0 < epsc) (hy : 0 ≤ y)
    (hn : (n : ℝ) ≤ Real.exp y)
    (hQ : (sliceA2LadderQ P0 ratio0 eta n : ℝ) + 1 ≤ Real.exp y)
    (hK : (brunPowerIntervalDepth
      (sliceA2LadderRatio ratio0 eta n) : ℝ) ≤ y)
    (hmargin : Real.log (32 / epsc) + y + 2 * y ^ 2 ≤
      Real.log (A1 : ℝ)) :
    ∑ i ∈ range n,
        brunPowerIntervalFiniteError A
          (sliceA2LadderP P0 ratio0 eta (i + 1))
          (sliceA2LadderRatio ratio0 eta (i + 1)) ≤
      (epsc / 8) *
        ∑ m ∈ Ioc A (2 * A), (1 : ℝ) / m := by
  have hA : 1 ≤ A := hA1.trans hAA1
  have hsum := sliceA2PositiveLadder_brunErrors_le
    P0 ratio0 eta n A hP0 hA
  let Q := sliceA2LadderQ P0 ratio0 eta n
  let K := brunPowerIntervalDepth (sliceA2LadderRatio ratio0 eta n)
  have hden : n * (2 * ((Q : ℝ) + 1) ^ (2 * K) / A) ≤
      n * (2 * ((Q : ℝ) + 1) ^ (2 * K) / A1) := by
    have hA1pos : (0 : ℝ) < A1 := by
      exact_mod_cast (show 0 < A1 by omega)
    have hcast : (A1 : ℝ) ≤ A := by exact_mod_cast hAA1
    have hnum0 : 0 ≤ 2 * ((Q : ℝ) + 1) ^ (2 * K) := by positivity
    gcongr
  have hsmall : n * (2 * ((Q : ℝ) + 1) ^ (2 * K) / A1) ≤
      epsc / 16 := by
    apply brunLastEnvelope_le_eps_div_sixteen A1 n Q K epsc y
      hA1 hepsc hy hn
    · simpa [Q] using hQ
    · simpa [K] using hK
    · exact hmargin
  have hhalf := dyadicHarmonicMass_ge_half A hA
  calc
    ∑ i ∈ range n,
        brunPowerIntervalFiniteError A
          (sliceA2LadderP P0 ratio0 eta (i + 1))
          (sliceA2LadderRatio ratio0 eta (i + 1)) ≤
        n * (2 * ((Q : ℝ) + 1) ^ (2 * K) / A) := by
      simpa [Q, K] using hsum
    _ ≤ epsc / 16 := hden.trans hsmall
    _ = (epsc / 8) * ((1 : ℝ) / 2) := by ring
    _ ≤ (epsc / 8) *
        ∑ m ∈ Ioc A (2 * A), (1 : ℝ) / m :=
      mul_le_mul_of_nonneg_left hhalf (by positivity)

end Tao2015

end MoltResearch
