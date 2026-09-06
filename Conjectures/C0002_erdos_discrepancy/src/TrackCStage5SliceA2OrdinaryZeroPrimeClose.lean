import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryZeroPrime
import MoltResearch.Discrepancy.VinogradovTypeI

/-!
# Track R A2-V': close the bottom prime-side fit

The fixed bottom coefficient is absorbed by
`log P0 * P0^(-7/20) → 0`.  This is the bottom-scale threshold promised in
the final parameter ledger.
-/

namespace MoltResearch

namespace Tao2015

open Filter

/-- A sufficiently large bottom endpoint absorbs the exact prime-side
level-zero schedule cost, uniformly in the unused later-level ratio. -/
theorem exists_sliceA2Ordinary_zero_prime_fit
    (ratio0 : ℕ) (eps rho0 : ℝ) (heps : 0 < eps) (hrho0 : 0 < rho0) :
    ∃ Pmin : ℕ, 3 ≤ Pmin ∧ ∀ P0 eta : ℕ, Pmin ≤ P0 →
      (2 * (sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℝ) *
            (Real.log (sliceA2LadderQ P0 ratio0 eta 0) -
              Real.log (sliceA2LadderP P0 ratio0 eta 0)) + 2) *
          (Real.exp Real.pi * Real.log 4 *
            (8 * ((sliceA2LadderP P0 ratio0 eta 0 : ℝ) ^
                (-(2 * innerBandScheduleAlpha 0)) *
              Real.exp (2 * innerBandScheduleAlpha 0 /
                ((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ))) *
              (((2 * sliceA2OrdinaryN P0 ratio0 eta 0 eps rho0 : ℕ) : ℝ) /
                (2 * innerBandScheduleAlpha 0) + 1))) ≤
          sliceA2KappaMain 0 / 2 * (eps ^ 2 * rho0 / 8) := by
  let C := sliceA2OrdinaryZeroPrimeCoefficient ratio0 eps rho0
  let target := sliceA2KappaMain 0 / 2 * (eps ^ 2 * rho0 / 8)
  let b : ℝ := 7 / 20
  have hC : 0 < C := by
    dsimp [C]
    exact sliceA2OrdinaryZeroPrimeCoefficient_pos ratio0 eps rho0 heps hrho0
  have htarget : 0 < target := by
    dsimp [target, sliceA2KappaMain, ordinaryLegShare]
    positivity
  have hb : 0 < b := by norm_num [b]
  have hconst : Tendsto (fun _ : ℝ => C) atTop (nhds C) := tendsto_const_nhds
  have hdecay : Tendsto
      (fun y : ℝ => y ^ (1 : ℕ) * Real.exp (-b * y)) atTop (nhds 0) :=
    by simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 b hb
  have hlimY : Tendsto
      (fun y : ℝ => C * (y ^ (1 : ℕ) * Real.exp (-b * y)))
      atTop (nhds 0) := by
    convert hconst.mul hdecay using 1 <;> simp
  have hlimX : Tendsto
      (fun x : ℝ => C *
        ((Real.log x) ^ (1 : ℕ) * Real.exp (-b * Real.log x)))
      atTop (nhds 0) := hlimY.comp Real.tendsto_log_atTop
  have hevent := (tendsto_order.1 hlimX).2 target htarget
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨X0, hX0⟩ := hevent
  let Pmin := max 3 (⌈max 0 X0⌉₊ + 1)
  refine ⟨Pmin, le_max_left _ _, fun P0 eta hP0 => ?_⟩
  have hPmin3 : 3 ≤ P0 := (le_max_left 3 (⌈max 0 X0⌉₊ + 1)).trans hP0
  have hceil : max 0 X0 ≤ (⌈max 0 X0⌉₊ : ℝ) := Nat.le_ceil _
  have hX0P : X0 ≤ (P0 : ℝ) := by
    have hnat : ⌈max 0 X0⌉₊ + 1 ≤ P0 :=
      (le_max_right 3 (⌈max 0 X0⌉₊ + 1)).trans hP0
    have hcast : ((⌈max 0 X0⌉₊ + 1 : ℕ) : ℝ) ≤ P0 := by exact_mod_cast hnat
    exact (le_max_right 0 X0).trans (hceil.trans (by
      push_cast at hcast
      linarith))
  have hraw := hX0 (P0 : ℝ) hX0P
  have hPpos : (0 : ℝ) < P0 := by positivity
  have hrpow : (P0 : ℝ) ^ (-(7 / 20 : ℝ)) =
      Real.exp (-b * Real.log (P0 : ℝ)) := by
    rw [Real.rpow_def_of_pos hPpos]
    dsimp [b]
    congr 1
    ring
  have henvelope :
      sliceA2OrdinaryZeroPrimeCoefficient ratio0 eps rho0 *
          Real.log (P0 : ℝ) * (P0 : ℝ) ^ (-(7 / 20 : ℝ)) ≤
        sliceA2KappaMain 0 / 2 * (eps ^ 2 * rho0 / 8) := by
    dsimp only [C, target] at hraw
    rw [hrpow]
    simpa [pow_one, mul_assoc] using hraw.le
  exact sliceA2Ordinary_zero_prime_fit_of_envelope
    P0 ratio0 eta eps rho0 hPmin3 heps hrho0 henvelope

end Tao2015

end MoltResearch
