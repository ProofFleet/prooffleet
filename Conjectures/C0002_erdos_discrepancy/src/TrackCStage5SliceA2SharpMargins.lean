import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2InnerClose

/-!
# Track R A2-V': uniform sharp-window margins

The canonical exceptional cutoff is at least the square root of the sharp
truncation.  Thus its logarithmic loss is at most `log 2 + 12`.  The same
constant controls the low-band truncation because `3(2X+1) <= X^2` once
`X >= 7`.  A fixed nonpretentiousness strength then pays both sharp windows.
-/

namespace MoltResearch

namespace Tao2015

set_option maxRecDepth 10000

/-- The square-root exceptional cutoff loses at most `log 2` between the two
iterated logarithms. -/
theorem sliceA2Exceptional_sharp_logLoss_le
    (X : ℕ) (hX : 1 ≤ X) :
    Real.log (Real.log ((3 * (2 * X + 1) : ℕ) : ℝ)) -
          Real.log (Real.log (exceptionalSharpCutoff X : ℝ)) + 12 ≤
        Real.log 2 + 12 := by
  let N : ℝ := (3 * (2 * X + 1) : ℕ)
  have hN1 : 1 < N := by
    dsimp [N]
    exact_mod_cast (show 1 < 3 * (2 * X + 1) by omega)
  have hN0 : 0 < N := zero_lt_one.trans hN1
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  have hcut : Real.sqrt N ≤ (exceptionalSharpCutoff X : ℝ) := by
    simpa [N] using exceptionalSharpCutoff_real_lower X
  have hsqrt0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hlogcut : Real.log N / 2 ≤
      Real.log (exceptionalSharpCutoff X : ℝ) := by
    calc
      Real.log N / 2 = Real.log (Real.sqrt N) := by
        rw [Real.log_sqrt hN0.le]
      _ ≤ Real.log (exceptionalSharpCutoff X : ℝ) :=
        Real.log_le_log hsqrt0 hcut
  have hlogcut0 : 0 < Real.log (exceptionalSharpCutoff X : ℝ) :=
    (by positivity : 0 < Real.log N / 2).trans_le hlogcut
  have hiter : Real.log (Real.log N / 2) ≤
      Real.log (Real.log (exceptionalSharpCutoff X : ℝ)) :=
    Real.log_le_log (by positivity) hlogcut
  have htwo : (0 : ℝ) < 2 := by norm_num
  rw [Real.log_div hlogN.ne' htwo.ne'] at hiter
  change Real.log (Real.log N) -
      Real.log (Real.log (exceptionalSharpCutoff X : ℝ)) + 12 ≤
    Real.log 2 + 12
  linarith

/-- The local left endpoint is also a square-root-scale cutoff for the
tripled sharp truncation. -/
theorem sliceA2_low_sharp_logLoss_le
    (X : ℕ) (hX : 7 ≤ X) :
    Real.log (Real.log ((3 * (2 * X + 1) : ℕ) : ℝ)) -
          Real.log (Real.log (X : ℝ)) + 12 ≤
        Real.log 2 + 12 := by
  let N : ℝ := (3 * (2 * X + 1) : ℕ)
  have hX1 : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hX0 : (0 : ℝ) < X := zero_lt_one.trans hX1
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos hX1
  have hN0 : 0 < N := by dsimp [N]; positivity
  have hNXsq : N ≤ (X : ℝ) ^ 2 := by
    dsimp [N]
    push_cast
    have hX7 : (7 : ℝ) ≤ X := by exact_mod_cast hX
    nlinarith
  have hlogN : Real.log N ≤ 2 * Real.log (X : ℝ) := by
    calc
      Real.log N ≤ Real.log ((X : ℝ) ^ 2) :=
        Real.log_le_log hN0 hNXsq
      _ = 2 * Real.log (X : ℝ) := by rw [Real.log_pow]; norm_num
  have hlogN0 : 0 < Real.log N := Real.log_pos (by
    dsimp [N]
    exact_mod_cast (show 1 < 3 * (2 * X + 1) by omega))
  have hiter := Real.log_le_log hlogN0 hlogN
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlogX.ne'] at hiter
  change Real.log (Real.log N) - Real.log (Real.log (X : ℝ)) + 12 ≤
    Real.log 2 + 12
  linarith

/-- Once the sharp truncation is in the numerical Halász range, every
frequency interval with top `T <= X` fits at strength `A0/9`. -/
theorem sliceA2_sharp_range_of_T_le
    (X : ℕ) (T A0 : ℝ)
    (hband : 7 *
      (((halaszM (3 * (2 * X + 1)) : ℕ) : ℝ) + 1) ≤
        ((3 * (2 * X + 1) : ℕ) : ℝ))
    (hT0 : 0 ≤ T) (hTX : T ≤ X) (hA0 : 27 ≤ A0) :
    2 * Real.pi * T +
          2 * Real.pi *
            (((halaszM (3 * (2 * X + 1)) : ℕ) : ℝ) + 1) ≤
        (A0 / 9) * ((3 * (2 * X + 1) : ℕ) : ℝ) := by
  let N := 3 * (2 * X + 1)
  change 2 * Real.pi * T +
      2 * Real.pi * (((halaszM N : ℕ) : ℝ) + 1) ≤
    (A0 / 9) * (N : ℝ)
  have hband' : 7 * (((halaszM N : ℕ) : ℝ) + 1) ≤ (N : ℝ) := by
    simpa only [N] using hband
  have hpi : Real.pi ≤ 4 := Real.pi_lt_four.le
  have hNpos : (0 : ℝ) < N := by positivity
  have hTX' : T ≤ (X : ℝ) := hTX
  have hXN : (X : ℝ) ≤ N / 6 := by
    dsimp [N]
    push_cast
    nlinarith
  have hM : ((halaszM N : ℕ) : ℝ) + 1 ≤ (N : ℝ) / 7 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 7)]
    simpa [mul_comm] using hband'
  have hsum : T + ((halaszM N : ℕ) : ℝ) + 1 ≤ (N : ℝ) / 3 := by
    have hTXN : T ≤ (N : ℝ) / 6 := hTX'.trans hXN
    linarith
  have hmargin :
      6 * Real.pi * (T + ((halaszM N : ℕ) : ℝ) + 1) ≤
        (A0 / 3) * (N : ℝ) := by
    calc
      _ ≤ 24 * (T + ((halaszM N : ℕ) : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
      _ ≤ 8 * (N : ℝ) := by nlinarith
      _ ≤ (A0 / 3) * (N : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hNpos.le
        linarith
  have hrange := exceptional_rangeSharp_of_margin
    (A0 / 3) T (((halaszM N : ℕ) : ℝ)) (N : ℝ) hmargin
  convert hrange using 1 <;> ring

/-- The low cutoff is at most one, so it obeys the same uniform sharp
frequency range. -/
theorem sliceA2_low_sharp_range
    (eps : ℝ) (X : ℕ) (A0 : ℝ) (heps : 0 < eps)
    (hX : 10 ^ 16 ≤ X) (hA0 : 27 ≤ A0) :
    2 * Real.pi * sliceA2LowCutoff eps +
          2 * Real.pi *
            (((halaszM (3 * (2 * X + 1)) : ℕ) : ℝ) + 1) ≤
        (A0 / 9) * ((3 * (2 * X + 1) : ℕ) : ℝ) := by
  have hXN0 : X ≤ 3 * (2 * X + 1) := by omega
  have hXN : 10 ^ 16 ≤ 3 * (2 * X + 1) := by
    exact hX.trans hXN0
  have hband := halaszM_band_le (3 * (2 * X + 1)) hXN 1 (by norm_num)
  have hband' : 7 *
      (((halaszM (3 * (2 * X + 1)) : ℕ) : ℝ) + 1) ≤
        ((3 * (2 * X + 1) : ℕ) : ℝ) := by simpa only [one_mul] using hband
  apply sliceA2_sharp_range_of_T_le X (sliceA2LowCutoff eps) A0 hband'
    (sliceA2LowCutoff_pos eps heps).le
  · exact (sliceA2LowCutoff_le_one eps heps).trans (by
      exact_mod_cast (show 1 ≤ X by omega))
  · exact hA0

/-- The fixed strength margin absorbs either of the two logarithmic losses. -/
theorem sliceA2_sharp_strength_of_logLoss_le
    (D A0 logLoss : ℝ) (hlog : logLoss ≤ Real.log 2 + 12)
    (hmargin : 18 * D + 18 * (Real.log 2 + 12) ≤ A0) :
    2 * D ≤ A0 / 9 - 2 * logLoss := by
  have hmargin' : 18 * D + 18 * logLoss ≤ A0 := by nlinarith
  linarith

end Tao2015

end MoltResearch
