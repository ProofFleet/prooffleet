import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2CoverWeight

/-!
# Track R A2-V': close one ordinary cover moment

The universal moment factors cost `0.054 log(2T)`, while the ordinary weight
costs `0.404 log(2T)`.  A final `0.001 log(2T)` slot absorbs the subpower
anchor and logarithmic terms, leaving the advertised `0.46` exponent.
-/

namespace MoltResearch

namespace Tao2015

/-- Abstract arithmetic that converts the recorded moment estimates into a
`23/50`-power cover envelope. -/
theorem sliceA2MomentLogEnvelope_le_twenty_three_fiftieths
    (P ell : ℕ) (V L W : ℝ) (hP : 2 ≤ P) (hellOne : 1 ≤ ell)
    (hV : 0 < V) (hL : 0 ≤ L)
    (hlogP : 256 ≤ Real.log (P : ℝ))
    (hell : (ell : ℝ) ≤ L / Real.log (P : ℝ) + 2)
    (hW : 0 ≤ W)
    (hlogell : Real.log (ell : ℝ) ≤ W)
    (hloglogP : Real.log (Real.log (2 * (P : ℝ))) ≤ W)
    (hWsmall : 40 * W ≤ Real.log (P : ℝ))
    (hweight : -(2 * (ell : ℝ)) * Real.log V ≤
      (101 / 250 : ℝ) * L +
        (101 / 125 : ℝ) * Real.log (P : ℝ))
    (hremainder : (101 / 125 : ℝ) * Real.log (P : ℝ) +
        8 * W + 14 ≤ L / 1000) :
    sliceA2MomentLogEnvelope P ell V ≤ (23 / 50 : ℝ) * L := by
  have hlogPpos : 0 < Real.log (P : ℝ) := by linarith
  have hell0 : (0 : ℝ) ≤ ell := by positivity
  have hlog2 : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
  have hlog9 : Real.log 9 ≤ 3 := log_nine_le.trans (by norm_num)
  have hellCoarse : (ell : ℝ) + 2 ≤ L / 250 + 4 := by
    have hdiv : L / Real.log (P : ℝ) ≤ L / 250 := by
      apply div_le_div_of_nonneg_left hL (by norm_num)
      linarith
    linarith
  have hfirst : ((ell : ℝ) + 2) * Real.log 2 ≤ L / 250 + 4 := by
    exact (mul_le_mul_of_nonneg_left hlog2 (by positivity)).trans (by
      simpa only [mul_one] using hellCoarse)
  have hratioTerm : 2 * (L / Real.log (P : ℝ)) * W ≤ L / 20 := by
    have hcross : 2 * L * W ≤ (L / 20) * Real.log (P : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hWsmall hL
      nlinarith
    rw [show 2 * (L / Real.log (P : ℝ)) * W =
      (2 * L * W) / Real.log (P : ℝ) by ring]
    exact (div_le_iff₀ hlogPpos).2 hcross
  have hfac : 2 * (ell : ℝ) * Real.log (ell : ℝ) ≤
      L / 20 + 4 * W := by
    have hmulLog := mul_le_mul_of_nonneg_left hlogell
      (by positivity : 0 ≤ 2 * (ell : ℝ))
    have hmulEll := mul_le_mul_of_nonneg_right hell
      (by positivity : 0 ≤ 2 * W)
    calc
      2 * (ell : ℝ) * Real.log (ell : ℝ) ≤
          2 * (ell : ℝ) * W := hmulLog
      _ ≤ 2 * (L / Real.log (P : ℝ) + 2) * W := by
        nlinarith
      _ = 2 * (L / Real.log (P : ℝ)) * W + 4 * W := by ring
      _ ≤ L / 20 + 4 * W := by linarith
  have hlast : 2 * (Real.log 9 + Real.log (ell : ℝ) +
      Real.log (Real.log (2 * (P : ℝ)))) ≤ 6 + 4 * W := by
    linarith
  have hraw := sliceA2MomentLogEnvelope_le_of_weightLoss
    P ell V ((101 / 250 : ℝ) * L +
      (101 / 125 : ℝ) * Real.log (P : ℝ))
      hP hellOne hV hweight
  calc
    sliceA2MomentLogEnvelope P ell V ≤
        Real.pi + ((ell : ℝ) + 2) * Real.log 2 +
          2 * (ell : ℝ) * Real.log (ell : ℝ) +
          2 * (Real.log 9 + Real.log (ell : ℝ) +
            Real.log (Real.log (2 * (P : ℝ)))) +
          ((101 / 250 : ℝ) * L +
            (101 / 125 : ℝ) * Real.log (P : ℝ)) := hraw
    _ ≤ 4 + (L / 250 + 4) + (L / 20 + 4 * W) +
        (6 + 4 * W) + ((101 / 250 : ℝ) * L +
          (101 / 125 : ℝ) * Real.log (P : ℝ)) := by
      gcongr
      exact Real.pi_lt_four.le
    _ ≤ 4 + (L / 250 + 4) + (L / 20 + 4 * W) +
        (6 + 4 * W) + ((101 / 250 : ℝ) * L +
          (L / 1000 - 8 * W - 14)) := by linarith
    _ = (459 / 1000 : ℝ) * L := by ring
    _ ≤ (23 / 50 : ℝ) * L := by nlinarith

/-- The last ordinary cell's concrete adaptive moment satisfies the
`23/50` logarithmic envelope under the displayed subpower remainder. -/
theorem sliceA2OrdinaryCover_logEnvelope_le
    (P0 ratio0 eta J r : ℕ) (eps rho0 T W : ℝ)
    (hT : 1 ≤ T)
    (hanchor : 6 ≤ sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r)
    (hlogAnchor : 256 ≤ Real.log
      (sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r : ℝ))
    (hW : 0 ≤ W)
    (hlogell : Real.log
      (sliceA2OrdinaryCoverMoment P0 ratio0 eta J eps rho0 T r : ℝ) ≤ W)
    (hloglogP : Real.log (Real.log (2 *
      (sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r : ℝ))) ≤ W)
    (hWsmall : 40 * W ≤ Real.log
      (sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r : ℝ))
    (hremainder : (101 / 125 : ℝ) * Real.log
          (sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r : ℝ) +
        8 * W + 14 ≤ Real.log (2 * T) / 1000) :
    sliceA2MomentLogEnvelope
        (sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r)
        (sliceA2OrdinaryCoverMoment P0 ratio0 eta J eps rho0 T r)
        (sliceA2OrdinaryCoverWeight P0 ratio0 eta J r eps rho0) ≤
      (23 / 50 : ℝ) * Real.log (2 * T) := by
  let P := sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r
  let ell := sliceA2OrdinaryCoverMoment P0 ratio0 eta J eps rho0 T r
  let V := sliceA2OrdinaryCoverWeight P0 ratio0 eta J r eps rho0
  have hPtwo : 2 ≤ P := by dsimp [P]; omega
  have hlogPpos : 0 < Real.log (P : ℝ) := by linarith
  have hL : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
  have hell := adaptivePrimeMoment_cast_lt_log_ratio_add_two P T hPtwo hT
  apply sliceA2MomentLogEnvelope_le_twenty_three_fiftieths
    P ell V (Real.log (2 * T)) W hPtwo
    (sliceA2OrdinaryCoverMoment_one_le P0 ratio0 eta J eps rho0 T r)
    (by dsimp [V, sliceA2OrdinaryCoverWeight]; positivity) hL hlogAnchor hell.le
    hW
  · simpa [ell] using hlogell
  · simpa [P] using hloglogP
  · simpa [P] using hWsmall
  · simpa [P, ell, V] using sliceA2OrdinaryCover_weightLoss_le
      P0 ratio0 eta J r eps rho0 T hT hanchor hlogAnchor
  · simpa [P] using hremainder

end Tao2015

end MoltResearch
