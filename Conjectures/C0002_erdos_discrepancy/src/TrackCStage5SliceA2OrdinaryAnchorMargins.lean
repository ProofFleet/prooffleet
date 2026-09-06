import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryGrowthMargins

/-!
# Track R A2-V': uniform ordinary anchor margins

A single lower bound on the bottom endpoint supplies the dyadic anchor and
anchor-log hypotheses at every positive ordinary level.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- Every previous-cell anchor is at least six once the bottom endpoint is
at least twenty-one. -/
theorem sliceA2Ordinary_anchor_six
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ)
    (hP0 : 21 ≤ P0) (hj : 0 < j)
    (r : ℕ) (hr : r ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1)) :
    6 ≤ sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r := by
  unfold sliceA2OrdinaryAnchor
  apply eadicCellLowerAnchor_six_of_cover_lower
    (sliceA2OrdinaryN P0 ratio0 eta (j - 1) eps rho0)
    (sliceA2LadderP P0 ratio0 eta (j - 1)) r
    (sliceA2OrdinaryN_pos P0 ratio0 eta (j - 1) eps rho0)
    ((show P0 ≤ sliceA2LadderP P0 ratio0 eta (j - 1) from
      sliceA2LadderP_mono P0 ratio0 eta (by omega) (Nat.zero_le _)) |>.trans' hP0)
  have := (Finset.mem_Ico.mp hr).1
  simpa [sliceA2OrdinaryV0, ordinaryLevelV0] using this

/-- If `log P₀` has the fixed margin `log 6 + 256`, every ordinary anchor
has logarithm at least `256`. -/
theorem sliceA2Ordinary_anchor_log_margin
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ)
    (hP0 : 21 ≤ P0) (hj : 0 < j)
    (hlogP0 : Real.log 6 + 256 ≤ Real.log (P0 : ℝ))
    (r : ℕ) (hr : r ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1)) :
    256 ≤ Real.log
      (sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r : ℝ) := by
  let Pprev := sliceA2LadderP P0 ratio0 eta (j - 1)
  let Pc := sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r
  have hanchor : 6 ≤ Pc := by
    simpa [Pc] using sliceA2Ordinary_anchor_six
      P0 ratio0 eta j eps rho0 hP0 hj r hr
  have hP0prev : P0 ≤ Pprev := by
    dsimp [Pprev]
    exact sliceA2LadderP_mono P0 ratio0 eta (by omega) (Nat.zero_le _)
  have hPprev := sliceA2LadderP_le_six_mul_ordinaryAnchor
    P0 ratio0 eta j r eps rho0 (by omega) hr (by omega)
  have hP00 : (0 : ℝ) < P0 := by exact_mod_cast (show 0 < P0 by omega)
  have hPprev0 : (0 : ℝ) < Pprev := by exact_mod_cast (show 0 < Pprev by
    exact lt_of_lt_of_le (by omega) hP0prev)
  have hPc0 : (0 : ℝ) < Pc := by exact_mod_cast (show 0 < Pc by omega)
  have hlogP0prev : Real.log (P0 : ℝ) ≤ Real.log (Pprev : ℝ) :=
    Real.log_le_log hP00 (by exact_mod_cast hP0prev)
  have hlogPrevPc : Real.log (Pprev : ℝ) ≤
      Real.log 6 + Real.log (Pc : ℝ) := by
    calc
      Real.log (Pprev : ℝ) ≤ Real.log (6 * (Pc : ℝ)) :=
        Real.log_le_log hPprev0 (by simpa [Pprev, Pc] using hPprev)
      _ = Real.log 6 + Real.log (Pc : ℝ) :=
        Real.log_mul (by norm_num) hPc0.ne'
  linarith

/-- The previous lower endpoint has at most twice the logarithm of every
scheduled previous-cell anchor. -/
theorem sliceA2Ordinary_log_previous_le_two_log_anchor
    (P0 ratio0 eta j : ℕ) (eps rho0 : ℝ)
    (hP0 : 21 ≤ P0) (hj : 0 < j)
    (r : ℕ) (hr : r ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1)) :
    Real.log (sliceA2LadderP P0 ratio0 eta (j - 1) : ℝ) ≤
      2 * Real.log
        (sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r : ℝ) := by
  let Pprev := sliceA2LadderP P0 ratio0 eta (j - 1)
  let Pc := sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r
  have hanchor : 6 ≤ Pc := by
    simpa [Pc] using sliceA2Ordinary_anchor_six
      P0 ratio0 eta j eps rho0 hP0 hj r hr
  have hPprev := sliceA2LadderP_le_six_mul_ordinaryAnchor
    P0 ratio0 eta j r eps rho0 (by omega) hr (by omega)
  have hPprev0 : (0 : ℝ) < Pprev := by
    exact_mod_cast (show 0 < Pprev by
      dsimp [Pprev]
      have := sliceA2LadderP_two_le P0 ratio0 eta (j - 1) (by omega)
      omega)
  have hPc0 : (0 : ℝ) < Pc := by exact_mod_cast (show 0 < Pc by omega)
  have hlogSix : Real.log 6 ≤ Real.log (Pc : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hanchor)
  calc
    Real.log (Pprev : ℝ) ≤ Real.log (6 * (Pc : ℝ)) :=
      Real.log_le_log hPprev0 (by simpa [Pprev, Pc] using hPprev)
    _ = Real.log 6 + Real.log (Pc : ℝ) :=
      Real.log_mul (by norm_num) hPc0.ne'
    _ ≤ 2 * Real.log (Pc : ℝ) := by linarith

end Tao2015

end MoltResearch
