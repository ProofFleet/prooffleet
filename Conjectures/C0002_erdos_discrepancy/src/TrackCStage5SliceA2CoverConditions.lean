import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2CoverClose

/-!
# Track R A2-V': last-level cover conditions

The selected last ordinary lower endpoint is at least `(log A1)^40`, while
its upper endpoint is below `exp((log A1)^(1/3))`.  These two facts verify
all cellwise hypotheses of the `23/50` moment estimate with the common
choice `W = loglog A1 - 1`.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The last ordinary endpoint bounds turn the scalar remainder margin into
the complete logarithmic certificate for every last-level cell. -/
theorem sliceA2OrdinaryCover_logEnvelope_of_last_level
    (P0 ratio0 eta J A1 r : ℕ) (eps rho0 T : ℝ)
    (hP0 : 2 ≤ P0) (hJ : 0 < J)
    (hr : r ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (J - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (J - 1) eps rho0 + 1))
    (hT : 1 ≤ T)
    (hX : 12 ≤ Real.log (A1 : ℝ))
    (hlogX : 7 ≤ Real.log (Real.log (A1 : ℝ)))
    (hreaches : ordinaryLadderCutoff A1 ≤
      (sliceA2LadderP P0 ratio0 eta (J - 1) : ℝ))
    (hQ : (sliceA2LadderQ P0 ratio0 eta (J - 1) : ℝ) + 1 ≤
      Real.exp ((Real.log (A1 : ℝ)) ^ (1 / 3 : ℝ)))
    (hLlower : Real.log (A1 : ℝ) / 2 ≤ Real.log (2 * T))
    (hLupper : Real.log (2 * T) ≤ 3 * Real.log (A1 : ℝ))
    (hremX : (101 / 125 : ℝ) *
          (Real.log (A1 : ℝ)) ^ (1 / 3 : ℝ) +
        8 * Real.log (Real.log (A1 : ℝ)) + 6 ≤
          Real.log (A1 : ℝ) / 2000) :
    sliceA2MomentLogEnvelope
        (sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r)
        (sliceA2OrdinaryCoverMoment P0 ratio0 eta J eps rho0 T r)
        (sliceA2OrdinaryCoverWeight P0 ratio0 eta J r eps rho0) ≤
      (23 / 50 : ℝ) * Real.log (2 * T) := by
  let X := Real.log (A1 : ℝ)
  let W := Real.log X - 1
  let P := sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r
  let Q := sliceA2LadderQ P0 ratio0 eta (J - 1)
  let ell := sliceA2OrdinaryCoverMoment P0 ratio0 eta J eps rho0 T r
  have hXpos : 0 < X := by dsimp [X]; linarith
  have hXone : 1 ≤ X := by dsimp [X]; linarith
  have hW0 : 0 ≤ W := by dsimp [W, X]; linarith
  have hcut21 : (21 : ℝ) ≤ ordinaryLadderCutoff A1 := by
    unfold ordinaryLadderCutoff
    have hx2 : (21 : ℝ) ≤ X ^ (2 : ℕ) := by nlinarith [sq_nonneg (X - 12)]
    exact hx2.trans (pow_le_pow_right₀ hXone (by norm_num : (2 : ℕ) ≤ 40))
  have hPlevel21 : 21 ≤ sliceA2LadderP P0 ratio0 eta (J - 1) := by
    exact_mod_cast hcut21.trans hreaches
  have hanchorRaw : 6 ≤
      eadicCellLowerAnchor
        (sliceA2OrdinaryN P0 ratio0 eta (J - 1) eps rho0) r := by
    apply eadicCellLowerAnchor_six_of_cover_lower
      (sliceA2OrdinaryN P0 ratio0 eta (J - 1) eps rho0)
      (sliceA2LadderP P0 ratio0 eta (J - 1)) r
      (sliceA2OrdinaryN_pos P0 ratio0 eta (J - 1) eps rho0)
      hPlevel21
    have := (Finset.mem_Ico.mp hr).1
    simpa [sliceA2OrdinaryV0, ordinaryLevelV0] using this
  have hanchor : 6 ≤ P := by simpa [P, sliceA2OrdinaryAnchor] using hanchorRaw
  have hPlevel := sliceA2LadderP_le_six_mul_ordinaryAnchor
    P0 ratio0 eta J r eps rho0 hP0 hr (by omega)
  have hPlevelPos : (0 : ℝ) <
      sliceA2LadderP P0 ratio0 eta (J - 1) := by positivity
  have hPpos : (0 : ℝ) < P := by
    have : (0 : ℝ) < 6 * (P : ℝ) := hPlevelPos.trans_le (by
      simpa [P] using hPlevel)
    positivity
  have hlogLevel : 40 * Real.log X ≤
      Real.log (sliceA2LadderP P0 ratio0 eta (J - 1) : ℝ) := by
    have hcutPos : 0 < ordinaryLadderCutoff A1 := by
      unfold ordinaryLadderCutoff
      positivity
    have hlogs := Real.log_le_log hcutPos hreaches
    unfold ordinaryLadderCutoff at hlogs
    rw [Real.log_pow] at hlogs
    norm_num at hlogs
    simpa [X] using hlogs
  have hlogSixP :
      Real.log (sliceA2LadderP P0 ratio0 eta (J - 1) : ℝ) ≤
        Real.log 6 + Real.log (P : ℝ) := by
    calc
      Real.log (sliceA2LadderP P0 ratio0 eta (J - 1) : ℝ) ≤
          Real.log (6 * (P : ℝ)) :=
        Real.log_le_log hPlevelPos (by simpa [P] using hPlevel)
      _ = Real.log 6 + Real.log (P : ℝ) :=
        Real.log_mul (by norm_num) hPpos.ne'
  have hlog6 : Real.log 6 ≤ 3 := by
    exact (Real.log_le_log (by norm_num) (by norm_num : (6 : ℝ) ≤ 9)).trans
      (log_nine_le.trans (by norm_num))
  have hPlogLower : 40 * Real.log X - 3 ≤ Real.log (P : ℝ) := by linarith
  have hlogAnchor : 256 ≤ Real.log (P : ℝ) := by
    linarith
  have hWsmall : 40 * W ≤ Real.log (P : ℝ) := by
    dsimp [W]
    linarith
  have hQpos : (0 : ℝ) < Q := by
    exact_mod_cast (show 0 < Q by
      have hp := sliceA2LadderP_two_le P0 ratio0 eta (J - 1) hP0
      exact lt_of_lt_of_le (by omega) (sliceA2LadderP_le_Q P0 ratio0 eta (J - 1)))
  have hPQ : (P : ℝ) ≤ Q := by
    simpa [P, Q] using sliceA2OrdinaryAnchor_le_Q
      P0 ratio0 eta J eps rho0 hP0 hJ r hr
  have hlogPQ : Real.log (P : ℝ) ≤ Real.log (Q : ℝ) :=
    Real.log_le_log hPpos hPQ
  have hlogQ : Real.log (Q : ℝ) ≤ X ^ (1 / 3 : ℝ) := by
    have hQexp : (Q : ℝ) ≤ Real.exp (X ^ (1 / 3 : ℝ)) := by
      dsimp [Q, X] at hQ ⊢
      linarith
    calc
      Real.log (Q : ℝ) ≤ Real.log (Real.exp (X ^ (1 / 3 : ℝ))) :=
        Real.log_le_log hQpos hQexp
      _ = X ^ (1 / 3 : ℝ) := Real.log_exp _
  have hlogPupper : Real.log (P : ℝ) ≤ X ^ (1 / 3 : ℝ) :=
    hlogPQ.trans hlogQ
  have hellRaw := adaptivePrimeMoment_cast_lt_log_ratio_add_two P T
    (by omega) hT
  have hlogP36 : 36 * Real.log X ≤ Real.log (P : ℝ) := by
    have : (3 : ℝ) ≤ Real.log X := by
      change (3 : ℝ) ≤ Real.log (Real.log (A1 : ℝ))
      linarith
    linarith
  have hellX : (ell : ℝ) ≤ X / 3 := by
    have hdiv : Real.log (2 * T) / Real.log (P : ℝ) ≤ X / 12 := by
      have hden : 0 < Real.log (P : ℝ) := by linarith
      apply (div_le_iff₀ hden).2
      have hmul := mul_le_mul_of_nonneg_left hlogP36 (by
        positivity : 0 ≤ X / 12)
      nlinarith
    have hX12 : 12 ≤ X := by simpa [X] using hX
    have hell' : (ell : ℝ) ≤
        Real.log (2 * T) / Real.log (P : ℝ) + 2 := by
      simpa [ell, sliceA2OrdinaryCoverMoment] using hellRaw.le
    linarith
  have hlogell : Real.log (ell : ℝ) ≤ W := by
    have hellPos : (0 : ℝ) < ell := by
      exact_mod_cast (show 0 < ell by
        have := sliceA2OrdinaryCoverMoment_one_le
          P0 ratio0 eta J eps rho0 T r
        dsimp [ell]
        omega)
    have hthird : X / 3 < X / Real.exp 1 := by
      have he := Real.exp_one_lt_three
      have hX0 : 0 < X := hXpos
      exact div_lt_div_of_pos_left hX0 (Real.exp_pos 1) he
    calc
      Real.log (ell : ℝ) ≤ Real.log (X / 3) :=
        Real.log_le_log hellPos hellX
      _ ≤ Real.log (X / Real.exp 1) :=
        Real.log_le_log (by positivity) hthird.le
      _ = W := by
        dsimp [W]
        rw [Real.log_div hXpos.ne' (Real.exp_ne_zero _), Real.log_exp]
  have hy1 : 1 ≤ X ^ (1 / 3 : ℝ) :=
    Real.one_le_rpow hXone (by norm_num)
  have hlogTwoPInner : Real.log (2 * (P : ℝ)) ≤
      2 * X ^ (1 / 3 : ℝ) := by
    rw [Real.log_mul (by norm_num) hPpos.ne']
    have hlog2 : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
    linarith
  have hloglogP : Real.log (Real.log (2 * (P : ℝ))) ≤ W := by
    have hinnerPos : 0 < Real.log (2 * (P : ℝ)) :=
      Real.log_pos (by nlinarith [show (6 : ℝ) ≤ P by exact_mod_cast hanchor])
    calc
      Real.log (Real.log (2 * (P : ℝ))) ≤
          Real.log (2 * X ^ (1 / 3 : ℝ)) :=
        Real.log_le_log hinnerPos hlogTwoPInner
      _ = Real.log 2 + (1 / 3 : ℝ) * Real.log X := by
        rw [Real.log_mul (by norm_num) (ne_of_gt (by positivity)),
          Real.log_rpow hXpos]
      _ ≤ W := by
        dsimp [W]
        have hlog2 : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
        linarith
  have hremainder : (101 / 125 : ℝ) * Real.log (P : ℝ) +
      8 * W + 14 ≤ Real.log (2 * T) / 1000 := by
    have hleft : (101 / 125 : ℝ) * Real.log (P : ℝ) +
        8 * W + 14 ≤ (101 / 125 : ℝ) * X ^ (1 / 3 : ℝ) +
          8 * Real.log X + 6 := by
      dsimp [W]
      linarith
    calc
      _ ≤ (101 / 125 : ℝ) * X ^ (1 / 3 : ℝ) +
          8 * Real.log X + 6 := hleft
      _ ≤ X / 2000 := by simpa [X] using hremX
      _ ≤ Real.log (2 * T) / 1000 := by linarith
  apply sliceA2OrdinaryCover_logEnvelope_le
    P0 ratio0 eta J r eps rho0 T W hT hanchor hlogAnchor hW0
  · simpa [ell] using hlogell
  · simpa [P] using hloglogP
  · simpa [P] using hWsmall
  · simpa [P] using hremainder

end Tao2015

end MoltResearch
