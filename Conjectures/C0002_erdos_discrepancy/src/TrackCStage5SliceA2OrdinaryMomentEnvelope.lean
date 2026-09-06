import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OrdinaryAnchorMargins

/-!
# Track R A2-V': ordinary borrowed-moment envelope

The exact adjacent ladder ratios give a scale-free upper bound for every
borrowed moment.  This is the `L_j` used in the later-level fit.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- Explicit real envelope for the borrowed moment at positive level `j`. -/
noncomputable def sliceA2OrdinaryMomentEnvelope
    (ratio0 eta j : ℕ) : ℝ :=
  4 + 200 * (j : ℝ) ^ 2 *
    (sliceA2LadderRatio ratio0 eta (j - 1) : ℝ) *
    (sliceA2LadderRatio ratio0 eta j : ℝ)

theorem sliceA2OrdinaryMomentEnvelope_one_le
    (ratio0 eta j : ℕ) :
    1 ≤ sliceA2OrdinaryMomentEnvelope ratio0 eta j := by
  unfold sliceA2OrdinaryMomentEnvelope
  have hnonneg : 0 ≤ 200 * (j : ℝ) ^ 2 *
      (sliceA2LadderRatio ratio0 eta (j - 1) : ℝ) *
      (sliceA2LadderRatio ratio0 eta j : ℝ) := by positivity
  linarith

/-- Exact logarithmic width of a positive ladder level. -/
theorem sliceA2LadderQ_log_formula
    (P0 ratio0 eta j : ℕ) (hj : 0 < j) :
    Real.log (sliceA2LadderQ P0 ratio0 eta j : ℝ) =
      ((100 * j ^ 2 * sliceA2LadderRatio ratio0 eta (j - 1) *
          sliceA2LadderRatio ratio0 eta j : ℕ) : ℝ) *
        Real.log (sliceA2LadderP P0 ratio0 eta (j - 1) : ℝ) := by
  have hpred : j - 1 + 1 = j := by omega
  have hPshape : sliceA2LadderP P0 ratio0 eta j =
      sliceA2LadderQ P0 ratio0 eta (j - 1) ^ (100 * j ^ 2) := by
    simpa only [hpred] using sliceA2LadderP_succ P0 ratio0 eta (j - 1)
  calc
    Real.log (sliceA2LadderQ P0 ratio0 eta j : ℝ) =
        (sliceA2LadderRatio ratio0 eta j : ℝ) *
          Real.log (sliceA2LadderP P0 ratio0 eta j : ℝ) := by
      rw [sliceA2LadderQ_eq, Nat.cast_pow, Real.log_pow]
    _ = (sliceA2LadderRatio ratio0 eta j : ℝ) *
        ((100 * j ^ 2 : ℕ) : ℝ) *
          Real.log (sliceA2LadderQ P0 ratio0 eta (j - 1) : ℝ) := by
      rw [hPshape, Nat.cast_pow, Real.log_pow]
      ring
    _ = _ := by
      rw [sliceA2LadderQ_eq, Nat.cast_pow, Real.log_pow]
      push_cast
      ring

/-- A current cell's empty-cell-safe scale is at most three times its level
upper endpoint. -/
theorem sliceA2OrdinaryCellScale_le_three_mul_Q
    (P0 ratio0 eta j v : ℕ) (eps rho0 : ℝ)
    (hP0 : 2 ≤ P0)
    (hv : v ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 + 1)) :
    (sliceA2OrdinaryCellScale P0 ratio0 eta j eps rho0 v : ℝ) ≤
      3 * (sliceA2LadderQ P0 ratio0 eta j : ℝ) := by
  let N := sliceA2OrdinaryN P0 ratio0 eta j eps rho0
  let Q := sliceA2LadderQ P0 ratio0 eta j
  let t := sliceA2OrdinaryCellScale P0 ratio0 eta j eps rho0 v
  have hN : 0 < N := by
    simpa [N] using sliceA2OrdinaryN_pos P0 ratio0 eta j eps rho0
  have hQ2 : 2 ≤ Q :=
    (sliceA2LadderP_two_le P0 ratio0 eta j hP0).trans
      (sliceA2LadderP_le_Q P0 ratio0 eta j)
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hvUpper : v ≤ ordinaryLevelV1 Q N := by
    have hvle : v ≤ sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 := by
      have := (Finset.mem_Ico.mp hv).2
      omega
    simpa [sliceA2OrdinaryV1, Q, N] using hvle
  have hfloor : (v : ℝ) ≤ (2 * N : ℕ) * Real.log (Q : ℝ) := by
    unfold ordinaryLevelV1 eadicCoverIndexUpper at hvUpper
    exact (by exact_mod_cast hvUpper :
      (v : ℝ) ≤ ⌊(2 * N : ℕ) * Real.log (Q : ℝ)⌋₊) |>.trans
        (Nat.floor_le (by positivity))
  have hexponent : ((v : ℝ) + 1) / (2 * (N : ℝ)) ≤
      Real.log (Q : ℝ) + 1 := by
    have hden : (0 : ℝ) < 2 * (N : ℝ) := by positivity
    have hfrac : (1 : ℝ) / (2 * (N : ℝ)) ≤ 1 := by
      rw [div_le_one hden]
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      nlinarith
    have hvdiv : (v : ℝ) / (2 * (N : ℝ)) ≤ Real.log (Q : ℝ) := by
      rw [div_le_iff₀ hden]
      convert hfloor using 1 <;> push_cast <;> ring
    rw [add_div]
    linarith
  have ht := sliceA2OrdinaryCellScale_le_exp
    P0 ratio0 eta j eps rho0 hP0 v hv
  calc
    (t : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ))) := by
      simpa [t, N] using ht
    _ ≤ Real.exp (Real.log (Q : ℝ) + 1) :=
      Real.exp_le_exp.mpr hexponent
    _ = (Q : ℝ) * Real.exp 1 := by rw [Real.exp_add, Real.exp_log hQ0]
    _ ≤ 3 * (Q : ℝ) := by
      have := Real.exp_one_lt_three.le
      nlinarith

/-- Every borrowed moment is bounded by the explicit adjacent-ratio
envelope. -/
theorem sliceA2LaterMoment_le_envelope
    (P0 ratio0 eta j : ℕ) (eps rho0 tau : ℝ)
    (hP0 : 21 ≤ P0) (hj : 0 < j) (htau0 : 0 ≤ tau) (htau : tau ≤ 1)
    (hx : ∀ v ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 + 1),
      1 ≤ (sliceA2OrdinaryCellScale P0 ratio0 eta j eps rho0 v : ℝ) * tau) :
    ∀ r ∈ Finset.Ico
        (sliceA2OrdinaryV0 P0 ratio0 eta (j - 1) eps rho0)
        (sliceA2OrdinaryV1 P0 ratio0 eta (j - 1) eps rho0 + 1),
      ∀ v ∈ Finset.Ico
        (sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0)
        (sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0 + 1),
      (sliceA2LaterMoment
        (sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0)
        (sliceA2OrdinaryCellScale P0 ratio0 eta j eps rho0) tau r v : ℝ) ≤
        sliceA2OrdinaryMomentEnvelope ratio0 eta j := by
  intro r hr v hv
  let Pprev := sliceA2LadderP P0 ratio0 eta (j - 1)
  let Pc := sliceA2OrdinaryAnchor P0 ratio0 eta j eps rho0 r
  let Q := sliceA2LadderQ P0 ratio0 eta j
  let t := sliceA2OrdinaryCellScale P0 ratio0 eta j eps rho0 v
  let C : ℝ :=
    (100 * j ^ 2 * sliceA2LadderRatio ratio0 eta (j - 1) *
      sliceA2LadderRatio ratio0 eta j : ℕ)
  have hPc6 : 6 ≤ Pc := by
    simpa [Pc] using sliceA2Ordinary_anchor_six
      P0 ratio0 eta j eps rho0 hP0 hj r hr
  have hPc0 : (0 : ℝ) < Pc := by exact_mod_cast (show 0 < Pc by omega)
  have hlogPc : 0 < Real.log (Pc : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Pc by omega))
  have ht0 : (0 : ℝ) < t := by
    dsimp [t, sliceA2OrdinaryCellScale]
    exact_mod_cast (show 0 < max (sliceA2LadderP P0 ratio0 eta j)
      (sliceA2OrdinaryRepresentative P0 ratio0 eta j eps rho0 v) by
        have := sliceA2LadderP_two_le P0 ratio0 eta j (by omega)
        omega)
  have hxt : (t : ℝ) * tau ≤ t := by
    nlinarith
  have hmoment := ordinaryBorrowMoment_le_log_scale Pc (by omega)
    ((t : ℝ) * tau) t (hx v hv) hxt
  have htQ := sliceA2OrdinaryCellScale_le_three_mul_Q
    P0 ratio0 eta j v eps rho0 (by omega) hv
  have hQ0 : (0 : ℝ) < Q := by
    dsimp [Q]
    exact_mod_cast (show 0 < sliceA2LadderQ P0 ratio0 eta j by
      have hp := sliceA2LadderP_two_le P0 ratio0 eta j (by omega)
      have hpq := sliceA2LadderP_le_Q P0 ratio0 eta j
      omega)
  have hlogt : Real.log (t : ℝ) ≤ Real.log 3 + Real.log (Q : ℝ) := by
    calc
      Real.log (t : ℝ) ≤ Real.log (3 * (Q : ℝ)) :=
        Real.log_le_log ht0 (by simpa [t, Q] using htQ)
      _ = Real.log 3 + Real.log (Q : ℝ) :=
        Real.log_mul (by norm_num) hQ0.ne'
  have hlogQ : Real.log (Q : ℝ) = C * Real.log (Pprev : ℝ) := by
    simpa [Q, C, Pprev] using
      sliceA2LadderQ_log_formula P0 ratio0 eta j hj
  have hPprev3 : (3 : ℝ) ≤ Pprev := by
    exact_mod_cast (show 3 ≤ Pprev by
      have hmono := sliceA2LadderP_mono P0 ratio0 eta (by omega)
      have hP0prev : P0 ≤ Pprev := by
        simpa [Pprev] using hmono (Nat.zero_le (j - 1))
      omega)
  have hlog3prev : Real.log 3 ≤ Real.log (Pprev : ℝ) :=
    Real.log_le_log (by norm_num) hPprev3
  have hC0 : 0 ≤ C := by positivity
  have hlogtPrev : Real.log (t : ℝ) ≤
      (C + 1) * Real.log (Pprev : ℝ) := by
    rw [hlogQ] at hlogt
    nlinarith
  have hprevAnchor := sliceA2Ordinary_log_previous_le_two_log_anchor
    P0 ratio0 eta j eps rho0 hP0 hj r hr
  have hratio : Real.log (t : ℝ) / Real.log (Pc : ℝ) ≤ 2 * (C + 1) := by
    rw [div_le_iff₀ hlogPc]
    calc
      Real.log (t : ℝ) ≤ (C + 1) * Real.log (Pprev : ℝ) := hlogtPrev
      _ ≤ (C + 1) * (2 * Real.log (Pc : ℝ)) := by gcongr
      _ = 2 * (C + 1) * Real.log (Pc : ℝ) := by ring
  unfold sliceA2LaterMoment
  unfold sliceA2OrdinaryMomentEnvelope
  have hCshape : 2 * (C + 1) + 2 =
      4 + 200 * (j : ℝ) ^ 2 *
        (sliceA2LadderRatio ratio0 eta (j - 1) : ℝ) *
        (sliceA2LadderRatio ratio0 eta j : ℝ) := by
    dsimp [C]
    push_cast
    ring
  rw [← hCshape]
  exact hmoment.trans (by linarith)

end Tao2015

end MoltResearch
