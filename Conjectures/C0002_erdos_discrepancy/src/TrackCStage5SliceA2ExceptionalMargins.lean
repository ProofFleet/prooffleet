import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalCover

/-!
# Track R A2-V': eventual exceptional anchor margins

The lower endpoint of the remote interval tends to infinity.  This leaf
turns that fact into the two logarithmic margins and the uniform lower
bound for every exceptional Brun anchor.
-/

namespace MoltResearch

namespace Tao2015

open Filter Finset

theorem tendsto_exceptionalPrimeLower_base :
    Filter.Tendsto
      (fun A1 : ℕ => Real.exp
        ((Real.log (A1 : ℝ)) ^ (49 / 50 : ℝ)))
      Filter.atTop Filter.atTop := by
  exact Real.tendsto_exp_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 49 / 50)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

/-- The integral remote lower endpoint eventually dominates every fixed
real constant. -/
theorem exists_exceptionalPrimeLower_ge (C : ℝ) :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 →
      C ≤ (exceptionalPrimeLower A1 : ℝ) := by
  have hevent := tendsto_exceptionalPrimeLower_base.eventually_ge_atTop C
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨A0, hA0⟩ := hevent
  refine ⟨A0, fun A1 hA1 => (hA0 A1 hA1).trans ?_⟩
  unfold exceptionalPrimeLower
  rw [Nat.cast_max]
  exact (Nat.le_ceil _).trans (le_max_right _ _)

/-- Indices in the standard lower-shifted e-adic cover have lower anchors
at least six once the covered interval begins at twenty-one. -/
theorem eadicCellLowerAnchor_six_of_cover_lower
    (N P v : ℕ) (hN : 0 < N) (hP : 21 ≤ P)
    (hv : eadicCoverIndexLower (2 * N) P ≤ v) :
    6 ≤ eadicCellLowerAnchor N v := by
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hceil1 : 1 ≤ ⌈((2 * N : ℕ) : ℝ) * Real.log (P : ℝ)⌉₊ :=
    Nat.one_le_ceil_iff.mpr (mul_pos (by positivity) hlogP)
  have hceilv : ⌈((2 * N : ℕ) : ℝ) * Real.log (P : ℝ)⌉₊ ≤ v + 1 := by
    unfold eadicCoverIndexLower at hv
    omega
  have hraw : ((2 * N : ℕ) : ℝ) * Real.log (P : ℝ) ≤ (v : ℝ) + 1 :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceilv)
  have hden : (0 : ℝ) < 2 * (N : ℝ) := by positivity
  have hlogdiv : Real.log (P : ℝ) ≤
      ((v : ℝ) + 1) / (2 * (N : ℝ)) := by
    rw [le_div_iff₀ hden]
    convert hraw using 1 <;> push_cast <;> ring
  have hinv : (1 : ℝ) / (2 * (N : ℝ)) ≤ 1 := by
    rw [div_le_one hden]
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    nlinarith
  have hloglower : Real.log (P : ℝ) - 1 ≤
      (v : ℝ) / (2 * (N : ℝ)) := by
    have hsplit : ((v : ℝ) + 1) / (2 * (N : ℝ)) =
        (v : ℝ) / (2 * (N : ℝ)) + 1 / (2 * (N : ℝ)) := by ring
    rw [hsplit] at hlogdiv
    linarith
  have hexplower : (7 : ℝ) ≤
      Real.exp ((v : ℝ) / (2 * (N : ℝ))) := by
    have hexp := Real.exp_le_exp.mpr hloglower
    have hneg : (1 : ℝ) / 3 < Real.exp (-1) := by
      linarith [Real.exp_neg_one_gt_d9]
    have hP21 : (21 : ℝ) ≤ P := by exact_mod_cast hP
    have hseven : (7 : ℝ) ≤ (P : ℝ) * Real.exp (-1) := by
      nlinarith [Real.exp_pos (-1)]
    calc
      (7 : ℝ) ≤ (P : ℝ) * Real.exp (-1) := hseven
      _ = Real.exp (Real.log (P : ℝ) - 1) := by
        rw [Real.exp_sub, Real.exp_log hPpos, Real.exp_neg]
        simp only [div_eq_mul_inv]
      _ ≤ Real.exp ((v : ℝ) / (2 * (N : ℝ))) := hexp
  have hceil7 : 7 ≤
      ⌈Real.exp ((v : ℝ) / (2 * (N : ℝ)))⌉₊ := by
    exact_mod_cast hexplower.trans (Nat.le_ceil _)
  unfold eadicCellLowerAnchor
  omega

/-- A single base threshold supplies all elementary lower-endpoint and
anchor conditions used by the exceptional aggregate. -/
theorem exists_sliceA2Exceptional_anchor_margins
    (epsc eps rho0 : ℝ) :
    ∃ A0 : ℕ, ∀ A1 : ℕ, A0 ≤ A1 →
      1 ≤ Real.log (exceptionalPrimeLower A1 : ℝ) ∧
      2 * Real.log 6 ≤ Real.log (exceptionalPrimeLower A1 : ℝ) ∧
      (∀ v ∈ sliceA2ExceptionalI A1 epsc eps rho0,
        6 ≤ sliceA2ExceptionalAnchor A1 v epsc eps rho0) := by
  let C : ℝ := max 21 (Real.exp (max 1 (2 * Real.log 6)))
  obtain ⟨A0, hA0⟩ := exists_exceptionalPrimeLower_ge C
  refine ⟨A0, fun A1 hA1 => ?_⟩
  have hPC : C ≤ (exceptionalPrimeLower A1 : ℝ) := hA0 A1 hA1
  have hP21 : 21 ≤ exceptionalPrimeLower A1 := by
    exact_mod_cast (show (21 : ℝ) ≤ exceptionalPrimeLower A1 from
      (le_max_left _ _).trans hPC)
  have hPpos : (0 : ℝ) < exceptionalPrimeLower A1 := by positivity
  have hlogC : max 1 (2 * Real.log 6) ≤
      Real.log (exceptionalPrimeLower A1 : ℝ) := by
    apply (Real.le_log_iff_exp_le hPpos).2
    exact (le_max_right (21 : ℝ) _).trans hPC
  refine ⟨(le_max_left _ _).trans hlogC,
    (le_max_right _ _).trans hlogC, ?_⟩
  intro v hv
  apply eadicCellLowerAnchor_six_of_cover_lower
    (sliceA2ExceptionalN A1 epsc eps rho0)
    (exceptionalPrimeLower A1) v
    (sliceA2ExceptionalN_pos A1 epsc eps rho0) hP21
  rw [sliceA2ExceptionalI, Finset.mem_Ico] at hv
  simpa [sliceA2ExceptionalV0, exceptionalV0,
    sliceA2ExceptionalAnchor, exceptionalCellAnchor] using hv.1

end Tao2015

end MoltResearch
