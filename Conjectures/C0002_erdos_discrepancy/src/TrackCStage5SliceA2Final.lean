import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2HeightChoice
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2LadderDensity
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5MajorArcEDP

/-!
# Track R A2-V': the slice mean-square theorem

The polynomial height choice fixes the bottom scale.  The density and
remote-prime thresholds are then included in the same analytic scale
witness, so all four clauses use one canonical level list.
-/

namespace MoltResearch

namespace Tao2015

open Finset ExpSums

/-- A sufficiently large height puts the fourth-root bottom scale above
any prescribed polylogarithmic prime cutoff. -/
theorem exists_sliceA2HeightP0_above_polylog
    (epsc C : ℝ) (B : ℕ) (hC : 0 < C) :
    ∃ h0 : ℕ, ∀ h : ℕ, h0 ≤ h →
      C * Real.log (h : ℝ) ^ B < sliceA2HeightP0 epsc h := by
  let R := sliceA2HeightRatio epsc
  let n := 4 * R
  let M := 2 * C
  have hn : 0 < n := by
    dsimp [n, R]
    have := sliceA2HeightRatio_three_le epsc
    positivity
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨hlog, hhlog⟩ := ExpSums.exists_log_pow_le (B * n)
    (1 / M ^ n) (by positivity)
  refine ⟨max 3 hlog, fun h hh => ?_⟩
  have hhlog' : hlog ≤ h := (le_max_right 3 hlog).trans hh
  have hh3 : 3 ≤ h := (le_max_left 3 hlog).trans hh
  have hlog0 : 0 ≤ Real.log (h : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ h by omega))
  have hraw := hhlog h hhlog'
  have hpowlog : (Real.log (h : ℝ) ^ B) ^ n =
      Real.log (h : ℝ) ^ (B * n) := by rw [← pow_mul]
  have hMn : 0 < M ^ n := by positivity
  have hscaled : (M * Real.log (h : ℝ) ^ B) ^ n ≤ (h : ℝ) := by
    rw [mul_pow, hpowlog]
    calc
      M ^ n * Real.log (h : ℝ) ^ (B * n) ≤
          M ^ n * (1 / M ^ n * (h : ℝ)) :=
        mul_le_mul_of_nonneg_left hraw hMn.le
      _ = h := by field_simp
  let z := M * Real.log (h : ℝ) ^ B
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hh0 : (0 : ℝ) ≤ h := by positivity
  have hroot : z ≤ (h : ℝ) ^ (1 / (n : ℝ)) := by
    have hr := Real.rpow_le_rpow (pow_nonneg hz0 n) hscaled
      (by positivity : (0 : ℝ) ≤ ((n : ℕ) : ℝ)⁻¹)
    calc
      z = (z ^ n) ^ (((n : ℕ) : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast hz0 hn.ne').symm
      _ ≤ (h : ℝ) ^ (((n : ℕ) : ℝ)⁻¹) := hr
      _ = (h : ℝ) ^ (1 / (n : ℝ)) := by norm_num
  have hrootPos : 0 < (h : ℝ) ^ (1 / (n : ℝ)) := by positivity
  have hcut : C * Real.log (h : ℝ) ^ B <
      (h : ℝ) ^ (1 / (n : ℝ)) := by
    dsimp [z, M] at hroot
    have hterm : 0 ≤ C * Real.log (h : ℝ) ^ B := by positivity
    nlinarith
  exact hcut.trans_le (by
    simpa [n, R] using sliceA2HeightP0_root_le epsc h)

set_option maxHeartbeats 2000000 in
/-- The complete A.2 slice estimate, conditional only on the two declared
large-values interfaces. -/
theorem sliceMeanSquareA2
    [HalaszLargeValuesAssumption] [PrimeLargeValuesAssumption] :
    SliceMeanSquareA2 := by
  obtain ⟨Cp, hCp1, hprimeBound⟩ := PrimeLargeValuesAssumption.bound
  intro epsc hepsc B C hC
  obtain ⟨Qlog0, hQlog0, hlogFit⟩ := exists_log_six_le_twentieth_rpow
  let HC := sliceA2HeightPowerConstant Cp epsc Qlog0
  let K := sliceA2HeightPower epsc
  obtain ⟨hcut, hhcut⟩ := exists_sliceA2HeightP0_above_polylog epsc C B hC
  let hconst := ⌈HC⌉₊ + 1
  let h1 := max hcut hconst
  refine ⟨h1, HC, K, ?_, ?_⟩
  · simpa [HC] using sliceA2HeightPowerConstant_pos Cp epsc Qlog0
  intro eps heps h hh1 hpower
  let e := sliceA2EffectiveEps eps
  let rho := sliceA2CanonicalRho eps
  let eta := sliceA2ExceptionalLadderEta Cp e epsc (e / 100) rho
  let P0 := sliceA2HeightP0 epsc h
  have he : 0 < e := by
    simpa [e] using (sliceA2EffectiveEps_bounds eps heps).1
  have hrho : 0 < rho := by
    simpa [rho] using sliceA2CanonicalRho_pos eps heps
  have hheight : HC / e ^ K ≤ (h : ℝ) := by
    by_cases heps1 : eps ≤ 1
    · simpa [HC, K, e, sliceA2EffectiveEps, min_eq_left heps1] using hpower
    · have hHCceil : HC ≤ (hconst : ℝ) := by
        dsimp [hconst]
        exact (Nat.le_ceil HC).trans (by exact_mod_cast Nat.le_succ _)
      have hhconst : hconst ≤ h := (le_max_right hcut hconst).trans hh1
      have hHCH : HC ≤ (h : ℝ) := hHCceil.trans (by exact_mod_cast hhconst)
      have hmine : e = 1 := by
        dsimp [e, sliceA2EffectiveEps]
        rw [min_eq_right]
        exact le_of_not_ge heps1
      simpa [hmine] using hHCH
  have hclosed := sliceA2HeightClosed_of_power
    Cp epsc eps h Qlog0 hCp1 hepsc heps hlogFit
      (by simpa [HC, K, e] using hheight)
  change SliceA2HeightClosed Cp epsc eps h P0 at hclosed
  rcases hclosed with ⟨Qlog0', hP021, hclosedTail⟩
  have hclosed : SliceA2HeightClosed Cp epsc eps h P0 :=
    ⟨Qlog0', hP021, hclosedTail⟩
  have hP03 : 3 ≤ P0 := by omega
  have heta1 : 1 ≤ eta := by
    simpa [eta] using
      sliceA2ExceptionalLadderEta_one_le Cp e epsc (e / 100) rho
  have hetaBudget : 64 * Real.exp 12 ≤ epsc * eta := by
    simpa [eta] using sliceA2ExceptionalLadderEta_density_budget
      Cp e epsc (e / 100) rho he hepsc (by positivity) hrho
  obtain ⟨AD, hAD⟩ := exists_sliceA2FinalLevels_density
    P0 eta epsc hP03 hepsc heta1 hetaBudget
  obtain ⟨AR, hAR⟩ := exists_exceptionalPrimeLower_ge (P0 : ℝ)
  let Amin : ℝ := max (AD : ℝ) (AR : ℝ)
  obtain ⟨A0, hA0, hAmin, hmean⟩ := exists_sliceA2_meanSquare_closed
    Cp hCp1 hprimeBound epsc eps h P0 Amin hepsc heps hclosed
  refine ⟨A0, hA0, fun A1 hA01 => ?_⟩
  have hAD1R : (AD : ℝ) ≤ A1 :=
    (le_max_left _ _).trans (hAmin.trans hA01)
  have hAR1R : (AR : ℝ) ≤ A1 :=
    (le_max_right _ _).trans (hAmin.trans hA01)
  have hAD1 : AD ≤ A1 := by exact_mod_cast hAD1R
  have hAR1 : AR ≤ A1 := by exact_mod_cast hAR1R
  have hremote : P0 ≤ exceptionalPrimeLower A1 := by
    exact_mod_cast hAR A1 hAR1
  let levels := sliceA2FinalLevels P0 (exceptionalIntervalRatio epsc)
    eta A1 epsc (by omega)
  refine ⟨levels, ?_, ?_, ?_, ?_⟩
  · simpa [levels] using sliceA2FinalLevels_prime P0
      (exceptionalIntervalRatio epsc) eta A1 epsc (by omega)
  · have hbottom : C * Real.log (h : ℝ) ^ B < P0 := by
      simpa [P0] using hhcut h ((le_max_left hcut hconst).trans hh1)
    simpa [levels] using sliceA2FinalLevels_above_polylog P0
      (exceptionalIntervalRatio epsc) eta A1 h B epsc C (by omega)
        hbottom hremote
  · intro A hA1A hAA1
    simpa [levels] using hAD A1 hAD1 A hA1A
  · simpa [levels, eta, e, rho, sliceA2CanonicalRho] using hmean A1 hA01

/-- The Erdős discrepancy endpoint obtained from the completed A.2 theorem,
with no separate A.2 hypothesis at the call site. -/
theorem trackR_edp
    [HalaszLargeValuesAssumption] [PrimeLargeValuesAssumption]
    (f : ℕ → ℤ) (hf : IsSignSequence f) : ¬ BoundedDiscrepancy f :=
  edp_of_sliceMeanSquareA2 sliceMeanSquareA2 f hf

end Tao2015

end MoltResearch
