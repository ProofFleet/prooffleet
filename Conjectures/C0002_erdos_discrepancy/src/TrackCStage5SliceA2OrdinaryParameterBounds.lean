import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ParameterBounds
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2BottomClose

/-!
# Track R A2-V': polynomial bounds for the ordinary coefficients

All constants in this file depend only on the already fixed density
accuracy.  The effective mean-square accuracy appears solely through the
displayed inverse powers.
-/

namespace MoltResearch

namespace Tao2015

noncomputable def sliceA2CoverPowerConstant : ℝ :=
  393216 * 163880000 * Real.exp Real.pi

noncomputable def sliceA2CellPowerConstant : ℝ :=
  8 + 28 * sliceA2CoverPowerConstant

noncomputable def sliceA2ZeroNPowerConstant (epsc : ℝ) : ℝ :=
  3 + sliceA2CoverPowerConstant *
    sliceA2OrdinaryZeroMassBound (exceptionalIntervalRatio epsc)

noncomputable def sliceA2FarPowerConstant (epsc : ℝ) : ℝ :=
  204 * (2 + (exceptionalIntervalRatio epsc : ℝ) +
    sliceA2EtaPowerConstant epsc) ^ 2

noncomputable def sliceA2ClosePowerConstant (epsc : ℝ) : ℝ :=
  1 + 1024 * sliceA2CellPowerConstant ^ 3 * Real.exp 17 *
    sliceA2FarPowerConstant epsc ^ 8 * 163880000 / 3

noncomputable def sliceA2ZeroPrimePowerConstant (epsc : ℝ) : ℝ :=
  (2 * sliceA2ZeroNPowerConstant epsc *
      max 2 (exceptionalIntervalRatio epsc : ℝ) + 2) *
    Real.exp Real.pi * Real.log 4 *
      (8 * Real.exp 1 * (6 * sliceA2ZeroNPowerConstant epsc + 1))

noncomputable def sliceA2ZeroFrequencyPowerConstant (epsc : ℝ) : ℝ :=
  (2 * sliceA2ZeroNPowerConstant epsc *
      max 2 (exceptionalIntervalRatio epsc : ℝ) + 2) *
    (Real.exp Real.pi * Real.log 4 *
      (2 * Real.exp 1 * Real.exp 1 *
        (4 * sliceA2ZeroNPowerConstant epsc + 1)))

theorem sliceA2CoverPowerConstant_pos : 0 < sliceA2CoverPowerConstant := by
  unfold sliceA2CoverPowerConstant
  positivity

theorem sliceA2CellPowerConstant_pos : 0 < sliceA2CellPowerConstant := by
  unfold sliceA2CellPowerConstant
  positivity [sliceA2CoverPowerConstant_pos]

theorem sliceA2ZeroNPowerConstant_pos (epsc : ℝ) :
    0 < sliceA2ZeroNPowerConstant epsc := by
  unfold sliceA2ZeroNPowerConstant
  have hmass : 0 ≤
      sliceA2OrdinaryZeroMassBound (exceptionalIntervalRatio epsc) := by
    unfold sliceA2OrdinaryZeroMassBound
    have hR : (1 : ℝ) ≤ max 2 (exceptionalIntervalRatio epsc : ℝ) :=
      (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)
    positivity [Real.log_nonneg hR]
  positivity [sliceA2CoverPowerConstant_pos]

theorem sliceA2FarPowerConstant_pos (epsc : ℝ) :
    0 < sliceA2FarPowerConstant epsc := by
  unfold sliceA2FarPowerConstant
  positivity [sliceA2EtaPowerConstant_pos epsc]

theorem sliceA2ClosePowerConstant_one_le (epsc : ℝ) :
    1 ≤ sliceA2ClosePowerConstant epsc := by
  unfold sliceA2ClosePowerConstant
  have hcell := (sliceA2CellPowerConstant_pos).le
  have hfar := (sliceA2FarPowerConstant_pos epsc).le
  exact le_add_of_nonneg_right (by positivity)

theorem sliceA2ZeroPrimePowerConstant_pos (epsc : ℝ) :
    0 < sliceA2ZeroPrimePowerConstant epsc := by
  unfold sliceA2ZeroPrimePowerConstant
  have hN := sliceA2ZeroNPowerConstant_pos epsc
  have hR : (0 : ℝ) < max 2 (exceptionalIntervalRatio epsc : ℝ) :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  positivity

theorem sliceA2ZeroFrequencyPowerConstant_pos (epsc : ℝ) :
    0 < sliceA2ZeroFrequencyPowerConstant epsc := by
  unfold sliceA2ZeroFrequencyPowerConstant
  have hN := sliceA2ZeroNPowerConstant_pos epsc
  have hR : (0 : ℝ) < max 2 (exceptionalIntervalRatio epsc : ℝ) :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  positivity

/-- The cell resolution coefficient costs four inverse powers. -/
theorem sliceA2CoverCellCoefficient_le_power
    (eps : ℝ) (heps : 0 < eps) :
    sliceA2CoverCellCoefficient (sliceA2EffectiveEps eps / 100)
        (sliceA2CanonicalRho eps) ≤
      sliceA2CoverPowerConstant / sliceA2EffectiveEps eps ^ 4 := by
  let e := sliceA2EffectiveEps eps
  let rho := sliceA2CanonicalRho eps
  have he : 0 < e := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).1
  have hrho := sliceA2EffectiveEps_sq_le_rho eps heps
  have hden : e ^ 4 / 163880000 ≤ (e / 100) ^ 2 * rho := by
    calc
      e ^ 4 / 163880000 = (e / 100) ^ 2 * (e ^ 2 / 16388) := by ring
      _ ≤ (e / 100) ^ 2 * rho := by gcongr
  unfold sliceA2CoverCellCoefficient sliceA2CoverPowerConstant
  change 393216 * Real.exp Real.pi / ((e / 100) ^ 2 * rho) ≤
    393216 * 163880000 * Real.exp Real.pi / e ^ 4
  calc
    393216 * Real.exp Real.pi / ((e / 100) ^ 2 * rho) ≤
        393216 * Real.exp Real.pi / (e ^ 4 / 163880000) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = 393216 * 163880000 * Real.exp Real.pi / e ^ 4 := by ring

theorem sliceA2OrdinaryCellCountCoefficient_le_power
    (eps : ℝ) (heps : 0 < eps) :
    sliceA2OrdinaryCellCountCoefficient (sliceA2EffectiveEps eps / 100)
        (sliceA2CanonicalRho eps) ≤
      sliceA2CellPowerConstant / sliceA2EffectiveEps eps ^ 4 := by
  let e := sliceA2EffectiveEps eps
  have he : 0 < e := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).1
  have he1 : e ≤ 1 := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).2.1
  have hcover := sliceA2CoverCellCoefficient_le_power eps heps
  have he4 : e ^ 4 ≤ 1 := pow_le_one₀ he.le he1
  unfold sliceA2OrdinaryCellCountCoefficient sliceA2CellPowerConstant
  change 8 + 28 * sliceA2CoverCellCoefficient (e / 100)
      (sliceA2CanonicalRho eps) ≤ (8 + 28 * sliceA2CoverPowerConstant) / e ^ 4
  calc
    8 + 28 * sliceA2CoverCellCoefficient (e / 100)
        (sliceA2CanonicalRho eps) ≤
      8 + 28 * (sliceA2CoverPowerConstant / e ^ 4) := by gcongr
    _ ≤ (8 + 28 * sliceA2CoverPowerConstant) / e ^ 4 := by
      rw [le_div_iff₀ (by positivity : 0 < e ^ 4)]
      have := mul_le_mul_of_nonneg_left he4 (by norm_num : (0 : ℝ) ≤ 8)
      field_simp
      nlinarith

/-- The fixed bottom resolution costs four inverse powers. -/
theorem sliceA2OrdinaryZeroNBound_le_power
    (epsc eps : ℝ) (heps : 0 < eps) :
    sliceA2OrdinaryZeroNBound (exceptionalIntervalRatio epsc)
        (sliceA2EffectiveEps eps / 100) (sliceA2CanonicalRho eps) ≤
      sliceA2ZeroNPowerConstant epsc / sliceA2EffectiveEps eps ^ 4 := by
  let e := sliceA2EffectiveEps eps
  let S := sliceA2OrdinaryZeroMassBound (exceptionalIntervalRatio epsc)
  have he : 0 < e := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).1
  have he1 : e ≤ 1 := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).2.1
  have hcover := sliceA2CoverCellCoefficient_le_power eps heps
  have hS : 0 ≤ S := by
    dsimp [S, sliceA2OrdinaryZeroMassBound]
    have hR : (1 : ℝ) ≤ max 2 (exceptionalIntervalRatio epsc : ℝ) :=
      (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)
    positivity [Real.log_nonneg hR]
  have he4 : e ^ 4 ≤ 1 := pow_le_one₀ he.le he1
  unfold sliceA2OrdinaryZeroNBound sliceA2ZeroNPowerConstant
  change 3 + sliceA2CoverCellCoefficient (e / 100)
      (sliceA2CanonicalRho eps) * S ≤
    (3 + sliceA2CoverPowerConstant * S) / e ^ 4
  calc
    3 + sliceA2CoverCellCoefficient (e / 100)
        (sliceA2CanonicalRho eps) * S ≤
      3 + (sliceA2CoverPowerConstant / e ^ 4) * S := by gcongr
    _ ≤ (3 + sliceA2CoverPowerConstant * S) / e ^ 4 := by
      rw [le_div_iff₀ (by positivity : 0 < e ^ 4)]
      have := mul_le_mul_of_nonneg_left he4 (by norm_num : (0 : ℝ) ≤ 3)
      field_simp
      nlinarith

/-- The all-level moment coefficient costs fourteen inverse powers. -/
theorem sliceA2OrdinaryFarCoefficient_le_power
    (epsc eps : ℝ) (hepsc : 0 < epsc) (heps : 0 < eps) :
    sliceA2OrdinaryFarCoefficient (exceptionalIntervalRatio epsc)
        (sliceA2ExceptionalLadderEta (sliceA2EffectiveEps eps) epsc
          (sliceA2EffectiveEps eps / 100) (sliceA2CanonicalRho eps)) ≤
      sliceA2FarPowerConstant epsc / sliceA2EffectiveEps eps ^ 14 := by
  let e := sliceA2EffectiveEps eps
  let R : ℝ := exceptionalIntervalRatio epsc
  let eta := sliceA2ExceptionalLadderEta e epsc (e / 100)
    (sliceA2CanonicalRho eps)
  let K := sliceA2EtaPowerConstant epsc
  have he : 0 < e := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).1
  have he1 : e ≤ 1 := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).2.1
  have heta : (eta : ℝ) ≤ K / e ^ 7 := by
    simpa [eta, K, e] using
      sliceA2ExceptionalLadderEta_le_power epsc eps hepsc heps
  have he7 : e ^ 7 ≤ 1 := pow_le_one₀ he.le he1
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hK0 : 0 ≤ K := (sliceA2EtaPowerConstant_pos epsc).le
  have hsum : 2 + R + (eta : ℝ) ≤ (2 + R + K) / e ^ 7 := by
    calc
      2 + R + (eta : ℝ) ≤ 2 + R + K / e ^ 7 := by gcongr
      _ ≤ (2 + R + K) / e ^ 7 := by
        rw [le_div_iff₀ (by positivity : 0 < e ^ 7)]
        have hbase : (2 + R) * e ^ 7 ≤ 2 + R :=
          mul_le_of_le_one_right (by positivity) he7
        field_simp
        linarith
  have hsum0 : 0 ≤ 2 + R + (eta : ℝ) := by positivity
  unfold sliceA2OrdinaryFarCoefficient sliceA2FarPowerConstant
  push_cast
  change 204 * (2 + R + (eta : ℝ)) ^ 2 ≤
    204 * (2 + R + K) ^ 2 / e ^ 14
  calc
    204 * (2 + R + (eta : ℝ)) ^ 2 ≤
        204 * ((2 + R + K) / e ^ 7) ^ 2 := by gcongr
    _ = 204 * (2 + R + K) ^ 2 / e ^ 14 := by
      field_simp

/-- The close-scale coefficient costs one hundred twenty-eight inverse
powers before its twentieth-power bottom margin is imposed. -/
theorem sliceA2OrdinaryCloseCoefficient_le_power
    (epsc eps : ℝ) (hepsc : 0 < epsc) (heps : 0 < eps) :
    sliceA2OrdinaryCloseCoefficient (exceptionalIntervalRatio epsc)
        (sliceA2ExceptionalLadderEta (sliceA2EffectiveEps eps) epsc
          (sliceA2EffectiveEps eps / 100) (sliceA2CanonicalRho eps))
        (sliceA2EffectiveEps eps / 100) (sliceA2CanonicalRho eps) ≤
      sliceA2ClosePowerConstant epsc / sliceA2EffectiveEps eps ^ 128 := by
  let e := sliceA2EffectiveEps eps
  let rho := sliceA2CanonicalRho eps
  let eta := sliceA2ExceptionalLadderEta e epsc (e / 100) rho
  let C := sliceA2OrdinaryCellCountCoefficient (e / 100) rho
  let F := sliceA2OrdinaryFarCoefficient (exceptionalIntervalRatio epsc) eta
  let raw := 1024 * C ^ 3 * Real.exp 17 * F ^ 8 /
    (3 * (e / 100) ^ 2 * rho)
  have he : 0 < e := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).1
  have he1 : e ≤ 1 := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).2.1
  have hrho : 0 < rho := by simpa [rho] using sliceA2CanonicalRho_pos eps heps
  have hC : C ≤ sliceA2CellPowerConstant / e ^ 4 := by
    simpa [C, e, rho] using sliceA2OrdinaryCellCountCoefficient_le_power eps heps
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact (sliceA2OrdinaryCellCountCoefficient_pos (e / 100) rho
      (by positivity) hrho).le
  have hF : F ≤ sliceA2FarPowerConstant epsc / e ^ 14 := by
    simpa [F, eta, e, rho] using
      sliceA2OrdinaryFarCoefficient_le_power epsc eps hepsc heps
  have hF0 : 0 ≤ F := by
    dsimp [F, sliceA2OrdinaryFarCoefficient]
    positivity
  have hden : e ^ 4 / 163880000 ≤ (e / 100) ^ 2 * rho := by
    calc
      e ^ 4 / 163880000 = (e / 100) ^ 2 * (e ^ 2 / 16388) := by ring
      _ ≤ (e / 100) ^ 2 * rho := by
        gcongr
        simpa [e, rho] using sliceA2EffectiveEps_sq_le_rho eps heps
  have hraw : raw ≤
      (1024 * sliceA2CellPowerConstant ^ 3 * Real.exp 17 *
        sliceA2FarPowerConstant epsc ^ 8 * 163880000 / 3) / e ^ 128 := by
    dsimp [raw]
    have hnum : 0 ≤ 1024 * C ^ 3 * Real.exp 17 * F ^ 8 := by positivity
    calc
      1024 * C ^ 3 * Real.exp 17 * F ^ 8 /
          (3 * (e / 100) ^ 2 * rho) ≤
        1024 * (sliceA2CellPowerConstant / e ^ 4) ^ 3 * Real.exp 17 *
            (sliceA2FarPowerConstant epsc / e ^ 14) ^ 8 /
          (3 * (e ^ 4 / 163880000)) := by
            apply div_le_div₀
            · positivity [sliceA2CellPowerConstant_pos,
                sliceA2FarPowerConstant_pos epsc]
            · gcongr <;> positivity [sliceA2CellPowerConstant_pos,
                sliceA2FarPowerConstant_pos epsc]
            · positivity
            · simpa [mul_assoc] using
                mul_le_mul_of_nonneg_left hden (by norm_num : (0 : ℝ) ≤ 3)
      _ = (1024 * sliceA2CellPowerConstant ^ 3 * Real.exp 17 *
          sliceA2FarPowerConstant epsc ^ 8 * 163880000 / 3) /
            e ^ 128 := by
        field_simp
  have he128 : e ^ 128 ≤ 1 := pow_le_one₀ he.le he1
  have he128pos : 0 < e ^ 128 := by positivity
  unfold sliceA2OrdinaryCloseCoefficient
  change max 1 raw ≤ sliceA2ClosePowerConstant epsc / e ^ 128
  apply max_le
  · rw [le_div_iff₀ he128pos]
    simpa using he128.trans (sliceA2ClosePowerConstant_one_le epsc)
  · exact hraw.trans (by
      rw [div_le_div_iff_of_pos_right he128pos]
      unfold sliceA2ClosePowerConstant
      norm_num)

/-- Fixed bottom prime-side coefficient bound. -/
theorem sliceA2OrdinaryZeroPrimeCoefficient_le_power
    (epsc eps : ℝ) (heps : 0 < eps) :
    sliceA2OrdinaryZeroPrimeCoefficient (exceptionalIntervalRatio epsc)
        (sliceA2EffectiveEps eps / 100) (sliceA2CanonicalRho eps) ≤
      sliceA2ZeroPrimePowerConstant epsc / sliceA2EffectiveEps eps ^ 8 := by
  let e := sliceA2EffectiveEps eps
  let N := sliceA2OrdinaryZeroNBound (exceptionalIntervalRatio epsc)
    (e / 100) (sliceA2CanonicalRho eps)
  let KN := sliceA2ZeroNPowerConstant epsc
  let R : ℝ := max 2 (exceptionalIntervalRatio epsc : ℝ)
  have he : 0 < e := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).1
  have he1 : e ≤ 1 := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).2.1
  have hN : N ≤ KN / e ^ 4 := by
    simpa [N, KN, e] using sliceA2OrdinaryZeroNBound_le_power epsc eps heps
  have hN0 : 0 < N := by
    dsimp [N]
    exact sliceA2OrdinaryZeroNBound_pos (exceptionalIntervalRatio epsc)
      (e / 100) (sliceA2CanonicalRho eps) (by positivity)
      (sliceA2CanonicalRho_pos eps heps)
  have hKN : 0 < KN := by simpa [KN] using sliceA2ZeroNPowerConstant_pos epsc
  have hR : 0 < R := by
    dsimp [R]
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have he4 : e ^ 4 ≤ 1 := pow_le_one₀ he.le he1
  have ha : 2 * N * R + 2 ≤ (2 * KN * R + 2) / e ^ 4 := by
    calc
      2 * N * R + 2 ≤ 2 * (KN / e ^ 4) * R + 2 := by gcongr
      _ ≤ (2 * KN * R + 2) / e ^ 4 := by
        rw [le_div_iff₀ (by positivity : 0 < e ^ 4)]
        have := mul_le_mul_of_nonneg_left he4 (by norm_num : (0 : ℝ) ≤ 2)
        field_simp
        nlinarith
  have hb : 6 * N + 1 ≤ (6 * KN + 1) / e ^ 4 := by
    calc
      6 * N + 1 ≤ 6 * (KN / e ^ 4) + 1 := by gcongr
      _ ≤ (6 * KN + 1) / e ^ 4 := by
        rw [le_div_iff₀ (by positivity : 0 < e ^ 4)]
        have := mul_le_mul_of_nonneg_left he4 (by norm_num : (0 : ℝ) ≤ 1)
        field_simp
        nlinarith
  unfold sliceA2OrdinaryZeroPrimeCoefficient
  dsimp only
  change (2 * N * R + 2) * Real.exp Real.pi * Real.log 4 *
      (8 * Real.exp 1 * (6 * N + 1)) ≤ _
  calc
    (2 * N * R + 2) * Real.exp Real.pi * Real.log 4 *
        (8 * Real.exp 1 * (6 * N + 1)) ≤
      ((2 * KN * R + 2) / e ^ 4) * Real.exp Real.pi * Real.log 4 *
        (8 * Real.exp 1 * ((6 * KN + 1) / e ^ 4)) := by
      gcongr <;> positivity
    _ = sliceA2ZeroPrimePowerConstant epsc / e ^ 8 := by
      unfold sliceA2ZeroPrimePowerConstant
      dsimp [KN, R]
      field_simp

/-- The bottom frequency coefficient is its explicit `log P0` and
`Q0^(13/20)` growth times an eight-power fixed envelope. -/
theorem sliceA2OrdinaryZeroFrequencyCoefficient_le_power
    (P0 : ℕ) (epsc eps : ℝ) (heps : 0 < eps) :
    let eta := sliceA2ExceptionalLadderEta (sliceA2EffectiveEps eps) epsc
      (sliceA2EffectiveEps eps / 100) (sliceA2CanonicalRho eps)
    sliceA2OrdinaryZeroFrequencyCoefficient P0
        (exceptionalIntervalRatio epsc) eta
        (sliceA2EffectiveEps eps / 100) (sliceA2CanonicalRho eps) ≤
      (sliceA2ZeroFrequencyPowerConstant epsc /
          sliceA2EffectiveEps eps ^ 8) * Real.log (P0 : ℝ) *
        (sliceA2LadderQ P0 (exceptionalIntervalRatio epsc) eta 0 : ℝ) ^
          (13 / 20 : ℝ) := by
  dsimp only
  let e := sliceA2EffectiveEps eps
  let eta := sliceA2ExceptionalLadderEta e epsc (e / 100)
    (sliceA2CanonicalRho eps)
  let N := sliceA2OrdinaryZeroNBound (exceptionalIntervalRatio epsc)
    (e / 100) (sliceA2CanonicalRho eps)
  let KN := sliceA2ZeroNPowerConstant epsc
  let R : ℝ := max 2 (exceptionalIntervalRatio epsc : ℝ)
  let Q : ℝ := sliceA2LadderQ P0 (exceptionalIntervalRatio epsc) eta 0
  have he : 0 < e := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).1
  have he1 : e ≤ 1 := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).2.1
  have hN : N ≤ KN / e ^ 4 := by
    simpa [N, KN, e] using sliceA2OrdinaryZeroNBound_le_power epsc eps heps
  have hN0 : 0 < N := by
    dsimp [N]
    exact sliceA2OrdinaryZeroNBound_pos (exceptionalIntervalRatio epsc)
      (e / 100) (sliceA2CanonicalRho eps) (by positivity)
      (sliceA2CanonicalRho_pos eps heps)
  have hKN : 0 < KN := by simpa [KN] using sliceA2ZeroNPowerConstant_pos epsc
  have hR : 0 < R := by
    dsimp [R]
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have he4 : e ^ 4 ≤ 1 := pow_le_one₀ he.le he1
  have ha : 2 * N * R + 2 ≤ (2 * KN * R + 2) / e ^ 4 := by
    calc
      2 * N * R + 2 ≤ 2 * (KN / e ^ 4) * R + 2 := by gcongr
      _ ≤ (2 * KN * R + 2) / e ^ 4 := by
        rw [le_div_iff₀ (by positivity : 0 < e ^ 4)]
        have := mul_le_mul_of_nonneg_left he4 (by norm_num : (0 : ℝ) ≤ 2)
        field_simp
        nlinarith
  have hb : 4 * N + 1 ≤ (4 * KN + 1) / e ^ 4 := by
    calc
      4 * N + 1 ≤ 4 * (KN / e ^ 4) + 1 := by gcongr
      _ ≤ (4 * KN + 1) / e ^ 4 := by
        rw [le_div_iff₀ (by positivity : 0 < e ^ 4)]
        have := mul_le_mul_of_nonneg_left he4 (by norm_num : (0 : ℝ) ≤ 1)
        field_simp
        nlinarith
  unfold sliceA2OrdinaryZeroFrequencyCoefficient
  dsimp only
  change (2 * N * R + 2) * Real.log (P0 : ℝ) *
      (Real.exp Real.pi * Real.log 4 *
        (2 * Real.exp 1 * (Q ^ (13 / 20 : ℝ) * Real.exp 1) *
          (4 * N + 1))) ≤ _
  calc
    (2 * N * R + 2) * Real.log (P0 : ℝ) *
        (Real.exp Real.pi * Real.log 4 *
          (2 * Real.exp 1 * (Q ^ (13 / 20 : ℝ) * Real.exp 1) *
            (4 * N + 1))) ≤
      ((2 * KN * R + 2) / e ^ 4) * Real.log (P0 : ℝ) *
        (Real.exp Real.pi * Real.log 4 *
          (2 * Real.exp 1 * (Q ^ (13 / 20 : ℝ) * Real.exp 1) *
            ((4 * KN + 1) / e ^ 4))) := by
      gcongr <;> positivity
    _ = (sliceA2ZeroFrequencyPowerConstant epsc / e ^ 8) *
        Real.log (P0 : ℝ) * Q ^ (13 / 20 : ℝ) := by
      unfold sliceA2ZeroFrequencyPowerConstant
      dsimp [KN, R, Q]
      field_simp

end Tao2015

end MoltResearch
