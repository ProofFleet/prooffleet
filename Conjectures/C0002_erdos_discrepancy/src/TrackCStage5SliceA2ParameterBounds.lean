import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalLadderBudget
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2WindowSchedule

/-!
# Track R A2-V': polynomial bounds for the fixed parameters

The final height must be polynomial in the requested accuracy.  This leaf
starts that ledger by bounding the exceptional ladder ratio by a fixed
constant times the inverse seventh power of the effective accuracy.  The
deliberately coarse exponent avoids hiding any asymptotic choice.
-/

namespace MoltResearch

namespace Tao2015

noncomputable def sliceA2CanonicalRho (eps : ℝ) : ℝ :=
  1 / (4 * sliceA2Parts eps)

noncomputable def sliceA2ExceptionalNPowerConstant (epsc : ℝ) : ℝ :=
  3 + 73728 * 163880000 * Real.exp Real.pi *
    sliceA2ExceptionalMass 0 epsc

noncomputable def sliceA2ExceptionalPrimePowerConstant (epsc : ℝ) : ℝ :=
  1 + 196608 * sliceA2ExceptionalNPowerConstant epsc *
    (exceptionalIntervalRatio epsc : ℝ) * sliceA2ExceptionalMass 0 epsc

noncomputable def sliceA2ExceptionalEpsilonDenominator (epsc : ℝ) : ℝ :=
  800 * 16388 * Real.exp 13 * (exceptionalIntervalRatio epsc : ℝ) *
    sliceA2ExceptionalPrimePowerConstant epsc

noncomputable def sliceA2ExceptionalBudgetDenominator (epsc : ℝ) : ℝ :=
  max (sliceA2ExceptionalEpsilonDenominator epsc) (1 / epsc)

noncomputable def sliceA2EtaPowerConstant (epsc : ℝ) : ℝ :=
  64 * Real.exp 12 * sliceA2ExceptionalBudgetDenominator epsc + 2

theorem sliceA2CanonicalRho_pos (eps : ℝ) (heps : 0 < eps) :
    0 < sliceA2CanonicalRho eps := by
  unfold sliceA2CanonicalRho
  have hM := (sliceA2Parts_bounds eps heps).1
  positivity

theorem sliceA2CanonicalRho_le_one (eps : ℝ) (heps : 0 < eps) :
    sliceA2CanonicalRho eps ≤ 1 := by
  unfold sliceA2CanonicalRho
  have hM := (sliceA2Parts_bounds eps heps).2.1
  have hMR : (30 : ℝ) ≤ sliceA2Parts eps := by exact_mod_cast hM
  have hden : 0 < (4 : ℝ) * sliceA2Parts eps := by positivity
  rw [div_le_iff₀ hden]
  nlinarith

/-- The reciprocal number of floor slices retains two powers of accuracy. -/
theorem sliceA2EffectiveEps_sq_le_rho
    (eps : ℝ) (heps : 0 < eps) :
    sliceA2EffectiveEps eps ^ 2 / 16388 ≤ sliceA2CanonicalRho eps := by
  let e := sliceA2EffectiveEps eps
  let M := sliceA2Parts eps
  have he : 0 < e := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).1
  have hM : (M : ℝ) ≤ 4097 / e ^ 2 := by
    simpa [M, e] using sliceA2Parts_le eps heps
  have hM0 : (0 : ℝ) < M := by
    exact_mod_cast (sliceA2Parts_bounds eps heps).1
  have hcross : (4 : ℝ) * M * e ^ 2 ≤ 16388 := by
    have he2 : 0 < e ^ 2 := sq_pos_of_pos he
    have := (le_div_iff₀ he2).mp hM
    nlinarith
  unfold sliceA2CanonicalRho
  dsimp [e, M] at hcross hM0 ⊢
  have hden : 0 < (16388 : ℝ) * (4 * sliceA2Parts eps) := by positivity
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 16388)
    (by positivity : (0 : ℝ) < 4 * sliceA2Parts eps)]
  nlinarith

theorem sliceA2ExceptionalNPowerConstant_pos (epsc : ℝ) :
    0 < sliceA2ExceptionalNPowerConstant epsc := by
  unfold sliceA2ExceptionalNPowerConstant
  have hmass := sliceA2ExceptionalMass_nonneg 0 epsc
  positivity

theorem sliceA2ExceptionalPrimePowerConstant_one_le (epsc : ℝ) :
    1 ≤ sliceA2ExceptionalPrimePowerConstant epsc := by
  unfold sliceA2ExceptionalPrimePowerConstant
  have hN := (sliceA2ExceptionalNPowerConstant_pos epsc).le
  have hmass := sliceA2ExceptionalMass_nonneg 0 epsc
  have hR : (0 : ℝ) ≤ exceptionalIntervalRatio epsc := by positivity
  exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (mul_nonneg
    (by norm_num) hN) hR) hmass)

theorem sliceA2ExceptionalEpsilonDenominator_one_le (epsc : ℝ) :
    1 ≤ sliceA2ExceptionalEpsilonDenominator epsc := by
  unfold sliceA2ExceptionalEpsilonDenominator
  have hR : (3 : ℝ) ≤ exceptionalIntervalRatio epsc := by
    exact_mod_cast exceptionalIntervalRatio_three_le epsc
  have hM := sliceA2ExceptionalPrimePowerConstant_one_le epsc
  have hexp : 1 ≤ Real.exp 13 := by
    simpa using Real.exp_one_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 13)
  calc
    (1 : ℝ) ≤ 800 * 16388 * 1 * 3 * 1 := by norm_num
    _ ≤ 800 * 16388 * Real.exp 13 *
        (exceptionalIntervalRatio epsc : ℝ) *
          sliceA2ExceptionalPrimePowerConstant epsc := by gcongr

theorem sliceA2ExceptionalBudgetDenominator_one_le
    (epsc : ℝ) : 1 ≤ sliceA2ExceptionalBudgetDenominator epsc := by
  unfold sliceA2ExceptionalBudgetDenominator
  exact (sliceA2ExceptionalEpsilonDenominator_one_le epsc).trans
    (le_max_left _ _)

theorem sliceA2EtaPowerConstant_pos (epsc : ℝ) :
    0 < sliceA2EtaPowerConstant epsc := by
  unfold sliceA2EtaPowerConstant
  have hD := sliceA2ExceptionalBudgetDenominator_one_le epsc
  positivity

/-- The exceptional resolution costs at most four inverse powers of the
effective accuracy. -/
theorem sliceA2ExceptionalN_zero_le_power
    (epsc eps : ℝ) (heps : 0 < eps) :
    (sliceA2ExceptionalN 0 epsc (sliceA2EffectiveEps eps / 100)
        (sliceA2CanonicalRho eps) : ℝ) ≤
      sliceA2ExceptionalNPowerConstant epsc /
        sliceA2EffectiveEps eps ^ 4 := by
  let e := sliceA2EffectiveEps eps
  let rho := sliceA2CanonicalRho eps
  let S := sliceA2ExceptionalMass 0 epsc
  let x := 73728 * Real.exp Real.pi * S / ((e / 100) ^ 2 * rho)
  have he : 0 < e := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).1
  have he1 : e ≤ 1 := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).2.1
  have hrho := sliceA2EffectiveEps_sq_le_rho eps heps
  have hrhopos : 0 < rho := by simpa [rho] using sliceA2CanonicalRho_pos eps heps
  have hdenLower : e ^ 4 / 163880000 ≤ (e / 100) ^ 2 * rho := by
    calc
      e ^ 4 / 163880000 = (e / 100) ^ 2 * (e ^ 2 / 16388) := by ring
      _ ≤ (e / 100) ^ 2 * rho := by
        gcongr
  have hdenLowerPos : 0 < e ^ 4 / 163880000 := by positivity
  have hx0 : 0 ≤ x := by
    dsimp [x, S]
    have hmass := sliceA2ExceptionalMass_nonneg 0 epsc
    positivity
  have hx : x ≤
      73728 * 163880000 * Real.exp Real.pi * S / e ^ 4 := by
    dsimp [x]
    have hnum : 0 ≤ 73728 * Real.exp Real.pi * S := by
      dsimp [S]
      positivity [sliceA2ExceptionalMass_nonneg 0 epsc]
    calc
      73728 * Real.exp Real.pi * S / ((e / 100) ^ 2 * rho) ≤
          73728 * Real.exp Real.pi * S / (e ^ 4 / 163880000) :=
        div_le_div_of_nonneg_left hnum hdenLowerPos hdenLower
      _ = 73728 * 163880000 * Real.exp Real.pi * S / e ^ 4 := by ring
  have hceil : (⌈x⌉₊ : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hx0).le
  have hmax : ((max 2 ⌈x⌉₊ : ℕ) : ℝ) ≤ 2 + (⌈x⌉₊ : ℕ) := by
    exact_mod_cast (show max 2 ⌈x⌉₊ ≤ 2 + ⌈x⌉₊ by omega)
  have he4 : e ^ 4 ≤ 1 := pow_le_one₀ he.le he1
  unfold sliceA2ExceptionalN
  change ((max 2 ⌈x⌉₊ : ℕ) : ℝ) ≤ _
  calc
    ((max 2 ⌈x⌉₊ : ℕ) : ℝ) ≤ 2 + (⌈x⌉₊ : ℕ) := hmax
    _ ≤ x + 3 := by linarith
    _ ≤ 73728 * 163880000 * Real.exp Real.pi * S / e ^ 4 + 3 := by
      linarith
    _ ≤ (3 + 73728 * 163880000 * Real.exp Real.pi * S) / e ^ 4 := by
      have he40 : 0 < e ^ 4 := by positivity
      rw [le_div_iff₀ he40]
      have := mul_le_mul_of_nonneg_left he4 (by norm_num : (0 : ℝ) ≤ 3)
      field_simp
      nlinarith
    _ = sliceA2ExceptionalNPowerConstant epsc /
        sliceA2EffectiveEps eps ^ 4 := by
      simp only [sliceA2ExceptionalNPowerConstant]
      dsimp [S, e]

/-- The coefficient under the sharp square root has the same four-power
envelope. -/
theorem sliceA2ExceptionalPrimeCoefficient_zero_le_power
    (epsc eps : ℝ) (heps : 0 < eps) :
    sliceA2ExceptionalPrimeCoefficient 0 epsc
        (sliceA2EffectiveEps eps / 100) (sliceA2CanonicalRho eps) ≤
      sliceA2ExceptionalPrimePowerConstant epsc /
        sliceA2EffectiveEps eps ^ 4 := by
  let e := sliceA2EffectiveEps eps
  let N := sliceA2ExceptionalN 0 epsc (e / 100) (sliceA2CanonicalRho eps)
  let R : ℝ := exceptionalIntervalRatio epsc
  let S := sliceA2ExceptionalMass 0 epsc
  have he : 0 < e := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).1
  have he1 : e ≤ 1 := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).2.1
  have hN : (N : ℝ) ≤ sliceA2ExceptionalNPowerConstant epsc / e ^ 4 := by
    simpa [N, e] using sliceA2ExceptionalN_zero_le_power epsc eps heps
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hS0 : 0 ≤ S := by dsimp [S]; exact sliceA2ExceptionalMass_nonneg 0 epsc
  have hraw : 196608 * (N : ℝ) * R * S ≤
      196608 * (sliceA2ExceptionalNPowerConstant epsc / e ^ 4) * R * S := by
    gcongr
  have he4 : e ^ 4 ≤ 1 := pow_le_one₀ he.le he1
  have he40 : 0 < e ^ 4 := by positivity
  unfold sliceA2ExceptionalPrimeCoefficient
  change max 1 (196608 * (N : ℝ) * R * S) ≤ _
  apply max_le
  · rw [le_div_iff₀ he40]
    have hC := sliceA2ExceptionalPrimePowerConstant_one_le epsc
    simpa using (mul_le_mul_of_nonneg_left he4 zero_le_one).trans (by simpa using hC)
  · calc
      196608 * (N : ℝ) * R * S ≤
          196608 * (sliceA2ExceptionalNPowerConstant epsc / e ^ 4) * R * S :=
        hraw
      _ = (196608 * sliceA2ExceptionalNPowerConstant epsc * R * S) /
          e ^ 4 := by ring
      _ ≤ (1 + 196608 * sliceA2ExceptionalNPowerConstant epsc * R * S) /
          e ^ 4 := by
        rw [div_le_div_iff_of_pos_right he40]
        norm_num
      _ = sliceA2ExceptionalPrimePowerConstant epsc / e ^ 4 := by
        simp only [sliceA2ExceptionalPrimePowerConstant]
        dsimp [R, S]

theorem sliceA2CanonicalRho_le_sqrt
    (eps : ℝ) (heps : 0 < eps) :
    sliceA2CanonicalRho eps ≤ Real.sqrt (sliceA2CanonicalRho eps) := by
  have hrho0 := (sliceA2CanonicalRho_pos eps heps).le
  have hrho1 := sliceA2CanonicalRho_le_one eps heps
  rw [Real.le_sqrt hrho0 hrho0]
  nlinarith [sq_nonneg (sliceA2CanonicalRho eps)]

theorem sqrt_sliceA2ExceptionalPrimeCoefficient_le_self
    (epsc eps : ℝ) :
    Real.sqrt (sliceA2ExceptionalPrimeCoefficient 0 epsc
        (sliceA2EffectiveEps eps / 100) (sliceA2CanonicalRho eps)) ≤
      sliceA2ExceptionalPrimeCoefficient 0 epsc
        (sliceA2EffectiveEps eps / 100) (sliceA2CanonicalRho eps) := by
  let M := sliceA2ExceptionalPrimeCoefficient 0 epsc
    (sliceA2EffectiveEps eps / 100) (sliceA2CanonicalRho eps)
  have hM : 1 ≤ M := by
    dsimp [M, sliceA2ExceptionalPrimeCoefficient]
    exact le_max_left _ _
  rw [Real.sqrt_le_iff]
  exact ⟨zero_le_one.trans hM, by nlinarith⟩

/-- At the canonical floor-slice budget, epsilon-prime loses at most seven
powers of the effective accuracy. -/
theorem sliceA2ExceptionalEpsilonPrime_zero_lower
    (epsc eps : ℝ) (heps : 0 < eps) :
    sliceA2EffectiveEps eps ^ 7 /
        sliceA2ExceptionalEpsilonDenominator epsc ≤
      sliceA2ExceptionalEpsilonPrime 0 epsc
        (sliceA2EffectiveEps eps / 100) (sliceA2CanonicalRho eps) := by
  let e := sliceA2EffectiveEps eps
  let rho := sliceA2CanonicalRho eps
  let R : ℝ := exceptionalIntervalRatio epsc
  let M := sliceA2ExceptionalPrimeCoefficient 0 epsc (e / 100) rho
  let CP := sliceA2ExceptionalPrimePowerConstant epsc
  let DE := sliceA2ExceptionalEpsilonDenominator epsc
  have he : 0 < e := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).1
  have hrho : 0 < rho := by simpa [rho] using sliceA2CanonicalRho_pos eps heps
  have hR : 0 < R := by
    dsimp [R]
    exact_mod_cast (show 0 < exceptionalIntervalRatio epsc by
      have := exceptionalIntervalRatio_three_le epsc
      omega)
  have hM : 0 < M := by
    dsimp [M]
    exact sliceA2ExceptionalPrimeCoefficient_pos 0 epsc (e / 100) rho
  have hCP : 0 < CP :=
    lt_of_lt_of_le zero_lt_one (sliceA2ExceptionalPrimePowerConstant_one_le epsc)
  have hDE : 0 < DE := by
    dsimp [DE]
    exact lt_of_lt_of_le zero_lt_one
      (sliceA2ExceptionalEpsilonDenominator_one_le epsc)
  have hrhoRoot : rho ≤ Real.sqrt rho := by
    simpa [rho] using sliceA2CanonicalRho_le_sqrt eps heps
  have hrhoLower : e ^ 2 / 16388 ≤ rho := by
    simpa [e, rho] using sliceA2EffectiveEps_sq_le_rho eps heps
  have hrootLower : e ^ 2 / 16388 ≤ Real.sqrt rho :=
    hrhoLower.trans hrhoRoot
  have hrootM : Real.sqrt M ≤ M := by
    simpa [M] using sqrt_sliceA2ExceptionalPrimeCoefficient_le_self epsc eps
  have hMpower : M ≤ CP / e ^ 4 := by
    simpa [M, CP, e, rho] using
      sliceA2ExceptionalPrimeCoefficient_zero_le_power epsc eps heps
  have hrootMpower : Real.sqrt M ≤ CP / e ^ 4 := hrootM.trans hMpower
  have hden : 0 < 8 * Real.exp 13 * R * Real.sqrt M := by
    have hsqrtM : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
    positivity
  unfold sliceA2ExceptionalEpsilonPrime exceptionalEpsilonPrime
  norm_num only [Real.sqrt_one, mul_one]
  change e ^ 7 / DE ≤ (e / 100 * Real.sqrt rho) /
    (8 * Real.exp 13 * R * Real.sqrt M)
  rw [div_le_div_iff₀ hDE hden]
  have hleft : e ^ 7 * (8 * Real.exp 13 * R * Real.sqrt M) ≤
      8 * Real.exp 13 * R * CP * e ^ 3 := by
    calc
      e ^ 7 * (8 * Real.exp 13 * R * Real.sqrt M) ≤
          e ^ 7 * (8 * Real.exp 13 * R * (CP / e ^ 4)) := by
        gcongr
      _ = 8 * Real.exp 13 * R * CP * e ^ 3 := by
        field_simp
  have hright : 8 * Real.exp 13 * R * CP * e ^ 3 ≤
      (e / 100 * Real.sqrt rho) * DE := by
    calc
      8 * Real.exp 13 * R * CP * e ^ 3 =
          (800 * 16388 * Real.exp 13 * R * CP) *
            (e / 100 * (e ^ 2 / 16388)) := by ring
      _ ≤ DE * (e / 100 * Real.sqrt rho) := by
        dsimp [DE, sliceA2ExceptionalEpsilonDenominator]
        gcongr
      _ = (e / 100 * Real.sqrt rho) * DE := by ring
  exact hleft.trans hright

/-- The minimum shared by the exceptional and density budgets still
retains seven powers of accuracy. -/
theorem sliceA2ExceptionalLadderDenominator_lower
    (epsc eps : ℝ) (hepsc : 0 < epsc) (heps : 0 < eps) :
    sliceA2EffectiveEps eps ^ 7 /
        sliceA2ExceptionalBudgetDenominator epsc ≤
      min (sliceA2ExceptionalLadderBudget (sliceA2EffectiveEps eps) epsc
          (sliceA2EffectiveEps eps / 100) (sliceA2CanonicalRho eps)) epsc := by
  let e := sliceA2EffectiveEps eps
  let DE := sliceA2ExceptionalEpsilonDenominator epsc
  let D := sliceA2ExceptionalBudgetDenominator epsc
  let ep := sliceA2ExceptionalEpsilonPrime 0 epsc (e / 100)
    (sliceA2CanonicalRho eps)
  let R : ℝ := exceptionalIntervalRatio epsc
  have he : 0 < e := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).1
  have he1 : e ≤ 1 := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).2.1
  have hD1 : 1 ≤ D := by
    simpa [D] using sliceA2ExceptionalBudgetDenominator_one_le epsc
  have hD : 0 < D := zero_lt_one.trans_le hD1
  have hDE1 : 1 ≤ DE := by
    simpa [DE] using sliceA2ExceptionalEpsilonDenominator_one_le epsc
  have hDED : DE ≤ D := by
    dsimp [D, sliceA2ExceptionalBudgetDenominator]
    exact le_max_left _ _
  have he7e : e ^ 7 ≤ e := by
    simpa using pow_le_pow_of_le_one he.le he1 (by omega : 1 ≤ 7)
  have he7one : e ^ 7 ≤ 1 := he7e.trans he1
  have hsmallE : e ^ 7 / D ≤ e := by
    rw [div_le_iff₀ hD]
    exact he7e.trans (by
      calc
        e ≤ e * 1 := by simp
        _ ≤ e * D := by gcongr)
  have hep : e ^ 7 / DE ≤ ep := by
    simpa [e, DE, ep] using
      sliceA2ExceptionalEpsilonPrime_zero_lower epsc eps heps
  have hsmallEp : e ^ 7 / D ≤
      8 * ep * Real.exp 13 * R := by
    have hsmallDE : e ^ 7 / D ≤ e ^ 7 / DE := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hDED
    have hfactor : 1 ≤ 8 * Real.exp 13 * R := by
      have hR : (3 : ℝ) ≤ R := by
        dsimp [R]
        exact_mod_cast exceptionalIntervalRatio_three_le epsc
      have hexp : 1 ≤ Real.exp 13 := by
        simpa using Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 13)
      calc
        (1 : ℝ) ≤ 8 * 1 * 3 := by norm_num
        _ ≤ 8 * Real.exp 13 * R := by gcongr
    exact hsmallDE.trans (hep.trans (by
      calc
        ep ≤ ep * 1 := by simp
        _ ≤ ep * (8 * Real.exp 13 * R) := by
          gcongr
          dsimp [ep]
          exact (sliceA2ExceptionalEpsilonPrime_pos 0 epsc (e / 100)
            (sliceA2CanonicalRho eps) (by positivity) (sliceA2CanonicalRho_pos eps heps)).le
        _ = 8 * ep * Real.exp 13 * R := by ring))
  have hsmallBudget : e ^ 7 / D ≤
      sliceA2ExceptionalLadderBudget e epsc (e / 100)
        (sliceA2CanonicalRho eps) := by
    unfold sliceA2ExceptionalLadderBudget
    apply le_min hsmallE
    simpa [ep, R, e] using hsmallEp
  have hrecip : 1 / epsc ≤ D := by
    dsimp [D, sliceA2ExceptionalBudgetDenominator]
    exact le_max_right _ _
  have hsmallEpsc : e ^ 7 / D ≤ epsc := by
    rw [div_le_iff₀ hD]
    have hpay : 1 ≤ epsc * D := by
      have := mul_le_mul_of_nonneg_left hrecip hepsc.le
      field_simp at this
      exact this
    exact he7one.trans hpay
  apply le_min
  · simpa [e, D] using hsmallBudget
  · simpa [e, D] using hsmallEpsc

/-- Explicit polynomial bound for the common exceptional/ordinary ladder
ratio. -/
theorem sliceA2ExceptionalLadderEta_le_power
    (epsc eps : ℝ) (hepsc : 0 < epsc) (heps : 0 < eps) :
    (sliceA2ExceptionalLadderEta (sliceA2EffectiveEps eps) epsc
        (sliceA2EffectiveEps eps / 100) (sliceA2CanonicalRho eps) : ℝ) ≤
      sliceA2EtaPowerConstant epsc / sliceA2EffectiveEps eps ^ 7 := by
  let e := sliceA2EffectiveEps eps
  let D := sliceA2ExceptionalBudgetDenominator epsc
  let b := sliceA2ExceptionalLadderBudget e epsc (e / 100)
    (sliceA2CanonicalRho eps)
  let d := min b epsc
  let x := 64 * Real.exp 12 / d
  have he : 0 < e := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).1
  have he1 : e ≤ 1 := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).2.1
  have hD : 0 < D := by
    exact zero_lt_one.trans_le (by simpa [D] using
      sliceA2ExceptionalBudgetDenominator_one_le epsc)
  have hdLower : e ^ 7 / D ≤ d := by
    simpa [e, D, b, d] using
      sliceA2ExceptionalLadderDenominator_lower epsc eps hepsc heps
  have hd : 0 < d := lt_of_lt_of_le (by positivity : 0 < e ^ 7 / D) hdLower
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx : x ≤ 64 * Real.exp 12 * D / e ^ 7 := by
    dsimp [x]
    calc
      64 * Real.exp 12 / d ≤ 64 * Real.exp 12 / (e ^ 7 / D) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hdLower
      _ = 64 * Real.exp 12 * D / e ^ 7 := by
        field_simp
  have hceil : (⌈x⌉₊ : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hx0).le
  have hmax : ((max 1 ⌈x⌉₊ : ℕ) : ℝ) ≤ 1 + (⌈x⌉₊ : ℕ) := by
    exact_mod_cast (show max 1 ⌈x⌉₊ ≤ 1 + ⌈x⌉₊ by omega)
  have he7 : e ^ 7 ≤ 1 := pow_le_one₀ he.le he1
  have he70 : 0 < e ^ 7 := by positivity
  unfold sliceA2ExceptionalLadderEta sliceA2LadderEta
  change ((max 1 ⌈x⌉₊ : ℕ) : ℝ) ≤ _
  calc
    ((max 1 ⌈x⌉₊ : ℕ) : ℝ) ≤ 1 + (⌈x⌉₊ : ℕ) := hmax
    _ ≤ x + 2 := by linarith
    _ ≤ 64 * Real.exp 12 * D / e ^ 7 + 2 := by linarith
    _ ≤ (64 * Real.exp 12 * D + 2) / e ^ 7 := by
      rw [le_div_iff₀ he70]
      have := mul_le_mul_of_nonneg_left he7 (by norm_num : (0 : ℝ) ≤ 2)
      field_simp
      nlinarith
    _ = sliceA2EtaPowerConstant epsc /
        sliceA2EffectiveEps eps ^ 7 := by
      simp only [sliceA2EtaPowerConstant]
      dsimp [D, e]


end Tao2015

end MoltResearch
