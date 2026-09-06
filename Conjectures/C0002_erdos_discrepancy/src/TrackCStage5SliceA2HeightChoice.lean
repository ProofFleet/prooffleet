import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2BottomPowerClose
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2MeanSquareClose

/-!
# Track R A2-V': the polynomial height choice

The bottom endpoint is the fourth-root scale
`P0 = max 21 ceil(H^(1/(4R)))`.  Thus `P0^(4R) >= H`, while the frequency
side grows by less than `H^(1/4)`.  The remaining three quarters of the
height pay the fixed coefficient.
-/

namespace MoltResearch

namespace Tao2015

open ExpSums

noncomputable def sliceA2HeightRatio (epsc : ℝ) : ℕ :=
  max 2 (exceptionalIntervalRatio epsc)

noncomputable def sliceA2HeightP0 (epsc : ℝ) (H : ℕ) : ℕ :=
  max 21 ⌈(H : ℝ) ^ (1 / (4 * sliceA2HeightRatio epsc) : ℝ)⌉₊

noncomputable def sliceA2WindowPowerConstant : ℝ :=
  max 10000 (max 2000
    (max (3072000 * 4097 * 360000 * explicitSliceWindowConstant)
      (4 * sliceA2OuterConstant * 360000 * explicitSliceWindowConstant)))

noncomputable def sliceA2FrequencyTargetConstant : ℝ :=
  sliceA2KappaMain 0 / (32 * 163880000)

noncomputable def sliceA2FrequencyPowerConstant (epsc : ℝ) : ℝ :=
  sliceA2OuterConstant * 360000 * explicitSliceWindowConstant *
    sliceA2ZeroFrequencyPowerConstant epsc *
      (22 : ℝ) ^ sliceA2HeightRatio epsc /
        sliceA2FrequencyTargetConstant

noncomputable def sliceA2HeightPowerConstant (Cp epsc : ℝ) (Qlog0 : ℕ) : ℝ :=
  max 1 (max
    (sliceA2BottomPowerConstant Cp epsc Qlog0 ^
      (4 * sliceA2HeightRatio epsc))
    (max sliceA2WindowPowerConstant
      (sliceA2FrequencyPowerConstant epsc ^ 2)))

noncomputable def sliceA2HeightPower (epsc : ℝ) : ℕ :=
  4 * sliceA2HeightRatio epsc * sliceA2BottomPower + 100

theorem sliceA2HeightRatio_three_le (epsc : ℝ) :
    3 ≤ sliceA2HeightRatio epsc := by
  unfold sliceA2HeightRatio
  exact (exceptionalIntervalRatio_three_le epsc).trans (le_max_right _ _)

theorem sliceA2HeightRatio_eq (epsc : ℝ) :
    sliceA2HeightRatio epsc = exceptionalIntervalRatio epsc := by
  unfold sliceA2HeightRatio
  rw [max_eq_right]
  exact (exceptionalIntervalRatio_three_le epsc).trans' (by norm_num)

theorem sliceA2WindowPowerConstant_pos : 0 < sliceA2WindowPowerConstant := by
  unfold sliceA2WindowPowerConstant
  exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem sliceA2FrequencyTargetConstant_pos :
    0 < sliceA2FrequencyTargetConstant := by
  unfold sliceA2FrequencyTargetConstant sliceA2KappaMain ordinaryLegShare
  positivity

theorem sliceA2FrequencyPowerConstant_pos (epsc : ℝ) :
    0 < sliceA2FrequencyPowerConstant epsc := by
  unfold sliceA2FrequencyPowerConstant
  positivity [sliceA2OuterConstant_pos, one_le_explicitSliceWindowConstant,
    sliceA2ZeroFrequencyPowerConstant_pos epsc,
    sliceA2FrequencyTargetConstant_pos]

theorem sliceA2HeightPowerConstant_pos (Cp epsc : ℝ) (Qlog0 : ℕ) :
    0 < sliceA2HeightPowerConstant Cp epsc Qlog0 := by
  unfold sliceA2HeightPowerConstant
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem sliceA2HeightPower_bottom_exponent (epsc : ℝ) :
    4 * sliceA2HeightRatio epsc * sliceA2BottomPower ≤
      sliceA2HeightPower epsc := by
  unfold sliceA2HeightPower
  omega

theorem sliceA2HeightPower_fourteen (epsc : ℝ) :
    14 ≤ sliceA2HeightPower epsc := by
  have hR := sliceA2HeightRatio_three_le epsc
  unfold sliceA2HeightPower sliceA2BottomPower
  omega

theorem sliceA2HeightP0_root_le (epsc : ℝ) (H : ℕ) :
    (H : ℝ) ^ (1 / (4 * sliceA2HeightRatio epsc) : ℝ) ≤
      sliceA2HeightP0 epsc H := by
  unfold sliceA2HeightP0
  exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 21 _))

theorem sliceA2HeightP0_le_root
    (epsc : ℝ) (H : ℕ) (hH : 1 ≤ H) :
    (sliceA2HeightP0 epsc H : ℝ) ≤
      22 * (H : ℝ) ^ (1 / (4 * sliceA2HeightRatio epsc) : ℝ) := by
  let x := (H : ℝ) ^ (1 / (4 * sliceA2HeightRatio epsc) : ℝ)
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hx1 : 1 ≤ x := by
    dsimp [x]
    exact Real.one_le_rpow hH1 (by positivity)
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  have hceil : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  unfold sliceA2HeightP0
  push_cast
  apply max_le
  · nlinarith
  · linarith

theorem sliceA2Height_le_P0_pow
    (epsc : ℝ) (H : ℕ) (hH : 1 ≤ H) :
    (H : ℝ) ≤
      (sliceA2HeightP0 epsc H : ℝ) ^ (4 * sliceA2HeightRatio epsc) := by
  let n := 4 * sliceA2HeightRatio epsc
  let x := (H : ℝ) ^ (1 / (n : ℝ))
  have hn : 0 < n := by
    dsimp [n]
    have := sliceA2HeightRatio_three_le epsc
    positivity
  have hH0 : (0 : ℝ) ≤ H := by positivity
  have hx := sliceA2HeightP0_root_le epsc H
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hp := pow_le_pow_left₀ hx0 (by simpa [x, n] using hx) n
  calc
    (H : ℝ) = x ^ n := by
      dsimp [x]
      simpa [one_div] using (Real.rpow_inv_natCast_pow hH0 hn.ne').symm
    _ ≤ (sliceA2HeightP0 epsc H : ℝ) ^ n := hp
    _ = _ := by rfl

set_option maxHeartbeats 2000000 in
/-- The one polynomial height inequality produces a concrete bottom scale
and discharges the complete fixed-height ledger. -/
theorem sliceA2HeightClosed_of_power
    (Cp epsc eps : ℝ) (H Qlog0 : ℕ) (hCp1 : 1 ≤ Cp)
    (hepsc : 0 < epsc) (heps : 0 < eps)
    (hlogFit : ∀ Q : ℕ, Qlog0 ≤ Q →
      Real.log (Q : ℝ) ^ 6 ≤ (Q : ℝ) ^ (1 / 20 : ℝ))
    (hheight : sliceA2HeightPowerConstant Cp epsc Qlog0 /
        sliceA2EffectiveEps eps ^ sliceA2HeightPower epsc ≤ H) :
    SliceA2HeightClosed Cp epsc eps H (sliceA2HeightP0 epsc H) := by
  let e := sliceA2EffectiveEps eps
  let rho := sliceA2CanonicalRho eps
  let R := exceptionalIntervalRatio epsc
  let R0 := sliceA2HeightRatio epsc
  let eta := sliceA2ExceptionalLadderEta Cp e epsc (e / 100) rho
  let P0 := sliceA2HeightP0 epsc H
  let HC := sliceA2HeightPowerConstant Cp epsc Qlog0
  let KH := sliceA2HeightPower epsc
  have he : 0 < e := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).1
  have he1 : e ≤ 1 := by simpa [e] using (sliceA2EffectiveEps_bounds eps heps).2.1
  have hrho : 0 < rho := by simpa [rho] using sliceA2CanonicalRho_pos eps heps
  have hHC : 0 < HC := by
    simpa [HC] using sliceA2HeightPowerConstant_pos Cp epsc Qlog0
  have heKH : 0 < e ^ KH := by positivity
  have hheight' : HC / e ^ KH ≤ (H : ℝ) := by
    simpa [HC, KH, e] using hheight
  have hcomponent (x : ℝ) (n : ℕ) (hx0 : 0 ≤ x) (hxHC : x ≤ HC)
      (hn : n ≤ KH) : x / e ^ n ≤ (H : ℝ) := by
    have hePow : e ^ KH ≤ e ^ n := pow_le_pow_of_le_one he.le he1 hn
    exact (div_le_div₀ hHC.le hxHC (by positivity) hePow).trans hheight'
  have hHCone : (1 : ℝ) ≤ HC := by
    dsimp [HC, sliceA2HeightPowerConstant]
    exact le_max_left _ _
  have hH1R : (1 : ℝ) ≤ H := by
    have hone : (1 : ℝ) / e ^ 0 ≤ H :=
      hcomponent 1 0 zero_le_one hHCone (Nat.zero_le _)
    simpa using hone
  have hH1 : 1 ≤ H := by exact_mod_cast hH1R
  have hbottomHC :
      sliceA2BottomPowerConstant Cp epsc Qlog0 ^ (4 * R0) ≤ HC := by
    dsimp [HC, sliceA2HeightPowerConstant]
    exact (le_max_left _ _).trans (le_max_right 1 _)
  have hbottomExp : 4 * R0 * sliceA2BottomPower ≤ KH := by
    simpa [R0, KH] using sliceA2HeightPower_bottom_exponent epsc
  have hbottomHeight :
      sliceA2BottomPowerConstant Cp epsc Qlog0 ^ (4 * R0) /
          e ^ (4 * R0 * sliceA2BottomPower) ≤ (H : ℝ) :=
    hcomponent _ _ (by positivity [sliceA2BottomPowerConstant_pos Cp epsc Qlog0])
      hbottomHC hbottomExp
  have hbottomHeight' :
      (sliceA2BottomPowerConstant Cp epsc Qlog0 /
          e ^ sliceA2BottomPower) ^ (4 * R0) ≤ (H : ℝ) := by
    convert hbottomHeight using 1
    rw [div_pow, ← pow_mul]
    congr 2
    push_cast
    ring
  have hn : 0 < 4 * R0 := by
    have := sliceA2HeightRatio_three_le epsc
    positivity
  have hbottomRoot :
      sliceA2BottomPowerConstant Cp epsc Qlog0 /
          e ^ sliceA2BottomPower ≤
        (H : ℝ) ^ (1 / (4 * R0) : ℝ) := by
    let z := sliceA2BottomPowerConstant Cp epsc Qlog0 /
      e ^ sliceA2BottomPower
    have hz0 : 0 ≤ z := by
      dsimp [z]
      positivity [sliceA2BottomPowerConstant_pos Cp epsc Qlog0]
    have hr := Real.rpow_le_rpow (pow_nonneg hz0 (4 * R0)) hbottomHeight'
      (by positivity : (0 : ℝ) ≤ ((4 * R0 : ℕ) : ℝ)⁻¹)
    calc
      z = (z ^ (4 * R0)) ^ (((4 * R0 : ℕ) : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast hz0 hn.ne').symm
      _ ≤ (H : ℝ) ^ (((4 * R0 : ℕ) : ℝ)⁻¹) := hr
      _ = (H : ℝ) ^ (1 / (4 * R0) : ℝ) := by norm_num
  have hbottomP : sliceA2BottomPowerConstant Cp epsc Qlog0 /
      e ^ sliceA2BottomPower ≤ (P0 : ℝ) :=
    hbottomRoot.trans (by simpa [P0, R0] using sliceA2HeightP0_root_le epsc H)
  obtain ⟨hbottom, hzeroClose⟩ := sliceA2_bottom_closed_of_power
    Cp epsc eps P0 Qlog0 hCp1 hepsc heps hlogFit
      (by simpa [P0, e] using hbottomP)
  have hwindowHC : sliceA2WindowPowerConstant ≤ HC := by
    dsimp [HC, sliceA2HeightPowerConstant]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right 1 _))
  have h10000HC : (10000 : ℝ) ≤ HC :=
    (le_max_left _ _).trans hwindowHC
  have h2000HC : (2000 : ℝ) ≤ HC :=
    (le_max_left 2000 _).trans ((le_max_right 10000 _).trans hwindowHC)
  let CL := 3072000 * 4097 * 360000 * explicitSliceWindowConstant
  let CO := 4 * sliceA2OuterConstant * 360000 * explicitSliceWindowConstant
  have hCLHC : CL ≤ HC := by
    dsimp [CL, sliceA2WindowPowerConstant]
    exact (le_max_left _ _).trans ((le_max_right 2000 _).trans
      ((le_max_right 10000 _).trans hwindowHC))
  have hCOHC : CO ≤ HC := by
    dsimp [CO, sliceA2WindowPowerConstant]
    exact (le_max_right _ _).trans ((le_max_right 2000 _).trans
      ((le_max_right 10000 _).trans hwindowHC))
  have hKH14 : 14 ≤ KH := by
    simpa [KH] using sliceA2HeightPower_fourteen epsc
  have h10000 : (10000 : ℝ) / e ≤ H :=
    by simpa using hcomponent 10000 1 (by norm_num) h10000HC (by omega)
  have h2000 : (2000 : ℝ) / e ≤ H :=
    by simpa using hcomponent 2000 1 (by norm_num) h2000HC (by omega)
  have hCL : CL / e ^ 5 ≤ H :=
    hcomponent CL 5 (by dsimp [CL]; positivity [one_le_explicitSliceWindowConstant])
      hCLHC (by omega)
  have hCO : CO / e ^ 2 ≤ H :=
    hcomponent CO 2 (by dsimp [CO]; positivity [sliceA2OuterConstant_pos,
      one_le_explicitSliceWindowConstant])
      hCOHC (by omega)
  have hgeom : 100 ≤ sliceA2GeomEps eps * H := by
    unfold sliceA2GeomEps
    change 100 ≤ e / 100 * (H : ℝ)
    have := mul_le_mul_of_nonneg_left h10000 he.le
    field_simp at this ⊢
    nlinarith
  have hround : 2000 ≤ e * H := by
    have := mul_le_mul_of_nonneg_left h2000 he.le
    field_simp at this
    exact this
  have hparts := sliceA2Parts_le eps heps
  have hderiv : explicitSliceWindowDerivBound (sliceA2GeomEps eps) =
      360000 * explicitSliceWindowConstant / e := by
    unfold explicitSliceWindowDerivBound sliceA2GeomEps
    change 3600 * explicitSliceWindowConstant / (e / 100) = _
    field_simp
    ring
  have hlipschitz :
      3072000 * (sliceA2Parts eps : ℝ) *
          explicitSliceWindowDerivBound (sliceA2GeomEps eps) ≤ e ^ 2 * H := by
    rw [hderiv]
    have hraw : 3072000 * (sliceA2Parts eps : ℝ) *
        (360000 * explicitSliceWindowConstant / e) ≤ CL / e ^ 3 := by
      dsimp [CL]
      have hp : (sliceA2Parts eps : ℝ) ≤ 4097 / e ^ 2 := by
        simpa [e] using hparts
      calc
        3072000 * (sliceA2Parts eps : ℝ) *
            (360000 * explicitSliceWindowConstant / e) ≤
          3072000 * (4097 / e ^ 2) *
            (360000 * explicitSliceWindowConstant / e) := by
              gcongr <;> positivity [one_le_explicitSliceWindowConstant]
        _ = CL / e ^ 3 := by
          dsimp [CL]
          field_simp
    have hpay := mul_le_mul_of_nonneg_left hCL (sq_nonneg e)
    have hshape : e ^ 2 * (CL / e ^ 5) = CL / e ^ 3 := by
      field_simp
    rw [hshape] at hpay
    exact hraw.trans hpay
  have houter :
      4 * sliceA2OuterConstant *
          explicitSliceWindowDerivBound (sliceA2GeomEps eps) ≤ e * H := by
    rw [hderiv]
    have hpay := mul_le_mul_of_nonneg_left hCO he.le
    have hshape : e * (CO / e ^ 2) =
        4 * sliceA2OuterConstant *
          (360000 * explicitSliceWindowConstant / e) := by
      dsimp [CO]
      field_simp
    rw [hshape] at hpay
    exact hpay
  have hP021 : 21 ≤ P0 := by
    dsimp [P0, sliceA2HeightP0]
    exact le_max_left _ _
  have hP01 : (1 : ℝ) ≤ P0 := by exact_mod_cast (show 1 ≤ P0 by omega)
  have hP0pow := sliceA2Height_le_P0_pow epsc H hH1
  have hR0eq : R0 = R := by simpa [R0, R] using sliceA2HeightRatio_eq epsc
  have hP1form : (sliceA2LadderP P0 R eta 1 : ℝ) =
      (P0 : ℝ) ^ (100 * R0) := by
    simp only [sliceA2LadderP_succ, sliceA2LadderQ_eq,
      sliceA2LadderP_zero, sliceA2LadderRatio_zero, Nat.cast_pow]
    rw [show max 2 R = R0 by simpa [R0, R, sliceA2HeightRatio]]
    rw [← pow_mul]
    congr 1
    omega
  have hP1 : (H : ℝ) ≤ sliceA2LadderP P0 R eta 1 := by
    rw [hP1form]
    exact hP0pow.trans (pow_le_pow_right₀ hP01 (by omega))
  have hOuterOne : (1 : ℝ) ≤ sliceA2OuterConstant := by
    unfold sliceA2OuterConstant
    have hexp : 1 ≤ Real.exp Real.pi := by
      simpa using Real.exp_le_exp.mpr Real.pi_nonneg
    nlinarith
  have hderivOne : (1 : ℝ) ≤
      explicitSliceWindowDerivBound (sliceA2GeomEps eps) := by
    rw [hderiv]
    rw [le_div_iff₀ he]
    have hW := one_le_explicitSliceWindowConstant
    nlinarith
  have hfirstCoeff : (1 : ℝ) ≤
      2 * sliceA2OuterConstant *
        explicitSliceWindowDerivBound (sliceA2GeomEps eps) / e := by
    rw [le_div_iff₀ he]
    have hone : (1 : ℝ) ≤ 2 * sliceA2OuterConstant *
        explicitSliceWindowDerivBound (sliceA2GeomEps eps) := by nlinarith
    simpa using he1.trans hone
  have hfirst : 1 ≤
      (sliceA2LadderP P0 R eta 1 : ℝ) *
        (2 * sliceA2OuterConstant *
          explicitSliceWindowDerivBound (sliceA2GeomEps eps) / (e * H)) := by
    have hHpos : (0 : ℝ) < H := by positivity
    rw [show 2 * sliceA2OuterConstant *
        explicitSliceWindowDerivBound (sliceA2GeomEps eps) / (e * (H : ℝ)) =
      (2 * sliceA2OuterConstant *
        explicitSliceWindowDerivBound (sliceA2GeomEps eps) / e) / H by ring]
    rw [← mul_div_assoc, le_div_iff₀ hHpos]
    have hmul := mul_le_mul_of_nonneg_left hfirstCoeff
      (by positivity : 0 ≤ (sliceA2LadderP P0 R eta 1 : ℝ))
    simpa using hP1.trans (by simpa using hmul)
  let FC := sliceA2FrequencyPowerConstant epsc
  have hFCHC : FC ^ 2 ≤ HC := by
    dsimp [FC, HC, sliceA2HeightPowerConstant]
    exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right 1 _))
  have hFCheight : FC ^ 2 / e ^ 28 ≤ (H : ℝ) :=
    hcomponent (FC ^ 2) 28 (by positivity [sliceA2FrequencyPowerConstant_pos epsc])
      hFCHC (by
        dsimp [KH, sliceA2HeightPower, sliceA2BottomPower]
        have := sliceA2HeightRatio_three_le epsc
        omega)
  have hFCroot : FC / e ^ 14 ≤ (H : ℝ) ^ (1 / 2 : ℝ) := by
    have hFC0 : 0 ≤ FC / e ^ 14 := by positivity [sliceA2FrequencyPowerConstant_pos epsc]
    have hr := Real.rpow_le_rpow (pow_nonneg hFC0 2) (by
      convert hFCheight using 1
      field_simp
      ) (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
    calc
      FC / e ^ 14 = ((FC / e ^ 14) ^ 2) ^ ((2 : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast hFC0 (by norm_num : (2 : ℕ) ≠ 0)).symm
      _ ≤ (H : ℝ) ^ ((2 : ℝ)⁻¹) := hr
      _ = (H : ℝ) ^ (1 / 2 : ℝ) := by norm_num
  have hFCthreeQuarter : FC / e ^ 14 ≤ (H : ℝ) ^ (3 / 4 : ℝ) :=
    hFCroot.trans (Real.rpow_le_rpow_of_exponent_le hH1R (by norm_num))
  have hP0upper := sliceA2HeightP0_le_root epsc H hH1
  let x := (H : ℝ) ^ (1 / (4 * R0) : ℝ)
  have hx1 : 1 ≤ x := by
    dsimp [x]
    exact Real.one_le_rpow hH1R (by positivity)
  have hbase22 : (1 : ℝ) ≤ 22 * x := by nlinarith
  have hQform : (sliceA2LadderQ P0 R eta 0 : ℝ) = (P0 : ℝ) ^ R0 := by
    simp only [sliceA2LadderQ_eq, sliceA2LadderP_zero,
      sliceA2LadderRatio_zero, Nat.cast_pow]
    rw [show max 2 R = R0 by simpa [R0, R, sliceA2HeightRatio]]
  have hlogP : Real.log (P0 : ℝ) ≤ P0 := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < P0)
    linarith
  have hexponent : (1 : ℝ) + (R0 : ℝ) * (13 / 20 : ℝ) ≤ R0 := by
    have hR03 : (3 : ℝ) ≤ R0 := by exact_mod_cast sliceA2HeightRatio_three_le epsc
    nlinarith
  have hPQ : Real.log (P0 : ℝ) *
      (sliceA2LadderQ P0 R eta 0 : ℝ) ^ (13 / 20 : ℝ) ≤
        (22 : ℝ) ^ R0 * (H : ℝ) ^ (1 / 4 : ℝ) := by
    rw [hQform]
    have hpowform : ((P0 : ℝ) ^ R0) ^ (13 / 20 : ℝ) =
        (P0 : ℝ) ^ ((R0 : ℝ) * (13 / 20 : ℝ)) := by
      exact (Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ P0) R0
        (13 / 20 : ℝ)).symm
    rw [hpowform]
    calc
      Real.log (P0 : ℝ) *
          (P0 : ℝ) ^ ((R0 : ℝ) * (13 / 20 : ℝ)) ≤
        (P0 : ℝ) * (P0 : ℝ) ^ ((R0 : ℝ) * (13 / 20 : ℝ)) := by gcongr
      _ = (P0 : ℝ) ^ (1 + (R0 : ℝ) * (13 / 20 : ℝ)) := by
        calc
          (P0 : ℝ) * (P0 : ℝ) ^ ((R0 : ℝ) * (13 / 20 : ℝ)) =
              (P0 : ℝ) ^ (1 : ℝ) *
                (P0 : ℝ) ^ ((R0 : ℝ) * (13 / 20 : ℝ)) := by simp
          _ = _ := (Real.rpow_add (by positivity : (0 : ℝ) < P0) _ _).symm
      _ ≤ (P0 : ℝ) ^ (R0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hP01 hexponent
      _ = (P0 : ℝ) ^ R0 := Real.rpow_natCast _ _
      _ ≤ (22 * x) ^ R0 := pow_le_pow_left₀ (by positivity) (by simpa [P0, x] using hP0upper) R0
      _ = (22 : ℝ) ^ R0 * (H : ℝ) ^ (1 / 4 : ℝ) := by
        rw [mul_pow]
        have hxpow : x ^ R0 = (H : ℝ) ^ (1 / 4 : ℝ) := by
          dsimp [x]
          have hR0pos : (0 : ℝ) < R0 := by
            exact_mod_cast (show 0 < R0 by
              have := sliceA2HeightRatio_three_le epsc
              omega)
          have hexponent : (1 / (4 * (R0 : ℝ))) * (R0 : ℝ) = 1 / 4 := by
            field_simp [ne_of_gt hR0pos]
          rw [← Real.rpow_natCast,
            ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ H), hexponent]
        rw [hxpow]
  have hfrequencyCoeff := sliceA2OrdinaryZeroFrequencyCoefficient_le_power
    Cp P0 epsc eps heps
  have hfrequencyRaw :
      (sliceA2OuterConstant * 360000 * explicitSliceWindowConstant /
          (e ^ 2 * H)) *
        sliceA2OrdinaryZeroFrequencyCoefficient P0 R eta (e / 100) rho ≤
      sliceA2FrequencyTargetConstant * e ^ 4 := by
    have hcoef : sliceA2OrdinaryZeroFrequencyCoefficient P0 R eta (e / 100) rho ≤
        (sliceA2ZeroFrequencyPowerConstant epsc / e ^ 8) *
          Real.log (P0 : ℝ) *
            (sliceA2LadderQ P0 R eta 0 : ℝ) ^ (13 / 20 : ℝ) := by
      simpa [R, eta, e, rho] using hfrequencyCoeff
    have hmain : sliceA2OrdinaryZeroFrequencyCoefficient P0 R eta (e / 100) rho ≤
        (sliceA2ZeroFrequencyPowerConstant epsc / e ^ 8) *
          ((22 : ℝ) ^ R0 * (H : ℝ) ^ (1 / 4 : ℝ)) := by
      calc
        sliceA2OrdinaryZeroFrequencyCoefficient P0 R eta (e / 100) rho ≤
            (sliceA2ZeroFrequencyPowerConstant epsc / e ^ 8) *
              Real.log (P0 : ℝ) *
                (sliceA2LadderQ P0 R eta 0 : ℝ) ^ (13 / 20 : ℝ) := hcoef
        _ = (sliceA2ZeroFrequencyPowerConstant epsc / e ^ 8) *
            (Real.log (P0 : ℝ) *
              (sliceA2LadderQ P0 R eta 0 : ℝ) ^ (13 / 20 : ℝ)) := by ring
        _ ≤ (sliceA2ZeroFrequencyPowerConstant epsc / e ^ 8) *
            ((22 : ℝ) ^ R0 * (H : ℝ) ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hPQ (by
            positivity [sliceA2ZeroFrequencyPowerConstant_pos epsc])
    have hHpos : (0 : ℝ) < H := by positivity
    have hpay := hFCthreeQuarter
    have htarget := sliceA2FrequencyTargetConstant_pos
    let AC := sliceA2OuterConstant * 360000 * explicitSliceWindowConstant *
      sliceA2ZeroFrequencyPowerConstant epsc * (22 : ℝ) ^ R0
    have hFCform : FC = AC / sliceA2FrequencyTargetConstant := by
      dsimp [FC, AC, sliceA2FrequencyPowerConstant]
    have hFCpay : FC ≤ e ^ 14 * (H : ℝ) ^ (3 / 4 : ℝ) := by
      rw [div_le_iff₀ (by positivity : 0 < e ^ 14)] at hpay
      simpa [mul_comm] using hpay
    have hACpay : AC ≤ sliceA2FrequencyTargetConstant * e ^ 14 *
        (H : ℝ) ^ (3 / 4 : ℝ) := by
      rw [hFCform] at hFCpay
      have := (div_le_iff₀ htarget).mp hFCpay
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have hHpow : (H : ℝ) ^ (3 / 4 : ℝ) *
        (H : ℝ) ^ (1 / 4 : ℝ) = H := by
      rw [← Real.rpow_add hHpos]
      norm_num
    have hACmul : AC * (H : ℝ) ^ (1 / 4 : ℝ) ≤
        sliceA2FrequencyTargetConstant * e ^ 14 * H := by
      have hm := mul_le_mul_of_nonneg_right hACpay
        (by positivity : 0 ≤ (H : ℝ) ^ (1 / 4 : ℝ))
      calc
        AC * (H : ℝ) ^ (1 / 4 : ℝ) ≤
            (sliceA2FrequencyTargetConstant * e ^ 14 *
              (H : ℝ) ^ (3 / 4 : ℝ)) *
                (H : ℝ) ^ (1 / 4 : ℝ) := hm
        _ = sliceA2FrequencyTargetConstant * e ^ 14 * H := by
          rw [show (sliceA2FrequencyTargetConstant * e ^ 14 *
              (H : ℝ) ^ (3 / 4 : ℝ)) * (H : ℝ) ^ (1 / 4 : ℝ) =
            sliceA2FrequencyTargetConstant * e ^ 14 *
              ((H : ℝ) ^ (3 / 4 : ℝ) * (H : ℝ) ^ (1 / 4 : ℝ)) by ring,
            hHpow]
    calc
      (sliceA2OuterConstant * 360000 * explicitSliceWindowConstant /
          (e ^ 2 * H)) *
          sliceA2OrdinaryZeroFrequencyCoefficient P0 R eta (e / 100) rho ≤
        (sliceA2OuterConstant * 360000 * explicitSliceWindowConstant /
          (e ^ 2 * H)) *
          ((sliceA2ZeroFrequencyPowerConstant epsc / e ^ 8) *
            ((22 : ℝ) ^ R0 * (H : ℝ) ^ (1 / 4 : ℝ))) := by
        exact mul_le_mul_of_nonneg_left hmain (by
          positivity [sliceA2OuterConstant_pos, one_le_explicitSliceWindowConstant])
      _ ≤ sliceA2FrequencyTargetConstant * e ^ 4 := by
        have hshape :
            (sliceA2OuterConstant * 360000 * explicitSliceWindowConstant /
              (e ^ 2 * H)) *
              ((sliceA2ZeroFrequencyPowerConstant epsc / e ^ 8) *
                ((22 : ℝ) ^ R0 * (H : ℝ) ^ (1 / 4 : ℝ))) =
            (AC * (H : ℝ) ^ (1 / 4 : ℝ)) / (e ^ 10 * H) := by
          dsimp [AC]
          field_simp
        rw [hshape, div_le_iff₀ (by positivity : 0 < e ^ 10 * (H : ℝ))]
        convert hACmul using 1 <;> ring
  have hfrequency :
      (sliceA2OuterConstant *
          explicitSliceWindowDerivBound (sliceA2GeomEps eps) / (e * H)) *
        sliceA2OrdinaryZeroFrequencyCoefficient P0 R eta (e / 100) rho ≤
      (sliceA2KappaMain 0 / 2 * ((e / 100) ^ 2 * rho / 8)) / 2 := by
    rw [hderiv]
    have hleft : sliceA2OuterConstant *
        (360000 * explicitSliceWindowConstant / e) / (e * (H : ℝ)) =
      sliceA2OuterConstant * 360000 * explicitSliceWindowConstant /
        (e ^ 2 * H) := by ring
    rw [hleft]
    refine hfrequencyRaw.trans ?_
    unfold sliceA2FrequencyTargetConstant
    have hproduct : e ^ 4 / 163880000 ≤ (e / 100) ^ 2 * rho := by
      calc
        e ^ 4 / 163880000 = (e / 100) ^ 2 * (e ^ 2 / 16388) := by ring
        _ ≤ (e / 100) ^ 2 * rho := by
          gcongr
          simpa [e, rho] using sliceA2EffectiveEps_sq_le_rho eps heps
    have hprod := mul_le_mul_of_nonneg_left (by
      simpa using hproduct)
      (by
        unfold sliceA2KappaMain ordinaryLegShare
        positivity : 0 ≤ sliceA2KappaMain 0 / 32)
    convert hprod using 1 <;> ring
  change SliceA2HeightClosed Cp epsc eps H P0
  refine ⟨Qlog0, hP021, ?_, ?_, ?_, ?_, ?_, hlogFit, ?_, ?_, ?_⟩
  · simpa [sliceA2GeomEps, e] using hgeom
  · simpa [e] using hround
  · simpa [e] using hlipschitz
  · simpa [e] using houter
  · simpa [e, rho, sliceA2CanonicalRho, eta, R] using hbottom
  · simpa [e, rho, sliceA2CanonicalRho, eta, R] using hzeroClose
  · simpa [e, rho, sliceA2CanonicalRho, eta, R] using hfirst
  · simpa [e, rho, sliceA2CanonicalRho, eta, R] using hfrequency

end Tao2015

end MoltResearch
