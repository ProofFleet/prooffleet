import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OuterWindow

/-!
# Track R A2-V': concrete explicit-window parameters

The effective accuracy is `min eps 1`.  We use `4096/e²` equal slices, a
geometric collar accuracy `e/100`, low cutoff `e²/10¹²`, outer cutoff
proportional to `B'A/(eH)`, and tail cutoff `A²`.
-/

namespace MoltResearch

namespace Tao2015

open ExpSums

noncomputable def sliceA2EffectiveEps (eps : ℝ) : ℝ := min eps 1

noncomputable def sliceA2GeomEps (eps : ℝ) : ℝ :=
  sliceA2EffectiveEps eps / 100

noncomputable def sliceA2Parts (eps : ℝ) : ℕ :=
  max 30 ⌈4096 / sliceA2EffectiveEps eps ^ 2⌉₊

noncomputable def sliceA2LowCutoff (eps : ℝ) : ℝ :=
  sliceA2EffectiveEps eps ^ 2 / 10 ^ 12

noncomputable def sliceA2OuterConstant : ℝ :=
  1105920 * Real.exp Real.pi

noncomputable def sliceA2OuterCutoff (eps : ℝ) (A H : ℕ) : ℝ :=
  sliceA2OuterConstant *
    explicitSliceWindowDerivBound (sliceA2GeomEps eps) * (A : ℝ) /
      (sliceA2EffectiveEps eps * H)

noncomputable def sliceA2TailCutoff (A : ℕ) : ℝ := (A : ℝ) ^ 2

noncomputable def sliceA2FourierDepth (eps : ℝ) (A H : ℕ) : ℕ :=
  ⌈sliceA2TailCutoff A / sliceA2OuterCutoff eps A H⌉₊ + 1

theorem sliceA2EffectiveEps_bounds (eps : ℝ) (heps : 0 < eps) :
    0 < sliceA2EffectiveEps eps ∧ sliceA2EffectiveEps eps ≤ 1 ∧
      sliceA2EffectiveEps eps ≤ eps := by
  unfold sliceA2EffectiveEps
  exact ⟨lt_min heps zero_lt_one, min_le_right _ _, min_le_left _ _⟩

theorem sliceA2GeomEps_bounds (eps : ℝ) (heps : 0 < eps) :
    0 < sliceA2GeomEps eps ∧ sliceA2GeomEps eps ≤ 1 := by
  obtain ⟨he, he1, heeps⟩ := sliceA2EffectiveEps_bounds eps heps
  unfold sliceA2GeomEps
  constructor
  · positivity
  · nlinarith

theorem sliceA2Parts_bounds (eps : ℝ) (heps : 0 < eps) :
    0 < sliceA2Parts eps ∧ 30 ≤ sliceA2Parts eps ∧
      4096 / sliceA2EffectiveEps eps ^ 2 ≤ sliceA2Parts eps := by
  obtain ⟨he, he1, heeps⟩ := sliceA2EffectiveEps_bounds eps heps
  have hceil : 4096 / sliceA2EffectiveEps eps ^ 2 ≤
      (⌈4096 / sliceA2EffectiveEps eps ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  have hM30 : 30 ≤ sliceA2Parts eps := by
    unfold sliceA2Parts
    exact le_max_left _ _
  have hceilM : ⌈4096 / sliceA2EffectiveEps eps ^ 2⌉₊ ≤
      sliceA2Parts eps := by
    unfold sliceA2Parts
    exact le_max_right _ _
  refine ⟨by omega, hM30, hceil.trans ?_⟩
  exact_mod_cast hceilM

/-- The chosen number of pieces satisfies both the partition remainder
budget and the collar's relative-width margin. -/
theorem sliceA2Parts_budget (eps : ℝ) (heps : 0 < eps) :
    16 ≤ eps ^ 2 * sliceA2Parts eps ∧
      1000 ≤ sliceA2EffectiveEps eps * sliceA2Parts eps := by
  obtain ⟨he, he1, heeps⟩ := sliceA2EffectiveEps_bounds eps heps
  obtain ⟨hM0, hM30, hM⟩ := sliceA2Parts_bounds eps heps
  have he2 : sliceA2EffectiveEps eps ^ 2 ≤ eps ^ 2 :=
    pow_le_pow_left₀ he.le heeps 2
  have hMe : 4096 ≤ sliceA2EffectiveEps eps ^ 2 * sliceA2Parts eps := by
    have hmul := mul_le_mul_of_nonneg_left hM
      (sq_nonneg (sliceA2EffectiveEps eps))
    have hne : sliceA2EffectiveEps eps ^ 2 ≠ 0 := by positivity
    field_simp at hmul
    exact hmul
  constructor
  · have hcomp : sliceA2EffectiveEps eps ^ 2 * sliceA2Parts eps ≤
        eps ^ 2 * sliceA2Parts eps := by gcongr
    linarith
  · have heSq : sliceA2EffectiveEps eps ^ 2 ≤ sliceA2EffectiveEps eps := by
      nlinarith [sq_nonneg (sliceA2EffectiveEps eps)]
    have hcomp : sliceA2EffectiveEps eps ^ 2 * sliceA2Parts eps ≤
        sliceA2EffectiveEps eps * sliceA2Parts eps := by gcongr
    have heM : 4096 ≤ sliceA2EffectiveEps eps * sliceA2Parts eps :=
      hMe.trans hcomp
    linarith

/-- A convenient upper bound for the rounded number of pieces. -/
theorem sliceA2Parts_le (eps : ℝ) (heps : 0 < eps) :
    (sliceA2Parts eps : ℝ) ≤ 4097 / sliceA2EffectiveEps eps ^ 2 := by
  obtain ⟨he, he1, heeps⟩ := sliceA2EffectiveEps_bounds eps heps
  let x : ℝ := 4096 / sliceA2EffectiveEps eps ^ 2
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx30 : (30 : ℝ) ≤ x := by
    dsimp [x]
    have he20 : 0 < sliceA2EffectiveEps eps ^ 2 := sq_pos_of_pos he
    rw [le_div_iff₀ he20]
    nlinarith [sq_nonneg (sliceA2EffectiveEps eps)]
  have hceil : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hmax : sliceA2Parts eps = ⌈x⌉₊ := by
    unfold sliceA2Parts
    rw [max_eq_right]
    have h30ceil : 30 ≤ ⌈x⌉₊ := by
      exact_mod_cast hx30.trans (Nat.le_ceil x)
    simpa [x] using h30ceil
  rw [hmax]
  have hone : (1 : ℝ) ≤ 1 / sliceA2EffectiveEps eps ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos he)]
    nlinarith [sq_nonneg (sliceA2EffectiveEps eps)]
  dsimp [x] at hceil
  have hlt : (⌈4096 / sliceA2EffectiveEps eps ^ 2⌉₊ : ℝ) <
      4097 / sliceA2EffectiveEps eps ^ 2 := by
    calc
    (⌈4096 / sliceA2EffectiveEps eps ^ 2⌉₊ : ℝ) <
        4096 / sliceA2EffectiveEps eps ^ 2 + 1 := hceil
    _ ≤ 4096 / sliceA2EffectiveEps eps ^ 2 +
        1 / sliceA2EffectiveEps eps ^ 2 := by gcongr
    _ = 4097 / sliceA2EffectiveEps eps ^ 2 := by ring
  exact hlt.le

theorem sliceA2LowCutoff_pos (eps : ℝ) (heps : 0 < eps) :
    0 < sliceA2LowCutoff eps := by
  unfold sliceA2LowCutoff
  positivity [sliceA2EffectiveEps_bounds eps heps |>.1]

theorem sliceA2LowCutoff_le_one (eps : ℝ) (heps : 0 < eps) :
    sliceA2LowCutoff eps ≤ 1 := by
  obtain ⟨he, he1, heeps⟩ := sliceA2EffectiveEps_bounds eps heps
  unfold sliceA2LowCutoff
  have he2 : sliceA2EffectiveEps eps ^ 2 ≤ 1 := by nlinarith [sq_nonneg (sliceA2EffectiveEps eps)]
  norm_num at ⊢
  linarith

theorem sliceA2OuterConstant_pos : 0 < sliceA2OuterConstant := by
  unfold sliceA2OuterConstant
  positivity

theorem sliceA2OuterCutoff_pos
    (eps : ℝ) (A H : ℕ) (heps : 0 < eps) (hA : 0 < A) (hH : 0 < H) :
    0 < sliceA2OuterCutoff eps A H := by
  unfold sliceA2OuterCutoff
  obtain ⟨he, he1, heeps⟩ := sliceA2EffectiveEps_bounds eps heps
  have hgeom := (sliceA2GeomEps_bounds eps heps).1
  unfold explicitSliceWindowDerivBound
  positivity [sliceA2OuterConstant_pos, one_le_explicitSliceWindowConstant]

/-- The selected outer cutoff satisfies the cross-multiplied outer-band
condition with room to spare. -/
theorem sliceA2OuterCutoff_fit
    (eps : ℝ) (A H : ℕ) (heps : 0 < eps) (hA : 0 < A) (hH : 0 < H) :
    1105920 * Real.exp Real.pi *
        explicitSliceWindowDerivBound (sliceA2GeomEps eps) ^ 2 * (A : ℝ) ^ 2 ≤
      sliceA2EffectiveEps eps ^ 2 * (H : ℝ) ^ 2 * Real.pi ^ 2 *
        sliceA2OuterCutoff eps A H ^ 2 := by
  obtain ⟨he, he1, heeps⟩ := sliceA2EffectiveEps_bounds eps heps
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hC : (1 : ℝ) ≤ Real.pi ^ 2 * sliceA2OuterConstant := by
    have hpi2 : (1 : ℝ) ≤ Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 1)]
    have hexp : (1 : ℝ) ≤ Real.exp Real.pi := Real.one_le_exp Real.pi_pos.le
    unfold sliceA2OuterConstant
    nlinarith [mul_nonneg (zero_le_one.trans hpi2) (zero_le_one.trans hexp)]
  unfold sliceA2OuterCutoff
  have hnonneg : 0 ≤
      1105920 * Real.exp Real.pi *
        explicitSliceWindowDerivBound (sliceA2GeomEps eps) ^ 2 * (A : ℝ) ^ 2 := by
    positivity
  have hshape :
      sliceA2EffectiveEps eps ^ 2 * (H : ℝ) ^ 2 * Real.pi ^ 2 *
          (sliceA2OuterConstant *
            explicitSliceWindowDerivBound (sliceA2GeomEps eps) * (A : ℝ) /
              (sliceA2EffectiveEps eps * H)) ^ 2 =
        (Real.pi ^ 2 * sliceA2OuterConstant) *
          (1105920 * Real.exp Real.pi *
            explicitSliceWindowDerivBound (sliceA2GeomEps eps) ^ 2 * (A : ℝ) ^ 2) := by
    unfold sliceA2OuterConstant
    field_simp
  rw [hshape]
  exact le_mul_of_one_le_left hnonneg hC

theorem sliceA2TailCutoff_pos (A : ℕ) (hA : 0 < A) :
    0 < sliceA2TailCutoff A := by
  unfold sliceA2TailCutoff
  positivity

/-- The canonical dyadic depth reaches the tail cutoff. -/
theorem sliceA2FourierDepth_fit
    (eps : ℝ) (A H : ℕ) (heps : 0 < eps) (hA : 0 < A) (hH : 0 < H) :
    sliceA2TailCutoff A <
      2 ^ sliceA2FourierDepth eps A H * sliceA2OuterCutoff eps A H := by
  let x := sliceA2TailCutoff A / sliceA2OuterCutoff eps A H
  let J := ⌈x⌉₊ + 1
  have hK : 0 < sliceA2OuterCutoff eps A H :=
    sliceA2OuterCutoff_pos eps A H heps hA hH
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (sliceA2TailCutoff_pos A hA).le hK.le
  have hxceil : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hceilJ : (⌈x⌉₊ : ℝ) < J := by dsimp [J]; norm_num
  have hJpowNat : J < 2 ^ J := Nat.lt_two_pow_self
  have hJpow : (J : ℝ) < ((2 ^ J : ℕ) : ℝ) := by exact_mod_cast hJpowNat
  have hxpow : x < ((2 ^ J : ℕ) : ℝ) := hxceil.trans_lt (hceilJ.trans hJpow)
  have hmul := mul_lt_mul_of_pos_right hxpow hK
  have hshape : x * sliceA2OuterCutoff eps A H = sliceA2TailCutoff A := by
    dsimp [x]
    field_simp
  simpa [sliceA2FourierDepth, J, hshape] using hmul

end Tao2015

end MoltResearch
