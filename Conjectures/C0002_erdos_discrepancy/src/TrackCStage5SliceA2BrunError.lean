import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2BrunLadder

/-!
# Track R A2-V'-28: a uniform envelope for finite Brun errors

Upper Mertens bounds the canonical truncation depth using only the interval
ratio.  Cardinality is bounded by the upper endpoint.  Monotonicity then
reduces every positive-level finite error to the last scheduled endpoint and
ratio.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- Ratio-only upper bound for the canonical Brun depth. -/
noncomputable def brunPowerIntervalDepth (R : ℕ) : ℕ :=
  ⌈Real.exp 1 * (Real.log ((R : ℝ) + 1) + 12)⌉₊

/-- Upper Mertens controls the canonical depth in a power interval. -/
theorem brunPowerInterval_depth_le
    (P R : ℕ) (hP : 3 ≤ P) (hR : 1 ≤ R) :
    ⌈Real.exp 1 *
        (∑ p ∈ (Ioc P (P ^ R)).filter Nat.Prime, (1 : ℝ) / p)⌉₊ ≤
      brunPowerIntervalDepth R := by
  unfold brunPowerIntervalDepth
  apply Nat.ceil_mono
  exact mul_le_mul_of_nonneg_left
    (prime_power_Ioc_mass_upper P R hP hR) (Real.exp_pos 1).le

/-- The finite error for `(P,P^R]` is bounded by its endpoint and the
ratio-only depth. -/
theorem brunPowerIntervalFiniteError_le
    (a P R : ℕ) (ha : 1 ≤ a) (hP : 3 ≤ P) (hR : 1 ≤ R) :
    brunPowerIntervalFiniteError a P R ≤
      2 * (((P ^ R : ℕ) : ℝ) + 1) ^
          (2 * brunPowerIntervalDepth R) / a := by
  let L := (Ioc P (P ^ R)).filter Nat.Prime
  let E := ∑ p ∈ L, (1 : ℝ) / p
  let k := ⌈Real.exp 1 * E⌉₊
  let K := brunPowerIntervalDepth R
  have hk : k ≤ K := by
    dsimp [k, E, L, K]
    exact brunPowerInterval_depth_le P R hP hR
  have hcardNat : L.card ≤ P ^ R := by
    calc
      L.card ≤ (Ioc P (P ^ R)).card := card_filter_le _ _
      _ = P ^ R - P := Nat.card_Ioc P (P ^ R)
      _ ≤ P ^ R := Nat.sub_le _ _
  have hbase : (L.card : ℝ) + 1 ≤ (P ^ R : ℕ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hcardNat 1
  have hbase0 : (0 : ℝ) ≤ (L.card : ℝ) + 1 := by positivity
  have hupper1 : (1 : ℝ) ≤ (P ^ R : ℕ) + 1 := by
    exact_mod_cast (show 1 ≤ P ^ R + 1 by omega)
  have hpowBase : ((L.card : ℝ) + 1) ^ (2 * k) ≤
      (((P ^ R : ℕ) : ℝ) + 1) ^ (2 * k) :=
    pow_le_pow_left₀ hbase0 hbase (2 * k)
  have hpowExp : (((P ^ R : ℕ) : ℝ) + 1) ^ (2 * k) ≤
      (((P ^ R : ℕ) : ℝ) + 1) ^ (2 * K) :=
    pow_le_pow_right₀ hupper1 (Nat.mul_le_mul_left 2 hk)
  have ha0 : (0 : ℝ) ≤ a := by positivity
  unfold brunPowerIntervalFiniteError
  dsimp only
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hpowBase.trans hpowExp) (by norm_num)) ha0

/-- The positive-level ratios are monotone. -/
theorem sliceA2LadderRatio_mono_of_pos
    (ratio0 eta i j : ℕ) (hi : 0 < i) (hij : i ≤ j) :
    sliceA2LadderRatio ratio0 eta i ≤
      sliceA2LadderRatio ratio0 eta j := by
  have hj : 0 < j := hi.trans_le hij
  rw [sliceA2LadderRatio_of_pos ratio0 eta i hi,
    sliceA2LadderRatio_of_pos ratio0 eta j hj]
  apply max_le_max_left
  exact Nat.mul_le_mul_right eta (pow_le_pow_right' (by norm_num) hij)

/-- The ratio-only Brun depth is monotone. -/
theorem brunPowerIntervalDepth_mono
    {R S : ℕ} (hRS : R ≤ S) :
    brunPowerIntervalDepth R ≤ brunPowerIntervalDepth S := by
  unfold brunPowerIntervalDepth
  apply Nat.ceil_mono
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
  gcongr

/-- Every finite error in the first `n` positive levels is bounded by the
last endpoint and ratio. -/
theorem sliceA2PositiveLadder_brunErrors_le
    (P0 ratio0 eta n a : ℕ) (hP0 : 3 ≤ P0) (ha : 1 ≤ a) :
    ∑ i ∈ range n,
        brunPowerIntervalFiniteError a
          (sliceA2LadderP P0 ratio0 eta (i + 1))
          (sliceA2LadderRatio ratio0 eta (i + 1)) ≤
      n * (2 *
        (((sliceA2LadderQ P0 ratio0 eta n : ℕ) : ℝ) + 1) ^
          (2 * brunPowerIntervalDepth
            (sliceA2LadderRatio ratio0 eta n)) / a) := by
  have hterm : ∀ i ∈ range n,
      brunPowerIntervalFiniteError a
          (sliceA2LadderP P0 ratio0 eta (i + 1))
          (sliceA2LadderRatio ratio0 eta (i + 1)) ≤
        2 * (((sliceA2LadderQ P0 ratio0 eta n : ℕ) : ℝ) + 1) ^
          (2 * brunPowerIntervalDepth
            (sliceA2LadderRatio ratio0 eta n)) / a := by
    intro i hi
    have hin : i < n := mem_range.mp hi
    let Pi := sliceA2LadderP P0 ratio0 eta (i + 1)
    let Ri := sliceA2LadderRatio ratio0 eta (i + 1)
    let Qi := sliceA2LadderQ P0 ratio0 eta (i + 1)
    let Qn := sliceA2LadderQ P0 ratio0 eta n
    let Ki := brunPowerIntervalDepth Ri
    let Kn := brunPowerIntervalDepth (sliceA2LadderRatio ratio0 eta n)
    have hPi : 3 ≤ Pi := hP0.trans
      (sliceA2LadderP_mono P0 ratio0 eta (by omega) (Nat.zero_le (i + 1)))
    have hRi : 1 ≤ Ri :=
      (sliceA2LadderRatio_two_le ratio0 eta (i + 1)).trans' (by norm_num)
    have hraw := brunPowerIntervalFiniteError_le a Pi Ri ha hPi hRi
    have hQ : Qi ≤ Qn := by
      dsimp [Qi, Qn]
      simpa only [Nat.add_sub_cancel] using!
        sliceA2LadderQ_le_last P0 ratio0 eta (n + 1) (i + 1)
          (by omega) (by omega) (by omega)
    have hR : Ri ≤ sliceA2LadderRatio ratio0 eta n := by
      dsimp [Ri]
      exact sliceA2LadderRatio_mono_of_pos ratio0 eta (i + 1) n
        (by omega) (by omega)
    have hK : Ki ≤ Kn := by
      dsimp [Ki, Kn]
      exact brunPowerIntervalDepth_mono hR
    have hbase : ((Qi : ℕ) : ℝ) + 1 ≤ (Qn : ℕ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hQ 1
    have hbase0 : (0 : ℝ) ≤ (Qi : ℕ) + 1 := by positivity
    have hQn1 : (1 : ℝ) ≤ (Qn : ℕ) + 1 := by
      exact_mod_cast (show 1 ≤ Qn + 1 by omega)
    have hpow : ((Qi : ℝ) + 1) ^ (2 * Ki) ≤
        ((Qn : ℝ) + 1) ^ (2 * Kn) := by
      calc
        ((Qi : ℝ) + 1) ^ (2 * Ki) ≤
            ((Qn : ℝ) + 1) ^ (2 * Ki) :=
          pow_le_pow_left₀ hbase0 hbase (2 * Ki)
        _ ≤ ((Qn : ℝ) + 1) ^ (2 * Kn) :=
          pow_le_pow_right₀ hQn1 (Nat.mul_le_mul_left 2 hK)
    have ha0 : (0 : ℝ) ≤ a := by positivity
    calc
      brunPowerIntervalFiniteError a Pi Ri ≤
          2 * (((Pi ^ Ri : ℕ) : ℝ) + 1) ^ (2 * Ki) / a := by
        simpa [Ki] using hraw
      _ = 2 * ((Qi : ℝ) + 1) ^ (2 * Ki) / a := by
        rw [show Pi ^ Ri = Qi by dsimp [Pi, Ri, Qi]]
      _ ≤ 2 * ((Qn : ℝ) + 1) ^ (2 * Kn) / a :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by norm_num)) ha0
      _ = _ := by rfl
  calc
    ∑ i ∈ range n,
        brunPowerIntervalFiniteError a
          (sliceA2LadderP P0 ratio0 eta (i + 1))
          (sliceA2LadderRatio ratio0 eta (i + 1)) ≤
      ∑ _i ∈ range n, 2 *
        (((sliceA2LadderQ P0 ratio0 eta n : ℕ) : ℝ) + 1) ^
          (2 * brunPowerIntervalDepth
            (sliceA2LadderRatio ratio0 eta n)) / a := sum_le_sum hterm
    _ = n * (2 *
        (((sliceA2LadderQ P0 ratio0 eta n : ℕ) : ℝ) + 1) ^
          (2 * brunPowerIntervalDepth
            (sliceA2LadderRatio ratio0 eta n)) / a) := by
      rw [sum_const, card_range, nsmul_eq_mul]

end Tao2015

end MoltResearch
