import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OneSlice
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2LowBand
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2Transfer

/-!
# Track R A2-V': close the explicit low-band slot

The Halasz saving is `e/32`, while the positive ladder is allowed absolute
mass `e/4`.  Since the low cutoff is `e^2/10^12`, these deliberately coarse
pointwise bounds still fit the normalized short-slice allocation.
-/

namespace MoltResearch

namespace Tao2015

open Real Finset MeasureTheory ExpSums

set_option maxHeartbeats 800000 in
/-- The top-scale split estimate fits the low Fourier slot of every full
floor slice. -/
theorem sliceA2_low_band_fit (eps : ℝ) (heps : 0 < eps) :
    ∃ (D0 : ℝ) (x0 : ℕ), 1 ≤ D0 ∧ cellHalaszThreshold ≤ x0 ∧
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → g 1 = 1 →
        (∀ n, ‖g n‖ ≤ 1) →
      ∀ Pl : ℕ → Finset ℕ, ∀ Pu : Finset ℕ, ∀ J : ℕ, 0 < J →
        (∀ p ∈ Pl 0, p.Prime) → (∀ p ∈ Pu, p.Prime) →
      ∀ A X Delta : ℕ,
        sliceA2Parts eps ≤ A → A ≤ X → X ≤ 2 * A →
        0 < Delta → Delta ≤ X → x0 ≤ X →
      ∀ A0 : ℝ, 9 ≤ A0 →
        NonPretentiousAt g (A0 / 9) (3 * (2 * X + 1)) →
      ∀ D : ℝ, D0 ≤ D →
        2 * Real.pi * sliceA2LowCutoff eps +
            2 * Real.pi *
              (((halaszM (3 * (2 * X + 1)) : ℕ) : ℝ) + 1) ≤
          (A0 / 9) * ((3 * (2 * X + 1) : ℕ) : ℝ) →
        2 * D ≤ A0 / 9 -
          2 * (Real.log (Real.log ((3 * (2 * X + 1) : ℕ) : ℝ)) -
            Real.log (Real.log (X : ℝ)) + 12) →
        ladderSiftedLogMass X (X + Delta)
            ((List.range (J - 1)).map (fun i => Pl (i + 1))) ≤
          sliceA2EffectiveEps eps / 4 →
        (∫ t in {t : ℝ | |t| < sliceA2LowCutoff eps},
          ‖∑ m ∈ typicalS X (X + Delta) (innerBandLevels Pl Pu J),
              (g m / (m : ℂ)) *
                ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖ ^ 2)
          ≤ sliceA2EffectiveEps eps ^ 2 *
            (∑ n ∈ Finset.Ioc X (X + A / sliceA2Parts eps),
              (1 : ℝ) / n) / 12288 := by
  let e := sliceA2EffectiveEps eps
  have he : 0 < e := by exact sliceA2EffectiveEps_bounds eps heps |>.1
  have he1 : e ≤ 1 := by exact sliceA2EffectiveEps_bounds eps heps |>.2.1
  have heta : 0 < e / 32 := by positivity
  have heta1 : e / 32 ≤ 1 := by linarith
  obtain ⟨D0, x0, hD0, hx0, hlow⟩ :=
    integral_norm_typicalS_dirichlet_poly_sq_le_low_band_top_split_eps
      (e / 32) heta heta1
  refine ⟨D0, x0, hD0, hx0, ?_⟩
  intro g hcm hg1 hg Pl Pu J hJ hPl hPu A X Delta hMA hAX hX2A
    hDelta0 hDelta x0X A0 hA0 hNP D hD hrange hstrength hRem
  let base : List (Finset ℕ) := [Pl 0, Pu]
  let ladder : List (Finset ℕ) :=
    (List.range (J - 1)).map (fun i => Pl (i + 1))
  have hbase : ∀ Q ∈ base, ∀ p ∈ Q, p.Prime := by
    intro Q hQ p hp
    simp only [base, List.mem_cons] at hQ
    rcases hQ with rfl | hQ
    · exact hPl p hp
    · have hQ' : Q = Pu := by simpa using hQ
      subst Q
      exact hPu p hp
  have hX : 0 < X := by
    have hM0 := sliceA2Parts_bounds eps heps |>.1
    omega
  have hX1 : 1 ≤ X := hX
  have hab : X < X + Delta := by
    omega
  have hb3 : X + Delta ≤ 3 * X := by omega
  have h3bN : 3 * (X + Delta) ≤ 3 * (2 * X + 1) := by omega
  have hraw := hlow g hcm hg1 hg base ladder hbase X (X + Delta)
    x0X hab hb3 (A0 / 9) (by linarith) (3 * (2 * X + 1)) hNP h3bN
    D hD (sliceA2LowCutoff eps) (sliceA2LowCutoff_pos eps heps).le
    hrange hstrength (e / 4) (by positivity)
    (by simpa [e, ladder] using hRem)
  have hratio : ((X + Delta : ℕ) : ℝ) / ((X + 1 : ℕ) : ℝ) ≤ 2 := by
    have hden : (0 : ℝ) < (X + 1 : ℕ) := by positivity
    rw [div_le_iff₀ hden]
    exact_mod_cast (by omega : X + Delta ≤ 2 * (X + 1))
  have hamp : (2 ^ base.length : ℕ) *
          ((e / 32) * ((X + Delta : ℕ) : ℝ) / ((X + 1 : ℕ) : ℝ)) + e / 4 ≤
        e / 2 := by
    have hmain : (2 ^ base.length : ℕ) *
        ((e / 32) * ((X + Delta : ℕ) : ℝ) /
          ((X + 1 : ℕ) : ℝ)) ≤ e / 4 := by
      have hbasepow : (2 ^ base.length : ℕ) = 4 := by
        dsimp only [base, List.length_cons, List.length_nil]
        norm_num
      rw [hbasepow]
      have hmul := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ e / 8)
      convert hmul using 1 <;> ring
    linarith
  have hamp0 : 0 ≤ (2 ^ base.length : ℕ) *
          ((e / 32) * ((X + Delta : ℕ) : ℝ) /
            ((X + 1 : ℕ) : ℝ)) + e / 4 := by
    positivity
  have hraw' :
      (2 * sliceA2LowCutoff eps *
          ((2 ^ base.length : ℕ) *
              ((e / 32) * ((X + Delta : ℕ) : ℝ) /
                ((X + 1 : ℕ) : ℝ)) +
            e / 4) ^ 2) ≤
        e ^ 4 / (2 * 10 ^ 12) := by
    have hsquare := pow_le_pow_left₀ hamp0 hamp 2
    unfold sliceA2LowCutoff
    dsimp only [e]
    calc
      _ ≤
        2 * (sliceA2EffectiveEps eps ^ 2 / 10 ^ 12) *
          (sliceA2EffectiveEps eps / 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquare (by positivity)
      _ = sliceA2EffectiveEps eps ^ 4 / (2 * 10 ^ 12) := by ring
  have hM0 := sliceA2Parts_bounds eps heps |>.1
  have hmass := sliceA2_floor_harmonic_lower A X (sliceA2Parts eps)
    hM0 hMA hAX hX2A
  have hMupper := sliceA2Parts_le eps heps
  have hcross : e ^ 2 * (sliceA2Parts eps : ℝ) ≤ 4097 := by
    calc
      e ^ 2 * (sliceA2Parts eps : ℝ) ≤
          e ^ 2 * (4097 / e ^ 2) :=
        mul_le_mul_of_nonneg_left (by simpa [e] using hMupper) (sq_nonneg e)
      _ = 4097 := by field_simp
  have hrecip : e ^ 2 / (5 * 4097) ≤
      (1 : ℝ) / (5 * sliceA2Parts eps) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 5 * 4097)
      (by positivity : (0 : ℝ) < 5 * sliceA2Parts eps)).2
    nlinarith
  have hmass' : e ^ 2 / (5 * 4097) ≤
      ∑ n ∈ Finset.Ioc X (X + A / sliceA2Parts eps), (1 : ℝ) / n :=
    hrecip.trans hmass
  have hnumeric : e ^ 4 / (2 * 10 ^ 12) ≤
      e ^ 2 * (e ^ 2 / (5 * 4097)) / 12288 := by
    have he4 : 0 ≤ e ^ 4 := by positivity
    norm_num at ⊢
    nlinarith
  have htarget : e ^ 4 / (2 * 10 ^ 12) ≤
      e ^ 2 *
        (∑ n ∈ Finset.Ioc X (X + A / sliceA2Parts eps), (1 : ℝ) / n) /
          12288 := by
    calc
      _ ≤ e ^ 2 * (e ^ 2 / (5 * 4097)) / 12288 := hnumeric
      _ ≤ _ := by gcongr
  have hperm := innerBandLevels_perm_lowBand Pl Pu J hJ
  apply integral_norm_typicalS_sq_le_of_perm g X (X + Delta)
    (innerBandLevels Pl Pu J) (base ++ ladder) hperm
    (sliceA2LowCutoff eps)
    (e ^ 2 * (∑ n ∈ Finset.Ioc X (X + A / sliceA2Parts eps),
      (1 : ℝ) / n) / 12288)
  exact hraw.trans (hraw'.trans htarget)

end Tao2015

end MoltResearch
