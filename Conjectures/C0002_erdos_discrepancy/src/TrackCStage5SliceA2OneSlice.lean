import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2WindowSchedule

set_option maxHeartbeats 800000

/-!
# Track R A2-V': one explicit short slice

This is the final Fourier-bookkeeping interface for one full slice.  The
low-band input has its normalized allowance, and the inner-band input has
exactly the shifted-capstone budget.  Every other term is discharged by the
explicit window schedule.
-/

namespace MoltResearch

namespace Tao2015

open Real Finset MeasureTheory SchwartzMap ExpSums
open scoped FourierTransform ContDiff

/-- A floor slice has the relative-width bound required by the collar
allocation. -/
theorem sliceA2_floor_relative_width
    (A X H M : ℕ) (eps : ℝ) (hM : 0 < M) (hX : 0 < X) (hAX : A ≤ X)
    (hparts : 1000 ≤ sliceA2EffectiveEps eps * M) :
    (H : ℝ) * (A / M : ℕ) / X ≤
      sliceA2EffectiveEps eps * H / 1000 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hdiv : ((A / M : ℕ) : ℝ) / X ≤ (1 : ℝ) / M := by
    apply (div_le_div_iff₀ hXR hMR).2
    have hnat : (A / M) * M ≤ X := by
      rw [Nat.mul_comm]
      exact (Nat.mul_div_le A M).trans hAX
    have hnatR : ((A / M : ℕ) : ℝ) * M ≤ X := by exact_mod_cast hnat
    simpa using hnatR
  have hrecip : (1 : ℝ) / M ≤ sliceA2EffectiveEps eps / 1000 := by
    apply (div_le_div_iff₀ hMR (by norm_num : (0 : ℝ) < 1000)).2
    simpa [mul_comm] using hparts
  calc
    (H : ℝ) * (A / M : ℕ) / X =
        (H : ℝ) * (((A / M : ℕ) : ℝ) / X) := by ring
    _ ≤ (H : ℝ) * ((1 : ℝ) / M) := by gcongr
    _ ≤ (H : ℝ) * (sliceA2EffectiveEps eps / 1000) := by gcongr
    _ = sliceA2EffectiveEps eps * H / 1000 := by ring

/-- The concrete explicit-window schedule reduces a full short slice to its
low and inner analytic estimates. -/
theorem slice_meanSquare_typicalS_le_of_explicit_schedule
    (levels : List (Finset ℕ)) (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A X H : ℕ) (eps : ℝ) (heps : 0 < eps)
    (hMA : sliceA2Parts eps ≤ A) (hAX : A ≤ X) (hX2A : X ≤ 2 * A)
    (h3H : 3 * H ≤ A)
    (hgeomLarge : 100 ≤ sliceA2GeomEps eps * H)
    (hcollarSmall :
      2 * H + 4 * sliceA2Collar (sliceA2GeomEps eps) H ≤
        A / sliceA2Parts eps)
    (hround : 2000 ≤ sliceA2EffectiveEps eps * H)
    (hlipschitz :
      3072000 * (sliceA2Parts eps : ℝ) *
          explicitSliceWindowDerivBound (sliceA2GeomEps eps) ≤
        sliceA2EffectiveEps eps ^ 2 * H)
    (hconversion :
      32 * (H : ℝ) ^ 2 ≤
        sliceA2EffectiveEps eps ^ 2 * (X : ℝ) ^ 2)
    (hK2X : sliceA2OuterCutoff eps X H ≤ X)
    (hK2L : sliceA2OuterCutoff eps X H ≤ sliceA2TailCutoff X)
    (hKK2 : sliceA2LowCutoff eps ≤ sliceA2OuterCutoff eps X H)
    (htail :
      3840 * (sliceA2Parts eps : ℝ) *
          (A / sliceA2Parts eps + 2 * H +
            4 * sliceA2Collar (sliceA2GeomEps eps) H : ℕ) ^ 2 *
          (X : ℝ) *
          explicitSliceWindowDerivBound (sliceA2GeomEps eps) ^ 2 ≤
        sliceA2EffectiveEps eps ^ 2 * (H : ℝ) ^ 3 * Real.pi ^ 2 *
          sliceA2TailCutoff X ^ 2)
    (hlow :
      (∫ xi in {xi : ℝ | |xi| < sliceA2LowCutoff eps},
        ‖∑ m ∈ typicalS X
            (X + A / sliceA2Parts eps + 2 * H +
              4 * sliceA2Collar (sliceA2GeomEps eps) H) levels,
            (g m / (m : ℂ)) *
              ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
        ≤ sliceA2EffectiveEps eps ^ 2 *
          (∑ n ∈ Finset.Ioc X (X + A / sliceA2Parts eps),
            (1 : ℝ) / n) / 12288)
    (hinner : ∀ w : ℝ → ℝ, Measurable w → (∀ xi, 0 ≤ w xi) →
      (∀ xi, w xi ≤ (4 * (H : ℝ) / X) ^ 2) →
      (∫ xi in {xi : ℝ |
          sliceA2LowCutoff eps ≤ |xi| ∧
            |xi| ≤ sliceA2OuterCutoff eps X H},
        ‖∑ m ∈ typicalS X
            (X + A / sliceA2Parts eps + 2 * H +
              4 * sliceA2Collar (sliceA2GeomEps eps) H) levels,
            (g m / (m : ℂ)) *
              ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2 *
          w xi) ≤
        (4 * (H : ℝ) / X) ^ 2 *
          bandBudget 1 (sliceA2EffectiveEps eps / 100)
            (((A / sliceA2Parts eps + 2 * H +
              4 * sliceA2Collar (sliceA2GeomEps eps) H : ℕ) : ℝ) / X)) :
    ∑ n ∈ Finset.Ioc X (X + A / sliceA2Parts eps),
        ‖∑ m ∈ (Finset.Ioc n (n + H)).filter (HasFactorInAll levels),
          g m‖ ^ 2 / n ≤
      (sliceA2EffectiveEps eps ^ 2 / 2) * (H : ℝ) ^ 2 *
        ∑ n ∈ Finset.Ioc X (X + A / sliceA2Parts eps),
          (1 : ℝ) / n := by
  let e := sliceA2EffectiveEps eps
  let eg := sliceA2GeomEps eps
  let M := sliceA2Parts eps
  let s := A / M
  let U := sliceA2Collar eg H
  let Delta := s + 2 * H + 4 * U
  let K := sliceA2LowCutoff eps
  let K2 := sliceA2OuterCutoff eps X H
  let L := sliceA2TailCutoff X
  let Jband := sliceA2FourierDepth eps X H
  obtain ⟨he, he1, heeps⟩ := sliceA2EffectiveEps_bounds eps heps
  obtain ⟨hM0, hM30, hpartsLower⟩ := sliceA2Parts_bounds eps heps
  obtain ⟨hparts16, hparts1000⟩ := sliceA2Parts_budget eps heps
  obtain ⟨heg, heg1⟩ := sliceA2GeomEps_bounds eps heps
  have hH : 0 < H := by
    by_contra! hz
    have hHzero : H = 0 := by omega
    rw [hHzero] at hgeomLarge
    norm_num at hgeomLarge
  obtain ⟨hU, hU100, hU50, h50U, h2U1⟩ :=
    sliceA2Collar_bounds eg H heg1 (by simpa [eg] using hgeomLarge)
  obtain ⟨hs, hsX, hs30, h3HX, hU', h2UH, hplat, hDeltaX, hrho⟩ :=
    sliceA2_floor_width_geometry A X H M U hM0 hM30
      (by simpa [M] using hMA) hAX hX2A h3H hU h50U h2U1
  have hX : 0 < X := by omega
  have hX1 : 1 ≤ X := hX
  have hDelta2s : Delta ≤ 2 * s := by
    have hcollarSmall' : 2 * H + 4 * U ≤ s := by
      simpa [U, eg, s, M] using hcollarSmall
    dsimp only [Delta]
    omega
  have henlarged : (Delta : ℝ) / X ≤
      4 * ∑ n ∈ Finset.Ioc X (X + s), (1 : ℝ) / n :=
    sliceA2_enlarged_ratio_le_four_harmonic X s Delta hX1 hsX hDelta2s
  have hmass : (1 : ℝ) / (5 * M) ≤
      ∑ n ∈ Finset.Ioc X (X + s), (1 : ℝ) / n :=
    sliceA2_floor_harmonic_lower A X M hM0
      (by simpa [M] using hMA) hAX hX2A
  have hrelative : (H : ℝ) * s / X ≤ e * H / 1000 := by
    exact sliceA2_floor_relative_width A X H M eps hM0 hX hAX
      (by simpa [e, M] using hparts1000)
  have hUsmall : (U : ℝ) ≤ e * H / 1000 := by
    have hraw : 50 * (U : ℝ) ≤ (e / 100) * H := by
      simpa [eg, sliceA2GeomEps, e] using! hU50
    have hnonneg : 0 ≤ e * H := by positivity
    nlinarith
  have hround' : (2 : ℝ) ≤ e * H / 1000 := by linarith
  have hcollar := sliceA2_collar_slot_fit X s U H e hX he hH
    hUsmall hrelative hround'
  have hlip := sliceA2_lipschitz_slot_fit X s H M e eg hX hH hM0
    hmass (by simpa [e, eg, M] using hlipschitz)
  have hconvert := sliceA2_conversion_slot_fit X s H e hX hsX
    (by simpa [e] using hconversion)
  have htail' := sliceA2_tail_slot_fit X s U H M e eg L hX hH hM0
    (sliceA2TailCutoff_pos X hX) hmass (by simpa [e, eg, M, s, U, Delta, L]
      using htail)
  have houter := sliceA2_outer_slot_fit X s U H e eg K2 hX1
    (sliceA2OuterCutoff_pos eps X H heps hX hH)
    (by simpa [K2] using hK2X) henlarged
    (by simpa [e, eg, K2] using sliceA2OuterCutoff_fit eps X H heps hX hH)
  let ElowNorm := e ^ 2 *
    (∑ n ∈ Finset.Ioc X (X + s), (1 : ℝ) / n) / 12288
  let EinnerNorm := (4 * (H : ℝ) / X) ^ 2 *
    bandBudget 1 (e / 100) ((Delta : ℝ) / X)
  have hElow0 : 0 ≤ ElowNorm := by dsimp [ElowNorm]; positivity
  have hEinner0 : 0 ≤ EinnerNorm := by
    dsimp [EinnerNorm]
    exact mul_nonneg (sq_nonneg _)
      (bandBudget_nonneg 1 (e / 100) ((Delta : ℝ) / X)
        (by norm_num) (by positivity))
  have hlowSlot := sliceA2_low_slot_fit X s H e ElowNorm hX (by rfl)
  have hinnerSlot := sliceA2_inner_slot_fit X s Delta H 1 (e / 100) e
    EinnerNorm hX (by norm_num) henlarged (by rfl) (by
      have he2 : 0 ≤ e ^ 2 := sq_nonneg e
      nlinarith)
  have haccount := sliceA2ExplicitWindowCost_le_half_target
    X s U H e eg K2 L ElowNorm EinnerNorm hX1 hsX hH heg
    (sliceA2OuterCutoff_pos eps X H heps hX hH)
    (sliceA2TailCutoff_pos X hX) hElow0 hEinner0 hlowSlot hinnerSlot
    houter htail' hcollar hlip hconvert
  have hresult := slice_meanSquare_typicalS_le_of_explicit_normalized_bands
    levels g hg X s U H hX1 hs hsX hU' h2UH h3HX hplat hDeltaX hs30
    eg heg heg1 hU100 hU50 K K2 L
    (by simpa [K, K2] using hKK2)
    (sliceA2OuterCutoff_pos eps X H heps hX hH)
    (by simpa [K2, L] using hK2L) Jband
    (by simpa [Jband, K2, L] using sliceA2FourierDepth_fit eps X H heps hX hH)
    ElowNorm EinnerNorm
    (by simpa [K, ElowNorm, e, M, s, eg, U, Delta] using hlow)
    (by
      intro w hwm hw0 hwsup
      simpa [K, K2, EinnerNorm, e, M, s, eg, U, Delta] using
        hinner w hwm hw0 hwsup)
    ((e ^ 2 / 2) * (H : ℝ) ^ 2 *
      ∑ n ∈ Finset.Ioc X (X + s), (1 : ℝ) / n) haccount
  simpa [e, M, s] using hresult

end Tao2015

end MoltResearch
