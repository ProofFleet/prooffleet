import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2OneSliceClose

/-!
# Track R A2-V': aggregate the closed local slices

The fixed-height ledger contains exactly the two bottom-scale inequalities
and four explicit-window inequalities.  Once it holds, the local theorem
applies to every complete floor slice and the partition lemma pays the final
incomplete slice.
-/

namespace MoltResearch

namespace Tao2015

open Finset ExpSums

/-- All data fixed at the short-interval height before the base scale is
chosen. -/
def SliceA2HeightClosed (epsc eps : ℝ) (H P0 : ℕ) : Prop :=
  ∃ Qlog0 : ℕ,
    21 ≤ P0 ∧
    100 ≤ sliceA2GeomEps eps * H ∧
    2000 ≤ sliceA2EffectiveEps eps * H ∧
    3072000 * (sliceA2Parts eps : ℝ) *
        explicitSliceWindowDerivBound (sliceA2GeomEps eps) ≤
      sliceA2EffectiveEps eps ^ 2 * H ∧
    4 * sliceA2OuterConstant *
        explicitSliceWindowDerivBound (sliceA2GeomEps eps) ≤
      sliceA2EffectiveEps eps * H ∧
    SliceA2OrdinaryBottomClosed P0 (exceptionalIntervalRatio epsc)
      (sliceA2ExceptionalLadderEta (sliceA2EffectiveEps eps) epsc
        (sliceA2EffectiveEps eps / 100)
        (1 / (4 * sliceA2Parts eps))) Qlog0
      (sliceA2EffectiveEps eps / 100)
      (1 / (4 * sliceA2Parts eps)) ∧
    (∀ Q : ℕ, Qlog0 ≤ Q →
      Real.log (Q : ℝ) ^ 6 ≤ (Q : ℝ) ^ (1 / 20 : ℝ)) ∧
    (∀ A : ℕ, ∀ T : ℝ, 1 ≤ A → 0 ≤ T →
      (T / (A : ℝ)) *
          sliceA2OrdinaryZeroFrequencyCoefficient P0
            (exceptionalIntervalRatio epsc)
            (sliceA2ExceptionalLadderEta (sliceA2EffectiveEps eps) epsc
              (sliceA2EffectiveEps eps / 100)
              (1 / (4 * sliceA2Parts eps)))
            (sliceA2EffectiveEps eps / 100)
            (1 / (4 * sliceA2Parts eps)) ≤
        sliceA2KappaMain 0 / 2 *
          ((sliceA2EffectiveEps eps / 100) ^ 2 *
            (1 / (4 * sliceA2Parts eps)) / 8) →
      SliceA2OrdinaryZeroFits P0 (exceptionalIntervalRatio epsc)
        (sliceA2ExceptionalLadderEta (sliceA2EffectiveEps eps) epsc
          (sliceA2EffectiveEps eps / 100)
          (1 / (4 * sliceA2Parts eps))) A
        (sliceA2EffectiveEps eps / 100)
        (1 / (4 * sliceA2Parts eps)) T) ∧
    1 ≤
      (sliceA2LadderP P0 (exceptionalIntervalRatio epsc)
        (sliceA2ExceptionalLadderEta (sliceA2EffectiveEps eps) epsc
          (sliceA2EffectiveEps eps / 100)
          (1 / (4 * sliceA2Parts eps))) 1 : ℝ) *
        (2 * sliceA2OuterConstant *
          explicitSliceWindowDerivBound (sliceA2GeomEps eps) /
            (sliceA2EffectiveEps eps * H)) ∧
    (sliceA2OuterConstant *
          explicitSliceWindowDerivBound (sliceA2GeomEps eps) /
            (sliceA2EffectiveEps eps * H)) *
        sliceA2OrdinaryZeroFrequencyCoefficient P0
          (exceptionalIntervalRatio epsc)
          (sliceA2ExceptionalLadderEta (sliceA2EffectiveEps eps) epsc
            (sliceA2EffectiveEps eps / 100)
            (1 / (4 * sliceA2Parts eps)))
          (sliceA2EffectiveEps eps / 100)
          (1 / (4 * sliceA2Parts eps)) ≤
      (sliceA2KappaMain 0 / 2 *
        ((sliceA2EffectiveEps eps / 100) ^ 2 *
          (1 / (4 * sliceA2Parts eps)) / 8)) / 2

set_option maxHeartbeats 5000000 in
/-- A closed fixed-height ledger gives the full dyadic-slice mean-square
clause for the canonical levels. -/
theorem exists_sliceA2_meanSquare_closed
    [HalaszLargeValuesAssumption] [PrimeLargeValuesAssumption]
    (epsc eps : ℝ) (H P0 : ℕ) (Amin : ℝ)
    (hepsc : 0 < epsc) (heps : 0 < eps)
    (hheight : SliceA2HeightClosed epsc eps H P0) :
    ∃ A0 : ℝ, 1 ≤ A0 ∧ Amin ≤ A0 ∧
      ∀ A1 : ℕ, A0 ≤ A1 →
        let levels := sliceA2FinalLevels P0 (exceptionalIntervalRatio epsc)
          (sliceA2ExceptionalLadderEta (sliceA2EffectiveEps eps) epsc
            (sliceA2EffectiveEps eps / 100)
            (1 / (4 * sliceA2Parts eps))) A1 epsc (by
              rcases hheight with ⟨_, hP0, _⟩
              omega)
        ∀ A : ℕ, A1 ≤ A → A ≤ A1 ^ 2 →
          ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g →
            (∀ n, ‖g n‖ ≤ 1) → g 1 = 1 →
            NonPretentiousAt g A0 (2 * A + 1) →
            ∀ J : ℕ, A / 2 ≤ J → J ≤ A →
              ∑ n ∈ Finset.Ioc A (A + J),
                  ‖∑ m ∈ (Finset.Ioc n (n + H)).filter
                    (HasFactorInAll levels), g m‖ ^ 2 / n ≤
                eps ^ 2 * (H : ℝ) ^ 2 *
                  ∑ n ∈ Finset.Ioc A (A + J), (1 : ℝ) / n := by
  rcases hheight with ⟨Qlog0, hP0, hgeom, hround, hlipschitz, houter,
    hbottom, hlogFit, hzeroClose, hfirst, hfrequency⟩
  obtain ⟨A0, hA0, hM0, hAmin, hlocal⟩ := exists_sliceA2_one_slice_closed
    epsc eps H P0 Qlog0 Amin hepsc heps hP0 hgeom hround hlipschitz houter
    hbottom hlogFit hzeroClose hfirst hfrequency
  refine ⟨A0, hA0, hAmin, fun A1 hA1 => ?_⟩
  let levels := sliceA2FinalLevels P0 (exceptionalIntervalRatio epsc)
    (sliceA2ExceptionalLadderEta (sliceA2EffectiveEps eps) epsc
      (sliceA2EffectiveEps eps / 100)
      (1 / (4 * sliceA2Parts eps))) A1 epsc (by omega)
  dsimp only
  intro A hA1A hAupper g hcm hg hg1 hNP J hJlo hJhi
  have hM := (sliceA2Parts_bounds eps heps).1
  have hMA : sliceA2Parts eps ≤ A := by
    have hM1R : (sliceA2Parts eps : ℝ) ≤ A1 := hM0.trans hA1
    have hM1 : sliceA2Parts eps ≤ A1 := by exact_mod_cast hM1R
    exact hM1.trans hA1A
  have hA : 2 ≤ A :=
    (by have := (sliceA2Parts_bounds eps heps).2.1; omega : 2 ≤ sliceA2Parts eps).trans hMA
  have hMfit := (sliceA2Parts_budget eps heps).1
  apply slice_meanSquare_le_of_small_slices levels g hg A J H
    (sliceA2Parts eps) eps hA hJlo hJhi hM hMA heps hMfit
  intro i hi
  let s := A / sliceA2Parts eps
  let X := A + i * s
  have hs : 0 < s := by
    dsimp [s]
    exact (Nat.one_le_div_iff hM).mpr hMA
  have hiK : i < J / s := by simpa [s] using Finset.mem_range.mp hi
  have hfull : (i + 1) * s ≤ J := by
    have hik : i + 1 ≤ J / s := by omega
    exact (Nat.mul_le_mul_right s hik).trans (Nat.div_mul_le_self J s)
  have hAX : A ≤ X := by dsimp [X]; omega
  have hX2A : X ≤ 2 * A := by
    have his : i * s ≤ (i + 1) * s :=
      Nat.mul_le_mul_right s (Nat.le_succ i)
    have : i * s ≤ J := his.trans hfull
    dsimp [X]
    omega
  have hslice := hlocal A1 hA1 A X hA1A hAupper hAX hX2A
    g hcm hg hg1 hNP
  have hepsSq : sliceA2EffectiveEps eps ^ 2 ≤ eps ^ 2 :=
    pow_le_pow_left₀ (sliceA2EffectiveEps_bounds eps heps).1.le
      (sliceA2EffectiveEps_bounds eps heps).2.2 2
  have hmass0 : 0 ≤
      (H : ℝ) ^ 2 *
        ∑ n ∈ Finset.Ioc X (X + A / sliceA2Parts eps), (1 : ℝ) / n := by
    positivity
  have htarget :
      (sliceA2EffectiveEps eps ^ 2 / 2) * (H : ℝ) ^ 2 *
          ∑ n ∈ Finset.Ioc X (X + A / sliceA2Parts eps), (1 : ℝ) / n ≤
        (eps ^ 2 / 2) * (H : ℝ) ^ 2 *
          ∑ n ∈ Finset.Ioc X (X + A / sliceA2Parts eps), (1 : ℝ) / n := by
    nlinarith
  have hbound := hslice.trans htarget
  have hend : X + A / sliceA2Parts eps =
      A + (i + 1) * (A / sliceA2Parts eps) := by
    have hmul : (i + 1) * (A / sliceA2Parts eps) =
        i * (A / sliceA2Parts eps) + A / sliceA2Parts eps := by
      rw [Nat.add_mul]
      simp
    dsimp [X, s]
    rw [hmul]
    exact Nat.add_assoc _ _ _
  rw [hend] at hbound
  simpa [levels, X, s] using hbound

end Tao2015

end MoltResearch
