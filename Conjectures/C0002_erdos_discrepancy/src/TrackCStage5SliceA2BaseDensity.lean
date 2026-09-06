import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2PrimeMassLower

/-!
# Track R A2-V'-21: Turan--Kubilius density for the two endpoint levels

Level zero and the exceptional interval are handled together by the window
Turan--Kubilius estimate.  Their reciprocal-prime masses each contribute at
most `epsc/4` of the dyadic harmonic mass; the finite-cardinality terms are
kept as one explicit error with a further `epsc/4` allocation.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The finite-cardinality part of one level in
`window_typicalS_complement_le`. -/
noncomputable def sliceA2TKFiniteError
    (A : ℕ) (P : Finset ℕ) : ℝ :=
  let E := ∑ p ∈ P, (1 : ℝ) / p
  (3 * (((P.card : ℝ) + (P.card : ℝ) ^ 2) / A) +
      2 * E * (3 * ((P.card : ℝ) / A))) / E ^ 2

/-- The exact TK summand splits into `H/E` and the finite error. -/
theorem sliceA2TK_summand_eq
    (A : ℕ) (P : Finset ℕ) (H : ℝ)
    (hE : 0 < ∑ p ∈ P, (1 : ℝ) / p) :
    ((∑ p ∈ P, (1 : ℝ) / p) * H +
        (3 * (((P.card : ℝ) + (P.card : ℝ) ^ 2) / A) +
          2 * (∑ p ∈ P, (1 : ℝ) / p) *
            (3 * ((P.card : ℝ) / A)))) /
        (∑ p ∈ P, (1 : ℝ) / p) ^ 2 =
      H / (∑ p ∈ P, (1 : ℝ) / p) +
        sliceA2TKFiniteError A P := by
  unfold sliceA2TKFiniteError
  dsimp only
  field_simp [ne_of_gt hE]

/-- The endpoint pair occupies at most three quarters of the density
budget once its finite TK errors occupy one quarter. -/
theorem typicalS_complement_bottom_exceptional_le
    (A : ℕ) (P0 Pu : Finset ℕ) (epsc : ℝ)
    (hA : 1 ≤ A) (hepsc : 0 < epsc)
    (hP0 : ∀ p ∈ P0, p.Prime) (hPu : ∀ p ∈ Pu, p.Prime)
    (hP0sq : ∀ p ∈ P0, ∀ q ∈ P0, p * q ≤ A)
    (hPusq : ∀ p ∈ Pu, ∀ q ∈ Pu, p * q ≤ A)
    (hmass0 : 4 / epsc ≤ ∑ p ∈ P0, (1 : ℝ) / p)
    (hmassU : 4 / epsc ≤ ∑ p ∈ Pu, (1 : ℝ) / p)
    (herror : sliceA2TKFiniteError A P0 +
        sliceA2TKFiniteError A Pu ≤
      (epsc / 4) * ∑ n ∈ Ioc A (2 * A), (1 : ℝ) / n) :
    ∑ n ∈ (Ioc A (2 * A)).filter
        (fun n ↦ ¬ HasFactorInAll [P0, Pu] n), (1 : ℝ) / n ≤
      (3 * epsc / 4) * ∑ n ∈ Ioc A (2 * A), (1 : ℝ) / n := by
  let H := ∑ n ∈ Ioc A (2 * A), (1 : ℝ) / n
  let E0 := ∑ p ∈ P0, (1 : ℝ) / p
  let EU := ∑ p ∈ Pu, (1 : ℝ) / p
  have hepsc0 : 0 ≤ epsc := hepsc.le
  have hE0 : 0 < E0 := lt_of_lt_of_le (by positivity) hmass0
  have hEU : 0 < EU := lt_of_lt_of_le (by positivity) hmassU
  have hH0 : 0 ≤ H := Finset.sum_nonneg fun n _ ↦ by positivity
  have hmain0 : H / E0 ≤ (epsc / 4) * H := by
    have hrecip : 1 / E0 ≤ epsc / 4 := by
      rw [div_le_iff₀ hE0]
      have hmass0' : 4 / epsc ≤ E0 := by simpa [E0] using hmass0
      calc
        1 = (epsc / 4) * (4 / epsc) := by field_simp
        _ ≤ (epsc / 4) * E0 :=
          mul_le_mul_of_nonneg_left hmass0' (by positivity)
    calc
      H / E0 = (1 / E0) * H := by ring
      _ ≤ (epsc / 4) * H := mul_le_mul_of_nonneg_right hrecip hH0
  have hmainU : H / EU ≤ (epsc / 4) * H := by
    have hrecip : 1 / EU ≤ epsc / 4 := by
      rw [div_le_iff₀ hEU]
      have hmassU' : 4 / epsc ≤ EU := by simpa [EU] using hmassU
      calc
        1 = (epsc / 4) * (4 / epsc) := by field_simp
        _ ≤ (epsc / 4) * EU :=
          mul_le_mul_of_nonneg_left hmassU' (by positivity)
    calc
      H / EU = (1 / EU) * H := by ring
      _ ≤ (epsc / 4) * H := mul_le_mul_of_nonneg_right hrecip hH0
  have hraw := window_typicalS_complement_le A (2 * A) [P0, Pu]
    (by
      intro P hP p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl
      · exact hP0 p hp
      · exact hPu p hp)
    (by
      intro P hP p hp q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl
      · exact hP0sq p hp q hq
      · exact hPusq p hp q hq)
    (by omega)
    (by
      intro P hP
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl
      · exact hE0
      · exact hEU)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero] at hraw
  rw [sliceA2TK_summand_eq A P0 H hE0,
    sliceA2TK_summand_eq A Pu H hEU] at hraw
  dsimp [H, E0, EU] at hraw hmain0 hmainU herror ⊢
  linarith

/-- Concrete specialization to the bottom and exceptional prime intervals. -/
theorem sliceA2_bottom_exceptional_density
    (P0 eta A1 A : ℕ) (epsc : ℝ) (hP0 : 3 ≤ P0)
    (hA : 1 ≤ A)
    (hP0sq : ∀ p ∈ sliceA2LadderPrimes P0
        (exceptionalIntervalRatio epsc) eta 0,
      ∀ q ∈ sliceA2LadderPrimes P0
        (exceptionalIntervalRatio epsc) eta 0, p * q ≤ A)
    (hPusq : ∀ p ∈ exceptionalPrimes A1 epsc,
      ∀ q ∈ exceptionalPrimes A1 epsc, p * q ≤ A)
    (herror : sliceA2TKFiniteError A
          (sliceA2LadderPrimes P0 (exceptionalIntervalRatio epsc) eta 0) +
        sliceA2TKFiniteError A (exceptionalPrimes A1 epsc) ≤
      (epsc / 4) * ∑ n ∈ Ioc A (2 * A), (1 : ℝ) / n)
    (hepsc : 0 < epsc) :
    ∑ n ∈ (Ioc A (2 * A)).filter
        (fun n ↦ ¬ HasFactorInAll
          [sliceA2LadderPrimes P0 (exceptionalIntervalRatio epsc) eta 0,
            exceptionalPrimes A1 epsc] n), (1 : ℝ) / n ≤
      (3 * epsc / 4) * ∑ n ∈ Ioc A (2 * A), (1 : ℝ) / n := by
  apply typicalS_complement_bottom_exceptional_le A
    (sliceA2LadderPrimes P0 (exceptionalIntervalRatio epsc) eta 0)
    (exceptionalPrimes A1 epsc) epsc hA hepsc
  · exact sliceA2LadderPrimes_prime P0
      (exceptionalIntervalRatio epsc) eta 0
  · exact exceptionalPrimes_prime A1 epsc
  · exact hP0sq
  · exact hPusq
  · exact sliceA2BottomPrimes_mass_ge_four_div P0 eta epsc hP0
  · exact exceptionalPrimes_mass_ge_four_div A1 epsc
  · exact herror

end Tao2015

end MoltResearch
