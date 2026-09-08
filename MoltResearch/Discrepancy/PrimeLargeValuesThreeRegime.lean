import MoltResearch.Discrepancy.ThreeRegimeEnvelope

/-!
# Prime large values from height-indexed zero-free data

This leaf combines the balanced Mellin height with the three-regime
real-variable envelope.  The short-polynomial and bounded transition ranges
are handled before the Mellin argument; the remaining range uses the kernel
bound at `zeroFreeRegionHeightHMax`.
-/

namespace MoltResearch

open Complex ExpSums Finset
open scoped ContDiff

set_option maxHeartbeats 1600000

/-- **V-B″-2.** Height-indexed zero-free data with `theta < theta'` and a
regular-part loss of order at most `log²` implies the three-regime prime
large-values estimate at exponent `theta'`. -/
theorem prime_large_values_bound_of_zeroFreeRegionDataH'
    {theta theta' m : ℝ} (h : ZeroFreeRegionDataH theta m)
    (hgap : theta < theta') (htheta' : theta' ≤ 1) (hm : m ≤ 2) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : ℕ) (Y : Finset ℕ),
      (∀ p ∈ Y, p.Prime) →
      (∀ p ∈ Y, P ≤ p ∧ p ≤ 2 * P) →
      ∀ (a : ℕ → ℂ) (T : ℝ) (𝒯 : Finset ℝ),
      2 ≤ P → 1 ≤ T → (∀ t ∈ 𝒯, |t| ≤ T) →
      (∀ t ∈ 𝒯, ∀ u ∈ 𝒯, t ≠ u → 1 ≤ |t - u|) →
      ∑ t ∈ 𝒯, ‖∑ p ∈ Y, (a p / (p : ℂ)) *
          ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖ ^ 2 ≤
        C * (1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) *
          (∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2) *
          (P : ℝ) / Real.log P := by
  classical
  have htheta'0 : 0 < theta' := lt_trans h.theta_pos hgap
  obtain ⟨x₀, D, hx₀, hD, henvelope⟩ :=
    exists_balanced_long_error_envelope h hgap htheta' hm
  obtain ⟨Ctriv, hCtriv, htrivial⟩ :=
    exists_trivial_three_regime_bound theta' x₀ htheta'0 htheta' hx₀
  obtain ⟨S, Cw, hSs, hS01, hS0, hS1, hCw0, hCw1, hCw2⟩ :=
    ExpSums.exists_master_transition
  obtain ⟨K, hK, hkernel⟩ :=
    exists_primeMellin_kernel_bound_of_zeroFreeRegionDataHMax h
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  let F : ℝ := K * (Cw + 1) ^ 2 * D
  let Canalytic : ℝ := 16 + 1000000 * (Cw + 1) ^ 2 + F
  let C : ℝ := max Ctriv Canalytic
  have hF0 : 0 ≤ F := by dsimp only [F]; positivity
  have hCanalytic : 1 ≤ Canalytic := by
    dsimp only [Canalytic]
    nlinarith [sq_nonneg (Cw + 1), hF0]
  have hC : 1 ≤ C := le_trans hCtriv (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro P Y hYprime hYrange a T 𝒯 hP hT hrange hsep
  by_cases hlong : (Real.log (2 * T)) ^ theta' < Real.log P
  · by_cases hxlarge : x₀ ≤ Real.log P
    · let Z := zeroFreeRegionHeightHMax theta T P
      let eta := zeroFreeRegionEtaH theta h.eta0 Z
      let M := zeroFreeRegionRegularBoundH m h.M0 Z
      let c := 1 + 1 / Real.log (2 * P)
      let position : ℝ → ℝ := fun t => -2 * Real.pi * t
      let A : ℝ := 250000 * (Cw + 1) ^ 2 * P
      let Raw : ℝ := P ^ (1 - eta / 2) +
        P ^ c * Real.log (2 * P) / (Z - 4 * Real.pi * T) +
        P ^ c / Z ^ 2 + Real.sqrt P * Real.log (4 * P)
      let E : ℝ := K * (Cw + 1) ^ 2 * (M + 1) * Raw
      have hpositionRange : ∀ t ∈ 𝒯, |position t| ≤ 2 * Real.pi * T := by
        intro t ht
        have habscoeff : |(-2 * Real.pi : ℝ)| = 2 * Real.pi := by
          rw [abs_of_neg (by linarith [Real.pi_pos] : (-2 * Real.pi : ℝ) < 0)]
          ring
        dsimp only [position]
        rw [abs_mul, habscoeff]
        have := hrange t ht
        nlinarith [Real.pi_pos.le]
      have hpositionSep : ∀ t ∈ 𝒯, ∀ s ∈ 𝒯, t ≠ s →
          1 ≤ |position t - position s| := by
        intro t ht s hs hts
        have hgap' := hsep t ht s hs hts
        have hpi2 : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
        have habscoeff : |(-2 * Real.pi : ℝ)| = 2 * Real.pi := by
          rw [abs_of_neg (by linarith [Real.pi_pos] : (-2 * Real.pi : ℝ) < 0)]
          ring
        dsimp only [position]
        rw [show -2 * Real.pi * t - -2 * Real.pi * s =
          (-2 * Real.pi) * (t - s) by ring, abs_mul, habscoeff]
        nlinarith [abs_nonneg (t - s)]
      have hdiffUpper : ∀ t ∈ 𝒯, ∀ s ∈ 𝒯,
          |position t - position s| ≤ 4 * Real.pi * T := by
        intro t ht s hs
        calc
          |position t - position s| ≤ |position t| + |position s| := abs_sub _ _
          _ ≤ 4 * Real.pi * T := by
            have ht' := hpositionRange t ht
            have hs' := hpositionRange s hs
            linarith
      have hZ0 : 0 < Z := by
        dsimp only [Z, zeroFreeRegionHeightHMax]
        exact lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
      have hRaw0 : 0 ≤ Raw := by
        have hden : 0 < Z - 4 * Real.pi * T := by
          have hbase : 8 * Real.pi * T ≤ Z := by
            dsimp only [Z, zeroFreeRegionHeightHMax]
            exact le_max_left _ _
          nlinarith [Real.pi_pos]
        have hlog2P : 0 ≤ Real.log (2 * P) := Real.log_nonneg (by
          have hPR : (2 : ℝ) ≤ P := by exact_mod_cast hP
          linarith)
        have hlog4P : 0 ≤ Real.log (4 * P) := Real.log_nonneg (by
          have hPR : (2 : ℝ) ≤ P := by exact_mod_cast hP
          linarith)
        dsimp only [Raw]
        positivity
      have hM0 : 0 ≤ M := by
        dsimp only [M, zeroFreeRegionRegularBoundH]
        exact le_trans (by linarith [h.one_le_M0] : 0 ≤ h.M0) (le_max_left _ _)
      have hE0 : 0 ≤ E := by
        dsimp only [E]
        exact mul_nonneg
          (mul_nonneg (mul_nonneg hK0 (sq_nonneg _)) (by linarith)) hRaw0
      have hA0 : 0 ≤ A := by dsimp only [A]; positivity
      have hkernelDiff : ∀ t ∈ 𝒯, ∀ s ∈ 𝒯, t ≠ s →
          ‖∑ p ∈ (Finset.Ioc 0 ⌊4 * (P : ℝ)⌋₊).filter Nat.Prime,
              ((primeMellinWindow S P p * Real.log p : ℝ) : ℂ) *
                (p : ℂ) ^ (I * ((position t - position s : ℝ) : ℂ))‖ ≤
            A / |position t - position s| ^ 2 + E := by
        intro t ht s hs hts
        let u := position t - position s
        have hu1 := hpositionSep t ht s hs hts
        have hu4 := hdiffUpper t ht s hs
        have hk := hkernel S Cw P T u hSs hS01 hS0 hS1 hCw0 hCw1 hCw2
          (by exact_mod_cast hP) hT hu1 hu4
        have hrawMono :
            P ^ (1 - eta / 2) +
                  P ^ c * Real.log (2 * P) / (Z - |u|) +
                  P ^ c / Z ^ 2 + Real.sqrt P * Real.log (4 * P) ≤ Raw := by
          have hdenU : 0 < Z - |u| := by
            have hbase : 8 * Real.pi * T ≤ Z := by
              dsimp only [Z, zeroFreeRegionHeightHMax]
              exact le_max_left _ _
            nlinarith
          have hdenT : 0 < Z - 4 * Real.pi * T := by
            have hbase : 8 * Real.pi * T ≤ Z := by
              dsimp only [Z, zeroFreeRegionHeightHMax]
              exact le_max_left _ _
            nlinarith [Real.pi_pos]
          have hnum : 0 ≤ P ^ c * Real.log (2 * P) := by
            have : 0 ≤ Real.log (2 * P) := Real.log_nonneg (by
              have hPR : (2 : ℝ) ≤ P := by exact_mod_cast hP
              linarith)
            positivity
          dsimp only [Raw]
          gcongr
        have hfac : 0 ≤ K * (Cw + 1) ^ 2 * (M + 1) :=
          mul_nonneg (mul_nonneg hK0 (sq_nonneg _)) (by linarith)
        calc
          _ ≤ (250000 * (Cw + 1) ^ 2 * P) / |u| ^ 2 +
              K * (Cw + 1) ^ 2 * (M + 1) *
                (P ^ (1 - eta / 2) +
                  P ^ c * Real.log (2 * P) / (Z - |u|) +
                  P ^ c / Z ^ 2 + Real.sqrt P * Real.log (4 * P)) := by
            simpa only [u, c, Z, eta, M] using hk
          _ ≤ (250000 * (Cw + 1) ^ 2 * P) / |u| ^ 2 +
              K * (Cw + 1) ^ 2 * (M + 1) * Raw :=
            add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hrawMono hfac)
          _ = A / |position t - position s| ^ 2 + E := by
            dsimp only [A, E, u]
      have hlv := prime_large_values_of_mellin_kernel S P Y a 𝒯 position A E
        hS01 hS1 hP hYprime hYrange hA0 hE0 hpositionSep hkernelDiff
      have hphase : ∀ t ∈ 𝒯,
          (∑ p ∈ Y, (a p / (p : ℂ)) *
              ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)) =
            ∑ p ∈ Y, (a p / (p : ℂ)) *
              (p : ℂ) ^ (I * (position t : ℂ)) := by
        intro t ht
        apply Finset.sum_congr rfl
        intro p hp
        rw [fourierChar_neg_log_eq_primeMellin_phase p
          (hYprime p hp).ne_zero t]
      have hmass : (∑ p ∈ Y, ‖a p / (p : ℂ)‖ ^ 2) =
          ∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [norm_div, Complex.norm_natCast, div_pow]
      have hcard := card_le_two_mul_add_one_of_one_separated T 𝒯 (by linarith)
        hrange hsep
      have henv := henvelope P T (4 * Real.pi * T) (𝒯.card : ℝ)
        (by exact_mod_cast hP) hT
        (by
          rw [abs_of_nonneg (by positivity)]
          have hpi2 : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
          nlinarith)
        (by rw [abs_of_nonneg (by positivity)]) (by positivity) hcard
        (by simpa using hxlarge) (by simpa using hlong)
      have hEnvRaw : (𝒯.card : ℝ) * (M + 1) * Raw ≤
          D * P * (1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) := by
        simpa only [Z, eta, M, c, Raw, abs_of_nonneg (by positivity :
          (0 : ℝ) ≤ 4 * Real.pi * T)] using henv
      have hEbound : (𝒯.card : ℝ) * E ≤
          F * P * (1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) := by
        have hfac : 0 ≤ K * (Cw + 1) ^ 2 := by positivity
        dsimp only [E, F]
        calc
          (𝒯.card : ℝ) * (K * (Cw + 1) ^ 2 * (M + 1) * Raw) =
              K * (Cw + 1) ^ 2 * ((𝒯.card : ℝ) * (M + 1) * Raw) := by ring
          _ ≤ K * (Cw + 1) ^ 2 *
              (D * P * (1 + (𝒯.card : ℝ) *
                primeLargeValuesDecay theta' P T)) :=
            mul_le_mul_of_nonneg_left hEnvRaw hfac
          _ = (K * (Cw + 1) ^ 2 * D) * P *
              (1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) := by ring
      have hdecay0 : 0 ≤ primeLargeValuesDecay theta' P T := by
        dsimp only [primeLargeValuesDecay]
        positivity
      have hcoeff : 16 * (P : ℝ) + 4 * A + (𝒯.card : ℝ) * E ≤
          Canalytic * (1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) * P := by
        let Q : ℝ := 1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T
        have hQ1 : 1 ≤ Q := by
          dsimp only [Q]
          exact le_add_of_nonneg_right (mul_nonneg (by positivity) hdecay0)
        have hPR : 0 ≤ (P : ℝ) := by positivity
        have hbase : 16 * (P : ℝ) + 4 * A ≤
            (16 + 1000000 * (Cw + 1) ^ 2) * Q * P := by
          have hcoef0 : 0 ≤ 16 + 1000000 * (Cw + 1) ^ 2 := by positivity
          calc
            16 * (P : ℝ) + 4 * A =
                (16 + 1000000 * (Cw + 1) ^ 2) * P := by
              dsimp only [A]
              ring
            _ ≤ ((16 + 1000000 * (Cw + 1) ^ 2) * Q) * P :=
              mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hcoef0 hQ1) hPR
            _ = _ := by ring
        calc
          _ ≤ (16 + 1000000 * (Cw + 1) ^ 2) * Q * P + F * P * Q :=
            add_le_add hbase (by simpa only [Q, mul_assoc] using hEbound)
          _ = Canalytic * Q * P := by dsimp only [Canalytic]; ring
          _ = _ := rfl
      have hcoeffC : 16 * (P : ℝ) + 4 * A + (𝒯.card : ℝ) * E ≤
          C * (1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) * P := by
        have hCanC : Canalytic ≤ C := le_max_right _ _
        have hfactor0 : 0 ≤
            (1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) * P := by positivity
        have hmono : Canalytic *
              ((1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) * P) ≤
            C * ((1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) * P) :=
          mul_le_mul_of_nonneg_right hCanC hfactor0
        exact hcoeff.trans (by simpa only [mul_assoc] using hmono)
      have hleftEq :
          (∑ t ∈ 𝒯, ‖∑ p ∈ Y, (a p / (p : ℂ)) *
              ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖ ^ 2) =
            ∑ t ∈ 𝒯, ‖∑ p ∈ Y, (a p / (p : ℂ)) *
              (p : ℂ) ^ (I * (position t : ℂ))‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [hphase t ht]
      rw [hleftEq]
      calc
        _ ≤ (16 * (P : ℝ) + 4 * A + (𝒯.card : ℝ) * E) *
            (∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2) / Real.log P := by
          rw [← hmass]
          exact hlv
        _ ≤ (C * (1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) * P) *
            (∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2) / Real.log P := by
          have hmass0 : 0 ≤ ∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2 := by positivity
          have hlogP : 0 < Real.log P :=
            Real.log_pos (by exact_mod_cast (show 1 < P by omega))
          gcongr
        _ = C * (1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) *
              (∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2) * P / Real.log P := by ring
    · have ht := htrivial P Y a T 𝒯 hP (fun p hp => (hYrange p hp).2)
        hT hrange hsep (Or.inr ⟨lt_of_not_ge hxlarge, hlong⟩)
      have hCtC : Ctriv ≤ C := le_max_left _ _
      have hfac0 : 0 ≤ (1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) *
          (∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2) * P / Real.log P := by
        have hlog : 0 < Real.log P :=
          Real.log_pos (by exact_mod_cast (show 1 < P by omega))
        dsimp only [primeLargeValuesDecay]
        positivity
      have hmono : Ctriv *
            ((1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) *
              (∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2) * P / Real.log P) ≤
          C * ((1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) *
              (∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2) * P / Real.log P) :=
        mul_le_mul_of_nonneg_right hCtC hfac0
      exact ht.trans (by simpa only [div_eq_mul_inv, mul_assoc] using hmono)
  · have ht := htrivial P Y a T 𝒯 hP (fun p hp => (hYrange p hp).2)
      hT hrange hsep (Or.inl (le_of_not_gt hlong))
    have hCtC : Ctriv ≤ C := le_max_left _ _
    have hfac0 : 0 ≤ (1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) *
        (∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2) * P / Real.log P := by
      have hlog : 0 < Real.log P :=
        Real.log_pos (by exact_mod_cast (show 1 < P by omega))
      dsimp only [primeLargeValuesDecay]
      positivity
    have hmono : Ctriv *
          ((1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) *
            (∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2) * P / Real.log P) ≤
        C * ((1 + (𝒯.card : ℝ) * primeLargeValuesDecay theta' P T) *
            (∑ p ∈ Y, ‖a p‖ ^ 2 / (p : ℝ) ^ 2) * P / Real.log P) :=
      mul_le_mul_of_nonneg_right hCtC hfac0
    exact ht.trans (by simpa only [div_eq_mul_inv, mul_assoc] using hmono)

end MoltResearch
