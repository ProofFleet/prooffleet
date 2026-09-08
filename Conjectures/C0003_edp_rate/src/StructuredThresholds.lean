import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5TCut
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5VKDischarge
import MoltResearch.Discrepancy.Repulsion

/-!
# Function-form thresholds for the finite structured branch

This file exposes the quantitative pieces used by the present formalization of Tao's
structured branch.  The Mertens and truncated Euler-product losses are named constants,
the `t`-cut's existential threshold is Skolemized into a function, and the final maximum
of all scale requirements is made explicit.

There is an important dependency correction.  Tao's paper proves the `t`-cut using a
Vinogradov--Korobov zero-free region.  In the formal tree,
`vinogradovKorobov_unconditional` instead proves the required twist-distance statement
from `ZetaBound.lean` and a character power trick.  Consequently the theorems below have
no zero-free-region assumption.  `Repulsion.lean` likewise states and proves that its
archimedean estimate needs no zero-free region.

The threshold selected from `tcut_of_vinogradovKorobov` is noncomputable because that
older theorem has an existential API.  It is nevertheless a function of exactly
`(Q, T, B, δ)` and its specification is proved below.  The outer structured scale is a
closed maximum of that function and the remaining elementary thresholds.  This is the
form needed by a finite consumer: it can state, and separately prove, that this one scale
fits below its available cutoff.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-! ## Audited analytic losses -/

/-- Additive loss in the elementary Mertens floor. -/
def structuredMertensError : ℝ := 1

/-- Additive loss in the finite-to-full Euler-product comparison. -/
def structuredEulerTruncationError : ℝ := 13

/-- Total additive loss in the zeta-pretense bound: `1 + 13`. -/
def structuredZetaPretenseError : ℝ := 14

/-- Additive loss in the public archimedean repulsion estimate. -/
def structuredRepulsionError : ℝ := 24

theorem structuredZetaPretenseError_eq :
    structuredZetaPretenseError =
      structuredMertensError + structuredEulerTruncationError := by
  norm_num [structuredZetaPretenseError, structuredMertensError,
    structuredEulerTruncationError]

/-- The Mertens floor with its loss exposed as a named constant. -/
theorem structured_mertens_floor {y : ℕ} (hy : 2 ≤ y) :
    Real.log (Real.log y) ≤
      (∑ p ∈ y.primesBelow, (1 : ℝ) / p) + structuredMertensError := by
  simpa only [structuredMertensError] using
    (log_log_le_sum_one_div_primesBelow (y := y) hy)

/-- The truncated Euler-product bridge with its finite truncation loss exposed. -/
theorem structured_euler_truncation {N : ℕ} (χ : DirichletCharacter ℂ N)
    {y : ℕ} (hy : 3 ≤ y) (t : ℝ) :
    ∑ p ∈ y.primesBelow, (χ p * (p : ℂ) ^ (Complex.I * t)).re / p
      ≤ Real.log ‖LSeries (fun n => χ n)
          (((1 + 1 / Real.log y : ℝ) : ℂ) - Complex.I * t)‖
        + structuredEulerTruncationError := by
  simpa only [structuredEulerTruncationError] using
    (sum_re_twist_div_le_log_norm_LSeries χ hy t)

/-- The public repulsion estimate with its additive loss exposed. -/
theorem structured_archimedean_repulsion (u : ℝ) (y : ℕ) (hy : 3 ≤ y)
    (hu : 6 ≤ |u|) :
    (∑ p ∈ y.primesBelow, (1 : ℝ) / p)
        - Real.log (Real.log (|u| + 2)) - structuredRepulsionError
      ≤ pretentiousDistSq (fun n => (n : ℂ) ^ (Complex.I * (u : ℂ)))
          (fun _ => 1) y := by
  simpa only [structuredRepulsionError] using
    (pretentiousDistSq_phase_one_ge u y hy hu)

/-! ## Function-form `t`-cut -/

/-- The terminal real scale selected by the proved `t`-cut.  Its only arguments are the
bounded-modulus, bounded-frequency, pretense, and scale-exponent parameters.

No `VinogradovKorobovAssumption` argument appears: importing
`TrackCStage5VKDischarge.lean` supplies its unconditional standard-axiom instance. -/
noncomputable def structuredTCutThreshold
    (Q T B : ℝ) (hQ : 1 ≤ Q) (hT : 1 ≤ T) (hB : 0 ≤ B)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) : ℝ :=
  Classical.choose
    (tcut_of_vinogradovKorobov Q T B hQ hT hB hδ0 hδ1)

/-- Specification of `structuredTCutThreshold`: at every later real scale, two
bounded character twists pretending to the same unimodular function have frequencies
closer than the truncation scale `X^δ`. -/
theorem structured_tcut_after_threshold
    (Q T B : ℝ) (hQ : 1 ≤ Q) (hT : 1 ≤ T) (hB : 0 ≤ B)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∀ X : ℝ, structuredTCutThreshold Q T B hQ hT hB δ hδ0 hδ1 ≤ X →
      ∀ g : ℕ → ℂ, Unimodular g →
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
        1 ≤ q → (q : ℝ) ≤ Q → |t| ≤ T * X →
        pretentiousDistSq g (charTwist q χ t) ⌊X ^ δ⌋₊ ≤ B →
      ∀ (q' : ℕ) (χ' : DirichletCharacter ℂ q') (t' : ℝ),
        1 ≤ q' → (q' : ℝ) ≤ Q → |t'| ≤ T * X →
        pretentiousDistSq g (charTwist q' χ' t') ⌊X ^ δ⌋₊ ≤ B →
        |t - t'| < X ^ δ :=
  Classical.choose_spec
    (tcut_of_vinogradovKorobov Q T B hQ hT hB hδ0 hδ1)

/-! ## Elementary thresholds and the terminal maximum -/

/-- A natural threshold after which `A ≤ log X`. -/
noncomputable def structuredLogThreshold (A : ℝ) : ℕ :=
  max 1 ⌈Real.exp A⌉₊

theorem structuredLogThreshold_spec (A : ℝ) {X : ℕ}
    (hX : structuredLogThreshold A ≤ X) : A ≤ Real.log X := by
  have hX1 : 1 ≤ X := le_trans (le_max_left _ _) hX
  have hXA : Real.exp A ≤ (X : ℝ) := by
    calc Real.exp A ≤ (⌈Real.exp A⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (X : ℝ) := by
        exact_mod_cast le_trans (le_max_right _ _) hX
  calc A = Real.log (Real.exp A) := (Real.log_exp A).symm
    _ ≤ Real.log X := Real.log_le_log (Real.exp_pos A) hXA

/-- A natural threshold after which `A ≤ X^δ`, for positive `δ`. -/
noncomputable def structuredRpowThreshold (A δ : ℝ) : ℕ :=
  ⌈(max A 1) ^ (1 / δ)⌉₊

theorem structuredRpowThreshold_spec (A : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {X : ℕ} (hX : structuredRpowThreshold A δ ≤ X) :
    A ≤ (X : ℝ) ^ δ := by
  have hB1 : (1 : ℝ) ≤ max A 1 := le_max_right _ _
  have hB0 : (0 : ℝ) ≤ max A 1 := by linarith
  have hXB : (max A 1) ^ (1 / δ) ≤ (X : ℝ) := by
    calc (max A 1) ^ (1 / δ)
          ≤ (⌈(max A 1) ^ (1 / δ)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (X : ℝ) := by exact_mod_cast hX
  have hrw : ((max A 1) ^ (1 / δ)) ^ δ = max A 1 := by
    rw [← Real.rpow_mul hB0, one_div_mul_cancel hδ.ne', Real.rpow_one]
  calc A ≤ max A 1 := le_max_left _ _
    _ = ((max A 1) ^ (1 / δ)) ^ δ := hrw.symm
    _ ≤ (X : ℝ) ^ δ :=
      Real.rpow_le_rpow (Real.rpow_nonneg hB0 _) hXB hδ.le

/-- All scale inequalities consumed by the current structured wrapper after its finite
character sweep.  `Xpair` is the largest per-character refutation threshold and `Xzero`
kills the junk modulus-zero pretender. -/
def StructuredScaleConditions
    (Xstart Xpair Xzero H : ℕ) (T δ twistThreshold : ℝ) (X : ℕ) : Prop :=
  Xstart ≤ X ∧
  Xpair ≤ X ∧
  Xzero ≤ X ∧
  3 ≤ X ∧
  1 ≤ Real.log X ∧
  4 * ((H : ℝ) + 1) ^ 2 ≤ Real.log X ∧
  72 * ((H : ℝ) + 1) ^ 3 * (T + 1) ≤ (X : ℝ) ^ δ ∧
  ((Xstart : ℝ) + 1) ≤ (X : ℝ) ^ δ ∧
  ((Xzero : ℝ) + 1) ≤ (X : ℝ) ^ δ ∧
  twistThreshold ≤ (X : ℝ)

/-- The single terminal natural scale used by the finite structured branch.  This is the
exact maximum appearing in the current qualitative wrapper, with the elementary
existential thresholds replaced by `structuredLogThreshold` and
`structuredRpowThreshold`. -/
noncomputable def structuredTerminalScale
    (Xstart Xpair Xzero H : ℕ) (T δ twistThreshold : ℝ) : ℕ :=
  max
    (max
      (max
        (max Xstart Xpair)
        (max Xzero (structuredLogThreshold 1)))
      (max
        (max (structuredLogThreshold (4 * ((H : ℝ) + 1) ^ 2))
          (structuredRpowThreshold
            (72 * ((H : ℝ) + 1) ^ 3 * (T + 1)) δ))
        (max (structuredRpowThreshold ((Xstart : ℝ) + 1) δ)
          (structuredRpowThreshold ((Xzero : ℝ) + 1) δ))))
    (max 3 ⌈twistThreshold⌉₊)

/-- Every scale at or beyond `structuredTerminalScale` satisfies all inequalities bundled
in `StructuredScaleConditions`. -/
theorem structuredTerminalScale_spec
    (Xstart Xpair Xzero H : ℕ) (T : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (twistThreshold : ℝ) {X : ℕ}
    (hX : structuredTerminalScale Xstart Xpair Xzero H T δ twistThreshold ≤ X) :
    StructuredScaleConditions Xstart Xpair Xzero H T δ twistThreshold X := by
  have hstart : Xstart ≤ X := by
    apply le_trans (le_max_left Xstart Xpair)
    apply le_trans (le_max_left _ _)
    apply le_trans (le_max_left _ _)
    exact le_trans (le_max_left _ _) hX
  have hpair : Xpair ≤ X := by
    apply le_trans (le_max_right Xstart Xpair)
    apply le_trans (le_max_left _ _)
    apply le_trans (le_max_left _ _)
    exact le_trans (le_max_left _ _) hX
  have hzero : Xzero ≤ X := by
    apply le_trans (le_max_left Xzero (structuredLogThreshold 1))
    apply le_trans (le_max_right (max Xstart Xpair) _)
    apply le_trans (le_max_left _ _)
    exact le_trans (le_max_left _ _) hX
  have hlogOneThreshold : structuredLogThreshold 1 ≤ X := by
    apply le_trans (le_max_right Xzero (structuredLogThreshold 1))
    apply le_trans (le_max_right (max Xstart Xpair) _)
    apply le_trans (le_max_left _ _)
    exact le_trans (le_max_left _ _) hX
  have hlogHThreshold :
      structuredLogThreshold (4 * ((H : ℝ) + 1) ^ 2) ≤ X := by
    apply le_trans (le_max_left _ _)
    apply le_trans (le_max_left _ _)
    apply le_trans (le_max_right _ _)
    exact le_trans (le_max_left _ _) hX
  have hrpowTransferThreshold :
      structuredRpowThreshold (72 * ((H : ℝ) + 1) ^ 3 * (T + 1)) δ ≤ X := by
    apply le_trans (le_max_right _ _)
    apply le_trans (le_max_left _ _)
    apply le_trans (le_max_right _ _)
    exact le_trans (le_max_left _ _) hX
  have hrpowStartThreshold :
      structuredRpowThreshold ((Xstart : ℝ) + 1) δ ≤ X := by
    apply le_trans (le_max_left _ _)
    apply le_trans (le_max_right _ _)
    apply le_trans (le_max_right _ _)
    exact le_trans (le_max_left _ _) hX
  have hrpowZeroThreshold :
      structuredRpowThreshold ((Xzero : ℝ) + 1) δ ≤ X := by
    apply le_trans (le_max_right _ _)
    apply le_trans (le_max_right _ _)
    apply le_trans (le_max_right _ _)
    exact le_trans (le_max_left _ _) hX
  have hthree : 3 ≤ X := by
    exact le_trans (le_max_left 3 ⌈twistThreshold⌉₊)
      (le_trans (le_max_right _ _) hX)
  have htwistNat : ⌈twistThreshold⌉₊ ≤ X := by
    exact le_trans (le_max_right 3 ⌈twistThreshold⌉₊)
      (le_trans (le_max_right _ _) hX)
  refine ⟨hstart, hpair, hzero, hthree,
    structuredLogThreshold_spec 1 hlogOneThreshold,
    structuredLogThreshold_spec _ hlogHThreshold,
    structuredRpowThreshold_spec _ hδ hrpowTransferThreshold,
    structuredRpowThreshold_spec _ hδ hrpowStartThreshold,
    structuredRpowThreshold_spec _ hδ hrpowZeroThreshold, ?_⟩
  calc twistThreshold ≤ (⌈twistThreshold⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (X : ℝ) := by exact_mod_cast htwistNat

/-- Convenience specialization: insert the proved function-form `t`-cut threshold directly
into the terminal maximum. -/
noncomputable def structuredTerminalScaleOfTCut
    (Qcut Tcut B : ℝ) (hQ : 1 ≤ Qcut) (hT : 1 ≤ Tcut) (hB : 0 ≤ B)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (Xstart Xpair Xzero H : ℕ) (Twindow : ℝ) : ℕ :=
  structuredTerminalScale Xstart Xpair Xzero H Twindow δ
    (structuredTCutThreshold Qcut Tcut B hQ hT hB δ hδ0 hδ1)

/-- The terminal scale with its `t`-cut witness inserted satisfies the complete scale
package.  `Tcut` and `Twindow` are separate because the current wrapper applies the `t`-cut
with frequency bound `2 * Twindow`. -/
theorem structuredTerminalScaleOfTCut_spec
    (Qcut Tcut B : ℝ) (hQ : 1 ≤ Qcut) (hT : 1 ≤ Tcut) (hB : 0 ≤ B)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (Xstart Xpair Xzero H : ℕ) (Twindow : ℝ) {X : ℕ}
    (hX : structuredTerminalScaleOfTCut Qcut Tcut B hQ hT hB δ hδ0 hδ1
      Xstart Xpair Xzero H Twindow ≤ X) :
    StructuredScaleConditions Xstart Xpair Xzero H Twindow δ
      (structuredTCutThreshold Qcut Tcut B hQ hT hB δ hδ0 hδ1) X := by
  exact structuredTerminalScale_spec Xstart Xpair Xzero H Twindow hδ0 _ hX

end Tao2015

end MoltResearch
