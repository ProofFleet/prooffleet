import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2WindowClose

/-!
# Track R A2-V': one fixed bottom threshold

Every scale-independent hypothesis of the ordinary schedule is absorbed into
one lower bound for `P0`.  The only remaining inputs are the two genuine
height ratios: the bottom frequency fit and the first positive-level moment
guard.
-/

namespace MoltResearch

namespace Tao2015

/-- Fixed bottom data returned by the common `P0` threshold. -/
def SliceA2OrdinaryBottomClosed
    (P0 ratio0 eta Qlog0 : ℕ) (eps rho0 : ℝ) : Prop :=
  Real.log 6 + 256 ≤ Real.log (P0 : ℝ) ∧
  40960 * (2 * Real.log (sliceA2OrdinaryFarCoefficient ratio0 eta) + 11) ≤
    Real.log (P0 : ℝ) ∧
  Qlog0 ≤ P0 ∧
  sliceA2OrdinaryCloseCoefficient ratio0 eta eps rho0 ^ 20 *
      (2 : ℝ) ^ 720 ≤ P0 ∧
  (160 * 2048 : ℝ) * Real.exp Real.pi ≤
    3 * eps ^ 2 * rho0 * P0

/-- One explicit integral threshold supplies all fixed ordinary-bottom
margins and the eventual logarithmic comparison. -/
theorem exists_sliceA2Ordinary_bottom_closed
    (ratio0 eta : ℕ) (eps rho0 : ℝ)
    (heps : 0 < eps) (hrho0 : 0 < rho0) :
    ∃ Pmin Qlog0 : ℕ,
      21 ≤ Pmin ∧ 3 ≤ Qlog0 ∧
      (∀ Q : ℕ, Qlog0 ≤ Q →
        Real.log (Q : ℝ) ^ 6 ≤ (Q : ℝ) ^ (1 / 20 : ℝ)) ∧
      ∀ P0 : ℕ, Pmin ≤ P0 →
        SliceA2OrdinaryBottomClosed P0 ratio0 eta Qlog0 eps rho0 ∧
        ∀ A : ℕ, ∀ T : ℝ, 1 ≤ A → 0 ≤ T →
          (T / (A : ℝ)) *
              sliceA2OrdinaryZeroFrequencyCoefficient
                P0 ratio0 eta eps rho0 ≤
            sliceA2KappaMain 0 / 2 * (eps ^ 2 * rho0 / 8) →
          SliceA2OrdinaryZeroFits P0 ratio0 eta A eps rho0 T := by
  obtain ⟨Pprime, hPprime, hprime⟩ :=
    exists_sliceA2Ordinary_zero_fits ratio0 eps rho0 heps hrho0
  obtain ⟨Qlog0, hQlog0, hlogFit⟩ := exists_log_six_le_twentieth_rpow
  let Lfar : ℝ :=
    40960 * (2 * Real.log (sliceA2OrdinaryFarCoefficient ratio0 eta) + 11)
  let Cclose : ℝ :=
    sliceA2OrdinaryCloseCoefficient ratio0 eta eps rho0 ^ 20 *
      (2 : ℝ) ^ 720
  let Ccollision : ℝ :=
    (160 * 2048 : ℝ) * Real.exp Real.pi / (3 * eps ^ 2 * rho0)
  let Pmin := max 21 (max Pprime (max Qlog0
    (max (⌈Real.exp (Real.log 6 + 256)⌉₊ + 1)
      (max (⌈Real.exp Lfar⌉₊ + 1)
        (max (⌈Cclose⌉₊ + 1) (⌈Ccollision⌉₊ + 1))))))
  refine ⟨Pmin, Qlog0, le_max_left _ _, hQlog0, hlogFit,
    fun P0 hP0 ↦ ?_⟩
  have hPprime0 : Pprime ≤ P0 :=
    (le_max_left Pprime (max Qlog0
      (max (⌈Real.exp (Real.log 6 + 256)⌉₊ + 1)
        (max (⌈Real.exp Lfar⌉₊ + 1)
          (max (⌈Cclose⌉₊ + 1) (⌈Ccollision⌉₊ + 1)))))).trans
      ((le_max_right 21 _).trans hP0)
  have hQlog : Qlog0 ≤ P0 :=
    (le_max_left Qlog0
      (max (⌈Real.exp (Real.log 6 + 256)⌉₊ + 1)
        (max (⌈Real.exp Lfar⌉₊ + 1)
          (max (⌈Cclose⌉₊ + 1) (⌈Ccollision⌉₊ + 1))))).trans
      ((le_max_right Pprime _).trans ((le_max_right 21 _).trans hP0))
  have hlogBase : ⌈Real.exp (Real.log 6 + 256)⌉₊ + 1 ≤ P0 :=
    (le_max_left _ _).trans
      ((le_max_right Qlog0 _).trans ((le_max_right Pprime _).trans
        ((le_max_right 21 _).trans hP0)))
  have hfarBase : ⌈Real.exp Lfar⌉₊ + 1 ≤ P0 :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right Qlog0 _).trans ((le_max_right Pprime _).trans
        ((le_max_right 21 _).trans hP0))))
  have hcloseBase : ⌈Cclose⌉₊ + 1 ≤ P0 :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right Qlog0 _).trans
        ((le_max_right Pprime _).trans ((le_max_right 21 _).trans hP0)))))
  have hcollisionBase : ⌈Ccollision⌉₊ + 1 ≤ P0 :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right Qlog0 _).trans
        ((le_max_right Pprime _).trans ((le_max_right 21 _).trans hP0)))))
  have hP0pos : (0 : ℝ) < P0 := by
    exact_mod_cast (show 0 < P0 by have := (le_max_left 21 _).trans hP0; omega)
  have hlog : Real.log 6 + 256 ≤ Real.log (P0 : ℝ) := by
    have hexp : Real.exp (Real.log 6 + 256) ≤ (P0 : ℝ) := by
      calc
        _ ≤ (⌈Real.exp (Real.log 6 + 256)⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (P0 : ℝ) := by exact_mod_cast
          (Nat.le_succ _ |>.trans hlogBase)
    calc
      Real.log 6 + 256 = Real.log (Real.exp (Real.log 6 + 256)) :=
        (Real.log_exp _).symm
      _ ≤ Real.log (P0 : ℝ) := Real.log_le_log (Real.exp_pos _) hexp
  have hfar : Lfar ≤ Real.log (P0 : ℝ) := by
    have hexp : Real.exp Lfar ≤ (P0 : ℝ) := by
      calc
        _ ≤ (⌈Real.exp Lfar⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (P0 : ℝ) := by exact_mod_cast
          (Nat.le_succ _ |>.trans hfarBase)
    calc
      Lfar = Real.log (Real.exp Lfar) := (Real.log_exp _).symm
      _ ≤ Real.log (P0 : ℝ) := Real.log_le_log (Real.exp_pos _) hexp
  have hclose : Cclose ≤ (P0 : ℝ) := by
    exact (Nat.le_ceil Cclose).trans (by exact_mod_cast
      (Nat.le_succ _ |>.trans hcloseBase))
  have hcollision : (160 * 2048 : ℝ) * Real.exp Real.pi ≤
      3 * eps ^ 2 * rho0 * P0 := by
    have hC : Ccollision ≤ (P0 : ℝ) :=
      (Nat.le_ceil Ccollision).trans (by exact_mod_cast
        (Nat.le_succ _ |>.trans hcollisionBase))
    have hden : 0 < 3 * eps ^ 2 * rho0 := by positivity
    dsimp [Ccollision] at hC
    have := (div_le_iff₀ hden).mp hC
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  refine ⟨⟨hlog, by simpa [Lfar] using hfar, hQlog,
    by simpa [Cclose] using hclose, hcollision⟩, ?_⟩
  intro A T hA hT hfrequency
  exact hprime P0 eta A T hPprime0 hA hT hfrequency

end Tao2015

end MoltResearch
