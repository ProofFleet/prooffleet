import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2LevelData

/-!
# Track R A2-V'-10: short-budget cell resolutions

The relative budget floor is `rho0`, so the cell resolution must include its
reciprocal.  The exact constant `9216 = 16*64*9` assigns half of the wide
replacement allowance to reciprocal-prime mass; the remaining half is left
for the finite-cardinality term.
-/

namespace MoltResearch

namespace Tao2015

/-- All three ordinary legs use the conservative L3 share. -/
noncomputable def sliceA2KappaMain (j : ℕ) : ℝ := ordinaryLegShare j

noncomputable def sliceA2KappaReplacement (j : ℕ) : ℝ := ordinaryLegShare j

noncomputable def sliceA2KappaCollision (j : ℕ) : ℝ := ordinaryLegShare j

theorem sliceA2Kappa_nonneg (j : ℕ) :
    0 ≤ sliceA2KappaMain j ∧ 0 ≤ sliceA2KappaReplacement j ∧
      0 ≤ sliceA2KappaCollision j := by
  unfold sliceA2KappaMain sliceA2KappaReplacement sliceA2KappaCollision
    ordinaryLegShare
  constructor
  · positivity
  constructor <;> positivity

theorem sliceA2Kappa_share_fit (j : ℕ) :
    2 * sliceA2KappaMain j + 2 * sliceA2KappaReplacement j +
        2 * sliceA2KappaCollision j ≤ (1 : ℝ) / 2 ^ (j + 2) := by
  exact ordinaryLegShares_fit_shifted j

/-- Cell resolution adapted to a relative budget floor `rho0`. -/
noncomputable def sliceA2LevelN
    (E kappa c3 eps rho0 : ℝ) : ℕ :=
  max 2 ⌈9216 * Real.exp Real.pi * E /
    (kappa * c3 * eps ^ 2 * rho0)⌉₊

theorem sliceA2LevelN_two_le (E kappa c3 eps rho0 : ℝ) :
    2 ≤ sliceA2LevelN E kappa c3 eps rho0 := by
  unfold sliceA2LevelN
  exact le_max_left _ _

/-- The chosen resolution pays the mass half of the wide replacement fit. -/
theorem sliceA2LevelN_replacement_mass_fit
    (E kappa c3 eps rho0 : ℝ) (hE : 0 ≤ E) (hkappa : 0 < kappa)
    (hc3 : 0 < c3) (heps : 0 < eps) (hrho0 : 0 < rho0) :
    64 * 9 * Real.exp Real.pi *
        (E / (sliceA2LevelN E kappa c3 eps rho0 : ℝ)) ≤
      kappa * c3 * eps ^ 2 * rho0 / 16 := by
  let budget : ℝ := kappa * c3 * eps ^ 2 * rho0
  let C : ℝ := 9216 * Real.exp Real.pi
  have hbudget : 0 < budget := by dsimp [budget]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hratio0 : 0 ≤ C * E / budget := by positivity
  have hceil : C * E / budget ≤ (⌈C * E / budget⌉₊ : ℕ) :=
    Nat.le_ceil _
  have hNlower : C * E / budget ≤
      (sliceA2LevelN E kappa c3 eps rho0 : ℝ) := by
    refine hceil.trans ?_
    exact_mod_cast (le_max_right 2 ⌈C * E / budget⌉₊)
  have hcross : C * E ≤
      budget * (sliceA2LevelN E kappa c3 eps rho0 : ℝ) := by
    calc
      C * E = budget * (C * E / budget) := by field_simp
      _ ≤ budget * (sliceA2LevelN E kappa c3 eps rho0 : ℝ) :=
        mul_le_mul_of_nonneg_left hNlower hbudget.le
  have hN0 : (0 : ℝ) < sliceA2LevelN E kappa c3 eps rho0 := by
    exact_mod_cast (show 0 < sliceA2LevelN E kappa c3 eps rho0 by
      have := sliceA2LevelN_two_le E kappa c3 eps rho0
      omega)
  have hdiv : C * E / (sliceA2LevelN E kappa c3 eps rho0 : ℝ) ≤
      budget := (div_le_iff₀ hN0).2 hcross
  dsimp [C, budget] at hdiv ⊢
  calc
    64 * 9 * Real.exp Real.pi *
          (E / (sliceA2LevelN E kappa c3 eps rho0 : ℝ)) =
        (9216 * Real.exp Real.pi * E /
          (sliceA2LevelN E kappa c3 eps rho0 : ℝ)) / 16 := by ring
    _ ≤ (kappa * c3 * eps ^ 2 * rho0) / 16 :=
      div_le_div_of_nonneg_right hdiv (by norm_num)

/-- Adding a cardinality margin completes the ratio-aware wide replacement
fit. -/
theorem sliceA2_replacement_fit
    (A : ℕ) (P : Finset ℕ) (T E kappa c3 eps rho0 rho : ℝ)
    (hA : 2 ≤ A) (hTA : T ≤ A)
    (hmass : ∑ p ∈ P, (1 : ℝ) / p ≤ E)
    (hE : 0 ≤ E) (hkappa : 0 < kappa) (hc3 : 0 < c3)
    (heps : 0 < eps) (hrho0 : 0 < rho0) (hratio : rho0 ≤ rho)
    (hcard : 64 * 9 * Real.exp Real.pi * ((P.card : ℝ) / A) ≤
      kappa * c3 * eps ^ 2 * rho0 / 16) :
    2 * replacementEnergyBoundWide A P
        (sliceA2LevelN E kappa c3 eps rho0) T ≤
      kappa * bandBudget c3 eps rho := by
  apply replacementEnergyBoundWide_fit_of_mass_card_ratio
    A (sliceA2LevelN E kappa c3 eps rho0) P T E kappa c3 eps rho0 rho
    hA (by have := sliceA2LevelN_two_le E kappa c3 eps rho0; omega) hTA
    hmass
  · have hmassFit := sliceA2LevelN_replacement_mass_fit
      E kappa c3 eps rho0 hE hkappa hc3 heps hrho0
    linarith
  · exact hc3.le
  · exact hkappa.le
  · exact hratio

end Tao2015

end MoltResearch
