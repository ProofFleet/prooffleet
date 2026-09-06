import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2Partition

/-!
# Track R A2-V'-4: scale and level-order transport

Small-slice aggregation changes the left endpoint but not the original
non-pretentiousness hypothesis.  The scale-up lemma loses only a fixed factor
of strength.  The other transport in this file rotates the exceptional level
beside level zero for the low-band inclusion--exclusion, while retaining the
canonical `innerBandLevels` order everywhere else.
-/

namespace MoltResearch

namespace Tao2015

open Finset MeasureTheory ExpSums

/-- A top hypothesis at `2*A+1` supplies every local slice beginning between
`A` and `2*A`, at one third of the strength. -/
theorem nonPretentiousAt_slice_scale
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (A X : ℕ) (A0 : ℝ) (hA0 : 0 ≤ A0)
    (hAX : A ≤ X) (hX2A : X ≤ 2 * A)
    (hNP : NonPretentiousAt g A0 (2 * A + 1)) :
    NonPretentiousAt g (A0 / 3) (2 * X + 1) := by
  apply nonPretentiousAt_scale_up_of_norm_le_one (c := 3) hg hNP
  · omega
  · have h : 2 * X + 1 ≤ 3 * (2 * A + 1) := by omega
    exact_mod_cast h
  · positivity
  · norm_num
  · ring_nf
    exact le_rfl

/-- The same original hypothesis supplies the tripled top scale used by the
sharp Halasz window, at one ninth of the strength. -/
theorem nonPretentiousAt_slice_sharp_scale
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (A X : ℕ) (A0 : ℝ) (hA0 : 0 ≤ A0)
    (hAX : A ≤ X) (hX2A : X ≤ 2 * A)
    (hNP : NonPretentiousAt g A0 (2 * A + 1)) :
    NonPretentiousAt g (A0 / 9) (3 * (2 * X + 1)) := by
  apply nonPretentiousAt_scale_up_of_norm_le_one (c := 9) hg hNP
  · omega
  · have h : 3 * (2 * X + 1) ≤ 9 * (2 * A + 1) := by omega
    exact_mod_cast h
  · positivity
  · norm_num
  · ring_nf
    exact le_rfl

/-- Canonical level order is a permutation of the low-band order: level zero
and the exceptional level form the fixed base, followed by the growing
ordinary ladder. -/
theorem innerBandLevels_perm_lowBand
    (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ) (J : ℕ) (hJ : 0 < J) :
    (innerBandLevels Pl Pu J).Perm
      ([Pl 0, Pu] ++
        (List.range (J - 1)).map (fun i => Pl (i + 1))) := by
  let ladder := (List.range (J - 1)).map (fun i => Pl (i + 1))
  have hord : (List.range J).map Pl = Pl 0 :: ladder := by
    simpa [ladder] using map_range_eq_cons_shifted Pl J hJ
  rw [innerBandLevels, hord]
  change (Pl 0 :: ladder ++ [Pu]).Perm (Pl 0 :: Pu :: ladder)
  exact List.Perm.cons _ (List.perm_append_comm)

/-- Transfer a normalized low-band integral through a permutation of the
level list. -/
theorem integral_norm_typicalS_sq_le_of_perm
    (g : ℕ → ℂ) (a b : ℕ)
    (levels levels' : List (Finset ℕ)) (hperm : levels.Perm levels')
    (K E : ℝ)
    (hE : (∫ t in {t : ℝ | |t| < K},
      ‖∑ m ∈ typicalS a b levels', (g m / (m : ℂ)) *
        ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖ ^ 2) ≤ E) :
    (∫ t in {t : ℝ | |t| < K},
      ‖∑ m ∈ typicalS a b levels, (g m / (m : ℂ)) *
        ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖ ^ 2) ≤ E := by
  rw [typicalS_perm a b hperm]
  exact hE

end Tao2015

end MoltResearch
