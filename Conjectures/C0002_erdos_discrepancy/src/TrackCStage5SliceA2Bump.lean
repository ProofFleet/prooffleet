import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2Density
import MoltResearch.Discrepancy.BumpDeriv

/-!
# Track R A2-V'-7: uniform bump constants for the short slices

The window geometry places every bump-radius ratio in one compact interval.
This leaf packages that fact in precisely the form consumed by the normalized
slice assembly theorem.
-/

namespace MoltResearch

namespace Tao2015

open ExpSums

/-- Under the standard short-slice geometry there are uniform bump constants
with the convenient choice `B' = 3*C0`. -/
theorem exists_sliceA2_bump_constants
    (A s U H : ℕ) (epsGeom : ℝ)
    (hA : 1 ≤ A) (hH : 0 < H) (hs30 : 30 * s ≤ A) (h3H : 3 * H ≤ A)
    (heps0 : 0 < epsGeom) (heps1 : epsGeom ≤ 1)
    (hU100 : epsGeom * (H : ℝ) ≤ 100 * U)
    (hU50 : 50 * (U : ℝ) ≤ epsGeom * H) :
    ∃ C0 B' : ℝ, 0 ≤ B' ∧
      (∀ (c : ℝ) (f : ContDiffBump c),
        f.rIn = ((A : ℝ) / H) *
            (Real.log (1 + (H : ℝ) / ((A : ℝ) + s)) -
              Real.log (1 + (U : ℝ) / A)) / 2 →
        f.rOut - f.rIn = ((A : ℝ) / H) *
            (min (Real.log (1 + (U : ℝ) / A) -
                  Real.log (1 + (U : ℝ) / (4 * ((A : ℝ) + s))))
              (Real.log (1 + ((H : ℝ) + 2 * U) / A) -
                  Real.log (1 + (H : ℝ) / ((A : ℝ) + s)))) →
        ∀ u : ℝ, |deriv (⇑f) u| ≤ C0 / f.rIn) ∧
      C0 / (((A : ℝ) / H) *
          (Real.log (1 + (H : ℝ) / ((A : ℝ) + s)) -
            Real.log (1 + (U : ℝ) / A)) / 2) ≤ B' := by
  let rin : ℝ := ((A : ℝ) / H) *
    (Real.log (1 + (H : ℝ) / ((A : ℝ) + s)) -
      Real.log (1 + (U : ℝ) / A)) / 2
  let gap : ℝ := ((A : ℝ) / H) *
    (min (Real.log (1 + (U : ℝ) / A) -
          Real.log (1 + (U : ℝ) / (4 * ((A : ℝ) + s))))
      (Real.log (1 + ((H : ℝ) + 2 * U) / A) -
          Real.log (1 + (H : ℝ) / ((A : ℝ) + s))))
  have hrin : (1 : ℝ) / 3 ≤ rin := by
    simpa [rin] using slice_rIn_lower A s U H epsGeom hA hH hs30 h3H
      heps1 hU50
  have hrin0 : 0 < rin := lt_of_lt_of_le (by norm_num) hrin
  have hgapLower : (epsGeom / 600) * rin ≤ gap := by
    simpa [rin, gap] using slice_ratio_lower A s U H epsGeom hA hH hs30 h3H
      heps0.le heps1 hU100 hU50
  have hgapUpper : gap ≤ (epsGeom / 20) * rin := by
    simpa [rin, gap] using slice_ratio_upper A s U H epsGeom hA hH hs30 h3H
      heps0.le heps1 hU50
  have hR0 : 1 < 1 + epsGeom / 600 := by nlinarith
  have hR01 : 1 + epsGeom / 600 ≤ 1 + epsGeom / 20 := by
    nlinarith
  obtain ⟨C0, hC00, hderiv⟩ :=
    exists_bump_deriv_bound (1 + epsGeom / 600) (1 + epsGeom / 20)
      hR0 hR01
  refine ⟨C0, 3 * C0, by positivity, ?_, ?_⟩
  · intro c f hfin hfgap u
    have hfin0 : 0 < f.rIn := f.rIn_pos
    have hratioShape : f.rOut / f.rIn =
        1 + (f.rOut - f.rIn) / f.rIn := by
      field_simp
      ring
    apply hderiv c f
    · rw [hratioShape]
      have hgapF : (epsGeom / 600) * f.rIn ≤ f.rOut - f.rIn := by
        calc
          (epsGeom / 600) * f.rIn = (epsGeom / 600) * rin := by rw [hfin]
          _ ≤ gap := hgapLower
          _ = f.rOut - f.rIn := hfgap.symm
      have hdiv : epsGeom / 600 ≤ (f.rOut - f.rIn) / f.rIn :=
        (le_div_iff₀ hfin0).2 hgapF
      linarith
    · rw [hratioShape]
      have hgapF : f.rOut - f.rIn ≤ (epsGeom / 20) * f.rIn := by
        calc
          f.rOut - f.rIn = gap := hfgap
          _ ≤ (epsGeom / 20) * rin := hgapUpper
          _ = (epsGeom / 20) * f.rIn := by rw [hfin]
      have hdiv : (f.rOut - f.rIn) / f.rIn ≤ epsGeom / 20 :=
        (div_le_iff₀ hfin0).2 hgapF
      linarith
  · change C0 / rin ≤ 3 * C0
    apply (div_le_iff₀ hrin0).2
    nlinarith

end Tao2015

end MoltResearch
