import MoltResearch.Discrepancy.WindowAssembly

/-!
# An explicit polynomially controlled bump window

`ContDiffBump` is built from an abstractly chosen bump base.  Compactness
therefore gives a derivative bound on each fixed radius-ratio interval, but
does not quantify that bound as the outer and inner radii coalesce.  The A.2
window needs precisely that quantitative dependence.

This leaf uses the concrete smooth transition function twice, once at each
edge.  Its derivative is bounded by one absolute constant, so a transition
gap `gap` costs at most `2 B / gap`.  In particular a gap at least
`eps * rIn / 600` gives the polynomial bound used by the final schedule.
-/

namespace MoltResearch

open Real Set Filter
open scoped ContDiff

/-- A two-sided smooth bump with plateau `[c-rIn,c+rIn]` and support inside
`(c-rOut,c+rOut)`. -/
noncomputable def explicitBumpWindow
    (c rIn rOut u : ℝ) : ℝ :=
  Real.smoothTransition ((u - (c - rOut)) / (rOut - rIn)) *
    Real.smoothTransition (((c + rOut) - u) / (rOut - rIn))

/-- The derivative of `smoothTransition` is bounded by one absolute
constant.  The maximum is taken only on `[0,1]`; off that interval the
function is locally constant. -/
theorem exists_smoothTransition_deriv_bound :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ u : ℝ,
      |deriv Real.smoothTransition u| ≤ B := by
  have hsmooth : ContDiff ℝ ∞ Real.smoothTransition :=
    Real.smoothTransition.contDiff
  have hcont : Continuous (deriv Real.smoothTransition) :=
    hsmooth.continuous_deriv (by norm_num)
  obtain ⟨u0, hu0, hmax⟩ := IsCompact.exists_isMaxOn
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))
    ⟨0, by norm_num⟩ ((continuous_abs.comp hcont).continuousOn)
  let B := max 1 |deriv Real.smoothTransition u0|
  refine ⟨B, le_max_left _ _, fun u => ?_⟩
  by_cases hu : u ∈ Set.Icc (0 : ℝ) 1
  · exact (hmax hu).trans (le_max_right _ _)
  · rw [Set.mem_Icc, not_and_or] at hu
    rcases hu with hu | hu
    · have hzero : deriv Real.smoothTransition u = 0 := by
        have hev : Real.smoothTransition =ᶠ[nhds u] (fun _ => 0) := by
          filter_upwards [Iio_mem_nhds (lt_of_not_ge hu)] with v hv
          exact Real.smoothTransition.zero_of_nonpos hv.le
        rw [hev.deriv_eq]
        simp
      rw [hzero, abs_zero]
      exact (zero_le_one.trans (le_max_left _ _))
    · push_neg at hu
      have hzero : deriv Real.smoothTransition u = 0 := by
        have hev : Real.smoothTransition =ᶠ[nhds u] (fun _ => 1) := by
          filter_upwards [Ioi_mem_nhds hu] with v hv
          exact Real.smoothTransition.one_of_one_le hv.le
        rw [hev.deriv_eq]
        simp
      rw [hzero, abs_zero]
      exact (zero_le_one.trans (le_max_left _ _))

/-- Basic smoothness, range, plateau, and support facts for the explicit
two-sided bump. -/
theorem explicitBumpWindow_properties
    (c rIn rOut : ℝ) (_hIn : 0 < rIn) (hOut : rIn < rOut) :
    ContDiff ℝ ∞ (explicitBumpWindow c rIn rOut) ∧
      (∀ u, 0 ≤ explicitBumpWindow c rIn rOut u ∧
        explicitBumpWindow c rIn rOut u ≤ 1) ∧
      (∀ u, |u - c| ≤ rIn → explicitBumpWindow c rIn rOut u = 1) ∧
      (∀ u, explicitBumpWindow c rIn rOut u ≠ 0 →
        c - rOut < u ∧ u < c + rOut) := by
  have hgap : 0 < rOut - rIn := sub_pos.mpr hOut
  constructor
  · unfold explicitBumpWindow
    fun_prop
  constructor
  · intro u
    have hL0 := Real.smoothTransition.nonneg
      ((u - (c - rOut)) / (rOut - rIn))
    have hL1 := Real.smoothTransition.le_one
      ((u - (c - rOut)) / (rOut - rIn))
    have hR0 := Real.smoothTransition.nonneg
      (((c + rOut) - u) / (rOut - rIn))
    have hR1 := Real.smoothTransition.le_one
      (((c + rOut) - u) / (rOut - rIn))
    constructor
    · exact mul_nonneg hL0 hR0
    · exact mul_le_one₀ hL1 hR0 hR1
  constructor
  · intro u hu
    rw [abs_le] at hu
    have hleft : 1 ≤ (u - (c - rOut)) / (rOut - rIn) := by
      rw [le_div_iff₀ hgap]
      linarith
    have hright : 1 ≤ ((c + rOut) - u) / (rOut - rIn) := by
      rw [le_div_iff₀ hgap]
      linarith
    simp [explicitBumpWindow,
      Real.smoothTransition.one_of_one_le hleft,
      Real.smoothTransition.one_of_one_le hright]
  · intro u hu
    unfold explicitBumpWindow at hu
    have hmul := mul_ne_zero_iff.mp hu
    have hleft := Real.smoothTransition.zero_iff_nonpos.not.mp hmul.1
    have hright := Real.smoothTransition.zero_iff_nonpos.not.mp hmul.2
    constructor
    · have hleftpos : 0 < (u - (c - rOut)) / (rOut - rIn) :=
        lt_of_not_ge hleft
      rcases div_pos_iff.mp hleftpos with hpos | hneg
      · linarith [hpos.1]
      · linarith [hneg.2]
    · have hrightpos : 0 < ((c + rOut) - u) / (rOut - rIn) :=
        lt_of_not_ge hright
      rcases div_pos_iff.mp hrightpos with hpos | hneg
      · linarith [hpos.1]
      · linarith [hneg.2]

/-- Polynomial derivative control as the plateau and support radii
coalesce.  The factor `1200` is two transition edges times the reciprocal
of the allowed relative gap `eps/600`. -/
theorem exists_explicitBumpWindow_deriv_bound :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ eps c rIn rOut : ℝ, 0 < eps → 0 < rIn → rIn < rOut →
        eps * rIn / 600 ≤ rOut - rIn →
        ∀ u : ℝ,
          |deriv (explicitBumpWindow c rIn rOut) u| ≤
            1200 * B / (eps * rIn) := by
  obtain ⟨B, hB, hBd⟩ := exists_smoothTransition_deriv_bound
  refine ⟨B, hB, ?_⟩
  intro eps c rIn rOut heps hIn hOut hgapLower u
  let gap := rOut - rIn
  let left : ℝ → ℝ := fun x =>
    Real.smoothTransition ((x - (c - rOut)) / gap)
  let right : ℝ → ℝ := fun x =>
    Real.smoothTransition (((c + rOut) - x) / gap)
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hsmoothAll : ContDiff ℝ ∞ Real.smoothTransition :=
    Real.smoothTransition.contDiff
  have hsmooth (z : ℝ) : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition z) z :=
    (hsmoothAll.differentiable (by norm_num) z).hasDerivAt
  have hleft : HasDerivAt left
      (deriv Real.smoothTransition ((u - (c - rOut)) / gap) / gap) u := by
    have hinner := ((hasDerivAt_id u).sub_const (c - rOut)).div_const gap
    simpa [left, Function.comp_def] using
      (hsmooth ((u - (c - rOut)) / gap)).comp u hinner
  have hright : HasDerivAt right
      (deriv Real.smoothTransition (((c + rOut) - u) / gap) *
        (-(1 : ℝ) / gap)) u := by
    have hinner := ((hasDerivAt_const u (c + rOut)).sub (hasDerivAt_id u)).div_const gap
    simpa [right, Function.comp_def, div_eq_mul_inv] using
      (hsmooth (((c + rOut) - u) / gap)).comp u hinner
  have hprod := hleft.mul hright
  have hderiv : deriv (explicitBumpWindow c rIn rOut) u =
      (deriv Real.smoothTransition ((u - (c - rOut)) / gap) / gap) * right u +
        left u * (deriv Real.smoothTransition (((c + rOut) - u) / gap) *
          (-(1 : ℝ) / gap)) := by
    change deriv (left * right) u = _
    rw [hprod.deriv]
  have hleft0 : 0 ≤ left u := Real.smoothTransition.nonneg _
  have hleft1 : left u ≤ 1 := Real.smoothTransition.le_one _
  have hright0 : 0 ≤ right u := Real.smoothTransition.nonneg _
  have hright1 : right u ≤ 1 := Real.smoothTransition.le_one _
  have hterm1 :
      |(deriv Real.smoothTransition ((u - (c - rOut)) / gap) / gap) * right u|
        ≤ B / gap := by
    rw [abs_mul, abs_div, abs_of_pos hgap, abs_of_nonneg hright0]
    calc
      |deriv Real.smoothTransition ((u - (c - rOut)) / gap)| / gap * right u
          ≤ (B / gap) * 1 := by gcongr; exact hBd _
      _ = B / gap := mul_one _
  have hterm2 :
      |left u * (deriv Real.smoothTransition (((c + rOut) - u) / gap) *
          (-(1 : ℝ) / gap))| ≤ B / gap := by
    rw [abs_mul, abs_mul, abs_div, abs_neg, abs_one, abs_of_pos hgap,
      abs_of_nonneg hleft0]
    calc
      left u * (|deriv Real.smoothTransition (((c + rOut) - u) / gap)| *
          (1 / gap)) ≤ 1 * (B * (1 / gap)) := by gcongr; exact hBd _
      _ = B / gap := by ring
  have hraw : |deriv (explicitBumpWindow c rIn rOut) u| ≤ 2 * B / gap := by
    rw [hderiv]
    exact (abs_add_le _ _).trans <| (add_le_add hterm1 hterm2).trans_eq (by ring)
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hden : 0 < eps * rIn := mul_pos heps hIn
  calc
    |deriv (explicitBumpWindow c rIn rOut) u| ≤ 2 * B / gap := hraw
    _ ≤ 1200 * B / (eps * rIn) := by
      rw [div_le_div_iff₀ hgap hden]
      calc
        2 * B * (eps * rIn) = 1200 * B * (eps * rIn / 600) := by ring
        _ ≤ 1200 * B * gap :=
          mul_le_mul_of_nonneg_left (by simpa [gap] using hgapLower)
            (mul_nonneg (by norm_num) hB0)

end MoltResearch
