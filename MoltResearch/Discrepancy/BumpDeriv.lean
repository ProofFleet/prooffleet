import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Discrepancy: a uniform derivative bound for bump functions (Track R, A2, W1e″)

Mathlib's `ContDiffBump` carries no derivative estimates.  But every
bump is the *same* base profile (`someContDiffBumpBase`) composed with
an affine map of the radii, and the base is jointly smooth in
`(R, x) ∈ (1,∞) × ℝ` — so over any compact ratio window
`R = rOut/rIn ∈ [R₀, R₁]` the base's `x`-derivative has a uniform sup,
and the chain rule prices every bump's derivative at `C₀/rIn`.  This
is the keystone that makes the slice windows' Lipschitz data explicit
across the A.2 window assembly.
-/

namespace MoltResearch

open Set Metric

/-- **The uniform bump derivative bound** (Track R, W1e″): over a
compact ratio window `[R₀, R₁] ⊂ (1, ∞)` there is one constant `C₀`
with `|deriv f| ≤ C₀/rIn` for every real bump in the window. -/
theorem exists_bump_deriv_bound (R₀ R₁ : ℝ) (hR₀ : 1 < R₀) (hR₁ : R₀ ≤ R₁) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (c : ℝ) (f : ContDiffBump c),
      R₀ ≤ f.rOut/f.rIn → f.rOut/f.rIn ≤ R₁ →
      ∀ u : ℝ, |deriv (⇑f) u| ≤ C₀/f.rIn := by
  classical
  set base := someContDiffBumpBase ℝ with hbase_def
  set g : ℝ × ℝ → ℝ := Function.uncurry base.toFun with hg_def
  have hU : IsOpen (Ioi (1:ℝ) ×ˢ (univ : Set ℝ)) :=
    isOpen_Ioi.prod isOpen_univ
  have hg_smooth : ContDiffOn ℝ (⊤:ℕ∞) g (Ioi (1:ℝ) ×ˢ univ) := by
    exact_mod_cast base.smooth
  have hfd_cont : ContinuousOn (fderiv ℝ g) (Ioi (1:ℝ) ×ˢ univ) :=
    hg_smooth.continuousOn_fderiv_of_isOpen hU (by exact_mod_cast le_top)
  set φ : ℝ × ℝ → ℝ := fun p => (fderiv ℝ g p) ((0:ℝ), (1:ℝ)) with hφ_def
  have hφ_cont : ContinuousOn φ (Ioi (1:ℝ) ×ˢ univ) :=
    hfd_cont.clm_apply continuousOn_const
  set K : Set (ℝ × ℝ) := Icc R₀ R₁ ×ˢ closedBall (0:ℝ) R₁ with hK_def
  have hKc : IsCompact K := (isCompact_Icc).prod (isCompact_closedBall _ _)
  have hKU : K ⊆ Ioi (1:ℝ) ×ˢ univ := by
    rintro ⟨R, x⟩ ⟨hR, -⟩
    exact ⟨lt_of_lt_of_le hR₀ hR.1, trivial⟩
  have hKne : K.Nonempty := by
    refine ⟨(R₀, 0), ⟨le_refl _, hR₁⟩, ?_⟩
    simp only [mem_closedBall, dist_zero_left, norm_zero]
    linarith
  obtain ⟨p₀, hp₀K, hmax⟩ := hKc.exists_isMaxOn hKne
    ((hφ_cont.mono hKU).norm)
  set C₀ : ℝ := ‖φ p₀‖ with hC₀_def
  refine ⟨C₀, norm_nonneg _, ?_⟩
  intro c f hfR₀ hfR₁ u
  have hrIn := f.rIn_pos
  set R : ℝ := f.rOut/f.rIn with hR_def
  have hR1 : (1:ℝ) < R := f.one_lt_rOut_div_rIn
  set y : ℝ := f.rIn⁻¹ * (u - c) with hy_def
  -- the partial-slice derivative equals the φ-value, wherever needed
  have hmem : ∀ z : ℝ, ((R, z) : ℝ × ℝ) ∈ Ioi (1:ℝ) ×ˢ univ :=
    fun z => ⟨lt_of_lt_of_le hR₀ hfR₀, trivial⟩
  have hslice : ∀ z : ℝ, HasDerivAt (fun x : ℝ => g (R, x)) (φ (R, z)) z := by
    intro z
    have hjoint : DifferentiableAt ℝ g (R, z) :=
      (hg_smooth.contDiffAt (hU.mem_nhds (hmem z))).differentiableAt
        (by simp)
    have hι : HasFDerivAt (fun x : ℝ => ((R, x) : ℝ × ℝ))
        (((0 : ℝ →L[ℝ] ℝ)).prod (ContinuousLinearMap.id ℝ ℝ)) z :=
      (hasFDerivAt_const R z).prodMk (hasFDerivAt_id z)
    have hcomp := (hjoint.hasFDerivAt.comp z hι)
    have hact := hcomp.hasDerivAt
    have hval : ((fderiv ℝ g (R, z)).comp
        (((0 : ℝ →L[ℝ] ℝ)).prod (ContinuousLinearMap.id ℝ ℝ))) 1
        = φ (R, z) := by
      simp [hφ_def]
    rw [hval] at hact
    exact hact
  -- the bump as the composed slice
  have hinner : HasDerivAt (fun v : ℝ => f.rIn⁻¹ * (v - c)) f.rIn⁻¹ u := by
    simpa using ((hasDerivAt_id u).sub_const c).const_mul f.rIn⁻¹
  have hbump : HasDerivAt (⇑f) (φ (R, y) * f.rIn⁻¹) u := by
    have hcomp := (hslice y).comp u hinner
    have hfeq : (fun v : ℝ => g (R, f.rIn⁻¹ * (v - c))) = ⇑f := by
      funext v
      rw [ContDiffBump.apply]
      simp [hg_def, smul_eq_mul, hbase_def, hR_def]
    rw [← hfeq]
    exact hcomp
  rw [hbump.deriv]
  -- price the φ-value: inside the window by the max, outside by zero
  have hφle : |φ (R, y)| ≤ C₀ := by
    by_cases hy : |y| ≤ R₁
    · have hyK : ((R, y) : ℝ × ℝ) ∈ K := by
        refine ⟨⟨hfR₀, hfR₁⟩, ?_⟩
        simpa [mem_closedBall, dist_zero_left, Real.norm_eq_abs] using hy
      have := hmax hyK
      simpa [hC₀_def, Real.norm_eq_abs] using this
    · push_neg at hy
      have hzero : φ (R, y) = 0 := by
        have hopen : IsOpen {x : ℝ | R < |x|} :=
          isOpen_lt continuous_const continuous_abs
      -- the slice vanishes on an open set around `y`
        have hev : (fun x : ℝ => g (R, x)) =ᶠ[nhds y] (fun _ => 0) := by
          refine Filter.eventuallyEq_of_mem (hopen.mem_nhds ?_) ?_
          · show R < |y|
            linarith [hfR₁]
          · intro x hx
            simp only [Set.mem_setOf_eq] at hx
            have hnot : x ∉ Function.support (base.toFun R) := by
              rw [base.support R hR1, mem_ball, dist_zero_right,
                Real.norm_eq_abs]
              linarith
            have := Function.notMem_support.mp hnot
            simpa [hg_def, Function.uncurry] using this
        have hde : deriv (fun x : ℝ => g (R, x)) y = 0 := by
          rw [hev.deriv_eq]
          simp
        rw [← (hslice y).deriv]
        exact hde
      rw [hzero]
      simp [hC₀_def]
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hrIn.le), div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hφle (inv_nonneg.mpr hrIn.le)

end MoltResearch
