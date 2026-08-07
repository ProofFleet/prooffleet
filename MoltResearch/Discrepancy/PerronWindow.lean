import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Track R: the Perron window (campaign #3044, M2-i1)

The quantitative Perron kernel of the cheap-Halász main term: a smooth
compactly supported window agreeing with `e^{−v}` on `[ρ, 2Y+1]`,
built by scaling a fixed master transition, with second-derivative
mass `≤ 9(C+1)²/ρ²` — so its Fourier transform has the explicit
`M₂/(2π|ξ|)²`-tail that prices the off-band part of the Hölder split,
uniformly in the scale `Y = log x`.
-/

namespace MoltResearch

namespace ExpSums

open Real MeasureTheory
open scoped FourierTransform ContDiff

/-- **The master transition** (Track R, M2-i1a): a smooth `0→1`
transition on `[0,1]` whose first two derivatives are uniformly bounded
by a single absolute constant, with derivatives supported in `[0,1]`.
The one existential constant of the Perron-window family — every
window scales from it, so the cheap-Halász thresholds depend only on
this `C`. -/
theorem exists_master_transition :
    ∃ (σ : ℝ → ℝ) (C : ℝ), ContDiff ℝ ∞ σ
      ∧ (∀ v, 0 ≤ σ v ∧ σ v ≤ 1)
      ∧ (∀ v, v ≤ 0 → σ v = 0) ∧ (∀ v, 1 ≤ v → σ v = 1)
      ∧ 0 ≤ C
      ∧ (∀ v, |deriv σ v| ≤ C)
      ∧ (∀ v, |deriv (deriv σ) v| ≤ C) := by
  classical
  set σ : ℝ → ℝ := Real.smoothTransition with hσ_def
  have hsm : ContDiff ℝ ∞ σ := Real.smoothTransition.contDiff
  have hzero : ∀ v, v ≤ 0 → σ v = 0 := fun v hv =>
    Real.smoothTransition.zero_of_nonpos hv
  have hone : ∀ v, 1 ≤ v → σ v = 1 := fun v hv =>
    Real.smoothTransition.one_of_one_le hv
  -- derivatives vanish off (0,1)
  have hd_zero : ∀ (f : ℝ → ℝ), (∀ v, v ≤ 0 → f v = 0) →
      (∀ v, 1 ≤ v → f v = 1) → ∀ v, v < 0 ∨ 1 < v → deriv f v = 0 := by
    intro f hf0 hf1 v hv
    rcases hv with hv | hv
    · have heq : f =ᶠ[nhds v] (fun _ => 0) := by
        refine Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Iio hv) ?_
        intro u hu
        exact hf0 u (le_of_lt hu)
      rw [heq.deriv_eq, deriv_const]
    · have heq : f =ᶠ[nhds v] (fun _ => 1) := by
        refine Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Ioi hv) ?_
        intro u hu
        exact hf1 u (le_of_lt hu)
      rw [heq.deriv_eq, deriv_const]
  have hd1_zero : ∀ v, v < 0 ∨ 1 < v → deriv σ v = 0 :=
    hd_zero σ hzero hone
  have hd2_zero : ∀ v, v < 0 ∨ 1 < v → deriv (deriv σ) v = 0 := by
    intro v hv
    rcases hv with hv | hv
    · have heq : deriv σ =ᶠ[nhds v] (fun _ => 0) := by
        refine Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Iio hv) ?_
        intro u hu
        exact hd1_zero u (Or.inl hu)
      rw [heq.deriv_eq, deriv_const]
    · have heq : deriv σ =ᶠ[nhds v] (fun _ => 0) := by
        refine Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Ioi hv) ?_
        intro u hu
        exact hd1_zero u (Or.inr hu)
      rw [heq.deriv_eq, deriv_const]
  have hd1sm : Continuous (deriv σ) := by
    have h := hsm.iterate_deriv 1
    simpa using h.continuous
  have hd2sm : Continuous (deriv (deriv σ)) := by
    have h := hsm.iterate_deriv 2
    have h2 : deriv^[2] σ = deriv (deriv σ) := by
      funext v
      simp [Function.iterate_succ, Function.iterate_one]
    rw [h2] at h
    exact h.continuous
  have hcs : ∀ (f : ℝ → ℝ), (∀ v, v < 0 ∨ 1 < v → f v = 0) →
      HasCompactSupport f := by
    intro f hf
    refine HasCompactSupport.intro isCompact_Icc (K := Set.Icc (0:ℝ) 1) ?_
    intro v hv
    rw [Set.mem_Icc] at hv
    push_neg at hv
    by_cases h0 : v < 0
    · exact hf v (Or.inl h0)
    · push_neg at h0
      exact hf v (Or.inr (hv h0))
  have hb1 : ∃ C₁, ∀ v, |deriv σ v| ≤ C₁ := by
    obtain ⟨v₀, hv₀⟩ := Continuous.exists_forall_ge_of_hasCompactSupport
      (hd1sm.abs) ((hcs _ hd1_zero).abs)
    exact ⟨|deriv σ v₀|, hv₀⟩
  have hb2 : ∃ C₂, ∀ v, |deriv (deriv σ) v| ≤ C₂ := by
    obtain ⟨v₀, hv₀⟩ := Continuous.exists_forall_ge_of_hasCompactSupport
      (hd2sm.abs) ((hcs _ hd2_zero).abs)
    exact ⟨|deriv (deriv σ) v₀|, hv₀⟩
  obtain ⟨C₁, hC₁⟩ := hb1
  obtain ⟨C₂, hC₂⟩ := hb2
  refine ⟨σ, max C₁ C₂, hsm, ?_, hzero, hone, ?_, ?_, ?_⟩
  · intro v
    exact ⟨Real.smoothTransition.nonneg v, Real.smoothTransition.le_one v⟩
  · exact le_trans (abs_nonneg _) (le_trans (hC₁ 0) (le_max_left _ _))
  · intro v
    exact le_trans (hC₁ v) (le_max_left _ _)
  · intro v
    exact le_trans (hC₂ v) (le_max_right _ _)


/-- **The Perron window** (Track R, M2-i1b): from the master transition,
a smooth compactly supported window agreeing with `e^{−v}` on
`[ρ, 2Y+1]`, vanishing off `[0, 2Y+2]`, bounded by `1`, with
second-derivative mass at most `9(C+1)²/ρ²` — the quantitative Perron
kernel of the cheap-Halász main term. -/
theorem exists_perron_window (σ : ℝ → ℝ) (C : ℝ)
    (hσs : ContDiff ℝ ∞ σ) (hσ01 : ∀ v, 0 ≤ σ v ∧ σ v ≤ 1)
    (hσ0 : ∀ v, v ≤ 0 → σ v = 0) (hσ1 : ∀ v, 1 ≤ v → σ v = 1)
    (hC0 : 0 ≤ C) (hC1 : ∀ v, |deriv σ v| ≤ C)
    (hC2 : ∀ v, |deriv (deriv σ) v| ≤ C)
    (ρ Y : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hY : 1 ≤ Y) :
    ∃ V : ℝ → ℝ, ContDiff ℝ ∞ V ∧ HasCompactSupport V
      ∧ (∀ v, v ≤ 0 → V v = 0) ∧ (∀ v, 2*Y + 2 ≤ v → V v = 0)
      ∧ (∀ v, ρ ≤ v → v ≤ 2*Y + 1 → V v = Real.exp (-v))
      ∧ (∀ v, 0 ≤ V v) ∧ (∀ v, V v ≤ Real.exp (-v))
      ∧ (∀ v, |V v| ≤ 1)
      ∧ ∫ v, |iteratedDeriv 2 V v| ≤ 9*(C+1)^2/ρ^2 := by
  classical
  have hσ1s : ContDiff ℝ ∞ (deriv σ) := by
    simpa using hσs.iterate_deriv 1
  set a : ℝ := 2*Y + 1 with ha_def
  set S : ℝ → ℝ := fun v => σ (v/ρ) * (1 - σ (v - a)) with hS_def
  set V : ℝ → ℝ := fun v => Real.exp (-v) * S v with hV_def
  have hcomp1 : ContDiff ℝ ∞ (fun v : ℝ => σ (v/ρ)) :=
    hσs.comp (contDiff_id.div_const ρ)
  have hcomp2 : ContDiff ℝ ∞ (fun v : ℝ => σ (v - a)) :=
    hσs.comp (contDiff_id.sub contDiff_const)
  have hSs : ContDiff ℝ ∞ S := hcomp1.mul (contDiff_const.sub hcomp2)
  have hVs : ContDiff ℝ ∞ V :=
    ((Real.contDiff_exp.comp contDiff_neg)).mul hSs
  have hS0 : ∀ v, v ≤ 0 → S v = 0 := by
    intro v hv
    rw [hS_def]
    dsimp only
    rw [hσ0 (v/ρ) (div_nonpos_of_nonpos_of_nonneg hv hρ0.le), zero_mul]
  have hS_after : ∀ v, 2*Y + 2 ≤ v → S v = 0 := by
    intro v hv
    rw [hS_def]
    dsimp only
    rw [hσ1 (v - a) (by rw [ha_def]; linarith), sub_self, mul_zero]
  have hV0 : ∀ v, v ≤ 0 → V v = 0 := by
    intro v hv
    rw [hV_def]
    dsimp only
    rw [hS0 v hv, mul_zero]
  have hV_after : ∀ v, 2*Y + 2 ≤ v → V v = 0 := by
    intro v hv
    rw [hV_def]
    dsimp only
    rw [hS_after v hv, mul_zero]
  have hVc : HasCompactSupport V := by
    refine HasCompactSupport.intro (isCompact_Icc
      (a := (0:ℝ)) (b := 2*Y+2)) ?_
    intro v hv
    rw [Set.mem_Icc] at hv
    push_neg at hv
    by_cases h0 : v < 0
    · exact hV0 v h0.le
    · push_neg at h0
      exact hV_after v (hv h0).le
  have hplateau : ∀ v, ρ ≤ v → v ≤ 2*Y + 1 → V v = Real.exp (-v) := by
    intro v h1 h2
    rw [hV_def]
    dsimp only
    rw [hS_def]
    dsimp only
    rw [hσ1 (v/ρ) ((le_div_iff₀ hρ0).mpr (by linarith)),
      hσ0 (v - a) (by rw [ha_def]; linarith)]
    ring
  have hS01 : ∀ v, 0 ≤ S v ∧ S v ≤ 1 := by
    intro v
    rw [hS_def]
    dsimp only
    constructor
    · refine mul_nonneg (hσ01 _).1 ?_
      linarith [(hσ01 (v - a)).2]
    · have h1 : σ (v/ρ) ≤ 1 := (hσ01 _).2
      have h2 : 0 ≤ 1 - σ (v - a) := by linarith [(hσ01 (v - a)).2]
      have h3 : 1 - σ (v - a) ≤ 1 := by linarith [(hσ01 (v - a)).1]
      nlinarith [(hσ01 (v/ρ)).1]
  have hVnn : ∀ v, 0 ≤ V v := by
    intro v
    rw [hV_def]
    dsimp only
    exact mul_nonneg (Real.exp_pos _).le (hS01 v).1
  have hVle : ∀ v, V v ≤ Real.exp (-v) := by
    intro v
    rw [hV_def]
    dsimp only
    calc Real.exp (-v) * S v ≤ Real.exp (-v) * 1 :=
        mul_le_mul_of_nonneg_left (hS01 v).2 (Real.exp_pos _).le
      _ = Real.exp (-v) := mul_one _
  have hVabs : ∀ v, |V v| ≤ 1 := by
    intro v
    rw [abs_of_nonneg (hVnn v)]
    by_cases h0 : v ≤ 0
    · rw [hV0 v h0]
      norm_num
    · push_neg at h0
      calc V v ≤ Real.exp (-v) := hVle v
        _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
        _ = 1 := Real.exp_zero
  refine ⟨V, hVs, hVc, hV0, hV_after, hplateau, hVnn, hVle, hVabs, ?_⟩
  -- derivative machinery
  have hσdiff : Differentiable ℝ σ := hσs.differentiable (by simp)
  have hσ'diff : Differentiable ℝ (deriv σ) := hσ1s.differentiable (by simp)
  set S₁ : ℝ → ℝ := fun v => deriv σ (v/ρ) / ρ * (1 - σ (v - a))
      - σ (v/ρ) * deriv σ (v - a) with hS₁_def
  set S₂ : ℝ → ℝ := fun v => deriv (deriv σ) (v/ρ) / ρ^2 * (1 - σ (v - a))
      - 2 * (deriv σ (v/ρ) / ρ) * deriv σ (v - a)
      - σ (v/ρ) * deriv (deriv σ) (v - a) with hS₂_def
  have hcomp_div : ∀ v : ℝ, HasDerivAt (fun v : ℝ => v/ρ) (1/ρ) v := by
    intro v
    simpa using (hasDerivAt_id v).div_const ρ
  have hcomp_sub : ∀ v : ℝ, HasDerivAt (fun v : ℝ => v - a) 1 v :=
    fun v => (hasDerivAt_id v).sub_const a
  have hσ_at : ∀ (g : ℝ → ℝ), Differentiable ℝ g → ∀ v : ℝ,
      HasDerivAt (fun v : ℝ => g (v/ρ)) (deriv g (v/ρ) / ρ) v := by
    intro g hg v
    have hout : HasDerivAt g (deriv g (v/ρ)) (v/ρ) :=
      (hg (v/ρ)).hasDerivAt
    have := hout.comp v (hcomp_div v)
    simpa [div_eq_mul_inv] using this
  have hσ_at2 : ∀ (g : ℝ → ℝ), Differentiable ℝ g → ∀ v : ℝ,
      HasDerivAt (fun v : ℝ => g (v - a)) (deriv g (v - a)) v := by
    intro g hg v
    have hout : HasDerivAt g (deriv g (v - a)) (v - a) :=
      (hg (v - a)).hasDerivAt
    have := hout.comp v (hcomp_sub v)
    simpa using this
  have hS'at : ∀ v, HasDerivAt S (S₁ v) v := by
    intro v
    have h1 := hσ_at σ hσdiff v
    have h3 : HasDerivAt (fun v : ℝ => 1 - σ (v - a))
        (-(deriv σ (v - a))) v := by
      simpa using (hasDerivAt_const v (1:ℝ)).sub (hσ_at2 σ hσdiff v)
    have := h1.mul h3
    rw [hS_def, hS₁_def]
    convert this using 1
    ring
  have hS''at : ∀ v, HasDerivAt S₁ (S₂ v) v := by
    intro v
    have h1 := hσ_at (deriv σ) hσ'diff v
    have h1' : HasDerivAt (fun v : ℝ => deriv σ (v/ρ) / ρ)
        (deriv (deriv σ) (v/ρ) / ρ / ρ) v :=
      (hσ_at (deriv σ) hσ'diff v).div_const ρ
    have h3 : HasDerivAt (fun v : ℝ => 1 - σ (v - a))
        (-(deriv σ (v - a))) v := by
      simpa using (hasDerivAt_const v (1:ℝ)).sub (hσ_at2 σ hσdiff v)
    have hA := h1'.mul h3
    have hB := (hσ_at σ hσdiff v).mul (hσ_at2 (deriv σ) hσ'diff v)
    have := hA.sub hB
    rw [hS₁_def, hS₂_def]
    convert this using 1
    field_simp
    ring
  have hexp_at : ∀ v : ℝ, HasDerivAt (fun v : ℝ => Real.exp (-v))
      (-(Real.exp (-v))) v := by
    intro v
    have := (Real.hasDerivAt_exp (-v)).comp v ((hasDerivAt_id v).neg)
    simpa using this
  have hV'at : ∀ v, HasDerivAt V (Real.exp (-v) * (S₁ v - S v)) v := by
    intro v
    have := (hexp_at v).mul (hS'at v)
    rw [hV_def]
    convert this using 1
    ring
  have hV''at : ∀ v, HasDerivAt (fun v => Real.exp (-v) * (S₁ v - S v))
      (Real.exp (-v) * (S₂ v - 2*S₁ v + S v)) v := by
    intro v
    have hs := (hS''at v).sub (hS'at v)
    have := (hexp_at v).mul hs
    convert this using 1
    simp only [Pi.sub_apply]
    ring
  have hiter : iteratedDeriv 2 V
      = fun v => Real.exp (-v) * (S₂ v - 2*S₁ v + S v) := by
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have hd1 : deriv V = fun v => Real.exp (-v) * (S₁ v - S v) :=
      funext fun v => (hV'at v).deriv
    rw [hd1]
    exact funext fun v => (hV''at v).deriv
  -- σ-derivative vanishing at nonpositive arguments
  have hσ'zero : ∀ u : ℝ, u < 0 → deriv σ u = 0 := by
    intro u hu
    have heq : σ =ᶠ[nhds u] (fun _ => 0) := by
      refine Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Iio hu) ?_
      intro x hx
      exact hσ0 x (le_of_lt hx)
    rw [heq.deriv_eq, deriv_const]
  have hσ''zero : ∀ u : ℝ, u < 0 → deriv (deriv σ) u = 0 := by
    intro u hu
    have heq : deriv σ =ᶠ[nhds u] (fun _ => 0) := by
      refine Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Iio hu) ?_
      intro x hx
      exact hσ'zero x hx
    rw [heq.deriv_eq, deriv_const]
  -- the pointwise majorant
  set K : ℝ := 9*(C+1)^2/ρ^2 with hK_def
  have hK0 : 0 ≤ K := by rw [hK_def]; positivity
  have hpt : ∀ v : ℝ, |iteratedDeriv 2 V v|
      ≤ Set.indicator (Set.Ici (0:ℝ)) (fun v => K * Real.exp (-v)) v := by
    intro v
    rw [hiter]
    dsimp only
    by_cases hv : (0:ℝ) ≤ v
    · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hv)]
      have hσb : ∀ u, |σ u| ≤ 1 := by
        intro u
        rw [abs_le]
        exact ⟨by linarith [(hσ01 u).1], (hσ01 u).2⟩
      have h1σb : ∀ u, |1 - σ u| ≤ 1 := by
        intro u
        rw [abs_le]
        constructor <;> [linarith [(hσ01 u).2]; linarith [(hσ01 u).1]]
      have hS_b : |S v| ≤ 1 := by
        rw [hS_def]
        dsimp only
        rw [abs_mul]
        calc |σ (v/ρ)| * |1 - σ (v - a)| ≤ 1 * 1 :=
            mul_le_mul (hσb _) (h1σb _) (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      have hS₁_b : |S₁ v| ≤ C/ρ + C := by
        rw [hS₁_def]
        dsimp only
        refine le_trans (abs_sub _ _) ?_
        rw [abs_mul, abs_mul, abs_div]
        have h1 : |deriv σ (v/ρ)|/|ρ| * |1 - σ (v - a)| ≤ C/ρ := by
          rw [abs_of_pos hρ0]
          calc |deriv σ (v/ρ)|/ρ * |1 - σ (v - a)|
              ≤ C/ρ * 1 := by
                refine mul_le_mul ?_ (h1σb _) (abs_nonneg _) (by positivity)
                exact div_le_div_of_nonneg_right (hC1 _) hρ0.le
            _ = C/ρ := mul_one _
        have h2 : |σ (v/ρ)| * |deriv σ (v - a)| ≤ C := by
          calc |σ (v/ρ)| * |deriv σ (v - a)| ≤ 1 * C :=
              mul_le_mul (hσb _) (hC1 _) (abs_nonneg _) zero_le_one
            _ = C := one_mul C
        linarith
      have hS₂_b : |S₂ v| ≤ C/ρ^2 + 2*C^2/ρ + C := by
        rw [hS₂_def]
        dsimp only
        refine le_trans (abs_sub _ _) ?_
        refine add_le_add (le_trans (abs_sub _ _) ?_) ?_
        · refine add_le_add ?_ ?_
          · rw [abs_mul, abs_div]
            have : |ρ^2| = ρ^2 := abs_of_pos (by positivity)
            rw [this]
            calc |deriv (deriv σ) (v/ρ)|/ρ^2 * |1 - σ (v - a)|
                ≤ C/ρ^2 * 1 := by
                  refine mul_le_mul ?_ (h1σb _) (abs_nonneg _) (by positivity)
                  exact div_le_div_of_nonneg_right (hC2 _) (by positivity : (0:ℝ) ≤ ρ^2)
              _ = C/ρ^2 := mul_one _
          · rw [abs_mul, abs_mul, abs_div, abs_of_pos hρ0]
            rw [show |(2:ℝ)| = 2 from by norm_num]
            calc 2 * (|deriv σ (v/ρ)|/ρ) * |deriv σ (v - a)|
                ≤ 2 * (C/ρ) * C := by
                  refine mul_le_mul ?_ (hC1 _) (abs_nonneg _) ?_
                  · refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
                    exact div_le_div_of_nonneg_right (hC1 _) hρ0.le
                  · positivity
              _ = 2*C^2/ρ := by ring
        · rw [abs_mul]
          calc |σ (v/ρ)| * |deriv (deriv σ) (v - a)| ≤ 1 * C :=
              mul_le_mul (hσb _) (hC2 _) (abs_nonneg _) zero_le_one
            _ = C := one_mul C
      rw [abs_mul, Real.abs_exp]
      rw [hK_def, show 9*(C+1)^2/ρ^2 * Real.exp (-v)
          = Real.exp (-v) * (9*(C+1)^2/ρ^2) from by ring]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      have h3 : |2*S₁ v| = 2*|S₁ v| := by
        rw [abs_mul, show |(2:ℝ)| = 2 from by norm_num]
      have htri : |S₂ v - 2*S₁ v + S v| ≤ |S₂ v| + 2*|S₁ v| + |S v| := by
        calc |S₂ v - 2*S₁ v + S v| ≤ |S₂ v - 2*S₁ v| + |S v| :=
            abs_add_le _ _
          _ ≤ (|S₂ v| + |2*S₁ v|) + |S v| := by
              linarith [abs_sub (S₂ v) (2*S₁ v)]
          _ = |S₂ v| + 2*|S₁ v| + |S v| := by rw [h3]
      refine le_trans htri ?_
      have hρ2' : (0:ℝ) < ρ^2 := by positivity
      calc |S₂ v| + 2*|S₁ v| + |S v|
          ≤ (C/ρ^2 + 2*C^2/ρ + C) + 2*(C/ρ + C) + 1 := by
            linarith [hS₂_b, hS₁_b, hS_b]
        _ ≤ 9*(C+1)^2/ρ^2 := by
            rw [le_div_iff₀ hρ2']
            have hexpand : ((C/ρ^2 + 2*C^2/ρ + C) + 2*(C/ρ + C) + 1)*ρ^2
                = C + 2*C^2*ρ + C*ρ^2 + 2*C*ρ + 2*C*ρ^2 + ρ^2 := by
              field_simp
              ring
            rw [hexpand]
            nlinarith [hρ1, hρ0.le, hC0, sq_nonneg C, sq_nonneg ρ,
              mul_nonneg hC0 hρ0.le]
    · push_neg at hv
      rw [Set.indicator_of_notMem (by
        rw [Set.mem_Ici]
        push_neg
        exact hv)]
      have hva : v/ρ < 0 := div_neg_of_neg_of_pos hv hρ0
      have hvb : v - a < 0 := by
        rw [ha_def]
        linarith
      have hS_z : S v = 0 := hS0 v hv.le
      have hS₁_z : S₁ v = 0 := by
        rw [hS₁_def]
        dsimp only
        rw [hσ'zero _ hva, hσ0 _ hva.le, hσ'zero _ hvb]
        ring
      have hS₂_z : S₂ v = 0 := by
        rw [hS₂_def]
        dsimp only
        rw [hσ''zero _ hva, hσ'zero _ hva, hσ0 _ hva.le, hσ''zero _ hvb]
        ring
      rw [hS_z, hS₁_z, hS₂_z]
      norm_num
  -- the σ-derivatives also vanish beyond 1
  have hσ'one : ∀ u : ℝ, 1 < u → deriv σ u = 0 := by
    intro u hu
    have heq : σ =ᶠ[nhds u] (fun _ => 1) := by
      refine Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Ioi hu) ?_
      intro x hx
      exact hσ1 x (le_of_lt hx)
    rw [heq.deriv_eq, deriv_const]
  have hσ''one : ∀ u : ℝ, 1 < u → deriv (deriv σ) u = 0 := by
    intro u hu
    have heq : deriv σ =ᶠ[nhds u] (fun _ => 0) := by
      refine Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Ioi hu) ?_
      intro x hx
      exact hσ'one x hx
    rw [heq.deriv_eq, deriv_const]
  -- continuity and compact support of the second derivative
  have hcontS : Continuous S := hSs.continuous
  have hσc : Continuous σ := hσs.continuous
  have hσ'c : Continuous (deriv σ) := hσ1s.continuous
  have hσ''c : Continuous (deriv (deriv σ)) := by
    have h := hσs.iterate_deriv 2
    have h2 : deriv^[2] σ = deriv (deriv σ) := by
      funext u
      simp [Function.iterate_succ, Function.iterate_one]
    rw [h2] at h
    exact h.continuous
  have hcd : Continuous (fun v : ℝ => v/ρ) := continuous_id.div_const ρ
  have hcs' : Continuous (fun v : ℝ => v - a) :=
    continuous_id.sub continuous_const
  have hcontS₁ : Continuous S₁ := by
    rw [hS₁_def]
    exact (((hσ'c.comp hcd).div_const ρ).mul
      (continuous_const.sub (hσc.comp hcs'))).sub
      ((hσc.comp hcd).mul (hσ'c.comp hcs'))
  have hcontS₂ : Continuous S₂ := by
    rw [hS₂_def]
    exact ((((hσ''c.comp hcd).div_const (ρ^2)).mul
      (continuous_const.sub (hσc.comp hcs'))).sub
      ((continuous_const.mul ((hσ'c.comp hcd).div_const ρ)).mul
        (hσ'c.comp hcs'))).sub
      ((hσc.comp hcd).mul (hσ''c.comp hcs'))
  have hcont2 : Continuous (iteratedDeriv 2 V) := by
    rw [hiter]
    exact (Real.continuous_exp.comp continuous_neg).mul
      ((hcontS₂.sub (continuous_const.mul hcontS₁)).add hcontS)
  have hcs2 : HasCompactSupport (iteratedDeriv 2 V) := by
    rw [hiter]
    refine HasCompactSupport.intro (isCompact_Icc
      (a := (0:ℝ)) (b := 2*Y+2)) ?_
    intro v hv
    rw [Set.mem_Icc] at hv
    push_neg at hv
    by_cases h0 : v < 0
    · have hva : v/ρ < 0 := div_neg_of_neg_of_pos h0 hρ0
      have hvb : v - a < 0 := by
        rw [ha_def]
        linarith
      rw [hS0 v h0.le]
      rw [show S₁ v = 0 from by
        rw [hS₁_def]
        dsimp only
        rw [hσ'zero _ hva, hσ0 _ hva.le, hσ'zero _ hvb]
        ring]
      rw [show S₂ v = 0 from by
        rw [hS₂_def]
        dsimp only
        rw [hσ''zero _ hva, hσ'zero _ hva, hσ0 _ hva.le, hσ''zero _ hvb]
        ring]
      ring
    · push_neg at h0
      have hv2 := hv h0
      have hva : 1 < v/ρ := by
        rw [lt_div_iff₀ hρ0]
        nlinarith
      have hvb : 1 < v - a := by
        rw [ha_def]
        linarith
      rw [show S v = 0 from by
        rw [hS_def]
        dsimp only
        rw [hσ1 (v - a) hvb.le, sub_self, mul_zero]]
      rw [show S₁ v = 0 from by
        rw [hS₁_def]
        dsimp only
        rw [hσ'one _ hva, hσ1 (v - a) hvb.le, hσ'one _ hvb, sub_self]
        ring]
      rw [show S₂ v = 0 from by
        rw [hS₂_def]
        dsimp only
        rw [hσ''one _ hva, hσ'one _ hva, hσ1 (v - a) hvb.le,
          hσ''one _ hvb, sub_self]
        ring]
      ring
  -- integrate the majorant
  have hint2 : Integrable (fun v => |iteratedDeriv 2 V v|) :=
    (hcont2.integrable_of_hasCompactSupport hcs2).abs
  have hind_int : Integrable
      (Set.indicator (Set.Ici (0:ℝ)) (fun v => K * Real.exp (-v))) := by
    rw [integrable_indicator_iff measurableSet_Ici]
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine Integrable.const_mul ?_ K
    have := exp_neg_integrableOn_Ioi (0:ℝ) (one_pos)
    simpa [neg_mul, one_mul] using this
  refine le_trans (integral_mono hint2 hind_int hpt) ?_
  rw [integral_indicator measurableSet_Ici]
  rw [integral_Ici_eq_integral_Ioi]
  rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one, hK_def]

/-- Casting commutes with `deriv`. -/
theorem deriv_ofReal_comp (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    deriv (fun v => ((f v : ℝ) : ℂ)) = fun v => ((deriv f v : ℝ) : ℂ) := by
  funext v
  exact (((hf.differentiable (by simp)) v).hasDerivAt.ofReal_comp).deriv

/-- Casting commutes with the second iterated derivative. -/
theorem iteratedDeriv_two_ofReal (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    iteratedDeriv 2 (fun v => ((f v : ℝ) : ℂ))
      = fun v => ((iteratedDeriv 2 f v : ℝ) : ℂ) := by
  have hf1 : ContDiff ℝ ∞ (deriv f) := by
    simpa using hf.iterate_deriv 1
  rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
    iteratedDeriv_succ, iteratedDeriv_one]
  rw [deriv_ofReal_comp f hf, deriv_ofReal_comp (deriv f) hf1]

/-- **Pointwise decay of a smooth window's transform** (Track R, N37):
for `V` smooth and compactly supported and `ξ ≠ 0`,

  `‖𝓕V(ξ)‖ ≤ M₂/(4π²ξ²)`,  `M₂ = ∫|V''|`.

Two integrations by parts: `𝓕V(ξ) = 𝓕(V'')(ξ)/(2πiξ)²`.

This is the ingredient that lets the sharp Halász argument run in the
*smoothed* Perron setting.  GHS's `I₂` carries the contour weight
`|ds|/|s|² = dt/(1+t²)`; here the same weight is supplied by the window
transform, so `sum_unit_interval_halasz_le` applies with no contour
integral anywhere.

The bound already existed inside `fourier_tail_le`'s proof as a local
step on the way to the tail mass `M₂/(2π²L)`; the pointwise form is
what the unit-interval decomposition needs, since it must be charged to
`1/(N²+1)` frequency by frequency rather than integrated away. -/
theorem fourier_pointwise_decay (V : ℝ → ℝ) (hVs : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (M₂ : ℝ)
    (hM₂ : ∫ v, |iteratedDeriv 2 V v| ≤ M₂) (ξ : ℝ) (hξ : ξ ≠ 0) :
    ‖𝓕 (fun v => ((V v : ℝ) : ℂ)) ξ‖ ≤ M₂/(4*Real.pi^2*ξ^2) := by
  classical
  set Vc : ℝ → ℂ := fun v => ((V v : ℝ) : ℂ) with hVc_def
  have hVcs : ContDiff ℝ ∞ Vc := Complex.ofRealCLM.contDiff.comp hVs
  have hVcc : HasCompactSupport Vc :=
    HasCompactSupport.comp_left hVc Complex.ofReal_zero
  have haux : ∀ n : ℕ, ContDiff ℝ ∞ (iteratedDeriv n Vc)
      ∧ HasCompactSupport (iteratedDeriv n Vc) := by
    intro n
    induction n with
    | zero =>
      rw [iteratedDeriv_zero]
      exact ⟨hVcs, hVcc⟩
    | succ k ih =>
      rw [iteratedDeriv_succ]
      refine ⟨?_, ih.2.deriv⟩
      simpa using ih.1.iterate_deriv 1
  have hint : ∀ n : ℕ, Integrable (iteratedDeriv n Vc) := fun n =>
    ((haux n).1.continuous).integrable_of_hasCompactSupport (haux n).2
  have hFI := Real.fourier_iteratedDeriv (f := Vc) (N := (2:ℕ∞))
    (hVcs.of_le (by exact_mod_cast le_top)) (fun n _ => hint n) (le_refl _)
  have h1 := congrFun hFI ξ
  have hnorm2 : ‖((2*Real.pi*Complex.I*(ξ:ℂ))^2 : ℂ)‖
      = 4*Real.pi^2*ξ^2 := by
    rw [norm_pow]
    rw [show (2*Real.pi*Complex.I*(ξ:ℂ))
        = (((2*Real.pi*ξ : ℝ)):ℂ) * Complex.I from by push_cast; ring]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    ring
  have h2 : ‖𝓕 (iteratedDeriv 2 Vc) ξ‖ = 4*Real.pi^2*ξ^2 * ‖𝓕 Vc ξ‖ := by
    rw [h1, norm_smul, hnorm2]
  have h3 : ‖𝓕 (iteratedDeriv 2 Vc) ξ‖ ≤ M₂ := by
    refine le_trans (VectorFourier.norm_fourierIntegral_le_integral_norm
      _ _ _ _ _) ?_
    rw [iteratedDeriv_two_ofReal V hVs]
    refine le_trans (le_of_eq ?_) hM₂
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    dsimp only
    rw [Complex.norm_real, Real.norm_eq_abs]
  have h4 : (0:ℝ) < 4*Real.pi^2*ξ^2 := by
    have := Real.pi_pos
    have hξ2 : (0:ℝ) < ξ^2 := by positivity
    positivity
  rw [le_div_iff₀ h4]
  calc ‖𝓕 Vc ξ‖ * (4*Real.pi^2*ξ^2)
      = 4*Real.pi^2*ξ^2 * ‖𝓕 Vc ξ‖ := by ring
    _ = ‖𝓕 (iteratedDeriv 2 Vc) ξ‖ := h2.symm
    _ ≤ M₂ := h3

/-- **The window transform is a Perron weight** (Track R, N38): for `V`
smooth and compactly supported,

  `‖𝓕V(ξ)‖ ≤ (2·MV + M₂/(2π²))/(1 + ξ²)`,

where `MV` bounds `‖𝓕V‖` and `M₂ = ∫|V''|`.

This is the join between the smoothed Perron setting and the sharp
Halász argument.  GHS take the contour weight `|ds|/|s|² = dt/(1+t²)`
directly; here the same shape is produced from the window, by using the
sup bound near the origin and `fourier_pointwise_decay` away from it.

Both regimes are needed and neither suffices alone: the pointwise decay
is vacuous at `ξ = 0`, and the sup carries no decay.  Splitting at
`|ξ| = 1` costs only the factor `2` in each, since `1 + ξ² ≤ 2` there
and `1 + ξ² ≤ 2ξ²` beyond.

With this, `sum_unit_interval_halasz_le` can be applied to the smoothed
Perron integral — no contour required. -/
theorem fourier_window_le_inv_one_add_sq (V : ℝ → ℝ) (hVs : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (M₂ MV : ℝ)
    (hM₂ : ∫ v, |iteratedDeriv 2 V v| ≤ M₂)
    (hMV : ∀ ξ, ‖𝓕 (fun v => ((V v : ℝ) : ℂ)) ξ‖ ≤ MV) (ξ : ℝ) :
    ‖𝓕 (fun v => ((V v : ℝ) : ℂ)) ξ‖
      ≤ (2*MV + M₂/(2*Real.pi^2))/(1+ξ^2) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hMV0 : (0:ℝ) ≤ MV := le_trans (norm_nonneg _) (hMV 0)
  have hM₂0 : (0:ℝ) ≤ M₂ :=
    le_trans (integral_nonneg fun v => abs_nonneg _) hM₂
  have hden : (0:ℝ) < 1 + ξ^2 := by positivity
  rw [le_div_iff₀ hden]
  by_cases hsmall : ξ^2 ≤ 1
  · -- near the origin: the sup bound, at a cost of 2
    calc ‖𝓕 (fun v => ((V v : ℝ) : ℂ)) ξ‖ * (1+ξ^2)
        ≤ MV * (1+ξ^2) := mul_le_mul_of_nonneg_right (hMV ξ) hden.le
      _ ≤ MV * 2 := by nlinarith [hMV0, hsmall]
      _ ≤ 2*MV + M₂/(2*Real.pi^2) := by
          have : (0:ℝ) ≤ M₂/(2*Real.pi^2) := by positivity
          linarith
  · -- away from the origin: two integrations by parts
    push_neg at hsmall
    have hξ0 : ξ ≠ 0 := by
      intro h
      rw [h] at hsmall
      norm_num at hsmall
    have hξsq : (0:ℝ) < ξ^2 := by positivity
    have hdec := fourier_pointwise_decay V hVs hVc M₂ hM₂ ξ hξ0
    have hcoef : (0:ℝ) < 4*Real.pi^2*ξ^2 := by positivity
    calc ‖𝓕 (fun v => ((V v : ℝ) : ℂ)) ξ‖ * (1+ξ^2)
        ≤ (M₂/(4*Real.pi^2*ξ^2)) * (1+ξ^2) :=
          mul_le_mul_of_nonneg_right hdec hden.le
      _ ≤ M₂/(2*Real.pi^2) := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ hcoef (by positivity)]
          nlinarith [mul_nonneg (mul_nonneg
            (by positivity : (0:ℝ) ≤ 2*Real.pi^2) hM₂0)
            (by linarith : (0:ℝ) ≤ ξ^2 - 1)]
      _ ≤ 2*MV + M₂/(2*Real.pi^2) := by linarith

/-- **Character polynomials are continuous** (Track R, N47): for any
finite index set, weights and frequencies,

  `ξ ↦ ∑_i w_i·𝐞(−s_i·ξ)`  is continuous.

Stated at the same generality as
`norm_sum_translates_le_integral_char`, whose conclusion is an integral
of exactly this shape — so the integrability side conditions of §4's
pairing estimate can be discharged directly from it, for whichever
polynomials are substituted.

The fact was previously available only as a local step inside
`HalaszAssembly`, specialised to `ℕ`-indexed sums with weights `f n/n`. -/
theorem continuous_char_poly {ι : Type*} (S : Finset ι) (w : ι → ℂ)
    (s : ι → ℝ) :
    Continuous (fun ξ : ℝ =>
      ∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)) := by
  refine continuous_finset_sum _ fun i _ => ?_
  refine Continuous.mul continuous_const ?_
  exact continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp (by fun_prop))

/-- **The trivial sup of a character polynomial** (Track R, N47):

  `‖∑_i w_i·𝐞(−s_i·ξ)‖ ≤ ∑_i ‖w_i‖`,  uniformly in `ξ`.

The characters are unimodular, so the triangle inequality is sharp at
`ξ = 0` when the weights are aligned.  This is the `B₁`/`B₂`/`B₃` input
of the pairing estimate — the crude bound that prices the tail, where no
cancellation is available. -/
theorem norm_char_poly_le_sum {ι : Type*} (S : Finset ι) (w : ι → ℂ)
    (s : ι → ℝ) (ξ : ℝ) :
    ‖∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖
      ≤ ∑ i ∈ S, ‖w i‖ := by
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  have hc : ‖((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖ = 1 := by simp
  rw [hc, mul_one]

/-- **Shifting a character polynomial** (Track R, N51):

  `∑_i w_i·𝐞(−s_i·(N+u)) = ∑_i (w_i·𝐞(−s_i·N))·𝐞(−s_i·u)`.

The frequency shift is absorbed into the coefficients, and does so
*without changing their moduli* — the characters are unimodular.

That is what lets the mean value theorem, which is stated on an interval
centred at the origin, be applied on the unit interval around any
frequency `N`: the shifted coefficients have the same `‖w_i‖`, so every
bound in terms of `∑‖w_i‖²Λ(i)` is unchanged.  GHS say this as "apply
Lemma 1 with `a_q = f(q)q^{−ih}`". -/
theorem char_poly_shift {ι : Type*} (S : Finset ι) (w : ι → ℂ) (s : ι → ℝ)
    (N u : ℝ) :
    (∑ i ∈ S, w i * ((Real.fourierChar (-(s i * (N + u))) : Circle) : ℂ))
      = ∑ i ∈ S, (w i * ((Real.fourierChar (-(s i * N)) : Circle) : ℂ))
          * ((Real.fourierChar (-(s i * u)) : Circle) : ℂ) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hadd : -(s i * (N + u)) = -(s i * N) + -(s i * u) := by ring
  rw [hadd, Real.fourierChar_apply, Real.fourierChar_apply,
    Real.fourierChar_apply]
  push_cast
  conv_rhs => rw [mul_assoc, ← Complex.exp_add]
  ring_nf

/-- **The shifted coefficients have the same moduli** (Track R, N51) —
the reason the shift is free. -/
theorem norm_shifted_coeff {ι : Type*} (w : ι → ℂ) (s : ι → ℝ) (N : ℝ)
    (i : ι) :
    ‖w i * ((Real.fourierChar (-(s i * N)) : Circle) : ℂ)‖ = ‖w i‖ := by
  rw [norm_mul]
  have hc : ‖((Real.fourierChar (-(s i * N)) : Circle) : ℂ)‖ = 1 := by simp
  rw [hc, mul_one]

/-- **Recentring a unit-interval integral** (Track R, N51):
`∫_{N−1/2}^{N+1/2} g = ∫_{−1/2}^{1/2} g(N+·)`. -/
theorem integral_unit_shift (g : ℝ → ℝ) (N : ℝ) :
    (∫ ξ in (N - 1/2)..(N + 1/2), g ξ)
      = ∫ u in (-(1:ℝ)/2)..((1:ℝ)/2), g (N + u) := by
  rw [intervalIntegral.integral_comp_add_left (fun x => g x) N]
  congr 1
  ring

/-- **A unit-interval energy is a centred one** (Track R, N52):

  `∫_{N−1/2}^{N+1/2} ‖∑ w_i·𝐞(−s_i·ξ)‖² dξ
     = ∫_{−1/2}^{1/2} ‖∑ (w_i·𝐞(−s_i·N))·𝐞(−s_i·u)‖² du`.

The mean value theorem is proved on an interval centred at the origin;
this is what lets it be used on the unit interval around any frequency
`N`.  By `norm_shifted_coeff` the shifted coefficients have the same
moduli, so any bound in terms of `∑‖w_i‖²Λ(i)` transfers verbatim — the
shift costs nothing at all.

This is the last piece needed to supply `hV` to
`integral_line_halasz_le`, which asks for a bound on
`∫_{N−1/2}^{N+1/2} ‖P₃‖²` uniformly in `N`. -/
theorem integral_unit_sq_shift {ι : Type*} (S : Finset ι) (w : ι → ℂ)
    (s : ι → ℝ) (N : ℝ) :
    (∫ ξ in (N - 1/2)..(N + 1/2),
        ‖∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖^2)
      = ∫ u in (-(1:ℝ)/2)..((1:ℝ)/2),
          ‖∑ i ∈ S, (w i * ((Real.fourierChar (-(s i * N)) : Circle) : ℂ))
            * ((Real.fourierChar (-(s i * u)) : Circle) : ℂ)‖^2 := by
  rw [integral_unit_shift (fun ξ =>
    ‖∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖^2) N]
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [char_poly_shift S w s N u]

/-- **The shift preserves the coefficient energy** (Track R, N52):
`∑ ‖w_i·𝐞(−s_i·N)‖² = ∑ ‖w_i‖²`.

The right-hand side of the mean value theorem is untouched by the
shift, which is why applying it off-centre is free. -/
theorem sum_norm_sq_shifted {ι : Type*} (S : Finset ι) (w : ι → ℂ)
    (s : ι → ℝ) (N : ℝ) :
    (∑ i ∈ S, ‖w i * ((Real.fourierChar (-(s i * N)) : Circle) : ℂ)‖^2)
      = ∑ i ∈ S, ‖w i‖^2 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_shifted_coeff w s N i]

/-- **A centred energy bound holds at every frequency** (Track R, N53):
if

  `∫_{−1/2}^{1/2} ‖∑ w'_i·𝐞(−s_i·u)‖² du ≤ V`

for *every* coefficient vector `w'` with the same moduli as `w`, then

  `∫_{N−1/2}^{N+1/2} ‖∑ w_i·𝐞(−s_i·ξ)‖² dξ ≤ V`  for every `N`.

This is the form `integral_line_halasz_le` consumes: it asks for a
uniform bound on the energy of `P₃` over the unit interval around each
frequency of the Halász range, and the mean value theorem supplies one
only at the origin.

Quantifying over all `w'` of equal modulus is exactly right, and is not
a weakening: every mean value theorem for Dirichlet polynomials bounds
the energy by `∑‖w_i‖²Λ(i)`, which depends on the coefficients only
through their moduli.  So a hypothesis in this shape is no harder to
supply than the centred bound itself, and it makes the transfer to
arbitrary `N` immediate. -/
theorem integral_unit_sq_le_of_centred {ι : Type*} (S : Finset ι)
    (w : ι → ℂ) (s : ι → ℝ) (V : ℝ)
    (hcen : ∀ w' : ι → ℂ, (∀ i, ‖w' i‖ = ‖w i‖) →
      (∫ u in (-(1:ℝ)/2)..((1:ℝ)/2),
        ‖∑ i ∈ S, w' i * ((Real.fourierChar (-(s i * u)) : Circle) : ℂ)‖^2)
        ≤ V)
    (N : ℝ) :
    (∫ ξ in (N - 1/2)..(N + 1/2),
      ‖∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖^2)
      ≤ V := by
  rw [integral_unit_sq_shift S w s N]
  exact hcen (fun i => w i * ((Real.fourierChar (-(s i * N)) : Circle) : ℂ))
    (fun i => norm_shifted_coeff w s N i)

/-- **The window transform tail** (Track R, M2-i1c): a smooth compactly
supported real window with second-derivative mass `M₂` has transform
tail `∫_{|ξ|>L} ‖𝓕V‖ ≤ M₂/(2π²L)` — two integrations by parts against
the explicit `ξ⁻²`-tail. -/
theorem fourier_tail_le (V : ℝ → ℝ) (hVs : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (M₂ : ℝ)
    (hM₂ : ∫ v, |iteratedDeriv 2 V v| ≤ M₂) (L : ℝ) (hL : 0 < L) :
    ∫ ξ in {ξ : ℝ | L < |ξ|}, ‖𝓕 (fun v => ((V v : ℝ) : ℂ)) ξ‖
      ≤ M₂/(2*Real.pi^2*L) := by
  classical
  set Vc : ℝ → ℂ := fun v => ((V v : ℝ) : ℂ) with hVc_def
  have hVcs : ContDiff ℝ ∞ Vc := Complex.ofRealCLM.contDiff.comp hVs
  have hVcc : HasCompactSupport Vc :=
    HasCompactSupport.comp_left hVc Complex.ofReal_zero
  have hM₂0 : 0 ≤ M₂ :=
    le_trans (integral_nonneg fun v => abs_nonneg _) hM₂
  -- the iterated-derivative integrabilities
  have haux : ∀ n : ℕ, ContDiff ℝ ∞ (iteratedDeriv n Vc)
      ∧ HasCompactSupport (iteratedDeriv n Vc) := by
    intro n
    induction n with
    | zero =>
      rw [iteratedDeriv_zero]
      exact ⟨hVcs, hVcc⟩
    | succ k ih =>
      rw [iteratedDeriv_succ]
      refine ⟨?_, ih.2.deriv⟩
      simpa using ih.1.iterate_deriv 1
  have hint : ∀ n : ℕ, Integrable (iteratedDeriv n Vc) := fun n =>
    ((haux n).1.continuous).integrable_of_hasCompactSupport (haux n).2
  -- pointwise decay from two integrations by parts
  have hFI := Real.fourier_iteratedDeriv (f := Vc) (N := (2:ℕ∞))
    (hVcs.of_le (by exact_mod_cast le_top)) (fun n _ => hint n) (le_refl _)
  have hpt : ∀ ξ : ℝ, ξ ≠ 0 →
      ‖𝓕 Vc ξ‖ ≤ M₂/(4*Real.pi^2*ξ^2) := by
    intro ξ hξ
    have h1 := congrFun hFI ξ
    have hnorm2 : ‖((2*Real.pi*Complex.I*(ξ:ℂ))^2 : ℂ)‖
        = 4*Real.pi^2*ξ^2 := by
      rw [norm_pow]
      rw [show (2*Real.pi*Complex.I*(ξ:ℂ))
          = (((2*Real.pi*ξ : ℝ)):ℂ) * Complex.I from by push_cast; ring]
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, sq_abs]
      ring
    have h2 : ‖𝓕 (iteratedDeriv 2 Vc) ξ‖ = 4*Real.pi^2*ξ^2 * ‖𝓕 Vc ξ‖ := by
      rw [h1, norm_smul, hnorm2]
    have h3 : ‖𝓕 (iteratedDeriv 2 Vc) ξ‖ ≤ M₂ := by
      refine le_trans (VectorFourier.norm_fourierIntegral_le_integral_norm
        _ _ _ _ _) ?_
      rw [iteratedDeriv_two_ofReal V hVs]
      refine le_trans (le_of_eq ?_) hM₂
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      dsimp only
      rw [Complex.norm_real, Real.norm_eq_abs]
    have h4 : (0:ℝ) < 4*Real.pi^2*ξ^2 := by
      have := Real.pi_pos
      have hξ2 : (0:ℝ) < ξ^2 := by positivity
      positivity
    rw [le_div_iff₀ h4]
    calc ‖𝓕 Vc ξ‖ * (4*Real.pi^2*ξ^2)
        = 4*Real.pi^2*ξ^2 * ‖𝓕 Vc ξ‖ := by ring
      _ = ‖𝓕 (iteratedDeriv 2 Vc) ξ‖ := h2.symm
      _ ≤ M₂ := h3
  -- integrate the tail
  have hset : {ξ : ℝ | L < |ξ|} = Set.Iio (-L) ∪ Set.Ioi L := by
    ext ξ
    rw [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi,
      lt_abs]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
  -- Schwartz integrability of the transform norm
  set G : SchwartzMap ℝ ℂ := hVcc.toSchwartzMap hVcs with hG_def
  have hFeq : ∀ ξ, ‖𝓕 Vc ξ‖ = ‖(𝓕 G) ξ‖ := fun _ => rfl
  have hFint : Integrable (fun ξ => ‖𝓕 Vc ξ‖) := by
    simp only [hFeq]
    exact (𝓕 G).integrable.norm
  -- the ξ⁻²-integral over Ioi L
  have hIoi : ∫ ξ in Set.Ioi L, M₂/(4*Real.pi^2*ξ^2) = M₂/(4*Real.pi^2*L) := by
    have h1 : ∀ ξ ∈ Set.Ioi L, M₂/(4*Real.pi^2*ξ^2)
        = M₂/(4*Real.pi^2) * ξ^((-2:ℝ)) := by
      intro ξ hξ
      rw [Set.mem_Ioi] at hξ
      have hξ0 : (0:ℝ) < ξ := lt_trans hL hξ
      have hval : ξ^((-2):ℝ) = 1/ξ^2 := by
        rw [show ((-2):ℝ) = -((2:ℕ):ℝ) from by push_cast; ring,
          Real.rpow_neg hξ0.le, Real.rpow_natCast, one_div]
      rw [hval]
      field_simp
    rw [setIntegral_congr_fun measurableSet_Ioi h1, integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num) hL]
    rw [show (-2:ℝ) + 1 = -1 from by norm_num,
      Real.rpow_neg_one]
    field_simp
  -- reflection: Iio(−L)-integrals become Ioi L-integrals
  have hflip : ∀ (g : ℝ → ℝ),
      (∫ ξ, Set.indicator (Set.Iio (-L)) g ξ)
        = ∫ ξ, Set.indicator (Set.Ioi L) (fun ξ => g (-ξ)) ξ := by
    intro g
    rw [← integral_neg_eq_self
      (f := Set.indicator (Set.Iio (-L)) g)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    dsimp only
    by_cases h : L < ξ
    · rw [Set.indicator_of_mem (show -ξ ∈ Set.Iio (-L) from by
        rw [Set.mem_Iio]
        linarith)]
      rw [Set.indicator_of_mem (Set.mem_Ioi.mpr h)]
    · rw [Set.indicator_of_notMem (show -ξ ∉ Set.Iio (-L) from by
        rw [Set.mem_Iio]
        push_neg
        linarith)]
      rw [Set.indicator_of_notMem (show ξ ∉ Set.Ioi L from by
        rw [Set.mem_Ioi]
        exact h)]
  -- majorant integrability on the right half
  have hmaj_Ioi : IntegrableOn (fun ξ => M₂/(4*Real.pi^2*ξ^2))
      (Set.Ioi L) := by
    have h1 := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1)
      hL).const_mul (M₂/(4*Real.pi^2))
    refine MeasureTheory.IntegrableOn.congr_fun h1
      (fun ξ hξ => ?_) measurableSet_Ioi
    rw [Set.mem_Ioi] at hξ
    have hξ0 : (0:ℝ) < ξ := lt_trans hL hξ
    have hval : ξ^((-2):ℝ) = 1/ξ^2 := by
      rw [show ((-2):ℝ) = -((2:ℕ):ℝ) from by push_cast; ring,
        Real.rpow_neg hξ0.le, Real.rpow_natCast, one_div]
    rw [hval]
    field_simp
  -- the right-half bound
  have hIoi_bound : ∫ ξ in Set.Ioi L, ‖𝓕 Vc ξ‖ ≤ M₂/(4*Real.pi^2*L) := by
    refine le_trans (setIntegral_mono_on hFint.integrableOn hmaj_Ioi
      measurableSet_Ioi ?_) (le_of_eq hIoi)
    intro ξ hξ
    rw [Set.mem_Ioi] at hξ
    exact hpt ξ (ne_of_gt (lt_trans hL hξ))
  -- the left-half bound via reflection
  have hIio_bound : ∫ ξ in Set.Iio (-L), ‖𝓕 Vc ξ‖ ≤ M₂/(4*Real.pi^2*L) := by
    rw [← integral_indicator measurableSet_Iio,
      hflip (fun ξ => ‖𝓕 Vc ξ‖), integral_indicator measurableSet_Ioi]
    have hmono : ∫ ξ in Set.Ioi L, ‖𝓕 Vc (-ξ)‖
        ≤ ∫ ξ in Set.Ioi L, M₂/(4*Real.pi^2*ξ^2) := by
      have hptneg : ∀ ξ ∈ Set.Ioi L, ‖𝓕 Vc (-ξ)‖ ≤ M₂/(4*Real.pi^2*ξ^2) := by
        intro ξ hξ
        rw [Set.mem_Ioi] at hξ
        have hξ0 : (0:ℝ) < ξ := lt_trans hL hξ
        have := hpt (-ξ) (by
          intro h
          rw [neg_eq_zero] at h
          linarith)
        rwa [neg_sq] at this
      refine setIntegral_mono_on ?_ hmaj_Ioi measurableSet_Ioi hptneg
      refine hmaj_Ioi.mono' ?_ ?_
      · refine Continuous.aestronglyMeasurable ?_ |>.restrict
        simp only [hFeq]
        exact ((𝓕 G).continuous.norm).comp continuous_neg
      · refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
        refine Filter.Eventually.of_forall fun ξ hξ => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact hptneg ξ hξ
    exact le_trans hmono (le_of_eq hIoi)
  -- combine
  rw [hset]
  have hdisj : Disjoint (Set.Iio (-L)) (Set.Ioi L) := by
    refine Set.disjoint_left.mpr fun ξ h1 h2 => ?_
    rw [Set.mem_Iio] at h1
    rw [Set.mem_Ioi] at h2
    linarith
  rw [setIntegral_union hdisj measurableSet_Ioi
    hFint.integrableOn hFint.integrableOn]
  have hval : M₂/(4*Real.pi^2*L) + M₂/(4*Real.pi^2*L) = M₂/(2*Real.pi^2*L) := by
    field_simp
    ring
  linarith [hIoi_bound, hIio_bound, hval]


set_option maxHeartbeats 1600000 in
/-- **The Perron sandwich** (Track R, M2-i2): the window-weighted sum
reproduces the normalized Cesàro mean up to the edge budget
`2ρ + 2/x` — the plateau weights are exactly `1/x`, the edge carries
at most `ρx + 1` terms of size `2/x`, and everything beyond `x`
vanishes. -/
theorem perron_sandwich (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (V : ℝ → ℝ) (ρ : ℝ) (x : ℕ) (hx : 4 ≤ x) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hVplat : ∀ v, ρ ≤ v → v ≤ 2*Real.log x + 1 → V v = Real.exp (-v))
    (hV0 : ∀ v, v ≤ 0 → V v = 0)
    (hVle : ∀ v, V v ≤ Real.exp (-v)) (hVnn : ∀ v, 0 ≤ V v)
    (S : Finset ℕ) (hS : Finset.Icc 1 x ⊆ S) (hS1 : ∀ n ∈ S, 1 ≤ n) :
    ‖(∑ n ∈ S, (g n/(n:ℂ))
          * ((V (Real.log x - Real.log n) : ℝ) : ℂ))
        - (∑ n ∈ Finset.Icc 1 x, g n)/(x:ℂ)‖
      ≤ 2*ρ + 2/(x:ℝ) := by
  classical
  have hx0 : (0:ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hlogx : (0:ℝ) ≤ Real.log x :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
  -- terms beyond x vanish
  have hbeyond : ∀ n ∈ S \ Finset.Icc 1 x,
      (g n/(n:ℂ)) * ((V (Real.log x - Real.log n) : ℝ) : ℂ) = 0 := by
    intro n hn
    rw [Finset.mem_sdiff, Finset.mem_Icc] at hn
    have h1 := hS1 n hn.1
    have hnx : x < n := by omega
    have hlog : Real.log x - Real.log n ≤ 0 := by
      have := Real.log_le_log hx0 (by exact_mod_cast hnx.le : (x:ℝ) ≤ n)
      linarith
    rw [hV0 _ hlog]
    simp
  have hsum_eq : ∑ n ∈ S, (g n/(n:ℂ))
        * ((V (Real.log x - Real.log n) : ℝ) : ℂ)
      = ∑ n ∈ Finset.Icc 1 x, (g n/(n:ℂ))
        * ((V (Real.log x - Real.log n) : ℝ) : ℂ) := by
    rw [← Finset.sum_sdiff hS]
    rw [Finset.sum_congr rfl hbeyond, Finset.sum_const_zero, zero_add]
  rw [hsum_eq]
  -- rewrite the Cesàro side as a sum of 1/x-weights
  have hces : (∑ n ∈ Finset.Icc 1 x, g n)/(x:ℂ)
      = ∑ n ∈ Finset.Icc 1 x, g n/(x:ℂ) := by
    rw [Finset.sum_div]
  rw [hces, ← Finset.sum_sub_distrib]
  -- split at the plateau threshold
  set P : ℕ → Prop := fun n => (n:ℝ) ≤ (x:ℝ)*Real.exp (-ρ) with hP_def
  have hplat_exact : ∀ n ∈ (Finset.Icc 1 x).filter (fun n => P n),
      (g n/(n:ℂ)) * ((V (Real.log x - Real.log n) : ℝ) : ℂ) - g n/(x:ℂ)
        = 0 := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    have hn1 : 1 ≤ n := hn.1.1
    have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn1
    have hv1 : ρ ≤ Real.log x - Real.log n := by
      have h2 : Real.log n ≤ Real.log ((x:ℝ)*Real.exp (-ρ)) :=
        Real.log_le_log (by linarith) hn.2
      rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',
        Real.log_exp] at h2
      linarith
    have hv2 : Real.log x - Real.log n ≤ 2*Real.log x + 1 := by
      have := Real.log_nonneg hnr
      linarith
    rw [hVplat _ hv1 hv2]
    have hexp : Real.exp (-(Real.log x - Real.log n)) = (n:ℝ)/(x:ℝ) := by
      rw [neg_sub, Real.exp_sub, Real.exp_log (by linarith),
        Real.exp_log hx0]
    rw [hexp]
    have hn0 : (n:ℂ) ≠ 0 := by
      exact_mod_cast (by omega : n ≠ 0)
    have hx0' : (x:ℂ) ≠ 0 := by
      exact_mod_cast (by omega : x ≠ 0)
    push_cast
    field_simp
    ring
  -- the edge terms
  have hedge_bound : ∀ n ∈ (Finset.Icc 1 x).filter (fun n => ¬ P n),
      ‖(g n/(n:ℂ)) * ((V (Real.log x - Real.log n) : ℝ) : ℂ) - g n/(x:ℂ)‖
        ≤ 2/(x:ℝ) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    have hn1 : 1 ≤ n := hn.1.1
    have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn1
    have hnx : (n:ℝ) ≤ x := by exact_mod_cast hn.1.2
    refine le_trans (norm_sub_le _ _) ?_
    have h1 : ‖(g n/(n:ℂ)) * ((V (Real.log x - Real.log n) : ℝ) : ℂ)‖
        ≤ 1/(x:ℝ) := by
      rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hVnn _)]
      have hV1 : V (Real.log x - Real.log n) ≤ (n:ℝ)/(x:ℝ) := by
        refine le_trans (hVle _) (le_of_eq ?_)
        rw [neg_sub, Real.exp_sub, Real.exp_log (by linarith),
          Real.exp_log hx0]
      calc ‖g n‖/(n:ℝ) * V (Real.log x - Real.log n)
          ≤ 1/(n:ℝ) * ((n:ℝ)/(x:ℝ)) := by
            refine mul_le_mul ?_ hV1 (hVnn _) (by positivity)
            exact div_le_div_of_nonneg_right (hg n) (by linarith)
        _ = 1/(x:ℝ) := by
            field_simp
    have h2 : ‖g n/(x:ℂ)‖ ≤ 1/(x:ℝ) := by
      rw [norm_div, Complex.norm_natCast]
      exact div_le_div_of_nonneg_right (hg n) hx0.le
    have hsum : 1/(x:ℝ) + 1/(x:ℝ) = 2/(x:ℝ) := by ring
    linarith
  -- the edge count
  have hedge_card : (((Finset.Icc 1 x).filter (fun n => ¬ P n)).card : ℝ)
      ≤ ρ*(x:ℝ) + 1 := by
    set m₀ : ℕ := ⌊(x:ℝ)*Real.exp (-ρ)⌋₊ with hm₀_def
    have hsub : (Finset.Icc 1 x).filter (fun n => ¬ P n)
        ⊆ Finset.Icc (m₀+1) x := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      rw [Finset.mem_Icc]
      refine ⟨?_, hn.1.2⟩
      have h1 : ¬((n:ℝ) ≤ (x:ℝ)*Real.exp (-ρ)) := hn.2
      push_neg at h1
      have h2 : m₀ < n := by
        rw [hm₀_def]
        exact (Nat.floor_lt (by positivity)).mpr h1
      omega
    have hm₀x : m₀ ≤ x := by
      rw [hm₀_def]
      have h1 : (x:ℝ)*Real.exp (-ρ) ≤ x := by
        have := Real.exp_le_one_iff.mpr (by linarith : -ρ ≤ 0)
        nlinarith
      calc ⌊(x:ℝ)*Real.exp (-ρ)⌋₊ ≤ ⌊(x:ℝ)⌋₊ := Nat.floor_le_floor h1
        _ = x := Nat.floor_natCast x
    have hm₀low : (x:ℝ)*Real.exp (-ρ) - 1 < m₀ := by
      rw [hm₀_def]
      exact Nat.sub_one_lt_floor _
    calc (((Finset.Icc 1 x).filter (fun n => ¬ P n)).card : ℝ)
        ≤ ((Finset.Icc (m₀+1) x).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ = ((x - m₀ : ℕ) : ℝ) := by
          rw [Nat.card_Icc]
          congr 1
          omega
      _ ≤ (x:ℝ) - ((x:ℝ)*Real.exp (-ρ) - 1) := by
          rw [Nat.cast_sub hm₀x]
          linarith [hm₀low]
      _ ≤ ρ*(x:ℝ) + 1 := by
          have hexp : 1 - ρ ≤ Real.exp (-ρ) := by
            have := Real.add_one_le_exp (-ρ)
            linarith
          nlinarith
  -- assemble
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 x)
    (fun n => P n)]
  rw [Finset.sum_congr rfl hplat_exact, Finset.sum_const_zero, zero_add]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ (2/(x:ℝ)) hedge_bound) ?_
  rw [nsmul_eq_mul]
  calc (((Finset.Icc 1 x).filter (fun n => ¬ P n)).card : ℝ) * (2/(x:ℝ))
      ≤ (ρ*(x:ℝ) + 1) * (2/(x:ℝ)) :=
        mul_le_mul_of_nonneg_right hedge_card (by positivity)
    _ = 2*ρ + 2/(x:ℝ) := by
        field_simp

set_option maxHeartbeats 1600000 in
/-- **The band/tail Hölder split** (Track R, M2-i3): the `L¹` pairing
of a triple-product polynomial with a window transform splits into the
band — where one factor is sup-bounded and the other two meet by
parametrized AM-GM — and the tail, priced by the transform's tail
mass. The free parameter `t` is the Cauchy–Schwarz optimizer, chosen
at tuning time. -/
theorem pairing_band_tail_split (P₁ P₂ P₃ : ℝ → ℂ)
    (hc₁ : Continuous P₁) (hc₂ : Continuous P₂) (hc₃ : Continuous P₃)
    (F : ℝ → ℂ) (hFc : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (L t B₁ B₂ B₃ Bband MV E₂ E₃ Mtail : ℝ)
    (hL : 0 < L) (ht : 0 < t) (hMV0 : 0 ≤ MV) (hBb0 : 0 ≤ Bband)
    (hB₂0 : 0 ≤ B₂) (hB₃0 : 0 ≤ B₃)
    (hB₁ : ∀ ξ, ‖P₁ ξ‖ ≤ B₁) (hB₂ : ∀ ξ, ‖P₂ ξ‖ ≤ B₂)
    (hB₃ : ∀ ξ, ‖P₃ ξ‖ ≤ B₃)
    (hBband : ∀ ξ, |ξ| ≤ L → ‖P₁ ξ‖ ≤ Bband)
    (hE₂ : ∫ ξ in (-L)..L, ‖P₂ ξ‖^2 ≤ E₂)
    (hE₃ : ∫ ξ in (-L)..L, ‖P₃ ξ‖^2 ≤ E₃)
    (hMV : ∀ ξ, ‖𝓕 F ξ‖ ≤ MV)
    (hMtail : ∫ ξ in {ξ : ℝ | L < |ξ|}, ‖𝓕 F ξ‖ ≤ Mtail) :
    ∫ ξ, ‖P₁ ξ * P₂ ξ * P₃ ξ‖ * ‖𝓕 F ξ‖
      ≤ MV * Bband * (t*E₂ + E₃/t)/2 + B₁*B₂*B₃*Mtail := by
  classical
  have hB₁0 : 0 ≤ B₁ := le_trans (norm_nonneg _) (hB₁ 0)
  -- Schwartz integrability of the window transform
  set G : SchwartzMap ℝ ℂ := hFc.toSchwartzMap hFs with hG_def
  have hFeq : ∀ ξ, ‖𝓕 F ξ‖ = ‖(𝓕 G) ξ‖ := fun _ => rfl
  have hFhat_int : Integrable (fun ξ => ‖𝓕 F ξ‖) := by
    simp only [hFeq]
    exact (𝓕 G).integrable.norm
  have hcont_int : Continuous fun ξ => ‖P₁ ξ * P₂ ξ * P₃ ξ‖ * ‖𝓕 F ξ‖ := by
    have h1 : Continuous fun ξ => ‖𝓕 F ξ‖ := by
      simp only [hFeq]
      exact (𝓕 G).continuous.norm
    exact (((hc₁.mul hc₂).mul hc₃).norm).mul h1
  have hint : Integrable (fun ξ => ‖P₁ ξ * P₂ ξ * P₃ ξ‖ * ‖𝓕 F ξ‖) := by
    refine (hFhat_int.const_mul (B₁*B₂*B₃)).mono'
      hcont_int.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ξ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (hB₁ ξ) (hB₂ ξ)
      (norm_nonneg _) hB₁0) (hB₃ ξ) (norm_nonneg _)
      (mul_nonneg hB₁0 hB₂0)
  -- split at the band
  set s : Set ℝ := {ξ : ℝ | |ξ| ≤ L} with hs_def
  have hs_meas : MeasurableSet s := by
    rw [hs_def]
    exact measurableSet_le (continuous_abs.measurable) measurable_const
  have hsplit : ∫ ξ, ‖P₁ ξ * P₂ ξ * P₃ ξ‖ * ‖𝓕 F ξ‖
      = (∫ ξ in s, ‖P₁ ξ * P₂ ξ * P₃ ξ‖ * ‖𝓕 F ξ‖)
        + ∫ ξ in sᶜ, ‖P₁ ξ * P₂ ξ * P₃ ξ‖ * ‖𝓕 F ξ‖ :=
    (integral_add_compl hs_meas hint).symm
  rw [hsplit]
  -- the tail part
  have hcompl : sᶜ = {ξ : ℝ | L < |ξ|} := by
    rw [hs_def]
    ext ξ
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  have htail : ∫ ξ in sᶜ, ‖P₁ ξ * P₂ ξ * P₃ ξ‖ * ‖𝓕 F ξ‖
      ≤ B₁*B₂*B₃*Mtail := by
    rw [hcompl]
    have hmono : ∫ ξ in {ξ : ℝ | L < |ξ|}, ‖P₁ ξ * P₂ ξ * P₃ ξ‖ * ‖𝓕 F ξ‖
        ≤ ∫ ξ in {ξ : ℝ | L < |ξ|}, (B₁*B₂*B₃) * ‖𝓕 F ξ‖ := by
      refine setIntegral_mono_on hint.integrableOn
        ((hFhat_int.const_mul _).integrableOn) ?_ ?_
      · rw [← hcompl]
        exact hs_meas.compl
      · intro ξ _
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [norm_mul, norm_mul]
        refine mul_le_mul (mul_le_mul (hB₁ ξ) (hB₂ ξ)
          (norm_nonneg _) hB₁0) (hB₃ ξ) (norm_nonneg _) ?_
        exact mul_nonneg hB₁0 hB₂0
    refine le_trans hmono ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left hMtail ?_
    exact mul_nonneg (mul_nonneg hB₁0 hB₂0) hB₃0
  -- the band part
  have hband : ∫ ξ in s, ‖P₁ ξ * P₂ ξ * P₃ ξ‖ * ‖𝓕 F ξ‖
      ≤ MV * Bband * (t*E₂ + E₃/t)/2 := by
    have hpt : ∀ ξ ∈ s, ‖P₁ ξ * P₂ ξ * P₃ ξ‖ * ‖𝓕 F ξ‖
        ≤ MV * Bband * ((t*‖P₂ ξ‖^2 + ‖P₃ ξ‖^2/t)/2) := by
      intro ξ hξ
      rw [hs_def, Set.mem_setOf_eq] at hξ
      have hamgm : ‖P₂ ξ‖ * ‖P₃ ξ‖ ≤ (t*‖P₂ ξ‖^2 + ‖P₃ ξ‖^2/t)/2 := by
        have hst : Real.sqrt t > 0 := Real.sqrt_pos.mpr ht
        have key := two_mul_le_add_sq (Real.sqrt t * ‖P₂ ξ‖)
          (‖P₃ ξ‖/Real.sqrt t)
        have hxy : (Real.sqrt t * ‖P₂ ξ‖) * (‖P₃ ξ‖/Real.sqrt t)
            = ‖P₂ ξ‖*‖P₃ ξ‖ := by
          field_simp
        have hx2 : (Real.sqrt t * ‖P₂ ξ‖)^2 = t*‖P₂ ξ‖^2 := by
          rw [mul_pow, Real.sq_sqrt ht.le]
        have hy2 : (‖P₃ ξ‖/Real.sqrt t)^2 = ‖P₃ ξ‖^2/t := by
          rw [div_pow, Real.sq_sqrt ht.le]
        have key2 : 2 * (‖P₂ ξ‖ * ‖P₃ ξ‖) ≤ t*‖P₂ ξ‖^2 + ‖P₃ ξ‖^2/t := by
          calc 2 * (‖P₂ ξ‖ * ‖P₃ ξ‖)
              = 2 * (Real.sqrt t * ‖P₂ ξ‖) * (‖P₃ ξ‖ / Real.sqrt t) := by
                rw [← hxy]
                ring
            _ ≤ (Real.sqrt t * ‖P₂ ξ‖)^2 + (‖P₃ ξ‖ / Real.sqrt t)^2 := key
            _ = t*‖P₂ ξ‖^2 + ‖P₃ ξ‖^2/t := by rw [hx2, hy2]
        linarith
      calc ‖P₁ ξ * P₂ ξ * P₃ ξ‖ * ‖𝓕 F ξ‖
          = (‖P₁ ξ‖ * (‖P₂ ξ‖ * ‖P₃ ξ‖)) * ‖𝓕 F ξ‖ := by
            rw [norm_mul, norm_mul]
            ring
        _ ≤ (Bband * ((t*‖P₂ ξ‖^2 + ‖P₃ ξ‖^2/t)/2)) * MV := by
            refine mul_le_mul ?_ (hMV ξ) (norm_nonneg _) ?_
            · refine mul_le_mul (hBband ξ hξ) hamgm
                (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hBb0
            · refine mul_nonneg hBb0 ?_
              have h2 : 0 ≤ t*‖P₂ ξ‖^2 := by positivity
              have h3 : 0 ≤ ‖P₃ ξ‖^2/t := by positivity
              linarith
        _ = MV * Bband * ((t*‖P₂ ξ‖^2 + ‖P₃ ξ‖^2/t)/2) := by ring
    have hs_icc : s = Set.Icc (-L) L := by
      rw [hs_def]
      ext ξ
      rw [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
    have hint₂ : IntegrableOn (fun ξ => ‖P₂ ξ‖^2) s := by
      rw [hs_icc]
      exact ((hc₂.norm.pow 2).continuousOn).integrableOn_compact isCompact_Icc
    have hint₃ : IntegrableOn (fun ξ => ‖P₃ ξ‖^2) s := by
      rw [hs_icc]
      exact ((hc₃.norm.pow 2).continuousOn).integrableOn_compact isCompact_Icc
    have hRint : IntegrableOn
        (fun ξ => MV * Bband * ((t*‖P₂ ξ‖^2 + ‖P₃ ξ‖^2/t)/2)) s := by
      exact (((hint₂.const_mul t).add (hint₃.div_const t)).div_const 2
        ).const_mul (MV*Bband)
    have hstep := setIntegral_mono_on hint.integrableOn hRint hs_meas hpt
    refine le_trans hstep ?_
    rw [integral_const_mul]
    have hlin : ∫ ξ in s, (t*‖P₂ ξ‖^2 + ‖P₃ ξ‖^2/t)/2
        = (t * (∫ ξ in s, ‖P₂ ξ‖^2) + (∫ ξ in s, ‖P₃ ξ‖^2)/t)/2 := by
      rw [integral_div, integral_add (hint₂.const_mul t) (hint₃.div_const t),
        integral_const_mul, integral_div]
    rw [hlin]
    have hconv₂ : ∫ ξ in s, ‖P₂ ξ‖^2 = ∫ ξ in (-L)..L, ‖P₂ ξ‖^2 := by
      rw [hs_icc, intervalIntegral.integral_of_le (by linarith : -L ≤ L),
        ← integral_Icc_eq_integral_Ioc]
    have hconv₃ : ∫ ξ in s, ‖P₃ ξ‖^2 = ∫ ξ in (-L)..L, ‖P₃ ξ‖^2 := by
      rw [hs_icc, intervalIntegral.integral_of_le (by linarith : -L ≤ L),
        ← integral_Icc_eq_integral_Ioc]
    rw [hconv₂, hconv₃]
    have hMB : 0 ≤ MV * Bband := mul_nonneg hMV0 hBb0
    have h2 : (∫ ξ in (-L)..L, ‖P₂ ξ‖^2) ≤ E₂ := hE₂
    have h3 : (∫ ξ in (-L)..L, ‖P₃ ξ‖^2)/t ≤ E₃/t :=
      div_le_div_of_nonneg_right hE₃ ht.le
    have hcomb : (t * (∫ ξ in (-L)..L, ‖P₂ ξ‖^2)
          + (∫ ξ in (-L)..L, ‖P₃ ξ‖^2)/t)/2
        ≤ (t*E₂ + E₃/t)/2 := by
      have := mul_le_mul_of_nonneg_left h2 ht.le
      linarith
    calc MV * Bband * ((t * (∫ ξ in (-L)..L, ‖P₂ ξ‖^2)
          + (∫ ξ in (-L)..L, ‖P₃ ξ‖^2)/t)/2)
        ≤ MV * Bband * ((t*E₂ + E₃/t)/2) :=
          mul_le_mul_of_nonneg_left hcomb hMB
      _ = MV * Bband * (t*E₂ + E₃/t)/2 := by ring
  linarith [htail, hband]

/-- **The window transform sup bound** (Track R, M2-i4b): the Fourier
transform of a Perron window — nonnegative, vanishing on the negative
axis, dominated by `e^{-v}` — is bounded by `1` in sup norm. This is
the `MV`-instance of the band/tail Hölder split. -/
theorem norm_fourier_window_le_one (V : ℝ → ℝ)
    (hVcont : Continuous V) (hVsupp : HasCompactSupport V)
    (hV0 : ∀ v, v ≤ 0 → V v = 0)
    (hVpos : ∀ v, 0 ≤ V v) (hVexp : ∀ v, V v ≤ Real.exp (-v)) (ξ : ℝ) :
    ‖𝓕 (fun v => ((V v : ℝ) : ℂ)) ξ‖ ≤ 1 := by
  refine le_trans
    (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _) ?_
  have hnorm : ∀ v, ‖((V v : ℝ) : ℂ)‖ = V v := fun v => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hVpos v)]
  have hVint : Integrable V := hVcont.integrable_of_hasCompactSupport hVsupp
  have hexpint : IntegrableOn (fun v : ℝ => Real.exp (-v)) (Set.Ioi 0) := by
    refine MeasureTheory.IntegrableOn.congr_fun
      (exp_neg_integrableOn_Ioi 0 (by norm_num : (0:ℝ) < 1)) ?_
      measurableSet_Ioi
    intro v _
    norm_num
  calc ∫ v, ‖((V v : ℝ) : ℂ)‖
      = ∫ v, V v := by
        exact integral_congr_ae (Filter.Eventually.of_forall hnorm)
    _ = ∫ v in Set.Ioi 0, V v := by
        refine (setIntegral_eq_integral_of_forall_compl_eq_zero
          fun v hv => ?_).symm
        simp only [Set.mem_Ioi, not_lt] at hv
        exact hV0 v hv
    _ ≤ ∫ v in Set.Ioi 0, Real.exp (-v) := by
        refine setIntegral_mono_on hVint.integrableOn hexpint
          measurableSet_Ioi fun v _ => hVexp v
    _ = 1 := integral_exp_neg_Ioi_zero

/-- **The trivial phase-polynomial sup** (Track R, M2-i4b): a
`1/n`-weighted phase polynomial is bounded everywhere by its harmonic
mass — the `B`-instances of the band/tail Hölder split. -/
theorem norm_char_poly_le_harmonic (S : Finset ℕ) (w : ℕ → ℂ)
    (hw : ∀ n ∈ S, ‖w n‖ ≤ 1/(n:ℝ)) (a : ℕ → ℝ) (ξ : ℝ) :
    ‖∑ n ∈ S, w n * ((Real.fourierChar (-(a n * ξ)) : Circle) : ℂ)‖
      ≤ ∑ n ∈ S, (1:ℝ)/n := by
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n hn => ?_)
  rw [norm_mul]
  have hc : ‖((Real.fourierChar (-(a n * ξ)) : Circle) : ℂ)‖ = 1 := by
    simp
  rw [hc, mul_one]
  exact hw n hn

/-- **The crude harmonic bound** (Track R, M2-i4b): the harmonic sum
up to `N` is at most `log N + 1` — the `H`-instance for the large
class, where no smoothness structure is available. -/
theorem sum_one_div_Icc_le_log (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (1:ℝ)/n ≤ Real.log N + 1 := by
  induction N with
  | zero => omega
  | succ k ih =>
    by_cases hk : 1 ≤ k
    · rw [show k + 1 = k + 1 from rfl, Finset.sum_Icc_succ_top (by omega)]
      have hk0 : (0:ℝ) < k := by exact_mod_cast hk
      have hstep : (1:ℝ)/(k+1) ≤ Real.log (k+1) - Real.log k := by
        have hexp : (1:ℝ) - 1/(k+1) ≤ Real.exp (-(1/(k+1))) := by
          have := Real.add_one_le_exp (-(1/((k:ℝ)+1)))
          linarith
        have hfrac : (k:ℝ)/(k+1) ≤ Real.exp (-(1/(k+1))) := by
          have h1 : (k:ℝ)/(k+1) = 1 - 1/(k+1) := by
            field_simp
            ring
          linarith [hexp, h1.le, h1.ge]
        have hlog : Real.log ((k:ℝ)/(k+1)) ≤ -(1/(k+1)) := by
          calc Real.log ((k:ℝ)/(k+1))
              ≤ Real.log (Real.exp (-(1/(k+1)))) :=
                Real.log_le_log (by positivity) hfrac
            _ = -(1/(k+1)) := Real.log_exp _
        rw [Real.log_div (by positivity) (by positivity)] at hlog
        push_cast
        linarith
      push_cast
      push_cast at ih hstep
      linarith [ih hk]
    · have hk0 : k = 0 := by omega
      subst hk0
      norm_num

/-- **The abscissa shift of a window sum** (Track R, M0-c): damping the
window by `e^{−αv}` moves the coefficients from the `1`-line to the
`1+α`-line, at the price of the explicit factor `x^α`:

`∑ₙ (f n/n)·V(log x − log n) = x^α · ∑ₙ (f n/n^{1+α})·(e^{−αv}V(v))`.

The window keeps its support, so the sum stays truncated at `n ≤ x`;
only the abscissa moves.  This is the bridge that lets the shipped
Perron-window machinery, which lives on the `1`-line, be priced by
L-series bounds on shifted lines — where the pretentious distance is
available (`norm_LSeries_le_log_mul_exp`). -/
theorem window_sum_abscissa_shift (f : ℕ → ℂ) (V : ℝ → ℝ) (α : ℝ)
    (x : ℕ) (hx : 1 ≤ x) (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n) :
    ∑ n ∈ S, (f n/(n:ℂ))
        * ((V (Real.log x - Real.log n) : ℝ) : ℂ)
      = ((x:ℝ)^α : ℝ) * ∑ n ∈ S, (f n/((n:ℝ)^((1:ℝ)+α) : ℝ))
          * ((Real.exp (-(α*(Real.log x - Real.log n)))
              * V (Real.log x - Real.log n) : ℝ) : ℂ) := by
  classical
  have hx0 : (0:ℝ) < x := by exact_mod_cast hx
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := hS n hn
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn1
  -- the real identity behind the shift
  have hsplit : ((n:ℝ)^((1:ℝ)+α)) = (n:ℝ) * (n:ℝ)^α := by
    rw [Real.rpow_add hn0, Real.rpow_one]
  have hexp : Real.exp (-(α*(Real.log x - Real.log n)))
      = (x:ℝ)^(-α) * (n:ℝ)^α := by
    rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hn0, ← Real.exp_add]
    congr 1
    ring
  have hxa0 : (0:ℝ) < (x:ℝ)^α := Real.rpow_pos_of_pos hx0 α
  have hna0 : (0:ℝ) < (n:ℝ)^α := Real.rpow_pos_of_pos hn0 α
  have hneg : (x:ℝ)^(-α) = ((x:ℝ)^α)⁻¹ := Real.rpow_neg hx0.le α
  rw [hsplit, hexp, hneg]
  have hA : ((x:ℝ)^α : ℝ) ≠ 0 := ne_of_gt hxa0
  have hB : ((n:ℝ)^α : ℝ) ≠ 0 := ne_of_gt hna0
  have hn' : (n:ℝ) ≠ 0 := ne_of_gt hn0
  have hAC : ((((x:ℝ)^α : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA
  have hBC : ((((n:ℝ)^α : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB
  push_cast
  field_simp


/-- **Casting commutes with every iterated derivative** (Track R, N80):
`iteratedDeriv n (fun v => (f v : ℂ)) = fun v => (iteratedDeriv n f v : ℂ)`.

The `n`-fold version of `iteratedDeriv_two_ofReal`, by induction on `n`
from `deriv_ofReal_comp`.  Needed because §4's window tail has to be
taken at order `3`, not `2` — the second-order bound `M₂/(2π²L)` is a
factor of `log x` short of what the pairing estimate's `Mtail` can
afford (see the third-order tail lemma). -/
theorem iteratedDeriv_ofReal (n : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    iteratedDeriv n (fun v => ((f v : ℝ) : ℂ))
      = fun v => ((iteratedDeriv n f v : ℝ) : ℂ) := by
  induction n generalizing f with
  | zero => simp [iteratedDeriv_zero]
  | succ m ih =>
    have hf1 : ContDiff ℝ ∞ (deriv f) := by
      simpa using hf.iterate_deriv 1
    rw [iteratedDeriv_succ', iteratedDeriv_succ', deriv_ofReal_comp f hf,
      ih (deriv f) hf1]

/-- **The window transform tail, at third order** (Track R, N80): a
smooth compactly supported real window with third-derivative mass `M₃`
has transform tail `∫_{|ξ|>L} ‖𝓕V‖ ≤ M₃/(8π³L²)`.

`fourier_tail_le` is the same statement at order `2`, giving `M₂/(2π²L)`
— and that is **a factor of `log x` short of what §4 can afford**.  The
pairing estimate's tail contributes `E₁·Mtail ≍ C·e^{−k}·log³x·Wtail`,
so with the band at `L = halaszM x ≍ log²x` the tail must satisfy
`Wtail ≲ e^{k}/(C·log³x)`; the second-order bound only supplies
`≍ 1/log²x`, which fails at `k = 1`.  One more integration by parts
gives `≍ 1/log⁴x` and clears it with room to spare.

The proof is `fourier_tail_le`'s, with the exponent odd rather than
even: `‖(2πiξ)³‖ = 8π³|ξ|³` carries an absolute value where the square
carried none, and the tail integral is `∫_{ξ>L} ξ^{−3} = 1/(2L²)`. -/
theorem fourier_tail_cube_le (V : ℝ → ℝ) (hVs : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (M₃ : ℝ)
    (hM₃ : ∫ v, |iteratedDeriv 3 V v| ≤ M₃) (L : ℝ) (hL : 0 < L) :
    ∫ ξ in {ξ : ℝ | L < |ξ|}, ‖𝓕 (fun v => ((V v : ℝ) : ℂ)) ξ‖
      ≤ M₃/(8*Real.pi^3*L^2) := by
  classical
  set Vc : ℝ → ℂ := fun v => ((V v : ℝ) : ℂ) with hVc_def
  have hVcs : ContDiff ℝ ∞ Vc := Complex.ofRealCLM.contDiff.comp hVs
  have hVcc : HasCompactSupport Vc :=
    HasCompactSupport.comp_left hVc Complex.ofReal_zero
  have hM₃0 : 0 ≤ M₃ :=
    le_trans (integral_nonneg fun v => abs_nonneg _) hM₃
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  -- the iterated-derivative integrabilities
  have haux : ∀ n : ℕ, ContDiff ℝ ∞ (iteratedDeriv n Vc)
      ∧ HasCompactSupport (iteratedDeriv n Vc) := by
    intro n
    induction n with
    | zero =>
      rw [iteratedDeriv_zero]
      exact ⟨hVcs, hVcc⟩
    | succ k ih =>
      rw [iteratedDeriv_succ]
      refine ⟨?_, ih.2.deriv⟩
      simpa using ih.1.iterate_deriv 1
  have hint : ∀ n : ℕ, Integrable (iteratedDeriv n Vc) := fun n =>
    ((haux n).1.continuous).integrable_of_hasCompactSupport (haux n).2
  -- pointwise decay from three integrations by parts
  have hFI := Real.fourier_iteratedDeriv (f := Vc) (N := (3:ℕ∞))
    (hVcs.of_le (by exact_mod_cast le_top)) (fun n _ => hint n) (le_refl _)
  have hpt : ∀ ξ : ℝ, ξ ≠ 0 →
      ‖𝓕 Vc ξ‖ ≤ M₃/(8*Real.pi^3*|ξ|^3) := by
    intro ξ hξ
    have h1 := congrFun hFI ξ
    have hnorm3 : ‖((2*Real.pi*Complex.I*(ξ:ℂ))^3 : ℂ)‖
        = 8*Real.pi^3*|ξ|^3 := by
      rw [norm_pow]
      rw [show (2*Real.pi*Complex.I*(ξ:ℂ))
          = (((2*Real.pi*ξ : ℝ)):ℂ) * Complex.I from by push_cast; ring]
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
        abs_of_nonneg hpi.le]
      ring
    have h2 : ‖𝓕 (iteratedDeriv 3 Vc) ξ‖ = 8*Real.pi^3*|ξ|^3 * ‖𝓕 Vc ξ‖ := by
      rw [h1, norm_smul, hnorm3]
    have h3 : ‖𝓕 (iteratedDeriv 3 Vc) ξ‖ ≤ M₃ := by
      refine le_trans (VectorFourier.norm_fourierIntegral_le_integral_norm
        _ _ _ _ _) ?_
      rw [hVc_def, iteratedDeriv_ofReal 3 V hVs]
      refine le_trans (le_of_eq ?_) hM₃
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      dsimp only
      rw [Complex.norm_real, Real.norm_eq_abs]
    have h4 : (0:ℝ) < 8*Real.pi^3*|ξ|^3 := by
      have hax : (0:ℝ) < |ξ| := abs_pos.mpr hξ
      positivity
    rw [le_div_iff₀ h4]
    calc ‖𝓕 Vc ξ‖ * (8*Real.pi^3*|ξ|^3)
        = 8*Real.pi^3*|ξ|^3 * ‖𝓕 Vc ξ‖ := by ring
      _ = ‖𝓕 (iteratedDeriv 3 Vc) ξ‖ := h2.symm
      _ ≤ M₃ := h3
  -- integrate the tail
  have hset : {ξ : ℝ | L < |ξ|} = Set.Iio (-L) ∪ Set.Ioi L := by
    ext ξ
    rw [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi,
      lt_abs]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
  set G : SchwartzMap ℝ ℂ := hVcc.toSchwartzMap hVcs with hG_def
  have hFeq : ∀ ξ, ‖𝓕 Vc ξ‖ = ‖(𝓕 G) ξ‖ := fun _ => rfl
  have hFint : Integrable (fun ξ => ‖𝓕 Vc ξ‖) := by
    simp only [hFeq]
    exact (𝓕 G).integrable.norm
  -- on the right half the absolute value disappears
  have habs : ∀ ξ ∈ Set.Ioi L, M₃/(8*Real.pi^3*|ξ|^3)
      = M₃/(8*Real.pi^3) * ξ^((-3:ℝ)) := by
    intro ξ hξ
    rw [Set.mem_Ioi] at hξ
    have hξ0 : (0:ℝ) < ξ := lt_trans hL hξ
    have hval : ξ^((-3):ℝ) = 1/ξ^3 := by
      rw [show ((-3):ℝ) = -((3:ℕ):ℝ) from by push_cast; ring,
        Real.rpow_neg hξ0.le, Real.rpow_natCast, one_div]
    rw [hval, abs_of_pos hξ0]
    field_simp
  have hIoi : ∫ ξ in Set.Ioi L, M₃/(8*Real.pi^3*|ξ|^3)
      = M₃/(16*Real.pi^3*L^2) := by
    rw [setIntegral_congr_fun measurableSet_Ioi habs, integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num) hL]
    rw [show (-3:ℝ) + 1 = -2 from by norm_num]
    have hL0 : L ≠ 0 := ne_of_gt hL
    rw [show ((-2):ℝ) = -((2:ℕ):ℝ) from by push_cast; ring,
      Real.rpow_neg hL.le, Real.rpow_natCast]
    field_simp
    ring
  have hmaj_Ioi : IntegrableOn (fun ξ => M₃/(8*Real.pi^3*|ξ|^3))
      (Set.Ioi L) := by
    have h1 := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1)
      hL).const_mul (M₃/(8*Real.pi^3))
    exact MeasureTheory.IntegrableOn.congr_fun h1
      (fun ξ hξ => (habs ξ hξ).symm) measurableSet_Ioi
  -- the right-half bound
  have hIoi_bound : ∫ ξ in Set.Ioi L, ‖𝓕 Vc ξ‖
      ≤ M₃/(16*Real.pi^3*L^2) := by
    refine le_trans (setIntegral_mono_on hFint.integrableOn hmaj_Ioi
      measurableSet_Ioi ?_) (le_of_eq hIoi)
    intro ξ hξ
    rw [Set.mem_Ioi] at hξ
    exact hpt ξ (ne_of_gt (lt_trans hL hξ))
  -- reflection: Iio(−L)-integrals become Ioi L-integrals
  have hflip : ∀ (g : ℝ → ℝ),
      (∫ ξ, Set.indicator (Set.Iio (-L)) g ξ)
        = ∫ ξ, Set.indicator (Set.Ioi L) (fun ξ => g (-ξ)) ξ := by
    intro g
    rw [← integral_neg_eq_self
      (f := Set.indicator (Set.Iio (-L)) g)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    dsimp only
    by_cases h : L < ξ
    · rw [Set.indicator_of_mem (show -ξ ∈ Set.Iio (-L) from by
        rw [Set.mem_Iio]
        linarith)]
      rw [Set.indicator_of_mem (Set.mem_Ioi.mpr h)]
    · rw [Set.indicator_of_notMem (show -ξ ∉ Set.Iio (-L) from by
        rw [Set.mem_Iio]
        push_neg
        linarith)]
      rw [Set.indicator_of_notMem (show ξ ∉ Set.Ioi L from by
        rw [Set.mem_Ioi]
        exact h)]
  have hIio_bound : ∫ ξ in Set.Iio (-L), ‖𝓕 Vc ξ‖
      ≤ M₃/(16*Real.pi^3*L^2) := by
    rw [← integral_indicator measurableSet_Iio,
      hflip (fun ξ => ‖𝓕 Vc ξ‖), integral_indicator measurableSet_Ioi]
    have hptneg : ∀ ξ ∈ Set.Ioi L,
        ‖𝓕 Vc (-ξ)‖ ≤ M₃/(8*Real.pi^3*|ξ|^3) := by
      intro ξ hξ
      rw [Set.mem_Ioi] at hξ
      have hξ0 : (0:ℝ) < ξ := lt_trans hL hξ
      have := hpt (-ξ) (by
        intro h
        rw [neg_eq_zero] at h
        linarith)
      rwa [abs_neg] at this
    have hmono : ∫ ξ in Set.Ioi L, ‖𝓕 Vc (-ξ)‖
        ≤ ∫ ξ in Set.Ioi L, M₃/(8*Real.pi^3*|ξ|^3) := by
      refine setIntegral_mono_on ?_ hmaj_Ioi measurableSet_Ioi hptneg
      refine hmaj_Ioi.mono' ?_ ?_
      · refine Continuous.aestronglyMeasurable ?_ |>.restrict
        simp only [hFeq]
        exact ((𝓕 G).continuous.norm).comp continuous_neg
      · refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
        refine Filter.Eventually.of_forall fun ξ hξ => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact hptneg ξ hξ
    exact le_trans hmono (le_of_eq hIoi)
  -- combine
  rw [hset]
  have hdisj : Disjoint (Set.Iio (-L)) (Set.Ioi L) := by
    refine Set.disjoint_left.mpr fun ξ h1 h2 => ?_
    rw [Set.mem_Iio] at h1
    rw [Set.mem_Ioi] at h2
    linarith
  rw [setIntegral_union hdisj measurableSet_Ioi
    hFint.integrableOn hFint.integrableOn]
  have hhalf : M₃/(16*Real.pi^3*L^2) + M₃/(16*Real.pi^3*L^2)
      = M₃/(8*Real.pi^3*L^2) := by
    have hne : (16*Real.pi^3*L^2) ≠ 0 := by positivity
    field_simp
    ring
  linarith [hIio_bound, hIoi_bound, hhalf.le, hhalf.ge]

/-- **Character polynomials multiply by adding frequencies** (Track R,
N84): for any two finite index sets,

  `(∑_i a_i·𝐞(−α_i ξ))·(∑_j b_j·𝐞(−β_j ξ))
     = ∑_{(i,j)} a_i b_j·𝐞(−(α_i + β_j)ξ)`.

`𝐞` is an additive character, so a product of phase polynomials is
again a phase polynomial — over the product index set, with the
frequencies added.

This is the algebraic join between GHS §3 and §4.  §4's pairing
estimate bounds `∫‖P₁·P₂·P₃‖·w`; §3 needs a bound on a *single* sum,
which `norm_sum_translates_le_integral_char` turns into an integral
against one phase polynomial.  The two meet exactly here: the triple
product is the polynomial of the convolved coefficients. -/
theorem char_poly_mul {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ) (α : ι → ℝ) (β : κ → ℝ) (ξ : ℝ) :
    (∑ i ∈ A, a i * ((Real.fourierChar (-(α i * ξ)) : Circle) : ℂ))
        * (∑ j ∈ B, b j * ((Real.fourierChar (-(β j * ξ)) : Circle) : ℂ))
      = ∑ p ∈ A ×ˢ B, (a p.1 * b p.2)
          * ((Real.fourierChar (-((α p.1 + β p.2) * ξ)) : Circle) : ℂ) := by
  classical
  rw [Finset.sum_product,
    Finset.sum_mul_sum A B
      (fun i => a i * ((Real.fourierChar (-(α i * ξ)) : Circle) : ℂ))
      (fun j => b j * ((Real.fourierChar (-(β j * ξ)) : Circle) : ℂ))]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hchar : ((Real.fourierChar (-((α i + β j) * ξ)) : Circle) : ℂ)
      = ((Real.fourierChar (-(α i * ξ)) : Circle) : ℂ)
        * ((Real.fourierChar (-(β j * ξ)) : Circle) : ℂ) := by
    rw [show -((α i + β j) * ξ) = -(α i * ξ) + -(β j * ξ) from by ring,
      Real.fourierChar.map_add_eq_mul]
    push_cast
    ring
  rw [hchar]
  ring

/-- **The Dirichlet form of the product** (Track R, N84): at the
frequencies `log n`, the added frequency is the frequency of the
product,

  `(∑_m a_m·𝐞(−log m·ξ))·(∑_n b_n·𝐞(−log n·ξ))
     = ∑_{(m,n)} a_m b_n·𝐞(−log(mn)·ξ)`.

`char_poly_mul` with `log m + log n = log(mn)`, which is what makes a
product of Dirichlet polynomials the polynomial of the *Dirichlet
convolution* — the form GHS §3 consumes.  Positivity of the indices is
what `Real.log_mul` needs. -/
theorem char_poly_mul_log (A B : Finset ℕ) (a b : ℕ → ℂ)
    (hA : ∀ m ∈ A, 0 < m) (hB : ∀ n ∈ B, 0 < n) (ξ : ℝ) :
    (∑ m ∈ A, a m
        * ((Real.fourierChar (-(Real.log (m:ℝ) * ξ)) : Circle) : ℂ))
        * (∑ n ∈ B, b n
          * ((Real.fourierChar (-(Real.log (n:ℝ) * ξ)) : Circle) : ℂ))
      = ∑ p ∈ A ×ˢ B, (a p.1 * b p.2)
          * ((Real.fourierChar
              (-(Real.log ((p.1 * p.2 : ℕ):ℝ) * ξ)) : Circle) : ℂ) := by
  classical
  rw [char_poly_mul A B a b (fun m => Real.log (m:ℝ))
    (fun n => Real.log (n:ℝ)) ξ]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_product] at hp
  have h1 : (0:ℝ) < (p.1:ℝ) := by exact_mod_cast hA p.1 hp.1
  have h2 : (0:ℝ) < (p.2:ℝ) := by exact_mod_cast hB p.2 hp.2
  have hlog : Real.log ((p.1 * p.2 : ℕ):ℝ)
      = Real.log (p.1:ℝ) + Real.log (p.2:ℝ) := by
    push_cast
    exact Real.log_mul (ne_of_gt h1) (ne_of_gt h2)
  rw [hlog]
end ExpSums

end MoltResearch
