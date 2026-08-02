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

end ExpSums

end MoltResearch
