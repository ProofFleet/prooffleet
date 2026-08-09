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

/-- **The Perron sandwich, rescaled** (Track R, N87): multiplying
`perron_sandwich` through by the scale,

  `‖∑_{n ≤ M} g(n) − M·∑_{n∈S}(g(n)/n)·V(log M − log n)‖ ≤ 2ρ·M + 2`.

The form §3 consumes.  `perron_sandwich` compares the window-weighted
sum with the *normalized* Cesàro mean `(∑_{n≤M} g)/M`; §3's triple
convolution contains the *unnormalized* inner sum `∑_{n ≤ x/pq} f(n)`,
so the scale has to be carried across.  The edge budget `2ρ + 2/M`
becomes `2ρ·M + 2`.

This is the step that makes `perron_sandwich` usable at all in §3.
Applied to the triple convolution it is used at `g := f` and
`M := x/(pq)` — the inner sum is the only one of the three factors
whose coefficients are `1`-bounded, so it is the only place the
sandwich can be applied.  Collecting the triple sum by `npq` instead
would present a Dirichlet convolution carrying `log p·log q`, which is
not `1`-bounded and to which the sandwich does not apply. -/
theorem perron_sandwich_scaled (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (V : ℝ → ℝ) (ρ : ℝ) (M : ℕ) (hM : 4 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hVplat : ∀ v, ρ ≤ v → v ≤ 2*Real.log M + 1 → V v = Real.exp (-v))
    (hV0 : ∀ v, v ≤ 0 → V v = 0)
    (hVle : ∀ v, V v ≤ Real.exp (-v)) (hVnn : ∀ v, 0 ≤ V v)
    (S : Finset ℕ) (hS : Finset.Icc 1 M ⊆ S) (hS1 : ∀ n ∈ S, 1 ≤ n) :
    ‖(∑ n ∈ Finset.Icc 1 M, g n)
        - (M:ℂ) * ∑ n ∈ S, (g n/(n:ℂ))
            * ((V (Real.log M - Real.log n) : ℝ) : ℂ)‖
      ≤ 2*ρ*(M:ℝ) + 2 := by
  classical
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hbase := perron_sandwich g hg V ρ M hM hρ0 hρ1 hVplat hV0 hVle hVnn
    S hS hS1
  -- multiply the sandwich through by the scale
  have hmul : ‖(M:ℂ)‖ * ‖(∑ n ∈ S, (g n/(n:ℂ))
        * ((V (Real.log M - Real.log n) : ℝ) : ℂ))
      - (∑ n ∈ Finset.Icc 1 M, g n)/(M:ℂ)‖
      ≤ (M:ℝ) * (2*ρ + 2/(M:ℝ)) := by
    rw [Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hbase hM0.le
  rw [← norm_mul] at hmul
  have hdist : (M:ℂ) * ((∑ n ∈ S, (g n/(n:ℂ))
        * ((V (Real.log M - Real.log n) : ℝ) : ℂ))
      - (∑ n ∈ Finset.Icc 1 M, g n)/(M:ℂ))
      = -((∑ n ∈ Finset.Icc 1 M, g n)
        - (M:ℂ) * ∑ n ∈ S, (g n/(n:ℂ))
            * ((V (Real.log M - Real.log n) : ℝ) : ℂ)) := by
    have hMne : (M:ℂ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    field_simp
    ring
  rw [hdist, norm_neg] at hmul
  refine le_trans hmul (le_of_eq ?_)
  field_simp

/-- **The rescaled sandwich at every scale** (Track R, N88): the
`4 ≤ M` hypothesis of `perron_sandwich_scaled` costs only a constant to
remove —

  `‖∑_{n ≤ M} g(n) − M·∑_{n∈S}(g(n)/n)·V(log M − log n)‖ ≤ 2ρ·M + 6`

for every `M ≥ 1`.

§3 applies the sandwich to `tripleConv`'s inner sum at `M = x/(pq)`,
which drops below `4` once `pq > x/4`.  Rather than carry that range
restriction through the substitution and discharge it separately, it is
cheaper to observe that the small-scale case is trivial: at `M ≤ 3` the
sharp sum has at most three terms, and `V(v) = 0` for `v ≤ 0` kills
every smoothed term with `n ≥ M`, leaving at most `M − 1 ≤ 2` of them,
each at most `1/M` after the rescaling.  So both sides are `O(1)` and
the difference is at most `5`.

Keeping the constant at `6` rather than `5` leaves the statement stable
if the plateau constant ever moves. -/
theorem perron_sandwich_uniform (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (V : ℝ → ℝ) (ρ : ℝ) (M : ℕ) (hM : 1 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hVplat : ∀ v, ρ ≤ v → v ≤ 2*Real.log M + 1 → V v = Real.exp (-v))
    (hV0 : ∀ v, v ≤ 0 → V v = 0)
    (hVle : ∀ v, V v ≤ Real.exp (-v)) (hVnn : ∀ v, 0 ≤ V v)
    (S : Finset ℕ) (hS : Finset.Icc 1 M ⊆ S) (hS1 : ∀ n ∈ S, 1 ≤ n) :
    ‖(∑ n ∈ Finset.Icc 1 M, g n)
        - (M:ℂ) * ∑ n ∈ S, (g n/(n:ℂ))
            * ((V (Real.log M - Real.log n) : ℝ) : ℂ)‖
      ≤ 2*ρ*(M:ℝ) + 6 := by
  classical
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast (by omega : 0 < M)
  by_cases hbig : 4 ≤ M
  · -- the genuine case
    refine le_trans (perron_sandwich_scaled g hg V ρ M hbig hρ0 hρ1 hVplat
      hV0 hVle hVnn S hS hS1) ?_
    linarith
  · -- `M ≤ 3`: both sides are `O(1)`
    push_neg at hbig
    have hM3 : M ≤ 3 := by omega
    -- the smoothed terms with `n ≥ M` vanish
    have hvanish : ∀ n ∈ S, n ∉ S.filter (fun n => n < M) →
        (g n/(n:ℂ)) * ((V (Real.log M - Real.log n) : ℝ) : ℂ) = 0 := by
      intro n hn hnot
      simp only [Finset.mem_filter, not_and, not_lt] at hnot
      have hnM : M ≤ n := hnot hn
      have hle : Real.log (M:ℝ) - Real.log (n:ℝ) ≤ 0 := by
        have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hS1 n hn
        have := Real.log_le_log hM0 (by exact_mod_cast hnM : (M:ℝ) ≤ (n:ℝ))
        linarith
      rw [hV0 _ hle]
      simp
    have hrestrict : (∑ n ∈ S, (g n/(n:ℂ))
          * ((V (Real.log M - Real.log n) : ℝ) : ℂ))
        = ∑ n ∈ S.filter (fun n => n < M), (g n/(n:ℂ))
            * ((V (Real.log M - Real.log n) : ℝ) : ℂ) :=
      (Finset.sum_subset (Finset.filter_subset _ _)
        (fun n hn hnot => hvanish n hn hnot)).symm
    -- each surviving term is at most `1/M` after rescaling
    have hterm : ∀ n ∈ S.filter (fun n => n < M),
        ‖(M:ℂ) * ((g n/(n:ℂ))
          * ((V (Real.log M - Real.log n) : ℝ) : ℂ))‖ ≤ 1 := by
      intro n hn
      simp only [Finset.mem_filter] at hn
      have hn1 : 1 ≤ n := hS1 n hn.1
      have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
      have hVb : V (Real.log M - Real.log n) ≤ (n:ℝ)/(M:ℝ) := by
        refine le_trans (hVle _) (le_of_eq ?_)
        rw [neg_sub, Real.exp_sub, Real.exp_log hn0, Real.exp_log hM0]
      rw [norm_mul, norm_mul, Complex.norm_natCast, norm_div,
        Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hVnn _)]
      have hgn : ‖g n‖ ≤ 1 := hg n
      have hstep : ‖g n‖/(n:ℝ) * V (Real.log M - Real.log n)
          ≤ (1/(n:ℝ)) * ((n:ℝ)/(M:ℝ)) := by
        refine mul_le_mul (by exact div_le_div_of_nonneg_right hgn hn0.le)
          hVb (hVnn _) (by positivity)
      have hval : (1/(n:ℝ)) * ((n:ℝ)/(M:ℝ)) = 1/(M:ℝ) := by
        field_simp
      have hMge : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
      calc (M:ℝ) * (‖g n‖/(n:ℝ) * V (Real.log M - Real.log n))
          ≤ (M:ℝ) * ((1/(n:ℝ)) * ((n:ℝ)/(M:ℝ))) :=
            mul_le_mul_of_nonneg_left hstep hM0.le
        _ = 1 := by rw [hval]; field_simp
    -- collect: at most `M − 1 ≤ 2` surviving terms
    have hcard : (S.filter (fun n => n < M)).card ≤ 2 := by
      have hsub : S.filter (fun n => n < M) ⊆ Finset.Ico 1 M := by
        intro n hn
        simp only [Finset.mem_filter] at hn
        exact Finset.mem_Ico.mpr ⟨hS1 n hn.1, hn.2⟩
      have := Finset.card_le_card hsub
      simp only [Nat.card_Ico] at this
      omega
    have hsmooth : ‖(M:ℂ) * ∑ n ∈ S, (g n/(n:ℂ))
        * ((V (Real.log M - Real.log n) : ℝ) : ℂ)‖ ≤ 2 := by
      rw [hrestrict, Finset.mul_sum]
      refine le_trans (norm_sum_le _ _) ?_
      refine le_trans (Finset.sum_le_sum hterm) ?_
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast hcard
    -- the sharp sum has at most `M ≤ 3` terms
    have hsharp : ‖∑ n ∈ Finset.Icc 1 M, g n‖ ≤ 3 := by
      refine le_trans (norm_sum_le _ _) ?_
      refine le_trans (Finset.sum_le_sum (fun n _ => hg n)) ?_
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc]
      have : (M + 1 - 1) ≤ 3 := by omega
      exact_mod_cast this
    have hρM : (0:ℝ) ≤ 2*ρ*(M:ℝ) := by positivity
    calc ‖(∑ n ∈ Finset.Icc 1 M, g n)
          - (M:ℂ) * ∑ n ∈ S, (g n/(n:ℂ))
              * ((V (Real.log M - Real.log n) : ℝ) : ℂ)‖
        ≤ ‖∑ n ∈ Finset.Icc 1 M, g n‖
          + ‖(M:ℂ) * ∑ n ∈ S, (g n/(n:ℂ))
              * ((V (Real.log M - Real.log n) : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ 3 + 2 := add_le_add hsharp hsmooth
      _ ≤ 2*ρ*(M:ℝ) + 6 := by linarith

/-- **The rescaled sandwich, real-valued** (Track R, N89): for a real
`1`-bounded `g` and every `M ≥ 1`,

  `|∑_{n ≤ M} g(n) − M·∑_{n∈S}(g(n)/n)·V(log M − log n)| ≤ 2ρ·M + 6`.

`perron_sandwich_uniform` reads `g : ℕ → ℂ`, but §3's `tripleConv` is
real-valued (`f : ℕ → ℝ`).  The mismatch is mechanical — every term is
the coercion of a real one, and `‖(r : ℂ)‖ = |r|` — but it would
otherwise have to be re-derived at each of the three places the
substitution touches, so it is discharged once here.

Same principle as removing the `4 ≤ M` hypothesis: take the friction
out at the source rather than carry it through every consumer. -/
theorem perron_sandwich_uniform_real (g : ℕ → ℝ) (hg : ∀ n, |g n| ≤ 1)
    (V : ℝ → ℝ) (ρ : ℝ) (M : ℕ) (hM : 1 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hVplat : ∀ v, ρ ≤ v → v ≤ 2*Real.log M + 1 → V v = Real.exp (-v))
    (hV0 : ∀ v, v ≤ 0 → V v = 0)
    (hVle : ∀ v, V v ≤ Real.exp (-v)) (hVnn : ∀ v, 0 ≤ V v)
    (S : Finset ℕ) (hS : Finset.Icc 1 M ⊆ S) (hS1 : ∀ n ∈ S, 1 ≤ n) :
    |(∑ n ∈ Finset.Icc 1 M, g n)
        - (M:ℝ) * ∑ n ∈ S, (g n/(n:ℝ)) * V (Real.log M - Real.log n)|
      ≤ 2*ρ*(M:ℝ) + 6 := by
  classical
  have hgc : ∀ n, ‖((g n : ℝ) : ℂ)‖ ≤ 1 := by
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hg n
  have hbase := perron_sandwich_uniform (fun n => ((g n : ℝ) : ℂ)) hgc
    V ρ M hM hρ0 hρ1 hVplat hV0 hVle hVnn S hS hS1
  -- the complex expression is the coercion of the real one
  have hcoe : ((∑ n ∈ Finset.Icc 1 M, ((g n : ℝ) : ℂ))
        - (M:ℂ) * ∑ n ∈ S, (((g n : ℝ) : ℂ)/(n:ℂ))
            * ((V (Real.log M - Real.log n) : ℝ) : ℂ))
      = ((((∑ n ∈ Finset.Icc 1 M, g n)
          - (M:ℝ) * ∑ n ∈ S, (g n/(n:ℝ))
              * V (Real.log M - Real.log n) : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hcoe, Complex.norm_real, Real.norm_eq_abs] at hbase
  exact hbase

/-- **The smoothed sum is at most `1`** (Track R, N92): for `1`-bounded
real `g` and any admissible window,

  `|∑_{n∈S} (g(n)/n)·V(log M − log n)| ≤ 1`,

uniformly in `M` and `S`.

Two window properties do all the work and no cancellation is needed:
`V(v) = 0` for `v ≤ 0` kills every term with `n ≥ M`, and
`V(v) ≤ exp(−v)` makes each survivor at most `(1/n)·(n/M) = 1/M`.  There
are fewer than `M` survivors, so the total is at most `(M−1)/M < 1`.

This is what prices the *floor* in §3's substitution.  The sandwich is
applied at the integer scale `⌊x/(pq)⌋`, so replacing it by `x/(pq)`
costs `|⌊x/(pq)⌋ − x/(pq)| < 1` times this sum, per term — and against
`tripleConv`'s weights that is `O(∑_p|A(p)|∑_q|B(q)|)`, which is `O(x)`
and so within what (3.2) allows.

The `M`-free form matters: `perron_sandwich_uniform`'s small-scale case
bounds `M` times this sum, which is a different statement — that one
degrades as `M` grows, this one does not. -/
theorem smoothed_sum_le_one (g : ℕ → ℝ) (hg : ∀ n, |g n| ≤ 1)
    (V : ℝ → ℝ) (M : ℕ) (hM : 1 ≤ M)
    (hV0 : ∀ v, v ≤ 0 → V v = 0) (hVle : ∀ v, V v ≤ Real.exp (-v))
    (hVnn : ∀ v, 0 ≤ V v)
    (S : Finset ℕ) (hS1 : ∀ n ∈ S, 1 ≤ n) :
    |∑ n ∈ S, (g n/(n:ℝ)) * V (Real.log M - Real.log n)| ≤ 1 := by
  classical
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast (by omega : 0 < M)
  -- terms with `n ≥ M` vanish
  have hvanish : ∀ n ∈ S, n ∉ S.filter (fun n => n < M) →
      (g n/(n:ℝ)) * V (Real.log M - Real.log n) = 0 := by
    intro n hn hnot
    simp only [Finset.mem_filter, not_and, not_lt] at hnot
    have hnM : M ≤ n := hnot hn
    have hle : Real.log (M:ℝ) - Real.log (n:ℝ) ≤ 0 := by
      have := Real.log_le_log hM0 (by exact_mod_cast hnM : (M:ℝ) ≤ (n:ℝ))
      linarith
    rw [hV0 _ hle, mul_zero]
  have hrestrict : (∑ n ∈ S, (g n/(n:ℝ)) * V (Real.log M - Real.log n))
      = ∑ n ∈ S.filter (fun n => n < M),
          (g n/(n:ℝ)) * V (Real.log M - Real.log n) :=
    (Finset.sum_subset (Finset.filter_subset _ _)
      (fun n hn hnot => hvanish n hn hnot)).symm
  -- each survivor is at most `1/M`
  have hterm : ∀ n ∈ S.filter (fun n => n < M),
      |(g n/(n:ℝ)) * V (Real.log M - Real.log n)| ≤ 1/(M:ℝ) := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    have hn1 : 1 ≤ n := hS1 n hn.1
    have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
    have hVb : V (Real.log M - Real.log n) ≤ (n:ℝ)/(M:ℝ) := by
      refine le_trans (hVle _) (le_of_eq ?_)
      rw [neg_sub, Real.exp_sub, Real.exp_log hn0, Real.exp_log hM0]
    rw [abs_mul, abs_div, abs_of_nonneg hn0.le,
      abs_of_nonneg (hVnn _)]
    have hstep : |g n|/(n:ℝ) * V (Real.log M - Real.log n)
        ≤ (1/(n:ℝ)) * ((n:ℝ)/(M:ℝ)) :=
      mul_le_mul (div_le_div_of_nonneg_right (hg n) hn0.le) hVb
        (hVnn _) (by positivity)
    refine le_trans hstep (le_of_eq ?_)
    field_simp
  refine le_trans (le_of_eq (by rw [hrestrict])) ?_
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  simp only [Finset.sum_const, nsmul_eq_mul]
  -- fewer than `M` survivors
  have hcard : ((S.filter (fun n => n < M)).card : ℝ) ≤ (M:ℝ) := by
    have hsub : S.filter (fun n => n < M) ⊆ Finset.Ico 1 M := by
      intro n hn
      simp only [Finset.mem_filter] at hn
      exact Finset.mem_Ico.mpr ⟨hS1 n hn.1, hn.2⟩
    have hc := Finset.card_le_card hsub
    simp only [Nat.card_Ico] at hc
    have : (S.filter (fun n => n < M)).card ≤ M := by omega
    exact_mod_cast this
  calc ((S.filter (fun n => n < M)).card : ℝ) * (1/(M:ℝ))
      ≤ (M:ℝ) * (1/(M:ℝ)) := by
        refine mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 1 := by field_simp

/-- **On the plateau, the scale cancels** (Track R, N94): whenever
`log M − log n` lies in the plateau range,

  `M · V(log M − log n) = n`,

**independently of `M`**.

`V(v) = exp(−v)` there, so `V(log M − log n) = n/M` and the `M` cancels
outright.  Two consequences, and the second is why this is a lemma
rather than a step:

* the sandwich's main term reconstructs `n` exactly on the plateau —
  the smoothing is lossless in the bulk, and all of its cost sits at
  the two edges;
* **the integer and real scales agree.** §3 applies the sandwich at the
  integer scale `⌊x/pq⌋`, while §4's polynomials carry the window at
  `log x − log(npq)`, i.e. the real scale `x/pq`.  Since both give `n`
  on the plateau, the floor shift `log(x/pq) − log⌊x/pq⌋` costs
  *nothing* in the bulk, and only the edge terms have to be paid for.

That was not obvious: the shift is nonzero (up to `≈ 1/M`), so the two
windows genuinely differ pointwise.  It is the *product with the
scale* that is invariant, not the window. -/
theorem scale_mul_window_eq (V : ℝ → ℝ) (ρ B M n : ℝ)
    (hM : 0 < M) (hn : 0 < n)
    (hplat : ∀ v, ρ ≤ v → v ≤ B → V v = Real.exp (-v))
    (hlo : ρ ≤ Real.log M - Real.log n)
    (hhi : Real.log M - Real.log n ≤ B) :
    M * V (Real.log M - Real.log n) = n := by
  rw [hplat _ hlo hhi, neg_sub, Real.exp_sub, Real.exp_log hn,
    Real.exp_log hM]
  field_simp

/-- **On the plateau, the weighted term is the coefficient** (Track R,
N95): for `n ≥ 1` and `log M − log n` in the plateau range,

  `(g(n)/n) · (M · V(log M − log n)) = g(n)`,

independently of `M`.

`scale_mul_window_eq` divided by `n`.  This is the form the edge
analysis consumes: it says the smoothed sum, *rescaled*, reproduces the
sharp sum term by term wherever the plateau reaches — so the two
scales `⌊x/pq⌋` and `x/pq` contribute *identically* in the bulk and
their difference is supported entirely on the edges.

Stated separately from `scale_mul_window_eq` because the edge argument
needs it at this weight: the difference of the two scaled sums is
`∑_n (g(n)/n)(M·V(…) − Q·V(…))`, whose summand vanishes exactly when
this applies to both scales at once. -/
theorem weighted_window_eq_of_plateau (g : ℕ → ℝ) (V : ℝ → ℝ) (ρ B M : ℝ)
    (n : ℕ) (hM : 0 < M) (hn : 1 ≤ n)
    (hplat : ∀ v, ρ ≤ v → v ≤ B → V v = Real.exp (-v))
    (hlo : ρ ≤ Real.log M - Real.log n)
    (hhi : Real.log M - Real.log n ≤ B) :
    (g n/(n:ℝ)) * (M * V (Real.log M - Real.log n)) = g n := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  rw [scale_mul_window_eq V ρ B M (n:ℝ) hM hn0 hplat hlo hhi]
  field_simp

/-- **Counting the integers above a real threshold** (Track R, N96):
for `0 ≤ c ≤ N`,

  `#{n ∈ [1, N] : c < n} ≤ N − c + 1`.

The off-plateau count of the edge analysis.  `V(v) = exp(−v)` fails
only for `v < ρ`, i.e. for `n > M·e^{−ρ}`, so the terms where the two
scales `⌊x/pq⌋` and `x/pq` disagree are exactly those counted here at
`c = M·e^{−ρ}` — and `1 − e^{−ρ} ≤ ρ` then turns the count into
`≤ ρ·M + 1`, matching the `2ρM + 6` shape the sandwich already
produces, so `perron_error_inner_le` and `perron_error_outer_le` sum it
unchanged.

`c ≤ N` is not cosmetic: without it the right side goes negative while
the count is `0`.  In the application `c = M·e^{−ρ} ≤ M ≤ x = N`. -/
theorem card_gt_le (N : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hcN : c ≤ (N:ℝ)) :
    (((Finset.Icc 1 N).filter (fun n : ℕ => c < (n:ℝ))).card : ℝ)
      ≤ (N:ℝ) - c + 1 := by
  classical
  -- every counted `n` exceeds `⌊c⌋₊`
  have hsub : (Finset.Icc 1 N).filter (fun n : ℕ => c < (n:ℝ))
      ⊆ Finset.Icc (⌊c⌋₊ + 1) N := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_Icc]
    refine ⟨?_, hn.1.2⟩
    have h1 : (⌊c⌋₊:ℝ) ≤ c := Nat.floor_le hc0
    have h2 : (⌊c⌋₊:ℝ) < (n:ℝ) := lt_of_le_of_lt h1 hn.2
    have h3 : ⌊c⌋₊ < n := by exact_mod_cast h2
    omega
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  -- the floor sits below `N`
  have hflN : ⌊c⌋₊ ≤ N := by
    have := Nat.floor_le_floor hcN
    simpa using this
  have hcast : (((Finset.Icc 1 N).filter (fun n : ℕ => c < (n:ℝ))).card : ℝ)
      ≤ ((N:ℝ) - (⌊c⌋₊:ℝ)) := by
    have h : ((Finset.Icc 1 N).filter (fun n : ℕ => c < (n:ℝ))).card
        ≤ N - ⌊c⌋₊ := by omega
    have hc : ((N - ⌊c⌋₊ : ℕ):ℝ) = (N:ℝ) - (⌊c⌋₊:ℝ) := by
      rw [Nat.cast_sub hflN]
    calc (((Finset.Icc 1 N).filter (fun n : ℕ => c < (n:ℝ))).card : ℝ)
        ≤ ((N - ⌊c⌋₊ : ℕ):ℝ) := by exact_mod_cast h
      _ = (N:ℝ) - (⌊c⌋₊:ℝ) := hc
  -- and above `c − 1`
  have hfl : c < (⌊c⌋₊:ℝ) + 1 := Nat.lt_floor_add_one c
  linarith [hcast, hfl]

/-- **A single scaled window term is at most `1`** (Track R, N97): for
`1`-bounded `g`, `n ≥ 1` and `M > 0`,

  `|(g(n)/n) · (M · V(log M − log n))| ≤ 1`,

with no plateau hypothesis — only `0 ≤ V ≤ exp(−·)`.

`V(log M − log n) ≤ exp(log n − log M) = n/M`, so the whole term is at
most `(1/n)·M·(n/M) = 1`.  The scale cancels here for the same reason
it cancels in `scale_mul_window_eq`, except that this is an inequality
holding *everywhere* rather than an identity holding on the plateau.

That is what the edge analysis needs.  Off the plateau the two scales
`⌊x/pq⌋` and `x/pq` no longer agree, but each is still bounded by this,
so their difference is at most `2` per term — and
`weighted_window_eq_of_plateau` plus `card_gt_le` confine those terms
to the `≤ ρ·M + 1` integers in `(M·e^{−ρ}, M]`. -/
theorem weighted_window_term_le_one (g : ℕ → ℝ) (hg : ∀ n, |g n| ≤ 1)
    (V : ℝ → ℝ) (M : ℝ) (hM : 0 < M) (n : ℕ) (hn : 1 ≤ n)
    (hVle : ∀ v, V v ≤ Real.exp (-v)) (hVnn : ∀ v, 0 ≤ V v) :
    |(g n/(n:ℝ)) * (M * V (Real.log M - Real.log n))| ≤ 1 := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hVb : V (Real.log M - Real.log n) ≤ (n:ℝ)/M := by
    refine le_trans (hVle _) (le_of_eq ?_)
    rw [neg_sub, Real.exp_sub, Real.exp_log hn0, Real.exp_log hM]
  rw [abs_mul, abs_div, abs_of_nonneg hn0.le, abs_mul, abs_of_pos hM,
    abs_of_nonneg (hVnn _)]
  have hstep : |g n|/(n:ℝ) * (M * V (Real.log M - Real.log n))
      ≤ (1/(n:ℝ)) * (M * ((n:ℝ)/M)) := by
    refine mul_le_mul (div_le_div_of_nonneg_right (hg n) hn0.le)
      (mul_le_mul_of_nonneg_left hVb hM.le)
      (mul_nonneg hM.le (hVnn _)) (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  field_simp

/-- **The two scales differ only on the edge** (Track R, N98): for
`M = ⌊Q⌋`,

  `|∑_{n∈S} (g(n)/n)·(M·V(log M − log n) − Q·V(log Q − log n))| ≤ 2ρ·M + 2`.

This is what lets §3's integer scale `⌊x/pq⌋` be traded for §4's real
scale `x/pq`.  Three facts combine and nothing new is proved:

* **the bulk vanishes** — for `n ≤ M·e^{−ρ}` both scales sit on the
  plateau, where `weighted_window_eq_of_plateau` makes each term
  `g(n)`, so the difference is `0`;
* **the far tail vanishes** — for `n > M` we have `n ≥ M+1 > Q`, so
  `hV0` kills both terms;
* **the edge is short** — what is left lies in `(M·e^{−ρ}, M]`, which
  `card_gt_le` counts at `≤ ρ·M + 1` via `1 − e^{−ρ} ≤ ρ`, and each
  term there is `≤ 2` by `weighted_window_term_le_one` applied twice.

The ceiling of the band is `M`, **not** the summation range: beyond `Q`
both scales vanish, and `M ≤ n < Q` holds for no integer since
`Q < M+1`.  Counting over the range instead would give `O(#S)` per
pair rather than `O(ρM)` — the difference between an error that closes
against `(3.2)` and one that does not. -/
theorem scale_diff_le (g : ℕ → ℝ) (hg : ∀ n, |g n| ≤ 1) (V : ℝ → ℝ)
    (ρ B : ℝ) (hρ0 : 0 ≤ ρ) (M : ℕ) (Q : ℝ) (hM1 : 1 ≤ M)
    (hMQ : (M:ℝ) ≤ Q) (hQM : Q < (M:ℝ) + 1)
    (hplat : ∀ v, ρ ≤ v → v ≤ B → V v = Real.exp (-v))
    (hV0 : ∀ v, v ≤ 0 → V v = 0) (hVle : ∀ v, V v ≤ Real.exp (-v))
    (hVnn : ∀ v, 0 ≤ V v) (hB : Real.log Q ≤ B)
    (S : Finset ℕ) (hS1 : ∀ n ∈ S, 1 ≤ n) :
    |∑ n ∈ S, (g n/(n:ℝ)) * ((M:ℝ) * V (Real.log (M:ℝ) - Real.log (n:ℝ))
        - Q * V (Real.log Q - Real.log (n:ℝ)))|
      ≤ 2*ρ*(M:ℝ) + 2 := by
  classical
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM1
  have hQ0 : (0:ℝ) < Q := lt_of_lt_of_le hM0 hMQ
  have hlogMQ : Real.log (M:ℝ) ≤ Real.log Q := Real.log_le_log hM0 hMQ
  set c : ℝ := (M:ℝ) * Real.exp (-ρ) with hc_def
  set E : Finset ℕ := S.filter (fun n : ℕ => c < (n:ℝ) ∧ n ≤ M) with hE_def
  -- outside the edge band the summand vanishes
  have hvanish : ∀ n ∈ S, n ∉ E →
      (g n/(n:ℝ)) * ((M:ℝ) * V (Real.log (M:ℝ) - Real.log (n:ℝ))
        - Q * V (Real.log Q - Real.log (n:ℝ))) = 0 := by
    intro n hn hnot
    have hn1 : 1 ≤ n := hS1 n hn
    have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
    have hlogn : (0:ℝ) ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
    simp only [hE_def, Finset.mem_filter, not_and] at hnot
    rcases le_or_gt ((n:ℝ)) c with hlo | hhi
    · -- the bulk: both scales on the plateau, each term is `g n`
      have hplo : ρ ≤ Real.log (M:ℝ) - Real.log (n:ℝ) := by
        have h1 : Real.log (n:ℝ) ≤ Real.log c := Real.log_le_log hn0 hlo
        have h2 : Real.log c = Real.log (M:ℝ) + (-ρ) := by
          rw [hc_def, Real.log_mul (ne_of_gt hM0) (Real.exp_ne_zero _),
            Real.log_exp]
        linarith
      have hphi : Real.log (M:ℝ) - Real.log (n:ℝ) ≤ B := by linarith
      have hqlo : ρ ≤ Real.log Q - Real.log (n:ℝ) := by linarith
      have hqhi : Real.log Q - Real.log (n:ℝ) ≤ B := by linarith
      rw [mul_sub,
        weighted_window_eq_of_plateau g V ρ B (M:ℝ) n hM0 hn1 hplat hplo hphi,
        weighted_window_eq_of_plateau g V ρ B Q n hQ0 hn1 hplat hqlo hqhi,
        sub_self]
    · -- the far tail: `n > M ≥ Q − 1`, so both windows are at `≤ 0`
      have hnM : M < n := by
        by_contra hcon
        push_neg at hcon
        exact absurd (hnot hn hhi) (by omega)
      have hnMR : (M:ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast hnM
      have hQn : Q ≤ (n:ℝ) := by linarith
      have h1 : Real.log (M:ℝ) - Real.log (n:ℝ) ≤ 0 := by
        have := Real.log_le_log hM0 (by linarith : (M:ℝ) ≤ (n:ℝ))
        linarith
      have h2 : Real.log Q - Real.log (n:ℝ) ≤ 0 := by
        have := Real.log_le_log hQ0 hQn
        linarith
      rw [hV0 _ h1, hV0 _ h2]
      ring
  have hrestrict : (∑ n ∈ S, (g n/(n:ℝ))
        * ((M:ℝ) * V (Real.log (M:ℝ) - Real.log (n:ℝ))
          - Q * V (Real.log Q - Real.log (n:ℝ))))
      = ∑ n ∈ E, (g n/(n:ℝ))
          * ((M:ℝ) * V (Real.log (M:ℝ) - Real.log (n:ℝ))
            - Q * V (Real.log Q - Real.log (n:ℝ))) :=
    (Finset.sum_subset (by rw [hE_def]; exact Finset.filter_subset _ _)
      (fun n hn hnot => hvanish n hn hnot)).symm
  -- each edge term is at most `2`
  have hterm : ∀ n ∈ E,
      |(g n/(n:ℝ)) * ((M:ℝ) * V (Real.log (M:ℝ) - Real.log (n:ℝ))
        - Q * V (Real.log Q - Real.log (n:ℝ)))| ≤ 2 := by
    intro n hn
    simp only [hE_def, Finset.mem_filter] at hn
    have hn1 : 1 ≤ n := hS1 n hn.1
    have h1 := weighted_window_term_le_one g hg V (M:ℝ) hM0 n hn1 hVle hVnn
    have h2 := weighted_window_term_le_one g hg V Q hQ0 n hn1 hVle hVnn
    calc |(g n/(n:ℝ)) * ((M:ℝ) * V (Real.log (M:ℝ) - Real.log (n:ℝ))
          - Q * V (Real.log Q - Real.log (n:ℝ)))|
        = |(g n/(n:ℝ)) * ((M:ℝ) * V (Real.log (M:ℝ) - Real.log (n:ℝ)))
            - (g n/(n:ℝ)) * (Q * V (Real.log Q - Real.log (n:ℝ)))| := by
          rw [mul_sub]
      _ ≤ |(g n/(n:ℝ)) * ((M:ℝ) * V (Real.log (M:ℝ) - Real.log (n:ℝ)))|
            + |(g n/(n:ℝ)) * (Q * V (Real.log Q - Real.log (n:ℝ)))| :=
          abs_sub _ _
      _ ≤ 1 + 1 := add_le_add h1 h2
      _ = 2 := by norm_num
  -- and the band is short
  have hsub : E ⊆ (Finset.Icc 1 M).filter (fun n : ℕ => c < (n:ℝ)) := by
    intro n hn
    simp only [hE_def, Finset.mem_filter] at hn
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hS1 n hn.1, hn.2.2⟩, hn.2.1⟩
  have hc0 : (0:ℝ) ≤ c := by rw [hc_def]; positivity
  have hcM : c ≤ (M:ℝ) := by
    rw [hc_def]
    have hexp : Real.exp (-ρ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith [hM0]
  have hcount : ((E.card : ℕ):ℝ) ≤ ρ*(M:ℝ) + 1 := by
    have h1 : ((E.card : ℕ):ℝ)
        ≤ ((((Finset.Icc 1 M).filter (fun n : ℕ => c < (n:ℝ))).card : ℕ):ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h2 := card_gt_le M c hc0 hcM
    have h3 : (M:ℝ) - c ≤ ρ*(M:ℝ) := by
      have hexp : 1 - ρ ≤ Real.exp (-ρ) := by
        have := Real.add_one_le_exp (-ρ)
        linarith
      rw [hc_def]
      nlinarith [hM0]
    linarith
  rw [hrestrict]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  simp only [Finset.sum_const, nsmul_eq_mul]
  nlinarith [hcount]

/-- **Below scale `1` the window vanishes** (Track R, N100): for
`0 ≤ Q ≤ 1` and any `n`,

  `V(log Q − log n) = 0`.

Immediate — `log Q ≤ 0 ≤ log n` — but it is what makes §3's
`p`-dependent inner range compatible with §4's fixed one.

`tripleConv` sums `q` over `(x/p).primesBelow`, which moves with `p`,
whereas `ghs_smoothed_triple_le` uses a single index set.  Enlarging the
inner range to a fixed superset adds terms at `q ≥ ⌊x/p⌋`, and this
kills every one of them with `pq > x`: there the real scale `x/pq` is
below `1`, so the whole smoothed sum is zero.

**What it does not kill** is `q = ⌊x/p⌋` itself, where `pq ≤ x` still
holds — at most one prime per `p`.  That term survives at size
`≤ 2·|log q·f(q)|`, and against the outer weight
`|log p·f(p)/log(x/p)|` it contributes `≤ 2 log p` per `p`, hence
`O(x)` overall by Chebyshev's θ-bound — within what (3.2) allows, but
not free.  The enlargement is therefore a real (if cheap) discard, not
a relabelling. -/
theorem window_vanishes_of_scale_le_one (V : ℝ → ℝ)
    (hV0 : ∀ v, v ≤ 0 → V v = 0) (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1)
    (n : ℕ) :
    V (Real.log Q - Real.log (n:ℝ)) = 0 := by
  refine hV0 _ ?_
  have hlogQ : Real.log Q ≤ 0 := Real.log_nonpos hQ0 hQ1
  have hlogn : (0:ℝ) ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  linarith

/-- **Past the inner range the smoothed sum is zero** (Track R, N101):
if `x < p·q` then

  `∑_{n∈S} (f(n)/n)·V(log(x/pq) − log n) = 0`.

The vanishing half of §3's range enlargement.  `tripleConv` sums `q`
over `(x/p).primesBelow`, a range that moves with `p`, while
`ghs_smoothed_triple_le` wants one fixed index set.  Enlarging to a
fixed superset adds exactly the primes `q ≥ ⌊x/p⌋`, and every one with
`q > ⌊x/p⌋` has `p·q > x` — so the scale falls below `1` and
`window_vanishes_of_scale_le_one` kills the sum outright, term by term.

What is left over is the single prime `q = ⌊x/p⌋`, where `p·q ≤ x`
still holds.  That one does not vanish and has to be discarded
explicitly; at `≤ 2 log p` per `p` it costs `O(x)` by Chebyshev, which
`(3.2)` allows.  Isolating the vanishing part here means that discard
can be stated against a single term rather than against the whole
added range — bounding the added range crudely would give `O(x log x)`
and not close. -/
theorem smoothed_vanishes_of_lt_mul (V : ℝ → ℝ)
    (hV0 : ∀ v, v ≤ 0 → V v = 0) (f : ℕ → ℝ) (x p q : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hpq : x < p*q) (S : Finset ℕ) :
    ∑ n ∈ S, (f n/(n:ℝ))
        * V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ)) = 0 := by
  refine Finset.sum_eq_zero fun n _ => ?_
  have hpq0 : (0:ℝ) < (p:ℝ)*(q:ℝ) := by
    have h1 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
    have h2 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
    positivity
  have hle : (x:ℝ)/((p:ℝ)*(q:ℝ)) ≤ 1 := by
    rw [div_le_one hpq0]
    have : ((x:ℕ):ℝ) ≤ ((p*q : ℕ):ℝ) := by exact_mod_cast hpq.le
    push_cast at this
    linarith
  have hnn : (0:ℝ) ≤ (x:ℝ)/((p:ℝ)*(q:ℝ)) := by positivity
  rw [window_vanishes_of_scale_le_one V hV0 _ hnn hle n, mul_zero]

/-- **The smoothed sum is at most `1`, at a real scale** (Track R,
N103): for `1`-bounded real `g` and any `M > 0`,

  `|∑_{n∈S} (g(n)/n)·V(log M − log n)| ≤ 1`.

`smoothed_sum_le_one` with the scale no longer required to be an
integer.  The proof is the same — `hV0` kills every `n ≥ M`,
`hVle` makes each survivor `≤ (1/n)·(n/M) = 1/M`, and there are at
most `⌊M⌋ ≤ M` of them — but the integer version cannot be applied
where §3 needs it.

§3's Perron scale is `x/(pq)`, a **real** quotient: the sandwich runs
at the integer scale `⌊x/pq⌋`, and `scale_diff_le` then trades it for
`x/pq`.  Everything downstream of that trade — in particular the
range-enlargement discard, whose surviving term sits at scale
`x/(p⌊x/p⌋)` — lives at the real scale, where the `ℕ`-indexed form
does not typecheck. -/
theorem smoothed_sum_le_one_real (g : ℕ → ℝ) (hg : ∀ n, |g n| ≤ 1)
    (V : ℝ → ℝ) (M : ℝ) (hM : 0 < M)
    (hV0 : ∀ v, v ≤ 0 → V v = 0) (hVle : ∀ v, V v ≤ Real.exp (-v))
    (hVnn : ∀ v, 0 ≤ V v)
    (S : Finset ℕ) (hS1 : ∀ n ∈ S, 1 ≤ n) :
    |∑ n ∈ S, (g n/(n:ℝ)) * V (Real.log M - Real.log (n:ℝ))| ≤ 1 := by
  classical
  -- terms at or beyond the scale vanish
  have hvanish : ∀ n ∈ S, n ∉ S.filter (fun n : ℕ => (n:ℝ) < M) →
      (g n/(n:ℝ)) * V (Real.log M - Real.log (n:ℝ)) = 0 := by
    intro n hn hnot
    simp only [Finset.mem_filter, not_and, not_lt] at hnot
    have hMn : M ≤ (n:ℝ) := hnot hn
    have hle : Real.log M - Real.log (n:ℝ) ≤ 0 := by
      have := Real.log_le_log hM hMn
      linarith
    rw [hV0 _ hle, mul_zero]
  have hrestrict : (∑ n ∈ S, (g n/(n:ℝ)) * V (Real.log M - Real.log (n:ℝ)))
      = ∑ n ∈ S.filter (fun n : ℕ => (n:ℝ) < M),
          (g n/(n:ℝ)) * V (Real.log M - Real.log (n:ℝ)) :=
    (Finset.sum_subset (Finset.filter_subset _ _)
      (fun n hn hnot => hvanish n hn hnot)).symm
  -- each survivor is at most `1/M`
  have hterm : ∀ n ∈ S.filter (fun n : ℕ => (n:ℝ) < M),
      |(g n/(n:ℝ)) * V (Real.log M - Real.log (n:ℝ))| ≤ 1/M := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    have hn1 : 1 ≤ n := hS1 n hn.1
    have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
    have hVb : V (Real.log M - Real.log (n:ℝ)) ≤ (n:ℝ)/M := by
      refine le_trans (hVle _) (le_of_eq ?_)
      rw [neg_sub, Real.exp_sub, Real.exp_log hn0, Real.exp_log hM]
    rw [abs_mul, abs_div, abs_of_nonneg hn0.le, abs_of_nonneg (hVnn _)]
    have hstep : |g n|/(n:ℝ) * V (Real.log M - Real.log (n:ℝ))
        ≤ (1/(n:ℝ)) * ((n:ℝ)/M) :=
      mul_le_mul (div_le_div_of_nonneg_right (hg n) hn0.le) hVb
        (hVnn _) (by positivity)
    refine le_trans hstep (le_of_eq ?_)
    field_simp
  -- and there are at most `⌊M⌋ ≤ M` of them
  have hcard : ((S.filter (fun n : ℕ => (n:ℝ) < M)).card : ℝ) ≤ M := by
    have hsub : S.filter (fun n : ℕ => (n:ℝ) < M) ⊆ Finset.Icc 1 ⌊M⌋₊ := by
      intro n hn
      simp only [Finset.mem_filter] at hn
      rw [Finset.mem_Icc]
      exact ⟨hS1 n hn.1, Nat.le_floor hn.2.le⟩
    have h1 : ((S.filter (fun n : ℕ => (n:ℝ) < M)).card : ℝ)
        ≤ ((⌊M⌋₊ : ℕ):ℝ) := by
      have := Finset.card_le_card hsub
      simp only [Nat.card_Icc] at this
      have h2 : (S.filter (fun n : ℕ => (n:ℝ) < M)).card ≤ ⌊M⌋₊ := by omega
      exact_mod_cast h2
    exact le_trans h1 (Nat.floor_le hM.le)
  rw [hrestrict]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  simp only [Finset.sum_const, nsmul_eq_mul]
  calc ((S.filter (fun n : ℕ => (n:ℝ) < M)).card : ℝ) * (1/M)
      ≤ M * (1/M) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 1 := by field_simp

/-- **The master transition, to third order** (Track R, N121):
`Real.smoothTransition` has all three of its first derivatives
uniformly bounded by one absolute constant.

`exists_master_transition` stops at the second derivative, because the
Perron window's `M₂` was all the cheap-Halász main term needed.  §4's
tail estimate needs `M₃`: the second-order window tail `M₂/(2π²L)` is a
factor of `log x` short of what `Mtail` can afford, and only the
third-order bound `M₃/(8π³L²)` closes it (see `fourier_tail_cube_le`).

Since every Perron window scales from this transition, the third
derivative has to be bounded here or nowhere.  The proof is the
existing one with one more layer: derivatives of a function constant
off `[0,1]` vanish there, so each is continuous with compact support
and therefore attains a maximum.

The constant is not computed.  It is a single absolute number, and
every downstream threshold depends on it only through `C`. -/
theorem exists_master_transition_three :
    ∃ (σ : ℝ → ℝ) (C : ℝ), ContDiff ℝ ∞ σ
      ∧ (∀ v, 0 ≤ σ v ∧ σ v ≤ 1)
      ∧ (∀ v, v ≤ 0 → σ v = 0) ∧ (∀ v, 1 ≤ v → σ v = 1)
      ∧ 0 ≤ C
      ∧ (∀ v, |deriv σ v| ≤ C)
      ∧ (∀ v, |deriv (deriv σ) v| ≤ C)
      ∧ (∀ v, |deriv (deriv (deriv σ)) v| ≤ C) := by
  classical
  set σ : ℝ → ℝ := Real.smoothTransition with hσ_def
  have hsm : ContDiff ℝ ∞ σ := Real.smoothTransition.contDiff
  have hzero : ∀ v, v ≤ 0 → σ v = 0 := fun v hv =>
    Real.smoothTransition.zero_of_nonpos hv
  have hone : ∀ v, 1 ≤ v → σ v = 1 := fun v hv =>
    Real.smoothTransition.one_of_one_le hv
  -- a function locally constant off `[0,1]` has vanishing derivative there
  have hd_of_const : ∀ (g : ℝ → ℝ) (c₀ c₁ : ℝ),
      (∀ v, v < 0 → g v = c₀) → (∀ v, 1 < v → g v = c₁) →
      ∀ v, v < 0 ∨ 1 < v → deriv g v = 0 := by
    intro g c₀ c₁ hg0 hg1 v hv
    rcases hv with hv | hv
    · have heq : g =ᶠ[nhds v] (fun _ => c₀) :=
        Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Iio hv)
          (fun u hu => hg0 u hu)
      rw [heq.deriv_eq, deriv_const]
    · have heq : g =ᶠ[nhds v] (fun _ => c₁) :=
        Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Ioi hv)
          (fun u hu => hg1 u hu)
      rw [heq.deriv_eq, deriv_const]
  have hd1_zero : ∀ v, v < 0 ∨ 1 < v → deriv σ v = 0 :=
    hd_of_const σ 0 1 (fun v hv => hzero v hv.le) (fun v hv => hone v hv.le)
  have hd2_zero : ∀ v, v < 0 ∨ 1 < v → deriv (deriv σ) v = 0 :=
    hd_of_const (deriv σ) 0 0 (fun v hv => hd1_zero v (Or.inl hv))
      (fun v hv => hd1_zero v (Or.inr hv))
  have hd3_zero : ∀ v, v < 0 ∨ 1 < v → deriv (deriv (deriv σ)) v = 0 :=
    hd_of_const (deriv (deriv σ)) 0 0 (fun v hv => hd2_zero v (Or.inl hv))
      (fun v hv => hd2_zero v (Or.inr hv))
  -- each derivative is continuous
  have hsm1 : ContDiff ℝ ∞ (deriv σ) := by simpa using hsm.iterate_deriv 1
  have hsm2 : ContDiff ℝ ∞ (deriv (deriv σ)) := by
    simpa using hsm1.iterate_deriv 1
  have hsm3 : ContDiff ℝ ∞ (deriv (deriv (deriv σ))) := by
    simpa using hsm2.iterate_deriv 1
  -- and compactly supported
  have hcs : ∀ (g : ℝ → ℝ), (∀ v, v < 0 ∨ 1 < v → g v = 0) →
      HasCompactSupport g := by
    intro g hg
    refine HasCompactSupport.intro isCompact_Icc (K := Set.Icc (0:ℝ) 1) ?_
    intro v hv
    rw [Set.mem_Icc] at hv
    push_neg at hv
    by_cases h0 : v < 0
    · exact hg v (Or.inl h0)
    · push_neg at h0
      exact hg v (Or.inr (hv h0))
  -- so each attains a maximum
  have hbound : ∀ (g : ℝ → ℝ), Continuous g →
      (∀ v, v < 0 ∨ 1 < v → g v = 0) → ∃ Cg, ∀ v, |g v| ≤ Cg := by
    intro g hgc hg0
    obtain ⟨v₀, hv₀⟩ := Continuous.exists_forall_ge_of_hasCompactSupport
      hgc.abs ((hcs g hg0).abs)
    exact ⟨|g v₀|, hv₀⟩
  obtain ⟨C₁, hC₁⟩ := hbound _ hsm1.continuous hd1_zero
  obtain ⟨C₂, hC₂⟩ := hbound _ hsm2.continuous hd2_zero
  obtain ⟨C₃, hC₃⟩ := hbound _ hsm3.continuous hd3_zero
  refine ⟨σ, max C₁ (max C₂ C₃), hsm, ?_, hzero, hone, ?_, ?_, ?_, ?_⟩
  · intro v
    exact ⟨Real.smoothTransition.nonneg v, Real.smoothTransition.le_one v⟩
  · exact le_trans (abs_nonneg _) (le_trans (hC₁ 0) (le_max_left _ _))
  · intro v
    exact le_trans (hC₁ v) (le_max_left _ _)
  · intro v
    exact le_trans (hC₂ v) (le_trans (le_max_left _ _) (le_max_right _ _))
  · intro v
    exact le_trans (hC₃ v) (le_trans (le_max_right _ _) (le_max_right _ _))

/-- **Leibniz for `e^{−v}·g`, to third order** (Track R, N122): if `g`
has successive derivatives `g₁, g₂, g₃`, then

  `(e^{−v}·g)''' = e^{−v}·(g₃ − 3g₂ + 3g₁ − g)`.

Each differentiation sends `e^{−v}·h` to `e^{−v}·(h' − h)`, so the
alternating binomial coefficients accumulate in the bracket while the
prefactor stays positive — the sign pattern is `+ − + −` inside, not a
sign out front.

`exists_perron_window` computes `(e^{−v}·S)'' = e^{−v}(S₂ − 2S₁ + S)`
inline, on the way to `M₂`; the same computation one order further is
what `M₃` needs, and `M₃` is what §4's tail estimate requires
(`fourier_tail_cube_le` — the second-order tail is a factor of `log x`
short).

Stated abstractly in `g, g₁, g₂, g₃` rather than at the window's own
`S`, because the derivative bookkeeping and the *bounds* on `S`'s
derivatives are independent problems: this settles the shape, and the
`|S₃| ≲ C³/ρ³` estimate is separate.  Doing both at once is what makes
the `M₂` proof two hundred lines. -/
theorem iteratedDeriv_three_exp_neg_mul (g g₁ g₂ g₃ : ℝ → ℝ)
    (h1 : ∀ v, HasDerivAt g (g₁ v) v) (h2 : ∀ v, HasDerivAt g₁ (g₂ v) v)
    (h3 : ∀ v, HasDerivAt g₂ (g₃ v) v) :
    iteratedDeriv 3 (fun v => Real.exp (-v) * g v)
      = fun v => Real.exp (-v) * (g₃ v - 3*g₂ v + 3*g₁ v - g v) := by
  have hexp : ∀ v : ℝ, HasDerivAt (fun v : ℝ => Real.exp (-v))
      (-(Real.exp (-v))) v := by
    intro v
    have := (Real.hasDerivAt_exp (-v)).comp v ((hasDerivAt_id v).neg)
    simpa using this
  -- first derivative
  have hd1 : ∀ v, HasDerivAt (fun v => Real.exp (-v) * g v)
      (Real.exp (-v) * (g₁ v - g v)) v := by
    intro v
    have := (hexp v).mul (h1 v)
    convert this using 1
    ring
  -- second
  have hd2 : ∀ v, HasDerivAt (fun v => Real.exp (-v) * (g₁ v - g v))
      (Real.exp (-v) * (g₂ v - 2*g₁ v + g v)) v := by
    intro v
    have hs := (h2 v).sub (h1 v)
    have := (hexp v).mul hs
    convert this using 1
    simp only [Pi.sub_apply]
    ring
  -- third
  have hd3 : ∀ v, HasDerivAt
      (fun v => Real.exp (-v) * (g₂ v - 2*g₁ v + g v))
      (Real.exp (-v) * (g₃ v - 3*g₂ v + 3*g₁ v - g v)) v := by
    intro v
    have hs : HasDerivAt (fun v => g₂ v - 2*g₁ v + g v)
        (g₃ v - 2*g₂ v + g₁ v) v := by
      have := ((h3 v).sub ((h2 v).const_mul 2)).add (h1 v)
      convert this using 1
    have hfun : ((fun v : ℝ => Real.exp (-v))
        * fun v : ℝ => g₂ v - 2*g₁ v + g v)
        = fun v : ℝ => Real.exp (-v) * (g₂ v - 2*g₁ v + g v) := rfl
    have h2' := (hexp v).mul hs
    rw [hfun] at h2'
    convert h2' using 1
    ring
  -- assemble
  have hexpand : iteratedDeriv 3 (fun v => Real.exp (-v) * g v)
      = deriv (deriv (deriv (fun v => Real.exp (-v) * g v))) := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
  rw [hexpand]
  have he1 : deriv (fun v => Real.exp (-v) * g v)
      = fun v => Real.exp (-v) * (g₁ v - g v) :=
    funext fun v => (hd1 v).deriv
  rw [he1]
  have he2 : deriv (fun v => Real.exp (-v) * (g₁ v - g v))
      = fun v => Real.exp (-v) * (g₂ v - 2*g₁ v + g v) :=
    funext fun v => (hd2 v).deriv
  rw [he2]
  exact funext fun v => (hd3 v).deriv

/-- **The third-order window constant** (Track R, N123): with the
Perron window's derivative bounds,

  `|S₃ − 3S₂ + 3S₁ − S| ≤ 27(C+1)³/ρ³`.

The arithmetic the `M₃` bound rests on, packaged.  The hypotheses are
exactly the shapes the `M₂` proof already establishes for `S`, `S₁`,
`S₂` — each Leibniz term of `S^{(i)} = (σ(·/ρ)·(1−σ(·−a)))^{(i)}`
contributes `σ^{(j)}(v/ρ)/ρ^j` against `σ^{(i−j)}(v−a)`, so the
`ρ`-powers accumulate exactly as stated.

Collecting under `ρ ≤ 1` turns the whole alternating sum into
`(12C² + 14C + 1)/ρ³`, which `27(C+1)³/ρ³` dominates with room to
spare.  The constant is not sharp and does not need to be: it enters
`M₃` and thence `Mtail`, and the audit that fixes `ρ` only needs the
`ρ^{−3}` scaling.

Separated from the derivative formula deliberately.  This can be
checked before `S₃` is computed, and it is the part the `M₂` proof
spends most of its length on. -/
theorem alternating_three_bound (S S₁ S₂ S₃ C ρ : ℝ)
    (hC0 : 0 ≤ C) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hS : |S| ≤ 1) (hS₁ : |S₁| ≤ C/ρ + C)
    (hS₂ : |S₂| ≤ C/ρ^2 + 2*C^2/ρ + C)
    (hS₃ : |S₃| ≤ C/ρ^3 + 3*C^2/ρ^2 + 3*C^2/ρ + C) :
    |S₃ - 3*S₂ + 3*S₁ - S| ≤ 27*(C+1)^3/ρ^3 := by
  have hρ2 : (0:ℝ) < ρ^2 := by positivity
  have hρ3 : (0:ℝ) < ρ^3 := by positivity
  -- the triangle inequality on the alternating sum
  have htri : |S₃ - 3*S₂ + 3*S₁ - S| ≤ |S₃| + 3*|S₂| + 3*|S₁| + |S| := by
    have h3 : |3*S₂| = 3*|S₂| := by
      rw [abs_mul, show |(3:ℝ)| = 3 from by norm_num]
    have h3' : |3*S₁| = 3*|S₁| := by
      rw [abs_mul, show |(3:ℝ)| = 3 from by norm_num]
    calc |S₃ - 3*S₂ + 3*S₁ - S|
        ≤ |S₃ - 3*S₂ + 3*S₁| + |S| := abs_sub _ _
      _ ≤ (|S₃ - 3*S₂| + |3*S₁|) + |S| := by
          linarith [abs_add_le (S₃ - 3*S₂) (3*S₁)]
      _ ≤ ((|S₃| + |3*S₂|) + |3*S₁|) + |S| := by
          linarith [abs_sub S₃ (3*S₂)]
      _ = |S₃| + 3*|S₂| + 3*|S₁| + |S| := by rw [h3, h3']
  refine le_trans htri ?_
  -- collect the four bounds
  have hsum : |S₃| + 3*|S₂| + 3*|S₁| + |S|
      ≤ (C/ρ^3 + 3*C^2/ρ^2 + 3*C^2/ρ + C)
        + 3*(C/ρ^2 + 2*C^2/ρ + C) + 3*(C/ρ + C) + 1 := by
    linarith [hS, hS₁, hS₂, hS₃]
  refine le_trans hsum ?_
  -- clear the denominators once, then compare coefficient by coefficient
  have hρne : ρ ≠ 0 := ne_of_gt hρ0
  rw [le_div_iff₀ hρ3]
  have hexp : ((C/ρ^3 + 3*C^2/ρ^2 + 3*C^2/ρ + C)
      + 3*(C/ρ^2 + 2*C^2/ρ + C) + 3*(C/ρ + C) + 1) * ρ^3
      = C + 3*C^2*ρ + 9*C^2*ρ^2 + 7*C*ρ^3 + 3*C*ρ + 3*C*ρ^2 + ρ^3 := by
    field_simp
    ring
  rw [hexp]
  -- every power of `ρ` is at most `1`
  have hp1 : ρ^1 ≤ 1 := by simpa using hρ1
  have hp2 : ρ^2 ≤ 1 := by nlinarith [hρ0.le, hρ1]
  have hp3 : ρ^3 ≤ 1 := by nlinarith [hρ0.le, hρ1, hp2]
  have hC2 : (0:ℝ) ≤ C^2 := sq_nonneg C
  nlinarith [hC0, hC2, hp1, hp2, hp3, hρ0.le, pow_nonneg hC0 3,
    mul_nonneg hC0 hC0]

/-- **A Leibniz term of the window's derivatives** (Track R, N124): for
`0 < ρ`, `|u| ≤ B`, `|w| ≤ D` and `j : ℕ`,

  `|u/ρ^j · w| ≤ B·D/ρ^j`.

Every term of `S^{(i)} = (σ(·/ρ)·(1−σ(·−a)))^{(i)}` has this shape: the
chain rule puts `σ^{(j)}(v/ρ)` over `ρ^j`, and the other factor is some
`σ^{(i−j)}(v−a)` or `1−σ(v−a)`, each bounded by `C` or `1`.

The `M₂` proof does this inline four times, at `j = 0, 1, 2`, with the
`abs_mul`/`abs_div`/`abs_of_pos`/`mul_le_mul` dance written out each
time; `M₃` needs it four more times at `j = 0, 1, 2, 3`.  Extracting it
once turns each of those into a single `exact`.

Stated with `ρ^j` rather than a fixed power so the same lemma covers
every order, which is what makes it worth extracting rather than
copying. -/
theorem abs_div_pow_mul_le (u w B D ρ : ℝ) (j : ℕ) (hρ0 : 0 < ρ)
    (hu : |u| ≤ B) (hw : |w| ≤ D) :
    |u/ρ^j * w| ≤ B*D/ρ^j := by
  have hρj : (0:ℝ) < ρ^j := by positivity
  have hB0 : (0:ℝ) ≤ B := le_trans (abs_nonneg u) hu
  rw [abs_mul, abs_div, abs_of_pos hρj]
  calc |u|/ρ^j * |w| ≤ B/ρ^j * D := by
        refine mul_le_mul ?_ hw (abs_nonneg _) (by positivity)
        exact div_le_div_of_nonneg_right hu hρj.le
    _ = B*D/ρ^j := by ring

/-- **The third derivative of the window's cutoff** (Track R, N125):
for the four Leibniz terms of `S₃`,

  `|t₃/ρ³·w₀ − 3·(t₂/ρ²)·w₁ − 3·(t₁/ρ)·w₂ − t₀·w₃|`
  `  ≤ C/ρ³ + 3C²/ρ² + 3C²/ρ + C`,

given `|tⱼ| ≤ C` for `j ≥ 1`, `|t₀| ≤ 1`, `|w₀| ≤ 1` and `|wⱼ| ≤ C`
for `j ≥ 1`.

`S = σ(·/ρ)·(1 − σ(·−a))`, so `S₃` is exactly this alternating
combination with `tⱼ = σ^{(j)}(v/ρ)`, `w₀ = 1 − σ(v−a)` and
`wⱼ = −σ^{(j)}(v−a)`.  Four applications of `abs_div_pow_mul_le` at
`j = 3, 2, 1, 0`, chained by the triangle inequality.

This is precisely `alternating_three_bound`'s `hS₃` hypothesis, so with
it the `M₃` constant follows from lemmas already on main; what is left
is the derivative *formula* `hS'''at` and the integration.

Stated over abstract `tⱼ, wⱼ` rather than at `σ` itself, for the same
reason as the term estimate: the shape is independent of which
transition is used, and separating it keeps the chain-rule bookkeeping
out of the arithmetic. -/
theorem abs_S_three_le (t₀ t₁ t₂ t₃ w₀ w₁ w₂ w₃ C ρ : ℝ)
    (hρ0 : 0 < ρ)
    (ht₀ : |t₀| ≤ 1) (ht₁ : |t₁| ≤ C) (ht₂ : |t₂| ≤ C) (ht₃ : |t₃| ≤ C)
    (hw₀ : |w₀| ≤ 1) (hw₁ : |w₁| ≤ C) (hw₂ : |w₂| ≤ C) (hw₃ : |w₃| ≤ C) :
    |t₃/ρ^3 * w₀ - 3*(t₂/ρ^2 * w₁) - 3*(t₁/ρ^1 * w₂) - t₀/ρ^0 * w₃|
      ≤ C/ρ^3 + 3*C^2/ρ^2 + 3*C^2/ρ + C := by
  -- the four terms
  have e₃ : |t₃/ρ^3 * w₀| ≤ C*1/ρ^3 :=
    abs_div_pow_mul_le t₃ w₀ C 1 ρ 3 hρ0 ht₃ hw₀
  have e₂ : |t₂/ρ^2 * w₁| ≤ C*C/ρ^2 :=
    abs_div_pow_mul_le t₂ w₁ C C ρ 2 hρ0 ht₂ hw₁
  have e₁ : |t₁/ρ^1 * w₂| ≤ C*C/ρ^1 :=
    abs_div_pow_mul_le t₁ w₂ C C ρ 1 hρ0 ht₁ hw₂
  have e₀ : |t₀/ρ^0 * w₃| ≤ 1*C/ρ^0 :=
    abs_div_pow_mul_le t₀ w₃ 1 C ρ 0 hρ0 ht₀ hw₃
  -- chain the triangle inequality
  have h3 : |3*(t₂/ρ^2 * w₁)| = 3*|t₂/ρ^2 * w₁| := by
    rw [abs_mul, show |(3:ℝ)| = 3 from by norm_num]
  have h3' : |3*(t₁/ρ^1 * w₂)| = 3*|t₁/ρ^1 * w₂| := by
    rw [abs_mul, show |(3:ℝ)| = 3 from by norm_num]
  have htri : |t₃/ρ^3 * w₀ - 3*(t₂/ρ^2 * w₁) - 3*(t₁/ρ^1 * w₂)
        - t₀/ρ^0 * w₃|
      ≤ |t₃/ρ^3 * w₀| + 3*|t₂/ρ^2 * w₁| + 3*|t₁/ρ^1 * w₂|
        + |t₀/ρ^0 * w₃| := by
    calc |t₃/ρ^3 * w₀ - 3*(t₂/ρ^2 * w₁) - 3*(t₁/ρ^1 * w₂) - t₀/ρ^0 * w₃|
        ≤ |t₃/ρ^3 * w₀ - 3*(t₂/ρ^2 * w₁) - 3*(t₁/ρ^1 * w₂)|
            + |t₀/ρ^0 * w₃| := abs_sub _ _
      _ ≤ (|t₃/ρ^3 * w₀ - 3*(t₂/ρ^2 * w₁)| + |3*(t₁/ρ^1 * w₂)|)
            + |t₀/ρ^0 * w₃| := by
          linarith [abs_sub (t₃/ρ^3 * w₀ - 3*(t₂/ρ^2 * w₁)) (3*(t₁/ρ^1 * w₂))]
      _ ≤ ((|t₃/ρ^3 * w₀| + |3*(t₂/ρ^2 * w₁)|) + |3*(t₁/ρ^1 * w₂)|)
            + |t₀/ρ^0 * w₃| := by
          linarith [abs_sub (t₃/ρ^3 * w₀) (3*(t₂/ρ^2 * w₁))]
      _ = |t₃/ρ^3 * w₀| + 3*|t₂/ρ^2 * w₁| + 3*|t₁/ρ^1 * w₂|
            + |t₀/ρ^0 * w₃| := by rw [h3, h3']
  refine le_trans htri ?_
  -- collect: normalise the powers in each bound
  have e₃' : |t₃/ρ^3 * w₀| ≤ C/ρ^3 := by
    refine le_trans e₃ (le_of_eq ?_); ring
  have e₂' : |t₂/ρ^2 * w₁| ≤ C^2/ρ^2 := by
    refine le_trans e₂ (le_of_eq ?_); ring
  have e₁' : |t₁/ρ^1 * w₂| ≤ C^2/ρ := by
    refine le_trans e₁ (le_of_eq ?_); rw [pow_one]; ring
  have e₀' : |t₀/ρ^0 * w₃| ≤ C := by
    refine le_trans e₀ (le_of_eq ?_); rw [pow_zero]; ring
  have r2 : 3*C^2/ρ^2 = 3*(C^2/ρ^2) := by ring
  have r3 : 3*C^2/ρ = 3*(C^2/ρ) := by ring
  linarith [e₀', e₁', e₂', e₃', r2.le, r2.ge, r3.le, r3.ge]

/-- **The window's two chain rules** (Track R, N126): for `ρ ≠ 0` and
differentiable `g`,

  `(v ↦ g(v/ρ))' = g'(v/ρ)/ρ`  and  `(v ↦ g(v−a))' = g'(v−a)`.

The two substitutions `S = σ(·/ρ)·(1 − σ(·−a))` is built from, so every
derivative of `S` is assembled from these by the product rule.

`exists_perron_window` proves both inline as `hσ_at`/`hσ_at2` while
computing `S₁` and `S₂`; `S₃` needs them again, and a fourth
application each.  Extracting them removes the `HasDerivAt.comp`
plumbing from the third-order computation, which is otherwise the
bulkiest part of it.

Stated for arbitrary differentiable `g` rather than for `σ` and its
derivatives separately, since all four uses instantiate the same
statement. -/
theorem hasDerivAt_comp_div_const (g : ℝ → ℝ) (hg : Differentiable ℝ g)
    (ρ : ℝ) (v : ℝ) :
    HasDerivAt (fun v : ℝ => g (v/ρ)) (deriv g (v/ρ) / ρ) v := by
  have hout : HasDerivAt g (deriv g (v/ρ)) (v/ρ) := (hg (v/ρ)).hasDerivAt
  have hin : HasDerivAt (fun v : ℝ => v/ρ) (1/ρ) v := by
    simpa using (hasDerivAt_id v).div_const ρ
  have := hout.comp v hin
  convert this using 1
  ring

/-- The shift substitution — see `hasDerivAt_comp_div_const`. -/
theorem hasDerivAt_comp_sub_const (g : ℝ → ℝ) (hg : Differentiable ℝ g)
    (a : ℝ) (v : ℝ) :
    HasDerivAt (fun v : ℝ => g (v - a)) (deriv g (v - a)) v := by
  have hout : HasDerivAt g (deriv g (v - a)) (v - a) := (hg (v - a)).hasDerivAt
  have hin : HasDerivAt (fun v : ℝ => v - a) 1 v := (hasDerivAt_id v).sub_const a
  have := hout.comp v hin
  simpa using this

/-- **The window cutoff's third derivative** (Track R, N127): for
`ρ ≠ 0` and `σ` three times differentiable, the second derivative of
`S = σ(·/ρ)·(1 − σ(·−a))` differentiates to

  `S₃ = σ'''(v/ρ)/ρ³·(1−σ(v−a)) − 3(σ''(v/ρ)/ρ²)·σ'(v−a)`
  `     − 3(σ'(v/ρ)/ρ)·σ''(v−a) − σ(v/ρ)·σ'''(v−a)`.

Differentiating `S₂` term by term with the product rule over the two
chain rules of `hasDerivAt_comp_div_const` and
`hasDerivAt_comp_sub_const`.  The binomial pattern `1, 3, 3, 1` appears
because `S` is a product of exactly two factors, each depending on `v`
through one substitution.

Stated as a `HasDerivAt` of the explicit `S₂` rather than of
`iteratedDeriv 2 S`, matching how `exists_perron_window` carries its
derivative chain: the `M₂` proof keeps `S₁` and `S₂` as named functions
and only converts to `iteratedDeriv` at the very end.  Following that
convention means this composes with the existing chain directly.

With `abs_S_three_le` this closes the `S`-side of `M₃`; what remains is
the integration. -/
theorem hasDerivAt_S_three (σ : ℝ → ℝ) (hσd : Differentiable ℝ σ)
    (hσd' : Differentiable ℝ (deriv σ))
    (hσd'' : Differentiable ℝ (deriv (deriv σ)))
    (ρ a : ℝ) (hρ : ρ ≠ 0) (v : ℝ) :
    HasDerivAt
      (fun v : ℝ => deriv (deriv σ) (v/ρ) / ρ^2 * (1 - σ (v - a))
        - 2 * (deriv σ (v/ρ) / ρ) * deriv σ (v - a)
        - σ (v/ρ) * deriv (deriv σ) (v - a))
      (deriv (deriv (deriv σ)) (v/ρ) / ρ^3 * (1 - σ (v - a))
        - 3 * (deriv (deriv σ) (v/ρ) / ρ^2) * deriv σ (v - a)
        - 3 * (deriv σ (v/ρ) / ρ) * deriv (deriv σ) (v - a)
        - σ (v/ρ) * deriv (deriv (deriv σ)) (v - a)) v := by
  -- the six substitution derivatives
  have h0 : HasDerivAt (fun v : ℝ => σ (v/ρ)) (deriv σ (v/ρ) / ρ) v :=
    hasDerivAt_comp_div_const σ hσd ρ v
  have h1 : HasDerivAt (fun v : ℝ => deriv σ (v/ρ))
      (deriv (deriv σ) (v/ρ) / ρ) v :=
    hasDerivAt_comp_div_const (deriv σ) hσd' ρ v
  have h2 : HasDerivAt (fun v : ℝ => deriv (deriv σ) (v/ρ))
      (deriv (deriv (deriv σ)) (v/ρ) / ρ) v :=
    hasDerivAt_comp_div_const (deriv (deriv σ)) hσd'' ρ v
  have k0 : HasDerivAt (fun v : ℝ => σ (v - a)) (deriv σ (v - a)) v :=
    hasDerivAt_comp_sub_const σ hσd a v
  have k1 : HasDerivAt (fun v : ℝ => deriv σ (v - a))
      (deriv (deriv σ) (v - a)) v :=
    hasDerivAt_comp_sub_const (deriv σ) hσd' a v
  have k2 : HasDerivAt (fun v : ℝ => deriv (deriv σ) (v - a))
      (deriv (deriv (deriv σ)) (v - a)) v :=
    hasDerivAt_comp_sub_const (deriv (deriv σ)) hσd'' a v
  -- the complement factor
  have kc : HasDerivAt (fun v : ℝ => 1 - σ (v - a))
      (-(deriv σ (v - a))) v := by
    simpa using (hasDerivAt_const v (1:ℝ)).sub k0
  -- differentiate the three products of `S₂`
  have hA : HasDerivAt
      (fun v : ℝ => deriv (deriv σ) (v/ρ) / ρ^2 * (1 - σ (v - a)))
      (deriv (deriv (deriv σ)) (v/ρ) / ρ / ρ^2 * (1 - σ (v - a))
        + deriv (deriv σ) (v/ρ) / ρ^2 * (-(deriv σ (v - a)))) v :=
    (h2.div_const (ρ^2)).mul kc
  have hB : HasDerivAt
      (fun v : ℝ => 2 * (deriv σ (v/ρ) / ρ) * deriv σ (v - a))
      ((2 * (deriv (deriv σ) (v/ρ) / ρ / ρ)) * deriv σ (v - a)
        + 2 * (deriv σ (v/ρ) / ρ) * deriv (deriv σ) (v - a)) v :=
    (((h1.div_const ρ).const_mul 2)).mul k1
  have hC : HasDerivAt
      (fun v : ℝ => σ (v/ρ) * deriv (deriv σ) (v - a))
      (deriv σ (v/ρ) / ρ * deriv (deriv σ) (v - a)
        + σ (v/ρ) * deriv (deriv (deriv σ)) (v - a)) v :=
    h0.mul k2
  have := (hA.sub hB).sub hC
  convert this using 1
  field_simp
  ring

/-- **From an exponential majorant to a derivative mass** (Track R,
N128): if `g` is continuous with compact support and

  `|g v| ≤ 1_{[0,∞)}(v)·K·e^{−v}`  pointwise,

then `∫|g| ≤ K`.

The step that turns the Perron window's pointwise derivative bounds
into the masses `M₂`, `M₃` the tail estimates consume.  The whole
content is `∫_{[0,∞)} e^{−v} dv = 1`: the majorant is `K` times a
probability density, so no scale enters and the constant passes
through unchanged.

`exists_perron_window` does this inline for `M₂`; `M₃` needs it again
at one order higher, with the same `K·e^{−v}` shape and a different
`K`.  Extracting it means the third-order bound is an application
rather than a repeat of the measure-theoretic bookkeeping.

Compact support is what makes `|g|` integrable; the majorant alone
would not, since it is only an upper bound. -/
theorem integral_abs_le_of_indicator_exp (g : ℝ → ℝ) (hg : Continuous g)
    (hcs : HasCompactSupport g) (K : ℝ)
    (hpt : ∀ v, |g v|
      ≤ Set.indicator (Set.Ici (0:ℝ)) (fun v => K * Real.exp (-v)) v) :
    ∫ v, |g v| ≤ K := by
  have hK0 : 0 ≤ K := by
    have h := hpt 0
    rw [Set.indicator_of_mem (Set.mem_Ici.mpr le_rfl)] at h
    simp only [neg_zero, Real.exp_zero, mul_one] at h
    exact le_trans (abs_nonneg _) h
  -- `|g|` is integrable
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hcs
  have habs : Integrable (fun v => |g v|) := hgi.abs
  -- the majorant is integrable, with integral `K`
  have hexp : IntegrableOn (fun v : ℝ => Real.exp (-v)) (Set.Ici 0) := by
    have := exp_neg_integrableOn_Ioi (0:ℝ) (by norm_num : (0:ℝ) < 1)
    simpa using this.congr_set_ae Ioi_ae_eq_Ici.symm
  have hmaji : Integrable
      (Set.indicator (Set.Ici (0:ℝ)) (fun v => K * Real.exp (-v))) := by
    rw [integrable_indicator_iff measurableSet_Ici]
    exact (hexp.const_mul K)
  have hmaj_int : (∫ v, Set.indicator (Set.Ici (0:ℝ))
      (fun v => K * Real.exp (-v)) v) = K := by
    rw [integral_indicator measurableSet_Ici, integral_const_mul]
    have hone : (∫ v in Set.Ici (0:ℝ), Real.exp (-v)) = 1 := by
      have h := integral_exp_neg_Ioi (0:ℝ)
      rw [neg_zero, Real.exp_zero] at h
      rw [← h]
      exact setIntegral_congr_set Ioi_ae_eq_Ici.symm
    rw [hone, mul_one]
  calc ∫ v, |g v|
      ≤ ∫ v, Set.indicator (Set.Ici (0:ℝ))
          (fun v => K * Real.exp (-v)) v :=
        integral_mono habs hmaji hpt
    _ = K := hmaj_int
end ExpSums

end MoltResearch
