import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

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

end ExpSums

end MoltResearch
