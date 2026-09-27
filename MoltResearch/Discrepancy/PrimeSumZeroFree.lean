import MoltResearch.Discrepancy.PerronWindow
import MoltResearch.Discrepancy.ZeroFreeRegion
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Chebyshev

/-!
# Prime sums from a zero-free region

This leaf starts the Mellin-shift route to the prime large-values estimate.
The first unit constructs a fixed smooth window in logarithmic coordinates.
Its Mellin transform is holomorphic on the whole plane and has uniform
quadratic decay on vertical lines in the strip used by the contour shift.
-/

namespace MoltResearch

namespace ExpSums

open Asymptotics Complex Filter Function MeasureTheory Real Set
open scoped ContDiff FourierTransform Topology

/-- A plateau profile made from two copies of one master transition.  It is
supported in `[-1/2, 3/2]` and is identically one on `[0, 1]`. -/
noncomputable def primeMellinProfile (S : ℝ → ℝ) (v : ℝ) : ℝ :=
  S (2 * v + 1) * S (3 - 2 * v)

/-- The profile at multiplicative scale `P`. -/
noncomputable def primeMellinWindow (S : ℝ → ℝ) (P x : ℝ) : ℝ :=
  primeMellinProfile S (Real.log (x / P) / Real.log 2)

/-- The Mellin transform of the fixed multiplicative window. -/
noncomputable def primeMellinTransform (S : ℝ → ℝ) (P : ℝ) (s : ℂ) : ℂ :=
  mellin (fun x : ℝ => (primeMellinWindow S P x : ℂ)) s

/-- The real logarithmic-coordinate function whose Fourier transform is a
vertical value of `primeMellinTransform`. -/
noncomputable def primeMellinVerticalWindow
    (S : ℝ → ℝ) (P α u : ℝ) : ℝ :=
  Real.exp (-α * u) *
    primeMellinProfile S ((-u - Real.log P) / Real.log 2)

/-- The fixed profile is smooth, lies in `[0,1]`, is supported in
`[-1/2, 3/2]`, and equals one on `[0,1]`. -/
theorem primeMellinProfile_properties (S : ℝ → ℝ)
    (hSs : ContDiff ℝ ∞ S)
    (hS01 : ∀ v, 0 ≤ S v ∧ S v ≤ 1)
    (hS0 : ∀ v, v ≤ 0 → S v = 0)
    (hS1 : ∀ v, 1 ≤ v → S v = 1) :
    ContDiff ℝ ∞ (primeMellinProfile S) ∧
      (∀ v, 0 ≤ primeMellinProfile S v ∧ primeMellinProfile S v ≤ 1) ∧
      (∀ v, v ≤ -(1 / 2) → primeMellinProfile S v = 0) ∧
      (∀ v, 3 / 2 ≤ v → primeMellinProfile S v = 0) ∧
      (∀ v, 0 ≤ v → v ≤ 1 → primeMellinProfile S v = 1) := by
  have hleft : ContDiff ℝ ∞ (fun v : ℝ => S (2 * v + 1)) := by fun_prop
  have hright : ContDiff ℝ ∞ (fun v : ℝ => S (3 - 2 * v)) := by fun_prop
  refine ⟨hleft.mul hright, ?_, ?_, ?_, ?_⟩
  · intro v
    exact ⟨mul_nonneg (hS01 _).1 (hS01 _).1,
      mul_le_one₀ (hS01 _).2 (hS01 _).1 (hS01 _).2⟩
  · intro v hv
    rw [primeMellinProfile, hS0 _ (by linarith), zero_mul]
  · intro v hv
    have hz : S (3 - 2 * v) = 0 := hS0 _ (by linarith)
    rw [primeMellinProfile, hz, mul_zero]
  · intro v hv1 hv2
    rw [primeMellinProfile, hS1 _ (by linarith), hS1 _ (by linarith), one_mul]

/-- The first derivative of the fixed profile. -/
theorem hasDerivAt_primeMellinProfile (S : ℝ → ℝ)
    (hSs : ContDiff ℝ ∞ S) (v : ℝ) :
    HasDerivAt (primeMellinProfile S)
      (2 * deriv S (2 * v + 1) * S (3 - 2 * v) -
        2 * S (2 * v + 1) * deriv S (3 - 2 * v)) v := by
  have hSd (x : ℝ) : HasDerivAt S (deriv S x) x :=
    (hSs.differentiable (by simp) x).hasDerivAt
  have hleft : HasDerivAt (fun x : ℝ => S (2 * x + 1))
      (2 * deriv S (2 * v + 1)) v := by
    convert! (hSd (2 * v + 1)).comp v
      ((hasDerivAt_const v 2).mul (hasDerivAt_id v) |>.add_const 1) using 1 <;>
      ring
  have hright : HasDerivAt (fun x : ℝ => S (3 - 2 * x))
      (-2 * deriv S (3 - 2 * v)) v := by
    convert! (hSd (3 - 2 * v)).comp v
      ((hasDerivAt_const v 3).sub ((hasDerivAt_const v 2).mul (hasDerivAt_id v))) using 1 <;>
      ring
  convert! hleft.mul hright using 1
  · ring

/-- The second derivative of the fixed profile. -/
theorem iteratedDeriv_two_primeMellinProfile (S : ℝ → ℝ)
    (hSs : ContDiff ℝ ∞ S) :
    iteratedDeriv 2 (primeMellinProfile S) = fun v =>
      4 * deriv (deriv S) (2 * v + 1) * S (3 - 2 * v) -
      8 * deriv S (2 * v + 1) * deriv S (3 - 2 * v) +
      4 * S (2 * v + 1) * deriv (deriv S) (3 - 2 * v) := by
  have hS1s : ContDiff ℝ ∞ (deriv S) := by
    simpa using hSs.iterate_deriv 1
  have hSd (x : ℝ) : HasDerivAt S (deriv S x) x :=
    (hSs.differentiable (by simp) x).hasDerivAt
  have hSdd (x : ℝ) : HasDerivAt (deriv S) (deriv (deriv S) x) x :=
    (hS1s.differentiable (by simp) x).hasDerivAt
  have hfirst : deriv (primeMellinProfile S) = fun v =>
      2 * deriv S (2 * v + 1) * S (3 - 2 * v) -
        2 * S (2 * v + 1) * deriv S (3 - 2 * v) := by
    funext v
    exact (hasDerivAt_primeMellinProfile S hSs v).deriv
  have htwo : iteratedDeriv 2 (primeMellinProfile S) =
      deriv (deriv (primeMellinProfile S)) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [htwo, hfirst]
  funext v
  have hA : HasDerivAt (fun x : ℝ => deriv S (2 * x + 1))
      (2 * deriv (deriv S) (2 * v + 1)) v := by
    convert! (hSdd (2 * v + 1)).comp v
      ((hasDerivAt_const v 2).mul (hasDerivAt_id v) |>.add_const 1) using 1 <;>
      ring
  have hB : HasDerivAt (fun x : ℝ => S (3 - 2 * x))
      (-2 * deriv S (3 - 2 * v)) v := by
    convert! (hSd (3 - 2 * v)).comp v
      ((hasDerivAt_const v 3).sub ((hasDerivAt_const v 2).mul (hasDerivAt_id v))) using 1 <;>
      ring
  have hC : HasDerivAt (fun x : ℝ => S (2 * x + 1))
      (2 * deriv S (2 * v + 1)) v := by
    convert! (hSd (2 * v + 1)).comp v
      ((hasDerivAt_const v 2).mul (hasDerivAt_id v) |>.add_const 1) using 1 <;>
      ring
  have hD : HasDerivAt (fun x : ℝ => deriv S (3 - 2 * x))
      (-2 * deriv (deriv S) (3 - 2 * v)) v := by
    convert! (hSdd (3 - 2 * v)).comp v
      ((hasDerivAt_const v 3).sub ((hasDerivAt_const v 2).mul (hasDerivAt_id v))) using 1 <;>
      ring
  have hterm1 := ((hA.const_mul 2).mul hB)
  have hterm2 := ((hC.const_mul 2).mul hD)
  have hderiv := hterm1.sub hterm2
  change deriv
    (((fun y : ℝ => 2 * deriv S (2 * y + 1)) * fun x : ℝ => S (3 - 2 * x)) -
      ((fun y : ℝ => 2 * S (2 * y + 1)) * fun x : ℝ => deriv S (3 - 2 * x))) v = _
  rw [hderiv.deriv]
  ring

/-- Uniform first- and second-derivative bounds for the fixed profile. -/
theorem primeMellinProfile_deriv_bounds (S : ℝ → ℝ) (C : ℝ)
    (hSs : ContDiff ℝ ∞ S)
    (hS01 : ∀ v, 0 ≤ S v ∧ S v ≤ 1)
    (hC0 : 0 ≤ C)
    (hC1 : ∀ v, |deriv S v| ≤ C)
    (hC2 : ∀ v, |deriv (deriv S) v| ≤ C) :
    (∀ v, |deriv (primeMellinProfile S) v| ≤ 6 * C) ∧
      (∀ v, |iteratedDeriv 2 (primeMellinProfile S) v| ≤ 18 * C + 18 * C ^ 2) := by
  constructor
  · intro v
    rw [(hasDerivAt_primeMellinProfile S hSs v).deriv]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_mul]
    norm_num
    have hL0 := (hS01 (2 * v + 1)).1
    have hL1 := (hS01 (2 * v + 1)).2
    have hR0 := (hS01 (3 - 2 * v)).1
    have hR1 := (hS01 (3 - 2 * v)).2
    calc
      2 * |deriv S (2 * v + 1)| * |S (3 - 2 * v)| +
          2 * |S (2 * v + 1)| * |deriv S (3 - 2 * v)|
          ≤ 2 * C * 1 + 2 * 1 * C := by
            rw [abs_of_nonneg hL0, abs_of_nonneg hR0]
            gcongr <;> first | exact hC1 _ | assumption
      _ ≤ 6 * C := by linarith
  · intro v
    rw [iteratedDeriv_two_primeMellinProfile S hSs]
    refine (abs_add_le _ _).trans
      ((add_le_add (abs_sub _ _) (le_refl _)).trans ?_)
    simp only [abs_mul]
    norm_num
    have hL0 := (hS01 (2 * v + 1)).1
    have hL1 := (hS01 (2 * v + 1)).2
    have hR0 := (hS01 (3 - 2 * v)).1
    have hR1 := (hS01 (3 - 2 * v)).2
    rw [abs_of_nonneg hL0, abs_of_nonneg hR0]
    calc
      4 * |deriv (deriv S) (2 * v + 1)| * S (3 - 2 * v) +
            8 * |deriv S (2 * v + 1)| * |deriv S (3 - 2 * v)| +
          4 * S (2 * v + 1) * |deriv (deriv S) (3 - 2 * v)|
          ≤ 4 * C * 1 + 8 * C * C + 4 * 1 * C := by
            gcongr <;> first | exact hC1 _ | exact hC2 _ | assumption
      _ ≤ 18 * C + 18 * C ^ 2 := by nlinarith [sq_nonneg C]

/-- The logarithmic-coordinate window is smooth and supported on an interval
of length `2 * log 2`. -/
theorem primeMellinVerticalWindow_smooth_support (S : ℝ → ℝ) (P α : ℝ)
    (hSs : ContDiff ℝ ∞ S)
    (hS01 : ∀ v, 0 ≤ S v ∧ S v ≤ 1)
    (hS0 : ∀ v, v ≤ 0 → S v = 0)
    (hS1 : ∀ v, 1 ≤ v → S v = 1) :
    ContDiff ℝ ∞ (primeMellinVerticalWindow S P α) ∧
      HasCompactSupport (primeMellinVerticalWindow S P α) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp := primeMellinProfile_properties S hSs hS01 hS0 hS1
  have hsmooth : ContDiff ℝ ∞ (primeMellinVerticalWindow S P α) := by
    have he : ContDiff ℝ ∞ (fun u : ℝ => Real.exp (-α * u)) := by fun_prop
    have hq : ContDiff ℝ ∞
        (fun u : ℝ => (-u - Real.log P) / Real.log 2) := by fun_prop
    have hprof := hp.1.comp hq
    simpa only [primeMellinVerticalWindow, Function.comp_apply] using! he.mul hprof
  refine ⟨hsmooth, ?_⟩
  refine HasCompactSupport.intro
    (isCompact_Icc (a := -Real.log P - (3 / 2) * Real.log 2)
      (b := -Real.log P + (1 / 2) * Real.log 2)) ?_
  intro u hu
  rw [Set.mem_Icc] at hu
  simp only [not_and_or, not_le] at hu
  rcases hu with hu | hu
  · have hv : 3 / 2 ≤ (-u - Real.log P) / Real.log 2 := by
      rw [le_div_iff₀ hlog2]
      linarith
    rw [primeMellinVerticalWindow, hp.2.2.2.1 _ hv, mul_zero]
  · have hv : (-u - Real.log P) / Real.log 2 ≤ -(1 / 2) := by
      rw [div_le_iff₀ hlog2]
      linarith
    rw [primeMellinVerticalWindow, hp.2.2.1 _ hv, mul_zero]

/-- Exact second derivative of the vertical window. -/
theorem iteratedDeriv_two_primeMellinVerticalWindow (S : ℝ → ℝ) (P α : ℝ)
    (hSs : ContDiff ℝ ∞ S) :
    iteratedDeriv 2 (primeMellinVerticalWindow S P α) = fun u =>
      Real.exp (-α * u) *
        (α ^ 2 * primeMellinProfile S ((-u - Real.log P) / Real.log 2) +
          (2 * α / Real.log 2) *
            deriv (primeMellinProfile S) ((-u - Real.log P) / Real.log 2) +
          (1 / (Real.log 2) ^ 2) *
            iteratedDeriv 2 (primeMellinProfile S)
              ((-u - Real.log P) / Real.log 2)) := by
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hφs : ContDiff ℝ ∞ (primeMellinProfile S) := by
    unfold primeMellinProfile
    fun_prop
  let q : ℝ → ℝ := fun u => (-u - Real.log P) / Real.log 2
  let A : ℝ → ℝ := fun u => primeMellinProfile S (q u)
  let A₁ : ℝ → ℝ := fun u =>
    (-deriv (primeMellinProfile S) (q u)) / Real.log 2
  let A₂ : ℝ → ℝ := fun u =>
    iteratedDeriv 2 (primeMellinProfile S) (q u) / (Real.log 2) ^ 2
  have hq (u : ℝ) : HasDerivAt q (-(1 / Real.log 2)) u := by
    dsimp [q]
    convert! ((hasDerivAt_id u).neg.sub_const (Real.log P)).div_const (Real.log 2) using 1
    field_simp
  have hA (u : ℝ) : HasDerivAt A (A₁ u) u := by
    have hφ := (hφs.differentiable (by simp) (q u)).hasDerivAt
    convert! hφ.comp u (hq u) using 1 <;> dsimp [A, A₁] <;> field_simp
  have hφ1s : ContDiff ℝ ∞ (deriv (primeMellinProfile S)) := by
    simpa using hφs.iterate_deriv 1
  have hA₁ (u : ℝ) : HasDerivAt A₁ (A₂ u) u := by
    have hφ := (hφ1s.differentiable (by simp) (q u)).hasDerivAt
    have hc := hφ.comp u (hq u)
    have hn := hc.neg.div_const (Real.log 2)
    have htwoφ : iteratedDeriv 2 (primeMellinProfile S) =
        deriv (deriv (primeMellinProfile S)) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    convert! hn using 1
    · dsimp [A₂]
      rw [htwoφ]
      field_simp
  let E : ℝ → ℝ := fun u => Real.exp (-α * u)
  have hE (u : ℝ) : HasDerivAt E (-α * E u) u := by
    dsimp [E]
    convert! (Real.hasDerivAt_exp (-α * u)).comp u
      ((hasDerivAt_const u (-α)).mul (hasDerivAt_id u)) using 1 <;> ring
  let F₁ : ℝ → ℝ := fun u => E u * (A₁ u - α * A u)
  have hF (u : ℝ) : HasDerivAt (primeMellinVerticalWindow S P α) (F₁ u) u := by
    have hp := (hE u).mul (hA u)
    convert! hp using 1 <;> dsimp [primeMellinVerticalWindow, E, A, A₁, F₁, q] <;> ring
  let F₂ : ℝ → ℝ := fun u =>
    E u * (A₂ u - 2 * α * A₁ u + α ^ 2 * A u)
  have hF₁ (u : ℝ) : HasDerivAt F₁ (F₂ u) u := by
    have hinner := (hA₁ u).sub ((hA u).const_mul α)
    have hp := (hE u).mul hinner
    convert hp using 1 <;> dsimp [F₁, F₂] <;> ring
  have htwo : iteratedDeriv 2 (primeMellinVerticalWindow S P α) =
      deriv (deriv (primeMellinVerticalWindow S P α)) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [htwo]
  funext u
  have hd : deriv (primeMellinVerticalWindow S P α) = F₁ := by
    funext x
    exact (hF x).deriv
  rw [hd, (hF₁ u).deriv]
  dsimp [F₂, E, A, A₁, A₂, q]
  field_simp
  ring

/-- On the support of the plateau window, its exponential factor is at most
`8 * P ^ α` throughout `1/2 ≤ α ≤ 2`. -/
theorem exp_neg_mul_le_eight_mul_rpow (P α u : ℝ)
    (hP : 2 ≤ P) (hα0 : 1 / 2 ≤ α) (hα2 : α ≤ 2)
    (hu : u ∈ Set.Icc (-Real.log P - (3 / 2) * Real.log 2)
      (-Real.log P + (1 / 2) * Real.log 2)) :
    Real.exp (-α * u) ≤ 8 * P ^ α := by
  have hP0 : 0 < P := by linarith
  have hαpos : 0 < α := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp : -α * u ≤ α * (Real.log P + (3 / 2) * Real.log 2) := by
    have hu1 := hu.1
    nlinarith
  calc
    Real.exp (-α * u) ≤ Real.exp (α * (Real.log P + (3 / 2) * Real.log 2)) :=
      Real.exp_le_exp.mpr hexp
    _ = P ^ α * 2 ^ ((3 / 2) * α) := by
      rw [mul_add, Real.exp_add, Real.rpow_def_of_pos hP0,
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 2 <;> ring
    _ ≤ P ^ α * 8 := by
      gcongr
      calc
        (2 : ℝ) ^ ((3 / 2) * α) ≤ 2 ^ (3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
        _ = 8 := by norm_num
    _ = 8 * P ^ α := by ring

/-- An elementary compact-support integral bound used for both the window
and its second derivative. -/
theorem integral_abs_le_of_support_Icc (f : ℝ → ℝ) (a b B : ℝ)
    (hab : a ≤ b) (hf : Continuous f) (hsupp : support f ⊆ Set.Icc a b)
    (hB0 : 0 ≤ B) (hB : ∀ x ∈ Set.Icc a b, |f x| ≤ B) :
    ∫ x, |f x| ≤ B * (b - a) := by
  have heq : (fun x => |f x|) =
      (Set.Icc a b).indicator (fun x => |f x|) := by
    funext x
    by_cases hx : x ∈ Set.Icc a b
    · simp [hx]
    · have hfx : f x = 0 := notMem_support.mp (fun hmem => hx (hsupp hmem))
      simp [hx, hfx]
  have hnonneg : 0 ≤ ∫ x in Set.Icc a b, |f x| :=
    setIntegral_nonneg measurableSet_Icc (fun _ _ => abs_nonneg _)
  have hnorm := norm_setIntegral_le_of_norm_le_const
    (μ := volume) (f := fun x : ℝ => |f x|) isCompact_Icc.measure_lt_top
    (fun x hx => by simpa [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg (f x))] using hB x hx)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hnorm
  have hmeasure : volume.real (Set.Icc a b) = b - a :=
    Real.volume_real_Icc_of_le hab
  have heqInt : ∫ x, |f x| = ∫ x in Set.Icc a b, |f x| := by
    calc
      ∫ x, |f x| = ∫ x, (Set.Icc a b).indicator (fun y => |f y|) x :=
        congrArg (fun g : ℝ → ℝ => ∫ x, g x) heq
      _ = ∫ x in Set.Icc a b, |f x| := integral_indicator measurableSet_Icc
  calc
    ∫ x, |f x| = ∫ x in Set.Icc a b, |f x| := heqInt
    _ ≤ B * volume.real (Set.Icc a b) := hnorm
    _ = B * (b - a) := by rw [hmeasure]

/-- `L¹` bounds for the vertical window and its second derivative.  The
constant is deliberately roomy; only its absoluteness is used later. -/
theorem primeMellinVerticalWindow_integral_bounds
    (S : ℝ → ℝ) (C P α : ℝ)
    (hSs : ContDiff ℝ ∞ S)
    (hS01 : ∀ v, 0 ≤ S v ∧ S v ≤ 1)
    (hS0 : ∀ v, v ≤ 0 → S v = 0)
    (hS1 : ∀ v, 1 ≤ v → S v = 1)
    (hC0 : 0 ≤ C)
    (hC1 : ∀ v, |deriv S v| ≤ C)
    (hC2 : ∀ v, |deriv (deriv S) v| ≤ C)
    (hP : 2 ≤ P) (hα0 : 1 / 2 ≤ α) (hα2 : α ≤ 2) :
    (∫ u, |primeMellinVerticalWindow S P α u| ≤ 16 * P ^ α) ∧
      (∫ u, |iteratedDeriv 2 (primeMellinVerticalWindow S P α) u| ≤
        3200 * (C + 1) ^ 2 * P ^ α) := by
  let a := -Real.log P - (3 / 2) * Real.log 2
  let b := -Real.log P + (1 / 2) * Real.log 2
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hp := primeMellinProfile_properties S hSs hS01 hS0 hS1
  have hs := primeMellinVerticalWindow_smooth_support S P α hSs hS01 hS0 hS1
  have hsupp : support (primeMellinVerticalWindow S P α) ⊆ Set.Icc a b := by
    intro u hu
    by_contra hnot
    simp only [Set.mem_Icc, not_and_or, not_le] at hnot
    rcases hnot with hleft | hright
    · have hv : 3 / 2 ≤ (-u - Real.log P) / Real.log 2 := by
        rw [le_div_iff₀ hlog2pos]
        dsimp [a] at hleft
        linarith
      exact hu (by rw [primeMellinVerticalWindow, hp.2.2.2.1 _ hv, mul_zero])
    · have hv : (-u - Real.log P) / Real.log 2 ≤ -(1 / 2) := by
        rw [div_le_iff₀ hlog2pos]
        dsimp [b] at hright
        linarith
      exact hu (by rw [primeMellinVerticalWindow, hp.2.2.1 _ hv, mul_zero])
  have hpoint : ∀ u ∈ Set.Icc a b,
      |primeMellinVerticalWindow S P α u| ≤ 8 * P ^ α := by
    intro u hu
    rw [primeMellinVerticalWindow, abs_mul,
      abs_of_nonneg (Real.exp_pos _).le,
      abs_of_nonneg (hp.2.1 _).1]
    calc
      Real.exp (-α * u) *
          primeMellinProfile S ((-u - Real.log P) / Real.log 2)
          ≤ (8 * P ^ α) * 1 :=
            mul_le_mul
              (exp_neg_mul_le_eight_mul_rpow P α u hP hα0 hα2
                (by simpa [a, b] using hu))
              (hp.2.1 _).2 (hp.2.1 _).1 (by positivity)
      _ = 8 * P ^ α := mul_one _
  have hfirst := integral_abs_le_of_support_Icc
    (primeMellinVerticalWindow S P α) a b (8 * P ^ α) hab hs.1.continuous
    hsupp (by positivity) hpoint
  have hlen : b - a = 2 * Real.log 2 := by dsimp [a, b]; ring
  have hlog2le : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hfirst' : ∫ u, |primeMellinVerticalWindow S P α u| ≤ 16 * P ^ α := by
    rw [hlen] at hfirst
    calc
      _ ≤ (8 * P ^ α) * (2 * Real.log 2) := hfirst
      _ ≤ (8 * P ^ α) * 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 16 * P ^ α := by ring
  refine ⟨hfirst', ?_⟩
  have hderiv := primeMellinProfile_deriv_bounds S C hSs hS01 hC0 hC1 hC2
  have hlog2half : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hinv : 1 / Real.log 2 ≤ 2 := by
    rw [div_le_iff₀ hlog2pos]
    linarith
  have hinvsq : 1 / (Real.log 2) ^ 2 ≤ 4 := by
    rw [div_le_iff₀ (sq_pos_of_pos hlog2pos)]
    nlinarith [sq_nonneg (Real.log 2 - 1 / 2)]
  have hαabs : |α| ≤ 2 := by rw [abs_of_pos (by linarith)]; exact hα2
  have hbracket : ∀ u : ℝ,
      |α ^ 2 * primeMellinProfile S ((-u - Real.log P) / Real.log 2) +
          (2 * α / Real.log 2) *
            deriv (primeMellinProfile S) ((-u - Real.log P) / Real.log 2) +
          (1 / (Real.log 2) ^ 2) *
            iteratedDeriv 2 (primeMellinProfile S)
              ((-u - Real.log P) / Real.log 2)|
        ≤ 200 * (C + 1) ^ 2 := by
    intro u
    refine (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) (le_refl _)).trans ?_)
    simp only [abs_mul, abs_div]
    norm_num
    have hαsq : α ^ 2 ≤ 4 := by nlinarith
    have hCplus : 1 ≤ C + 1 := by linarith
    have hCplus0 : 0 ≤ C + 1 := by linarith
    have hprof := (hp.2.1 ((-u - Real.log P) / Real.log 2)).2
    have hprof0 := (hp.2.1 ((-u - Real.log P) / Real.log 2)).1
    rw [abs_of_nonneg hprof0, abs_of_pos hlog2pos]
    have hterm0 : α ^ 2 * primeMellinProfile S ((-u - Real.log P) / Real.log 2) ≤ 4 := by
      nlinarith
    have hcoef1 : 2 * |α| / Real.log 2 ≤ 8 := by
      calc
        2 * |α| / Real.log 2 = 2 * |α| * (1 / Real.log 2) := by ring
        _ ≤ 2 * 2 * 2 := by gcongr
        _ = 8 := by norm_num
    have hterm1 : 2 * |α| / Real.log 2 *
        |deriv (primeMellinProfile S) ((-u - Real.log P) / Real.log 2)| ≤ 48 * C := by
      calc
        2 * |α| / Real.log 2 *
            |deriv (primeMellinProfile S) ((-u - Real.log P) / Real.log 2)|
            ≤ 8 * (6 * C) :=
              mul_le_mul hcoef1 (hderiv.1 _) (abs_nonneg _) (by positivity)
        _ = 48 * C := by ring
    have hterm2 : 1 / Real.log 2 ^ 2 *
        |iteratedDeriv 2 (primeMellinProfile S) ((-u - Real.log P) / Real.log 2)|
          ≤ 72 * C + 72 * C ^ 2 := by
      calc
        1 / Real.log 2 ^ 2 *
            |iteratedDeriv 2 (primeMellinProfile S) ((-u - Real.log P) / Real.log 2)|
            ≤ 4 * (18 * C + 18 * C ^ 2) :=
              mul_le_mul hinvsq (hderiv.2 _) (abs_nonneg _) (by positivity)
        _ = 72 * C + 72 * C ^ 2 := by ring
    have hterm2' : (Real.log 2 ^ 2)⁻¹ *
        |iteratedDeriv 2 (primeMellinProfile S) ((-u - Real.log P) / Real.log 2)|
          ≤ 72 * C + 72 * C ^ 2 := by
      simpa only [one_div] using hterm2
    calc
      α ^ 2 * primeMellinProfile S ((-u - Real.log P) / Real.log 2) +
            2 * |α| / Real.log 2 *
              |deriv (primeMellinProfile S) ((-u - Real.log P) / Real.log 2)| +
          (Real.log 2 ^ 2)⁻¹ *
              |iteratedDeriv 2 (primeMellinProfile S)
                ((-u - Real.log P) / Real.log 2)|
          ≤ 4 + 48 * C + (72 * C + 72 * C ^ 2) :=
            add_le_add (add_le_add hterm0 hterm1) hterm2'
      _ ≤ 200 * (C + 1) ^ 2 := by nlinarith [sq_nonneg C]
  have htwo := iteratedDeriv_two_primeMellinVerticalWindow S P α hSs
  have hsecondSmooth : Continuous
      (iteratedDeriv 2 (primeMellinVerticalWindow S P α)) :=
    by
      have h1 : ContDiff ℝ ∞ (deriv (primeMellinVerticalWindow S P α)) := by
        simpa using hs.1.iterate_deriv 1
      have h2 : ContDiff ℝ ∞ (deriv (deriv (primeMellinVerticalWindow S P α))) := by
        simpa using h1.iterate_deriv 1
      rw [show iteratedDeriv 2 (primeMellinVerticalWindow S P α) =
        deriv (deriv (primeMellinVerticalWindow S P α)) by
          rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]]
      exact h2.continuous
  have hts : tsupport (primeMellinVerticalWindow S P α) ⊆ Set.Icc a b := by
    exact closure_minimal hsupp isClosed_Icc
  have htsderiv : tsupport (deriv (primeMellinVerticalWindow S P α)) ⊆
      tsupport (primeMellinVerticalWindow S P α) :=
    closure_minimal support_deriv_subset isClosed_closure
  have hsupp2 : support (iteratedDeriv 2 (primeMellinVerticalWindow S P α)) ⊆
      Set.Icc a b := by
    rw [show iteratedDeriv 2 (primeMellinVerticalWindow S P α) =
      deriv (deriv (primeMellinVerticalWindow S P α)) by
        rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]]
    exact support_deriv_subset.trans
      (htsderiv.trans hts)
  have hpoint2 : ∀ u ∈ Set.Icc a b,
      |iteratedDeriv 2 (primeMellinVerticalWindow S P α) u| ≤
        1600 * (C + 1) ^ 2 * P ^ α := by
    intro u hu
    rw [htwo]
    rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    calc
      Real.exp (-α * u) * _ ≤ (8 * P ^ α) * (200 * (C + 1) ^ 2) := by
        gcongr
        · exact exp_neg_mul_le_eight_mul_rpow P α u hP hα0 hα2
            (by simpa [a, b] using hu)
        · exact hbracket u
      _ = 1600 * (C + 1) ^ 2 * P ^ α := by ring
  have hsecond := integral_abs_le_of_support_Icc
    (iteratedDeriv 2 (primeMellinVerticalWindow S P α)) a b
    (1600 * (C + 1) ^ 2 * P ^ α) hab hsecondSmooth hsupp2
    (by positivity) hpoint2
  rw [hlen] at hsecond
  calc
    _ ≤ (1600 * (C + 1) ^ 2 * P ^ α) * (2 * Real.log 2) := hsecond
    _ ≤ (1600 * (C + 1) ^ 2 * P ^ α) * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 3200 * (C + 1) ^ 2 * P ^ α := by ring

/-- A coarse lower support bound for the multiplicative plateau window. -/
theorem primeMellinWindow_eq_zero_of_le (S : ℝ → ℝ) (P x : ℝ)
    (hS0 : ∀ v, v ≤ 0 → S v = 0) (hP : 0 < P) (hx : 0 < x) (hxP : 2 * x ≤ P) :
    primeMellinWindow S P x = 0 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio0 : 0 < x / P := div_pos hx hP
  have hratio : x / P ≤ 1 / 2 := by
    rw [div_le_iff₀ hP]
    linarith
  have hlogs : Real.log (x / P) ≤ Real.log (1 / 2) :=
    Real.log_le_log hratio0 hratio
  have hloghalf : Real.log (1 / 2) = -Real.log 2 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    simp
  have hv : Real.log (x / P) / Real.log 2 ≤ -(1 / 2) := by
    rw [div_le_iff₀ hlog2]
    rw [hloghalf] at hlogs
    linarith
  rw [primeMellinWindow, primeMellinProfile, hS0 _ (by linarith), zero_mul]

/-- A coarse upper support bound for the multiplicative plateau window. -/
theorem primeMellinWindow_eq_zero_of_two_mul_le (S : ℝ → ℝ) (P x : ℝ)
    (hS0 : ∀ v, v ≤ 0 → S v = 0) (hP : 0 < P) (hx : 4 * P ≤ x) :
    primeMellinWindow S P x = 0 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity : 0 < 4 * P) hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : 4 ≤ x / P := (le_div_iff₀ hP).mpr (by linarith)
  have hlogs : Real.log 4 ≤ Real.log (x / P) := Real.log_le_log (by norm_num) hratio
  have hlogfour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hv : 3 / 2 ≤ Real.log (x / P) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    rw [hlogfour] at hlogs
    linarith
  have hz : S (3 - 2 * (Real.log (x / P) / Real.log 2)) = 0 :=
    hS0 _ (by linarith)
  rw [primeMellinWindow, primeMellinProfile, hz, mul_zero]

/-- The plateau window is identically one on its central dyadic interval. -/
theorem primeMellinWindow_eq_one (S : ℝ → ℝ) (P x : ℝ)
    (hS1 : ∀ v, 1 ≤ v → S v = 1) (hP : 0 < P)
    (hxP : P ≤ x) (hx2P : x ≤ 2 * P) :
    primeMellinWindow S P x = 1 := by
  have hx : 0 < x := lt_of_lt_of_le hP hxP
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio0 : 0 < x / P := div_pos hx hP
  have hratio1 : 1 ≤ x / P := (le_div_iff₀ hP).mpr (by simpa using hxP)
  have hratio2 : x / P ≤ 2 := (div_le_iff₀ hP).mpr (by simpa [mul_comm] using hx2P)
  have hv0 : 0 ≤ Real.log (x / P) / Real.log 2 := by
    exact div_nonneg (Real.log_nonneg hratio1) hlog2.le
  have hv1 : Real.log (x / P) / Real.log 2 ≤ 1 := by
    rw [div_le_one hlog2]
    exact Real.log_le_log hratio0 hratio2
  rw [primeMellinWindow, primeMellinProfile, hS1 _ (by linarith),
    hS1 _ (by linarith), one_mul]

/-- Exact positive support of the plateau window. -/
theorem primeMellinWindow_support (S : ℝ → ℝ) (P x : ℝ)
    (hSs : ContDiff ℝ ∞ S)
    (hS01 : ∀ v, 0 ≤ S v ∧ S v ≤ 1)
    (hS0 : ∀ v, v ≤ 0 → S v = 0)
    (hS1 : ∀ v, 1 ≤ v → S v = 1)
    (hP : 0 < P) (hx : 0 < x)
    (hxw : primeMellinWindow S P x ≠ 0) :
    P / Real.sqrt 2 < x ∧ x < 2 * Real.sqrt 2 * P := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hp := primeMellinProfile_properties S hSs hS01 hS0 hS1
  let v : ℝ := Real.log (x / P) / Real.log 2
  have hvw : primeMellinProfile S v ≠ 0 := by
    simpa only [primeMellinWindow, v] using hxw
  have hvlow : -(1 / 2) < v := by
    by_contra h
    exact hvw (hp.2.2.1 v (le_of_not_gt h))
  have hvhigh : v < 3 / 2 := by
    by_contra h
    exact hvw (hp.2.2.2.1 v (le_of_not_gt h))
  have hratio : 0 < x / P := div_pos hx hP
  have hlogratio : Real.log (x / P) = Real.log x - Real.log P :=
    Real.log_div (ne_of_gt hx) (ne_of_gt hP)
  have hlogsqrt : Real.log (Real.sqrt 2) = Real.log 2 / 2 :=
    Real.log_sqrt (by norm_num)
  constructor
  · apply (Real.log_lt_log_iff (div_pos hP hsqrt) hx).mp
    rw [Real.log_div (ne_of_gt hP) (ne_of_gt hsqrt), hlogsqrt]
    have := (lt_div_iff₀ hlog2).mp hvlow
    rw [hlogratio] at this
    linarith
  · apply (Real.log_lt_log_iff hx (by positivity : 0 < 2 * Real.sqrt 2 * P)).mp
    rw [Real.log_mul (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hsqrt))
      (ne_of_gt hP), Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hsqrt), hlogsqrt]
    have := (div_lt_iff₀ hlog2).mp hvhigh
    rw [hlogratio] at this
    linarith

/-- In logarithmic coordinates the Mellin transform is exactly the Fourier
transform of `primeMellinVerticalWindow`. -/
theorem primeMellinTransform_eq_fourier (S : ℝ → ℝ) (P α τ : ℝ) (hP : 0 < P) :
    primeMellinTransform S P ((α : ℂ) + (τ : ℂ) * I) =
      𝓕 (fun u : ℝ => (primeMellinVerticalWindow S P α u : ℂ))
        (τ / (2 * Real.pi)) := by
  rw [primeMellinTransform, mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Complex.add_im,
    Complex.mul_im, mul_one, zero_add, add_zero]
  apply congrArg (fun f : ℝ → ℂ => 𝓕 f (τ / (2 * Real.pi)))
  funext u
  have hlog : Real.log (Real.exp (-u) / P) = -u - Real.log P := by
    rw [Real.log_div (Real.exp_ne_zero _) (ne_of_gt hP), Real.log_exp]
  rw [primeMellinVerticalWindow, primeMellinWindow, hlog]
  change ((Real.exp (-α * u) : ℝ) : ℂ) *
      (primeMellinProfile S ((-u - Real.log P) / Real.log 2) : ℂ) = _
  norm_cast

/-- The Mellin transform of the compactly supported multiplicative window is
holomorphic on the whole complex plane. -/
theorem primeMellinTransform_differentiable (S : ℝ → ℝ) (P : ℝ)
    (hSs : ContDiff ℝ ∞ S)
    (hS0 : ∀ v, v ≤ 0 → S v = 0)
    (hP : 0 < P) :
    Differentiable ℂ (primeMellinTransform S P) := by
  have hcont : ContinuousOn
      (fun x : ℝ => (primeMellinWindow S P x : ℂ)) (Set.Ioi 0) := by
    intro x hx
    have hdiv : ContinuousAt (fun y : ℝ => y / P) x := continuousAt_id.div_const P
    have hlog : ContinuousAt (fun y : ℝ => Real.log (y / P)) x :=
      hdiv.log (div_ne_zero (ne_of_gt hx) (ne_of_gt hP))
    have hv : ContinuousAt (fun y : ℝ => Real.log (y / P) / Real.log 2) x :=
      hlog.div_const (Real.log 2)
    have hleft : ContinuousAt
        (fun y : ℝ => S (2 * (Real.log (y / P) / Real.log 2) + 1)) x :=
      hSs.continuous.continuousAt.comp
        ((continuousAt_const.mul hv).add_const 1)
    have hright : ContinuousAt
        (fun y : ℝ => S (3 - 2 * (Real.log (y / P) / Real.log 2))) x :=
      hSs.continuous.continuousAt.comp
        (continuousAt_const.sub (continuousAt_const.mul hv))
    exact (Complex.continuous_ofReal.continuousAt.comp
      (hleft.mul hright)).continuousWithinAt
  have hloc : LocallyIntegrableOn
      (fun x : ℝ => (primeMellinWindow S P x : ℂ)) (Set.Ioi 0) :=
    hcont.locallyIntegrableOn measurableSet_Ioi
  intro s
  let a : ℝ := s.re + 1
  let b : ℝ := s.re - 1
  have htopEq : (fun x : ℝ => (primeMellinWindow S P x : ℂ)) =ᶠ[atTop]
      (fun _ => 0) := by
    filter_upwards [eventually_ge_atTop (4 * P)] with x hx
    rw [primeMellinWindow_eq_zero_of_two_mul_le S P x hS0 hP hx]
    norm_num
  have htop : (fun x : ℝ => (primeMellinWindow S P x : ℂ)) =O[atTop]
      (fun x : ℝ => x ^ (-a)) :=
    htopEq.trans_isBigO (isBigO_zero _ _)
  have hbotEq : (fun x : ℝ => (primeMellinWindow S P x : ℂ)) =ᶠ[𝓝[>] 0]
      (fun _ => 0) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (half_pos hP))] with x hx0 hxP
    rw [primeMellinWindow_eq_zero_of_le S P x hS0 hP hx0 (by
      norm_num [div_eq_mul_inv] at hxP ⊢
      linarith)]
    norm_num
  have hbot : (fun x : ℝ => (primeMellinWindow S P x : ℂ)) =O[𝓝[>] 0]
      (fun x : ℝ => x ^ (-b)) :=
    hbotEq.trans_isBigO (isBigO_zero _ _)
  simpa only [primeMellinTransform] using!
    mellin_differentiableAt_of_isBigO_rpow hloc htop (by dsimp [a]; linarith)
      hbot (by dsimp [b]; linarith)

/-- The defining Mellin integral converges on every vertical line because the
multiplicative window is compactly supported away from zero. -/
theorem primeMellinWindow_mellinConvergent (S : ℝ → ℝ) (P : ℝ)
    (hSs : ContDiff ℝ ∞ S)
    (hS0 : ∀ v, v ≤ 0 → S v = 0)
    (hP : 0 < P) (s : ℂ) :
    MellinConvergent (fun x : ℝ => (primeMellinWindow S P x : ℂ)) s := by
  have hcont : ContinuousOn
      (fun x : ℝ => (primeMellinWindow S P x : ℂ)) (Set.Ioi 0) := by
    intro x hx
    have hdiv : ContinuousAt (fun y : ℝ => y / P) x := continuousAt_id.div_const P
    have hlog : ContinuousAt (fun y : ℝ => Real.log (y / P)) x :=
      hdiv.log (div_ne_zero (ne_of_gt hx) (ne_of_gt hP))
    have hv : ContinuousAt (fun y : ℝ => Real.log (y / P) / Real.log 2) x :=
      hlog.div_const (Real.log 2)
    have hleft : ContinuousAt
        (fun y : ℝ => S (2 * (Real.log (y / P) / Real.log 2) + 1)) x :=
      hSs.continuous.continuousAt.comp
        ((continuousAt_const.mul hv).add_const 1)
    have hright : ContinuousAt
        (fun y : ℝ => S (3 - 2 * (Real.log (y / P) / Real.log 2))) x :=
      hSs.continuous.continuousAt.comp
        (continuousAt_const.sub (continuousAt_const.mul hv))
    exact (Complex.continuous_ofReal.continuousAt.comp
      (hleft.mul hright)).continuousWithinAt
  have hloc : LocallyIntegrableOn
      (fun x : ℝ => (primeMellinWindow S P x : ℂ)) (Set.Ioi 0) :=
    hcont.locallyIntegrableOn measurableSet_Ioi
  let a : ℝ := s.re + 1
  let b : ℝ := s.re - 1
  have htopEq : (fun x : ℝ => (primeMellinWindow S P x : ℂ)) =ᶠ[atTop]
      (fun _ => 0) := by
    filter_upwards [eventually_ge_atTop (4 * P)] with x hx
    rw [primeMellinWindow_eq_zero_of_two_mul_le S P x hS0 hP hx]
    norm_num
  have htop : (fun x : ℝ => (primeMellinWindow S P x : ℂ)) =O[atTop]
      (fun x : ℝ => x ^ (-a)) := htopEq.trans_isBigO (isBigO_zero _ _)
  have hbotEq : (fun x : ℝ => (primeMellinWindow S P x : ℂ)) =ᶠ[𝓝[>] 0]
      (fun _ => 0) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (half_pos hP))] with x hx0 hxP
    rw [primeMellinWindow_eq_zero_of_le S P x hS0 hP hx0 (by
      norm_num [div_eq_mul_inv] at hxP ⊢
      linarith)]
    norm_num
  have hbot : (fun x : ℝ => (primeMellinWindow S P x : ℂ)) =O[𝓝[>] 0]
      (fun x : ℝ => x ^ (-b)) := hbotEq.trans_isBigO (isBigO_zero _ _)
  exact mellinConvergent_of_isBigO_rpow hloc htop (by dsimp [a]; linarith)
    hbot (by dsimp [b]; linarith)

/-- The multiplicative window is continuous at every positive point. -/
theorem primeMellinWindow_continuousAt (S : ℝ → ℝ) (P x : ℝ)
    (hSs : ContDiff ℝ ∞ S) (hP : 0 < P) (hx : 0 < x) :
    ContinuousAt (fun y : ℝ => (primeMellinWindow S P y : ℂ)) x := by
  have hdiv : ContinuousAt (fun y : ℝ => y / P) x := continuousAt_id.div_const P
  have hlog : ContinuousAt (fun y : ℝ => Real.log (y / P)) x :=
    hdiv.log (div_ne_zero (ne_of_gt hx) (ne_of_gt hP))
  have hv : ContinuousAt (fun y : ℝ => Real.log (y / P) / Real.log 2) x :=
    hlog.div_const (Real.log 2)
  have hleft : ContinuousAt
      (fun y : ℝ => S (2 * (Real.log (y / P) / Real.log 2) + 1)) x :=
    hSs.continuous.continuousAt.comp
      ((continuousAt_const.mul hv).add_const 1)
  have hright : ContinuousAt
      (fun y : ℝ => S (3 - 2 * (Real.log (y / P) / Real.log 2))) x :=
    hSs.continuous.continuousAt.comp
      (continuousAt_const.sub (continuousAt_const.mul hv))
  exact Complex.continuous_ofReal.continuousAt.comp (hleft.mul hright)

/-- Quadratic vertical decay, uniform for `1/2 ≤ α ≤ 2`. -/
theorem primeMellinTransform_vertical_decay
    (S : ℝ → ℝ) (C P α τ : ℝ)
    (hSs : ContDiff ℝ ∞ S)
    (hS01 : ∀ v, 0 ≤ S v ∧ S v ≤ 1)
    (hS0 : ∀ v, v ≤ 0 → S v = 0)
    (hS1 : ∀ v, 1 ≤ v → S v = 1)
    (hC0 : 0 ≤ C)
    (hC1 : ∀ v, |deriv S v| ≤ C)
    (hC2 : ∀ v, |deriv (deriv S) v| ≤ C)
    (hP : 2 ≤ P) (hα0 : 1 / 2 ≤ α) (hα2 : α ≤ 2) :
    ‖primeMellinTransform S P ((α : ℂ) + (τ : ℂ) * I)‖ ≤
      250000 * (C + 1) ^ 2 * P ^ α / (1 + τ ^ 2) := by
  have hP0 : 0 < P := by linarith
  have hs := primeMellinVerticalWindow_smooth_support S P α hSs hS01 hS0 hS1
  have hi := primeMellinVerticalWindow_integral_bounds S C P α hSs hS01 hS0 hS1
    hC0 hC1 hC2 hP hα0 hα2
  have hMV : ∀ ξ : ℝ,
      ‖𝓕 (fun u : ℝ => (primeMellinVerticalWindow S P α u : ℂ)) ξ‖ ≤
        16 * P ^ α := by
    intro ξ
    exact (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans
      (by simpa [Complex.norm_real, Real.norm_eq_abs] using hi.1)
  have hf := fourier_window_le_inv_one_add_sq
    (primeMellinVerticalWindow S P α) hs.1 hs.2
    (3200 * (C + 1) ^ 2 * P ^ α) (16 * P ^ α) hi.2 hMV
    (τ / (2 * Real.pi))
  rw [primeMellinTransform_eq_fourier S P α τ hP0]
  have hCp : 1 ≤ (C + 1) ^ 2 := by nlinarith [sq_nonneg C]
  have hpow0 : 0 ≤ P ^ α := Real.rpow_nonneg hP0.le _
  have hcoef : 2 * (16 * P ^ α) +
        3200 * (C + 1) ^ 2 * P ^ α / (2 * Real.pi ^ 2)
      ≤ 3232 * (C + 1) ^ 2 * P ^ α := by
    have hden : 1 ≤ 2 * Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
    have hdiv : 3200 * (C + 1) ^ 2 * P ^ α / (2 * Real.pi ^ 2) ≤
        3200 * (C + 1) ^ 2 * P ^ α := by
      exact div_le_self (by positivity) hden
    nlinarith [mul_le_mul_of_nonneg_right hCp hpow0]
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hden1 : 0 < 1 + (τ / (2 * Real.pi)) ^ 2 := by positivity
  have hden2 : 0 < 1 + τ ^ 2 := by positivity
  have hratio : (1 + τ ^ 2) ≤ 64 * (1 + (τ / (2 * Real.pi)) ^ 2) := by
    have hpisq : Real.pi ^ 2 ≤ 16 := by nlinarith
    have hmain : τ ^ 2 ≤ 16 / Real.pi ^ 2 * τ ^ 2 := by
      have hone : 1 ≤ 16 / Real.pi ^ 2 := by
        rw [le_div_iff₀ (sq_pos_of_pos hpi0)]
        simpa only [one_mul] using hpisq
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hone (sq_nonneg τ)
    calc
      1 + τ ^ 2 ≤ 64 + 16 / Real.pi ^ 2 * τ ^ 2 := by linarith
      _ = 64 * (1 + (τ / (2 * Real.pi)) ^ 2) := by
        have hsq : (τ / (2 * Real.pi)) ^ 2 = τ ^ 2 / (4 * Real.pi ^ 2) := by
          field_simp
          ring
        rw [hsq]
        ring
  calc
    ‖𝓕 (fun u : ℝ => (primeMellinVerticalWindow S P α u : ℂ))
        (τ / (2 * Real.pi))‖
        ≤ (2 * (16 * P ^ α) +
            3200 * (C + 1) ^ 2 * P ^ α / (2 * Real.pi ^ 2)) /
              (1 + (τ / (2 * Real.pi)) ^ 2) := hf
    _ ≤ (3232 * (C + 1) ^ 2 * P ^ α) /
          (1 + (τ / (2 * Real.pi)) ^ 2) :=
      div_le_div_of_nonneg_right hcoef hden1.le
    _ ≤ 250000 * (C + 1) ^ 2 * P ^ α / (1 + τ ^ 2) := by
      rw [div_le_div_iff₀ hden1 hden2]
      have hbase : 0 ≤ (C + 1) ^ 2 * P ^ α := mul_nonneg (sq_nonneg _) hpow0
      have hscaled : 3232 * ((C + 1) ^ 2 * P ^ α) * (1 + τ ^ 2) ≤
          3232 * ((C + 1) ^ 2 * P ^ α) *
            (64 * (1 + (τ / (2 * Real.pi)) ^ 2)) :=
        mul_le_mul_of_nonneg_left hratio (mul_nonneg (by norm_num) hbase)
      calc
        3232 * (C + 1) ^ 2 * P ^ α * (1 + τ ^ 2)
            = 3232 * ((C + 1) ^ 2 * P ^ α) * (1 + τ ^ 2) := by ring
        _ ≤ 3232 * ((C + 1) ^ 2 * P ^ α) *
              (64 * (1 + (τ / (2 * Real.pi)) ^ 2)) := hscaled
        _ = 206848 * (((C + 1) ^ 2 * P ^ α) *
              (1 + (τ / (2 * Real.pi)) ^ 2)) := by ring
        _ ≤ 250000 * (((C + 1) ^ 2 * P ^ α) *
              (1 + (τ / (2 * Real.pi)) ^ 2)) :=
            mul_le_mul_of_nonneg_right (by norm_num)
              (mul_nonneg hbase hden1.le)
        _ = 250000 * (C + 1) ^ 2 * P ^ α *
              (1 + (τ / (2 * Real.pi)) ^ 2) := by ring

/-- The quadratic vertical decay makes the Mellin transform integrable on
every line in the strip used below. -/
theorem primeMellinTransform_verticalIntegrable (S : ℝ → ℝ) (C P α : ℝ)
    (hSs : ContDiff ℝ ∞ S)
    (hS01 : ∀ v, 0 ≤ S v ∧ S v ≤ 1)
    (hS0 : ∀ v, v ≤ 0 → S v = 0)
    (hS1 : ∀ v, 1 ≤ v → S v = 1)
    (hC0 : 0 ≤ C) (hC1 : ∀ v, |deriv S v| ≤ C)
    (hC2 : ∀ v, |deriv (deriv S) v| ≤ C)
    (hP : 2 ≤ P) (hα0 : 1 / 2 ≤ α) (hα2 : α ≤ 2) :
    VerticalIntegrable (primeMellinTransform S P) α := by
  let K : ℝ := 250000 * (C + 1) ^ 2 * P ^ α
  have hmajorant : Integrable (fun τ : ℝ => K * (1 + τ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul K
  have hdiff := primeMellinTransform_differentiable S P hSs hS0 (by linarith)
  have hmeas : AEStronglyMeasurable
      (fun τ : ℝ => primeMellinTransform S P ((α : ℂ) + (τ : ℂ) * I)) :=
    (hdiff.continuous.comp (by fun_prop)).aestronglyMeasurable
  refine hmajorant.mono' hmeas (ae_of_all _ fun τ => ?_)
  simpa only [K, div_eq_mul_inv] using
    primeMellinTransform_vertical_decay S C P α τ hSs hS01 hS0 hS1
      hC0 hC1 hC2 hP hα0 hα2

/-- Mellin inversion for the compactly supported multiplicative window. -/
theorem primeMellin_inversion (S : ℝ → ℝ) (C P α x : ℝ)
    (hSs : ContDiff ℝ ∞ S)
    (hS01 : ∀ v, 0 ≤ S v ∧ S v ≤ 1)
    (hS0 : ∀ v, v ≤ 0 → S v = 0)
    (hS1 : ∀ v, 1 ≤ v → S v = 1)
    (hC0 : 0 ≤ C) (hC1 : ∀ v, |deriv S v| ≤ C)
    (hC2 : ∀ v, |deriv (deriv S) v| ≤ C)
    (hP : 2 ≤ P) (hα0 : 1 / 2 ≤ α) (hα2 : α ≤ 2) (hx : 0 < x) :
    mellinInv α (primeMellinTransform S P) x = (primeMellinWindow S P x : ℂ) := by
  apply mellinInv_mellin_eq
  · exact hx
  · exact primeMellinWindow_mellinConvergent S P hSs hS0 (by linarith) _
  · exact primeMellinTransform_verticalIntegrable S C P α hSs hS01 hS0 hS1
      hC0 hC1 hC2 hP hα0 hα2
  · exact primeMellinWindow_continuousAt S P x hSs (by linarith) hx

/-- **V-A-1.** A single absolute master transition produces the smooth
multiplicative windows used in the Mellin shift. -/
theorem exists_primeMellin_window :
    ∃ (S : ℝ → ℝ) (C : ℝ), ContDiff ℝ ∞ S ∧
      (∀ v, 0 ≤ S v ∧ S v ≤ 1) ∧
      (∀ v, v ≤ 0 → S v = 0) ∧ (∀ v, 1 ≤ v → S v = 1) ∧
      0 ≤ C ∧ (∀ v, |deriv S v| ≤ C) ∧
      (∀ v, |deriv (deriv S) v| ≤ C) ∧
      (∀ P : ℝ, 0 < P → Differentiable ℂ (primeMellinTransform S P)) ∧
      ∀ (P α τ : ℝ), 2 ≤ P → 1 / 2 ≤ α → α ≤ 2 →
        ‖primeMellinTransform S P ((α : ℂ) + (τ : ℂ) * I)‖ ≤
          250000 * (C + 1) ^ 2 * P ^ α / (1 + τ ^ 2) := by
  obtain ⟨S, C, hSs, hS01, hS0, hS1, hC0, hC1, hC2⟩ := exists_master_transition
  refine ⟨S, C, hSs, hS01, hS0, hS1, hC0, hC1, hC2,
    fun P hP => primeMellinTransform_differentiable S P hSs hS0 hP, ?_⟩
  intro P α τ hP hα0 hα2
  exact primeMellinTransform_vertical_decay S C P α τ hSs hS01 hS0 hS1
    hC0 hC1 hC2 hP hα0 hα2

/-- **V-A-1 (plateau form).** The campaign window is one on `[P,2P]`,
has positive support inside `[P/√2, 2√2 P]`, and retains the entire Mellin
transform and uniform quadratic vertical decay proved above. -/
theorem exists_primeMellin_plateau_window :
    ∃ (S : ℝ → ℝ) (C : ℝ), ContDiff ℝ ∞ S ∧
      (∀ v, 0 ≤ S v ∧ S v ≤ 1) ∧
      (∀ v, v ≤ 0 → S v = 0) ∧ (∀ v, 1 ≤ v → S v = 1) ∧
      0 ≤ C ∧ (∀ v, |deriv S v| ≤ C) ∧
      (∀ v, |deriv (deriv S) v| ≤ C) ∧
      (∀ P : ℝ, 0 < P → Differentiable ℂ (primeMellinTransform S P)) ∧
      (∀ (P α τ : ℝ), 2 ≤ P → 1 / 2 ≤ α → α ≤ 2 →
        ‖primeMellinTransform S P ((α : ℂ) + (τ : ℂ) * I)‖ ≤
          250000 * (C + 1) ^ 2 * P ^ α / (1 + τ ^ 2)) ∧
      (∀ (P x : ℝ), 0 < P → P ≤ x → x ≤ 2 * P →
        primeMellinWindow S P x = 1) ∧
      ∀ (P x : ℝ), 0 < P → 0 < x → primeMellinWindow S P x ≠ 0 →
        P / Real.sqrt 2 < x ∧ x < 2 * Real.sqrt 2 * P := by
  obtain ⟨S, C, hSs, hS01, hS0, hS1, hC0, hC1, hC2, hdiff, hdecay⟩ :=
    exists_primeMellin_window
  refine ⟨S, C, hSs, hS01, hS0, hS1, hC0, hC1, hC2, hdiff, hdecay, ?_, ?_⟩
  · intro P x hP hxP hx2P
    exact primeMellinWindow_eq_one S P x hS1 hP hxP hx2P
  · intro P x hP hx hxw
    exact primeMellinWindow_support S P x hSs hS01 hS0 hS1 hP hx hxw

/-- **V-A-2.** Mellin inversion and absolute convergence give the
von Mangoldt sum as a vertical integral of its Dirichlet series. -/
theorem primeMellin_vonMangoldt_representation
    (S : ℝ → ℝ) (C P c u : ℝ)
    (hSs : ContDiff ℝ ∞ S)
    (hS01 : ∀ v, 0 ≤ S v ∧ S v ≤ 1)
    (hS0 : ∀ v, v ≤ 0 → S v = 0)
    (hS1 : ∀ v, 1 ≤ v → S v = 1)
    (hC0 : 0 ≤ C) (hC1 : ∀ v, |deriv S v| ≤ C)
    (hC2 : ∀ v, |deriv (deriv S) v| ≤ C)
    (hP : 2 ≤ P) (hc1 : 1 < c) (hc2 : c ≤ 2) :
    (∑' n : ℕ, (primeMellinWindow S P n : ℂ) *
        LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((u : ℂ) * I) n) =
      (1 / (2 * Real.pi) : ℂ) * ∫ τ : ℝ,
        primeMellinTransform S P ((c : ℂ) + (τ : ℂ) * I) *
          LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
            ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I) := by
  let a : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let F : ℕ → ℝ → ℂ := fun n τ =>
    primeMellinTransform S P ((c : ℂ) + (τ : ℂ) * I) *
      LSeries.term a ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I) n
  let K : ℝ := 250000 * (C + 1) ^ 2 * P ^ c
  have hc0 : 1 / 2 ≤ c := by linarith
  have hLS : LSeriesSummable a (c : ℂ) := by
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa [a] using hc1)
  have hFint : ∀ n, Integrable (F n) := by
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [F]
    · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
      have hmeas : AEStronglyMeasurable (F n) := by
        apply Continuous.aestronglyMeasurable
        have hW : Continuous (fun τ : ℝ =>
            primeMellinTransform S P ((c : ℂ) + (τ : ℂ) * I)) :=
          (primeMellinTransform_differentiable S P hSs hS0 (by linarith)).continuous.comp
            (by fun_prop)
        have hterm : Continuous (fun τ : ℝ => LSeries.term a
            ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I) n) := by
          simp_rw [LSeries.term_of_ne_zero hn0]
          simp only [Complex.cpow_def, Nat.cast_eq_zero, hn0, if_false]
          exact continuous_const.div (Complex.continuous_exp.comp (by fun_prop))
            (fun τ => Complex.exp_ne_zero _)
        exact hW.mul hterm
      have hmajorant : Integrable (fun τ : ℝ =>
          (K * ‖LSeries.term a (c : ℂ) n‖) * (1 + τ ^ 2)⁻¹) :=
        integrable_inv_one_add_sq.const_mul _
      refine hmajorant.mono' hmeas (ae_of_all _ fun τ => ?_)
      have hdecay := primeMellinTransform_vertical_decay S C P c τ hSs hS01
        hS0 hS1 hC0 hC1 hC2 hP hc0 hc2
      have hterm : ‖LSeries.term a
          ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I) n‖ =
          ‖LSeries.term a (c : ℂ) n‖ := by
        simp only [LSeries.norm_term_eq, Complex.add_re, Complex.ofReal_re,
          Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          mul_zero, sub_zero, mul_one, add_zero]
      simp only [F, norm_mul, hterm]
      calc
        ‖primeMellinTransform S P ((c : ℂ) + (τ : ℂ) * I)‖ *
              ‖LSeries.term a (c : ℂ) n‖
            ≤ (K / (1 + τ ^ 2)) * ‖LSeries.term a (c : ℂ) n‖ :=
          mul_le_mul_of_nonneg_right (by simpa only [K] using hdecay) (norm_nonneg _)
        _ = (K * ‖LSeries.term a (c : ℂ) n‖) * (1 + τ ^ 2)⁻¹ := by
          rw [div_eq_mul_inv]
          ring
  have hFsum : Summable (fun n => ∫ τ : ℝ, ‖F n τ‖) := by
    have hnormsum : Summable (fun n => ‖LSeries.term a (c : ℂ) n‖) :=
      summable_norm_iff.mpr hLS
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) ((hnormsum.mul_left (K * Real.pi)))
    have hmajorant : Integrable (fun τ : ℝ =>
        (K * ‖LSeries.term a (c : ℂ) n‖) * (1 + τ ^ 2)⁻¹) :=
      integrable_inv_one_add_sq.const_mul _
    have hbound : ∀ τ : ℝ, ‖F n τ‖ ≤
        (K * ‖LSeries.term a (c : ℂ) n‖) * (1 + τ ^ 2)⁻¹ := by
      intro τ
      rcases n.eq_zero_or_pos with rfl | hn
      · simp [F, a]
      · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
        have hdecay := primeMellinTransform_vertical_decay S C P c τ hSs hS01
          hS0 hS1 hC0 hC1 hC2 hP hc0 hc2
        have hterm : ‖LSeries.term a
            ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I) n‖ =
            ‖LSeries.term a (c : ℂ) n‖ := by
          simp only [LSeries.norm_term_eq, Complex.add_re, Complex.ofReal_re,
            Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
            mul_zero, sub_zero, mul_one, add_zero]
        simp only [F, norm_mul, hterm]
        calc
          ‖primeMellinTransform S P ((c : ℂ) + (τ : ℂ) * I)‖ *
                ‖LSeries.term a (c : ℂ) n‖
              ≤ (K / (1 + τ ^ 2)) * ‖LSeries.term a (c : ℂ) n‖ :=
            mul_le_mul_of_nonneg_right (by simpa only [K] using hdecay) (norm_nonneg _)
          _ = (K * ‖LSeries.term a (c : ℂ) n‖) * (1 + τ ^ 2)⁻¹ := by
            rw [div_eq_mul_inv]
            ring
    calc
      ∫ τ : ℝ, ‖F n τ‖ ≤ ∫ τ : ℝ,
          (K * ‖LSeries.term a (c : ℂ) n‖) * (1 + τ ^ 2)⁻¹ :=
        integral_mono (hFint n).norm hmajorant hbound
      _ = (K * Real.pi) * ‖LSeries.term a (c : ℂ) n‖ := by
        rw [integral_const_mul, integral_univ_inv_one_add_sq]
        ring
  have hinterchange : (∑' n : ℕ, ∫ τ : ℝ, F n τ) =
      ∫ τ : ℝ, ∑' n : ℕ, F n τ :=
    integral_tsum_of_summable_integral_norm hFint hFsum
  have htermIntegral (n : ℕ) :
      (1 / (2 * Real.pi) : ℂ) * ∫ τ : ℝ, F n τ =
        (primeMellinWindow S P n : ℂ) * LSeries.term a ((u : ℂ) * I) n := by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [F, a]
    · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
      have hpoint (τ : ℝ) : F n τ =
          (a n * (n : ℂ) ^ (-((u : ℂ) * I))) *
            ((n : ℂ) ^ (-((c : ℂ) + (τ : ℂ) * I)) *
              primeMellinTransform S P ((c : ℂ) + (τ : ℂ) * I)) := by
        dsimp only [F]
        rw [LSeries.term_of_ne_zero hn0, div_eq_mul_inv, ← Complex.cpow_neg]
        rw [show -((c : ℂ) + ((τ + u : ℝ) : ℂ) * I) =
            (-((c : ℂ) + (τ : ℂ) * I)) + (-((u : ℂ) * I)) by
          push_cast
          ring]
        rw [Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn0)]
        ring
      have hinv := primeMellin_inversion S C P c (n : ℝ) hSs hS01 hS0 hS1
        hC0 hC1 hC2 hP hc0 hc2 (by exact_mod_cast hn)
      rw [mellinInv] at hinv
      have hcoeff : ((1 / (2 * Real.pi) : ℝ) : ℂ) =
          1 / (2 * (Real.pi : ℂ)) := by norm_cast
      rw [Complex.real_smul, hcoeff] at hinv
      have hinv' : (1 / (2 * (Real.pi : ℂ))) *
          ∫ τ : ℝ, (n : ℂ) ^ (-((c : ℂ) + (τ : ℂ) * I)) *
            primeMellinTransform S P ((c : ℂ) + (τ : ℂ) * I) =
          (primeMellinWindow S P n : ℂ) := by
        simpa only [smul_eq_mul, Complex.ofReal_natCast] using hinv
      rw [integral_congr_ae (ae_of_all _ hpoint), integral_const_mul]
      rw [LSeries.term_of_ne_zero hn0]
      have htermu : a n / (n : ℂ) ^ ((u : ℂ) * I) =
          a n * (n : ℂ) ^ (-((u : ℂ) * I)) := by
        rw [div_eq_mul_inv, ← Complex.cpow_neg]
      rw [htermu]
      change (1 / (2 * (Real.pi : ℂ))) *
          ((a n * (n : ℂ) ^ (-((u : ℂ) * I))) *
            ∫ τ : ℝ, (n : ℂ) ^ (-((c : ℂ) + (τ : ℂ) * I)) *
              primeMellinTransform S P ((c : ℂ) + (τ : ℂ) * I)) = _
      calc
        _ = (a n * (n : ℂ) ^ (-((u : ℂ) * I))) *
            ((1 / (2 * (Real.pi : ℂ))) *
              ∫ τ : ℝ, (n : ℂ) ^ (-((c : ℂ) + (τ : ℂ) * I)) *
                primeMellinTransform S P ((c : ℂ) + (τ : ℂ) * I)) := by ring
        _ = (a n * (n : ℂ) ^ (-((u : ℂ) * I))) *
            (primeMellinWindow S P n : ℂ) := by rw [hinv']
        _ = (primeMellinWindow S P n : ℂ) *
            (a n * (n : ℂ) ^ (-((u : ℂ) * I))) := by ring
  have hinside (τ : ℝ) : (∑' n : ℕ, F n τ) =
      primeMellinTransform S P ((c : ℂ) + (τ : ℂ) * I) *
        LSeries a ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I) := by
    simp only [F, LSeries, tsum_mul_left]
  change (∑' n : ℕ, (primeMellinWindow S P n : ℂ) *
      LSeries.term a ((u : ℂ) * I) n) = _
  calc
    (∑' n : ℕ, (primeMellinWindow S P n : ℂ) *
        LSeries.term a ((u : ℂ) * I) n) =
        ∑' n : ℕ, (1 / (2 * Real.pi) : ℂ) * ∫ τ : ℝ, F n τ :=
      tsum_congr fun n => (htermIntegral n).symm
    _ = (1 / (2 * Real.pi) : ℂ) * ∑' n : ℕ, ∫ τ : ℝ, F n τ :=
      tsum_mul_left
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ τ : ℝ, ∑' n : ℕ, F n τ := by
      rw [hinterchange]
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ τ : ℝ,
        primeMellinTransform S P ((c : ℂ) + (τ : ℂ) * I) *
          LSeries a ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I) := by
      congr 2
      funext τ
      exact hinside τ

/-- The right-line representation at the campaign's chosen abscissa, with
the von Mangoldt Dirichlet series identified as `-ζ'/ζ`. -/
theorem primeMellin_vonMangoldt_zeta_representation
    (S : ℝ → ℝ) (C P u : ℝ)
    (hSs : ContDiff ℝ ∞ S)
    (hS01 : ∀ v, 0 ≤ S v ∧ S v ≤ 1)
    (hS0 : ∀ v, v ≤ 0 → S v = 0)
    (hS1 : ∀ v, 1 ≤ v → S v = 1)
    (hC0 : 0 ≤ C) (hC1 : ∀ v, |deriv S v| ≤ C)
    (hC2 : ∀ v, |deriv (deriv S) v| ≤ C)
    (hP : 2 ≤ P) :
    (∑' n : ℕ,
        (((ArithmeticFunction.vonMangoldt n * primeMellinWindow S P n : ℝ) : ℂ) *
          (n : ℂ) ^ (-((u : ℂ) * I)))) =
      (1 / (2 * Real.pi) : ℂ) * ∫ τ : ℝ,
        let c := 1 + 1 / Real.log (2 * P)
        primeMellinTransform S P ((c : ℂ) + (τ : ℂ) * I) *
          (-deriv riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I) /
            riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I)) := by
  let c : ℝ := 1 + 1 / Real.log (2 * P)
  have hlog1 : 1 < Real.log (2 * P) := by
    calc
      1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      _ ≤ Real.log (2 * P) := Real.strictMonoOn_log.monotoneOn
        (show 3 ∈ Set.Ioi (0 : ℝ) by norm_num)
        (show 2 * P ∈ Set.Ioi (0 : ℝ) by
          exact mul_pos (by norm_num : (0 : ℝ) < 2) (by linarith))
        (by linarith)
  have hlog0 : 0 < Real.log (2 * P) := by linarith
  have hc1 : 1 < c := by
    dsimp [c]
    have : 0 < 1 / Real.log (2 * P) := one_div_pos.mpr hlog0
    linarith
  have hc2 : c ≤ 2 := by
    dsimp [c]
    have hinv : 1 / Real.log (2 * P) ≤ 1 := by
      rw [div_le_iff₀ hlog0]
      linarith
    linarith
  have hrep := primeMellin_vonMangoldt_representation S C P c u hSs hS01 hS0 hS1
    hC0 hC1 hC2 hP hc1 hc2
  let a : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have hleft : (∑' n : ℕ,
      (((ArithmeticFunction.vonMangoldt n * primeMellinWindow S P n : ℝ) : ℂ) *
        (n : ℂ) ^ (-((u : ℂ) * I)))) =
      ∑' n : ℕ, (primeMellinWindow S P n : ℂ) *
        LSeries.term a ((u : ℂ) * I) n := by
    apply tsum_congr
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [a]
    · rw [LSeries.term_of_ne_zero (Nat.ne_of_gt hn), div_eq_mul_inv,
        ← Complex.cpow_neg]
      push_cast
      ring
  rw [hleft]
  change _ = (1 / (2 * Real.pi) : ℂ) * ∫ τ : ℝ,
      primeMellinTransform S P ((c : ℂ) + (τ : ℂ) * I) *
        (-deriv riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I) /
          riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I))
  rw [hrep]
  congr 2
  funext τ
  congr 1
  exact ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, add_zero]
    exact hc1)

/-- On the standard right line, absolute convergence and the real pole bound
give a uniform logarithmic bound for the von Mangoldt Dirichlet series. -/
theorem exists_norm_LSeries_vonMangoldt_le_log :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (P t : ℝ), 2 ≤ P →
      ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (((1 + 1 / Real.log (2 * P) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        A * Real.log (2 * P) := by
  open ArithmeticFunction in
    obtain ⟨cp, hcp⟩ := zeta_logDeriv_pole_bound
  refine ⟨|cp| + 2, by linarith [abs_nonneg cp], ?_⟩
  intro P t hP
  have hlog1 : 1 < Real.log (2 * P) := by
    calc
      1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      _ ≤ Real.log (2 * P) := Real.strictMonoOn_log.monotoneOn
        (show 3 ∈ Set.Ioi (0 : ℝ) by norm_num)
        (show 2 * P ∈ Set.Ioi (0 : ℝ) by
          exact mul_pos (by norm_num : (0 : ℝ) < 2) (by linarith))
        (by linarith)
  let c : ℝ := 1 + 1 / Real.log (2 * P)
  have hc1 : 1 < c := by
    dsimp [c]
    have : 0 < 1 / Real.log (2 * P) := one_div_pos.mpr (by linarith)
    linarith
  have hc2 : c ≤ 2 := by
    dsimp [c]
    have hinv : 1 / Real.log (2 * P) ≤ 1 := by
      rw [div_le_iff₀ (by linarith : 0 < Real.log (2 * P))]
      linarith
    linarith
  let a : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have himsum : Summable (fun n =>
      ‖LSeries.term a ((c : ℂ) + (t : ℂ) * I) n‖) :=
    summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simp [hc1]))
  have htermnorm :
      (∑' n : ℕ, ‖LSeries.term a ((c : ℂ) + (t : ℂ) * I) n‖) =
        ∑' n : ℕ, ‖LSeries.term a (c : ℂ) n‖ := by
    apply tsum_congr
    intro n
    simp only [LSeries.norm_term_eq, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, sub_zero, mul_one, add_zero]
  have hreal : (∑' n : ℕ, ‖LSeries.term a (c : ℂ) n‖) =
      (LSeries a (c : ℂ)).re := by
    have hr : (LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        (c : ℂ)).re = ∑' n : ℕ,
          ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c) := by
      simpa using re_LSeries_vonMangoldt c 0 hc1
    rw [hr]
    apply tsum_congr
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [a]
    · rw [LSeries.norm_term_eq]
      simp [a, Nat.ne_of_gt hn,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have hpole : (LSeries a (c : ℂ)).re ≤ Real.log (2 * P) + cp := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hc1]
    have h := hcp c hc1 hc2
    rw [← neg_div] at h
    calc
      _ ≤ 1 / (c - 1) + cp := h
      _ = Real.log (2 * P) + cp := by
        dsimp [c]
        field_simp
        ring
  calc
    ‖LSeries a ((c : ℂ) + (t : ℂ) * I)‖
        ≤ ∑' n : ℕ, ‖LSeries.term a ((c : ℂ) + (t : ℂ) * I) n‖ :=
      norm_tsum_le_tsum_norm himsum
    _ = (LSeries a (c : ℂ)).re := htermnorm.trans hreal
    _ ≤ Real.log (2 * P) + cp := hpole
    _ ≤ (|cp| + 2) * Real.log (2 * P) := by
      nlinarith [le_abs_self cp, abs_nonneg cp]

/-- The two tails of the quadratic Mellin majorant have mass at most `2/H`. -/
theorem integral_inv_one_add_sq_tail_le (H : ℝ) (hH : 0 < H) :
    ∫ τ : ℝ in Set.Iic (-H) ∪ Set.Ioi H, (1 + τ ^ 2)⁻¹ ≤ 2 / H := by
  have hrightInt : IntegrableOn (fun τ : ℝ => (1 + τ ^ 2)⁻¹) (Set.Ioi H) :=
    integrable_inv_one_add_sq.integrableOn
  have hpowInt : IntegrableOn (fun τ : ℝ => τ ^ (-2 : ℝ)) (Set.Ioi H) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hH
  have hright : (∫ τ : ℝ in Set.Ioi H, (1 + τ ^ 2)⁻¹) ≤ 1 / H := by
    calc
      _ ≤ ∫ τ : ℝ in Set.Ioi H, τ ^ (-2 : ℝ) := by
        apply integral_mono_ae hrightInt hpowInt
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
        have hτ0 : 0 < τ := hH.trans hτ
        rw [Real.rpow_neg hτ0.le]
        norm_num
        exact (inv_le_inv₀ (by positivity) (sq_pos_of_pos hτ0)).2 (by linarith)
      _ = 1 / H := by
        rw [integral_Ioi_rpow_of_lt (by norm_num) hH]
        norm_num [Real.rpow_neg_one]
  have hleft : (∫ τ : ℝ in Set.Iic (-H), (1 + τ ^ 2)⁻¹) =
      ∫ τ : ℝ in Set.Ioi H, (1 + τ ^ 2)⁻¹ := by
    have h := integral_comp_neg_Iic (-H) (fun τ : ℝ => (1 + τ ^ 2)⁻¹)
    simp only [neg_neg] at h
    convert h using 1
    congr 1
    funext τ
    ring
  rw [setIntegral_union (Iic_disjoint_Ioi (by linarith)) measurableSet_Ioi
    integrable_inv_one_add_sq.integrableOn hrightInt, hleft]
  calc
    _ ≤ 1 / H + 1 / H := add_le_add hright hright
    _ = 2 / H := by ring

/-- **V-A-3.** The part of the standard right-line integral outside
`[-H,H]` is `O(P^c log(2P) / H)`, uniformly in the vertical translate. -/
theorem exists_primeMellin_right_tail_bound :
    ∃ B : ℝ, 1 ≤ B ∧ ∀
      (S : ℝ → ℝ) (C P u H : ℝ),
      ContDiff ℝ ∞ S →
      (∀ v, 0 ≤ S v ∧ S v ≤ 1) →
      (∀ v, v ≤ 0 → S v = 0) →
      (∀ v, 1 ≤ v → S v = 1) →
      0 ≤ C → (∀ v, |deriv S v| ≤ C) →
      (∀ v, |deriv (deriv S) v| ≤ C) →
      2 ≤ P → 0 < H →
      let c := 1 + 1 / Real.log (2 * P)
      ‖(1 / (2 * Real.pi) : ℂ) *
          ∫ τ : ℝ in Set.Iic (-H) ∪ Set.Ioi H,
            primeMellinTransform S P ((c : ℂ) + (τ : ℂ) * I) *
              (-deriv riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I) /
                riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I))‖ ≤
        B * (C + 1) ^ 2 * P ^ c * Real.log (2 * P) / H := by
  obtain ⟨A, hA1, hALS⟩ := exists_norm_LSeries_vonMangoldt_le_log
  refine ⟨500000 * A, by nlinarith, ?_⟩
  intro S C P u H hSs hS01 hS0 hS1 hC0 hC1 hC2 hP hH
  let c : ℝ := 1 + 1 / Real.log (2 * P)
  have hlog1 : 1 < Real.log (2 * P) := by
    calc
      1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      _ ≤ Real.log (2 * P) := Real.strictMonoOn_log.monotoneOn
        (show 3 ∈ Set.Ioi (0 : ℝ) by norm_num)
        (show 2 * P ∈ Set.Ioi (0 : ℝ) by
          exact mul_pos (by norm_num : (0 : ℝ) < 2) (by linarith))
        (by linarith)
  have hc1 : 1 < c := by
    dsimp [c]
    have : 0 < 1 / Real.log (2 * P) := one_div_pos.mpr (by linarith)
    linarith
  have hc2 : c ≤ 2 := by
    dsimp [c]
    have hinv : 1 / Real.log (2 * P) ≤ 1 := by
      rw [div_le_iff₀ (by linarith : 0 < Real.log (2 * P))]
      linarith
    linarith
  let D : ℝ := 250000 * (C + 1) ^ 2 * P ^ c * (A * Real.log (2 * P))
  have hD0 : 0 ≤ D := by
    dsimp [D]
    positivity
  have hmajorant : Integrable (fun τ : ℝ => D * (1 + τ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul D
  let f : ℝ → ℂ := fun τ =>
    primeMellinTransform S P ((c : ℂ) + (τ : ℂ) * I) *
      (-deriv riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I) /
        riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I))
  have hfbound (τ : ℝ) : ‖f τ‖ ≤ D * (1 + τ ^ 2)⁻¹ := by
    have hdecay := primeMellinTransform_vertical_decay S C P c τ hSs hS01
      hS0 hS1 hC0 hC1 hC2 hP (by linarith) hc2
    have hzeta :
        ‖-deriv riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I) /
            riemannZeta ((c : ℂ) + ((τ + u : ℝ) : ℂ) * I)‖ ≤
          A * Real.log (2 * P) := by
      rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, add_zero]
        exact hc1)]
      simpa only [c] using hALS P (τ + u) hP
    simp only [f, norm_mul]
    calc
      _ ≤ (250000 * (C + 1) ^ 2 * P ^ c / (1 + τ ^ 2)) *
          (A * Real.log (2 * P)) :=
        mul_le_mul hdecay hzeta (norm_nonneg _) (by positivity)
      _ = D * (1 + τ ^ 2)⁻¹ := by
        dsimp [D]
        rw [div_eq_mul_inv]
        ring
  have hint : ‖∫ τ : ℝ in Set.Iic (-H) ∪ Set.Ioi H, f τ‖ ≤
      ∫ τ : ℝ in Set.Iic (-H) ∪ Set.Ioi H, D * (1 + τ ^ 2)⁻¹ :=
    norm_integral_le_of_norm_le hmajorant.integrableOn (ae_of_all _ hfbound)
  have htail := integral_inv_one_add_sq_tail_le H hH
  have htailD : (∫ τ : ℝ in Set.Iic (-H) ∪ Set.Ioi H,
      D * (1 + τ ^ 2)⁻¹) ≤ D * (2 / H) := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left htail hD0
  have hcoef : ‖(1 / (2 * Real.pi) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [div_le_one (mul_pos (by norm_num) Real.pi_pos)]
    nlinarith [Real.two_le_pi]
  change ‖(1 / (2 * Real.pi) : ℂ) * ∫ τ : ℝ in Set.Iic (-H) ∪ Set.Ioi H,
      f τ‖ ≤ _
  calc
    _ = ‖(1 / (2 * Real.pi) : ℂ)‖ *
        ‖∫ τ : ℝ in Set.Iic (-H) ∪ Set.Ioi H, f τ‖ := norm_mul _ _
    _ ≤ ‖∫ τ : ℝ in Set.Iic (-H) ∪ Set.Ioi H, f τ‖ := by
      nlinarith [norm_nonneg (∫ τ : ℝ in Set.Iic (-H) ∪ Set.Ioi H, f τ)]
    _ ≤ ∫ τ : ℝ in Set.Iic (-H) ∪ Set.Ioi H,
        D * (1 + τ ^ 2)⁻¹ := hint
    _ ≤ D * (2 / H) := htailD
    _ = (500000 * A) * (C + 1) ^ 2 * P ^ c * Real.log (2 * P) / H := by
      dsimp [D]
      ring

/-- The positively oriented boundary integral of `1/z` around an
axis-parallel rectangle containing the origin is `2πi`.  This elementary
form is convenient for the pole term in the Mellin shift. -/
theorem integral_boundary_rect_inv (A B Y : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hY : 0 < Y) :
    (∫ x : ℝ in -B..A, ((x : ℂ) - (Y : ℂ) * I)⁻¹) -
        (∫ x : ℝ in -B..A, ((x : ℂ) + (Y : ℂ) * I)⁻¹) +
      I * (∫ y : ℝ in -Y..Y, ((A : ℂ) + (y : ℂ) * I)⁻¹) -
      I * (∫ y : ℝ in -Y..Y, (-(B : ℂ) + (y : ℂ) * I)⁻¹) =
        2 * Real.pi * I := by
  let fb : ℝ → ℂ := fun x => ((x : ℂ) - (Y : ℂ) * I)⁻¹
  let ft : ℝ → ℂ := fun x => ((x : ℂ) + (Y : ℂ) * I)⁻¹
  let fr : ℝ → ℂ := fun y => ((A : ℂ) + (y : ℂ) * I)⁻¹
  let fl : ℝ → ℂ := fun y => (-(B : ℂ) + (y : ℂ) * I)⁻¹
  have hfb : IntervalIntegrable fb volume (-B) A := by
    apply Continuous.intervalIntegrable
    exact (continuous_ofReal.sub (continuous_const.mul continuous_const)).inv₀ fun x hx => by
      have := congrArg Complex.im hx
      simp [hY.ne'] at this
  have hft : IntervalIntegrable ft volume (-B) A := by
    apply Continuous.intervalIntegrable
    exact (continuous_ofReal.add (continuous_const.mul continuous_const)).inv₀ fun x hx => by
      have := congrArg Complex.im hx
      simp [hY.ne'] at this
  have hfr : IntervalIntegrable fr volume (-Y) Y := by
    apply Continuous.intervalIntegrable
    exact (continuous_const.add (continuous_ofReal.mul continuous_const)).inv₀ fun y hy => by
      have := congrArg Complex.re hy
      simp [hA.ne'] at this
  have hfl : IntervalIntegrable fl volume (-Y) Y := by
    apply Continuous.intervalIntegrable
    exact (continuous_const.add (continuous_ofReal.mul continuous_const)).inv₀ fun y hy => by
      have := congrArg Complex.re hy
      simp [hB.ne'] at this
  have hre {f : ℝ → ℂ} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
      (∫ x : ℝ in a..b, f x).re = ∫ x : ℝ in a..b, (f x).re := by
    exact ((@RCLike.reCLM ℂ _).intervalIntegral_comp_comm hf).symm
  have him {f : ℝ → ℂ} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
      (∫ x : ℝ in a..b, f x).im = ∫ x : ℝ in a..b, (f x).im := by
    exact ((@RCLike.imCLM ℂ _).intervalIntegral_comp_comm hf).symm
  have hodd (c : ℝ) : (∫ y : ℝ in -Y..Y, y / (c ^ 2 + y ^ 2)) = 0 := by
    have h := intervalIntegral.integral_comp_neg
      (fun y : ℝ => y / (c ^ 2 + y ^ 2)) (a := -Y) (b := Y)
    have heq : (∫ y : ℝ in -Y..Y, -(y / (c ^ 2 + y ^ 2))) =
        ∫ y : ℝ in -Y..Y, y / (c ^ 2 + y ^ 2) := by
      simpa only [neg_neg, neg_sq, neg_div] using h
    rw [intervalIntegral.integral_neg] at heq
    linarith
  change (∫ x : ℝ in -B..A, fb x) - (∫ x : ℝ in -B..A, ft x) +
      I * (∫ y : ℝ in -Y..Y, fr y) - I * (∫ y : ℝ in -Y..Y, fl y) = _
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, zero_mul, one_mul]
    rw [hre hfb, hre hft, him hfr, him hfl]
    simp [fb, ft, fr, fl, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
    rw [show (∫ x : ℝ in -Y..Y, -x / (A * A + x * x)) =
        -(∫ x : ℝ in -Y..Y, x / (A ^ 2 + x ^ 2)) by
      rw [← intervalIntegral.integral_neg]
      congr 1
      funext x
      ring]
    rw [show (∫ x : ℝ in -Y..Y, -x / (B * B + x * x)) =
        -(∫ x : ℝ in -Y..Y, x / (B ^ 2 + x ^ 2)) by
      rw [← intervalIntegral.integral_neg]
      congr 1
      funext x
      ring]
    rw [hodd A, hodd B]
    norm_num
  · simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, zero_add]
    rw [him hfb, him hft, hre hfr, hre hfl]
    simp [fb, ft, fr, fl, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
    push_cast
    have hYint : (∫ x : ℝ in -B..A, Y / (x * x + Y * Y)) =
        Real.arctan (A / Y) + Real.arctan (B / Y) := by
      convert integral_div_sq_add_sq (a := -B) (b := A) (c := Y) using 1
      · congr 1
        funext x
        congr 1
        ring
      rw [show -B / Y = -(B / Y) by ring, Real.arctan_neg]
      ring
    have hAint : (∫ y : ℝ in -Y..Y, A / (A * A + y * y)) =
        2 * Real.arctan (Y / A) := by
      convert integral_div_sq_add_sq (a := -Y) (b := Y) (c := A) using 1
      · congr 1
        funext y
        congr 1
        ring
      rw [show -Y / A = -(Y / A) by ring, Real.arctan_neg]
      ring
    have hBint : (∫ y : ℝ in -Y..Y, B / (B * B + y * y)) =
        2 * Real.arctan (Y / B) := by
      convert integral_div_sq_add_sq (a := -Y) (b := Y) (c := B) using 1
      · congr 1
        funext y
        congr 1
        ring
      rw [show -Y / B = -(Y / B) by ring, Real.arctan_neg]
      ring
    rw [show (∫ x : ℝ in -B..A, -Y / (x * x + Y * Y)) =
        -(∫ x : ℝ in -B..A, Y / (x * x + Y * Y)) by
      rw [← intervalIntegral.integral_neg]
      congr 1
      funext x
      ring]
    rw [show (∫ x : ℝ in -Y..Y, -B / (B * B + x * x)) =
        -(∫ x : ℝ in -Y..Y, B / (B * B + x * x)) by
      rw [← intervalIntegral.integral_neg]
      congr 1
      funext x
      ring]
    rw [hYint, hAint, hBint]
    rw [show Y / A = (A / Y)⁻¹ by field_simp,
      show Y / B = (B / Y)⁻¹ by field_simp,
      Real.arctan_inv_of_pos (div_pos hA hY),
      Real.arctan_inv_of_pos (div_pos hB hY)]
    ring

/-- The entire function `(z - 1) ζ(z)`, expressed using the tree's entire
regularization of the zeta pole. -/
noncomputable def zetaPoleRemoved (G : ℂ → ℂ) (z : ℂ) : ℂ :=
  1 + (z - 1) * G z

/-- The analytic regular part of `-ζ'/ζ` attached to a pole
regularization `G`. -/
noncomputable def zetaLogDerivRegular (G : ℂ → ℂ) (z : ℂ) : ℂ :=
  -deriv (zetaPoleRemoved G) z / zetaPoleRemoved G z

theorem zetaPoleRemoved_differentiable (G : ℂ → ℂ)
    (hG : Differentiable ℂ G) : Differentiable ℂ (zetaPoleRemoved G) := by
  unfold zetaPoleRemoved
  fun_prop

theorem zetaPoleRemoved_eq (G : ℂ → ℂ)
    (hGval : ∀ z : ℂ, z ≠ 1 → G z = riemannZeta z - 1 / (z - 1))
    (z : ℂ) (hz : z ≠ 1) :
    zetaPoleRemoved G z = (z - 1) * riemannZeta z := by
  rw [zetaPoleRemoved, hGval z hz]
  field_simp [sub_ne_zero.mpr hz]
  ring

theorem zetaLogDerivRegular_differentiableOn (G : ℂ → ℂ)
    (hG : Differentiable ℂ G) (U : Set ℂ)
    (hne : ∀ z ∈ U, zetaPoleRemoved G z ≠ 0) :
    DifferentiableOn ℂ (zetaLogDerivRegular G) U := by
  have hF := zetaPoleRemoved_differentiable G hG
  have hF' : Differentiable ℂ (deriv (zetaPoleRemoved G)) := by
    simpa only [differentiableOn_univ] using hF.differentiableOn.deriv isOpen_univ
  intro z hz
  exact ((hF' z).neg.div (hF z) (hne z hz)).differentiableWithinAt

theorem zetaLogDerivRegular_differentiableAt (G : ℂ → ℂ)
    (hG : Differentiable ℂ G) (z : ℂ)
    (hne : zetaPoleRemoved G z ≠ 0) :
    DifferentiableAt ℂ (zetaLogDerivRegular G) z := by
  have hF := zetaPoleRemoved_differentiable G hG
  have hF' : Differentiable ℂ (deriv (zetaPoleRemoved G)) := by
    simpa only [differentiableOn_univ] using hF.differentiableOn.deriv isOpen_univ
  exact (hF' z).neg.div (hF z) hne

theorem zetaLogDerivRegular_eq (G : ℂ → ℂ)
    (hG : Differentiable ℂ G)
    (hGval : ∀ z : ℂ, z ≠ 1 → G z = riemannZeta z - 1 / (z - 1))
    (z : ℂ) (hz : z ≠ 1) (hζ : riemannZeta z ≠ 0) :
    zetaLogDerivRegular G z =
      -deriv riemannZeta z / riemannZeta z - 1 / (z - 1) := by
  have hF := zetaPoleRemoved_differentiable G hG
  have hev : zetaPoleRemoved G =ᶠ[𝓝 z]
      fun w => (w - 1) * riemannZeta w := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    exact zetaPoleRemoved_eq G hGval w hw
  have hprod : HasDerivAt (fun w : ℂ => (w - 1) * riemannZeta w)
      (riemannZeta z + (z - 1) * deriv riemannZeta z) z := by
    convert! ((hasDerivAt_id z).sub_const 1).mul
      (differentiableAt_riemannZeta hz).hasDerivAt using 1 <;> simp [id_eq] <;> ring
  rw [zetaLogDerivRegular, hev.deriv_eq, hprod.deriv,
    zetaPoleRemoved_eq G hGval z hz]
  field_simp [sub_ne_zero.mpr hz, hζ]
  ring

/-- Cauchy's formula on the campaign rectangle, written with `dslope` as
the removable quotient.  The rectangle is centered at the pole, so its
translated zeta heights are exactly `[-Y,Y]`. -/
theorem primeMellin_pole_rectangle (W : ℂ → ℂ)
    (hW : Differentiable ℂ W) (s₀ : ℂ) (A B Y : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hY : 0 < Y) :
    (∫ x : ℝ in -B..A, W (s₀ + ((x : ℂ) - (Y : ℂ) * I)) /
        ((x : ℂ) - (Y : ℂ) * I)) -
      (∫ x : ℝ in -B..A, W (s₀ + ((x : ℂ) + (Y : ℂ) * I)) /
        ((x : ℂ) + (Y : ℂ) * I)) +
      I * (∫ y : ℝ in -Y..Y, W (s₀ + ((A : ℂ) + (y : ℂ) * I)) /
        ((A : ℂ) + (y : ℂ) * I)) -
      I * (∫ y : ℝ in -Y..Y, W (s₀ + (-(B : ℂ) + (y : ℂ) * I)) /
        (-(B : ℂ) + (y : ℂ) * I)) =
        2 * Real.pi * I * W s₀ := by
  let U : ℂ → ℂ := fun z => W (s₀ + z)
  let d : ℂ → ℂ := dslope U 0
  let r : ℂ → ℂ := fun z => U 0 * z⁻¹
  have hU : Differentiable ℂ U := hW.comp (by fun_prop)
  have hdOn : DifferentiableOn ℂ d Set.univ := by
    exact (Complex.differentiableOn_dslope univ_mem).mpr hU.differentiableOn
  have hd : Differentiable ℂ d := by
    simpa only [differentiableOn_univ] using hdOn
  have hdrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn d
    ((-B : ℂ) - (Y : ℂ) * I) ((A : ℂ) + (Y : ℂ) * I)
    hd.differentiableOn
  have hdrect' :
      (∫ x : ℝ in -B..A, d ((x : ℂ) - (Y : ℂ) * I)) -
        (∫ x : ℝ in -B..A, d ((x : ℂ) + (Y : ℂ) * I)) +
        I * (∫ y : ℝ in -Y..Y, d ((A : ℂ) + (y : ℂ) * I)) -
        I * (∫ y : ℝ in -Y..Y, d (-(B : ℂ) + (y : ℂ) * I)) = 0 := by
    simpa [smul_eq_mul] using! hdrect
  have hpoint (z : ℂ) (hz : z ≠ 0) : U z / z = d z + r z := by
    dsimp [d, r]
    rw [dslope_of_ne U hz, slope]
    simp only [sub_zero, vsub_eq_sub, div_eq_mul_inv, smul_eq_mul]
    ring
  have hdB : IntervalIntegrable (fun x : ℝ => d ((x : ℂ) - (Y : ℂ) * I))
      volume (-B) A := by
    apply Continuous.intervalIntegrable
    exact hd.continuous.comp
      (continuous_ofReal.sub (continuous_const.mul continuous_const))
  have hdT : IntervalIntegrable (fun x : ℝ => d ((x : ℂ) + (Y : ℂ) * I))
      volume (-B) A := by
    apply Continuous.intervalIntegrable
    exact hd.continuous.comp
      (continuous_ofReal.add (continuous_const.mul continuous_const))
  have hdR : IntervalIntegrable (fun y : ℝ => d ((A : ℂ) + (y : ℂ) * I))
      volume (-Y) Y := by
    apply Continuous.intervalIntegrable
    exact hd.continuous.comp
      (continuous_const.add (continuous_ofReal.mul continuous_const))
  have hdL : IntervalIntegrable (fun y : ℝ => d (-(B : ℂ) + (y : ℂ) * I))
      volume (-Y) Y := by
    apply Continuous.intervalIntegrable
    exact hd.continuous.comp
      (continuous_const.add (continuous_ofReal.mul continuous_const))
  have hrB : IntervalIntegrable (fun x : ℝ => r ((x : ℂ) - (Y : ℂ) * I))
      volume (-B) A := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul
      ((continuous_ofReal.sub (continuous_const.mul continuous_const)).inv₀ fun x hx => by
        have := congrArg Complex.im hx
        simp [hY.ne'] at this)
  have hrT : IntervalIntegrable (fun x : ℝ => r ((x : ℂ) + (Y : ℂ) * I))
      volume (-B) A := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul
      ((continuous_ofReal.add (continuous_const.mul continuous_const)).inv₀ fun x hx => by
        have := congrArg Complex.im hx
        simp [hY.ne'] at this)
  have hrR : IntervalIntegrable (fun y : ℝ => r ((A : ℂ) + (y : ℂ) * I))
      volume (-Y) Y := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul
      ((continuous_const.add (continuous_ofReal.mul continuous_const)).inv₀ fun y hy => by
        have := congrArg Complex.re hy
        simp [hA.ne'] at this)
  have hrL : IntervalIntegrable (fun y : ℝ => r (-(B : ℂ) + (y : ℂ) * I))
      volume (-Y) Y := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul
      ((continuous_const.add (continuous_ofReal.mul continuous_const)).inv₀ fun y hy => by
        have := congrArg Complex.re hy
        simp [hB.ne'] at this)
  have hbot : (∫ x : ℝ in -B..A, U ((x : ℂ) - (Y : ℂ) * I) /
      ((x : ℂ) - (Y : ℂ) * I)) =
      (∫ x : ℝ in -B..A, d ((x : ℂ) - (Y : ℂ) * I)) +
      ∫ x : ℝ in -B..A, r ((x : ℂ) - (Y : ℂ) * I) := by
    rw [← intervalIntegral.integral_add hdB hrB]
    apply intervalIntegral.integral_congr
    intro x _
    apply hpoint
    intro hx
    have := congrArg Complex.im hx
    simp [hY.ne'] at this
  have htop : (∫ x : ℝ in -B..A, U ((x : ℂ) + (Y : ℂ) * I) /
      ((x : ℂ) + (Y : ℂ) * I)) =
      (∫ x : ℝ in -B..A, d ((x : ℂ) + (Y : ℂ) * I)) +
      ∫ x : ℝ in -B..A, r ((x : ℂ) + (Y : ℂ) * I) := by
    rw [← intervalIntegral.integral_add hdT hrT]
    apply intervalIntegral.integral_congr
    intro x _
    apply hpoint
    intro hx
    have := congrArg Complex.im hx
    simp [hY.ne'] at this
  have hright : (∫ y : ℝ in -Y..Y, U ((A : ℂ) + (y : ℂ) * I) /
      ((A : ℂ) + (y : ℂ) * I)) =
      (∫ y : ℝ in -Y..Y, d ((A : ℂ) + (y : ℂ) * I)) +
      ∫ y : ℝ in -Y..Y, r ((A : ℂ) + (y : ℂ) * I) := by
    rw [← intervalIntegral.integral_add hdR hrR]
    apply intervalIntegral.integral_congr
    intro y _
    apply hpoint
    intro hy
    have := congrArg Complex.re hy
    simp [hA.ne'] at this
  have hleft : (∫ y : ℝ in -Y..Y, U (-(B : ℂ) + (y : ℂ) * I) /
      (-(B : ℂ) + (y : ℂ) * I)) =
      (∫ y : ℝ in -Y..Y, d (-(B : ℂ) + (y : ℂ) * I)) +
      ∫ y : ℝ in -Y..Y, r (-(B : ℂ) + (y : ℂ) * I) := by
    rw [← intervalIntegral.integral_add hdL hrL]
    apply intervalIntegral.integral_congr
    intro y _
    apply hpoint
    intro hy
    have := congrArg Complex.re hy
    simp [hB.ne'] at this
  change (∫ x : ℝ in -B..A, U ((x : ℂ) - (Y : ℂ) * I) /
      ((x : ℂ) - (Y : ℂ) * I)) - _ + I * _ - I * _ = _
  rw [hbot, htop, hright, hleft]
  simp only [r, U, zero_add, intervalIntegral.integral_const_mul]
  rw [show W (s₀ + 0) = W s₀ by ring]
  calc
    _ = ((∫ x : ℝ in -B..A, d ((x : ℂ) - (Y : ℂ) * I)) -
          (∫ x : ℝ in -B..A, d ((x : ℂ) + (Y : ℂ) * I)) +
          I * (∫ y : ℝ in -Y..Y, d ((A : ℂ) + (y : ℂ) * I)) -
          I * (∫ y : ℝ in -Y..Y, d (-(B : ℂ) + (y : ℂ) * I))) +
        W s₀ * ((∫ x : ℝ in -B..A, ((x : ℂ) - (Y : ℂ) * I)⁻¹) -
          (∫ x : ℝ in -B..A, ((x : ℂ) + (Y : ℂ) * I)⁻¹) +
          I * (∫ y : ℝ in -Y..Y, ((A : ℂ) + (y : ℂ) * I)⁻¹) -
          I * (∫ y : ℝ in -Y..Y, (-(B : ℂ) + (y : ℂ) * I)⁻¹)) := by ring
    _ = 0 + W s₀ * (2 * Real.pi * I) := by
      rw [hdrect', integral_boundary_rect_inv A B Y hA hB hY]
    _ = 2 * Real.pi * I * W s₀ := by ring

/-- **V-A-4 (the asymmetric Mellin rectangle).**  After centering the
rectangle at `1 - iu`, its translated zeta argument is `1 + z`; hence its
imaginary coordinate runs over exactly `[-Y,Y]`.  The pole term is evaluated
by `primeMellin_pole_rectangle`, while the regular part has zero boundary
integral. -/
theorem primeMellin_zeta_rectangle (W : ℂ → ℂ)
    (hW : Differentiable ℂ W) (η c Y u : ℝ)
    (hη : 0 < η) (hc1 : 1 < c) (hc2 : c ≤ 2) (hY : 0 < Y)
    (hzero : ∀ s : ℂ, 1 - η ≤ s.re → s.re ≤ 2 → |s.im| ≤ Y →
      s ≠ 1 → riemannZeta s ≠ 0) :
    let s₀ : ℂ := 1 - (u : ℂ) * I
    let A : ℝ := c - 1
    let B : ℝ := η / 2
    (∫ x : ℝ in -B..A,
        W (s₀ + ((x : ℂ) - (Y : ℂ) * I)) *
          (-deriv riemannZeta (1 + (x : ℂ) - (Y : ℂ) * I) /
            riemannZeta (1 + (x : ℂ) - (Y : ℂ) * I))) -
      (∫ x : ℝ in -B..A,
        W (s₀ + ((x : ℂ) + (Y : ℂ) * I)) *
          (-deriv riemannZeta (1 + (x : ℂ) + (Y : ℂ) * I) /
            riemannZeta (1 + (x : ℂ) + (Y : ℂ) * I))) +
      I * (∫ y : ℝ in -Y..Y,
        W (s₀ + ((A : ℂ) + (y : ℂ) * I)) *
          (-deriv riemannZeta (1 + (A : ℂ) + (y : ℂ) * I) /
            riemannZeta (1 + (A : ℂ) + (y : ℂ) * I))) -
      I * (∫ y : ℝ in -Y..Y,
        W (s₀ + (-(B : ℂ) + (y : ℂ) * I)) *
          (-deriv riemannZeta (1 - (B : ℂ) + (y : ℂ) * I) /
            riemannZeta (1 - (B : ℂ) + (y : ℂ) * I))) =
        2 * Real.pi * I * W s₀ := by
  dsimp only
  let s₀ : ℂ := 1 - (u : ℂ) * I
  let A : ℝ := c - 1
  let B : ℝ := η / 2
  have hA : 0 < A := by dsimp [A]; linarith
  have hB : 0 < B := by dsimp [B]; linarith
  obtain ⟨G, hG, hGval⟩ := exists_zeta_pole_reg
  let R : Set ℂ := Set.uIcc (-B) A ×ℂ Set.uIcc (-Y) Y
  have hcoord (z : ℂ) (hz : z ∈ R) :
      -B ≤ z.re ∧ z.re ≤ A ∧ -Y ≤ z.im ∧ z.im ≤ Y := by
    rcases hz with ⟨hzre, hzim⟩
    rw [Set.uIcc_of_le (by linarith : -B ≤ A)] at hzre
    rw [Set.uIcc_of_le (by linarith : -Y ≤ Y)] at hzim
    exact ⟨hzre.1, hzre.2, hzim.1, hzim.2⟩
  have hremoved (z : ℂ) (hz : z ∈ R) :
      zetaPoleRemoved G (1 + z) ≠ 0 := by
    rcases eq_or_ne z 0 with rfl | hz0
    · simp [zetaPoleRemoved]
    · have hone : (1 : ℂ) + z ≠ 1 := by
        intro h
        apply hz0
        linear_combination h
      have hc := hcoord z hz
      rw [zetaPoleRemoved_eq G hGval (1 + z) hone]
      apply mul_ne_zero
      · simpa only [add_sub_cancel_left] using hz0
      · apply hzero (1 + z)
        · simp only [Complex.add_re, Complex.one_re]
          dsimp [B] at hc
          linarith
        · simp only [Complex.add_re, Complex.one_re]
          dsimp [A] at hc
          linarith
        · simp only [Complex.add_im, Complex.one_im, zero_add]
          rw [abs_le]
          exact ⟨hc.2.2.1, hc.2.2.2⟩
        · exact hone
  let q : ℂ → ℂ := fun z =>
    W (s₀ + z) * zetaLogDerivRegular G (1 + z)
  have hqAt (z : ℂ) (hz : z ∈ R) : DifferentiableAt ℂ q z := by
    exact ((hW (s₀ + z)).comp z (by fun_prop)).mul
      ((zetaLogDerivRegular_differentiableAt G hG (1 + z)
        (hremoved z hz)).comp z (by fun_prop))
  have hq : DifferentiableOn ℂ q R := fun z hz => (hqAt z hz).differentiableWithinAt
  have hqrect : DifferentiableOn ℂ q
      (Set.uIcc ((-B : ℂ) - (Y : ℂ) * I).re ((A : ℂ) + (Y : ℂ) * I).re ×ℂ
        Set.uIcc ((-B : ℂ) - (Y : ℂ) * I).im ((A : ℂ) + (Y : ℂ) * I).im) := by
    simpa [R, Set.uIcc_of_le (by linarith : -B ≤ A),
      Set.uIcc_of_le (by linarith : -Y ≤ Y)] using hq
  have hregRect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn q
    ((-B : ℂ) - (Y : ℂ) * I) ((A : ℂ) + (Y : ℂ) * I) hqrect
  have hregRect' :
      (∫ x : ℝ in -B..A,
          W (s₀ + ((x : ℂ) - (Y : ℂ) * I)) *
            zetaLogDerivRegular G (1 + (x : ℂ) - (Y : ℂ) * I)) -
        (∫ x : ℝ in -B..A,
          W (s₀ + ((x : ℂ) + (Y : ℂ) * I)) *
            zetaLogDerivRegular G (1 + (x : ℂ) + (Y : ℂ) * I)) +
        I * (∫ y : ℝ in -Y..Y,
          W (s₀ + ((A : ℂ) + (y : ℂ) * I)) *
            zetaLogDerivRegular G (1 + (A : ℂ) + (y : ℂ) * I)) -
        I * (∫ y : ℝ in -Y..Y,
          W (s₀ + (-(B : ℂ) + (y : ℂ) * I)) *
            zetaLogDerivRegular G (1 - (B : ℂ) + (y : ℂ) * I)) = 0 := by
    simpa [q, smul_eq_mul, sub_eq_add_neg, add_assoc] using hregRect
  have hdecomp (z : ℂ) (hz : z ∈ R) (hz0 : z ≠ 0) :
      W (s₀ + z) *
          (-deriv riemannZeta (1 + z) / riemannZeta (1 + z)) =
        W (s₀ + z) * zetaLogDerivRegular G (1 + z) + W (s₀ + z) / z := by
    have hone : (1 : ℂ) + z ≠ 1 := by
      intro h
      apply hz0
      linear_combination h
    have hζ : riemannZeta (1 + z) ≠ 0 := by
      have hc := hcoord z hz
      apply hzero (1 + z)
      · simp only [Complex.add_re, Complex.one_re]
        dsimp [B] at hc
        linarith
      · simp only [Complex.add_re, Complex.one_re]
        dsimp [A] at hc
        linarith
      · simp only [Complex.add_im, Complex.one_im, zero_add]
        rw [abs_le]
        exact ⟨hc.2.2.1, hc.2.2.2⟩
      · exact hone
    rw [zetaLogDerivRegular_eq G hG hGval (1 + z) hone hζ]
    have hzsub : (1 : ℂ) + z - 1 = z := by ring
    rw [hzsub]
    ring
  have hpole := primeMellin_pole_rectangle W hW s₀ A B Y hA hB hY
  have hbotMem (x : ℝ) (hx : x ∈ Set.uIcc (-B) A) :
      (x : ℂ) - (Y : ℂ) * I ∈ R := by
    rw [show R = Set.uIcc (-B) A ×ℂ Set.uIcc (-Y) Y from rfl, mem_reProdIm]
    constructor
    · simpa using hx
    · simpa [Set.uIcc_of_le (by linarith : -Y ≤ Y)] using hY.le
  have htopMem (x : ℝ) (hx : x ∈ Set.uIcc (-B) A) :
      (x : ℂ) + (Y : ℂ) * I ∈ R := by
    rw [show R = Set.uIcc (-B) A ×ℂ Set.uIcc (-Y) Y from rfl, mem_reProdIm]
    constructor
    · simpa using hx
    · simpa [Set.uIcc_of_le (by linarith : -Y ≤ Y)] using hY.le
  have hrightMem (y : ℝ) (hy : y ∈ Set.uIcc (-Y) Y) :
      (A : ℂ) + (y : ℂ) * I ∈ R := by
    rw [show R = Set.uIcc (-B) A ×ℂ Set.uIcc (-Y) Y from rfl, mem_reProdIm]
    constructor
    · have : -B ≤ A := by linarith
      simpa [Set.uIcc_of_le this] using this
    · simpa using hy
  have hleftMem (y : ℝ) (hy : y ∈ Set.uIcc (-Y) Y) :
      -(B : ℂ) + (y : ℂ) * I ∈ R := by
    rw [show R = Set.uIcc (-B) A ×ℂ Set.uIcc (-Y) Y from rfl, mem_reProdIm]
    constructor
    · have : -B ≤ A := by linarith
      simpa [Set.uIcc_of_le this] using this
    · simpa using hy
  have hside
      (f g r : ℝ → ℂ) (a b : ℝ)
      (hf : IntervalIntegrable f volume a b)
      (hg : IntervalIntegrable g volume a b)
      (heq : ∀ x ∈ Set.uIcc a b, r x = f x + g x) :
      (∫ x : ℝ in a..b, r x) =
        (∫ x : ℝ in a..b, f x) + ∫ x : ℝ in a..b, g x := by
    rw [← intervalIntegral.integral_add hf hg]
    exact intervalIntegral.integral_congr heq
  have hpoleInt (p : ℝ → ℂ) (hp : Continuous p) (a b : ℝ) :
      IntervalIntegrable p volume a b := hp.intervalIntegrable a b
  have hbot :
      (∫ x : ℝ in -B..A,
        W (s₀ + ((x : ℂ) - (Y : ℂ) * I)) *
          (-deriv riemannZeta (1 + (x : ℂ) - (Y : ℂ) * I) /
            riemannZeta (1 + (x : ℂ) - (Y : ℂ) * I))) =
      (∫ x : ℝ in -B..A,
        W (s₀ + ((x : ℂ) - (Y : ℂ) * I)) *
          zetaLogDerivRegular G (1 + (x : ℂ) - (Y : ℂ) * I)) +
      ∫ x : ℝ in -B..A,
        W (s₀ + ((x : ℂ) - (Y : ℂ) * I)) /
          ((x : ℂ) - (Y : ℂ) * I) := by
    apply hside
    · apply ContinuousOn.intervalIntegrable
      intro x hx
      have hpath : ContinuousWithinAt (fun x : ℝ =>
          (x : ℂ) - (Y : ℂ) * I) (Set.uIcc (-B) A) x := by fun_prop
      have hcont := ContinuousAt.comp_continuousWithinAt
        (f := fun x : ℝ => (x : ℂ) - (Y : ℂ) * I) (g := q)
        (hqAt ((x : ℂ) - (Y : ℂ) * I) (hbotMem x hx)).continuousAt hpath
      simpa [q, sub_eq_add_neg, add_assoc] using! hcont
    · apply hpoleInt
      apply Continuous.div (hW.continuous.comp (by fun_prop)) (by fun_prop)
      intro x
      intro hx
      have := congrArg Complex.im hx
      simp [hY.ne'] at this
    · intro x hx
      convert hdecomp ((x : ℂ) - (Y : ℂ) * I) (hbotMem x hx) ?_ using 1 <;> try ring
      · intro h
        have := congrArg Complex.im h
        simp [hY.ne'] at this
  have htop :
      (∫ x : ℝ in -B..A,
        W (s₀ + ((x : ℂ) + (Y : ℂ) * I)) *
          (-deriv riemannZeta (1 + (x : ℂ) + (Y : ℂ) * I) /
            riemannZeta (1 + (x : ℂ) + (Y : ℂ) * I))) =
      (∫ x : ℝ in -B..A,
        W (s₀ + ((x : ℂ) + (Y : ℂ) * I)) *
          zetaLogDerivRegular G (1 + (x : ℂ) + (Y : ℂ) * I)) +
      ∫ x : ℝ in -B..A,
        W (s₀ + ((x : ℂ) + (Y : ℂ) * I)) /
          ((x : ℂ) + (Y : ℂ) * I) := by
    apply hside
    · apply ContinuousOn.intervalIntegrable
      intro x hx
      have hpath : ContinuousWithinAt (fun x : ℝ =>
          (x : ℂ) + (Y : ℂ) * I) (Set.uIcc (-B) A) x := by fun_prop
      have hcont := ContinuousAt.comp_continuousWithinAt
        (f := fun x : ℝ => (x : ℂ) + (Y : ℂ) * I) (g := q)
        (hqAt ((x : ℂ) + (Y : ℂ) * I) (htopMem x hx)).continuousAt hpath
      simpa [q, sub_eq_add_neg, add_assoc] using! hcont
    · apply hpoleInt
      apply Continuous.div (hW.continuous.comp (by fun_prop)) (by fun_prop)
      intro x
      intro hx
      have := congrArg Complex.im hx
      simp [hY.ne'] at this
    · intro x hx
      convert hdecomp ((x : ℂ) + (Y : ℂ) * I) (htopMem x hx) ?_ using 1 <;> try ring
      · intro h
        have := congrArg Complex.im h
        simp [hY.ne'] at this
  have hright :
      (∫ y : ℝ in -Y..Y,
        W (s₀ + ((A : ℂ) + (y : ℂ) * I)) *
          (-deriv riemannZeta (1 + (A : ℂ) + (y : ℂ) * I) /
            riemannZeta (1 + (A : ℂ) + (y : ℂ) * I))) =
      (∫ y : ℝ in -Y..Y,
        W (s₀ + ((A : ℂ) + (y : ℂ) * I)) *
          zetaLogDerivRegular G (1 + (A : ℂ) + (y : ℂ) * I)) +
      ∫ y : ℝ in -Y..Y,
        W (s₀ + ((A : ℂ) + (y : ℂ) * I)) /
          ((A : ℂ) + (y : ℂ) * I) := by
    apply hside
    · apply ContinuousOn.intervalIntegrable
      intro y hy
      have hpath : ContinuousWithinAt (fun y : ℝ =>
          (A : ℂ) + (y : ℂ) * I) (Set.uIcc (-Y) Y) y := by fun_prop
      have hcont := ContinuousAt.comp_continuousWithinAt
        (f := fun y : ℝ => (A : ℂ) + (y : ℂ) * I) (g := q)
        (hqAt ((A : ℂ) + (y : ℂ) * I) (hrightMem y hy)).continuousAt hpath
      simpa [q, sub_eq_add_neg, add_assoc] using! hcont
    · apply hpoleInt
      apply Continuous.div (hW.continuous.comp (by fun_prop)) (by fun_prop)
      intro y
      intro hy
      have := congrArg Complex.re hy
      simp [hA.ne'] at this
    · intro y hy
      convert hdecomp ((A : ℂ) + (y : ℂ) * I) (hrightMem y hy) ?_ using 1 <;> try ring
      · intro h
        have := congrArg Complex.re h
        simp [hA.ne'] at this
  have hleft :
      (∫ y : ℝ in -Y..Y,
        W (s₀ + (-(B : ℂ) + (y : ℂ) * I)) *
          (-deriv riemannZeta (1 - (B : ℂ) + (y : ℂ) * I) /
            riemannZeta (1 - (B : ℂ) + (y : ℂ) * I))) =
      (∫ y : ℝ in -Y..Y,
        W (s₀ + (-(B : ℂ) + (y : ℂ) * I)) *
          zetaLogDerivRegular G (1 - (B : ℂ) + (y : ℂ) * I)) +
      ∫ y : ℝ in -Y..Y,
        W (s₀ + (-(B : ℂ) + (y : ℂ) * I)) /
          (-(B : ℂ) + (y : ℂ) * I) := by
    apply hside
    · apply ContinuousOn.intervalIntegrable
      intro y hy
      have hpath : ContinuousWithinAt (fun y : ℝ =>
          -(B : ℂ) + (y : ℂ) * I) (Set.uIcc (-Y) Y) y := by fun_prop
      have hcont := ContinuousAt.comp_continuousWithinAt
        (f := fun y : ℝ => -(B : ℂ) + (y : ℂ) * I) (g := q)
        (hqAt (-(B : ℂ) + (y : ℂ) * I) (hleftMem y hy)).continuousAt hpath
      simpa [q, sub_eq_add_neg, add_assoc] using! hcont
    · apply hpoleInt
      apply Continuous.div (hW.continuous.comp (by fun_prop)) (by fun_prop)
      intro y
      intro hy
      have := congrArg Complex.re hy
      simp [hB.ne'] at this
    · intro y hy
      convert hdecomp (-(B : ℂ) + (y : ℂ) * I) (hleftMem y hy) ?_ using 1 <;> try ring
      · intro h
        have := congrArg Complex.re h
        simp [hB.ne'] at this
  rw [hbot, htop, hright, hleft]
  calc
    _ = ((∫ x : ℝ in -B..A,
            W (s₀ + ((x : ℂ) - (Y : ℂ) * I)) *
              zetaLogDerivRegular G (1 + (x : ℂ) - (Y : ℂ) * I)) -
          (∫ x : ℝ in -B..A,
            W (s₀ + ((x : ℂ) + (Y : ℂ) * I)) *
              zetaLogDerivRegular G (1 + (x : ℂ) + (Y : ℂ) * I)) +
          I * (∫ y : ℝ in -Y..Y,
            W (s₀ + ((A : ℂ) + (y : ℂ) * I)) *
              zetaLogDerivRegular G (1 + (A : ℂ) + (y : ℂ) * I)) -
          I * (∫ y : ℝ in -Y..Y,
            W (s₀ + (-(B : ℂ) + (y : ℂ) * I)) *
              zetaLogDerivRegular G (1 - (B : ℂ) + (y : ℂ) * I))) +
        ((∫ x : ℝ in -B..A,
            W (s₀ + ((x : ℂ) - (Y : ℂ) * I)) /
              ((x : ℂ) - (Y : ℂ) * I)) -
          (∫ x : ℝ in -B..A,
            W (s₀ + ((x : ℂ) + (Y : ℂ) * I)) /
              ((x : ℂ) + (Y : ℂ) * I)) +
          I * (∫ y : ℝ in -Y..Y,
            W (s₀ + ((A : ℂ) + (y : ℂ) * I)) /
              ((A : ℂ) + (y : ℂ) * I)) -
          I * (∫ y : ℝ in -Y..Y,
            W (s₀ + (-(B : ℂ) + (y : ℂ) * I)) /
              (-(B : ℂ) + (y : ℂ) * I))) := by ring
    _ = 0 + 2 * Real.pi * I * W s₀ := by rw [hregRect', hpole]
    _ = 2 * Real.pi * I * W s₀ := by ring

/-- A translated interval contains at most the full mass of the Cauchy
kernel.  The coarse constant `4` keeps the later campaign constants simple. -/
theorem integral_inv_one_add_sq_sub_le_four (a b u : ℝ) (hab : a ≤ b) :
    (∫ y : ℝ in a..b, (1 + (y - u) ^ 2)⁻¹) ≤ 4 := by
  have hshift : (∫ y : ℝ in a..b, (1 + (y - u) ^ 2)⁻¹) =
      ∫ y : ℝ in a - u..b - u, (1 + y ^ 2)⁻¹ := by
    simpa only using intervalIntegral.integral_comp_sub_right
      (fun y : ℝ => (1 + y ^ 2)⁻¹) u (a := a) (b := b)
  rw [hshift, integral_inv_one_add_sq]
  have htop := Real.arctan_lt_pi_div_two (b - u)
  have hbot := Real.neg_pi_div_two_lt_arctan (a - u)
  have hpi := Real.pi_le_four
  linarith

/-- **V-A-5, shifted side.**  The regular part on the left side costs a
constant times `M P^(1-η/2)`, with no loss in `η`. -/
theorem primeMellin_shifted_side_bound
    (S : ℝ → ℝ) (C P η Y u M : ℝ)
    (hSs : ContDiff ℝ ∞ S)
    (hS01 : ∀ v, 0 ≤ S v ∧ S v ≤ 1)
    (hS0 : ∀ v, v ≤ 0 → S v = 0)
    (hS1 : ∀ v, 1 ≤ v → S v = 1)
    (hC0 : 0 ≤ C) (hC1 : ∀ v, |deriv S v| ≤ C)
    (hC2 : ∀ v, |deriv (deriv S) v| ≤ C)
    (hP : 2 ≤ P) (hη : 0 < η) (hη1 : η ≤ 1 / 2)
    (hY : 0 < Y) (hM : 0 ≤ M)
    (hreg : ∀ z : ℂ, 1 - η ≤ z.re → z.re ≤ 2 → |z.im| ≤ Y → z ≠ 1 →
      ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤ M) :
    ‖∫ y : ℝ in -Y..Y,
        primeMellinTransform S P
            (((1 - η / 2 : ℝ) : ℂ) + ((y - u : ℝ) : ℂ) * I) *
          (-deriv riemannZeta
                (((1 - η / 2 : ℝ) : ℂ) + (y : ℂ) * I) /
              riemannZeta (((1 - η / 2 : ℝ) : ℂ) + (y : ℂ) * I) -
            1 / ((((1 - η / 2 : ℝ) : ℂ) + (y : ℂ) * I) - 1))‖ ≤
      1000000 * (C + 1) ^ 2 * M * P ^ (1 - η / 2) := by
  let D : ℝ := 250000 * (C + 1) ^ 2 * M * P ^ (1 - η / 2)
  have hα0 : 1 / 2 ≤ 1 - η / 2 := by linarith
  have hα2 : 1 - η / 2 ≤ 2 := by linarith
  have hD0 : 0 ≤ D := by
    dsimp [D]
    positivity
  have hmajor : IntervalIntegrable (fun y : ℝ =>
      D * (1 + (y - u) ^ 2)⁻¹) volume (-Y) Y := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul
      ((continuous_const.add ((continuous_id.sub continuous_const).pow 2)).inv₀ fun y => by
        change 1 + (y - u) ^ 2 ≠ 0
        nlinarith [sq_nonneg (y - u)])
  have hpoint : ∀ y ∈ Set.Ioc (-Y) Y,
      ‖primeMellinTransform S P
            (((1 - η / 2 : ℝ) : ℂ) + ((y - u : ℝ) : ℂ) * I) *
          (-deriv riemannZeta
                (((1 - η / 2 : ℝ) : ℂ) + (y : ℂ) * I) /
              riemannZeta (((1 - η / 2 : ℝ) : ℂ) + (y : ℂ) * I) -
            1 / ((((1 - η / 2 : ℝ) : ℂ) + (y : ℂ) * I) - 1))‖ ≤
        D * (1 + (y - u) ^ 2)⁻¹ := by
    intro y hy
    have hycc : y ∈ Set.Icc (-Y) Y := ⟨hy.1.le, hy.2⟩
    have hw := primeMellinTransform_vertical_decay S C P (1 - η / 2) (y - u)
      hSs hS01 hS0 hS1 hC0 hC1 hC2 hP hα0 hα2
    have hz :
        ‖-deriv riemannZeta
              (((1 - η / 2 : ℝ) : ℂ) + (y : ℂ) * I) /
            riemannZeta (((1 - η / 2 : ℝ) : ℂ) + (y : ℂ) * I) -
          1 / ((((1 - η / 2 : ℝ) : ℂ) + (y : ℂ) * I) - 1)‖ ≤ M := by
      apply hreg
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, mul_zero, sub_zero]
        linarith
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, mul_zero, sub_zero]
        linarith
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, zero_mul, mul_one, zero_add]
        rw [abs_le]
        simpa using hycc
      · intro heq
        have hre := congrArg Complex.re heq
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, mul_zero, sub_zero, Complex.one_re] at hre
        linarith
    simp only [norm_mul]
    calc
      _ ≤ (250000 * (C + 1) ^ 2 * P ^ (1 - η / 2) /
            (1 + (y - u) ^ 2)) * M :=
        mul_le_mul hw hz (norm_nonneg _) (by positivity)
      _ = D * (1 + (y - u) ^ 2)⁻¹ := by
        dsimp [D]
        rw [div_eq_mul_inv]
        ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le
    (by linarith : -Y ≤ Y) (ae_of_all _ fun y => fun hy => hpoint y hy) hmajor
  calc
    _ ≤ ∫ y : ℝ in -Y..Y, D * (1 + (y - u) ^ 2)⁻¹ := hint
    _ = D * (∫ y : ℝ in -Y..Y, (1 + (y - u) ^ 2)⁻¹) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ D * 4 := mul_le_mul_of_nonneg_left
      (integral_inv_one_add_sq_sub_le_four (-Y) Y u (by linarith)) hD0
    _ = 1000000 * (C + 1) ^ 2 * M * P ^ (1 - η / 2) := by
      dsimp [D]
      ring

/-- **V-A-5, horizontal side.**  Here `t` is the height seen by zeta and
`τ` is the (possibly translated) height seen by the Mellin transform. -/
theorem primeMellin_horizontal_side_bound
    (S : ℝ → ℝ) (C P η c Y M t τ : ℝ)
    (hSs : ContDiff ℝ ∞ S)
    (hS01 : ∀ v, 0 ≤ S v ∧ S v ≤ 1)
    (hS0 : ∀ v, v ≤ 0 → S v = 0)
    (hS1 : ∀ v, 1 ≤ v → S v = 1)
    (hC0 : 0 ≤ C) (hC1 : ∀ v, |deriv S v| ≤ C)
    (hC2 : ∀ v, |deriv (deriv S) v| ≤ C)
    (hP : 2 ≤ P) (hη : 0 < η) (hη1 : η ≤ 1 / 2)
    (hc1 : 1 < c) (hc2 : c ≤ 2) (hY : 0 < Y) (hM : 0 ≤ M)
    (htY : |t| ≤ Y) (ht0 : t ≠ 0)
    (hreg : ∀ z : ℂ, 1 - η ≤ z.re → z.re ≤ 2 → |z.im| ≤ Y → z ≠ 1 →
      ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤ M) :
    ‖∫ x : ℝ in -(η / 2)..(c - 1),
        primeMellinTransform S P
            ((((1 + x : ℝ) : ℂ) + (τ : ℂ) * I)) *
          (-deriv riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * I) /
              riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * I) -
            1 / ((((1 + x : ℝ) : ℂ) + (t : ℂ) * I) - 1))‖ ≤
      (250000 * (C + 1) ^ 2 * M * P ^ c / (1 + τ ^ 2)) *
        (c - 1 + η / 2) := by
  have hBA : -(η / 2) ≤ c - 1 := by linarith
  let Q : ℝ := 250000 * (C + 1) ^ 2 * M * P ^ c / (1 + τ ^ 2)
  have hpoint : ∀ x ∈ Set.uIoc (-(η / 2)) (c - 1),
      ‖primeMellinTransform S P ((((1 + x : ℝ) : ℂ) + (τ : ℂ) * I)) *
          (-deriv riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * I) /
              riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * I) -
            1 / ((((1 + x : ℝ) : ℂ) + (t : ℂ) * I) - 1))‖ ≤ Q := by
    intro x hx
    rw [Set.uIoc_of_le hBA] at hx
    rcases hx with ⟨hxlo, hxhi⟩
    have hα0 : 1 / 2 ≤ 1 + x := by linarith
    have hα2 : 1 + x ≤ 2 := by linarith
    have hw := primeMellinTransform_vertical_decay S C P (1 + x) τ
      hSs hS01 hS0 hS1 hC0 hC1 hC2 hP hα0 hα2
    have hz :
        ‖-deriv riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * I) /
              riemannZeta (((1 + x : ℝ) : ℂ) + (t : ℂ) * I) -
            1 / ((((1 + x : ℝ) : ℂ) + (t : ℂ) * I) - 1)‖ ≤ M := by
      apply hreg
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
        linarith
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
        linarith
      · simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, zero_mul, mul_one, zero_add,
          add_zero] using htY
      · intro heq
        have him := congrArg Complex.im heq
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, zero_mul, mul_one, zero_add,
          Complex.one_im] at him
        exact ht0 (by simpa only [add_zero] using him)
    have hp : P ^ (1 + x) ≤ P ^ c :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    simp only [norm_mul]
    calc
      _ ≤ (250000 * (C + 1) ^ 2 * P ^ (1 + x) / (1 + τ ^ 2)) * M :=
        mul_le_mul hw hz (norm_nonneg _) (by positivity)
      _ ≤ (250000 * (C + 1) ^ 2 * P ^ c / (1 + τ ^ 2)) * M := by
        gcongr
      _ = Q := by dsimp [Q]; ring
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  calc
    _ ≤ Q * |(c - 1) - -(η / 2)| := hnorm
    _ = Q * (c - 1 + η / 2) := by
      rw [abs_of_nonneg (by linarith : 0 ≤ (c - 1) - -(η / 2))]
      ring
    _ = (250000 * (C + 1) ^ 2 * M * P ^ c / (1 + τ ^ 2)) *
        (c - 1 + η / 2) := by rfl

theorem inv_one_add_sq_le_four_div_sq (Y τ : ℝ)
    (hY : 0 < Y) (hτ : Y / 2 ≤ |τ|) :
    (1 + τ ^ 2)⁻¹ ≤ 4 / Y ^ 2 := by
  have hsq : (Y / 2) ^ 2 ≤ τ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hτ)
      (add_nonneg (abs_nonneg τ) (by positivity)), sq_abs τ]
  have hτsq : 0 < τ ^ 2 := by
    have : 0 < |τ| := lt_of_lt_of_le (by positivity : 0 < Y / 2) hτ
    nlinarith [sq_abs τ]
  calc
    (1 + τ ^ 2)⁻¹ ≤ (τ ^ 2)⁻¹ := by
      exact inv_anti₀ hτsq (by linarith)
    _ ≤ ((Y / 2) ^ 2)⁻¹ := by
      exact inv_anti₀ (by positivity) hsq
    _ = 4 / Y ^ 2 := by
      field_simp
      ring

/-- **V-A-5, both horizontal sides.**  If `|u| ≤ Y/2`, their total
regular-part contribution has quadratic height decay. -/
theorem primeMellin_horizontal_sides_bound
    (S : ℝ → ℝ) (C P η c Y u M : ℝ)
    (hSs : ContDiff ℝ ∞ S)
    (hS01 : ∀ v, 0 ≤ S v ∧ S v ≤ 1)
    (hS0 : ∀ v, v ≤ 0 → S v = 0)
    (hS1 : ∀ v, 1 ≤ v → S v = 1)
    (hC0 : 0 ≤ C) (hC1 : ∀ v, |deriv S v| ≤ C)
    (hC2 : ∀ v, |deriv (deriv S) v| ≤ C)
    (hP : 2 ≤ P) (hη : 0 < η) (hη1 : η ≤ 1 / 2)
    (hc1 : 1 < c) (hc2 : c ≤ 2) (hY : 0 < Y) (hM : 0 ≤ M)
    (hu : |u| ≤ Y / 2)
    (hreg : ∀ z : ℂ, 1 - η ≤ z.re → z.re ≤ 2 → |z.im| ≤ Y → z ≠ 1 →
      ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤ M) :
    ‖∫ x : ℝ in -(η / 2)..(c - 1),
        primeMellinTransform S P
            ((((1 + x : ℝ) : ℂ) + ((-Y - u : ℝ) : ℂ) * I)) *
          (-deriv riemannZeta (((1 + x : ℝ) : ℂ) - (Y : ℂ) * I) /
              riemannZeta (((1 + x : ℝ) : ℂ) - (Y : ℂ) * I) -
            1 / ((((1 + x : ℝ) : ℂ) - (Y : ℂ) * I) - 1))‖ +
      ‖∫ x : ℝ in -(η / 2)..(c - 1),
        primeMellinTransform S P
            ((((1 + x : ℝ) : ℂ) + ((Y - u : ℝ) : ℂ) * I)) *
          (-deriv riemannZeta (((1 + x : ℝ) : ℂ) + (Y : ℂ) * I) /
              riemannZeta (((1 + x : ℝ) : ℂ) + (Y : ℂ) * I) -
            1 / ((((1 + x : ℝ) : ℂ) + (Y : ℂ) * I) - 1))‖ ≤
      4000000 * (C + 1) ^ 2 * M * P ^ c / Y ^ 2 := by
  have hτbot : Y / 2 ≤ |-Y - u| := by
    have htri := abs_add_le (-Y - u) u
    rw [show -Y - u + u = -Y by ring, abs_neg, abs_of_pos hY] at htri
    linarith
  have hτtop : Y / 2 ≤ |Y - u| := by
    have htri := abs_add_le (Y - u) u
    rw [show Y - u + u = Y by ring, abs_of_pos hY] at htri
    linarith
  have hb := primeMellin_horizontal_side_bound S C P η c Y M (-Y) (-Y - u)
    hSs hS01 hS0 hS1 hC0 hC1 hC2 hP hη hη1 hc1 hc2 hY hM
    (by simp [abs_of_pos hY]) (by linarith) hreg
  have ht := primeMellin_horizontal_side_bound S C P η c Y M Y (Y - u)
    hSs hS01 hS0 hS1 hC0 hC1 hC2 hP hη hη1 hc1 hc2 hY hM
    (by simp [abs_of_pos hY]) hY.ne' hreg
  have hbotInv := inv_one_add_sq_le_four_div_sq Y (-Y - u) hY hτbot
  have htopInv := inv_one_add_sq_le_four_div_sq Y (Y - u) hY hτtop
  have hlen : c - 1 + η / 2 ≤ 2 := by linarith
  have hlen0 : 0 ≤ c - 1 + η / 2 := by linarith
  have hbase : 0 ≤ 250000 * (C + 1) ^ 2 * M * P ^ c := by positivity
  have hYsq : 0 < Y ^ 2 := sq_pos_of_pos hY
  have hb' :
      ‖∫ x : ℝ in -(η / 2)..(c - 1),
          primeMellinTransform S P
              ((((1 + x : ℝ) : ℂ) + ((-Y - u : ℝ) : ℂ) * I)) *
            (-deriv riemannZeta (((1 + x : ℝ) : ℂ) - (Y : ℂ) * I) /
                riemannZeta (((1 + x : ℝ) : ℂ) - (Y : ℂ) * I) -
              1 / ((((1 + x : ℝ) : ℂ) - (Y : ℂ) * I) - 1))‖ ≤
        2000000 * (C + 1) ^ 2 * M * P ^ c / Y ^ 2 := by
    have hb0 :
        ‖∫ x : ℝ in -(η / 2)..(c - 1),
            primeMellinTransform S P
                ((((1 + x : ℝ) : ℂ) + ((-Y - u : ℝ) : ℂ) * I)) *
              (-deriv riemannZeta (((1 + x : ℝ) : ℂ) - (Y : ℂ) * I) /
                  riemannZeta (((1 + x : ℝ) : ℂ) - (Y : ℂ) * I) -
                1 / ((((1 + x : ℝ) : ℂ) - (Y : ℂ) * I) - 1))‖ ≤
          (250000 * (C + 1) ^ 2 * M * P ^ c / (1 + (-Y - u) ^ 2)) *
            (c - 1 + η / 2) := by
      simpa [sub_eq_add_neg] using hb
    refine hb0.trans ?_
    calc
      (250000 * (C + 1) ^ 2 * M * P ^ c / (1 + (-Y - u) ^ 2)) *
          (c - 1 + η / 2) =
          (250000 * (C + 1) ^ 2 * M * P ^ c) *
            (1 + (-Y - u) ^ 2)⁻¹ * (c - 1 + η / 2) := by rw [div_eq_mul_inv]
      _ ≤ (250000 * (C + 1) ^ 2 * M * P ^ c) *
            (4 / Y ^ 2) * 2 := by gcongr
      _ = 2000000 * (C + 1) ^ 2 * M * P ^ c / Y ^ 2 := by ring
  have ht' :
      ‖∫ x : ℝ in -(η / 2)..(c - 1),
          primeMellinTransform S P
              ((((1 + x : ℝ) : ℂ) + ((Y - u : ℝ) : ℂ) * I)) *
            (-deriv riemannZeta (((1 + x : ℝ) : ℂ) + (Y : ℂ) * I) /
                riemannZeta (((1 + x : ℝ) : ℂ) + (Y : ℂ) * I) -
              1 / ((((1 + x : ℝ) : ℂ) + (Y : ℂ) * I) - 1))‖ ≤
        2000000 * (C + 1) ^ 2 * M * P ^ c / Y ^ 2 := by
    refine ht.trans ?_
    calc
      (250000 * (C + 1) ^ 2 * M * P ^ c / (1 + (Y - u) ^ 2)) *
          (c - 1 + η / 2) =
          (250000 * (C + 1) ^ 2 * M * P ^ c) *
            (1 + (Y - u) ^ 2)⁻¹ * (c - 1 + η / 2) := by rw [div_eq_mul_inv]
      _ ≤ (250000 * (C + 1) ^ 2 * M * P ^ c) *
            (4 / Y ^ 2) * 2 := by gcongr
      _ = 2000000 * (C + 1) ^ 2 * M * P ^ c / Y ^ 2 := by ring
  have hsum := add_le_add hb' ht'
  calc
    _ ≤ (2000000 * (C + 1) ^ 2 * M * P ^ c / Y ^ 2) +
        (2000000 * (C + 1) ^ 2 * M * P ^ c / Y ^ 2) := hsum
    _ = 4000000 * (C + 1) ^ 2 * M * P ^ c / Y ^ 2 := by ring

/-- Weighted prime powers are dominated by the classical `ψ-θ` bound. -/
theorem weighted_nonprime_vonMangoldt_sum_le
    (x : ℝ) (hx : 1 ≤ x) (w : ℕ → ℝ) (χ : ℕ → ℂ)
    (hw : ∀ n, 0 ≤ w n ∧ w n ≤ 1) (hχ : ∀ n, ‖χ n‖ ≤ 1) :
    ‖∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬n.Prime),
        (w n : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ n‖ ≤
      2 * Real.sqrt x * Real.log x := by
  calc
    _ ≤ ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬n.Prime),
        ‖(w n : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬n.Prime),
        ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_le_sum
      intro n hn
      have hwn := hw n
      have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n :=
        ArithmeticFunction.vonMangoldt_nonneg
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hwn.1, abs_of_nonneg hΛ]
      calc
        w n * ArithmeticFunction.vonMangoldt n * ‖χ n‖ ≤
            1 * ArithmeticFunction.vonMangoldt n * 1 := by
          gcongr
          · exact hwn.2
          · exact hχ n
        _ = ArithmeticFunction.vonMangoldt n := by ring
    _ = Chebyshev.psi x - Chebyshev.theta x := by
      exact (Chebyshev.psi_sub_theta_eq_sum_not_prime x).symm
    _ ≤ |Chebyshev.psi x - Chebyshev.theta x| := le_abs_self _
    _ ≤ 2 * Real.sqrt x * Real.log x :=
      Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx

/-- **V-A-6.**  Removing prime powers from the plateau-supported von
Mangoldt sum costs at most `6 √P log(4P)`. -/
theorem primeMellin_prime_powers_bound
    (S : ℝ → ℝ) (P u : ℝ)
    (hS01 : ∀ v, 0 ≤ S v ∧ S v ≤ 1) (hP : 2 ≤ P) :
    ‖∑ n ∈ (Finset.Ioc 0 ⌊4 * P⌋₊).filter (fun n => ¬n.Prime),
        (primeMellinWindow S P n : ℂ) *
          (ArithmeticFunction.vonMangoldt n : ℂ) *
          (n : ℂ) ^ (-(u : ℂ) * I)‖ ≤
      6 * Real.sqrt P * Real.log (4 * P) := by
  let χ : ℕ → ℂ := fun n => if n = 0 then 0 else (n : ℂ) ^ (-(u : ℂ) * I)
  have hw : ∀ n : ℕ, 0 ≤ primeMellinWindow S P n ∧
      primeMellinWindow S P n ≤ 1 := by
    intro n
    unfold primeMellinWindow primeMellinProfile
    have hL := hS01 (2 * (Real.log (↑n / P) / Real.log 2) + 1)
    have hR := hS01 (3 - 2 * (Real.log (↑n / P) / Real.log 2))
    constructor
    · exact mul_nonneg hL.1 hR.1
    · nlinarith [mul_nonneg hL.1 hR.1,
        mul_nonneg (sub_nonneg.mpr hL.2) hR.1]
  have hχ : ∀ n, ‖χ n‖ ≤ 1 := by
    intro n
    by_cases hn : n = 0
    · simp [χ, hn]
    · simp only [χ, if_neg hn]
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos hn0]
      simp
  have hmain := weighted_nonprime_vonMangoldt_sum_le (4 * P)
    (by linarith) (fun n => primeMellinWindow S P n) χ hw hχ
  have heq :
      (∑ n ∈ (Finset.Ioc 0 ⌊4 * P⌋₊).filter (fun n => ¬n.Prime),
          (primeMellinWindow S P n : ℂ) *
            (ArithmeticFunction.vonMangoldt n : ℂ) *
            (n : ℂ) ^ (-(u : ℂ) * I)) =
        ∑ n ∈ (Finset.Ioc 0 ⌊4 * P⌋₊).filter (fun n => ¬n.Prime),
          (primeMellinWindow S P n : ℂ) *
            (ArithmeticFunction.vonMangoldt n : ℂ) * χ n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos : 0 < n := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
    simp only [χ, if_neg (Nat.ne_of_gt hnpos)]
  rw [heq]
  refine hmain.trans ?_
  have hsqrt : Real.sqrt (4 * P) = 2 * Real.sqrt P := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hsqrt]
  have hlog : 0 ≤ Real.log (4 * P) := Real.log_nonneg (by linarith)
  have hsqrt0 : 0 ≤ Real.sqrt P := Real.sqrt_nonneg P
  nlinarith

end ExpSums

end MoltResearch
