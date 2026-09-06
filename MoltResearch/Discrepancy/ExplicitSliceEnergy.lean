import MoltResearch.Discrepancy.ExplicitSliceWindow

/-!
# Slice energy through an explicit window

This is the window-energy scaffold with the explicit polynomially controlled
window substituted for the abstract bump family.  It leaves the Fourier-line
energy as one hypothesis, so later leaves can reuse the established low/mid/
outer/tail decomposition unchanged.
-/

namespace MoltResearch

namespace ExpSums

open MeasureTheory Real Finset
open scoped ContDiff

set_option maxHeartbeats 800000 in
/-- Per-slice energy from a Fourier-line bound, with the derivative constant
shown explicitly as `explicitSliceWindowDerivBound epsGeom`. -/
theorem slice_energy_le_of_explicit_window_energy
    (h : ℕ → ℂ) (hb : ∀ m, ‖h m‖ ≤ 1)
    (A s U H : ℕ) (hA : 1 ≤ A) (hs : 1 ≤ s) (hsA : s ≤ A)
    (hU : 0 < U) (hUH : 2 * U ≤ H) (h3H : 3 * H ≤ A)
    (hplat : ((U : ℝ) + 1) * ((A : ℝ) + s) ≤ (A : ℝ) * H)
    (hs30 : 30 * s ≤ A)
    (epsGeom : ℝ) (heps : 0 < epsGeom) (heps1 : epsGeom ≤ 1)
    (hU100 : epsGeom * (H : ℝ) ≤ 100 * U)
    (hU50 : 50 * (U : ℝ) ≤ epsGeom * H)
    (R : ℝ)
    (hreg : ∀ eta : ℝ → ℝ,
      ContDiff ℝ ∞ eta → (∀ u, 0 ≤ eta u ∧ eta u ≤ 1) →
      (∀ u, eta u ≠ 0 → |u| ≤ 2) →
      (∀ u, |deriv eta u| ≤ explicitSliceWindowDerivBound epsGeom) →
      ∫ y, ‖(4 * (H : ℂ)) * smoothedLogSum ((A : ℝ) / H) eta
          (fun m => if m ∈ Finset.Ioc A (A + s + 2 * H + 4 * U)
            then h m * (m : ℂ) / (4 * (A : ℂ)) else 0)
          (Finset.Ioc A (A + s + 2 * H + 4 * U)) y‖ ^ 2 ≤ R) :
    ∑ n ∈ Finset.Ioc A (A + s),
        ‖∑ m ∈ Finset.Ioc n (n + H), h m‖ ^ 2 / n
      ≤ 6 * R +
        (3 * (U : ℝ) ^ 2 +
          3 * (6 * (U : ℝ) + (H : ℝ) * s / A + 2) ^ 2) *
            (∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) / n) +
        6 * (800 * (H : ℝ) * (A : ℝ) *
          explicitSliceWindowDerivBound epsGeom) / A := by
  classical
  have hH : 0 < H := by omega
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hT : (0 : ℝ) < (A : ℝ) / H := by positivity
  have hT1 : (1 : ℝ) ≤ (A : ℝ) / H := by
    rw [le_div_iff₀ hH0]
    have h3 : (3 : ℝ) * H ≤ A := by exact_mod_cast h3H
    linarith
  obtain ⟨eta, hetaSmooth, heta01, heta2, hetaDeriv, hcollar⟩ :=
    exists_explicit_slice_window epsGeom heps heps1 h hb A s U H hA hs hsA
      hU hUH hplat hs30 h3H hU100 hU50
  obtain ⟨B2, hB20, hB2, hd2⟩ :=
    exists_deriv_bound eta hetaSmooth heta2
  have heta1 : ∀ u, |eta u| ≤ 1 := by
    intro u
    rw [abs_le]
    exact ⟨by linarith [(heta01 u).1], (heta01 u).2⟩
  have hSpos : ∀ m ∈ Finset.Ioc A (A + s + 2 * H + 4 * U), 0 < m := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    omega
  have hSA : ∀ m ∈ Finset.Ioc A (A + s + 2 * H + 4 * U), A ≤ m := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    omega
  have ha1 : ∀ m, ‖(fun m =>
      if m ∈ Finset.Ioc A (A + s + 2 * H + 4 * U)
      then h m * (m : ℂ) / (4 * (A : ℂ)) else 0) m‖ ≤ 1 := by
    intro m
    refine norm_truncated_weight_le h hb A (by omega) _ ?_ m
    intro k hk
    rw [Finset.mem_Ioc] at hk
    omega
  set G : ℝ → ℂ := fun y =>
    (4 * (H : ℂ)) * smoothedLogSum ((A : ℝ) / H) eta
      (fun m => if m ∈ Finset.Ioc A (A + s + 2 * H + 4 * U)
        then h m * (m : ℂ) / (4 * (A : ℂ)) else 0)
      (Finset.Ioc A (A + s + 2 * H + 4 * U)) y with hG
  have hGcont : Continuous G := by
    rw [hG]
    exact continuous_const.mul
      ((smoothedLogSum_contDiff ((A : ℝ) / H) eta hetaSmooth _ _).continuous)
  have hcollar' : ∀ n ∈ Finset.Ioc A (A + s),
      ‖((1 / (U : ℂ)) * ∑ u ∈ Finset.range U,
          ∑ m ∈ Finset.Ioc (n + u) (n + u + H), h m) - G (Real.log n)‖
        ≤ 6 * (U : ℝ) + (H : ℝ) * s / A + 2 := by
    intro n hn
    have hcn := hcollar n hn
    have hid := window_sum_eq_smoothedLogSum h A H (by omega) hH eta
      (Finset.Ioc A (A + s + 2 * H + 4 * U)) hSpos (Real.log n)
    rw [hG]
    dsimp only
    rw [← hid]
    exact hcn
  have hLip : ∀ y z : ℝ, |‖G y‖ ^ 2 - ‖G z‖ ^ 2| ≤
      (800 * (H : ℝ) * (A : ℝ) * explicitSliceWindowDerivBound epsGeom) *
        |y - z| := by
    intro y z
    have hbase := abs_norm_sq_smoothedLogSum_sub_le ((A : ℝ) / H) hT1 eta
      hetaSmooth heta2 1 heta1 hd2 (explicitSliceWindowDerivBound epsGeom)
      hetaDeriv _ ha1 (Finset.Ioc A (A + s + 2 * H + 4 * U)) A hSA hA
      (by
        rw [div_le_iff₀ hH0]
        have h1H : (1 : ℝ) ≤ H := by exact_mod_cast hH
        nlinarith) y z
    have hGsq : ∀ w : ℝ, ‖G w‖ ^ 2 =
        16 * (H : ℝ) ^ 2 *
          ‖smoothedLogSum ((A : ℝ) / H) eta
            (fun m => if m ∈ Finset.Ioc A (A + s + 2 * H + 4 * U)
              then h m * (m : ℂ) / (4 * (A : ℂ)) else 0)
            (Finset.Ioc A (A + s + 2 * H + 4 * U)) w‖ ^ 2 := by
      intro w
      rw [hG]
      dsimp only
      rw [norm_mul]
      have h4H : ‖(4 * (H : ℂ) : ℂ)‖ = 4 * (H : ℝ) := by
        rw [norm_mul, Complex.norm_natCast]
        norm_num
      rw [h4H, mul_pow]
      ring
    rw [hGsq y, hGsq z, ← mul_sub, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 16 * (H : ℝ) ^ 2)]
    calc
      16 * (H : ℝ) ^ 2 *
          |‖smoothedLogSum ((A : ℝ) / H) eta
              (fun m => if m ∈ Finset.Ioc A (A + s + 2 * H + 4 * U)
                then h m * (m : ℂ) / (4 * (A : ℂ)) else 0)
              (Finset.Ioc A (A + s + 2 * H + 4 * U)) y‖ ^ 2 -
            ‖smoothedLogSum ((A : ℝ) / H) eta
              (fun m => if m ∈ Finset.Ioc A (A + s + 2 * H + 4 * U)
                then h m * (m : ℂ) / (4 * (A : ℂ)) else 0)
              (Finset.Ioc A (A + s + 2 * H + 4 * U)) z‖ ^ 2|
          ≤ 16 * (H : ℝ) ^ 2 *
              ((50 * 1 * explicitSliceWindowDerivBound epsGeom *
                ((A : ℝ) / H)) * |y - z|) :=
            mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = (800 * (H : ℝ) * (A : ℝ) *
            explicitSliceWindowDerivBound epsGeom) * |y - z| := by
          field_simp
          ring
  have hBnonneg : 0 ≤ explicitSliceWindowDerivBound epsGeom := by
    unfold explicitSliceWindowDerivBound
    positivity [one_le_explicitSliceWindowConstant]
  have hmean := slice_window_mean_sq_le h hb A s H U hA hU (by omega)
    G hGcont (6 * (U : ℝ) + (H : ℝ) * s / A + 2) (by positivity)
    hcollar' (800 * (H : ℝ) * (A : ℝ) *
      explicitSliceWindowDerivBound epsGeom) (by positivity) hLip
  have hGcs : HasCompactSupport G := by
    rw [hG]
    have hetacs : HasCompactSupport eta := by
      refine HasCompactSupport.intro
        (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) ?_
      intro u hu
      by_contra hne
      have h2 := heta2 u hne
      rw [Set.mem_Icc, not_and_or] at hu
      rw [abs_le] at h2
      rcases hu with hu | hu
      · push_neg at hu
        linarith [h2.1]
      · push_neg at hu
        linarith [h2.2]
    have hsupp := smoothedLogSum_hasCompactSupport ((A : ℝ) / H) hT eta
      hetacs (fun m => if m ∈ Finset.Ioc A (A + s + 2 * H + 4 * U)
        then h m * (m : ℂ) / (4 * (A : ℂ)) else 0)
      (Finset.Ioc A (A + s + 2 * H + 4 * U))
    exact hsupp.mul_left
  have hG1 := intervalIntegral_norm_sq_le_integral G hGcont hGcs
    (Real.log A) (Real.log (((A + s : ℕ) : ℝ) + 1))
  have hint : ∫ y, ‖G y‖ ^ 2 ≤ R := by
    rw [hG]
    exact hreg eta hetaSmooth heta01 heta2 hetaDeriv
  have hstep : ∫ y in (Real.log A)..(Real.log (((A + s : ℕ) : ℝ) + 1)),
      ‖G y‖ ^ 2 ≤ R := hG1.trans hint
  have h6 := mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 6)
  linarith [hmean, h6]

end ExpSums

end MoltResearch
