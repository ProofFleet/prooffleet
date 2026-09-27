import MoltResearch.Discrepancy.PlancherelHarness
import MoltResearch.Discrepancy.ParsevalBridge

/-!
# The regime split with the low band left as an energy (Track R, A2-III)

`integral_norm_sq_sum_translates_regime_split` (the harness's three-regime
split) prices the frequency line in three pieces: an explicit low-band energy
`∫_{|ξ|<K} ‖P‖²‖𝓕F‖²`, a middle piece `Mmid²·∫‖𝓕F‖²` controlled by the
**pointwise sup** of the phase polynomial on `K ≤ |ξ| ≤ L`, and a tail
controlled by `Mtot²/L²`.

**That middle piece is the trivial bound on the band energy it stands for**,
and it is exactly the quantity the `[mrt]` A.2 band campaign exists to improve:
`Mmid²·∫‖𝓕F‖²` is sup² × window mass, whereas the campaign's capstone
(`band_energy_le_budget`) delivers the honest `∫_band ‖P‖²·w ≤ 𝔅`.  A sup slot
cannot consume an energy bound, so the campaign's output does not compose with
its own consumer.

This module supplies the missing shape.  Rather than a four-way split it uses
**two regimes**: everything below `L` is left as an integral, and only the tail
is collapsed.  The consumer then splits `{|ξ| ≤ L}` into whatever bands it
wants — the low band `|ξ| < K` and the mid band `K ≤ |ξ| ≤ L`, say — with
`setIntegral_le_sum_of_cover`, which already exists and takes an arbitrary
finite cover.  That is simpler than fixing the two-band structure here and
strictly more useful, since the band structure is the schedule's business and
varies with `J`.

The weight in the surviving integral is `‖𝓕 F‖²`, which is the capstone's
abstract `w`; when `F` is the slice window its sup is `(4H/A)²`
(`norm_fourier_slice_window_le`), which is the capstone's `Cw`.  The two sides
were designed to meet — only the slot was the wrong shape.

Kept in its own module because `PlancherelHarness` has twenty modules
downstream, `DyadicMVT` among them, which makes editing it the most expensive
change in the tree.
-/

namespace MoltResearch

namespace ExpSums

open Real MeasureTheory SchwartzMap
open scoped FourierTransform ContDiff

/-- **The two-regime split, low band left as an energy** (Track R, A2-III).

The translate-sum energy is at most the phase polynomial's band energy below
`L`, plus the derivative-energy tail.  No sup appears below `L`: that is the
whole point, and it is what lets the A.2 band capstone discharge the middle.

Compare `integral_norm_sq_sum_translates_regime_split`, which additionally
collapses `K ≤ |ξ| ≤ L` to `Mmid²·∫‖𝓕F‖²`.  Everything that lemma proves about
the tail is proved here in the same way; only the treatment below `L` differs,
and this one keeps the information the band estimates supply.

`Mtot` is still needed — the tail genuinely has no band estimate behind it, and
`ξ²/L² ≥ 1` there is what converts the derivative energy into a bound. -/
theorem integral_norm_sq_sum_translates_energy_split
    (F : ℝ → ℂ) (hFc : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    {ι : Type*} (S : Finset ι) (w : ι → ℂ) (s : ι → ℝ)
    (L Mtot : ℝ) (hL : 0 < L)
    (htot : ∀ ξ : ℝ,
      ‖∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖ ≤ Mtot) :
    ∫ y, ‖∑ i ∈ S, w i * F (y - s i)‖^2
      ≤ (∫ ξ in {ξ : ℝ | |ξ| ≤ L},
            ‖∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖^2
              * ‖𝓕 F ξ‖^2)
        + Mtot^2 * ((1/L^2) * ∫ ξ, ξ^2 * ‖𝓕 F ξ‖^2) := by
  classical
  have hMtot0 : 0 ≤ Mtot := le_trans (norm_nonneg _) (htot 0)
  set G : SchwartzMap ℝ ℂ := hFc.toSchwartzMap hFs with hG_def
  have hbase := integral_norm_sq_sum_translates F hFc hFs S w s
  rw [hbase]
  set φ : ℝ → ℝ := fun ξ =>
    ‖∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖^2
      * ‖𝓕 F ξ‖^2 with hφ_def
  -- the Schwartz sup bound, and the two integrability facts it gives
  obtain ⟨C, hC⟩ := (𝓕 G).decay' 0 0
  have hC' : ∀ ξ : ℝ, ‖(𝓕 G) ξ‖ ≤ C := fun ξ => by
    have := hC ξ
    simpa using! this
  have hFG : (fun ξ : ℝ => ‖𝓕 F ξ‖^2) = (fun ξ : ℝ => ‖(𝓕 G) ξ‖^2) := rfl
  have hFhat_int : Integrable (fun ξ : ℝ => ‖𝓕 F ξ‖^2) := by
    rw [hFG]
    refine ((𝓕 G).integrable.norm.const_mul C).mono' ?_ ?_
    · exact ((𝓕 G).continuous.norm.pow 2).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ξ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ‖(𝓕 G) ξ‖^2 = ‖(𝓕 G) ξ‖ * ‖(𝓕 G) ξ‖ := by ring
        _ ≤ C * ‖(𝓕 G) ξ‖ :=
            mul_le_mul_of_nonneg_right (hC' ξ) (norm_nonneg _)
  have hFGpt : ∀ ξ : ℝ, ‖𝓕 F ξ‖ = ‖(𝓕 G) ξ‖ := fun _ => rfl
  have hxi_int : Integrable (fun ξ : ℝ => ξ^2 * ‖𝓕 F ξ‖^2) := by
    simp only [hFGpt]
    refine (((𝓕 G).integrable_pow_mul volume 2).const_mul C).mono' ?_ ?_
    · exact ((continuous_id.pow 2).mul
        ((𝓕 G).continuous.norm.pow 2)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ξ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ξ^2 * ‖(𝓕 G) ξ‖^2 = (‖(𝓕 G) ξ‖ * ξ^2) * ‖(𝓕 G) ξ‖ := by ring
        _ ≤ (C * ξ^2) * ‖(𝓕 G) ξ‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            exact mul_le_mul_of_nonneg_right (hC' ξ) (by positivity)
        _ = C * (ξ^2 * ‖(𝓕 G) ξ‖) := by ring
        _ = C * (‖ξ‖^2 * ‖(𝓕 G) ξ‖) := by rw [Real.norm_eq_abs, sq_abs]
  have hphase_cont : Continuous fun ξ : ℝ =>
      ∑ i ∈ S, w i * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ) := by
    refine continuous_finset_sum _ fun i _ => ?_
    refine Continuous.mul continuous_const ?_
    refine Continuous.comp continuous_subtype_val ?_
    exact Real.continuous_fourierChar.comp (by fun_prop)
  have hφ_int : Integrable φ := by
    refine (hFhat_int.const_mul (Mtot^2)).mono' ?_ ?_
    · rw [hφ_def]
      simp only [hFGpt]
      exact ((hphase_cont.norm.pow 2).mul
        ((𝓕 G).continuous.norm.pow 2)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ξ => ?_
      rw [hφ_def, Real.norm_eq_abs]
      dsimp only
      rw [abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have h1 := htot ξ
      nlinarith [norm_nonneg (∑ i ∈ S, w i
        * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ))]
  -- the tail majorant
  set ψ : ℝ → ℝ := fun ξ => Mtot^2 * ((1/L^2) * (ξ^2 * ‖𝓕 F ξ‖^2)) with hψ_def
  have hψ_int : Integrable ψ := (hxi_int.const_mul _).const_mul _
  have hmeas : MeasurableSet {ξ : ℝ | |ξ| ≤ L} :=
    measurableSet_le continuous_abs.measurable measurable_const
  have hsplit := (integral_add_compl hmeas hφ_int).symm
  rw [hsplit]
  -- above `L` the phase polynomial is bounded and `ξ²/L² ≥ 1`
  have hpt : ∀ ξ ∈ {ξ : ℝ | |ξ| ≤ L}ᶜ, φ ξ ≤ ψ ξ := by
    intro ξ hξ
    have hξL : L < |ξ| := by
      rw [Set.mem_compl_iff, Set.mem_setOf_eq] at hξ
      exact not_le.mp hξ
    rw [hφ_def, hψ_def]
    dsimp only
    have h2 : ‖∑ i ∈ S, w i
          * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ)‖^2 ≤ Mtot^2 := by
      nlinarith [htot ξ, norm_nonneg (∑ i ∈ S, w i
        * ((Real.fourierChar (-(s i * ξ)) : Circle) : ℂ))]
    have h4 : ‖𝓕 F ξ‖^2 ≤ (1/L^2) * (ξ^2 * ‖𝓕 F ξ‖^2) := by
      have h5 : (1/L^2) * (ξ^2 * ‖𝓕 F ξ‖^2) = (ξ^2/L^2) * ‖𝓕 F ξ‖^2 := by ring
      have h3 : (1:ℝ) ≤ ξ^2 / L^2 := by
        rw [le_div_iff₀ (by positivity)]
        have h6 : L^2 ≤ ξ^2 := by
          rw [← sq_abs ξ]
          exact pow_le_pow_left₀ hL.le hξL.le 2
        linarith
      rw [h5]
      nlinarith [sq_nonneg ‖𝓕 F ξ‖]
    nlinarith [sq_nonneg ‖𝓕 F ξ‖, mul_le_mul_of_nonneg_right h2
      (sq_nonneg ‖𝓕 F ξ‖), mul_le_mul_of_nonneg_left h4 (sq_nonneg Mtot)]
  have hcompl : ∫ ξ in {ξ : ℝ | |ξ| ≤ L}ᶜ, φ ξ
      ≤ ∫ ξ in {ξ : ℝ | |ξ| ≤ L}ᶜ, ψ ξ :=
    setIntegral_mono_on hφ_int.integrableOn hψ_int.integrableOn
      hmeas.compl hpt
  have hfull : ∫ ξ in {ξ : ℝ | |ξ| ≤ L}ᶜ, ψ ξ ≤ ∫ ξ, ψ ξ := by
    refine setIntegral_le_integral hψ_int ?_
    refine Filter.Eventually.of_forall fun ξ => ?_
    rw [hψ_def]
    dsimp only
    positivity
  have hψ_val : ∫ ξ, ψ ξ = Mtot^2 * ((1/L^2) * ∫ ξ, ξ^2 * ‖𝓕 F ξ‖^2) := by
    rw [hψ_def, integral_const_mul, integral_const_mul]
  linarith [hcompl, hfull, hψ_val.le, hψ_val.ge]

/-- **The window energy, low band left as an energy** (Track R, A2-III E-2).

`window_energy_regime_le` with the sup slot removed: the smoothed-window line
energy against the *band energy* of the plain phase polynomial below `L`, plus
the derivative-energy tail.

This is the form the `[mrt]` A.2 capstone can discharge.  Its predecessor prices
the frequency range below `L` as `(4H/A)²·∫_{−K}^{K}‖P‖² + Mmid²·(4H/A)` — an
explicit low-band energy plus the *trivial* bound on the mid band — and the
whole point of the band campaign is that the mid band admits far better than
trivial.  Here the mid band is not bounded at all: it is left inside the
integral, weighted by `‖𝓕F‖²`, which is exactly the capstone's abstract `w`.

**Three hypotheses of the predecessor are gone**: `K` and `Mmid` with the sup
they carried, and `hη01`.  That last one is worth noting — `0 ≤ η ≤ 1` was
needed only to sup the window transform by `4/T` on the low band
(`norm_fourier_slice_window_le`), and with the weight kept there is nothing to
sup.  A consumer that wants the sup back applies
`ExpSums.setIntegral_weight_le_const` at `Cw = (4H/A)²`, which is where that
constant belongs.

The `4H·(A/H)·(h·m/(4A))/m = h` weight identity is the same as in the
predecessor: the translate weights are the raw coefficients. -/
theorem window_energy_regime_energy_le (h : ℕ → ℂ)
    (A s H U : ℕ) (hA : 1 ≤ A) (hH : 0 < H)
    (η : ℝ → ℝ) (hηs : ContDiff ℝ ∞ η) (hη2 : ∀ u, η u ≠ 0 → |u| ≤ 2)
    (L Mtot Eder : ℝ) (hL : 0 < L)
    (htot : ∀ ξ : ℝ,
      ‖∑ m ∈ Finset.Ioc A (A+s+2*H+4*U),
        h m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖ ≤ Mtot)
    (hder : ∫ ξ, ξ^2 * ‖𝓕 (fun v =>
        ((η (((A:ℝ)/H)*v) : ℝ) : ℂ)) ξ‖^2 ≤ Eder) :
    ∫ y, ‖(4*(H:ℂ)) * smoothedLogSum ((A:ℝ)/H) η
        (fun m => if m ∈ Finset.Ioc A (A+s+2*H+4*U)
          then h m * (m:ℂ)/(4*(A:ℂ)) else 0)
        (Finset.Ioc A (A+s+2*H+4*U)) y‖^2
      ≤ (∫ ξ in {ξ : ℝ | |ξ| ≤ L},
            ‖∑ m ∈ Finset.Ioc A (A+s+2*H+4*U),
              h m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2
              * ‖𝓕 (fun v => ((η (((A:ℝ)/H)*v) : ℝ) : ℂ)) ξ‖^2)
        + Mtot^2 * ((1/L^2) * Eder) := by
  classical
  have hAR : (0:ℝ) < (A:ℝ) := by exact_mod_cast (by omega : 0 < A)
  have hHR : (0:ℝ) < (H:ℝ) := by exact_mod_cast hH
  set T : ℝ := (A:ℝ)/H with hT_def
  have hT : 0 < T := by positivity
  set S : Finset ℕ := Finset.Ioc A (A+s+2*H+4*U) with hS_def
  set F : ℝ → ℂ := fun v => ((η (T*v) : ℝ) : ℂ) with hF_def
  obtain ⟨hFc, hFs⟩ := window_profile_props T hT η hηs hη2
  -- the weight identity: the translate weights are the raw `h`
  have htrans : ∀ y : ℝ, (4*(H:ℂ)) * smoothedLogSum T η
      (fun m => if m ∈ S then h m * (m:ℂ)/(4*(A:ℂ)) else 0) S y
      = ∑ m ∈ S, h m * F (y - Real.log m) := by
    intro y
    rw [smoothedLogSum_eq_sum_translates, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [if_pos hm]
    have hm1 : 1 ≤ m := by
      rw [hS_def, Finset.mem_Ioc] at hm
      omega
    have hmC : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hAC : ((A:ℕ):ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hHC : ((H:ℕ):ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hTC : ((T:ℝ):ℂ) = ((A:ℕ):ℂ)/((H:ℕ):ℂ) := by
      rw [hT_def]
      push_cast
      ring
    rw [hF_def, hTC]
    field_simp
  have hcongr : ∫ y, ‖(4*(H:ℂ)) * smoothedLogSum T η
      (fun m => if m ∈ S then h m * (m:ℂ)/(4*(A:ℂ)) else 0) S y‖^2
      = ∫ y, ‖∑ m ∈ S, h m * F (y - Real.log m)‖^2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => by
      simpa using congrArg (fun z : ℂ => ‖z‖^2) (htrans y))
  rw [hcongr]
  refine le_trans (integral_norm_sq_sum_translates_energy_split F hFc hFs S h
    (fun m => Real.log m) L Mtot hL htot) ?_
  have htail : Mtot^2 * ((1/L^2) * ∫ ξ, ξ^2 * ‖𝓕 F ξ‖^2)
      ≤ Mtot^2 * ((1/L^2) * Eder) := by
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg Mtot)
    exact mul_le_mul_of_nonneg_left hder (by positivity)
  linarith [htail]


end ExpSums

end MoltResearch
