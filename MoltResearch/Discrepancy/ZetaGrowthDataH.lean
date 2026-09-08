import MoltResearch.Discrepancy.ZetaGrowthLogDerivSharp
import MoltResearch.Discrepancy.PrimeLargeValuesFromRegionH
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Height-indexed zero-free data from a zeta growth estimate

This leaf joins the asymptotic zero-free and logarithmic-derivative theorems
to the height-indexed record.  A compactness argument for the entire
pole-removed zeta function supplies the bounded-height constants.
-/

namespace MoltResearch

namespace ExpSums

open Complex Filter

/-- On a bounded horizontal strip, the pole-removed zeta function stays
uniformly nonzero in a sufficiently thin neighbourhood of `re = 1`, and its
regular logarithmic derivative is uniformly bounded there. -/
theorem exists_zeta_compact_strip_data (H : ℝ) (hH : 0 ≤ H) :
    ∃ eta M : ℝ, 0 < eta ∧ eta ≤ 1 / 16 ∧ 1 ≤ M ∧
      ∀ z : ℂ, 1 - eta ≤ z.re → z.re ≤ 2 → |z.im| ≤ H → z ≠ 1 →
        riemannZeta z ≠ 0 ∧
          ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤ M := by
  classical
  obtain ⟨G, hG, hGval⟩ := exists_zeta_pole_reg
  let F : ℂ → ℂ := zetaPoleRemoved G
  let K : Set ℂ := Set.Icc (1 : ℝ) 1 ×ℂ Set.Icc (-H) H
  let N : Set ℂ := {z | F z = 0}
  have hFdiff : Differentiable ℂ F := zetaPoleRemoved_differentiable G hG
  have hKcompact : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hNclosed : IsClosed N := by
    exact isClosed_eq hFdiff.continuous continuous_const
  have hKN : Disjoint K N := by
    rw [Set.disjoint_left]
    intro z hzK hzN
    have hzre : z.re = 1 := by
      have := hzK.1
      simpa only [Set.mem_Icc] using le_antisymm this.2 this.1
    by_cases hz1 : z = 1
    · subst z
      simp [N, F, zetaPoleRemoved] at hzN
    · have hzeta : riemannZeta z ≠ 0 :=
        riemannZeta_ne_zero_of_one_le_re (by rw [hzre])
      have hFeq := zetaPoleRemoved_eq G hGval z hz1
      change F z = 0 at hzN
      change zetaPoleRemoved G z = 0 at hzN
      rw [hFeq] at hzN
      exact (mul_ne_zero (sub_ne_zero.mpr hz1) hzeta) hzN
  obtain ⟨r, hr, hsep⟩ :=
    Metric.exists_pos_forall_lt_edist hKcompact hNclosed hKN
  let eta : ℝ := min (1 / 16) ((r : ℝ) / 2)
  have heta0 : 0 < eta := lt_min (by norm_num) (by positivity)
  have heta16 : eta ≤ 1 / 16 := min_le_left _ _
  have hetar : eta ≤ (r : ℝ) / 2 := min_le_right _ _
  let R : Set ℂ := Set.Icc (1 - eta) 2 ×ℂ Set.Icc (-H) H
  have hRcompact : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  have hFne : ∀ z ∈ R, F z ≠ 0 := by
    intro z hzR hzF
    by_cases hzright : 1 ≤ z.re
    · by_cases hz1 : z = 1
      · subst z
        simp [F, zetaPoleRemoved] at hzF
      · have hzeta : riemannZeta z ≠ 0 :=
          riemannZeta_ne_zero_of_one_le_re hzright
        have hFeq := zetaPoleRemoved_eq G hGval z hz1
        change zetaPoleRemoved G z = 0 at hzF
        rw [hFeq] at hzF
        exact (mul_ne_zero (sub_ne_zero.mpr hz1) hzeta) hzF
    · let w : ℂ := (1 : ℂ) + I * z.im
      have hwK : w ∈ K := by
        change w.re ∈ Set.Icc (1 : ℝ) 1 ∧ w.im ∈ Set.Icc (-H) H
        constructor
        · simp [w]
        · have him := hzR.2
          change z.im ∈ Set.Icc (-H) H at him
          rw [Set.mem_Icc] at him ⊢
          simpa [w] using him
      have hzN : z ∈ N := by simpa only [N, Set.mem_setOf_eq] using hzF
      have hsep' := hsep w hwK z hzN
      rw [edist_dist, ← ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_lt_ofReal_iff'] at hsep'
      have hdist : dist w z = |1 - z.re| := by
        rw [dist_eq]
        have heq : w - z = ((1 - z.re : ℝ) : ℂ) := by
          apply Complex.ext <;> simp [w]
        rw [heq, Complex.norm_real, Real.norm_eq_abs]
      have hdisteta : dist w z ≤ eta := by
        rw [hdist, abs_of_nonneg (by linarith)]
        have hre := hzR.1
        change z.re ∈ Set.Icc (1 - eta) 2 at hre
        rw [Set.mem_Icc] at hre
        linarith
      have : (r : ℝ) < dist w z := hsep'.1
      linarith
  have hregCont : ContinuousOn (zetaLogDerivRegular G) R := by
    intro z hz
    exact (zetaLogDerivRegular_differentiableAt G hG z (hFne z hz)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hRcompact.exists_bound_of_continuousOn hregCont
  let M : ℝ := max 1 C
  refine ⟨eta, M, heta0, heta16, le_max_left _ _, ?_⟩
  intro z hzre hzre2 hzim hz1
  have hzR : z ∈ R := by
    change z.re ∈ Set.Icc (1 - eta) 2 ∧ z.im ∈ Set.Icc (-H) H
    exact ⟨⟨hzre, hzre2⟩, (abs_le.mp hzim)⟩
  have hFz := hFne z hzR
  have hFeq := zetaPoleRemoved_eq G hGval z hz1
  have hzeta : riemannZeta z ≠ 0 := by
    intro hz
    apply hFz
    change zetaPoleRemoved G z = 0
    rw [hFeq, hz, mul_zero]
  refine ⟨hzeta, ?_⟩
  rw [← zetaLogDerivRegular_eq G hG hGval z hz1 hzeta]
  exact (hC z hzR).trans (le_max_right _ _)

/-- Any stated growth bound can be enlarged, above a harmless height, so that
all three coefficients used by the Landau argument have the required signs. -/
theorem exists_nonnegative_zetaGrowthBound
    {t₀ a B b B₀ : ℝ} (h : ZetaGrowthBound t₀ a B b B₀)
    (ha : 0 < a) :
    ∃ t₁ B₁ b₁ B₁₀ : ℝ, t₀ ≤ t₁ ∧ 0 < B₁ ∧ 0 ≤ b₁ ∧ 0 ≤ B₁₀ ∧
      ZetaGrowthBound t₁ a B₁ b₁ B₁₀ := by
  let t₁ : ℝ := max t₀ (Real.exp (Real.exp 1))
  let B₁ : ℝ := max B 1
  let b₁ : ℝ := max b 0
  let B₁₀ : ℝ := max B₀ 0
  have ht : t₀ ≤ t₁ := le_max_left _ _
  have hB : 0 < B₁ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hb : 0 ≤ b₁ := le_max_right _ _
  have hB₀ : 0 ≤ B₁₀ := le_max_right _ _
  refine ⟨t₁, B₁, b₁, B₁₀, ht, hB, hb, hB₀, ⟨?_⟩⟩
  intro σ t ht₁ hσ hσ₂
  have htold : t₀ ≤ |t| := le_trans ht ht₁
  have habs : Real.exp (Real.exp 1) ≤ |t| := le_trans (le_max_right _ _) ht₁
  have hlog : Real.exp 1 ≤ Real.log |t| := by
    exact (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) habs)).mpr habs
  have hlog0 : 0 ≤ Real.log |t| := le_trans (Real.exp_pos _).le hlog
  have hloglog : 0 ≤ Real.log (Real.log |t|) := by
    have := Real.log_le_log (Real.exp_pos 1) hlog
    have : 1 ≤ Real.log (Real.log |t|) := by simpa using this
    linarith
  have hbase : 0 ≤ (max (1 - σ) 0) ^ a := Real.rpow_nonneg (by positivity) _
  have hold := h.bound σ t htold hσ hσ₂
  calc
    Real.log ‖riemannZeta ((σ : ℂ) + I * t)‖ ≤
        B * (max (1 - σ) 0) ^ a * Real.log |t| +
          b * Real.log (Real.log |t|) + B₀ := hold
    _ ≤ B₁ * (max (1 - σ) 0) ^ a * Real.log |t| +
          b₁ * Real.log (Real.log |t|) + B₁₀ := by
      have hBmono := le_max_left B 1
      have hbmono := le_max_left b 0
      have hB₀mono := le_max_left B₀ 0
      gcongr

/-- A named threshold for absorbing an arbitrary real power of `log L` into
the fixed spare power `L^eps`. -/
theorem exists_log_rpow_le_mul_rpow
    (q d eps : ℝ) (hd : 0 < d) (heps : 0 < eps) :
    ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      (Real.log L) ^ q ≤ d * L ^ eps := by
  have hlo := isLittleO_log_rpow_rpow_atTop q heps
  have hevent := hlo.def hd
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨L₁, hL₁⟩ := hevent
  refine ⟨max (Real.exp 1) L₁, le_max_left _ _, ?_⟩
  intro L hL
  have hLe : Real.exp 1 ≤ L := le_trans (le_max_left _ _) hL
  have hL₁' : L₁ ≤ L := le_trans (le_max_right _ _) hL
  have hlog0 : 0 ≤ Real.log L :=
    Real.log_nonneg (le_trans (Real.one_lt_exp_iff.mpr zero_lt_one).le hLe)
  have hL0 : 0 ≤ L := le_trans (Real.exp_pos 1).le hLe
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog0 _),
    abs_of_nonneg (Real.rpow_nonneg hL0 _)] using hL₁ L hL₁'

/-- The spare exponent `1/100` dominates the iterated-log loss in the true
growth-region width. -/
theorem exists_record_width_le_growth_model
    (a d : ℝ) (ha : 1 < a) (hd : 0 < d) :
    ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      L ^ (-(1 / a + 1 / 100)) ≤
        d * (Real.log L) ^ (1 / a - 1) / L ^ (1 / a) := by
  let p : ℝ := 1 / a
  let q : ℝ := 1 - p
  obtain ⟨L₀, hL₀, hbound⟩ :=
    exists_log_rpow_le_mul_rpow q d (1 / 100) hd (by norm_num)
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL
  have hLe : Real.exp 1 ≤ L := le_trans hL₀ hL
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
  have hlog1 : 1 ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos 1) hLe
    simpa using this
  have hlog0 : 0 < Real.log L := by linarith
  have hp0 : 0 < p := by dsimp only [p]; positivity
  have hq0 : 0 < q := by
    dsimp only [q, p]
    have : 1 / a < 1 := (div_lt_one (by linarith : 0 < a)).2 ha
    linarith
  have hqbound : (Real.log L) ^ q ≤ d * L ^ (1 / 100 : ℝ) :=
    hbound L hL
  have hLeps : 0 < L ^ (1 / 100 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hlogq : 0 < (Real.log L) ^ q := Real.rpow_pos_of_pos hlog0 _
  have hinv : 1 / L ^ (1 / 100 : ℝ) ≤ d / (Real.log L) ^ q := by
    rw [div_le_div_iff₀ hLeps hlogq]
    simpa only [one_mul] using hqbound
  have hmul := mul_le_mul_of_nonneg_left hinv
    (show 0 ≤ 1 / L ^ p by positivity)
  have hleft : (1 / L ^ p) * (1 / L ^ (1 / 100 : ℝ)) =
      L ^ (-(1 / a + 1 / 100)) := by
    dsimp only [p]
    rw [Real.rpow_neg hL0.le, Real.rpow_add hL0]
    field_simp
  have hright : (1 / L ^ p) * (d / (Real.log L) ^ q) =
      d * (Real.log L) ^ (1 / a - 1) / L ^ (1 / a) := by
    have hexp : 1 / a - 1 = -q := by dsimp only [q, p]; ring
    rw [hexp, Real.rpow_neg hlog0.le]
    dsimp only [p]
    ring
  rw [hleft, hright] at hmul
  exact hmul

/-- The model width evaluated at an upper height is no larger than the true
growth width at any sufficiently large lower height. -/
theorem growth_model_le_zetaGrowthWidth
    {a u V : ℝ} (ha : 1 < a) (hu : Real.exp (Real.exp 1) ≤ u)
    (huV : u ≤ V) :
    (Real.log (Real.log V)) ^ (1 / a - 1) /
        (Real.log V) ^ (1 / a) ≤ zetaGrowthWidth a u := by
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos _) hu
  have hV0 : 0 < V := lt_of_lt_of_le hu0 huV
  have hLuExp : Real.exp 1 ≤ Real.log u :=
    (Real.le_log_iff_exp_le hu0).mpr hu
  have hLu0 : 0 < Real.log u := lt_of_lt_of_le (Real.exp_pos 1) hLuExp
  have hellu1 : 1 ≤ Real.log (Real.log u) := by
    have := Real.log_le_log (Real.exp_pos 1) hLuExp
    simpa using this
  have hLV : Real.log u ≤ Real.log V := Real.log_le_log hu0 huV
  have hLV0 : 0 < Real.log V := lt_of_lt_of_le hLu0 hLV
  have hell : Real.log (Real.log u) ≤ Real.log (Real.log V) :=
    Real.log_le_log hLu0 hLV
  have hp0 : 0 < 1 / a := one_div_pos.mpr (by linarith)
  have hexp : 1 / a - 1 ≤ 0 := by
    have : 1 / a ≤ 1 := (div_le_one (by linarith : 0 < a)).2 (by linarith)
    linarith
  have hnum : (Real.log (Real.log V)) ^ (1 / a - 1) ≤
      (Real.log (Real.log u)) ^ (1 / a - 1) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hell hexp
  have hden : (Real.log u) ^ (1 / a) ≤ (Real.log V) ^ (1 / a) :=
    Real.rpow_le_rpow hLu0.le hLV hp0.le
  rw [zetaGrowthWidth, abs_of_pos hu0]
  exact div_le_div₀ (Real.rpow_nonneg (by linarith) _) hnum
    (Real.rpow_pos_of_pos hLu0 _) hden

/-- After increasing the height threshold, the fixed coefficient in the
half-slack estimate is absorbed by the remaining `1/20`. -/
theorem zeta_regular_logDeriv_bound_of_growth_unit
    {t₀ a B b B₀ : ℝ} (h : ZetaGrowthBound t₀ a B b B₀)
    (ha : 1 < a) (hB : 0 < B) (hb : 0 ≤ b) (hB₀ : 0 ≤ B₀) :
    ∃ c t₁ : ℝ, 0 < c ∧ t₀ ≤ t₁ ∧
      ∀ z : ℂ, t₁ ≤ |z.im| →
        1 - zetaGrowthRegionEta a c z.im / 2 ≤ z.re → z.re ≤ 2 →
        z ≠ 1 →
        ‖-deriv riemannZeta z / riemannZeta z - 1 / (z - 1)‖ ≤
          (Real.log |z.im|) ^ (1 / a + 1 / 10) := by
  obtain ⟨c, C, t₁, hc, hC, ht₁, hreg⟩ :=
    zeta_regular_logDeriv_bound_of_growth_half h ha hB hb hB₀
  have hpowtop : Tendsto (fun L : ℝ => L ^ (1 / 20 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hevent : ∀ᶠ L : ℝ in atTop, C ≤ L ^ (1 / 20 : ℝ) :=
    hpowtop.eventually (eventually_ge_atTop C)
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨L₀, hL₀⟩ := hevent
  let t₂ : ℝ := max t₁ (Real.exp (max 1 L₀))
  have ht₀t₂ : t₀ ≤ t₂ := le_trans ht₁ (le_max_left _ _)
  refine ⟨c, t₂, hc, ht₀t₂, ?_⟩
  intro z hz hzr hzre hz1
  have hzt₁ : t₁ ≤ |z.im| := le_trans (le_max_left _ _) hz
  have hexp : Real.exp (max 1 L₀) ≤ |z.im| :=
    le_trans (le_max_right _ _) hz
  have hu0 : 0 < |z.im| := lt_of_lt_of_le (Real.exp_pos _) hexp
  have hlog : max 1 L₀ ≤ Real.log |z.im| :=
    (Real.le_log_iff_exp_le hu0).mpr hexp
  have hlog0 : 0 < Real.log |z.im| := lt_of_lt_of_le zero_lt_one
    (le_trans (le_max_left _ _) hlog)
  have hCL : C ≤ (Real.log |z.im|) ^ (1 / 20 : ℝ) :=
    hL₀ _ (le_trans (le_max_right _ _) hlog)
  have hbase0 : 0 ≤ (Real.log |z.im|) ^ (1 / a + 1 / 20) :=
    Real.rpow_nonneg hlog0.le _
  calc
    _ ≤ C * (Real.log |z.im|) ^ (1 / a + 1 / 20) :=
      hreg z hzt₁ hzr hzre hz1
    _ ≤ (Real.log |z.im|) ^ (1 / 20 : ℝ) *
        (Real.log |z.im|) ^ (1 / a + 1 / 20) :=
      mul_le_mul_of_nonneg_right hCL hbase0
    _ = (Real.log |z.im|) ^ (1 / a + 1 / 10) := by
      rw [← Real.rpow_add hlog0]
      congr 1
      ring

set_option maxHeartbeats 1600000

/-- **V-C4-4, existence form.** A power-type zeta growth estimate with
`a ≥ 33/25` supplies a height-indexed zero-free record at the exact exponents
needed by the three-regime argument. -/
theorem nonempty_zeroFreeRegionDataH_of_growth
    {t₀ a B b B₀ : ℝ} (h : ZetaGrowthBound t₀ a B b B₀)
    (ha : 33 / 25 ≤ a) :
    Nonempty (ZeroFreeRegionDataH (1 / a + 1 / 100) (1 / a + 1 / 10)) := by
  have ha1 : 1 < a := by linarith
  have ha0 : 0 < a := by linarith
  obtain ⟨tg, Bg, bg, Bg₀, ht₀g, hBg, hbg, hBg₀, hg⟩ :=
    exists_nonnegative_zetaGrowthBound h ha0
  obtain ⟨cz, tz, hcz, htgz, hzero⟩ :=
    zeta_zero_free_of_growth hg ha1 hBg hbg hBg₀
  obtain ⟨cr, tr, hcr, htgr, hreg⟩ :=
    zeta_regular_logDeriv_bound_of_growth_unit hg ha1 hBg hbg hBg₀
  let d : ℝ := min (cz / 2) (cr / 4)
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hdcz : d ≤ cz / 2 := min_le_left _ _
  have hdcr : d ≤ cr / 4 := min_le_right _ _
  obtain ⟨L₀, hL₀, hwidth⟩ :=
    exists_record_width_le_growth_model a d ha1 hd
  let H : ℝ := max (Real.exp (Real.exp 1))
    (max tz (max tr (Real.exp L₀)))
  have hH0 : 0 ≤ H := le_trans (Real.exp_pos _).le (le_max_left _ _)
  obtain ⟨eta₀, M₀, heta₀, heta₀16, hM₀, hcompact⟩ :=
    exists_zeta_compact_strip_data H hH0
  have htheta : 0 < 1 / a + 1 / 100 := by positivity
  refine ⟨⟨htheta, eta₀, heta₀, le_trans heta₀16 (by norm_num),
    M₀, hM₀, ?_, ?_⟩⟩
  · intro Z hZ z hzre hzre2 hzim hz1
    by_cases hlow : |z.im| ≤ H
    · exact (hcompact z
        (le_trans (by
          dsimp only [zeroFreeRegionEtaH]
          exact sub_le_sub_left (min_le_left _ _) 1) hzre)
        hzre2 hlow hz1).1
    · have hhigh : H < |z.im| := lt_of_not_ge hlow
      let L : ℝ := Real.log (2 * Z)
      have hZ0 : 0 < Z := by linarith
      have hL0pos : 0 < L := by
        dsimp only [L]
        exact Real.log_pos (by nlinarith)
      have hExpL : Real.exp L₀ ≤ 2 * Z := by
        have hHexp : Real.exp L₀ ≤ H :=
          le_trans (le_max_right _ _)
            (le_trans (le_max_right _ _) (le_max_right _ _))
        have habsZ : |z.im| ≤ Z := hzim
        linarith
      have hLL₀ : L₀ ≤ L := by
        dsimp only [L]
        exact (Real.le_log_iff_exp_le (by positivity : 0 < 2 * Z)).mpr hExpL
      have hrecord := hwidth L hLL₀
      have huBase : Real.exp (Real.exp 1) ≤ |z.im| :=
        le_trans (le_max_left _ _) hhigh.le
      have huV : |z.im| ≤ 2 * Z := by linarith
      have hmodelZero := growth_model_le_zetaGrowthWidth ha1 huBase huV
      have hmodelZero' :
          (Real.log L) ^ (1 / a - 1) / L ^ (1 / a) ≤
            zetaGrowthWidth a z.im := by
        simpa only [L, zetaGrowthWidth, abs_abs] using hmodelZero
      have hetaLog : zeroFreeRegionEtaH (1 / a + 1 / 100) eta₀ Z ≤
          L ^ (-(1 / a + 1 / 100)) := by
        dsimp only [zeroFreeRegionEtaH, L]
        exact min_le_right _ _
      have hetaModel : zeroFreeRegionEtaH (1 / a + 1 / 100) eta₀ Z ≤
          d * ((Real.log L) ^ (1 / a - 1) / L ^ (1 / a)) :=
        hetaLog.trans (by simpa only [mul_div_assoc] using hrecord)
      have hmodel0 : 0 < (Real.log L) ^ (1 / a - 1) / L ^ (1 / a) := by
        have hLexp : Real.exp 1 ≤ L := le_trans hL₀ hLL₀
        have : 0 < Real.log L := by
          have hh := Real.log_le_log (Real.exp_pos 1) hLexp
          have : 1 ≤ Real.log L := by simpa using hh
          linarith
        positivity
      have hwidth0 : 0 < zetaGrowthWidth a z.im :=
        lt_of_lt_of_le hmodel0 hmodelZero'
      have hetaWidth : zeroFreeRegionEtaH (1 / a + 1 / 100) eta₀ Z <
          cz * zetaGrowthWidth a z.im := by
        calc
          _ ≤ d * ((Real.log L) ^ (1 / a - 1) / L ^ (1 / a)) := hetaModel
          _ ≤ d * zetaGrowthWidth a z.im :=
            mul_le_mul_of_nonneg_left hmodelZero' hd.le
          _ ≤ (cz / 2) * zetaGrowthWidth a z.im :=
            mul_le_mul_of_nonneg_right hdcz hwidth0.le
          _ < cz * zetaGrowthWidth a z.im := by nlinarith
      intro hzeta
      have htz : tz ≤ |z.im| :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hhigh.le)
      have hzform : ((z.re : ℝ) : ℂ) + I * z.im = z := by
        apply Complex.ext <;> simp
      have hzbound := hzero z.re z.im htz (by rw [hzform]; exact hzeta)
      have hzbound' : z.re ≤ 1 - cz * zetaGrowthWidth a z.im := by
        simpa only [show cz * (Real.log (Real.log |z.im|)) ^ (1 / a - 1) /
            (Real.log |z.im|) ^ (1 / a) = cz * zetaGrowthWidth a z.im by
          rw [zetaGrowthWidth]
          ring] using hzbound
      linarith
  · intro Z hZ z hzre hzre2 hzim hz1
    by_cases hlow : |z.im| ≤ H
    · exact (hcompact z
        (le_trans (by
          dsimp only [zeroFreeRegionEtaH]
          exact sub_le_sub_left (min_le_left _ _) 1) hzre)
        hzre2 hlow hz1).2.trans (le_max_left _ _)
    · have hhigh : H < |z.im| := lt_of_not_ge hlow
      let L : ℝ := Real.log (2 * Z)
      have hZ0 : 0 < Z := by linarith
      have hExpL : Real.exp L₀ ≤ 2 * Z := by
        have hHexp : Real.exp L₀ ≤ H :=
          le_trans (le_max_right _ _)
            (le_trans (le_max_right _ _) (le_max_right _ _))
        linarith
      have hLL₀ : L₀ ≤ L := by
        dsimp only [L]
        exact (Real.le_log_iff_exp_le (by positivity : 0 < 2 * Z)).mpr hExpL
      have hrecord := hwidth L hLL₀
      have huBase : Real.exp (Real.exp 1) ≤ 2 * |z.im| := by
        have := le_trans (le_max_left _ _) hhigh.le
        nlinarith [abs_nonneg z.im]
      have huV : 2 * |z.im| ≤ 2 * Z := by nlinarith
      have hmodelReg := growth_model_le_zetaGrowthWidth ha1 huBase huV
      have hmodelReg' :
          (Real.log L) ^ (1 / a - 1) / L ^ (1 / a) ≤
            zetaGrowthWidth a (2 * |z.im|) := by
        simpa only [L] using hmodelReg
      have hetaLog : zeroFreeRegionEtaH (1 / a + 1 / 100) eta₀ Z ≤
          L ^ (-(1 / a + 1 / 100)) := by
        dsimp only [zeroFreeRegionEtaH, L]
        exact min_le_right _ _
      have hetaModel : zeroFreeRegionEtaH (1 / a + 1 / 100) eta₀ Z ≤
          d * ((Real.log L) ^ (1 / a - 1) / L ^ (1 / a)) :=
        hetaLog.trans (by simpa only [mul_div_assoc] using hrecord)
      have hetaWidth : zeroFreeRegionEtaH (1 / a + 1 / 100) eta₀ Z ≤
          (cr / 4) * zetaGrowthWidth a (2 * |z.im|) :=
        calc
          _ ≤ d * ((Real.log L) ^ (1 / a - 1) / L ^ (1 / a)) := hetaModel
          _ ≤ d * zetaGrowthWidth a (2 * |z.im|) :=
            mul_le_mul_of_nonneg_left hmodelReg' hd.le
          _ ≤ (cr / 4) * zetaGrowthWidth a (2 * |z.im|) :=
            mul_le_mul_of_nonneg_right hdcr (by
              have hLpos : 0 < L := by
                dsimp only [L]
                exact Real.log_pos (by nlinarith)
              have hlogL : 0 < Real.log L := by
                have hLexp : Real.exp 1 ≤ L := le_trans hL₀ hLL₀
                have hh := Real.log_le_log (Real.exp_pos 1) hLexp
                have : 1 ≤ Real.log L := by simpa using hh
                linarith
              exact le_trans (by positivity) hmodelReg')
      have heta16 : zeroFreeRegionEtaH (1 / a + 1 / 100) eta₀ Z ≤ 1 / 16 :=
        le_trans (min_le_left _ _) heta₀16
      have hetaRegion : zeroFreeRegionEtaH (1 / a + 1 / 100) eta₀ Z ≤
          zetaGrowthRegionEta a cr z.im / 2 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
        rw [zetaGrowthRegionEta]
        apply le_min
        · nlinarith
        · simpa only [abs_abs] using (show
            zeroFreeRegionEtaH (1 / a + 1 / 100) eta₀ Z * 2 ≤
              (cr / 2) * zetaGrowthWidth a (2 * |z.im|) by
                nlinarith)
      have htr : tr ≤ |z.im| := by
        calc
          tr ≤ max tr (Real.exp L₀) := le_max_left _ _
          _ ≤ max tz (max tr (Real.exp L₀)) := le_max_right _ _
          _ ≤ H := le_max_right _ _
          _ ≤ |z.im| := hhigh.le
      have hr := hreg z htr (by linarith) hzre2 hz1
      have hlogim0 : 0 < Real.log |z.im| := by
        have hu : Real.exp (Real.exp 1) ≤ |z.im| :=
          le_trans (le_max_left _ _) hhigh.le
        have : Real.exp 1 ≤ Real.log |z.im| :=
          (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) hu)).mpr hu
        linarith [Real.exp_pos 1]
      have hlogZ : Real.log |z.im| ≤ L := by
        dsimp only [L]
        have him0 : 0 < |z.im| := lt_of_lt_of_le (Real.exp_pos _)
          (le_trans (le_max_left _ _) hhigh.le)
        exact Real.log_le_log him0 (by linarith)
      have hm0 : 0 ≤ 1 / a + 1 / 10 := by positivity
      calc
        _ ≤ (Real.log |z.im|) ^ (1 / a + 1 / 10) :=
          hreg z htr (by linarith [hetaRegion]) hzre2 hz1
        _ ≤ L ^ (1 / a + 1 / 10) :=
          Real.rpow_le_rpow hlogim0.le hlogZ hm0
        _ ≤ zeroFreeRegionRegularBoundH (1 / a + 1 / 10) M₀ Z := by
          dsimp only [zeroFreeRegionRegularBoundH, L]
          exact le_max_right _ _

/-- **V-C4-4.** The chosen height-indexed zero-free record.  The
`noncomputable` choice only extracts the record whose existence was proved
above. -/
noncomputable def zeroFreeRegionDataH_of_growth
    {t₀ a B b B₀ : ℝ} (h : ZetaGrowthBound t₀ a B b B₀)
    (ha : 33 / 25 ≤ a) :
    ZeroFreeRegionDataH (1 / a + 1 / 100) (1 / a + 1 / 10) :=
  Classical.choice (nonempty_zeroFreeRegionDataH_of_growth h ha)

end ExpSums

end MoltResearch
