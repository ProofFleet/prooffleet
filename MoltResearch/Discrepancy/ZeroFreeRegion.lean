import MoltResearch.Discrepancy.LandauLemma
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Track C: the zero-free region substrate (Track R, campaign #3044, phase P4)

The `ζ'/ζ` legs of the zero-free region: the 3-4-1 positivity (the classical
`3 + 4cos θ + cos 2θ = 2(1+cos θ)² ≥ 0` amplification, through the von Mangoldt
L-series), and the pole bound `-ζ'/ζ(σ) ≤ 1/(σ-1) + c` on `(1, 2]` by the
compactness route (the ε-form interfaces permit nonconstructive constants, so
continuity of `-ζ'/ζ - 1/(σ-1)` up to `σ = 1` plus compactness of `[1,2]`
replaces Chebyshev partial summation entirely).

Together with `landau_inequality` and `zeta_strip_bound` these are the only
inputs of the region (P6); the Perron machinery is needed only by the later
prime-sum legs, not here.
-/

namespace MoltResearch

namespace ExpSums

open Complex

/-- The real part of an L-series-style term of a real arithmetic function:
`(f n / n^{σ+it}).re = f n · n^{-σ} · cos (t log n)`. -/
theorem re_term_eq (f : ℕ → ℝ) (σ t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ((f n : ℂ) / (n : ℂ) ^ ((σ:ℂ) + (t:ℂ) * Complex.I)).re
      = f n * (n:ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hnne : ((n:ℕ):ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hcpow : ((n:ℕ):ℂ) ^ ((σ:ℂ) + (t:ℂ) * Complex.I)
      = Complex.exp (((σ:ℂ) + (t:ℂ) * Complex.I) * (Real.log n : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hnne,
      show ((n:ℕ):ℂ) = (((n:ℝ)):ℂ) from by push_cast; ring,
      ← Complex.ofReal_log hn0.le]
    exact congrArg Complex.exp (mul_comm _ _)
  have hdiv : ((f n : ℂ)) / ((n:ℕ):ℂ) ^ ((σ:ℂ) + (t:ℂ) * Complex.I)
      = (f n : ℂ)
        * Complex.exp (-(((σ:ℂ) + (t:ℂ) * Complex.I) * (Real.log n : ℂ))) := by
    rw [hcpow, div_eq_mul_inv, ← Complex.exp_neg]
  rw [hdiv]
  set w : ℂ := -(((σ:ℂ) + (t:ℂ) * Complex.I) * (Real.log n : ℂ)) with hw_def
  have hwre : w.re = -(σ * Real.log n) := by
    rw [hw_def]
    simp only [Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hwim : w.im = -(t * Real.log n) := by
    rw [hw_def]
    simp only [Complex.neg_im, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  rw [show ((f n : ℂ) * Complex.exp w).re = f n * (Complex.exp w).re from by
      rw [Complex.re_ofReal_mul]]
  rw [Complex.exp_re, hwre, hwim, Real.cos_neg]
  have hexp : Real.exp (-(σ * Real.log n)) = (n:ℝ) ^ (-σ) := by
    rw [Real.rpow_def_of_pos hn0]
    congr 1
    ring
  rw [hexp]
  ring

open ArithmeticFunction in
/-- The real part of the von Mangoldt L-series at `σ + it`:
`∑ Λ(n)·n^{-σ}·cos(t log n)`. -/
theorem re_LSeries_vonMangoldt (σ t : ℝ) (hσ : 1 < σ) :
    (LSeries (fun n => (vonMangoldt n : ℂ)) ((σ:ℂ) + (t:ℂ) * Complex.I)).re
      = ∑' n : ℕ, vonMangoldt n * (n:ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
  have hre : ((σ:ℂ) + (t:ℂ) * Complex.I).re = σ := by
    simp
  have hsum : LSeriesSummable (fun n => (vonMangoldt n : ℂ))
      ((σ:ℂ) + (t:ℂ) * Complex.I) := by
    have := LSeriesSummable_vonMangoldt (s := (σ:ℂ) + (t:ℂ) * Complex.I)
      (by rw [hre]; exact hσ)
    exact this
  rw [LSeries, Complex.re_tsum hsum]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with h0 | h1
  · subst h0
    rw [LSeries.term_zero]
    simp
  · rw [LSeries.term_of_ne_zero (by omega : n ≠ 0)]
    exact re_term_eq (fun n => vonMangoldt n) σ t n h1

open ArithmeticFunction in
/-- Summability of the real von Mangoldt series with a cosine weight. -/
theorem summable_vonMangoldt_cos (σ t : ℝ) (hσ : 1 < σ) :
    Summable (fun n : ℕ =>
      vonMangoldt n * (n:ℝ) ^ (-σ) * Real.cos (t * Real.log n)) := by
  have hsum : LSeriesSummable (fun n => (vonMangoldt n : ℂ))
      ((σ:ℂ) + (t:ℂ) * Complex.I) := by
    refine LSeriesSummable_vonMangoldt ?_
    simp [hσ]
  have hre : Summable (fun n =>
      (LSeries.term (fun n => (vonMangoldt n : ℂ))
        ((σ:ℂ) + (t:ℂ) * Complex.I) n).re) :=
    (Complex.hasSum_re hsum.hasSum).summable
  refine hre.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with h0 | h1
  · subst h0
    rw [LSeries.term_zero]
    simp
  · rw [LSeries.term_of_ne_zero (by omega : n ≠ 0)]
    exact re_term_eq (fun n => vonMangoldt n) σ t n h1

open ArithmeticFunction in
/-- **The 3-4-1 positivity**: for `σ > 1`,
`3·Re L(Λ)(σ) + 4·Re L(Λ)(σ+it) + Re L(Λ)(σ+2it) ≥ 0` — termwise
`Λ(n)·n^{-σ}·(3 + 4cos θ + cos 2θ) = Λ(n)·n^{-σ}·2(1+cos θ)² ≥ 0`. -/
theorem vonMangoldt_341_nonneg (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (LSeries (fun n => (vonMangoldt n : ℂ))
        ((σ:ℂ) + ((0:ℝ):ℂ) * Complex.I)).re
      + 4 * (LSeries (fun n => (vonMangoldt n : ℂ))
        ((σ:ℂ) + (t:ℂ) * Complex.I)).re
      + (LSeries (fun n => (vonMangoldt n : ℂ))
        ((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I)).re := by
  rw [re_LSeries_vonMangoldt σ 0 hσ, re_LSeries_vonMangoldt σ t hσ,
    re_LSeries_vonMangoldt σ (2*t) hσ]
  have h1 := summable_vonMangoldt_cos σ 0 hσ
  have h2 := summable_vonMangoldt_cos σ t hσ
  have h3 := summable_vonMangoldt_cos σ (2*t) hσ
  rw [← tsum_mul_left, ← tsum_mul_left]
  rw [← (h1.mul_left 3).tsum_add (h2.mul_left 4),
    ← ((h1.mul_left 3).add (h2.mul_left 4)).tsum_add h3]
  refine tsum_nonneg fun n => ?_
  rcases Nat.eq_zero_or_pos n with h0 | hn1
  · subst h0
    simp
  · set θ : ℝ := t * Real.log n with hθ_def
    have hcos2 : Real.cos (2*t * Real.log n) = 2 * Real.cos θ ^ 2 - 1 := by
      rw [show 2*t * Real.log n = 2 * θ from by rw [hθ_def]; ring,
        Real.cos_two_mul]
    have hcos0 : Real.cos (0 * Real.log n) = 1 := by
      rw [zero_mul, Real.cos_zero]
    rw [hcos0, hcos2]
    have hΛ : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
    have hpow : (0:ℝ) ≤ (n:ℝ) ^ (-σ) := by positivity
    have hkey : 3 * (vonMangoldt n * (n:ℝ) ^ (-σ) * 1)
        + 4 * (vonMangoldt n * (n:ℝ) ^ (-σ) * Real.cos θ)
        + vonMangoldt n * (n:ℝ) ^ (-σ) * (2 * Real.cos θ ^ 2 - 1)
        = vonMangoldt n * (n:ℝ) ^ (-σ) * (2 * (1 + Real.cos θ) ^ 2) := by
      ring
    rw [hkey]
    positivity

/-- **The regularized pole-subtracted zeta**: some entire-on-`ℂ` function
agreeing with `ζ - 1/(·-1)` away from `1` (the removable singularity is filled
with the limit from `tendsto_riemannZeta_sub_one_div`; the value itself is
irrelevant downstream). -/
theorem exists_zeta_pole_reg :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      ∀ s : ℂ, s ≠ 1 → G s = riemannZeta s - 1 / (s - 1) := by
  classical
  set base : ℂ → ℂ := fun s => riemannZeta s - 1 / (s - 1) with hbase_def
  have hbase_diff : ∀ w : ℂ, w ≠ 1 → DifferentiableAt ℂ base w := by
    intro w hw
    exact (differentiableAt_riemannZeta hw).sub
      ((differentiableAt_const 1).div ((differentiableAt_id).sub_const 1)
        (sub_ne_zero.mpr hw))
  obtain ⟨l, hl⟩ : ∃ l : ℂ, Filter.Tendsto base (nhdsWithin 1 {(1:ℂ)}ᶜ)
      (nhds l) := ⟨_, tendsto_riemannZeta_sub_one_div⟩
  set G : ℂ → ℂ := Function.update base 1 l with hG_def
  have hupd : ∀ s : ℂ, s ≠ 1 → G s = base s := by
    intro s hs
    rw [hG_def, Function.update_of_ne hs]
  refine ⟨G, ?_, fun s hs => (hupd s hs).trans (by rw [hbase_def])⟩
  intro s
  rcases eq_or_ne s 1 with h1 | h1
  · subst h1
    have hpunct : ∀ᶠ w in nhdsWithin 1 {(1:ℂ)}ᶜ, DifferentiableAt ℂ G w := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hw1 : w ≠ 1 := hw
      refine (hbase_diff w hw1).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ne.mem_nhds hw1] with z hz
      exact hupd z hz
    have hcont : ContinuousAt G 1 := by
      rw [hG_def, continuousAt_update_same]
      exact hl
    exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      hpunct hcont).differentiableAt
  · refine (hbase_diff s h1).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds h1] with z hz
    exact hupd z hz

/-- **The pole bound for `-ζ'/ζ` on `(1, 2]`** (the compactness route — the
ε-form interfaces permit nonconstructive constants, so continuity of
`-ζ'/ζ - 1/(σ-1)` up to `σ = 1` on the compact `[1,2]` replaces Chebyshev
partial summation): `∃ c, -Re (ζ'/ζ)(σ) ≤ 1/(σ-1) + c`. -/
theorem zeta_logDeriv_pole_bound :
    ∃ c : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (-(deriv riemannZeta (σ:ℂ) / riemannZeta (σ:ℂ))).re ≤ 1/(σ - 1) + c := by
  classical
  obtain ⟨G, hGdiff, hGval⟩ := exists_zeta_pole_reg
  set E : ℝ → ℝ := fun σ =>
    ((-(((σ:ℂ) - 1) * deriv G (σ:ℂ)) - G (σ:ℂ))
      / (1 + ((σ:ℂ) - 1) * G (σ:ℂ))).re with hE_def
  have hden : ∀ σ : ℝ, 1 ≤ σ → σ ≤ 2 →
      (1 + ((σ:ℂ) - 1) * G (σ:ℂ)) ≠ 0 := by
    intro σ h1 h2
    rcases eq_or_lt_of_le h1 with h1' | h1'
    · rw [← h1']
      norm_num
    · have hσne : ((σ:ℂ) - 1) ≠ 0 := by
        rw [show ((σ:ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) from by push_cast; ring]
        exact_mod_cast (by linarith : σ - 1 ≠ 0)
      have h1c : ((σ:ℂ)) ≠ 1 := by
        intro h
        exact hσne (by rw [h]; ring)
      have hζne : riemannZeta (σ:ℂ) ≠ 0 := by
        refine riemannZeta_ne_zero_of_one_le_re ?_
        simp only [Complex.ofReal_re]
        linarith
      have hkey : 1 + ((σ:ℂ) - 1) * G (σ:ℂ)
          = ((σ:ℂ) - 1) * riemannZeta (σ:ℂ) := by
        rw [hGval _ h1c]
        field_simp
        ring
      rw [hkey]
      exact mul_ne_zero hσne hζne
  have hG'cont : Continuous (deriv G) := by
    exact continuous_iff_continuousAt.mpr fun z =>
      ((hGdiff.analyticAt z).deriv).continuousAt
  have hEcont : ContinuousOn E (Set.Icc (1:ℝ) 2) := by
    have hcR : Continuous (fun σ : ℝ => ((σ:ℂ) - 1)) :=
      Complex.continuous_ofReal.sub continuous_const
    have hcG : Continuous (fun σ : ℝ => G ((σ:ℂ))) :=
      hGdiff.continuous.comp Complex.continuous_ofReal
    have hcG' : Continuous (fun σ : ℝ => deriv G ((σ:ℂ))) :=
      hG'cont.comp Complex.continuous_ofReal
    rw [hE_def]
    refine Complex.continuous_re.comp_continuousOn ?_
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (((hcR.mul hcG').neg).sub hcG).continuousOn
    · exact (continuous_const.add (hcR.mul hcG)).continuousOn
    · intro σ hσ
      exact hden σ hσ.1 hσ.2
  have hbdd : BddAbove (E '' Set.Icc (1:ℝ) 2) :=
    (isCompact_Icc.image_of_continuousOn hEcont).bddAbove
  obtain ⟨c, hc⟩ := hbdd
  refine ⟨c, fun σ hσ1 hσ2 => ?_⟩
  have hEle : E σ ≤ c := hc (Set.mem_image_of_mem E ⟨hσ1.le, hσ2⟩)
  have hσne : ((σ:ℂ) - 1) ≠ 0 := by
    rw [show ((σ:ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) from by push_cast; ring]
    exact_mod_cast (by linarith : σ - 1 ≠ 0)
  have h1ne : (σ:ℂ) ≠ 1 := by
    intro h
    exact hσne (by rw [h]; ring)
  have hζne : riemannZeta (σ:ℂ) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    simp only [Complex.ofReal_re]
    linarith
  -- `ζ' = G' - 1/(s-1)²` at `s = σ`
  have hinv : HasDerivAt (fun w : ℂ => 1 / (w - 1))
      (-(1 / ((σ:ℂ) - 1) ^ 2)) (σ:ℂ) := by
    have h1 : HasDerivAt (fun w : ℂ => w - 1) 1 (σ:ℂ) :=
      (hasDerivAt_id _).sub_const 1
    have h2 := h1.inv (sub_ne_zero.mpr h1ne)
    have h2' : HasDerivAt (fun w : ℂ => 1 / (w - 1))
        (-1 / ((σ:ℂ) - 1) ^ 2) (σ:ℂ) := by
      refine h2.congr_of_eventuallyEq ?_
      filter_upwards with w
      simp [one_div]
    have h4 : -1 / ((σ:ℂ) - 1) ^ 2 = -(1 / ((σ:ℂ) - 1) ^ 2) := by ring
    rw [h4] at h2'
    exact h2'
  have hζdiff : DifferentiableAt ℂ riemannZeta (σ:ℂ) :=
    differentiableAt_riemannZeta h1ne
  have hGev : G =ᶠ[nhds (σ:ℂ)] (fun s => riemannZeta s - 1 / (s - 1)) := by
    filter_upwards [isOpen_ne.mem_nhds h1ne] with z hz
    exact hGval z hz
  have hζ' : deriv riemannZeta (σ:ℂ)
      = deriv G (σ:ℂ) - 1 / ((σ:ℂ) - 1) ^ 2 := by
    have h1 : deriv G (σ:ℂ)
        = deriv (fun s => riemannZeta s - 1 / (s - 1)) (σ:ℂ) :=
      hGev.deriv_eq
    have h2 : deriv (fun s => riemannZeta s - 1 / (s - 1)) (σ:ℂ)
        = deriv riemannZeta (σ:ℂ) - deriv (fun w : ℂ => 1 / (w - 1)) (σ:ℂ) :=
      deriv_sub hζdiff hinv.differentiableAt
    rw [h1, h2, hinv.deriv]
    ring
  have hζval : riemannZeta (σ:ℂ) = 1 / ((σ:ℂ) - 1) + G (σ:ℂ) := by
    rw [hGval _ h1ne]
    ring
  -- the identity `-ζ'/ζ - 1/(σ-1) = E σ` and its real part
  have hdenne := hden σ hσ1.le hσ2
  have hiden : -(deriv riemannZeta (σ:ℂ) / riemannZeta (σ:ℂ))
      - 1 / ((σ:ℂ) - 1)
      = (-(((σ:ℂ) - 1) * deriv G (σ:ℂ)) - G (σ:ℂ))
        / (1 + ((σ:ℂ) - 1) * G (σ:ℂ)) := by
    have hdenkey : 1 + ((σ:ℂ) - 1) * G (σ:ℂ)
        = ((σ:ℂ) - 1) * riemannZeta (σ:ℂ) := by
      rw [hGval _ h1ne]
      field_simp
      ring
    rw [hdenkey, hζ', hGval _ h1ne]
    field_simp
    ring
  have hre1 : ((1 : ℂ) / ((σ:ℂ) - 1)).re = 1 / (σ - 1) := by
    rw [show ((σ:ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) from by push_cast; ring,
      show (1:ℂ) / ((σ - 1 : ℝ) : ℂ) = (((1 / (σ - 1) : ℝ)) : ℂ) from by
        push_cast
        ring]
    exact Complex.ofReal_re _
  have hsplit : (-(deriv riemannZeta (σ:ℂ) / riemannZeta (σ:ℂ))).re
      = E σ + 1 / (σ - 1) := by
    have h1 := congrArg Complex.re hiden
    rw [Complex.sub_re, hre1] at h1
    rw [hE_def]
    simp only []
    linarith [h1]
  rw [hsplit]
  linarith

end ExpSums

end MoltResearch
