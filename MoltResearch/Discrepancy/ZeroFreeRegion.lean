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

/-- **The 3-4-1 product bound for `ζ`** (P4b-iii): for `σ₀ > 1` and any `t`,
`1 ≤ ‖ζ(σ₀)³ · ζ(σ₀+it)⁴ · ζ(σ₀+2it)‖` — Mathlib's
`DirichletCharacter.norm_LSeries_product_ge_one` at level `N = 1`, with the
three L-series rewritten to `riemannZeta`. This is the multiplicative form of
the classical `3 + 4cos θ + cos 2θ ≥ 0` amplification consumed by the
zero-free region (P6). -/
theorem zeta_341_prod_ge_one (σ₀ t : ℝ) (hσ : 1 < σ₀) :
    1 ≤ ‖riemannZeta (σ₀:ℂ) ^ 3
        * riemannZeta ((σ₀:ℂ) + Complex.I * t) ^ 4
        * riemannZeta ((σ₀:ℂ) + 2 * Complex.I * t)‖ := by
  have hx : (0:ℝ) < σ₀ - 1 := by linarith
  have h := DirichletCharacter.norm_LSeries_product_ge_one
    (N := 1) 1 hx t
  rw [ge_iff_le] at h
  rw [show ((1 : DirichletCharacter ℂ 1) ^ 2) = 1 from one_pow 2] at h
  rw [DirichletCharacter.LSeries_modOne_eq] at h
  rw [show (1 : ℂ) + ((σ₀ - 1 : ℝ):ℂ) = (σ₀:ℂ) from by push_cast; ring] at h
  rw [LSeries_one_eq_riemannZeta (by simp [hσ]),
    LSeries_one_eq_riemannZeta (by simp [hσ]),
    LSeries_one_eq_riemannZeta (by simp [hσ])] at h
  exact h

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

/-- **The crude zeta upper bound on the extended strip**: for
`1/2 ≤ σ ≤ 5/2` and `|t| ≥ 4`, `‖ζ(σ - it)‖ ≤ 10⁴·t²` — three pieces:
the AFE strip bound on `[1/2, 1]`, the Track-L `log/loglog` bound on
`(1, 2]`, and the trivial series bound on `(2, 5/2]`. -/
theorem zeta_norm_upper (σ t : ℝ) (hσl : 1/2 ≤ σ) (hσu : σ ≤ 5/2)
    (ht : 4 ≤ |t|) :
    ‖riemannZeta ((σ:ℂ) - Complex.I * t)‖ ≤ 10000 * t^2 := by
  have ht0 : (0:ℝ) < |t| := by linarith
  have ht2 : (0:ℝ) < t^2 := by
    have := sq_abs t
    nlinarith [ht0]
  rcases le_or_gt σ 1 with hσ1 | hσ1
  · -- the strip piece via `zeta_strip_bound` at the dyadic window of `|t|`
    set m : ℕ := ⌊|t|⌋₊ with hmdef
    have hm4 : 4 ≤ m := by
      rw [hmdef]
      exact Nat.le_floor (by exact_mod_cast ht)
    set d : ℕ := Nat.log 2 m with hddef
    have hd2 : 2 ≤ d := by
      rw [hddef]
      calc 2 = Nat.log 2 4 := by
            rw [show (4:ℕ) = 2^2 from by norm_num, Nat.log_pow (by norm_num)]
        _ ≤ Nat.log 2 m := Nat.log_mono_right hm4
    have hdlow : (2:ℝ)^d ≤ |t| := by
      have h1 : (2:ℕ)^d ≤ m := Nat.pow_log_le_self 2 (by omega)
      have h2 : ((m:ℕ):ℝ) ≤ |t| := Nat.floor_le ht0.le
      calc (2:ℝ)^d = ((2^d : ℕ):ℝ) := by push_cast; ring
        _ ≤ ((m:ℕ):ℝ) := by exact_mod_cast h1
        _ ≤ |t| := h2
    have hdhigh : |t| ≤ 2^(d+1) := by
      have h1 : m < 2^(d+1) := Nat.lt_pow_succ_log_self (by norm_num) m
      have h2 : |t| < ((m:ℕ):ℝ) + 1 := Nat.lt_floor_add_one _
      have h3 : ((m:ℕ):ℝ) + 1 ≤ ((2^(d+1) : ℕ):ℝ) := by
        exact_mod_cast h1
      calc |t| ≤ ((m:ℕ):ℝ) + 1 := h2.le
        _ ≤ ((2^(d+1) : ℕ):ℝ) := h3
        _ = (2:ℝ)^(d+1) := by push_cast; ring
    have hbound := zeta_strip_bound σ t d 0 hσl hσ1 (by omega) hdlow hdhigh
    -- crude absorption of the four terms
    have hdR : (d:ℝ) ≤ |t| := by
      have h1 : (d:ℝ) ≤ (2:ℝ)^d := by
        exact_mod_cast (Nat.lt_two_pow_self).le
      linarith [hdlow]
    have h2d1 : (2:ℝ)^(d+1) ≤ 2*|t| := by
      calc (2:ℝ)^(d+1) = 2 * 2^d := by ring
        _ ≤ 2 * |t| := by linarith [hdlow]
    have h2d4 : ((2^(d+4) : ℕ):ℝ) ≤ 16*|t| := by
      have h1 : ((2^(d+4) : ℕ):ℝ) = 16 * (2:ℝ)^d := by push_cast; ring
      rw [h1]
      linarith [hdlow]
    have hpow1 : ((2:ℝ)^(d+1)) ^ (1-σ) ≤ 2*|t| := by
      have h1 : ((2:ℝ)^(d+1)) ^ (1-σ) ≤ ((2:ℝ)^(d+1)) ^ (1:ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le ?_ (by linarith)
        have : (1:ℝ) ≤ 2^(d+1) := one_le_pow₀ (by norm_num)
        linarith
      rw [Real.rpow_one] at h1
      linarith [h2d1]
    have hpow0 : ((2:ℝ)^(d+1)) ^ (-σ) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (by linarith)
      have : (1:ℝ) ≤ 2^(d+1) := one_le_pow₀ (by norm_num)
      linarith
    have hpow4 : ((2^(d+4) : ℕ):ℝ) ^ (1-σ) ≤ 16*|t| := by
      have h0 : (1:ℝ) ≤ ((2^(d+4) : ℕ):ℝ) := by
        have : (1:ℕ) ≤ 2^(d+4) := Nat.one_le_two_pow
        exact_mod_cast this
      have h1 : ((2^(d+4) : ℕ):ℝ) ^ (1-σ) ≤ ((2^(d+4) : ℕ):ℝ) ^ (1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h0 (by linarith)
      rw [Real.rpow_one] at h1
      linarith [h2d4]
    have hsnorm : ‖((σ:ℂ) - Complex.I * t) - 1‖ ≤ 2 + |t| := by
      calc ‖((σ:ℂ) - Complex.I * t) - 1‖
          = ‖((σ - 1 : ℝ):ℂ) - Complex.I * (t:ℂ)‖ := by
            congr 1
            push_cast
            ring
        _ ≤ ‖((σ - 1 : ℝ):ℂ)‖ + ‖Complex.I * (t:ℂ)‖ := norm_sub_le _ _
        _ = |σ - 1| + |t| := by
            rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I,
              one_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ 2 + |t| := by
            have : |σ - 1| ≤ 2 := by
              rw [abs_le]
              constructor <;> linarith
            linarith
    have hsnorm_low : 1 ≤ ‖((σ:ℂ) - Complex.I * t) - 1‖ := by
      have h1 : |t| ≤ ‖((σ:ℂ) - Complex.I * t) - 1‖ := by
        have h2 : (((σ:ℂ) - Complex.I * t) - 1).im = -t := by
          simp
        calc |t| = |(((σ:ℂ) - Complex.I * t) - 1).im| := by
              rw [h2, abs_neg]
          _ ≤ ‖((σ:ℂ) - Complex.I * t) - 1‖ := Complex.abs_im_le_norm _
      linarith
    have htail : (((2^(d+4) : ℕ):ℝ) - 1) ^ (-σ) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (by linarith)
      have h1 : (32:ℕ) ≤ 2^(d+4) := by
        calc (32:ℕ) = 2^5 := by norm_num
          _ ≤ 2^(d+4) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : (32:ℝ) ≤ ((2^(d+4) : ℕ):ℝ) := by exact_mod_cast h1
      linarith
    -- assemble the four crude pieces
    have hsched : (((d-2)/(0+2) + 2^(0+7) + 3 : ℕ) : ℝ) ≤ |t| + 131 := by
      have h1 : ((d-2)/(0+2) + 2^(0+7) + 3 : ℕ) = (d-2)/2 + 131 := by norm_num
      rw [h1]
      push_cast
      have h2 : (((d-2)/2 : ℕ) : ℝ) ≤ (d:ℝ) := by
        have h3 : ((d-2)/2 : ℕ) ≤ d := by omega
        exact_mod_cast h3
      linarith [hdR]
    refine le_trans hbound ?_
    have habs : |t| ≤ t^2 / 4 * 4 := by
      nlinarith [sq_abs t, ht]
    have habs2 : |t| * |t| = t^2 := by
      rw [← sq_abs t]
      ring
    have hb1 : ((2:ℝ)^(d+1)) ^ (1-σ)
        * (((d-2)/(0+2) + 2^(0+7) + 3 : ℕ) : ℝ)
        ≤ 2*|t| * (|t| + 131) := by
      refine mul_le_mul hpow1 hsched (by positivity) (by positivity)
    have hb2 : 7 * (2:ℝ)^(d+1) * ((2:ℝ)^(d+1)) ^ (-σ) ≤ 14*|t| := by
      calc 7 * (2:ℝ)^(d+1) * ((2:ℝ)^(d+1)) ^ (-σ)
          ≤ 7 * (2:ℝ)^(d+1) * 1 := by
            refine mul_le_mul_of_nonneg_left hpow0 (by positivity)
        _ = 7 * (2:ℝ)^(d+1) := by ring
        _ ≤ 14*|t| := by linarith [h2d1]
    have hb3 : ((2^(d+4) : ℕ):ℝ) ^ (1-σ) / ‖((σ:ℂ) - Complex.I * t) - 1‖
        ≤ 16*|t| := by
      calc ((2^(d+4) : ℕ):ℝ) ^ (1-σ) / ‖((σ:ℂ) - Complex.I * t) - 1‖
          ≤ ((2^(d+4) : ℕ):ℝ) ^ (1-σ) / 1 := by
            gcongr
        _ = ((2^(d+4) : ℕ):ℝ) ^ (1-σ) := div_one _
        _ ≤ 16*|t| := hpow4
    have htail_nonneg : (0:ℝ) ≤ (((2^(d+4) : ℕ):ℝ) - 1) ^ (-σ) := by
      refine Real.rpow_nonneg ?_ _
      have h1 : (32:ℕ) ≤ 2^(d+4) := by
        calc (32:ℕ) = 2^5 := by norm_num
          _ ≤ 2^(d+4) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : (32:ℝ) ≤ ((2^(d+4) : ℕ):ℝ) := by exact_mod_cast h1
      linarith
    have hb4 : 2 * ‖((σ:ℂ) - Complex.I * t) - 1‖
        * (((2^(d+4) : ℕ):ℝ) - 1) ^ (-σ) / σ ≤ 8 + 4*|t| := by
      calc 2 * ‖((σ:ℂ) - Complex.I * t) - 1‖
          * (((2^(d+4) : ℕ):ℝ) - 1) ^ (-σ) / σ
          ≤ 2 * (2 + |t|) * 1 / σ := by
            gcongr <;> first | exact hsnorm | exact htail | positivity | linarith
        _ ≤ 2 * (2 + |t|) * 1 / (1/2) := by
            gcongr <;> first | positivity | linarith
        _ = 8 + 4*|t| := by ring
    have hfinal : 2*|t| * (|t| + 131) + 14*|t| + 16*|t| + (8 + 4*|t|)
        ≤ 10000 * t^2 := by
      nlinarith [sq_abs t, ht, sq_nonneg (|t| - 4)]
    linarith [hb1, hb2, hb3, hb4, hfinal]
  · rcases le_or_gt σ 2 with hσ2 | hσ2
    · -- the Track-L piece on `(1, 2]`
      have h1 : ‖LSeries (fun _ => 1) ((σ:ℂ) - Complex.I * t)‖
          ≤ 8192 * Real.log (|t| + 2) / Real.log (Real.log (|t| + 2)) :=
        zeta_LSeries_bound σ t hσ1 hσ2 (by linarith)
      have h2 : LSeries (fun _ => 1) ((σ:ℂ) - Complex.I * t)
          = riemannZeta ((σ:ℂ) - Complex.I * t) := by
        refine LSeries_one_eq_riemannZeta ?_
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_im]
        simp
        linarith
      rw [h2] at h1
      refine le_trans h1 ?_
      -- `loglog ≥ 1/2` and `log(|t|+2) ≤ |t|+2`
      have hlog6 : Real.exp (1/2) ≤ Real.log (|t| + 2) := by
        have ha : Real.exp (1/2) ≤ 1.65 := by
          have hb : Real.exp (1/2) * Real.exp (1/2) = Real.exp 1 := by
            rw [← Real.exp_add]
            norm_num
          nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1/2:ℝ)]
        have hc : (1.65:ℝ) ≤ Real.log 6 := by
          have hd : Real.log 6 = Real.log 2 + Real.log 3 := by
            rw [← Real.log_mul (by norm_num) (by norm_num)]
            norm_num
          have he : (1:ℝ) ≤ Real.log 3 := by
            have hf : Real.exp 1 ≤ 3 := by
              nlinarith [Real.exp_one_lt_d9]
            calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
              _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) hf
          have hg := Real.log_two_gt_d9
          rw [hd]
          linarith
        have hh : Real.log 6 ≤ Real.log (|t| + 2) :=
          Real.log_le_log (by norm_num) (by linarith)
        linarith
      have hloglog : (1/2:ℝ) ≤ Real.log (Real.log (|t| + 2)) := by
        calc (1/2:ℝ) = Real.log (Real.exp (1/2)) := (Real.log_exp _).symm
          _ ≤ Real.log (Real.log (|t| + 2)) :=
            Real.log_le_log (Real.exp_pos _) hlog6
      have hlogup : Real.log (|t| + 2) ≤ |t| + 2 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < |t| + 2 by linarith)
        linarith
      calc 8192 * Real.log (|t| + 2) / Real.log (Real.log (|t| + 2))
          ≤ 8192 * (|t| + 2) / (1/2) := by
            gcongr <;> first | positivity | linarith
        _ = 16384 * (|t| + 2) := by ring
        _ ≤ 10000 * t^2 := by
            nlinarith [sq_abs t, ht, sq_nonneg (|t| - 4)]
    · -- the trivial piece on `(2, 5/2]`
      have hre : ((σ:ℂ) - Complex.I * t).re = σ := by
        simp
      have h1 : ‖riemannZeta ((σ:ℂ) - Complex.I * t)‖ ≤ 2 := by
        have hcomp : ∀ n : ℕ, ‖1/(n:ℂ) ^ ((σ:ℂ) - Complex.I * t)‖
            ≤ (n:ℝ) ^ (-(2:ℝ)) := by
          intro n
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · subst h0
            rw [show ((0:ℕ):ℂ) = 0 from by norm_num,
              Complex.zero_cpow (by
                intro h
                rw [Complex.ext_iff] at h
                simp [hre] at h
                linarith)]
            simp [Real.zero_rpow (by norm_num : (-2:ℝ) ≠ 0)]
          · rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos h0, hre]
            rw [show (1:ℝ) / (n:ℝ) ^ σ = (n:ℝ) ^ (-σ) from by
                rw [Real.rpow_neg (Nat.cast_nonneg n), inv_eq_one_div]]
            refine Real.rpow_le_rpow_of_exponent_le ?_ (by linarith)
            exact_mod_cast h0
        have hnormsum : Summable (fun n : ℕ =>
            ‖1/(n:ℂ) ^ ((σ:ℂ) - Complex.I * t)‖) := by
          have hs := (Real.summable_one_div_nat_rpow (p := σ)).mpr
            (by linarith : 1 < σ)
          refine hs.of_nonneg_of_le (fun n => norm_nonneg _) ?_
          intro n
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · subst h0
            rw [show ((0:ℕ):ℂ) = 0 from by norm_num,
              Complex.zero_cpow (by
                intro h
                rw [Complex.ext_iff] at h
                simp [hre] at h
                linarith)]
            simp
            positivity
          · rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos h0, hre]
        have hsum2 : Summable (fun n : ℕ => (n:ℝ) ^ (-(2:ℝ))) := by
          rw [show (fun n : ℕ => ((n:ℝ)) ^ (-(2:ℝ)))
              = (fun n : ℕ => 1 / ((n:ℝ)) ^ (2:ℝ)) from funext fun n => by
              rw [Real.rpow_neg (Nat.cast_nonneg n), inv_eq_one_div]]
          exact (Real.summable_one_div_nat_rpow).mpr (by norm_num)
        rw [zeta_eq_tsum_one_div_nat_cpow (by rw [hre]; linarith)]
        refine le_trans (norm_tsum_le_tsum_norm hnormsum) ?_
        refine le_trans (hnormsum.tsum_le_tsum hcomp hsum2) ?_
        refine Real.tsum_le_of_sum_range_le (fun n => by positivity)
          (fun K => ?_)
        rcases le_or_gt K 2 with hK | hK
        · have hsub : ∑ n ∈ Finset.range K, (n:ℝ) ^ (-(2:ℝ))
              ≤ ∑ n ∈ Finset.range 2, (n:ℝ) ^ (-(2:ℝ)) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro x hx
              rw [Finset.mem_range] at *
              omega
            · intro n _ _
              positivity
          have h2 : ∑ n ∈ Finset.range 2, (n:ℝ) ^ (-(2:ℝ)) ≤ 2 := by
            rw [Finset.sum_range_succ, Finset.sum_range_one]
            norm_num
          linarith
        · have hsplit : ∑ n ∈ Finset.range K, (n:ℝ) ^ (-(2:ℝ))
              = ∑ n ∈ Finset.range 2, (n:ℝ) ^ (-(2:ℝ))
                + ∑ n ∈ Finset.Ico 2 K, (n:ℝ) ^ (-(2:ℝ)) := by
            rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
              ← Finset.sum_Ico_consecutive _ (by omega : 0 ≤ 2)
                (by omega : 2 ≤ K)]
          rw [hsplit]
          have h2 : ∑ n ∈ Finset.range 2, (n:ℝ) ^ (-(2:ℝ)) ≤ 1 := by
            rw [Finset.sum_range_succ, Finset.sum_range_one]
            norm_num
          have h3 : ∑ n ∈ Finset.Ico 2 K, (n:ℝ) ^ (-(2:ℝ)) ≤ 1 := by
            have h4 : ∑ n ∈ Finset.Ico 2 K, (n:ℝ) ^ (-(2:ℝ))
                = ∑ n ∈ Finset.Ico 2 K, (1:ℝ)/(n:ℝ)^2 := by
              refine Finset.sum_congr rfl fun n hn => ?_
              rw [Finset.mem_Ico] at hn
              rw [Real.rpow_neg (Nat.cast_nonneg n), inv_eq_one_div]
              congr 1
              rw [show ((2:ℝ)) = ((2:ℕ):ℝ) from by norm_num,
                Real.rpow_natCast]
            rw [h4]
            have h5 := sum_inv_sq_Ico_le 2 K (le_refl 2)
            linarith
          linarith
      have h16 : (16:ℝ) ≤ t^2 := by nlinarith [sq_abs t, ht]
      linarith [h1]


/-- **Point-form of the strip growth bound**: any `z` in the strip
`1/2 ≤ re ≤ 5/2` with `|im z| ≥ 4` has `‖ζ(z)‖ ≤ 10⁴·(im z)²`. -/
theorem zeta_norm_upper_pt (z : ℂ) (h1 : 1/2 ≤ z.re) (h2 : z.re ≤ 5/2)
    (him : 4 ≤ |z.im|) : ‖riemannZeta z‖ ≤ 10000 * z.im^2 := by
  have h := zeta_norm_upper z.re (-z.im) h1 h2 (by rwa [abs_neg])
  have hpt : ((z.re:ℝ):ℂ) - Complex.I * ((-z.im:ℝ):ℂ) = z := by
    apply Complex.ext <;> simp
  rw [hpt] at h
  calc ‖riemannZeta z‖ ≤ 10000 * (-z.im)^2 := h
    _ = 10000 * z.im^2 := by ring

/-- **The real-axis upper bound near the pole**: `‖ζ(σ)‖ ≤ 1 + 1/(σ-1)`
for `σ > 1` — the `n = 1` term plus the telescoped tail
(`sum_rpow_neg_Ico_le` at exponent `-(1+(σ-1))`). -/
theorem zeta_real_upper (σ : ℝ) (hσ : 1 < σ) :
    ‖riemannZeta (σ:ℂ)‖ ≤ 1 + 1/(σ - 1) := by
  have hre : ((σ:ℂ)).re = σ := Complex.ofReal_re σ
  have hcomp : ∀ n : ℕ, ‖1/(n:ℂ) ^ ((σ:ℂ))‖ ≤ (n:ℝ) ^ (-σ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      rw [show ((0:ℕ):ℂ) = 0 from by norm_num,
        Complex.zero_cpow (by
          intro h
          rw [Complex.ext_iff] at h
          simp [hre] at h
          linarith)]
      simp [Real.zero_rpow (by linarith : -σ ≠ 0)]
    · rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos h0, hre]
      rw [show (1:ℝ) / (n:ℝ) ^ σ = (n:ℝ) ^ (-σ) from by
          rw [Real.rpow_neg (Nat.cast_nonneg n), inv_eq_one_div]]
  have hnormsum : Summable (fun n : ℕ => ‖1/(n:ℂ) ^ ((σ:ℂ))‖) := by
    have hs := (Real.summable_one_div_nat_rpow (p := σ)).mpr hσ
    refine hs.of_nonneg_of_le (fun n => norm_nonneg _) ?_
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      rw [show ((0:ℕ):ℂ) = 0 from by norm_num,
        Complex.zero_cpow (by
          intro h
          rw [Complex.ext_iff] at h
          simp [hre] at h
          linarith)]
      simp
      positivity
    · rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos h0, hre]
  rw [zeta_eq_tsum_one_div_nat_cpow (by rw [hre]; linarith)]
  refine le_trans (norm_tsum_le_tsum_norm hnormsum) ?_
  refine Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _)
    (fun K => ?_)
  have hstep : ∑ n ∈ Finset.range K, ‖1/(n:ℂ) ^ ((σ:ℂ))‖
      ≤ ∑ n ∈ Finset.range K, (n:ℝ) ^ (-σ) :=
    Finset.sum_le_sum fun n _ => hcomp n
  refine le_trans hstep ?_
  have hpos : (0:ℝ) < 1/(σ-1) := by
    have : (0:ℝ) < σ - 1 := by linarith
    positivity
  rcases le_or_gt K 2 with hK | hK
  · have hsub : ∑ n ∈ Finset.range K, (n:ℝ) ^ (-σ)
        ≤ ∑ n ∈ Finset.range 2, (n:ℝ) ^ (-σ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro x hx
        rw [Finset.mem_range] at *
        omega
      · intro n _ _
        positivity
    have h2 : ∑ n ∈ Finset.range 2, (n:ℝ) ^ (-σ) ≤ 1 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one, Nat.cast_zero,
        Nat.cast_one, Real.zero_rpow (by linarith : -σ ≠ 0), Real.one_rpow]
      norm_num
    linarith
  · have hsplit : ∑ n ∈ Finset.range K, (n:ℝ) ^ (-σ)
        = ∑ n ∈ Finset.range 2, (n:ℝ) ^ (-σ)
          + ∑ n ∈ Finset.Ico 2 K, (n:ℝ) ^ (-σ) := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive _ (by omega : 0 ≤ 2)
          (by omega : 2 ≤ K)]
    rw [hsplit]
    have h2 : ∑ n ∈ Finset.range 2, (n:ℝ) ^ (-σ) ≤ 1 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one, Nat.cast_zero,
        Nat.cast_one, Real.zero_rpow (by linarith : -σ ≠ 0), Real.one_rpow]
      norm_num
    have h3 : ∑ n ∈ Finset.Ico 2 K, (n:ℝ) ^ (-σ) ≤ 1/(σ-1) := by
      have h4 : ∑ n ∈ Finset.Ico 2 K, (n:ℝ) ^ (-σ)
          = ∑ n ∈ Finset.Ico 2 K, (n:ℝ) ^ (-(1+(σ-1))) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [show -σ = -(1+(σ-1)) from by ring]
      rw [h4]
      have h5 := sum_rpow_neg_Ico_le (σ-1) 2 K (by linarith) (le_refl 2)
      rw [show ((2:ℕ):ℝ) - 1 = 1 from by norm_num, Real.one_rpow] at h5
      linarith
    linarith

/-- **The 3-4-1 lower bound**: for `1 < σ₀ ≤ 2` and `|t| ≥ 2`,
`‖ζ(σ₀+it)‖⁴ ≥ 1/((1+1/(σ₀-1))³ · 10⁴(2t)²)` — the product bound with the
real-axis factor bounded by `zeta_real_upper` and the `2t`-factor by the
strip growth bound. This feeds the Landau `M`'s without any cascade. -/
theorem zeta_norm_lower_341 (σ₀ t : ℝ) (hσ : 1 < σ₀) (hσ2 : σ₀ ≤ 2)
    (ht : 2 ≤ |t|) :
    1/((1 + 1/(σ₀-1))^3 * (10000*(2*t)^2))
      ≤ ‖riemannZeta ((σ₀:ℂ) + Complex.I * t)‖^4 := by
  have hA : ‖riemannZeta (σ₀:ℂ)‖ ≤ 1 + 1/(σ₀-1) := zeta_real_upper σ₀ hσ
  have hApos : (0:ℝ) < 1 + 1/(σ₀-1) := by
    have : (0:ℝ) < σ₀ - 1 := by linarith
    positivity
  have ht0 : (0:ℝ) < t^2 := by
    have h1 : (0:ℝ) < |t| := by linarith
    nlinarith [sq_abs t]
  have hU : ‖riemannZeta ((σ₀:ℂ) + 2 * Complex.I * t)‖ ≤ 10000*(2*t)^2 := by
    have h1 : ((σ₀:ℂ) + 2 * Complex.I * t).re = σ₀ := by simp
    have h2 : ((σ₀:ℂ) + 2 * Complex.I * t).im = 2*t := by simp
    have h3 := zeta_norm_upper_pt ((σ₀:ℂ) + 2 * Complex.I * t)
      (by rw [h1]; linarith) (by rw [h1]; linarith)
      (by rw [h2, abs_mul]; norm_num; linarith)
    rwa [h2] at h3
  have h341 := zeta_341_prod_ge_one σ₀ t hσ
  rw [norm_mul, norm_mul, norm_pow, norm_pow] at h341
  set a := ‖riemannZeta (σ₀:ℂ)‖ with ha_def
  set b := ‖riemannZeta ((σ₀:ℂ) + Complex.I * t)‖ with hb_def
  set c := ‖riemannZeta ((σ₀:ℂ) + 2 * Complex.I * t)‖ with hc_def
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hc0 : 0 ≤ c := norm_nonneg _
  have hchain : (1:ℝ) ≤ (1 + 1/(σ₀-1))^3 * b^4 * (10000*(2*t)^2) := by
    have h1 : a^3 * b^4 * c ≤ (1 + 1/(σ₀-1))^3 * b^4 * (10000*(2*t)^2) := by
      have h2 : a^3 ≤ (1 + 1/(σ₀-1))^3 := by
        exact pow_le_pow_left₀ ha0 hA 3
      have h3 : a^3 * b^4 ≤ (1 + 1/(σ₀-1))^3 * b^4 :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      calc a^3 * b^4 * c ≤ (1 + 1/(σ₀-1))^3 * b^4 * c :=
            mul_le_mul_of_nonneg_right h3 hc0
        _ ≤ (1 + 1/(σ₀-1))^3 * b^4 * (10000*(2*t)^2) :=
            mul_le_mul_of_nonneg_left hU
              (mul_nonneg (pow_nonneg hApos.le 3) (by positivity))
    linarith
  rw [div_le_iff₀ (mul_pos (pow_pos hApos 3) (by nlinarith [ht0]))]
  calc (1:ℝ) ≤ (1 + 1/(σ₀-1))^3 * b^4 * (10000*(2*t)^2) := hchain
    _ = b^4 * ((1 + 1/(σ₀-1))^3 * (10000*(2*t)^2)) := by ring


/-- **Landau's inequality instantiated at `ζ`** (P6b): at the center
`c := σ₀ + iτ` with `1 < σ₀ ≤ 3/2` and `|τ| ≥ 8`, radius `R = 1/2` and
`M := log(10⁴(|τ|+1)²/‖ζ(c)‖)`, both the designated-zero form and the
zero-free form. The ratio hypothesis comes from `zeta_norm_upper_pt`
(every point of the ball stays in the strip with `|im| ≥ 4`), the
quarter-ball re-condition from `riemannZeta_ne_zero_of_one_le_re`. -/
theorem zeta_landau_core (σ₀ τ : ℝ) (hσ1 : 1 < σ₀) (hσ2 : σ₀ ≤ 3/2)
    (hτ : 8 ≤ |τ|) :
    (∀ ρ ∈ Metric.closedBall ((σ₀:ℂ) + Complex.I * τ) (1/8),
      riemannZeta ρ = 0 →
      -(deriv riemannZeta ((σ₀:ℂ) + Complex.I * τ)
          / riemannZeta ((σ₀:ℂ) + Complex.I * τ)).re
        ≤ 32 * (Real.log (10000*(|τ|+1)^2
            / ‖riemannZeta ((σ₀:ℂ) + Complex.I * τ)‖) + 1)
          - (1/(((σ₀:ℂ) + Complex.I * τ) - ρ)).re)
    ∧ -(deriv riemannZeta ((σ₀:ℂ) + Complex.I * τ)
          / riemannZeta ((σ₀:ℂ) + Complex.I * τ)).re
        ≤ 32 * (Real.log (10000*(|τ|+1)^2
            / ‖riemannZeta ((σ₀:ℂ) + Complex.I * τ)‖) + 1) := by
  set c : ℂ := (σ₀:ℂ) + Complex.I * τ with hc_def
  have hcre : c.re = σ₀ := by rw [hc_def]; simp
  have hcim : c.im = τ := by rw [hc_def]; simp
  have hfc : riemannZeta c ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [hcre]; linarith)
  have hfc0 : (0:ℝ) < ‖riemannZeta c‖ := norm_pos_iff.mpr hfc
  have hUopen : IsOpen ({(1:ℂ)}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hf : AnalyticOnNhd ℂ riemannZeta ({(1:ℂ)}ᶜ : Set ℂ) := by
    refine DifferentiableOn.analyticOnNhd ?_ hUopen
    intro z hz
    exact (differentiableAt_riemannZeta
      (Set.mem_compl_singleton_iff.mp hz)).differentiableWithinAt
  have hball : Metric.closedBall c (1/2) ⊆ ({(1:ℂ)}ᶜ : Set ℂ) := by
    intro z hz
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h1
    have h2 : dist z c ≤ 1/2 := Metric.mem_closedBall.mp hz
    have h3 : |z.im - c.im| ≤ 1/2 := by
      calc |z.im - c.im| = |(z - c).im| := by rw [Complex.sub_im]
        _ ≤ ‖z - c‖ := Complex.abs_im_le_norm _
        _ ≤ 1/2 := by rwa [← dist_eq_norm]
    rw [h1, hcim] at h3
    rw [show (1:ℂ).im - τ = -τ from by simp, abs_neg] at h3
    linarith
  have hratio : ∀ z ∈ Metric.closedBall c (1/2),
      ‖riemannZeta z‖
        ≤ Real.exp (Real.log (10000*(|τ|+1)^2 / ‖riemannZeta c‖))
          * ‖riemannZeta c‖ := by
    intro z hz
    have hBpos : (0:ℝ) < 10000*(|τ|+1)^2 := by positivity
    rw [Real.exp_log (by positivity), div_mul_cancel₀ _ (ne_of_gt hfc0)]
    have h2 : dist z c ≤ 1/2 := Metric.mem_closedBall.mp hz
    have hre1 : |z.re - σ₀| ≤ 1/2 := by
      calc |z.re - σ₀| = |(z - c).re| := by rw [Complex.sub_re, hcre]
        _ ≤ ‖z - c‖ := Complex.abs_re_le_norm _
        _ ≤ 1/2 := by rwa [← dist_eq_norm]
    have him1 : |z.im - τ| ≤ 1/2 := by
      calc |z.im - τ| = |(z - c).im| := by rw [Complex.sub_im, hcim]
        _ ≤ ‖z - c‖ := Complex.abs_im_le_norm _
        _ ≤ 1/2 := by rwa [← dist_eq_norm]
    have hre2 := abs_le.mp hre1
    have him2 := abs_le.mp him1
    have hzre1 : 1/2 ≤ z.re := by linarith [hre2.1]
    have hzre2 : z.re ≤ 5/2 := by linarith [hre2.2]
    have hzim : 4 ≤ |z.im| := by
      rcases abs_cases τ with ⟨hτ1, hτ2⟩ | ⟨hτ1, hτ2⟩
      · rw [abs_of_nonneg (by linarith [him2.1] : (0:ℝ) ≤ z.im)]
        linarith [him2.1]
      · rw [abs_of_nonpos (by linarith [him2.2] : z.im ≤ 0)]
        linarith [him2.2]
    refine le_trans (zeta_norm_upper_pt z hzre1 hzre2 hzim) ?_
    have h8 : |z.im| ≤ |τ| + 1 := by
      calc |z.im| = |τ + (z.im - τ)| := by
            rw [show τ + (z.im - τ) = z.im from by ring]
        _ ≤ |τ| + |z.im - τ| := abs_add_le _ _
        _ ≤ |τ| + 1 := by linarith
    nlinarith [sq_abs z.im, abs_nonneg z.im, abs_nonneg τ]
  have hrecond : ∀ z ∈ Metric.closedBall c (1/2/4),
      riemannZeta z = 0 → z.re ≤ c.re := by
    intro z _ hz0
    rw [hcre]
    by_contra h
    push_neg at h
    exact absurd hz0 (riemannZeta_ne_zero_of_one_le_re (by linarith))
  constructor
  · intro ρ hρ hζρ
    have hρ' : ρ ∈ Metric.closedBall c (1/2/4) := by
      rw [show (1:ℝ)/2/4 = 1/8 from by norm_num]
      exact hρ
    have h := landau_inequality hUopen hf (by norm_num : (0:ℝ) < 1/2)
      hball hfc hratio hrecond hρ' hζρ
    calc -(deriv riemannZeta c / riemannZeta c).re
        ≤ 16 * (Real.log (10000*(|τ|+1)^2 / ‖riemannZeta c‖) + 1) / (1/2)
          - (1/(c - ρ)).re := h
      _ = 32 * (Real.log (10000*(|τ|+1)^2 / ‖riemannZeta c‖) + 1)
          - (1/(c - ρ)).re := by ring
  · have h := landau_inequality_free hUopen hf (by norm_num : (0:ℝ) < 1/2)
      hball hfc hratio hrecond
    calc -(deriv riemannZeta c / riemannZeta c).re
        ≤ 16 * (Real.log (10000*(|τ|+1)^2 / ‖riemannZeta c‖) + 1) / (1/2) := h
      _ = 32 * (Real.log (10000*(|τ|+1)^2 / ‖riemannZeta c‖) + 1) := by ring


set_option maxHeartbeats 2000000 in
open ArithmeticFunction in
/-- **The zero-free region for `ζ`** (P6c, campaign #3044): there is a
`c₀ > 0` such that every zero `β + it` of `ζ` with `|t| ≥ 8` has
`β ≤ 1 - c₀/log|t|` — the de la Vallée Poussin region, machine-checked.

The assembly: the pole bound (`zeta_logDeriv_pole_bound`), Landau's
inequality at `σ₀ + it` with the designated zero and at `σ₀ + 2it`
zero-free (`zeta_landau_core`, `M`'s bounded through the cascade-free
3-4-1 lower bound `zeta_norm_lower_341`), and the additive 3-4-1
positivity (`vonMangoldt_341_nonneg`), at `σ₀ := 1 + 1/(v²·log|t|)` where
`v` absorbs the pole constant. The classical `4 > 3` margin closes the
contradiction. -/
theorem zeta_zero_free_region :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ β t : ℝ, 8 ≤ |t| →
      riemannZeta ((β:ℂ) + Complex.I * t) = 0 →
      β ≤ 1 - c₀ / Real.log |t| := by
  classical
  obtain ⟨cp, hcp⟩ := zeta_logDeriv_pole_bound
  set P : ℝ := max cp 0 with hP_def
  have hP0 : 0 ≤ P := le_max_right _ _
  have hcpP : cp ≤ P := le_max_left _ _
  set v : ℝ := 3*P + 2002576 with hv_def
  have hv2000 : 2000 ≤ v := by rw [hv_def]; linarith
  have hv0 : (0:ℝ) < v := by linarith
  have hvsq : 2000*v ≤ v^2 := by
    have h1 := mul_nonneg (by linarith : (0:ℝ) ≤ v)
      (by linarith : (0:ℝ) ≤ v - 2000)
    have h2 : v*(v-2000) = v^2 - 2000*v := by ring
    linarith
  refine ⟨1/(9*v^2), div_pos one_pos (by nlinarith [hvsq, hv2000]), ?_⟩
  intro β t ht hzero
  have ht0 : (0:ℝ) < |t| := by linarith
  have htne : t ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht0
    exact lt_irrefl 0 ht0
  -- `L := log|t| ≥ 2`
  have hL2 : 2 ≤ Real.log |t| := by
    have h1 : Real.log 8 ≤ Real.log |t| := Real.log_le_log (by norm_num) ht
    have h2 : (2:ℝ) ≤ Real.log 8 := by
      rw [show (8:ℝ) = 2^3 from by norm_num, Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast
      linarith
    linarith
  have hL0 : (0:ℝ) < Real.log |t| := by linarith
  -- the zero is strictly left of `re = 1`
  have hβ1 : β < 1 := by
    by_contra h
    push_neg at h
    refine absurd hzero (riemannZeta_ne_zero_of_one_le_re ?_)
    simpa using h
  set x : ℝ := 1 - β with hx_def
  have hx0 : 0 < x := by rw [hx_def]; linarith
  by_contra hcon
  push_neg at hcon
  have hxc : x < (1/(9*v^2)) / Real.log |t| := by
    rw [hx_def]; linarith
  -- the parameters
  set δ : ℝ := 1/(v^2 * Real.log |t|) with hδ_def
  have hvsqL : (100:ℝ) ≤ v^2 * Real.log |t| := by nlinarith [hvsq, hv2000, hL2]
  have hvsqL0 : (0:ℝ) < v^2 * Real.log |t| := by linarith
  have hδ0 : 0 < δ := by rw [hδ_def]; positivity
  have hδ100 : δ ≤ 1/100 := by
    rw [hδ_def]
    exact one_div_le_one_div_of_le (by norm_num) hvsqL
  have hc₀100 : (1:ℝ)/(9*v^2) ≤ 1/100 := by
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith [hvsq, hv2000])
  have hx100 : x < 1/100 := by
    have h1 : (1/(9*v^2)) / Real.log |t| ≤ (1/(9*v^2)) / 2 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hL2
    have h2 : (1/(9*v^2)) / 2 ≤ (1/100)/2 := by linarith [hc₀100]
    linarith
  set σ₀ : ℝ := 1 + δ with hσ₀_def
  have hσ₀1 : 1 < σ₀ := by rw [hσ₀_def]; linarith
  have hσ₀2 : σ₀ ≤ 2 := by rw [hσ₀_def]; linarith
  have hσ₀32 : σ₀ ≤ 3/2 := by rw [hσ₀_def]; linarith
  have hσδ : σ₀ - 1 = δ := by rw [hσ₀_def]; ring
  -- points
  have hq1re : ((σ₀:ℂ) + Complex.I * t).re = σ₀ := by simp
  have hq2re : ((σ₀:ℂ) + Complex.I * (2*t:ℝ)).re = σ₀ := by simp
  have hz1 : riemannZeta ((σ₀:ℂ) + Complex.I * t) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [hq1re]; linarith)
  have hz2 : riemannZeta ((σ₀:ℂ) + Complex.I * (2*t:ℝ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [hq2re]; linarith)
  have hz1n : (0:ℝ) < ‖riemannZeta ((σ₀:ℂ) + Complex.I * t)‖ :=
    norm_pos_iff.mpr hz1
  have hz2n : (0:ℝ) < ‖riemannZeta ((σ₀:ℂ) + Complex.I * (2*t:ℝ))‖ :=
    norm_pos_iff.mpr hz2
  -- log toolkit
  have hlog1e4 : Real.log 10000 ≤ 9999 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 10000 by norm_num)
    linarith
  have hlog2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  have hlog3' : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)
    linarith
  have hlog4' : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num)
    linarith
  have hlogv : Real.log v ≤ v := by
    have := Real.log_le_sub_one_of_pos hv0
    linarith
  have hlogL : Real.log (Real.log |t|) ≤ Real.log |t| := by
    have := Real.log_le_sub_one_of_pos hL0
    linarith
  have hlogA : Real.log (1 + 1/δ) ≤ 1 + 2*v + Real.log |t| := by
    have h1δ : (0:ℝ) < 1/δ := by positivity
    have h1 : (1:ℝ) + 1/δ ≤ 2/δ := by
      have h2 : (1:ℝ) ≤ 1/δ := by
        rw [le_div_iff₀ hδ0]
        linarith
      calc (1:ℝ) + 1/δ ≤ 1/δ + 1/δ := by linarith
        _ = 2/δ := by ring
    have h3 : Real.log (1 + 1/δ) ≤ Real.log (2/δ) :=
      Real.log_le_log (by linarith) h1
    have h4 : Real.log (2/δ) = Real.log 2 - Real.log δ :=
      Real.log_div (by norm_num) (ne_of_gt hδ0)
    have h5 : Real.log δ = -Real.log (v^2 * Real.log |t|) := by
      rw [hδ_def, one_div, Real.log_inv]
    have h6 : Real.log (v^2 * Real.log |t|)
        = 2*Real.log v + Real.log (Real.log |t|) := by
      rw [Real.log_mul (by positivity) (ne_of_gt hL0), Real.log_pow]
      push_cast
      ring
    rw [h4, h5, h6] at h3
    linarith
  have hlogT1 : Real.log (|t|+1) ≤ 1 + Real.log |t| := by
    have h1 : Real.log (|t|+1) ≤ Real.log (2*|t|) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (ne_of_gt ht0)] at h1
    linarith
  have hlogT2 : Real.log (|2*t|+1) ≤ 2 + Real.log |t| := by
    have habs2t : |2*t| = 2*|t| := by
      rw [abs_mul, abs_two]
    have h1 : Real.log (|2*t|+1) ≤ Real.log (3*|t|) := by
      refine Real.log_le_log (by rw [habs2t]; linarith) ?_
      rw [habs2t]
      linarith
    rw [Real.log_mul (by norm_num) (ne_of_gt ht0)] at h1
    linarith
  have hlog2t : Real.log (2*t) = Real.log 2 + Real.log |t| := by
    rw [← Real.log_abs (2*t), abs_mul, abs_two,
      Real.log_mul (by norm_num) (ne_of_gt ht0)]
  have hlog4t : Real.log (4*t) = Real.log 4 + Real.log |t| := by
    rw [← Real.log_abs (4*t), abs_mul,
      show |(4:ℝ)| = 4 from by norm_num,
      Real.log_mul (by norm_num) (ne_of_gt ht0)]
  have h2t2 : (0:ℝ) < (2*t)^2 := by positivity
  have h4t2 : (0:ℝ) < (4*t)^2 := by positivity
  have hlogU2 : Real.log (10000*(2*t)^2) ≤ 10001 + 2*Real.log |t| := by
    rw [Real.log_mul (by norm_num) (ne_of_gt h2t2), Real.log_pow]
    push_cast
    linarith [hlog1e4, hlog2', hlog2t]
  have hlogU4 : Real.log (10000*(4*t)^2) ≤ 10005 + 2*Real.log |t| := by
    rw [Real.log_mul (by norm_num) (ne_of_gt h4t2), Real.log_pow]
    push_cast
    linarith [hlog1e4, hlog4', hlog4t]
  -- the 3-4-1 lower bounds, in log form
  have hA0 : (0:ℝ) < 1 + 1/δ := by positivity
  have hlow1 := zeta_norm_lower_341 σ₀ t hσ₀1 hσ₀2 (by linarith : 2 ≤ |t|)
  rw [hσδ] at hlow1
  have hlow2 := zeta_norm_lower_341 σ₀ (2*t) hσ₀1 hσ₀2
    (by rw [abs_mul, abs_two]; linarith : 2 ≤ |2*t|)
  rw [hσδ, show (2:ℝ)*(2*t) = 4*t from by ring] at hlow2
  have hlog_low1 : -(4*Real.log ‖riemannZeta ((σ₀:ℂ) + Complex.I * t)‖)
      ≤ 3*Real.log (1+1/δ) + Real.log (10000*(2*t)^2) := by
    have hden : (0:ℝ) < (1+1/δ)^3 * (10000*(2*t)^2) := by
      have := pow_pos hA0 3
      nlinarith [h2t2]
    have h1 : Real.log (1/((1+1/δ)^3 * (10000*(2*t)^2)))
        ≤ Real.log (‖riemannZeta ((σ₀:ℂ) + Complex.I * t)‖^4) :=
      Real.log_le_log (by positivity) hlow1
    rw [one_div, Real.log_inv,
      Real.log_mul (ne_of_gt (pow_pos hA0 3)) (by nlinarith [h2t2]),
      Real.log_pow, Real.log_pow] at h1
    push_cast at h1
    linarith
  have hlog_low2 : -(4*Real.log ‖riemannZeta ((σ₀:ℂ) + Complex.I * (2*t:ℝ))‖)
      ≤ 3*Real.log (1+1/δ) + Real.log (10000*(4*t)^2) := by
    have h1 : Real.log (1/((1+1/δ)^3 * (10000*(4*t)^2)))
        ≤ Real.log (‖riemannZeta ((σ₀:ℂ) + Complex.I * (2*t:ℝ))‖^4) := by
      exact Real.log_le_log (by positivity) hlow2
    rw [one_div, Real.log_inv,
      Real.log_mul (ne_of_gt (pow_pos hA0 3)) (by nlinarith [h4t2]),
      Real.log_pow, Real.log_pow] at h1
    simp only [Nat.cast_ofNat] at h1
    linarith
  -- the Landau M bounds
  have hM1 : Real.log (10000*(|t|+1)^2
        / ‖riemannZeta ((σ₀:ℂ) + Complex.I * t)‖)
      ≤ 12502 + 4*Real.log |t| + 2*v := by
    rw [Real.log_div (by positivity) (ne_of_gt hz1n)]
    have hup : Real.log (10000*(|t|+1)^2) ≤ 9999 + 2*(1 + Real.log |t|) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      linarith [hlog1e4, hlogT1]
    linarith [hlog_low1, hlogA, hlogU2]
  have hM2 : Real.log (10000*(|2*t|+1)^2
        / ‖riemannZeta ((σ₀:ℂ) + Complex.I * (2*t:ℝ))‖)
      ≤ 12505 + 4*Real.log |t| + 2*v := by
    rw [Real.log_div (by positivity) (ne_of_gt hz2n)]
    have hup : Real.log (10000*(|2*t|+1)^2)
        ≤ 9999 + 2*(2 + Real.log |t|) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      linarith [hlog1e4, hlogT2]
    linarith [hlog_low2, hlogA, hlogU4]
  -- the designated zero sits in the quarter ball
  have hδx8 : δ + x ≤ 1/8 := by linarith
  have hρball : ((β:ℂ) + Complex.I * t)
      ∈ Metric.closedBall ((σ₀:ℂ) + Complex.I * t) (1/8) := by
    rw [Metric.mem_closedBall, dist_eq_norm,
      show ((β:ℂ) + Complex.I * t) - ((σ₀:ℂ) + Complex.I * t)
        = (((β - σ₀ : ℝ)):ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith : β - σ₀ < 0)]
    have hsb : σ₀ - β = δ + x := by rw [hσ₀_def, hx_def]; ring
    linarith
  -- Landau at the two points
  have hlan1 := (zeta_landau_core σ₀ t hσ₀1 hσ₀32 ht).1
    ((β:ℂ) + Complex.I * t) hρball hzero
  have hlan2 := (zeta_landau_core σ₀ (2*t) hσ₀1 hσ₀32
    (by rw [abs_mul, abs_two]; linarith)).2
  -- the real part of the designated-zero term
  have hReterm : (1/(((σ₀:ℂ) + Complex.I * t) - ((β:ℂ) + Complex.I * t))).re
      = 1/(δ + x) := by
    rw [show ((σ₀:ℂ) + Complex.I * t) - ((β:ℂ) + Complex.I * t)
        = (((δ + x : ℝ)):ℂ) from by
        rw [hσ₀_def, hx_def]; push_cast; ring,
      show (1:ℂ)/(((δ + x : ℝ)):ℂ) = (((1/(δ + x) : ℝ)):ℂ) from by
        push_cast; ring]
    exact Complex.ofReal_re _
  rw [hReterm] at hlan1
  -- the pole bound
  have hpole := hcp σ₀ hσ₀1 hσ₀2
  rw [Complex.neg_re, hσδ] at hpole
  -- the additive 3-4-1 positivity, bridged to `-ζ'/ζ`
  have hbridge : ∀ s : ℂ, 1 < s.re →
      (LSeries (fun n => (vonMangoldt n : ℂ)) s).re
        = -(deriv riemannZeta s / riemannZeta s).re := by
    intro s hs
    rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_div,
      Complex.neg_re]
  have h341 := vonMangoldt_341_nonneg σ₀ t hσ₀1
  rw [show (σ₀:ℂ) + ((0:ℝ):ℂ) * Complex.I = (σ₀:ℂ) from by push_cast; ring,
    show (σ₀:ℂ) + (t:ℂ) * Complex.I = (σ₀:ℂ) + Complex.I * t from by ring,
    show (σ₀:ℂ) + ((2*t:ℝ):ℂ) * Complex.I
      = (σ₀:ℂ) + Complex.I * (2*t:ℝ) from by push_cast; ring] at h341
  rw [hbridge (σ₀:ℂ) (by simp; linarith),
    hbridge ((σ₀:ℂ) + Complex.I * t) (by rw [hq1re]; linarith),
    hbridge ((σ₀:ℂ) + Complex.I * (2*t:ℝ)) (by rw [hq2re]; linarith)] at h341
  -- the master inequality
  have hstar : 4/(δ + x) ≤ 3/δ + 3*P + 2000576
      + 640*Real.log |t| + 320*v := by
    have h1 : -(deriv riemannZeta (σ₀:ℂ) / riemannZeta (σ₀:ℂ)).re
        ≤ 1/δ + P := by linarith
    have h4x : 4/(δ + x) = 4*(1/(δ + x)) := by ring
    have h3d : 3/δ = 3*(1/δ) := by ring
    linarith [h341, hlan1, hlan2, hM1, hM2, h1, h4x, h3d]
  -- the contradiction: `4 > 3` beats the budget
  have h3δ : 3/δ = 3*(v^2 * Real.log |t|) := by
    rw [hδ_def, div_div_eq_mul_div, div_one]
  have hδx0 : (0:ℝ) < δ + x := by linarith
  have hmul1 : v^2 * Real.log |t| * δ = 1 := by
    rw [hδ_def]
    field_simp
  have hmul2 : v^2 * Real.log |t| * x < 1/9 := by
    have h1 : v^2 * Real.log |t| * x
        < v^2 * Real.log |t| * ((1/(9*v^2)) / Real.log |t|) :=
      mul_lt_mul_of_pos_left hxc hvsqL0
    have h2 : v^2 * Real.log |t| * ((1/(9*v^2)) / Real.log |t|) = 1/9 := by
      field_simp
    linarith
  have hlhs : (18/5)*(v^2 * Real.log |t|) < 4/(δ + x) := by
    rw [lt_div_iff₀ hδx0]
    nlinarith [hmul1, hmul2, hvsqL0]
  have hend : (3/5)*(v^2 * Real.log |t|)
      < 3*P + 2000576 + 640*Real.log |t| + 320*v := by
    have h1 := hstar
    rw [h3δ] at h1
    linarith
  have hnn : (0:ℝ) ≤ (3/5)*v^2 - 640 := by nlinarith [hvsq, hv2000]
  have helim : 2*((3/5)*v^2 - 640)
      ≤ Real.log |t| * ((3/5)*v^2 - 640) :=
    mul_le_mul_of_nonneg_right hL2 hnn
  have hid : Real.log |t| * ((3/5)*v^2 - 640)
      = (3/5)*(v^2 * Real.log |t|) - 640*Real.log |t| := by ring
  have hfinal : (6/5)*v^2 < 3*P + 2001856 + 320*v := by
    rw [hid] at helim
    linarith
  have hvP : 3*P = v - 2002576 := by rw [hv_def]; ring
  nlinarith [hfinal, hvsq, hv2000, hvP]

end ExpSums

end MoltResearch
