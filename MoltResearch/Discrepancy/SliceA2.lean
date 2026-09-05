import MoltResearch.Discrepancy.BandCapstone

/-!
# The per-slice A.2 accounting (Track R, A2-IV-0)

`slice_energy_le_of_window_energy` (E-5) prices a slice's short-interval mean square
by the line energy of the slice window, and `window_energy_le_of_low_mid` (E-4)
splits that energy into three frequency slots — low (`|ξ| < K`, unweighted), mid
(`K ≤ |ξ| ≤ L`, weighted by `‖𝓕 window‖²`) and the derivative tail.  This module
composes the two and splits the mid slot once more, at `K₂`, into the **inner band**
(left as a hypothesis in the shape the `[mrt]` A.2 capstone delivers: a weighted
energy against a measurable weight bounded by `(4H/A)²`) and the **outer band**
(discharged by `band_energy_outer_le` through the transform's decay
`‖𝓕 window‖ ≤ 2B'/(π|ξ|)`).

The point of the statement is its right-hand side.  Every slot appears with its
own constant, so the budget the inner band must meet can be *read off*: the inner
band enters as `6·Einner` against a slice target of `ε²H²·∑_{slice} 1/n`.  With
the coefficient choice `h m = 1_𝒮(m)·g m·(A/m)` the plain polynomial is
`A·F_norm`, and the capstone must therefore deliver
`∫ ‖F_norm‖²·w ≲ (H/A)²·ε²·(s/A)/6` — that is `bandBudget` at
`c₃'' = (4H/A)²·c₃_report`, not at `c₃_report`
(`Problems/tao2015_a1_r6r7_design_report.md`, §4).

Two details of the composition are worth recording.  The weight's
measurability comes from the Schwartz packaging of the window
(`HasCompactSupport.toSchwartzMap`), whose Fourier transform is continuous; and
the outer band is priced by swapping the weight for the *bounded* envelope
`(2B'/(π·max(|ξ|, K₂)))²`, which agrees with the decay on the band and keeps the
integrability lemma's global bound honest.
-/

namespace MoltResearch

open Real Finset MeasureTheory SchwartzMap ExpSums
open scoped FourierTransform ContDiff

/-- **A2-IV-0 — the per-slice energy from its four frequency slots** (Track R).

The slice mean square is at most `6` times the window energy, which is priced
slot by slot: the low band `|ξ| < K` (unweighted, times the weight's sup
`(4H/A)²`), the inner band `K ≤ |ξ| ≤ K₂` (weighted, `Einner`, the capstone's
job), the outer band `K₂ ≤ |ξ| ≤ L` (`band_energy_outer_le` through the
transform's decay), and the tail `|ξ| ≥ L` (the derivative energy), plus the
collar and Lipschitz costs of `slice_energy_le_of_window_energy`.

`hinner` is quantified over the weight because the window is built inside the
harness (`exists_slice_window'`) — a consumer only ever knows the weight is
measurable, nonnegative and at most `(4H/A)²`, which is exactly what
`band_energy_typicalS_le` and its descendants assume of it. -/
theorem slice_energy_le_of_bands (h : ℕ → ℂ) (hb : ∀ m, ‖h m‖ ≤ 1)
    (A s U H : ℕ) (hA : 1 ≤ A) (hs : 1 ≤ s) (hsA : s ≤ A) (hU : 0 < U)
    (hUH : 2*U ≤ H) (h3H : 3*H ≤ A)
    (hplat : ((U:ℝ)+1)*((A:ℝ)+s) ≤ (A:ℝ)*H)
    (hΔA : s + 2*H + 4*U ≤ A)
    (C₀ B' : ℝ) (hB'0 : 0 ≤ B')
    (hC₀ : ∀ (c : ℝ) (f : ContDiffBump c),
      f.rIn = ((A:ℝ)/H)*(Real.log (1 + (H:ℝ)/((A:ℝ)+s))
          - Real.log (1 + (U:ℝ)/A))/2 →
      f.rOut - f.rIn = ((A:ℝ)/H)
          * (min (Real.log (1 + (U:ℝ)/A)
              - Real.log (1 + (U:ℝ)/(4*((A:ℝ)+s))))
            (Real.log (1 + ((H:ℝ)+2*U)/A)
              - Real.log (1 + (H:ℝ)/((A:ℝ)+s)))) →
      ∀ u : ℝ, |deriv (⇑f) u| ≤ C₀/f.rIn)
    (hB' : C₀/(((A:ℝ)/H)*(Real.log (1 + (H:ℝ)/((A:ℝ)+s))
        - Real.log (1 + (U:ℝ)/A))/2) ≤ B')
    (K K₂ L Mtot : ℝ) (hKK₂ : K ≤ K₂) (hK₂ : 0 < K₂) (hK₂L : K₂ ≤ L)
    (J : ℕ) (hJ : L < 2^J*K₂)
    (htot : ∀ ξ : ℝ,
      ‖∑ m ∈ Finset.Ioc A (A+s+2*H+4*U),
        h m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖ ≤ Mtot)
    (Elow Einner : ℝ)
    (hlow : (∫ ξ in {ξ : ℝ | |ξ| < K},
        ‖∑ m ∈ Finset.Ioc A (A+s+2*H+4*U),
          h m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2) ≤ Elow)
    (hinner : ∀ w : ℝ → ℝ, Measurable w → (∀ ξ, 0 ≤ w ξ) →
      (∀ ξ, w ξ ≤ (4*(H:ℝ)/A)^2) →
      (∫ ξ in {ξ : ℝ | K ≤ |ξ| ∧ |ξ| ≤ K₂},
        ‖∑ m ∈ Finset.Ioc A (A+s+2*H+4*U),
          h m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)‖^2 * w ξ)
        ≤ Einner) :
    ∑ n ∈ Finset.Ioc A (A+s), ‖∑ m ∈ Finset.Ioc n (n+H), h m‖^2/n
      ≤ 6*((4*(H:ℝ)/A)^2 * Elow + Einner
            + (4*B'^2/π^2) * ((2*(A:ℝ)+1)^2
                * (Real.exp Real.pi * ((4/(K₂*(A:ℝ))) + (6/K₂^2))
                    * (∑ n ∈ Finset.Ioc A (A+s+2*H+4*U), (1:ℝ)/n)))
            + Mtot^2*((1/L^2)*((A:ℝ)/H*B'^2/π^2)))
        + (3*(U:ℝ)^2 + 3*(6*(U:ℝ)+(H:ℝ)*s/A+2)^2)
            * (∑ n ∈ Finset.Ioc A (A+s), (1:ℝ)/n)
        + 6*(800*(H:ℝ)*(A:ℝ)*B')/A := by
  classical
  have hH : 0 < H := by omega
  have hA0 : (0:ℝ) < A := by exact_mod_cast hA
  have hH0 : (0:ℝ) < H := by exact_mod_cast hH
  have hT : (0:ℝ) < (A:ℝ)/H := by positivity
  have hL : 0 < L := lt_of_lt_of_le hK₂ hK₂L
  have hKL : K ≤ L := le_trans hKK₂ hK₂L
  -- the plain phase polynomial of the slice
  set P : ℝ → ℂ := fun ξ => ∑ m ∈ Finset.Ioc A (A+s+2*H+4*U),
      h m * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) with hP_def
  have hPcont : Continuous P := continuous_char_poly _ _ _
  refine slice_energy_le_of_window_energy h hb A s U H hA hs hsA hU hUH h3H
    hplat C₀ B' hB'0 hC₀ hB' _ ?_
  intro c f hrIn hrOutsub hηs hη01 hη2
  obtain ⟨B₂, hB₂0, hB₂, hd2⟩ := exists_deriv_bound (⇑f) hηs hη2
  have hderiv : ∀ u : ℝ, |deriv (⇑f) u| ≤ B' := by
    intro u
    refine le_trans (hC₀ c f hrIn hrOutsub u) ?_
    rw [hrIn]
    exact hB'
  -- the derivative energy (the tail slot)
  have hG3c := integral_sq_norm_fourier_slice_window_le ((A:ℝ)/H) hT (⇑f)
    hηs hη2 B' hB'0 hderiv hd2
  -- the weight: nonnegative, bounded by the sup, decaying, measurable
  set w : ℝ → ℝ := fun ξ =>
    ‖𝓕 (fun v => ((f (((A:ℝ)/H)*v) : ℝ) : ℂ)) ξ‖^2 with hw_def
  have hw0 : ∀ ξ, 0 ≤ w ξ := fun ξ => by positivity
  have hwC : ∀ ξ, w ξ ≤ (4*(H:ℝ)/A)^2 := by
    intro ξ
    have h1 := norm_fourier_slice_window_le ((A:ℝ)/H) hT (⇑f) hηs.continuous
      hη01 hη2 ξ
    have h2 : (4:ℝ)/((A:ℝ)/H) = 4*(H:ℝ)/A := by field_simp
    rw [h2] at h1
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hwdecay : ∀ ξ : ℝ, ξ ≠ 0 → w ξ ≤ (2*B'/(π*|ξ|))^2 := by
    intro ξ hξ
    have h1 := norm_fourier_slice_window_decay ((A:ℝ)/H) hT (⇑f) hηs hη2 B' hB'0
      hderiv hd2 ξ hξ
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  obtain ⟨hcs, hcd⟩ := window_profile_props ((A:ℝ)/H) hT (⇑f) hηs hη2
  set G : SchwartzMap ℝ ℂ := hcs.toSchwartzMap hcd with hG_def
  have hwG : w = fun ξ => ‖(𝓕 G) ξ‖^2 := rfl
  have hwm : Measurable w := by
    rw [hwG]
    exact ((𝓕 G).continuous.norm.pow 2).measurable
  have hwC' : ∀ ξ, ‖w ξ‖ ≤ (4*(H:ℝ)/A)^2 := by
    intro ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (hw0 ξ)]
    exact hwC ξ
  -- integrability of the two slot integrands
  have hint : IntegrableOn (fun ξ => ‖P ξ‖^2 * w ξ) {ξ : ℝ | |ξ| ≤ L} := by
    refine integrableOn_norm_sq_mul_inner_band P hPcont w hwm ((4*(H:ℝ)/A)^2)
      hwC' 0 L _ ?_
    intro ξ hξ
    exact ⟨abs_nonneg ξ, hξ⟩
  have hintLow : IntegrableOn (fun ξ => ‖P ξ‖^2) {ξ : ℝ | |ξ| < K} := by
    refine integrableOn_norm_sq_inner_band P hPcont 0 K _ ?_
    intro ξ hξ
    exact ⟨abs_nonneg ξ, le_of_lt hξ⟩
  have hf0 : ∀ ξ, 0 ≤ ‖P ξ‖^2 * w ξ := fun ξ => mul_nonneg (by positivity) (hw0 ξ)
  -- the mid band splits at `K₂` into the inner band and the (open) outer band
  have hmeasO : MeasurableSet {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L} :=
    measurableSet_inner_band K₂ L
  have hmeasO' : MeasurableSet {ξ : ℝ | K₂ < |ξ| ∧ |ξ| ≤ L} :=
    (measurableSet_lt measurable_const measurable_abs).inter
      (measurableSet_le measurable_abs measurable_const)
  have hintI : IntegrableOn (fun ξ => ‖P ξ‖^2 * w ξ)
      {ξ : ℝ | K ≤ |ξ| ∧ |ξ| ≤ K₂} :=
    hint.mono_set (fun ξ hξ => le_trans hξ.2 hK₂L)
  have hintO' : IntegrableOn (fun ξ => ‖P ξ‖^2 * w ξ)
      {ξ : ℝ | K₂ < |ξ| ∧ |ξ| ≤ L} :=
    hint.mono_set (fun ξ hξ => hξ.2)
  have hintO : IntegrableOn (fun ξ => ‖P ξ‖^2 * w ξ)
      {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L} :=
    hint.mono_set (fun ξ hξ => hξ.2)
  have hsplit : (∫ ξ in {ξ : ℝ | K ≤ |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖^2 * w ξ)
      ≤ (∫ ξ in {ξ : ℝ | K ≤ |ξ| ∧ |ξ| ≤ K₂}, ‖P ξ‖^2 * w ξ)
        + ∫ ξ in {ξ : ℝ | K₂ < |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖^2 * w ξ := by
    have hcover : {ξ : ℝ | K ≤ |ξ| ∧ |ξ| ≤ L}
        ⊆ {ξ : ℝ | K ≤ |ξ| ∧ |ξ| ≤ K₂} ∪ {ξ : ℝ | K₂ < |ξ| ∧ |ξ| ≤ L} := by
      intro ξ hξ
      rcases le_or_gt |ξ| K₂ with h1 | h1
      · exact Or.inl ⟨hξ.1, h1⟩
      · exact Or.inr ⟨h1, hξ.2⟩
    have hdisj : Disjoint {ξ : ℝ | K ≤ |ξ| ∧ |ξ| ≤ K₂}
        {ξ : ℝ | K₂ < |ξ| ∧ |ξ| ≤ L} := by
      rw [Set.disjoint_left]
      intro ξ h1 h2
      exact absurd h1.2 (not_le.mpr h2.1)
    calc (∫ ξ in {ξ : ℝ | K ≤ |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖^2 * w ξ)
        ≤ ∫ ξ in {ξ : ℝ | K ≤ |ξ| ∧ |ξ| ≤ K₂} ∪ {ξ : ℝ | K₂ < |ξ| ∧ |ξ| ≤ L},
            ‖P ξ‖^2 * w ξ :=
          setIntegral_mono_set (hintI.union hintO')
            (Filter.Eventually.of_forall hf0) hcover.eventuallyLE
      _ = _ := setIntegral_union hdisj hmeasO' hintI hintO'
  -- the outer band: enlarge to the closed band, swap the weight for the decay
  -- envelope, and apply the outer-band estimate
  have houter : (∫ ξ in {ξ : ℝ | K₂ < |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖^2 * w ξ)
      ≤ (4*B'^2/π^2) * ((2*(A:ℝ)+1)^2
          * (Real.exp Real.pi * ((4/(K₂*(A:ℝ))) + (6/K₂^2))
              * (∑ n ∈ Finset.Ioc A (A+s+2*H+4*U), (1:ℝ)/n))) := by
    have h1 : (∫ ξ in {ξ : ℝ | K₂ < |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖^2 * w ξ)
        ≤ ∫ ξ in {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖^2 * w ξ :=
      setIntegral_mono_set hintO (Filter.Eventually.of_forall hf0)
        (Filter.Eventually.of_forall fun ξ hξ => ⟨le_of_lt hξ.1, hξ.2⟩)
    set w₂ : ℝ → ℝ := fun ξ => (2*B'/(π*max |ξ| K₂))^2 with hw₂_def
    have hw₂m : Measurable w₂ := by
      apply Measurable.pow_const
      apply Measurable.div measurable_const
      exact measurable_const.mul (measurable_abs.max measurable_const)
    have hw₂bdd : ∀ ξ, ‖w₂ ξ‖ ≤ (2*B'/(π*K₂))^2 := by
      intro ξ
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hmax : K₂ ≤ max |ξ| K₂ := le_max_right _ _
      have hpos : 0 < π*K₂ := by positivity
      have hle : 2*B'/(π*max |ξ| K₂) ≤ 2*B'/(π*K₂) := by
        apply div_le_div_of_nonneg_left (by positivity) hpos
        exact mul_le_mul_of_nonneg_left hmax Real.pi_pos.le
      exact pow_le_pow_left₀ (by positivity) hle 2
    have hint₂ : IntegrableOn (fun ξ => ‖P ξ‖^2 * w₂ ξ)
        {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L} :=
      integrableOn_norm_sq_mul_inner_band P hPcont w₂ hw₂m _ hw₂bdd K₂ L _
        (Set.Subset.refl _)
    have h2 : (∫ ξ in {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖^2 * w ξ)
        ≤ ∫ ξ in {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖^2 * w₂ ξ := by
      refine setIntegral_weight_mono (fun ξ => ‖P ξ‖^2) w w₂
        (fun ξ => by positivity) _ hmeasO ?_ hintO hint₂
      intro ξ hξ
      have hξ0 : ξ ≠ 0 := by
        intro h0
        have h1 : K₂ ≤ |ξ| := hξ.1
        rw [h0, abs_zero] at h1
        exact absurd h1 (not_le.mpr hK₂)
      have hd := hwdecay ξ hξ0
      have hmax : max |ξ| K₂ = |ξ| := max_eq_left hξ.1
      simp only [hw₂_def, hmax]
      exact hd
    have h3 : (∫ ξ in {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖^2 * w₂ ξ)
        = ∫ ξ in {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L},
            ‖P ξ‖^2 * (2*B'/(π*|ξ|))^2 := by
      refine setIntegral_congr_fun hmeasO ?_
      intro ξ hξ
      simp only [hw₂_def, max_eq_left hξ.1]
    have h4 := band_energy_outer_le A (s+2*H+4*U) (by omega) hΔA
      (Finset.Ioc A (A+(s+2*H+4*U))) (Finset.Subset.refl _) h hb B' K₂ L hB'0 hK₂
      J hJ
    have hIoc : A + (s + 2*H + 4*U) = A + s + 2*H + 4*U := by omega
    simp only [hIoc] at h4
    calc (∫ ξ in {ξ : ℝ | K₂ < |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖^2 * w ξ)
        ≤ ∫ ξ in {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖^2 * w ξ := h1
      _ ≤ ∫ ξ in {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖^2 * w₂ ξ := h2
      _ = ∫ ξ in {ξ : ℝ | K₂ ≤ |ξ| ∧ |ξ| ≤ L},
            ‖P ξ‖^2 * (2*B'/(π*|ξ|))^2 := h3
      _ ≤ _ := h4
  have hmid : (∫ ξ in {ξ : ℝ | K ≤ |ξ| ∧ |ξ| ≤ L}, ‖P ξ‖^2 * w ξ)
      ≤ Einner + (4*B'^2/π^2) * ((2*(A:ℝ)+1)^2
          * (Real.exp Real.pi * ((4/(K₂*(A:ℝ))) + (6/K₂^2))
              * (∑ n ∈ Finset.Ioc A (A+s+2*H+4*U), (1:ℝ)/n))) :=
    hsplit.trans (add_le_add (hinner w hwm hw0 hwC) houter)
  -- assemble the three slots
  have hwin := window_energy_le_of_low_mid h A s H U hA hH (⇑f) hηs hη2 K L Mtot
    ((A:ℝ)/H*B'^2/π^2) ((4*(H:ℝ)/A)^2) Elow _ hL hKL (by positivity)
    htot hG3c hwC hint hintLow hlow hmid
  linarith [hwin]

end MoltResearch
