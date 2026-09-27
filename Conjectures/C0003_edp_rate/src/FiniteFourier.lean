import Conjectures.C0003_edp_rate.src.Reduction
import Conjectures.C0003_edp_rate.src.SourceBudget
import MoltResearch.Discrepancy.SpectralLaw
import MoltResearch.Discrepancy.SpectralLimit

/-!
# Finite Fourier package: the exact remaining schedule inequality

The existing exponent-box construction can be localized all the way to a finite law.  At
outer scale `x`, take spectral scale `edpAnalysisCutoff x` and the smallest modulus already
used by the qualitative construction, `modSchedule`.  The sole remaining premise is then
that the exact A4 source budget at the largest requested moment lies below `x`.

**Blocked:** this premise is not a consequence of the proposed A3 schedule.  Its left side
is primorial-sized in `modSchedule (edpAnalysisCutoff x)`, whereas the right side is only
`x`.  The theorem `finiteFourierReduction_of_schedule` below proves that this is the exact
missing inequality for the current construction; it does not install an unconditional
`FiniteFourierReductionAssumption` instance.
-/

namespace MoltResearch

open Finset MeasureTheory

/-- The spectral scale required to supply every moment in `FiniteSecondMomentBound`. -/
noncomputable def edpFourierScale (x : ℝ) : ℕ :=
  edpAnalysisCutoff x

/-- The least modulus furnished by the existing wraparound estimate at the chosen scale. -/
noncomputable def edpFourierModulus (x : ℝ) : ℕ :=
  modSchedule (edpFourierScale x)

instance (x : ℝ) : NeZero (edpFourierModulus x) := by
  unfold edpFourierModulus
  infer_instance

/-- The largest source product queried while supplying every requested moment. -/
noncomputable def edpFourierSourceBudget (x : ℝ) : ℕ :=
  spectralSourceBudget (edpFourierScale x) (edpFourierModulus x) (edpFourierScale x)

/-- Every shorter moment has source budget bounded by the terminal moment's budget. -/
theorem spectralSourceBudget_le_edpFourierSourceBudget {x : ℝ} {n : ℕ}
    (hn : n ≤ edpFourierScale x) :
    spectralSourceBudget (edpFourierScale x) (edpFourierModulus x) n
      ≤ edpFourierSourceBudget x := by
  unfold spectralSourceBudget edpFourierSourceBudget
  exact Nat.mul_le_mul_left _ hn

/-- The chosen modulus satisfies the wraparound constraint. -/
theorem edpFourierModulus_spec (x : ℝ) :
    Fintype.card (PrimeIdx (edpFourierScale x)) * Nat.log 2 (edpFourierScale x) *
        (edpFourierScale x) ^ 2
      ≤ edpFourierModulus x := by
  unfold edpFourierModulus modSchedule
  exact le_max_right _ _

/-- The chosen modulus is always strictly larger than the valuation width.  Thus A4's
maximal source-product theorem applies at every outer scale, including degenerate scales. -/
theorem log_lt_edpFourierModulus (x : ℝ) :
    Nat.log 2 (edpFourierScale x) < edpFourierModulus x := by
  change Nat.log 2 (edpFourierScale x) < modSchedule (edpFourierScale x)
  let X := edpFourierScale x
  change Nat.log 2 X < modSchedule X
  by_cases hX : 2 ≤ X
  · have hcard : 1 ≤ Fintype.card (PrimeIdx X) := by
      exact (Fintype.card_pos_iff.mpr
        ⟨⟨2, Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩⟩⟩)
    have hlog : 1 ≤ Nat.log 2 X := Nat.log_pos (by omega) hX
    have hXsq : 4 ≤ X ^ 2 := by nlinarith
    have hlarge : Nat.log 2 X <
        Fintype.card (PrimeIdx X) * Nat.log 2 X * X ^ 2 := by
      calc
        Nat.log 2 X < Nat.log 2 X * 4 := by nlinarith
        _ ≤ Nat.log 2 X * X ^ 2 := Nat.mul_le_mul_left _ hXsq
        _ ≤ Fintype.card (PrimeIdx X) * Nat.log 2 X * X ^ 2 := by
          have := Nat.mul_le_mul_right (Nat.log 2 X * X ^ 2) hcard
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this
    exact lt_of_lt_of_le hlarge (le_max_right _ _)
  · have hsmall : X = 0 ∨ X = 1 := by omega
    rcases hsmall with h0 | h1
    · simp [h0, modSchedule]
    · simp [h1, modSchedule]

/-- If the schedule inequality fails, A4's exact maximum supplies a concrete wrap-free
point whose terminal source progression lies outside the outer budget. -/
theorem exists_wrapFree_source_exceeds_of_schedule_failure {x : ℝ}
    (hfail : x < (edpFourierSourceBudget x : ℝ)) :
    ∃ a : PrimeIdx (edpFourierScale x) → ZMod (edpFourierModulus x),
      WrapFree (edpFourierScale x) (edpFourierModulus x) a ∧
        x < (dExp (edpFourierScale x) a * edpFourierScale x : ℕ) := by
  have hgreatest := spectralSourceBudget_isGreatest
    (X := edpFourierScale x) (M := edpFourierModulus x) (n := edpFourierScale x)
    (log_lt_edpFourierModulus x)
  rcases hgreatest.1 with ⟨a, ha, heq⟩
  refine ⟨a, ha, ?_⟩
  rw [← heq]
  exact hfail

/-- Source-localized version of the spectral-law moment estimate. -/
theorem integral_windowFunctional_spectralLaw_le_of_sourceBudget
    {f : ℕ → ℤ} (hs : IsSignSequence f) {B X M n : ℕ} [NeZero M]
    (hB : ∀ d m : ℕ, d > 0 →
      d * m ≤ spectralSourceBudget X M n → (apSum f d m).natAbs ≤ B)
    (hnX : n ≤ X)
    (hM : Fintype.card (PrimeIdx X) * Nat.log 2 X * X ^ 2 ≤ M) :
    ∫ ω, windowFunctional n ω ∂(spectralLaw f X M hs : Measure PrimeData)
      ≤ (B : ℝ) ^ 2 + 1 := by
  have hmap : (spectralLaw f X M hs : Measure PrimeData)
      = ((spectralPMF f X M hs).toMeasure).map (liftFreq X M) := rfl
  rw [hmap, integral_map Measurable.of_discrete.aemeasurable
    (windowFunctional n).continuous.aestronglyMeasurable]
  rw [MeasureTheory.integral_fintype (Integrable.of_finite)]
  have hterm : ∀ ξ : PrimeIdx X → ZMod M,
      ((spectralPMF f X M hs).toMeasure).real {ξ}
          • windowFunctional n (liftFreq X M ξ)
        = ‖prodDFT (smoothEval f X) ξ‖ ^ 2
          * ‖apSumC (spectralSample X M ξ) 1 n‖ ^ 2 := by
    intro ξ
    have hmass : ((spectralPMF f X M hs).toMeasure).real {ξ}
        = ‖prodDFT (smoothEval f X) ξ‖ ^ 2 := by
      unfold Measure.real
      rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton ξ)]
      unfold spectralPMF
      rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (by positivity)]
    rw [hmass, windowFunctional_apply, toCM_liftFreq, smul_eq_mul]
  rw [Finset.sum_congr rfl fun ξ _ => hterm ξ]
  have heq : ∀ ξ : PrimeIdx X → ZMod M,
      apSumC (spectralSample X M ξ) 1 n
        = ∑ j ∈ Finset.Icc 1 n, prodChar (piExp X M j) ξ := by
    intro ξ
    unfold apSumC
    rw [show Finset.Icc 1 n = Finset.Ico 1 (n + 1) from Finset.val_inj.mp rfl]
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, mul_one]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [spectralSample_apply (by omega) (by omega)]
    congr 2
    omega
  simp_rw [heq]
  exact spectral_window_bound_of_sourceBudget hs hB hnX hM

/-- If the terminal source budget fits inside the outer product cutoff at every large
scale, the existing finite spectral law discharges the Fourier interface.  This theorem
isolates the only schedule premise left by the current construction. -/
theorem finiteFourierReduction_of_schedule
    (hbudget : ∀ x : ℝ, edpRateStart < x → (edpFourierSourceBudget x : ℝ) ≤ x) :
    FiniteFourierReductionAssumption := by
  constructor
  intro f hf x hx hsmall
  let X := edpFourierScale x
  let M := edpFourierModulus x
  let B := ⌊edpTripleLogRate x⌋₊
  let ν := spectralLaw f X M hf
  let G : StochasticMultiplicative (ν : Measure PrimeData) :=
    ⟨fun ω => toCM ω, fun n => (continuous_toCM_apply n).measurable,
      ae_of_all _ toCM_completelyMultiplicativeC, ae_of_all _ toCM_unimodular⟩
  refine ⟨PrimeData, inferInstance, (ν : Measure PrimeData), ν.2, G, ?_⟩
  intro n hn
  have hnX : n ≤ X := by simpa [X, edpFourierScale] using hn
  have hx0 : 0 < x := lt_trans (by
    unfold edpRateStart
    positivity) hx
  have hlogx : Real.exp (Real.exp 1) < Real.log x := by
    rw [← Real.exp_lt_exp, Real.exp_log hx0]
    simpa [edpRateStart] using hx
  have hloglog : Real.exp 1 < Real.log (Real.log x) := by
    rw [← Real.exp_lt_exp, Real.exp_log (lt_trans (by positivity) hlogx)]
    exact hlogx
  have hlogloglog : 0 ≤ Real.log (Real.log (Real.log x)) := by
    have : 1 < Real.log (Real.log (Real.log x)) := by
      rw [← Real.exp_lt_exp, Real.exp_log (lt_trans (by positivity) hloglog)]
      exact hloglog
    linarith
  have hrate0 : 0 ≤ edpTripleLogRate x := by
    rw [edpTripleLogRate, if_neg (not_le_of_gt hx)]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg hlogloglog _)
  have hBreal : (B : ℝ) ≤ edpTripleLogRate x := by
    exact Nat.floor_le hrate0
  have hlocal : ∀ d m : ℕ, d > 0 →
      d * m ≤ spectralSourceBudget X M n → (apSum f d m).natAbs ≤ B := by
    intro d m hd hdm
    have hterminal : d * m ≤ edpFourierSourceBudget x := by
      refine le_trans hdm ?_
      simpa [X, M] using
        (spectralSourceBudget_le_edpFourierSourceBudget (x := x) hnX)
    have hterminalR : ((d * m : ℕ) : ℝ) ≤ x :=
      le_trans (by exact_mod_cast hterminal) (hbudget x hx)
    have hsmall' := hsmall d m hd (by simpa [Nat.cast_mul, mul_comm] using hterminalR)
    have habs : ((apSum f d m).natAbs : ℝ) < edpTripleLogRate x := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact hsmall'
    exact Nat.le_floor habs.le
  have hmoment : sndMomentPartialSum G n ≤ (B : ℝ) ^ 2 + 1 := by
    change ∫ ω, windowFunctional n ω ∂(ν : Measure PrimeData) ≤ (B : ℝ) ^ 2 + 1
    exact integral_windowFunctional_spectralLaw_le_of_sourceBudget hf hlocal hnX
      (by simpa [X, M] using edpFourierModulus_spec x)
  have hB0 : (0 : ℝ) ≤ B := by positivity
  nlinarith [(sq_le_sq₀ hB0 hrate0).2 hBreal]

end MoltResearch
