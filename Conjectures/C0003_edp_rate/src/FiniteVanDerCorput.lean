import Conjectures.C0003_edp_rate.src.ElliottThresholds
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5VanDerCorputProof

/-!
# Finite van der Corput package: endpoint and parameter-budget obstructions

The A6 cutoff-local Markov estimate needs the moment-fit inequality `X + H ≤ L`, where
`L` is the last index supplied by `FiniteSecondMomentBound` and `H` is the positive van der
Corput window length.  The A3 target `FinitePersistentPretentious`, however, asks for the
pretentiousness estimate at every `X` through the same endpoint `L`.

**Blocked:** at `X = L` these two requirements give `L + H ≤ L`, while
`one_le_edpVdCWindowLength` proves `1 ≤ H`.  Thus no starting scale `X₀ ≤ L` makes the A6
consumer applicable on the full interval required by the current interface.  This file
formalizes that exact failing inequality and does not install a
`FiniteVanDerCorputRateAssumption` instance.

Possible repairs are the interface changes already identified in
`Problems/edp_rate_elliott_thresholds.md`: supply Fourier moments through `L + H`, shorten
the persistent interval and check the structured consumer against it, or prove a different
scale-transfer/window lemma.  None is among A7's listed deliverables.

The A3″ schedule implements the shortened-interval repair and reserves the largest
admissible window.  The second part of this file retries the complete finite van der Corput
argument against that interface.  It isolates four remaining comparisons: the common
function-form Elliott strength must fit the cutoff-dependent modulus, frequency, distance,
and starting-scale caps.  Conditional on exactly those comparisons, the finite proof goes
through.

**Blocked (A7″):** `EDPRateElliottThresholdAssumption` gives no upper bound on its threshold
function.  Indeed a valid threshold function may be enlarged by an arbitrary real constant
without changing its theorem.  `exists_elliottThresholdAssumption_not_vdCParameterBudgetFits`
kernel-checks that, at every outer scale, one can enlarge valid threshold data past the
distance cap.  Hence the A3'' branch premise supplies the window inequality but cannot supply
the parameter-cap inequalities needed by the A6 proof.  No
`FiniteVanDerCorputRateAssumption .budgeted` instance is installed.
-/

namespace MoltResearch

/-- The schedule condition needed to apply A6's cutoff-local Elliott-window estimate at
every scale in the interval required by `FinitePersistentPretentious`. -/
def FiniteVdCWindowScheduleFits (C ε : ℝ) (L : ℕ) : Prop :=
  ∃ X₀ : ℕ, 1 ≤ X₀ ∧ X₀ ≤ L ∧
    ∀ X : ℕ, X₀ ≤ X → X ≤ L → X + edpVdCWindowLength C ε ≤ L

/-- The terminal Elliott window never fits inside a moment cutoff ending at the same scale:
its positive length forces the endpoint moment index strictly past `L`. -/
theorem edpVdC_endpoint_window_does_not_fit (C ε : ℝ) (L : ℕ) :
    ¬ L + edpVdCWindowLength C ε ≤ L := by
  have hH : 1 ≤ edpVdCWindowLength C ε := one_le_edpVdCWindowLength C ε
  omega

/-- No nonempty starting interval through `L` can satisfy the moment-fit premise consumed by
the A6 expectation and Markov estimates at every scale in that interval. -/
theorem finiteVdCWindowScheduleFits_false (C ε : ℝ) (L : ℕ) :
    ¬ FiniteVdCWindowScheduleFits C ε L := by
  rintro ⟨X₀, -, hX₀L, hfit⟩
  exact edpVdC_endpoint_window_does_not_fit C ε L (hfit L hX₀L le_rfl)

/-! ## The second-revision finite construction, conditional on the missing cap comparison -/

open MeasureTheory

/-- The four parameter comparisons needed to place the A6 van der Corput construction inside
the A3″ budgeted target.  Here `A` is the common function-form Elliott strength and
`W = max A (exp 2)` is the logarithmic-window ratio from Tao's Proposition 1.11 proof.

The active start theorem proves the subsequent moment-window fit once the last comparison is
known.  None of these four comparisons follows from the current function-form Elliott class,
which records a threshold but no growth bound for it. -/
noncomputable def EDPVdCParameterBudgetFitsAt
    [EDPRateElliottThresholdAssumption] (x : ℝ) : Prop :=
  let L := edpAnalysisCutoff x
  let C := edpTripleLogRate x ^ 2 + 1
  let ε := edpAccuracyFloor L
  let A := edpVdCElliottThreshold C ε
  let W := max A (Real.exp 2)
  A ≤ edpPretentiousModulusCap L ∧
    A ≤ edpPretentiousFrequencyCap L ∧
    A ≤ edpPretentiousDistanceCap L ∧
    ⌈W⌉₊ ≤ edpPersistentStartCap L

/-- **Missing A7″ quantitative input.**  The A6 threshold data must fit the four caps fixed
by the A3″ cutoff whenever the active large-scale branch opens.

This assumption is deliberately separate from `EDPRateElliottThresholdAssumption`: the
latter exposes a function but states no bound on its growth.  The conditional construction
below shows that this comparison, rather than the already-repaired moment endpoint, is the
remaining obstruction. -/
class EDPRateVdCParameterBudgetAssumption [EDPRateElliottThresholdAssumption] : Prop where
  fits : ∀ x : ℝ, edpBudgetedRateStart x < x → EDPVdCParameterBudgetFitsAt x

/-- The A6 and A3″ window-length definitions agree at the finite moment cap. -/
theorem edpVdCWindowLength_eq_persistentWindowLength (x ε : ℝ) :
    edpVdCWindowLength (edpTripleLogRate x ^ 2 + 1) ε =
      edpPersistentWindowLength x ε := by
  rfl

/-- At every accuracy used by the budgeted policy, the A6 shift box contains the distinct
pair `(1,2)`. -/
theorem eight_le_edpVdCWindowLength {C ε : ℝ} (hεpos : 0 < ε) (hεone : ε ≤ 1) :
    8 ≤ edpVdCWindowLength C ε := by
  unfold edpVdCWindowLength
  apply le_trans ?_ (Nat.le_max_right _ _)
  have hC : (1 : ℝ) ≤ max C 1 := le_max_right _ _
  have hdiv : (8 : ℝ) ≤ 8 / ε := by
    rw [le_div_iff₀ hεpos]
    nlinarith
  have hreal : (8 : ℝ) ≤ 8 * max C 1 / ε :=
    hdiv.trans (div_le_div_of_nonneg_right (by nlinarith) hεpos.le)
  have hceil := Nat.le_ceil (8 * max C 1 / ε)
  exact_mod_cast hreal.trans hceil

/-- Conditional completion of the second-revision finite van der Corput package.

The proof is the finite-cutoff version of `vanDerCorputAssumption_of_logElliottNonasymptotic`:
it uses the A6 local Markov theorem at every base scale whose `X + H` moment fits, and uses
the function-form maximum for all distinct shifts.  The only extra hypothesis is the named
four-cap comparison above.  This is a theorem returning the target class, not an instance,
because `EDPRateVdCParameterBudgetAssumption` is itself an unproved analytic obligation. -/
noncomputable def finiteVanDerCorputRateAssumption_of_parameterBudget
    [EDPRateElliottThresholdAssumption]
    [hbudget : EDPRateVdCParameterBudgetAssumption] :
    FiniteVanDerCorputRateAssumption .budgeted where
  pretentious := by
    intro Ω mΩ μ hprob G x hx hG
    let L : ℕ := edpAnalysisCutoff x
    let C : ℝ := edpTripleLogRate x ^ 2 + 1
    let C' : ℝ := max C 1
    let ε : ℝ := edpAccuracyFloor L
    let H : ℕ := edpVdCWindowLength C ε
    let A : ℝ := edpVdCElliottThreshold C ε
    let W : ℝ := max A (Real.exp 2)
    have hcaps := hbudget.fits x (by simpa [edpPolicyRateStart] using hx)
    change EDPVdCParameterBudgetFitsAt x at hcaps
    change A ≤ edpPretentiousModulusCap L ∧
      A ≤ edpPretentiousFrequencyCap L ∧
      A ≤ edpPretentiousDistanceCap L ∧
      ⌈W⌉₊ ≤ edpPersistentStartCap L at hcaps
    rcases hcaps with ⟨hQcap, hTcap, hBcap, hX₀cap⟩
    have hx' : edpBudgetedRateStart x < x := by
      simpa [edpPolicyRateStart] using hx
    have hεpos : 0 < ε := by
      simpa [ε, L] using edpAccuracyFloor_pos (edpAnalysisCutoff x)
    have hεone : ε ≤ 1 := by
      simpa [ε, L] using edpAccuracyFloor_le_one (edpAnalysisCutoff x)
    have hε : EDPBudgetedAccuracy x ε := by
      exact ⟨by simp [ε, L], hεone⟩
    have hC'one : (1 : ℝ) ≤ C' := le_max_right _ _
    have hC'pos : (0 : ℝ) < C' := one_pos.trans_le hC'one
    have hmoment : ∀ n : ℕ, n ≤ L → sndMomentPartialSum G n ≤ C' := by
      intro n hn
      exact (hG n (by simpa [L] using hn)).trans (le_max_left _ _)
    have hHbudget : 8 * C' / ε ≤ (H : ℝ) := by
      simpa [H, C'] using (edpVdCWindowLength_budget (C := C) (hεpos))
    have hHone : 1 ≤ H := by
      simpa [H] using one_le_edpVdCWindowLength C ε
    have hAone : (1 : ℝ) ≤ A := by
      simpa [A] using one_le_edpVdCElliottThreshold C ε
    have hAW : A ≤ W := le_max_left _ _
    have hWone : (1 : ℝ) ≤ W := hAone.trans hAW
    have hWpos : (0 : ℝ) < W := one_pos.trans_le hWone
    have hlogW : 2 ≤ Real.log W := by
      rw [Real.le_log_iff_exp_le hWpos]
      exact le_max_right A _
    have hX₀one : 1 ≤ ⌈W⌉₊ := Nat.ceil_pos.mpr hWpos
    have hHpersistent : H = edpPersistentWindowLength x ε := by
      simpa [H, C] using edpVdCWindowLength_eq_persistentWindowLength x ε
    have hstartFit :
        ⌈W⌉₊ + edpPersistentWindowLength x ε + 1 ≤ L := by
      simpa [L] using
        (edpBudgeted_window_fits_of_rateStart_lt hx' hε hX₀cap)
    change BudgetedFinitePersistentPretentious μ G x
    refine ⟨1, zero_le_one, ?_, ε, hε, ?_, A, A, A,
      hAone, hQcap, hAone, hTcap, zero_le_one.trans hAone, hBcap,
      ⌈W⌉₊, hX₀one, hX₀cap, hstartFit, ?_, ?_⟩
    · exact le_max_left _ _
    · simpa using
        (edpProbabilityLoss_mul_accuracyFloor_le
          (L := edpAnalysisCutoff x) (K := 1) (le_max_left _ _))
    · intro hQ hT hB δ hδ0 hδ1 Xpair Xzero H' Twindow hadmissible
      exact edpStructuredTerminalMaximum_le_cutoff_of_admissible
        hx' hε hQ hT hB hδ0 hδ1 ⌈W⌉₊ Xpair Xzero H' Twindow hadmissible
    · intro X hX₀X hXfit
      have hWX : W ≤ (X : ℝ) :=
        (Nat.le_ceil W).trans (by exact_mod_cast hX₀X)
      have hSlog : Real.log W - 1 ≤
          ∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n :=
        Tao2015.log_sub_one_le_sum_one_div hWone hWX
      have hShalf : Real.log W / 2 ≤
          ∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n := by
        linarith
      have hSpos : 0 <
          ∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n := by
        linarith
      have hCS : 0 < C' *
          ∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n :=
        mul_pos hC'pos hSpos
      have hfit : X + H ≤ L := by
        rw [hHpersistent]
        simpa [L] using hXfit
      have hmarkov := prob_elliottWindow_normSq_le_of_moment_cutoff
        (G := G) (C := C') (L := L) (X := X) (H := H) (W := W)
        hmoment hfit hεpos hCS
      rw [one_mul]
      refine le_trans hmarkov (measure_mono_ae ?_)
      filter_upwards [G.mul_ae, G.unimodular_ae] with ω hgmul hguni hω
      have hmarkovBudget :
          4 * C' * (∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n) / ε ≤
            (H : ℝ) *
              (∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n) / 2 := by
        calc
          4 * C' * (∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n) / ε
              = 8 * C' / ε *
                  ((∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n) / 2) := by
                    field_simp
                    ring
          _ ≤ (H : ℝ) *
                ((∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n) / 2) :=
              mul_le_mul_of_nonneg_right hHbudget (by positivity)
          _ = (H : ℝ) *
                (∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n) / 2 := by
              ring
      obtain ⟨h, hh, h', hh', hne, hcorr⟩ :=
        hguni.exists_pair_windowCorr_le hHone hSpos hω hmarkovBudget
      have hnot : ¬ NonPretentiousAt (G.g ω) A X := by
        intro hnp
        have hnp' : NonPretentiousAt (G.g ω) A ⌈((X : ℕ) : ℝ)⌉₊ := by
          rwa [Nat.ceil_natCast]
        have hEl := edpElliott_bound_of_vdCThreshold
          (C := C) (ε := ε) hh hh' hne A le_rfl hAone
          ((X : ℕ) : ℝ) W hAW hWX (G.g ω) hgmul hguni hnp'
        have hsum :
            (∑ n ∈ Finset.Ioc ⌊((X : ℕ) : ℝ) / W⌋₊ ⌊((X : ℕ) : ℝ)⌋₊,
                (G.g ω) (n + h) * (starRingEnd ℂ) ((G.g ω) (n + h')) / (n : ℂ)) =
              windowCorr (G.g ω) (Finset.Ioc ⌊(X : ℝ) / W⌋₊ X) h h' := by
          rw [Nat.floor_natCast]
          unfold windowCorr
          rfl
        rw [hsum] at hEl
        have hup :
            (∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n) / (2 * H) ≤
              edpVdCElliottTolerance C ε * Real.log W :=
          hcorr.trans hEl
        rw [edpVdCElliottTolerance] at hup
        have h2H : (0 : ℝ) < 2 * H := by positivity
        have hupper :
            (∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n) ≤
              Real.log W / 4 := by
          have hmul := (div_le_iff₀ h2H).mp hup
          calc
            (∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n)
                ≤ 1 / (8 * (H : ℝ)) * Real.log W * (2 * H) := hmul
            _ = Real.log W / 4 := by
              field_simp
              ring
        linarith
      unfold NonPretentiousAt at hnot
      push_neg at hnot
      obtain ⟨q, χ, t, hq, ht, hdist⟩ := hnot
      exact ⟨q, χ, t, hq, ht, hdist.le⟩

/-! ## Why the missing comparison cannot be obtained from A6's present interface -/

/-- Enlarging every function-form Elliott threshold preserves the A6 theorem: a value above
the enlarged threshold is also above the original threshold. -/
def EDPRateElliottThresholdAssumption.inflate
    (inst : EDPRateElliottThresholdAssumption) (R : ℝ) :
    EDPRateElliottThresholdAssumption where
  threshold b₁ b₂ ε := max (inst.threshold b₁ b₂ ε) R
  bound b₁ b₂ hb ε hε A hA hAone x w hAw hwx g hmul huni hnp :=
    inst.bound b₁ b₂ hb ε hε A ((le_max_left _ _).trans hA) hAone
      x w hAw hwx g hmul huni hnp

/-- Under the inflated valid threshold data, the A6 common strength is at least the
arbitrary inflation constant. -/
theorem le_edpVdCElliottThreshold_inflate
    (inst : EDPRateElliottThresholdAssumption) (R C ε : ℝ)
    (hεpos : 0 < ε) (hεone : ε ≤ 1) :
    letI := inst.inflate R
    R ≤ edpVdCElliottThreshold C ε := by
  letI := inst.inflate R
  rw [edpVdCElliottThreshold]
  apply le_trans ?_ (le_max_right _ _)
  have hHtwo : 2 ≤ edpVdCWindowLength C ε :=
    (by omega : 2 ≤ 8).trans (eight_le_edpVdCWindowLength hεpos hεone)
  have hp : (1, 2) ∈ edpVdCShiftPairs C ε := by
    rw [edpVdCShiftPairs, Finset.mem_product]
    exact ⟨Finset.mem_Icc.mpr ⟨le_rfl, one_le_edpVdCWindowLength C ε⟩,
      Finset.mem_Icc.mpr ⟨by omega, hHtwo⟩⟩
  have hsup := Finset.le_sup'
    (fun p : ℕ × ℕ ↦ edpElliottThreshold p.1 p.2 (edpVdCElliottTolerance C ε)) hp
  apply le_trans ?_ hsup
  change R ≤ max (inst.threshold 1 2 (edpVdCElliottTolerance C ε)) R
  exact le_max_right _ _

/-- **A7″ obstruction.**  At every outer scale and starting from any valid A6 threshold
data, there is equally valid threshold data whose common van der Corput strength exceeds the
A3'' distance cap.  Consequently the four-cap condition cannot be inferred from
`EDPRateElliottThresholdAssumption`; an explicit growth estimate synchronized with the cutoff
is still missing. -/
theorem exists_elliottThresholdAssumption_not_vdCParameterBudgetFits
    (inst : EDPRateElliottThresholdAssumption) (x : ℝ) :
    ∃ inst' : EDPRateElliottThresholdAssumption,
      letI := inst'
      ¬ EDPVdCParameterBudgetFitsAt x := by
  let R : ℝ := edpPretentiousDistanceCap (edpAnalysisCutoff x) + 1
  let inst' := inst.inflate R
  refine ⟨inst', ?_⟩
  letI := inst'
  intro hfits
  have hA := le_edpVdCElliottThreshold_inflate inst R
    (edpTripleLogRate x ^ 2 + 1)
    (edpAccuracyFloor (edpAnalysisCutoff x))
    (edpAccuracyFloor_pos (edpAnalysisCutoff x))
    (edpAccuracyFloor_le_one (edpAnalysisCutoff x))
  change EDPVdCParameterBudgetFitsAt x at hfits
  have hcap := hfits.2.2.1
  dsimp only [R] at hA
  linarith

end MoltResearch
