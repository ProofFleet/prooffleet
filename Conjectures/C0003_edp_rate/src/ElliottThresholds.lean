import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Elliott
import Conjectures.C0003_edp_rate.src.Reduction

/-!
# Function-form Elliott thresholds and the finite van der Corput ledger

This file carries out the threshold and moment-index audit described in
`Problems/edp_rate_elliott_thresholds.md`.  The qualitative nonasymptotic Elliott interface
hides a separate threshold behind an existential for each pair of shifts and error tolerance.
`EDPRateElliottThresholdAssumption` strengthens it by carrying that threshold as function
data, then `edpVdCElliottThreshold` takes the finite maximum required by the van der Corput
shift box.

This does not extract a numerical modulus from Tao's proof.  The function-form class is a new,
strictly stronger open obligation; no instance is declared from the existing existential
interface.

The second part localizes the expectation and Markov estimates used by the van der Corput
argument.  A window based at `n` with length `H` touches partial-sum moments at exactly `n`
and `n + H`.  Consequently an Elliott window ending at `X` requires moment control through
`X + H`; the hypotheses below record that endpoint explicitly.
-/

namespace MoltResearch

open MeasureTheory

/-! ## Function-form Elliott thresholds -/

/-- **Function-form nonasymptotic Elliott input for the EDP-rate campaign.**

Unlike `Tao2015.LogElliottNonasymptoticAssumption`, the threshold is data with visible
dependence on `(b₁, b₂, ε)`, rather than an existential selected after those parameters.
The class lives in `Type` because it carries a real-valued function.  No instance is declared:
extracting a quantitative function from the entropy-decrement/Matomäki--Radziwiłł chain is an
open analytic obligation documented in `Problems/edp_rate_elliott_thresholds.md`.
-/
class EDPRateElliottThresholdAssumption where
  threshold : ℕ → ℕ → ℝ → ℝ
  bound :
    ∀ (b₁ b₂ : ℕ), b₁ ≠ b₂ →
      ∀ ε : ℝ, 0 < ε →
        ∀ A : ℝ, threshold b₁ b₂ ε ≤ A → 1 ≤ A →
          ∀ x w : ℝ, A ≤ w → w ≤ x →
            ∀ g : ℕ → ℂ,
              CompletelyMultiplicativeC g → Unimodular g →
              NonPretentiousAt g A ⌈x⌉₊ →
              ‖∑ n ∈ Finset.Ioc ⌊x / w⌋₊ ⌊x⌋₊,
                  g (n + b₁) * (starRingEnd ℂ) (g (n + b₂)) / (n : ℂ)‖
                ≤ ε * Real.log w

/-- The named threshold function carried by `EDPRateElliottThresholdAssumption`. -/
def edpElliottThreshold [inst : EDPRateElliottThresholdAssumption]
    (b₁ b₂ : ℕ) (ε : ℝ) : ℝ :=
  inst.threshold b₁ b₂ ε

/-- The defining specification of the function-form threshold. -/
theorem edpElliott_bound_of_threshold
    [inst : EDPRateElliottThresholdAssumption]
    {b₁ b₂ : ℕ} (hb : b₁ ≠ b₂) {ε : ℝ} (hε : 0 < ε) :
    ∀ A : ℝ, edpElliottThreshold b₁ b₂ ε ≤ A → 1 ≤ A →
      ∀ x w : ℝ, A ≤ w → w ≤ x →
        ∀ g : ℕ → ℂ,
          CompletelyMultiplicativeC g → Unimodular g →
          NonPretentiousAt g A ⌈x⌉₊ →
          ‖∑ n ∈ Finset.Ioc ⌊x / w⌋₊ ⌊x⌋₊,
              g (n + b₁) * (starRingEnd ℂ) (g (n + b₂)) / (n : ℂ)‖
            ≤ ε * Real.log w := by
  exact inst.bound b₁ b₂ hb ε hε

/-- Forgetting the threshold data recovers the existing existential Elliott interface.
This direction is safe; the converse would require a noncomputable choice and would not
provide the quantitative dependence needed by a rate proof. -/
instance [inst : EDPRateElliottThresholdAssumption] :
    Tao2015.LogElliottNonasymptoticAssumption where
  bound b₁ b₂ hb ε hε :=
    ⟨inst.threshold b₁ b₂ ε, fun A hA hA1 x w hAw hwx g hmul huni hnp =>
      inst.bound b₁ b₂ hb ε hε A hA hA1 x w hAw hwx g hmul huni hnp⟩

/-- The window length used by the finite van der Corput argument.  The outer `max` makes the
function total while preserving the original choice `⌈8 max(C,1) / ε⌉₊` on valid inputs. -/
noncomputable def edpVdCWindowLength (C ε : ℝ) : ℕ :=
  max 1 ⌈8 * max C 1 / ε⌉₊

theorem one_le_edpVdCWindowLength (C ε : ℝ) :
    1 ≤ edpVdCWindowLength C ε := by
  simp [edpVdCWindowLength]

/-- On the positive-error regime used by van der Corput, totalization does not change the
original ceiling choice. -/
theorem edpVdCWindowLength_eq {C ε : ℝ} (hε : 0 < ε) :
    edpVdCWindowLength C ε = ⌈8 * max C 1 / ε⌉₊ := by
  rw [edpVdCWindowLength, max_eq_right]
  exact Nat.ceil_pos.mpr (by positivity)

/-- The Elliott tolerance paired with `edpVdCWindowLength`. -/
noncomputable def edpVdCElliottTolerance (C ε : ℝ) : ℝ :=
  1 / (8 * edpVdCWindowLength C ε)

theorem edpVdCElliottTolerance_pos (C ε : ℝ) :
    0 < edpVdCElliottTolerance C ε := by
  have hH : (0 : ℝ) < edpVdCWindowLength C ε := by
    exact_mod_cast one_le_edpVdCWindowLength C ε
  rw [edpVdCElliottTolerance]
  positivity

/-- The window length pays the Markov/pigeonhole budget `8 max(C,1) / ε`. -/
theorem edpVdCWindowLength_budget {C ε : ℝ} (hε : 0 < ε) :
    8 * max C 1 / ε ≤ (edpVdCWindowLength C ε : ℝ) := by
  have hceil : 8 * max C 1 / ε ≤ (⌈8 * max C 1 / ε⌉₊ : ℝ) := Nat.le_ceil _
  rwa [edpVdCWindowLength_eq hε]

/-- The finite square of shifts inspected by the van der Corput pigeonhole. -/
noncomputable def edpVdCShiftPairs (C ε : ℝ) : Finset (ℕ × ℕ) :=
  Finset.Icc 1 (edpVdCWindowLength C ε) ×ˢ
    Finset.Icc 1 (edpVdCWindowLength C ε)

theorem edpVdCShiftPairs_nonempty (C ε : ℝ) :
    (edpVdCShiftPairs C ε).Nonempty := by
  refine ⟨(1, 1), ?_⟩
  rw [edpVdCShiftPairs, Finset.mem_product]
  exact ⟨Finset.mem_Icc.mpr ⟨le_rfl, one_le_edpVdCWindowLength C ε⟩,
    Finset.mem_Icc.mpr ⟨le_rfl, one_le_edpVdCWindowLength C ε⟩⟩

/-- One explicit (Skolemized) strength dominates the Elliott threshold of every pair in the
finite van der Corput shift box.  The maximum also dominates `1`, as required by the
nonasymptotic interface. -/
noncomputable def edpVdCElliottThreshold
    [EDPRateElliottThresholdAssumption] (C ε : ℝ) : ℝ :=
  max 1 ((edpVdCShiftPairs C ε).sup' (edpVdCShiftPairs_nonempty C ε)
    (fun p => edpElliottThreshold p.1 p.2 (edpVdCElliottTolerance C ε)))

theorem one_le_edpVdCElliottThreshold
    [EDPRateElliottThresholdAssumption] (C ε : ℝ) :
    1 ≤ edpVdCElliottThreshold C ε := by
  simp [edpVdCElliottThreshold]

/-- Every requested pair threshold is below the common finite maximum. -/
theorem edpElliottThreshold_le_edpVdCElliottThreshold
    [EDPRateElliottThresholdAssumption]
    {C ε : ℝ} {h h' : ℕ}
    (hh : h ∈ Finset.Icc 1 (edpVdCWindowLength C ε))
    (hh' : h' ∈ Finset.Icc 1 (edpVdCWindowLength C ε)) :
    edpElliottThreshold h h' (edpVdCElliottTolerance C ε) ≤
      edpVdCElliottThreshold C ε := by
  rw [edpVdCElliottThreshold]
  have hp : (h, h') ∈ edpVdCShiftPairs C ε := by
    rw [edpVdCShiftPairs, Finset.mem_product]
    exact ⟨hh, hh'⟩
  have hle := Finset.le_sup'
    (fun p : ℕ × ℕ => edpElliottThreshold p.1 p.2 (edpVdCElliottTolerance C ε)) hp
  exact hle.trans (le_max_right _ _)

/-- The common finite maximum is a valid Elliott threshold for every distinct pair in the
van der Corput shift box.  This is the function-form replacement for the `choose A₀f` block
in `TrackCStage5VanDerCorputProof.lean`. -/
theorem edpElliott_bound_of_vdCThreshold
    [EDPRateElliottThresholdAssumption]
    {C ε : ℝ} {h h' : ℕ}
    (hh : h ∈ Finset.Icc 1 (edpVdCWindowLength C ε))
    (hh' : h' ∈ Finset.Icc 1 (edpVdCWindowLength C ε)) (hne : h ≠ h') :
    ∀ A : ℝ, edpVdCElliottThreshold C ε ≤ A → 1 ≤ A →
      ∀ x w : ℝ, A ≤ w → w ≤ x →
        ∀ g : ℕ → ℂ,
          CompletelyMultiplicativeC g → Unimodular g →
          NonPretentiousAt g A ⌈x⌉₊ →
          ‖∑ n ∈ Finset.Ioc ⌊x / w⌋₊ ⌊x⌋₊,
              g (n + h) * (starRingEnd ℂ) (g (n + h')) / (n : ℂ)‖
            ≤ edpVdCElliottTolerance C ε * Real.log w := by
  intro A hA
  apply edpElliott_bound_of_threshold hne (edpVdCElliottTolerance_pos C ε) A
  exact (edpElliottThreshold_le_edpVdCElliottThreshold hh hh').trans hA

/-! ## Finite second-moment estimates with an explicit index ledger -/

/-- A length-`H` window uses only the two partial-sum moments at `n` and `n + H`.
This is the cutoff-local version of `windowSndMoment_le`. -/
theorem windowSndMoment_le_of_two_indices
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) {C : ℝ} (n H : ℕ)
    (hn : sndMomentPartialSum G n ≤ C)
    (hnH : sndMomentPartialSum G (n + H) ≤ C) :
    ∫ ω, ‖windowSumC (G.g ω) n H‖ ^ 2 ∂μ ≤ 4 * C := by
  have hpt : ∀ ω : Ω, ‖windowSumC (G.g ω) n H‖ ^ 2
      ≤ 2 * ‖apSumC (G.g ω) 1 (n + H)‖ ^ 2 + 2 * ‖apSumC (G.g ω) 1 n‖ ^ 2 := by
    intro ω
    rw [windowSumC_eq_apSumC_sub]
    set a := apSumC (G.g ω) 1 (n + H)
    set b := apSumC (G.g ω) 1 n
    have h1 : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
    nlinarith [norm_nonneg (a - b), norm_nonneg a, norm_nonneg b,
      sq_nonneg (‖a‖ - ‖b‖)]
  have hint : Integrable
      (fun ω => 2 * ‖apSumC (G.g ω) 1 (n + H)‖ ^ 2 +
        2 * ‖apSumC (G.g ω) 1 n‖ ^ 2) μ :=
    ((G.integrable_normSq_apSumC 1 (n + H)).const_mul 2).add
      ((G.integrable_normSq_apSumC 1 n).const_mul 2)
  calc
    ∫ ω, ‖windowSumC (G.g ω) n H‖ ^ 2 ∂μ
        ≤ ∫ ω, (2 * ‖apSumC (G.g ω) 1 (n + H)‖ ^ 2 +
            2 * ‖apSumC (G.g ω) 1 n‖ ^ 2) ∂μ := by
          refine integral_mono_of_nonneg ?_ hint ?_
          · exact Filter.Eventually.of_forall fun ω => sq_nonneg _
          · exact Filter.Eventually.of_forall hpt
    _ = 2 * sndMomentPartialSum G (n + H) + 2 * sndMomentPartialSum G n := by
          rw [integral_add ((G.integrable_normSq_apSumC 1 (n + H)).const_mul 2)
            ((G.integrable_normSq_apSumC 1 n).const_mul 2),
            integral_const_mul, integral_const_mul]
          rfl
    _ ≤ 2 * C + 2 * C := by nlinarith
    _ = 4 * C := by ring

/-- Expected log-averaged squared window sums under a finite moment cutoff.

The index premise is deliberately local: for each base point `n` in `s`, it records that the
largest touched moment index `n + H` is at most `L`. -/
theorem integral_sum_div_normSq_windowSumC_le_of_moment_cutoff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) {C : ℝ} {L : ℕ}
    (hC : ∀ m : ℕ, m ≤ L → sndMomentPartialSum G m ≤ C)
    (s : Finset ℕ) (H : ℕ) (hindices : ∀ n ∈ s, n + H ≤ L) :
    ∫ ω, (∑ n ∈ s, ‖windowSumC (G.g ω) n H‖ ^ 2 / (n : ℝ)) ∂μ
      ≤ 4 * C * (∑ n ∈ s, (1 : ℝ) / n) := by
  rw [integral_finset_sum _
    (fun n _ => (G.integrable_normSq_windowSumC n H).div_const _), Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn ↦ ?_
  rw [integral_div, mul_one_div]
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp
  · have hnH := hindices n hn
    have hnL : n ≤ L := by omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    exact div_le_div_of_nonneg_right
      (windowSndMoment_le_of_two_indices G n H (hC n hnL) (hC (n + H) hnH)) hnpos.le

/-- The Markov estimate used by the finite van der Corput argument, with the same explicit
moment-index ledger as the expectation estimate. -/
theorem prob_sum_div_normSq_windowSumC_le_of_moment_cutoff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) {C : ℝ} {L : ℕ}
    (hC : ∀ m : ℕ, m ≤ L → sndMomentPartialSum G m ≤ C)
    (s : Finset ℕ) (H : ℕ) (hindices : ∀ n ∈ s, n + H ≤ L)
    {ε : ℝ} (hε : 0 < ε)
    (hCS : 0 < C * (∑ n ∈ s, (1 : ℝ) / n)) :
    ENNReal.ofReal (1 - ε) ≤
      μ {ω | ∑ n ∈ s, ‖windowSumC (G.g ω) n H‖ ^ 2 / (n : ℝ)
          ≤ 4 * C * (∑ n ∈ s, (1 : ℝ) / n) / ε} := by
  classical
  set S : ℝ := ∑ n ∈ s, (1 : ℝ) / n with hSdef
  set Z : Ω → ℝ := fun ω =>
    ∑ n ∈ s, ‖windowSumC (G.g ω) n H‖ ^ 2 / (n : ℝ) with hZdef
  set a : ℝ := 4 * C * S / ε with hadef
  have h4CS : (0 : ℝ) < 4 * C * S := by nlinarith
  have ha : 0 < a := div_pos h4CS hε
  have hZ0 : 0 ≤ᵐ[μ] Z := Filter.Eventually.of_forall fun ω =>
    Finset.sum_nonneg fun n _ => div_nonneg (pow_nonneg (norm_nonneg _) 2)
      (Nat.cast_nonneg n)
  have hmark := mul_meas_ge_le_integral_of_nonneg hZ0
    (G.integrable_sum_div_normSq_windowSumC s H) a
  have hint := integral_sum_div_normSq_windowSumC_le_of_moment_cutoff G hC s H hindices
  have hreal : μ.real {ω | a ≤ Z ω} ≤ ε := by
    have h4 : a * μ.real {ω | a ≤ Z ω} ≤ 4 * C * S := le_trans hmark hint
    have hdiv : μ.real {ω | a ≤ Z ω} ≤ 4 * C * S / a :=
      (le_div_iff₀ ha).2 (by linarith [h4, mul_comm a (μ.real {ω | a ≤ Z ω})])
    have haval : 4 * C * S / a = ε := by
      rw [hadef, div_div_eq_mul_div, mul_comm (4 * C * S) ε, mul_div_assoc,
        div_self (ne_of_gt h4CS), mul_one]
    exact hdiv.trans_eq haval
  have hmeasZ : Measurable Z := G.measurable_sum_div_normSq_windowSumC s H
  have hmeas : MeasurableSet {ω | a ≤ Z ω} := measurableSet_le measurable_const hmeasZ
  have hENN : μ {ω | a ≤ Z ω} ≤ ENNReal.ofReal ε := by
    rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hε.le]
    exact hreal
  calc
    ENNReal.ofReal (1 - ε) = 1 - ENNReal.ofReal ε := by
      rw [ENNReal.ofReal_sub _ hε.le, ENNReal.ofReal_one]
    _ ≤ 1 - μ {ω | a ≤ Z ω} := tsub_le_tsub_left hENN 1
    _ = μ ({ω | a ≤ Z ω}ᶜ) := (prob_compl_eq_one_sub hmeas).symm
    _ ≤ μ {ω | Z ω ≤ a} := by
      refine measure_mono fun ω hω => ?_
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
      exact hω.le

/-- Exact moment ledger for an Elliott window: every base index is at most `X`, and every
endpoint index is at most `X + H`.  Thus `X + H`, rather than `X`, is the largest moment
index required by the van der Corput expectation and Markov steps. -/
theorem mem_elliottWindow_moment_indices {X H n : ℕ} {W : ℝ}
    (hn : n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X) :
    n ≤ X ∧ n + H ≤ X + H := by
  rw [Finset.mem_Ioc] at hn
  omega

/-- Expected squared-window estimate on the actual Elliott window.  The single fit condition
`X + H ≤ L` is exactly what turns a moment bound through `L` into all moment values used by
the proof. -/
theorem integral_elliottWindow_normSq_le_of_moment_cutoff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) {C : ℝ} {L X H : ℕ} {W : ℝ}
    (hC : ∀ m : ℕ, m ≤ L → sndMomentPartialSum G m ≤ C)
    (hfit : X + H ≤ L) :
    ∫ ω, (∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X,
        ‖windowSumC (G.g ω) n H‖ ^ 2 / (n : ℝ)) ∂μ
      ≤ 4 * C * (∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n) := by
  apply integral_sum_div_normSq_windowSumC_le_of_moment_cutoff G hC
  intro n hn
  exact (mem_elliottWindow_moment_indices (H := H) hn).2.trans hfit

/-- Markov on the actual Elliott window, under the exact finite fit `X + H ≤ L`. -/
theorem prob_elliottWindow_normSq_le_of_moment_cutoff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) {C : ℝ} {L X H : ℕ} {W : ℝ}
    (hC : ∀ m : ℕ, m ≤ L → sndMomentPartialSum G m ≤ C)
    (hfit : X + H ≤ L) {ε : ℝ} (hε : 0 < ε)
    (hCS : 0 < C * (∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n)) :
    ENNReal.ofReal (1 - ε) ≤
      μ {ω | ∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X,
          ‖windowSumC (G.g ω) n H‖ ^ 2 / (n : ℝ)
          ≤ 4 * C * (∑ n ∈ Finset.Ioc ⌊(X : ℝ) / W⌋₊ X, (1 : ℝ) / n) / ε} := by
  apply prob_sum_div_normSq_windowSumC_le_of_moment_cutoff G hC _ H
    (fun n hn => (mem_elliottWindow_moment_indices (H := H) hn).2.trans hfit)
    hε hCS

end MoltResearch
