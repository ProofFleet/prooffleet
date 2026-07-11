import MoltResearch.Discrepancy.MultiplicativeC

/-!
# Discrepancy: stochastic completely multiplicative functions

Language-layer module for derivation (C) (`Problems/tao2015_derivation_c.md`): the
measure-theoretic packaging of Tao's *stochastic completely multiplicative functions*
(arXiv:1509.05363, Theorem 1.9 phrasing — a probability space and a measurable family of
completely multiplicative unimodular functions), together with the second-moment functional
`𝔼|∑_{j≤n} 𝐠(j)|²` that Theorem 1.8 says is unbounded.

Design notes (from the card's gotchas):
- Randomness is load-bearing in the derivation, and Theorem 1.9's measure-theoretic phrasing is
  the Lean-friendly formulation — a `structure` bundling the family, measurability, and
  almost-everywhere pointwise properties, parametrized by an arbitrary measure (probability
  assumptions are placed on lemmas, not baked into the structure).
- The multiplicativity/unimodularity fields are `∀ᵐ` (almost everywhere), matching "for almost
  every ω, g(ω) is completely multiplicative" in Theorem 1.9.
- `ofDeterministic` embeds a single completely multiplicative unimodular `g` as a constant
  family, so deterministic statements are literal special cases of stochastic ones.
-/

namespace MoltResearch

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A stochastic completely multiplicative unimodular function (Tao 2015, Theorem 1.9 style):
a measurable family `ω ↦ g ω` of ℂ-valued sequences over a measure space, almost every member
of which is completely multiplicative and unimodular. -/
structure StochasticMultiplicative (μ : Measure Ω) where
  /-- The underlying random sequence. -/
  g : Ω → ℕ → ℂ
  /-- Coordinatewise measurability of the family. -/
  measurable : ∀ n : ℕ, Measurable fun ω => g ω n
  /-- Almost every member is completely multiplicative. -/
  mul_ae : ∀ᵐ ω ∂μ, CompletelyMultiplicativeC (g ω)
  /-- Almost every member is unimodular. -/
  unimodular_ae : ∀ᵐ ω ∂μ, Unimodular (g ω)

variable {μ : Measure Ω}

/-- Second moment of the step-one partial sums: `𝔼|∑_{j≤n} 𝐠(j)|²`.

Theorem 1.8 of Tao 2015 states that this is unbounded in `n` for every stochastic completely
multiplicative function; a *bounded* second moment is the standing hypothesis of the
van der Corput argument (Proposition 1.11).
-/
noncomputable def sndMomentPartialSum (G : StochasticMultiplicative μ) (n : ℕ) : ℝ :=
  ∫ ω, ‖apSumC (G.g ω) 1 n‖ ^ 2 ∂μ

/-- Degenerate length: the empty partial sum has second moment `0`. -/
@[simp] theorem sndMomentPartialSum_zero (G : StochasticMultiplicative μ) :
    sndMomentPartialSum G 0 = 0 := by
  simp [sndMomentPartialSum]

/-- The second moment is nonnegative (it is an integral of squares). -/
theorem sndMomentPartialSum_nonneg (G : StochasticMultiplicative μ) (n : ℕ) :
    0 ≤ sndMomentPartialSum G n :=
  integral_nonneg fun ω => by positivity

namespace StochasticMultiplicative

/-- Coordinatewise measurability extends to the partial sums. -/
theorem measurable_apSumC (G : StochasticMultiplicative μ) (d n : ℕ) :
    Measurable fun ω => apSumC (G.g ω) d n := by
  unfold apSumC
  exact Finset.measurable_sum _ fun i _ => G.measurable ((i + 1) * d)

/-- Coordinatewise measurability extends to the window sums. -/
theorem measurable_windowSumC (G : StochasticMultiplicative μ) (n H : ℕ) :
    Measurable fun ω => windowSumC (G.g ω) n H := by
  unfold windowSumC
  exact Finset.measurable_sum _ fun h _ => G.measurable (n + h)

/-- Almost every sample's step-one partial sum is bounded by its length. -/
theorem ae_norm_apSumC_le (G : StochasticMultiplicative μ) (d n : ℕ) :
    ∀ᵐ ω ∂μ, ‖apSumC (G.g ω) d n‖ ≤ n := by
  filter_upwards [G.unimodular_ae] with ω hω
  exact norm_apSumC_le _ (fun k => (hω k).le) d n

/-- The squared partial-sum norms are integrable over a finite measure (bounded measurable). -/
theorem integrable_normSq_apSumC [IsFiniteMeasure μ] (G : StochasticMultiplicative μ)
    (d n : ℕ) :
    MeasureTheory.Integrable (fun ω => ‖apSumC (G.g ω) d n‖ ^ 2) μ := by
  refine (MeasureTheory.integrable_const ((n : ℝ) ^ 2)).mono'
    ((((G.measurable_apSumC d n).norm).pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [G.ae_norm_apSumC_le d n] with ω hω
  have h0 : (0 : ℝ) ≤ ‖apSumC (G.g ω) d n‖ := norm_nonneg _
  simpa [abs_of_nonneg (pow_nonneg h0 2)] using pow_le_pow_left₀ h0 hω 2

/-- Almost every sample's window sum is bounded by the window length. -/
theorem ae_norm_windowSumC_le (G : StochasticMultiplicative μ) (n H : ℕ) :
    ∀ᵐ ω ∂μ, ‖windowSumC (G.g ω) n H‖ ≤ H := by
  filter_upwards [G.unimodular_ae] with ω hω
  exact norm_windowSumC_le _ (fun k => (hω k).le) n H

/-- The squared window-sum norms are integrable over a finite measure (bounded measurable). -/
theorem integrable_normSq_windowSumC [IsFiniteMeasure μ] (G : StochasticMultiplicative μ)
    (n H : ℕ) :
    MeasureTheory.Integrable (fun ω => ‖windowSumC (G.g ω) n H‖ ^ 2) μ := by
  refine (MeasureTheory.integrable_const ((H : ℝ) ^ 2)).mono'
    ((((G.measurable_windowSumC n H).norm).pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [G.ae_norm_windowSumC_le n H] with ω hω
  have h0 : (0 : ℝ) ≤ ‖windowSumC (G.g ω) n H‖ := norm_nonneg _
  simpa [abs_of_nonneg (pow_nonneg h0 2)] using pow_le_pow_left₀ h0 hω 2

end StochasticMultiplicative

/-- **Van der Corput input** (Tao 2015 §3, first step): if the partial-sum second moments are
uniformly bounded by `C`, every window second moment is bounded by `4·C` — the window sum is
an increment of partial sums, and `‖a − b‖² ≤ 2‖a‖² + 2‖b‖²`.

This is the standing bound the van der Corput expansion contradicts: the squared window sum
expands into `H` diagonal terms plus shift correlations, so a bound independent of `H` forces
large negative correlations. -/
theorem windowSndMoment_le [IsProbabilityMeasure μ] (G : StochasticMultiplicative μ)
    {C : ℝ} (hC : ∀ m : ℕ, sndMomentPartialSum G m ≤ C) (n H : ℕ) :
    ∫ ω, ‖windowSumC (G.g ω) n H‖ ^ 2 ∂μ ≤ 4 * C := by
  have hpt : ∀ ω : Ω, ‖windowSumC (G.g ω) n H‖ ^ 2
      ≤ 2 * ‖apSumC (G.g ω) 1 (n + H)‖ ^ 2 + 2 * ‖apSumC (G.g ω) 1 n‖ ^ 2 := by
    intro ω
    rw [windowSumC_eq_apSumC_sub]
    set a := apSumC (G.g ω) 1 (n + H)
    set b := apSumC (G.g ω) 1 n
    have h1 : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
    nlinarith [norm_nonneg (a - b), norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖ - ‖b‖)]
  have hint : MeasureTheory.Integrable
      (fun ω => 2 * ‖apSumC (G.g ω) 1 (n + H)‖ ^ 2 + 2 * ‖apSumC (G.g ω) 1 n‖ ^ 2) μ :=
    ((G.integrable_normSq_apSumC 1 (n + H)).const_mul 2).add
      ((G.integrable_normSq_apSumC 1 n).const_mul 2)
  calc ∫ ω, ‖windowSumC (G.g ω) n H‖ ^ 2 ∂μ
      ≤ ∫ ω, (2 * ‖apSumC (G.g ω) 1 (n + H)‖ ^ 2 + 2 * ‖apSumC (G.g ω) 1 n‖ ^ 2) ∂μ := by
        refine MeasureTheory.integral_mono_of_nonneg ?_ hint ?_
        · exact Filter.Eventually.of_forall fun ω => sq_nonneg _
        · exact Filter.Eventually.of_forall hpt
    _ = 2 * sndMomentPartialSum G (n + H) + 2 * sndMomentPartialSum G n := by
        rw [MeasureTheory.integral_add ((G.integrable_normSq_apSumC 1 (n + H)).const_mul 2)
          ((G.integrable_normSq_apSumC 1 n).const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
        rfl
    _ ≤ 2 * C + 2 * C := by
        have h1 := hC (n + H)
        have h2 := hC n
        nlinarith
    _ = 4 * C := by ring

/-- **Forced correlations** (Tao 2015 §3): under a uniform second-moment bound `C`, the
integrated off-diagonal shift correlations over any window of length `H` are at most
`4·C − H` — large and *negative* once `H > 4C`.

This is `windowSndMoment_le` minus the diagonal contribution of the van der Corput expansion
(`Unimodular.normSq_windowSumC`); the averaging/pigeonhole step of Proposition 1.11 starts
from here. -/
theorem integral_offdiag_windowSumC_le [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) {C : ℝ} (hC : ∀ m : ℕ, sndMomentPartialSum G m ≤ C)
    (n H : ℕ) :
    ∫ ω, (∑ h ∈ Finset.Icc 1 H, ∑ h' ∈ (Finset.Icc 1 H).erase h,
        ((G.g ω) (n + h) * (starRingEnd ℂ) ((G.g ω) (n + h'))).re) ∂μ ≤ 4 * C - H := by
  have hae : (fun ω => ∑ h ∈ Finset.Icc 1 H, ∑ h' ∈ (Finset.Icc 1 H).erase h,
        ((G.g ω) (n + h) * (starRingEnd ℂ) ((G.g ω) (n + h'))).re)
      =ᵐ[μ] fun ω => ‖windowSumC (G.g ω) n H‖ ^ 2 - H := by
    filter_upwards [G.unimodular_ae] with ω hω
    rw [hω.normSq_windowSumC n H]
    ring
  rw [MeasureTheory.integral_congr_ae hae,
    MeasureTheory.integral_sub (G.integrable_normSq_windowSumC n H)
      (MeasureTheory.integrable_const _)]
  have hconst : ∫ (_ : Ω), (H : ℝ) ∂μ = H := by simp
  rw [hconst]
  have hw := windowSndMoment_le G hC n H
  linarith

namespace StochasticMultiplicative

/-- Measurability of the log-averaged squared window sums. -/
theorem measurable_sum_div_normSq_windowSumC (G : StochasticMultiplicative μ)
    (s : Finset ℕ) (H : ℕ) :
    Measurable fun ω => ∑ n ∈ s, ‖windowSumC (G.g ω) n H‖ ^ 2 / (n : ℝ) :=
  Finset.measurable_sum _ fun n _ =>
    (((G.measurable_windowSumC n H).norm.pow_const 2).div_const _)

/-- Integrability of the log-averaged squared window sums over a finite measure. -/
theorem integrable_sum_div_normSq_windowSumC [IsFiniteMeasure μ]
    (G : StochasticMultiplicative μ) (s : Finset ℕ) (H : ℕ) :
    MeasureTheory.Integrable
      (fun ω => ∑ n ∈ s, ‖windowSumC (G.g ω) n H‖ ^ 2 / (n : ℝ)) μ :=
  MeasureTheory.integrable_finset_sum _ fun n _ =>
    (G.integrable_normSq_windowSumC n H).div_const _

end StochasticMultiplicative

/-- Expected log-averaged squared window sum: at most `4·C·S` with `S = ∑_{n ∈ s} 1/n`
(per-window `windowSndMoment_le`, summed with the log weights). -/
theorem integral_sum_div_normSq_windowSumC_le [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) {C : ℝ} (hC : ∀ m : ℕ, sndMomentPartialSum G m ≤ C)
    (s : Finset ℕ) (H : ℕ) :
    ∫ ω, (∑ n ∈ s, ‖windowSumC (G.g ω) n H‖ ^ 2 / (n : ℝ)) ∂μ
      ≤ 4 * C * (∑ n ∈ s, (1 : ℝ) / n) := by
  rw [MeasureTheory.integral_finset_sum _
    (fun n _ => (G.integrable_normSq_windowSumC n H).div_const _), Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [MeasureTheory.integral_div, mul_one_div]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hpos : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_le_div_of_nonneg_right (windowSndMoment_le G hC n H) hpos.le

/-- **Markov step** (Tao 2015 §3): with probability at least `1 − ε`, the sample's
log-averaged squared window sum is at most `4·C·S/ε`.

Combined with the pigeonhole `Unimodular.exists_pair_windowCorr_le` (choose `H ≥ 8C/ε` so
that `4CS/ε ≤ H·S/2`), this extracts on the good event a shift pair with a large window
correlation — the violation of the nonasymptotic Elliott bound. -/
theorem prob_sum_div_normSq_windowSumC_le [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) {C : ℝ} (hC : ∀ m : ℕ, sndMomentPartialSum G m ≤ C)
    (s : Finset ℕ) (H : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hCS : 0 < C * (∑ n ∈ s, (1 : ℝ) / n)) :
    ENNReal.ofReal (1 - ε)
      ≤ μ {ω | ∑ n ∈ s, ‖windowSumC (G.g ω) n H‖ ^ 2 / (n : ℝ)
          ≤ 4 * C * (∑ n ∈ s, (1 : ℝ) / n) / ε} := by
  classical
  set S : ℝ := ∑ n ∈ s, (1 : ℝ) / n with hSdef
  set Z : Ω → ℝ := fun ω => ∑ n ∈ s, ‖windowSumC (G.g ω) n H‖ ^ 2 / (n : ℝ) with hZdef
  set a : ℝ := 4 * C * S / ε with hadef
  have h4CS : (0 : ℝ) < 4 * C * S := by nlinarith
  have ha : 0 < a := div_pos h4CS hε
  have hZ0 : 0 ≤ᵐ[μ] Z := Filter.Eventually.of_forall fun ω =>
    Finset.sum_nonneg fun n _ => div_nonneg (pow_nonneg (norm_nonneg _) 2) (Nat.cast_nonneg n)
  have hmark := MeasureTheory.mul_meas_ge_le_integral_of_nonneg hZ0
    (G.integrable_sum_div_normSq_windowSumC s H) a
  have hint := integral_sum_div_normSq_windowSumC_le G hC s H
  have hreal : μ.real {ω | a ≤ Z ω} ≤ ε := by
    have h4 : a * μ.real {ω | a ≤ Z ω} ≤ 4 * C * S := le_trans hmark hint
    have hdiv : μ.real {ω | a ≤ Z ω} ≤ 4 * C * S / a :=
      (le_div_iff₀ ha).2 (by linarith [h4, mul_comm a (μ.real {ω | a ≤ Z ω})])
    have haval : 4 * C * S / a = ε := by
      rw [hadef, div_div_eq_mul_div, mul_comm (4 * C * S) ε, mul_div_assoc,
        div_self (ne_of_gt h4CS), mul_one]
    calc μ.real {ω | a ≤ Z ω} ≤ 4 * C * S / a := hdiv
      _ = ε := haval
  have hmeasZ : Measurable Z := G.measurable_sum_div_normSq_windowSumC s H
  have hmeas : MeasurableSet {ω | a ≤ Z ω} := measurableSet_le measurable_const hmeasZ
  have hENN : μ {ω | a ≤ Z ω} ≤ ENNReal.ofReal ε := by
    rw [ENNReal.le_ofReal_iff_toReal_le (MeasureTheory.measure_ne_top μ _) hε.le]
    exact hreal
  calc ENNReal.ofReal (1 - ε)
      = 1 - ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_sub _ hε.le, ENNReal.ofReal_one]
    _ ≤ 1 - μ {ω | a ≤ Z ω} := tsub_le_tsub_left hENN 1
    _ = μ ({ω | a ≤ Z ω}ᶜ) := (MeasureTheory.prob_compl_eq_one_sub hmeas).symm
    _ ≤ μ {ω | Z ω ≤ a} := by
        refine MeasureTheory.measure_mono fun ω hω => ?_
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
        exact hω.le

namespace StochasticMultiplicative

/-- A single completely multiplicative unimodular `g` as a constant (deterministic) stochastic
family over any measure space. -/
def ofDeterministic (μ : Measure Ω) (g : ℕ → ℂ)
    (hmul : CompletelyMultiplicativeC g) (hg : Unimodular g) :
    StochasticMultiplicative μ where
  g := fun _ => g
  measurable := fun _ => measurable_const
  mul_ae := ae_of_all μ fun _ => hmul
  unimodular_ae := ae_of_all μ fun _ => hg

/-- Over a probability measure, the deterministic embedding's second moment is the squared
partial-sum norm itself — deterministic statements are literal special cases of stochastic
ones. -/
@[simp] theorem sndMomentPartialSum_ofDeterministic [IsProbabilityMeasure μ] (g : ℕ → ℂ)
    (hmul : CompletelyMultiplicativeC g) (hg : Unimodular g) (n : ℕ) :
    sndMomentPartialSum (ofDeterministic μ g hmul hg) n = ‖apSumC g 1 n‖ ^ 2 := by
  simp [sndMomentPartialSum, ofDeterministic]

end StochasticMultiplicative

end MoltResearch
