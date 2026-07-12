import MoltResearch.Discrepancy

/-!
# Track C: Stage 5 — measurable Markov event for zeta-weighted window sums (Tao 2015 §4)

Consumer of the stochastic substrate (issue #2871, PR G2a): the Markov step of the
generalized Borwein–Choi–Coons analysis of arXiv:1509.05363 §4. After the van der Corput
stage produces the standing bound `𝔼|∑_{h ≤ H'} 𝐠(n+h)|² ≤ 4C` uniformly in `n` and `H'`
(`windowSndMoment_le`), Tao averages the zeta-weighted squared window sums over the window
lengths `H' ∈ (H, 2H]` and concludes: *with probability `1 − O(ε)`, one has*

`(1/H) ∑_{H < H' ≤ 2H} ∑_n |∑_{h ≤ H'} 𝐠(n+h)|² / n^{1+1/log X} ≪_ε log X`.

`exists_measurable_zeta_window_event` is that step with explicit constants: the bound is
`4·C·(2 + log X)/ε`, from the per-window bound `4C`, the zeta mass
`∑_n 1/n^{1+1/log X} ≤ 2 + log X` (`tsum_one_div_rpow_le_two_add_log`), and Markov at
threshold `1/ε`.

Design notes:
- **The event is measurable by construction** — it is a sublevel set of a measurable
  `ℝ≥0∞`-valued functional. This is load-bearing: §4 intersects this event with the two
  Proposition-1.11 pretentious events before extracting a sample, so a mere outer-measure
  statement would not compose.
- **The bound is `H`-free.** The `1/H` average over `H' ∈ (H, 2H]` exactly cancels the
  `H` window lengths contributing `4C(2 + log X)` each; §4 later sends `H → ∞` against
  the fixed `≪_ε log X` budget, so an `H`-dependent bound would be useless.
- The proof runs in `ℝ≥0∞` to dodge integrability-of-tsum side conditions: Markov
  (`meas_ge_le_lintegral_div`) is applied to
  `Z ω = ∑_{H'} ∑'_n ENNReal.ofReal (|…|²/n^σ)`, whose lintegral is computed by Tonelli
  (`lintegral_finset_sum`, `lintegral_tsum`) with no summability hypotheses; on the good
  event the real tsums are recovered through `toReal` (a non-summable real tsum is junk
  `0`, which sits inside the bound anyway).
-/

namespace MoltResearch

namespace Tao2015

open MeasureTheory
open scoped ENNReal

/-- `3 ≤ X` puts the zeta exponent strictly right of `1`: `1 < log X` (since `e < 3`). -/
private lemma one_lt_log {X : ℝ} (hX : 3 ≤ X) : 1 < Real.log X := by
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    _ ≤ Real.log X := Real.log_le_log (by norm_num) hX

/-- Single cell of the Tonelli computation: the lintegral of one zeta-weighted squared
window sum is at most the (deweighted) window second moment `4C` times the zeta weight.
The `n = 0` row is the junk `0 ≤ 0` (`x / 0 = 0` on both sides). -/
private lemma lintegral_ofReal_zeta_term_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (G : StochasticMultiplicative μ)
    {C : ℝ} (hC : ∀ m : ℕ, sndMomentPartialSum G m ≤ C) (n H' : ℕ) (σ : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (‖windowSumC (G.g ω) n H'‖ ^ 2 / (n : ℝ) ^ σ) ∂μ
      ≤ ENNReal.ofReal (4 * C / (n : ℝ) ^ σ) := by
  refine le_trans (le_of_eq (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    ((G.integrable_normSq_windowSumC n H').div_const ((n : ℝ) ^ σ))
    (Filter.Eventually.of_forall fun ω =>
      div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) σ))).symm) ?_
  refine ENNReal.ofReal_le_ofReal ?_
  rw [MeasureTheory.integral_div]
  exact div_le_div_of_nonneg_right (windowSndMoment_le G hC n H')
    (Real.rpow_nonneg (Nat.cast_nonneg n) σ)

/-- One window length `H'`: summing the cell bounds over `n` against the zeta mass
`∑'_n 1/n^{1+1/log X} ≤ 2 + log X` gives the `H'`-uniform budget `4C(2 + log X)`. -/
private lemma lintegral_tsum_zeta_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (G : StochasticMultiplicative μ)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ m : ℕ, sndMomentPartialSum G m ≤ C) (H' : ℕ)
    {X : ℝ} (hX : 3 ≤ X) :
    ∫⁻ ω, ∑' n : ℕ, ENNReal.ofReal
        (‖windowSumC (G.g ω) n H'‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)) ∂μ
      ≤ ENNReal.ofReal (4 * C * (2 + Real.log X)) := by
  have hlog1 : 1 < Real.log X := one_lt_log hX
  have hσ1 : 1 < 1 + 1 / Real.log X := by
    have h0 : 0 < 1 / Real.log X := by positivity
    linarith
  have h4C : (0 : ℝ) ≤ 4 * C := by linarith
  rw [MeasureTheory.lintegral_tsum fun n =>
    ((((G.measurable_windowSumC n H').norm.pow_const 2).div_const
      ((n : ℝ) ^ (1 + 1 / Real.log X))).ennreal_ofReal).aemeasurable]
  calc ∑' n : ℕ, ∫⁻ ω, ENNReal.ofReal
        (‖windowSumC (G.g ω) n H'‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)) ∂μ
      ≤ ∑' n : ℕ, ENNReal.ofReal (4 * C / (n : ℝ) ^ (1 + 1 / Real.log X)) :=
        ENNReal.tsum_le_tsum fun n => lintegral_ofReal_zeta_term_le G hC n H' _
    _ = ENNReal.ofReal (4 * C) * ∑' n : ℕ,
          ENNReal.ofReal (1 / (n : ℝ) ^ (1 + 1 / Real.log X)) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun n => ?_
        rw [← ENNReal.ofReal_mul h4C, mul_one_div]
    _ = ENNReal.ofReal (4 * C) * ENNReal.ofReal
          (∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / Real.log X)) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
          (Real.summable_one_div_nat_rpow.mpr hσ1)]
    _ ≤ ENNReal.ofReal (4 * C) * ENNReal.ofReal (2 + Real.log X) :=
        mul_le_mul_right (ENNReal.ofReal_le_ofReal
          (tsum_one_div_rpow_le_two_add_log hX)) _
    _ = ENNReal.ofReal (4 * C * (2 + Real.log X)) :=
        (ENNReal.ofReal_mul h4C).symm

/-- **Measurable Markov event for zeta-weighted window sums** (Tao 2015,
arXiv:1509.05363 §4): under the standing second-moment bound `C`, with probability at
least `1 − ε` the sample's `H'`-averaged zeta-weighted squared window sums over
`H' ∈ (H, 2H]` are at most `4·C·(2 + log X)/ε` — an `H`-free budget, `≪_ε log X` in the
paper's notation. The event is measurable (a sublevel set of a measurable `ℝ≥0∞`
functional), so §4 can intersect it with the two Proposition-1.11 pretentious events. -/
theorem exists_measurable_zeta_window_event {Ω : Type} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) {C : ℝ} (hC0 : 0 < C)
    (hC : ∀ n : ℕ, sndMomentPartialSum G n ≤ C) {H : ℕ} (hH : 1 ≤ H) {X : ℝ} (hX : 3 ≤ X)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - ε) ≤ μ E ∧
      ∀ ω ∈ E,
        (1 / (H : ℝ)) * ∑ H' ∈ Finset.Ioc H (2 * H),
            ∑' n : ℕ, ‖windowSumC (G.g ω) n H'‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
          ≤ 4 * C * (2 + Real.log X) / ε := by
  classical
  have hlog1 : 1 < Real.log X := one_lt_log hX
  have h2log : (0 : ℝ) < 2 + Real.log X := by linarith
  have hH0 : (0 : ℝ) < H := Nat.cast_pos.mpr hH
  set σ : ℝ := 1 + 1 / Real.log X with hσdef
  -- the `ℝ≥0∞`-valued total, so Tonelli and Markov need no summability side conditions
  set Z : Ω → ℝ≥0∞ := fun ω => ∑ H' ∈ Finset.Ioc H (2 * H),
    ∑' n : ℕ, ENNReal.ofReal (‖windowSumC (G.g ω) n H'‖ ^ 2 / (n : ℝ) ^ σ) with hZdef
  have hZmeas : Measurable Z := by
    rw [hZdef]
    exact Finset.measurable_sum _ fun H' _ =>
      Measurable.ennreal_tsum fun n =>
        (((G.measurable_windowSumC n H').norm.pow_const 2).div_const
          ((n : ℝ) ^ σ)).ennreal_ofReal
  -- Tonelli + the per-window budget: `∫⁻ Z ≤ 4·C·H·(2 + log X)`
  have hZle : ∫⁻ ω, Z ω ∂μ ≤ ENNReal.ofReal (4 * C * (H : ℝ) * (2 + Real.log X)) := by
    have h1 : ∫⁻ ω, Z ω ∂μ = ∑ H' ∈ Finset.Ioc H (2 * H),
        ∫⁻ ω, ∑' n : ℕ, ENNReal.ofReal
          (‖windowSumC (G.g ω) n H'‖ ^ 2 / (n : ℝ) ^ σ) ∂μ := by
      simp only [hZdef]
      exact MeasureTheory.lintegral_finset_sum _ fun H' _ =>
        Measurable.ennreal_tsum fun n =>
          (((G.measurable_windowSumC n H').norm.pow_const 2).div_const
            ((n : ℝ) ^ σ)).ennreal_ofReal
    have hcard : (Finset.Ioc H (2 * H)).card = H := by
      rw [Nat.card_Ioc]
      omega
    calc ∫⁻ ω, Z ω ∂μ
        = ∑ H' ∈ Finset.Ioc H (2 * H), ∫⁻ ω, ∑' n : ℕ, ENNReal.ofReal
            (‖windowSumC (G.g ω) n H'‖ ^ 2 / (n : ℝ) ^ σ) ∂μ := h1
      _ ≤ ∑ _H' ∈ Finset.Ioc H (2 * H), ENNReal.ofReal (4 * C * (2 + Real.log X)) := by
          refine Finset.sum_le_sum fun H' _ => ?_
          rw [hσdef]
          exact lintegral_tsum_zeta_le G hC0.le hC H' hX
      _ = ENNReal.ofReal (4 * C * (H : ℝ) * (2 + Real.log X)) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul, ← ENNReal.ofReal_natCast H,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg H)]
          congr 1
          ring
  -- Markov at the threshold `4·C·H·(2 + log X)/ε`
  have hx0 : (0 : ℝ) < 4 * C * (H : ℝ) * (2 + Real.log X) :=
    mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hC0) hH0) h2log
  have hxε0 : (0 : ℝ) < 4 * C * (H : ℝ) * (2 + Real.log X) / ε := div_pos hx0 hε0
  set a : ℝ≥0∞ := ENNReal.ofReal (4 * C * (H : ℝ) * (2 + Real.log X) / ε) with hadef
  have ha0 : a ≠ 0 := by
    rw [hadef]
    exact (ENNReal.ofReal_pos.mpr hxε0).ne'
  have hatop : a ≠ ∞ := by
    rw [hadef]
    exact ENNReal.ofReal_ne_top
  have hprob : μ {ω | a ≤ Z ω} ≤ ENNReal.ofReal ε := by
    refine le_trans (MeasureTheory.meas_ge_le_lintegral_div hZmeas.aemeasurable ha0 hatop) ?_
    refine le_trans (ENNReal.div_le_div_right hZle a) ?_
    rw [hadef, ← ENNReal.ofReal_div_of_pos hxε0]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [div_div_eq_mul_div, mul_comm (4 * C * (H : ℝ) * (2 + Real.log X)) ε,
      mul_div_assoc, div_self hx0.ne', mul_one]
  refine ⟨{ω | Z ω < a}, measurableSet_lt hZmeas measurable_const, ?_, ?_⟩
  -- the good event has probability at least `1 − ε`
  · have hmeasge : MeasurableSet {ω | a ≤ Z ω} := measurableSet_le measurable_const hZmeas
    calc ENNReal.ofReal (1 - ε)
        = 1 - ENNReal.ofReal ε := by
          rw [ENNReal.ofReal_sub _ hε0.le, ENNReal.ofReal_one]
      _ ≤ 1 - μ {ω | a ≤ Z ω} := tsub_le_tsub_left hprob 1
      _ = μ ({ω | a ≤ Z ω}ᶜ) := (MeasureTheory.prob_compl_eq_one_sub hmeasge).symm
      _ = μ {ω | Z ω < a} := by
          congr 1
          ext ω
          simp [not_le]
  -- on the good event, recover the real average from the finite `ℝ≥0∞` total
  · intro ω hω
    have hZa : Z ω < a := hω
    have hZtop : Z ω ≠ ∞ := ne_top_of_lt hZa
    have hZω : Z ω = ∑ H' ∈ Finset.Ioc H (2 * H),
        ∑' n : ℕ, ENNReal.ofReal (‖windowSumC (G.g ω) n H'‖ ^ 2 / (n : ℝ) ^ σ) := by
      simp only [hZdef]
    have hterm_top : ∀ H' ∈ Finset.Ioc H (2 * H),
        (∑' n : ℕ, ENNReal.ofReal (‖windowSumC (G.g ω) n H'‖ ^ 2 / (n : ℝ) ^ σ)) ≠ ∞ := by
      intro H' hH'
      refine ne_top_of_le_ne_top hZtop ?_
      rw [hZω]
      exact Finset.single_le_sum (f := fun H'' => ∑' n : ℕ,
        ENNReal.ofReal (‖windowSumC (G.g ω) n H''‖ ^ 2 / (n : ℝ) ^ σ))
        (fun _ _ => zero_le _) hH'
    -- each real tsum sits below its `ℝ≥0∞` twin's `toReal` (junk `0` if not summable)
    have hS_le : ∀ H' ∈ Finset.Ioc H (2 * H),
        (∑' n : ℕ, ‖windowSumC (G.g ω) n H'‖ ^ 2 / (n : ℝ) ^ σ)
          ≤ (∑' n : ℕ, ENNReal.ofReal
              (‖windowSumC (G.g ω) n H'‖ ^ 2 / (n : ℝ) ^ σ)).toReal := by
      intro H' _
      by_cases hsum : Summable fun n : ℕ => ‖windowSumC (G.g ω) n H'‖ ^ 2 / (n : ℝ) ^ σ
      · refine le_of_eq ?_
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => div_nonneg (sq_nonneg _)
            (Real.rpow_nonneg (Nat.cast_nonneg n) σ)) hsum,
          ENNReal.toReal_ofReal (tsum_nonneg fun n => div_nonneg (sq_nonneg _)
            (Real.rpow_nonneg (Nat.cast_nonneg n) σ))]
      · rw [tsum_eq_zero_of_not_summable hsum]
        exact ENNReal.toReal_nonneg
    have hZreal : (Z ω).toReal ≤ 4 * C * (H : ℝ) * (2 + Real.log X) / ε := by
      have h1 : (Z ω).toReal ≤ a.toReal := ENNReal.toReal_mono hatop hZa.le
      rwa [hadef, ENNReal.toReal_ofReal hxε0.le] at h1
    have hεne : ε ≠ 0 := hε0.ne'
    calc (1 / (H : ℝ)) * ∑ H' ∈ Finset.Ioc H (2 * H),
          ∑' n : ℕ, ‖windowSumC (G.g ω) n H'‖ ^ 2 / (n : ℝ) ^ σ
        ≤ (1 / (H : ℝ)) * (4 * C * (H : ℝ) * (2 + Real.log X) / ε) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc ∑ H' ∈ Finset.Ioc H (2 * H),
                ∑' n : ℕ, ‖windowSumC (G.g ω) n H'‖ ^ 2 / (n : ℝ) ^ σ
              ≤ ∑ H' ∈ Finset.Ioc H (2 * H), (∑' n : ℕ, ENNReal.ofReal
                  (‖windowSumC (G.g ω) n H'‖ ^ 2 / (n : ℝ) ^ σ)).toReal :=
                Finset.sum_le_sum hS_le
            _ = (Z ω).toReal := by rw [hZω, ENNReal.toReal_sum hterm_top]
            _ ≤ 4 * C * (H : ℝ) * (2 + Real.log X) / ε := hZreal
      _ = 4 * C * (2 + Real.log X) / ε := by
          rw [div_mul_div_comm, one_mul, div_eq_div_iff (mul_pos hH0 hε0).ne' hεne]
          ring

-- Consumer check (compile-only): on the same event, the average controls each single
-- window length `H' ∈ (H, 2H]` by nonnegativity — the shape the §4 chain consumes after
-- fixing one `H'`.
example {Ω : Type} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] (G : StochasticMultiplicative μ) {C : ℝ}
    (hC0 : 0 < C) (hC : ∀ n : ℕ, sndMomentPartialSum G n ≤ C) {H : ℕ} (hH : 1 ≤ H)
    {X : ℝ} (hX : 3 ≤ X) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {H' : ℕ} (hH' : H' ∈ Finset.Ioc H (2 * H)) :
    ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - ε) ≤ μ E ∧
      ∀ ω ∈ E,
        ∑' n : ℕ, ‖windowSumC (G.g ω) n H'‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
          ≤ (H : ℝ) * (4 * C * (2 + Real.log X) / ε) := by
  obtain ⟨E, hEmeas, hEprob, hEbound⟩ :=
    exists_measurable_zeta_window_event G hC0 hC hH hX hε0 hε1
  refine ⟨E, hEmeas, hEprob, fun ω hω => ?_⟩
  have hH0 : (0 : ℝ) < H := Nat.cast_pos.mpr hH
  have h1 : ∑' n : ℕ, ‖windowSumC (G.g ω) n H'‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X)
      ≤ ∑ H'' ∈ Finset.Ioc H (2 * H),
          ∑' n : ℕ, ‖windowSumC (G.g ω) n H''‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X) :=
    Finset.single_le_sum (f := fun H'' => ∑' n : ℕ,
      ‖windowSumC (G.g ω) n H''‖ ^ 2 / (n : ℝ) ^ (1 + 1 / Real.log X))
      (fun H'' _ => tsum_nonneg fun n =>
        div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hH'
  have h3 := mul_le_mul_of_nonneg_left (hEbound ω hω) hH0.le
  rw [← mul_assoc, mul_one_div, div_self hH0.ne', one_mul] at h3
  exact h1.trans h3

end Tao2015

end MoltResearch
