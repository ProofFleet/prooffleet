import Conjectures.C0003_edp_rate.src.Statement
import Conjectures.C0003_edp_rate.src.SourceBudget
import Conjectures.C0003_edp_rate.src.StructuredThresholds
import MoltResearch.Discrepancy.PretentiousDist
import MoltResearch.Discrepancy.StochasticMultiplicative

/-!
# A finite-scale reduction for an explicit Erdős-discrepancy rate

This file records the conditional interface selected in
`Problems/edp_rate_approach.md` and repaired in
`Problems/edp_rate_interface_repair.md` and
`Problems/edp_rate_interface_repair_2.md`.  It replaces the compact limiting law in Tao's
Section 2 with one law used only up to an explicit cutoff.  The three unproved inputs are
deliberately named `*Assumption`; the theorem at the end is only their logical composition
and does not claim an unconditional discrepancy rate.

The rate is a conservative, concrete version of the triple-logarithmic product-scale rate
obtained by reparameterizing McNamara's quantitative rectangle.  The exponent `1/500` stays
strictly below the published `1/484-o(1)` exponent.  The analysis cutoff is calibrated to the
exact source budget of the finite exponent-box construction; see
`Problems/edp_rate_fourier_redesign.md`.
-/

namespace MoltResearch

open MeasureTheory

/-- The historical A3 start scale.  It remains public because the checked A5/A7/A9
obstruction files use it.  The active `.budgeted` policy uses the schedule-dependent
`edpBudgetedRateStart` below. -/
noncomputable def edpRateStart : ℝ :=
  Real.exp (Real.exp (Real.exp 1))

/-- The exact terminal source budget of the exponent-box construction at analysis scale `X`,
using the least positive modulus that pays for the wraparound error. -/
def edpScheduledSourceBudget (X : ℕ) : ℕ :=
  spectralSourceBudget X
    (max 1 (Fintype.card (PrimeIdx X) * Nat.log 2 X * X ^ 2)) X

/-- The finite analytic window available at product scale `x`: the greatest `X ≤ ⌊x⌋₊`
whose exact scheduled source budget fits below `⌊x⌋₊`.

This replaces the overlarge A3 schedule.  It makes the Fourier source-budget inequality true
by construction, while every fixed `X` is eventually admitted once the outer budget exceeds
the fixed natural number `max X (edpScheduledSourceBudget X)`.
-/
noncomputable def edpAnalysisCutoff (x : ℝ) : ℕ :=
  Nat.findGreatest
    (fun X => edpScheduledSourceBudget X ≤ ⌊x⌋₊) ⌊x⌋₊

/-- A concrete first-rate target.  Past `edpRateStart` it is a fixed positive multiple of
`(log log log x)^(1/500)`; before that scale it is `1`, so the progression `(d,m) = (1,1)`
suffices.

The triple logarithm comes from converting McNamara's rectangular range to the product budget;
`1/500 < 1/484` leaves room for his lower-order iterated-log losses.  The coefficient `10^-7`
is the A5' recalibration after replacing the A3 cutoff by the source-budget-safe schedule.  See
`Problems/edp_rate_fourier_redesign.md`.
-/
noncomputable def edpTripleLogRate (x : ℝ) : ℝ :=
  if x ≤ edpRateStart then 1
  else (1 / 10 ^ 7 : ℝ) *
    Real.rpow (Real.log (Real.log (Real.log x))) ((1 : ℝ) / 500)

/-- A law has the finite second-moment bound needed by the effective analytic stages at
product scale `x`.  Unlike `exists_limit_law`, this asks for bounds only through the explicit
cutoff `edpAnalysisCutoff x`.
-/
def FiniteSecondMomentBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G : StochasticMultiplicative μ) (x : ℝ) : Prop :=
  ∀ n : ℕ, n ≤ edpAnalysisCutoff x →
    sndMomentPartialSum G n ≤ edpTripleLogRate x ^ 2 + 1

/-- The finite-scale version of Tao's pretentious event: at truncation `X`, a sample lies
within squared pretentious distance `B` of some character twist of modulus at most `Q` and
frequency at most `T * X`.
-/
noncomputable def finitePretentiousEvent {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (G : StochasticMultiplicative μ)
    (Q T B : ℝ) (X : ℕ) : Set Ω :=
  {ω : Ω | ∃ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
    (q : ℝ) ≤ Q ∧ |t| ≤ T * X ∧
      pretentiousDistSq (G.g ω) (charTwist q χ t) X ≤ B}

/-- Which finite-endpoint contract a conditional rate assumption uses.

`historical` preserves the A3 statement so the checked A7/A9 obstruction artifacts remain
buildable.  The active reduction uses `budgeted`; its first endpoint restrictions came from
A3' and its schedule-dependent start plus structured witness caps come from A3''. -/
inductive FiniteEndpointPolicy where
  | historical
  | budgeted

/-- Historical A3 persistent-pretense target.  It is retained only as the subject of the
checked obstruction artifacts in `FiniteVanDerCorput.lean` and `FiniteStructured.lean`.
New rate assumptions must use `FiniteEndpointPolicy.budgeted`. -/
def HistoricalFinitePersistentPretentious {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G : StochasticMultiplicative μ) (x : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ Q T B : ℝ, 1 ≤ Q ∧ 1 ≤ T ∧ 0 ≤ B ∧
        ∃ X₀ : ℕ, 1 ≤ X₀ ∧ X₀ ≤ edpAnalysisCutoff x ∧
          ∀ X : ℕ, X₀ ≤ X → X ≤ edpAnalysisCutoff x →
            ENNReal.ofReal (1 - K * ε) ≤ μ (finitePretentiousEvent G Q T B X)

/-! ## Repaired finite-endpoint controls -/

/-- Cofinal modulus cap fixed by the cutoff before a pretentious package is selected. -/
noncomputable def edpPretentiousModulusCap (L : ℕ) : ℝ :=
  max 1 (Real.log ((L : ℝ) + 1))

/-- Cofinal frequency cap fixed by the cutoff before a pretentious package is selected. -/
noncomputable def edpPretentiousFrequencyCap (L : ℕ) : ℝ :=
  max 1 (Real.log ((L : ℝ) + 1))

/-- A deliberately slow cofinal distance cap.  Unlike the historical interface, the
package cannot enlarge `B` to the universal finite-truncation bound after seeing `L`. -/
noncomputable def edpPretentiousDistanceCap (L : ℕ) : ℝ :=
  max 0 ((1 / 4 : ℝ) * Real.log (Real.log ((L : ℝ) + 3)))

/-- The largest moment shift reserved for the A6 van-der-Corput window at accuracy `ε`.
This is definitionally the A6 function `edpVdCWindowLength` at the moment cap
`edpTripleLogRate x ^ 2 + 1`, but is defined here to avoid a downstream import cycle. -/
noncomputable def edpPersistentWindowLength (x ε : ℝ) : ℕ :=
  max 1 ⌈8 * max (edpTripleLogRate x ^ 2 + 1) 1 / ε⌉₊

theorem one_le_edpPersistentWindowLength (x ε : ℝ) :
    1 ≤ edpPersistentWindowLength x ε := by
  simp [edpPersistentWindowLength]

/-! ## Second-repair schedule and structured threshold budgets -/

/-- A cofinal cap for the probability-loss constant.  Fixing this cap before the
van-der-Corput package also fixes a positive lower bound for its accuracy. -/
noncomputable def edpProbabilityLossCap (L : ℕ) : ℝ :=
  max 1 (Real.log ((L : ℝ) + 1))

/-- The smallest accuracy admitted by the budgeted policy at cutoff `L`.  Choosing this
value makes `K * ε ≤ 1/4` for every `K ≤ edpProbabilityLossCap L`. -/
noncomputable def edpAccuracyFloor (L : ℕ) : ℝ :=
  1 / (4 * (edpProbabilityLossCap L + 1))

theorem edpAccuracyFloor_pos (L : ℕ) : 0 < edpAccuracyFloor L := by
  unfold edpAccuracyFloor edpProbabilityLossCap
  positivity

theorem edpAccuracyFloor_le_one (L : ℕ) : edpAccuracyFloor L ≤ 1 := by
  unfold edpAccuracyFloor edpProbabilityLossCap
  rw [div_le_one (by positivity)]
  have hcap : (1 : ℝ) ≤ max 1 (Real.log ((L : ℝ) + 1)) := le_max_left _ _
  linarith

/-- The scheduled accuracy pays the structured two-event probability budget for every
admitted loss constant. -/
theorem edpProbabilityLoss_mul_accuracyFloor_le {L : ℕ} {K : ℝ}
    (hK : K ≤ edpProbabilityLossCap L) :
    K * edpAccuracyFloor L ≤ 1 / 4 := by
  have hcap : (1 : ℝ) ≤ edpProbabilityLossCap L := by
    exact le_max_left _ _
  have hden : 0 < 4 * (edpProbabilityLossCap L + 1) := by positivity
  rw [edpAccuracyFloor, mul_one_div, div_le_iff₀ hden]
  nlinarith

/-- The accuracy range whose largest A6 window is reserved before the large-scale branch
opens.  The positive lower endpoint is essential: the old range `0 < ε ≤ 1` has no finite
uniform upper bound on `edpPersistentWindowLength x ε`. -/
def EDPBudgetedAccuracy (x ε : ℝ) : Prop :=
  edpAccuracyFloor (edpAnalysisCutoff x) ≤ ε ∧ ε ≤ 1

theorem edpBudgetedAccuracy_pos {x ε : ℝ} (hε : EDPBudgetedAccuracy x ε) : 0 < ε :=
  (edpAccuracyFloor_pos (edpAnalysisCutoff x)).trans_le hε.1

/-- A cofinal cap on the starting scale selected by the finite van-der-Corput package. -/
def edpPersistentStartCap (L : ℕ) : ℕ :=
  max 1 (Nat.log 2 (L + 1))

/-- The largest A6 window over the complete admissible accuracy interval. -/
noncomputable def edpPersistentWindowMax (x : ℝ) : ℕ :=
  edpPersistentWindowLength x (edpAccuracyFloor (edpAnalysisCutoff x))

/-- Every admissible accuracy has a window no longer than the scheduled maximum. -/
theorem edpPersistentWindowLength_le_max {x ε : ℝ}
    (hε : EDPBudgetedAccuracy x ε) :
    edpPersistentWindowLength x ε ≤ edpPersistentWindowMax x := by
  unfold edpPersistentWindowLength edpPersistentWindowMax
  apply max_le_max le_rfl
  apply Nat.ceil_mono
  exact div_le_div_of_nonneg_left (by positivity)
    (edpAccuracyFloor_pos (edpAnalysisCutoff x)) hε.1

/-- The analysis index that reserves every admissible A6 window, one positive starting
index, and the additional `X + 1` scale used by the structured two-event argument. -/
noncomputable def edpBudgetedRequiredCutoff (x : ℝ) : ℕ :=
  edpPersistentStartCap (edpAnalysisCutoff x) + edpPersistentWindowMax x + 1

/-- The active start schedule.  At the same outer horizon `x`, it charges both the desired
analysis index and its exact exponent-box source budget.  Thus entering the active branch is
itself a proof that `edpBudgetedRequiredCutoff x` is admitted by `edpAnalysisCutoff x`.

The dependence on `x` is intentional: the moment cap, accuracy floor, and resulting A6
window all vary with the outer horizon.  The historical fixed constant `edpRateStart` is only
the first term of this maximum. -/
noncomputable def edpBudgetedRateStart (x : ℝ) : ℝ :=
  max edpRateStart
    ((max (edpBudgetedRequiredCutoff x)
      (edpScheduledSourceBudget (edpBudgetedRequiredCutoff x)) : ℕ) : ℝ)

/-- The active start dominates the historical analytic positivity threshold. -/
theorem edpRateStart_le_budgetedRateStart (x : ℝ) :
    edpRateStart ≤ edpBudgetedRateStart x := by
  exact le_max_left _ _

/-- Kernel-checked schedule invariant: the active large-scale branch cannot open before its
entire reserved index is inside the source-budget-safe analysis cutoff. -/
theorem edpBudgetedRequiredCutoff_le_analysisCutoff {x : ℝ}
    (hx : edpBudgetedRateStart x < x) :
    edpBudgetedRequiredCutoff x ≤ edpAnalysisCutoff x := by
  have hmaxlt :
      ((max (edpBudgetedRequiredCutoff x)
        (edpScheduledSourceBudget (edpBudgetedRequiredCutoff x)) : ℕ) : ℝ) < x :=
    lt_of_le_of_lt (le_max_right _ _) (by simpa [edpBudgetedRateStart] using hx)
  have hrequired : edpBudgetedRequiredCutoff x ≤ ⌊x⌋₊ := by
    apply Nat.le_floor
    exact le_of_lt (lt_of_le_of_lt (by
      exact_mod_cast Nat.le_max_left (edpBudgetedRequiredCutoff x)
        (edpScheduledSourceBudget (edpBudgetedRequiredCutoff x))) hmaxlt)
  have hbudget : edpScheduledSourceBudget (edpBudgetedRequiredCutoff x) ≤ ⌊x⌋₊ := by
    apply Nat.le_floor
    exact le_of_lt (lt_of_le_of_lt (by
      exact_mod_cast Nat.le_max_right (edpBudgetedRequiredCutoff x)
        (edpScheduledSourceBudget (edpBudgetedRequiredCutoff x))) hmaxlt)
  unfold edpAnalysisCutoff
  exact Nat.le_findGreatest hrequired hbudget

/-- In particular, every active analysis cutoff contains at least the indices `0,1,2,3`.
This directly excludes the `x = 10^10`, cutoff-at-most-two obstruction from A7'. -/
theorem three_le_edpAnalysisCutoff_of_budgetedRateStart_lt {x : ℝ}
    (hx : edpBudgetedRateStart x < x) : 3 ≤ edpAnalysisCutoff x := by
  have hrequired := edpBudgetedRequiredCutoff_le_analysisCutoff hx
  have hstart : 1 ≤ edpPersistentStartCap (edpAnalysisCutoff x) := le_max_left _ _
  have hwindow : 1 ≤ edpPersistentWindowMax x :=
    one_le_edpPersistentWindowLength _ _
  unfold edpBudgetedRequiredCutoff at hrequired
  omega

/-- Every admissible `(ε,X₀)` has its A6 window and the structured `+1` charge below the
cutoff as soon as the active branch begins.  This is the quantified inequality missing from
the first repair. -/
theorem edpBudgeted_window_fits_of_rateStart_lt {x ε : ℝ} {X₀ : ℕ}
    (hx : edpBudgetedRateStart x < x) (hε : EDPBudgetedAccuracy x ε)
    (hX₀ : X₀ ≤ edpPersistentStartCap (edpAnalysisCutoff x)) :
    X₀ + edpPersistentWindowLength x ε + 1 ≤ edpAnalysisCutoff x := by
  have hrequired := edpBudgetedRequiredCutoff_le_analysisCutoff hx
  have hwindow := edpPersistentWindowLength_le_max hε
  unfold edpBudgetedRequiredCutoff at hrequired
  omega

/-- The active rate: it remains `1` until the schedule invariant is available, then agrees
with the historical triple-log formula. -/
noncomputable def edpBudgetedTripleLogRate (x : ℝ) : ℝ :=
  if x ≤ edpBudgetedRateStart x then 1
  else (1 / 10 ^ 7 : ℝ) *
    Real.rpow (Real.log (Real.log (Real.log x))) ((1 : ℝ) / 500)

/-- On the active large-scale branch the historical and repaired formulas coincide. -/
theorem edpTripleLogRate_eq_budgeted_of_rateStart_lt {x : ℝ}
    (hx : edpBudgetedRateStart x < x) :
    edpTripleLogRate x = edpBudgetedTripleLogRate x := by
  have hlegacy : edpRateStart < x := (edpRateStart_le_budgetedRateStart x).trans_lt hx
  simp only [edpTripleLogRate, edpBudgetedTripleLogRate, if_neg (not_le_of_gt hlegacy),
    if_neg (not_le_of_gt hx)]

/-- Cofinal cap for the function-form maximum of per-character BCC thresholds. -/
def edpStructuredPairThresholdCap (L : ℕ) : ℕ :=
  edpPersistentStartCap L

theorem edpStructuredPairThresholdCap_le {L : ℕ} (hL : 1 ≤ L) :
    edpStructuredPairThresholdCap L ≤ L := by
  have hlog : Nat.log 2 (L + 1) < L + 1 :=
    Nat.log_lt_self 2 (by omega)
  unfold edpStructuredPairThresholdCap edpPersistentStartCap
  omega

/-- Cofinal cap for the function-form modulus-zero exclusion threshold. -/
def edpStructuredZeroThresholdCap (L : ℕ) : ℕ :=
  edpPersistentStartCap L

/-- Cofinal cap for the function-form Vinogradov--Korobov `t`-cut witness. -/
noncomputable def edpStructuredTCutThresholdCap (L : ℕ) : ℝ :=
  max 0 (Real.log ((L : ℝ) + 1))

/-- The last base index at which the structured terminal scale may be placed while reserving
both its `X + 1` event and the full A6 moment window. -/
noncomputable def edpStructuredTerminalCap (x ε : ℝ) : ℕ :=
  edpAnalysisCutoff x - (1 + edpPersistentWindowLength x ε)

/-- The exact joint terminal maximum charged by the structured route, including its second
event and every moment touched by the reserved A6 window. -/
noncomputable def edpStructuredTerminalMaximum
    (x ε Q T B : ℝ) (hQ : 1 ≤ Q) (hT : 1 ≤ T) (hB : 0 ≤ B)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (Xstart Xpair Xzero H : ℕ) (Twindow : ℝ) : ℕ :=
  Tao2015.structuredTerminalScaleOfTCut Q T B hQ hT hB δ hδ0 hδ1
      Xstart Xpair Xzero H Twindow
    + 1 + edpPersistentWindowLength x ε

/-- Admissible function-form structured data.  `Xpair`, `Xzero`, and the actual A8 `t`-cut
function are each capped before use; the final conjunct caps their *joint* terminal maximum,
including all nonlinear log/rpow threshold constructors.  Individual caps alone do not imply
that last comparison. -/
noncomputable def BudgetedStructuredThresholdsAdmissible
    (x ε Q T B : ℝ) (hQ : 1 ≤ Q) (hT : 1 ≤ T) (hB : 0 ≤ B)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (Xstart Xpair Xzero H : ℕ) (Twindow : ℝ) : Prop :=
  Xpair ≤ edpStructuredPairThresholdCap (edpAnalysisCutoff x) ∧
  Xzero ≤ edpStructuredZeroThresholdCap (edpAnalysisCutoff x) ∧
  Tao2015.structuredTCutThreshold Q T B hQ hT hB δ hδ0 hδ1 ≤
    edpStructuredTCutThresholdCap (edpAnalysisCutoff x) ∧
  Tao2015.structuredTerminalScaleOfTCut Q T B hQ hT hB δ hδ0 hδ1
      Xstart Xpair Xzero H Twindow ≤ edpStructuredTerminalCap x ε

/-- The A9' counterexample `Xpair = L + 1` is rejected by the repaired function-form cap
at every active cutoff. -/
theorem not_budgetedStructuredThresholdsAdmissible_cutoff_add_one
    {x ε Q T B : ℝ} (hx : edpBudgetedRateStart x < x)
    (hQ : 1 ≤ Q) (hT : 1 ≤ T) (hB : 0 ≤ B)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (Xstart Xzero H : ℕ) (Twindow : ℝ) :
    ¬ BudgetedStructuredThresholdsAdmissible
      x ε Q T B hQ hT hB δ hδ0 hδ1 Xstart
        (edpAnalysisCutoff x + 1) Xzero H Twindow := by
  intro hadmissible
  have hL : 1 ≤ edpAnalysisCutoff x :=
    (three_le_edpAnalysisCutoff_of_budgetedRateStart_lt hx).trans' (by omega)
  have hcap := edpStructuredPairThresholdCap_le hL
  unfold BudgetedStructuredThresholdsAdmissible at hadmissible
  omega

/-- Every admissible structured package has the exact terminal fit requested by A9'. -/
theorem edpStructuredTerminalMaximum_le_cutoff_of_admissible
    {x ε Q T B : ℝ} (hx : edpBudgetedRateStart x < x)
    (hε : EDPBudgetedAccuracy x ε)
    (hQ : 1 ≤ Q) (hT : 1 ≤ T) (hB : 0 ≤ B)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (Xstart Xpair Xzero H : ℕ) (Twindow : ℝ)
    (hadmissible : BudgetedStructuredThresholdsAdmissible
      x ε Q T B hQ hT hB δ hδ0 hδ1 Xstart Xpair Xzero H Twindow) :
    edpStructuredTerminalMaximum x ε Q T B hQ hT hB δ hδ0 hδ1
      Xstart Xpair Xzero H Twindow ≤ edpAnalysisCutoff x := by
  have hreserve := edpBudgeted_window_fits_of_rateStart_lt
    (x := x) (ε := ε) (X₀ := 0) hx hε (Nat.zero_le _)
  unfold BudgetedStructuredThresholdsAdmissible at hadmissible
  unfold edpStructuredTerminalCap at hadmissible
  unfold edpStructuredTerminalMaximum
  omega

/-- The twice-repaired finite persistent-pretense target.

Only one accuracy is requested: this is exactly what the structured contradiction consumes.
It must give probability loss at most `1/4`, choose `K`, `ε`, `X₀`, and `(Q,T,B)` under
cutoff-dependent caps fixed before the package, and reserve every A6 moment through `X + H`.
The starting-scale fit includes one additional index for the structured two-event call.
The estimate then holds throughout the entire interval ending at
`edpAnalysisCutoff x - H`.

The caps are cofinal functions, so a fixed qualitative package is eventually admitted, but
no package can diagonalize by choosing an arbitrarily large `B` at the last finite endpoint.
See `Problems/edp_rate_interface_repair_2.md`. -/
noncomputable def BudgetedFinitePersistentPretentious
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G : StochasticMultiplicative μ) (x : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ K ≤ edpProbabilityLossCap (edpAnalysisCutoff x) ∧
    ∃ ε : ℝ, EDPBudgetedAccuracy x ε ∧ K * ε ≤ 1 / 4 ∧
      ∃ Q T B : ℝ,
        1 ≤ Q ∧ Q ≤ edpPretentiousModulusCap (edpAnalysisCutoff x) ∧
        1 ≤ T ∧ T ≤ edpPretentiousFrequencyCap (edpAnalysisCutoff x) ∧
        0 ≤ B ∧ B ≤ edpPretentiousDistanceCap (edpAnalysisCutoff x) ∧
          ∃ X₀ : ℕ, 1 ≤ X₀ ∧
            X₀ ≤ edpPersistentStartCap (edpAnalysisCutoff x) ∧
            X₀ + edpPersistentWindowLength x ε + 1 ≤ edpAnalysisCutoff x ∧
              (∀ (hQ : 1 ≤ Q) (hT : 1 ≤ T) (hB : 0 ≤ B)
                (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
                (Xpair Xzero H : ℕ) (Twindow : ℝ),
                BudgetedStructuredThresholdsAdmissible
                    x ε Q T B hQ hT hB δ hδ0 hδ1
                      X₀ Xpair Xzero H Twindow →
                  edpStructuredTerminalMaximum
                    x ε Q T B hQ hT hB δ hδ0 hδ1
                      X₀ Xpair Xzero H Twindow ≤ edpAnalysisCutoff x) ∧
              ∀ X : ℕ, X₀ ≤ X →
                X + edpPersistentWindowLength x ε ≤ edpAnalysisCutoff x →
                  ENNReal.ofReal (1 - K * ε) ≤
                    μ (finitePretentiousEvent G Q T B X)

/-- Policy-indexed finite persistent pretense.

The default is historical solely so the two merged obstruction files remain compile-time
regressions.  All three active rate classes and the glue theorem explicitly select
`.budgeted`; future consumers should do the same. -/
noncomputable def FinitePersistentPretentious {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G : StochasticMultiplicative μ) (x : ℝ)
    (policy : FiniteEndpointPolicy := .historical) : Prop :=
  match policy with
  | .historical => HistoricalFinitePersistentPretentious μ G x
  | .budgeted => BudgetedFinitePersistentPretentious μ G x

/-- A budgeted package always leaves the positive A6 window inside the moment cutoff. -/
theorem budgetedFinitePersistentPretentious_has_slack
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (G : StochasticMultiplicative μ) (x : ℝ)
    (h : FinitePersistentPretentious μ G x .budgeted) :
    ∃ ε : ℝ, ∃ X₀ : ℕ, 0 < ε ∧ 1 ≤ X₀ ∧
      X₀ + edpPersistentWindowLength x ε + 1 ≤ edpAnalysisCutoff x := by
  change BudgetedFinitePersistentPretentious μ G x at h
  rcases h with ⟨K, hK, hKcap, ε, hε, hKε, Q, T, B, hQ1, hQcap,
    hT1, hTcap, hB0, hBcap, X₀, hX₀1, hX₀cap, hfit, hstructured,
    hpersistent⟩
  exact ⟨ε, X₀, edpBudgetedAccuracy_pos hε, hX₀1, hfit⟩

/-- A budgeted persistent package exposes a terminal-fit theorem for every admissible set of
function-form structured witnesses. -/
theorem budgetedFinitePersistentPretentious_structuredTerminalFits
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (G : StochasticMultiplicative μ) (x : ℝ)
    (h : FinitePersistentPretentious μ G x .budgeted) :
    ∃ (ε Q T B : ℝ) (hQ : 1 ≤ Q) (hT : 1 ≤ T) (hB : 0 ≤ B) (X₀ : ℕ),
      EDPBudgetedAccuracy x ε ∧
      ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
        (Xpair Xzero H : ℕ) (Twindow : ℝ),
        BudgetedStructuredThresholdsAdmissible
            x ε Q T B hQ hT hB δ hδ0 hδ1 X₀ Xpair Xzero H Twindow →
          edpStructuredTerminalMaximum
            x ε Q T B hQ hT hB δ hδ0 hδ1 X₀ Xpair Xzero H Twindow ≤
              edpAnalysisCutoff x := by
  change BudgetedFinitePersistentPretentious μ G x at h
  rcases h with ⟨K, hK, hKcap, ε, hε, hKε, Q, T, B, hQ, hQcap,
    hT, hTcap, hB, hBcap, X₀, hX₀1, hX₀cap, hfit, hstructured,
    hpersistent⟩
  exact ⟨ε, Q, T, B, hQ, hT, hB, X₀, hε,
    hstructured hQ hT hB⟩

/-- The branch condition attached to a policy.  Historical regression artifacts retain the
fixed A3 start; the active policy uses the source-budget-aware second-repair schedule. -/
noncomputable def edpPolicyRateStart
    (policy : FiniteEndpointPolicy) (x : ℝ) : ℝ :=
  match policy with
  | .historical => edpRateStart
  | .budgeted => edpBudgetedRateStart x

/-- **Finite Fourier-reduction input.**  If every homogeneous sum inside the product budget
`dm ≤ x` is smaller than `edpTripleLogRate x`, produce a stochastic completely multiplicative
law whose second moments are small through `edpAnalysisCutoff x`.

This is the precise replacement for `exists_limit_law` proposed in
`Problems/edp_rate_approach.md`.  The tree already constructs exact completely multiplicative
finite spectral samples; the new mathematical obligation is to keep every translating dilation
inside the source budget instead of assuming a global discrepancy bound.  The policy index
keeps that same Fourier payload synchronized with the repaired downstream contract; see
`Problems/edp_rate_interface_repair_2.md`.
-/
class FiniteFourierReductionAssumption
    (policy : FiniteEndpointPolicy := .historical) : Prop where
  reduce :
    ∀ (f : ℕ → ℤ), IsSignSequence f →
      ∀ x : ℝ, edpRateStart < x →
        (∀ d m : ℕ, 0 < d → (m * d : ℝ) ≤ x →
          |(apSum f d m : ℝ)| < edpTripleLogRate x) →
          ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ)
            (_ : @IsProbabilityMeasure Ω mΩ μ)
            (G : @StochasticMultiplicative Ω mΩ μ),
            @FiniteSecondMomentBound Ω mΩ μ G x

/-- Historical consumer-facing projection, retained for the merged A5 obstruction. -/
theorem finiteFourierReduction [inst : FiniteFourierReductionAssumption]
    (f : ℕ → ℤ) (hf : IsSignSequence f) (x : ℝ) (hx : edpRateStart < x)
    (hsmall : ∀ d m : ℕ, 0 < d → (m * d : ℝ) ≤ x →
      |(apSum f d m : ℝ)| < edpTripleLogRate x) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ)
      (_ : @IsProbabilityMeasure Ω mΩ μ)
      (G : @StochasticMultiplicative Ω mΩ μ),
      @FiniteSecondMomentBound Ω mΩ μ G x :=
  inst.reduce f hf x hx hsmall

/-- Consumer-facing projection of the repaired Fourier interface. -/
theorem finiteFourierReduction_budgeted
    [inst : FiniteFourierReductionAssumption .budgeted]
    (f : ℕ → ℤ) (hf : IsSignSequence f) (x : ℝ) (hx : edpRateStart < x)
    (hsmall : ∀ d m : ℕ, 0 < d → (m * d : ℝ) ≤ x →
      |(apSum f d m : ℝ)| < edpTripleLogRate x) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ)
      (_ : @IsProbabilityMeasure Ω mΩ μ)
      (G : @StochasticMultiplicative Ω mΩ μ),
      @FiniteSecondMomentBound Ω mΩ μ G x :=
  inst.reduce f hf x hx hsmall

/-- **Finite van-der-Corput/Elliott input.**  A finite second-moment bound forces persistent
pretentiousness before the same explicit cutoff.

At policy `.budgeted`, the intended proof is a threshold-tracked version of the tree's
`TrackCStage5VanDerCorputProof.lean`, consuming the nonasymptotic Elliott estimate and fitting
all choices of `H`, `A`, `w`, and the terminal truncation below the scheduled endpoint.
The active branch premise already reserves the maximum window over every admissible accuracy;
see `Problems/edp_rate_interface_repair_2.md`, Sections 4 and 6.
-/
class FiniteVanDerCorputRateAssumption
    (policy : FiniteEndpointPolicy := .historical) : Prop where
  pretentious :
    ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : @Measure Ω mΩ)
      [@IsProbabilityMeasure Ω mΩ μ]
      (G : @StochasticMultiplicative Ω mΩ μ) (x : ℝ),
      edpPolicyRateStart policy x < x → FiniteSecondMomentBound μ G x →
        FinitePersistentPretentious μ G x policy

/-- Historical consumer-facing projection, retained for the merged A7 obstruction. -/
theorem finiteVanDerCorputRate [inst : FiniteVanDerCorputRateAssumption]
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) (x : ℝ) (hx : edpRateStart < x)
    (hG : FiniteSecondMomentBound μ G x) :
    FinitePersistentPretentious μ G x :=
  inst.pretentious μ G x (by simpa [edpPolicyRateStart] using hx) hG

/-- Consumer-facing projection of the repaired van-der-Corput interface. -/
theorem finiteVanDerCorputRate_budgeted
    [inst : FiniteVanDerCorputRateAssumption .budgeted]
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) (x : ℝ)
    (hx : edpBudgetedRateStart x < x)
    (hG : FiniteSecondMomentBound μ G x) :
    FinitePersistentPretentious μ G x .budgeted :=
  inst.pretentious μ G x (by simpa [edpPolicyRateStart] using hx) hG

/-- **Finite Borwein--Choi--Coons input.**  The structured branch defeats the finite
persistent-pretentiousness conclusion while the same second-moment cap is in force.

At policy `.budgeted`, the intended proof effectivizes the present Section 4 wrapper using the
tree's explicit Mertens, repulsion, zero-free-region, and Euler-product bounds.  It must handle
every `(Q,T,B)` below the fixed cutoff caps and fit its dependent terminal scale below the
shortened endpoint, with `Xpair`, `Xzero`, the t-cut, and their joint maximum all admitted by
the second-repair caps; no limit in `x` is available.  See
`Problems/edp_rate_interface_repair_2.md`, Sections 4 and 6.
-/
class FiniteBorweinChoiCoonsRateAssumption
    (policy : FiniteEndpointPolicy := .historical) : Prop where
  not_pretentious :
    ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : @Measure Ω mΩ)
      [@IsProbabilityMeasure Ω mΩ μ]
      (G : @StochasticMultiplicative Ω mΩ μ) (x : ℝ),
      edpPolicyRateStart policy x < x → FiniteSecondMomentBound μ G x →
        ¬ FinitePersistentPretentious μ G x policy

/-- Historical consumer-facing projection, retained for the merged A9 obstruction. -/
theorem finiteBorweinChoiCoonsRate [inst : FiniteBorweinChoiCoonsRateAssumption]
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) (x : ℝ) (hx : edpRateStart < x)
    (hG : FiniteSecondMomentBound μ G x) :
    ¬ FinitePersistentPretentious μ G x :=
  inst.not_pretentious μ G x (by simpa [edpPolicyRateStart] using hx) hG

/-- Consumer-facing projection of the repaired structured interface. -/
theorem finiteBorweinChoiCoonsRate_budgeted
    [inst : FiniteBorweinChoiCoonsRateAssumption .budgeted]
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : StochasticMultiplicative μ) (x : ℝ)
    (hx : edpBudgetedRateStart x < x)
    (hG : FiniteSecondMomentBound μ G x) :
    ¬ FinitePersistentPretentious μ G x .budgeted :=
  inst.not_pretentious μ G x (by simpa [edpPolicyRateStart] using hx) hG

/-- Conditional first EDP rate: the finite Fourier reduction, finite Elliott/van-der-Corput
stage, and finite structured branch compose to
`HasDiscrepancyRateBy edpBudgetedTripleLogRate`.

This theorem proves only the glue.  Its three `.budgeted` typeclass inputs are open obligations
listed in `Problems/edp_rate_interface_repair_2.md`; only the Fourier input is instantiated
separately in `FiniteFourierBudget.lean`.
-/
theorem discrepancyRate_of_assumptions
    [FiniteFourierReductionAssumption .budgeted]
    [FiniteVanDerCorputRateAssumption .budgeted]
    [FiniteBorweinChoiCoonsRateAssumption .budgeted] :
    HasDiscrepancyRateBy edpBudgetedTripleLogRate := by
  intro f hf x hx
  by_cases hsmallx : x ≤ edpBudgetedRateStart x
  · refine ⟨1, 1, by norm_num, ?_, ?_⟩
    · norm_num
      linarith
    · rw [edpBudgetedTripleLogRate, if_pos hsmallx]
      rcases hf 1 with h | h <;> simp [apSum, h]
  · have hlarge : edpBudgetedRateStart x < x := lt_of_not_ge hsmallx
    have hlegacy : edpRateStart < x := (edpRateStart_le_budgetedRateStart x).trans_lt hlarge
    have hrates := edpTripleLogRate_eq_budgeted_of_rateStart_lt hlarge
    by_contra hwitness
    have hsmall : ∀ d m : ℕ, 0 < d → (m * d : ℝ) ≤ x →
        |(apSum f d m : ℝ)| < edpTripleLogRate x := by
      intro d m hd hdm
      have hrate : |(apSum f d m : ℝ)| < edpBudgetedTripleLogRate x :=
        lt_of_not_ge fun hrate => hwitness ⟨d, m, hd, hdm, hrate⟩
      simpa only [hrates] using hrate
    obtain ⟨Ω, mΩ, μ, hμ, G, hG⟩ :=
      finiteFourierReduction_budgeted f hf x hlegacy hsmall
    have hpersistent :=
      finiteVanDerCorputRate_budgeted (μ := μ) G x hlarge hG
    exact (finiteBorweinChoiCoonsRate_budgeted (μ := μ) G x hlarge hG)
      hpersistent

end MoltResearch
