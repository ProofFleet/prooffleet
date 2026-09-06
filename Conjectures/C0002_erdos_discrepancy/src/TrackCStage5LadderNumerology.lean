import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5InnerBandScheduleSharpNumerology
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5InnerBandScheduleSharpCellsWideShifted
import MoltResearch.Discrepancy.EadicCellBrunTitchmarsh

/-!
# Track R L3: exceptional-cell aggregation

The Phase-4 exceptional fit proposes the uniform per-cell share

`1 / (2^(J+4) * cellCount^2)`.

Its stated prime-term reduction would require

`DeltaU^2 <= share * c3 * eps^2 * logP / (24*1024)`.

For the exceptional power interval the e-adic cover has at least a constant
multiple of `logP` cells.  The first algebraic lemmas record the resulting
necessary upper bound on `logP`.  The final section implements the repaired
accounting: reserve half the band for the exceptional level and define every
cell share to be its actual cost divided by the common band budget.  The cell
costs can then be summed before the outer Cauchy factor is paid.
-/

namespace MoltResearch

namespace Tao2015

/-- The lower/upper e-adic index convention used for a prime interval whose
logarithmic endpoints, after multiplication by the cell density, are `a,b`. -/
noncomputable def phase4EadicIndexRange (a b : ℝ) : Finset ℕ :=
  Finset.Ico (⌈a⌉₊ - 1) (⌊b⌋₊ + 1)

/-- The chosen contiguous e-adic index range has at least its real
logarithmic width.  Applied with `a = 2*Nu*log P` and
`b = 2*Nu*log Q`, this is the cell-count lower bound used below. -/
theorem phase4EadicIndexRange_width_le_card
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    b - a ≤ ((phase4EadicIndexRange a b).card : ℝ) := by
  have ha0 : 0 ≤ a := ha.le
  have hb0 : 0 ≤ b := ha0.trans hab
  have hceil1 : 1 ≤ ⌈a⌉₊ := Nat.one_le_ceil_iff.mpr ha
  have hceil : ((⌈a⌉₊ : ℕ) : ℝ) < a + 1 := Nat.ceil_lt_add_one ha0
  have hfloor : b < ((⌊b⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one b
  have hindex : ⌈a⌉₊ - 1 ≤ ⌊b⌋₊ + 1 := by
    have hcast : ((⌈a⌉₊ : ℕ) : ℝ) < ((⌊b⌋₊ + 2 : ℕ) : ℝ) := by
      push_cast
      linarith
    have hnat : ⌈a⌉₊ < ⌊b⌋₊ + 2 := by exact_mod_cast hcast
    omega
  rw [phase4EadicIndexRange, Nat.card_Ico, Nat.cast_sub hindex,
    Nat.cast_add, Nat.cast_one, Nat.cast_sub hceil1, Nat.cast_one]
  linarith

/-- Any exceptional interval with `log Q >= 2*log P` has at least `log P`
cells under the Phase-4 index convention, already at the coarsest admissible
cell density `Nu = 1`. -/
theorem phase4EadicIndexRange_log_lower
    (Nu : ℕ) (logP logQ : ℝ) (hNu : 0 < Nu) (hlogP : 0 < logP)
    (hlogQ : 2 * logP ≤ logQ) :
    logP ≤
      ((phase4EadicIndexRange (2 * (Nu : ℝ) * logP)
        (2 * (Nu : ℝ) * logQ)).card : ℝ) := by
  have hNuR : (1 : ℝ) ≤ Nu := by exact_mod_cast hNu
  have hleft : 0 < 2 * (Nu : ℝ) * logP := by positivity
  have horder : 2 * (Nu : ℝ) * logP ≤ 2 * (Nu : ℝ) * logQ := by
    gcongr
    linarith
  have hwidth := phase4EadicIndexRange_width_le_card
    (2 * (Nu : ℝ) * logP) (2 * (Nu : ℝ) * logQ) hleft horder
  calc
    logP ≤
        2 * (Nu : ℝ) * logQ - 2 * (Nu : ℝ) * logP := by
      nlinarith
    _ ≤ _ := hwidth

/-- The uniform exceptional-cell share prescribed by the Phase-4 schedule. -/
noncomputable def ladderExceptionalCellShare
    (J : ℕ) (cellCount : ℝ) : ℝ :=
  1 / ((2 : ℝ) ^ (J + 4) * cellCount ^ 2)

/-- **L3-5 obstruction.**  If the number of exceptional cells is at least
`logP`, the proposed sufficient prime fit forces

`384 * 2^(J+4) * epsilon'^2 * logP <= c3 * eps^2`.

The factor `384` is exact: `24*1024 / 8^2 = 384`. -/
theorem ladderExceptionalCellShare_prime_fit_forces_log_upper
    (J : ℕ) (cellCount logP c3 eps epsilon' : ℝ)
    (hlogP : 0 < logP) (hcellCount : logP ≤ cellCount)
    (hepsilon' : 0 < epsilon')
    (hfit : (epsilon' / 8) ^ 2 ≤
      ladderExceptionalCellShare J cellCount * c3 * eps ^ 2 * logP /
        (24 * 1024)) :
    384 * (2 : ℝ) ^ (J + 4) * epsilon' ^ 2 * logP ≤ c3 * eps ^ 2 := by
  have hcellCount0 : 0 < cellCount := hlogP.trans_le hcellCount
  have hpow0 : 0 < (2 : ℝ) ^ (J + 4) := by positivity
  have hcountSq : logP ^ 2 ≤ cellCount ^ 2 :=
    pow_le_pow_left₀ hlogP.le hcellCount 2
  have hden : 0 < 24576 * (2 : ℝ) ^ (J + 4) * cellCount ^ 2 := by
    positivity
  have hshape :
      ladderExceptionalCellShare J cellCount * c3 * eps ^ 2 * logP /
          (24 * 1024) =
        (c3 * eps ^ 2 * logP) /
          (24576 * (2 : ℝ) ^ (J + 4) * cellCount ^ 2) := by
    unfold ladderExceptionalCellShare
    ring
  rw [hshape] at hfit
  have hcross :
      (epsilon' / 8) ^ 2 *
          (24576 * (2 : ℝ) ^ (J + 4) * cellCount ^ 2) ≤
        c3 * eps ^ 2 * logP :=
    (le_div_iff₀ hden).mp hfit
  have hlower :
      384 * (2 : ℝ) ^ (J + 4) * epsilon' ^ 2 * logP ^ 2 ≤
        c3 * eps ^ 2 * logP := by
    calc
      384 * (2 : ℝ) ^ (J + 4) * epsilon' ^ 2 * logP ^ 2 =
          (epsilon' / 8) ^ 2 *
            (24576 * (2 : ℝ) ^ (J + 4) * logP ^ 2) := by ring
      _ ≤ (epsilon' / 8) ^ 2 *
            (24576 * (2 : ℝ) ^ (J + 4) * cellCount ^ 2) := by
        gcongr
      _ ≤ c3 * eps ^ 2 * logP := hcross
  apply le_of_mul_le_mul_right _ hlogP
  convert hlower using 1
  all_goals ring

/-- Once `logP` exceeds the forced upper bound, the proposed uniform
exceptional prime fit is impossible.  The failed margin grows at least
linearly in `2^J * logP`. -/
theorem ladderExceptionalCellShare_prime_fit_fails_of_large_log
    (J : ℕ) (cellCount logP c3 eps epsilon' : ℝ)
    (hlogP : 0 < logP) (hcellCount : logP ≤ cellCount)
    (hepsilon' : 0 < epsilon')
    (hlarge : c3 * eps ^ 2 <
      384 * (2 : ℝ) ^ (J + 4) * epsilon' ^ 2 * logP) :
    ¬ ((epsilon' / 8) ^ 2 ≤
      ladderExceptionalCellShare J cellCount * c3 * eps ^ 2 * logP /
        (24 * 1024)) := by
  intro hfit
  exact (not_le_of_gt hlarge)
    (ladderExceptionalCellShare_prime_fit_forces_log_upper J cellCount logP
      c3 eps epsilon' hlogP hcellCount hepsilon' hfit)

/-- **Share-independent form of the L3-5 obstruction.**  Suppose the summed
prime parts of the exceptional cell fits cost at least
`Cp*d^2*E/logQ`, as they do for unit-modulus prime coefficients, and the
e-adic cover has at least `logQ` cells.  The aggregate exceptional share then
forces `16*Cp*2^(J+1)*d^2*E <= c3*eps^2`.

Thus redistributing the cell shares cannot repair the geometric loss. -/
theorem ladderExceptionalAggregate_prime_fit_forces_level_upper
    (J : ℕ) (Cp cellCount logQ totalShareCost budget d E c3 eps : ℝ)
    (hCp0 : 0 ≤ Cp)
    (hlogQ : 0 < logQ) (hcellCount : logQ ≤ cellCount)
    (hd : 0 < d) (hE : 0 < E)
    (hprime : Cp * d ^ 2 * E / logQ ≤ totalShareCost)
    (haggregate : 2 * cellCount * totalShareCost ≤
      (1 / (2 : ℝ) ^ (J + 1)) * budget)
    (hbudget : budget ≤ c3 * eps ^ 2 / 8) :
    16 * Cp * (2 : ℝ) ^ (J + 1) * d ^ 2 * E ≤ c3 * eps ^ 2 := by
  have htotal0 : 0 ≤ totalShareCost := by
    exact le_trans (by positivity : 0 ≤ Cp * d ^ 2 * E / logQ) hprime
  have hcost : 2 * Cp * d ^ 2 * E ≤ 2 * cellCount * totalShareCost := by
    calc
      2 * Cp * d ^ 2 * E =
          2 * logQ * (Cp * d ^ 2 * E / logQ) := by field_simp
      _ ≤ 2 * logQ * totalShareCost :=
        mul_le_mul_of_nonneg_left hprime (by positivity)
      _ ≤ 2 * cellCount * totalShareCost := by gcongr
  have hpow0 : 0 < (2 : ℝ) ^ (J + 1) := by positivity
  have hscaled : 2 * Cp * d ^ 2 * E ≤
      c3 * eps ^ 2 / (8 * (2 : ℝ) ^ (J + 1)) := by
    calc
      2 * Cp * d ^ 2 * E ≤ 2 * cellCount * totalShareCost := hcost
      _ ≤ (1 / (2 : ℝ) ^ (J + 1)) * budget := haggregate
      _ ≤ (1 / (2 : ℝ) ^ (J + 1)) * (c3 * eps ^ 2 / 8) := by
        gcongr
      _ = c3 * eps ^ 2 / (8 * (2 : ℝ) ^ (J + 1)) := by ring
  have hden : 0 < 8 * (2 : ℝ) ^ (J + 1) := by positivity
  have := (le_div_iff₀ hden).mp hscaled
  nlinarith

/-- With the sharp envelope's fixed floor `d = epsilon'/8`, the preceding
necessary condition has the simpler exact coefficient `16`. -/
theorem ladderExceptionalAggregate_fixed_floor_forces_level_upper
    (J : ℕ) (Cp cellCount logQ totalShareCost budget E c3 eps epsilon' : ℝ)
    (hCp0 : 0 ≤ Cp)
    (hlogQ : 0 < logQ) (hcellCount : logQ ≤ cellCount)
    (hE : 0 < E) (hepsilon' : 0 < epsilon')
    (hprime : Cp * (epsilon' / 8) ^ 2 * E / logQ ≤ totalShareCost)
    (haggregate : 2 * cellCount * totalShareCost ≤
      (1 / (2 : ℝ) ^ (J + 1)) * budget)
    (hbudget : budget ≤ c3 * eps ^ 2 / 8) :
    Cp / 4 * (2 : ℝ) ^ (J + 1) * epsilon' ^ 2 * E ≤ c3 * eps ^ 2 := by
  have hraw := ladderExceptionalAggregate_prime_fit_forces_level_upper
    J Cp cellCount logQ totalShareCost budget (epsilon' / 8) E c3 eps hCp0
    hlogQ hcellCount (by positivity) hE hprime haggregate hbudget
  nlinarith

/-! ## The repaired exceptional aggregate -/

/-- The exceptional cell share is its exact cost divided by the common band
budget.  This makes the pointwise fit an identity; only the sum of the actual
cell costs remains to be estimated. -/
noncomputable def exceptionalCellKappa (cost budget : ℝ) : ℝ := cost / budget

theorem exceptionalCellKappa_mul_budget (cost budget : ℝ) (hbudget : budget ≠ 0) :
    exceptionalCellKappa cost budget * budget = cost := by
  unfold exceptionalCellKappa
  field_simp

theorem sum_exceptionalCellKappa_mul_budget
    (I : Finset ℕ) (cost : ℕ → ℝ) (budget : ℝ) (hbudget : budget ≠ 0) :
    (∑ v ∈ I, exceptionalCellKappa (cost v) budget) * budget =
      ∑ v ∈ I, cost v := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  exact exceptionalCellKappa_mul_budget (cost v) budget hbudget

/-- With actual-cost shares, every pointwise fit is an equality and the
schedule aggregate is exactly the aggregate inequality for the costs. -/
theorem exceptional_actual_cost_schedule
    (I : Finset ℕ) (cost : ℕ → ℝ) (budget wide : ℝ)
    (hbudget : budget ≠ 0)
    (haggregate :
      2 * (I.card : ℝ) * (∑ v ∈ I, cost v) + wide ≤ budget / 2) :
    (∀ v, cost v ≤ exceptionalCellKappa (cost v) budget * budget) ∧
      2 * (I.card : ℝ) *
          (∑ v ∈ I, exceptionalCellKappa (cost v) budget) * budget + wide ≤
        budget / 2 := by
  constructor
  · intro v
    exact (exceptionalCellKappa_mul_budget (cost v) budget hbudget).ge
  · calc
      2 * (I.card : ℝ) *
            (∑ v ∈ I, exceptionalCellKappa (cost v) budget) * budget + wide =
          2 * (I.card : ℝ) *
            ((∑ v ∈ I, exceptionalCellKappa (cost v) budget) * budget) + wide := by
              ring
      _ = 2 * (I.card : ℝ) * (∑ v ∈ I, cost v) + wide := by
            rw [sum_exceptionalCellKappa_mul_budget I cost budget hbudget]
      _ ≤ budget / 2 := haggregate

/-- The prime large-values coefficient of one cell is controlled by its
harmonic prime mass.  This retains one factor of `1/log P` while allowing the
cell masses to be summed before the outer Cauchy factor is applied. -/
theorem exceptional_prime_factor_le_harmonic
    (Cp : ℝ) (hCp0 : 0 ≤ Cp) (Y : Finset ℕ) (Pc : ℕ) (hPc : 2 ≤ Pc)
    (hlo : ∀ p ∈ Y, Pc < p) (g : ℕ → ℂ) (hg : ∀ p, ‖g p‖ ≤ 1)
    (L : ℝ) (hL : 0 < L) (hlog : L ≤ Real.log (Pc : ℝ)) :
    Cp * (∑ p ∈ Y, ‖g p‖ ^ 2 / (p : ℝ) ^ 2) * (Pc : ℝ) /
        Real.log (Pc : ℝ) ≤
      Cp / L * ∑ p ∈ Y, (1 : ℝ) / p := by
  have hPc0 : (0 : ℝ) < Pc := by positivity
  have hlogPc : 0 < Real.log (Pc : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Pc by omega))
  have hsum :
      (∑ p ∈ Y, ‖g p‖ ^ 2 / (p : ℝ) ^ 2) * (Pc : ℝ) ≤
        ∑ p ∈ Y, (1 : ℝ) / p := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro p hp
    have hp0 : (0 : ℝ) < p := by
      exact_mod_cast (lt_trans (by omega : 0 < Pc) (hlo p hp))
    have hnorm : ‖g p‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg (g p), hg p]
    have hPcp : (Pc : ℝ) ≤ p := by exact_mod_cast (hlo p hp).le
    have hnum : ‖g p‖ ^ 2 * (Pc : ℝ) ≤ 1 * (p : ℝ) :=
      mul_le_mul hnorm hPcp (by positivity) (by norm_num)
    calc
      ‖g p‖ ^ 2 / (p : ℝ) ^ 2 * (Pc : ℝ) =
          (‖g p‖ ^ 2 * (Pc : ℝ)) / (p : ℝ) ^ 2 := by ring
      _ ≤ (p : ℝ) / (p : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (by simpa using hnum) (by positivity)
      _ = (1 : ℝ) / p := by field_simp
  have hmass0 : 0 ≤ ∑ p ∈ Y, (1 : ℝ) / p :=
    Finset.sum_nonneg fun p hp => by positivity
  have hnum :
      Cp * (∑ p ∈ Y, ‖g p‖ ^ 2 / (p : ℝ) ^ 2) * (Pc : ℝ) ≤
        Cp * (∑ p ∈ Y, (1 : ℝ) / p) := by
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hsum hCp0
  calc
    Cp * (∑ p ∈ Y, ‖g p‖ ^ 2 / (p : ℝ) ^ 2) * (Pc : ℝ) /
          Real.log (Pc : ℝ)
        ≤ Cp * (∑ p ∈ Y, (1 : ℝ) / p) / Real.log (Pc : ℝ) := by
          exact div_le_div_of_nonneg_right hnum hlogPc.le
    _ ≤ Cp * (∑ p ∈ Y, (1 : ℝ) / p) / L := by
          exact div_le_div_of_nonneg_left (by positivity) hL hlog
    _ = Cp / L * ∑ p ∈ Y, (1 : ℝ) / p := by ring

/-- The e-adic cells are disjoint, so their harmonic masses sum to the mass
of the covered prime level exactly. -/
theorem sum_eadicCell_harmonic_eq
    (I P : Finset ℕ) (N : ℕ)
    (hcov : I.biUnion (eadicCell P (2 * N)) = P) :
    ∑ v ∈ I, ∑ p ∈ eadicCell P (2 * N) v, (1 : ℝ) / p =
      ∑ p ∈ P, (1 : ℝ) / p := by
  have hdisj : (I : Set ℕ).PairwiseDisjoint (eadicCell P (2 * N)) := by
    intro v hv r hr hvr
    exact eadicCell_disjoint P (2 * N) hvr
  calc
    ∑ v ∈ I, ∑ p ∈ eadicCell P (2 * N) v, (1 : ℝ) / p =
        ∑ p ∈ I.biUnion (eadicCell P (2 * N)), (1 : ℝ) / p :=
      (Finset.sum_biUnion hdisj).symm
    _ = ∑ p ∈ P, (1 : ℝ) / p := by rw [hcov]

/-- Aggregate prime-part bound after summing the actual cell costs.  If the
number of cells is at most `Ccells*N*R*L`, the outer Cauchy factor costs only
the fixed quantity `8*Cp*Ccells*N*R*d²*E`; no geometric factor in the number of
ordinary ladder levels remains. -/
theorem exceptional_prime_aggregate_le
    (Cp : ℝ) (hCp0 : 0 ≤ Cp) (I : Finset ℕ) (Y : ℕ → Finset ℕ) (Pc : ℕ → ℕ)
    (hPc : ∀ v ∈ I, 2 ≤ Pc v) (hlo : ∀ v ∈ I, ∀ p ∈ Y v, Pc v < p)
    (g : ℕ → ℂ) (hg : ∀ p, ‖g p‖ ≤ 1)
    (Delta Gamma : ℕ → ℝ) (d L E N R Ccells : ℝ)
    (hL : 0 < L) (hE : 0 ≤ E)
    (hDelta0 : ∀ v ∈ I, 0 ≤ Delta v)
    (hDelta : ∀ v ∈ I, Delta v ≤ d)
    (hGamma0 : ∀ v ∈ I, 0 ≤ Gamma v)
    (hGamma : ∀ v ∈ I, Gamma v ≤ 1)
    (hlog : ∀ v ∈ I, L ≤ Real.log (Pc v : ℝ))
    (hmass : ∑ v ∈ I, ∑ p ∈ Y v, (1 : ℝ) / p ≤ E)
    (hcard : (I.card : ℝ) ≤ Ccells * N * R * L) :
    2 * (I.card : ℝ) *
        (∑ v ∈ I, 2 * Delta v ^ 2 *
          ((Cp * (∑ p ∈ Y v, ‖g p‖ ^ 2 / (p : ℝ) ^ 2) *
              (Pc v : ℝ) / Real.log (Pc v : ℝ)) * (1 + Gamma v))) ≤
      8 * Cp * Ccells * N * R * d ^ 2 * E := by
  have hcell : ∀ v ∈ I,
      2 * Delta v ^ 2 *
          ((Cp * (∑ p ∈ Y v, ‖g p‖ ^ 2 / (p : ℝ) ^ 2) *
              (Pc v : ℝ) / Real.log (Pc v : ℝ)) * (1 + Gamma v)) ≤
        4 * Cp * d ^ 2 / L * ∑ p ∈ Y v, (1 : ℝ) / p := by
    intro v hv
    have hDeltaSq : Delta v ^ 2 ≤ d ^ 2 :=
      pow_le_pow_left₀ (hDelta0 v hv) (hDelta v hv) 2
    have hfactor := exceptional_prime_factor_le_harmonic
      Cp hCp0 (Y v) (Pc v) (hPc v hv) (hlo v hv) g hg L hL (hlog v hv)
    have hmassv0 : 0 ≤ ∑ p ∈ Y v, (1 : ℝ) / p :=
      Finset.sum_nonneg fun p hp => by positivity
    have hfactor0 : 0 ≤ Cp *
        (∑ p ∈ Y v, ‖g p‖ ^ 2 / (p : ℝ) ^ 2) *
          (Pc v : ℝ) / Real.log (Pc v : ℝ) := by
      have := hPc v hv
      positivity
    have hGamma1 : 0 ≤ 1 + Gamma v := by linarith [hGamma0 v hv]
    have hGamma2 : 1 + Gamma v ≤ 2 := by linarith [hGamma v hv]
    have hrhs0 : 0 ≤ Cp / L * ∑ p ∈ Y v, (1 : ℝ) / p := by
      positivity
    have hproduct :
        (Cp * (∑ p ∈ Y v, ‖g p‖ ^ 2 / (p : ℝ) ^ 2) *
              (Pc v : ℝ) / Real.log (Pc v : ℝ)) * (1 + Gamma v) ≤
          (Cp / L * ∑ p ∈ Y v, (1 : ℝ) / p) * 2 :=
      mul_le_mul hfactor hGamma2 hGamma1 hrhs0
    have hproduct0 : 0 ≤
        (Cp * (∑ p ∈ Y v, ‖g p‖ ^ 2 / (p : ℝ) ^ 2) *
              (Pc v : ℝ) / Real.log (Pc v : ℝ)) * (1 + Gamma v) :=
      mul_nonneg hfactor0 hGamma1
    calc
      2 * Delta v ^ 2 *
          ((Cp * (∑ p ∈ Y v, ‖g p‖ ^ 2 / (p : ℝ) ^ 2) *
              (Pc v : ℝ) / Real.log (Pc v : ℝ)) * (1 + Gamma v))
          ≤ 2 * d ^ 2 *
              ((Cp * (∑ p ∈ Y v, ‖g p‖ ^ 2 / (p : ℝ) ^ 2) *
                (Pc v : ℝ) / Real.log (Pc v : ℝ)) * (1 + Gamma v)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hDeltaSq (by norm_num)) hproduct0
      _ ≤ 2 * d ^ 2 * ((Cp / L * ∑ p ∈ Y v, (1 : ℝ) / p) * 2) := by
            exact mul_le_mul_of_nonneg_left hproduct (by positivity)
      _ = 4 * Cp * d ^ 2 / L * ∑ p ∈ Y v, (1 : ℝ) / p := by ring
  have hsum := Finset.sum_le_sum hcell
  have hsum' :
      ∑ v ∈ I, 2 * Delta v ^ 2 *
          ((Cp * (∑ p ∈ Y v, ‖g p‖ ^ 2 / (p : ℝ) ^ 2) *
              (Pc v : ℝ) / Real.log (Pc v : ℝ)) * (1 + Gamma v)) ≤
        4 * Cp * d ^ 2 / L * E := by
    calc
      _ ≤ ∑ v ∈ I, 4 * Cp * d ^ 2 / L * ∑ p ∈ Y v, (1 : ℝ) / p := hsum
      _ = 4 * Cp * d ^ 2 / L *
          (∑ v ∈ I, ∑ p ∈ Y v, (1 : ℝ) / p) := by
            rw [Finset.mul_sum]
      _ ≤ 4 * Cp * d ^ 2 / L * E := by gcongr
  have hsum0 : 0 ≤ 4 * Cp * d ^ 2 / L * E := by positivity
  calc
    2 * (I.card : ℝ) *
        (∑ v ∈ I, 2 * Delta v ^ 2 *
          ((Cp * (∑ p ∈ Y v, ‖g p‖ ^ 2 / (p : ℝ) ^ 2) *
              (Pc v : ℝ) / Real.log (Pc v : ℝ)) * (1 + Gamma v)))
        ≤ 2 * (I.card : ℝ) * (4 * Cp * d ^ 2 / L * E) := by gcongr
    _ ≤ 2 * (Ccells * N * R * L) * (4 * Cp * d ^ 2 / L * E) := by gcongr
    _ = 8 * Cp * Ccells * N * R * d ^ 2 * E := by
      field_simp [ne_of_gt hL]
      ring

end Tao2015

end MoltResearch
