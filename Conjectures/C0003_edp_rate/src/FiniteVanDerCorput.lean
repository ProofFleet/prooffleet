import Conjectures.C0003_edp_rate.src.ElliottThresholds
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite van der Corput package: revised finite-cutoff obstruction

The A6 cutoff-local Markov estimate needs the moment-fit inequality `X + H ≤ L`, where
`L` is the last index supplied by `FiniteSecondMomentBound` and `H` is the positive van der
Corput window length.  The A3 target `FinitePersistentPretentious`, however, asks for the
pretentiousness estimate at every `X` through the same endpoint `L`.

**Blocked:** at `X = L` these two requirements give `L + H ≤ L`, while
`one_le_edpVdCWindowLength` proves `1 ≤ H`.  Thus no starting scale `X₀ ≤ L` makes the A6
consumer applicable on the full interval required by the current interface.  This file
formalizes that exact failing inequality and does not install a
`FiniteVanDerCorputRateAssumption` instance.

The A3' repair shortens the requested interval, so the historical endpoint contradiction no
longer applies to the active target.  It leaves a separate nonempty-window obligation:
`1 + H(x,ε) ≤ edpAnalysisCutoff x`.  The current fixed start scale does not imply this.

**Blocked (A7'):** at the concrete outer scale `x = 10^10`, which is already strictly above
`edpRateStart`, the source-budget schedule has `edpAnalysisCutoff x ≤ 2`.  Every admissible
accuracy `0 < ε ≤ 1` has `8 ≤ edpPersistentWindowLength x ε`, while the repaired
target requires `1 ≤ X₀` and `X₀ + H ≤ edpAnalysisCutoff x`.  The theorems below prove
these inequalities and exhibit a deterministic completely multiplicative law satisfying the
finite moment premise through that cutoff.  Consequently the active
`FiniteVanDerCorputRateAssumption .budgeted` is false as stated; no instance is installed.

Repair requires enlarging `edpRateStart` (or making it schedule-dependent) until the Fourier
cutoff leaves the A6 window and subsequent thresholds.  That changes `Reduction.lean`, outside
A7''s sole listed deliverable.
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

/-! ## The revised target still has no window at the fixed start scale -/

/-- Every admissible repaired-interface accuracy makes the reserved A6 window at least `8`.
The lower bound uses only `ε ≤ 1` and the built-in `max C 1`; it is independent of the
unknown Elliott threshold. -/
theorem eight_le_edpPersistentWindowLength {x ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    8 ≤ edpPersistentWindowLength x ε := by
  unfold edpPersistentWindowLength
  apply le_trans ?_ (Nat.le_max_right _ _)
  have hC : (1 : ℝ) ≤ max (edpTripleLogRate x ^ 2 + 1) 1 := le_max_right _ _
  have hdiv : (8 : ℝ) ≤ 8 / ε := by
    rw [le_div_iff₀ hε0]
    nlinarith
  have hreal : (8 : ℝ) ≤ 8 * max (edpTripleLogRate x ^ 2 + 1) 1 / ε :=
    hdiv.trans (div_le_div_of_nonneg_right (by nlinarith) hε0.le)
  have hceil := Nat.le_ceil (8 * max (edpTripleLogRate x ^ 2 + 1) 1 / ε)
  exact_mod_cast hreal.trans hceil

/-- From scale `3` onward, the exponent-box schedule already exceeds `8·10^12`.
This deliberately coarse lower bound is enough to audit the first admissible outer range. -/
theorem eight_trillion_le_edpScheduledSourceBudget {X : ℕ} (hX : 3 ≤ X) :
    8463329722368 ≤ edpScheduledSourceBudget X := by
  let M : ℕ := max 1 (Fintype.card (PrimeIdx X) * Nat.log 2 X * X ^ 2)
  let p2 : PrimeIdx X := ⟨2, Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩⟩
  let p3 : PrimeIdx X := ⟨3, Nat.mem_primesBelow.mpr ⟨by omega, by norm_num⟩⟩
  have hcard : 2 ≤ Fintype.card (PrimeIdx X) := by
    have hsubset : ({2, 3} : Finset ℕ) ⊆ (X + 1).primesBelow := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩
      · exact Nat.mem_primesBelow.mpr ⟨by omega, by norm_num⟩
    rw [show Fintype.card (PrimeIdx X) = (X + 1).primesBelow.card by
      exact Fintype.card_coe _]
    rw [← Finset.card_pair (by norm_num : (2 : ℕ) ≠ 3)]
    exact Finset.card_le_card hsubset
  have hlog : 1 ≤ Nat.log 2 X := by
    exact Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hsq : 9 ≤ X ^ 2 := by nlinarith
  have hexponent : 16 ≤ M - (Nat.log 2 X + 1) := by
    apply Nat.le_sub_of_add_le
    calc
      16 + (Nat.log 2 X + 1) ≤ 18 * Nat.log 2 X := by omega
      _ = (2 * Nat.log 2 X) * 9 := by ring
      _ ≤ (Fintype.card (PrimeIdx X) * Nat.log 2 X) * X ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul hcard le_rfl) hsq
      _ ≤ M := le_max_right _ _
  have hone : ∀ p ∈ (X + 1).primesBelow.attach,
      1 ≤ p.1 ^ (M - (Nat.log 2 X + 1)) := by
    intro p hp
    exact one_le_pow₀ (Nat.prime_of_mem_primesBelow p.2).one_le
  have hp2 : p2 ∈ (X + 1).primesBelow.attach := Finset.mem_attach _ _
  have hp3 : p3 ∈ (X + 1).primesBelow.attach := Finset.mem_attach _ _
  have hpne : p2 ≠ p3 := by
    intro h
    have := congrArg Subtype.val h
    norm_num [p2, p3] at this
  have htwo : 2 ^ 16 ≤ 2 ^ (M - (Nat.log 2 X + 1)) :=
    Nat.pow_le_pow_right (by norm_num) hexponent
  have hthree : 3 ^ 16 ≤ 3 ^ (M - (Nat.log 2 X + 1)) :=
    Nat.pow_le_pow_right (by norm_num) hexponent
  have hprod :
      2 ^ 16 * 3 ^ 16 ≤
        ∏ p ∈ (X + 1).primesBelow.attach,
          p.1 ^ (M - (Nat.log 2 X + 1)) := by
    exact (Nat.mul_le_mul htwo hthree).trans
      (Finset.mul_le_prod hone hp2 hp3 hpne)
  unfold edpScheduledSourceBudget spectralSourceBudget spectralDilationBudget
  change 8463329722368 ≤
    (∏ p ∈ (X + 1).primesBelow.attach,
      p.1 ^ (M - (Nat.log 2 X + 1))) * X
  calc
    8463329722368 = (2 ^ 16 * 3 ^ 16) * 3 := by norm_num
    _ ≤ (∏ p ∈ (X + 1).primesBelow.attach,
        p.1 ^ (M - (Nat.log 2 X + 1))) * X := Nat.mul_le_mul hprod hX

/-- The fixed large-`x` branch starts below the concrete test scale `10^10`. -/
theorem edpRateStart_lt_ten_billion : edpRateStart < (10 ^ 10 : ℝ) := by
  unfold edpRateStart
  have he1 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
  have he3 : Real.exp (3 : ℝ) < 21 := by
    rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    have hp : Real.exp 1 ^ (3 : ℕ) < (2.7182818286 : ℝ) ^ (3 : ℕ) :=
      pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
    exact hp.trans (by norm_num)
  have hee : Real.exp (Real.exp 1) < 21 :=
    (Real.exp_lt_exp.mpr he1).trans he3
  calc
    Real.exp (Real.exp (Real.exp 1)) < Real.exp 21 := Real.exp_lt_exp.mpr hee
    _ = (Real.exp 3) ^ (7 : ℕ) := by
      rw [show (21 : ℝ) = (7 : ℕ) * 3 by norm_num, Real.exp_nat_mul]
    _ < (21 : ℝ) ^ (7 : ℕ) :=
      pow_lt_pow_left₀ he3 (Real.exp_pos 3).le (by norm_num)
    _ < (10 ^ 10 : ℝ) := by norm_num

/-- At `x = 10^10`, every analysis scale `X ≥ 3` violates the exact Fourier source
budget, so the greatest feasible cutoff is at most `2`. -/
theorem edpAnalysisCutoff_ten_billion_le_two :
    edpAnalysisCutoff (10 ^ 10 : ℝ) ≤ 2 := by
  unfold edpAnalysisCutoff
  by_contra hnot
  have hX : 3 ≤ Nat.findGreatest
      (fun X => edpScheduledSourceBudget X ≤ ⌊(10 ^ 10 : ℝ)⌋₊) ⌊(10 ^ 10 : ℝ)⌋₊ := by
    omega
  have hfit : edpScheduledSourceBudget
      (Nat.findGreatest
        (fun X => edpScheduledSourceBudget X ≤ ⌊(10 ^ 10 : ℝ)⌋₊) ⌊(10 ^ 10 : ℝ)⌋₊)
        ≤ ⌊(10 ^ 10 : ℝ)⌋₊ :=
    Nat.findGreatest_spec
      (P := fun X => edpScheduledSourceBudget X ≤ ⌊(10 ^ 10 : ℝ)⌋₊)
      (Nat.zero_le _) (by
      norm_num [edpScheduledSourceBudget, spectralSourceBudget, spectralDilationBudget])
  norm_num at hX hfit
  have hlarge := eight_trillion_le_edpScheduledSourceBudget hX
  omega

/-- The repaired persistent target is empty at the first concrete large-`x` audit point:
the cutoff is at most `2`, while `X₀ + H` is at least `1 + 8`. -/
theorem not_budgetedFinitePersistentPretentious_ten_billion
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (G : StochasticMultiplicative μ) :
    ¬ FinitePersistentPretentious μ G (10 ^ 10 : ℝ) .budgeted := by
  intro h
  change BudgetedFinitePersistentPretentious μ G (10 ^ 10 : ℝ) at h
  rcases h with ⟨K, hK, ε, hε0, hε1, hKε, Q, T, B, hQ1, hQcap,
    hT1, hTcap, hB0, hBcap, X₀, hX₀1, hfit, hpersistent⟩
  have hH : 8 ≤ edpPersistentWindowLength (10 ^ 10 : ℝ) ε :=
    eight_le_edpPersistentWindowLength hε0 hε1
  have hL := edpAnalysisCutoff_ten_billion_le_two
  omega

/-- The Liouville-style completely multiplicative test function used to show that the
finite-moment premise is inhabited at the obstructed cutoff. -/
noncomputable def edpVdCLiouville (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ ArithmeticFunction.cardFactors n

theorem edpVdCLiouville_completelyMultiplicative :
    CompletelyMultiplicativeC edpVdCLiouville := by
  intro a b ha hb
  simp only [edpVdCLiouville, ArithmeticFunction.cardFactors_mul ha hb, pow_add]

theorem edpVdCLiouville_unimodular : Unimodular edpVdCLiouville := by
  intro n
  simp only [edpVdCLiouville, norm_pow, norm_neg, norm_one, one_pow]

/-- The deterministic Liouville law on a one-point probability space. -/
noncomputable def edpVdCLiouvilleLaw :
    StochasticMultiplicative (MeasureTheory.Measure.dirac ()) :=
  StochasticMultiplicative.ofDeterministic _ edpVdCLiouville
    edpVdCLiouville_completelyMultiplicative edpVdCLiouville_unimodular

/-- The test law satisfies the finite second-moment premise at `10^10`: only indices
`0`, `1`, and `2` can occur, and its first two nonempty partial sums are `1` and `0`. -/
theorem edpVdCLiouvilleLaw_finiteSecondMoment_ten_billion :
    FiniteSecondMomentBound (MeasureTheory.Measure.dirac ()) edpVdCLiouvilleLaw
      (10 ^ 10 : ℝ) := by
  intro n hn
  have hn2 : n ≤ 2 := hn.trans edpAnalysisCutoff_ten_billion_le_two
  interval_cases n
  · simp [edpVdCLiouvilleLaw]
    nlinarith [sq_nonneg (edpTripleLogRate (10 ^ 10 : ℝ))]
  · simp [edpVdCLiouvilleLaw, apSumC, edpVdCLiouville,
      ArithmeticFunction.cardFactors_one]
    positivity
  · have hsum : apSumC edpVdCLiouville 1 2 = 0 := by
      unfold apSumC
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp [edpVdCLiouville, ArithmeticFunction.cardFactors_one,
        ArithmeticFunction.cardFactors_apply_prime Nat.prime_two]
    simp [edpVdCLiouvilleLaw, hsum]
    nlinarith [sq_nonneg (edpTripleLogRate (10 ^ 10 : ℝ))]

/-- **A7' obstruction.**  The active repaired van-der-Corput class is inconsistent with
the current fixed `edpRateStart` and source-budget cutoff.  At `x = 10^10` its premise is
inhabited by `edpVdCLiouvilleLaw`, but its budgeted persistent conclusion is empty. -/
theorem not_finiteVanDerCorputRateAssumption_budgeted :
    ¬ FiniteVanDerCorputRateAssumption .budgeted := by
  intro inst
  letI : FiniteVanDerCorputRateAssumption .budgeted := inst
  exact not_budgetedFinitePersistentPretentious_ten_billion
    (MeasureTheory.Measure.dirac ()) edpVdCLiouvilleLaw
    (finiteVanDerCorputRate_budgeted
      (μ := MeasureTheory.Measure.dirac ()) edpVdCLiouvilleLaw (10 ^ 10 : ℝ)
      edpRateStart_lt_ten_billion edpVdCLiouvilleLaw_finiteSecondMoment_ten_billion)

end MoltResearch
