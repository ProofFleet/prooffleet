import MoltResearch.Discrepancy.Multiplicative
import MoltResearch.Discrepancy.SignSequenceCoercions
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Nat.Squarefree
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.InfinitePi

/-!
# Erdős Problem 1144: random completely multiplicative functions

This file fixes the random model and states the open problem.  The sample space has one
Boolean coordinate for each prime.  Each coordinate has the uniform probability mass
function on `Bool`, and `Measure.infinitePi` supplies their countable product measure.

The proved results below concern only the construction: the coordinate signs are fair and
independent, and their extension through `Nat.factorization` is completely multiplicative
and sign-valued.  `Erdos1144` itself is a `def` because the fluctuation assertion remains open.

We also give separately named squarefree-supported Rademacher and Steinhaus extensions.  In
particular, `rademacherSquarefree` vanishes off the squarefree integers, whereas `randomCM`
retains every prime-power contribution.
-/

namespace MoltResearch

open MeasureTheory
open scoped BigOperators

/-- Prime-indexed Boolean samples for the random completely multiplicative model. -/
abbrev Ω : Type := Nat.Primes → Bool

/-- A fair coin: the uniform probability mass function on `Bool`, viewed as a measure. -/
noncomputable def fairCoin : Measure Bool :=
  (PMF.uniformOfFintype Bool).toMeasure

instance fairCoin_isProbabilityMeasure : IsProbabilityMeasure fairCoin := by
  unfold fairCoin
  infer_instance

/-- Each of the two Boolean outcomes has mass `1 / 2`. -/
theorem fairCoin_singleton (b : Bool) : fairCoin {b} = (1 : ENNReal) / 2 := by
  unfold fairCoin
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b),
    PMF.uniformOfFintype_apply]
  norm_num

/-- The product of fair-coin laws over all primes, constructed by `Measure.infinitePi`. -/
noncomputable def randomCMMeasure : Measure Ω :=
  Measure.infinitePi fun _ : Nat.Primes ↦ fairCoin

/-- The infinite product of the coordinate probability measures is a probability measure. -/
instance randomCMMeasure_isProbabilityMeasure : IsProbabilityMeasure randomCMMeasure := by
  unfold randomCMMeasure
  infer_instance

/-- The decoded prime signs are independent under the product measure. -/
theorem iIndepFun_primeSign :
    ProbabilityTheory.iIndepFun
      (fun p (omega : Ω) ↦ boolToSign (omega p)) randomCMMeasure := by
  exact ProbabilityTheory.iIndepFun_infinitePi
    (P := fun _ : Nat.Primes ↦ fairCoin) (fun _ ↦ Measurable.of_discrete)

/-- Decode the coordinate at a prime, using `1` at irrelevant non-prime arguments. -/
def primeSign (omega : Ω) (p : ℕ) : ℤ :=
  if hp : p.Prime then boolToSign (omega ⟨p, hp⟩) else 1

/-- The completely multiplicative extension of the sampled prime signs.

As elsewhere in the discrepancy API, the value at `0` is harmless junk: its empty
factorization gives `1`, while multiplicativity is asserted only for nonzero inputs.
-/
noncomputable def randomCM (omega : Ω) (n : ℕ) : ℤ :=
  n.factorization.prod fun p k ↦ primeSign omega p ^ k

@[simp] theorem randomCM_zero (omega : Ω) : randomCM omega 0 = 1 := by
  simp [randomCM]

@[simp] theorem randomCM_one (omega : Ω) : randomCM omega 1 = 1 := by
  simp [randomCM]

/-- On a prime, the extension recovers the sampled sign. -/
theorem randomCM_apply_prime (omega : Ω) {p : ℕ} (hp : p.Prime) :
    randomCM omega p = boolToSign (omega ⟨p, hp⟩) := by
  unfold randomCM
  have hprod : (Finsupp.single p 1).prod (fun q k ↦ primeSign omega q ^ k) =
      primeSign omega p ^ 1 :=
    Finsupp.prod_single_index (pow_zero (primeSign omega p))
  rw [Nat.Prime.factorization hp, hprod, pow_one]
  simp [primeSign, hp]

/-- Every sampled extension is completely multiplicative on the positive naturals. -/
theorem randomCM_completelyMultiplicative (omega : Ω) :
    CompletelyMultiplicative (randomCM omega) := by
  intro a b ha hb
  unfold randomCM
  rw [Nat.factorization_mul ha hb]
  exact Finsupp.prod_add_index' (fun p ↦ pow_zero (primeSign omega p))
    fun p k l ↦ pow_add (primeSign omega p) k l

private theorem primeSign_natAbs (omega : Ω) (p : ℕ) :
    Int.natAbs (primeSign omega p) = 1 := by
  unfold primeSign
  split_ifs with hp
  · cases omega ⟨p, hp⟩ <;> simp [boolToSign]
  · simp

/-- Every sampled extension is `±1`-valued, including at the junk input `0`. -/
theorem randomCM_isSignSequence (omega : Ω) : IsSignSequence (randomCM omega) := by
  rw [isSignSequence_iff_forall_natAbs_eq_one]
  intro n
  unfold randomCM Finsupp.prod
  change Int.natAbsHom
      (∏ p ∈ n.factorization.support, primeSign omega p ^ n.factorization p) = 1
  rw [map_prod Int.natAbsHom]
  exact Finset.prod_eq_one fun p _ ↦ by
    change Int.natAbs (primeSign omega p ^ n.factorization p) = 1
    rw [Int.natAbs_pow, primeSign_natAbs, one_pow]

/-- The partial sum `S(N) = ∑_{1 ≤ m ≤ N} f(m)`. -/
noncomputable def partialSum (omega : Ω) (N : ℕ) : ℤ :=
  ∑ m ∈ Finset.Icc 1 N, randomCM omega m

/-- The squarefree-supported Rademacher model (Erdős Problem 520), kept separate from
the completely multiplicative model of Problem 1144. -/
noncomputable def rademacherSquarefree (omega : Ω) (n : ℕ) : ℤ :=
  if Squarefree n then randomCM omega n else 0

/-- Prime-indexed unit-circle samples for the Steinhaus model. -/
abbrev SteinhausOmega : Type := Nat.Primes → Circle

/-- The Steinhaus completely multiplicative extension.  Its prime coordinates take values
on the whole unit circle rather than only in `{−1, 1}`. -/
noncomputable def steinhausCM (omega : SteinhausOmega) (n : ℕ) : ℂ :=
  n.factorization.prod fun p k ↦
    (if hp : p.Prime then (omega ⟨p, hp⟩ : ℂ) else 1) ^ k

/-- Erdős Problem 1144, in the frequent-exceedance form of an infinite limsup.

For almost every sample, every real height is exceeded at arbitrarily large indices by
`S(N) / √N`.  This is one-sided: large negative values alone do not satisfy the statement.
-/
def Erdos1144 : Prop :=
  ∀ᵐ omega ∂randomCMMeasure, ∀ M : ℝ, ∃ᶠ N : ℕ in Filter.atTop,
    M ≤ (partialSum omega N : ℝ) / Real.sqrt N

end MoltResearch
