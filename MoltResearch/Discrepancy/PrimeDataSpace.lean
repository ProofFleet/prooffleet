import MoltResearch.Discrepancy.CMOfPrimes
import MoltResearch.Discrepancy.MultiplicativeC
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Discrepancy: the compact space of unimodular prime data

Tao 2015 §2 (arXiv:1509.05363, `Problems/tao2015_derivation_c.md`, issue #2920): the
paper's space `𝓜` of completely multiplicative `S¹`-valued functions, realized as the
compact space of their prime data.

* `PrimeData := Nat.Primes → Circle` — compact (Tychonoff) and metrizable (countable
  product of metric spaces); the ambient space for the limiting law.
* `toCM ω = cmOfPrimes (p ↦ ω_p)` — the encoded completely multiplicative function;
  completely multiplicative and unimodular for **every** `ω`.
* `continuous_toCM_apply` — each evaluation `ω ↦ toCM ω j` is continuous (a finite
  product of coordinate powers).
* `windowFunctional n : PrimeData →ᵇ ℝ` — the test functional `ω ↦ ‖∑_{j≤n} toCM ω j‖²`
  as a bounded continuous function (compactness supplies the bound), ready for the
  weak-convergence step (`ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`).
-/

namespace MoltResearch

open Finset

/-- The compact metrizable space of unimodular prime data — the paper's `𝓜`. -/
abbrev PrimeData : Type := Nat.Primes → Circle

/-- The coercion `Circle → ℂ` is continuous (the topology is induced). -/
private lemma continuous_circle_coe : Continuous fun z : Circle => (z : ℂ) :=
  continuous_induced_dom

/-- The completely multiplicative function encoded by a point of `PrimeData`. -/
noncomputable def toCM (ω : PrimeData) : ℕ → ℂ :=
  cmOfPrimes fun p => if h : p.Prime then (ω ⟨p, h⟩ : ℂ) else 1

/-- Every encoded function is completely multiplicative. -/
theorem toCM_completelyMultiplicativeC (ω : PrimeData) :
    CompletelyMultiplicativeC (toCM ω) :=
  cmOfPrimes_completelyMultiplicativeC _

/-- Every encoded function is unimodular. -/
theorem toCM_unimodular (ω : PrimeData) : Unimodular (toCM ω) := by
  refine cmOfPrimes_unimodular fun p hp => ?_
  rw [dif_pos hp]
  exact Circle.norm_coe _

/-- Each evaluation `ω ↦ toCM ω j` is continuous: a finite product of coordinate
powers. -/
theorem continuous_toCM_apply (j : ℕ) : Continuous fun ω : PrimeData => toCM ω j := by
  have hshow : (fun ω : PrimeData => toCM ω j)
      = fun ω : PrimeData => ∏ p ∈ j.factorization.support,
          (if h : p.Prime then ((ω ⟨p, h⟩ : ℂ)) else 1) ^ j.factorization p := rfl
  rw [hshow]
  refine continuous_finset_prod _ fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors
    (by rwa [Nat.support_factorization] at hp)
  simp only [dif_pos hpp]
  exact ((continuous_circle_coe.comp (continuous_apply (⟨p, hpp⟩ : Nat.Primes))).pow _)

/-- The window functional `ω ↦ ‖∑_{j ≤ n} toCM ω j‖²` as a bounded continuous function
(compactness supplies the bound). -/
noncomputable def windowFunctional (n : ℕ) :
    BoundedContinuousFunction PrimeData ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun ω => ‖apSumC (toCM ω) 1 n‖ ^ 2, by
      refine Continuous.pow (Continuous.norm ?_) 2
      unfold apSumC
      exact continuous_finset_sum _ fun i _ => continuous_toCM_apply _⟩

@[simp] theorem windowFunctional_apply (n : ℕ) (ω : PrimeData) :
    windowFunctional n ω = ‖apSumC (toCM ω) 1 n‖ ^ 2 := rfl

/-- The window functionals are nonnegative. -/
theorem windowFunctional_nonneg (n : ℕ) (ω : PrimeData) :
    0 ≤ windowFunctional n ω := by
  rw [windowFunctional_apply]
  positivity

end MoltResearch
