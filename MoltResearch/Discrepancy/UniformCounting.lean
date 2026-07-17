import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic

/-!
# Discrepancy: the uniform counting dictionary

Track C, Elliott campaign (`Problems/tao2015_derivation_c.md`, issue #2946, E6e-1):
the bridge between finite counting and measure theory that the Hoeffding step
runs through — on a finite discrete space every set is measurable, the uniform
measure of a set is its normalized cardinality, the product of uniforms assigns
each point `1/|Π|`, and coordinate evaluations are independent.
-/

namespace MoltResearch

open MeasureTheory

section Discrete

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- On a finite type with measurable singletons, every set is measurable. -/
theorem measurableSet_of_finite (S : Set α) : MeasurableSet S :=
  (Set.toFinite S).measurableSet

/-- Every map out of a finite discrete space is measurable. -/
theorem measurable_of_finite {β : Type*} [MeasurableSpace β] (f : α → β) :
    Measurable f := fun _ _ => measurableSet_of_finite _

/-- Finite additivity over the points of a `Finset`. -/
theorem measure_coe_finset_eq_sum (μ : Measure α) (s : Finset α) :
    μ ↑s = ∑ x ∈ s, μ {x} := by
  have hset : (↑s : Set α) = ⋃ x ∈ s, ({x} : Set α) := by
    ext y
    simp
  rw [hset, measure_biUnion_finset ?_ fun x _ => measurableSet_singleton x]
  intro x _ y _ hxy
  simp [Set.disjoint_singleton_left, hxy]

theorem measureReal_coe_finset_eq_sum (μ : Measure α) [IsFiniteMeasure μ]
    (s : Finset α) : μ.real ↑s = ∑ x ∈ s, μ.real {x} := by
  rw [measureReal_def, measure_coe_finset_eq_sum]
  rw [ENNReal.toReal_sum fun x _ => measure_ne_top μ {x}]
  rfl

end Discrete

section Uniform

variable (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- The uniform singleton mass is `1/|α|`. -/
theorem uniform_real_singleton (x : α) :
    ((PMF.uniformOfFintype α).toMeasure).real {x} = 1 / Fintype.card α := by
  rw [measureReal_def,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x),
    PMF.uniformOfFintype_apply]
  rw [ENNReal.toReal_inv]
  simp [one_div]

/-- **The uniform counting dictionary**: the uniform probability of an event is
the number of favourable points over the number of points. -/
theorem uniform_real_filter (p : α → Prop) [DecidablePred p] :
    ((PMF.uniformOfFintype α).toMeasure).real {x | p x}
      = ((Finset.univ.filter p).card : ℝ) / Fintype.card α := by
  have hset : {x | p x} = ↑(Finset.univ.filter p) := by
    ext y
    simp
  rw [hset, measureReal_coe_finset_eq_sum]
  rw [Finset.sum_congr rfl fun x _ => uniform_real_singleton α x,
    Finset.sum_const, nsmul_eq_mul]
  ring

end Uniform

section Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
  [∀ i, Nonempty (Ω i)] [∀ i, MeasurableSpace (Ω i)]
  [∀ i, MeasurableSingletonClass (Ω i)]

/-- The product of the coordinate uniforms — the sampling space of the
Hoeffding step. -/
noncomputable def uniformPi (Ω : ι → Type*) [∀ i, Fintype (Ω i)]
    [∀ i, Nonempty (Ω i)] [∀ i, MeasurableSpace (Ω i)] :
    Measure (Π i, Ω i) :=
  Measure.pi fun i => (PMF.uniformOfFintype (Ω i)).toMeasure

instance : IsProbabilityMeasure (uniformPi Ω) := by
  rw [uniformPi]
  infer_instance

/-- The product uniform assigns each point mass `∏ 1/|Ω i|`. -/
theorem uniformPi_singleton (ω : Π i, Ω i) :
    uniformPi Ω {ω} = ∏ i, ((PMF.uniformOfFintype (Ω i)).toMeasure) {ω i} := by
  rw [uniformPi, ← Set.univ_pi_singleton, Measure.pi_pi]

theorem uniformPi_real_singleton (ω : Π i, Ω i) :
    (uniformPi Ω).real {ω} = 1 / Fintype.card (Π i, Ω i) := by
  rw [measureReal_def, uniformPi_singleton, ENNReal.toReal_prod]
  have hper : ∀ i, (((PMF.uniformOfFintype (Ω i)).toMeasure) {ω i}).toReal
      = 1 / Fintype.card (Ω i) := fun i => uniform_real_singleton (Ω i) (ω i)
  rw [Finset.prod_congr rfl fun i _ => hper i, Fintype.card_pi]
  push_cast
  rw [Finset.prod_div_distrib]
  simp

/-- **The product counting dictionary**. -/
theorem uniformPi_real_filter (p : (Π i, Ω i) → Prop) [DecidablePred p] :
    (uniformPi Ω).real {ω | p ω}
      = ((Finset.univ.filter p).card : ℝ) / Fintype.card (Π i, Ω i) := by
  have hset : {ω | p ω} = ↑(Finset.univ.filter p) := by
    ext y
    simp
  rw [hset, measureReal_coe_finset_eq_sum]
  rw [Finset.sum_congr rfl fun ω _ => uniformPi_real_singleton ω,
    Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Coordinate evaluations are independent** under the product uniform. -/
theorem iIndepFun_eval_uniformPi (f : Π i, Ω i → ℝ) :
    ProbabilityTheory.iIndepFun (fun i ω => f i (ω i)) (uniformPi Ω) := by
  rw [uniformPi]
  exact ProbabilityTheory.iIndepFun_pi fun i => (measurable_of_finite (f i)).aemeasurable

end Product

end MoltResearch
