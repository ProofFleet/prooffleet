import MoltResearch.Discrepancy.UniformCounting
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Data.ZMod.QuotientRing

/-!
# Discrepancy: sub-Gaussian bounds on uniform spaces

Track C, Elliott campaign (issue #2946, E6e-2): bounded mean-zero functions on a
finite uniform space are sub-Gaussian (Hoeffding's lemma), and the bound lifts
through coordinate evaluation to the product uniform — the hypotheses of
Mathlib's Hoeffding inequality, assembled for the counting world.
-/

namespace MoltResearch

open MeasureTheory ProbabilityTheory
open scoped NNReal

section UniformIntegral

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- Integration against the uniform measure is averaging. -/
theorem integral_uniform (f : α → ℝ) :
    ∫ x, f x ∂((PMF.uniformOfFintype α).toMeasure)
      = (∑ x, f x) / Fintype.card α := by
  rw [integral_fintype _ (Integrable.of_finite)]
  simp_rw [uniform_real_singleton, smul_eq_mul, one_div_mul_eq_div]
  rw [← Finset.sum_div]

/-- **Hoeffding's lemma on a uniform space**: a `[-c, c]`-bounded function with
zero sum is sub-Gaussian with parameter `c²`. -/
theorem hasSubgaussianMGF_uniform (f : α → ℝ) {c : ℝ≥0}
    (hbound : ∀ x, f x ∈ Set.Icc (-(c : ℝ)) c) (hmean : ∑ x, f x = 0) :
    HasSubgaussianMGF f (c ^ 2) ((PMF.uniformOfFintype α).toMeasure) := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := (PMF.uniformOfFintype α).toMeasure) (X := f)
    (measurable_of_finite f).aemeasurable (ae_of_all _ hbound)
    (by rw [integral_uniform, hmean, zero_div])
  have hconst : (‖(c : ℝ) - -(c : ℝ)‖₊ / 2) ^ 2 = c ^ 2 := by
    have h2 : ((c : ℝ) - -(c : ℝ)) = 2 * (c : ℝ) := by ring
    apply NNReal.coe_injective
    rw [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, h2, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    push_cast
    ring
  rw [hconst] at h
  exact h

end UniformIntegral

section ProductLift

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
  [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] [∀ i, MeasurableSpace (Ω i)]
  [∀ i, MeasurableSingletonClass (Ω i)]

/-- A coordinate-wise sub-Gaussian bound lifts to the product uniform. -/
theorem hasSubgaussianMGF_eval_uniformPi (f : Π i, Ω i → ℝ) (i : ι) {c : ℝ≥0}
    (h : HasSubgaussianMGF (f i) c ((PMF.uniformOfFintype (Ω i)).toMeasure)) :
    HasSubgaussianMGF (fun ω => f i (ω i)) c (uniformPi Ω) := by
  have hmp : (uniformPi Ω).map (fun ω => ω i)
      = (PMF.uniformOfFintype (Ω i)).toMeasure := by
    rw [uniformPi]
    exact (measurePreserving_eval _ i).map_eq
  have h' : HasSubgaussianMGF (f i ∘ fun ω => ω i) c (uniformPi Ω) :=
    HasSubgaussianMGF.of_map (measurable_of_finite _).aemeasurable
      (by rw [hmp]; exact h)
  exact h'

/-- **Hoeffding's inequality in counting form**: bounded mean-zero coordinate
functions on the product uniform deviate exponentially rarely. -/
theorem card_deviation_le_uniformPi (f : Π i, Ω i → ℝ) (c : ι → ℝ≥0)
    (hbound : ∀ i, ∀ x, f i x ∈ Set.Icc (-(c i : ℝ)) (c i))
    (hmean : ∀ i, ∑ x, f i x = 0) {ε : ℝ} (hε : 0 ≤ ε) :
    ((Finset.univ.filter
        (fun ω : Π i, Ω i => ε ≤ ∑ i, f i (ω i))).card : ℝ)
        / Fintype.card (Π i, Ω i)
      ≤ Real.exp (-ε ^ 2 / (2 * ((∑ i, (c i) ^ 2 : ℝ≥0) : ℝ))) := by
  classical
  have hsub : ∀ i ∈ Finset.univ, HasSubgaussianMGF
      (fun ω : Π j, Ω j => f i (ω i)) ((c i) ^ 2) (uniformPi Ω) := fun i _ =>
    hasSubgaussianMGF_eval_uniformPi f i
      (hasSubgaussianMGF_uniform (f i) (hbound i) (hmean i))
  have hH := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (iIndepFun_eval_uniformPi f) hsub hε
  rw [uniformPi_real_filter (fun ω => ε ≤ ∑ i, f i (ω i))] at hH
  exact hH

end ProductLift

section ZModTransfer

/-- A product of nonzero moduli is nonzero — the instance the CRT transfer's
statement elaborates under. -/
instance neZero_prod_of_neZero {ι : Type*} [Fintype ι] (a : ι → ℕ)
    [∀ i, NeZero (a i)] : NeZero (∏ i, a i) :=
  ⟨Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne (a i)⟩

open scoped Function in
/-- **Hoeffding on a squarefree modulus**: transporting the counting bound
through the Chinese remainder theorem. The deviation event of
`y ↦ ∑ i, f i (y mod a i)` on uniform `y : ZMod (∏ a i)` is exponentially
rare. -/
theorem card_deviation_le_zmod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (hcop : Pairwise (Nat.Coprime on a)) [∀ i, NeZero (a i)]
    (f : Π i, ZMod (a i) → ℝ) (c : ι → ℝ≥0)
    (hbound : ∀ i, ∀ x, f i x ∈ Set.Icc (-(c i : ℝ)) (c i))
    (hmean : ∀ i, ∑ x, f i x = 0) {ε : ℝ} (hε : 0 ≤ ε) :
    ((Finset.univ.filter (fun y : ZMod (∏ i, a i) =>
        ε ≤ ∑ i, f i (ZMod.prodEquivPi a hcop y i))).card : ℝ)
        / ((∏ i, a i : ℕ) : ℝ)
      ≤ Real.exp (-ε ^ 2 / (2 * ((∑ i, (c i) ^ 2 : ℝ≥0) : ℝ))) := by
  classical
  have h := card_deviation_le_uniformPi f c hbound hmean hε
  have hcard : (Finset.univ.filter (fun y : ZMod (∏ i, a i) =>
      ε ≤ ∑ i, f i (ZMod.prodEquivPi a hcop y i))).card
      = (Finset.univ.filter (fun ω : Π i, ZMod (a i) =>
          ε ≤ ∑ i, f i (ω i))).card := by
    apply Finset.card_bij (fun y _ => ZMod.prodEquivPi a hcop y)
    · intro y hy
      rw [Finset.mem_filter] at hy ⊢
      exact ⟨Finset.mem_univ _, hy.2⟩
    · intro y1 h1 y2 h2 heq
      exact (ZMod.prodEquivPi a hcop).injective heq
    · intro ω hω
      rw [Finset.mem_filter] at hω
      refine ⟨(ZMod.prodEquivPi a hcop).symm ω, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [RingEquiv.apply_symm_apply]
        exact hω.2
      · rw [RingEquiv.apply_symm_apply]
  have hpi : (Fintype.card (Π i, ZMod (a i)) : ℝ) = ((∏ i, a i : ℕ) : ℝ) := by
    rw [Fintype.card_pi]
    congr 1
    exact Finset.prod_congr rfl fun i _ => ZMod.card (a i)
  rw [hcard, ← hpi]
  exact h

/-- The coordinate fibers of a finite product are equinumerous: each has size
`|Π|/|Ω i₀|`, stated multiplicatively. -/
theorem card_pi_coord_fiber_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (i₀ : ι) (r : Ω i₀) :
    (Finset.univ.filter (fun ω : Π i, Ω i => ω i₀ = r)).card
        * Fintype.card (Ω i₀)
      = Fintype.card (Π i, Ω i) := by
  classical
  have hfib : ∀ r' : Ω i₀,
      (Finset.univ.filter (fun ω : Π i, Ω i => ω i₀ = r')).card
        = (Finset.univ.filter (fun ω : Π i, Ω i => ω i₀ = r)).card := by
    intro r'
    apply Finset.card_bij (fun ω _ => Function.update ω i₀ r)
    · intro ω hω
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Function.update_self i₀ r ω⟩
    · intro ω₁ h₁ ω₂ h₂ heq
      rw [Finset.mem_filter] at h₁ h₂
      funext i
      by_cases hi : i = i₀
      · subst hi
        rw [h₁.2, h₂.2]
      · have hcoord := congrArg (fun ω : Π i, Ω i => ω i) heq
        simpa [Function.update, hi] using hcoord
    · intro ω hω
      rw [Finset.mem_filter] at hω
      refine ⟨Function.update ω i₀ r', ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, Function.update_self i₀ r' ω⟩
      · funext i
        by_cases hi : i = i₀
        · subst hi
          simp [Function.update_self, hω.2]
        · simp [Function.update, hi]
  have htotal : Fintype.card (Π i, Ω i)
      = ∑ r' : Ω i₀,
          (Finset.univ.filter (fun ω : Π i, Ω i => ω i₀ = r')).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise fun ω _ => Finset.mem_univ (ω i₀)
  rw [htotal, Finset.sum_congr rfl fun r' _ => hfib r', Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_comm]

open scoped Function in
/-- **The exact residue average** (the `(1/P)∑_y F_p(x,y) = (1/p)∑_j (…)`
computation of arXiv:1509.05422 §3): summing a residue-indicator sum over all
`y : ZMod (∏ a)` collapses each class to its exact share `(∏ a)/(a i₀)`. -/
theorem sum_zmod_coord_indicator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (hcop : Pairwise (Nat.Coprime on a))
    [∀ i, NeZero (a i)] (i₀ : ι) {β : Type*} (s : Finset β) (c : β → ℂ)
    (ρ : β → ZMod (a i₀)) :
    ∑ y : ZMod (∏ i, a i), ∑ j ∈ s,
        (if ZMod.prodEquivPi a hcop y i₀ = ρ j then c j else 0)
      = (((∏ i, a i) / a i₀ : ℕ) : ℂ) * ∑ j ∈ s, c j := by
  classical
  have hcard : ∀ r : ZMod (a i₀),
      (Finset.univ.filter
        (fun ω : Π i, ZMod (a i) => ω i₀ = r)).card = (∏ i, a i) / a i₀ := by
    intro r
    have h := card_pi_coord_fiber_mul (Ω := fun i => ZMod (a i)) i₀ r
    rw [ZMod.card, Fintype.card_pi] at h
    have hprod : ∏ i, Fintype.card (ZMod (a i)) = ∏ i, a i :=
      Finset.prod_congr rfl fun i _ => ZMod.card (a i)
    rw [hprod] at h
    have hpos : 0 < a i₀ := Nat.pos_of_ne_zero (NeZero.ne (a i₀))
    calc (Finset.univ.filter
        (fun ω : Π i, ZMod (a i) => ω i₀ = r)).card
        = (Finset.univ.filter
            (fun ω : Π i, ZMod (a i) => ω i₀ = r)).card * a i₀ / a i₀ :=
          (Nat.mul_div_cancel _ hpos).symm
      _ = (∏ i, a i) / a i₀ := by rw [h]
  rw [Finset.sum_comm]
  have hper : ∀ j ∈ s,
      ∑ y : ZMod (∏ i, a i),
          (if ZMod.prodEquivPi a hcop y i₀ = ρ j then c j else 0)
        = (((∏ i, a i) / a i₀ : ℕ) : ℂ) * c j := by
    intro j _
    have hcomp := Equiv.sum_comp (ZMod.prodEquivPi a hcop).toEquiv
      (fun ω : Π i, ZMod (a i) => if ω i₀ = ρ j then c j else 0)
    rw [show (∑ y : ZMod (∏ i, a i),
        (fun ω : Π i, ZMod (a i) => if ω i₀ = ρ j then c j else 0)
          ((ZMod.prodEquivPi a hcop).toEquiv y))
      = ∑ y : ZMod (∏ i, a i),
          (if ZMod.prodEquivPi a hcop y i₀ = ρ j then c j else 0) from rfl]
      at hcomp
    rw [hcomp, ← Finset.sum_filter, Finset.sum_const, hcard (ρ j),
      nsmul_eq_mul]
  rw [Finset.sum_congr rfl hper, ← Finset.mul_sum]

open scoped Function in
/-- **The CRT coordinate dictionary**: the `i`-th coordinate of a cast residue
is the cast residue at the `i`-th modulus. -/
theorem prodEquivPi_natCast {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (hcop : Pairwise (Nat.Coprime on a)) [∀ i, NeZero (a i)]
    (n : ℕ) (i : ι) :
    ZMod.prodEquivPi a hcop ((n : ZMod (∏ j, a j))) i = (n : ZMod (a i)) := by
  have h := map_natCast (ZMod.prodEquivPi a hcop) n
  rw [h, Pi.natCast_apply]

end ZModTransfer

end MoltResearch
