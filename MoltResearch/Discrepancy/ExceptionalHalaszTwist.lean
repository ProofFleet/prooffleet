import MoltResearch.Discrepancy.CellHalasz

/-!
# Twisted Halász input for the exceptional cells

The older exceptional-cell bound first estimated an untwisted partial sum and
then differentiated the Fourier phase.  That introduces the false factor
`3 + 2πT`.  Here the phase is absorbed into the archimedean twist before Abel
summation.  Consequently Abel sees only the decreasing weight `1/n`.

The second seam keeps the Ramaré factor sum nonuniform.  In particular, a
quotient below `cellHalaszThreshold` is charged its own harmonic mass rather
than the largest cost of any quotient.
-/

namespace MoltResearch

open Finset ExpSums

/-- The logarithmically weighted cost obtained from the cheap twisted Halász
bound on a block `(a,b]`.  It has no dependence on a frequency cap `T`. -/
noncomputable def cheapTwistedDirichletCost
    (eps W D : ℝ) (a b : ℕ) : ℝ :=
  2 * (b : ℝ) *
      (eps + Real.exp (W * Real.log (Real.log b) + W - D / 2)) /
    ((a + 1 : ℕ) : ℝ)

/-- The cheap twisted Halász theorem followed by Abel summation against
`1/n`.  The oscillation remains inside the completely multiplicative
coefficient throughout, so the estimate contains no Abel frequency factor. -/
theorem cheap_halasz_twisted_dirichlet_block (eps : ℝ) (heps : 0 < eps) :
    ∃ (x0 : ℕ) (W : ℝ), 0 < W ∧
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → g 1 = 1 →
        (∀ n, ‖g n‖ ≤ 1) →
      ∀ a b : ℕ, x0 ≤ a → a < b →
      ∀ D : ℝ, 2 ≤ D →
        (∀ u : ℕ, a ≤ u → u ≤ b → NonPretentiousAt g D u) →
      ∀ t : ℝ, |2 * Real.pi * t| ≤ (D / 2) * a →
        ‖∑ n ∈ Finset.Ioc a b, (g n / (n : ℂ)) *
            ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
          ≤ cheapTwistedDirichletCost eps W D a b := by
  obtain ⟨xbase, W, hW, hplain⟩ := low_band_block_sup eps heps
  refine ⟨max xbase 3, W, hW, ?_⟩
  intro g hcm hg1 hgb a b hxa hab D hD hnp t ht
  have ha1 : 1 ≤ a + 1 := Nat.succ_pos _
  have hab1 : a + 1 ≤ b := by omega
  let c : ℕ → ℂ := fun n =>
    g n * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)
  have hpartial : ∀ u : ℕ, a + 1 ≤ u → u ≤ b →
      ‖∑ n ∈ Finset.Icc (a + 1) u, c n‖ ≤
        2 * ((b : ℝ) *
          (eps + Real.exp (W * Real.log (Real.log b) + W - D / 2))) := by
    intro u hau hub
    have hset : Finset.Icc (a + 1) u = Finset.Ioc a u := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hset]
    exact (hplain g hcm hg1 hgb a u
      (le_trans (le_max_left _ _) hxa) (by omega) D hD
      (hnp a le_rfl (le_trans (by omega) hub))
      (hnp u (by omega) hub) t ht).trans (by
        have hu : (u : ℝ) ≤ b := by exact_mod_cast hub
        have hlogu : Real.log (Real.log u) ≤ Real.log (Real.log b) := by
          have ha3 : 3 ≤ a := le_trans (le_max_right _ _) hxa
          have hu0 : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
          have hlu0 : (0 : ℝ) < Real.log u :=
            Real.log_pos (by exact_mod_cast (by omega : 1 < u))
          exact Real.log_le_log hlu0 (Real.log_le_log hu0 hu)
        have hexp : Real.exp (W * Real.log (Real.log u) + W - D / 2) ≤
            Real.exp (W * Real.log (Real.log b) + W - D / 2) := by
          apply Real.exp_le_exp.2
          nlinarith [mul_le_mul_of_nonneg_left hlogu hW.le]
        have heta0 : 0 ≤ eps +
            Real.exp (W * Real.log (Real.log u) + W - D / 2) := by positivity
        nlinarith)
  have habSum := norm_sum_div_le_of_partial c (a + 1) b ha1 hab1
    (2 * ((b : ℝ) *
      (eps + Real.exp (W * Real.log (Real.log b) + W - D / 2)))) hpartial
  have hrewrite : ∑ n ∈ Finset.Ioc a b,
      (g n / (n : ℂ)) *
        ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ) =
      ∑ n ∈ Finset.Icc (a + 1) b, c n / (n : ℂ) := by
    rw [show Finset.Ioc a b = Finset.Icc (a + 1) b by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega]
    refine Finset.sum_congr rfl fun n hn => ?_
    dsimp [c]
    ring
  rw [hrewrite]
  simpa only [cheapTwistedDirichletCost, Nat.cast_add, Nat.cast_one,
    mul_assoc] using habSum

/-- The no-frequency-loss block bound specialized to a level-free twist.
The base non-pretentiousness strength is doubled exactly once by the existing
Ramaré robustness lemma. -/
theorem cheap_halasz_levelFreeTwist_dirichlet_block
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (x0 : ℕ) (W : ℝ), 0 < W ∧
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → g 1 = 1 →
        (∀ n, ‖g n‖ ≤ 1) →
      ∀ levels : List (Finset ℕ),
        (∀ Q ∈ levels, ∀ p ∈ Q, p.Prime) →
      ∀ a b : ℕ, x0 ≤ a → a < b →
      ∀ D : ℝ, 2 ≤ D →
        (∀ u : ℕ, a ≤ u → u ≤ b → NonPretentiousAt g (2 * D) u) →
      ∀ t : ℝ, |2 * Real.pi * t| ≤ (D / 2) * a →
        ‖∑ n ∈ Finset.Ioc a b,
            (levelFreeTwist g levels n / (n : ℂ)) *
              ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
          ≤ cheapTwistedDirichletCost eps W D a b := by
  obtain ⟨x0, W, hW, hblock⟩ := cheap_halasz_twisted_dirichlet_block eps heps
  refine ⟨x0, W, hW, ?_⟩
  intro g hcm hg1 hgb levels hlevels a b hxa hab D hD hnp t ht
  apply hblock (levelFreeTwist g levels)
    (completelyMultiplicativeC_levelFreeTwist g hcm levels hlevels)
    (levelFreeTwist_one g hg1 levels hlevels)
    (norm_levelFreeTwist_le_one g hgb levels)
    a b hxa hab D hD
  · intro u hau hub
    exact nonPretentiousAt_levelFreeTwist g hgb levels D (by linarith)
      u (hnp u hau hub)
  · exact ht

/-- The honest cost of one Ramaré quotient.  Long quotients use the
archimedean-twist bound; short quotients retain their own harmonic mass. -/
noncomputable def exceptionalTwistedQuotientCost
    (x0 : ℕ) (eps W D : ℝ) (a b : ℕ) : ℝ :=
  if x0 ≤ a then cheapTwistedDirichletCost eps W D a b
  else cellHalaszTrivialCost a b

theorem exceptionalTwistedQuotientCost_nonneg
    (x0 : ℕ) (eps W D : ℝ) (a b : ℕ) (heps : 0 ≤ eps) :
    0 ≤ exceptionalTwistedQuotientCost x0 eps W D a b := by
  unfold exceptionalTwistedQuotientCost
  split_ifs
  · unfold cheapTwistedDirichletCost
    positivity
  · unfold cellHalaszTrivialCost
    positivity

/-- Every quotient in the exceptional Ramaré decomposition is bounded by
its own long/short cost.  The returned cutoff dominates the existing
`cellHalaszThreshold`, so the analytic lower-scale requirement is retained. -/
theorem norm_filter_levelFreeTwist_quotient_le_recut
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (x0 : ℕ) (W : ℝ), cellHalaszThreshold ≤ x0 ∧ 0 < W ∧
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → g 1 = 1 →
        (∀ n, ‖g n‖ ≤ 1) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ∀ levels : List (Finset ℕ),
        (∀ Q ∈ levels, ∀ p ∈ Q, p.Prime) →
      ∀ a b : ℕ, a ≤ b →
      ∀ D : ℝ, 2 ≤ D →
        (∀ u : ℕ, a ≤ u → u ≤ b → NonPretentiousAt g (2 * D) u) →
      ∀ t : ℝ, |2 * Real.pi * t| ≤ (D / 2) * a →
        ‖∑ n ∈ (Finset.Ioc a b).filter (fun n => ∀ p ∈ P, ¬ p ∣ n),
            (levelFreeTwist g levels n / (n : ℂ)) *
              ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
          ≤ exceptionalTwistedQuotientCost x0 eps W D a b := by
  obtain ⟨xbase, W, hW, hlong⟩ :=
    cheap_halasz_levelFreeTwist_dirichlet_block eps heps
  refine ⟨max cellHalaszThreshold xbase, W, le_max_left _ _, hW, ?_⟩
  intro g hcm hg1 hgb P hP levels hlevels a b hab D hD hnp t ht
  rw [sum_filter_levelFreeTwist_eq_cons]
  by_cases hcut : max cellHalaszThreshold xbase ≤ a
  · rw [exceptionalTwistedQuotientCost, if_pos hcut]
    rcases eq_or_lt_of_le hab with rfl | hablt
    · simp only [Finset.Ioc_self, sum_empty, norm_zero]
      unfold cheapTwistedDirichletCost
      positivity
    · apply hlong g hcm hg1 hgb (P :: levels)
        (by
          intro Q hQ p hp
          rw [List.mem_cons] at hQ
          rcases hQ with rfl | hQ
          · exact hP p hp
          · exact hlevels Q hQ p hp)
        a b (le_trans (le_max_right _ _) hcut) hablt D hD hnp t ht
  · rw [exceptionalTwistedQuotientCost, if_neg hcut]
    exact norm_dirichlet_poly_le_harmonic
      (levelFreeTwist g (P :: levels))
      (norm_levelFreeTwist_le_one g hgb (P :: levels)) a b t

/-- Ramaré weight removal with a separate quotient cost for every
`P`-supported factor.  This is the accounting seam needed to charge a short
quotient by its own harmonic mass. -/
theorem norm_ramare_weighted_poly_le_sum_cost
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g)
    (hg : ∀ n, ‖g n‖ ≤ 1) (A B : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (t : ℝ) (cost : ℕ → ℝ)
    (hcost : ∀ n1 ∈ (Finset.Icc 1 B).filter
      (fun n => n.primeFactors ⊆ P),
      ‖∑ n2 ∈ (Finset.Ioc (A / n1) (B / n1)).filter
          (fun n => ∀ p ∈ P, ¬ p ∣ n),
          (g n2 / (n2 : ℂ)) *
            ((Real.fourierChar (-(Real.log n2 * t)) : Circle) : ℂ)‖
        ≤ cost n1) :
    ‖∑ m ∈ Finset.Ioc A B, (g m / (m : ℂ)) *
        ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ) /
          (((P.filter (· ∣ m)).card : ℂ) + 1)‖
      ≤ ∑ n1 ∈ (Finset.Icc 1 B).filter
          (fun n => n.primeFactors ⊆ P), (1 : ℝ) / n1 * cost n1 := by
  classical
  rw [ramare_weighted_poly_eq_sum_pPart g hcm A B P hP t]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n1 hn1 => ?_)
  have hn1pos : 0 < n1 := by
    rw [Finset.mem_filter, Finset.mem_Icc] at hn1
    exact hn1.1.1
  rw [norm_mul]
  have hcoeff : ‖(g n1 * ((Real.fourierChar (-(Real.log n1 * t))
      : Circle) : ℂ)) / ((n1 : ℂ) * (((P.filter (· ∣ n1)).card : ℂ) + 1))‖
      ≤ 1 / (n1 : ℝ) := by
    rw [norm_div, norm_mul, norm_eq_of_mem_sphere, mul_one, norm_mul]
    have hden : (n1 : ℝ) * ‖(((P.filter (· ∣ n1)).card : ℂ) + 1)‖ =
        (n1 : ℝ) * (((P.filter (· ∣ n1)).card : ℝ) + 1) := by
      congr 1
      have heq : (((P.filter (· ∣ n1)).card : ℂ) + 1) =
          (((((P.filter (· ∣ n1)).card : ℕ) + 1 : ℕ)) : ℂ) := by
        push_cast
        ring
      rw [heq, Complex.norm_natCast]
      push_cast
      ring
    rw [Complex.norm_natCast, hden]
    have hcard : (1 : ℝ) ≤ ((P.filter (· ∣ n1)).card : ℝ) + 1 := by
      have hc0 : (0 : ℝ) ≤ ((P.filter (· ∣ n1)).card : ℝ) := Nat.cast_nonneg _
      linarith
    have hn1R : (1 : ℝ) ≤ (n1 : ℝ) := by exact_mod_cast hn1pos
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc
      ‖g n1‖ * (n1 : ℝ) ≤ 1 * (n1 : ℝ) :=
        mul_le_mul_of_nonneg_right (hg n1) (by positivity)
      _ ≤ (n1 : ℝ) * (((P.filter (· ∣ n1)).card : ℝ) + 1) := by
        nlinarith
      _ = 1 * ((n1 : ℝ) * (((P.filter (· ∣ n1)).card : ℝ) + 1)) := by
        ring
  exact mul_le_mul hcoeff (hcost n1 hn1) (norm_nonneg _) (by positivity)

/-- The sum of the individual long/short quotient charges after Ramaré
weight removal. -/
noncomputable def exceptionalTwistedRamareCost
    (x0 : ℕ) (eps W D : ℝ) (A B : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ n1 ∈ (Finset.Icc 1 B).filter (fun n => n.primeFactors ⊆ P),
    (1 : ℝ) / n1 *
      exceptionalTwistedQuotientCost x0 eps W D (A / n1) (B / n1)

/-- The recut pointwise Ramaré estimate.  Unlike `cellHalaszBound`, this
contains neither a global quotient maximum nor an Abel factor depending on
the ambient frequency cap. -/
theorem norm_levelFreeTwist_ramare_poly_le_recut
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (x0 : ℕ) (W : ℝ), cellHalaszThreshold ≤ x0 ∧ 0 < W ∧
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → g 1 = 1 →
        (∀ n, ‖g n‖ ≤ 1) →
      ∀ levels : List (Finset ℕ),
        (∀ Q ∈ levels, ∀ p ∈ Q, p.Prime) →
      ∀ A B : ℕ, A ≤ B →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ∀ D : ℝ, 2 ≤ D →
        (∀ n1 ∈ (Finset.Icc 1 B).filter (fun n => n.primeFactors ⊆ P),
          ∀ u : ℕ, A / n1 ≤ u → u ≤ B / n1 →
            NonPretentiousAt g (2 * D) u) →
      ∀ t : ℝ,
        (∀ n1 ∈ (Finset.Icc 1 B).filter (fun n => n.primeFactors ⊆ P),
          |2 * Real.pi * t| ≤ (D / 2) * ((A / n1 : ℕ) : ℝ)) →
        ‖∑ n ∈ Finset.Ioc A B,
            (levelFreeTwist g levels n / (n : ℂ)) *
              ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ) /
                (((P.filter (· ∣ n)).card : ℂ) + 1)‖
          ≤ exceptionalTwistedRamareCost x0 eps W D A B P := by
  obtain ⟨x0, W, hx0, hW, hquot⟩ :=
    norm_filter_levelFreeTwist_quotient_le_recut eps heps
  refine ⟨x0, W, hx0, hW, ?_⟩
  intro g hcm hg1 hgb levels hlevels A B hAB P hP D hD hnp t ht
  unfold exceptionalTwistedRamareCost
  apply norm_ramare_weighted_poly_le_sum_cost
    (levelFreeTwist g levels)
    (completelyMultiplicativeC_levelFreeTwist g hcm levels hlevels)
    (norm_levelFreeTwist_le_one g hgb levels) A B P hP t
    (fun n1 => exceptionalTwistedQuotientCost x0 eps W D
      (A / n1) (B / n1))
  intro n1 hn1
  apply hquot g hcm hg1 hgb P hP levels hlevels
    (A / n1) (B / n1) (Nat.div_le_div_right hAB) D hD
    (hnp n1 hn1) t (ht n1 hn1)

/-- The harmonic mass of the integers supported on the selected finite prime
set is bounded by its own Euler product.  This is sharper than replacing `P`
by every prime below a common cutoff. -/
theorem pSmoothHarmonicMass_le_exp_primeMass
    (B : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    pSmoothHarmonicMass B P ≤
      Real.exp (2 * ∑ p ∈ P, (1 : ℝ) / p) := by
  classical
  let S := (Finset.Icc 1 B).filter (fun n => n.primeFactors ⊆ P)
  let E := Nat.log 2 B + 1
  let F : ℕ → ({p // p ∈ P} → ℕ) := fun n p => n.factorization p.1
  have hval : ∀ n ∈ S,
      (1 : ℝ) / n = ∏ p : {p // p ∈ P},
        ((1 : ℝ) / p.1) ^ F n p := by
    intro n hn
    have hattach : (∏ p : {p // p ∈ P},
        ((1 : ℝ) / p.1) ^ F n p) =
        ∏ p ∈ P, ((1 : ℝ) / p) ^ n.factorization p := by
      change (∏ p ∈ (Finset.univ : Finset {p // p ∈ P}),
        ((1 : ℝ) / p.1) ^ n.factorization p.1) = _
      rw [Finset.univ_eq_attach]
      exact Finset.prod_attach P
        (fun p => ((1 : ℝ) / p) ^ n.factorization p)
    rw [hattach]
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hext : ∏ p ∈ P, ((1 : ℝ) / p) ^ n.factorization p =
        ∏ p ∈ n.primeFactors, ((1 : ℝ) / p) ^ n.factorization p := by
      refine (Finset.prod_subset hn.2 fun p hpP hp => ?_).symm
      have hfac0 : n.factorization p = 0 := by
        rw [← Finsupp.notMem_support_iff]
        simpa only [Nat.support_factorization] using hp
      rw [hfac0, pow_zero]
    have hnat : ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p = n := by
      rw [show ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p =
          ((∏ p ∈ n.primeFactors, p ^ n.factorization p : ℕ) : ℝ) by
        push_cast
        rfl]
      exact_mod_cast Nat.factorization_prod_pow_eq_self hn0
    rw [hext]
    rw [show ∏ p ∈ n.primeFactors, ((1 : ℝ) / p) ^ n.factorization p =
        (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p)⁻¹ by
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun p hp => by rw [one_div, inv_pow]]
    rw [hnat, one_div]
  have hrecon : ∀ n ∈ S, n = ∏ p : {p // p ∈ P}, p.1 ^ F n p := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hattach : (∏ p : {p // p ∈ P}, p.1 ^ F n p) =
        ∏ p ∈ P, p ^ n.factorization p := by
      change (∏ p ∈ (Finset.univ : Finset {p // p ∈ P}),
        p.1 ^ n.factorization p.1) = _
      rw [Finset.univ_eq_attach]
      exact Finset.prod_attach P (fun p => p ^ n.factorization p)
    rw [hattach]
    rw [show ∏ p ∈ P, p ^ n.factorization p =
        ∏ p ∈ n.primeFactors, p ^ n.factorization p from
      (Finset.prod_subset hn.2 fun p hpP hp => by
        have hfac0 : n.factorization p = 0 := by
          rw [← Finsupp.notMem_support_iff]
          simpa only [Nat.support_factorization] using hp
        rw [hfac0, pow_zero]).symm]
    exact (Nat.factorization_prod_pow_eq_self hn0).symm
  have hinj : Set.InjOn F S := by
    intro n hn m hm hnm
    rw [hrecon n hn, hrecon m hm]
    exact Finset.prod_congr rfl fun p hp => by rw [hnm]
  have himg : S.image F ⊆ Fintype.piFinset
      (fun _ : {p // p ∈ P} => Finset.range E) := by
    intro f hf
    rw [Finset.mem_image] at hf
    obtain ⟨n, hn, rfl⟩ := hf
    rw [Fintype.mem_piFinset]
    intro p
    rw [Finset.mem_range]
    change n.factorization p.1 < Nat.log 2 B + 1
    rw [Nat.lt_succ_iff]
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    exact factorization_le_log hn.1.1 hn.1.2 p.1
  have hbox : pSmoothHarmonicMass B P ≤
      ∏ p ∈ P, ∑ e ∈ Finset.range E, ((1 : ℝ) / p) ^ e := by
    unfold pSmoothHarmonicMass
    change ∑ n ∈ S, (1 : ℝ) / n ≤ _
    calc
      ∑ n ∈ S, (1 : ℝ) / n =
          ∑ n ∈ S, ∏ p : {p // p ∈ P},
            ((1 : ℝ) / p.1) ^ F n p := Finset.sum_congr rfl hval
      _ = ∑ f ∈ S.image F, ∏ p : {p // p ∈ P},
            ((1 : ℝ) / p.1) ^ f p := by
          rw [Finset.sum_image fun n hn m hm hnm => hinj hn hm hnm]
      _ ≤ ∑ f ∈ Fintype.piFinset
            (fun _ : {p // p ∈ P} => Finset.range E),
            ∏ p : {p // p ∈ P}, ((1 : ℝ) / p.1) ^ f p := by
          exact Finset.sum_le_sum_of_subset_of_nonneg himg
            (fun f hf hnf => Finset.prod_nonneg fun p hp => by positivity)
      _ = ∏ p ∈ P, ∑ e ∈ Finset.range E, ((1 : ℝ) / p) ^ e := by
          rw [← Finset.prod_attach P
            (fun p => ∑ e ∈ Finset.range E, ((1 : ℝ) / p) ^ e),
            show P.attach = Finset.univ from (Finset.univ_eq_attach P).symm,
            Finset.prod_univ_sum]
  refine hbox.trans ?_
  calc
    ∏ p ∈ P, ∑ e ∈ Finset.range E, ((1 : ℝ) / p) ^ e
        ≤ ∏ p ∈ P, Real.exp (2 * ((1 : ℝ) / p)) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact Finset.sum_nonneg fun e he => by positivity
      · intro p hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
        have hp0 : (0 : ℝ) < p := by linarith
        have hx0 : (0 : ℝ) ≤ 1 / p := by positivity
        have hxhalf : (1 : ℝ) / p ≤ 1 / 2 :=
          one_div_le_one_div_of_le (by norm_num) hp2
        have htail : (0 : ℝ) ≤ 1 - 2 * ((1 : ℝ) / p) := by linarith
        have hgeom := sum_pow_le_one_div ((1 : ℝ) / p) hx0 (by linarith) E
        have hinv : (1 : ℝ) / (1 - 1 / p) ≤ 1 + 2 * (1 / p) := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith [mul_nonneg hx0 htail]
        exact hgeom.trans (hinv.trans (by
          simpa only [add_comm] using Real.add_one_le_exp (2 * ((1 : ℝ) / p))))
    _ = Real.exp (2 * ∑ p ∈ P, (1 : ℝ) / p) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]

/-- The complete recut pointwise envelope after inclusion--exclusion. -/
noncomputable def cellHalaszReCutBound
    (x0 : ℕ) (eps W D : ℝ) (Aq Bq : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ)) : ℝ :=
  ((2 ^ rest.length : ℕ) : ℝ) *
    exceptionalTwistedRamareCost x0 eps W D Aq Bq P

/-- **VI-9e: the exceptional-cell pointwise recut.**

The representative polynomial is bounded using the cheap Halász theorem on
the already twisted completely multiplicative function.  Long quotients have
no `T`-dependent Abel loss; short quotients carry their own harmonic mass;
and the analytic cutoff still dominates `cellHalaszThreshold`. -/
theorem norm_typicalS_quot_block_poly_le_recut
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (x0 : ℕ) (W : ℝ), cellHalaszThreshold ≤ x0 ∧ 0 < W ∧
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → g 1 = 1 →
        (∀ n, ‖g n‖ ≤ 1) →
      ∀ A B q : ℕ, 1 ≤ q → A ≤ B →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ∀ rest : List (Finset ℕ),
        (∀ Q ∈ rest, ∀ p ∈ Q, p.Prime) →
      ∀ D : ℝ, 2 ≤ D →
        (∀ n1 ∈ (Finset.Icc 1 (B / q)).filter
            (fun n => n.primeFactors ⊆ P),
          ∀ u : ℕ, (A / q) / n1 ≤ u → u ≤ (B / q) / n1 →
            NonPretentiousAt g (2 * D) u) →
      ∀ t : ℝ,
        (∀ n1 ∈ (Finset.Icc 1 (B / q)).filter
            (fun n => n.primeFactors ⊆ P),
          |2 * Real.pi * t| ≤
            (D / 2) * ((((A / q) / n1 : ℕ)) : ℝ)) →
        ‖∑ n ∈ Finset.Ioc (A / q) (B / q),
            (typicalSQuotCoeff g P (typicalS 0 B rest) n / (n : ℂ)) *
              ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
          ≤ cellHalaszReCutBound x0 eps W D (A / q) (B / q) P rest := by
  obtain ⟨x0, W, hx0, hW, hramare⟩ :=
    norm_levelFreeTwist_ramare_poly_le_recut eps heps
  refine ⟨x0, W, hx0, hW, ?_⟩
  intro g hcm hg1 hgb A B q hq hAB P hP rest hrest D hD hnp t ht
  have hBqB : B / q ≤ B := Nat.div_le_self _ _
  refine (norm_typicalSQuotCoeff_poly_le_inclexcl g P rest
    (A / q) (B / q) B hBqB t).trans ?_
  let C := exceptionalTwistedRamareCost x0 eps W D (A / q) (B / q) P
  calc
    (rest.sublists.map fun S =>
        ‖∑ n ∈ Finset.Ioc (A / q) (B / q),
            (levelFreeTwist g S n / (n : ℂ)) *
              ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ) /
                (((P.filter (· ∣ n)).card : ℂ) + 1)‖).sum
        ≤ (rest.sublists.map fun _ => C).sum := by
      apply List.sum_le_sum
      intro S hS
      exact hramare g hcm hg1 hgb S
        (by
          intro Q hQS p hp
          exact hrest Q ((List.mem_sublists.mp hS).mem hQS) p hp)
        (A / q) (B / q) (Nat.div_le_div_right hAB) P hP D hD hnp t ht
    _ = cellHalaszReCutBound x0 eps W D (A / q) (B / q) P rest := by
      rw [show (rest.sublists.map fun _ => C) =
          List.replicate rest.sublists.length C from List.map_const,
        List.sum_replicate, List.length_sublists, nsmul_eq_mul]
      simp only [C, cellHalaszReCutBound]

end MoltResearch
