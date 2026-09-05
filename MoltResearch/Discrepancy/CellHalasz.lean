import MoltResearch.Discrepancy.LevelLegs
import MoltResearch.Discrepancy.WindowAssembly

/-!
# Per-cell Halász input for the `[mrt]` exceptional leg

This leaf module assembles the IV-0 inclusion–exclusion, Ramaré-weight
removal, and short-sum Halász chain at the quotient scale of one e-adic
cell.  It leaves the later schedule choice of the free parameter to the
capstone consumer.
-/

namespace MoltResearch

open Finset ExpSums

/-! ## IV-0e: multiplicative freeness twists -/

/-- The finite set of all primes appearing in a list of prime levels. -/
def primesInLevels : List (Finset ℕ) → Finset ℕ
  | [] => ∅
  | P :: levels => P ∪ primesInLevels levels

@[simp] theorem mem_primesInLevels {p : ℕ} {levels : List (Finset ℕ)} :
    p ∈ primesInLevels levels ↔ ∃ P ∈ levels, p ∈ P := by
  induction levels with
  | nil => simp [primesInLevels]
  | cons P levels ih => simp [primesInLevels, ih]

/-- The completely multiplicative twist obtained by killing integers
divisible by a prime in one of `levels`. -/
noncomputable def levelFreeTwist (g : ℕ → ℂ)
    (levels : List (Finset ℕ)) (n : ℕ) : ℂ :=
  if ∀ p ∈ primesInLevels levels, ¬ p ∣ n then g n else 0

theorem levelFreeTwist_eq_if (g : ℕ → ℂ)
    (levels : List (Finset ℕ)) (n : ℕ) :
    levelFreeTwist g levels n =
      if ∀ Q ∈ levels, ∀ p ∈ Q, ¬ p ∣ n then g n else 0 := by
  classical
  unfold levelFreeTwist
  congr 1
  simp only [mem_primesInLevels]
  apply propext
  constructor
  · intro h Q hQ p hpQ
    exact h p ⟨Q, hQ, hpQ⟩
  · intro h p hp
    obtain ⟨Q, hQ, hpQ⟩ := hp
    exact h Q hQ p hpQ

theorem completelyMultiplicativeC_levelFreeTwist (g : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC g) (levels : List (Finset ℕ))
    (hlevels : ∀ Q ∈ levels, ∀ p ∈ Q, p.Prime) :
    CompletelyMultiplicativeC (levelFreeTwist g levels) := by
  classical
  unfold levelFreeTwist
  apply completelyMultiplicativeC_free_indicator g hcm
  intro p hp
  rw [mem_primesInLevels] at hp
  obtain ⟨Q, hQ, hpQ⟩ := hp
  exact hlevels Q hQ p hpQ

theorem norm_levelFreeTwist_le_one (g : ℕ → ℂ)
    (hg : ∀ n, ‖g n‖ ≤ 1) (levels : List (Finset ℕ)) (n : ℕ) :
    ‖levelFreeTwist g levels n‖ ≤ 1 := by
  classical
  unfold levelFreeTwist
  split_ifs
  · exact hg n
  · simp

theorem levelFreeTwist_one (g : ℕ → ℂ) (h1 : g 1 = 1)
    (levels : List (Finset ℕ))
    (hlevels : ∀ Q ∈ levels, ∀ p ∈ Q, p.Prime) :
    levelFreeTwist g levels 1 = 1 := by
  classical
  rw [levelFreeTwist_eq_if, if_pos, h1]
  intro Q hQ p hpQ hp1
  exact (hlevels Q hQ p hpQ).not_dvd_one hp1

/-! ## IV-0f: non-pretentiousness of the twists -/

/-- The real `0/1` weight underlying a level-freeness twist. -/
noncomputable def levelFreeIndicator (levels : List (Finset ℕ))
    (n : ℕ) : ℂ :=
  if ∀ p ∈ primesInLevels levels, ¬ p ∣ n then 1 else 0

theorem levelFreeTwist_eq_mul_indicator (g : ℕ → ℂ)
    (levels : List (Finset ℕ)) :
    levelFreeTwist g levels = fun n => g n * levelFreeIndicator levels n := by
  classical
  funext n
  unfold levelFreeTwist levelFreeIndicator
  split_ifs <;> simp

/-- The Ramaré robustness inequality with a `1`-bounded comparison.
The in-tree statement assumes a unimodular comparison, while
`charTwist` can vanish at primes dividing the character modulus.  The
same pointwise argument only uses the weaker norm bound recorded here. -/
theorem pretentiousDistSq_mul_weight_ge_of_norm_le_one
    (f g h : ℕ → ℂ) (N : ℕ)
    (hf : ∀ p, ‖f p‖ ≤ 1) (hh : ∀ p, ‖h p‖ ≤ 1)
    (hg_re : ∀ p, (g p).im = 0) (hg0 : ∀ p, 0 ≤ (g p).re)
    (hg1 : ∀ p, (g p).re ≤ 1) :
    (1 / 2) * pretentiousDistSq f h N ≤
      pretentiousDistSq (fun n => f n * g n) h N := by
  rw [pretentiousDistSq, pretentiousDistSq, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp0 : (0 : ℝ) < p := by
    have : (0 : ℕ) < p := (Nat.prime_of_mem_primesBelow hp).pos
    exact_mod_cast this
  set R := (f p * (starRingEnd ℂ) (h p)).re with hR_def
  have hRabs : |R| ≤ 1 := by
    rw [hR_def]
    refine le_trans (Complex.abs_re_le_norm _) ?_
    rw [norm_mul, RCLike.norm_conj]
    calc
      ‖f p‖ * ‖h p‖ ≤ 1 * 1 :=
        mul_le_mul (hf p) (hh p) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hR := abs_le.mp hRabs
  set γ : ℝ := (g p).re with hγ_def
  have hγdef : g p = (γ : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im]
      exact hg_re p
  have hkey : ((fun n => f n * g n) p * (starRingEnd ℂ) (h p)).re = γ * R := by
    have hmul : (fun n => f n * g n) p * (starRingEnd ℂ) (h p) =
        (γ : ℂ) * (f p * (starRingEnd ℂ) (h p)) := by
      dsimp only
      rw [hγdef]
      ring
    rw [hmul, Complex.re_ofReal_mul, hR_def]
  rw [hkey]
  have hnum : (1 / 2) * (1 - R) ≤ 1 - γ * R := by
    nlinarith [mul_nonneg (by linarith [hR.1] : (0 : ℝ) ≤ 1 + R)
        (by linarith [hg1 p] : (0 : ℝ) ≤ 1 - γ),
      mul_nonneg (by linarith [hR.2] : (0 : ℝ) ≤ 1 - R)
        (show (0 : ℝ) ≤ γ from hg0 p)]
  calc
    (1 / 2) * ((1 - R) / p) = ((1 / 2) * (1 - R)) / p := by ring
    _ ≤ (1 - γ * R) / p := div_le_div_of_nonneg_right hnum hp0.le

/-- Doubling the input strength pays exactly for the factor `1/2` in
Ramaré robustness, uniformly for every level-freeness twist. -/
theorem nonPretentiousAt_levelFreeTwist (g : ℕ → ℂ)
    (hg : ∀ n, ‖g n‖ ≤ 1) (levels : List (Finset ℕ))
    (D : ℝ) (hD : 0 ≤ D) (x : ℕ)
    (hNP : NonPretentiousAt g (2 * D) x) :
    NonPretentiousAt (levelFreeTwist g levels) D x := by
  intro q χ t hq ht
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hbase : 2 * D ≤ pretentiousDistSq g (charTwist q χ t) x :=
    hNP q χ t (by linarith) (by nlinarith)
  have hrobust := pretentiousDistSq_mul_weight_ge_of_norm_le_one g
    (levelFreeIndicator levels) (charTwist q χ t) x hg
    (charTwist_norm_le_one q χ t)
    (fun p => by classical unfold levelFreeIndicator; split_ifs <;> simp)
    (fun p => by classical unfold levelFreeIndicator; split_ifs <;> simp)
    (fun p => by classical unfold levelFreeIndicator; split_ifs <;> simp)
  rw [← levelFreeTwist_eq_mul_indicator] at hrobust
  nlinarith

/-! ## IV-0e: inclusion–exclusion in Ramaré normal form -/

/-- Inclusion–exclusion removes the `typicalS` indicator from a
Ramaré-weighted block.  Every resulting term is the whole block for a
level-freeness twist, in the exact normal form consumed by
`norm_ramare_weighted_poly_le`. -/
theorem norm_typicalSQuotCoeff_poly_le_inclexcl
    (g : ℕ → ℂ) (P : Finset ℕ) (rest : List (Finset ℕ))
    (a b U : ℕ) (hbU : b ≤ U) (t : ℝ) :
    ‖∑ n ∈ Finset.Ioc a b,
        (typicalSQuotCoeff g P (typicalS 0 U rest) n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
      ≤ (rest.sublists.map fun S =>
          ‖∑ n ∈ Finset.Ioc a b,
              (levelFreeTwist g S n / (n : ℂ))
                * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)
                / (((P.filter (· ∣ n)).card : ℂ) + 1)‖).sum := by
  classical
  let F : ℕ → ℂ := fun n =>
    (g n / (n : ℂ))
      * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)
      / (((P.filter (· ∣ n)).card : ℂ) + 1)
  have hpoly :
      ∑ n ∈ Finset.Ioc a b,
          (typicalSQuotCoeff g P (typicalS 0 U rest) n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)
        = ∑ n ∈ typicalS a b rest, F n := by
    change _ = ∑ n ∈ (Finset.Ioc a b).filter (HasFactorInAll rest), F n
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Ioc] at hn
    unfold typicalSQuotCoeff
    by_cases hfree : HasFactorInAll rest n
    · have hmem : n ∈ typicalS 0 U rest := by
        rw [mem_typicalS]
        exact ⟨⟨by omega, hn.2.trans hbU⟩, hfree⟩
      rw [if_pos hmem, if_pos hfree]
      dsimp [F]
      ring
    · have hnotmem : n ∉ typicalS 0 U rest := by
        rw [mem_typicalS]
        exact fun h => hfree h.2
      rw [if_neg hnotmem, if_neg hfree]
      simp
  rw [hpoly]
  refine (norm_sum_typicalS_le_inclexcl a b F rest).trans_eq ?_
  congr 1
  apply List.map_congr_left
  intro S hS
  congr 1
  change (∑ n ∈ (Finset.Ioc a b).filter
      (fun n => ∀ Q ∈ S, ∀ p ∈ Q, ¬ p ∣ n), F n) = _
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [levelFreeTwist_eq_if]
  by_cases hfree : ∀ Q ∈ S, ∀ p ∈ Q, ¬ p ∣ n
  · rw [if_pos hfree, if_pos hfree]
  · rw [if_neg hfree, if_neg hfree]
    simp

/-! ## IV-0c/IV-0f: one quotient block -/

/-- The numerical cutoff at which the in-tree Halász shell becomes
available. -/
def cellHalaszThreshold : ℕ := 10 ^ 16

/-- The initial-segment envelope supplied by IV-0f-3 at top scale `b`. -/
noncomputable def cellHalaszPartialBudget (D δ₀ : ℝ) (b : ℕ) : ℝ :=
  (cellHalaszThreshold : ℝ) + 1
    + halaszBudgetShell D (3 * (b : ℝ)) / (18 * δ₀)
    + (Real.exp 1 * (b : ℝ) * δ₀ + 1)

/-- The Abel factor, made uniform on `|t| ≤ T`. -/
noncomputable def cellHalaszAbelFactor (T : ℝ) : ℝ :=
  3 + 2 * Real.pi * T

/-- The harmless possible last point left when natural-number division
turns a factor-two block into a block with top `2a+1`. -/
noncomputable def cellHalaszDivisionTail (a b : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc (2 * a) b, (1 : ℝ) / n

/-- The long-block Halász cost at quotient endpoints `(a,b]`. -/
noncomputable def cellHalaszLongCost (D δ₀ T : ℝ) (a b : ℕ) : ℝ :=
  cellHalaszPartialBudget D δ₀ b * cellHalaszAbelFactor T / (a : ℝ)
    + cellHalaszDivisionTail a b

/-- The exact harmonic cost used below the Halász cutoff. -/
noncomputable def cellHalaszTrivialCost (a b : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc a b, (1 : ℝ) / n

/-- The explicit long/short cost for one quotient block. -/
noncomputable def cellHalaszQuotientCost
    (D δ₀ T : ℝ) (a b : ℕ) : ℝ :=
  if cellHalaszThreshold ≤ b then cellHalaszLongCost D δ₀ T a b
  else cellHalaszTrivialCost a b

/-- A norm-one coefficient has at most the harmonic mass of its block,
uniformly in frequency. -/
theorem norm_dirichlet_poly_le_harmonic (c : ℕ → ℂ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (a b : ℕ) (t : ℝ) :
    ‖∑ n ∈ Finset.Ioc a b, (c n / (n : ℂ))
        * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
      ≤ ∑ n ∈ Finset.Ioc a b, (1 : ℝ) / n := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  rw [norm_mul, norm_div, Complex.norm_natCast, norm_eq_of_mem_sphere, mul_one]
  exact div_le_div_of_nonneg_right (hc n) (by positivity)

/-- Dividing a factor-two natural block, including one previously
accumulated floor endpoint, still costs at most one endpoint:
`B ≤ 2A+1` implies `B/d ≤ 2(A/d)+1`. -/
theorem div_le_two_mul_div_add_one (A B d : ℕ) (hd : 0 < d)
    (hB : B ≤ 2 * A + 1) :
    B / d ≤ 2 * (A / d) + 1 := by
  have hAupper : A < (A / d + 1) * d :=
    (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (A / d))
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hd]
  nlinarith

/-- The `P`-free restriction of a level-free twist is the unrestricted
twist for `P :: levels`. -/
theorem sum_filter_levelFreeTwist_eq_cons
    (g : ℕ → ℂ) (P : Finset ℕ) (levels : List (Finset ℕ))
    (a b : ℕ) (t : ℝ) :
    ∑ n ∈ (Finset.Ioc a b).filter (fun n => ∀ p ∈ P, ¬ p ∣ n),
        (levelFreeTwist g levels n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)
      = ∑ n ∈ Finset.Ioc a b,
          (levelFreeTwist g (P :: levels) n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ) := by
  classical
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [levelFreeTwist_eq_if, levelFreeTwist_eq_if]
  by_cases hPfree : ∀ p ∈ P, ¬ p ∣ n
  · rw [if_pos hPfree]
    by_cases hfree : ∀ Q ∈ levels, ∀ p ∈ Q, ¬ p ∣ n
    · rw [if_pos hfree, if_pos]
      simpa only [List.forall_mem_cons] using And.intro hPfree hfree
    · have hcons : ¬ ∀ Q ∈ P :: levels, ∀ p ∈ Q, ¬ p ∣ n := by
        have hcons' : ¬ ((∀ p ∈ P, ¬ p ∣ n) ∧
            ∀ Q ∈ levels, ∀ p ∈ Q, ¬ p ∣ n) := fun h => hfree h.2
        simpa only [List.forall_mem_cons] using hcons'
      rw [if_neg hfree, if_neg hcons]
  · have hcons : ¬ ∀ Q ∈ P :: levels, ∀ p ∈ Q, ¬ p ∣ n := by
      have hcons' : ¬ ((∀ p ∈ P, ¬ p ∣ n) ∧
          ∀ Q ∈ levels, ∀ p ∈ Q, ¬ p ∣ n) := fun h => hPfree h.1
      simpa only [List.forall_mem_cons] using hcons'
    rw [if_neg hPfree, if_neg hcons]
    simp

/-- Abel plus IV-0f-3 on a long quotient block.  The only cost of the
floor endpoints is the explicitly displayed harmonic tail beyond `2a`. -/
theorem norm_levelFreeTwist_long_block_le
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g)
    (hg : ∀ n, ‖g n‖ ≤ 1) (h1 : g 1 = 1)
    (levels : List (Finset ℕ))
    (hlevels : ∀ Q ∈ levels, ∀ p ∈ Q, p.Prime)
    (D : ℝ) (hD : 1 ≤ D) (δ₀ : ℝ) (hδ0 : 0 < δ₀) (hδ1 : δ₀ ≤ 1)
    (a b : ℕ) (hab : a ≤ b) (hb2 : b ≤ 2 * a + 1)
    (T t : ℝ) (ht : |t| ≤ T)
    (hlong : cellHalaszThreshold ≤ b)
    (hNP : ∀ u : ℕ, cellHalaszThreshold ≤ u → u ≤ 3 * b →
      NonPretentiousAt g (2 * D) u) :
    ‖∑ n ∈ Finset.Ioc a b, (levelFreeTwist g levels n / (n : ℂ))
        * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
      ≤ cellHalaszLongCost D δ₀ T a b := by
  classical
  have ha : 1 ≤ a := by
    unfold cellHalaszThreshold at hlong
    omega
  let c := min b (2 * a)
  have hac : a ≤ c := by simp only [c]; omega
  have hcb : c ≤ b := min_le_left _ _
  have hc2 : c ≤ 2 * a := min_le_right _ _
  have htwcm := completelyMultiplicativeC_levelFreeTwist g hcm levels hlevels
  have htw1 := levelFreeTwist_one g h1 levels hlevels
  have htwbd := norm_levelFreeTwist_le_one g hg levels
  have hpartial : ∀ u : ℕ, u ≤ b →
      ‖∑ k ∈ Finset.Icc 0 u, levelFreeTwist g levels k‖
        ≤ cellHalaszPartialBudget D δ₀ b := by
    have hs := sup_partial_le_halaszBudgetShell
      (levelFreeTwist g levels) htwbd htwcm htw1 b hlong D hD
      δ₀ hδ0 hδ1 (fun u hu hub =>
        nonPretentiousAt_levelFreeTwist g hg levels D
          (zero_le_one.trans hD) u (hNP u hu hub))
    simpa only [cellHalaszPartialBudget, cellHalaszThreshold,
      Nat.cast_pow, Nat.cast_ofNat] using hs
  have hmain := norm_short_poly_le_sup_partial
    (levelFreeTwist g levels) a c ha hac hc2 t
    (cellHalaszPartialBudget D δ₀ b)
    (fun u hu => hpartial u (hu.trans hcb))
  have hbudget0 : 0 ≤ cellHalaszPartialBudget D δ₀ b :=
    le_trans (norm_nonneg _) (hpartial 0 (Nat.zero_le _))
  have haR : (0 : ℝ) < (a : ℝ) := by positivity
  have hmainT :
      ‖∑ n ∈ Finset.Ioc a c, (levelFreeTwist g levels n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
        ≤ cellHalaszPartialBudget D δ₀ b
            * cellHalaszAbelFactor T / (a : ℝ) := by
    refine hmain.trans ?_
    unfold cellHalaszAbelFactor
    gcongr
  have hsplit : Finset.Ioc a c ∪ Finset.Ioc c b = Finset.Ioc a b :=
    Finset.Ioc_union_Ioc_eq_Ioc hac hcb
  have hdisj : Disjoint (Finset.Ioc a c) (Finset.Ioc c b) := by
    refine Finset.disjoint_left.mpr fun n hn1 hn2 => ?_
    rw [Finset.mem_Ioc] at hn1 hn2
    omega
  rw [← hsplit, Finset.sum_union hdisj]
  refine (norm_add_le _ _).trans ?_
  have htail := norm_dirichlet_poly_le_harmonic
    (levelFreeTwist g levels) htwbd c b t
  have htailset : Finset.Ioc c b = Finset.Ioc (2 * a) b := by
    by_cases hba : b ≤ 2 * a
    · have hc : c = b := min_eq_left hba
      rw [hc]
      ext n
      simp only [Finset.mem_Ioc]
      omega
    · have hc : c = 2 * a := min_eq_right (le_of_not_ge hba)
      rw [hc]
  rw [htailset] at htail
  rw [htailset]
  simpa [cellHalaszLongCost, cellHalaszDivisionTail] using
    add_le_add hmainT htail

/-! ## IV-0d: Ramaré weight removal with an explicit quotient budget -/

/-- The harmonic mass of the `P`-supported factors occurring in the
Ramaré factorization. -/
noncomputable def pSmoothHarmonicMass (B : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 B).filter (fun n => n.primeFactors ⊆ P),
    (1 : ℝ) / n

/-- The largest explicit quotient-block cost among the finitely many
`P`-supported factors.  Inserting `0` makes the maximum total even when
the factor set is empty and records nonnegativity without a side condition. -/
noncomputable def cellHalaszQuotientBudget
    (D δ₀ T : ℝ) (A B : ℕ) (P : Finset ℕ) : ℝ :=
  let costs := ((Finset.Icc 1 B).filter
    (fun n => n.primeFactors ⊆ P)).image (fun n =>
      cellHalaszQuotientCost D δ₀ T (A / n) (B / n))
  (insert 0 costs).max' (insert_nonempty 0 costs)

theorem cellHalaszQuotientCost_le_budget
    (D δ₀ T : ℝ) (A B : ℕ) (P : Finset ℕ)
    (n : ℕ) (hn : n ∈ (Finset.Icc 1 B).filter
      (fun n => n.primeFactors ⊆ P)) :
    cellHalaszQuotientCost D δ₀ T (A / n) (B / n)
      ≤ cellHalaszQuotientBudget D δ₀ T A B P := by
  classical
  unfold cellHalaszQuotientBudget
  apply Finset.le_max'
  rw [Finset.mem_insert]
  right
  exact Finset.mem_image.mpr ⟨n, hn, rfl⟩

/-- One `P`-free quotient polynomial is bounded by its explicit
long/short cost. -/
theorem norm_filter_levelFreeTwist_quotient_le_cost
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g)
    (hg : ∀ n, ‖g n‖ ≤ 1) (h1 : g 1 = 1)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (levels : List (Finset ℕ))
    (hlevels : ∀ Q ∈ levels, ∀ p ∈ Q, p.Prime)
    (D : ℝ) (hD : 1 ≤ D) (δ₀ : ℝ) (hδ0 : 0 < δ₀) (hδ1 : δ₀ ≤ 1)
    (A B n₁ : ℕ) (hn₁ : 0 < n₁) (hAB : A ≤ B) (hB2 : B ≤ 2 * A + 1)
    (T t : ℝ) (ht : |t| ≤ T)
    (hNP : ∀ u : ℕ, cellHalaszThreshold ≤ u → u ≤ 3 * (B / n₁) →
      NonPretentiousAt g (2 * D) u) :
    ‖∑ n ∈ (Finset.Ioc (A / n₁) (B / n₁)).filter
          (fun n => ∀ p ∈ P, ¬ p ∣ n),
        (levelFreeTwist g levels n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
      ≤ cellHalaszQuotientCost D δ₀ T (A / n₁) (B / n₁) := by
  rw [sum_filter_levelFreeTwist_eq_cons]
  by_cases hlong : cellHalaszThreshold ≤ B / n₁
  · rw [cellHalaszQuotientCost, if_pos hlong]
    apply norm_levelFreeTwist_long_block_le g hcm hg h1 (P :: levels)
      (by
        intro Q hQ p hpQ
        rw [List.mem_cons] at hQ
        rcases hQ with rfl | hQ
        · exact hP p hpQ
        · exact hlevels Q hQ p hpQ)
      D hD δ₀ hδ0 hδ1 (A / n₁) (B / n₁)
      (Nat.div_le_div_right hAB)
      (div_le_two_mul_div_add_one A B n₁ hn₁ hB2)
      T t ht hlong hNP
  · rw [cellHalaszQuotientCost, if_neg hlong]
    exact norm_dirichlet_poly_le_harmonic
      (levelFreeTwist g (P :: levels))
      (norm_levelFreeTwist_le_one g hg (P :: levels)) (A / n₁) (B / n₁) t

/-- Ramaré weight removal followed by the uniform maximum of the
explicit quotient costs. -/
theorem norm_levelFreeTwist_ramare_poly_le
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g)
    (hg : ∀ n, ‖g n‖ ≤ 1) (h1 : g 1 = 1)
    (levels : List (Finset ℕ))
    (hlevels : ∀ Q ∈ levels, ∀ p ∈ Q, p.Prime)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (D : ℝ) (hD : 1 ≤ D) (δ₀ : ℝ) (hδ0 : 0 < δ₀) (hδ1 : δ₀ ≤ 1)
    (A B : ℕ) (hAB : A ≤ B) (hB2 : B ≤ 2 * A + 1)
    (T t : ℝ) (ht : |t| ≤ T)
    (hNP : ∀ u : ℕ, cellHalaszThreshold ≤ u → u ≤ 3 * B →
      NonPretentiousAt g (2 * D) u) :
    ‖∑ n ∈ Finset.Ioc A B,
        (levelFreeTwist g levels n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)
          / (((P.filter (· ∣ n)).card : ℂ) + 1)‖
      ≤ pSmoothHarmonicMass B P *
          cellHalaszQuotientBudget D δ₀ T A B P := by
  have htwcm := completelyMultiplicativeC_levelFreeTwist g hcm levels hlevels
  have htwbd := norm_levelFreeTwist_le_one g hg levels
  refine (norm_ramare_weighted_poly_le (levelFreeTwist g levels)
    htwcm htwbd A B P hP t
    (cellHalaszQuotientBudget D δ₀ T A B P) ?_).trans_eq ?_
  · intro n₁ hn₁
    have hn₁pos : 0 < n₁ := by
      rw [Finset.mem_filter, Finset.mem_Icc] at hn₁
      exact hn₁.1.1
    refine (norm_filter_levelFreeTwist_quotient_le_cost g hcm hg h1 P hP
      levels hlevels D hD δ₀ hδ0 hδ1 A B n₁ hn₁pos hAB hB2 T t ht ?_).trans
      (cellHalaszQuotientCost_le_budget D δ₀ T A B P n₁ hn₁)
    intro u hu hub
    apply hNP u hu
    have hdiv : B / n₁ ≤ B := Nat.div_le_self _ _
    omega
  · rfl

/-! ## VI-6: the per-cell Halász input -/

/-- The complete explicit `δ` for one cell.  Its factors are, in order,
the `2^J` inclusion–exclusion cost, the `P`-smooth harmonic mass from
Ramaré weight removal, and the largest fully expanded long/short
quotient-block cost. -/
noncomputable def cellHalaszBound
    (D δ₀ T : ℝ) (Aq Bq : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ)) : ℝ :=
  ((2 ^ rest.length : ℕ) : ℝ) * pSmoothHarmonicMass Bq P
    * cellHalaszQuotientBudget D δ₀ T Aq Bq P

/-- **The per-cell Halász input** (Track R, A2-III, VI-6).

Uniformly for `|t| ≤ T`, the cell representative block is bounded by
the named quantity `cellHalaszBound`.  Expanding its definitions shows
all constants: `2^rest.length`, the `P`-smooth harmonic mass up to
`B/q`, IV-0f-3's `halaszBudgetShell D (3b)`, the free parameter
`δ₀ ∈ (0,1]`, Abel's `3+2πT` divided by the quotient scale
`(A/q)/n₁`, the possible one-point division tail, and the exact
harmonic mass of every block whose top is below `10^16`.

The hypothesis on `g` is at strength `2D`; Ramaré robustness transfers
it to every inclusion–exclusion and `P`-free twist at strength `D`. -/
theorem norm_typicalS_quot_block_poly_le
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g)
    (hg : ∀ n, ‖g n‖ ≤ 1) (h1 : g 1 = 1)
    (A B q : ℕ) (hq : 1 ≤ q) (hAB : A ≤ B) (hB2 : B ≤ 2 * A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ))
    (hrest : ∀ Q ∈ rest, ∀ p ∈ Q, p.Prime)
    (D : ℝ) (hD : 1 ≤ D) (δ₀ : ℝ) (hδ0 : 0 < δ₀) (hδ1 : δ₀ ≤ 1)
    (T t : ℝ) (ht : |t| ≤ T)
    (hNP : ∀ u : ℕ, cellHalaszThreshold ≤ u → u ≤ 3 * (B / q) →
      NonPretentiousAt g (2 * D) u) :
    ‖∑ n ∈ Finset.Ioc (A / q) (B / q),
        (typicalSQuotCoeff g P (typicalS 0 B rest) n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
      ≤ cellHalaszBound D δ₀ T (A / q) (B / q) P rest := by
  classical
  have hq0 : 0 < q := hq
  have hABq : A / q ≤ B / q := Nat.div_le_div_right hAB
  have hBq2 : B / q ≤ 2 * (A / q) + 1 :=
    div_le_two_mul_div_add_one A B q hq0 (by omega)
  have hBqB : B / q ≤ B := Nat.div_le_self _ _
  refine (norm_typicalSQuotCoeff_poly_le_inclexcl g P rest
    (A / q) (B / q) B hBqB t).trans ?_
  let C : ℝ := pSmoothHarmonicMass (B / q) P
    * cellHalaszQuotientBudget D δ₀ T (A / q) (B / q) P
  calc
    (rest.sublists.map fun S =>
        ‖∑ n ∈ Finset.Ioc (A / q) (B / q),
            (levelFreeTwist g S n / (n : ℂ))
              * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)
              / (((P.filter (· ∣ n)).card : ℂ) + 1)‖).sum
        ≤ (rest.sublists.map fun _ => C).sum := by
          apply List.sum_le_sum
          intro S hS
          apply norm_levelFreeTwist_ramare_poly_le g hcm hg h1 S
            (by
              intro Q hQS p hpQ
              exact hrest Q ((List.mem_sublists.mp hS).mem hQS) p hpQ)
            P hP D hD δ₀ hδ0 hδ1 (A / q) (B / q) hABq hBq2 T t ht hNP
    _ = cellHalaszBound D δ₀ T (A / q) (B / q) P rest := by
      rw [show (rest.sublists.map fun _ => C) =
          List.replicate rest.sublists.length C from List.map_const,
        List.sum_replicate, List.length_sublists, nsmul_eq_mul]
      simp only [C, cellHalaszBound]
      push_cast
      ring

end MoltResearch
