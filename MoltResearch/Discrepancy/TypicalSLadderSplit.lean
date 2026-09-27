import MoltResearch.Discrepancy.ExceptionalHalaszSharp
import MoltResearch.Discrepancy.LowBandTypicalSSharp
import MoltResearch.Discrepancy.BrunIntervalSieve

/-!
# Splitting growing ladder levels from the typical-set estimates

The sharp quotient and low-band bounds pay inclusion--exclusion only for
the fixed base levels.  The appended ladder levels are removed by a union
bound, leaving one explicit sifted logarithmic mass per ladder level.
-/

namespace MoltResearch

open Finset MeasureTheory ExpSums

/-- Some ladder level has no divisor of `n`. -/
def MissingFactorInSome (ladder : List (Finset ℕ)) (n : ℕ) : Prop :=
  ∃ L ∈ ladder, ∀ p ∈ L, ¬ p ∣ n

instance (ladder : List (Finset ℕ)) (n : ℕ) :
    Decidable (MissingFactorInSome ladder n) := by
  unfold MissingFactorInSome
  infer_instance

/-- Factor-in-every-level splits across concatenation. -/
theorem hasFactorInAll_append (base ladder : List (Finset ℕ)) (n : ℕ) :
    HasFactorInAll (base ++ ladder) n ↔
      HasFactorInAll base n ∧ HasFactorInAll ladder n := by
  constructor
  · intro h
    exact ⟨fun L hL => h L (List.mem_append_left _ hL),
      fun L hL => h L (List.mem_append_right _ hL)⟩
  · rintro ⟨hb, hl⟩ L hL
    rcases List.mem_append.mp hL with hL | hL
    · exact hb L hL
    · exact hl L hL

/-- Failure of the ladder condition is exactly absence of a divisor in
one of its levels. -/
theorem not_hasFactorInAll_iff_missingFactorInSome
    (ladder : List (Finset ℕ)) (n : ℕ) :
    ¬ HasFactorInAll ladder n ↔ MissingFactorInSome ladder n := by
  simp [HasFactorInAll, MissingFactorInSome, filter_eq_empty_iff]

/-- The appended and base quotient coefficients agree away from a
base-typical integer missing a factor in some ladder level.  Both
coefficients retain their unit norm bound. -/
theorem typicalSQuotCoeff_append_sub_support
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (P : Finset ℕ) (B n : ℕ)
    (base ladder : List (Finset ℕ)) :
    (typicalSQuotCoeff g P (typicalS 0 B (base ++ ladder)) n ≠
        typicalSQuotCoeff g P (typicalS 0 B base) n →
      n ∈ typicalS 0 B base ∧ MissingFactorInSome ladder n) ∧
    ‖typicalSQuotCoeff g P (typicalS 0 B (base ++ ladder)) n‖ ≤ 1 ∧
    ‖typicalSQuotCoeff g P (typicalS 0 B base) n‖ ≤ 1 := by
  classical
  refine ⟨?_, norm_typicalSQuotCoeff_le_one g hg _ _ _,
    norm_typicalSQuotCoeff_le_one g hg _ _ _⟩
  intro hne
  have hsub : n ∈ typicalS 0 B (base ++ ladder) →
      n ∈ typicalS 0 B base := by
    intro hn
    rw [mem_typicalS] at hn ⊢
    exact ⟨hn.1, (hasFactorInAll_append base ladder n).mp hn.2 |>.1⟩
  have hnbase : n ∈ typicalS 0 B base := by
    by_contra hn
    have hnapp : n ∉ typicalS 0 B (base ++ ladder) :=
      fun h => hn (hsub h)
    apply hne
    simp [typicalSQuotCoeff, hn, hnapp]
  refine ⟨hnbase, ?_⟩
  rw [← not_hasFactorInAll_iff_missingFactorInSome]
  intro hnladder
  apply hne
  have hnapp : n ∈ typicalS 0 B (base ++ ladder) := by
    rw [mem_typicalS] at hnbase ⊢
    exact ⟨hnbase.1,
      (hasFactorInAll_append base ladder n).mpr ⟨hnbase.2, hnladder⟩⟩
  simp [typicalSQuotCoeff, hnbase, hnapp]

/-- Sum of the sifted logarithmic masses attached to the ladder levels. -/
noncomputable def ladderSiftedLogMass
    (a b : ℕ) (ladder : List (Finset ℕ)) : ℝ :=
  ∑ L ∈ ladder.toFinset,
    ∑ n ∈ (Ioc a b).filter (fun n => ∀ p ∈ L, ¬ p ∣ n),
      (1 : ℝ) / n

/-- The quotient coefficient changes by at most one, and only on the
union of the ladder-sifted sets. -/
theorem norm_typicalSQuotCoeff_append_sub_le
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (P : Finset ℕ) (B n : ℕ)
    (base ladder : List (Finset ℕ)) :
    ‖typicalSQuotCoeff g P (typicalS 0 B (base ++ ladder)) n -
        typicalSQuotCoeff g P (typicalS 0 B base) n‖ ≤
      if MissingFactorInSome ladder n then 1 else 0 := by
  classical
  by_cases happ : n ∈ typicalS 0 B (base ++ ladder)
  · have hbase : n ∈ typicalS 0 B base := by
      rw [mem_typicalS] at happ ⊢
      exact ⟨happ.1, (hasFactorInAll_append base ladder n).mp happ.2 |>.1⟩
    simp only [typicalSQuotCoeff, if_pos happ, if_pos hbase, sub_self,
      norm_zero]
    split <;> norm_num
  · by_cases hbase : n ∈ typicalS 0 B base
    · have hmissing : MissingFactorInSome ladder n := by
        rw [← not_hasFactorInAll_iff_missingFactorInSome]
        intro hall
        apply happ
        rw [mem_typicalS] at hbase ⊢
        exact ⟨hbase.1,
          (hasFactorInAll_append base ladder n).mpr ⟨hbase.2, hall⟩⟩
      simp only [typicalSQuotCoeff, if_neg happ, if_pos hbase,
        zero_sub, norm_neg, if_pos hmissing]
      simpa [typicalSQuotCoeff, hbase] using
        norm_typicalSQuotCoeff_le_one g hg P (typicalS 0 B base) n
    · simp only [typicalSQuotCoeff, if_neg happ, if_neg hbase,
        sub_self, norm_zero]
      split <;> norm_num

/-- Replacing appended ladder support by base support costs at most the
sum of the ladder's sifted logarithmic masses. -/
theorem norm_typicalSQuotCoeff_append_poly_sub_le
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (P : Finset ℕ) (u v B : ℕ)
    (base ladder : List (Finset ℕ)) (t : ℝ) :
    ‖(∑ n ∈ Ioc u v,
        (typicalSQuotCoeff g P (typicalS 0 B (base ++ ladder)) n /
            (n : ℂ)) *
          ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)) -
      ∑ n ∈ Ioc u v,
        (typicalSQuotCoeff g P (typicalS 0 B base) n / (n : ℂ)) *
          ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
      ≤ ladderSiftedLogMass u v ladder := by
  classical
  rw [← sum_sub_distrib]
  calc
    ‖∑ n ∈ Ioc u v,
        ((typicalSQuotCoeff g P (typicalS 0 B (base ++ ladder)) n /
              (n : ℂ)) *
            ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ) -
          (typicalSQuotCoeff g P (typicalS 0 B base) n / (n : ℂ)) *
            ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ))‖
        ≤ ∑ n ∈ Ioc u v,
          ‖(typicalSQuotCoeff g P (typicalS 0 B (base ++ ladder)) n /
                (n : ℂ)) *
              ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ) -
            (typicalSQuotCoeff g P (typicalS 0 B base) n / (n : ℂ)) *
              ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Ioc u v,
        ∑ L ∈ ladder.toFinset,
          if (∀ p ∈ L, ¬ p ∣ n) then (1 : ℝ) / n else 0 := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by
        exact_mod_cast (by have := (mem_Ioc.mp hn).1; omega : 0 < n)
      by_cases hmissing : MissingFactorInSome ladder n
      · have hmissing' := hmissing
        rcases hmissing with ⟨L, hL, hno⟩
        have hterm :
            ‖(typicalSQuotCoeff g P (typicalS 0 B (base ++ ladder)) n /
                  (n : ℂ)) *
                ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ) -
              (typicalSQuotCoeff g P (typicalS 0 B base) n / (n : ℂ)) *
                ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
              ≤ (1 : ℝ) / n := by
          rw [← sub_mul, ← sub_div]
          simp only [norm_mul, norm_div, Complex.norm_natCast,
            Circle.norm_coe, mul_one]
          have hc := norm_typicalSQuotCoeff_append_sub_le
            g hg P B n base ladder
          have hc' :
              ‖typicalSQuotCoeff g P (typicalS 0 B (base ++ ladder)) n -
                typicalSQuotCoeff g P (typicalS 0 B base) n‖ ≤ 1 := by
            simpa [hmissing'] using hc
          exact div_le_div_of_nonneg_right hc' hn0.le
        refine hterm.trans ?_
        have hsingle := Finset.single_le_sum
          (s := ladder.toFinset)
          (f := fun L => if (∀ p ∈ L, ¬ p ∣ n) then (1 : ℝ) / n else 0)
          (fun L _ => by positivity) (by simpa using hL)
        rw [if_pos hno] at hsingle
        exact hsingle
      · have heq :
            typicalSQuotCoeff g P (typicalS 0 B (base ++ ladder)) n =
              typicalSQuotCoeff g P (typicalS 0 B base) n := by
          by_contra hne
          exact hmissing
            ((typicalSQuotCoeff_append_sub_support
              g hg P B n base ladder).1 hne).2
        have hnonneg : (0 : ℝ) ≤ ∑ L ∈ ladder.toFinset,
            if (∀ p ∈ L, ¬ p ∣ n) then (1 : ℝ) / n else 0 := by
          positivity
        simpa [heq] using hnonneg
    _ = ladderSiftedLogMass u v ladder := by
      unfold ladderSiftedLogMass
      simp only [sum_filter]
      rw [sum_comm]

/-- **Sharp quotient bound with growing ladder levels removed by
density.**  Inclusion--exclusion sees only `base`; the appended levels
contribute their sifted logarithmic masses. -/
theorem norm_typicalS_quot_block_poly_le_sharp_split
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg1 : g 1 = 1)
    (hgb : ∀ n, ‖g n‖ ≤ 1)
    (A B q : ℕ) (hAB : A ≤ B)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (base ladder : List (Finset ℕ))
    (hbase : ∀ Q ∈ base, ∀ p ∈ Q, p.Prime)
    (x0 : ℕ) (hx0 : cellHalaszThreshold ≤ x0)
    (D : ℝ) (hD : 1 ≤ D) (t : ℝ)
    (hwin : ∀ n1 ∈ (Icc 1 (B / q)).filter (fun n => n.primeFactors ⊆ P),
      x0 ≤ (A / q) / n1 →
      ∀ u : ℕ, (A / q) / n1 ≤ u → u ≤ 3 * ((B / q) / n1) →
        HalaszWindowAt
          (fun n => g n * (n : ℂ) ^
            (Complex.I * ((-(2 * Real.pi * t) : ℝ) : ℂ))) (2 * D) u)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₁ : δ₀ ≤ 1) :
    ‖∑ n ∈ Ioc (A / q) (B / q),
        (typicalSQuotCoeff g P
            (typicalS 0 B (base ++ ladder)) n / (n : ℂ)) *
          ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
      ≤ cellHalaszSharpBound x0 D δ₀ (A / q) (B / q) P base +
        ladderSiftedLogMass (A / q) (B / q) ladder := by
  let Pfull : ℂ := ∑ n ∈ Ioc (A / q) (B / q),
    (typicalSQuotCoeff g P (typicalS 0 B (base ++ ladder)) n /
        (n : ℂ)) *
      ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)
  let Pbase : ℂ := ∑ n ∈ Ioc (A / q) (B / q),
    (typicalSQuotCoeff g P (typicalS 0 B base) n / (n : ℂ)) *
      ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)
  change ‖Pfull‖ ≤ _
  have hdiff : ‖Pfull - Pbase‖ ≤
      ladderSiftedLogMass (A / q) (B / q) ladder := by
    dsimp only [Pfull, Pbase]
    exact norm_typicalSQuotCoeff_append_poly_sub_le g hgb P
      (A / q) (B / q) B base ladder t
  have hsharp : ‖Pbase‖ ≤
      cellHalaszSharpBound x0 D δ₀ (A / q) (B / q) P base := by
    dsimp only [Pbase]
    exact norm_typicalS_quot_block_poly_le_sharp g hcm hg1 hgb A B q
      hAB P hP base hbase x0 hx0 D hD t hwin δ₀ hδ₀ hδ₁
  calc
    ‖Pfull‖ = ‖(Pfull - Pbase) + Pbase‖ := by
      congr 1
      ring
    _ ≤ ‖Pfull - Pbase‖ + ‖Pbase‖ := norm_add_le _ _
    _ ≤ ladderSiftedLogMass (A / q) (B / q) ladder +
        cellHalaszSharpBound x0 D δ₀ (A / q) (B / q) P base :=
      add_le_add hdiff hsharp
    _ = _ := add_comm _ _

/-- The direct Brun upper bound for one level's sifted logarithmic mass. -/
noncomputable def brunSiftedLogMassBound
    (a b : ℕ) (L : Finset ℕ) (k : ℕ) : ℝ :=
  (1 / (a : ℝ)) *
    (((b : ℝ) - a) *
      ((∏ p ∈ L, (1 - 1 / (p : ℝ))) +
        (∑ p ∈ L, (1 : ℝ) / p) ^ (2 * k + 1) /
          ((2 * k + 1).factorial : ℝ)) +
      ((L.card : ℝ) + 1) ^ (2 * k))

/-- Sum of the direct Brun bounds, allowing a separate truncation depth
for every ladder level. -/
noncomputable def ladderBrunLogMassBound
    (a b : ℕ) (ladder : List (Finset ℕ))
    (ks : Finset ℕ → ℕ) : ℝ :=
  ∑ L ∈ ladder.toFinset, brunSiftedLogMassBound a b L (ks L)

/-- The explicit Brun expression bounds the ladder remainder. -/
theorem ladderSiftedLogMass_le_brun
    (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b)
    (ladder : List (Finset ℕ))
    (hladder : ∀ L ∈ ladder, ∀ p ∈ L, p.Prime)
    (ks : Finset ℕ → ℕ) :
    ladderSiftedLogMass a b ladder ≤
      ladderBrunLogMassBound a b ladder ks := by
  classical
  unfold ladderSiftedLogMass ladderBrunLogMassBound
  apply sum_le_sum
  intro L hL
  exact sum_one_div_no_factor_Ioc_le_brun a b ha hab L
    (fun p hp => hladder L (by simpa using hL) p hp) (ks L)

/-- The sharp quotient split with every ladder remainder replaced by its
compiled Brun expression. -/
theorem norm_typicalS_quot_block_poly_le_sharp_split_brun
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg1 : g 1 = 1)
    (hgb : ∀ n, ‖g n‖ ≤ 1)
    (A B q : ℕ) (hAB : A ≤ B) (hAq : 1 ≤ A / q)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (base ladder : List (Finset ℕ))
    (hbase : ∀ Q ∈ base, ∀ p ∈ Q, p.Prime)
    (hladder : ∀ L ∈ ladder, ∀ p ∈ L, p.Prime)
    (ks : Finset ℕ → ℕ)
    (x0 : ℕ) (hx0 : cellHalaszThreshold ≤ x0)
    (D : ℝ) (hD : 1 ≤ D) (t : ℝ)
    (hwin : ∀ n1 ∈ (Icc 1 (B / q)).filter (fun n => n.primeFactors ⊆ P),
      x0 ≤ (A / q) / n1 →
      ∀ u : ℕ, (A / q) / n1 ≤ u → u ≤ 3 * ((B / q) / n1) →
        HalaszWindowAt
          (fun n => g n * (n : ℂ) ^
            (Complex.I * ((-(2 * Real.pi * t) : ℝ) : ℂ))) (2 * D) u)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₁ : δ₀ ≤ 1) :
    ‖∑ n ∈ Ioc (A / q) (B / q),
        (typicalSQuotCoeff g P
            (typicalS 0 B (base ++ ladder)) n / (n : ℂ)) *
          ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
      ≤ cellHalaszSharpBound x0 D δ₀ (A / q) (B / q) P base +
        ladderBrunLogMassBound (A / q) (B / q) ladder ks := by
  refine (norm_typicalS_quot_block_poly_le_sharp_split g hcm hg1 hgb
    A B q hAB P hP base ladder hbase x0 hx0 D hD t hwin δ₀ hδ₀ hδ₁).trans ?_
  exact add_le_add le_rfl
    (ladderSiftedLogMass_le_brun (A / q) (B / q) hAq
      (Nat.div_le_div_right hAB) ladder hladder ks)

/-- A typical-set polynomial is the empty-Ramaré-level quotient
polynomial on the same interval. -/
theorem sum_typicalS_eq_quotCoeff_empty
    (g : ℕ → ℂ) (a b : ℕ) (levels : List (Finset ℕ)) (t : ℝ) :
    (∑ m ∈ typicalS a b levels,
        (g m / (m : ℂ)) *
          ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)) =
      ∑ m ∈ Ioc a b,
        (typicalSQuotCoeff g ∅ (typicalS 0 b levels) m / (m : ℂ)) *
          ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ) := by
  classical
  rw [typicalS, sum_filter]
  apply sum_congr rfl
  intro m hm
  have hm0 : 0 < m := by
    exact (Nat.zero_le a).trans_lt (mem_Ioc.mp hm).1
  have hmem : m ∈ typicalS 0 b levels ↔ HasFactorInAll levels m := by
    rw [mem_typicalS]
    simp [hm0, (mem_Ioc.mp hm).2]
  by_cases hall : HasFactorInAll levels m
  · rw [if_pos hall]
    simp [typicalSQuotCoeff, hmem.mpr hall]
  · rw [if_neg hall]
    simp [typicalSQuotCoeff, hmem.not.mpr hall]

/-- The low-band polynomial changes by at most the same ladder sifted
mass as the quotient polynomial. -/
theorem norm_typicalS_append_poly_sub_le
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (a b : ℕ) (base ladder : List (Finset ℕ)) (t : ℝ) :
    ‖(∑ m ∈ typicalS a b (base ++ ladder),
        (g m / (m : ℂ)) *
          ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)) -
      ∑ m ∈ typicalS a b base,
        (g m / (m : ℂ)) *
          ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖
      ≤ ladderSiftedLogMass a b ladder := by
  rw [sum_typicalS_eq_quotCoeff_empty g a b (base ++ ladder) t,
    sum_typicalS_eq_quotCoeff_empty g a b base t]
  exact norm_typicalSQuotCoeff_append_poly_sub_le g hg ∅ a b b
    base ladder t

/-- **Sharp low-band pointwise bound with growing ladder levels removed
by density.** -/
theorem norm_typicalS_dirichlet_poly_le_low_band_sharp_split
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg1 : g 1 = 1)
    (hgb : ∀ n, ‖g n‖ ≤ 1)
    (base ladder : List (Finset ℕ))
    (hbase : ∀ Q ∈ base, ∀ p ∈ Q, p.Prime)
    (a b : ℕ) (ha : 10 ^ 16 ≤ a) (hab : a < b)
    (D : ℝ) (hD : 2 ≤ D)
    (hnp : ∀ u : ℕ, a ≤ u → u ≤ 3 * b →
      NonPretentiousAt g (2 * D) u)
    (delta0 : ℝ) (hdelta0 : 0 < delta0) (hdelta1 : delta0 ≤ 1)
    (t : ℝ) (hfreq : |2 * Real.pi * t| ≤ (D / 2) * a) :
    ‖∑ m ∈ typicalS a b (base ++ ladder),
        (g m / (m : ℂ)) *
          ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖
      ≤ (2 ^ base.length : ℕ) *
          sharpTwistedDirichletCost (D / 2) delta0 a b +
        ladderSiftedLogMass a b ladder := by
  let Pfull : ℂ := ∑ m ∈ typicalS a b (base ++ ladder),
    (g m / (m : ℂ)) *
      ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)
  let Pbase : ℂ := ∑ m ∈ typicalS a b base,
    (g m / (m : ℂ)) *
      ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)
  change ‖Pfull‖ ≤ _
  have hdiff : ‖Pfull - Pbase‖ ≤ ladderSiftedLogMass a b ladder := by
    dsimp only [Pfull, Pbase]
    exact norm_typicalS_append_poly_sub_le g hgb a b base ladder t
  have hsharp : ‖Pbase‖ ≤
      (2 ^ base.length : ℕ) *
        sharpTwistedDirichletCost (D / 2) delta0 a b := by
    dsimp only [Pbase]
    exact norm_typicalS_dirichlet_poly_le_low_band_sharp g hcm hg1 hgb
      base hbase a b ha hab D hD hnp delta0 hdelta0 hdelta1 t hfreq
  calc
    ‖Pfull‖ = ‖(Pfull - Pbase) + Pbase‖ := by
      congr 1
      ring
    _ ≤ ‖Pfull - Pbase‖ + ‖Pbase‖ := norm_add_le _ _
    _ ≤ ladderSiftedLogMass a b ladder +
        (2 ^ base.length : ℕ) *
          sharpTwistedDirichletCost (D / 2) delta0 a b :=
      add_le_add hdiff hsharp
    _ = _ := add_comm _ _

/-- The pointwise low-band split with the ladder remainder replaced by
the direct Brun expression. -/
theorem norm_typicalS_dirichlet_poly_le_low_band_sharp_split_brun
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg1 : g 1 = 1)
    (hgb : ∀ n, ‖g n‖ ≤ 1)
    (base ladder : List (Finset ℕ))
    (hbase : ∀ Q ∈ base, ∀ p ∈ Q, p.Prime)
    (hladder : ∀ L ∈ ladder, ∀ p ∈ L, p.Prime)
    (ks : Finset ℕ → ℕ)
    (a b : ℕ) (ha : 10 ^ 16 ≤ a) (hab : a < b)
    (D : ℝ) (hD : 2 ≤ D)
    (hnp : ∀ u : ℕ, a ≤ u → u ≤ 3 * b →
      NonPretentiousAt g (2 * D) u)
    (delta0 : ℝ) (hdelta0 : 0 < delta0) (hdelta1 : delta0 ≤ 1)
    (t : ℝ) (hfreq : |2 * Real.pi * t| ≤ (D / 2) * a) :
    ‖∑ m ∈ typicalS a b (base ++ ladder),
        (g m / (m : ℂ)) *
          ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖
      ≤ (2 ^ base.length : ℕ) *
          sharpTwistedDirichletCost (D / 2) delta0 a b +
        ladderBrunLogMassBound a b ladder ks := by
  refine (norm_typicalS_dirichlet_poly_le_low_band_sharp_split
    g hcm hg1 hgb base ladder hbase a b ha hab D hD hnp
      delta0 hdelta0 hdelta1 t hfreq).trans ?_
  exact add_le_add le_rfl
    (ladderSiftedLogMass_le_brun a b (by omega) hab.le
      ladder hladder ks)

/-- Integrating the sharp split pointwise estimate over the low band. -/
theorem integral_norm_typicalS_dirichlet_poly_sq_le_low_band_sharp_split
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg1 : g 1 = 1)
    (hgb : ∀ n, ‖g n‖ ≤ 1)
    (base ladder : List (Finset ℕ))
    (hbase : ∀ Q ∈ base, ∀ p ∈ Q, p.Prime)
    (a b : ℕ) (ha : 10 ^ 16 ≤ a) (hab : a < b)
    (D : ℝ) (hD : 2 ≤ D)
    (hnp : ∀ u : ℕ, a ≤ u → u ≤ 3 * b →
      NonPretentiousAt g (2 * D) u)
    (delta0 : ℝ) (hdelta0 : 0 < delta0) (hdelta1 : delta0 ≤ 1)
    (K : ℝ) (hK : 0 ≤ K)
    (hfreq : 2 * Real.pi * K ≤ (D / 2) * a) :
    (∫ t in {t : ℝ | |t| < K},
      ‖∑ m ∈ typicalS a b (base ++ ladder),
          (g m / (m : ℂ)) *
            ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖ ^ 2)
      ≤ 2 * K * ((2 ^ base.length : ℕ) *
          sharpTwistedDirichletCost (D / 2) delta0 a b +
        ladderSiftedLogMass a b ladder) ^ 2 := by
  let P : ℝ → ℂ := fun t =>
    ∑ m ∈ typicalS a b (base ++ ladder), (g m / (m : ℂ)) *
      ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)
  let C : ℝ := (2 ^ base.length : ℕ) *
      sharpTwistedDirichletCost (D / 2) delta0 a b +
    ladderSiftedLogMass a b ladder
  have hPc : Continuous P := continuous_char_poly _ _ _
  have hmeas : MeasurableSet {t : ℝ | |t| < K} :=
    measurableSet_lt measurable_abs measurable_const
  have hint : IntegrableOn (fun t => ‖P t‖ ^ 2) {t : ℝ | |t| < K} :=
    integrableOn_norm_sq_inner_band P hPc 0 K _ fun t ht =>
      ⟨abs_nonneg t, le_of_lt ht⟩
  have hfin : volume {t : ℝ | |t| < K} ≠ ⊤ := by
    rw [abs_lt_set_eq_Ioo K, Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hmono : (∫ t in {t : ℝ | |t| < K}, ‖P t‖ ^ 2) ≤
      ∫ _t in {t : ℝ | |t| < K}, C ^ 2 := by
    refine setIntegral_mono_on hint (integrableOn_const hfin) hmeas ?_
    intro t ht
    have htK : |2 * Real.pi * t| ≤ 2 * Real.pi * K := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)]
      exact mul_le_mul_of_nonneg_left (le_of_lt ht) (by positivity)
    have hnorm : ‖P t‖ ≤ C :=
      norm_typicalS_dirichlet_poly_le_low_band_sharp_split
        g hcm hg1 hgb base ladder hbase a b ha hab D hD hnp
          delta0 hdelta0 hdelta1 t (htK.trans hfreq)
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [abs_lt_set_eq_Ioo K, setIntegral_const,
    Real.volume_real_Ioo_of_le (by linarith), smul_eq_mul] at hmono
  rw [abs_lt_set_eq_Ioo K]
  dsimp only [P, C] at hmono ⊢
  convert hmono using 1
  all_goals ring

/-- **Fixed-saving low-band split with an explicit ladder remainder.**

The inclusion--exclusion factor depends only on `base`.  Any nonnegative
`Rem` dominating the ladder's sifted logarithmic mass may be inserted. -/
theorem integral_norm_typicalS_dirichlet_poly_sq_le_low_band_eps_split
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ∃ (D0 : ℝ) (x0 : ℕ), 2 ≤ D0 ∧ 10 ^ 16 ≤ x0 ∧
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → g 1 = 1 →
        (∀ n, ‖g n‖ ≤ 1) →
      ∀ base ladder : List (Finset ℕ),
        (∀ Q ∈ base, ∀ p ∈ Q, p.Prime) →
      ∀ a b : ℕ, x0 ≤ a → a < b → b ≤ 3 * a →
      ∀ D : ℝ, D0 ≤ D →
        (∀ u : ℕ, a ≤ u → u ≤ 3 * b → NonPretentiousAt g (2 * D) u) →
      ∀ K : ℝ, 0 ≤ K → 2 * Real.pi * K ≤ (D / 2) * a →
      ∀ Rem : ℝ, 0 ≤ Rem → ladderSiftedLogMass a b ladder ≤ Rem →
        (∫ t in {t : ℝ | |t| < K},
          ‖∑ m ∈ typicalS a b (base ++ ladder),
              (g m / (m : ℂ)) *
                ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖ ^ 2)
          ≤ 2 * K * ((2 ^ base.length : ℕ) *
              (eta * (b : ℝ) / ((a + 1 : ℕ) : ℝ)) + Rem) ^ 2 := by
  obtain ⟨Dcost, x0, hDcost, hx0, hcost⟩ :=
    sharpTwistedDirichletCost_le_eps eta heta
  refine ⟨2 * Dcost, x0, by linarith, hx0, ?_⟩
  intro g hcm hg1 hgb base ladder hbase a b hxa hab hb3 D hD hnp
    K hK hfreq Rem hRem0 hRem
  have ha16 : 10 ^ 16 ≤ a := hx0.trans hxa
  have hD2 : 2 ≤ D := by linarith
  have hdelta0 : 0 < eta / (8 * Real.exp 1) := by positivity
  have hdelta1 : eta / (8 * Real.exp 1) ≤ 1 := by
    have hden : (1 : ℝ) ≤ 8 * Real.exp 1 := by
      nlinarith [Real.exp_one_gt_d9]
    rw [div_le_one (by positivity)]
    exact heta1.trans hden
  have hraw :=
    integral_norm_typicalS_dirichlet_poly_sq_le_low_band_sharp_split
      g hcm hg1 hgb base ladder hbase a b ha16 hab D hD2 hnp
        (eta / (8 * Real.exp 1)) hdelta0 hdelta1 K hK hfreq
  have hcost' : sharpTwistedDirichletCost (D / 2)
      (eta / (8 * Real.exp 1)) a b ≤
        eta * (b : ℝ) / ((a + 1 : ℕ) : ℝ) :=
    hcost (D / 2) (by linarith) a b hxa hab.le hb3
  have hmain :
      (2 ^ base.length : ℕ) *
          sharpTwistedDirichletCost (D / 2)
            (eta / (8 * Real.exp 1)) a b +
          ladderSiftedLogMass a b ladder ≤
        (2 ^ base.length : ℕ) *
          (eta * (b : ℝ) / ((a + 1 : ℕ) : ℝ)) + Rem :=
    add_le_add (mul_le_mul_of_nonneg_left hcost' (by positivity)) hRem
  have hleft0 : 0 ≤ (2 ^ base.length : ℕ) *
        sharpTwistedDirichletCost (D / 2)
          (eta / (8 * Real.exp 1)) a b +
        ladderSiftedLogMass a b ladder := by
    have hmass0 : 0 ≤ ladderSiftedLogMass a b ladder := by
      unfold ladderSiftedLogMass
      positivity
    exact add_nonneg
      (mul_nonneg (by positivity)
        (sharpTwistedDirichletCost_nonneg (D / 2)
          (eta / (8 * Real.exp 1)) a b (by linarith) hdelta0
            (by omega) (by omega))) hmass0
  have hpow := pow_le_pow_left₀ hleft0 hmain 2
  exact hraw.trans (mul_le_mul_of_nonneg_left hpow (by positivity))

/-- The fixed-saving integral split with `Rem` instantiated by the
per-level Brun bounds. -/
theorem integral_norm_typicalS_dirichlet_poly_sq_le_low_band_eps_split_brun
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ∃ (D0 : ℝ) (x0 : ℕ), 2 ≤ D0 ∧ 10 ^ 16 ≤ x0 ∧
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → g 1 = 1 →
        (∀ n, ‖g n‖ ≤ 1) →
      ∀ base ladder : List (Finset ℕ),
        (∀ Q ∈ base, ∀ p ∈ Q, p.Prime) →
        (∀ L ∈ ladder, ∀ p ∈ L, p.Prime) →
      ∀ ks : Finset ℕ → ℕ,
      ∀ a b : ℕ, x0 ≤ a → a < b → b ≤ 3 * a →
      ∀ D : ℝ, D0 ≤ D →
        (∀ u : ℕ, a ≤ u → u ≤ 3 * b → NonPretentiousAt g (2 * D) u) →
      ∀ K : ℝ, 0 ≤ K → 2 * Real.pi * K ≤ (D / 2) * a →
        (∫ t in {t : ℝ | |t| < K},
          ‖∑ m ∈ typicalS a b (base ++ ladder),
              (g m / (m : ℂ)) *
                ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖ ^ 2)
          ≤ 2 * K * ((2 ^ base.length : ℕ) *
              (eta * (b : ℝ) / ((a + 1 : ℕ) : ℝ)) +
            ladderBrunLogMassBound a b ladder ks) ^ 2 := by
  obtain ⟨D0, x0, hD0, hx0, hsplit⟩ :=
    integral_norm_typicalS_dirichlet_poly_sq_le_low_band_eps_split
      eta heta heta1
  refine ⟨D0, x0, hD0, hx0, ?_⟩
  intro g hcm hg1 hgb base ladder hbase hladder ks a b hxa hab hb3
    D hD hnp K hK hfreq
  have hmass := ladderSiftedLogMass_le_brun a b
    ((by norm_num : 1 ≤ 10 ^ 16).trans (hx0.trans hxa)) hab.le
    ladder hladder ks
  have hmass0 : 0 ≤ ladderSiftedLogMass a b ladder := by
    unfold ladderSiftedLogMass
    positivity
  have hbrun0 : 0 ≤ ladderBrunLogMassBound a b ladder ks :=
    hmass0.trans hmass
  exact hsplit g hcm hg1 hgb base ladder hbase a b hxa hab hb3 D hD hnp
    K hK hfreq (ladderBrunLogMassBound a b ladder ks) hbrun0 hmass

end MoltResearch
