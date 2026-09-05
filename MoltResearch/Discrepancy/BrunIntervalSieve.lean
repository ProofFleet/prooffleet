import MoltResearch.Discrepancy.MertensFirst
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Brun's pure sieve on an interval

This leaf supplies the finite Bonferroni truncation used to sift the ladder
levels.  All endpoint errors are explicit: the count of multiples in an
interval differs from its real main term by at most one, and there is one
such error for every subset retained by the truncation.
-/

namespace MoltResearch

open Finset

/-- The number of members of `P` which divide `m`. -/
def omegaFinset (P : Finset ℕ) (m : ℕ) : ℕ :=
  (P.filter (· ∣ m)).card

/-- A cardinality-truncated powerset sum is the corresponding truncated
binomial sum. -/
theorem sum_powerset_card_le_neg_one (P : Finset ℕ) (M : ℕ) :
    (∑ D ∈ P.powerset.filter (fun D => D.card ≤ M), (-1 : ℤ) ^ D.card) =
      ∑ j ∈ range (M + 1), (-1 : ℤ) ^ j * (P.card.choose j : ℤ) := by
  rw [sum_filter]
  change (∑ D ∈ P.powerset,
      (fun n => if n ≤ M then (-1 : ℤ) ^ n else 0) D.card) = _
  calc
    _ = ∑ j ∈ range (P.card + 1), P.card.choose j •
          (if j ≤ M then (-1 : ℤ) ^ j else 0) :=
      Finset.sum_powerset_apply_card
        (fun n => if n ≤ M then (-1 : ℤ) ^ n else 0)
    _ = _ := by
      simp only [nsmul_eq_mul, mul_ite, mul_zero]
      rw [← sum_filter]
      by_cases h : P.card ≤ M
      · rw [filter_eq_self.2]
        · simpa only [mul_comm] using
            (sum_subset (range_mono (Nat.succ_le_succ h)) (fun j _ hj => by
              rw [Nat.choose_eq_zero_of_lt (by simpa using hj), Nat.cast_zero,
                zero_mul]) :
              (∑ j ∈ range (P.card + 1),
                  (P.card.choose j : ℤ) * (-1 : ℤ) ^ j) =
                ∑ j ∈ range (M + 1),
                  (P.card.choose j : ℤ) * (-1 : ℤ) ^ j)
        · intro j hj
          rw [mem_range] at hj
          omega
      · rw [show (range (P.card + 1)).filter (fun j => j ≤ M) =
            range (M + 1) by
          ext j
          simp only [mem_filter, mem_range]
          omega]
        apply sum_congr rfl
        intro j hj
        ring

/-- The even Bonferroni truncation of a binomial row is nonnegative. -/
theorem bonferroni_even_nonneg (r k : ℕ) :
    (0 : ℤ) ≤ ∑ j ∈ range (2 * k + 1),
      (-1 : ℤ) ^ j * (r.choose j : ℤ) := by
  cases r with
  | zero => simp [sum_range_succ']
  | succ r =>
      rw [Int.alternating_sum_range_choose_eq_choose
        (n := r) (m := 2 * k)]
      rw [show (-1 : ℤ) ^ (2 * k) = 1 by rw [pow_mul]; norm_num,
        one_mul]
      exact Int.natCast_nonneg _

/-- The indicator of having no divisor in `P` is bounded by the even
inclusion--exclusion truncation. -/
theorem indicator_coprime_le_truncated_inclexcl
    (P : Finset ℕ) (m k : ℕ) :
    (if omegaFinset P m = 0 then 1 else 0 : ℤ) ≤
      ∑ D ∈ P.powerset.filter (fun D => D.card ≤ 2 * k),
        (-1 : ℤ) ^ D.card *
          (if ∀ p ∈ D, p ∣ m then 1 else 0) := by
  classical
  let S := P.filter (· ∣ m)
  have hsum :
      (∑ D ∈ P.powerset.filter (fun D => D.card ≤ 2 * k),
        (-1 : ℤ) ^ D.card *
          (if ∀ p ∈ D, p ∣ m then 1 else 0)) =
      ∑ D ∈ S.powerset.filter (fun D => D.card ≤ 2 * k),
        (-1 : ℤ) ^ D.card := by
    rw [sum_filter]
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [← sum_filter, ← sum_filter]
    apply sum_congr
    · ext D
      simp only [mem_filter, mem_powerset, S, subset_iff]
      aesop
    · intro D hD
      rfl
  rw [hsum, sum_powerset_card_le_neg_one S (2 * k)]
  by_cases hS : S.card = 0
  · simp only [omegaFinset, S] at hS ⊢
    simp [hS, sum_range_succ']
  · simp only [omegaFinset, S] at hS ⊢
    simp only [if_neg hS]
    exact bonferroni_even_nonneg S.card k

/-- Exact count of multiples in a natural interval. -/
theorem card_multiples_Ioc_eq (a b d : ℕ) :
    ((Ioc a b).filter (d ∣ ·)).card = b / d - a / d := by
  by_cases hab : a ≤ b
  · have heq : (Ioc a b).filter (d ∣ ·) =
        (Ioc 0 b).filter (d ∣ ·) \ (Ioc 0 a).filter (d ∣ ·) := by
      ext x
      simp only [mem_filter, mem_Ioc, mem_sdiff]
      omega
    have hsub : (Ioc 0 a).filter (d ∣ ·) ⊆
        (Ioc 0 b).filter (d ∣ ·) := by
      intro x hx
      simp only [mem_filter, mem_Ioc] at hx ⊢
      omega
    rw [heq, card_sdiff_of_subset hsub,
      Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div]
  · have hab' : b ≤ a := Nat.le_of_not_ge hab
    have hdiv : b / d ≤ a / d := Nat.div_le_div_right hab'
    simp [Ioc_eq_empty (not_lt_of_ge hab'), Nat.sub_eq_zero_of_le hdiv]

/-- The interval multiple count has the usual main term plus one endpoint
error. -/
theorem card_multiples_Ioc (a b d : ℕ) (hd : 1 ≤ d) :
    (((Ioc a b).filter (d ∣ ·)).card : ℝ) ≤
      (b - a : ℕ) / (d : ℝ) + 1 := by
  rw [card_multiples_Ioc_eq]
  by_cases hab : a ≤ b
  · have hfloorb : ((b / d : ℕ) : ℝ) ≤ (b : ℝ) / d :=
      Nat.cast_div_le
    have hfloora : (a : ℝ) / d < ((a / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ (by exact_mod_cast hd)]
      exact_mod_cast (Nat.div_lt_iff_lt_mul (by omega : 0 < d)).mp
        (Nat.lt_succ_self (a / d))
    rw [Nat.cast_sub (Nat.div_le_div_right hab)]
    have hdelta : (((b - a : ℕ) : ℝ) / (d : ℝ)) =
        (b : ℝ) / d - (a : ℝ) / d := by
      rw [Nat.cast_sub hab]
      ring
    rw [hdelta]
    linarith
  · have hdiv : b / d ≤ a / d :=
      Nat.div_le_div_right (Nat.le_of_not_ge hab)
    rw [Nat.sub_eq_zero_of_le hdiv, Nat.cast_zero]
    positivity

/-- The two-sided endpoint estimate needed when the inclusion--exclusion
coefficient is negative. -/
theorem card_multiples_Ioc_error (a b d : ℕ) (hd : 1 ≤ d) :
    |(((Ioc a b).filter (d ∣ ·)).card : ℝ) -
        (b - a : ℕ) / (d : ℝ)| ≤ 1 := by
  rw [card_multiples_Ioc_eq]
  by_cases hab : a ≤ b
  · have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have hfloorb : ((b / d : ℕ) : ℝ) ≤ (b : ℝ) / d :=
      Nat.cast_div_le
    have hfloora : ((a / d : ℕ) : ℝ) ≤ (a : ℝ) / d :=
      Nat.cast_div_le
    have hceilb : (b : ℝ) / d < ((b / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hd0]
      exact_mod_cast (Nat.div_lt_iff_lt_mul (by omega : 0 < d)).mp
        (Nat.lt_succ_self (b / d))
    have hceila : (a : ℝ) / d < ((a / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hd0]
      exact_mod_cast (Nat.div_lt_iff_lt_mul (by omega : 0 < d)).mp
        (Nat.lt_succ_self (a / d))
    rw [abs_le, Nat.cast_sub (Nat.div_le_div_right hab), Nat.cast_sub hab]
    have hdelta : ((b : ℝ) - (a : ℝ)) / (d : ℝ) =
        (b : ℝ) / d - (a : ℝ) / d := by ring
    rw [hdelta]
    constructor <;> linarith
  · have hdiv : b / d ≤ a / d :=
      Nat.div_le_div_right (Nat.le_of_not_ge hab)
    rw [Nat.sub_eq_zero_of_le hdiv,
      Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hab)]
    norm_num

/-- For a finite set of distinct primes, divisibility by every member is
equivalent to divisibility by their product. -/
theorem prod_dvd_iff_all_dvd_of_primes (D : Finset ℕ)
    (hD : ∀ p ∈ D, p.Prime) (m : ℕ) :
    (∏ p ∈ D, p) ∣ m ↔ ∀ p ∈ D, p ∣ m := by
  classical
  induction D using Finset.induction_on with
  | empty => simp
  | @insert p D hpD ih =>
      rw [prod_insert hpD]
      have hp : p.Prime := hD p (mem_insert_self p D)
      have hD' : ∀ q ∈ D, q.Prime :=
        fun q hq => hD q (mem_insert_of_mem hq)
      have hcop : Nat.Coprime p (∏ q ∈ D, q) :=
        Nat.Coprime.prod_right fun q hq =>
          (Nat.coprime_primes hp (hD' q hq)).mpr (by
            intro hpq
            exact hpD (hpq ▸ hq))
      constructor
      · intro hdvd
        have hpdiv : p ∣ m :=
          dvd_trans (dvd_mul_right p (∏ q ∈ D, q)) hdvd
        have hproddiv : (∏ q ∈ D, q) ∣ m :=
          dvd_trans (dvd_mul_left (∏ q ∈ D, q) p)
            (by simpa [mul_comm] using hdvd)
        have hall := (ih hD').mp hproddiv
        intro q hq
        rcases mem_insert.mp hq with rfl | hq
        · exact hpdiv
        · exact hall q hq
      · intro hall
        apply hcop.mul_dvd_of_dvd_of_dvd
        · exact hall p (mem_insert_self p D)
        · apply (ih hD').mpr
          exact fun q hq => hall q (mem_insert_of_mem hq)

/-- The elementary symmetric sum of degree `r`. -/
def brunElementary {α : Type*} [DecidableEq α]
    (S : Finset α) (x : α → ℝ) (r : ℕ) : ℝ :=
  ∑ D ∈ S.powersetCard r, ∏ p ∈ D, x p

/-- Elementary symmetric sums obey the insertion recurrence. -/
theorem brunElementary_insert_succ {α : Type*} [DecidableEq α]
    (S : Finset α) (a : α) (ha : a ∉ S) (x : α → ℝ) (r : ℕ) :
    brunElementary (insert a S) x (r + 1) =
      brunElementary S x (r + 1) + x a * brunElementary S x r := by
  unfold brunElementary
  rw [show r + 1 = r.succ by omega, powersetCard_succ_insert ha]
  have hdisj : Disjoint (S.powersetCard r.succ)
      ((S.powersetCard r).image (insert a)) := by
    rw [Finset.disjoint_left]
    intro D hD hDi
    obtain ⟨E, hE, rfl⟩ := mem_image.mp hDi
    exact ha ((mem_powersetCard.mp hD).1 (mem_insert_self a E))
  rw [sum_union hdisj]
  congr 1
  rw [sum_image]
  · rw [mul_sum]
    apply sum_congr rfl
    intro D hD
    rw [prod_insert (fun haD => ha ((mem_powersetCard.mp hD).1 haD))]
  · intro D hD E hE hDE
    have haD : a ∉ D :=
      fun haD => ha ((mem_powersetCard.mp hD).1 haD)
    have haE : a ∉ E :=
      fun haE => ha ((mem_powersetCard.mp hE).1 haE)
    have he := congrArg (fun T : Finset α => T.erase a) hDE
    simpa [haD, haE] using he

/-- The first two terms of the binomial expansion give this lower bound. -/
theorem pow_add_linear_le (A E : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (r : ℕ) :
    E ^ (r + 1) + (r + 1 : ℕ) * A * E ^ r ≤
      (E + A) ^ (r + 1) := by
  rw [add_pow]
  let T : Finset ℕ := {r, r + 1}
  have hsub : T ⊆ range (r + 1 + 1) := by
    intro j hj
    simp only [T, mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl <;> simp
  have hnonneg : ∀ j ∈ range (r + 1 + 1), j ∉ T →
      0 ≤ E ^ j * A ^ (r + 1 - j) * (r + 1).choose j := by
    intro j hj hjT
    positivity
  have hle := sum_le_sum_of_subset_of_nonneg hsub hnonneg
  have hsumT : ∑ j ∈ T,
      E ^ j * A ^ (r + 1 - j) * (r + 1).choose j =
      E ^ (r + 1) + (r + 1 : ℕ) * A * E ^ r := by
    simp only [T]
    by_cases hr : r = r + 1
    · omega
    rw [sum_insert (by simpa [eq_comm] using hr), sum_singleton]
    rw [show r + 1 - r = 1 by omega,
      show r + 1 - (r + 1) = 0 by omega,
      pow_zero, pow_one, mul_one, Nat.choose_self, Nat.cast_one,
      Nat.choose_succ_self_right]
    ring
  rw [hsumT] at hle
  exact hle

/-- The standard factorial bound for an elementary symmetric sum. -/
theorem factorial_mul_brunElementary_le_sum_pow
    {α : Type*} [DecidableEq α]
    (S : Finset α) (x : α → ℝ) (hx : ∀ p ∈ S, 0 ≤ x p) (r : ℕ) :
    (r.factorial : ℝ) * brunElementary S x r ≤
      (∑ p ∈ S, x p) ^ r := by
  induction S using Finset.induction_on generalizing r with
  | empty =>
      cases r with
      | zero => simp [brunElementary]
      | succ r =>
          have he : (∅ : Finset α).powersetCard (r + 1) = ∅ := by
            ext D
            simp only [mem_powersetCard, Finset.notMem_empty, iff_false]
            rintro ⟨hD, hcard⟩
            have hDe : D = ∅ := Finset.subset_empty.mp hD
            subst D
            simp at hcard
          simp [brunElementary, he]
  | @insert a S ha ih =>
      have hA : 0 ≤ x a := hx a (mem_insert_self a S)
      have hxS : ∀ p ∈ S, 0 ≤ x p :=
        fun p hp => hx p (mem_insert_of_mem hp)
      cases r with
      | zero => simp [brunElementary]
      | succ r =>
          rw [brunElementary_insert_succ S a ha x r, sum_insert ha]
          have ihs := ih hxS (r + 1)
          have ihr := ih hxS r
          have hE : 0 ≤ ∑ p ∈ S, x p := sum_nonneg hxS
          have hmul : ((r + 1).factorial : ℝ) *
              (x a * brunElementary S x r) ≤
              ((r : ℝ) + 1) * x a * (∑ p ∈ S, x p) ^ r := by
            rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
            calc
              ((r : ℝ) + 1) * (r.factorial : ℝ) *
                    (x a * brunElementary S x r) =
                  ((r : ℝ) + 1) * x a *
                    ((r.factorial : ℝ) * brunElementary S x r) := by ring
              _ ≤ ((r : ℝ) + 1) * x a * (∑ p ∈ S, x p) ^ r :=
                mul_le_mul_of_nonneg_left ihr
                  (mul_nonneg (by positivity) hA)
              _ = ((r : ℝ) + 1) * x a *
                    (∑ p ∈ S, x p) ^ r := by ring
          calc
            ((r + 1).factorial : ℝ) *
                (brunElementary S x (r + 1) +
                  x a * brunElementary S x r) =
                ((r + 1).factorial : ℝ) *
                    brunElementary S x (r + 1) +
                  ((r + 1).factorial : ℝ) *
                    (x a * brunElementary S x r) := by ring
            _ ≤ (∑ p ∈ S, x p) ^ (r + 1) +
                  (r + 1 : ℕ) * x a * (∑ p ∈ S, x p) ^ r := by
              simpa only [Nat.cast_add, Nat.cast_one] using
                add_le_add ihs hmul
            _ ≤ ((∑ p ∈ S, x p) + x a) ^ (r + 1) :=
              pow_add_linear_le (x a) (∑ p ∈ S, x p) hA hE r
            _ = (x a + ∑ p ∈ S, x p) ^ (r + 1) := by rw [add_comm]

/-- Divided form of the elementary-symmetric factorial bound. -/
theorem brunElementary_le_sum_pow_div_factorial
    {α : Type*} [DecidableEq α]
    (S : Finset α) (x : α → ℝ) (hx : ∀ p ∈ S, 0 ≤ x p) (r : ℕ) :
    brunElementary S x r ≤
      (∑ p ∈ S, x p) ^ r / (r.factorial : ℝ) := by
  rw [le_div_iff₀ (by exact_mod_cast Nat.factorial_pos r)]
  simpa [mul_comm] using
    factorial_mul_brunElementary_le_sum_pow S x hx r

/-- The weighted inclusion--exclusion sum truncated at degree `m`. -/
def brunTrunc {α : Type*} [DecidableEq α]
    (S : Finset α) (x : α → ℝ) (m : ℕ) : ℝ :=
  ∑ D ∈ S.powerset.filter (fun D => D.card ≤ m),
    (-1 : ℝ) ^ D.card * ∏ p ∈ D, x p

/-- Degree-zero truncation. -/
theorem brunTrunc_zero {α : Type*} [DecidableEq α]
    (S : Finset α) (x : α → ℝ) : brunTrunc S x 0 = 1 := by
  unfold brunTrunc
  have he : S.powerset.filter (fun D => D.card ≤ 0) = {∅} := by
    ext D
    simp only [mem_filter, mem_powerset, nonpos_iff_eq_zero,
      mem_singleton]
    constructor
    · exact fun h => card_eq_zero.mp h.2
    · rintro rfl
      simp
  rw [he]
  simp

/-- Inserting one variable gives the usual truncation recurrence. -/
theorem brunTrunc_insert_succ {α : Type*} [DecidableEq α]
    (S : Finset α) (a : α) (ha : a ∉ S) (x : α → ℝ) (m : ℕ) :
    brunTrunc (insert a S) x (m + 1) =
      brunTrunc S x (m + 1) - x a * brunTrunc S x m := by
  unfold brunTrunc
  have hsets : (insert a S).powerset.filter
      (fun D => D.card ≤ m + 1) =
      S.powerset.filter (fun D => D.card ≤ m + 1) ∪
        (S.powerset.filter (fun D => D.card ≤ m)).image (insert a) := by
    ext D
    simp only [mem_filter, mem_powerset, mem_union, mem_image]
    constructor
    · rintro ⟨hsub, hcard⟩
      by_cases haD : a ∈ D
      · right
        refine ⟨D.erase a, ?_, ?_⟩
        · constructor
          · exact fun p hp => by
              have hpD := (mem_erase.mp hp).2
              rcases mem_insert.mp (hsub hpD) with hpa | hpS
              · exact ((mem_erase.mp hp).1 hpa).elim
              · exact hpS
          · rw [card_erase_of_mem haD]
            omega
        · exact insert_erase haD
      · left
        refine ⟨?_, hcard⟩
        intro p hp
        rcases mem_insert.mp (hsub hp) with hpa | hpS
        · subst p
          exact (haD hp).elim
        · exact hpS
    · rintro (hleft | hright)
      · exact ⟨fun p hp => mem_insert_of_mem (hleft.1 hp), hleft.2⟩
      · obtain ⟨E, hE, hEq⟩ := hright
        rw [← hEq]
        constructor
        · intro p hp
          rcases mem_insert.mp hp with hpa | hp
          · rw [hpa]
            exact mem_insert_self a S
          · exact mem_insert_of_mem (hE.1 hp)
        · rw [card_insert_of_notMem (fun haE => ha (hE.1 haE))]
          omega
  rw [hsets]
  have hdisj : Disjoint (S.powerset.filter (fun D => D.card ≤ m + 1))
      ((S.powerset.filter (fun D => D.card ≤ m)).image (insert a)) := by
    rw [Finset.disjoint_left]
    intro D hD hDi
    obtain ⟨E, hE, rfl⟩ := mem_image.mp hDi
    exact ha ((mem_powerset.mp (mem_filter.mp hD).1)
      (mem_insert_self a E))
  rw [sum_union hdisj, sum_image]
  · rw [mul_sum]
    congr 1
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro D hD
    have haD : a ∉ D :=
      fun haD => ha ((mem_powerset.mp (mem_filter.mp hD).1) haD)
    rw [card_insert_of_notMem haD, prod_insert haD, pow_succ]
    ring
  · intro D hD E hE hDE
    have haD : a ∉ D :=
      fun haD => ha ((mem_powerset.mp (mem_filter.mp hD).1) haD)
    have haE : a ∉ E :=
      fun haE => ha ((mem_powerset.mp (mem_filter.mp hE).1) haE)
    have he := congrArg (fun T : Finset α => T.erase a) hDE
    simpa [haD, haE] using he

@[simp] theorem brunTrunc_empty {α : Type*} [DecidableEq α]
    (x : α → ℝ) (m : ℕ) : brunTrunc ∅ x m = 1 := by
  unfold brunTrunc
  have he : (∅ : Finset α).powerset.filter
      (fun D => D.card ≤ m) = {∅} := by
    ext D
    simp only [mem_filter, mem_powerset, Finset.subset_empty,
      mem_singleton]
    constructor
    · exact fun h => h.1
    · rintro rfl
      simp
  rw [he]
  simp

/-- Weighted Bonferroni inequalities for variables in `[0,1]`. -/
theorem brunTrunc_bonferroni {α : Type*} [DecidableEq α]
    (S : Finset α) (x : α → ℝ)
    (hx0 : ∀ p ∈ S, 0 ≤ x p) (hx1 : ∀ p ∈ S, x p ≤ 1) :
    (∀ k, brunTrunc S x (2 * k + 1) ≤ ∏ p ∈ S, (1 - x p)) ∧
      (∀ k, (∏ p ∈ S, (1 - x p)) ≤ brunTrunc S x (2 * k)) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      have hA0 : 0 ≤ x a := hx0 a (mem_insert_self a S)
      have hA1 : x a ≤ 1 := hx1 a (mem_insert_self a S)
      have hx0S : ∀ p ∈ S, 0 ≤ x p :=
        fun p hp => hx0 p (mem_insert_of_mem hp)
      have hx1S : ∀ p ∈ S, x p ≤ 1 :=
        fun p hp => hx1 p (mem_insert_of_mem hp)
      obtain ⟨ihodd, iheven⟩ := ih hx0S hx1S
      have hprod0 : 0 ≤ ∏ p ∈ S, (1 - x p) :=
        prod_nonneg fun p hp => sub_nonneg.mpr (hx1S p hp)
      constructor
      · intro k
        rw [brunTrunc_insert_succ S a ha x (2 * k), prod_insert ha]
        have ho := ihodd k
        have he := iheven k
        nlinarith
      · intro k
        cases k with
        | zero =>
            rw [Nat.mul_zero, brunTrunc_zero (insert a S) x, prod_insert ha]
            have he := iheven 0
            have hp1 : (∏ p ∈ S, (1 - x p)) ≤ 1 := by
              simpa only [Nat.mul_zero, brunTrunc_zero S x] using he
            calc
              (1 - x a) * ∏ p ∈ S, (1 - x p) ≤ 1 * 1 :=
                mul_le_mul (by linarith) hp1 hprod0 zero_le_one
              _ = 1 := by ring
        | succ k =>
            rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
              brunTrunc_insert_succ S a ha x (2 * k + 1), prod_insert ha]
            have he := iheven (k + 1)
            have ho := ihodd k
            rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega] at he
            have hd1 : 0 ≤ brunTrunc S x (2 * k + 1 + 1) -
                ∏ p ∈ S, (1 - x p) := by linarith
            have hd2 : 0 ≤ (∏ p ∈ S, (1 - x p)) -
                brunTrunc S x (2 * k + 1) := by linarith
            have hmul := mul_nonneg hA0 hd2
            nlinarith

/-- Adding one more degree to a truncation adds the corresponding
elementary symmetric sum. -/
theorem brunTrunc_succ_eq {α : Type*} [DecidableEq α]
    (S : Finset α) (x : α → ℝ) (m : ℕ) :
    brunTrunc S x (m + 1) = brunTrunc S x m +
      (-1 : ℝ) ^ (m + 1) * brunElementary S x (m + 1) := by
  unfold brunTrunc brunElementary
  have hsets : S.powerset.filter (fun D => D.card ≤ m + 1) =
      S.powerset.filter (fun D => D.card ≤ m) ∪
        S.powersetCard (m + 1) := by
    ext D
    simp only [mem_filter, mem_powerset, mem_union, mem_powersetCard]
    by_cases hsub : D ⊆ S <;> simp [hsub]
    omega
  rw [hsets]
  have hdisj : Disjoint (S.powerset.filter (fun D => D.card ≤ m))
      (S.powersetCard (m + 1)) := by
    rw [Finset.disjoint_left]
    intro D hD hDc
    have hle := (mem_filter.mp hD).2
    have heq := (mem_powersetCard.mp hDc).2
    omega
  rw [sum_union hdisj, mul_sum]
  congr 1
  apply sum_congr rfl
  intro D hD
  rw [(mem_powersetCard.mp hD).2]

/-- The even truncation is at most the full Euler product plus the first
omitted elementary symmetric sum. -/
theorem brunTrunc_even_le_prod_add_elementary
    {α : Type*} [DecidableEq α]
    (S : Finset α) (x : α → ℝ)
    (hx0 : ∀ p ∈ S, 0 ≤ x p) (hx1 : ∀ p ∈ S, x p ≤ 1) (k : ℕ) :
    brunTrunc S x (2 * k) ≤
      (∏ p ∈ S, (1 - x p)) + brunElementary S x (2 * k + 1) := by
  have hodd := (brunTrunc_bonferroni S x hx0 hx1).1 k
  have hsplit : brunTrunc S x (2 * k + 1) =
      brunTrunc S x (2 * k) - brunElementary S x (2 * k + 1) := by
    rw [brunTrunc_succ_eq S x (2 * k)]
    rw [show (-1 : ℝ) ^ (2 * k + 1) = -1 by
      rw [pow_succ, pow_mul]
      norm_num]
    ring
  linarith

/-- Cardinality of a truncated powerset as a binomial sum. -/
theorem card_powerset_filter_le_eq_sum_choose
    {α : Type*} [DecidableEq α] (S : Finset α) (M : ℕ) :
    (S.powerset.filter (fun D => D.card ≤ M)).card =
      ∑ j ∈ range (M + 1), S.card.choose j := by
  rw [card_eq_sum_ones, sum_filter]
  change (∑ D ∈ S.powerset,
      (fun n => if n ≤ M then 1 else 0) D.card) = _
  calc
    _ = ∑ j ∈ range (S.card + 1), S.card.choose j •
          (if j ≤ M then 1 else 0) :=
      Finset.sum_powerset_apply_card (fun n => if n ≤ M then 1 else 0)
    _ = _ := by
      simp only [nsmul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [← sum_filter]
      by_cases h : S.card ≤ M
      · rw [filter_eq_self.2]
        · exact sum_subset (range_mono (Nat.succ_le_succ h))
            (fun j _ hj => by
              rw [Nat.choose_eq_zero_of_lt (by simpa using hj)]
              simp)
        · intro j hj
          rw [mem_range] at hj
          omega
      · rw [show (range (S.card + 1)).filter (fun j => j ≤ M) =
            range (M + 1) by
          ext j
          simp only [mem_filter, mem_range]
          omega]
        apply sum_congr rfl
        intro j hj
        simp

/-- The number of subsets of size at most `r` is bounded by the number of
length-`r` words over the set with one padding symbol. -/
theorem card_powerset_filter_le_pow (S : Finset ℕ) (r : ℕ) :
    (S.powerset.filter (fun D => D.card ≤ r)).card ≤
      (S.card + 1) ^ r := by
  rw [card_powerset_filter_le_eq_sum_choose]
  calc
    ∑ j ∈ range (r + 1), S.card.choose j ≤
        ∑ j ∈ range (r + 1), S.card ^ j := by
          exact sum_le_sum fun j hj => Nat.choose_le_pow _ _
    _ ≤ ∑ j ∈ range (r + 1), S.card ^ j * r.choose j := by
          apply sum_le_sum
          intro j hj
          exact Nat.le_mul_of_pos_right _
            (Nat.choose_pos (by simpa using hj))
    _ = (S.card + 1) ^ r := by
          rw [add_pow]
          apply sum_congr rfl
          intro j hj
          simp

/-- A product of reciprocal natural numbers is the reciprocal of the
product. -/
theorem prod_one_div_eq_one_div_prod (D : Finset ℕ) :
    (∏ p ∈ D, (1 : ℝ) / p) = 1 / ((∏ p ∈ D, p : ℕ) : ℝ) := by
  simp only [one_div]
  calc
    (∏ p ∈ D, ((p : ℝ))⁻¹) = (∏ p ∈ D, (p : ℝ))⁻¹ := by
      rw [Finset.prod_inv_distrib]
    _ = ((∏ p ∈ D, p : ℕ) : ℝ)⁻¹ := by rw [Nat.cast_prod]

/-- A signed multiple count is bounded by its signed main term plus one. -/
theorem signed_card_multiples_Ioc_le (a b d r : ℕ) (hd : 1 ≤ d) :
    (-1 : ℝ) ^ r * (((Ioc a b).filter (d ∣ ·)).card : ℝ) ≤
      (-1 : ℝ) ^ r * ((b - a : ℕ) / (d : ℝ)) + 1 := by
  have herr := card_multiples_Ioc_error a b d hd
  have hsign : |(-1 : ℝ) ^ r| = 1 := by simp
  have hmul : (-1 : ℝ) ^ r *
      ((((Ioc a b).filter (d ∣ ·)).card : ℝ) -
        (b - a : ℕ) / (d : ℝ)) ≤ 1 := by
    calc
      (-1 : ℝ) ^ r *
          ((((Ioc a b).filter (d ∣ ·)).card : ℝ) -
            (b - a : ℕ) / (d : ℝ)) ≤
          |(-1 : ℝ) ^ r *
            ((((Ioc a b).filter (d ∣ ·)).card : ℝ) -
              (b - a : ℕ) / (d : ℝ))| := le_abs_self _
      _ = |(((Ioc a b).filter (d ∣ ·)).card : ℝ) -
              (b - a : ℕ) / (d : ℝ)| := by
            rw [abs_mul, hsign, one_mul]
      _ ≤ 1 := herr
  linarith

/-- Real-valued form of the pointwise Bonferroni indicator bound. -/
theorem indicator_coprime_le_truncated_inclexcl_real
    (P : Finset ℕ) (m k : ℕ) :
    (if omegaFinset P m = 0 then 1 else 0 : ℝ) ≤
      ∑ D ∈ P.powerset.filter (fun D => D.card ≤ 2 * k),
        (-1 : ℝ) ^ D.card *
          (if ∀ p ∈ D, p ∣ m then 1 else 0) := by
  exact_mod_cast indicator_coprime_le_truncated_inclexcl P m k

/-- Summing the pointwise indicator and swapping the finite sums gives the
truncated inclusion--exclusion count. -/
theorem card_no_factor_le_truncated_count
    (a b : ℕ) (P : Finset ℕ) (k : ℕ) :
    (((Ioc a b).filter (fun m => ∀ p ∈ P, ¬ p ∣ m)).card : ℝ) ≤
      ∑ D ∈ P.powerset.filter (fun D => D.card ≤ 2 * k),
        (-1 : ℝ) ^ D.card *
          (((Ioc a b).filter (fun m => ∀ p ∈ D, p ∣ m)).card : ℝ) := by
  classical
  calc
    (((Ioc a b).filter (fun m => ∀ p ∈ P, ¬ p ∣ m)).card : ℝ) =
        ∑ m ∈ Ioc a b,
          (if omegaFinset P m = 0 then 1 else 0 : ℝ) := by
          rw [card_eq_sum_ones]
          push_cast
          rw [sum_filter]
          apply sum_congr rfl
          intro m hm
          unfold omegaFinset
          by_cases hfree : ∀ p ∈ P, ¬ p ∣ m
          · have hz : (P.filter (· ∣ m)).card = 0 := by
              rw [card_eq_zero]
              ext p
              simp only [mem_filter, Finset.notMem_empty, iff_false,
                not_and]
              exact fun hpP => hfree p hpP
            rw [if_pos hfree, if_pos hz]
          · have hz : (P.filter (· ∣ m)).card ≠ 0 := by
              intro hz
              rw [card_eq_zero] at hz
              push_neg at hfree
              obtain ⟨p, hpP, hpdiv⟩ := hfree
              have hp : p ∈ P.filter (· ∣ m) :=
                mem_filter.mpr ⟨hpP, hpdiv⟩
              rw [hz] at hp
              simp at hp
            rw [if_neg hfree, if_neg hz]
    _ ≤ ∑ m ∈ Ioc a b,
        ∑ D ∈ P.powerset.filter (fun D => D.card ≤ 2 * k),
          (-1 : ℝ) ^ D.card *
            (if ∀ p ∈ D, p ∣ m then 1 else 0) := by
          exact sum_le_sum fun m hm =>
            indicator_coprime_le_truncated_inclexcl_real P m k
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro D hD
      rw [← mul_sum]
      congr 1
      rw [← sum_filter]
      simp

/-- Each retained subset contributes its signed density main term and at
most one endpoint error. -/
theorem truncated_count_le_main_error (a b : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (k : ℕ) :
    (∑ D ∈ P.powerset.filter (fun D => D.card ≤ 2 * k),
        (-1 : ℝ) ^ D.card *
          (((Ioc a b).filter (fun m => ∀ p ∈ D, p ∣ m)).card : ℝ)) ≤
      ((b - a : ℕ) : ℝ) *
          brunTrunc P (fun p => (1 : ℝ) / p) (2 * k) +
        ((P.powerset.filter (fun D => D.card ≤ 2 * k)).card : ℝ) := by
  classical
  calc
    (∑ D ∈ P.powerset.filter (fun D => D.card ≤ 2 * k),
        (-1 : ℝ) ^ D.card *
          (((Ioc a b).filter (fun m => ∀ p ∈ D, p ∣ m)).card : ℝ)) ≤
        ∑ D ∈ P.powerset.filter (fun D => D.card ≤ 2 * k),
          (((b - a : ℕ) : ℝ) *
            ((-1 : ℝ) ^ D.card * ∏ p ∈ D, (1 : ℝ) / p) + 1) := by
          apply sum_le_sum
          intro D hD
          have hDP : D ⊆ P := mem_powerset.mp (mem_filter.mp hD).1
          have hprime : ∀ p ∈ D, p.Prime :=
            fun p hp => hP p (hDP hp)
          have hd : 1 ≤ ∏ p ∈ D, p := by
            exact prod_pos fun p hp => (hprime p hp).pos
          have hfilter :
              (Ioc a b).filter (fun m => ∀ p ∈ D, p ∣ m) =
                (Ioc a b).filter ((∏ p ∈ D, p) ∣ ·) := by
            ext m
            simp only [mem_filter, and_congr_right_iff]
            intro hm
            exact (prod_dvd_iff_all_dvd_of_primes D hprime m).symm
          rw [hfilter]
          have hs := signed_card_multiples_Ioc_le
            a b (∏ p ∈ D, p) D.card hd
          rw [prod_one_div_eq_one_div_prod D]
          calc
            (-1 : ℝ) ^ D.card *
                (((Ioc a b).filter ((∏ p ∈ D, p) ∣ ·)).card : ℝ) ≤
                (-1 : ℝ) ^ D.card *
                    ((b - a : ℕ) / (((∏ p ∈ D, p : ℕ) : ℝ))) + 1 := hs
            _ = ((b - a : ℕ) : ℝ) *
                  ((-1 : ℝ) ^ D.card *
                    (1 / ((∏ p ∈ D, p : ℕ) : ℝ))) + 1 := by ring
    _ = ((b - a : ℕ) : ℝ) *
          brunTrunc P (fun p => (1 : ℝ) / p) (2 * k) +
        ((P.powerset.filter (fun D => D.card ≤ 2 * k)).card : ℝ) := by
          unfold brunTrunc
          rw [sum_add_distrib, mul_sum, sum_const, nsmul_eq_mul]
          ring

/-- Brun's pure upper-bound sieve on `(a,b]`. -/
theorem card_no_factor_Ioc_le_brun (a b : ℕ) (hab : a ≤ b)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (k : ℕ) :
    (((Ioc a b).filter (fun m => ∀ p ∈ P, ¬ p ∣ m)).card : ℝ) ≤
      ((b : ℝ) - a) *
        ((∏ p ∈ P, (1 - 1 / (p : ℝ))) +
          (∑ p ∈ P, (1 : ℝ) / p) ^ (2 * k + 1) /
            ((2 * k + 1).factorial : ℝ)) +
        ((P.card : ℝ) + 1) ^ (2 * k) := by
  let x : ℕ → ℝ := fun p => (1 : ℝ) / p
  have hx0 : ∀ p ∈ P, 0 ≤ x p := fun p hp => by positivity
  have hx1 : ∀ p ∈ P, x p ≤ 1 := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by
      exact_mod_cast (hP p hp).one_lt.le
    rw [div_le_one (by positivity)]
    exact hp1
  have htrunc := brunTrunc_even_le_prod_add_elementary P x hx0 hx1 k
  have helem := brunElementary_le_sum_pow_div_factorial
    P x hx0 (2 * k + 1)
  have hcard :
      ((P.powerset.filter (fun D => D.card ≤ 2 * k)).card : ℝ) ≤
        ((P.card : ℝ) + 1) ^ (2 * k) := by
    exact_mod_cast card_powerset_filter_le_pow P (2 * k)
  have hdelta : (0 : ℝ) ≤ (b : ℝ) - a := by
    have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hcast : (((b - a : ℕ) : ℝ)) = (b : ℝ) - a := by
    rw [Nat.cast_sub hab]
  calc
    (((Ioc a b).filter (fun m => ∀ p ∈ P, ¬ p ∣ m)).card : ℝ) ≤
        ∑ D ∈ P.powerset.filter (fun D => D.card ≤ 2 * k),
          (-1 : ℝ) ^ D.card *
            (((Ioc a b).filter (fun m => ∀ p ∈ D, p ∣ m)).card : ℝ) :=
      card_no_factor_le_truncated_count a b P k
    _ ≤ (((b - a : ℕ) : ℝ)) * brunTrunc P x (2 * k) +
          ((P.powerset.filter (fun D => D.card ≤ 2 * k)).card : ℝ) :=
      truncated_count_le_main_error a b P hP k
    _ ≤ ((b : ℝ) - a) *
          ((∏ p ∈ P, (1 - x p)) +
            brunElementary P x (2 * k + 1)) +
          ((P.card : ℝ) + 1) ^ (2 * k) := by
      rw [hcast]
      exact add_le_add (mul_le_mul_of_nonneg_left htrunc hdelta) hcard
    _ ≤ ((b : ℝ) - a) *
          ((∏ p ∈ P, (1 - x p)) +
            (∑ p ∈ P, x p) ^ (2 * k + 1) /
              ((2 * k + 1).factorial : ℝ)) +
          ((P.card : ℝ) + 1) ^ (2 * k) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl helem) hdelta) le_rfl
    _ = _ := by rfl

/-! ## Harmonic mass and Mertens consequences -/

/-- The harmonic mass of the sifted set is at most `1/a` times the
cardinality bound. -/
theorem sum_one_div_no_factor_Ioc_le_brun
    (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (k : ℕ) :
    (∑ m ∈ (Ioc a b).filter (fun m => ∀ p ∈ P, ¬ p ∣ m),
        (1 : ℝ) / m) ≤
      (1 / (a : ℝ)) *
        (((b : ℝ) - a) *
          ((∏ p ∈ P, (1 - 1 / (p : ℝ))) +
            (∑ p ∈ P, (1 : ℝ) / p) ^ (2 * k + 1) /
              ((2 * k + 1).factorial : ℝ)) +
          ((P.card : ℝ) + 1) ^ (2 * k)) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hcard := card_no_factor_Ioc_le_brun a b hab P hP k
  calc
    (∑ m ∈ (Ioc a b).filter (fun m => ∀ p ∈ P, ¬ p ∣ m),
        (1 : ℝ) / m) ≤
        ∑ _m ∈ (Ioc a b).filter (fun m => ∀ p ∈ P, ¬ p ∣ m),
          (1 : ℝ) / a := by
            apply sum_le_sum
            intro m hm
            have ham : (a : ℝ) ≤ m := by
              exact_mod_cast (mem_Ioc.mp (mem_filter.mp hm).1).1.le
            exact one_div_le_one_div_of_le ha0 ham
    _ = (1 / (a : ℝ)) *
          (((Ioc a b).filter (fun m => ∀ p ∈ P, ¬ p ∣ m)).card : ℝ) := by
            rw [sum_const, nsmul_eq_mul]
            ring
    _ ≤ (1 / (a : ℝ)) *
        (((b : ℝ) - a) *
          ((∏ p ∈ P, (1 - 1 / (p : ℝ))) +
            (∑ p ∈ P, (1 : ℝ) / p) ^ (2 * k + 1) /
              ((2 * k + 1).factorial : ℝ)) +
          ((P.card : ℝ) + 1) ^ (2 * k)) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)

/-- Euler's factors are bounded by exponentials of their linear terms. -/
theorem prod_one_sub_inv_le_exp_neg_sum (P : Finset ℕ) :
    (∏ p ∈ P, (1 - 1 / (p : ℝ))) ≤
      Real.exp (-(∑ p ∈ P, (1 : ℝ) / p)) := by
  have hfac0 : ∀ p ∈ P, (0 : ℝ) ≤ 1 - 1 / p := by
    intro p hp
    rcases p with _ | p
    · norm_num
    · have hp1 : (1 : ℝ) ≤ (p + 1 : ℕ) := by exact_mod_cast Nat.succ_pos p
      rw [sub_nonneg, div_le_one (by positivity)]
      exact hp1
  calc
    (∏ p ∈ P, (1 - 1 / (p : ℝ))) ≤
        ∏ p ∈ P, Real.exp (-(1 / (p : ℝ))) := by
          exact prod_le_prod hfac0 fun p hp => Real.one_sub_le_exp_neg _
    _ = Real.exp (∑ p ∈ P, -(1 / (p : ℝ))) := by
          rw [← Real.exp_sum]
    _ = Real.exp (-(∑ p ∈ P, (1 : ℝ) / p)) := by
          rw [sum_neg_distrib]

/-- A lower bound `E` for the reciprocal prime mass gives density
`exp (-E)`. -/
theorem prod_one_sub_inv_le_exp_neg_of_mass
    (P : Finset ℕ) (E : ℝ)
    (hE : E ≤ ∑ p ∈ P, (1 : ℝ) / p) :
    (∏ p ∈ P, (1 - 1 / (p : ℝ))) ≤ Real.exp (-E) := by
  exact (prod_one_sub_inv_le_exp_neg_sum P).trans
    (Real.exp_le_exp.mpr (neg_le_neg hE))

/-- A Mertens lower bound in logarithmic-ratio form gives the ladder
density in ratio form. -/
theorem prod_one_sub_inv_le_exp_const_mul_log_ratio
    (P : Finset ℕ) (lo hi : ℝ) (c : ℝ)
    (hlo : 1 < lo) (hhi : 1 < hi)
    (hE : Real.log (Real.log hi) - Real.log (Real.log lo) - c ≤
      ∑ p ∈ P, (1 : ℝ) / p) :
    (∏ p ∈ P, (1 - 1 / (p : ℝ))) ≤
      Real.exp c * Real.log lo / Real.log hi := by
  have hloglo : 0 < Real.log lo := Real.log_pos hlo
  have hloghi : 0 < Real.log hi := Real.log_pos hhi
  calc
    (∏ p ∈ P, (1 - 1 / (p : ℝ))) ≤
        Real.exp (-(Real.log (Real.log hi) -
          Real.log (Real.log lo) - c)) :=
      prod_one_sub_inv_le_exp_neg_of_mass P _ hE
    _ = Real.exp c * Real.log lo / Real.log hi := by
      rw [show -(Real.log (Real.log hi) - Real.log (Real.log lo) - c) =
          c + Real.log (Real.log lo) - Real.log (Real.log hi) by ring,
        Real.exp_sub, Real.exp_add, Real.exp_log hloglo,
        Real.exp_log hloghi]

/-- The in-tree Mertens floor and sharp upper envelope give the reciprocal
mass of the prime interval `(lo,hi]` with constant `12`. -/
theorem prime_Ioc_mass_lower_mertens (lo hi : ℕ)
    (hlo : 3 ≤ lo) (hlohi : lo ≤ hi) :
    Real.log (Real.log ((hi : ℝ) + 1)) -
        Real.log (Real.log ((lo : ℝ) + 1)) - 12 ≤
      ∑ p ∈ (Ioc lo hi).filter Nat.Prime, (1 : ℝ) / p := by
  have hsub : (lo + 1).primesBelow ⊆ (hi + 1).primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hdiff :
      ∑ p ∈ (Ioc lo hi).filter Nat.Prime, (1 : ℝ) / p =
        (∑ p ∈ (hi + 1).primesBelow, (1 : ℝ) / p) -
          ∑ p ∈ (lo + 1).primesBelow, (1 : ℝ) / p := by
    rw [← sum_sdiff_eq_sub hsub]
    apply sum_congr
    · ext p
      simp only [mem_filter, mem_Ioc, mem_sdiff, Nat.mem_primesBelow]
      constructor
      · rintro ⟨⟨hlop, hphi⟩, hpprime⟩
        exact ⟨⟨by omega, hpprime⟩, fun hp => by omega⟩
      · rintro ⟨⟨hphi, hpprime⟩, hnlo⟩
        exact ⟨⟨by
          by_contra h
          apply hnlo
          exact ⟨by omega, hpprime⟩, by omega⟩, hpprime⟩
    · intro p hp
      rfl
  have hlow := log_log_le_sum_one_div_primesBelow (y := hi + 1)
    (by omega : 2 ≤ hi + 1)
  have hupp := sum_one_div_primesBelow_le_sharp (lo + 1) (by omega)
  have hcastlo : ((lo + 1 : ℕ) : ℝ) = (lo : ℝ) + 1 := by
    push_cast
    ring
  have hcasthi : ((hi + 1 : ℕ) : ℝ) = (hi : ℝ) + 1 := by
    push_cast
    ring
  rw [hcastlo] at hupp
  rw [hcasthi] at hlow
  rw [hdiff]
  linarith

/-- Concrete Mertens consequence for the Euler product over primes in
`(lo,hi]`. -/
theorem prime_Ioc_prod_one_sub_inv_le_mertens (lo hi : ℕ)
    (hlo : 3 ≤ lo) (hlohi : lo ≤ hi) :
    (∏ p ∈ (Ioc lo hi).filter Nat.Prime,
        (1 - 1 / (p : ℝ))) ≤
      Real.exp 12 * Real.log ((lo : ℝ) + 1) /
        Real.log ((hi : ℝ) + 1) := by
  apply prod_one_sub_inv_le_exp_const_mul_log_ratio
  · exact_mod_cast (by omega : 1 < lo + 1)
  · exact_mod_cast (by omega : 1 < hi + 1)
  · exact prime_Ioc_mass_lower_mertens lo hi hlo hlohi

/-!
For a ladder level, take `E` to be its reciprocal prime mass and
`k = ⌈exp(1) E⌉₊`.  Stirling's lower bound makes the Bonferroni tail at
most `2⁻^(2k+1)`, while the Euler product is at most `exp (-E)`.
Consequently the only non-density term below is
`2 * (#P + 1)^(2k) / a`.  In the ladder regime `#P ≤ Q`,
`Q ≤ exp (sqrt (log a))`, and `k ≤ 3E`, its logarithm is
`O(E * sqrt (log a)) - log a`; hence it is at most `a⁻¹/²` once `a`
exceeds a threshold depending on `E`.
-/

/-- Brun's dyadic density bound with the canonical truncation depth.

Here `E` is the actual reciprocal mass of `P`; a separate lower Mertens
bound may then replace `exp (-E)` by the desired logarithmic ratio. -/
theorem no_factor_density_le_of_ratio (a : ℕ) (ha : 1 ≤ a)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (E : ℝ) (hE : 0 ≤ E)
    (hmass : E = ∑ p ∈ P, (1 : ℝ) / p) :
    let k := ⌈Real.exp 1 * E⌉₊
    (∑ m ∈ (Ioc a (2 * a)).filter (fun m => ∀ p ∈ P, ¬ p ∣ m),
        (1 : ℝ) / m) ≤
      2 * (Real.exp (-E) +
          (2 : ℝ) ^ (-(↑(2 * k + 1) : ℤ))) *
          (∑ m ∈ Ioc a (2 * a), (1 : ℝ) / m) +
        2 * ((P.card : ℝ) + 1) ^ (2 * k) / a := by
  let k := ⌈Real.exp 1 * E⌉₊
  let H := ∑ m ∈ Ioc a (2 * a), (1 : ℝ) / m
  let err := ((P.card : ℝ) + 1) ^ (2 * k)
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have htail : E ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) ≤
      (2 : ℝ) ^ (-(↑(2 * k + 1) : ℤ)) := by
    let n := 2 * k + 1
    have hn : n ≠ 0 := by simp [n]
    have hceil : Real.exp 1 * E ≤ (k : ℝ) := by
      exact Nat.le_ceil _
    have hexp : 0 < Real.exp 1 := Real.exp_pos 1
    have hEn : E ≤ (n : ℝ) / Real.exp 1 / 2 := by
      have hk : (k : ℝ) ≤ (n : ℝ) / 2 := by
        dsimp [n]
        push_cast
        linarith
      calc
        E = (Real.exp 1 * E) / Real.exp 1 := by field_simp
        _ ≤ (k : ℝ) / Real.exp 1 :=
          (div_le_div_iff_of_pos_right hexp).2 hceil
        _ ≤ ((n : ℝ) / 2) / Real.exp 1 :=
          (div_le_div_iff_of_pos_right hexp).2 hk
        _ = (n : ℝ) / Real.exp 1 / 2 := by ring
    have hbase0 : 0 ≤ (n : ℝ) / Real.exp 1 := by positivity
    have hpow : E ^ n ≤ ((n : ℝ) / Real.exp 1 / 2) ^ n :=
      pow_le_pow_left₀ hE hEn n
    have hstir : ((n : ℝ) / Real.exp 1) ^ n ≤
        (n.factorial : ℝ) := by
      have hs := Stirling.le_factorial_stirling n
      have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * n) := by
        rw [Real.one_le_sqrt]
        have hpi : 3 ≤ Real.pi := Real.pi_gt_three.le
        have hn1 : (1 : ℝ) ≤ n := by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
        nlinarith
      calc
        ((n : ℝ) / Real.exp 1) ^ n =
            1 * ((n : ℝ) / Real.exp 1) ^ n := by ring
        _ ≤ Real.sqrt (2 * Real.pi * n) *
            ((n : ℝ) / Real.exp 1) ^ n :=
          mul_le_mul_of_nonneg_right hsqrt (pow_nonneg hbase0 n)
        _ ≤ (n.factorial : ℝ) := hs
    have hfacpos : (0 : ℝ) < n.factorial := by positivity
    calc
      E ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) =
          E ^ n / (n.factorial : ℝ) := by rfl
      _ ≤ (((n : ℝ) / Real.exp 1 / 2) ^ n) /
          (n.factorial : ℝ) :=
        (div_le_div_iff_of_pos_right hfacpos).2 hpow
      _ = (1 / 2 : ℝ) ^ n *
          (((n : ℝ) / Real.exp 1) ^ n / (n.factorial : ℝ)) := by
        rw [div_pow]
        field_simp
        rw [← mul_pow]
        norm_num
      _ ≤ (1 / 2 : ℝ) ^ n * 1 := by
        gcongr
        exact (div_le_one hfacpos).2 hstir
      _ = (2 : ℝ) ^ (-(↑(2 * k + 1) : ℤ)) := by
        rw [mul_one]
        change (1 / 2 : ℝ) ^ n = (2 : ℝ) ^ (-(n : ℤ))
        rw [zpow_neg, zpow_natCast]
        simp [one_div]
  have hhalf : (1 : ℝ) / 2 ≤ H := by
    have hpt : ∀ n ∈ Ioc a (2 * a),
        (1 : ℝ) / ((2 * a : ℕ) : ℝ) ≤ (1 : ℝ) / n := by
      intro n hn
      rw [mem_Ioc] at hn
      have hn0 : (0 : ℝ) < n := by
        exact_mod_cast (by omega : 0 < n)
      exact one_div_le_one_div_of_le hn0 (by exact_mod_cast hn.2)
    have hsum := card_nsmul_le_sum _ _ _ hpt
    rw [Nat.card_Ioc, nsmul_eq_mul] at hsum
    calc
      (1 : ℝ) / 2 = ((2 * a - a : ℕ) : ℝ) *
          (1 / ((2 * a : ℕ) : ℝ)) := by
        have haa : 2 * a - a = a := by omega
        rw [haa]
        push_cast
        field_simp
      _ ≤ H := hsum
  have hs := sum_one_div_no_factor_Ioc_le_brun a (2 * a) ha
    (by omega) P hP k
  have hs' :
      (∑ m ∈ (Ioc a (2 * a)).filter (fun m => ∀ p ∈ P, ¬ p ∣ m),
        (1 : ℝ) / m) ≤
        (∏ p ∈ P, (1 - 1 / (p : ℝ))) +
          (∑ p ∈ P, (1 : ℝ) / p) ^ (2 * k + 1) /
            ((2 * k + 1).factorial : ℝ) + err / a := by
    calc
      _ ≤ (1 / (a : ℝ)) *
        ((((2 * a : ℕ) : ℝ) - a) *
          ((∏ p ∈ P, (1 - 1 / (p : ℝ))) +
            (∑ p ∈ P, (1 : ℝ) / p) ^ (2 * k + 1) /
              ((2 * k + 1).factorial : ℝ)) +
          ((P.card : ℝ) + 1) ^ (2 * k)) := hs
      _ = _ := by
        dsimp [err]
        push_cast
        field_simp
        ring
  have hprod := prod_one_sub_inv_le_exp_neg_of_mass P E hmass.le
  have herr : 0 ≤ err / (a : ℝ) := by positivity
  have hX : 0 ≤ Real.exp (-E) +
      (2 : ℝ) ^ (-(↑(2 * k + 1) : ℤ)) := by positivity
  have hscale :
      Real.exp (-E) + (2 : ℝ) ^ (-(↑(2 * k + 1) : ℤ)) ≤
        2 * (Real.exp (-E) +
          (2 : ℝ) ^ (-(↑(2 * k + 1) : ℤ))) * H := by
    nlinarith [mul_le_mul_of_nonneg_left hhalf
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hX)]
  calc
    _ ≤ (∏ p ∈ P, (1 - 1 / (p : ℝ))) +
          (∑ p ∈ P, (1 : ℝ) / p) ^ (2 * k + 1) /
            ((2 * k + 1).factorial : ℝ) + err / a := hs'
    _ ≤ Real.exp (-E) + (2 : ℝ) ^ (-(↑(2 * k + 1) : ℤ)) +
        err / a := by
      gcongr
      simpa [hmass, k] using htail
    _ ≤ 2 * (Real.exp (-E) +
          (2 : ℝ) ^ (-(↑(2 * k + 1) : ℤ))) * H +
        2 * err / a := by
      have herr2 : err / (a : ℝ) ≤ 2 * err / a := by
        calc
          err / (a : ℝ) ≤ 2 * (err / a) := by linarith
          _ = 2 * err / a := by ring
      linarith

end MoltResearch
