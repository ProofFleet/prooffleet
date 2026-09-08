import MoltResearch.Discrepancy.VinogradovMeanValue
import MoltResearch.Discrepancy.ExpSums
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Weyl sums from Vinogradov's mean value theorem

This leaf develops the Vinogradov shift argument for the logarithmic phase.
The Taylor normalization follows Ford, Lemma 6.3: the short variable has
length `M`, and the coefficient neighbourhood in degree `j` has width
proportional to `M⁻ʲ`.  This is the scale at which the multiplicity of the
top coefficient is `O(M)`.
-/

namespace MoltResearch

open scoped BigOperators

namespace VinogradovWeylSum

/-- The degree-`k` Taylor polynomial for `log (1 + x)`. -/
noncomputable def logPolynomial (k : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 k, (-1 : ℝ) ^ (j + 1) * x ^ j / j

theorem ofReal_logPolynomial_eq_logTaylor (k : ℕ) (x : ℝ) :
    (logPolynomial k x : ℂ) = Complex.logTaylor (k + 1) (x : ℂ) := by
  classical
  induction k with
  | zero => simp [logPolynomial, Complex.logTaylor]
  | succ k ih =>
      rw [logPolynomial, Finset.sum_Icc_succ_top (by omega),
        Complex.ofReal_add, Complex.logTaylor_succ]
      rw [← logPolynomial, ih]
      congr 1
      push_cast
      simp

theorem logPolynomial_eq_logTaylor_re (k : ℕ) (x : ℝ) :
    logPolynomial k x = (Complex.logTaylor (k + 1) (x : ℂ)).re := by
  rw [← ofReal_logPolynomial_eq_logTaylor]
  simp

/-- Taylor's formula for `log (1+x)`, with the geometric tail kept in the
form used by the Vinogradov shift. -/
theorem abs_log_one_add_sub_logPolynomial_le (k : ℕ) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    |Real.log (1 + x) - logPolynomial k x|
      ≤ x ^ (k + 1) * (1 - x)⁻¹ / (k + 1) := by
  have hnorm : ‖(x : ℂ)‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hx0] using hx1
  have h := Complex.norm_log_sub_logTaylor_le k hnorm
  have hreal : Complex.log (1 + (x : ℂ)) - Complex.logTaylor (k + 1) (x : ℂ)
      = ((Real.log (1 + x) - logPolynomial k x : ℝ) : ℂ) := by
    have hpos : (0 : ℝ) < 1 + x := by positivity
    rw [← Complex.ofReal_one, ← Complex.ofReal_add,
      ← Complex.ofReal_log hpos.le, ← ofReal_logPolynomial_eq_logTaylor]
    norm_cast
  rw [hreal, Complex.norm_real, Real.norm_eq_abs] at h
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0] using h

/-- Taylor expansion about a positive base point. -/
theorem abs_log_add_sub_taylor_le (k : ℕ) {y x : ℝ}
    (hy : 0 < y) (hx0 : 0 ≤ x) (hxy : x < y) :
    |Real.log (y + x) - Real.log y - logPolynomial k (x / y)|
      ≤ (x / y) ^ (k + 1) * (1 - x / y)⁻¹ / (k + 1) := by
  have hratio0 : 0 ≤ x / y := div_nonneg hx0 hy.le
  have hratio1 : x / y < 1 := (div_lt_one hy).mpr hxy
  have hlog : Real.log (y + x) - Real.log y = Real.log (1 + x / y) := by
    have hy0 := hy.ne'
    have hsum : y + x = y * (1 + x / y) := by field_simp
    rw [hsum, Real.log_mul hy0 (by positivity), add_sub_cancel_left]
  rw [hlog]
  exact abs_log_one_add_sub_logPolynomial_le k hratio0 hratio1

/-- The normalized logarithmic phase splits into a polynomial phase and a
remainder whose absolute value has the Taylor bound. -/
theorem logPhase_taylor (k : ℕ) {t y x : ℝ}
    (hy : 0 < y) (hx0 : 0 ≤ x) (hxy : x < y) :
    let ρ := Real.log (y + x) - Real.log y - logPolynomial k (x / y)
    (-(t / (2 * Real.pi) * Real.log (y + x)) =
        -(t / (2 * Real.pi) * Real.log y)
          - t / (2 * Real.pi) * logPolynomial k (x / y)
          - t / (2 * Real.pi) * ρ
      ∧ |ρ| ≤ (x / y) ^ (k + 1) * (1 - x / y)⁻¹ / (k + 1)) := by
  dsimp
  constructor
  · ring
  · exact abs_log_add_sub_taylor_le k hy hx0 hxy

/-- A phase perturbation of size `ρ` changes the normalized character by at
most `2π|ρ|`. -/
theorem norm_e_add_sub_e_le (a ρ : ℝ) :
    ‖ExpSums.e (a + ρ) - ExpSums.e a‖ ≤ 2 * Real.pi * |ρ| := by
  rw [ExpSums.e_add]
  have heq : ExpSums.e a * ExpSums.e ρ - ExpSums.e a =
      ExpSums.e a * (ExpSums.e ρ - 1) := by ring
  rw [heq, norm_mul, ExpSums.norm_e, one_mul]
  rw [ExpSums.e]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * ρ)
  calc
    ‖Complex.exp (2 * Real.pi * (ρ : ℂ) * Complex.I) - 1‖ =
        ‖Complex.exp (Complex.I * ((2 * Real.pi * ρ : ℝ) : ℂ)) - 1‖ := by
          congr 2
          push_cast
          ring_nf
    _ ≤ ‖2 * Real.pi * ρ‖ := h
    _ = 2 * Real.pi * |ρ| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]

/-! ## Shift averaging -/

/-- Moving both endpoints of an integer interval gives two signed collars.
This local form keeps the Weyl-sum leaf independent of the band machinery. -/
theorem sum_Ioc_sub_sum_Ioc_eq_collars {E : Type*} [AddCommGroup E]
    (a b a' b' : ℕ) (hab : a ≤ b) (haa' : a ≤ a')
    (ha'b' : a' ≤ b') (hbb' : b ≤ b') (f : ℕ → E) :
    (∑ n ∈ Finset.Ioc a b, f n) - ∑ n ∈ Finset.Ioc a' b', f n =
      (∑ n ∈ Finset.Ioc a a', f n) - ∑ n ∈ Finset.Ioc b b', f n := by
  rcases le_total a' b with ha'b | hba'
  · rw [← Finset.sum_Ioc_consecutive f haa' ha'b,
      ← Finset.sum_Ioc_consecutive f ha'b hbb']
    abel
  · rw [← Finset.sum_Ioc_consecutive f hab hba',
      ← Finset.sum_Ioc_consecutive f hba' ha'b']
    abel

/-- Translation of an `Ioc` sum. -/
theorem sum_Ioc_shift {E : Type*} [AddCommMonoid E] (f : ℕ → E)
    {N R m : ℕ} (hmN : m ≤ N) (hNR : N ≤ R) :
    ∑ q ∈ Finset.Ioc N R, f q =
      ∑ n ∈ Finset.Ioc (N - m) (R - m), f (n + m) := by
  have hmap : Finset.Ioc N R =
      (Finset.Ioc (N - m) (R - m)).map (addRightEmbedding m) := by
    rw [Finset.map_add_right_Ioc]
    congr 1 <;> omega
  rw [hmap, Finset.sum_map]
  simp only [addRightEmbedding_apply]

/-- A shift by `m` differs from the common inner window by at most its two
endpoint collars.  The deliberately round constant `2m` also covers the
degenerate overlap configurations. -/
theorem norm_shift_sub_reference_le {E : Type*} [SeminormedAddCommGroup E]
    (f : ℕ → E) {N R m : ℕ} (hNR : N < R) (hm1 : 1 ≤ m) (hmN : m ≤ N)
    (hf : ∀ q, ‖f q‖ ≤ 1) :
    ‖(∑ q ∈ Finset.Ioc N R, f q) -
        ∑ n ∈ Finset.Ioc N (R - 1), f (n + m)‖ ≤ 2 * (m : ℝ) := by
  rw [sum_Ioc_shift f hmN hNR.le]
  rw [sum_Ioc_sub_sum_Ioc_eq_collars (N - m) (R - m) N (R - 1)
    (by omega) (by omega) (by omega) (by omega)]
  calc
    ‖(∑ n ∈ Finset.Ioc (N - m) N, f (n + m)) -
        ∑ n ∈ Finset.Ioc (R - m) (R - 1), f (n + m)‖
        ≤ ‖∑ n ∈ Finset.Ioc (N - m) N, f (n + m)‖ +
          ‖∑ n ∈ Finset.Ioc (R - m) (R - 1), f (n + m)‖ := norm_sub_le _ _
    _ ≤ (∑ _n ∈ Finset.Ioc (N - m) N, (1 : ℝ)) +
          ∑ _n ∈ Finset.Ioc (R - m) (R - 1), (1 : ℝ) :=
      add_le_add
        (norm_sum_le_of_le _ fun n _ => hf (n + m))
        (norm_sum_le_of_le _ fun n _ => hf (n + m))
    _ = ((m : ℕ) : ℝ) + ((m - 1 : ℕ) : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Ioc]
      norm_cast
      omega
    _ ≤ 2 * (m : ℝ) := by
      norm_cast
      omega

/-- Weyl shift averaging in the common-window form.  This is the exact
finite-sum version of Ford (6.1), with a harmless `2U` collar cost. -/
theorem norm_sum_le_shift_average
    (f : ℕ → ℂ) {N R U : ℕ} (hNR : N < R)
    (hU1 : 1 ≤ U) (hUN : U ≤ N) (hf : ∀ q, ‖f q‖ ≤ 1) :
    ‖∑ q ∈ Finset.Ioc N R, f q‖ ≤
      (1 / (U : ℝ)) *
          ‖∑ n ∈ Finset.Ioc N (R - 1), ∑ m ∈ Finset.Icc 1 U, f (n + m)‖
        + 2 * U := by
  let S : ℂ := ∑ q ∈ Finset.Ioc N R, f q
  let A : ℕ → ℂ := fun m => ∑ n ∈ Finset.Ioc N (R - 1), f (n + m)
  have hcard : (Finset.Icc 1 U).card = U := by simp [Nat.card_Icc]
  have hdiff : ∀ m ∈ Finset.Icc 1 U, ‖S - A m‖ ≤ 2 * (U : ℝ) := by
    intro m hm
    rcases Finset.mem_Icc.mp hm with ⟨hm1, hmU⟩
    exact (norm_shift_sub_reference_le f hNR hm1 (hmU.trans hUN) hf).trans
      (by gcongr)
  have hsumdiff :
      ‖∑ m ∈ Finset.Icc 1 U, (S - A m)‖ ≤ 2 * (U : ℝ) ^ 2 := by
    calc
      ‖∑ m ∈ Finset.Icc 1 U, (S - A m)‖
          ≤ ∑ m ∈ Finset.Icc 1 U, ‖S - A m‖ := norm_sum_le _ _
      _ ≤ ∑ _m ∈ Finset.Icc 1 U, 2 * (U : ℝ) :=
        Finset.sum_le_sum hdiff
      _ = 2 * (U : ℝ) ^ 2 := by rw [Finset.sum_const, hcard]; simp; ring
  have hdecomp :
      (U : ℕ) • S =
        (∑ n ∈ Finset.Ioc N (R - 1), ∑ m ∈ Finset.Icc 1 U, f (n + m)) +
          ∑ m ∈ Finset.Icc 1 U, (S - A m) := by
    rw [← Finset.sum_comm]
    simp only [A, Finset.sum_sub_distrib, Finset.sum_const, hcard]
    abel
  have hmul : (U : ℝ) * ‖S‖ ≤
      ‖∑ n ∈ Finset.Ioc N (R - 1), ∑ m ∈ Finset.Icc 1 U, f (n + m)‖ +
        2 * (U : ℝ) ^ 2 := by
    calc
      (U : ℝ) * ‖S‖ = ‖(U : ℕ) • S‖ := by simp [nsmul_eq_mul]
      _ = ‖(∑ n ∈ Finset.Ioc N (R - 1), ∑ m ∈ Finset.Icc 1 U, f (n + m)) +
          ∑ m ∈ Finset.Icc 1 U, (S - A m)‖ := by rw [hdecomp]
      _ ≤ ‖∑ n ∈ Finset.Ioc N (R - 1), ∑ m ∈ Finset.Icc 1 U, f (n + m)‖ +
          ‖∑ m ∈ Finset.Icc 1 U, (S - A m)‖ := norm_add_le _ _
      _ ≤ _ := by gcongr
  have hUpos : (0 : ℝ) < U := by exact_mod_cast hU1
  calc
    ‖S‖ ≤ (‖∑ n ∈ Finset.Ioc N (R - 1),
        ∑ m ∈ Finset.Icc 1 U, f (n + m)‖ + 2 * (U : ℝ) ^ 2) / U :=
      (le_div_iff₀ hUpos).2 (by simpa [mul_comm] using hmul)
    _ = (1 / (U : ℝ)) *
          ‖∑ n ∈ Finset.Ioc N (R - 1), ∑ m ∈ Finset.Icc 1 U, f (n + m)‖
        + 2 * U := by
      field_simp

/-- The finite Hölder step in the exponent convention used by the mean
value theorem. -/
theorem sum_norm_le_holder {ι : Type*} (A : Finset ι) (F : ι → ℂ)
    (s : ℕ) (hs : 1 ≤ s) :
    (∑ a ∈ A, ‖F a‖) ≤
      (A.card : ℝ) ^ (1 - ((2 * s : ℕ) : ℝ)⁻¹) *
        (∑ a ∈ A, ‖F a‖ ^ (2 * s)) ^ (((2 * s : ℕ) : ℝ)⁻¹) := by
  have hp : (1 : ℝ) ≤ (2 * s : ℕ) := by exact_mod_cast (by omega : 1 ≤ 2 * s)
  have h := Real.inner_le_weight_mul_Lp_of_nonneg A hp
    (fun _ => (1 : ℝ)) (fun a => ‖F a‖) (fun _ => zero_le_one)
    (fun _ => norm_nonneg _)
  simpa only [one_mul, Finset.sum_const, nsmul_eq_mul, mul_one,
    Real.rpow_natCast] using h

/-! ## Polynomial moments and orthogonality -/

/-- A polynomial phase with coefficient vector indexed by its degrees. -/
noncomputable def polynomialPhase {k : ℕ} (β : Fin k → ℝ) (m : ℕ) : ℝ :=
  ∑ j, β j * (m : ℝ) ^ ((j : ℕ) + 1)

/-- The normalized polynomial Weyl sum on `[1,M]`. -/
noncomputable def polynomialSum (k M : ℕ) (β : Fin k → ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, ExpSums.e (polynomialPhase β m)

/-- The product measure on the half-open unit cube. -/
noncomputable def unitCubeMeasure (k : ℕ) : MeasureTheory.Measure (Fin k → ℝ) :=
  MeasureTheory.Measure.pi fun _ =>
    MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)

theorem unitCubeMeasure_eq_restrict_Icc (k : ℕ) :
    unitCubeMeasure k = MeasureTheory.volume.restrict
      (Set.Icc (fun _ : Fin k => (0 : ℝ)) (fun _ => 1)) := by
  rw [unitCubeMeasure]
  simp_rw [MeasureTheory.restrict_Ioc_eq_restrict_Icc]
  rw [← MeasureTheory.Measure.restrict_pi_pi, ← MeasureTheory.volume_pi]
  congr 1
  ext β
  simp

theorem e_finset_sum {ι : Type*} (A : Finset ι) (f : ι → ℝ) :
    ExpSums.e (∑ i ∈ A, f i) = ∏ i ∈ A, ExpSums.e (f i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [ExpSums.e]
  | @insert a A ha ih => simp [ha, ih, ExpSums.e_add]

/-- Orthogonality of one integer character on the unit interval. -/
theorem integral_e_int_mul (c : ℤ) :
    (∫ x : ℝ in Set.Ioc 0 1, ExpSums.e ((c : ℝ) * x)) =
      if c = 0 then 1 else 0 := by
  by_cases hc : c = 0
  · subst c
    simp [ExpSums.e]
  · rw [if_neg hc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simp_rw [ExpSums.e]
    have hcoef : (2 * (Real.pi : ℂ) * (c : ℂ) * Complex.I) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (Int.cast_ne_zero.mpr hc))
          Complex.I_ne_zero
    have heq : (fun x : ℝ =>
        Complex.exp (2 * Real.pi * (((c : ℝ) * x : ℝ) : ℂ) * Complex.I)) =
        fun x : ℝ => Complex.exp ((2 * (Real.pi : ℂ) * (c : ℂ) * Complex.I) * x) := by
      funext x
      congr 1
      push_cast
      ring
    rw [heq, integral_exp_mul_complex hcoef]
    have hone : Complex.exp (2 * (Real.pi : ℂ) * (c : ℂ) * Complex.I) = 1 := by
      rw [show 2 * (Real.pi : ℂ) * (c : ℂ) * Complex.I =
        (c : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I c
    simp [hone]

/-- Orthogonality of a character of the finite-dimensional unit torus. -/
theorem integral_e_integer_character {k : ℕ} (c : Fin k → ℤ) :
    (∫ β : Fin k → ℝ, ExpSums.e (∑ j, β j * (c j : ℝ))
        ∂unitCubeMeasure k) = if c = 0 then 1 else 0 := by
  classical
  have hprod : (fun β : Fin k → ℝ => ExpSums.e (∑ j, β j * (c j : ℝ))) =
      fun β => ∏ j, ExpSums.e ((c j : ℝ) * β j) := by
    funext β
    rw [e_finset_sum Finset.univ]
    congr 1 with j
    rw [mul_comm]
  rw [hprod, unitCubeMeasure,
    MeasureTheory.integral_fintype_prod_eq_prod (𝕜 := ℂ)
      (μ := fun _ : Fin k =>
        MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))
      (fun j x => ExpSums.e ((c j : ℝ) * x))]
  simp_rw [integral_e_int_mul]
  by_cases hc : c = 0
  · subst c
    simp
  · rw [if_neg hc]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    have hj0 : c j ≠ 0 := by simpa using hj
    rw [if_neg hj0]

/-- A product of polynomial characters is the character of the associated
power-sum vector. -/
theorem prod_e_polynomialPhase {s k : ℕ} (β : Fin k → ℝ)
    (x : Fin s → ℕ) :
    (∏ i, ExpSums.e (polynomialPhase β (x i))) =
      ExpSums.e (∑ j, β j * (vinogradovPowerSum x ((j : ℕ) + 1) : ℝ)) := by
  rw [← e_finset_sum Finset.univ]
  congr 1
  simp only [polynomialPhase, vinogradovPowerSum, Nat.cast_sum, Nat.cast_pow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]

/-- Expanding a power of a polynomial Weyl sum produces tuples in
`[1,M]^s`. -/
theorem polynomialSum_pow (s k M : ℕ) (β : Fin k → ℝ) :
    polynomialSum k M β ^ s =
      ∑ x ∈ vinogradovTuples s M,
        ExpSums.e (∑ j, β j *
          (vinogradovPowerSum x ((j : ℕ) + 1) : ℝ)) := by
  rw [polynomialSum, Finset.sum_pow']
  change (∑ x ∈ vinogradovTuples s M,
    ∏ i, ExpSums.e (polynomialPhase β (x i))) = _
  refine Finset.sum_congr rfl fun x _ => prod_e_polynomialPhase β x

/-- The signed difference of the two moment vectors. -/
def integerMomentDifference {s : ℕ} (k : ℕ)
    (xy : (Fin s → ℕ) × (Fin s → ℕ)) : Fin k → ℤ :=
  fun j => (vinogradovPowerSum xy.1 ((j : ℕ) + 1) : ℤ) -
    (vinogradovPowerSum xy.2 ((j : ℕ) + 1) : ℤ)

theorem integerMomentDifference_eq_zero_iff {s k : ℕ}
    (xy : (Fin s → ℕ) × (Fin s → ℕ)) :
    integerMomentDifference k xy = 0 ↔ IsVinogradovSolution k xy.1 xy.2 := by
  rw [isVinogradovSolution_iff_momentVector_eq]
  constructor
  · intro h
    funext j
    have hj := congrFun h j
    simp only [integerMomentDifference, Pi.zero_apply, sub_eq_zero] at hj
    exact_mod_cast hj
  · intro h
    funext j
    simp only [integerMomentDifference, Pi.zero_apply, sub_eq_zero]
    exact_mod_cast congrFun h j

/-- The character attached to a pair of tuples is the product of the first
tuple's character and the conjugate of the second tuple's character. -/
theorem e_integerMomentDifference {s k : ℕ} (β : Fin k → ℝ)
    (xy : (Fin s → ℕ) × (Fin s → ℕ)) :
    ExpSums.e (∑ j, β j * (integerMomentDifference k xy j : ℝ)) =
      ExpSums.e (∑ j, β j *
          (vinogradovPowerSum xy.1 ((j : ℕ) + 1) : ℝ)) *
        (starRingEnd ℂ) (ExpSums.e (∑ j, β j *
          (vinogradovPowerSum xy.2 ((j : ℕ) + 1) : ℝ))) := by
  have hphase : (∑ j, β j * (integerMomentDifference k xy j : ℝ)) =
      (∑ j, β j * (vinogradovPowerSum xy.1 ((j : ℕ) + 1) : ℝ)) -
        ∑ j, β j * (vinogradovPowerSum xy.2 ((j : ℕ) + 1) : ℝ) := by
    simp only [integerMomentDifference, Int.cast_sub, Int.cast_natCast,
      mul_sub, Finset.sum_sub_distrib]
  rw [hphase, ExpSums.e_mul_conj]

/-- The even norm power is the usual product with the conjugate. -/
theorem ofReal_norm_pow_even (z : ℂ) (s : ℕ) :
    ((‖z‖ ^ (2 * s) : ℝ) : ℂ) = z ^ s * ((starRingEnd ℂ) z) ^ s := by
  rw [show 2 * s = 2 * s from rfl, pow_mul, Complex.ofReal_pow,
    Complex.sq_norm, ← mul_pow, Complex.mul_conj]

/-- Expansion of the even moment as a sum over pairs of tuples. -/
theorem ofReal_norm_polynomialSum_pow_even (s k M : ℕ) (β : Fin k → ℝ) :
    ((‖polynomialSum k M β‖ ^ (2 * s) : ℝ) : ℂ) =
      ∑ xy ∈ (vinogradovTuples s M) ×ˢ (vinogradovTuples s M),
        ExpSums.e (∑ j, β j * (integerMomentDifference k xy j : ℝ)) := by
  calc
    ((‖polynomialSum k M β‖ ^ (2 * s) : ℝ) : ℂ) =
        polynomialSum k M β ^ s *
          ((starRingEnd ℂ) (polynomialSum k M β)) ^ s :=
      ofReal_norm_pow_even _ _
    _ = (∑ x ∈ vinogradovTuples s M,
          ExpSums.e (∑ j, β j *
            (vinogradovPowerSum x ((j : ℕ) + 1) : ℝ))) *
        ∑ y ∈ vinogradovTuples s M,
          (starRingEnd ℂ) (ExpSums.e (∑ j, β j *
            (vinogradovPowerSum y ((j : ℕ) + 1) : ℝ))) := by
      have hstar : ((starRingEnd ℂ) (polynomialSum k M β)) ^ s =
          ∑ y ∈ vinogradovTuples s M,
            (starRingEnd ℂ) (ExpSums.e (∑ j, β j *
              (vinogradovPowerSum y ((j : ℕ) + 1) : ℝ))) := by
        rw [← map_pow, polynomialSum_pow, map_sum]
      rw [polynomialSum_pow, hstar]
    _ = _ := by
      rw [Finset.sum_mul_sum, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      exact (e_integerMomentDifference β (x, y)).symm

theorem norm_polynomialSum_le (k M : ℕ) (β : Fin k → ℝ) :
    ‖polynomialSum k M β‖ ≤ M := by
  rw [polynomialSum]
  calc
    ‖∑ m ∈ Finset.Icc 1 M, ExpSums.e (polynomialPhase β m)‖
        ≤ ∑ _m ∈ Finset.Icc 1 M, (1 : ℝ) :=
      norm_sum_le_of_le _ fun m _ => (ExpSums.norm_e _).le
    _ = M := by simp [Nat.card_Icc]

theorem continuous_polynomialSum (k M : ℕ) :
    Continuous (polynomialSum k M) := by
  unfold polynomialSum polynomialPhase ExpSums.e
  fun_prop

theorem integrable_ofReal_norm_polynomialSum_pow_even (s k M : ℕ) :
    MeasureTheory.Integrable
      (fun β : Fin k → ℝ => ((‖polynomialSum k M β‖ ^ (2 * s) : ℝ) : ℂ))
      (unitCubeMeasure k) := by
  letI : MeasureTheory.IsFiniteMeasure (unitCubeMeasure k) := by
    rw [unitCubeMeasure]
    infer_instance
  apply MeasureTheory.Integrable.of_bound
    ((Complex.continuous_ofReal.comp
      ((continuous_polynomialSum k M).norm.pow (2 * s))).aestronglyMeasurable)
    ((M : ℝ) ^ (2 * s))
  filter_upwards [] with β
  ·
    rw [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_polynomialSum_le k M β) _

theorem integrable_integer_character {k : ℕ} (c : Fin k → ℤ) :
    MeasureTheory.Integrable
      (fun β : Fin k → ℝ => ExpSums.e (∑ j, β j * (c j : ℝ)))
      (unitCubeMeasure k) := by
  letI : MeasureTheory.IsFiniteMeasure (unitCubeMeasure k) := by
    rw [unitCubeMeasure]
    infer_instance
  apply MeasureTheory.Integrable.of_bound (C := 1)
  · have hc : Continuous (fun β : Fin k → ℝ =>
        ExpSums.e (∑ j, β j * (c j : ℝ))) := by
      unfold ExpSums.e
      fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [] with β
    rw [ExpSums.norm_e]

/-- The exponential-sum form of Vinogradov orthogonality.  This is the
conversion from the counting definition used by `vinogradov_mean_value`. -/
theorem integral_ofReal_norm_polynomialSum_pow_even (s k M : ℕ) :
    (∫ β : Fin k → ℝ,
        ((‖polynomialSum k M β‖ ^ (2 * s) : ℝ) : ℂ)
        ∂unitCubeMeasure k) = (vinogradovJ s k M : ℂ) := by
  classical
  have hfun : (fun β : Fin k → ℝ =>
      ((‖polynomialSum k M β‖ ^ (2 * s) : ℝ) : ℂ)) =
      fun β => ∑ xy ∈ (vinogradovTuples s M) ×ˢ (vinogradovTuples s M),
        ExpSums.e (∑ j, β j * (integerMomentDifference k xy j : ℝ)) := by
    funext β
    exact ofReal_norm_polynomialSum_pow_even s k M β
  rw [hfun, MeasureTheory.integral_finset_sum]
  · simp_rw [integral_e_integer_character,
      integerMomentDifference_eq_zero_iff]
    rw [vinogradovJ]
    simp
  · intro xy hxy
    exact integrable_integer_character (integerMomentDifference k xy)

/-- Real-valued form of the same orthogonality identity. -/
theorem integral_norm_polynomialSum_pow_even (s k M : ℕ) :
    (∫ β : Fin k → ℝ, ‖polynomialSum k M β‖ ^ (2 * s)
        ∂unitCubeMeasure k) = (vinogradovJ s k M : ℝ) := by
  have hc := integral_ofReal_norm_polynomialSum_pow_even s k M
  have hi := integrable_ofReal_norm_polynomialSum_pow_even s k M
  have hre := Complex.reCLM.integral_comp_comm hi
  calc
    (∫ β : Fin k → ℝ, ‖polynomialSum k M β‖ ^ (2 * s)
        ∂unitCubeMeasure k) =
        ∫ β : Fin k → ℝ,
          Complex.reCLM (((‖polynomialSum k M β‖ ^ (2 * s) : ℝ) : ℂ))
          ∂unitCubeMeasure k := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with β
      change ‖polynomialSum k M β‖ ^ (2 * s) =
        (((‖polynomialSum k M β‖ ^ (2 * s) : ℝ) : ℂ)).re
      exact Complex.ofReal_re _ |>.symm
    _ = Complex.reCLM (∫ β : Fin k → ℝ,
        ((‖polynomialSum k M β‖ ^ (2 * s) : ℝ) : ℂ)
        ∂unitCubeMeasure k) := hre
    _ = Complex.reCLM (vinogradovJ s k M : ℂ) := by rw [hc]
    _ = (vinogradovJ s k M : ℝ) := by simp

/-! ## Partial summation inside coefficient boxes -/

/-- Discrete partial summation on `[1,M]`. -/
theorem sum_mul_eq_last_mul_add_sum_diff (a w : ℕ → ℂ) (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, w m * a m =
      w M * (∑ m ∈ Finset.Icc 1 M, a m) +
        ∑ m ∈ Finset.Ico 1 M,
          (w m - w (m + 1)) * ∑ q ∈ Finset.Icc 1 m, a q := by
  induction M with
  | zero => simp
  | succ M ih =>
      by_cases hM : M = 0
      · subst M
        simp
      · have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM
        rw [Finset.sum_Icc_succ_top (by omega),
          Finset.sum_Icc_succ_top (by omega),
          Finset.sum_Ico_succ_top hM1, ih]
        ring

/-- Norm consequence of discrete partial summation. -/
theorem norm_sum_mul_le_partial_sums (a w : ℕ → ℂ) (M : ℕ)
    (hw : ‖w M‖ ≤ 1) (D : ℝ)
    (hD : ∀ m ∈ Finset.Ico 1 M, ‖w m - w (m + 1)‖ ≤ D) :
    ‖∑ m ∈ Finset.Icc 1 M, w m * a m‖ ≤
      ‖∑ m ∈ Finset.Icc 1 M, a m‖ +
        D * ∑ m ∈ Finset.Ico 1 M, ‖∑ q ∈ Finset.Icc 1 m, a q‖ := by
  rw [sum_mul_eq_last_mul_add_sum_diff]
  calc
    ‖w M * (∑ m ∈ Finset.Icc 1 M, a m) +
        ∑ m ∈ Finset.Ico 1 M,
          (w m - w (m + 1)) * ∑ q ∈ Finset.Icc 1 m, a q‖
        ≤ ‖w M * (∑ m ∈ Finset.Icc 1 M, a m)‖ +
          ‖∑ m ∈ Finset.Ico 1 M,
            (w m - w (m + 1)) * ∑ q ∈ Finset.Icc 1 m, a q‖ :=
      norm_add_le _ _
    _ ≤ ‖∑ m ∈ Finset.Icc 1 M, a m‖ +
        ∑ m ∈ Finset.Ico 1 M,
          D * ‖∑ q ∈ Finset.Icc 1 m, a q‖ := by
      gcongr
      · rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) hw
      · exact norm_sum_le_of_le _ fun m hm => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hD m hm) (norm_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

/-- Ford's partial-sum majorant. -/
noncomputable def polynomialPartialMajorant (k M : ℕ) (β : Fin k → ℝ) : ℝ :=
  ‖polynomialSum k M β‖ +
    (2 / (M : ℝ)) * ∑ m ∈ Finset.Ico 1 M, ‖polynomialSum k m β‖

theorem polynomialPartialMajorant_nonneg (k M : ℕ) (β : Fin k → ℝ) :
    0 ≤ polynomialPartialMajorant k M β := by
  unfold polynomialPartialMajorant
  positivity

theorem polynomialPartialMajorant_pow_le (s k M : ℕ) (hM : 1 ≤ M)
    (hs : 1 ≤ s) (β : Fin k → ℝ) :
    polynomialPartialMajorant k M β ^ (2 * s) ≤
      2 ^ (2 * s - 1) *
        (‖polynomialSum k M β‖ ^ (2 * s) +
          (2 : ℝ) ^ (2 * s) / M *
            ∑ m ∈ Finset.Ico 1 M, ‖polynomialSum k m β‖ ^ (2 * s)) := by
  let A : ℝ := ‖polynomialSum k M β‖
  let B : ℝ := ∑ m ∈ Finset.Ico 1 M, ‖polynomialSum k m β‖
  have hA : 0 ≤ A := norm_nonneg _
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hp : 1 ≤ 2 * s := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hsum : B ^ (2 * s) ≤ (M : ℝ) ^ (2 * s - 1) *
      ∑ m ∈ Finset.Ico 1 M, ‖polynomialSum k m β‖ ^ (2 * s) := by
    have hpow := pow_sum_le_card_mul_sum_pow
      (s := Finset.Ico 1 M) (f := fun m => ‖polynomialSum k m β‖)
      (fun _ _ => norm_nonneg _) (2 * s - 1)
    have hcard : ((Finset.Ico 1 M).card : ℝ) ≤ M := by
      rw [Nat.card_Ico]
      exact_mod_cast Nat.sub_le M 1
    have hcardpow : ((Finset.Ico 1 M).card : ℝ) ^ (2 * s - 1) ≤
        (M : ℝ) ^ (2 * s - 1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hcard _
    calc
      B ^ (2 * s) ≤ ((Finset.Ico 1 M).card : ℝ) ^ (2 * s - 1) *
          ∑ m ∈ Finset.Ico 1 M, ‖polynomialSum k m β‖ ^ (2 * s) := by
        simpa [B, Nat.sub_add_cancel hp] using hpow
      _ ≤ (M : ℝ) ^ (2 * s - 1) *
          ∑ m ∈ Finset.Ico 1 M, ‖polynomialSum k m β‖ ^ (2 * s) :=
        mul_le_mul_of_nonneg_right hcardpow
          (Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _)
  have hscale : ((2 : ℝ) / M * B) ^ (2 * s) ≤
      (2 : ℝ) ^ (2 * s) / M *
        ∑ m ∈ Finset.Ico 1 M, ‖polynomialSum k m β‖ ^ (2 * s) := by
    rw [mul_pow]
    calc
      ((2 : ℝ) / M) ^ (2 * s) * B ^ (2 * s) ≤
          ((2 : ℝ) / M) ^ (2 * s) *
            ((M : ℝ) ^ (2 * s - 1) *
              ∑ m ∈ Finset.Ico 1 M,
                ‖polynomialSum k m β‖ ^ (2 * s)) :=
        mul_le_mul_of_nonneg_left hsum (pow_nonneg (by positivity) _)
      _ = (2 : ℝ) ^ (2 * s) / M *
          ∑ m ∈ Finset.Ico 1 M, ‖polynomialSum k m β‖ ^ (2 * s) := by
        have hpowM : (M : ℝ) * (M : ℝ) ^ (2 * s - 1) =
            (M : ℝ) ^ (2 * s) := by
          nth_rewrite 2 [show 2 * s = (2 * s - 1) + 1 by omega]
          rw [pow_succ]
          ring
        rw [div_pow]
        field_simp
        calc
          ((M : ℝ) ^ (2 * s - 1) *
              ∑ m ∈ Finset.Ico 1 M, ‖polynomialSum k m β‖ ^ (2 * s)) * M =
              ((M : ℝ) * (M : ℝ) ^ (2 * s - 1)) *
                ∑ m ∈ Finset.Ico 1 M,
                  ‖polynomialSum k m β‖ ^ (2 * s) := by ring
          _ = _ := by rw [hpowM]
  unfold polynomialPartialMajorant
  change (A + 2 / (M : ℝ) * B) ^ (2 * s) ≤ _
  exact (add_pow_le hA (mul_nonneg (by positivity) hB) (2 * s)).trans
    (mul_le_mul_of_nonneg_left (add_le_add_right hscale (A ^ (2 * s)))
      (pow_nonneg (by positivity) _))

theorem polynomialPartialMajorant_le (k M : ℕ) (hM : 1 ≤ M)
    (β : Fin k → ℝ) : polynomialPartialMajorant k M β ≤ 3 * M := by
  have hsum : (∑ m ∈ Finset.Ico 1 M, ‖polynomialSum k m β‖) ≤
      (M : ℝ) * M := by
    calc
      (∑ m ∈ Finset.Ico 1 M, ‖polynomialSum k m β‖) ≤
          ∑ _m ∈ Finset.Ico 1 M, (M : ℝ) := by
        apply Finset.sum_le_sum
        intro m hm
        exact (norm_polynomialSum_le k m β).trans (by
          exact_mod_cast (Finset.mem_Ico.mp hm).2.le)
      _ = ((Finset.Ico 1 M).card : ℝ) * M := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (M : ℝ) * M := by
        gcongr
        rw [Nat.card_Ico]
        exact_mod_cast Nat.sub_le M 1
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  unfold polynomialPartialMajorant
  calc
    ‖polynomialSum k M β‖ +
        2 / (M : ℝ) * ∑ m ∈ Finset.Ico 1 M, ‖polynomialSum k m β‖ ≤
        (M : ℝ) + 2 / M * ((M : ℝ) * M) := by
      gcongr
      · exact norm_polynomialSum_le k M β
    _ = 3 * M := by field_simp; ring

theorem integrable_norm_polynomialSum_pow_even_real (s k M : ℕ) :
    MeasureTheory.Integrable
      (fun β : Fin k → ℝ => ‖polynomialSum k M β‖ ^ (2 * s))
      (unitCubeMeasure k) := by
  letI : MeasureTheory.IsFiniteMeasure (unitCubeMeasure k) := by
    rw [unitCubeMeasure]
    infer_instance
  apply MeasureTheory.Integrable.of_bound
    (((continuous_polynomialSum k M).norm.pow (2 * s)).aestronglyMeasurable)
    ((M : ℝ) ^ (2 * s))
  filter_upwards [] with β
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_polynomialSum_le k M β) _

theorem integrable_polynomialPartialMajorant_pow (s k M : ℕ) (hM : 1 ≤ M) :
    MeasureTheory.Integrable
      (fun β : Fin k → ℝ => polynomialPartialMajorant k M β ^ (2 * s))
      (unitCubeMeasure k) := by
  letI : MeasureTheory.IsFiniteMeasure (unitCubeMeasure k) := by
    rw [unitCubeMeasure]
    infer_instance
  apply MeasureTheory.Integrable.of_bound (C := (3 * (M : ℝ)) ^ (2 * s))
  · unfold polynomialPartialMajorant
    exact (((continuous_polynomialSum k M).norm.add
      (continuous_const.mul (continuous_finset_sum _ fun m _ =>
        (continuous_polynomialSum k m).norm))).pow (2 * s)).aestronglyMeasurable
  · filter_upwards [] with β
    rw [Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (polynomialPartialMajorant_nonneg k M β) _)]
    exact pow_le_pow_left₀ (polynomialPartialMajorant_nonneg k M β)
      (polynomialPartialMajorant_le k M hM β) _

/-- The coefficient-box majorant has the same mean-value cost as the
polynomial sum, up to Ford's explicit `2^(4s)` factor. -/
theorem integral_polynomialPartialMajorant_pow_le (s k M : ℕ)
    (hM : 1 ≤ M) (hs : 1 ≤ s) :
    (∫ β : Fin k → ℝ, polynomialPartialMajorant k M β ^ (2 * s)
        ∂unitCubeMeasure k) ≤
      (2 : ℝ) ^ (4 * s) * (vinogradovJ s k M : ℝ) := by
  let μ := unitCubeMeasure k
  let fM : (Fin k → ℝ) → ℝ :=
    fun β => ‖polynomialSum k M β‖ ^ (2 * s)
  let fsum : (Fin k → ℝ) → ℝ := fun β =>
    ∑ m ∈ Finset.Ico 1 M, ‖polynomialSum k m β‖ ^ (2 * s)
  have hfM : MeasureTheory.Integrable fM μ :=
    integrable_norm_polynomialSum_pow_even_real s k M
  have hfsum : MeasureTheory.Integrable fsum μ := by
    apply MeasureTheory.integrable_finset_sum
    intro m hm
    exact integrable_norm_polynomialSum_pow_even_real s k m
  have hright : MeasureTheory.Integrable (fun β =>
      (2 : ℝ) ^ (2 * s - 1) *
        (fM β + (2 : ℝ) ^ (2 * s) / M * fsum β)) μ :=
    (hfM.add (hfsum.const_mul ((2 : ℝ) ^ (2 * s) / M))).const_mul
      ((2 : ℝ) ^ (2 * s - 1))
  have hpoint : ∀ β, polynomialPartialMajorant k M β ^ (2 * s) ≤
      (2 : ℝ) ^ (2 * s - 1) *
        (fM β + (2 : ℝ) ^ (2 * s) / M * fsum β) := by
    intro β
    exact polynomialPartialMajorant_pow_le s k M hM hs β
  have hint := MeasureTheory.integral_mono_ae
    (integrable_polynomialPartialMajorant_pow s k M hM) hright
    (Filter.Eventually.of_forall hpoint)
  have heval : (∫ β, (2 : ℝ) ^ (2 * s - 1) *
        (fM β + (2 : ℝ) ^ (2 * s) / M * fsum β) ∂μ) =
      (2 : ℝ) ^ (2 * s - 1) *
        ((vinogradovJ s k M : ℝ) + (2 : ℝ) ^ (2 * s) / M *
          ∑ m ∈ Finset.Ico 1 M, (vinogradovJ s k m : ℝ)) := by
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add hfM
        (hfsum.const_mul ((2 : ℝ) ^ (2 * s) / M)),
      MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finset_sum]
    · dsimp [fM, fsum, μ]
      simp_rw [integral_norm_polynomialSum_pow_even]
    · intro m hm
      exact integrable_norm_polynomialSum_pow_even_real s k m
  rw [heval] at hint
  refine hint.trans ?_
  have hsumJ : (∑ m ∈ Finset.Ico 1 M, (vinogradovJ s k m : ℝ)) ≤
      (M : ℝ) * vinogradovJ s k M := by
    calc
      (∑ m ∈ Finset.Ico 1 M, (vinogradovJ s k m : ℝ)) ≤
          ∑ _m ∈ Finset.Ico 1 M, (vinogradovJ s k M : ℝ) := by
        apply Finset.sum_le_sum
        intro m hm
        exact_mod_cast vinogradovJ_mono (Nat.le_of_lt (Finset.mem_Ico.mp hm).2)
      _ = ((Finset.Ico 1 M).card : ℝ) * vinogradovJ s k M := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (M : ℝ) * vinogradovJ s k M := by
        gcongr
        · rw [Nat.card_Ico]
          exact_mod_cast Nat.sub_le M 1
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hinside : (vinogradovJ s k M : ℝ) + (2 : ℝ) ^ (2 * s) / M *
      ∑ m ∈ Finset.Ico 1 M, (vinogradovJ s k m : ℝ) ≤
      (1 + (2 : ℝ) ^ (2 * s)) * vinogradovJ s k M := by
    calc
      (vinogradovJ s k M : ℝ) + (2 : ℝ) ^ (2 * s) / M *
          ∑ m ∈ Finset.Ico 1 M, (vinogradovJ s k m : ℝ) ≤
          (vinogradovJ s k M : ℝ) + (2 : ℝ) ^ (2 * s) / M *
            ((M : ℝ) * vinogradovJ s k M) := by
        gcongr
      _ = (1 + (2 : ℝ) ^ (2 * s)) * vinogradovJ s k M := by
        field_simp
  calc
    (2 : ℝ) ^ (2 * s - 1) *
        ((vinogradovJ s k M : ℝ) + (2 : ℝ) ^ (2 * s) / M *
          ∑ m ∈ Finset.Ico 1 M, (vinogradovJ s k m : ℝ)) ≤
        (2 : ℝ) ^ (2 * s - 1) *
          ((1 + (2 : ℝ) ^ (2 * s)) * vinogradovJ s k M) := by
      gcongr
    _ ≤ (2 : ℝ) ^ (4 * s) * vinogradovJ s k M := by
      have hpow : (2 : ℝ) ^ (2 * s - 1) *
          (1 + (2 : ℝ) ^ (2 * s)) ≤ (2 : ℝ) ^ (4 * s) := by
        have hp : 1 ≤ 2 * s := by omega
        calc
          (2 : ℝ) ^ (2 * s - 1) * (1 + (2 : ℝ) ^ (2 * s)) ≤
              (2 : ℝ) ^ (2 * s - 1) * (2 * (2 : ℝ) ^ (2 * s)) := by
            gcongr
            have hpow1 : (1 : ℝ) ≤ 2 ^ (2 * s) :=
              one_le_pow₀ (a := (2 : ℝ)) (by norm_num)
            nlinarith
          _ = (2 : ℝ) ^ (4 * s) := by
            have htwo : (2 : ℝ) * 2 ^ (2 * s) = 2 ^ (2 * s + 1) := by
              rw [pow_succ']
            rw [htwo, ← pow_add]
            congr 1
            omega
      calc
        (2 : ℝ) ^ (2 * s - 1) *
            ((1 + (2 : ℝ) ^ (2 * s)) * vinogradovJ s k M) =
            ((2 : ℝ) ^ (2 * s - 1) *
              (1 + (2 : ℝ) ^ (2 * s))) * vinogradovJ s k M := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)

/-! ## The logarithmic coefficients -/

/-- The degree-`j+1` coefficient in the shifted logarithmic phase. -/
noncomputable def logCoefficient (t u : ℝ) (n : ℕ) {k : ℕ} (j : Fin k) : ℝ :=
  (-1 : ℝ) ^ ((j : ℕ) + 1) * t /
    (2 * Real.pi * ((j : ℕ) + 1) * ((n : ℝ) + u) ^ ((j : ℕ) + 1))

/-- Derivative of the real logarithmic Taylor remainder. -/
theorem hasDerivAt_log_sub_logPolynomial (k : ℕ) {y w : ℝ}
    (hy : 0 < y) (hyw : 0 < y + w) :
    HasDerivAt (fun x : ℝ =>
      Real.log (1 + x / y) - logPolynomial k (x / y))
      (((-w / y) ^ k * (1 + w / y)⁻¹) / y) w := by
  have hz : 1 + ((w / y : ℝ) : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
    have : 0 < 1 + w / y := by
      rw [show 1 + w / y = (y + w) / y by field_simp]
      positivity
    exact this
  have hc0 := (Complex.hasDerivAt_log_sub_logTaylor k hz).comp_ofReal
  have hq : HasDerivAt (fun x : ℝ => x / y) (1 / y) w :=
    (hasDerivAt_id w).div_const y
  have hc := hc0.scomp w hq
  have hre := Complex.reCLM.hasFDerivAt.comp w hc.hasFDerivAt
  have hre' := hre.hasDerivAt
  convert hre' using 1
  · funext x
    simp only [Function.comp_apply, Complex.reCLM_apply, Complex.sub_re]
    rw [show (1 : ℂ) + ((x / y : ℝ) : ℂ) = ((1 + x / y : ℝ) : ℂ) by
      push_cast; rfl, Complex.log_ofReal_re, ← logPolynomial_eq_logTaylor_re]
  · simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul, Complex.reCLM_apply,
      Complex.smul_re, smul_eq_mul]
    have hreal : (-((w / y : ℝ) : ℂ)) ^ k *
        (1 + ((w / y : ℝ) : ℂ))⁻¹ =
        (((-w / y) ^ k * (1 + w / y)⁻¹ : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hreal, Complex.ofReal_re]
    ring

theorem polynomialPhase_logCoefficient (k n m : ℕ) (t u : ℝ)
    (hnu : (n : ℝ) + u ≠ 0) :
    polynomialPhase (fun j : Fin k => logCoefficient t u n j) m =
      -(t / (2 * Real.pi)) *
        logPolynomial k ((m : ℝ) / ((n : ℝ) + u)) := by
  classical
  unfold polynomialPhase logPolynomial logCoefficient
  let F : ℕ → ℝ := fun i =>
    (-1 : ℝ) ^ (i + 1) * t /
      (2 * Real.pi * (i + 1) * ((n : ℝ) + u) ^ (i + 1)) * (m : ℝ) ^ (i + 1)
  change (∑ j : Fin k, F j) = _
  rw [Fin.sum_univ_eq_sum_range F k]
  have hreindex : (∑ j ∈ Finset.Icc 1 k,
      (-1 : ℝ) ^ (j + 1) * ((m : ℝ) / ((n : ℝ) + u)) ^ j / j) =
      ∑ i ∈ Finset.range k,
        (-1 : ℝ) ^ (i + 2) *
          ((m : ℝ) / ((n : ℝ) + u)) ^ (i + 1) / (i + 1) := by
    rw [← Finset.Ico_add_one_right_eq_Icc 1 k,
      Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [add_comm, add_left_comm]
  rw [hreindex]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change F i = _
  unfold F
  have hi1 : ((i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hsign1 : (-1 : ℝ) ^ (i + 1) = -((-1 : ℝ) ^ i) := by
    rw [pow_succ]
    ring
  have hsign2 : (-1 : ℝ) ^ (i + 2) = (-1 : ℝ) ^ i := by
    rw [show i + 2 = (i + 1) + 1 by omega, pow_succ, hsign1]
    ring
  rw [div_pow, hsign1, hsign2]
  field_simp [hnu]

/-- Polynomial phase evaluated on a real short variable. -/
noncomputable def polynomialPhaseReal {k : ℕ} (β : Fin k → ℝ) (w : ℝ) : ℝ :=
  ∑ j, β j * w ^ ((j : ℕ) + 1)

theorem hasDerivAt_polynomialPhaseReal {k : ℕ} (β : Fin k → ℝ) (w : ℝ) :
    HasDerivAt (polynomialPhaseReal β)
      (∑ j : Fin k, ((j : ℕ) + 1) * β j * w ^ (j : ℕ)) w := by
  have hsum : HasDerivAt
      (fun x : ℝ => ∑ j : Fin k, β j * x ^ ((j : ℕ) + 1))
      (∑ j : Fin k, ((j : ℕ) + 1) * β j * w ^ (j : ℕ)) w := by
    convert HasDerivAt.sum (u := Finset.univ) (fun (j : Fin k) _ =>
      (hasDerivAt_pow ((j : ℕ) + 1) w).const_mul (β j)) using 1
    · funext x
      simp
    · apply Finset.sum_congr rfl
      intro j hj
      push_cast
      ring
  exact hsum

/-- Residual phase after replacing the logarithm by a nearby polynomial. -/
noncomputable def phaseError (k n : ℕ) (t u : ℝ)
    (β : Fin k → ℝ) (w : ℝ) : ℝ :=
  -(t / (2 * Real.pi)) *
      (Real.log (1 + w / ((n : ℝ) + u)) -
        logPolynomial k (w / ((n : ℝ) + u))) +
    polynomialPhaseReal (fun j => logCoefficient t u n j - β j) w

noncomputable def phaseErrorDerivative (k n : ℕ) (t u : ℝ)
    (β : Fin k → ℝ) (w : ℝ) : ℝ :=
  -(t / (2 * Real.pi)) *
      (((-w / ((n : ℝ) + u)) ^ k *
        (1 + w / ((n : ℝ) + u))⁻¹) / ((n : ℝ) + u)) +
    ∑ j : Fin k, ((j : ℕ) + 1) * (logCoefficient t u n j - β j) *
      w ^ (j : ℕ)

theorem hasDerivAt_phaseError (k n : ℕ) (t u : ℝ)
    (β : Fin k → ℝ) {w : ℝ} (hnu : 0 < (n : ℝ) + u)
    (hnuw : 0 < (n : ℝ) + u + w) :
    HasDerivAt (phaseError k n t u β)
      (phaseErrorDerivative k n t u β w) w := by
  unfold phaseError
  unfold phaseErrorDerivative
  exact ((hasDerivAt_log_sub_logPolynomial k hnu hnuw).const_mul
    (-(t / (2 * Real.pi)))).add
      (hasDerivAt_polynomialPhaseReal _ w)

theorem phaseError_eq (k n m : ℕ) (t u : ℝ)
    (β : Fin k → ℝ) (hnu : (n : ℝ) + u ≠ 0) :
    -(t / (2 * Real.pi)) * Real.log (1 + (m : ℝ) / ((n : ℝ) + u)) -
        polynomialPhase β m = phaseError k n t u β m := by
  unfold phaseError polynomialPhaseReal
  have hgamma := polynomialPhase_logCoefficient k n m t u hnu
  unfold polynomialPhase at hgamma ⊢
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  rw [hgamma]
  ring

/-- Radius of Ford's coefficient neighbourhood in degree `j+1`. -/
noncomputable def coefficientRadius (k M : ℕ) {d : ℕ} (j : Fin d) : ℝ :=
  1 / (2 * Real.pi * (k : ℝ) ^ 2 * (M : ℝ) ^ ((j : ℕ) + 1))

theorem coefficientRadius_pos {k M d : ℕ} (hk : 1 ≤ k) (hM : 1 ≤ M)
    (j : Fin d) : 0 < coefficientRadius k M j := by
  unfold coefficientRadius
  positivity

/-- Inside a coefficient box, the polynomial part of the residual derivative
costs at most `1/(2πM)`. -/
theorem abs_sum_coefficient_error_le {k M n : ℕ} {t u w : ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hw0 : 0 ≤ w) (hwM : w ≤ M)
    (β : Fin k → ℝ)
    (hβ : ∀ j, |β j - logCoefficient t u n j| ≤ coefficientRadius k M j) :
    |∑ j : Fin k, ((j : ℕ) + 1) * (logCoefficient t u n j - β j) *
        w ^ (j : ℕ)| ≤ 1 / (2 * Real.pi * M) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  calc
    |∑ j : Fin k, ((j : ℕ) + 1) * (logCoefficient t u n j - β j) *
        w ^ (j : ℕ)| ≤
        ∑ j : Fin k, |((j : ℕ) + 1) *
          (logCoefficient t u n j - β j) * w ^ (j : ℕ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin k, 1 / (2 * Real.pi * k * M) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity :
          (0 : ℝ) ≤ ((j : ℕ) : ℝ) + 1),
        abs_of_nonneg (pow_nonneg hw0 _), abs_sub_comm]
      have hjk : ((j : ℝ) + 1) ≤ (k : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr j.isLt)
      have hpow : w ^ (j : ℕ) ≤ (M : ℝ) ^ (j : ℕ) :=
        pow_le_pow_left₀ hw0 hwM _
      have hfirst :
          (((j : ℕ) : ℝ) + 1) * |β j - logCoefficient t u n j| ≤
            (k : ℝ) * coefficientRadius k M j :=
        mul_le_mul hjk (hβ j) (abs_nonneg _)
          hkR.le
      calc
        (((j : ℕ) : ℝ) + 1) * |β j - logCoefficient t u n j| *
            w ^ (j : ℕ) ≤
            (k : ℝ) * coefficientRadius k M j *
              (M : ℝ) ^ (j : ℕ) := by
          exact mul_le_mul hfirst hpow (pow_nonneg hw0 _)
            (mul_nonneg hkR.le (coefficientRadius_pos hk hM j).le)
        _ = 1 / (2 * Real.pi * k * M) := by
          unfold coefficientRadius
          have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
          field_simp
          rw [show (j : ℕ) + 1 = (j : ℕ) + 1 by rfl, pow_succ]
    _ = 1 / (2 * Real.pi * M) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp

/-- The full residual derivative bound once the Taylor tail is at its
natural `1/(2πM)` scale. -/
theorem abs_phaseErrorDerivative_le {k M n : ℕ} {t u w : ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hw0 : 0 ≤ w) (hwM : w ≤ M)
    (β : Fin k → ℝ)
    (hβ : ∀ j, |β j - logCoefficient t u n j| ≤ coefficientRadius k M j)
    (hrem : |-(t / (2 * Real.pi)) *
        (((-w / ((n : ℝ) + u)) ^ k *
          (1 + w / ((n : ℝ) + u))⁻¹) / ((n : ℝ) + u))| ≤
        1 / (2 * Real.pi * M)) :
    |phaseErrorDerivative k n t u β w| ≤ 1 / (Real.pi * M) := by
  unfold phaseErrorDerivative
  calc
    |-(t / (2 * Real.pi)) *
          (((-w / ((n : ℝ) + u)) ^ k *
            (1 + w / ((n : ℝ) + u))⁻¹) / ((n : ℝ) + u)) +
        ∑ j : Fin k, ((j : ℕ) + 1) * (logCoefficient t u n j - β j) *
          w ^ (j : ℕ)| ≤
        |-(t / (2 * Real.pi)) *
          (((-w / ((n : ℝ) + u)) ^ k *
            (1 + w / ((n : ℝ) + u))⁻¹) / ((n : ℝ) + u))| +
        |∑ j : Fin k, ((j : ℕ) + 1) * (logCoefficient t u n j - β j) *
          w ^ (j : ℕ)| := abs_add_le _ _
    _ ≤ 1 / (2 * Real.pi * M) + 1 / (2 * Real.pi * M) :=
      add_le_add hrem (abs_sum_coefficient_error_le hk hM hw0 hwM β hβ)
    _ = 1 / (Real.pi * M) := by field_simp; ring

/-- Ford's scale condition makes the differentiated logarithmic Taylor tail
cost at most `1/(2πM)`. -/
theorem abs_logTaylor_derivative_le {k M N n : ℕ} {t u w : ℝ}
    (hM : 1 ≤ M) (hN : 1 ≤ N) (hn : N ≤ n)
    (ht0 : 0 ≤ t) (hu0 : 0 ≤ u) (hw0 : 0 ≤ w) (hwM : w ≤ M)
    (hscale : t * (M : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1)) :
    |-(t / (2 * Real.pi)) *
        (((-w / ((n : ℝ) + u)) ^ k *
          (1 + w / ((n : ℝ) + u))⁻¹) / ((n : ℝ) + u))| ≤
      1 / (2 * Real.pi * M) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnu : (0 : ℝ) < (n : ℝ) + u := lt_of_lt_of_le hNR (by linarith)
  have hnuw : (0 : ℝ) < (n : ℝ) + u + w := by linarith
  have hwpow : w ^ k ≤ (M : ℝ) ^ k := pow_le_pow_left₀ hw0 hwM k
  have hnuN : (N : ℝ) ≤ (n : ℝ) + u := by linarith
  have hcore :
      t * w ^ k * M ≤
        ((n : ℝ) + u) ^ k * ((n : ℝ) + u + w) := by
    calc
      t * w ^ k * M ≤ t * (M : ℝ) ^ k * M := by gcongr
      _ = t * (M : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
      _ ≤ (N : ℝ) ^ (k + 1) := hscale
      _ ≤ ((n : ℝ) + u) ^ (k + 1) :=
        pow_le_pow_left₀ hNR.le hnuN (k + 1)
      _ = ((n : ℝ) + u) ^ k * ((n : ℝ) + u) := by rw [pow_succ]
      _ ≤ ((n : ℝ) + u) ^ k * ((n : ℝ) + u + w) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hnu.le _)
  have hform :
      |-(t / (2 * Real.pi)) *
          (((-w / ((n : ℝ) + u)) ^ k *
            (1 + w / ((n : ℝ) + u))⁻¹) / ((n : ℝ) + u))| =
        t * w ^ k /
          (2 * Real.pi * ((n : ℝ) + u) ^ k * ((n : ℝ) + u + w)) := by
    rw [abs_mul, abs_neg, abs_div, abs_of_nonneg ht0,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), abs_div,
      abs_mul, abs_pow, abs_div, abs_neg, abs_of_nonneg hw0,
      abs_of_pos hnu, abs_inv,
      abs_of_pos (by positivity : (0 : ℝ) < 1 + w / ((n : ℝ) + u))]
    field_simp
    rw [div_pow]
    field_simp
  rw [hform]
  apply (div_le_div_iff₀ (by positivity :
    (0 : ℝ) < 2 * Real.pi * ((n : ℝ) + u) ^ k * ((n : ℝ) + u + w))
      (by positivity : (0 : ℝ) < 2 * Real.pi * M)).2
  nlinarith [Real.pi_pos]

/-- Consecutive residual phases differ by at most `1/(πM)` throughout a
Ford block. -/
theorem abs_phaseError_succ_sub_le {k M N n m : ℕ} {t u : ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hN : 1 ≤ N) (hn : N ≤ n)
    (hm : m < M) (ht0 : 0 ≤ t) (hu0 : 0 ≤ u)
    (hscale : t * (M : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1))
    (β : Fin k → ℝ)
    (hβ : ∀ j, |β j - logCoefficient t u n j| ≤ coefficientRadius k M j) :
    |phaseError k n t u β ((m + 1 : ℕ) : ℝ) -
        phaseError k n t u β m| ≤
      1 / (Real.pi * M) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnu : (0 : ℝ) < (n : ℝ) + u := lt_of_lt_of_le hNR (by linarith)
  have hmM : m + 1 ≤ M := by omega
  have hderiv : ∀ x ∈ Set.Icc (m : ℝ) (m + 1 : ℕ),
      HasDerivWithinAt (phaseError k n t u β)
        (phaseErrorDerivative k n t u β x)
        (Set.Icc (m : ℝ) (m + 1 : ℕ)) x := by
    intro x hx
    apply HasDerivAt.hasDerivWithinAt
    apply hasDerivAt_phaseError
    · exact hnu
    · have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg m) hx.1
      positivity
  have hbound : ∀ x ∈ Set.Ico (m : ℝ) (m + 1 : ℕ),
      ‖phaseErrorDerivative k n t u β x‖ ≤ 1 / (Real.pi * M) := by
    intro x hx
    rw [Real.norm_eq_abs]
    apply abs_phaseErrorDerivative_le hk hM
    · exact le_trans (Nat.cast_nonneg m) hx.1
    · exact le_trans hx.2.le (by exact_mod_cast hmM)
    · exact hβ
    · apply abs_logTaylor_derivative_le hM hN hn ht0 hu0
        (le_trans (Nat.cast_nonneg m) hx.1)
        (le_trans hx.2.le (by exact_mod_cast hmM)) hscale
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := (m : ℝ)) (b := (m + 1 : ℕ)) hderiv hbound
      ((m + 1 : ℕ) : ℝ) (by norm_num :
        (((m + 1 : ℕ) : ℝ) ∈ Set.Icc (m : ℝ) (m + 1 : ℕ)))
  simpa [Real.norm_eq_abs] using hmv

/-- The normalized characters attached to consecutive residual phases have
variation at most `2/M`. -/
theorem norm_e_phaseError_sub_succ_le {k M N n m : ℕ} {t u : ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hN : 1 ≤ N) (hn : N ≤ n)
    (hm : m < M) (ht0 : 0 ≤ t) (hu0 : 0 ≤ u)
    (hscale : t * (M : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1))
    (β : Fin k → ℝ)
    (hβ : ∀ j, |β j - logCoefficient t u n j| ≤ coefficientRadius k M j) :
    ‖ExpSums.e (phaseError k n t u β m) -
        ExpSums.e (phaseError k n t u β ((m + 1 : ℕ) : ℝ))‖ ≤ 2 / M := by
  let a := phaseError k n t u β ((m + 1 : ℕ) : ℝ)
  let ρ := phaseError k n t u β m - a
  have hρ : |ρ| ≤ 1 / (Real.pi * M) := by
    simpa [a, ρ, abs_sub_comm] using
      abs_phaseError_succ_sub_le hk hM hN hn hm ht0 hu0 hscale β hβ
  calc
    ‖ExpSums.e (phaseError k n t u β m) -
        ExpSums.e (phaseError k n t u β ((m + 1 : ℕ) : ℝ))‖ =
        ‖ExpSums.e (a + ρ) - ExpSums.e a‖ := by
      rw [show phaseError k n t u β m = a + ρ by simp [a, ρ],
        show phaseError k n t u β ((m + 1 : ℕ) : ℝ) = a by rfl]
    _ ≤ 2 * Real.pi * |ρ| := norm_e_add_sub_e_le a ρ
    _ ≤ 2 * Real.pi * (1 / (Real.pi * M)) := by gcongr
    _ = 2 / M := by field_simp

/-- Exact phase factorization used before discrete partial summation. -/
theorem e_log_phase_factorization {k n m : ℕ} {t u : ℝ}
    (β : Fin k → ℝ) (hnu : 0 < (n : ℝ) + u) :
    ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((n : ℝ) + u + m)) =
      ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((n : ℝ) + u)) *
        (ExpSums.e (phaseError k n t u β m) *
          ExpSums.e (polynomialPhase β m)) := by
  have hratio : 0 < 1 + (m : ℝ) / ((n : ℝ) + u) := by positivity
  have hmul : ((n : ℝ) + u) * (1 + (m : ℝ) / ((n : ℝ) + u)) =
      (n : ℝ) + u + m := by field_simp
  have hlog : Real.log ((n : ℝ) + u + m) =
      Real.log ((n : ℝ) + u) +
        Real.log (1 + (m : ℝ) / ((n : ℝ) + u)) := by
    rw [← hmul, Real.log_mul hnu.ne' hratio.ne']
  have herr := phaseError_eq k n m t u β hnu.ne'
  have hphase :
      -(t / (2 * Real.pi)) * Real.log ((n : ℝ) + u + m) =
        -(t / (2 * Real.pi)) * Real.log ((n : ℝ) + u) +
          (phaseError k n t u β m + polynomialPhase β m) := by
    rw [hlog]
    linarith
  rw [hphase, ExpSums.e_add, ExpSums.e_add]

/-- A logarithmic block whose coefficient vector lies in Ford's box is
controlled by the polynomial partial-sum majorant. -/
theorem norm_log_block_le_polynomialPartialMajorant
    {k M N n : ℕ} {t u : ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hN : 1 ≤ N) (hn : N ≤ n)
    (ht0 : 0 ≤ t) (hu0 : 0 ≤ u)
    (hscale : t * (M : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1))
    (β : Fin k → ℝ)
    (hβ : ∀ j, |β j - logCoefficient t u n j| ≤ coefficientRadius k M j) :
    ‖∑ m ∈ Finset.Icc 1 M,
        ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((n : ℝ) + u + m))‖ ≤
      polynomialPartialMajorant k M β := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnu : (0 : ℝ) < (n : ℝ) + u := lt_of_lt_of_le hNR (by linarith)
  let a : ℕ → ℂ := fun m => ExpSums.e (polynomialPhase β m)
  let w : ℕ → ℂ := fun m => ExpSums.e (phaseError k n t u β m)
  have hab := norm_sum_mul_le_partial_sums a w M
    (by simp [w, ExpSums.norm_e]) (2 / M) (by
      intro m hm
      have hm' : 1 ≤ m ∧ m < M := by simpa using hm
      simpa only [w] using
        norm_e_phaseError_sub_succ_le hk hM hN hn hm'.2 ht0 hu0
          hscale β hβ)
  have hfactor :
      (∑ m ∈ Finset.Icc 1 M,
          ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((n : ℝ) + u + m))) =
        ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((n : ℝ) + u)) *
          ∑ m ∈ Finset.Icc 1 M, w m * a m := by
    simp_rw [e_log_phase_factorization β hnu]
    rw [Finset.mul_sum]
  rw [hfactor, norm_mul, ExpSums.norm_e, one_mul]
  simpa only [a, w, polynomialPartialMajorant, polynomialSum] using hab

/-! ## Coefficient boxes -/

/-- The fractional coefficient vector around which the frequency box is
centered. -/
noncomputable def fractionalLogCoefficient (t u : ℝ) (n : ℕ) {k : ℕ}
    (j : Fin k) : ℝ := Int.fract (logCoefficient t u n j)

/-- Centered Ford box.  It lies in the slightly enlarged cube
`[-r,1+r]^k`, which avoids special cases at `0` and `1`. -/
noncomputable def coefficientBox (k M n : ℕ) (t u : ℝ) : Set (Fin k → ℝ) :=
  Set.Icc
    (fun j => fractionalLogCoefficient t u n j - coefficientRadius k M j)
    (fun j => fractionalLogCoefficient t u n j + coefficientRadius k M j)

/-- Restore the integer parts of the logarithmic coefficient vector. -/
noncomputable def liftCoefficient (t u : ℝ) (n : ℕ) {k : ℕ}
    (β : Fin k → ℝ) (j : Fin k) : ℝ :=
  β j + (⌊logCoefficient t u n j⌋ : ℤ)

theorem liftCoefficient_sub_logCoefficient {k n : ℕ} {t u : ℝ}
    (β : Fin k → ℝ) (j : Fin k) :
    liftCoefficient t u n β j - logCoefficient t u n j =
      β j - fractionalLogCoefficient t u n j := by
  unfold liftCoefficient fractionalLogCoefficient
  linarith [Int.fract_add_floor (logCoefficient t u n j)]

theorem abs_liftCoefficient_sub_le_radius {k M n : ℕ} {t u : ℝ}
    {β : Fin k → ℝ} (hβ : β ∈ coefficientBox k M n t u) (j : Fin k) :
    |liftCoefficient t u n β j - logCoefficient t u n j| ≤
      coefficientRadius k M j := by
  rw [liftCoefficient_sub_logCoefficient, abs_le]
  exact ⟨by linarith [hβ.1 j], by linarith [hβ.2 j]⟩

theorem coefficientRadius_le_one {k M d : ℕ} (hk : 1 ≤ k) (hM : 1 ≤ M)
    (j : Fin d) : coefficientRadius k M j ≤ 1 := by
  unfold coefficientRadius
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hden : (1 : ℝ) ≤
      2 * Real.pi * (k : ℝ) ^ 2 * (M : ℝ) ^ ((j : ℕ) + 1) := by
    have hpi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    calc
      (1 : ℝ) ≤ 2 * Real.pi * 1 ^ 2 * 1 ^ ((j : ℕ) + 1) := by simpa
      _ ≤ 2 * Real.pi * (k : ℝ) ^ 2 * (M : ℝ) ^ ((j : ℕ) + 1) := by
        gcongr
  exact (one_div_le_one_div_of_le zero_lt_one hden).trans_eq (one_div_one)

theorem coefficientBox_subset_enlargedCube {k M n : ℕ} {t u : ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) :
    coefficientBox k M n t u ⊆ Set.Icc (fun _ => (-1 : ℝ)) (fun _ => 2) := by
  intro β hβ
  constructor
  · intro j
    have hfract := Int.fract_nonneg (logCoefficient t u n j)
    have hr := coefficientRadius_le_one hk hM j
    have hlow : (-1 : ℝ) ≤ fractionalLogCoefficient t u n j -
        coefficientRadius k M j := by
      unfold fractionalLogCoefficient
      linarith
    exact hlow.trans (hβ.1 j)
  · intro j
    have hfract := Int.fract_lt_one (logCoefficient t u n j)
    have hr := coefficientRadius_le_one hk hM j
    have hupp : fractionalLogCoefficient t u n j +
        coefficientRadius k M j ≤ 2 := by
      unfold fractionalLogCoefficient
      linarith
    exact (hβ.2 j).trans hupp

theorem coefficientBox_volume_toReal {k M n : ℕ} {t u : ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) :
    (MeasureTheory.volume (coefficientBox k M n t u)).toReal =
      ∏ j : Fin k, 2 * coefficientRadius k M j := by
  unfold coefficientBox
  rw [Real.volume_Icc_pi_toReal]
  · apply Finset.prod_congr rfl
    intro j hj
    ring
  · intro j
    dsimp
    linarith [coefficientRadius_pos hk hM j]

theorem coefficientBox_volume_pos {k M n : ℕ} {t u : ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) :
    0 < (MeasureTheory.volume (coefficientBox k M n t u)).toReal := by
  rw [coefficientBox_volume_toReal hk hM]
  exact Finset.prod_pos fun j _ => mul_pos zero_lt_two
    (coefficientRadius_pos hk hM j)

/-- The common volume of every coefficient box at fixed `k,M`. -/
noncomputable def coefficientBoxVolume (k M : ℕ) : ℝ :=
  ∏ j : Fin k, 2 * coefficientRadius k M j

theorem coefficientBox_volume_eq_common {k M n : ℕ} {t u : ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) :
    (MeasureTheory.volume (coefficientBox k M n t u)).toReal =
      coefficientBoxVolume k M := by
  exact coefficientBox_volume_toReal hk hM

theorem coefficientBoxVolume_pos {k M : ℕ} (hk : 1 ≤ k) (hM : 1 ≤ M) :
    0 < coefficientBoxVolume k M := by
  unfold coefficientBoxVolume
  exact Finset.prod_pos fun j _ => mul_pos zero_lt_two
    (coefficientRadius_pos hk hM j)

private theorem sum_fin_val_add_one (k : ℕ) :
    ∑ j : Fin k, ((j : ℕ) + 1) = k * (k + 1) / 2 := by
  rw [Finset.sum_fin_eq_sum_range]
  have hclean : Finset.sum (Finset.range k)
      (fun i => if h : i < k then i + 1 else 0) =
      Finset.sum (Finset.range k) (fun i => i + 1) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  rw [hclean]
  have hsplit := Finset.sum_add_distrib (s := Finset.range k)
    (f := fun i => i) (g := fun _ => 1)
  rw [hsplit]
  simp only [Finset.sum_range_id, Finset.sum_const, Finset.card_range,
    smul_eq_mul, mul_one]
  calc
    k * (k - 1) / 2 + k = (k + 1) * (k + 1 - 1) / 2 :=
      (Nat.triangle_succ k).symm
    _ = k * (k + 1) / 2 := by
      rw [Nat.add_sub_cancel]
      congr 1
      exact Nat.mul_comm _ _

/-- Closed form for the common coefficient-box volume. -/
theorem coefficientBoxVolume_eq {k M : ℕ} (hk : 1 ≤ k) (hM : 1 ≤ M) :
    coefficientBoxVolume k M =
      (1 / (Real.pi * (k : ℝ) ^ 2)) ^ k *
        (1 / (M : ℝ)) ^ (k * (k + 1) / 2) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hterm : ∀ j : Fin k,
      2 * coefficientRadius k M j =
        (1 / (Real.pi * (k : ℝ) ^ 2)) *
          (1 / (M : ℝ)) ^ ((j : ℕ) + 1) := by
    intro j
    unfold coefficientRadius
    rw [one_div_pow]
    field_simp [Real.pi_ne_zero, hk0, hM0]
  unfold coefficientBoxVolume
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_pow_eq_pow_sum, sum_fin_val_add_one]
  simp only [Finset.card_univ, Fintype.card_fin]

/-- Adding integral coefficients does not change a normalized polynomial
character at integer arguments. -/
theorem e_polynomialPhase_add_int {k : ℕ} (β : Fin k → ℝ)
    (z : Fin k → ℤ) (m : ℕ) :
    ExpSums.e (polynomialPhase (fun j => β j + (z j : ℝ)) m) =
      ExpSums.e (polynomialPhase β m) := by
  let q : ℤ := ∑ j : Fin k, z j * (m : ℤ) ^ ((j : ℕ) + 1)
  have hphase : polynomialPhase (fun j => β j + (z j : ℝ)) m =
      polynomialPhase β m + (q : ℝ) := by
    unfold polynomialPhase q
    simp_rw [add_mul, Finset.sum_add_distrib]
    push_cast
    rfl
  rw [hphase, ExpSums.e_add, ExpSums.e_intCast, mul_one]

theorem polynomialSum_add_int {k M : ℕ} (β : Fin k → ℝ)
    (z : Fin k → ℤ) :
    polynomialSum k M (fun j => β j + (z j : ℝ)) = polynomialSum k M β := by
  unfold polynomialSum
  apply Finset.sum_congr rfl
  intro m hm
  exact e_polynomialPhase_add_int β z m

theorem polynomialPartialMajorant_add_int {k M : ℕ} (β : Fin k → ℝ)
    (z : Fin k → ℤ) :
    polynomialPartialMajorant k M (fun j => β j + (z j : ℝ)) =
      polynomialPartialMajorant k M β := by
  unfold polynomialPartialMajorant
  rw [polynomialSum_add_int β z]
  congr 2
  apply Finset.sum_congr rfl
  intro m hm
  rw [polynomialSum_add_int β z]

/-! ## Folding coefficient space -/

/-- The three integral shifts `-1, 0, 1` used to cover each coordinate of
the enlarged coefficient cube. -/
def foldShift {k : ℕ} (z : Fin k → Fin 3) : Fin k → ℤ :=
  fun j => (z j : ℤ) - 1

/-- The unit coefficient cube translated by one of the folding shifts. -/
def shiftedUnitCube {k : ℕ} (z : Fin k → Fin 3) : Set (Fin k → ℝ) :=
  Set.Icc (fun j => (foldShift z j : ℝ))
    (fun j => (foldShift z j : ℝ) + 1)

theorem image_unitCube_add_foldShift {k : ℕ} (z : Fin k → Fin 3) :
    (fun β : Fin k → ℝ => (fun j => (foldShift z j : ℝ)) + β) ''
        Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1) = shiftedUnitCube z := by
  ext β
  constructor
  · rintro ⟨α, hα, rfl⟩
    constructor <;> intro j
    · exact le_add_of_nonneg_right (hα.1 j)
    · simpa only [Pi.add_apply, add_comm] using add_le_add_left (hα.2 j)
        (foldShift z j : ℝ)
  · intro hβ
    refine ⟨β - fun j => (foldShift z j : ℝ), ?_, ?_⟩
    · constructor <;> intro j
      · simpa only [Pi.sub_apply] using sub_nonneg.mpr (hβ.1 j)
      · simpa only [Pi.sub_apply, sub_le_iff_le_add, add_comm] using hβ.2 j
    · funext j
      simp

theorem enlargedCube_subset_iUnion_shiftedUnitCube (k : ℕ) :
    Set.Icc (fun _ : Fin k => (-1 : ℝ)) (fun _ => 2) ⊆
      ⋃ z : Fin k → Fin 3, shiftedUnitCube z := by
  intro β hβ
  let z : Fin k → Fin 3 := fun j =>
    if h₀ : β j ≤ 0 then ⟨0, by omega⟩
    else if h₁ : β j ≤ 1 then ⟨1, by omega⟩ else ⟨2, by omega⟩
  rw [Set.mem_iUnion]
  refine ⟨z, ?_⟩
  constructor <;> intro j
  · dsimp [z, shiftedUnitCube, foldShift]
    split_ifs with h₀ h₁
    · norm_num
      exact (hβ.1 j)
    · norm_num
      exact le_of_not_ge h₀
    · norm_num
      exact le_of_not_ge h₁
  · dsimp [z, shiftedUnitCube, foldShift]
    split_ifs with h₀ h₁
    · norm_num
      exact h₀
    · norm_num
      exact h₁
    · norm_num
      exact hβ.2 j

/-- Translation by an integral coefficient vector leaves the majorant's
unit-cube moment unchanged. -/
theorem integral_shiftedUnitCube_majorant_pow {s k M : ℕ}
    (z : Fin k → Fin 3) :
    ∫ β in shiftedUnitCube z, polynomialPartialMajorant k M β ^ (2 * s) =
      ∫ β in Set.Icc (fun _ : Fin k => (0 : ℝ)) (fun _ => 1),
        polynomialPartialMajorant k M β ^ (2 * s) := by
  let a : Fin k → ℝ := fun j => (foldShift z j : ℝ)
  let f : (Fin k → ℝ) → (Fin k → ℝ) := fun β => a + β
  have hpres : MeasureTheory.MeasurePreserving f := by
    exact MeasureTheory.measurePreserving_add_left MeasureTheory.volume a
  have hemb : MeasurableEmbedding f := by
    exact (Homeomorph.addLeft a).isClosedEmbedding.measurableEmbedding
  have himage : f '' Set.Icc (fun _ : Fin k => (0 : ℝ)) (fun _ => 1) =
      shiftedUnitCube z := by
    simpa only [f, a] using image_unitCube_add_foldShift z
  rw [← himage, hpres.setIntegral_image_emb hemb]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro β hβ
  have hperiod := polynomialPartialMajorant_add_int (M := M) β (foldShift z)
  change polynomialPartialMajorant k M (f β) ^ (2 * s) =
    polynomialPartialMajorant k M β ^ (2 * s)
  rw [show f β = fun j => β j + (foldShift z j : ℝ) by
    funext j
    simp only [f, a, Pi.add_apply, add_comm]]
  exact congrArg (fun x : ℝ => x ^ (2 * s)) hperiod

/-- Fold `[-1,2]^k` into three unit periods in each coordinate.  Endpoint
overlap is harmless because the integrand is nonnegative. -/
theorem integral_enlargedCube_majorant_pow_le {s k M : ℕ} :
    ∫ β in Set.Icc (fun _ : Fin k => (-1 : ℝ)) (fun _ => 2),
        polynomialPartialMajorant k M β ^ (2 * s) ≤
      (3 : ℝ) ^ k *
        ∫ β in Set.Icc (fun _ : Fin k => (0 : ℝ)) (fun _ => 1),
          polynomialPartialMajorant k M β ^ (2 * s) := by
  classical
  let g : (Fin k → ℝ) → ℝ := fun β =>
    polynomialPartialMajorant k M β ^ (2 * s)
  let E : Set (Fin k → ℝ) :=
    Set.Icc (fun _ => (-1 : ℝ)) (fun _ => 2)
  let B : (Fin k → Fin 3) → Set (Fin k → ℝ) := shiftedUnitCube
  have hgcont : Continuous g := by
    dsimp [g]
    unfold polynomialPartialMajorant
    exact ((continuous_polynomialSum k M).norm.add
      (continuous_const.mul (continuous_finset_sum _ fun m _ =>
        (continuous_polynomialSum k m).norm))).pow (2 * s)
  have hg0 : ∀ β, 0 ≤ g β := fun β => by
    exact pow_nonneg (polynomialPartialMajorant_nonneg k M β) _
  have hBcompact : ∀ z, IsCompact (B z) := fun z => by
    dsimp [B, shiftedUnitCube]
    exact isCompact_Icc
  have hBint : ∀ z, MeasureTheory.Integrable ((B z).indicator g) := fun z =>
    (hgcont.continuousOn.integrableOn_compact (hBcompact z)).integrable_indicator
      measurableSet_Icc
  have hEcompact : IsCompact E := by
    dsimp [E]
    exact isCompact_Icc
  have hleft : MeasureTheory.Integrable (E.indicator g) :=
    (hgcont.continuousOn.integrableOn_compact hEcompact).integrable_indicator
      measurableSet_Icc
  have hright : MeasureTheory.Integrable
      (fun β => ∑ z : Fin k → Fin 3, (B z).indicator g β) :=
    MeasureTheory.integrable_finset_sum _ fun z _ => hBint z
  have hpoint : ∀ β, E.indicator g β ≤
      ∑ z : Fin k → Fin 3, (B z).indicator g β := by
    intro β
    by_cases hβE : β ∈ E
    · rw [Set.indicator_of_mem hβE]
      obtain ⟨z, hβz⟩ := Set.mem_iUnion.mp
        (enlargedCube_subset_iUnion_shiftedUnitCube k hβE)
      calc
        g β = (B z).indicator g β := by
          exact (Set.indicator_of_mem hβz g).symm
        _ ≤ ∑ w : Fin k → Fin 3, (B w).indicator g β := by
          apply Finset.single_le_sum (s := Finset.univ)
            (f := fun w => (B w).indicator g β)
          · intro w hw
            by_cases hβw : β ∈ B w
            · rw [Set.indicator_of_mem hβw]
              exact hg0 β
            · rw [Set.indicator_of_notMem hβw]
          · exact Finset.mem_univ z
    · simp only [Set.indicator_apply, hβE, if_false]
      apply Finset.sum_nonneg
      intro z hz
      change 0 ≤ (B z).indicator g β
      by_cases hβz : β ∈ B z
      · rw [Set.indicator_of_mem hβz]
        exact hg0 β
      · rw [Set.indicator_of_notMem hβz]
  have hint := MeasureTheory.integral_mono hleft hright hpoint
  rw [MeasureTheory.integral_finset_sum _ (fun z _ => hBint z)] at hint
  have hfold : ∀ z : Fin k → Fin 3,
      ∫ β, (B z).indicator g β =
        ∫ β in Set.Icc (fun _ : Fin k => (0 : ℝ)) (fun _ => 1), g β := by
    intro z
    change (∫ β, (shiftedUnitCube z).indicator g β) = _
    calc
      (∫ β, (shiftedUnitCube z).indicator g β) =
          ∫ β in shiftedUnitCube z, g β :=
        MeasureTheory.integral_indicator measurableSet_Icc
      _ = _ := integral_shiftedUnitCube_majorant_pow z
  calc
    (∫ β in E, g β) = ∫ β, E.indicator g β := by
      rw [MeasureTheory.integral_indicator measurableSet_Icc]
    _ ≤ ∑ z : Fin k → Fin 3, ∫ β, (B z).indicator g β := hint
    _ = (Fintype.card (Fin k → Fin 3) : ℝ) *
        ∫ β in Set.Icc (fun _ : Fin k => (0 : ℝ)) (fun _ => 1), g β := by
      simp_rw [hfold]
      rw [Finset.sum_const, nsmul_eq_mul]
      simp
    _ = (3 : ℝ) ^ k *
        ∫ β in Set.Icc (fun _ : Fin k => (0 : ℝ)) (fun _ => 1), g β := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      norm_cast

/-- Every point of the centered fractional box gives the same logarithmic
block majorant after restoring the integer parts. -/
theorem norm_log_block_le_majorant_of_mem_box
    {k M N n : ℕ} {t u : ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hN : 1 ≤ N) (hn : N ≤ n)
    (ht0 : 0 ≤ t) (hu0 : 0 ≤ u)
    (hscale : t * (M : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1))
    {β : Fin k → ℝ} (hβ : β ∈ coefficientBox k M n t u) :
    ‖∑ m ∈ Finset.Icc 1 M,
        ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((n : ℝ) + u + m))‖ ≤
      polynomialPartialMajorant k M β := by
  let z : Fin k → ℤ := fun j => ⌊logCoefficient t u n j⌋
  have h := norm_log_block_le_polynomialPartialMajorant hk hM hN hn ht0 hu0
    hscale (liftCoefficient t u n β)
      (abs_liftCoefficient_sub_le_radius hβ)
  rw [show liftCoefficient t u n β = fun j => β j + (z j : ℝ) by rfl,
    polynomialPartialMajorant_add_int β z] at h
  exact h

/-- Averaging the pointwise box majorant turns one logarithmic block into a
local moment integral. -/
theorem log_block_pow_mul_volume_le_box_integral
    {s k M N n : ℕ} {t u : ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hN : 1 ≤ N) (hn : N ≤ n)
    (ht0 : 0 ≤ t) (hu0 : 0 ≤ u)
    (hscale : t * (M : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1)) :
    ‖∑ m ∈ Finset.Icc 1 M,
        ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((n : ℝ) + u + m))‖ ^
          (2 * s) *
        (MeasureTheory.volume (coefficientBox k M n t u)).toReal ≤
      ∫ β in coefficientBox k M n t u,
        polynomialPartialMajorant k M β ^ (2 * s) := by
  let L : ℝ := ‖∑ m ∈ Finset.Icc 1 M,
    ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((n : ℝ) + u + m))‖
  have hvolpos := coefficientBox_volume_pos (n := n) (t := t) (u := u) hk hM
  have hvolfin : MeasureTheory.volume (coefficientBox k M n t u) ≠ ⊤ := by
    intro hv
    rw [hv] at hvolpos
    simp at hvolpos
  have hconst : MeasureTheory.IntegrableOn
      (fun _β : Fin k → ℝ => L ^ (2 * s))
      (coefficientBox k M n t u) :=
    MeasureTheory.integrableOn_const hvolfin
  have hmajor : MeasureTheory.IntegrableOn
      (fun β : Fin k → ℝ => polynomialPartialMajorant k M β ^ (2 * s))
      (coefficientBox k M n t u) := by
    have hcompact : IsCompact (coefficientBox k M n t u) := by
      unfold coefficientBox
      exact isCompact_Icc
    have hcontinuous : Continuous
        (fun β : Fin k → ℝ => polynomialPartialMajorant k M β ^ (2 * s)) := by
      unfold polynomialPartialMajorant
      exact ((continuous_polynomialSum k M).norm.add
        (continuous_const.mul (continuous_finset_sum _ fun m _ =>
          (continuous_polynomialSum k m).norm))).pow (2 * s)
    exact hcontinuous.continuousOn.integrableOn_compact hcompact
  have hint := MeasureTheory.setIntegral_mono_on hconst hmajor measurableSet_Icc
    (fun β hβ => pow_le_pow_left₀ (norm_nonneg _)
      (norm_log_block_le_majorant_of_mem_box hk hM hN hn ht0 hu0 hscale hβ)
      (2 * s))
  rw [MeasureTheory.setIntegral_const, smul_eq_mul] at hint
  simpa [L, mul_comm] using hint

/-! ## Top-coefficient separation -/

/-- Quantitative separation of reciprocal powers, in the form needed for
the monotone top coefficient. -/
theorem one_div_pow_sub_one_div_pow_ge {k : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    (1 / a ^ k) - (1 / b ^ k) ≥
      (k : ℝ) * (b - a) / b ^ (k + 1) := by
  let f : ℝ → ℝ := fun x => x ^ (-(k : ℤ))
  let f' : ℝ → ℝ := fun x => -(k : ℝ) / x ^ (k + 1)
  have hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (ha.trans hx.1)
    dsimp [f, f']
    convert hasDerivAt_zpow (-(k : ℤ)) x (Or.inl hx0) using 1
    rw [show -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) by push_cast; omega,
      zpow_neg]
    norm_num [div_eq_mul_inv]
    left
    exact (zpow_natCast x (k + 1)).symm
  have hcont : ContinuousOn f (Set.Icc a b) := by
    dsimp [f]
    apply (continuousOn_zpow₀ (-(k : ℤ))).mono
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt (ha.trans_le hx.1)
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f f' hab hcont hderiv
  have hcpos : 0 < c := ha.trans hc.1
  have hcb : c ≤ b := hc.2.le
  have hpow : c ^ (k + 1) ≤ b ^ (k + 1) :=
    pow_le_pow_left₀ hcpos.le hcb (k + 1)
  have hrecip : 1 / b ^ (k + 1) ≤ 1 / c ^ (k + 1) :=
    one_div_le_one_div_of_le (pow_pos hcpos _) hpow
  have hba : 0 < b - a := sub_pos.mpr hab
  have hslope' : f a - f b = (k : ℝ) * (b - a) / c ^ (k + 1) := by
    have hne : b - a ≠ 0 := ne_of_gt hba
    have hdiff : f' c * (b - a) = f b - f a :=
      (eq_div_iff hne).mp hslope
    rw [show f a - f b = -(f b - f a) by ring, ← hdiff]
    dsimp [f']
    ring
  have hfinal : f a - f b ≥
      (k : ℝ) * (b - a) / b ^ (k + 1) := by
    rw [hslope']
    exact div_le_div_of_nonneg_left
      (mul_nonneg (Nat.cast_nonneg k) hba.le) (pow_pos hcpos _) hpow
  dsimp [f] at hfinal
  rw [zpow_neg, zpow_neg] at hfinal
  simpa [one_div] using hfinal

/-- Index of the highest-degree coefficient. -/
def topIndex (k : ℕ) (hk : 1 ≤ k) : Fin k := ⟨k - 1, by omega⟩

@[simp] theorem topIndex_val_add_one (k : ℕ) (hk : 1 ≤ k) :
    (topIndex k hk : ℕ) + 1 = k := by
  simp [topIndex, Nat.sub_add_cancel hk]

/-- The highest-degree coefficient radius in closed form. -/
theorem two_mul_coefficientRadius_top_eq {k M : ℕ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) :
    2 * coefficientRadius k M (topIndex k hk) =
      1 / (Real.pi * (k : ℝ) ^ 2 * (M : ℝ) ^ k) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  unfold coefficientRadius
  rw [topIndex_val_add_one]
  field_simp [Real.pi_ne_zero, hk0, hM0]

/-- Distinct base points in `[N,2N]` have separated top coefficients. -/
theorem abs_topCoefficient_sub_ge {k N n₁ n₂ : ℕ} {t u : ℝ}
    (hk : 1 ≤ k) (hN : 1 ≤ N) (ht : 0 < t) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hn₁ : N ≤ n₁) (hnlt : n₁ < n₂) (hn₂ : n₂ ≤ 2 * N) :
    |logCoefficient t u n₁ (topIndex k hk) -
        logCoefficient t u n₂ (topIndex k hk)| ≥
      t / (2 * Real.pi * (2 * N + 1 : ℝ) ^ (k + 1)) := by
  let a : ℝ := (n₁ : ℝ) + u
  let b : ℝ := (n₂ : ℝ) + u
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hn₁R : (N : ℝ) ≤ n₁ := by exact_mod_cast hn₁
  have hnltR : (n₁ : ℝ) < n₂ := by exact_mod_cast hnlt
  have hn₂R : (n₂ : ℝ) ≤ 2 * N := by exact_mod_cast hn₂
  have ha : 0 < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a, b]; linarith
  have hb : 0 < b := ha.trans hab
  have hbupper : b ≤ (2 * N + 1 : ℕ) := by
    dsimp [b]
    push_cast
    linarith
  have hrecip := one_div_pow_sub_one_div_pow_ge (k := k) ha hab
  have hrecip0 : 0 ≤ 1 / a ^ k - 1 / b ^ k := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    exact le_trans
      (div_nonneg (mul_nonneg hk0 (sub_nonneg.mpr hab.le))
        (pow_nonneg hb.le _)) hrecip
  have hA : 0 < t / (2 * Real.pi * k) := by positivity
  have hform :
      logCoefficient t u n₁ (topIndex k hk) -
          logCoefficient t u n₂ (topIndex k hk) =
        (-1 : ℝ) ^ k * (t / (2 * Real.pi * k)) *
          (1 / a ^ k - 1 / b ^ k) := by
    unfold logCoefficient
    simp only [topIndex]
    rw [Nat.sub_add_cancel hk]
    dsimp [a, b]
    field_simp
    rw [Nat.cast_sub hk]
    norm_num
    ring
  rw [hform]
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [abs_of_pos hA, abs_of_nonneg hrecip0]
  have hdiff : (1 : ℝ) ≤ b - a := by
    dsimp [a, b]
    have hsucc : ((n₁ + 1 : ℕ) : ℝ) ≤ n₂ := by
      exact_mod_cast (Nat.succ_le_iff.mpr hnlt)
    push_cast at hsucc
    linarith
  have hpow : b ^ (k + 1) ≤ (2 * N + 1 : ℝ) ^ (k + 1) := by
    have hp := pow_le_pow_left₀ hb.le hbupper (k + 1)
    norm_num at hp ⊢
    exact hp
  have hsep :
      (k : ℝ) * (b - a) / b ^ (k + 1) ≥
        (k : ℝ) / (2 * N + 1 : ℝ) ^ (k + 1) := by
    calc
      (k : ℝ) / (2 * N + 1 : ℝ) ^ (k + 1) ≤
          (k : ℝ) / b ^ (k + 1) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg k) (pow_pos hb _)
          hpow
      _ ≤ (k : ℝ) * (b - a) / b ^ (k + 1) := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg hb.le _)
        nlinarith [show (0 : ℝ) < k by exact_mod_cast hk]
  calc
    t / (2 * Real.pi * k) * (1 / a ^ k - 1 / b ^ k) ≥
        t / (2 * Real.pi * k) *
          ((k : ℝ) * (b - a) / b ^ (k + 1)) :=
      mul_le_mul_of_nonneg_left hrecip hA.le
    _ ≥ t / (2 * Real.pi * k) *
          ((k : ℝ) / (2 * N + 1 : ℝ) ^ (k + 1)) :=
      mul_le_mul_of_nonneg_left hsep hA.le
    _ = t / (2 * Real.pi * (2 * N + 1 : ℝ) ^ (k + 1)) := by
      field_simp

/-- Packing bound for a finite separated set in a real interval. -/
theorem card_le_length_div_add_one_of_separated
    (A B d : ℝ) (𝒯 : Finset ℝ) (hd : 0 < d) (hAB : A ≤ B)
    (hrange : ∀ x ∈ 𝒯, A ≤ x ∧ x ≤ B)
    (hsep : ∀ x ∈ 𝒯, ∀ y ∈ 𝒯, x ≠ y → d ≤ |x - y|) :
    (𝒯.card : ℝ) ≤ (B - A) / d + 1 := by
  classical
  let q : ℝ → ℕ := fun x => ⌊(x - A) / d⌋₊
  have hq_nonneg : ∀ x ∈ 𝒯, 0 ≤ (x - A) / d := by
    intro x hx
    exact div_nonneg (sub_nonneg.mpr (hrange x hx).1) hd.le
  have hq_inj : Set.InjOn q (↑𝒯 : Set ℝ) := by
    intro x hx y hy hqxy
    have hxmem : x ∈ 𝒯 := Finset.mem_coe.mp hx
    have hymem : y ∈ 𝒯 := Finset.mem_coe.mp hy
    have hqx : ((q x : ℕ) : ℝ) ≤ (x - A) / d :=
      Nat.floor_le (hq_nonneg x hxmem)
    have hqy : ((q y : ℕ) : ℝ) ≤ (y - A) / d :=
      Nat.floor_le (hq_nonneg y hymem)
    have hxq : (x - A) / d < (q x : ℕ) + 1 := Nat.lt_floor_add_one _
    have hyq : (y - A) / d < (q y : ℕ) + 1 := Nat.lt_floor_add_one _
    have hqR : ((q x : ℕ) : ℝ) = q y := by exact_mod_cast hqxy
    by_contra hxy
    have habs : |x - y| < d := by
      rw [abs_lt]
      constructor
      · have := hyq
        rw [← hqR] at this
        apply (div_lt_iff₀ hd).mp at this
        apply (le_div_iff₀ hd).mp at hqx
        linarith
      · have := hxq
        rw [hqR] at this
        apply (div_lt_iff₀ hd).mp at this
        apply (le_div_iff₀ hd).mp at hqy
        linarith
    exact (not_lt_of_ge (hsep x hxmem y hymem hxy)) habs
  have hcardImage : 𝒯.card = (𝒯.image q).card := by
    exact (Finset.card_image_iff.mpr hq_inj).symm
  have hBA : 0 ≤ (B - A) / d := by
    exact div_nonneg (sub_nonneg.mpr hAB) hd.le
  have himage : 𝒯.image q ⊆ Finset.range (⌊(B - A) / d⌋₊ + 1) := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨x, hx, rfl⟩ := hm
    rw [Finset.mem_range]
    have hxupper := (hrange x hx).2
    have hfloor : q x ≤ ⌊(B - A) / d⌋₊ := by
      dsimp only [q]
      apply Nat.floor_mono
      exact div_le_div_of_nonneg_right (sub_le_sub_right hxupper A) hd.le
    omega
  have hcardNat : 𝒯.card ≤ ⌊(B - A) / d⌋₊ + 1 := by
    rw [hcardImage]
    simpa using Finset.card_le_card himage
  have hfloorR : ((⌊(B - A) / d⌋₊ : ℕ) : ℝ) ≤ (B - A) / d :=
    Nat.floor_le hBA
  have hcardR : (𝒯.card : ℝ) ≤ ((⌊(B - A) / d⌋₊ : ℕ) : ℝ) + 1 := by
    exact_mod_cast hcardNat
  linarith

/-- In Ford's range `t ≤ N^k`, the raw top coefficient has magnitude below
one, so only two integer lifts can occur. -/
theorem abs_topCoefficient_lt_one {k N n : ℕ} {t u : ℝ}
    (hk : 1 ≤ k) (hN : 1 ≤ N) (ht0 : 0 ≤ t) (htN : t ≤ (N : ℝ) ^ k)
    (hu0 : 0 ≤ u) (hn : N ≤ n) :
    |logCoefficient t u n (topIndex k hk)| < 1 := by
  let y : ℝ := (n : ℝ) + u
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hy : 0 < y := by dsimp [y]; linarith
  have hNy : (N : ℝ) ≤ y := by dsimp [y]; linarith
  have hpow : (N : ℝ) ^ k ≤ y ^ k := pow_le_pow_left₀ hNR.le hNy k
  have hcoef : (1 : ℝ) < 2 * Real.pi * k := by
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [Real.pi_gt_three]
  have hden : 0 < 2 * Real.pi * (k : ℝ) * y ^ k := by positivity
  have htden : t < 2 * Real.pi * (k : ℝ) * y ^ k := by
    calc
      t ≤ (N : ℝ) ^ k := htN
      _ ≤ y ^ k := hpow
      _ < 2 * Real.pi * (k : ℝ) * y ^ k := by
        nlinarith [pow_pos hy k]
  have hform : |logCoefficient t u n (topIndex k hk)| =
      t / (2 * Real.pi * (k : ℝ) * y ^ k) := by
    unfold logCoefficient
    simp only [topIndex]
    rw [Nat.sub_add_cancel hk]
    dsimp [y]
    rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg ht0]
    rw [Nat.cast_sub hk]
    norm_num
    rw [abs_of_pos Real.pi_pos,
      abs_of_pos (show (0 : ℝ) < (n : ℝ) + u by simpa [y] using hy)]
  rw [hform]
  exact (div_lt_one hden).2 htden

theorem floor_topCoefficient_eq_neg_one_or_zero {k N n : ℕ} {t u : ℝ}
    (hk : 1 ≤ k) (hN : 1 ≤ N) (ht0 : 0 ≤ t) (htN : t ≤ (N : ℝ) ^ k)
    (hu0 : 0 ≤ u) (hn : N ≤ n) :
    ⌊logCoefficient t u n (topIndex k hk)⌋ = (-1 : ℤ) ∨
      ⌊logCoefficient t u n (topIndex k hk)⌋ = 0 := by
  let γ := logCoefficient t u n (topIndex k hk)
  have habs := abs_topCoefficient_lt_one hk hN ht0 htN hu0 hn
  change |γ| < 1 at habs
  rw [abs_lt] at habs
  by_cases hγ : 0 ≤ γ
  · right
    apply Int.floor_eq_iff.mpr
    norm_num
    exact ⟨hγ, habs.2⟩
  · left
    apply Int.floor_eq_iff.mpr
    norm_num
    exact ⟨habs.1.le, lt_of_not_ge hγ⟩

/-- Base points whose centered coefficient box contains `β`, split by the
integer lift of the top coefficient. -/
noncomputable def coefficientOverlapLift (k M N : ℕ) (t u : ℝ)
    (hk : 1 ≤ k) (β : Fin k → ℝ) (z : ℤ) : Finset ℕ :=
  let p := fun n => β ∈ coefficientBox k M n t u ∧
    ⌊logCoefficient t u n (topIndex k hk)⌋ = z
  @Finset.filter ℕ p (Classical.decPred p) (Finset.Icc N (2 * N))

noncomputable def coefficientOverlap (k M N : ℕ) (t u : ℝ)
    (β : Fin k → ℝ) : Finset ℕ :=
  let p := fun n => β ∈ coefficientBox k M n t u
  @Finset.filter ℕ p (Classical.decPred p) (Finset.Icc N (2 * N))

/-- One fixed integer lift of the top coefficient has the elementary packing
bound `2r/d+1`. -/
theorem card_coefficientOverlapLift_le {k M N : ℕ} {t u : ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hN : 1 ≤ N) (ht : 0 < t)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (β : Fin k → ℝ) (z : ℤ) :
    ((coefficientOverlapLift k M N t u hk β z).card : ℝ) ≤
      2 * coefficientRadius k M (topIndex k hk) /
          (t / (2 * Real.pi * (2 * N + 1 : ℝ) ^ (k + 1))) + 1 := by
  classical
  let γ : ℕ → ℝ := fun n => logCoefficient t u n (topIndex k hk)
  let r := coefficientRadius k M (topIndex k hk)
  let d := t / (2 * Real.pi * (2 * N + 1 : ℝ) ^ (k + 1))
  let 𝒩 := coefficientOverlapLift k M N t u hk β z
  have hd : 0 < d := by dsimp [d]; positivity
  have hγinj : Set.InjOn γ (↑𝒩 : Set ℕ) := by
    intro n hn m hm heq
    have hnmem : n ∈ 𝒩 := Finset.mem_coe.mp hn
    have hmmem : m ∈ 𝒩 := Finset.mem_coe.mp hm
    simp only [𝒩, coefficientOverlapLift, Finset.mem_filter] at hnmem hmmem
    have hnrange : n ∈ Finset.Icc N (2 * N) :=
      hnmem.1
    have hmrange : m ∈ Finset.Icc N (2 * N) :=
      hmmem.1
    have hnrange' : N ≤ n ∧ n ≤ 2 * N := by simpa using hnrange
    have hmrange' : N ≤ m ∧ m ≤ 2 * N := by simpa using hmrange
    by_contra hne
    rcases lt_or_gt_of_ne hne with hnm | hmn
    · have hsep := abs_topCoefficient_sub_ge hk hN ht hu0 hu1
        hnrange'.1 hnm hmrange'.2
      change d ≤ |γ n - γ m| at hsep
      rw [heq, sub_self, abs_zero] at hsep
      exact (not_lt_of_ge hsep) hd
    · have hsep := abs_topCoefficient_sub_ge hk hN ht hu0 hu1
        hmrange'.1 hmn hnrange'.2
      change d ≤ |γ m - γ n| at hsep
      rw [heq, sub_self, abs_zero] at hsep
      exact (not_lt_of_ge hsep) hd
  let 𝒯 : Finset ℝ := 𝒩.image γ
  have hcard : 𝒩.card = 𝒯.card := by
    exact (Finset.card_image_iff.mpr hγinj).symm
  have hrange : ∀ x ∈ 𝒯,
      β (topIndex k hk) - r + z ≤ x ∧
        x ≤ β (topIndex k hk) + r + z := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨n, hn, rfl⟩ := hx
    simp only [𝒩, coefficientOverlapLift, Finset.mem_filter] at hn
    have hnfilter := hn.2
    have hnbox := hnfilter.1
    have hnfloor := hnfilter.2
    have hlow := hnbox.1 (topIndex k hk)
    have hupp := hnbox.2 (topIndex k hk)
    have hfract := Int.fract_add_floor (γ n)
    change ⌊γ n⌋ = z at hnfloor
    change fractionalLogCoefficient t u n (topIndex k hk) - r ≤
      β (topIndex k hk) at hlow
    change β (topIndex k hk) ≤
      fractionalLogCoefficient t u n (topIndex k hk) + r at hupp
    unfold fractionalLogCoefficient at hlow hupp
    rw [hnfloor] at hfract
    constructor <;> linarith
  have hsep : ∀ x ∈ 𝒯, ∀ y ∈ 𝒯, x ≠ y → d ≤ |x - y| := by
    intro x hx y hy hxy
    rw [Finset.mem_image] at hx hy
    obtain ⟨n, hn, rfl⟩ := hx
    obtain ⟨m, hm, rfl⟩ := hy
    simp only [𝒩, coefficientOverlapLift, Finset.mem_filter] at hn hm
    have hnrange := hn.1
    have hmrange := hm.1
    have hnrange' : N ≤ n ∧ n ≤ 2 * N := by simpa using hnrange
    have hmrange' : N ≤ m ∧ m ≤ 2 * N := by simpa using hmrange
    have hne : n ≠ m := fun h => hxy (by subst m; rfl)
    rcases lt_or_gt_of_ne hne with hnm | hmn
    · exact abs_topCoefficient_sub_ge hk hN ht hu0 hu1
        hnrange'.1 hnm hmrange'.2
    · simpa [abs_sub_comm] using abs_topCoefficient_sub_ge hk hN ht hu0 hu1
        hmrange'.1 hmn hnrange'.2
  have hpack := card_le_length_div_add_one_of_separated
    (β (topIndex k hk) - r + z) (β (topIndex k hk) + r + z)
      d 𝒯 hd (by linarith [coefficientRadius_pos hk hM (topIndex k hk)])
      hrange hsep
  rw [← hcard] at hpack
  dsimp [𝒩, r, d] at hpack ⊢
  ring_nf at hpack ⊢
  exact hpack

/-- Exact multiplicity bound for the centered boxes.  The factor `2` is the
two possible integer lifts of a top coefficient of magnitude below one. -/
theorem card_coefficientOverlap_le {k M N : ℕ} {t u : ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hN : 1 ≤ N) (ht : 0 < t)
    (htN : t ≤ (N : ℝ) ^ k) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (β : Fin k → ℝ) :
    ((coefficientOverlap k M N t u β).card : ℝ) ≤
      2 * (2 * coefficientRadius k M (topIndex k hk) /
          (t / (2 * Real.pi * (2 * N + 1 : ℝ) ^ (k + 1))) + 1) := by
  classical
  let 𝒩 := coefficientOverlap k M N t u β
  let 𝒩neg := coefficientOverlapLift k M N t u hk β (-1)
  let 𝒩zero := coefficientOverlapLift k M N t u hk β 0
  have hsub : 𝒩 ⊆ 𝒩neg ∪ 𝒩zero := by
    intro n hn
    simp only [𝒩, coefficientOverlap, Finset.mem_filter] at hn
    have hnrange : N ≤ n ∧ n ≤ 2 * N := by simpa using hn.1
    have hfloor := floor_topCoefficient_eq_neg_one_or_zero hk hN ht.le htN hu0
      hnrange.1
    rw [Finset.mem_union]
    rcases hfloor with hfloor | hfloor
    · left
      simp only [𝒩neg, coefficientOverlapLift, Finset.mem_filter]
      exact ⟨hn.1, hn.2, hfloor⟩
    · right
      simp only [𝒩zero, coefficientOverlapLift, Finset.mem_filter]
      exact ⟨hn.1, hn.2, hfloor⟩
  have hcardSub : 𝒩.card ≤ (𝒩neg ∪ 𝒩zero).card := Finset.card_le_card hsub
  have hunion : (𝒩neg ∪ 𝒩zero).card ≤ 𝒩neg.card + 𝒩zero.card :=
    Finset.card_union_le 𝒩neg 𝒩zero
  have hneg := card_coefficientOverlapLift_le hk hM hN ht hu0 hu1 β (-1)
  have hzero := card_coefficientOverlapLift_le hk hM hN ht hu0 hu1 β 0
  have hcardSubR : (𝒩.card : ℝ) ≤ ((𝒩neg ∪ 𝒩zero).card : ℝ) := by
    exact_mod_cast hcardSub
  have hunionR : ((𝒩neg ∪ 𝒩zero).card : ℝ) ≤
      (𝒩neg.card : ℝ) + 𝒩zero.card := by
    exact_mod_cast hunion
  calc
    ((coefficientOverlap k M N t u β).card : ℝ) = (𝒩.card : ℝ) := rfl
    _ ≤ ((𝒩neg ∪ 𝒩zero).card : ℝ) := hcardSubR
    _ ≤ (𝒩neg.card : ℝ) + 𝒩zero.card := hunionR
    _ ≤ 2 * (2 * coefficientRadius k M (topIndex k hk) /
          (t / (2 * Real.pi * (2 * N + 1 : ℝ) ^ (k + 1))) + 1) := by
      linarith

/-- Summing local box integrals costs only the maximal overlap multiplicity.
All centered boxes lie in the enlarged cube `[-1,2]^k`. -/
theorem sum_box_integrals_le_multiplicity {s k M N : ℕ} {t u : ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hN : 1 ≤ N) (ht : 0 < t)
    (htN : t ≤ (N : ℝ) ^ k) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∑ n ∈ Finset.Icc N (2 * N),
        ∫ β in coefficientBox k M n t u,
          polynomialPartialMajorant k M β ^ (2 * s)) ≤
      2 * (2 * coefficientRadius k M (topIndex k hk) /
          (t / (2 * Real.pi * (2 * N + 1 : ℝ) ^ (k + 1))) + 1) *
        ∫ β in Set.Icc (fun _ : Fin k => (-1 : ℝ)) (fun _ => 2),
          polynomialPartialMajorant k M β ^ (2 * s) := by
  classical
  let g : (Fin k → ℝ) → ℝ := fun β =>
    polynomialPartialMajorant k M β ^ (2 * s)
  let E : Set (Fin k → ℝ) := Set.Icc (fun _ => (-1 : ℝ)) (fun _ => 2)
  let W : ℝ := 2 * (2 * coefficientRadius k M (topIndex k hk) /
    (t / (2 * Real.pi * (2 * N + 1 : ℝ) ^ (k + 1))) + 1)
  have hgcont : Continuous g := by
    dsimp [g]
    unfold polynomialPartialMajorant
    exact ((continuous_polynomialSum k M).norm.add
      (continuous_const.mul (continuous_finset_sum _ fun m _ =>
        (continuous_polynomialSum k m).norm))).pow (2 * s)
  have hg0 : ∀ β, 0 ≤ g β := fun β => by
    exact pow_nonneg (polynomialPartialMajorant_nonneg k M β) _
  have hfi : ∀ n ∈ Finset.Icc N (2 * N), MeasureTheory.Integrable
      ((coefficientBox k M n t u).indicator g) := by
    intro n hn
    have hcompact : IsCompact (coefficientBox k M n t u) := by
      unfold coefficientBox
      exact isCompact_Icc
    exact (hgcont.continuousOn.integrableOn_compact hcompact).integrable_indicator
      measurableSet_Icc
  have hEcompact : IsCompact E := by
    dsimp [E]
    exact isCompact_Icc
  have hright : MeasureTheory.Integrable (E.indicator fun β => W * g β) := by
    exact ((continuous_const.mul hgcont).continuousOn.integrableOn_compact hEcompact)
      |>.integrable_indicator measurableSet_Icc
  have hleft : MeasureTheory.Integrable
      (fun β => ∑ n ∈ Finset.Icc N (2 * N),
        (coefficientBox k M n t u).indicator g β) :=
    MeasureTheory.integrable_finset_sum _ hfi
  have hpoint : ∀ β,
      (∑ n ∈ Finset.Icc N (2 * N),
          (coefficientBox k M n t u).indicator g β) ≤
        E.indicator (fun β => W * g β) β := by
    intro β
    by_cases hβE : β ∈ E
    · rw [Set.indicator_of_mem hβE]
      have hsum :
          (∑ n ∈ Finset.Icc N (2 * N),
              (coefficientBox k M n t u).indicator g β) =
            ((coefficientOverlap k M N t u β).card : ℝ) * g β := by
        simp only [Set.indicator_apply]
        rw [← Finset.sum_filter]
        change (∑ _n ∈ coefficientOverlap k M N t u β, g β) = _
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [hsum]
      exact mul_le_mul_of_nonneg_right
        (card_coefficientOverlap_le hk hM hN ht htN hu0 hu1 β) (hg0 β)
    · simp only [Set.indicator_apply, hβE, if_false]
      have hz : (∑ n ∈ Finset.Icc N (2 * N),
          if β ∈ coefficientBox k M n t u then g β else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        rw [if_neg]
        intro hβbox
        exact hβE (coefficientBox_subset_enlargedCube hk hM hβbox)
      rw [hz]
  have hint := MeasureTheory.integral_mono hleft hright hpoint
  rw [MeasureTheory.integral_finset_sum _ hfi] at hint
  calc
    (∑ n ∈ Finset.Icc N (2 * N),
        ∫ β in coefficientBox k M n t u,
          polynomialPartialMajorant k M β ^ (2 * s)) =
        ∑ n ∈ Finset.Icc N (2 * N),
          ∫ β, (coefficientBox k M n t u).indicator g β := by
      apply Finset.sum_congr rfl
      intro n hn
      symm
      exact MeasureTheory.integral_indicator measurableSet_Icc
    _ ≤ ∫ β, E.indicator (fun β => W * g β) β := hint
    _ = ∫ β in E, W * g β :=
      MeasureTheory.integral_indicator measurableSet_Icc
    _ = W * ∫ β in E, g β := MeasureTheory.integral_const_mul W g
    _ = _ := by rfl

/-- Ford's frequency-box reduction before folding the enlarged cube back to
the unit torus. -/
theorem sum_log_blocks_pow_mul_volume_le {s k M N : ℕ} {t u : ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hN : 1 ≤ N) (ht : 0 < t)
    (htN : t ≤ (N : ℝ) ^ k) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hscale : t * (M : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1)) :
    (∑ n ∈ Finset.Icc N (2 * N),
        ‖∑ m ∈ Finset.Icc 1 M,
          ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((n : ℝ) + u + m))‖ ^
            (2 * s) *
          (MeasureTheory.volume (coefficientBox k M n t u)).toReal) ≤
      2 * (2 * coefficientRadius k M (topIndex k hk) /
          (t / (2 * Real.pi * (2 * N + 1 : ℝ) ^ (k + 1))) + 1) *
        ∫ β in Set.Icc (fun _ : Fin k => (-1 : ℝ)) (fun _ => 2),
          polynomialPartialMajorant k M β ^ (2 * s) := by
  calc
    (∑ n ∈ Finset.Icc N (2 * N),
        ‖∑ m ∈ Finset.Icc 1 M,
          ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((n : ℝ) + u + m))‖ ^
            (2 * s) *
          (MeasureTheory.volume (coefficientBox k M n t u)).toReal) ≤
      ∑ n ∈ Finset.Icc N (2 * N),
        ∫ β in coefficientBox k M n t u,
          polynomialPartialMajorant k M β ^ (2 * s) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' : N ≤ n := by simpa using (Finset.mem_Icc.mp hn).1
      exact log_block_pow_mul_volume_le_box_integral hk hM hN hn' ht.le hu0 hscale
    _ ≤ _ := sum_box_integrals_le_multiplicity hk hM hN ht htN hu0 hu1

/-- Ford's frequency-box reduction on the unit coefficient torus.  The
centered cube has exactly three possible unit periods in every coordinate,
so folding costs `3^k`. -/
theorem sum_log_blocks_pow_mul_volume_le_unitCube
    {s k M N : ℕ} {t u : ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hN : 1 ≤ N) (ht : 0 < t)
    (htN : t ≤ (N : ℝ) ^ k) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hscale : t * (M : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1)) :
    (∑ n ∈ Finset.Icc N (2 * N),
        ‖∑ m ∈ Finset.Icc 1 M,
          ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((n : ℝ) + u + m))‖ ^
            (2 * s) *
          (MeasureTheory.volume (coefficientBox k M n t u)).toReal) ≤
      2 * (2 * coefficientRadius k M (topIndex k hk) /
          (t / (2 * Real.pi * (2 * N + 1 : ℝ) ^ (k + 1))) + 1) *
        (3 : ℝ) ^ k *
          ∫ β in Set.Icc (fun _ : Fin k => (0 : ℝ)) (fun _ => 1),
            polynomialPartialMajorant k M β ^ (2 * s) := by
  have hfold := integral_enlargedCube_majorant_pow_le (s := s) (k := k) (M := M)
  calc
    (∑ n ∈ Finset.Icc N (2 * N),
        ‖∑ m ∈ Finset.Icc 1 M,
          ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((n : ℝ) + u + m))‖ ^
            (2 * s) *
          (MeasureTheory.volume (coefficientBox k M n t u)).toReal) ≤
      2 * (2 * coefficientRadius k M (topIndex k hk) /
          (t / (2 * Real.pi * (2 * N + 1 : ℝ) ^ (k + 1))) + 1) *
        ∫ β in Set.Icc (fun _ : Fin k => (-1 : ℝ)) (fun _ => 2),
          polynomialPartialMajorant k M β ^ (2 * s) :=
      sum_log_blocks_pow_mul_volume_le hk hM hN ht htN hu0 hu1 hscale
    _ ≤ 2 * (2 * coefficientRadius k M (topIndex k hk) /
          (t / (2 * Real.pi * (2 * N + 1 : ℝ) ^ (k + 1))) + 1) *
        ((3 : ℝ) ^ k *
          ∫ β in Set.Icc (fun _ : Fin k => (0 : ℝ)) (fun _ => 1),
            polynomialPartialMajorant k M β ^ (2 * s)) := by
      apply mul_le_mul_of_nonneg_left hfold
      have hrpos := coefficientRadius_pos hk hM (topIndex k hk)
      positivity
    _ = _ := by ring

/-! ## Long-interval assembly -/

/-- The folded box estimate after inserting the explicit weak VMVT
constant.  This is the moment input for the shift/Hölder assembly. -/
theorem sum_log_blocks_pow_mul_volume_le_meanValue
    {k τ M N : ℕ} {t u : ℝ}
    (hk : 2 ≤ k) (hτ : 1 ≤ τ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (ht : 0 < t) (htN : t ≤ (N : ℝ) ^ k)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hscale : t * (M : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1)) :
    (∑ n ∈ Finset.Icc N (2 * N),
        ‖∑ m ∈ Finset.Icc 1 M,
          ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((n : ℝ) + u + m))‖ ^
            (2 * (k * τ)) *
          (MeasureTheory.volume (coefficientBox k M n t u)).toReal) ≤
      2 * (2 * coefficientRadius k M (topIndex k (by omega)) /
          (t / (2 * Real.pi * (2 * N + 1 : ℝ) ^ (k + 1))) + 1) *
        (3 : ℝ) ^ k * (2 : ℝ) ^ (4 * (k * τ)) *
          vinogradovMeanValueConstant k τ *
            (M : ℝ) ^ vinogradovExponent k τ := by
  let W : ℝ := 2 * (2 * coefficientRadius k M (topIndex k (by omega)) /
    (t / (2 * Real.pi * (2 * N + 1 : ℝ) ^ (k + 1))) + 1)
  have hW0 : 0 ≤ W := by
    dsimp [W]
    have hr := coefficientRadius_pos (by omega : 1 ≤ k) hM
      (topIndex k (by omega))
    positivity
  have hfold := sum_log_blocks_pow_mul_volume_le_unitCube
    (s := k * τ) (k := k) (M := M) (N := N) (t := t) (u := u)
    (by omega) hM hN ht htN hu0 hu1 hscale
  have hint := integral_polynomialPartialMajorant_pow_le
    (k * τ) k M hM (by
      have : 0 < k * τ := Nat.mul_pos (by omega) (by omega)
      omega)
  have hint' :
      (∫ β in Set.Icc (fun _ : Fin k => (0 : ℝ)) (fun _ => 1),
          polynomialPartialMajorant k M β ^ (2 * (k * τ))) ≤
        (2 : ℝ) ^ (4 * (k * τ)) * (vinogradovJ (k * τ) k M : ℝ) := by
    rw [unitCubeMeasure_eq_restrict_Icc] at hint
    exact hint
  have hvmv := (vinogradovMeanValueConstant_spec hk hτ).2 M hM
  calc
    (∑ n ∈ Finset.Icc N (2 * N),
        ‖∑ m ∈ Finset.Icc 1 M,
          ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((n : ℝ) + u + m))‖ ^
            (2 * (k * τ)) *
          (MeasureTheory.volume (coefficientBox k M n t u)).toReal) ≤
      W * (3 : ℝ) ^ k *
        ∫ β in Set.Icc (fun _ : Fin k => (0 : ℝ)) (fun _ => 1),
          polynomialPartialMajorant k M β ^ (2 * (k * τ)) := by
        simpa only [W] using hfold
    _ ≤ W * (3 : ℝ) ^ k *
        ((2 : ℝ) ^ (4 * (k * τ)) * (vinogradovJ (k * τ) k M : ℝ)) := by
      apply mul_le_mul_of_nonneg_left hint'
      exact mul_nonneg hW0 (by positivity)
    _ ≤ W * (3 : ℝ) ^ k *
        ((2 : ℝ) ^ (4 * (k * τ)) *
          (vinogradovMeanValueConstant k τ *
            (M : ℝ) ^ vinogradovExponent k τ)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hW0 (by positivity))
      exact mul_le_mul_of_nonneg_left hvmv (by positivity)
    _ = _ := by
      dsimp [W]
      ring

/-- The explicit moment factor in the long-interval assembly. -/
noncomputable def vinogradovWeylMomentFactor
    (k τ M N : ℕ) (t : ℝ) (hk : 1 ≤ k) : ℝ :=
  2 * (2 * coefficientRadius k M (topIndex k hk) /
      (t / (2 * Real.pi * (2 * N + 1 : ℝ) ^ (k + 1))) + 1) *
    (3 : ℝ) ^ k * (2 : ℝ) ^ (4 * (k * τ)) *
      vinogradovMeanValueConstant k τ *
        (M : ℝ) ^ vinogradovExponent k τ

/-- All dimensionless constants in the assembled Vinogradov moment.  The
remaining scale factor is `M^(2*k*τ+δ)/N`. -/
noncomputable def vinogradovWeylPrefactor
    (k τ M N : ℕ) (t : ℝ) : ℝ :=
  2 * (2 * (2 * N + 1 : ℝ) ^ (k + 1) /
        ((k : ℝ) ^ 2 * t * (M : ℝ) ^ k) + 1) *
    (3 : ℝ) ^ k * (2 : ℝ) ^ (4 * (k * τ)) *
      vinogradovMeanValueConstant k τ *
        (Real.pi * (k : ℝ) ^ 2) ^ k

private theorem vinogradovMultiplicityFactor_eq
    {k M N : ℕ} {t : ℝ} (hk : 1 ≤ k) (hM : 1 ≤ M) (ht : 0 < t) :
    2 * (2 * coefficientRadius k M (topIndex k hk) /
          (t / (2 * Real.pi * (2 * N + 1 : ℝ) ^ (k + 1))) + 1) =
      2 * (2 * (2 * N + 1 : ℝ) ^ (k + 1) /
          ((k : ℝ) ^ 2 * t * (M : ℝ) ^ k) + 1) := by
  rw [two_mul_coefficientRadius_top_eq hk hM]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hX0 : (2 * N + 1 : ℝ) ≠ 0 := by positivity
  field_simp [Real.pi_ne_zero, hk0, hM0, ht.ne']

/-- Dividing by the coefficient-box volume cancels the triangular VMVT
degree loss.  This is the exact algebra behind the main term in V-C2-9. -/
theorem vinogradovWeylMomentFactor_div_volume
    {k τ M N : ℕ} {t : ℝ}
    (hk : 2 ≤ k) (hM : 1 ≤ M) (ht : 0 < t) :
    vinogradovWeylMomentFactor k τ M N t (by omega) /
        coefficientBoxVolume k M =
      vinogradovWeylPrefactor k τ M N t *
        (M : ℝ) ^ (2 * (k : ℝ) * τ + vinogradovDelta k τ) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hB : 0 < Real.pi * (k : ℝ) ^ 2 := by positivity
  rw [vinogradovWeylMomentFactor, coefficientBoxVolume_eq (by omega) hM,
    vinogradovMultiplicityFactor_eq (by omega) hM ht]
  unfold vinogradovWeylPrefactor vinogradovExponent
  rw [one_div_pow, one_div_pow]
  field_simp
  rw [mul_assoc]
  rw [← Real.rpow_natCast (M : ℝ) (k * (k + 1) / 2),
    ← Real.rpow_add hMR]
  congr 1
  rw [Nat.cast_div (even_iff_two_dvd.mp (Nat.even_mul_succ_self k))
    (by norm_num)]
  push_cast
  ring_nf

private theorem shiftHolder_scale_identity {A M N : ℝ} {s : ℕ}
    (hA : 0 ≤ A) (hM : 0 < M) (hN : 0 < N) (hs : 1 ≤ s) :
    (1 / M) * N ^ (1 - ((2 * s : ℕ) : ℝ)⁻¹) *
        (A * M ^ ((2 * s : ℕ) : ℝ)) ^ (((2 * s : ℕ) : ℝ)⁻¹) =
      N * (A / N) ^ (((2 * s : ℕ) : ℝ)⁻¹) := by
  let r : ℝ := ((2 * s : ℕ) : ℝ)⁻¹
  have h2s : (((2 * s : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (show 2 * s ≠ 0 by omega)
  have hr : ((2 * s : ℕ) : ℝ) * r = 1 := by
    dsimp [r]
    field_simp
  rw [Real.mul_rpow hA (Real.rpow_nonneg hM.le _)]
  rw [← Real.rpow_mul hM.le, hr, Real.rpow_one]
  rw [Real.div_rpow hA hN.le]
  rw [Real.rpow_sub hN, Real.rpow_one]
  field_simp

/-- Shift averaging, Hölder, the folded coefficient boxes, and the weak
VMVT assembled on one dyadic interval.  The sole remaining operation for a
parameter choice is to bound the displayed explicit factor. -/
theorem norm_log_sum_le_vinogradovAssembly
    {k τ M N R : ℕ} {t u : ℝ}
    (hk : 2 ≤ k) (hτ : 1 ≤ τ) (hM : 1 ≤ M) (hMN : M ≤ N)
    (hNR : N < R) (hR : R ≤ 2 * N)
    (ht : 0 < t) (htN : t ≤ (N : ℝ) ^ k)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hscale : t * (M : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1)) :
    ‖∑ q ∈ Finset.Ioc N R,
        ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((q : ℝ) + u))‖ ≤
      (1 / (M : ℝ)) *
        ((Finset.Ioc N (R - 1)).card : ℝ) ^
          (1 - ((2 * (k * τ) : ℕ) : ℝ)⁻¹) *
        (vinogradovWeylMomentFactor k τ M N t (by omega) /
          coefficientBoxVolume k M) ^
            (((2 * (k * τ) : ℕ) : ℝ)⁻¹) +
      2 * M := by
  let s := k * τ
  let A := Finset.Ioc N (R - 1)
  let F : ℕ → ℂ := fun n =>
    ∑ m ∈ Finset.Icc 1 M,
      ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((n : ℝ) + u + m))
  let V := coefficientBoxVolume k M
  let K := vinogradovWeylMomentFactor k τ M N t (by omega)
  have hN : 1 ≤ N := hM.trans hMN
  have hV : 0 < V := coefficientBoxVolume_pos (by omega) hM
  have hmean := sum_log_blocks_pow_mul_volume_le_meanValue
    hk hτ hM hN ht htN hu0 hu1 hscale
  have hmean' :
      (∑ n ∈ Finset.Icc N (2 * N), ‖F n‖ ^ (2 * s)) * V ≤ K := by
    dsimp only [F, V, K, s]
    simp_rw [coefficientBox_volume_eq_common (by omega : 1 ≤ k) hM] at hmean
    rw [Finset.sum_mul]
    simpa only [vinogradovWeylMomentFactor] using hmean
  have hfull : (∑ n ∈ Finset.Icc N (2 * N), ‖F n‖ ^ (2 * s)) ≤ K / V := by
    rw [le_div_iff₀ hV]
    simpa [mul_comm] using hmean'
  have hsubset : A ⊆ Finset.Icc N (2 * N) := by
    intro n hn
    change n ∈ Finset.Ioc N (R - 1) at hn
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_Icc]
    omega
  have hmoment : (∑ n ∈ A, ‖F n‖ ^ (2 * s)) ≤ K / V := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ => pow_nonneg (norm_nonneg _) _)).trans hfull
  have hs : 1 ≤ s := by
    have : 0 < k * τ := Nat.mul_pos (by omega) (by omega)
    simpa only [s] using this
  have hholder := sum_norm_le_holder A F s hs
  have hroot : (∑ n ∈ A, ‖F n‖ ^ (2 * s)) ^ (((2 * s : ℕ) : ℝ)⁻¹) ≤
      (K / V) ^ (((2 * s : ℕ) : ℝ)⁻¹) := by
    apply Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _)
      hmoment
    positivity
  have hsumNorm : (∑ n ∈ A, ‖F n‖) ≤
      (A.card : ℝ) ^ (1 - ((2 * s : ℕ) : ℝ)⁻¹) *
        (K / V) ^ (((2 * s : ℕ) : ℝ)⁻¹) :=
    hholder.trans (mul_le_mul_of_nonneg_left hroot (by positivity))
  let f : ℕ → ℂ := fun q =>
    ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((q : ℝ) + u))
  have hf : ∀ q, ‖f q‖ ≤ 1 := by
    intro q
    dsimp [f]
    rw [ExpSums.norm_e]
  have hshift := norm_sum_le_shift_average f hNR hM hMN hf
  have houter :
      ‖∑ n ∈ A, F n‖ ≤ ∑ n ∈ A, ‖F n‖ := norm_sum_le _ _
  calc
    ‖∑ q ∈ Finset.Ioc N R,
        ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((q : ℝ) + u))‖ =
      ‖∑ q ∈ Finset.Ioc N R, f q‖ := rfl
    _ ≤ (1 / (M : ℝ)) * ‖∑ n ∈ A, F n‖ + 2 * M := by
      simpa only [f, F, A, Nat.cast_ofNat, Nat.cast_add, add_assoc,
        add_left_comm, add_comm] using hshift
    _ ≤ (1 / (M : ℝ)) * (∑ n ∈ A, ‖F n‖) + 2 * M := by
      gcongr
    _ ≤ (1 / (M : ℝ)) *
        ((A.card : ℝ) ^ (1 - ((2 * s : ℕ) : ℝ)⁻¹) *
          (K / V) ^ (((2 * s : ℕ) : ℝ)⁻¹)) + 2 * M := by
      gcongr
    _ = _ := by
      dsimp only [A, s, K, V]
      ring

/-- V-C2-9 in normalized main-term form.  The first summand is `N` times
the `2kτ`-th root of the explicit dimensionless factor; the second is the
endpoint-collar cost from shift averaging. -/
theorem norm_log_sum_le_vinogradovMainTerm
    {k τ M N R : ℕ} {t u : ℝ}
    (hk : 2 ≤ k) (hτ : 1 ≤ τ) (hM : 1 ≤ M) (hMN : M ≤ N)
    (hNR : N < R) (hR : R ≤ 2 * N)
    (ht : 0 < t) (htN : t ≤ (N : ℝ) ^ k)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hscale : t * (M : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1)) :
    ‖∑ q ∈ Finset.Ioc N R,
        ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((q : ℝ) + u))‖ ≤
      (N : ℝ) *
        (vinogradovWeylPrefactor k τ M N t *
            (M : ℝ) ^ vinogradovDelta k τ / (N : ℝ)) ^
          (((2 * (k * τ) : ℕ) : ℝ)⁻¹) +
      2 * M := by
  let s := k * τ
  let A : ℝ := vinogradovWeylPrefactor k τ M N t *
    (M : ℝ) ^ vinogradovDelta k τ
  have hs : 1 ≤ s := by
    dsimp [s]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hNnat : 1 ≤ N := hM.trans hMN
  have hNR' : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hMR : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hC := (vinogradovMeanValueConstant_spec hk hτ).1
  have hA : 0 ≤ A := by
    dsimp [A, vinogradovWeylPrefactor]
    positivity
  have hr0 : 0 ≤ (((2 * s : ℕ) : ℝ)⁻¹) := by positivity
  have hr1 : (((2 * s : ℕ) : ℝ)⁻¹) ≤ 1 := by
    rw [inv_le_one₀]
    exact_mod_cast (show 1 ≤ 2 * s by omega)
    exact_mod_cast (show 0 < 2 * s by omega)
  have hp : 0 ≤ 1 - (((2 * s : ℕ) : ℝ)⁻¹) := sub_nonneg.mpr hr1
  have hcardNat : (Finset.Ioc N (R - 1)).card ≤ N := by
    simp only [Nat.card_Ioc]
    omega
  have hcard : ((Finset.Ioc N (R - 1)).card : ℝ) ≤ N := by
    exact_mod_cast hcardNat
  have hbase := norm_log_sum_le_vinogradovAssembly hk hτ hM hMN hNR hR
    ht htN hu0 hu1 hscale
  have hmoment :
      vinogradovWeylMomentFactor k τ M N t (by omega) /
          coefficientBoxVolume k M =
        A * (M : ℝ) ^ ((2 * s : ℕ) : ℝ) := by
    rw [vinogradovWeylMomentFactor_div_volume hk hM ht]
    dsimp only [A, s]
    have hexp : 2 * (k : ℝ) * τ + vinogradovDelta k τ =
        vinogradovDelta k τ + ((2 * (k * τ) : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hexp, Real.rpow_add hMR]
    ring
  calc
    ‖∑ q ∈ Finset.Ioc N R,
        ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((q : ℝ) + u))‖ ≤
      (1 / (M : ℝ)) *
        ((Finset.Ioc N (R - 1)).card : ℝ) ^
          (1 - ((2 * s : ℕ) : ℝ)⁻¹) *
        (vinogradovWeylMomentFactor k τ M N t (by omega) /
          coefficientBoxVolume k M) ^ (((2 * s : ℕ) : ℝ)⁻¹) +
        2 * M := by simpa only [s] using hbase
    _ ≤ (1 / (M : ℝ)) *
        (N : ℝ) ^ (1 - ((2 * s : ℕ) : ℝ)⁻¹) *
        (vinogradovWeylMomentFactor k τ M N t (by omega) /
          coefficientBoxVolume k M) ^ (((2 * s : ℕ) : ℝ)⁻¹) +
        2 * M := by
      have hpow := Real.rpow_le_rpow (Nat.cast_nonneg _) hcard hp
      have hleft := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 1 / (M : ℝ))
      have hroot : 0 ≤
          (vinogradovWeylMomentFactor k τ M N t (by omega) /
            coefficientBoxVolume k M) ^ (((2 * s : ℕ) : ℝ)⁻¹) := by
        rw [hmoment]
        exact Real.rpow_nonneg (mul_nonneg hA (Real.rpow_nonneg hMR.le _)) _
      exact add_le_add (mul_le_mul_of_nonneg_right hleft hroot) le_rfl
    _ = (N : ℝ) * (A / (N : ℝ)) ^ (((2 * s : ℕ) : ℝ)⁻¹) +
        2 * M := by
      rw [hmoment, shiftHolder_scale_identity hA hMR hNR' hs]
    _ = _ := by rfl

/-! ## The fixed parameter ledger -/

/-- The degree used on the logarithmic-height band.  Degree two handles the
bounded band `1 ≤ λ ≤ 2`; above it we use the unique integer band
`k - 1 < λ ≤ k`. -/
noncomputable def vinogradovDegree (lam : ℝ) : ℕ :=
  if lam ≤ 2 then 2 else ⌈lam⌉₊

/-- Iteration depth for the weak mean-value theorem.  The fixed degree-two
band gets six rounds; all other bands use `⌈2k log k⌉ + 2`. -/
noncomputable def vinogradovIterations (k : ℕ) : ℕ :=
  if k = 2 then 6 else ⌈2 * (k : ℝ) * Real.log k⌉₊ + 2

/-- The maximal integral short length below the Taylor scale
`N / t^(1/(k+1))`. -/
noncomputable def vinogradovShortLength (N : ℕ) (t : ℝ) (k : ℕ) : ℕ :=
  ⌊(N : ℝ) / t ^ (1 / (k + 1 : ℝ))⌋₊

/-- The logarithmic size budget for the reduced explicit prefactor. -/
noncomputable def vinogradovPrefactorLogBudget (k τ : ℕ) : ℝ :=
  8192 * (k : ℝ) * τ * (k + τ + 1) * Real.log (2 * (k + τ + 1))

/-- The absolute saving recorded by the fixed Weyl-sum theorem. -/
noncomputable def vinogradovWeylSaving : ℝ := (134217728 : ℝ)⁻¹

theorem vinogradovWeylSaving_pos : 0 < vinogradovWeylSaving := by
  norm_num [vinogradovWeylSaving]

private theorem vinogradovDegree_bounds {lam : ℝ} (hlam : 1 ≤ lam) :
    let k := vinogradovDegree lam
    2 ≤ k ∧ lam ≤ (k : ℝ) ∧ (k : ℝ) ≤ 2 * lam := by
  dsimp only [vinogradovDegree]
  by_cases hsmall : lam ≤ 2
  · simp only [if_pos hsmall, Nat.cast_ofNat]
    constructor
    · omega
    · constructor <;> linarith
  · simp only [if_neg hsmall]
    have hlam0 : 0 ≤ lam := le_trans (by norm_num) hlam
    have hlo : lam ≤ (⌈lam⌉₊ : ℕ) := Nat.le_ceil lam
    have hhi : ((⌈lam⌉₊ : ℕ) : ℝ) < lam + 1 := Nat.ceil_lt_add_one hlam0
    have hk2R : (2 : ℝ) < (⌈lam⌉₊ : ℕ) := lt_of_not_ge hsmall |>.trans_le hlo
    have hk2 : 2 ≤ ⌈lam⌉₊ := by exact_mod_cast hk2R.le
    exact ⟨hk2, hlo, by linarith⟩

private theorem log_two_mul_nat_gt_one {k : ℕ} (hk : 2 ≤ k) :
    1 < Real.log (2 * (k : ℝ)) := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hfour : (4 : ℝ) ≤ 2 * k := by linarith
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hfour
  rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)] at hlog
  nlinarith [Real.log_two_gt_d9]

private theorem vinogradovIterations_le {k : ℕ} (hk : 2 ≤ k) :
    (vinogradovIterations k : ℝ) ≤
      4 * (k : ℝ) * Real.log (2 * k) := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hL : 1 < Real.log (2 * (k : ℝ)) := log_two_mul_nat_gt_one hk
  by_cases hk2 : k = 2
  · subst k
    norm_num [vinogradovIterations]
    norm_num at hL ⊢
    nlinarith
  · rw [vinogradovIterations, if_neg hk2]
    have ha0 : 0 ≤ 2 * (k : ℝ) * Real.log k := by
      have : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by
        exact_mod_cast (show 1 ≤ k by omega))
      positivity
    have hceil := Nat.ceil_lt_add_one ha0
    have hlog : Real.log (k : ℝ) ≤ Real.log (2 * k) := by
      apply Real.log_le_log (by positivity)
      nlinarith
    push_cast at hceil ⊢
    nlinarith

private theorem vinogradovIterations_one_le (k : ℕ) :
    1 ≤ vinogradovIterations k := by
  rw [vinogradovIterations]
  split_ifs <;> omega

private theorem vinogradovDelta_le_half_of_iterations {k : ℕ}
    (hk : 2 ≤ k) :
    vinogradovDelta k (vinogradovIterations k) ≤ 1 / 2 := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (by norm_num) hkR
  by_cases hk2 : k = 2
  · subst k
    norm_num [vinogradovDelta, vinogradovIterations]
  · let τ := vinogradovIterations k
    have hτ : 2 * (k : ℝ) * Real.log k ≤ (τ : ℕ) := by
      dsimp only [τ, vinogradovIterations]
      rw [if_neg hk2]
      have hceil := Nat.le_ceil (2 * (k : ℝ) * Real.log k)
      push_cast
      linarith
    have hbase0 : 0 ≤ (1 : ℝ) - 1 / k := by
      field_simp
      linarith
    have hbaseExp : (1 : ℝ) - 1 / k ≤ Real.exp (-(1 / k)) :=
      Real.one_sub_le_exp_neg _
    have hpow : ((1 : ℝ) - 1 / k) ^ τ ≤
        Real.exp (-(1 / k)) ^ τ :=
      pow_le_pow_left₀ hbase0 hbaseExp τ
    have harg : (τ : ℝ) * (-(1 / k)) ≤ -2 * Real.log k := by
      calc
        (τ : ℝ) * (-(1 / k)) ≤
            (2 * (k : ℝ) * Real.log k) * (-(1 / k)) :=
          mul_le_mul_of_nonpos_right hτ (neg_nonpos.mpr (by positivity))
        _ = -2 * Real.log k := by field_simp
    have hexp : Real.exp (-(1 / k)) ^ τ ≤
        Real.exp (-2 * Real.log k) := by
      rw [← Real.exp_nat_mul]
      exact Real.exp_monotone harg
    have heq : Real.exp (-2 * Real.log k) = 1 / (k : ℝ) ^ 2 := by
      rw [show -2 * Real.log (k : ℝ) = -Real.log ((k : ℝ) ^ 2) by
        rw [Real.log_pow]; norm_num]
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      simp only [one_div]
    rw [heq] at hexp
    have := hpow.trans hexp
    have hk2ne : (k : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ hk0.ne'
    dsimp only [vinogradovDelta]
    calc
      (k : ℝ) ^ 2 / 2 * (1 - 1 / (k : ℝ)) ^ vinogradovIterations k ≤
          (k : ℝ) ^ 2 / 2 * (1 / (k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      _ = 1 / 2 := by field_simp

private theorem taylorScale_eq_rpow {N : ℕ} {t : ℝ} {k : ℕ}
    (hN : 2 ≤ N) (ht : 0 < t) :
    (N : ℝ) / t ^ (1 / (k + 1 : ℝ)) =
      (N : ℝ) ^
        (1 - (Real.log t / Real.log N) / (k + 1 : ℝ)) := by
  have hNR : (0 : ℝ) < N := by positivity
  have hlogN : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by
    exact_mod_cast hN)).ne'
  have hk1 : (k + 1 : ℝ) ≠ 0 := by positivity
  rw [Real.rpow_def_of_pos ht, Real.rpow_def_of_pos hNR]
  have hexp : Real.log (N : ℝ) *
        (1 - Real.log t / Real.log (N : ℝ) / (k + 1 : ℝ)) =
      Real.log (N : ℝ) - Real.log t * (1 / (k + 1 : ℝ)) := by
    field_simp
  rw [hexp]
  rw [Real.exp_sub, Real.exp_log hNR]

private theorem vinogradovShortLength_spec {N : ℕ} {t : ℝ} {k : ℕ}
    (hN : 2 ≤ N) (ht1 : 1 ≤ t) (htNk : t ≤ (N : ℝ) ^ k) :
    let M := vinogradovShortLength N t k
    1 ≤ M ∧ M ≤ N ∧
      t * (M : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1) ∧
      (N : ℝ) ^ (k + 1) ≤
        (2 : ℝ) ^ (k + 1) * t * (M : ℝ) ^ (k + 1) ∧
      (M : ℝ) ≤ (N : ℝ) ^
        (1 - (Real.log t / Real.log N) / (k + 1 : ℝ)) := by
  let a : ℝ := 1 / (k + 1 : ℝ)
  let root : ℝ := t ^ a
  let x : ℝ := (N : ℝ) / root
  let M := vinogradovShortLength N t k
  have hNR : (0 : ℝ) < N := by positivity
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have ha : 0 < a := by dsimp [a]; positivity
  have hroot0 : 0 < root := by dsimp [root]; positivity
  have hroot1 : 1 ≤ root := by
    dsimp [root]
    exact Real.one_le_rpow ht1 ha.le
  have hrootPow : root ^ (k + 1) = t := by
    dsimp [root, a]
    rw [← Real.rpow_natCast]
    push_cast
    rw [← Real.rpow_mul ht0.le]
    convert Real.rpow_one t using 2
    field_simp
  have htNk' : t ≤ (N : ℝ) ^ (k : ℝ) := by
    simpa only [Real.rpow_natCast] using htNk
  have hroot_le_pow : root ≤ (N : ℝ) ^ ((k : ℝ) / (k + 1 : ℝ)) := by
    have h := Real.rpow_le_rpow ht0.le htNk' ha.le
    dsimp only [root, a]
    dsimp only [a] at h
    rw [← Real.rpow_mul hNR.le] at h
    convert h using 1
    field_simp
  have hexp_le : (k : ℝ) / (k + 1 : ℝ) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  have hrootN : root ≤ (N : ℝ) := hroot_le_pow.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hN1R hexp_le)
  have hx1 : 1 ≤ x := by
    dsimp [x]
    exact (le_div_iff₀ hroot0).mpr (by simpa using hrootN)
  have hMdef : M = ⌊x⌋₊ := by rfl
  have hM1 : 1 ≤ M := by
    rw [hMdef]
    exact Nat.le_floor (by simpa using hx1)
  have hfloor : (M : ℝ) ≤ x := by
    rw [hMdef]
    exact Nat.floor_le (by positivity)
  have hxN : x ≤ N := by
    dsimp [x]
    exact (div_le_iff₀ hroot0).mpr (by nlinarith)
  have hMN : M ≤ N := by exact_mod_cast hfloor.trans hxN
  have hxM : x ≤ 2 * (M : ℝ) := by
    have hlt := Nat.lt_floor_add_one x
    rw [← hMdef] at hlt
    have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    linarith
  have hMroot : (M : ℝ) * root ≤ N := by
    apply (le_div_iff₀ hroot0).mp
    simpa only [x] using hfloor
  have hNrootM : (N : ℝ) ≤ 2 * (M : ℝ) * root := by
    apply (div_le_iff₀ hroot0).mp
    simpa only [x, mul_assoc] using hxM
  have hscalePow := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg M) hroot0.le)
    hMroot (k + 1)
  have hlowerPow := pow_le_pow_left₀ hNR.le hNrootM (k + 1)
  have hscale : t * (M : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1) := by
    rw [mul_pow, hrootPow] at hscalePow
    nlinarith
  have hlower : (N : ℝ) ^ (k + 1) ≤
      (2 : ℝ) ^ (k + 1) * t * (M : ℝ) ^ (k + 1) := by
    rw [mul_pow, mul_pow, hrootPow] at hlowerPow
    nlinarith
  have hMrpow : (M : ℝ) ≤ (N : ℝ) ^
      (1 - (Real.log t / Real.log N) / (k + 1 : ℝ)) := by
    rw [← taylorScale_eq_rpow hN ht0]
    exact hfloor
  exact ⟨hM1, hMN, hscale, hlower, hMrpow⟩

/-- The portion of the Weyl prefactor which remains after its one factor of
the short length has been exposed. -/
noncomputable def vinogradovReducedPrefactor (k τ : ℕ) : ℝ :=
  (6 : ℝ) ^ (k + 2) * (3 : ℝ) ^ k * (2 : ℝ) ^ (4 * (k * τ)) *
    vinogradovMeanValueEnvelope k τ * (Real.pi * (k : ℝ) ^ 2) ^ k

private theorem vinogradovWeylPrefactor_le_reduced
    {k τ M N : ℕ} {t : ℝ}
    (hk : 2 ≤ k) (hτ : 1 ≤ τ) (hM : 1 ≤ M) (hN : 1 ≤ N) (ht : 0 < t)
    (hlower : (N : ℝ) ^ (k + 1) ≤
      (2 : ℝ) ^ (k + 1) * t * (M : ℝ) ^ (k + 1)) :
    vinogradovWeylPrefactor k τ M N t ≤
      vinogradovReducedPrefactor k τ * M := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hthreeN : (2 * N + 1 : ℝ) ≤ 3 * N := by
    nlinarith
  have hnum := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * N + 1)
    hthreeN (k + 1)
  have hratio : (2 * N + 1 : ℝ) ^ (k + 1) /
        ((k : ℝ) ^ 2 * t * (M : ℝ) ^ k) ≤
      (6 : ℝ) ^ (k + 1) * M := by
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      (2 * N + 1 : ℝ) ^ (k + 1) ≤
          (3 * (N : ℝ)) ^ (k + 1) := hnum
      _ = (3 : ℝ) ^ (k + 1) * (N : ℝ) ^ (k + 1) := by rw [mul_pow]
      _ ≤ (3 : ℝ) ^ (k + 1) *
          ((2 : ℝ) ^ (k + 1) * t * (M : ℝ) ^ (k + 1)) :=
        mul_le_mul_of_nonneg_left hlower (by positivity)
      _ ≤ (6 : ℝ) ^ (k + 1) * M *
          ((k : ℝ) ^ 2 * t * (M : ℝ) ^ k) := by
        rw [show (6 : ℝ) ^ (k + 1) =
          (3 : ℝ) ^ (k + 1) * 2 ^ (k + 1) by
            rw [← mul_pow]; norm_num]
        rw [show (M : ℝ) ^ (k + 1) = (M : ℝ) ^ k * M by rw [pow_succ]]
        have hkSq : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [sq_nonneg (k : ℝ)]
        have hfac0 : 0 ≤ (3 : ℝ) ^ (k + 1) * 2 ^ (k + 1) * t *
            (M : ℝ) ^ k * M := by positivity
        calc
          (3 : ℝ) ^ (k + 1) * (2 ^ (k + 1) * t * ((M : ℝ) ^ k * M)) =
              (3 : ℝ) ^ (k + 1) * 2 ^ (k + 1) * t *
                (M : ℝ) ^ k * M := by ring
          _ ≤ ((3 : ℝ) ^ (k + 1) * 2 ^ (k + 1) * t *
                (M : ℝ) ^ k * M) * (k : ℝ) ^ 2 :=
            le_mul_of_one_le_right hfac0 hkSq
          _ = (3 : ℝ) ^ (k + 1) * 2 ^ (k + 1) * M *
                ((k : ℝ) ^ 2 * t * (M : ℝ) ^ k) := by ring
  have hmult : 2 * (2 * ((2 * N + 1 : ℝ) ^ (k + 1) /
          ((k : ℝ) ^ 2 * t * (M : ℝ) ^ k)) + 1) ≤
      (6 : ℝ) ^ (k + 2) * M := by
    have hpow6 : (1 : ℝ) ≤ (6 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
    have heq : (6 : ℝ) ^ (k + 2) * M =
        6 * ((6 : ℝ) ^ (k + 1) * M) := by
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
      ring
    rw [heq]
    have hBM1 : (1 : ℝ) ≤ (6 : ℝ) ^ (k + 1) * M := by
      have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM
      simpa only [one_mul] using mul_le_mul hpow6 hM1R (by positivity) (by norm_num)
    nlinarith
  have hmult' : 2 * (2 * (2 * N + 1 : ℝ) ^ (k + 1) /
          ((k : ℝ) ^ 2 * t * (M : ℝ) ^ k) + 1) ≤
      (6 : ℝ) ^ (k + 2) * M := by
    convert hmult using 1
    ring
  have hC := vinogradovMeanValueConstant_le hk hτ
  have hcore :
      2 * (2 * (2 * N + 1 : ℝ) ^ (k + 1) /
            ((k : ℝ) ^ 2 * t * (M : ℝ) ^ k) + 1) *
          vinogradovMeanValueConstant k τ ≤
        ((6 : ℝ) ^ (k + 2) * M) * vinogradovMeanValueEnvelope k τ := by
    calc
      2 * (2 * (2 * N + 1 : ℝ) ^ (k + 1) /
            ((k : ℝ) ^ 2 * t * (M : ℝ) ^ k) + 1) *
          vinogradovMeanValueConstant k τ ≤
        ((6 : ℝ) ^ (k + 2) * M) * vinogradovMeanValueConstant k τ :=
          mul_le_mul_of_nonneg_right hmult' (vinogradovMeanValueConstant_spec hk hτ).1.le
      _ ≤ ((6 : ℝ) ^ (k + 2) * M) * vinogradovMeanValueEnvelope k τ :=
        mul_le_mul_of_nonneg_left hC (by positivity)
  unfold vinogradovWeylPrefactor vinogradovReducedPrefactor
  calc
    2 * (2 * (2 * N + 1 : ℝ) ^ (k + 1) /
          ((k : ℝ) ^ 2 * t * (M : ℝ) ^ k) + 1) *
        3 ^ k * 2 ^ (4 * (k * τ)) * vinogradovMeanValueConstant k τ *
          (Real.pi * (k : ℝ) ^ 2) ^ k =
      (2 * (2 * (2 * N + 1 : ℝ) ^ (k + 1) /
          ((k : ℝ) ^ 2 * t * (M : ℝ) ^ k) + 1) *
        vinogradovMeanValueConstant k τ) *
          (3 ^ k * 2 ^ (4 * (k * τ)) * (Real.pi * (k : ℝ) ^ 2) ^ k) := by ring
    _ ≤ (((6 : ℝ) ^ (k + 2) * M) * vinogradovMeanValueEnvelope k τ) *
          (3 ^ k * 2 ^ (4 * (k * τ)) * (Real.pi * (k : ℝ) ^ 2) ^ k) :=
      mul_le_mul_of_nonneg_right hcore (by positivity)
    _ = (6 : ℝ) ^ (k + 2) * 3 ^ k * 2 ^ (4 * (k * τ)) *
          vinogradovMeanValueEnvelope k τ * (Real.pi * (k : ℝ) ^ 2) ^ k * M := by ring

private theorem log_vinogradovReducedPrefactor_le {k τ : ℕ}
    (hk : 2 ≤ k) (hτ : 1 ≤ τ) :
    Real.log (vinogradovReducedPrefactor k τ) ≤
      vinogradovPrefactorLogBudget k τ := by
  let m : ℕ := k + τ + 1
  let L : ℝ := Real.log (2 * (m : ℝ))
  have hm : 4 ≤ m := by dsimp [m]; omega
  have hm0 : (0 : ℝ) < m := by positivity
  have hkR : (0 : ℝ) < k := by positivity
  have hL0 : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by nlinarith [show (4 : ℝ) ≤ m by exact_mod_cast hm])
  have hlog2 : Real.log 2 ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by norm_num) (by
      have hmR : (4 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith)
  have hlog3 : Real.log 3 ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by norm_num) (by nlinarith [show (4 : ℝ) ≤ m by exact_mod_cast hm])
  have hlog6 : Real.log 6 ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by norm_num) (by nlinarith [show (4 : ℝ) ≤ m by exact_mod_cast hm])
  have hk_m : (k : ℝ) ≤ m := by exact_mod_cast (show k ≤ m by dsimp [m]; omega)
  have hpi : Real.pi * (k : ℝ) ^ 2 ≤ (2 * (m : ℝ)) ^ 3 := by
    have hp : Real.pi ≤ 4 := Real.pi_lt_four.le
    have hkSq := pow_le_pow_left₀ hkR.le hk_m 2
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    calc
      Real.pi * (k : ℝ) ^ 2 ≤ 4 * (m : ℝ) ^ 2 :=
        mul_le_mul hp hkSq (sq_nonneg _) (by positivity)
      _ ≤ (2 * (m : ℝ)) ^ 3 := by
        rw [mul_pow]
        nlinarith [sq_nonneg ((m : ℝ) - 1)]
  have hlogpi : Real.log (Real.pi * (k : ℝ) ^ 2) ≤ 3 * L := by
    calc
      Real.log (Real.pi * (k : ℝ) ^ 2) ≤ Real.log ((2 * (m : ℝ)) ^ 3) :=
        Real.log_le_log (by positivity) hpi
      _ = 3 * L := by rw [Real.log_pow]; rfl
  have henv := log_vinogradovMeanValueEnvelope_le hk hτ
  have henv' : Real.log (vinogradovMeanValueEnvelope k τ) ≤
      6144 * (k : ℝ) * τ * m * L := by
    dsimp only [m, L]
    push_cast
    exact henv
  have hcoeff : ((k + 2 : ℕ) : ℝ) + k + 4 * (k * τ) + 3 * k +
      6144 * (k : ℝ) * τ * m ≤ 8192 * (k : ℝ) * τ * m := by
    have hk_le : k ≤ k * τ * m := by
      calc
        k = k * 1 * 1 := by omega
        _ ≤ k * τ * m := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hτ) (by
          dsimp [m]; omega)
    have hkτ_le : k * τ ≤ k * τ * m := by
      calc
        k * τ = k * τ * 1 := by omega
        _ ≤ k * τ * m := Nat.mul_le_mul_left _ (by dsimp [m]; omega)
    have hcoeffNat : (k + 2) + k + 4 * (k * τ) + 3 * k +
        6144 * (k * τ * m) ≤ 8192 * (k * τ * m) := by omega
    have hcoeffR : (((k + 2) + k + 4 * (k * τ) + 3 * k +
        6144 * (k * τ * m) : ℕ) : ℝ) ≤ (8192 * (k * τ * m) : ℕ) := by
      exact_mod_cast hcoeffNat
    norm_num [Nat.cast_add, Nat.cast_mul] at hcoeffR ⊢
    simpa only [mul_assoc] using hcoeffR
  have henv0 : 0 < vinogradovMeanValueEnvelope k τ := by
    unfold vinogradovMeanValueEnvelope vinogradovMeanValueEnvelopeBase
    positivity
  have hbudget : vinogradovPrefactorLogBudget k τ =
      8192 * (k : ℝ) * τ * (m : ℝ) * L := by
    dsimp [vinogradovPrefactorLogBudget, m, L]
    push_cast
    ring
  unfold vinogradovReducedPrefactor
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) henv0.ne',
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  rw [hbudget]
  change ((k : ℝ) + 2) * Real.log 6 + (k : ℝ) * Real.log 3 +
      (4 * ((k : ℝ) * τ)) * Real.log 2 +
      Real.log (vinogradovMeanValueEnvelope k τ) +
      (k : ℝ) * Real.log (Real.pi * (k : ℝ) ^ 2) ≤
    8192 * (k : ℝ) * τ * (m : ℝ) * L
  have h6 := mul_le_mul_of_nonneg_left hlog6 (by positivity : 0 ≤ (k : ℝ) + 2)
  have h3 := mul_le_mul_of_nonneg_left hlog3 (by positivity : 0 ≤ (k : ℝ))
  have h2 := mul_le_mul_of_nonneg_left hlog2 (by positivity : 0 ≤ 4 * (k : ℝ) * τ)
  have hp := mul_le_mul_of_nonneg_left hlogpi (by positivity : 0 ≤ (k : ℝ))
  have hcoeff' : ((k : ℝ) + 2) + k + 4 * (k * τ) + 3 * k +
      6144 * (k : ℝ) * τ * m ≤ 8192 * (k : ℝ) * τ * m := by
    norm_num [Nat.cast_add] at hcoeff
    exact hcoeff
  calc
    ((k : ℝ) + 2) * Real.log 6 + (k : ℝ) * Real.log 3 +
          (4 * ((k : ℝ) * τ)) * Real.log 2 +
          Real.log (vinogradovMeanValueEnvelope k τ) +
          (k : ℝ) * Real.log (Real.pi * (k : ℝ) ^ 2) ≤
      ((k : ℝ) + 2) * L + (k : ℝ) * L +
          (4 * ((k : ℝ) * τ)) * L +
          6144 * (k : ℝ) * τ * m * L + (k : ℝ) * (3 * L) := by
        nlinarith
    _ =
      (((k : ℝ) + 2) + k + 4 * (k * τ) + 3 * k +
          6144 * (k : ℝ) * τ * m) * L := by ring
    _ ≤ 8192 * (k : ℝ) * τ * m * L :=
      mul_le_mul_of_nonneg_right hcoeff' hL0.le

private theorem vinogradovReducedPrefactor_le_exp {k τ : ℕ}
    (hk : 2 ≤ k) (hτ : 1 ≤ τ) :
    vinogradovReducedPrefactor k τ ≤
      Real.exp (vinogradovPrefactorLogBudget k τ) := by
  have henv0 : 0 < vinogradovMeanValueEnvelope k τ := by
    unfold vinogradovMeanValueEnvelope vinogradovMeanValueEnvelopeBase
    positivity
  rw [← Real.log_le_iff_le_exp (by
    unfold vinogradovReducedPrefactor
    positivity : 0 < vinogradovReducedPrefactor k τ)]
  exact log_vinogradovReducedPrefactor_le hk hτ

private theorem vinogradovScaleExponent_le_three_quarters {lam : ℝ}
    (hlam : 1 ≤ lam) :
    let k := vinogradovDegree lam
    let τ := vinogradovIterations k
    (1 + vinogradovDelta k τ) * (1 - lam / (k + 1 : ℝ)) ≤ 3 / 4 := by
  dsimp only
  by_cases hsmall : lam ≤ 2
  · rw [vinogradovDegree, if_pos hsmall]
    norm_num [vinogradovIterations, vinogradovDelta]
    nlinarith
  · have hlam2 : 2 < lam := lt_of_not_ge hsmall
    have hlam0 : 0 ≤ lam := by linarith
    rw [vinogradovDegree, if_neg hsmall]
    let k : ℕ := ⌈lam⌉₊
    let τ : ℕ := vinogradovIterations k
    have hklo : lam ≤ (k : ℝ) := by
      dsimp [k]
      exact Nat.le_ceil lam
    have hkhi : (k : ℝ) < lam + 1 := by
      dsimp [k]
      exact Nat.ceil_lt_add_one hlam0
    have hk : 2 ≤ k := by
      have : (2 : ℝ) < k := hlam2.trans_le hklo
      exact_mod_cast this.le
    have hk10 : (0 : ℝ) < k + 1 := by positivity
    have hratio0 : 0 ≤ lam / (k + 1 : ℝ) := div_nonneg hlam0 hk10.le
    have hratio1 : lam / (k + 1 : ℝ) ≤ 1 := by
      apply (div_le_one hk10).mpr
      linarith
    have hratioHalf : (1 / 2 : ℝ) ≤ lam / (k + 1 : ℝ) := by
      apply (le_div_iff₀ hk10).mpr
      linarith
    have hdelta := vinogradovDelta_le_half_of_iterations hk
    have hdelta0 : 0 ≤ vinogradovDelta k τ := by
      dsimp [vinogradovDelta]
      have hbase : 0 ≤ (1 : ℝ) - 1 / k := by
        have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
        field_simp
        linarith
      positivity
    have hleft : 0 ≤ 1 + vinogradovDelta k τ := by positivity
    have hright : 0 ≤ 1 - lam / (k + 1 : ℝ) := by linarith
    have hmul := mul_le_mul (by linarith : 1 + vinogradovDelta k τ ≤ 3 / 2)
      (by linarith : 1 - lam / (k + 1 : ℝ) ≤ 1 / 2)
      hright (by norm_num : (0 : ℝ) ≤ 3 / 2)
    norm_num at hmul ⊢
    simpa only [k, τ] using hmul

private theorem vinogradovParameterLogBudget_le {lam : ℝ} (hlam : 1 ≤ lam) :
    let k := vinogradovDegree lam
    let τ := vinogradovIterations k
    vinogradovPrefactorLogBudget k τ ≤
      46137344 * lam ^ 3 * Real.log (2 * lam) ^ 3 := by
  let k := vinogradovDegree lam
  let τ := vinogradovIterations k
  let m : ℕ := k + τ + 1
  let L : ℝ := Real.log (2 * lam)
  let Lk : ℝ := Real.log (2 * (k : ℝ))
  have hb := vinogradovDegree_bounds hlam
  change 2 ≤ k ∧ lam ≤ (k : ℝ) ∧ (k : ℝ) ≤ 2 * lam at hb
  rcases hb with ⟨hk, hlamk, hklam⟩
  have hlam0 : 0 ≤ lam := le_trans (by norm_num) hlam
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hLhalf : (1 / 2 : ℝ) ≤ L := by
    have hlog2lam : Real.log 2 ≤ L := by
      dsimp [L]
      exact Real.log_le_log (by norm_num) (by nlinarith)
    nlinarith [Real.log_two_gt_d9]
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hLhalf
  have hLupper : L ≤ 2 * lam := by
    dsimp [L]
    exact (Real.log_le_sub_one_of_pos (by positivity : 0 < 2 * lam)).trans (by linarith)
  have hLk : Lk ≤ 2 * L := by
    have harg : (2 : ℝ) * k ≤ 4 * lam := by nlinarith
    have hlog := Real.log_le_log (by positivity : 0 < 2 * (k : ℝ)) harg
    have hsplit : Real.log (4 * lam) = Real.log 2 + L := by
      rw [show 4 * lam = 2 * (2 * lam) by ring,
        Real.log_mul (by norm_num) (by positivity)]
    rw [hsplit] at hlog
    have hlog2L : Real.log 2 ≤ L := by
      dsimp [L]
      exact Real.log_le_log (by norm_num) (by nlinarith)
    exact hlog.trans (by linarith)
  have hτk := vinogradovIterations_le hk
  change (τ : ℝ) ≤ 4 * (k : ℝ) * Lk at hτk
  have hτlam : (τ : ℝ) ≤ 16 * lam * L := by
    have hLk0 : 0 ≤ Lk := le_trans zero_le_one (log_two_mul_nat_gt_one hk).le
    calc
      (τ : ℝ) ≤ 4 * (k : ℝ) * Lk := hτk
      _ ≤ 4 * (2 * lam) * (2 * L) := by gcongr
      _ = 16 * lam * L := by ring
  have hm : (m : ℝ) ≤ 22 * lam * L := by
    have hkL : (k : ℝ) ≤ 4 * lam * L := by
      calc
        (k : ℝ) ≤ 2 * lam := hklam
        _ ≤ 4 * lam * L := by nlinarith [mul_nonneg hlam0 hL0.le]
    have hone : (1 : ℝ) ≤ 2 * lam * L := by
      nlinarith [mul_nonneg hlam0 hL0.le]
    dsimp [m]
    push_cast
    linarith
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hlogm : Real.log (2 * (m : ℝ)) ≤ 8 * L := by
    have hmrough : (2 : ℝ) * m ≤ 88 * lam ^ 2 := by
      calc
        (2 : ℝ) * m ≤ 2 * (22 * lam * L) := mul_le_mul_of_nonneg_left hm (by norm_num)
        _ = 44 * lam * L := by ring
        _ ≤ 44 * lam * (2 * lam) :=
          mul_le_mul_of_nonneg_left hLupper (mul_nonneg (by norm_num) hlam0)
        _ = 88 * lam ^ 2 := by ring
    have hlam2 : (1 : ℝ) ≤ lam ^ 2 := one_le_pow₀ hlam
    have hlam4 : lam ^ 2 ≤ lam ^ 4 := by
      calc
        lam ^ 2 = lam ^ 2 * 1 := by ring
        _ ≤ lam ^ 2 * lam ^ 2 := mul_le_mul_of_nonneg_left hlam2 (sq_nonneg lam)
        _ = lam ^ 4 := by ring
    have hlam8 : lam ^ 4 ≤ lam ^ 8 := by
      have hlam4one : (1 : ℝ) ≤ lam ^ 4 := hlam2.trans hlam4
      calc
        lam ^ 4 = lam ^ 4 * 1 := by ring
        _ ≤ lam ^ 4 * lam ^ 4 := mul_le_mul_of_nonneg_left hlam4one (by positivity)
        _ = lam ^ 8 := by ring
    have hpow : (2 : ℝ) * m ≤ (2 * lam) ^ 8 := by
      calc
        (2 : ℝ) * m ≤ 88 * lam ^ 2 := hmrough
        _ ≤ 256 * lam ^ 8 := by nlinarith [hlam4.trans hlam8]
        _ = (2 * lam) ^ 8 := by ring
    calc
      Real.log (2 * (m : ℝ)) ≤ Real.log ((2 * lam) ^ 8) :=
        Real.log_le_log (by positivity) hpow
      _ = 8 * L := by rw [Real.log_pow]; rfl
  have hbudget : vinogradovPrefactorLogBudget k τ =
      8192 * (k : ℝ) * τ * (m : ℝ) * Real.log (2 * (m : ℝ)) := by
    dsimp [vinogradovPrefactorLogBudget, m]
    push_cast
    ring
  change vinogradovPrefactorLogBudget k τ ≤ 46137344 * lam ^ 3 * L ^ 3
  rw [hbudget]
  have hlogm0 : 0 ≤ Real.log (2 * (m : ℝ)) := by
    apply Real.log_nonneg
    have hmNat : 1 ≤ m := by dsimp [m]; omega
    exact_mod_cast (show 1 ≤ 2 * m by omega)
  calc
    8192 * (k : ℝ) * τ * (m : ℝ) * Real.log (2 * (m : ℝ)) ≤
        8192 * (2 * lam) * (16 * lam * L) * (22 * lam * L) * (8 * L) := by
      gcongr
    _ = 46137344 * lam ^ 3 * L ^ 3 := by ring

private theorem vinogradovTargetSaving_le_natural {lam : ℝ} (hlam : 1 ≤ lam) :
    let k := vinogradovDegree lam
    let τ := vinogradovIterations k
    vinogradovWeylSaving / (lam ^ 3 * Real.log (2 * lam) ^ 3) ≤
      1 / (16 * (k : ℝ) * τ) := by
  let k := vinogradovDegree lam
  let τ := vinogradovIterations k
  let L : ℝ := Real.log (2 * lam)
  have hb := vinogradovDegree_bounds hlam
  change 2 ≤ k ∧ lam ≤ (k : ℝ) ∧ (k : ℝ) ≤ 2 * lam at hb
  rcases hb with ⟨hk, _hlamk, hklam⟩
  have hLhalf : (1 / 2 : ℝ) ≤ L := by
    have hlog2lam : Real.log 2 ≤ L := by
      dsimp [L]
      exact Real.log_le_log (by norm_num) (by nlinarith)
    nlinarith [Real.log_two_gt_d9]
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hLhalf
  have hLk : Real.log (2 * (k : ℝ)) ≤ 2 * L := by
    have hlam0 : 0 ≤ lam := by linarith
    have harg : (2 : ℝ) * k ≤ 4 * lam := by nlinarith
    have hlog := Real.log_le_log (by positivity : 0 < 2 * (k : ℝ)) harg
    have hsplit : Real.log (4 * lam) = Real.log 2 + L := by
      rw [show 4 * lam = 2 * (2 * lam) by ring,
        Real.log_mul (by norm_num) (by positivity)]
    have hlog2L : Real.log 2 ≤ L := by
      dsimp [L]
      exact Real.log_le_log (by norm_num) (by nlinarith)
    rw [hsplit] at hlog
    exact hlog.trans (by linarith)
  have hτk := vinogradovIterations_le hk
  change (τ : ℝ) ≤ 4 * (k : ℝ) * Real.log (2 * k) at hτk
  have hkτ : (k : ℝ) * τ ≤ 32 * lam ^ 2 * L := by
    have hLk0 : 0 ≤ Real.log (2 * (k : ℝ)) :=
      le_trans zero_le_one (log_two_mul_nat_gt_one hk).le
    calc
      (k : ℝ) * τ ≤ (k : ℝ) * (4 * k * Real.log (2 * k)) :=
        mul_le_mul_of_nonneg_left hτk (by positivity)
      _ ≤ (2 * lam) * (4 * (2 * lam) * (2 * L)) := by gcongr
      _ = 32 * lam ^ 2 * L := by ring
  have hden0 : 0 < lam ^ 3 * L ^ 3 := by positivity
  have hnatDen0 : 0 < 16 * (k : ℝ) * τ := by
    have hτ := vinogradovIterations_one_le k
    positivity
  change vinogradovWeylSaving / (lam ^ 3 * L ^ 3) ≤
    1 / (16 * (k : ℝ) * τ)
  apply (div_le_div_iff₀ hden0 hnatDen0).mpr
  have hsmall : 512 * vinogradovWeylSaving ≤ lam * L ^ 2 := by
    have : (512 : ℝ) * vinogradovWeylSaving ≤ 1 / 4 := by
      norm_num [vinogradovWeylSaving]
    have hlam0 : (0 : ℝ) ≤ lam := by linarith
    have hprod : (1 / 4 : ℝ) ≤ lam * L ^ 2 := by
      have hs : (1 / 4 : ℝ) ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1 / 2)]
      have hp := mul_le_mul hlam hs (by norm_num : (0 : ℝ) ≤ 1 / 4) hlam0
      simpa only [one_mul] using hp
    exact this.trans hprod
  have hc0 : 0 ≤ vinogradovWeylSaving := vinogradovWeylSaving_pos.le
  have hden : 16 * (k : ℝ) * τ ≤ 512 * lam ^ 2 * L := by
    nlinarith
  calc
    vinogradovWeylSaving * (16 * (k : ℝ) * τ) ≤
        vinogradovWeylSaving * (512 * lam ^ 2 * L) := by
      exact mul_le_mul_of_nonneg_left hden hc0
    _ ≤ lam ^ 3 * L ^ 3 := by
      calc
        vinogradovWeylSaving * (512 * lam ^ 2 * L) =
            (512 * vinogradovWeylSaving) * (lam ^ 2 * L) := by ring
        _ ≤ (lam * L ^ 2) * (lam ^ 2 * L) :=
          mul_le_mul_of_nonneg_right hsmall (mul_nonneg (sq_nonneg lam) hL0.le)
        _ = lam ^ 3 * L ^ 3 := by ring
    _ = 1 * (lam ^ 3 * L ^ 3) := by ring

private theorem rpow_prefactor_absorb {N Q B r : ℝ}
    (hN : 1 ≤ N) (hQ : 0 ≤ Q) (hr : 0 ≤ r)
    (hQexp : Q ≤ Real.exp B) (hlarge : 8 * B ≤ Real.log N) :
    (Q * N ^ (-(1 / 4 : ℝ))) ^ r ≤ N ^ (-(r / 8)) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hNpow0 : 0 ≤ N ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hN0.le _
  have hQpow : Q ^ r ≤ N ^ (r / 8) := by
    have hfirst := Real.rpow_le_rpow hQ hQexp hr
    calc
      Q ^ r ≤ (Real.exp B) ^ r := hfirst
      _ = Real.exp (B * r) := by rw [Real.rpow_def_of_pos (Real.exp_pos B), Real.log_exp]
      _ ≤ Real.exp (Real.log N * (r / 8)) := by
        apply Real.exp_monotone
        have := mul_le_mul_of_nonneg_right hlarge hr
        nlinarith
      _ = N ^ (r / 8) := by rw [Real.rpow_def_of_pos hN0]
  rw [Real.mul_rpow hQ hNpow0]
  calc
    Q ^ r * (N ^ (-(1 / 4 : ℝ))) ^ r ≤
        N ^ (r / 8) * (N ^ (-(1 / 4 : ℝ))) ^ r :=
      mul_le_mul_of_nonneg_right hQpow (Real.rpow_nonneg hNpow0 _)
    _ = N ^ (r / 8) * N ^ (-(r / 4)) := by
      rw [← Real.rpow_mul hN0.le]
      congr 2
      ring
    _ = N ^ (-(r / 8)) := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring

set_option maxHeartbeats 1000000 in
/-- V-C2-10'.  The fixed Vinogradov parameter choice, including the
degree-two bounded band, the large-`N` prefactor absorption, and the
trivial complementary branch.  The constants recorded here are
`c = 2⁻²⁷`, `C = 100`, and `K = 8 · 46137344 = 369098752`. -/
theorem norm_log_sum_le_vinogradovFixed
    (N : ℕ) (t : ℝ) (hN : 2 ≤ N) (htN : (N : ℝ) ≤ t)
    (u : ℝ) (R : ℕ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hNR : N < R) (hR : R ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc N R,
        ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((n : ℝ) + u))‖ ≤
      100 * (N : ℝ) ^
        (1 - vinogradovWeylSaving /
          ((Real.log t / Real.log N) ^ 3 *
            Real.log (2 * (Real.log t / Real.log N)) ^ 3)) := by
  let lam : ℝ := Real.log t / Real.log N
  let k : ℕ := vinogradovDegree lam
  let τ : ℕ := vinogradovIterations k
  let M : ℕ := vinogradovShortLength N t k
  let B : ℝ := vinogradovPrefactorLogBudget k τ
  let eps : ℝ := vinogradovWeylSaving / (lam ^ 3 * Real.log (2 * lam) ^ 3)
  let r : ℝ := (((2 * (k * τ) : ℕ) : ℝ))⁻¹
  have hNR0 : (0 : ℝ) < N := by positivity
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have ht0 : 0 < t := lt_of_lt_of_le hNR0 htN
  have ht1 : 1 ≤ t := le_trans hN1R htN
  have hlogNt : Real.log (N : ℝ) ≤ Real.log t :=
    Real.log_le_log hNR0 htN
  have hlam : 1 ≤ lam := by
    dsimp [lam]
    exact (le_div_iff₀ hlogN).mpr (by simpa using hlogNt)
  have hb := vinogradovDegree_bounds hlam
  change 2 ≤ k ∧ lam ≤ (k : ℝ) ∧ (k : ℝ) ≤ 2 * lam at hb
  rcases hb with ⟨hk, hlamk, hklam⟩
  have hτ : 1 ≤ τ := vinogradovIterations_one_le k
  have htNk : t ≤ (N : ℝ) ^ k := by
    have hlogtk : Real.log t ≤ (k : ℝ) * Real.log N := by
      have := (mul_le_mul_of_nonneg_right hlamk hlogN.le)
      dsimp [lam] at this
      field_simp [hlogN.ne'] at this
      nlinarith
    calc
      t = Real.exp (Real.log t) := (Real.exp_log ht0).symm
      _ ≤ Real.exp ((k : ℝ) * Real.log N) := Real.exp_monotone hlogtk
      _ = (N : ℝ) ^ k := by rw [Real.exp_nat_mul, Real.exp_log hNR0]
  have hMspec := vinogradovShortLength_spec hN ht1 htNk
  change 1 ≤ M ∧ M ≤ N ∧
      t * (M : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1) ∧
      (N : ℝ) ^ (k + 1) ≤
        (2 : ℝ) ^ (k + 1) * t * (M : ℝ) ^ (k + 1) ∧
      (M : ℝ) ≤ (N : ℝ) ^ (1 - lam / (k + 1 : ℝ)) at hMspec
  rcases hMspec with ⟨hM, hMN, hscale, hlower, hMpow⟩
  have hdelta := vinogradovDelta_le_half_of_iterations hk
  have hdelta0 : 0 ≤ vinogradovDelta k τ := by
    dsimp [vinogradovDelta]
    have hbase : 0 ≤ (1 : ℝ) - 1 / k := by
      have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
      field_simp
      linarith
    positivity
  have halpha0 : 0 ≤ 1 - lam / (k + 1 : ℝ) := by
    have hk10 : (0 : ℝ) < k + 1 := by positivity
    have : lam / (k + 1 : ℝ) ≤ 1 := (div_le_one hk10).mpr (by linarith)
    linarith
  have hscaleExp := vinogradovScaleExponent_le_three_quarters hlam
  change (1 + vinogradovDelta k τ) * (1 - lam / (k + 1 : ℝ)) ≤ 3 / 4 at hscaleExp
  have hMthree : (M : ℝ) ^ (1 + vinogradovDelta k τ) ≤
      (N : ℝ) ^ (3 / 4 : ℝ) := by
    have hp := Real.rpow_le_rpow (Nat.cast_nonneg M) hMpow (by positivity :
      0 ≤ 1 + vinogradovDelta k τ)
    rw [← Real.rpow_mul hNR0.le] at hp
    exact hp.trans (Real.rpow_le_rpow_of_exponent_le hN1R (by
      simpa only [mul_comm] using hscaleExp))
  have hQ := vinogradovWeylPrefactor_le_reduced hk hτ hM (show 1 ≤ N by omega) ht0 hlower
  have henv0 : 0 < vinogradovMeanValueEnvelope k τ := by
    unfold vinogradovMeanValueEnvelope vinogradovMeanValueEnvelopeBase
    positivity
  have hred0 : 0 ≤ vinogradovReducedPrefactor k τ := by
    unfold vinogradovReducedPrefactor
    positivity
  have hpref0 : 0 ≤ vinogradovWeylPrefactor k τ M N t := by
    have hC0 := (vinogradovMeanValueConstant_spec hk hτ).1.le
    unfold vinogradovWeylPrefactor
    positivity
  have hbase : vinogradovWeylPrefactor k τ M N t *
        (M : ℝ) ^ vinogradovDelta k τ / (N : ℝ) ≤
      vinogradovReducedPrefactor k τ * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hleft := mul_le_mul_of_nonneg_right hQ
      (Real.rpow_nonneg hM0 (vinogradovDelta k τ))
    have hprod : (M : ℝ) * (M : ℝ) ^ vinogradovDelta k τ =
        (M : ℝ) ^ (1 + vinogradovDelta k τ) := by
      rw [Real.rpow_add (by positivity : (0 : ℝ) < M), Real.rpow_one]
    calc
      vinogradovWeylPrefactor k τ M N t *
          (M : ℝ) ^ vinogradovDelta k τ / (N : ℝ) ≤
        (vinogradovReducedPrefactor k τ * M) *
          (M : ℝ) ^ vinogradovDelta k τ / (N : ℝ) := by gcongr
      _ = vinogradovReducedPrefactor k τ *
          ((M : ℝ) ^ (1 + vinogradovDelta k τ) / (N : ℝ)) := by
        rw [← hprod]
        ring
      _ ≤ vinogradovReducedPrefactor k τ *
          ((N : ℝ) ^ (3 / 4 : ℝ) / (N : ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hMthree hNR0.le) hred0
      _ = vinogradovReducedPrefactor k τ * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
        congr 1
        calc
          (N : ℝ) ^ (3 / 4 : ℝ) / (N : ℝ) =
              (N : ℝ) ^ (3 / 4 : ℝ) / (N : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          _ = (N : ℝ) ^ ((3 / 4 : ℝ) - 1) :=
            (Real.rpow_sub hNR0 (3 / 4 : ℝ) 1).symm
          _ = (N : ℝ) ^ (-(1 / 4 : ℝ)) := by norm_num
  have hB := vinogradovParameterLogBudget_le hlam
  change B ≤ 46137344 * lam ^ 3 * Real.log (2 * lam) ^ 3 at hB
  have hepsNatural := vinogradovTargetSaving_le_natural hlam
  change eps ≤ 1 / (16 * (k : ℝ) * τ) at hepsNatural
  have heps0 : 0 < eps := by
    dsimp [eps]
    have hL : 0 < Real.log (2 * lam) := Real.log_pos (by nlinarith)
    exact div_pos vinogradovWeylSaving_pos (mul_pos (pow_pos (by linarith) 3) (pow_pos hL 3))
  have hrEq : r / 8 = 1 / (16 * (k : ℝ) * τ) := by
    dsimp [r]
    push_cast
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    have hτ0 : (τ : ℝ) ≠ 0 := by exact_mod_cast (show τ ≠ 0 by omega)
    field_simp
    ring
  have hepsr : eps ≤ r / 8 := by rw [hrEq]; exact hepsNatural
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrSmall : r / 8 ≤ 1 / 16 := by
    rw [hrEq]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (k : ℝ) * τ)
      (by norm_num : (0 : ℝ) < 16)).mpr
    nlinarith [show (2 : ℝ) ≤ k by exact_mod_cast hk,
      show (1 : ℝ) ≤ τ by exact_mod_cast hτ]
  have htargetExp : (3 / 4 : ℝ) ≤ 1 - eps := by linarith
  have hMtarget : (M : ℝ) ≤ (N : ℝ) ^ (1 - eps) :=
    hMpow.trans (Real.rpow_le_rpow_of_exponent_le hN1R (by
      have halpha : 1 - lam / (k + 1 : ℝ) ≤ 3 / 4 := by
        have hmulLower : 1 - lam / (k + 1 : ℝ) ≤
            (1 + vinogradovDelta k τ) * (1 - lam / (k + 1 : ℝ)) := by
          nlinarith [mul_nonneg hdelta0 halpha0]
        exact hmulLower.trans hscaleExp
      exact halpha.trans htargetExp))
  by_cases hlarge : 8 * B ≤ Real.log N
  · have hmain := norm_log_sum_le_vinogradovMainTerm hk hτ hM hMN hNR hR
      ht0 htNk hu0 hu1 hscale
    have hredExp := vinogradovReducedPrefactor_le_exp hk hτ
    have habsorb := rpow_prefactor_absorb hN1R
      hred0 hr0 hredExp hlarge
    have hroot := Real.rpow_le_rpow (by
      exact div_nonneg (mul_nonneg hpref0 (Real.rpow_nonneg (Nat.cast_nonneg M) _)) hNR0.le : 0 ≤
        vinogradovWeylPrefactor k τ M N t * (M : ℝ) ^ vinogradovDelta k τ / N)
      hbase hr0
    have hmainTerm : (N : ℝ) *
        (vinogradovWeylPrefactor k τ M N t *
          (M : ℝ) ^ vinogradovDelta k τ / (N : ℝ)) ^ r ≤
        (N : ℝ) ^ (1 - eps) := by
      calc
        (N : ℝ) * (vinogradovWeylPrefactor k τ M N t *
            (M : ℝ) ^ vinogradovDelta k τ / (N : ℝ)) ^ r ≤
          (N : ℝ) * (vinogradovReducedPrefactor k τ *
            (N : ℝ) ^ (-(1 / 4 : ℝ))) ^ r :=
          mul_le_mul_of_nonneg_left hroot hNR0.le
        _ ≤ (N : ℝ) * (N : ℝ) ^ (-(r / 8)) :=
          mul_le_mul_of_nonneg_left habsorb hNR0.le
        _ = (N : ℝ) ^ (1 - r / 8) := by
          calc
            (N : ℝ) * (N : ℝ) ^ (-(r / 8)) =
                (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(r / 8)) := by
              rw [Real.rpow_one]
            _ = (N : ℝ) ^ ((1 : ℝ) + -(r / 8)) :=
              (Real.rpow_add hNR0 (1 : ℝ) (-(r / 8))).symm
            _ = (N : ℝ) ^ (1 - r / 8) := by ring
        _ ≤ (N : ℝ) ^ (1 - eps) :=
          Real.rpow_le_rpow_of_exponent_le hN1R (by linarith)
    change _ ≤ 100 * (N : ℝ) ^ (1 - eps)
    calc
      ‖∑ n ∈ Finset.Ioc N R,
          ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((n : ℝ) + u))‖ ≤
        (N : ℝ) *
          (vinogradovWeylPrefactor k τ M N t *
              (M : ℝ) ^ vinogradovDelta k τ / (N : ℝ)) ^ r +
            2 * M := by simpa only [r] using hmain
      _ ≤ (N : ℝ) ^ (1 - eps) + 2 * (N : ℝ) ^ (1 - eps) := by
        exact add_le_add hmainTerm (mul_le_mul_of_nonneg_left hMtarget (by norm_num))
      _ ≤ 100 * (N : ℝ) ^ (1 - eps) := by
        have := Real.rpow_nonneg hNR0.le (1 - eps)
        nlinarith
  · have hsmall : Real.log N < 8 * B := lt_of_not_ge hlarge
    have hlogeps : eps * Real.log N < 3 := by
      have hden0 : 0 < lam ^ 3 * Real.log (2 * lam) ^ 3 := by
        have : 0 < Real.log (2 * lam) := Real.log_pos (by nlinarith)
        positivity
      have hsmall' : Real.log N <
          8 * (46137344 * lam ^ 3 * Real.log (2 * lam) ^ 3) :=
        hsmall.trans_le (mul_le_mul_of_nonneg_left hB (by norm_num))
      dsimp [eps]
      have hc := vinogradovWeylSaving_pos
      rw [show vinogradovWeylSaving /
          (lam ^ 3 * Real.log (2 * lam) ^ 3) * Real.log N =
        (vinogradovWeylSaving * Real.log N) /
          (lam ^ 3 * Real.log (2 * lam) ^ 3) by ring]
      apply (div_lt_iff₀ hden0).mpr
      calc
        vinogradovWeylSaving * Real.log N <
            vinogradovWeylSaving *
              (8 * (46137344 * lam ^ 3 * Real.log (2 * lam) ^ 3)) :=
          mul_lt_mul_of_pos_left hsmall' hc
        _ = (11 / 4 : ℝ) * (lam ^ 3 * Real.log (2 * lam) ^ 3) := by
          norm_num [vinogradovWeylSaving]
          ring
        _ < 3 * (lam ^ 3 * Real.log (2 * lam) ^ 3) := by
          nlinarith
    have hNeps : (N : ℝ) ^ eps ≤ 100 := by
      rw [Real.rpow_def_of_pos hNR0]
      have hexp : Real.exp (Real.log N * eps) ≤ Real.exp 3 := by
        apply Real.exp_monotone
        nlinarith
      calc
        Real.exp (Real.log N * eps) ≤ Real.exp 3 := hexp
        _ = Real.exp 1 ^ (3 : ℕ) := by
          rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
        _ ≤ (3 : ℝ) ^ (3 : ℕ) :=
          pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 3
        _ ≤ 100 := by norm_num
    have htriv : ‖∑ n ∈ Finset.Ioc N R,
        ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((n : ℝ) + u))‖ ≤
        ((Finset.Ioc N R).card : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      simp only [ExpSums.norm_e, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact le_rfl
    have hcard : ((Finset.Ioc N R).card : ℝ) ≤ N := by
      rw [Nat.card_Ioc]
      exact_mod_cast (show R - N ≤ N by omega)
    have hNfactor : (N : ℝ) ≤ 100 * (N : ℝ) ^ (1 - eps) := by
      calc
        (N : ℝ) = (N : ℝ) ^ eps * (N : ℝ) ^ (1 - eps) := by
          rw [← Real.rpow_add hNR0]
          norm_num
        _ ≤ 100 * (N : ℝ) ^ (1 - eps) :=
          mul_le_mul_of_nonneg_right hNeps (Real.rpow_nonneg hNR0.le _)
    change _ ≤ 100 * (N : ℝ) ^ (1 - eps)
    exact htriv.trans (hcard.trans hNfactor)

/-! ## Conversion to complex powers -/

/-- The normalized logarithmic character used above is exactly the complex
power occurring in the requested Weyl sum. -/
theorem cpow_neg_mul_I_eq_e_log {y t : ℝ} (hy : 0 < y) :
    (y : ℂ) ^ (-(t : ℂ) * Complex.I) =
      ExpSums.e (-(t / (2 * Real.pi)) * Real.log y) := by
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hlog : Complex.log (y : ℂ) = (Real.log y : ℂ) :=
    (Complex.ofReal_log hy.le).symm
  rw [Complex.cpow_def_of_ne_zero hyc, hlog]
  unfold ExpSums.e
  congr 1
  push_cast
  field_simp

/-- V-C2-11.  Vinogradov's logarithmic Weyl-sum estimate in the requested
complex-power form.  One admissible explicit pair is
`c = 2⁻²⁷`, `C = 100`. -/
theorem vinogradov_weyl_sum :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (N : ℕ) (t : ℝ), 2 ≤ N → (N : ℝ) ≤ t →
        ∀ (u : ℝ) (R : ℕ), 0 ≤ u → u ≤ 1 → N < R → R ≤ 2 * N →
          ‖∑ n ∈ Finset.Ioc N R,
              ((n : ℝ) + u : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ≤
            C * (N : ℝ) ^
              (1 - c / ((Real.log t / Real.log N) ^ 3 *
                Real.log (2 * (Real.log t / Real.log N)) ^ 3)) := by
  refine ⟨vinogradovWeylSaving, 100, vinogradovWeylSaving_pos, by norm_num, ?_⟩
  intro N t hN htN u R hu0 hu1 hNR hR
  have hconvert :
      ∑ n ∈ Finset.Ioc N R,
          ((n : ℝ) + u : ℂ) ^ (-(t : ℂ) * Complex.I) =
        ∑ n ∈ Finset.Ioc N R,
          ExpSums.e (-(t / (2 * Real.pi)) * Real.log ((n : ℝ) + u)) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hy : (0 : ℝ) < (n : ℝ) + u := by
      have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      exact add_pos_of_pos_of_nonneg hnR hu0
    simpa only [Complex.ofReal_add] using
      (cpow_neg_mul_I_eq_e_log (t := t) hy)
  rw [hconvert]
  exact norm_log_sum_le_vinogradovFixed N t hN htN u R hu0 hu1 hNR hR

end VinogradovWeylSum

end MoltResearch
