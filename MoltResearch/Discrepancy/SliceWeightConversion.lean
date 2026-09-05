import MoltResearch.Discrepancy.SliceA2

/-!
# Removing the slice normalization

The Fourier-side coefficient used by the A.2 harness is `f m * A / m`.
On a short interval `(n,n+H]`, multiplication of that sum by `n/A`
changes the original sum by at most `H^2/n`.  The second theorem records
the resulting slice `L²` estimate with all constants exposed.
-/

namespace MoltResearch

open Finset

/-- The coefficient error on `(n,n+H]` is at most `H/n`. -/
theorem weight_conversion_coefficient_le (A n H m : ℕ)
    (hA : 0 < A) (hn : 0 < n) (hmn : n < m) (hmH : m ≤ n + H) :
    ‖(1 : ℂ) - (n : ℂ) / (A : ℂ) * ((A : ℂ) / (m : ℂ))‖
      ≤ (H : ℝ) / n := by
  have hA0 : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have hmn' : (n : ℝ) ≤ m := by exact_mod_cast hmn.le
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by exact_mod_cast hn) hmn'
  have hmH' : (m : ℝ) ≤ n + H := by exact_mod_cast hmH
  have hdiff : (m : ℝ) - n ≤ H := by linarith
  rw [div_mul_div_cancel₀ hA0]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast,
    ← Complex.ofReal_one, ← Complex.ofReal_div]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [one_sub_div (ne_of_gt hmpos)]
    calc
      ((m : ℝ) - n) / m ≤ ((m : ℝ) - n) / n := by
        exact div_le_div_of_nonneg_left (sub_nonneg.mpr hmn') hn0 hmn'
      _ ≤ (H : ℝ) / n := (div_le_div_iff_of_pos_right hn0).mpr hdiff
  · exact sub_nonneg.mpr ((div_le_one hmpos).mpr hmn')

/-- **A2-IV-2, pointwise form.**  Replacing a short sum by the scaled
`A/m`-weighted sum costs at most `H²/n`. -/
theorem norm_short_sum_sub_scaled_weighted_le
    (f : ℕ → ℂ) (hf : ∀ m, ‖f m‖ ≤ 1)
    (A n H : ℕ) (hA : 0 < A) (hn : 0 < n) :
    ‖(∑ m ∈ Finset.Ioc n (n + H), f m) -
        (n : ℂ) / (A : ℂ) *
          ∑ m ∈ Finset.Ioc n (n + H), f m * ((A : ℂ) / (m : ℂ))‖
      ≤ (H : ℝ)^2 / n := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    ∑ m ∈ Finset.Ioc n (n + H), ‖f m -
          (n : ℂ) / (A : ℂ) * (f m * ((A : ℂ) / (m : ℂ)))‖
        ≤ ∑ _m ∈ Finset.Ioc n (n + H), (H : ℝ) / n := by
          refine Finset.sum_le_sum fun m hm => ?_
          rw [show f m - (n : ℂ) / (A : ℂ) *
                (f m * ((A : ℂ) / (m : ℂ))) =
              f m * ((1 : ℂ) - (n : ℂ) / (A : ℂ) *
                ((A : ℂ) / (m : ℂ))) by ring]
          rw [norm_mul]
          exact (mul_le_mul (hf m)
            (weight_conversion_coefficient_le A n H m hA hn
              (Finset.mem_Ioc.mp hm).1 (Finset.mem_Ioc.mp hm).2)
            (norm_nonneg _) (by positivity)).trans_eq (one_mul _)
    _ = (H : ℝ) * ((H : ℝ) / n) := by
          rw [Finset.sum_const, Nat.card_Ioc, Nat.add_sub_cancel_left,
            nsmul_eq_mul]
    _ = (H : ℝ)^2 / n := by ring

/-- The scaling factor `n/A` is uniformly bounded on a slice `(A,A+s]`. -/
theorem slice_scale_sq_le (A s n : ℕ) (hA : 0 < A)
    (hn : n ∈ Finset.Ioc A (A + s)) :
    ((n : ℝ) / A)^2 ≤ (((A + s : ℕ) : ℝ) / A)^2 := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnle : (n : ℝ) ≤ A + s := by
    exact_mod_cast (Finset.mem_Ioc.mp hn).2
  exact (sq_le_sq₀ (div_nonneg hn0 hA0.le)
    (div_nonneg (by positivity) hA0.le)).mpr
      (div_le_div_of_nonneg_right (by
        simpa only [Nat.cast_add] using hnle) hA0.le)

/-- The accumulated pointwise conversion error on a slice has the announced
`2 H⁴ s / A³` cost. -/
theorem slice_weight_conversion_error_le (A s H : ℕ) (hA : 0 < A) :
    ∑ n ∈ Finset.Ioc A (A + s),
        2 * (((H : ℝ)^2 / n)^2) / n
      ≤ 2 * (H : ℝ)^4 * s / (A : ℝ)^3 := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  calc
    ∑ n ∈ Finset.Ioc A (A + s), 2 * (((H : ℝ)^2 / n)^2) / n
        ≤ ∑ _n ∈ Finset.Ioc A (A + s),
            2 * (H : ℝ)^4 / (A : ℝ)^3 := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hnA : (A : ℝ) ≤ n := by
            exact_mod_cast (Finset.mem_Ioc.mp hn).1.le
          have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hA0 hnA
          rw [show 2 * (((H : ℝ)^2 / n)^2) / n =
            2 * (H : ℝ)^4 / (n : ℝ)^3 by ring]
          exact div_le_div_of_nonneg_left (by positivity) (pow_pos hA0 3)
            (pow_le_pow_left₀ hA0.le hnA 3)
    _ = 2 * (H : ℝ)^4 * s / (A : ℝ)^3 := by
          rw [Finset.sum_const, Nat.card_Ioc, Nat.add_sub_cancel_left,
            nsmul_eq_mul]
          ring

/-- **A2-IV-2, slice form.**  The unweighted short-interval energy is
controlled by the energy of the `A/m`-weighted coefficient sequence and the
elementary `H⁴s/A³` conversion error. -/
theorem slice_energy_le_scaled_weighted_energy
    (f : ℕ → ℂ) (hf : ∀ m, ‖f m‖ ≤ 1)
    (A s H : ℕ) (hA : 0 < A) :
    ∑ n ∈ Finset.Ioc A (A + s),
        ‖∑ m ∈ Finset.Ioc n (n + H), f m‖^2 / n
      ≤ 2 * (((A + s : ℕ) : ℝ) / A)^2 *
          (∑ n ∈ Finset.Ioc A (A + s),
            ‖∑ m ∈ Finset.Ioc n (n + H),
                f m * ((A : ℂ) / (m : ℂ))‖^2 / n) +
        2 * (H : ℝ)^4 * s / (A : ℝ)^3 := by
  classical
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  calc
    ∑ n ∈ Finset.Ioc A (A + s),
        ‖∑ m ∈ Finset.Ioc n (n + H), f m‖^2 / n
        ≤ ∑ n ∈ Finset.Ioc A (A + s),
            (2 * (((n : ℝ) / A)^2 *
                ‖∑ m ∈ Finset.Ioc n (n + H),
                    f m * ((A : ℂ) / (m : ℂ))‖^2) +
              2 * (((H : ℝ)^2 / n)^2)) / n := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn0 : 0 < n :=
            lt_of_lt_of_le hA (Finset.mem_Ioc.mp hn).1.le
          have herr := norm_short_sum_sub_scaled_weighted_le f hf A n H hA hn0
          have htri : ‖∑ m ∈ Finset.Ioc n (n + H), f m‖ ≤
              ‖(n : ℂ) / (A : ℂ) *
                  ∑ m ∈ Finset.Ioc n (n + H),
                    f m * ((A : ℂ) / (m : ℂ))‖ +
                (H : ℝ)^2 / n := by
            calc
              _ = ‖((∑ m ∈ Finset.Ioc n (n + H), f m) -
                    (n : ℂ) / (A : ℂ) *
                      ∑ m ∈ Finset.Ioc n (n + H),
                        f m * ((A : ℂ) / (m : ℂ)) +
                  (n : ℂ) / (A : ℂ) *
                      ∑ m ∈ Finset.Ioc n (n + H),
                        f m * ((A : ℂ) / (m : ℂ)))‖ := by
                    congr 2
                    exact (sub_add_cancel _ _).symm
              _ ≤ ‖(∑ m ∈ Finset.Ioc n (n + H), f m) -
                    (n : ℂ) / (A : ℂ) *
                      ∑ m ∈ Finset.Ioc n (n + H),
                        f m * ((A : ℂ) / (m : ℂ))‖ +
                  ‖(n : ℂ) / (A : ℂ) *
                      ∑ m ∈ Finset.Ioc n (n + H),
                        f m * ((A : ℂ) / (m : ℂ))‖ := norm_add_le _ _
              _ ≤ _ := by linarith
          have hsq := (sq_le_sq₀ (norm_nonneg _)
            (add_nonneg (norm_nonneg _) (by positivity))).mpr htri
          let u : ℝ := ‖(n : ℂ) / (A : ℂ) *
              ∑ m ∈ Finset.Ioc n (n + H),
                f m * ((A : ℂ) / (m : ℂ))‖
          let v : ℝ := (H : ℝ)^2 / n
          have hadd : (u + v)^2 ≤ 2 * u^2 + 2 * v^2 := by
            nlinarith [sq_nonneg (u - v)]
          dsimp only [u, v] at hadd
          have hscale : ‖(n : ℂ) / (A : ℂ) *
                  ∑ m ∈ Finset.Ioc n (n + H),
                    f m * ((A : ℂ) / (m : ℂ))‖^2 =
                ((n : ℝ) / A)^2 *
                  ‖∑ m ∈ Finset.Ioc n (n + H),
                    f m * ((A : ℂ) / (m : ℂ))‖^2 := by
            rw [norm_mul, norm_div, Complex.norm_natCast,
              Complex.norm_natCast]
            ring
          have hnum := le_trans hsq hadd
          rw [hscale] at hnum
          exact div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ ∑ n ∈ Finset.Ioc A (A + s),
          (2 * (((A + s : ℕ) : ℝ) / A)^2 *
              ‖∑ m ∈ Finset.Ioc n (n + H),
                  f m * ((A : ℂ) / (m : ℂ))‖^2) / n +
        ∑ n ∈ Finset.Ioc A (A + s),
          2 * (((H : ℝ)^2 / n)^2) / n := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun n hn => ?_
          rw [add_div]
          have hscale := mul_le_mul_of_nonneg_right
            (slice_scale_sq_le A s n hA hn)
            (sq_nonneg ‖∑ m ∈ Finset.Ioc n (n + H),
              f m * ((A : ℂ) / (m : ℂ))‖)
          have hscale2 := mul_le_mul_of_nonneg_left hscale
            (by norm_num : (0 : ℝ) ≤ 2)
          exact add_le_add
            (div_le_div_of_nonneg_right (by simpa [mul_assoc] using hscale2)
              (by positivity)) le_rfl
    _ ≤ 2 * (((A + s : ℕ) : ℝ) / A)^2 *
          (∑ n ∈ Finset.Ioc A (A + s),
            ‖∑ m ∈ Finset.Ioc n (n + H),
                f m * ((A : ℂ) / (m : ℂ))‖^2 / n) +
        2 * (H : ℝ)^4 * s / (A : ℝ)^3 := by
          rw [Finset.mul_sum]
          refine add_le_add ?_ (slice_weight_conversion_error_le A s H hA)
          refine le_of_eq ?_
          refine Finset.sum_congr rfl fun n _ => ?_
          ring

end MoltResearch
