import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Complex.Basic

/-!
# Discrepancy: log-uniform weights and finitary affine invariance

Track C, Elliott campaign (`Problems/tao2015_derivation_c.md`, issue #2946, E3): the
toolbox for the logarithmically averaged random variable `𝐧` of arXiv:1509.05422 §2 —
`P(𝐧 = n) ∝ 1/n` on a window `a < n ≤ b`. The log-averaging buys *approximate affine
invariance* (the paper's Lemma `linear`): restricting to a residue class `n ≡ r (q)` and
substituting `n = q·n' + r` reproduces the log-uniform weights at scale `n' = n/q`, at
the cost `1/n − 1/(q·(n/q)) = O(r/(q·(n/q))²)` per term — summable to `O(r/q²)`.

* `sum_one_div_sq_le_two` — `∑_{n ∈ S} 1/n² ≤ 2` for any finite `S ⊆ ℕ` (public
  telescoping util).
* `sum_filter_residue_eq_sum_image` — the **exact** reindexing of a residue-class sum
  along `n ↦ n/q` (zero error; the affine range bookkeeping stays with the consumer).
* `norm_sum_div_residue_sub_le` — the **weight comparison**: replacing `1/n` by
  `(1/q)·(1/(n/q))` on the residue class costs at most `2r/q²` in total, uniformly over
  `1`-bounded numerators.
-/

namespace MoltResearch

open Finset

/-- Telescoping bound, public form: `∑_{n ∈ S} 1/n² ≤ 2` for any finite set of
naturals (the `n = 0` term is junk `0`, the `n = 1` term is `1`, and the tail
telescopes through `1/(n(n−1))`). -/
theorem sum_one_div_sq_le_two (S : Finset ℕ) :
    ∑ n ∈ S, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 2 := by
  classical
  have hmono : ∑ n ∈ S, (1 : ℝ) / (n : ℝ) ^ 2
      ≤ ∑ n ∈ Finset.range (S.sup id + 1), (1 : ℝ) / (n : ℝ) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (fun n hn => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)))
      fun n _ _ => by positivity
  refine le_trans hmono ?_
  set N := S.sup id + 1
  -- split off n = 0 (junk zero) and n = 1 (value one); telescope the rest
  have hsplit : ∑ n ∈ Finset.range N, (1 : ℝ) / (n : ℝ) ^ 2
      ≤ 1 + ∑ n ∈ (Finset.range N).filter (2 ≤ ·), (1 : ℝ) / (n : ℝ) ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) (2 ≤ ·)]
    have hsmall : ∑ n ∈ (Finset.range N).filter (fun n => ¬ 2 ≤ n),
        (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 := by
      have hsub : (Finset.range N).filter (fun n => ¬ 2 ≤ n) ⊆ {0, 1} := by
        intro n hn
        rw [Finset.mem_filter] at hn
        rw [Finset.mem_insert, Finset.mem_singleton]
        omega
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
        fun n _ _ => by positivity) ?_
      rw [show ({0, 1} : Finset ℕ) = insert 0 {1} from rfl,
        Finset.sum_insert (by norm_num), Finset.sum_singleton]
      norm_num
    linarith
  refine le_trans hsplit ?_
  -- closed telescoping form on Ico 2 M
  have hclosed : ∀ M : ℕ, 2 ≤ M →
      ∑ n ∈ Finset.Ico 2 M, ((1 : ℝ) / ((n : ℝ) - 1) - 1 / n)
        = 1 - 1 / ((M : ℝ) - 1) := by
    intro M hM
    induction M with
    | zero => omega
    | succ L ihL =>
      rcases Nat.lt_or_ge L 2 with hL | hL
      · have hL1 : L = 1 := by omega
        subst hL1
        simp
        norm_num
      · rw [Finset.sum_Ico_succ_top (by omega), ihL hL]
        have hL1 : (1 : ℝ) < (L : ℝ) := by
          have : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
          linarith
        push_cast
        rw [show ((L : ℝ) + 1 - 1) = (L : ℝ) from by ring]
        ring
  have htel : ∑ n ∈ (Finset.range N).filter (2 ≤ ·), (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 := by
    have hterm : ∀ n ∈ (Finset.range N).filter (2 ≤ ·),
        (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / ((n : ℝ) - 1) - 1 / n := by
      intro n hn
      rw [Finset.mem_filter] at hn
      have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.2
      have h1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
      have h0 : (0 : ℝ) < (n : ℝ) := by linarith
      rw [div_sub_div _ _ (ne_of_gt h1) (ne_of_gt h0), one_mul, mul_one,
        show (n : ℝ) - ((n : ℝ) - 1) = 1 from by ring]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hsub : (Finset.range N).filter (2 ≤ ·) = Finset.Ico 2 N := by
      ext n
      rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [hsub]
    rcases Nat.lt_or_ge N 2 with hN | hN
    · rw [show Finset.Ico 2 N = ∅ from Finset.Ico_eq_empty (by omega),
        Finset.sum_empty]
      norm_num
    · rw [hclosed N hN]
      have hN1 : (1 : ℝ) < (N : ℝ) := by
        have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        linarith
      have : (0 : ℝ) < 1 / ((N : ℝ) - 1) := by
        have : (0:ℝ) < (N : ℝ) - 1 := by linarith
        positivity
      linarith
  linarith

variable {q r : ℕ}

/-- **Exact residue-class reindexing**: on the class `n ≡ r (q)`, summing `f n` equals
summing `f (q·n' + r)` over the quotients `n' = n/q` — zero error; the affine range
bookkeeping stays with the consumer. -/
theorem sum_filter_residue_eq_sum_image (hq : 0 < q) (hr : r < q)
    (f : ℕ → ℂ) (s : Finset ℕ) :
    ∑ n ∈ s.filter (fun n => n % q = r), f n
      = ∑ n' ∈ (s.filter (fun n => n % q = r)).image (· / q), f (q * n' + r) := by
  classical
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_filter] at hn
    congr 1
    have h2 : n % q = r := hn.2
    have h3 := Nat.div_add_mod n q
    omega
  · intro n hn m hm h
    have hn2 : n % q = r := by
      have hn' : n ∈ s.filter (fun n => n % q = r) := hn
      exact (Finset.mem_filter.mp hn').2
    have hm2 : m % q = r := by
      have hm' : m ∈ s.filter (fun n => n % q = r) := hm
      exact (Finset.mem_filter.mp hm').2
    have h' : n / q = m / q := h
    calc n = q * (n / q) + n % q := (Nat.div_add_mod n q).symm
      _ = q * (m / q) + m % q := by rw [h', hn2, hm2]
      _ = m := Nat.div_add_mod m q

/-- **The log-uniform weight comparison** (the analytic heart of the paper's Lemma
`linear`): replacing the weight `1/n` by `(1/q)·(1/(n/q))` on the residue class
`n ≡ r (q)` costs at most `2r/q²` in total, uniformly over `1`-bounded numerators —
provided the window starts above `q` (so the quotients are positive). -/
theorem norm_sum_div_residue_sub_le (hq : 0 < q) (hr : r < q)
    {F : ℕ → ℂ} (hF : ∀ n, ‖F n‖ ≤ 1) {a b : ℕ} (ha : q ≤ a) :
    ‖(∑ n ∈ (Finset.Ioc a b).filter (fun n => n % q = r), F n / (n : ℂ))
        - ∑ n ∈ (Finset.Ioc a b).filter (fun n => n % q = r),
            F n / (q : ℂ) / ((n / q : ℕ) : ℂ)‖
      ≤ 2 * r / q ^ 2 := by
  classical
  rw [← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  set T := (Finset.Ioc a b).filter (fun n => n % q = r) with hT
  have hterm : ∀ n ∈ T, ‖F n / (n : ℂ) - F n / (q : ℂ) / ((n / q : ℕ) : ℂ)‖
      ≤ (r : ℝ) / (q : ℝ) ^ 2 / ((n / q : ℕ) : ℝ) ^ 2 := by
    intro n hn
    rw [hT, Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨han, hbn⟩, hmod⟩ := hn
    set m : ℕ := n / q with hm
    have hn_eq : n = q * m + r := by
      rw [hm]
      have h3 := Nat.div_add_mod n q
      omega
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h1
      · rw [h0] at hn_eq
        omega
      · exact h1
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hnR : (n : ℝ) = q * m + r := by exact_mod_cast hn_eq
    have hn0 : (0 : ℝ) < (n : ℝ) := by rw [hnR]; positivity
    -- factor out F n and compare the weights as complex numbers of real entries
    have hfactor : F n / (n : ℂ) - F n / (q : ℂ) / ((m : ℕ) : ℂ)
        = F n * ((1 : ℂ) / (n : ℂ) - 1 / ((q : ℂ) * (m : ℂ))) := by
      field_simp
    rw [hfactor, norm_mul]
    have hweights : ‖(1 : ℂ) / (n : ℂ) - 1 / ((q : ℂ) * (m : ℂ))‖
        ≤ (r : ℝ) / (q : ℝ) ^ 2 / (m : ℝ) ^ 2 := by
      have hcast : (1 : ℂ) / (n : ℂ) - 1 / ((q : ℂ) * (m : ℂ))
          = (((1 : ℝ) / (n : ℝ) - 1 / ((q : ℝ) * (m : ℝ)) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hcast, Complex.norm_real]
      have hval : (1 : ℝ) / (n : ℝ) - 1 / ((q : ℝ) * (m : ℝ))
          = -(r : ℝ) / ((q * m) * (q * m + r)) := by
        rw [hnR]
        have h1 : (0:ℝ) < (q:ℝ) * m := by positivity
        field_simp
        ring
      have hr0 : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg r
      have hqm0 : (0:ℝ) ≤ (q:ℝ) * m := by positivity
      have hge : (q:ℝ)^2 * (m:ℝ)^2 ≤ ((q:ℝ) * m) * ((q:ℝ) * m + (r:ℝ)) := by
        nlinarith [mul_nonneg hqm0 hr0]
      have hd1 : (0:ℝ) < ((q:ℝ) * m) * ((q:ℝ) * m + (r:ℝ)) := by positivity
      have hd2 : (0:ℝ) < (q:ℝ)^2 * (m:ℝ)^2 := by positivity
      rw [hval, Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg hr0,
        abs_of_pos hd1]
      calc (r:ℝ) / (((q:ℝ) * m) * ((q:ℝ) * m + (r:ℝ)))
          ≤ (r:ℝ) / ((q:ℝ)^2 * (m:ℝ)^2) :=
            div_le_div_of_nonneg_left hr0 hd2 hge
        _ = (r : ℝ) / (q : ℝ) ^ 2 / (m : ℝ) ^ 2 := by rw [div_div]
    calc ‖F n‖ * ‖(1 : ℂ) / (n : ℂ) - 1 / ((q : ℂ) * (m : ℂ))‖
        ≤ 1 * ((r : ℝ) / (q : ℝ) ^ 2 / (m : ℝ) ^ 2) := by
          have := hF n
          have h0 := norm_nonneg ((1 : ℂ) / (n : ℂ) - 1 / ((q : ℂ) * (m : ℂ)))
          nlinarith [hweights]
      _ = (r : ℝ) / (q : ℝ) ^ 2 / ((n / q : ℕ) : ℝ) ^ 2 := by rw [one_mul]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  -- reindex the error sum through the quotients and close with the 1/n² util
  have himg : ∑ n ∈ T, (r : ℝ) / (q : ℝ) ^ 2 / ((n / q : ℕ) : ℝ) ^ 2
      = ∑ m ∈ T.image (· / q), (r : ℝ) / (q : ℝ) ^ 2 / (m : ℝ) ^ 2 := by
    rw [Finset.sum_image]
    intro n hn m hm h
    have hn2 : n % q = r := by
      have hn' : n ∈ (Finset.Ioc a b).filter (fun n => n % q = r) := hn
      exact (Finset.mem_filter.mp hn').2
    have hm2 : m % q = r := by
      have hm' : m ∈ (Finset.Ioc a b).filter (fun n => n % q = r) := hm
      exact (Finset.mem_filter.mp hm').2
    have h' : n / q = m / q := h
    calc n = q * (n / q) + n % q := (Nat.div_add_mod n q).symm
      _ = q * (m / q) + m % q := by rw [h', hn2, hm2]
      _ = m := Nat.div_add_mod m q
  rw [himg]
  have hfinal : ∑ m ∈ T.image (· / q), (r : ℝ) / (q : ℝ) ^ 2 / (m : ℝ) ^ 2
      = (r : ℝ) / (q : ℝ) ^ 2 * ∑ m ∈ T.image (· / q), (1:ℝ) / (m : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hfinal]
  have hutil := sum_one_div_sq_le_two (T.image (· / q))
  have hcoef : (0:ℝ) ≤ (r : ℝ) / (q : ℝ) ^ 2 := by positivity
  have hsum0 : (0:ℝ) ≤ ∑ m ∈ T.image (· / q), (1:ℝ) / (m : ℝ) ^ 2 :=
    Finset.sum_nonneg fun m _ => by positivity
  have h2 : (r : ℝ) / (q : ℝ) ^ 2 * ∑ m ∈ T.image (· / q), (1:ℝ) / (m : ℝ) ^ 2
      ≤ (r : ℝ) / (q : ℝ) ^ 2 * 2 := by nlinarith
  have h3 : (r : ℝ) / (q : ℝ) ^ 2 * 2 = 2 * (r : ℝ) / (q : ℝ) ^ 2 := by ring
  linarith

end MoltResearch
