import MoltResearch.Discrepancy.MultiplicativeC
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

/-- **Shift comparison for log-uniform sums**: advancing the argument by one changes a
log-averaged window sum by at most `3/a` — one weight comparison plus two boundary
terms. The engine of the paper's `Q(s+1) = Q(s) + O(1/p)` fluctuation step
(arXiv:1509.05422, Proposition `conv`). -/
theorem norm_sum_div_shift_sub_le {F : ℕ → ℂ} (hF : ∀ n, ‖F n‖ ≤ 1) {a b : ℕ}
    (ha : 1 ≤ a) :
    ‖(∑ n ∈ Finset.Ioc a b, F (n + 1) / (n : ℂ))
        - ∑ n ∈ Finset.Ioc a b, F n / (n : ℂ)‖ ≤ 3 / a := by
  classical
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < (a : ℝ) := by linarith
  rcases Nat.lt_or_ge a b with hab | hba
  swap
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, Finset.sum_empty,
      sub_zero, norm_zero]
    positivity
  -- piece 1: weight comparison at the same index, telescoped
  have hw : ‖(∑ n ∈ Finset.Ioc a b, F (n + 1) / (n : ℂ))
      - ∑ n ∈ Finset.Ioc a b, F (n + 1) / ((n + 1 : ℕ) : ℂ)‖ ≤ 1 / a := by
    rw [← Finset.sum_sub_distrib]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n ∈ Finset.Ioc a b,
        ‖F (n + 1) / (n : ℂ) - F (n + 1) / ((n + 1 : ℕ) : ℂ)‖
          ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      have hn1 : 1 ≤ n := by omega
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hfac : F (n + 1) / (n : ℂ) - F (n + 1) / ((n + 1 : ℕ) : ℂ)
          = F (n + 1) * ((1 : ℂ) / (n : ℂ) - 1 / ((n + 1 : ℕ) : ℂ)) := by
        field_simp
      rw [hfac, norm_mul]
      have hcast : (1 : ℂ) / (n : ℂ) - 1 / ((n + 1 : ℕ) : ℂ)
          = (((1 : ℝ) / (n : ℝ) - 1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs]
      have hpos : (0 : ℝ) < 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
        rw [show (1 : ℝ) / (n : ℝ) - 1 / ((n : ℝ) + 1)
            = 1 / ((n : ℝ) * ((n : ℝ) + 1)) from by
          field_simp
          ring]
        positivity
      rw [abs_of_pos hpos]
      have h1 := hF (n + 1)
      nlinarith [hpos]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hclosed : ∀ c : ℕ, a ≤ c →
        ∑ n ∈ Finset.Ioc a c, ((1 : ℝ) / n - 1 / ((n : ℝ) + 1))
          = 1 / ((a : ℝ) + 1) - 1 / ((c : ℝ) + 1) := by
      intro c hc
      induction c with
      | zero =>
        exfalso
        omega
      | succ d ih =>
        rcases Nat.lt_or_ge d a with hd | hd
        · have hde : d + 1 = a := by omega
          rw [← hde, Finset.Ioc_self, Finset.sum_empty]
          ring
        · rw [Finset.sum_Ioc_succ_top (by omega), ih hd]
          push_cast
          ring
    rw [hclosed b (by omega)]
    have hb1 : (0 : ℝ) < (b : ℝ) + 1 := by positivity
    have h3 : (1 : ℝ) / ((a : ℝ) + 1) ≤ 1 / (a : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) ha0]
      nlinarith
    have h4 : (0 : ℝ) ≤ 1 / ((b : ℝ) + 1) := by positivity
    linarith
  -- piece 2: exact reindex of the corrected sum
  have hreindex : ∑ m ∈ Finset.Ioc (a + 1) (b + 1), F m / (m : ℂ)
      = ∑ n ∈ Finset.Ioc a b, F (n + 1) / ((n + 1 : ℕ) : ℂ) := by
    rw [show Finset.Ioc (a + 1) (b + 1) = (Finset.Ioc a b).image (· + 1) from by
      ext m
      rw [Finset.mem_Ioc, Finset.mem_image]
      constructor
      · intro hm
        exact ⟨m - 1, by rw [Finset.mem_Ioc]; omega, by omega⟩
      · rintro ⟨k, hk, rfl⟩
        rw [Finset.mem_Ioc] at hk
        omega]
    refine Finset.sum_image fun x _ y _ h => ?_
    have h' : x + 1 = y + 1 := h
    omega
  -- piece 3: boundary comparison between the shifted and original windows
  have hbound : ‖(∑ m ∈ Finset.Ioc (a + 1) (b + 1), F m / (m : ℂ))
      - ∑ n ∈ Finset.Ioc a b, F n / (n : ℂ)‖ ≤ 2 / a := by
    have hsplit1 : ∑ m ∈ Finset.Ioc (a + 1) (b + 1), F m / (m : ℂ)
        = (∑ m ∈ Finset.Ioc (a + 1) b, F m / (m : ℂ))
          + F (b + 1) / ((b + 1 : ℕ) : ℂ) :=
      Finset.sum_Ioc_succ_top (by omega) _
    have herase : Finset.Ioc (a + 1) b = (Finset.Ioc a b).erase (a + 1) := by
      ext m
      rw [Finset.mem_erase, Finset.mem_Ioc, Finset.mem_Ioc]
      omega
    have hsplit2 : ∑ n ∈ Finset.Ioc a b, F n / (n : ℂ)
        = (∑ m ∈ Finset.Ioc (a + 1) b, F m / (m : ℂ))
          + F (a + 1) / ((a + 1 : ℕ) : ℂ) := by
      rw [herase]
      exact (Finset.sum_erase_add _ _ (by rw [Finset.mem_Ioc]; omega)).symm
    rw [hsplit1, hsplit2]
    rw [show ((∑ m ∈ Finset.Ioc (a + 1) b, F m / (m : ℂ))
          + F (b + 1) / ((b + 1 : ℕ) : ℂ))
        - ((∑ m ∈ Finset.Ioc (a + 1) b, F m / (m : ℂ))
          + F (a + 1) / ((a + 1 : ℕ) : ℂ))
        = F (b + 1) / ((b + 1 : ℕ) : ℂ) - F (a + 1) / ((a + 1 : ℕ) : ℂ) from by ring]
    refine le_trans (norm_sub_le _ _) ?_
    have hnb : ‖F (b + 1) / ((b + 1 : ℕ) : ℂ)‖ ≤ 1 / a := by
      rw [norm_div]
      have hb0 : (0 : ℝ) < ((b + 1 : ℕ) : ℝ) := by positivity
      have hnorm : ‖((b + 1 : ℕ) : ℂ)‖ = ((b + 1 : ℕ) : ℝ) := by
        rw [Complex.norm_natCast]
      rw [hnorm]
      have h1 := hF (b + 1)
      have hab' : (a : ℝ) ≤ ((b + 1 : ℕ) : ℝ) := by
        push_cast
        have : a ≤ b := by omega
        have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast this
        linarith
      rw [div_le_div_iff₀ hb0 ha0]
      nlinarith
    have hna : ‖F (a + 1) / ((a + 1 : ℕ) : ℂ)‖ ≤ 1 / a := by
      rw [norm_div]
      have ha1 : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) := by positivity
      rw [Complex.norm_natCast]
      have h1 := hF (a + 1)
      have haa : (a : ℝ) ≤ ((a + 1 : ℕ) : ℝ) := by push_cast; linarith
      rw [div_le_div_iff₀ ha1 ha0]
      nlinarith
    calc ‖F (b + 1) / ((b + 1 : ℕ) : ℂ)‖ + ‖F (a + 1) / ((a + 1 : ℕ) : ℂ)‖
        ≤ 1 / a + 1 / a := by linarith
      _ = 2 / a := by ring
  -- assemble by the triangle inequality through the corrected sum
  calc ‖(∑ n ∈ Finset.Ioc a b, F (n + 1) / (n : ℂ))
        - ∑ n ∈ Finset.Ioc a b, F n / (n : ℂ)‖
      ≤ ‖(∑ n ∈ Finset.Ioc a b, F (n + 1) / (n : ℂ))
          - ∑ n ∈ Finset.Ioc a b, F (n + 1) / ((n + 1 : ℕ) : ℂ)‖
        + ‖(∑ n ∈ Finset.Ioc a b, F (n + 1) / ((n + 1 : ℕ) : ℂ))
          - ∑ n ∈ Finset.Ioc a b, F n / (n : ℂ)‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub
          (∑ n ∈ Finset.Ioc a b, F (n + 1) / (n : ℂ))
          (∑ n ∈ Finset.Ioc a b, F (n + 1) / ((n + 1 : ℕ) : ℂ))
          (∑ n ∈ Finset.Ioc a b, F n / (n : ℂ))
        linarith
    _ ≤ 1 / a + 2 / a := by
        have hbound' : ‖(∑ n ∈ Finset.Ioc a b, F (n + 1) / ((n + 1 : ℕ) : ℂ))
            - ∑ n ∈ Finset.Ioc a b, F n / (n : ℂ)‖ ≤ 2 / a := by
          rw [← hreindex]
          exact hbound
        exact add_le_add hw hbound'
    _ = 3 / a := by ring

/-- **The two-modulus residue split** (Chinese remainder, filter form): for coprime
`a`, `p`, the residue class mod `a·p` is the intersection of the classes mod `a` and
mod `p` — the paper's split of `1_{𝐧+j ≡ pb (ap)}`. -/
theorem filter_mod_mul_eq {a p : ℕ} (hcop : Nat.Coprime a p) (c : ℕ) (s : Finset ℕ) :
    s.filter (fun n => n % (a * p) = c % (a * p))
      = (s.filter (fun n => n % a = c % a)).filter (fun n => n % p = c % p) := by
  ext n
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter, and_assoc]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mpr h.2
    exact ⟨h.1, h1, h2⟩
  · rintro ⟨hs, h1, h2⟩
    exact ⟨hs, (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1, h2⟩⟩

/-- **The conjugate-pair dilation identity** (exact; the reason `c_p = 1` for the
Erdős-discrepancy application of arXiv:1509.05422): for unimodular completely
multiplicative `g`, dilating both arguments of a conjugate-pair correlation by `p`
changes nothing. -/
theorem conjPair_dilate {g : ℕ → ℂ} (hcm : CompletelyMultiplicativeC g)
    (huni : Unimodular g) {p m k : ℕ} (hp : p ≠ 0) (hm : m ≠ 0) (hk : k ≠ 0) :
    g (p * m) * (starRingEnd ℂ) (g (p * k)) = g m * (starRingEnd ℂ) (g k) := by
  rw [hcm p m hp hm, hcm p k hp hk, map_mul]
  have h1 : g p * (starRingEnd ℂ) (g p) = 1 := by
    rw [Complex.mul_conj]
    rw [show Complex.normSq (g p) = ‖g p‖ ^ 2 from by
      rw [Complex.sq_norm]]
    rw [huni p]
    norm_num
  calc g p * g m * ((starRingEnd ℂ) (g p) * (starRingEnd ℂ) (g k))
      = (g p * (starRingEnd ℂ) (g p)) * (g m * (starRingEnd ℂ) (g k)) := by ring
    _ = g m * (starRingEnd ℂ) (g k) := by rw [h1, one_mul]

/-- Generalized weight comparison: the `1/n ↦ (1/q)·(1/(n/q))` replacement costs at
most `2r/q²` over **any** finite set of naturals from the residue class `r (q)` lying
above `q` — the sub-window form the Proposition-`conv` chain needs. -/
theorem norm_sum_div_residue_sub_le' {q r : ℕ} (hq : 0 < q) (hr : r < q)
    {F : ℕ → ℂ} (hF : ∀ n, ‖F n‖ ≤ 1) {T : Finset ℕ}
    (hT : ∀ n ∈ T, q ≤ n ∧ n % q = r) :
    ‖(∑ n ∈ T, F n / (n : ℂ)) - ∑ n ∈ T, F n / (q : ℂ) / ((n / q : ℕ) : ℂ)‖
      ≤ 2 * r / q ^ 2 := by
  classical
  rw [← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ n ∈ T, ‖F n / (n : ℂ) - F n / (q : ℂ) / ((n / q : ℕ) : ℂ)‖
      ≤ (r : ℝ) / (q : ℝ) ^ 2 / ((n / q : ℕ) : ℝ) ^ 2 := by
    intro n hn
    obtain ⟨hqn, hmod⟩ := hT n hn
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
  have himg : ∑ n ∈ T, (r : ℝ) / (q : ℝ) ^ 2 / ((n / q : ℕ) : ℝ) ^ 2
      = ∑ m ∈ T.image (· / q), (r : ℝ) / (q : ℝ) ^ 2 / (m : ℝ) ^ 2 := by
    rw [Finset.sum_image]
    intro n hn m hm h
    have hn2 : n % q = r := (hT n (by
      have hn' : n ∈ T := hn
      exact hn')).2
    have hm2 : m % q = r := (hT m (by
      have hm' : m ∈ T := hm
      exact hm')).2
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
  have hsum0 : (0:ℝ) ≤ ∑ m ∈ T.image (· / q), (1:ℝ) / (m : ℝ) ^ 2 :=
    Finset.sum_nonneg fun m _ => by positivity
  have hcoef : (0:ℝ) ≤ (r : ℝ) / (q : ℝ) ^ 2 := by positivity
  have h2 : (r : ℝ) / (q : ℝ) ^ 2 * ∑ m ∈ T.image (· / q), (1:ℝ) / (m : ℝ) ^ 2
      ≤ (r : ℝ) / (q : ℝ) ^ 2 * 2 := by nlinarith
  have h3 : (r : ℝ) / (q : ℝ) ^ 2 * 2 = 2 * (r : ℝ) / (q : ℝ) ^ 2 := by ring
  linarith

/-- Iterated shift comparison: advancing the argument by `t` costs at most `3t/a`. -/
theorem norm_sum_div_shift_iterate_sub_le {F : ℕ → ℂ} (hF : ∀ n, ‖F n‖ ≤ 1)
    {a b : ℕ} (ha : 1 ≤ a) (t : ℕ) :
    ‖(∑ n ∈ Finset.Ioc a b, F (n + t) / (n : ℂ))
        - ∑ n ∈ Finset.Ioc a b, F n / (n : ℂ)‖ ≤ 3 * t / a := by
  induction t with
  | zero =>
    simp
  | succ u ih =>
    have hstep := norm_sum_div_shift_sub_le (F := fun n => F (n + u)) (b := b)
      (fun n => hF (n + u)) ha
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (∑ n ∈ Finset.Ioc a b, F (n + (u + 1)) / (n : ℂ))
      (∑ n ∈ Finset.Ioc a b, F (n + u) / (n : ℂ))
      (∑ n ∈ Finset.Ioc a b, F n / (n : ℂ))
    have hshape : ∑ n ∈ Finset.Ioc a b, F (n + (u + 1)) / (n : ℂ)
        = ∑ n ∈ Finset.Ioc a b, F ((n + 1) + u) / (n : ℂ) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      congr 2
      omega
    rw [hshape]
    have haR : (0 : ℝ) < (a : ℝ) := by
      have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
      linarith
    calc ‖(∑ n ∈ Finset.Ioc a b, F ((n + 1) + u) / (n : ℂ))
          - ∑ n ∈ Finset.Ioc a b, F n / (n : ℂ)‖
        ≤ ‖(∑ n ∈ Finset.Ioc a b, F ((n + 1) + u) / (n : ℂ))
            - ∑ n ∈ Finset.Ioc a b, F (n + u) / (n : ℂ)‖
          + ‖(∑ n ∈ Finset.Ioc a b, F (n + u) / (n : ℂ))
            - ∑ n ∈ Finset.Ioc a b, F n / (n : ℂ)‖ := by
          have := norm_sub_le_norm_sub_add_norm_sub
            (∑ n ∈ Finset.Ioc a b, F ((n + 1) + u) / (n : ℂ))
            (∑ n ∈ Finset.Ioc a b, F (n + u) / (n : ℂ))
            (∑ n ∈ Finset.Ioc a b, F n / (n : ℂ))
          linarith
      _ ≤ 3 / a + 3 * u / a := add_le_add hstep ih
      _ = 3 * (u + 1) / a := by
          field_simp
          ring
      _ = 3 * ((u + 1 : ℕ) : ℝ) / a := by push_cast; ring

/-- **The exact `p`-division identity for conjugate-pair correlations** (the core of
eq. (toc) in arXiv:1509.05422, Proposition `conv`): on the class `p ∣ m`, the
log-weighted correlation sum collapses **exactly** to `1/p` times the correlation sum
at the divided scale — the weights satisfy `1/m = (1/p)·(1/(m/p))` with no error, and
the conjugate-pair dilation identity has no error. The `a`-congruence rides along
untouched. -/
theorem sum_conjPair_pDiv_eq {g : ℕ → ℂ} (hcm : CompletelyMultiplicativeC g)
    (huni : Unimodular g) {p : ℕ} (hp : p ≠ 0) {a c h : ℕ} {A B : ℕ} :
    ∑ m ∈ ((Finset.Ioc A B).filter (fun m => m % a = c)).filter (fun m => m % p = 0),
        g m * (starRingEnd ℂ) (g (m + p * h)) / (m : ℂ)
      = (1 / (p : ℂ)) * ∑ m' ∈ (((Finset.Ioc A B).filter (fun m => m % a = c)).filter
            (fun m => m % p = 0)).image (· / p),
          g m' * (starRingEnd ℂ) (g (m' + h)) / (m' : ℂ) := by
  classical
  set T := ((Finset.Ioc A B).filter (fun m => m % a = c)).filter (fun m => m % p = 0)
    with hT
  -- membership facts on the p-class
  have hmem : ∀ m ∈ T, 1 ≤ m ∧ m % p = 0 := by
    intro m hm
    rw [hT, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc] at hm
    exact ⟨by omega, hm.2⟩
  -- reindex through the quotient map (injective on the p-class)
  have hinj : ∀ x ∈ T, ∀ y ∈ T, x / p = y / p → x = y := by
    intro x hx y hy hxy
    have hx2 := (hmem x hx).2
    have hy2 := (hmem y hy).2
    calc x = p * (x / p) + x % p := (Nat.div_add_mod x p).symm
      _ = p * (y / p) + y % p := by rw [hxy, hx2, hy2]
      _ = y := Nat.div_add_mod y p
  rw [Finset.mul_sum]
  rw [Finset.sum_image (fun x hx y hy h' => hinj x hx y hy h')]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨hm1, hmp⟩ := hmem m hm
  -- reconstruct m = p·(m/p)
  have hm_eq : m = p * (m / p) := by
    have h3 := Nat.div_add_mod m p
    omega
  have hm'1 : 1 ≤ m / p := by
    rcases Nat.eq_zero_or_pos (m / p) with h0 | h1
    · rw [h0, Nat.mul_zero] at hm_eq
      omega
    · exact h1
  -- the correlation collapses exactly
  have hval : g m * (starRingEnd ℂ) (g (m + p * h))
      = g (m / p) * (starRingEnd ℂ) (g (m / p + h)) := by
    have harg : m + p * h = p * (m / p + h) := by
      rw [show p * (m / p + h) = p * (m / p) + p * h from by ring, ← hm_eq]
    have hd := conjPair_dilate hcm huni (m := m / p) (k := m / p + h) hp
      (by omega) (by omega)
    rw [← hm_eq] at hd
    rw [harg]
    exact hd
  -- the weight collapses exactly
  have hw : ((m : ℂ))⁻¹ = (1 / (p : ℂ)) * ((m / p : ℕ) : ℂ)⁻¹ := by
    have hpC : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hp
    have hm'C : (((m / p : ℕ) : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (by omega : m / p ≠ 0)
    rw [show ((m : ℕ) : ℂ) = ((p : ℕ) : ℂ) * (((m / p : ℕ) : ℕ) : ℂ) from by
      rw [← Nat.cast_mul]
      exact_mod_cast hm_eq]
    field_simp
  rw [div_eq_mul_inv, div_eq_mul_inv, hval, hw]
  ring

/-- **The image window, characterized exactly**: dividing the `p`-multiples of a
congruence-filtered window `(A, B]` by `p` gives the window `(A/p, B/p]` filtered by
the dilated congruence — with no boundary error. -/
theorem image_pDiv_filter_eq {p : ℕ} (hp : 0 < p) (a c A B : ℕ) :
    (((Finset.Ioc A B).filter (fun m => m % a = c)).filter
        (fun m => m % p = 0)).image (· / p)
      = (Finset.Ioc (A / p) (B / p)).filter (fun m' => (p * m') % a = c) := by
  classical
  ext m'
  rw [Finset.mem_image, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc] at hm
    obtain ⟨⟨⟨hAm, hmB⟩, hma⟩, hmp⟩ := hm
    have hm_eq : m = p * (m / p) := by
      have h3 := Nat.div_add_mod m p
      omega
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul hp]
      calc A < m := hAm
        _ = m / p * p := by rw [Nat.mul_comm] at hm_eq; omega
    · rw [Nat.le_div_iff_mul_le hp]
      calc m / p * p = m := by rw [Nat.mul_comm] at hm_eq; omega
        _ ≤ B := hmB
    · rw [← hm_eq]
      exact hma
  · rintro ⟨⟨hA, hB⟩, hc⟩
    refine ⟨p * m', ?_, by
      rw [Nat.mul_div_cancel_left m' hp]⟩
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨⟨?_, ?_⟩, hc⟩, by
      rw [Nat.mul_mod_right]⟩
    · rw [Nat.div_lt_iff_lt_mul hp] at hA
      rw [Nat.mul_comm] at hA
      exact hA
    · rw [Nat.le_div_iff_mul_le hp] at hB
      rw [Nat.mul_comm] at hB
      exact hB

/-- The affine image window, characterized exactly: `n ↦ a·n + b` carries `(A, B]`
onto the `b`-class of `(aA+b, aB+b]`. -/
theorem image_affine_eq {a : ℕ} (ha : 0 < a) (b A B : ℕ) :
    (Finset.Ioc A B).image (fun n => a * n + b)
      = (Finset.Ioc (a * A + b) (a * B + b)).filter (fun m => m % a = b % a) := by
  classical
  ext m
  rw [Finset.mem_image, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [Finset.mem_Ioc] at hn
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have h1 : a * A < a * n := (Nat.mul_lt_mul_left ha).mpr hn.1
      omega
    · have h2 : a * n ≤ a * B := Nat.mul_le_mul_left a hn.2
      omega
    · rw [Nat.add_comm, Nat.add_mul_mod_self_left]
  · rintro ⟨⟨hAm, hmB⟩, hmod⟩
    have hbm : b ≤ m := by omega
    have hdvd : a ∣ m - b := (Nat.modEq_iff_dvd' hbm).mp (Nat.ModEq.symm hmod)
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k, ?_, by omega⟩
    rw [Finset.mem_Ioc]
    constructor
    · have h1 : a * A < a * k := by omega
      exact Nat.lt_of_mul_lt_mul_left h1
    · have h2 : a * k ≤ a * B := by omega
      exact Nat.le_of_mul_le_mul_left h2 ha

/-- **The affine conversion** (interface-form ↔ residue-filtered form): the
interface's correlation `∑ F(a·n+b)/n` matches `a` times the residue-filtered
log-uniform sum, at total cost `2b/a` — the paper's passage from eq. (face) to
eq. (face-2). -/
theorem norm_sum_affine_sub_le {F : ℕ → ℂ} (hF : ∀ n, ‖F n‖ ≤ 1)
    {a b A B : ℕ} (ha : 0 < a) (hA : 1 ≤ A) :
    ‖(∑ n ∈ Finset.Ioc A B, F (a * n + b) / (n : ℂ))
        - (a : ℂ) * ∑ m ∈ (Finset.Ioc (a * A + b) (a * B + b)).filter
            (fun m => m % a = b % a), F m / (m : ℂ)‖ ≤ 2 * b / a := by
  classical
  -- reindex the filtered sum through the affine image
  have himg : ∑ m ∈ (Finset.Ioc (a * A + b) (a * B + b)).filter
        (fun m => m % a = b % a), F m / (m : ℂ)
      = ∑ n ∈ Finset.Ioc A B, F (a * n + b) / ((a * n + b : ℕ) : ℂ) := by
    rw [← image_affine_eq ha b A B]
    refine Finset.sum_image fun x _ y _ h => ?_
    have h' : a * x + b = a * y + b := h
    have h2 : a * x = a * y := by omega
    exact Nat.eq_of_mul_eq_mul_left ha h2
  rw [himg, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ n ∈ Finset.Ioc A B,
      ‖F (a * n + b) / (n : ℂ)
          - (a : ℂ) * (F (a * n + b) / ((a * n + b : ℕ) : ℂ))‖
        ≤ (b : ℝ) / (a : ℝ) / (n : ℝ) ^ 2 := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn1 : 1 ≤ n := by omega
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
    have hanb : (0 : ℝ) < (a : ℝ) * (n : ℝ) + (b : ℝ) := by positivity
    have hfac : F (a * n + b) / (n : ℂ)
        - (a : ℂ) * (F (a * n + b) / ((a * n + b : ℕ) : ℂ))
        = F (a * n + b) * ((1 : ℂ) / (n : ℂ) - (a : ℂ) / ((a * n + b : ℕ) : ℂ)) := by
      field_simp
    rw [hfac, norm_mul]
    have hcast : (1 : ℂ) / (n : ℂ) - (a : ℂ) / ((a * n + b : ℕ) : ℂ)
        = (((1 : ℝ) / (n : ℝ) - (a : ℝ) / ((a : ℝ) * n + b) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    have hval : (1 : ℝ) / (n : ℝ) - (a : ℝ) / ((a : ℝ) * n + b)
        = (b : ℝ) / ((n : ℝ) * ((a : ℝ) * n + b)) := by
      field_simp
      ring
    rw [hval, abs_of_nonneg (by positivity)]
    have hbound : (b : ℝ) / ((n : ℝ) * ((a : ℝ) * n + b))
        ≤ (b : ℝ) / (a : ℝ) / (n : ℝ) ^ 2 := by
      rw [div_div]
      refine div_le_div_of_nonneg_left hb0 (by positivity) ?_
      calc (a : ℝ) * (n : ℝ) ^ 2 = (n : ℝ) * ((a : ℝ) * n) := by ring
        _ ≤ (n : ℝ) * ((a : ℝ) * n + b) := by nlinarith
    have h1 := hF (a * n + b)
    have h0 : (0 : ℝ) ≤ (b : ℝ) / ((n : ℝ) * ((a : ℝ) * n + b)) := by positivity
    nlinarith [hbound]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hfinal : ∑ n ∈ Finset.Ioc A B, (b : ℝ) / (a : ℝ) / (n : ℝ) ^ 2
      = (b : ℝ) / (a : ℝ) * ∑ n ∈ Finset.Ioc A B, (1 : ℝ) / (n : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hfinal]
  have hutil := sum_one_div_sq_le_two (Finset.Ioc A B)
  have hsum0 : (0 : ℝ) ≤ ∑ n ∈ Finset.Ioc A B, (1 : ℝ) / (n : ℝ) ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  have hcoef : (0 : ℝ) ≤ (b : ℝ) / (a : ℝ) := by positivity
  have h2 : (b : ℝ) / (a : ℝ) * ∑ n ∈ Finset.Ioc A B, (1 : ℝ) / (n : ℝ) ^ 2
      ≤ (b : ℝ) / (a : ℝ) * 2 := by nlinarith
  have h3 : (b : ℝ) / (a : ℝ) * 2 = 2 * (b : ℝ) / (a : ℝ) := by ring
  linarith

/-- **Harmonic upper bound**, sharp telescoping form: `∑_{c < n ≤ d} 1/n ≤ log d − log c`
for `1 ≤ c` (each `1/n ≤ log n − log(n−1)` from `log t ≤ t − 1` at `t = (n−1)/n`). -/
theorem sum_one_div_Ioc_le {c d : ℕ} (hc : 1 ≤ c) (hcd : c ≤ d) :
    ∑ n ∈ Finset.Ioc c d, (1 : ℝ) / n ≤ Real.log d - Real.log c := by
  have hterm : ∀ n ∈ Finset.Ioc c d,
      (1 : ℝ) / n ≤ Real.log n - Real.log ((n - 1 : ℕ) : ℝ) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn2 : 2 ≤ n := by omega
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      linarith
    have hn1R : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
      ring
    have hn10 : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      linarith
    have hlog := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < ((n : ℝ) - 1) / (n : ℝ) by positivity)
    rw [Real.log_div (by linarith) (ne_of_gt hn0)] at hlog
    have hval : ((n : ℝ) - 1) / (n : ℝ) - 1 = -(1 / (n : ℝ)) := by
      field_simp
      ring
    rw [hval] at hlog
    rw [hn1R]
    linarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  -- telescoping closed form
  have hclosed : ∀ e : ℕ, c ≤ e →
      ∑ n ∈ Finset.Ioc c e, (Real.log n - Real.log ((n - 1 : ℕ) : ℝ))
        = Real.log e - Real.log c := by
    intro e he
    induction e with
    | zero =>
      have : c = 0 := by omega
      omega
    | succ f ihf =>
      rcases Nat.lt_or_ge f c with hf | hf
      · have hfe : f + 1 = c := by omega
        rw [← hfe, Finset.Ioc_self, Finset.sum_empty]
        rw [hfe]
        ring
      · rw [Finset.sum_Ioc_succ_top (by omega), ihf hf]
        have hcast : ((f + 1 - 1 : ℕ) : ℝ) = (f : ℝ) := by
          push_cast
          ring
      -- wait: (f+1) - 1 = f in ℕ: Nat.add_sub_cancel ✓ so the last term is log(f+1) − log f
        rw [show ((f + 1 : ℕ) - 1 : ℕ) = f from by omega]
        push_cast
        ring
  rw [hclosed d hcd]

/-- The `r`-general divided image window: the quotients of the `r (q)`-class of
`(A, B]` form exactly `((A−r)/q, (B−r)/q]`, provided `r ≤ A`. -/
theorem image_div_filter_eq {q : ℕ} (hq : 0 < q) {r : ℕ} (hr : r < q) (A B : ℕ)
    (hrA : r ≤ A) :
    ((Finset.Ioc A B).filter (fun n => n % q = r)).image (· / q)
      = Finset.Ioc ((A - r) / q) ((B - r) / q) := by
  classical
  ext n'
  rw [Finset.mem_image, Finset.mem_Ioc]
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨hAn, hnB⟩, hmod⟩ := hn
    have hrn : r ≤ n := by
      have := Nat.mod_le n q
      omega
    have hn_eq : n = q * (n / q) + r := by
      have h3 := Nat.div_add_mod n q
      omega
    constructor
    · rw [Nat.div_lt_iff_lt_mul hq]
      have h1 : A - r < q * (n / q) := by omega
      rw [Nat.mul_comm] at h1
      exact h1
    · rw [Nat.le_div_iff_mul_le hq]
      have h2 : q * (n / q) ≤ B - r := by omega
      rw [Nat.mul_comm] at h2
      exact h2
  · rintro ⟨hA', hB'⟩
    refine ⟨q * n' + r, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Ioc]
      rw [Nat.div_lt_iff_lt_mul hq] at hA'
      rw [Nat.le_div_iff_mul_le hq] at hB'
      have hsub : A - r + r = A := Nat.sub_add_cancel hrA
      have hsub2 : B - r + r = B ∨ (B - r = 0 ∧ B ≤ r) := by omega
      have hcomm : n' * q = q * n' := Nat.mul_comm n' q
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · omega
      · omega
      · rw [Nat.add_comm, Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt hr
    · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hq]
      have h0 : r / q = 0 := Nat.div_eq_of_lt hr
      omega

/-- Windows nest after division: helper facts for the `(A, B]` vs `(A/p, B/p]`
comparison. -/
theorem log_div_window_le {p A : ℕ} (hp : 2 ≤ p) (hA : p ≤ A) :
    Real.log A - Real.log (A / p : ℕ) ≤ Real.log (2 * p) := by
  have hp0 : 0 < p := by omega
  have hA0 : (0 : ℝ) < (A : ℝ) := by
    have : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast le_trans hp hA
    linarith
  have hq1 : 1 ≤ A / p := (Nat.one_le_div_iff hp0).mpr hA
  have hq0 : (0 : ℝ) < ((A / p : ℕ) : ℝ) := by exact_mod_cast hq1
  rw [← Real.log_div (ne_of_gt hA0) (ne_of_gt hq0)]
  refine Real.log_le_log (by positivity) ?_
  -- A ≤ p·(A/p) + p ≤ 2p·(A/p)
  have hA2 : A ≤ 2 * p * (A / p) := by
    have hmod := Nat.div_add_mod A p
    have hlt : A % p < p := Nat.mod_lt _ hp0
    have h2 : p ≤ p * (A / p) := Nat.le_mul_of_pos_right p hq1
    have h3 : 2 * p * (A / p) = 2 * (p * (A / p)) := by ring
    omega
  have hA2R : (A : ℝ) ≤ 2 * (p : ℝ) * ((A / p : ℕ) : ℝ) := by exact_mod_cast hA2
  rw [div_le_iff₀ hq0]
  nlinarith [hA2R]

set_option maxHeartbeats 800000 in
/-- **The per-`(p, j)` toc estimate** (eq. (toc) of arXiv:1509.05422, Proposition
`conv`, unit-dilation form): the `j`-shifted `p`-divisibility-filtered conjugate-pair
correlation is `(1/p)` times the base correlation, within `3j/A + (2 log p + 2)/p` —
the shift engine prices the `j`-offset, the `p`-division and image window are exact,
and the window restoration costs two `log(2p)` masses. -/
theorem norm_toc_sub_le {g : ℕ → ℂ} (hcm : CompletelyMultiplicativeC g)
    (huni : Unimodular g) {p : ℕ} (hp : 2 ≤ p) {h j A B : ℕ}
    (hA : p ≤ A) (hpB : p * A ≤ B) :
    ‖(∑ n ∈ Finset.Ioc A B,
          (if (n + j) % p = 0
            then g (n + j) * (starRingEnd ℂ) (g (n + j + p * h)) else 0) / (n : ℂ))
        - (1 / (p : ℂ)) * ∑ m ∈ Finset.Ioc A B,
            g m * (starRingEnd ℂ) (g (m + h)) / (m : ℂ)‖
      ≤ 3 * j / A + (2 * Real.log p + 2) / p := by
  classical
  have hp0 : 0 < p := by omega
  have hA1 : 1 ≤ A := le_trans (by omega) hA
  have hAR : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA1
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  -- the masked correlation, 1-bounded
  set G : ℕ → ℂ := fun m =>
    if m % p = 0 then g m * (starRingEnd ℂ) (g (m + p * h)) else 0 with hG
  have hG1 : ∀ m, ‖G m‖ ≤ 1 := by
    intro m
    rw [hG]
    dsimp only
    split_ifs with hcase
    · rw [norm_mul, RCLike.norm_conj, huni m, huni (m + p * h)]
      norm_num
    · rw [norm_zero]
      norm_num
  -- step 1: the j-shift
  have hshift := norm_sum_div_shift_iterate_sub_le (F := G) hG1 (b := B) hA1 j
  -- step 2: the un-shifted masked sum is the filtered sum
  have hfilter : ∑ m ∈ Finset.Ioc A B, G m / (m : ℂ)
      = ∑ m ∈ (Finset.Ioc A B).filter (fun m => m % p = 0),
          g m * (starRingEnd ℂ) (g (m + p * h)) / (m : ℂ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hG]
    dsimp only
    split_ifs with hcase
    · rfl
    · rw [zero_div]
  -- step 3: exact p-division through the trivial a = 1 layer
  have htriv : (Finset.Ioc A B).filter (fun m => m % p = 0)
      = ((Finset.Ioc A B).filter (fun m => m % 1 = 0)).filter
          (fun m => m % p = 0) := by
    congr 1
    exact (Finset.filter_true_of_mem fun m _ => Nat.mod_one m).symm
  have hpdiv : ∑ m ∈ (Finset.Ioc A B).filter (fun m => m % p = 0),
        g m * (starRingEnd ℂ) (g (m + p * h)) / (m : ℂ)
      = (1 / (p : ℂ)) * ∑ m' ∈ ((Finset.Ioc A B).filter
            (fun m => m % p = 0)).image (· / p),
          g m' * (starRingEnd ℂ) (g (m' + h)) / (m' : ℂ) := by
    rw [htriv, sum_conjPair_pDiv_eq hcm huni (by omega : p ≠ 0) (a := 1) (c := 0),
      ← htriv]
  -- step 4: the image window
  have himg : ((Finset.Ioc A B).filter (fun m => m % p = 0)).image (· / p)
      = Finset.Ioc (A / p) (B / p) := by
    have hraw := image_div_filter_eq hp0 (r := 0) hp0 A B (Nat.zero_le A)
    rw [Nat.sub_zero, Nat.sub_zero] at hraw
    exact hraw
  -- step 5: window restoration
  have hADp : A / p ≤ A := Nat.div_le_self A p
  have hABp : A ≤ B / p := by
    rw [Nat.le_div_iff_mul_le hp0]
    rw [Nat.mul_comm]
    exact hpB
  have hBpB : B / p ≤ B := Nat.div_le_self B p
  have hcorr1 : ∀ m : ℕ, 1 ≤ m →
      ‖g m * (starRingEnd ℂ) (g (m + h)) / (m : ℂ)‖ = 1 / (m : ℝ) := by
    intro m hm
    rw [norm_div, norm_mul, RCLike.norm_conj, huni m, huni (m + h),
      Complex.norm_natCast, one_mul]
  have hwin : ‖(∑ m' ∈ Finset.Ioc (A / p) (B / p),
        g m' * (starRingEnd ℂ) (g (m' + h)) / (m' : ℂ))
      - ∑ m ∈ Finset.Ioc A B, g m * (starRingEnd ℂ) (g (m + h)) / (m : ℂ)‖
      ≤ 2 * Real.log p + 2 := by
    have hsplit1 : Finset.Ioc (A / p) (B / p)
        = Finset.Ioc (A / p) A ∪ Finset.Ioc A (B / p) :=
      (Finset.Ioc_union_Ioc_eq_Ioc hADp hABp).symm
    have hsplit2 : Finset.Ioc A B
        = Finset.Ioc A (B / p) ∪ Finset.Ioc (B / p) B :=
      (Finset.Ioc_union_Ioc_eq_Ioc hABp hBpB).symm
    have hdisj1 : Disjoint (Finset.Ioc (A / p) A) (Finset.Ioc A (B / p)) := by
      refine Finset.disjoint_left.mpr fun m hm1 hm2 => ?_
      rw [Finset.mem_Ioc] at hm1 hm2
      omega
    have hdisj2 : Disjoint (Finset.Ioc A (B / p)) (Finset.Ioc (B / p) B) := by
      refine Finset.disjoint_left.mpr fun m hm1 hm2 => ?_
      rw [Finset.mem_Ioc] at hm1 hm2
      omega
    rw [hsplit1, hsplit2, Finset.sum_union hdisj1, Finset.sum_union hdisj2]
    rw [show ∀ x y z : ℂ, (x + y) - (y + z) = x - z from fun x y z => by ring]
    refine le_trans (norm_sub_le _ _) ?_
    have hmass1 : ‖∑ m ∈ Finset.Ioc (A / p) A,
        g m * (starRingEnd ℂ) (g (m + h)) / (m : ℂ)‖ ≤ Real.log p + 1 := by
      refine le_trans (norm_sum_le _ _) ?_
      have hAp1 : 1 ≤ A / p := (Nat.one_le_div_iff hp0).mpr hA
      have hle : ∀ m ∈ Finset.Ioc (A / p) A,
          ‖g m * (starRingEnd ℂ) (g (m + h)) / (m : ℂ)‖ = 1 / (m : ℝ) := by
        intro m hm
        rw [Finset.mem_Ioc] at hm
        exact hcorr1 m (by omega)
      rw [Finset.sum_congr rfl hle]
      refine le_trans (sum_one_div_Ioc_le hAp1 hADp) ?_
      have hld := log_div_window_le hp hA
      have hlog2 : Real.log 2 ≤ 1 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        linarith [Real.exp_one_gt_d9]
      have hsplit : Real.log (2 * (p : ℝ)) = Real.log 2 + Real.log p := by
        rw [Real.log_mul (by norm_num) (by positivity)]
      rw [hsplit] at hld
      linarith
    have hmass2 : ‖∑ m ∈ Finset.Ioc (B / p) B,
        g m * (starRingEnd ℂ) (g (m + h)) / (m : ℂ)‖ ≤ Real.log p + 1 := by
      refine le_trans (norm_sum_le _ _) ?_
      have hBp1 : 1 ≤ B / p := le_trans (le_trans hA1 hABp) (le_refl _)
      have hle : ∀ m ∈ Finset.Ioc (B / p) B,
          ‖g m * (starRingEnd ℂ) (g (m + h)) / (m : ℂ)‖ = 1 / (m : ℝ) := by
        intro m hm
        rw [Finset.mem_Ioc] at hm
        exact hcorr1 m (by omega)
      rw [Finset.sum_congr rfl hle]
      refine le_trans (sum_one_div_Ioc_le hBp1 hBpB) ?_
      have hld := log_div_window_le hp (le_trans hA (le_trans (Nat.le_mul_of_pos_left A hp0) hpB))
      have hlog2 : Real.log 2 ≤ 1 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        linarith [Real.exp_one_gt_d9]
      have hsplit : Real.log (2 * (p : ℝ)) = Real.log 2 + Real.log p := by
        rw [Real.log_mul (by norm_num) (by positivity)]
      rw [hsplit] at hld
      linarith
    linarith
  -- assemble: triangle through the un-shifted masked sum
  have hLHS : ∑ n ∈ Finset.Ioc A B,
      (if (n + j) % p = 0
        then g (n + j) * (starRingEnd ℂ) (g (n + j + p * h)) else 0) / (n : ℂ)
      = ∑ n ∈ Finset.Ioc A B, G (n + j) / (n : ℂ) := rfl
  have hmid : ∑ m ∈ Finset.Ioc A B, G m / (m : ℂ)
      = (1 / (p : ℂ)) * ∑ m' ∈ Finset.Ioc (A / p) (B / p),
          g m' * (starRingEnd ℂ) (g (m' + h)) / (m' : ℂ) := by
    rw [hfilter, hpdiv, himg]
  have hpnorm : ‖(1 / (p : ℂ))‖ = 1 / (p : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  rw [hLHS]
  calc ‖(∑ n ∈ Finset.Ioc A B, G (n + j) / (n : ℂ))
        - (1 / (p : ℂ)) * ∑ m ∈ Finset.Ioc A B,
            g m * (starRingEnd ℂ) (g (m + h)) / (m : ℂ)‖
      ≤ ‖(∑ n ∈ Finset.Ioc A B, G (n + j) / (n : ℂ))
          - ∑ m ∈ Finset.Ioc A B, G m / (m : ℂ)‖
        + ‖(∑ m ∈ Finset.Ioc A B, G m / (m : ℂ))
          - (1 / (p : ℂ)) * ∑ m ∈ Finset.Ioc A B,
              g m * (starRingEnd ℂ) (g (m + h)) / (m : ℂ)‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub
          (∑ n ∈ Finset.Ioc A B, G (n + j) / (n : ℂ))
          (∑ m ∈ Finset.Ioc A B, G m / (m : ℂ))
          ((1 / (p : ℂ)) * ∑ m ∈ Finset.Ioc A B,
            g m * (starRingEnd ℂ) (g (m + h)) / (m : ℂ))
        linarith
    _ ≤ 3 * j / A + (2 * Real.log p + 2) / p := by
        have h1 : ‖(∑ n ∈ Finset.Ioc A B, G (n + j) / (n : ℂ))
            - ∑ m ∈ Finset.Ioc A B, G m / (m : ℂ)‖ ≤ 3 * j / A := hshift
        have h2 : ‖(∑ m ∈ Finset.Ioc A B, G m / (m : ℂ))
            - (1 / (p : ℂ)) * ∑ m ∈ Finset.Ioc A B,
                g m * (starRingEnd ℂ) (g (m + h)) / (m : ℂ)‖
            ≤ (2 * Real.log p + 2) / p := by
          rw [hmid, ← mul_sub, norm_mul, hpnorm]
          have hp0R : (0 : ℝ) < (p : ℝ) := by linarith
          rw [div_eq_mul_inv (2 * Real.log p + 2), mul_comm (2 * Real.log p + 2),
            one_div]
          exact mul_le_mul_of_nonneg_left hwin (by positivity)
        linarith

/-- Conjugation symmetry of the two-point correlation: the two shift orders have
equal norms. -/
theorem norm_pair_sum_conj_symm (g : ℕ → ℂ) (b₁ b₂ : ℕ) (A B : ℕ) :
    ‖∑ n ∈ Finset.Ioc A B, g (n + b₁) * (starRingEnd ℂ) (g (n + b₂)) / (n : ℂ)‖
      = ‖∑ n ∈ Finset.Ioc A B,
          g (n + b₂) * (starRingEnd ℂ) (g (n + b₁)) / (n : ℂ)‖ := by
  rw [← RCLike.norm_conj (K := ℂ)
    (∑ n ∈ Finset.Ioc A B,
      g (n + b₂) * (starRingEnd ℂ) (g (n + b₁)) / (n : ℂ)), map_sum]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_div₀, map_mul, RingHomInvPair.comp_apply_eq, Complex.conj_natCast]
  ring

/-- **The `b`-shift reduction**: a large shifted-pair correlation forces a large
base-window correlation at shift `h`, at cost `3b₁/A`. -/
theorem shift_pair_window_ge {g : ℕ → ℂ} (huni : Unimodular g)
    {b₁ h A B : ℕ} (ha : 1 ≤ A) {X : ℝ}
    (hbig : X ≤ ‖∑ n ∈ Finset.Ioc A B,
      g (n + b₁) * (starRingEnd ℂ) (g (n + b₁ + h)) / (n : ℂ)‖) :
    X - 3 * b₁ / A
      ≤ ‖∑ m ∈ Finset.Ioc A B,
          g m * (starRingEnd ℂ) (g (m + h)) / (m : ℂ)‖ := by
  have hFb : ∀ m, ‖g m * (starRingEnd ℂ) (g (m + h))‖ ≤ 1 := by
    intro m
    rw [norm_mul, RCLike.norm_conj, huni m, huni (m + h), one_mul]
  have hshift := norm_sum_div_shift_iterate_sub_le
    (F := fun m => g m * (starRingEnd ℂ) (g (m + h))) hFb (b := B) ha b₁
  have htri := norm_sub_norm_le
    (∑ n ∈ Finset.Ioc A B,
      (fun m => g m * (starRingEnd ℂ) (g (m + h))) (n + b₁) / (n : ℂ))
    (∑ m ∈ Finset.Ioc A B, g m * (starRingEnd ℂ) (g (m + h)) / (m : ℂ))
  have halign : (∑ n ∈ Finset.Ioc A B,
      (fun m => g m * (starRingEnd ℂ) (g (m + h))) (n + b₁) / (n : ℂ))
      = ∑ n ∈ Finset.Ioc A B,
        g (n + b₁) * (starRingEnd ℂ) (g (n + b₁ + h)) / (n : ℂ) := rfl
  rw [halign] at hshift htri
  linarith [hshift, htri, hbig]

end MoltResearch
