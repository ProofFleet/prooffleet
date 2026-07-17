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

end MoltResearch
