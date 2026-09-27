import MoltResearch.Discrepancy.HalaszCapstone

/-!
# Track C: the Halász chain over ℂ (Track R, A.2 leg, A2-0)

The complex-valued mirror of the §3 Riesz/plain-sum Halász chain.  The
analytic layer (`HalaszTriple.lean`, `HalaszTripleG.lean`) is complex
end-to-end already; what needs mirroring is the ℝ-valued combinatorial
§3 chain (`tripleConvR` and its estimates) up through the capstone, so
that the plain-sum log-free Halász bound applies to the character
twists `g·χ̄` and archimedean twists `g·n^{−it}` that the [mrt]
Appendix-A mean-value layer feeds it.  Mirrors are added here as
`…C`-named copies (house rule: the 9.9k-line hosts stay untouched, new
units go in leaf files).
-/

namespace MoltResearch

open Real Finset in
/-- **The `k`-split, summand-free** (Track R, A2-0): the bookkeeping of
`tripleConvR_ksplit_le` over an abstract summand — the split never
looks inside the convolution, so the ℝ- and ℂ-chains share it. -/
theorem sum_ksplit_le (v : ℕ → ℝ) (K M : ℕ) (hKM : K ≤ M)
    (A T : ℝ)
    (hhead : ∀ k ∈ Finset.Icc 1 K, v k ≤ A)
    (htail : ∑ k ∈ Finset.Icc (K+1) M, v k ≤ T) :
    ∑ k ∈ Finset.Icc 1 M, v k ≤ (K:ℝ) * A + T := by
  classical
  have hsplit : Finset.Icc 1 M = Finset.Icc 1 K ∪ Finset.Icc (K+1) M := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 K) (Finset.Icc (K+1) M) := by
    refine Finset.disjoint_left.mpr fun k hk1 hk2 => ?_
    rw [Finset.mem_Icc] at hk1 hk2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have hhead' : ∑ k ∈ Finset.Icc 1 K, v k ≤ (K:ℝ) * A := by
    refine le_trans (Finset.sum_le_sum hhead) ?_
    simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
    have hcard : ((K + 1 - 1 : ℕ):ℝ) = (K:ℝ) := by
      simp
    rw [hcard]
  linarith [hhead', htail]


open ArithmeticFunction Finset in
/-- **The Riesz identity closes, over ℂ** (Track R, A2-0): the mirror
of `rieszMean_log_identity` for ℂ-valued completely multiplicative
`f` — with `R(y) = ∑_{n≤y} f(n)·log(y/n)` and
`R₂(y) = ∑_{n≤y} f(n)·log²(y/n)`,

  `R(y)·log y = ∑_{d≤y} f(d)·Λ(d)·R(y/d) + R₂(y)`.

Same three ingredients (`vonMangoldt_sum`, `sum_divisors_swap` — which
is `AddCommMonoid`-generic — and complete multiplicativity); the real
proof's closing `linarith` on the equality becomes
`linear_combination`, and the log-weights ride under `ofReal` with
`push_cast` discharging the cast algebra. -/
theorem rieszMean_log_identityC (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (y : ℝ) (hy : 0 < y) :
    (∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
        f n * ((Real.log y - Real.log (n:ℝ) : ℝ) : ℂ))
        * ((Real.log y : ℝ) : ℂ)
      = (∑ d ∈ Finset.Icc 1 ⌊y⌋₊, f d * ((vonMangoldt d : ℝ) : ℂ)
            * ∑ m ∈ Finset.Icc 1 ⌊y/(d:ℝ)⌋₊, f m
                * ((Real.log (y/(d:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ))
        + ∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
            f n * ((Real.log y - Real.log (n:ℝ) : ℝ) : ℂ)^2 := by
  classical
  set N : ℕ := ⌊y⌋₊ with hN_def
  -- Step 1: the two `R`-terms combine into the diagonal `log n`
  have hsplit : (∑ n ∈ Finset.Icc 1 N,
        f n * ((Real.log y - Real.log (n:ℝ) : ℝ) : ℂ))
        * ((Real.log y : ℝ) : ℂ)
      - ∑ n ∈ Finset.Icc 1 N,
          f n * ((Real.log y - Real.log (n:ℝ) : ℝ) : ℂ)^2
      = ∑ n ∈ Finset.Icc 1 N,
          f n * ((Real.log (n:ℝ) : ℝ) : ℂ)
            * ((Real.log y - Real.log (n:ℝ) : ℝ) : ℂ) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    ring
  -- Step 2: `log n = ∑_{d ∣ n} Λ(d)`
  have hlog : ∀ n ∈ Finset.Icc 1 N,
      f n * ((Real.log (n:ℝ) : ℝ) : ℂ)
          * ((Real.log y - Real.log (n:ℝ) : ℝ) : ℂ)
        = ∑ d ∈ n.divisors,
            ((vonMangoldt d : ℝ) : ℂ)
              * (f n * ((Real.log y - Real.log (n:ℝ) : ℝ) : ℂ)) := by
    intro n _
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, vonMangoldt_sum]
    ring
  -- Step 3: swap the order of summation
  have hswap := sum_divisors_swap N
    (fun d n => ((vonMangoldt d : ℝ) : ℂ)
      * (f n * ((Real.log y - Real.log (n:ℝ) : ℝ) : ℂ)))
  -- Step 4: complete multiplicativity and the log split
  have hinner : ∀ d ∈ Finset.Icc 1 N,
      (∑ m ∈ Finset.Icc 1 (N/d),
          ((vonMangoldt d : ℝ) : ℂ)
            * (f (d*m) * ((Real.log y - Real.log ((d*m : ℕ):ℝ) : ℝ) : ℂ)))
        = f d * ((vonMangoldt d : ℝ) : ℂ)
            * ∑ m ∈ Finset.Icc 1 ⌊y/(d:ℝ)⌋₊, f m
                * ((Real.log (y/(d:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd1 : 1 ≤ d := hd.1
    have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd1
    have hfloor : N/d = ⌊y/(d:ℝ)⌋₊ := by
      rw [hN_def, Nat.floor_div_natCast]
    rw [← hfloor, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    have hm1 : 1 ≤ m := hm.1
    have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
    have hcast : (((d*m : ℕ)):ℝ) = (d:ℝ) * (m:ℝ) := by push_cast; ring
    rw [hcm d m (by omega) (by omega), hcast,
      Real.log_mul (ne_of_gt hd0) (ne_of_gt hm0),
      Real.log_div (ne_of_gt hy) (ne_of_gt hd0)]
    push_cast
    ring
  -- assemble
  have hchain : ∑ n ∈ Finset.Icc 1 N,
      f n * ((Real.log (n:ℝ) : ℝ) : ℂ)
        * ((Real.log y - Real.log (n:ℝ) : ℝ) : ℂ)
      = ∑ d ∈ Finset.Icc 1 N, f d * ((vonMangoldt d : ℝ) : ℂ)
          * ∑ m ∈ Finset.Icc 1 ⌊y/(d:ℝ)⌋₊, f m
              * ((Real.log (y/(d:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl hlog, hswap, Finset.sum_congr rfl hinner]
  linear_combination hsplit + hchain


open Real Finset in
/-- **The Riesz triple convolution over ℂ** (Track R, A2-0): the mirror
of `tripleConvR` for ℂ-valued `f` — §3's central object, the
log-weights riding under `ofReal`. -/
noncomputable def tripleConvRC (f : ℕ → ℂ) (x : ℕ) (P : Finset ℕ) : ℂ :=
  ∑ p ∈ P, ((Real.log (p:ℝ) : ℂ) * f p / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ))
    * ∑ q ∈ (x/p).primesBelow, ((Real.log (q:ℝ) : ℂ) * f q)
        * ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
            f n * ((Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ) : ℝ) : ℂ)

open Finset in
/-- **The survivor sum decomposes over blocks, over ℂ** (Track R,
A2-0): `tripleConvRC` at the survivor set is the sum of its `K`
per-block values.  `survivor_sum_split` is `AddCommMonoid`-generic, so
the mirror is verbatim. -/
theorem tripleConvRC_survivor_split (f : ℕ → ℂ) (x y K : ℕ) (hx : 1 ≤ x)
    (hK : Real.exp (-(K:ℝ)) * Real.log (x:ℝ) < Real.log 2) :
    tripleConvRC f x ((((Finset.Icc 1 x).filter Nat.Prime).filter
        (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p))
      = ∑ k ∈ Finset.Icc 1 K,
          tripleConvRC f x
            (((Finset.Ico (blockLo x k) (blockHi x k)).filter
              Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p)) := by
  classical
  simp only [tripleConvRC]
  exact survivor_sum_split _ x y K hx hK


namespace ExpSums

open Real Finset in
/-- **The Riesz mean is the window sum, over ℂ** (Track R, A2-0): the
mirror of `rieszMean_eq_window_sum` — an identity, the window facts
staying real under `ofReal`. -/
theorem rieszMeanC_eq_window_sum (f : ℕ → ℂ) (y : ℝ) (hy : 0 < y) (N : ℕ)
    (hN : y ≤ (N:ℝ)) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, f n * ((Real.log y - Real.log (n:ℝ) : ℝ) : ℂ)
      = (y : ℂ) * ∑ n ∈ Finset.Icc 1 N, (f n/(n:ℂ))
          * ((rieszWindow (Real.log y - Real.log (n:ℝ)) : ℝ) : ℂ) := by
  classical
  rw [Finset.mul_sum]
  have hfl : ⌊y⌋₊ ≤ N := by
    have h1 := Nat.floor_le_of_le hN
    simpa using h1
  have hsub : Finset.Icc 1 ⌊y⌋₊ ⊆ Finset.Icc 1 N :=
    Finset.Icc_subset_Icc_right hfl
  -- terms above `y` vanish: the window is supported on `v > 0`
  have hzero : ∀ n ∈ Finset.Icc 1 N, n ∉ Finset.Icc 1 ⌊y⌋₊ →
      (y : ℂ) * ((f n/(n:ℂ))
        * ((rieszWindow (Real.log y - Real.log (n:ℝ)) : ℝ) : ℂ)) = 0 := by
    intro n hn hnot
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_Icc] at hnot
    push_neg at hnot
    have hgt : ⌊y⌋₊ < n := hnot hn.1
    have hyn : y < (n:ℝ) := by
      have h1 : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
      have h2 : ((⌊y⌋₊ : ℕ):ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast hgt
      linarith
    have hlt : Real.log y - Real.log (n:ℝ) < 0 := by
      have := Real.log_lt_log hy hyn
      linarith
    have hneg : ¬ (0 < Real.log y - Real.log (n:ℝ)) := by linarith
    rw [rieszWindow, if_neg hneg, Complex.ofReal_zero, mul_zero, mul_zero]
  rw [← Finset.sum_subset hsub hzero]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hn1 : 1 ≤ n := hn.1
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hnle : (n:ℝ) ≤ y := (Nat.le_floor_iff hy.le).mp hn.2
  rcases eq_or_lt_of_le hnle with heq | hlt
  · -- `n = y`: both sides vanish, the window at `0` and the log at `1`
    have hlog : Real.log y - Real.log (n:ℝ) = 0 := by rw [heq]; ring
    rw [hlog, rieszWindow]
    simp
  · have hpos : 0 < Real.log y - Real.log (n:ℝ) := by
      have := Real.log_lt_log hn0 hlt
      linarith
    rw [rieszWindow, if_pos hpos]
    have hexp : Real.exp (-(Real.log y - Real.log (n:ℝ))) = (n:ℝ)/y := by
      rw [show -(Real.log y - Real.log (n:ℝ))
          = Real.log (n:ℝ) - Real.log y from by ring,
        Real.exp_sub, Real.exp_log hn0, Real.exp_log hy]
    rw [hexp]
    have hyC : ((y:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hy)
    have hnC : ((n:ℕ):ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast
    field_simp

open Real Finset in
/-- **The trivial bound on the ℂ-Riesz mean** (Track R, A2-0): the
mirror of `norm_rieszMean_le` — `‖R_f(y)‖ ≤ y` for `‖f‖ ≤ 1`. -/
theorem norm_rieszMeanC_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (y : ℝ)
    (hy : 1 ≤ y) :
    ‖∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
        f n * ((Real.log y - Real.log (n:ℝ) : ℝ) : ℂ)‖ ≤ y := by
  classical
  have hy0 : (0:ℝ) < y := by linarith
  set M : ℕ := ⌊y⌋₊ with hM_def
  have hM1 : 1 ≤ M := Nat.le_floor (by exact_mod_cast hy)
  have hMR : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM1
  have hMy : (M:ℝ) ≤ y := Nat.floor_le hy0.le
  have hterm : ∀ n ∈ Finset.Icc 1 M,
      ‖f n * ((Real.log y - Real.log (n:ℝ) : ℝ) : ℂ)‖
        ≤ Real.log y - Real.log (n:ℝ) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn.1
    have hnM : (n:ℝ) ≤ (M:ℝ) := by exact_mod_cast hn.2
    have hny : (n:ℝ) ≤ y := le_trans hnM hMy
    have hnn : 0 ≤ Real.log y - Real.log (n:ℝ) := by
      have := Real.log_le_log hn0 hny
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
    calc ‖f n‖ * (Real.log y - Real.log (n:ℝ))
        ≤ 1 * (Real.log y - Real.log (n:ℝ)) :=
          mul_le_mul_of_nonneg_right (hf n) hnn
      _ = Real.log y - Real.log (n:ℝ) := one_mul _
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hsplit : ∑ n ∈ Finset.Icc 1 M, (Real.log y - Real.log (n:ℝ))
      = (M:ℝ)*(Real.log y - Real.log (M:ℝ))
        + ∑ n ∈ Finset.Icc 1 M, (Real.log (M:ℝ) - Real.log (n:ℝ)) := by
    have hpt : ∀ n ∈ Finset.Icc 1 M, Real.log y - Real.log (n:ℝ)
        = (Real.log y - Real.log (M:ℝ))
          + (Real.log (M:ℝ) - Real.log (n:ℝ)) := fun n _ => by ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib,
      Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    norm_num
  rw [hsplit]
  have hhead : (M:ℝ)*(Real.log y - Real.log (M:ℝ)) ≤ y - (M:ℝ) := by
    have hlog : Real.log y - Real.log (M:ℝ) = Real.log (y/(M:ℝ)) := by
      rw [Real.log_div (ne_of_gt hy0) (ne_of_gt hMR)]
    rw [hlog]
    have h2 : Real.log (y/(M:ℝ)) ≤ y/(M:ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    calc (M:ℝ) * Real.log (y/(M:ℝ)) ≤ (M:ℝ) * (y/(M:ℝ) - 1) :=
          mul_le_mul_of_nonneg_left h2 hMR.le
      _ = y - (M:ℝ) := by field_simp
  linarith [hhead, sum_log_ratio_le M]

open Real Finset in
/-- **The ℂ-Riesz window sum is at most `1`** (Track R, A2-0): the
mirror of `riesz_smoothed_sum_le_one`, through the mean rather than the
window, for the same reason. -/
theorem rieszC_smoothed_sum_le_one (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (y : ℝ) (hy : 1 ≤ y) (N : ℕ) (hN : y ≤ (N:ℝ)) :
    ‖∑ n ∈ Finset.Icc 1 N, (f n/(n:ℂ))
        * ((rieszWindow (Real.log y - Real.log (n:ℝ)) : ℝ) : ℂ)‖ ≤ 1 := by
  have hy0 : (0:ℝ) < y := by linarith
  have hreal := rieszMeanC_eq_window_sum f y hy0 N hN
  have htriv := norm_rieszMeanC_le f hf y hy
  rw [hreal, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hy0] at htriv
  by_contra hcon
  push_neg at hcon
  nlinarith [htriv, hcon, hy0]

end ExpSums


open Real Finset in
/-- **The ℂ-Riesz triple convolution, realised** (Track R, A2-0): the
mirror of `tripleConvR_eq_scaled` — termwise
`rieszMeanC_eq_window_sum` at `y = x/pq`, an identity with no `ρ` and
no edge budget. -/
theorem tripleConvRC_eq_scaled (f : ℕ → ℂ) (x : ℕ) (hx : 0 < x)
    (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) :
    tripleConvRC f x P
      = ∑ p ∈ P, ((Real.log (p:ℝ) : ℂ) * f p / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ))
          * ∑ q ∈ (x/p).primesBelow, ((Real.log (q:ℝ) : ℂ) * f q)
              * ((((x:ℝ)/((p:ℝ)*(q:ℝ)) : ℝ) : ℂ)
                * ∑ n ∈ Finset.Icc 1 x, (f n/(n:ℂ))
                    * ((ExpSums.rieszWindow
                        (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                          - Real.log (n:ℝ)) : ℝ) : ℂ)) := by
  classical
  have hxR : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx
  rw [tripleConvRC]
  refine Finset.sum_congr rfl fun p hp => ?_
  refine congrArg _ (Finset.sum_congr rfl fun q hq => ?_)
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hP p hp
  have hqp : q.Prime := (Nat.mem_primesBelow.mp hq).2
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hqp.pos
  have hy0 : (0:ℝ) < (x:ℝ)/((p:ℝ)*(q:ℝ)) := by positivity
  have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hP p hp
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hqp.one_lt.le
  have hyx : (x:ℝ)/((p:ℝ)*(q:ℝ)) ≤ (x:ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have hpq1 : (1:ℝ) ≤ (p:ℝ)*(q:ℝ) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hpq1 hxR.le]
  refine congrArg _ ?_
  exact ExpSums.rieszMeanC_eq_window_sum f ((x:ℝ)/((p:ℝ)*(q:ℝ))) hy0 x hyx


open Real Finset in
/-- **The discarded top-block weight, over ℂ** (Track R, A2-0): the
mirror of `discard_weight_le` —

  `‖log p·f(p)/log(x/p)‖·(2·log⌊x/p⌋) ≤ 2·log p`  for `2p ≤ x`. -/
theorem discard_weight_leC (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x p : ℕ) (hp : p.Prime) (h2p : 2*p ≤ x) :
    ‖(Real.log (p:ℝ) : ℂ) * f p / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ)‖
        * (2 * Real.log (((x/p : ℕ)):ℝ))
      ≤ 2 * Real.log (p:ℝ) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
  have hquot : (2:ℝ) ≤ (x:ℝ)/(p:ℝ) := by
    rw [le_div_iff₀ hp0]
    have hc : ((2*p : ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast h2p
    push_cast at hc; linarith
  have hL : (0:ℝ) < Real.log ((x:ℝ)/(p:ℝ)) := Real.log_pos (by linarith)
  have hlogp : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
  -- the floor's log is at most the quotient's
  have hfl : (((x/p : ℕ)):ℝ) ≤ (x:ℝ)/(p:ℝ) := Nat.cast_div_le
  have hfl0 : (0:ℝ) ≤ Real.log (((x/p : ℕ)):ℝ) :=
    Real.log_natCast_nonneg (x/p)
  have hlogfl : Real.log (((x/p : ℕ)):ℝ) ≤ Real.log ((x:ℝ)/(p:ℝ)) := by
    rcases eq_or_lt_of_le (Nat.cast_nonneg (α := ℝ) (x/p)) with h | h
    · rw [← h]; simpa using hL.le
    · exact Real.log_le_log h hfl
  -- the outer weight
  have hw : ‖(Real.log (p:ℝ) : ℂ) * f p / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ)‖
      ≤ Real.log (p:ℝ)/Real.log ((x:ℝ)/(p:ℝ)) := by
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hL,
      abs_of_nonneg hlogp]
    refine div_le_div_of_nonneg_right ?_ hL.le
    nlinarith [hf p, norm_nonneg (f p), hlogp]
  calc ‖(Real.log (p:ℝ) : ℂ) * f p / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ)‖
        * (2 * Real.log (((x/p : ℕ)):ℝ))
      ≤ (Real.log (p:ℝ)/Real.log ((x:ℝ)/(p:ℝ)))
          * (2 * Real.log (((x/p : ℕ)):ℝ)) := by
        refine mul_le_mul_of_nonneg_right hw (by linarith)
    _ ≤ (Real.log (p:ℝ)/Real.log ((x:ℝ)/(p:ℝ)))
          * (2 * Real.log ((x:ℝ)/(p:ℝ))) := by
        refine mul_le_mul_of_nonneg_left (by linarith) ?_
        positivity
    _ = 2 * Real.log (p:ℝ) := by
        field_simp


open Real Finset in
/-- **Vanishing beyond the scale, over ℂ** (Track R, A2-0): the mirror
of `smoothed_vanishes_of_lt_mul` — for `p·q > x` the scale falls below
`1` and the windowed sum dies term by term
(`window_vanishes_of_scale_le_one` is window-only, shared). -/
theorem smoothed_vanishes_of_lt_mulC (V : ℝ → ℝ)
    (hV0 : ∀ v, v ≤ 0 → V v = 0) (f : ℕ → ℂ) (x p q : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hpq : x < p*q) (S : Finset ℕ) :
    ∑ n ∈ S, (f n/(n:ℂ))
        * ((V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ)) : ℝ) : ℂ)
      = 0 := by
  refine Finset.sum_eq_zero fun n _ => ?_
  have hpq0 : (0:ℝ) < (p:ℝ)*(q:ℝ) := by
    have h1 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
    have h2 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
    positivity
  have hle : (x:ℝ)/((p:ℝ)*(q:ℝ)) ≤ 1 := by
    rw [div_le_one hpq0]
    have : ((x:ℕ):ℝ) ≤ ((p*q : ℕ):ℝ) := by exact_mod_cast hpq.le
    push_cast at this
    linarith
  have hnn : (0:ℝ) ≤ (x:ℝ)/((p:ℝ)*(q:ℝ)) := by positivity
  rw [ExpSums.window_vanishes_of_scale_le_one V hV0 _ hnn hle n,
    Complex.ofReal_zero, mul_zero]

open Real Finset in
/-- **The range enlargement costs one term, over ℂ** (Track R, A2-0):
the mirror of `enlargement_discard_le'` — every added prime beyond
`⌊x/p⌋` dies outright, and the single survivor costs `2·log⌊x/p⌋`
against the threaded unit-sum bound. -/
theorem enlargement_discard_le'C (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (V : ℝ → ℝ) (hV0 : ∀ v, v ≤ 0 → V v = 0)
    (x p : ℕ) (hp : 0 < p) (h2p : 2*p ≤ x)
    (S : Finset ℕ) (hS1 : ∀ n ∈ S, 1 ≤ n)
    (hsum : ∀ y : ℝ, 1 ≤ y → y ≤ 2 →
      ‖∑ n ∈ S, (f n/(n:ℂ)) * ((V (Real.log y - Real.log (n:ℝ)) : ℝ) : ℂ)‖
        ≤ 1)
    (Q : Finset ℕ) (hQp : ∀ q ∈ Q, q.Prime) :
    ‖∑ q ∈ Q \ (x/p).primesBelow, ((Real.log (q:ℝ) : ℂ) * f q)
        * ((((x:ℝ)/((p:ℝ)*(q:ℝ)) : ℝ) : ℂ)
          * ∑ n ∈ S, (f n/(n:ℂ))
              * ((V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                  - Real.log (n:ℝ)) : ℝ) : ℂ))‖
      ≤ 2 * Real.log (((x/p : ℕ)):ℝ) := by
  classical
  set A : Finset ℕ := Q \ (x/p).primesBelow with hA_def
  set m : ℕ := x/p with hm_def
  have hm2 : 2 ≤ m := by
    rw [hm_def]
    exact Nat.le_div_iff_mul_le hp |>.mpr (by omega)
  have hmR : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm2
  have hlogm : (0:ℝ) ≤ Real.log (m:ℝ) := Real.log_natCast_nonneg m
  -- every added prime but `m` zeroes the inner sum
  have hvanish : ∀ q ∈ A, q ∉ A.filter (fun q : ℕ => q = m) →
      ‖((Real.log (q:ℝ) : ℂ) * f q)
        * ((((x:ℝ)/((p:ℝ)*(q:ℝ)) : ℝ) : ℂ)
          * ∑ n ∈ S, (f n/(n:ℂ))
              * ((V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                  - Real.log (n:ℝ)) : ℝ) : ℂ))‖ = 0 := by
    intro q hq hnot
    simp only [Finset.mem_filter, not_and] at hnot
    have hqne : q ≠ m := hnot hq
    rw [hA_def, Finset.mem_sdiff] at hq
    have hqp : q.Prime := hQp q hq.1
    have hqm : m ≤ q := by
      by_contra hcon
      push_neg at hcon
      exact hq.2 (Nat.mem_primesBelow.mpr ⟨hcon, hqp⟩)
    have hqgt : m < q := lt_of_le_of_ne hqm (Ne.symm hqne)
    have hpq : x < p*q := by
      have hdm : p*m + x % p = x := by rw [hm_def]; exact Nat.div_add_mod x p
      have hmod : x % p < p := Nat.mod_lt _ hp
      have h1 : p*(m+1) ≤ p*q := Nat.mul_le_mul_left p hqgt
      have h2 : p*(m+1) = p*m + p := by ring
      omega
    rw [smoothed_vanishes_of_lt_mulC V hV0 f x p q hp hqp.pos hpq S,
      mul_zero, mul_zero, norm_zero]
  have hrestrict : (∑ q ∈ A, ‖((Real.log (q:ℝ) : ℂ) * f q)
        * ((((x:ℝ)/((p:ℝ)*(q:ℝ)) : ℝ) : ℂ)
          * ∑ n ∈ S, (f n/(n:ℂ))
              * ((V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                  - Real.log (n:ℝ)) : ℝ) : ℂ))‖)
      = ∑ q ∈ A.filter (fun q : ℕ => q = m),
          ‖((Real.log (q:ℝ) : ℂ) * f q)
            * ((((x:ℝ)/((p:ℝ)*(q:ℝ)) : ℝ) : ℂ)
              * ∑ n ∈ S, (f n/(n:ℂ))
                  * ((V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                      - Real.log (n:ℝ)) : ℝ) : ℂ))‖ :=
    (Finset.sum_subset (Finset.filter_subset _ _)
      (fun q hq hnot => hvanish q hq hnot)).symm
  -- the survivor's size
  have hterm : ∀ q ∈ A.filter (fun q : ℕ => q = m),
      ‖((Real.log (q:ℝ) : ℂ) * f q)
        * ((((x:ℝ)/((p:ℝ)*(q:ℝ)) : ℝ) : ℂ)
          * ∑ n ∈ S, (f n/(n:ℂ))
              * ((V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                  - Real.log (n:ℝ)) : ℝ) : ℂ))‖
      ≤ 2 * Real.log (m:ℝ) := by
    intro q hq
    simp only [Finset.mem_filter] at hq
    obtain ⟨-, hqm⟩ := hq
    rw [hqm]
    have hm0 : (0:ℝ) < (m:ℝ) := by linarith
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
    have hscale : (0:ℝ) < (x:ℝ)/((p:ℝ)*(m:ℝ)) := by
      have hx0 : (0:ℝ) < (x:ℝ) := by
        have : 0 < x := by omega
        exact_mod_cast this
      positivity
    have hcoef : ‖(Real.log (m:ℝ) : ℂ) * f m‖ ≤ Real.log (m:ℝ) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_natCast_nonneg m)]
      nlinarith [hf m, norm_nonneg (f m), Real.log_natCast_nonneg m]
    have hsc2 : (x:ℝ)/((p:ℝ)*(m:ℝ)) ≤ 2 := x_div_mul_floor_le_two x p hp h2p
    have hsc1 : (1:ℝ) ≤ (x:ℝ)/((p:ℝ)*(m:ℝ)) := by
      rw [le_div_iff₀ (by positivity)]
      have hpm : p * m ≤ x := by
        rw [hm_def, Nat.mul_comm]; exact Nat.div_mul_le_self x p
      have : ((p*m : ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast hpm
      push_cast at this; linarith
    have hsm := hsum _ hsc1 hsc2
    have hinner : ‖(((x:ℝ)/((p:ℝ)*(m:ℝ)) : ℝ) : ℂ)
        * ∑ n ∈ S, (f n/(n:ℂ))
            * ((V (Real.log ((x:ℝ)/((p:ℝ)*(m:ℝ)))
                - Real.log (n:ℝ)) : ℝ) : ℂ)‖ ≤ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hscale]
      calc (x:ℝ)/((p:ℝ)*(m:ℝ)) * ‖∑ n ∈ S, (f n/(n:ℂ))
              * ((V (Real.log ((x:ℝ)/((p:ℝ)*(m:ℝ)))
                  - Real.log (n:ℝ)) : ℝ) : ℂ)‖
          ≤ (x:ℝ)/((p:ℝ)*(m:ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left hsm hscale.le
        _ ≤ 2 := by linarith
    rw [norm_mul]
    calc ‖(Real.log (m:ℝ) : ℂ) * f m‖ * ‖(((x:ℝ)/((p:ℝ)*(m:ℝ)) : ℝ) : ℂ)
            * ∑ n ∈ S, (f n/(n:ℂ))
                * ((V (Real.log ((x:ℝ)/((p:ℝ)*(m:ℝ)))
                    - Real.log (n:ℝ)) : ℝ) : ℂ)‖
        ≤ Real.log (m:ℝ) * 2 :=
          mul_le_mul hcoef hinner (norm_nonneg _)
            (Real.log_natCast_nonneg m)
      _ = 2 * Real.log (m:ℝ) := by ring
  -- at most one survivor
  have hcard : (A.filter (fun q : ℕ => q = m)).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    simp only [Finset.mem_filter] at ha hb
    rw [ha.2, hb.2]
  refine le_trans (norm_sum_le _ _) ?_
  rw [hrestrict]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hc : ((A.filter (fun q : ℕ => q = m)).card : ℝ) ≤ 1 := by
    exact_mod_cast hcard
  nlinarith [hc, hlogm]


open Real Finset in
/-- **The range enlargement, summed, over ℂ** (Track R, A2-0): the
mirror of `enlargement_error_le'` — per `p` the discard costs
`2·log p` (`enlargement_discard_le'C` × `discard_weight_leC`), and
Chebyshev prices the sum at `2x·log 4`. -/
theorem enlargement_error_le'C (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (V : ℝ → ℝ) (hV0 : ∀ v, v ≤ 0 → V v = 0)
    (x : ℕ) (P : Finset ℕ) (hPp : ∀ p ∈ P, p.Prime) (h2p : ∀ p ∈ P, 2*p ≤ x)
    (S : Finset ℕ) (hS1 : ∀ n ∈ S, 1 ≤ n)
    (hsum : ∀ y : ℝ, 1 ≤ y → y ≤ 2 →
      ‖∑ n ∈ S, (f n/(n:ℂ)) * ((V (Real.log y - Real.log (n:ℝ)) : ℝ) : ℂ)‖
        ≤ 1)
    (Q : Finset ℕ) (hQp : ∀ q ∈ Q, q.Prime) :
    ‖∑ p ∈ P, ((Real.log (p:ℝ) : ℂ) * f p / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ))
        * ∑ q ∈ Q \ (x/p).primesBelow, ((Real.log (q:ℝ) : ℂ) * f q)
            * ((((x:ℝ)/((p:ℝ)*(q:ℝ)) : ℝ) : ℂ)
              * ∑ n ∈ S, (f n/(n:ℂ))
                  * ((V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                      - Real.log (n:ℝ)) : ℝ) : ℂ))‖
      ≤ 2 * (x:ℝ) * Real.log 4 := by
  classical
  refine le_trans (norm_sum_le _ _) ?_
  -- per `p`: the discard, then the cancellation
  have hstep : ∀ p ∈ P,
      ‖((Real.log (p:ℝ) : ℂ) * f p / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ))
        * ∑ q ∈ Q \ (x/p).primesBelow, ((Real.log (q:ℝ) : ℂ) * f q)
            * ((((x:ℝ)/((p:ℝ)*(q:ℝ)) : ℝ) : ℂ)
              * ∑ n ∈ S, (f n/(n:ℂ))
                  * ((V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                      - Real.log (n:ℝ)) : ℝ) : ℂ))‖
      ≤ 2 * Real.log (p:ℝ) := by
    intro p hp
    have hpp : p.Prime := hPp p hp
    rw [norm_mul]
    refine le_trans (mul_le_mul_of_nonneg_left
      (enlargement_discard_le'C f hf V hV0 x p hpp.pos (h2p p hp)
        S hS1 hsum Q hQp) (norm_nonneg _)) ?_
    exact discard_weight_leC f hf x p hpp (h2p p hp)
  refine le_trans (Finset.sum_le_sum hstep) ?_
  -- Chebyshev over the primes below `x`
  rw [← Finset.mul_sum]
  have hsub : P ⊆ x.primesBelow := by
    intro p hp
    have hpp : p.Prime := hPp p hp
    have h2 := h2p p hp
    have hp2 : 2 ≤ p := hpp.two_le
    exact Nat.mem_primesBelow.mpr ⟨by omega, hpp⟩
  have hmono : ∑ p ∈ P, Real.log (p:ℝ)
      ≤ ∑ p ∈ x.primesBelow, Real.log (p:ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => Real.log_natCast_nonneg i)
  have hcheb : ∑ p ∈ x.primesBelow, Real.log (p:ℝ) ≤ (x:ℝ) * Real.log 4 :=
    sum_log_primesBelow_le x
  linarith [hmono, hcheb]

open Real Finset in
/-- **The range enlargement as a difference, over ℂ** (Track R, A2-0):
the mirror of `enlargement_extend_le'` — `Finset.sum_sdiff` and the
summed error, verbatim. -/
theorem enlargement_extend_le'C (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (V : ℝ → ℝ) (hV0 : ∀ v, v ≤ 0 → V v = 0)
    (x : ℕ) (P : Finset ℕ) (hPp : ∀ p ∈ P, p.Prime) (h2p : ∀ p ∈ P, 2*p ≤ x)
    (S : Finset ℕ) (hS1 : ∀ n ∈ S, 1 ≤ n)
    (hsum : ∀ y : ℝ, 1 ≤ y → y ≤ 2 →
      ‖∑ n ∈ S, (f n/(n:ℂ)) * ((V (Real.log y - Real.log (n:ℝ)) : ℝ) : ℂ)‖
        ≤ 1)
    (Q : Finset ℕ) (hQp : ∀ q ∈ Q, q.Prime)
    (hQsub : ∀ p ∈ P, (x/p).primesBelow ⊆ Q) :
    ‖(∑ p ∈ P, ((Real.log (p:ℝ) : ℂ) * f p / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ))
        * ∑ q ∈ Q, ((Real.log (q:ℝ) : ℂ) * f q)
            * ((((x:ℝ)/((p:ℝ)*(q:ℝ)) : ℝ) : ℂ)
              * ∑ n ∈ S, (f n/(n:ℂ))
                  * ((V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                      - Real.log (n:ℝ)) : ℝ) : ℂ)))
      - (∑ p ∈ P, ((Real.log (p:ℝ) : ℂ) * f p / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ))
        * ∑ q ∈ (x/p).primesBelow, ((Real.log (q:ℝ) : ℂ) * f q)
            * ((((x:ℝ)/((p:ℝ)*(q:ℝ)) : ℝ) : ℂ)
              * ∑ n ∈ S, (f n/(n:ℂ))
                  * ((V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                      - Real.log (n:ℝ)) : ℝ) : ℂ)))‖
      ≤ 2 * (x:ℝ) * Real.log 4 := by
  classical
  have hsplit : (∑ p ∈ P, ((Real.log (p:ℝ) : ℂ) * f p
          / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ))
        * ∑ q ∈ Q, ((Real.log (q:ℝ) : ℂ) * f q)
            * ((((x:ℝ)/((p:ℝ)*(q:ℝ)) : ℝ) : ℂ)
              * ∑ n ∈ S, (f n/(n:ℂ))
                  * ((V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                      - Real.log (n:ℝ)) : ℝ) : ℂ)))
      - (∑ p ∈ P, ((Real.log (p:ℝ) : ℂ) * f p
          / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ))
        * ∑ q ∈ (x/p).primesBelow, ((Real.log (q:ℝ) : ℂ) * f q)
            * ((((x:ℝ)/((p:ℝ)*(q:ℝ)) : ℝ) : ℂ)
              * ∑ n ∈ S, (f n/(n:ℂ))
                  * ((V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                      - Real.log (n:ℝ)) : ℝ) : ℂ)))
      = ∑ p ∈ P, ((Real.log (p:ℝ) : ℂ) * f p
          / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ))
          * ∑ q ∈ Q \ (x/p).primesBelow, ((Real.log (q:ℝ) : ℂ) * f q)
              * ((((x:ℝ)/((p:ℝ)*(q:ℝ)) : ℝ) : ℂ)
                * ∑ n ∈ S, (f n/(n:ℂ))
                    * ((V (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                        - Real.log (n:ℝ)) : ℝ) : ℂ)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← mul_sub]
    congr 1
    rw [sub_eq_iff_eq_add]
    exact (Finset.sum_sdiff (hQsub p hp)).symm
  rw [hsplit]
  exact enlargement_error_le'C f hf V hV0 x P hPp h2p S hS1 hsum Q hQp


open Real Finset in
/-- **The raw ℂ-Riesz mean is priced by its scale** (Track R, A2-0):
the mirror of `abs_rieszMean_le` — `‖R_f(Y)‖ ≤ Y` at a real scale,
every inner sum of the R-world discard chain worth its scale and
nothing more. -/
theorem norm_rieszMeanC_le' (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (Y : ℝ) (hY : 1 ≤ Y) :
    ‖∑ m ∈ Finset.Icc 1 ⌊Y⌋₊,
        f m * ((Real.log Y - Real.log (m:ℝ) : ℝ) : ℂ)‖
      ≤ Y := by
  classical
  have hY0 : (0:ℝ) < Y := by linarith
  have hN1 : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  have hNY : ((⌊Y⌋₊ : ℕ):ℝ) ≤ Y := Nat.floor_le hY0.le
  have hN0 : (0:ℝ) < ((⌊Y⌋₊ : ℕ):ℝ) := by
    exact_mod_cast (by omega : 0 < ⌊Y⌋₊)
  have hterm : ∀ m ∈ Finset.Icc 1 ⌊Y⌋₊,
      ‖f m * ((Real.log Y - Real.log (m:ℝ) : ℝ) : ℂ)‖
      ≤ Real.log Y - Real.log (m:ℝ) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hmY : (m:ℝ) ≤ Y := le_trans (by exact_mod_cast hm.2) hNY
    have hpos : (0:ℝ) ≤ Real.log Y - Real.log (m:ℝ) := by
      have := Real.log_le_log hm0 hmY
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
    nlinarith [hf m, norm_nonneg (f m)]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hcard : (Finset.Icc 1 ⌊Y⌋₊).card = ⌊Y⌋₊ := by
    rw [Nat.card_Icc]
    omega
  have hsum_eq : ∑ m ∈ Finset.Icc 1 ⌊Y⌋₊,
      (Real.log Y - Real.log (m:ℝ))
      = (∑ m ∈ Finset.Icc 1 ⌊Y⌋₊,
          (Real.log ((⌊Y⌋₊ : ℕ):ℝ) - Real.log (m:ℝ)))
        + ((⌊Y⌋₊ : ℕ):ℝ) * (Real.log Y - Real.log ((⌊Y⌋₊ : ℕ):ℝ)) := by
    have h1 : ∑ m ∈ Finset.Icc 1 ⌊Y⌋₊, (Real.log Y - Real.log (m:ℝ))
        = ∑ m ∈ Finset.Icc 1 ⌊Y⌋₊,
            ((Real.log ((⌊Y⌋₊ : ℕ):ℝ) - Real.log (m:ℝ))
              + (Real.log Y - Real.log ((⌊Y⌋₊ : ℕ):ℝ))) :=
      Finset.sum_congr rfl fun m _ => by ring
    rw [h1, Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul]
  rw [hsum_eq]
  have h2 := sum_log_ratio_mass_le ⌊Y⌋₊ hN1
  have hdivpos : (0:ℝ) < Y/((⌊Y⌋₊ : ℕ):ℝ) := by positivity
  have h3 : Real.log Y - Real.log ((⌊Y⌋₊ : ℕ):ℝ)
      ≤ Y/((⌊Y⌋₊ : ℕ):ℝ) - 1 := by
    have hlg := Real.log_le_sub_one_of_pos hdivpos
    rw [Real.log_div (ne_of_gt hY0) (ne_of_gt hN0)] at hlg
    linarith
  have hcancel : ((⌊Y⌋₊ : ℕ):ℝ) * (Y/((⌊Y⌋₊ : ℕ):ℝ)) = Y :=
    mul_div_cancel₀ Y (ne_of_gt hN0)
  have h4 : ((⌊Y⌋₊ : ℕ):ℝ) * (Real.log Y - Real.log ((⌊Y⌋₊ : ℕ):ℝ))
      ≤ Y - ((⌊Y⌋₊ : ℕ):ℝ) := by
    have := mul_le_mul_of_nonneg_left h3 hN0.le
    nlinarith [this, hcancel]
  linarith [h2, h4]


open Real Finset ArithmeticFunction in
/-- **The ℂ-R-world mean value, prime-restricted** (Track R, A2-0): the
mirror of `rieszMean_mul_log_prime_restrict` —

  `‖R_f(x)·log x − ∑_p f(p)·Λ(p)·R-inner(x/p)‖ ≤ 35·x`,

`rieszMean_log_identityC`'s maiden application: the non-prime
Λ-support prices at `8x` against `norm_rieszMeanC_le'`, the diagonal
at `27x` against `sum_log_sub_sq_le`. -/
theorem rieszMeanC_mul_log_prime_restrict (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hcm : CompletelyMultiplicativeC f)
    (x : ℕ) (hx : 1 ≤ x) :
    ‖(∑ n ∈ Finset.Icc 1 x,
        f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
        * ((Real.log (x:ℝ) : ℝ) : ℂ)
      - ∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime,
          f p * ((vonMangoldt p : ℝ) : ℂ)
            * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
                f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ)‖
      ≤ 35 * (x:ℝ) := by
  classical
  have hx0 : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hid := rieszMean_log_identityC f hcm (x:ℝ) hx0
  rw [Nat.floor_natCast] at hid
  rw [hid]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 x) Nat.Prime
    (fun d => f d * ((vonMangoldt d : ℝ) : ℂ)
      * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(d:ℝ)⌋₊,
          f m * ((Real.log ((x:ℝ)/(d:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ))]
  -- the prime part cancels; the rest is the non-prime Λ-support + diagonal
  have hcancel : ∀ A B C : ℂ, (A + B) + C - A = B + C := by
    intro A B C
    ring
  rw [hcancel]
  refine le_trans (norm_add_le _ _) ?_
  -- the non-prime branch
  have hNP : ‖∑ d ∈ (Finset.Icc 1 x).filter (fun d => ¬ d.Prime),
      f d * ((vonMangoldt d : ℝ) : ℂ)
        * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(d:ℝ)⌋₊,
            f m * ((Real.log ((x:ℝ)/(d:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ)‖
      ≤ 8 * (x:ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ d ∈ (Finset.Icc 1 x).filter (fun d => ¬ d.Prime),
        ‖f d * ((vonMangoldt d : ℝ) : ℂ)
          * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(d:ℝ)⌋₊,
              f m * ((Real.log ((x:ℝ)/(d:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ)‖
        ≤ (x:ℝ) * (vonMangoldt d / (d:ℝ)) := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_Icc] at hd
      have hd1 : 1 ≤ d := hd.1.1
      have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd1
      have hdx : (d:ℝ) ≤ (x:ℝ) := by exact_mod_cast hd.1.2
      have hY1 : (1:ℝ) ≤ (x:ℝ)/(d:ℝ) := by
        rw [le_div_iff₀ hd0]
        linarith
      have hR := norm_rieszMeanC_le' f hf ((x:ℝ)/(d:ℝ)) hY1
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg vonMangoldt_nonneg]
      calc ‖f d‖ * vonMangoldt d
            * ‖∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(d:ℝ)⌋₊,
                f m * ((Real.log ((x:ℝ)/(d:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ)‖
          ≤ 1 * vonMangoldt d * ((x:ℝ)/(d:ℝ)) := by
            have h1 := hf d
            have h2 : (0:ℝ) ≤ vonMangoldt d := vonMangoldt_nonneg
            have h3 := norm_nonneg (∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(d:ℝ)⌋₊,
              f m * ((Real.log ((x:ℝ)/(d:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ))
            nlinarith [hR, mul_nonneg h2 h3, norm_nonneg (f d),
              mul_nonneg (norm_nonneg (f d)) h2]
        _ = (x:ℝ) * (vonMangoldt d / (d:ℝ)) := by
            field_simp
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    -- restrict to the proper prime powers, where `Λ` lives
    have hsupp : ∑ d ∈ (Finset.Icc 1 x).filter (fun d => ¬ d.Prime),
        vonMangoldt d / (d:ℝ)
        = ∑ d ∈ (Finset.Icc 1 x).filter
            (fun d => IsPrimePow d ∧ ¬ d.Prime),
            vonMangoldt d / (d:ℝ) := by
      refine (Finset.sum_subset ?_ ?_).symm
      · intro d hd
        rw [Finset.mem_filter] at hd ⊢
        exact ⟨hd.1, hd.2.2⟩
      · intro d hd hnd
        rw [Finset.mem_filter] at hd hnd
        have : ¬ IsPrimePow d := by
          intro hpp
          exact hnd ⟨hd.1, hpp, hd.2⟩
        rw [vonMangoldt_eq_zero_iff.mpr this, zero_div]
    rw [hsupp]
    have hmass := sum_vonMangoldt_div_properPrimePow_le x
    nlinarith [hmass, hx0]
  -- the diagonal
  have hD : ‖∑ n ∈ Finset.Icc 1 x,
      f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ)^2‖
      ≤ 27 * (x:ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n ∈ Finset.Icc 1 x,
        ‖f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ)^2‖
        ≤ (Real.log (x:ℝ) - Real.log (n:ℝ))^2 := by
      intro n _
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      nlinarith [hf n, norm_nonneg (f n), sq_nonneg
        (Real.log (x:ℝ) - Real.log (n:ℝ))]
    exact le_trans (Finset.sum_le_sum hterm) (sum_log_sub_sq_le x hx)
  linarith [hNP, hD]


open Real Finset ArithmeticFunction in
/-- **The ℂ-R-world head discard** (Track R, A2-0): the mirror of
`rieszMean_prime_head_le` — primes below `y` cost `x·(log y + 2)`
against the sharp Mertens mass. -/
theorem rieszMeanC_prime_head_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x y : ℕ) (hy : 2 ≤ y) :
    ‖∑ p ∈ ((Finset.Icc 1 x).filter Nat.Prime).filter (fun p => p < y),
        f p * ((vonMangoldt p : ℝ) : ℂ)
          * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
              f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ)‖
      ≤ (x:ℝ) * (Real.log (y:ℝ) + 2) := by
  classical
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ p ∈ ((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => p < y),
      ‖f p * ((vonMangoldt p : ℝ) : ℂ)
        * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
            f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ)‖
      ≤ (x:ℝ) * (Real.log (p:ℝ)/(p:ℝ)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hp1, hpx⟩, hpp⟩, -⟩ := hp
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
    have hY1 : (1:ℝ) ≤ (x:ℝ)/(p:ℝ) := by
      rw [le_div_iff₀ hp0]
      have : (p:ℝ) ≤ (x:ℝ) := by exact_mod_cast hpx
      linarith
    have hR := norm_rieszMeanC_le' f hf ((x:ℝ)/(p:ℝ)) hY1
    rw [vonMangoldt_apply_prime hpp, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_natCast_nonneg p)]
    have hlog0 : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
    calc ‖f p‖ * Real.log (p:ℝ)
          * ‖∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
              f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ)‖
        ≤ 1 * Real.log (p:ℝ) * ((x:ℝ)/(p:ℝ)) := by
          have h1 := hf p
          have h3 := norm_nonneg (∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
            f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ))
          nlinarith [hR, norm_nonneg (f p),
            mul_nonneg (norm_nonneg (f p)) hlog0,
            mul_nonneg hlog0 h3]
      _ = (x:ℝ) * (Real.log (p:ℝ)/(p:ℝ)) := by
          field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hsub : ((Finset.Icc 1 x).filter Nat.Prime).filter (fun p => p < y)
      ⊆ y.primesBelow := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    rw [Nat.mem_primesBelow]
    exact ⟨hp.2, hp.1.2⟩
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  have hmass := sum_log_div_primesBelow_le_sharp y hy
  have hx0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
  nlinarith [hmono, hmass, hx0]

open Real Finset ArithmeticFunction in
/-- **The ℂ-R-world tail discard** (Track R, A2-0): the mirror of
`rieszMean_prime_tail_le` — primes above `x/2` cost `2(x+1)·log 4`,
Chebyshev against the scale-2 inner. -/
theorem rieszMeanC_prime_tail_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x : ℕ) :
    ‖∑ p ∈ ((Finset.Icc 1 x).filter Nat.Prime).filter (fun p => x < 2*p),
        f p * ((vonMangoldt p : ℝ) : ℂ)
          * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
              f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ)‖
      ≤ 2*((x:ℝ)+1) * Real.log 4 := by
  classical
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ p ∈ ((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => x < 2*p),
      ‖f p * ((vonMangoldt p : ℝ) : ℂ)
        * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
            f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ)‖
      ≤ 2 * Real.log (p:ℝ) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hp1, hpx⟩, hpp⟩, h2p⟩ := hp
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
    have hY1 : (1:ℝ) ≤ (x:ℝ)/(p:ℝ) := by
      rw [le_div_iff₀ hp0]
      have : (p:ℝ) ≤ (x:ℝ) := by exact_mod_cast hpx
      linarith
    have hY2 : (x:ℝ)/(p:ℝ) ≤ 2 := by
      rw [div_le_iff₀ hp0]
      have : (x:ℝ) < 2*(p:ℝ) := by exact_mod_cast h2p
      linarith
    have hR := norm_rieszMeanC_le' f hf ((x:ℝ)/(p:ℝ)) hY1
    rw [vonMangoldt_apply_prime hpp, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_natCast_nonneg p)]
    have hlog0 : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
    have h3 := norm_nonneg (∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
      f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ))
    nlinarith [hR, hY2, hf p, norm_nonneg (f p),
      mul_nonneg (norm_nonneg (f p)) hlog0, mul_nonneg hlog0 h3]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hsub : ((Finset.Icc 1 x).filter Nat.Prime).filter (fun p => x < 2*p)
      ⊆ (x+1).primesBelow := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    rw [Nat.mem_primesBelow]
    exact ⟨by omega, hp.1.2⟩
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => Real.log_natCast_nonneg p)
  have hmass := sum_log_primesBelow_le (x+1)
  have hcast : ((x+1 : ℕ):ℝ) = (x:ℝ)+1 := by push_cast; ring
  rw [hcast] at hmass
  have hlog4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  nlinarith [hmono, hmass, hlog4]


open Real Finset ArithmeticFunction in
/-- **The ℂ-R-mean value at real scale** (Track R, A2-0): the mirror of
`rieszMean_mul_log_prime_restrict'` — the identity error is linear at
any real scale `Y ≥ 1`, the diagonal priced by `sum_log_sub_sq_le'`. -/
theorem rieszMeanC_mul_log_prime_restrict' (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hcm : CompletelyMultiplicativeC f)
    (Y : ℝ) (hY : 1 ≤ Y) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊Y⌋₊,
        f n * ((Real.log Y - Real.log (n:ℝ) : ℝ) : ℂ))
        * ((Real.log Y : ℝ) : ℂ)
      - ∑ p ∈ (Finset.Icc 1 ⌊Y⌋₊).filter Nat.Prime,
          f p * ((vonMangoldt p : ℝ) : ℂ)
            * ∑ m ∈ Finset.Icc 1 ⌊Y/(p:ℝ)⌋₊,
                f m * ((Real.log (Y/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ)‖
      ≤ 63 * Y := by
  classical
  have hY0 : (0:ℝ) < Y := by linarith
  have hid := rieszMean_log_identityC f hcm Y hY0
  rw [hid]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 ⌊Y⌋₊) Nat.Prime
    (fun d => f d * ((vonMangoldt d : ℝ) : ℂ)
      * ∑ m ∈ Finset.Icc 1 ⌊Y/(d:ℝ)⌋₊,
          f m * ((Real.log (Y/(d:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ))]
  have hcancel : ∀ A B C : ℂ, (A + B) + C - A = B + C := by
    intro A B C
    ring
  rw [hcancel]
  refine le_trans (norm_add_le _ _) ?_
  -- the non-prime branch
  have hNP : ‖∑ d ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun d => ¬ d.Prime),
      f d * ((vonMangoldt d : ℝ) : ℂ)
        * ∑ m ∈ Finset.Icc 1 ⌊Y/(d:ℝ)⌋₊,
            f m * ((Real.log (Y/(d:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ)‖
      ≤ 8 * Y := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ d ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun d => ¬ d.Prime),
        ‖f d * ((vonMangoldt d : ℝ) : ℂ)
          * ∑ m ∈ Finset.Icc 1 ⌊Y/(d:ℝ)⌋₊,
              f m * ((Real.log (Y/(d:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ)‖
        ≤ Y * (vonMangoldt d / (d:ℝ)) := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_Icc] at hd
      have hd1 : 1 ≤ d := hd.1.1
      have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd1
      have hdN : (d:ℝ) ≤ ((⌊Y⌋₊:ℕ):ℝ) := by exact_mod_cast hd.1.2
      have hdx : (d:ℝ) ≤ Y := le_trans hdN (Nat.floor_le hY0.le)
      have hY1 : (1:ℝ) ≤ Y/(d:ℝ) := by
        rw [le_div_iff₀ hd0]
        linarith
      have hR := norm_rieszMeanC_le' f hf (Y/(d:ℝ)) hY1
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg vonMangoldt_nonneg]
      calc ‖f d‖ * vonMangoldt d
            * ‖∑ m ∈ Finset.Icc 1 ⌊Y/(d:ℝ)⌋₊,
                f m * ((Real.log (Y/(d:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ)‖
          ≤ 1 * vonMangoldt d * (Y/(d:ℝ)) := by
            have h1 := hf d
            have h2 : (0:ℝ) ≤ vonMangoldt d := vonMangoldt_nonneg
            have h3 := norm_nonneg (∑ m ∈ Finset.Icc 1 ⌊Y/(d:ℝ)⌋₊,
              f m * ((Real.log (Y/(d:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ))
            nlinarith [hR, mul_nonneg h2 h3, norm_nonneg (f d),
              mul_nonneg (norm_nonneg (f d)) h2]
        _ = Y * (vonMangoldt d / (d:ℝ)) := by
            field_simp
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hsupp : ∑ d ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun d => ¬ d.Prime),
        vonMangoldt d / (d:ℝ)
        = ∑ d ∈ (Finset.Icc 1 ⌊Y⌋₊).filter
            (fun d => IsPrimePow d ∧ ¬ d.Prime),
            vonMangoldt d / (d:ℝ) := by
      refine (Finset.sum_subset ?_ ?_).symm
      · intro d hd
        rw [Finset.mem_filter] at hd ⊢
        exact ⟨hd.1, hd.2.2⟩
      · intro d hd hnd
        rw [Finset.mem_filter] at hd hnd
        have : ¬ IsPrimePow d := by
          intro hpp
          exact hnd ⟨hd.1, hpp, hd.2⟩
        rw [vonMangoldt_eq_zero_iff.mpr this, zero_div]
    rw [hsupp]
    have hmass := sum_vonMangoldt_div_properPrimePow_le ⌊Y⌋₊
    have hNY : ((⌊Y⌋₊:ℕ):ℝ) ≤ Y := Nat.floor_le hY0.le
    nlinarith [hmass, hY0, hNY]
  -- the diagonal
  have hD : ‖∑ n ∈ Finset.Icc 1 ⌊Y⌋₊,
      f n * ((Real.log Y - Real.log (n:ℝ) : ℝ) : ℂ)^2‖
      ≤ 55 * Y := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n ∈ Finset.Icc 1 ⌊Y⌋₊,
        ‖f n * ((Real.log Y - Real.log (n:ℝ) : ℝ) : ℂ)^2‖
        ≤ (Real.log Y - Real.log (n:ℝ))^2 := by
      intro n _
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      nlinarith [hf n, norm_nonneg (f n), sq_nonneg
        (Real.log Y - Real.log (n:ℝ))]
    exact le_trans (Finset.sum_le_sum hterm) (sum_log_sub_sq_le' Y hY)
  linarith [hNP, hD]


open Real Finset ArithmeticFunction in
/-- **The ℂ-R-mean value in `primesBelow` form** (Track R, A2-0): the
mirror of `rieszMean_mul_log_primesBelow_le` — the boundary prime
`⌊Y⌋` costs one more `Y`, giving the identity error in exactly the
range `tripleConvRC`'s inner sum uses. -/
theorem rieszMeanC_mul_log_primesBelow_le (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hcm : CompletelyMultiplicativeC f)
    (Y : ℝ) (hY : 1 ≤ Y) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊Y⌋₊,
        f n * ((Real.log Y - Real.log (n:ℝ) : ℝ) : ℂ))
        * ((Real.log Y : ℝ) : ℂ)
      - ∑ q ∈ (⌊Y⌋₊).primesBelow,
          f q * ((vonMangoldt q : ℝ) : ℂ)
            * ∑ m ∈ Finset.Icc 1 ⌊Y/(q:ℝ)⌋₊,
                f m * ((Real.log (Y/(q:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ)‖
      ≤ 64 * Y := by
  classical
  have hY0 : (0:ℝ) < Y := by linarith
  have hbase := rieszMeanC_mul_log_prime_restrict' f hf hcm Y hY
  by_cases hNp : (⌊Y⌋₊).Prime
  · have hset : (Finset.Icc 1 ⌊Y⌋₊).filter Nat.Prime
        = insert ⌊Y⌋₊ ((⌊Y⌋₊).primesBelow) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
        Nat.mem_primesBelow]
      constructor
      · rintro ⟨⟨hq1, hqN⟩, hqp⟩
        rcases eq_or_lt_of_le hqN with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, hqp⟩
      · rintro (rfl | ⟨hlt, hqp⟩)
        · exact ⟨⟨hNp.one_lt.le, le_refl _⟩, hNp⟩
        · exact ⟨⟨hqp.one_lt.le, hlt.le⟩, hqp⟩
    have hnotmem : ⌊Y⌋₊ ∉ (⌊Y⌋₊).primesBelow := by
      simp [Nat.mem_primesBelow]
    rw [hset, Finset.sum_insert hnotmem] at hbase
    have hN1 : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
    have hN0 : (0:ℝ) < ((⌊Y⌋₊:ℕ):ℝ) := by exact_mod_cast hN1
    have hNY : ((⌊Y⌋₊:ℕ):ℝ) ≤ Y := Nat.floor_le hY0.le
    have hY1' : (1:ℝ) ≤ Y/((⌊Y⌋₊:ℕ):ℝ) := by
      rw [le_div_iff₀ hN0]
      linarith
    have hR := norm_rieszMeanC_le' f hf (Y/((⌊Y⌋₊:ℕ):ℝ)) hY1'
    have hlogN : Real.log ((⌊Y⌋₊:ℕ):ℝ) ≤ ((⌊Y⌋₊:ℕ):ℝ) := by
      have := Real.log_le_sub_one_of_pos hN0
      linarith
    have hterm : ‖f ⌊Y⌋₊ * ((vonMangoldt ⌊Y⌋₊ : ℝ) : ℂ)
        * ∑ m ∈ Finset.Icc 1 ⌊Y/((⌊Y⌋₊:ℕ):ℝ)⌋₊,
            f m * ((Real.log (Y/((⌊Y⌋₊:ℕ):ℝ))
              - Real.log (m:ℝ) : ℝ) : ℂ)‖ ≤ Y := by
      rw [vonMangoldt_apply_prime hNp, norm_mul, norm_mul,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_natCast_nonneg _)]
      have hq0 : (0:ℝ) ≤ Y/((⌊Y⌋₊:ℕ):ℝ) := by positivity
      calc ‖f ⌊Y⌋₊‖ * Real.log ((⌊Y⌋₊:ℕ):ℝ)
            * ‖∑ m ∈ Finset.Icc 1 ⌊Y/((⌊Y⌋₊:ℕ):ℝ)⌋₊,
                f m * ((Real.log (Y/((⌊Y⌋₊:ℕ):ℝ))
                  - Real.log (m:ℝ) : ℝ) : ℂ)‖
          ≤ 1 * Real.log ((⌊Y⌋₊:ℕ):ℝ) * (Y/((⌊Y⌋₊:ℕ):ℝ)) := by
            have h1 := hf ⌊Y⌋₊
            have h2 : (0:ℝ) ≤ Real.log ((⌊Y⌋₊:ℕ):ℝ) :=
              Real.log_natCast_nonneg _
            have h3 := norm_nonneg (∑ m ∈ Finset.Icc 1 ⌊Y/((⌊Y⌋₊:ℕ):ℝ)⌋₊,
              f m * ((Real.log (Y/((⌊Y⌋₊:ℕ):ℝ))
                - Real.log (m:ℝ) : ℝ) : ℂ))
            nlinarith [hR, norm_nonneg (f ⌊Y⌋₊),
              mul_nonneg (norm_nonneg (f ⌊Y⌋₊)) h2,
              mul_nonneg h2 h3]
        _ ≤ ((⌊Y⌋₊:ℕ):ℝ) * (Y/((⌊Y⌋₊:ℕ):ℝ)) := by
            nlinarith [hlogN, hq0]
        _ = Y := by
            field_simp
    have hsplit : (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊,
          f n * ((Real.log Y - Real.log (n:ℝ) : ℝ) : ℂ))
          * ((Real.log Y : ℝ) : ℂ)
        - ∑ q ∈ (⌊Y⌋₊).primesBelow,
            f q * ((vonMangoldt q : ℝ) : ℂ)
              * ∑ m ∈ Finset.Icc 1 ⌊Y/(q:ℝ)⌋₊,
                  f m * ((Real.log (Y/(q:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ)
        = ((∑ n ∈ Finset.Icc 1 ⌊Y⌋₊,
              f n * ((Real.log Y - Real.log (n:ℝ) : ℝ) : ℂ))
              * ((Real.log Y : ℝ) : ℂ)
            - (f ⌊Y⌋₊ * ((vonMangoldt ⌊Y⌋₊ : ℝ) : ℂ)
                * ∑ m ∈ Finset.Icc 1 ⌊Y/((⌊Y⌋₊:ℕ):ℝ)⌋₊,
                    f m * ((Real.log (Y/((⌊Y⌋₊:ℕ):ℝ))
                      - Real.log (m:ℝ) : ℝ) : ℂ)
              + ∑ q ∈ (⌊Y⌋₊).primesBelow,
                  f q * ((vonMangoldt q : ℝ) : ℂ)
                    * ∑ m ∈ Finset.Icc 1 ⌊Y/(q:ℝ)⌋₊,
                        f m * ((Real.log (Y/(q:ℝ))
                          - Real.log (m:ℝ) : ℝ) : ℂ)))
          + f ⌊Y⌋₊ * ((vonMangoldt ⌊Y⌋₊ : ℝ) : ℂ)
              * ∑ m ∈ Finset.Icc 1 ⌊Y/((⌊Y⌋₊:ℕ):ℝ)⌋₊,
                  f m * ((Real.log (Y/((⌊Y⌋₊:ℕ):ℝ))
                    - Real.log (m:ℝ) : ℝ) : ℂ) := by
      ring
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    linarith [hbase, hterm]
  · have hset : (Finset.Icc 1 ⌊Y⌋₊).filter Nat.Prime
        = (⌊Y⌋₊).primesBelow := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesBelow]
      constructor
      · rintro ⟨⟨hq1, hqN⟩, hqp⟩
        rcases eq_or_lt_of_le hqN with h | h
        · exact absurd (h ▸ hqp) hNp
        · exact ⟨h, hqp⟩
      · rintro ⟨hlt, hqp⟩
        exact ⟨⟨hqp.one_lt.le, hlt.le⟩, hqp⟩
    rw [hset] at hbase
    linarith [hbase, hY0]


open Real Finset ArithmeticFunction in
/-- **The survivor sum becomes the ℂ-triple convolution** (Track R,
A2-0): the mirror of `rieszMean_survivors_to_tripleConvR` — iterating
the identity once more (`rieszMeanC_mul_log_primesBelow_le` at
`Y = x/p`) turns `∑_p f(p)Λ(p)·R(x/p)` into `tripleConvRC` at Mertens
cost; the scale floor `log(x/p) ≥ log 2` prices the division. -/
theorem rieszMeanC_survivors_to_tripleConvRC (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hcm : CompletelyMultiplicativeC f)
    (x y : ℕ) (hx : 1 ≤ x) :
    ‖∑ p ∈ (((Finset.Icc 1 x).filter Nat.Prime).filter
          (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p),
        f p * ((vonMangoldt p : ℝ) : ℂ)
          * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
              f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ)
      - tripleConvRC f x ((((Finset.Icc 1 x).filter Nat.Prime).filter
          (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p))‖
      ≤ 64 * (x:ℝ) / Real.log 2 * (Real.log ((x+1:ℕ):ℝ) + 2) := by
  classical
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [tripleConvRC, ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ p ∈ (((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p),
      ‖f p * ((vonMangoldt p : ℝ) : ℂ)
          * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
              f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ)
        - ((Real.log (p:ℝ) : ℂ) * f p / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ))
            * ∑ q ∈ (x/p).primesBelow, ((Real.log (q:ℝ) : ℂ) * f q)
                * ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
                    f n * ((Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                      - Real.log (n:ℝ) : ℝ) : ℂ)‖
      ≤ 64 * (x:ℝ) / Real.log 2 * (Real.log (p:ℝ)/(p:ℝ)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨⟨hp1, hpx⟩, hpp⟩, -⟩, h2p⟩ := hp
    have h2p' : 2*p ≤ x := by omega
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
    have hY2 : (2:ℝ) ≤ (x:ℝ)/(p:ℝ) := by
      rw [le_div_iff₀ hp0]
      exact_mod_cast h2p'
    have hY1 : (1:ℝ) ≤ (x:ℝ)/(p:ℝ) := by linarith
    have hlogY : Real.log 2 ≤ Real.log ((x:ℝ)/(p:ℝ)) :=
      Real.log_le_log (by norm_num) hY2
    have hlogY0 : (0:ℝ) < Real.log ((x:ℝ)/(p:ℝ)) :=
      lt_of_lt_of_le hlog2 hlogY
    have hfloor : ⌊(x:ℝ)/(p:ℝ)⌋₊ = x/p := by
      rw [Nat.floor_div_natCast, Nat.floor_natCast]
    rw [hfloor]
    have hb := rieszMeanC_mul_log_primesBelow_le f hf hcm
      ((x:ℝ)/(p:ℝ)) hY1
    rw [hfloor] at hb
    have hstuff : ∑ q ∈ (x/p).primesBelow,
        f q * ((vonMangoldt q : ℝ) : ℂ)
          * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)/(q:ℝ)⌋₊,
              f m * ((Real.log ((x:ℝ)/(p:ℝ)/(q:ℝ))
                - Real.log (m:ℝ) : ℝ) : ℂ)
        = ∑ q ∈ (x/p).primesBelow, ((Real.log (q:ℝ) : ℂ) * f q)
            * ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
                f n * ((Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                  - Real.log (n:ℝ) : ℝ) : ℂ) := by
      refine Finset.sum_congr rfl fun q hq => ?_
      have hqp := (Nat.mem_primesBelow.mp hq).2
      rw [vonMangoldt_apply_prime hqp, div_div]
      ring
    rw [hstuff] at hb
    have hlogC : ((Real.log ((x:ℝ)/(p:ℝ)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hlogY0)
    have hdiff : f p * ((vonMangoldt p : ℝ) : ℂ)
          * ∑ m ∈ Finset.Icc 1 (x/p),
              f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ)
        - ((Real.log (p:ℝ) : ℂ) * f p / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ))
            * ∑ q ∈ (x/p).primesBelow, ((Real.log (q:ℝ) : ℂ) * f q)
                * ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
                    f n * ((Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                      - Real.log (n:ℝ) : ℝ) : ℂ)
        = ((Real.log (p:ℝ) : ℂ) * f p / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ))
            * ((∑ m ∈ Finset.Icc 1 (x/p),
                  f m * ((Real.log ((x:ℝ)/(p:ℝ))
                    - Real.log (m:ℝ) : ℝ) : ℂ))
                * ((Real.log ((x:ℝ)/(p:ℝ)) : ℝ) : ℂ)
              - ∑ q ∈ (x/p).primesBelow, ((Real.log (q:ℝ) : ℂ) * f q)
                  * ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
                      f n * ((Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                        - Real.log (n:ℝ) : ℝ) : ℂ)) := by
      rw [vonMangoldt_apply_prime hpp]
      field_simp
    rw [hdiff, norm_mul]
    have habs1 : ‖(Real.log (p:ℝ) : ℂ) * f p
        / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ)‖
        ≤ Real.log (p:ℝ) / Real.log 2 := by
      rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_natCast_nonneg p),
        abs_of_pos hlogY0, div_le_div_iff₀ hlogY0 hlog2]
      nlinarith [hf p, norm_nonneg (f p), Real.log_natCast_nonneg p,
        hlog2.le, hlogY, mul_nonneg (Real.log_natCast_nonneg p) hlog2.le]
    calc ‖(Real.log (p:ℝ) : ℂ) * f p / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ)‖
          * ‖(∑ m ∈ Finset.Icc 1 (x/p),
                f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ))
              * ((Real.log ((x:ℝ)/(p:ℝ)) : ℝ) : ℂ)
            - ∑ q ∈ (x/p).primesBelow, ((Real.log (q:ℝ) : ℂ) * f q)
                * ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
                    f n * ((Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                      - Real.log (n:ℝ) : ℝ) : ℂ)‖
        ≤ (Real.log (p:ℝ) / Real.log 2) * (64 * ((x:ℝ)/(p:ℝ))) :=
          mul_le_mul habs1 hb (norm_nonneg _)
            (div_nonneg (Real.log_natCast_nonneg p) hlog2.le)
      _ = 64 * (x:ℝ) / Real.log 2 * (Real.log (p:ℝ)/(p:ℝ)) := by
          field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hsub : (((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p)
      ⊆ (x+1).primesBelow := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    rw [Nat.mem_primesBelow]
    exact ⟨by omega, hp.1.1.2⟩
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  have hmass := sum_log_div_primesBelow_le_sharp (x+1) (by omega)
  have hc0 : (0:ℝ) ≤ 64 * (x:ℝ) / Real.log 2 := by positivity
  exact mul_le_mul_of_nonneg_left (le_trans hmono hmass) hc0


open Real Finset ArithmeticFunction in
/-- **The survivor sum becomes the ℂ-triple convolution, sharply**
(Track R, budget repair R-a2): `rieszMeanC_survivors_to_tripleConvRC`
with the per-prime division priced by its own scale gap `1/log(x/p)`
instead of the uniform floor `1/log 2`.  The floored version's Mertens
sum is `≈ 92·x·log x` — a full-log additive overpricing that made the
plain-sum capstone vacuous; here the scale-weighted Mertens mass
(`sum_log_div_mul_log_ratio_closed_le`) prices the survivor sum at
`64·x·(12·loglog x + 18)`, the classical GHS-III loss shape. -/
theorem rieszMeanC_survivors_to_tripleConvRC_sharp (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hcm : CompletelyMultiplicativeC f)
    (x y : ℕ) (hx : 4 ≤ x) :
    ‖∑ p ∈ (((Finset.Icc 1 x).filter Nat.Prime).filter
          (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p),
        f p * ((vonMangoldt p : ℝ) : ℂ)
          * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
              f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ)
      - tripleConvRC f x ((((Finset.Icc 1 x).filter Nat.Prime).filter
          (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p))‖
      ≤ 64 * (x:ℝ) * (12 * Real.log (Real.log (x:ℝ)) + 18) := by
  classical
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [tripleConvRC, ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ p ∈ (((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p),
      ‖f p * ((vonMangoldt p : ℝ) : ℂ)
          * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
              f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ)
        - ((Real.log (p:ℝ) : ℂ) * f p / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ))
            * ∑ q ∈ (x/p).primesBelow, ((Real.log (q:ℝ) : ℂ) * f q)
                * ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
                    f n * ((Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                      - Real.log (n:ℝ) : ℝ) : ℂ)‖
      ≤ 64 * (x:ℝ)
          * (Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ)))) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨⟨hp1, hpx⟩, hpp⟩, -⟩, h2p⟩ := hp
    have h2p' : 2*p ≤ x := by omega
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpp.pos
    have hY2 : (2:ℝ) ≤ (x:ℝ)/(p:ℝ) := by
      rw [le_div_iff₀ hp0]
      exact_mod_cast h2p'
    have hY1 : (1:ℝ) ≤ (x:ℝ)/(p:ℝ) := by linarith
    have hlogY : Real.log 2 ≤ Real.log ((x:ℝ)/(p:ℝ)) :=
      Real.log_le_log (by norm_num) hY2
    have hlogY0 : (0:ℝ) < Real.log ((x:ℝ)/(p:ℝ)) :=
      lt_of_lt_of_le hlog2 hlogY
    have hfloor : ⌊(x:ℝ)/(p:ℝ)⌋₊ = x/p := by
      rw [Nat.floor_div_natCast, Nat.floor_natCast]
    rw [hfloor]
    have hb := rieszMeanC_mul_log_primesBelow_le f hf hcm
      ((x:ℝ)/(p:ℝ)) hY1
    rw [hfloor] at hb
    have hstuff : ∑ q ∈ (x/p).primesBelow,
        f q * ((vonMangoldt q : ℝ) : ℂ)
          * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)/(q:ℝ)⌋₊,
              f m * ((Real.log ((x:ℝ)/(p:ℝ)/(q:ℝ))
                - Real.log (m:ℝ) : ℝ) : ℂ)
        = ∑ q ∈ (x/p).primesBelow, ((Real.log (q:ℝ) : ℂ) * f q)
            * ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
                f n * ((Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                  - Real.log (n:ℝ) : ℝ) : ℂ) := by
      refine Finset.sum_congr rfl fun q hq => ?_
      have hqp := (Nat.mem_primesBelow.mp hq).2
      rw [vonMangoldt_apply_prime hqp, div_div]
      ring
    rw [hstuff] at hb
    have hlogC : ((Real.log ((x:ℝ)/(p:ℝ)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hlogY0)
    have hdiff : f p * ((vonMangoldt p : ℝ) : ℂ)
          * ∑ m ∈ Finset.Icc 1 (x/p),
              f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ)
        - ((Real.log (p:ℝ) : ℂ) * f p / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ))
            * ∑ q ∈ (x/p).primesBelow, ((Real.log (q:ℝ) : ℂ) * f q)
                * ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
                    f n * ((Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                      - Real.log (n:ℝ) : ℝ) : ℂ)
        = ((Real.log (p:ℝ) : ℂ) * f p / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ))
            * ((∑ m ∈ Finset.Icc 1 (x/p),
                  f m * ((Real.log ((x:ℝ)/(p:ℝ))
                    - Real.log (m:ℝ) : ℝ) : ℂ))
                * ((Real.log ((x:ℝ)/(p:ℝ)) : ℝ) : ℂ)
              - ∑ q ∈ (x/p).primesBelow, ((Real.log (q:ℝ) : ℂ) * f q)
                  * ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
                      f n * ((Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                        - Real.log (n:ℝ) : ℝ) : ℂ)) := by
      rw [vonMangoldt_apply_prime hpp]
      field_simp
    rw [hdiff, norm_mul]
    have habs1 : ‖(Real.log (p:ℝ) : ℂ) * f p
        / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ)‖
        ≤ Real.log (p:ℝ) / Real.log ((x:ℝ)/(p:ℝ)) := by
      rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_natCast_nonneg p),
        abs_of_pos hlogY0, div_le_div_iff₀ hlogY0 hlogY0]
      have hkey : (0:ℝ) ≤ Real.log (p:ℝ) * (1 - ‖f p‖)
          * Real.log ((x:ℝ)/(p:ℝ)) :=
        mul_nonneg (mul_nonneg (Real.log_natCast_nonneg p)
          (sub_nonneg.mpr (hf p))) (le_of_lt hlogY0)
      nlinarith [hkey]
    calc ‖(Real.log (p:ℝ) : ℂ) * f p / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ)‖
          * ‖(∑ m ∈ Finset.Icc 1 (x/p),
                f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ))
              * ((Real.log ((x:ℝ)/(p:ℝ)) : ℝ) : ℂ)
            - ∑ q ∈ (x/p).primesBelow, ((Real.log (q:ℝ) : ℂ) * f q)
                * ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
                    f n * ((Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                      - Real.log (n:ℝ) : ℝ) : ℂ)‖
        ≤ (Real.log (p:ℝ) / Real.log ((x:ℝ)/(p:ℝ)))
            * (64 * ((x:ℝ)/(p:ℝ))) :=
          mul_le_mul habs1 hb (norm_nonneg _)
            (div_nonneg (Real.log_natCast_nonneg p) hlogY0.le)
      _ = 64 * (x:ℝ)
            * (Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ)))) := by
          field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hsub2 : (((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p)
      ⊆ (Finset.Icc 1 (x/2)).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1.1.1, by omega⟩, hp.1.1.2⟩
  have hwnonneg : ∀ p ∈ (Finset.Icc 1 (x/2)).filter Nat.Prime,
      (0:ℝ) ≤ Real.log (p:ℝ) / ((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    have hp0 : 0 < p := hp.2.pos
    have h2p : 2*p ≤ x := by omega
    have hY1 : (1:ℝ) ≤ (x:ℝ)/(p:ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast hp0 : (0:ℝ) < (p:ℝ))]
      have : (p:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : p ≤ x)
      linarith
    exact div_nonneg (Real.log_natCast_nonneg p)
      (mul_nonneg (Nat.cast_nonneg p) (Real.log_nonneg hY1))
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub2
    (fun p hp _ => hwnonneg p hp)
  have hmass := sum_log_div_mul_log_ratio_closed_le x hx
  have hc0 : (0:ℝ) ≤ 64 * (x:ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left (le_trans hmono hmass) hc0


open Real Finset in
/-- The per-block trivial mass (restated: the capstone's copy is
private): `∑_p (log p/(p·log(x/p)))·(∑_q log q/q) ≤ 16·(log B − log A)
+ 16·log 4` over primes of `[A,B)` with `2p ≤ x`. -/
private theorem Sk_trivial_mass_le'' (x A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ A ≤ p ∧ p < B)
    (h2P : ∀ p ∈ P, 2*p ≤ x) :
    ∑ p ∈ P, (Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
        * (∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ))
      ≤ 16 * (Real.log (B:ℝ) - Real.log (A:ℝ)) + 16 * Real.log 4 := by
  classical
  have hterm : ∀ p ∈ P,
      (Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
          * (∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ))
        ≤ 4 * (Real.log (p:ℝ)/(p:ℝ)) := by
    intro p hp
    obtain ⟨hpp, hAp, hpB⟩ := hP p hp
    have hp1 : 1 ≤ p := hpp.one_lt.le
    exact inner_mertens_cancel x p hp1 (h2P p hp)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hsub : P ⊆ (Finset.Ico A B).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpp, hAp, hpB⟩ := hP p hp
    simp only [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨hAp, hpB⟩, hpp⟩
  have hmono : ∑ p ∈ P, Real.log (p:ℝ)/(p:ℝ)
      ≤ ∑ p ∈ (Finset.Ico A B).filter Nat.Prime, Real.log (p:ℝ)/(p:ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => div_nonneg (Real.log_natCast_nonneg i) (Nat.cast_nonneg _))
  have hmass := sum_log_div_Ico_le_log A B hA hAB
  linarith [hmono, hmass]

open Real Finset in
/-- **The trivial ℂ-Riesz block bound, fit-free** (Track R, A2-0): the
mirror of `norm_tripleConvR_le''` — per-element `2p ≤ x` suffices, and

  `‖tripleConvRC f x P‖ ≤ x·(16·(log B − log A) + 16·log 4)`. -/
theorem norm_tripleConvRC_le'' (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (x A B : ℕ)
    (hA : 1 ≤ A) (hAB : A ≤ B)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ A ≤ p ∧ p < B)
    (h2P : ∀ p ∈ P, 2*p ≤ x) :
    ‖tripleConvRC f x P‖
      ≤ (x:ℝ) * (16 * (Real.log (B:ℝ) - Real.log (A:ℝ)) + 16 * Real.log 4) := by
  classical
  have hx0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
  rw [tripleConvRC]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ p ∈ P,
      ‖((Real.log (p:ℝ) : ℂ) * f p / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ))
        * ∑ q ∈ (x/p).primesBelow, ((Real.log (q:ℝ) : ℂ) * f q)
            * ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
                f n * ((Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                  - Real.log (n:ℝ) : ℝ) : ℂ)‖
      ≤ (x:ℝ) * ((Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
          * ∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ)) := by
    intro p hp
    obtain ⟨hpp, hAp, hpB⟩ := hP p hp
    have hp1 : 1 ≤ p := hpp.one_lt.le
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp1
    have h2p : 2*p ≤ x := h2P p hp
    have hquot : (2:ℝ) ≤ (x:ℝ)/(p:ℝ) := by
      rw [le_div_iff₀ hp0]
      have hc : ((2*p : ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast h2p
      push_cast at hc
      linarith
    have hlogpos : (0:ℝ) < Real.log ((x:ℝ)/(p:ℝ)) := Real.log_pos (by linarith)
    have hlogp : (0:ℝ) ≤ Real.log (p:ℝ) := Real.log_natCast_nonneg p
    have hmid : ‖∑ q ∈ (x/p).primesBelow, ((Real.log (q:ℝ) : ℂ) * f q)
          * ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
              f n * ((Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                - Real.log (n:ℝ) : ℝ) : ℂ)‖
        ≤ ((x:ℝ)/(p:ℝ)) * ∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ) := by
      refine le_trans (norm_sum_le _ _) ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun q hq => ?_
      rw [Nat.mem_primesBelow] at hq
      obtain ⟨hqlt, hqp⟩ := hq
      have hq1 : 1 ≤ q := hqp.one_lt.le
      have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq1
      have hlogq : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_natCast_nonneg q
      have hpqx : p*q < x := by
        have h1 : p*q < p*(x/p) := by
          have hp0' : 0 < p := hpp.pos
          exact (Nat.mul_lt_mul_left hp0').mpr hqlt
        have h2 : p*(x/p) ≤ x := by
          rw [Nat.mul_comm]; exact Nat.div_mul_le_self x p
        omega
      have hy1 : (1:ℝ) ≤ (x:ℝ)/((p:ℝ)*(q:ℝ)) := by
        rw [le_div_iff₀ (by positivity)]
        have : ((p*q : ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast hpqx.le
        push_cast at this; linarith
      have hinner := norm_rieszMeanC_le' f hf
        ((x:ℝ)/((p:ℝ)*(q:ℝ))) hy1
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hlogq]
      calc Real.log (q:ℝ) * ‖f q‖
            * ‖∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
                f n * ((Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                  - Real.log (n:ℝ) : ℝ) : ℂ)‖
          ≤ Real.log (q:ℝ) * 1 * ((x:ℝ)/((p:ℝ)*(q:ℝ))) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left (hf q) hlogq)
              hinner (norm_nonneg _) (by positivity)
        _ = (x:ℝ)/(p:ℝ) * (Real.log (q:ℝ)/(q:ℝ)) := by field_simp
    rw [norm_mul]
    have houter : ‖(Real.log (p:ℝ) : ℂ) * f p
        / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ)‖
        ≤ Real.log (p:ℝ) / Real.log ((x:ℝ)/(p:ℝ)) := by
      rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogp,
        abs_of_nonneg hlogpos.le]
      refine div_le_div_of_nonneg_right ?_ hlogpos.le
      calc Real.log (p:ℝ) * ‖f p‖ ≤ Real.log (p:ℝ) * 1 :=
            mul_le_mul_of_nonneg_left (hf p) hlogp
        _ = Real.log (p:ℝ) := mul_one _
    calc ‖(Real.log (p:ℝ) : ℂ) * f p / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ)‖
          * ‖∑ q ∈ (x/p).primesBelow, ((Real.log (q:ℝ) : ℂ) * f q)
              * ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)/((p:ℝ)*(q:ℝ))⌋₊,
                  f n * ((Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                    - Real.log (n:ℝ) : ℝ) : ℂ)‖
        ≤ (Real.log (p:ℝ) / Real.log ((x:ℝ)/(p:ℝ)))
            * (((x:ℝ)/(p:ℝ)) * ∑ q ∈ (x/p).primesBelow,
                Real.log (q:ℝ)/(q:ℝ)) := by
          refine mul_le_mul houter hmid (norm_nonneg _) ?_
          exact div_nonneg hlogp hlogpos.le
      _ = (x:ℝ) * ((Real.log (p:ℝ)/((p:ℝ) * Real.log ((x:ℝ)/(p:ℝ))))
            * ∑ q ∈ (x/p).primesBelow, Real.log (q:ℝ)/(q:ℝ)) := by
          field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (Sk_trivial_mass_le'' x A B hA hAB P hP h2P) hx0


open MeasureTheory Real Complex ArithmeticFunction Finset in
open scoped FourierTransform in
/-- **§3's bound on the ℂ-Riesz triple convolution, through the smooth
tsum** (Track R, A2-0): the mirror of `tripleConvR_le'`, with `f`
ℂ-valued natively — the realisation (`tripleConvRC_eq_scaled`) and the
enlargement (`enlargement_extend_le'C`) feed
`ghs_riesz_triple_tsum_le` directly: the `_real` coercion bridge of the
ℝ-chain has no counterpart here. -/
theorem tripleConvRC_le' (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (x : ℕ) (hx : 2 ≤ x) (P : Finset ℕ)
    (hPp : ∀ p ∈ P, p.Prime) (h2p : ∀ p ∈ P, 2*p ≤ x)
    (Q : Finset ℕ) (hQp : ∀ q ∈ Q, q.Prime) (hQ : ∀ q ∈ Q, 0 < q)
    (hQsub : ∀ p ∈ P, (x/p).primesBelow ⊆ Q)
    (V₃ Mtail E₁ b Gmax : ℝ)
    (hE₁0 : 0 < E₁) (hb0 : 0 ≤ b) (hV₃0 : 0 ≤ V₃) (hMtail0 : 0 < Mtail)
    (hGb : ∀ ξ, ‖ExpSums.smoothPhaseSum f x ξ‖ ≤ Gmax)
    (hE₁ : (∫ ξ, ‖ghsBlockPoly f x P ξ‖^2
        * ‖𝓕 (fun v => ((ExpSums.rieszWindow v : ℝ) : ℂ)) ξ‖) ≤ E₁)
    (hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖ExpSums.smoothPhaseSum f x t‖ ≤ b)
    (hV : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2),
        ‖ghsPrimePoly f Q t‖^2) ≤ V₃)
    (hMtail : (∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ))^2 * Gmax^2
        * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2))) ≤ Mtail) :
    ‖tripleConvRC f x P‖
      ≤ (x:ℝ) * Real.sqrt (E₁ * (5 * V₃ * (6*b^2) + Mtail))
        + 2*(x:ℝ)*Real.log 4 := by
  classical
  have hx0 : 0 < x := by omega
  have hx1 : 1 ≤ x := by omega
  set W : ℝ → ℝ := ExpSums.rieszWindow with hW_def
  have hW0 : ∀ v, v ≤ 0 → W v = 0 := by
    intro v hv
    rw [hW_def, ExpSums.rieszWindow, if_neg (not_lt.mpr hv)]
  have hsum : ∀ y : ℝ, 1 ≤ y → y ≤ 2 →
      ‖∑ n ∈ Finset.Icc 1 x, (f n/(n:ℂ))
          * ((W (Real.log y - Real.log (n:ℝ)) : ℝ) : ℂ)‖ ≤ 1 := by
    intro y h1y h2y
    refine ExpSums.rieszC_smoothed_sum_le_one f hf y h1y x ?_
    have : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
    linarith
  have hS1 : ∀ n ∈ Finset.Icc 1 x, 1 ≤ n :=
    fun n hn => (Finset.mem_Icc.mp hn).1
  -- the two forms: over the moving range, and over the fixed `Q`
  set C : ℂ := ∑ p ∈ P, ((Real.log (p:ℝ) : ℂ) * f p
      / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ))
      * ∑ q ∈ (x/p).primesBelow, ((Real.log (q:ℝ) : ℂ) * f q)
          * ((((x:ℝ)/((p:ℝ)*(q:ℝ)) : ℝ) : ℂ)
            * ∑ n ∈ Finset.Icc 1 x, (f n/(n:ℂ))
                * ((W (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                    - Real.log (n:ℝ)) : ℝ) : ℂ))
    with hC_def
  set D : ℂ := ∑ p ∈ P, ((Real.log (p:ℝ) : ℂ) * f p
      / (Real.log ((x:ℝ)/(p:ℝ)) : ℂ))
      * ∑ q ∈ Q, ((Real.log (q:ℝ) : ℂ) * f q)
          * ((((x:ℝ)/((p:ℝ)*(q:ℝ)) : ℝ) : ℂ)
            * ∑ n ∈ Finset.Icc 1 x, (f n/(n:ℂ))
                * ((W (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                    - Real.log (n:ℝ)) : ℝ) : ℂ))
    with hD_def
  have hCeq : tripleConvRC f x P = C := by
    rw [hC_def, hW_def]
    exact tripleConvRC_eq_scaled f x hx0 P (fun p hp => (hPp p hp).pos)
  -- the enlargement, the only error term left
  have hCD : ‖D - C‖ ≤ 2*(x:ℝ)*Real.log 4 := by
    rw [hD_def, hC_def]
    exact enlargement_extend_le'C f hf W hW0 x P hPp h2p (Finset.Icc 1 x) hS1
      hsum Q hQp hQsub
  -- §4 through the smooth tsum, on the enlarged form directly
  have hDle : ‖D‖ ≤ (x:ℝ) * Real.sqrt (E₁ * (5 * V₃ * (6*b^2) + Mtail)) := by
    rw [hD_def, hW_def]
    exact ExpSums.ghs_riesz_triple_tsum_le f hcm h1 hf x hx1 P Q
      (fun p hp => (hPp p hp).pos) hQ V₃ Mtail E₁ b Gmax
      hE₁0 hb0 hV₃0 hMtail0 hGb hE₁ hBu hV hMtail
  rw [hCeq]
  have hCDC : C = D - (D - C) := by ring
  rw [hCDC]
  calc ‖D - (D - C)‖ ≤ ‖D‖ + ‖D - C‖ := norm_sub_le _ _
    _ ≤ (x:ℝ) * Real.sqrt (E₁ * (5 * V₃ * (6*b^2) + Mtail))
          + 2*(x:ℝ)*Real.log 4 := by linarith [hDle, hCD]


open MeasureTheory Real Complex Finset in
/-- **The per-block sharp estimate over ℂ** (Track R, A2-0): the
mirror of `tripleConvR_block_sharp_le'` at native ℂ-valued `f` — the
coercion prologue of the ℝ version has no counterpart, the class-B
suppliers apply to `f` directly, and the §4 step is
`tripleConvRC_le'`. -/
theorem tripleConvRC_block_sharp_le' (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (x k : ℕ) (hx : 2 ≤ x) (hk : 1 ≤ k) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k)
    (hfit : 2 * blockHi x k ≤ x)
    (hX3 : 3 ≤ x / blockLo x k)
    (T : ℝ) (hT : 5 ≤ T) (hPT : ∀ p ∈ P, T^2 ≤ (p:ℝ))
    (b : ℝ) (hb0 : 0 ≤ b)
    (hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖ExpSums.smoothPhaseSum f x t‖ ≤ b) :
    ‖tripleConvRC f x P‖
      ≤ (x:ℝ) * Real.sqrt
          ((Real.exp π *
              (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
                  * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ))
                        * Real.log (x:ℝ) + Real.log 2) + 4 * Real.log 4))
                + T * (6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
                    * (16/(Real.log (x:ℝ))^2
                        + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
            + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
                * (1/(2*Real.pi^2*T)))
          * (5 * (2 * (Real.exp π * (12290
                * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
                + 4*T * (6144 + Real.exp (-(π*T^2/64))
                    * (((x / blockLo x k : ℕ):ℝ) * Real.log 4))))
              + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
                    (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
                  Real.log (q:ℝ)/(q:ℝ))^2)
              * (6*b^2)
            + (∑ q ∈ (x / blockLo x k).primesBelow,
                  Real.log (q:ℝ)/(q:ℝ))^2
                * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2
                * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))))
        + 2*(x:ℝ)*Real.log 4 := by
  classical
  have hx1 : 1 ≤ x := by omega
  obtain ⟨hlo1, hlohi⟩ := blockLo_le_blockHi x k hx1
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have h2p : ∀ p ∈ P, 2*p ≤ x := by
    intro p hp
    obtain ⟨-, -, hpB⟩ := hP p hp
    omega
  have hX2 : 2 ≤ x / blockLo x k := by omega
  -- the enlarged inner range
  have hQp : ∀ q ∈ (x / blockLo x k).primesBelow, q.Prime :=
    fun q hq => (Nat.mem_primesBelow.mp hq).2
  have hQpos : ∀ q ∈ (x / blockLo x k).primesBelow, 0 < q :=
    fun q hq => (hQp q hq).pos
  have hQsub : ∀ p ∈ P, (x/p).primesBelow ⊆ (x / blockLo x k).primesBelow := by
    intro p hp q hq
    obtain ⟨-, hlop, -⟩ := hP p hp
    rw [Nat.mem_primesBelow] at hq ⊢
    exact ⟨lt_of_lt_of_le hq.1 (Nat.div_le_div_left hlop (by omega)), hq.2⟩
  -- positivity of the block energy
  have hlogx : (0:ℝ) < Real.log (x:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 2 ≤ x))
  have he1 : (0:ℝ) < Real.exp 1 - 1 := by
    have := Real.add_one_le_exp (1:ℝ)
    linarith
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hT0 : (0:ℝ) < T := by linarith
  have hsqx : (0:ℝ) < Real.sqrt ((Nat.sqrt x : ℕ):ℝ) := by
    refine Real.sqrt_pos.mpr ?_
    have : 1 ≤ Nat.sqrt x := by
      have := Nat.sqrt_pos.mpr (by omega : 0 < x)
      omega
    exact_mod_cast this
  have hE₁0 : (0:ℝ) < Real.exp π *
      (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
          * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ))
                * Real.log (x:ℝ) + Real.log 2) + 4 * Real.log 4))
        + T * (6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
            * (16/(Real.log (x:ℝ))^2
                + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
      + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
          * (1/(2*Real.pi^2*T)) := by
    have hA : (0:ℝ) < 12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
        * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ))
              * Real.log (x:ℝ) + Real.log 2) + 4 * Real.log 4)) := by
      have h1 : (0:ℝ) < (Real.exp 1 - 1) * Real.exp (-(k:ℝ))
          * Real.log (x:ℝ) := by positivity
      positivity
    have hB' : (0:ℝ) ≤ T * (6144 + Real.exp (-(π*T^2/64))
        * ((x:ℝ) * Real.log 4))
        * (16/(Real.log (x:ℝ))^2
            + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)) := by
      positivity
    have hC : (0:ℝ) ≤ (∑ p ∈ P, Real.log (p:ℝ)
        /((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2 * (1/(2*Real.pi^2*T)) := by
      positivity
    nlinarith [Real.exp_pos π, mul_pos (Real.exp_pos π) hA,
      mul_nonneg (Real.exp_pos π).le hB']
  -- non-negativity of the unit-interval energy
  have hV₃0 : (0:ℝ) ≤ 2 * (Real.exp π * (12290
        * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
        + 4*T * (6144 + Real.exp (-(π*T^2/64))
            * (((x / blockLo x k : ℕ):ℝ) * Real.log 4))))
      + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
            (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
          Real.log (q:ℝ)/(q:ℝ))^2 := by
    have hlogX1 : (0:ℝ) ≤ Real.log ((x / blockLo x k + 1 : ℕ):ℝ) :=
      Real.log_natCast_nonneg _
    positivity
  -- strict positivity of the tail mass: `2` is in the inner range
  have h2mem : 2 ∈ (x / blockLo x k).primesBelow :=
    Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩
  have hQsum : (0:ℝ) < ∑ q ∈ (x / blockLo x k).primesBelow,
      Real.log (q:ℝ)/(q:ℝ) := by
    have hle : Real.log ((2:ℕ):ℝ)/((2:ℕ):ℝ)
        ≤ ∑ q ∈ (x / blockLo x k).primesBelow, Real.log (q:ℝ)/(q:ℝ) :=
      Finset.single_le_sum
        (fun q _ => div_nonneg (Real.log_natCast_nonneg q)
          (Nat.cast_nonneg q)) h2mem
    have h2 : (0:ℝ) < Real.log ((2:ℕ):ℝ)/((2:ℕ):ℝ) := by
      have : ((2:ℕ):ℝ) = (2:ℝ) := by norm_num
      rw [this]
      positivity
    linarith
  have hsummass : Summable
      (fun m : (Nat.smoothNumbers x) => (((m : ℕ) : ℝ))⁻¹) := by
    have hone : CompletelyMultiplicativeC (fun _ : ℕ => (1:ℂ)) :=
      fun a b _ _ => by simp
    refine (ExpSums.summable_norm_smooth_phase (fun _ => 1) hone rfl
      (fun n => by simp) x 0).congr fun m => ?_
    rw [norm_mul, norm_mul, Circle.norm_coe, mul_one, norm_one,
      one_mul, norm_inv, Complex.norm_natCast]
  have hnsum : (0:ℝ) < ∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹ := by
    have h1mem : (1:ℕ) ∈ Nat.smoothNumbers x :=
      Nat.mem_smoothNumbers_of_lt one_pos (by omega)
    refine hsummass.tsum_pos (fun m => by positivity) ⟨1, h1mem⟩ ?_
    show (0:ℝ) < (((1:ℕ):ℝ))⁻¹
    norm_num
  have hMtail0 : (0:ℝ) < (∑ q ∈ (x / blockLo x k).primesBelow,
        Real.log (q:ℝ)/(q:ℝ))^2
      * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2
      * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2))) := by
    have hM : (0:ℝ) < ((halaszM x : ℕ):ℝ) + 1/2 := by positivity
    have hpi := Real.pi_pos
    positivity
  -- the suppliers
  have hE₁ := ghsBlock_E1_riesz_block_le f hf
    x k hx hk P T hT hP hfit hPT
  have hV : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2),
        ‖ghsPrimePoly f (x / blockLo x k).primesBelow t‖^2)
      ≤ 2 * (Real.exp π * (12290
            * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
            + 4*T * (6144 + Real.exp (-(π*T^2/64))
                * (((x / blockLo x k : ℕ):ℝ) * Real.log 4))))
          + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
                (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
              Real.log (q:ℝ)/(q:ℝ))^2 :=
    fun N _ => ghsPrimePoly_unit_energy_primesBelow_le
      f hf (x / blockLo x k) hX2 T hT (N:ℝ)
  exact tripleConvRC_le' f hf hcm h1 x hx P hPp h2p
    (x / blockLo x k).primesBelow hQp hQpos hQsub
    _ _ _ b _ hE₁0 hb0 hV₃0 hMtail0
    (fun ξ => ExpSums.norm_smoothPhaseSum_le f hcm h1 hf x ξ)
    hE₁ hBu hV le_rfl



open MeasureTheory Real Complex Finset ArithmeticFunction in
open scoped FourierTransform in
/-- **§3's sharp estimate on a retained block, ℂ shell form** (Track R,
budget repair R-b2-d-i): `tripleConvRC_block_sharp_le'` with the
unit-interval energy supplied by the 64-split shell chain — the ℂ twin
of `tripleConvR_block_sharp_shell_le`, feeding the rebuilt balance:

  `‖tripleConvRC f x P‖ ≤ x·√(E₁·(5·V₃''·6b² + Mtail)) + 2x·log 4`,

with `V₃'' = 2·e^π·8·(1539·(log(X+1)+2) + 24576) + 2·(∑_{q<64} log q/q)²`
— no `T` and no block mass in the `b²`-coefficient. -/
theorem tripleConvRC_block_sharp_shell_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (x k : ℕ) (hx : 2 ≤ x) (hk : 1 ≤ k) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k)
    (hfit : 2 * blockHi x k ≤ x)
    (hX3 : 3 ≤ x / blockLo x k)
    (T : ℝ) (hT : 5 ≤ T) (hPT : ∀ p ∈ P, T^2 ≤ (p:ℝ))
    (b : ℝ) (hb0 : 0 ≤ b)
    (hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖ExpSums.smoothPhaseSum f x t‖ ≤ b) :
    ‖tripleConvRC f x P‖
      ≤ (x:ℝ) * Real.sqrt
          ((Real.exp π *
              (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
                  * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ))
                        * Real.log (x:ℝ) + Real.log 2) + 4 * Real.log 4))
                + T * (6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
                    * (16/(Real.log (x:ℝ))^2
                        + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
            + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
                * (1/(2*Real.pi^2*T)))
          * (5 * (2 * (Real.exp π * 8
                * (1539 * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
                  + 6144 * 4))
              + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
                    (fun q : ℕ => ¬ 64 ≤ q),
                  Real.log (q:ℝ)/(q:ℝ))^2)
              * (6*b^2)
            + (∑ q ∈ (x / blockLo x k).primesBelow,
                  Real.log (q:ℝ)/(q:ℝ))^2
                * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2
                * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))))
        + 2*(x:ℝ)*Real.log 4 := by
  classical
  have hx1 : 1 ≤ x := by omega
  obtain ⟨hlo1, hlohi⟩ := blockLo_le_blockHi x k hx1
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have h2p : ∀ p ∈ P, 2*p ≤ x := by
    intro p hp
    obtain ⟨-, -, hpB⟩ := hP p hp
    omega
  have hX2 : 2 ≤ x / blockLo x k := by omega
  -- the enlarged inner range
  have hQp : ∀ q ∈ (x / blockLo x k).primesBelow, q.Prime :=
    fun q hq => (Nat.mem_primesBelow.mp hq).2
  have hQpos : ∀ q ∈ (x / blockLo x k).primesBelow, 0 < q :=
    fun q hq => (hQp q hq).pos
  have hQsub : ∀ p ∈ P, (x/p).primesBelow ⊆ (x / blockLo x k).primesBelow := by
    intro p hp q hq
    obtain ⟨-, hlop, -⟩ := hP p hp
    rw [Nat.mem_primesBelow] at hq ⊢
    exact ⟨lt_of_lt_of_le hq.1 (Nat.div_le_div_left hlop (by omega)), hq.2⟩
  -- positivity of the block energy
  have hlogx : (0:ℝ) < Real.log (x:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 2 ≤ x))
  have he1 : (0:ℝ) < Real.exp 1 - 1 := by
    have := Real.add_one_le_exp (1:ℝ)
    linarith
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hT0 : (0:ℝ) < T := by linarith
  have hsqx : (0:ℝ) < Real.sqrt ((Nat.sqrt x : ℕ):ℝ) := by
    refine Real.sqrt_pos.mpr ?_
    have : 1 ≤ Nat.sqrt x := by
      have := Nat.sqrt_pos.mpr (by omega : 0 < x)
      omega
    exact_mod_cast this
  have hE₁0 : (0:ℝ) < Real.exp π *
      (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
          * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ))
                * Real.log (x:ℝ) + Real.log 2) + 4 * Real.log 4))
        + T * (6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
            * (16/(Real.log (x:ℝ))^2
                + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
      + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
          * (1/(2*Real.pi^2*T)) := by
    have hA : (0:ℝ) < 12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
        * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ))
              * Real.log (x:ℝ) + Real.log 2) + 4 * Real.log 4)) := by
      have h1 : (0:ℝ) < (Real.exp 1 - 1) * Real.exp (-(k:ℝ))
          * Real.log (x:ℝ) := by positivity
      positivity
    have hB' : (0:ℝ) ≤ T * (6144 + Real.exp (-(π*T^2/64))
        * ((x:ℝ) * Real.log 4))
        * (16/(Real.log (x:ℝ))^2
            + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)) := by
      positivity
    have hC : (0:ℝ) ≤ (∑ p ∈ P, Real.log (p:ℝ)
        /((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2 * (1/(2*Real.pi^2*T)) := by
      positivity
    nlinarith [Real.exp_pos π, mul_pos (Real.exp_pos π) hA,
      mul_nonneg (Real.exp_pos π).le hB']
  -- non-negativity of the unit-interval energy
  have hV₃0 : (0:ℝ) ≤ 2 * (Real.exp π * 8
        * (1539 * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
          + 6144 * 4))
      + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
            (fun q : ℕ => ¬ 64 ≤ q),
          Real.log (q:ℝ)/(q:ℝ))^2 := by
    have hlogX1 : (0:ℝ) ≤ Real.log ((x / blockLo x k + 1 : ℕ):ℝ) :=
      Real.log_natCast_nonneg _
    positivity
  -- strict positivity of the tail mass: `2` is in the inner range
  have h2mem : 2 ∈ (x / blockLo x k).primesBelow :=
    Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩
  have hQsum : (0:ℝ) < ∑ q ∈ (x / blockLo x k).primesBelow,
      Real.log (q:ℝ)/(q:ℝ) := by
    have hle : Real.log ((2:ℕ):ℝ)/((2:ℕ):ℝ)
        ≤ ∑ q ∈ (x / blockLo x k).primesBelow, Real.log (q:ℝ)/(q:ℝ) :=
      Finset.single_le_sum
        (fun q _ => div_nonneg (Real.log_natCast_nonneg q)
          (Nat.cast_nonneg q)) h2mem
    have h2 : (0:ℝ) < Real.log ((2:ℕ):ℝ)/((2:ℕ):ℝ) := by
      have : ((2:ℕ):ℝ) = (2:ℝ) := by norm_num
      rw [this]
      positivity
    linarith
  have hsummass : Summable
      (fun m : (Nat.smoothNumbers x) => (((m : ℕ) : ℝ))⁻¹) := by
    have hone : CompletelyMultiplicativeC (fun _ : ℕ => (1:ℂ)) :=
      fun a b _ _ => by simp
    refine (ExpSums.summable_norm_smooth_phase (fun _ => 1) hone rfl
      (fun n => by simp) x 0).congr fun m => ?_
    rw [norm_mul, norm_mul, Circle.norm_coe, mul_one, norm_one,
      one_mul, norm_inv, Complex.norm_natCast]
  have hnsum : (0:ℝ) < ∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹ := by
    have h1mem : (1:ℕ) ∈ Nat.smoothNumbers x :=
      Nat.mem_smoothNumbers_of_lt one_pos (by omega)
    refine hsummass.tsum_pos (fun m => by positivity) ⟨1, h1mem⟩ ?_
    show (0:ℝ) < (((1:ℕ):ℝ))⁻¹
    norm_num
  have hMtail0 : (0:ℝ) < (∑ q ∈ (x / blockLo x k).primesBelow,
        Real.log (q:ℝ)/(q:ℝ))^2
      * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2
      * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2))) := by
    have hM : (0:ℝ) < ((halaszM x : ℕ):ℝ) + 1/2 := by positivity
    have hpi := Real.pi_pos
    positivity
  -- the suppliers
  have hE₁ := ghsBlock_E1_riesz_block_le f hf
    x k hx hk P T hT hP hfit hPT
  have hV : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2),
        ‖ghsPrimePoly f (x / blockLo x k).primesBelow t‖^2)
      ≤ 2 * (Real.exp π * 8
            * (1539 * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
              + 6144 * 4))
          + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
                (fun q : ℕ => ¬ 64 ≤ q),
              Real.log (q:ℝ)/(q:ℝ))^2 :=
    fun N _ => ghsPrimePoly_unit_energy_primesBelow_shell_le
      f hf (x / blockLo x k) hX2 (N:ℝ)
  exact tripleConvRC_le' f hf hcm h1 x hx P hPp h2p
    (x / blockLo x k).primesBelow hQp hQpos hQsub
    _ _ _ b _ hE₁0 hb0 hV₃0 hMtail0
    (fun ξ => ExpSums.norm_smoothPhaseSum_le f hcm h1 hf x ξ)
    hE₁ hBu hV le_rfl

open Real in
/-- `e^{2k}/L² = 1/((e^{−k})²·L²)` — N188's bridge, the block index as
`u = e^{−k}` (restated: the capstone's copy is private). -/
private lemma exp_two_k_div_sq (k : ℕ) (L : ℝ) :
    Real.exp (2*(k:ℝ)) / L^2 = 1/((Real.exp (-(k:ℝ)))^2 * L^2) := by
  have h : (Real.exp (-(k:ℝ)))^2 = Real.exp (-(2*(k:ℝ))) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [h, Real.exp_neg]
  field_simp

open Real in
/-- `e^{1−k}·L = e·(e^{−k}·L)` — N185's decay in the balance's `e·P`
shape (restated: the capstone's copy is private). -/
private lemma exp_one_sub_k_mul (k : ℕ) (L : ℝ) :
    Real.exp (1 - (k:ℝ)) * L = Real.exp 1 * (Real.exp (-(k:ℝ)) * L) := by
  rw [show (1 - (k:ℝ)) = 1 + (-(k:ℝ)) by ring, Real.exp_add]
  ring

open Real in
/-- `1 ≤ log x` for `x ≥ 3` — the balance's `hL1` (restated: the
capstone's copy is private). -/
private lemma one_le_log_of_three_le (x : ℕ) (hx : 3 ≤ x) :
    (1:ℝ) ≤ Real.log (x:ℝ) := by
  have he : Real.exp 1 ≤ (x:ℝ) := by
    have h3 : (3:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
    have := Real.exp_one_lt_d9
    linarith
  calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (x:ℝ) := Real.log_le_log (Real.exp_pos 1) he

set_option maxHeartbeats 3200000 in
open MeasureTheory Real Complex Finset in
/-- **§3's per-block estimate, balanced, through the smooth tsum**
(Track R, M0R-5): N189 with the band sup demanded of the smooth phase
sum and the tail weight at the smooth-mass budget:

  `‖tripleConvRC f x P‖ ≤ x·√(2000·(e^π)²·10¹⁵·((SM² + T + 1)·b² + 1)) + 2x·log 4`.

The chain is verbatim N189 with `tripleConvR_block_sharp_le'` at the
bottom and `balance_product_le'` at the top: the energy side is
ring-equal to the `u`-form, the `V`-side and tail lose exactly the
N185/N186 monotonicities, and `hW` is now the smooth-mass budget
`≤ 2000` (discharged later by `bandWeight_smooth_mass_le`).  Complete
multiplicativity is the one new hypothesis — the Euler product behind
the band sup needs it. -/
theorem tripleConvRC_block_balanced_le' (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (x k : ℕ) (hx3 : 3 ≤ x) (hk : 1 ≤ k) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k)
    (hfit : 2 * blockHi x k ≤ x)
    (hX3 : 3 ≤ x / blockLo x k)
    (T : ℝ) (hT : 5 ≤ T) (hPT : ∀ p ∈ P, T^2 ≤ (p:ℝ))
    (b : ℝ) (hb0 : 0 ≤ b)
    (hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖ExpSums.smoothPhaseSum f x t‖ ≤ b)
    (hTL : T ≤ Real.log (x:ℝ)) (hLT : Real.log (x:ℝ) ≤ T^2)
    (hγ1 : Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4) ≤ 1)
    (hSL : 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)
      * Real.log (x:ℝ) ≤ 1)
    (hMp : ∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|)
      ≤ 18)
    (hW : (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))
      * ((Real.log (x:ℝ))^2
        * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2) ≤ 2000) :
    ‖tripleConvRC f x P‖
      ≤ (x:ℝ) * Real.sqrt (2000 * ((Real.exp π)^2 * 10^15
          * (((∑ q ∈ (x / blockLo x k).primesBelow.filter
                (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
              Real.log (q:ℝ)/(q:ℝ))^2 + T + 1) * b^2 + 1)))
        + 2*(x:ℝ)*Real.log 4 := by
  classical
  have hx : 2 ≤ x := by omega
  have hxR0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
  have hL0 : (0:ℝ) < Real.log (x:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 2 ≤ x))
  have hu0 : (0:ℝ) < Real.exp (-(k:ℝ)) := Real.exp_pos _
  have hu1 : Real.exp (-(k:ℝ)) ≤ 1 := by
    rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (Nat.cast_nonneg k))
  refine le_trans (tripleConvRC_block_sharp_le' f hf hcm h1 x k hx hk P hP
    hfit hX3 T hT hPT b hb0 hBu) ?_
  -- the √-argument chain
  have hX1 : 1 ≤ x / blockLo x k := by omega
  have hXx : x / blockLo x k ≤ x := Nat.div_le_self x _
  -- (i) the enlarged-range γ is dominated by the global one
  have hγmono : Real.exp (-(π*T^2/64)) * (((x / blockLo x k : ℕ):ℝ) * Real.log 4)
      ≤ Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4) := by
    have hc : ((x / blockLo x k : ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast hXx
    have h4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hc h4) (Real.exp_pos _).le
  -- (ii) `log(X+1) + 2 ≤ e·(u·L) + log 2 + 2`
  have hlogX1 : Real.log ((x / blockLo x k + 1 : ℕ):ℝ)
      ≤ Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + Real.log 2 := by
    have hle2X : ((x / blockLo x k + 1 : ℕ):ℝ)
        ≤ 2 * ((x / blockLo x k : ℕ):ℝ) := by
      have : x / blockLo x k + 1 ≤ 2 * (x / blockLo x k) := by omega
      exact_mod_cast this
    have hX0 : (0:ℝ) < ((x / blockLo x k : ℕ):ℝ) := by
      exact_mod_cast (by omega : 0 < x / blockLo x k)
    calc Real.log ((x / blockLo x k + 1 : ℕ):ℝ)
        ≤ Real.log (2 * ((x / blockLo x k : ℕ):ℝ)) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < x / blockLo x k + 1))
            hle2X
      _ = Real.log 2 + Real.log ((x / blockLo x k : ℕ):ℝ) :=
          Real.log_mul (by norm_num) (ne_of_gt hX0)
      _ ≤ Real.log 2 + Real.exp (1 - (k:ℝ)) * Real.log (x:ℝ) := by
          linarith [log_div_blockLo_le x k hx]
      _ = Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + Real.log 2 := by
          rw [exp_one_sub_k_mul]
          ring
  -- (iii) the tail mass in the `e·P + 2` shape
  have hqm : ∑ q ∈ (x / blockLo x k).primesBelow, Real.log (q:ℝ)/(q:ℝ)
      ≤ Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + 2 := by
    have h := qMass_le x k hx (by omega)
    rw [exp_one_sub_k_mul] at h
    linarith
  have hqm0 : (0:ℝ) ≤ ∑ q ∈ (x / blockLo x k).primesBelow,
      Real.log (q:ℝ)/(q:ℝ) :=
    Finset.sum_nonneg fun q _ => div_nonneg (Real.log_natCast_nonneg q)
      (Nat.cast_nonneg q)
  have hqm_sq : (∑ q ∈ (x / blockLo x k).primesBelow,
        Real.log (q:ℝ)/(q:ℝ))^2
      ≤ (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + 2)^2 := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self hqm0 hqm
  -- non-negativity of the energy factor
  have he1nn : (0:ℝ) ≤ Real.exp 1 - 1 := by linarith [Real.exp_one_gt_d9.le]
  have hA1nn : (0:ℝ) ≤ 4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ))
      * Real.log (x:ℝ) + Real.log 2) + 4 * Real.log 4 := by
    have hp1 : (0:ℝ) ≤ (Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ) :=
      mul_nonneg (mul_nonneg he1nn hu0.le) hL0.le
    have hp2 := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)
    have hp4 := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)
    linarith
  have hE0 : (0:ℝ) ≤ Real.exp π *
      (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
          * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
              + Real.log 2) + 4 * Real.log 4))
        + T * (6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
            * (16/(Real.log (x:ℝ))^2
                + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
      + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
          * (1/(2*Real.pi^2*T)) := by
    have hT0 : (0:ℝ) < T := by linarith
    have hb1 : (0:ℝ) ≤ Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2 := by positivity
    have hb2 : (0:ℝ) ≤ T * (6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
        * (16/(Real.log (x:ℝ))^2
            + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)) := by
      positivity
    have hb3 : (0:ℝ) ≤ (∑ p ∈ P, Real.log (p:ℝ)
        /((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2 * (1/(2*Real.pi^2*T)) := by
      positivity
    have hb4 : (0:ℝ) ≤ 12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
        * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
            + Real.log 2) + 4 * Real.log 4)) := by
      have := mul_nonneg hb1 hA1nn
      nlinarith [this]
    have := mul_nonneg (Real.exp_pos π).le (add_nonneg hb4 hb2)
    linarith
  -- the V-side monotonicity
  have hT0' : (0:ℝ) ≤ T := by linarith
  have hVinner : 12290 * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
        + 4*T*(6144 + Real.exp (-(π*T^2/64))
            * (((x / blockLo x k : ℕ):ℝ) * Real.log 4))
      ≤ 12290 * (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
            + Real.log 2 + 2)
        + 4*T*(6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4)) := by
    have hm1 : Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2
        ≤ Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
          + Real.log 2 + 2 := by linarith [hlogX1]
    have hm2 : (6144:ℝ) + Real.exp (-(π*T^2/64))
        * (((x / blockLo x k : ℕ):ℝ) * Real.log 4)
        ≤ 6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4) := by
      linarith [hγmono]
    have hm3 := mul_le_mul_of_nonneg_left hm1 (by norm_num : (0:ℝ) ≤ 12290)
    have hm4 := mul_le_mul_of_nonneg_left hm2
      (by positivity : (0:ℝ) ≤ 4*T)
    linarith
  have hVle : 2 * (Real.exp π * (12290
        * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
        + 4*T*(6144 + Real.exp (-(π*T^2/64))
            * (((x / blockLo x k : ℕ):ℝ) * Real.log 4))))
      + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
            (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
          Real.log (q:ℝ)/(q:ℝ))^2
      ≤ 2 * (Real.exp π * (12290
            * (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
              + Real.log 2 + 2)
            + 4*T*(6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))))
        + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
              (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
            Real.log (q:ℝ)/(q:ℝ))^2 := by
    have := mul_le_mul_of_nonneg_left hVinner (Real.exp_pos π).le
    linarith
  -- the tail-mass monotonicity, at the smooth mass
  have hMtle : (∑ q ∈ (x / blockLo x k).primesBelow,
        Real.log (q:ℝ)/(q:ℝ))^2
      * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2
      * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))
      ≤ (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + 2)^2
        * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2
        * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2))) := by
    have hm1 := mul_le_mul_of_nonneg_right hqm_sq
      (sq_nonneg (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹))
    exact mul_le_mul_of_nonneg_right hm1 (by positivity)
  -- the bracket
  have hbrk : 5 * (2 * (Real.exp π * (12290
        * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
        + 4*T*(6144 + Real.exp (-(π*T^2/64))
            * (((x / blockLo x k : ℕ):ℝ) * Real.log 4))))
      + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
            (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
          Real.log (q:ℝ)/(q:ℝ))^2) * (6*b^2)
      + (∑ q ∈ (x / blockLo x k).primesBelow,
            Real.log (q:ℝ)/(q:ℝ))^2
          * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2
          * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))
      ≤ 5 * (2 * (Real.exp π * (12290
            * (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
              + Real.log 2 + 2)
            + 4*T*(6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))))
          + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
                (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
              Real.log (q:ℝ)/(q:ℝ))^2) * (6*b^2)
        + (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + 2)^2
          * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2
          * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2))) := by
    have hm5 := mul_le_mul_of_nonneg_left hVle (by norm_num : (0:ℝ) ≤ 5)
    have hm56 := mul_le_mul_of_nonneg_right hm5
      (by positivity : (0:ℝ) ≤ 6*b^2)
    linarith [hMtle]
  -- E-rewrite into the u-form
  have hEeq : Real.exp π *
      (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
          * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
              + Real.log 2) + 4 * Real.log 4))
        + T * (6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
            * (16/(Real.log (x:ℝ))^2
                + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
      + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
          * (1/(2*Real.pi^2*T))
      = Real.exp π * (12290 * (1/((Real.exp (-(k:ℝ)))^2*(Real.log (x:ℝ))^2)
          * (4*(Real.exp 1 - 1)*(Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
            + (4*Real.log 2 + 4*Real.log 4))))
        + Real.exp π * (T * (6144 + Real.exp (-(π*T^2/64))
            * ((x:ℝ) * Real.log 4))
          * (16/(Real.log (x:ℝ))^2
              + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
        + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
            * (1/(2*Real.pi^2*T)) := by
    rw [exp_two_k_div_sq]
    ring
  -- the full argument bound
  have harg : (Real.exp π *
      (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
          * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
              + Real.log 2) + 4 * Real.log 4))
        + T * (6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
            * (16/(Real.log (x:ℝ))^2
                + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
      + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
          * (1/(2*Real.pi^2*T)))
      * (5 * (2 * (Real.exp π * (12290
            * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
            + 4*T*(6144 + Real.exp (-(π*T^2/64))
                * (((x / blockLo x k : ℕ):ℝ) * Real.log 4))))
          + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
                (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
              Real.log (q:ℝ)/(q:ℝ))^2) * (6*b^2)
        + (∑ q ∈ (x / blockLo x k).primesBelow,
              Real.log (q:ℝ)/(q:ℝ))^2
            * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2
            * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2))))
      ≤ 2000 * ((Real.exp π)^2 * 10^15
          * (((∑ q ∈ (x / blockLo x k).primesBelow.filter
                (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
              Real.log (q:ℝ)/(q:ℝ))^2 + T + 1) * b^2 + 1)) := by
    refine le_trans (mul_le_mul_of_nonneg_left hbrk hE0) ?_
    rw [hEeq]
    exact balance_product_le' (Real.log (x:ℝ)) (Real.exp (-(k:ℝ))) T b
      (Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
      (4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2))
      (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))
      (∑ q ∈ (x / blockLo x k).primesBelow.filter
          (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)), Real.log (q:ℝ)/(q:ℝ))
      (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)
      (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))
      (block_index_le_of_fit x k hx hfit) hu0 hu1
      (one_le_log_of_three_le x hx3) hT hTL hLT
      (by positivity) hγ1 (by positivity) hSL
      (Finset.sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p)
        (by positivity)) hMp
      (Finset.sum_nonneg fun q _ => div_nonneg (Real.log_natCast_nonneg q)
        (Nat.cast_nonneg q))
      (tsum_nonneg fun m => by positivity)
      (by positivity) hW hb0
  have hs := Real.sqrt_le_sqrt harg
  have hxs := mul_le_mul_of_nonneg_left hs hxR0
  linarith



set_option maxHeartbeats 3200000 in
open MeasureTheory Real Complex Finset ArithmeticFunction in
open scoped FourierTransform in
/-- **§3's per-block estimate, balanced, ℂ shell form** (Track R,
budget repair R-b2-d-ii): the shell block-sharp walked into the
rebuilt balance at `T := log x` —

  `‖tripleConvRC f x P‖ ≤ x·√((e^π)²·10¹⁵·(b² + 1)) + 2x·log 4`

— **no `T`, no small-prime mass, and no block index in the envelope**.
`hγ1` and the sharp `hSL2` are hypotheses (discharged at the survivors
level from `x ≥ 10¹⁶`), `SM ≤ 7` closes here by
`small_prime_mass_64_le`, and the completion term is capped by
`T = log x` — the whole content of the repair, per block. -/
theorem tripleConvRC_block_balanced_shell_le (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (x k : ℕ) (hx3 : 3 ≤ x) (hk : 1 ≤ k) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k)
    (hfit : 2 * blockHi x k ≤ x)
    (hX3 : 3 ≤ x / blockLo x k)
    (hL36 : 36 ≤ Real.log (x:ℝ))
    (hPT : ∀ p ∈ P, (Real.log (x:ℝ))^2 ≤ (p:ℝ))
    (b : ℝ) (hb0 : 0 ≤ b)
    (hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖ExpSums.smoothPhaseSum f x t‖ ≤ b)
    (hγ1 : Real.exp (-(π*(Real.log (x:ℝ))^2/64)) * ((x:ℝ) * Real.log 4) ≤ 1)
    (hSL2 : 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)
      * (Real.log (x:ℝ))^2 ≤ 32)
    (hMp : ∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|)
      ≤ 18)
    (hW : (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))
      * ((Real.log (x:ℝ))^2
        * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2) ≤ 2000) :
    ‖tripleConvRC f x P‖
      ≤ (x:ℝ) * Real.sqrt ((Real.exp π)^2 * 10^15 * (b^2 + 1))
        + 2*(x:ℝ)*Real.log 4 := by
  classical
  have hx : 2 ≤ x := by omega
  have hxR0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
  have hL0 : (0:ℝ) < Real.log (x:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 2 ≤ x))
  have hu0 : (0:ℝ) < Real.exp (-(k:ℝ)) := Real.exp_pos _
  have hu1 : Real.exp (-(k:ℝ)) ≤ 1 := by
    rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (Nat.cast_nonneg k))
  have hT5 : (5:ℝ) ≤ Real.log (x:ℝ) := by linarith
  refine le_trans (tripleConvRC_block_sharp_shell_le f hf hcm h1 x k hx hk
    P hP hfit hX3 (Real.log (x:ℝ)) hT5 hPT b hb0 hBu) ?_
  -- the √-argument chain
  have hX1 : 1 ≤ x / blockLo x k := by omega
  have hXx : x / blockLo x k ≤ x := Nat.div_le_self x _
  -- (i) the enlarged-range γ is dominated by the global one
  have hγmono : Real.exp (-(π*(Real.log (x:ℝ))^2/64)) * (((x / blockLo x k : ℕ):ℝ) * Real.log 4)
      ≤ Real.exp (-(π*(Real.log (x:ℝ))^2/64)) * ((x:ℝ) * Real.log 4) := by
    have hc : ((x / blockLo x k : ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast hXx
    have h4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hc h4) (Real.exp_pos _).le
  -- (ii) `log(X+1) + 2 ≤ e·(u·L) + log 2 + 2`
  have hlogX1 : Real.log ((x / blockLo x k + 1 : ℕ):ℝ)
      ≤ Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + Real.log 2 := by
    have hle2X : ((x / blockLo x k + 1 : ℕ):ℝ)
        ≤ 2 * ((x / blockLo x k : ℕ):ℝ) := by
      have : x / blockLo x k + 1 ≤ 2 * (x / blockLo x k) := by omega
      exact_mod_cast this
    have hX0 : (0:ℝ) < ((x / blockLo x k : ℕ):ℝ) := by
      exact_mod_cast (by omega : 0 < x / blockLo x k)
    calc Real.log ((x / blockLo x k + 1 : ℕ):ℝ)
        ≤ Real.log (2 * ((x / blockLo x k : ℕ):ℝ)) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < x / blockLo x k + 1))
            hle2X
      _ = Real.log 2 + Real.log ((x / blockLo x k : ℕ):ℝ) :=
          Real.log_mul (by norm_num) (ne_of_gt hX0)
      _ ≤ Real.log 2 + Real.exp (1 - (k:ℝ)) * Real.log (x:ℝ) := by
          linarith [log_div_blockLo_le x k hx]
      _ = Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + Real.log 2 := by
          rw [exp_one_sub_k_mul]
          ring
  -- (iii) the tail mass in the `e·P + 2` shape
  have hqm : ∑ q ∈ (x / blockLo x k).primesBelow, Real.log (q:ℝ)/(q:ℝ)
      ≤ Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + 2 := by
    have h := qMass_le x k hx (by omega)
    rw [exp_one_sub_k_mul] at h
    linarith
  have hqm0 : (0:ℝ) ≤ ∑ q ∈ (x / blockLo x k).primesBelow,
      Real.log (q:ℝ)/(q:ℝ) :=
    Finset.sum_nonneg fun q _ => div_nonneg (Real.log_natCast_nonneg q)
      (Nat.cast_nonneg q)
  have hqm_sq : (∑ q ∈ (x / blockLo x k).primesBelow,
        Real.log (q:ℝ)/(q:ℝ))^2
      ≤ (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + 2)^2 := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self hqm0 hqm
  -- non-negativity of the energy factor
  have he1nn : (0:ℝ) ≤ Real.exp 1 - 1 := by linarith [Real.exp_one_gt_d9.le]
  have hA1nn : (0:ℝ) ≤ 4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ))
      * Real.log (x:ℝ) + Real.log 2) + 4 * Real.log 4 := by
    have hp1 : (0:ℝ) ≤ (Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ) :=
      mul_nonneg (mul_nonneg he1nn hu0.le) hL0.le
    have hp2 := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)
    have hp4 := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)
    linarith
  have hE0 : (0:ℝ) ≤ Real.exp π *
      (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
          * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
              + Real.log 2) + 4 * Real.log 4))
        + (Real.log (x:ℝ)) * (6144 + Real.exp (-(π*(Real.log (x:ℝ))^2/64)) * ((x:ℝ) * Real.log 4))
            * (16/(Real.log (x:ℝ))^2
                + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
      + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
          * (1/(2*Real.pi^2*(Real.log (x:ℝ)))) := by
    have hT0 : (0:ℝ) < (Real.log (x:ℝ)) := by linarith
    have hb1 : (0:ℝ) ≤ Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2 := by positivity
    have hb2 : (0:ℝ) ≤ (Real.log (x:ℝ)) * (6144 + Real.exp (-(π*(Real.log (x:ℝ))^2/64)) * ((x:ℝ) * Real.log 4))
        * (16/(Real.log (x:ℝ))^2
            + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)) := by
      positivity
    have hb3 : (0:ℝ) ≤ (∑ p ∈ P, Real.log (p:ℝ)
        /((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2 * (1/(2*Real.pi^2*(Real.log (x:ℝ)))) := by
      positivity
    have hb4 : (0:ℝ) ≤ 12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
        * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
            + Real.log 2) + 4 * Real.log 4)) := by
      have := mul_nonneg hb1 hA1nn
      nlinarith [this]
    have := mul_nonneg (Real.exp_pos π).le (add_nonneg hb4 hb2)
    linarith
  -- the V-side monotonicity (shell: only the log(X+1)-bridge)
  have hVle : 2 * (Real.exp π * 8
        * (1539 * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
          + 6144 * 4))
      + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
            (fun q : ℕ => ¬ 64 ≤ q),
          Real.log (q:ℝ)/(q:ℝ))^2
      ≤ 2 * (Real.exp π * 8
            * (1539 * (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
              + Real.log 2 + 2) + 6144 * 4))
        + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
              (fun q : ℕ => ¬ 64 ≤ q),
            Real.log (q:ℝ)/(q:ℝ))^2 := by
    have h1 : Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2
        ≤ Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
          + Real.log 2 + 2 := by linarith [hlogX1]
    have h3 := mul_le_mul_of_nonneg_left h1
      (by norm_num : (0:ℝ) ≤ 1539)
    have h4 := mul_le_mul_of_nonneg_left
      (by linarith [h3] : 1539 * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
          + 6144 * 4
        ≤ 1539 * (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
            + Real.log 2 + 2) + 6144 * 4)
      (by positivity : (0:ℝ) ≤ Real.exp π * 8)
    linarith
  -- the tail-mass monotonicity, at the smooth mass
  have hMtle : (∑ q ∈ (x / blockLo x k).primesBelow,
        Real.log (q:ℝ)/(q:ℝ))^2
      * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2
      * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))
      ≤ (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + 2)^2
        * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2
        * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2))) := by
    have hm1 := mul_le_mul_of_nonneg_right hqm_sq
      (sq_nonneg (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹))
    exact mul_le_mul_of_nonneg_right hm1 (by positivity)
  -- the bracket
  have hbrk : 5 * (2 * (Real.exp π * 8
        * (1539 * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
          + 6144 * 4))
      + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
            (fun q : ℕ => ¬ 64 ≤ q),
          Real.log (q:ℝ)/(q:ℝ))^2) * (6*b^2)
      + (∑ q ∈ (x / blockLo x k).primesBelow,
            Real.log (q:ℝ)/(q:ℝ))^2
          * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2
          * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))
      ≤ 5 * (2 * (Real.exp π * 8
            * (1539 * (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
              + Real.log 2 + 2) + 6144 * 4))
          + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
                (fun q : ℕ => ¬ 64 ≤ q),
              Real.log (q:ℝ)/(q:ℝ))^2) * (6*b^2)
        + (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + 2)^2
          * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2
          * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2))) := by
    have hm5 := mul_le_mul_of_nonneg_left hVle (by norm_num : (0:ℝ) ≤ 5)
    have hm56 := mul_le_mul_of_nonneg_right hm5
      (by positivity : (0:ℝ) ≤ 6*b^2)
    linarith [hMtle]
  -- E-rewrite into the u-form
  have hEeq : Real.exp π *
      (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
          * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
              + Real.log 2) + 4 * Real.log 4))
        + (Real.log (x:ℝ)) * (6144 + Real.exp (-(π*(Real.log (x:ℝ))^2/64)) * ((x:ℝ) * Real.log 4))
            * (16/(Real.log (x:ℝ))^2
                + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
      + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
          * (1/(2*Real.pi^2*(Real.log (x:ℝ))))
      = Real.exp π * (12290 * (1/((Real.exp (-(k:ℝ)))^2*(Real.log (x:ℝ))^2)
          * (4*(Real.exp 1 - 1)*(Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
            + (4*Real.log 2 + 4*Real.log 4))))
        + Real.exp π * ((Real.log (x:ℝ)) * (6144 + Real.exp (-(π*(Real.log (x:ℝ))^2/64))
            * ((x:ℝ) * Real.log 4))
          * (16/(Real.log (x:ℝ))^2
              + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
        + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
            * (1/(2*Real.pi^2*(Real.log (x:ℝ)))) := by
    rw [exp_two_k_div_sq]
    ring
  -- the full argument bound
  have hSM7 : ∑ q ∈ (x / blockLo x k).primesBelow.filter
      (fun q : ℕ => ¬ 64 ≤ q), Real.log (q:ℝ)/(q:ℝ) ≤ 7 :=
    small_prime_mass_64_le (x / blockLo x k).primesBelow
      (fun q hq => (Nat.mem_primesBelow.mp hq).2)
  have harg : (Real.exp π *
      (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
          * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
              + Real.log 2) + 4 * Real.log 4))
        + (Real.log (x:ℝ)) * (6144 + Real.exp (-(π*(Real.log (x:ℝ))^2/64))
            * ((x:ℝ) * Real.log 4))
            * (16/(Real.log (x:ℝ))^2
                + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
      + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
          * (1/(2*Real.pi^2*(Real.log (x:ℝ)))))
      * (5 * (2 * (Real.exp π * 8
            * (1539 * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
              + 6144 * 4))
          + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
                (fun q : ℕ => ¬ 64 ≤ q),
              Real.log (q:ℝ)/(q:ℝ))^2) * (6*b^2)
        + (∑ q ∈ (x / blockLo x k).primesBelow,
              Real.log (q:ℝ)/(q:ℝ))^2
            * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2
            * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2))))
      ≤ (Real.exp π)^2 * 10^15 * (b^2 + 1) := by
    refine le_trans (mul_le_mul_of_nonneg_left hbrk hE0) ?_
    rw [hEeq]
    exact balance_product_shell_le (Real.log (x:ℝ)) (Real.exp (-(k:ℝ))) b
      (4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2))
      (Real.exp (-(π*(Real.log (x:ℝ))^2/64)) * ((x:ℝ) * Real.log 4))
      (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))
      (∑ q ∈ (x / blockLo x k).primesBelow.filter
          (fun q : ℕ => ¬ 64 ≤ q), Real.log (q:ℝ)/(q:ℝ))
      (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)
      (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))
      hL36 hu0 hu1 (block_index_le_of_fit x k hx hfit)
      (by positivity) hγ1 (by positivity) hSL2
      (Finset.sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p)
        (by positivity)) hMp
      (Finset.sum_nonneg fun q _ => div_nonneg (Real.log_natCast_nonneg q)
        (Nat.cast_nonneg q)) hSM7
      (tsum_nonneg fun m => by positivity)
      (by positivity) hW hb0
  have hs := Real.sqrt_le_sqrt harg
  have hxs := mul_le_mul_of_nonneg_left hs hxR0
  linarith

set_option maxHeartbeats 3200000 in
open Real Finset in
/-- **§3's head, closed, through the smooth tsum** (Track R, M0R-5):
N196 with the band sup demanded of the smooth phase sum and every
rider discharged at the smooth-mass budget — the per-block input is
`tripleConvR_block_balanced_le'`, its `hW` is
`bandWeight_smooth_mass_le`, and the envelope carries the constant
`2000`:

  `‖tripleConvRC f x (survivors)| ≤ K₀·(x·√(2000·(e^π)²·10¹⁵·(((log⌈T²⌉+2)² + T + 1)·b² + 1)) + 2x·log 4) + 2·x·(16((e−1)·e·log 2 + log 2) + 16·log 4)`.

The boundary blocks are priced fit-free exactly as in N196 — the tail
branch never sees the band sup. -/
theorem tripleConvRC_survivors_balanced_le' (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (x y K₀ : ℕ) (hx : 10^16 ≤ x) (hy2 : 2 ≤ y)
    (T : ℝ) (hT1 : Real.sqrt (21 * Real.log (x:ℝ)) ≤ T)
    (hT2 : T ≤ Real.log (x:ℝ)) (hTy : T^2 ≤ (y:ℝ))
    (hK₀1 : 1 ≤ K₀)
    (hK₀low : Real.exp 1 * Real.log 2
      ≤ Real.exp (-(K₀:ℝ)) * Real.log (x:ℝ))
    (hK₀max : Real.exp (-((K₀:ℝ)+1)) * Real.log (x:ℝ)
      < Real.exp 1 * Real.log 2)
    (hX3 : ∀ k ∈ Finset.Icc 1 K₀, 3 ≤ x / blockLo x k)
    (b : ℝ) (hb0 : 0 ≤ b)
    (hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖ExpSums.smoothPhaseSum f x t‖ ≤ b) :
    ‖tripleConvRC f x ((((Finset.Icc 1 x).filter Nat.Prime).filter
        (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p))‖
      ≤ (K₀:ℝ) * ((x:ℝ) * Real.sqrt (2000 * ((Real.exp π)^2 * 10^15
            * (((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1) * b^2 + 1)))
          + 2*(x:ℝ)*Real.log 4)
        + 2 * ((x:ℝ) * (16 * ((Real.exp 1 - 1) * (Real.exp 1 * Real.log 2)
            + Real.log 2) + 16 * Real.log 4)) := by
  classical
  have hx2 : (2:ℕ) ≤ x := le_trans (by norm_num) hx
  have hx3' : (3:ℕ) ≤ x := le_trans (by norm_num) hx
  have hx3000 : (3000:ℕ) ≤ x := le_trans (by norm_num) hx
  have hx1 : (1:ℕ) ≤ x := by omega
  have hL0 : (0:ℝ) < Real.log (x:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 2 ≤ x))
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨h5T, hLT2, hγT⟩ := T_window_conditions x T hx hT1 hT2
  -- split validity at `K₀+2`
  have hK : Real.exp (-((K₀+2:ℕ):ℝ)) * Real.log (x:ℝ) < Real.log 2 := by
    have hs1 : Real.exp (-((K₀+2:ℕ):ℝ))
        = Real.exp (-1) * Real.exp (-((K₀:ℝ)+1)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    have hs2 : Real.exp (-1) * (Real.exp 1 * Real.log 2) = Real.log 2 := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    calc Real.exp (-((K₀+2:ℕ):ℝ)) * Real.log (x:ℝ)
        = Real.exp (-1) * (Real.exp (-((K₀:ℝ)+1)) * Real.log (x:ℝ)) := by
          rw [hs1]; ring
      _ < Real.exp (-1) * (Real.exp 1 * Real.log 2) := by
          exact mul_lt_mul_of_pos_left hK₀max (Real.exp_pos _)
      _ = Real.log 2 := hs2
  -- split, triangle, k-split
  rw [tripleConvRC_survivor_split f x y (K₀+2) hx1 hK]
  refine le_trans (norm_sum_le _ _) ?_
  refine sum_ksplit_le
    (fun k => ‖tripleConvRC f x (((Finset.Ico (blockLo x k)
      (blockHi x k)).filter Nat.Prime).filter
      (fun p => ¬ p < y ∧ ¬ x < 2*p))‖) K₀ (K₀+2) (by omega) _ _ ?_ ?_
  · -- the head: the primed N189 per block, then the SM-monotone step
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk1 : 1 ≤ k := hk.1
    have hkK : k ≤ K₀ := hk.2
    -- the block-membership facts
    have hP : ∀ p ∈ (((Finset.Ico (blockLo x k) (blockHi x k)).filter
        Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p)),
        p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Ico] at hp
      exact ⟨hp.1.2, hp.1.1.1, hp.1.1.2⟩
    have hPT : ∀ p ∈ (((Finset.Ico (blockLo x k) (blockHi x k)).filter
        Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p)),
        T^2 ≤ (p:ℝ) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Ico] at hp
      have hyp : y ≤ p := Nat.le_of_not_lt hp.2.1
      have : (y:ℝ) ≤ (p:ℝ) := by exact_mod_cast hyp
      linarith [hTy]
    -- the per-block mass floor
    have huL : Real.exp 1 * Real.log 2
        ≤ Real.exp (-(k:ℝ)) * Real.log (x:ℝ) := by
      have hmono : Real.exp (-(K₀:ℝ)) ≤ Real.exp (-(k:ℝ)) := by
        refine Real.exp_le_exp.mpr ?_
        have : (k:ℝ) ≤ (K₀:ℝ) := by exact_mod_cast hkK
        linarith
      have := mul_le_mul_of_nonneg_right hmono hL0.le
      linarith [hK₀low]
    have hMp := blockMass_le_const x k hx2 hk1 _ hP huL
    have hγ1 := gamma_le_one_of x T hx2 hγT
    have hSL := tailS_mul_log_le_one x hx
    have hW := bandWeight_smooth_mass_le x hx3000
    have hbal := tripleConvRC_block_balanced_le' f hf hcm h1 x k hx3' hk1 _ hP
      (fit_of_mass_floor x k (by omega) huL)
      (hX3 k (by rw [Finset.mem_Icc]; omega)) T h5T hPT
      b hb0 hBu hT2 hLT2 hγ1 hSL hMp hW
    refine le_trans hbal ?_
    -- the SM-monotone step: `SM(k) ≤ log⌈T²⌉ + 2`, under the `2000`
    have hSM := smallMass_le (x / blockLo x k) T h5T
    have hSM0 : (0:ℝ) ≤ ∑ q ∈ (x / blockLo x k).primesBelow.filter
        (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)), Real.log (q:ℝ)/(q:ℝ) :=
      Finset.sum_nonneg fun q _ => div_nonneg (Real.log_natCast_nonneg q)
        (Nat.cast_nonneg q)
    have hSMsq : (∑ q ∈ (x / blockLo x k).primesBelow.filter
          (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)), Real.log (q:ℝ)/(q:ℝ))^2
        ≤ (Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 := by
      nlinarith [hSM, hSM0]
    have hargmono : 2000 * ((Real.exp π)^2 * 10^15
        * (((∑ q ∈ (x / blockLo x k).primesBelow.filter
            (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
          Real.log (q:ℝ)/(q:ℝ))^2 + T + 1) * b^2 + 1))
        ≤ 2000 * ((Real.exp π)^2 * 10^15
          * (((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1) * b^2 + 1)) := by
      have hq1 : ((∑ q ∈ (x / blockLo x k).primesBelow.filter
            (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
          Real.log (q:ℝ)/(q:ℝ))^2 + T + 1) * b^2
          ≤ ((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1) * b^2 :=
        mul_le_mul_of_nonneg_right (by linarith [hSMsq]) (sq_nonneg b)
      have hq2 : (0:ℝ) ≤ (Real.exp π)^2 * 10^15 := by positivity
      have hq3 := mul_le_mul_of_nonneg_left
        (by linarith [hq1] :
          ((∑ q ∈ (x / blockLo x k).primesBelow.filter
              (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
            Real.log (q:ℝ)/(q:ℝ))^2 + T + 1) * b^2 + 1
          ≤ ((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1) * b^2 + 1) hq2
      exact mul_le_mul_of_nonneg_left hq3 (by norm_num : (0:ℝ) ≤ 2000)
    have hxR0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
    have hs := Real.sqrt_le_sqrt hargmono
    have := mul_le_mul_of_nonneg_left hs hxR0
    linarith
  · -- the tail: two boundary blocks, fit-free
    have htb : ∀ k ∈ Finset.Icc (K₀+1) (K₀+2),
        ‖tripleConvRC f x (((Finset.Ico (blockLo x k) (blockHi x k)).filter
          Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p))‖
        ≤ (x:ℝ) * (16 * ((Real.exp 1 - 1) * (Real.exp 1 * Real.log 2)
            + Real.log 2) + 16 * Real.log 4) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hk1 : 1 ≤ k := by omega
      obtain ⟨hlo1, hlohi⟩ := blockLo_le_blockHi x k hx1
      have hP' : ∀ p ∈ (((Finset.Ico (blockLo x k) (blockHi x k)).filter
          Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p)),
          p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ico] at hp
        exact ⟨hp.1.2, hp.1.1.1, hp.1.1.2⟩
      have h2P : ∀ p ∈ (((Finset.Ico (blockLo x k) (blockHi x k)).filter
          Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p)), 2*p ≤ x := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ico] at hp
        omega
      refine le_trans (norm_tripleConvRC_le'' f hf x (blockLo x k)
        (blockHi x k) hlo1 hlohi _ hP' h2P) ?_
      have hw := log_blockHi_sub_log_blockLo_le x k hx2 hk1
      have hmono : Real.exp (-(k:ℝ)) ≤ Real.exp (-((K₀:ℝ)+1)) := by
        refine Real.exp_le_exp.mpr ?_
        have hc1 : ((K₀+1:ℕ):ℝ) ≤ (k:ℝ) := by exact_mod_cast hk.1
        push_cast at hc1
        linarith
      have huk : Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
          ≤ Real.exp 1 * Real.log 2 := by
        have hc2 := mul_le_mul_of_nonneg_right hmono hL0.le
        linarith [hK₀max]
      have he1nn : (0:ℝ) ≤ Real.exp 1 - 1 := by
        linarith [Real.exp_one_gt_d9.le]
      have hwidth2 : Real.log ((blockHi x k : ℕ):ℝ)
          - Real.log ((blockLo x k : ℕ):ℝ)
          ≤ (Real.exp 1 - 1) * (Real.exp 1 * Real.log 2) + Real.log 2 := by
        have hc3 : (Real.exp 1 - 1) * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
            ≤ (Real.exp 1 - 1) * (Real.exp 1 * Real.log 2) :=
          mul_le_mul_of_nonneg_left huk he1nn
        nlinarith [hw, hc3]
      have hx0' : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
      refine mul_le_mul_of_nonneg_left ?_ hx0'
      linarith [hwidth2]
    refine le_trans (Finset.sum_le_sum htb) ?_
    rw [Finset.sum_const, Nat.card_Icc]
    have h2c : K₀+2+1 - (K₀+1) = 2 := by omega
    rw [h2c]
    simp [nsmul_eq_mul]




set_option maxHeartbeats 3200000 in
open Real Finset ArithmeticFunction in
/-- **The survivor estimate, ℂ shell form** (Track R, budget repair
R-b2-e): the `k`-split of the survivor triple convolution with every
block priced by the shell balanced estimate at `T := log x` —

  `‖tripleConvRC f x 𝒮‖ ≤ K₀·(x·√((e^π)²·10¹⁵·(b²+1)) + 2x·log 4)
     + 2x·(16((e−1)e·log2 + log2) + 16·log4)`

— the envelope is a single absolute constant against `b²`, with no
`T`, no small-prime mass, and no per-block residue.  The window's only
remaining duties are `y ≥ log²x` (for the per-block prime floor) and
the `K₀`-schedule; `hγ1`/`hSL2` close from `x ≥ 10¹⁶` alone. -/
theorem tripleConvRC_survivors_balanced_shell_le (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (x y K₀ : ℕ) (hx : 10^16 ≤ x) (hy2 : 2 ≤ y)
    (hy : (Real.log (x:ℝ))^2 ≤ (y:ℝ))
    (hK₀1 : 1 ≤ K₀)
    (hK₀low : Real.exp 1 * Real.log 2
      ≤ Real.exp (-(K₀:ℝ)) * Real.log (x:ℝ))
    (hK₀max : Real.exp (-((K₀:ℝ)+1)) * Real.log (x:ℝ)
      < Real.exp 1 * Real.log 2)
    (hX3 : ∀ k ∈ Finset.Icc 1 K₀, 3 ≤ x / blockLo x k)
    (b : ℝ) (hb0 : 0 ≤ b)
    (hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖ExpSums.smoothPhaseSum f x t‖ ≤ b) :
    ‖tripleConvRC f x ((((Finset.Icc 1 x).filter Nat.Prime).filter
        (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p))‖
      ≤ (K₀:ℝ) * ((x:ℝ) * Real.sqrt ((Real.exp π)^2 * 10^15 * (b^2 + 1))
          + 2*(x:ℝ)*Real.log 4)
        + 2 * ((x:ℝ) * (16 * ((Real.exp 1 - 1) * (Real.exp 1 * Real.log 2)
            + Real.log 2) + 16 * Real.log 4)) := by
  classical
  have hx2 : (2:ℕ) ≤ x := le_trans (by norm_num) hx
  have hx3' : (3:ℕ) ≤ x := le_trans (by norm_num) hx
  have hx3000 : (3000:ℕ) ≤ x := le_trans (by norm_num) hx
  have hx1 : (1:ℕ) ≤ x := by omega
  have hL0 : (0:ℝ) < Real.log (x:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 2 ≤ x))
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hx0R : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hL36 : (36:ℝ) ≤ Real.log (x:ℝ) := by
    rw [Real.le_log_iff_exp_le hx0R]
    have he3 : Real.exp (3:ℝ) ≤ 20.1 := by
      have h3 : Real.exp (3:ℝ) = (Real.exp 1)^(3:ℕ) := by
        rw [← Real.exp_nat_mul]
        norm_num
      rw [h3]
      have hcube : (Real.exp 1)^(3:ℕ) ≤ (2.7182818286:ℝ)^(3:ℕ) :=
        pow_le_pow_left₀ (Real.exp_pos 1).le
          (by linarith [Real.exp_one_lt_d9]) 3
      have hnum : (2.7182818286:ℝ)^(3:ℕ) ≤ 20.1 := by norm_num
      linarith
    have h36 : Real.exp (36:ℝ) = (Real.exp 3)^(12:ℕ) := by
      rw [← Real.exp_nat_mul]
      norm_num
    have hp12 : (Real.exp 3)^(12:ℕ) ≤ (20.1:ℝ)^(12:ℕ) :=
      pow_le_pow_left₀ (Real.exp_pos 3).le he3 12
    have hnum12 : (20.1:ℝ)^(12:ℕ) ≤ 10^16 := by norm_num
    have hxR : (10:ℝ)^16 ≤ (x:ℝ) := by exact_mod_cast hx
    rw [h36]
    linarith
  have hT1L : Real.sqrt (21 * Real.log (x:ℝ)) ≤ Real.log (x:ℝ) := by
    have h1 : Real.sqrt (21 * Real.log (x:ℝ))
        ≤ Real.sqrt ((Real.log (x:ℝ))^2) := by
      refine Real.sqrt_le_sqrt ?_
      nlinarith [hL36]
    rwa [Real.sqrt_sq (by linarith)] at h1
  obtain ⟨h5T, hLT2, hγT⟩ :=
    T_window_conditions x (Real.log (x:ℝ)) hx hT1L le_rfl
  -- split validity at `K₀+2`
  have hK : Real.exp (-((K₀+2:ℕ):ℝ)) * Real.log (x:ℝ) < Real.log 2 := by
    have hs1 : Real.exp (-((K₀+2:ℕ):ℝ))
        = Real.exp (-1) * Real.exp (-((K₀:ℝ)+1)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    have hs2 : Real.exp (-1) * (Real.exp 1 * Real.log 2) = Real.log 2 := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    calc Real.exp (-((K₀+2:ℕ):ℝ)) * Real.log (x:ℝ)
        = Real.exp (-1) * (Real.exp (-((K₀:ℝ)+1)) * Real.log (x:ℝ)) := by
          rw [hs1]; ring
      _ < Real.exp (-1) * (Real.exp 1 * Real.log 2) := by
          exact mul_lt_mul_of_pos_left hK₀max (Real.exp_pos _)
      _ = Real.log 2 := hs2
  -- split, triangle, k-split
  rw [tripleConvRC_survivor_split f x y (K₀+2) hx1 hK]
  refine le_trans (norm_sum_le _ _) ?_
  refine sum_ksplit_le
    (fun k => ‖tripleConvRC f x (((Finset.Ico (blockLo x k)
      (blockHi x k)).filter Nat.Prime).filter
      (fun p => ¬ p < y ∧ ¬ x < 2*p))‖) K₀ (K₀+2) (by omega) _ _ ?_ ?_
  · -- the head: the primed N189 per block, then the SM-monotone step
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk1 : 1 ≤ k := hk.1
    have hkK : k ≤ K₀ := hk.2
    -- the block-membership facts
    have hP : ∀ p ∈ (((Finset.Ico (blockLo x k) (blockHi x k)).filter
        Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p)),
        p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Ico] at hp
      exact ⟨hp.1.2, hp.1.1.1, hp.1.1.2⟩
    have hPT : ∀ p ∈ (((Finset.Ico (blockLo x k) (blockHi x k)).filter
        Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p)),
        (Real.log (x:ℝ))^2 ≤ (p:ℝ) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Ico] at hp
      have hyp : y ≤ p := Nat.le_of_not_lt hp.2.1
      have : (y:ℝ) ≤ (p:ℝ) := by exact_mod_cast hyp
      linarith [hy]
    -- the per-block mass floor
    have huL : Real.exp 1 * Real.log 2
        ≤ Real.exp (-(k:ℝ)) * Real.log (x:ℝ) := by
      have hmono : Real.exp (-(K₀:ℝ)) ≤ Real.exp (-(k:ℝ)) := by
        refine Real.exp_le_exp.mpr ?_
        have : (k:ℝ) ≤ (K₀:ℝ) := by exact_mod_cast hkK
        linarith
      have := mul_le_mul_of_nonneg_right hmono hL0.le
      linarith [hK₀low]
    have hMp := blockMass_le_const x k hx2 hk1 _ hP huL
    have hγ1 := gamma_le_one_of x (Real.log (x:ℝ)) hx2 hγT
    have hSL2 := tailS_mul_log_sq_le x hx
    have hW := bandWeight_smooth_mass_le x hx3000
    exact tripleConvRC_block_balanced_shell_le f hf hcm h1 x k hx3' hk1 _ hP
      (fit_of_mass_floor x k (by omega) huL)
      (hX3 k (by rw [Finset.mem_Icc]; omega)) hL36 hPT
      b hb0 hBu hγ1 hSL2 hMp hW
  · -- the tail: two boundary blocks, fit-free
    have htb : ∀ k ∈ Finset.Icc (K₀+1) (K₀+2),
        ‖tripleConvRC f x (((Finset.Ico (blockLo x k) (blockHi x k)).filter
          Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p))‖
        ≤ (x:ℝ) * (16 * ((Real.exp 1 - 1) * (Real.exp 1 * Real.log 2)
            + Real.log 2) + 16 * Real.log 4) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hk1 : 1 ≤ k := by omega
      obtain ⟨hlo1, hlohi⟩ := blockLo_le_blockHi x k hx1
      have hP' : ∀ p ∈ (((Finset.Ico (blockLo x k) (blockHi x k)).filter
          Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p)),
          p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ico] at hp
        exact ⟨hp.1.2, hp.1.1.1, hp.1.1.2⟩
      have h2P : ∀ p ∈ (((Finset.Ico (blockLo x k) (blockHi x k)).filter
          Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p)), 2*p ≤ x := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ico] at hp
        omega
      refine le_trans (norm_tripleConvRC_le'' f hf x (blockLo x k)
        (blockHi x k) hlo1 hlohi _ hP' h2P) ?_
      have hw := log_blockHi_sub_log_blockLo_le x k hx2 hk1
      have hmono : Real.exp (-(k:ℝ)) ≤ Real.exp (-((K₀:ℝ)+1)) := by
        refine Real.exp_le_exp.mpr ?_
        have hc1 : ((K₀+1:ℕ):ℝ) ≤ (k:ℝ) := by exact_mod_cast hk.1
        push_cast at hc1
        linarith
      have huk : Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
          ≤ Real.exp 1 * Real.log 2 := by
        have hc2 := mul_le_mul_of_nonneg_right hmono hL0.le
        linarith [hK₀max]
      have he1nn : (0:ℝ) ≤ Real.exp 1 - 1 := by
        linarith [Real.exp_one_gt_d9.le]
      have hwidth2 : Real.log ((blockHi x k : ℕ):ℝ)
          - Real.log ((blockLo x k : ℕ):ℝ)
          ≤ (Real.exp 1 - 1) * (Real.exp 1 * Real.log 2) + Real.log 2 := by
        have hc3 : (Real.exp 1 - 1) * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
            ≤ (Real.exp 1 - 1) * (Real.exp 1 * Real.log 2) :=
          mul_le_mul_of_nonneg_left huk he1nn
        nlinarith [hw, hc3]
      have hx0' : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
      refine mul_le_mul_of_nonneg_left ?_ hx0'
      linarith [hwidth2]
    refine le_trans (Finset.sum_le_sum htb) ?_
    rw [Finset.sum_const, Nat.card_Icc]
    have h2c : K₀+2+1 - (K₀+1) = 2 := by omega
    rw [h2c]
    simp [nsmul_eq_mul]

open Real Finset ArithmeticFunction in
/-- **§3, end to end, through the smooth tsum** (Track R, M0R-5): the
`b`-parametric assembly `rieszMean_log_le_of_nonPretentious` with the
band sup demanded of the smooth phase sum — the survivor estimate is
`tripleConvR_survivors_balanced_le'`, so the envelope carries the
smooth-mass constant `2000` and `b` can be instantiated log-freely.
The identity error, head/tail discards, and the survivor bridge are
untouched: they never see the band sup. -/
theorem rieszMeanC_log_le'_of_nonPretentious (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hcm : CompletelyMultiplicativeC f)
    (h1 : f 1 = 1)
    (x y K₀ : ℕ) (hx : 10^16 ≤ x) (hy2 : 2 ≤ y) (hyx : 2*y ≤ x)
    (T : ℝ) (hT1 : Real.sqrt (21 * Real.log (x:ℝ)) ≤ T)
    (hT2 : T ≤ Real.log (x:ℝ)) (hTy : T^2 ≤ (y:ℝ))
    (hK₀1 : 1 ≤ K₀)
    (hK₀low : Real.exp 1 * Real.log 2
      ≤ Real.exp (-(K₀:ℝ)) * Real.log (x:ℝ))
    (hK₀max : Real.exp (-((K₀:ℝ)+1)) * Real.log (x:ℝ)
      < Real.exp 1 * Real.log 2)
    (hX3 : ∀ k ∈ Finset.Icc 1 K₀, 3 ≤ x / blockLo x k)
    (b : ℝ) (hb0 : 0 ≤ b)
    (hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖ExpSums.smoothPhaseSum f x t‖ ≤ b) :
    ‖(∑ n ∈ Finset.Icc 1 x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
        * ((Real.log (x:ℝ) : ℝ) : ℂ)‖
      ≤ 35*(x:ℝ) + (x:ℝ)*(Real.log (y:ℝ) + 2) + 2*((x:ℝ)+1)*Real.log 4
        + 64 * (x:ℝ) / Real.log 2 * (Real.log ((x+1:ℕ):ℝ) + 2)
        + ((K₀:ℝ) * ((x:ℝ) * Real.sqrt (2000 * ((Real.exp π)^2 * 10^15
              * (((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1) * b^2 + 1)))
            + 2*(x:ℝ)*Real.log 4)
          + 2 * ((x:ℝ) * (16 * ((Real.exp 1 - 1) * (Real.exp 1 * Real.log 2)
              + Real.log 2) + 16 * Real.log 4))) := by
  classical
  have hx1 : (1:ℕ) ≤ x := le_trans (by norm_num) hx
  have hid := rieszMeanC_mul_log_prime_restrict f hf hcm x hx1
  have hhead := rieszMeanC_prime_head_le f hf x y hy2
  have htail := rieszMeanC_prime_tail_le f hf x
  have hbridge := rieszMeanC_survivors_to_tripleConvRC f hf hcm x y hx1
  have hconv := tripleConvRC_survivors_balanced_le' f hf hcm h1 x y K₀ hx hy2
    T hT1 hT2 hTy hK₀1 hK₀low hK₀max hX3 b hb0 hBu
  -- the three-way split of the prime sum
  have hfe : (((Finset.Icc 1 x).filter Nat.Prime).filter
        (fun p => ¬ p < y)).filter (fun p => x < 2*p)
      = ((Finset.Icc 1 x).filter Nat.Prime).filter (fun p => x < 2*p) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hS, _⟩, h2⟩
      exact ⟨hS, h2⟩
    · rintro ⟨hS, h2⟩
      exact ⟨⟨hS, by omega⟩, h2⟩
  have hsplit1 := Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 x).filter Nat.Prime) (fun p => p < y)
    (fun p => f p * ((vonMangoldt p : ℝ) : ℂ)
      * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
          f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ))
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    (((Finset.Icc 1 x).filter Nat.Prime).filter (fun p => ¬ p < y))
    (fun p => x < 2*p)
    (fun p => f p * ((vonMangoldt p : ℝ) : ℂ)
      * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
          f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ))
  rw [hfe] at hsplit2
  -- name the five quantities
  set A := (∑ n ∈ Finset.Icc 1 x,
      f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ)) * Real.log (x:ℝ) with hA_def
  set H := ∑ p ∈ ((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => p < y),
      f p * ((vonMangoldt p : ℝ) : ℂ)
        * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
            f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ) with hH_def
  set Tl := ∑ p ∈ ((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => x < 2*p),
      f p * ((vonMangoldt p : ℝ) : ℂ)
        * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
            f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ) with hTl_def
  set Sv := ∑ p ∈ (((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p),
      f p * ((vonMangoldt p : ℝ) : ℂ)
        * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
            f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ) with hSv_def
  set C := tripleConvRC f x ((((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p)) with hC_def
  set Sp := ∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime,
      f p * ((vonMangoldt p : ℝ) : ℂ)
        * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
            f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ) with hSp_def
  -- the split as an equation between the named sums
  have hSp : Sp = H + (Tl + Sv) := by
    rw [← hsplit1, ← hsplit2]
  -- triangle chain
  have habs1 : ‖A‖ ≤ ‖A - Sp‖ + ‖Sp‖ := by
    have h : A = (A - Sp) + Sp := by ring
    calc ‖A‖ = ‖(A - Sp) + Sp‖ := by rw [← h]
      _ ≤ ‖A - Sp‖ + ‖Sp‖ := norm_add_le _ _
  have habs2 : ‖Sp‖ ≤ ‖H‖ + (‖Tl‖ + ‖Sv‖) := by
    rw [hSp]
    calc ‖H + (Tl + Sv)‖ ≤ ‖H‖ + ‖Tl + Sv‖ := norm_add_le _ _
      _ ≤ ‖H‖ + (‖Tl‖ + ‖Sv‖) := by
          have := norm_add_le Tl Sv
          linarith
  have habs3 : ‖Sv‖ ≤ ‖Sv - C‖ + ‖C‖ := by
    have h : Sv = (Sv - C) + C := by ring
    calc ‖Sv‖ = ‖(Sv - C) + C‖ := by rw [← h]
      _ ≤ ‖Sv - C‖ + ‖C‖ := norm_add_le _ _
  have hsum := add_le_add hid (add_le_add hhead (add_le_add htail
    (add_le_add hbridge hconv)))
  have hchain : ‖A‖ ≤ ‖A - Sp‖ + (‖H‖ + (‖Tl‖ + (‖Sv - C‖ + ‖C‖))) := by
    linarith [habs1, habs2, habs3]
  linarith [le_trans hchain hsum]



set_option maxHeartbeats 1600000 in
open Real Finset ArithmeticFunction in
/-- **§3, end to end, through the shell chain** (Track R, budget repair
R-b2-f): the identity/head/tail/bridge/survivor assembly with BOTH
repairs installed — the sharp survivors bridge prices the iteration at
`64x·(12·loglog x + 18)` (the `T4` repair), and the shell survivor
estimate prices the band at `K₀·(x·√((e^π)²·10¹⁵·(b²+1)) + 2x·log4)`
(the `+T·b²` repair).  Every remaining term is `x·polylog`-free against
`b²`. -/
theorem rieszMeanC_log_le_shell_of_nonPretentious (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hcm : CompletelyMultiplicativeC f)
    (h1 : f 1 = 1)
    (x y K₀ : ℕ) (hx : 10^16 ≤ x) (hy2 : 2 ≤ y) (hyx : 2*y ≤ x)
    (hy : (Real.log (x:ℝ))^2 ≤ (y:ℝ))
    (hK₀1 : 1 ≤ K₀)
    (hK₀low : Real.exp 1 * Real.log 2
      ≤ Real.exp (-(K₀:ℝ)) * Real.log (x:ℝ))
    (hK₀max : Real.exp (-((K₀:ℝ)+1)) * Real.log (x:ℝ)
      < Real.exp 1 * Real.log 2)
    (hX3 : ∀ k ∈ Finset.Icc 1 K₀, 3 ≤ x / blockLo x k)
    (b : ℝ) (hb0 : 0 ≤ b)
    (hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖ExpSums.smoothPhaseSum f x t‖ ≤ b) :
    ‖(∑ n ∈ Finset.Icc 1 x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
        * ((Real.log (x:ℝ) : ℝ) : ℂ)‖
      ≤ 35*(x:ℝ) + (x:ℝ)*(Real.log (y:ℝ) + 2) + 2*((x:ℝ)+1)*Real.log 4
        + 64 * (x:ℝ) * (12 * Real.log (Real.log (x:ℝ)) + 18)
        + ((K₀:ℝ) * ((x:ℝ) * Real.sqrt ((Real.exp π)^2 * 10^15 * (b^2 + 1))
            + 2*(x:ℝ)*Real.log 4)
          + 2 * ((x:ℝ) * (16 * ((Real.exp 1 - 1) * (Real.exp 1 * Real.log 2)
              + Real.log 2) + 16 * Real.log 4))) := by
  classical
  have hx1 : (1:ℕ) ≤ x := le_trans (by norm_num) hx
  have hid := rieszMeanC_mul_log_prime_restrict f hf hcm x hx1
  have hhead := rieszMeanC_prime_head_le f hf x y hy2
  have htail := rieszMeanC_prime_tail_le f hf x
  have hbridge := rieszMeanC_survivors_to_tripleConvRC_sharp f hf hcm x y
    (le_trans (by norm_num) hx)
  have hconv := tripleConvRC_survivors_balanced_shell_le f hf hcm h1 x y K₀
    hx hy2 hy hK₀1 hK₀low hK₀max hX3 b hb0 hBu
  -- the three-way split of the prime sum
  have hfe : (((Finset.Icc 1 x).filter Nat.Prime).filter
        (fun p => ¬ p < y)).filter (fun p => x < 2*p)
      = ((Finset.Icc 1 x).filter Nat.Prime).filter (fun p => x < 2*p) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hS, _⟩, h2⟩
      exact ⟨hS, h2⟩
    · rintro ⟨hS, h2⟩
      exact ⟨⟨hS, by omega⟩, h2⟩
  have hsplit1 := Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 x).filter Nat.Prime) (fun p => p < y)
    (fun p => f p * ((vonMangoldt p : ℝ) : ℂ)
      * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
          f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ))
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    (((Finset.Icc 1 x).filter Nat.Prime).filter (fun p => ¬ p < y))
    (fun p => x < 2*p)
    (fun p => f p * ((vonMangoldt p : ℝ) : ℂ)
      * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
          f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ))
  rw [hfe] at hsplit2
  -- name the five quantities
  set A := (∑ n ∈ Finset.Icc 1 x,
      f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ)) * Real.log (x:ℝ) with hA_def
  set H := ∑ p ∈ ((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => p < y),
      f p * ((vonMangoldt p : ℝ) : ℂ)
        * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
            f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ) with hH_def
  set Tl := ∑ p ∈ ((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => x < 2*p),
      f p * ((vonMangoldt p : ℝ) : ℂ)
        * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
            f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ) with hTl_def
  set Sv := ∑ p ∈ (((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p),
      f p * ((vonMangoldt p : ℝ) : ℂ)
        * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
            f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ) with hSv_def
  set C := tripleConvRC f x ((((Finset.Icc 1 x).filter Nat.Prime).filter
      (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p)) with hC_def
  set Sp := ∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime,
      f p * ((vonMangoldt p : ℝ) : ℂ)
        * ∑ m ∈ Finset.Icc 1 ⌊(x:ℝ)/(p:ℝ)⌋₊,
            f m * ((Real.log ((x:ℝ)/(p:ℝ)) - Real.log (m:ℝ) : ℝ) : ℂ) with hSp_def
  -- the split as an equation between the named sums
  have hSp : Sp = H + (Tl + Sv) := by
    rw [← hsplit1, ← hsplit2]
  -- triangle chain
  have habs1 : ‖A‖ ≤ ‖A - Sp‖ + ‖Sp‖ := by
    have h : A = (A - Sp) + Sp := by ring
    calc ‖A‖ = ‖(A - Sp) + Sp‖ := by rw [← h]
      _ ≤ ‖A - Sp‖ + ‖Sp‖ := norm_add_le _ _
  have habs2 : ‖Sp‖ ≤ ‖H‖ + (‖Tl‖ + ‖Sv‖) := by
    rw [hSp]
    calc ‖H + (Tl + Sv)‖ ≤ ‖H‖ + ‖Tl + Sv‖ := norm_add_le _ _
      _ ≤ ‖H‖ + (‖Tl‖ + ‖Sv‖) := by
          have := norm_add_le Tl Sv
          linarith
  have habs3 : ‖Sv‖ ≤ ‖Sv - C‖ + ‖C‖ := by
    have h : Sv = (Sv - C) + C := by ring
    calc ‖Sv‖ = ‖(Sv - C) + C‖ := by rw [← h]
      _ ≤ ‖Sv - C‖ + ‖C‖ := norm_add_le _ _
  have hsum := add_le_add hid (add_le_add hhead (add_le_add htail
    (add_le_add hbridge hconv)))
  have hchain : ‖A‖ ≤ ‖A - Sp‖ + (‖H‖ + (‖Tl‖ + (‖Sv - C‖ + ‖C‖))) := by
    linarith [habs1, habs2, habs3]
  linarith [le_trans hchain hsum]

open Real Finset in
/-- **The log-free Halász Riesz mean** (Track R, M0R-5, the campaign
goal): under `NonPretentiousAt` at strength `A` with the band inside
the frequency range (`7(halaszM+1) ≤ A·x`, using `2π < 7`), the FULL
Riesz mean at the top scale obeys

  `‖R_f(x)·log x| ≤ … + K₀·(x·√(2000·(e^π)²·10¹⁵·(((log⌈T²⌉+2)² + T + 1)·(e⁵(2+log x)e^{−A})² + 1)) + …) + …`

— `rieszMean_log_le'_of_nonPretentious` at
`b := e⁵·(2+log x)·e^{−A}`, discharged by
`norm_smoothPhaseSum_le_of_nonPretentious`.  No `y₂`-smooth
restriction, no `W ≈ 2×10⁷` detour losses: the band-sup quality is
`e^{−A}` against the *log-free* prefactor `e⁵(2+log x)` — Halász for
the Riesz mean, through the truncated Euler product. -/
theorem rieszMeanC_log_le_halasz_of_nonPretentious (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hcm : CompletelyMultiplicativeC f)
    (h1 : f 1 = 1)
    (x y K₀ : ℕ) (hx : 10^16 ≤ x) (hy2 : 2 ≤ y) (hyx : 2*y ≤ x)
    (T : ℝ) (hT1 : Real.sqrt (21 * Real.log (x:ℝ)) ≤ T)
    (hT2 : T ≤ Real.log (x:ℝ)) (hTy : T^2 ≤ (y:ℝ))
    (hK₀1 : 1 ≤ K₀)
    (hK₀low : Real.exp 1 * Real.log 2
      ≤ Real.exp (-(K₀:ℝ)) * Real.log (x:ℝ))
    (hK₀max : Real.exp (-((K₀:ℝ)+1)) * Real.log (x:ℝ)
      < Real.exp 1 * Real.log 2)
    (A : ℝ) (hA : NonPretentiousAt f A x)
    (h1A : 1 ≤ A)
    (hband : 7 * (((halaszM x : ℕ):ℝ) + 1) ≤ A * (x:ℝ)) :
    ‖(∑ n ∈ Finset.Icc 1 x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
        * ((Real.log (x:ℝ) : ℝ) : ℂ)‖
      ≤ 35*(x:ℝ) + (x:ℝ)*(Real.log (y:ℝ) + 2) + 2*((x:ℝ)+1)*Real.log 4
        + 64 * (x:ℝ) / Real.log 2 * (Real.log ((x+1:ℕ):ℝ) + 2)
        + ((K₀:ℝ) * ((x:ℝ) * Real.sqrt (2000 * ((Real.exp π)^2 * 10^15
              * (((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1)
                * (Real.exp 5 * (2 + Real.log (x:ℝ))
                    * Real.exp (-A))^2 + 1)))
            + 2*(x:ℝ)*Real.log 4)
          + 2 * ((x:ℝ) * (16 * ((Real.exp 1 - 1) * (Real.exp 1 * Real.log 2)
              + Real.log 2) + 16 * Real.log 4))) := by
  classical
  have hx3 : (3:ℕ) ≤ x := le_trans (by norm_num) hx
  have hb0 : (0:ℝ) ≤ Real.exp 5 * (2 + Real.log (x:ℝ)) * Real.exp (-A) := by
    have h2L : (0:ℝ) ≤ 2 + Real.log (x:ℝ) := by
      have := Real.log_natCast_nonneg x
      linarith
    exact mul_nonneg (mul_nonneg (Real.exp_pos 5).le h2L)
      (Real.exp_pos (-A)).le
  have hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖ExpSums.smoothPhaseSum f x t‖
        ≤ Real.exp 5 * (2 + Real.log (x:ℝ)) * Real.exp (-A) := by
    intro t ht
    refine ExpSums.norm_smoothPhaseSum_le_of_nonPretentious
      f hcm h1 hf x hx3 A h1A hA t ?_
    -- `|2πt| ≤ 7·(M+1) ≤ A·x`, using `2π < 7`
    have hpi7 : 2 * Real.pi ≤ 7 := by
      have := Real.pi_lt_d2
      linarith
    rw [abs_mul, abs_of_pos Real.two_pi_pos]
    calc 2 * Real.pi * |t| ≤ 7 * |t| :=
          mul_le_mul_of_nonneg_right hpi7 (abs_nonneg t)
      _ ≤ 7 * (((halaszM x : ℕ):ℝ) + 1) :=
          mul_le_mul_of_nonneg_left ht (by norm_num)
      _ ≤ A * (x:ℝ) := hband
  exact rieszMeanC_log_le'_of_nonPretentious f hf hcm h1 x y K₀ hx hy2 hyx
    T hT1 hT2 hTy hK₀1 hK₀low hK₀max
    (three_le_div_blockLo x K₀ hx hK₀low)
    (Real.exp 5 * (2 + Real.log (x:ℝ)) * Real.exp (-A)) hb0 hBu



open Real Finset in
/-- **The log-free Halász Riesz mean, shell form** (Track R, budget
repair R-b2-g): the b-instantiation of the shell §3 assembly at
`b := e⁵(2+log x)e^{−A}` — the quality slot of the repaired budget,
with no `T` and no window residue against it. -/
theorem rieszMeanC_log_le_halasz_shell_of_nonPretentious (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hcm : CompletelyMultiplicativeC f)
    (h1 : f 1 = 1)
    (x y K₀ : ℕ) (hx : 10^16 ≤ x) (hy2 : 2 ≤ y) (hyx : 2*y ≤ x)
    (hy : (Real.log (x:ℝ))^2 ≤ (y:ℝ))
    (hK₀1 : 1 ≤ K₀)
    (hK₀low : Real.exp 1 * Real.log 2
      ≤ Real.exp (-(K₀:ℝ)) * Real.log (x:ℝ))
    (hK₀max : Real.exp (-((K₀:ℝ)+1)) * Real.log (x:ℝ)
      < Real.exp 1 * Real.log 2)
    (A : ℝ) (hA : NonPretentiousAt f A x)
    (h1A : 1 ≤ A)
    (hband : 7 * (((halaszM x : ℕ):ℝ) + 1) ≤ A * (x:ℝ)) :
    ‖(∑ n ∈ Finset.Icc 1 x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
        * ((Real.log (x:ℝ) : ℝ) : ℂ)‖
      ≤ 35*(x:ℝ) + (x:ℝ)*(Real.log (y:ℝ) + 2) + 2*((x:ℝ)+1)*Real.log 4
        + 64 * (x:ℝ) * (12 * Real.log (Real.log (x:ℝ)) + 18)
        + ((K₀:ℝ) * ((x:ℝ) * Real.sqrt ((Real.exp π)^2 * 10^15
              * ((Real.exp 5 * (2 + Real.log (x:ℝ))
                  * Real.exp (-A))^2 + 1))
            + 2*(x:ℝ)*Real.log 4)
          + 2 * ((x:ℝ) * (16 * ((Real.exp 1 - 1) * (Real.exp 1 * Real.log 2)
              + Real.log 2) + 16 * Real.log 4))) := by
  classical
  have hx3 : (3:ℕ) ≤ x := le_trans (by norm_num) hx
  have hb0 : (0:ℝ) ≤ Real.exp 5 * (2 + Real.log (x:ℝ)) * Real.exp (-A) := by
    have h2L : (0:ℝ) ≤ 2 + Real.log (x:ℝ) := by
      have := Real.log_natCast_nonneg x
      linarith
    exact mul_nonneg (mul_nonneg (Real.exp_pos 5).le h2L)
      (Real.exp_pos (-A)).le
  have hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖ExpSums.smoothPhaseSum f x t‖
        ≤ Real.exp 5 * (2 + Real.log (x:ℝ)) * Real.exp (-A) := by
    intro t ht
    refine ExpSums.norm_smoothPhaseSum_le_of_nonPretentious
      f hcm h1 hf x hx3 A h1A hA t ?_
    -- `|2πt| ≤ 7·(M+1) ≤ A·x`, using `2π < 7`
    have hpi7 : 2 * Real.pi ≤ 7 := by
      have := Real.pi_lt_d2
      linarith
    rw [abs_mul, abs_of_pos Real.two_pi_pos]
    calc 2 * Real.pi * |t| ≤ 7 * |t| :=
          mul_le_mul_of_nonneg_right hpi7 (abs_nonneg t)
      _ ≤ 7 * (((halaszM x : ℕ):ℝ) + 1) :=
          mul_le_mul_of_nonneg_left ht (by norm_num)
      _ ≤ A * (x:ℝ) := hband
  exact rieszMeanC_log_le_shell_of_nonPretentious f hf hcm h1 x y K₀ hx hy2
    hyx hy hK₀1 hK₀low hK₀max
    (three_le_div_blockLo x K₀ hx hK₀low)
    (Real.exp 5 * (2 + Real.log (x:ℝ)) * Real.exp (-A)) hb0 hBu

open Real Finset in
/-- **Flat differencing** (Track R, M0R-6a): the plain sum at `x'` is
priced by two Riesz means and the edge mass —

  `|S(x')|·(log x − log x') ≤ |R(x)| + |R(x')| + (x−x')·(log x − log x')`.

Splitting `Icc 1 x` at `x'` gives the exact identity
`R(x) = R(x') + S(x')·log(x/x') + ∑_{x'<n≤x} f(n)·log(x/n)`, and every
edge term is at most `log(x/x')` in absolute value.  Downstream the
two Riesz means carry the log-free Halász bound at scales `x` and
`x'`, and choosing `log(x/x') ≍ e^{−A/2}` splits the quality evenly —
the √-loss of the flat recovery. -/
theorem plain_sumC_mul_log_ratio_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x' x : ℕ) (hx'1 : 1 ≤ x') (hx'x : x' ≤ x) :
    ‖∑ n ∈ Finset.Icc 1 x', f n‖ * (Real.log (x:ℝ) - Real.log (x':ℝ))
      ≤ ‖∑ n ∈ Finset.Icc 1 x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ)‖
        + ‖∑ n ∈ Finset.Icc 1 x', f n * ((Real.log (x':ℝ) - Real.log (n:ℝ) : ℝ) : ℂ)‖
        + ((x:ℝ) - (x':ℝ)) * (Real.log (x:ℝ) - Real.log (x':ℝ)) := by
  classical
  have hx'0 : (0:ℝ) < (x':ℝ) := by exact_mod_cast (by omega : 0 < x')
  have hlogd0 : (0:ℝ) ≤ Real.log (x:ℝ) - Real.log (x':ℝ) := by
    have := Real.log_le_log hx'0 (by exact_mod_cast hx'x : (x':ℝ) ≤ (x:ℝ))
    linarith
  -- the split of the index range at `x'`
  have hunion : Finset.Icc 1 x' ∪ Finset.Ioc x' x = Finset.Icc 1 x := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 x') (Finset.Ioc x' x) := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_Ioc] at hn'
    omega
  -- the exact differencing identity
  have hkey : ∑ n ∈ Finset.Icc 1 x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ)
      = (∑ n ∈ Finset.Icc 1 x', f n * ((Real.log (x':ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
        + (∑ n ∈ Finset.Icc 1 x', f n)
            * ((Real.log (x:ℝ) - Real.log (x':ℝ) : ℝ) : ℂ)
        + ∑ n ∈ Finset.Ioc x' x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ) := by
    rw [← hunion, Finset.sum_union hdisj]
    have hhead : ∑ n ∈ Finset.Icc 1 x',
        f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ)
        = (∑ n ∈ Finset.Icc 1 x', f n * ((Real.log (x':ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
          + (∑ n ∈ Finset.Icc 1 x', f n)
              * ((Real.log (x:ℝ) - Real.log (x':ℝ) : ℝ) : ℂ) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      push_cast
      ring
    rw [hhead]
  -- the edge mass: each term at most `log x − log x'`
  have hedge : ‖∑ n ∈ Finset.Ioc x' x,
      f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ)‖
      ≤ ((x:ℝ) - (x':ℝ)) * (Real.log (x:ℝ) - Real.log (x':ℝ)) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n ∈ Finset.Ioc x' x,
        ‖f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ)‖
          ≤ Real.log (x:ℝ) - Real.log (x':ℝ) := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      have hn0 : (0:ℝ) < (n:ℝ) := by
        exact_mod_cast (by omega : 0 < n)
      have hlogn : Real.log (x':ℝ) ≤ Real.log (n:ℝ) :=
        Real.log_le_log hx'0 (by exact_mod_cast hn.1.le : (x':ℝ) ≤ (n:ℝ))
      have hlognx : Real.log (n:ℝ) ≤ Real.log (x:ℝ) :=
        Real.log_le_log hn0 (by exact_mod_cast hn.2 : (n:ℝ) ≤ (x:ℝ))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : (0:ℝ)
          ≤ Real.log (x:ℝ) - Real.log (n:ℝ))]
      calc ‖f n‖ * (Real.log (x:ℝ) - Real.log (n:ℝ))
          ≤ 1 * (Real.log (x:ℝ) - Real.log (n:ℝ)) :=
            mul_le_mul_of_nonneg_right (hf n) (by linarith)
        _ = Real.log (x:ℝ) - Real.log (n:ℝ) := one_mul _
        _ ≤ Real.log (x:ℝ) - Real.log (x':ℝ) := by linarith
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    have hcast : ((x - x' : ℕ):ℝ) = (x:ℝ) - (x':ℝ) := by
      rw [Nat.cast_sub hx'x]
    rw [hcast]
  -- assemble: `S(x')·(log x − log x') = R(x) − R(x') − edge`
  have hS : (∑ n ∈ Finset.Icc 1 x', f n)
        * ((Real.log (x:ℝ) - Real.log (x':ℝ) : ℝ) : ℂ)
      = (∑ n ∈ Finset.Icc 1 x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
        - (∑ n ∈ Finset.Icc 1 x', f n * ((Real.log (x':ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
        - ∑ n ∈ Finset.Ioc x' x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ) := by
    rw [hkey]
    ring
  have hLHS : ‖∑ n ∈ Finset.Icc 1 x', f n‖
        * (Real.log (x:ℝ) - Real.log (x':ℝ))
      = ‖(∑ n ∈ Finset.Icc 1 x', f n)
          * ((Real.log (x:ℝ) - Real.log (x':ℝ) : ℝ) : ℂ)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogd0]
  rw [hLHS, hS]
  calc ‖(∑ n ∈ Finset.Icc 1 x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
        - (∑ n ∈ Finset.Icc 1 x', f n * ((Real.log (x':ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
        - ∑ n ∈ Finset.Ioc x' x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ)‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
          - (∑ n ∈ Finset.Icc 1 x',
              f n * ((Real.log (x':ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))‖
        + ‖∑ n ∈ Finset.Ioc x' x,
            f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ ‖∑ n ∈ Finset.Icc 1 x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ)‖
        + ‖∑ n ∈ Finset.Icc 1 x', f n * ((Real.log (x':ℝ) - Real.log (n:ℝ) : ℝ) : ℂ)‖
        + ‖∑ n ∈ Finset.Ioc x' x,
            f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ)‖ := by
      have := norm_sub_le (∑ n ∈ Finset.Icc 1 x,
          f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
        (∑ n ∈ Finset.Icc 1 x', f n * ((Real.log (x':ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
      linarith
    _ ≤ ‖∑ n ∈ Finset.Icc 1 x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ)‖
        + ‖∑ n ∈ Finset.Icc 1 x', f n * ((Real.log (x':ℝ) - Real.log (n:ℝ) : ℝ) : ℂ)‖
        + ((x:ℝ) - (x':ℝ)) * (Real.log (x:ℝ) - Real.log (x':ℝ)) := by
      linarith [hedge]


open Real Finset in
/-- **The plain sum from two Riesz-mean bounds** (Track R, M0R-6b):
abstract glue over the differencing lemma — if the log-weighted Riesz
means at a target scale `x` and a top scale `X` are priced
(`|R(x)·log x| ≤ Bx`, `|R(X)·log X| ≤ BX`), then

  `|S(x)|·(log X − log x) ≤ BX/log X + Bx/log x + (X−x)·(log X − log x)`.

`B`-parametric on purpose: the Halász instantiation (`#3443` at both
scales) and the scale-ratio choice `log(X/x) ≍ e^{−A/2}` happen at
packaging time, keeping this statement small. -/
theorem plain_sumC_le_of_riesz_bounds (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x X : ℕ) (hx2 : 2 ≤ x) (hxX : x ≤ X)
    (Bx BX : ℝ)
    (hRx : ‖(∑ n ∈ Finset.Icc 1 x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
        * ((Real.log (x:ℝ) : ℝ) : ℂ)‖ ≤ Bx)
    (hRX : ‖(∑ n ∈ Finset.Icc 1 X, f n * ((Real.log (X:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
        * ((Real.log (X:ℝ) : ℝ) : ℂ)‖ ≤ BX) :
    ‖∑ n ∈ Finset.Icc 1 x, f n‖ * (Real.log (X:ℝ) - Real.log (x:ℝ))
      ≤ BX / Real.log (X:ℝ) + Bx / Real.log (x:ℝ)
        + ((X:ℝ) - (x:ℝ)) * (Real.log (X:ℝ) - Real.log (x:ℝ)) := by
  have hLx : (0:ℝ) < Real.log (x:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 2 ≤ x))
  have hLX : (0:ℝ) < Real.log (X:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 2 ≤ X))
  -- each Riesz mean is priced by its budget over its own log
  have hRx' : ‖∑ n ∈ Finset.Icc 1 x,
      f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ)‖ ≤ Bx / Real.log (x:ℝ) := by
    rw [le_div_iff₀ hLx]
    calc ‖∑ n ∈ Finset.Icc 1 x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ)‖
          * Real.log (x:ℝ)
        = ‖(∑ n ∈ Finset.Icc 1 x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
            * ((Real.log (x:ℝ) : ℝ) : ℂ)‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLx]
      _ ≤ Bx := hRx
  have hRX' : ‖∑ n ∈ Finset.Icc 1 X,
      f n * ((Real.log (X:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ)‖ ≤ BX / Real.log (X:ℝ) := by
    rw [le_div_iff₀ hLX]
    calc ‖∑ n ∈ Finset.Icc 1 X, f n * ((Real.log (X:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ)‖
          * Real.log (X:ℝ)
        = ‖(∑ n ∈ Finset.Icc 1 X, f n * ((Real.log (X:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
            * ((Real.log (X:ℝ) : ℝ) : ℂ)‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLX]
      _ ≤ BX := hRX
  have hdiff := plain_sumC_mul_log_ratio_le f hf x X (by omega) hxX
  linarith [hdiff, hRx', hRX']


set_option maxHeartbeats 1600000 in
open Real Finset in
/-- **The log-free Halász Riesz mean, windowed** (Track R, M0R-6c):
`rieszMean_log_le_halasz_of_nonPretentious` with the §3 window
destructured (`exists_section3_window`) and every window quantity
priced in `x` alone: `log y ≤ log(2·log²x)`, `K₀ ≤ log log x`
(from the mass floor `e·log 2 ≤ e^{−K₀}·log x` and `e·log 2 ≥ 1`),
`log⌈T²⌉ ≤ log(2·log²x + 1)`, `T ≤ log x`.  The RHS depends only on
`x` and `A` — the shape the flat-differencing glue consumes at two
scales. -/
theorem rieszMeanC_log_halasz_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (x : ℕ) (hx : 10^16 ≤ x)
    (A : ℝ) (hA : NonPretentiousAt f A x)
    (h1A : 1 ≤ A)
    (hband : 7 * (((halaszM x : ℕ):ℝ) + 1) ≤ A * (x:ℝ)) :
    ‖(∑ n ∈ Finset.Icc 1 x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
        * ((Real.log (x:ℝ) : ℝ) : ℂ)‖
      ≤ 35*(x:ℝ) + (x:ℝ)*(Real.log (2*(Real.log (x:ℝ))^2) + 2)
        + 2*((x:ℝ)+1)*Real.log 4
        + 64 * (x:ℝ) / Real.log 2 * (Real.log ((x+1:ℕ):ℝ) + 2)
        + (Real.log (Real.log (x:ℝ))
            * ((x:ℝ) * Real.sqrt (2000 * ((Real.exp π)^2 * 10^15
                * (((Real.log (2*(Real.log (x:ℝ))^2 + 1) + 2)^2
                    + Real.log (x:ℝ) + 1)
                  * (Real.exp 5 * (2 + Real.log (x:ℝ))
                      * Real.exp (-A))^2 + 1)))
              + 2*(x:ℝ)*Real.log 4)
          + 2 * ((x:ℝ) * (16 * ((Real.exp 1 - 1) * (Real.exp 1 * Real.log 2)
              + Real.log 2) + 16 * Real.log 4))) := by
  classical
  obtain ⟨y, K₀, T, hy2, hyx, hT1, hT2, hTy, hylog, hK₀1, hK₀low, hK₀max⟩ :=
    exists_section3_window x hx
  have hcap := rieszMeanC_log_le_halasz_of_nonPretentious f hf hcm h1
    x y K₀ hx hy2 hyx T hT1 hT2 hTy hK₀1 hK₀low hK₀max A hA h1A hband
  refine le_trans hcap ?_
  have hxR0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
  have hL0 : (0:ℝ) < Real.log (x:ℝ) :=
    Real.log_pos (by exact_mod_cast (by
      have : (2:ℕ) ≤ x := le_trans (by norm_num) hx
      omega : (1:ℕ) < x))
  obtain ⟨h5T, hLT2, hγT⟩ := T_window_conditions x T hx hT1 hT2
  have hlog4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  -- the y-term: `log y ≤ log(2·log²x)`
  have hy0 : (0:ℝ) < (y:ℝ) := by exact_mod_cast (by omega : 0 < y)
  have hylog' : Real.log (y:ℝ) ≤ Real.log (2*(Real.log (x:ℝ))^2) :=
    Real.log_le_log hy0 hylog
  have hyterm : (x:ℝ)*(Real.log (y:ℝ) + 2)
      ≤ (x:ℝ)*(Real.log (2*(Real.log (x:ℝ))^2) + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hxR0
  -- the K₀-multiplier: `K₀ ≤ log log x`
  have he_log2 : (1:ℝ) ≤ Real.exp 1 * Real.log 2 := by
    nlinarith [Real.exp_one_gt_d9, Real.log_two_gt_d9]
  have hexpK : Real.exp ((K₀:ℝ)) * (Real.exp 1 * Real.log 2)
      ≤ Real.log (x:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hK₀low (Real.exp_pos ((K₀:ℝ))).le
    have hid : Real.exp ((K₀:ℝ)) * (Real.exp (-(K₀:ℝ)) * Real.log (x:ℝ))
        = Real.log (x:ℝ) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    rw [hid] at h
    exact h
  have hexpK' : Real.exp ((K₀:ℝ)) ≤ Real.log (x:ℝ) := by
    nlinarith [Real.exp_pos ((K₀:ℝ)), he_log2, hexpK]
  have hK₀le : ((K₀:ℕ):ℝ) ≤ Real.log (Real.log (x:ℝ)) :=
    calc ((K₀:ℕ):ℝ) = Real.log (Real.exp ((K₀:ℝ))) := (Real.log_exp _).symm
      _ ≤ Real.log (Real.log (x:ℝ)) :=
          Real.log_le_log (Real.exp_pos _) hexpK'
  -- the √-argument monotonicity
  have hT0 : (0:ℝ) < T := by linarith
  have hceil0 : (0:ℝ) < ((⌈T^2⌉₊ : ℕ):ℝ) := by
    have : (0:ℕ) < ⌈T^2⌉₊ := Nat.ceil_pos.mpr (by positivity)
    exact_mod_cast this
  have hceil_le : ((⌈T^2⌉₊ : ℕ):ℝ) ≤ 2*(Real.log (x:ℝ))^2 + 1 := by
    have h1' := Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ T^2)
    linarith [hTy, hylog]
  have hc1 : Real.log ((⌈T^2⌉₊ : ℕ):ℝ)
      ≤ Real.log (2*(Real.log (x:ℝ))^2 + 1) :=
    Real.log_le_log hceil0 hceil_le
  have hc10 : (0:ℝ) ≤ Real.log ((⌈T^2⌉₊ : ℕ):ℝ) :=
    Real.log_natCast_nonneg _
  have hc1sq : (Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2
      ≤ (Real.log (2*(Real.log (x:ℝ))^2 + 1) + 2)^2 := by
    have hc1a : (0:ℝ) ≤ Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2 := by linarith
    have hc1b : Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2
        ≤ Real.log (2*(Real.log (x:ℝ))^2 + 1) + 2 := by linarith
    exact pow_le_pow_left₀ hc1a hc1b 2
  have hb2 : (0:ℝ) ≤ (Real.exp 5 * (2 + Real.log (x:ℝ))
      * Real.exp (-A))^2 := sq_nonneg _
  have hargle : 2000 * ((Real.exp π)^2 * 10^15
        * (((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1)
          * (Real.exp 5 * (2 + Real.log (x:ℝ)) * Real.exp (-A))^2 + 1))
      ≤ 2000 * ((Real.exp π)^2 * 10^15
        * (((Real.log (2*(Real.log (x:ℝ))^2 + 1) + 2)^2
            + Real.log (x:ℝ) + 1)
          * (Real.exp 5 * (2 + Real.log (x:ℝ)) * Real.exp (-A))^2 + 1)) := by
    have hin : ((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1)
        * (Real.exp 5 * (2 + Real.log (x:ℝ)) * Real.exp (-A))^2
        ≤ ((Real.log (2*(Real.log (x:ℝ))^2 + 1) + 2)^2
            + Real.log (x:ℝ) + 1)
          * (Real.exp 5 * (2 + Real.log (x:ℝ)) * Real.exp (-A))^2 :=
      mul_le_mul_of_nonneg_right (by linarith [hc1sq, hT2]) hb2
    have hC0 : (0:ℝ) ≤ 2000 * ((Real.exp π)^2 * 10^15) := by positivity
    nlinarith [hin, hC0]
  -- the bracket and the K₀-product
  have hbrk_le : (x:ℝ) * Real.sqrt (2000 * ((Real.exp π)^2 * 10^15
        * (((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1)
          * (Real.exp 5 * (2 + Real.log (x:ℝ)) * Real.exp (-A))^2 + 1)))
        + 2*(x:ℝ)*Real.log 4
      ≤ (x:ℝ) * Real.sqrt (2000 * ((Real.exp π)^2 * 10^15
          * (((Real.log (2*(Real.log (x:ℝ))^2 + 1) + 2)^2
              + Real.log (x:ℝ) + 1)
            * (Real.exp 5 * (2 + Real.log (x:ℝ)) * Real.exp (-A))^2 + 1)))
        + 2*(x:ℝ)*Real.log 4 := by
    have hs := Real.sqrt_le_sqrt hargle
    have := mul_le_mul_of_nonneg_left hs hxR0
    linarith
  have hbrk0 : (0:ℝ) ≤ (x:ℝ) * Real.sqrt (2000 * ((Real.exp π)^2 * 10^15
        * (((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1)
          * (Real.exp 5 * (2 + Real.log (x:ℝ)) * Real.exp (-A))^2 + 1)))
        + 2*(x:ℝ)*Real.log 4 := by
    have h1' : (0:ℝ) ≤ (x:ℝ) * Real.sqrt (2000 * ((Real.exp π)^2 * 10^15
        * (((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1)
          * (Real.exp 5 * (2 + Real.log (x:ℝ)) * Real.exp (-A))^2 + 1))) :=
      mul_nonneg hxR0 (Real.sqrt_nonneg _)
    have h2' : (0:ℝ) ≤ 2*(x:ℝ)*Real.log 4 := by
      have := mul_nonneg (by linarith : (0:ℝ) ≤ 2*(x:ℝ)) hlog4
      linarith
    linarith
  have hLL0 : (0:ℝ) ≤ Real.log (Real.log (x:ℝ)) := by
    have h21 : (21:ℝ) ≤ Real.log (x:ℝ) := by
      have hs21 : Real.sqrt (21 * Real.log (x:ℝ)) ≤ Real.log (x:ℝ) :=
        le_trans hT1 hT2
      have hnn : (0:ℝ) ≤ 21 * Real.log (x:ℝ) := by positivity
      have := mul_self_le_mul_self (Real.sqrt_nonneg _) hs21
      rw [Real.mul_self_sqrt hnn] at this
      nlinarith [hL0]
    exact Real.log_nonneg (by linarith)
  have hKprod : ((K₀:ℕ):ℝ) * ((x:ℝ) * Real.sqrt (2000 * ((Real.exp π)^2
          * 10^15 * (((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1)
          * (Real.exp 5 * (2 + Real.log (x:ℝ)) * Real.exp (-A))^2 + 1)))
        + 2*(x:ℝ)*Real.log 4)
      ≤ Real.log (Real.log (x:ℝ))
        * ((x:ℝ) * Real.sqrt (2000 * ((Real.exp π)^2 * 10^15
            * (((Real.log (2*(Real.log (x:ℝ))^2 + 1) + 2)^2
                + Real.log (x:ℝ) + 1)
              * (Real.exp 5 * (2 + Real.log (x:ℝ)) * Real.exp (-A))^2 + 1)))
          + 2*(x:ℝ)*Real.log 4) :=
    mul_le_mul hK₀le hbrk_le hbrk0 hLL0
  have hstep : 2 * ((x:ℝ) * (16 * ((Real.exp 1 - 1) * (Real.exp 1 * Real.log 2)
      + Real.log 2) + 16 * Real.log 4))
      ≤ 2 * ((x:ℝ) * (16 * ((Real.exp 1 - 1) * (Real.exp 1 * Real.log 2)
      + Real.log 2) + 16 * Real.log 4)) := le_rfl
  exact add_le_add
    (add_le_add_left
      (add_le_add_left
        (add_le_add_right hyterm (35*(x:ℝ)))
        (2*((x:ℝ)+1)*Real.log 4))
      (64 * (x:ℝ) / Real.log 2 * (Real.log ((x+1:ℕ):ℝ) + 2)))
    (add_le_add hKprod hstep)





set_option maxHeartbeats 1600000 in
open Real Finset in
/-- **The log-free Halász Riesz mean, windowed, shell form** (Track R,
budget repair R-b2-g): the shell window destructured and every window
quantity priced in `x` alone —

  `‖R(x)·log x‖ ≤ 35x + x(log(2·log²x)+2) + 2(x+1)·log4
     + 64x·(12·loglog x + 18)
     + loglog x·(x·√((e^π)²·10¹⁵·((e⁵(2+logx)e^{−A})²+1)) + 2x·log4)
     + 2x·(16((e−1)e·log2+log2)+16·log4)`

— the repaired budget `Ĥ′(x,A)`: the Mertens term is
`loglog`-additive, the quality group carries no window residue, and
the two-scale differencing glue can now consume it. -/
theorem rieszMeanC_log_halasz_shell_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (x : ℕ) (hx : 10^16 ≤ x)
    (A : ℝ) (hA : NonPretentiousAt f A x) (h1A : 1 ≤ A)
    (hband : 7 * (((halaszM x : ℕ):ℝ) + 1) ≤ A * (x:ℝ)) :
    ‖(∑ n ∈ Finset.Icc 1 x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
        * ((Real.log (x:ℝ) : ℝ) : ℂ)‖
      ≤ 35*(x:ℝ) + (x:ℝ)*(Real.log (2*(Real.log (x:ℝ))^2) + 2)
        + 2*((x:ℝ)+1)*Real.log 4
        + 64 * (x:ℝ) * (12 * Real.log (Real.log (x:ℝ)) + 18)
        + (Real.log (Real.log (x:ℝ))
            * ((x:ℝ) * Real.sqrt ((Real.exp π)^2 * 10^15
                * ((Real.exp 5 * (2 + Real.log (x:ℝ))
                    * Real.exp (-A))^2 + 1))
              + 2*(x:ℝ)*Real.log 4)
          + 2 * ((x:ℝ) * (16 * ((Real.exp 1 - 1) * (Real.exp 1 * Real.log 2)
              + Real.log 2) + 16 * Real.log 4))) := by
  classical
  obtain ⟨y, K₀, hy2, hyx, hy, hylog, hK₀1, hK₀low, hK₀max⟩ :=
    exists_section3_window_shell x hx
  have hcap := rieszMeanC_log_le_halasz_shell_of_nonPretentious f hf hcm h1
    x y K₀ hx hy2 hyx hy hK₀1 hK₀low hK₀max A hA h1A hband
  refine le_trans hcap ?_
  have hxR0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
  have hL0 : (0:ℝ) < Real.log (x:ℝ) :=
    Real.log_pos (by exact_mod_cast (by
      have : (2:ℕ) ≤ x := le_trans (by norm_num) hx
      omega : (1:ℕ) < x))
  have hlog4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hy0 : (0:ℝ) < (y:ℝ) := by exact_mod_cast (by omega : 0 < y)
  have hylog' : Real.log (y:ℝ) ≤ Real.log (2*(Real.log (x:ℝ))^2) :=
    Real.log_le_log hy0 hylog
  have hyterm : (x:ℝ)*(Real.log (y:ℝ) + 2)
      ≤ (x:ℝ)*(Real.log (2*(Real.log (x:ℝ))^2) + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hxR0
  have he_log2 : (1:ℝ) ≤ Real.exp 1 * Real.log 2 := by
    nlinarith [Real.exp_one_gt_d9, Real.log_two_gt_d9]
  have hexpK : Real.exp ((K₀:ℝ)) * (Real.exp 1 * Real.log 2)
      ≤ Real.log (x:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hK₀low (Real.exp_pos ((K₀:ℝ))).le
    have hid : Real.exp ((K₀:ℝ)) * (Real.exp (-(K₀:ℝ)) * Real.log (x:ℝ))
        = Real.log (x:ℝ) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    rw [hid] at h
    exact h
  have hexpK' : Real.exp ((K₀:ℝ)) ≤ Real.log (x:ℝ) := by
    nlinarith [Real.exp_pos ((K₀:ℝ)), he_log2, hexpK]
  have hK₀le : ((K₀:ℕ):ℝ) ≤ Real.log (Real.log (x:ℝ)) :=
    calc ((K₀:ℕ):ℝ) = Real.log (Real.exp ((K₀:ℝ))) := (Real.log_exp _).symm
      _ ≤ Real.log (Real.log (x:ℝ)) :=
          Real.log_le_log (Real.exp_pos _) hexpK'
  have hgrp0 : (0:ℝ) ≤ (x:ℝ) * Real.sqrt ((Real.exp π)^2 * 10^15
                * ((Real.exp 5 * (2 + Real.log (x:ℝ))
                    * Real.exp (-A))^2 + 1))
              + 2*(x:ℝ)*Real.log 4 := by positivity
  have hKprod : ((K₀:ℕ):ℝ) * ((x:ℝ) * Real.sqrt ((Real.exp π)^2 * 10^15
                * ((Real.exp 5 * (2 + Real.log (x:ℝ))
                    * Real.exp (-A))^2 + 1))
              + 2*(x:ℝ)*Real.log 4)
      ≤ Real.log (Real.log (x:ℝ)) * ((x:ℝ) * Real.sqrt ((Real.exp π)^2 * 10^15
                * ((Real.exp 5 * (2 + Real.log (x:ℝ))
                    * Real.exp (-A))^2 + 1))
              + 2*(x:ℝ)*Real.log 4) :=
    mul_le_mul_of_nonneg_right hK₀le hgrp0
  linarith [hyterm, hKprod]

open Real Finset in
/-- **The plain-sum log-free Halász bound** (Track R, M0R-6e, the M0R
campaign's final product): for `10¹⁶ ≤ x ≤ X` and `f` completely
multiplicative, `1`-bounded, non-pretentious at strength `A ≥ 1` at
both scales,

  `‖∑_{n≤x} f(n)‖·(log X − log x) ≤ Ĥ(X,A)/log X + Ĥ(x,A)/log x + (X−x)·(log X − log x)`,

with `Ĥ(z,A)` the windowed Halász budget of `rieszMean_log_halasz_le`
— every constant absolute, the quality `e⁵(2+log z)e^{−A}` log-free.
The consumer picks the scale ratio: `log(X/x) ≍ e^{−A/2}` balances the
two error groups (the √-loss), and any fixed ratio yields a
`(1+A)e^{−A}·polylog + loglog/log`-type saving — exactly what the
[mrt] A.2 layer's `ε`-form needs.  Both `hband`s are discharged by
`halaszM_band_le`; the window hypotheses by `exists_section3_window`
inside the windowed capstone. -/
theorem plain_sumC_le_halasz_of_nonPretentious (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hcm : CompletelyMultiplicativeC f)
    (h1 : f 1 = 1)
    (x X : ℕ) (hx : 10^16 ≤ x) (hxX : x ≤ X)
    (A : ℝ) (h1A : 1 ≤ A)
    (hAx : NonPretentiousAt f A x)
    (hAX : NonPretentiousAt f A X) :
    ‖∑ n ∈ Finset.Icc 1 x, f n‖ * (Real.log (X:ℝ) - Real.log (x:ℝ))
      ≤ (35*(X:ℝ) + (X:ℝ)*(Real.log (2*(Real.log (X:ℝ))^2) + 2)
          + 2*((X:ℝ)+1)*Real.log 4
          + 64 * (X:ℝ) / Real.log 2 * (Real.log ((X+1:ℕ):ℝ) + 2)
          + (Real.log (Real.log (X:ℝ))
              * ((X:ℝ) * Real.sqrt (2000 * ((Real.exp π)^2 * 10^15
                  * (((Real.log (2*(Real.log (X:ℝ))^2 + 1) + 2)^2
                      + Real.log (X:ℝ) + 1)
                    * (Real.exp 5 * (2 + Real.log (X:ℝ))
                        * Real.exp (-A))^2 + 1)))
                + 2*(X:ℝ)*Real.log 4)
            + 2 * ((X:ℝ) * (16 * ((Real.exp 1 - 1)
                * (Real.exp 1 * Real.log 2)
                + Real.log 2) + 16 * Real.log 4)))) / Real.log (X:ℝ)
        + (35*(x:ℝ) + (x:ℝ)*(Real.log (2*(Real.log (x:ℝ))^2) + 2)
          + 2*((x:ℝ)+1)*Real.log 4
          + 64 * (x:ℝ) / Real.log 2 * (Real.log ((x+1:ℕ):ℝ) + 2)
          + (Real.log (Real.log (x:ℝ))
              * ((x:ℝ) * Real.sqrt (2000 * ((Real.exp π)^2 * 10^15
                  * (((Real.log (2*(Real.log (x:ℝ))^2 + 1) + 2)^2
                      + Real.log (x:ℝ) + 1)
                    * (Real.exp 5 * (2 + Real.log (x:ℝ))
                        * Real.exp (-A))^2 + 1)))
                + 2*(x:ℝ)*Real.log 4)
            + 2 * ((x:ℝ) * (16 * ((Real.exp 1 - 1)
                * (Real.exp 1 * Real.log 2)
                + Real.log 2) + 16 * Real.log 4)))) / Real.log (x:ℝ)
        + ((X:ℝ) - (x:ℝ)) * (Real.log (X:ℝ) - Real.log (x:ℝ)) := by
  have hX : 10^16 ≤ X := le_trans hx hxX
  have hx2 : 2 ≤ x := le_trans (by norm_num) hx
  have hRx := rieszMeanC_log_halasz_le f hf hcm h1 x hx A hAx h1A
    (halaszM_band_le x hx A h1A)
  have hRX := rieszMeanC_log_halasz_le f hf hcm h1 X hX A hAX h1A
    (halaszM_band_le X hX A h1A)
  exact plain_sumC_le_of_riesz_bounds f hf x X hx2 hxX _ _ hRx hRX


open Real Finset in
/-- **The plain-sum log-free Halász bound, shell form** (Track R,
budget repair R-b2-h — the repaired capstone): for `10¹⁶ ≤ x ≤ X` and
`f` completely multiplicative, `1`-bounded, non-pretentious at
strength `A ≥ 1` at both scales,

  `‖∑_{n≤x} f(n)‖·(log X − log x)
     ≤ Ĥ′(X,A)/log X + Ĥ′(x,A)/log x + (X−x)·(log X − log x)`,

with `Ĥ′(z,A)` the REPAIRED budget of `rieszMeanC_log_halasz_shell_le`:
the Mertens term `64z·(12·loglog z+18)` is loglog-additive (the old
`64z/log2·(log(z+1)+2) ≈ 92·z·log z` was a full-log overpricing that
made the old capstone vacuous), and the quality group
`loglog z·z·√((e^π)²·10¹⁵·((e⁵(2+log z)e^{−A})²+1))` carries no window
residue (the old `(SM²+T+1)`-envelope's `√T`-surcharge is gone).
`Ĥ′(z,A)/log z ≍ z·(loglog²z·e^{−A}·polylog⁰ + loglog z/log z)` — the
classical GHS shape, and [mrt]'s `ρ ≈ 0.0606` regime closes. -/
theorem plain_sumC_le_halasz_shell_of_nonPretentious (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hcm : CompletelyMultiplicativeC f)
    (h1 : f 1 = 1)
    (x X : ℕ) (hx : 10^16 ≤ x) (hxX : x ≤ X)
    (A : ℝ) (h1A : 1 ≤ A)
    (hAx : NonPretentiousAt f A x)
    (hAX : NonPretentiousAt f A X) :
    ‖∑ n ∈ Finset.Icc 1 x, f n‖ * (Real.log (X:ℝ) - Real.log (x:ℝ))
      ≤ (35*(X:ℝ) + (X:ℝ)*(Real.log (2*(Real.log (X:ℝ))^2) + 2)
          + 2*((X:ℝ)+1)*Real.log 4
          + 64 * (X:ℝ) * (12 * Real.log (Real.log (X:ℝ)) + 18)
          + (Real.log (Real.log (X:ℝ))
              * ((X:ℝ) * Real.sqrt ((Real.exp π)^2 * 10^15
                  * ((Real.exp 5 * (2 + Real.log (X:ℝ))
                      * Real.exp (-A))^2 + 1))
                + 2*(X:ℝ)*Real.log 4)
            + 2 * ((X:ℝ) * (16 * ((Real.exp 1 - 1)
                * (Real.exp 1 * Real.log 2)
                + Real.log 2) + 16 * Real.log 4)))) / Real.log (X:ℝ)
        + (35*(x:ℝ) + (x:ℝ)*(Real.log (2*(Real.log (x:ℝ))^2) + 2)
          + 2*((x:ℝ)+1)*Real.log 4
          + 64 * (x:ℝ) * (12 * Real.log (Real.log (x:ℝ)) + 18)
          + (Real.log (Real.log (x:ℝ))
              * ((x:ℝ) * Real.sqrt ((Real.exp π)^2 * 10^15
                  * ((Real.exp 5 * (2 + Real.log (x:ℝ))
                      * Real.exp (-A))^2 + 1))
                + 2*(x:ℝ)*Real.log 4)
            + 2 * ((x:ℝ) * (16 * ((Real.exp 1 - 1)
                * (Real.exp 1 * Real.log 2)
                + Real.log 2) + 16 * Real.log 4)))) / Real.log (x:ℝ)
        + ((X:ℝ) - (x:ℝ)) * (Real.log (X:ℝ) - Real.log (x:ℝ)) := by
  have hX : 10^16 ≤ X := le_trans hx hxX
  have hx2 : 2 ≤ x := le_trans (by norm_num) hx
  have hRx := rieszMeanC_log_halasz_shell_le f hf hcm h1 x hx A hAx h1A
    (halaszM_band_le x hx A h1A)
  have hRX := rieszMeanC_log_halasz_shell_le f hf hcm h1 X hX A hAX h1A
    (halaszM_band_le X hX A h1A)
  exact plain_sumC_le_of_riesz_bounds f hf x X hx2 hxX _ _ hRx hRX

end MoltResearch
