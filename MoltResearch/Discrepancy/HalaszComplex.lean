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

end MoltResearch
