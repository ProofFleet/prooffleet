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

end MoltResearch
