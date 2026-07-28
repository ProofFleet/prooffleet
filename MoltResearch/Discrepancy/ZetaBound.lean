import MoltResearch.Discrepancy.LogDifferences
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Track C: the zeta tail estimate (Track L, campaign #3020)

The elementary tail bound for `∑ n^{-s}` beyond `2‖s-1‖`: each term is
telescoped against the potential `n^{1-s}/(s-1)`, with the second-order
exponential bound `‖e^z - 1 - z‖ ≤ ‖z‖²` standing in for calculus — no
integration anywhere. The partial sums of the tail are uniformly `≤ 4`,
hence so is the L-series remainder (`norm_LSeries_one_sub_partial_le`).
Together with `zeta_head_bound` this pins `‖ζ(s)‖` just right of the
`1`-line to `O(log|t|/log log|t|)` — the Littlewood-strength bound the
Vinogradov–Korobov interface reduces to.
-/

namespace MoltResearch

namespace ExpSums

open Finset

/-- Telescoping consecutive differences over an interval. -/
theorem sum_Ico_sub_succ {G : Type*} [AddCommGroup G] (f : ℕ → G)
    (N M : ℕ) (h : N ≤ M) :
    ∑ n ∈ Finset.Ico N M, (f n - f (n + 1)) = f N - f M := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h1 := Finset.sum_range_sub' (fun i => f (N + i)) (M - N)
  have h2 : N + (M - N) = M := by omega
  rw [h2] at h1
  exact h1

/-- The telescope potential `n^{1-s}/(s-1)`. -/
noncomputable def zPot (s : ℂ) (n : ℕ) : ℂ :=
  (n : ℂ) ^ ((1 : ℂ) - s) / (s - 1)

/-- **The per-term telescope error**: for `n ≥ ‖s-1‖`, the term `n^{-s}`
matches the potential difference up to `2‖s-1‖/n²`. -/
theorem cpow_sub_telescope_le (s : ℂ) (n : ℕ)
    (hσ1 : 1 ≤ s.re) (hs1 : 1 ≤ ‖s - 1‖) (hn : ‖s - 1‖ ≤ n) :
    ‖(n : ℂ) ^ (-s) - (zPot s n - zPot s (n + 1))‖
      ≤ 2 * ‖s - 1‖ / n ^ 2 := by
  have hn1 : 1 ≤ n := by
    by_contra h
    push_neg at h
    interval_cases n
    simp only [Nat.cast_zero] at hn
    linarith
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hnneC : ((n:ℕ):ℂ) ≠ 0 := by
    exact_mod_cast (by omega : n ≠ 0)
  have hsne : s - 1 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hs1
    linarith
  have hs0 : (0:ℝ) < ‖s - 1‖ := by linarith
  set L : ℝ := Real.log (1 + 1/n) with hLdef
  have hL0 : 0 ≤ L := by
    rw [hLdef]
    exact Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  have hLle : L ≤ 1/(n:ℝ) := by
    have h1 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 1/n by positivity)
    rw [← hLdef] at h1
    linarith
  have hLge : 1/((n:ℝ)+1) ≤ L := by
    have h1 := Real.log_le_sub_one_of_pos
      (show (0:ℝ) < (1 + 1/(n:ℝ))⁻¹ by positivity)
    rw [Real.log_inv, ← hLdef] at h1
    have h2 : ((1 + 1/(n:ℝ)))⁻¹ - 1 = -(1/((n:ℝ)+1)) := by
      rw [inv_eq_one_div]
      field_simp
      ring
    rw [h2] at h1
    linarith
  have hnL1 : (n:ℝ) * L ≤ 1 := by
    calc (n:ℝ) * L ≤ (n:ℝ) * (1/n) :=
          mul_le_mul_of_nonneg_left hLle hn0.le
      _ = 1 := by field_simp
  have hnL2 : 1 - 1/(n:ℝ) ≤ (n:ℝ) * L := by
    have h1 : (n:ℝ) * (1/((n:ℝ)+1)) ≤ (n:ℝ) * L :=
      mul_le_mul_of_nonneg_left hLge hn0.le
    have h2 : (n:ℝ) * (1/((n:ℝ)+1)) = 1 - 1/((n:ℝ)+1) := by
      field_simp
      ring
    have h3 : 1/((n:ℝ)+1) ≤ 1/(n:ℝ) :=
      one_div_le_one_div_of_le hn0 (by linarith)
    linarith
  have hplus : (((n+1 : ℕ)):ℂ) = ((n:ℝ):ℂ) * (((1 + 1/(n:ℝ) : ℝ)):ℂ) := by
    push_cast
    field_simp
  have hsplit : (((n+1 : ℕ)):ℂ) ^ ((1:ℂ) - s)
      = ((n:ℝ):ℂ) ^ ((1:ℂ) - s) * (((1 + 1/(n:ℝ) : ℝ)):ℂ) ^ ((1:ℂ) - s) := by
    rw [hplus, Complex.mul_cpow_ofReal_nonneg hn0.le (by positivity)]
  have hexp : (((1 + 1/(n:ℝ) : ℝ)):ℂ) ^ ((1:ℂ) - s)
      = Complex.exp ((L:ℂ) * ((1:ℂ) - s)) := by
    rw [Complex.cpow_def_of_ne_zero (by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        positivity),
      ← Complex.ofReal_log (by positivity : (0:ℝ) ≤ 1 + 1/(n:ℝ))]
  set z : ℂ := (L:ℂ) * ((1:ℂ) - s) with hzdef
  have hznorm : ‖z‖ = L * ‖s - 1‖ := by
    rw [hzdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hL0, ← norm_neg ((1:ℂ) - s)]
    ring_nf
  have hz1 : ‖z‖ ≤ 1 := by
    rw [hznorm]
    calc L * ‖s - 1‖ ≤ (1/n) * (n:ℝ) :=
          mul_le_mul hLle hn hs0.le (by positivity)
      _ = 1 := by field_simp
  set R : ℂ := Complex.exp z - 1 - z with hRdef
  have hR : ‖R‖ ≤ ‖z‖ ^ 2 := by
    rw [hRdef]
    exact Complex.norm_exp_sub_one_sub_id_le hz1
  have hone : ((n:ℝ):ℂ) = ((n:ℕ):ℂ) := by push_cast; ring
  have hpow1 : ((n:ℕ):ℂ) ^ ((1:ℂ) - s) = ((n:ℕ):ℂ) * ((n:ℕ):ℂ) ^ (-s) := by
    rw [show (1:ℂ) - s = 1 + (-s) by ring, Complex.cpow_add _ _ hnneC,
      Complex.cpow_one]
  have hexpz : Complex.exp ((L:ℂ) * ((1:ℂ) - s))
      = 1 + (L:ℂ) * ((1:ℂ) - s) + R := by
    rw [hRdef, hzdef]
    ring
  have hkey : (((n:ℕ)):ℂ) ^ (-s) - (zPot s n - zPot s (n + 1))
      = ((n:ℕ):ℂ) ^ (-s) * (((1 - (n:ℝ) * L : ℝ)):ℂ)
        + ((n:ℕ):ℂ) * ((n:ℕ):ℂ) ^ (-s) * R / (s - 1) := by
    rw [zPot, zPot, hsplit, hone, hexp, hexpz, hpow1]
    push_cast
    field_simp [hsne]
    ring
  rw [hkey]
  have hnorm1 : ‖((n:ℕ):ℂ) ^ (-s)‖ ≤ 1/(n:ℝ) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    have h1 : ((-s).re : ℝ) ≤ -1 := by
      simp only [Complex.neg_re]
      linarith
    calc ((n:ℝ)) ^ ((-s).re) ≤ ((n:ℝ)) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) h1
      _ = 1/(n:ℝ) := by
        rw [Real.rpow_neg_one, inv_eq_one_div]
  have hnormn : ‖((n:ℕ):ℂ)‖ = (n:ℝ) := by
    rw [Complex.norm_natCast]
  have habs : ‖(((1 - (n:ℝ) * L : ℝ)):ℂ)‖ ≤ 1/(n:ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith, by linarith⟩
  calc ‖((n:ℕ):ℂ) ^ (-s) * (((1 - (n:ℝ) * L : ℝ)):ℂ)
        + ((n:ℕ):ℂ) * ((n:ℕ):ℂ) ^ (-s) * R / (s - 1)‖
      ≤ ‖((n:ℕ):ℂ) ^ (-s) * (((1 - (n:ℝ) * L : ℝ)):ℂ)‖
        + ‖((n:ℕ):ℂ) * ((n:ℕ):ℂ) ^ (-s) * R / (s - 1)‖ := norm_add_le _ _
    _ ≤ (1/(n:ℝ)) * (1/(n:ℝ)) + ((n:ℝ) * (1/(n:ℝ)) * ‖R‖) / ‖s - 1‖ := by
        refine add_le_add ?_ ?_
        · rw [norm_mul]
          exact mul_le_mul hnorm1 habs (norm_nonneg _) (by positivity)
        · rw [norm_div, norm_mul, norm_mul, hnormn]
          gcongr
    _ ≤ 1/(n:ℝ)^2 + (L * ‖s - 1‖)^2 / ‖s - 1‖ := by
        refine add_le_add (le_of_eq (by ring)) ?_
        have hnum : (n:ℝ) * (1/(n:ℝ)) * ‖R‖ ≤ (L * ‖s - 1‖)^2 := by
          have he : (n:ℝ) * (1/(n:ℝ)) * ‖R‖ = ‖R‖ := by field_simp
          rw [he, ← hznorm]
          exact hR
        gcongr
    _ ≤ 1/(n:ℝ)^2 + ‖s - 1‖ / (n:ℝ)^2 := by
        refine add_le_add le_rfl ?_
        have h1 : (L * ‖s - 1‖)^2 / ‖s - 1‖ = L^2 * ‖s - 1‖ := by
          field_simp
        rw [h1]
        have h2 : L^2 ≤ (1/(n:ℝ))^2 := pow_le_pow_left₀ hL0 hLle 2
        calc L^2 * ‖s - 1‖ ≤ (1/(n:ℝ))^2 * ‖s - 1‖ :=
              mul_le_mul_of_nonneg_right h2 hs0.le
          _ = ‖s - 1‖ / (n:ℝ)^2 := by ring
    _ ≤ 2 * ‖s - 1‖ / (n:ℝ) ^ 2 := by
        have h1 : (1:ℝ)/(n:ℝ)^2 ≤ ‖s - 1‖/(n:ℝ)^2 := by gcongr
        have h2 : 2 * ‖s - 1‖ / (n:ℝ)^2 = ‖s - 1‖/(n:ℝ)^2 + ‖s - 1‖/(n:ℝ)^2 := by
          ring
        linarith
    _ = 2 * ‖s - 1‖ / ((n:ℕ):ℝ) ^ 2 := by norm_num

/-- Squared-reciprocal interval sums telescope to `2/N`. -/
theorem sum_inv_sq_Ico_le (N M : ℕ) (hN : 2 ≤ N) :
    ∑ n ∈ Finset.Ico N M, (1:ℝ) / (n:ℝ) ^ 2 ≤ 2 / N := by
  rcases le_or_gt M N with hMN | hMN
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    positivity
  · have hstep : ∀ n ∈ Finset.Ico N M, (1:ℝ)/(n:ℝ)^2
        ≤ (fun k : ℕ => 1/((k:ℝ) - 1)) n - (fun k : ℕ => 1/((k:ℝ) - 1)) (n + 1) := by
      intro n hn
      rw [Finset.mem_Ico] at hn
      have hn2 : 2 ≤ n := le_trans hN hn.1
      have hnr : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
      have he : (fun k : ℕ => 1/((k:ℝ) - 1)) n - (fun k : ℕ => 1/((k:ℝ) - 1)) (n + 1)
          = 1/(((n:ℝ) - 1) * n) := by
        show 1/((n:ℝ) - 1) - 1/(((n+1:ℕ):ℝ) - 1) = 1/(((n:ℝ) - 1) * n)
        push_cast
        rw [add_sub_cancel_right]
        rw [div_sub_div _ _ (by linarith) (by linarith)]
        congr 1
        ring
      rw [he, div_le_div_iff₀ (by positivity) (by nlinarith)]
      nlinarith
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [sum_Ico_sub_succ (fun k : ℕ => 1/((k:ℝ) - 1)) N M hMN.le]
    have hNr : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hMr : (2:ℝ) ≤ (M:ℝ) := by exact_mod_cast (by omega : 2 ≤ M)
    have h1 : (0:ℝ) ≤ 1/((M:ℝ) - 1) := by
      have : (0:ℝ) < (M:ℝ) - 1 := by linarith
      positivity
    have h2 : 1/((N:ℝ) - 1) ≤ 2/(N:ℝ) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      linarith
    show (fun k : ℕ => 1/((k:ℝ) - 1)) N - (fun k : ℕ => 1/((k:ℝ) - 1)) M ≤ 2 / N
    show 1/((N:ℝ) - 1) - 1/((M:ℝ) - 1) ≤ 2 / N
    linarith

/-- **The tail block bound**: beyond `2‖s-1‖`, every partial sum of
`n^{-s}` is uniformly bounded by `4`. -/
theorem norm_sum_cpow_Ico_le (s : ℂ) (N M : ℕ)
    (hσ1 : 1 ≤ s.re) (hs1 : 1 ≤ ‖s - 1‖) (hN : 2 * ‖s - 1‖ ≤ N) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-s)‖ ≤ 4 := by
  rcases le_or_gt M N with hMN | hMN
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, norm_zero]
    norm_num
  · have hs0 : (0:ℝ) < ‖s - 1‖ := by linarith
    have hN2 : 2 ≤ N := by
      have h1 : (2:ℝ) ≤ (N:ℝ) := le_trans (by linarith) hN
      exact_mod_cast h1
    have hsplit : ∀ n ∈ Finset.Ico N M, (n:ℂ)^(-s)
        = (zPot s n - zPot s (n+1))
          + ((n:ℂ)^(-s) - (zPot s n - zPot s (n+1))) := by
      intro n _
      ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    refine le_trans (norm_add_le _ _) ?_
    have hb : ∀ k : ℕ, 1 ≤ k → ‖zPot s k‖ ≤ 1 := by
      intro k hk
      rw [zPot, norm_div]
      have h1 : ‖((k:ℕ):ℂ) ^ ((1:ℂ) - s)‖ ≤ 1 := by
        rw [Complex.norm_natCast_cpow_of_pos (by omega)]
        have h2 : (((1:ℂ) - s).re) ≤ 0 := by
          simp only [Complex.sub_re, Complex.one_re]
          linarith
        calc ((k:ℝ)) ^ (((1:ℂ) - s).re) ≤ ((k:ℝ)) ^ (0:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hk) h2
          _ = 1 := Real.rpow_zero _
      rw [div_le_one hs0]
      exact le_trans h1 hs1
    have htel : ‖∑ n ∈ Finset.Ico N M, (zPot s n - zPot s (n+1))‖ ≤ 2 := by
      rw [sum_Ico_sub_succ (zPot s) N M hMN.le]
      refine le_trans (norm_sub_le _ _) ?_
      have hN1 : 1 ≤ N := by omega
      have hM1 : 1 ≤ M := by omega
      linarith [hb N hN1, hb M hM1]
    have herr : ‖∑ n ∈ Finset.Ico N M,
        ((n:ℂ)^(-s) - (zPot s n - zPot s (n+1)))‖ ≤ 2 := by
      refine le_trans (norm_sum_le _ _) ?_
      have hptw : ∀ n ∈ Finset.Ico N M,
          ‖(n:ℂ)^(-s) - (zPot s n - zPot s (n+1))‖
            ≤ 2*‖s-1‖ * ((1:ℝ)/(n:ℝ)^2) := by
        intro n hn
        rw [Finset.mem_Ico] at hn
        have h1 : ‖s - 1‖ ≤ (n:ℝ) := by
          calc ‖s-1‖ ≤ 2*‖s-1‖ := by linarith
            _ ≤ (N:ℝ) := hN
            _ ≤ (n:ℝ) := by exact_mod_cast hn.1
        refine le_trans (cpow_sub_telescope_le s n hσ1 hs1 h1) ?_
        rw [mul_one_div]
      refine le_trans (Finset.sum_le_sum hptw) ?_
      rw [← Finset.mul_sum]
      have hgeo := sum_inv_sq_Ico_le N M hN2
      have hN0 : (0:ℝ) < (N:ℝ) := by
        have : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN2
        linarith
      calc 2*‖s-1‖ * ∑ n ∈ Finset.Ico N M, (1:ℝ)/(n:ℝ)^2
          ≤ 2*‖s-1‖ * (2/(N:ℝ)) := by
            refine mul_le_mul_of_nonneg_left hgeo (by positivity)
        _ ≤ 2 := by
            rw [show 2*‖s-1‖ * (2/(N:ℝ)) = 4*‖s-1‖/(N:ℝ) by ring,
              div_le_iff₀ hN0]
            linarith
    linarith [htel, herr]

/-- **The zeta tail bound**: the L-series of `1` differs from its partial
sum below `N ≥ 2‖s-1‖` by at most `4`. -/
theorem norm_LSeries_one_sub_partial_le (s : ℂ) (N : ℕ)
    (hσ1 : 1 < s.re) (hs1 : 1 ≤ ‖s - 1‖) (hN : 2 * ‖s - 1‖ ≤ N)
    (hN1 : 1 ≤ N) :
    ‖LSeries (fun _ => 1) s - ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)‖ ≤ 4 := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hσ1
    norm_num at hσ1
  have htermeq : ∀ n : ℕ, n ≠ 0 →
      LSeries.term (fun _ => 1) s n = (n:ℂ)^(-s) := by
    intro n hn
    rw [LSeries.term_of_ne_zero hn, Complex.cpow_neg, one_div]
  have hsum : Summable (fun n => LSeries.term (fun _ => 1) s n) := by
    have h1 : Summable (fun n : ℕ => 1/(n:ℂ)^s) :=
      Complex.summable_one_div_nat_cpow.mpr hσ1
    refine h1.congr ?_
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_zero, Nat.cast_zero, Complex.zero_cpow hs0,
        div_zero]
    · rw [htermeq n hn, Complex.cpow_neg, one_div]
  have hrange : ∑ i ∈ Finset.range N, LSeries.term (fun _ => 1) s i
      = ∑ n ∈ Finset.Ico 1 N, (n:ℂ)^(-s) := by
    have h1 : Finset.range N = insert 0 (Finset.Ico 1 N) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [h1, Finset.sum_insert (by simp)]
    rw [LSeries.term_zero, zero_add]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Ico] at hn
    exact htermeq n (by omega)
  have htail : ‖∑' i, LSeries.term (fun _ => 1) s (i + N)‖ ≤ 4 := by
    have hsum2 : Summable (fun i => LSeries.term (fun _ => 1) s (i + N)) :=
      (summable_nat_add_iff N).mpr hsum
    have hlim := hsum2.hasSum.tendsto_sum_nat
    have hbound : ∀ m : ℕ,
        ‖∑ i ∈ Finset.range m, LSeries.term (fun _ => 1) s (i + N)‖ ≤ 4 := by
      intro m
      have he : ∑ i ∈ Finset.range m, LSeries.term (fun _ => 1) s (i + N)
          = ∑ n ∈ Finset.Ico N (N + m), (n:ℂ)^(-s) := by
        rw [Finset.sum_Ico_eq_sum_range]
        have h2 : N + m - N = m := by omega
        rw [h2]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show i + N = N + i by omega]
        exact htermeq (N + i) (by omega)
      rw [he]
      exact norm_sum_cpow_Ico_le s N (N+m) hσ1.le hs1 hN
    exact le_of_tendsto hlim.norm (Filter.Eventually.of_forall hbound)
  have hdecomp := hsum.sum_add_tsum_nat_add N
  have hL : LSeries (fun _ => 1) s
      = (∑ n ∈ Finset.Ico 1 N, (n:ℂ)^(-s))
        + ∑' i, LSeries.term (fun _ => 1) s (i + N) := by
    rw [LSeries, ← hdecomp, hrange]
  rw [hL, add_sub_cancel_left]
  exact htail

/-- **The phase identity**: complex powers of naturals split into the
rpow weight and the log-phase character. -/
theorem cpow_neg_eq_smul_e (σ t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ((n:ℕ):ℂ) ^ (-((σ:ℂ) - Complex.I * t))
      = ((n:ℝ) ^ (-σ) : ℝ) • e (t / (2 * Real.pi) * Real.log n) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hnne : ((n:ℕ):ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hπC : ((Real.pi : ℝ):ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  rw [Complex.cpow_def_of_ne_zero hnne,
    show ((n:ℕ):ℂ) = (((n:ℝ)):ℂ) from by push_cast; ring,
    ← Complex.ofReal_log hn0.le, Complex.real_smul,
    Real.rpow_def_of_pos hn0]
  simp only [e]
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/-- Norms of phase sums are conjugation-invariant: the sign of the phase
is immaterial. -/
theorem norm_sum_smul_e_neg (S : Finset ℕ) (w : ℕ → ℝ) (θ : ℕ → ℝ) :
    ‖∑ n ∈ S, w n • e (θ n)‖ = ‖∑ n ∈ S, w n • e (-(θ n))‖ := by
  calc ‖∑ n ∈ S, w n • e (θ n)‖
      = ‖(starRingEnd ℂ) (∑ n ∈ S, w n • e (θ n))‖ :=
        (RCLike.norm_conj _).symm
    _ = ‖∑ n ∈ S, w n • e (-(θ n))‖ := by
        rw [map_sum]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Complex.real_smul, map_mul, Complex.conj_ofReal, e_conj,
          Complex.real_smul]

/-- Pointwise: `‖n^{-s}‖ ≤ 1/n` on `σ ≥ 1`. -/
theorem norm_cpow_neg_le (σ t : ℝ) (n : ℕ) (hσ1 : 1 ≤ σ) (hn : 1 ≤ n) :
    ‖((n:ℕ):ℂ) ^ (-((σ:ℂ) - Complex.I * t))‖ ≤ 1/(n:ℝ) := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  have h1 : ((-((σ:ℂ) - Complex.I * t)).re) = -σ := by simp
  rw [h1]
  calc ((n:ℝ)) ^ (-σ) ≤ ((n:ℝ)) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
    _ = 1/(n:ℝ) := by rw [Real.rpow_neg_one, inv_eq_one_div]

/-- **The head in power form**: the schedule bound applies to `∑ n^{-s}`
over the head range, for either sign of `t`. -/
theorem norm_sum_cpow_head_le (σ t : ℝ) (d K : ℕ)
    (hσ1 : 1 < σ) (ht1 : (2:ℝ)^d ≤ |t|) (ht2 : |t| ≤ 2^(d+1)) :
    ‖∑ n ∈ Finset.Ico 1 (2^(d+1)),
        ((n:ℕ):ℂ) ^ (-((σ:ℂ) - Complex.I * t))‖
      ≤ (((d-2)/(K+2) + 2^(K+7) + 3 : ℕ) : ℝ) := by
  set w : ℕ → ℝ := fun n => (n:ℝ) ^ (-σ) with hwdef
  have hw0 : ∀ n : ℕ, 1 ≤ n → 0 ≤ w n := by
    intro n hn
    rw [hwdef]
    positivity
  have hwd : ∀ n : ℕ, 1 ≤ n → w (n + 1) ≤ w n := by
    intro n hn
    rw [hwdef]
    have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    simp only []
    have h1 : ((n:ℕ):ℝ) ^ σ ≤ (((n+1:ℕ)):ℝ) ^ σ := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
      push_cast
      linarith
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity),
      inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) h1
  have hwM : ∀ n : ℕ, 1 ≤ n → w n ≤ 1/(n:ℝ) := by
    intro n hn
    rw [hwdef]
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    simp only []
    calc (n:ℝ) ^ (-σ) ≤ (n:ℝ) ^ (-1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      _ = 1/(n:ℝ) := by rw [Real.rpow_neg_one, inv_eq_one_div]
  have hcongr : ∑ n ∈ Finset.Ico 1 (2^(d+1)),
      ((n:ℕ):ℂ) ^ (-((σ:ℂ) - Complex.I * t))
      = ∑ n ∈ Finset.Ico 1 (2^(d+1)),
          w n • e (t / (2 * Real.pi) * Real.log n) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Ico] at hn
    exact cpow_neg_eq_smul_e σ t n hn.1
  rw [hcongr]
  rcases le_or_gt t 0 with htneg | htpos
  · -- t ≤ 0: the phase is already `-(|t|/2π)·log n`
    have habs : |t| = -t := abs_of_nonpos htneg
    have hcongr2 : ∀ n ∈ Finset.Ico 1 (2^(d+1)),
        w n • e (t / (2 * Real.pi) * Real.log n)
        = w n • e (-(|t| / (2 * Real.pi) * Real.log n)) := by
      intro n _
      congr 1
      rw [habs]
      ring
    rw [Finset.sum_congr rfl hcongr2]
    exact zeta_head_bound d K |t| w ht1 ht2 hw0 hwd hwM
  · have habs : |t| = t := abs_of_pos htpos
    have hcongr2 : ∀ n ∈ Finset.Ico 1 (2^(d+1)),
        w n • e (t / (2 * Real.pi) * Real.log n)
        = w n • e (|t| / (2 * Real.pi) * Real.log n) := by
      intro n _
      rw [habs]
    rw [Finset.sum_congr rfl hcongr2,
      norm_sum_smul_e_neg _ w (fun n => |t| / (2 * Real.pi) * Real.log n)]
    exact zeta_head_bound d K |t| w ht1 ht2 hw0 hwd hwM

/-- The middle strip is crudely bounded by its length times the weight. -/
theorem norm_sum_cpow_middle_le (σ t : ℝ) (d : ℕ) (hσ1 : 1 ≤ σ) :
    ‖∑ n ∈ Finset.Ico (2^(d+1)) (2^(d+3)),
        ((n:ℕ):ℂ) ^ (-((σ:ℂ) - Complex.I * t))‖ ≤ 3 := by
  refine le_trans (norm_sum_le _ _) ?_
  have hptw : ∀ n ∈ Finset.Ico (2^(d+1) : ℕ) (2^(d+3)),
      ‖((n:ℕ):ℂ) ^ (-((σ:ℂ) - Complex.I * t))‖ ≤ 1/((2:ℝ)^(d+1)) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn1 : 1 ≤ n := le_trans Nat.one_le_two_pow hn.1
    refine le_trans (norm_cpow_neg_le σ t n hσ1 hn1) ?_
    have h1 : ((2:ℝ))^(d+1) ≤ (n:ℝ) := by
      have h2 : ((2^(d+1) : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast hn.1
      push_cast at h2
      exact h2
    exact one_div_le_one_div_of_le (by positivity) h1
  refine le_trans (Finset.sum_le_sum hptw) ?_
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have h1 : ((2^(d+3) - 2^(d+1) : ℕ) : ℝ) = 3 * 2^(d+1) := by
    rw [Nat.cast_sub (Nat.pow_le_pow_right (by norm_num) (by omega))]
    push_cast
    ring
  rw [h1]
  rw [mul_one_div]
  rw [div_le_iff₀ (by positivity)]

set_option maxHeartbeats 1600000 in
/-- **The Littlewood-strength zeta bound**, fully elementary: just right
of the `1`-line, the zeta L-series is `O(log|t|/log log|t|)` with the
explicit constant `8192`. -/
theorem zeta_LSeries_bound (σ t : ℝ) (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (ht : 1 ≤ |t|) :
    ‖LSeries (fun _ => 1) ((σ:ℂ) - Complex.I * t)‖
      ≤ 8192 * Real.log (|t| + 2) / Real.log (Real.log (|t| + 2)) := by
  set s : ℂ := (σ:ℂ) - Complex.I * t with hsdef
  have hsre : s.re = σ := by
    rw [hsdef]
    simp
  have hsim : (s - 1).im = -t := by
    rw [hsdef]
    simp
  have hnorm_ge : |t| ≤ ‖s - 1‖ := by
    calc |t| = |(s-1).im| := by rw [hsim, abs_neg]
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
  have hs1 : 1 ≤ ‖s - 1‖ := le_trans ht hnorm_ge
  have hnorm_le : ‖s - 1‖ ≤ σ - 1 + |t| := by
    have h1 : s - 1 = ((σ - 1 : ℝ):ℂ) - Complex.I * t := by
      rw [hsdef]
      push_cast
      ring
    rw [h1]
    refine le_trans (norm_sub_le _ _) ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  -- the dyadic scale
  set m : ℕ := ⌊|t|⌋₊ with hmdef
  have hm1 : 1 ≤ m := by
    rw [hmdef]
    exact Nat.le_floor (by exact_mod_cast ht)
  set d : ℕ := Nat.log 2 m with hddef
  have hd1 : (2:ℝ)^d ≤ |t| := by
    have h1 : (2:ℕ)^d ≤ m := by
      rw [hddef]
      exact Nat.pow_log_le_self 2 (by omega)
    have h2 : ((2^d : ℕ):ℝ) ≤ (m:ℝ) := by exact_mod_cast h1
    have h3 : (m:ℝ) ≤ |t| := by
      rw [hmdef]
      exact Nat.floor_le (by positivity)
    push_cast at h2
    linarith
  have hd2 : |t| ≤ (2:ℝ)^(d+1) := by
    have h1 : m < 2^(d+1) := by
      rw [hddef]
      exact Nat.lt_pow_succ_log_self (by norm_num) m
    have h2 : |t| < (m:ℝ) + 1 := by
      rw [hmdef]
      exact Nat.lt_floor_add_one _
    have h3 : ((m:ℕ):ℝ) + 1 ≤ ((2^(d+1) : ℕ):ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith
  set K : ℕ := Nat.log 2 (d + 2) / 2 with hKdef
  have h2pow : (1:ℝ) ≤ (2:ℝ)^(d+1) := one_le_pow₀ (by norm_num)
  -- tail remainder at 2^{d+3}
  have hNs : 2 * ‖s - 1‖ ≤ ((2^(d+3) : ℕ):ℝ) := by
    push_cast
    have h1 : ‖s-1‖ ≤ 1 + 2^(d+1) := by linarith
    have h2 : ((2:ℝ))^(d+3) = 4 * 2^(d+1) := by ring
    linarith
  have htail := norm_LSeries_one_sub_partial_le s (2^(d+3))
    (by rw [hsre]; exact hσ1) hs1 hNs Nat.one_le_two_pow
  have hsplit : ∑ n ∈ Finset.Ico (1:ℕ) (2^(d+3)), (n:ℂ)^(-s)
      = (∑ n ∈ Finset.Ico (1:ℕ) (2^(d+1)), (n:ℂ)^(-s))
        + ∑ n ∈ Finset.Ico ((2:ℕ)^(d+1)) (2^(d+3)), (n:ℂ)^(-s) :=
    (Finset.sum_Ico_consecutive _ Nat.one_le_two_pow
      (Nat.pow_le_pow_right (by norm_num) (by omega))).symm
  have hhead : ‖∑ n ∈ Finset.Ico (1:ℕ) (2^(d+1)), (n:ℂ)^(-s)‖
      ≤ (((d-2)/(K+2) + 2^(K+7) + 3 : ℕ) : ℝ) :=
    norm_sum_cpow_head_le σ t d K hσ1 hd1 hd2
  have hmid : ‖∑ n ∈ Finset.Ico ((2:ℕ)^(d+1)) (2^(d+3)), (n:ℂ)^(-s)‖ ≤ 3 :=
    norm_sum_cpow_middle_le σ t d hσ1.le
  have hassemble : ‖LSeries (fun _ => 1) s‖
      ≤ (((d-2)/(K+2) + 2^(K+7) + 3 : ℕ) : ℝ) + 7 := by
    have h1 : LSeries (fun _ => 1) s
        = ((LSeries (fun _ => 1) s
            - ∑ n ∈ Finset.Ico (1:ℕ) (2^(d+3)), (n:ℂ)^(-s))
          + ∑ n ∈ Finset.Ico (1:ℕ) (2^(d+1)), (n:ℂ)^(-s))
          + ∑ n ∈ Finset.Ico ((2:ℕ)^(d+1)) (2^(d+3)), (n:ℂ)^(-s) := by
      rw [hsplit]
      ring
    rw [h1]
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
    linarith [htail, hhead, hmid]
  -- ℕ-arithmetic for the schedule scale
  have hK2 : ((2:ℕ)^K)^2 ≤ d + 2 := by
    calc ((2:ℕ)^K)^2 = 2^(2*K) := by rw [← pow_mul, mul_comm]
      _ ≤ 2^(Nat.log 2 (d+2)) :=
          Nat.pow_le_pow_right (by norm_num) (by rw [hKdef]; omega)
      _ ≤ d + 2 := Nat.pow_log_le_self 2 (by omega)
  have hdlt : d + 2 < 2^(d+2) := by
    have h1 := two_succ_le_two_pow d
    have h2 : (2:ℕ)^(d+2) = 4 * 2^d := by ring
    have h3 : 1 ≤ (2:ℕ)^d := Nat.one_le_two_pow
    omega
  have hKd : K + 2 ≤ d + 2 := by
    have h1 : Nat.log 2 (d+2) < d + 2 := Nat.log_lt_of_lt_pow (by omega) hdlt
    rw [hKdef]
    omega
  have hK4 : (K:ℝ) + 2 ≤ 4 * (2:ℝ)^K := by
    have h1 := two_succ_le_two_pow K
    have h2 : ((2*K+2 : ℕ):ℝ) ≤ ((2^(K+2) : ℕ):ℝ) := by exact_mod_cast h1
    push_cast at h2
    have h3 : ((2:ℝ))^(K+2) = 4 * 2^K := by ring
    linarith
  have h2K0 : (0:ℝ) < (2:ℝ)^K := by positivity
  have hK2R : ((2:ℝ)^K)^2 ≤ (d:ℝ) + 2 := by
    have h1 : (((2^K)^2 : ℕ):ℝ) ≤ ((d + 2 : ℕ):ℝ) := by exact_mod_cast hK2
    push_cast at h1
    linarith
  have h2Kle : (2:ℝ)^K ≤ ((d:ℝ)+2) / (2:ℝ)^K := by
    rw [le_div_iff₀ h2K0]
    nlinarith
  have h2Kle2 : ((d:ℝ)+2) / (2:ℝ)^K ≤ 4 * ((d:ℝ)+2) / ((K:ℝ)+2) := by
    rw [div_le_div_iff₀ h2K0 (by positivity)]
    have hd0 : (0:ℝ) ≤ (d:ℝ) + 2 := by positivity
    nlinarith
  -- cast the head count
  have hcount : (((d-2)/(K+2) + 2^(K+7) + 3 : ℕ) : ℝ) + 7
      ≤ 523 * ((d:ℝ)+2) / ((K:ℝ)+2) := by
    push_cast
    have h1 : (((d-2)/(K+2) : ℕ) : ℝ) ≤ ((d:ℝ)+2) / ((K:ℝ)+2) := by
      have h1a : ((d-2)/(K+2) : ℕ) ≤ (d/(K+2) : ℕ) :=
        Nat.div_le_div_right (by omega)
      have h1b : (((d/(K+2) : ℕ)) : ℝ) ≤ (d:ℝ)/((K:ℝ)+2) := by
        refine le_trans Nat.cast_div_le ?_
        push_cast
        exact le_rfl
      have h1c : (d:ℝ)/((K:ℝ)+2) ≤ ((d:ℝ)+2)/((K:ℝ)+2) := by
        gcongr
        linarith
      calc (((d-2)/(K+2) : ℕ) : ℝ)
          ≤ (((d/(K+2) : ℕ)) : ℝ) := by exact_mod_cast h1a
        _ ≤ (d:ℝ)/((K:ℝ)+2) := h1b
        _ ≤ ((d:ℝ)+2)/((K:ℝ)+2) := h1c
    have h2 : ((2:ℝ))^(K+7) = 128 * (2:ℝ)^K := by ring
    have h3 : ((2:ℝ))^K ≤ 4 * ((d:ℝ)+2) / ((K:ℝ)+2) :=
      le_trans h2Kle h2Kle2
    have h4 : (10:ℝ) ≤ 10 * (((d:ℝ)+2) / ((K:ℝ)+2)) := by
      have h5 : (1:ℝ) ≤ ((d:ℝ)+2) / ((K:ℝ)+2) := by
        rw [le_div_iff₀ (by positivity)]
        have h6 : ((K+2:ℕ):ℝ) ≤ ((d+2:ℕ):ℝ) := by exact_mod_cast hKd
        push_cast at h6
        linarith
      linarith
    calc (((d-2)/(K+2) : ℕ) : ℝ) + (2:ℝ)^(K+7) + 3 + 7
        ≤ ((d:ℝ)+2)/((K:ℝ)+2) + 128 * (4 * ((d:ℝ)+2) / ((K:ℝ)+2))
          + 10 * (((d:ℝ)+2) / ((K:ℝ)+2)) := by
          rw [h2]
          have h8 : 128 * (2:ℝ)^K ≤ 128 * (4 * ((d:ℝ)+2) / ((K:ℝ)+2)) := by
            linarith
          linarith
      _ = 523 * ((d:ℝ)+2) / ((K:ℝ)+2) := by ring
  -- the log conversions
  have hlog3 : (1:ℝ) < Real.log (|t| + 2) := by
    rw [show (1:ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    refine Real.log_lt_log (Real.exp_pos 1) ?_
    linarith [Real.exp_one_lt_d9]
  have hlogpos : (0:ℝ) < Real.log (|t| + 2) := by linarith
  have hll_pos : (0:ℝ) < Real.log (Real.log (|t| + 2)) := Real.log_pos hlog3
  have hlog2fact : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hdlog : (d:ℝ) + 2 ≤ 4 * Real.log (|t| + 2) := by
    have h2 := Real.log_le_log (by positivity : (0:ℝ) < 2^d) hd1
    rw [Real.log_pow] at h2
    have h3 : Real.log |t| ≤ Real.log (|t| + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    have h4 : (d:ℝ) * Real.log 2 ≤ Real.log (|t|+2) := by linarith
    have h5 : (d:ℝ) ≤ 2 * Real.log (|t|+2) := by
      nlinarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
    linarith
  have hKlog : Real.log (Real.log (|t| + 2)) ≤ 2 * ((K:ℝ) + 2) := by
    have h2a : (2:ℝ) ≤ (2:ℝ)^(d+1) := by
      calc (2:ℝ) = 2^1 := (pow_one 2).symm
        _ ≤ 2^(d+1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h1 : Real.log (|t| + 2) ≤ (d:ℝ) + 2 := by
      have h2 : |t| + 2 ≤ (2:ℝ)^(d+2) := by
        have h3 : ((2:ℝ))^(d+2) = 2 * 2^(d+1) := by ring
        linarith
      have h4 : Real.log (|t|+2) ≤ Real.log ((2:ℝ)^(d+2)) :=
        Real.log_le_log (by positivity) h2
      rw [Real.log_pow] at h4
      have h5 : ((d:ℝ)+2) * Real.log 2 ≤ ((d:ℝ)+2) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith [Real.log_two_lt_d9]
      push_cast at h4
      linarith
    have h6 : Real.log (Real.log (|t| + 2)) ≤ Real.log ((d:ℝ) + 2) :=
      Real.log_le_log hlogpos h1
    have h7 : (d:ℝ) + 2 < ((2:ℝ))^(Nat.log 2 (d+2) + 1) := by
      have h8 := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) (d+2)
      have h9 : ((d+2 : ℕ):ℝ) < ((2^(Nat.log 2 (d+2)+1) : ℕ):ℝ) := by
        exact_mod_cast h8
      push_cast at h9
      linarith
    have h10 : Real.log ((d:ℝ)+2)
        ≤ (↑(Nat.log 2 (d+2)) + 1) * Real.log 2 := by
      have h11 : Real.log ((d:ℝ)+2) ≤ Real.log ((2:ℝ)^(Nat.log 2 (d+2)+1)) :=
        Real.log_le_log (by positivity) h7.le
      rw [Real.log_pow] at h11
      push_cast at h11
      linarith
    have h12 : (↑(Nat.log 2 (d+2)) : ℝ) ≤ 2*(K:ℝ) + 1 := by
      have h13 : Nat.log 2 (d+2) ≤ 2*K + 1 := by
        rw [hKdef]
        omega
      exact_mod_cast h13
    have h14 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have h16 : Real.log ((d:ℝ)+2) ≤ 2*(K:ℝ) + 2 := by
      calc Real.log ((d:ℝ)+2) ≤ (↑(Nat.log 2 (d+2)) + 1) * Real.log 2 := h10
        _ ≤ (2*(K:ℝ) + 2) * 1 := by
            refine mul_le_mul (by linarith) h14
              (Real.log_nonneg (by norm_num)) (by positivity)
        _ = 2*(K:ℝ) + 2 := by ring
    linarith
  have hfinal : 523 * ((d:ℝ)+2) / ((K:ℝ)+2)
      ≤ 8192 * Real.log (|t| + 2) / Real.log (Real.log (|t| + 2)) := by
    have hK20 : (0:ℝ) < (K:ℝ) + 2 := by positivity
    have h1 : 523 * ((d:ℝ)+2) / ((K:ℝ)+2)
        ≤ 523 * (4 * Real.log (|t|+2)) / ((K:ℝ)+2) := by
      gcongr
    have h2 : Real.log (Real.log (|t| + 2)) / 2 ≤ (K:ℝ) + 2 := by linarith
    have h3 : 523 * (4 * Real.log (|t|+2)) / ((K:ℝ)+2)
        ≤ 523 * (4 * Real.log (|t|+2))
          / (Real.log (Real.log (|t| + 2)) / 2) := by
      gcongr
    have h4 : 523 * (4 * Real.log (|t|+2))
          / (Real.log (Real.log (|t| + 2)) / 2)
        = 4184 * Real.log (|t|+2) / Real.log (Real.log (|t| + 2)) := by
      field_simp
      norm_num
    have h5 : 4184 * Real.log (|t|+2) / Real.log (Real.log (|t| + 2))
        ≤ 8192 * Real.log (|t|+2) / Real.log (Real.log (|t| + 2)) := by
      gcongr
      linarith
    calc 523 * ((d:ℝ)+2) / ((K:ℝ)+2)
        ≤ 523 * (4 * Real.log (|t|+2)) / ((K:ℝ)+2) := h1
      _ ≤ 523 * (4 * Real.log (|t|+2))
          / (Real.log (Real.log (|t| + 2)) / 2) := h3
      _ = 4184 * Real.log (|t|+2) / Real.log (Real.log (|t| + 2)) := h4
      _ ≤ 8192 * Real.log (|t|+2) / Real.log (Real.log (|t| + 2)) := h5
  calc ‖LSeries (fun _ => 1) s‖
      ≤ (((d-2)/(K+2) + 2^(K+7) + 3 : ℕ) : ℝ) + 7 := hassemble
    _ ≤ 523 * ((d:ℝ)+2) / ((K:ℝ)+2) := hcount
    _ ≤ 8192 * Real.log (|t| + 2) / Real.log (Real.log (|t| + 2)) := hfinal

end ExpSums

end MoltResearch
