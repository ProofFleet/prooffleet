import MoltResearch.Discrepancy.LogDifferences
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.LocallyUniformLimit
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

/-! ### The strip (`0 ≤ σ ≤ 1`): head and middle with the trivial-size rescaling

The schedule bound extends left of the 1-line by pulling out the trivial size
`(2^{d+1})^{1-σ}` of the head range: the capped weight
`min (n^{-σ}/C) (1/n)` satisfies the `zeta_head_bound` hypotheses globally and
agrees with `n^{-σ}/C` on the head range.  Substrate for the Track R zero-free
region (issue #3044, phase P). -/

/-- **The head in the strip** (`0 ≤ σ ≤ 1`): the schedule bound applies after
rescaling by the trivial size `(2^{d+1})^{1-σ}` of the head range. -/
theorem norm_sum_cpow_head_le_strip (σ t : ℝ) (d K : ℕ)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (ht1 : (2:ℝ)^d ≤ |t|) (ht2 : |t| ≤ 2^(d+1)) :
    ‖∑ n ∈ Finset.Ico 1 (2^(d+1)),
        ((n:ℕ):ℂ) ^ (-((σ:ℂ) - Complex.I * t))‖
      ≤ ((2:ℝ)^(d+1)) ^ (1-σ) * (((d-2)/(K+2) + 2^(K+7) + 3 : ℕ) : ℝ) := by
  set C : ℝ := ((2:ℝ)^(d+1)) ^ (1-σ) with hC_def
  have hC0 : (0:ℝ) < C := by
    rw [hC_def]
    positivity
  set w : ℕ → ℝ := fun n => min ((n:ℝ) ^ (-σ) / C) (1/(n:ℝ)) with hwdef
  have hw0 : ∀ n : ℕ, 1 ≤ n → 0 ≤ w n := by
    intro n hn
    rw [hwdef]
    exact le_min (by positivity) (by positivity)
  have hwd : ∀ n : ℕ, 1 ≤ n → w (n + 1) ≤ w n := by
    intro n hn
    have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    rw [hwdef]
    simp only []
    refine min_le_min ?_ ?_
    · have h1 : ((n:ℕ):ℝ) ^ σ ≤ (((n+1:ℕ)):ℝ) ^ σ := by
        refine Real.rpow_le_rpow (by positivity) ?_ hσ0
        push_cast
        linarith
      have h2 : (((n+1:ℕ)):ℝ) ^ (-σ) ≤ ((n:ℕ):ℝ) ^ (-σ) := by
        rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity),
          inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le (by positivity) h1
      exact div_le_div_of_nonneg_right (by exact_mod_cast h2) hC0.le
    · refine one_div_le_one_div_of_le (by positivity) ?_
      push_cast
      linarith
  have hwM : ∀ n : ℕ, 1 ≤ n → w n ≤ 1/(n:ℝ) := by
    intro n _
    rw [hwdef]
    exact min_le_right _ _
  -- on the head range the cap is inactive and the weight is `n^{-σ}/C`
  have hcap : ∀ n ∈ Finset.Ico 1 (2^(d+1) : ℕ), (n:ℝ) ^ (-σ) = C * w n := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn.1
    have hle : (n:ℝ) ^ (-σ) / C ≤ 1/(n:ℝ) := by
      rw [div_le_div_iff₀ hC0 hn0]
      have h1 : (n:ℝ) ^ (-σ) * (n:ℝ) = (n:ℝ) ^ (1-σ) := by
        rw [show (n:ℝ) ^ (-σ) * (n:ℝ) = (n:ℝ) ^ (-σ) * (n:ℝ) ^ (1:ℝ) from by
            rw [Real.rpow_one],
          ← Real.rpow_add hn0, neg_add_eq_sub]
      have h2 : (n:ℝ) ^ (1-σ) ≤ ((2:ℝ)^(d+1)) ^ (1-σ) := by
        refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
        calc (n:ℝ) ≤ ((2^(d+1) : ℕ):ℝ) := by exact_mod_cast hn.2.le
          _ = (2:ℝ)^(d+1) := by push_cast; ring
      rw [hC_def]
      linarith [h1, h2]
    rw [hwdef]
    simp only []
    rw [min_eq_left hle, mul_comm, div_mul_cancel₀ _ (ne_of_gt hC0)]
  have hcongr : ∑ n ∈ Finset.Ico 1 (2^(d+1)),
      ((n:ℕ):ℂ) ^ (-((σ:ℂ) - Complex.I * t))
      = C • ∑ n ∈ Finset.Ico 1 (2^(d+1)),
          w n • e (t / (2 * Real.pi) * Real.log n) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Ico.mp hn).1
    rw [cpow_neg_eq_smul_e σ t n hn1, hcap n hn]
    exact (smul_smul C (w n) _).symm
  rw [hcongr, norm_smul, Real.norm_eq_abs, abs_of_pos hC0]
  refine mul_le_mul_of_nonneg_left ?_ hC0.le
  rcases le_or_gt t 0 with htneg | htpos
  · have habs : |t| = -t := abs_of_nonpos htneg
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

/-- **The middle strip in the strip**: crude bound by length times the largest
weight, picking up the same trivial-size factor. -/
theorem norm_sum_cpow_middle_le_strip (σ t : ℝ) (d : ℕ) (hσ0 : 0 ≤ σ) :
    ‖∑ n ∈ Finset.Ico (2^(d+1)) (2^(d+3)),
        ((n:ℕ):ℂ) ^ (-((σ:ℂ) - Complex.I * t))‖
      ≤ 3 * ((2:ℝ)^(d+1)) ^ (1-σ) := by
  refine le_trans (norm_sum_le _ _) ?_
  have hptw : ∀ n ∈ Finset.Ico (2^(d+1) : ℕ) (2^(d+3)),
      ‖((n:ℕ):ℂ) ^ (-((σ:ℂ) - Complex.I * t))‖ ≤ ((2:ℝ)^(d+1)) ^ (-σ) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn1 : (1:ℕ) ≤ n := le_trans Nat.one_le_two_pow hn.1
    have hbase : (2:ℝ)^(d+1) ≤ (n:ℝ) := by
      have h2 : ((2^(d+1) : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast hn.1
      push_cast at h2
      exact h2
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    have hre : ((-((σ:ℂ) - Complex.I * t)).re) = -σ := by simp
    rw [hre]
    have h1 : ((2:ℝ)^(d+1)) ^ σ ≤ (n:ℝ) ^ σ :=
      Real.rpow_le_rpow (by positivity) hbase hσ0
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity),
      inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) h1
  refine le_trans (Finset.sum_le_sum hptw) ?_
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have h1 : ((2^(d+3) - 2^(d+1) : ℕ) : ℝ) = 3 * 2^(d+1) := by
    rw [Nat.cast_sub (Nat.pow_le_pow_right (by norm_num) (by omega))]
    push_cast
    ring
  rw [h1]
  have h2 : (2:ℝ)^(d+1) * ((2:ℝ)^(d+1)) ^ (-σ) = ((2:ℝ)^(d+1)) ^ (1-σ) := by
    rw [show (2:ℝ)^(d+1) * ((2:ℝ)^(d+1)) ^ (-σ)
        = ((2:ℝ)^(d+1)) ^ (1:ℝ) * ((2:ℝ)^(d+1)) ^ (-σ) from by
        rw [Real.rpow_one],
      ← Real.rpow_add (by positivity), ← sub_eq_add_neg]
  rw [mul_assoc, h2]

/-- **The per-term telescope error in the strip**: for `0 < s.re` and
`max 1 ‖s-1‖ ≤ n`, the term `n^{-s}` matches the potential difference up to
`2‖s-1‖/n^{1+re s}`.  Generalizes `cpow_sub_telescope_le` (which required
`1 ≤ s.re`); the only change is the pointwise size `‖n^{-s}‖ = n^{-re s}`. -/
theorem cpow_sub_telescope_le_strip (s : ℂ) (n : ℕ)
    (hσ0 : 0 < s.re) (hs1 : 1 ≤ ‖s - 1‖) (hn : ‖s - 1‖ ≤ n) (hn1 : 1 ≤ n) :
    ‖(n : ℂ) ^ (-s) - (zPot s n - zPot s (n + 1))‖
      ≤ 2 * ‖s - 1‖ / (n:ℝ) ^ (1 + s.re) := by
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
  have hnormpow : ‖((n:ℕ):ℂ) ^ (-s)‖ = (n:ℝ) ^ (-(s.re)) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    congr 1
  have habs : ‖(((1 - (n:ℝ) * L : ℝ)):ℂ)‖ ≤ 1/(n:ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith, by linarith⟩
  have hsplitpow : (n:ℝ) ^ (-(s.re)) * (1/(n:ℝ)) = (n:ℝ) ^ (-(1 + s.re)) := by
    rw [show (1:ℝ)/(n:ℝ) = (n:ℝ) ^ (-(1:ℝ)) from by
        rw [Real.rpow_neg_one, inv_eq_one_div],
      ← Real.rpow_add hn0]
    congr 1
    ring
  calc ‖((n:ℕ):ℂ) ^ (-s) * (((1 - (n:ℝ) * L : ℝ)):ℂ)
        + ((n:ℕ):ℂ) * ((n:ℕ):ℂ) ^ (-s) * R / (s - 1)‖
      ≤ ‖((n:ℕ):ℂ) ^ (-s) * (((1 - (n:ℝ) * L : ℝ)):ℂ)‖
        + ‖((n:ℕ):ℂ) * ((n:ℕ):ℂ) ^ (-s) * R / (s - 1)‖ := norm_add_le _ _
    _ ≤ (n:ℝ) ^ (-(s.re)) * (1/(n:ℝ))
        + ((n:ℝ) * (n:ℝ) ^ (-(s.re)) * ‖R‖) / ‖s - 1‖ := by
        refine add_le_add ?_ ?_
        · rw [norm_mul, hnormpow]
          exact mul_le_mul_of_nonneg_left habs (by positivity)
        · rw [norm_div, norm_mul, norm_mul, Complex.norm_natCast, hnormpow]
    _ ≤ (n:ℝ) ^ (-(1 + s.re)) + ‖s - 1‖ * (n:ℝ) ^ (-(1 + s.re)) := by
        refine add_le_add (le_of_eq hsplitpow) ?_
        have hRb : ‖R‖ ≤ (L * ‖s - 1‖) ^ 2 := by
          rw [← hznorm]
          exact hR
        have hL2 : (L * ‖s - 1‖) ^ 2 ≤ (1/(n:ℝ)) ^ 2 * ‖s - 1‖ ^ 2 := by
          have h1 : L ^ 2 ≤ (1/(n:ℝ)) ^ 2 := pow_le_pow_left₀ hL0 hLle 2
          calc (L * ‖s - 1‖) ^ 2 = L ^ 2 * ‖s - 1‖ ^ 2 := by ring
            _ ≤ (1/(n:ℝ)) ^ 2 * ‖s - 1‖ ^ 2 :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
        calc ((n:ℝ) * (n:ℝ) ^ (-(s.re)) * ‖R‖) / ‖s - 1‖
            ≤ ((n:ℝ) * (n:ℝ) ^ (-(s.re)) * ((1/(n:ℝ)) ^ 2 * ‖s - 1‖ ^ 2)) / ‖s - 1‖ := by
              gcongr
              exact le_trans hRb hL2
          _ = ‖s - 1‖ * ((n:ℝ) ^ (-(s.re)) * (1/(n:ℝ))) := by
              field_simp
          _ = ‖s - 1‖ * (n:ℝ) ^ (-(1 + s.re)) := by rw [hsplitpow]
    _ ≤ 2 * ‖s - 1‖ / (n:ℝ) ^ (1 + s.re) := by
        have h1 : (n:ℝ) ^ (-(1 + s.re)) = 1 / (n:ℝ) ^ (1 + s.re) := by
          rw [Real.rpow_neg hn0.le, inv_eq_one_div]
        rw [h1]
        have h3 : 1 / (n:ℝ) ^ (1 + s.re) + ‖s - 1‖ * (1 / (n:ℝ) ^ (1 + s.re))
            = (1 + ‖s - 1‖) / (n:ℝ) ^ (1 + s.re) := by ring
        rw [h3]
        gcongr
        linarith

/-- **The strip tail sum**: `∑_{N ≤ n < M} n^{-1-σ} ≤ (N-1)^{-σ}/σ`, by
telescoping against `k ↦ (k-1)^{-σ}` — the Bernoulli step
`(1-1/n)^{-σ} ≥ 1 + σ/n` comes from `exp x ≥ 1 + x` and
`log(1-1/n) ≤ -1/n`, keeping the file integration-free. -/
theorem sum_rpow_neg_Ico_le (σ : ℝ) (N M : ℕ) (hσ0 : 0 < σ) (hN : 2 ≤ N) :
    ∑ n ∈ Finset.Ico N M, (n:ℝ) ^ (-(1+σ)) ≤ ((N:ℝ)-1) ^ (-σ) / σ := by
  rcases le_or_gt M N with hMN | hMN
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    have hN1 : (0:ℝ) ≤ (N:ℝ) - 1 := by
      have : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
      linarith
    exact div_nonneg (Real.rpow_nonneg hN1 _) hσ0.le
  · have hstep : ∀ n ∈ Finset.Ico N M, (n:ℝ) ^ (-(1+σ))
        ≤ ((fun k : ℕ => ((k:ℝ)-1) ^ (-σ) / σ) n
            - (fun k : ℕ => ((k:ℝ)-1) ^ (-σ) / σ) (n + 1)) := by
      intro n hn
      rw [Finset.mem_Ico] at hn
      have hn2 : 2 ≤ n := le_trans hN hn.1
      have hnr : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
      have hn0 : (0:ℝ) < (n:ℝ) := by linarith
      have hn10 : (0:ℝ) < (n:ℝ) - 1 := by linarith
      simp only []
      -- `(n-1)^{-σ} = n^{-σ}·(1-1/n)^{-σ}` and the Bernoulli lower bound
      have hfrac0 : (0:ℝ) < 1 - 1/(n:ℝ) := by
        have : 1/(n:ℝ) ≤ 1/2 := by
          rw [div_le_div_iff₀ hn0 (by norm_num)]
          linarith
        linarith
      have hsplit : ((n:ℝ)-1) ^ (-σ) = (n:ℝ) ^ (-σ) * (1 - 1/(n:ℝ)) ^ (-σ) := by
        rw [show (n:ℝ) - 1 = (n:ℝ) * (1 - 1/(n:ℝ)) from by field_simp,
          Real.mul_rpow hn0.le hfrac0.le]
      have hlog : Real.log (1 - 1/(n:ℝ)) ≤ -(1/(n:ℝ)) := by
        have h1 := Real.log_le_sub_one_of_pos hfrac0
        linarith
      have hbern : 1 + σ/(n:ℝ) ≤ (1 - 1/(n:ℝ)) ^ (-σ) := by
        rw [Real.rpow_def_of_pos hfrac0]
        calc 1 + σ/(n:ℝ) ≤ 1 + (-σ) * Real.log (1 - 1/(n:ℝ)) := by
              have h2 : σ * (1/(n:ℝ)) ≤ (-σ) * Real.log (1 - 1/(n:ℝ)) := by
                have h3 : (-σ) * Real.log (1 - 1/(n:ℝ)) = σ * (-(Real.log (1 - 1/(n:ℝ)))) := by
                  ring
                rw [h3]
                refine mul_le_mul_of_nonneg_left ?_ hσ0.le
                linarith
              have h4 : σ/(n:ℝ) = σ * (1/(n:ℝ)) := by ring
              linarith [h4.le, h4.ge, h2]
          _ ≤ Real.exp ((-σ) * Real.log (1 - 1/(n:ℝ))) := by
              have := Real.add_one_le_exp ((-σ) * Real.log (1 - 1/(n:ℝ)))
              linarith
          _ = Real.exp (Real.log (1 - 1/(n:ℝ)) * (-σ)) := by ring_nf
      have hdiff : σ * (n:ℝ) ^ (-(1+σ)) ≤ ((n:ℝ)-1) ^ (-σ) - (n:ℝ) ^ (-σ) := by
        have h1 : ((n:ℝ)-1) ^ (-σ) - (n:ℝ) ^ (-σ)
            = (n:ℝ) ^ (-σ) * ((1 - 1/(n:ℝ)) ^ (-σ) - 1) := by
          rw [hsplit]
          ring
        have h2 : σ/(n:ℝ) ≤ (1 - 1/(n:ℝ)) ^ (-σ) - 1 := by linarith [hbern]
        have h3 : (n:ℝ) ^ (-σ) * (σ/(n:ℝ)) = σ * (n:ℝ) ^ (-(1+σ)) := by
          rw [show (n:ℝ) ^ (-(1+σ)) = (n:ℝ) ^ (-σ) * (n:ℝ) ^ (-(1:ℝ)) from by
              rw [← Real.rpow_add hn0]
              congr 1
              ring,
            Real.rpow_neg_one]
          field_simp
        rw [h1]
        calc σ * (n:ℝ) ^ (-(1+σ)) = (n:ℝ) ^ (-σ) * (σ/(n:ℝ)) := h3.symm
          _ ≤ (n:ℝ) ^ (-σ) * ((1 - 1/(n:ℝ)) ^ (-σ) - 1) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
      have hcast : ((n + 1 : ℕ):ℝ) - 1 = (n:ℝ) := by push_cast; ring
      rw [hcast, div_sub_div_same, le_div_iff₀ hσ0]
      calc (n:ℝ) ^ (-(1+σ)) * σ = σ * (n:ℝ) ^ (-(1+σ)) := by ring
        _ ≤ ((n:ℝ)-1) ^ (-σ) - (n:ℝ) ^ (-σ) := hdiff
    calc ∑ n ∈ Finset.Ico N M, (n:ℝ) ^ (-(1+σ))
        ≤ ∑ n ∈ Finset.Ico N M,
            ((fun k : ℕ => ((k:ℝ)-1) ^ (-σ) / σ) n
              - (fun k : ℕ => ((k:ℝ)-1) ^ (-σ) / σ) (n + 1)) :=
          Finset.sum_le_sum hstep
      _ = ((N:ℝ)-1) ^ (-σ) / σ - ((M:ℝ)-1) ^ (-σ) / σ := by
          rw [sum_Ico_sub_succ (fun k : ℕ => ((k:ℝ)-1) ^ (-σ) / σ) N M hMN.le]
      _ ≤ ((N:ℝ)-1) ^ (-σ) / σ := by
          have hM0 : (0:ℝ) ≤ ((M:ℝ)-1) ^ (-σ) / σ := by
            have hMr : (0:ℝ) ≤ (M:ℝ) - 1 := by
              have h2 : (2:ℕ) ≤ M := le_trans hN hMN.le
              have h3 : (2:ℝ) ≤ (M:ℝ) := by exact_mod_cast h2
              linarith
            exact div_nonneg (Real.rpow_nonneg hMr _) hσ0.le
          linarith

/-! #### The tail series and the approximate functional equation (P2b)

`zTail s N` is the telescope-error series from `N`.  For `re s > 1` it equals
`ζ(s) - ∑_{n<N} n^{-s} - zPot s N` (proved here); it converges absolutely for
`re s > 0`, which is what continues the identity into the strip (P2b-ii). -/

/-- The telescope-error tail series from `N`. -/
noncomputable def zTail (s : ℂ) (N : ℕ) : ℂ :=
  ∑' k : ℕ, ((((N + k : ℕ)) : ℂ) ^ (-s) - (zPot s (N + k) - zPot s (N + k + 1)))

/-- Absolute summability of the tail terms, with the strip-telescope domination
`2‖s-1‖/(N+k)^{1+re s}`. -/
theorem summable_zTail_terms (s : ℂ) (N : ℕ)
    (hσ0 : 0 < s.re) (hs1 : 1 ≤ ‖s - 1‖) (hN : 2 * ‖s - 1‖ ≤ N) (hN2 : 2 ≤ N) :
    Summable (fun k : ℕ =>
      ‖(((N + k : ℕ)) : ℂ) ^ (-s) - (zPot s (N + k) - zPot s (N + k + 1))‖) := by
  have hdom : ∀ k : ℕ,
      ‖(((N + k : ℕ)) : ℂ) ^ (-s) - (zPot s (N + k) - zPot s (N + k + 1))‖
        ≤ 2 * ‖s - 1‖ / ((N + k : ℕ):ℝ) ^ (1 + s.re) := by
    intro k
    refine cpow_sub_telescope_le_strip s (N + k) hσ0 hs1 ?_ (by omega)
    have h1 : ‖s - 1‖ ≤ (N:ℝ) := by linarith
    have h2 : (N:ℝ) ≤ ((N + k : ℕ):ℝ) := by exact_mod_cast Nat.le_add_right N k
    linarith
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) hdom ?_
  have hbase : Summable (fun n : ℕ => ((n:ℝ)) ^ (-(1 + s.re))) := by
    rw [show (fun n : ℕ => ((n:ℝ)) ^ (-(1 + s.re)))
        = (fun n : ℕ => 1 / ((n:ℝ)) ^ (1 + s.re)) from funext fun n => by
        rw [Real.rpow_neg (Nat.cast_nonneg n), inv_eq_one_div]]
    exact (Real.summable_one_div_nat_rpow).mpr (by linarith)
  have hshift : Summable (fun k : ℕ => (((N + k : ℕ)):ℝ) ^ (-(1 + s.re))) := by
    have h1 := (summable_nat_add_iff (f := fun n : ℕ => ((n:ℝ)) ^ (-(1 + s.re))) N).mpr hbase
    refine h1.congr fun k => ?_
    congr 2
    push_cast
    ring
  have hconst := hshift.mul_left (2 * ‖s - 1‖)
  refine hconst.congr fun k => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg _), inv_eq_one_div]
  ring

/-- **The approximate functional equation at `re s > 1`**: the tail series is
exactly the zeta remainder. -/
theorem zeta_eq_partial_add_zPot_add_zTail (s : ℂ) (N : ℕ)
    (hσ1 : 1 < s.re) (hs1 : 1 ≤ ‖s - 1‖) (hN : 2 * ‖s - 1‖ ≤ N) (hN2 : 2 ≤ N) :
    riemannZeta s
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) + zPot s N + zTail s N := by
  have hσ0 : 0 < s.re := by linarith
  have hsne : s - 1 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hs1
    linarith
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hσ1
    norm_num at hσ1
  -- the full cpow series and its value
  have hf : Summable (fun n : ℕ => (n:ℂ) ^ (-s)) := by
    have h1 : Summable (fun n : ℕ => 1/(n:ℂ) ^ s) := by
      rw [← summable_norm_iff]
      have h2 : ∀ n : ℕ, ‖1/(n:ℂ) ^ s‖ = 1/((n:ℝ)) ^ s.re := by
        intro n
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · subst h0
          rw [show ((0:ℕ):ℂ) = 0 from by norm_num, Complex.zero_cpow hs0]
          simp [Real.zero_rpow (by linarith : s.re ≠ 0)]
        · rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos h0]
      refine Summable.congr ?_ (fun n => (h2 n).symm)
      exact (Real.summable_one_div_nat_rpow).mpr hσ1
    refine h1.congr fun n => ?_
    rw [Complex.cpow_neg, one_div]
  have hzeta : riemannZeta s = ∑' n : ℕ, (n:ℂ) ^ (-s) := by
    rw [zeta_eq_tsum_one_div_nat_cpow hσ1]
    refine tsum_congr fun n => ?_
    rw [Complex.cpow_neg, one_div]
  -- split at N
  have hsplit := hf.sum_add_tsum_nat_add N
  have hrange : ∑ n ∈ Finset.range N, (n:ℂ) ^ (-s)
      = ∑ n ∈ Finset.Ico 1 N, (n:ℂ) ^ (-s) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < N)]
    rw [show ((0:ℕ):ℂ) = 0 from by norm_num, Complex.zero_cpow (by
      intro h
      rw [neg_eq_zero] at h
      exact hs0 h)]
    ring
  -- the potential telescope sums to `zPot s N`
  have hpotdiff : Summable (fun k : ℕ => zPot s (N + k) - zPot s (N + k + 1)) := by
    have h1 : Summable (fun k : ℕ => (((N + k : ℕ)):ℂ) ^ (-s)) := by
      have := (summable_nat_add_iff (f := fun n : ℕ => (n:ℂ) ^ (-s)) N).mpr hf
      refine this.congr fun k => ?_
      congr 2
      push_cast
      ring
    have h2 : Summable (fun k : ℕ =>
        (((N + k : ℕ)):ℂ) ^ (-s) - (zPot s (N + k) - zPot s (N + k + 1))) := by
      rw [← summable_norm_iff]
      exact summable_zTail_terms s N hσ0 hs1 hN hN2
    have h3 := h1.sub h2
    refine h3.congr fun k => ?_
    ring
  have hpot_tendsto : Filter.Tendsto (fun K : ℕ => zPot s (N + K)) Filter.atTop
      (nhds 0) := by
    rw [show (0:ℂ) = 0 from rfl]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbound : ∀ K : ℕ, ‖zPot s (N + K)‖ ≤ ((N + K : ℕ):ℝ) ^ (1 - s.re) := by
      intro K
      rw [zPot, norm_div]
      have hNK : 0 < N + K := by omega
      have h1 : ‖(((N + K : ℕ)):ℂ) ^ ((1:ℂ) - s)‖ = ((N + K : ℕ):ℝ) ^ (1 - s.re) := by
        rw [Complex.norm_natCast_cpow_of_pos hNK]
        congr 1
      rw [h1]
      calc ((N + K : ℕ):ℝ) ^ (1 - s.re) / ‖s - 1‖
          ≤ ((N + K : ℕ):ℝ) ^ (1 - s.re) / 1 := by
            gcongr
          _ = ((N + K : ℕ):ℝ) ^ (1 - s.re) := div_one _
    refine squeeze_zero (fun K => norm_nonneg _) hbound ?_
    have h1 : Filter.Tendsto (fun K : ℕ => ((N + K : ℕ):ℝ)) Filter.atTop
        Filter.atTop := by
      refine Filter.tendsto_atTop_mono (fun K => ?_)
        tendsto_natCast_atTop_atTop
      exact_mod_cast Nat.le_add_left K N
    have h2 : Filter.Tendsto (fun x : ℝ => x ^ (1 - s.re)) Filter.atTop
        (nhds 0) := by
      have h3 := tendsto_rpow_neg_atTop (y := s.re - 1) (by linarith)
      refine h3.congr fun x => ?_
      congr 1
      ring
    exact h2.comp h1
  have hpot_sum : ∑' k : ℕ, (zPot s (N + k) - zPot s (N + k + 1)) = zPot s N := by
    have hpartial : ∀ K : ℕ, ∑ k ∈ Finset.range K,
        (zPot s (N + k) - zPot s (N + k + 1)) = zPot s N - zPot s (N + K) := by
      intro K
      calc ∑ k ∈ Finset.range K, (zPot s (N + k) - zPot s (N + k + 1))
          = ∑ k ∈ Finset.range K,
            ((fun j => zPot s (N + j)) k - (fun j => zPot s (N + j)) (k + 1)) := rfl
        _ = zPot s (N + 0) - zPot s (N + K) := Finset.sum_range_sub' _ K
        _ = zPot s N - zPot s (N + K) := by norm_num
    have h1 := hpotdiff.hasSum.tendsto_sum_nat
    have h2 : Filter.Tendsto (fun K : ℕ => zPot s N - zPot s (N + K))
        Filter.atTop (nhds (zPot s N)) := by
      have := Filter.Tendsto.const_sub (zPot s N) hpot_tendsto
      simpa using this
    have h3 : Filter.Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K,
        (zPot s (N + k) - zPot s (N + k + 1))) Filter.atTop (nhds (zPot s N)) := by
      refine h2.congr fun K => ?_
      rw [hpartial K]
    exact tendsto_nhds_unique h1 h3
  -- assemble
  have hshift : Summable (fun k : ℕ => (((N + k : ℕ)):ℂ) ^ (-s)) := by
    have := (summable_nat_add_iff (f := fun n : ℕ => (n:ℂ) ^ (-s)) N).mpr hf
    refine this.congr fun k => ?_
    congr 2
    push_cast
    ring
  have htail : zTail s N
      = (∑' k : ℕ, (((N + k : ℕ)):ℂ) ^ (-s)) - zPot s N := by
    rw [zTail, Summable.tsum_sub hshift hpotdiff, hpot_sum]
  have htsum_shift : ∑' k : ℕ, (((N + k : ℕ)):ℂ) ^ (-s)
      = ∑' k : ℕ, ((k + N : ℕ):ℂ) ^ (-s) := by
    refine tsum_congr fun k => ?_
    congr 2
    omega
  have hkey : ∑' n : ℕ, (n:ℂ) ^ (-s)
      = (∑ n ∈ Finset.Ico 1 N, (n:ℂ) ^ (-s))
        + ∑' k : ℕ, (((N + k : ℕ)):ℂ) ^ (-s) := by
    rw [htsum_shift]
    rw [← hrange, ← hsplit]
  rw [hzeta, hkey, htail]
  ring

/-- Differentiability of the tail series on an open set in the strip that is
bounded away from `s = 1` and has `‖s-1‖` dominated by `N`. -/
theorem differentiableOn_zTail (N : ℕ) (hN2 : 2 ≤ N) (V : Set ℂ)
    (hVo : IsOpen V)
    (hVsub : ∀ s ∈ V, 1/4 < s.re ∧ 1 ≤ ‖s - 1‖ ∧ 2 * ‖s - 1‖ ≤ N) :
    DifferentiableOn ℂ (fun s => zTail s N) V := by
  have hu : Summable (fun k : ℕ => (N:ℝ) * (((N + k : ℕ)):ℝ) ^ (-(5/4 : ℝ))) := by
    have hbase : Summable (fun n : ℕ => ((n:ℝ)) ^ (-(5/4 : ℝ))) := by
      rw [show (fun n : ℕ => ((n:ℝ)) ^ (-(5/4 : ℝ)))
          = (fun n : ℕ => 1 / ((n:ℝ)) ^ (5/4 : ℝ)) from funext fun n => by
          rw [Real.rpow_neg (Nat.cast_nonneg n), inv_eq_one_div]]
      exact (Real.summable_one_div_nat_rpow).mpr (by norm_num)
    have hshift := (summable_nat_add_iff
      (f := fun n : ℕ => ((n:ℝ)) ^ (-(5/4 : ℝ))) N).mpr hbase
    have hshift' : Summable (fun k : ℕ => (((N + k : ℕ)):ℝ) ^ (-(5/4 : ℝ))) := by
      refine hshift.congr fun k => ?_
      congr 2
      push_cast
      ring
    exact hshift'.mul_left _
  refine Complex.differentiableOn_tsum_of_summable_norm hu ?_ hVo ?_
  · intro k
    have hbne : (((N + k : ℕ)):ℂ) ≠ 0 := by
      exact_mod_cast (by omega : N + k ≠ 0)
    have hbne' : (((N + k + 1 : ℕ)):ℂ) ≠ 0 := by
      exact_mod_cast (by omega : N + k + 1 ≠ 0)
    have hphase : Differentiable ℂ (fun s : ℂ => -s) := differentiable_id.neg
    have hd1 : DifferentiableOn ℂ (fun s : ℂ => (((N + k : ℕ)):ℂ) ^ (-s)) V :=
      (hphase.const_cpow (Or.inl hbne)).differentiableOn
    have hne1 : ∀ w ∈ V, w - 1 ≠ 0 := by
      intro w hw h0
      have h1 := (hVsub w hw).2.1
      rw [h0, norm_zero] at h1
      linarith
    have hdpot : ∀ m : ℕ, ((m:ℕ):ℂ) ≠ 0 →
        DifferentiableOn ℂ (fun s : ℂ => zPot s m) V := by
      intro m hm
      have hnum : Differentiable ℂ (fun s : ℂ => (1:ℂ) - s) :=
        (differentiable_const 1).sub differentiable_id
      refine DifferentiableOn.div ?_ ?_ hne1
      · exact (hnum.const_cpow (Or.inl hm)).differentiableOn
      · exact (differentiable_id.sub_const 1).differentiableOn
    exact (hd1.sub ((hdpot _ hbne).sub (hdpot _ hbne')))
  · intro k s hs
    obtain ⟨hre, hs1, hsN⟩ := hVsub s hs
    have hσ0 : 0 < s.re := by linarith
    have hnk : ‖s - 1‖ ≤ ((N + k : ℕ):ℝ) := by
      have h1 : ‖s - 1‖ ≤ (N:ℝ) := by linarith
      have h2 : (N:ℝ) ≤ ((N + k : ℕ):ℝ) := by exact_mod_cast Nat.le_add_right N k
      linarith
    refine le_trans (cpow_sub_telescope_le_strip s (N + k) hσ0 hs1 hnk (by omega)) ?_
    have hNK1 : (1:ℝ) ≤ ((N + k : ℕ):ℝ) := by
      have : (1:ℕ) ≤ N + k := by omega
      exact_mod_cast this
    have hexp : (((N + k : ℕ)):ℝ) ^ (-(1 + s.re))
        ≤ (((N + k : ℕ)):ℝ) ^ (-(5/4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hNK1 (by linarith)
    calc 2 * ‖s - 1‖ / ((N + k : ℕ):ℝ) ^ (1 + s.re)
        = 2 * ‖s - 1‖ * ((N + k : ℕ):ℝ) ^ (-(1 + s.re)) := by
          rw [Real.rpow_neg (by linarith), inv_eq_one_div]
          ring
      _ ≤ (N:ℝ) * ((N + k : ℕ):ℝ) ^ (-(1 + s.re)) :=
          mul_le_mul_of_nonneg_right hsN (by positivity)
      _ ≤ (N:ℝ) * ((N + k : ℕ):ℝ) ^ (-(5/4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)

/-- **The AFE on a convex region** (identity-theorem step): on an open convex
region inside the strip, avoiding `s = 1` via `1 ≤ ‖s-1‖`, dominated by `N`,
and containing a point of `re > 1`, the approximate functional equation holds
throughout. -/
theorem zeta_eq_partial_add_zPot_add_zTail_of_convex (N : ℕ) (hN2 : 2 ≤ N)
    (V : Set ℂ) (hVo : IsOpen V) (hVc : Convex ℝ V)
    (hVsub : ∀ s ∈ V, 1/4 < s.re ∧ 1 ≤ ‖s - 1‖ ∧ 2 * ‖s - 1‖ ≤ N)
    (s₀ : ℂ) (hs₀V : s₀ ∈ V) (hs₀ : 1 < s₀.re)
    {s : ℂ} (hs : s ∈ V) :
    riemannZeta s
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) + zPot s N + zTail s N := by
  have hne1 : ∀ w ∈ V, w ≠ 1 := by
    intro w hw h1
    have h2 := (hVsub w hw).2.1
    rw [h1, sub_self, norm_zero] at h2
    linarith
  have hne1' : ∀ w ∈ V, w - 1 ≠ 0 := by
    intro w hw h0
    exact hne1 w hw (by
      have := sub_eq_zero.mp h0
      exact this)
  -- both sides analytic on `V`
  have hlhs : AnalyticOnNhd ℂ riemannZeta V := by
    refine DifferentiableOn.analyticOnNhd ?_ hVo
    intro w hw
    exact (differentiableAt_riemannZeta (hne1 w hw)).differentiableWithinAt
  have hrhs : AnalyticOnNhd ℂ
      (fun s => (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) + zPot s N + zTail s N)
      V := by
    refine DifferentiableOn.analyticOnNhd ?_ hVo
    refine DifferentiableOn.add (DifferentiableOn.add ?_ ?_) ?_
    · have hterm : ∀ n ∈ Finset.Ico 1 N,
          DifferentiableOn ℂ (fun s : ℂ => (n : ℂ) ^ (-s)) V := by
        intro n hn
        have hnne : ((n:ℕ):ℂ) ≠ 0 := by
          rw [Finset.mem_Ico] at hn
          exact_mod_cast (by omega : n ≠ 0)
        have hphase : Differentiable ℂ (fun s : ℂ => -s) := differentiable_id.neg
        exact (hphase.const_cpow (Or.inl hnne)).differentiableOn
      refine (DifferentiableOn.sum hterm).congr fun w _ => ?_
      simp
    · have hnum : Differentiable ℂ (fun s : ℂ => (1:ℂ) - s) :=
        (differentiable_const 1).sub differentiable_id
      refine DifferentiableOn.div ?_ ?_ hne1'
      · have hNne : ((N:ℕ):ℂ) ≠ 0 := by
          exact_mod_cast (by omega : N ≠ 0)
        exact (hnum.const_cpow (Or.inl hNne)).differentiableOn
      · exact (differentiable_id.sub_const 1).differentiableOn
    · exact differentiableOn_zTail N hN2 V hVo hVsub
  -- they agree near the anchor
  have hevent : riemannZeta =ᶠ[nhds s₀]
      (fun s => (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) + zPot s N + zTail s N) := by
    have hU : IsOpen ({w : ℂ | 1 < w.re} ∩ V) :=
      (isOpen_lt continuous_const Complex.continuous_re).inter hVo
    refine Filter.eventuallyEq_of_mem (hU.mem_nhds ⟨hs₀, hs₀V⟩) ?_
    intro w hw
    exact zeta_eq_partial_add_zPot_add_zTail w N hw.1 (hVsub w hw.2).2.1
      (hVsub w hw.2).2.2 hN2
  exact hlhs.eqOn_of_preconnected_of_eventuallyEq hrhs hVc.isPreconnected
    hs₀V hevent hs

/-- **The approximate functional equation in the strip**: for `1/2 ≤ re s`,
`2 ≤ |im s|`, and `N ≥ 4‖s-1‖`, the zeta function is the partial sum plus the
potential plus the absolutely convergent tail.  (The convex-region argument is
run in the upper or lower half-plane according to the sign of `im s`.) -/
theorem zeta_afe_strip (s : ℂ) (N : ℕ)
    (hσ : 1/2 ≤ s.re) (him : 2 ≤ |s.im|) (hN : 4 * ‖s - 1‖ ≤ N) :
    riemannZeta s
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) + zPot s N + zTail s N := by
  have him1 : 1 ≤ ‖s - 1‖ := by
    have h1 : |s.im| ≤ ‖s - 1‖ := by
      have h2 : (s - 1).im = s.im := by simp
      calc |s.im| = |(s - 1).im| := by rw [h2]
        _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
    linarith
  have hN2 : 2 ≤ N := by
    have h1 : (4:ℝ) ≤ (N:ℝ) := by linarith
    have h2 : (4:ℕ) ≤ N := by exact_mod_cast h1
    omega
  have hNhalf : ‖s - 1‖ < (N:ℝ)/2 := by
    have h0 : (0:ℝ) < N := by
      have : (2:ℕ) ≤ N := hN2
      exact_mod_cast lt_of_lt_of_le (by norm_num) this
    nlinarith
  -- the membership conditions common to both half-plane regions
  have hmem : ∀ w : ℂ, 1/4 < w.re → 1 < |w.im| → w ∈ Metric.ball (1:ℂ) ((N:ℝ)/2) →
      1/4 < w.re ∧ 1 ≤ ‖w - 1‖ ∧ 2 * ‖w - 1‖ ≤ N := by
    intro w hre him' hball
    refine ⟨hre, ?_, ?_⟩
    · have h1 : |w.im| ≤ ‖w - 1‖ := by
        have h2 : (w - 1).im = w.im := by simp
        calc |w.im| = |(w - 1).im| := by rw [h2]
          _ ≤ ‖w - 1‖ := Complex.abs_im_le_norm _
      linarith
    · have h1 : ‖w - 1‖ < (N:ℝ)/2 := by
        rw [Metric.mem_ball, Complex.dist_eq] at hball
        exact hball
      linarith
  rcases le_abs.mp him with hup | hdn
  · -- upper half-plane region
    set V : Set ℂ := {w : ℂ | 1/4 < w.re} ∩ ({w : ℂ | 1 < w.im}
      ∩ Metric.ball (1:ℂ) ((N:ℝ)/2)) with hV_def
    have hVo : IsOpen V :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          Metric.isOpen_ball))
    have hVc : Convex ℝ V :=
      (convex_halfSpace_re_gt _).inter
        ((convex_halfSpace_im_gt _).inter (convex_ball _ _))
    have hVsub : ∀ w ∈ V, 1/4 < w.re ∧ 1 ≤ ‖w - 1‖ ∧ 2 * ‖w - 1‖ ≤ N := by
      intro w hw
      obtain ⟨h1, h2, h3⟩ := hw
      have h1' : 1/4 < w.re := h1
      have h2' : 1 < w.im := h2
      exact hmem w h1' (by
        rw [abs_of_pos (by linarith : (0:ℝ) < w.im)]
        exact h2') h3
    have hanchorV : (2 + 2*Complex.I : ℂ) ∈ V := by
      refine ⟨show (1:ℝ)/4 < (2 + 2*Complex.I : ℂ).re from by
          norm_num [Complex.add_re, Complex.mul_re],
        show (1:ℝ) < (2 + 2*Complex.I : ℂ).im from by
          simp [Complex.add_im, Complex.mul_im], ?_⟩
      rw [Metric.mem_ball, Complex.dist_eq]
      have h1 : (2 + 2*Complex.I : ℂ) - 1 = 1 + 2*Complex.I := by ring
      rw [h1]
      have h2 : ‖(1 + 2*Complex.I : ℂ)‖ ≤ 3 := by
        calc ‖(1 + 2*Complex.I : ℂ)‖ ≤ ‖(1:ℂ)‖ + ‖(2*Complex.I : ℂ)‖ :=
              norm_add_le _ _
          _ = 1 + 2 := by simp
          _ = 3 := by norm_num
      have h3 : (3:ℝ) < (N:ℝ)/2 := by
        have h4 : (4:ℝ) * 1 ≤ (N:ℝ) := by
          calc (4:ℝ) * 1 ≤ 4 * ‖s - 1‖ := by linarith
            _ ≤ (N:ℝ) := hN
        have h5 : (4:ℝ) * 2 ≤ (N:ℝ) := by
          have h6 : (2:ℝ) ≤ ‖s - 1‖ := by
            have h7 : |s.im| ≤ ‖s - 1‖ := by
              have h8 : (s - 1).im = s.im := by simp
              calc |s.im| = |(s - 1).im| := by rw [h8]
                _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
            linarith
          linarith
        linarith
      linarith
    have hsV : s ∈ V := by
      refine ⟨show (1:ℝ)/4 < s.re from by linarith,
        show (1:ℝ) < s.im from by linarith, ?_⟩
      rw [Metric.mem_ball, Complex.dist_eq]
      exact hNhalf
    refine zeta_eq_partial_add_zPot_add_zTail_of_convex N hN2 V hVo hVc hVsub
      (2 + 2*Complex.I) hanchorV ?_ hsV
    simp [Complex.add_re, Complex.mul_re]
  · -- lower half-plane region
    set V : Set ℂ := {w : ℂ | 1/4 < w.re} ∩ ({w : ℂ | w.im < -1}
      ∩ Metric.ball (1:ℂ) ((N:ℝ)/2)) with hV_def
    have hVo : IsOpen V :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        ((isOpen_lt Complex.continuous_im continuous_const).inter
          Metric.isOpen_ball))
    have hVc : Convex ℝ V :=
      (convex_halfSpace_re_gt _).inter
        ((convex_halfSpace_im_lt _).inter (convex_ball _ _))
    have hVsub : ∀ w ∈ V, 1/4 < w.re ∧ 1 ≤ ‖w - 1‖ ∧ 2 * ‖w - 1‖ ≤ N := by
      intro w hw
      obtain ⟨h1, h2, h3⟩ := hw
      have h1' : 1/4 < w.re := h1
      have h2' : w.im < -1 := h2
      exact hmem w h1' (by
        rw [abs_of_neg (by linarith : w.im < 0)]
        linarith) h3
    have hanchorV : (2 - 2*Complex.I : ℂ) ∈ V := by
      refine ⟨show (1:ℝ)/4 < (2 - 2*Complex.I : ℂ).re from by
          norm_num [Complex.sub_re, Complex.mul_re],
        show (2 - 2*Complex.I : ℂ).im < -1 from by
          simp [Complex.sub_im, Complex.mul_im], ?_⟩
      · rw [Metric.mem_ball, Complex.dist_eq]
        have h1 : (2 - 2*Complex.I : ℂ) - 1 = 1 - 2*Complex.I := by ring
        rw [h1]
        have h2 : ‖(1 - 2*Complex.I : ℂ)‖ ≤ 3 := by
          calc ‖(1 - 2*Complex.I : ℂ)‖ ≤ ‖(1:ℂ)‖ + ‖(2*Complex.I : ℂ)‖ :=
                norm_sub_le _ _
            _ = 1 + 2 := by simp
            _ = 3 := by norm_num
        have h3 : (3:ℝ) < (N:ℝ)/2 := by
          have h5 : (4:ℝ) * 2 ≤ (N:ℝ) := by
            have h6 : (2:ℝ) ≤ ‖s - 1‖ := by
              have h7 : |s.im| ≤ ‖s - 1‖ := by
                have h8 : (s - 1).im = s.im := by simp
                calc |s.im| = |(s - 1).im| := by rw [h8]
                  _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
              linarith
            linarith
          linarith
        linarith
    have hsV : s ∈ V := by
      refine ⟨show (1:ℝ)/4 < s.re from by linarith,
        show s.im < (-1:ℝ) from by linarith, ?_⟩
      rw [Metric.mem_ball, Complex.dist_eq]
      exact hNhalf
    refine zeta_eq_partial_add_zPot_add_zTail_of_convex N hN2 V hVo hVc hVsub
      (2 - 2*Complex.I) hanchorV ?_ hsV
    simp [Complex.sub_re, Complex.mul_re]

end ExpSums

end MoltResearch
