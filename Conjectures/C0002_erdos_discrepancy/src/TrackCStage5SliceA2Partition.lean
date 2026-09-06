import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2Ladder

/-!
# Track R A2-V'-3: aggregation of short relative slices

The Fourier window has a collar proportional to `H*s/A`, so the honest
application uses slices with `s/A` small.  This file is the purely arithmetic
aggregation step: equal slices cover an initial segment and the final partial
slice is paid trivially.  A dyadic-length interval has harmonic mass bounded
below by an absolute constant, so choosing the number of slices of order
`eps^{-2}` absorbs that remainder.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- A block of length at least half its left endpoint has a fixed amount of
harmonic mass.  The constant `1/8` leaves room for natural-number rounding. -/
theorem one_eighth_le_slice_harmonic
    (A J : ℕ) (hA : 2 ≤ A) (hJlo : A / 2 ≤ J) (hJhi : J ≤ A) :
    (1 : ℝ) / 8 ≤ ∑ n ∈ Finset.Ioc A (A + J), (1 : ℝ) / n := by
  have hJ1 : 1 ≤ J := by
    have : 1 ≤ A / 2 := (Nat.one_le_div_iff (by norm_num)).mpr hA
    omega
  have hA3J : A ≤ 3 * J := by
    have hround : A ≤ 2 * J + 1 := by omega
    omega
  have hAR : (0 : ℝ) < A := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hA)
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ1
  have hratio : (1 : ℝ) / 8 ≤ (J : ℝ) / (2 * A) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * A)]
    have hA3JR : (A : ℝ) ≤ 3 * J := by exact_mod_cast hA3J
    nlinarith
  calc
    (1 : ℝ) / 8 ≤ (J : ℝ) / (2 * A) := hratio
    _ = ∑ _n ∈ Finset.Ioc A (A + J), (1 : ℝ) / (2 * A) := by
      rw [Finset.sum_const, Nat.card_Ioc, Nat.add_sub_cancel_left,
        nsmul_eq_mul]
      ring
    _ ≤ ∑ n ∈ Finset.Ioc A (A + J), (1 : ℝ) / n := by
      apply Finset.sum_le_sum
      intro n hn
      have hnle : n ≤ 2 * A := by
        have hn' := (Finset.mem_Ioc.mp hn).2
        omega
      have hnpos : 0 < n := by
        have hn' := (Finset.mem_Ioc.mp hn).1
        omega
      apply one_div_le_one_div_of_le
        (by exact_mod_cast hnpos)
      exact_mod_cast hnle

/-- Aggregate fixed-width small slices and absorb the final incomplete slice.

The full slices are allowed half of the requested square-saving.  The guard
`16 ≤ eps² M` gives the other half to the remainder of length less than
`A/M`. -/
theorem slice_meanSquare_le_of_small_slices
    (levels : List (Finset ℕ)) (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (A J H M : ℕ) (eps : ℝ)
    (hA : 2 ≤ A) (hJlo : A / 2 ≤ J) (hJhi : J ≤ A)
    (hM : 0 < M) (hMA : M ≤ A) (heps : 0 < eps)
    (hMfit : 16 ≤ eps ^ 2 * (M : ℝ))
    (hslices : ∀ i ∈ Finset.range (J / (A / M)),
      ∑ n ∈ Finset.Ioc (A + i * (A / M)) (A + (i + 1) * (A / M)),
          ‖∑ m ∈ (Finset.Ioc n (n + H)).filter (HasFactorInAll levels),
            g m‖ ^ 2 / n
        ≤ (eps ^ 2 / 2) * (H : ℝ) ^ 2 *
          ∑ n ∈ Finset.Ioc (A + i * (A / M))
            (A + (i + 1) * (A / M)), (1 : ℝ) / n) :
    ∑ n ∈ Finset.Ioc A (A + J),
        ‖∑ m ∈ (Finset.Ioc n (n + H)).filter (HasFactorInAll levels),
          g m‖ ^ 2 / n
      ≤ eps ^ 2 * (H : ℝ) ^ 2 *
        ∑ n ∈ Finset.Ioc A (A + J), (1 : ℝ) / n := by
  classical
  let s := A / M
  let K := J / s
  let R := J % s
  have hs : 0 < s := by
    dsimp [s]
    exact (Nat.one_le_div_iff hM).mpr hMA
  have hdecomp : K * s + R = J := by
    dsimp [K, R]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod J s
  let F : ℕ → ℝ := fun n =>
    ‖∑ m ∈ (Finset.Ioc n (n + H)).filter (HasFactorInAll levels),
      g m‖ ^ 2 / n
  let W : ℕ → ℝ := fun n => (1 : ℝ) / n
  have hF0 : ∀ n, 0 ≤ F n := fun n => by dsimp [F]; positivity
  have hW0 : ∀ n, 0 ≤ W n := fun n => by dsimp [W]; positivity
  have hfull : ∑ n ∈ Finset.Ioc A (A + K * s), F n ≤
      (eps ^ 2 / 2) * (H : ℝ) ^ 2 *
        ∑ n ∈ Finset.Ioc A (A + K * s), W n := by
    calc
      ∑ n ∈ Finset.Ioc A (A + K * s), F n ≤
          ∑ i ∈ Finset.range K,
            ((eps ^ 2 / 2) * (H : ℝ) ^ 2 *
              ∑ n ∈ Finset.Ioc (A + i * s) (A + (i + 1) * s), W n) := by
        apply MoltResearch.ExpSums.sum_Ioc_le_of_slice_bounds
        intro i hi
        simpa only [s, K, F, W] using hslices i hi
      _ = (eps ^ 2 / 2) * (H : ℝ) ^ 2 *
          ∑ n ∈ Finset.Ioc A (A + K * s), W n := by
        rw [← Finset.mul_sum, MoltResearch.sum_range_sum_Ioc_slices]
  have hKR : A + K * s ≤ A + J := by omega
  have hsplitF :
      (∑ n ∈ Finset.Ioc A (A + J), F n) =
        ∑ n ∈ Finset.Ioc A (A + K * s), F n +
          ∑ n ∈ Finset.Ioc (A + K * s) (A + J), F n := by
    rw [Finset.sum_Ioc_consecutive F (Nat.le_add_right A (K * s)) hKR]
  have hsplitW :
      (∑ n ∈ Finset.Ioc A (A + J), W n) =
        ∑ n ∈ Finset.Ioc A (A + K * s), W n +
          ∑ n ∈ Finset.Ioc (A + K * s) (A + J), W n := by
    rw [Finset.sum_Ioc_consecutive W (Nat.le_add_right A (K * s)) hKR]
  have htail : ∑ n ∈ Finset.Ioc (A + K * s) (A + J), F n ≤
      (eps ^ 2 / 2) * (H : ℝ) ^ 2 *
        ∑ n ∈ Finset.Ioc A (A + J), W n := by
    have hpoint : ∀ n ∈ Finset.Ioc (A + K * s) (A + J),
        F n ≤ (H : ℝ) ^ 2 / A := by
      intro n hn
      have hnA : A ≤ n := by
        have hn' := (Finset.mem_Ioc.mp hn).1
        omega
      have hn0 : (0 : ℝ) < n := by
        exact_mod_cast (lt_of_lt_of_le (by omega : 0 < A) hnA)
      have hnorm := norm_filter_block_le_card (HasFactorInAll levels) g hg n (n + H)
      have hnorm' :
          ‖∑ m ∈ (Finset.Ioc n (n + H)).filter (HasFactorInAll levels),
            g m‖ ≤ H := by simpa using hnorm
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm' 2
      dsimp [F]
      calc
        _ ≤ (H : ℝ) ^ 2 / n := div_le_div_of_nonneg_right hsq hn0.le
        _ ≤ (H : ℝ) ^ 2 / A := by
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          exact_mod_cast hnA
    have hcard : (Finset.Ioc (A + K * s) (A + J)).card = R := by
      rw [Nat.card_Ioc]
      omega
    have hsum : ∑ n ∈ Finset.Ioc (A + K * s) (A + J), F n ≤
        (R : ℝ) * ((H : ℝ) ^ 2 / A) := by
      calc
        _ ≤ ∑ _n ∈ Finset.Ioc (A + K * s) (A + J),
            (H : ℝ) ^ 2 / A := Finset.sum_le_sum hpoint
        _ = (R : ℝ) * ((H : ℝ) ^ 2 / A) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
    have hRlt : R < s := Nat.mod_lt J hs
    have hRle : (R : ℝ) ≤ (A : ℝ) / M := by
      have hRN : R ≤ A / M := by simpa [s] using hRlt.le
      have hcast : ((A / M : ℕ) : ℝ) ≤ (A : ℝ) / M := by
        exact Nat.cast_div_le
      have hRN' : (R : ℝ) ≤ (A / M : ℕ) := by exact_mod_cast hRN
      exact hRN'.trans hcast
    have htailSimple :
        (R : ℝ) * ((H : ℝ) ^ 2 / A) ≤ (H : ℝ) ^ 2 / M := by
      have hMR : (0 : ℝ) < M := by exact_mod_cast hM
      have hAR : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
      calc
        _ ≤ ((A : ℝ) / M) * ((H : ℝ) ^ 2 / A) := by
          gcongr
        _ = (H : ℝ) ^ 2 / M := by field_simp
    have hsmall : (H : ℝ) ^ 2 / M ≤ eps ^ 2 * (H : ℝ) ^ 2 / 16 := by
      apply (div_le_iff₀ (by exact_mod_cast hM)).2
      have hMfit' : 16 ≤ eps ^ 2 * (M : ℝ) := hMfit
      nlinarith [sq_nonneg (H : ℝ)]
    have hmass := one_eighth_le_slice_harmonic A J hA hJlo hJhi
    have htarget : eps ^ 2 * (H : ℝ) ^ 2 / 16 ≤
        (eps ^ 2 / 2) * (H : ℝ) ^ 2 *
          ∑ n ∈ Finset.Ioc A (A + J), W n := by
      dsimp [W]
      have hcoef : 0 ≤ (eps ^ 2 / 2) * (H : ℝ) ^ 2 := by positivity
      calc
        _ = ((eps ^ 2 / 2) * (H : ℝ) ^ 2) * ((1 : ℝ) / 8) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hmass hcoef
    exact hsum.trans (htailSimple.trans (hsmall.trans htarget))
  rw [hsplitF, hsplitW]
  have hfullW : 0 ≤ ∑ n ∈ Finset.Ioc A (A + K * s), W n :=
    Finset.sum_nonneg fun n _ => hW0 n
  have htailW : 0 ≤ ∑ n ∈ Finset.Ioc (A + K * s) (A + J), W n :=
    Finset.sum_nonneg fun n _ => hW0 n
  have htail' : ∑ n ∈ Finset.Ioc (A + K * s) (A + J), F n ≤
      (eps ^ 2 / 2) * (H : ℝ) ^ 2 *
        (∑ n ∈ Finset.Ioc A (A + K * s), W n +
          ∑ n ∈ Finset.Ioc (A + K * s) (A + J), W n) := by
    rw [← hsplitW]
    exact htail
  calc
    _ ≤ (eps ^ 2 / 2) * (H : ℝ) ^ 2 *
          ∑ n ∈ Finset.Ioc A (A + K * s), W n +
        (eps ^ 2 / 2) * (H : ℝ) ^ 2 *
          (∑ n ∈ Finset.Ioc A (A + K * s), W n +
            ∑ n ∈ Finset.Ioc (A + K * s) (A + J), W n) :=
      add_le_add hfull htail'
    _ ≤ eps ^ 2 * (H : ℝ) ^ 2 *
          (∑ n ∈ Finset.Ioc A (A + K * s), W n +
            ∑ n ∈ Finset.Ioc (A + K * s) (A + J), W n) := by
      have he2 : 0 ≤ eps ^ 2 / 2 * (H : ℝ) ^ 2 := by positivity
      nlinarith

end Tao2015

end MoltResearch
