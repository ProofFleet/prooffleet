import MoltResearch.Discrepancy.HalaszComplex

/-!
# The sharp survivor split: Halász with no `loglog` against the quality

`tripleConvRC_survivors_balanced_shell_le` prices every one of the
`K₀ ≈ loglog x` prime blocks of §3's survivor set by the same band-sup
shell `x·√((e^π)²·10¹⁵·(b²+1)) + 2x·log 4`, so the Riesz-mean budget
carries the factor `loglog x` against the Halász quality
`b = e⁵(2+log x)·e^{−A}`.  At a *fixed* strength `A` that factor is fatal
(design report §6, Finding C; Phase 0 report, "central `T₀` window"): the
plain-sum saving `≍ √(loglog x)·e^{−A/2}` is not small uniformly in the
scale, so the `𝒯₀` leg of `[mrt]` Prop. A.3 could not be stated.

The loss is an artefact of the accounting, not of the method.  Block `k`
(`p ∈ [x^{1−e^{1−k}}, x^{1−e^{−k}})`) also has the trivial bound
`x·(16·(log blockHi − log blockLo) + 16·log 4)
  ≤ 16(e−1)·e^{−k}·x·log x + 48·log 2·x`
(`norm_tripleConvRC_le''` with `log_blockHi_sub_log_blockLo_le`), which is
geometric in `k`.  Pricing only the first `K₁ ≤ K₀` blocks by the shell and
the remaining `K₀ + 2 − K₁` trivially gives

  `K₁·shell + 16(e−1)·e^{−K₁}·x·log x + (K₀+2−K₁)·48·log 2·x`

(`tripleConvRC_survivors_sharp_le`).  With `K₁ := min(K₀, ⌈A⌉)` one has
`K₁ ≤ A + 1`, `K₁ ≤ loglog x`, and `e^{−K₁}·log x ≤ e^{−A}·log x + e²·log 2`,
so the windowed budget `halaszBudgetSharp` carries `(A+1)` in place of
`loglog x` against `e^{−A}`, while the shell's `+1` floor and the trivial
tail are confined to the `loglog x/log x` group.  This is the classical
`(1+M)·e^{−M}` shape of Halász's theorem (Granville–Harper–Soundararajan,
Cor. 1.2), obtained inside the existing §3 machinery; the plain-sum
corollaries `plain_sumC_le_halaszBudgetSharp(_div)` are the exact mirrors
of the shell wrappers, ready for the window plumbing of the `𝒯₀` leg.
-/

namespace MoltResearch

set_option maxHeartbeats 3200000 in
open Real Finset ArithmeticFunction in
/-- **The survivor estimate, sharp `k`-split** (Track R, T0-1): the
`k`-split of the survivor triple convolution with the first `K₁ ≤ K₀`
blocks priced by the shell balanced estimate and every later block
(`K₁ < k ≤ K₀ + 2`) by the fit-free trivial bound, summed geometrically —

  `‖tripleConvRC f x 𝒮‖ ≤ K₁·(x·√((e^π)²·10¹⁵·(b²+1)) + 2x·log 4)
     + 16(e−1)·x·log x·e^{−K₁} + (K₀+2−K₁)·x·(16·log 2 + 16·log 4)`.

At `K₁ = K₀` this is the shell estimate (up to the tail's `e^{−K₀}·log x
≤ e²·log 2`); the point is that `K₁` may be chosen `≍ A`, so the factor
against the quality `b` stops growing with the scale. -/
theorem tripleConvRC_survivors_sharp_le (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (x y K₀ K₁ : ℕ) (hx : 10^16 ≤ x) (hy2 : 2 ≤ y)
    (hy : (Real.log (x:ℝ))^2 ≤ (y:ℝ))
    (hK₀1 : 1 ≤ K₀)
    (hK₀low : Real.exp 1 * Real.log 2
      ≤ Real.exp (-(K₀:ℝ)) * Real.log (x:ℝ))
    (hK₀max : Real.exp (-((K₀:ℝ)+1)) * Real.log (x:ℝ)
      < Real.exp 1 * Real.log 2)
    (hK₁ : K₁ ≤ K₀)
    (hX3 : ∀ k ∈ Finset.Icc 1 K₀, 3 ≤ x / blockLo x k)
    (b : ℝ) (hb0 : 0 ≤ b)
    (hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖ExpSums.smoothPhaseSum f x t‖ ≤ b) :
    ‖tripleConvRC f x ((((Finset.Icc 1 x).filter Nat.Prime).filter
        (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p))‖
      ≤ (K₁:ℝ) * ((x:ℝ) * Real.sqrt ((Real.exp π)^2 * 10^15 * (b^2 + 1))
          + 2*(x:ℝ)*Real.log 4)
        + (16 * (Real.exp 1 - 1) * (x:ℝ) * Real.log (x:ℝ) * Real.exp (-(K₁:ℝ))
          + ((K₀ + 2 - K₁ : ℕ):ℝ)
            * ((x:ℝ) * (16 * Real.log 2 + 16 * Real.log 4))) := by
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
  -- split, triangle, k-split at `K₁`
  rw [tripleConvRC_survivor_split f x y (K₀+2) hx1 hK]
  refine le_trans (norm_sum_le _ _) ?_
  refine sum_ksplit_le
    (fun k => ‖tripleConvRC f x (((Finset.Ico (blockLo x k)
      (blockHi x k)).filter Nat.Prime).filter
      (fun p => ¬ p < y ∧ ¬ x < 2*p))‖) K₁ (K₀+2) (by omega) _ _ ?_ ?_
  · -- the head: the primed N189 per block, then the SM-monotone step
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk1 : 1 ≤ k := hk.1
    have hkK : k ≤ K₀ := le_trans hk.2 hK₁
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
  · -- the tail: every block past `K₁`, fit-free and geometric in `k`
    have he1nn : (0:ℝ) ≤ Real.exp 1 - 1 := by
      linarith [Real.add_one_le_exp (1:ℝ)]
    have hc0 : (0:ℝ) ≤ 16 * (Real.exp 1 - 1) * (x:ℝ) * Real.log (x:ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) he1nn) hx0R.le) hL0.le
    have htb : ∀ k ∈ Finset.Icc (K₁+1) (K₀+2),
        ‖tripleConvRC f x (((Finset.Ico (blockLo x k) (blockHi x k)).filter
          Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p))‖
        ≤ 16 * (Real.exp 1 - 1) * (x:ℝ) * Real.log (x:ℝ) * Real.exp (-(k:ℝ))
          + (x:ℝ) * (16 * Real.log 2 + 16 * Real.log 4) := by
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
      have hw' : 16 * (Real.log ((blockHi x k : ℕ):ℝ)
            - Real.log ((blockLo x k : ℕ):ℝ)) + 16 * Real.log 4
          ≤ 16 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
            + (16 * Real.log 2 + 16 * Real.log 4) := by
        linarith
      calc (x:ℝ) * (16 * (Real.log ((blockHi x k : ℕ):ℝ)
              - Real.log ((blockLo x k : ℕ):ℝ)) + 16 * Real.log 4)
          ≤ (x:ℝ) * (16 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
              + (16 * Real.log 2 + 16 * Real.log 4)) :=
            mul_le_mul_of_nonneg_left hw' hx0R.le
        _ = 16 * (Real.exp 1 - 1) * (x:ℝ) * Real.log (x:ℝ) * Real.exp (-(k:ℝ))
              + (x:ℝ) * (16 * Real.log 2 + 16 * Real.log 4) := by ring
    refine le_trans (Finset.sum_le_sum htb) ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, ← Finset.mul_sum]
    have hcard : K₀ + 2 + 1 - (K₁ + 1) = K₀ + 2 - K₁ := by omega
    rw [hcard, nsmul_eq_mul]
    have hgeom := sum_exp_neg_tail_le K₁ (K₀+2)
    have hg := mul_le_mul_of_nonneg_left hgeom hc0
    linarith

set_option maxHeartbeats 1600000 in
open Real Finset ArithmeticFunction in
/-- **§3, end to end, through the sharp survivor split** (Track R, T0-2):
the identity/head/tail/bridge/survivor assembly of
`rieszMeanC_log_le_shell_of_nonPretentious` with the survivor estimate
replaced by `tripleConvRC_survivors_sharp_le` at a free split index
`K₁ ≤ K₀`.  Nothing else changes: the identity error, the head and tail
discards and the sharp survivors bridge never see the band sup. -/
theorem rieszMeanC_log_le_sharp_of_nonPretentious (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hcm : CompletelyMultiplicativeC f)
    (h1 : f 1 = 1)
    (x y K₀ K₁ : ℕ) (hx : 10^16 ≤ x) (hy2 : 2 ≤ y) (hyx : 2*y ≤ x)
    (hy : (Real.log (x:ℝ))^2 ≤ (y:ℝ))
    (hK₀1 : 1 ≤ K₀)
    (hK₀low : Real.exp 1 * Real.log 2
      ≤ Real.exp (-(K₀:ℝ)) * Real.log (x:ℝ))
    (hK₀max : Real.exp (-((K₀:ℝ)+1)) * Real.log (x:ℝ)
      < Real.exp 1 * Real.log 2)
    (hK₁ : K₁ ≤ K₀)
    (hX3 : ∀ k ∈ Finset.Icc 1 K₀, 3 ≤ x / blockLo x k)
    (b : ℝ) (hb0 : 0 ≤ b)
    (hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖ExpSums.smoothPhaseSum f x t‖ ≤ b) :
    ‖(∑ n ∈ Finset.Icc 1 x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
        * ((Real.log (x:ℝ) : ℝ) : ℂ)‖
      ≤ 35*(x:ℝ) + (x:ℝ)*(Real.log (y:ℝ) + 2) + 2*((x:ℝ)+1)*Real.log 4
        + 64 * (x:ℝ) * (12 * Real.log (Real.log (x:ℝ)) + 18)
        + ((K₁:ℝ) * ((x:ℝ) * Real.sqrt ((Real.exp π)^2 * 10^15 * (b^2 + 1))
            + 2*(x:ℝ)*Real.log 4)
          + (16 * (Real.exp 1 - 1) * (x:ℝ) * Real.log (x:ℝ) * Real.exp (-(K₁:ℝ))
            + ((K₀ + 2 - K₁ : ℕ):ℝ)
              * ((x:ℝ) * (16 * Real.log 2 + 16 * Real.log 4)))) := by
  classical
  have hx1 : (1:ℕ) ≤ x := le_trans (by norm_num) hx
  have hid := rieszMeanC_mul_log_prime_restrict f hf hcm x hx1
  have hhead := rieszMeanC_prime_head_le f hf x y hy2
  have htail := rieszMeanC_prime_tail_le f hf x
  have hbridge := rieszMeanC_survivors_to_tripleConvRC_sharp f hf hcm x y
    (le_trans (by norm_num) hx)
  have hconv := tripleConvRC_survivors_sharp_le f hf hcm h1 x y K₀ K₁
    hx hy2 hy hK₀1 hK₀low hK₀max hK₁ hX3 b hb0 hBu
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
/-- **The sharp Halász Riesz mean at a free split** (Track R, T0-3): the
`b`-instantiation of the sharp §3 assembly at `b := e⁵(2+log x)e^{−A}`,
the band sup being `norm_smoothPhaseSum_le_of_nonPretentious` on the
range `7(halaszM x + 1) ≤ A·x` (using `2π < 7`). -/
theorem rieszMeanC_log_le_sharp_halasz_of_nonPretentious (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hcm : CompletelyMultiplicativeC f)
    (h1 : f 1 = 1)
    (x y K₀ K₁ : ℕ) (hx : 10^16 ≤ x) (hy2 : 2 ≤ y) (hyx : 2*y ≤ x)
    (hy : (Real.log (x:ℝ))^2 ≤ (y:ℝ))
    (hK₀1 : 1 ≤ K₀)
    (hK₀low : Real.exp 1 * Real.log 2
      ≤ Real.exp (-(K₀:ℝ)) * Real.log (x:ℝ))
    (hK₀max : Real.exp (-((K₀:ℝ)+1)) * Real.log (x:ℝ)
      < Real.exp 1 * Real.log 2)
    (hK₁ : K₁ ≤ K₀)
    (A : ℝ) (hA : NonPretentiousAt f A x)
    (h1A : 1 ≤ A)
    (hband : 7 * (((halaszM x : ℕ):ℝ) + 1) ≤ A * (x:ℝ)) :
    ‖(∑ n ∈ Finset.Icc 1 x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
        * ((Real.log (x:ℝ) : ℝ) : ℂ)‖
      ≤ 35*(x:ℝ) + (x:ℝ)*(Real.log (y:ℝ) + 2) + 2*((x:ℝ)+1)*Real.log 4
        + 64 * (x:ℝ) * (12 * Real.log (Real.log (x:ℝ)) + 18)
        + ((K₁:ℝ) * ((x:ℝ) * Real.sqrt ((Real.exp π)^2 * 10^15
              * ((Real.exp 5 * (2 + Real.log (x:ℝ))
                  * Real.exp (-A))^2 + 1))
            + 2*(x:ℝ)*Real.log 4)
          + (16 * (Real.exp 1 - 1) * (x:ℝ) * Real.log (x:ℝ) * Real.exp (-(K₁:ℝ))
            + ((K₀ + 2 - K₁ : ℕ):ℝ)
              * ((x:ℝ) * (16 * Real.log 2 + 16 * Real.log 4)))) := by
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
    have hpi7 : 2 * Real.pi ≤ 7 := by
      have := Real.pi_lt_d2
      linarith
    rw [abs_mul, abs_of_pos Real.two_pi_pos]
    calc 2 * Real.pi * |t| ≤ 7 * |t| :=
          mul_le_mul_of_nonneg_right hpi7 (abs_nonneg t)
      _ ≤ 7 * (((halaszM x : ℕ):ℝ) + 1) :=
          mul_le_mul_of_nonneg_left ht (by norm_num)
      _ ≤ A * (x:ℝ) := hband
  exact rieszMeanC_log_le_sharp_of_nonPretentious f hf hcm h1 x y K₀ K₁ hx hy2
    hyx hy hK₀1 hK₀low hK₀max hK₁
    (three_le_div_blockLo x K₀ hx hK₀low)
    (Real.exp 5 * (2 + Real.log (x:ℝ)) * Real.exp (-A)) hb0 hBu

/-- **The sharp Halász budget** (Track R, T0-4): the per-scale numerator
`Ĥ⁺(A, z)` of the sharp plain-sum Halász capstone
`plain_sumC_le_halaszBudgetSharp`, as a function of a real scale.  Its
quality group is `(A+1)·z·√((e^π)²10¹⁵)·e⁵(2+log z)·e^{−A}
+ 16(e−1)·z·log z·e^{−A}` — **no `loglog z` against `e^{−A}`** — and
everything else is `≲ z·loglog z`:

  `Ĥ⁺(A,z)/(z·log z) ≲ (A+1)·10¹¹·e^{−A} + 10⁹·loglog z/log z`.

Compare `halaszBudgetShell`, whose quality group is
`loglog z·z·√((e^π)²10¹⁵·((e⁵(2+log z)e^{−A})²+1))`. -/
noncomputable def halaszBudgetSharp (A z : ℝ) : ℝ :=
  35*z + z*(Real.log (2*(Real.log z)^2) + 2)
    + 2*(z+1)*Real.log 4
    + 64 * z * (12 * Real.log (Real.log z) + 18)
    + (A + 1) * (z * (Real.sqrt ((Real.exp Real.pi)^2 * 10^15)
        * (Real.exp 5 * (2 + Real.log z) * Real.exp (-A))))
    + Real.log (Real.log z)
        * (z * (Real.sqrt ((Real.exp Real.pi)^2 * 10^15) + 2*Real.log 4))
    + 16 * (Real.exp 1 - 1)
        * (z * (Real.exp (-A) * Real.log z + (Real.exp 1)^2 * Real.log 2))
    + (Real.log (Real.log z) + 2)
        * (z * (16 * Real.log 2 + 16 * Real.log 4))

set_option maxHeartbeats 1600000 in
open Real Finset in
/-- **The sharp Halász Riesz mean, windowed** (Track R, T0-4): the §3
window destructured (`exists_section3_window_shell`), the split index
chosen as `K₁ := min(K₀, ⌈A⌉₊)`, and every window quantity priced in
`x` and `A` alone: `K₁ ≤ A + 1`, `K₁ ≤ K₀ ≤ loglog x`,
`√((e^π)²10¹⁵(b²+1)) ≤ √((e^π)²10¹⁵)·(b+1)`, and
`e^{−K₁}·log x ≤ e^{−A}·log x + e²·log 2` (the second alternative when
`⌈A⌉ > K₀`, from the window's `e^{−(K₀+1)}·log x < e·log 2`). -/
theorem rieszMeanC_log_sharp_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (x : ℕ) (hx : 10^16 ≤ x)
    (A : ℝ) (hA : NonPretentiousAt f A x) (h1A : 1 ≤ A)
    (hband : 7 * (((halaszM x : ℕ):ℝ) + 1) ≤ A * (x:ℝ)) :
    ‖(∑ n ∈ Finset.Icc 1 x, f n * ((Real.log (x:ℝ) - Real.log (n:ℝ) : ℝ) : ℂ))
        * ((Real.log (x:ℝ) : ℝ) : ℂ)‖
      ≤ halaszBudgetSharp A (x:ℝ) := by
  classical
  obtain ⟨y, K₀, hy2, hyx, hy, hylog, hK₀1, hK₀low, hK₀max⟩ :=
    exists_section3_window_shell x hx
  have hK₁ : min K₀ ⌈A⌉₊ ≤ K₀ := min_le_left _ _
  have hcap := rieszMeanC_log_le_sharp_halasz_of_nonPretentious f hf hcm h1
    x y K₀ (min K₀ ⌈A⌉₊) hx hy2 hyx hy hK₀1 hK₀low hK₀max hK₁ A hA h1A hband
  refine le_trans hcap ?_
  unfold halaszBudgetSharp
  -- shared numerics
  have hxR0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
  have hL0 : (0:ℝ) < Real.log (x:ℝ) :=
    Real.log_pos (by exact_mod_cast (by
      have : (2:ℕ) ≤ x := le_trans (by norm_num) hx
      omega : (1:ℕ) < x))
  have hlog4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hA0 : (0:ℝ) ≤ A := by linarith
  have he1nn : (0:ℝ) ≤ Real.exp 1 - 1 := by
    linarith [Real.add_one_le_exp (1:ℝ)]
  -- (i) the head scale `y`
  have hy0 : (0:ℝ) < (y:ℝ) := by exact_mod_cast (by omega : 0 < y)
  have hylog' : Real.log (y:ℝ) ≤ Real.log (2*(Real.log (x:ℝ))^2) :=
    Real.log_le_log hy0 hylog
  have hyterm : (x:ℝ)*(Real.log (y:ℝ) + 2)
      ≤ (x:ℝ)*(Real.log (2*(Real.log (x:ℝ))^2) + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hxR0
  -- (ii) `K₀ ≤ loglog x`
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
  have hK₁le : ((min K₀ ⌈A⌉₊ : ℕ):ℝ) ≤ Real.log (Real.log (x:ℝ)) :=
    le_trans (by exact_mod_cast hK₁) hK₀le
  have hK₁A : ((min K₀ ⌈A⌉₊ : ℕ):ℝ) ≤ A + 1 := by
    have h1' : ((min K₀ ⌈A⌉₊ : ℕ):ℝ) ≤ ((⌈A⌉₊ : ℕ):ℝ) := by
      exact_mod_cast (min_le_right _ _)
    have h2' : ((⌈A⌉₊ : ℕ):ℝ) < A + 1 := Nat.ceil_lt_add_one hA0
    linarith
  -- (iii) the square-root split
  set C : ℝ := (Real.exp π)^2 * 10^15 with hC_def
  set b : ℝ := Real.exp 5 * (2 + Real.log (x:ℝ)) * Real.exp (-A) with hb_def
  have hC0 : (0:ℝ) ≤ C := by positivity
  have hb0 : (0:ℝ) ≤ b := by
    have h2L : (0:ℝ) ≤ 2 + Real.log (x:ℝ) := by
      have := Real.log_natCast_nonneg x
      linarith
    exact mul_nonneg (mul_nonneg (Real.exp_pos 5).le h2L) (Real.exp_pos (-A)).le
  have hsqC0 : (0:ℝ) ≤ Real.sqrt C := Real.sqrt_nonneg _
  have hsqrt : Real.sqrt (C * (b^2 + 1)) ≤ Real.sqrt C * (b + 1) := by
    have h1' : C * (b^2 + 1) ≤ C * (b+1)^2 := by
      refine mul_le_mul_of_nonneg_left ?_ hC0
      nlinarith
    calc Real.sqrt (C * (b^2 + 1)) ≤ Real.sqrt (C * (b+1)^2) :=
          Real.sqrt_le_sqrt h1'
      _ = Real.sqrt C * Real.sqrt ((b+1)^2) := Real.sqrt_mul hC0 _
      _ = Real.sqrt C * (b+1) := by rw [Real.sqrt_sq (by linarith)]
  have hhead : ((min K₀ ⌈A⌉₊ : ℕ):ℝ)
        * ((x:ℝ) * Real.sqrt (C * (b^2 + 1)) + 2*(x:ℝ)*Real.log 4)
      ≤ (A + 1) * ((x:ℝ) * (Real.sqrt C * b))
        + Real.log (Real.log (x:ℝ)) * ((x:ℝ) * (Real.sqrt C + 2*Real.log 4)) := by
    have hK₁0 : (0:ℝ) ≤ ((min K₀ ⌈A⌉₊ : ℕ):ℝ) := Nat.cast_nonneg _
    have hs : (x:ℝ) * Real.sqrt (C * (b^2 + 1)) + 2*(x:ℝ)*Real.log 4
        ≤ (x:ℝ) * (Real.sqrt C * b) + (x:ℝ) * (Real.sqrt C + 2*Real.log 4) := by
      have := mul_le_mul_of_nonneg_left hsqrt hxR0
      nlinarith
    have hxb0 : (0:ℝ) ≤ (x:ℝ) * (Real.sqrt C * b) :=
      mul_nonneg hxR0 (mul_nonneg hsqC0 hb0)
    have hxc0 : (0:ℝ) ≤ (x:ℝ) * (Real.sqrt C + 2*Real.log 4) :=
      mul_nonneg hxR0 (by linarith)
    calc ((min K₀ ⌈A⌉₊ : ℕ):ℝ)
          * ((x:ℝ) * Real.sqrt (C * (b^2 + 1)) + 2*(x:ℝ)*Real.log 4)
        ≤ ((min K₀ ⌈A⌉₊ : ℕ):ℝ)
          * ((x:ℝ) * (Real.sqrt C * b) + (x:ℝ) * (Real.sqrt C + 2*Real.log 4)) :=
          mul_le_mul_of_nonneg_left hs hK₁0
      _ = ((min K₀ ⌈A⌉₊ : ℕ):ℝ) * ((x:ℝ) * (Real.sqrt C * b))
          + ((min K₀ ⌈A⌉₊ : ℕ):ℝ) * ((x:ℝ) * (Real.sqrt C + 2*Real.log 4)) := by
          ring
      _ ≤ (A + 1) * ((x:ℝ) * (Real.sqrt C * b))
          + Real.log (Real.log (x:ℝ)) * ((x:ℝ) * (Real.sqrt C + 2*Real.log 4)) :=
          add_le_add (mul_le_mul_of_nonneg_right hK₁A hxb0)
            (mul_le_mul_of_nonneg_right hK₁le hxc0)
  -- (iv) the geometric tail: `e^{−K₁}·log x ≤ e^{−A}·log x + e²·log 2`
  have hexpK₁ : Real.exp (-((min K₀ ⌈A⌉₊ : ℕ):ℝ)) * Real.log (x:ℝ)
      ≤ Real.exp (-A) * Real.log (x:ℝ) + (Real.exp 1)^2 * Real.log 2 := by
    have hpos1 : (0:ℝ) ≤ Real.exp (-A) * Real.log (x:ℝ) :=
      mul_nonneg (Real.exp_pos _).le hL0.le
    have hpos2 : (0:ℝ) ≤ (Real.exp 1)^2 * Real.log 2 := by positivity
    rcases Nat.lt_or_ge K₀ ⌈A⌉₊ with hlt | hle
    · have hK₁eq : min K₀ ⌈A⌉₊ = K₀ := min_eq_left hlt.le
      have hs1 : Real.exp 1 * (Real.exp (-((K₀:ℝ)+1)) * Real.log (x:ℝ))
          = Real.exp (-(K₀:ℝ)) * Real.log (x:ℝ) := by
        rw [← mul_assoc, ← Real.exp_add]
        rw [show (1:ℝ) + -((K₀:ℝ) + 1) = -(K₀:ℝ) by ring]
      have hs2 : Real.exp (-(K₀:ℝ)) * Real.log (x:ℝ)
          ≤ Real.exp 1 * (Real.exp 1 * Real.log 2) := by
        rw [← hs1]
        exact mul_le_mul_of_nonneg_left hK₀max.le (Real.exp_pos 1).le
      rw [hK₁eq]
      nlinarith [hs2, hpos1]
    · have hK₁eq : min K₀ ⌈A⌉₊ = ⌈A⌉₊ := min_eq_right hle
      have hAle : A ≤ ((min K₀ ⌈A⌉₊ : ℕ):ℝ) := by
        rw [hK₁eq]
        exact Nat.le_ceil A
      have hexp : Real.exp (-((min K₀ ⌈A⌉₊ : ℕ):ℝ)) ≤ Real.exp (-A) :=
        Real.exp_le_exp.mpr (by linarith)
      have := mul_le_mul_of_nonneg_right hexp hL0.le
      linarith
  have htail1 : 16 * (Real.exp 1 - 1) * (x:ℝ) * Real.log (x:ℝ)
        * Real.exp (-((min K₀ ⌈A⌉₊ : ℕ):ℝ))
      ≤ 16 * (Real.exp 1 - 1)
        * ((x:ℝ) * (Real.exp (-A) * Real.log (x:ℝ) + (Real.exp 1)^2 * Real.log 2)) := by
    have hc0 : (0:ℝ) ≤ 16 * (Real.exp 1 - 1) * (x:ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) he1nn) hxR0
    have := mul_le_mul_of_nonneg_left hexpK₁ hc0
    calc 16 * (Real.exp 1 - 1) * (x:ℝ) * Real.log (x:ℝ)
          * Real.exp (-((min K₀ ⌈A⌉₊ : ℕ):ℝ))
        = 16 * (Real.exp 1 - 1) * (x:ℝ)
          * (Real.exp (-((min K₀ ⌈A⌉₊ : ℕ):ℝ)) * Real.log (x:ℝ)) := by ring
      _ ≤ 16 * (Real.exp 1 - 1) * (x:ℝ)
          * (Real.exp (-A) * Real.log (x:ℝ) + (Real.exp 1)^2 * Real.log 2) := this
      _ = 16 * (Real.exp 1 - 1)
          * ((x:ℝ) * (Real.exp (-A) * Real.log (x:ℝ) + (Real.exp 1)^2 * Real.log 2)) := by
          ring
  -- (v) the floor of the trivial tail: `K₀ + 2 − K₁ ≤ loglog x + 2`
  have hcardle : ((K₀ + 2 - min K₀ ⌈A⌉₊ : ℕ):ℝ) ≤ Real.log (Real.log (x:ℝ)) + 2 := by
    have h1' : ((K₀ + 2 - min K₀ ⌈A⌉₊ : ℕ):ℝ) ≤ ((K₀ + 2 : ℕ):ℝ) := by
      exact_mod_cast Nat.sub_le _ _
    have h2' : ((K₀ + 2 : ℕ):ℝ) = (K₀:ℝ) + 2 := by push_cast; ring
    linarith
  have hfl0 : (0:ℝ) ≤ (x:ℝ) * (16 * Real.log 2 + 16 * Real.log 4) :=
    mul_nonneg hxR0 (by linarith)
  have htail2 := mul_le_mul_of_nonneg_right hcardle hfl0
  linarith [hyterm, hhead, htail1, htail2]

open Real Finset in
/-- **The sharp plain-sum Halász bound** (Track R, T0-4): for
`10¹⁶ ≤ x ≤ X` and `f` completely multiplicative, `1`-bounded,
non-pretentious at strength `A ≥ 1` at both scales,

  `‖∑_{n≤x} f(n)‖·(log X − log x) ≤ Ĥ⁺(A,X)/log X + Ĥ⁺(A,x)/log x + (X−x)·(log X − log x)`.

The exact mirror of `plain_sumC_le_halaszBudgetShell` at the sharp budget:
in the dominant regime `Ĥ⁺(A,z)/(z log z) ≍ (A+1)e^{−A}` with no
`loglog z`, so at a fixed strength the two-scale differencing at
`log(X/x) ≍ √((A+1)e^{−A})` yields a saving `≍ √(A+1)·e^{−A/2}` **uniform
in the scale** — the fixed-strength Halász input of the `𝒯₀` leg. -/
theorem plain_sumC_le_halaszBudgetSharp (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hcm : CompletelyMultiplicativeC f)
    (h1 : f 1 = 1)
    (x X : ℕ) (hx : 10^16 ≤ x) (hxX : x ≤ X)
    (A : ℝ) (h1A : 1 ≤ A)
    (hAx : NonPretentiousAt f A x)
    (hAX : NonPretentiousAt f A X) :
    ‖∑ n ∈ Finset.Icc 1 x, f n‖ * (Real.log (X:ℝ) - Real.log (x:ℝ))
      ≤ halaszBudgetSharp A (X:ℝ) / Real.log (X:ℝ)
        + halaszBudgetSharp A (x:ℝ) / Real.log (x:ℝ)
        + ((X:ℝ) - (x:ℝ)) * (Real.log (X:ℝ) - Real.log (x:ℝ)) := by
  have hX : 10^16 ≤ X := le_trans hx hxX
  have hx2 : 2 ≤ x := le_trans (by norm_num) hx
  have hRx := rieszMeanC_log_sharp_le f hf hcm h1 x hx A hAx h1A
    (halaszM_band_le x hx A h1A)
  have hRX := rieszMeanC_log_sharp_le f hf hcm h1 X hX A hAX h1A
    (halaszM_band_le X hX A h1A)
  exact plain_sumC_le_of_riesz_bounds f hf x X hx2 hxX _ _ hRx hRX

/-- **The sharp budget is nonnegative** past `z = e` for `A ≥ 0`
(Track R, T0-4): every summand is a product of nonnegative factors once
`log z ≥ 1`. -/
theorem halaszBudgetSharp_nonneg (A z : ℝ) (hA : 0 ≤ A) (hz : Real.exp 1 ≤ z) :
    0 ≤ halaszBudgetSharp A z := by
  have hz0 : (0:ℝ) < z := lt_of_lt_of_le (Real.exp_pos 1) hz
  have hlog1 : (1:ℝ) ≤ Real.log z := by
    rw [Real.le_log_iff_exp_le hz0]
    exact hz
  have hloglog0 : (0:ℝ) ≤ Real.log (Real.log z) := Real.log_nonneg hlog1
  have hlog4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogsq0 : (0:ℝ) ≤ Real.log (2*(Real.log z)^2) :=
    Real.log_nonneg (by nlinarith)
  have he1nn : (0:ℝ) ≤ Real.exp 1 - 1 := by
    linarith [Real.add_one_le_exp (1:ℝ)]
  have hsq0 : (0:ℝ) ≤ Real.sqrt ((Real.exp Real.pi)^2 * 10^15) := Real.sqrt_nonneg _
  have h1 : (0:ℝ) ≤ 35*z := by positivity
  have h2 : (0:ℝ) ≤ z*(Real.log (2*(Real.log z)^2) + 2) :=
    mul_nonneg hz0.le (by linarith)
  have h3 : (0:ℝ) ≤ 2*(z+1)*Real.log 4 := mul_nonneg (by positivity) hlog4
  have h4 : (0:ℝ) ≤ 64 * z * (12 * Real.log (Real.log z) + 18) :=
    mul_nonneg (by positivity) (by linarith)
  have h5 : (0:ℝ) ≤ (A + 1) * (z * (Real.sqrt ((Real.exp Real.pi)^2 * 10^15)
      * (Real.exp 5 * (2 + Real.log z) * Real.exp (-A)))) :=
    mul_nonneg (by linarith) (mul_nonneg hz0.le (mul_nonneg hsq0
      (mul_nonneg (mul_nonneg (Real.exp_pos 5).le (by linarith)) (Real.exp_pos _).le)))
  have h6 : (0:ℝ) ≤ Real.log (Real.log z)
      * (z * (Real.sqrt ((Real.exp Real.pi)^2 * 10^15) + 2*Real.log 4)) :=
    mul_nonneg hloglog0 (mul_nonneg hz0.le (by linarith))
  have h7 : (0:ℝ) ≤ 16 * (Real.exp 1 - 1)
      * (z * (Real.exp (-A) * Real.log z + (Real.exp 1)^2 * Real.log 2)) :=
    mul_nonneg (mul_nonneg (by norm_num) he1nn) (mul_nonneg hz0.le
      (add_nonneg (mul_nonneg (Real.exp_pos _).le (by linarith)) (by positivity)))
  have h8 : (0:ℝ) ≤ (Real.log (Real.log z) + 2)
      * (z * (16 * Real.log 2 + 16 * Real.log 4)) :=
    mul_nonneg (by linarith) (mul_nonneg hz0.le (by linarith))
  unfold halaszBudgetSharp
  linarith

open Real in
/-- **The sharp budget is monotone in the scale** (Track R, T0-4): for
`A ≥ 0` and `e ≤ z ≤ Z`, `Ĥ⁺(A,z) ≤ Ĥ⁺(A,Z)` — every summand is a product
of nonnegative factors each nondecreasing in the scale.  As for the shell
budget, this lets a single budget at the top scale majorize every initial
segment of a window. -/
theorem halaszBudgetSharp_mono (A z Z : ℝ) (hA : 0 ≤ A) (hz : Real.exp 1 ≤ z)
    (hzZ : z ≤ Z) :
    halaszBudgetSharp A z ≤ halaszBudgetSharp A Z := by
  have hz0 : (0:ℝ) < z := lt_of_lt_of_le (Real.exp_pos 1) hz
  have hZ0 : (0:ℝ) < Z := lt_of_lt_of_le hz0 hzZ
  have hlog1 : (1:ℝ) ≤ Real.log z := (Real.le_log_iff_exp_le hz0).mpr hz
  have hlogz0 : (0:ℝ) < Real.log z := lt_of_lt_of_le one_pos hlog1
  have hlogzZ : Real.log z ≤ Real.log Z := Real.log_le_log hz0 hzZ
  have hlogZ0 : (0:ℝ) < Real.log Z := lt_of_lt_of_le hlogz0 hlogzZ
  have hloglogzZ : Real.log (Real.log z) ≤ Real.log (Real.log Z) :=
    Real.log_le_log hlogz0 hlogzZ
  have hlogsum : (0:ℝ) ≤ 2 + Real.log z := by linarith
  have hsqz0 : (0:ℝ) < 2*(Real.log z)^2 := by nlinarith
  have hlogsqzZ : Real.log (2*(Real.log z)^2) ≤ Real.log (2*(Real.log Z)^2) := by
    refine Real.log_le_log hsqz0 ?_
    nlinarith
  have hlogsq0 : (0:ℝ) ≤ Real.log (2*(Real.log z)^2) :=
    Real.log_nonneg (by nlinarith)
  have hloglogZ0 : (0:ℝ) ≤ Real.log (Real.log Z) :=
    Real.log_nonneg (le_trans hlog1 hlogzZ)
  have hloglog0z : (0:ℝ) ≤ Real.log (Real.log z) := Real.log_nonneg hlog1
  have hlog4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have he1nn : (0:ℝ) ≤ Real.exp 1 - 1 := by
    linarith [Real.add_one_le_exp (1:ℝ)]
  have hA1 : (0:ℝ) ≤ A + 1 := by linarith
  have hsq0 : (0:ℝ) ≤ Real.sqrt ((Real.exp Real.pi)^2 * 10^15) := Real.sqrt_nonneg _
  unfold halaszBudgetSharp
  gcongr

end MoltResearch
