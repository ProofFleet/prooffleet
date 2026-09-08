import MoltResearch.Discrepancy.VinogradovWeylSum
import MoltResearch.Discrepancy.ZetaBound
import MoltResearch.Discrepancy.ZetaGrowthRegion
import MoltResearch.Discrepancy.HalaszMontgomeryLargeValues

/-!
# The zeta growth bound from Vinogradov's Weyl-sum estimate

This leaf converts the logarithmic Weyl-sum estimate into the power-type
growth input used by the parametrized zero-free-region argument.  The loss
`log³ (2 * lambda)` is first absorbed into `lambda^(1/10)`; optimizing the
resulting saving gives exponent `41/31`, with enough room for the stable
exponent `33/25`.
-/

namespace MoltResearch

namespace ExpSums

open Complex

/-! ## Partial summation on one block -/

/-- The sign of the height is immaterial in the unweighted Vinogradov block
estimate. -/
theorem norm_log_phase_Ioc_le_of_vinogradov
    {c C : ℝ}
    (hweyl : ∀ (N : ℕ) (T : ℝ), 2 ≤ N → (N : ℝ) ≤ T →
      ∀ (u : ℝ) (R : ℕ), 0 ≤ u → u ≤ 1 → N < R → R ≤ 2 * N →
        ‖∑ n ∈ Finset.Ioc N R,
            ((n : ℝ) + u : ℂ) ^ (-(T : ℂ) * I)‖ ≤
          C * (N : ℝ) ^
            (1 - c / ((Real.log T / Real.log N) ^ 3 *
              Real.log (2 * (Real.log T / Real.log N)) ^ 3)))
    (N R : ℕ) (t : ℝ) (hN : 2 ≤ N) (hNt : (N : ℝ) ≤ |t|)
    (hNR : N < R) (hR : R ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc N R,
        e (-(t / (2 * Real.pi) * Real.log n))‖ ≤
      C * (N : ℝ) ^
        (1 - c / ((Real.log |t| / Real.log N) ^ 3 *
          Real.log (2 * (Real.log |t| / Real.log N)) ^ 3)) := by
  have hT0 : 0 < |t| := lt_of_lt_of_le (by
    exact_mod_cast (show 0 < N by omega)) hNt
  have hbase := hweyl N |t| hN hNt 0 R (by norm_num) (by norm_num) hNR hR
  have hconvert :
      (∑ n ∈ Finset.Ioc N R,
          (((n : ℝ) : ℂ) + ((0 : ℝ) : ℂ)) ^
            (-((|t| : ℝ) : ℂ) * I)) =
        ∑ n ∈ Finset.Ioc N R,
          e (-(|t| / (2 * Real.pi) * Real.log n)) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Ioc] at hn
    simpa using
      (VinogradovWeylSum.cpow_neg_mul_I_eq_e_log
        (t := |t|) (show (0 : ℝ) < (n : ℝ) + 0 by
          exact_mod_cast (show 0 < n by omega)))
  rw [hconvert] at hbase
  rcases le_total 0 t with ht | ht
  · simpa [abs_of_nonneg ht] using hbase
  · have ht' : t ≤ 0 := ht
    have habs : |t| = -t := abs_of_nonpos ht'
    calc
      ‖∑ n ∈ Finset.Ioc N R,
          e (-(t / (2 * Real.pi) * Real.log n))‖ =
          ‖∑ n ∈ Finset.Ioc N R,
            (1 : ℝ) • e (-t / (2 * Real.pi) * Real.log n)‖ := by
        congr 1
        apply Finset.sum_congr rfl
        intro n _
        simp only [one_smul]
        congr 1
        ring
      _ = ‖∑ n ∈ Finset.Ioc N R,
            (1 : ℝ) • e (-(-t / (2 * Real.pi) * Real.log n))‖ :=
        norm_sum_smul_e_neg _ (fun _ => 1)
          (fun n => -t / (2 * Real.pi) * Real.log n)
      _ = ‖∑ n ∈ Finset.Ioc N R,
            e (-(-t / (2 * Real.pi) * Real.log n))‖ := by simp
      _ ≤ _ := by simpa [habs] using hbase

/-- Abel summation against `n^(-sigma)` transfers the unweighted Weyl
estimate to a zeta block.  The factor `2` is a deliberately round endpoint
allowance. -/
theorem norm_sum_cpow_Ioc_le_of_vinogradov
    {c C : ℝ} (hC : 0 < C)
    (hweyl : ∀ (N : ℕ) (T : ℝ), 2 ≤ N → (N : ℝ) ≤ T →
      ∀ (u : ℝ) (R : ℕ), 0 ≤ u → u ≤ 1 → N < R → R ≤ 2 * N →
        ‖∑ n ∈ Finset.Ioc N R,
            ((n : ℝ) + u : ℂ) ^ (-(T : ℂ) * I)‖ ≤
          C * (N : ℝ) ^
            (1 - c / ((Real.log T / Real.log N) ^ 3 *
              Real.log (2 * (Real.log T / Real.log N)) ^ 3)))
    (N R : ℕ) (sigma t : ℝ) (hsigma : 0 ≤ sigma)
    (hN : 2 ≤ N) (hNt : (N : ℝ) ≤ |t|) (hNR : N ≤ R)
    (hR : R ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc N R,
        ((n : ℕ) : ℂ) ^ (-((sigma : ℂ) + I * t))‖ ≤
      2 * C * (N : ℝ) ^
        (1 - sigma - c / ((Real.log |t| / Real.log N) ^ 3 *
          Real.log (2 * (Real.log |t| / Real.log N)) ^ 3)) := by
  rcases eq_or_lt_of_le hNR with rfl | hNR
  · simp
    positivity
  let E : ℝ := C * (N : ℝ) ^
    (1 - c / ((Real.log |t| / Real.log N) ^ 3 *
      Real.log (2 * (Real.log |t| / Real.log N)) ^ 3))
  let w : ℕ → ℝ := fun n => (n : ℝ) ^ (-sigma)
  let a : ℕ → ℂ := fun n => e (-(t / (2 * Real.pi) * Real.log n))
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hw0 : ∀ n, N + 1 ≤ n → n ≤ R → 0 ≤ w n := by
    intro n _ _
    dsimp only [w]
    positivity
  have hwanti : ∀ n, N + 1 ≤ n → n < R → w (n + 1) ≤ w n := by
    intro n hn _
    dsimp only [w]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hpow : (n : ℝ) ^ sigma ≤ ((n + 1 : ℕ) : ℝ) ^ sigma := by
      apply Real.rpow_le_rpow (by positivity)
      · push_cast
        linarith
      · exact hsigma
    rw [Real.rpow_neg hn0.le, Real.rpow_neg (by positivity),
      inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) hpow
  have hpartial : ∀ P, N + 1 ≤ P → P ≤ R + 1 →
      ‖∑ n ∈ Finset.Ico (N + 1) P, a n‖ ≤ E := by
    intro P hNP hPR
    rcases eq_or_lt_of_le hNP with rfl | hNP'
    · simpa using hE0
    · have hQ : N < P - 1 := by omega
      have hQR : P - 1 ≤ R := by omega
      have hQ2 : P - 1 ≤ 2 * N := hQR.trans hR
      have hset : Finset.Ico (N + 1) P = Finset.Ioc N (P - 1) := by
        ext n
        simp only [Finset.mem_Ico, Finset.mem_Ioc]
        omega
      rw [hset]
      exact norm_log_phase_Ioc_le_of_vinogradov hweyl N (P - 1) t hN hNt hQ hQ2
  have habel := abel_weight_bound (M := N + 1) (N := R) (E := E)
    (w := w) (a := a) (by omega) hw0 hwanti hpartial
  have hfactor : ∀ n ∈ Finset.Ioc N R,
      ((n : ℕ) : ℂ) ^ (-((sigma : ℂ) + I * t)) = w n • a n := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hphase := cpow_neg_eq_smul_e sigma (-t) n (by omega)
    dsimp only [w, a]
    rw [show -(t / (2 * Real.pi) * Real.log n) =
      -t / (2 * Real.pi) * Real.log n by ring]
    convert hphase using 1
    push_cast
    ring
  have hsum :
      (∑ n ∈ Finset.Ioc N R,
          ((n : ℕ) : ℂ) ^ (-((sigma : ℂ) + I * t))) =
        ∑ n ∈ Finset.Ico (N + 1) (R + 1), w n • a n := by
    rw [show Finset.Ioc N R = Finset.Ico (N + 1) (R + 1) by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega]
    exact Finset.sum_congr rfl fun n hn => hfactor n (by
      rw [Finset.mem_Ioc]
      rw [Finset.mem_Ico] at hn
      omega)
  rw [hsum]
  have hlead : w (N + 1) ≤ (N : ℝ) ^ (-sigma) := by
    dsimp only [w]
    have hpow : (N : ℝ) ^ sigma ≤ ((N + 1 : ℕ) : ℝ) ^ sigma := by
      apply Real.rpow_le_rpow (by positivity)
      · push_cast
        linarith
      · exact hsigma
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity),
      inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) hpow
  have hfirst : ‖∑ n ∈ Finset.Ico (N + 1) (R + 1), w n • a n‖ ≤
      (N : ℝ) ^ (-sigma) * E :=
    habel.trans (mul_le_mul_of_nonneg_right hlead hE0)
  have hN0 : (0 : ℝ) < N := by positivity
  have hcombine : (N : ℝ) ^ (-sigma) * E =
      C * (N : ℝ) ^
        (1 - sigma - c / ((Real.log |t| / Real.log N) ^ 3 *
          Real.log (2 * (Real.log |t| / Real.log N)) ^ 3)) := by
    dsimp only [E]
    calc
      (N : ℝ) ^ (-sigma) *
          (C * (N : ℝ) ^
            (1 - c / ((Real.log |t| / Real.log N) ^ 3 *
              Real.log (2 * (Real.log |t| / Real.log N)) ^ 3))) =
          C * ((N : ℝ) ^ (-sigma) *
            (N : ℝ) ^
              (1 - c / ((Real.log |t| / Real.log N) ^ 3 *
                Real.log (2 * (Real.log |t| / Real.log N)) ^ 3))) := by ring
      _ = C * (N : ℝ) ^
          (-sigma + (1 - c / ((Real.log |t| / Real.log N) ^ 3 *
            Real.log (2 * (Real.log |t| / Real.log N)) ^ 3))) := by
          rw [Real.rpow_add hN0]
      _ = _ := by congr 1; ring
  rw [hcombine] at hfirst
  exact hfirst.trans (by
    have hpow0 : 0 ≤ (N : ℝ) ^
        (1 - sigma - c / ((Real.log |t| / Real.log N) ^ 3 *
          Real.log (2 * (Real.log |t| / Real.log N)) ^ 3)) := by positivity
    nlinarith)

/-! ## Optimizing the weakened saving -/

/-- Three powers of the logarithmic loss cost only `lambda^(1/10)`. -/
theorem log_two_mul_cube_le_rpow (lambda : ℝ) (hlambda : 1 ≤ lambda) :
    Real.log (2 * lambda) ^ 3 ≤
      54000 * lambda ^ (1 / 10 : ℝ) := by
  have hx0 : 0 ≤ 2 * lambda := by positivity
  have hx1 : 1 ≤ 2 * lambda := by linarith
  have hlog0 : 0 ≤ Real.log (2 * lambda) := Real.log_nonneg hx1
  have hraw := Real.log_le_rpow_div hx0
    (show (0 : ℝ) < 1 / 30 by norm_num)
  have hlog : Real.log (2 * lambda) ≤
      30 * (2 * lambda) ^ (1 / 30 : ℝ) := by
    calc
      Real.log (2 * lambda) ≤
          (2 * lambda) ^ (1 / 30 : ℝ) / (1 / 30) := hraw
      _ = 30 * (2 * lambda) ^ (1 / 30 : ℝ) := by ring
  have hcubed := pow_le_pow_left₀ hlog0 hlog 3
  have hrpow : ((2 * lambda) ^ (1 / 30 : ℝ)) ^ (3 : ℕ) =
      (2 * lambda) ^ (1 / 10 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  have hsplit : (2 * lambda) ^ (1 / 10 : ℝ) =
      2 ^ (1 / 10 : ℝ) * lambda ^ (1 / 10 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) (by linarith)]
  have htwo : 2 ^ (1 / 10 : ℝ) ≤ (2 : ℝ) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show (1 / 10 : ℝ) ≤ 1 by norm_num))
  calc
    Real.log (2 * lambda) ^ 3 ≤
        (30 * (2 * lambda) ^ (1 / 30 : ℝ)) ^ 3 := hcubed
    _ = 27000 * (2 * lambda) ^ (1 / 10 : ℝ) := by
      rw [mul_pow, hrpow]
      norm_num
    _ = 27000 * (2 ^ (1 / 10 : ℝ) * lambda ^ (1 / 10 : ℝ)) := by
      rw [hsplit]
    _ ≤ 54000 * lambda ^ (1 / 10 : ℝ) := by
      have hnonneg : 0 ≤ lambda ^ (1 / 10 : ℝ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right htwo hnonneg]

/-- The elementary two-case optimization.  The intermediate exponent is
`41/31`; monotonicity on `[0,1]` then leaves the requested `33/25`. -/
theorem vinogradov_saving_optimization (c delta lambda : ℝ)
    (hc : 0 < c) (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hlambda : 1 ≤ lambda) :
    delta / lambda -
        c / (lambda ^ 4 * Real.log (2 * lambda) ^ 3) ≤
      (c / 54000) ^ (-10 / 31 : ℝ) * delta ^ (33 / 25 : ℝ) := by
  let d : ℝ := c / 54000
  have hd : 0 < d := by dsimp only [d]; positivity
  have hlam0 : 0 < lambda := lt_of_lt_of_le zero_lt_one hlambda
  have hlog0 : 0 < Real.log (2 * lambda) := Real.log_pos (by linarith)
  have hloss := log_two_mul_cube_le_rpow lambda hlambda
  have hdenom : lambda ^ 4 * Real.log (2 * lambda) ^ 3 ≤
      54000 * lambda ^ (41 / 10 : ℝ) := by
    have hlam4 : 0 ≤ lambda ^ 4 := by positivity
    calc
      lambda ^ 4 * Real.log (2 * lambda) ^ 3 ≤
          lambda ^ 4 * (54000 * lambda ^ (1 / 10 : ℝ)) :=
        mul_le_mul_of_nonneg_left hloss hlam4
      _ = 54000 * lambda ^ (41 / 10 : ℝ) := by
        calc
          lambda ^ 4 * (54000 * lambda ^ (1 / 10 : ℝ)) =
              54000 * (lambda ^ 4 * lambda ^ (1 / 10 : ℝ)) := by ring
          _ = 54000 * (lambda ^ (4 : ℝ) *
              lambda ^ (1 / 10 : ℝ)) := by
            norm_num [Real.rpow_natCast]
          _ = 54000 * lambda ^ ((4 : ℝ) + 1 / 10) := by
            rw [Real.rpow_add hlam0]
          _ = _ := by norm_num
  have hdenom0 : 0 < lambda ^ 4 * Real.log (2 * lambda) ^ 3 := by positivity
  have hlargeDenom0 : 0 < 54000 * lambda ^ (41 / 10 : ℝ) := by positivity
  have hsaving : d / lambda ^ (41 / 10 : ℝ) ≤
      c / (lambda ^ 4 * Real.log (2 * lambda) ^ 3) := by
    have hdiv := div_le_div_of_nonneg_left hc.le hdenom0 hdenom
    dsimp only [d]
    calc
      c / 54000 / lambda ^ (41 / 10 : ℝ) =
          c / (54000 * lambda ^ (41 / 10 : ℝ)) := by ring
      _ ≤ _ := hdiv
  have hreduce :
      delta / lambda -
          c / (lambda ^ 4 * Real.log (2 * lambda) ^ 3) ≤
        delta / lambda - d / lambda ^ (41 / 10 : ℝ) := by linarith
  refine hreduce.trans ?_
  by_cases hcase : delta * lambda ^ (31 / 10 : ℝ) ≤ d
  · have hpow : lambda ^ (41 / 10 : ℝ) =
        lambda ^ (31 / 10 : ℝ) * lambda := by
      calc
        lambda ^ (41 / 10 : ℝ) = lambda ^ ((31 / 10 : ℝ) + 1) := by norm_num
        _ = lambda ^ (31 / 10 : ℝ) * lambda ^ (1 : ℝ) :=
          Real.rpow_add hlam0 _ _
        _ = _ := by rw [Real.rpow_one]
    have hquot : delta / lambda ≤ d / lambda ^ (41 / 10 : ℝ) := by
      rw [hpow]
      rw [div_le_div_iff₀ hlam0
        (mul_pos (Real.rpow_pos_of_pos hlam0 _) hlam0)]
      have hmul := mul_le_mul_of_nonneg_right hcase hlam0.le
      nlinarith
    have hright0 : 0 ≤ d ^ (-10 / 31 : ℝ) * delta ^ (33 / 25 : ℝ) := by
      positivity
    linarith
  · have hstrict : d < delta * lambda ^ (31 / 10 : ℝ) := lt_of_not_ge hcase
    have hdelta : 0 < delta := by
      by_contra h
      have : delta = 0 := le_antisymm (not_lt.mp h) hdelta0
      subst delta
      simp at hstrict
      exact (not_lt_of_ge hd.le) hstrict
    have hratio : d / delta < lambda ^ (31 / 10 : ℝ) := by
      rw [div_lt_iff₀ hdelta]
      simpa [mul_comm] using hstrict
    have hroot := Real.rpow_lt_rpow (by positivity : 0 ≤ d / delta) hratio
      (show (0 : ℝ) < 10 / 31 by norm_num)
    have hrootEq : (lambda ^ (31 / 10 : ℝ)) ^ (10 / 31 : ℝ) = lambda := by
      rw [← Real.rpow_mul hlam0.le]
      norm_num
    rw [hrootEq] at hroot
    have hrecip : delta / lambda ≤ delta / (d / delta) ^ (10 / 31 : ℝ) := by
      exact div_le_div_of_nonneg_left hdelta0 (Real.rpow_pos_of_pos (by positivity) _)
        hroot.le
    have heq : delta / (d / delta) ^ (10 / 31 : ℝ) =
        d ^ (-10 / 31 : ℝ) * delta ^ (41 / 31 : ℝ) := by
      rw [Real.div_rpow hd.le hdelta.le]
      rw [show (-10 / 31 : ℝ) = -(10 / 31) by ring,
        Real.rpow_neg hd.le]
      rw [show (41 / 31 : ℝ) = 1 + 10 / 31 by norm_num,
        Real.rpow_add hdelta]
      field_simp
      rw [Real.rpow_one]
    have hpower : delta ^ (41 / 31 : ℝ) ≤ delta ^ (33 / 25 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_ge hdelta hdelta1 (by norm_num)
    have hcoeff0 : 0 ≤ d ^ (-10 / 31 : ℝ) := by positivity
    calc
      delta / lambda - d / lambda ^ (41 / 10 : ℝ) ≤ delta / lambda := by
        have : 0 ≤ d / lambda ^ (41 / 10 : ℝ) := by positivity
        linarith
      _ ≤ delta / (d / delta) ^ (10 / 31 : ℝ) := hrecip
      _ = d ^ (-10 / 31 : ℝ) * delta ^ (41 / 31 : ℝ) := heq
      _ ≤ d ^ (-10 / 31 : ℝ) * delta ^ (33 / 25 : ℝ) :=
        mul_le_mul_of_nonneg_left hpower hcoeff0

/-! ## The long truncation and its two block ranges -/

/-- The norm estimate for the analytic tail in `zeta_afe_strip`, extracted
in a reusable form. -/
theorem norm_zTail_le_strip (s : ℂ) (N : ℕ)
    (hsigma : 0 < s.re) (hs1 : 1 ≤ ‖s - 1‖)
    (hN : 2 * ‖s - 1‖ ≤ N) (hN2 : 2 ≤ N) :
    ‖zTail s N‖ ≤
      2 * ‖s - 1‖ * (((N : ℕ) : ℝ) - 1) ^ (-s.re) / s.re := by
  have hsum := summable_zTail_terms s N hsigma hs1 hN hN2
  have hnorm : ‖zTail s N‖ ≤ ∑' k : ℕ,
      ‖(((N + k : ℕ)) : ℂ) ^ (-s) -
        (zPot s (N + k) - zPot s (N + k + 1))‖ := by
    rw [zTail]
    exact norm_tsum_le_tsum_norm hsum
  have hdomsum : Summable (fun k : ℕ =>
      2 * ‖s - 1‖ * (((N + k : ℕ)) : ℝ) ^ (-(1 + s.re))) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-(1 + s.re))) := by
      rw [show (fun n : ℕ => ((n : ℝ)) ^ (-(1 + s.re))) =
          (fun n : ℕ => 1 / ((n : ℝ)) ^ (1 + s.re)) from funext fun n => by
        rw [Real.rpow_neg (Nat.cast_nonneg n), inv_eq_one_div]]
      exact (Real.summable_one_div_nat_rpow).mpr (by linarith)
    have hshift := (summable_nat_add_iff
      (f := fun n : ℕ => ((n : ℝ)) ^ (-(1 + s.re))) N).mpr hbase
    have hshift' : Summable (fun k : ℕ =>
        (((N + k : ℕ)) : ℝ) ^ (-(1 + s.re))) := by
      refine hshift.congr fun k => ?_
      congr 2
      ring
    exact hshift'.mul_left _
  have hdom : ∑' k : ℕ,
      ‖(((N + k : ℕ)) : ℂ) ^ (-s) -
        (zPot s (N + k) - zPot s (N + k + 1))‖ ≤
      ∑' k : ℕ,
        2 * ‖s - 1‖ * (((N + k : ℕ)) : ℝ) ^ (-(1 + s.re)) := by
    refine hsum.tsum_le_tsum (fun k => ?_) hdomsum
    have hnk : ‖s - 1‖ ≤ ((N + k : ℕ) : ℝ) := by
      have ha : ‖s - 1‖ ≤ (N : ℝ) := by
        nlinarith [norm_nonneg (s - 1)]
      have hb : (N : ℝ) ≤ ((N + k : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_add_right N k
      linarith
    refine (cpow_sub_telescope_le_strip s (N + k) hsigma hs1 hnk
      (by omega)).trans_eq ?_
    rw [Real.rpow_neg (Nat.cast_nonneg _), inv_eq_one_div]
    rw [div_eq_mul_one_div]
  have htailSum : ∑' k : ℕ,
      (((N + k : ℕ)) : ℝ) ^ (-(1 + s.re)) ≤
        (((N : ℕ) : ℝ) - 1) ^ (-s.re) / s.re := by
    refine Real.tsum_le_of_sum_range_le (fun k => by positivity) (fun K => ?_)
    have hshift : ∑ k ∈ Finset.range K,
        (((N + k : ℕ)) : ℝ) ^ (-(1 + s.re)) =
      ∑ n ∈ Finset.Ico N (N + K), ((n : ℝ)) ^ (-(1 + s.re)) := by
      rw [Finset.sum_Ico_eq_sum_range]
      have : N + K - N = K := by omega
      rw [this]
    rw [hshift]
    exact sum_rpow_neg_Ico_le s.re N (N + K) hsigma hN2
  calc
    ‖zTail s N‖ ≤ ∑' k : ℕ,
        ‖(((N + k : ℕ)) : ℂ) ^ (-s) -
          (zPot s (N + k) - zPot s (N + k + 1))‖ := hnorm
    _ ≤ ∑' k : ℕ,
        2 * ‖s - 1‖ * (((N + k : ℕ)) : ℝ) ^ (-(1 + s.re)) := hdom
    _ = 2 * ‖s - 1‖ * ∑' k : ℕ,
        (((N + k : ℕ)) : ℝ) ^ (-(1 + s.re)) := tsum_mul_left
    _ ≤ 2 * ‖s - 1‖ *
        ((((N : ℕ) : ℝ) - 1) ^ (-s.re) / s.re) := by
      exact mul_le_mul_of_nonneg_left htailSum (by positivity)
    _ = _ := by ring

/-- Capped dyadic blocks tile one interval. -/
theorem zetaGrowth_sum_dyadic_tiling {M : Type*} [AddCommMonoid M]
    (V N J : ℕ) (f : ℕ → M) :
    ∑ j ∈ Finset.range J,
        ∑ n ∈ Finset.Ioc (min (2 ^ j * V) N)
          (min (2 ^ (j + 1) * V) N), f n =
      ∑ n ∈ Finset.Ioc (min V N) (min (2 ^ J * V) N), f n := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      have hleft : min V N ≤ min (2 ^ J * V) N := by
        refine min_le_min ?_ le_rfl
        calc
          V = 1 * V := (one_mul V).symm
          _ ≤ 2 ^ J * V := Nat.mul_le_mul_right V Nat.one_le_two_pow
      have hright : min (2 ^ J * V) N ≤ min (2 ^ (J + 1) * V) N := by
        refine min_le_min ?_ le_rfl
        exact Nat.mul_le_mul_right V
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J))
      exact Finset.sum_Ioc_consecutive f hleft hright

/-- A low dyadic block after the logarithmic loss has been optimized. -/
theorem norm_sum_cpow_Ioc_le_vinogradov_optimized
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hweyl : ∀ (N : ℕ) (T : ℝ), 2 ≤ N → (N : ℝ) ≤ T →
      ∀ (u : ℝ) (R : ℕ), 0 ≤ u → u ≤ 1 → N < R → R ≤ 2 * N →
        ‖∑ n ∈ Finset.Ioc N R,
            ((n : ℝ) + u : ℂ) ^ (-(T : ℂ) * I)‖ ≤
          C * (N : ℝ) ^
            (1 - c / ((Real.log T / Real.log N) ^ 3 *
              Real.log (2 * (Real.log T / Real.log N)) ^ 3)))
    (N R : ℕ) (sigma t : ℝ) (hsigma0 : 0 ≤ sigma)
    (hsigma1 : sigma ≤ 1) (hN : 2 ≤ N) (hNt : (N : ℝ) ≤ |t|)
    (hNR : N ≤ R) (hR : R ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc N R,
        ((n : ℕ) : ℂ) ^ (-((sigma : ℂ) + I * t))‖ ≤
      2 * C * |t| ^
        ((c / 54000) ^ (-10 / 31 : ℝ) *
          (1 - sigma) ^ (33 / 25 : ℝ)) := by
  have hraw := norm_sum_cpow_Ioc_le_of_vinogradov hC hweyl
    N R sigma t hsigma0 hN hNt hNR hR
  have hN0 : (0 : ℝ) < N := by positivity
  have ht0 : 0 < |t| := lt_of_lt_of_le hN0 hNt
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hlogNt : Real.log (N : ℝ) ≤ Real.log |t| := Real.log_le_log hN0 hNt
  have hlogt0 : 0 < Real.log |t| := lt_of_lt_of_le hlogN hlogNt
  let lambda : ℝ := Real.log |t| / Real.log N
  have hlambda : 1 ≤ lambda := by
    dsimp only [lambda]
    exact (le_div_iff₀ hlogN).2 (by simpa using hlogNt)
  have hlambda0 : 0 < lambda := lt_of_lt_of_le zero_lt_one hlambda
  have hllog : 0 < Real.log (2 * lambda) := Real.log_pos (by linarith)
  have hdelta0 : 0 ≤ 1 - sigma := by linarith
  have hdelta1 : 1 - sigma ≤ 1 := by linarith
  have hopt := vinogradov_saving_optimization c (1 - sigma) lambda
    hc hdelta0 hdelta1 hlambda
  have hlogRelation : Real.log (N : ℝ) * lambda = Real.log |t| := by
    dsimp only [lambda]
    field_simp
  have hexponent :
      Real.log (N : ℝ) *
          (1 - sigma - c / (lambda ^ 3 * Real.log (2 * lambda) ^ 3)) =
        Real.log |t| *
          ((1 - sigma) / lambda -
            c / (lambda ^ 4 * Real.log (2 * lambda) ^ 3)) := by
    rw [← hlogRelation]
    field_simp [ne_of_gt hlambda0, ne_of_gt hllog]
  have hrpow :
      (N : ℝ) ^
          (1 - sigma - c / (lambda ^ 3 * Real.log (2 * lambda) ^ 3)) ≤
        |t| ^ ((c / 54000) ^ (-10 / 31 : ℝ) *
          (1 - sigma) ^ (33 / 25 : ℝ)) := by
    rw [Real.rpow_def_of_pos hN0, Real.rpow_def_of_pos ht0]
    apply Real.exp_monotone
    rw [hexponent]
    exact mul_le_mul_of_nonneg_left hopt hlogt0.le
  dsimp only [lambda] at hrpow
  exact hraw.trans (mul_le_mul_of_nonneg_left hrpow (by positivity))

/-- Kusmin--Landau controls logarithmic phase sums after the lower endpoint
passes the height. -/
theorem norm_log_phase_Ioc_le_kusmin (N R : ℕ) (t : ℝ)
    (ht0 : 0 < |t|) (hN : 1 ≤ N) (hNR : N ≤ R) (hR : R ≤ 2 * N)
    (hlarge : 13 * (|t| / (2 * Real.pi)) ≤ 12 * (N + 1 : ℕ)) :
    ‖∑ n ∈ Finset.Ioc N R,
        e (-(t / (2 * Real.pi) * Real.log n))‖ ≤
      12 * (N + 1 : ℕ) / (|t| / (2 * Real.pi)) := by
  have hv0 : 0 < |t| / (2 * Real.pi) := by positivity
  have hbase := MoltResearch.norm_sum_e_neg_log_Ioc_le_kusmin
    (|t| / (2 * Real.pi)) N R hv0 hN hNR hR hlarge
  rcases le_total 0 t with ht | ht
  · simpa [abs_of_nonneg ht] using hbase
  · have habs : |t| = -t := abs_of_nonpos ht
    calc
      ‖∑ n ∈ Finset.Ioc N R,
          e (-(t / (2 * Real.pi) * Real.log n))‖ =
          ‖∑ n ∈ Finset.Ioc N R,
            (1 : ℝ) • e (-t / (2 * Real.pi) * Real.log n)‖ := by
        congr 1
        apply Finset.sum_congr rfl
        intro n _
        simp only [one_smul]
        congr 1
        ring
      _ = ‖∑ n ∈ Finset.Ioc N R,
            (1 : ℝ) • e (-(-t / (2 * Real.pi) * Real.log n))‖ :=
        norm_sum_smul_e_neg _ (fun _ => 1)
          (fun n => -t / (2 * Real.pi) * Real.log n)
      _ = ‖∑ n ∈ Finset.Ioc N R,
            e (-(-t / (2 * Real.pi) * Real.log n))‖ := by simp
      _ ≤ _ := by simpa [habs] using hbase

/-- Above the height, partial summation and Kusmin--Landau make every
dyadic zeta block absolutely bounded. -/
theorem norm_sum_cpow_Ioc_le_kusmin_two_hundred
    (N R : ℕ) (sigma t : ℝ) (hsigma0 : 0 ≤ sigma)
    (hsigma34 : 3 / 4 ≤ sigma) (hsigma1 : sigma ≤ 1) (ht : 16 ≤ |t|)
    (hTN : |t| ≤ (N + 1 : ℕ)) (hN : 1 ≤ N)
    (hNR : N ≤ R) (hR : R ≤ 2 * N)
    (hNupper : ((N + 1 : ℕ) : ℝ) ≤ 2 * |t| ^ 2) :
    ‖∑ n ∈ Finset.Ioc N R,
        ((n : ℕ) : ℂ) ^ (-((sigma : ℂ) + I * t))‖ ≤ 200 := by
  rcases eq_or_lt_of_le hNR with rfl | hNR
  · simp
  let v : ℝ := |t| / (2 * Real.pi)
  let E : ℝ := 12 * (N + 1 : ℕ) / v
  let w : ℕ → ℝ := fun n => (n : ℝ) ^ (-sigma)
  let a : ℕ → ℂ := fun n => e (-(t / (2 * Real.pi) * Real.log n))
  have ht0 : 0 < |t| := by linarith
  have hv0 : 0 < v := by dsimp only [v]; positivity
  have hlarge : 13 * v ≤ 12 * (N + 1 : ℕ) := by
    have hpi : (6 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hv : v ≤ |t| / 6 := by
      dsimp only [v]
      exact div_le_div_of_nonneg_left (abs_nonneg t) (by norm_num) hpi.le
    have hTN' : |t| ≤ ((N + 1 : ℕ) : ℝ) := hTN
    nlinarith
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hw0 : ∀ n, N + 1 ≤ n → n ≤ R → 0 ≤ w n := by
    intro n _ _
    dsimp only [w]
    positivity
  have hwanti : ∀ n, N + 1 ≤ n → n < R → w (n + 1) ≤ w n := by
    intro n hn _
    dsimp only [w]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hpow : (n : ℝ) ^ sigma ≤ ((n + 1 : ℕ) : ℝ) ^ sigma := by
      apply Real.rpow_le_rpow (by positivity)
      · push_cast
        linarith
      · exact hsigma0
    rw [Real.rpow_neg hn0.le, Real.rpow_neg (by positivity),
      inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) hpow
  have hpartial : ∀ P, N + 1 ≤ P → P ≤ R + 1 →
      ‖∑ n ∈ Finset.Ico (N + 1) P, a n‖ ≤ E := by
    intro P hNP hPR
    rcases eq_or_lt_of_le hNP with rfl | hNP
    · simpa using hE0
    · have hQ : N < P - 1 := by omega
      have hQR : P - 1 ≤ R := by omega
      have hQ2 : P - 1 ≤ 2 * N := hQR.trans hR
      have hset : Finset.Ico (N + 1) P = Finset.Ioc N (P - 1) := by
        ext n
        simp only [Finset.mem_Ico, Finset.mem_Ioc]
        omega
      rw [hset]
      dsimp only [E, v]
      exact norm_log_phase_Ioc_le_kusmin N (P - 1) t ht0 hN hQ.le hQ2
        (by simpa only [v] using hlarge)
  have habel := abel_weight_bound (M := N + 1) (N := R) (E := E)
    (w := w) (a := a) (by omega) hw0 hwanti hpartial
  have hfactor : ∀ n ∈ Finset.Ioc N R,
      ((n : ℕ) : ℂ) ^ (-((sigma : ℂ) + I * t)) = w n • a n := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hphase := cpow_neg_eq_smul_e sigma (-t) n (by omega)
    dsimp only [w, a]
    rw [show -(t / (2 * Real.pi) * Real.log n) =
      -t / (2 * Real.pi) * Real.log n by ring]
    convert hphase using 1
    push_cast
    ring
  have hsum :
      (∑ n ∈ Finset.Ioc N R,
          ((n : ℕ) : ℂ) ^ (-((sigma : ℂ) + I * t))) =
        ∑ n ∈ Finset.Ico (N + 1) (R + 1), w n • a n := by
    rw [show Finset.Ioc N R = Finset.Ico (N + 1) (R + 1) by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega]
    exact Finset.sum_congr rfl fun n hn => hfactor n (by
      rw [Finset.mem_Ioc]
      rw [Finset.mem_Ico] at hn
      omega)
  rw [hsum]
  have hfirst := habel
  have hdelta0 : 0 ≤ 1 - sigma := by linarith
  have hdelta : 1 - sigma ≤ 1 / 4 := by linarith
  have hbase : ((N + 1 : ℕ) : ℝ) ^ (1 - sigma) ≤ 2 * |t| := by
    have hN1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ N + 1 by omega)
    have hmonoExp := Real.rpow_le_rpow_of_exponent_le hN1 hdelta
    have hmonoBase := Real.rpow_le_rpow (Nat.cast_nonneg _) hNupper
      (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    have htwo : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ 2 by norm_num) (show (1 / 4 : ℝ) ≤ 1 by norm_num)
    have ht1 : 1 ≤ |t| := by linarith
    have htpart : (|t| ^ 2) ^ (1 / 4 : ℝ) ≤ |t| := by
      have heq : (|t| ^ 2) ^ (1 / 4 : ℝ) = |t| ^ (1 / 2 : ℝ) := by
        rw [show |t| ^ 2 = |t| ^ (2 : ℝ) by
          norm_num [Real.rpow_natCast]]
        rw [← Real.rpow_mul (abs_nonneg t)]
        norm_num
      rw [heq]
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le ht1 (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    calc
      ((N + 1 : ℕ) : ℝ) ^ (1 - sigma) ≤
          ((N + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ) := hmonoExp
      _ ≤ (2 * |t| ^ 2) ^ (1 / 4 : ℝ) := hmonoBase
      _ = 2 ^ (1 / 4 : ℝ) * (|t| ^ 2) ^ (1 / 4 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) (sq_nonneg |t|)]
      _ ≤ 2 * |t| := mul_le_mul htwo htpart (by positivity) (by norm_num)
  have hweight : w (N + 1) * E =
      12 / v * ((N + 1 : ℕ) : ℝ) ^ (1 - sigma) := by
    dsimp only [w, E]
    have hNp : (0 : ℝ) < (N + 1 : ℕ) := by positivity
    calc
      ((N + 1 : ℕ) : ℝ) ^ (-sigma) *
          (12 * (N + 1 : ℕ) / v) =
        12 / v * (((N + 1 : ℕ) : ℝ) ^ (-sigma) *
          ((N + 1 : ℕ) : ℝ) ^ (1 : ℝ)) := by rw [Real.rpow_one]; ring
      _ = 12 / v * ((N + 1 : ℕ) : ℝ) ^ (-sigma + 1) := by
        rw [Real.rpow_add hNp]
      _ = _ := by congr 1; ring
  rw [hweight] at hfirst
  have hcoef0 : 0 ≤ 12 / v := by positivity
  have hbound : 12 / v * ((N + 1 : ℕ) : ℝ) ^ (1 - sigma) ≤
      48 * Real.pi := by
    calc
      12 / v * ((N + 1 : ℕ) : ℝ) ^ (1 - sigma) ≤
          12 / v * (2 * |t|) := mul_le_mul_of_nonneg_left hbase hcoef0
      _ = 48 * Real.pi := by
        dsimp only [v]
        field_simp
        ring
  have hpi : 48 * Real.pi < 200 := by nlinarith [Real.pi_lt_four]
  exact hfirst.trans (hbound.trans hpi.le)

/-- Both dyadic ranges used below contain at most `3 log T` blocks. -/
theorem natLog2_succ_le_three_log_height (X : ℕ) (T : ℝ)
    (hX : 1 ≤ X) (hXT : (X : ℝ) ≤ T) (hT : 2 ≤ T) :
    (((X.log2 + 1 : ℕ) : ℝ)) ≤ 3 * Real.log T := by
  have hcount := MoltResearch.natLog2_succ_le_three_halves_log_two_mul X hX
  have hT0 : 0 < T := by linarith
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hlogmono : Real.log (2 * (X : ℝ)) ≤ Real.log (2 * T) := by
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hlogtwo : Real.log 2 ≤ Real.log T :=
    Real.log_le_log (by norm_num) hT
  have hsplit : Real.log (2 * T) = Real.log 2 + Real.log T := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hT0)]
  rw [hsplit] at hlogmono
  nlinarith

set_option maxHeartbeats 1600000 in
/-- The strip estimate before taking logarithms. -/
theorem norm_zeta_le_vinogradov_growth
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hweyl : ∀ (N : ℕ) (T : ℝ), 2 ≤ N → (N : ℝ) ≤ T →
      ∀ (u : ℝ) (R : ℕ), 0 ≤ u → u ≤ 1 → N < R → R ≤ 2 * N →
        ‖∑ n ∈ Finset.Ioc N R,
            ((n : ℝ) + u : ℂ) ^ (-(T : ℂ) * I)‖ ≤
          C * (N : ℝ) ^
            (1 - c / ((Real.log T / Real.log N) ^ 3 *
              Real.log (2 * (Real.log T / Real.log N)) ^ 3)))
    (sigma t : ℝ) (ht : 16 ≤ |t|) (hsigma34 : 3 / 4 ≤ sigma)
    (hsigma1 : sigma ≤ 1) :
    ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤
      1000 * (C + 1) * Real.log |t| *
        |t| ^ ((c / 54000) ^ (-10 / 31 : ℝ) *
          (1 - sigma) ^ (33 / 25 : ℝ)) := by
  let T : ℝ := |t|
  let X : ℕ := ⌊T⌋₊
  let N : ℕ := X ^ 2 + 1
  let s : ℂ := (sigma : ℂ) + I * t
  let E : ℝ := (c / 54000) ^ (-10 / 31 : ℝ) *
    (1 - sigma) ^ (33 / 25 : ℝ)
  let f : ℕ → ℂ := fun n => ((n : ℕ) : ℂ) ^ (-s)
  have hT : 16 ≤ T := ht
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hlogT : 1 ≤ Real.log T := by
    have hlog := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ T by linarith [Real.exp_one_lt_three])
    simpa using hlog
  have hXlower : (16 : ℕ) ≤ X := by
    dsimp only [X]
    exact Nat.le_floor (by simpa only [Nat.cast_ofNat] using hT)
  have hX1 : 1 ≤ X := by omega
  have hX2 : 2 ≤ X := by omega
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXT : (X : ℝ) ≤ T := by
    dsimp only [X]
    exact Nat.floor_le (by positivity)
  have hTX : T < (X : ℝ) + 1 := by
    dsimp only [X]
    exact Nat.lt_floor_add_one T
  have hcount : (((X.log2 + 1 : ℕ) : ℝ)) ≤ 3 * Real.log T :=
    natLog2_succ_le_three_log_height X T hX1 hXT (by linarith)
  have hcountLow : ((X.log2 : ℕ) : ℝ) ≤ 3 * Real.log T := by
    have : ((X.log2 : ℕ) : ℝ) ≤ ((X.log2 + 1 : ℕ) : ℝ) := by norm_num
    exact this.trans hcount
  have hsre : s.re = sigma := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hsigma0 : 0 ≤ sigma := by linarith
  have hdelta0 : 0 ≤ 1 - sigma := by linarith
  have hdelta14 : 1 - sigma ≤ 1 / 4 := by linarith
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hTE : 1 ≤ T ^ E := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hT1 hE0

  -- The low blocks, where Vinogradov's estimate applies.
  have hpowX : 2 ^ X.log2 ≤ X := Nat.log2_self_le (by omega)
  have hlowBase : ∀ j ∈ Finset.range X.log2, 2 ^ j * 2 ≤ X := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjp : j + 1 ≤ X.log2 := by omega
    calc
      2 ^ j * 2 = 2 ^ (j + 1) := by rw [pow_succ]
      _ ≤ 2 ^ X.log2 := Nat.pow_le_pow_right (by norm_num) hjp
      _ ≤ X := hpowX
  have hlowTile :
      ∑ j ∈ Finset.range X.log2,
          ∑ n ∈ Finset.Ioc (2 ^ j * 2)
            (min (2 ^ (j + 1) * 2) X), f n =
        ∑ n ∈ Finset.Ioc 2 X, f n := by
    have htile := zetaGrowth_sum_dyadic_tiling 2 X X.log2 f
    have hleft :
        (∑ j ∈ Finset.range X.log2,
            ∑ n ∈ Finset.Ioc (min (2 ^ j * 2) X)
              (min (2 ^ (j + 1) * 2) X), f n) =
          ∑ j ∈ Finset.range X.log2,
            ∑ n ∈ Finset.Ioc (2 ^ j * 2)
              (min (2 ^ (j + 1) * 2) X), f n := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [min_eq_left (hlowBase j hj)]
    rw [hleft] at htile
    have hstart : min 2 X = 2 := min_eq_left hX2
    have hend : min (2 ^ X.log2 * 2) X = X := by
      rw [min_eq_right]
      exact (Nat.log2_lt (by omega : X ≠ 0)).mp (Nat.lt_succ_self X.log2) |>.le
    simpa only [hstart, hend] using htile
  have hlowBlock : ∀ j ∈ Finset.range X.log2,
      ‖∑ n ∈ Finset.Ioc (2 ^ j * 2)
          (min (2 ^ (j + 1) * 2) X), f n‖ ≤ 2 * C * T ^ E := by
    intro j hj
    let M : ℕ := 2 ^ j * 2
    let P : ℕ := min (2 ^ (j + 1) * 2) X
    have hM : M ≤ X := hlowBase j hj
    have hM2 : 2 ≤ M := by
      dsimp only [M]
      have hp : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      omega
    have hMP : M ≤ P := by
      dsimp only [M, P]
      apply le_min
      · rw [pow_succ]
        omega
      · exact hM
    have hP : P ≤ 2 * M := by
      dsimp only [P, M]
      calc
        min (2 ^ (j + 1) * 2) X ≤ 2 ^ (j + 1) * 2 := min_le_left _ _
        _ = 2 * (2 ^ j * 2) := by rw [pow_succ]; ring
    have hMT : (M : ℝ) ≤ |t| := by
      have hMX : (M : ℝ) ≤ X := by exact_mod_cast hM
      dsimp only [T] at hXT
      exact hMX.trans hXT
    have hblock := norm_sum_cpow_Ioc_le_vinogradov_optimized hc hC hweyl
      M P sigma t hsigma0 hsigma1 hM2 hMT hMP hP
    simpa only [f, s, T, E] using hblock
  have hlowSum :
      ‖∑ n ∈ Finset.Ioc 2 X, f n‖ ≤
        6 * C * Real.log T * T ^ E := by
    rw [← hlowTile]
    calc
      ‖∑ j ∈ Finset.range X.log2,
          ∑ n ∈ Finset.Ioc (2 ^ j * 2)
            (min (2 ^ (j + 1) * 2) X), f n‖ ≤
          ∑ j ∈ Finset.range X.log2,
            ‖∑ n ∈ Finset.Ioc (2 ^ j * 2)
              (min (2 ^ (j + 1) * 2) X), f n‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range X.log2, 2 * C * T ^ E :=
        Finset.sum_le_sum hlowBlock
      _ = ((X.log2 : ℕ) : ℝ) * (2 * C * T ^ E) := by simp
      _ ≤ 6 * C * Real.log T * T ^ E := by
        have hfac : 0 ≤ 2 * C * T ^ E := by positivity
        have := mul_le_mul_of_nonneg_right hcountLow hfac
        nlinarith
  have hsmall : ‖f 1‖ + ‖f 2‖ ≤ 2 := by
    have hfn : ∀ n : ℕ, 1 ≤ n → ‖f n‖ ≤ 1 := by
      intro n hn
      dsimp only [f]
      rw [Complex.norm_natCast_cpow_of_pos (by omega)]
      have hneg : (-s).re = -sigma := by rw [neg_re, hsre]
      rw [hneg]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      simpa only [Real.rpow_zero] using
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith : -sigma ≤ 0)
    linarith [hfn 1 le_rfl, hfn 2 (by omega)]
  have hlowDecomp :
      (∑ n ∈ Finset.Icc 1 X, f n) = f 1 + f 2 + ∑ n ∈ Finset.Ioc 2 X, f n := by
    rw [Finset.Icc_eq_cons_Ioc hX1, Finset.sum_cons]
    have hsplit := Finset.sum_Ioc_consecutive f (show 1 ≤ 2 by omega) hX2
    rw [show ∑ n ∈ Finset.Ioc 1 2, f n = f 2 by simp] at hsplit
    rw [← hsplit]
    ring
  have hlow : ‖∑ n ∈ Finset.Icc 1 X, f n‖ ≤
      2 + 6 * C * Real.log T * T ^ E := by
    rw [hlowDecomp]
    calc
      ‖f 1 + f 2 + ∑ n ∈ Finset.Ioc 2 X, f n‖ ≤
          ‖f 1‖ + ‖f 2‖ + ‖∑ n ∈ Finset.Ioc 2 X, f n‖ := by
        have h1 := norm_add_le (f 1) (f 2)
        have h2 := norm_add_le (f 1 + f 2) (∑ n ∈ Finset.Ioc 2 X, f n)
        linarith
      _ ≤ _ := by linarith [hsmall, hlowSum]

  -- The high blocks, where the first derivative is separated from integers.
  have hhighBase : ∀ j ∈ Finset.range (X.log2 + 1), 2 ^ j * X ≤ X ^ 2 := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjle : j ≤ X.log2 := by omega
    have hp : 2 ^ j ≤ X :=
      (Nat.pow_le_pow_right (by norm_num) hjle).trans hpowX
    nlinarith
  have hhighTile :
      ∑ j ∈ Finset.range (X.log2 + 1),
          ∑ n ∈ Finset.Ioc (2 ^ j * X)
            (min (2 ^ (j + 1) * X) (X ^ 2)), f n =
        ∑ n ∈ Finset.Ioc X (X ^ 2), f n := by
    have htile := zetaGrowth_sum_dyadic_tiling X (X ^ 2) (X.log2 + 1) f
    have hleft :
        (∑ j ∈ Finset.range (X.log2 + 1),
            ∑ n ∈ Finset.Ioc (min (2 ^ j * X) (X ^ 2))
              (min (2 ^ (j + 1) * X) (X ^ 2)), f n) =
          ∑ j ∈ Finset.range (X.log2 + 1),
            ∑ n ∈ Finset.Ioc (2 ^ j * X)
              (min (2 ^ (j + 1) * X) (X ^ 2)), f n := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [min_eq_left (hhighBase j hj)]
    rw [hleft] at htile
    have hstart : min X (X ^ 2) = X := min_eq_left (by nlinarith)
    have hend : min (2 ^ (X.log2 + 1) * X) (X ^ 2) = X ^ 2 := by
      rw [min_eq_right]
      have hp : X < 2 ^ (X.log2 + 1) :=
        (Nat.log2_lt (by omega : X ≠ 0)).mp (Nat.lt_succ_self X.log2)
      nlinarith
    simpa only [hstart, hend] using htile
  have hhighBlock : ∀ j ∈ Finset.range (X.log2 + 1),
      ‖∑ n ∈ Finset.Ioc (2 ^ j * X)
          (min (2 ^ (j + 1) * X) (X ^ 2)), f n‖ ≤ 200 := by
    intro j hj
    let M : ℕ := 2 ^ j * X
    let P : ℕ := min (2 ^ (j + 1) * X) (X ^ 2)
    have hM : M ≤ X ^ 2 := hhighBase j hj
    have hMX : X ≤ M := by
      dsimp only [M]
      calc X = 1 * X := (one_mul X).symm
        _ ≤ 2 ^ j * X := Nat.mul_le_mul_right X Nat.one_le_two_pow
    have hM1 : 1 ≤ M := hX1.trans hMX
    have hMP : M ≤ P := by
      dsimp only [M, P]
      apply le_min
      · exact Nat.mul_le_mul_right X
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ j))
      · exact hM
    have hP : P ≤ 2 * M := by
      dsimp only [P, M]
      calc
        min (2 ^ (j + 1) * X) (X ^ 2) ≤ 2 ^ (j + 1) * X := min_le_left _ _
        _ = 2 * (2 ^ j * X) := by rw [pow_succ]; ring
    have hTM : |t| ≤ ((M + 1 : ℕ) : ℝ) := by
      dsimp only [T] at hTX
      have hXM : (X : ℝ) ≤ M := by exact_mod_cast hMX
      push_cast
      linarith
    have hMupper : ((M + 1 : ℕ) : ℝ) ≤ 2 * |t| ^ 2 := by
      have hMreal : (M : ℝ) ≤ (X : ℝ) ^ 2 := by exact_mod_cast hM
      have hXT0 : (0 : ℝ) ≤ X := by positivity
      have hsq : (X : ℝ) ^ 2 ≤ T ^ 2 := by nlinarith
      dsimp only [T] at hsq
      push_cast
      nlinarith [sq_nonneg |t|]
    have hblock := norm_sum_cpow_Ioc_le_kusmin_two_hundred
      M P sigma t hsigma0 hsigma34 hsigma1 ht hTM hM1 hMP hP hMupper
    simpa only [f, s] using hblock
  have hhigh : ‖∑ n ∈ Finset.Ioc X (X ^ 2), f n‖ ≤
      600 * Real.log T * T ^ E := by
    rw [← hhighTile]
    calc
      ‖∑ j ∈ Finset.range (X.log2 + 1),
          ∑ n ∈ Finset.Ioc (2 ^ j * X)
            (min (2 ^ (j + 1) * X) (X ^ 2)), f n‖ ≤
          ∑ j ∈ Finset.range (X.log2 + 1),
            ‖∑ n ∈ Finset.Ioc (2 ^ j * X)
              (min (2 ^ (j + 1) * X) (X ^ 2)), f n‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range (X.log2 + 1), 200 :=
        Finset.sum_le_sum hhighBlock
      _ = ((X.log2 + 1 : ℕ) : ℝ) * 200 := by simp
      _ ≤ 600 * Real.log T := by nlinarith
      _ ≤ 600 * Real.log T * T ^ E := by
        have hlog0 : 0 ≤ Real.log T := by linarith
        have hnonneg : 0 ≤ 600 * Real.log T := by positivity
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hTE hnonneg
  have hpartialDecomp :
      (∑ n ∈ Finset.Ico 1 N, f n) =
        (∑ n ∈ Finset.Icc 1 X, f n) + ∑ n ∈ Finset.Ioc X (X ^ 2), f n := by
    have hXsq : X + 1 ≤ N := by dsimp only [N]; nlinarith
    have hsplit := Finset.sum_Ico_consecutive f (show 1 ≤ X + 1 by omega) hXsq
    have hfirst : Finset.Ico 1 (X + 1) = Finset.Icc 1 X := by
      ext n
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    have hsecond : Finset.Ico (X + 1) N = Finset.Ioc X (X ^ 2) := by
      dsimp only [N]
      ext n
      simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega
    rw [hfirst, hsecond] at hsplit
    exact hsplit.symm
  have hpartial : ‖∑ n ∈ Finset.Ico 1 N, f n‖ ≤
      2 + (6 * C + 600) * Real.log T * T ^ E := by
    rw [hpartialDecomp]
    refine (norm_add_le _ _).trans ?_
    nlinarith [hlow, hhigh]

  -- The long cutoff makes the potential and the analytic tail bounded.
  have hnormLower : T ≤ ‖s - 1‖ := by
    calc
      T = |(s - 1).im| := by simp [T, s]
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
  have hnormUpper : ‖s - 1‖ ≤ T + 1 / 4 := by
    have heq : s - 1 = ((sigma - 1 : ℝ) : ℂ) + I * t := by
      dsimp only [s]
      push_cast
      ring
    rw [heq]
    calc
      ‖((sigma - 1 : ℝ) : ℂ) + I * t‖ ≤
          ‖((sigma - 1 : ℝ) : ℂ)‖ + ‖I * (t : ℂ)‖ := norm_add_le _ _
      _ = |sigma - 1| + T := by
        rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_I,
          one_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ T + 1 / 4 := by
        rw [abs_of_nonpos (by linarith : sigma - 1 ≤ 0)]
        linarith
  have hNafe : 4 * ‖s - 1‖ ≤ (N : ℝ) := by
    have hXR : (16 : ℝ) ≤ X := by exact_mod_cast hXlower
    have hTXle : T ≤ (X : ℝ) + 1 := hTX.le
    have hNsimp : (N : ℝ) = (X : ℝ) ^ 2 + 1 := by
      dsimp only [N]
      push_cast
      ring
    rw [hNsimp]
    nlinarith [sq_nonneg ((X : ℝ) - 2)]
  have him : 2 ≤ |s.im| := by simpa [hsim, T] using (show 2 ≤ T by linarith)
  have hafe := zeta_afe_strip s N (by rw [hsre]; linarith) him hNafe
  have hN2 : 2 ≤ N := by
    dsimp only [N]
    have hp : 1 ≤ X ^ 2 := one_le_pow₀ hX1
    omega
  have hs1 : 1 ≤ ‖s - 1‖ := hT1.trans hnormLower
  have hNtail : 2 * ‖s - 1‖ ≤ (N : ℝ) := by
    nlinarith [norm_nonneg (s - 1)]
  have hNupper : (N : ℝ) ≤ 2 * T ^ 2 := by
    have hsq : (X : ℝ) ^ 2 ≤ T ^ 2 := by nlinarith [hXT]
    have hNsimp : (N : ℝ) = (X : ℝ) ^ 2 + 1 := by
      dsimp only [N]
      push_cast
      ring
    rw [hNsimp]
    nlinarith [sq_nonneg T]
  have hNrpow : (N : ℝ) ^ (1 - sigma) ≤ 2 * T := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hmonoExp := Real.rpow_le_rpow_of_exponent_le hN1 hdelta14
    have hmonoBase := Real.rpow_le_rpow (Nat.cast_nonneg _) hNupper
      (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    have htwo : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ 2 by norm_num) (show (1 / 4 : ℝ) ≤ 1 by norm_num)
    have htpart : (T ^ 2) ^ (1 / 4 : ℝ) ≤ T := by
      have heq : (T ^ 2) ^ (1 / 4 : ℝ) = T ^ (1 / 2 : ℝ) := by
        rw [show T ^ 2 = T ^ (2 : ℝ) by norm_num [Real.rpow_natCast]]
        rw [← Real.rpow_mul hT0.le]
        norm_num
      rw [heq]
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT1
        (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    calc
      (N : ℝ) ^ (1 - sigma) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := hmonoExp
      _ ≤ (2 * T ^ 2) ^ (1 / 4 : ℝ) := hmonoBase
      _ = 2 ^ (1 / 4 : ℝ) * (T ^ 2) ^ (1 / 4 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) (sq_nonneg T)]
      _ ≤ 2 * T := mul_le_mul htwo htpart (by positivity) (by norm_num)
  have hpot : ‖zPot s N‖ ≤ 2 := by
    rw [zPot, norm_div]
    have hpow : ‖((N : ℕ) : ℂ) ^ ((1 : ℂ) - s)‖ =
        (N : ℝ) ^ (1 - sigma) := by
      rw [Complex.norm_natCast_cpow_of_pos (by omega)]
      congr 1
      simp [hsre]
    rw [hpow]
    exact (div_le_iff₀ (lt_of_lt_of_le hT0 hnormLower)).2 (by nlinarith)
  have htailRaw := norm_zTail_le_strip s N (by rw [hsre]; linarith)
    hs1 hNtail hN2
  have hXneg : ((X : ℝ) ^ 2) ^ (-sigma) ≤ 1 / (X : ℝ) := by
    have heq : ((X : ℝ) ^ 2) ^ (-sigma) = (X : ℝ) ^ (-2 * sigma) := by
      rw [show (X : ℝ) ^ 2 = (X : ℝ) ^ (2 : ℝ) by
        norm_num [Real.rpow_natCast]]
      rw [← Real.rpow_mul hX0.le]
      congr 1
      ring
    rw [heq, show 1 / (X : ℝ) = (X : ℝ) ^ (-1 : ℝ) by
      rw [Real.rpow_neg_one, one_div]]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hX1) (by linarith)
  have hnormX : ‖s - 1‖ ≤ 2 * (X : ℝ) := by
    have hTXle : T ≤ (X : ℝ) + 1 := hTX.le
    have hXR : (16 : ℝ) ≤ X := by exact_mod_cast hXlower
    linarith
  have htail : ‖zTail s N‖ ≤ 6 := by
    have hNminus : ((N : ℝ) - 1) ^ (-s.re) = ((X : ℝ) ^ 2) ^ (-sigma) := by
      have hNsimp : (N : ℝ) - 1 = (X : ℝ) ^ 2 := by
        dsimp only [N]
        push_cast
        ring
      rw [hNsimp, hsre]
    rw [hNminus] at htailRaw
    rw [hsre] at htailRaw
    have hnum := mul_le_mul_of_nonneg_left hnormX (by norm_num : (0 : ℝ) ≤ 2)
    have hmul := mul_le_mul hnum hXneg (by positivity) (by positivity)
    have hsig : (0 : ℝ) < sigma := by linarith
    have hpre : 2 * ‖s - 1‖ * ((X : ℝ) ^ 2) ^ (-sigma) ≤ 4 := by
      calc
        2 * ‖s - 1‖ * ((X : ℝ) ^ 2) ^ (-sigma) ≤
            (4 * (X : ℝ)) * (1 / (X : ℝ)) := by nlinarith
        _ = 4 := by field_simp
    have := (div_le_div_of_nonneg_right hpre hsig.le)
    have hfour : 4 / sigma ≤ 6 := by
      rw [div_le_iff₀ hsig]
      nlinarith
    exact htailRaw.trans (this.trans hfour)

  have hpartialActual : ‖∑ n ∈ Finset.Ico 1 N, ((n : ℕ) : ℂ) ^ (-s)‖ ≤
      2 + (6 * C + 600) * Real.log T * T ^ E := by
    simpa only [f] using hpartial
  rw [hafe]
  have hassemble :
      ‖(∑ n ∈ Finset.Ico 1 N, ((n : ℕ) : ℂ) ^ (-s)) + zPot s N + zTail s N‖ ≤
        10 + (6 * C + 600) * Real.log T * T ^ E := by
    calc
      _ ≤ ‖∑ n ∈ Finset.Ico 1 N, ((n : ℕ) : ℂ) ^ (-s)‖ +
          ‖zPot s N‖ + ‖zTail s N‖ := by
        have h1 := norm_add_le
          ((∑ n ∈ Finset.Ico 1 N, ((n : ℕ) : ℂ) ^ (-s)) + zPot s N)
          (zTail s N)
        have h2 := norm_add_le
          (∑ n ∈ Finset.Ico 1 N, ((n : ℕ) : ℂ) ^ (-s)) (zPot s N)
        linarith
      _ ≤ _ := by linarith [hpartialActual, hpot, htail]
  refine hassemble.trans ?_
  have hlog0 : 0 ≤ Real.log T := by linarith
  have hunit : 1 ≤ Real.log T * T ^ E := one_le_mul_of_one_le_of_one_le hlogT hTE
  have hC0 : 0 ≤ C := hC.le
  have hcoef : 10 + (6 * C + 600) * Real.log T * T ^ E ≤
      1000 * (C + 1) * Real.log T * T ^ E := by
    nlinarith [mul_nonneg hlog0 (Real.rpow_nonneg hT0.le E)]
  simpa only [T, E] using hcoef

set_option maxHeartbeats 800000 in
/-- Logarithmic form of the Vinogradov strip estimate. -/
theorem log_norm_zeta_le_vinogradov_growth
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hweyl : ∀ (N : ℕ) (T : ℝ), 2 ≤ N → (N : ℝ) ≤ T →
      ∀ (u : ℝ) (R : ℕ), 0 ≤ u → u ≤ 1 → N < R → R ≤ 2 * N →
        ‖∑ n ∈ Finset.Ioc N R,
            ((n : ℝ) + u : ℂ) ^ (-(T : ℂ) * I)‖ ≤
          C * (N : ℝ) ^
            (1 - c / ((Real.log T / Real.log N) ^ 3 *
              Real.log (2 * (Real.log T / Real.log N)) ^ 3)))
    (sigma t : ℝ) (ht : 16 ≤ |t|) (hsigma34 : 3 / 4 ≤ sigma)
    (hsigma1 : sigma ≤ 1) :
    Real.log ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤
      (c / 54000) ^ (-10 / 31 : ℝ) *
          (1 - sigma) ^ (33 / 25 : ℝ) * Real.log |t| +
        Real.log (Real.log |t|) + Real.log (1000 * (C + 1)) := by
  let E : ℝ := (c / 54000) ^ (-10 / 31 : ℝ) *
    (1 - sigma) ^ (33 / 25 : ℝ)
  let A : ℝ := 1000 * (C + 1)
  have hnorm := norm_zeta_le_vinogradov_growth hc hC hweyl sigma t ht hsigma34 hsigma1
  have ht0 : 0 < |t| := by linarith
  have hlogt : 1 ≤ Real.log |t| := by
    have hlog := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ |t| by linarith [Real.exp_one_lt_three])
    simpa using hlog
  have hA : 0 < A := by dsimp only [A]; positivity
  have hE : 0 ≤ E := by
    dsimp only [E]
    have : 0 ≤ 1 - sigma := by linarith
    positivity
  have htpow : 0 < |t| ^ E := Real.rpow_pos_of_pos ht0 E
  by_cases hz : riemannZeta ((sigma : ℂ) + I * t) = 0
  · rw [hz, norm_zero, Real.log_zero]
    have hloglog : 0 ≤ Real.log (Real.log |t|) := Real.log_nonneg hlogt
    have hlogA : 0 ≤ Real.log A := Real.log_nonneg (by
      dsimp only [A]
      nlinarith)
    have hmain : 0 ≤ E * Real.log |t| := mul_nonneg hE (by linarith)
    simpa only [E, A] using add_nonneg (add_nonneg hmain hloglog) hlogA
  · have hnorm0 : 0 < ‖riemannZeta ((sigma : ℂ) + I * t)‖ :=
      norm_pos_iff.mpr hz
    have hbound : ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤
        A * Real.log |t| * |t| ^ E := by
      simpa only [A, E] using hnorm
    calc
      Real.log ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤
          Real.log (A * Real.log |t| * |t| ^ E) :=
        Real.log_le_log hnorm0 hbound
      _ = Real.log A + Real.log (Real.log |t|) + E * Real.log |t| := by
        rw [Real.log_mul (mul_ne_zero hA.ne' (by linarith)) htpow.ne',
          Real.log_mul hA.ne' (by linarith), Real.log_rpow ht0]
      _ = _ := by
        dsimp only [E, A]
        ring

/-- The elementary L-series estimate controls the part of the strip to the
right of one. -/
theorem log_norm_zeta_le_right_strip (sigma t : ℝ)
    (ht : max 16 (Real.exp (Real.exp 1)) ≤ |t|)
    (hsigma1 : 1 < sigma) (hsigma2 : sigma ≤ 2) :
    Real.log ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤
      Real.log (Real.log |t|) + Real.log 16384 := by
  let T : ℝ := |t|
  have hT16 : 16 ≤ T := (le_max_left _ _).trans ht
  have hTexp : Real.exp (Real.exp 1) ≤ T := (le_max_right _ _).trans ht
  have hT0 : 0 < T := by linarith
  have hlogT0 : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogT : 1 ≤ Real.log T := by
    have hlog := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ T by linarith [Real.exp_one_lt_three])
    simpa using hlog
  have hden : 1 ≤ Real.log (Real.log (T + 2)) := by
    have hinner : Real.exp 1 ≤ Real.log (T + 2) := by
      calc
        Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := by rw [Real.log_exp]
        _ ≤ Real.log (T + 2) :=
          Real.log_le_log (Real.exp_pos _) (by linarith)
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log (Real.log (T + 2)) :=
        Real.log_le_log (Real.exp_pos _) hinner
  have hseries := zeta_LSeries_bound sigma (-t) hsigma1 hsigma2 (by
    simpa only [abs_neg, T] using (show 1 ≤ T by linarith))
  have hone : (fun _ : ℕ => (1 : ℂ)) = 1 := by ext; rfl
  rw [hone] at hseries
  rw [LSeries_one_eq_riemannZeta (by simp; linarith)] at hseries
  have hseries' : ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤
      8192 * Real.log (T + 2) / Real.log (Real.log (T + 2)) := by
    convert hseries using 1 <;> simp only [T, abs_neg, Complex.ofReal_neg] <;> ring
  have hlogplus0 : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
  have hdivide :
      8192 * Real.log (T + 2) / Real.log (Real.log (T + 2)) ≤
        8192 * Real.log (T + 2) :=
    div_le_self (mul_nonneg (by norm_num) hlogplus0) hden
  have hplus : T + 2 ≤ T ^ 2 := by nlinarith [sq_nonneg (T - 2)]
  have hlogplus : Real.log (T + 2) ≤ 2 * Real.log T := by
    calc
      Real.log (T + 2) ≤ Real.log (T ^ 2) :=
        Real.log_le_log (by positivity) hplus
      _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
  have hnorm : ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤
      16384 * Real.log T := by
    calc
      _ ≤ 8192 * Real.log (T + 2) /
          Real.log (Real.log (T + 2)) := hseries'
      _ ≤ 8192 * Real.log (T + 2) := hdivide
      _ ≤ 16384 * Real.log T := by nlinarith
  by_cases hz : riemannZeta ((sigma : ℂ) + I * t) = 0
  · rw [hz, norm_zero, Real.log_zero]
    have hloglog : 0 ≤ Real.log (Real.log T) :=
      Real.log_nonneg hlogT
    have hlogC : 0 ≤ Real.log (16384 : ℝ) := Real.log_nonneg (by norm_num)
    simpa only [T] using add_nonneg hloglog hlogC
  · have hnorm0 : 0 < ‖riemannZeta ((sigma : ℂ) + I * t)‖ :=
      norm_pos_iff.mpr hz
    calc
      Real.log ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤
          Real.log (16384 * Real.log T) := Real.log_le_log hnorm0 hnorm
      _ = Real.log 16384 + Real.log (Real.log T) :=
        Real.log_mul (by norm_num) hlogT0.ne'
      _ = _ := by simp only [T]; ring

/-- **V-C3.** Vinogradov's Weyl-sum estimate gives the growth exponent
`33/25`. -/
theorem zeta_growth_vinogradov :
    ∃ (t₀ B B₀ : ℝ), 3 ≤ t₀ ∧ 0 < B ∧ ∀ sigma t : ℝ,
      t₀ ≤ |t| → 3 / 4 ≤ sigma → sigma ≤ 2 →
        Real.log ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤
          B * (max (1 - sigma) 0) ^ (33 / 25 : ℝ) * Real.log |t| +
            Real.log (Real.log |t|) + B₀ := by
  obtain ⟨c, C, hc, hC, hweyl⟩ := VinogradovWeylSum.vinogradov_weyl_sum
  let t₀ : ℝ := max 16 (Real.exp (Real.exp 1))
  let B : ℝ := (c / 54000) ^ (-10 / 31 : ℝ)
  let B₀ : ℝ := Real.log (1000 * (C + 1)) + Real.log 16384
  refine ⟨t₀, B, B₀, ?_, ?_, ?_⟩
  · dsimp only [t₀]
    exact le_trans (by norm_num) (le_max_left _ _)
  · dsimp only [B]
    positivity
  · intro sigma t ht hsigma34 hsigma2
    rcases le_or_gt sigma 1 with hsigma1 | hsigma1
    · have hstrip := log_norm_zeta_le_vinogradov_growth hc hC hweyl
        sigma t ((le_max_left _ _).trans ht) hsigma34 hsigma1
      have hmax : max (1 - sigma) 0 = 1 - sigma := max_eq_left (by linarith)
      rw [hmax]
      dsimp only [B, B₀]
      have hlogC : 0 ≤ Real.log (16384 : ℝ) := Real.log_nonneg (by norm_num)
      linarith
    · have hright := log_norm_zeta_le_right_strip sigma t ht hsigma1 hsigma2
      have hmax : max (1 - sigma) 0 = 0 := max_eq_right (by linarith)
      rw [hmax, Real.zero_rpow (by norm_num : (33 / 25 : ℝ) ≠ 0), mul_zero,
        zero_mul]
      dsimp only [B₀]
      have hlogA : 0 ≤ Real.log (1000 * (C + 1)) := Real.log_nonneg (by
        nlinarith)
      linarith

/-- Packaged form consumed by the V-C4 zero-free-region interface. -/
theorem exists_zetaGrowthBound_vinogradov :
    ∃ (t₀ B B₀ : ℝ), 3 ≤ t₀ ∧ 0 < B ∧
      ZetaGrowthBound t₀ (33 / 25) B 1 B₀ := by
  obtain ⟨t₀, B, B₀, ht₀, hB, hbound⟩ := zeta_growth_vinogradov
  exact ⟨t₀, B, B₀, ht₀, hB, ⟨by
    intro sigma t ht hsigma34 hsigma2
    have hsigma34' : 3 / 4 ≤ sigma := by norm_num at hsigma34 ⊢; exact hsigma34
    simpa only [one_mul] using hbound sigma t ht hsigma34' hsigma2⟩⟩

#print axioms zeta_growth_vinogradov
#print axioms exists_zetaGrowthBound_vinogradov

end ExpSums

end MoltResearch
