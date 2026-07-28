import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5VinogradovKorobov

/-!
# Track C: Stage 5 — the Vinogradov–Korobov interface, discharged (Track L, #3020)

**The Littlewood leg closes.** The Vinogradov–Korobov pretense interface —
until now carried as the assumption class `LittlewoodLBoundAssumption` via
the W4 wrapper — is here proved *outright*, from the fully elementary
van der Corput zeta bound `zeta_LSeries_bound` of the nucleus.

The character aspect dissolves by **the power trick**: for unimodular `z`,
`1 - Re(z^k) ≤ k²(1 - Re z)` (a geometric-series estimate), so at
`k = |(ZMod q)ˣ|` every Dirichlet twist is bounded below by the *pure zeta*
twist at frequency `k·s` — Lagrange kills `χ(p)^k`. No per-residue
exponential sums, no Pólya–Vinogradov, no `q`-uniformity: the modulus costs
only the factor `1/k² ≥ 1/Q²` and an additive `q`, both absorbed by the
`log log log X` divergence of the zeta pretense margin.

After this file, `VinogradovKorobovAssumption` is an unconditional instance
and Theorem 1.8 / EDP rest on `MatomakiRadziwillAssumption` alone.
-/

namespace MoltResearch

namespace Tao2015

open Finset ExpSums

/-- **The power trick**: on the unit circle, `1 - Re(z^k) ≤ k²(1 - Re z)`. -/
private theorem one_sub_re_pow_le (z : ℂ) (hz : ‖z‖ = 1) (k : ℕ) :
    1 - (z^k).re ≤ (k:ℝ)^2 * (1 - z.re) := by
  have hid : ∀ w : ℂ, ‖w‖ = 1 → 1 - w.re = ‖1 - w‖^2 / 2 := by
    intro w hw
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hre : ((1:ℂ) - w).re = 1 - w.re := by simp
    have him : ((1:ℂ) - w).im = -w.im := by simp
    rw [hre, him]
    have hw2 : w.re^2 + w.im^2 = 1 := by
      have h1 := Complex.sq_norm w
      rw [Complex.normSq_apply, hw] at h1
      nlinarith [h1]
    nlinarith [hw2]
  have hzk : ‖z^k‖ = 1 := by rw [norm_pow, hz, one_pow]
  rw [hid z hz, hid _ hzk]
  have hgeom : (1:ℂ) - z^k = (∑ i ∈ Finset.range k, z^i) * (1 - z) := by
    have h1 := geom_sum_mul z k
    have h2 : (∑ i ∈ Finset.range k, z ^ i) * (1 - z)
        = -((∑ i ∈ Finset.range k, z ^ i) * (z - 1)) := by ring
    rw [h2, h1]
    ring
  have hnorm : ‖(1:ℂ) - z^k‖ ≤ (k:ℝ) * ‖1 - z‖ := by
    rw [hgeom, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine le_trans (norm_sum_le _ _) ?_
    have h3 : ∀ i ∈ Finset.range k, ‖z^i‖ = 1 := fun i _ => by
      rw [norm_pow, hz, one_pow]
    rw [Finset.sum_congr rfl h3, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  have h4 : ‖(1:ℂ) - z^k‖^2 ≤ ((k:ℝ) * ‖1 - z‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc ‖(1:ℂ) - z^k‖^2/2 ≤ ((k:ℝ) * ‖(1:ℂ) - z‖)^2/2 := by linarith
    _ = (k:ℝ)^2 * (‖(1:ℂ) - z‖^2/2) := by ring

/-- Powers of positive-real cpow characters merge frequencies. -/
private theorem cpow_I_pow (p k : ℕ) (hp : 1 ≤ p) (s : ℝ) :
    ((p:ℂ) ^ (Complex.I * (s:ℝ)))^k
      = (p:ℂ) ^ (Complex.I * (((k:ℝ) * s : ℝ):ℂ)) := by
  have hpne : ((p:ℕ):ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  rw [Complex.cpow_def_of_ne_zero hpne, Complex.cpow_def_of_ne_zero hpne,
    ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- On non-divisor primes the character twist has unit norm and its
`card`-th power is the pure zeta twist. -/
private theorem charTwist_pow (q : ℕ) (hq : 1 ≤ q) [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℝ) (p : ℕ) (hp : p.Prime)
    (hpq : ¬ p ∣ q) :
    ‖charTwist q χ s p‖ = 1
    ∧ (charTwist q χ s p) ^ (Fintype.card (ZMod q)ˣ)
        = (p:ℂ) ^ (Complex.I * (((Fintype.card (ZMod q)ˣ : ℝ) * s : ℝ):ℂ)) := by
  set k := Fintype.card (ZMod q)ˣ with hkdef
  have hk1 : 1 ≤ k := Fintype.card_pos
  have hunit : IsUnit ((p : ℕ) : ZMod q) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (hp.coprime_iff_not_dvd).mpr hpq
  obtain ⟨u, hu⟩ := hunit
  have hχk : (χ ((p:ℕ) : ZMod q))^k = 1 := by
    rw [← hu, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one,
      Units.val_one, map_one]
  have hχnorm : ‖χ ((p:ℕ) : ZMod q)‖ = 1 := by
    have h1 : ‖χ ((p:ℕ) : ZMod q)‖^k = 1 := by
      rw [← norm_pow, hχk, norm_one]
    have h2 := norm_nonneg (χ ((p:ℕ) : ZMod q))
    rcases lt_trichotomy ‖χ ((p:ℕ) : ZMod q)‖ 1 with h | h | h
    · exfalso
      have h3 := pow_lt_one₀ h2 h (by omega : k ≠ 0)
      rw [h1] at h3
      exact lt_irrefl 1 h3
    · exact h
    · exfalso
      have h3 := one_lt_pow₀ h (by omega : k ≠ 0)
      rw [h1] at h3
      exact lt_irrefl 1 h3
  constructor
  · rw [charTwist, norm_mul, hχnorm, one_mul]
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    have h3 : (Complex.I * (s:ℝ)).re = 0 := by simp
    rw [h3, Real.rpow_zero]
  · rw [charTwist, mul_pow, hχk, one_mul]
    exact cpow_I_pow p k hp.one_lt.le s

/-- **The distance comparison**: every character twist is bounded below by
the pure zeta twist at the multiplied frequency, up to the modulus. -/
private theorem distSq_ge (q : ℕ) (hq : 1 ≤ q) [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℝ) (y : ℕ) :
    (1/((Fintype.card (ZMod q)ˣ : ℝ))^2)
        * ((∑ p ∈ y.primesBelow, (1:ℝ)/p)
          - ∑ p ∈ y.primesBelow,
              ((p:ℂ) ^ (Complex.I
                * (((Fintype.card (ZMod q)ˣ : ℝ) * s : ℝ):ℂ))).re / p)
      - q
    ≤ pretentiousDistSq (fun _ => 1) (charTwist q χ s) y := by
  classical
  set k := Fintype.card (ZMod q)ˣ with hkdef
  have hk1 : 1 ≤ k := Fintype.card_pos
  have hk0 : (0:ℝ) < (k:ℝ)^2 := by positivity
  have hk1R : (1:ℝ) ≤ (k:ℝ)^2 := by
    have h1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
    nlinarith
  have hdist : pretentiousDistSq (fun _ => 1) (charTwist q χ s) y
      = ∑ p ∈ y.primesBelow, (1 - (charTwist q χ s p).re) / p := by
    rw [pretentiousDistSq]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [one_mul, Complex.conj_re]
  rw [hdist]
  have hptw : ∀ p ∈ y.primesBelow,
      (1/(k:ℝ)^2) * (1 - ((p:ℂ)^(Complex.I * (((k:ℝ)*s : ℝ):ℂ))).re) / p
        - (if p ∣ q then (1:ℝ) else 0)
      ≤ (1 - (charTwist q χ s p).re) / p := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hp0 : (0:ℝ) < p := by linarith
    have hζnorm : ‖(p:ℂ)^(Complex.I * (((k:ℝ)*s : ℝ):ℂ))‖ = 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hpp.pos]
      have h3 : (Complex.I * (((k:ℝ)*s : ℝ):ℂ)).re = 0 := by simp
      rw [h3, Real.rpow_zero]
    have hζre : -1 ≤ ((p:ℂ)^(Complex.I * (((k:ℝ)*s : ℝ):ℂ))).re := by
      have h4 := Complex.abs_re_le_norm
        ((p:ℂ)^(Complex.I * (((k:ℝ)*s : ℝ):ℂ)))
      rw [hζnorm] at h4
      rw [abs_le] at h4
      exact h4.1
    by_cases hdvd : p ∣ q
    · rw [if_pos hdvd]
      have hzero : charTwist q χ s p = 0 := by
        rw [charTwist]
        have h1 : ¬ IsUnit ((p:ℕ) : ZMod q) := by
          rw [ZMod.isUnit_iff_coprime]
          intro h2
          have h3 : p ∣ Nat.gcd p q := Nat.dvd_gcd dvd_rfl hdvd
          rw [Nat.Coprime] at h2
          rw [h2] at h3
          have h4 := Nat.le_of_dvd (by norm_num) h3
          have h5 := hpp.two_le
          omega
        rw [MulChar.map_nonunit χ h1, zero_mul]
      rw [hzero]
      simp only [Complex.zero_re, sub_zero]
      have h6 : (1/(k:ℝ)^2) * (1 - ((p:ℂ)^(Complex.I
          * (((k:ℝ)*s : ℝ):ℂ))).re) ≤ 2 := by
        have h7 : 1 - ((p:ℂ)^(Complex.I * (((k:ℝ)*s : ℝ):ℂ))).re ≤ 2 := by
          linarith
        have h8 : (1:ℝ)/(k:ℝ)^2 ≤ 1 := by
          rw [div_le_one hk0]
          exact hk1R
        have h9 : (0:ℝ) ≤ 1 - ((p:ℂ)^(Complex.I
            * (((k:ℝ)*s : ℝ):ℂ))).re := by
          have h10 := Complex.re_le_norm
            ((p:ℂ)^(Complex.I * (((k:ℝ)*s : ℝ):ℂ)))
          rw [hζnorm] at h10
          linarith
        nlinarith
      have h11 : (1/(k:ℝ)^2) * (1 - ((p:ℂ)^(Complex.I
          * (((k:ℝ)*s : ℝ):ℂ))).re) / p ≤ 2/p := by
        gcongr
      have h12 : (2:ℝ)/p ≤ 1 := by
        rw [div_le_one hp0]
        linarith
      have h13 : (0:ℝ) ≤ 1/p := by positivity
      linarith
    · rw [if_neg hdvd, sub_zero]
      obtain ⟨hnorm1, hpow⟩ := charTwist_pow q hq χ s p hpp hdvd
      have h5 := one_sub_re_pow_le (charTwist q χ s p) hnorm1 k
      rw [hpow] at h5
      have h14 : (1/(k:ℝ)^2) * (1 - ((p:ℂ)^(Complex.I
          * (((k:ℝ)*s : ℝ):ℂ))).re) ≤ 1 - (charTwist q χ s p).re := by
        have h17 := mul_le_mul_of_nonneg_left h5
          (by positivity : (0:ℝ) ≤ 1/(k:ℝ)^2)
        have h18 : (1/(k:ℝ)^2) * ((k:ℝ)^2 * (1 - (charTwist q χ s p).re))
            = 1 - (charTwist q χ s p).re := by
          field_simp
        linarith
      gcongr
  refine le_trans ?_ (Finset.sum_le_sum hptw)
  rw [Finset.sum_sub_distrib]
  have hite : ∑ p ∈ y.primesBelow, (if p ∣ q then (1:ℝ) else 0) ≤ q := by
    rw [Finset.sum_boole]
    have h1 : (y.primesBelow.filter (fun p => p ∣ q)) ⊆ Finset.Icc 1 q := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hpp := Nat.prime_of_mem_primesBelow hp.1
      rw [Finset.mem_Icc]
      exact ⟨hpp.one_lt.le, Nat.le_of_dvd (by omega) hp.2⟩
    have h2 := Finset.card_le_card h1
    rw [Nat.card_Icc] at h2
    have h3 : q + 1 - 1 = q := by omega
    rw [h3] at h2
    exact_mod_cast h2
  have hmain : ∑ p ∈ y.primesBelow,
      (1/(k:ℝ)^2) * (1 - ((p:ℂ)^(Complex.I * (((k:ℝ)*s : ℝ):ℂ))).re) / p
      = (1/(k:ℝ)^2) * ((∑ p ∈ y.primesBelow, (1:ℝ)/p)
          - ∑ p ∈ y.primesBelow,
              ((p:ℂ)^(Complex.I * (((k:ℝ)*s:ℝ):ℂ))).re / p) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpp := Nat.prime_of_mem_primesBelow hp
    have hp0 : ((p:ℕ):ℝ) ≠ 0 := by
      have := hpp.pos
      positivity
    have hkne : ((k:ℝ))^2 ≠ 0 := by positivity
    field_simp
  rw [hmain]
  linarith [hite]

/-- **The zeta pretense bound**: the twisted prime sum is at most
`log log |t| - log log log |t|` plus absolute constants — Littlewood
strength, fully proved. -/
private theorem zeta_pretense_le {y : ℕ} (hy : 3 ≤ y) (t : ℝ) (ht : 1 ≤ |t|) :
    ∑ p ∈ y.primesBelow, ((p:ℂ) ^ (Complex.I * (t:ℂ))).re / p
      ≤ Real.log 8192 + Real.log (Real.log (|t|+2))
        - Real.log (Real.log (Real.log (|t|+2))) + 14 := by
  have hy3 : (3:ℝ) ≤ y := by exact_mod_cast hy
  have hy0 : (0:ℝ) < Real.log y := Real.log_pos (by linarith)
  have hlogy1 : (1:ℝ) < Real.log y := by
    rw [show (1:ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    refine Real.log_lt_log (Real.exp_pos 1) ?_
    linarith [Real.exp_one_lt_d9]
  have hσ1 : 1 < 1 + 1/Real.log y := by
    have h1 : (0:ℝ) < 1/Real.log y := by positivity
    linarith
  have hσ2 : 1 + 1/Real.log y ≤ 2 := by
    have h4 : 1/Real.log y ≤ 1 := by
      rw [div_le_one hy0]
      linarith
    linarith
  have hb := sum_re_twist_div_le_log_norm_LSeries (1 : DirichletCharacter ℂ 1)
    hy t
  have hχ1 : ∀ n : ℕ, ((1 : DirichletCharacter ℂ 1) ((n:ℕ) : ZMod 1)) = 1 :=
    fun n => MulChar.one_apply (isUnit_of_subsingleton _)
  have h5 : ∀ p ∈ y.primesBelow,
      ((1 : DirichletCharacter ℂ 1) ((p:ℕ) : ZMod 1)
        * (p:ℂ)^(Complex.I * (t:ℂ))).re / p
      = ((p:ℂ)^(Complex.I * (t:ℂ))).re / p := by
    intro p _
    rw [hχ1 p, one_mul]
  have h6 : LSeries (fun n => (1 : DirichletCharacter ℂ 1) ((n:ℕ) : ZMod 1))
      = LSeries (fun _ => 1) := by
    refine congrArg LSeries ?_
    funext n
    exact hχ1 n
  rw [Finset.sum_congr rfl h5, h6] at hb
  have hζ := zeta_LSeries_bound (1 + 1/Real.log y) t hσ1 hσ2 ht
  set w : ℝ := |t| + 2 with hwdef
  have hw3 : (3:ℝ) ≤ w := by
    rw [hwdef]
    linarith
  have hlogw : (1:ℝ) < Real.log w := by
    rw [show (1:ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    refine Real.log_lt_log (Real.exp_pos 1) ?_
    linarith [Real.exp_one_lt_d9]
  have hllw : (0:ℝ) < Real.log (Real.log w) := Real.log_pos hlogw
  rcases eq_or_lt_of_le (norm_nonneg (LSeries (fun _ => 1)
      (((1 + 1/Real.log y : ℝ):ℂ) - Complex.I * t))) with h0 | h0
  · rw [← h0, Real.log_zero] at hb
    have h7 : Real.log (Real.log (Real.log w))
        ≤ Real.log (Real.log w) - 1 :=
      Real.log_le_sub_one_of_pos hllw
    have h8 : (0:ℝ) ≤ Real.log 8192 := Real.log_nonneg (by norm_num)
    linarith [hb]
  · have h9 := Real.log_le_log h0 hζ
    have h10 : Real.log (8192 * Real.log w / Real.log (Real.log w))
        = Real.log 8192 + Real.log (Real.log w)
          - Real.log (Real.log (Real.log w)) := by
      rw [Real.log_div (by positivity) (by linarith),
        Real.log_mul (by norm_num) (by linarith)]
    rw [h10] at h9
    linarith [hb, h9]

set_option maxHeartbeats 1600000 in
/-- **The Vinogradov–Korobov interface, unconditionally**: every character
twist in the critical frequency range is pretentiously far from `1`,
eventually in `X` — proved outright from the elementary van der Corput
zeta bound. No assumption class remains on this leg. -/
instance (priority := 90) vinogradovKorobov_unconditional :
    VinogradovKorobovAssumption where
  twist_far := by
    intro Q T M hQ hT δ hδ0 hδ1
    set M₁ : ℝ := max M 1 with hM₁def
    have hM₁ : 1 ≤ M₁ := le_max_right _ _
    set E : ℝ := Q^2*(M₁+Q) + 15 + Real.log 8192 + 2*Real.log 2
      - Real.log (δ/2) with hEdef
    refine ⟨max (max ((3:ℝ)^(1/δ)) (Real.exp ((2/δ) * Real.log 2)))
      (max (max (Q*(T+2)) (Real.exp (Real.exp 1)))
        (max (Real.exp (1/δ^2)) (Real.exp (Real.exp (Real.exp E))))),
      fun X hX q χ hq hqQ s hs hsT => ?_⟩
    have hXa : (3:ℝ)^(1/δ) ≤ X :=
      le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hX)
    have hXc : Real.exp ((2/δ) * Real.log 2) ≤ X :=
      le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hX)
    have hXd : Q * (T+2) ≤ X :=
      le_trans (le_max_left _ _)
        (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX))
    have hXe : Real.exp (Real.exp 1) ≤ X :=
      le_trans (le_max_right _ _)
        (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX))
    have hXf : Real.exp (1/δ^2) ≤ X :=
      le_trans (le_max_left _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX))
    have hXg : Real.exp (Real.exp (Real.exp E)) ≤ X :=
      le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX))
    have hX1 : (1:ℝ) < X := lt_of_lt_of_le
      (by nlinarith [Real.add_one_le_exp (Real.exp 1), Real.exp_pos 1]) hXe
    have hX0 : (0:ℝ) < X := by linarith
    have hlogX : (1:ℝ) ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le hX0]
      calc Real.exp 1 ≤ Real.exp (Real.exp 1) :=
            Real.exp_le_exp.mpr (by linarith [Real.add_one_le_exp (1:ℝ)])
        _ ≤ X := hXe
    have hlogX0 : (0:ℝ) < Real.log X := by linarith
    have hloglogX : Real.exp 1 ≤ Real.log X := by
      rw [show Real.exp 1 = Real.log (Real.exp (Real.exp 1)) from
        (Real.log_exp _).symm]
      exact Real.log_le_log (Real.exp_pos _) hXe
    have hloglogX1 : (1:ℝ) ≤ Real.log (Real.log X) := by
      rw [Real.le_log_iff_exp_le hlogX0]
      exact hloglogX
    have hloglogX0 : (0:ℝ) < Real.log (Real.log X) := by linarith
    have hXd3 : (3:ℝ) ≤ X ^ δ := by
      calc (3:ℝ) = ((3:ℝ)^(1/δ))^δ := by
            rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3), one_div,
              inv_mul_cancel₀ (ne_of_gt hδ0), Real.rpow_one]
        _ ≤ X^δ := Real.rpow_le_rpow (by positivity) hXa hδ0.le
    set y : ℕ := ⌊X^δ⌋₊ with hy_def
    have hy3 : 3 ≤ y := Nat.le_floor (by exact_mod_cast hXd3)
    have hs3 : (3:ℝ) ≤ |s| := le_trans hXd3 hs
    have hs1 : (1:ℝ) ≤ |s| := by linarith
    have hyX : (X^δ) - 1 ≤ y := by
      rw [hy_def]
      have := Nat.sub_one_lt_floor (X^δ)
      linarith
    have hXd2 : (2:ℝ) ≤ X^δ := by linarith
    have hy_half : X^δ/2 ≤ y := by
      have h1 : X^δ/2 ≤ X^δ - 1 := by linarith
      linarith
    have hlogy : (δ/2) * Real.log X ≤ Real.log y := by
      have h1 : Real.log (X^δ/2) ≤ Real.log y :=
        Real.log_le_log (by positivity) hy_half
      have h2 : Real.log (X^δ/2) = δ * Real.log X - Real.log 2 := by
        rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hX0]
      have h3 : Real.log 2 ≤ (δ/2) * Real.log X := by
        have h4 : (2/δ) * Real.log 2 ≤ Real.log X := by
          rw [Real.le_log_iff_exp_le hX0]
          exact hXc
        have hδ2 : (0:ℝ) < δ/2 := by linarith
        calc Real.log 2 = (δ/2) * ((2/δ) * Real.log 2) := by field_simp
          _ ≤ (δ/2) * Real.log X := by nlinarith
      linarith
    have hlogy0 : (0:ℝ) < Real.log y := by
      have h1 : (0:ℝ) < (δ/2) * Real.log X := by nlinarith
      linarith
    have hloglogy : Real.log (δ/2) + Real.log (Real.log X)
        ≤ Real.log (Real.log y) := by
      have h1 : Real.log ((δ/2) * Real.log X) ≤ Real.log (Real.log y) :=
        Real.log_le_log (by nlinarith) hlogy
      rw [Real.log_mul (by linarith [hδ0] : δ/2 ≠ (0:ℝ)) (ne_of_gt hlogX0)] at h1
      exact h1
    haveI : NeZero q := ⟨by omega⟩
    set k := Fintype.card (ZMod q)ˣ with hkdef
    have hk1 : 1 ≤ k := Fintype.card_pos
    have hkq : k ≤ q := by
      rw [hkdef, ZMod.card_units_eq_totient]
      exact Nat.totient_le q
    have hk1R : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
    have hkQ : (k:ℝ) ≤ Q := by
      have h1 : (k:ℝ) ≤ q := by exact_mod_cast hkq
      linarith [hqQ]
    have hks : |(k:ℝ) * s| = (k:ℝ) * |s| := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ (k:ℝ))]
    have hks1 : 1 ≤ |(k:ℝ) * s| := by
      rw [hks]
      nlinarith
    have harg_le : (k:ℝ) * |s| + 2 ≤ Q*(T+2)*X := by
      have h1 : |s| ≤ T*X := hsT
      have h2 : (k:ℝ)*|s| ≤ Q*(T*X) := by nlinarith [abs_nonneg s]
      nlinarith
    have harg3 : (3:ℝ) ≤ (k:ℝ)*|s| + 2 := by nlinarith
    have hu_ub : Real.log (Real.log ((k:ℝ)*|s| + 2))
        ≤ Real.log 2 + Real.log (Real.log X) := by
      have h1 : Real.log ((k:ℝ)*|s| + 2) ≤ Real.log (Q*(T+2)*X) :=
        Real.log_le_log (by linarith) harg_le
      have h2 : Real.log (Q*(T+2)*X) = Real.log (Q*(T+2)) + Real.log X := by
        rw [Real.log_mul (by positivity) (ne_of_gt hX0)]
      have h3 : Real.log (Q*(T+2)) ≤ Real.log X :=
        Real.log_le_log (by positivity) hXd
      have h4 : Real.log ((k:ℝ)*|s| + 2) ≤ 2 * Real.log X := by linarith
      have h5 : (0:ℝ) < Real.log ((k:ℝ)*|s| + 2) := by
        have h6 := Real.log_le_log (show (0:ℝ) < 3 by norm_num) harg3
        have h7 : (1:ℝ) < Real.log 3 := by
          rw [Real.lt_log_iff_exp_lt (by norm_num)]
          linarith [Real.exp_one_lt_d9]
        linarith
      calc Real.log (Real.log ((k:ℝ)*|s|+2))
          ≤ Real.log (2 * Real.log X) := Real.log_le_log h5 h4
        _ = Real.log 2 + Real.log (Real.log X) := by
            rw [Real.log_mul (by norm_num) (ne_of_gt hlogX0)]
    have hu_lb : Real.log δ + Real.log (Real.log X)
        ≤ Real.log (Real.log ((k:ℝ)*|s| + 2)) := by
      have h1 : X^δ ≤ (k:ℝ)*|s| + 2 := by nlinarith [hs]
      have h3 : Real.log (X^δ) ≤ Real.log ((k:ℝ)*|s|+2) :=
        Real.log_le_log (by positivity) h1
      rw [Real.log_rpow hX0] at h3
      have h4 : (0:ℝ) < δ * Real.log X := by nlinarith
      have h5 : Real.log (δ * Real.log X)
          ≤ Real.log (Real.log ((k:ℝ)*|s|+2)) := Real.log_le_log h4 h3
      rw [Real.log_mul (ne_of_gt hδ0) (ne_of_gt hlogX0)] at h5
      exact h5
    have hδlog : -(Real.log (Real.log X)) / 2 ≤ Real.log δ := by
      have h1 : (1:ℝ)/δ^2 ≤ Real.log X := by
        rw [Real.le_log_iff_exp_le hX0]
        exact hXf
      have h2 : Real.log (1/δ^2) ≤ Real.log (Real.log X) :=
        Real.log_le_log (by positivity) h1
      rw [Real.log_div one_ne_zero (by positivity), Real.log_one,
        Real.log_pow] at h2
      push_cast at h2
      linarith
    have hu_half : Real.log (Real.log X) / 2
        ≤ Real.log (Real.log ((k:ℝ)*|s| + 2)) := by
      linarith [hu_lb, hδlog]
    have hlogu_lb : Real.log (Real.log (Real.log X)) - Real.log 2
        ≤ Real.log (Real.log (Real.log ((k:ℝ)*|s| + 2))) := by
      have h1 : (0:ℝ) < Real.log (Real.log X) / 2 := by linarith
      have h2 := Real.log_le_log h1 hu_half
      rw [Real.log_div (ne_of_gt hloglogX0) (by norm_num)] at h2
      linarith
    have hE3 : E ≤ Real.log (Real.log (Real.log X)) := by
      have h1 : Real.exp (Real.exp E) ≤ Real.log X := by
        rw [show Real.exp (Real.exp E)
            = Real.log (Real.exp (Real.exp (Real.exp E))) from
          (Real.log_exp _).symm]
        exact Real.log_le_log (Real.exp_pos _) hXg
      have h2 : Real.exp E ≤ Real.log (Real.log X) := by
        rw [show Real.exp E = Real.log (Real.exp (Real.exp E)) from
          (Real.log_exp _).symm]
        exact Real.log_le_log (Real.exp_pos _) h1
      rw [show E = Real.log (Real.exp E) from (Real.log_exp _).symm]
      exact Real.log_le_log (Real.exp_pos _) h2
    have hpret := zeta_pretense_le hy3 ((k:ℝ) * s) hks1
    rw [hks] at hpret
    have hfloor := log_log_le_sum_one_div_primesBelow (y := y) (by omega)
    set D : ℝ := (∑ p ∈ y.primesBelow, (1:ℝ)/p)
      - ∑ p ∈ y.primesBelow,
          ((p:ℂ)^(Complex.I * (((k:ℝ)*s:ℝ):ℂ))).re / p with hDdef
    have hcomp := distSq_ge q hq χ s y
    rw [← hkdef, ← hDdef] at hcomp
    have hDζ : Q^2 * (M₁ + Q) ≤ D := by
      have h1 : Real.log (δ/2) + Real.log (Real.log X) - 1
          ≤ ∑ p ∈ y.primesBelow, (1:ℝ)/p := by
        linarith [hloglogy, hfloor]
      have h2 : ∑ p ∈ y.primesBelow,
          ((p:ℂ)^(Complex.I * (((k:ℝ)*s:ℝ):ℂ))).re / p
          ≤ Real.log 8192 + (Real.log 2 + Real.log (Real.log X))
            - (Real.log (Real.log (Real.log X)) - Real.log 2) + 14 := by
        refine le_trans hpret ?_
        linarith [hu_ub, hlogu_lb]
      rw [hEdef] at hE3
      rw [hDdef]
      linarith [h1, h2, hE3]
    have hQ0 : (0:ℝ) < Q := by linarith
    have hk2Q : (k:ℝ)^2 ≤ Q^2 := by nlinarith
    have hk20 : (0:ℝ) < (k:ℝ)^2 := by positivity
    have hD0 : (0:ℝ) ≤ D := by nlinarith [hDζ]
    have hfrac : M₁ + Q ≤ (1/(k:ℝ)^2) * D := by
      have h1 : (1:ℝ)/Q^2 ≤ 1/(k:ℝ)^2 :=
        one_div_le_one_div_of_le hk20 hk2Q
      have h2 : (1/(Q:ℝ)^2) * D ≤ (1/(k:ℝ)^2) * D :=
        mul_le_mul_of_nonneg_right h1 hD0
      have h3 : (1/(Q:ℝ)^2) * (Q^2 * (M₁ + Q)) ≤ (1/(Q:ℝ)^2) * D :=
        mul_le_mul_of_nonneg_left hDζ (by positivity)
      have h4 : (1/(Q:ℝ)^2) * (Q^2 * (M₁ + Q)) = M₁ + Q := by
        field_simp
      linarith
    have hqR : (q:ℝ) ≤ Q := hqQ
    calc M ≤ M₁ := le_max_left _ _
      _ = (M₁ + Q) - Q := by ring
      _ ≤ (1/(k:ℝ)^2) * D - q := by linarith [hfrac, hqR]
      _ ≤ pretentiousDistSq (fun _ => 1) (charTwist q χ s) y := hcomp

end Tao2015

end MoltResearch
