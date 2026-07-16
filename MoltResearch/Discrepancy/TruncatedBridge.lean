import MoltResearch.Discrepancy.EulerLogBridge
import MoltResearch.Discrepancy.MertensFirst
import MoltResearch.Discrepancy.ChebyshevTail

/-!
# Discrepancy: the truncated Euler-product bridge

Track C, VK/Littlewood campaign (`Problems/tao2015_derivation_c.md`, issue #2935, W2d):
the assembly of W2a + W2b + W2c —

  `∑_{p<y} Re(χ(p) p^{it})/p ≤ log ‖L(χ, 1 + 1/log y − it)‖ + 13`.

Three losses, each `O(1)`: replacing the weights `1/p` by `p^{−σ}` (σ = 1 + 1/log y)
costs `(1/log y)·∑_{p<y} log p/p ≤ 4` (Mertens' first theorem, W2b); completing the
truncated sum to the full prime sum costs the tail `∑_{p≥y} p^{−σ} ≤ 8` (Chebyshev,
W2c); and the full prime sum is at most `log ‖L‖ + 1` (the Euler-product log bridge,
W2a).

This reduces the Vinogradov–Korobov pretense bound to an upper bound on `‖L‖` just
right of the `1`-line — the `LittlewoodLBoundAssumption` interface (W3).
-/

namespace MoltResearch

open Finset Complex

variable {N : ℕ}

/-- Norm bound for the prime summand (local copy of W2a's private lemma). -/
private theorem norm_summand_le (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) (p : Nat.Primes) :
    ‖χ (p : ℕ) * (p : ℂ) ^ (-s)‖ ≤ ((p : ℕ) : ℝ) ^ (-s.re) := by
  rw [norm_mul]
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.pos
  have hnorm : ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s).re := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hp0]
  rw [hnorm, neg_re]
  exact mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)

/-- **The truncated Euler-product bridge** (W2d): the pretense term of the
Vinogradov–Korobov interface is controlled by `log ‖L‖` just right of the `1`-line,
up to an absolute constant. -/
theorem sum_re_twist_div_le_log_norm_LSeries (χ : DirichletCharacter ℂ N)
    {y : ℕ} (hy : 3 ≤ y) (t : ℝ) :
    ∑ p ∈ y.primesBelow, (χ p * (p : ℂ) ^ (Complex.I * t)).re / p
      ≤ Real.log ‖LSeries (fun n => χ n) (((1 + 1 / Real.log y : ℝ) : ℂ) - Complex.I * t)‖
        + 13 := by
  classical
  set ε : ℝ := 1 / Real.log y with hε
  have hlogy : (1 : ℝ) < Real.log y := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    have h3 : (3 : ℝ) ≤ y := by exact_mod_cast hy
    linarith [Real.exp_one_lt_d9]
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hε1 : ε < 1 := by
    rw [hε, div_lt_one (by linarith)]
    exact hlogy
  set s : ℂ := ((1 + ε : ℝ) : ℂ) - Complex.I * t with hs_def
  have hsre : s.re = 1 + ε := by
    rw [hs_def]
    simp
  have hs1 : 1 < s.re := by rw [hsre]; linarith
  -- the prime summand and its facts
  set w : Nat.Primes → ℂ := fun p => χ (p : ℕ) * (p : ℂ) ^ (-s) with hw
  have hsum : Summable w := by
    have h := (summable_dirichletSummand χ hs1).of_norm
    exact h.subtype _
  have hsumnorm : Summable fun p : Nat.Primes => ‖w p‖ :=
    (summable_dirichletSummand χ hs1).subtype _
  -- pointwise: the twist against 1/p is the summand against p^{-σ}, plus weight error
  have hp_facts : ∀ p ∈ y.primesBelow, p.Prime ∧ 2 ≤ p ∧ p < y :=
    fun p hp => ⟨Nat.prime_of_mem_primesBelow hp,
      (Nat.prime_of_mem_primesBelow hp).two_le, Nat.lt_of_mem_primesBelow hp⟩
  -- the real-part identity: Re(w) at a prime is Re(twist)·p^{-(1+ε)}
  have hreid : ∀ (p : ℕ), p.Prime →
      (χ p * (p : ℂ) ^ (Complex.I * t)).re * (p : ℝ) ^ (-(1 + ε))
        = (χ p * (p : ℂ) ^ (-s)).re := by
    intro p hpp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hsplit : ((p : ℕ) : ℂ) ^ (-s)
        = ((p : ℂ) ^ (Complex.I * t)) * ((((p : ℝ) ^ (-(1 + ε)) : ℝ)) : ℂ) := by
      rw [Complex.ofReal_cpow hp0.le]
      push_cast
      rw [← Complex.cpow_add _ _ (by exact_mod_cast hpp.ne_zero)]
      congr 1
      rw [hs_def]
      push_cast
      ring
    rw [hsplit, ← mul_assoc]
    rw [Complex.mul_re]
    simp [Complex.ofReal_re, Complex.ofReal_im]
  -- weight comparison: 1/p − p^{-(1+ε)} ∈ [0, ε log p / p]
  have hweight : ∀ (p : ℕ), 2 ≤ p →
      0 ≤ 1 / (p : ℝ) - (p : ℝ) ^ (-(1 + ε))
        ∧ 1 / (p : ℝ) - (p : ℝ) ^ (-(1 + ε)) ≤ ε * Real.log p / p := by
    intro p hp2
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      linarith
    have hfact : (p : ℝ) ^ (-(1 + ε)) = (1 / p) * (p : ℝ) ^ (-ε) := by
      rw [show -(1 + ε) = -1 + -ε from by ring, Real.rpow_add hp0,
        Real.rpow_neg_one, one_div]
    have hexpform : (p : ℝ) ^ (-ε) = Real.exp (-(ε * Real.log p)) := by
      rw [Real.rpow_def_of_pos hp0]
      ring_nf
    have hlogp : (0 : ℝ) ≤ Real.log p :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt hp2)
    constructor
    · rw [hfact]
      have hle1 : (p : ℝ) ^ (-ε) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos
          (by exact_mod_cast Nat.one_le_of_lt hp2) (by linarith)
      have : (0 : ℝ) < 1 / p := by positivity
      nlinarith
    · rw [hfact, hexpform]
      have hexp : 1 - Real.exp (-(ε * Real.log p)) ≤ ε * Real.log p := by
        linarith [Real.add_one_le_exp (-(ε * Real.log p))]
      have h1p : (0 : ℝ) ≤ 1 / p := by positivity
      calc 1 / (p : ℝ) - 1 / p * Real.exp (-(ε * Real.log p))
          = (1 / p) * (1 - Real.exp (-(ε * Real.log p))) := by ring
        _ ≤ (1 / p) * (ε * Real.log p) := by nlinarith
        _ = ε * Real.log p / p := by ring
  -- the twist real parts are bounded by 1
  have htwist_le : ∀ (p : ℕ), p.Prime → |(χ p * (p : ℂ) ^ (Complex.I * t)).re| ≤ 1 := by
    intro p hpp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    refine le_trans (Complex.abs_re_le_norm _) ?_
    rw [norm_mul]
    have h1 : ‖((p : ℕ) : ℂ) ^ (Complex.I * t)‖ = 1 := by
      rw [show ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) from by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hp0]
      simp
    rw [h1, mul_one]
    exact χ.norm_le_one _
  -- STEP 1: pass from 1/p weights to p^{-(1+ε)} weights (cost ≤ 4)
  have hstep1 : ∑ p ∈ y.primesBelow, (χ p * (p : ℂ) ^ (Complex.I * t)).re / p
      ≤ (∑ p ∈ y.primesBelow, (χ p * (p : ℂ) ^ (-s)).re) + 4 := by
    have hper : ∀ p ∈ y.primesBelow,
        (χ p * (p : ℂ) ^ (Complex.I * t)).re / p
          ≤ (χ p * (p : ℂ) ^ (-s)).re + ε * Real.log p / p := by
      intro p hp
      obtain ⟨hpp, hp2, -⟩ := hp_facts p hp
      have hid := hreid p hpp
      obtain ⟨hw0, hwle⟩ := hweight p hp2
      have habs := htwist_le p hpp
      set R := (χ p * (p : ℂ) ^ (Complex.I * t)).re
      have hcomp : R / p - R * (p : ℝ) ^ (-(1 + ε))
          = R * (1 / p - (p : ℝ) ^ (-(1 + ε))) := by ring
      have hRbound : R * (1 / p - (p : ℝ) ^ (-(1 + ε))) ≤ ε * Real.log p / p := by
        calc R * (1 / p - (p : ℝ) ^ (-(1 + ε)))
            ≤ |R| * (1 / p - (p : ℝ) ^ (-(1 + ε))) := by
              have := le_abs_self R
              nlinarith
          _ ≤ 1 * (1 / p - (p : ℝ) ^ (-(1 + ε))) := by nlinarith
          _ ≤ ε * Real.log p / p := by linarith [hwle]
      rw [← hid]
      linarith [hcomp, hRbound]
    calc ∑ p ∈ y.primesBelow, (χ p * (p : ℂ) ^ (Complex.I * t)).re / p
        ≤ ∑ p ∈ y.primesBelow,
            ((χ p * (p : ℂ) ^ (-s)).re + ε * Real.log p / p) :=
          Finset.sum_le_sum hper
      _ = (∑ p ∈ y.primesBelow, (χ p * (p : ℂ) ^ (-s)).re)
            + ε * ∑ p ∈ y.primesBelow, Real.log p / p := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun p _ => by ring
      _ ≤ (∑ p ∈ y.primesBelow, (χ p * (p : ℂ) ^ (-s)).re) + 4 := by
          have hm := sum_log_div_primesBelow_le y
          have h4 : ε * ∑ p ∈ y.primesBelow, Real.log p / p ≤ 4 := by
            have hsum_nonneg : 0 ≤ ∑ p ∈ y.primesBelow, Real.log p / p := by
              refine Finset.sum_nonneg fun p hp => ?_
              obtain ⟨hpp, hp2, -⟩ := hp_facts p hp
              have h1 : (0 : ℝ) ≤ Real.log p :=
                Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt hp2)
              positivity
            calc ε * ∑ p ∈ y.primesBelow, Real.log p / p
                ≤ ε * (4 * Real.log y) := by nlinarith
              _ = 4 * (ε * Real.log y) := by ring
              _ = 4 := by
                  rw [hε]
                  field_simp
          linarith
  -- STEP 2: complete the truncated sum to the full prime tsum (cost ≤ 8)
  -- the finset of primes below y, as a finset of Nat.Primes
  set Sy : Finset Nat.Primes := y.primesBelow.attach.image
    (fun q => (⟨q.1, Nat.prime_of_mem_primesBelow q.2⟩ : Nat.Primes)) with hSy
  have hmemSy : ∀ P : Nat.Primes, P ∈ Sy ↔ (P : ℕ) < y := by
    intro P
    constructor
    · intro hP
      rw [hSy, Finset.mem_image] at hP
      obtain ⟨q, -, rfl⟩ := hP
      exact Nat.lt_of_mem_primesBelow q.2
    · intro hP
      rw [hSy, Finset.mem_image]
      exact ⟨⟨(P : ℕ), Nat.mem_primesBelow.mpr ⟨hP, P.prop⟩⟩,
        Finset.mem_attach _ _, Subtype.ext rfl⟩
  have hsum_eq : ∑ p ∈ y.primesBelow, (χ p * (p : ℂ) ^ (-s)).re
      = ∑ P ∈ Sy, (w P).re := by
    have h1 : ∑ P ∈ Sy, (w P).re
        = ∑ q ∈ y.primesBelow.attach, (χ q.1 * (q.1 : ℂ) ^ (-s)).re := by
      rw [hSy]
      exact Finset.sum_image fun q _ r _ h =>
        Subtype.ext (congrArg (Subtype.val : Nat.Primes → ℕ) h)
    have h2 : ∑ q ∈ y.primesBelow.attach, (χ q.1 * (q.1 : ℂ) ^ (-s)).re
        = ∑ p ∈ y.primesBelow, (χ p * (p : ℂ) ^ (-s)).re :=
      Finset.sum_attach y.primesBelow (fun p => (χ p * (p : ℂ) ^ (-s)).re)
    exact (h1.trans h2).symm
  -- split the full tsum
  have hsumRe : Summable fun P : Nat.Primes => (w P).re :=
    (Complex.hasSum_re hsum.hasSum).summable
  have htail_f : Summable fun P : Nat.Primes =>
      (if y ≤ (P : ℕ) then (w P).re else 0) := by
    refine Summable.of_norm_bounded (g := fun P : Nat.Primes => ‖w P‖) hsumnorm ?_
    intro P
    by_cases h : y ≤ (P : ℕ) <;> simp [h, Complex.abs_re_le_norm]
  have hhead_f : Summable fun P : Nat.Primes =>
      (if (P : ℕ) < y then (w P).re else 0) := by
    refine Summable.of_norm_bounded (g := fun P : Nat.Primes => ‖w P‖) hsumnorm ?_
    intro P
    by_cases h : (P : ℕ) < y <;> simp [h, Complex.abs_re_le_norm]
  have hsplit_pt : ∀ P : Nat.Primes,
      (w P).re = (if (P : ℕ) < y then (w P).re else 0)
        + (if y ≤ (P : ℕ) then (w P).re else 0) := by
    intro P
    by_cases h : (P : ℕ) < y
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  have hhead_eq : ∑' P : Nat.Primes, (if (P : ℕ) < y then (w P).re else 0)
      = ∑ P ∈ Sy, (w P).re := by
    rw [tsum_eq_sum (s := Sy) (fun P hP => if_neg (fun hlt => hP ((hmemSy P).mpr hlt)))]
    exact Finset.sum_congr rfl fun P hP => if_pos ((hmemSy P).mp hP)
  have htsum_split : ∑' P : Nat.Primes, (w P).re
      = (∑ P ∈ Sy, (w P).re)
        + ∑' P : Nat.Primes, (if y ≤ (P : ℕ) then (w P).re else 0) := by
    rw [← hhead_eq, ← Summable.tsum_add hhead_f htail_f]
    exact tsum_congr hsplit_pt
  -- the tail is at least −8
  have htail_ge : ∑' P : Nat.Primes, (if y ≤ (P : ℕ) then (w P).re else 0) ≥ -8 := by
    have hbound : ∀ P : Nat.Primes,
        -(if y ≤ (P : ℕ) then ((P : ℕ) : ℝ) ^ (-(1 + ε)) else 0)
          ≤ (if y ≤ (P : ℕ) then (w P).re else 0) := by
      intro P
      by_cases h : y ≤ (P : ℕ)
      · rw [if_pos h, if_pos h]
        have h1 : |(w P).re| ≤ ‖w P‖ := Complex.abs_re_le_norm _
        have h2 : ‖w P‖ ≤ ((P : ℕ) : ℝ) ^ (-s.re) := norm_summand_le χ hs1 P
        rw [hsre] at h2
        have := neg_abs_le (w P).re
        linarith
      · rw [if_neg h, if_neg h]
        simp
    have hsummable_tail : Summable fun P : Nat.Primes =>
        (if y ≤ (P : ℕ) then ((P : ℕ) : ℝ) ^ (-(1 + ε)) else 0) := by
      refine Summable.of_nonneg_of_le (fun P => by positivity) (fun P => ?_)
        (Nat.Primes.summable_rpow.mpr (show -(1 + ε) < -1 by linarith))
      by_cases h : y ≤ (P : ℕ)
      · rw [if_pos h]
      · rw [if_neg h]; positivity
    have htail8 := tsum_primes_tail_rpow_le hy
    rw [← hε] at htail8
    calc ∑' P : Nat.Primes, (if y ≤ (P : ℕ) then (w P).re else 0)
        ≥ ∑' P : Nat.Primes,
            -(if y ≤ (P : ℕ) then ((P : ℕ) : ℝ) ^ (-(1 + ε)) else 0) :=
          Summable.tsum_le_tsum hbound hsummable_tail.neg htail_f
      _ = -(∑' P : Nat.Primes,
            (if y ≤ (P : ℕ) then ((P : ℕ) : ℝ) ^ (-(1 + ε)) else 0)) := by
          rw [tsum_neg]
      _ ≥ -8 := neg_le_neg htail8
  -- STEP 3: the full prime sum against log ‖L‖ (W2a)
  have hbridge := tsum_re_dirichlet_le_log_norm_LSeries χ hs1
  -- assemble
  have hfull : ∑ P ∈ Sy, (w P).re
      ≤ Real.log ‖LSeries (fun n => χ n) s‖ + 1 + 8 := by
    have := htsum_split
    have h1 : ∑ P ∈ Sy, (w P).re
        = (∑' P : Nat.Primes, (w P).re)
          - ∑' P : Nat.Primes, (if y ≤ (P : ℕ) then (w P).re else 0) := by
      linarith
    rw [h1]
    have h2 : ∑' P : Nat.Primes, (w P).re ≤ Real.log ‖LSeries (fun n => χ n) s‖ + 1 :=
      hbridge
    linarith [htail_ge]
  have hLform : LSeries (fun n => χ n) s
      = LSeries (fun n => χ n) (((1 + 1 / Real.log y : ℝ) : ℂ) - Complex.I * t) := by
    rw [hs_def, hε]
  calc ∑ p ∈ y.primesBelow, (χ p * (p : ℂ) ^ (Complex.I * t)).re / p
      ≤ (∑ p ∈ y.primesBelow, (χ p * (p : ℂ) ^ (-s)).re) + 4 := hstep1
    _ = (∑ P ∈ Sy, (w P).re) + 4 := by rw [hsum_eq]
    _ ≤ (Real.log ‖LSeries (fun n => χ n) s‖ + 1 + 8) + 4 := by linarith [hfull]
    _ = Real.log ‖LSeries (fun n => χ n)
          (((1 + 1 / Real.log y : ℝ) : ℂ) - Complex.I * t)‖ + 13 := by
        rw [hLform]
        ring

end MoltResearch
