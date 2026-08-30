/-
# Window Turán–Kubilius substrate (Track R, A2-III, N3-h)

The in-tree Turán–Kubilius and sift bounds (`TuranKubilius.lean`,
`TypicalFactorization.lean`) run on the global range `Ico 1 N`.  The
band-energy schedule prices the atypical complement *per block*
`(A, A+Δ]`, so it needs the first/second prime moments and the sifted
log-average on a window — with errors measured against the window
harmonic mass, not `log N`.

This file builds that substrate from the exact fibre reindex: the
`d`-multiples of a window are the dilated quotient window, so every
moment computation reduces to comparing harmonic masses of quotient
windows.
-/
import MoltResearch.Discrepancy.TuranKubilius
import MoltResearch.Discrepancy.RamareIdentity
import MoltResearch.Discrepancy.PlancherelHarness
import MoltResearch.Discrepancy.TypicalFactorization

namespace MoltResearch

open Finset

/-- **The window divisibility reindex, exactly** (Track R, A2-III,
N3-h0): the harmonic mass of the `d`-multiples in a window is `1/d`
times the harmonic mass of the quotient window — an identity, no
error term.  Every window moment computation reduces to this. -/
theorem sum_one_div_Ioc_dvd_eq (A B d : ℕ) (hd : 0 < d) :
    ∑ n ∈ (Finset.Ioc A B).filter (fun n => d ∣ n), (1:ℝ)/n
      = (1/(d:ℝ)) * ∑ k ∈ Finset.Ioc (A/d) (B/d), (1:ℝ)/k := by
  classical
  rw [sum_filter_dvd_eq_sum_image (Finset.Ioc A B) hd (fun n => (1:ℝ)/n)]
  have himg : ((Finset.Ioc A B).filter (fun n => d ∣ n)).image (· / d)
      = Finset.Ioc (A/d) (B/d) := by
    refine le_antisymm
      (image_div_fibre_subset A B (Finset.Ioc A B)
        (Finset.Subset.refl _) hd) ?_
    intro k hk
    rw [Finset.mem_Ioc] at hk
    rw [Finset.mem_image]
    refine ⟨d*k, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Ioc]
      have h1 : A < k * d := (Nat.div_lt_iff_lt_mul hd).mp hk.1
      have h2 : k * d ≤ B := (Nat.le_div_iff_mul_le hd).mp hk.2
      refine ⟨⟨?_, ?_⟩, ⟨k, rfl⟩⟩
      · rw [mul_comm d k]
        exact h1
      · rw [mul_comm d k]
        exact h2
    · rw [Nat.mul_div_cancel_left k hd]
  rw [himg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_Ioc] at hk
  have hk0 : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hk.1
  have hkc : ((k:ℝ)) ≠ 0 := by exact_mod_cast hk0.ne'
  have hdc : ((d:ℝ)) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp


/-- **The windowed harmonic floor** (Track R, A2-III, N3-h1a): the
window log-ratio lower bound `log b − log a ≤ ∑_{a ≤ m < b} 1/m` —
the missing partner of `sum_one_div_Ico_window_le`, by the same
telescoping `log(m+1) − log m ≤ 1/m` step. -/
theorem log_sub_log_le_sum_one_div_Ico (a b : ℕ) (ha : 1 ≤ a) :
    Real.log b - Real.log a ≤ ∑ m ∈ Finset.Ico a b, (1:ℝ)/m := by
  induction b with
  | zero =>
      simp only [Nat.cast_zero, Real.log_zero, Finset.Ico_eq_empty_of_le
        (Nat.zero_le a), Finset.sum_empty]
      have h0 : (0:ℝ) ≤ Real.log a :=
        Real.log_nonneg (by exact_mod_cast ha)
      linarith
  | succ m ih =>
      rcases Nat.lt_or_ge m a with hma | hma
      · -- `b = m+1 ≤ a`: empty or singleton-degenerate window
        rcases Nat.lt_or_ge (m+1) a with hm1a | hm1a
        · rw [Finset.Ico_eq_empty_of_le (by omega)]
          simp only [Finset.sum_empty]
          have hlog : Real.log (m+1 : ℕ) ≤ Real.log a := by
            have : ((m+1 : ℕ):ℝ) ≤ (a:ℝ) := by exact_mod_cast hm1a.le
            exact Real.log_le_log (by positivity) this
          push_cast at hlog ⊢
          linarith
        · have hae : a = m+1 := by omega
          rw [hae]
          simp
      · -- `a ≤ m`: peel the top element
        rw [Finset.sum_Ico_succ_top hma]
        have hm0 : (0:ℝ) < m := by
          have : (1:ℕ) ≤ m := le_trans ha hma
          exact_mod_cast this
        have hstep : Real.log ((m:ℝ)+1) - Real.log m ≤ 1/m := by
          rw [← Real.log_div (by positivity) (ne_of_gt hm0)]
          have h1 : ((m:ℝ)+1)/m = 1 + 1/m := by field_simp
          have h2 := Real.log_le_sub_one_of_pos
            (x := ((m:ℝ)+1)/m) (by positivity)
          rw [h1] at h2 ⊢
          linarith
        have ihm := ih
        push_cast
        push_cast at ihm
        linarith


set_option maxHeartbeats 1600000 in
/-- **The quotient window has the same harmonic mass** (Track R,
A2-III, N3-h1b): dividing a window `(A, B]` by `d ≤ A` moves its
harmonic mass by at most `3d/A` — the two-sided log bracket on both
windows, with the floor error `d·(⌊x/d⌋+1) ∈ (x, x+d]` absorbed into
one `log(1+d/x) ≤ d/x` step each.  Combined with the exact reindex
`sum_one_div_Ioc_dvd_eq`, every prime moment on a window is the
prime's harmonic weight times the window mass, up to `3/A` per
prime. -/
theorem sum_one_div_Ioc_div_sub_le (A B d : ℕ) (hd : 0 < d)
    (hdA : d ≤ A) (hAB : A ≤ B) :
    |(∑ k ∈ Finset.Ioc (A/d) (B/d), (1:ℝ)/k)
        - ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n| ≤ 3*((d:ℝ)/A) := by
  have hA0 : (0:ℝ) < A := by
    have : (1:ℕ) ≤ A := le_trans hd hdA
    exact_mod_cast this
  have hB0 : (0:ℝ) < B := lt_of_lt_of_le hA0 (by exact_mod_cast hAB)
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hdmA := Nat.div_add_mod A d
  have hmodA := Nat.mod_lt A hd
  have hdmB := Nat.div_add_mod B d
  have hmodB := Nat.mod_lt B hd
  have hab' : A/d ≤ B/d := Nat.div_le_div_right hAB
  have hIco1 : Finset.Ioc A B = Finset.Ico (A+1) (B+1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have hIco2 : Finset.Ioc (A/d) (B/d) = Finset.Ico (A/d+1) (B/d+1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have hU1 : ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n
      ≤ 1/((A:ℝ)+1) + Real.log ((B:ℝ)+1) - Real.log ((A:ℝ)+1) := by
    rw [hIco1]
    have := ExpSums.sum_one_div_Ico_window_le (A+1) (B+1)
      (Nat.succ_le_succ (Nat.zero_le _)) (Nat.succ_le_succ hAB)
    push_cast at this ⊢
    linarith
  have hL1 : Real.log ((B:ℝ)+1) - Real.log ((A:ℝ)+1)
      ≤ ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n := by
    rw [hIco1]
    have := log_sub_log_le_sum_one_div_Ico (A+1) (B+1)
      (Nat.succ_le_succ (Nat.zero_le _))
    push_cast at this ⊢
    linarith
  have hU2 : ∑ k ∈ Finset.Ioc (A/d) (B/d), (1:ℝ)/k
      ≤ 1/(((A/d : ℕ):ℝ)+1) + Real.log (((B/d : ℕ):ℝ)+1)
        - Real.log (((A/d : ℕ):ℝ)+1) := by
    rw [hIco2]
    have := ExpSums.sum_one_div_Ico_window_le (A/d+1) (B/d+1)
      (Nat.succ_le_succ (Nat.zero_le _)) (Nat.succ_le_succ hab')
    push_cast at this ⊢
    linarith
  have hL2 : Real.log (((B/d : ℕ):ℝ)+1) - Real.log (((A/d : ℕ):ℝ)+1)
      ≤ ∑ k ∈ Finset.Ioc (A/d) (B/d), (1:ℝ)/k := by
    rw [hIco2]
    have := log_sub_log_le_sum_one_div_Ico (A/d+1) (B/d+1)
      (Nat.succ_le_succ (Nat.zero_le _))
    push_cast at this ⊢
    linarith
  have hcastB : ((d*(B/d) + d : ℕ):ℝ) = (d:ℝ)*(((B/d : ℕ):ℝ)+1) := by
    push_cast
    ring
  have hcastA : ((d*(A/d) + d : ℕ):ℝ) = (d:ℝ)*(((A/d : ℕ):ℝ)+1) := by
    push_cast
    ring
  have hb1 : ((B:ℝ)+1) ≤ (d:ℝ)*(((B/d : ℕ):ℝ)+1) := by
    have h1 : B + 1 ≤ d*(B/d) + d := by omega
    calc ((B:ℝ)+1) ≤ ((d*(B/d) + d : ℕ):ℝ) := by exact_mod_cast h1
      _ = (d:ℝ)*(((B/d : ℕ):ℝ)+1) := hcastB
  have hb2 : (d:ℝ)*(((B/d : ℕ):ℝ)+1) ≤ (B:ℝ)+d := by
    have h1 : d*(B/d) + d ≤ B + d := by omega
    calc (d:ℝ)*(((B/d : ℕ):ℝ)+1) = ((d*(B/d) + d : ℕ):ℝ) := hcastB.symm
      _ ≤ ((B + d : ℕ):ℝ) := by exact_mod_cast h1
      _ = (B:ℝ)+d := by push_cast; ring
  have ha1 : ((A:ℝ)+1) ≤ (d:ℝ)*(((A/d : ℕ):ℝ)+1) := by
    have h1 : A + 1 ≤ d*(A/d) + d := by omega
    calc ((A:ℝ)+1) ≤ ((d*(A/d) + d : ℕ):ℝ) := by exact_mod_cast h1
      _ = (d:ℝ)*(((A/d : ℕ):ℝ)+1) := hcastA
  have ha2 : (d:ℝ)*(((A/d : ℕ):ℝ)+1) ≤ (A:ℝ)+d := by
    have h1 : d*(A/d) + d ≤ A + d := by omega
    calc (d:ℝ)*(((A/d : ℕ):ℝ)+1) = ((d*(A/d) + d : ℕ):ℝ) := hcastA.symm
      _ ≤ ((A + d : ℕ):ℝ) := by exact_mod_cast h1
      _ = (A:ℝ)+d := by push_cast; ring
  have hq0 : (0:ℝ) < ((A/d : ℕ):ℝ)+1 := by positivity
  have hqB0 : (0:ℝ) < ((B/d : ℕ):ℝ)+1 := by positivity
  have hsplitB : Real.log ((d:ℝ)*(((B/d : ℕ):ℝ)+1))
      = Real.log d + Real.log (((B/d : ℕ):ℝ)+1) :=
    Real.log_mul (ne_of_gt hd0) (ne_of_gt hqB0)
  have hsplitA : Real.log ((d:ℝ)*(((A/d : ℕ):ℝ)+1))
      = Real.log d + Real.log (((A/d : ℕ):ℝ)+1) :=
    Real.log_mul (ne_of_gt hd0) (ne_of_gt hq0)
  have hlogB_lo : Real.log ((B:ℝ)+1)
      ≤ Real.log ((d:ℝ)*(((B/d : ℕ):ℝ)+1)) :=
    Real.log_le_log (by positivity) hb1
  have hlogB_hi : Real.log ((d:ℝ)*(((B/d : ℕ):ℝ)+1))
      ≤ Real.log ((B:ℝ)+d) :=
    Real.log_le_log (by positivity) hb2
  have hlogA_lo : Real.log ((A:ℝ)+1)
      ≤ Real.log ((d:ℝ)*(((A/d : ℕ):ℝ)+1)) :=
    Real.log_le_log (by positivity) ha1
  have hlogA_hi : Real.log ((d:ℝ)*(((A/d : ℕ):ℝ)+1))
      ≤ Real.log ((A:ℝ)+d) :=
    Real.log_le_log (by positivity) ha2
  have hedgeB : Real.log ((B:ℝ)+d) - Real.log ((B:ℝ)+1) ≤ (d:ℝ)/A := by
    have h1 := Real.log_le_sub_one_of_pos
      (x := ((B:ℝ)+d)/((B:ℝ)+1)) (by positivity)
    rw [← Real.log_div (by positivity) (by positivity)]
    have h2 : ((B:ℝ)+d)/((B:ℝ)+1) - 1 = ((d:ℝ)-1)/((B:ℝ)+1) := by
      field_simp
      ring
    have h3 : ((d:ℝ)-1)/((B:ℝ)+1) ≤ (d:ℝ)/A := by
      rw [div_le_div_iff₀ (by positivity) hA0]
      nlinarith [hA0, hB0, hd0, (by exact_mod_cast hAB : (A:ℝ) ≤ B)]
    linarith
  have hedgeA : Real.log ((A:ℝ)+d) - Real.log ((A:ℝ)+1) ≤ (d:ℝ)/A := by
    have h1 := Real.log_le_sub_one_of_pos
      (x := ((A:ℝ)+d)/((A:ℝ)+1)) (by positivity)
    rw [← Real.log_div (by positivity) (by positivity)]
    have h2 : ((A:ℝ)+d)/((A:ℝ)+1) - 1 = ((d:ℝ)-1)/((A:ℝ)+1) := by
      field_simp
      ring
    have h3 : ((d:ℝ)-1)/((A:ℝ)+1) ≤ (d:ℝ)/A := by
      rw [div_le_div_iff₀ (by positivity) hA0]
      nlinarith [hA0, hd0]
    linarith
  have hrecq : 1/(((A/d : ℕ):ℝ)+1) ≤ (d:ℝ)/A := by
    rw [div_le_div_iff₀ hq0 hA0]
    nlinarith [ha1, hd0, hA0]
  have hrecA : 1/((A:ℝ)+1) ≤ (d:ℝ)/A := by
    rw [div_le_div_iff₀ (by positivity) hA0]
    nlinarith [hA0, hd0]
  have hdA0 : (0:ℝ) ≤ (d:ℝ)/A := by positivity
  rw [abs_le]
  constructor
  · have hD : Real.log ((A:ℝ)+1) - Real.log ((A:ℝ)+d)
        ≤ (Real.log (((B/d : ℕ):ℝ)+1) - Real.log (((A/d : ℕ):ℝ)+1))
          - (Real.log ((B:ℝ)+1) - Real.log ((A:ℝ)+1)) := by
      have e1 : Real.log (((B/d : ℕ):ℝ)+1)
          = Real.log ((d:ℝ)*(((B/d : ℕ):ℝ)+1)) - Real.log d := by
        rw [hsplitB]
        ring
      have e2 : Real.log (((A/d : ℕ):ℝ)+1)
          = Real.log ((d:ℝ)*(((A/d : ℕ):ℝ)+1)) - Real.log d := by
        rw [hsplitA]
        ring
      rw [e1, e2]
      linarith [hlogB_lo, hlogA_hi]
    have hs1 : (Real.log (((B/d : ℕ):ℝ)+1) - Real.log (((A/d : ℕ):ℝ)+1))
          - (1/((A:ℝ)+1) + Real.log ((B:ℝ)+1) - Real.log ((A:ℝ)+1))
        ≤ (∑ k ∈ Finset.Ioc (A/d) (B/d), (1:ℝ)/k)
          - ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n := by
      linarith [hL2, hU1]
    have hs2 : -((d:ℝ)/A) - (d:ℝ)/A
        ≤ (Real.log (((B/d : ℕ):ℝ)+1) - Real.log (((A/d : ℕ):ℝ)+1))
          - (1/((A:ℝ)+1) + Real.log ((B:ℝ)+1) - Real.log ((A:ℝ)+1)) := by
      linarith [hD, hedgeA, hrecA]
    linarith [hs1, hs2, hdA0]
  · have hD : (Real.log (((B/d : ℕ):ℝ)+1) - Real.log (((A/d : ℕ):ℝ)+1))
          - (Real.log ((B:ℝ)+1) - Real.log ((A:ℝ)+1))
        ≤ Real.log ((B:ℝ)+d) - Real.log ((B:ℝ)+1) := by
      have e1 : Real.log (((B/d : ℕ):ℝ)+1)
          = Real.log ((d:ℝ)*(((B/d : ℕ):ℝ)+1)) - Real.log d := by
        rw [hsplitB]
        ring
      have e2 : Real.log (((A/d : ℕ):ℝ)+1)
          = Real.log ((d:ℝ)*(((A/d : ℕ):ℝ)+1)) - Real.log d := by
        rw [hsplitA]
        ring
      rw [e1, e2]
      linarith [hlogB_hi, hlogA_lo]
    have hs1 : (∑ k ∈ Finset.Ioc (A/d) (B/d), (1:ℝ)/k)
        - ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n
        ≤ (1/(((A/d : ℕ):ℝ)+1) + Real.log (((B/d : ℕ):ℝ)+1)
            - Real.log (((A/d : ℕ):ℝ)+1))
          - (Real.log ((B:ℝ)+1) - Real.log ((A:ℝ)+1)) := by
      linarith [hU2, hL1]
    have hs2 : (1/(((A/d : ℕ):ℝ)+1) + Real.log (((B/d : ℕ):ℝ)+1)
            - Real.log (((A/d : ℕ):ℝ)+1))
          - (Real.log ((B:ℝ)+1) - Real.log ((A:ℝ)+1))
        ≤ (d:ℝ)/A + (d:ℝ)/A := by
      linarith [hD, hedgeB, hrecq]
    linarith [hs1, hs2, hdA0]


/-- **The window first prime moment** (Track R, A2-III, N3-h2): over a
window `(A, B]`, the log-averaged prime-divisor count sits within
`3·#P/A` of the prime harmonic mass times the window mass —

  `|∑_{A<n≤B} ω_P(n)/n − (∑_p 1/p)·∑_{A<n≤B} 1/n| ≤ 3·#P/A`,

by the exact fibre reindex and the quotient-window comparison, one
prime at a time.  This is the windowed Turán–Kubilius first moment. -/
theorem window_omega_first_moment (A B : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPA : ∀ p ∈ P, p ≤ A) (hAB : A ≤ B) :
    |(∑ n ∈ Finset.Ioc A B, ((P.filter (· ∣ n)).card : ℝ)/n)
        - (∑ p ∈ P, (1:ℝ)/p) * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n|
      ≤ 3*((P.card : ℝ)/A) := by
  classical
  -- the count splits into prime fibres
  have hswap : ∑ n ∈ Finset.Ioc A B, ((P.filter (· ∣ n)).card : ℝ)/n
      = ∑ p ∈ P, ∑ n ∈ (Finset.Ioc A B).filter (fun n => p ∣ n),
          (1:ℝ)/n := by
    have h1 : ∀ n ∈ Finset.Ioc A B,
        ((P.filter (· ∣ n)).card : ℝ)/n
          = ∑ p ∈ P, (if p ∣ n then (1:ℝ)/n else 0) := by
      intro n _
      rw [Finset.card_filter]
      push_cast
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun p _ => ?_
      split_ifs <;> simp
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_filter]
  rw [hswap, Finset.sum_mul, ← Finset.sum_sub_distrib]
  -- the per-prime deviation
  have hper : ∀ p ∈ P,
      |(∑ n ∈ (Finset.Ioc A B).filter (fun n => p ∣ n), (1:ℝ)/n)
          - (1:ℝ)/p * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n|
        ≤ 3*((1:ℝ)/A) := by
    intro p hp
    have hp0 : 0 < p := (hP p hp).pos
    have hpr : (0:ℝ) < p := by exact_mod_cast hp0
    have hA1 : 1 ≤ A := le_trans hp0 (hPA p hp)
    have hA0 : (0:ℝ) < A := by exact_mod_cast hA1
    rw [sum_one_div_Ioc_dvd_eq A B p hp0]
    have hcomp := sum_one_div_Ioc_div_sub_le A B p hp0 (hPA p hp) hAB
    have hfac : (1:ℝ)/p * (∑ k ∈ Finset.Ioc (A/p) (B/p), (1:ℝ)/k)
          - (1:ℝ)/p * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n
        = (1:ℝ)/p * ((∑ k ∈ Finset.Ioc (A/p) (B/p), (1:ℝ)/k)
          - ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n) := by
      ring
    rw [hfac, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (1:ℝ)/p)]
    have hstep := mul_le_mul_of_nonneg_left hcomp
      (by positivity : (0:ℝ) ≤ (1:ℝ)/p)
    have hcan : (1:ℝ)/p * (3*((p:ℝ)/A)) = 3*((1:ℝ)/A) := by
      field_simp
    linarith [hstep, hcan.le, hcan.ge]
  -- triangle and count
  calc |∑ p ∈ P, ((∑ n ∈ (Finset.Ioc A B).filter (fun n => p ∣ n),
          (1:ℝ)/n) - (1:ℝ)/p * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n)|
      ≤ ∑ p ∈ P, |(∑ n ∈ (Finset.Ioc A B).filter (fun n => p ∣ n),
          (1:ℝ)/n) - (1:ℝ)/p * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ P, 3*((1:ℝ)/A) := Finset.sum_le_sum hper
    _ = (P.card : ℝ) * (3*((1:ℝ)/A)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = 3*((P.card : ℝ)/A) := by
        ring


/-- **The window second-moment expansion** (Track R, A2-III, N3-h3a):
the squared prime-divisor count expands into pair fibres —

  `∑ ω_P(n)²/n = ∑_{p,q ∈ P} ∑_{n ∈ (A,B], p∣n, q∣n} 1/n`,

pure counting, no primality: `ω² = (∑_p [p∣n])²` opened by
`Finset.sum_mul_sum` and the `n`-sum swapped inside. -/
theorem window_omega_sq_expand (A B : ℕ) (P : Finset ℕ) :
    ∑ n ∈ Finset.Ioc A B, (((P.filter (· ∣ n)).card : ℝ))^2/n
      = ∑ p ∈ P, ∑ q ∈ P, ∑ n ∈ (Finset.Ioc A B).filter
          (fun n => p ∣ n ∧ q ∣ n), (1:ℝ)/n := by
  classical
  have h1 : ∀ n ∈ Finset.Ioc A B,
      (((P.filter (· ∣ n)).card : ℝ))^2/n
        = ∑ p ∈ P, ∑ q ∈ P,
            (if p ∣ n ∧ q ∣ n then (1:ℝ)/n else 0) := by
    intro n _
    rw [Finset.card_filter]
    push_cast
    rw [pow_two, Finset.sum_mul_sum]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs with h₁ h₂ h₃ <;> simp_all
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_filter]


/-- **Distinct-prime pair fibres are product fibres** (Track R,
A2-III): for primes `p ≠ q`, divisibility by both is divisibility by
`pq` — the coprimality step that turns the second-moment pair fibres
into single reindexable fibres. -/
theorem filter_dvd_pair_eq (A B : ℕ) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    (Finset.Ioc A B).filter (fun n => p ∣ n ∧ q ∣ n)
      = (Finset.Ioc A B).filter (fun n => (p*q) ∣ n) := by
  classical
  refine Finset.filter_congr fun n _ => ?_
  constructor
  · rintro ⟨h1, h2⟩
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
      ((Nat.coprime_primes hp hq).mpr hne) h1 h2
  · intro h
    exact ⟨dvd_trans (dvd_mul_right p q) h,
      dvd_trans (dvd_mul_left q p) h⟩

/-- **The window second prime moment** (Track R, A2-III, N3-h3b): over
a window `(A, B]` with all prime products `pq ≤ A`, the log-averaged
squared divisor count sits within `3(#P + #P²)/A` of its main term —

  `|∑ ω_P(n)²/n − (E + ∑_{p≠q} 1/(pq))·∑ 1/n| ≤ 3(#P + #P²)/A`,

by the pair expansion, the diagonal/off-diagonal split, and the
generic-modulus fibre deviation (`3/A` per modulus).  The windowed
Turán–Kubilius second moment. -/
theorem window_omega_sq_first_moment (A B : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPA2 : ∀ p ∈ P, ∀ q ∈ P, p*q ≤ A)
    (hAB : A ≤ B) :
    |(∑ n ∈ Finset.Ioc A B, (((P.filter (· ∣ n)).card : ℝ))^2/n)
        - ((∑ p ∈ P, (1:ℝ)/p)
            + ∑ p ∈ P, ∑ q ∈ P.erase p, (1:ℝ)/((p:ℝ)*q))
          * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n|
      ≤ 3*(((P.card : ℝ) + ((P.card : ℝ))^2)/A) := by
  classical
  -- generic modulus deviation
  have hdev : ∀ d : ℕ, 0 < d → d ≤ A →
      |(∑ n ∈ (Finset.Ioc A B).filter (fun n => d ∣ n), (1:ℝ)/n)
          - (1:ℝ)/d * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n|
        ≤ 3*((1:ℝ)/A) := by
    intro d hd0 hdA
    rw [sum_one_div_Ioc_dvd_eq A B d hd0]
    have hcomp := sum_one_div_Ioc_div_sub_le A B d hd0 hdA hAB
    have hdr : (0:ℝ) < d := by exact_mod_cast hd0
    have hfac : (1:ℝ)/d * (∑ k ∈ Finset.Ioc (A/d) (B/d), (1:ℝ)/k)
          - (1:ℝ)/d * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n
        = (1:ℝ)/d * ((∑ k ∈ Finset.Ioc (A/d) (B/d), (1:ℝ)/k)
          - ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n) := by
      ring
    rw [hfac, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (1:ℝ)/d)]
    have hstep := mul_le_mul_of_nonneg_left hcomp
      (by positivity : (0:ℝ) ≤ (1:ℝ)/d)
    have hA0 : (0:ℝ) < A := by
      have : (1:ℕ) ≤ A := le_trans hd0 hdA
      exact_mod_cast this
    have hcan : (1:ℝ)/d * (3*((d:ℝ)/A)) = 3*((1:ℝ)/A) := by
      field_simp
    linarith [hstep, hcan.le, hcan.ge]
  rw [window_omega_sq_expand]
  -- reorganize both sides per `p`
  have hexp : ∀ p ∈ P, ∑ q ∈ P, ∑ n ∈ (Finset.Ioc A B).filter
        (fun n => p ∣ n ∧ q ∣ n), (1:ℝ)/n
      = (∑ n ∈ (Finset.Ioc A B).filter (fun n => p ∣ n), (1:ℝ)/n)
        + ∑ q ∈ P.erase p, ∑ n ∈ (Finset.Ioc A B).filter
            (fun n => (p*q) ∣ n), (1:ℝ)/n := by
    intro p hp
    rw [← Finset.add_sum_erase P _ hp]
    congr 1
    · refine Finset.sum_congr (Finset.filter_congr fun n _ => ?_) fun _ _ => rfl
      simp
    · refine Finset.sum_congr rfl fun q hq => ?_
      rw [Finset.mem_erase] at hq
      rw [filter_dvd_pair_eq A B (hP p hp) (hP q hq.2) (Ne.symm hq.1)]
  have hmain : ((∑ p ∈ P, (1:ℝ)/p)
        + ∑ p ∈ P, ∑ q ∈ P.erase p, (1:ℝ)/((p:ℝ)*q))
      * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n
      = ∑ p ∈ P, ((1:ℝ)/p * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n
        + ∑ q ∈ P.erase p, (1:ℝ)/((p:ℝ)*q)
            * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n) := by
    rw [add_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl hexp, hmain, ← Finset.sum_sub_distrib]
  -- per-`p` deviations
  have hper : ∀ p ∈ P,
      |((∑ n ∈ (Finset.Ioc A B).filter (fun n => p ∣ n), (1:ℝ)/n)
          + ∑ q ∈ P.erase p, ∑ n ∈ (Finset.Ioc A B).filter
              (fun n => (p*q) ∣ n), (1:ℝ)/n)
        - ((1:ℝ)/p * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n
          + ∑ q ∈ P.erase p, (1:ℝ)/((p:ℝ)*q)
              * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n)|
        ≤ 3*((1:ℝ)/A) + (P.card : ℝ) * (3*((1:ℝ)/A)) := by
    intro p hp
    have hp0 : 0 < p := (hP p hp).pos
    have hpA : p ≤ A :=
      le_trans (Nat.le_mul_of_pos_left p hp0) (hPA2 p hp p hp)
    have hdiag := hdev p hp0 hpA
    have hoff : ∀ q ∈ P.erase p,
        |(∑ n ∈ (Finset.Ioc A B).filter (fun n => (p*q) ∣ n), (1:ℝ)/n)
            - (1:ℝ)/((p:ℝ)*q) * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n|
          ≤ 3*((1:ℝ)/A) := by
      intro q hq
      rw [Finset.mem_erase] at hq
      have hq0 : 0 < q := (hP q hq.2).pos
      have hcast : (1:ℝ)/((p:ℝ)*q) = (1:ℝ)/((p*q : ℕ):ℝ) := by
        push_cast
        ring
      rw [hcast]
      exact hdev (p*q) (Nat.mul_pos hp0 hq0) (hPA2 p hp q hq.2)
    have htri : |((∑ n ∈ (Finset.Ioc A B).filter (fun n => p ∣ n),
            (1:ℝ)/n)
          + ∑ q ∈ P.erase p, ∑ n ∈ (Finset.Ioc A B).filter
              (fun n => (p*q) ∣ n), (1:ℝ)/n)
        - ((1:ℝ)/p * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n
          + ∑ q ∈ P.erase p, (1:ℝ)/((p:ℝ)*q)
              * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n)|
        ≤ |(∑ n ∈ (Finset.Ioc A B).filter (fun n => p ∣ n), (1:ℝ)/n)
            - (1:ℝ)/p * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n|
          + ∑ q ∈ P.erase p,
            |(∑ n ∈ (Finset.Ioc A B).filter (fun n => (p*q) ∣ n),
                (1:ℝ)/n)
              - (1:ℝ)/((p:ℝ)*q) * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n| := by
      have hrw : ((∑ n ∈ (Finset.Ioc A B).filter (fun n => p ∣ n),
            (1:ℝ)/n)
          + ∑ q ∈ P.erase p, ∑ n ∈ (Finset.Ioc A B).filter
              (fun n => (p*q) ∣ n), (1:ℝ)/n)
        - ((1:ℝ)/p * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n
          + ∑ q ∈ P.erase p, (1:ℝ)/((p:ℝ)*q)
              * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n)
          = ((∑ n ∈ (Finset.Ioc A B).filter (fun n => p ∣ n), (1:ℝ)/n)
              - (1:ℝ)/p * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n)
            + ∑ q ∈ P.erase p,
              ((∑ n ∈ (Finset.Ioc A B).filter (fun n => (p*q) ∣ n),
                  (1:ℝ)/n)
                - (1:ℝ)/((p:ℝ)*q) * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n) := by
        rw [Finset.sum_sub_distrib]
        ring
      rw [hrw]
      refine le_trans (abs_add_le _ _) ?_
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    refine le_trans htri ?_
    have hsum : ∑ q ∈ P.erase p,
        |(∑ n ∈ (Finset.Ioc A B).filter (fun n => (p*q) ∣ n), (1:ℝ)/n)
          - (1:ℝ)/((p:ℝ)*q) * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n|
        ≤ (P.card : ℝ) * (3*((1:ℝ)/A)) := by
      calc ∑ q ∈ P.erase p, |_| ≤ ∑ _q ∈ P.erase p, 3*((1:ℝ)/A) :=
            Finset.sum_le_sum hoff
        _ = ((P.erase p).card : ℝ) * (3*((1:ℝ)/A)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (P.card : ℝ) * (3*((1:ℝ)/A)) := by
            have hc : (P.erase p).card ≤ P.card :=
              Finset.card_le_card (Finset.erase_subset _ _)
            have hc' : ((P.erase p).card : ℝ) ≤ (P.card : ℝ) := by
              exact_mod_cast hc
            have h30 : (0:ℝ) ≤ 3*((1:ℝ)/A) := by positivity
            exact mul_le_mul_of_nonneg_right hc' h30
    linarith [hdiag, hsum]
  -- total
  calc |∑ p ∈ P, _| ≤ ∑ p ∈ P, _ := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ P, (3*((1:ℝ)/A) + (P.card : ℝ) * (3*((1:ℝ)/A))) :=
        Finset.sum_le_sum hper
    _ = (P.card : ℝ) * (3*((1:ℝ)/A) + (P.card : ℝ) * (3*((1:ℝ)/A))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = 3*(((P.card : ℝ) + ((P.card : ℝ))^2)/A) := by
        ring


/-- **The window variance bound** (Track R, A2-III, N3-h4): the
windowed Turán–Kubilius variance —

  `∑_{A<n≤B} (ω_P(n) − E)²/n ≤ E·∑ 1/n + 3(#P+#P²)/A + 6E·#P/A`,

from the two window moments: the expansion
`(ω−E)² = ω² − 2Eω + E²`, the second moment's main coefficient
`E + ∑_{p≠q} 1/(pq) ≤ E + E²`, and the cross term priced by the first
moment.  The `E·H` main term (not `E²·H`) is the whole point: the
sifted set pays `E²` per element, so its mass is `H/E`-small. -/
theorem window_variance_le (A B : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPA2 : ∀ p ∈ P, ∀ q ∈ P, p*q ≤ A)
    (hAB : A ≤ B) :
    ∑ n ∈ Finset.Ioc A B,
        (((P.filter (· ∣ n)).card : ℝ) - ∑ p ∈ P, (1:ℝ)/p)^2/n
      ≤ (∑ p ∈ P, (1:ℝ)/p) * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n
        + (3*(((P.card : ℝ) + ((P.card : ℝ))^2)/A)
          + 2*(∑ p ∈ P, (1:ℝ)/p) * (3*((P.card : ℝ)/A))) := by
  classical
  have hE0 : (0:ℝ) ≤ ∑ p ∈ P, (1:ℝ)/p :=
    Finset.sum_nonneg fun p _ => by positivity
  have hH0 : (0:ℝ) ≤ ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n :=
    Finset.sum_nonneg fun n _ => by positivity
  -- the square expands
  have hident : ∑ n ∈ Finset.Ioc A B,
      (((P.filter (· ∣ n)).card : ℝ) - ∑ p ∈ P, (1:ℝ)/p)^2/n
      = (∑ n ∈ Finset.Ioc A B, (((P.filter (· ∣ n)).card : ℝ))^2/n)
        - 2*(∑ p ∈ P, (1:ℝ)/p)
            * (∑ n ∈ Finset.Ioc A B, ((P.filter (· ∣ n)).card : ℝ)/n)
        + ((∑ p ∈ P, (1:ℝ)/p))^2 * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n := by
    have hpt : ∀ n ∈ Finset.Ioc A B,
        (((P.filter (· ∣ n)).card : ℝ) - ∑ p ∈ P, (1:ℝ)/p)^2/n
          = (((P.filter (· ∣ n)).card : ℝ))^2/n
            - (2*(∑ p ∈ P, (1:ℝ)/p))
                * (((P.filter (· ∣ n)).card : ℝ)/n)
            + ((∑ p ∈ P, (1:ℝ)/p))^2 * ((1:ℝ)/n) := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      have hn0 : ((n:ℝ)) ≠ 0 := by
        have : (0:ℕ) < n := by omega
        exact_mod_cast this.ne'
      field_simp
      ring
    calc ∑ n ∈ Finset.Ioc A B,
        (((P.filter (· ∣ n)).card : ℝ) - ∑ p ∈ P, (1:ℝ)/p)^2/n
        = ∑ n ∈ Finset.Ioc A B,
            ((((P.filter (· ∣ n)).card : ℝ))^2/n
              - (2*(∑ p ∈ P, (1:ℝ)/p))
                  * (((P.filter (· ∣ n)).card : ℝ)/n)
              + ((∑ p ∈ P, (1:ℝ)/p))^2 * ((1:ℝ)/n)) :=
          Finset.sum_congr rfl hpt
      _ = (∑ n ∈ Finset.Ioc A B, (((P.filter (· ∣ n)).card : ℝ))^2/n)
            - 2*(∑ p ∈ P, (1:ℝ)/p)
                * (∑ n ∈ Finset.Ioc A B,
                    ((P.filter (· ∣ n)).card : ℝ)/n)
            + ((∑ p ∈ P, (1:ℝ)/p))^2
                * ∑ n ∈ Finset.Ioc A B, (1:ℝ)/n := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
  -- the moment inputs
  have h2m := window_omega_first_moment A B P hP
    (fun p hp => le_trans (Nat.le_mul_of_pos_left p (hP p hp).pos)
      (hPA2 p hp p hp)) hAB
  have h3m := window_omega_sq_first_moment A B P hP hPA2 hAB
  -- the off-diagonal coefficient sits below `E²`
  have hSoff : ∑ p ∈ P, ∑ q ∈ P.erase p, (1:ℝ)/((p:ℝ)*q)
      ≤ ((∑ p ∈ P, (1:ℝ)/p))^2 := by
    have h1 : ∀ p ∈ P, ∑ q ∈ P.erase p, (1:ℝ)/((p:ℝ)*q)
        ≤ ∑ q ∈ P, (1:ℝ)/((p:ℝ)*q) := fun p _ =>
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun q _ _ => by positivity)
    have h2 : ∑ p ∈ P, ∑ q ∈ P, (1:ℝ)/((p:ℝ)*q)
        = ((∑ p ∈ P, (1:ℝ)/p))^2 := by
      rw [pow_two, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [div_mul_div_comm, one_mul]
    calc ∑ p ∈ P, ∑ q ∈ P.erase p, (1:ℝ)/((p:ℝ)*q)
        ≤ ∑ p ∈ P, ∑ q ∈ P, (1:ℝ)/((p:ℝ)*q) := Finset.sum_le_sum h1
      _ = ((∑ p ∈ P, (1:ℝ)/p))^2 := h2
  -- unpack the moment bounds
  have h3up : (∑ n ∈ Finset.Ioc A B, (((P.filter (· ∣ n)).card : ℝ))^2/n)
      ≤ ((∑ p ∈ P, (1:ℝ)/p)
          + ∑ p ∈ P, ∑ q ∈ P.erase p, (1:ℝ)/((p:ℝ)*q))
        * (∑ n ∈ Finset.Ioc A B, (1:ℝ)/n)
        + 3*(((P.card : ℝ) + ((P.card : ℝ))^2)/A) := by
    linarith [(abs_le.mp h3m).2]
  have h2lo : (∑ p ∈ P, (1:ℝ)/p) * (∑ n ∈ Finset.Ioc A B, (1:ℝ)/n)
      - 3*((P.card : ℝ)/A)
      ≤ ∑ n ∈ Finset.Ioc A B, ((P.filter (· ∣ n)).card : ℝ)/n := by
    linarith [(abs_le.mp h2m).1]
  -- assemble
  rw [hident]
  nlinarith [h3up,
    mul_le_mul_of_nonneg_left h2lo
      (by linarith : (0:ℝ) ≤ 2*(∑ p ∈ P, (1:ℝ)/p)),
    mul_le_mul_of_nonneg_right hSoff hH0, hE0, hH0]


/-- **The window sifted bound** (Track R, A2-III, N3-h5): elements of
`(A, B]` with no prime factor in `P` have `(ω_P − E)² = E²`, so their
log-mass is at most `1/E²` times the window variance —

  `∑_{n sifted} 1/n ≤ (E·H + 3(#P+#P²)/A + 6E·#P/A)/E²`.

With `E ≥ E₀` the main term is `H/E₀`: the block-level `[mrt]`
Lemma-"excep" shape with everything measured against the window
harmonic mass. -/
theorem window_sifted_le (A B : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPA2 : ∀ p ∈ P, ∀ q ∈ P, p*q ≤ A)
    (hAB : A ≤ B) (hE0 : (0:ℝ) < ∑ p ∈ P, (1:ℝ)/p) :
    ∑ n ∈ (Finset.Ioc A B).filter
        (fun n => (P.filter (· ∣ n)).card = 0), (1:ℝ)/n
      ≤ ((∑ p ∈ P, (1:ℝ)/p) * (∑ n ∈ Finset.Ioc A B, (1:ℝ)/n)
          + (3*(((P.card : ℝ) + ((P.card : ℝ))^2)/A)
            + 2*(∑ p ∈ P, (1:ℝ)/p) * (3*((P.card : ℝ)/A))))
        / ((∑ p ∈ P, (1:ℝ)/p))^2 := by
  classical
  have hvar := window_variance_le A B P hP hPA2 hAB
  -- the sifted mass is dominated termwise by the variance summand
  have hterm : ∀ n ∈ (Finset.Ioc A B).filter
      (fun n => (P.filter (· ∣ n)).card = 0),
      (1:ℝ)/n = (((P.filter (· ∣ n)).card : ℝ)
          - ∑ p ∈ P, (1:ℝ)/p)^2/n / ((∑ p ∈ P, (1:ℝ)/p))^2 := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [hn.2]
    rw [show ((0:ℕ):ℝ) - ∑ p ∈ P, (1:ℝ)/p = -(∑ p ∈ P, (1:ℝ)/p) by
      push_cast; ring]
    rw [neg_pow]
    field_simp
  have hsub : ∑ n ∈ (Finset.Ioc A B).filter
      (fun n => (P.filter (· ∣ n)).card = 0), (1:ℝ)/n
      ≤ (∑ n ∈ Finset.Ioc A B,
          (((P.filter (· ∣ n)).card : ℝ) - ∑ p ∈ P, (1:ℝ)/p)^2/n)
        / ((∑ p ∈ P, (1:ℝ)/p))^2 := by
    calc (∑ n ∈ (Finset.Ioc A B).filter
          (fun n => (P.filter (· ∣ n)).card = 0), (1:ℝ)/n)
        = ∑ n ∈ (Finset.Ioc A B).filter
            (fun n => (P.filter (· ∣ n)).card = 0),
            (((P.filter (· ∣ n)).card : ℝ)
              - ∑ p ∈ P, (1:ℝ)/p)^2/n / ((∑ p ∈ P, (1:ℝ)/p))^2 :=
          Finset.sum_congr rfl hterm
      _ ≤ ∑ n ∈ Finset.Ioc A B,
            (((P.filter (· ∣ n)).card : ℝ)
              - ∑ p ∈ P, (1:ℝ)/p)^2/n / ((∑ p ∈ P, (1:ℝ)/p))^2 :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) fun n _ _ => by positivity
      _ = (∑ n ∈ Finset.Ioc A B,
            (((P.filter (· ∣ n)).card : ℝ)
              - ∑ p ∈ P, (1:ℝ)/p)^2/n) / ((∑ p ∈ P, (1:ℝ)/p))^2 := by
          rw [← Finset.sum_div]
  refine le_trans hsub ?_
  refine div_le_div_of_nonneg_right hvar (by positivity)


open Real Finset in
/-- **The window typical-set complement telescope** (Track R, A2-III,
N3-h6): over a window `(A, B]`, missing a factor in some level means
being sifted at that level, so the atypical log-mass is at most the
sum of the per-level window sifted bounds —

  `∑_{n atypical} 1/n ≤ ∑_{P ∈ levels} (E_P·H + errs_P)/E_P²`.

The union-bound induction of `typicalS_complement_logavg_le`, with
`window_sifted_le` pricing each level against the window mass. -/
theorem window_typicalS_complement_le (A B : ℕ)
    (levels : List (Finset ℕ))
    (hP : ∀ P ∈ levels, ∀ p ∈ P, p.Prime)
    (hPA2 : ∀ P ∈ levels, ∀ p ∈ P, ∀ q ∈ P, p*q ≤ A)
    (hAB : A ≤ B)
    (hE0 : ∀ P ∈ levels, (0:ℝ) < ∑ p ∈ P, (1:ℝ)/p) :
    ∑ n ∈ (Finset.Ioc A B).filter
        (fun n => ¬ HasFactorInAll levels n), (1:ℝ)/n
      ≤ (levels.map (fun (P : Finset ℕ) =>
          ((∑ p ∈ P, (1:ℝ)/p) * (∑ n ∈ Finset.Ioc A B, (1:ℝ)/n)
            + (3*(((P.card : ℝ) + ((P.card : ℝ))^2)/A)
              + 2*(∑ p ∈ P, (1:ℝ)/p) * (3*((P.card : ℝ)/A))))
          / ((∑ p ∈ P, (1:ℝ)/p))^2)).sum := by
  classical
  induction levels with
  | nil =>
      simp [HasFactorInAll]
  | cons P rest ih =>
      have hP' : ∀ Q ∈ rest, ∀ p ∈ Q, p.Prime :=
        fun Q hQ => hP Q (List.mem_cons_of_mem _ hQ)
      have hPA2' : ∀ Q ∈ rest, ∀ p ∈ Q, ∀ q ∈ Q, p*q ≤ A :=
        fun Q hQ => hPA2 Q (List.mem_cons_of_mem _ hQ)
      have hE0' : ∀ Q ∈ rest, (0:ℝ) < ∑ p ∈ Q, (1:ℝ)/p :=
        fun Q hQ => hE0 Q (List.mem_cons_of_mem _ hQ)
      have hrest := ih hP' hPA2' hE0'
      have hhead := window_sifted_le A B P
        (hP P (List.mem_cons_self ..))
        (hPA2 P (List.mem_cons_self ..)) hAB
        (hE0 P (List.mem_cons_self ..))
      -- missing `P :: rest` means sifted at `P` or missing `rest`
      have hsub : (Finset.Ioc A B).filter
          (fun n => ¬ HasFactorInAll (P :: rest) n)
          ⊆ ((Finset.Ioc A B).filter
              (fun n => (P.filter (· ∣ n)).card = 0))
            ∪ ((Finset.Ioc A B).filter
              (fun n => ¬ HasFactorInAll rest n)) := by
        intro n hn
        rw [Finset.mem_filter] at hn
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
        rw [hasFactorInAll_cons, not_and_or] at hn
        rcases hn.2 with h | h
        · exact Or.inl ⟨hn.1, by omega⟩
        · exact Or.inr ⟨hn.1, h⟩
      have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ => by positivity :
          ∀ n ∈ ((Finset.Ioc A B).filter
              (fun n => (P.filter (· ∣ n)).card = 0))
            ∪ ((Finset.Ioc A B).filter
              (fun n => ¬ HasFactorInAll rest n)),
            n ∉ (Finset.Ioc A B).filter
              (fun n => ¬ HasFactorInAll (P :: rest) n) → (0:ℝ) ≤ 1/n)
      have hunion : ∑ n ∈ ((Finset.Ioc A B).filter
            (fun n => (P.filter (· ∣ n)).card = 0))
          ∪ ((Finset.Ioc A B).filter
            (fun n => ¬ HasFactorInAll rest n)), (1:ℝ)/n
          ≤ (∑ n ∈ (Finset.Ioc A B).filter
              (fun n => (P.filter (· ∣ n)).card = 0), (1:ℝ)/n)
            + ∑ n ∈ (Finset.Ioc A B).filter
              (fun n => ¬ HasFactorInAll rest n), (1:ℝ)/n := by
        have hui := Finset.sum_union_inter
          (s₁ := (Finset.Ioc A B).filter
            (fun n => (P.filter (· ∣ n)).card = 0))
          (s₂ := (Finset.Ioc A B).filter
            (fun n => ¬ HasFactorInAll rest n))
          (f := fun n => (1:ℝ)/n)
        have hint : (0:ℝ) ≤ ∑ n ∈ ((Finset.Ioc A B).filter
            (fun n => (P.filter (· ∣ n)).card = 0))
          ∩ ((Finset.Ioc A B).filter
            (fun n => ¬ HasFactorInAll rest n)), (1:ℝ)/n :=
          Finset.sum_nonneg fun n _ => by positivity
        linarith
      rw [List.map_cons, List.sum_cons]
      calc ∑ n ∈ (Finset.Ioc A B).filter
            (fun n => ¬ HasFactorInAll (P :: rest) n), (1:ℝ)/n
          ≤ _ := hmono
        _ ≤ _ := hunion
        _ ≤ ((∑ p ∈ P, (1:ℝ)/p) * (∑ n ∈ Finset.Ioc A B, (1:ℝ)/n)
              + (3*(((P.card : ℝ) + ((P.card : ℝ))^2)/A)
                + 2*(∑ p ∈ P, (1:ℝ)/p) * (3*((P.card : ℝ)/A))))
            / ((∑ p ∈ P, (1:ℝ)/p))^2
            + (rest.map (fun (Q : Finset ℕ) =>
                ((∑ p ∈ Q, (1:ℝ)/p)
                    * (∑ n ∈ Finset.Ioc A B, (1:ℝ)/n)
                  + (3*(((Q.card : ℝ) + ((Q.card : ℝ))^2)/A)
                    + 2*(∑ p ∈ Q, (1:ℝ)/p)
                        * (3*((Q.card : ℝ)/A))))
                / ((∑ p ∈ Q, (1:ℝ)/p))^2)).sum := by
            linarith [hhead, hrest]


open MeasureTheory ExpSums in
/-- **The collision fibre energy** (Track R, A2-III, II-4): the part
of a block polynomial supported on multiples of `p²` has energy
`1/p²`-small —

  `∫_{−T}^{T} ‖∑_{n∈S, p²∣n} (b n/n)·e(−ξ log n)‖²
     ≤ e^π·(T/A + 4)·(1/p²)·∑_{k ∈ (A/p², (A+Δ)/p²]} 1/k`.

In `[MR]`'s Ramaré decomposition the collision term collects the
fibres where the extracted prime divides the quotient, i.e. exactly
the `p²`-multiples.  The essential point — and the one an earlier
design pass got wrong — is that its harmonic mass must be measured at
the **quotient scale** `A/p²`, via the exact reindex
`sum_one_div_Ioc_dvd_eq`, not at the block scale: pricing it at the
block scale gives a bound that is false by a factor `p²` whenever
`p² ≈ A`. -/
theorem collision_fibre_energy_le (A Δ p : ℕ) (hA : 1 ≤ A)
    (hΔA : Δ ≤ A) (hp : 0 < p)
    (S : Finset ℕ) (hS : S ⊆ Finset.Ioc A (A+Δ))
    (b : ℕ → ℂ) (hb : ∀ n, ‖b n‖ ≤ 1) (T : ℝ) (hT : 0 < T) :
    (∫ ξ in (-T)..T, ‖∑ n ∈ S.filter (fun n => p*p ∣ n), (b n/(n:ℂ))
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
      ≤ Real.exp Real.pi * (T/(A:ℝ) + 4)
          * ((1/((p:ℝ)*(p:ℝ)))
              * ∑ k ∈ Finset.Ioc (A/(p*p)) ((A+Δ)/(p*p)), (1:ℝ)/k) := by
  classical
  have hpp : 0 < p*p := Nat.mul_pos hp hp
  -- the fibre sits in a dyadic block
  have hsub : S.filter (fun n => p*p ∣ n) ⊆ Finset.Ioc A (2*A) := by
    refine (Finset.filter_subset _ _).trans (hS.trans ?_)
    refine Finset.Ioc_subset_Ioc_right ?_
    omega
  have hbase := intervalIntegral_norm_sq_short_poly_le_sharp_of_bound
    A hA (S.filter (fun n => p*p ∣ n)) hsub b 1 (by norm_num) hb T hT
  refine le_trans hbase ?_
  -- the fibre mass, measured at the quotient scale
  have hmass : ∑ n ∈ S.filter (fun n => p*p ∣ n), (1:ℝ)/(n:ℝ)
      ≤ (1/((p:ℝ)*(p:ℝ)))
          * ∑ k ∈ Finset.Ioc (A/(p*p)) ((A+Δ)/(p*p)), (1:ℝ)/k := by
    have hsub2 : S.filter (fun n => p*p ∣ n)
        ⊆ (Finset.Ioc A (A+Δ)).filter (fun n => p*p ∣ n) := by
      intro n hn
      rw [Finset.mem_filter] at hn ⊢
      exact ⟨hS hn.1, hn.2⟩
    have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub2
      (fun n _ _ => by positivity :
        ∀ n ∈ (Finset.Ioc A (A+Δ)).filter (fun n => p*p ∣ n),
          n ∉ S.filter (fun n => p*p ∣ n) → (0:ℝ) ≤ 1/(n:ℝ))
    have hexact := sum_one_div_Ioc_dvd_eq A (A+Δ) (p*p) hpp
    have hcast : ((1:ℝ)/((p*p : ℕ):ℝ))
        = 1/((p:ℝ)*(p:ℝ)) := by
      push_cast
      ring
    rw [hexact, hcast] at hmono
    exact hmono
  have hconst : (0:ℝ) ≤ Real.exp Real.pi * (T/(A:ℝ) + 4) := by positivity
  calc Real.exp Real.pi * (T/(A:ℝ) + 4)
        * (1^2 * ∑ n ∈ S.filter (fun n => p*p ∣ n), (1:ℝ)/(n:ℝ))
      = Real.exp Real.pi * (T/(A:ℝ) + 4)
          * (∑ n ∈ S.filter (fun n => p*p ∣ n), (1:ℝ)/(n:ℝ)) := by
        ring
    _ ≤ Real.exp Real.pi * (T/(A:ℝ) + 4)
          * ((1/((p:ℝ)*(p:ℝ)))
              * ∑ k ∈ Finset.Ioc (A/(p*p)) ((A+Δ)/(p*p)), (1:ℝ)/k) :=
        mul_le_mul_of_nonneg_left hmass hconst


open MeasureTheory Finset ExpSums in
/-- **The fourth moment of a prime polynomial** (Track R, A2-III,
III-3a): for primes in a dyadic range `(P, 2P]`,

  `∫_{−T}^{T} ‖Q(ξ)²‖² ≤ e^π·(T/P² + 8)·4·∑_{n ∈ Y·Y} 1/n`,

with `Q(ξ) = ∑_{p∈Y} (b p/p)·e(−ξ log p)`.

This is the `k = 2` case of the `[MR]` moment input, and it is pure
assembly of the pieces already on main: `phase_poly_mul` convolves the
square onto the product support, `phase_poly_fiberwise` collapses it
to a Dirichlet polynomial, `card_prime_pair_fiber_le` bounds the
resulting coefficients by `2` (a product of two primes has at most two
ordered factorisations), and the support sits in `(P², 4P²]`, so the
ratio-general sharp mean value theorem applies at `R = 4` — log-free. -/
theorem intervalIntegral_norm_sq_prime_poly_sq_le (Y : Finset ℕ)
    (hY : ∀ p ∈ Y, p.Prime) (P : ℕ) (hP : 1 ≤ P)
    (hlo : ∀ p ∈ Y, P < p) (hhi : ∀ p ∈ Y, p ≤ 2*P)
    (b : ℕ → ℂ) (hb : ∀ p, ‖b p‖ ≤ 1) (T : ℝ) (hT : 0 < T) :
    (∫ ξ in (-T)..T, ‖(∑ p ∈ Y, (b p/(p:ℂ))
        * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))^2‖^2)
      ≤ Real.exp Real.pi * (T/((P:ℝ)*(P:ℝ)) + 8)
          * (4 * ∑ n ∈ (Y ×ˢ Y).image (fun q : ℕ × ℕ => q.1 * q.2),
                (1:ℝ)/(n:ℝ)) := by
  classical
  set Tgt : Finset ℕ := (Y ×ˢ Y).image (fun q : ℕ × ℕ => q.1 * q.2)
    with hTgt_def
  have hppos : ∀ p ∈ Y, 0 < p := fun p hp => (hY p hp).pos
  -- the coefficients of the collapsed polynomial
  set c : ℕ → ℂ := fun n =>
    ∑ q ∈ (Y ×ˢ Y).filter (fun q => q.1 * q.2 = n), b q.1 * b q.2
    with hc_def
  -- the square is the collapsed Dirichlet polynomial
  have hsq : ∀ ξ : ℝ, (∑ p ∈ Y, (b p/(p:ℂ))
        * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))^2
      = ∑ n ∈ Tgt, (c n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ) := by
    intro ξ
    rw [pow_two, phase_poly_mul Y Y b b hppos hppos ξ]
    rw [phase_poly_fiberwise (Y ×ˢ Y) Tgt (fun q hq => by
      rw [hTgt_def, Finset.mem_image]
      exact ⟨q, hq, rfl⟩) (fun q => b q.1 * b q.2) ξ]
  rw [intervalIntegral.integral_congr (fun ξ _ => by
    rw [hsq ξ] : ∀ ξ ∈ Set.uIcc (-T) T,
      ‖(∑ p ∈ Y, (b p/(p:ℂ))
          * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))^2‖^2
      = ‖∑ n ∈ Tgt, (c n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)]
  -- the support sits in `(P², 4P²]`
  have hPP : 1 ≤ P*P := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hsupp : Tgt ⊆ Finset.Ioc (P*P) (4*(P*P)) := by
    intro n hn
    rw [hTgt_def, Finset.mem_image] at hn
    obtain ⟨q, hq, rfl⟩ := hn
    rw [Finset.mem_product] at hq
    have h1 := hlo q.1 hq.1
    have h2 := hlo q.2 hq.2
    have h3 := hhi q.1 hq.1
    have h4 := hhi q.2 hq.2
    rw [Finset.mem_Ioc]
    constructor
    · have hq2 : 0 < q.2 := (hY q.2 hq.2).pos
      calc P*P < q.1 * P := by
            exact Nat.mul_lt_mul_of_lt_of_le h1 le_rfl (by omega)
        _ ≤ q.1 * q.2 := Nat.mul_le_mul_left _ h2.le
    · calc q.1 * q.2 ≤ (2*P) * (2*P) := Nat.mul_le_mul h3 h4
        _ = 4*(P*P) := by ring
  -- the coefficient bound: at most two ordered factorisations
  have hcb : ∀ n : ℕ, ‖c n‖ ≤ 2 := by
    intro n
    have hfib := card_prime_pair_fiber_le Y Y hY hY n
    have hnorm : ‖c n‖
        ≤ (((Y ×ˢ Y).filter (fun q => q.1 * q.2 = n)).card : ℝ) * 1 := by
      rw [hc_def]
      refine norm_sum_fiber_le (Y ×ˢ Y) (fun q => b q.1 * b q.2) 1
        (by norm_num) (fun q => ?_) n
      rw [norm_mul]
      have h1 := hb q.1
      have h2 := hb q.2
      nlinarith [norm_nonneg (b q.1), norm_nonneg (b q.2)]
    have hcard : (((Y ×ˢ Y).filter (fun q => q.1 * q.2 = n)).card : ℝ)
        ≤ 2 := by exact_mod_cast hfib
    linarith
  -- the ratio-general sharp mean value theorem at `R = 4`
  have hmvt := intervalIntegral_norm_sq_poly_le_sharp_ratio (P*P) 4
    hPP (by norm_num) Tgt hsupp c T hT
  refine le_trans hmvt ?_
  have hcast : ((P*P : ℕ):ℝ) = (P:ℝ)*(P:ℝ) := by
    push_cast
    ring
  rw [hcast]
  have hconst : (0:ℝ) ≤ Real.exp Real.pi * (T/((P:ℝ)*(P:ℝ)) + 2*(4:ℕ)) := by
    positivity
  have hmass : ∑ n ∈ Tgt, ‖c n‖^2/(n:ℝ)
      ≤ 4 * ∑ n ∈ Tgt, (1:ℝ)/(n:ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn0 : (0:ℝ) < n := by
      have hnIoc := Finset.mem_Ioc.mp (hsupp hn)
      have : (0:ℕ) < n := by omega
      exact_mod_cast this
    have hsq2 : ‖c n‖^2 ≤ 4 := by
      have := hcb n
      nlinarith [norm_nonneg (c n)]
    rw [div_le_iff₀ hn0]
    calc ‖c n‖^2 ≤ 4 := hsq2
      _ = 4 * (1/(n:ℝ)) * (n:ℝ) := by field_simp
  have hnum : ((4:ℕ):ℝ) = (4:ℝ) := by norm_num
  calc Real.exp Real.pi * (T/((P:ℝ)*(P:ℝ)) + 2*((4:ℕ):ℝ))
        * ∑ n ∈ Tgt, ‖c n‖^2/(n:ℝ)
      = Real.exp Real.pi * (T/((P:ℝ)*(P:ℝ)) + 8)
          * ∑ n ∈ Tgt, ‖c n‖^2/(n:ℝ) := by
        rw [hnum]
        ring_nf
    _ ≤ Real.exp Real.pi * (T/((P:ℝ)*(P:ℝ)) + 8)
          * (4 * ∑ n ∈ Tgt, (1:ℝ)/(n:ℝ)) := by
        refine mul_le_mul_of_nonneg_left hmass ?_
        positivity


/-! ## The telescoping energy (Track R, A2-III, II-2c) -/

open Finset in
/-- **A difference of disjoint sums is one signed sum** (Track R,
A2-III, II-2c): for disjoint `S`, `S'`,

  `∑_{S} w − ∑_{S'} w = ∑_{S ∪ S'} (if · ∈ S then w · else −w ·)`.

The point is that a *difference* of two polynomials supported in one
collar is again a *single* polynomial supported in that collar, with
coefficients of the same size — so the mean value theorem applies to it
once, rather than twice through a square-splitting triangle. -/
theorem sum_sub_sum_eq_sum_union_signed (S S' : Finset ℕ)
    (hdisj : Disjoint S S') (w : ℕ → ℂ) :
    (∑ m ∈ S, w m) - (∑ m ∈ S', w m)
      = ∑ m ∈ S ∪ S', (if m ∈ S then w m else -w m) := by
  classical
  rw [Finset.sum_union hdisj]
  have h1 : ∑ m ∈ S, (if m ∈ S then w m else -w m) = ∑ m ∈ S, w m :=
    Finset.sum_congr rfl fun m hm => by simp [hm]
  have h2 : ∑ m ∈ S', (if m ∈ S then w m else -w m) = ∑ m ∈ S', (-(w m)) :=
    Finset.sum_congr rfl fun m hm => by
      have hmS : m ∉ S := Finset.disjoint_right.mp hdisj hm
      simp [hmS]
  rw [h1, h2, Finset.sum_neg_distrib]
  ring

open MeasureTheory Finset ExpSums in
/-- **The telescoping energy** (Track R, A2-III, II-2c): if two windows
`(a, b]` and `(a', b']` have left endpoints within `L₁` and right
endpoints within `L₂` of each other, then the two `1/n`-normalised phase
polynomials they carry differ, in energy, by two collars —

  `∫_{−T}^{T} ‖∑_{(a,b]} − ∑_{(a',b']}‖²
     ≤ 2e^π(T/a₀ + 4)(L₁/a₀) + 2e^π(T/b₀ + 4)(L₂/b₀)`,

with `a₀ = min a a'` and `b₀ = min b b'`.

This is the analytic half of the `[MR]` decomposition lemma, and it is
what lets the band assembly replace a `p`-dependent fibre window
`(A/p, (A+Δ)/p]` by a cell-uniform reference block: on an e-adic cell at
resolution `2N` the two endpoints move by at most `A/(N·p) + 1` and
`B/(N·p) + 1` respectively
(`div_le_div_add_div_add_one`), so the error is `O(1/N)` per prime and
sums to `O(1/N)` over the cell.

The proof is the identity `sum_Ioc_eq_sum_Ioc_add_collars` followed by
two applications of `collar_energy_length_le`.  Its one inefficiency is
the square-splitting `intervalIntegral_norm_add_sq_le`, unavoidable
because the two collars are anchored at different scales; the four
collars of the identity are *not* split, since each pair lives in one
collar interval and `sum_sub_sum_eq_sum_union_signed` merges it. -/
theorem intervalIntegral_norm_sq_window_sub_le
    (a b a' b' L₁ L₂ : ℕ) (hab : a ≤ b) (ha'b' : a' ≤ b')
    (haa' : max a a' ≤ min a a' + L₁) (hbb' : max b b' ≤ min b b' + L₂)
    (hLa : L₁ ≤ min a a') (hLb : L₂ ≤ min b b')
    (ha1 : 1 ≤ min a a') (hb1 : 1 ≤ min b b')
    (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (T : ℝ) (hT : 0 < T) :
    (∫ ξ in (-T)..T,
        ‖(∑ m ∈ Finset.Ioc a b, (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
          - (∑ m ∈ Finset.Ioc a' b', (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))‖^2)
      ≤ 2 * (Real.exp Real.pi * (T/((min a a' : ℕ):ℝ) + 4)
              * ((L₁:ℝ)/((min a a' : ℕ):ℝ)))
        + 2 * (Real.exp Real.pi * (T/((min b b' : ℕ):ℝ) + 4)
              * ((L₂:ℝ)/((min b b' : ℕ):ℝ))) := by
  classical
  -- the two left collars are disjoint, as are the two right collars
  have hdisj13 : Disjoint (Finset.Ioc a (min b a')) (Finset.Ioc a' (min b' a)) := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    simp only [Finset.mem_Ioc] at hn hn'
    omega
  have hdisj24 :
      Disjoint (Finset.Ioc (max a b') b) (Finset.Ioc (max a' b) b') := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    simp only [Finset.mem_Ioc] at hn hn'
    omega
  -- each pair sits inside a single collar interval
  have hsubA : (Finset.Ioc a (min b a')) ∪ (Finset.Ioc a' (min b' a))
      ⊆ Finset.Ioc (min a a') (min a a' + L₁) := by
    refine Finset.union_subset ?_ ?_ <;>
      intro n hn <;>
      simp only [Finset.mem_Ioc] at hn ⊢ <;>
      omega
  have hsubB : (Finset.Ioc (max a b') b) ∪ (Finset.Ioc (max a' b) b')
      ⊆ Finset.Ioc (min b b') (min b b' + L₂) := by
    refine Finset.union_subset ?_ ?_ <;>
      intro n hn <;>
      simp only [Finset.mem_Ioc] at hn ⊢ <;>
      omega
  -- the signed coefficients are still `1`-bounded
  have hd₁ : ∀ n : ℕ,
      ‖(if n ∈ Finset.Ioc a (min b a') then c n else -c n)‖ ≤ 1 := by
    intro n
    split_ifs with h
    · exact hc n
    · rw [norm_neg]; exact hc n
  have hd₂ : ∀ n : ℕ,
      ‖(if n ∈ Finset.Ioc (max a b') b then c n else -c n)‖ ≤ 1 := by
    intro n
    split_ifs with h
    · exact hc n
    · rw [norm_neg]; exact hc n
  -- pointwise, the difference of the two windows is two collar polynomials
  have hpt : ∀ ξ : ℝ,
      (∑ m ∈ Finset.Ioc a b, (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
          - (∑ m ∈ Finset.Ioc a' b', (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
        = (∑ m ∈ (Finset.Ioc a (min b a')) ∪ (Finset.Ioc a' (min b' a)),
              ((if m ∈ Finset.Ioc a (min b a') then c m else -c m)/(m:ℂ))
                * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
          + (∑ m ∈ (Finset.Ioc (max a b') b) ∪ (Finset.Ioc (max a' b) b'),
              ((if m ∈ Finset.Ioc (max a b') b then c m else -c m)/(m:ℂ))
                * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)) := by
    intro ξ
    have hpush : ∀ (S : Finset ℕ) (m : ℕ),
        (if m ∈ S then (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)
          else -((c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)))
          = ((if m ∈ S then c m else -c m)/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) := by
      intro S m
      split_ifs with h
      · rfl
      · ring
    have h1 := sum_sub_sum_eq_sum_union_signed (Finset.Ioc a (min b a'))
      (Finset.Ioc a' (min b' a)) hdisj13
      (fun m => (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
    have h2 := sum_sub_sum_eq_sum_union_signed (Finset.Ioc (max a b') b)
      (Finset.Ioc (max a' b) b') hdisj24
      (fun m => (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
    have h1' : (∑ m ∈ Finset.Ioc a (min b a'), (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
          - (∑ m ∈ Finset.Ioc a' (min b' a), (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
        = ∑ m ∈ (Finset.Ioc a (min b a')) ∪ (Finset.Ioc a' (min b' a)),
            ((if m ∈ Finset.Ioc a (min b a') then c m else -c m)/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) := by
      rw [h1]
      exact Finset.sum_congr rfl fun m _ => hpush _ m
    have h2' : (∑ m ∈ Finset.Ioc (max a b') b, (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
          - (∑ m ∈ Finset.Ioc (max a' b) b', (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
        = ∑ m ∈ (Finset.Ioc (max a b') b) ∪ (Finset.Ioc (max a' b) b'),
            ((if m ∈ Finset.Ioc (max a b') b then c m else -c m)/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) := by
      rw [h2]
      exact Finset.sum_congr rfl fun m _ => hpush _ m
    rw [sum_Ioc_eq_sum_Ioc_add_collars a b a' b' hab ha'b'
      (fun m => (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)), ← h1', ← h2']
    ring
  simp only [hpt]
  -- both collar polynomials are continuous
  have hchar : ∀ v : ℝ, Continuous fun ξ : ℝ =>
      ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ) := fun v =>
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hXc : Continuous fun ξ : ℝ =>
      ∑ m ∈ (Finset.Ioc a (min b a')) ∪ (Finset.Ioc a' (min b' a)),
        ((if m ∈ Finset.Ioc a (min b a') then c m else -c m)/(m:ℂ))
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) :=
    continuous_finset_sum _ fun m _ =>
      continuous_const.mul (hchar (Real.log m))
  have hYc : Continuous fun ξ : ℝ =>
      ∑ m ∈ (Finset.Ioc (max a b') b) ∪ (Finset.Ioc (max a' b) b'),
        ((if m ∈ Finset.Ioc (max a b') b then c m else -c m)/(m:ℂ))
          * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) :=
    continuous_finset_sum _ fun m _ =>
      continuous_const.mul (hchar (Real.log m))
  refine le_trans (intervalIntegral_norm_add_sq_le _ _ hXc hYc T hT.le) ?_
  have hXe := collar_energy_length_le (min a a') L₁ ha1 hLa
    ((Finset.Ioc a (min b a')) ∪ (Finset.Ioc a' (min b' a))) hsubA
    (fun m => if m ∈ Finset.Ioc a (min b a') then c m else -c m) hd₁ T hT
  have hYe := collar_energy_length_le (min b b') L₂ hb1 hLb
    ((Finset.Ioc (max a b') b) ∪ (Finset.Ioc (max a' b) b')) hsubB
    (fun m => if m ∈ Finset.Ioc (max a b') b then c m else -c m) hd₂ T hT
  linarith


open MeasureTheory Finset ExpSums in
/-- **The decomposition lemma on an e-adic cell** (Track R, A2-III,
II-2d): for two primes `q ≤ p` of the same e-adic cell at resolution
`2N`, the quotient windows they cut out of `(A, B]` carry phase
polynomials whose energies differ by two `1/N`-collars —

  `∫_{−T}^{T} ‖∑_{(A/p, B/p]} − ∑_{(A/q, B/q]}‖²
     ≤ 2e^π(T/(A/p) + 4)·(A/(Np) + 1)/(A/p)
       + 2e^π(T/(B/p) + 4)·(B/(Np) + 1)/(B/p)`.

This is `[MR]`'s decomposition lemma in the form the band assembly
consumes: every prime of a cell may be replaced by one fixed reference
prime of that cell, at a cost of `O(1/N)` per prime.  The main terms
`(A/(Np))/(A/p) ≈ 1/N` are the genuine collar cost; the `+1`s are the
`ℕ`-division floors, contributing `p/A` — negligible at the scales the
assembly runs at, but honestly carried here.

The polynomial runs over the *full* quotient window with a global
coefficient function `c`.  That is deliberate: in the assembly the
Ramaré fibre is a proper subset of the window (the typical-set
quotients), and it is recovered by letting `c` vanish off it — which is
also why the collars of `sum_Ioc_eq_sum_Ioc_add_collars` had to be
independent of the coefficients.

`eadicCell_ratio_le` supplies the arithmetic ratio, and
`div_le_div_add_div_add_one` turns it into the two collar lengths. -/
theorem intervalIntegral_norm_sq_cell_fibre_sub_le
    {P : Finset ℕ} {N v : ℕ} (hN : 0 < N) {p q : ℕ}
    (hp : p ∈ eadicCell P (2*N) v) (hq : q ∈ eadicCell P (2*N) v)
    (hq1 : 1 ≤ q) (hqp : q ≤ p)
    (A B : ℕ) (hAB : A ≤ B)
    (hLA : A/(N*p) + 1 ≤ A/p) (hLB : B/(N*p) + 1 ≤ B/p)
    (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (T : ℝ) (hT : 0 < T) :
    (∫ ξ in (-T)..T,
        ‖(∑ m ∈ Finset.Ioc (A/p) (B/p), (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
          - (∑ m ∈ Finset.Ioc (A/q) (B/q), (c m/(m:ℂ)) * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))‖^2)
      ≤ 2 * (Real.exp Real.pi * (T/((A/p : ℕ):ℝ) + 4)
              * (((A/(N*p) + 1 : ℕ):ℝ)/((A/p : ℕ):ℝ)))
        + 2 * (Real.exp Real.pi * (T/((B/p : ℕ):ℝ) + 4)
              * (((B/(N*p) + 1 : ℕ):ℝ)/((B/p : ℕ):ℝ))) := by
  have hp1 : 1 ≤ p := le_trans hq1 hqp
  have hratio := eadicCell_ratio_le hN hp hq hp1 hq1
  have hAq := div_le_div_add_div_add_one A N p q hN hq1 hqp hratio
  have hBq := div_le_div_add_div_add_one B N p q hN hq1 hqp hratio
  -- the larger prime cuts the smaller window
  have hdivA : A/p ≤ A/q := Nat.div_le_div_left hqp hq1
  have hdivB : B/p ≤ B/q := Nat.div_le_div_left hqp hq1
  -- the side conditions, by hand: `omega` treats `A/(N*p)` (variable divisor)
  -- as an opaque atom and does not even know it is nonnegative
  have hcolA : A/q ≤ A/p + (A/(N*p) + 1) := by
    rw [← Nat.add_assoc]; exact hAq
  have hcolB : B/q ≤ B/p + (B/(N*p) + 1) := by
    rw [← Nat.add_assoc]; exact hBq
  have hA1 : 1 ≤ A/p := le_trans (Nat.le_add_left 1 (A/(N*p))) hLA
  have hB1 : 1 ≤ B/p := le_trans (Nat.le_add_left 1 (B/(N*p))) hLB
  have hminA : min (A/p) (A/q) = A/p := min_eq_left hdivA
  have hminB : min (B/p) (B/q) = B/p := min_eq_left hdivB
  have hmaxA : max (A/p) (A/q) = A/q := max_eq_right hdivA
  have hmaxB : max (B/p) (B/q) = B/q := max_eq_right hdivB
  have hkey := intervalIntegral_norm_sq_window_sub_le
    (A/p) (B/p) (A/q) (B/q) (A/(N*p) + 1) (B/(N*p) + 1)
    (Nat.div_le_div_right hAB) (Nat.div_le_div_right hAB)
    (by rw [hmaxA, hminA]; exact hcolA) (by rw [hmaxB, hminB]; exact hcolB)
    (by rw [hminA]; exact hLA) (by rw [hminB]; exact hLB)
    (by rw [hminA]; exact hA1) (by rw [hminB]; exact hB1)
    c hc T hT
  rwa [hminA, hminB] at hkey

end MoltResearch
