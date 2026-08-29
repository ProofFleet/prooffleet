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

end MoltResearch
