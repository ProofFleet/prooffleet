import MoltResearch.Discrepancy.MertensFloor

/-!
# Discrepancy: the Turán–Kubilius substrate (Track R, cheap-frame C1)

The harmonic window for the Turán–Kubilius inequality on prime blocks
(campaign #3044, phase C1): the harmonic ceiling `∑_{1≤n≤y} 1/n ≤ log y + 1`
(the mirror of `log_le_sum_one_div_Ico`), and the dvd-filtered harmonic
window — the harmonic sum over multiples of `k` in `[1, N)` reindexes to
`(1/k)·∑_{1≤m≤(N-1)/k} 1/m` and is squeezed between
`(1/k)(log N − log k − 2)` and `(1/k)(log N + 1)`.

These feed the first/second moment computations of the block
Turán–Kubilius variance bound (C1c–C1e).
-/

namespace MoltResearch

open Finset

/-- **The harmonic ceiling**: `∑_{1 ≤ n ≤ y} 1/n ≤ log y + 1` — telescoping
`1/(n+1) ≤ log (n+1) − log n` from `log(1 − u) ≤ −u`. -/
theorem sum_one_div_Ico_succ_le_log_add_one (y : ℕ) :
    ∑ n ∈ Finset.Ico 1 (y + 1), (1 : ℝ) / n ≤ Real.log y + 1 := by
  induction y with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · norm_num
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hstep : (1 : ℝ) / (m + 1) ≤ Real.log (m + 1) - Real.log m := by
      have h1 : Real.log ((m : ℝ) / (m + 1)) ≤ (m : ℝ) / (m + 1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h2 : Real.log ((m : ℝ) / (m + 1))
          = Real.log m - Real.log (m + 1) :=
        Real.log_div (ne_of_gt hm0) (by positivity)
      have h3 : (m : ℝ) / (m + 1) - 1 = -(1 / (m + 1)) := by
        field_simp
        ring
      rw [h2, h3] at h1
      linarith
    push_cast
    linarith

/-- The harmonic ceiling, plain `Ico` form. -/
theorem sum_one_div_Ico_le_log_add_one (y : ℕ) :
    ∑ n ∈ Finset.Ico 1 y, (1 : ℝ) / n ≤ Real.log y + 1 := by
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp
  have h1 : y = (y - 1) + 1 := by omega
  rw [h1]
  refine le_trans (sum_one_div_Ico_succ_le_log_add_one (y - 1)) ?_
  have h2 : Real.log ((y - 1 : ℕ)) ≤ Real.log ((y - 1 : ℕ) + 1 : ℕ) := by
    rcases Nat.eq_zero_or_pos (y - 1) with h3 | h3
    · rw [h3, Nat.cast_zero, Real.log_zero]
      exact Real.log_natCast_nonneg _
    · refine Real.log_le_log (by exact_mod_cast h3) ?_
      exact_mod_cast Nat.le_succ _
  push_cast at h2 ⊢
  linarith

/-- **The dvd reindex**: the harmonic sum over multiples of `k` in `[1, N)`
is `(1/k)` times the harmonic sum over `[1, (N-1)/k]`. -/
theorem sum_one_div_filter_dvd_eq (k N : ℕ) (hk : 1 ≤ k) :
    ∑ n ∈ (Finset.Ico 1 N).filter (k ∣ ·), (1 : ℝ) / n
      = (1 / k) * ∑ m ∈ Finset.Ico 1 ((N - 1) / k + 1), (1 : ℝ) / m := by
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun n => n / k) (fun m => k * m) ?_ ?_ ?_ ?_ ?_
  · dsimp only
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ico] at hn
    obtain ⟨⟨hn1, hn2⟩, c, hc⟩ := hn
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with rfl | h
      · rw [Nat.mul_zero] at hc
        omega
      · exact h
    rw [Finset.mem_Ico, hc, Nat.mul_div_cancel_left c (by omega)]
    have hck : c * k = k * c := Nat.mul_comm c k
    refine ⟨hc1, ?_⟩
    have h4 : c ≤ (N - 1) / k := by
      refine (Nat.le_div_iff_mul_le (by omega)).mpr ?_
      omega
    omega
  · dsimp only
    intro m hm
    rw [Finset.mem_Ico] at hm
    obtain ⟨hm1, hm2⟩ := hm
    have h1 : k * m ≤ N - 1 := by
      have h2 : m ≤ (N - 1) / k := by omega
      calc k * m ≤ k * ((N - 1) / k) := Nat.mul_le_mul_left k h2
        _ ≤ N - 1 := Nat.mul_div_le _ _
    have h2 : 0 < k * m := Nat.mul_pos (by omega) (by omega)
    rw [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨by omega, by omega⟩, ⟨m, rfl⟩⟩
  · dsimp only
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨_, c, hc⟩ := hn
    rw [hc, Nat.mul_div_cancel_left c (by omega)]
  · dsimp only
    intro m _
    rw [Nat.mul_div_cancel_left m (by omega)]
  · dsimp only
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨_, c, hc⟩ := hn
    rw [hc, Nat.mul_div_cancel_left c (by omega)]
    push_cast
    rw [one_div, one_div, one_div, mul_inv]

/-- **The dvd-filtered harmonic ceiling**:
`∑_{n < N, k ∣ n} 1/n ≤ (1/k)(log N + 1)`. -/
theorem sum_one_div_filter_dvd_le (k N : ℕ) (hk : 1 ≤ k) :
    ∑ n ∈ (Finset.Ico 1 N).filter (k ∣ ·), (1 : ℝ) / n
      ≤ (1 / k) * (Real.log N + 1) := by
  rw [sum_one_div_filter_dvd_eq k N hk]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (sum_one_div_Ico_succ_le_log_add_one _) ?_
  have h1 : Real.log (((N - 1) / k : ℕ)) ≤ Real.log N := by
    rcases Nat.eq_zero_or_pos ((N - 1) / k) with h2 | h2
    · rw [h2, Nat.cast_zero, Real.log_zero]
      exact Real.log_natCast_nonneg N
    · refine Real.log_le_log (by exact_mod_cast h2) ?_
      have h3 : (N - 1) / k ≤ N := le_trans (Nat.div_le_self _ _) (by omega)
      exact_mod_cast h3
  linarith

/-- **The dvd-filtered harmonic floor**: for `2k ≤ N`,
`(1/k)(log N − log k − 2) ≤ ∑_{n < N, k ∣ n} 1/n`. -/
theorem le_sum_one_div_filter_dvd (k N : ℕ) (hk : 1 ≤ k) (hkN : 2 * k ≤ N) :
    (1 / k) * (Real.log N - Real.log k - 2)
      ≤ ∑ n ∈ (Finset.Ico 1 N).filter (k ∣ ·), (1 : ℝ) / n := by
  rw [sum_one_div_filter_dvd_eq k N hk]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans ?_ (MoltResearch.log_le_sum_one_div_Ico _)
  -- `(N-1)/k + 1 > (N-1)/k ≥ (N-1)/k` in `ℝ`, and `N/2 ≤ N-1`
  have hN2 : (2:ℝ) ≤ (N:ℝ) := by
    have : 2 ≤ N := by omega
    exact_mod_cast this
  have hNat : N - 1 < ((N - 1) / k + 1) * k := by
    calc N - 1 = k * ((N - 1) / k) + (N - 1) % k :=
          (Nat.div_add_mod _ _).symm
      _ < k * ((N - 1) / k) + k := by
          have := Nat.mod_lt (N - 1) (show 0 < k by omega)
          omega
      _ = ((N - 1) / k + 1) * k := by ring
  have h1 : ((N:ℝ) - 1) / k < (((N - 1) / k + 1 : ℕ) : ℝ) := by
    rw [div_lt_iff₀ hk0]
    have h2 : ((N - 1 : ℕ) : ℝ) < (((N - 1) / k + 1 : ℕ) : ℝ) * k := by
      exact_mod_cast hNat
    have h3 : ((N:ℝ) - 1) = ((N - 1 : ℕ) : ℝ) := by
      have h4 : 1 ≤ N := by omega
      have h5 : ((N - 1 : ℕ) : ℝ) = (N:ℝ) - 1 := by
        push_cast [h4]
        ring
      linarith [h5]
    rw [h3]
    exact h2
  have h5 : Real.log N - Real.log k - 2
      ≤ Real.log (((N:ℝ) - 1) / k) := by
    have h6 : Real.log (((N:ℝ) - 1) / k)
        = Real.log ((N:ℝ) - 1) - Real.log k := by
      rw [Real.log_div (by linarith) (ne_of_gt hk0)]
    have h7 : Real.log N - Real.log 2 ≤ Real.log ((N:ℝ) - 1) := by
      have h8 : (N:ℝ) / 2 ≤ (N:ℝ) - 1 := by linarith
      calc Real.log N - Real.log 2 = Real.log ((N:ℝ)/2) := by
            rw [Real.log_div (by linarith) (by norm_num)]
        _ ≤ Real.log ((N:ℝ) - 1) :=
            Real.log_le_log (by linarith) h8
    have h9 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
      linarith
    rw [h6]
    linarith
  refine le_trans h5 ?_
  refine Real.log_le_log ?_ h1.le
  have h10 : (0:ℝ) < (N:ℝ) - 1 := by linarith
  positivity

end MoltResearch
