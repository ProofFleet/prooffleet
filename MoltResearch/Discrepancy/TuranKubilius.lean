import MoltResearch.Discrepancy.MertensFloor
import MoltResearch.Discrepancy.MertensFirst
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Sqrt

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

/-- **The first-moment swap**: with `ω_P(n) := #{p ∈ P : p ∣ n}`,
`∑_{n<N} ω_P(n)/n` unfolds prime-by-prime into the dvd-filtered
harmonic sums. -/
theorem sum_card_dvd_div_eq (P : Finset ℕ) (N : ℕ) :
    ∑ n ∈ Finset.Ico 1 N, ((P.filter (· ∣ n)).card : ℝ) / n
      = ∑ p ∈ P, ∑ n ∈ (Finset.Ico 1 N).filter (p ∣ ·), (1 : ℝ) / n := by
  have h1 : ∀ n : ℕ, ((P.filter (· ∣ n)).card : ℝ) / n
      = ∑ p ∈ P, if p ∣ n then (1 : ℝ) / n else 0 := by
    intro n
    rw [Finset.card_filter]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : p ∣ n
    · simp [h]
    · simp [h]
  rw [Finset.sum_congr rfl fun n _ => h1 n, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_filter]

/-- **The second-moment split**: `∑_{n<N} ω_P(n)²/n` is at most the first
moment plus the off-diagonal dvd-filtered sums at the products `p·q` of
distinct primes of `P`. -/
theorem sum_card_sq_dvd_div_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (N : ℕ) :
    ∑ n ∈ Finset.Ico 1 N, ((P.filter (· ∣ n)).card : ℝ)^2 / n
      ≤ ∑ n ∈ Finset.Ico 1 N, ((P.filter (· ∣ n)).card : ℝ) / n
        + ∑ p ∈ P, ∑ q ∈ P.erase p,
            ∑ n ∈ (Finset.Ico 1 N).filter ((p*q) ∣ ·), (1 : ℝ) / n := by
  have hpoint : ∀ n ∈ Finset.Ico 1 N,
      ((P.filter (· ∣ n)).card : ℝ)^2 / n
        ≤ ((P.filter (· ∣ n)).card : ℝ) / n
          + ∑ p ∈ P, ∑ q ∈ P.erase p,
              (if p*q ∣ n then (1:ℝ)/n else 0) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn0 : (0:ℝ) < n := by
      have := hn.1
      exact_mod_cast this
    have hcard : ((P.filter (· ∣ n)).card : ℝ)
        = ∑ p ∈ P, (if p ∣ n then (1:ℝ) else 0) := by
      rw [Finset.card_filter]
      push_cast
      rfl
    have hnum : ((P.filter (· ∣ n)).card : ℝ)^2
        ≤ ((P.filter (· ∣ n)).card : ℝ)
          + ∑ p ∈ P, ∑ q ∈ P.erase p, (if p*q ∣ n then (1:ℝ) else 0) := by
      rw [hcard, sq, Finset.sum_mul_sum]
      have hsplit : ∀ p ∈ P,
          ∑ q ∈ P, (if p ∣ n then (1:ℝ) else 0)
              * (if q ∣ n then (1:ℝ) else 0)
            = (if p ∣ n then (1:ℝ) else 0) * (if p ∣ n then (1:ℝ) else 0)
              + ∑ q ∈ P.erase p, (if p ∣ n then (1:ℝ) else 0)
                  * (if q ∣ n then (1:ℝ) else 0) := by
        intro p hp
        exact (Finset.add_sum_erase P
          (fun q => (if p ∣ n then (1:ℝ) else 0)
            * (if q ∣ n then (1:ℝ) else 0)) hp).symm
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
      have hdiag : ∑ p ∈ P, (if p ∣ n then (1:ℝ) else 0)
            * (if p ∣ n then (1:ℝ) else 0)
          = ∑ p ∈ P, (if p ∣ n then (1:ℝ) else 0) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases h : p ∣ n <;> simp [h]
      rw [hdiag]
      refine add_le_add (le_refl _) ?_
      refine Finset.sum_le_sum fun p hp => ?_
      refine Finset.sum_le_sum fun q hq => ?_
      rw [Finset.mem_erase] at hq
      by_cases h1 : p ∣ n
      · by_cases h2 : q ∣ n
        · have h3 : p*q ∣ n := by
            have hco : Nat.Coprime p q :=
              (Nat.coprime_primes (hP p hp) (hP q hq.2)).mpr (Ne.symm hq.1)
            exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hco h1 h2
          simp [h1, h2, h3]
        · have h4 : (0:ℝ) ≤ if p*q ∣ n then (1:ℝ) else 0 := by
            split <;> norm_num
          simpa [h1, h2] using h4
      · have h4 : (0:ℝ) ≤ if p*q ∣ n then (1:ℝ) else 0 := by
          split <;> norm_num
        simpa [h1] using h4
    have hstep : ((P.filter (· ∣ n)).card : ℝ)^2 / n
        ≤ (((P.filter (· ∣ n)).card : ℝ)
            + ∑ p ∈ P, ∑ q ∈ P.erase p, (if p*q ∣ n then (1:ℝ) else 0)) / n := by
      exact div_le_div_of_nonneg_right hnum hn0.le
    refine le_trans hstep ?_
    rw [add_div]
    refine add_le_add (le_refl _) (le_of_eq ?_)
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases h : p*q ∣ n
    · simp [h]
    · simp [h]
  refine le_trans (Finset.sum_le_sum hpoint) ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add (le_refl _) (le_of_eq ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_filter]

/-- **The block Turán–Kubilius variance bound** (C1d): with
`ω_P(n) := #{p ∈ P : p ∣ n}` and `E := ∑_{p∈P} 1/p`, for a prime set `P`
inside `[1, Pmax]` with `2·Pmax ≤ N`,
`∑_{n<N} (ω_P(n) − E)²/n ≤ E·log N + 8·E·log(Pmax+1) + 6E² + E`.
All four moment pieces come from the harmonic window; the `log p/p` sum
is Mertens' first theorem. -/
theorem tk_variance (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (N Pmax : ℕ)
    (hPle : ∀ p ∈ P, p ≤ Pmax) (h2P : 2 * Pmax ≤ N) :
    ∑ n ∈ Finset.Ico 1 N,
        (((P.filter (· ∣ n)).card : ℝ) - ∑ p ∈ P, (1:ℝ)/p)^2 / n
      ≤ (∑ p ∈ P, (1:ℝ)/p) * Real.log N
        + 8 * (∑ p ∈ P, (1:ℝ)/p) * Real.log (Pmax + 1)
        + 6 * (∑ p ∈ P, (1:ℝ)/p)^2 + (∑ p ∈ P, (1:ℝ)/p) := by
  have hE0 : (0:ℝ) ≤ ∑ p ∈ P, (1:ℝ)/p :=
    Finset.sum_nonneg fun p _ => by positivity
  have hp1 : ∀ p ∈ P, 1 ≤ p := fun p hp => (hP p hp).one_lt.le
  -- the expansion into the three moments
  have hexpand : ∑ n ∈ Finset.Ico 1 N,
        (((P.filter (· ∣ n)).card : ℝ) - ∑ p ∈ P, (1:ℝ)/p)^2 / n
      = (∑ n ∈ Finset.Ico 1 N, ((P.filter (· ∣ n)).card : ℝ)^2 / n)
        - 2*(∑ p ∈ P, (1:ℝ)/p)
            * (∑ n ∈ Finset.Ico 1 N, ((P.filter (· ∣ n)).card : ℝ) / n)
        + (∑ p ∈ P, (1:ℝ)/p)^2
            * (∑ n ∈ Finset.Ico 1 N, (1:ℝ) / n) := by
    have h1 : ∑ n ∈ Finset.Ico 1 N,
          (((P.filter (· ∣ n)).card : ℝ) - ∑ p ∈ P, (1:ℝ)/p)^2 / n
        = ∑ n ∈ Finset.Ico 1 N,
            (((P.filter (· ∣ n)).card : ℝ)^2 / n
              - 2*(∑ p ∈ P, (1:ℝ)/p) * (((P.filter (· ∣ n)).card : ℝ) / n)
              + (∑ p ∈ P, (1:ℝ)/p)^2 * ((1:ℝ) / n)) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_Ico] at hn
      have hn0 : ((n:ℝ)) ≠ 0 := by
        have : (0:ℝ) < n := by exact_mod_cast hn.1
        linarith
      field_simp
      ring
    rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
  -- Mertens' first theorem on the block
  have hmert : ∑ p ∈ P, Real.log p / p ≤ 4*Real.log (Pmax+1) := by
    have hsub : P ⊆ Nat.primesBelow (Pmax+1) := by
      intro p hp
      rw [Nat.mem_primesBelow]
      exact ⟨by have := hPle p hp; omega, hP p hp⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) ?_
    · intro p _ _
      exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
    · have h1 := sum_log_div_primesBelow_le (Pmax+1)
      have h2 : (((Pmax+1 : ℕ)):ℝ) = (Pmax:ℝ) + 1 := by push_cast; ring
      rw [h2] at h1
      exact h1
  -- the first moment, both sides
  have hS1eq := sum_card_dvd_div_eq P N
  have hS1up : ∑ n ∈ Finset.Ico 1 N, ((P.filter (· ∣ n)).card : ℝ) / n
      ≤ (∑ p ∈ P, (1:ℝ)/p) * (Real.log N + 1) := by
    rw [hS1eq]
    calc ∑ p ∈ P, ∑ n ∈ (Finset.Ico 1 N).filter (p ∣ ·), (1:ℝ)/n
        ≤ ∑ p ∈ P, (1/p) * (Real.log N + 1) :=
          Finset.sum_le_sum fun p hp =>
            sum_one_div_filter_dvd_le p N (hp1 p hp)
      _ = (∑ p ∈ P, (1:ℝ)/p) * (Real.log N + 1) := by
          rw [Finset.sum_mul]
  have hS1low : (∑ p ∈ P, (1:ℝ)/p) * Real.log N
        - 2*(∑ p ∈ P, (1:ℝ)/p) - 4*Real.log (Pmax+1)
      ≤ ∑ n ∈ Finset.Ico 1 N, ((P.filter (· ∣ n)).card : ℝ) / n := by
    rw [hS1eq]
    have hper : ∀ p ∈ P,
        (1/(p:ℝ)) * (Real.log N - Real.log p - 2)
          ≤ ∑ n ∈ (Finset.Ico 1 N).filter (p ∣ ·), (1:ℝ)/n := by
      intro p hp
      refine le_sum_one_div_filter_dvd p N (hp1 p hp) ?_
      have h1 := hPle p hp
      omega
    refine le_trans ?_ (Finset.sum_le_sum hper)
    have hid : ∑ p ∈ P, (1/(p:ℝ)) * (Real.log N - Real.log p - 2)
        = (∑ p ∈ P, (1:ℝ)/p) * Real.log N
          - (∑ p ∈ P, Real.log p / p) - 2*(∑ p ∈ P, (1:ℝ)/p) := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    rw [hid]
    linarith [hmert]
  -- the second moment
  have hS2 := sum_card_sq_dvd_div_le P hP N
  have hCR : ∑ p ∈ P, ∑ q ∈ P.erase p,
        ∑ n ∈ (Finset.Ico 1 N).filter ((p*q) ∣ ·), (1:ℝ)/n
      ≤ (∑ p ∈ P, (1:ℝ)/p)^2 * (Real.log N + 1) := by
    have hstep : ∀ p ∈ P, ∑ q ∈ P.erase p,
          ∑ n ∈ (Finset.Ico 1 N).filter ((p*q) ∣ ·), (1:ℝ)/n
        ≤ (1/(p:ℝ)) * (∑ p ∈ P, (1:ℝ)/p) * (Real.log N + 1) := by
      intro p hp
      calc ∑ q ∈ P.erase p,
              ∑ n ∈ (Finset.Ico 1 N).filter ((p*q) ∣ ·), (1:ℝ)/n
          ≤ ∑ q ∈ P.erase p, (1/((p*q : ℕ):ℝ)) * (Real.log N + 1) := by
            refine Finset.sum_le_sum fun q hq => ?_
            refine sum_one_div_filter_dvd_le (p*q) N ?_
            have h1 := hp1 p hp
            have h2 := hp1 q (Finset.mem_of_mem_erase hq)
            exact Nat.one_le_iff_ne_zero.mpr (by positivity)
        _ = (1/(p:ℝ)) * (∑ q ∈ P.erase p, (1:ℝ)/q) * (Real.log N + 1) := by
            rw [Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun q _ => ?_
            push_cast
            rw [mul_comm ((1:ℝ)/p) ((1:ℝ)/q)]
            rw [one_div, one_div, one_div, mul_inv]
            ring
        _ ≤ (1/(p:ℝ)) * (∑ p ∈ P, (1:ℝ)/p) * (Real.log N + 1) := by
            have hsub : ∑ q ∈ P.erase p, (1:ℝ)/q ≤ ∑ p ∈ P, (1:ℝ)/p := by
              refine Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.erase_subset _ _) ?_
              intro q _ _
              positivity
            have hlog1 : (0:ℝ) ≤ Real.log N + 1 := by
              have := Real.log_natCast_nonneg N
              linarith
            have hp0 : (0:ℝ) ≤ 1/(p:ℝ) := by positivity
            refine mul_le_mul_of_nonneg_right ?_ hlog1
            exact mul_le_mul_of_nonneg_left hsub hp0
    calc ∑ p ∈ P, ∑ q ∈ P.erase p,
            ∑ n ∈ (Finset.Ico 1 N).filter ((p*q) ∣ ·), (1:ℝ)/n
        ≤ ∑ p ∈ P, (1/(p:ℝ)) * (∑ p ∈ P, (1:ℝ)/p) * (Real.log N + 1) :=
          Finset.sum_le_sum hstep
      _ = (∑ p ∈ P, (1:ℝ)/p)^2 * (Real.log N + 1) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, sq]
  -- the harmonic factor
  have hH := sum_one_div_Ico_le_log_add_one N
  -- assemble
  have h2E : (0:ℝ) ≤ 2*(∑ p ∈ P, (1:ℝ)/p) := by linarith
  have hm1 : 2*(∑ p ∈ P, (1:ℝ)/p)
        * ((∑ p ∈ P, (1:ℝ)/p) * Real.log N
            - 2*(∑ p ∈ P, (1:ℝ)/p) - 4*Real.log (Pmax+1))
      ≤ 2*(∑ p ∈ P, (1:ℝ)/p)
        * (∑ n ∈ Finset.Ico 1 N, ((P.filter (· ∣ n)).card : ℝ) / n) :=
    mul_le_mul_of_nonneg_left hS1low h2E
  have hm2 : (∑ p ∈ P, (1:ℝ)/p)^2 * (∑ n ∈ Finset.Ico 1 N, (1:ℝ) / n)
      ≤ (∑ p ∈ P, (1:ℝ)/p)^2 * (Real.log N + 1) :=
    mul_le_mul_of_nonneg_left hH (sq_nonneg _)
  linarith [hexpand, hS2, hCR, hS1up, hm1, hm2]

/-- **The block Turán–Kubilius inequality** (C1e, the consumer ε-form):
for any `ε > 0`, whenever a prime set `P ⊆ [1, Pmax]` with `2·Pmax ≤ N` has
block mass `E := ∑_{p∈P} 1/p ≥ 32/ε² + 1` and `E ≤ log N`,
`log(Pmax+1) ≤ log N`, `1 ≤ log N`, then
`∑_{n<N} |ω_P(n)/E − 1|/n ≤ ε·log N` — most integers see the expected
number of block prime factors. Cauchy–Schwarz on the variance bound. -/
theorem turan_kubilius_block (ε : ℝ) (hε : 0 < ε) :
    ∃ E₀ : ℝ, 0 < E₀ ∧ ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ∀ N Pmax : ℕ, (∀ p ∈ P, p ≤ Pmax) → 2*Pmax ≤ N →
      E₀ ≤ ∑ p ∈ P, (1:ℝ)/p →
      (∑ p ∈ P, (1:ℝ)/p) ≤ Real.log N →
      Real.log (Pmax+1) ≤ Real.log N →
      1 ≤ Real.log N →
      ∑ n ∈ Finset.Ico 1 N,
          |((P.filter (· ∣ n)).card : ℝ)/(∑ p ∈ P, (1:ℝ)/p) - 1| / n
        ≤ ε * Real.log N := by
  refine ⟨32/ε^2 + 1, by positivity, ?_⟩
  intro P hP N Pmax hPle h2P hE₀ hEA hBA hA1
  have hE1 : (1:ℝ) ≤ ∑ p ∈ P, (1:ℝ)/p := by
    have h1 : (0:ℝ) < 32/ε^2 := by positivity
    linarith
  have hE0 : (0:ℝ) < ∑ p ∈ P, (1:ℝ)/p := by linarith
  -- the variance at budget `16·E·log N`
  have hvar := tk_variance P hP N Pmax hPle h2P
  have hvar16 : ∑ n ∈ Finset.Ico 1 N,
        (((P.filter (· ∣ n)).card : ℝ) - ∑ p ∈ P, (1:ℝ)/p)^2 / n
      ≤ 16 * (∑ p ∈ P, (1:ℝ)/p) * Real.log N := by
    have h1 : 8*(∑ p ∈ P, (1:ℝ)/p)*Real.log (Pmax+1)
        ≤ 8*(∑ p ∈ P, (1:ℝ)/p)*Real.log N := by
      rw [mul_assoc, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact mul_le_mul_of_nonneg_left hBA (by linarith)
    have h2 : (∑ p ∈ P, (1:ℝ)/p)*(∑ p ∈ P, (1:ℝ)/p)
        ≤ (∑ p ∈ P, (1:ℝ)/p)*Real.log N :=
      mul_le_mul_of_nonneg_left hEA hE0.le
    have h3 := mul_nonneg hE0.le (sub_nonneg.mpr hA1)
    nlinarith [hvar, h1, h2, h3]
  -- pull `1/E` out of the target
  have habs : ∑ n ∈ Finset.Ico 1 N,
        |((P.filter (· ∣ n)).card : ℝ)/(∑ p ∈ P, (1:ℝ)/p) - 1| / n
      = (1/(∑ p ∈ P, (1:ℝ)/p))
        * ∑ n ∈ Finset.Ico 1 N,
            |((P.filter (· ∣ n)).card : ℝ) - ∑ p ∈ P, (1:ℝ)/p| / n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [show ((P.filter (· ∣ n)).card : ℝ)/(∑ p ∈ P, (1:ℝ)/p) - 1
        = (((P.filter (· ∣ n)).card : ℝ) - ∑ p ∈ P, (1:ℝ)/p)
            /(∑ p ∈ P, (1:ℝ)/p) from by
        field_simp]
    rw [abs_div, abs_of_pos hE0]
    ring
  -- Cauchy–Schwarz against the harmonic weight
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Ico 1 N)
    (fun n => |((P.filter (· ∣ n)).card : ℝ) - ∑ p ∈ P, (1:ℝ)/p|
      / Real.sqrt n)
    (fun n => 1 / Real.sqrt n)
  have hfg : ∀ n ∈ Finset.Ico 1 N,
      (|((P.filter (· ∣ n)).card : ℝ) - ∑ p ∈ P, (1:ℝ)/p| / Real.sqrt n)
          * (1/Real.sqrt n)
        = |((P.filter (· ∣ n)).card : ℝ) - ∑ p ∈ P, (1:ℝ)/p| / n := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn.1
    rw [div_mul_div_comm, mul_one, Real.mul_self_sqrt hn0.le]
  have hf2 : ∀ n ∈ Finset.Ico 1 N,
      (|((P.filter (· ∣ n)).card : ℝ) - ∑ p ∈ P, (1:ℝ)/p| / Real.sqrt n)^2
        = (((P.filter (· ∣ n)).card : ℝ) - ∑ p ∈ P, (1:ℝ)/p)^2 / n := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn.1
    rw [div_pow, sq_abs, Real.sq_sqrt hn0.le]
  have hg2 : ∀ n ∈ Finset.Ico 1 N, ((1:ℝ)/Real.sqrt n)^2 = 1/n := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn.1
    rw [div_pow, one_pow, Real.sq_sqrt hn0.le]
  rw [Finset.sum_congr rfl hfg, Finset.sum_congr rfl hf2,
    Finset.sum_congr rfl hg2] at hCS
  -- the harmonic factor
  have hH : ∑ n ∈ Finset.Ico 1 N, (1:ℝ)/n ≤ 2*Real.log N := by
    have := sum_one_div_Ico_le_log_add_one N
    linarith
  have hHnn : (0:ℝ) ≤ ∑ n ∈ Finset.Ico 1 N, (1:ℝ)/n :=
    Finset.sum_nonneg fun n _ => by positivity
  -- square the budget
  have hT2 : (∑ n ∈ Finset.Ico 1 N,
        |((P.filter (· ∣ n)).card : ℝ) - ∑ p ∈ P, (1:ℝ)/p| / n)^2
      ≤ 32 * (∑ p ∈ P, (1:ℝ)/p) * (Real.log N)^2 := by
    refine le_trans hCS ?_
    have h16nn : (0:ℝ) ≤ 16 * (∑ p ∈ P, (1:ℝ)/p) * Real.log N := by
      have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 16) hE0.le)
        (by linarith : (0:ℝ) ≤ Real.log N)
      linarith
    calc (∑ n ∈ Finset.Ico 1 N,
          (((P.filter (· ∣ n)).card : ℝ) - ∑ p ∈ P, (1:ℝ)/p)^2 / n)
            * ∑ n ∈ Finset.Ico 1 N, (1:ℝ)/n
        ≤ (16 * (∑ p ∈ P, (1:ℝ)/p) * Real.log N)
            * ∑ n ∈ Finset.Ico 1 N, (1:ℝ)/n :=
          mul_le_mul_of_nonneg_right hvar16 hHnn
      _ ≤ (16 * (∑ p ∈ P, (1:ℝ)/p) * Real.log N) * (2*Real.log N) :=
          mul_le_mul_of_nonneg_left hH h16nn
      _ = 32 * (∑ p ∈ P, (1:ℝ)/p) * (Real.log N)^2 := by ring
  -- discharge through squares
  rw [habs, one_div, inv_mul_eq_div, div_le_iff₀ hE0]
  have hTnn : (0:ℝ) ≤ ∑ n ∈ Finset.Ico 1 N,
      |((P.filter (· ∣ n)).card : ℝ) - ∑ p ∈ P, (1:ℝ)/p| / n :=
    Finset.sum_nonneg fun n _ => by positivity
  have hrhs_nn : (0:ℝ) ≤ ε * Real.log N * (∑ p ∈ P, (1:ℝ)/p) :=
    mul_nonneg (mul_nonneg hε.le (by linarith)) hE0.le
  have h32 : (32:ℝ) ≤ ε^2*(∑ p ∈ P, (1:ℝ)/p) := by
    have h1 : ε^2*(32/ε^2 + 1) = 32 + ε^2 := by
      field_simp
    have h2 := mul_le_mul_of_nonneg_left hE₀ (sq_nonneg ε)
    nlinarith [sq_nonneg ε]
  have hsq : (∑ n ∈ Finset.Ico 1 N,
        |((P.filter (· ∣ n)).card : ℝ) - ∑ p ∈ P, (1:ℝ)/p| / n)^2
      ≤ (ε * Real.log N * (∑ p ∈ P, (1:ℝ)/p))^2 := by
    have hkey := mul_nonneg (sub_nonneg.mpr h32)
      (mul_nonneg hE0.le (sq_nonneg (Real.log N)))
    nlinarith [hT2, hkey]
  calc ∑ n ∈ Finset.Ico 1 N,
        |((P.filter (· ∣ n)).card : ℝ) - ∑ p ∈ P, (1:ℝ)/p| / n
      = Real.sqrt ((∑ n ∈ Finset.Ico 1 N,
          |((P.filter (· ∣ n)).card : ℝ) - ∑ p ∈ P, (1:ℝ)/p| / n)^2) :=
        (Real.sqrt_sq hTnn).symm
    _ ≤ Real.sqrt ((ε * Real.log N * (∑ p ∈ P, (1:ℝ)/p))^2) :=
        Real.sqrt_le_sqrt hsq
    _ = ε * Real.log N * (∑ p ∈ P, (1:ℝ)/p) := Real.sqrt_sq hrhs_nn

end MoltResearch
