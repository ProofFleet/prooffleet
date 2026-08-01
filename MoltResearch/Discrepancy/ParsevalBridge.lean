import MoltResearch.Discrepancy.TuranKubilius

/-!
# Track C: the Parseval bridge (Track R, B-arc)

The bridge from the major-arc interface's log-averaged window target

  `∑_{n ∈ (x/w, x]} ‖W_n‖/(H·n) ≤ ε·log w`

to the frequency-side objects (`PlancherelHarness`,
`DyadicMVT`/`HalaszEuler` energies). Units: B1 the outer
Cauchy–Schwarz (this file's opener), B2 the dyadic range decomposition,
B3 the discrete-to-smoothed window comparison, B4 the per-dyadic
regime-split assembly.
-/

open Finset

namespace MoltResearch

/-- **The outer Cauchy–Schwarz** (Track R, B1): a log-averaged sum of
nonnegative window data is controlled by the harmonic mass times the
log-averaged mean square — the first step of the Parseval bridge, which
trades the interface's `∑ ‖W_n‖/(Hn)`-target for a mean-square object
at cost `√(log w)`. -/
theorem sum_div_le_sqrt_mul_sqrt (a b : ℕ) (W : ℕ → ℝ) (hW : ∀ n, 0 ≤ W n) :
    ∑ n ∈ Finset.Ioc a b, W n/n
      ≤ Real.sqrt (∑ n ∈ Finset.Ioc a b, (1:ℝ)/n)
        * Real.sqrt (∑ n ∈ Finset.Ioc a b, (W n)^2/n) := by
  classical
  have hn1 : ∀ n ∈ Finset.Ioc a b, 1 ≤ n := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    omega
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Ioc a b)
    (fun n => 1/Real.sqrt n) (fun n => W n/Real.sqrt n)
  have hprod : ∀ n ∈ Finset.Ioc a b,
      (1/Real.sqrt n) * (W n/Real.sqrt n) = W n/n := by
    intro n hn
    have h0 : (0:ℝ) < (n:ℝ) := by
      have := hn1 n hn
      exact_mod_cast this
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt h0.le]
  have hfsq : ∀ n ∈ Finset.Ioc a b, (1/Real.sqrt n)^2 = 1/(n:ℝ) := by
    intro n hn
    have h0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    rw [div_pow, one_pow, Real.sq_sqrt h0]
  have hgsq : ∀ n ∈ Finset.Ioc a b, (W n/Real.sqrt n)^2 = (W n)^2/n := by
    intro n hn
    have h0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    rw [div_pow, Real.sq_sqrt h0]
  rw [Finset.sum_congr rfl hprod, Finset.sum_congr rfl hfsq,
    Finset.sum_congr rfl hgsq] at hcs
  have hnn : (0:ℝ) ≤ ∑ n ∈ Finset.Ioc a b, W n/n :=
    Finset.sum_nonneg fun n hn => by
      have := hW n
      positivity
  have h1nn : (0:ℝ) ≤ ∑ n ∈ Finset.Ioc a b, (1:ℝ)/n :=
    Finset.sum_nonneg fun n _ => by positivity
  calc ∑ n ∈ Finset.Ioc a b, W n/n
      = Real.sqrt ((∑ n ∈ Finset.Ioc a b, W n/n)^2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((∑ n ∈ Finset.Ioc a b, (1:ℝ)/n)
          * ∑ n ∈ Finset.Ioc a b, (W n)^2/n) := Real.sqrt_le_sqrt hcs
    _ = Real.sqrt (∑ n ∈ Finset.Ioc a b, (1:ℝ)/n)
          * Real.sqrt (∑ n ∈ Finset.Ioc a b, (W n)^2/n) := Real.sqrt_mul h1nn _

/-- **The dyadic decomposition** (Track R, B2): any range sum splits into
its dyadic fibres `Nat.log 2 n = k`; each fibre sits in `[2^k, 2^{k+1})`
(by `Nat.pow_log_le_self` / `Nat.lt_pow_succ_log_self`), the dyadic
block shape that the MVT and the smoothed-window comparison consume,
and there are at most `log₂ b + 1` fibres. -/
theorem sum_Ioc_eq_sum_dyadic_fibres {M : Type*} [AddCommMonoid M]
    (a b : ℕ) (f : ℕ → M) :
    ∑ n ∈ Finset.Ioc a b, f n
      = ∑ k ∈ Finset.range (Nat.log 2 b + 1),
          ∑ n ∈ (Finset.Ioc a b).filter (fun n => Nat.log 2 n = k), f n := by
  classical
  refine (Finset.sum_fiberwise_of_maps_to ?_ f).symm
  intro n hn
  rw [Finset.mem_Ioc] at hn
  rw [Finset.mem_range]
  have := Nat.log_mono_right (b := 2) hn.2
  omega


/-- **The shift average** (Track R, B3-i, Saffari–Vaughan): a sharp
window sum differs from the average of its `U` shifts by at most `U` —
each shift changes the window by two boundary strips of length `≤ U`,
trivially bounded. The mean-square consumer pays `2U²` per point and
gains a trapezoidal (smoothable) window shape. -/
theorem norm_window_sub_shift_avg_le (h : ℕ → ℂ) (hb : ∀ m, ‖h m‖ ≤ 1)
    (n H U : ℕ) (hU : 0 < U) (hUH : U ≤ H) :
    ‖(∑ m ∈ Finset.Ioc n (n+H), h m)
        - (1/(U:ℂ)) * ∑ u ∈ Finset.range U, ∑ m ∈ Finset.Ioc (n+u) (n+u+H), h m‖
      ≤ U := by
  classical
  have hU0 : ((U:ℂ)) ≠ 0 := by exact_mod_cast hU.ne'
  -- rewrite the difference as the averaged strip difference
  have havg : (∑ m ∈ Finset.Ioc n (n+H), h m)
      - (1/(U:ℂ)) * ∑ u ∈ Finset.range U, ∑ m ∈ Finset.Ioc (n+u) (n+u+H), h m
      = (1/(U:ℂ)) * ∑ u ∈ Finset.range U,
          ((∑ m ∈ Finset.Ioc n (n+H), h m)
            - ∑ m ∈ Finset.Ioc (n+u) (n+u+H), h m) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      mul_sub, nsmul_eq_mul]
    congr 1
    field_simp
  rw [havg, norm_mul]
  have hnorm_inv : ‖(1/(U:ℂ))‖ = 1/(U:ℝ) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  rw [hnorm_inv]
  -- per-shift strip decomposition
  have hstrip : ∀ u ∈ Finset.range U,
      ‖(∑ m ∈ Finset.Ioc n (n+H), h m)
        - ∑ m ∈ Finset.Ioc (n+u) (n+u+H), h m‖ ≤ 2*(u:ℝ) := by
    intro u hu
    rw [Finset.mem_range] at hu
    have huH : u ≤ H := le_trans hu.le hUH
    have hsplit1 : ∑ m ∈ Finset.Ioc n (n+u), h m
        + ∑ m ∈ Finset.Ioc (n+u) (n+H), h m
        = ∑ m ∈ Finset.Ioc n (n+H), h m :=
      Finset.sum_Ioc_consecutive _ (by omega) (by omega)
    have hsplit2 : ∑ m ∈ Finset.Ioc (n+u) (n+H), h m
        + ∑ m ∈ Finset.Ioc (n+H) (n+u+H), h m
        = ∑ m ∈ Finset.Ioc (n+u) (n+u+H), h m :=
      Finset.sum_Ioc_consecutive _ (by omega) (by omega)
    have hdiff : (∑ m ∈ Finset.Ioc n (n+H), h m)
        - ∑ m ∈ Finset.Ioc (n+u) (n+u+H), h m
        = (∑ m ∈ Finset.Ioc n (n+u), h m)
          - ∑ m ∈ Finset.Ioc (n+H) (n+u+H), h m := by
      rw [← hsplit1, ← hsplit2]
      ring
    rw [hdiff]
    have hA : ‖∑ m ∈ Finset.Ioc n (n+u), h m‖ ≤ (u:ℝ) := by
      refine le_trans (norm_sum_le _ _) ?_
      calc ∑ m ∈ Finset.Ioc n (n+u), ‖h m‖
          ≤ ∑ _m ∈ Finset.Ioc n (n+u), (1:ℝ) := Finset.sum_le_sum fun m _ => hb m
        _ = ((Finset.Ioc n (n+u)).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ = (u:ℝ) := by
            rw [Nat.card_Ioc]
            congr 1
            omega
    have hD : ‖∑ m ∈ Finset.Ioc (n+H) (n+u+H), h m‖ ≤ (u:ℝ) := by
      refine le_trans (norm_sum_le _ _) ?_
      calc ∑ m ∈ Finset.Ioc (n+H) (n+u+H), ‖h m‖
          ≤ ∑ _m ∈ Finset.Ioc (n+H) (n+u+H), (1:ℝ) :=
            Finset.sum_le_sum fun m _ => hb m
        _ = ((Finset.Ioc (n+H) (n+u+H)).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ = (u:ℝ) := by
            rw [Nat.card_Ioc]
            congr 1
            omega
    calc ‖(∑ m ∈ Finset.Ioc n (n+u), h m)
          - ∑ m ∈ Finset.Ioc (n+H) (n+u+H), h m‖
        ≤ ‖∑ m ∈ Finset.Ioc n (n+u), h m‖
          + ‖∑ m ∈ Finset.Ioc (n+H) (n+u+H), h m‖ := norm_sub_le _ _
      _ ≤ (u:ℝ) + u := add_le_add hA hD
      _ = 2*(u:ℝ) := by ring
  calc (1/(U:ℝ)) * ‖∑ u ∈ Finset.range U,
        ((∑ m ∈ Finset.Ioc n (n+H), h m)
          - ∑ m ∈ Finset.Ioc (n+u) (n+u+H), h m)‖
      ≤ (1/(U:ℝ)) * ∑ u ∈ Finset.range U, 2*(u:ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum hstrip)
    _ = (1/(U:ℝ)) * (2 * ∑ u ∈ Finset.range U, (u:ℝ)) := by
        rw [← Finset.mul_sum]
    _ = (1/(U:ℝ)) * ((U:ℝ) * ((U:ℝ) - 1)) := by
        have hg := Finset.sum_range_id_mul_two U
        have h2 : (((∑ i ∈ Finset.range U, i) * 2 : ℕ) : ℝ) = ((U * (U-1) : ℕ) : ℝ) := by
          exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hg
        push_cast [Nat.cast_sub hU] at h2
        congr 1
        linarith [h2]
    _ = (U:ℝ) - 1 := by
        field_simp
    _ ≤ (U:ℝ) := by linarith


/-- **The trapezoid identity** (Track R, B3-ii): the sum of `U` shifted
windows is a single weighted sum whose weight at `m` counts the shifts
whose window contains `m` — the trapezoidal profile (ramp of width `U`,
plateau, ramp), supported in `(n, n+U+H]`. Exact; the smoothing
comparison consumes the count's plateau and support facts. -/
theorem shift_avg_eq_sum_count (h : ℕ → ℂ) (n H U : ℕ) :
    ∑ u ∈ Finset.range U, ∑ m ∈ Finset.Ioc (n+u) (n+u+H), h m
      = ∑ m ∈ Finset.Ioc n (n+U+H),
          (((Finset.range U).filter (fun u => n+u < m ∧ m ≤ n+u+H)).card : ℂ)
            * h m := by
  classical
  have hsub : ∀ u ∈ Finset.range U,
      ∑ m ∈ Finset.Ioc (n+u) (n+u+H), h m
        = ∑ m ∈ Finset.Ioc n (n+U+H),
            if n+u < m ∧ m ≤ n+u+H then h m else 0 := by
    intro u hu
    rw [Finset.mem_range] at hu
    rw [show Finset.Ioc (n+u) (n+u+H)
        = (Finset.Ioc n (n+U+H)).filter (fun m => n+u < m ∧ m ≤ n+u+H) from by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      omega]
    rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl hsub, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.card_filter]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun u hu => ?_
  by_cases hc : n+u < m ∧ m ≤ n+u+H
  · simp [hc]
  · simp [hc]


end MoltResearch
