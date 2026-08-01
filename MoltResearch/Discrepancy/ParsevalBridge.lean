import MoltResearch.Discrepancy.TuranKubilius
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

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


/-- **The collar comparison** (Track R, B3-iii-a): two `[0,1]`-valued
window weights that agree off a disagreement set `D` produce weighted
sums differing by at most `|D|` — the trivial counting bound that turns
the B3-ii trapezoid into any aligned smooth window (ramps and mollifier
collars land in `D`; no cancellation is needed there). -/
theorem norm_sum_mul_sub_weights_le (S D : Finset ℕ) (h : ℕ → ℂ)
    (hb : ∀ m, ‖h m‖ ≤ 1) (c ψ : ℕ → ℝ)
    (hc : ∀ m, 0 ≤ c m ∧ c m ≤ 1) (hψ : ∀ m, 0 ≤ ψ m ∧ ψ m ≤ 1)
    (hagree : ∀ m ∈ S, m ∉ D → c m = ψ m) :
    ‖∑ m ∈ S, h m * (((c m - ψ m : ℝ)) : ℂ)‖ ≤ (D.card : ℝ) := by
  classical
  have hzero : ∀ m ∈ S, m ∉ D → h m * (((c m - ψ m : ℝ)) : ℂ) = 0 := by
    intro m hm hd
    rw [hagree m hm hd]
    simp
  rw [← Finset.sum_filter_of_ne (fun m hm hne => by
    by_contra hd
    exact hne (hzero m hm hd))]
  refine le_trans (norm_sum_le _ _) ?_
  have hpt : ∀ m ∈ S.filter (· ∈ D),
      ‖h m * (((c m - ψ m : ℝ)) : ℂ)‖ ≤ 1 := by
    intro m _
    rw [norm_mul, Complex.norm_real]
    have h1 := hc m
    have h2 := hψ m
    have habs : |c m - ψ m| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    calc ‖h m‖ * |c m - ψ m| ≤ 1 * 1 :=
          mul_le_mul (hb m) habs (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  calc ∑ m ∈ S.filter (· ∈ D), ‖h m * (((c m - ψ m : ℝ)) : ℂ)‖
      ≤ ∑ _m ∈ S.filter (· ∈ D), (1:ℝ) := Finset.sum_le_sum hpt
    _ = ((S.filter (· ∈ D)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (D.card : ℝ) := by
        have hsub : S.filter (· ∈ D) ⊆ D := fun m hm =>
          (Finset.mem_filter.mp hm).2
        exact_mod_cast Finset.card_le_card hsub


/-- **The Riemann comparison** (Track R, B3-iv): a log-sampled harmonic
sum of a nonnegative Lipschitz function is at most twice its integral
plus a second-order Lipschitz tail — the discrete-to-continuous step
that hands the fibre mean square to the Plancherel harness's
`y`-integral. -/
theorem sum_log_div_le_two_mul_integral_add (a b : ℕ) (ha : 1 ≤ a)
    (hab : a ≤ b) (f : ℝ → ℝ) (hf0 : ∀ y, 0 ≤ f y) (hfc : Continuous f)
    (Λ : ℝ) (hΛ0 : 0 ≤ Λ) (hLip : ∀ y z, |f y - f z| ≤ Λ * |y - z|) :
    ∑ n ∈ Finset.Ioc a b, f (Real.log n)/n
      ≤ 2 * (∫ y in (Real.log a)..(Real.log (b+1)), f y) + 2*Λ/a := by
  classical
  -- per-piece bound
  have hpiece : ∀ n ∈ Finset.Ioc a b,
      f (Real.log n)/n
        ≤ 2 * (∫ y in (Real.log n)..(Real.log (n+1)), f y) + 2*Λ/(n:ℝ)^2 := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn1 : 1 ≤ n := by omega
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn1
    have hlogle : Real.log n ≤ Real.log (n+1) :=
      Real.log_le_log (by positivity) (by push_cast; linarith)
    set L : ℝ := Real.log (n+1) - Real.log n with hL_def
    have hL_eq : L = Real.log (1 + 1/n) := by
      rw [hL_def, ← Real.log_div (by positivity) (by positivity)]
      congr 1
      field_simp
    have hL_up : L ≤ 1/n := by
      rw [hL_eq]
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 1/n by positivity)
      linarith
    have hL_low : 1/(2*(n:ℝ)) ≤ L := by
      rw [hL_eq]
      have h1 := Real.one_sub_inv_le_log_of_pos
        (show (0:ℝ) < 1 + 1/n by positivity)
      have h2 : (1:ℝ) - (1 + 1/(n:ℝ))⁻¹ = 1/((n:ℝ)+1) := by
        field_simp
        ring
      have h3 : 1/(2*(n:ℝ)) ≤ 1/((n:ℝ)+1) := by
        refine one_div_le_one_div_of_le (by positivity) ?_
        have : (1:ℝ) ≤ n := by exact_mod_cast hn1
        linarith
      linarith [h1, h2 ▸ h1]
    -- pointwise: f(log n) − Λ/n ≤ f y on the piece
    have hpt : ∀ y ∈ Set.uIcc (Real.log n) (Real.log (n+1)),
        f (Real.log n) - Λ/n ≤ f y := by
      intro y hy
      rw [Set.uIcc_of_le hlogle] at hy
      have hdist : |Real.log n - y| ≤ 1/n := by
        rw [abs_of_nonpos (by linarith [hy.1])]
        have := hy.2
        have hLb : y - Real.log n ≤ L := by
          rw [hL_def]
          linarith [hy.2]
        linarith [hL_up]
      have := hLip (Real.log n) y
      have habs : f (Real.log n) - f y ≤ Λ * (1/n) := by
        calc f (Real.log n) - f y ≤ |f (Real.log n) - f y| := le_abs_self _
          _ ≤ Λ * |Real.log n - y| := this
          _ ≤ Λ * (1/n) := mul_le_mul_of_nonneg_left hdist hΛ0
      have hbridge : Λ * (1/(n:ℝ)) = Λ/(n:ℝ) := by ring
      linarith [hbridge]
    have hmono : (f (Real.log n) - Λ/n) * L
        ≤ ∫ y in (Real.log n)..(Real.log (n+1)), f y := by
      have h1 : ∫ y in (Real.log n)..(Real.log (n+1)), (f (Real.log n) - Λ/n)
          ≤ ∫ y in (Real.log n)..(Real.log (n+1)), f y := by
        refine intervalIntegral.integral_mono_on hlogle
          intervalIntegrable_const (hfc.intervalIntegrable _ _) ?_
        intro y hy
        exact hpt y (Set.mem_uIcc_of_le hy.1 hy.2)
      rw [intervalIntegral.integral_const, smul_eq_mul] at h1
      calc (f (Real.log n) - Λ/n) * L
          = (Real.log (n+1) - Real.log n) * (f (Real.log n) - Λ/n) := by
            rw [hL_def]; ring
        _ ≤ ∫ y in (Real.log n)..(Real.log (n+1)), f y := h1
    -- assemble per-piece
    have hint_nonneg : (0:ℝ) ≤ ∫ y in (Real.log n)..(Real.log (n+1)), f y :=
      intervalIntegral.integral_nonneg hlogle (fun y _ => hf0 y)
    have hf0n := hf0 (Real.log n)
    -- f(logn)/n ≤ 2 f(logn) L ≤ 2∫ + 2ΛL/n ≤ 2∫ + 2Λ/n²
    have hkey : f (Real.log n) * (1/(n:ℝ)) ≤ 2 * (f (Real.log n) * L) := by
      have hm := mul_le_mul_of_nonneg_left hL_low hf0n
      have hbridge : f (Real.log n) * (1/(n:ℝ))
          = 2 * (f (Real.log n) * (1/(2*(n:ℝ)))) := by ring
      linarith [hm, hbridge]
    have hkey2 : f (Real.log n) * L
        ≤ (∫ y in (Real.log n)..(Real.log (n+1)), f y) + (Λ/n) * L := by
      have hbridge : (f (Real.log n) - Λ/(n:ℝ)) * L
          = f (Real.log n) * L - (Λ/(n:ℝ)) * L := by ring
      linarith [hmono, hbridge]
    have hkey3 : (Λ/n) * L ≤ Λ/(n:ℝ)^2 := by
      have h1 : (Λ/n) * L ≤ (Λ/n) * (1/n) :=
        mul_le_mul_of_nonneg_left hL_up (by positivity)
      calc (Λ/n) * L ≤ (Λ/n) * (1/n) := h1
        _ = Λ/(n:ℝ)^2 := by ring
    calc f (Real.log n)/n = f (Real.log n) * (1/(n:ℝ)) := by ring
      _ ≤ 2 * (f (Real.log n) * L) := hkey
      _ ≤ 2 * ((∫ y in (Real.log n)..(Real.log (n+1)), f y) + (Λ/n) * L) := by
          linarith [hkey2]
      _ ≤ 2 * (∫ y in (Real.log n)..(Real.log (n+1)), f y) + 2*Λ/(n:ℝ)^2 := by
          have hb : 2*Λ/(n:ℝ)^2 = 2*(Λ/(n:ℝ)^2) := by ring
          linarith [hkey3, hb]
  -- sum the pieces
  refine le_trans (Finset.sum_le_sum hpiece) ?_
  rw [Finset.sum_add_distrib]
  -- (1) telescope the integrals
  have htele : ∑ n ∈ Finset.Ioc a b,
      (∫ y in (Real.log n)..(Real.log (n+1)), f y)
      = ∫ y in (Real.log ((a:ℝ)+1))..(Real.log ((b:ℝ)+1)), f y := by
    set d : ℕ → ℝ := fun k => Real.log ((a+1+k : ℕ) : ℝ) with hd_def
    have hreindex : ∑ n ∈ Finset.Ioc a b,
        (∫ y in (Real.log n)..(Real.log (n+1)), f y)
        = ∑ k ∈ Finset.range (b - a), (∫ y in (d k)..(d (k+1)), f y) := by
      refine Finset.sum_bij' (fun n _ => n - (a+1)) (fun k _ => a+1+k)
        ?_ ?_ ?_ ?_ ?_
      · intro n hn
        rw [Finset.mem_Ioc] at hn
        rw [Finset.mem_range]
        dsimp only
        omega
      · intro k hk
        rw [Finset.mem_range] at hk
        rw [Finset.mem_Ioc]
        dsimp only
        omega
      · intro n hn
        rw [Finset.mem_Ioc] at hn
        dsimp only
        omega
      · intro k _
        dsimp only
        omega
      · intro n hn
        rw [Finset.mem_Ioc] at hn
        dsimp only
        have e1 : d (n - (a+1)) = Real.log n := by
          rw [hd_def]
          dsimp only
          congr 1
          exact_mod_cast congrArg (Nat.cast : ℕ → ℝ)
            (by omega : a+1+(n-(a+1)) = n)
        have e2 : d (n - (a+1) + 1) = Real.log ((n:ℝ)+1) := by
          rw [hd_def]
          dsimp only
          have h5 : a+1+(n-(a+1)+1) = n+1 := by omega
          rw [h5]
          congr 1
          push_cast
          ring
        rw [e1, e2]
    rw [hreindex]
    have hd2 := intervalIntegral.sum_integral_adjacent_intervals
      (μ := MeasureTheory.volume) (a := d) (n := b - a)
      (fun k _ => (hfc.intervalIntegrable _ _))
    have e0 : d 0 = Real.log ((a:ℝ)+1) := by
      rw [hd_def]
      dsimp only
      congr 1
      push_cast
      ring
    have eN : d (b-a) = Real.log ((b:ℝ)+1) := by
      rw [hd_def]
      dsimp only
      have h5 : a+1+(b-a) = b+1 := by omega
      rw [h5]
      congr 1
      push_cast
      ring
    rw [e0, eN] at hd2
    exact hd2
  have hext : ∫ y in (Real.log ((a:ℝ)+1))..(Real.log ((b:ℝ)+1)), f y
      ≤ ∫ y in (Real.log a)..(Real.log ((b:ℝ)+1)), f y := by
    have ha0 : (0:ℝ) < a := by exact_mod_cast ha
    have hlog1 : Real.log a ≤ Real.log ((a:ℝ)+1) :=
      Real.log_le_log ha0 (by linarith)
    have hlog2 : Real.log ((a:ℝ)+1) ≤ Real.log ((b:ℝ)+1) := by
      refine Real.log_le_log (by positivity) ?_
      have : (a:ℝ) ≤ b := by exact_mod_cast hab
      linarith
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume)
      (a := Real.log a) (b := Real.log ((a:ℝ)+1)) (c := Real.log ((b:ℝ)+1))
      (hfc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _)
    have hfirst : (0:ℝ) ≤ ∫ y in (Real.log a)..(Real.log ((a:ℝ)+1)), f y :=
      intervalIntegral.integral_nonneg hlog1 (fun y _ => hf0 y)
    linarith [hsplit, hfirst]
  -- (2) the quadratic tail telescopes
  have htail : ∑ n ∈ Finset.Ioc a b, (1:ℝ)/(n:ℝ)^2 ≤ 1/a := by
    have hstep : ∀ b', a ≤ b' →
        ∑ n ∈ Finset.Ioc a b', (1:ℝ)/(n:ℝ)^2 ≤ 1/a - 1/b' := by
      intro b' hb'
      induction b' with
      | zero => omega
      | succ m ih =>
        rcases Nat.lt_or_ge a (m+1) with hlt | hge
        · have ham : a ≤ m := by omega
          have hm0 : (0:ℝ) < m := by
            have : 1 ≤ m := by omega
            exact_mod_cast this
          rw [Finset.sum_Ioc_succ_top (by omega : a ≤ m)]
          have hq : (1:ℝ)/((m+1:ℕ):ℝ)^2 ≤ 1/(m:ℝ) - 1/((m:ℝ)+1) := by
            push_cast
            rw [div_sub_div _ _ (by positivity) (by positivity)]
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            ring_nf
            nlinarith [hm0]
          have hih := ih ham
          push_cast at hq ⊢
          have hlast : (1:ℝ)/(m:ℝ) - 1/((m:ℝ)+1) + (1/a - 1/(m:ℝ))
              = 1/a - 1/((m:ℝ)+1) := by ring
          linarith [hq, hih, hlast]
        · have heq : a = m + 1 := by omega
          rw [heq]
          simp
    have hb0 : (0:ℝ) < b := by
      have : 1 ≤ b := by omega
      exact_mod_cast this
    have := hstep b hab
    have hbpos : (0:ℝ) ≤ 1/(b:ℝ) := by positivity
    linarith
  -- close
  have hsum2 : ∑ n ∈ Finset.Ioc a b, 2*Λ/(n:ℝ)^2 ≤ 2*Λ/a := by
    have hfac : ∀ n ∈ Finset.Ioc a b, 2*Λ/(n:ℝ)^2 = 2*Λ*((1:ℝ)/(n:ℝ)^2) := by
      intro n _
      ring
    rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum]
    have h2 : 2*Λ*((1:ℝ)/a) = 2*Λ/a := by ring
    calc 2*Λ * ∑ n ∈ Finset.Ioc a b, (1:ℝ)/(n:ℝ)^2
        ≤ 2*Λ*(1/a) := by
          refine mul_le_mul_of_nonneg_left htail (by linarith)
      _ = 2*Λ/a := h2
  have hsumint : ∑ n ∈ Finset.Ioc a b,
      2 * (∫ y in (Real.log n)..(Real.log (n+1)), f y)
      = 2 * ∫ y in (Real.log ((a:ℝ)+1))..(Real.log ((b:ℝ)+1)), f y := by
    rw [← Finset.mul_sum, htele]
  rw [hsumint]
  have hfin : 2 * (∫ y in (Real.log ((a:ℝ)+1))..(Real.log ((b:ℝ)+1)), f y)
      ≤ 2 * (∫ y in (Real.log a)..(Real.log ((b:ℝ)+1)), f y) := by
    linarith [hext]
  linarith [hfin, hsum2]


end MoltResearch
