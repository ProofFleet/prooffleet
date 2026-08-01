import MoltResearch.Discrepancy.TuranKubilius
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

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


/-- **The slice partition** (Track R, B2′): a range `(A, A+J·s]` is the
disjoint union of `J` consecutive slices of width `s`. Refines the B2
dyadic fibres into slices on which the relative window width `H/n`
varies by only the slice ratio — the alignment the fixed smooth window
of the Plancherel comparison needs. -/
theorem sum_range_sum_Ioc_slices {M : Type*} [AddCommMonoid M]
    (A s J : ℕ) (f : ℕ → M) :
    ∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ioc (A + j*s) (A + (j+1)*s), f n
      = ∑ n ∈ Finset.Ioc A (A + J*s), f n := by
  induction J with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : A ≤ A + K*s := by omega
    have h2 : A + K*s ≤ A + (K+1)*s := by
      have : K*s ≤ (K+1)*s := Nat.mul_le_mul_right s (by omega)
      omega
    exact Finset.sum_Ioc_consecutive f h1 h2


/-- **The floor-window count** (Track R, B3-iii-b prep): the number of
integers in a real window `(x, y]` is at most `y − x + 1` — the count
that turns collar widths into collar cardinalities in the
smooth-vs-trapezoid comparison. -/
theorem card_Ioc_floor_le (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    ((Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).card : ℝ) ≤ y - x + 1 := by
  rw [Nat.card_Ioc]
  have h1 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (le_trans hx hxy)
  have h2 : x - 1 < (⌊x⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one x
    linarith
  have h3 : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hxy
  have h4 : ((⌊y⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) = (⌊y⌋₊ : ℝ) - (⌊x⌋₊ : ℝ) :=
    Nat.cast_sub h3
  rw [h4]
  linarith


/-- **The per-slice mean square** (Track R, B4-scaffold): on a slice,
the sharp-window mean square is controlled by the smooth-window energy
integral plus the shift, collar, and Riemann costs. The smooth-window
data enters as hypotheses (`G`, the collar bound, the Lipschitz
constant); B3-iii-b discharges them with an explicit `ContDiffBump`
window, and the harness's `regime_split` then bounds the integral on
the frequency side. -/
theorem slice_window_mean_sq_le (h : ℕ → ℂ) (hb : ∀ m, ‖h m‖ ≤ 1)
    (A s H U : ℕ) (hA : 1 ≤ A) (hU : 0 < U) (hUH : U ≤ H)
    (G : ℝ → ℂ) (hGcont : Continuous G)
    (Dbound : ℝ) (hD0 : 0 ≤ Dbound)
    (hcollar : ∀ n ∈ Finset.Ioc A (A+s),
      ‖((1/(U:ℂ)) * ∑ u ∈ Finset.range U, ∑ m ∈ Finset.Ioc (n+u) (n+u+H), h m)
        - G (Real.log n)‖ ≤ Dbound)
    (Λ : ℝ) (hΛ0 : 0 ≤ Λ)
    (hLip : ∀ y z, |‖G y‖^2 - ‖G z‖^2| ≤ Λ * |y - z|) :
    ∑ n ∈ Finset.Ioc A (A+s), ‖∑ m ∈ Finset.Ioc n (n+H), h m‖^2/n
      ≤ 6 * (∫ y in (Real.log A)..(Real.log (((A+s : ℕ) : ℝ)+1)), ‖G y‖^2)
        + (3*(U:ℝ)^2 + 3*Dbound^2) * (∑ n ∈ Finset.Ioc A (A+s), (1:ℝ)/n)
        + 6*Λ/A := by
  classical
  have hper : ∀ n ∈ Finset.Ioc A (A+s),
      ‖∑ m ∈ Finset.Ioc n (n+H), h m‖^2/n
        ≤ (3*(U:ℝ)^2 + 3*Dbound^2)*(1/n) + 3*(‖G (Real.log n)‖^2/n) := by
    intro n hn
    have hmem := hn
    rw [Finset.mem_Ioc] at hmem
    have hn0 : (0:ℝ) < n := by
      have h1 : 1 ≤ n := by omega
      exact_mod_cast h1
    have h1 := norm_window_sub_shift_avg_le h hb n H U hU hUH
    have h2 := hcollar n hn
    have htri : ‖∑ m ∈ Finset.Ioc n (n+H), h m‖
        ≤ (U:ℝ) + Dbound + ‖G (Real.log n)‖ := by
      have e1 : ∑ m ∈ Finset.Ioc n (n+H), h m
          = ((∑ m ∈ Finset.Ioc n (n+H), h m)
              - (1/(U:ℂ)) * ∑ u ∈ Finset.range U,
                  ∑ m ∈ Finset.Ioc (n+u) (n+u+H), h m)
            + (((1/(U:ℂ)) * ∑ u ∈ Finset.range U,
                  ∑ m ∈ Finset.Ioc (n+u) (n+u+H), h m)
                - G (Real.log n))
            + G (Real.log n) := by ring
      calc ‖∑ m ∈ Finset.Ioc n (n+H), h m‖
          = ‖((∑ m ∈ Finset.Ioc n (n+H), h m)
              - (1/(U:ℂ)) * ∑ u ∈ Finset.range U,
                  ∑ m ∈ Finset.Ioc (n+u) (n+u+H), h m)
            + (((1/(U:ℂ)) * ∑ u ∈ Finset.range U,
                  ∑ m ∈ Finset.Ioc (n+u) (n+u+H), h m)
                - G (Real.log n))
            + G (Real.log n)‖ := by rw [← e1]
        _ ≤ ‖(∑ m ∈ Finset.Ioc n (n+H), h m)
              - (1/(U:ℂ)) * ∑ u ∈ Finset.range U,
                  ∑ m ∈ Finset.Ioc (n+u) (n+u+H), h m‖
            + ‖((1/(U:ℂ)) * ∑ u ∈ Finset.range U,
                  ∑ m ∈ Finset.Ioc (n+u) (n+u+H), h m)
                - G (Real.log n)‖
            + ‖G (Real.log n)‖ := norm_add₃_le
        _ ≤ (U:ℝ) + Dbound + ‖G (Real.log n)‖ := by
            refine add_le_add (add_le_add ?_ h2) le_rfl
            exact h1
    have hsq : ‖∑ m ∈ Finset.Ioc n (n+H), h m‖^2
        ≤ 3*(U:ℝ)^2 + 3*Dbound^2 + 3*‖G (Real.log n)‖^2 := by
      have hWnn : (0:ℝ) ≤ ‖∑ m ∈ Finset.Ioc n (n+H), h m‖ := norm_nonneg _
      have hGnn : (0:ℝ) ≤ ‖G (Real.log n)‖ := norm_nonneg _
      have hUnn : (0:ℝ) ≤ (U:ℝ) := Nat.cast_nonneg U
      nlinarith [htri, hWnn, hGnn, hUnn, hD0,
        sq_nonneg ((U:ℝ) - Dbound), sq_nonneg ((U:ℝ) - ‖G (Real.log n)‖),
        sq_nonneg (Dbound - ‖G (Real.log n)‖)]
    have hdiv : ‖∑ m ∈ Finset.Ioc n (n+H), h m‖^2/n
        ≤ (3*(U:ℝ)^2 + 3*Dbound^2 + 3*‖G (Real.log n)‖^2)/n := by
      gcongr
    have hbridge : (3*(U:ℝ)^2 + 3*Dbound^2 + 3*‖G (Real.log n)‖^2)/(n:ℝ)
        = (3*(U:ℝ)^2 + 3*Dbound^2)*(1/(n:ℝ)) + 3*(‖G (Real.log n)‖^2/(n:ℝ)) := by
      ring
    linarith [hdiv, hbridge.le, hbridge.ge]
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [Finset.sum_add_distrib]
  have hR := sum_log_div_le_two_mul_integral_add A (A+s) hA (by omega)
    (fun y => ‖G y‖^2) (fun y => by positivity) (hGcont.norm.pow 2)
    Λ hΛ0 hLip
  have hsum1 : ∑ n ∈ Finset.Ioc A (A+s), (3*(U:ℝ)^2 + 3*Dbound^2)*(1/(n:ℝ))
      = (3*(U:ℝ)^2 + 3*Dbound^2) * (∑ n ∈ Finset.Ioc A (A+s), (1:ℝ)/n) := by
    rw [Finset.mul_sum]
  have hsum2 : ∑ n ∈ Finset.Ioc A (A+s), 3*(‖G (Real.log n)‖^2/(n:ℝ))
      = 3 * ∑ n ∈ Finset.Ioc A (A+s), ‖G (Real.log n)‖^2/(n:ℝ) := by
    rw [Finset.mul_sum]
  rw [hsum1, hsum2]
  have h6 : 3 * ∑ n ∈ Finset.Ioc A (A+s), ‖G (Real.log n)‖^2/(n:ℝ)
      ≤ 6 * (∫ y in (Real.log A)..(Real.log (((A+s : ℕ) : ℝ)+1)), ‖G y‖^2)
        + 6*Λ/A := by
    have hb1 : 3 * ∑ n ∈ Finset.Ioc A (A+s), ‖G (Real.log n)‖^2/(n:ℝ)
        ≤ 3 * (2 * (∫ y in (Real.log A)..(Real.log (((A+s : ℕ) : ℝ)+1)),
            ‖G y‖^2) + 2*Λ/A) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact hR
    have hb2 : 3 * (2 * (∫ y in (Real.log A)..(Real.log (((A+s : ℕ) : ℝ)+1)),
        ‖G y‖^2) + 2*Λ/A)
        = 6 * (∫ y in (Real.log A)..(Real.log (((A+s : ℕ) : ℝ)+1)), ‖G y‖^2)
          + 6*Λ/A := by
      ring
    linarith [hb1, hb2.le, hb2.ge]
  linarith [h6]


/-- **The trapezoid plateau** (Track R, B3-iii-b-0): on `[n+U, n+H]`
every one of the `U` shifted windows contains `m`, so the B3-ii count
is exactly `U`. -/
theorem trapWeight_eq_of_plateau (n H U m : ℕ) (h1 : n+U ≤ m) (h2 : m ≤ n+H) :
    ((Finset.range U).filter (fun u => n+u < m ∧ m ≤ n+u+H)).card = U := by
  rw [Finset.filter_true_of_mem, Finset.card_range]
  intro u hu
  rw [Finset.mem_range] at hu
  omega

/-- Off the support on the left (`m ≤ n`): no shifted window contains
`m`; the count vanishes. -/
theorem trapWeight_eq_zero_left (n H U m : ℕ) (h : m ≤ n) :
    ((Finset.range U).filter (fun u => n+u < m ∧ m ≤ n+u+H)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u _
  omega

/-- Off the support on the right (`m ≥ n+U+H`): no shifted window
contains `m`; the count vanishes. -/
theorem trapWeight_eq_zero_right (n H U m : ℕ) (h : n+U+H ≤ m) :
    ((Finset.range U).filter (fun u => n+u < m ∧ m ≤ n+u+H)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u hu
  rw [Finset.mem_range] at hu
  omega


/-- **The collar identification** (Track R, B3-iii-b-1): the shift-averaged
window differs from any `[0,1]`-valued smooth window `ψ` — with plateau
`[P,Q]` inside the trapezoid's plateau and support `(R,S']` — by at most
the two collar counts `(P−n) + (max S' (n+U+H) − Q)`. The agreement
regions are: below `n` and above both supports (both weights vanish),
and `[P,Q]` (both weights are `1`); everything else is counted. -/
theorem norm_shift_avg_sub_smooth_le (h : ℕ → ℂ) (hb : ∀ m, ‖h m‖ ≤ 1)
    (n U H P Q R S' : ℕ) (hU : 0 < U)
    (hPU : n+U ≤ P) (hQH : Q ≤ n+H) (hPQ : P ≤ Q) (hR : n ≤ R) (hQS : Q ≤ S')
    (M : Finset ℕ) (hM : Finset.Ioc n (max S' (n+U+H)) ⊆ M)
    (ψ : ℕ → ℝ) (hψ01 : ∀ m, 0 ≤ ψ m ∧ ψ m ≤ 1)
    (hψ_plateau : ∀ m, P ≤ m → m ≤ Q → ψ m = 1)
    (hψ_supp : ∀ m, ψ m ≠ 0 → R < m ∧ m ≤ S') :
    ‖((1/(U:ℂ)) * ∑ u ∈ Finset.range U, ∑ m ∈ Finset.Ioc (n+u) (n+u+H), h m)
        - ∑ m ∈ M, h m * ((ψ m : ℝ) : ℂ)‖
      ≤ ((P - n : ℕ) : ℝ) + ((max S' (n+U+H) - Q : ℕ) : ℝ) := by
  classical
  have hU0 : ((U:ℂ)) ≠ 0 := by exact_mod_cast hU.ne'
  have hU0' : ((U:ℝ)) ≠ 0 := by exact_mod_cast hU.ne'
  set c : ℕ → ℝ := fun m =>
    (((Finset.range U).filter (fun u => n+u < m ∧ m ≤ n+u+H)).card : ℝ) / U
    with hc_def
  -- step 1: the average is the trapezoid-weighted M-sum
  have h1 : (1/(U:ℂ)) * ∑ u ∈ Finset.range U, ∑ m ∈ Finset.Ioc (n+u) (n+u+H), h m
      = ∑ m ∈ M, h m * ((c m : ℝ) : ℂ) := by
    rw [shift_avg_eq_sum_count]
    have hext : ∑ m ∈ Finset.Ioc n (n+U+H),
        (((Finset.range U).filter (fun u => n+u < m ∧ m ≤ n+u+H)).card : ℂ) * h m
        = ∑ m ∈ M,
            (((Finset.range U).filter (fun u => n+u < m ∧ m ≤ n+u+H)).card : ℂ) * h m := by
      refine Finset.sum_subset ?_ ?_
      · refine subset_trans ?_ hM
        intro m hm
        rw [Finset.mem_Ioc] at hm ⊢
        omega
      · intro m _ hm
        rw [Finset.mem_Ioc] at hm
        push_neg at hm
        by_cases hle : m ≤ n
        · rw [trapWeight_eq_zero_left n H U m hle]
          simp
        · have hge : n + U + H ≤ m := by omega
          rw [trapWeight_eq_zero_right n H U m hge]
          simp
    rw [hext, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hc_def]
    push_cast
    ring
  rw [h1]
  -- step 2: the difference is a weight-difference sum
  have h2 : (∑ m ∈ M, h m * ((c m : ℝ) : ℂ)) - ∑ m ∈ M, h m * ((ψ m : ℝ) : ℂ)
      = ∑ m ∈ M, h m * (((c m - ψ m : ℝ)) : ℂ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    push_cast
    ring
  rw [h2]
  -- step 3: the collar comparison
  set D : Finset ℕ := (Finset.Ioo n P) ∪ (Finset.Ioc Q (max S' (n+U+H)))
    with hD_def
  have hc01 : ∀ m, 0 ≤ c m ∧ c m ≤ 1 := by
    intro m
    rw [hc_def]
    constructor
    · positivity
    · rw [div_le_one (by exact_mod_cast hU)]
      exact_mod_cast le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_range U))
  have hagree : ∀ m ∈ M, m ∉ D → c m = ψ m := by
    intro m _ hmD
    rw [hD_def, Finset.mem_union, Finset.mem_Ioo, Finset.mem_Ioc] at hmD
    push_neg at hmD
    obtain ⟨hD1, hD2⟩ := hmD
    by_cases hle : m ≤ n
    · -- both vanish below n
      have hcz : c m = 0 := by
        rw [hc_def]
        dsimp only
        rw [trapWeight_eq_zero_left n H U m hle]
        simp
      have hψz : ψ m = 0 := by
        by_contra hne
        have := (hψ_supp m hne).1
        omega
      rw [hcz, hψz]
    · have hlt : n < m := by omega
      by_cases hPm : P ≤ m
      · by_cases hmQ : m ≤ Q
        · -- the common plateau
          have hcU : c m = 1 := by
            rw [hc_def]
            dsimp only
            rw [trapWeight_eq_of_plateau n H U m (by omega) (by omega)]
            field_simp
          rw [hcU, hψ_plateau m hPm hmQ]
        · -- m > Q and not in D₂ ⟹ m > max S' (n+U+H): both vanish
          have hmax : max S' (n+U+H) < m := hD2 (by omega)
          have hcz : c m = 0 := by
            rw [hc_def]
            dsimp only
            rw [trapWeight_eq_zero_right n H U m (by omega)]
            simp
          have hψz : ψ m = 0 := by
            by_contra hne
            have := (hψ_supp m hne).2
            omega
          rw [hcz, hψz]
      · -- n < m < P and not in D₁: contradiction with hD1
        exact absurd (hD1 hlt) hPm
  have hcard : ((D.card : ℕ) : ℝ)
      ≤ ((P - n : ℕ) : ℝ) + ((max S' (n+U+H) - Q : ℕ) : ℝ) := by
    have h3 : D.card ≤ (Finset.Ioo n P).card + (Finset.Ioc Q (max S' (n+U+H))).card := by
      rw [hD_def]
      exact Finset.card_union_le _ _
    have h4 : (Finset.Ioo n P).card = P - n - 1 := Nat.card_Ioo n P
    have h5 : (Finset.Ioc Q (max S' (n+U+H))).card = max S' (n+U+H) - Q :=
      Nat.card_Ioc Q _
    have h6 : D.card ≤ (P - n) + (max S' (n+U+H) - Q) := by omega
    exact_mod_cast h6
  exact le_trans (norm_sum_mul_sub_weights_le M D h hb c ψ hc01 hψ01 hagree) hcard


/-- **The collar bound from real cut-points** (Track R, B3-iii-b-2): the
b-1 collar identification with the plateau/support data given by real
cut-points `x₀ ≤ x₁ < x₂ ≤ x₃` (as produced by a bump window in log
coordinates, `xᵢ = n·e^{tᵢ}`), with the collar counted in real terms.
Floor/ceil packaging on top of `norm_shift_avg_sub_smooth_le`. -/
theorem norm_shift_avg_sub_smooth_le_of_cuts (h : ℕ → ℂ)
    (hb : ∀ m, ‖h m‖ ≤ 1) (n U H : ℕ) (hU : 0 < U)
    (x₀ x₁ x₂ x₃ : ℝ)
    (h₀₁ : x₀ ≤ x₁) (h₁₂ : x₁ + 1 ≤ x₂) (h₂₃ : x₂ ≤ x₃)
    (hU₁ : (n:ℝ) + U ≤ x₁) (h₂H : x₂ ≤ (n:ℝ) + H) (h₀n : (n:ℝ) ≤ x₀)
    (M : Finset ℕ) (hM : Finset.Ioc n (max ⌊x₃⌋₊ (n+U+H)) ⊆ M)
    (ψ : ℕ → ℝ) (hψ01 : ∀ m, 0 ≤ ψ m ∧ ψ m ≤ 1)
    (hψ_plateau : ∀ m : ℕ, x₁ ≤ (m:ℝ) → (m:ℝ) ≤ x₂ → ψ m = 1)
    (hψ_supp : ∀ m : ℕ, ψ m ≠ 0 → x₀ < (m:ℝ) ∧ (m:ℝ) ≤ x₃) :
    ‖((1/(U:ℂ)) * ∑ u ∈ Finset.range U, ∑ m ∈ Finset.Ioc (n+u) (n+u+H), h m)
        - ∑ m ∈ M, h m * ((ψ m : ℝ) : ℂ)‖
      ≤ (x₁ - n + 1) + (max x₃ ((n:ℝ)+U+H) - x₂ + 1) := by
  classical
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hx₀0 : (0:ℝ) ≤ x₀ := le_trans hn0 h₀n
  have hx₁0 : (0:ℝ) ≤ x₁ := le_trans hx₀0 h₀₁
  have hx₂0 : (0:ℝ) ≤ x₂ := by linarith
  set P : ℕ := ⌈x₁⌉₊ with hP_def
  set Q : ℕ := ⌊x₂⌋₊ with hQ_def
  set R : ℕ := ⌊x₀⌋₊ with hR_def
  set S' : ℕ := ⌊x₃⌋₊ with hS_def
  -- nat geometry from real geometry
  have hPU : n+U ≤ P := by
    have h1 : ((n+U : ℕ) : ℝ) ≤ x₁ := by push_cast; linarith
    have h2 := Nat.le_ceil x₁
    have : ((n+U : ℕ) : ℝ) ≤ (P:ℝ) := le_trans h1 h2
    exact_mod_cast this
  have hQH : Q ≤ n+H := by
    have h1 : x₂ ≤ ((n+H : ℕ) : ℝ) := by push_cast; linarith
    exact Nat.floor_le_of_le h1
  have hPQ : P ≤ Q := by
    have h1 : (P:ℝ) < x₁ + 1 := Nat.ceil_lt_add_one hx₁0
    have h2 : (P:ℝ) ≤ x₂ := by linarith
    exact_mod_cast Nat.le_floor h2
  have hRn : n ≤ R := Nat.le_floor h₀n
  have hQS : Q ≤ S' := Nat.floor_le_floor h₂₃
  -- the ψ-facts in nat form
  have hψ_plateau' : ∀ m, P ≤ m → m ≤ Q → ψ m = 1 := by
    intro m h1 h2
    refine hψ_plateau m ?_ ?_
    · have := Nat.ceil_le.mp h1
      exact this
    · have h3 : (m:ℝ) ≤ (Q:ℝ) := by exact_mod_cast h2
      have h4 : (Q:ℝ) ≤ x₂ := Nat.floor_le hx₂0
      linarith
  have hψ_supp' : ∀ m, ψ m ≠ 0 → R < m ∧ m ≤ S' := by
    intro m hne
    obtain ⟨h1, h2⟩ := hψ_supp m hne
    constructor
    · have h3 : (R:ℝ) ≤ x₀ := Nat.floor_le hx₀0
      have h4 : (R:ℝ) < (m:ℝ) := by linarith
      exact_mod_cast h4
    · exact Nat.le_floor h2
  -- apply b-1
  have hmain := norm_shift_avg_sub_smooth_le h hb n U H P Q R S' hU
    hPU hQH hPQ hRn hQS M hM ψ hψ01 hψ_plateau' hψ_supp'
  refine le_trans hmain ?_
  -- convert the nat collar counts to real
  have hc1 : ((P - n : ℕ) : ℝ) ≤ x₁ - n + 1 := by
    have h1 : (P:ℝ) < x₁ + 1 := Nat.ceil_lt_add_one hx₁0
    have h2 : n ≤ P := by omega
    have h3 : ((P - n : ℕ) : ℝ) = (P:ℝ) - n := Nat.cast_sub h2
    linarith [h3.le, h3.ge]
  have hc2 : ((max S' (n+U+H) - Q : ℕ) : ℝ)
      ≤ max x₃ ((n:ℝ)+U+H) - x₂ + 1 := by
    have hQmax : Q ≤ max S' (n+U+H) := le_trans hQS (le_max_left _ _)
    have h3 : ((max S' (n+U+H) - Q : ℕ) : ℝ)
        = ((max S' (n+U+H) : ℕ) : ℝ) - (Q:ℝ) := Nat.cast_sub hQmax
    have h4 : ((max S' (n+U+H) : ℕ) : ℝ)
        = max ((S' : ℕ) : ℝ) (((n+U+H : ℕ) : ℝ)) := Nat.cast_max _ _
    have h5 : ((S' : ℕ) : ℝ) ≤ x₃ := Nat.floor_le (by linarith)
    have h6 : (((n+U+H : ℕ)) : ℝ) ≤ ((n:ℝ)+U+H) := by
      push_cast
      linarith
    have h7 : max ((S' : ℕ) : ℝ) (((n+U+H : ℕ)) : ℝ)
        ≤ max x₃ ((n:ℝ)+U+H) := max_le_max h5 h6
    have h8 : x₂ - 1 < (Q:ℝ) := by
      have := Nat.lt_floor_add_one x₂
      linarith
    linarith [h3.le, h3.ge, h4.le, h4.ge]
  linarith [hc1, hc2]


open scoped ContDiff in
/-- **The bump window** (Track R, B3-iii-b-3): for any admissible edge
data `t₀ < t₁ < t₂ < t₃` with `T·t₃ ≤ 2`, there is a smooth `[0,1]`
window equal to `1` on `[−T t₂, −T t₁]`, supported in
`(−T t₃, −T t₀)` — in particular within `[−2, 2]`, the harness's
support class. `ContDiffBump` centred at the plateau midpoint. -/
theorem exists_bump_window (T t₀ t₁ t₂ t₃ : ℝ) (hT : 0 < T) (h0 : 0 < t₀)
    (h01 : t₀ < t₁) (h12 : t₁ < t₂) (h23 : t₂ < t₃) (h3 : T * t₃ ≤ 2) :
    ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ (∀ u, 0 ≤ η u ∧ η u ≤ 1) ∧
      (∀ u, -(T*t₂) ≤ u → u ≤ -(T*t₁) → η u = 1) ∧
      (∀ u, η u ≠ 0 → -(T*t₃) < u ∧ u < -(T*t₀)) ∧
      (∀ u, η u ≠ 0 → |u| ≤ 2) := by
  classical
  set c : ℝ := -(T*(t₁+t₂)/2) with hc_def
  set rIn : ℝ := T*(t₂-t₁)/2 with hrIn_def
  set rOut : ℝ := rIn + T*(min (t₁-t₀) (t₃-t₂)) with hrOut_def
  have hrIn_pos : 0 < rIn := by
    rw [hrIn_def]
    nlinarith
  have hmin_pos : 0 < min (t₁-t₀) (t₃-t₂) := by
    rw [lt_min_iff]
    constructor <;> linarith
  have hrlt : rIn < rOut := by
    rw [hrOut_def]
    nlinarith
  set f : ContDiffBump c := ⟨rIn, rOut, hrIn_pos, hrlt⟩ with hf_def
  refine ⟨fun u => f u, f.contDiff, fun u => ⟨f.nonneg, f.le_one⟩, ?_, ?_, ?_⟩
  · -- the plateau
    intro u h1 h2
    refine f.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, Real.dist_eq]
    show |u - c| ≤ rIn
    rw [abs_le]
    have hcv : c = -(T*(t₁+t₂)/2) := hc_def
    have hrv : rIn = T*(t₂-t₁)/2 := hrIn_def
    constructor <;> nlinarith [hcv, hrv]
  · -- the support
    intro u hne
    have hmem : u ∈ Function.support (fun u => f u) := hne
    rw [f.support_eq, Metric.mem_ball, Real.dist_eq] at hmem
    have hmem' : |u - c| < rOut := hmem
    rw [abs_lt] at hmem'
    have hmin1 : min (t₁-t₀) (t₃-t₂) ≤ t₁-t₀ := min_le_left _ _
    have hmin2 : min (t₁-t₀) (t₃-t₂) ≤ t₃-t₂ := min_le_right _ _
    have hcv : c = -(T*(t₁+t₂)/2) := hc_def
    have hrv : rOut = T*(t₂-t₁)/2 + T*(min (t₁-t₀) (t₃-t₂)) := by
      rw [hrOut_def, hrIn_def]
    constructor
    · nlinarith [hmem'.1, hcv, hrv]
    · nlinarith [hmem'.2, hcv, hrv]
  · -- the support is within [−2, 2]
    intro u hne
    have hmem : u ∈ Function.support (fun u => f u) := hne
    rw [f.support_eq, Metric.mem_ball, Real.dist_eq] at hmem
    have hmem' : |u - c| < rOut := hmem
    rw [abs_lt] at hmem'
    have hmin1 : min (t₁-t₀) (t₃-t₂) ≤ t₁-t₀ := min_le_left _ _
    have hmin2 : min (t₁-t₀) (t₃-t₂) ≤ t₃-t₂ := min_le_right _ _
    have hcv : c = -(T*(t₁+t₂)/2) := hc_def
    have hrv : rOut = T*(t₂-t₁)/2 + T*(min (t₁-t₀) (t₃-t₂)) := by
      rw [hrOut_def, hrIn_def]
    rw [abs_le]
    constructor
    · nlinarith [hmem'.1, hcv, hrv]
    · nlinarith [hmem'.2, hcv, hrv, mul_pos hT h0]


/-- **The slice edge geometry** (Track R, W1a): the four log edge
offsets of the slice bump window are positive, strictly ordered, and
`T`-scale admissible (`T·t₃ ≤ 2` at `T := A/H`) under the slice
parameter conditions `s ≤ A`, `2U ≤ H`, `(U+1)(A+s) ≤ AH`. These are
exactly `exists_bump_window`'s hypotheses. -/
theorem slice_edge_geometry (A s U H : ℕ) (hA : 1 ≤ A) (hs : 1 ≤ s)
    (hsA : s ≤ A) (hU : 0 < U) (hUH : 2*U ≤ H)
    (hplat : ((U:ℝ)+1)*((A:ℝ)+s) ≤ (A:ℝ)*H) :
    0 < Real.log (1 + (U:ℝ)/(4*((A:ℝ)+s)))
    ∧ Real.log (1 + (U:ℝ)/(4*((A:ℝ)+s))) < Real.log (1 + (U:ℝ)/A)
    ∧ Real.log (1 + (U:ℝ)/A) < Real.log (1 + (H:ℝ)/((A:ℝ)+s))
    ∧ Real.log (1 + (H:ℝ)/((A:ℝ)+s)) < Real.log (1 + ((H:ℝ)+2*U)/A)
    ∧ ((A:ℝ)/H) * Real.log (1 + ((H:ℝ)+2*U)/A) ≤ 2 := by
  have hA0 : (0:ℝ) < A := by exact_mod_cast hA
  have hs0 : (0:ℝ) < s := by exact_mod_cast hs
  have hU0 : (0:ℝ) < U := by exact_mod_cast hU
  have hH0 : (0:ℝ) < H := by
    have : 0 < H := by omega
    exact_mod_cast this
  have hAs0 : (0:ℝ) < (A:ℝ)+s := by linarith
  have hsA' : (s:ℝ) ≤ A := by exact_mod_cast hsA
  have hUH' : 2*(U:ℝ) ≤ H := by exact_mod_cast hUH
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine Real.log_pos ?_
    have : (0:ℝ) < (U:ℝ)/(4*((A:ℝ)+s)) := by positivity
    linarith
  · refine Real.log_lt_log (by positivity) ?_
    have h1 : (U:ℝ)/(4*((A:ℝ)+s)) < (U:ℝ)/A := by
      refine div_lt_div_of_pos_left hU0 hA0 ?_
      linarith
    linarith
  · refine Real.log_lt_log (by positivity) ?_
    have h1 : (U:ℝ)/A < (H:ℝ)/((A:ℝ)+s) := by
      rw [div_lt_div_iff₀ hA0 hAs0]
      nlinarith
    linarith
  · refine Real.log_lt_log (by positivity) ?_
    have h1 : (H:ℝ)/((A:ℝ)+s) < ((H:ℝ)+2*U)/A := by
      rw [div_lt_div_iff₀ hAs0 hA0]
      nlinarith
    linarith
  · have hlog : Real.log (1 + ((H:ℝ)+2*U)/A) ≤ ((H:ℝ)+2*U)/A := by
      have := Real.log_le_sub_one_of_pos
        (show (0:ℝ) < 1 + ((H:ℝ)+2*U)/A by positivity)
      linarith
    have h2 : ((A:ℝ)/H) * (((H:ℝ)+2*U)/A) = 1 + 2*(U:ℝ)/H := by
      field_simp
    have h3 : 2*(U:ℝ)/H ≤ 1 := by
      rw [div_le_one hH0]
      linarith
    calc ((A:ℝ)/H) * Real.log (1 + ((H:ℝ)+2*U)/A)
        ≤ ((A:ℝ)/H) * (((H:ℝ)+2*U)/A) := by
          refine mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 1 + 2*(U:ℝ)/H := h2
      _ ≤ 2 := by linarith


set_option maxHeartbeats 1600000 in
/-- **The slice cut points** (Track R, W1b): for `n` in the slice
`(A, A+s]`, the four window edges `xᵢ = n(1+rᵢ)` (closed forms of
`n·e^{tᵢ}` via `exp_log`) satisfy the b-2 geometry, and the collar
count is at most `6U + Hs/A + 2`. Pure field arithmetic. -/
theorem slice_cut_points (A s U H n : ℕ) (hA : 1 ≤ A) (hs : 1 ≤ s)
    (hsA : s ≤ A) (hU : 0 < U) (hUH : 2*U ≤ H)
    (hplat : ((U:ℝ)+1)*((A:ℝ)+s) ≤ (A:ℝ)*H)
    (hn1 : A < n) (hn2 : n ≤ A+s) :
    ((n:ℝ) ≤ (n:ℝ)*(1+(U:ℝ)/(4*((A:ℝ)+s))))
    ∧ ((n:ℝ)*(1+(U:ℝ)/(4*((A:ℝ)+s))) ≤ (n:ℝ)*(1+(U:ℝ)/A))
    ∧ ((n:ℝ)*(1+(U:ℝ)/A) + 1 ≤ (n:ℝ)*(1+(H:ℝ)/((A:ℝ)+s)))
    ∧ ((n:ℝ)*(1+(H:ℝ)/((A:ℝ)+s)) ≤ (n:ℝ)*(1+((H:ℝ)+2*U)/A))
    ∧ ((n:ℝ) + U ≤ (n:ℝ)*(1+(U:ℝ)/A))
    ∧ ((n:ℝ)*(1+(H:ℝ)/((A:ℝ)+s)) ≤ (n:ℝ) + H)
    ∧ ((n:ℝ)*(1+(U:ℝ)/A) - n + 1)
        + (max ((n:ℝ)*(1+((H:ℝ)+2*U)/A)) ((n:ℝ)+U+H)
            - (n:ℝ)*(1+(H:ℝ)/((A:ℝ)+s)) + 1)
      ≤ 6*(U:ℝ) + (H:ℝ)*s/A + 2 := by
  have hA0 : (0:ℝ) < A := by exact_mod_cast hA
  have hs0 : (0:ℝ) < s := by exact_mod_cast hs
  have hU0 : (0:ℝ) < U := by exact_mod_cast hU
  have hH0 : (0:ℝ) < H := by
    have h1 : 0 < H := by omega
    exact_mod_cast h1
  have hAs0 : (0:ℝ) < (A:ℝ)+s := by linarith
  have hsA' : (s:ℝ) ≤ A := by exact_mod_cast hsA
  have hUH' : 2*(U:ℝ) ≤ H := by exact_mod_cast hUH
  have hn1' : (A:ℝ) < n := by exact_mod_cast hn1
  have hn2' : (n:ℝ) ≤ (A:ℝ)+s := by exact_mod_cast hn2
  have hn0 : (0:ℝ) < n := by linarith
  have hnA : (A:ℝ) ≤ n := hn1'.le
  -- key div-facts
  have hr1 : (U:ℝ) ≤ (n:ℝ)*((U:ℝ)/A) := by
    rw [mul_div_assoc']
    rw [le_div_iff₀ hA0]
    nlinarith
  have hr2 : (n:ℝ)*((H:ℝ)/((A:ℝ)+s)) ≤ H := by
    rw [mul_div_assoc']
    rw [div_le_iff₀ hAs0]
    nlinarith
  have hmax : (n:ℝ)+U+H ≤ (n:ℝ)*(1+((H:ℝ)+2*U)/A) := by
    have h1 : (H:ℝ)+2*U ≤ (n:ℝ)*(((H:ℝ)+2*U)/A) := by
      rw [mul_div_assoc']
      rw [le_div_iff₀ hA0]
      nlinarith
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [mul_pos hn0 (div_pos hU0 (by linarith : (0:ℝ) < 4*((A:ℝ)+s)))]
  · have h1 : (U:ℝ)/(4*((A:ℝ)+s)) ≤ (U:ℝ)/A := by
      refine div_le_div_of_nonneg_left hU0.le hA0 ?_
      linarith
    have h2 : (1:ℝ)+(U:ℝ)/(4*((A:ℝ)+s)) ≤ 1+(U:ℝ)/A := by linarith
    exact mul_le_mul_of_nonneg_left h2 hn0.le
  · -- plateau width ≥ 1
    have h1 : (A:ℝ)*((H:ℝ)/((A:ℝ)+s) - (U:ℝ)/A) ≥ 1 := by
      have h2 : (A:ℝ)*((H:ℝ)/((A:ℝ)+s)) = (A:ℝ)*H/((A:ℝ)+s) := by ring
      have h3 : (A:ℝ)*((U:ℝ)/A) = U := by field_simp
      have h4 : ((U:ℝ)+1) ≤ (A:ℝ)*H/((A:ℝ)+s) := by
        rw [le_div_iff₀ hAs0]
        linarith
      nlinarith [h2, h3, h4]
    have h5 : (n:ℝ)*((H:ℝ)/((A:ℝ)+s) - (U:ℝ)/A)
        ≥ (A:ℝ)*((H:ℝ)/((A:ℝ)+s) - (U:ℝ)/A) := by
      refine mul_le_mul_of_nonneg_right hnA ?_
      nlinarith [h1]
    nlinarith [h1, h5]
  · have h1 : (H:ℝ)/((A:ℝ)+s) ≤ ((H:ℝ)+2*U)/A := by
      rw [div_le_div_iff₀ hAs0 hA0]
      nlinarith
    have h2 : (1:ℝ)+(H:ℝ)/((A:ℝ)+s) ≤ 1+((H:ℝ)+2*U)/A := by linarith
    exact mul_le_mul_of_nonneg_left h2 hn0.le
  · nlinarith [hr1]
  · nlinarith [hr2]
  · rw [max_eq_left hmax]
    -- x₁ − n ≤ 2U and x₃ − x₂ ≤ Hs/A + 4U
    have hc1 : (n:ℝ)*((U:ℝ)/A) ≤ 2*U := by
      have hn2A : (n:ℝ) ≤ 2*A := by linarith
      calc (n:ℝ)*((U:ℝ)/A) ≤ 2*(A:ℝ)*((U:ℝ)/A) :=
            mul_le_mul_of_nonneg_right hn2A (by positivity)
        _ = 2*U := by field_simp
    have hc2 : (n:ℝ)*(((H:ℝ)+2*U)/A) - (n:ℝ)*((H:ℝ)/((A:ℝ)+s))
        ≤ (H:ℝ)*s/A + 4*U := by
      have he : (n:ℝ)*(((H:ℝ)+2*U)/A) - (n:ℝ)*((H:ℝ)/((A:ℝ)+s))
          = (n:ℝ)*(((H:ℝ)*s + 2*(U:ℝ)*((A:ℝ)+s))/((A:ℝ)*((A:ℝ)+s))) := by
        field_simp
        ring
      have hb : (n:ℝ)*(((H:ℝ)*s + 2*(U:ℝ)*((A:ℝ)+s))/((A:ℝ)*((A:ℝ)+s)))
          ≤ ((A:ℝ)+s)*(((H:ℝ)*s + 2*(U:ℝ)*((A:ℝ)+s))/((A:ℝ)*((A:ℝ)+s))) := by
        refine mul_le_mul_of_nonneg_right hn2' ?_
        positivity
      have hcol : ((A:ℝ)+s)*(((H:ℝ)*s + 2*(U:ℝ)*((A:ℝ)+s))/((A:ℝ)*((A:ℝ)+s)))
          = (H:ℝ)*s/A + 2*(U:ℝ)*((A:ℝ)+s)/A := by
        field_simp
      have hfin : 2*(U:ℝ)*((A:ℝ)+s)/A ≤ 4*U := by
        rw [div_le_iff₀ hA0]
        nlinarith
      calc (n:ℝ)*(((H:ℝ)+2*U)/A) - (n:ℝ)*((H:ℝ)/((A:ℝ)+s))
          = (n:ℝ)*(((H:ℝ)*s + 2*(U:ℝ)*((A:ℝ)+s))/((A:ℝ)*((A:ℝ)+s))) := he
        _ ≤ ((A:ℝ)+s)*(((H:ℝ)*s + 2*(U:ℝ)*((A:ℝ)+s))/((A:ℝ)*((A:ℝ)+s))) := hb
        _ = (H:ℝ)*s/A + 2*(U:ℝ)*((A:ℝ)+s)/A := hcol
        _ ≤ (H:ℝ)*s/A + 4*U := by linarith [hfin]
    have hb1 : (n:ℝ)*(1+(U:ℝ)/A) - n = (n:ℝ)*((U:ℝ)/A) := by ring
    have hb2 : (n:ℝ)*(1+((H:ℝ)+2*U)/A) - (n:ℝ)*(1+(H:ℝ)/((A:ℝ)+s))
        = (n:ℝ)*(((H:ℝ)+2*U)/A) - (n:ℝ)*((H:ℝ)/((A:ℝ)+s)) := by ring
    linarith [hc1, hc2, hb1, hb2]


/-- **The window transfer** (Track R, W1c): the bump window evaluated at
the log-ratio phase `T(log n − log m)` has plateau and support given by
the closed-form cut points `n(1+rᵢ)` — `log_mul` and `exp_log`
monotonicity; the `m = 0` degenerate case dies on the support's
negativity since `log n > 0`. -/
theorem psi_transfer (A n : ℕ) (hA : 1 ≤ A) (hn1 : A < n)
    (T : ℝ) (hT : 0 < T) (r₀ r₁ r₂ r₃ : ℝ)
    (hr₀ : 0 < r₀) (hr01 : r₀ ≤ r₁) (hr12 : r₁ ≤ r₂) (hr23 : r₂ ≤ r₃)
    (η : ℝ → ℝ)
    (hηplat : ∀ u, -(T*Real.log (1+r₂)) ≤ u → u ≤ -(T*Real.log (1+r₁)) → η u = 1)
    (hηsupp : ∀ u, η u ≠ 0 → -(T*Real.log (1+r₃)) < u ∧ u < -(T*Real.log (1+r₀))) :
    (∀ m : ℕ, (n:ℝ)*(1+r₁) ≤ (m:ℝ) → (m:ℝ) ≤ (n:ℝ)*(1+r₂)
      → η (T*(Real.log n - Real.log m)) = 1)
    ∧ (∀ m : ℕ, η (T*(Real.log n - Real.log m)) ≠ 0
      → (n:ℝ)*(1+r₀) < (m:ℝ) ∧ (m:ℝ) ≤ (n:ℝ)*(1+r₃)) := by
  have hn2 : 2 ≤ n := by omega
  have hn0 : (0:ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hlogn : 0 < Real.log n := by
    refine Real.log_pos ?_
    exact_mod_cast hn2
  have h1r₀ : (0:ℝ) < 1 + r₀ := by linarith
  have h1r₁ : (0:ℝ) < 1 + r₁ := by linarith
  have h1r₂ : (0:ℝ) < 1 + r₂ := by linarith
  have h1r₃ : (0:ℝ) < 1 + r₃ := by linarith
  constructor
  · -- the plateau
    intro m hm1 hm2
    have hm0 : (0:ℝ) < m := by nlinarith
    have hlog1 : Real.log ((n:ℝ)*(1+r₁)) ≤ Real.log m :=
      Real.log_le_log (by positivity) hm1
    have hlog2 : Real.log m ≤ Real.log ((n:ℝ)*(1+r₂)) :=
      Real.log_le_log hm0 hm2
    rw [Real.log_mul hn0.ne' h1r₁.ne'] at hlog1
    rw [Real.log_mul hn0.ne' h1r₂.ne'] at hlog2
    refine hηplat _ ?_ ?_
    · nlinarith [hlog2]
    · nlinarith [hlog1]
  · -- the support
    intro m hne
    obtain ⟨h1, h2⟩ := hηsupp _ hne
    have hlog₀ : (0:ℝ) < Real.log (1+r₀) := Real.log_pos (by linarith)
    -- m must be positive
    have hm0 : (0:ℝ) < m := by
      by_contra hm
      push_neg at hm
      have hmz : (m:ℝ) = 0 := le_antisymm hm (Nat.cast_nonneg m)
      rw [hmz, Real.log_zero, sub_zero] at h2
      nlinarith [h2]
    have hm1 : 1 ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
      intro hz
      rw [hz] at hm0
      norm_num at hm0)
    -- extract the log-inequalities
    have hL1 : Real.log n + Real.log (1+r₀) < Real.log m := by
      have := lt_of_mul_lt_mul_left
        (by linarith [h2] : T*(Real.log n - Real.log m) < T*(-(Real.log (1+r₀))))
        hT.le
      linarith
    have hL2 : Real.log m < Real.log n + Real.log (1+r₃) := by
      have := lt_of_mul_lt_mul_left
        (by linarith [h1] : T*(-(Real.log (1+r₃))) < T*(Real.log n - Real.log m))
        hT.le
      linarith
    constructor
    · have h3 : Real.log ((n:ℝ)*(1+r₀)) < Real.log m := by
        rw [Real.log_mul hn0.ne' h1r₀.ne']
        exact hL1
      have h4 := Real.exp_lt_exp.mpr h3
      rw [Real.exp_log (by positivity), Real.exp_log hm0] at h4
      exact h4
    · have h3 : Real.log m < Real.log ((n:ℝ)*(1+r₃)) := by
        rw [Real.log_mul hn0.ne' h1r₃.ne']
        exact hL2
      have h4 := Real.exp_lt_exp.mpr h3
      rw [Real.exp_log hm0, Real.exp_log (by positivity)] at h4
      exact h4.le


open scoped ContDiff in
/-- **The slice window** (Track R, W1d): for every admissible slice
there is one smooth `[0,1]` window `η` (support in `[−2,2]`) whose
log-ratio evaluations track all the slice's shift-averaged windows to
within the collar budget `6U + Hs/A + 2` — the composition
W1a → bump → W1c → W1b → b-2, with the slice-uniform index range
`(A, A+s+2H+4U]`. This is the `hcollar` provider for the B4 scaffold. -/
theorem exists_slice_window (h : ℕ → ℂ) (hb : ∀ m, ‖h m‖ ≤ 1)
    (A s U H : ℕ) (hA : 1 ≤ A) (hs : 1 ≤ s) (hsA : s ≤ A) (hU : 0 < U)
    (hUH : 2*U ≤ H) (hplat : ((U:ℝ)+1)*((A:ℝ)+s) ≤ (A:ℝ)*H) :
    ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ (∀ u, 0 ≤ η u ∧ η u ≤ 1)
      ∧ (∀ u, η u ≠ 0 → |u| ≤ 2)
      ∧ ∀ n ∈ Finset.Ioc A (A+s),
          ‖((1/(U:ℂ)) * ∑ u ∈ Finset.range U,
                ∑ m ∈ Finset.Ioc (n+u) (n+u+H), h m)
              - ∑ m ∈ Finset.Ioc A (A+s+2*H+4*U),
                  h m * ((η (((A:ℝ)/H)*(Real.log n - Real.log m)) : ℝ) : ℂ)‖
            ≤ 6*(U:ℝ) + (H:ℝ)*s/A + 2 := by
  classical
  have hA0 : (0:ℝ) < A := by exact_mod_cast hA
  have hH0 : (0:ℝ) < H := by
    have h1 : 0 < H := by omega
    exact_mod_cast h1
  have hAs0 : (0:ℝ) < (A:ℝ)+s := by
    have : (0:ℝ) < s := by exact_mod_cast hs
    linarith
  have hT : (0:ℝ) < (A:ℝ)/H := by positivity
  obtain ⟨hg0, hg1, hg2, hg3, hg4⟩ :=
    slice_edge_geometry A s U H hA hs hsA hU hUH hplat
  obtain ⟨η, hηs, hη01, hηplat, hηsupp, hη2⟩ :=
    exists_bump_window ((A:ℝ)/H)
      (Real.log (1 + (U:ℝ)/(4*((A:ℝ)+s)))) (Real.log (1 + (U:ℝ)/A))
      (Real.log (1 + (H:ℝ)/((A:ℝ)+s))) (Real.log (1 + ((H:ℝ)+2*U)/A))
      hT hg0 hg1 hg2 hg3 hg4
  refine ⟨η, hηs, hη01, hη2, ?_⟩
  intro n hn
  rw [Finset.mem_Ioc] at hn
  obtain ⟨hn1, hn2⟩ := hn
  -- the per-n transfer
  have hr₀0 : (0:ℝ) < (U:ℝ)/(4*((A:ℝ)+s)) := by positivity
  have hr01 : (U:ℝ)/(4*((A:ℝ)+s)) ≤ (U:ℝ)/A := by
    refine div_le_div_of_nonneg_left (by positivity) hA0 ?_
    linarith
  have hr12 : (U:ℝ)/A ≤ (H:ℝ)/((A:ℝ)+s) := by
    rw [div_le_div_iff₀ hA0 hAs0]
    have hU0 : (0:ℝ) < U := by exact_mod_cast hU
    have hs0 : (0:ℝ) < s := by exact_mod_cast hs
    nlinarith
  have hr23 : (H:ℝ)/((A:ℝ)+s) ≤ ((H:ℝ)+2*U)/A := by
    rw [div_le_div_iff₀ hAs0 hA0]
    have hU0 : (0:ℝ) < U := by exact_mod_cast hU
    have hsA' : (s:ℝ) ≤ A := by exact_mod_cast hsA
    nlinarith
  obtain ⟨hψplat, hψsupp⟩ := psi_transfer A n hA hn1 ((A:ℝ)/H) hT
    ((U:ℝ)/(4*((A:ℝ)+s))) ((U:ℝ)/A) ((H:ℝ)/((A:ℝ)+s)) (((H:ℝ)+2*U)/A)
    hr₀0 hr01 hr12 hr23 η hηplat hηsupp
  obtain ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6⟩ :=
    slice_cut_points A s U H n hA hs hsA hU hUH hplat hn1 hn2
  -- the M-inclusion
  have hMsub : Finset.Ioc n (max ⌊(n:ℝ)*(1+((H:ℝ)+2*U)/A)⌋₊ (n+U+H))
      ⊆ Finset.Ioc A (A+s+2*H+4*U) := by
    intro k hk
    rw [Finset.mem_Ioc] at hk ⊢
    have hfl : ⌊(n:ℝ)*(1+((H:ℝ)+2*U)/A)⌋₊ ≤ A+s+2*H+4*U := by
      refine Nat.floor_le_of_le ?_
      have hn2' : (n:ℝ) ≤ (A:ℝ)+s := by exact_mod_cast hn2
      have hAs2A : (A:ℝ)+s ≤ 2*A := by
        have : (s:ℝ) ≤ A := by exact_mod_cast hsA
        linarith
      have hx : (n:ℝ)*(1+((H:ℝ)+2*U)/A) ≤ ((A:ℝ)+s)*(1+((H:ℝ)+2*U)/A) := by
        refine mul_le_mul_of_nonneg_right hn2' ?_
        positivity
      have hy : ((A:ℝ)+s)*(((H:ℝ)+2*U)/A) ≤ 2*((H:ℝ)+2*U) := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ hA0]
        nlinarith
      push_cast
      nlinarith [hx, hy]
    constructor
    · omega
    · have := hk.2
      have h2 : max ⌊(n:ℝ)*(1+((H:ℝ)+2*U)/A)⌋₊ (n+U+H) ≤ A+s+2*H+4*U := by
        rw [max_le_iff]
        constructor
        · exact hfl
        · omega
      omega
  -- b-2 at the closed-form cut points
  have hmain := norm_shift_avg_sub_smooth_le_of_cuts h hb n U H hU
    ((n:ℝ)*(1+(U:ℝ)/(4*((A:ℝ)+s)))) ((n:ℝ)*(1+(U:ℝ)/A))
    ((n:ℝ)*(1+(H:ℝ)/((A:ℝ)+s))) ((n:ℝ)*(1+((H:ℝ)+2*U)/A))
    hc1 hc2 hc3 hc4 hc5 hc0
    (Finset.Ioc A (A+s+2*H+4*U)) hMsub
    (fun m => η (((A:ℝ)/H)*(Real.log n - Real.log m)))
    (fun m => hη01 _) hψplat hψsupp
  exact le_trans hmain hc6


open scoped ContDiff in
/-- **The derivative bound** (Track R, W1e): a smooth window supported
in `[−2,2]` has a globally bounded derivative that is also supported in
`[−2,2]` — compactness for the bound on the support, and local
vanishing off it. Supplies the `B′`-data that the smoothed-window
Lipschitz bound (`abs_norm_sq_smoothedLogSum_sub_le`) consumes. -/
theorem exists_deriv_bound (η : ℝ → ℝ) (hηs : ContDiff ℝ ∞ η)
    (hη2 : ∀ u, η u ≠ 0 → |u| ≤ 2) :
    ∃ B' : ℝ, 0 ≤ B' ∧ (∀ u, |deriv η u| ≤ B')
      ∧ (∀ u, deriv η u ≠ 0 → |u| ≤ 2) := by
  classical
  have hcont : Continuous (deriv η) := hηs.continuous_deriv (by norm_num)
  -- the derivative vanishes off the support
  have hzero : ∀ u : ℝ, 2 < |u| → deriv η u = 0 := by
    intro u hu
    have hopen : IsOpen {v : ℝ | 2 < |v|} :=
      isOpen_lt continuous_const continuous_abs
    have hmem : u ∈ {v : ℝ | 2 < |v|} := hu
    have hev : η =ᶠ[nhds u] (fun _ => 0) := by
      refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) ?_
      intro v hv
      by_contra hne
      exact absurd (hη2 v hne) (by
        simp only [Set.mem_setOf_eq] at hv
        linarith)
    have := hev.deriv_eq
    rw [this]
    simp
  -- bound on the compact support
  obtain ⟨u₀, -, hmax'⟩ := IsCompact.exists_isMaxOn
    (isCompact_Icc : IsCompact (Set.Icc (-2:ℝ) 2))
    ⟨-2, by norm_num⟩
    ((continuous_abs.comp hcont).continuousOn)
  have hmax : ∀ u ∈ Set.Icc (-2:ℝ) 2, |deriv η u| ≤ |deriv η u₀| :=
    fun u hu => hmax' hu
  refine ⟨|deriv η u₀|, abs_nonneg _, ?_, ?_⟩
  · intro u
    rcases le_or_gt |u| 2 with hle | hgt
    · refine hmax u ?_
      rw [Set.mem_Icc]
      rw [abs_le] at hle
      exact hle
    · rw [hzero u hgt]
      simp
  · intro u hne
    by_contra hgt
    push_neg at hgt
    exact hne (hzero u hgt)


end MoltResearch
