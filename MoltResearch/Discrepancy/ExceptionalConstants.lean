import MoltResearch.Discrepancy.BrunTitchmarsh
import MoltResearch.Discrepancy.BandSchedule
import MoltResearch.Discrepancy.PrimeMassCell
import MoltResearch.Discrepancy.ExpSums

/-!
# The `𝒰` leg's integer constants (Track R, A2-III, M-5)

`BandSchedule.exceptional_threshold_le_budget` names three groups of
`setIntegral_band_energy_exceptional_max_le`'s right-hand side — `Aint` the
integer large-values factor, `Bpri` the prime one, and `Γ` the ratio by which
the `V₀`-dependent part of the prime term exceeds the `V₀`-free part — and
leaves all three abstract.  `PrimeMassCell` instantiates the prime-supported
ones; this module is `Aint`.

`Aint = 64·(N + #K·√T)·(log 2T + 1)·∑_{n ≤ N} ‖a_n‖²/n²`, and two of its four
factors are not schedule parameters at all: the coefficient energy of the
integer polynomial, and the number of cells in the cover.  Both are bounded
here by absolute arithmetic — the energy by the telescoping `∑ 1/n² < 2` the
Brun–Titchmarsh module already carries, the cell count by the observation that
integer cells lying inside `[−T, T]` are indexed by distinct integers of
`[⌈−T⌉, ⌊T−1⌋]`.

**The two large-values factors run in opposite directions, and that is the
shape of the leg.**  `Bpri ≲ (log P)^{−2}` decays (`prime_energy_dyadic_le`),
while `Aint ≲ T^{3/2}·log T` *grows*: the cover contributes `#K·√T ≍ T^{3/2}`,
which is the price of counting frequencies one integer cell at a time.  The
`𝒰` leg's binding term is the cross term `2δ√(Aint·Bpri·Γ)`, so what it
actually has to afford is `δ·T^{3/4}·(log T)^{1/2}/log P` up to constants —
the square root that S-cal-5's exponent `25/4` comes from.
-/

namespace MoltResearch

open Finset

/-- **The coefficient energy of the integer polynomial** (Track R, A2-III, M-5).

`∑_{1 ≤ n ≤ N} ‖a_n‖²/n² ≤ 2` for coefficients bounded by `1`.

The last factor of `Aint`, and an absolute constant rather than a schedule
quantity: the integer polynomial's length `N` enters the `𝒰` leg through the
large-values count, not through its energy.  `sum_one_div_sq_Icc_le_two` is the
telescoping `∑_{m ≤ z} 1/m² ≤ 2 − 1/z` already in `BrunTitchmarsh`. -/
theorem integer_energy_le (N : ℕ) (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) :
    ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 ≤ 2 := by
  classical
  have hbare : ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n ^ 2) := by
    refine Finset.sum_le_sum fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hb1 : ‖a n‖ ^ 2 ≤ 1 := by
      have h0 : (0 : ℝ) ≤ ‖a n‖ := norm_nonneg _
      nlinarith [ha n]
    gcongr
  exact hbare.trans (sum_one_div_sq_Icc_le_two N)

/-- **The number of cells in the cover** (Track R, A2-III, M-5).

`#K ≤ 2T` for a family of integer cells `[k, k+1)` all lying inside `[−T, T]`.

The hypothesis is `hKT` of `setIntegral_band_energy_exceptional_max_le` verbatim
— the statement that the *cells*, not the sample points, sit in the frequency
range — so a consumer of that lemma has already supplied it.  The bound is the
`ℤ`-interval count `⌊T−1⌋ − ⌈−T⌉ + 1 ≤ 2T`, and the two roundings cancel
against the cell's own width rather than costing anything.

This is what makes `Aint` explicit in `T`: without it the leg's integer factor
carries `#K`, a quantity of the cover rather than of the schedule. -/
theorem card_cells_le (T : ℝ) (hT : 0 ≤ T) (K : Finset ℤ)
    (hKT : ∀ k ∈ K, -T ≤ (k : ℝ) ∧ (k : ℝ) + 1 ≤ T) :
    (K.card : ℝ) ≤ 2 * T := by
  classical
  have hsub : K ⊆ Finset.Icc ⌈-T⌉ ⌊T - 1⌋ := by
    intro k hk
    obtain ⟨h1, h2⟩ := hKT k hk
    rw [Finset.mem_Icc]
    exact ⟨Int.ceil_le.mpr h1, Int.le_floor.mpr (by linarith)⟩
  have hcard : K.card ≤ (Finset.Icc ⌈-T⌉ ⌊T - 1⌋).card := Finset.card_le_card hsub
  have hIcc : (Finset.Icc ⌈-T⌉ ⌊T - 1⌋).card = (⌊T - 1⌋ + 1 - ⌈-T⌉).toNat :=
    Int.card_Icc _ _
  have hfl : ((⌊T - 1⌋ : ℤ) : ℝ) ≤ T - 1 := Int.floor_le _
  have hce : -T ≤ ((⌈-T⌉ : ℤ) : ℝ) := Int.le_ceil _
  have hbd : (((⌊T - 1⌋ + 1 - ⌈-T⌉ : ℤ)) : ℝ) ≤ 2 * T := by
    push_cast
    linarith
  have hnat : (((⌊T - 1⌋ + 1 - ⌈-T⌉).toNat : ℕ) : ℝ) ≤ 2 * T := by
    rcases le_or_gt (⌊T - 1⌋ + 1 - ⌈-T⌉) 0 with h | h
    · have : (⌊T - 1⌋ + 1 - ⌈-T⌉).toNat = 0 := Int.toNat_of_nonpos h
      rw [this]
      simpa using (by linarith : (0 : ℝ) ≤ 2 * T)
    · have hcast : (((⌊T - 1⌋ + 1 - ⌈-T⌉).toNat : ℕ) : ℝ)
          = (((⌊T - 1⌋ + 1 - ⌈-T⌉ : ℤ)) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg h.le
      rw [hcast]
      exact hbd
  calc (K.card : ℝ) ≤ (((⌊T - 1⌋ + 1 - ⌈-T⌉).toNat : ℕ) : ℝ) := by
        rw [← hIcc]
        exact_mod_cast hcard
    _ ≤ 2 * T := hnat

/-- **The `𝒰` leg's integer large-values factor** (Track R, A2-III, M-5).

`Aint ≤ 128·(N + 2T^{3/2})·(log 2T + 1)`.

The left-hand side is the group named `Aint` in
`BandSchedule.exceptional_threshold_le_budget`, i.e. the `V₀²`-coefficient of
`setIntegral_band_energy_exceptional_max_le`, and the right-hand side is free of
both the cover and the coefficients: `integer_energy_le` absorbs the energy into
the constant and `card_cells_le` turns `#K·√T` into `2T·√T`.

`log(2T) + 1 ≥ 0` is where `1 ≤ T` is used, and it is the only place — the leg's
integer half is otherwise insensitive to the frequency range's size beyond the
`T^{3/2}` the cover costs. -/
theorem integer_largeValues_factor_le (N : ℕ) (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (T : ℝ) (hT : 1 ≤ T) (K : Finset ℤ)
    (hKT : ∀ k ∈ K, -T ≤ (k : ℝ) ∧ (k : ℝ) + 1 ≤ T) :
    64 * ((N : ℝ) + (K.card : ℝ) * Real.sqrt T) * (Real.log (2 * T) + 1)
        * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ 128 * ((N : ℝ) + 2 * T * Real.sqrt T) * (Real.log (2 * T) + 1) := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hlog : (0 : ℝ) ≤ Real.log (2 * T) + 1 := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * T)
    linarith
  have hcard := card_cells_le T hT0 K hKT
  have henergy := integer_energy_le N a ha
  have hsqrt : (0 : ℝ) ≤ Real.sqrt T := Real.sqrt_nonneg T
  have hE0 : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  calc 64 * ((N : ℝ) + (K.card : ℝ) * Real.sqrt T) * (Real.log (2 * T) + 1)
        * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ 64 * ((N : ℝ) + 2 * T * Real.sqrt T) * (Real.log (2 * T) + 1) * 2 := by
        gcongr
    _ = 128 * ((N : ℝ) + 2 * T * Real.sqrt T) * (Real.log (2 * T) + 1) := by ring

/-! ## The ratio `Γ` (M-6) -/

/-- **The Ramaré split's parameter has an optimum, and it is attained**
(Track R, A2-III, M-6).

`setIntegral_band_energy_exceptional_max_le` carries a free positive parameter
`lam`, entering its prime term as `(1 + lam) + (1/lam)·c²` with
`c = 2π·log(2P)` — the split between the block's own contribution and the cost
of its derivative.  The best choice is `lam = c`, where the two halves balance
and the factor is `1 + 2c`.

Stated as an existential, and for the same reason
`BandSchedule.exists_threshold_balanced` is: `lam` is the estimate's own
parameter rather than the consumer's, so what a consumer needs is that *some*
admissible value makes the leg fit — and it must be able to exhibit one, not
merely know that a good one exists.  Recorded as an **equality** at the optimum
for that reason. -/
theorem exists_lam_balanced (c : ℝ) (hc : 0 < c) :
    ∃ lam : ℝ, 0 < lam ∧ (1 + lam) + (1 / lam) * c ^ 2 = 1 + 2 * c := by
  refine ⟨c, hc, ?_⟩
  field_simp
  ring

/-- **The `𝒰` leg's ratio `Γ`, instantiated** (Track R, A2-III, M-6).

`Γ ≤ e^π·((T+1)/P + 4)·(256/log P + 2048π)·e^{−log P/(log 2T)^θ}·(log 2T)²`
at the balanced `lam`.

`Γ` is the group of `BandSchedule.exceptional_threshold_le_budget` measuring how
much the `V₀`-dependent part of the prime term exceeds the `V₀`-free part.  It
is the last of that lemma's three groups to be instantiated, after `Bpri`
(`PrimeMassCell.prime_energy_dyadic_le`) and `Aint`
(`integer_largeValues_factor_le`).

**The finding: the Ramaré cost and the block's prime mass cancel to an absolute
constant.**  `exists_lam_balanced` prices the split at `1 + 4π·log(2P)`, which
*grows* like `log P`; the block's prime mass is `≤ 256/log P`
(`PrimeMassCell.sum_one_div_prime_dyadic_le`), which decays at exactly the same
rate.  Their product is `256/log P + 1024π·log(2P)/log P ≤ 256/log P + 2048π`,
bounded absolutely — so `Γ`'s dependence on the prime scale is carried entirely
by the exponential saving `e^{−log P/(log 2T)^θ}` and the term `(T+1)/P`,
and by nothing else.  `log(2P) ≤ 2 log P` is what closes it, and it is sharp at
`P = 2`.

That matters for the leg's arithmetic: with `Bpri ≲ (log P)^{−2}` and `Γ`'s
prime dependence reduced to the exponential, the cross term
`2δ√(Aint·Bpri·Γ)` inherits the *square root* of the zero-free-region saving,
which is the `[MR]` Lemma 11 input entering at half strength. -/
theorem exists_lam_exceptional_ratio_le (θ : ℝ) (P : ℕ) (hP : 2 ≤ P) (Y : Finset ℕ)
    (hY : ∀ p ∈ Y, p.Prime) (hlo : ∀ p ∈ Y, P < p) (hhi : ∀ p ∈ Y, p ≤ 2 * P)
    (T : ℝ) (hT : 1 ≤ T) :
    ∃ lam : ℝ, 0 < lam ∧
      Real.exp Real.pi * ((T + 1) / (P : ℝ) + 2 * (2 : ℝ))
            * ((1 + lam) + (1 / lam) * (2 * Real.pi * Real.log (2 * (P : ℝ))) ^ 2)
            * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ))
            * Real.exp (-(Real.log P / (Real.log (2 * T)) ^ θ))
            * (Real.log (2 * T)) ^ 2
        ≤ Real.exp Real.pi * ((T + 1) / (P : ℝ) + 4)
            * (256 / Real.log P + 2048 * Real.pi)
            * Real.exp (-(Real.log P / (Real.log (2 * T)) ^ θ))
            * (Real.log (2 * T)) ^ 2 := by
  classical
  have hP0 : (0 : ℝ) < (P : ℝ) := by
    have : 0 < P := by omega
    exact_mod_cast this
  have hlogP : (0 : ℝ) < Real.log P := Real.log_pos (by exact_mod_cast hP)
  have hlog2P : (0 : ℝ) < Real.log (2 * (P : ℝ)) := by
    refine Real.log_pos ?_
    have : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
    linarith
  have hc : (0 : ℝ) < 2 * Real.pi * Real.log (2 * (P : ℝ)) := by
    have := Real.pi_pos
    positivity
  obtain ⟨lam, hlam0, hlam⟩ := exists_lam_balanced _ hc
  refine ⟨lam, hlam0, ?_⟩
  -- the mass of the block, and the cancellation against the split's cost
  have hmass := sum_one_div_prime_dyadic_le P hP Y hY hlo hhi
  have hmass0 : (0 : ℝ) ≤ ∑ p ∈ Y, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_nonneg fun p _ => by positivity
  have hsplit0 : (0 : ℝ) ≤ 1 + 2 * (2 * Real.pi * Real.log (2 * (P : ℝ))) := by
    linarith
  have hlogle : Real.log (2 * (P : ℝ)) ≤ 2 * Real.log P := by
    have h2 : Real.log (2 * (P : ℝ)) = Real.log 2 + Real.log P := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hP0)]
    have hle : Real.log 2 ≤ Real.log P := by
      refine Real.log_le_log (by norm_num) ?_
      exact_mod_cast hP
    linarith
  have hkey : ((1 + lam) + (1 / lam) * (2 * Real.pi * Real.log (2 * (P : ℝ))) ^ 2)
      * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ))
      ≤ 256 / Real.log P + 2048 * Real.pi := by
    rw [hlam]
    refine (mul_le_mul_of_nonneg_left hmass hsplit0).trans ?_
    have hpi := Real.pi_pos
    have hL : (1 + 2 * (2 * Real.pi * Real.log (2 * (P : ℝ)))) * (256 / Real.log P)
        = (256 * (1 + 2 * (2 * Real.pi * Real.log (2 * (P : ℝ))))) / Real.log P := by
      ring
    rw [hL, div_add' _ _ _ (ne_of_gt hlogP)]
    gcongr
    nlinarith [hpi, hlogle]
  -- the two flanking groups are nonnegative, so the middle bound propagates
  have hA0 : (0 : ℝ) ≤ Real.exp Real.pi * ((T + 1) / (P : ℝ) + 4) := by
    have : (0 : ℝ) ≤ (T + 1) / (P : ℝ) := by positivity
    have := Real.exp_pos Real.pi
    nlinarith
  have hC0 : (0 : ℝ) ≤ Real.exp (-(Real.log P / (Real.log (2 * T)) ^ θ))
      * (Real.log (2 * T)) ^ 2 := by positivity
  calc Real.exp Real.pi * ((T + 1) / (P : ℝ) + 2 * (2 : ℝ))
          * ((1 + lam) + (1 / lam) * (2 * Real.pi * Real.log (2 * (P : ℝ))) ^ 2)
          * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ))
          * Real.exp (-(Real.log P / (Real.log (2 * T)) ^ θ))
          * (Real.log (2 * T)) ^ 2
      = (Real.exp Real.pi * ((T + 1) / (P : ℝ) + 4))
          * (((1 + lam) + (1 / lam) * (2 * Real.pi * Real.log (2 * (P : ℝ))) ^ 2)
              * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ)))
          * (Real.exp (-(Real.log P / (Real.log (2 * T)) ^ θ))
              * (Real.log (2 * T)) ^ 2) := by ring
    _ ≤ (Real.exp Real.pi * ((T + 1) / (P : ℝ) + 4))
          * (256 / Real.log P + 2048 * Real.pi)
          * (Real.exp (-(Real.log P / (Real.log (2 * T)) ^ θ))
              * (Real.log (2 * T)) ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey hA0) hC0
    _ = Real.exp Real.pi * ((T + 1) / (P : ℝ) + 4)
          * (256 / Real.log P + 2048 * Real.pi)
          * Real.exp (-(Real.log P / (Real.log (2 * T)) ^ θ))
          * (Real.log (2 * T)) ^ 2 := by ring

/-! ## The pointwise input `δ` (M-12) -/

/-- **The normalised polynomial is bounded by its plain partial sums** (Track R,
A2-III, M-12).

`‖∑_{1 ≤ n ≤ N} (a_n/n)·e(−t log n)‖ ≤ E` whenever every plain partial sum
`∑_{1 ≤ n < P} a_n·e(−t log n)` is bounded by `E`.

This is the shape of `δ` — the pointwise hypothesis `hδ` of
`band_energy_le_budget_of_exceptional` and of its instantiated form — expressed
in terms of a *plain* sum bound, which is what the in-tree Halász chain
produces (`plain_sumC_le_halasz_shell_of_nonPretentious` bounds `‖∑_{n ≤ x} f n‖`,
not a normalised polynomial).

**The `1/n` weight costs nothing.**  `ExpSums.abel_weight_bound` prices a
decreasing nonnegative weight against uniformly bounded partial sums at
`w(M)·E`, and here `M = 1`, so `w(M) = 1` and `δ = E` exactly.  That is worth
recording because the `𝒰` leg has no margin: `BandSchedule.exceptional_saving_le_budget`
already spends a factor `2/ε` on the *other* partial summation in this chain —
the long-sum-to-short-sum transfer — and a second loss here would not be
affordable.  There is none.

The twist `e(−t log n)` rides along untouched: it is absorbed into the
coefficient sequence before the Abel step, so the bound is uniform in `t` as
soon as the partial-sum hypothesis is. -/
theorem norm_slice_poly_le_of_partial_sums (a : ℕ → ℂ) (N : ℕ) (t E : ℝ)
    (hN : 1 ≤ N)
    (hE : ∀ P, P ≤ N + 1 →
      ‖∑ n ∈ Finset.Ico 1 P, a n
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ E) :
    ‖∑ n ∈ Finset.Icc 1 N, (a n / (n : ℂ))
        * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ E := by
  classical
  set A : ℕ → ℂ := fun n => a n
    * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ) with hA
  set w : ℕ → ℝ := fun n => 1 / (n : ℝ) with hw
  have hw0 : ∀ n, 1 ≤ n → n ≤ N → 0 ≤ w n := by
    intro n _ _
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    positivity
  have hwd : ∀ n, 1 ≤ n → n < N → w (n + 1) ≤ w n := by
    intro n hn _
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hstep : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact one_div_le_one_div_of_le hn0 hstep
  have habel := ExpSums.abel_weight_bound (w := w) (a := A) (M := 1) (N := N)
    (E := E) hN hw0 hwd (fun P h1 h2 => hE P h2)
  have hrw : ∑ n ∈ Finset.Ico 1 (N + 1), w n • A n
      = ∑ n ∈ Finset.Icc 1 N, (a n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ) := by
    have hset : Finset.Ico 1 (N + 1) = Finset.Icc 1 N := by
      ext m
      rw [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [hset]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    have hn0 : (n : ℂ) ≠ 0 := by
      have : 0 < n := hn.1
      exact_mod_cast Nat.cast_ne_zero.mpr (by omega)
    rw [hA, hw, Complex.real_smul]
    push_cast
    field_simp
  have hw1 : w 1 = 1 := by rw [hw]; norm_num
  rw [hrw] at habel
  rw [hw1, one_mul] at habel
  exact habel

end MoltResearch
