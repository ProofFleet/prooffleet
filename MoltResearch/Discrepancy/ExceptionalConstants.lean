import MoltResearch.Discrepancy.BrunTitchmarsh
import MoltResearch.Discrepancy.BandSchedule

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

end MoltResearch
