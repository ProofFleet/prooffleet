import MoltResearch.Discrepancy.MajorArcAssembly
import MoltResearch.Discrepancy.WindowAssembly
import MoltResearch.Discrepancy.LogUniform

/-!
# Track R: the block scale and the wrapper's bookkeeping (R6-8a, R7-A, R7-B, R7-C0)

The A.2 input of `sum_restricted_window_logavg_le_of_meanSquare` is demanded, for every
divisor `d ∣ q` and every character `χ` mod `q/d`, on dyadic blocks `(A', A'+J]` with
`⌊A/q⌋ ≤ A'+1` and `A' + J ≤ 3A`; each such application needs the twist `χ·g` to be
non-pretentious at truncation `2A'+1`.  This leaf produces all of those from **one**
hypothesis on `g` — strength `q·A₀ + 26`, truncation `6A+1` — by the downward scale
transfer of `WindowAssembly` (`nonPretentiousAt_scale_transfer`, priced by
`mertens_mass_diff_le`) followed by the character twist of `MajorArcAssembly`
(`nonPretentiousAt_charMul`).  It is kept out of `MajorArcAssembly` so that module stays
below the window harness in the import graph.

The second half (R7-A) holds the elementary bookkeeping of the `mrp` wrapper
(`Problems/tao2015_a1_r6r7_design_report.md` §1.4, §8 Phase R7): the harmonic mass of a
dyadic block lies in `[1/2, 1]`; the once-paid `𝒮ᶜ` removal on a dyadic block
(`sum_window_div_le_restricted_add_complement`), priced by the complement mass of
`(A, 2A+H]`, which the density clause of the A.2 Prop on two dyadic blocks bounds by
`3εc·∑_{(A,2A]} 1/n` (`sum_complement_Ioc_le_of_density`); and the dyadic cover of
`(lo, hi]` by the blocks `(2^k, 2^{k+1}]`, `⌊log₂ lo⌋ ≤ k ≤ ⌊log₂ hi⌋`, whose total
harmonic mass is at most `log(4·hi/lo)` (`sum_Ioc_le_sum_dyadic_cover`,
`sum_dyadic_cover_one_div_le`).

The third part (R7-B) is what the wrapper does with the three kinds of dyadic block: a
**good** block `(Ab, 2Ab]` — one with `log(6Ab+1) ≥ θ·log(8⌈x⌉₊)` — inherits
non-pretentiousness from the interface's hypothesis at scale `⌈x⌉₊` at strength
`A/8 − 24 − 2log(1/θ)` (`nonPretentiousAt_block_of_good`: up to `8⌈x⌉₊`, then down at a
Mertens cost bounded by `θ`); the **small** and **bad** blocks are priced trivially
(`sum_window_div_le_sum_one_div`), and there are few of them
(`card_filter_pow_lt_le`: at most `⌊log₂ X⌋ + 1` blocks `(2^k, 2^{k+1}]` with `2^k < X`).

The last part (R7-C0) supplies the two analytic trivialities of the parameter choice:
eventually `T·max(C(log H)^B, 1)^m ≤ H` (`exists_forall_polylog_le`, from
`Real.isLittleO_pow_log_id_atTop`), which produces the interface's `H₀`, and
`⌊t⌋₊ ≥ t/2` for `t ≥ 1` (`half_le_floor`), which compares `⌊x/w⌋₊` with `x/w`.
-/

namespace MoltResearch

open ExpSums

/-- **The twist is non-pretentious at every block scale** (Track R, R6-8a).

Let `g` be unimodular and non-pretentious at strength `q·A₀ + 26` and truncation `6A+1`,
with `7q² ≤ A`.  Then for every `d ∣ q`, every character `χ` mod `q/d`, and every block
start `A'` with `⌊A/q⌋ ≤ A'+1` and `A' ≤ 3A`, the twist `χ·g` is non-pretentious at
strength `A₀` and truncation `2A'+1`.  The truncation is moved down from `6A+1` to
`2A'+1 ≥ ⌊A/q⌋` at the Mertens cost `2·(loglog(6A+1) − loglog(2A'+1) + 12)`
(`nonPretentiousAt_scale_transfer`, `mertens_mass_diff_le`), which is at most `26`
because `(2A'+1)² ≥ ⌊A/q⌋² ≥ 6A+1`; then `nonPretentiousAt_charMul` trades the factor
`q/d ≤ q` in strength.  This is the shape in which the wrapper hands the interface's
single non-pretentiousness hypothesis to the A.2 input of every class and character. -/
theorem nonPretentiousAt_charMul_of_block (g : ℕ → ℂ) (hgu : Unimodular g) {A₀ : ℝ}
    (hA₀ : 0 ≤ A₀) {q : ℕ} (hq : 0 < q) {d : ℕ} (hd0 : 0 < d) (hdq : d ∣ q)
    (χ : DirichletCharacter ℂ (q / d)) (A A' : ℕ) (hA7 : 7 * q ^ 2 ≤ A)
    (hA'lo : A / q ≤ A' + 1) (hA'hi : A' ≤ 3 * A)
    (hnp : NonPretentiousAt g (q * A₀ + 26) (6 * A + 1)) :
    NonPretentiousAt (fun n => χ n * g n) A₀ (2 * A' + 1) := by
  have hq₀ : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdq) hd0
  have hq₀le : q / d ≤ q := Nat.div_le_self q d
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq
  -- `⌊A/q⌋ ≥ 7q`, hence `2A'+1 ≥ ⌊A/q⌋ ≥ 7q ≥ 7` and `⌊A/q⌋² ≥ 6A+1`
  have hAq7 : 7 * q ≤ A / q := (Nat.le_div_iff_mul_le hq).mpr (by nlinarith)
  have hA'2 : 4 ≤ 2 * A' + 1 := by omega
  have hsq : 6 * A + 1 ≤ (A / q) * (A / q) := by
    have hmod := Nat.div_add_mod A q
    have hlt := Nat.mod_lt A hq
    have h1 : 7 * (q * (A / q)) ≤ (A / q) * (A / q) := by
      have := Nat.mul_le_mul_right (A / q) hAq7
      linarith [this]
    have h2 : A + 1 ≤ q * (A / q) + q := by omega
    nlinarith
  have hu : A / q ≤ 2 * A' + 1 := by omega
  -- the Mertens cost of moving the truncation down is at most `26`
  have hmass : (∑ p ∈ (6 * A + 1).primesBelow, (1:ℝ)/p)
      - (∑ p ∈ (2 * A' + 1).primesBelow, (1:ℝ)/p) ≤ 13 := by
    have hle : 2 * A' + 1 ≤ 6 * A + 1 := by omega
    have hmd := mertens_mass_diff_le (2 * A' + 1) (6 * A + 1) hA'2 hle
    have huR : (4:ℝ) ≤ ((2 * A' + 1 : ℕ) : ℝ) := by exact_mod_cast hA'2
    have h6R : ((6 * A + 1 : ℕ) : ℝ) ≤ ((2 * A' + 1 : ℕ) : ℝ) ^ 2 := by
      have h1 : 6 * A + 1 ≤ (2 * A' + 1) * (2 * A' + 1) :=
        le_trans hsq (Nat.mul_le_mul hu hu)
      have h2 : ((6 * A + 1 : ℕ) : ℝ) ≤ (((2 * A' + 1) * (2 * A' + 1) : ℕ) : ℝ) := by
        exact_mod_cast h1
      rw [sq]
      push_cast at h2 ⊢
      exact h2
    have hlogu : 0 < Real.log ((2 * A' + 1 : ℕ) : ℝ) := Real.log_pos (by linarith)
    have hlog6 : Real.log ((6 * A + 1 : ℕ) : ℝ) ≤ Real.exp 1 * Real.log ((2 * A' + 1 : ℕ) : ℝ) := by
      calc Real.log ((6 * A + 1 : ℕ) : ℝ)
          ≤ Real.log (((2 * A' + 1 : ℕ) : ℝ) ^ 2) := Real.log_le_log (by positivity) h6R
        _ = 2 * Real.log ((2 * A' + 1 : ℕ) : ℝ) := by rw [Real.log_pow]; push_cast; ring
        _ ≤ Real.exp 1 * Real.log ((2 * A' + 1 : ℕ) : ℝ) := by
            have : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
            exact mul_le_mul_of_nonneg_right this hlogu.le
    have hloglog : Real.log (Real.log ((6 * A + 1 : ℕ) : ℝ))
        ≤ 1 + Real.log (Real.log ((2 * A' + 1 : ℕ) : ℝ)) := by
      have hpos6 : 0 < Real.log ((6 * A + 1 : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < 6 * A + 1))
      calc Real.log (Real.log ((6 * A + 1 : ℕ) : ℝ))
          ≤ Real.log (Real.exp 1 * Real.log ((2 * A' + 1 : ℕ) : ℝ)) :=
            Real.log_le_log hpos6 hlog6
        _ = 1 + Real.log (Real.log ((2 * A' + 1 : ℕ) : ℝ)) := by
            rw [Real.log_mul (Real.exp_ne_zero 1) hlogu.ne', Real.log_exp]
    linarith
  -- move the truncation down at strength `q·A₀`
  have hdown : NonPretentiousAt g (q * A₀) (2 * A' + 1) := by
    refine nonPretentiousAt_scale_transfer (fun p => (hgu p).le) hnp (by omega)
      (by positivity) ?_
    linarith
  -- and twist
  refine nonPretentiousAt_charMul g hdown hq₀ χ hA₀ ?_
  have : ((q / d : ℕ) : ℝ) ≤ q := by exact_mod_cast hq₀le
  calc A₀ * ((q / d : ℕ) : ℝ) ≤ A₀ * q := mul_le_mul_of_nonneg_left this hA₀
    _ = q * A₀ := mul_comm _ _

/-! ### R7-A: the wrapper's bookkeeping on dyadic blocks -/

/-- The harmonic mass of a dyadic block is at least `1/2` (Track R, R7-A). -/
theorem half_le_sum_one_div_Ioc_dyadic (A : ℕ) (hA : 1 ≤ A) :
    (1:ℝ)/2 ≤ ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n := by
  have hpt : ∀ n ∈ Finset.Ioc A (2 * A), (1:ℝ) / ((2 * A : ℕ) : ℝ) ≤ (1:ℝ)/n := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    exact one_div_le_one_div_of_le hn0 (by exact_mod_cast hn.2)
  have := Finset.card_nsmul_le_sum _ _ _ hpt
  rw [Nat.card_Ioc, nsmul_eq_mul] at this
  have hA0 : (0:ℝ) < A := by exact_mod_cast hA
  calc (1:ℝ)/2 = ((2 * A - A : ℕ) : ℝ) * (1 / ((2 * A : ℕ) : ℝ)) := by
        have : (2 * A - A : ℕ) = A := by omega
        rw [this]
        push_cast
        field_simp
    _ ≤ _ := this

/-- The harmonic mass of a dyadic block is at most `log 2 < 1` (Track R, R7-A). -/
theorem sum_one_div_Ioc_dyadic_le_one (A : ℕ) (hA : 1 ≤ A) :
    ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n ≤ 1 := by
  have h := sum_one_div_Ioc_le hA (by omega : A ≤ 2 * A)
  have hA0 : (0:ℝ) < A := by exact_mod_cast hA
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul two_ne_zero hA0.ne'] at h
  linarith [Real.log_two_lt_d9]

/-- **The once-paid `𝒮ᶜ` removal on a dyadic block** (Track R, R7-3): the log-averaged
window sums of a `1`-bounded `g` twisted by `e(mα)` are at most the `𝒮`-restricted ones
plus twice the complement mass of `(A, 2A+H]` — `norm_block_le_restricted_add_card`
window by window, and the harmonic sliding count `sum_card_filter_window_div_le`
(`2H ≤ A`) for the counts. -/
theorem sum_window_div_le_restricted_add_complement (g : ℕ → ℂ) (hb : ∀ m, ‖g m‖ ≤ 1)
    (levels : List (Finset ℕ)) (α : ℝ) (A H : ℕ) (hH : 0 < H) (h2H : 2 * H ≤ A) :
    ∑ n ∈ Finset.Ioc A (2 * A),
        ‖∑ m ∈ Finset.Ioc n (n + H),
          g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ))‖ / ((H : ℝ) * n)
      ≤ (∑ n ∈ Finset.Ioc A (2 * A),
          ‖∑ m ∈ (Finset.Ioc n (n + H)).filter (HasFactorInAll levels),
            g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ))‖ / ((H : ℝ) * n))
        + 2 * ∑ m ∈ (Finset.Ioc A (2 * A + H)).filter (fun m => ¬ HasFactorInAll levels m),
            (1:ℝ) / m := by
  classical
  have hH0 : (0:ℝ) < H := by exact_mod_cast hH
  have hφ : ∀ m : ℕ, ‖Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ))‖ ≤ 1 := by
    intro m
    rw [Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero]
  have hpt : ∀ n ∈ Finset.Ioc A (2 * A),
      ‖∑ m ∈ Finset.Ioc n (n + H),
          g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ))‖ / ((H : ℝ) * n)
        ≤ ‖∑ m ∈ (Finset.Ioc n (n + H)).filter (HasFactorInAll levels),
            g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ))‖ / ((H : ℝ) * n)
          + (1 / (H : ℝ)) * ((((Finset.Ioc n (n + H)).filter
              (fun m => ¬ HasFactorInAll levels m)).card : ℝ) / n) := by
    intro n hn
    have hn0 : (0:ℝ) < n := by
      rw [Finset.mem_Ioc] at hn
      exact_mod_cast (by omega : 0 < n)
    have h := norm_block_le_restricted_add_card g hb
      (fun m => Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ))) hφ levels n H
    calc ‖∑ m ∈ Finset.Ioc n (n + H),
            g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ))‖ / ((H : ℝ) * n)
        ≤ (‖∑ m ∈ (Finset.Ioc n (n + H)).filter (HasFactorInAll levels),
              g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ))‖
            + (((Finset.Ioc n (n + H)).filter
                (fun m => ¬ HasFactorInAll levels m)).card : ℝ)) / ((H : ℝ) * n) :=
          div_le_div_of_nonneg_right h (by positivity)
      _ = _ := by
          rw [add_div]
          congr 1
          rw [div_mul_eq_div_div_swap, one_div_mul_eq_div]
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  refine add_le_add le_rfl ?_
  have hcount := sum_card_filter_window_div_le (fun m => ¬ HasFactorInAll levels m) A (2 * A) H h2H
  calc (1 / (H : ℝ)) * ∑ n ∈ Finset.Ioc A (2 * A),
        (((Finset.Ioc n (n + H)).filter (fun m => ¬ HasFactorInAll levels m)).card : ℝ) / n
      ≤ (1 / (H : ℝ)) * (2 * H * ∑ m ∈ (Finset.Ioc A (2 * A + H)).filter
          (fun m => ¬ HasFactorInAll levels m), (1:ℝ) / m) :=
        mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = 2 * ∑ m ∈ (Finset.Ioc A (2 * A + H)).filter
          (fun m => ¬ HasFactorInAll levels m), (1:ℝ) / m := by
        field_simp

/-- **The complement mass of `(A, 2A+H]` from the density clause** (Track R, R7-3'): if
the `𝒮ᶜ` log-density of the dyadic blocks `(A, 2A]` and `(2A, 4A]` is at most `εc`, then
for `H ≤ 2A` the complement mass of `(A, 2A+H]` is at most `3εc·∑_{(A,2A]} 1/n`
(the second block's harmonic mass is `≤ 1 ≤ 2·∑_{(A,2A]} 1/n`). -/
theorem sum_complement_Ioc_le_of_density (levels : List (Finset ℕ)) (εc : ℝ) (hεc : 0 ≤ εc)
    (A H : ℕ) (hA : 1 ≤ A) (hHA : H ≤ 2 * A)
    (hd1 : ∑ n ∈ (Finset.Ioc A (2 * A)).filter (fun n => ¬ HasFactorInAll levels n), (1:ℝ)/n
      ≤ εc * ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n)
    (hd2 : ∑ n ∈ (Finset.Ioc (2 * A) (2 * (2 * A))).filter
        (fun n => ¬ HasFactorInAll levels n), (1:ℝ)/n
      ≤ εc * ∑ n ∈ Finset.Ioc (2 * A) (2 * (2 * A)), (1:ℝ)/n) :
    ∑ m ∈ (Finset.Ioc A (2 * A + H)).filter (fun m => ¬ HasFactorInAll levels m), (1:ℝ) / m
      ≤ 3 * εc * ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n := by
  classical
  have hS := half_le_sum_one_div_Ioc_dyadic A hA
  have hS2 := sum_one_div_Ioc_dyadic_le_one (2 * A) (by omega)
  have hsub : (Finset.Ioc A (2 * A + H)).filter (fun m => ¬ HasFactorInAll levels m)
      ⊆ ((Finset.Ioc A (2 * A)).filter (fun m => ¬ HasFactorInAll levels m))
        ∪ ((Finset.Ioc (2 * A) (2 * (2 * A))).filter (fun m => ¬ HasFactorInAll levels m)) := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Ioc] at hm
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ioc]
    rcases le_or_gt m (2 * A) with h | h
    · exact Or.inl ⟨⟨hm.1.1, h⟩, hm.2⟩
    · exact Or.inr ⟨⟨h, by omega⟩, hm.2⟩
  calc ∑ m ∈ (Finset.Ioc A (2 * A + H)).filter (fun m => ¬ HasFactorInAll levels m), (1:ℝ) / m
      ≤ ∑ m ∈ ((Finset.Ioc A (2 * A)).filter (fun m => ¬ HasFactorInAll levels m))
          ∪ ((Finset.Ioc (2 * A) (2 * (2 * A))).filter (fun m => ¬ HasFactorInAll levels m)),
          (1:ℝ) / m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => by positivity)
    _ = (∑ m ∈ (Finset.Ioc A (2 * A)).filter (fun m => ¬ HasFactorInAll levels m), (1:ℝ) / m)
        + ∑ m ∈ (Finset.Ioc (2 * A) (2 * (2 * A))).filter
            (fun m => ¬ HasFactorInAll levels m), (1:ℝ) / m := by
        refine Finset.sum_union ?_
        rw [Finset.disjoint_left]
        intro m hm1 hm2
        rw [Finset.mem_filter, Finset.mem_Ioc] at hm1 hm2
        omega
    _ ≤ εc * (∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n)
        + εc * ∑ n ∈ Finset.Ioc (2 * A) (2 * (2 * A)), (1:ℝ)/n := add_le_add hd1 hd2
    _ ≤ εc * (∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n)
        + εc * (2 * ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n) := by
        gcongr
        linarith
    _ = 3 * εc * ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n := by ring

/-- **The dyadic cover** (Track R, R7-1): a nonnegative sum over `(lo, hi]`, `1 ≤ lo`, is
at most the sum over the dyadic blocks `(2^k, 2^{k+1}]`, `⌊log₂ lo⌋ ≤ k ≤ ⌊log₂ hi⌋`
(fibre by `k = ⌊log₂(n−1)⌋`; each fibre lies in its block). -/
theorem sum_Ioc_le_sum_dyadic_cover (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (lo hi : ℕ)
    (hlo : 1 ≤ lo) :
    ∑ n ∈ Finset.Ioc lo hi, f n
      ≤ ∑ k ∈ Finset.Icc (Nat.log 2 lo) (Nat.log 2 hi),
          ∑ n ∈ Finset.Ioc (2 ^ k) (2 ^ (k + 1)), f n := by
  classical
  have hmaps : ∀ n ∈ Finset.Ioc lo hi,
      Nat.log 2 (n - 1) ∈ Finset.Icc (Nat.log 2 lo) (Nat.log 2 hi) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_Icc]
    exact ⟨Nat.log_mono_right (by omega), Nat.log_mono_right (by omega)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun k _ => ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => hf n)
  intro n hn
  rw [Finset.mem_filter, Finset.mem_Ioc] at hn
  obtain ⟨⟨hlon, _⟩, hk⟩ := hn
  rw [Finset.mem_Ioc]
  have hn1 : n - 1 ≠ 0 := by omega
  have h1 : 2 ^ k ≤ n - 1 := by
    rw [← hk]
    exact Nat.pow_log_le_self 2 hn1
  have h2 : n - 1 < 2 ^ (k + 1) := by
    rw [← hk]
    exact Nat.lt_pow_succ_log_self (by norm_num) (n - 1)
  omega

/-- **The harmonic mass of the dyadic cover** (Track R, R7-1): the blocks
`(2^k, 2^{k+1}]`, `⌊log₂ lo⌋ ≤ k ≤ ⌊log₂ hi⌋`, carry total harmonic mass at most
`log(4·hi/lo)` — each block has mass `log 2`, and `2^{⌊log₂ hi⌋ + 1 − ⌊log₂ lo⌋} ≤ 4hi/lo`. -/
theorem sum_dyadic_cover_one_div_le (lo hi : ℕ) (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) :
    ∑ k ∈ Finset.Icc (Nat.log 2 lo) (Nat.log 2 hi),
        ∑ n ∈ Finset.Ioc (2 ^ k : ℕ) (2 ^ (k + 1)), (1:ℝ)/n
      ≤ Real.log (4 * (hi : ℝ) / lo) := by
  classical
  set k₀ := Nat.log 2 lo with hk₀
  set K := Nat.log 2 hi with hK
  have hkK : k₀ ≤ K := Nat.log_mono_right hlohi
  have hblock : ∀ k ∈ Finset.Icc k₀ K,
      ∑ n ∈ Finset.Ioc (2 ^ k : ℕ) (2 ^ (k + 1)), (1:ℝ)/n ≤ Real.log 2 := by
    intro k _
    have h := sum_one_div_Ioc_le (c := 2 ^ k) (d := 2 ^ (k + 1)) Nat.one_le_two_pow
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right k 1))
    have h2 : ((2 ^ (k + 1) : ℕ) : ℝ) = 2 * ((2 ^ k : ℕ) : ℝ) := by push_cast; ring
    rw [h2, Real.log_mul two_ne_zero (by positivity)] at h
    linarith
  refine le_trans (Finset.sum_le_sum hblock) ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  -- `2^{K+1-k₀} ≤ 4 hi / lo`
  have hlo0 : (0:ℝ) < lo := by exact_mod_cast hlo
  have hhi0 : (0:ℝ) < hi := by exact_mod_cast (le_trans hlo hlohi)
  have hpowK : 2 ^ K ≤ hi := Nat.pow_log_le_self 2 (by omega)
  have hpowk₀ : lo < 2 ^ (k₀ + 1) := Nat.lt_pow_succ_log_self (by norm_num) lo
  have hkey : ((2 ^ (K + 1 - k₀) : ℕ) : ℝ) ≤ 4 * (hi : ℝ) / lo := by
    rw [le_div_iff₀ hlo0]
    have h1 : (2 ^ (K + 1 - k₀) : ℕ) * lo ≤ 4 * hi := by
      have hsplit : 2 ^ (K + 1) = 2 ^ (K + 1 - k₀) * 2 ^ k₀ := by
        rw [← pow_add, Nat.sub_add_cancel (by omega)]
      calc (2 ^ (K + 1 - k₀) : ℕ) * lo ≤ 2 ^ (K + 1 - k₀) * (2 * 2 ^ k₀) :=
            Nat.mul_le_mul_left _ (by rw [pow_succ] at hpowk₀; omega)
        _ = 2 * 2 ^ (K + 1) := by rw [hsplit]; ring
        _ = 4 * 2 ^ K := by ring
        _ ≤ 4 * hi := Nat.mul_le_mul_left 4 hpowK
    exact_mod_cast h1
  calc ((K + 1 - k₀ : ℕ) : ℝ) * Real.log 2
      = Real.log (((2 ^ (K + 1 - k₀) : ℕ) : ℝ)) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    _ ≤ Real.log (4 * (hi : ℝ) / lo) := Real.log_le_log (by positivity) hkey

/-! ### R7-B: good blocks, and the trivial bound on the others -/

/-- **A good block inherits non-pretentiousness** (Track R, R7-2 / R7-5).

Let `g` be unimodular and non-pretentious at strength `A` and truncation `x'`, and let
`(Ab, 2Ab]` be a dyadic block with `1 ≤ Ab ≤ x'` that is *good* for the parameter
`θ ∈ (0, 1]`: `θ·log(8x') ≤ log(6Ab+1)`.  Then `g` is non-pretentious at truncation
`6Ab+1` and any strength `S ≥ 0` with `S + 24 + 2log(1/θ) ≤ A/8`.  The truncation is
first moved up to `8x'` (`nonPretentiousAt_scale_up`, strength `A/8`) — the twisted block
scale of the top blocks exceeds `x'` — and then down to `6Ab+1`
(`nonPretentiousAt_scale_transfer`), at the Mertens cost
`2(loglog(8x') − loglog(6Ab+1) + 12) ≤ 2log(1/θ) + 24` (`mertens_mass_diff_le`). -/
theorem nonPretentiousAt_block_of_good (g : ℕ → ℂ) (hgu : Unimodular g) {A : ℝ} (x' Ab : ℕ)
    (hx' : 1 ≤ x') (hAb : 1 ≤ Ab) (hAbx : Ab ≤ x') (h : NonPretentiousAt g A x')
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hgood : θ * Real.log ((8 * x' : ℕ) : ℝ) ≤ Real.log ((6 * Ab + 1 : ℕ) : ℝ))
    (S : ℝ) (hS0 : 0 ≤ S) (hS : S + 24 + 2 * Real.log (1 / θ) ≤ A / 8) :
    NonPretentiousAt g S (6 * Ab + 1) := by
  have hA0 : 0 ≤ A := by
    have : 0 ≤ Real.log (1 / θ) := Real.log_nonneg (by rw [le_div_iff₀ hθ0]; linarith)
    linarith
  -- up to `8x'` at strength `A/8`
  have hup : NonPretentiousAt g (A / 8) (8 * x') :=
    nonPretentiousAt_scale_up (c := 8) hgu h (by omega) (le_of_eq (by push_cast; ring))
      (by positivity) (by norm_num) (by linarith)
  -- the Mertens cost of coming back down to `6Ab+1`
  have h8pos : (1:ℝ) < ((8 * x' : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < 8 * x')
  have h6pos : (1:ℝ) < ((6 * Ab + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < 6 * Ab + 1)
  have hlog8 : 0 < Real.log ((8 * x' : ℕ) : ℝ) := Real.log_pos h8pos
  have hlog6 : 0 < Real.log ((6 * Ab + 1 : ℕ) : ℝ) := Real.log_pos h6pos
  have hratio : Real.log ((8 * x' : ℕ) : ℝ) ≤ (1 / θ) * Real.log ((6 * Ab + 1 : ℕ) : ℝ) := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hθ0]
    linarith
  have hloglog : Real.log (Real.log ((8 * x' : ℕ) : ℝ))
      ≤ Real.log (1 / θ) + Real.log (Real.log ((6 * Ab + 1 : ℕ) : ℝ)) := by
    rw [← Real.log_mul (by positivity) hlog6.ne']
    exact Real.log_le_log hlog8 hratio
  have hmass := mertens_mass_diff_le (6 * Ab + 1) (8 * x') (by omega) (by omega)
  refine nonPretentiousAt_scale_transfer (fun p => (hgu p).le) hup (by omega) hS0 ?_
  linarith

/-- **The trivial bound on a dyadic block** (Track R, R7-B): for `1`-bounded `g` the
log-averaged twisted window sums over `(Ab, 2Ab]` are at most the block's harmonic mass. -/
theorem sum_window_div_le_sum_one_div (g : ℕ → ℂ) (hb : ∀ m, ‖g m‖ ≤ 1) (α : ℝ) (Ab H : ℕ)
    (hH : 0 < H) :
    ∑ n ∈ Finset.Ioc Ab (2 * Ab),
        ‖∑ m ∈ Finset.Ioc n (n + H),
          g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ))‖ / ((H : ℝ) * n)
      ≤ ∑ n ∈ Finset.Ioc Ab (2 * Ab), (1:ℝ) / n := by
  classical
  have hH0 : (0:ℝ) < H := by exact_mod_cast hH
  refine Finset.sum_le_sum fun n hn => ?_
  have hn0 : (0:ℝ) < n := by
    rw [Finset.mem_Ioc] at hn
    exact_mod_cast (by omega : 0 < n)
  have hφ : ∀ m : ℕ, ‖g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ))‖ ≤ 1 := by
    intro m
    rw [norm_mul, Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero, mul_one]
    exact hb m
  have hnorm : ‖∑ m ∈ Finset.Ioc n (n + H),
      g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ))‖ ≤ H := by
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ m ∈ Finset.Ioc n (n + H),
          ‖g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ))‖
        ≤ ∑ m ∈ Finset.Ioc n (n + H), (1:ℝ) := Finset.sum_le_sum fun m _ => hφ m
      _ = H := by rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one, Nat.add_sub_cancel_left]
  rw [div_le_iff₀ (by positivity)]
  calc ‖∑ m ∈ Finset.Ioc n (n + H),
          g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ))‖
      ≤ H := hnorm
    _ = (1 / (n : ℝ)) * ((H : ℝ) * n) := by field_simp

/-- **Few dyadic blocks lie below a threshold** (Track R, R7-B): at most `⌊log₂ X⌋ + 1`
indices `k` (in any range) have `2^k < X`. -/
theorem card_filter_pow_lt_le (a b X : ℕ) (hX : 1 ≤ X) :
    ((Finset.Icc a b).filter (fun k => 2 ^ k < X)).card ≤ Nat.log 2 X + 1 := by
  classical
  have hsub : (Finset.Icc a b).filter (fun k => 2 ^ k < X) ⊆ Finset.range (Nat.log 2 X + 1) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr hk.2.le
  calc ((Finset.Icc a b).filter (fun k => 2 ^ k < X)).card
      ≤ (Finset.range (Nat.log 2 X + 1)).card := Finset.card_le_card hsub
    _ = Nat.log 2 X + 1 := Finset.card_range _

/-- **The trivial cost of the blocks below a threshold** (Track R, R7-B): the harmonic
mass of the dyadic blocks `(2^k, 2^{k+1}]` (`k` in any range) with `2^k < X` is at most
`log(2X)`. -/
theorem sum_filter_pow_lt_one_div_le (a b X : ℕ) (hX : 1 ≤ X) :
    ∑ k ∈ (Finset.Icc a b).filter (fun k => 2 ^ k < X),
        ∑ n ∈ Finset.Ioc (2 ^ k : ℕ) (2 ^ (k + 1)), (1:ℝ)/n
      ≤ Real.log (2 * (X : ℝ)) := by
  classical
  have hblock : ∀ k ∈ (Finset.Icc a b).filter (fun k => 2 ^ k < X),
      ∑ n ∈ Finset.Ioc (2 ^ k : ℕ) (2 ^ (k + 1)), (1:ℝ)/n ≤ Real.log 2 := by
    intro k _
    have h := sum_one_div_Ioc_le (c := 2 ^ k) (d := 2 ^ (k + 1)) Nat.one_le_two_pow
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right k 1))
    have h2 : ((2 ^ (k + 1) : ℕ) : ℝ) = 2 * ((2 ^ k : ℕ) : ℝ) := by push_cast; ring
    rw [h2, Real.log_mul two_ne_zero (by positivity)] at h
    linarith
  refine le_trans (Finset.sum_le_sum hblock) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard := card_filter_pow_lt_le a b X hX
  have hpow : ((2 ^ (Nat.log 2 X + 1) : ℕ) : ℝ) ≤ 2 * (X : ℝ) := by
    have : 2 ^ (Nat.log 2 X + 1) ≤ 2 * X := by
      rw [pow_succ]
      exact Nat.mul_le_mul_right 2 (Nat.pow_log_le_self 2 (by omega)) |>.trans_eq (mul_comm _ _)
    exact_mod_cast this
  calc (((Finset.Icc a b).filter (fun k => 2 ^ k < X)).card : ℝ) * Real.log 2
      ≤ ((Nat.log 2 X + 1 : ℕ) : ℝ) * Real.log 2 := by
        gcongr
    _ = Real.log (((2 ^ (Nat.log 2 X + 1) : ℕ) : ℝ)) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    _ ≤ Real.log (2 * (X : ℝ)) := Real.log_le_log (by positivity) hpow

/-! ### R7-C0: the parameter choice's analytic trivialities -/

/-- `max(Q, 1)^m ≤ Q^m + 1` for `Q ≥ 0`. -/
theorem max_one_pow_le_pow_add_one (Q : ℝ) (hQ : 0 ≤ Q) (m : ℕ) :
    (max Q 1) ^ m ≤ Q ^ m + 1 := by
  rcases le_or_gt 1 Q with h | h
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right h.le, one_pow]
    have : 0 ≤ Q ^ m := pow_nonneg hQ m
    linarith

/-- **Polylogs are eventually below `H`** (Track R, R7-C0): for `T, C > 0` and any `B, m`
there is `H₀` with `2 ≤ H` and `T·max(C(log H)^B, 1)^m ≤ H` for all `H ≥ H₀` — the
form in which every size condition of the wrapper's parameter choice (`h₀ ≥ h₁`,
`h₀ ≥ C₁/ε'^k`, `H ≤ h₀²`, `2h₀ ≤ H`) is a polylog-versus-`H` inequality. -/
theorem exists_forall_polylog_le (T C : ℝ) (hT : 0 < T) (hC : 0 < C) (B m : ℕ) :
    ∃ H₀ : ℕ, ∀ H : ℕ, H₀ ≤ H → 2 ≤ H ∧ T * (max (C * Real.log H ^ B) 1) ^ m ≤ H := by
  have hc : (0:ℝ) < 1 / (2 * T * C ^ m) := by positivity
  have hlo := (Real.isLittleO_pow_log_id_atTop (n := m * B)).def hc
  rw [Filter.eventually_atTop] at hlo
  obtain ⟨x₀, hx₀⟩ := hlo
  refine ⟨max ⌈x₀⌉₊ (⌈2 * T⌉₊ + 2), fun H hH => ?_⟩
  have hH2 : 2 ≤ H := by
    have := le_trans (le_max_right _ _) hH
    omega
  refine ⟨hH2, ?_⟩
  have hHx₀ : x₀ ≤ (H : ℝ) := by
    calc x₀ ≤ (⌈x₀⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (H : ℝ) := by exact_mod_cast le_trans (le_max_left _ _) hH
  have hH2T : 2 * T ≤ (H : ℝ) := by
    calc 2 * T ≤ (⌈2 * T⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (H : ℝ) := by
          exact_mod_cast le_trans (by omega : ⌈2 * T⌉₊ ≤ ⌈2 * T⌉₊ + 2)
            (le_trans (le_max_right _ _) hH)
  have hHpos : (0:ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hlog0 : 0 ≤ Real.log (H : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ H))
  have hbound := hx₀ (H : ℝ) hHx₀
  simp only [id, Real.norm_eq_abs, abs_pow, abs_of_nonneg hlog0, abs_of_pos hHpos] at hbound
  -- `T·C^m·(log H)^{mB} ≤ H/2`
  have hmain : T * (C ^ m * Real.log (H : ℝ) ^ (m * B)) ≤ (H : ℝ) / 2 := by
    have h1 : Real.log (H : ℝ) ^ (m * B) ≤ (H : ℝ) / (2 * T * C ^ m) := by
      rw [div_eq_mul_one_div, mul_comm (H : ℝ)]
      exact hbound
    have hpos : (0:ℝ) < 2 * T * C ^ m := by positivity
    rw [le_div_iff₀ hpos] at h1
    have : T * (C ^ m * Real.log (H : ℝ) ^ (m * B)) * 2 ≤ (H : ℝ) := by
      calc T * (C ^ m * Real.log (H : ℝ) ^ (m * B)) * 2
          = Real.log (H : ℝ) ^ (m * B) * (2 * T * C ^ m) := by ring
        _ ≤ (H : ℝ) := h1
    linarith
  have hQ0 : 0 ≤ C * Real.log H ^ B := by positivity
  calc T * (max (C * Real.log H ^ B) 1) ^ m
      ≤ T * ((C * Real.log H ^ B) ^ m + 1) :=
        mul_le_mul_of_nonneg_left (max_one_pow_le_pow_add_one _ hQ0 m) hT.le
    _ = T * (C ^ m * Real.log (H : ℝ) ^ (m * B)) + T := by
        rw [mul_pow, ← pow_mul, mul_comm B m]
        ring
    _ ≤ (H : ℝ) / 2 + (H : ℝ) / 2 := add_le_add hmain (by linarith)
    _ = H := by ring

/-- `⌊t⌋₊ ≥ t/2` for `t ≥ 1` (Track R, R7-C0). -/
theorem half_le_floor (t : ℝ) (ht : 1 ≤ t) : t / 2 ≤ (⌊t⌋₊ : ℝ) := by
  rcases le_or_gt 2 t with h2 | h2
  · have := Nat.lt_floor_add_one t
    linarith
  · have h1 : (1:ℝ) ≤ (⌊t⌋₊ : ℝ) := by
      exact_mod_cast Nat.le_floor (by simpa using ht)
    linarith

end MoltResearch
