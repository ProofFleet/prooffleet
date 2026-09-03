import MoltResearch.Discrepancy.WindowAssembly
import MoltResearch.Discrepancy.BandSchedule

/-!
# The level polynomials' sizes, in schedule terms (Track R, A2-III, M-3)

`BandCapstone.setIntegral_norm_sq_level_sum_of_prev_large_le` and
`BandSchedule.levelJ_le_budget` are stated with two abstract sizes: `small v`,
a pointwise bound on the current level's cell polynomial on `G`, and `large`, a
pointwise lower bound on the previous level's prime polynomial there.
`WindowTK.band_energy_level_le_of_prev_large` records what the schedule supplies
for them — `small v = e^{−αv/(2N)}` and `large = e^{−βr/(2N_prev)}`, the
`e`-adic ladder factors at the cell index — and leaves the instantiation to the
consumer.  This module is that instantiation, and it is the fourth of the
schedule's abstract quantities to be bound after the cell mass, the level total
(`PrimeMassCell`) and the cell count (`BandSchedule.cellCount_le`).

**The finding: the level-`j` total smallness needs no new schedule input.**
`levelJ_le_budget` consumes the sizes through `S₁ = ∑_v (small v)²`, and at the
schedule's `small` that sum is a geometric series in the `e`-adic index at rate
`2α` — *the same series, at the same rate, from the same level bottom* that the
level-one leg already pays as its smallness gain.  So
`levelSmallness_total_le`'s right-hand side is literally the middle factor of
`levelOne_le_budget`'s `hfitP`, and a schedule that affords the level-one leg
affords this one on the same arithmetic.  Nothing here is new analysis; both
lemmas are the `e`-adic index bounds of S-cal-2 read at the level-`j` seam.

Note the direction each size is bounded in.  `small` enters `levelJ_le_budget`
multiplied, so it needs an **upper** bound and `eadic_level_bot_exp_le` supplies
it from the level's bottom `P`.  `large` enters *divided* — the level-`j`
estimate pays `1/large^{2ℓ}` for inserting `ℓ` copies of the previous level's
polynomial — so it needs a **lower** bound, and that is
`eadic_level_top_exp_le` read as a reciprocal, priced by the previous level's
top `Q`.
-/

namespace MoltResearch

open Finset

/-- **The total smallness of a level** (Track R, A2-III, M-3).

`∑_{v₀ ≤ v ≤ v₁} (e^{−αv/(2N)})² ≤ P^{−2α}·e^{2α/(2N)}·(2N/(2α) + 1)`, the
`S₁` input of `BandSchedule.levelJ_le_budget` at the schedule's smallness
`small v = e^{−αv/(2N)}`.

Two in-tree pieces and no new content: `sum_exp_neg_index_le` sums the
geometric series over the `e`-adic index range, and `eadic_level_bot_exp_le`
converts its leading term `e^{−2αv₀/(2N)}` into the prime form `P^{−2α}` the
schedule states its constraints in.  The hypothesis `hbot` is the same
`2N log P − 1 ≤ v₀` that `levelOne_le_budget` and `cellCount_le` already take,
so a consumer that has priced either has discharged it.

The right-hand side is exactly the smallness factor of `levelOne_le_budget`'s
`hfitP`: the level-`j` leg's total smallness is the level-one leg's geometric
gain, not a new demand on the schedule. -/
theorem levelSmallness_total_le (N v₀ v₁ : ℕ) (P α : ℝ) (hN : 0 < N)
    (hα : 0 < α) (hP0 : 0 < P)
    (hbot : 2 * (N : ℝ) * Real.log P - 1 ≤ (v₀ : ℝ)) :
    ∑ v ∈ Finset.Ico v₀ (v₁ + 1),
        (Real.exp (-(α * (v : ℝ) / ((2 * N : ℕ) : ℝ)))) ^ 2
      ≤ P ^ (-(2 * α)) * Real.exp (2 * α / ((2 * N : ℕ) : ℝ))
          * (((2 * N : ℕ) : ℝ) / (2 * α) + 1) := by
  have h2N : 0 < 2 * N := by omega
  have hgeo0 : (0 : ℝ) ≤ ((2 * N : ℕ) : ℝ) / (2 * α) + 1 := by positivity
  -- the square of the ladder factor is the ladder factor at rate `2α`
  have hsq : ∀ v : ℕ, (Real.exp (-(α * (v : ℝ) / ((2 * N : ℕ) : ℝ)))) ^ 2
      = Real.exp (-(2 * α * (v : ℝ) / ((2 * N : ℕ) : ℝ))) := by
    intro v
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hsum := ExpSums.sum_exp_neg_index_le (2 * α) (by linarith) (2 * N) h2N v₀ v₁
  have hbotfac := eadic_level_bot_exp_le N v₀ P (2 * α) hN (by linarith) hP0 hbot
  calc ∑ v ∈ Finset.Ico v₀ (v₁ + 1),
        (Real.exp (-(α * (v : ℝ) / ((2 * N : ℕ) : ℝ)))) ^ 2
      = ∑ v ∈ Finset.Ico v₀ (v₁ + 1),
          Real.exp (-(2 * α * (v : ℝ) / ((2 * N : ℕ) : ℝ))) :=
        Finset.sum_congr rfl fun v _ => hsq v
    _ ≤ Real.exp (-(2 * α * (v₀ : ℝ) / ((2 * N : ℕ) : ℝ)))
          * (((2 * N : ℕ) : ℝ) / (2 * α) + 1) := hsum
    _ ≤ P ^ (-(2 * α)) * Real.exp (2 * α / ((2 * N : ℕ) : ℝ))
          * (((2 * N : ℕ) : ℝ) / (2 * α) + 1) :=
        mul_le_mul_of_nonneg_right hbotfac hgeo0

/-- **The largeness of the previous level, in prime terms** (Track R, A2-III,
M-3).

`e^{−βr/(2N)} ≥ Q^{−β}·e^{−β/(2N)}` for any cell index `r` of a level topping
out at primes `≤ Q`: the `large` input of
`BandCapstone.setIntegral_norm_sq_level_sum_of_prev_large_le`, bounded **below**
because the level-`j` estimate divides by it.

This is `eadic_level_top_exp_le` read as a reciprocal, and the one place where
the reciprocal reading matters: `1/large^{2ℓ}` is a loss growing like `Q^{2βℓ}`,
so the previous level's *top* is what prices the moment the level-`j` leg has
to afford — the smallness is priced by this level's *bottom*
(`levelSmallness_total_le`) and the two ends of the ladder enter through
different lemmas.

Combined with `levelJ_moment_le`'s criterion `2ℓ²σ < large²`, the bound here
turns that criterion into the schedule-level statement `2ℓ²σ < Q^{−2β}e^{−β/N}`,
i.e. `ℓ ≲ Q^{−β}/√σ` — the `ℓ_{j,r}` of constraint `S5`. -/
theorem levelLargeness_ge (N r v₁ : ℕ) (Q β : ℝ) (hN : 0 < N) (hβ : 0 ≤ β)
    (hQ0 : 0 < Q) (hr : r ≤ v₁)
    (htop : (v₁ : ℝ) ≤ 2 * (N : ℝ) * Real.log Q) :
    Q ^ (-β) * Real.exp (-(β / ((2 * N : ℕ) : ℝ)))
      ≤ Real.exp (-(β * (r : ℝ) / ((2 * N : ℕ) : ℝ))) := by
  have h2N : (0 : ℝ) < ((2 * N : ℕ) : ℝ) := by
    have : 0 < 2 * N := by omega
    exact_mod_cast this
  have hrv : (r : ℝ) ≤ (v₁ : ℝ) + 1 := by
    have : (r : ℝ) ≤ (v₁ : ℝ) := by exact_mod_cast hr
    linarith
  -- the ladder factor at `r` is at most the one at the top of the level …
  have hmono : Real.exp (β * (r : ℝ) / ((2 * N : ℕ) : ℝ))
      ≤ Real.exp (β * ((v₁ : ℝ) + 1) / ((2 * N : ℕ) : ℝ)) := by
    refine Real.exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_left hrv hβ
    exact div_le_div_of_nonneg_right this h2N.le
  -- … which the schedule prices by `Q^β`
  have hchain : Real.exp (β * (r : ℝ) / ((2 * N : ℕ) : ℝ))
      ≤ Q ^ β * Real.exp (β / ((2 * N : ℕ) : ℝ)) :=
    hmono.trans (eadic_level_top_exp_le N v₁ Q β hN hβ hQ0 htop)
  have hrw : Q ^ (-β) * Real.exp (-(β / ((2 * N : ℕ) : ℝ)))
      = 1 / (Q ^ β * Real.exp (β / ((2 * N : ℕ) : ℝ))) := by
    rw [Real.rpow_neg hQ0.le, Real.exp_neg, ← mul_inv, inv_eq_one_div]
  have hrw' : Real.exp (-(β * (r : ℝ) / ((2 * N : ℕ) : ℝ)))
      = 1 / Real.exp (β * (r : ℝ) / ((2 * N : ℕ) : ℝ)) := by
    rw [Real.exp_neg, inv_eq_one_div]
  rw [hrw, hrw']
  exact one_div_le_one_div_of_le (Real.exp_pos _) hchain

/-- **The level-`j` leg meets its share, in schedule terms** (Track R, A2-III,
M-9).

`BandSchedule.levelJ_le_budget` takes the cell count `#I` and the total
smallness `S₁` abstractly; this is that lemma with both supplied — `#I` by
`cellCount_le` (M-2) and `S₁` by `levelSmallness_total_le` (M-3).  What is left
of the leg's condition is `hfit`, an inequality in the level's endpoints `P`,
`Q`, the `e`-adic resolution `N`, the decay rate `α`, the previous level's
largeness and the moment factor — schedule parameters only, with nothing about
the cell decomposition surviving.

This is the level-`j` counterpart of what M-8 did for the `𝒰` leg, and it needs
no new import: `levelJ_le_budget` and `cellCount_le` are both in `BandSchedule`
and `levelSmallness_total_le` is local.

**The two hypotheses `htop` and `hbot` are shared between the two inputs, and
that is why the composition is free.**  `cellCount_le` needs exactly
`v₁ ≤ 2N log Q` and `2N log P − 1 ≤ v₀`; `levelSmallness_total_le` needs the
second of them, and `levelOne_le_budget` needs both.  So a schedule that has
priced *any* of the three legs has already discharged everything this one
asks about the `e`-adic index range. -/
theorem levelJ_le_budget_eadic (N v₀ v₁ ℓ : ℕ) (P Q α large E M c₃ ε ρ κ : ℝ)
    (hN : 0 < N) (hα : 0 < α) (hP0 : 0 < P) (hPQ : P ≤ Q)
    (hlarge : 0 < large) (hE0 : 0 ≤ E) (hM0 : 0 ≤ M)
    (htop : (v₁ : ℝ) ≤ 2 * (N : ℝ) * Real.log Q)
    (hbot : 2 * (N : ℝ) * Real.log P - 1 ≤ (v₀ : ℝ))
    (hfit : (2 * (N : ℝ) * (Real.log Q - Real.log P) + 2)
        * ((P ^ (-(2 * α)) * Real.exp (2 * α / ((2 * N : ℕ) : ℝ))
              * (((2 * N : ℕ) : ℝ) / (2 * α) + 1))
            * (E * (M / large ^ (2 * ℓ))))
      ≤ κ * bandBudget c₃ ε ρ) :
    ((Finset.Ico v₀ (v₁ + 1)).card : ℝ)
        * ∑ v ∈ Finset.Ico v₀ (v₁ + 1),
            (Real.exp (-(α * (v : ℝ) / ((2 * N : ℕ) : ℝ)))) ^ 2 / large ^ (2 * ℓ)
              * (E * M)
      ≤ κ * bandBudget c₃ ε ρ := by
  have hS₁0 : (0 : ℝ) ≤ P ^ (-(2 * α)) * Real.exp (2 * α / ((2 * N : ℕ) : ℝ))
      * (((2 * N : ℕ) : ℝ) / (2 * α) + 1) := by
    have h1 : (0 : ℝ) ≤ P ^ (-(2 * α)) := (Real.rpow_pos_of_pos hP0 _).le
    have h2 : (0 : ℝ) ≤ (((2 * N : ℕ) : ℝ) / (2 * α) + 1) := by positivity
    have h3 : (0 : ℝ) < Real.exp (2 * α / ((2 * N : ℕ) : ℝ)) := Real.exp_pos _
    positivity
  have hX0 : (0 : ℝ) ≤ (P ^ (-(2 * α)) * Real.exp (2 * α / ((2 * N : ℕ) : ℝ))
        * (((2 * N : ℕ) : ℝ) / (2 * α) + 1)) * (E * (M / large ^ (2 * ℓ))) := by
    have hlp : (0 : ℝ) < large ^ (2 * ℓ) := by positivity
    exact mul_nonneg hS₁0 (mul_nonneg hE0 (div_nonneg hM0 hlp.le))
  refine levelJ_le_budget (Finset.Ico v₀ (v₁ + 1)) ℓ
    (fun v => Real.exp (-(α * (v : ℝ) / ((2 * N : ℕ) : ℝ)))) large E M
    (P ^ (-(2 * α)) * Real.exp (2 * α / ((2 * N : ℕ) : ℝ))
      * (((2 * N : ℕ) : ℝ) / (2 * α) + 1))
    c₃ ε ρ κ hlarge hE0 hM0 (levelSmallness_total_le N v₀ v₁ P α hN hα hP0 hbot) ?_
  exact le_trans
    (mul_le_mul_of_nonneg_right (cellCount_le N v₀ v₁ P Q hP0 hPQ htop hbot) hX0)
    hfit

end MoltResearch
