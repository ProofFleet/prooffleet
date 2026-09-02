import Mathlib

/-!
# The band schedule (Track R, `[mrt]` A.2, §4)

The `[mrt]` A.2 inner-band estimate is assembled from legs that each produce an
explicit real bound; `MoltResearch.Discrepancy.BandCapstone` composes them.  What
remains after that composition is *numerical*: each leg's bound must be shown to
fit inside its share of the band's slice budget

  `𝔅 = c₃ ε² (Δ/A) / 8`     (design report §4.1),

and the schedule `S1–S7` of §4.4 is exactly a choice of parameters making every
leg fit at once.  This module is that arithmetic.  It is deliberately free of
measure theory and of every in-tree dependency: each statement is an inequality
between real expressions, whose left-hand side is the *literal* right-hand side
of a merged band lemma, so a consumer composes with `le_trans` and nothing else.

**Why the conditions are hypotheses.**  §4.3 does not prove the legs fit; it
derives, leg by leg, the condition under which they do (`N_j ≥ C/ε³`,
`P₁ ≥ C/ε³`, a lower bound on `γ`, …).  Each lemma here takes that condition in
explicit form and concludes the fit.  Discharging all of them simultaneously
from a concrete `W`-schedule is a separate, self-contained computation.

## The collar leg (§4.3(a)), and one correction to the report

The report prices a collar as `e^π(T/A + 2)·Σ_{collar} 1/n ≈ 3e^π/N_j`, compares
that to `𝔅`, and reads off `N_j ≥ C/ε³` with an absolute `C`.  That is the cost
of **one** collar.  The quantity the tree actually produces — the error half of
`setIntegral_norm_sq_cell_prime_block_le` — is the assembled one, and it carries
two factors the report's estimate does not:

* the Cauchy–Schwarz factor `#I` over cells (the cell contributions are not
  orthogonal on `G`), and
* the weight `∑_v (∑_{p ∈ 𝒞_v} 1/p)²`, from the outer prime mass of each cell.

Both are exposed here as parameters rather than absorbed, because their product
is *not* absolutely bounded: `#I` grows linearly in the e-adic resolution `N`,
which cancels the `1/N` the collar ratio buys.  What saves the leg is that the
second factor is small — each `e`-adic cell has multiplicative width `e^{1/(2N)}`,
so `∑_v σ_v² ≤ (max_v σ_v)·∑_v σ_v` decays in `N` as well.  The honest condition
is therefore `N ≥ 64·#I·X·S₂/(κc₃ε³)` with `X` and `S₂` as below, not
`N ≥ C/ε³` at absolute `C`.
-/

namespace MoltResearch

/-- **The band's share of the slice budget** (Track R, A2-III, §4.1).

For the *normalised* integrand `F(ξ) = ∑ (g m/m)·e(−ξ log m)`, the prior slice
arithmetic gives the band `∫_band |F|² ≤ c₃ε²(Δ/A)/8`.  The third argument is
the ratio `ρ = Δ/A`; keeping it as one parameter is what makes the `Δ/A`
cancellation of §4.1 visible — the trivial bound carries the same factor, so the
requirement is a saving of `ε²` and nothing else. -/
noncomputable def bandBudget (c₃ ε ρ : ℝ) : ℝ := c₃ * ε ^ 2 * ρ / 8

/-- The budget is nonnegative whenever `c₃` and the ratio `ρ = Δ/A` are. -/
theorem bandBudget_nonneg (c₃ ε ρ : ℝ) (hc₃ : 0 ≤ c₃) (hρ : 0 ≤ ρ) :
    0 ≤ bandBudget c₃ ε ρ := by
  unfold bandBudget
  positivity

/-- **The collar ratio** (Track R, A2-III, S-cal-1): a block of length `⌊A/p⌋`
has collar `⌊A/(Np)⌋ + 1`, and once the block is at least `N` long that collar
is at most `2/N` of it.

This is the `1/N_j` of design report §4.3(a), and the factor `2` is `ℕ`-division
friction — the `+1` is a whole extra term when the block is short, so the naive
`1/N` is false and `2/N` is the first true bound.  The hypothesis `N ≤ ⌊A/p⌋` is
exactly "the block is long enough to have `N` collars", which is `hLA`/`hLB` of
`setIntegral_norm_sq_cell_prime_block_le` in a usable form. -/
theorem collar_ratio_le (A N p : ℕ) (hN : 1 ≤ N) (hNA : N ≤ A / p) :
    ((A / (N * p) + 1 : ℕ) : ℝ) / ((A / p : ℕ) : ℝ) ≤ 2 / (N : ℝ) := by
  have hdiv : A / (N * p) = A / p / N := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm p N]
  have ha : 1 ≤ A / p := le_trans hN hNA
  have ha0 : (0 : ℝ) < ((A / p : ℕ) : ℝ) := by exact_mod_cast ha
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have key : (A / (N * p) + 1) * N ≤ 2 * (A / p) := by
    rw [hdiv]
    have h1 : A / p / N * N ≤ A / p := Nat.div_mul_le_self _ _
    calc (A / p / N + 1) * N = A / p / N * N + N := by ring
      _ ≤ A / p + A / p := Nat.add_le_add h1 hNA
      _ = 2 * (A / p) := by ring
  rw [div_le_div_iff₀ ha0 hN0]
  exact_mod_cast key

/-- **The per-prime collar cost, in schedule form** (Track R, A2-III, S-cal-1).

The collar term of `setIntegral_norm_sq_cell_prime_block_le` is
`e^π(T/⌊A/p⌋ + 4)·(⌊A/(Np)⌋+1)/⌊A/p⌋` at each prime `p` of the cell.  Both
factors are priced by the schedule: the quotient scale `T/⌊A/p⌋` by the largest
prime in play, and the ratio by `collar_ratio_le`.

`2*p ≤ A` is the same `ℕ`-division hypothesis `quotient_scale_le_cell_scale`
needs, and for the same reason — `⌊A/p⌋` is only comparable to `A/p` once the
block has at least two terms. -/
theorem collar_cost_le (A N p : ℕ) (T Qmax : ℝ) (hN : 1 ≤ N) (hp : 1 ≤ p)
    (hpA : 2 * p ≤ A) (hNA : N ≤ A / p) (hT : 0 ≤ T) (hQ : (p : ℝ) ≤ Qmax) :
    Real.exp Real.pi * (T / ((A / p : ℕ) : ℝ) + 4)
        * (((A / (N * p) + 1 : ℕ) : ℝ) / ((A / p : ℕ) : ℝ))
      ≤ Real.exp Real.pi * (2 * T * Qmax / (A : ℝ) + 4) * (2 / (N : ℝ)) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hA0 : (0 : ℝ) < (A : ℝ) := by
    have : 0 < A := by omega
    exact_mod_cast this
  have ha : 1 ≤ A / p := le_trans hN hNA
  have ha0 : (0 : ℝ) < ((A / p : ℕ) : ℝ) := by exact_mod_cast ha
  have hf1 : (1 : ℝ) ≤ ((A / p : ℕ) : ℝ) := by exact_mod_cast ha
  -- `⌊A/p⌋ ≥ A/(2p)`: the same `ℕ`-division step as `quotient_scale_le_cell_scale`
  have hdm : (p : ℝ) * ((A / p : ℕ) : ℝ) + ((A % p : ℕ) : ℝ) = (A : ℝ) := by
    exact_mod_cast Nat.div_add_mod A p
  have hmod : ((A % p : ℕ) : ℝ) < (p : ℝ) := by
    exact_mod_cast Nat.mod_lt A (by omega : 0 < p)
  have hfloor : (A : ℝ) / (2 * (p : ℝ)) ≤ ((A / p : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hdm, hmod, hp0, hf1]
  have hscale : T / ((A / p : ℕ) : ℝ) ≤ 2 * T * Qmax / (A : ℝ) := by
    calc T / ((A / p : ℕ) : ℝ) ≤ T / ((A : ℝ) / (2 * (p : ℝ))) := by gcongr
      _ = 2 * T * (p : ℝ) / (A : ℝ) := by field_simp
      _ ≤ 2 * T * Qmax / (A : ℝ) := by gcongr
  have hratio := collar_ratio_le A N p hN hNA
  have hnum0 : (0 : ℝ) ≤ ((A / (N * p) + 1 : ℕ) : ℝ) / ((A / p : ℕ) : ℝ) := by
    positivity
  have hQ0 : (0 : ℝ) ≤ Qmax := le_trans hp0.le hQ
  have hdiv0 : (0 : ℝ) ≤ 2 * T * Qmax / (A : ℝ) :=
    div_nonneg (mul_nonneg (by linarith) hQ0) hA0.le
  have hb0 : (0 : ℝ) ≤ Real.exp Real.pi * (2 * T * Qmax / (A : ℝ) + 4) :=
    mul_nonneg (Real.exp_pos _).le (by linarith)
  have hleft : Real.exp Real.pi * (T / ((A / p : ℕ) : ℝ) + 4)
      ≤ Real.exp Real.pi * (2 * T * Qmax / (A : ℝ) + 4) :=
    mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  exact mul_le_mul hleft hratio hnum0 hb0

/-- **The assembled collar error, reduced** (Track R, A2-III, S-cal-1).

The error half of `setIntegral_norm_sq_cell_prime_block_le`, with each per-prime
collar cost priced uniformly by `X` and the outer prime mass collected into
`S₂ = ∑_v (∑_{p ∈ 𝒞_v} 1/p)²`.  The two costs `cA`, `cB` are abstract: the
consumer instantiates them at the `A`- and `B`-endpoint collars, and
`collar_cost_le` supplies both bounds from one schedule condition.

The `8` is `2` (the `L²` triangle of VI-1c-4) times `2 + 2` (the two endpoint
collars).  The factor `#I` is the Cauchy–Schwarz over cells and does **not**
cancel — see the module docstring. -/
theorem collar_error_le (I : Finset ℕ) (C : ℕ → Finset ℕ) (cA cB : ℕ → ℝ)
    (X S₂ : ℝ) (hX0 : 0 ≤ X)
    (hA : ∀ v ∈ I, ∀ p ∈ C v, cA p ≤ X) (hB : ∀ v ∈ I, ∀ p ∈ C v, cB p ≤ X)
    (hS₂ : ∑ v ∈ I, (∑ p ∈ C v, (1 : ℝ) / (p : ℝ)) ^ 2 ≤ S₂) :
    2 * ((I.card : ℝ)
          * ∑ v ∈ I, (∑ p ∈ C v, (1 : ℝ) / (p : ℝ))
              * ∑ p ∈ C v, ((1 : ℝ) / (p : ℝ)) * (2 * cA p + 2 * cB p))
      ≤ 8 * (I.card : ℝ) * X * S₂ := by
  classical
  have hσ0 : ∀ v : ℕ, (0 : ℝ) ≤ ∑ p ∈ C v, (1 : ℝ) / (p : ℝ) :=
    fun v => Finset.sum_nonneg fun p _ => by positivity
  -- each cell contributes at most `4X σ_v²`
  have hcell : ∀ v ∈ I, (∑ p ∈ C v, (1 : ℝ) / (p : ℝ))
      * ∑ p ∈ C v, ((1 : ℝ) / (p : ℝ)) * (2 * cA p + 2 * cB p)
      ≤ 4 * X * (∑ p ∈ C v, (1 : ℝ) / (p : ℝ)) ^ 2 := by
    intro v hv
    have hinner : ∑ p ∈ C v, ((1 : ℝ) / (p : ℝ)) * (2 * cA p + 2 * cB p)
        ≤ 4 * X * ∑ p ∈ C v, (1 : ℝ) / (p : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun p hp => ?_
      have h1 := hA v hv p hp
      have h2 := hB v hv p hp
      have hp0 : (0 : ℝ) ≤ (1 : ℝ) / (p : ℝ) := by positivity
      nlinarith [hp0, h1, h2]
    calc (∑ p ∈ C v, (1 : ℝ) / (p : ℝ))
            * ∑ p ∈ C v, ((1 : ℝ) / (p : ℝ)) * (2 * cA p + 2 * cB p)
        ≤ (∑ p ∈ C v, (1 : ℝ) / (p : ℝ)) * (4 * X * ∑ p ∈ C v, (1 : ℝ) / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hinner (hσ0 v)
      _ = 4 * X * (∑ p ∈ C v, (1 : ℝ) / (p : ℝ)) ^ 2 := by ring
  have hsum : ∑ v ∈ I, (∑ p ∈ C v, (1 : ℝ) / (p : ℝ))
      * ∑ p ∈ C v, ((1 : ℝ) / (p : ℝ)) * (2 * cA p + 2 * cB p)
      ≤ 4 * X * S₂ := by
    calc ∑ v ∈ I, (∑ p ∈ C v, (1 : ℝ) / (p : ℝ))
            * ∑ p ∈ C v, ((1 : ℝ) / (p : ℝ)) * (2 * cA p + 2 * cB p)
        ≤ ∑ v ∈ I, 4 * X * (∑ p ∈ C v, (1 : ℝ) / (p : ℝ)) ^ 2 :=
          Finset.sum_le_sum hcell
      _ = 4 * X * ∑ v ∈ I, (∑ p ∈ C v, (1 : ℝ) / (p : ℝ)) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ 4 * X * S₂ := by
          have : (0 : ℝ) ≤ 4 * X := by linarith
          exact mul_le_mul_of_nonneg_left hS₂ this
  have hcard : (0 : ℝ) ≤ (I.card : ℝ) := Nat.cast_nonneg _
  nlinarith [hsum, hcard]

/-- **The collar leg meets its share of the budget** (Track R, A2-III, S-cal-1;
design report §4.3(a), constraint `S3`).

`hfit` is the schedule condition in explicit form.  Instantiated with the
`X = e^π(2TQ/A + 4)·(2/N)` of `collar_cost_le` it reads

  `N ≥ 128·e^π·#I·(2TQ/A + 4)·S₂ / (κ c₃ ε³)`,

which is §4.3(a)'s `N_j ≥ C/ε³` with the constant made honest — see the module
docstring for why `C` cannot be taken absolute.

`hρ : ε ≤ Δ/A` is `S1`'s `s ≤ εA/2` in the form the budget uses; it is the one
place the slice geometry enters, and it is what turns the `ε²` of `𝔅` into the
`ε³` the collar must beat. -/
theorem collar_error_le_budget (I : Finset ℕ) (C : ℕ → Finset ℕ) (cA cB : ℕ → ℝ)
    (X S₂ c₃ ε ρ κ : ℝ) (hX0 : 0 ≤ X)
    (hA : ∀ v ∈ I, ∀ p ∈ C v, cA p ≤ X) (hB : ∀ v ∈ I, ∀ p ∈ C v, cB p ≤ X)
    (hS₂ : ∑ v ∈ I, (∑ p ∈ C v, (1 : ℝ) / (p : ℝ)) ^ 2 ≤ S₂)
    (hκc : 0 ≤ κ * c₃) (hρ : ε ≤ ρ)
    (hfit : 64 * (I.card : ℝ) * X * S₂ ≤ κ * c₃ * ε ^ 3) :
    2 * ((I.card : ℝ)
          * ∑ v ∈ I, (∑ p ∈ C v, (1 : ℝ) / (p : ℝ))
              * ∑ p ∈ C v, ((1 : ℝ) / (p : ℝ)) * (2 * cA p + 2 * cB p))
      ≤ κ * bandBudget c₃ ε ρ := by
  have hred := collar_error_le I C cA cB X S₂ hX0 hA hB hS₂
  have hstep : κ * c₃ * ε ^ 3 ≤ κ * c₃ * ε ^ 2 * ρ := by
    have h0 : (0 : ℝ) ≤ κ * c₃ * ε ^ 2 := mul_nonneg hκc (sq_nonneg ε)
    calc κ * c₃ * ε ^ 3 = κ * c₃ * ε ^ 2 * ε := by ring
      _ ≤ κ * c₃ * ε ^ 2 * ρ := mul_le_mul_of_nonneg_left hρ h0
  unfold bandBudget
  have hshape : κ * (c₃ * ε ^ 2 * ρ / 8) = κ * c₃ * ε ^ 2 * ρ / 8 := by ring
  rw [hshape]
  linarith [hred, hfit, hstep]

/-! ## The level-one leg (§4.3(d)) -/

/-- **The top of an `e`-adic level range, in prime terms** (Track R, A2-III,
S-cal-2).

`band_energy_level_one_le` prices the mean value error by
`exp((1−2α)(v₁+1)/(2N))`, where `v₁` is the top cell index of the level.  The
schedule speaks of primes, not indices.  Since `v = ⌊2N log p⌋`, a level topping
out at primes `≤ Q` has `v₁ ≤ 2N log Q`, and the factor is at most `Q^{1−2α}`
times one `e`-adic ladder step.

This is the step §4.3(d) takes silently when it writes the error term as
`Q₁^{1/2+3η}`: with `2α₁ = 1/2 − 3η` the exponent `1 − 2α₁` is exactly
`1/2 + 3η`. -/
theorem eadic_level_top_exp_le (N v₁ : ℕ) (Q β : ℝ) (hN : 0 < N) (hβ : 0 ≤ β)
    (hQ0 : 0 < Q) (htop : (v₁ : ℝ) ≤ 2 * (N : ℝ) * Real.log Q) :
    Real.exp (β * ((v₁ : ℝ) + 1) / ((2 * N : ℕ) : ℝ))
      ≤ Q ^ β * Real.exp (β / ((2 * N : ℕ) : ℝ)) := by
  have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hd : (0 : ℝ) < 2 * (N : ℝ) := by linarith
  rw [Real.rpow_def_of_pos hQ0, ← Real.exp_add, hcast]
  refine Real.exp_le_exp.mpr ?_
  have hv : (v₁ : ℝ) / (2 * (N : ℝ)) ≤ Real.log Q := by
    rw [div_le_iff₀ hd]
    linarith [htop]
  have hmul : β * ((v₁ : ℝ) / (2 * (N : ℝ))) ≤ β * Real.log Q :=
    mul_le_mul_of_nonneg_left hv hβ
  have hsplit : β * ((v₁ : ℝ) + 1) / (2 * (N : ℝ))
      = β * ((v₁ : ℝ) / (2 * (N : ℝ))) + β / (2 * (N : ℝ)) := by
    field_simp
  rw [hsplit]
  linarith [hmul]

/-- **The bottom of an `e`-adic level range, in prime terms** (Track R, A2-III,
S-cal-2).

The companion of `eadic_level_top_exp_le` for the smallness factor
`exp(−2αv₀/(2N))`.  A level starting at primes `> P` has `v₀ ≥ 2N log P − 1` —
the `−1` is the one ladder step a floor loses — and the factor is at most
`P^{−2α}` times that step.

This is §4.3(d)'s `P₁^{−1/2+3η}`: with `2α₁ = 1/2 − 3η`, `−2α₁ = −1/2 + 3η`. -/
theorem eadic_level_bot_exp_le (N v₀ : ℕ) (P β : ℝ) (hN : 0 < N) (hβ : 0 ≤ β)
    (hP0 : 0 < P) (hbot : 2 * (N : ℝ) * Real.log P - 1 ≤ (v₀ : ℝ)) :
    Real.exp (-(β * (v₀ : ℝ) / ((2 * N : ℕ) : ℝ)))
      ≤ P ^ (-β) * Real.exp (β / ((2 * N : ℕ) : ℝ)) := by
  have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hd : (0 : ℝ) < 2 * (N : ℝ) := by linarith
  rw [Real.rpow_def_of_pos hP0, ← Real.exp_add, hcast]
  refine Real.exp_le_exp.mpr ?_
  have hv : Real.log P - 1 / (2 * (N : ℝ)) ≤ (v₀ : ℝ) / (2 * (N : ℝ)) := by
    rw [le_div_iff₀ hd]
    have : (Real.log P - 1 / (2 * (N : ℝ))) * (2 * (N : ℝ))
        = 2 * (N : ℝ) * Real.log P - 1 := by field_simp
    rw [this]
    exact hbot
  have hmul : β * (Real.log P - 1 / (2 * (N : ℝ)))
      ≤ β * ((v₀ : ℝ) / (2 * (N : ℝ))) := mul_le_mul_of_nonneg_left hv hβ
  have hsplitL : -(β * (v₀ : ℝ) / (2 * (N : ℝ)))
      = -(β * ((v₀ : ℝ) / (2 * (N : ℝ)))) := by ring
  have hsplitR : Real.log P * -β + β / (2 * (N : ℝ))
      = -(β * (Real.log P - 1 / (2 * (N : ℝ)))) := by field_simp; ring
  rw [hsplitL, hsplitR]
  linarith [hmul]

/-- **The level-one leg meets its share of the budget** (Track R, A2-III,
S-cal-2; design report §4.3(d)).

The closed form of `band_energy_level_one_le` is a sum of two terms — the mean
value error, growing at rate `1 − 2α` up the level range, and the smallness
gain, decaying at rate `2α` from its bottom — and §4.3(d) imposes one condition
on each.  Both are taken here in the prime form supplied by
`eadic_level_top_exp_le` and `eadic_level_bot_exp_le`, which is the form the
schedule states them in (`Q₁^{1/2+3η}` and `P₁^{−1/2+3η}`).

`V` is left as a real rather than `#(Ico v₀ (v₁+1))`: it is the Cauchy–Schwarz
factor over levels, the consumer already has it as a cardinality, and keeping it
abstract is what lets one lemma serve both the bare level-one estimate and
VI-1c-4's main half.

Unlike the collar leg, §4.3(d) needs no correction — the report's `N₁² log Q₁`
prefactor is exactly `V ≍ 2N log(Q₁/P₁)` against the `2N/(1−2α)` and `2N/(2α)`
of the geometric sums. -/
theorem levelOne_le_budget (N R : ℕ) (V T A C P Q α c₃ ε ρ κ : ℝ)
    (hN : 0 < N) (hV0 : 0 ≤ V) (hC0 : 0 ≤ C) (hT0 : 0 ≤ T) (hA0 : 0 < A)
    (hα : 0 < α) (hα2 : 2 * α < 1) (hP0 : 0 < P) (hQ0 : 0 < Q)
    (v₀ v₁ : ℕ)
    (htop : (v₁ : ℝ) ≤ 2 * (N : ℝ) * Real.log Q)
    (hbot : 2 * (N : ℝ) * Real.log P - 1 ≤ (v₀ : ℝ))
    (hfitT : V * (Real.exp Real.pi * C
        * ((2 * T * Real.exp (1 / ((2 * N : ℕ) : ℝ)) / A)
            * (Q ^ (1 - 2 * α) * Real.exp ((1 - 2 * α) / ((2 * N : ℕ) : ℝ)))
            * (((2 * N : ℕ) : ℝ) / (1 - 2 * α) + 1)))
      ≤ κ / 2 * bandBudget c₃ ε ρ)
    (hfitP : V * (Real.exp Real.pi * C
        * (4 * (R : ℝ)
            * (P ^ (-(2 * α)) * Real.exp (2 * α / ((2 * N : ℕ) : ℝ)))
            * (((2 * N : ℕ) : ℝ) / (2 * α) + 1)))
      ≤ κ / 2 * bandBudget c₃ ε ρ) :
    V * (Real.exp Real.pi * C
        * ((2 * T * Real.exp (1 / ((2 * N : ℕ) : ℝ)) / A)
              * Real.exp ((1 - 2 * α) * ((v₁ : ℝ) + 1) / ((2 * N : ℕ) : ℝ))
              * (((2 * N : ℕ) : ℝ) / (1 - 2 * α) + 1)
            + 4 * (R : ℝ) * Real.exp (-(2 * α * (v₀ : ℝ) / ((2 * N : ℕ) : ℝ)))
              * (((2 * N : ℕ) : ℝ) / (2 * α) + 1)))
      ≤ κ * bandBudget c₃ ε ρ := by
  have h2N : (0 : ℝ) < ((2 * N : ℕ) : ℝ) := by
    have : 0 < 2 * N := by omega
    exact_mod_cast this
  have hpre0 : (0 : ℝ) ≤ V * (Real.exp Real.pi * C) :=
    mul_nonneg hV0 (mul_nonneg (Real.exp_pos _).le hC0)
  have hlead0 : (0 : ℝ) ≤ 2 * T * Real.exp (1 / ((2 * N : ℕ) : ℝ)) / A :=
    div_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le) hA0.le
  have hgeo0 : (0 : ℝ) ≤ ((2 * N : ℕ) : ℝ) / (1 - 2 * α) + 1 := by
    have : (0 : ℝ) < 1 - 2 * α := by linarith
    positivity
  have hgeo0' : (0 : ℝ) ≤ ((2 * N : ℕ) : ℝ) / (2 * α) + 1 := by positivity
  have hR0 : (0 : ℝ) ≤ 4 * (R : ℝ) := by positivity
  -- the two `e`-adic factors, priced in prime terms
  have htopfac := eadic_level_top_exp_le N v₁ Q (1 - 2 * α) hN (by linarith) hQ0 htop
  have hbotfac := eadic_level_bot_exp_le N v₀ P (2 * α) hN (by linarith) hP0 hbot
  have hX : (2 * T * Real.exp (1 / ((2 * N : ℕ) : ℝ)) / A)
        * Real.exp ((1 - 2 * α) * ((v₁ : ℝ) + 1) / ((2 * N : ℕ) : ℝ))
        * (((2 * N : ℕ) : ℝ) / (1 - 2 * α) + 1)
      ≤ (2 * T * Real.exp (1 / ((2 * N : ℕ) : ℝ)) / A)
        * (Q ^ (1 - 2 * α) * Real.exp ((1 - 2 * α) / ((2 * N : ℕ) : ℝ)))
        * (((2 * N : ℕ) : ℝ) / (1 - 2 * α) + 1) := by
    gcongr
  have hY : 4 * (R : ℝ) * Real.exp (-(2 * α * (v₀ : ℝ) / ((2 * N : ℕ) : ℝ)))
        * (((2 * N : ℕ) : ℝ) / (2 * α) + 1)
      ≤ 4 * (R : ℝ) * (P ^ (-(2 * α)) * Real.exp (2 * α / ((2 * N : ℕ) : ℝ)))
        * (((2 * N : ℕ) : ℝ) / (2 * α) + 1) := by
    gcongr
  have hsplit : V * (Real.exp Real.pi * C
      * ((2 * T * Real.exp (1 / ((2 * N : ℕ) : ℝ)) / A)
            * Real.exp ((1 - 2 * α) * ((v₁ : ℝ) + 1) / ((2 * N : ℕ) : ℝ))
            * (((2 * N : ℕ) : ℝ) / (1 - 2 * α) + 1)
          + 4 * (R : ℝ) * Real.exp (-(2 * α * (v₀ : ℝ) / ((2 * N : ℕ) : ℝ)))
            * (((2 * N : ℕ) : ℝ) / (2 * α) + 1)))
      ≤ V * (Real.exp Real.pi * C
          * ((2 * T * Real.exp (1 / ((2 * N : ℕ) : ℝ)) / A)
              * (Q ^ (1 - 2 * α) * Real.exp ((1 - 2 * α) / ((2 * N : ℕ) : ℝ)))
              * (((2 * N : ℕ) : ℝ) / (1 - 2 * α) + 1)))
        + V * (Real.exp Real.pi * C
          * (4 * (R : ℝ)
              * (P ^ (-(2 * α)) * Real.exp (2 * α / ((2 * N : ℕ) : ℝ)))
              * (((2 * N : ℕ) : ℝ) / (2 * α) + 1))) := by
    have := mul_le_mul_of_nonneg_left (add_le_add hX hY) hpre0
    calc V * (Real.exp Real.pi * C * (_ + _))
        = V * (Real.exp Real.pi * C) * (_ + _) := by ring
      _ ≤ V * (Real.exp Real.pi * C)
            * ((2 * T * Real.exp (1 / ((2 * N : ℕ) : ℝ)) / A)
                * (Q ^ (1 - 2 * α) * Real.exp ((1 - 2 * α) / ((2 * N : ℕ) : ℝ)))
                * (((2 * N : ℕ) : ℝ) / (1 - 2 * α) + 1)
              + 4 * (R : ℝ)
                * (P ^ (-(2 * α)) * Real.exp (2 * α / ((2 * N : ℕ) : ℝ)))
                * (((2 * N : ℕ) : ℝ) / (2 * α) + 1)) := this
      _ = _ := by ring
  linarith [hsplit, hfitT, hfitP]

/-! ## The level-`j` leg (§4.3(e)) -/

/-- **When the `ℓ`-th moment is affordable** (Track R, A2-III, S-cal-3).

This is the whole mechanism of the level-`j` estimate, isolated.
`band_energy_level_le_of_prev_large` pays `1/large^{2ℓ}` for inserting `ℓ` copies
of the previous level's prime polynomial — a **loss**, since `large < 1` — and
recovers it from the moment of the `ℓ`-fold prime product, which is
`ℓ!²·2^{ℓ+1}(ℓ+1)σ^ℓ` rather than the trivial `(2^{ℓ+1})^{2ℓ}`.  Whether the
level gains or loses is therefore the single question of how

  `ℓ!²·(2σ)^ℓ / large^{2ℓ}`

behaves, and by `ℓ! ≤ ℓ^ℓ` it is at most `(2ℓ²σ/large²)^ℓ`.

Stated with no hypothesis on that ratio, so the gain stays visible: the factor is
`< 1` and *decreasing in `ℓ`* exactly when `2ℓ²σ < large²`, which is what makes
"take `ℓ` as large as the previous level's largeness supports" — the `ℓ_{j,r}` of
schedule constraint `S5` — the right choice rather than a tuning knob.

`σ = ∑_{p ∈ Y} 1/p ≍ 1/log P_j` on a dyadic prime range, so the criterion reads
`ℓ ≲ large·√(log P_j)`. -/
theorem levelJ_moment_le (ℓ : ℕ) (σ large : ℝ) (hσ : 0 ≤ σ) (hL : 0 < large) :
    ((Nat.factorial ℓ : ℝ) ^ 2
        * (((2 ^ (ℓ + 1) : ℕ) : ℝ) * ((ℓ : ℝ) + 1) * σ ^ ℓ)) / large ^ (2 * ℓ)
      ≤ 2 * ((ℓ : ℝ) + 1) * (2 * (ℓ : ℝ) ^ 2 * σ / large ^ 2) ^ ℓ := by
  have hL2 : (0 : ℝ) < large ^ 2 := by positivity
  have hD : (0 : ℝ) < (large ^ 2) ^ ℓ := by positivity
  have hfl : ((Nat.factorial ℓ : ℕ) : ℝ) ≤ (ℓ : ℝ) ^ ℓ := by
    exact_mod_cast Nat.factorial_le_pow ℓ
  have hfl0 : (0 : ℝ) ≤ ((Nat.factorial ℓ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsq : ((Nat.factorial ℓ : ℕ) : ℝ) ^ 2 ≤ ((ℓ : ℝ) ^ 2) ^ ℓ := by
    have h : ((Nat.factorial ℓ : ℕ) : ℝ) ^ 2 ≤ ((ℓ : ℝ) ^ ℓ) ^ 2 := by gcongr
    calc ((Nat.factorial ℓ : ℕ) : ℝ) ^ 2 ≤ ((ℓ : ℝ) ^ ℓ) ^ 2 := h
      _ = ((ℓ : ℝ) ^ 2) ^ ℓ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have h2σ : (0 : ℝ) ≤ (2 * σ) ^ ℓ := pow_nonneg (by linarith) ℓ
  have hcast : (((2 ^ (ℓ + 1) : ℕ)) : ℝ) = 2 * 2 ^ ℓ := by push_cast; ring
  have hnum : ((Nat.factorial ℓ : ℕ) : ℝ) ^ 2 * (2 * σ) ^ ℓ
      ≤ ((ℓ : ℝ) ^ 2) ^ ℓ * (2 * σ) ^ ℓ := by gcongr
  calc ((Nat.factorial ℓ : ℝ) ^ 2
          * (((2 ^ (ℓ + 1) : ℕ) : ℝ) * ((ℓ : ℝ) + 1) * σ ^ ℓ)) / large ^ (2 * ℓ)
      = 2 * ((ℓ : ℝ) + 1) * (((Nat.factorial ℓ : ℕ) : ℝ) ^ 2 * (2 * σ) ^ ℓ)
          / (large ^ 2) ^ ℓ := by
        rw [pow_mul, hcast, mul_pow]; ring
    _ ≤ 2 * ((ℓ : ℝ) + 1) * (((ℓ : ℝ) ^ 2) ^ ℓ * (2 * σ) ^ ℓ)
          / (large ^ 2) ^ ℓ := by gcongr
    _ = 2 * ((ℓ : ℝ) + 1) * (2 * (ℓ : ℝ) ^ 2 * σ / large ^ 2) ^ ℓ := by
        rw [div_pow, ← mul_pow]
        ring_nf

/-- **The level-`j` leg meets its share of the budget** (Track R, A2-III,
S-cal-3; design report §4.3(e)).

`setIntegral_norm_sq_level_sum_of_prev_large_le` shares `large`, the moment
factor `M` and the mean value envelope `E` across all cells of the level; only
`small v` varies.  So the level sum collapses to the total smallness
`S₁ = ∑_v (small v)²` against one constant, and the schedule condition is a
single inequality — with `M/large^{2ℓ}` in the shape `levelJ_moment_le` delivers.

§4.3(e) reaches its condition `P₁ ≥ C/ε³` after transferring the short-block
factorisation count to the dyadic one, at cost `A/Δ = 2/ε`; that transfer is a
step in the moment leg, not here.  What this lemma fixes is the seam: the
`ε³` the level must beat, and the exact arrangement of factors the moment bound
plugs into. -/
theorem levelJ_le_budget (I : Finset ℕ) (ℓ : ℕ) (small : ℕ → ℝ)
    (large E M S₁ c₃ ε ρ κ : ℝ) (hlarge : 0 < large) (hE0 : 0 ≤ E) (hM0 : 0 ≤ M)
    (hS₁ : ∑ v ∈ I, (small v) ^ 2 ≤ S₁)
    (hfit : (I.card : ℝ) * (S₁ * (E * (M / large ^ (2 * ℓ))))
      ≤ κ * bandBudget c₃ ε ρ) :
    (I.card : ℝ) * ∑ v ∈ I, (small v) ^ 2 / large ^ (2 * ℓ) * (E * M)
      ≤ κ * bandBudget c₃ ε ρ := by
  have hD : (0 : ℝ) < large ^ (2 * ℓ) := by positivity
  have hconst : (0 : ℝ) ≤ E * (M / large ^ (2 * ℓ)) :=
    mul_nonneg hE0 (div_nonneg hM0 hD.le)
  have hrw : ∑ v ∈ I, (small v) ^ 2 / large ^ (2 * ℓ) * (E * M)
      = (∑ v ∈ I, (small v) ^ 2) * (E * (M / large ^ (2 * ℓ))) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun v _ => by ring
  have hstep : (∑ v ∈ I, (small v) ^ 2) * (E * (M / large ^ (2 * ℓ)))
      ≤ S₁ * (E * (M / large ^ (2 * ℓ))) :=
    mul_le_mul_of_nonneg_right hS₁ hconst
  have hcard : (0 : ℝ) ≤ (I.card : ℝ) := Nat.cast_nonneg _
  calc (I.card : ℝ) * ∑ v ∈ I, (small v) ^ 2 / large ^ (2 * ℓ) * (E * M)
      = (I.card : ℝ) * ((∑ v ∈ I, (small v) ^ 2) * (E * (M / large ^ (2 * ℓ)))) := by
        rw [hrw]
    _ ≤ (I.card : ℝ) * (S₁ * (E * (M / large ^ (2 * ℓ)))) :=
        mul_le_mul_of_nonneg_left hstep hcard
    _ ≤ κ * bandBudget c₃ ε ρ := hfit

end MoltResearch
