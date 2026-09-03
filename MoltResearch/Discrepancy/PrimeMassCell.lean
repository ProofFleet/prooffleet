import MoltResearch.Discrepancy.BrunTitchmarsh
import MoltResearch.Discrepancy.MertensFirst

/-!
# Prime mass on a short interval (Track R, A2-III, the instantiation)

`BandSchedule.collar_weight_le` is stated with two abstract quantities: `M`, a
bound on the prime mass `∑_{p ∈ 𝒞_v} 1/p` of a single `e`-adic cell, and
`Stot`, a bound on the total mass over the level.  Its docstring says a consumer
supplies them "from Mertens on a cell and the total from Mertens on the level".
This module is those two inputs.

They matter more than bookkeeping.  The S-cal-6/7 correction to design report
§4.3(a) turned on the observation that the assembled collar quantity carries a
Cauchy–Schwarz factor `#I ≍ 2N log(Q/P)` growing linearly in `N`, which cancels
the `1/N` the collar ratio buys — and that the leg survives only because the
cells are narrow, `σ_v = O(1/(N log P))`, giving a *second* factor of `1/N`.
`sum_one_div_prime_Ioc_le` is what makes that second factor a theorem rather
than an assertion: a cell of multiplicative width `e^{1/(2N)}` sitting above `P`
is an interval of length `≍ P/N`, and Brun–Titchmarsh prices its primes.

No new sieve input is needed — `card_primes_Ioc_le` (the crude Brun–Titchmarsh
already in the tree, via the linear Selberg sieve) and
`sum_one_div_primesBelow_le_sharp` (Mertens) are both on main.
-/

namespace MoltResearch

open Finset

/-- **The prime mass of a short interval** (Track R, A2-III).

`∑_{a < p ≤ a+K} 1/p ≤ 256·K/(a·log K)`.

Every prime of the interval exceeds `a`, so each term is at most `1/a` and the
sum is at most the count over `a`; the count is Brun–Titchmarsh
(`card_primes_Ioc_le`).  Crude in the constant and sharp in the shape, which is
what the collar leg needs: at `a ≍ P` and `K ≍ P/N` — an `e`-adic cell of
multiplicative width `e^{1/(2N)}` above `P` — it reads

  `σ_v ≤ 256/(N·log(P/N))`,

the `O(1/(N log P))` that S-cal-7's `collar_weight_le` takes as `M`.  Note the
bound does **not** degrade as the cell narrows relative to `a`: the `K` upstairs
and the `log K` downstairs both shrink, and it is the ratio `K/a` that carries
the decay. -/
theorem sum_one_div_prime_Ioc_le (a K : ℕ) (ha : 1 ≤ a) (hK : 2 ≤ K) :
    ∑ p ∈ (Finset.Ioc a (a + K)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
      ≤ 256 * (K : ℝ) / ((a : ℝ) * Real.log K) := by
  classical
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hK1 : (1 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hlogK : (0 : ℝ) < Real.log K := Real.log_pos hK1
  have hterm : ∀ p ∈ (Finset.Ioc a (a + K)).filter Nat.Prime,
      (1 : ℝ) / (p : ℝ) ≤ 1 / (a : ℝ) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    have : (a : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.1.1.le
    exact one_div_le_one_div_of_le ha0 this
  have hcard := card_primes_Ioc_le a K hK
  calc ∑ p ∈ (Finset.Ioc a (a + K)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
      ≤ ∑ _p ∈ (Finset.Ioc a (a + K)).filter Nat.Prime, (1 : ℝ) / (a : ℝ) :=
        Finset.sum_le_sum hterm
    _ = (((Finset.Ioc a (a + K)).filter Nat.Prime).card : ℝ) * (1 / (a : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (256 * (K : ℝ) / Real.log K) * (1 / (a : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 256 * (K : ℝ) / ((a : ℝ) * Real.log K) := by
        field_simp

/-- **The prime mass of a level, from Mertens** (Track R, A2-III).

`∑_{a < p ≤ b} 1/p ≤ log log (b+1) + 11`, the `Stot` input of
`collar_weight_le`.

The primes of `(a, b]` sit inside `primesBelow (b+1)`, and every term is
nonnegative, so the in-tree sharp Mertens bound applies to the larger set.
Discarding the lower endpoint costs nothing the collar leg notices: `Stot`
enters `collar_weight_le` multiplied by `M`, which already carries both factors
of `1/N`, so the level total only has to be `(log log)`-small rather than
sharp. -/
theorem sum_one_div_prime_Ioc_le_mertens (a b : ℕ) (hb : 3 ≤ b) :
    ∑ p ∈ (Finset.Ioc a b).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
      ≤ Real.log (Real.log ((b : ℝ) + 1)) + 11 := by
  classical
  have hsub : (Finset.Ioc a b).filter Nat.Prime ⊆ (b + 1).primesBelow := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    rw [Nat.mem_primesBelow]
    exact ⟨by omega, hp.2⟩
  have hmono : ∑ p ∈ (Finset.Ioc a b).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
      ≤ ∑ p ∈ (b + 1).primesBelow, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity
  refine hmono.trans ?_
  have := sum_one_div_primesBelow_le_sharp (b + 1) (by omega)
  have hcast : ((b + 1 : ℕ) : ℝ) = (b : ℝ) + 1 := by push_cast; ring
  rwa [hcast] at this

end MoltResearch
