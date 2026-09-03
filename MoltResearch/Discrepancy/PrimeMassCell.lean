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

/-- **The prime energy of a short interval** (Track R, A2-III, M-4).

`∑_{a < p ≤ a+K} 1/p² ≤ 256·K/(a²·log K)`, the companion of
`sum_one_div_prime_Ioc_le` one power further down.

Same two ingredients and the same shape: every prime of the interval exceeds
`a`, so each term is at most `1/a²`, and Brun–Titchmarsh counts them.  It is the
`∑_{p ∈ Y} ‖b p‖²/p²` of the `𝒰` leg's prime large-values factor that needs
this power — coefficient *energy*, not coefficient mass. -/
theorem sum_one_div_prime_sq_Ioc_le (a K : ℕ) (ha : 1 ≤ a) (hK : 2 ≤ K) :
    ∑ p ∈ (Finset.Ioc a (a + K)).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2
      ≤ 256 * (K : ℝ) / ((a : ℝ) ^ 2 * Real.log K) := by
  classical
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hK1 : (1 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hlogK : (0 : ℝ) < Real.log K := Real.log_pos hK1
  have hterm : ∀ p ∈ (Finset.Ioc a (a + K)).filter Nat.Prime,
      (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / (a : ℝ) ^ 2 := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    have hap : (a : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.1.1.le
    have : (a : ℝ) ^ 2 ≤ (p : ℝ) ^ 2 := by nlinarith
    exact one_div_le_one_div_of_le (by positivity) this
  have hcard := card_primes_Ioc_le a K hK
  calc ∑ p ∈ (Finset.Ioc a (a + K)).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2
      ≤ ∑ _p ∈ (Finset.Ioc a (a + K)).filter Nat.Prime, (1 : ℝ) / (a : ℝ) ^ 2 :=
        Finset.sum_le_sum hterm
    _ = (((Finset.Ioc a (a + K)).filter Nat.Prime).card : ℝ) * (1 / (a : ℝ) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (256 * (K : ℝ) / Real.log K) * (1 / (a : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 256 * (K : ℝ) / ((a : ℝ) ^ 2 * Real.log K) := by
        field_simp

/-- **The `𝒰` leg's prime mass on a dyadic block** (Track R, A2-III, M-4).

`∑_{p ∈ Y} 1/p ≤ 256/log P` for a set `Y` of primes in `(P, 2P]`.

`sum_one_div_prime_Ioc_le` at `a = K = P`, where the interval's length equals
its base and the bound's ratio `K/a` is `1`.  This is the `∑_{p ∈ Y} 1/p` that
appears inside `Γ` — the ratio by which the `V₀`-dependent part of the `𝒰`
leg's prime term exceeds the `V₀`-free part, in
`BandSchedule.exceptional_threshold_le_budget`. -/
theorem sum_one_div_prime_dyadic_le (P : ℕ) (hP : 2 ≤ P) (Y : Finset ℕ)
    (hY : ∀ p ∈ Y, p.Prime) (hlo : ∀ p ∈ Y, P < p) (hhi : ∀ p ∈ Y, p ≤ 2 * P) :
    ∑ p ∈ Y, (1 : ℝ) / (p : ℝ) ≤ 256 / Real.log P := by
  classical
  have hsub : Y ⊆ (Finset.Ioc P (P + P)).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hlo p hp, by have := hhi p hp; omega⟩, hY p hp⟩
  have hmono : ∑ p ∈ Y, (1 : ℝ) / (p : ℝ)
      ≤ ∑ p ∈ (Finset.Ioc P (P + P)).filter Nat.Prime, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity
  refine hmono.trans ?_
  have hbt := sum_one_div_prime_Ioc_le P P (by omega) hP
  have hP0 : (0 : ℝ) < (P : ℝ) := by
    have : 0 < P := by omega
    exact_mod_cast this
  have hlogP : (0 : ℝ) < Real.log P := Real.log_pos (by exact_mod_cast hP)
  refine hbt.trans ?_
  rw [div_le_div_iff₀ (by positivity) hlogP]
  ring_nf
  nlinarith [hP0, hlogP]

/-- **The `𝒰` leg's prime large-values factor** (Track R, A2-III, M-4).

`(∑_{p ∈ Y} ‖b p‖²/p²)·P/log P ≤ 256/(log P)²` for `Y` a set of primes in
`(P, 2P]` with bounded coefficients.

This is the group named `Bpri` in `BandSchedule.exceptional_threshold_le_budget`
— the `V₀`-free part of `setIntegral_band_energy_exceptional_max_le`'s prime
term — up to its explicit constant `64`, so the instantiated statement is
`Bpri ≤ 2^14/(log P)²`.

**The finding: `Bpri` does not depend on `P` at all, only on `log P`.**  The
prime energy of the block is `≍ 1/(P log P)` (`sum_one_div_prime_sq_Ioc_le`:
one `1/P` from the second power, one `1/log P` from Brun–Titchmarsh counting),
and the leg multiplies it back by the `P/log P` of the prime large-values
theorem.  The `P` cancels exactly, and what survives is two factors of
`1/log P`.  That is why the `𝒰` leg's `δ²Bpri` term is *harmless* at the
schedule's scales and the binding term is the cross term `2δ√(Aint·BpriΓ)` —
the observation `exceptional_threshold_le_budget`'s docstring records and does
not derive. -/
theorem prime_energy_dyadic_le (P : ℕ) (hP : 2 ≤ P) (Y : Finset ℕ)
    (hY : ∀ p ∈ Y, p.Prime) (hlo : ∀ p ∈ Y, P < p) (hhi : ∀ p ∈ Y, p ≤ 2 * P)
    (b : ℕ → ℂ) (hb : ∀ p, ‖b p‖ ≤ 1) :
    (∑ p ∈ Y, ‖b p‖ ^ 2 / (p : ℝ) ^ 2) * (P : ℝ) / Real.log P
      ≤ 256 / (Real.log P) ^ 2 := by
  classical
  have hP0 : (0 : ℝ) < (P : ℝ) := by
    have : 0 < P := by omega
    exact_mod_cast this
  have hlogP : (0 : ℝ) < Real.log P := Real.log_pos (by exact_mod_cast hP)
  have hsub : Y ⊆ (Finset.Ioc P (P + P)).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hlo p hp, by have := hhi p hp; omega⟩, hY p hp⟩
  -- coefficient energy ≤ the bare prime energy
  have hcoef : ∑ p ∈ Y, ‖b p‖ ^ 2 / (p : ℝ) ^ 2 ≤ ∑ p ∈ Y, (1 : ℝ) / (p : ℝ) ^ 2 := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hb1 : ‖b p‖ ^ 2 ≤ 1 := by
      have h0 : (0 : ℝ) ≤ ‖b p‖ := norm_nonneg _
      nlinarith [hb p]
    have hpp : (0 : ℝ) < (p : ℝ) ^ 2 := by
      have : 0 < p := (hY p hp).pos
      have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast this
      positivity
    gcongr
  have hmono : ∑ p ∈ Y, (1 : ℝ) / (p : ℝ) ^ 2
      ≤ ∑ p ∈ (Finset.Ioc P (P + P)).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity
  have hbt := sum_one_div_prime_sq_Ioc_le P P (by omega) hP
  have hkey : ∑ p ∈ Y, ‖b p‖ ^ 2 / (p : ℝ) ^ 2 ≤ 256 / ((P : ℝ) * Real.log P) := by
    refine (hcoef.trans (hmono.trans hbt)).trans (le_of_eq ?_)
    field_simp
  calc (∑ p ∈ Y, ‖b p‖ ^ 2 / (p : ℝ) ^ 2) * (P : ℝ) / Real.log P
      ≤ (256 / ((P : ℝ) * Real.log P)) * (P : ℝ) / Real.log P := by
        gcongr
    _ = 256 / (Real.log P) ^ 2 := by
        field_simp

end MoltResearch
