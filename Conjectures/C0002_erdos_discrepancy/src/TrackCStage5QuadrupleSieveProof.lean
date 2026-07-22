import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Assembly

/-!
# Track C: the quadruple sieve, layer 1 — fibering over the sum (Track S of #3004)

First unit of the Track-S campaign discharging `PrimeQuadrupleCountAssumption`:
the additive-quadruple count fibers over the common sum,

  `Q(n₀) = ∑_{s ∈ (2n₀, 4n₀]} r(s)²`,

where `r(s) = blockRep n₀ s` is the number of ordered pairs of block primes
with sum `s`. Downstream, the Selberg Λ² upper bound controls each `r(s)` and
the singular-series second moment sums the squares.

Also the trivial bounds (`r(s) ≤ |𝒫| ≤ n₀`, `Q ≤ 2n₀·n₀² = 2n₀³`) — the
second of which already disposes of every fixed threshold regime `n₀ ≤ N₀`
by enlarging the constant, so the sieve only has to win for large `n₀`.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The representation count: ordered pairs of block primes with sum `s`. -/
noncomputable def blockRep (n₀ s : ℕ) : ℕ :=
  ((primeBlock n₀ ×ˢ primeBlock n₀).filter (fun q => q.1 + q.2 = s)).card

/-- The block cardinality is at most `n₀` (the trivial interval bound). -/
theorem card_primeBlock_le_self (n₀ : ℕ) : (primeBlock n₀).card ≤ n₀ := by
  have hsub : primeBlock n₀ ⊆ Finset.Ioc n₀ (2 * n₀) := by
    intro p hp
    obtain ⟨-, h1, h2⟩ := mem_primeBlock hp
    exact Finset.mem_Ioc.mpr ⟨h1, h2⟩
  calc (primeBlock n₀).card ≤ (Finset.Ioc n₀ (2 * n₀)).card :=
      Finset.card_le_card hsub
    _ = n₀ := by rw [Nat.card_Ioc]; omega

/-- The representation count is at most the block size: the first coordinate
determines the pair. -/
theorem blockRep_le_card (n₀ s : ℕ) : blockRep n₀ s ≤ (primeBlock n₀).card := by
  classical
  rw [blockRep]
  have hinj : ∀ q ∈ (primeBlock n₀ ×ˢ primeBlock n₀).filter
      (fun q => q.1 + q.2 = s), Prod.fst q ∈ primeBlock n₀ := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_product] at hq
    exact hq.1.1
  refine Finset.card_le_card_of_injOn Prod.fst hinj ?_
  intro q₁ hq₁ q₂ hq₂ hfst
  rw [Finset.mem_coe, Finset.mem_filter] at hq₁ hq₂
  have h1 := hq₁.2
  have h2 := hq₂.2
  ext
  · exact hfst
  · omega

/-- The trivial representation bound. -/
theorem blockRep_le (n₀ s : ℕ) : blockRep n₀ s ≤ n₀ :=
  le_trans (blockRep_le_card n₀ s) (card_primeBlock_le_self n₀)

/-- Sums of two block primes land in `(2n₀, 4n₀]`. -/
theorem blockRep_eq_zero_of_notMem {n₀ s : ℕ}
    (hs : s ∉ Finset.Ioc (2 * n₀) (4 * n₀)) : blockRep n₀ s = 0 := by
  classical
  rw [blockRep, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q hq
  rw [Finset.mem_product] at hq
  obtain ⟨h1, h2, h3⟩ := mem_primeBlock hq.1
  obtain ⟨h4, h5, h6⟩ := mem_primeBlock hq.2
  intro hsum
  exact hs (Finset.mem_Ioc.mpr (by omega))

/-- **The fibering identity**: the additive-quadruple count is the second
moment of the representation function over the dyadic sum window. -/
theorem card_quadruple_eq_sum_blockRep_sq (n₀ : ℕ) :
    (((primeBlock n₀ ×ˢ primeBlock n₀) ×ˢ
        (primeBlock n₀ ×ˢ primeBlock n₀)).filter
      (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)).card
    = ∑ s ∈ Finset.Ioc (2 * n₀) (4 * n₀), blockRep n₀ s ^ 2 := by
  classical
  -- expand the filtered product as a double sum of indicators
  rw [Finset.card_filter, Finset.sum_product]
  -- the inner sum over the second pair is the representation count at the sum
  have hinner : ∀ x ∈ primeBlock n₀ ×ˢ primeBlock n₀,
      (∑ y ∈ primeBlock n₀ ×ˢ primeBlock n₀,
        if x.1 + x.2 = y.1 + y.2 then 1 else 0) = blockRep n₀ (x.1 + x.2) := by
    intro x _
    rw [blockRep, Finset.card_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h : y.1 + y.2 = x.1 + x.2
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (fun hc => h hc.symm), if_neg h]
  rw [Finset.sum_congr rfl hinner]
  -- fiber the outer sum over the value of the pair sum
  have hmaps : ∀ x ∈ primeBlock n₀ ×ˢ primeBlock n₀,
      x.1 + x.2 ∈ Finset.Ioc (2 * n₀) (4 * n₀) := by
    intro x hx
    rw [Finset.mem_product] at hx
    obtain ⟨-, h1, h2⟩ := mem_primeBlock hx.1
    obtain ⟨-, h3, h4⟩ := mem_primeBlock hx.2
    exact Finset.mem_Ioc.mpr (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun x => blockRep n₀ (x.1 + x.2))]
  refine Finset.sum_congr rfl fun s _ => ?_
  -- on each fiber the summand is constant `blockRep n₀ s`, and the fiber has
  -- `blockRep n₀ s` elements
  have hconst : ∀ x ∈ (primeBlock n₀ ×ˢ primeBlock n₀).filter
      (fun x => x.1 + x.2 = s), blockRep n₀ (x.1 + x.2) = blockRep n₀ s := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [hx.2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, ← blockRep,
    smul_eq_mul, sq]

/-- **The trivial quadruple bound** `Q ≤ 2·n₀³`: disposes of any fixed
threshold regime by enlarging the constant, so the sieve only has to win for
large `n₀`. -/
theorem card_quadruple_le_cube (n₀ : ℕ) :
    (((primeBlock n₀ ×ˢ primeBlock n₀) ×ˢ
        (primeBlock n₀ ×ˢ primeBlock n₀)).filter
      (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)).card ≤ 2 * n₀ ^ 3 := by
  classical
  rw [card_quadruple_eq_sum_blockRep_sq]
  have hcard : (Finset.Ioc (2 * n₀) (4 * n₀)).card = 2 * n₀ := by
    rw [Nat.card_Ioc]
    omega
  calc ∑ s ∈ Finset.Ioc (2 * n₀) (4 * n₀), blockRep n₀ s ^ 2
      ≤ ∑ _s ∈ Finset.Ioc (2 * n₀) (4 * n₀), n₀ ^ 2 := by
        refine Finset.sum_le_sum fun s _ => ?_
        exact Nat.pow_le_pow_left (blockRep_le n₀ s) 2
    _ = (Finset.Ioc (2 * n₀) (4 * n₀)).card * n₀ ^ 2 := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = 2 * n₀ ^ 3 := by
        rw [hcard]
        ring

end Tao2015

end MoltResearch
