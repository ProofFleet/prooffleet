import Mathlib.NumberTheory.DirichletCharacter.Basic
import MoltResearch.Discrepancy.PretentiousDist
import MoltResearch.Discrepancy.CharTwistCompose

/-!
# Discrepancy: conductor reduction for pretense certificates

Support for the reduction step of Tao 2015 (arXiv:1509.05363, §4, TeX line ~451): after
Proposition 1.11 produces a Dirichlet character `χ` of period `q = O_ε(1)` with

`∑_{p ≤ X} (1 − Re g(p) conj(χ(p)) p^{−i𝐭})/p ≪_ε 1`,

the paper says *"By reducing `χ` if necessary we may assume that `χ` is primitive."* This
module makes that step quantitative: passing from a pretense certificate at **any** character
`χ` mod `N` to one at its primitive core `χ.primitiveCharacter` mod `χ.conductor` costs only
the primes dividing the modulus, with the explicit crude constant `2 · ω(N)`:

`𝔻(g, χ*(·)·(·)^{i𝐭}; M)² ≤ 𝔻(g, χ(·)·(·)^{i𝐭}; M)² + 2 · ω(N)`  (`ω(N) = N.primeFactors.card`).

Contents:
- `primitiveCharacter_apply_eq` — value agreement off the level: at a natural `n` that is a
  unit mod `N`, the primitive core takes the same value as `χ` (from Mathlib's factorization
  `changeLevel_primitiveCharacter` plus `changeLevel_apply_natCast_of_isUnit`).
- `charTwist_primitiveCharacter_eq` — hence the two archimedean twists agree at every prime
  `p ∤ N` (the `cpow` parts are identical).
- `pretentiousDistSq_summand_le_one` — crude per-prime bound: each summand lies in
  `[0, 2/p] ⊆ [0, 1]` for `p ≥ 2`, unimodular `g`, 1-bounded comparison.
- `pretentiousDistSq_primitive_le` — the distance bound above: split `M.primesBelow` at
  `p ∣ N`; off the divisors the summands are equal, and the `≤ ω(N)` divisor primes each
  contribute at most `1` (the slack constant `2` is deliberate crudeness, Tao-style `O(1)`
  bookkeeping at fixed period).
- `conductor_le` — period bookkeeping for the consumer: `χ.conductor ≤ N` as reals, so the
  reduced character still has period `O_ε(1)`.
- `conductor_eq_one_iff` — the degenerate-branch dichotomy: the conductor is `1` exactly for
  the principal character (whose primitive core lives at level `1`, where the character is
  trivially the unit character).

Junk conventions are embraced throughout (`χ` vanishes off the coprime locus, `x / 0 = 0`,
`(0 : ℂ)^s = 0` for `s ≠ 0`), exactly as in `charTwist`.
-/

namespace MoltResearch

/-- **Value agreement off the level** (Tao 2015 §4, "by reducing `χ` if necessary"):
at a natural number `n` that is a unit mod `N`, the primitive core `χ.primitiveCharacter`
(at level `χ.conductor`) takes the same value as `χ` (at level `N`).

Proof: Mathlib's factorization `χ = changeLevel (conductor ∣ N) χ.primitiveCharacter`
evaluated through `changeLevel_apply_natCast_of_isUnit`. No `NeZero` hypothesis is needed. -/
theorem primitiveCharacter_apply_eq {N : ℕ} (χ : DirichletCharacter ℂ N) {n : ℕ}
    (hn : IsUnit ((n : ℕ) : ZMod N)) :
    χ.primitiveCharacter ((n : ℕ) : ZMod χ.conductor) = χ ((n : ℕ) : ZMod N) := by
  rw [← changeLevel_apply_natCast_of_isUnit χ.conductor_dvd_level χ.primitiveCharacter n hn,
    DirichletCharacter.changeLevel_primitiveCharacter]

/-- At a prime `p ∤ N`, the primitive-core twist agrees with the original twist:
the character values agree (`primitiveCharacter_apply_eq`; a prime not dividing `N` is a
unit mod `N`) and the archimedean `cpow` parts are identical. -/
theorem charTwist_primitiveCharacter_eq {N : ℕ} (χ : DirichletCharacter ℂ N) (t : ℝ)
    {p : ℕ} (hp : p.Prime) (hpN : ¬p ∣ N) :
    charTwist χ.conductor χ.primitiveCharacter t p = charTwist N χ t p := by
  simp only [charTwist]
  rw [primitiveCharacter_apply_eq χ (ZMod.isUnit_prime_of_not_dvd hp hpN)]

/-- Crude per-prime bound: each `pretentiousDistSq` summand is at most `2/p ≤ 1` when
`p ≥ 2`, `g` is unimodular, and the comparison `h` is 1-bounded — because
`Re(g p · conj (h p)) ∈ [−1, 1]` forces the numerator into `[0, 2]`. -/
theorem pretentiousDistSq_summand_le_one {g h : ℕ → ℂ} (hg : Unimodular g)
    (hh : ∀ p : ℕ, ‖h p‖ ≤ 1) {p : ℕ} (hp : 2 ≤ p) :
    (1 - (g p * (starRingEnd ℂ) (h p)).re) / p ≤ 1 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hnorm : ‖g p * (starRingEnd ℂ) (h p)‖ ≤ 1 := by
    rw [norm_mul, hg p, RCLike.norm_conj, one_mul]
    exact hh p
  have habs : |(g p * (starRingEnd ℂ) (h p)).re| ≤ 1 :=
    le_trans (Complex.abs_re_le_norm _) hnorm
  have hre : -1 ≤ (g p * (starRingEnd ℂ) (h p)).re := (abs_le.mp habs).1
  rw [div_le_one hp0]
  linarith

/-- **Conductor reduction for pretense certificates** (Tao 2015 §4, TeX line ~451: "By
reducing `χ` if necessary we may assume that `χ` is primitive."): replacing the twist at `χ`
mod `N` by the twist at its primitive core costs at most `2 · ω(N)` in squared pretentious
distance:

`𝔻(g, χ*(·)·(·)^{i𝐭}; M)² ≤ 𝔻(g, χ(·)·(·)^{i𝐭}; M)² + 2 · ω(N)`.

Split the prime sum at `p ∣ N`: off the divisors of `N` the summands agree
(`charTwist_primitiveCharacter_eq`), while the divisor primes in `M.primesBelow` inject into
`N.primeFactors` and each contribute at most `1` on the left and at least `0` on the right.
The constant `2` is deliberate slack (the sharp count is `ω(N)`): at fixed period `O_ε(1)`
this is Tao's `O_ε(1)` bookkeeping. -/
theorem pretentiousDistSq_primitive_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {g : ℕ → ℂ} (hu : Unimodular g) (t : ℝ) (M : ℕ) :
    pretentiousDistSq g (charTwist χ.conductor χ.primitiveCharacter t) M
      ≤ pretentiousDistSq g (charTwist N χ t) M + 2 * N.primeFactors.card := by
  classical
  -- Split each side of the prime sum at `p ∣ N`.
  have hsplit : ∀ h : ℕ → ℂ,
      pretentiousDistSq g h M
        = (∑ p ∈ M.primesBelow.filter (fun p => p ∣ N),
              (1 - (g p * (starRingEnd ℂ) (h p)).re) / p)
          + ∑ p ∈ M.primesBelow.filter (fun p => ¬p ∣ N),
              (1 - (g p * (starRingEnd ℂ) (h p)).re) / p := by
    intro h
    unfold pretentiousDistSq
    exact (Finset.sum_filter_add_sum_filter_not M.primesBelow (fun p => p ∣ N) _).symm
  rw [hsplit (charTwist χ.conductor χ.primitiveCharacter t), hsplit (charTwist N χ t)]
  -- Off the divisors of `N`, the two twists (hence the summands) agree.
  have heq : (∑ p ∈ M.primesBelow.filter (fun p => ¬p ∣ N),
        (1 - (g p * (starRingEnd ℂ)
          (charTwist χ.conductor χ.primitiveCharacter t p)).re) / p)
      = ∑ p ∈ M.primesBelow.filter (fun p => ¬p ∣ N),
        (1 - (g p * (starRingEnd ℂ) (charTwist N χ t p)).re) / p := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter, Nat.mem_primesBelow] at hp
    rw [charTwist_primitiveCharacter_eq χ t hp.1.2 hp.2]
  -- On the divisor part, the left summands are each at most `1`.
  have hLdvd : (∑ p ∈ M.primesBelow.filter (fun p => p ∣ N),
        (1 - (g p * (starRingEnd ℂ)
          (charTwist χ.conductor χ.primitiveCharacter t p)).re) / p)
      ≤ ((M.primesBelow.filter (fun p => p ∣ N)).card : ℝ) := by
    calc (∑ p ∈ M.primesBelow.filter (fun p => p ∣ N),
          (1 - (g p * (starRingEnd ℂ)
            (charTwist χ.conductor χ.primitiveCharacter t p)).re) / p)
        ≤ ∑ _p ∈ M.primesBelow.filter (fun p => p ∣ N), (1 : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          rw [Finset.mem_filter, Nat.mem_primesBelow] at hp
          exact pretentiousDistSq_summand_le_one hu
            (charTwist_norm_le_one χ.conductor χ.primitiveCharacter t) hp.1.2.two_le
      _ = ((M.primesBelow.filter (fun p => p ∣ N)).card : ℝ) := by simp
  -- The divisor primes below `M` inject into `N.primeFactors` (here `N ≠ 0` is used).
  have hcard : ((M.primesBelow.filter (fun p => p ∣ N)).card : ℝ)
      ≤ (N.primeFactors.card : ℝ) := by
    have hsub : M.primesBelow.filter (fun p => p ∣ N) ⊆ N.primeFactors := by
      intro p hp
      rw [Finset.mem_filter, Nat.mem_primesBelow] at hp
      exact Nat.mem_primeFactors.mpr ⟨hp.1.2, hp.2, NeZero.ne N⟩
    exact_mod_cast Finset.card_le_card hsub
  -- On the divisor part, the right summands are each nonnegative.
  have hRdvd : (0 : ℝ) ≤ ∑ p ∈ M.primesBelow.filter (fun p => p ∣ N),
      (1 - (g p * (starRingEnd ℂ) (charTwist N χ t p)).re) / p :=
    Finset.sum_nonneg fun p _ =>
      pretentiousDistSq_summand_nonneg_of_norm_le_one hu (charTwist_norm_le_one N χ t) p
  have homega : (0 : ℝ) ≤ (N.primeFactors.card : ℝ) := Nat.cast_nonneg _
  linarith

/-- Period bookkeeping for the conductor-reduction consumer: the reduced period is no larger,
`χ.conductor ≤ N` as reals (so a period bound `(N : ℝ) ≤ A` transfers to the primitive core).
From `conductor_dvd_level` and `N ≠ 0`. -/
theorem conductor_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    (χ.conductor : ℝ) ≤ (N : ℝ) := by
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) χ.conductor_dvd_level

/-- Primitive-or-trivial dichotomy note: the conductor is `1` exactly when `χ` is the
principal character — in that case the primitive core lives at level `1`, where
`DirichletCharacter ℂ 1` is a subsingleton, so it is the trivial character. Re-export of
Mathlib's `eq_one_iff_conductor_eq_one` in the `NeZero` idiom of this file. -/
theorem conductor_eq_one_iff {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    χ.conductor = 1 ↔ χ = 1 :=
  DirichletCharacter.eq_one_iff_conductor_eq_one.symm

end MoltResearch
