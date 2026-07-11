import MoltResearch.Discrepancy.Basic
import MoltResearch.Discrepancy.Unbounded

/-!
# Discrepancy: completely multiplicative reduction

The first genuinely mathematical step of the Tao 2015 proof shape: for a **completely
multiplicative** sequence, the sum along the homogeneous arithmetic progression with step `d`
factors as `f d` times the plain partial sum, so (for sign sequences) discrepancy along *any*
step collapses to the step-one case.

Consequences packaged here:
- `CompletelyMultiplicative.apSum_eq_mul_apSum_one` — the sum-level factorization.
- `CompletelyMultiplicative.discrepancy_eq_discrepancy_one` — the discrepancy-level collapse.
- `CompletelyMultiplicative.forall_hasDiscrepancyAtLeast_iff_unboundedDiscrepancy_one` —
  for completely multiplicative sign sequences, the full Erdős-discrepancy surface statement
  `∀ C, HasDiscrepancyAtLeast f C` is equivalent to unboundedness of the plain partial sums.
- `CompletelyMultiplicative.boundedDiscrepancy_iff_exists_forall_natAbs_apSum_one_le` — the
  bounded (negation) side of the same equivalence.

This is the verified bridge behind the Track C reduction-to-multiplicative interface: once a
Fourier-reduction stage produces a completely multiplicative counterexample candidate, its EDP
statement is exactly "unbounded partial sums".
-/

namespace MoltResearch

/-- A completely multiplicative sequence: `f (a * b) = f a * f b` for all **nonzero**
`a b : ℕ` (no coprimality hypothesis).

Note we do not bake in `f 1 = 1`: it follows for sign sequences
(`CompletelyMultiplicative.map_one_of_isSignSequence`), and keeping the definition minimal makes
it easier to produce.

The `a ≠ 0 → b ≠ 0` guards are load-bearing (issue #2879): the literature defines completely
multiplicative sequences on `{1, 2, ...}`, and an unguarded law instantiated at `b = 0` gives
`f 0 = f a * f 0` for every `a`, which under `IsSignSequence` (`f 0 = ±1 ≠ 0`) collapses the
class to the constant-1 sequence and vacates every statement quantifying over it. With the
guards, `f 0` is genuinely unconstrained junk.
-/
def CompletelyMultiplicative (f : ℕ → ℤ) : Prop :=
  ∀ a b : ℕ, a ≠ 0 → b ≠ 0 → f (a * b) = f a * f b

namespace CompletelyMultiplicative

variable {f : ℕ → ℤ}

/-- A completely multiplicative sign sequence fixes `1`.

From `f 1 = f 1 * f 1` the only sign-sequence value that works is `1`.
-/
theorem map_one_of_isSignSequence (hmul : CompletelyMultiplicative f)
    (hf : IsSignSequence f) : f 1 = 1 := by
  have h := hmul 1 1 one_ne_zero one_ne_zero
  rw [Nat.mul_one] at h
  rcases hf 1 with h1 | h1
  · exact h1
  · rw [h1] at h
    norm_num at h

/-- Sum-level multiplicative reduction (normal form): the AP sum at step `d` factors through the
step-one (plain partial) sum.

Normal form: `apSum f d n = f d * apSum f 1 n`. The `d ≠ 0` hypothesis is necessary: at
`d = 0` the left side is `n • f 0` (junk) while the right is `f 0 * (f 1 + ⋯)`.
-/
theorem apSum_eq_mul_apSum_one (hmul : CompletelyMultiplicative f) {d : ℕ} (hd : d ≠ 0)
    (n : ℕ) :
    apSum f d n = f d * apSum f 1 n := by
  unfold apSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.mul_one, hmul (i + 1) d (Nat.succ_ne_zero i) hd]
  exact mul_comm _ _

/-- Discrepancy-level multiplicative reduction (normal form): for a completely multiplicative
sign sequence, discrepancy along any step `d` equals the step-one discrepancy.

The sign hypothesis is used only through `|f d| = 1`. The `d ≠ 0` hypothesis is necessary
(at `d = 0` the left side is `n * |f 0|`).
-/
theorem discrepancy_eq_discrepancy_one (hmul : CompletelyMultiplicative f)
    (hf : IsSignSequence f) {d : ℕ} (hd : d ≠ 0) (n : ℕ) :
    discrepancy f d n = discrepancy f 1 n := by
  rw [discrepancy_eq_natAbs_apSum, discrepancy_eq_natAbs_apSum,
    hmul.apSum_eq_mul_apSum_one hd n, Int.natAbs_mul, hf.natAbs_eq_one d, one_mul]

/-- `disc`-wrapper variant of `discrepancy_eq_discrepancy_one` (API coherence). -/
theorem disc_eq_disc_one (hmul : CompletelyMultiplicative f) (hf : IsSignSequence f) {d : ℕ}
    (hd : d ≠ 0) (n : ℕ) :
    disc f d n = disc f 1 n := by
  rw [disc_eq_discrepancy, disc_eq_discrepancy]
  exact hmul.discrepancy_eq_discrepancy_one hf hd n

/-- **Step 1 of the Tao 2015 proof shape**: for a completely multiplicative sign sequence, the
Erdős-discrepancy surface statement is equivalent to unboundedness of the plain partial sums.

Normal form: `(∀ C, HasDiscrepancyAtLeast f C) ↔ UnboundedDiscrepancy f 1`.

The forward direction collapses an arbitrary-step witness to step one via
`discrepancy_eq_discrepancy_one`; the backward direction instantiates the step existential at
`d = 1`.
-/
theorem forall_hasDiscrepancyAtLeast_iff_unboundedDiscrepancy_one
    (hmul : CompletelyMultiplicative f) (hf : IsSignSequence f) :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔ UnboundedDiscrepancy f 1 := by
  constructor
  · intro h B
    rcases h B with ⟨d, n, hd, hgt⟩
    refine ⟨n, ?_⟩
    rw [← hmul.discrepancy_eq_discrepancy_one hf hd.ne' n, discrepancy_eq_natAbs_apSum]
    exact hgt
  · intro h C
    rcases h C with ⟨n, hn⟩
    refine ⟨1, n, Nat.one_pos, ?_⟩
    rw [discrepancy_eq_natAbs_apSum] at hn
    exact hn

/-- Bounded-side normal form of the multiplicative reduction: bounded discrepancy for a
completely multiplicative sign sequence is exactly a uniform bound on the plain partial sums.

Normal form: `BoundedDiscrepancy f ↔ ∃ B, ∀ n, Int.natAbs (apSum f 1 n) ≤ B`.
-/
theorem boundedDiscrepancy_iff_exists_forall_natAbs_apSum_one_le
    (hmul : CompletelyMultiplicative f) (hf : IsSignSequence f) :
    BoundedDiscrepancy f ↔ ∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSum f 1 n) ≤ B := by
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨B, fun n => hB 1 n Nat.one_pos⟩
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro d n hd
    calc Int.natAbs (apSum f d n)
        = discrepancy f d n := natAbs_apSum_eq_discrepancy f d n
      _ = discrepancy f 1 n := hmul.discrepancy_eq_discrepancy_one hf hd.ne' n
      _ = Int.natAbs (apSum f 1 n) := discrepancy_eq_natAbs_apSum f 1 n
      _ ≤ B := hB n

end CompletelyMultiplicative

end MoltResearch
