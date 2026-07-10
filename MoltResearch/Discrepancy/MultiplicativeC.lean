import MoltResearch.Discrepancy.Multiplicative

/-!
# Discrepancy: ℂ-valued completely multiplicative language layer

First language-layer module for the Tao 2015 analytic core
(`Problems/tao2015_analytic_core.md`): the ℂ-valued predicates the Fourier-reduction and
log-Elliott interfaces are stated over, plus the coercion bridge from the existing ℤ-valued
substrate.

Definitions:
- `CompletelyMultiplicativeC g` — `g (a * b) = g a * g b` for **all** `a b : ℕ` (no coprimality
  hypothesis, mirroring the ℤ-valued `CompletelyMultiplicative`).
- `Unimodular g` — `‖g n‖ = 1` for all `n` (the "valued in the unit circle `S¹`" hypothesis of
  Tao's interfaces, arXiv:1509.05363 §2).

Bridges (the ℤ-valued substrate embeds in the ℂ-valued language):
- `CompletelyMultiplicative.toC` — a ℤ-valued completely multiplicative sequence is completely
  multiplicative after coercion to ℂ.
- `IsSignSequence.unimodularC` — sign sequences are unimodular after coercion to ℂ.

Partial sums:
- `apSumC g d n` — ℂ-valued homogeneous AP partial sum, mirroring `apSum`.
- `CompletelyMultiplicativeC.apSumC_eq_mul_apSumC_one` — the multiplicative collapse
  `apSumC g d n = g d * apSumC g 1 n` (port of `CompletelyMultiplicative.apSum_eq_mul_apSum_one`).
- `CompletelyMultiplicativeC.norm_apSumC_eq_norm_apSumC_one` — its norm-level corollary for
  unimodular `g`: partial-sum growth along any step `d` is the step-one growth.

Design note (from the card's decision record): interfaces for the analytic core must be stated
over ℂ-valued unimodular functions — the ±1 subclass loses the character-modulated cases. The
ℤ-valued bridge below is the hand-off *into* that subclass once a reduction produces candidates,
not a substitute for it.
-/

namespace MoltResearch

/-- A ℂ-valued completely multiplicative sequence: `g (a * b) = g a * g b` for **all** `a b : ℕ`
(no coprimality hypothesis).

ℂ-valued analogue of `CompletelyMultiplicative`. As there, we do not bake in `g 1 = 1`: it
follows for unimodular sequences (`CompletelyMultiplicativeC.map_one_of_unimodular`), and keeping
the definition minimal makes it easier to produce.
-/
def CompletelyMultiplicativeC (g : ℕ → ℂ) : Prop :=
  ∀ a b : ℕ, g (a * b) = g a * g b

/-- A unimodular sequence: every value lies on the complex unit circle.

This is the "valued in `S¹`" hypothesis in Tao's Fourier-reduction and log-Elliott interfaces.
-/
def Unimodular (g : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, ‖g n‖ = 1

namespace Unimodular

variable {g : ℕ → ℂ}

/-- Unfolding lemma in simp-friendly form: unimodular values have norm `1`. -/
@[simp] theorem norm_eq_one (hg : Unimodular g) (n : ℕ) : ‖g n‖ = 1 :=
  hg n

/-- Unimodular values are nonzero (they have norm `1`). -/
theorem ne_zero (hg : Unimodular g) (n : ℕ) : g n ≠ 0 := by
  intro h
  have h1 := hg n
  rw [h] at h1
  norm_num at h1

end Unimodular

/-- ℂ-valued homogeneous AP partial sum: `g d + g (2*d) + ⋯ + g (n*d)`.

Mirrors `apSum` (`Finset.range n` with `i + 1`, so the progression starts at `d`; `n = 0`
yields sum `0`).
-/
noncomputable def apSumC (g : ℕ → ℂ) (d n : ℕ) : ℂ :=
  (Finset.range n).sum (fun i => g ((i + 1) * d))

/-- Degenerate length: the empty AP sum vanishes. -/
@[simp] theorem apSumC_zero_length (g : ℕ → ℂ) (d : ℕ) : apSumC g d 0 = 0 := by
  simp [apSumC]

namespace CompletelyMultiplicativeC

variable {g : ℕ → ℂ}

/-- A completely multiplicative unimodular sequence fixes `1`.

From `g 1 = g 1 * g 1` and `g 1 ≠ 0`, cancellation gives `g 1 = 1`. ℂ-valued analogue of
`CompletelyMultiplicative.map_one_of_isSignSequence`.
-/
@[simp] theorem map_one_of_unimodular (hmul : CompletelyMultiplicativeC g)
    (hg : Unimodular g) : g 1 = 1 := by
  have h := hmul 1 1
  rw [Nat.mul_one] at h
  have h' : g 1 * g 1 = g 1 * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel₀ (hg.ne_zero 1) h'

/-- Sum-level multiplicative collapse (normal form): the ℂ-valued AP sum at step `d` factors
through the step-one (plain partial) sum.

Normal form: `apSumC g d n = g d * apSumC g 1 n`. Port of
`CompletelyMultiplicative.apSum_eq_mul_apSum_one` to ℂ.
-/
theorem apSumC_eq_mul_apSumC_one (hmul : CompletelyMultiplicativeC g) (d n : ℕ) :
    apSumC g d n = g d * apSumC g 1 n := by
  unfold apSumC
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.mul_one, hmul (i + 1) d]
  exact mul_comm _ _

/-- Norm-level corollary of the multiplicative collapse for unimodular `g`: partial-sum growth
along any step `d` is exactly the step-one growth (`‖g d‖ = 1` scales nothing away).

This is the quantity Tao's Fourier-reduction interface controls: unboundedness of
`‖apSumC g 1 n‖` is unboundedness along every step.
-/
theorem norm_apSumC_eq_norm_apSumC_one (hmul : CompletelyMultiplicativeC g)
    (hg : Unimodular g) (d n : ℕ) :
    ‖apSumC g d n‖ = ‖apSumC g 1 n‖ := by
  rw [hmul.apSumC_eq_mul_apSumC_one d n, norm_mul, hg d, one_mul]

end CompletelyMultiplicativeC

/-- Cast bridge at the norm level: the ℂ-partial-sum norm of a coerced ℤ-valued sequence is the
`natAbs` of its step-one AP sum.

This is the hand-off from ℂ-valued interface conclusions (`∃ n, C < ‖∑ j ∈ Icc 1 n, g j‖` at
`g = fun n => (f n : ℂ)`) back to the ℤ-valued discrepancy substrate
(`discrepancy f 1 n = natAbs (apSum f 1 n)`).
-/
theorem norm_sum_Icc_intCast_eq_natAbs_apSum_one (f : ℕ → ℤ) (n : ℕ) :
    ‖∑ j ∈ Finset.Icc 1 n, ((f j : ℂ))‖ = ((apSum f 1 n).natAbs : ℝ) := by
  have hsum : (∑ j ∈ Finset.Icc 1 n, ((f j : ℂ))) = ((apSum f 1 n : ℤ) : ℂ) := by
    rw [apSum_one_d]
    push_cast
    rfl
  rw [hsum, Complex.norm_intCast, Int.cast_natAbs, Int.cast_abs]

namespace CompletelyMultiplicative

variable {f : ℕ → ℤ}

/-- Coercion bridge: a ℤ-valued completely multiplicative sequence is completely multiplicative
as a ℂ-valued sequence.

This is the hand-off from the verified ±1 substrate into the ℂ-valued language layer of the
analytic core.
-/
theorem toC (hmul : CompletelyMultiplicative f) :
    CompletelyMultiplicativeC (fun n => (f n : ℂ)) := by
  intro a b
  show ((f (a * b) : ℂ)) = (f a : ℂ) * (f b : ℂ)
  exact_mod_cast hmul a b

end CompletelyMultiplicative

namespace IsSignSequence

variable {f : ℕ → ℤ}

/-- Coercion bridge: sign sequences are unimodular as ℂ-valued sequences
(`‖(±1 : ℂ)‖ = 1`). -/
theorem unimodularC (hf : IsSignSequence f) :
    Unimodular (fun n => (f n : ℂ)) := by
  intro n
  rcases hf n with h | h <;> simp [h]

end IsSignSequence

end MoltResearch
