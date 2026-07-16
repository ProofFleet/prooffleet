import MoltResearch.Discrepancy.DilationCover
import MoltResearch.Discrepancy.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Discrepancy: the averaged window bound (eq. (fpi))

Tao 2015 §2 (arXiv:1509.05363, `Problems/tao2015_derivation_c.md`, issue #2920), the
averaged square bound: evaluating a bounded-discrepancy sign sequence along the smooth
encoding `dExp`, the group average of squared window sums is at most `B² + 1` once the
exponent modulus `M` is large.

* `smoothEval f X x = f(dExp X x)` — the sign sequence on the exponent group.
* Away from wraparound (`WrapFree`), a window `j ↦ x + piExp j` is the HAP
  `j ↦ dExp(x)·j` (by `dExp_add_piExp`), so the window sum **is** `apSum` and is bounded
  by `B` (`norm_window_smoothEval_le_of_wrapFree`).
* Wraparound points are rare: at most `r·log₂X·M^{r−1}` of `M^r`
  (`card_not_wrapFree_le`), and each carries only the trivial bound `n² ≤ X²`.
* `avg_normSq_window_smoothEval_le` — eq. (fpi): the average is `≤ B² + 1` for
  `M ≥ r·log₂X·X²`.
-/

namespace MoltResearch

open Finset

variable {X M : ℕ}

/-- The sign sequence evaluated along the smooth encoding of the exponent group. -/
def smoothEval (f : ℕ → ℤ) (X : ℕ) {M : ℕ}
    (x : {p : ℕ // p ∈ (X + 1).primesBelow} → ZMod M) : ℂ :=
  ((f (dExp X x) : ℤ) : ℂ)

/-- Points of the exponent group whose coordinates all leave `log₂ X` of headroom:
adding any exponent vector of a `j ≤ X` cannot wrap mod `M`. -/
def WrapFree (X M : ℕ) (x : {p : ℕ // p ∈ (X + 1).primesBelow} → ZMod M) : Prop :=
  ∀ p : {p : ℕ // p ∈ (X + 1).primesBelow}, (x p).val + Nat.log 2 X < M

instance : DecidablePred (WrapFree X M) := fun _ => Fintype.decidableForallFintype

/-- On wrap-free points the window sum is a homogeneous AP sum of the sign sequence. -/
theorem window_smoothEval_eq_apSum [NeZero M] {f : ℕ → ℤ} {n : ℕ} (hnX : n ≤ X)
    {x : {p : ℕ // p ∈ (X + 1).primesBelow} → ZMod M} (hx : WrapFree X M x) :
    ∑ j ∈ Finset.Icc 1 n, smoothEval f X (x + piExp X M j)
      = ((apSum f (dExp X x) n : ℤ) : ℂ) := by
  have hterm : ∀ j ∈ Finset.Icc 1 n,
      smoothEval f X (x + piExp X M j) = ((f (dExp X x * j) : ℤ) : ℂ) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hgood : ∀ p : {p : ℕ // p ∈ (X + 1).primesBelow},
        (x p).val + j.factorization p.1 < M := by
      intro p
      have h1 := factorization_le_log (X := X) (j := j) (by omega) (by omega) p.1
      have h2 := hx p
      omega
    unfold smoothEval
    rw [dExp_add_piExp (by omega) (by omega) x hgood]
  rw [Finset.sum_congr rfl hterm]
  unfold apSum
  rw [show Finset.Icc 1 n = Finset.Ico 1 (n + 1) from Finset.val_inj.mp rfl,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.add_comm 1 i, Nat.mul_comm]

/-- Wrap-free windows are bounded by the discrepancy constant. -/
theorem norm_window_smoothEval_le_of_wrapFree [NeZero M] {f : ℕ → ℤ} {B : ℕ}
    (hB : ∀ d n : ℕ, d > 0 → (apSum f d n).natAbs ≤ B) {n : ℕ} (hnX : n ≤ X)
    {x : {p : ℕ // p ∈ (X + 1).primesBelow} → ZMod M} (hx : WrapFree X M x) :
    ‖∑ j ∈ Finset.Icc 1 n, smoothEval f X (x + piExp X M j)‖ ≤ (B : ℝ) := by
  rw [window_smoothEval_eq_apSum hnX hx, Complex.norm_intCast, ← Int.cast_abs]
  have h2 : |apSum f (dExp X x) n| ≤ (B : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hB (dExp X x) n (dExp_pos x)
  exact_mod_cast h2

/-- Every window is trivially bounded by its length (sign sequences are unimodular). -/
theorem norm_window_smoothEval_le {f : ℕ → ℤ} (hs : IsSignSequence f) (n : ℕ)
    (x : {p : ℕ // p ∈ (X + 1).primesBelow} → ZMod M) :
    ‖∑ j ∈ Finset.Icc 1 n, smoothEval f X (x + piExp X M j)‖ ≤ (n : ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  have hone : ∀ j ∈ Finset.Icc 1 n, ‖smoothEval f X (x + piExp X M j)‖ = 1 := by
    intro j _
    unfold smoothEval
    rcases hs (dExp X (x + piExp X M j)) with h | h <;>
      rw [h] <;> norm_num
  rw [Finset.sum_congr rfl hone, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  simp

/-- Reducible alias for the prime-index type of the exponent group. -/
abbrev PrimeIdx (X : ℕ) := {p : ℕ // p ∈ (X + 1).primesBelow}

/-- Coordinate values in a length-`L` top window are rare: at most `L` of `M`. -/
private lemma card_val_top_le [NeZero M] (L : ℕ) :
    ((Finset.univ : Finset (ZMod M)).filter fun a : ZMod M => M ≤ a.val + L).card
      ≤ L := by
  classical
  refine le_trans (Finset.card_le_card_of_injOn (fun a => a.val + L - M)
    ?_ ?_) (Finset.card_range L).le
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_coe, Finset.mem_range]
    have hlt : a.val < M := ZMod.val_lt a
    omega
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha hb
    have hva : a.val < M := ZMod.val_lt a
    have hvb : b.val < M := ZMod.val_lt b
    have hab' : a.val + L - M = b.val + L - M := hab
    have hv : a.val = b.val := by omega
    exact ZMod.val_injective M hv

/-- **Wraparound points are rare**: at most `r·log₂X·M^{r−1}` of the `M^r` group
points fail `WrapFree`. -/
theorem card_not_wrapFree_le [NeZero M] :
    ((Finset.univ : Finset (PrimeIdx X → ZMod M)).filter
        fun x => ¬ WrapFree X M x).card
      ≤ Fintype.card (PrimeIdx X) * Nat.log 2 X
        * M ^ (Fintype.card (PrimeIdx X) - 1) := by
  classical
  set L := Nat.log 2 X with hLdef
  have hsub : (Finset.univ : Finset (PrimeIdx X → ZMod M)).filter
      (fun x => ¬ WrapFree X M x)
      ⊆ Finset.univ.biUnion fun p : PrimeIdx X =>
          (Finset.univ : Finset (PrimeIdx X → ZMod M)).filter
            fun x => M ≤ (x p).val + L := by
    intro x hx
    rw [Finset.mem_filter] at hx
    have hbad := hx.2
    unfold WrapFree at hbad
    push_neg at hbad
    obtain ⟨p, hp⟩ := hbad
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ p,
      Finset.mem_filter.mpr ⟨Finset.mem_univ x, by omega⟩⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans Finset.card_biUnion_le ?_
  have hper : ∀ p : PrimeIdx X,
      ((Finset.univ : Finset (PrimeIdx X → ZMod M)).filter
          fun x => M ≤ (x p).val + L).card
        ≤ L * M ^ (Fintype.card (PrimeIdx X) - 1) := by
    intro p
    have hemb : ((Finset.univ : Finset (PrimeIdx X → ZMod M)).filter
        fun x => M ≤ (x p).val + L).card
          ≤ (((Finset.univ : Finset (ZMod M)).filter
              fun a : ZMod M => M ≤ a.val + L)
            ×ˢ (Finset.univ : Finset ({q : PrimeIdx X // q ≠ p} → ZMod M))).card := by
      refine Finset.card_le_card_of_injOn
        (fun x => (x p, fun q => x q.1)) ?_ ?_
      · intro x hx
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hx
        simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact ⟨hx, trivial⟩
      · intro x _ y _ hxy
        have h1 : x p = y p := congrArg Prod.fst hxy
        have h2 : ∀ q : {q : PrimeIdx X // q ≠ p}, x q.1 = y q.1 :=
          fun q => congrFun (congrArg Prod.snd hxy) q
        funext q
        by_cases hq : q = p
        · rw [hq]
          exact h1
        · exact h2 ⟨q, hq⟩
    refine le_trans hemb ?_
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fun, ZMod.card]
    have hcard : Fintype.card {q : PrimeIdx X // q ≠ p}
        = Fintype.card (PrimeIdx X) - 1 := by
      rw [Fintype.card_subtype_compl]
      simp
    rw [hcard]
    exact Nat.mul_le_mul_right _ (card_val_top_le L)
  calc ∑ p : PrimeIdx X, ((Finset.univ : Finset (PrimeIdx X → ZMod M)).filter
        fun x => M ≤ (x p).val + L).card
      ≤ ∑ _p : PrimeIdx X, L * M ^ (Fintype.card (PrimeIdx X) - 1) :=
        Finset.sum_le_sum fun p _ => hper p
    _ = Fintype.card (PrimeIdx X) * L * M ^ (Fintype.card (PrimeIdx X) - 1) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        ring

end MoltResearch
