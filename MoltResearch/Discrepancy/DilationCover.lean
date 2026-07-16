import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.SmoothNumbers

/-!
# Discrepancy: the dilation cover for the Fourier reduction

Combinatorial substrate for the Tao 2015 §2 Fourier reduction (arXiv:1509.05363,
`Problems/tao2015_derivation_c.md`, issue #2920): the correspondence between shifts on
the exponent group `(p ∈ primesBelow (X+1)) → ZMod M` and dilations of `[1, X]`.

* `piExp X M j` — the exponent vector of `j` (its factorization, reduced mod `M`).
* `dExp X x` — the `X`-smooth number `∏ p^{(x p).val}` encoded by a group point.
* `factorization_le_log` — every exponent of `j ≤ X` is at most `log₂ X`.
* `dExp_add_piExp` — **the dilation identity**: away from wraparound
  (`(x p).val + v_p(j) < M` for all `p`), `dExp (x + piExp j) = dExp x * j` — so the
  window `j ↦ x + π(j)` of group shifts is the homogeneous arithmetic progression
  `j ↦ d_x·j` in disguise.

The §2 argument evaluates the sign sequence along `dExp` and uses this identity to
convert group-shifted windows into HAP windows, where `BoundedDiscrepancy` applies.
-/

namespace MoltResearch

open Finset

variable {X M : ℕ}

/-- The exponent vector of `j` on the primes up to `X`, reduced mod `M`. -/
def piExp (X M : ℕ) (j : ℕ) : {p : ℕ // p ∈ (X + 1).primesBelow} → ZMod M :=
  fun p => ((j.factorization p.1 : ℕ) : ZMod M)

/-- The `X`-smooth number encoded by a point of the exponent group. -/
def dExp (X : ℕ) {M : ℕ} (x : {p : ℕ // p ∈ (X + 1).primesBelow} → ZMod M) : ℕ :=
  ∏ p ∈ (X + 1).primesBelow.attach, p.1 ^ (x p).val

/-- Every prime exponent of `1 ≤ j ≤ X` is at most `log₂ X`. -/
theorem factorization_le_log {j : ℕ} (hj1 : 1 ≤ j) (hjX : j ≤ X) (p : ℕ) :
    j.factorization p ≤ Nat.log 2 X := by
  by_cases hp : p.Prime
  · have hdvd : p ^ j.factorization p ∣ j := Nat.ordProj_dvd j p
    have h2p : 2 ^ j.factorization p ≤ p ^ j.factorization p :=
      Nat.pow_le_pow_left hp.two_le _
    have hle : 2 ^ j.factorization p ≤ X :=
      le_trans h2p (le_trans (Nat.le_of_dvd (by omega) hdvd) hjX)
    exact (Nat.le_log_iff_pow_le (by omega) (by omega)).mpr hle
  · rw [Nat.factorization_eq_zero_of_not_prime j hp]
    exact Nat.zero_le _

/-- `dExp` is positive when every base is (primes are). -/
theorem dExp_pos (x : {p : ℕ // p ∈ (X + 1).primesBelow} → ZMod M) : 0 < dExp X x := by
  refine Finset.prod_pos fun p _ => ?_
  exact Nat.pow_pos (Nat.prime_of_mem_primesBelow p.2).pos

/-- **The dilation identity** (Tao 2015 §2): away from wraparound, adding the exponent
vector of `j` to `x` multiplies the encoded smooth number by `j`. -/
theorem dExp_add_piExp [NeZero M] {j : ℕ} (hj1 : 1 ≤ j) (hjX : j ≤ X)
    (x : {p : ℕ // p ∈ (X + 1).primesBelow} → ZMod M)
    (hgood : ∀ p : {p : ℕ // p ∈ (X + 1).primesBelow},
      (x p).val + j.factorization p.1 < M) :
    dExp X (x + piExp X M j) = dExp X x * j := by
  have hval : ∀ p : {p : ℕ // p ∈ (X + 1).primesBelow},
      ((x + piExp X M j) p).val = (x p).val + j.factorization p.1 := by
    intro p
    have hlt : j.factorization p.1 < M := by
      have := hgood p
      omega
    have hcast : ((piExp X M j) p).val = j.factorization p.1 := by
      unfold piExp
      exact ZMod.val_natCast_of_lt hlt
    rw [Pi.add_apply, ZMod.val_add_of_lt]
    · rw [hcast]
    · rw [hcast]
      exact hgood p
  unfold dExp
  calc ∏ p ∈ (X + 1).primesBelow.attach, p.1 ^ ((x + piExp X M j) p).val
      = ∏ p ∈ (X + 1).primesBelow.attach,
          (p.1 ^ (x p).val * p.1 ^ j.factorization p.1) := by
        refine Finset.prod_congr rfl fun p _ => ?_
        rw [hval p, pow_add]
    _ = (∏ p ∈ (X + 1).primesBelow.attach, p.1 ^ (x p).val)
        * ∏ p ∈ (X + 1).primesBelow.attach, p.1 ^ j.factorization p.1 := by
        rw [Finset.prod_mul_distrib]
    _ = (∏ p ∈ (X + 1).primesBelow.attach, p.1 ^ (x p).val) * j := by
        congr 1
        -- the attached product recovers `j` from its factorization
        have hattach : ∏ p ∈ (X + 1).primesBelow.attach, p.1 ^ j.factorization p.1
            = ∏ p ∈ (X + 1).primesBelow, p ^ j.factorization p :=
          Finset.prod_attach _ (fun p => p ^ j.factorization p)
        rw [hattach]
        -- the support of the factorization sits inside `primesBelow (X+1)`
        have hsub : j.factorization.support ⊆ (X + 1).primesBelow := by
          intro p hp
          have hpp : p.Prime := Nat.prime_of_mem_primeFactors
            (by rwa [Nat.support_factorization] at hp)
          have hpdvd : p ∣ j := Nat.dvd_of_mem_primeFactors
            (by rwa [Nat.support_factorization] at hp)
          rw [Nat.mem_primesBelow]
          exact ⟨lt_of_le_of_lt (le_trans (Nat.le_of_dvd (by omega) hpdvd) hjX)
            (by omega), hpp⟩
        rw [← Finset.prod_subset hsub (fun p _ hps => by
          rw [Finsupp.notMem_support_iff.mp hps, pow_zero])]
        exact Nat.factorization_prod_pow_eq_self (by omega)

end MoltResearch
