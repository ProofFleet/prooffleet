import MoltResearch.Discrepancy.Affine

/-!
# Discrepancy: gcd / coprimality normalization helpers

Checklist item: Problems/erdos_discrepancy.md (Track B) —
`GCD/step normalization helper: ... normalize hypotheses to Nat.coprime d m by factoring out gcd`.

This module is intentionally small:
- it provides a canonical way to factor out `g := Nat.gcd a d` from an affine AP sum
  `apSumFrom f a d n`, producing reduced parameters `a/g` and `d/g` that are coprime;
- the proof is just arithmetic + the existing dilation normal form.

Downstream stages can use these lemmas to assume coprimality “for free” by rewriting into the
reduced form.
-/

namespace MoltResearch

open scoped Nat

/-- The reduced pair `(a / gcd(a,d), d / gcd(a,d))` is coprime.

Mathlib provides `Nat.coprime_div_gcd_div_gcd`, but it expects a proof that `0 < gcd a d`.
This wrapper keeps the call sites lightweight.
-/
theorem coprime_div_gcd_div_gcd (a d : ℕ) (hgd : 0 < Nat.gcd a d) :
    Nat.Coprime (a / Nat.gcd a d) (d / Nat.gcd a d) := by
  simpa using (Nat.coprime_div_gcd_div_gcd (m := a) (n := d) hgd)

/-- Normalize an affine AP sum by dividing out `g := Nat.gcd a d`.

This rewrites `apSumFrom f a d n` into an AP sum with coprime parameters `(a/g, d/g)` on the
*gcd-restricted* sequence `k ↦ f (k * g)`.

The point: once rewritten, later stages may assume `Nat.Coprime (a/g) (d/g)`.
-/
theorem apSumFrom_eq_apSumFrom_div_gcd_map_mul_right (f : ℕ → ℤ) (a d n : ℕ) :
    apSumFrom f a d n =
      apSumFrom (fun k => f (k * Nat.gcd a d)) (a / Nat.gcd a d) (d / Nat.gcd a d) n := by
  -- Use the existing dilation normal form, then cancel the `div_mul_cancel` terms.
  have hgA : Nat.gcd a d ∣ a := Nat.gcd_dvd_left a d
  have hgD : Nat.gcd a d ∣ d := Nat.gcd_dvd_right a d
  -- Start from the forward dilation lemma and rewrite its RHS.
  have h := (apSumFrom_map_mul_right (f := fun k => f k) (q := Nat.gcd a d)
    (a := a / Nat.gcd a d) (d := d / Nat.gcd a d) (n := n))
  -- `h` is: apSumFrom (fun k => f (k * g)) (a/g) (d/g) n = apSumFrom f ((a/g)*g) ((d/g)*g) n
  -- Rewrite the RHS to `apSumFrom f a d n`.
  have h' :
      apSumFrom (fun k => f (k * Nat.gcd a d)) (a / Nat.gcd a d) (d / Nat.gcd a d) n =
        apSumFrom f a d n := by
    simpa [Nat.div_mul_cancel hgA, Nat.div_mul_cancel hgD] using h
  simpa [h']

end MoltResearch
