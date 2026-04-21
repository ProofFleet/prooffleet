import MoltResearch.Discrepancy.Basic

/-!
# Discrepancy: sign-sequence coercion hygiene

This file provides a tiny “coercion bridge” for users who already have ±1-valued data packaged in a
non-`ℤ` type (typically a subtype of `ℤ`, or a structure with a coercion to `ℤ`).

The stable discrepancy API is expressed in terms of `f : ℕ → ℤ` together with `IsSignSequence f`.
These lemmas make it easy to reuse existing data without rewriting everything by hand.
-/

namespace MoltResearch

/-- A bundled ±1 value in `ℤ`, intended as a convenient source type for sign sequences.

Users can write `f : ℕ → SignZ` and then coerce to `ℤ` via `(f n : ℤ)`.
-/
abbrev SignZ : Type := { z : ℤ // z = 1 ∨ z = -1 }

instance : CoeTC SignZ ℤ := ⟨Subtype.val⟩

@[simp] lemma SignZ.coe_mk (z : ℤ) (hz : z = 1 ∨ z = -1) : ((⟨z, hz⟩ : SignZ) : ℤ) = z := rfl

/-- If a sequence has values in a type that coerces to `ℤ` and those coerced values are always
`±1`, then the coerced sequence is a sign sequence.

This is the main “treat `{±1}`-style data as `ℕ → ℤ`” helper.
-/
lemma isSignSequence_coe {α : Type} [CoeTC α ℤ] (f : ℕ → α)
    (h : ∀ n, (f n : ℤ) = 1 ∨ (f n : ℤ) = -1) :
    IsSignSequence (fun n => (f n : ℤ)) :=
  h

/-- Special case: a `SignZ`-valued sequence coerces to an `IsSignSequence` in one step.

This lemma exists mostly so `simpa` can find it easily.
-/
lemma isSignSequence_coe_signZ (f : ℕ → SignZ) : IsSignSequence (fun n => (f n : ℤ)) := by
  intro n
  simpa using (f n).property

end MoltResearch
