import MoltResearch.Discrepancy.Basic

/-!
# Discrepancy: sign-sequence coercion hygiene

This file provides a tiny “coercion bridge” for users who already have ±1-valued data packaged in a
non-`ℤ` type (typically a subtype of `ℤ`, or a structure with a coercion to `ℤ`).

The stable discrepancy API is expressed in terms of `f : ℕ → ℤ` together with `IsSignSequence f`.
These lemmas make it easy to reuse existing data without rewriting everything by hand.
-/

namespace MoltResearch

/-!
## Bool / Fin2 sign encodings (Track B)

Checklist item: Problems/erdos_discrepancy.md (Track B) — `discOffset` invariance under swapping `ℤ`
sign encoding.

Later stages often encode sign sequences as `Bool` or `Fin 2`. The nucleus API is written for
`f : ℕ → ℤ`, so we provide a tiny, explicit coercion and a `discOffset`-level congruence wrapper
that lets you swap representations in *statements* without touching downstream lemmas.
-/

/-- Boolean sign encoding: `true ↦ 1`, `false ↦ -1`. -/
def boolToSign : Bool → ℤ
  | true => 1
  | false => -1

@[simp] lemma boolToSign_true : boolToSign true = (1 : ℤ) := rfl
@[simp] lemma boolToSign_false : boolToSign false = (-1 : ℤ) := rfl

/-- Any boolean sequence yields an `IsSignSequence` after decoding via `boolToSign`. -/
lemma isSignSequence_boolToSign (b : ℕ → Bool) : IsSignSequence (fun n => boolToSign (b n)) := by
  intro n
  -- Unfolding `boolToSign` produces a `match`; splitting on `b n` discharges both cases.
  cases h : b n <;> simp [boolToSign, h]

/-- Discrepancy-level representation swap: replace `f : ℕ → ℤ` by a `Bool`-encoded sequence.

If `f` is pointwise equal to the decoded boolean sign sequence, then all offset discrepancies agree.
This packages the index bookkeeping so later stages can change sign encodings without rewriting
`discOffset` statements by hand.
-/
lemma discOffset_congr_boolToSign (f : ℕ → ℤ) (b : ℕ → Bool) (d m n : ℕ)
    (h : ∀ t, f t = boolToSign (b t)) :
    discOffset f d m n = discOffset (fun t => boolToSign (b t)) d m n := by
  -- Use the pointwise congruence wrapper; the hypothesis `h` discharges every accessed index.
  apply discOffset_congr (f := f) (g := fun t => boolToSign (b t)) (d := d) (m := m) (n := n)
  intro i hi
  simpa using (h ((m + i + 1) * d))

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
