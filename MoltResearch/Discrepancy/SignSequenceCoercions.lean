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

/-- Helper: on `±1` inputs, decoding `decide (z = 1)` via `boolToSign` recovers `z`. -/
lemma boolToSign_decide_eq (z : ℤ) (hz : z = 1 ∨ z = -1) :
    boolToSign (decide (z = 1)) = z := by
  rcases hz with hz | hz <;> simp [hz, boolToSign]

/-- Packaged version of `discOffset_congr_boolToSign` for sign sequences.

This lets you *change encodings in statements* without providing the pointwise equality by hand:
use the canonical boolean encoding `t ↦ decide (f t = 1)`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — `discOffset` invariance under swapping `ℤ`
sign encoding.
-/
lemma IsSignSequence.discOffset_eq_boolToSign_decide {f : ℕ → ℤ} (hf : IsSignSequence f)
    (d m n : ℕ) :
    discOffset f d m n = discOffset (fun t => boolToSign (decide (f t = 1))) d m n := by
  apply discOffset_congr (f := f) (g := fun t => boolToSign (decide (f t = 1)))
      (d := d) (m := m) (n := n)
  intro i hi
  simpa using (boolToSign_decide_eq (z := f ((m + i + 1) * d)) (hf ((m + i + 1) * d))).symm

/-!
### `Fin 2` sign encoding

Some later stages prefer `Fin 2` in place of `Bool`.
We provide the same explicit decoding and a `discOffset`-level congruence wrapper.
-/

/-- `Fin 2` sign encoding: `0 ↦ 1`, `1 ↦ -1`. -/
def fin2ToSign (x : Fin 2) : ℤ :=
  if x = 0 then 1 else -1

@[simp] lemma fin2ToSign_zero : fin2ToSign (0 : Fin 2) = (1 : ℤ) := by
  simp [fin2ToSign]

@[simp] lemma fin2ToSign_one : fin2ToSign (1 : Fin 2) = (-1 : ℤ) := by
  simp [fin2ToSign]

/-- Any `Fin 2` sequence yields an `IsSignSequence` after decoding via `fin2ToSign`. -/
lemma isSignSequence_fin2ToSign (b : ℕ → Fin 2) : IsSignSequence (fun n => fin2ToSign (b n)) := by
  intro n
  classical
  by_cases h : b n = 0
  · left; simp [fin2ToSign, h]
  · right
    -- In `Fin 2`, anything other than `0` is `1`.
    have : b n = 1 := by
      -- `Fin 2` has exactly two values.
      have hn : (b n).val = 0 ∨ (b n).val = 1 := by
        have : (b n).val < 2 := (b n).isLt
        omega
      cases hn with
      | inl h0 =>
          exfalso
          apply h
          ext
          simpa using h0
      | inr h1 =>
          ext
          simpa using h1
    simp [fin2ToSign, h, this]

/-- Discrepancy-level representation swap: replace `f : ℕ → ℤ` by a `Fin 2`-encoded sequence. -/
lemma discOffset_congr_fin2ToSign (f : ℕ → ℤ) (b : ℕ → Fin 2) (d m n : ℕ)
    (h : ∀ t, f t = fin2ToSign (b t)) :
    discOffset f d m n = discOffset (fun t => fin2ToSign (b t)) d m n := by
  apply discOffset_congr (f := f) (g := fun t => fin2ToSign (b t)) (d := d) (m := m) (n := n)
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
