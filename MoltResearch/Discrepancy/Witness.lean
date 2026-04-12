import MoltResearch.Discrepancy.Affine

namespace MoltResearch

/-! Discrepancy witnesses -/

/-- Homogeneous discrepancy witness. -/
structure DiscrepancyWitness (f : ℕ → ℤ) (C : ℕ) where
  d : ℕ
  n : ℕ
  hd : d > 0
  hgt : Int.natAbs (apSum f d n) > C

/-- Homogeneous discrepancy witness with a positive `n`. -/
structure DiscrepancyWitnessPos (f : ℕ → ℤ) (C : ℕ) extends DiscrepancyWitness f C where
  hn : n > 0

/-- Homogeneous discrepancy witness with the step-size side condition written as `d ≥ 1`.

This is a small “step-positivity normal form”: it avoids the annoying `d > 0` vs `d ≥ 1`
conversion dance in downstream statements.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Step-positivity normal form.
-/
structure DiscrepancyWitnessGeOne (f : ℕ → ℤ) (C : ℕ) where
  d : ℕ
  n : ℕ
  hd : d ≥ 1
  hgt : Int.natAbs (apSum f d n) > C

/-- Convert a `DiscrepancyWitness` to the underlying `HasDiscrepancyAtLeast`. -/
def DiscrepancyWitness.toHas {f C} (w : DiscrepancyWitness f C) :
    HasDiscrepancyAtLeast f C :=
  ⟨w.d, w.n, w.hd, w.hgt⟩

/-- Convert a `DiscrepancyWitnessPos` to the underlying `HasDiscrepancyAtLeast`. -/
def DiscrepancyWitnessPos.toHas {f C} (w : DiscrepancyWitnessPos f C) :
    HasDiscrepancyAtLeast f C :=
  ⟨w.d, w.n, w.hd, w.hgt⟩

/-- Convert a `DiscrepancyWitnessGeOne` to the underlying `HasDiscrepancyAtLeast`. -/
def DiscrepancyWitnessGeOne.toHas {f C} (w : DiscrepancyWitnessGeOne f C) :
    HasDiscrepancyAtLeast f C :=
  ⟨w.d, w.n, (Nat.succ_le_iff).1 w.hd, w.hgt⟩

/-- Turn a `HasDiscrepancyAtLeast` into a `DiscrepancyWitness`. -/
noncomputable def HasDiscrepancyAtLeast.toWitness {f C} (h : HasDiscrepancyAtLeast f C) :
    DiscrepancyWitness f C := by
  classical
  let d := Classical.choose h
  have h₁ := Classical.choose_spec h
  let n := Classical.choose h₁
  have h₂ := Classical.choose_spec h₁
  exact
    { d := d
    , n := n
    , hd := h₂.1
    , hgt := h₂.2 }

/-- Turn a `HasDiscrepancyAtLeast` into a `DiscrepancyWitnessGeOne`.

This is the `d ≥ 1` witness normal form.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Step-positivity normal form.
-/
noncomputable def HasDiscrepancyAtLeast.toWitnessGeOne {f C} (h : HasDiscrepancyAtLeast f C) :
    DiscrepancyWitnessGeOne f C := by
  classical
  let hex : ∃ d n, d ≥ 1 ∧ Int.natAbs (apSum f d n) > C :=
    h.exists_witness_d_ge_one (C := C)
  let d := Classical.choose hex
  have hd' := Classical.choose_spec hex
  let n := Classical.choose hd'
  have hn' := Classical.choose_spec hd'
  exact { d := d, n := n, hd := hn'.1, hgt := hn'.2 }

/-- Turn a `HasDiscrepancyAtLeast` into a `DiscrepancyWitnessPos`. -/
noncomputable def HasDiscrepancyAtLeast.toWitnessPos {f C} (h : HasDiscrepancyAtLeast f C) :
    DiscrepancyWitnessPos f C := by
  classical
  let hpos := h.exists_witness_pos
  let d := Classical.choose hpos
  have h₁ := Classical.choose_spec hpos
  let n := Classical.choose h₁
  have h₂ := Classical.choose_spec h₁
  exact
    { d := d
    , n := n
    , hd := h₂.1
    , hn := h₂.2.1
    , hgt := h₂.2.2 }

/-- Equivalence between `HasDiscrepancyAtLeast` and a nonempty `DiscrepancyWitness`. -/
theorem HasDiscrepancyAtLeast.iff_nonempty_witness {f C} :
    HasDiscrepancyAtLeast f C ↔ Nonempty (DiscrepancyWitness f C) := by
  constructor
  · intro h
    exact ⟨h.toWitness⟩
  · rintro ⟨w⟩
    exact w.toHas

/-- Equivalence between `HasDiscrepancyAtLeast` and a nonempty `DiscrepancyWitnessPos`. -/
theorem HasDiscrepancyAtLeast.iff_nonempty_witnessPos {f C} :
    HasDiscrepancyAtLeast f C ↔ Nonempty (DiscrepancyWitnessPos f C) := by
  constructor
  · intro h
    exact ⟨h.toWitnessPos⟩
  · rintro ⟨w⟩
    exact w.toHas

/-- Equivalence between `HasDiscrepancyAtLeast` and a nonempty `DiscrepancyWitnessGeOne`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Step-positivity normal form.
-/
theorem HasDiscrepancyAtLeast.iff_nonempty_witnessGeOne {f C} :
    HasDiscrepancyAtLeast f C ↔ Nonempty (DiscrepancyWitnessGeOne f C) := by
  constructor
  · intro h
    exact ⟨h.toWitnessGeOne⟩
  · rintro ⟨w⟩
    exact w.toHas

/-- Normal form: “unbounded discrepancy” as a `Nonempty` witness family. -/
theorem forall_hasDiscrepancyAtLeast_iff_forall_nonempty_witnessPos (f : ℕ → ℤ) :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔ (∀ C : ℕ, Nonempty (DiscrepancyWitnessPos f C)) := by
  simp [HasDiscrepancyAtLeast.iff_nonempty_witnessPos]

/-- The `d` component of a `DiscrepancyWitnessPos` is at least `1`. -/
lemma DiscrepancyWitnessPos.d_ge_one {f C} (w : DiscrepancyWitnessPos f C) :
    w.d ≥ 1 := by
  exact Nat.succ_le_of_lt w.hd

/-- Affine discrepancy witness. -/
structure AffineDiscrepancyWitness (f : ℕ → ℤ) (C : ℕ) where
  a : ℕ
  d : ℕ
  n : ℕ
  hd : d > 0
  hgt : Int.natAbs (apSumFrom f a d n) > C

/-- Affine discrepancy witness with a positive `n`. -/
structure AffineDiscrepancyWitnessPos (f : ℕ → ℤ) (C : ℕ) extends AffineDiscrepancyWitness f C where
  hn : n > 0

/-- Affine discrepancy witness with the step-size side condition written as `d ≥ 1`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Step-positivity normal form.
-/
structure AffineDiscrepancyWitnessGeOne (f : ℕ → ℤ) (C : ℕ) where
  a : ℕ
  d : ℕ
  n : ℕ
  hd : d ≥ 1
  hgt : Int.natAbs (apSumFrom f a d n) > C

/-- Convert an `AffineDiscrepancyWitness` to the underlying `HasAffineDiscrepancyAtLeast`. -/
def AffineDiscrepancyWitness.toHas {f C} (w : AffineDiscrepancyWitness f C) :
    HasAffineDiscrepancyAtLeast f C :=
  ⟨w.a, w.d, w.n, w.hd, w.hgt⟩

/-- Convert an `AffineDiscrepancyWitnessPos` to the underlying `HasAffineDiscrepancyAtLeast`. -/
def AffineDiscrepancyWitnessPos.toHas {f C} (w : AffineDiscrepancyWitnessPos f C) :
    HasAffineDiscrepancyAtLeast f C :=
  ⟨w.a, w.d, w.n, w.hd, w.hgt⟩

/-- Convert an `AffineDiscrepancyWitnessGeOne` to the underlying `HasAffineDiscrepancyAtLeast`. -/
def AffineDiscrepancyWitnessGeOne.toHas {f C} (w : AffineDiscrepancyWitnessGeOne f C) :
    HasAffineDiscrepancyAtLeast f C :=
  ⟨w.a, w.d, w.n, (Nat.succ_le_iff).1 w.hd, w.hgt⟩

/-- Turn a `HasAffineDiscrepancyAtLeast` into an `AffineDiscrepancyWitness`. -/
noncomputable def HasAffineDiscrepancyAtLeast.toWitness {f C} (h : HasAffineDiscrepancyAtLeast f C) :
    _root_.MoltResearch.AffineDiscrepancyWitness f C := by
  classical
  let a := Classical.choose h
  have h₁ := Classical.choose_spec h
  let d := Classical.choose h₁
  have h₂ := Classical.choose_spec h₁
  let n := Classical.choose h₂
  have h₃ := Classical.choose_spec h₂
  exact
    { a := a
    , d := d
    , n := n
    , hd := h₃.1
    , hgt := h₃.2 }

/-- Turn a `HasAffineDiscrepancyAtLeast` into an `AffineDiscrepancyWitnessPos`. -/
noncomputable def HasAffineDiscrepancyAtLeast.toWitnessPos {f C} (h : HasAffineDiscrepancyAtLeast f C) :
    _root_.MoltResearch.AffineDiscrepancyWitnessPos f C := by
  classical
  let hpos := h.exists_witness_pos
  let a := Classical.choose hpos
  have h₁ := Classical.choose_spec hpos
  let d := Classical.choose h₁
  have h₂ := Classical.choose_spec h₁
  let n := Classical.choose h₂
  have h₃ := Classical.choose_spec h₂
  exact
    { a := a
    , d := d
    , n := n
    , hd := h₃.1
    , hn := h₃.2.1
    , hgt := h₃.2.2 }

/-- Turn a `HasAffineDiscrepancyAtLeast` into an `AffineDiscrepancyWitnessGeOne`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Step-positivity normal form.
-/
noncomputable def HasAffineDiscrepancyAtLeast.toWitnessGeOne {f C} (h : HasAffineDiscrepancyAtLeast f C) :
    AffineDiscrepancyWitnessGeOne f C := by
  classical
  let hex : ∃ a d n, d ≥ 1 ∧ Int.natAbs (apSumFrom f a d n) > C :=
    h.exists_witness_d_ge_one (C := C)
  let a := Classical.choose hex
  have ha' := Classical.choose_spec hex
  let d := Classical.choose ha'
  have hd' := Classical.choose_spec ha'
  let n := Classical.choose hd'
  have hn' := Classical.choose_spec hd'
  exact { a := a, d := d, n := n, hd := hn'.1, hgt := hn'.2 }

/-- Equivalence between `HasAffineDiscrepancyAtLeast` and a nonempty `AffineDiscrepancyWitness`. -/
theorem HasAffineDiscrepancyAtLeast.iff_nonempty_witness {f C} :
    HasAffineDiscrepancyAtLeast f C ↔ Nonempty (AffineDiscrepancyWitness f C) := by
  constructor
  · intro h
    exact ⟨h.toWitness⟩
  · rintro ⟨w⟩
    exact w.toHas

/-- Equivalence between `HasAffineDiscrepancyAtLeast` and a nonempty `AffineDiscrepancyWitnessPos`. -/
theorem HasAffineDiscrepancyAtLeast.iff_nonempty_witnessPos {f C} :
    HasAffineDiscrepancyAtLeast f C ↔ Nonempty (AffineDiscrepancyWitnessPos f C) := by
  constructor
  · intro h
    exact ⟨h.toWitnessPos⟩
  · rintro ⟨w⟩
    exact w.toHas

/-- Equivalence between `HasAffineDiscrepancyAtLeast` and a nonempty `AffineDiscrepancyWitnessGeOne`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Step-positivity normal form.
-/
theorem HasAffineDiscrepancyAtLeast.iff_nonempty_witnessGeOne {f C} :
    HasAffineDiscrepancyAtLeast f C ↔ Nonempty (AffineDiscrepancyWitnessGeOne f C) := by
  constructor
  · intro h
    exact ⟨h.toWitnessGeOne⟩
  · rintro ⟨w⟩
    exact w.toHas

/-- Normal form: “unbounded affine discrepancy” as a `Nonempty` witness family. -/
theorem forall_hasAffineDiscrepancyAtLeast_iff_forall_nonempty_witnessPos (f : ℕ → ℤ) :
    (∀ C : ℕ, HasAffineDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ, Nonempty (AffineDiscrepancyWitnessPos f C)) := by
  simp [HasAffineDiscrepancyAtLeast.iff_nonempty_witnessPos]

/-- The `d` component of an `AffineDiscrepancyWitnessPos` is at least `1`. -/
lemma AffineDiscrepancyWitnessPos.d_ge_one {f C} (w : _root_.MoltResearch.AffineDiscrepancyWitnessPos f C) :
    w.d ≥ 1 := by
  exact Nat.succ_le_of_lt w.hd

/-! ### Witness-level translation between homogeneous and affine discrepancy

These lemmas package the idea that a homogeneous discrepancy witness for the **shifted** sequence
`k ↦ f (k + a)` is the same data as an affine discrepancy witness for `f` with offset `a`.

This is intentionally witness-level (not a global invariance statement), and is meant to be used
as glue when switching normal forms.
-/

/-- Convert a `DiscrepancyWitness` for the shifted sequence `k ↦ f (k + a)` into an
`AffineDiscrepancyWitness` for `f` with offset `a`. -/
def DiscrepancyWitness.toAffineWitness {f : ℕ → ℤ} {C a : ℕ}
    (w : DiscrepancyWitness (fun k => f (k + a)) C) :
    AffineDiscrepancyWitness f C := by
  refine
    { a := a
      d := w.d
      n := w.n
      hd := w.hd
      hgt := ?_ }
  -- Rewrite the homogeneous sum on the shifted sequence as an affine sum on `f`.
  simpa [natAbs_apSum_shift_add_eq_natAbs_apSumFrom] using w.hgt

/-- Convert a `DiscrepancyWitnessPos` for the shifted sequence into an
`AffineDiscrepancyWitnessPos`. -/
def DiscrepancyWitnessPos.toAffineWitnessPos {f : ℕ → ℤ} {C a : ℕ}
    (w : DiscrepancyWitnessPos (fun k => f (k + a)) C) :
    AffineDiscrepancyWitnessPos f C := by
  refine
    { a := a
      d := w.d
      n := w.n
      hd := w.hd
      hn := w.hn
      hgt := ?_ }
  simpa [natAbs_apSum_shift_add_eq_natAbs_apSumFrom] using w.hgt

/-- From `HasDiscrepancyAtLeast (k ↦ f (k + a)) C` produce a nonempty affine witness for `f`. -/
theorem HasDiscrepancyAtLeast.shift_add_toAffineWitness {f : ℕ → ℤ} {C a : ℕ}
    (h : HasDiscrepancyAtLeast (fun k => f (k + a)) C) :
    Nonempty (AffineDiscrepancyWitness f C) := by
  classical
  refine ⟨(h.toWitness).toAffineWitness (f := f) (C := C) (a := a)⟩

/-- From `HasDiscrepancyAtLeast (k ↦ f (k + a)) C` produce a nonempty affine witness with `n > 0`. -/
theorem HasDiscrepancyAtLeast.shift_add_toAffineWitnessPos {f : ℕ → ℤ} {C a : ℕ}
    (h : HasDiscrepancyAtLeast (fun k => f (k + a)) C) :
    Nonempty (AffineDiscrepancyWitnessPos f C) := by
  classical
  refine ⟨(h.toWitnessPos).toAffineWitnessPos (f := f) (C := C) (a := a)⟩

end MoltResearch
