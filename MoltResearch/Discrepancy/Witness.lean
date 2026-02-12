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

/-- Convert a `DiscrepancyWitness` to the underlying `HasDiscrepancyAtLeast`. -/
def DiscrepancyWitness.toHas {f C} (w : DiscrepancyWitness f C) :
    HasDiscrepancyAtLeast f C :=
  ⟨w.d, w.n, w.hd, w.hgt⟩

/-- Convert a `DiscrepancyWitnessPos` to the underlying `HasDiscrepancyAtLeast`. -/
def DiscrepancyWitnessPos.toHas {f C} (w : DiscrepancyWitnessPos f C) :
    HasDiscrepancyAtLeast f C :=
  ⟨w.d, w.n, w.hd, w.hgt⟩

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

/-- Convert an `AffineDiscrepancyWitness` to the underlying `HasAffineDiscrepancyAtLeast`. -/
def AffineDiscrepancyWitness.toHas {f C} (w : AffineDiscrepancyWitness f C) :
    HasAffineDiscrepancyAtLeast f C :=
  ⟨w.a, w.d, w.n, w.hd, w.hgt⟩

/-- Convert an `AffineDiscrepancyWitnessPos` to the underlying `HasAffineDiscrepancyAtLeast`. -/
def AffineDiscrepancyWitnessPos.toHas {f C} (w : AffineDiscrepancyWitnessPos f C) :
    HasAffineDiscrepancyAtLeast f C :=
  ⟨w.a, w.d, w.n, w.hd, w.hgt⟩

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

/-- The `d` component of an `AffineDiscrepancyWitnessPos` is at least `1`. -/
lemma AffineDiscrepancyWitnessPos.d_ge_one {f C} (w : _root_.MoltResearch.AffineDiscrepancyWitnessPos f C) :
    w.d ≥ 1 := by
  exact Nat.succ_le_of_lt w.hd

end MoltResearch
