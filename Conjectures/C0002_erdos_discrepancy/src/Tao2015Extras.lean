import Conjectures.C0002_erdos_discrepancy.src.Tao2015

/-!
# Tao 2015 (Track C): small interface extras

This module is **Conjectures-only**: it may contain axiom stubs (and, if needed, `sorry`), but the intent here is to add tiny
helper lemmas that make the stage interfaces easier to consume.

Nothing in this file should edit or depend on implementation details under `MoltResearch/`.
-/

namespace MoltResearch

namespace Tao2015

/-!
## Small nucleus normal forms

These are tiny rewrite lemmas that show up repeatedly when consuming the stage interfaces.
They live in this Conjectures-only file to avoid growing the verified substrate.
-/

/-
Note: `Tao2015` already provides the lemma
`hasDiscrepancyAtLeastAlong_iff_exists_natAbs_apSum_gt'`.

`Tao2015Extras` is intended only for additional (non-duplicated) convenience lemmas.
-/


/-
Note: the bounded-discrepancy-along nucleus normal form lives in `Tao2015` as
`boundedDiscrepancyAlong_iff_exists_forall_natAbs_apSum_le`.
-/


/- Normal form: the affine-tail nucleus at start `m*d` is the bundled offset nucleus.

Provided by `Conjectures.C0002_erdos_discrepancy.src.Tao2015` as
`Tao2015.apSumFrom_mul_eq_apSumOffset` and
`Tao2015.discOffset_eq_natAbs_apSumFrom_mul`; we just use them in this file.
-/

/-- Paper-notation normal form: affine-tail nuclei at start `m*d` written as an interval sum.

This is `apSumFrom_mul_eq_apSumOffset` composed with `natAbs_apSumOffset_eq_natAbs_sum_Icc`.
-/
theorem natAbs_apSumFrom_mul_eq_natAbs_sum_Icc (f : ℕ → ℤ) (d m n : ℕ) :
    Int.natAbs (apSumFrom f (m * d) d n) =
      Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) := by
  calc
    Int.natAbs (apSumFrom f (m * d) d n) = Int.natAbs (apSumOffset f d m n) := by
      exact
        congrArg Int.natAbs
          (apSumFrom_mul_eq_apSumOffset (f := f) (d := d) (m := m) (n := n))
    _ =
        Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) := by
      simpa using
        (natAbs_apSumOffset_eq_natAbs_sum_Icc (f := f) (d := d) (m := m) (n := n))

/-
Note: `Tao2015` already provides the interval-sum normal form

  Tao2015.discOffset_eq_natAbs_sum_Icc

so we deliberately do not restate it here. (Otherwise this file cannot be imported together with
`Tao2015`.)
-/

/-- Inequality normal form: `discOffset f d m n < B` rewritten using affine-tail nuclei. -/
theorem discOffset_lt_iff_natAbs_apSumFrom_mul_lt (f : ℕ → ℤ) (d m n B : ℕ) :
    discOffset f d m n < B ↔ Int.natAbs (apSumFrom f (m * d) d n) < B := by
  simp [discOffset_eq_natAbs_apSumFrom_mul (f := f) (d := d) (m := m) (n := n)]

/-- Inequality normal form: `discOffset f d m n > B` rewritten using affine-tail nuclei. -/
theorem discOffset_gt_iff_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ) (d m n B : ℕ) :
    discOffset f d m n > B ↔ Int.natAbs (apSumFrom f (m * d) d n) > B := by
  simp [discOffset_eq_natAbs_apSumFrom_mul (f := f) (d := d) (m := m) (n := n)]

/-- Inequality normal form: `B < discOffset f d m n` rewritten using affine-tail nuclei. -/
theorem lt_discOffset_iff_lt_natAbs_apSumFrom_mul (f : ℕ → ℤ) (d m n B : ℕ) :
    B < discOffset f d m n ↔ B < Int.natAbs (apSumFrom f (m * d) d n) := by
  simp [discOffset_eq_natAbs_apSumFrom_mul (f := f) (d := d) (m := m) (n := n)]

/-- Inequality normal form: `discOffset f d m n ≤ B` rewritten using affine-tail nuclei. -/
theorem discOffset_le_iff_natAbs_apSumFrom_mul_le (f : ℕ → ℤ) (d m n B : ℕ) :
    discOffset f d m n ≤ B ↔ Int.natAbs (apSumFrom f (m * d) d n) ≤ B := by
  simp [discOffset_eq_natAbs_apSumFrom_mul (f := f) (d := d) (m := m) (n := n)]

/-- Inequality normal form: `B ≤ discOffset f d m n` rewritten using affine-tail nuclei. -/
theorem le_discOffset_iff_le_natAbs_apSumFrom_mul (f : ℕ → ℤ) (d m n B : ℕ) :
    B ≤ discOffset f d m n ↔ B ≤ Int.natAbs (apSumFrom f (m * d) d n) := by
  simp [discOffset_eq_natAbs_apSumFrom_mul (f := f) (d := d) (m := m) (n := n)]

/-- Normal form: boundedness of `discOffset f d m` expressed using affine-tail nuclei.

This avoids unfolding `discOffset` and repeatedly rewriting `apSumOffset` into an `apSumFrom` tail.
-/
theorem boundedDiscOffset_iff_forall_natAbs_apSumFrom_mul_le (f : ℕ → ℤ) (d m B : ℕ) :
    BoundedDiscOffset f d m B ↔ ∀ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) ≤ B := by
  constructor
  · intro h n
    have hn : discOffset f d m n ≤ B := h n
    simpa [discOffset_eq_natAbs_apSumFrom_mul (f := f) (d := d) (m := m) (n := n)] using hn
  · intro h n
    have hn : Int.natAbs (apSumFrom f (m * d) d n) ≤ B := h n
    simpa [discOffset_eq_natAbs_apSumFrom_mul (f := f) (d := d) (m := m) (n := n)] using hn

/-- Packaging normal form: existence of a bundled offset bound expressed via affine-tail nuclei.

This is just `BoundedDiscOffset` packaged under an existential quantifier and rewritten using
`boundedDiscOffset_iff_forall_natAbs_apSumFrom_mul_le`.
-/
theorem exists_boundedDiscOffset_iff_exists_forall_natAbs_apSumFrom_mul_le (f : ℕ → ℤ) (d m : ℕ) :
    (∃ B : ℕ, BoundedDiscOffset f d m B) ↔
      (∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) ≤ B) := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    exact
      (boundedDiscOffset_iff_forall_natAbs_apSumFrom_mul_le (f := f) (d := d) (m := m) (B := B)).1
        hB
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    exact
      (boundedDiscOffset_iff_forall_natAbs_apSumFrom_mul_le (f := f) (d := d) (m := m) (B := B)).2
        hB

/-- Normal form: unbounded offset discrepancy means there is no uniform bundled offset-nucleus bound.

Negation-normal form:
`¬ ∃ B, ∀ n, Int.natAbs (apSumOffset f d m n) ≤ B`.

This can be convenient when proving unboundedness by contradiction.
-/
theorem unboundedDiscOffset_iff_not_exists_forall_natAbs_apSumOffset_le (f : ℕ → ℤ) (d m : ℕ) :
    UnboundedDiscOffset f d m ↔
      (¬ ∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumOffset f d m n) ≤ B) := by
  -- Rewrite unboundedness through the negation-normal-form boundedness predicate, then unfold the
  -- relevant definitions.
  simpa [BoundedDiscOffset, discOffset, -natAbs_apSumOffset_eq_discOffset] using
    (Tao2015.unboundedDiscOffset_iff_not_exists_boundedDiscOffset (f := f) (d := d) (m := m))

-- moved to `Conjectures.C0002_erdos_discrepancy.src.Tao2015` (core interface)

/-- Normal form: unbounded offset discrepancy means there is no uniform affine-tail nucleus bound.

Negation-normal form:
`¬ ∃ B, ∀ n, Int.natAbs (apSumFrom f (m*d) d n) ≤ B`.

This can be convenient when proving unboundedness by contradiction.
-/
theorem unboundedDiscOffset_iff_not_exists_forall_natAbs_apSumFrom_mul_le (f : ℕ → ℤ) (d m : ℕ) :
    UnboundedDiscOffset f d m ↔
      (¬ ∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) ≤ B) := by
  -- Rewrite through the negation-normal-form boundedness predicate, then use the affine-tail
  -- normal form for `BoundedDiscOffset`.
  simpa [boundedDiscOffset_iff_forall_natAbs_apSumFrom_mul_le (f := f) (d := d) (m := m)] using
    (Tao2015.unboundedDiscOffset_iff_not_exists_boundedDiscOffset (f := f) (d := d) (m := m))

/-- Normal form: boundedness of `discOffset f d m` expressed directly using the bundled offset nucleus.

This avoids having to unfold `discOffset` at each call site.
-/
theorem boundedDiscOffset_iff_forall_natAbs_apSumOffset_le (f : ℕ → ℤ) (d m B : ℕ) :
    BoundedDiscOffset f d m B ↔ ∀ n : ℕ, Int.natAbs (apSumOffset f d m n) ≤ B := by
  constructor
  · intro h n
    have hn : discOffset f d m n ≤ B := h n
    unfold discOffset at hn
    exact hn
  · intro h n
    have hn : Int.natAbs (apSumOffset f d m n) ≤ B := h n
    unfold discOffset
    exact hn

/-- Packaging normal form: existence of a bundled offset bound expressed via offset nuclei.

This is `BoundedDiscOffset` packaged under an existential quantifier and rewritten using
`boundedDiscOffset_iff_forall_natAbs_apSumOffset_le`.
-/
theorem exists_boundedDiscOffset_iff_exists_forall_natAbs_apSumOffset_le (f : ℕ → ℤ) (d m : ℕ) :
    (∃ B : ℕ, BoundedDiscOffset f d m B) ↔
      (∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumOffset f d m n) ≤ B) := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    exact
      (boundedDiscOffset_iff_forall_natAbs_apSumOffset_le (f := f) (d := d) (m := m) (B := B)).1
        hB
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    exact
      (boundedDiscOffset_iff_forall_natAbs_apSumOffset_le (f := f) (d := d) (m := m) (B := B)).2
        hB

/-- Negation-normal-form packaging: nonexistence of a bundled offset bound expressed via offset nuclei.

This is `exists_boundedDiscOffset_iff_exists_forall_natAbs_apSumOffset_le` under `not`.
-/
theorem not_exists_boundedDiscOffset_iff_not_exists_forall_natAbs_apSumOffset_le
    (f : ℕ → ℤ) (d m : ℕ) :
    (¬ ∃ B : ℕ, BoundedDiscOffset f d m B) ↔
      (¬ ∃ B : ℕ, ∀ n : ℕ, Int.natAbs (apSumOffset f d m n) ≤ B) := by
  exact
    not_congr
      (exists_boundedDiscOffset_iff_exists_forall_natAbs_apSumOffset_le (f := f) (d := d) (m := m))

/-- Paper-notation normal form: boundedness of `discOffset f d m` expressed as interval sums on `Icc`.

This rewrites the bundled offset nuclei `apSumOffset f d m n` as the shifted progression sums
`∑ i ∈ Icc (m+1) (m+n), f (i*d)`.
-/
theorem boundedDiscOffset_iff_forall_natAbs_sum_Icc_offset_le (f : ℕ → ℤ) (d m B : ℕ) :
    BoundedDiscOffset f d m B ↔
      ∀ n : ℕ,
        Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) ≤ B := by
  constructor
  · intro h n
    have hn : Int.natAbs (apSumOffset f d m n) ≤ B := by
      have hn' : discOffset f d m n ≤ B := h n
      unfold discOffset at hn'
      exact hn'
    simpa [natAbs_apSumOffset_eq_natAbs_sum_Icc (f := f) (d := d) (m := m) (n := n)] using hn
  · intro h n
    have hn : Int.natAbs (apSumOffset f d m n) ≤ B := by
      simpa [natAbs_apSumOffset_eq_natAbs_sum_Icc (f := f) (d := d) (m := m) (n := n)] using h n
    unfold discOffset
    exact hn

/-- Packaging normal form: existence of a bundled offset bound expressed as interval sums on `Icc`.

This is `BoundedDiscOffset` packaged under an existential quantifier and rewritten using
`boundedDiscOffset_iff_forall_natAbs_sum_Icc_offset_le`.
-/
theorem exists_boundedDiscOffset_iff_exists_forall_natAbs_sum_Icc_offset_le (f : ℕ → ℤ) (d m : ℕ) :
    (∃ B : ℕ, BoundedDiscOffset f d m B) ↔
      (∃ B : ℕ,
        ∀ n : ℕ,
          Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) ≤ B) := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    exact
      (boundedDiscOffset_iff_forall_natAbs_sum_Icc_offset_le (f := f) (d := d) (m := m) (B := B)).1
        hB
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    exact
      (boundedDiscOffset_iff_forall_natAbs_sum_Icc_offset_le (f := f) (d := d) (m := m) (B := B)).2
        hB

/-- Normal form: unbounded offset discrepancy expressed directly using the bundled offset nucleus.

Since `discOffset f d m n` is definitionally `Int.natAbs (apSumOffset f d m n)`, this lemma lets
later stages avoid unfolding `discOffset` by hand.
-/
theorem unboundedDiscOffset_iff_forall_exists_natAbs_apSumOffset_gt (f : ℕ → ℤ) (d m : ℕ) :
    UnboundedDiscOffset f d m ↔
      (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumOffset f d m n)) := by
  simpa using
    (UnboundedDiscOffset.iff_forall_exists_natAbs_apSumOffset_gt (f := f) (d := d) (m := m))

/-- Variant of `unboundedDiscOffset_iff_forall_exists_natAbs_apSumOffset_gt` with the inequality
written as `Int.natAbs ... > B` (often the normal form used by Stage interfaces).
-/
theorem unboundedDiscOffset_iff_forall_exists_natAbs_apSumOffset_gt' (f : ℕ → ℤ) (d m : ℕ) :
    UnboundedDiscOffset f d m ↔
      (∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumOffset f d m n) > B) := by
  simpa [gt_iff_lt] using
    (unboundedDiscOffset_iff_forall_exists_natAbs_apSumOffset_gt (f := f) (d := d) (m := m))

/-- Witness-positivity variant of `unboundedDiscOffset_iff_forall_exists_natAbs_apSumOffset_gt'`.

Since `apSumOffset f d m 0 = 0`, any unboundedness witness length can be taken positive.
-/
theorem unboundedDiscOffset_iff_forall_exists_natAbs_apSumOffset_gt'_witness_pos (f : ℕ → ℤ)
    (d m : ℕ) :
    UnboundedDiscOffset f d m ↔
      (∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ Int.natAbs (apSumOffset f d m n) > B) := by
  constructor
  · intro hunb B
    simpa using
      (forall_exists_natAbs_apSumOffset_gt_witness_pos (f := f) (d := d) (m := m) hunb B)
  · intro h
    refine
      (unboundedDiscOffset_iff_forall_exists_natAbs_apSumOffset_gt' (f := f) (d := d) (m := m)).2
        ?_
    intro B
    rcases h B with ⟨n, hnpos, hn⟩
    exact ⟨n, hn⟩

/-- Paper-notation normal form: unbounded offset discrepancy expressed as interval sums on `Icc`.

This rewrites the offset nuclei `apSumOffset f d m n` as the shifted progression sums
`∑ i ∈ Icc (m+1) (m+n), f (i*d)`.
-/
theorem unboundedDiscOffset_iff_forall_exists_natAbs_sum_Icc_offset_gt' (f : ℕ → ℤ) (d m : ℕ) :
    UnboundedDiscOffset f d m ↔
      (∀ B : ℕ, ∃ n : ℕ,
        Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) > B) := by
  constructor
  · intro hunb B
    rcases
        (unboundedDiscOffset_iff_forall_exists_natAbs_apSumOffset_gt' (f := f) (d := d) (m := m)).1
          hunb B with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [Tao2015.natAbs_apSumOffset_eq_natAbs_sum_Icc (f := f) (d := d) (m := m) (n := n)] using
      hn
  · intro h
    refine
      (unboundedDiscOffset_iff_forall_exists_natAbs_apSumOffset_gt' (f := f) (d := d) (m := m)).2
        ?_
    intro B
    rcases h B with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [Tao2015.natAbs_apSumOffset_eq_natAbs_sum_Icc (f := f) (d := d) (m := m) (n := n)] using
      hn

/-- Normal form: unbounded offset discrepancy expressed directly using the affine-tail nucleus.

This is a small helper for later analytic stages: it avoids repeatedly unfolding `discOffset` and
rewriting `apSumOffset` to `apSumFrom` tails.
-/
theorem unboundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ) (d m : ℕ) :
    UnboundedDiscOffset f d m ↔
      (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumFrom f (m * d) d n)) := by
  simpa using
    (UnboundedDiscOffset.iff_forall_exists_natAbs_apSumFrom_mul_gt (f := f) (d := d) (m := m))

/-- Variant of `unboundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt` with the inequality
written as `Int.natAbs ... > B` (often the normal form used by Stage interfaces).
-/
theorem unboundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt' (f : ℕ → ℤ) (d m : ℕ) :
    UnboundedDiscOffset f d m ↔
      (∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) > B) := by
  simpa [gt_iff_lt] using
    (unboundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt (f := f) (d := d) (m := m))

/-- Witness-positive variant of `unboundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt'`.

Since `apSumFrom f (m*d) d 0 = 0`, the unboundedness witness length can always be taken positive.
-/
theorem unboundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt'_witness_pos (f : ℕ → ℤ)
    (d m : ℕ) :
    UnboundedDiscOffset f d m ↔
      (∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ Int.natAbs (apSumFrom f (m * d) d n) > B) := by
  constructor
  · intro hunb B
    simpa using
      (UnboundedDiscOffset.forall_exists_natAbs_apSumFrom_mul_gt_witness_pos (f := f) (d := d)
        (m := m) hunb B)
  · intro h
    refine
      (unboundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt' (f := f) (d := d) (m := m)).2
        ?_
    intro B
    rcases h B with ⟨n, hnpos, hn⟩
    exact ⟨n, hn⟩

/-- Witness-positive variant of `unboundedDiscOffset_iff_forall_exists_natAbs_sum_Icc_offset_gt'`.

When `n = 0`, the interval `Icc (m+1) (m+n)` is empty, so the sum is `0`; thus any unboundedness
witness can be taken with `n > 0`.
-/
theorem unboundedDiscOffset_iff_forall_exists_natAbs_sum_Icc_offset_gt'_witness_pos (f : ℕ → ℤ)
    (d m : ℕ) :
    UnboundedDiscOffset f d m ↔
      (∀ B : ℕ, ∃ n : ℕ, n > 0 ∧
        Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) > B) := by
  constructor
  · intro hunb B
    rcases
        (unboundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt'_witness_pos (f := f)
              (d := d) (m := m)).1
          hunb B with
      ⟨n, hnpos, hn⟩
    refine ⟨n, hnpos, ?_⟩
    simpa [natAbs_apSumFrom_mul_eq_natAbs_sum_Icc (f := f) (d := d) (m := m) (n := n)] using hn
  · intro h
    refine
      (unboundedDiscOffset_iff_forall_exists_natAbs_apSumOffset_gt' (f := f) (d := d) (m := m)).2
        ?_
    intro B
    rcases h B with ⟨n, hnpos, hn⟩
    refine ⟨n, ?_⟩
    simpa [Tao2015.natAbs_apSumOffset_eq_natAbs_sum_Icc (f := f) (d := d) (m := m) (n := n)] using hn

/-- Normal form: the negation-normal-form boundedness statement
`¬ ∃ B, BoundedDiscOffset f d m B` expressed directly using bundled offset nuclei.

This is just the composition of
`Tao2015.unboundedDiscOffset_iff_not_exists_boundedDiscOffset` and
`unboundedDiscOffset_iff_forall_exists_natAbs_apSumOffset_gt`.
-/
theorem not_exists_boundedDiscOffset_iff_forall_exists_natAbs_apSumOffset_gt (f : ℕ → ℤ)
    (d m : ℕ) :
    (¬ ∃ B : ℕ, BoundedDiscOffset f d m B) ↔
      (∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumOffset f d m n) > B) := by
  -- Rewrite the negation-normal form through the witness predicate `UnboundedDiscOffset`.
  simpa [gt_iff_lt] using
    (Tao2015.unboundedDiscOffset_iff_not_exists_boundedDiscOffset (f := f) (d := d) (m := m)).symm.trans
      (unboundedDiscOffset_iff_forall_exists_natAbs_apSumOffset_gt (f := f) (d := d) (m := m))

/-- Normal form: the negation-normal-form boundedness statement
`¬ ∃ B, BoundedDiscOffset f d m B` expressed directly using affine-tail nuclei.

This is just the composition of
`Tao2015.unboundedDiscOffset_iff_not_exists_boundedDiscOffset` and
`unboundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt'`.
-/
theorem not_exists_boundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt (f : ℕ → ℤ)
    (d m : ℕ) :
    (¬ ∃ B : ℕ, BoundedDiscOffset f d m B) ↔
      (∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (m * d) d n) > B) := by
  -- Rewrite the negation-normal form through the witness predicate `UnboundedDiscOffset`.
  exact
    (Tao2015.unboundedDiscOffset_iff_not_exists_boundedDiscOffset (f := f) (d := d) (m := m)).symm.trans
      (unboundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt' (f := f) (d := d) (m := m))

/-- Witness-positive variant of `not_exists_boundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt`.

Since `apSumFrom f (m*d) d 0 = 0`, any unboundedness witness length can be taken positive.
-/
theorem not_exists_boundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt'_witness_pos
    (f : ℕ → ℤ) (d m : ℕ) :
    (¬ ∃ B : ℕ, BoundedDiscOffset f d m B) ↔
      (∀ B : ℕ, ∃ n : ℕ, n > 0 ∧ Int.natAbs (apSumFrom f (m * d) d n) > B) := by
  simpa using
    (Tao2015.unboundedDiscOffset_iff_not_exists_boundedDiscOffset (f := f) (d := d) (m := m)).symm.trans
      (unboundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt'_witness_pos (f := f) (d := d)
        (m := m))

/-- Paper-notation normal form: the negation-normal-form boundedness statement
`¬ ∃ B, BoundedDiscOffset f d m B` expressed using interval sums on `Icc (m+1) (m+n)`.

This is the composition of `Tao2015.unboundedDiscOffset_iff_not_exists_boundedDiscOffset` and
`unboundedDiscOffset_iff_forall_exists_natAbs_sum_Icc_offset_gt'`.
-/
theorem not_exists_boundedDiscOffset_iff_forall_exists_natAbs_sum_Icc_offset_gt (f : ℕ → ℤ)
    (d m : ℕ) :
    (¬ ∃ B : ℕ, BoundedDiscOffset f d m B) ↔
      (∀ B : ℕ, ∃ n : ℕ,
        Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) > B) := by
  exact
    (Tao2015.unboundedDiscOffset_iff_not_exists_boundedDiscOffset (f := f) (d := d) (m := m)).symm.trans
      (unboundedDiscOffset_iff_forall_exists_natAbs_sum_Icc_offset_gt' (f := f) (d := d) (m := m))

/-- Packaging: global bounded discrepancy gives a uniform bound for every bundled offset discrepancy family.

This is the forward direction used implicitly in contrapositive arguments:
if `BoundedDiscrepancy f`, then for any `d > 0` and `m` there exists `B` with
`BoundedDiscOffset f d m B`.
-/
theorem exists_boundedDiscOffset_of_boundedDiscrepancy (f : ℕ → ℤ) (hb : BoundedDiscrepancy f)
    (d m : ℕ) (hd : d > 0) :
    ∃ B : ℕ, BoundedDiscOffset f d m B := by
  classical
  let ctx : Context f := Context.ofBoundedDiscrepancy (f := f) hb
  refine ⟨2 * ctx.B, ?_⟩
  exact Context.boundedDiscOffset_two_mul (ctx := ctx) (d := d) (m := m) hd

namespace Context

variable {f : ℕ → ℤ}

/-- Normal form: the global offset-nucleus bound bundled in `ctx` also bounds affine-tail nuclei
`apSumFrom f (m*d) d n`.

This is a small convenience wrapper around `Context.bound_natAbs_apSumOffset_two_mul`, rewritten
using `apSumFrom_mul_eq_apSumOffset`.
-/
theorem bound_natAbs_apSumFrom_mul_two_mul (ctx : Context f) (d m n : ℕ) (hd : d > 0) :
    Int.natAbs (apSumFrom f (m * d) d n) ≤ 2 * ctx.B := by
  simpa [apSumFrom_mul_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)] using
    (Context.bound_natAbs_apSumOffset_two_mul (ctx := ctx) (d := d) (m := m) (n := n) hd)

end Context

namespace ReductionOutput

variable {f : ℕ → ℤ}

/-!
## Transfer helpers: from reduced fixed-step contexts back to bundled offset families

Stage 1 (`ReductionOutput`) packages a *reduced* sign sequence `out.g` along a fixed step `out.d`.
Many downstream stages maintain a `ContextAlong out.g out.d` (uniform bound on `discrepancy` along
that step).

These tiny lemmas let such a reduced context immediately yield bounds on the *bundled offset*
family `discOffset f out.d out.m`, without having to manually rewrite each time.
-/

/-- A fixed-step discrepancy context for the reduced sequence bounds the bundled offset discrepancies.

This is just `ctx.bound` transported via the stage-1 rewrite
`discrepancy out.g out.d n = discOffset f out.d out.m n`.
-/
theorem bound_discOffset_of_contextAlong (out : ReductionOutput f) (ctx : ContextAlong out.g out.d) :
    ∀ n : ℕ, discOffset f out.d out.m n ≤ ctx.B := by
  intro n
  have h : discrepancy out.g out.d n ≤ ctx.B := ctx.bound_discrepancy n
  -- Avoid `simp`: rewriting is more robust here.
  rw [out.discrepancy_eq_discOffset_via_contract (f := f) (n := n)] at h
  exact h

/-- Package `bound_discOffset_of_contextAlong` as a `BoundedDiscOffset` witness.

Many later stages prefer the Prop-level boundedness predicate `BoundedDiscOffset` rather than
writing out the pointwise bound. This lemma is a tiny wrapper to keep consumer code clean.
-/
theorem boundedDiscOffset_of_contextAlong (out : ReductionOutput f) (ctx : ContextAlong out.g out.d) :
    BoundedDiscOffset f out.d out.m ctx.B := by
  intro n
  exact bound_discOffset_of_contextAlong (f := f) out ctx n

/-- Extract an existential bundled offset bound from a fixed-step bounded-discrepancy witness for the
reduced sequence.

This is just `ContextAlong.ofBoundedDiscrepancyAlong` followed by
`boundedDiscOffset_of_contextAlong`.
-/
theorem exists_boundedDiscOffset_of_boundedDiscrepancyAlong (out : ReductionOutput f)
    (hb : BoundedDiscrepancyAlong out.g out.d) :
    ∃ B : ℕ, BoundedDiscOffset f out.d out.m B := by
  classical
  let ctx : ContextAlong out.g out.d :=
    ContextAlong.ofBoundedDiscrepancyAlong (g := out.g) (d := out.d) hb
  exact ⟨ctx.B, boundedDiscOffset_of_contextAlong (f := f) out ctx⟩

/-- Build a reduced fixed-step discrepancy context from a bundled offset bound.

If you can uniformly bound `discOffset f out.d out.m`, the Stage-1 transfer contract immediately
yields a uniform bound on the reduced discrepancy `discrepancy out.g out.d`.
-/
def contextAlong_of_boundedDiscOffset (out : ReductionOutput f) {B : ℕ}
    (hB : BoundedDiscOffset f out.d out.m B) : ContextAlong out.g out.d := by
  refine ⟨B, ?_⟩
  intro n
  exact out.contract_discrepancy_le B hB n

/-- Package `contextAlong_of_boundedDiscOffset` as a Prop-level boundedness statement.

This is a small convenience wrapper: some consumers want a `BoundedDiscrepancyAlong` witness rather
than carrying a `ContextAlong` record.
-/
theorem boundedDiscrepancyAlong_of_boundedDiscOffset (out : ReductionOutput f) {B : ℕ}
    (hB : BoundedDiscOffset f out.d out.m B) : BoundedDiscrepancyAlong out.g out.d := by
  exact
    (contextAlong_of_boundedDiscOffset (f := f) (out := out) (B := B) hB).toBoundedDiscrepancyAlong

/-- Nucleus-level variant of `bound_discOffset_of_contextAlong`.

This version expands `discOffset` into `Int.natAbs (apSumOffset ...)`.
-/
theorem bound_natAbs_apSumOffset_of_contextAlong (out : ReductionOutput f) (ctx : ContextAlong out.g out.d) :
    ∀ n : ℕ, Int.natAbs (apSumOffset f out.d out.m n) ≤ ctx.B := by
  intro n
  have h := bound_discOffset_of_contextAlong (f := f) out ctx n
  -- Avoid `simp`: the simp bridge `Int.natAbs (apSumOffset …) = discOffset …` can loop.
  unfold discOffset at h
  exact h

/-- Paper-notation variant of `bound_natAbs_apSumOffset_of_contextAlong`.

This rewrites the bundled offset nucleus `apSumOffset` into an interval sum over
`Finset.Icc (out.m + 1) (out.m + n)`.
-/
theorem bound_natAbs_sum_Icc_offset_of_contextAlong (out : ReductionOutput f)
    (ctx : ContextAlong out.g out.d) :
    ∀ n : ℕ,
      Int.natAbs ((Finset.Icc (out.m + 1) (out.m + n)).sum (fun i => f (i * out.d))) ≤ ctx.B := by
  intro n
  have hOffset : Int.natAbs (apSumOffset f out.d out.m n) ≤ ctx.B :=
    bound_natAbs_apSumOffset_of_contextAlong (f := f) out ctx n
  simpa [natAbs_apSumOffset_eq_natAbs_sum_Icc (f := f) (d := out.d) (m := out.m) (n := n)] using
    hOffset

/-- Tail-nucleus variant of `bound_natAbs_apSumOffset_of_contextAlong`.

This exposes the affine-tail nucleus `apSumFrom f (m*d) d n` rather than the bundled wrapper
`apSumOffset f d m n`.
-/
theorem bound_natAbs_apSumFrom_mul_of_contextAlong (out : ReductionOutput f)
    (ctx : ContextAlong out.g out.d) :
    ∀ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) ≤ ctx.B := by
  intro n
  have hOffset : Int.natAbs (apSumOffset f out.d out.m n) ≤ ctx.B :=
    bound_natAbs_apSumOffset_of_contextAlong (f := f) out ctx n
  simpa [apSumFrom_mul_eq_apSumOffset (f := f) (d := out.d) (m := out.m) (n := n)] using hOffset

/-- Build a fixed-step discrepancy context for the reduced sequence from a global boundedness context.

This is the most common consumer pattern for Stage 1:
- from `BoundedDiscrepancy f` build `ctx : Tao2015.Context f`,
- then recover a uniform bound on the reduced discrepancy `discrepancy out.g out.d`.

We use the packaged bound `ctx.bound_discOffset_two_mul` together with the Stage-1 transport
contract `out.contract_discrepancy_le`.
-/
def contextAlong_of_context (out : ReductionOutput f) (ctx : Tao2015.Context f) :
    ContextAlong out.g out.d := by
  refine ⟨2 * ctx.B, ?_⟩
  intro n
  have hOffset : ∀ n : ℕ, discOffset f out.d out.m n ≤ 2 * ctx.B := by
    intro n
    simpa using
      (ctx.bound_discOffset_two_mul (f := f) (d := out.d) (m := out.m) (n := n) out.hd)
  exact out.contract_discrepancy_le (B := 2 * ctx.B) hOffset n

/-- If `f` has globally bounded discrepancy, then the reduced sequence `out.g` has bounded
fixed-step discrepancy along `out.d`.

This is a convenience wrapper around `contextAlong_of_context`: it builds a `Context` from
`BoundedDiscrepancy f`, then unwraps the resulting `ContextAlong` into the Prop-style predicate
`BoundedDiscrepancyAlong`.
-/
theorem boundedDiscrepancyAlong_of_boundedDiscrepancy (out : ReductionOutput f)
    (hb : BoundedDiscrepancy f) :
    BoundedDiscrepancyAlong out.g out.d := by
  classical
  let ctx : Tao2015.Context f := Tao2015.Context.ofBoundedDiscrepancy (f := f) hb
  let ctxAlong : ContextAlong out.g out.d := contextAlong_of_context (f := f) out ctx
  exact ⟨ctxAlong.B, ctxAlong.bound_discrepancy⟩

/-- Convenience wrapper: unboundedness of the bundled offset discrepancy family `discOffset f out.d out.m`
is equivalent to arbitrarily large affine-tail nucleus values `apSumFrom f (out.m*out.d) out.d`.

This is just `Tao2015.unboundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt` specialized to
`(d, m) = (out.d, out.m)`, but phrased as a method on the Stage-1 output record.
-/
theorem unboundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt (out : ReductionOutput f) :
    UnboundedDiscOffset f out.d out.m ↔
      (∀ B : ℕ, ∃ n : ℕ, B < Int.natAbs (apSumFrom f (out.m * out.d) out.d n)) := by
  simpa using
    (Tao2015.unboundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt (f := f) (d := out.d)
      (m := out.m))

/-- Inequality-direction variant of `unboundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt`,
written as `Int.natAbs ... > B`.

Many consumers prefer this normal form so they can `simp [gt_iff_lt]` at the call site.
-/
theorem unboundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt' (out : ReductionOutput f) :
    UnboundedDiscOffset f out.d out.m ↔
      (∀ B : ℕ, ∃ n : ℕ, Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > B) := by
  simpa [gt_iff_lt] using
    (unboundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt (f := f) (out := out))

/-- Witness-positive variant of `unboundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt'`.

Since `apSumFrom f (m*d) d 0 = 0`, the unboundedness witness length can always be taken positive.
-/
theorem unboundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt'_witness_pos
    (out : ReductionOutput f) :
    UnboundedDiscOffset f out.d out.m ↔
      (∀ B : ℕ, ∃ n : ℕ, n > 0 ∧
        Int.natAbs (apSumFrom f (out.m * out.d) out.d n) > B) := by
  simpa using
    (Tao2015.unboundedDiscOffset_iff_forall_exists_natAbs_apSumFrom_mul_gt'_witness_pos (f := f)
      (d := out.d) (m := out.m))

end ReductionOutput

end Tao2015

end MoltResearch
