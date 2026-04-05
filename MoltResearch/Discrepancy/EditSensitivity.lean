import MoltResearch.Discrepancy.Basic

/-!
# Local edit sensitivity (sum level)

This file contains Track B lemmas controlling how much an arithmetic-progression sum can change
when you modify a sign sequence on only a few indices.

Checklist item: Problems/erdos_discrepancy.md (Track B)
- Local edit sensitivity (sum-level): if `f` and `g` differ on at most `t` indices of the relevant
  `Icc`/`range`, prove a canonical bound.
-/

namespace MoltResearch

/-- Pointwise bound: if `f` and `g` are sign sequences, then `|f n - g n| ≤ 2`. -/
lemma IsSignSequence.natAbs_sub_le_two {f g : ℕ → ℤ}
    (hf : IsSignSequence f) (hg : IsSignSequence g) (n : ℕ) :
    Int.natAbs (f n - g n) ≤ 2 := by
  rcases hf n with hn | hn <;> rcases hg n with hm | hm <;> simp [hn, hm]

/-- **Local edit sensitivity (sum level, range form).**

For sign sequences `f,g`, the absolute difference of the homogeneous AP sums is controlled by the
number of indices in `Finset.range n` where the sampled values differ.

This is a canonical “count-the-edits” bound intended to be used after normalizing sums into
`Finset.range` form.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Local edit sensitivity (sum-level).
-/
lemma IsSignSequence.natAbs_apSum_sub_apSum_le_two_mul_card_range_diff {f g : ℕ → ℤ}
    (hf : IsSignSequence f) (hg : IsSignSequence g) (d n : ℕ) :
    Int.natAbs (apSum f d n - apSum g d n) ≤
      2 * ((Finset.range n).filter (fun i => f ((i + 1) * d) ≠ g ((i + 1) * d))).card := by
  classical
  -- Expand the subtraction to a single `Finset.range` sum.
  have hsub : apSum f d n - apSum g d n =
      (Finset.range n).sum (fun i => (f ((i + 1) * d) - g ((i + 1) * d))) := by
    simp [apSum, Finset.sum_sub_distrib]

  -- Replace the full sum by the filtered sum (the summand is 0 when `f=g` at that index).
  let p : ℕ → Prop := fun i => f ((i + 1) * d) ≠ g ((i + 1) * d)
  have hfilter :
      (Finset.range n).sum (fun i => (f ((i + 1) * d) - g ((i + 1) * d))) =
        ((Finset.range n).filter p).sum (fun i => (f ((i + 1) * d) - g ((i + 1) * d))) := by
    -- Use the standard `sum_filter` normal form.
    -- `(range n).filter p` sums the same because the summand is 0 when `p` is false.
    --
    -- `sum_filter` says:
    --   `(s.filter p).sum h = s.sum (fun x => if p x then h x else 0)`.
    -- We prove the original sum equals the `if`-version, then rewrite using `sum_filter`.
    have hif :
        (Finset.range n).sum (fun i => (f ((i + 1) * d) - g ((i + 1) * d))) =
          (Finset.range n).sum (fun i => if p i then (f ((i + 1) * d) - g ((i + 1) * d)) else 0) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hp : p i
      · simp [hp]
      · -- If `f=g` at this index, the summand is `0`.
        have : f ((i + 1) * d) = g ((i + 1) * d) := by
          exact by simpa [p] using hp
        simp [hp, this]
    -- Now rewrite the RHS using `sum_filter`.
    -- `sum_filter` gives the filtered sum equals the if-sum, so we use it in reverse.
    have hsum_filter :
        ((Finset.range n).filter p).sum (fun i => (f ((i + 1) * d) - g ((i + 1) * d))) =
          (Finset.range n).sum (fun i => if p i then (f ((i + 1) * d) - g ((i + 1) * d)) else 0) := by
      simpa [Finset.sum_filter] using
        (Finset.sum_filter (s := Finset.range n)
          (p := p) (f := fun i => (f ((i + 1) * d) - g ((i + 1) * d))))
    -- Combine.
    exact (hif.trans hsum_filter.symm)

  -- Apply triangle inequality + pointwise bound `≤ 2` on the filtered sum.
  -- A small helper: triangle inequality for `Int.natAbs` over `Finset.sum`.
  have natAbs_sum_le_sum_natAbs {α : Type} (s : Finset α) (h : α → ℤ) :
      Int.natAbs (s.sum h) ≤ s.sum (fun a => Int.natAbs (h a)) := by
    classical
    refine Finset.induction_on s ?h0 ?hstep
    · simp
    · intro a s ha hs
      -- `|h a + sum h| ≤ |h a| + |sum h| ≤ |h a| + sum |h|`.
      have h1 : Int.natAbs (h a + s.sum h) ≤ Int.natAbs (h a) + Int.natAbs (s.sum h) := by
        simpa [add_comm, add_left_comm, add_assoc] using (Int.natAbs_add_le (h a) (s.sum h))
      have h2 : Int.natAbs (s.sum h) ≤ s.sum (fun b => Int.natAbs (h b)) := hs
      have h3 : Int.natAbs (h a) + Int.natAbs (s.sum h) ≤
          Int.natAbs (h a) + s.sum (fun b => Int.natAbs (h b)) := by
        exact Nat.add_le_add_left h2 _
      -- Reassociate the RHS into a `Finset.sum`.
      simpa [Finset.sum_insert ha, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Nat.le_trans h1 h3)

  have htri :
      Int.natAbs (((Finset.range n).filter p).sum (fun i => (f ((i + 1) * d) - g ((i + 1) * d)))) ≤
        ((Finset.range n).filter p).sum (fun i => Int.natAbs (f ((i + 1) * d) - g ((i + 1) * d))) := by
    simpa using
      (natAbs_sum_le_sum_natAbs ((Finset.range n).filter p)
        (fun i => (f ((i + 1) * d) - g ((i + 1) * d))))

  have hpt : ∀ i, Int.natAbs (f ((i + 1) * d) - g ((i + 1) * d)) ≤ 2 := by
    intro i
    simpa [sub_eq_add_neg] using (IsSignSequence.natAbs_sub_le_two (hf := hf) (hg := hg) ((i + 1) * d))

  have hsum_le :
      ((Finset.range n).filter p).sum (fun i => Int.natAbs (f ((i + 1) * d) - g ((i + 1) * d))) ≤
        ((Finset.range n).filter p).card * 2 := by
    -- A `Nat`-sum bounded termwise by `2`.
    exact Finset.sum_le_card_nsmul _ _ 2 (by intro i hi; simpa using (hpt i))

  -- Put everything together.
  -- Note: rewrite the RHS into `2 * card` for consistency.
  have :
      Int.natAbs (apSum f d n - apSum g d n) ≤ ((Finset.range n).filter p).card * 2 := by
    -- Rewrite to the filtered sum, then chain inequalities.
    simpa [hsub, hfilter] using Nat.le_trans htri hsum_le

  -- Normalize `card * 2` to `2 * card`.
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, p] using this

/-- Convenience corollary: if `f,g` differ on at most `t` sampled indices, then
`|apSum f d n - apSum g d n| ≤ 2*t`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Local edit sensitivity (sum-level).
-/
lemma IsSignSequence.natAbs_apSum_sub_apSum_le_two_mul_of_card_range_diff_le {f g : ℕ → ℤ}
    (hf : IsSignSequence f) (hg : IsSignSequence g) (d n t : ℕ)
    (ht : ((Finset.range n).filter (fun i => f ((i + 1) * d) ≠ g ((i + 1) * d))).card ≤ t) :
    Int.natAbs (apSum f d n - apSum g d n) ≤ 2 * t := by
  have h :=
    IsSignSequence.natAbs_apSum_sub_apSum_le_two_mul_card_range_diff (hf := hf) (hg := hg) (d := d)
      (n := n)
  exact le_trans h (Nat.mul_le_mul_left 2 ht)

/-- **Local edit sensitivity (sum level, offset range form).**

For sign sequences `f,g`, the absolute difference of offset AP sums is controlled by the
number of indices in `Finset.range n` where the sampled values differ.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Local edit sensitivity (sum-level).
-/
lemma IsSignSequence.natAbs_apSumOffset_sub_apSumOffset_le_two_mul_card_range_diff {f g : ℕ → ℤ}
    (hf : IsSignSequence f) (hg : IsSignSequence g) (d m n : ℕ) :
    Int.natAbs (apSumOffset f d m n - apSumOffset g d m n) ≤
      2 * ((Finset.range n).filter (fun i => f ((m + i + 1) * d) ≠ g ((m + i + 1) * d))).card := by
  classical
  -- Expand the subtraction to a single `Finset.range` sum.
  have hsub : apSumOffset f d m n - apSumOffset g d m n =
      (Finset.range n).sum (fun i => (f ((m + i + 1) * d) - g ((m + i + 1) * d))) := by
    simp [apSumOffset, Finset.sum_sub_distrib]

  -- Replace the full sum by the filtered sum (the summand is 0 when `f=g` at that index).
  let p : ℕ → Prop := fun i => f ((m + i + 1) * d) ≠ g ((m + i + 1) * d)
  have hfilter :
      (Finset.range n).sum (fun i => (f ((m + i + 1) * d) - g ((m + i + 1) * d))) =
        ((Finset.range n).filter p).sum (fun i => (f ((m + i + 1) * d) - g ((m + i + 1) * d))) := by
    have hif :
        (Finset.range n).sum (fun i => (f ((m + i + 1) * d) - g ((m + i + 1) * d))) =
          (Finset.range n).sum (fun i => if p i then (f ((m + i + 1) * d) - g ((m + i + 1) * d)) else 0) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hp : p i
      · simp [hp]
      · have : f ((m + i + 1) * d) = g ((m + i + 1) * d) := by
          exact by simpa [p] using hp
        simp [hp, this]
    have hsum_filter :
        ((Finset.range n).filter p).sum (fun i => (f ((m + i + 1) * d) - g ((m + i + 1) * d))) =
          (Finset.range n).sum (fun i => if p i then (f ((m + i + 1) * d) - g ((m + i + 1) * d)) else 0) := by
      simpa [Finset.sum_filter] using
        (Finset.sum_filter (s := Finset.range n)
          (p := p) (f := fun i => (f ((m + i + 1) * d) - g ((m + i + 1) * d))))
    exact (hif.trans hsum_filter.symm)

  -- Triangle inequality for `Int.natAbs` over `Finset.sum`.
  have natAbs_sum_le_sum_natAbs {α : Type} (s : Finset α) (h : α → ℤ) :
      Int.natAbs (s.sum h) ≤ s.sum (fun a => Int.natAbs (h a)) := by
    classical
    refine Finset.induction_on s ?h0 ?hstep
    · simp
    · intro a s ha hs
      have h1 : Int.natAbs (h a + s.sum h) ≤ Int.natAbs (h a) + Int.natAbs (s.sum h) := by
        simpa [add_comm, add_left_comm, add_assoc] using (Int.natAbs_add_le (h a) (s.sum h))
      have h2 : Int.natAbs (s.sum h) ≤ s.sum (fun b => Int.natAbs (h b)) := hs
      have h3 : Int.natAbs (h a) + Int.natAbs (s.sum h) ≤
          Int.natAbs (h a) + s.sum (fun b => Int.natAbs (h b)) :=
        Nat.add_le_add_left h2 _
      simpa [Finset.sum_insert ha, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Nat.le_trans h1 h3)

  have htri :
      Int.natAbs (((Finset.range n).filter p).sum (fun i => (f ((m + i + 1) * d) - g ((m + i + 1) * d)))) ≤
        ((Finset.range n).filter p).sum (fun i => Int.natAbs (f ((m + i + 1) * d) - g ((m + i + 1) * d))) := by
    simpa using
      (natAbs_sum_le_sum_natAbs ((Finset.range n).filter p)
        (fun i => (f ((m + i + 1) * d) - g ((m + i + 1) * d))))

  have hpt : ∀ i, Int.natAbs (f ((m + i + 1) * d) - g ((m + i + 1) * d)) ≤ 2 := by
    intro i
    simpa [sub_eq_add_neg] using (IsSignSequence.natAbs_sub_le_two (hf := hf) (hg := hg) ((m + i + 1) * d))

  have hsum_le :
      ((Finset.range n).filter p).sum (fun i => Int.natAbs (f ((m + i + 1) * d) - g ((m + i + 1) * d))) ≤
        ((Finset.range n).filter p).card * 2 := by
    exact Finset.sum_le_card_nsmul _ _ 2 (by intro i hi; simpa using (hpt i))

  have :
      Int.natAbs (apSumOffset f d m n - apSumOffset g d m n) ≤ ((Finset.range n).filter p).card * 2 := by
    simpa [hsub, hfilter] using Nat.le_trans htri hsum_le

  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, p] using this

/-- Convenience corollary: if `f,g` differ on at most `t` sampled indices for `apSumOffset`, then
`|apSumOffset f d m n - apSumOffset g d m n| ≤ 2*t`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Local edit sensitivity (sum-level).
-/
lemma IsSignSequence.natAbs_apSumOffset_sub_apSumOffset_le_two_mul_of_card_range_diff_le {f g : ℕ → ℤ}
    (hf : IsSignSequence f) (hg : IsSignSequence g) (d m n t : ℕ)
    (ht : ((Finset.range n).filter (fun i => f ((m + i + 1) * d) ≠ g ((m + i + 1) * d))).card ≤ t) :
    Int.natAbs (apSumOffset f d m n - apSumOffset g d m n) ≤ 2 * t := by
  have h :=
    IsSignSequence.natAbs_apSumOffset_sub_apSumOffset_le_two_mul_card_range_diff
      (hf := hf) (hg := hg) (d := d) (m := m) (n := n)
  exact le_trans h (Nat.mul_le_mul_left 2 ht)

/-!
## Local edit sensitivity (discrepancy level)

The lemmas above control the *sum* difference `|apSumOffset f - apSumOffset g|` in terms of the
number of sampled indices where `f` and `g` differ.

Here we package the corresponding *discrepancy* corollaries at the `discOffset` level.

Checklist item: Problems/erdos_discrepancy.md (Track B)
- Local edit sensitivity (disc-level): derive the discrepancy-level corollary.
-/

/-- **Discrepancy-level edit bound (generic form).**

If an offset AP sum changes by at most `t` in `Int.natAbs`, then the corresponding discrepancy
changes by at most `t` (in the one-sided direction).

This is a lightweight triangle-inequality wrapper intended to be combined with the sum-level
edit-sensitivity bounds in this file.
-/
lemma discOffset_le_discOffset_add_of_natAbs_apSumOffset_sub_le (f g : ℕ → ℤ) (d m n t : ℕ)
    (ht : Int.natAbs (apSumOffset f d m n - apSumOffset g d m n) ≤ t) :
    discOffset f d m n ≤ discOffset g d m n + t := by
  -- `|Sf| = |(Sf - Sg) + Sg| ≤ |Sf - Sg| + |Sg|`.
  have htri :
      Int.natAbs (apSumOffset f d m n) ≤
        Int.natAbs (apSumOffset f d m n - apSumOffset g d m n) +
          Int.natAbs (apSumOffset g d m n) := by
    -- Triangle inequality: `|a + b| ≤ |a| + |b|`, with `a = Sf - Sg`, `b = Sg`.
    set a : ℤ := apSumOffset f d m n - apSumOffset g d m n
    set b : ℤ := apSumOffset g d m n
    have hab : a + b = apSumOffset f d m n := by
      -- `(Sf - Sg) + Sg = Sf`.
      -- `a` and `b` are just abbreviations, so this is `sub_add_cancel`.
      simpa [a, b] using (sub_add_cancel (apSumOffset f d m n) (apSumOffset g d m n))
    have h' : Int.natAbs (a + b) ≤ Int.natAbs a + Int.natAbs b :=
      Int.natAbs_add_le a b
    -- Rewrite `|a+b|` to `|Sf|`.
    have habAbs : Int.natAbs (a + b) = Int.natAbs (apSumOffset f d m n) :=
      congrArg Int.natAbs hab
    -- Now transfer the bound.
    have h'' := h'
    rw [habAbs] at h''
    simpa [a, b] using h''

  -- Convert to the `discOffset` wrappers and apply the hypothesis `ht`.
  -- Note: `discOffset` is definitional `Int.natAbs (apSumOffset ...)`.
  have : discOffset f d m n ≤ t + discOffset g d m n := by
    -- Combine triangle inequality with the bound on the difference term.
    have hstep :
        Int.natAbs (apSumOffset f d m n - apSumOffset g d m n) +
            Int.natAbs (apSumOffset g d m n)
          ≤ t + Int.natAbs (apSumOffset g d m n) :=
      Nat.add_le_add_right ht (Int.natAbs (apSumOffset g d m n))
    -- Convert the target to `Int.natAbs` form and finish.
    unfold discOffset
    -- After unfolding, the goal is exactly the chained inequality.
    exact le_trans htri hstep

  -- Normalize `t + discOffset g ...` to `discOffset g ... + t`.
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

/-- **Local edit sensitivity (disc-level, offset form).**

If `f,g` are sign sequences and they differ on at most `t` sampled indices in the offset AP sum,
then the discrepancy `discOffset` of length `n` changes by at most `2*t` (one-sided).

Checklist item: Problems/erdos_discrepancy.md (Track B) — Local edit sensitivity (disc-level).
-/
lemma IsSignSequence.discOffset_le_discOffset_add_two_mul_of_card_range_diff_le {f g : ℕ → ℤ}
    (hf : IsSignSequence f) (hg : IsSignSequence g) (d m n t : ℕ)
    (ht : ((Finset.range n).filter (fun i => f ((m + i + 1) * d) ≠ g ((m + i + 1) * d))).card ≤ t) :
    discOffset f d m n ≤ discOffset g d m n + 2 * t := by
  have hsum :
      Int.natAbs (apSumOffset f d m n - apSumOffset g d m n) ≤ 2 * t := by
    simpa using
      (IsSignSequence.natAbs_apSumOffset_sub_apSumOffset_le_two_mul_of_card_range_diff_le
        (hf := hf) (hg := hg) (d := d) (m := m) (n := n) (t := t) ht)
  simpa using
    (discOffset_le_discOffset_add_of_natAbs_apSumOffset_sub_le (f := f) (g := g) (d := d) (m := m)
      (n := n) (t := 2 * t) hsum)

/-- Symmetric form of `IsSignSequence.discOffset_le_discOffset_add_two_mul_of_card_range_diff_le`. -/
lemma IsSignSequence.discOffset_le_discOffset_add_two_mul_of_card_range_diff_le' {f g : ℕ → ℤ}
    (hf : IsSignSequence f) (hg : IsSignSequence g) (d m n t : ℕ)
    (ht : ((Finset.range n).filter (fun i => f ((m + i + 1) * d) ≠ g ((m + i + 1) * d))).card ≤ t) :
    discOffset g d m n ≤ discOffset f d m n + 2 * t := by
  have ht' : ((Finset.range n).filter (fun i => g ((m + i + 1) * d) ≠ f ((m + i + 1) * d))).card ≤ t := by
    simpa [ne_comm] using ht
  simpa [Nat.mul_comm] using
    (IsSignSequence.discOffset_le_discOffset_add_two_mul_of_card_range_diff_le
      (hf := hg) (hg := hf) (d := d) (m := m) (n := n) (t := t) ht')

/-!
## API polish: `…_edit_…` naming

The Track B card asks for the discrepancy-level edit-sensitivity bounds to be packaged with
`…_edit_…`-style names, so downstream proofs read naturally (“edit the sequence; discrepancy
changes by at most …”). These are thin wrappers around the canonical lemmas above.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Local edit sensitivity (disc-level).
-/

/-- **Local edit sensitivity (disc-level).**

If `f,g` are sign sequences and they differ on at most `t` sampled indices in the offset AP sum,
then editing `f` into `g` changes `discOffset` by at most `2*t` (one-sided).

This is just a renamed wrapper for
`IsSignSequence.discOffset_le_discOffset_add_two_mul_of_card_range_diff_le`.
-/
lemma IsSignSequence.discOffset_edit_le {f g : ℕ → ℤ}
    (hf : IsSignSequence f) (hg : IsSignSequence g) (d m n t : ℕ)
    (ht : ((Finset.range n).filter (fun i => f ((m + i + 1) * d) ≠ g ((m + i + 1) * d))).card ≤ t) :
    discOffset f d m n ≤ discOffset g d m n + 2 * t := by
  simpa using
    (IsSignSequence.discOffset_le_discOffset_add_two_mul_of_card_range_diff_le
      (hf := hf) (hg := hg) (d := d) (m := m) (n := n) (t := t) ht)

/-- The opposite one-sided inequality, packaged with `…_le_edit_add` naming. -/
lemma IsSignSequence.discOffset_le_edit_add {f g : ℕ → ℤ}
    (hf : IsSignSequence f) (hg : IsSignSequence g) (d m n t : ℕ)
    (ht : ((Finset.range n).filter (fun i => f ((m + i + 1) * d) ≠ g ((m + i + 1) * d))).card ≤ t) :
    discOffset g d m n ≤ discOffset f d m n + 2 * t := by
  simpa using
    (IsSignSequence.discOffset_le_discOffset_add_two_mul_of_card_range_diff_le'
      (hf := hf) (hg := hg) (d := d) (m := m) (n := n) (t := t) ht)

/-!
## API: edit sensitivity phrased via `apSupport`

The Track B checklist item asks for the local edit-sensitivity bounds to be stated without
`Finset.range`/`Icc` bookkeeping, purely in terms of the normal-form support object `apSupport`.

Because `apSupport d m n` is defined as an *image* of `Finset.range n`, we assume `d > 0` so that
`i ↦ (m + i + 1) * d` is injective; otherwise multiplicities can collapse (e.g. `d = 0`).
-/

/-- Relate the “range-filter” disagreement count to the disagreement count on `apSupport`.

If `d > 0`, the sampling map `i ↦ (m+i+1)*d` is injective, so counting disagreements over
`Finset.range n` is bounded by counting disagreements over the induced `apSupport` finset.
-/
lemma card_range_diff_le_card_apSupport_diff (f g : ℕ → ℤ) (d m n : ℕ) (hd : d > 0) :
    ((Finset.range n).filter (fun i => f ((m + i + 1) * d) ≠ g ((m + i + 1) * d))).card ≤
      ((apSupport d m n).filter (fun x => f x ≠ g x)).card := by
  classical
  -- Set up the sampling map.
  let h : ℕ → ℕ := fun i => (m + i + 1) * d
  -- Injectivity of `h` when `d > 0`.
  have hinj : Function.Injective h := by
    intro i j hij
    have hmul : m + i + 1 = m + j + 1 := by
      -- Cancel the positive factor `d`.
      exact Nat.mul_right_cancel hd hij
    have hmul' : m + (i + 1) = m + (j + 1) := by
      simpa [h, Nat.add_assoc] using hmul
    have : i + 1 = j + 1 := Nat.add_left_cancel hmul'
    exact Nat.succ_inj.mp (by simpa using this)

  -- The filtered disagreement finset on indices `i`.
  let s : Finset ℕ :=
    (Finset.range n).filter (fun i => f (h i) ≠ g (h i))

  -- Push disagreements forward into `apSupport`.
  have himage_subset : s.image h ⊆ (apSupport d m n).filter (fun x => f x ≠ g x) := by
    intro x hx
    rcases Finset.mem_image.1 hx with ⟨i, hi, rfl⟩
    have hi' := (Finset.mem_filter.1 hi)
    have hirange : i ∈ Finset.range n := hi'.1
    have hidiff : f (h i) ≠ g (h i) := hi'.2
    have hxSupp : h i ∈ apSupport d m n := by
      -- `i < n` implies the sampled index lies in `apSupport`.
      exact mem_apSupport_of_lt (d := d) (m := m) (n := n) (i := i) (Finset.mem_range.1 hirange)
    exact Finset.mem_filter.2 ⟨hxSupp, by simpa [h] using hidiff⟩

  -- Compare cardinalities.
  have hcard_image : (s.image h).card = s.card := by
    simpa [h] using (Finset.card_image_of_injective s hinj)
  -- `card s = card (image)` and `image ⊆ filter`, so `card s ≤ card filter`.
  have : s.card ≤ ((apSupport d m n).filter (fun x => f x ≠ g x)).card := by
    -- Rewrite `s.card` as `(s.image h).card`.
    have : (s.image h).card ≤ ((apSupport d m n).filter (fun x => f x ≠ g x)).card :=
      Finset.card_le_card himage_subset
    simpa [hcard_image] using this

  -- Unfold `s` back to the statement.
  simpa [s, h] using this

/-- **Local edit sensitivity (disc-level, `apSupport` form).**

If `f,g` are sign sequences and they differ on at most `t` indices in the normal-form support
`apSupport d m n`, then editing `f` into `g` changes `discOffset` by at most `2*t` (one-sided).

Checklist item: Problems/erdos_discrepancy.md (Track B) — Local edit sensitivity (disc-level),
`apSupport` normal form.
-/
lemma IsSignSequence.discOffset_edit_le_of_card_apSupport_diff_le {f g : ℕ → ℤ}
    (hf : IsSignSequence f) (hg : IsSignSequence g) (d m n t : ℕ) (hd : d > 0)
    (ht : ((apSupport d m n).filter (fun x => f x ≠ g x)).card ≤ t) :
    discOffset f d m n ≤ discOffset g d m n + 2 * t := by
  have htrange :
      ((Finset.range n).filter (fun i => f ((m + i + 1) * d) ≠ g ((m + i + 1) * d))).card ≤ t := by
    exact le_trans (card_range_diff_le_card_apSupport_diff (f := f) (g := g)
      (d := d) (m := m) (n := n) hd) ht
  simpa using (IsSignSequence.discOffset_edit_le (hf := hf) (hg := hg) (d := d) (m := m) (n := n)
    (t := t) htrange)

/-- Symmetric `apSupport`-form edit sensitivity inequality. -/
lemma IsSignSequence.discOffset_le_edit_add_of_card_apSupport_diff_le {f g : ℕ → ℤ}
    (hf : IsSignSequence f) (hg : IsSignSequence g) (d m n t : ℕ) (hd : d > 0)
    (ht : ((apSupport d m n).filter (fun x => f x ≠ g x)).card ≤ t) :
    discOffset g d m n ≤ discOffset f d m n + 2 * t := by
  -- Use the one-sided lemma with swapped roles.
  have ht' : ((apSupport d m n).filter (fun x => g x ≠ f x)).card ≤ t := by
    simpa [ne_comm] using ht
  simpa [Nat.mul_comm] using
    (IsSignSequence.discOffset_edit_le_of_card_apSupport_diff_le (hf := hg) (hg := hf)
      (d := d) (m := m) (n := n) (t := t) hd ht')

end MoltResearch
