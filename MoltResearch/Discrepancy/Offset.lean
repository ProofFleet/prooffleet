import MoltResearch.Discrepancy.Basic

/-!
# Discrepancy: offset sums

Extra lemmas about `apSumOffset` and its relation to differences of `apSum`.
-/

namespace MoltResearch

/-!
## Normal-form: `Finset.range` expansions

These are intentionally small “shape” lemmas: they let downstream code rewrite an `apSumOffset`
into an explicit `Finset.range` sum without switching to `Icc`-based paper notation.

We keep both binder orders:
- the canonical definition order `m + i + 1`
- a translation-friendly `_add` variant with `i + m + 1`
-/

/-- Normal-form lemma: rewrite `apSumOffset` as a `Finset.range` sum in the canonical binder order. -/
lemma apSumOffset_eq_sum_range (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = (Finset.range n).sum (fun i => f ((m + i + 1) * d)) := by
  rfl

/-!
## Stable rewrite lemmas

These expose the same rewrite as `apSumOffset_eq_sum_range` but with **stable names** that we
intend downstream developments to depend on.
-/

/-- Stable normal-form lemma: rewrite `apSumOffset` as a `Finset.range` sum.

This is a thin wrapper around `apSumOffset_eq_sum_range` (the definitional lemma).
-/
lemma apSumOffset_eq_sum_range' (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = (Finset.range n).sum (fun i => f ((m + i + 1) * d)) := by
  simpa using (apSumOffset_eq_sum_range (f := f) (d := d) (m := m) (n := n))

/-- Stable inverse rewrite lemma: a `Finset.range` tail sum is an `apSumOffset`.

This is the symmetric orientation of `apSumOffset_eq_sum_range'`.
-/
lemma sum_range_eq_apSumOffset' (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.range n).sum (fun i => f ((m + i + 1) * d)) = apSumOffset f d m n := by
  simpa using (apSumOffset_eq_sum_range' (f := f) (d := d) (m := m) (n := n)).symm

/-!
### Range-form stability

The range-form congruence lemmas `apSumOffset_congr_range` and `discOffset_congr_range` live in
`MoltResearch.Discrepancy.Basic` (so pointwise wrappers can discharge to them without import cycles).
-/

/-- Translation-friendly variant of `apSumOffset_eq_sum_range` with the binder variable on the left:
`i + m + 1`.

This avoids commuting `Nat.add_comm` under a lambda in downstream normalizations.
-/
lemma apSumOffset_eq_sum_range_add (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = (Finset.range n).sum (fun i => f ((i + m + 1) * d)) := by
  unfold apSumOffset
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Reverse-reindex normal form for `apSumOffset` over `Finset.range`.

This reindexes the defining range sum by `i ↦ n-1-i`, packaging the standard lemma
`Finset.sum_range_reflect` into the discrepancy nucleus API.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Offset-reindex “reverse” normal form.
-/
lemma apSumOffset_eq_sum_range_reflect (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n =
      (Finset.range n).sum (fun i => f ((m + (n - 1 - i) + 1) * d)) := by
  classical
  calc
    apSumOffset f d m n
        = (Finset.range n).sum (fun i => f ((m + i + 1) * d)) := by
            simpa using (apSumOffset_eq_sum_range' (f := f) (d := d) (m := m) (n := n))
    _ = (Finset.range n).sum (fun i => f ((m + (n - 1 - i) + 1) * d)) := by
          simpa using (Finset.sum_range_reflect (f := fun i => f ((m + i + 1) * d)) n).symm

/-- Reverse-reindex normal form for `discOffset` over `Finset.range`.

This is the `discOffset` wrapper analogue of `apSumOffset_eq_sum_range_reflect`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Reflection invariance (disc-level).
-/
lemma discOffset_eq_natAbs_sum_range_reflect (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset f d m n =
      Int.natAbs ((Finset.range n).sum (fun i => f ((m + (n - 1 - i) + 1) * d))) := by
  -- Apply `Int.natAbs` to the sum-level reflect lemma.
  unfold discOffset
  exact
    congrArg Int.natAbs
      (apSumOffset_eq_sum_range_reflect (f := f) (d := d) (m := m) (n := n))

/-!
## One-cut normal form (range sums)

When you expand an `apSumOffset` into a `Finset.range` sum (via `apSumOffset_eq_sum_range'`), you
often want to split that range sum into two consecutive blocks and *immediately* land back in the
nucleus normal form `apSumOffset` for each piece.

This lemma packages that rewrite pipeline.
-/

/-- Split a `Finset.range` tail sum at a cut `n₁`, and rewrite both pieces to `apSumOffset`.

Concretely, this rewrites
`∑ i < n₁+n₂, f ((m+i+1)*d)`
into
`apSumOffset f d m n₁ + apSumOffset f d (m+n₁) n₂`.

This is the `Finset.range` analogue of the paper-notation bridge
`sum_Icc_add_len_eq_apSumOffset_add`.
-/
lemma sum_range_add_len_eq_apSumOffset_add (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    (Finset.range (n₁ + n₂)).sum (fun i => f ((m + i + 1) * d)) =
      apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
  -- Split the `range (n₁+n₂)` sum, then rewrite each block back to the nucleus API.
  classical
  -- Use the standard `range`-split lemma and normalize the shifted summand.
  simpa [apSumOffset_eq_sum_range', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (Finset.sum_range_add (f := fun i => f ((m + i + 1) * d)) n₁ n₂)

/-- One-cut normal form for `discOffset` over a concatenated `Finset.range`.

This rewrites `discOffset f d m (n₁+n₂)` into the absolute value of the sum of the two offset sums
corresponding to the prefix of length `n₁` and the tail of length `n₂`.

This is a Track B “range-cut normal form” lemma. -/
lemma discOffset_add_len_eq_natAbs_apSumOffset_add (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    discOffset f d m (n₁ + n₂) =
      Int.natAbs (apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂) := by
  unfold discOffset
  have h : apSumOffset f d m (n₁ + n₂) =
      apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
    calc
      apSumOffset f d m (n₁ + n₂)
          = (Finset.range (n₁ + n₂)).sum (fun i => f ((m + i + 1) * d)) := by
              simpa using
                (apSumOffset_eq_sum_range' (f := f) (d := d) (m := m) (n := n₁ + n₂))
      _ = apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
            simpa using
              (sum_range_add_len_eq_apSumOffset_add (f := f) (d := d) (m := m) (n₁ := n₁)
                (n₂ := n₂))
  simpa [h]

/-- Range-cut normal form for `discOffset`: split at a cut length `k ≤ n`.

This packages the “expand to `Finset.range`, cut, and rewrite back” pipeline into a single lemma
that later proofs can use without dropping down to raw `Finset` sums.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Range-cut normal form (discOffset-level).
-/
lemma discOffset_eq_natAbs_apSumOffset_cut (f : ℕ → ℤ) (d m n k : ℕ) (hk : k ≤ n) :
    discOffset f d m n =
      Int.natAbs (apSumOffset f d m k + apSumOffset f d (m + k) (n - k)) := by
  -- Rewrite `n` as `k + (n-k)` and apply the length-splitting normal form.
  have hn : k + (n - k) = n := Nat.add_sub_of_le hk
  -- `discOffset_add_len_eq_natAbs_apSumOffset_add` is stated for `n₁+n₂`.
  -- We specialize it with `n₁=k`, `n₂=n-k` and rewrite using `hn`.
  simpa [hn] using
    (discOffset_add_len_eq_natAbs_apSumOffset_add (f := f) (d := d) (m := m)
      (n₁ := k) (n₂ := n - k))

/-- Range-cut normal form for `apSumOffset`: split at a cut length `k ≤ n`.

This is the sum-level companion to `discOffset_eq_natAbs_apSumOffset_cut`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Range-form cut lemma (sum level).
-/
lemma apSumOffset_eq_add_apSumOffset_cut (f : ℕ → ℤ) (d m n k : ℕ) (hk : k ≤ n) :
    apSumOffset f d m n = apSumOffset f d m k + apSumOffset f d (m + k) (n - k) := by
  classical
  -- Expand to a `Finset.range` sum, split at `k`, and rewrite both blocks back to `apSumOffset`.
  have hn : k + (n - k) = n := Nat.add_sub_of_le hk
  -- Work in the `Finset.range` normal form.
  have hsplit :
      (Finset.range n).sum (fun i => f ((m + i + 1) * d)) =
        (Finset.range k).sum (fun i => f ((m + i + 1) * d)) +
          (Finset.range (n - k)).sum (fun i => f (((m + k) + i + 1) * d)) := by
    -- Use the standard range split `sum_range_add` on `n = k + (n-k)`.
    -- `sum_range_add` shifts the index in the second block by `k`.
    -- We then normalize the arithmetic to expose `(m+k)+i+1`.
    simpa [hn, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Finset.sum_range_add (f := fun i => f ((m + i + 1) * d)) k (n - k))
  -- Rewrite the left-hand side from `apSumOffset` into `Finset.range` form, apply the split,
  -- then rewrite both blocks back to `apSumOffset`.
  calc
    apSumOffset f d m n
        = (Finset.range n).sum (fun i => f ((m + i + 1) * d)) := by
            simpa using (apSumOffset_eq_sum_range' (f := f) (d := d) (m := m) (n := n))
    _ = (Finset.range k).sum (fun i => f ((m + i + 1) * d)) +
          (Finset.range (n - k)).sum (fun i => f (((m + k) + i + 1) * d)) := by
            simpa using hsplit
    _ = apSumOffset f d m k + apSumOffset f d (m + k) (n - k) := by
          -- Each block is exactly the stable `Finset.range` normal form of an `apSumOffset`.
          simp [apSumOffset_eq_sum_range']

/-- Difference normal form for `apSumOffset`: the tail after cutting at `k ≤ n`.

This is the exact (non-`natAbs`) companion to `apSumOffset_eq_add_apSumOffset_cut`:
subtracting the prefix sum of length `k` from the sum of length `n` yields the tail sum.

Checklist item: Problems/erdos_discrepancy.md (Track B) — `discOffset` cut equality (NatAbs-level):
complement `discOffset_eq_natAbs_apSumOffset_cut` with an exact difference lemma.
-/
lemma apSumOffset_sub_apSumOffset_cut (f : ℕ → ℤ) (d m n k : ℕ) (hk : k ≤ n) :
    apSumOffset f d m n - apSumOffset f d m k = apSumOffset f d (m + k) (n - k) := by
  have h := apSumOffset_eq_add_apSumOffset_cut (f := f) (d := d) (m := m) (n := n) (k := k) hk
  calc
    apSumOffset f d m n - apSumOffset f d m k
        = (apSumOffset f d m k + apSumOffset f d (m + k) (n - k)) - apSumOffset f d m k := by
            simpa [h]
    _ = apSumOffset f d (m + k) (n - k) := by
          simpa using
            (add_sub_cancel_left (apSumOffset f d m k) (apSumOffset f d (m + k) (n - k)))

/-- Difference normal form for `apSumOffset`: the increment when increasing the length.

This complements the “cut” lemmas by giving the *exact* tail difference as an `apSumOffset`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — `discOffset` cut equality (NatAbs-level):
exact difference at the `Int` level.
-/
lemma apSumOffset_add_length_sub (f : ℕ → ℤ) (d m n k : ℕ) :
    apSumOffset f d m (n + k) - apSumOffset f d m n = apSumOffset f d (m + n) k := by
  -- This is just the length-splitting lemma, rearranged.
  have h := apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := n) (n₂ := k)
  -- `h` is: `apSumOffset … (n+k) = apSumOffset … n + apSumOffset … (m+n) k`.
  calc
    apSumOffset f d m (n + k) - apSumOffset f d m n
        = (apSumOffset f d m n + apSumOffset f d (m + n) k) - apSumOffset f d m n := by
            simpa [h] using (congrArg (fun t => t - apSumOffset f d m n) h)
    _ = apSumOffset f d (m + n) k := by
          simpa using (add_sub_cancel_left (apSumOffset f d m n) (apSumOffset f d (m + n) k))

--

/-- Range-cut triangle inequality for `discOffset`: split at a cut length `k ≤ n`.

This is the inequality counterpart of `discOffset_eq_natAbs_apSumOffset_cut`, rewriting the
result back into the `discOffset` wrapper on both pieces.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Range-cut normal form (discOffset-level).
-/
lemma discOffset_cut_le (f : ℕ → ℤ) (d m n k : ℕ) (hk : k ≤ n) :
    discOffset f d m n ≤ discOffset f d m k + discOffset f d (m + k) (n - k) := by
  -- Rewrite the left-hand side into a single `Int.natAbs (x+y)`.
  have hEq := discOffset_eq_natAbs_apSumOffset_cut (f := f) (d := d) (m := m) (n := n) (k := k) hk
  -- `|x+y| ≤ |x|+|y|`.
  simpa [hEq] using
    (Int.natAbs_add_le (apSumOffset f d m k) (apSumOffset f d (m + k) (n - k)))

lemma apSumOffset_eq_sub (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSum f d (m + n) - apSum f d m := by
  have h0 := (apSum_add_length (f := f) (d := d) (m := m) (n := n)).symm
  have h : apSumOffset f d m n + apSum f d m = apSum f d (m + n) := by
    simpa [add_comm] using h0
  exact eq_sub_of_add_eq h

/-- Prefix + tail = total, with the tail written as `apSumOffset`. -/
lemma apSumOffset_add_apSum_eq (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n + apSum f d m = apSum f d (m + n) := by
  -- This is just `apSum_add_length`, in a convenient orientation.
  simpa [add_comm] using (apSum_add_length (f := f) (d := d) (m := m) (n := n)).symm

/-- Prefix + tail = total, with the prefix on the left.

This is the commuted variant of `apSumOffset_add_apSum_eq`.
-/
lemma apSum_add_apSumOffset_eq (f : ℕ → ℤ) (d m n : ℕ) :
    apSum f d m + apSumOffset f d m n = apSum f d (m + n) := by
  simpa [add_comm] using apSumOffset_add_apSum_eq (f := f) (d := d) (m := m) (n := n)

/-- Rewrite `apSumOffset` as the familiar interval sum `∑ i ∈ Icc (m+1) (m+n), f (i*d)`.

This is intended for surface statements: keep the nucleus API in terms of `apSumOffset`, and
rewrite to this form only when matching paper notation.
-/
lemma apSumOffset_eq_sum_Icc (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) := by
  classical
  unfold apSumOffset
  have h :=
    (Finset.sum_Ico_eq_sum_range (f := fun i => f (i * d)) (m := m + 1) (n := m + (n + 1)))
  have hlen : (m + (n + 1)) - (m + 1) = n := by
    -- `(m+1+n) - (m+1) = n`, and `m+1+n = m+(n+1)`.
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Nat.add_sub_cancel_left (m + 1) n)
  calc
    (Finset.range n).sum (fun i => f ((m + i + 1) * d))
        = (Finset.range n).sum (fun i => f ((m + (i + 1)) * d)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            -- `m + i + 1 = m + (i + 1)`
            simp [Nat.add_assoc]
    _ = (Finset.Ico (m + 1) (m + (n + 1))).sum (fun i => f (i * d)) := by
            -- `h` is oriented from `Ico` to `range`; we use it backwards.
            simpa [hlen, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h.symm
    _ = (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) := by
            -- Convert the upper endpoint to the canonical `(m+n)+1` form.
            have hend : m + (n + 1) = (m + n) + 1 := by
              simp [Nat.add_assoc]
            have hsum :
                (Finset.Ico (m + 1) ((m + n) + 1)).sum (fun i => f (i * d)) =
                  (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) := by
              simpa using
                congrArg (fun s : Finset ℕ => s.sum (fun i => f (i * d)))
                  (Finset.Ico_add_one_right_eq_Icc (a := m + 1) (b := m + n))
            simpa [hend] using hsum

/-- Paper-interval discrepancy normal form: rewrite `discOffset` directly as an `Icc`-sum.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Paper-interval discrepancy normal form.

This is the stable bridge lemma for surface statements written in paper notation.
-/
lemma discOffset_eq_natAbs_sum_Icc (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset f d m n =
      Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) := by
  unfold discOffset
  -- `discOffset` is definitional `Int.natAbs (apSumOffset ...)`.
  -- Rewrite `apSumOffset` into paper notation.
  simpa [apSumOffset_eq_sum_Icc]

/-- `simp` lemma: normalize a paper `Icc` discrepancy into the nucleus wrapper `discOffset`.

This is oriented in the **normal-form direction** (paper notation → nucleus).

Checklist item: Problems/erdos_discrepancy.md (Track B) — One-shot “normalization pipeline” wrapper.
-/
@[simp] lemma natAbs_sum_Icc_eq_discOffset (f : ℕ → ℤ) (d m n : ℕ) :
    Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) = discOffset f d m n := by
  simpa using
    (discOffset_eq_natAbs_sum_Icc (f := f) (d := d) (m := m) (n := n)).symm

/-- One-shot goal rewrite: a paper-style bound on `Int.natAbs (∑ i ∈ Icc …, f (i*d))`
can be rewritten into the nucleus form `discOffset f d m n ≤ C` in a single `simp`/`simpa` step.

Checklist item: Problems/erdos_discrepancy.md (Track B) — One-shot “normalization pipeline” wrapper.
-/
lemma natAbs_sum_Icc_le_iff_discOffset_le (f : ℕ → ℤ) (d m n C : ℕ) :
    Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) ≤ C ↔
      discOffset f d m n ≤ C := by
  -- Just rewrite the `Int.natAbs` expression to `discOffset`.
  simpa [natAbs_sum_Icc_eq_discOffset (f := f) (d := d) (m := m) (n := n)]


/-!
## `discOffsetUpTo` paper↔nucleus bridge

Checklist item: Problems/erdos_discrepancy.md (Track B) — `discOffsetUpTo` paper↔nucleus bridge.

The nucleus API defines `discOffsetUpTo` as a finitary `Finset.sup` over lengths `n ≤ N`.
Paper arguments often want to range over the *right endpoint* `b = m + n` instead.

This lemma rewrites between these two equivalent finitary maximizations.
-/

/-- Rewrite `discOffsetUpTo` as a supremum over paper-style interval endpoints.

Concretely, this transports the supremum over lengths `n ≤ N` to a supremum over endpoints
`b ∈ Icc m (m+N)` with the paper-interval discrepancy expression
`Int.natAbs (∑ i ∈ Icc (m+1) b, f (i*d))`.
-/
lemma discOffsetUpTo_eq_sup_Icc_endpoints (f : ℕ → ℤ) (d m N : ℕ) :
    discOffsetUpTo f d m N =
      (Finset.Icc m (m + N)).sup
        (fun b => Int.natAbs ((Finset.Icc (m + 1) b).sum (fun i => f (i * d)))) := by
  classical
  unfold discOffsetUpTo
  apply le_antisymm
  · -- `≤`: turn a length witness `n ≤ N` into an endpoint witness `b = m+n`.
    refine Finset.sup_le ?_
    intro n hn
    have hnle : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.1 hn)
    -- Show `m+n ∈ Icc m (m+N)`.
    have hmem : m + n ∈ Finset.Icc m (m + N) := by
      refine Finset.mem_Icc.2 ?_
      constructor
      · exact Nat.le_add_right _ _
      · exact Nat.add_le_add_left hnle _
    -- Discharge via `le_sup` at the endpoint `b = m+n`.
    -- `simp` then normalizes the paper `Int.natAbs (Icc-sum)` expression back to `discOffset`.
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Finset.le_sup (s := Finset.Icc m (m + N))
        (f := fun b => Int.natAbs ((Finset.Icc (m + 1) b).sum (fun i => f (i * d))))
        hmem)
  · -- `≥`: turn an endpoint witness `b ∈ Icc m (m+N)` into a length witness `n = b-m ≤ N`.
    refine Finset.sup_le ?_
    intro b hb
    rcases Finset.mem_Icc.1 hb with ⟨hmb, hbN⟩
    have hnle : b - m ≤ N := by
      -- From `b ≤ m+N`, subtract `m` from both sides.
      have : b - m ≤ (m + N) - m := Nat.sub_le_sub_right hbN _
      simpa [Nat.add_sub_cancel_left] using this
    have hnmem : b - m ∈ Finset.range (N + 1) := by
      exact Finset.mem_range.2 (Nat.lt_succ_of_le hnle)
    -- Compare the paper expression at `b` with the nucleus `discOffset` at length `b-m`.
    have hrewrite :
        Int.natAbs ((Finset.Icc (m + 1) b).sum (fun i => f (i * d))) =
          discOffset f d m (b - m) := by
      -- Normalize the endpoint `b` into the canonical `m + (b - m)` shape expected by the simp bridge.
      have hmadd : m + (b - m) = b := by
        simpa [Nat.add_comm] using (Nat.sub_add_cancel hmb)
      -- Use the simp lemma at the canonical endpoint, then rewrite `m + (b - m) = b`.
      simpa [hmadd, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (natAbs_sum_Icc_eq_discOffset (f := f) (d := d) (m := m) (n := b - m))
    -- Finish via `le_sup` in the original `range` finset.
    -- (Note: `le_sup` expects the function in the `sup` to match exactly.)
    simpa [hrewrite] using
      (Finset.le_sup (s := Finset.range (N + 1)) (f := fun n => discOffset f d m n) hnmem)


/-- One-shot goal rewrite: a paper-style `Icc` endpoint bound on `discOffsetUpTo`.

This is the finitary statement that
`discOffsetUpTo f d m N ≤ C`
iff *every* endpoint `b ∈ Icc m (m+N)` has paper discrepancy
`Int.natAbs (∑ i ∈ Icc (m+1) b, f (i*d)) ≤ C`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — `discOffsetUpTo` paper↔nucleus bridge
(endpoint style).
-/
lemma discOffsetUpTo_le_iff_forall_Icc_endpoints (f : ℕ → ℤ) (d m N C : ℕ) :
    discOffsetUpTo f d m N ≤ C ↔
      ∀ b ∈ Finset.Icc m (m + N),
        Int.natAbs ((Finset.Icc (m + 1) b).sum (fun i => f (i * d))) ≤ C := by
  classical
  -- Rewrite `discOffsetUpTo` into the paper-endpoint `sup`, then use `Finset.sup_le_iff`.
  simpa [discOffsetUpTo_eq_sup_Icc_endpoints] using
    (Finset.sup_le_iff (s := Finset.Icc m (m + N))
      (f := fun b => Int.natAbs ((Finset.Icc (m + 1) b).sum (fun i => f (i * d))))
      (a := C))


/-- Paper-endpoint normalization for `discOffsetUpTo`: rewrite directly into a `sup` of paper-interval
expressions indexed by the length parameter `n ≤ N`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Paper-endpoint normalization for
`discOffsetUpTo`.
-/
lemma discOffsetUpTo_eq_sup_range_Icc (f : ℕ → ℤ) (d m N : ℕ) :
    discOffsetUpTo f d m N =
      (Finset.range (N + 1)).sup
        (fun n => Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)))) := by
  classical
  unfold discOffsetUpTo
  -- Rewrite each paper `Int.natAbs (Icc-sum)` term back into the nucleus wrapper `discOffset`.
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Paper↔nucleus bridge for `discOffsetUpTo` (endpoint style): rewrite the `Finset.range (N+1)`
supremum in `discOffsetUpTo_eq_sup_range_Icc` as a supremum over `Finset.Icc 0 N`.

This matches the common “witness `n ≤ N`” convention used in later Tao2015 stages.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Paper↔nucleus bridge for
`discOffsetUpTo` (endpoint style).
-/
lemma discOffsetUpTo_eq_sup_Icc_lengths (f : ℕ → ℤ) (d m N : ℕ) :
    discOffsetUpTo f d m N =
      (Finset.Icc 0 N).sup
        (fun n => Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)))) := by
  classical
  have hrange : (Finset.range (N + 1)) = Finset.Icc 0 N := by
    simpa using (Nat.range_eq_Icc_zero_sub_one (N + 1) (Nat.add_one_ne_zero N))
  simpa [hrange] using (discOffsetUpTo_eq_sup_range_Icc (f := f) (d := d) (m := m) (N := N))

/-- One-shot goal rewrite: a bound on `discOffsetUpTo` is equivalent to a uniform bound on the
paper-interval discrepancy expressions `Int.natAbs (∑ i ∈ Icc (m+1) (m+n), f (i*d))` for all
lengths `n ≤ N`.

This packages `discOffsetUpTo_eq_sup_range_Icc` together with `Finset.sup_le_iff`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — `discOffsetUpTo` paper↔nucleus bridge
(endpoint style): one-shot bound rewrite.
-/
lemma discOffsetUpTo_le_iff_forall_range_Icc (f : ℕ → ℤ) (d m N C : ℕ) :
    discOffsetUpTo f d m N ≤ C ↔
      ∀ n ∈ Finset.range (N + 1),
        Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) ≤ C := by
  classical
  -- Rewrite `discOffsetUpTo` to a `sup` over paper expressions.
  -- Then `sup ≤ C` iff all entries are `≤ C`.
  simpa [discOffsetUpTo_eq_sup_range_Icc] using
    (Finset.sup_le_iff (s := Finset.range (N + 1))
      (f := fun n => Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))))
      (a := C))

/-!
## “One-cut in paper notation” bridge

These lemmas let you split a paper-style interval sum into two pieces and then immediately
rewrite both pieces into the nucleus API `apSumOffset`.

The point is to keep downstream proofs working with the stable normal form while still allowing
surface statements to be written in the familiar paper notation.
-/

/-- Split a paper-style interval sum at the interior cut `m+n₁`.

Concretely, this splits
`∑ i ∈ Icc (m+1) (m+n₁+n₂), f (i*d)`
into two paper sums over `Icc (m+1) (m+n₁)` and `Icc (m+n₁+1) (m+n₁+n₂)`.
-/
lemma sum_Icc_add_len_split (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    (Finset.Icc (m + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) =
      (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d)) +
        (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) := by
  -- Convert the paper notation to the nucleus, split in the nucleus, then convert back.
  classical
  -- LHS → nucleus.
  have hL :
      (Finset.Icc (m + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) =
        apSumOffset f d m (n₁ + n₂) := by
    simpa [Nat.add_assoc] using
      (apSumOffset_eq_sum_Icc (f := f) (d := d) (m := m) (n := n₁ + n₂)).symm
  -- Each RHS paper piece → nucleus.
  have hR1 :
      (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d)) = apSumOffset f d m n₁ := by
    simpa using (apSumOffset_eq_sum_Icc (f := f) (d := d) (m := m) (n := n₁)).symm
  have hR2 :
      (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) =
        apSumOffset f d (m + n₁) n₂ := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (apSumOffset_eq_sum_Icc (f := f) (d := d) (m := m + n₁) (n := n₂)).symm
  -- Split in the nucleus and rewrite back.
  -- Note: the split lemma lives in `Basic.lean` and is re-exported via the stable surface.
  calc
    (Finset.Icc (m + 1) (m + n₁ + n₂)).sum (fun i => f (i * d))
        = apSumOffset f d m (n₁ + n₂) := hL
    _ = apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
          simpa using (apSumOffset_add_len (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))
    _ = (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d)) +
          (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) := by
          simpa [hR1, hR2]

/-- The same “one-cut” split, but with both pieces immediately rewritten to the nucleus API.

This is the lemma you usually want in proofs: it lets you start from paper notation and end
in the canonical `apSumOffset` normal form in one step.
-/
lemma sum_Icc_add_len_eq_apSumOffset_add (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    (Finset.Icc (m + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) =
      apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
  -- First split in paper notation, then rewrite each piece.
  classical
  simpa [apSumOffset_eq_sum_Icc] using
    (sum_Icc_add_len_split (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)).trans
      (by
        -- Rewrite each paper sum to `apSumOffset`.
        -- We use `simp` with `apSumOffset_eq_sum_Icc` in the right orientation.
        -- (The `simp` target is the nucleus form.)
        simp [apSumOffset_eq_sum_Icc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm])

/-!
### “Cut at k” coherence lemmas for paper `Icc` notation

Checklist item: Problems/erdos_discrepancy.md (Track B) —
“Cut at k” API coherence for paper notation: provide paper-style cut lemmas at the `Icc` level
(both sum- and disc-level).

These are convenience wrappers around `sum_Icc_add_len_split`/`sum_Icc_add_len_eq_apSumOffset_add`
that expose the common `k ≤ n` cut parameterization directly.
-/

/-- Paper-notation cut lemma (sum level): split the tail interval at length `k ≤ n` and rewrite to
`apSumOffset` pieces.

Concretely, this rewrites
`∑ i ∈ Icc (m+1) (m+n), f (i*d)`
into
`apSumOffset f d m k + apSumOffset f d (m+k) (n-k)`.
-/
lemma sum_Icc_eq_apSumOffset_cut (f : ℕ → ℤ) (d m n k : ℕ) (hk : k ≤ n) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) =
      apSumOffset f d m k + apSumOffset f d (m + k) (n - k) := by
  have hn : k + (n - k) = n := Nat.add_sub_of_le hk
  -- Specialize the two-length split and rewrite endpoints via `hn`.
  simpa [hn, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (sum_Icc_add_len_eq_apSumOffset_add (f := f) (d := d) (m := m) (n₁ := k) (n₂ := n - k))

/-- Paper-notation cut lemma (discrepancy level): split the `Icc` sum at length `k ≤ n` **without**
leaving paper notation.

This is useful when a proof wants to remain in `Icc`-indexed sums but still perform a cut.
-/
lemma discOffset_eq_natAbs_sum_Icc_cut (f : ℕ → ℤ) (d m n k : ℕ) (hk : k ≤ n) :
    discOffset f d m n =
      Int.natAbs
        ((Finset.Icc (m + 1) (m + k)).sum (fun i => f (i * d)) +
          (Finset.Icc (m + k + 1) (m + n)).sum (fun i => f (i * d))) := by
  have hn : k + (n - k) = n := Nat.add_sub_of_le hk
  -- Split the paper interval sum at `k`, then apply `Int.natAbs`.
  have hsplit :
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) =
        (Finset.Icc (m + 1) (m + k)).sum (fun i => f (i * d)) +
          (Finset.Icc (m + k + 1) (m + n)).sum (fun i => f (i * d)) := by
    -- Start from the two-parameter split, then rewrite the endpoints.
    simpa [hn, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (sum_Icc_add_len_split (f := f) (d := d) (m := m) (n₁ := k) (n₂ := n - k))
  -- Now rewrite `discOffset` into paper notation and replace the interval sum using `hsplit`.
  calc
    discOffset f d m n = Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) := by
      simpa using (discOffset_eq_natAbs_sum_Icc (f := f) (d := d) (m := m) (n := n))
    _ = Int.natAbs
          ((Finset.Icc (m + 1) (m + k)).sum (fun i => f (i * d)) +
            (Finset.Icc (m + k + 1) (m + n)).sum (fun i => f (i * d))) := by
          simpa [hsplit]

/-- Rewrite `apSumOffset` as a length-indexed interval sum over `Icc 1 n`.

Concretely, this is the form
`∑ i ∈ Icc 1 n, f ((m+i)*d)`.

This is sometimes convenient when you want an interval with a *fixed* lower endpoint and the
offset bookkeeping moved into the summand.
-/
lemma apSumOffset_eq_sum_Icc_length (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = (Finset.Icc 1 n).sum (fun i => f ((m + i) * d)) := by
  classical
  unfold apSumOffset
  -- Convert `Icc 1 n` to `Ico 1 (n+1)`, then use `sum_Ico_eq_sum_range`.
  have h :=
    (Finset.sum_Ico_eq_sum_range (f := fun i => f ((m + i) * d)) (m := 1) (n := n + 1))
  -- `h` is oriented `Ico → range`; we use it backwards and simplify.
  -- The key simplifications are `(n+1) - 1 = n` and `m + (1 + i) = m + i + 1`.
  simpa [Finset.Ico_add_one_right_eq_Icc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    h.symm

/-- Normal form: rewrite the “paper notation” length-indexed interval sum
`∑ i ∈ Icc 1 n, f ((m+i)*d)` back to `apSumOffset`.

This is the inverse orientation of `apSumOffset_eq_sum_Icc_length`.
-/
lemma sum_Icc_eq_apSumOffset_length (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc 1 n).sum (fun i => f ((m + i) * d)) = apSumOffset f d m n := by
  simpa using (apSumOffset_eq_sum_Icc_length (f := f) (d := d) (m := m) (n := n)).symm

/-- Translation-friendly variant of `apSumOffset_eq_sum_Icc_length` using `d * (m+i)`.

This avoids commuting multiplication under binders when your surrounding development already uses
`d * i` summand shapes.
-/
lemma apSumOffset_eq_sum_Icc_length_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = (Finset.Icc 1 n).sum (fun i => f (d * (m + i))) := by
  classical
  refine (apSumOffset_eq_sum_Icc_length (f := f) (d := d) (m := m) (n := n)).trans ?_
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Nat.mul_comm]

/-- Normal form: rewrite the “paper notation” length-indexed interval sum
`∑ i ∈ Icc 1 n, f (d*(m+i))` back to `apSumOffset`.

This is the inverse orientation of `apSumOffset_eq_sum_Icc_length_mul_left`.
-/
lemma sum_Icc_eq_apSumOffset_length_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc 1 n).sum (fun i => f (d * (m + i))) = apSumOffset f d m n := by
  simpa using
    (apSumOffset_eq_sum_Icc_length_mul_left (f := f) (d := d) (m := m) (n := n)).symm

/-- Translation-friendly variant of `apSumOffset_eq_sum_Icc_length` with the summand written as
`f (i*d + m*d)` instead of `f ((m+i)*d)`.

This is sometimes a good intermediate normal form if you want an explicit `x + const` structure
before applying translation lemmas.
-/
lemma apSumOffset_eq_sum_Icc_length_add (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = (Finset.Icc 1 n).sum (fun i => f (i * d + m * d)) := by
  classical
  refine (apSumOffset_eq_sum_Icc_length (f := f) (d := d) (m := m) (n := n)).trans ?_
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hmul : (m + i) * d = m * d + i * d := Nat.add_mul m i d
  have hcomm : m * d + i * d = i * d + m * d := by
    simpa using Nat.add_comm (m * d) (i * d)
  simpa using congrArg f (hmul.trans hcomm)

/-- Translation-friendly variant of `apSumOffset_eq_sum_Icc_length` with the constant on the left:
`f (m*d + i*d)`.

Compared to `apSumOffset_eq_sum_Icc_length_add`, this avoids an extra commutativity rewrite when
your surrounding development already prefers the `const + x` summand shape.
-/
lemma apSumOffset_eq_sum_Icc_length_add_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = (Finset.Icc 1 n).sum (fun i => f (m * d + i * d)) := by
  classical
  refine (apSumOffset_eq_sum_Icc_length (f := f) (d := d) (m := m) (n := n)).trans ?_
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- `(m+i)*d = m*d + i*d`.
  simpa using congrArg f (Nat.add_mul m i d)

/-- Inverse orientation of `apSumOffset_eq_sum_Icc_length_add`. -/
lemma sum_Icc_eq_apSumOffset_length_add (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc 1 n).sum (fun i => f (i * d + m * d)) = apSumOffset f d m n := by
  simpa using (apSumOffset_eq_sum_Icc_length_add (f := f) (d := d) (m := m) (n := n)).symm

/-- Inverse orientation of `apSumOffset_eq_sum_Icc_length_add_left`. -/
lemma sum_Icc_eq_apSumOffset_length_add_left (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc 1 n).sum (fun i => f (m * d + i * d)) = apSumOffset f d m n := by
  simpa using
    (apSumOffset_eq_sum_Icc_length_add_left (f := f) (d := d) (m := m) (n := n)).symm

/-- Mul-left + translation-friendly variant of `apSumOffset_eq_sum_Icc_length_mul_left`, with the
summand written as `f (d*i + d*m)` instead of `f (d*(m+i))`.

This avoids commuting multiplication under binders and makes the translation by `d*m` explicit.
-/
lemma apSumOffset_eq_sum_Icc_length_mul_left_add (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = (Finset.Icc 1 n).sum (fun i => f (d * i + d * m)) := by
  classical
  refine (apSumOffset_eq_sum_Icc_length_mul_left (f := f) (d := d) (m := m) (n := n)).trans ?_
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hmul : d * (m + i) = d * m + d * i := Nat.mul_add d m i
  have hcomm : d * m + d * i = d * i + d * m := by
    simpa using Nat.add_comm (d * m) (d * i)
  simpa using congrArg f (hmul.trans hcomm)

/-- Inverse orientation of `apSumOffset_eq_sum_Icc_length_mul_left_add`. -/
lemma sum_Icc_eq_apSumOffset_length_mul_left_add (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc 1 n).sum (fun i => f (d * i + d * m)) = apSumOffset f d m n := by
  simpa using
    (apSumOffset_eq_sum_Icc_length_mul_left_add (f := f) (d := d) (m := m) (n := n)).symm

/-- Mul-left + translation-friendly variant of `apSumOffset_eq_sum_Icc_length_mul_left_add` with the
constant on the left: `f (d*m + d*i)`.

This avoids an extra commutativity rewrite under binders when your downstream development prefers
`const + x` summand shapes.
-/
lemma apSumOffset_eq_sum_Icc_length_mul_left_add_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = (Finset.Icc 1 n).sum (fun i => f (d * m + d * i)) := by
  classical
  refine (apSumOffset_eq_sum_Icc_length_mul_left_add (f := f) (d := d) (m := m) (n := n)).trans ?_
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- Commute the summand shape.
  simp [Nat.add_comm]

/-- Inverse orientation of `apSumOffset_eq_sum_Icc_length_mul_left_add_left`. -/
lemma sum_Icc_eq_apSumOffset_length_mul_left_add_left (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc 1 n).sum (fun i => f (d * m + d * i)) = apSumOffset f d m n := by
  simpa using
    (apSumOffset_eq_sum_Icc_length_mul_left_add_left (f := f) (d := d) (m := m) (n := n)).symm

/-- Normal form: relate the paper-notation tail interval sum over `Icc (m+1) (m+n)` to the
length-indexed `Icc 1 n` version.

Concretely, this rewrites
`∑ i ∈ Icc (m+1) (m+n), f (i*d)`
into
`∑ i ∈ Icc 1 n, f ((m+i)*d)`.

This is just `(apSumOffset_eq_sum_Icc …).symm` followed by `apSumOffset_eq_sum_Icc_length`.
-/
lemma sum_Icc_eq_sum_Icc_length (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) =
      (Finset.Icc 1 n).sum (fun i => f ((m + i) * d)) := by
  classical
  calc
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))
        = apSumOffset f d m n := by
            simpa using
              (apSumOffset_eq_sum_Icc (f := f) (d := d) (m := m) (n := n)).symm
    _ = (Finset.Icc 1 n).sum (fun i => f ((m + i) * d)) := by
            simpa using (apSumOffset_eq_sum_Icc_length (f := f) (d := d) (m := m) (n := n))

/-- Translation-friendly variant of `sum_Icc_eq_sum_Icc_length` using `d * i` and `d * (m+i)`.

This avoids commuting multiplication under binders.
-/
lemma sum_Icc_eq_sum_Icc_length_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) =
      (Finset.Icc 1 n).sum (fun i => f (d * (m + i))) := by
  classical
  -- Reduce to the `i * d` statement via commutativity.
  simpa [Nat.mul_comm] using
    (sum_Icc_eq_sum_Icc_length (f := f) (d := d) (m := m) (n := n))

/-- Variant of `sum_Icc_eq_sum_Icc_length` that makes the translation by `m*d` explicit.

Concretely, this rewrites
`∑ i ∈ Icc (m+1) (m+n), f (i*d)`
into
`∑ i ∈ Icc 1 n, f (i*d + m*d)`.

This can be a useful intermediate normal form when you want an explicit `x + const` summand shape
before applying translation lemmas.
-/
lemma sum_Icc_eq_sum_Icc_length_add (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) =
      (Finset.Icc 1 n).sum (fun i => f (i * d + m * d)) := by
  classical
  calc
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))
        = (Finset.Icc 1 n).sum (fun i => f ((m + i) * d)) := by
            simpa using sum_Icc_eq_sum_Icc_length (f := f) (d := d) (m := m) (n := n)
    _ = (Finset.Icc 1 n).sum (fun i => f (i * d + m * d)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hmul : (m + i) * d = m * d + i * d := Nat.add_mul m i d
            have hcomm : m * d + i * d = i * d + m * d := by
              simpa using Nat.add_comm (m * d) (i * d)
            simpa using congrArg f (hmul.trans hcomm)

/-- Mul-left variant of `sum_Icc_eq_sum_Icc_length_add` using `d * i` and `d * m`.

This avoids commuting multiplication under binders.
-/
lemma sum_Icc_eq_sum_Icc_length_mul_left_add (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) =
      (Finset.Icc 1 n).sum (fun i => f (d * i + d * m)) := by
  classical
  simpa [Nat.mul_comm] using
    (sum_Icc_eq_sum_Icc_length_add (f := f) (d := d) (m := m) (n := n))

/-- Mul-left + `const + x` variant of `sum_Icc_eq_sum_Icc_length_mul_left_add`.

This is convenient when downstream goals prefer the translation-friendly summand shape
`d * m + d * i`.
-/
lemma sum_Icc_eq_sum_Icc_length_mul_left_add_left (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) =
      (Finset.Icc 1 n).sum (fun i => f (d * m + d * i)) := by
  classical
  calc
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i))
        = (Finset.Icc 1 n).sum (fun i => f (d * i + d * m)) := by
            simpa using
              (sum_Icc_eq_sum_Icc_length_mul_left_add (f := f) (d := d) (m := m) (n := n))
    _ = (Finset.Icc 1 n).sum (fun i => f (d * m + d * i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            -- Commute the translation constant past the variable term.
            simp [Nat.add_comm]

/-- Special case: step size `d = 1` turns `apSumOffset` into the plain interval sum
`∑ i ∈ Icc (m+1) (m+n), f i`.

This is a small convenience wrapper around `apSumOffset_eq_sum_Icc`.
-/
lemma apSumOffset_one_d (f : ℕ → ℤ) (m n : ℕ) :
    apSumOffset f 1 m n = (Finset.Icc (m + 1) (m + n)).sum f := by
  simpa using (apSumOffset_eq_sum_Icc (f := f) (d := 1) (m := m) (n := n))

/-! ### `d = 1` simp-friendly normal forms (range-shift)

These lemmas are convenience wrappers for rewriting offset AP sums with step size `1` into a plain
`Finset.range` sum.

We provide both a translation-friendly binder form `i ↦ f (i + const)` and a constant-on-the-left
variant.
-/

@[simp] lemma apSumOffset_one_d_range (f : ℕ → ℤ) (m n : ℕ) :
    apSumOffset f 1 m n = (Finset.range n).sum (fun i => f (i + (m + 1))) := by
  -- Unfold and simplify `((m+i+1) * 1)` into `i + (m+1)`.
  unfold apSumOffset
  simp [Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma apSumOffset_one_d_range_add_left (f : ℕ → ℤ) (m n : ℕ) :
    apSumOffset f 1 m n = (Finset.range n).sum (fun i => f ((m + 1) + i)) := by
  simpa [Nat.add_comm] using (apSumOffset_one_d_range (f := f) (m := m) (n := n))

/-- Normal form: rewrite the “paper notation” interval sum `∑ i ∈ Icc (m+1) (m+n), f (i*d)` back
to `apSumOffset`.

This is useful when starting from a surface statement and normalizing into the nucleus API.
-/
lemma sum_Icc_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) = apSumOffset f d m n := by
  simpa using (apSumOffset_eq_sum_Icc (f := f) (d := d) (m := m) (n := n)).symm

/-- Translation-friendly variant of `apSumOffset_eq_sum_Icc` using `d * i` (step size on the left).

This is occasionally convenient when you want to share a summand shape with affine sums, which are
commonly written as `i * d + a`.
-/
lemma apSumOffset_eq_sum_Icc_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) := by
  classical
  refine (apSumOffset_eq_sum_Icc (f := f) (d := d) (m := m) (n := n)).trans ?_
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Nat.mul_comm]

/-- Normal form: rewrite the “paper notation” interval sum `∑ i ∈ Icc (m+1) (m+n), f (d*i)` back to
`apSumOffset`.

This is the inverse orientation of `apSumOffset_eq_sum_Icc_mul_left`.
-/
lemma sum_Icc_eq_apSumOffset_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) = apSumOffset f d m n := by
  simpa using (apSumOffset_eq_sum_Icc_mul_left (f := f) (d := d) (m := m) (n := n)).symm

/-- Mul-left variant of `discOffset_eq_natAbs_sum_Icc`, rewriting the summand as `f (d*i)`.

This is occasionally convenient when a paper statement has already normalized multiplication to the
`d * i` convention.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Stable-surface export audit for
paper-notation lemmas.
-/
lemma discOffset_eq_natAbs_sum_Icc_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset f d m n =
      Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i))) := by
  unfold discOffset
  simpa [apSumOffset_eq_sum_Icc_mul_left]

/-- Inverse orientation of `discOffset_eq_natAbs_sum_Icc_mul_left`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Stable-surface export audit for
paper-notation lemmas.
-/
@[simp] lemma natAbs_sum_Icc_mul_left_eq_discOffset (f : ℕ → ℤ) (d m n : ℕ) :
    Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i))) = discOffset f d m n := by
  simpa using
    (discOffset_eq_natAbs_sum_Icc_mul_left (f := f) (d := d) (m := m) (n := n)).symm

/-- Split the “paper notation” interval sum
`∑ i ∈ Icc (m+1) (m+(n₁+n₂)), f (i*d)` into the first `n₁` terms and the next `n₂` terms.

This is the interval-sum counterpart of the nucleus normal form `apSumOffset_add_length`.
-/
lemma sum_Icc_add_length (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d)) =
      (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d)) +
        (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) := by
  classical
  -- Normalize to offset sums, split by length, then rewrite back to interval sums.
  calc
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d))
        = apSumOffset f d m (n₁ + n₂) := by
            simpa using
              (sum_Icc_eq_apSumOffset (f := f) (d := d) (m := m) (n := n₁ + n₂))
    _ = apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
            simpa using
              (apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))
    _ = (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d)) +
          (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) := by
            simp [apSumOffset_eq_sum_Icc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- One-cut bridge (paper → nucleus): split a paper interval sum into two consecutive blocks and
rewrite both pieces directly to `apSumOffset`.

This is a convenience wrapper around `sum_Icc_eq_apSumOffset` and `apSumOffset_add_length`.
-/
lemma sum_Icc_eq_apSumOffset_add_length (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d)) =
      apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
  classical
  calc
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d))
        = apSumOffset f d m (n₁ + n₂) := by
            simpa using
              (sum_Icc_eq_apSumOffset (f := f) (d := d) (m := m) (n := n₁ + n₂))
    _ = apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
            simpa using
              (apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))

/-- Paper-pretty variant of `sum_Icc_eq_apSumOffset_add_length`, with the right endpoint written as
`m + n₁ + n₂` (no parentheses).

This is just a `simp` wrapper around `sum_Icc_eq_apSumOffset_add_length`.
-/
lemma sum_Icc_eq_apSumOffset_add_length_paper (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    (Finset.Icc (m + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) =
      apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
  simpa [Nat.add_assoc] using
    (sum_Icc_eq_apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))

/-- Translation-friendly variant of `sum_Icc_add_length` using `d * i` (step size on the left).

This is occasionally convenient when the surrounding development is already using the
`apSumOffset_eq_sum_Icc_mul_left` / `apSum_sub_eq_sum_Icc_mul_left` normal forms (so you don’t need
to commute multiplication under binders).
-/
lemma sum_Icc_add_length_mul_left (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (d * i)) =
      (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (d * i)) +
        (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (d * i)) := by
  classical
  -- Reduce to the `i * d` statement via commutativity.
  simpa [Nat.mul_comm] using
    (sum_Icc_add_length (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))

/-- Difference normal form for “paper notation” interval sums.

Subtracting the first `n₁` terms from the first `n₁ + n₂` terms leaves exactly the tail block.
This is the subtraction-oriented counterpart of `sum_Icc_add_length`.
-/
lemma sum_Icc_sub_sum_Icc_eq_sum_Icc (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d)) -
        (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d)) =
      (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) := by
  classical
  have h := sum_Icc_add_length (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)
  calc
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d)) -
        (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d))
        = ((Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d)) +
            (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d))) -
            (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d)) := by
            simpa [h]
    _ = (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) := by
            simp [add_sub_cancel_left]

/-- Translation-friendly variant of `sum_Icc_sub_sum_Icc_eq_sum_Icc` using `d * i` (step size on the
left). -/
lemma sum_Icc_sub_sum_Icc_eq_sum_Icc_mul_left (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (d * i)) -
        (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (d * i)) =
      (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (d * i)) := by
  classical
  simpa [Nat.mul_comm] using
    (sum_Icc_sub_sum_Icc_eq_sum_Icc (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))

/-- Normal form (paper → nucleus, difference → tail): subtracting the first block from a longer
block yields the corresponding `apSumOffset` tail.

This is a convenience wrapper around `sum_Icc_sub_sum_Icc_eq_sum_Icc` followed by
`sum_Icc_eq_apSumOffset`.
-/
lemma sum_Icc_sub_sum_Icc_eq_apSumOffset (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d)) -
        (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d)) =
      apSumOffset f d (m + n₁) n₂ := by
  classical
  calc
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d)) -
        (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d)) =
        (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) := by
          simpa using
            (sum_Icc_sub_sum_Icc_eq_sum_Icc (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))
    _ = apSumOffset f d (m + n₁) n₂ := by
          -- Normalize to the canonical `Icc ((m+n₁)+1) ((m+n₁)+n₂)` endpoint shape.
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            (sum_Icc_eq_apSumOffset (f := f) (d := d) (m := m + n₁) (n := n₂))

/-- Translation-friendly variant of `sum_Icc_sub_sum_Icc_eq_apSumOffset` using `d * i` (step size on
the left).

This is a convenience wrapper around `sum_Icc_sub_sum_Icc_eq_sum_Icc_mul_left` followed by
`sum_Icc_eq_apSumOffset_mul_left`.
-/
lemma sum_Icc_sub_sum_Icc_eq_apSumOffset_mul_left (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (d * i)) -
        (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (d * i)) =
      apSumOffset f d (m + n₁) n₂ := by
  classical
  calc
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (d * i)) -
        (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (d * i)) =
        (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (d * i)) := by
          simpa using
            (sum_Icc_sub_sum_Icc_eq_sum_Icc_mul_left (f := f) (d := d) (m := m) (n₁ := n₁)
              (n₂ := n₂))
    _ = apSumOffset f d (m + n₁) n₂ := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            (sum_Icc_eq_apSumOffset_mul_left (f := f) (d := d) (m := m + n₁) (n := n₂))

/-- Split the interval sum `∑ i ∈ Icc (m+1) n, f (i*d)` at an intermediate index `k`, assuming
`m ≤ k ≤ n`.

This is a convenience wrapper around `sum_Icc_add_length` that avoids manual arithmetic when your
surface statement uses a variable upper endpoint.
-/
lemma sum_Icc_split_of_le (f : ℕ → ℤ) (d : ℕ) {m k n : ℕ}
    (hmk : m ≤ k) (hkn : k ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) =
      (Finset.Icc (m + 1) k).sum (fun i => f (i * d)) +
        (Finset.Icc (k + 1) n).sum (fun i => f (i * d)) := by
  have hupper : m + ((k - m) + (n - k)) = n := by
    calc
      m + ((k - m) + (n - k)) = (m + (k - m)) + (n - k) := by
        simp [Nat.add_assoc]
      _ = k + (n - k) := by
        simp [Nat.add_sub_of_le hmk, Nat.add_assoc]
      _ = n := by
        simp [Nat.add_sub_of_le hkn]
  calc
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) =
        (Finset.Icc (m + 1) (m + ((k - m) + (n - k)))).sum (fun i => f (i * d)) := by
          simpa [hupper]
    _ = (Finset.Icc (m + 1) (m + (k - m))).sum (fun i => f (i * d)) +
          (Finset.Icc (m + (k - m) + 1) (m + (k - m) + (n - k))).sum (fun i => f (i * d)) := by
          simpa using
            (sum_Icc_add_length (f := f) (d := d) (m := m) (n₁ := k - m) (n₂ := n - k))
    _ = (Finset.Icc (m + 1) k).sum (fun i => f (i * d)) +
          (Finset.Icc (k + 1) n).sum (fun i => f (i * d)) := by
          simp [Nat.add_sub_of_le hmk, Nat.add_sub_of_le hkn, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm]

/-- Translation-friendly variant of `sum_Icc_split_of_le` using `d * i` (step size on the left). -/
lemma sum_Icc_split_of_le_mul_left (f : ℕ → ℤ) (d : ℕ) {m k n : ℕ}
    (hmk : m ≤ k) (hkn : k ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (d * i)) =
      (Finset.Icc (m + 1) k).sum (fun i => f (d * i)) +
        (Finset.Icc (k + 1) n).sum (fun i => f (d * i)) := by
  -- Reduce to the `i * d` statement via commutativity.
  simpa [Nat.mul_comm] using
    (sum_Icc_split_of_le (f := f) (d := d) (m := m) (k := k) (n := n) (hmk := hmk) (hkn := hkn))

/-- Normal form: when `m ≤ n`, rewrite the “paper notation” interval sum
`∑ i ∈ Icc (m+1) n, f (i*d)` back to `apSumOffset f d m (n - m)`.

This is a convenience wrapper around `sum_Icc_eq_apSumOffset` that normalizes the upper endpoint
into the canonical `(m + (n - m))` form.
-/
lemma sum_Icc_eq_apSumOffset_of_le (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) = apSumOffset f d m (n - m) := by
  simpa [Nat.add_sub_of_le hmn] using
    (sum_Icc_eq_apSumOffset (f := f) (d := d) (m := m) (n := n - m))

/-- Translation-friendly variant of `sum_Icc_eq_apSumOffset_of_le` using `d * i` (step size on the
left).

This avoids a commutativity rewrite under binders when you are working in a `d * i` convention.
-/
lemma sum_Icc_eq_apSumOffset_of_le_mul_left (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (d * i)) = apSumOffset f d m (n - m) := by
  classical
  -- Reduce to the `i * d` statement via commutativity.
  simpa [Nat.mul_comm] using
    (sum_Icc_eq_apSumOffset_of_le (f := f) (d := d) (m := m) (n := n) hmn)

/-- Convenience wrapper around `sum_Icc_eq_apSumOffset_of_le` specialized to the canonical tail
endpoint form `Icc (m+1) (m+n)`.

This is simp-friendly in downstream proofs because it avoids the explicit `Nat.add_sub_of_le`
normalization step that appears in the general `…_of_le` lemma.
-/
@[simp] lemma sum_Icc_eq_apSumOffset_of_le_add_len (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) = apSumOffset f d m n := by
  simpa using (sum_Icc_eq_apSumOffset (f := f) (d := d) (m := m) (n := n))

/-- Translation-friendly variant of `sum_Icc_eq_apSumOffset_of_le_add_len` using `d * i` (step size
on the left). -/
@[simp] lemma sum_Icc_eq_apSumOffset_of_le_add_len_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) = apSumOffset f d m n := by
  simpa using (sum_Icc_eq_apSumOffset_mul_left (f := f) (d := d) (m := m) (n := n))

/-- Checklist item (Track B): “Reindexing API coherence for `Icc` endpoints”.

These are small endpoint-normalization wrappers around
`sum_Icc_eq_apSumOffset_of_le_add_len{,_mul_left}` for common arithmetic shapes of the upper
endpoint, so downstream proofs can `simp` without fighting `Nat.add_assoc`/`Nat.add_comm`.
-/
@[simp] lemma sum_Icc_eq_apSumOffset_of_le_add_len_add_one (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n + 1)).sum (fun i => f (i * d)) = apSumOffset f d m (n + 1) := by
  -- `m + (n+1)` is the canonical form expected by `…_add_len`.
  simpa [Nat.add_assoc] using
    (sum_Icc_eq_apSumOffset_of_le_add_len (f := f) (d := d) (m := m) (n := n + 1))

@[simp] lemma sum_Icc_eq_apSumOffset_of_le_add_len_add_one_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n + 1)).sum (fun i => f (d * i)) = apSumOffset f d m (n + 1) := by
  simpa [Nat.add_assoc] using
    (sum_Icc_eq_apSumOffset_of_le_add_len_mul_left (f := f) (d := d) (m := m) (n := n + 1))

@[simp] lemma sum_Icc_eq_apSumOffset_of_le_add_len_add_comm (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (n + m)).sum (fun i => f (i * d)) = apSumOffset f d m n := by
  simpa [Nat.add_comm] using
    (sum_Icc_eq_apSumOffset_of_le_add_len (f := f) (d := d) (m := m) (n := n))

@[simp] lemma sum_Icc_eq_apSumOffset_of_le_add_len_add_comm_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (n + m)).sum (fun i => f (d * i)) = apSumOffset f d m n := by
  simpa [Nat.add_comm] using
    (sum_Icc_eq_apSumOffset_of_le_add_len_mul_left (f := f) (d := d) (m := m) (n := n))

@[simp] lemma sum_Icc_eq_apSumOffset_of_le_add_len_add_one_comm (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (n + m + 1)).sum (fun i => f (i * d)) = apSumOffset f d m (n + 1) := by
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (sum_Icc_eq_apSumOffset_of_le_add_len_add_one (f := f) (d := d) (m := m) (n := n))

@[simp] lemma sum_Icc_eq_apSumOffset_of_le_add_len_add_one_comm_mul_left
    (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (n + m + 1)).sum (fun i => f (d * i)) = apSumOffset f d m (n + 1) := by
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (sum_Icc_eq_apSumOffset_of_le_add_len_add_one_mul_left (f := f) (d := d) (m := m) (n := n))

/-- A simp-friendly alias for `sum_Icc_eq_apSumOffset_of_le_add_len`.

This specialises the `sum_Icc_eq_apSumOffset_of_le` family to the homogeneous tail interval
`Icc (m+1) (m+n)`.
-/
lemma sum_Icc_eq_apSumOffset_of_le_homogeneousTail
    (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) = apSumOffset f d m n := by
  simpa using (sum_Icc_eq_apSumOffset_of_le_add_len (f := f) (d := d) (m := m) (n := n))

/-- A simp-friendly alias for `sum_Icc_eq_apSumOffset_of_le_add_len_mul_left`.

This keeps the binder in the `d * i` convention, avoiding commutativity rewrites under binders in
downstream proofs.
-/
lemma sum_Icc_eq_apSumOffset_of_le_homogeneousTail_mul_left
    (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) = apSumOffset f d m n := by
  simpa using
    (sum_Icc_eq_apSumOffset_of_le_add_len_mul_left (f := f) (d := d) (m := m) (n := n))

/-- Surface form: when `m ≤ n`, rewrite the offset sum `apSumOffset f d m (n - m)` as the
interval sum `∑ i ∈ Icc (m+1) n, f (i*d)`.

This is the inverse orientation of `sum_Icc_eq_apSumOffset_of_le`.
-/
lemma apSumOffset_eq_sum_Icc_of_le (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    apSumOffset f d m (n - m) = (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) := by
  simpa using (sum_Icc_eq_apSumOffset_of_le (f := f) (d := d) (m := m) (n := n) hmn).symm

/-- Translation-friendly variant of `apSumOffset_eq_sum_Icc_of_le` using `d * i` (step size on the
left).

This is the inverse orientation of `sum_Icc_eq_apSumOffset_of_le_mul_left`.
-/
lemma apSumOffset_eq_sum_Icc_of_le_mul_left (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    apSumOffset f d m (n - m) = (Finset.Icc (m + 1) n).sum (fun i => f (d * i)) := by
  simpa using
    (sum_Icc_eq_apSumOffset_of_le_mul_left (f := f) (d := d) (m := m) (n := n) hmn).symm

/-- Difference of two homogeneous AP partial sums as an offset AP sum when `m ≤ n`. -/
lemma apSum_sub_apSum_eq_apSumOffset (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    apSum f d n - apSum f d m = apSumOffset f d m (n - m) := by
  -- use apSumOffset_eq_sub with length (n-m)
  have h := (apSumOffset_eq_sub (f := f) (d := d) (m := m) (n := n - m)).symm
  have hmn' : m + (n - m) = n := Nat.add_sub_of_le hmn
  simpa [hmn'] using h

/-- Convenience: when `m ≤ n`, rewrite an offset sum of length `n - m` as a difference of
homogeneous AP partial sums.

This is the inverse orientation of `apSum_sub_apSum_eq_apSumOffset`. It avoids the intermediate
endpoint `m + (n - m)` that appears when expanding `apSumOffset` via `apSumOffset_eq_sub`.
-/
lemma apSumOffset_eq_apSum_sub_apSum_of_le (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    apSumOffset f d m (n - m) = apSum f d n - apSum f d m := by
  simpa [Nat.add_sub_of_le hmn] using
    (apSumOffset_eq_sub (f := f) (d := d) (m := m) (n := n - m))

/-- Convenience: when `m ≤ n`, split `apSum f d n` into its first `m` terms and the remaining
`n - m` terms as an `apSumOffset`.

This is a small wrapper around `apSum_add_length` that normalizes the upper endpoint into the
canonical `m + (n - m)` form.
-/
lemma apSum_eq_add_apSumOffset_of_le (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    apSum f d n = apSum f d m + apSumOffset f d m (n - m) := by
  -- Normalize `n` as `m + (n - m)` and apply the length-splitting lemma.
  simpa [Nat.add_sub_of_le hmn] using (apSum_add_length (f := f) (d := d) (m := m) (n := n - m))

/-- Difference of a longer homogeneous AP partial sum and its initial segment, in the `(m + n) - m`
normal form.

This lemma is a convenience wrapper around `apSumOffset_eq_sub`, oriented so that rewriting
turns a subtraction into an explicit offset sum.
-/
lemma apSum_sub_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSum f d (m + n) - apSum f d m = apSumOffset f d m n := by
  simpa using (apSumOffset_eq_sub (f := f) (d := d) (m := m) (n := n)).symm

/-- Canonical “difference of partial sums” normal form for `discOffset`.

This is the `discOffset` wrapper around `apSum_sub_eq_apSumOffset`, oriented so rewriting turns
`discOffset` into the natural absolute value of a two-sum difference.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Canonical difference of partial sums
normal form (discOffset)”.
-/
lemma discOffset_eq_natAbs_apSum_sub (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset f d m n = Int.natAbs (apSum f d (m + n) - apSum f d m) := by
  unfold discOffset
  have h : apSumOffset f d m n = apSum f d (m + n) - apSum f d m := by
    simpa using (apSum_sub_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)).symm
  simpa [h]

/-- Rewrite the normal-form difference `apSum f d (m+n) - apSum f d m` as an interval sum
`∑ i ∈ Icc (m+1) (m+n), f (i*d)`.

This is intended for surface statements: keep the nucleus API in terms of `apSumOffset` and use
this lemma only when matching paper notation.
-/
lemma apSum_sub_eq_sum_Icc (f : ℕ → ℤ) (d m n : ℕ) :
    apSum f d (m + n) - apSum f d m =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) := by
  -- Rewrite subtraction to an offset sum, then to an interval sum.
  simp [apSum_sub_eq_apSumOffset, apSumOffset_eq_sum_Icc, -sum_Icc_eq_apSumOffset_of_le_add_len]

/-- Translation-friendly variant of `apSum_sub_eq_sum_Icc` using `d * i` (step size on the left). -/
lemma apSum_sub_eq_sum_Icc_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSum f d (m + n) - apSum f d m =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) := by
  classical
  refine (apSum_sub_eq_sum_Icc (f := f) (d := d) (m := m) (n := n)).trans ?_
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Nat.mul_comm]

/-- Rewrite the normal-form difference `apSum f d (m+n) - apSum f d m` as a length-indexed
interval sum over `Icc 1 n`.

Concretely, this is the normal form
`∑ i ∈ Icc 1 n, f ((m+i)*d)`.

This is sometimes convenient when you want a *fixed* lower endpoint (1) and you prefer to keep the
offset bookkeeping inside the summand, analogous to `apSumOffset_eq_sum_Icc_length`.
-/
lemma apSum_sub_eq_sum_Icc_length (f : ℕ → ℤ) (d m n : ℕ) :
    apSum f d (m + n) - apSum f d m =
      (Finset.Icc 1 n).sum (fun i => f ((m + i) * d)) := by
  -- Rewrite subtraction to an offset sum, then to a length-indexed interval sum.
  simp [apSum_sub_eq_apSumOffset, apSumOffset_eq_sum_Icc_length]

/-- Translation-friendly variant of `apSum_sub_eq_sum_Icc_length` using `d * (m+i)` (step size on
the left). -/
lemma apSum_sub_eq_sum_Icc_length_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSum f d (m + n) - apSum f d m =
      (Finset.Icc 1 n).sum (fun i => f (d * (m + i))) := by
  classical
  refine (apSum_sub_eq_sum_Icc_length (f := f) (d := d) (m := m) (n := n)).trans ?_
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Nat.mul_comm]

/-- Translation-friendly variant of `apSum_sub_apSum_eq_sum_Icc` using `d * i` (step size on the
left).

This is occasionally convenient when you want to share a summand shape with affine sums.
-/
lemma apSum_sub_apSum_eq_sum_Icc_mul_left (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    apSum f d n - apSum f d m = (Finset.Icc (m + 1) n).sum (fun i => f (d * i)) := by
  classical
  calc
    apSum f d n - apSum f d m = apSumOffset f d m (n - m) := by
        simpa using apSum_sub_apSum_eq_apSumOffset (f := f) (d := d) (m := m) (n := n) hmn
    _ = (Finset.Icc (m + 1) (m + (n - m))).sum (fun i => f (d * i)) := by
        simpa using
          (apSumOffset_eq_sum_Icc_mul_left (f := f) (d := d) (m := m) (n := n - m))
    _ = (Finset.Icc (m + 1) n).sum (fun i => f (d * i)) := by
        simp [Nat.add_sub_of_le hmn]

/-- Normal form (paper → nucleus, difference): rewrite the interval sum
`∑ i ∈ Icc (m+1) (m+n), f (d*i)` as the difference of homogeneous AP partial sums.

This is the inverse orientation of `apSum_sub_eq_sum_Icc_mul_left`.
-/
lemma sum_Icc_eq_apSum_sub_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) = apSum f d (m + n) - apSum f d m := by
  simpa using (apSum_sub_eq_sum_Icc_mul_left (f := f) (d := d) (m := m) (n := n)).symm

/-- Normal form (paper → nucleus, difference): when `m ≤ n`, rewrite
`∑ i ∈ Icc (m+1) n, f (d*i)` as a difference of homogeneous AP partial sums.

This is the inverse orientation of `apSum_sub_apSum_eq_sum_Icc_mul_left`.
-/
lemma sum_Icc_eq_apSum_sub_apSum_of_le_mul_left (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (d * i)) = apSum f d n - apSum f d m := by
  simpa using (apSum_sub_apSum_eq_sum_Icc_mul_left (f := f) (d := d) (m := m) (n := n) hmn).symm

/-- When `m ≤ n`, rewrite `apSum f d n - apSum f d m` as an interval sum
`∑ i ∈ Icc (m+1) n, f (i*d)`.

This is the “paper notation” counterpart of `apSum_sub_apSum_eq_apSumOffset`.
-/
lemma apSum_sub_apSum_eq_sum_Icc (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    apSum f d n - apSum f d m = (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) := by
  have h := apSum_sub_apSum_eq_apSumOffset (f := f) (d := d) (hmn := hmn)
  -- Rewrite the offset tail to an interval sum and simplify the endpoint `m + (n - m) = n`.
  simpa [apSumOffset_eq_sum_Icc, Nat.add_sub_of_le hmn] using h

/-- Normal form (paper → nucleus, difference): rewrite the interval sum
`∑ i ∈ Icc (m+1) (m+n), f (i*d)` as the difference of homogeneous AP partial sums.

This is the inverse orientation of `apSum_sub_eq_sum_Icc`.
-/
lemma sum_Icc_eq_apSum_sub (f : ℕ → ℤ) (d m n : ℕ) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) = apSum f d (m + n) - apSum f d m := by
  simpa using (apSum_sub_eq_sum_Icc (f := f) (d := d) (m := m) (n := n)).symm

/-- Normal form (paper → nucleus, difference): when `m ≤ n`, rewrite
`∑ i ∈ Icc (m+1) n, f (i*d)` as a difference of homogeneous AP partial sums.

This is the inverse orientation of `apSum_sub_apSum_eq_sum_Icc`.
-/
lemma sum_Icc_eq_apSum_sub_apSum_of_le (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) = apSum f d n - apSum f d m := by
  simpa using (apSum_sub_apSum_eq_sum_Icc (f := f) (d := d) (m := m) (n := n) hmn).symm

/-- Normal form (“step-one”): express an offset AP sum as an `apSumOffset` with step size `1`
by bundling the step size `d` into the summand.

This is the offset-sum analogue of `apSum_eq_apSum_step_one`.
-/
lemma apSumOffset_eq_apSumOffset_step_one (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSumOffset (fun k => f (k * d)) 1 m n := by
  unfold apSumOffset
  simp

/-!
### Step-one normalization for `discOffset`

Checklist item: Problems/erdos_discrepancy.md (Track B) — `discOffset` step-one normalization.
-/

/-- Normal form (“step-one”): push the step size into the summand for `discOffset`.

This is the `Int.natAbs` wrapper analogue of `apSumOffset_eq_apSumOffset_step_one`.
-/
lemma discOffset_eq_discOffset_step_one (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset f d m n = discOffset (fun k => f (k * d)) 1 m n := by
  -- Avoid `simp`: the simp bridge `Int.natAbs (apSumOffset …) = discOffset …` can loop.
  unfold discOffset
  -- Push the step into the summand at the `apSumOffset` level, then wrap with `Int.natAbs`.
  simpa using congrArg Int.natAbs (apSumOffset_eq_apSumOffset_step_one (f := f) (d := d) (m := m) (n := n))

/-- `mul_left`-friendly variant of `discOffset_eq_discOffset_step_one`.

This is occasionally convenient when the downstream normal form prefers `d * k`.
-/
lemma discOffset_eq_discOffset_step_one_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset f d m n = discOffset (fun k => f (d * k)) 1 m n := by
  -- Rewrite the summand index using commutativity.
  simpa [Nat.mul_comm] using (discOffset_eq_discOffset_step_one (f := f) (d := d) (m := m) (n := n))

/-- Combined “shift-start + step-one” normal form.

This pushes both a *start shift* `a` (in the underlying sequence) and the AP step `d` into the
summand, yielding the convenient translation-friendly shape `k*d + a`.
-/
lemma apSumOffset_shift_add_eq_apSumOffset_step_one_add_left (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumOffset (fun t => f (t + a)) d m n = apSumOffset (fun k => f (k * d + a)) 1 m n := by
  -- Apply the step-one lemma to the shifted function, then β-reduce.
  simpa using
    (apSumOffset_eq_apSumOffset_step_one (f := fun t => f (t + a)) (d := d) (m := m) (n := n))

-- (deprecated alias `apSumOffset_step_one_eq_apSumOffset` moved to `MoltResearch.Discrepancy.Deprecated`)

/-- Express `apSumOffset` as an `apSum` with step `1`. -/
lemma apSumOffset_eq_apSum_step_one (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSum (fun k => f ((m + k) * d)) 1 n := by
  unfold apSumOffset apSum
  -- `simp` reduces `((i+1)*1)` and normalizes `(m + (i+1))`.
  simp [Nat.add_assoc]

/-- Translation-friendly variant of `apSumOffset_eq_apSum_step_one`.

This rewrites the summand index from `((m + k) * d)` into the “constant on the right” form
`k * d + m * d` using `Nat.add_mul`.

This normal form is occasionally more convenient when you plan to apply translation lemmas that
expect an explicit `x + const` structure.
-/
lemma apSumOffset_eq_apSum_step_one_add_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSum (fun k => f (k * d + m * d)) 1 n := by
  -- Start from the canonical step-one form and rewrite the AP index.
  simpa [Nat.add_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (apSumOffset_eq_apSum_step_one (f := f) (d := d) (m := m) (n := n))

-- (deprecated alias `apSum_step_one_eq_apSumOffset` moved to `MoltResearch.Discrepancy.Deprecated`)

-- (deprecated alias `apSum_step_one_add_left_eq_apSumOffset` moved to `MoltResearch.Discrepancy.Deprecated`)

/-- Normal form: rewrite an offset AP sum to a step-one offset sum with zero offset by bundling the
offset `m` and step size `d` into the summand.

This is occasionally convenient when you want to reuse lemmas about `apSumOffset` while avoiding
both the explicit offset and the explicit step size.
-/
lemma apSumOffset_eq_apSumOffset_step_one_zero_m (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSumOffset (fun k => f ((m + k) * d)) 1 0 n := by
  calc
    apSumOffset f d m n = apSum (fun k => f ((m + k) * d)) 1 n := by
      simpa using apSumOffset_eq_apSum_step_one (f := f) (d := d) (m := m) (n := n)
    _ = apSumOffset (fun k => f ((m + k) * d)) 1 0 n := by
      simpa using
        (apSumOffset_zero_start (f := fun k => f ((m + k) * d)) (d := 1) (n := n)).symm

/-- Variant of `apSumOffset_eq_apSumOffset_step_one_zero_m` written in the translation-friendly
`k * d + m * d` form.

This eliminates both the offset parameter and the AP step size as explicit arguments of
`apSumOffset`, at the cost of moving them into the summand.
-/
lemma apSumOffset_eq_apSumOffset_step_one_zero_m_add_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSumOffset (fun k => f (k * d + m * d)) 1 0 n := by
  calc
    apSumOffset f d m n = apSum (fun k => f (k * d + m * d)) 1 n := by
      simpa using apSumOffset_eq_apSum_step_one_add_left (f := f) (d := d) (m := m) (n := n)
    _ = apSumOffset (fun k => f (k * d + m * d)) 1 0 n := by
      simpa using
        (apSumOffset_zero_start (f := fun k => f (k * d + m * d)) (d := 1) (n := n)).symm

/-- Normal form: rewrite the canonical difference `apSum f d (m+n) - apSum f d m` as a *step-one*
`apSumOffset` with `m = 0`, by bundling the step size `d` and offset `m` into the summand.

Concretely, this produces the translation-friendly summand shape `k * d + m * d`.

This is the `apSum`-difference analogue of `apSumOffset_eq_apSumOffset_step_one_zero_m_add_left`.
-/
lemma apSum_sub_eq_apSumOffset_step_one_zero_m_add_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSum f d (m + n) - apSum f d m = apSumOffset (fun k => f (k * d + m * d)) 1 0 n := by
  calc
    apSum f d (m + n) - apSum f d m = apSumOffset f d m n := by
      simpa using apSum_sub_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)
    _ = apSumOffset (fun k => f (k * d + m * d)) 1 0 n := by
      simpa using
        apSumOffset_eq_apSumOffset_step_one_zero_m_add_left (f := f) (d := d) (m := m) (n := n)

-- (deprecated inverse-orientation lemmas moved to `MoltResearch.Discrepancy.Deprecated`)

/-- Express `apSumOffset` as an `apSum` with the same step on a shifted function. -/
lemma apSumOffset_eq_apSum_shift (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSum (fun k => f (m * d + k)) d n := by
  unfold apSumOffset apSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hmul : (m + i + 1) * d = m * d + (i + 1) * d := by
    simpa [Nat.add_assoc] using (Nat.add_mul m (i + 1) d)
  -- rewrite the AP index in the summand
  simp [hmul]

/-- Mul-left variant of `apSumOffset_eq_apSum_shift` with translation constant written as `d*m`.

This avoids an extra commutativity rewrite when your surrounding development already prefers
multiplication-on-the-left forms (`d * i`) and hence naturally produces constants as `d*m`.
-/
lemma apSumOffset_eq_apSum_shift_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSum (fun k => f (d * m + k)) d n := by
  -- Start from the canonical `m*d + k` normal form and rewrite `m*d` as `d*m`.
  simpa [Nat.mul_comm] using
    (apSumOffset_eq_apSum_shift (f := f) (d := d) (m := m) (n := n))

/-- Variant of `apSumOffset_eq_apSum_shift` written in the translation-friendly `k + const` form.

This can be convenient when composing with lemmas that are oriented as `x ↦ x + k`.
-/
lemma apSumOffset_eq_apSum_shift_add (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSum (fun k => f (k + m * d)) d n := by
  have h := apSumOffset_eq_apSum_shift (f := f) (d := d) (m := m) (n := n)
  have hswap :
      apSum (fun k => f (m * d + k)) d n = apSum (fun k => f (k + m * d)) d n := by
    unfold apSum
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [Nat.add_comm]
  exact h.trans hswap

/-- Mul-left variant of `apSumOffset_eq_apSum_shift_add` with translation constant written as `d*m`.

This avoids an extra commutativity rewrite when your surrounding development already prefers
multiplication-on-the-left forms (`d * i`) and hence naturally produces constants as `d*m`.
-/
lemma apSumOffset_eq_apSum_shift_add_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSum (fun k => f (k + d * m)) d n := by
  -- Start from the canonical `k + m*d` normal form and rewrite `m*d` as `d*m`.
  simpa [Nat.mul_comm] using
    (apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n))

/-!
### Offset-of-offset flattening normal form

Checklist item: Problems/erdos_discrepancy.md (Track B) — Offset-of-offset flattening.

This lemma provides a conservative normal form that eliminates **nested `apSumOffset`** in the
summand by rewriting the inner offset sums using `apSumOffset_eq_apSum_shift_add`.

It is intentionally not tagged `[simp]`: it is a directed rewrite that can be useful in
normal-form pipelines, but we want to avoid accidental unfolding / simp blow-ups.
-/
lemma apSumOffset_offset_summand_eq_sum_apSum_shift_add
    (f : ℕ → ℤ) (d m n k : ℕ) :
    apSumOffset (fun t => apSumOffset f d (m + t) n) 1 0 k =
      (Finset.range k).sum (fun i => apSum (fun s => f (s + (m + (i + 1)) * d)) d n) := by
  -- Expand the outer `apSumOffset` (`d=1, m=0`).
  unfold apSumOffset
  -- The outer step-one offset sum is just a range sum over `i ↦ apSumOffset f d (m + (i+1)) n`.
  simp [Nat.mul_one, Nat.zero_add, Nat.add_assoc]
  -- Normalize each inner offset sum using `apSumOffset_eq_apSum_shift_add`.
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- Unfold `apSum` so the normal form is a plain range sum (no nested `apSumOffset`).
  simp [apSumOffset_eq_apSum_shift_add, apSum, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_assoc, Nat.add_mul, Nat.mul_add, two_mul]

/-- Length-splitting normal form: split an offset sum into a prefix offset sum and a shifted
homogeneous AP sum.

Concretely:

`apSumOffset f d m (n₁ + n₂) = apSumOffset f d m n₁ + apSum (fun k => f (k + (m + n₁) * d)) d n₂`.

This is just `apSumOffset_add_length` followed by the shifted-sequence normal form
`apSumOffset_eq_apSum_shift_add` on the tail.
-/
lemma apSumOffset_add_length_eq_add_apSum_shift_add (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    apSumOffset f d m (n₁ + n₂) =
      apSumOffset f d m n₁ + apSum (fun k => f (k + (m + n₁) * d)) d n₂ := by
  calc
    apSumOffset f d m (n₁ + n₂)
        = apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
            simpa using
              (apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))
    _ = apSumOffset f d m n₁ + apSum (fun k => f (k + (m + n₁) * d)) d n₂ := by
            -- Normalize the tail offset sum into a homogeneous AP sum on a shifted sequence.
            simp [apSumOffset_eq_apSum_shift_add]

/-- Corollary of `apSumOffset_add_length_eq_add_apSum_shift_add` for `n₁ = 0`. -/
lemma apSumOffset_add_length_eq_add_apSum_shift_add_zero_left
    (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m (0 + n) =
      apSumOffset f d m 0 + apSum (fun k => f (k + (m + 0) * d)) d n := by
  simpa using
    (apSumOffset_add_length_eq_add_apSum_shift_add (f := f) (d := d) (m := m) (n₁ := 0) (n₂ := n))

/-- Corollary of `apSumOffset_add_length_eq_add_apSum_shift_add` for `n₂ = 0`. -/
lemma apSumOffset_add_length_eq_add_apSum_shift_add_zero_right
    (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m (n + 0) =
      apSumOffset f d m n + apSum (fun k => f (k + (m + n) * d)) d 0 := by
  simpa using
    (apSumOffset_add_length_eq_add_apSum_shift_add (f := f) (d := d) (m := m) (n₁ := n) (n₂ := 0))

/-- Normal form: rewrite the normal-form difference `apSum f d (m+n) - apSum f d m` as a
homogeneous AP sum on a shifted sequence.

Concretely:
`apSum f d (m+n) - apSum f d m = apSum (fun k => f (k + m*d)) d n`.

This is `apSum_sub_eq_apSumOffset` followed by `apSumOffset_eq_apSum_shift_add`.
-/
lemma apSum_sub_eq_apSum_shift_add (f : ℕ → ℤ) (d m n : ℕ) :
    apSum f d (m + n) - apSum f d m = apSum (fun k => f (k + m * d)) d n := by
  calc
    apSum f d (m + n) - apSum f d m = apSumOffset f d m n := by
      simpa using apSum_sub_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)
    _ = apSum (fun k => f (k + m * d)) d n := by
      simpa using apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n)

/-- Normal form: rewrite the canonical difference `apSum f d (m+n) - apSum f d m` as an offset sum
with zero offset on the shifted sequence.

Concretely:
`apSum f d (m+n) - apSum f d m = apSumOffset (fun k => f (k + m*d)) d 0 n`.

This is `apSum_sub_eq_apSumOffset` followed by `apSumOffset_eq_apSumOffset_shift_add`.
-/
lemma apSum_sub_eq_apSumOffset_shift_add (f : ℕ → ℤ) (d m n : ℕ) :
    apSum f d (m + n) - apSum f d m = apSumOffset (fun k => f (k + m * d)) d 0 n := by
  calc
    apSum f d (m + n) - apSum f d m = apSum (fun k => f (k + m * d)) d n := by
      simpa using apSum_sub_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n)
    _ = apSumOffset (fun k => f (k + m * d)) d 0 n := by
      -- `apSumOffset g d 0 n` simp-normalizes to `apSum g d n`.
      simpa using
        (apSumOffset_eq_apSum_shift_add (f := fun k => f (k + m * d)) (d := d) (m := 0) (n := n)).symm

/-- Mul-left variant of `apSum_sub_eq_apSum_shift_add` with translation constant written as `d*m`.

This wrapper is useful when a downstream goal is already in the binder convention `d * i` and the
natural “shift” constant appears as `d*m` rather than `m*d`.
-/
lemma apSum_sub_eq_apSum_shift_add_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSum f d (m + n) - apSum f d m = apSum (fun k => f (k + d * m)) d n := by
  -- Rewrite the shift constant `m*d` as `d*m`.
  simpa [Nat.mul_comm] using
    (apSum_sub_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n))

/-- Variant of `apSum_sub_eq_apSum_shift_add` with the translation constant written as `m*d + k`.

This often avoids a commutativity rewrite when your downstream development already prefers the
`const + x` summand shape.
-/
lemma apSum_sub_eq_apSum_shift (f : ℕ → ℤ) (d m n : ℕ) :
    apSum f d (m + n) - apSum f d m = apSum (fun k => f (m * d + k)) d n := by
  calc
    apSum f d (m + n) - apSum f d m = apSumOffset f d m n := by
      simpa using apSum_sub_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)
    _ = apSum (fun k => f (m * d + k)) d n := by
      simpa using apSumOffset_eq_apSum_shift (f := f) (d := d) (m := m) (n := n)

/-- Normal form: when `m ≤ n`, rewrite `apSum f d n - apSum f d m` as a homogeneous AP sum on the
shifted sequence `k ↦ f (k + m*d)`.

Concretely:
`apSum f d n - apSum f d m = apSum (fun k => f (k + m*d)) d (n-m)`.

This is `apSum_sub_apSum_eq_apSumOffset` followed by `apSumOffset_eq_apSum_shift_add`.
-/
lemma apSum_sub_apSum_eq_apSum_shift_add_of_le (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    apSum f d n - apSum f d m = apSum (fun k => f (k + m * d)) d (n - m) := by
  calc
    apSum f d n - apSum f d m = apSumOffset f d m (n - m) := by
      simpa using apSum_sub_apSum_eq_apSumOffset (f := f) (d := d) (m := m) (n := n) hmn
    _ = apSum (fun k => f (k + m * d)) d (n - m) := by
      simpa using apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n - m)

/-- Variant of `apSum_sub_apSum_eq_apSum_shift_add_of_le` with the translation constant written as
`m*d + k`.

This can avoid a commutativity rewrite when composing with lemmas that expect the `const + x`
shape.
-/
lemma apSum_sub_apSum_eq_apSum_shift_of_le (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    apSum f d n - apSum f d m = apSum (fun k => f (m * d + k)) d (n - m) := by
  calc
    apSum f d n - apSum f d m = apSumOffset f d m (n - m) := by
      simpa using apSum_sub_apSum_eq_apSumOffset (f := f) (d := d) (m := m) (n := n) hmn
    _ = apSum (fun k => f (m * d + k)) d (n - m) := by
      simpa using apSumOffset_eq_apSum_shift (f := f) (d := d) (m := m) (n := n - m)

/-- Inverse orientation of `apSumOffset_eq_apSum_shift`. -/
lemma apSum_shift_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSum (fun k => f (m * d + k)) d n = apSumOffset f d m n := by
  simpa using (apSumOffset_eq_apSum_shift (f := f) (d := d) (m := m) (n := n)).symm

/-- Inverse orientation of `apSumOffset_eq_apSum_shift_add`.

We do *not* mark this as `[simp]`: our normal forms generally prefer to *introduce* the
translation-friendly shifted-sequence view.
-/
lemma apSum_shift_add_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSum (fun k => f (k + m * d)) d n = apSumOffset f d m n := by
  simpa using (apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n)).symm

/-- Normal form (paper → nucleus, shifted-sum): when `m ≤ n`, rewrite the interval sum
`∑ i ∈ Icc (m+1) n, f (i*d)` as a homogeneous AP sum on a shifted sequence.

Concretely:
`(Finset.Icc (m+1) n).sum (fun i => f (i*d)) = apSum (fun k => f (k + m*d)) d (n - m)`.

This is `sum_Icc_eq_apSumOffset_of_le` followed by `apSumOffset_eq_apSum_shift_add`.
-/
lemma sum_Icc_eq_apSum_shift_add_of_le (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) = apSum (fun k => f (k + m * d)) d (n - m) := by
  calc
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) = apSumOffset f d m (n - m) := by
      simpa using sum_Icc_eq_apSumOffset_of_le (f := f) (d := d) (m := m) (n := n) hmn
    _ = apSum (fun k => f (k + m * d)) d (n - m) := by
      simpa using apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n - m)

/-- Translation-friendly `d * i` variant of `sum_Icc_eq_apSum_shift_add_of_le`. -/
lemma sum_Icc_eq_apSum_shift_add_of_le_mul_left (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (d * i)) = apSum (fun k => f (k + m * d)) d (n - m) := by
  calc
    (Finset.Icc (m + 1) n).sum (fun i => f (d * i)) = apSumOffset f d m (n - m) := by
      simpa using sum_Icc_eq_apSumOffset_of_le_mul_left (f := f) (d := d) (m := m) (n := n) hmn
    _ = apSum (fun k => f (k + m * d)) d (n - m) := by
      simpa using apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n - m)

/-- Variant of `sum_Icc_eq_apSum_shift_add_of_le` with the translation constant written as `m*d + k`.

This can avoid a commutativity rewrite when composing with lemmas that expect the `const + x`
shape.
-/
lemma sum_Icc_eq_apSum_shift_of_le (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) = apSum (fun k => f (m * d + k)) d (n - m) := by
  calc
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) = apSumOffset f d m (n - m) := by
      simpa using sum_Icc_eq_apSumOffset_of_le (f := f) (d := d) (m := m) (n := n) hmn
    _ = apSum (fun k => f (m * d + k)) d (n - m) := by
      simpa using apSumOffset_eq_apSum_shift (f := f) (d := d) (m := m) (n := n - m)

/-- Translation-friendly `d * i` variant of `sum_Icc_eq_apSum_shift_of_le`. -/
lemma sum_Icc_eq_apSum_shift_of_le_mul_left (f : ℕ → ℤ) (d : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (d * i)) = apSum (fun k => f (m * d + k)) d (n - m) := by
  calc
    (Finset.Icc (m + 1) n).sum (fun i => f (d * i)) = apSumOffset f d m (n - m) := by
      simpa using sum_Icc_eq_apSumOffset_of_le_mul_left (f := f) (d := d) (m := m) (n := n) hmn
    _ = apSum (fun k => f (m * d + k)) d (n - m) := by
      simpa using apSumOffset_eq_apSum_shift (f := f) (d := d) (m := m) (n := n - m)

/-- Commute a translation in the shifted-sequence view of `apSumOffset`.

This is a convenience lemma: the two shifted sequences `k ↦ f (a + k)` and `k ↦ f (k + a)` are
definitionally different, and without this lemma you often need a `funext` + `Nat.add_comm` rewrite
to swap between them.

We do *not* mark this as `[simp]`: it is meant as an explicit normal-form rewrite when you want to
standardize on the translation-friendly `k + a` presentation.
-/
lemma apSumOffset_shift_comm (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumOffset (fun k => f (a + k)) d m n = apSumOffset (fun k => f (k + a)) d m n := by
  unfold apSumOffset
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Normalize an offset AP sum by shifting the underlying sequence and resetting the offset `m = 0`.

This can be a convenient normal form when you want to treat offset sums as homogeneous sums on a
shifted sequence, so that subsequent rewriting/simp lemmas only have to handle the `m = 0` case.

We provide both an `m*d + k` variant (constant on the left) and a translation-friendly `k + m*d`
variant (constant on the right).
-/
lemma apSumOffset_eq_apSumOffset_shift (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSumOffset (fun k => f (m * d + k)) d 0 n := by
  unfold apSumOffset
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- Both sides simplify to the same shifted index `m*d + (i+1)*d`.
  simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.add_mul]

/-- Translation-friendly variant of `apSumOffset_eq_apSumOffset_shift` written in the `k + const` form.

This can be convenient when composing with lemmas that are oriented as `x ↦ x + k`.
-/
lemma apSumOffset_eq_apSumOffset_shift_add (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSumOffset (fun k => f (k + m * d)) d 0 n := by
  -- Start from the `m*d + k` form and commute the addition in the summand.
  have h := apSumOffset_eq_apSumOffset_shift (f := f) (d := d) (m := m) (n := n)
  -- Rewrite `m*d + k` to `k + m*d` pointwise.
  unfold apSumOffset at h ⊢
  -- `simp` can now do the pointwise arithmetic normalization.
  simpa [Nat.add_comm] using h

/-- Inverse orientation of `apSumOffset_eq_apSumOffset_shift`. -/
lemma apSumOffset_shift_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset (fun k => f (m * d + k)) d 0 n = apSumOffset f d m n := by
  simpa using (apSumOffset_eq_apSumOffset_shift (f := f) (d := d) (m := m) (n := n)).symm

/-- Inverse orientation of `apSumOffset_eq_apSumOffset_shift_add`.

We do *not* mark this as `[simp]`: our normal forms usually prefer to *introduce* the explicit
shifted-sequence view and eliminate the offset parameter `m`.
-/
lemma apSumOffset_shift_add_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset (fun k => f (k + m * d)) d 0 n = apSumOffset f d m n := by
  simpa using (apSumOffset_eq_apSumOffset_shift_add (f := f) (d := d) (m := m) (n := n)).symm

/-!
### Boundedness transport lemmas (`BoundedDiscOffset`)

Checklist item: Problems/erdos_discrepancy.md (Track B) — Boundedness API hygiene.
-/

/-- Re-express `discOffset f d m n` as an `m = 0` discrepancy on a shifted sequence.

This is the `discOffset`-level wrapper of `apSumOffset_eq_apSumOffset_shift_add`.
-/
lemma discOffset_eq_discOffset_shift_add (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset f d m n = discOffset (fun k => f (k + m * d)) d 0 n := by
  -- Avoid `simp` loops by rewriting under `Int.natAbs` explicitly.
  unfold discOffset
  exact congrArg Int.natAbs
    (apSumOffset_eq_apSumOffset_shift_add (f := f) (d := d) (m := m) (n := n))

/-- Transport boundedness along the `apSumOffset_eq_apSumOffset_shift_add` viewpoint change.

If all offset discrepancies at start `m` are bounded by `B`, then the corresponding `m = 0`
discrepancies of the shifted sequence are bounded by the same `B`.
-/
theorem BoundedDiscOffset.map_shift_add {f : ℕ → ℤ} {d m B : ℕ}
    (h : BoundedDiscOffset f d m B) :
    BoundedDiscOffset (fun k => f (k + m * d)) d 0 B := by
  intro n
  -- Avoid `simp` recursion; just rewrite the goal.
  -- `discOffset f d m n = discOffset (fun k => f (k + m*d)) d 0 n`.
  rw [← discOffset_eq_discOffset_shift_add (f := f) (d := d) (m := m) (n := n)]
  exact h n

/-- Inverse transport for `BoundedDiscOffset.map_shift_add`. -/
theorem BoundedDiscOffset.of_map_shift_add {f : ℕ → ℤ} {d m B : ℕ}
    (h : BoundedDiscOffset (fun k => f (k + m * d)) d 0 B) :
    BoundedDiscOffset f d m B := by
  intro n
  rw [discOffset_eq_discOffset_shift_add (f := f) (d := d) (m := m) (n := n)]
  exact h n

/-!
### Predicate-level translation invariance (boundedness/unboundedness)

Checklist item: Problems/erdos_discrepancy.md (Track B) — Predicate-level translation invariance.

These lemmas repackage the pointwise transport lemmas above into equivalences between the
quantified boundedness/unboundedness predicates.
-/

/-- `BoundedDiscOffsetExists` is invariant under the shift `k ↦ f (k + m*d)`.

This is the predicate-level wrapper of `BoundedDiscOffset.map_shift_add`.
-/
theorem boundedDiscOffsetExists_shift_add_iff (f : ℕ → ℤ) (d m : ℕ) :
    BoundedDiscOffsetExists f d m ↔
      BoundedDiscOffsetExists (fun k => f (k + m * d)) d 0 := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    exact BoundedDiscOffset.map_shift_add (f := f) (d := d) (m := m) (B := B) hB
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    exact BoundedDiscOffset.of_map_shift_add (f := f) (d := d) (m := m) (B := B) hB

/-- `UnboundedDiscOffset` is invariant under the shift `k ↦ f (k + m*d)`.

Since `UnboundedDiscOffset` is defined as the negation of `BoundedDiscOffsetExists`, this is a
direct `not_congr` wrapper around `boundedDiscOffsetExists_shift_add_iff`.
-/
theorem unboundedDiscOffset_shift_add_iff (f : ℕ → ℤ) (d m : ℕ) :
    UnboundedDiscOffset f d m ↔
      UnboundedDiscOffset (fun k => f (k + m * d)) d 0 := by
  -- Unfold the definitional sugar and use negation congruence.
  simpa [UnboundedDiscOffset] using
    (not_congr (boundedDiscOffsetExists_shift_add_iff (f := f) (d := d) (m := m)))

/-- `BoundedDiscAlongExists` for the shifted sequence is equivalent to `BoundedDiscOffsetExists`
for the unshifted sequence.

This lemma is the predicate-level wrapper of the identity
`discAlong (fun k => f (k + m*d)) d n = discOffset f d m n`.
-/
theorem boundedDiscAlongExists_shift_add_iff (f : ℕ → ℤ) (d m : ℕ) :
    BoundedDiscAlongExists (fun k => f (k + m * d)) d ↔ BoundedDiscOffsetExists f d m := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- `hB n : discAlong (shifted) d n ≤ B`.
    -- Rewrite it into the `discOffset f d m n` view.
    -- First: `discAlong` is `discOffset _ d 0`.
    have hn : discOffset (fun k => f (k + m * d)) d 0 n ≤ B := by
      simpa [BoundedDiscOffset, discAlong] using hB n
    -- Then: use `discOffset_eq_discOffset_shift_add` to remove the shift.
    simpa [BoundedDiscOffset, discOffset_eq_discOffset_shift_add] using hn
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    have hn : discOffset f d m n ≤ B := by
      simpa [BoundedDiscOffset] using hB n
    have hn' : discOffset (fun k => f (k + m * d)) d 0 n ≤ B := by
      -- `discOffset f d m n = discOffset (shifted) d 0 n`.
      simpa [discOffset_eq_discOffset_shift_add] using hn
    simpa [discAlong] using hn'

/-!
### Further boundedness transports (`BoundedDiscOffset`)

These lemmas let downstream code rewrite boundedness hypotheses under the standard discrepancy
normal-form rewrite `step_one`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Bounded transport API.
-/

/-- Transport boundedness along `discOffset_eq_discOffset_step_one`. -/
theorem BoundedDiscOffset.map_step_one {f : ℕ → ℤ} {d m B : ℕ}
    (h : BoundedDiscOffset f d m B) :
    BoundedDiscOffset (fun k => f (k * d)) 1 m B := by
  intro n
  rw [← discOffset_eq_discOffset_step_one (f := f) (d := d) (m := m) (n := n)]
  exact h n

/-- Inverse transport for `BoundedDiscOffset.map_step_one`. -/
theorem BoundedDiscOffset.of_map_step_one {f : ℕ → ℤ} {d m B : ℕ}
    (h : BoundedDiscOffset (fun k => f (k * d)) 1 m B) :
    BoundedDiscOffset f d m B := by
  intro n
  rw [discOffset_eq_discOffset_step_one (f := f) (d := d) (m := m) (n := n)]
  exact h n

/-!
### Finite-length along-`d` boundedness transport (`BoundedDiscrepancyAlong`)

These lemmas let downstream code rewrite boundedness hypotheses between the offset form
(`discOffset f d m n`) and the along-`d` form on a shifted sequence
(`discAlong (fun k => f (k + m*d)) d n`) without unfolding definitions.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Boundedness API hygiene.
-/

/-- Re-express `discOffset f d m n` as an along-`d` discrepancy on the shifted sequence.

This is just `discOffset_eq_discOffset_shift_add` plus the `discAlong` wrapper.
-/
lemma discOffset_eq_discAlong_shift_add (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset f d m n = discAlong (fun k => f (k + m * d)) d n := by
  -- `discAlong g d n = discOffset g d 0 n` by definition.
  simpa [discAlong] using
    (discOffset_eq_discOffset_shift_add (f := f) (d := d) (m := m) (n := n))

/-- Inverse orientation of `discOffset_eq_discAlong_shift_add`. -/
lemma discAlong_shift_add_eq_discOffset (f : ℕ → ℤ) (d m n : ℕ) :
    discAlong (fun k => f (k + m * d)) d n = discOffset f d m n := by
  simpa using (discOffset_eq_discAlong_shift_add (f := f) (d := d) (m := m) (n := n)).symm

/-- Triangle inequality for `discAlong` across concatenation, in the along-`d` normal form.

This mirrors `discOffset_add_le`, but expresses the suffix segment as an along-`d` discrepancy on
the shifted sequence.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Triangle inequality for `discAlong` across concatenation.
-/
lemma discAlong_add_le (f : ℕ → ℤ) (d n₁ n₂ : ℕ) :
    discAlong f d (n₁ + n₂) ≤
      discAlong f d n₁ + discAlong (fun k => f (k + n₁ * d)) d n₂ := by
  -- Start from the offset concatenation inequality at `m = 0`.
  have h := discOffset_add_le (f := f) (d := d) (m := 0) (n₁ := n₁) (n₂ := n₂)
  -- Normalize the middle start index `0 + n₁`.
  have h' : discOffset f d 0 (n₁ + n₂) ≤ discOffset f d 0 n₁ + discOffset f d n₁ n₂ := by
    simpa [Nat.zero_add] using h
  -- Rewrite the suffix discrepancy into along-`d` form on the shifted sequence.
  -- (Avoid `simp [discAlong, discOffset_eq_discAlong_shift_add]` which can loop.)
  rw [discOffset_eq_discAlong_shift_add (f := f) (d := d) (m := n₁) (n := n₂)] at h'
  -- Finally, fold `discOffset f d 0 _` back into `discAlong`.
  simpa [discAlong] using h'

/-- If a uniform bound holds for all offset discrepancies, then it holds for the finite-length
along-`d` predicate on the shifted sequence. -/
theorem BoundedDiscOffset.toBoundedDiscrepancyAlong_shift_add {f : ℕ → ℤ} {d m B : ℕ} (len : ℕ)
    (h : BoundedDiscOffset f d m B) :
    BoundedDiscrepancyAlong (fun k => f (k + m * d)) d len B := by
  intro n hn
  -- Rewrite `discAlong` back to `discOffset` at start `m`.
  rw [discAlong_shift_add_eq_discOffset (f := f) (d := d) (m := m) (n := n)]
  exact h n

/-- Package a `BoundedDiscrepancyAlong` hypothesis on the shifted sequence as a boundedness
statement about `discOffset` up to `len`.

This is often the right shape when you want to later promote to a `BoundedDiscOffset` after
discharging `n ≤ len` (e.g. by choosing `len := n`).
-/
theorem BoundedDiscrepancyAlong.to_forall_le_discOffset_le_shift_add {f : ℕ → ℤ} {d m len B : ℕ}
    (h : BoundedDiscrepancyAlong (fun k => f (k + m * d)) d len B) :
    ∀ n : ℕ, n ≤ len → discOffset f d m n ≤ B := by
  intro n hn
  -- Rewrite the target into a `discAlong` statement.
  simpa [discOffset_eq_discAlong_shift_add (f := f) (d := d) (m := m) (n := n)] using h n hn

/-!
### Predicate-level translation invariance (boundedness / unboundedness)

These wrappers are the “quantifier-level” versions of `discOffset_eq_discAlong_shift_add`:
shifting the underlying sequence by an affine tail `m*d` does not change the boundedness or
unboundedness predicates.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Predicate-level translation invariance.
-/

/-- Boundedness-exists for `discOffset` is invariant under shifting the sequence by `m*d`.

Concretely, `discOffset f d m n` is definitionally the along-`d` discrepancy of the shifted
sequence `fun k => f (k + m*d)`, so existence of a uniform bound is equivalent.
-/
theorem boundedDiscOffsetExists_iff_boundedDiscAlongExists_shift_add (f : ℕ → ℤ) (d m : ℕ) :
    BoundedDiscOffsetExists f d m ↔ BoundedDiscAlongExists (fun k => f (k + m * d)) d := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- Rewrite `discAlong` on the shifted sequence back to `discOffset`.
    simpa [discAlong_shift_add_eq_discOffset (f := f) (d := d) (m := m) (n := n)] using hB n
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro n
    -- Rewrite `discOffset` into `discAlong` on the shifted sequence.
    simpa [discOffset_eq_discAlong_shift_add (f := f) (d := d) (m := m) (n := n)] using hB n

/-- Unboundedness (witness normal form) is invariant under shifting the sequence by `m*d`.

This is the natural dual of `boundedDiscOffsetExists_iff_boundedDiscAlongExists_shift_add`.
-/
theorem unboundedDiscOffset_iff_unboundedDiscAlong_shift_add (f : ℕ → ℤ) (d m : ℕ) :
    UnboundedDiscOffset f d m ↔ UnboundedDiscAlong (fun k => f (k + m * d)) d := by
  -- Reduce the left-hand side to the witness normal form and rewrite each witness inequality.
  simp [unboundedDiscOffset_iff_forall_exists_discOffset_lt, UnboundedDiscAlong,
    discOffset_eq_discAlong_shift_add]

/-- Mul-left variant of `apSumOffset_eq_apSumOffset_shift_add` using the translation constant `d*m`.

This avoids commuting multiplication in the shift constant when downstream development prefers
`d * m` over `m * d`.
-/
lemma apSumOffset_eq_apSumOffset_shift_add_mul_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m n = apSumOffset (fun k => f (k + d * m)) d 0 n := by
  -- Start from the canonical `k + m*d` normal form and rewrite `m*d` as `d*m`.
  simpa [Nat.mul_comm] using
    (apSumOffset_eq_apSumOffset_shift_add (f := f) (d := d) (m := m) (n := n))

/-- Inverse orientation of `apSumOffset_eq_apSumOffset_shift_add_mul_left`. -/
lemma apSumOffset_shift_add_mul_left_eq_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset (fun k => f (k + d * m)) d 0 n = apSumOffset f d m n := by
  simpa using
    (apSumOffset_eq_apSumOffset_shift_add_mul_left (f := f) (d := d) (m := m) (n := n)).symm

/-- Normal form: when `m ≤ n`, rewrite a difference of homogeneous AP partial sums
as an offset sum with `m = 0` on a shifted sequence.

Concretely:
`apSum f d n - apSum f d m = apSumOffset (fun k => f (k + m*d)) d 0 (n - m)`.

This combines `apSum_sub_apSum_eq_apSumOffset` with `apSumOffset_eq_apSumOffset_shift_add`.
-/
lemma apSum_sub_apSum_eq_apSumOffset_shift_add_of_le (f : ℕ → ℤ) (d : ℕ) {m n : ℕ}
    (hmn : m ≤ n) :
    apSum f d n - apSum f d m = apSumOffset (fun k => f (k + m * d)) d 0 (n - m) := by
  calc
    apSum f d n - apSum f d m = apSumOffset f d m (n - m) := by
      simpa using apSum_sub_apSum_eq_apSumOffset (f := f) (d := d) (m := m) (n := n) hmn
    _ = apSumOffset (fun k => f (k + m * d)) d 0 (n - m) := by
      simpa using
        (apSumOffset_eq_apSumOffset_shift_add (f := f) (d := d) (m := m) (n := n - m))

/-- Normal form: push an offset parameter into a translation of the underlying sequence.

Concretely, an offset sum on the shifted sequence `k ↦ f (k + a)` can be rewritten as an offset sum
with `m = 0` by absorbing the offset into the translation constant:

`apSumOffset (fun k => f (k + a)) d m n = apSumOffset (fun k => f (k + (a + m*d))) d 0 n`.

This is useful when you want to eliminate the explicit offset parameter `m` but keep the
translation-friendly `k + const` presentation.
-/
lemma apSumOffset_shift_add_eq_apSumOffset_shift_add (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumOffset (fun k => f (k + a)) d m n = apSumOffset (fun k => f (k + (a + m * d))) d 0 n := by
  -- First eliminate the offset parameter using the generic shifted-sequence normal form.
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (apSumOffset_eq_apSumOffset_shift_add (f := fun k => f (k + a)) (d := d) (m := m) (n := n))

/-- Inverse orientation of `apSumOffset_shift_add_eq_apSumOffset_shift_add`. -/
lemma apSumOffset_shift_add_shift_add_eq_apSumOffset_shift_add (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumOffset (fun k => f (k + (a + m * d))) d 0 n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using (apSumOffset_shift_add_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m)
    (n := n)).symm

/-- Normal form: normalize an *added* offset parameter on a shifted sequence.

Concretely, shifting the offset from `m` to `m + b` can be absorbed into the translation constant:

`apSumOffset (fun k => f (k + a)) d (m + b) n = apSumOffset (fun k => f (k + (a + b*d))) d m n`.

This keeps the binder in the translation-friendly `k + const` shape while preventing “shift
bookkeeping” from proliferating.
-/
lemma apSumOffset_shift_add_add_offset_eq (f : ℕ → ℤ) (a d m b n : ℕ) :
    apSumOffset (fun k => f (k + a)) d (m + b) n =
      apSumOffset (fun k => f (k + (a + b * d))) d m n := by
  -- Rewrite both sides using the `apSum` shifted-sequence normal form and simplify.
  simp [apSumOffset_eq_apSum_shift_add, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Inverse orientation of `apSumOffset_shift_add_add_offset_eq`. -/
lemma apSumOffset_shift_add_shift_add_eq_apSumOffset_shift_add_add_offset (f : ℕ → ℤ)
    (a d m b n : ℕ) :
    apSumOffset (fun k => f (k + (a + b * d))) d m n =
      apSumOffset (fun k => f (k + a)) d (m + b) n := by
  simpa using
    (apSumOffset_shift_add_add_offset_eq (f := f) (a := a) (d := d) (m := m) (b := b)
      (n := n)).symm

/-- Normal form: shift in the *start index* of an offset sum.

Concretely, shifting the start from `m` to `m + k` can be absorbed into a translation of the
summand function:

`apSumOffset f d (m + k) n = apSumOffset (fun t => f (t + k*d)) d m n`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Tail-shift coherence (sum level).

This is a specialization of `apSumOffset_shift_add_add_offset_eq` with `a = 0`.
-/
lemma apSumOffset_shift_start_add (f : ℕ → ℤ) (d m k n : ℕ) :
    apSumOffset f d (m + k) n = apSumOffset (fun t => f (t + k * d)) d m n := by
  simpa using
    (apSumOffset_shift_add_add_offset_eq (f := f) (a := 0) (d := d) (m := m) (b := k) (n := n))

/-- Add-left variant of `apSumOffset_shift_start_add`.

`apSumOffset f d (m + k) n = apSumOffset (fun t => f (k*d + t)) d m n`.
-/
lemma apSumOffset_shift_start_add_left (f : ℕ → ℤ) (d m k n : ℕ) :
    apSumOffset f d (m + k) n = apSumOffset (fun t => f (k * d + t)) d m n := by
  simpa [Nat.add_comm] using
    (apSumOffset_shift_start_add (f := f) (d := d) (m := m) (k := k) (n := n))

/-- Normal form (mul-left variant): shift in the *start index* using the translation constant `d*k`.

`apSumOffset f d (m + k) n = apSumOffset (fun t => f (t + d*k)) d m n`.

This is a thin wrapper around `apSumOffset_shift_start_add` that avoids commuting multiplication
in downstream developments that prefer the `d * k` convention.
-/
lemma apSumOffset_shift_start_add_mul_left (f : ℕ → ℤ) (d m k n : ℕ) :
    apSumOffset f d (m + k) n = apSumOffset (fun t => f (t + d * k)) d m n := by
  simpa [Nat.mul_comm] using
    (apSumOffset_shift_start_add (f := f) (d := d) (m := m) (k := k) (n := n))

/-- Normal form (add-left variant): push an offset parameter into a translation constant.

This is the `a + k` analogue of `apSumOffset_shift_add_eq_apSumOffset_shift_add`.

Concretely:
`apSumOffset (fun k => f (a + k)) d m n = apSumOffset (fun k => f ((a + m*d) + k)) d 0 n`.

We keep both `… + k` and `k + …` flavors available since `simp` often behaves better when we avoid
commuting addition under binders.
-/
lemma apSumOffset_shift_add_left_eq_apSumOffset_shift_add_left (f : ℕ → ℤ) (a d m n : ℕ) :
    apSumOffset (fun k => f (a + k)) d m n = apSumOffset (fun k => f ((a + m * d) + k)) d 0 n := by
  -- Eliminate the offset parameter using the generic `m*d + k` shifted-sequence view.
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (apSumOffset_eq_apSumOffset_shift (f := fun k => f (a + k)) (d := d) (m := m) (n := n))

/-- Inverse orientation of `apSumOffset_shift_add_left_eq_apSumOffset_shift_add_left`. -/
lemma apSumOffset_shift_add_left_shift_add_left_eq_apSumOffset_shift_add_left (f : ℕ → ℤ)
    (a d m n : ℕ) :
    apSumOffset (fun k => f ((a + m * d) + k)) d 0 n = apSumOffset (fun k => f (a + k)) d m n := by
  simpa using
    (apSumOffset_shift_add_left_eq_apSumOffset_shift_add_left (f := f) (a := a) (d := d) (m := m)
      (n := n)).symm

-- (lemma `apSumOffset_add_length` moved to `MoltResearch/Discrepancy/Basic.lean`)

/-- Split an offset AP sum at an intermediate length `n₁` when `n₁ ≤ n₂`.

This is the offset-sum analogue of `apSumFrom_eq_add_apSumFrom_tail`.
-/
lemma apSumOffset_eq_add_apSumOffset_tail (f : ℕ → ℤ) (d m : ℕ) {n₁ n₂ : ℕ}
    (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ =
      apSumOffset f d m n₁ + apSumOffset f d (m + n₁) (n₂ - n₁) := by
  -- Rewrite `n₂` as `n₁ + (n₂ - n₁)` and apply `apSumOffset_add_length`.
  simpa [Nat.add_sub_of_le hn] using
    (apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂ - n₁))

/-- Split the tail `apSumOffset f d m (n - m)` at an intermediate index `k`, assuming `m ≤ k ≤ n`.

Concretely, the tail from `m+1` to `n` splits into the tail from `m+1` to `k` and the tail from
`k+1` to `n`:

`apSumOffset f d m (n - m) = apSumOffset f d m (k - m) + apSumOffset f d k (n - k)`.
-/
lemma apSumOffset_eq_add_apSumOffset_of_le (f : ℕ → ℤ) (d : ℕ) {m k n : ℕ}
    (hmk : m ≤ k) (hkn : k ≤ n) :
    apSumOffset f d m (n - m) =
      apSumOffset f d m (k - m) + apSumOffset f d k (n - k) := by
  have hkm : k - m ≤ n - m := Nat.sub_le_sub_right hkn m
  have h :=
    apSumOffset_eq_add_apSumOffset_tail (f := f) (d := d) (m := m) (n₁ := k - m) (n₂ := n - m)
      hkm
  have hdiff : (n - m) - (k - m) = n - k := by
    calc
      (n - m) - (k - m) = n - (m + (k - m)) := by
        simpa [Nat.sub_sub]
      _ = n - k := by
        simpa [Nat.add_sub_of_le hmk]
  simpa [Nat.add_sub_of_le hmk, hdiff] using h

/-- Split an offset AP sum `apSumOffset f d m n` at an interior cut `k`, assuming `m ≤ k ≤ m+n`.

Concretely, the tail from `m+1` to `m+n` splits into the tail from `m+1` to `k` and the tail from
`k+1` to `m+n`:

`apSumOffset f d m n = apSumOffset f d m (k - m) + apSumOffset f d k (m + n - k)`.
-/
lemma apSumOffset_split_at (f : ℕ → ℤ) (d : ℕ) {m k n : ℕ}
    (hmk : m ≤ k) (hkn : k ≤ m + n) :
    apSumOffset f d m n =
      apSumOffset f d m (k - m) + apSumOffset f d k (m + n - k) := by
  -- Use the existing split lemma on the canonical tail form `apSumOffset f d m ((m+n) - m)`.
  simpa [Nat.add_sub_cancel] using
    (apSumOffset_eq_add_apSumOffset_of_le (f := f) (d := d) (m := m) (k := k) (n := m + n)
      hmk hkn)

/-- Split an offset AP sum `apSumOffset f d m n` at an interior cut `k`, proved by splitting the
paper-style `Icc` sum `∑ i ∈ Icc (m+1) (m+n), f (i*d)` at `k` and immediately rewriting back to
the nucleus normal form.

This complements `apSumOffset_split_at` with a proof path that stays close to paper endpoints,
which is often the easiest shape to match in downstream arguments.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Interior-cut equality (sum-level, offset).
-/
lemma apSumOffset_split_at_via_Icc (f : ℕ → ℤ) (d : ℕ) {m k n : ℕ}
    (hmk : m ≤ k) (hkn : k ≤ m + n) :
    apSumOffset f d m n =
      apSumOffset f d m (k - m) + apSumOffset f d k (m + n - k) := by
  classical
  -- Start from the paper notation, split at `k`, then normalize each piece back to `apSumOffset`.
  have hsplit :=
    (sum_Icc_split_of_le (f := f) (d := d) (m := m) (k := k) (n := m + n) hmk hkn)
  have hL :
      apSumOffset f d m n = (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) := by
    simpa using (apSumOffset_eq_sum_Icc (f := f) (d := d) (m := m) (n := n))
  have hR1 :
      (Finset.Icc (m + 1) k).sum (fun i => f (i * d)) = apSumOffset f d m (k - m) := by
    simpa using (sum_Icc_eq_apSumOffset_of_le (f := f) (d := d) (m := m) (n := k) hmk)
  have hR2 :
      (Finset.Icc (k + 1) (m + n)).sum (fun i => f (i * d)) = apSumOffset f d k (m + n - k) := by
    simpa using (sum_Icc_eq_apSumOffset_of_le (f := f) (d := d) (m := k) (n := m + n) hkn)
  -- Assemble.
  calc
    apSumOffset f d m n
        = (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) := hL
    _ = (Finset.Icc (m + 1) k).sum (fun i => f (i * d)) +
          (Finset.Icc (k + 1) (m + n)).sum (fun i => f (i * d)) := hsplit
    _ = apSumOffset f d m (k - m) + apSumOffset f d k (m + n - k) := by
          simp [hR1, hR2]

/-- First term of an offset AP sum. -/
lemma apSumOffset_succ_length (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m (n + 1) = f ((m + 1) * d) + apSumOffset f d (m + 1) n := by
  have h := apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := 1) (n₂ := n)
  simpa [Nat.add_comm, apSumOffset_one, add_comm] using h

/-- Rearranged version of `apSumOffset_succ_length`. -/
lemma apSumOffset_succ_offset (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d (m + 1) n = apSumOffset f d m (n + 1) - f ((m + 1) * d) := by
  have h : apSumOffset f d (m + 1) n + f ((m + 1) * d) = apSumOffset f d m (n + 1) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (apSumOffset_succ_length (f := f) (d := d) (m := m) (n := n)).symm
  simpa using eq_sub_of_add_eq h

-- NOTE: `apSumOffset_tail_eq_sub` and `apSumOffset_sub_eq_apSumOffset_tail` live in
-- `MoltResearch.Discrepancy.Basic` (kept in the “basic substrate” layer).

/-!
## Difference → tail: common rewrite shape

Downstream proofs often produce the difference
`apSumOffset f d m (n₁+n₂) - apSumOffset f d m n₁`.

The basic substrate lemma is `apSumOffset_sub_eq_apSumOffset_tail`; here we provide a
“shape-forward” alias plus a couple of tiny regression examples.
-/

/-- Stable alias for the common “subtract an initial block from a longer block” pattern.

This is the offset-sum analogue of `apSumFrom_sub_eq_apSumFrom_tail`-style lemmas.
-/
lemma apSumOffset_sub_apSumOffset_eq_apSumOffset_add_len (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ = apSumOffset f d (m + n₁) n₂ := by
  simpa using
    (apSumOffset_sub_eq_apSumOffset_tail (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))

-- regression: the rewrite should stay simp-friendly.
example (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ = apSumOffset f d (m + n₁) n₂ := by
  simpa using apSumOffset_sub_apSumOffset_eq_apSumOffset_add_len (f := f) (d := d) (m := m)
    (n₁ := n₁) (n₂ := n₂)

example (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    apSumOffset f d (m + n₁) n₂ = apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ := by
  simpa [eq_comm] using
    (apSumOffset_sub_apSumOffset_eq_apSumOffset_add_len (f := f) (d := d) (m := m) (n₁ := n₁)
      (n₂ := n₂))

/-- Normal form: rewrite the normal-form difference `apSumOffset f d m (n₁+n₂) - apSumOffset f d m n₁`
as an offset sum with `m = 0` on a shifted sequence.

Concretely:
`apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ = apSumOffset (fun k => f (k + (m + n₁) * d)) d 0 n₂`.

This is `apSumOffset_sub_eq_apSumOffset_tail` followed by `apSumOffset_eq_apSumOffset_shift_add`.
-/
lemma apSumOffset_sub_eq_apSumOffset_shift_add (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ =
      apSumOffset (fun k => f (k + (m + n₁) * d)) d 0 n₂ := by
  calc
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ = apSumOffset f d (m + n₁) n₂ := by
      simpa using
        apSumOffset_sub_eq_apSumOffset_tail (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)
    _ = apSumOffset (fun k => f (k + (m + n₁) * d)) d 0 n₂ := by
      simpa using apSumOffset_eq_apSumOffset_shift_add (f := f) (d := d) (m := m + n₁) (n := n₂)

/-- Mul-left variant of `apSumOffset_sub_eq_apSumOffset_shift_add` with the translation constant
written as `d * (m + n₁)`.

This wrapper avoids a commutativity rewrite under binders when a downstream development already
prefers the `d * i` convention for arithmetic progression points.
-/
lemma apSumOffset_sub_eq_apSumOffset_shift_add_mul_left (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ =
      apSumOffset (fun k => f (k + d * (m + n₁))) d 0 n₂ := by
  simpa [Nat.mul_comm] using
    (apSumOffset_sub_eq_apSumOffset_shift_add (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))

/-- Normal form: rewrite the difference of two offset sums (in the canonical `n₁ + n₂` form)
into a homogeneous AP sum on a shifted sequence.

Concretely:
`apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ = apSum (fun k => f (k + (m + n₁) * d)) d n₂`.

This is `apSumOffset_sub_eq_apSumOffset_tail` followed by `apSumOffset_eq_apSum_shift_add`.
-/
lemma apSumOffset_sub_eq_apSum_shift_add (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ =
      apSum (fun k => f (k + (m + n₁) * d)) d n₂ := by
  calc
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ = apSumOffset f d (m + n₁) n₂ := by
      simpa using
        apSumOffset_sub_eq_apSumOffset_tail (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)
    _ = apSum (fun k => f (k + (m + n₁) * d)) d n₂ := by
      simpa using apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m + n₁) (n := n₂)

/-- Mul-left variant of `apSumOffset_sub_eq_apSum_shift_add` with the translation constant written as
`d * (m + n₁)`.

This wrapper avoids a commutativity rewrite under binders when a downstream development already
prefers the `d * i` convention for arithmetic progression points.
-/
lemma apSumOffset_sub_eq_apSum_shift_add_mul_left (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ =
      apSum (fun k => f (k + d * (m + n₁))) d n₂ := by
  simpa [Nat.mul_comm] using
    (apSumOffset_sub_eq_apSum_shift_add (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))

/-- Normal form: when `n₁ ≤ n₂`, rewrite the difference of two offset sums over the same start `m`
into a homogeneous AP sum on a shifted sequence.

Concretely:
`apSumOffset f d m n₂ - apSumOffset f d m n₁ = apSum (fun k => f (k + (m + n₁) * d)) d (n₂ - n₁)`.

This is `apSumOffset_sub_eq_apSum_shift_add` applied after rewriting `n₂` as `n₁ + (n₂ - n₁)`.
-/
lemma apSumOffset_sub_apSumOffset_eq_apSum_shift_add (f : ℕ → ℤ) (d m : ℕ) {n₁ n₂ : ℕ}
    (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ =
      apSum (fun k => f (k + (m + n₁) * d)) d (n₂ - n₁) := by
  have h :=
    apSumOffset_sub_eq_apSum_shift_add (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂ - n₁)
  simpa [Nat.add_sub_of_le hn] using h

/-- Mul-left variant of `apSumOffset_sub_apSumOffset_eq_apSum_shift_add` with the translation constant
written as `d * (m + n₁)`.

This wrapper avoids a commutativity rewrite under binders when a downstream development already
prefers the `d * i` convention for arithmetic progression points.
-/
lemma apSumOffset_sub_apSumOffset_eq_apSum_shift_add_mul_left (f : ℕ → ℤ) (d m : ℕ) {n₁ n₂ : ℕ}
    (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ =
      apSum (fun k => f (k + d * (m + n₁))) d (n₂ - n₁) := by
  simpa [Nat.mul_comm] using
    (apSumOffset_sub_apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n₁ := n₁)
      (n₂ := n₂) (hn := hn))

/-- Rewrite the normal-form difference `apSumOffset f d m (n₁+n₂) - apSumOffset f d m n₁`
as the “paper notation” interval sum `∑ i ∈ Icc (m+n₁+1) (m+n₁+n₂), f (i*d)`.

This is intended for surface statements: keep the nucleus API in terms of `apSumOffset` and use
this lemma only when matching paper notation.
-/
lemma apSumOffset_sub_eq_sum_Icc (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ =
      (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) := by
  -- First rewrite the subtraction to a tail sum, then rewrite that tail to an interval sum.
  calc
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁
        = apSumOffset f d (m + n₁) n₂ := by
            simpa using
              (apSumOffset_sub_eq_apSumOffset_tail (f := f) (d := d) (m := m) (n₁ := n₁)
                (n₂ := n₂))
    _ = (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) := by
            simpa [Nat.add_assoc] using
              (apSumOffset_eq_sum_Icc (f := f) (d := d) (m := m + n₁) (n := n₂))

/-- Translation-friendly variant of `apSumOffset_sub_eq_sum_Icc` using `d * i` (step size on the left).

This avoids commuting multiplication under binders when your surrounding development already uses
`d * i` summand shapes.
-/
lemma apSumOffset_sub_eq_sum_Icc_mul_left (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ =
      (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (d * i)) := by
  classical
  refine (apSumOffset_sub_eq_sum_Icc (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)).trans ?_
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Nat.mul_comm]

/-- Difference of two offset sums over the same start `m` as a tail sum when `n₁ ≤ n₂`. -/
lemma apSumOffset_sub_apSumOffset_eq_apSumOffset (f : ℕ → ℤ) (d m : ℕ) {n₁ n₂ : ℕ}
    (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ = apSumOffset f d (m + n₁) (n₂ - n₁) := by
  have h :=
    apSumOffset_sub_eq_apSumOffset_tail (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂ - n₁)
  simpa [Nat.add_sub_of_le hn] using h

/-- Normal form: when `n₁ ≤ n₂`, rewrite the difference of two offset sums over the same start `m`
as an offset sum with `m = 0` on a shifted sequence.

Concretely:
`apSumOffset f d m n₂ - apSumOffset f d m n₁ = apSumOffset (fun k => f (k + (m + n₁) * d)) d 0 (n₂ - n₁)`.

This is `apSumOffset_sub_eq_apSumOffset_shift_add` applied after rewriting `n₂` as `n₁ + (n₂ - n₁)`.
-/
lemma apSumOffset_sub_apSumOffset_eq_apSumOffset_shift_add (f : ℕ → ℤ) (d m : ℕ) {n₁ n₂ : ℕ}
    (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ =
      apSumOffset (fun k => f (k + (m + n₁) * d)) d 0 (n₂ - n₁) := by
  have h :=
    apSumOffset_sub_eq_apSumOffset_shift_add (f := f) (d := d) (m := m) (n₁ := n₁)
      (n₂ := n₂ - n₁)
  simpa [Nat.add_sub_of_le hn] using h

/-- Mul-left variant of `apSumOffset_sub_apSumOffset_eq_apSumOffset_shift_add` with the translation
constant written as `d * (m + n₁)`.

This wrapper avoids a commutativity rewrite under binders when a downstream development already
prefers the `d * i` convention for arithmetic progression points.
-/
lemma apSumOffset_sub_apSumOffset_eq_apSumOffset_shift_add_mul_left (f : ℕ → ℤ) (d m : ℕ)
    {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ =
      apSumOffset (fun k => f (k + d * (m + n₁))) d 0 (n₂ - n₁) := by
  simpa [Nat.mul_comm] using
    (apSumOffset_sub_apSumOffset_eq_apSumOffset_shift_add (f := f) (d := d) (m := m) (n₁ := n₁)
      (n₂ := n₂) (hn := hn))

/-- When `n₁ ≤ n₂`, rewrite the difference of two offset sums as the “paper notation” interval sum
`∑ i ∈ Icc (m+n₁+1) (m+n₂), f (i*d)`.

This is the “paper notation” counterpart of `apSumOffset_sub_apSumOffset_eq_apSumOffset`.
-/
lemma apSumOffset_sub_apSumOffset_eq_sum_Icc (f : ℕ → ℤ) (d m : ℕ) {n₁ n₂ : ℕ}
    (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ =
      (Finset.Icc (m + n₁ + 1) (m + n₂)).sum (fun i => f (i * d)) := by
  have hEq :=
    apSumOffset_sub_apSumOffset_eq_apSumOffset (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)
      (hn := hn)
  -- Rewrite the tail to an interval sum and simplify `m + n₁ + (n₂ - n₁) = m + n₂`.
  simpa [apSumOffset_eq_sum_Icc, Nat.add_sub_of_le hn, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    -sum_Icc_eq_apSumOffset_of_le_add_len] using hEq

/-- Translation-friendly variant of `apSumOffset_sub_apSumOffset_eq_sum_Icc` using `d * i` (step size
on the left).

This avoids commuting multiplication under binders when your surrounding development already uses
`d * i` summand shapes.
-/
lemma apSumOffset_sub_apSumOffset_eq_sum_Icc_mul_left (f : ℕ → ℤ) (d m : ℕ) {n₁ n₂ : ℕ}
    (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ =
      (Finset.Icc (m + n₁ + 1) (m + n₂)).sum (fun i => f (d * i)) := by
  classical
  refine
    (apSumOffset_sub_apSumOffset_eq_sum_Icc (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)
        (hn := hn)).trans ?_
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Nat.mul_comm]

/-!
## Discrepancy-level split inequality for offset sums

The wrapper `discOffset f d m n := Int.natAbs (apSumOffset f d m n)` is defined in
`MoltResearch.Discrepancy.Basic`. Here we add the common “split at an interior cut” inequality.
-/

/-- Triangle inequality for splitting an offset sum at an interior cut `k` (with `m ≤ k ≤ m+n`). -/
lemma discOffset_split_at_le (f : ℕ → ℤ) (d : ℕ) {m k n : ℕ}
    (hmk : m ≤ k) (hkn : k ≤ m + n) :
    discOffset f d m n ≤ discOffset f d m (k - m) + discOffset f d k (m + n - k) := by
  -- Expand the wrapper so the proof is a direct `Int.natAbs` statement.
  unfold discOffset
  have h := apSumOffset_split_at (f := f) (d := d) (m := m) (k := k) (n := n) hmk hkn
  -- `|x+y| ≤ |x|+|y|`.
  simpa [h] using
    (Int.natAbs_add_le (apSumOffset f d m (k - m)) (apSumOffset f d k (m + n - k)))

/-- Triangle inequality for splitting a homogeneous sum at a cut `k` (with `k ≤ n`).

This is the homogeneous analogue of `discOffset_split_at_le`.
-/
lemma disc_split_at_le (f : ℕ → ℤ) (d : ℕ) {k n : ℕ} (hkn : k ≤ n) :
    disc f d n ≤ disc f d k + discOffset f d k (n - k) := by
  have h :=
    discOffset_split_at_le (f := f) (d := d) (m := 0) (k := k) (n := n)
      (hmk := Nat.zero_le _) (hkn := by simpa using hkn)
  -- Normalize away `m = 0` and the degenerate subtraction terms.
  simpa using h

/-- Sign-sequence bound on the difference of two offset sums when `n₁ ≤ n₂`. -/
lemma IsSignSequence.natAbs_apSumOffset_sub_apSumOffset_le {f : ℕ → ℤ} (hf : IsSignSequence f)
    (d m : ℕ) {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) :
    Int.natAbs (apSumOffset f d m n₂ - apSumOffset f d m n₁) ≤ n₂ - n₁ := by
  have hEq :=
    apSumOffset_sub_apSumOffset_eq_apSumOffset (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)
      (hn := hn)
  have hf' : IsSignSequence (fun k => f ((m + n₁) * d + k)) := by
    intro k
    exact hf (((m + n₁) * d) + k)
  have hle :
      Int.natAbs (apSum (fun k => f ((m + n₁) * d + k)) d (n₂ - n₁)) ≤ n₂ - n₁ :=
    IsSignSequence.natAbs_apSum_le (hf := hf') (d := d) (n := n₂ - n₁)
  have hShift := apSumOffset_eq_apSum_shift (f := f) (d := d) (m := m + n₁) (n := n₂ - n₁)
  have htail : Int.natAbs (apSumOffset f d (m + n₁) (n₂ - n₁)) ≤ n₂ - n₁ := by
    simpa [hShift] using hle
  simpa [hEq] using htail

/-!
### `discOffset` invariances (sign and affine shifts)

Checklist item: Problems/erdos_discrepancy.md (Track B) — DiscOffset-level sign/shift invariances.

These are thin `discOffset`-level wrappers around existing `apSumOffset` algebra/shift lemmas.

Note: the sign-flip invariances (`apSumOffset_neg`, `discOffset_neg`) live in
`MoltResearch.Discrepancy.Basic` so they are available from the stable surface without importing
this file.
-/

/-- Shifting the underlying sequence by an affine `a*d` translation corresponds to shifting the
start index from `m` to `m + a`.

This is the `discOffset`-level wrapper of `apSumOffset_shift_start_add`.
-/
lemma discOffset_shift_add_mul (f : ℕ → ℤ) (a d m n : ℕ) :
    discOffset (fun k => f (k + a * d)) d m n = discOffset f d (m + a) n := by
  unfold discOffset
  -- Use the already-normalized `apSumOffset` lemma and rewrite under `Int.natAbs`.
  have h : apSumOffset (fun k => f (k + a * d)) d m n = apSumOffset f d (m + a) n := by
    -- `apSumOffset_shift_start_add` is oriented the other way.
    simpa [Nat.mul_comm] using
      (apSumOffset_shift_start_add (f := f) (d := d) (m := m) (k := a) (n := n)).symm
  simpa [h]

/-!
### DiscOffset shift-start coherence

Checklist item: Problems/erdos_discrepancy.md (Track B) — DiscOffset shift-start coherence.

These are stable-surface `discOffset` wrappers around `apSumOffset_shift_start_add*`.
-/

/-- Shift-start coherence for `discOffset`: absorb a start-index shift `m ↦ m + k` into a
translation of the summand.

This is the `discOffset`-level wrapper of `apSumOffset_shift_start_add`.
-/
lemma discOffset_shift_start_add (f : ℕ → ℤ) (d m k n : ℕ) :
    discOffset f d (m + k) n = discOffset (fun t => f (t + k * d)) d m n := by
  -- `discOffset` is a wrapper around `Int.natAbs (apSumOffset …)`.
  unfold discOffset
  simp [apSumOffset_shift_start_add]

/-- `mul_left`-friendly variant of `discOffset_shift_start_add`.

This avoids commuting multiplication in downstream developments that prefer the `d * k` convention.
-/
lemma discOffset_shift_start_add_mul_left (f : ℕ → ℤ) (d m k n : ℕ) :
    discOffset f d (m + k) n = discOffset (fun t => f (t + d * k)) d m n := by
  simpa [Nat.mul_comm] using
    (discOffset_shift_start_add (f := f) (d := d) (m := m) (k := k) (n := n))

/-!
### Boundedness transport lemmas (`BoundedDiscOffset`) for shift-start coherence

These lemmas let downstream code rewrite boundedness hypotheses under the `shift_start` normal form
without unfolding `BoundedDiscOffset`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Bounded transport API.
-/

/-- Transport boundedness along `discOffset_shift_start_add`. -/
theorem BoundedDiscOffset.map_shift_start_add {f : ℕ → ℤ} {d m k B : ℕ}
    (h : BoundedDiscOffset f d (m + k) B) :
    BoundedDiscOffset (fun t => f (t + k * d)) d m B := by
  intro n
  rw [← discOffset_shift_start_add (f := f) (d := d) (m := m) (k := k) (n := n)]
  exact h n

/-- Inverse transport for `BoundedDiscOffset.map_shift_start_add`. -/
theorem BoundedDiscOffset.of_map_shift_start_add {f : ℕ → ℤ} {d m k B : ℕ}
    (h : BoundedDiscOffset (fun t => f (t + k * d)) d m B) :
    BoundedDiscOffset f d (m + k) B := by
  intro n
  rw [discOffset_shift_start_add (f := f) (d := d) (m := m) (k := k) (n := n)]
  exact h n

/-- Offset AP sum of a pointwise subtraction of functions. -/
lemma apSumOffset_sub (f g : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset (fun k => f k - g k) d m n = apSumOffset f d m n - apSumOffset g d m n := by
  classical
  unfold apSumOffset
  simp [Finset.sum_sub_distrib]

/-- Multiplication by a constant on the left commutes with `apSumOffset`. -/
@[simp] lemma apSumOffset_mul_left (c : ℤ) (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset (fun k => c * f k) d m n = c * apSumOffset f d m n := by
  classical
  unfold apSumOffset
  simp [Finset.mul_sum]

/-- Multiplication by a constant on the right commutes with `apSumOffset`. -/
@[simp] lemma apSumOffset_mul_right (f : ℕ → ℤ) (c : ℤ) (d m n : ℕ) :
    apSumOffset (fun k => f k * c) d m n = apSumOffset f d m n * c := by
  classical
  unfold apSumOffset
  simp [Finset.sum_mul]

lemma IsSignSequence.natAbs_apSumOffset_le {f : ℕ → ℤ} (hf : IsSignSequence f) (d m n : ℕ) :
    Int.natAbs (apSumOffset f d m n) ≤ n := by
  have hf' : IsSignSequence (fun k => f (m * d + k)) := by
    intro k
    exact hf (m * d + k)
  have h_eq := apSumOffset_eq_apSum_shift (f := f) (d := d) (m := m) (n := n)
  have h_le := (IsSignSequence.natAbs_apSum_le (hf := hf') (d := d) (n := n))
  simpa [h_eq] using h_le

/-- Order-free sign-sequence bound on the difference of two offset sums.

This is a convenient triangle-inequality estimate when you do not want to case-split on `n ≤ n'`.
A tighter bound under `n ≤ n'` is `IsSignSequence.natAbs_apSumOffset_sub_apSumOffset_le`.
-/
lemma IsSignSequence.natAbs_apSumOffset_sub_apSumOffset_le_add {f : ℕ → ℤ} (hf : IsSignSequence f)
    (d m n n' : ℕ) :
    Int.natAbs (apSumOffset f d m n - apSumOffset f d m n') ≤ n + n' := by
  have htri :
      Int.natAbs (apSumOffset f d m n - apSumOffset f d m n') ≤
        Int.natAbs (apSumOffset f d m n) + Int.natAbs (apSumOffset f d m n') := by
    -- `x - y = x + (-y)` and apply triangle inequality.
    simpa [sub_eq_add_neg, Int.natAbs_neg, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Int.natAbs_add_le (apSumOffset f d m n) (- apSumOffset f d m n'))
  exact
    le_trans htri
      (Nat.add_le_add (hf.natAbs_apSumOffset_le (d := d) (m := m) (n := n))
        (hf.natAbs_apSumOffset_le (d := d) (m := m) (n := n')))

lemma IsSignSequence.natAbs_apSum_sub_le {f : ℕ → ℤ} (hf : IsSignSequence f) (d m n : ℕ) :
    Int.natAbs (apSum f d (m + n) - apSum f d m) ≤ n := by
  have h := hf.natAbs_apSumOffset_le (d := d) (m := m) (n := n)
  simpa [apSumOffset_eq_sub (f := f) (d := d) (m := m) (n := n)] using h

lemma IsSignSequence.natAbs_apSum_sub_apSum_le {f : ℕ → ℤ} (hf : IsSignSequence f) (d : ℕ) {m n : ℕ}
    (hmn : m ≤ n) :
    Int.natAbs (apSum f d n - apSum f d m) ≤ n - m := by
  have h := hf.natAbs_apSumOffset_le (d := d) (m := m) (n := n - m)
  simpa [apSum_sub_apSum_eq_apSumOffset (f := f) (d := d) (hmn := hmn)] using h

end MoltResearch
