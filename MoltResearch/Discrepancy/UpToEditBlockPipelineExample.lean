import MoltResearch.Discrepancy

/-!
# Discrepancy: stable-surface “UpTo + edits + blocks” consumer pipeline example

Compile-only regression test wired into `MoltResearch.Discrepancy.SurfaceAudit`.

Checklist item (Track B): Problems/erdos_discrepancy.md
- "Consumer regression example (UpTo + edits + blocks)"

This is the intended downstream workflow:
1. Control a whole family of window lengths at once via `discOffsetUpTo` and the cutoff support
   `apSupportUpTo d m N`.
2. Perform “local surgery” (edit `f` into `g` on at most `t` indices of the cutoff support) via
   the edit-sensitivity wrappers.
3. Split an exact-multiple window `k * L` into `k` consecutive blocks and bound by the
   triangle inequality — all in nucleus terms.
-/

namespace MoltResearch

section
  variable (f g : ℕ → ℤ) (d m L k t N : ℕ)

  -- (1) `UpTo`-level surgery: an edit budget on the single cutoff support controls the whole
  -- `n ≤ N` family of discrepancies.
  example (hd : 0 < d) (hf : IsSignSequence f) (hg : IsSignSequence g)
      (ht : ((apSupportUpTo d m N).filter (fun x => f x ≠ g x)).card ≤ t) :
      discOffsetUpTo f d m N ≤ discOffsetUpTo g d m N + 2 * t := by
    simpa using
      (IsSignSequence.discOffsetUpTo_edit_le_of_card_apSupportUpTo_diff_le
        (hf := hf) (hg := hg) (d := d) (m := m) (N := N) (t := t) hd ht)

  -- (2) Full pipeline: edit `f` into `g` inside the cutoff support (cost `2*t`), then split the
  -- length `k*L` window of the edited sequence into `k` blocks (triangle bound).
  example (hd : 0 < d) (hf : IsSignSequence f) (hg : IsSignSequence g)
      (hN : k * L ≤ N)
      (ht : ((apSupportUpTo d m N).filter (fun x => f x ≠ g x)).card ≤ t) :
      discOffset f d m (k * L) ≤
        (∑ j ∈ Finset.range k, discOffset g d (m + j * L) L) + 2 * t := by
    -- Step 1: transport the edit budget from the cutoff support to the `k*L` window.
    have hmono : ((apSupport d m (k * L)).filter (fun x => f x ≠ g x)).card ≤ t := by
      refine le_trans (Finset.card_le_card ?_) ht
      exact Finset.filter_subset_filter _
        (apSupport_subset_apSupportUpTo (d := d) (m := m) hN)
    -- Step 2: edit sensitivity replaces `f` by `g` at cost `2*t`.
    have hedit : discOffset f d m (k * L) ≤ discOffset g d m (k * L) + 2 * t :=
      IsSignSequence.discOffset_edit_le_of_card_apSupport_diff_le
        (hf := hf) (hg := hg) (d := d) (m := m) (n := k * L) (t := t) hd hmono
    -- Step 3: block decomposition + triangle bound on the edited sequence.
    have hblock : discOffset g d m (k * L) ≤
        ∑ j ∈ Finset.range k, discOffset g d (m + j * L) L :=
      discOffset_mul_len_le_sum_range_block (f := g) (d := d) (m := m) (L := L) (k := k)
    omega
end

end MoltResearch
