import MoltResearch.Discrepancy

/-!
# Discrepancy: stable-surface “support + edit” pipeline example

Compile-only regression test wired into `MoltResearch.Discrepancy.SurfaceAudit`.

Checklist item (Track B): Problems/erdos_discrepancy.md
- "Stable-surface support + edit pipeline example"

This is the common downstream workflow:
1. Work on the finite accessed-index finset `apSupport d m n`.
2. Prove `f` and `g` differ on at most `t` points of this support.
3. Conclude a `discOffset` bound via the edit-sensitivity wrapper.
-/

namespace MoltResearch

section
  variable (f g : ℕ → ℤ) (d m n t : ℕ)

  example (hd : 0 < d) (hf : IsSignSequence f) (hg : IsSignSequence g)
      (ht : ((apSupport d m n).filter (fun x => f x ≠ g x)).card ≤ t) :
      discOffset f d m n ≤ discOffset g d m n + 2 * t := by
    simpa using
      (IsSignSequence.discOffset_edit_le_of_card_apSupport_diff_le
        (hf := hf) (hg := hg) (d := d) (m := m) (n := n) (t := t) hd ht)
end

end MoltResearch
