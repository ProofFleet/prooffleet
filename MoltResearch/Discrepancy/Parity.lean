import MoltResearch.Discrepancy.Affine

/-!
# Discrepancy: parity lemmas

For a ±1-valued sequence, every term is congruent to `1` modulo `2`,
so the various AP-sum notions reduce to the length when viewed in `ZMod 2`.
-/

namespace MoltResearch

lemma IsSignSequence.apSum_zmod2 {f : ℕ → ℤ} (hf : IsSignSequence f) (d n : ℕ) :
    (apSum f d n : ZMod 2) = n := by
  induction n with
  | zero =>
      simp [apSum]
  | succ n ih =>
      have hterm : ((f ((n + 1) * d)) : ZMod 2) = (1 : ZMod 2) := by
        rcases hf ((n + 1) * d) with h | h <;> simp [h]
      have hs :
          (apSum f d (n + 1) : ZMod 2) =
            (apSum f d n : ZMod 2) + (f ((n + 1) * d) : ZMod 2) := by
        simpa using
          congrArg (fun z : ℤ => (z : ZMod 2))
            (apSum_succ (f := f) (d := d) (n := n))
      simpa [ih, hterm] using hs

lemma IsSignSequence.apSumOffset_zmod2 {f : ℕ → ℤ} (hf : IsSignSequence f) (d m n : ℕ) :
    (apSumOffset f d m n : ZMod 2) = n := by
  induction n with
  | zero =>
      simp [apSumOffset]
  | succ n ih =>
      have hterm : ((f ((m + n + 1) * d)) : ZMod 2) = (1 : ZMod 2) := by
        rcases hf ((m + n + 1) * d) with h | h <;> simp [h]
      have hs :
          (apSumOffset f d m (n + 1) : ZMod 2) =
            (apSumOffset f d m n : ZMod 2) + (f ((m + n + 1) * d) : ZMod 2) := by
        simpa using
          congrArg (fun z : ℤ => (z : ZMod 2))
            (apSumOffset_succ (f := f) (d := d) (m := m) (n := n))
      simpa [ih, hterm] using hs

lemma IsSignSequence.apSumFrom_zmod2 {f : ℕ → ℤ} (hf : IsSignSequence f) (a d n : ℕ) :
    (apSumFrom f a d n : ZMod 2) = n := by
  induction n with
  | zero =>
      simp [apSumFrom]
  | succ n ih =>
      have hterm : ((f (a + (n + 1) * d)) : ZMod 2) = (1 : ZMod 2) := by
        rcases hf (a + (n + 1) * d) with h | h <;> simp [h]
      have hs :
          (apSumFrom f a d (n + 1) : ZMod 2) =
            (apSumFrom f a d n : ZMod 2) + (f (a + (n + 1) * d) : ZMod 2) := by
        simpa using
          congrArg (fun z : ℤ => (z : ZMod 2))
            (apSumFrom_succ (f := f) (a := a) (d := d) (n := n))
      simpa [ih, hterm] using hs

end MoltResearch
