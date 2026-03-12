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
      -- `simp` (via `add_mul_succ_norm`) prefers the endpoint normal form `a + (n+1) * d`.
      have hterm : ((f (a + (n + 1) * d)) : ZMod 2) = (1 : ZMod 2) := by
        rcases hf (a + (n + 1) * d) with h | h <;> simp [h]
      have hs :
          (apSumFrom f a d (n + 1) : ZMod 2) =
            (apSumFrom f a d n : ZMod 2) + (f (a + (n + 1) * d) : ZMod 2) := by
        simpa using
          congrArg (fun z : ℤ => (z : ZMod 2))
            (apSumFrom_succ (f := f) (a := a) (d := d) (n := n))
      simpa [ih, hterm] using hs

/-!
## Parity split (length-2 normal form)

Split a homogeneous AP sum of even length into its even-index and odd-index sub-sums.

Even-index terms form a homogeneous AP sum with doubled step size.
Odd-index terms are `f d` plus an affine tail sum.
-/

/-- Parity split for homogeneous AP sums of even length.

`apSum f d (2*(n+1))` splits into:
- the even-index terms: `apSum f (2*d) (n+1)`;
- the odd-index terms: `f d + apSumFrom f d (2*d) n`.

Purely algebraic (no `IsSignSequence` assumptions).
-/
lemma apSum_two_mul_len_succ (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d (2 * (n + 1)) = apSum f (2 * d) (n + 1) + f d + apSumFrom f d (2 * d) n := by
  induction n with
  | zero =>
      -- `2*(0+1)=2`.
      -- After simplification, this is just commutativity in `ℤ`.
      simp [apSum_two, apSum_one, apSumFrom, add_assoc, add_left_comm, add_comm]
  | succ n ih =>
      -- Expand the LHS by adding the next two terms.
      have hL :
          apSum f d (2 * (n + 2)) =
            apSum f d (2 * (n + 1)) + f ((2 * (n + 1) + 1) * d) + f ((2 * (n + 1) + 2) * d) := by
        calc
          apSum f d (2 * (n + 2))
              = apSum f d (2 * (n + 1) + 2) := by
                  have : 2 * (n + 2) = 2 * (n + 1) + 2 := by ring
                  simpa [this]
          _ = apSum f d (2 * (n + 1) + 1) + f ((2 * (n + 1) + 2) * d) := by
                  simpa [Nat.add_assoc] using
                    (apSum_succ (f := f) (d := d) (n := 2 * (n + 1) + 1))
          _ = (apSum f d (2 * (n + 1)) + f ((2 * (n + 1) + 1) * d)) + f ((2 * (n + 1) + 2) * d) := by
                  simpa [Nat.add_assoc, add_assoc] using
                    congrArg (fun z => z + f ((2 * (n + 1) + 2) * d))
                      (apSum_succ (f := f) (d := d) (n := 2 * (n + 1)))
          _ = apSum f d (2 * (n + 1)) + f ((2 * (n + 1) + 1) * d) + f ((2 * (n + 1) + 2) * d) := by
                  abel

      -- Expand the even part on the RHS.
      have hE :
          apSum f (2 * d) (n + 2) = apSum f (2 * d) (n + 1) + f ((n + 2) * (2 * d)) := by
        simpa [Nat.add_assoc] using (apSum_succ (f := f) (d := 2 * d) (n := n + 1))

      -- Expand the odd tail on the RHS.
      have hO :
          apSumFrom f d (2 * d) (n + 1) = apSumFrom f d (2 * d) n + f (d + (n + 1) * (2 * d)) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (apSumFrom_succ (f := f) (a := d) (d := 2 * d) (n := n))

      -- Match the two new terms with the expansions above.
      have hodd_term : (2 * (n + 1) + 1) * d = d + (n + 1) * (2 * d) := by
        ring

      have heven_term : (2 * (n + 1) + 2) * d = (n + 2) * (2 * d) := by
        ring

      -- Combine (avoid `simp` recursion-depth blowups by rewriting + `abel`).
      calc
        apSum f d (2 * (n + 2))
            = apSum f d (2 * (n + 1)) + f ((2 * (n + 1) + 1) * d) + f ((2 * (n + 1) + 2) * d) := hL
        _ = (apSum f (2 * d) (n + 1) + f d + apSumFrom f d (2 * d) n)
              + f (d + (n + 1) * (2 * d)) + f ((n + 2) * (2 * d)) := by
              rw [ih]
              rw [hodd_term, heven_term]
        _ = apSum f (2 * d) (n + 2) + f d + apSumFrom f d (2 * d) (n + 1) := by
              rw [hE, hO]
              abel

end MoltResearch
