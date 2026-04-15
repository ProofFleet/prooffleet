import MoltResearch.Discrepancy

/-!
# Discrepancy: end-to-end normal-form pipeline (compile-only)

This file is intentionally **example-only**: it provides a tiny “paper-shaped” script that exercises
several parts of the stable discrepancy surface in the order they typically appear in Track B.

Pipeline (typical):

1. **Paper sum** (`Finset.Icc`)
2. **Nucleus normal form** (`discOffset` wrapper)
3. **Local edit sensitivity** (change at ≤1 sampled index)
4. **Triangle / split bound** (`discOffset_split_at_le`)

This is wired into `MoltResearch.Discrepancy.SurfaceAudit` so it cannot silently regress.
-/

namespace MoltResearch

section
  open scoped BigOperators

  /-!
  ## Micro-pipeline starter scripts (compile-only)

  These are intentionally tiny examples that exercise the *most common* rewrite path in Track B:

  paper notation → nucleus (`apSumFrom` / `apSumOffset`) → discrepancy wrapper (`discOffset`).

  They must continue to compile under:

  ```lean
  import MoltResearch.Discrepancy
  ```
  -/

  section MicroPipeline

  variable (f : ℕ → ℤ) (a d m n : ℕ)

  -- (1) Paper affine partial sum (`Icc 1 n`) → nucleus `apSumFrom`.
  example : (Finset.Icc 1 n).sum (fun i => f (a + i * d)) = apSumFrom f a d n := by
    simpa [sum_Icc_eq_apSumFrom]

  -- (2) Nucleus difference form → tail normal form `apSumOffset` (on a shifted sequence).
  example : apSumFrom f a d (m + n) - apSumFrom f a d m =
      apSumOffset (fun k => f (k + a)) d m n := by
    simpa using
      (apSumFrom_sub_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n))

  -- (3) Tail normal form → discrepancy wrapper (`discOffset`).
  -- Avoid `simp` here: the global simp set contains both directions of the `discOffset` wrapper,
  -- and unfolding can trigger a simp loop.
  example : Int.natAbs (apSumOffset f d m n) = discOffset f d m n := by
    rfl

  end MicroPipeline

  /-!
  A compact “support + edit” pipeline example.

  Typical Track B pattern:

  1. Use **support congruence** to ignore changes outside `apSupport d m n`.
  2. Use **edit sensitivity** to compare two sign sequences that differ on ≤1 sampled index.

  Compile-only; the goal is to keep the stable surface usable under:

  ```lean
  import MoltResearch.Discrepancy
  ```
  -/
  example :
      let f : ℕ → ℤ := fun _ => 1
      let g : ℕ → ℤ := fun n => if n = 4 then (-1) else 1
      let h : ℕ → ℤ := fun n => if n = 100 then (-1) else g n
      -- (1) Changes outside the support do not affect `discOffset`.
      discOffset h 1 0 6 = discOffset g 1 0 6 ∧
      -- (2) If `f` and `h` differ on ≤1 sampled index in `range 6`, pay a +2 edit cost.
      discOffset f 1 0 6 ≤ discOffset h 1 0 6 + 2 := by
    intro f g h
    constructor
    · -- Support congruence: `h = g` on the relevant finite support.
      refine (discOffset_congr_support (f := h) (g := g) (d := 1) (m := 0) (n := 6) ?_).symm
      intro x hx
      -- Any `x ∈ apSupport 1 0 6` satisfies `x ≤ 6`, so in particular `x ≠ 100`.
      have hx' : ∃ i, 0 < i ∧ i ≤ 0 + 6 ∧ x = i * 1 := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (mem_apSupport_iff_exists_endpoints (d := 1) (m := 0) (n := 6) (x := x)).1 hx
      rcases hx' with ⟨i, hi0, hi6, rfl⟩
      have hi6' : i ≤ 6 := by simpa using hi6
      have hi100 : i ≠ 100 := by
        -- `i ≤ 6 < 100`.
        exact ne_of_lt (lt_of_le_of_lt hi6' (by decide))
      -- Now `h` reduces to `g` on this support point.
      simp [h, g, hi100]
    · -- Edit sensitivity bound.
      have hf : IsSignSequence f := by
        intro n; simp [f]
      have hh : IsSignSequence h := by
        intro n
        by_cases hn : n = 100
        · simp [h, hn]
        · by_cases h4 : n = 4 <;> simp [h, hn, g, h4]
      have hcard :
          ((Finset.range 6).filter (fun i => f ((0 + i + 1) * 1) ≠ h ((0 + i + 1) * 1))).card ≤ 1 := by
        -- On sampled indices `1..6`, `h` agrees with `g`, so only the `i=3` (`n=4`) sample differs.
        decide
      simpa using
        (IsSignSequence.discOffset_edit_le
          (hf := hf) (hg := hh) (d := 1) (m := 0) (n := 6) (t := 1) hcard)

  /-!
  A compact “edit + split + bound” example.

  We compare two sign sequences `f` and `g` that differ at exactly one sampled index, and we bound
  the discrepancy of `g` by splitting the interval, then transport the bound to `f` via edit
  sensitivity.

  The goal is not a tight inequality; the goal is to keep the rewrite pipeline stable and
  one-screen.
  -/
  example :
      let f : ℕ → ℤ := fun _ => 1
      let g : ℕ → ℤ := fun n => if n = 4 then (-1) else 1
      -- Paper `Icc` tail-sum form rewritten into the nucleus normal form `apSumOffset`:
      (Finset.Icc (0 + 1) (0 + 6)).sum (fun i => g (i * 1)) = apSumOffset g 1 0 6 ∧
      -- End-to-end inequality: split `g`, then pay a +2 edit cost to replace `g` by `f`.
      discOffset f 1 0 6 ≤ discOffset g 1 0 3 + discOffset g 1 3 3 + 2 := by
    intro f g
    constructor
    · -- (1) Paper sum → nucleus normal form.
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (apSumOffset_eq_sum_Icc (f := g) (d := 1) (m := 0) (n := 6)).symm
    · -- (2) Local edit sensitivity: `f` and `g` differ on at most one sampled index in `range 6`.
      have hf : IsSignSequence f := by
        intro n; simp [f]
      have hg : IsSignSequence g := by
        intro n
        by_cases h : n = 4 <;> simp [g, h]
      have hcard :
          ((Finset.range 6).filter (fun i => f ((0 + i + 1) * 1) ≠ g ((0 + i + 1) * 1))).card ≤ 1 := by
        -- Only `i=3` (sampled index `4`) differs.
        decide

      have h_edit : discOffset f 1 0 6 ≤ discOffset g 1 0 6 + 2 := by
        -- Apply the standard offset edit bound with `t = 1`.
        simpa using
          (IsSignSequence.discOffset_edit_le
            (hf := hf) (hg := hg) (d := 1) (m := 0) (n := 6) (t := 1) hcard)

      -- (3) Triangle/split bound on `g` at cut `k = 3`.
      have h_split : discOffset g 1 0 6 ≤ discOffset g 1 0 3 + discOffset g 1 3 3 := by
        -- `discOffset_split_at_le` expects an interior cut `m ≤ k ≤ m+n`.
        have h :=
          discOffset_split_at_le (f := g) (d := 1) (m := 0) (k := 3) (n := 6)
            (hmk := by decide) (hkn := by decide)
        -- Normalize the subtraction terms: `k - m = 3`, `m + n - k = 3`.
        simpa using h

      -- Combine: `discOffset f ≤ discOffset g + 2 ≤ (split g) + 2`.
      calc
        discOffset f 1 0 6 ≤ discOffset g 1 0 6 + 2 := h_edit
        _ ≤ (discOffset g 1 0 3 + discOffset g 1 3 3) + 2 := by
              exact Nat.add_le_add_right h_split 2
        _ = discOffset g 1 0 3 + discOffset g 1 3 3 + 2 := by
              ac_rfl

  /-!
  ## `discOffsetUpTo` cut/concatenation inequality (compile-only)

  A very common Track B move is: bound a long segment by cutting it into an initial prefix of
  length `N` and a tail segment of length `K`.

  This exercises the `discOffsetUpTo` “max up to length” wrapper *and* the cut/concatenation lemma,
  under the stable surface:

  ```lean
  import MoltResearch.Discrepancy
  ```
  -/

  section UpToCut

  variable (f : ℕ → ℤ) (d m N K : ℕ)

  -- Cut/concatenation inequality (stable surface):
  --   max up to `N+K` ≤ (max up to `N`) + (max on tail length `K`).
  example :
      discOffsetUpTo f d m (N + K) ≤ discOffsetUpTo f d m N + discOffsetUpTo f d (m + N) K := by
    simpa using (discOffsetUpTo_add_le_add_discOffsetUpTo (f := f) (d := d) (m := m) (N := N) (K := K))

  -- A clean inequality for a *particular* tail length, chained through `discOffset ≤ discOffsetUpTo`.
  example :
      discOffset f d m (N + K) ≤ discOffsetUpTo f d m N + discOffsetUpTo f d (m + N) K := by
    have h1 : discOffset f d m (N + K) ≤ discOffsetUpTo f d m (N + K) := by
      simpa using (discOffset_le_discOffsetUpTo_self (f := f) (d := d) (m := m) (n := N + K))
    have h2 :
        discOffsetUpTo f d m (N + K) ≤ discOffsetUpTo f d m N + discOffsetUpTo f d (m + N) K := by
      simpa using (discOffsetUpTo_add_le_add_discOffsetUpTo (f := f) (d := d) (m := m) (N := N) (K := K))
    exact le_trans h1 h2

  end UpToCut

end

end MoltResearch
