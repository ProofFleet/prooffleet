import MoltResearch.Discrepancy.Affine
import MoltResearch.Discrepancy.Offset
import MoltResearch.Discrepancy.Reindex

/-!
# Discrepancy: residue-class splitting

This module generalizes the parity-split normal form (`q = 2`) to an arbitrary modulus `q > 0`.

The main lemma rewrites a homogeneous AP sum of length `q * (n+1)` into:
- a homogeneous AP sum along the `q`-dilated step; plus
- a finite sum of affine-tail AP sums (one for each nonzero residue class mod `q`).

This is a key normal form for “split by residue class” arguments.
-/

namespace MoltResearch

/-- Residue-class split for homogeneous AP sums.

For `q > 0`, rewrite the length-`q*(n+1)` homogeneous AP sum into:
- the `0 mod q` class (a homogeneous AP sum with step `q*d`), and
- the `r mod q` classes for `1 ≤ r ≤ q-1` (each as a head term plus an affine tail).

The statement is expressed using `Finset.range (q-1)` (indexing residues `r = i+1`).

Specializing to `q = 2` recovers the parity split.
-/
lemma apSum_mul_len_succ (f : ℕ → ℤ) (d q n : ℕ) (hq : q > 0) :
    apSum f d (q * (n + 1)) =
      apSum f (q * d) (n + 1) +
        (Finset.range (q - 1)).sum (fun r =>
          f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n) := by
  classical
  have h1 : 1 ≤ q := Nat.succ_le_iff.mp hq

  induction n with
  | zero =>
      -- `q*(0+1)=q`.
      -- Both sides are `apSum f d (q-1)` plus the final term `f (q*d)`.
      have hq' : q - 1 + 1 = q := Nat.sub_add_cancel h1
      -- Expand the `q*d` term out of `apSum`.
      have hL : apSum f d q = apSum f d (q - 1) + f (q * d) := by
        simpa [hq'] using (apSum_succ (f := f) (d := d) (n := q - 1))
      -- Expand the RHS at `n=0`.
      -- `apSumFrom ... 0 = 0` and `apSum f (q*d) 1 = f (q*d)`.
      have hR :
          apSum f (q * d) 1 +
              (Finset.range (q - 1)).sum (fun r => f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) 0)
            =
            f (q * d) + (Finset.range (q - 1)).sum (fun r => f ((r + 1) * d)) := by
        simp [apSum, apSumFrom, add_assoc, add_left_comm, add_comm]
      -- `apSum f d (q-1)` is exactly the residue `1..q-1` sum.
      have hAp : apSum f d (q - 1) = (Finset.range (q - 1)).sum (fun r => f ((r + 1) * d)) := by
        rfl
      -- Finish.
      calc
        apSum f d (q * (0 + 1))
            = apSum f d q := by simp
        _ = apSum f d (q - 1) + f (q * d) := hL
        _ = f (q * d) + (Finset.range (q - 1)).sum (fun r => f ((r + 1) * d)) := by
              simpa [hAp, add_assoc, add_left_comm, add_comm]
        _ = apSum f (q * d) 1 +
              (Finset.range (q - 1)).sum (fun r => f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) 0) := by
              simpa [hR, add_assoc, add_left_comm, add_comm]
  | succ n ih =>
      -- Write `q*(n+2)` as `q*(n+1) + q` and split off the final block of length `q`.
      have hmul : q * (n + 2) = q * (n + 1) + q := by ring
      have hsplit :
          apSum f d (q * (n + 2)) = apSum f d (q * (n + 1)) + apSumOffset f d (q * (n + 1)) q := by
        simpa [hmul] using
          (apSum_add_len (f := f) (d := d) (n₁ := q * (n + 1)) (n₂ := q))

      -- Expand the final block as: residues `1..q-1` plus the final `0 mod q` term.
      have hblock :
          apSumOffset f d (q * (n + 1)) q =
            (Finset.range (q - 1)).sum (fun r => f ((r + 1) * d + (n + 1) * (q * d))) + f ((n + 2) * (q * d)) := by
        -- Split `range q` as `range (q-1)` plus the last element.
        have hq' : q - 1 + 1 = q := Nat.sub_add_cancel h1
        unfold apSumOffset
        -- First, split the range.
        have hsum :
            (Finset.range q).sum (fun i => f ((q * (n + 1) + i + 1) * d)) =
              (Finset.range (q - 1)).sum (fun i => f ((q * (n + 1) + i + 1) * d)) +
                f ((q * (n + 1) + (q - 1) + 1) * d) := by
          simpa [hq'] using
            (Finset.sum_range_succ (fun i => f ((q * (n + 1) + i + 1) * d)) (q - 1))

        -- Rewrite the `range (q-1)` summand into the normal form `((r+1)*d) + (n+1)*(q*d)`.
        have hrewrite :
            (Finset.range (q - 1)).sum (fun i => f ((q * (n + 1) + i + 1) * d)) =
              (Finset.range (q - 1)).sum (fun r => f ((r + 1) * d + (n + 1) * (q * d))) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          -- Pure arithmetic normalization.
          have : (q * (n + 1) + r + 1) * d = (r + 1) * d + (n + 1) * (q * d) := by
            ring
          -- Avoid `simp` commutativity issues by rewriting via `congrArg`.
          simpa using congrArg f this

        -- Rewrite the final term.
        have hlast : (q * (n + 1) + (q - 1) + 1) * d = (n + 2) * (q * d) := by
          -- reassociate so `q-1+1` appears.
          calc
            (q * (n + 1) + (q - 1) + 1) * d
                = (q * (n + 1) + ((q - 1) + 1)) * d := by
                    simp [Nat.add_assoc]
            _ = (q * (n + 1) + q) * d := by
                    simp [Nat.sub_add_cancel h1]
            _ = (q * (n + 2)) * d := by
                    ring
            _ = (n + 2) * (q * d) := by
                    ring

        -- Combine.
        calc
          apSumOffset f d (q * (n + 1)) q
              = (Finset.range q).sum (fun i => f ((q * (n + 1) + i + 1) * d)) := by rfl
          _ = (Finset.range (q - 1)).sum (fun i => f ((q * (n + 1) + i + 1) * d)) +
                f ((q * (n + 1) + (q - 1) + 1) * d) := hsum
          _ = (Finset.range (q - 1)).sum (fun r => f ((r + 1) * d + (n + 1) * (q * d))) +
                f ((q * (n + 1) + (q - 1) + 1) * d) := by
                simpa [hrewrite]
          _ = (Finset.range (q - 1)).sum (fun r => f ((r + 1) * d + (n + 1) * (q * d))) + f ((n + 2) * (q * d)) := by
                simpa [hlast]

      -- Expand the RHS pieces at `n+1`.
      have hE : apSum f (q * d) (n + 2) = apSum f (q * d) (n + 1) + f ((n + 2) * (q * d)) := by
        simpa [Nat.add_assoc] using (apSum_succ (f := f) (d := q * d) (n := n + 1))

      have hF :
          (Finset.range (q - 1)).sum (fun r => f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) (n + 1)) =
            (Finset.range (q - 1)).sum (fun r => f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n) +
              (Finset.range (q - 1)).sum (fun r => f ((r + 1) * d + (n + 1) * (q * d))) := by
        -- Pointwise use `apSumFrom_succ`, then reassociate.
        have hpoint :
            ∀ r, f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) (n + 1) =
              (f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n) + f ((r + 1) * d + (n + 1) * (q * d)) := by
          intro r
          have := apSumFrom_succ (f := f) (a := (r + 1) * d) (d := q * d) (n := n)
          -- `this` is: apSumFrom ... (n+1) = apSumFrom ... n + f(...)
          -- Add `f((r+1)*d)` to both sides.
          -- Use `simp` to normalize the endpoint term.
          simpa [this, add_assoc, add_left_comm, add_comm]

        -- Convert the LHS sum by rewriting each term via `hpoint`.
        -- Then `Finset.sum_add_distrib` splits the two summands.
        classical
        -- Rewrite the summand.
        have hsum' :
            (Finset.range (q - 1)).sum (fun r => f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) (n + 1)) =
              (Finset.range (q - 1)).sum (fun r => (f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n) +
                f ((r + 1) * d + (n + 1) * (q * d))) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          simpa using (hpoint r)

        -- Split the sum of a sum.
        calc
          (Finset.range (q - 1)).sum (fun r => f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) (n + 1))
              = (Finset.range (q - 1)).sum (fun r => (f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n) +
                  f ((r + 1) * d + (n + 1) * (q * d))) := hsum'
          _ = (Finset.range (q - 1)).sum (fun r => (f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n)) +
                (Finset.range (q - 1)).sum (fun r => f ((r + 1) * d + (n + 1) * (q * d))) := by
                simpa [Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]

      -- Main calculation.
      calc
        apSum f d (q * (n + 2))
            = apSum f d (q * (n + 1)) + apSumOffset f d (q * (n + 1)) q := hsplit
        _ = (apSum f (q * d) (n + 1) +
              (Finset.range (q - 1)).sum (fun r => f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n))
              + apSumOffset f d (q * (n + 1)) q := by
              rw [ih]
        _ = (apSum f (q * d) (n + 1) +
              (Finset.range (q - 1)).sum (fun r => f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n))
              + ((Finset.range (q - 1)).sum (fun r => f ((r + 1) * d + (n + 1) * (q * d))) + f ((n + 2) * (q * d))) := by
              simpa [hblock]
        _ = apSum f (q * d) (n + 2) +
              (Finset.range (q - 1)).sum (fun r => f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) (n + 1)) := by
              -- use the expansions `hE` and `hF`, then rearrange
              rw [hE]
              rw [hF]
              abel

/-!
## Residue-class splitting into `q` blocks (all residue classes)

This is a more symmetric normal form than `apSum_mul_len_succ`: instead of separating out the
`0 mod q` class, it packages *all* residue classes into a single `Finset.range q` sum.

It matches the common “reindex by `i = q * k + r`” viewpoint.
-/

/-- Helper: split the `0 mod q` class `apSum f (q*d) (n+1)` into a head term and an affine tail.

This is the same arithmetic progression; we just expose the first term `f (q*d)` explicitly so it
fits the uniform residue-class summand form.
-/
lemma apSum_mul_succ_len_head_tail (f : ℕ → ℤ) (d q n : ℕ) :
    apSum f (q * d) (n + 1) = f (q * d) + apSumFrom f (q * d) (q * d) n := by
  classical
  unfold apSum apSumFrom

  -- A small arithmetic normalization used by `simp` under the tail sum.
  have hNat : ∀ i : ℕ, (i + 1 + 1) * (q * d) = q * d + (i + 1) * (q * d) := by
    intro i
    calc
      (i + 1 + 1) * (q * d) = ((i + 1) + 1) * (q * d) := by
        simp [Nat.add_assoc]
      _ = (i + 1) * (q * d) + 1 * (q * d) := by
        simpa [Nat.add_mul]
      _ = (i + 1) * (q * d) + (q * d) := by
        simp
      _ = q * d + (i + 1) * (q * d) := by
        simp [Nat.add_comm]

  -- Split the range sum into the head term plus the tail, then rewrite the tail
  -- into the `apSumFrom` summand form.
  -- `sum_range_succ'` gives: `∑ i < n+1, g i = g 0 + ∑ i < n, g (i+1)`.
  simp [Finset.sum_range_succ', hNat, Nat.mul_assoc]
  abel

/-- Symmetric residue-class split for homogeneous AP sums.

For `q > 0`, rewrite the length-`q*(n+1)` sum as a sum of `q` smaller blocks, one for each residue
class modulo `q`, using the reindexing `i = q*k + r`.

Each block is expressed in the uniform “head + affine tail” normal form
`f ((r+1)*d) + apSumFrom f ((r+1)*d) (q*d) n`.
-/
lemma apSum_mul_len_succ_eq_sum_range (f : ℕ → ℤ) (d q n : ℕ) (hq : q > 0) :
    apSum f d (q * (n + 1)) =
      (Finset.range q).sum (fun r => f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n) := by
  classical
  have h1 : 1 ≤ q := Nat.succ_le_iff.mp hq
  have hq' : q - 1 + 1 = q := Nat.sub_add_cancel h1

  -- Start from the existing split that isolates the `0 mod q` class.
  have h := apSum_mul_len_succ (f := f) (d := d) (q := q) (n := n) hq

  -- Rewrite the `0 mod q` class into the uniform head+tail form.
  have h0 : apSum f (q * d) (n + 1) = f (q * d) + apSumFrom f (q * d) (q * d) n :=
    apSum_mul_succ_len_head_tail (f := f) (d := d) (q := q) (n := n)

  -- Package everything as a single `range q` sum: `range q = range (q-1)` plus the last term.
  -- The last residue `r = q-1` corresponds to the `0 mod q` class.
  have hsum :
      (Finset.range q).sum (fun r => f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n) =
        (Finset.range (q - 1)).sum (fun r => f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n) +
          (f (q * d) + apSumFrom f (q * d) (q * d) n) := by
    -- `Finset.sum_range_succ` with `n = q-1`.
    -- Note: `q-1+1=q` by `hq'`.
    simpa [hq', Nat.sub_add_cancel h1, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Finset.sum_range_succ
        (fun r => f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n)
        (q - 1))

  -- Finish by rewriting `h` into the symmetric sum form.
  -- The existing lemma already has the `range (q-1)` part; we just replace the `0 mod q` class.
  calc
    apSum f d (q * (n + 1))
        = apSum f (q * d) (n + 1) +
            (Finset.range (q - 1)).sum (fun r => f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n) := h
    _ = (f (q * d) + apSumFrom f (q * d) (q * d) n) +
            (Finset.range (q - 1)).sum (fun r => f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n) := by
          simpa [h0, add_assoc, add_left_comm, add_comm]
    _ = (Finset.range q).sum (fun r => f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n) := by
          -- Commute the two summands, then use `hsum`.
          have hcomm :
              (f (q * d) + apSumFrom f (q * d) (q * d) n) +
                  (Finset.range (q - 1)).sum (fun r => f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n)
                =
                (Finset.range (q - 1)).sum (fun r => f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n) +
                  (f (q * d) + apSumFrom f (q * d) (q * d) n) := by
            abel
          -- Now rewrite using `hsum`.
          simpa [hcomm] using hsum.symm

/-- Residue-class split for affine AP sums.

This is the shifted analogue of `apSum_mul_len_succ_eq_sum_range`:
reindex `apSumFrom f a d (q*(n+1))` by `i = q*k + r`.
-/
lemma apSumFrom_mul_len_succ_eq_sum_range (f : ℕ → ℤ) (a d q n : ℕ) (hq : q > 0) :
    apSumFrom f a d (q * (n + 1)) =
      (Finset.range q).sum (fun r => f (a + (r + 1) * d) + apSumFrom f (a + (r + 1) * d) (q * d) n) := by
  classical
  -- Apply the homogeneous split to the shifted sequence `k ↦ f (k + a)`.
  have h :=
    apSum_mul_len_succ_eq_sum_range (f := fun k => f (k + a)) (d := d) (q := q) (n := n) hq

  -- Normalize the LHS `apSum` into `apSumFrom`.
  have hL : apSum (fun k => f (k + a)) d (q * (n + 1)) = apSumFrom f a d (q * (n + 1)) := by
    simpa [apSum_shift_add_eq_apSumFrom] using
      (apSum_shift_add_eq_apSumFrom (f := f) (a := a) (d := d) (n := q * (n + 1)))

  -- Normalize each summand on the RHS.
  have hR :
      (Finset.range q).sum (fun r => (fun k => f (k + a)) ((r + 1) * d) +
          apSumFrom (fun k => f (k + a)) ((r + 1) * d) (q * d) n)
        =
        (Finset.range q).sum (fun r => f (a + (r + 1) * d) + apSumFrom f (a + (r + 1) * d) (q * d) n) := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    -- First term: just reassociate `((r+1)*d) + a`.
    -- Second term: push the shift into the start.
    unfold apSumFrom
    -- `simp` can handle the arithmetic normalization under the binder.
    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

  -- Put it together.
  -- `h` is an equality; rewrite both sides by `hL` and `hR`.
  simpa [hL, hR] using h

/-- Residue-class split for affine tails `apSumFrom f (a + m*d) d …`.

This is a small arithmetic-convenience wrapper around `apSumFrom_mul_len_succ_eq_sum_range`.
It avoids a downstream “normalize the start by hand” step when working with affine tails.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Residue-class split for affine tails.
-/
lemma apSumFrom_tail_mul_len_succ_eq_sum_range
    (f : ℕ → ℤ) (a d m q n : ℕ) (hq : q > 0) :
    apSumFrom f (a + m * d) d (q * (n + 1)) =
      (Finset.range q).sum (fun r =>
        f (a + (m + r + 1) * d) + apSumFrom f (a + (m + r + 1) * d) (q * d) n) := by
  classical
  have h :=
    apSumFrom_mul_len_succ_eq_sum_range (f := f) (a := a + m * d) (d := d) (q := q) (n := n) hq

  -- Normalize the residue-class starts: `(a + m*d) + (r+1)*d = a + (m+r+1)*d`.
  have hadd : ∀ r : ℕ, (a + m * d) + (r + 1) * d = a + (m + r + 1) * d := by
    intro r
    calc
      (a + m * d) + (r + 1) * d = a + (m * d + (r + 1) * d) := by
        simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      _ = a + ((m + (r + 1)) * d) := by
        -- `m*d + (r+1)*d = (m+(r+1))*d`.
        simpa [Nat.add_mul] using (Nat.add_mul m (r + 1) d).symm
      _ = a + (m + r + 1) * d := by
        simp [Nat.add_assoc]

  -- Rewrite each summand using `hadd`.
  simpa [hadd, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/-!
### Discrepancy inequality: affine tails

Checklist item: Problems/erdos_discrepancy.md (Track B) — Residue-class split for affine tails (disc-level inequality).

After rewriting an affine tail sum into the residue-class split normal form, apply the triangle
inequality to bound the absolute value by the sum of absolute values of the residue blocks.
-/

/-- Triangle-inequality bound for residue-class splitting of an affine tail `apSumFrom f (a + m*d) d …`.

We do not currently have a dedicated discrepancy wrapper for `apSumFrom`, so this lemma is stated
at the `Int.natAbs` level.
-/
lemma natAbs_apSumFrom_tail_mul_len_succ_le_sum_range_natAbs
    (f : ℕ → ℤ) (a d m q n : ℕ) (hq : q > 0) :
    Int.natAbs (apSumFrom f (a + m * d) d (q * (n + 1))) ≤
      (Finset.range q).sum (fun r =>
        Int.natAbs (f (a + (m + r + 1) * d) + apSumFrom f (a + (m + r + 1) * d) (q * d) n)) := by
  classical
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

  -- Rewrite to the residue split normal form and apply the triangle inequality.
  simpa [apSumFrom_tail_mul_len_succ_eq_sum_range (f := f) (a := a) (d := d) (m := m) (q := q) (n := n) hq] using
    (natAbs_sum_le_sum_natAbs (Finset.range q)
      (fun r => f (a + (m + r + 1) * d) + apSumFrom f (a + (m + r + 1) * d) (q * d) n))

/-- Residue-class split for offset AP sums.

This is the offset analogue of `apSum_mul_len_succ_eq_sum_range`.
It follows by rewriting `apSumOffset` as an affine AP sum via `apSumOffset_eq_apSumFrom`.
-/
lemma apSumOffset_mul_len_succ_eq_sum_range (f : ℕ → ℤ) (d m q n : ℕ) (hq : q > 0) :
    apSumOffset f d m (q * (n + 1)) =
      (Finset.range q).sum (fun r =>
        f ((m + r + 1) * d) + apSumFrom f ((m + r + 1) * d) (q * d) n) := by
  -- Convert to the affine nucleus, apply the affine split, and simplify the starts.
  have h := apSumFrom_mul_len_succ_eq_sum_range (f := f) (a := m * d) (d := d) (q := q) (n := n) hq
  -- `m*d + (r+1)*d = (m+r+1)*d`.
  have hadd : ∀ r : ℕ, m * d + (r + 1) * d = (m + r + 1) * d := by
    intro r
    -- `m*d + (r+1)*d = (m + (r+1))*d`.
    calc
      m * d + (r + 1) * d = (m + (r + 1)) * d := by
        simpa [Nat.add_mul] using (Nat.add_mul m (r + 1) d).symm
      _ = (m + r + 1) * d := by
        simp [Nat.add_assoc]
  -- Finish.
  simpa [apSumOffset_eq_apSumFrom, hadd, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/-!
## Step-one + residue split (bundled normal form)

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Drop-to-step-one then split residues”.

These lemmas package a common downstream rewrite pipeline:

1. normalize an offset AP sum into the step-one normal form
   `apSumOffset f d m n = apSumOffset (fun k => f (k*d)) 1 m n`, then
2. apply the residue-class split for offset sums.

The result is a single `rw` that produces a `∑ r<q` decomposition without intermediate rewrites.
-/

/-- Bundle: step-one normalization + residue-class split for `apSumOffset` at length `q*(n+1)`.

This rewrites the step size `d` into the summand and then performs the residue split at modulus `q`.
-/
lemma apSumOffset_step_one_mul_len_succ_eq_sum_range
    (f : ℕ → ℤ) (d m q n : ℕ) (hq : q > 0) :
    apSumOffset f d m (q * (n + 1)) =
      (Finset.range q).sum (fun r =>
        f ((m + r + 1) * d) + apSumFrom (fun k => f (k * d)) (m + r + 1) q n) := by
  -- Step 1: drop to step-one.
  have hstep : apSumOffset f d m (q * (n + 1)) = apSumOffset (fun k => f (k * d)) 1 m (q * (n + 1)) := by
    simpa using (apSumOffset_eq_apSumOffset_step_one (f := f) (d := d) (m := m) (n := q * (n + 1)))
  -- Step 2: split residues at `d = 1`.
  -- Then simplify the arithmetic in the summand.
  simpa [hstep, Nat.mul_one, Nat.one_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (apSumOffset_mul_len_succ_eq_sum_range
      (f := fun k => f (k * d)) (d := 1) (m := m) (q := q) (n := n) hq)

/-- Bundle: step-one normalization + residue-class split for `discOffset` at length `q*(n+1)`.

This is the `discOffset`-level companion to `apSumOffset_step_one_mul_len_succ_eq_sum_range`.
-/
lemma discOffset_step_one_mul_len_succ_eq_natAbs_sum_range
    (f : ℕ → ℤ) (d m q n : ℕ) (hq : q > 0) :
    discOffset f d m (q * (n + 1)) =
      Int.natAbs ((Finset.range q).sum (fun r =>
        f ((m + r + 1) * d) + apSumFrom (fun k => f (k * d)) (m + r + 1) q n)) := by
  unfold discOffset
  simp [apSumOffset_step_one_mul_len_succ_eq_sum_range (f := f) (d := d) (m := m) (q := q) (n := n) hq]


/-!
## Support API for residue decomposition (Track B)

Checklist item: Problems/erdos_discrepancy.md (Track B) — Residue decomposition support API.

After splitting a length-`q*(n+1)` offset AP sum into residue classes modulo `q`, it is useful to
have a corresponding statement at the level of the *accessed-index support* finset `apSupport`.

We package this as:
- a finset `apSupportResidue d m q n r` for the indices accessed by the `r`-th residue class, and
- a rewrite lemma expressing `apSupport d m (q*(n+1))` as the union of these residue supports.

When `d > 0`, these residue supports are pairwise disjoint (no multiplicities collapse).
-/

def apSupportResidue (d m q n r : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).image (fun k => (m + (q * k + r) + 1) * d)

lemma apSupport_mul_len_succ_eq_biUnion_apSupportResidue (d m q n : ℕ) (hq : q > 0) :
    apSupport d m (q * (n + 1)) =
      (Finset.range q).biUnion (fun r => apSupportResidue d m q n r) := by
  classical
  ext x
  constructor
  · intro hx
    rcases (mem_apSupport (d := d) (m := m) (n := q * (n + 1)) (x := x)).1 hx with ⟨i, hi, rfl⟩
    let r : ℕ := i % q
    let k : ℕ := i / q
    have hr : r < q := Nat.mod_lt _ hq
    have hk : k < n + 1 := by
      -- `i < q*(n+1)` implies `i/q < n+1` when `q > 0`.
      have hi' : i < (n + 1) * q := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hi
      have : i / q < n + 1 := (Nat.div_lt_iff_lt_mul hq).2 (by simpa [Nat.mul_comm] using hi')
      simpa [k] using this
    have hdecomp : q * k + r = i := by
      -- `i / q * q + i % q = i`.
      simpa [k, r, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.div_add_mod i q)

    -- Membership in the biUnion.
    refine (Finset.mem_biUnion).2 ?_
    refine ⟨r, Finset.mem_range.2 hr, ?_⟩
    refine Finset.mem_image.2 ?_
    refine ⟨k, Finset.mem_range.2 hk, ?_⟩
    -- Normalize `q*k + r` back to `i`.
    simp [apSupportResidue, hdecomp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

  · intro hx
    rcases (Finset.mem_biUnion).1 hx with ⟨r, hr, hx⟩
    rcases Finset.mem_image.1 hx with ⟨k, hk, rfl⟩
    have hr' : r < q := Finset.mem_range.1 hr
    have hk' : k < n + 1 := Finset.mem_range.1 hk
    -- Show the combined index `i = q*k + r` lies in the `q*(n+1)` range.
    have hi : q * k + r < q * (n + 1) := by
      -- First, `q*k + r < q*k + q` since `r < q`.
      have h1 : q * k + r < q * k + q := Nat.add_lt_add_left hr' _
      -- And `q*k + q = q*(k+1) ≤ q*(n+1)` since `k+1 ≤ n+1`.
      have hle : q * k + q ≤ q * (n + 1) := by
        have hkle : k + 1 ≤ n + 1 := Nat.succ_le_of_lt hk'
        -- Multiply the inequality by `q` on the left.
        have : q * (k + 1) ≤ q * (n + 1) := Nat.mul_le_mul_left q hkle
        -- Rewrite `q*(k+1)`.
        simpa [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
      exact lt_of_lt_of_le h1 hle

    exact (mem_apSupport (d := d) (m := m) (n := q * (n + 1)) (x := (m + (q * k + r) + 1) * d)).2
      ⟨q * k + r, by simpa [Nat.mul_assoc] using hi, rfl⟩

lemma disjoint_apSupportResidue_of_ne
    (d m q n r₁ r₂ : ℕ) (hq : q > 0) (hd : d > 0) (hr₁ : r₁ < q) (hr₂ : r₂ < q) (hne : r₁ ≠ r₂) :
    Disjoint (apSupportResidue d m q n r₁) (apSupportResidue d m q n r₂) := by
  classical
  -- Prove disjointness by elementwise contradiction.
  refine Finset.disjoint_left.2 ?_
  intro x hx₁ hx₂
  rcases Finset.mem_image.1 hx₁ with ⟨k₁, hk₁, hkx₁⟩
  rcases Finset.mem_image.1 hx₂ with ⟨k₂, hk₂, hkx₂⟩

  -- Cancel the positive factor `d`.
  have hmul : (m + (q * k₁ + r₁) + 1) = (m + (q * k₂ + r₂) + 1) := by
    apply Nat.mul_right_cancel hd
    -- both sides equal `x`.
    simpa [apSupportResidue] using hkx₁.trans hkx₂.symm

  -- Cancel the common `m` and the trailing `+ 1`.
  have hidx : q * k₁ + r₁ = q * k₂ + r₂ := by
    -- First cancel the common prefix `m`.
    have h' : (q * k₁ + r₁) + 1 = (q * k₂ + r₂) + 1 := by
      have hm' : m + ((q * k₁ + r₁) + 1) = m + ((q * k₂ + r₂) + 1) := by
        simpa [Nat.add_assoc] using hmul
      exact Nat.add_left_cancel hm'
    exact Nat.succ_inj.mp h'

  -- Reduce the equality modulo `q` to force `r₁ = r₂`.
  have hmod : (q * k₁ + r₁) % q = (q * k₂ + r₂) % q := congrArg (fun t => t % q) hidx
  have : r₁ = r₂ := by
    -- simplify both sides using `r < q`.
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hr₁, Nat.mod_eq_of_lt hr₂] using hmod

  exact hne this


/-!
## Multiplication-on-the-left variants

These are small convenience wrappers around the main residue-class split lemmas.
They keep the summands in the `d * i` form, which can be friendlier in downstream code
(since it avoids commuting multiplication under binders).
-/

/-- `d * i` summand-order variant of `apSum_mul_len_succ_eq_sum_range`. -/
lemma apSum_mul_len_succ_eq_sum_range_mul_left (f : ℕ → ℤ) (d q n : ℕ) (hq : q > 0) :
    apSum f d (q * (n + 1)) =
      (Finset.range q).sum (fun r => f (d * (r + 1)) + apSumFrom f (d * (r + 1)) (q * d) n) := by
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (apSum_mul_len_succ_eq_sum_range (f := f) (d := d) (q := q) (n := n) hq)

/-- `d * i` summand-order variant of `apSumOffset_mul_len_succ_eq_sum_range`. -/
lemma apSumOffset_mul_len_succ_eq_sum_range_mul_left (f : ℕ → ℤ) (d m q n : ℕ) (hq : q > 0) :
    apSumOffset f d m (q * (n + 1)) =
      (Finset.range q).sum (fun r =>
        f (d * (m + r + 1)) + apSumFrom f (d * (m + r + 1)) (q * d) n) := by
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (apSumOffset_mul_len_succ_eq_sum_range (f := f) (d := d) (m := m) (q := q) (n := n) hq)

/-!
## Paper-notation residue-class splitting (`Finset.Icc` form)

Checklist item: Problems/erdos_discrepancy.md (Track B) —
“Sum-level residue-class decomposition (offset form): after splitting `Finset.Icc (m+1) (m+n)` into
residues mod `r`, prove a canonical equality”.

These lemmas are thin wrappers that let callers start from the common “paper” interval notation
`∑ i∈Icc (m+1) (m+N), …` and jump directly to the residue-class normal form.

They are intentionally phrased for the special-but-common block length `N = q*(n+1)`; this is the
shape produced by repeated residue-class splitting in discrepancy arguments.
-/

/-- Residue-class split normal form for the paper-notation interval sum
`∑ i ∈ Icc (m+1) (m+q*(n+1)), f (i*d)`.

This is the `Finset.Icc`-notation wrapper around `apSumOffset_mul_len_succ_eq_sum_range`.
-/
lemma sum_Icc_mul_len_succ_eq_sum_range
    (f : ℕ → ℤ) (d m q n : ℕ) (hq : q > 0) :
    (Finset.Icc (m + 1) (m + q * (n + 1))).sum (fun i => f (i * d)) =
      (Finset.range q).sum (fun r =>
        f ((m + r + 1) * d) + apSumFrom f ((m + r + 1) * d) (q * d) n) := by
  calc
    (Finset.Icc (m + 1) (m + q * (n + 1))).sum (fun i => f (i * d))
        = apSumOffset f d m (q * (n + 1)) := by
            simpa using
              (sum_Icc_eq_apSumOffset (f := f) (d := d) (m := m) (n := q * (n + 1)))
    _ = (Finset.range q).sum (fun r =>
          f ((m + r + 1) * d) + apSumFrom f ((m + r + 1) * d) (q * d) n) := by
          simpa using
            (apSumOffset_mul_len_succ_eq_sum_range (f := f) (d := d) (m := m) (q := q) (n := n) hq)

/-- `d * i` summand-order variant of `sum_Icc_mul_len_succ_eq_sum_range`. -/
lemma sum_Icc_mul_len_succ_eq_sum_range_mul_left
    (f : ℕ → ℤ) (d m q n : ℕ) (hq : q > 0) :
    (Finset.Icc (m + 1) (m + q * (n + 1))).sum (fun i => f (d * i)) =
      (Finset.range q).sum (fun r =>
        f (d * (m + r + 1)) + apSumFrom f (d * (m + r + 1)) (q * d) n) := by
  calc
    (Finset.Icc (m + 1) (m + q * (n + 1))).sum (fun i => f (d * i))
        = apSumOffset f d m (q * (n + 1)) := by
            simpa using
              (sum_Icc_eq_apSumOffset_mul_left (f := f) (d := d) (m := m) (n := q * (n + 1)))
    _ = (Finset.range q).sum (fun r =>
          f (d * (m + r + 1)) + apSumFrom f (d * (m + r + 1)) (q * d) n) := by
          simpa using
            (apSumOffset_mul_len_succ_eq_sum_range_mul_left (f := f) (d := d) (m := m)
              (q := q) (n := n) hq)

/-!
## Nested-sum residue-class splitting (reindexing normal form)

The “nested sum” normal forms for residue-class splitting (residue `r` outer, quotient `k` inner)
are useful occasionally, but they are not part of the stable discrepancy surface.

They live behind an explicit opt-in import:

```lean
import MoltResearch.Discrepancy.Deprecated
```

See `MoltResearch.Discrepancy.ResidueDeprecated`.
-/

/-!
## Discrepancy-level residue-class splitting

These are thin wrappers around the sum-level residue split lemmas, rewriting `discOffset` (which is
`Int.natAbs` of an `apSumOffset`) into the corresponding residue-class normal form.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Residue-class split (offset → r tracks).
-/

/-- Residue-class split normal form for `discOffset` (offset discrepancy) at a block length `q*(n+1)`. -/
lemma discOffset_mul_len_succ_eq_natAbs_sum_range (f : ℕ → ℤ) (d m q n : ℕ) (hq : q > 0) :
    discOffset f d m (q * (n + 1)) =
      Int.natAbs ((Finset.range q).sum (fun r =>
        f ((m + r + 1) * d) + apSumFrom f ((m + r + 1) * d) (q * d) n)) := by
  unfold discOffset
  simp [apSumOffset_mul_len_succ_eq_sum_range (f := f) (d := d) (m := m) (q := q) (n := n) hq]

/-- `d * i` summand-order variant of `discOffset_mul_len_succ_eq_natAbs_sum_range`. -/
lemma discOffset_mul_len_succ_eq_natAbs_sum_range_mul_left (f : ℕ → ℤ) (d m q n : ℕ) (hq : q > 0) :
    discOffset f d m (q * (n + 1)) =
      Int.natAbs ((Finset.range q).sum (fun r =>
        f (d * (m + r + 1)) + apSumFrom f (d * (m + r + 1)) (q * d) n)) := by
  unfold discOffset
  simp [apSumOffset_mul_len_succ_eq_sum_range_mul_left (f := f) (d := d) (m := m) (q := q) (n := n) hq]

/-!
### Discrepancy inequality: bound by sum of residue discrepancies

Checklist item: Problems/erdos_discrepancy.md (Track B) — Residue-class on offsets: disc-level inequality.

After rewriting an offset discrepancy into the residue-class split normal form, apply the triangle
inequality to bound the whole discrepancy by the sum of the residue-class discrepancies.
-/

/-- Triangle-inequality bound for the residue-class split normal form of `discOffset`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Residue-class on offsets: disc-level inequality.
-/
lemma discOffset_mul_len_succ_le_sum_range_natAbs (f : ℕ → ℤ) (d m q n : ℕ) (hq : q > 0) :
    discOffset f d m (q * (n + 1)) ≤
      (Finset.range q).sum (fun r =>
        Int.natAbs (f ((m + r + 1) * d) + apSumFrom f ((m + r + 1) * d) (q * d) n)) := by
  classical
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

  -- Rewrite to the residue-class split normal form and apply the triangle inequality.
  -- (We keep the summand in the stable-surface `f + apSumFrom` form.)
  simpa [discOffset_mul_len_succ_eq_natAbs_sum_range (f := f) (d := d) (m := m) (q := q) (n := n) hq] using
    (natAbs_sum_le_sum_natAbs (Finset.range q)
      (fun r => f ((m + r + 1) * d) + apSumFrom f ((m + r + 1) * d) (q * d) n))



/-!
### Max-level residue-class bound (block lengths `q*(n+1)`)

Checklist item: Problems/erdos_discrepancy.md (Track B) — Residue-class bound at max-level.

We often want a *max discrepancy up to a cutoff* but only along the block lengths `q*(n+1)` that
appear naturally after residue-class splitting.  This lemma packages the residue-class split
inequality at the level of the `Finset.sup` maximum over `n ≤ N`.

The bound is stated in terms of the residue-class split summands
`Int.natAbs (f (...) + apSumFrom ...)`, keeping the stable-surface normal form exposed by
`discOffset_mul_len_succ_le_sum_range_natAbs`.
-/

/-- Max discrepancy (over `n ≤ N`) restricted to the block lengths `q*(n+1)`. -/
def discOffsetUpTo_blockLen_mul_succ (f : ℕ → ℤ) (d m q N : ℕ) : ℕ :=
  (Finset.range (N + 1)).sup (fun n => discOffset f d m (q * (n + 1)))

/-- Max-level residue-class bound for block lengths `q*(n+1)`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Residue-class bound at max-level.
-/
lemma discOffsetUpTo_blockLen_mul_succ_le_sum_range_sup_natAbs (f : ℕ → ℤ)
    (d m q N : ℕ) (hq : q > 0) :
    discOffsetUpTo_blockLen_mul_succ f d m q N ≤
      (Finset.range q).sum (fun r =>
        (Finset.range (N + 1)).sup (fun n =>
          Int.natAbs (f ((m + r + 1) * d) + apSumFrom f ((m + r + 1) * d) (q * d) n))) := by
  classical
  unfold discOffsetUpTo_blockLen_mul_succ
  -- bound each term in the `sup` using the residue-class split inequality, then push the bound
  -- through the finite supremum.
  refine Finset.sup_le ?_
  intro n hn
  have hsplit : discOffset f d m (q * (n + 1)) ≤
      (Finset.range q).sum (fun r =>
        Int.natAbs (f ((m + r + 1) * d) + apSumFrom f ((m + r + 1) * d) (q * d) n)) :=
    discOffset_mul_len_succ_le_sum_range_natAbs (f := f) (d := d) (m := m) (q := q) (n := n) hq
  -- each residue summand is ≤ the corresponding `sup` over all `n ≤ N`.
  have hterm : (Finset.range q).sum (fun r =>
        Int.natAbs (f ((m + r + 1) * d) + apSumFrom f ((m + r + 1) * d) (q * d) n)) ≤
      (Finset.range q).sum (fun r =>
        (Finset.range (N + 1)).sup (fun t =>
          Int.natAbs (f ((m + r + 1) * d) + apSumFrom f ((m + r + 1) * d) (q * d) t))) := by
    -- pointwise bound, then sum.
    refine Finset.sum_le_sum ?_
    intro r hr
    -- `n ∈ range (N+1)` so we can take the `le_sup` bound at index `n`.
    exact Finset.le_sup (s := Finset.range (N + 1))
      (f := fun t => Int.natAbs (f ((m + r + 1) * d) + apSumFrom f ((m + r + 1) * d) (q * d) t)) hn
  exact le_trans hsplit hterm

/-!
### Residue max inequality (clean API surface)

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Residue max inequality (clean API surface)”.

This is just a lightweight wrapper around the residue-class `sup` term that appears in
`discOffsetUpTo_blockLen_mul_succ_le_sum_range_sup_natAbs`.

Downstream proofs can now refer to `discOffsetUpTo_residueTerm` without restating the `Finset.sup`
expression (and without ad-hoc reindexing).
-/

/-- The `r`-th residue-class term appearing in the max-level bound for block lengths.

This is the finitary supremum over `n ≤ N` of the absolute value of the residue-class split summand
in `discOffset_mul_len_succ_le_sum_range_natAbs`.
-/
def discOffsetUpTo_residueTerm (f : ℕ → ℤ) (d m q r N : ℕ) : ℕ :=
  (Finset.range (N + 1)).sup (fun n =>
    Int.natAbs (f ((m + r + 1) * d) + apSumFrom f ((m + r + 1) * d) (q * d) n))

/-- Restatement of `discOffsetUpTo_blockLen_mul_succ_le_sum_range_sup_natAbs` using the clean API
surface `discOffsetUpTo_residueTerm`.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Residue max inequality (clean API surface)”.
-/
lemma discOffsetUpTo_blockLen_mul_succ_le_sum_range_residueTerm (f : ℕ → ℤ)
    (d m q N : ℕ) (hq : q > 0) :
    discOffsetUpTo_blockLen_mul_succ f d m q N ≤
      (Finset.range q).sum (fun r => discOffsetUpTo_residueTerm f d m q r N) := by
  simpa [discOffsetUpTo_residueTerm] using
    (discOffsetUpTo_blockLen_mul_succ_le_sum_range_sup_natAbs (f := f) (d := d) (m := m) (q := q)
      (N := N) hq)

/-!
### “Argmax extractor” (pigeonhole) wrapper for residue/max pipelines

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Argmax extractor” for residue/max pipelines.

Given an inequality of the form `X ≤ ∑ r, Y r` over a finite range, this produces an index `r`
whose term is large enough (up to a factor of the range size).

This is the standard pigeonhole step used to pass from a *sum of residue-class terms* to a *single*
residue class controlling the whole quantity.
-/

/-- Pigeonhole step: if `X ≤ ∑ r < q, Y r` then some residue `r` satisfies `X ≤ q * Y r`.

This is the “extract a large term from a large sum” lemma, specialized to a `range` sum.
-/
lemma exists_le_mul_of_le_sum_range (X q : ℕ) (Y : ℕ → ℕ) (hq : q > 0)
    (hX : X ≤ (Finset.range q).sum Y) :
    ∃ r < q, X ≤ q * Y r := by
  classical
  by_contra h
  have hall : ∀ r ∈ Finset.range q, q * Y r < X := by
    intro r hr
    have : ¬ X ≤ q * Y r := by
      -- unpack the negated `∃`.
      intro hle
      exact h ⟨r, by simpa using hr, hle⟩
    exact Nat.lt_of_not_ge this
  have hsumlt : (Finset.range q).sum (fun r => q * Y r) < (Finset.range q).sum (fun _ => X) := by
    have hle : ∀ r ∈ Finset.range q, (q * Y r) ≤ X := by
      intro r hr
      exact le_of_lt (hall r hr)
    have hex : ∃ r ∈ Finset.range q, (q * Y r) < X := by
      refine ⟨0, ?_, hall 0 ?_⟩
      · exact (Finset.mem_range.mpr hq)
      · exact (Finset.mem_range.mpr hq)
    exact Finset.sum_lt_sum hle hex
  have hmul_lt : q * ((Finset.range q).sum Y) < q * X := by
    -- rewrite both sides of `hsumlt`.
    simpa [Finset.mul_sum] using hsumlt
  have hmul_le : q * X ≤ q * ((Finset.range q).sum Y) := by
    exact Nat.mul_le_mul_left q hX
  exact (not_lt_of_ge hmul_le) hmul_lt

/-- Packaged “argmax extractor” for the max-level residue inequality:
from the stable-surface sum bound, extract a single residue class controlling the LHS.

Checklist item: Problems/erdos_discrepancy.md (Track B) — “Argmax extractor” for residue/max pipelines.
-/
lemma exists_discOffsetUpTo_blockLen_mul_succ_le_mul_residueTerm (f : ℕ → ℤ)
    (d m q N : ℕ) (hq : q > 0) :
    ∃ r < q,
      discOffsetUpTo_blockLen_mul_succ f d m q N ≤
        q * discOffsetUpTo_residueTerm f d m q r N := by
  have hsum :=
    discOffsetUpTo_blockLen_mul_succ_le_sum_range_residueTerm (f := f) (d := d) (m := m)
      (q := q) (N := N) hq
  -- Apply the generic pigeonhole lemma to the residue-term sum.
  simpa using
    (exists_le_mul_of_le_sum_range (X := discOffsetUpTo_blockLen_mul_succ f d m q N) (q := q)
      (Y := fun r => discOffsetUpTo_residueTerm f d m q r N) hq hsum)

end MoltResearch
