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
## Nested-sum residue-class splitting (reindexing normal form)

These are lightweight wrappers around the general reindexing lemma
`sum_range_mul_reindex_mod_div`, specialized to the `apSum` nucleus.

Checklist item: Problems/erdos_discrepancy.md (Track B) — Residue-class split (homogeneous, nucleus).
-/

/-- Residue-class split for `apSum` as a **nested sum** over residues `r < q` and quotients `k < n+1`.

This is a direct reindexing normal form of the length-`q*(n+1)` homogeneous AP sum.
-/
lemma apSum_mul_len_succ_eq_sum_range_sum_range (f : ℕ → ℤ) (d q n : ℕ) (hq : q > 0) :
    apSum f d (q * (n + 1)) =
      (Finset.range q).sum (fun r =>
        (Finset.range (n + 1)).sum (fun k => f ((q * k + (r + 1)) * d))) := by
  classical
  -- Apply the generic range reindexing lemma to the summand function `i ↦ f ((i+1)*d)`.
  simpa [apSum, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (sum_range_mul_reindex_mod_div (q := q) (n := n + 1) (hq := hq)
      (f := fun i => f ((i + 1) * d)))

/-- `d*i` multiplication-order variant of `apSum_mul_len_succ_eq_sum_range_sum_range`. -/
lemma apSum_mul_len_succ_eq_sum_range_sum_range_mul_left (f : ℕ → ℤ) (d q n : ℕ) (hq : q > 0) :
    apSum f d (q * (n + 1)) =
      (Finset.range q).sum (fun r =>
        (Finset.range (n + 1)).sum (fun k => f (d * (q * k + (r + 1))))) := by
  -- Just commute multiplication in the summand of the previous lemma.
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (apSum_mul_len_succ_eq_sum_range_sum_range (f := f) (d := d) (q := q) (n := n) hq)

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

end MoltResearch
