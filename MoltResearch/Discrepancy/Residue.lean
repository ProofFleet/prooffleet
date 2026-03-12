import MoltResearch.Discrepancy.Affine

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

end MoltResearch
