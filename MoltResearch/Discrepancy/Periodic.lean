import MoltResearch.Discrepancy.Basic

/-!
# Discrepancy: periodicity lemmas

This file records small normalization lemmas for arithmetic-progression sums when the
underlying sequence is (additively) periodic.

Main use: if `f` has period `p`, then any AP whose step is a multiple of `p` only samples
values of `f` at multiples of `p`, hence is a constant sum.
-/

namespace MoltResearch

variable {f : ℕ → ℤ} {p : ℕ}

/-- If `f` is periodic with period `p`, then `f (t * p) = f 0` for all `t`. -/
lemma periodic_mul_eq (hp : Function.Periodic f p) (t : ℕ) : f (t * p) = f 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
      -- `(t+1) * p = t * p + p` and then use periodicity.
      have hper : f (t * p + p) = f (t * p) := by
        simpa using (hp (t * p))
      -- Finish by rewriting and applying the IH.
      simpa [Nat.succ_mul, ih] using hper

/-- **Periodicity normal form.**

If `f` has additive period `p`, then an offset AP sum with step `p*d` is a constant sum.

This is often the right normal form for later Fourier/character-style manipulations.
-/
lemma apSumOffset_mul_periodic (hp : Function.Periodic f p) (d m n : ℕ) :
    apSumOffset f (p * d) m n = n • f 0 := by
  unfold apSumOffset
  -- Every term is `f 0` since each index is a multiple of `p`.
  have hterm : ∀ i, f ((m + i + 1) * (p * d)) = f 0 := by
    intro i
    -- Rewrite the argument into the form `t * p`.
    have : (m + i + 1) * (p * d) = ((m + i + 1) * d) * p := by
      -- `a*(p*d) = a*d*p`.
      simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    -- Now use `periodic_mul_eq`.
    simpa [this] using (periodic_mul_eq (f := f) (p := p) hp ((m + i + 1) * d))

  -- Rewrite the sum to a constant sum.
  have : (Finset.range n).sum (fun i => f ((m + i + 1) * (p * d))) =
      (Finset.range n).sum (fun _ => f 0) := by
    refine Finset.sum_congr rfl ?_
    intro i _hi
    exact hterm i

  -- Evaluate the constant sum.
  calc
    (Finset.range n).sum (fun i => f ((m + i + 1) * (p * d)))
        = (Finset.range n).sum (fun _ => f 0) := this
    _ = n • f 0 := by
        simp

/-!
## Periodicity normal form (step divides the period)

Checklist item: `Problems/erdos_discrepancy.md` (Track B) — Periodicity normal form for `discOffset`.

If `f` has period `p` and `p ∣ d`, then an offset AP sum with step `d` only samples values of `f`
at multiples of `p`, hence is a constant sum. This is the same normal form as
`apSumOffset_mul_periodic`, but with the divisibility hypothesis exposed.
-/

/-- If `f` is periodic with period `p` and `p ∣ d`, then `apSumOffset f d m n` is the constant sum
`n • f 0`.

This is a normalization lemma used in Track B.
-/
lemma apSumOffset_periodic_of_dvd_step (hp : Function.Periodic f p) {d : ℕ} (hd : p ∣ d)
    (m n : ℕ) :
    apSumOffset f d m n = n • f 0 := by
  rcases hd with ⟨k, rfl⟩
  -- Reduce to the explicit `p * k` form.
  simpa using (apSumOffset_mul_periodic (f := f) (p := p) hp (d := k) (m := m) (n := n))

/-- If `f` is periodic with period `p` and `p ∣ d`, then `discOffset f d m n` is independent of the
starting index `m`.

This is the `discOffset`-level periodicity normal form requested in Track B.
-/
lemma discOffset_periodic_of_dvd_step (hp : Function.Periodic f p) {d : ℕ} (hd : p ∣ d)
    (m n : ℕ) :
    discOffset f d m n = discOffset f d 0 n := by
  unfold discOffset
  simp [apSumOffset_periodic_of_dvd_step (f := f) (p := p) hp (d := d) hd (m := m) (n := n),
    apSumOffset_periodic_of_dvd_step (f := f) (p := p) hp (d := d) hd (m := 0) (n := n)]

end MoltResearch
