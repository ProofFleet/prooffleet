import MoltResearch.Discrepancy
-- Opt-in simp set regression tests (does not affect the stable surface).
import MoltResearch.Discrepancy.DiscOffsetSimp
import MoltResearch.Discrepancy.DiscSimp

-- (CI) Touch this file to retrigger PR metadata validation after PR-body edits.

/-!
# Discrepancy normal-form regression examples

This module is a standalone compilation test-bed for the preferred “normal form” rewrite pipelines.

It imports the **stable surface** `MoltResearch.Discrepancy`, and additionally imports a couple of
**opt-in** simp bundles (`DiscOffsetSimp`, `DiscSimp`) solely to run regression tests for those
simp collections.

Downstream developments should not need to import this file.
-/

namespace MoltResearch

section NormalFormExamples

variable (f : ℕ → ℤ) (a b d k m n n₁ n₂ p C : ℕ)

-- Regression: `simp` should normalize away a spurious zero-offset tail.
example : apSumOffset f d 0 n = apSum f d n := by
  simp

-- Regression (Track B / homogeneous view of offsets): push the offset `m*d` into the summand.
example : apSumOffset f d m n = apSum (fun k => f (k + m * d)) d n := by
  simpa using (apSumOffset_eq_apSum_shift_mul (f := f) (d := d) (m := m) (n := n))

-- Regression (Track B / canonical discrepancy view of offsets): same rewrite at the `discrepancy` level.
example : discOffset f d m n = discrepancy (fun k => f (k + m * d)) d n := by
  simpa using (discOffset_eq_discrepancy_shift_mul (f := f) (d := d) (m := m) (n := n))

-- Regression (Track B / degenerate tail normal forms):
-- `discOffset` at length 0 and 1 should simplify to explicit normal forms.
example : discOffset f d m 0 = 0 := by
  simp

example : discOffset f d m 1 = Int.natAbs (f ((m + 1) * d)) := by
  simp

-- Regression (Track B / discOffset invariances):
example : discOffset (fun k => -f k) d m n = discOffset f d m n := by
  simpa using (discOffset_neg (f := f) (d := d) (m := m) (n := n))

example : discOffset (fun k => f (k + a * d)) d m n = discOffset f d (m + a) n := by
  simpa using (discOffset_shift_add_mul (f := f) (a := a) (d := d) (m := m) (n := n))

-- Regression (Track B / discOffset periodicity normal form):
-- If `f` is periodic with period `p` and `p ∣ d`, then `discOffset f d m n` is independent of `m`.
example (hp : Function.Periodic f p) (hd : p ∣ d) :
    discOffset f d m n = discOffset f d 0 n := by
  simpa using (discOffset_periodic_of_dvd_step (f := f) (p := p) hp (d := d) hd (m := m) (n := n))

-- Regression (Track B / simp-first pipeline hygiene): importing `DiscSimp` should let `simp`
-- normalize start-index shifts into a translated summand.
example : apSumOffset f d (m + k) n = apSumOffset (fun t => f (t + k * d)) d m n := by
  simp

example : discOffset f d (m + k) n = discOffset (fun t => f (t + k * d)) d m n := by
  simpa using (discOffset_shift_start_add (f := f) (d := d) (m := m) (k := k) (n := n))

-- Regression (Track B / step-one normalization, discOffset):
-- push the step size into the summand.
example : discOffset f d m n = discOffset (fun k => f (k * d)) 1 m n := by
  simpa using (discOffset_eq_discOffset_step_one (f := f) (d := d) (m := m) (n := n))

-- Regression (Track B / step-one normalization, discOffset / mul_left-friendly):
example : discOffset f d m n = discOffset (fun k => f (d * k)) 1 m n := by
  simpa using (discOffset_eq_discOffset_step_one_mul_left (f := f) (d := d) (m := m) (n := n))

-- Regression (Track B / step-factor coherence, discOffset):
-- normalize a product step size `d*k` by pushing `d` into the summand.
example : discOffset f (d * k) m n = discOffset (fun x => f (x * d)) k m n := by
  simpa using
    (discOffset_mul_eq_discOffset_map_mul (f := f) (d := d) (k := k) (m := m) (n := n))

-- Regression (Track B / step-factor coherence, discOffset / mul_left-friendly):
example : discOffset f (d * k) m n = discOffset (fun x => f (d * x)) k m n := by
  simpa using
    (discOffset_mul_eq_discOffset_map_mul_left (f := f) (d₁ := d) (d₂ := k) (m := m) (n := n))

-- Regression (Track B / residue reindexing infra): commute the quotient/residue nesting order.
example (q n' : ℕ) (hq : q > 0) :
    (Finset.range (q * n')).sum f =
      (Finset.range q).sum (fun r => (Finset.range n').sum (fun k => f (q * k + r))) := by
  simpa using
    (sum_range_mul_reindex_mod_div (q := q) (n := n') (hq := hq) (f := f))

-- Regression (Track B / residue-class split, homogeneous nucleus):
-- `apSum` at block length `q*(n+1)` rewrites into the nested residue/quotient normal form.
example (q : ℕ) (hq : q > 0) :
    apSum f d (q * (n + 1)) =
      (Finset.range q).sum (fun r =>
        (Finset.range (n + 1)).sum (fun k => f ((q * k + (r + 1)) * d))) := by
  simpa using
    (apSum_mul_len_succ_eq_sum_range_sum_range (f := f) (d := d) (q := q) (n := n) hq)

-- Regression (Track B / residue-class split, homogeneous nucleus / mul_left variant):
-- same normal form, but with the multiplication order normalized to `d * i`.
example (q : ℕ) (hq : q > 0) :
    apSum f d (q * (n + 1)) =
      (Finset.range q).sum (fun r =>
        (Finset.range (n + 1)).sum (fun k => f (d * (q * k + (r + 1))))) := by
  simpa using
    (apSum_mul_len_succ_eq_sum_range_sum_range_mul_left (f := f) (d := d) (q := q) (n := n) hq)

-- Regression (Track B / witness normal form): rewrite `HasDiscrepancyAtLeast` directly into the
-- `discOffset … 0 n` wrapper (avoid exposing `Int.natAbs (apSumOffset …)` downstream).
example : HasDiscrepancyAtLeast f C ↔ ∃ d n : ℕ, d > 0 ∧ discOffset f d 0 n > C := by
  simpa using (HasDiscrepancyAtLeast_iff_exists_discOffset_zero_start (f := f) (C := C))

-- Regression (Track B / unbounded witness normal form, along-`d`): shift-by-`m*d` unboundedness
-- rewrites to the pure `discOffset` ∀∃ normal form.
example :
    UnboundedDiscrepancyAlong (fun k => f (k + m * d)) d ↔
      (∀ C : ℕ, ∃ n : ℕ, C < discOffset f d m n) := by
  simpa using
    (UnboundedDiscrepancyAlong.shift_mul_iff_forall_exists_discOffset_lt (f := f) (d := d) (m := m))

-- Regression (Track B / witness normal form, along-`d`): unshifted along-`d` predicate
-- rewrites to the `discOffset … 0 n` witness form.
example : HasDiscrepancyAtLeastAlong f d C ↔ ∃ n : ℕ, C < discOffset f d 0 n := by
  simpa using (HasDiscrepancyAtLeastAlong.iff_exists_discOffset_zero_start_lt (f := f) (d := d) (C := C))

-- Regression (Track B / API coherence): the same witness form, but using the specialized
-- wrapper `discAlong`.
example : HasDiscrepancyAtLeastAlong f d C ↔ ∃ n : ℕ, C < discAlong f d n := by
  simpa using (HasDiscrepancyAtLeastAlong.iff_exists_discAlong_lt (f := f) (d := d) (C := C))

-- Regression (Track B / unbounded witness normal form, along-`d`): unshifted unboundedness
-- rewrites to the `discOffset … 0 n` ∀∃ normal form.
example : UnboundedDiscrepancyAlong f d ↔ (∀ C : ℕ, ∃ n : ℕ, C < discOffset f d 0 n) := by
  simpa using (UnboundedDiscrepancyAlong.iff_forall_exists_discOffset_zero_start_lt (f := f) (d := d))

-- Regression (Track B / local surgery at `discOffset` level):
-- if two sequences agree on `apSupport d m n`, then their offset discrepancies coincide.
example (g : ℕ → ℤ) (h : ∀ x ∈ apSupport d m n, f x = g x) :
    discOffset f d m n = discOffset g d m n := by
  simpa using (discOffset_congr_support (f := f) (g := g) (d := d) (m := m) (n := n) h)

-- Regression (Track B / local surgery at homogeneous `disc` level):
-- if two sequences agree on `apSupport d 0 n`, then their homogeneous discrepancies coincide.
example (g : ℕ → ℤ) (h : ∀ x ∈ apSupport d 0 n, f x = g x) :
    disc f d n = disc g d n := by
  simpa using (disc_congr_support (f := f) (g := g) (d := d) (n := n) h)

-- Regression (Track B / local surgery, range form):
-- pointwise agreement on the summation indices `i < n` suffices.
example (g : ℕ → ℤ)
    (h : ∀ i, i < n → f ((m + i + 1) * d) = g ((m + i + 1) * d)) :
    discOffset f d m n = discOffset g d m n := by
  simpa using (discOffset_congr (f := f) (g := g) (d := d) (m := m) (n := n) h)

-- Regression (Track B / translation invariance wrapper):
-- agreement on the affine tail indices `(m+i)*d` for `i ≤ n` suffices.
example (g : ℕ → ℤ)
    (h : ∀ i, i ≤ n → f ((m + i) * d) = g ((m + i) * d)) :
    discOffset f d m n = discOffset g d m n := by
  simpa using (discOffset_congr_le (f := f) (g := g) (d := d) (m := m) (n := n) h)

-- Regression (Track B / translation invariance wrapper, affine nucleus):
example (g : ℕ → ℤ)
    (h : ∀ i, i ≤ n → f (a + i * d) = g (a + i * d)) :
    apSumFrom f a d n = apSumFrom g a d n := by
  simpa using (apSumFrom_congr_le (f := f) (g := g) (a := a) (d := d) (n := n) h)

-- Regression (Track B / local surgery, range form via `Finset.range` membership):
example (g : ℕ → ℤ)
    (h : ∀ i, i ∈ Finset.range n → f ((m + i + 1) * d) = g ((m + i + 1) * d)) :
    discOffset f d m n = discOffset g d m n := by
  simpa using (discOffset_congr_range (f := f) (g := g) (d := d) (m := m) (n := n) h)

-- Regression (Track B / range-cut inequality): split `discOffset` at a cut length `k ≤ n`.
example (hk : k ≤ n) :
    discOffset f d m n ≤ discOffset f d m k + discOffset f d (m + k) (n - k) := by
  simpa using (discOffset_cut_le (f := f) (d := d) (m := m) (n := n) (k := k) hk)

-- Regression (Track B / step-factoring at a multiple start):
-- normalize `apSumFrom f (a*d) (k*d) n` directly into an `apSumOffset` on a shifted sequence.
example : apSumFrom f (a * d) (k * d) n = apSumOffset (fun t => f ((t + a) * d)) k 0 n := by
  simpa using
    (apSumFrom_mul_start_mul_step_eq_apSumOffset_shift_mul_right (f := f) (a₀ := a) (d₁ := k)
      (d₂ := d) (n := n))

-- Regression (Track B / Lipschitz-in-length): one-step extension for offset AP sums.
example : apSumOffset f d m (n + 1) = apSumOffset f d m n + f ((m + n + 1) * d) := by
  simpa using (apSumOffset_succ (f := f) (d := d) (m := m) (n := n))

-- Regression (Track B / API hygiene): the opt-in `DiscOffsetSimp` simp set should normalize
-- `Nat.succ` endpoints without manual rewriting.
example :
    Int.natAbs (apSumOffset f d m n + f ((m + Nat.succ n) * d)) = discOffset f d m (Nat.succ n) := by
  simp

example :
    Int.natAbs (apSum f d n + f ((Nat.succ n) * d)) = disc f d (Nat.succ n) := by
  simp

-- Regression (Track B / Lipschitz-in-length): one-step difference form.
example : apSumOffset f d m (n + 1) - apSumOffset f d m n = f ((m + n + 1) * d) := by
  simpa using (apSumOffset_succ_sub (f := f) (d := d) (m := m) (n := n))

-- Regression (Track B / Lipschitz-in-length): Lipschitz bound in `Int.natAbs` for sign sequences.
example (hf : IsSignSequence f) :
    Int.natAbs (apSumOffset f d m (n + 1)) ≤ Int.natAbs (apSumOffset f d m n) + 1 := by
  simpa using (IsSignSequence.natAbs_apSumOffset_succ_le (f := f) (hf := hf) (d := d) (m := m) (n := n))

-- Regression (Track B / discOffset Lipschitz bound): one-step inequality (triangle form).
example :
    discOffset f d m (n + 1) ≤ discOffset f d m n + Int.natAbs (f ((m + n + 1) * d)) := by
  simpa using (discOffset_succ_le_add_natAbs (f := f) (d := d) (m := m) (n := n))

-- Regression (Track B / discOffset Lipschitz bound): sign-sequence specialization.
example (hf : IsSignSequence f) :
    discOffset f d m (n + 1) ≤ discOffset f d m n + 1 := by
  simpa using
    (IsSignSequence.discOffset_succ_le (f := f) (hf := hf) (d := d) (m := m) (n := n))

-- Regression (Track B / discOffset Lipschitz bound): reverse inequality.
example (hf : IsSignSequence f) :
    discOffset f d m n ≤ discOffset f d m (n + 1) + 1 := by
  simpa using
    (IsSignSequence.discOffset_le_succ_add_one (f := f) (hf := hf) (d := d) (m := m) (n := n))

-- Regression (Track B / basic size bound for sign sequences): `discOffset` bound by length.
example (hf : IsSignSequence f) :
    discOffset f d m n ≤ n := by
  simpa using (discOffset_le (f := f) (hf := hf) (d := d) (m := m) (n := n))

-- Regression (Track B / basic size bound for sign sequences): `discAlong` bound by length.
example (hf : IsSignSequence f) :
    discAlong f d n ≤ n := by
  simpa using (discAlong_le (f := f) (hf := hf) (d := d) (n := n))

-- Regression: bounded discrepancy is stable under dilation (`n ↦ n*k`).
example (hb : BoundedDiscrepancy f) (hk : k > 0) :
    BoundedDiscrepancy (fun n => f (n * k)) := by
  simpa using (BoundedDiscrepancy.map_mul (f := f) hb (k := k) hk)

-- Regression (Track B / boundedness quantifier normal form, discOffset-native):
-- `BoundedDiscOffset` should rewrite to the explicit `∀ n, discOffset … ≤ B` form via a stable name.
example (B : ℕ) :
    BoundedDiscOffset f d m B ↔ ∀ n : ℕ, discOffset f d m n ≤ B := by
  simpa using (boundedDiscOffset_iff_forall_discOffset_le (f := f) (d := d) (m := m) (B := B))

-- Regression (Track B / unboundedness quantifier normal form, discOffset-native):
-- Negation-pushed form: `¬ ∃ B, BoundedDiscOffset … B` rewrites to `∀ B, ∃ n, B < discOffset … n`.
example :
    (¬ ∃ B : ℕ, BoundedDiscOffset f d m B) ↔ ∀ B : ℕ, ∃ n : ℕ, B < discOffset f d m n := by
  simpa using
    (not_exists_boundedDiscOffset_iff_forall_exists_discOffset_lt (f := f) (d := d) (m := m))

-- Regression (Track B / boundedness API hygiene): monotonicity in the bound parameter.
example (B B' : ℕ) (h : BoundedDiscOffset f d m B) (hBB' : B ≤ B') :
    BoundedDiscOffset f d m B' := by
  simpa using (BoundedDiscOffset.mono_B (f := f) (d := d) (m := m) (B := B) (B' := B') h hBB')

-- Regression (Track B / boundedness API hygiene): shift-to-`m = 0` transport.
example (B : ℕ) (h : BoundedDiscOffset f d m B) :
    BoundedDiscOffset (fun k => f (k + m * d)) d 0 B := by
  simpa using (BoundedDiscOffset.map_shift_add (f := f) (d := d) (m := m) (B := B) h)

-- Regression (Track B / boundedness API hygiene): inverse shift transport.
example (B : ℕ) (h : BoundedDiscOffset (fun k => f (k + m * d)) d 0 B) :
    BoundedDiscOffset f d m B := by
  simpa using (BoundedDiscOffset.of_map_shift_add (f := f) (d := d) (m := m) (B := B) h)

-- Regression (Track B / boundedness API hygiene): shift-start transport.
example (B : ℕ) (h : BoundedDiscOffset f d (m + k) B) :
    BoundedDiscOffset (fun t => f (t + k * d)) d m B := by
  simpa using
    (BoundedDiscOffset.map_shift_start_add (f := f) (d := d) (m := m) (k := k) (B := B) h)

example (B : ℕ) (h : BoundedDiscOffset (fun t => f (t + k * d)) d m B) :
    BoundedDiscOffset f d (m + k) B := by
  simpa using
    (BoundedDiscOffset.of_map_shift_start_add (f := f) (d := d) (m := m) (k := k) (B := B) h)

-- Regression (Track B / boundedness API hygiene): step-one transport.
example (B : ℕ) (h : BoundedDiscOffset f d m B) :
    BoundedDiscOffset (fun k => f (k * d)) 1 m B := by
  simpa using
    (BoundedDiscOffset.map_step_one (f := f) (d := d) (m := m) (B := B) h)

example (B : ℕ) (h : BoundedDiscOffset (fun k => f (k * d)) 1 m B) :
    BoundedDiscOffset f d m B := by
  simpa using
    (BoundedDiscOffset.of_map_step_one (f := f) (d := d) (m := m) (B := B) h)

-- Regression (Track B / boundedness API hygiene): step-factor transport.
example (B : ℕ) (h : BoundedDiscOffset f (d * k) m B) :
    BoundedDiscOffset (fun x => f (x * d)) k m B := by
  simpa using
    (BoundedDiscOffset.map_mul (f := f) (d := d) (k := k) (m := m) (B := B) h)

example (B : ℕ) (h : BoundedDiscOffset (fun x => f (x * d)) k m B) :
    BoundedDiscOffset f (d * k) m B := by
  simpa using
    (BoundedDiscOffset.of_map_mul (f := f) (d := d) (k := k) (m := m) (B := B) h)

-- Regression (Track B / boundedness API hygiene): finite-length along-`d` boundedness
-- rewrites to the explicit `∀ n ≤ len, discAlong … ≤ B` form via a stable name.
example (len B : ℕ) :
    BoundedDiscrepancyAlong f d len B ↔ ∀ n : ℕ, n ≤ len → discAlong f d n ≤ B := by
  simpa using
    (boundedDiscrepancyAlong_iff_forall_le_discAlong_le (f := f) (d := d) (len := len) (B := B))

-- Regression (Track B / boundedness API hygiene): monotonicity in the bound parameter (finite-length along-`d`).
example (len B B' : ℕ) (h : BoundedDiscrepancyAlong f d len B) (hBB' : B ≤ B') :
    BoundedDiscrepancyAlong f d len B' := by
  simpa using (BoundedDiscrepancyAlong.mono_B (f := f) (d := d) (len := len) (B := B) (B' := B') h hBB')

-- Regression (Track B / boundedness API hygiene): monotonicity in the length parameter (finite-length along-`d`).
example (len len' B : ℕ) (h : BoundedDiscrepancyAlong f d len' B) (hlen : len ≤ len') :
    BoundedDiscrepancyAlong f d len B := by
  simpa using (BoundedDiscrepancyAlong.mono_len (f := f) (d := d) (len := len) (len' := len') (B := B) h hlen)

-- Regression (Track B / boundedness API hygiene): promote offset-boundedness to finite-length
-- along-`d` boundedness on the shifted sequence.
example (len B : ℕ) (h : BoundedDiscOffset f d m B) :
    BoundedDiscrepancyAlong (fun k => f (k + m * d)) d len B := by
  simpa using (BoundedDiscOffset.toBoundedDiscrepancyAlong_shift_add (f := f) (d := d) (m := m) (B := B) len h)

-- Regression (Track B / boundedness API hygiene): unpack finite-length along-`d` boundedness on the shifted
-- sequence into the corresponding `discOffset` inequality up to `len`.
example (len B : ℕ) (h : BoundedDiscrepancyAlong (fun k => f (k + m * d)) d len B) :
    ∀ n : ℕ, n ≤ len → discOffset f d m n ≤ B := by
  simpa using
    (BoundedDiscrepancyAlong.to_forall_le_discOffset_le_shift_add (f := f) (d := d) (m := m) (len := len) (B := B) h)

-- Regression: parity split normal form for even-length homogeneous AP sums.
example :
    apSum f d (2 * (n + 1)) = apSum f (2 * d) (n + 1) + f d + apSumFrom f d (2 * d) n := by
  simpa using (apSum_two_mul_len_succ (f := f) (d := d) (n := n))

-- Regression: residue-class split normal form (paper-friendly `i*d` summand convention).
example (q : ℕ) (hq : q > 0) :
    apSum f d (q * (n + 1)) =
      (Finset.range q).sum (fun r => f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n) := by
  simpa using
    (apSum_mul_len_succ_eq_sum_range (f := f) (d := d) (q := q) (n := n) hq)

-- Regression: residue-class split normal form (multiplication-on-the-left summand convention).
example (q : ℕ) (hq : q > 0) :
    apSum f d (q * (n + 1)) =
      (Finset.range q).sum (fun r => f (d * (r + 1)) + apSumFrom f (d * (r + 1)) (q * d) n) := by
  simpa using
    (apSum_mul_len_succ_eq_sum_range_mul_left (f := f) (d := d) (q := q) (n := n) hq)

-- Regression: residue-class split normal form for offset sums (multiplication-on-the-left summand convention).
example (q : ℕ) (hq : q > 0) :
    apSumOffset f d m (q * (n + 1)) =
      (Finset.range q).sum (fun r => f (d * (m + r + 1)) + apSumFrom f (d * (m + r + 1)) (q * d) n) := by
  simpa using
    (apSumOffset_mul_len_succ_eq_sum_range_mul_left (f := f) (d := d) (m := m) (q := q) (n := n) hq)

-- Regression (Track B / residue-class split, offset discrepancy): paper-friendly `i*d` summand convention.
example (q : ℕ) (hq : q > 0) :
    discOffset f d m (q * (n + 1)) =
      Int.natAbs ((Finset.range q).sum (fun r =>
        f ((m + r + 1) * d) + apSumFrom f ((m + r + 1) * d) (q * d) n)) := by
  simpa using
    (discOffset_mul_len_succ_eq_natAbs_sum_range (f := f) (d := d) (m := m) (q := q) (n := n) hq)

-- Regression (Track B / residue-class split, offset discrepancy): multiplication-on-the-left summand convention.
example (q : ℕ) (hq : q > 0) :
    discOffset f d m (q * (n + 1)) =
      Int.natAbs ((Finset.range q).sum (fun r =>
        f (d * (m + r + 1)) + apSumFrom f (d * (m + r + 1)) (q * d) n)) := by
  simpa using
    (discOffset_mul_len_succ_eq_natAbs_sum_range_mul_left (f := f) (d := d) (m := m) (q := q) (n := n) hq)

-- Regression (Track B / reindex-by-residue infrastructure):
-- raw `Finset.range` reindexing lemma packaged via `div`/`mod`.
example (q : ℕ) (hq : q > 0) :
    (Finset.range (q * n)).sum (fun i => f i) =
      (Finset.range n).sum (fun k => (Finset.range q).sum (fun r => f (q * k + r))) := by
  simpa using (sum_range_mul_reindex_div_mod (q := q) (n := n) hq (f := f))

/-!
## Typical “user script” examples

These are meant to look like what someone does after reading a paper statement:
start from an `Icc` sum / difference of partial sums, then normalize into the stable-surface
`apSumOffset`/`discOffset` wrappers with a small `simp`/`rw` pipeline.
-/

-- Tiny one-line pipelines (intended “typical user scripts”).

-- Paper tail sum bound → `discOffset` bound.
example
    (h : Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) ≤ C) :
    discOffset f d m n ≤ C := by
  simpa using h

/-!
### NEW (Track B): paper `Icc` statements → `discOffset` normal form → split/bound

These are intentionally “paper-shaped” and *do not* mention
`Int.natAbs (apSumOffset ...)` as an intermediate normal form.
-/

-- 1) Direct normalization from a paper `Icc` inequality.
example
    (h : Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) ≤ C) :
    discOffset f d m n ≤ C := by
  -- `simp` turns the `Icc` sum into `discOffset` via `apSumOffset_eq_sum_Icc`.
  simpa [discOffset, apSumOffset_eq_sum_Icc] using h

-- 2) Split/bound a single paper interval into two consecutive tails.
example (n₁ n₂ : ℕ) :
    Int.natAbs ((Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d))) ≤
      discOffset f d m n₁ + discOffset f d (m + n₁) n₂ := by
  have hmk : m ≤ m + n₁ := Nat.le_add_right _ _
  have hkn : m + n₁ ≤ m + (n₁ + n₂) := by
    exact Nat.add_le_add_left (Nat.le_add_right n₁ n₂) m
  -- Normalize LHS to `discOffset` and apply the stable-surface split lemma.
  simpa [discOffset, apSumOffset_eq_sum_Icc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (discOffset_split_at_le (f := f) (d := d) (m := m) (k := m + n₁) (n := n₁ + n₂) hmk hkn)

-- 3) Combine two paper bounds into a bound on the concatenated interval.
example (n₁ n₂ C₁ C₂ : ℕ)
    (h₁ : Int.natAbs ((Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d))) ≤ C₁)
    (h₂ : Int.natAbs ((Finset.Icc (m + n₁ + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d))) ≤ C₂) :
    Int.natAbs ((Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d))) ≤ C₁ + C₂ := by
  have h₁' : discOffset f d m n₁ ≤ C₁ := by
    simpa [discOffset, apSumOffset_eq_sum_Icc] using h₁
  have h₂' : discOffset f d (m + n₁) n₂ ≤ C₂ := by
    simpa [discOffset, apSumOffset_eq_sum_Icc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h₂
  have hmk : m ≤ m + n₁ := Nat.le_add_right _ _
  have hkn : m + n₁ ≤ m + (n₁ + n₂) := by
    exact Nat.add_le_add_left (Nat.le_add_right n₁ n₂) m
  have hsplit : discOffset f d m (n₁ + n₂) ≤ discOffset f d m n₁ + discOffset f d (m + n₁) n₂ := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (discOffset_split_at_le (f := f) (d := d) (m := m) (k := m + n₁) (n := n₁ + n₂) hmk hkn)
  have : discOffset f d m (n₁ + n₂) ≤ C₁ + C₂ :=
    le_trans hsplit (Nat.add_le_add h₁' h₂')
  -- Return to a paper `Icc` inequality.
  simpa [discOffset, apSumOffset_eq_sum_Icc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

-- 3a) Three-way split/bound: paper `Icc` tail → normalize to `discOffset` → split twice.
example (n₁ n₂ n₃ : ℕ) :
    Int.natAbs ((Finset.Icc (m + 1) (m + (n₁ + n₂ + n₃))).sum (fun i => f (i * d))) ≤
      discOffset f d m n₁ + discOffset f d (m + n₁) n₂ + discOffset f d (m + n₁ + n₂) n₃ := by
  have hmk : m ≤ m + n₁ := Nat.le_add_right _ _
  have hkn : m + n₁ ≤ m + (n₁ + n₂ + n₃) := by
    exact Nat.add_le_add_left (Nat.le_add_right n₁ (n₂ + n₃)) m
  have hsplit₁ : discOffset f d m (n₁ + (n₂ + n₃)) ≤ discOffset f d m n₁ + discOffset f d (m + n₁) (n₂ + n₃) := by
    simpa [Nat.add_assoc] using
      (discOffset_split_at_le (f := f) (d := d) (m := m) (k := m + n₁) (n := n₁ + (n₂ + n₃)) hmk hkn)
  have hmk' : m + n₁ ≤ m + n₁ + n₂ := Nat.le_add_right _ _
  have hkn' : m + n₁ + n₂ ≤ m + n₁ + (n₂ + n₃) := by
    simpa [Nat.add_assoc] using Nat.add_le_add_left (Nat.le_add_right n₂ n₃) (m + n₁)
  have hsplit₂ : discOffset f d (m + n₁) (n₂ + n₃) ≤ discOffset f d (m + n₁) n₂ + discOffset f d (m + n₁ + n₂) n₃ := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (discOffset_split_at_le (f := f) (d := d) (m := m + n₁) (k := m + n₁ + n₂) (n := n₂ + n₃) hmk' hkn')
  have h : discOffset f d m (n₁ + n₂ + n₃) ≤
      discOffset f d m n₁ + discOffset f d (m + n₁) n₂ + discOffset f d (m + n₁ + n₂) n₃ := by
    -- Combine the two split inequalities.
    have : discOffset f d m (n₁ + (n₂ + n₃)) ≤
        discOffset f d m n₁ + (discOffset f d (m + n₁) n₂ + discOffset f d (m + n₁ + n₂) n₃) := by
      refine le_trans hsplit₁ ?_
      -- bound the second summand via the second split.
      exact Nat.add_le_add_left hsplit₂ _
    -- Reassociate the RHS.
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
  simpa [discOffset, apSumOffset_eq_sum_Icc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

-- 3b) Paper `Icc` bound + pointwise `|f| ≤ B` bound → split, then bound the second piece by `n₂ * B`.
example {B : ℕ} (n₁ n₂ C₁ : ℕ)
    (h₁ : Int.natAbs ((Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d))) ≤ C₁)
    (hf : ∀ k, Int.natAbs (f k) ≤ B) :
    Int.natAbs ((Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d))) ≤ C₁ + n₂ * B := by
  have h₁' : discOffset f d m n₁ ≤ C₁ := by
    simpa [discOffset, apSumOffset_eq_sum_Icc] using h₁
  have htail : discOffset f d (m + n₁) n₂ ≤ n₂ * B := by
    simpa using
      (discOffset_le_mul_of_natAbs_le (f := f) (B := B) (hf := hf) (d := d) (m := m + n₁) (n := n₂))
  have hmk : m ≤ m + n₁ := Nat.le_add_right _ _
  have hkn : m + n₁ ≤ m + (n₁ + n₂) := by
    exact Nat.add_le_add_left (Nat.le_add_right n₁ n₂) m
  have hsplit : discOffset f d m (n₁ + n₂) ≤ discOffset f d m n₁ + discOffset f d (m + n₁) n₂ := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (discOffset_split_at_le (f := f) (d := d) (m := m) (k := m + n₁) (n := n₁ + n₂) hmk hkn)
  have : discOffset f d m (n₁ + n₂) ≤ C₁ + n₂ * B := by
    exact le_trans hsplit (Nat.add_le_add h₁' htail)
  simpa [discOffset, apSumOffset_eq_sum_Icc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

-- 3c) Pure compile-only: normalize a paper `Icc` tail into `discOffset` at a shifted start.
example (hmn : m ≤ n) :
    Int.natAbs ((Finset.Icc (m + 1) (m + (n - m))).sum (fun i => f (i * d))) =
      discOffset f d m (n - m) := by
  -- Here the endpoint `m + (n - m)` is definitionally the “length-(n-m)” tail endpoint.
  simp [discOffset, apSumOffset_eq_sum_Icc, Nat.add_sub_of_le hmn]

-- 4) Homogeneous variant (`m = 0`): normalize a paper `Icc 1 (n₁+n₂)` sum to `disc`, then split.
example (n₁ n₂ : ℕ) :
    Int.natAbs ((Finset.Icc 1 (n₁ + n₂)).sum (fun i => f (i * d))) ≤
      disc f d n₁ + discOffset f d n₁ n₂ := by
  -- Normalize the paper `Icc` sum into `disc`, then use the stable-surface length split bound.
  simpa [disc, apSum_eq_sum_Icc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (disc_add_le (f := f) (d := d) (n₁ := n₁) (n₂ := n₂))

-- 5) Same split, but keep everything in paper `Icc` notation on both sides.
example (n₁ n₂ : ℕ) :
    Int.natAbs ((Finset.Icc 1 (n₁ + n₂)).sum (fun i => f (i * d))) ≤
      Int.natAbs ((Finset.Icc 1 n₁).sum (fun i => f (i * d))) + discOffset f d n₁ n₂ := by
  -- `disc f d n₁` is definitionaly `|apSum f d n₁|`, and `apSum` is the `Icc` sum.
  simpa [disc, apSum_eq_sum_Icc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (disc_add_le (f := f) (d := d) (n₁ := n₁) (n₂ := n₂))

-- 6) Combine two paper bounds to bound a concatenated homogeneous interval.
example (n₁ n₂ C₁ C₂ : ℕ)
    (h₁ : Int.natAbs ((Finset.Icc 1 n₁).sum (fun i => f (i * d))) ≤ C₁)
    (h₂ : discOffset f d n₁ n₂ ≤ C₂) :
    Int.natAbs ((Finset.Icc 1 (n₁ + n₂)).sum (fun i => f (i * d))) ≤ C₁ + C₂ := by
  have hsplit :
      disc f d (n₁ + n₂) ≤ disc f d n₁ + discOffset f d n₁ n₂ := by
    simpa using (disc_add_le (f := f) (d := d) (n₁ := n₁) (n₂ := n₂))
  have h₁' : disc f d n₁ ≤ C₁ := by
    simpa [disc, apSum_eq_sum_Icc] using h₁
  have : disc f d (n₁ + n₂) ≤ C₁ + C₂ :=
    le_trans hsplit (Nat.add_le_add h₁' h₂)
  simpa [disc, apSum_eq_sum_Icc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

-- Compile-only regression (Track B / paper `Icc` → `discOffset`):
-- normalize to the stable-surface wrapper (not `Int.natAbs (apSumOffset ...)`).
example :
    Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) = discOffset f d m n := by
  simp [discOffset, apSumOffset_eq_sum_Icc]

-- Compile-only regression (Track B / paper `Icc` → `discOffset`, then one-step bound).
example (hf : IsSignSequence f) :
    Int.natAbs ((Finset.Icc (m + 1) (m + (n + 1))).sum (fun i => f (i * d))) ≤
      discOffset f d m n + 1 := by
  -- Normalize the paper statement into `discOffset` at length `n+1`, then apply the stable-surface
  -- Lipschitz bound for sign sequences.
  simpa [discOffset, apSumOffset_eq_sum_Icc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (IsSignSequence.discOffset_succ_le (f := f) (hf := hf) (d := d) (m := m) (n := n))

-- Compile-only regression (Track B / paper `Icc` → `discOffset`, split at an interior cut).
example (n₁ n₂ : ℕ) :
    Int.natAbs ((Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d))) ≤
      discOffset f d m n₁ + discOffset f d (m + n₁) n₂ := by
  have hmk : m ≤ m + n₁ := Nat.le_add_right _ _
  have hkn : m + n₁ ≤ m + (n₁ + n₂) := by
    exact Nat.add_le_add_left (Nat.le_add_right n₁ n₂) m
  -- Normalize the paper `Icc` sum into `discOffset`, then use the stable-surface split lemma.
  simpa [discOffset, apSumOffset_eq_sum_Icc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (discOffset_split_at_le (f := f) (d := d) (m := m) (k := m + n₁) (n := n₁ + n₂) hmk hkn)

-- Regression (Track B / paper-to-stable-surface):
-- `discOffset` is exactly the paper-style `Icc` tail sum in disguise.
example :
    discOffset f d m n = Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) := by
  -- `discOffset` is `Int.natAbs (apSumOffset ...)`, and `apSumOffset` is the `Icc` tail sum.
  simp [discOffset, apSumOffset_eq_sum_Icc]

-- Regression (Track B / paper `Icc` → `discOffset` (no `Int.natAbs (apSumOffset ...)`), then split/bound).
example (n₁ n₂ : ℕ) :
    Int.natAbs ((Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d))) ≤
      discOffset f d m n₁ + discOffset f d (m + n₁) n₂ := by
  have hmk : m ≤ m + n₁ := Nat.le_add_right _ _
  have hkn : m + n₁ ≤ m + (n₁ + n₂) := by
    exact Nat.add_le_add_left (Nat.le_add_right n₁ n₂) m
  -- Split the tail at `k = m+n₁`, then normalize the LHS back into paper `Icc` form.
  simpa [discOffset, apSumOffset_eq_sum_Icc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (discOffset_split_at_le (f := f) (d := d) (m := m) (k := m + n₁) (n := n₁ + n₂) hmk hkn)

-- Regression (Track B / paper `Icc` → `discOffset` → split/bound → return to paper `Icc` statement).
example (n₁ n₂ C₁ C₂ : ℕ)
    (h₁ : Int.natAbs ((Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d))) ≤ C₁)
    (h₂ : Int.natAbs ((Finset.Icc (m + n₁ + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d))) ≤ C₂) :
    Int.natAbs ((Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d))) ≤ C₁ + C₂ := by
  have h₁' : discOffset f d m n₁ ≤ C₁ := by
    simpa using h₁
  have h₂' : discOffset f d (m + n₁) n₂ ≤ C₂ := by
    -- Normalize the second paper interval; note `m + n₁ + n₂ = m + (n₁ + n₂)`.
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h₂
  have hmk : m ≤ m + n₁ := Nat.le_add_right _ _
  have hkn : m + n₁ ≤ m + (n₁ + n₂) := by
    exact Nat.add_le_add_left (Nat.le_add_right n₁ n₂) m
  have hsplit :
      discOffset f d m (n₁ + n₂) ≤ discOffset f d m n₁ + discOffset f d (m + n₁) n₂ := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (discOffset_split_at_le (f := f) (d := d) (m := m) (k := m + n₁) (n := n₁ + n₂) hmk hkn)
  have : discOffset f d m (n₁ + n₂) ≤ C₁ + C₂ :=
    le_trans hsplit (Nat.add_le_add h₁' h₂')
  -- Return to the paper `Icc` tail sum statement.
  simpa [discOffset, apSumOffset_eq_sum_Icc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

-- Paper `Icc` tail (length `n₁+n₂`) → normalize to `discOffset`, then split/bound at an interior cut.
--
-- This is the shape that shows up constantly in papers: a single interval sum, then you want to
-- split it into two consecutive tails.
example (n₁ n₂ : ℕ) :
    Int.natAbs ((Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d))) ≤
      discOffset f d m n₁ + discOffset f d (m + n₁) n₂ := by
  have hsum :
      (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d)) = apSumOffset f d m (n₁ + n₂) := by
    -- Route through the stable-surface lemma that splits the paper interval into two tails;
    -- set the second length to 0 so the split collapses to a single `apSumOffset`.
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (sum_Icc_add_len_eq_apSumOffset_add (f := f) (d := d) (m := m) (n₁ := n₁ + n₂) (n₂ := 0))
  have hsplit :
      discOffset f d m (n₁ + n₂) ≤ discOffset f d m n₁ + discOffset f d (m + n₁) n₂ := by
    have hmk : m ≤ m + n₁ := Nat.le_add_right _ _
    have hkn : m + n₁ ≤ m + (n₁ + n₂) := by
      exact Nat.add_le_add_left (Nat.le_add_right n₁ n₂) m
    -- Split the tail at `k = m+n₁`.
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (discOffset_split_at_le (f := f) (d := d) (m := m) (k := m + n₁) (n := n₁ + n₂) hmk hkn)
  -- Normalize the paper `Icc` statement to the stable-surface `discOffset` wrapper.
  simpa [discOffset, hsum] using hsplit

-- Paper `Icc` tail split: if both pieces are bounded, then the concatenation is bounded.
-- (This is the “paper statement → normalize to `discOffset` → split/bound” pipeline.)
example (n₁ n₂ C₁ C₂ : ℕ)
    (h₁ : Int.natAbs ((Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d))) ≤ C₁)
    (h₂ : Int.natAbs ((Finset.Icc (m + n₁ + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d))) ≤ C₂) :
    discOffset f d m (n₁ + n₂) ≤ C₁ + C₂ := by
  have h₁' : discOffset f d m n₁ ≤ C₁ := by
    simpa using h₁
  have h₂' : discOffset f d (m + n₁) n₂ ≤ C₂ := by
    -- Normalize the second paper interval; note `m + n₁ + n₂ = m + (n₁ + n₂)`.
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h₂
  have hsplit :
      discOffset f d m (n₁ + n₂) ≤ discOffset f d m n₁ + discOffset f d (m + n₁) n₂ := by
    have hmk : m ≤ m + n₁ := Nat.le_add_right _ _
    have hkn : m + n₁ ≤ m + (n₁ + n₂) := by
      exact Nat.add_le_add_left (Nat.le_add_right n₁ n₂) m
    -- Split the tail at `k = m+n₁`.
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (discOffset_split_at_le (f := f) (d := d) (m := m) (k := m + n₁) (n := n₁ + n₂) hmk hkn)
  exact le_trans hsplit (Nat.add_le_add h₁' h₂')

-- Same split, but bound the second piece crudely by `n₂*B` from a pointwise `|f| ≤ B` bound.
example {B : ℕ} (n₁ n₂ C₁ : ℕ)
    (h₁ : Int.natAbs ((Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d))) ≤ C₁)
    (hf : ∀ k, Int.natAbs (f k) ≤ B) :
    discOffset f d m (n₁ + n₂) ≤ C₁ + n₂ * B := by
  have h₁' : discOffset f d m n₁ ≤ C₁ := by
    simpa using h₁
  have h₂' : discOffset f d (m + n₁) n₂ ≤ n₂ * B := by
    simpa using
      (discOffset_le_mul_of_natAbs_le (f := f) (B := B) (hf := hf) (d := d) (m := m + n₁) (n := n₂))
  have hsplit :
      discOffset f d m (n₁ + n₂) ≤ discOffset f d m n₁ + discOffset f d (m + n₁) n₂ := by
    have hmk : m ≤ m + n₁ := Nat.le_add_right _ _
    have hkn : m + n₁ ≤ m + (n₁ + n₂) := by
      exact Nat.add_le_add_left (Nat.le_add_right n₁ n₂) m
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (discOffset_split_at_le (f := f) (d := d) (m := m) (k := m + n₁) (n := n₁ + n₂) hmk hkn)
  have : discOffset f d m (n₁ + n₂) ≤ C₁ + n₂ * B := by
    exact le_trans hsplit (Nat.add_le_add h₁' h₂')
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

-- Paper `Icc` tail → normalize to `discOffset`, then apply a crude `n*B` bound.
example {B : ℕ} (hf : ∀ k, Int.natAbs (f k) ≤ B) :
    Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) ≤ n * B := by
  have hsum :
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) = apSumOffset f d m n := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (sum_Icc_add_len_eq_apSumOffset_add (f := f) (d := d) (m := m) (n₁ := n) (n₂ := 0))
  have hbound : discOffset f d m n ≤ n * B := by
    simpa using
      (discOffset_le_mul_of_natAbs_le (f := f) (B := B) (hf := hf) (d := d) (m := m) (n := n))
  simpa [discOffset, hsum] using hbound

-- Paper `Icc` tail → normalize to `discOffset`, then split and bound the second piece by `n₂*B`.
example {B : ℕ} (n₁ n₂ : ℕ) (hf : ∀ k, Int.natAbs (f k) ≤ B) :
    Int.natAbs ((Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d))) ≤
      discOffset f d m n₁ + n₂ * B := by
  have hsum :
      (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d)) = apSumOffset f d m (n₁ + n₂) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (sum_Icc_add_len_eq_apSumOffset_add (f := f) (d := d) (m := m) (n₁ := n₁ + n₂) (n₂ := 0))
  have hsplit :
      discOffset f d m (n₁ + n₂) ≤ discOffset f d m n₁ + discOffset f d (m + n₁) n₂ := by
    have hmk : m ≤ m + n₁ := Nat.le_add_right _ _
    have hkn : m + n₁ ≤ m + (n₁ + n₂) := by
      exact Nat.add_le_add_left (Nat.le_add_right n₁ n₂) m
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (discOffset_split_at_le (f := f) (d := d) (m := m) (k := m + n₁) (n := n₁ + n₂) hmk hkn)
  have htail : discOffset f d (m + n₁) n₂ ≤ n₂ * B := by
    simpa using
      (discOffset_le_mul_of_natAbs_le (f := f) (B := B) (hf := hf) (d := d) (m := m + n₁) (n := n₂))
  have : discOffset f d m (n₁ + n₂) ≤ discOffset f d m n₁ + n₂ * B := by
    -- Combine split + crude bound on the second piece.
    exact le_trans hsplit (Nat.add_le_add_left htail _)
  simpa [discOffset, hsum] using this

-- Paper affine tail with variable endpoint (`m ≤ n`) → `discOffset` in `apSumOffset` normal form.
example (hmn : m ≤ n)
    (h : Int.natAbs ((Finset.Icc (m + 1) n).sum (fun i => f (a + i * d))) ≤ C) :
    discOffset (fun k => f (a + k)) d m (n - m) ≤ C := by
  simpa [discOffset,
    sum_Icc_eq_apSumOffset_of_le_affineEndpoints (f := f) (a := a) (d := d) (m := m) (n := n) hmn] using h

-- Paper difference of affine partial sums (`m ≤ n`) → `discOffset` on a shifted sequence (single `simpa`).
example (hmn : m ≤ n)
    (h : Int.natAbs (apSumFrom f a d n - apSumFrom f a d m) ≤ C) :
    discOffset (fun k => f (k + a)) d m (n - m) ≤ C := by
  simpa [discOffset,
    apSumFrom_sub_apSumFrom_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n) hmn] using h

-- Paper tail sum with affine endpoints (`m ≤ n`) → normalize to an `apSumOffset` nucleus statement.
-- (I.e. strip away the paper `Icc` and expose the canonical tail-sum wrapper.)
example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (a + i * d)) =
      apSumOffset (fun k => f (a + k)) d m (n - m) := by
  simpa using
    (sum_Icc_eq_apSumOffset_of_le_affineEndpoints (f := f) (a := a) (d := d) (m := m) (n := n) hmn)

-- Paper difference of two affine-endpoint tails → normalize to a later tail in `apSumOffset` normal form.
example (hmn : m ≤ n) (hmn₁ : m + n₁ ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (a + i * d)) -
        (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (a + i * d)) =
      apSumOffset (fun k => f (a + k)) d (m + n₁) (n - m - n₁) := by
  have hn₁ : n₁ ≤ n - m :=
    Nat.le_sub_of_add_le hmn₁
  -- Rewrite both paper tails to `apSumOffset`, then normalize the difference.
  simpa [
    sum_Icc_eq_apSumOffset_of_le_affineEndpoints (f := f) (a := a) (d := d) (m := m) (n := n) hmn,
    sum_Icc_eq_apSumOffset_of_le_affineEndpoints (f := f) (a := a) (d := d) (m := m) (n := m + n₁)
      (Nat.le_add_right m n₁),
    apSumOffset_sub_apSumOffset_eq_apSumOffset (f := fun k => f (a + k)) (d := d) (m := m)
      (n₁ := n₁) (n₂ := n - m) hn₁,
    Nat.sub_eq
  ]
  using
    (apSumOffset_sub_apSumOffset_eq_apSumOffset (f := fun k => f (a + k)) (d := d) (m := m)
      (n₁ := n₁) (n₂ := n - m) hn₁)

-- Same normalization as above, but keep the `discOffset` wrapper (single `simpa` pipeline).
example (hmn : m ≤ n) (hmn₁ : m + n₁ ≤ n)
    (h :
        Int.natAbs
            ((Finset.Icc (m + 1) n).sum (fun i => f (a + i * d)) -
              (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (a + i * d))) ≤
          C) :
    discOffset (fun k => f (a + k)) d (m + n₁) (n - m - n₁) ≤ C := by
  have hn₁ : n₁ ≤ n - m :=
    Nat.le_sub_of_add_le hmn₁
  simpa [discOffset,
    sum_Icc_eq_apSumOffset_of_le_affineEndpoints (f := f) (a := a) (d := d) (m := m) (n := n) hmn,
    sum_Icc_eq_apSumOffset_of_le_affineEndpoints (f := f) (a := a) (d := d) (m := m) (n := m + n₁)
      (Nat.le_add_right m n₁),
    apSumOffset_sub_apSumOffset_eq_apSumOffset (f := fun k => f (a + k)) (d := d) (m := m)
      (n₁ := n₁) (n₂ := n - m) hn₁
  ] using h

-- Paper tail sum with affine endpoints (`m ≤ n`) → normalize to the shifted-sequence `discOffset` view.
--
-- This is a very typical "paper statement": a tail interval `Icc (m+1) n` with an affine summand.
example (hmn : m ≤ n)
    (h : Int.natAbs ((Finset.Icc (m + 1) n).sum (fun i => f (a + i * d))) ≤ C) :
    discOffset (fun k => f (k + a)) d m (n - m) ≤ C := by
  -- Paper tail → affine-tail nucleus → offset-sum on the shifted sequence.
  simpa [discOffset,
    sum_Icc_eq_apSumFrom_tail_of_le (f := f) (a := a) (d := d) (m := m) (n := n) hmn,
    apSumFrom_tail_eq_apSumOffset_shift_add] using h

-- Paper difference of affine partial sums (`m ≤ n`) → normalize into an offset tail on the shifted sequence.
example (hmn : m ≤ n)
    (h : Int.natAbs (apSumFrom f a d n - apSumFrom f a d m) ≤ C) :
    discOffset (fun k => f (k + a)) d m (n - m) ≤ C := by
  simpa [discOffset,
    apSumFrom_sub_apSumFrom_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)
      hmn] using h

-- Paper difference of *paper* affine tail sums → normalize to a later tail (`tail-of-tail` normal form).
example
    (h :
        Int.natAbs
            (((Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (a + i * d))) -
              (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (a + i * d))) ≤
          C) :
    discOffset (fun k => f (k + a)) d (m + n₁) n₂ ≤ C := by
  -- Paper tails → affine-tail nucleus (`apSumFrom`), then difference → offset tail on shifted sequence.
  simpa [discOffset, sum_Icc_eq_apSumFrom_tail, apSumFrom_tail_sub_eq_apSumOffset_shift_add_tail,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

-- Paper tail sum with affine summand `a + i` (i.e. `d = 1`) → normalize to the shifted-sequence `discOffset` view.
example
    (h : Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i))) ≤ C) :
    discOffset (fun k => f (k + a)) 1 m n ≤ C := by
  simpa [discOffset, Nat.mul_one, sum_Icc_eq_apSumFrom_tail, apSumFrom_tail_eq_apSumOffset_shift_add] using h

-- Paper difference of homogeneous partial sums with `d = 1` → normalize to an offset tail (single `simpa` pipeline).
example
    (h :
        Int.natAbs
            ((Finset.Icc 1 (m + n)).sum f - (Finset.Icc 1 m).sum f) ≤
          C) :
    discOffset f 1 m n ≤ C := by
  simpa [discOffset, Nat.mul_one, sum_Icc_eq_apSum, apSum_sub_eq_apSumOffset] using h

-- Paper tail sum with affine endpoints (`m ≤ n`) and `d = 1` → normalize directly to a `discOffset` bound.
example (hmn : m ≤ n)
    (h : Int.natAbs ((Finset.Icc (m + 1) n).sum (fun i => f (a + i))) ≤ C) :
    discOffset (fun k => f (a + k)) 1 m (n - m) ≤ C := by
  simpa [discOffset, Nat.mul_one,
    sum_Icc_eq_apSumOffset_of_le_affineEndpoints (f := f) (a := a) (d := 1) (m := m) (n := n) hmn] using h

-- Paper tail sum with an affine summand `a + i*d` → normalize to the shifted-sequence `discOffset` view.
example
    (h : Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d))) ≤ C) :
    discOffset (fun k => f (k + a)) d m n ≤ C := by
  simpa [discOffset, sum_Icc_eq_apSumFrom_tail, apSumFrom_tail_eq_apSumOffset_shift_add] using h

-- Paper tail sum with a mul-left affine summand `a + d*i` → same normalization (single `simpa` pipeline).
example
    (h : Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + d * i))) ≤ C) :
    discOffset (fun k => f (k + a)) d m n ≤ C := by
  simpa [discOffset, sum_Icc_eq_apSumFrom_tail_mul_left, apSumFrom_tail_eq_apSumOffset_shift_add] using h

-- Paper difference of homogeneous partial sums (paper `Icc` notation) → normalize to an offset tail.
example
    (h :
        Int.natAbs
            ((Finset.Icc 1 (m + n)).sum (fun i => f (i * d)) - (Finset.Icc 1 m).sum (fun i => f (i * d))) ≤
          C) :
    discOffset f d m n ≤ C := by
  simpa [discOffset, sum_Icc_eq_apSum, apSum_sub_eq_apSumOffset] using h

-- Paper affine sum bound (with affine endpoints) → step-one `discOffset` normal form.
example
    (h : Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (a + i * d))) ≤ C) :
    discOffset (fun k => f (k * d + a)) 1 0 n ≤ C := by
  -- `simp` rewrites the `Icc` sum into `apSumOffset … 1 0 n`, then into `discOffset`.
  simpa [Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

-- Regression (Track B / affine difference→tail): difference of affine partial sums is the later tail.
example :
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSumFrom f (a + m * d) d n := by
  simpa using (apSumFrom_sub_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n := n))

-- Difference of affine partial sums → `discOffset` of an offset tail on a shifted sequence.
example
    (h : Int.natAbs (apSumFrom f a d (m + n) - apSumFrom f a d m) ≤ C) :
    discOffset (fun k => f (k + a)) d m n ≤ C := by
  -- Difference → affine tail → offset-sum on the shifted sequence.
  simpa [apSumFrom_sub_eq_apSumOffset_shift_add] using h

-- Paper tail sum with an *affine summand* `i*d + a` → `discOffset` bound in step-one offset form.
--
-- This is the kind of thing that shows up if a paper writes an AP as an *index interval* `Icc (m+1) (m+n)`
-- and bundles the step `d` into the summand.
example
    (h : Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d + a))) ≤ C) :
    discOffset (fun k => f (k * d + a)) 1 m n ≤ C := by
  -- `apSumOffset_one_d` rewrites the offset-sum into the `Icc` paper notation.
  simpa [discOffset, apSumOffset_one_d] using h

-- Paper difference of *paper* affine partial sums → `discOffset` bound (difference → tail → offset).
example
    (h :
        Int.natAbs
            ((Finset.Icc 1 (m + n)).sum (fun i => f (a + i * d)) -
              (Finset.Icc 1 m).sum (fun i => f (a + i * d))) ≤
          C) :
    discOffset (fun k => f (k + a)) d m n ≤ C := by
  -- Paper → nucleus (`apSumFrom`), then difference → `apSumOffset` on a shifted sequence.
  simpa [discOffset, sum_Icc_eq_apSumFrom, apSumFrom_sub_eq_apSumOffset_shift_add] using h

-- Paper tail sum with a translation-friendly summand `i*d + a` → `discOffset` bound (tail → offset on shifted seq).
example
    (h : Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d + a))) ≤ C) :
    discOffset (fun k => f (k + a)) d m n ≤ C := by
  -- Paper tail → affine-tail nucleus → offset tail on the shifted sequence.
  simpa [discOffset, sum_Icc_eq_apSumFrom_tail_add, apSumFrom_tail_eq_apSumOffset_shift_add_left] using h

-- Paper tail sum with affine endpoints (`m ≤ n`) → `discOffset` bound in `apSumOffset` normal form.
example (hmn : m ≤ n)
    (h : Int.natAbs ((Finset.Icc (m + 1) n).sum (fun i => f (a + i * d))) ≤ C) :
    discOffset (fun k => f (a + k)) d m (n - m) ≤ C := by
  simpa [discOffset,
    sum_Icc_eq_apSumOffset_of_le_affineEndpoints (f := f) (a := a) (d := d) (m := m) (n := n) hmn] using h

-- Same as above, but with the summand written as `a + d*i` (mul-left convention).
example (hmn : m ≤ n)
    (h : Int.natAbs ((Finset.Icc (m + 1) n).sum (fun i => f (a + d * i))) ≤ C) :
    discOffset (fun k => f (a + k)) d m (n - m) ≤ C := by
  simpa [discOffset,
    sum_Icc_eq_apSumOffset_of_le_affineEndpoints_mul_left (f := f) (a := a) (d := d) (m := m) (n := n) hmn] using h

-- Paper difference of two *paper* affine-endpoint tail sums → `discOffset` bound
-- (tail - shorter tail = later tail).
example (hmn : m ≤ n) (hmn₁ : m + n₁ ≤ n)
    (h :
        Int.natAbs
            ((Finset.Icc (m + 1) n).sum (fun i => f (a + i * d)) -
              (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (a + i * d))) ≤
          C) :
    discOffset (fun k => f (a + k)) d (m + n₁) (n - m - n₁) ≤ C := by
  have hn₁ : n₁ ≤ n - m := by
    exact Nat.le_sub_of_add_le hmn₁
  -- Rewrite both `Icc` tails into `apSumOffset` (stable surface), then normalize the difference.
  simpa [discOffset,
    sum_Icc_eq_apSumOffset_of_le_affineEndpoints (f := f) (a := a) (d := d) (m := m) (n := n) hmn,
    sum_Icc_eq_apSumOffset_of_le_affineEndpoints (f := f) (a := a) (d := d) (m := m) (n := m + n₁)
      (Nat.le_add_right m n₁),
    apSumOffset_sub_apSumOffset_eq_apSumOffset (f := fun k => f (a + k)) (d := d) (m := m)
      (n₁ := n₁) (n₂ := n - m) hn₁] using h

-- Same as the previous example, but with the summand written as `a + d*i` (mul-left convention).
example (hmn : m ≤ n) (hmn₁ : m + n₁ ≤ n)
    (h :
        Int.natAbs
            ((Finset.Icc (m + 1) n).sum (fun i => f (a + d * i)) -
              (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (a + d * i))) ≤
          C) :
    discOffset (fun k => f (a + k)) d (m + n₁) (n - m - n₁) ≤ C := by
  have hn₁ : n₁ ≤ n - m := by
    exact Nat.le_sub_of_add_le hmn₁
  simpa [discOffset,
    sum_Icc_eq_apSumOffset_of_le_affineEndpoints_mul_left (f := f) (a := a) (d := d) (m := m) (n := n) hmn,
    sum_Icc_eq_apSumOffset_of_le_affineEndpoints_mul_left (f := f) (a := a) (d := d) (m := m) (n := m + n₁)
      (Nat.le_add_right m n₁),
    apSumOffset_sub_apSumOffset_eq_apSumOffset (f := fun k => f (a + k)) (d := d) (m := m)
      (n₁ := n₁) (n₂ := n - m) hn₁] using h

-- Difference of affine partial sums (`m ≤ n`) → `discOffset` bound (difference → tail → offset on shifted sequence).
example (hmn : m ≤ n)
    (h : Int.natAbs (apSumFrom f a d n - apSumFrom f a d m) ≤ C) :
    discOffset (fun k => f (a + k)) d m (n - m) ≤ C := by
  simpa [discOffset,
    apSumFrom_sub_apSumFrom_eq_apSumOffset_shift (f := f) (a := a) (d := d) (m := m) (n := n) hmn] using h

-- Regression: definitional lemmas expose the wrappers.
example : discrepancy f d n = Int.natAbs (apSum f d n) := by
  rfl

example : affineDiscrepancy f a d n = Int.natAbs (apSumFrom f a d n) := by
  rfl

-- Regression: `simp` can also move `Int.natAbs` *into* the wrappers without looping.
example : Int.natAbs (apSum f d n) = discrepancy f d n := by
  simp

example : Int.natAbs (apSumFrom f a d n) = affineDiscrepancy f a d n := by
  simp

example : discrepancy (fun k => f (k + a)) d n = Int.natAbs (apSumFrom f a d n) := by
  simp

example : Int.natAbs (apSum (fun k => f (k + a)) d n) = Int.natAbs (apSumFrom f a d n) := by
  simp

example : apSum f d n = (Finset.Icc 1 n).sum (fun i => f (i * d)) := by
  simpa using apSum_eq_sum_Icc (f := f) (d := d) (n := n)

example : (Finset.Icc 1 n).sum (fun i => f (i * d)) = apSum f d n := by
  simpa using sum_Icc_eq_apSum (f := f) (d := d) (n := n)

-- Regression: use the congruence lemmas to rewrite AP sums under a pointwise equality hypothesis.
example (g : ℕ → ℤ)
    (h : ∀ i, i < n → f ((i + 1) * d) = g ((i + 1) * d)) :
    apSum f d n = apSum g d n := by
  simpa using (apSum_congr (f := f) (g := g) (d := d) (n := n) (h := h))

example (g : ℕ → ℤ)
    (h : ∀ i, i < n → f ((m + i + 1) * d) = g ((m + i + 1) * d)) :
    apSumOffset f d m n = apSumOffset g d m n := by
  simpa using (apSumOffset_congr (f := f) (g := g) (d := d) (m := m) (n := n) (h := h))

-- Regression: range-form congruence lemma (Finset.range hypothesis) is usable from the stable surface.
example (g : ℕ → ℤ)
    (h : ∀ i, i ∈ Finset.range n → f ((m + i + 1) * d) = g ((m + i + 1) * d)) :
    apSumOffset f d m n = apSumOffset g d m n := by
  simpa using (apSumOffset_congr_range (f := f) (g := g) (d := d) (m := m) (n := n) h)

-- Regression: support-form congruence lemmas are usable from the stable surface.
example (g : ℕ → ℤ)
    (h : ∀ x ∈ apSupport d m n, f x = g x) :
    apSumOffset f d m n = apSumOffset g d m n := by
  simpa using
    (apSumOffset_congr_support (f := f) (g := g) (d := d) (m := m) (n := n) (h := h))

example (g : ℕ → ℤ)
    (h : ∀ x ∈ apSupport d 0 n, f x = g x) :
    apSum f d n = apSum g d n := by
  simpa using (apSum_congr_support (f := f) (g := g) (d := d) (n := n) (h := h))

-- Regression: `apSumOffset` reindexing under a bijection on `Finset.range` indices.
--
-- This is intentionally a very small compile-time test: we use the identity permutation.
example :
    apSumOffset f d m n = (Finset.range n).sum (fun i => f ((m + i + 1) * d)) := by
  -- Route the proof through the Track B reindexing glue lemma.
  let σ : ℕ → ℕ := fun i => i
  have hσ_range : ∀ i ∈ Finset.range n, σ i ∈ Finset.range n := by
    intro i hi
    simpa [σ] using hi
  have hσ_inj :
      ∀ i₁ ∈ Finset.range n, ∀ i₂ ∈ Finset.range n, σ i₁ = σ i₂ → i₁ = i₂ := by
    intro i₁ hi₁ i₂ hi₂ hEq
    simpa [σ] using hEq
  have hσ_surj : ∀ j ∈ Finset.range n, ∃ i ∈ Finset.range n, σ i = j := by
    intro j hj
    exact ⟨j, hj, rfl⟩
  simpa [σ] using
    (apSumOffset_reindex_range_bij (f := f) (d := d) (m := m) (n := n) (σ := σ)
      (hσ_range := hσ_range) (hσ_inj := hσ_inj) (hσ_surj := hσ_surj))

example (g : ℕ → ℤ)
    (h : ∀ i, i < n → f (a + (i + 1) * d) = g (a + (i + 1) * d)) :
    apSumFrom f a d n = apSumFrom g a d n := by
  simpa using (apSumFrom_congr (f := f) (g := g) (a := a) (d := d) (n := n) (h := h))

-- Regression: `congrOn` variants (predicate on indices) are usable from the stable surface.
example (g : ℕ → ℤ) (P : ℕ → Prop)
    (hP : ∀ i, i < n → P i)
    (hfg : ∀ i, P i → f ((m + i + 1) * d) = g ((m + i + 1) * d)) :
    apSumOffset f d m n = apSumOffset g d m n := by
  simpa using
    (apSumOffset_congrOn (f := f) (g := g) (P := P) (d := d) (m := m) (n := n) (hP := hP)
      (hfg := hfg))

example (g : ℕ → ℤ) (P : ℕ → Prop)
    (hP : ∀ i, i < n → P i)
    (hfg : ∀ i, P i → f (a + (i + 1) * d) = g (a + (i + 1) * d)) :
    apSumFrom f a d n = apSumFrom g a d n := by
  simpa using
    (apSumFrom_congrOn (f := f) (g := g) (P := P) (a := a) (d := d) (n := n) (hP := hP)
      (hfg := hfg))

-- Regression: `simp` normalizes nested shifts inside translated summands.
example : (fun k => f (k + a + b)) = fun k => f (k + (a + b)) := by
  simp

-- Translation-friendly `d * i` variant (avoids commuting multiplication under binders).
example : apSum f d n = (Finset.Icc 1 n).sum (fun i => f (d * i)) := by
  simpa [Nat.mul_comm] using (apSum_eq_sum_Icc (f := f) (d := d) (n := n))

example : (Finset.Icc 1 n).sum (fun i => f (d * i)) = apSum f d n := by
  simpa [Nat.mul_comm] using (sum_Icc_eq_apSum (f := f) (d := d) (n := n))

example : apSum f 1 n = (Finset.Icc 1 n).sum f := by
  simpa using apSum_one_d (f := f) (n := n)

-- Paper affine sums → affine nucleus → step-one offset nucleus.
example : (Finset.Icc 1 n).sum (fun i => f (a + i * d)) = apSumOffset (fun k => f (a + k * d)) 1 0 n := by
  simpa using sum_Icc_eq_apSumOffset_step_one (f := f) (a := a) (d := d) (n := n)

-- Regression: normalize paper affine sums via the shifted-sequence offset view, then step-one.
example : (Finset.Icc 1 n).sum (fun i => f (a + i * d)) = apSumOffset (fun k => f (k * d + a)) 1 0 n := by
  simpa [Nat.add_comm] using
    (sum_Icc_eq_apSumOffset_step_one (f := f) (a := a) (d := d) (n := n))


-- Affine tails as offset sums (both summand conventions).

example : apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (a + k)) d m n := by
  simpa using apSumFrom_tail_eq_apSumOffset_shift (f := f) (a := a) (d := d) (m := m) (n := n)

example : apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using apSumFrom_tail_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Same normal form, but with the affine start written as `m*d + a`.
example : apSumFrom f (m * d + a) d n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using apSumFrom_tail_eq_apSumOffset_shift_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- Step-one + offset bridge at a pure multiple start `m*d` (multiplication-on-the-left convention).
example : apSumFrom f (m * d) d n = apSumOffset (fun k => f (d * k)) 1 m n := by
  simpa using apSumFrom_eq_apSumOffset_mul_left (f := f) (d := d) (m := m) (n := n)

example : apSumOffset (fun k => f (d * k)) 1 m n = apSumFrom f (m * d) d n := by
  simpa using (apSumFrom_eq_apSumOffset_mul_left (f := f) (d := d) (m := m) (n := n)).symm

-- Switching between `a + k` and `k + a` inside the shifted-sequence view of `apSumOffset`.
example : apSumOffset (fun k => f (a + k)) d m n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using apSumOffset_shift_comm (f := f) (a := a) (d := d) (m := m) (n := n)

-- Commuting `a + k` ↔ `k + a` under the nucleus sums.
--
-- These are small but useful “normalization” steps when you want a translation-friendly `k + const`
-- summand shape without doing a manual `funext` rewrite.
example : apSum (fun k => f (a + k)) d n = apSum (fun k => f (k + a)) d n := by
  simpa using apSum_shift_comm (f := f) (a := a) (d := d) (n := n)

example : apSumFrom (fun x => f (a + x)) m d n = apSumFrom (fun x => f (x + a)) m d n := by
  simpa using apSumFrom_shift_comm (f := f) (a := a) (k := m) (d := d) (n := n)

-- Translation bookkeeping for affine starts.
example : apSumFrom f (a + b) d n = apSumFrom (fun t => f (t + b)) a d n := by
  simpa using apSumFrom_start_add_eq_shift_add (f := f) (a := a) (b := b) (d := d) (n := n)

example : apSumFrom (fun t => f (t + b)) a d n = apSumFrom f (a + b) d n := by
  simpa using apSumFrom_shift_add_eq_start_add (f := f) (a := a) (b := b) (d := d) (n := n)

-- Witness-level translation normal form (div/mod reduced translation inside an `apSumOffset`).
example :
    HasDiscrepancyAtLeast (fun k => f (k + a)) C ↔
      ∃ d n : ℕ, d > 0 ∧ Int.natAbs (apSumOffset (fun t => f (t + (a % d))) d (a / d) n) > C := by
  simpa using
    (HasDiscrepancyAtLeast_shift_add_iff_exists_apSumOffset_div_mod (f := f) (a := a) (C := C))

-- Summand-shift normalization modulo the step inside an `apSumOffset`.
example (hd : 0 < d) :
    apSumOffset (fun k => f (k + a)) d m n =
      apSumOffset (fun k => f (k + (a % d))) d (m + a / d) n := by
  simpa using (apSumOffset_shift_mod (f := f) (d := d) (m := m) (n := n) (a := a) hd)

-- Canonical quotient/remainder normal form for affine starts (div/mod).
example (hd : 0 < d) :
    apSumFrom f a d n = apSumOffset (fun t => f (t + (a % d))) d (a / d) n := by
  -- Convert `0 < d` to `d > 0` for the API lemma.
  simpa using (apSumFrom_eq_apSumOffset_div_mod (f := f) (a := a) (d := d) (n := n) hd)


-- “Push the translation into the function” normal forms.
--
-- These are mathematically the same as the `…_shift` / `…_shift_add` family.
-- (The older `*_map_add` names are now deprecated wrappers.)
example : apSumFrom f a d n = apSum (fun x => f (x + a)) d n := by
  simpa using apSumFrom_eq_apSum_shift_add (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = apSum (fun x => f (a + x)) d n := by
  simpa using apSumFrom_eq_apSum_shift_add_left (f := f) (a := a) (d := d) (n := n)

-- Differences → tails (canonical normal form).

example : apSum f d (m + n) - apSum f d m = apSumOffset f d m n := by
  simpa using apSum_sub_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

example : apSumFrom f a d (m + n) - apSumFrom f a d m = apSumFrom f (a + m * d) d n := by
  simpa using apSumFrom_sub_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n := n)

-- If you prefer the canonical offset-sum normal form on the shifted sequence `k ↦ f (k + a)`,
-- rewrite the same difference directly to `apSumOffset`.
example :
    apSumFrom f a d (m + n) - apSumFrom f a d m =
      apSumOffset (fun k => f (k + a)) d m n := by
  -- Two-step “difference → affine tail → offset on a shifted sequence” normal form.
  --
  -- This is a regression test for the Track B glue lemma
  -- apSumFrom_sub_eq_apSumOffset_shift_add: even if that lemma gets refactored,
  -- we want this common rewrite pipeline to keep working from the stable import
  -- surface `import MoltResearch.Discrepancy`.
  calc
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSumFrom f (a + m * d) d n := by
      simpa using
        apSumFrom_sub_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n := n)
    _ = apSumOffset (fun k => f (k + a)) d m n := by
      simpa using
        apSumFrom_tail_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Tail-of-tail differences → offset-sum tails (and the `m = 0` shifted-sequence normal form).
example :
    apSumFrom f (a + m * d) d (n₁ + n₂) - apSumFrom f (a + m * d) d n₁ =
      apSumOffset (fun k => f (k + a)) d (m + n₁) n₂ := by
  simpa using
    apSumFrom_tail_sub_eq_apSumOffset_shift_add_tail (f := f) (a := a) (d := d) (m := m)
      (n1 := n₁) (n2 := n₂)

example :
    apSumFrom f (a + m * d) d (n₁ + n₂) - apSumFrom f (a + m * d) d n₁ =
      apSumOffset (fun k => f (k + (a + (m + n₁) * d))) d 0 n₂ := by
  simpa using
    apSumFrom_tail_sub_eq_apSumOffset_shift_add_zero_m_tail (f := f) (a := a) (d := d) (m := m)
      (n1 := n₁) (n2 := n₂)

-- Degenerate constant APs.
example : apSum f 0 n = n • f 0 := by
  simp

-- Periodicity normal form: a step that is a multiple of the period yields a constant sum.
example (hp : Function.Periodic f p) : apSumOffset f (p * d) m n = n • f 0 := by
  simpa using (apSumOffset_mul_periodic (f := f) (p := p) hp (d := d) (m := m) (n := n))

-- Periodicity normal form (divisibility phrasing): if the step is any multiple of the period.
example (hp : Function.Periodic f p) (hd : p ∣ d) : apSumOffset f d m n = n • f 0 := by
  simpa using (apSumOffset_periodic_of_dvd_step (f := f) (p := p) hp (d := d) hd (m := m) (n := n))

-- Discrepancy-level corollary: shifting the offset does not change `discOffset`.
example (hp : Function.Periodic f p) (hd : p ∣ d) : discOffset f d m n = discOffset f d 0 n := by
  simpa using (discOffset_periodic_of_dvd_step (f := f) (p := p) hp (d := d) hd (m := m) (n := n))

example : apSum f d n = apSum (fun k => f (k * d)) 1 n := by
  simpa using apSum_eq_apSum_step_one (f := f) (d := d) (n := n)

example : apSum (fun k => f (k * d)) 1 n = apSum f d n := by
  simpa using (apSum_eq_apSum_step_one (f := f) (d := d) (n := n)).symm

-- Offset/tail normal forms.
example : apSum f d (m + n) - apSum f d m = apSumOffset f d m n := by
  simpa using apSum_sub_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

-- Expand `apSumOffset` into a `Finset.range` sum (avoids `Icc` paper bookkeeping).
example : apSumOffset f d m n = (Finset.range n).sum (fun i => f ((m + i + 1) * d)) := by
  simpa using apSumOffset_eq_sum_range (f := f) (d := d) (m := m) (n := n)

-- Regression: stable lemma name for the same normal form.
example : apSumOffset f d m n = (Finset.range n).sum (fun i => f ((m + i + 1) * d)) := by
  simpa using apSumOffset_eq_sum_range' (f := f) (d := d) (m := m) (n := n)

-- Range-form stability at discrepancy level: range-index congruence (no `Icc` endpoints).
example (g : ℕ → ℤ)
    (h : ∀ i, i ∈ Finset.range n → f ((m + i + 1) * d) = g ((m + i + 1) * d)) :
    discOffset f d m n = discOffset g d m n := by
  simpa using (discOffset_congr_range (f := f) (g := g) (d := d) (m := m) (n := n) h)

-- Translation-friendly variant with binder order `i + m + 1`.
example : apSumOffset f d m n = (Finset.range n).sum (fun i => f ((i + m + 1) * d)) := by
  simpa using apSumOffset_eq_sum_range_add (f := f) (d := d) (m := m) (n := n)

-- One-cut normal form for `Finset.range` expansions: split the range sum and land back in `apSumOffset`.
example :
    (Finset.range (n₁ + n₂)).sum (fun i => f ((m + i + 1) * d)) =
      apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
  simpa using
    sum_range_add_len_eq_apSumOffset_add (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- One-cut normal form at the `discOffset` level (range-cut lemma regression).
example :
    discOffset f d m (n₁ + n₂) =
      Int.natAbs (apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂) := by
  simpa using
    discOffset_add_len_eq_natAbs_apSumOffset_add (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Range-cut normal form specialized to a cut length `k ≤ n`.
example {k : ℕ} (hk : k ≤ n) :
    discOffset f d m n =
      Int.natAbs (apSumOffset f d m k + apSumOffset f d (m + k) (n - k)) := by
  simpa using
    (discOffset_eq_natAbs_apSumOffset_cut (f := f) (d := d) (m := m) (n := n) (k := k) hk)

-- Same difference normal form, but eliminate the explicit offset sum into a homogeneous AP sum
-- on a shifted sequence.
example : apSum f d (m + n) - apSum f d m = apSum (fun k => f (k + m * d)) d n := by
  simpa using apSum_sub_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n)

-- Length-splitting normal forms for `apSumOffset`.
example : apSumOffset f d m (n₁ + n₂) = apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
  simpa using apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Range-cut normal form for `apSumOffset`: split at a cut length `k ≤ n`.
example {k : ℕ} (hk : k ≤ n) :
    apSumOffset f d m n = apSumOffset f d m k + apSumOffset f d (m + k) (n - k) := by
  simpa using
    (apSumOffset_eq_add_apSumOffset_cut (f := f) (d := d) (m := m) (n := n) (k := k) hk)

-- Regression: split a paper interval sum in two, then land in the nucleus `apSumOffset` normal form.
example :
    (Finset.Icc (m + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) =
      apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
  simpa using
    sum_Icc_add_len_eq_apSumOffset_add (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Splitting at an interior cut `k` (with `m ≤ k ≤ m+n`).
example {k : ℕ} (hmk : m ≤ k) (hkn : k ≤ m + n) :
    apSumOffset f d m n = apSumOffset f d m (k - m) + apSumOffset f d k (m + n - k) := by
  simpa using (apSumOffset_split_at (f := f) (d := d) (hmk := hmk) (hkn := hkn))

-- Same split, but at the discrepancy wrapper level (`discOffset`).
example {k : ℕ} (hmk : m ≤ k) (hkn : k ≤ m + n) :
    discOffset f d m n ≤ discOffset f d m (k - m) + discOffset f d k (m + n - k) := by
  simpa using (discOffset_split_at_le (f := f) (d := d) (m := m) (k := k) (n := n) hmk hkn)

-- Homogeneous analogue (`disc`), specialized to `m = 0`.
example {k : ℕ} (hkn : k ≤ n) :
    disc f d n ≤ disc f d k + discOffset f d k (n - k) := by
  simpa using (disc_split_at_le (f := f) (d := d) (k := k) (n := n) hkn)

-- `disc` shift normal form (API coherence regression).
example (a : ℕ) :
    disc (fun k => f (k + a * d)) d n = Int.natAbs (apSumOffset f d a n) := by
  simpa using (disc_shift_mul (f := f) (a := a) (d := d) (n := n))

-- `discOffset` bound wrapper regression: `|apSumOffset| ≤ n*B` implies `discOffset ≤ n*B`.
example {B : ℕ} (hf : ∀ k, Int.natAbs (f k) ≤ B) : discOffset f d m n ≤ n * B := by
  simpa using (discOffset_le_mul_of_natAbs_le (f := f) (B := B) (hf := hf) (d := d) (m := m)
    (n := n))

-- `discOffset` length bound regression (the `B = 1` specialization).
example (hf : ∀ k, Int.natAbs (f k) ≤ 1) : discOffset f d m n ≤ n := by
  simpa using (discOffset_le_of_natAbs_le_one (f := f) (hf := hf) (d := d) (m := m) (n := n))

-- `disc` bound wrapper regression: `|apSum| ≤ n*B` implies `disc ≤ n*B`.
example {B : ℕ} (hf : ∀ k, Int.natAbs (f k) ≤ B) : disc f d n ≤ n * B := by
  simpa using (disc_le_mul_of_natAbs_le (f := f) (B := B) (hf := hf) (d := d) (n := n))

-- `disc` length bound regression (the `B = 1` specialization).
example (hf : ∀ k, Int.natAbs (f k) ≤ 1) : disc f d n ≤ n := by
  simpa using (disc_le_of_natAbs_le_one (f := f) (hf := hf) (d := d) (n := n))

-- `discOffset` triangle inequality regression (Track B item: concatenation bound).
example :
    discOffset f d m (n₁ + n₂) ≤ discOffset f d m n₁ + discOffset f d (m + n₁) n₂ := by
  simpa using (discOffset_add_le (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))

-- `disc` triangle inequality regression (homogeneous analogue of `discOffset_add_le`).
example : disc f d (n₁ + n₂) ≤ disc f d n₁ + discOffset f d n₁ n₂ := by
  simpa using (disc_add_le (f := f) (d := d) (n₁ := n₁) (n₂ := n₂))

-- `disc` one-step stability regression (homogeneous analogue of `discOffset_succ_le_add_natAbs`).
example : disc f d (n + 1) ≤ disc f d n + Int.natAbs (f ((n + 1) * d)) := by
  simpa using (disc_succ_le_add_natAbs (f := f) (d := d) (n := n))

example (hf : IsSignSequence f) : disc f d (n + 1) ≤ disc f d n + 1 := by
  simpa using (IsSignSequence.disc_succ_le (f := f) (hf := hf) (d := d) (n := n))

example :
    apSumOffset f d m (n₁ + n₂) =
      apSumOffset f d m n₁ + apSum (fun k => f (k + (m + n₁) * d)) d n₂ := by
  simpa using
    apSumOffset_add_length_eq_add_apSum_shift_add (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

example : apSumOffset f d 0 n = apSum f d n := by
  simp

-- Regression (Track B / step-factoring at a multiple start):
-- normalize `apSumFrom f (a*d) (k*d) n` directly into an `apSumOffset` on a shifted sequence.
example : apSumFrom f (a * d) (k * d) n = apSumOffset (fun t => f ((t + a) * d)) k 0 n := by
  simpa using
    (apSumFrom_mul_start_mul_step_eq_apSumOffset_shift_mul_right (f := f) (a₀ := a) (d₁ := k)
      (d₂ := d) (n := n))

-- Regression (Track B / step-factoring when the start is a multiple):
-- normalize `apSumFrom f a (k*d) n` assuming `d ∣ a`.
example (ha : d ∣ a) :
    apSumFrom f a (k * d) n = apSumOffset (fun t => f ((t + a / d) * d)) k 0 n := by
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (apSumFrom_mul_step_eq_apSumOffset_shift_mul_of_dvd (f := f) (a := a) (d₁ := k) (d₂ := d)
      (n := n) (ha := ha))

example : apSumFrom f 0 d n = apSum f d n := by
  simpa using apSumFrom_zero_start (f := f) (d := d) (n := n)

example : apSum f d n = apSumFrom f 0 d n := by
  simpa using apSum_eq_apSumFrom (f := f) (d := d) (n := n)

-- Offset sums: shifted-sequence normal forms (translation-friendly `k + const`).
example : apSumOffset f d m n = apSum (fun k => f (k + m * d)) d n := by
  simpa using apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n)

-- Same normal form, but write the translation constant as `d*m` (mul-left convention).
example : apSumOffset f d m n = apSum (fun k => f (k + d * m)) d n := by
  simpa using apSumOffset_eq_apSum_shift_add_mul_left (f := f) (d := d) (m := m) (n := n)

-- Differences of offset sums: mul-left translation constant variant.
example :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ =
      apSum (fun k => f (k + d * (m + n₁))) d n₂ := by
  simpa using
    apSumOffset_sub_eq_apSum_shift_add_mul_left (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

example : apSumOffset f d m n = apSumOffset (fun k => f (k + m * d)) d 0 n := by
  simpa using apSumOffset_eq_apSumOffset_shift_add (f := f) (d := d) (m := m) (n := n)

-- Same normal form, but write the translation constant as `d*m` (mul-left convention).
example : apSumOffset f d m n = apSumOffset (fun k => f (k + d * m)) d 0 n := by
  simpa using
    apSumOffset_eq_apSumOffset_shift_add_mul_left (f := f) (d := d) (m := m) (n := n)

-- Shift in the start index: absorb `+k` in the offset parameter into a translation of the summand.
example (k : ℕ) :
    apSumOffset f d (m + k) n = apSumOffset (fun t => f (t + k * d)) d m n := by
  simpa using apSumOffset_shift_start_add (f := f) (d := d) (m := m) (k := k) (n := n)

-- Add-left variant.
example (k : ℕ) :
    apSumOffset f d (m + k) n = apSumOffset (fun t => f (k * d + t)) d m n := by
  simpa using apSumOffset_shift_start_add_left (f := f) (d := d) (m := m) (k := k) (n := n)

-- Paper normal form: rewrite `Icc (m+1) (m+n)` tails to the fixed-lower-endpoint `Icc 1 n` form.
example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) =
      (Finset.Icc 1 n).sum (fun i => f ((m + i) * d)) := by
  simpa using sum_Icc_eq_sum_Icc_length (f := f) (d := d) (m := m) (n := n)

-- Translation-friendly `d * i` variant.
example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) =
      (Finset.Icc 1 n).sum (fun i => f (d * (m + i))) := by
  simpa using sum_Icc_eq_sum_Icc_length_mul_left (f := f) (d := d) (m := m) (n := n)

-- Offset paper notation: multiplication-on-the-left variants (avoid commuting `i*d` under binders).
example : apSumOffset f d m n = (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) := by
  simpa using apSumOffset_eq_sum_Icc_mul_left (f := f) (d := d) (m := m) (n := n)

example : (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) = apSumOffset f d m n := by
  simpa using sum_Icc_eq_apSumOffset_mul_left (f := f) (d := d) (m := m) (n := n)

-- Offset sums on a shifted sequence: return to the affine-tail nucleus API.
example : apSumOffset (fun k => f (k + a)) d m n = apSumFrom f (a + m * d) d n := by
  simpa using apSumOffset_shift_add_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m)
    (n := n)

-- Regression example: same statement via the “first term” bridge lemma.
example : apSumOffset (fun k => f (k + a)) d m n = apSumFrom f (a + m * d) d n := by
  simpa using
    apSumOffset_shift_add_eq_apSumFrom_tail_firstTerm (f := f) (a := a) (d := d) (m := m)
      (n := n)

example : apSumOffset (fun k => f (k + a)) d m n = apSumFrom f (m * d + a) d n := by
  simpa using apSumOffset_shift_add_eq_apSumFrom_tail_left (f := f) (a := a) (d := d) (m := m)
    (n := n)

-- Affine sums: shift-add normal form (translation-friendly `k + a`).
example : apSumFrom f a d n = apSum (fun k => f (k + a)) d n := by
  simpa using apSumFrom_eq_apSum_shift_add (f := f) (a := a) (d := d) (n := n)

-- Affine sums: offset-sum normal form on the shifted sequence.
example : apSumFrom f a d n = apSumOffset (fun k => f (k + a)) d 0 n := by
  simpa using apSumFrom_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (n := n)

-- Normal form when the affine start is a multiple of the step.
example (h : d ∣ a) : ∃ m, apSumFrom f a d n = apSumOffset f d m n := by
  simpa using
    (apSumFrom_exists_eq_apSumOffset_of_dvd (f := f) (a := a) (d := d) (n := n) h)

-- Same affine sum, but with the translation “pushed into the function” form `x ↦ f (x + a)`.
-- This is handy when you want to reuse translation lemmas stated for homogeneous `apSum`.
example : apSumFrom f a d n = apSum (fun x => f (x + a)) d n := by
  simpa using apSumFrom_eq_apSum_shift_add (f := f) (a := a) (d := d) (n := n)

-- Affine paper notation: multiplication-on-the-left variants (avoid commuting `i*d` under binders).
-- These are *not* separate surface lemmas: rewrite `i * d` ↔ `d * i` with `Nat.mul_comm` as needed.
example : apSumFrom f a d n = (Finset.Icc 1 n).sum (fun i => f (a + d * i)) := by
  simpa [Nat.mul_comm] using (apSumFrom_eq_sum_Icc (f := f) (a := a) (d := d) (n := n))

example : apSumFrom f a d n = (Finset.Icc 1 n).sum (fun i => f (d * i + a)) := by
  simpa [Nat.mul_comm] using (apSumFrom_eq_sum_Icc_add (f := f) (a := a) (d := d) (n := n))

-- Regression: paper affine sums can normalize to a step-one `apSumOffset` form.
example : (Finset.Icc 1 n).sum (fun i => f (a + i * d)) = apSumOffset (fun k => f (a + k * d)) 1 0 n := by
  -- Paper → nucleus (`apSumFrom`), then “step-one” offset normal form.
  simpa using
    (sum_Icc_eq_apSumFrom (f := f) (a := a) (d := d) (n := n)).trans
      (apSumFrom_eq_apSumOffset_step_one (f := f) (a := a) (d := d) (n := n))

-- Regression: paper affine sums with translation-friendly binder normalize to a step-one homogeneous `apSum` form.
example : (Finset.Icc 1 n).sum (fun i => f (i * d + a)) = apSum (fun k => f (k * d + a)) 1 n := by
  -- Paper → nucleus (`apSumFrom`), then “step-one” homogeneous normal form.
  simpa using
    (sum_Icc_eq_apSumFrom_add (f := f) (a := a) (d := d) (n := n)).trans
      (apSumFrom_eq_apSum_step_one_add_left (f := f) (a := a) (d := d) (n := n))

-- Regression: “step into summand” coherence.
-- Paper → nucleus → step-one offset normal form, packaged via the shifted-sequence route.
example :
    (Finset.Icc 1 n).sum (fun i => f (i * d + a)) = apSumOffset (fun k => f (k * d + a)) 1 0 n := by
  simpa using
    (sum_Icc_eq_apSumFrom_add (f := f) (a := a) (d := d) (n := n)).trans
      (apSumFrom_eq_apSumOffset_step_one_add_left (f := f) (a := a) (d := d) (n := n))

-- Regression: “step into summand” coherence for the more common `a + i*d` paper form.
example :
    (Finset.Icc 1 n).sum (fun i => f (a + i * d)) = apSumOffset (fun k => f (k * d + a)) 1 0 n := by
  simpa [Nat.add_comm] using
    sum_Icc_eq_apSumOffset_step_one (f := f) (a := a) (d := d) (n := n)

-- Affine differences: normalize to an offset sum on a shifted sequence.
example :
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using
    apSumFrom_sub_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Same difference normal form, but eliminate the tail parameter into a homogeneous AP sum.
-- Writing the translation constant as `m*d + a` avoids a commutativity rewrite.
example :
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSum (fun k => f (k + (m * d + a))) d n := by
  simpa using
    apSumFrom_sub_eq_apSum_shift_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- Same normal form, but write the translation constant as `d*m + a` (mul-left convention).
example :
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSum (fun k => f (k + (d * m + a))) d n := by
  simpa using
    apSumFrom_sub_eq_apSum_shift_add_mul_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- Difference → tail, then absorb the tail offset into the translation constant so the offset is `0`.
-- This is often a good “don’t carry extra parameters” normal form before bounding/splitting.
example :
    apSumFrom f a d (m + n) - apSumFrom f a d m =
      apSumOffset (fun k => f (k + (a + m * d))) d 0 n := by
  simpa using
    apSumFrom_sub_eq_apSumOffset_shift_add_zero_m (f := f) (a := a) (d := d) (m := m) (n := n)

-- Translation-friendly affine “step-one” normal forms.
example : apSumFrom f a d n = apSum (fun k => f (k * d + a)) 1 n := by
  simpa using apSumFrom_eq_apSum_step_one_add_left (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f (a + m * d) d n = apSum (fun k => f (k * d + (a + m * d))) 1 n := by
  simpa using
    apSumFrom_tail_eq_apSum_step_one_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- Same tail step-one normal form, but with the affine start already written as `m*d + a`.
example : apSumFrom f (m * d + a) d n = apSum (fun k => f (k * d + (m * d + a))) 1 n := by
  simpa using
    apSumFrom_tail_eq_apSum_step_one_add_left_start_add_left (f := f) (a := a) (d := d) (m := m)
      (n := n)

-- Regression: tail head+tail normal form (translation-friendly add-left form).
example :
    apSumFrom f (a + m * d) d (n + 1) =
      f ((m + 1) * d + a) + apSumFrom f ((m + 1) * d + a) d n := by
  simpa using
    apSumFrom_tail_succ_length_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- Regression: tail append-one-term normal form (translation-friendly add-left form).
example :
    apSumFrom f (a + m * d) d (n + 1) = apSumFrom f (a + m * d) d n + f ((m + n + 1) * d + a) := by
  simpa using
    apSumFrom_tail_succ_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- Regression: tail normal forms when the affine start is already written as `m*d + a`.
example : apSumFrom f (m * d + a) d n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using
    apSumFrom_tail_eq_apSumOffset_shift_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

example : apSumFrom f (m * d + a) d n = apSum (fun k => f (k + (m * d + a))) d n := by
  simpa using
    apSumFrom_tail_eq_apSum_shift_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    apSumFrom f (m * d + a) d (n + 1) =
      f ((m + 1) * d + a) + apSumFrom f ((m + 1) * d + a) d n := by
  simpa using
    apSumFrom_tail_succ_length_start_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    apSumFrom f (m * d + a) d (n + 1) = apSumFrom f (m * d + a) d n + f ((m + n + 1) * d + a) := by
  simpa using
    apSumFrom_tail_succ_start_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- Step-one normalization that stays inside the offset nucleus API (`m = 0`) in the
-- translation-friendly `k*d + const` presentation.
example : apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (k * d + (a + m * d))) 1 0 n := by
  simpa using
    apSumFrom_tail_eq_apSumOffset_step_one_zero_m_add_left (f := f) (a := a) (d := d) (m := m)
      (n := n)

-- Same step-one offset-sum normal form, but with the affine start already written as `m*d + a`.
example : apSumFrom f (m * d + a) d n = apSumOffset (fun k => f (k * d + (m * d + a))) 1 0 n := by
  simpa using
    apSumFrom_tail_eq_apSumOffset_step_one_zero_m_add_left_start_add_left (f := f) (a := a) (d := d)
      (m := m) (n := n)

-- Step-one normalization that keeps the offset parameter `m`, with the summand written as
-- `a + k*d`.
example : apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (a + k * d)) 1 m n := by
  simpa using
    apSumFrom_tail_eq_apSumOffset_step_one (f := f) (a := a) (d := d) (m := m) (n := n)

-- Offset ↔ affine normal forms.
example : apSumOffset f d m n = apSumFrom f (m * d) d n := by
  simpa using apSumOffset_eq_apSumFrom (f := f) (d := d) (m := m) (n := n)

example : apSumFrom f (m * d) d n = apSumOffset f d m n := by
  simpa using apSumFrom_mul_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

-- Divisibility normal form: if `d ∣ a`, rewrite the affine sum to an offset sum using the
-- canonical quotient `a / d`.
example (h : d ∣ a) : apSumFrom f a d n = apSumOffset f d (a / d) n := by
  simpa using (apSumFrom_eq_apSumOffset_of_dvd (f := f) (a := a) (d := d) (n := n) h)

-- Same offset normal form, but with the affine start written as `d*m`.
-- (Downstream code can rewrite with `Nat.mul_comm` to use the canonical `m*d` lemma.)
example : apSumFrom f (d * m) d n = apSumOffset f d m n := by
  simpa [Nat.mul_comm] using apSumFrom_mul_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

-- Step-one normalization: bundle the step size `d` into the summand and switch to step `1`.
example : apSumFrom f a d n = apSum (fun k => f (a + k * d)) 1 n := by
  simpa using apSumFrom_eq_apSum_step_one (f := f) (a := a) (d := d) (n := n)

-- Differences of partial sums: normalize to tails early.
example : apSum f d (m + n) - apSum f d m = apSumOffset f d m n := by
  simpa using apSum_sub_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

-- If you want the *fixed lower endpoint* paper normal form (useful for splitting by length),
-- rewrite the same difference directly to an `Icc 1 n` interval sum.
example : apSum f d (m + n) - apSum f d m = (Finset.Icc 1 n).sum (fun i => f ((m + i) * d)) := by
  simpa using apSum_sub_eq_sum_Icc_length (f := f) (d := d) (m := m) (n := n)

-- Same paper normal form, but in the translation-friendly `d * (m+i)` binder convention.
example : apSum f d (m + n) - apSum f d m = (Finset.Icc 1 n).sum (fun i => f (d * (m + i))) := by
  simpa using apSum_sub_eq_sum_Icc_length_mul_left (f := f) (d := d) (m := m) (n := n)

-- And you can normalize back into the nucleus API without carrying a variable upper endpoint.
example : (Finset.Icc 1 n).sum (fun i => f ((m + i) * d)) = apSumOffset f d m n := by
  simpa using sum_Icc_eq_apSumOffset_length (f := f) (d := d) (m := m) (n := n)

example : apSumFrom f a d (m + n) - apSumFrom f a d m = apSumFrom f (a + m * d) d n := by
  simpa using
    apSumFrom_sub_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n := n)

-- Offset sums: additional normal forms that tend to compose well.
example : apSumOffset f d m n = apSum (fun k => f (k * d + m * d)) 1 n := by
  simpa using apSumOffset_eq_apSum_step_one_add_left (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f d m n = apSum (fun k => f (k + m * d)) d n := by
  simpa using apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n)

-- Eliminate an offset parameter `m` by absorbing it into a translation constant.
example :
    apSumOffset (fun k => f (k + a)) d m n = apSumOffset (fun k => f (k + (a + m * d))) d 0 n := by
  simpa using
    apSumOffset_shift_add_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Normalize an *added* offset `m + b` by pushing `b` into the translation constant.
example :
    apSumOffset (fun k => f (k + a)) d (m + b) n = apSumOffset (fun k => f (k + (a + b * d))) d m n := by
  simpa using
    apSumOffset_shift_add_add_offset_eq (f := f) (a := a) (d := d) (m := m) (b := b) (n := n)

-- Same coherence, but in the reverse direction.
example :
    apSumOffset (fun k => f (k + (a + b * d))) d m n = apSumOffset (fun k => f (k + a)) d (m + b) n := by
  simpa using
    apSumOffset_shift_add_shift_add_eq_apSumOffset_shift_add_add_offset (f := f) (a := a) (d := d)
      (m := m) (b := b) (n := n)

-- Shift in the start index: absorb `k` into a summand translation.
example :
    apSumOffset f d (m + k) n = apSumOffset (fun t => f (t + k * d)) d m n := by
  simpa using apSumOffset_shift_start_add (f := f) (d := d) (m := m) (k := k) (n := n)

-- Homogeneous AP view: push an offset into the translation constant under `apSum`.
example :
    apSumOffset (fun k => f (k + a)) d b n = apSum (fun k => f (k + (a + b * d))) d n := by
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (apSumOffset_shift_add_eq_apSum_shift_add (f := f) (a := a) (d := d) (m := b) (n := n))

-- Affine tails/differences as offset sums on a shifted sequence (translation-friendly `k + a`).
example : apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using apSumFrom_tail_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Split affine tails by length, with the second block expressed as an `apSumOffset` on the
-- shifted sequence `k ↦ f (k + a)`.
example :
    apSumFrom f (a + m * d) d (n₁ + n₂) =
      apSumFrom f (a + m * d) d n₁ + apSumOffset (fun k => f (k + a)) d (m + n₁) n₂ := by
  simpa using
    apSumFrom_tail_add_length_eq_add_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m)
      (n1 := n₁) (n2 := n₂)

-- Same normal form, but keep the shifted sequence in the `a + k` shape.
example :
    apSumFrom f (a + m * d) d (n₁ + n₂) =
      apSumFrom f (a + m * d) d n₁ + apSumOffset (fun k => f (a + k)) d (m + n₁) n₂ := by
  simpa using
    apSumFrom_tail_add_length_eq_add_apSumOffset_shift (f := f) (a := a) (d := d) (m := m)
      (n1 := n₁) (n2 := n₂)

-- Further normalize affine tails by absorbing `m` into the translation constant (so the offset is `0`).
example :
    apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (k + (a + m * d))) d 0 n := by
  simpa using
    apSumFrom_tail_eq_apSumOffset_shift_add_zero_m (f := f) (a := a) (d := d) (m := m) (n := n)

-- Same normalization, but eliminate the now-trivial offset sum (`m = 0`) into a homogeneous AP sum.
example :
    apSumFrom f (a + m * d) d n = apSum (fun k => f (k + (a + m * d))) d n := by
  simpa using
    apSumFrom_tail_eq_apSum_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Same idea, but for the standard `m+n` splitting normal form.
example :
    apSumFrom f a d (m + n) =
      apSumFrom f a d m + apSumOffset (fun k => f (k + (a + m * d))) d 0 n := by
  simpa using
    apSumFrom_add_length_eq_add_apSumOffset_shift_add_zero_m (f := f) (a := a) (d := d) (m := m)
      (n := n)

-- Same splitting normal form, but write the translation constant as `d*m + a` (mul-left convention).
example :
    apSumFrom f a d (m + n) =
      apSumFrom f a d m + apSumOffset (fun k => f (k + (d * m + a))) d 0 n := by
  simpa using
    apSumFrom_add_length_eq_add_apSumOffset_shift_add_zero_m_mul_left (f := f) (a := a) (d := d)
      (m := m) (n := n)

-- Same splitting normal form, but eliminate the now-trivial offset sum (`m = 0`) into a
-- homogeneous AP sum on a shifted sequence.
example :
    apSumFrom f a d (m + n) =
      apSumFrom f a d m + apSum (fun k => f (k + (a + m * d))) d n := by
  simpa using
    apSumFrom_add_length_eq_add_apSum_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Same, with the translation constant written as `m*d + a` (often avoids commutativity rewrites).
example :
    apSumFrom f a d (m + n) =
      apSumFrom f a d m + apSum (fun k => f (k + (m * d + a))) d n := by
  -- `AffineTail` has the main lemma in the `(a + m*d)` presentation; this wrapper just
  -- reassociates/commutes the translation constant.
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (apSumFrom_add_length_eq_add_apSum_shift_add (f := f) (a := a) (d := d) (m := m) (n := n))

-- Same normal form, but with the affine start written as `m*d + a` (avoids a commutativity rewrite).
example : apSumFrom f (m * d + a) d n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using
    apSumFrom_tail_eq_apSumOffset_shift_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- Same normalization, but eliminate the tail parameter entirely into a homogeneous AP sum.
example : apSumFrom f (m * d + a) d n = apSum (fun k => f (k + (m * d + a))) d n := by
  simpa using
    apSumFrom_tail_eq_apSum_shift_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- If you prefer to keep the shifted summand in the `a + k` form, use the corresponding wrappers.
example : apSumFrom f (m * d + a) d n = apSumOffset (fun k => f (a + k)) d m n := by
  simpa using
    apSumFrom_tail_eq_apSumOffset_shift_start_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

example : apSumOffset (fun k => f (a + k)) d m n = apSumFrom f (m * d + a) d n := by
  simpa using
    apSumOffset_shift_eq_apSumFrom_tail_start_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

example : apSumFrom f a d n = apSumOffset (fun k => f (k + a)) d 0 n := by
  simpa using apSumFrom_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (n := n)

-- If you have already shifted the summand `k ↦ f (k + a)`, normalize back to the canonical
-- `apSumFrom f a d n` form.
example : apSumFrom (fun k => f (k + a)) 0 d n = apSumFrom f a d n := by
  simpa using apSumFrom_shift_add_eq_apSumFrom (f := f) (a := a) (d := d) (n := n)

-- Same normal form, but with the shifted summand written as `a + k` (avoids a commutativity rewrite
-- under binders).
example : apSumFrom f a d n = apSumFrom (fun k => f (a + k)) 0 d n := by
  simpa using apSumFrom_eq_apSumFrom_shift_add_left (f := f) (a := a) (d := d) (n := n)

example : apSumFrom (fun k => f (a + k)) 0 d n = apSumFrom f a d n := by
  simpa using apSumFrom_shift_add_left_eq_apSumFrom (f := f) (a := a) (d := d) (n := n)

-- Translation (additive reindexing) normal forms.
-- These are lightweight but practical: they let you commute a shift through the nucleus APIs
-- without needing to unfold `apSumFrom` and fight `Nat.add_*` under binders.

-- Commute a translation in the binder convention for `apSum` (normal-form helper).
example : apSum (fun x => f (a + x)) d n = apSum (fun x => f (x + a)) d n := by
  simpa using apSum_shift_comm (f := f) (a := a) (d := d) (n := n)

-- Same commutation normal form, but inside `apSumOffset`.
example : apSumOffset (fun x => f (a + x)) d m n = apSumOffset (fun x => f (x + a)) d m n := by
  simpa using apSumOffset_shift_comm (f := f) (a := a) (d := d) (m := m) (n := n)

-- Same commutation normal form, but inside `apSumFrom`.
example : apSumFrom (fun x => f (a + x)) m d n = apSumFrom (fun x => f (x + a)) m d n := by
  simpa using apSumFrom_shift_comm (f := f) (a := a) (k := m) (d := d) (n := n)

example : apSumFrom (fun x => f (x + m)) a d n = apSumFrom f (a + m) d n := by
  simpa using apSumFrom_shift_add (f := f) (k := m) (a := a) (d := d) (n := n)

example : apSumFrom (fun x => f (m + x)) a d n = apSumFrom f (m + a) d n := by
  simpa using apSumFrom_shift_add_left (f := f) (k := m) (a := a) (d := d) (n := n)

-- Translation under the homogeneous nucleus API.
example : apSum (fun x => f (x + a)) d n = apSumFrom f a d n := by
  simpa using apSum_shift_add (f := f) (k := a) (d := d) (n := n)

example : apSum (fun x => f (a + x)) d n = apSumFrom f a d n := by
  calc
    apSum (fun x => f (a + x)) d n = apSum (fun x => f (x + a)) d n := by
      simpa using apSum_shift_comm (f := f) (a := a) (d := d) (n := n)
    _ = apSumFrom f a d n := by
      simpa using apSum_shift_add (f := f) (k := a) (d := d) (n := n)

-- Translation under the offset nucleus API.
example : apSumOffset (fun x => f (x + a)) d m n = apSumFrom f (m * d + a) d n := by
  simpa using apSumOffset_shift_add (f := f) (k := a) (d := d) (m := m) (n := n)

-- Inverse orientation: normalize an affine tail with start `m*d + a` back into an offset sum
-- on a shifted sequence.
example : apSumFrom f (m * d + a) d n = apSumOffset (fun x => f (x + a)) d m n := by
  simpa using apSumFrom_tail_eq_apSumOffset_shift_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

example : apSumOffset (fun x => f (a + x)) d m n = apSumFrom f (a + m * d) d n := by
  calc
    apSumOffset (fun x => f (a + x)) d m n = apSumOffset (fun x => f (x + a)) d m n := by
      simpa using apSumOffset_shift_comm (f := f) (a := a) (d := d) (m := m) (n := n)
    _ = apSumFrom f (a + m * d) d n := by
      simpa using
        apSumOffset_shift_add_start_add_left (f := f) (k := a) (d := d) (m := m) (n := n)

example : apSumFrom f a d (m + n) - apSumFrom f a d m = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using apSumFrom_sub_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Step-one normal form: package the step size `d` into the summand.
example :
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSum (fun k => f (k * d + (a + m * d))) 1 n := by
  simpa using
    apSumFrom_sub_eq_apSum_step_one_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- Inequality normal form: subtracting two affine partial sums as a tail sum.
example (hmn : m ≤ n) :
    apSumFrom f a d n - apSumFrom f a d m = apSumFrom f (a + m * d) d (n - m) := by
  simpa using apSumFrom_sub_apSumFrom_eq_apSumFrom (f := f) (a := a) (d := d) (m := m) (n := n)
    hmn

-- Paper-notation fixed-length tail → nucleus offset normal form: rewrite
-- `∑ i ∈ Icc (m+1) (m+n), f (i*d + a)` directly to an `apSumOffset` on the shifted sequence.
example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d + a)) =
      apSumOffset (fun k => f (k + a)) d m n := by
  simpa using
    sum_Icc_eq_apSumOffset_shift_add_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Mul-left + translation-friendly variant: `f (d*i + a)`.
example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i + a)) =
      apSumOffset (fun k => f (k + a)) d m n := by
  simpa using
    sum_Icc_eq_apSumOffset_shift_add_mul_left_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Paper boundary bridge: keep paper summand `a + i*d` but normalize into the translation-friendly
-- offset normal form `k ↦ f (k + a)`.
example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d)) =
      apSumOffset (fun k => f (k + a)) d m n := by
  simpa using
    sum_Icc_eq_apSumOffset_shift_add_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- Mul-left variant of the paper boundary bridge: `a + d*i`.
example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + d * i)) =
      apSumOffset (fun k => f (k + a)) d m n := by
  simpa [Nat.mul_comm] using
    (sum_Icc_eq_apSumOffset_shift_add_left (f := f) (a := a) (d := d) (m := m) (n := n))

-- Paper-notation inequality normal form: `Icc (m+1) n` tails for affine sums.
example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d + a)) = apSumFrom f (a + m * d) d (n - m) := by
  simpa using
    sum_Icc_eq_apSumFrom_tail_of_le_add (f := f) (a := a) (d := d) (m := m) (n := n) hmn

-- Mul-left variants: `d * i` binder form.
example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (a + d * i)) = apSumFrom f (a + m * d) d (n - m) := by
  simpa using
    sum_Icc_eq_apSumFrom_tail_of_le_mul_left (f := f) (a := a) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (d * i + a)) = apSumFrom f (a + m * d) d (n - m) := by
  simpa using
    sum_Icc_eq_apSumFrom_tail_of_le_mul_left_add (f := f) (a := a) (d := d) (m := m) (n := n) hmn

example :
    apSumFrom f (a + m * d) d (n₁ + n₂) - apSumFrom f (a + m * d) d n₁ =
      apSumOffset (fun k => f (k + a)) d (m + n₁) n₂ := by
  simpa using
    apSumFrom_tail_sub_eq_apSumOffset_shift_add_tail (f := f) (a := a) (d := d) (m := m)
      (n1 := n₁) (n2 := n₂)

example : apSum f d (n + 1) = apSum f d n + f ((n + 1) * d) := by
  simpa using apSum_succ (f := f) (d := d) (n := n)

example : apSum f d (n + 1) = f d + apSumOffset f d 1 n := by
  simpa using apSum_succ_length (f := f) (d := d) (n := n)

example : apSumOffset f d 0 n = apSum f d n := by
  simp

-- Regression (Track B / step-factoring at a multiple start):
-- normalize `apSumFrom f (a*d) (k*d) n` directly into an `apSumOffset` on a shifted sequence.
example : apSumFrom f (a * d) (k * d) n = apSumOffset (fun t => f ((t + a) * d)) k 0 n := by
  simpa using
    (apSumFrom_mul_start_mul_step_eq_apSumOffset_shift_mul_right (f := f) (a₀ := a) (d₁ := k)
      (d₂ := d) (n := n))

example : apSumOffset f d m 0 = 0 := by
  simp

-- Single-term normal forms (useful when you want to peel a tail down to one summand).
example : apSumOffset f d m 1 = f ((m + 1) * d) := by
  simpa using apSumOffset_one (f := f) (d := d) (m := m)

example : apSumFrom f a d 1 = f (a + d) := by
  -- `apSumFrom` is the affine AP sum over `a + d, a + 2d, ...`.
  simpa using apSumFrom_one (f := f) (a := a) (d := d)

-- Degenerate constant AP tails.
example : apSumOffset f 0 m n = n • f 0 := by
  simp

example : apSumOffset f d m (n + 1) = f ((m + 1) * d) + apSumOffset f d (m + 1) n := by
  simpa using apSumOffset_succ_length (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f d m (n + 1) = apSumOffset f d m n + f ((m + n + 1) * d) := by
  simpa using apSumOffset_succ (f := f) (d := d) (m := m) (n := n)

example :
    apSumOffset f d m (n₁ + n₂) = apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
  simpa using apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

example : apSumOffset f d m n = apSum f d (m + n) - apSum f d m := by
  simpa using apSumOffset_eq_sub (f := f) (d := d) (m := m) (n := n)

-- Canonical “difference of partial sums” normal form: rewrite subtraction into a tail.
example : apSum f d (m + n) - apSum f d m = apSumOffset f d m n := by
  simpa using apSum_sub_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f d m n = apSum f d (m + n) - apSum f d m := by
  simpa using (apSum_sub_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)).symm

-- Variable upper endpoints often appear in surface statements. When `m ≤ n`, normalize
-- `∑ i ∈ Icc (m+1) n, ...` into the canonical tail length `n - m`.
example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) = apSumOffset f d m (n - m) := by
  simpa using sum_Icc_eq_apSumOffset_of_le (f := f) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    apSumOffset f d m (n - m) = (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) := by
  simpa using apSumOffset_eq_sum_Icc_of_le (f := f) (d := d) (m := m) (n := n) hmn

-- Translation-friendly `d * i` variants (avoid commuting multiplication under binders).
example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (d * i)) = apSumOffset f d m (n - m) := by
  simpa using sum_Icc_eq_apSumOffset_of_le_mul_left (f := f) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    apSumOffset f d m (n - m) = (Finset.Icc (m + 1) n).sum (fun i => f (d * i)) := by
  simpa using apSumOffset_eq_sum_Icc_of_le_mul_left (f := f) (d := d) (m := m) (n := n) hmn

-- If you want to eliminate `apSumOffset` entirely, normalize paper tails directly into an
-- `apSum` on a shifted sequence.
example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) = apSum (fun k => f (k + m * d)) d (n - m) := by
  simpa using sum_Icc_eq_apSum_shift_add_of_le (f := f) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (d * i)) = apSum (fun k => f (k + m * d)) d (n - m) := by
  simpa using sum_Icc_eq_apSum_shift_add_of_le_mul_left (f := f) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) : apSum f d n - apSum f d m = apSumOffset f d m (n - m) := by
  simpa using apSum_sub_apSum_eq_apSumOffset (f := f) (d := d) (m := m) (n := n) hmn

-- Same difference normal form, but rewrite the tail into a homogeneous AP sum on a shifted sequence.
example (hmn : m ≤ n) : apSum f d n - apSum f d m = apSum (fun k => f (k + m * d)) d (n - m) := by
  simpa using apSum_sub_apSum_eq_apSum_shift_add_of_le (f := f) (d := d) (m := m) (n := n) hmn

-- Canonical tail endpoints `Icc (m+1) (m+n)` simplify directly to `apSumOffset`.
example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) = apSumOffset f d m n := by
  simp

example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) = apSumOffset f d m n := by
  simp

-- Same difference normal form, but eliminate the offset parameter by shifting the underlying
-- sequence so the offset is `0`.
example (hmn : m ≤ n) :
    apSum f d n - apSum f d m = apSumOffset (fun k => f (k + m * d)) d 0 (n - m) := by
  simpa using
    apSum_sub_apSum_eq_apSumOffset_shift_add_of_le (f := f) (d := d) (m := m) (n := n) hmn

example : apSumOffset f d m n = apSumFrom f (m * d) d n := by
  simpa using apSumOffset_eq_apSumFrom (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f d m n = apSumOffset (fun k => f (k * d)) 1 m n := by
  simpa using apSumOffset_eq_apSumOffset_step_one (f := f) (d := d) (m := m) (n := n)

example : apSumOffset (fun k => f (k * d)) 1 m n = apSumOffset f d m n := by
  simpa using (apSumOffset_eq_apSumOffset_step_one (f := f) (d := d) (m := m) (n := n)).symm

example : apSumOffset f d m n = apSum (fun k => f ((m + k) * d)) 1 n := by
  simpa using apSumOffset_eq_apSum_step_one (f := f) (d := d) (m := m) (n := n)

-- Multiplication-on-the-left variant (avoids commuting `(_ * d)` under binders).
example : apSumOffset f d m n = apSum (fun k => f (d * (m + k))) 1 n := by
  simpa [Nat.mul_comm] using
    (apSumOffset_eq_apSum_step_one (f := f) (d := d) (m := m) (n := n))

-- Multiplication-on-the-left + translation-friendly variant: `k ↦ f (d*k + d*m)`.
example : apSumOffset f d m n = apSum (fun k => f (d * k + d * m)) 1 n := by
  simpa [Nat.mul_comm] using
    (apSumOffset_eq_apSum_step_one_add_left (f := f) (d := d) (m := m) (n := n))

example : apSum (fun k => f ((m + k) * d)) 1 n = apSumOffset f d m n := by
  simpa using (apSumOffset_eq_apSum_step_one (f := f) (d := d) (m := m) (n := n)).symm

-- A translation-friendly variant of the step-one form: `k ↦ f (k*d + m*d)`.
example : apSumOffset f d m n = apSum (fun k => f (k * d + m * d)) 1 n := by
  simpa using apSumOffset_eq_apSum_step_one_add_left (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f d m n = apSumOffset (fun k => f ((m + k) * d)) 1 0 n := by
  simpa using apSumOffset_eq_apSumOffset_step_one_zero_m (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f d m n = apSumOffset (fun k => f (k * d + m * d)) 1 0 n := by
  simpa using
    apSumOffset_eq_apSumOffset_step_one_zero_m_add_left (f := f) (d := d) (m := m) (n := n)

-- Multiplication-on-the-left, translation-friendly step-one normal form that stays inside the
-- offset nucleus API (`m = 0`).
example : apSumOffset f d m n = apSumOffset (fun k => f (d * k + d * m)) 1 0 n := by
  simpa [Nat.mul_comm] using
    (apSumOffset_eq_apSumOffset_step_one_zero_m_add_left (f := f) (d := d) (m := m) (n := n))

example : apSumOffset f d m n = apSum (fun k => f (m * d + k)) d n := by
  simpa using apSumOffset_eq_apSum_shift (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f d m n = apSum (fun k => f (k + m * d)) d n := by
  simpa using apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n := n)

-- A convenient normal form: eliminate the explicit offset parameter by shifting the underlying
-- sequence and resetting the offset to `0`.
example : apSumOffset f d m n = apSumOffset (fun k => f (k + m * d)) d 0 n := by
  simpa using apSumOffset_eq_apSumOffset_shift_add (f := f) (d := d) (m := m) (n := n)

example : apSumOffset (fun k => f (k + m * d)) d 0 n = apSumOffset f d m n := by
  simpa using apSumOffset_shift_add_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

-- Splitting a paper-notation tail sum into consecutive blocks matches the nucleus split lemma.
example :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d)) =
      (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d)) +
        (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) := by
  simpa using sum_Icc_add_length (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- One-cut bridge (paper → nucleus): split and immediately rewrite to `apSumOffset` blocks.
example :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d)) =
      apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
  simpa using
    sum_Icc_eq_apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Regression: paper-pretty right endpoint `m + n₁ + n₂` (no parentheses) compiles and rewrites.
example :
    (Finset.Icc (m + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) =
      apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
  simpa using
    sum_Icc_eq_apSumOffset_add_length_paper (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Translation-friendly `d * i` variant (avoids commuting multiplication under binders).
example :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (d * i)) =
      (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (d * i)) +
        (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (d * i)) := by
  simpa using
    sum_Icc_add_length_mul_left (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Paper difference normal form: subtracting the first block leaves the tail block.
example :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d)) -
        (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d)) =
      (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) := by
  simpa using
    sum_Icc_sub_sum_Icc_eq_sum_Icc (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Translation-friendly `d * i` variant (avoids commuting multiplication under binders).
example :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (d * i)) -
        (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (d * i)) =
      (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (d * i)) := by
  simpa using
    sum_Icc_sub_sum_Icc_eq_sum_Icc_mul_left (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Paper difference → nucleus normal form: convert directly to an `apSumOffset` tail.
example :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d)) -
        (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d)) =
      apSumOffset f d (m + n₁) n₂ := by
  simpa using
    sum_Icc_sub_sum_Icc_eq_apSumOffset (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Translation-friendly `d * i` variant (avoids commuting multiplication under binders).
example :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (d * i)) -
        (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (d * i)) =
      apSumOffset f d (m + n₁) n₂ := by
  simpa using
    sum_Icc_sub_sum_Icc_eq_apSumOffset_mul_left (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

/-!
### “Typical user script” regressions (paper statements → nucleus normal form)

These are intended to mimic how downstream files often look:
- start from an interval-sum statement (paper-friendly `Icc` endpoints)
- rewrite a *difference* of two such blocks into an `apSumOffset`
- immediately normalize the discrepancy wrapper via `simp` (to `discOffset`)

The goal is that these normalize with a single `simp`/`rw` pipeline when importing only
`MoltResearch.Discrepancy` (the stable surface).
-/

-- 1) Difference of paper blocks → `apSumOffset` (then `discOffset`) with no extra bookkeeping.
example :
    Int.natAbs (
        (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d)) -
          (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d))) =
      discOffset f d (m + n₁) n₂ := by
  simp [sum_Icc_sub_sum_Icc_eq_apSumOffset (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)]

-- 2) Same, but with an affine translation *after* the `i*d` (very common in paper statements).
example :
    Int.natAbs (
        (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (a + i * d)) -
          (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (a + i * d))) =
      discOffset (fun t => f (a + t)) d (m + n₁) n₂ := by
  -- First rewrite the *difference of blocks* to an `apSumOffset` tail, then let `simp`
  -- turn `Int.natAbs (apSumOffset …)` into `discOffset …`.
  simp [sum_Icc_sub_sum_Icc_eq_apSumOffset (f := fun t => f (a + t)) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)]

-- 3) “Tail length” form with variable upper endpoint: `m ≤ n` paper tail → `discOffset` tail.
example (hmn : m ≤ n) :
    Int.natAbs ((Finset.Icc (m + 1) n).sum (fun i => f (a + i * d))) =
      discOffset (fun t => f (a + t)) d m (n - m) := by
  simp [sum_Icc_eq_apSumOffset_of_le (f := fun t => f (a + t)) (d := d) (m := m) (n := n) hmn]

-- Variable upper endpoints often appear in surface statements. When `m ≤ k ≤ n`, split the
-- interval sum at `k`. 
example (k : ℕ) (hmk : m ≤ k) (hkn : k ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) =
      (Finset.Icc (m + 1) k).sum (fun i => f (i * d)) +
        (Finset.Icc (k + 1) n).sum (fun i => f (i * d)) := by
  simpa using sum_Icc_split_of_le (f := f) (d := d) (m := m) (k := k) (n := n) hmk hkn

-- Translation-friendly `d * i` variant (avoids commuting multiplication under binders).
example (k : ℕ) (hmk : m ≤ k) (hkn : k ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (d * i)) =
      (Finset.Icc (m + 1) k).sum (fun i => f (d * i)) +
        (Finset.Icc (k + 1) n).sum (fun i => f (d * i)) := by
  simpa using
    sum_Icc_split_of_le_mul_left (f := f) (d := d) (m := m) (k := k) (n := n) hmk hkn

-- Nucleus counterpart: when `m ≤ k ≤ n`, split the tail `apSumOffset f d m (n - m)` at `k`.
example (k : ℕ) (hmk : m ≤ k) (hkn : k ≤ n) :
    apSumOffset f d m (n - m) =
      apSumOffset f d m (k - m) + apSumOffset f d k (n - k) := by
  simpa using
    apSumOffset_eq_add_apSumOffset_of_le (f := f) (d := d) (m := m) (k := k) (n := n) hmk hkn

-- Pipeline example: paper interval sum → `apSumOffset`, then split via `apSumOffset_add_length`.
example (k : ℕ) (hmn : m ≤ n) (hmk : m ≤ k) (hkn : k ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) =
      apSumOffset f d m (k - m) + apSumOffset f d k (n - k) := by
  calc
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) = apSumOffset f d m (n - m) := by
      simpa using sum_Icc_eq_apSumOffset_of_le (f := f) (d := d) (m := m) (n := n) hmn
    _ = apSumOffset f d m ((k - m) + (n - k)) := by
      have hlen : n - m = (k - m) + (n - k) := by
        -- `n - k + (k - m) = n - m`; commute the LHS to match our `k - m + (n - k)` ordering.
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Nat.sub_add_sub_cancel hkn hmk).symm
      simpa [hlen]
    _ = apSumOffset f d m (k - m) + apSumOffset f d (m + (k - m)) (n - k) := by
      simpa using
        (apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := k - m) (n₂ := n - k))
    _ = apSumOffset f d m (k - m) + apSumOffset f d k (n - k) := by
      simpa [Nat.add_sub_of_le hmk]

-- Same pipeline, but in the translation-friendly `d * i` binder convention.
example (k : ℕ) (hmn : m ≤ n) (hmk : m ≤ k) (hkn : k ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (d * i)) =
      apSumOffset f d m (k - m) + apSumOffset f d k (n - k) := by
  calc
    (Finset.Icc (m + 1) n).sum (fun i => f (d * i)) = apSumOffset f d m (n - m) := by
      simpa using
        sum_Icc_eq_apSumOffset_of_le_mul_left (f := f) (d := d) (m := m) (n := n) hmn
    _ = apSumOffset f d m ((k - m) + (n - k)) := by
      have hlen : n - m = (k - m) + (n - k) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Nat.sub_add_sub_cancel hkn hmk).symm
      simpa [hlen]
    _ = apSumOffset f d m (k - m) + apSumOffset f d (m + (k - m)) (n - k) := by
      simpa using
        (apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := k - m) (n₂ := n - k))
    _ = apSumOffset f d m (k - m) + apSumOffset f d k (n - k) := by
      simpa [Nat.add_sub_of_le hmk]

-- Affine paper splitting: mul-left form `a + d*i`.
example :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (a + d * i)) =
      (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (a + d * i)) +
        (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (a + d * i)) := by
  simpa using
    sum_Icc_add_length_affine_mul_left (f := f) (a := a) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Affine paper splitting: mul-left + translation-friendly form `d*i + a`.
example :
    (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (d * i + a)) =
      (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (d * i + a)) +
        (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (d * i + a)) := by
  simpa using
    sum_Icc_add_length_affine_mul_left_add (f := f) (a := a) (d := d) (m := m) (n₁ := n₁)
      (n₂ := n₂)

-- Normal form: a later tail as a difference of a longer tail and its initial segment.
example :
    apSumOffset f d (m + n₁) n₂ = apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ := by
  simpa using apSumOffset_tail_eq_sub (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Normal form: difference of offset sums with the same `m` becomes a later tail.
example :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ = apSumOffset f d (m + n₁) n₂ := by
  simpa using apSumOffset_sub_eq_apSumOffset_tail (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Same difference normal form, but eliminate the tail offset parameter by shifting the underlying
-- sequence and resetting the offset to `0`.
example :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ =
      apSumOffset (fun k => f (k + (m + n₁) * d)) d 0 n₂ := by
  simpa using
    apSumOffset_sub_eq_apSumOffset_shift_add (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

-- Same difference normal form, but eliminate the explicit `apSumOffset` into an `apSum` on a
-- shifted sequence.
example :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ = apSum (fun k => f (k + (m + n₁) * d)) d n₂ := by
  simpa using apSumOffset_sub_eq_apSum_shift_add (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

example (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ = apSumOffset f d (m + n₁) (n₂ - n₁) := by
  simpa using
    apSumOffset_sub_apSumOffset_eq_apSumOffset (f := f) (d := d) (m := m) (n₁ := n₁)
      (n₂ := n₂) (hn := hn)

-- Same inequality normal form, but eliminate the offset parameter by shifting the underlying
-- sequence and resetting the offset to `0`.
example (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ =
      apSumOffset (fun k => f (k + (m + n₁) * d)) d 0 (n₂ - n₁) := by
  simpa using
    apSumOffset_sub_apSumOffset_eq_apSumOffset_shift_add (f := f) (d := d) (m := m) (n₁ := n₁)
      (n₂ := n₂) (hn := hn)

-- Same inequality normal form, but eliminate the explicit `apSumOffset` into an `apSum` on a
-- shifted sequence.
example (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ =
      apSum (fun k => f (k + (m + n₁) * d)) d (n₂ - n₁) := by
  simpa using
    apSumOffset_sub_apSumOffset_eq_apSum_shift_add (f := f) (d := d) (m := m) (n₁ := n₁)
      (n₂ := n₂) (hn := hn)

-- Splitting a longer tail into an initial segment plus a (normalized) later tail.
example (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ =
      apSumOffset f d m n₁ + apSumOffset f d (m + n₁) (n₂ - n₁) := by
  simpa using
    apSumOffset_eq_add_apSumOffset_tail (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)
      (hn := hn)

-- Split an offset sum at an interior cut `k` with `m ≤ k ≤ m+n`.
example {k : ℕ} (hmk : m ≤ k) (hkn : k ≤ m + n) :
    apSumOffset f d m n = apSumOffset f d m (k - m) + apSumOffset f d k (m + n - k) := by
  simpa using apSumOffset_split_at (f := f) (d := d) (m := m) (k := k) (n := n) hmk hkn

example :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ =
      (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) := by
  simpa using apSumOffset_sub_eq_sum_Icc (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

example (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ =
      (Finset.Icc (m + n₁ + 1) (m + n₂)).sum (fun i => f (i * d)) := by
  simpa using
    apSumOffset_sub_apSumOffset_eq_sum_Icc (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)
      (hn := hn)

-- Translation-friendly `d * i` variants (avoid commuting multiplication under binders).
example :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ =
      (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (d * i)) := by
  simpa using
    apSumOffset_sub_eq_sum_Icc_mul_left (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)

example (hn : n₁ ≤ n₂) :
    apSumOffset f d m n₂ - apSumOffset f d m n₁ =
      (Finset.Icc (m + n₁ + 1) (m + n₂)).sum (fun i => f (d * i)) := by
  simpa using
    apSumOffset_sub_apSumOffset_eq_sum_Icc_mul_left (f := f) (d := d) (m := m) (n₁ := n₁)
      (n₂ := n₂) (hn := hn)

example :
    apSum f d (m + n) - apSum f d m =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) := by
  simpa using apSum_sub_eq_sum_Icc (f := f) (d := d) (m := m) (n := n)

-- Translation-friendly `d * i` variant (avoids commuting multiplication under binders).
example :
    apSum f d (m + n) - apSum f d m =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) := by
  simpa using apSum_sub_eq_sum_Icc_mul_left (f := f) (d := d) (m := m) (n := n)

example :
    apSumOffset f d m n = (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) := by
  simpa using apSumOffset_eq_sum_Icc (f := f) (d := d) (m := m) (n := n)

-- Translation-friendly `d * i` variant (avoids commuting multiplication under binders).
example :
    apSumOffset f d m n = (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i)) := by
  simpa using apSumOffset_eq_sum_Icc_mul_left (f := f) (d := d) (m := m) (n := n)

-- Fixed-lower-endpoint (“length-indexed”) paper notation.
example : apSumOffset f d m n = (Finset.Icc 1 n).sum (fun i => f ((m + i) * d)) := by
  simpa using apSumOffset_eq_sum_Icc_length (f := f) (d := d) (m := m) (n := n)

example : (Finset.Icc 1 n).sum (fun i => f ((m + i) * d)) = apSumOffset f d m n := by
  simpa using sum_Icc_eq_apSumOffset_length (f := f) (d := d) (m := m) (n := n)

-- Translation-friendly `d * (m+i)` variant.
example : apSumOffset f d m n = (Finset.Icc 1 n).sum (fun i => f (d * (m + i))) := by
  simpa using apSumOffset_eq_sum_Icc_length_mul_left (f := f) (d := d) (m := m) (n := n)

example : (Finset.Icc 1 n).sum (fun i => f (d * (m + i))) = apSumOffset f d m n := by
  simpa using sum_Icc_eq_apSumOffset_length_mul_left (f := f) (d := d) (m := m) (n := n)

example : apSumOffset f 1 m n = (Finset.Icc (m + 1) (m + n)).sum f := by
  simpa using apSumOffset_one_d (f := f) (m := m) (n := n)

-- `d = 1` simp-friendly range normal forms (stable surface)
example : apSumOffset f 1 m n = (Finset.range n).sum (fun i => f (i + (m + 1))) := by
  simpa using apSumOffset_one_d_range (f := f) (m := m) (n := n)

example : apSumOffset f 1 m n = (Finset.range n).sum (fun i => f ((m + 1) + i)) := by
  simpa using apSumOffset_one_d_range_add_left (f := f) (m := m) (n := n)

example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) = apSumOffset f d m n := by
  simpa using sum_Icc_eq_apSumOffset (f := f) (d := d) (m := m) (n := n)

example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d)) = apSum f d (m + n) - apSum f d m := by
  simpa using sum_Icc_eq_apSum_sub (f := f) (d := d) (m := m) (n := n)

example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) = apSumOffset f d m (n - m) := by
  simpa using sum_Icc_eq_apSumOffset_of_le (f := f) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) = apSum f d n - apSum f d m := by
  simpa using sum_Icc_eq_apSum_sub_apSum_of_le (f := f) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    apSumOffset f d m (n - m) = apSum f d n - apSum f d m := by
  simpa using apSumOffset_eq_apSum_sub_apSum_of_le (f := f) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) : apSum f d n - apSum f d m = apSumOffset f d m (n - m) := by
  simpa using apSum_sub_apSum_eq_apSumOffset (f := f) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    apSum f d n - apSum f d m = (Finset.Icc (m + 1) n).sum (fun i => f (i * d)) := by
  simpa using apSum_sub_apSum_eq_sum_Icc (f := f) (d := d) (m := m) (n := n) hmn

example :
    (Finset.Icc 1 n).sum (fun i => f (a + i * d)) = apSumFrom f a d n := by
  simpa using sum_Icc_eq_apSumFrom (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = (Finset.Icc 1 n).sum (fun i => f (a + i * d)) := by
  simpa using apSumFrom_eq_sum_Icc (f := f) (a := a) (d := d) (n := n)

-- Translation-friendly paper notation: avoid commuting `a + …` under binders.
example : apSumFrom f a d n = (Finset.Icc 1 n).sum (fun i => f (i * d + a)) := by
  simpa using apSumFrom_eq_sum_Icc_add (f := f) (a := a) (d := d) (n := n)

example : (Finset.Icc 1 n).sum (fun i => f (i * d + a)) = apSumFrom f a d n := by
  simpa using sum_Icc_eq_apSumFrom_add (f := f) (a := a) (d := d) (n := n)

-- Affine start `a = 0` recovers the homogeneous AP sum.
example : apSumFrom f 0 d n = apSum f d n := by
  simpa using apSumFrom_zero_start (f := f) (d := d) (n := n)

example : apSumFrom f a 1 n = (Finset.Icc 1 n).sum (fun i => f (a + i)) := by
  simpa using apSumFrom_one_d (f := f) (a := a) (n := n)

-- `d = 1` simp-friendly range normal forms (stable surface)
example : apSumFrom f a 1 n = (Finset.range n).sum (fun i => f (i + (a + 1))) := by
  simpa using apSumFrom_one_d_range (f := f) (a := a) (n := n)

example : apSumFrom f a 1 n = (Finset.range n).sum (fun i => f ((a + 1) + i)) := by
  simpa using apSumFrom_one_d_range_add_left (f := f) (a := a) (n := n)

example : apSumFrom f a d (n + 1) = apSumFrom f a d n + f (a + (n + 1) * d) := by
  simpa using apSumFrom_succ (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d 0 = 0 := by
  simp

example : apSumFrom f a d (n + 1) = f (a + d) + apSumFrom f (a + d) d n := by
  simpa using apSumFrom_succ_length (f := f) (a := a) (d := d) (n := n)

example :
    apSumFrom f a d (n₁ + n₂) = apSumFrom f a d n₁ + apSumFrom f (a + n₁ * d) d n₂ := by
  simpa using apSumFrom_add_length (f := f) (a := a) (d := d) (m := n₁) (n := n₂)

example : apSumFrom f a d (m + n) = apSumFrom f a d m + apSumFrom f (a + m * d) d n := by
  simpa using apSumFrom_add_length (f := f) (a := a) (d := d) (m := m) (n := n)

example : apSumFrom f a 0 n = n • f a := by
  simp

-- Affine sums at `a = 0` are just homogeneous AP sums.
example : apSumFrom f 0 d n = apSum f d n := by
  simpa using apSumFrom_zero_start (f := f) (d := d) (n := n)

example : apSum f d n = apSumFrom f 0 d n := by
  simpa using apSum_eq_apSumFrom (f := f) (d := d) (n := n)

example : apSumFrom f a d n = apSum (fun k => f (k + a)) d n := by
  simpa using apSumFrom_eq_apSum_shift_add (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = apSum (fun k => f (a + k)) d n := by
  simpa using apSumFrom_eq_apSum_shift_add_left (f := f) (a := a) (d := d) (n := n)

-- Sometimes you want to package the translation as a map on the sequence `f` itself.
-- These lemmas commute the `+ a` past the multiplication inside the binder.
example : apSumFrom f a d n = apSum (fun x => f (x + a)) d n := by
  simpa using apSumFrom_eq_apSum_shift_add (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = apSum (fun x => f (a + x)) d n := by
  simpa using apSumFrom_eq_apSum_shift_add_left (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = apSum (fun k => f (a + k * d)) 1 n := by
  simpa using apSumFrom_eq_apSum_step_one (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = apSumOffset (fun k => f (a + k * d)) 1 0 n := by
  simpa using
    apSumFrom_eq_apSumOffset_step_one (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = apSumOffset (fun k => f (k * d + a)) 1 0 n := by
  simpa using
    apSumFrom_eq_apSumOffset_step_one_add_left (f := f) (a := a) (d := d) (n := n)

example : apSum (fun k => f (a + k * d)) 1 n = apSumFrom f a d n := by
  simpa using (apSumFrom_eq_apSum_step_one (f := f) (a := a) (d := d) (n := n)).symm

example : apSumFrom f a d n = apSum (fun k => f (k * d + a)) 1 n := by
  simpa using apSumFrom_eq_apSum_step_one_add_left (f := f) (a := a) (d := d) (n := n)

-- Canonical affine difference `(m+n) - m` as an offset sum on the shifted sequence.
example :
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using apSumFrom_sub_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Variable upper endpoints appear in surface statements.
-- When `m ≤ n`, normalize the difference `apSumFrom … n - apSumFrom … m` into the canonical tail
-- length `n - m` (in translation-friendly `k + a` form).
example (hmn : m ≤ n) :
    apSumFrom f a d n - apSumFrom f a d m = apSumOffset (fun k => f (k + a)) d m (n - m) := by
  simpa using
    apSumFrom_sub_apSumFrom_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)
      (hmn := hmn)

-- Same normalization, but eliminate the offset sum entirely into a homogeneous `apSum` on a
-- further-shifted sequence.
example (hmn : m ≤ n) :
    apSumFrom f a d n - apSumFrom f a d m = apSum (fun k => f (k + (a + m * d))) d (n - m) := by
  simpa using
    apSumFrom_sub_apSumFrom_eq_apSum_shift_add_of_le (f := f) (a := a) (d := d) (m := m) (n := n)
      (hmn := hmn)

-- Same `m ≤ n` normalization, but in step-one mul-left form (summand `d * k + const`).
example (hmn : m ≤ n) :
    apSumFrom f a d n - apSumFrom f a d m = apSum (fun k => f (d * k + (d * m + a))) 1 (n - m) := by
  simpa using
    apSumFrom_sub_apSumFrom_eq_apSum_step_one_mul_left_add_left_of_le (f := f) (a := a) (d := d)
      (m := m) (n := n) (hmn := hmn)

-- Regression example for the plain step-one mul-left lemma.
example (hmn : m ≤ n) :
    apSumFrom f a d n - apSumFrom f a d m = apSum (fun k => f (d * k + (m * d + a))) 1 (n - m) := by
  simpa using
    apSumFrom_sub_apSumFrom_eq_apSum_step_one_mul_left (f := f) (a := a) (d := d)
      (m := m) (n := n) (hmn := hmn)

-- Inverse orientation: normalize an `apSumOffset` tail sum on a shifted sequence back into a
-- difference of affine partial sums.
example (hmn : m ≤ n) :
    apSumOffset (fun k => f (k + a)) d m (n - m) = apSumFrom f a d n - apSumFrom f a d m := by
  simpa using
    apSumOffset_shift_add_eq_apSumFrom_sub_apSumFrom_of_le (f := f) (a := a) (d := d) (m := m)
      (n := n) (hmn := hmn)

-- Splitting an affine partial sum at an intermediate point, with the tail normalized into the
-- `apSumOffset` API on a shifted sequence.
example (hmn : m ≤ n) :
    apSumFrom f a d n = apSumFrom f a d m + apSumOffset (fun k => f (k + a)) d m (n - m) := by
  simpa using
    apSumFrom_eq_add_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)
      (hmn := hmn)

-- “Paper notation” for affine tails, in the translation-friendly `i*d + a` form.
example :
    apSumFrom f (a + m * d) d n =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d + a)) := by
  simpa using apSumFrom_tail_eq_sum_Icc_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Same tail paper notation, but in the mul-left `a + d*i` form.
example :
    apSumFrom f (a + m * d) d n =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + d * i)) := by
  simpa using apSumFrom_tail_eq_sum_Icc_mul_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- Same tail paper notation, in the mul-left + translation-friendly `d*i + a` form.
example :
    apSumFrom f (a + m * d) d n =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i + a)) := by
  simpa using
    apSumFrom_tail_eq_sum_Icc_mul_left_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Length-indexed paper notation for affine tails (fixed lower endpoint `1`).
example :
    apSumFrom f (a + m * d) d n =
      (Finset.Icc 1 n).sum (fun i => f (a + (m + i) * d)) := by
  simpa using apSumFrom_tail_eq_sum_Icc_length (f := f) (a := a) (d := d) (m := m) (n := n)

-- Translation-friendly length-indexed variant, with the summand written as `(m+i)*d + a`.
example :
    apSumFrom f (a + m * d) d n =
      (Finset.Icc 1 n).sum (fun i => f ((m + i) * d + a)) := by
  simpa using
    apSumFrom_tail_eq_sum_Icc_length_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Mul-left length-indexed variant (avoid commuting multiplication under binders): `a + d*(m+i)`.
example :
    apSumFrom f (a + m * d) d n =
      (Finset.Icc 1 n).sum (fun i => f (a + d * (m + i))) := by
  simpa using
    apSumFrom_tail_eq_sum_Icc_length_mul_left (f := f) (a := a) (d := d) (m := m) (n := n)

-- Mul-left + translation-friendly length-indexed variant: `d*(m+i) + a`.
example :
    apSumFrom f (a + m * d) d n =
      (Finset.Icc 1 n).sum (fun i => f (d * (m + i) + a)) := by
  simpa using
    apSumFrom_tail_eq_sum_Icc_length_mul_left_add (f := f) (a := a) (d := d) (m := m) (n := n)

-- Regression: normalize the paper-notation tail sum via `sum_Icc_eq_apSumFrom_tail`
-- and then `apSumFrom_tail_eq_apSumOffset_step_one` to the step-one offset normal form.
example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d)) =
      apSumOffset (fun k => f (a + k * d)) 1 m n := by
  calc
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d)) =
        apSumFrom f (a + m * d) d n := by
      simpa using (sum_Icc_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n := n))
    _ = apSumOffset (fun k => f (a + k * d)) 1 m n := by
      simpa using
        (apSumFrom_tail_eq_apSumOffset_step_one (f := f) (a := a) (d := d) (m := m) (n := n))

-- Variable upper endpoints appear often in surface statements.
-- When `m ≤ n`, normalize `∑ i ∈ Icc (m+1) n, f (i*d + a)` into the canonical tail length `n - m`.
example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (i * d + a)) =
      apSumFrom f (a + m * d) d (n - m) := by
  simpa using
    sum_Icc_eq_apSumFrom_tail_of_le_add (f := f) (a := a) (d := d) (m := m) (n := n) hmn

example : apSumFrom f (a + m * d) d n = apSum (fun k => f (a + (m + k) * d)) 1 n := by
  simpa using apSumFrom_tail_eq_apSum_step_one (f := f) (a := a) (d := d) (m := m) (n := n)

example : apSum (fun k => f (a + (m + k) * d)) 1 n = apSumFrom f (a + m * d) d n := by
  simpa using (apSumFrom_tail_eq_apSum_step_one (f := f) (a := a) (d := d) (m := m) (n := n)).symm

-- Head+tail normal form for affine tails: increment the tail parameter `m`.
example :
    apSumFrom f (a + m * d) d (n + 1) =
      f (a + (m + 1) * d) + apSumFrom f (a + (m + 1) * d) d n := by
  simpa using apSumFrom_tail_succ_length (f := f) (a := a) (d := d) (m := m) (n := n)

-- Same head+tail normal form, but with the remaining tail expressed as an `apSumOffset`.
example :
    apSumFrom f (a + m * d) d (n + 1) =
      f (a + (m + 1) * d) + apSumOffset (fun k => f (a + k)) d (m + 1) n := by
  simpa using
    apSumFrom_tail_succ_length_eq_add_apSumOffset_shift (f := f) (a := a) (d := d) (m := m)
      (n := n)

-- Translation-friendly variant (`k + a` inside binders, and `(m+1)*d + a` for the head term).
example :
    apSumFrom f (a + m * d) d (n + 1) =
      f ((m + 1) * d + a) + apSumOffset (fun k => f (k + a)) d (m + 1) n := by
  simpa using
    apSumFrom_tail_succ_length_eq_add_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m)
      (n := n)

example : apSumFrom f a d n = apSumOffset (fun k => f (a + k)) d 0 n := by
  simpa using apSumFrom_eq_apSumOffset_shift (f := f) (a := a) (d := d) (n := n)

example : apSumFrom f a d n = apSumOffset (fun k => f (k + a)) d 0 n := by
  simpa using apSumFrom_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (n := n)

example :
    apSumFrom f a d (m + n) - apSumFrom f a d m =
      apSumOffset (fun k => f (a + k)) d m n := by
  simpa using apSumFrom_sub_eq_apSumOffset_shift (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSumFrom f (a + m * d) d n := by
  simpa using apSumFrom_sub_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    apSumFrom f (a + m * d) d n = apSumFrom f a d (m + n) - apSumFrom f a d m := by
  simpa using apSumFrom_tail_eq_sub (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    apSumFrom f a d (m + n) - apSumFrom f a d m =
      apSumOffset (fun k => f (k + a)) d m n := by
  simpa using
    apSumFrom_sub_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d)) = apSumFrom f (a + m * d) d n := by
  simpa using sum_Icc_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n := n)

example (k : ℕ) (hmk : m ≤ k) (hkn : k ≤ m + n) :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d)) =
      (Finset.Icc (m + 1) k).sum (fun i => f (a + i * d)) +
        (Finset.Icc (k + 1) (m + n)).sum (fun i => f (a + i * d)) := by
  simpa using
    (sum_Icc_split_affine_of_le (f := f) (a := a) (d := d) (m := m) (k := k) (n := m + n) hmk hkn)

example :
    apSumFrom f a d (m + n) - apSumFrom f a d m =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d)) := by
  simpa using apSumFrom_sub_eq_sum_Icc (f := f) (a := a) (d := d) (m := m) (n := n)

-- Translation-friendly `d*i + a` surface form (avoid commuting multiplication under binders).
example :
    apSumFrom f a d (m + n) - apSumFrom f a d m =
      (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i + a)) := by
  simpa using
    apSumFrom_sub_eq_sum_Icc_mul_left_add (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (d * i + a)) =
      apSumFrom f a d (m + n) - apSumFrom f a d m := by
  simpa using
    sum_Icc_eq_apSumFrom_sub_mul_left_add (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    (Finset.Icc (m + 1) (m + n)).sum (fun i => f (a + i * d)) =
      apSumFrom f a d (m + n) - apSumFrom f a d m := by
  simpa using sum_Icc_eq_apSumFrom_sub (f := f) (a := a) (d := d) (m := m) (n := n)

example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (a + i * d)) = apSumFrom f (a + m * d) d (n - m) := by
  simpa using
    (sum_Icc_eq_apSumFrom_tail_of_le (f := f) (a := a) (d := d) (m := m) (n := n) hmn)

example (hmn : m ≤ n) :
    apSumFrom f (a + m * d) d (n - m) = apSumFrom f a d n - apSumFrom f a d m := by
  simpa using apSumFrom_tail_eq_sub_of_le (f := f) (a := a) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    apSumFrom f a d n - apSumFrom f a d m = (Finset.Icc (m + 1) n).sum (fun i => f (a + i * d)) := by
  simpa using apSumFrom_sub_apSumFrom_eq_sum_Icc (f := f) (a := a) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (a + i * d)) = apSumFrom f a d n - apSumFrom f a d m := by
  simpa using
    sum_Icc_eq_apSumFrom_sub_apSumFrom_of_le (f := f) (a := a) (d := d) (m := m) (n := n) hmn

example :
    apSumFrom f (a + m * d) d (n₁ + n₂) - apSumFrom f (a + m * d) d n₁ =
      apSumFrom f (a + (m + n₁) * d) d n₂ := by
  simpa using
    apSumFrom_tail_sub_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n1 := n₁)
      (n2 := n₂)

example :
    apSumFrom f (a + m * d) d (n₁ + n₂) - apSumFrom f (a + m * d) d n₁ =
      apSumOffset (fun k => f (a + k)) d (m + n₁) n₂ := by
  simpa using
    apSumFrom_tail_sub_eq_apSumOffset_shift_tail (f := f) (a := a) (d := d) (m := m) (n1 := n₁)
      (n2 := n₂)

example :
    apSumFrom f (a + m * d) d (n₁ + n₂) - apSumFrom f (a + m * d) d n₁ =
      apSumOffset (fun k => f (k + a)) d (m + n₁) n₂ := by
  simpa using
    apSumFrom_tail_sub_eq_apSumOffset_shift_add_tail (f := f) (a := a) (d := d) (m := m)
      (n1 := n₁) (n2 := n₂)

-- Further normalize tail-of-tail differences by absorbing the explicit offset into the translation.
example :
    apSumFrom f (a + m * d) d (n₁ + n₂) - apSumFrom f (a + m * d) d n₁ =
      apSumOffset (fun k => f (k + (a + (m + n₁) * d))) d 0 n₂ := by
  simpa using
    apSumFrom_tail_sub_eq_apSumOffset_shift_add_zero_m_tail (f := f) (a := a) (d := d) (m := m)
      (n1 := n₁) (n2 := n₂)

example :
    HasDiscrepancyAtLeast f C ↔
      ∃ d n : ℕ, d > 0 ∧ Int.natAbs (apSumOffset f d 0 n) > C := by
  simpa using HasDiscrepancyAtLeast_iff_exists_apSumOffset_zero_start (f := f) (C := C)

-- NEW (Track B / discOffset witness normal form): avoid exposing `Int.natAbs (apSumOffset …)`.
example :
    HasDiscrepancyAtLeast f C ↔
      ∃ d n : ℕ, d > 0 ∧ discOffset f d 0 n > C := by
  simpa using HasDiscrepancyAtLeast_iff_exists_discOffset_zero_start (f := f) (C := C)

example :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ,
        ∃ d n : ℕ,
          d ≥ 1 ∧ n > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C) := by
  simpa using forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos (f := f)

example :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ,
        ∃ d n : ℕ,
          d > 0 ∧ n > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C) := by
  simpa using forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos (f := f)

example :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔ (∀ C : ℕ, Nonempty (DiscrepancyWitnessPos f C)) := by
  simpa using forall_hasDiscrepancyAtLeast_iff_forall_nonempty_witnessPos (f := f)

example :
    (∀ C : ℕ, HasAffineDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ, Nonempty (AffineDiscrepancyWitnessPos f C)) := by
  simpa using forall_hasAffineDiscrepancyAtLeast_iff_forall_nonempty_witnessPos (f := f)

example :
    (∀ C : ℕ, HasAffineDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ,
        ∃ a d n : ℕ,
          d ≥ 1 ∧ n > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (a + i * d))) > C) := by
  simpa using
    forall_hasAffineDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos (f := f)

example :
    (∀ C : ℕ, HasAffineDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ,
        ∃ a d n : ℕ,
          d > 0 ∧ n > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (a + i * d))) > C) := by
  simpa using
    forall_hasAffineDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos (f := f)

example :
    (∀ C : ℕ, HasAffineDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ, ∃ a : ℕ, HasDiscrepancyAtLeast (fun k => f (a + k)) C) := by
  simpa using forall_hasAffineDiscrepancyAtLeast_iff_forall_exists_shift (f := f)

/-! ### Transform / reindexing regression tests -/

example (k : ℕ) : apSum (fun x => f (x * k)) d n = apSum f (d * k) n := by
  simpa using apSum_map_mul (f := f) (k := k) (d := d) (n := n)

-- Regression: reindex `apSumOffset` into the mapped-finset normal form.
example :
    apSumOffset f d m n =
      ((Finset.range n).map (affineEmbedding (m + 1) 1 (Nat.succ_pos 0))).sum
        (fun k => f (k * d)) := by
  simpa using (apSumOffset_reindex_affine (f := f) (d := d) (m := m) (n := n))

example (k : ℕ) : apSum (fun x => f (x + k)) d n = apSumFrom f k d n := by
  simpa using apSum_shift_add (f := f) (k := k) (d := d) (n := n)

example (k : ℕ) : apSum (fun x => f (k + x)) d n = apSumFrom f k d n := by
  calc
    apSum (fun x => f (k + x)) d n = apSum (fun x => f (x + k)) d n := by
      simpa using apSum_shift_comm (f := f) (a := k) (d := d) (n := n)
    _ = apSumFrom f k d n := by
      simpa using apSum_shift_add (f := f) (k := k) (d := d) (n := n)

example (k : ℕ) : apSumOffset (fun x => f (x + k)) d m n = apSumFrom f (k + m * d) d n := by
  simpa using apSumOffset_shift_add_start_add_left (f := f) (k := k) (d := d) (m := m) (n := n)

example (k : ℕ) : apSumOffset (fun x => f (k + x)) d m n = apSumFrom f (k + m * d) d n := by
  calc
    apSumOffset (fun x => f (k + x)) d m n = apSumOffset (fun x => f (x + k)) d m n := by
      simpa using apSumOffset_shift_comm (f := f) (a := k) (d := d) (m := m) (n := n)
    _ = apSumFrom f (k + m * d) d n := by
      simpa using
        apSumOffset_shift_add_start_add_left (f := f) (k := k) (d := d) (m := m) (n := n)

-- Regression: compose a shift-add reindexing with the offset→shift normal form.
example (k : ℕ) :
    apSumOffset (fun x => f (x + k)) d m n = apSum (fun x => f (x + (k + m * d))) d n := by
  simpa using apSumOffset_shift_add_eq_apSum_shift_add (f := f) (a := k) (d := d) (m := m)
    (n := n)

-- Add-left (`k + x`) variant of the same regression.
example (k : ℕ) :
    apSumOffset (fun x => f (k + x)) d m n = apSum (fun x => f ((k + m * d) + x)) d n := by
  simpa using
    apSumOffset_shift_add_left_eq_apSum_shift_add_left (f := f) (a := k) (d := d) (m := m) (n := n)

-- Regression: inverse orientation (rewrite a shifted homogeneous sum back into an offset sum).
example (k : ℕ) :
    apSum (fun x => f (x + (k + m * d))) d n = apSumOffset (fun x => f (x + k)) d m n := by
  simpa using apSum_shift_add_eq_apSumOffset_shift_add (f := f) (a := k) (d := d) (m := m) (n := n)

example (k C : ℕ) (hk : k > 0) :
    HasDiscrepancyAtLeast (fun x => f (x * k)) C → HasDiscrepancyAtLeast f C := by
  intro h
  exact HasDiscrepancyAtLeast.of_map_mul (f := f) (hk := hk) (h := h)

example (k C : ℕ) :
    HasDiscrepancyAtLeast (fun x => f (x + k)) C → HasAffineDiscrepancyAtLeast f C := by
  intro h
  exact HasDiscrepancyAtLeast.of_shift_add (f := f) (k := k) (C := C) h

-- Regression: witness-level offset-sum normal form for shifted discrepancy.
example (k C : ℕ) :
    HasDiscrepancyAtLeast (fun x => f (x + k)) C ↔
      ∃ d n : ℕ, d > 0 ∧ Int.natAbs (apSumOffset (fun x => f (x + k)) d 0 n) > C := by
  simpa using
    (HasDiscrepancyAtLeast_shift_add_iff_exists_apSumOffset_zero_start (f := f) (a := k) (C := C))

example (c : ℤ) (hc : c ≠ 0) (C : ℕ) :
    HasDiscrepancyAtLeast f C → HasDiscrepancyAtLeast (fun n => c * f n) C := by
  intro h
  exact HasDiscrepancyAtLeast.mul_left_of_ne_zero (f := f) (C := C) c hc h



-- A few regression-test examples for the affine/offset “glue” normal forms.
-- These are intentionally small: they protect the stable import surface
-- `import MoltResearch.Discrepancy` against accidental breakage.

variable (a d m n : ℕ)

-- Endpoint normalization for affine tails (variable upper endpoint).
-- These examples ensure callers can rewrite tails written as `a + i*d` without doing `Nat.add_comm` under binders.
example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (a + i * d)) =
      apSumOffset (fun k => f (k + a)) d m (n - m) := by
  simpa using
    sum_Icc_eq_apSumOffset_shift_add_of_le_left (f := f) (a := a) (d := d) (m := m) (n := n) hmn

example (hmn : m ≤ n) :
    (Finset.Icc (m + 1) n).sum (fun i => f (a + d * i)) =
      apSumOffset (fun k => f (k + a)) d m (n - m) := by
  simpa using
    sum_Icc_eq_apSumOffset_shift_add_of_le_left_mul_left (f := f) (a := a) (d := d) (m := m)
      (n := n) hmn

example : apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using apSumFrom_tail_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    apSumFrom f a d (m + n) - apSumFrom f a d m = apSumOffset (fun k => f (k + a)) d m n := by
  simpa using apSumFrom_sub_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n)

example :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ = apSumOffset (fun k => f (k + (m + n₁) * d)) d 0 n₂ := by
  simpa using apSumOffset_sub_eq_apSumOffset_shift_add (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)


-- Residue-class split normal forms (regression tests).

variable (q : ℕ)

example (hq : q > 0) :
    apSum f d (q * (n + 1)) =
      (Finset.range q).sum (fun r => f ((r + 1) * d) + apSumFrom f ((r + 1) * d) (q * d) n) := by
  simpa using apSum_mul_len_succ_eq_sum_range (f := f) (d := d) (q := q) (n := n) hq

example (hq : q > 0) :
    apSumOffset f d m (q * (n + 1)) =
      (Finset.range q).sum (fun r => f ((m + r + 1) * d) + apSumFrom f ((m + r + 1) * d) (q * d) n) := by
  simpa using apSumOffset_mul_len_succ_eq_sum_range (f := f) (d := d) (m := m) (q := q) (n := n) hq

example (hq : q > 0) :
    discOffset f d m (q * (n + 1)) =
      Int.natAbs ((Finset.range q).sum (fun r =>
        f ((m + r + 1) * d) + apSumFrom f ((m + r + 1) * d) (q * d) n)) := by
  simpa using discOffset_mul_len_succ_eq_natAbs_sum_range (f := f) (d := d) (m := m) (q := q) (n := n) hq


-- Bounds (regression tests): sign sequences give the expected triangle-inequality-style estimates.

variable (hf : IsSignSequence f)

example (hn : n₁ ≤ n₂) :
    Int.natAbs (apSumOffset f d m n₂ - apSumOffset f d m n₁) ≤ n₂ - n₁ := by
  simpa using
    hf.natAbs_apSumOffset_sub_apSumOffset_le (d := d) (m := m) (n₁ := n₁) (n₂ := n₂) hn

example : Int.natAbs (apSumOffset f d m n) ≤ n := by
  simpa using hf.natAbs_apSumOffset_le (d := d) (m := m) (n := n)

-- Track B regression test: offset concatenation normal form (sum level).
example (k : ℕ) :
    apSumOffset f d m (n + k) = apSumOffset f d m n + apSumOffset f d (m + n) k := by
  simpa using (apSumOffset_add_len (f := f) (d := d) (m := m) (n₁ := n) (n₂ := k))

example : Int.natAbs (apSumOffset f d m n - apSumOffset f d m n') ≤ n + n' := by
  have hsub :
      Int.natAbs (apSumOffset f d m n - apSumOffset f d m n') ≤
        Int.natAbs (apSumOffset f d m n) + Int.natAbs (apSumOffset f d m n') := by
    simpa using Int.natAbs_sub_le (apSumOffset f d m n) (apSumOffset f d m n')
  have hn : Int.natAbs (apSumOffset f d m n) ≤ n := by
    simpa using hf.natAbs_apSumOffset_le (d := d) (m := m) (n := n)
  have hn' : Int.natAbs (apSumOffset f d m n') ≤ n' := by
    simpa using hf.natAbs_apSumOffset_le (d := d) (m := m) (n := n')
  exact le_trans hsub (by gcongr)

example : Int.natAbs (apSum f d (m + n) - apSum f d m) ≤ n := by
  simpa using hf.natAbs_apSum_sub_le (d := d) (m := m) (n := n)


-- Bounds (regression tests): `B`-bounded sequences give the expected tail estimates.

variable (B : ℕ) (hB : ∀ k, Int.natAbs (f k) ≤ B)

example : Int.natAbs (apSumFrom f a d (m + n) - apSumFrom f a d m) ≤ n * B := by
  simpa using
    natAbs_apSumFrom_add_sub_apSumFrom_le_mul (f := f) (B := B) (hB := hB)
      (a := a) (d := d) (m := m) (n := n)


-- Witness normal forms (regression tests): `HasDiscrepancyAtLeast` ↔ paper-style interval witnesses.

variable (C : ℕ)

example : HasDiscrepancyAtLeast f C ↔
    ∃ d n : ℕ,
      d ≥ 1 ∧ n > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  simpa using
    (HasDiscrepancyAtLeast_iff_exists_sum_Icc_d_ge_one_witness_pos (f := f) (C := C))

example : (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔
    (∀ C : ℕ,
      ∃ d n : ℕ,
        d ≥ 1 ∧ n > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C) := by
  simpa using
    (forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos (f := f))

-- Track B regression test: fixed-step discrepancy (`along d`) rewrites to `discOffset` witnesses.

variable (d m : ℕ)

example : HasDiscrepancyAtLeastAlong (fun k => f (k + m * d)) d C ↔ (∃ n : ℕ, C < discOffset f d m n) := by
  simpa using
    (HasDiscrepancyAtLeastAlong.shift_mul_iff_exists_discOffset_lt (f := f) (d := d) (m := m) (C := C))

/-!
## `disc` wrapper regression tests

These ensure the homogeneous wrapper `disc` stays coherent with the offset wrapper `discOffset`.
-/

example (f : ℕ → ℤ) (d n₁ n₂ : ℕ) :
    disc f d (n₁ + n₂) ≤ disc f d n₁ + discOffset f d n₁ n₂ := by
  simpa using (disc_add_length_le (f := f) (d := d) (n₁ := n₁) (n₂ := n₂))

example (f : ℕ → ℤ) (hf : IsSignSequence f) (d n : ℕ) :
    disc f d n ≤ n := by
  simpa using (disc_le (hf := hf) (d := d) (n := n))

/-!
## Step-factor coherence regression tests

These are compile-time sanity checks that downstream code can “factor the step” at the discrepancy
level (staying in `discOffset` normal form, without unfolding `Int.natAbs`).
-/

example (f : ℕ → ℤ) (d₁ d₂ m n : ℕ) :
    discOffset f (d₁ * d₂) m n = discOffset (fun t => f (t * d₁)) d₂ m n := by
  simpa using
    (discOffset_mul_eq_discOffset_map_mul₁₂ (f := f) (d₁ := d₁) (d₂ := d₂) (m := m) (n := n))

end NormalFormExamples

end MoltResearch
