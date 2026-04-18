# Educational Overlays for Canonical Modules

This file provides concise pedagogical context for key canonical modules.
The goal is to pair verified artifacts with learning scaffolding.

## `MoltResearch/Basics.lean`

- **Intuition:** basic algebraic and logical rewrites are the smallest reusable units in larger formal proofs.
- **Proof sketch pattern:** start from `simp` and `rw`; isolate one transform per line when readability drops.
- **Common pitfalls:** overusing automation before introducing necessary local hypotheses.
- **Related tasks:** `T0_01`, `T0_03`.

## `MoltResearch/Logic.lean`

- **Intuition:** proposition-level transformations (`→`, `∧`, `∨`, `¬`) create glue lemmas used across domains.
- **Proof sketch pattern:** `intro` hypotheses early, then `constructor` / `cases` to mirror logical structure.
- **Common pitfalls:** proving a stronger statement than needed and getting stuck in mismatched goals.
- **Related tasks:** `T0_07`, `T0_11`.

## `MoltResearch/Discrepancy/Basic.lean`

- **Intuition:** foundational discrepancy definitions and small bounds let later modules reuse a common vocabulary.
- **Proof sketch pattern:** normalize definitions first, then prove small local inequalities and compose.
- **Common pitfalls:** jumping into advanced lemmas before reducing to canonical definitions.
- **API note (wrapper naming coherence):** there are two homogeneous discrepancy wrappers:
  - `discrepancy f d n` (readable name), and
  - `disc f d n` (matches the `discOffset` / `discOffsetUpTo` family).
  They are definitionally equal; use `discrepancy_eq_disc` / `disc_eq_discrepancy` when you want to normalize one spelling to the other without unfolding.

  For definitional unfolding, prefer the explicit lemmas `discrepancy_eq_natAbs_apSum` / `disc_eq_natAbs_apSum` over the shorter `*_def` aliases. Similarly, for offsets prefer `discOffset_eq_natAbs_apSumOffset` (the older `discOffset_def` alias is deprecated).

  **Argument-order coherence:** `apSumFrom` uses `(a d n)` (“start, step, length”), while the historical offset nucleus uses `apSumOffset f d m n`. When you want to line up parameters across the affine/offset nuclei, use the definitional aliases `apSumOffset' f m d n`, `discOffset' f m d n`, and `discOffsetUpTo' f m d N`.
- **API note (triangle vs reverse triangle):** for concatenation, `discOffset_add_le` is the forward triangle inequality. The reverse-triangle companions are `discOffset_left_le_add` / `discOffset_right_le_add`, proved by rewriting `S(n₁) = S(n₁+n₂) - S'(n₂)` and applying `Int.natAbs_sub_le`.
- **API note (endpoint-algebra wrappers):** three-segment concatenation is available as `discOffset_add_add_le`, but downstream goals often appear with right-associated endpoints. Use `discOffset_add_add_le_assoc` when your goal has length `n₁ + (n₂ + n₃)` and/or third-start index `m + (n₁ + n₂)` so you can `simpa` without manual `Nat.add_assoc` reassociation.
- **API note:** `discOffsetUpTo` is monotone in the cutoff. Use `discOffsetUpTo_mono` for an arbitrary `N ≤ N'`, or the convenience wrapper `discOffsetUpTo_le_add` for the common “extend by `K`” case `N ≤ N+K`.
  If your goal is stated with `Nat.succ N` instead of `N+1`, use the wrapper `discOffsetUpTo_le_succNat`.
- **API note (tail concatenation, max-level):** for later Tao2015 bookkeeping, prefer the wrapper
  `discOffsetUpTo_tail_concat_le`:
  `discOffsetUpTo f d m (N+K) ≤ discOffsetUpTo f d m N + discOffsetUpTo f d (m+N) K`.
  It is just a stable-name wrapper around `discOffsetUpTo_add_le_add_discOffsetUpTo`, but avoids downstream proofs having to remember that name.
- **API note (Lipschitz step):** for sign sequences, the one-step cutoff bound is `discOffsetUpTo_succ_le_add_one`:
  `discOffsetUpTo f d m (N+1) ≤ discOffsetUpTo f d m N + 1`. The reverse direction (monotonicity) is `discOffsetUpTo_le_succ`.
- **API note (bounding a fixed tail):** to bound a particular `discOffset f d m n` by the max cutoff at the *same* `n`, use `discOffset_le_discOffsetUpTo_self` (it’s just the `N = n` specialization, so you don’t have to write `le_rfl`).
- **API note (boundedness ↔ max-level nucleus, finite length):** for the finite-length “along `d`” predicate,
  `BoundedDiscrepancyAlong f d len B` is equivalent to the single inequality
  `discOffsetUpTo f d 0 len ≤ B` via `boundedDiscrepancyAlong_iff_discOffsetUpTo_le`.
  This is the bridge that lets later steps rewrite boundedness hypotheses into a one-line max bound.
- **API note (max recursion):** when you need to peel the last case off a cutoff, rewrite `discOffsetUpTo f d m (N+1)` using `discOffsetUpTo_succ` to get a clean `max (discOffsetUpTo … N) (discOffset … (N+1))` normal form.
- **API note (step positivity):** when extracting unboundedness witnesses, prefer the `Nat.succ` normal forms (`HasDiscrepancyAtLeast.exists_witness_succ(_pos)` and the affine analogue) so you can work with a concrete positive step without carrying a separate `d ≥ 1` side condition.
  The degenerate corner case `d = 0` also has stable-surface simp normal forms:
  - `apSum_zero_step`: `apSum f 0 n = (n : ℤ) * f 0`
  - `apSumOffset_zero_step`: `apSumOffset f 0 m n = (n : ℤ) * f 0`
  - `discOffset_zero_step`: `discOffset f 0 m n = Int.natAbs ((n : ℤ) * f 0)`
- **API note (monotone-in-`C`):** `HasDiscrepancyAtLeast f C` is **antitone** in `C` (the witness inequality is `> C`).
  Use `HasDiscrepancyAtLeast.mono` to *lower* the bound, and the contrapositive lemma
  `HasDiscrepancyAtLeast.not_mono` to *raise* bounds under negation (useful for boundedness normal forms).
- **API note (degenerate parameters for `UpTo`):** in downstream goals, you often want to normalize away “spurious” degenerate parameters without unfolding the finitary `Finset.sup` definition. The stable surface exports simp lemmas for:
  - `discOffsetUpTo f d m 0 = 0`
  - `discOffsetUpTo f d 0 N = discUpTo f d N`
  - step-one shift: `discOffsetUpTo f 1 m N = discUpTo (fun k => f (k + m)) 1 N`
  - dilation/coarsening: `discOffsetUpTo (fun k => f (q*k)) d m N = discOffsetUpTo f (q*d) m N`
  - if you want to pull a factor `q` into the step *at the wrapper level* (without unfolding the `Finset.sup`), use the rewrite lemmas
    `discOffsetUpTo_map_mul_right` / `discOffsetUpTo_map_mul_left` (and their `discOffset_*` analogues),
    which package the `((m+i+1)*d)*q = (m+i+1)*(d*q)` index normalization.
    For cutoff scaling bookkeeping, use `discOffsetUpTo_le_mul` (monotonicity under `N ↦ N*q`, assuming `q > 0`).
- **API note (start-shift vs sequence-shift, max-level):** if you want to “advance the start” without pushing arithmetic through the `Finset.sup` definition, rewrite using
  `discOffsetUpTo_add_start`:
  `discOffsetUpTo f d (m + k) N = discOffsetUpTo (fun t => f (t + k*d)) d m N`.
- **API note (max-level congruence wrappers):** when you have pointwise agreement of two sequences on the tail indices that can occur up to cutoff `N`, you can rewrite `discOffsetUpTo` without unfolding the outer `Finset.range`/`Finset.sup` using:
  - `discOffsetUpTo_congr` (hypothesis over `i < N+1` on indices `(m+i+1)*d`)
  - `discOffsetUpTo_congr_le` (hypothesis over `i ≤ N+1` on indices `(m+i)*d`)
- **API note (degenerate length for `apSupport`):** when writing support-form hypotheses (agreement on `apSupport d m n`), the base case `n = 0` should reduce immediately. Use the simp lemma `apSupport_zero` to rewrite `apSupport d m 0` to `∅`.
- **API note (`apSupport` bookkeeping helpers):** for common “no-op” shifts/dilations, the stable surface provides simp lemmas
  `apSupport_add_left_zero` and `apSupport_mul_right_one` so `simp` can discharge trivial `m+0` / `d*1` noise without unfolding.
  For unfold-free membership reasoning, use `mem_apSupport_iff`, or the binder-notation variant `mem_apSupport` when you want to feed the result directly to `simp`/`rcases` as `∃ i < n, ...`.
  If you want the *paper endpoint convention* (`m < i ∧ i ≤ m+n` with accessed index `i*d`), use `mem_apSupport_iff_exists_endpoints`.
  If you want to expose the underlying `Finset.range` image form of the support (to map/filter/count over it) without unfolding the definition, rewrite via `apSupport_eq_image_range`.
- **API note (`apSupport` canonical membership):** if your membership goal is already in the normal form
  `((m + i + 1) * d) ∈ apSupport d m n`, and you have `hd : d > 0`, then `simp [mem_apSupport_index_iff (m := m) (n := n) (i := i) hd]` reduces it to the expected bound `i < n`.
- **API note (`apSupport` size / no collisions):** if you need a cardinality statement, use `card_apSupport (m := m) (n := n) (hd := hd)` to rewrite
  `(apSupport d m n).card = n` (the proof is by injectivity of `i ↦ (m+i+1)*d` when `d > 0`).
- **API note (shift–dilation coherence):** when you both (i) push an offset shift into the summand and (ii) pull a factor `q` into the step, use the commutation lemma `apSumOffset_shift_mul_right_comm` (and the wrapper `discOffset_shift_mul_right_comm`) to avoid redoing index algebra. Conceptually: “shift then dilate” = “dilate then shift (with scaled offset)”.
- **API note (paper interval normalization):** many downstream proofs naturally produce paper-style terms like `Int.natAbs ((Finset.Icc (m+1) (m+n)).sum ...)`. The stable surface exports simp lemmas rewriting these directly to `discOffset f d m n`, so endpoint algebra can be normalized by `simp` without manually rewriting `discOffset_eq_natAbs_sum_Icc` back and forth.
- **API note (affine interval sum → `apSumOffset`):** if you have an interval sum with an extra affine offset in the summand,
  `∑ i ∈ Finset.Icc (m+1) (m+n), f (a + i*d)`,
  rewrite it in one shot using `sum_Icc_affine_eq_apSumOffset` to
  `apSumOffset (fun k => f (a + k)) d m n`.
  This is the “Icc↔offset sum normal form (affine endpoints)” Track B checklist item.
- **API note (endpoint normalization):** when you have endpoint-style constraints in a `Finset.Icc` form, you can convert cleanly to the paper-style conjunction used by `discOffset_congr_endpoints`. Use `endpoints_lt_le_iff_mem_finset_Icc` to rewrite
  `m < i ∧ i ≤ m+n` ↔ `i ∈ Finset.Icc (m+1) (m+n)`, and `endpoints_lt_le_iff_succ_le_lt_succ` for the variant `m+1 ≤ i ∧ i < m+n+1`.
- **API note (endpoint arithmetic normalization):** when your upper endpoint algebra is off by a “successor/pred” shim (common after `Nat.succ`/`Nat.pred` normalizations), use
  `add_one_add_pred_eq_add` / `add_pred_add_one_eq_add` (both require `0 < n`) to normalize `m+1+(n-1)` (or `m+(n-1)+1`) back to `m+n`.
  We *do not* add generic associativity/commutativity theorems to the simp set here: that tends to loop. Keep these helper lemmas explicit.
- **Related tasks:** `T1_01`, `T1_07`, `T1_12`.
