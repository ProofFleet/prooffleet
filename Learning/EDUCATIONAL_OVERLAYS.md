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

- **API note (`discAlong` ↔ `discOffset` bridge):** `discAlong f d n` is the “no-offset” specialization
  `discOffset f d 0 n`. Use the stable-name wrapper-level bridge lemmas to rewrite between these normal
  forms **without unfolding**:
  - `discAlong_eq_discOffset` (rewrite `discAlong` → `discOffset … 0 …`),
  - `discOffset_zero_eq_discAlong` (rewrite `discOffset … 0 …` → `discAlong`).

  These are intentionally *not* `[simp]` lemmas, since the discrepancy API contains other bridge lemmas
  that can interact to create simp loops.

- **API note (homogeneous cut at `k ≤ n`):** if you want to cut a homogeneous AP sum/discrepancy without rewriting into an offset normal form, use:
  - `apSum_eq_add_apSumOffset_cut` / `apSum_sub_apSum_cut` for exact prefix+tail / tail-difference statements, and
  - `disc_cut_le` for the one-line triangle bound
    `disc f d n ≤ disc f d k + discOffset f d k (n-k)`.

  For definitional unfolding, prefer the explicit lemmas `discrepancy_eq_natAbs_apSum` / `disc_eq_natAbs_apSum` over the shorter `*_def` aliases. Similarly, for offsets prefer `discOffset_eq_natAbs_apSumOffset` (the older `discOffset_def` alias is deprecated).

  **Degenerate step (`d = 0`) convention:** `d = 0` is **allowed** (not forbidden) and the stable surface provides terminating `[simp]` normal forms so downstream goals don't get stuck in the corner case. Typical normal forms:
  - `apSum f 0 n` and `apSumOffset f 0 m n` simplify to constant-sums
  - `disc f 0 n` / `discrepancy f 0 n` / `discOffset f 0 m n` simplify to `n * Int.natAbs (f 0)`
    (see the stable-surface simp lemmas `disc_zero_step` / `discrepancy_zero_step` / `discOffset_zero_step`).
  - `discUpTo f 0 N` / `discOffsetUpTo f 0 m N` simplify to a `Finset.sup` of the same multiplicative form

  **Argument-order coherence:** `apSumFrom` uses `(a d n)` (“start, step, length”), while the historical offset nucleus uses `apSumOffset f d m n`. When you want to line up parameters across the affine/offset nuclei, use the definitional aliases `apSumOffset' f m d n`, `discOffset' f m d n`, and `discOffsetUpTo' f m d N`.
- **API note (reverse/reindex normal form, sum-level):** if you need to “reverse the order” of an offset AP sum without doing raw `Finset` algebra, use
  `apSumOffset_eq_sum_range_reverse`:
  `apSumOffset f d m n = ∑ i in range n, f ((m + (n - i)) * d)`.
  This packages the standard `range` reflection (`i ↦ n-1-i`) and simplifies the index to the clean `n - i` form.
- **API note (triangle vs reverse triangle):** for concatenation, `discOffset_add_le` is the forward triangle inequality. The reverse-triangle companions are `discOffset_left_le_add` / `discOffset_right_le_add`, proved by rewriting `S(n₁) = S(n₁+n₂) - S'(n₂)` and applying `Int.natAbs_sub_le`.
- **API note ("cut then shift" coherence):** when you’re building longer normal-form pipelines, you often want to commute:
  1) a tail cut (rewrite a tail as a difference of a longer sum and its prefix), and
  2) a start-shift (`m ↦ m + k`) pushed into the summand as `t ↦ t + k*d`.

  Use:
  - `apSumOffset_tail_add_start_coherent` for the sum-level normal form, and
  - `discOffset_tail_add_start_eq_natAbs_sub` / `discOffset_tail_add_start_le` for the discrepancy-level normal form + triangle bound,

  so downstream code can reorder these rewrites and apply `discOffset_*` bounds **without** unfolding definitions or redoing index algebra.
- **API note (endpoint-algebra wrappers):** three-segment concatenation is available as `discOffset_add_add_le`, but downstream goals often appear with right-associated endpoints. Use `discOffset_add_add_le_assoc` when your goal has length `n₁ + (n₂ + n₃)` and/or third-start index `m + (n₁ + n₂)` so you can `simpa` without manual `Nat.add_assoc` reassociation.
- **API note:** `discOffsetUpTo` is monotone in the cutoff. Use `discOffsetUpTo_mono` for an arbitrary `N ≤ N'`, or the convenience wrapper `discOffsetUpTo_le_add` for the common “extend by `K`” case `N ≤ N+K`.
  If your goal is stated with `Nat.succ N` instead of `N+1`, use the wrapper `discOffsetUpTo_le_succNat`.

- **API note (residue-class `UpTo` bridge):** the wrapper `discOffsetUpTo_modEq f d m N q r` packages
  “take the maximum discrepancy over `n ≤ N` in the residue class `n ≡ r [MOD q]`”. When you want to
  compare it to the unrestricted max, use the wrapper lemma
  `discOffsetUpTo_modEq_le_discOffsetUpTo`.
- **API note (argmax witness for `discOffsetUpTo`):** the lemma
  `exists_discOffset_eq_discOffsetUpTo` returns a witness `n ≤ N` together with
  the *argmax* comparison fact `∀ n' ≤ N, discOffset … n' ≤ discOffset … n`, and
  an equality oriented as `discOffsetUpTo … N = discOffset … n`.
  Pattern: `rcases exists_discOffset_eq_discOffsetUpTo … with ⟨n, hnle, hnEq, hmax⟩`;
  then `simpa [hnEq]` rewrites the max value to the chosen witness, and `hmax`
  supplies all “≤ maximizer” inequalities without redoing `Finset.sup` reasoning.

- **API note (endpoint normalization in `discOffsetUpTo` witnesses):** after extracting a witness `n ≤ N`, goals/hypotheses often contain endpoint algebra like
  `n ≤ r*(N+1)` / `n < r*(N+1)` (or commuted `((N+1)*r)` forms). Use the stable-surface simp wrappers in `MoltResearch/Discrepancy/Basic.lean` to normalize these to the right-associated form
  `n ≤ r*N + r` / `n < r*N + r` so downstream `simp`/`linarith` steps can match other lemmas without manual `Nat.mul_add`/`Nat.add_assoc` rewriting.

- **API note (single-witness strict inequality, max-level):** if you *only* need a witness for a strict inequality (rather than an argmax + comparison), use
  `lt_discOffsetUpTo_iff_exists_lt_discOffset`:
  `C < discOffsetUpTo f d m N ↔ ∃ n ≤ N, C < discOffset f d m n`.
  This is often the cleanest way to move between “max over a finite set” and “∃ witness” without unfolding `Finset.sup`.
- **API note (tail concatenation, max-level):** for later Tao2015 bookkeeping, prefer the wrapper
  `discOffsetUpTo_tail_concat_le`:
  `discOffsetUpTo f d m (N+K) ≤ discOffsetUpTo f d m N + discOffsetUpTo f d (m+N) K`.
  It is just a stable-name wrapper around `discOffsetUpTo_add_le_add_discOffsetUpTo`, but avoids downstream proofs having to remember that name.
- **API note (Lipschitz step):** for sign sequences, the one-step cutoff bound is `discOffsetUpTo_succ_le_add_one`:
  `discOffsetUpTo f d m (N+1) ≤ discOffsetUpTo f d m N + 1`. The reverse direction (monotonicity) is `discOffsetUpTo_le_succ`.
- **API note (sign sequences under reindexing):** once you have `hf : IsSignSequence f`, you should not re-prove the pointwise `{±1}` bound after shifting/dilating indices. Use:
  - additive shift (`n ↦ n + k`): `IsSignSequence.shift_add (f := f) k hf` (or dot-notation `hf.shift_add' k`),
  - multiplicative dilation (`n ↦ n * k`): `IsSignSequence.map_mul (f := f) k hf` (or dot-notation `hf.map_mul' k`).
  These are intended as lightweight hypothesis-transport wrappers for later normal-form pipelines.
- **API note (bounding a fixed tail):** to bound a particular `discOffset f d m n` by the max cutoff at the *same* `n`, use `discOffset_le_discOffsetUpTo_self` (it’s just the `N = n` specialization, so you don’t have to write `le_rfl`).
- **API note (boundedness ↔ max-level nucleus, finite length):** for the finite-length “along `d`” predicate,
  `BoundedDiscrepancyAlong f d len B` is equivalent to the single inequality
  `discOffsetUpTo f d 0 len ≤ B` via `boundedDiscrepancyAlong_iff_discOffsetUpTo_le`.
  This is the bridge that lets later steps rewrite boundedness hypotheses into a one-line max bound.
- **API note (exists-bound normal form, `discOffsetUpTo`):** if you want the *existential* boundedness normal form (there exists a uniform bound over all cutoffs), use
  `boundedDiscOffsetExists_iff_exists_forall_discOffsetUpTo_le`:
  `BoundedDiscOffsetExists f d m ↔ ∃ B, ∀ N, discOffsetUpTo f d m N ≤ B`.
  This packages the fixed-`B` bridge `boundedDiscOffset_iff_forall_discOffsetUpTo_le` into a single ergonomic equivalence.

- **API note (translation invariance in `m`, boundedness-level):** to reset the start parameter to the
  normal form `m := 0`, use `boundedDiscOffset_shift_mul_start`:
  `BoundedDiscOffset f d m B ↔ BoundedDiscOffset (fun k => f (k + m*d)) d 0 B`.
  This is proved via the stable normal form `discOffset_eq_discrepancy_shift_mul`, so downstream code
  can perform the rewrite without unfolding `discOffset`.

- **API note (boundedness bridge, `UpTo` ↔ witnesses):** when you want to move *a fixed bound* `B` between the two quantifier normal forms,
  - `(∀ N, discOffsetUpTo f d m N ≤ B)` and
  - `(∀ n, discOffset f d m n ≤ B)`,
  use `forall_discOffsetUpTo_le_iff_forall_discOffset_le`.
  The directional lemmas `forall_discOffset_le_of_forall_discOffsetUpTo_le` and
  `forall_discOffsetUpTo_le_of_forall_discOffset_le` are convenient when you want to stay in implication form.
- **API note (max recursion):** when you need to peel the last case off a cutoff, rewrite `discOffsetUpTo f d m (N+1)` using `discOffsetUpTo_succ` to get a clean `max (discOffsetUpTo … N) (discOffset … (N+1))` normal form.
- **API note (step positivity):** when extracting unboundedness witnesses, prefer the `Nat.succ` normal forms (`HasDiscrepancyAtLeast.exists_witness_succ(_pos)` and the affine analogue) so you can work with a concrete positive step without carrying a separate `d ≥ 1` side condition.
  The degenerate corner case `d = 0` also has stable-surface simp normal forms:
  - `apSum_zero_step`: `apSum f 0 n = (n : ℤ) * f 0`
  - `apSumOffset_zero_step`: `apSumOffset f 0 m n = (n : ℤ) * f 0`
  - `discOffset_zero_step`: `discOffset f 0 m n = Int.natAbs ((n : ℤ) * f 0)`
- **API note (monotone-in-`C`):** `HasDiscrepancyAtLeast f C` is **antitone** in `C` (the witness inequality is `> C`).
  Use `HasDiscrepancyAtLeast.mono` to *lower* the bound, and the contrapositive lemma
  `HasDiscrepancyAtLeast.not_mono` to *raise* bounds under negation (useful for boundedness normal forms).
- **API note (boundedness monotonicity, `B`):** for the boundedness predicates,
  `BoundedDiscOffset f d m B` and `BoundedDiscrepancyAlong f d len B` are monotone in the bound parameter `B`.
  Use `BoundedDiscOffset.mono_B` / `BoundedDiscrepancyAlong.mono_B` to enlarge bounds, and the contrapositive
  helpers `BoundedDiscOffset.not_mono_B` / `BoundedDiscrepancyAlong.not_mono_B` to shrink bounds under negation.
- **API note (degenerate parameters for `UpTo`):** in downstream goals, you often want to normalize away “spurious” degenerate parameters without unfolding the finitary `Finset.sup` definition. The stable surface exports simp lemmas for:
  - `discOffsetUpTo f d m 0 = 0`
  - `discOffsetUpTo f d 0 N = discUpTo f d N`
  - step-one shift: `discOffsetUpTo f 1 m N = discUpTo (fun k => f (k + m)) 1 N`
  - general offset→shift coherence (max-level): `discOffsetUpTo f d m N = discUpTo (fun k => f (k + m*d)) d N`
    (lemma: `discOffsetUpTo_eq_discUpTo_shift_mul`)
  - dilation/coarsening: `discOffsetUpTo (fun k => f (q*k)) d m N = discOffsetUpTo f (q*d) m N`
  - if you want to pull a factor `q` into the step *at the wrapper level* (without unfolding the `Finset.sup`), use the rewrite lemmas
    `discOffsetUpTo_map_mul_right` / `discOffsetUpTo_map_mul_left` (and their `discOffset_*` analogues),
    which package the `((m+i+1)*d)*q = (m+i+1)*(d*q)` index normalization.
    If your goal is oriented the other way (the step is already written as `d*q` / `q*d` and you want to push the multiplier into the input), use the non-simp orientation helpers:
    `discOffsetUpTo_step_mul_right` / `discOffsetUpTo_step_mul_left`.

    **Tip (sum-level and witness-level):** the same “step is already scaled” orientation helpers exist one level down:
    - `apSumOffset_step_mul_right` / `apSumOffset_step_mul_left`
    - `discOffset_step_mul_right` / `discOffset_step_mul_left`
    These are handy when you want to normalize a tail sum/discrepancy *before* applying residue/dilation lemmas, without unfolding definitions.
    For cutoff scaling bookkeeping, use `discOffsetUpTo_le_mul` (monotonicity under `N ↦ N*q`, assuming `q > 0`).
    If you just need to normalize the *orientation* of a scaled cutoff (so you can match another lemma’s statement), use:
    - `discOffsetUpTo_length_mul_comm` to rewrite `discOffsetUpTo f d m (q * N)` into `discOffsetUpTo f d m (N * q)`
    - `discOffsetUpTo_length_mul_succ_comm` for the common `q * (N+1)` case.
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
- **API note (`apSupport` concatenation):** to split the support of a length `(n+k)` block into its first `n` and last `k` pieces, use
  `apSupport_add`:
  `apSupport d m (n+k) = apSupport d m n ∪ apSupport d (m+n) k`.
  This is the support-side normal form that matches “concatenate AP sums” arguments.
- **API note (`apSupport` size / no collisions):** if you need a cardinality statement, there are two stable-surface wrappers:
  - `card_apSupport_le` gives the always-true bound `(apSupport d m n).card ≤ n` (since it is an image of `Finset.range n`), and
  - `card_apSupport_eq` (or the older `card_apSupport`) gives the exact value `(apSupport d m n).card = n` assuming `d > 0` (injectivity of `i ↦ (m+i+1)*d`).
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

- **API note (`apSupport` cut-stability for congruence hypotheses):** when you have a hypothesis of the form
  `h : ∀ x ∈ apSupport d m (n + k), f x = g x`, you often want to transport it through cut/split normal forms like `apSumOffset_add_len`.
  Use `apSupport_agree_add_iff` to split/merge that hypothesis across the cut:
  `∀ x ∈ apSupport d m (n+k), ...` ↔ `(∀ x ∈ apSupport d m n, ...) ∧ (∀ x ∈ apSupport d (m+n) k, ...)`.

  For the common “cut at `k ≤ n`” shape (prefix length `k`, suffix length `n-k`), use the wrapper
  `apSupport_agree_cut_iff`:
  `∀ x ∈ apSupport d m n, ...` ↔ `(∀ x ∈ apSupport d m k, ...) ∧ (∀ x ∈ apSupport d (m+k) (n-k), ...)`.

  These avoid unfolding `apSupport` and keep “agree on accessed indices” hypotheses in a canonical, transport-friendly form.
