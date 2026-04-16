import MoltResearch.Discrepancy
import MoltResearch.Discrepancy.NormalFormPipelineExample
import MoltResearch.Discrepancy.MiniPipelineMaxExample
import MoltResearch.Discrepancy.SupportEditPipelineExample

/-!
# Discrepancy: stable surface audit (compile-time regression tests)

This file is a tiny, explicit **API surface checklist** for the stable import surface

```lean
import MoltResearch.Discrepancy
```

It aims to enforce two things:

1. **Presence:** the normal-form “nucleus” lemmas we want downstream proofs to use remain exported.
2. **Absence:** deprecated legacy wrappers (e.g. older `*_map_add` names) are **not** exported by
   default; they live behind an explicit opt-in import.

Guiding principle: prefer a few high-leverage checks over a huge brittle list.

If you need backwards-compatible / deprecated aliases, import:

```lean
import MoltResearch.Discrepancy.Deprecated
```
-/

namespace MoltResearch

section
  variable (f : ℕ → ℤ) (a d m n : ℕ)

  /-!
  ## Presence checks (stable surface)

  These are the objects/lemmas we consider part of the “stable normal-form toolkit”.
  -/

  -- Nucleus objects should be present.
  #check apSum
  #check apSumOffset
  #check apSumFrom

  -- Paper-notation ↔ nucleus bridge lemmas should be present (export audit).
  -- (This checklist item: Problems/erdos_discrepancy.md, Track B)
  #check apSumOffset_eq_sum_Icc
  #check apSumOffset_eq_sum_Icc_mul_left
  #check apSumOffset_eq_sum_Icc_of_le
  #check apSumOffset_eq_sum_Icc_of_le_mul_left
  #check sum_Icc_eq_apSumOffset_of_le
  #check sum_Icc_eq_apSumOffset_of_le_mul_left
  #check apSumOffset_eq_sum_Icc_length
  #check apSumOffset_eq_sum_Icc_length_mul_left
  #check sum_Icc_eq_apSumOffset_length
  #check sum_Icc_eq_apSumOffset_length_mul_left
  #check sum_Icc_eq_apSumOffset
  #check sum_Icc_eq_apSumOffset_mul_left

  #check apSumFrom_eq_sum_Icc
  #check apSumFrom_eq_sum_Icc_add
  #check sum_Icc_eq_apSumFrom
  #check sum_Icc_eq_apSumFrom_add

  -- Affine tails (paper-notation endpoints) ↔ nucleus.
  #check apSumFrom_tail_eq_sum_Icc
  #check apSumFrom_tail_eq_sum_Icc_add
  #check sum_Icc_eq_apSumFrom_tail_of_le_add
  #check sum_Icc_eq_apSumFrom_tail
  #check sum_Icc_eq_apSumFrom_tail_of_le

  -- Paper-notation ↔ nucleus bridge for affine tails with `d * i` summand convention.
  #check apSumFrom_tail_eq_sum_Icc_mul_left
  #check apSumFrom_tail_eq_sum_Icc_mul_left_add

  -- Discrepancy wrappers for paper notation.
  #check discOffset_eq_natAbs_sum_Icc
  #check natAbs_sum_Icc_eq_discOffset
  #check discOffset_eq_natAbs_sum_Icc_mul_left
  #check natAbs_sum_Icc_mul_left_eq_discOffset
  #check discOffset_congr_endpoints

  -- Stable-surface simp wrappers for the paper `Icc (m+1) (m+n)` endpoint convention.
  -- These live in `MoltResearch.Discrepancy.EndpointSimp` and should remain exported via
  -- `import MoltResearch.Discrepancy`.
  #check sum_Icc_add_one_add_len_eq_apSumOffset
  #check sum_Icc_add_one_add_len_eq_apSumOffset_mul_left
  #check sum_Icc_add_one_add_len_eq_apSumFrom_tail
  #check natAbs_sum_Icc_add_one_add_len_eq_discOffset
  #check natAbs_sum_Icc_add_one_add_len_eq_discOffset_mul_left
  #check natAbs_sum_Icc_add_one_add_len_eq_natAbs_apSumFrom_tail

  -- One-step length extension/difference nucleus lemmas should be present.
  #check apSumOffset_succ
  #check apSumOffset_succ_sub

  -- Algebraic (multiplication) lemmas should be present and coherent across the nucleus APIs.
  #check apSum_mul_left
  #check apSum_mul_right
  #check apSumOffset_mul_left
  #check apSumOffset_mul_right
  #check apSumFrom_mul_left
  #check apSumFrom_mul_right

  -- Canonical translation-friendly normal forms should be present.
  #check apSumFrom_eq_apSum_shift_add
  #check apSumFrom_eq_apSum_shift_add_left

  -- Step-one normal-form entrypoints (preferred forward orientation) should be present.
  #check apSum_eq_apSum_step_one
  #check apSumOffset_eq_apSumOffset_step_one
  #check apSumOffset_shift_add_eq_apSumOffset_step_one_add_left
  #check apSumFrom_eq_apSum_step_one

  -- Additional stable step-one bridge lemmas across the families.
  #check apSumOffset_eq_apSum_step_one
  #check apSumOffset_eq_apSum_step_one_add_left
  #check apSumFrom_eq_apSumOffset_step_one
  #check apSumFrom_eq_apSumOffset_step_one_add_left
  #check apSumFrom_tail_eq_apSum_step_one
  #check apSumFrom_tail_eq_apSumOffset_step_one
  #check apSumOffset_eq_apSumOffset_step_one_zero_m
  #check apSumOffset_eq_apSumOffset_step_one_zero_m_add_left

  #check apSumOffset_eq_apSum_shift_add
  #check apSumOffset_eq_apSumOffset_shift_add

  -- Affine-tail ↔ shifted-sequence normal forms should be present.
  #check apSumFrom_tail_eq_apSumOffset_shift_add
  #check apSumOffset_shift_add_eq_apSumFrom_tail
  #check apSumOffset_shift_add_eq_apSumFrom_tail_firstTerm

  -- Tail-parameter-elimination normal-form lemmas should be present.
  #check apSumFrom_tail_eq_apSumOffset_shift_add_zero_m
  #check apSumFrom_tail_eq_apSumOffset_shift_add_zero_m_left
  #check apSumFrom_tail_eq_apSum_shift_add
  #check apSum_shift_add_eq_apSumFrom_tail
  #check apSumFrom_sub_eq_apSumOffset_shift_add_zero_m
  #check apSumFrom_sub_eq_apSumOffset_shift_add_zero_m_left
  #check apSumFrom_sub_eq_apSum_shift_add
  #check apSumFrom_sub_eq_apSum_shift_add_left
  #check apSumFrom_add_length_eq_add_apSumOffset_shift_add_zero_m
  #check apSumFrom_add_length_eq_add_apSumOffset_shift_add_zero_m_left
  #check apSumFrom_add_length_eq_add_apSumOffset_shift_add_zero_m_mul_left

  -- Translation normal form (div/mod step) should be present.
  #check apSumOffset_shift_add_eq_apSumOffset_div_mod
  #check apSumOffset_shift_add_mod

  -- Differences → tails normal forms should be present.
  #check apSum_sub_eq_apSumOffset
  #check apSumFrom_sub_eq_apSumFrom_tail
  #check apSumFrom_sub_eq_apSumOffset_shift_add

  /-!
  ## Tao 2015 skeleton: stable normal-form exports

  The `Conjectures/C0002_erdos_discrepancy/src/Tao2015.lean` proof skeleton is intentionally
  lightweight, and it should only rely on the **stable discrepancy surface**.

  These `#check`s ensure the key wrappers / normal-form lemmas it uses remain exported by:

  ```lean
  import MoltResearch.Discrepancy
  ```
  -/

  #check IsSignSequence

  #check BoundedDiscrepancy
  #check discrepancy
  #check discOffset

  /-!
  ### Degenerate-step/offset simp coherence (stable surface)

  These are tiny regression tests ensuring the stable surface exports the simp lemmas that
  normalize `d = 0` and small-length cases without unfolding into `Finset` sums.
  -/

  -- Degenerate step (`d = 0`) simp normal forms.
  --
  -- We intentionally unfold the wrappers here, rather than requiring `simp` to unfold them by
  -- default: the stable surface keeps `discOffset`/`discrepancy` as the normalization boundary.
  example : discOffset f 0 m n = Int.natAbs ((n : ℤ) * f 0) := by
    simp [discOffset, apSumOffset_zero_d, zsmul_eq_mul]

  example : discrepancy f 0 n = Int.natAbs ((n : ℤ) * f 0) := by
    simp [discrepancy, apSum_zero_d, zsmul_eq_mul]

  example : disc f 0 n = Int.natAbs ((n : ℤ) * f 0) := by
    simp [disc, apSum_zero_d, zsmul_eq_mul]

  /-!
  ### `UpTo` degenerate-parameter simp coherence (stable surface)

  These ensure the stable surface exports the simp lemmas that normalize the `UpTo` wrappers in
  the key degenerate cases, without users having to unfold into finset `sup`s.
  -/

  #check discUpTo
  #check discOffsetUpTo

  -- Definitional unfold: `discUpTo` is a finitary `sup` over `range (N+1)`.
  example : discUpTo f d n = (Finset.range (n + 1)).sup (fun t => disc f d t) := by
    rfl

  -- One-shot bound rewrite for `discUpTo` (matches the `discOffsetUpTo` bound rewrites below).
  example (C : ℕ) :
      discUpTo f d n ≤ C ↔ ∀ t ∈ Finset.range (n + 1), disc f d t ≤ C := by
    -- `Finset.sup_le_iff` handles the bound; we just unfold `discUpTo`.
    simpa [discUpTo] using
      (Finset.sup_le_iff (s := Finset.range (n + 1)) (f := fun t => disc f d t) (a := C))

  -- Max-level normal forms (the `UpTo` family): keep the core rewrite lemmas exported.
  -- (This checklist item: Problems/erdos_discrepancy.md, Track B)
  #check discOffsetUpTo_zero
  #check discOffsetUpTo_zero_start
  #check discOffsetUpTo_one_shift
  #check discOffsetUpTo_succ
  #check discOffsetUpTo_add_start
  #check discOffset_le_discOffsetUpTo_self
  #check discOffsetUpTo_mono
  #check discOffsetUpTo_le_add
  #check discOffsetUpTo_le_succ

  -- One-line usage audit: the max-recursion normal form.
  example :
      discOffsetUpTo f d m (n + 1) =
        max (discOffsetUpTo f d m n) (discOffset f d m (n + 1)) := by
    simpa using (discOffsetUpTo_succ (f := f) (d := d) (m := m) (N := n))

  -- One-line usage audit: advancing the start parameter is just a sequence shift by `k*d`.
  example (k : ℕ) :
      discOffsetUpTo f d (m + k) n = discOffsetUpTo (fun t => f (t + k * d)) d m n := by
    simpa using (discOffsetUpTo_add_start (f := f) (d := d) (m := m) (k := k) (N := n))

  -- “Max over lengths/endpoints” normal-form expansions.
  #check discOffsetUpTo_eq_sup_Icc_lengths
  #check discOffsetUpTo_eq_sup_range_Icc
  #check discOffsetUpTo_eq_sup_Icc_endpoints

  -- High-leverage bound normal forms.
  #check discOffsetUpTo_le_iff_forall_range_Icc
  #check discOffsetUpTo_le_iff_forall_Icc_endpoints

  -- API-level inequalities used in Track B.
  #check discOffsetUpTo_add_le_add_discOffsetUpTo
  #check discOffsetUpTo_tail_concat_le

  example : discOffsetUpTo f d m 0 = 0 := by
    simp

  example : discOffsetUpTo f d 0 n = discUpTo f d n := by
    simp

  example : discOffsetUpTo f 1 m n = discUpTo (fun k => f (k + m)) 1 n := by
    simp

  /-!
  ### Max-level `discOffsetUpTo` normal forms (stable surface)

  These are compile-only regression tests that the intended “one-line” rewrite pipeline
  for max-level normal forms remains available under `import MoltResearch.Discrepancy`.
  -/

  -- Rewrite `discOffsetUpTo` into the paper-style endpoint convention as a finitary `sup`.
  example :
      discOffsetUpTo f d m n =
        (Finset.Icc 0 n).sup
          (fun t => Int.natAbs ((Finset.Icc (m + 1) (m + t)).sum (fun i => f (i * d)))) := by
    simpa using
      (discOffsetUpTo_eq_sup_Icc_lengths (f := f) (d := d) (m := m) (N := n))

  -- “One-shot bound rewrite” for the endpoint-style paper form (`sup ≤ C` iff all entries ≤ C).
  example (C : ℕ) :
      discOffsetUpTo f d m n ≤ C ↔
        ∀ t ∈ Finset.Icc 0 n,
          Int.natAbs ((Finset.Icc (m + 1) (m + t)).sum (fun i => f (i * d))) ≤ C := by
    simpa [discOffsetUpTo_eq_sup_Icc_lengths (f := f) (d := d) (m := m) (N := n)] using
      (Finset.sup_le_iff (s := Finset.Icc 0 n)
        (f := fun t => Int.natAbs ((Finset.Icc (m + 1) (m + t)).sum (fun i => f (i * d))))
        (a := C))

  -- Additional max-level audit examples: exercise the “range (N+1)” and “endpoint (Icc m (m+N))”
  -- normal forms in one line under `import MoltResearch.Discrepancy`.

  -- Rewrite into the paper-endpoint `sup` indexed by `n ≤ N` (as `range (N+1)`).
  example :
      discOffsetUpTo f d m n =
        (Finset.range (n + 1)).sup
          (fun t => Int.natAbs ((Finset.Icc (m + 1) (m + t)).sum (fun i => f (i * d)))) := by
    simpa using (discOffsetUpTo_eq_sup_range_Icc (f := f) (d := d) (m := m) (N := n))

  -- One-shot bound rewrite for the `range (N+1)` normal form.
  example (C : ℕ) :
      discOffsetUpTo f d m n ≤ C ↔
        ∀ t ∈ Finset.range (n + 1),
          Int.natAbs ((Finset.Icc (m + 1) (m + t)).sum (fun i => f (i * d))) ≤ C := by
    simpa using (discOffsetUpTo_le_iff_forall_range_Icc (f := f) (d := d) (m := m) (N := n) (C := C))

  -- Rewrite into the paper-endpoint `sup` indexed by right endpoints `b ∈ Icc m (m+N)`.
  example :
      discOffsetUpTo f d m n =
        (Finset.Icc m (m + n)).sup
          (fun b => Int.natAbs ((Finset.Icc (m + 1) b).sum (fun i => f (i * d)))) := by
    simpa using (discOffsetUpTo_eq_sup_Icc_endpoints (f := f) (d := d) (m := m) (N := n))

  -- One-shot bound rewrite for the endpoint-indexed normal form.
  example (C : ℕ) :
      discOffsetUpTo f d m n ≤ C ↔
        ∀ b ∈ Finset.Icc m (m + n),
          Int.natAbs ((Finset.Icc (m + 1) b).sum (fun i => f (i * d))) ≤ C := by
    simpa using
      (discOffsetUpTo_le_iff_forall_Icc_endpoints (f := f) (d := d) (m := m) (N := n) (C := C))

  /-!
  ### discOffset_* lemma exports (stable surface)

  These are high-leverage `discOffset` rewrite/transport lemmas used throughout Track B.
  Keeping them available under `import MoltResearch.Discrepancy` avoids “mystery imports”.
  -/

  -- Invariances / transports.
  #check discOffset_neg
  #check discOffset_shift_add_mul
  #check discOffset_shift_start_add
  #check discOffset_periodic_of_dvd_step

  -- Step-one normalization (and mul-left friendly variant).
  #check discOffset_eq_discOffset_step_one
  #check discOffset_eq_discOffset_step_one_mul_left

  -- Step-factor / reindexing coherence.
  #check discOffset_mul_eq_discOffset_map_mul
  #check discOffset_mul_eq_discOffset_map_mul_left

  -- Local surgery / congruence.
  #check apSumOffset_congr_support
  #check discOffset_congr_support
  #check discOffset_congr
  #check discOffset_congr_range

  -- Splitting / triangle inequality / one-step Lipschitz bounds.
  #check discOffset_add_le
  #check discOffset_add_add_le
  #check discOffset_add_length_le
  #check discOffset_cut_le
  #check discOffset_split_at_le
  #check discOffset_succ_le_add_natAbs
  #check IsSignSequence.discOffset_succ_le

  -- Additional convenient normal forms (still stable surface).
  #check discOffset_eq_discOffset_shift_add
  #check discOffset_shift_start_add_mul_left
  #check discOffset_le_mul_of_natAbs_le
  #check discOffset_le_of_natAbs_le_one

  -- Paper-notation bridge identities.
  #check discOffset_add_len_eq_natAbs_apSumOffset_add
  #check discOffset_eq_natAbs_apSumOffset_cut

  -- Reindexing / step-factorization additional exports.
  #check discOffset_map_mul
  #check discOffset_mul_eq_discOffset_map_mul₁₂

  -- Residue-class splitting (API surface coherence).
  -- Homogeneous / offset / discrepancy-level normal forms should be available from the stable surface.
  #check apSum_mul_len_succ_eq_sum_range
  #check apSum_mul_len_succ_eq_sum_range_mul_left
  #check apSumOffset_mul_len_succ_eq_sum_range
  #check apSumOffset_mul_len_succ_eq_sum_range_mul_left
  #check discOffset_mul_len_succ_eq_natAbs_sum_range
  #check discOffset_mul_len_succ_eq_natAbs_sum_range_mul_left

  -- Boundedness normal forms.
  #check boundedDiscOffset_iff_forall_discOffset_le
  #check not_exists_boundedDiscOffset_iff_forall_exists_discOffset_lt

  #check apSumOffset_eq_sub
  #check apSumOffset_eq_apSum_shift_add

  #check apSum_eq_sum_Icc
  #check sum_Icc_eq_apSum

  /-!
  ## Absence checks (stable surface)

  These names should *not* be available under `import MoltResearch.Discrepancy`.
  They are kept behind an explicit opt-in import:

  ```lean
  import MoltResearch.Discrepancy.Deprecated
  ```
  -/

  -- Deprecated `discOffset` congruence variants.
  #check_failure discOffset_congr_Icc
  #check_failure discOffset_congr_finset_Icc

  -- Deprecated nested-sum residue splitting normal forms (kept behind `Discrepancy.Deprecated`).
  #check_failure apSum_mul_len_succ_eq_sum_range_sum_range
  #check_failure apSum_mul_len_succ_eq_sum_range_sum_range_mul_left

  /-!
  ## Rewrite pipeline examples (compile-only)

  These are a few “go-to” rewrite steps that downstream Track B proofs use constantly.
  We keep them as `example` blocks so they are checked by CI without introducing new lemmas.
  -/

  -- Paper difference of homogeneous `Icc` sums → nucleus offset tail.
  example :
      (Finset.Icc 1 (m + n)).sum (fun i => f (i * d)) - (Finset.Icc 1 m).sum (fun i => f (i * d)) =
        apSumOffset f d m n := by
    -- Paper → nucleus (`apSum`), then difference → tail (`apSumOffset`).
    simpa [sum_Icc_eq_apSum, apSum_sub_eq_apSumOffset]

  -- Paper affine partial sum (`Icc 1 n`) → nucleus `apSumFrom`.
  example : (Finset.Icc 1 n).sum (fun i => f (a + i * d)) = apSumFrom f a d n := by
    simpa [sum_Icc_eq_apSumFrom]

  -- Difference of affine partial sums → explicit affine tail (before shifting to `apSumOffset`).
  example : apSumFrom f a d (m + n) - apSumFrom f a d m = apSumFrom f (a + m * d) d n := by
    simpa using (apSumFrom_sub_eq_apSumFrom_tail (f := f) (a := a) (d := d) (m := m) (n := n))

  -- Canonical difference → offset-tail normal form.
  example : apSum f d (m + n) - apSum f d m = apSumOffset f d m n := by
    simpa using (apSum_sub_eq_apSumOffset (f := f) (d := d) (m := m) (n := n))

  -- Canonical affine-tail ↔ shifted-sequence offset bridge.
  example : apSumFrom f (a + m * d) d n = apSumOffset (fun k => f (k + a)) d m n := by
    simpa using
      (apSumFrom_tail_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n))

  -- Canonical step-one normalization for offset sums.
  example : apSumOffset f d m n = apSumOffset (fun k => f (k * d)) 1 m n := by
    simpa using (apSumOffset_eq_apSumOffset_step_one (f := f) (d := d) (m := m) (n := n))

  -- Canonical subtraction of affine partial sums (with `a = 0`) → offset-tail normal form.
  example : apSumFrom f 0 d (m + n) - apSumFrom f 0 d m = apSumOffset f d m n := by
    -- `apSumFrom_sub_eq_apSumOffset_shift_add` gives the canonical “difference → offset-tail” normal form.
    simpa using
      (apSumFrom_sub_eq_apSumOffset_shift_add (f := f) (a := 0) (d := d) (m := m) (n := n))

  -- Translation+dilation rewrite chain under stable import surface.
  example :
      discOffset (fun t => f (t + a * (d * k))) (d * k) m n =
        discOffset (fun x => f (x * d)) k (m + a) n := by
    calc
      discOffset (fun t => f (t + a * (d * k))) (d * k) m n = discOffset f (d * k) (m + a) n := by
        simpa using
          (discOffset_shift_add_mul (f := f) (a := a) (d := d * k) (m := m) (n := n))
      _ = discOffset (fun x => f (x * d)) k (m + a) n := by
        simpa using
          (discOffset_mul_eq_discOffset_map_mul (f := f) (d := d) (k := k) (m := m + a) (n := n))

  -- Zero-offset tail → homogeneous `apSum` → step-one normalization.
  example : apSumOffset f d 0 n = apSum (fun k => f (k * d)) 1 n := by
    -- First drop the zero offset, then normalize the step size.
    calc
      apSumOffset f d 0 n = apSum f d n := by
        simp
      _ = apSum (fun k => f (k * d)) 1 n := by
        simpa using (apSum_eq_apSum_step_one (f := f) (d := d) (n := n))

  /-!
  ### Additional compile-only rewrite pipeline examples

  These mirror the most common “paper → nucleus” rewrite moves used downstream:
  tail interval sums and differences of affine partial sums normalized into `discOffset` / `apSumOffset`.
  -/

  -- Paper tail sum (`Icc (m+1) (m+n)`) → `discOffset` bound (homogeneous AP summand `i*d`).
  example (C : ℕ)
      (h : Int.natAbs ((Finset.Icc (m + 1) (m + n)).sum (fun i => f (i * d))) ≤ C) :
      discOffset f d m n ≤ C := by
    simpa using h

  -- Paper tail sum with affine endpoints (`m ≤ n`) → `discOffset` in `apSumOffset` normal form.
  --
  -- This is the “paper tail interval” shape that shows up constantly:
  -- `∑_{i=m+1}^n f (a + i*d)`.
  example (C : ℕ) (hmn : m ≤ n)
      (h : Int.natAbs ((Finset.Icc (m + 1) n).sum (fun i => f (a + i * d))) ≤ C) :
      discOffset (fun k => f (a + k)) d m (n - m) ≤ C := by
    -- Avoid simp loops: unfold `discOffset` via `rw`, not `simp`.
    rw [discOffset_def]
    -- Rewrite the paper interval sum into the nucleus `apSumOffset` wrapper.
    have hs :
        (Finset.Icc (m + 1) n).sum (fun i => f (a + i * d)) =
          apSumOffset (fun k => f (a + k)) d m (n - m) := by
      simpa using
        (sum_Icc_eq_apSumOffset_of_le_affineEndpoints (f := f) (a := a) (d := d) (m := m) (n := n) hmn)
    -- Convert the bound by rewriting with `hs`.
    simpa [hs] using h

  -- Paper difference of affine partial sums (`m ≤ n`) → shifted-sequence `discOffset`.
  example (C : ℕ) (hmn : m ≤ n)
      (h : Int.natAbs (apSumFrom f a d n - apSumFrom f a d m) ≤ C) :
      discOffset (fun k => f (k + a)) d m (n - m) ≤ C := by
    -- Avoid simp loops: unfold `discOffset` via `rw`, not `simp`.
    rw [discOffset_def]
    -- Rewrite the difference into the canonical offset-tail normal form.
    have hdiff : apSumFrom f a d n - apSumFrom f a d m = apSumOffset (fun k => f (k + a)) d m (n - m) := by
      simpa using
        (apSumFrom_sub_apSumFrom_eq_apSumOffset_shift_add (f := f) (a := a) (d := d) (m := m) (n := n) hmn)
    -- Turn the bound on the paper form into a bound on the nucleus form.
    simpa [hdiff] using h

  -- Additional bridge lemmas (high-leverage normal-form glue).
  #check apSumOffset_eq_sub
  #check apSumOffset_eq_apSumFrom

  -- Paper ↔ nucleus rewrite entrypoints should be present.
  #check sum_Icc_eq_apSum
  #check apSum_eq_sum_Icc
  #check sum_Icc_eq_apSumOffset
  #check apSumOffset_eq_sum_Icc
  #check sum_Icc_eq_apSumFrom
  #check apSumFrom_eq_sum_Icc

  -- Bridge lemmas for splitting paper interval sums should be present.
  #check sum_Icc_eq_apSumOffset_add_length
  #check sum_Icc_add_length

  -- Paper boundary bridge: affine paper tails → translation-friendly offset normal form.
  #check sum_Icc_eq_apSumOffset_shift_add_left

  -- `simp`-friendly degenerate split corollaries should be coherent across the nucleus APIs.
  #check apSum_add_length_zero_left
  #check apSum_add_length_zero_right
  #check apSumOffset_add_length_zero_left
  #check apSumOffset_add_length_zero_right
  #check apSumFrom_add_length_zero_left
  #check apSumFrom_add_length_zero_right
  #check apSumFrom_add_len
  #check apSumFrom_add_len_zero_left
  #check apSumFrom_add_len_zero_right

  -- Explicitly also audit the `n₁`/`n₂`-named split lemmas for the other nucleus objects.
  #check apSum_add_len
  #check apSum_add_len_zero_left
  #check apSum_add_len_zero_right
  #check apSumOffset_add_len
  #check apSumOffset_add_len_zero_left
  #check apSumOffset_add_len_zero_right

  /-!
  ## `simp` coherence checks

  These are tiny regression tests that the degenerate split corollaries actually *work* with `simp`.
  -/

  example : apSum f d (0 + n) = apSum f d n := by simp
  example : apSum f d (m + 0) = apSum f d m := by simp

  example : apSumOffset f d m (0 + n) = apSumOffset f d m n := by simp
  example : apSumOffset f d m (n + 0) = apSumOffset f d m n := by simp

  -- Explicitly exercise the `n₁`/`n₂`-named simp corollaries for `apSum`.
  example : apSum f d (0 + n) = apSum f d n := by
    simpa using (apSum_add_len_zero_left (f := f) (d := d) (n := n))
  example : apSum f d (n + 0) = apSum f d n := by
    simpa using (apSum_add_len_zero_right (f := f) (d := d) (n := n))

  -- Explicitly exercise the `n₁`/`n₂`-named simp corollaries for `apSumOffset`.
  example : apSumOffset f d m (0 + n) = apSumOffset f d m n := by
    simpa using (apSumOffset_add_len_zero_left (f := f) (d := d) (m := m) (n := n))
  example : apSumOffset f d m (n + 0) = apSumOffset f d m n := by
    simpa using (apSumOffset_add_len_zero_right (f := f) (d := d) (m := m) (n := n))

  example : apSumFrom f a d (0 + n) = apSumFrom f a d n := by simp
  example : apSumFrom f a d (m + 0) = apSumFrom f a d m := by simp

  -- Explicitly exercise the `n₁`/`n₂`-named simp corollaries for `apSumFrom`.
  example : apSumFrom f a d (0 + n) = apSumFrom f a d n := by
    simpa using (apSumFrom_add_len_zero_left (f := f) (a := a) (d := d) (n := n))
  example : apSumFrom f a d (n + 0) = apSumFrom f a d n := by
    simpa using (apSumFrom_add_len_zero_right (f := f) (a := a) (d := d) (n := n))

  -- Step-factorization (compare different steps) normal form should be present.
  #check apSum_mul_eq_apSum_map_mul

  -- Step-one (difference) normal form should be present.
  #check apSum_sub_eq_apSumOffset_step_one_zero_m_add_left

  /-!
  ## Presence checks (invariance / translation / reindexing)

  These are the high-leverage “change of viewpoint” lemmas used to move discrepancy witnesses
  across translated/reindexed sequences.
  -/

  -- Translation invariance (sequence shifted by `k`).
  #check HasDiscrepancyAtLeast.of_shift_add
  #check HasDiscrepancyAtLeast.of_shift_add_left
  #check HasAffineDiscrepancyAtLeast.of_shift_add
  #check HasAffineDiscrepancyAtLeast.of_shift_add_left

  -- Multiplicative reindexing invariance (sequence reindexed by `x ↦ x * k`).
  -- (These require a side condition `k > 0` when used in proofs; we just audit the names.)
  #check HasDiscrepancyAtLeast.of_map_mul
  #check HasAffineDiscrepancyAtLeast.of_map_mul

  -- Sum-level reindexing bridges.
  #check apSum_map_mul
  #check apSumFrom_shift_add

  -- Degenerate-simp lemmas (canonical naming)
  #check apSum_zero
  #check apSum_one
  #check apSumOffset_zero
  #check apSumOffset_one
  #check apSumOffset_zero_start
  #check apSumFrom_zero
  #check apSumFrom_one
  #check apSumFrom_zero_start

  /-!
  ## Absence checks (deprecated names must NOT be in the stable surface)

  We deliberately assert these names are *not* available under `import MoltResearch.Discrepancy`.
  If any of these starts typechecking here, the stable surface has regressed.

  We include a couple of deprecated `discOffset_*` variants to ensure they stay behind the explicit
  opt-in import `MoltResearch.Discrepancy.Deprecated`.
  -/

  /-- error: Unknown constant `MoltResearch.IsSignSequence.map_add` -/
  #guard_msgs in
  #check IsSignSequence.map_add

  /-- error: Unknown identifier `discOffset_congr_Icc` -/
  #guard_msgs in
  #check discOffset_congr_Icc

  /-- error: Unknown identifier `discOffset_congr_finset_Icc` -/
  #guard_msgs in
  #check discOffset_congr_finset_Icc

  /-- error: Unknown constant `MoltResearch.IsSignSequence.map_add_left` -/
  #guard_msgs in
  #check IsSignSequence.map_add_left

  /-- error: Unknown constant `MoltResearch.HasDiscrepancyAtLeast.of_map_add` -/
  #guard_msgs in
  #check HasDiscrepancyAtLeast.of_map_add

  /-- error: Unknown constant `MoltResearch.HasDiscrepancyAtLeast.of_map_add_left` -/
  #guard_msgs in
  #check HasDiscrepancyAtLeast.of_map_add_left

  /-- error: Unknown constant `MoltResearch.HasAffineDiscrepancyAtLeast.of_map_add` -/
  #guard_msgs in
  #check HasAffineDiscrepancyAtLeast.of_map_add

  /-- error: Unknown constant `MoltResearch.HasAffineDiscrepancyAtLeast.of_map_add_left` -/
  #guard_msgs in
  #check HasAffineDiscrepancyAtLeast.of_map_add_left

  /-!
  ### Additional absence checks: legacy `*_zero` / `*_zero_start` naming

  The stable surface reserves the suffix `*_zero` for “length = 0” simp lemmas, and uses
  `*_zero_start` for “start parameter = 0” simp lemmas.

  Older aliases live in `MoltResearch.Discrepancy.Deprecated` and must not typecheck here.
  -/

  /-- error: Unknown identifier `apSumOffset_zero_n` -/
  #guard_msgs in
  #check apSumOffset_zero_n

  /-- error: Unknown identifier `apSumOffset_zero_m` -/
  #guard_msgs in
  #check apSumOffset_zero_m

  /-- error: Unknown identifier `apSumFrom_zero_a` -/
  #guard_msgs in
  #check apSumFrom_zero_a

  /-- error: Unknown identifier `apSumFrom_zero_eq_sum_Icc` -/
  #guard_msgs in
  #check apSumFrom_zero_eq_sum_Icc

  /-- error: Unknown identifier `sum_Icc_eq_apSumFrom_zero` -/
  #guard_msgs in
  #check sum_Icc_eq_apSumFrom_zero

  /-- error: Unknown identifier `HasDiscrepancyAtLeast_iff_exists_apSumOffset_zero` -/
  #guard_msgs in
  #check HasDiscrepancyAtLeast_iff_exists_apSumOffset_zero

  /-- error: Unknown identifier `HasDiscrepancyAtLeast_iff_exists_apSumOffset_zero_m` -/
  #guard_msgs in
  #check HasDiscrepancyAtLeast_iff_exists_apSumOffset_zero_m

  /-- error: Unknown identifier `HasDiscrepancyAtLeast_shift_add_iff_exists_apSumOffset_zero` -/
  #guard_msgs in
  #check HasDiscrepancyAtLeast_shift_add_iff_exists_apSumOffset_zero

  /-!
  ### Additional absence checks: deprecated alias families

  These names are still available behind `import MoltResearch.Discrepancy.Deprecated`, but must
  *not* leak into the stable surface.
  -/

  /-- error: Unknown identifier `apSum_mul_right_cfirst` -/
  #guard_msgs in
  #check apSum_mul_right_cfirst

  /-- error: Unknown identifier `apSumOffset_mul_right_cfirst` -/
  #guard_msgs in
  #check apSumOffset_mul_right_cfirst

  /-- error: Unknown identifier `apSumFrom_mul_right_cfirst` -/
  #guard_msgs in
  #check apSumFrom_mul_right_cfirst

  /-- error: Unknown identifier `apSum_mul_left_ffirst` -/
  #guard_msgs in
  #check apSum_mul_left_ffirst

  /-- error: Unknown identifier `apSumOffset_mul_left_ffirst` -/
  #guard_msgs in
  #check apSumOffset_mul_left_ffirst

  /-- error: Unknown identifier `apSumFrom_mul_left_ffirst` -/
  #guard_msgs in
  #check apSumFrom_mul_left_ffirst

  /-- error: Unknown identifier `apSum_step_one_eq_apSum` -/
  #guard_msgs in
  #check apSum_step_one_eq_apSum

  /-- error: Unknown identifier `apSumOffset_step_one_eq_apSumOffset` -/
  #guard_msgs in
  #check apSumOffset_step_one_eq_apSumOffset

  /-- error: Unknown identifier `apSumFrom_step_one_eq_apSumFrom` -/
  #guard_msgs in
  #check apSumFrom_step_one_eq_apSumFrom

  /-- error: Unknown identifier `apSumFrom_eq_apSum_shift` -/
  #guard_msgs in
  #check apSumFrom_eq_apSum_shift

  /-- error: Unknown identifier `apSumFrom_eq_apSum_map_add` -/
  #guard_msgs in
  #check apSumFrom_eq_apSum_map_add

  /-- error: Unknown identifier `apSumFrom_eq_apSum_map_add_left` -/
  #guard_msgs in
  #check apSumFrom_eq_apSum_map_add_left

  /-- error: Unknown identifier `apSumFrom_map_add` -/
  #guard_msgs in
  #check apSumFrom_map_add

  /-- error: Unknown identifier `apSumFrom_map_add_left` -/
  #guard_msgs in
  #check apSumFrom_map_add_left

  /-- error: Unknown identifier `apSumFrom_eq_apSumOffset_step_one_add_left_via_shift_add` -/
  #guard_msgs in
  #check apSumFrom_eq_apSumOffset_step_one_add_left_via_shift_add

  /-- error: Unknown identifier `apSumFrom_eq_apSumOffset_step_one_via_shift_add` -/
  #guard_msgs in
  #check apSumFrom_eq_apSumOffset_step_one_via_shift_add

  /-- error: Unknown identifier `sum_Icc_eq_apSumOffset_step_one_via_shift_add` -/
  #guard_msgs in
  #check sum_Icc_eq_apSumOffset_step_one_via_shift_add

  /-- error: Unknown identifier `apSum_map_add` -/
  #guard_msgs in
  #check apSum_map_add

  /-- error: Unknown identifier `apSum_map_add_left` -/
  #guard_msgs in
  #check apSum_map_add_left

  /-- error: Unknown identifier `apSumOffset_shift_add_left_start_mul` -/
  #guard_msgs in
  #check apSumOffset_shift_add_left_start_mul

  /-- error: Unknown identifier `apSum_eq_sum_Icc_mul_left` -/
  #guard_msgs in
  #check apSum_eq_sum_Icc_mul_left

  /-- error: Unknown identifier `sum_Icc_eq_apSum_mul_left` -/
  #guard_msgs in
  #check sum_Icc_eq_apSum_mul_left

  /-- error: Unknown identifier `apSumFrom_eq_sum_Icc_mul_left` -/
  #guard_msgs in
  #check apSumFrom_eq_sum_Icc_mul_left

  /-- error: Unknown identifier `sum_Icc_eq_apSumFrom_mul_left` -/
  #guard_msgs in
  #check sum_Icc_eq_apSumFrom_mul_left

  /-- error: Unknown identifier `apSumFrom_eq_sum_Icc_mul_left_add` -/
  #guard_msgs in
  #check apSumFrom_eq_sum_Icc_mul_left_add

  /-- error: Unknown identifier `sum_Icc_eq_apSumFrom_mul_left_add` -/
  #guard_msgs in
  #check sum_Icc_eq_apSumFrom_mul_left_add

  /-- error: Unknown identifier `sum_Icc_eq_apSumOffset_shift_add_left_mul_left` -/
  #guard_msgs in
  #check sum_Icc_eq_apSumOffset_shift_add_left_mul_left

  /-- error: Unknown identifier `apSumOffset_eq_apSum_step_one_mul_left` -/
  #guard_msgs in
  #check apSumOffset_eq_apSum_step_one_mul_left

  -- Step-one inverse-orientation names are deprecated and must not be in the stable surface.
  -- Affine step-one inverse-orientation names are deprecated and must not be in the stable surface.

  /-- error: Unknown identifier `apSumFrom_eq_apSumFrom_step_one` -/
  #guard_msgs in
  #check apSumFrom_eq_apSumFrom_step_one

  /-- error: Unknown identifier `apSumFrom_eq_apSumOffset_step_one_zero_m` -/
  #guard_msgs in
  #check apSumFrom_eq_apSumOffset_step_one_zero_m

  /-- error: Unknown identifier `apSumFrom_eq_apSumOffset_step_one_zero_m_add_left` -/
  #guard_msgs in
  #check apSumFrom_eq_apSumOffset_step_one_zero_m_add_left

  /-- error: Unknown identifier `apSumFrom_step_one_eq_apSumFrom` -/
  #guard_msgs in
  #check apSumFrom_step_one_eq_apSumFrom

  /-- error: Unknown identifier `apSumFrom_step_one_add_left_eq_apSumFrom` -/
  #guard_msgs in
  #check apSumFrom_step_one_add_left_eq_apSumFrom

  /-- error: Unknown identifier `apSumOffset_eq_apSumFrom_mul_left` -/
  #guard_msgs in
  #check apSumOffset_eq_apSumFrom_mul_left

  /-- error: Unknown identifier `apSumFrom_mul_left_eq_apSumOffset` -/
  #guard_msgs in
  #check apSumFrom_mul_left_eq_apSumOffset

  /-- error: Unknown identifier `apSumFrom_eq_apSumOffset_of_eq_mul_left` -/
  #guard_msgs in
  #check apSumFrom_eq_apSumOffset_of_eq_mul_left

  /-- error: Unknown identifier `apSumFrom_mul_right_cfirst` -/
  #guard_msgs in
  #check apSumFrom_mul_right_cfirst

  /-- error: Unknown identifier `apSum_mul_right_cfirst` -/
  #guard_msgs in
  #check apSum_mul_right_cfirst

  /-- error: Unknown identifier `apSumOffset_mul_right_cfirst` -/
  #guard_msgs in
  #check apSumOffset_mul_right_cfirst

  /-- error: Unknown identifier `apSumFrom_mul_left_ffirst` -/
  #guard_msgs in
  #check apSumFrom_mul_left_ffirst

  /-- error: Unknown identifier `apSum_mul_left_ffirst` -/
  #guard_msgs in
  #check apSum_mul_left_ffirst

  /-- error: Unknown identifier `apSumOffset_mul_left_ffirst` -/
  #guard_msgs in
  #check apSumOffset_mul_left_ffirst

  /-- error: Unknown identifier `apSumOffset_shift_add_left_start_mul` -/
  #guard_msgs in
  #check apSumOffset_shift_add_left_start_mul

  /-- error: Unknown identifier `apSumOffset_one_mul_left` -/
  #guard_msgs in
  #check apSumOffset_one_mul_left


  /-- error: Unknown identifier `apSum_step_one_eq_apSum` -/
  #guard_msgs in
  #check apSum_step_one_eq_apSum

  /-- error: Unknown identifier `apSumOffset_step_one_eq_apSumOffset` -/
  #guard_msgs in
  #check apSumOffset_step_one_eq_apSumOffset

  /-- error: Unknown identifier `apSumOffset_step_one_zero_m_eq_apSumOffset` -/
  #guard_msgs in
  #check apSumOffset_step_one_zero_m_eq_apSumOffset

  /-- error: Unknown identifier `apSumOffset_step_one_zero_m_add_left_eq_apSumOffset` -/
  #guard_msgs in
  #check apSumOffset_step_one_zero_m_add_left_eq_apSumOffset

  /-- error: Unknown identifier `apSum_step_one_eq_apSumOffset` -/
  #guard_msgs in
  #check apSum_step_one_eq_apSumOffset

  /-- error: Unknown identifier `apSum_step_one_eq_apSumFrom` -/
  #guard_msgs in
  #check apSum_step_one_eq_apSumFrom

  /-- error: Unknown identifier `apSum_step_one_eq_apSumFrom_tail` -/
  #guard_msgs in
  #check apSum_step_one_eq_apSumFrom_tail

  /-- error: Unknown identifier `apSumOffset_eq_apSum_step_one_mul_left_add_left` -/
  #guard_msgs in
  #check apSumOffset_eq_apSum_step_one_mul_left_add_left

  /-- error: Unknown identifier `apSum_step_one_mul_left_eq_apSumOffset` -/
  #guard_msgs in
  #check apSum_step_one_mul_left_eq_apSumOffset

  /-- error: Unknown identifier `apSum_step_one_mul_left_add_left_eq_apSumOffset` -/
  #guard_msgs in
  #check apSum_step_one_mul_left_add_left_eq_apSumOffset

  /-- error: Unknown identifier `apSumOffset_eq_apSumOffset_step_one_zero_m_mul_left_add_left` -/
  #guard_msgs in
  #check apSumOffset_eq_apSumOffset_step_one_zero_m_mul_left_add_left

  /-- error: Unknown identifier `apSumOffset_step_one_zero_m_mul_left_add_left_eq_apSumOffset` -/
  #guard_msgs in
  #check apSumOffset_step_one_zero_m_mul_left_add_left_eq_apSumOffset

  /-- error: Unknown identifier `apSum_sub_eq_apSumOffset_step_one_zero_m_mul_left_add_left` -/
  #guard_msgs in
  #check apSum_sub_eq_apSumOffset_step_one_zero_m_mul_left_add_left


  /-- error: Unknown identifier `apSumFrom_sub_apSumFrom_eq_apSum_step_one_mul_left_mul_left` -/
  #guard_msgs in
  #check apSumFrom_sub_apSumFrom_eq_apSum_step_one_mul_left_mul_left

  /-- error: Unknown identifier `apSumFrom_eq_apSumOffset_step_one_zero_m` -/
  #guard_msgs in
  #check apSumFrom_eq_apSumOffset_step_one_zero_m

  /-- error: Unknown identifier `apSumFrom_eq_apSumOffset_step_one_zero_m_add_left` -/
  #guard_msgs in
  #check apSumFrom_eq_apSumOffset_step_one_zero_m_add_left

  -- Deprecated aliases for degenerate-simp lemmas (must NOT be in the stable surface)

  /-- error: Unknown identifier `apSumOffset_zero_n` -/
  #guard_msgs in
  #check apSumOffset_zero_n

  /-- error: Unknown identifier `apSumOffset_zero_m` -/
  #guard_msgs in
  #check apSumOffset_zero_m

  /-- error: Unknown identifier `apSumFrom_zero_a` -/
  #guard_msgs in
  #check apSumFrom_zero_a

  /-- error: Unknown identifier `HasDiscrepancyAtLeast_iff_exists_apSumOffset_zero_m` -/
  #guard_msgs in
  #check HasDiscrepancyAtLeast_iff_exists_apSumOffset_zero_m
end

/-!
## Example usage (ensures the pipeline works end-to-end)

A tiny example rewriting a paper-notation interval sum into two consecutive `apSumOffset` blocks,
then expanding those blocks back into paper notation. This is a regression test that the
one-cut paper→nucleus bridge lemma is available in the stable surface.
-/
section
  variable (f : ℕ → ℤ) (d m n₁ n₂ : ℕ)

  example :
      (Finset.Icc (m + 1) (m + (n₁ + n₂))).sum (fun i => f (i * d)) =
        (Finset.Icc (m + 1) (m + n₁)).sum (fun i => f (i * d)) +
          (Finset.Icc (m + n₁ + 1) (m + n₁ + n₂)).sum (fun i => f (i * d)) := by
    classical
    -- Rewrite the LHS to `apSumOffset` blocks, then expand back to `Finset.Icc` sums.
    simpa [apSumOffset_eq_sum_Icc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      -sum_Icc_eq_apSumOffset_of_le_add_len,
      -sum_Icc_add_one_add_len_eq_apSumOffset] using
      (sum_Icc_eq_apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))
end

end MoltResearch
