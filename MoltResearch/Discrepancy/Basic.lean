import Mathlib

/-!
# Discrepancy: basic definitions

These definitions are intended as **reusable verified substrate** for discrepancy-style problems.

Design principles:
- keep definitions small and composable
- avoid baking in problem-specific choices too early
- prefer ℕ-indexed sequences with ℤ values for summation convenience
-/

namespace MoltResearch

/-- A ±1-valued sequence on ℕ (values in ℤ). -/
def IsSignSequence (f : ℕ → ℤ) : Prop := ∀ n, f n = 1 ∨ f n = -1

/-- Sum of `f` along the homogeneous arithmetic progression `d, 2d, ..., nd`.

We use `Finset.range n` with `i+1` so the progression starts at `d`.
- `n = 0` yields sum 0.
-/
def apSum (f : ℕ → ℤ) (d n : ℕ) : ℤ :=
  (Finset.range n).sum (fun i => f ((i + 1) * d))

/-! ### Discrepancy definition and basic API -/

/-- A convenient wrapper for the absolute value of an arithmetic-progression sum.

It is defined as the natural absolute value of `apSum f d n`.
-/
def discrepancy (f : ℕ → ℤ) (d n : ℕ) : ℕ :=
  Int.natAbs (apSum f d n)

/-- Definitional lemma exposing the definition. -/
lemma discrepancy_eq_natAbs_apSum (f : ℕ → ℤ) (d n : ℕ) :
    discrepancy f d n = Int.natAbs (apSum f d n) :=
  rfl

/-- Alias for the definitional lemma. -/
lemma discrepancy_def (f : ℕ → ℤ) (d n : ℕ) :
    discrepancy f d n = Int.natAbs (apSum f d n) :=
  rfl

/-- `simp` bridge: `Int.natAbs (apSum …)` simplifies to the `discrepancy` wrapper.

This direction avoids simp loops with `discrepancy_def`.
-/
@[simp] lemma natAbs_apSum_eq_discrepancy (f : ℕ → ℤ) (d n : ℕ) :
    Int.natAbs (apSum f d n) = discrepancy f d n :=
  rfl

/-- The discrepancy of an empty progression is zero. -/
@[simp] lemma discrepancy_zero (f : ℕ → ℤ) (d : ℕ) : discrepancy f d 0 = 0 := by
  unfold discrepancy apSum
  simp

/-- Sum of `f` over the next `n` terms of the arithmetic progression after skipping `m` terms.

It is defined as `∑ i in range n, f ((m + i + 1) * d)`. -/
def apSumOffset (f : ℕ → ℤ) (d m n : ℕ) : ℤ :=
  (Finset.range n).sum (fun i => f ((m + i + 1) * d))

/-- A convenient wrapper for the absolute value of an offset arithmetic-progression sum.

It is defined as the natural absolute value of `apSumOffset f d m n`.
-/
def discOffset (f : ℕ → ℤ) (d m n : ℕ) : ℕ :=
  Int.natAbs (apSumOffset f d m n)

/-- Definitional lemma exposing the definition. -/
lemma discOffset_eq_natAbs_apSumOffset (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset f d m n = Int.natAbs (apSumOffset f d m n) :=
  rfl

/-- Alias for the definitional lemma. -/
lemma discOffset_def (f : ℕ → ℤ) (d m n : ℕ) :
    discOffset f d m n = Int.natAbs (apSumOffset f d m n) :=
  rfl

/-- `simp` bridge: `Int.natAbs (apSumOffset …)` simplifies to the `discOffset` wrapper.

This direction avoids simp loops with `discOffset_def`.
-/
@[simp] lemma natAbs_apSumOffset_eq_discOffset (f : ℕ → ℤ) (d m n : ℕ) :
    Int.natAbs (apSumOffset f d m n) = discOffset f d m n :=
  rfl

/-! ### Congruence lemmas -/

/-- If two functions agree pointwise on the indices used in `apSum`, then the AP sums are equal. -/
lemma apSum_congr (f g : ℕ → ℤ) (d n : ℕ)
    (h : ∀ i, i < n → f ((i + 1) * d) = g ((i + 1) * d)) :
    apSum f d n = apSum g d n := by
  unfold apSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi' : i < n := Finset.mem_range.mp hi
  exact h i hi'

/-- If two functions agree pointwise on the indices used in `apSumOffset`, then the offset sums are equal. -/
lemma apSumOffset_congr (f g : ℕ → ℤ) (d m n : ℕ)
    (h : ∀ i, i < n → f ((m + i + 1) * d) = g ((m + i + 1) * d)) :
    apSumOffset f d m n = apSumOffset g d m n := by
  unfold apSumOffset
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi' : i < n := Finset.mem_range.mp hi
  exact h i hi'

/-- Support statement: if `f` and `g` agree on every *progression index* used by `apSumOffset`
(i.e. on `Set.Icc (m+1) (m+n)`), then the offset sums are equal.

This is convenient as “glue” for later local-surgery arguments where you know that `f` and `g`
coincide on a bounded interval, and you want to change `f` outside that interval.
-/
lemma apSumOffset_congr_Icc (f g : ℕ → ℤ) (d m n : ℕ)
    (h : ∀ i, i ∈ Set.Icc (m + 1) (m + n) → f (i * d) = g (i * d)) :
    apSumOffset f d m n = apSumOffset g d m n := by
  apply apSumOffset_congr (f := f) (g := g) (d := d) (m := m) (n := n)
  intro i hi
  have hlow : m + 1 ≤ m + i + 1 := by
    have : 1 ≤ i + 1 := Nat.succ_le_succ (Nat.zero_le i)
    have : m + 1 ≤ m + (i + 1) := Nat.add_le_add_left this m
    simpa [Nat.add_assoc] using this
  have hhigh : m + i + 1 ≤ m + n := by
    have : i + 1 ≤ n := Nat.succ_le_of_lt hi
    have : m + (i + 1) ≤ m + n := Nat.add_le_add_left this m
    simpa [Nat.add_assoc] using this
  exact h (m + i + 1) ⟨hlow, hhigh⟩

/-- Finset-membership variant of `apSumOffset_congr_Icc`.

This matches paper notation where the relevant progression indices are written as
`Finset.Icc (m+1) (m+n)`.
-/
lemma apSumOffset_congr_finset_Icc (f g : ℕ → ℤ) (d m n : ℕ)
    (h : ∀ i, i ∈ Finset.Icc (m + 1) (m + n) → f (i * d) = g (i * d)) :
    apSumOffset f d m n = apSumOffset g d m n := by
  apply apSumOffset_congr_Icc (f := f) (g := g) (d := d) (m := m) (n := n)
  intro i hi
  have : i ∈ Finset.Icc (m + 1) (m + n) := by
    exact Finset.mem_Icc.2 hi
  exact h i this

/-- `congr` variant: if `P` holds on every *index* used in `apSumOffset`, and the summands agree
whenever `P i` holds, then the offset AP sums are equal.

This is convenient when you have a hypothesis stated on the summation range `i < n` (or
`i ∈ range n`) and want to apply it without rewriting the whole function.
-/
lemma apSumOffset_congrOn (f g : ℕ → ℤ) (P : ℕ → Prop) (d m n : ℕ)
    (hP : ∀ i, i < n → P i)
    (hfg : ∀ i, P i → f ((m + i + 1) * d) = g ((m + i + 1) * d)) :
    apSumOffset f d m n = apSumOffset g d m n := by
  apply apSumOffset_congr (f := f) (g := g) (d := d) (m := m) (n := n)
  intro i hi
  exact hfg i (hP i hi)

/-- Value-predicate variant of `apSumOffset_congrOn`: if `P` holds on every value used in
`apSumOffset`, and `f = g` on `P`, then the offset AP sums are equal.

This is convenient when you have an ambient hypothesis like `∀ x, P x → f x = g x`.
-/
lemma apSumOffset_congrOn_val (f g : ℕ → ℤ) (P : ℕ → Prop) (d m n : ℕ)
    (hP : ∀ i, i < n → P ((m + i + 1) * d))
    (hfg : ∀ x, P x → f x = g x) :
    apSumOffset f d m n = apSumOffset g d m n := by
  apply apSumOffset_congr (f := f) (g := g) (d := d) (m := m) (n := n)
  intro i hi
  exact hfg _ (hP i hi)

/-! ### Invariance / normal-form lemmas -/

/-- Shifting the input by `a*d` converts an `apSum` into an `apSumOffset`.

This is the natural “invariance normal form” for arithmetic progressions: the *sequence* shift
by `a*d` corresponds to an *offset* `a` in the progression index.
-/
lemma apSum_shift_mul (f : ℕ → ℤ) (a d n : ℕ) :
    apSum (fun k => f (k + a * d)) d n = apSumOffset f d a n := by
  unfold apSum apSumOffset
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- `((i+1)*d) + a*d = (a+i+1)*d`.
  have h : (i + 1) * d + a * d = (a + i + 1) * d := by
    calc
      (i + 1) * d + a * d = a * d + (i + 1) * d := by
        simpa [Nat.add_comm]
      _ = (a + (i + 1)) * d := by
        simpa [Nat.add_mul]
      _ = (a + i + 1) * d := by
        simp [Nat.add_assoc]
  simp [h, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- One-way normal form for discrepancy of a shift by `a*d`: it expands to the `natAbs` of an
offset AP sum.

Marked `[simp]` since the rewrite goes from the wrapper `discrepancy` to a `natAbs` normal form.
-/
@[simp] lemma discrepancy_shift_mul (f : ℕ → ℤ) (a d n : ℕ) :
    discrepancy (fun k => f (k + a * d)) d n = Int.natAbs (apSumOffset f d a n) := by
  unfold discrepancy
  simpa [apSum_shift_mul]

/-- `simp`-friendly variant of `apSum_shift_mul` under `Int.natAbs`.

This lets goals normalize after rewriting `discrepancy_def` without having to manually unfold
`apSum_shift_mul`.
-/
@[simp] lemma natAbs_apSum_shift_mul (f : ℕ → ℤ) (a d n : ℕ) :
    Int.natAbs (apSum (fun k => f (k + a * d)) d n) = Int.natAbs (apSumOffset f d a n) := by
  simpa [apSum_shift_mul]

/-- Normal form: shifting by `m*d` becomes `apSumOffset`. (Not a `[simp]` lemma: it can loop.) -/
lemma apSum_shift_mul_simp (f : ℕ → ℤ) (m d n : ℕ) :
    apSum (fun k => f (k + m * d)) d n = apSumOffset f d m n := by
  simpa using (apSum_shift_mul (f := f) (a := m) (d := d) (n := n))

/-- Normal form: discrepancy of a shift by `m*d` becomes `natAbs (apSumOffset ...)`. (Not `[simp]`.) -/
lemma discrepancy_shift_mul_simp (f : ℕ → ℤ) (m d n : ℕ) :
    discrepancy (fun k => f (k + m * d)) d n = Int.natAbs (apSumOffset f d m n) := by
  simpa using (discrepancy_shift_mul (f := f) (a := m) (d := d) (n := n))

/-! ### Shifting the “start index” in `apSumOffset` -/

/-- Normal form: shifting the skipped prefix `m` by `k` can be moved into the summand as a shift
by `k*d`.

Concretely, this rewrites
`apSumOffset f d (m + k) n`
into
`apSumOffset (fun t => f (t + k*d)) d m n`.
-/
lemma apSumOffset_add_start (f : ℕ → ℤ) (d m k n : ℕ) :
    apSumOffset f d (m + k) n = apSumOffset (fun t => f (t + k * d)) d m n := by
  unfold apSumOffset
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- Align the indices so we can use distributivity of `(* d)` over `+`.
  have hmk : m + k + i + 1 = (m + i + 1) + k := by
    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hmul : (m + k + i + 1) * d = (m + i + 1) * d + k * d := by
    calc
      (m + k + i + 1) * d = ((m + i + 1) + k) * d := by
        simpa [hmk]
      _ = (m + i + 1) * d + k * d := by
        simpa [Nat.add_mul]
  -- Now the summands match definitionally.
  simp [hmul]

/-- Translation-friendly variant of `apSumOffset_add_start` with the constant shift on the left:
`k*d + t`.
-/
lemma apSumOffset_add_start_add_left (f : ℕ → ℤ) (d m k n : ℕ) :
    apSumOffset f d (m + k) n = apSumOffset (fun t => f (k * d + t)) d m n := by
  -- Just commute the addition inside the shifted summand.
  simpa [Nat.add_comm] using (apSumOffset_add_start (f := f) (d := d) (m := m) (k := k) (n := n))

/-! ### Normalization of nested shifts inside summands -/

/-- `simp` normal form for nested additive shifts under binders.

This is intentionally *function-level* (rather than a `[simp]` lemma about `Nat.add_assoc`) so it
only fires when a goal actually contains a shifted summand `fun k => f (k + a + b)`.

We orient the rewrite as
`fun k => f (k + a + b)` → `fun k => f (k + (a + b))`
to avoid simp loops.
-/
@[simp] lemma shift_summand_add_assoc {α : Type} (f : ℕ → α) (a b : ℕ) :
    (fun k => f (k + a + b)) = fun k => f (k + (a + b)) := by
  funext k
  simp [Nat.add_assoc]

/-! ### Shifts by a known multiple of `d` -/

/-- If `a` is (definitionally) a multiple of `d`, shifting by `a` is the same normal form
as shifting by `m*d` and rewriting via `apSumOffset`. -/
lemma apSum_shift_of_eq_mul (f : ℕ → ℤ) (a d n m : ℕ) (ha : a = m * d) :
    apSum (fun k => f (k + a)) d n = apSumOffset f d m n := by
  subst ha
  simpa using (apSum_shift_mul (f := f) (a := m) (d := d) (n := n))

/-- The corresponding `discrepancy` normal form when `a = m*d`. -/
lemma discrepancy_shift_of_eq_mul (f : ℕ → ℤ) (a d n m : ℕ) (ha : a = m * d) :
    discrepancy (fun k => f (k + a)) d n = Int.natAbs (apSumOffset f d m n) := by
  subst ha
  simpa using (discrepancy_shift_mul (f := f) (a := m) (d := d) (n := n))

/-! ### Normalizing shifts modulo the step -/

/-- Normal form: shifting by `a` can be reduced modulo the step `d`.

Concretely, for `d > 0` we rewrite the summand shift `k ↦ f (k + a)` as
`k ↦ f (k + (a % d))` while adjusting the AP start index by `a / d`.

This is aligned with the standard decomposition `a = (a / d) * d + (a % d)`.
-/
lemma apSumOffset_shift_mod (f : ℕ → ℤ) (d m n a : ℕ) (hd : 0 < d) :
    apSumOffset (fun k => f (k + a)) d m n =
      apSumOffset (fun k => f (k + (a % d))) d (m + a / d) n := by
  -- (We keep the hypothesis `d > 0` since this lemma is used as a normalization rule.)
  unfold apSumOffset
  refine Finset.sum_congr rfl ?_
  intro i hi
  have ha : a = (a / d) * d + a % d := by
    -- `Nat.div_add_mod` is stated with `d * (a / d)`; commute the factors.
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (Nat.div_add_mod a d).symm
  have hadd : (m + i + 1) + a / d = m + a / d + i + 1 := by
    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hmul : (m + i + 1) * d + (a / d) * d = ((m + i + 1) + a / d) * d := by
    simpa [Nat.add_mul] using (Nat.add_mul (m + i + 1) (a / d) d).symm
  have hidx : ((m + i + 1) * d) + a = ((m + a / d + i + 1) * d) + a % d := by
    calc
      ((m + i + 1) * d) + a
          = ((m + i + 1) * d) + ((a / d) * d + a % d) := by
              nth_rewrite 1 [ha]
              rfl
      _ = ((m + i + 1) * d + (a / d) * d) + a % d := by
              simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      _ = (((m + i + 1) + a / d) * d) + a % d := by
              -- `x*d + y*d = (x+y)*d`
              rw [hmul]
      _ = ((m + a / d + i + 1) * d) + a % d := by
              simp [hadd, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  exact congrArg f hidx

/-! ### Triangle-inequality API for AP sums -/

/-- `apSumOffset` splits over addition of lengths. -/
lemma apSumOffset_add_len (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    apSumOffset f d m (n₁ + n₂) =
      apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
  unfold apSumOffset
  -- `range (n₁ + n₂)` splits into `range n₁` and a shifted `range n₂`.
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (Finset.sum_range_add (f := fun i => f ((m + i + 1) * d)) n₁ n₂)

/-! ### Tails / differences for `apSumOffset` -/

/-- Tail of an offset AP sum as a difference of a longer sum and its initial segment.

This is a convenient normal form for “difference → later tail” pipelines.
-/
lemma apSumOffset_tail_eq_sub (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    apSumOffset f d (m + n₁) n₂ = apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ := by
  -- Start from the length-splitting lemma and rearrange.
  have h := apSumOffset_add_len (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)
  -- `h : apSumOffset … (n₁+n₂) = apSumOffset … n₁ + apSumOffset … (m+n₁) n₂`.
  -- Subtract the prefix.
  have hsub := congrArg (fun z : ℤ => z - apSumOffset f d m n₁) h
  -- Clean up `(+ …) - …`.
  simpa [add_sub_cancel_left, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsub.symm

/-- Rewrite the normal-form difference
`apSumOffset f d m (n₁+n₂) - apSumOffset f d m n₁` as the tail `apSumOffset f d (m+n₁) n₂`.

This is the offset-sum analogue of `apSum_sub_eq_apSumOffset` / `apSumFrom_sub_eq_apSumFrom_tail`.
-/
lemma apSumOffset_sub_eq_apSumOffset_tail (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    apSumOffset f d m (n₁ + n₂) - apSumOffset f d m n₁ = apSumOffset f d (m + n₁) n₂ := by
  simpa using (apSumOffset_tail_eq_sub (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂)).symm

/-- `simp`-friendly corollary of `apSumOffset_add_len` for `n₁ = 0`. -/
@[simp] lemma apSumOffset_add_len_zero_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m (0 + n) = apSumOffset f d m n := by
  simpa [apSumOffset_add_len] using
    (apSumOffset_add_len (f := f) (d := d) (m := m) (n₁ := 0) (n₂ := n))

/-- `simp`-friendly corollary of `apSumOffset_add_len` for `n₂ = 0`. -/
@[simp] lemma apSumOffset_add_len_zero_right (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m (n + 0) = apSumOffset f d m n := by
  simpa [apSumOffset_add_len] using
    (apSumOffset_add_len (f := f) (d := d) (m := m) (n₁ := n) (n₂ := 0))

/-- Triangle inequality for concatenating two offset AP sums. -/
lemma natAbs_apSumOffset_add_le (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    Int.natAbs (apSumOffset f d m (n₁ + n₂)) ≤
      Int.natAbs (apSumOffset f d m n₁) + Int.natAbs (apSumOffset f d (m + n₁) n₂) := by
  -- `Int.natAbs` satisfies `|x + y| ≤ |x| + |y|`.
  simpa [apSumOffset_add_len] using
    (Int.natAbs_add_le (apSumOffset f d m n₁) (apSumOffset f d (m + n₁) n₂))

/-- Triangle inequality for concatenating two offset AP sums, at the `discOffset` level.

This proof stays at the discrepancy-normal-form level: we apply the `Int.natAbs` lemma and
rewrite using the simp bridge `natAbs_apSumOffset_eq_discOffset`, rather than unfolding
`discOffset`.
-/
lemma discOffset_add_le (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    discOffset f d m (n₁ + n₂) ≤
      discOffset f d m n₁ + discOffset f d (m + n₁) n₂ := by
  simpa using
    (natAbs_apSumOffset_add_le (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))

/-- Normal form: an offset sum with start index `m = 0` is just the homogeneous sum `apSum`.

Marked `[simp]` so that normalizing away a spurious `m = 0` offset is automatic.
(We intentionally do *not* simp in the other direction.)
-/
@[simp] lemma apSumOffset_zero_start (f : ℕ → ℤ) (d n : ℕ) :
    apSumOffset f d 0 n = apSum f d n := by
  unfold apSumOffset apSum
  simp

/-- Triangle inequality for `apSum` by splitting into a prefix and a shifted suffix. -/
lemma natAbs_apSum_add_le (f : ℕ → ℤ) (d n₁ n₂ : ℕ) :
    Int.natAbs (apSum f d (n₁ + n₂)) ≤
      Int.natAbs (apSum f d n₁) + Int.natAbs (apSumOffset f d n₁ n₂) := by
  -- This is `natAbs_apSumOffset_add_le` at `m = 0`, with the definitional rewrite
  -- `apSumOffset f d 0 _ = apSum f d _`.
  simpa [apSumOffset_zero_start] using
    (natAbs_apSumOffset_add_le (f := f) (d := d) (m := 0) (n₁ := n₁) (n₂ := n₂))

/-! ### Basic inequalities for sign sequences -/

/-! ### General `Int.natAbs` bounds for offset AP sums -/

/-- Uniform bound on `Int.natAbs` gives a length-times-bound estimate for offset AP sums.

If `|f k| ≤ B` for every term, then the offset AP partial sums satisfy
`|apSumOffset f d m n| ≤ n * B`.

This is the nucleus form of the standard “triangle inequality + induction on length” bound,
parameterised by the per-term bound `B`.
-/
lemma natAbs_apSumOffset_le_mul_of_natAbs_le {f : ℕ → ℤ} {B : ℕ}
    (hf : ∀ k, Int.natAbs (f k) ≤ B) (d m n : ℕ) :
    Int.natAbs (apSumOffset f d m n) ≤ n * B := by
  induction n with
  | zero =>
      simp [apSumOffset]
  | succ n ih =>
      have hterm : Int.natAbs (f ((m + n + 1) * d)) ≤ B := hf _
      have hsum :
          apSumOffset f d m (n + 1) =
            apSumOffset f d m n + f ((m + n + 1) * d) := by
        simp [apSumOffset, Finset.sum_range_succ, Nat.add_assoc]
      calc
        Int.natAbs (apSumOffset f d m (n + 1))
            = Int.natAbs (apSumOffset f d m n + f ((m + n + 1) * d)) := by
                simpa [hsum]
        _ ≤ Int.natAbs (apSumOffset f d m n) + Int.natAbs (f ((m + n + 1) * d)) := by
                simpa using
                  (Int.natAbs_add_le (apSumOffset f d m n) (f ((m + n + 1) * d)))
        _ ≤ n * B + B := by
                exact Nat.add_le_add ih hterm
        _ = (n + 1) * B := by
                simpa [Nat.succ_mul, Nat.add_assoc]

/-- Uniform bound on `Int.natAbs` gives a length-times-bound estimate for homogeneous AP sums.

This is the `apSum` specialization of `natAbs_apSumOffset_le_mul_of_natAbs_le`.
-/
lemma natAbs_apSum_le_mul_of_natAbs_le {f : ℕ → ℤ} {B : ℕ}
    (hf : ∀ k, Int.natAbs (f k) ≤ B) (d n : ℕ) :
    Int.natAbs (apSum f d n) ≤ n * B := by
  simpa [apSumOffset_zero_start] using
    (natAbs_apSumOffset_le_mul_of_natAbs_le (f := f) (B := B) (hf := hf) (d := d) (m := 0)
      (n := n))

/-- If the terms of `f` are uniformly bounded by `1` in `Int.natAbs`, then any offset AP sum has
`Int.natAbs` bounded by its length.

This is the nucleus form of the standard “triangle inequality + induction on length” bound.
-/
lemma natAbs_apSumOffset_le_of_natAbs_le_one {f : ℕ → ℤ}
    (hf : ∀ k, Int.natAbs (f k) ≤ 1) (d m n : ℕ) :
    Int.natAbs (apSumOffset f d m n) ≤ n := by
  induction n with
  | zero =>
      simp [apSumOffset]
  | succ n ih =>
      have hterm : Int.natAbs (f ((m + n + 1) * d)) ≤ 1 := hf _
      have hsum :
          apSumOffset f d m (n + 1) =
            apSumOffset f d m n + f ((m + n + 1) * d) := by
        simp [apSumOffset, Finset.sum_range_succ, Nat.add_assoc]
      calc
        Int.natAbs (apSumOffset f d m (n + 1))
            = Int.natAbs (apSumOffset f d m n + f ((m + n + 1) * d)) := by
                simpa [hsum]
        _ ≤ Int.natAbs (apSumOffset f d m n) + Int.natAbs (f ((m + n + 1) * d)) := by
                simpa using
                  (Int.natAbs_add_le (apSumOffset f d m n) (f ((m + n + 1) * d)))
        _ ≤ n + 1 :=
                Nat.add_le_add ih hterm

/-- A sign sequence has `Int.natAbs` bounded by length on any offset AP sum. -/
lemma natAbs_apSumOffset_le {f : ℕ → ℤ} (hf : IsSignSequence f) (d m n : ℕ) :
    Int.natAbs (apSumOffset f d m n) ≤ n := by
  refine natAbs_apSumOffset_le_of_natAbs_le_one (f := f) (d := d) (m := m) (n := n) ?_ 
  intro k
  rcases hf k with h | h <;> simp [h]

/-- If the terms of `f` are uniformly bounded by `1` in `Int.natAbs`, then any AP sum has
`Int.natAbs` bounded by its length.

This is the `apSum` specialization of `natAbs_apSumOffset_le_of_natAbs_le_one`.
-/
lemma natAbs_apSum_le_of_natAbs_le_one {f : ℕ → ℤ}
    (hf : ∀ k, Int.natAbs (f k) ≤ 1) (d n : ℕ) :
    Int.natAbs (apSum f d n) ≤ n := by
  simpa [apSumOffset_zero_start] using
    (natAbs_apSumOffset_le_of_natAbs_le_one (f := f) (hf := hf) (d := d) (m := 0) (n := n))

/-- A sign sequence has `Int.natAbs` bounded by length on any AP sum. -/
lemma natAbs_apSum_le {f : ℕ → ℤ} (hf : IsSignSequence f) (d n : ℕ) :
    Int.natAbs (apSum f d n) ≤ n := by
  simpa [apSumOffset_zero_start] using
    (natAbs_apSumOffset_le (hf := hf) (d := d) (m := 0) (n := n))

/-- Bounding a *difference of discrepancies* (offset AP sums) by total length.

Useful for triangle-inequality pipelines: `|Sₙ - Sₙ'| ≤ |Sₙ| + |Sₙ'| ≤ n + n'`.
-/
lemma natAbs_apSumOffset_sub_le {f : ℕ → ℤ} (hf : IsSignSequence f) (d m n n' : ℕ) :
    Int.natAbs (apSumOffset f d m n - apSumOffset f d m n') ≤ n + n' := by
  have hn : Int.natAbs (apSumOffset f d m n) ≤ n := natAbs_apSumOffset_le (hf := hf) d m n
  have hn' : Int.natAbs (apSumOffset f d m n') ≤ n' := natAbs_apSumOffset_le (hf := hf) d m n'
  -- `natAbs_sub_le` is the triangle inequality for subtraction.
  refine le_trans (Int.natAbs_sub_le (apSumOffset f d m n) (apSumOffset f d m n')) ?_
  -- Push the bound through addition.
  exact Nat.add_le_add hn hn'

/-- `f` has discrepancy at least `C` if some AP partial sum exceeds `C` in absolute value,
with a **positive** step size `d ≥ 1`.

We compare via `Int.natAbs` so `C : ℕ` stays natural.
-/
def HasDiscrepancyAtLeast (f : ℕ → ℤ) (C : ℕ) : Prop :=
  ∃ d n : ℕ, d > 0 ∧ Int.natAbs (apSum f d n) > C

/-- Sign-flip invariance: negating the sequence does not change discrepancy. -/
@[simp] lemma HasDiscrepancyAtLeast_neg_iff (f : ℕ → ℤ) (C : ℕ) :
    HasDiscrepancyAtLeast (fun k => -f k) C ↔ HasDiscrepancyAtLeast f C := by
  constructor
  · rintro ⟨d, n, hd, hgt⟩
    refine ⟨d, n, hd, ?_⟩
    have hnatAbs : Int.natAbs (apSum (fun k => -f k) d n) = Int.natAbs (apSum f d n) := by
      unfold apSum
      simp
    simpa [hnatAbs] using hgt
  · rintro ⟨d, n, hd, hgt⟩
    refine ⟨d, n, hd, ?_⟩
    have hnatAbs : Int.natAbs (apSum (fun k => -f k) d n) = Int.natAbs (apSum f d n) := by
      unfold apSum
      simp
    -- Rewrite the goal to match `hgt`.
    simpa [hnatAbs] using hgt

/-- Monotonicity of `HasDiscrepancyAtLeast` in the bound. -/
lemma HasDiscrepancyAtLeast.mono {f : ℕ → ℤ} {C₁ C₂ : ℕ}
    (h : HasDiscrepancyAtLeast f C₂) (hC : C₁ ≤ C₂) : HasDiscrepancyAtLeast f C₁ := by
  rcases h with ⟨d, n, hd, hn⟩
  exact ⟨d, n, hd, lt_of_le_of_lt hC hn⟩

/-- Decrease the bound by one. -/
lemma HasDiscrepancyAtLeast.of_succ {f : ℕ → ℤ} {C : ℕ}
    (h : HasDiscrepancyAtLeast f (C + 1)) : HasDiscrepancyAtLeast f C := by
  exact
    HasDiscrepancyAtLeast.mono (f := f) (C₁ := C) (C₂ := C + 1) h (Nat.le_succ C)

/-- If we can beat every bound by one, we can beat every bound.

This is a small but frequently useful “quantifier-level” normal form: it lets you assume a
strictly-stronger hypothesis `HasDiscrepancyAtLeast f (C+1)` and immediately obtain the standard
unbounded-discrepancy statement.
-/
theorem forall_hasDiscrepancyAtLeast_of_succ (f : ℕ → ℤ) :
    (∀ C : ℕ, HasDiscrepancyAtLeast f (C + 1)) → (∀ C : ℕ, HasDiscrepancyAtLeast f C) := by
  intro h C
  exact HasDiscrepancyAtLeast.of_succ (h C)

/-- From a discrepancy witness obtain `d` and `n` both positive. -/
lemma HasDiscrepancyAtLeast.exists_witness_pos {f : ℕ → ℤ} {C : ℕ}
    (h : HasDiscrepancyAtLeast f C) :
    ∃ d n, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  rcases h with ⟨d, n, hd, hgt⟩
  cases n with
  | zero =>
      -- `apSum f d 0 = 0`, so `natAbs` cannot be strictly greater than `C`.
      exfalso
      have : (0 : ℕ) > C := by
        simpa [apSum] using hgt
      have hgt' : C < 0 := by
        simpa [gt_iff_lt] using this
      exact Nat.not_lt_zero C hgt'
  | succ n' =>
      refine ⟨d, Nat.succ n', hd, Nat.succ_pos n', ?_⟩
      exact hgt

/-- From a discrepancy witness obtain a step size `d ≥ 1`. -/
lemma HasDiscrepancyAtLeast.exists_witness_d_ge_one {f : ℕ → ℤ} {C : ℕ}
    (h : HasDiscrepancyAtLeast f C) :
    ∃ d n, d ≥ 1 ∧ Int.natAbs (apSum f d n) > C := by
  rcases h with ⟨d, n, hd, hgt⟩
  exact ⟨d, n, Nat.succ_le_of_lt hd, hgt⟩

/-- From a discrepancy witness obtain `d ≥ 1` *and* `n > 0`.

This is a common “surface statement” normal form when working with natural step sizes.
-/
lemma HasDiscrepancyAtLeast.exists_witness_d_ge_one_pos {f : ℕ → ℤ} {C : ℕ}
    (h : HasDiscrepancyAtLeast f C) :
    ∃ d n, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  rcases HasDiscrepancyAtLeast.exists_witness_pos (h := h) with ⟨d, n, hd, hn, hgt⟩
  exact ⟨d, n, Nat.succ_le_of_lt hd, hn, hgt⟩

/-- `HasDiscrepancyAtLeast` can be stated with `d` and `n` both positive.

This is often the most readable form for conjecture statements, and it lets you
convert back to the nucleus predicate without unfolding definitions.
-/
lemma HasDiscrepancyAtLeast_iff_exists_witness_pos {f : ℕ → ℤ} {C : ℕ} :
    HasDiscrepancyAtLeast f C ↔
      ∃ d n, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  constructor
  · intro h
    exact HasDiscrepancyAtLeast.exists_witness_pos (h := h)
  · rintro ⟨d, n, hd, hn, hgt⟩
    exact ⟨d, n, hd, hgt⟩

/-- Normal form: rewrite `HasDiscrepancyAtLeast` using the offset-sum API `apSumOffset … 0 n`.

This is definitionally the same notion (since `apSumOffset f d 0 n = apSum f d n`), but it is
sometimes more convenient when downstream developments are already in the “tail sum” vocabulary.
-/
lemma HasDiscrepancyAtLeast_iff_exists_apSumOffset_zero {f : ℕ → ℤ} {C : ℕ} :
    HasDiscrepancyAtLeast f C ↔
      ∃ d n : ℕ, d > 0 ∧ Int.natAbs (apSumOffset f d 0 n) > C := by
  constructor
  · rintro ⟨d, n, hd, hgt⟩
    refine ⟨d, n, hd, ?_⟩
    -- NOTE: `apSumOffset_zero_start` is proved later in this file, so we unfold here.
    have h0 : apSumOffset f d 0 n = apSum f d n := by
      unfold apSumOffset apSum
      simp
    simpa [h0] using hgt
  · rintro ⟨d, n, hd, hgt⟩
    refine ⟨d, n, hd, ?_⟩
    have h0 : apSumOffset f d 0 n = apSum f d n := by
      unfold apSumOffset apSum
      simp
    -- rewrite the offset-sum witness back into the homogeneous-sum form.
    simpa [h0] using hgt

-- Backwards-compatibility: earlier versions used the slightly confusing name
-- `HasDiscrepancyAtLeast_iff_exists_apSumOffset_zero_m`.
lemma HasDiscrepancyAtLeast_iff_exists_apSumOffset_zero_start {f : ℕ → ℤ} {C : ℕ} :
    HasDiscrepancyAtLeast f C ↔
      ∃ d n : ℕ, d > 0 ∧ Int.natAbs (apSumOffset f d 0 n) > C := by
  simpa using (HasDiscrepancyAtLeast_iff_exists_apSumOffset_zero (f := f) (C := C))

/-- Restate `HasDiscrepancyAtLeast` using the `discrepancy` wrapper. -/
lemma HasDiscrepancyAtLeast_iff_exists_discrepancy (f : ℕ → ℤ) (C : ℕ) :
    HasDiscrepancyAtLeast f C ↔ ∃ d n, d > 0 ∧ discrepancy f d n > C := by
  unfold HasDiscrepancyAtLeast discrepancy
  constructor
  · rintro ⟨d, n, hd, hgt⟩
    exact ⟨d, n, hd, hgt⟩
  · rintro ⟨d, n, hd, hgt⟩
    exact ⟨d, n, hd, hgt⟩

/-- Variant with the step-size side condition written as `d ≥ 1`. -/
lemma HasDiscrepancyAtLeast_iff_exists_discrepancy_ge_one (f : ℕ → ℤ) (C : ℕ) :
    HasDiscrepancyAtLeast f C ↔ ∃ d n, d ≥ 1 ∧ discrepancy f d n > C := by
  constructor
  · rintro ⟨d, n, hd, hgt⟩
    exact ⟨d, n, Nat.succ_le_of_lt hd, hgt⟩
  · rintro ⟨d, n, hd, hgt⟩
    exact ⟨d, n, (Nat.succ_le_iff).1 hd, hgt⟩

/-- Variant with side conditions `d ≥ 1` and `n > 0` (useful for “surface statement” witnesses). -/
lemma HasDiscrepancyAtLeast_iff_exists_discrepancy_ge_one_witness_pos (f : ℕ → ℤ) (C : ℕ) :
    HasDiscrepancyAtLeast f C ↔ ∃ d n, d ≥ 1 ∧ n > 0 ∧ discrepancy f d n > C := by
  constructor
  · intro h
    rcases HasDiscrepancyAtLeast.exists_witness_d_ge_one_pos (h := h) with ⟨d, n, hd, hn, hgt⟩
    refine ⟨d, n, hd, hn, ?_⟩
    simpa using hgt
  · rintro ⟨d, n, hd, _hn, hgt⟩
    refine ⟨d, n, (Nat.succ_le_iff).1 hd, ?_⟩
    simpa using hgt

/-- The “unbounded discrepancy” statement `∀ C, HasDiscrepancyAtLeast f C` is equivalent to
the more explicit witness form `∀ C, ∃ d n > 0, …`.

This is the intended bridge for conjecture stubs: state the theorem using the nucleus predicate,
and rewrite to the quantifier-heavy version only when needed.
-/
theorem forall_hasDiscrepancyAtLeast_iff_forall_exists_witness_pos (f : ℕ → ℤ) :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ, ∃ d n : ℕ, d > 0 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C) := by
  constructor
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_witness_pos (f := f) (C := C)).1 (h C)
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_witness_pos (f := f) (C := C)).2 (h C)

/-- The step-size side condition `d > 0` can be written as `d ≥ 1`. -/
lemma HasDiscrepancyAtLeast_iff_exists_d_ge_one {f : ℕ → ℤ} {C : ℕ} :
    HasDiscrepancyAtLeast f C ↔ ∃ d n, d ≥ 1 ∧ Int.natAbs (apSum f d n) > C := by
  constructor
  · intro h
    exact HasDiscrepancyAtLeast.exists_witness_d_ge_one (h := h)
  · rintro ⟨d, n, hd, hgt⟩
    refine ⟨d, n, ?_, hgt⟩
    exact (Nat.succ_le_iff).1 hd

/-- Convenience witness normal form: `HasDiscrepancyAtLeast f C` has a witness with
`d ≥ 1` and `n > 0`.

The `n > 0` side condition is automatic from `Int.natAbs (apSum f d n) > C`, but it is often
useful to keep it explicit in “surface” statements.
-/
lemma HasDiscrepancyAtLeast_iff_exists_d_ge_one_witness_pos {f : ℕ → ℤ} {C : ℕ} :
    HasDiscrepancyAtLeast f C ↔
      ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C := by
  constructor
  · intro h
    rcases HasDiscrepancyAtLeast.exists_witness_pos (h := h) with ⟨d, n, hd, hn, hgt⟩
    exact ⟨d, n, Nat.succ_le_of_lt hd, hn, hgt⟩
  · rintro ⟨d, n, hd, _hn, hgt⟩
    refine ⟨d, n, (Nat.succ_le_iff).1 hd, hgt⟩

/-- Bridge: the unbounded discrepancy statement `∀ C, HasDiscrepancyAtLeast f C` is equivalent to
an explicit witness form with side conditions `d ≥ 1` and `n > 0`.
-/
theorem forall_hasDiscrepancyAtLeast_iff_forall_exists_d_ge_one_witness_pos (f : ℕ → ℤ) :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ, ∃ d n : ℕ, d ≥ 1 ∧ n > 0 ∧ Int.natAbs (apSum f d n) > C) := by
  constructor
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_d_ge_one_witness_pos (f := f) (C := C)).1 (h C)
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_d_ge_one_witness_pos (f := f) (C := C)).2 (h C)

/-- Unpack the defining property. -/
lemma IsSignSequence.eq_one_or_eq_neg_one {f : ℕ → ℤ} (hf : IsSignSequence f) (n : ℕ) :
    f n = 1 ∨ f n = -1 :=
  hf n

/-- A sign sequence stays a sign sequence after reindexing by any function `g : ℕ → ℕ`. -/
lemma IsSignSequence.comp {f : ℕ → ℤ} (g : ℕ → ℕ) (hf : IsSignSequence f) :
    IsSignSequence (fun n => f (g n)) := by
  intro n
  simpa using hf (g n)

/-- Reindexing a sign sequence by a fixed additive shift preserves the sign-sequence property.

This uses the translation-friendly convention `n ↦ n + k`.
-/
lemma IsSignSequence.shift_add {f : ℕ → ℤ} (k : ℕ) (hf : IsSignSequence f) :
    IsSignSequence (fun n => f (n + k)) :=
  IsSignSequence.comp (f := f) (fun n => n + k) hf

/-- Add-left variant of `IsSignSequence.shift_add`.

This uses the `n ↦ k + n` binder convention.
-/
lemma IsSignSequence.shift_add_left {f : ℕ → ℤ} (k : ℕ) (hf : IsSignSequence f) :
    IsSignSequence (fun n => f (k + n)) :=
  IsSignSequence.comp (f := f) (fun n => k + n) hf

/-- Reindexing a sign sequence by a fixed multiplicative map preserves the sign-sequence property. -/
lemma IsSignSequence.map_mul {f : ℕ → ℤ} (k : ℕ) (hf : IsSignSequence f) :
    IsSignSequence (fun n => f (n * k)) :=
  IsSignSequence.comp (f := f) (fun n => n * k) hf

lemma IsSignSequence.natAbs_eq_one {f : ℕ → ℤ} (hf : IsSignSequence f) (n : ℕ) :
    Int.natAbs (f n) = 1 := by
  rcases hf n with h | h <;> simp [h]

/-- Normal form: a function is a sign sequence iff all its values have `Int.natAbs = 1`.

This is often the most convenient way to *consume* the `IsSignSequence` hypothesis in proofs,
while the `f n = 1 ∨ f n = -1` form is convenient to *produce* it.
-/
lemma isSignSequence_iff_forall_natAbs_eq_one (f : ℕ → ℤ) :
    IsSignSequence f ↔ ∀ n, Int.natAbs (f n) = 1 := by
  constructor
  · intro hf n
    exact IsSignSequence.natAbs_eq_one (hf := hf) n
  · intro h n
    -- use the `natAbs` normal form to recover the `±1` pointwise description
    have hn : (f n).natAbs = 1 := h n
    have h' : f n = (1 : ℤ) ∨ f n = - (1 : ℤ) := (Int.natAbs_eq_iff (a := f n) (n := 1)).1 hn
    simpa using h'

/-- Normal form: a function is a sign sequence iff all its values have `abs = 1`.

This is a sibling of `isSignSequence_iff_forall_natAbs_eq_one` that can be convenient when you
want to stay in `ℤ` instead of converting through `Int.natAbs`.
-/
lemma isSignSequence_iff_forall_abs_eq_one (f : ℕ → ℤ) :
    IsSignSequence f ↔ ∀ n, abs (f n) = (1 : ℤ) := by
  constructor
  · intro hf n
    rcases hf n with h | h <;> simp [h]
  · intro h n
    -- `abs x = 1` implies `x = 1 ∨ x = -1`.
    have h' : f n = (1 : ℤ) ∨ f n = - (1 : ℤ) :=
      (abs_eq (zero_le_one' ℤ)).1 (h n)
    simpa using h'

/-- Normal form: for a sign sequence, the integer absolute value satisfies `|f n| = 1`. -/
lemma IsSignSequence.abs_eq_one {f : ℕ → ℤ} (hf : IsSignSequence f) (n : ℕ) :
    abs (f n) = 1 := by
  rcases hf n with h | h <;> simp [h]

/-- A sign sequence is pointwise bounded by `1` in absolute value. -/
lemma IsSignSequence.abs_le_one {f : ℕ → ℤ} (hf : IsSignSequence f) (n : ℕ) :
    abs (f n) ≤ 1 := by
  simp [hf.abs_eq_one n]

/-- Any ±1 sequence has discrepancy at least 0 (take d = 1, n = 1). -/
lemma IsSignSequence.hasDiscrepancyAtLeast_zero {f : ℕ → ℤ} (hf : IsSignSequence f) :
    HasDiscrepancyAtLeast f 0 := by
  unfold HasDiscrepancyAtLeast
  refine ⟨1, 1, ?_, ?_⟩
  · decide
  · simp [apSum, IsSignSequence.natAbs_eq_one (hf := hf) 1]

lemma IsSignSequence.intNatAbs_eq_one {f : ℕ → ℤ} (hf : IsSignSequence f) (n : ℕ) :
    (Int.natAbs (f n) : ℤ) = 1 := by
  simpa using
    congrArg (fun k : ℕ => (k : ℤ)) (IsSignSequence.natAbs_eq_one (hf := hf) n)

lemma IsSignSequence.ne_zero {f : ℕ → ℤ} (hf : IsSignSequence f) (n : ℕ) : f n ≠ 0 := by
  rcases hf n with h | h <;> simp [h]

/-- Helper lemmas for `Int.natAbs`. -/
lemma natAbs_pos_of_ne_zero {c : ℤ} (hc : c ≠ 0) : 0 < Int.natAbs c := by
  exact Int.natAbs_pos.2 hc

lemma one_le_natAbs_of_ne_zero {c : ℤ} (hc : c ≠ 0) : 1 ≤ Int.natAbs c := by
  exact Nat.succ_le_iff.2 (natAbs_pos_of_ne_zero (c := c) hc)

@[simp] lemma apSum_zero (f : ℕ → ℤ) (d : ℕ) : apSum f d 0 = 0 := by
  simp [apSum]

@[simp] lemma apSum_one (f : ℕ → ℤ) (d : ℕ) : apSum f d 1 = f d := by
  simp [apSum]

/-- Rewrite `apSum` as the more familiar sum `∑ i ∈ Icc 1 n, f (i*d)`.

This is intended for conjecture/theorem statements: it matches the usual notation
`∑_{i=1}^n f(i*d)` while the nucleus API continues to use `apSum`.
-/
lemma apSum_eq_sum_Icc (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d n = (Finset.Icc 1 n).sum (fun i => f (i * d)) := by
  classical
  unfold apSum
  -- `Icc 1 n` is `Ico 1 (n+1)`; convert interval sums to `Finset.range`.
  have h :=
    (Finset.sum_Ico_eq_sum_range (f := fun i => f (i * d)) (m := 1) (n := n + 1))
  -- `h` is oriented from `Ico` to `range`; we use it backwards.
  calc
    (Finset.range n).sum (fun i => f ((i + 1) * d))
        = (Finset.range n).sum (fun i => f ((1 + i) * d)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            -- `i + 1 = 1 + i`
            simp [Nat.add_comm]
    _ = (Finset.Ico 1 (n + 1)).sum (fun i => f (i * d)) := by
            simpa [Nat.add_sub_cancel] using h.symm
    _ = (Finset.Icc 1 n).sum (fun i => f (i * d)) := by
            simp [Finset.Ico_add_one_right_eq_Icc]

/-- Normal form: rewrite the “paper notation” interval sum `∑ i ∈ Icc 1 n, f (i*d)` back to `apSum`.

This is useful when starting from a surface statement and normalizing into the nucleus API.
-/
lemma sum_Icc_eq_apSum (f : ℕ → ℤ) (d n : ℕ) :
    (Finset.Icc 1 n).sum (fun i => f (i * d)) = apSum f d n := by
  simpa using (apSum_eq_sum_Icc (f := f) (d := d) (n := n)).symm

/-!
Note: deprecated `*_mul_left` paper-notation wrappers live in `MoltResearch.Discrepancy.Deprecated`.
The stable surface uses the `i * d` convention (`apSum_eq_sum_Icc` / `sum_Icc_eq_apSum`).
-/


/-- Special case: step size `d = 1` turns `apSum` into the plain interval sum `∑ i ∈ Icc 1 n, f i`.

This is often the most readable surface form when you have already normalized the step size.
-/
lemma apSum_one_d (f : ℕ → ℤ) (n : ℕ) : apSum f 1 n = (Finset.Icc 1 n).sum f := by
  simpa using (apSum_eq_sum_Icc (f := f) (d := 1) (n := n))

/-- `HasDiscrepancyAtLeast` can be stated using the more familiar interval sum
`∑ i ∈ Icc 1 n, f (i*d)`.

This is a convenience lemma for conjecture/theorem statements: keep the nucleus
predicate as the normalization boundary, and rewrite to this form only at the surface.
-/
lemma HasDiscrepancyAtLeast_iff_exists_sum_Icc {f : ℕ → ℤ} {C : ℕ} :
    HasDiscrepancyAtLeast f C ↔
      ∃ d n : ℕ, d > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  constructor
  · rintro ⟨d, n, hd, hgt⟩
    refine ⟨d, n, hd, ?_⟩
    simpa [apSum_eq_sum_Icc] using hgt
  · rintro ⟨d, n, hd, hgt⟩
    refine ⟨d, n, hd, ?_⟩
    simpa [apSum_eq_sum_Icc] using hgt

/-- Variant of `HasDiscrepancyAtLeast_iff_exists_sum_Icc` writing the step-size side condition
as `d ≥ 1` instead of `d > 0`.

This is often the most readable surface form when `d : ℕ`.
-/
lemma HasDiscrepancyAtLeast_iff_exists_sum_Icc_d_ge_one {f : ℕ → ℤ} {C : ℕ} :
    HasDiscrepancyAtLeast f C ↔
      ∃ d n : ℕ, d ≥ 1 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  constructor
  · intro h
    rcases (HasDiscrepancyAtLeast_iff_exists_d_ge_one (f := f) (C := C)).1 h with ⟨d, n, hd, hgt⟩
    refine ⟨d, n, hd, ?_⟩
    simpa [apSum_eq_sum_Icc] using hgt
  · rintro ⟨d, n, hd, hgt⟩
    refine (HasDiscrepancyAtLeast_iff_exists_d_ge_one (f := f) (C := C)).2 ?_
    refine ⟨d, n, hd, ?_⟩
    simpa [apSum_eq_sum_Icc] using hgt

/-- Variant of `HasDiscrepancyAtLeast_iff_exists_sum_Icc_d_ge_one` that also records the (automatic)
side condition `n > 0`.

This is often the cleanest “paper notation” witness normal form: a positive step size `d ≥ 1`,
a positive length, and an interval sum exceeding the bound.
-/
lemma HasDiscrepancyAtLeast_iff_exists_sum_Icc_d_ge_one_witness_pos {f : ℕ → ℤ} {C : ℕ} :
    HasDiscrepancyAtLeast f C ↔
      ∃ d n : ℕ,
        d ≥ 1 ∧ n > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  constructor
  · intro h
    rcases HasDiscrepancyAtLeast.exists_witness_pos (h := h) with ⟨d, n, hd, hn, hgt⟩
    refine ⟨d, n, Nat.succ_le_of_lt hd, hn, ?_⟩
    simpa [apSum_eq_sum_Icc] using hgt
  · rintro ⟨d, n, hd, _hn, hgt⟩
    refine ⟨d, n, ?_, ?_⟩
    · exact lt_of_lt_of_le Nat.zero_lt_one hd
    · simpa [apSum_eq_sum_Icc] using hgt

/-- Bridge: `∀ C, HasDiscrepancyAtLeast f C` written in the interval-sum witness normal form
with side conditions `d ≥ 1` and `n > 0`.
-/
theorem forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one_witness_pos (f : ℕ → ℤ) :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ,
        ∃ d n : ℕ,
          d ≥ 1 ∧ n > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C) := by
  constructor
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_sum_Icc_d_ge_one_witness_pos (f := f) (C := C)).1 (h C)
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_sum_Icc_d_ge_one_witness_pos (f := f) (C := C)).2 (h C)

/-- Variant of `HasDiscrepancyAtLeast_iff_exists_sum_Icc` that also records the (automatic)
side condition `n > 0`.

This is the closest match to the usual “paper statement” of the Erdős discrepancy problem: a
positive step size `d > 0`, a positive length, and an interval sum exceeding the bound.
-/
lemma HasDiscrepancyAtLeast_iff_exists_sum_Icc_witness_pos {f : ℕ → ℤ} {C : ℕ} :
    HasDiscrepancyAtLeast f C ↔
      ∃ d n : ℕ,
        d > 0 ∧ n > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C := by
  constructor
  · intro h
    rcases
        (HasDiscrepancyAtLeast_iff_exists_sum_Icc_d_ge_one_witness_pos (f := f) (C := C)).1 h with
      ⟨d, n, hd, hn, hgt⟩
    exact ⟨d, n, lt_of_lt_of_le Nat.zero_lt_one hd, hn, hgt⟩
  · rintro ⟨d, n, hd, hn, hgt⟩
    refine (HasDiscrepancyAtLeast_iff_exists_sum_Icc_d_ge_one_witness_pos (f := f) (C := C)).2 ?_
    exact ⟨d, n, Nat.succ_le_of_lt hd, hn, hgt⟩

/-- Bridge: `∀ C, HasDiscrepancyAtLeast f C` written in the interval-sum witness normal form
with side conditions `d > 0` and `n > 0`.
-/
theorem forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_witness_pos (f : ℕ → ℤ) :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ,
        ∃ d n : ℕ,
          d > 0 ∧ n > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C) := by
  constructor
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_sum_Icc_witness_pos (f := f) (C := C)).1 (h C)
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_sum_Icc_witness_pos (f := f) (C := C)).2 (h C)

/-- Bridge: the unbounded discrepancy statement phrased using `HasDiscrepancyAtLeast`
is equivalent to the more explicit “interval sum” form `∑ i ∈ Icc 1 n, f (i*d)`.

This is intended for conjecture/theorem statements: downstream files can keep the nucleus
predicate as a normalization boundary, and then rewrite to the quantifier-heavy surface form
without unfolding definitions.
-/
theorem forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc (f : ℕ → ℤ) :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ,
        ∃ d n : ℕ,
          d > 0 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C) := by
  constructor
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_sum_Icc (f := f) (C := C)).1 (h C)
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_sum_Icc (f := f) (C := C)).2 (h C)

/-- Bridge: the unbounded discrepancy statement `∀ C, HasDiscrepancyAtLeast f C` is equivalent to
an explicit witness form using the interval sum `∑ i ∈ Icc 1 n, f (i*d)` with side condition
`d ≥ 1` (instead of `d > 0`).

This is intended as a surface rewrite lemma: keep `HasDiscrepancyAtLeast` as the normalization
boundary and only expand to quantifiers when needed.
-/
theorem forall_hasDiscrepancyAtLeast_iff_forall_exists_sum_Icc_d_ge_one (f : ℕ → ℤ) :
    (∀ C : ℕ, HasDiscrepancyAtLeast f C) ↔
      (∀ C : ℕ,
        ∃ d n : ℕ,
          d ≥ 1 ∧ Int.natAbs ((Finset.Icc 1 n).sum (fun i => f (i * d))) > C) := by
  constructor
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_sum_Icc_d_ge_one (f := f) (C := C)).1 (h C)
  · intro h C
    exact (HasDiscrepancyAtLeast_iff_exists_sum_Icc_d_ge_one (f := f) (C := C)).2 (h C)

/-! ### Degenerate length simp lemmas

These mirror `apSum_zero` / `apSum_one` for the offset nucleus `apSumOffset`.
-/
section apSumOffset_degenerate

@[simp] lemma apSumOffset_zero (f : ℕ → ℤ) (d m : ℕ) : apSumOffset f d m 0 = 0 := by
  simp [apSumOffset]

@[simp] lemma apSumOffset_one (f : ℕ → ℤ) (d m : ℕ) : apSumOffset f d m 1 = f ((m + 1) * d) := by
  simp [apSumOffset]

end apSumOffset_degenerate

-- (deprecated alias moved to `MoltResearch.Discrepancy.Deprecated`)

lemma apSumOffset_succ (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m (n + 1) = apSumOffset f d m n + f ((m + n + 1) * d) := by
  classical
  -- expand definition and use `Finset.range_add_one`
  unfold apSumOffset
  simp [Finset.range_add_one, Finset.sum_insert, add_comm, add_assoc]

lemma apSum_eq_apSumOffset (f : ℕ → ℤ) (d n : ℕ) : apSum f d n = apSumOffset f d 0 n := by
  unfold apSum apSumOffset
  simp

/- (deprecated aliases for `apSumOffset_zero_start` live in `MoltResearch.Discrepancy.Deprecated`). -/

/-- Normal form (“step-one”): express a homogeneous AP sum as an `apSum` with step size `1`
by bundling the step size `d` into the summand.

This is the homogeneous analogue of `apSumOffset_eq_apSum_step_one` and
`apSumFrom_eq_apSum_step_one`.
-/
lemma apSum_eq_apSum_step_one (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d n = apSum (fun k => f (k * d)) 1 n := by
  unfold apSum
  simp

-- (deprecated alias `apSum_step_one_eq_apSum` moved to `MoltResearch.Discrepancy.Deprecated`)

/-! ### Normal forms for shifts (step-one presentation) -/

/-!
## Normalization of nested shifts

We frequently encounter functions of the form `fun k => f (k + a + b)`.
For a tidy normal form we prefer the addition to be grouped as `k + (a + b)`.

This is a tiny `[simp]` rule that rewrites the former into the latter without introducing a simp loop.
Only associativity is used, so the orientation is safe.
-/

@[simp] lemma fun_shift_add_assoc {α : Type*} (f : ℕ → α) (a b : ℕ) :
  (fun k => f (k + a + b)) = fun k => f (k + (a + b)) := by
  funext k
  simp [Nat.add_assoc]


/-- Normal form: shifting the index in the step-one presentation corresponds to `apSumOffset`.

This is the key rewrite used when we first normalize `apSum f d n` into the step-one form
`apSum (fun k => f (k*d)) 1 n`, then want to skip an initial segment.
-/
lemma apSum_step_one_shift_eq_apSumOffset (f : ℕ → ℤ) (d a n : ℕ) :
    apSum (fun k => f ((k + a) * d)) 1 n = apSumOffset f d a n := by
  unfold apSum apSumOffset
  simp [Nat.add_assoc, Nat.add_comm]

/-- The corresponding `discrepancy` normal form. -/
@[simp] lemma discrepancy_step_one_shift (f : ℕ → ℤ) (d a n : ℕ) :
    discrepancy (fun k => f ((k + a) * d)) 1 n = Int.natAbs (apSumOffset f d a n) := by
  unfold discrepancy
  simp [apSum_step_one_shift_eq_apSumOffset]

lemma apSum_succ (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d (n + 1) = apSum f d n + f ((n + 1) * d) := by
  classical
  -- `Finset.range (n+1)` is `insert n (range n)`
  simp [apSum, Finset.range_add_one, Finset.sum_insert]
  -- remaining goal is just commutativity
  simp [add_comm]

@[simp] lemma apSum_two (f : ℕ → ℤ) (d : ℕ) : apSum f d 2 = f d + f (2 * d) := by
  simpa [apSum_one] using (apSum_succ (f := f) (d := d) (n := 1))

/-- Split `apSum` over a sum of lengths: `apSum f d (m + n)` equals the sum over the first `m`
terms plus the sum over the next `n` terms. -/
lemma apSum_add_length (f : ℕ → ℤ) (d m n : ℕ) :
    apSum f d (m + n) = apSum f d m + apSumOffset f d m n := by
  classical
  unfold apSum apSumOffset
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (Finset.sum_range_add (fun i => f ((i + 1) * d)) m n)

/-- Alias of `apSum_add_length` with the more symmetric “`n₁`/`n₂`” naming. -/
lemma apSum_add_len (f : ℕ → ℤ) (d n₁ n₂ : ℕ) :
    apSum f d (n₁ + n₂) = apSum f d n₁ + apSumOffset f d n₁ n₂ := by
  simpa using (apSum_add_length (f := f) (d := d) (m := n₁) (n := n₂))

/-- `simp`-friendly corollary of `apSum_add_len` for `n₁ = 0`. -/
@[simp] lemma apSum_add_len_zero_left (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d (0 + n) = apSum f d n := by
  simpa [apSum_add_len] using
    (apSum_add_len (f := f) (d := d) (n₁ := 0) (n₂ := n))

/-- `simp`-friendly corollary of `apSum_add_len` for `n₂ = 0`. -/
@[simp] lemma apSum_add_len_zero_right (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d (n + 0) = apSum f d n := by
  simpa [apSum_add_len] using
    (apSum_add_len (f := f) (d := d) (n₁ := n) (n₂ := 0))

/-- `simp`-friendly corollary of `apSum_add_length` for `m = 0`. -/
@[simp] lemma apSum_add_length_zero_left (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d (0 + n) = apSum f d n := by
  simpa [apSum_add_length] using (apSum_add_length (f := f) (d := d) (m := 0) (n := n))

/-- `simp`-friendly corollary of `apSum_add_length` for `n = 0`. -/
@[simp] lemma apSum_add_length_zero_right (f : ℕ → ℤ) (d m : ℕ) :
    apSum f d (m + 0) = apSum f d m := by
  simpa [apSum_add_length] using (apSum_add_length (f := f) (d := d) (m := m) (n := 0))

/-- First-term decomposition for a homogeneous AP sum.

This is a convenient “head + tail” normal form, pairing the first term `f d` with an offset sum.
Compare `apSumOffset_succ_length` for the analogous lemma on `apSumOffset`.
-/
lemma apSum_succ_length (f : ℕ → ℤ) (d n : ℕ) :
    apSum f d (n + 1) = f d + apSumOffset f d 1 n := by
  -- rewrite using the length-splitting lemma at `m = 1`
  have h := apSum_add_length (f := f) (d := d) (m := 1) (n := n)
  -- normalize `1 + n` to `n + 1` and `apSum f d 1` to `f d`
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

-- (See `MoltResearch/Discrepancy/Offset.lean` for `apSumOffset_eq_sub` and related lemmas.)

/-- Split an offset AP sum over a sum of lengths. -/
lemma apSumOffset_add_length (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    apSumOffset f d m (n₁ + n₂) = apSumOffset f d m n₁ + apSumOffset f d (m + n₁) n₂ := by
  classical
  unfold apSumOffset
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (Finset.sum_range_add (fun i => f ((m + i + 1) * d)) n₁ n₂)

/-- `simp`-friendly corollary of `apSumOffset_add_length` for `n₁ = 0`. -/
@[simp] lemma apSumOffset_add_length_zero_left (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m (0 + n) = apSumOffset f d m n := by
  simpa [apSumOffset_add_length] using
    (apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := 0) (n₂ := n))

/-- `simp`-friendly corollary of `apSumOffset_add_length` for `n₂ = 0`. -/
@[simp] lemma apSumOffset_add_length_zero_right (f : ℕ → ℤ) (d m n : ℕ) :
    apSumOffset f d m (n + 0) = apSumOffset f d m n := by
  simpa [apSumOffset_add_length] using
    (apSumOffset_add_length (f := f) (d := d) (m := m) (n₁ := n) (n₂ := 0))

/-- Triangle inequality API for splitting an offset AP sum by length. -/
lemma natAbs_apSumOffset_add_length_le (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    Int.natAbs (apSumOffset f d m (n₁ + n₂)) ≤
      Int.natAbs (apSumOffset f d m n₁) + Int.natAbs (apSumOffset f d (m + n₁) n₂) := by
  -- Normalize the LHS to a sum of two offset sums, then apply `natAbs_add_le`.
  simpa [apSumOffset_add_length] using
    (Int.natAbs_add_le (apSumOffset f d m n₁) (apSumOffset f d (m + n₁) n₂))

/-- Triangle inequality API for splitting `discOffset` by length.

This is a wrapper around `natAbs_apSumOffset_add_length_le`, using the `discOffset` simp bridge.
-/
lemma discOffset_add_length_le (f : ℕ → ℤ) (d m n₁ n₂ : ℕ) :
    discOffset f d m (n₁ + n₂) ≤
      discOffset f d m n₁ + discOffset f d (m + n₁) n₂ := by
  simpa using
    (natAbs_apSumOffset_add_length_le (f := f) (d := d) (m := m) (n₁ := n₁) (n₂ := n₂))

/-- Triangle inequality API for splitting a homogeneous AP sum by length. -/
lemma natAbs_apSum_add_length_le (f : ℕ → ℤ) (d n₁ n₂ : ℕ) :
    Int.natAbs (apSum f d (n₁ + n₂)) ≤
      Int.natAbs (apSum f d n₁) + Int.natAbs (apSumOffset f d n₁ n₂) := by
  -- `apSum_add_length` (with `m = n₁`) is the canonical length-splitting normal form.
  simpa [apSum_add_length] using
    (Int.natAbs_add_le (apSum f d n₁) (apSumOffset f d n₁ n₂))

-- Algebraic properties of `apSum`
lemma apSum_add (f g : ℕ → ℤ) (d n : ℕ) :
    apSum (fun k => f k + g k) d n = apSum f d n + apSum g d n := by
  classical
  unfold apSum
  simp [Finset.sum_add_distrib]

@[simp] lemma apSum_neg (f : ℕ → ℤ) (d n : ℕ) :
    apSum (fun k => - f k) d n = - apSum f d n := by
  classical
  unfold apSum
  simp [Finset.sum_neg_distrib]

/-- `discrepancy` is invariant under pointwise negation. -/
@[simp] lemma discrepancy_neg (f : ℕ → ℤ) (d n : ℕ) :
    discrepancy (fun k => -f k) d n = discrepancy f d n := by
  unfold discrepancy
  simp [apSum_neg]

lemma apSum_sub (f g : ℕ → ℤ) (d n : ℕ) :
    apSum (fun k => f k - g k) d n = apSum f d n - apSum g d n := by
  classical
  unfold apSum
  simp [Finset.sum_sub_distrib]

/-- Multiplication by a fixed integer on the left commutes with `apSum`. -/
@[simp] lemma apSum_mul_left (c : ℤ) (f : ℕ → ℤ) (d n : ℕ) :
    apSum (fun k => c * f k) d n = c * apSum f d n := by
  classical
  unfold apSum
  simp [Finset.mul_sum]

/-- Multiplication by a fixed integer on the right commutes with `apSum`. -/
@[simp] lemma apSum_mul_right (f : ℕ → ℤ) (c : ℤ) (d n : ℕ) :
    apSum (fun k => f k * c) d n = apSum f d n * c := by
  classical
  unfold apSum
  simp [Finset.sum_mul]

/-- A sign sequence has AP partial sums bounded by length: `|∑_{i=1}^n f (i*d)| ≤ n`.

This is the basic triangle-inequality estimate used to show discrepancy is at most linear.
-/
lemma IsSignSequence.natAbs_apSum_le {f : ℕ → ℤ} (hf : IsSignSequence f) (d n : ℕ) :
    Int.natAbs (apSum f d n) ≤ n := by
  induction n with
  | zero =>
      simp [apSum]
  | succ n ih =>
      -- triangle inequality, plus `Int.natAbs (f _) = 1`
      calc
        Int.natAbs (apSum f d (n + 1))
            = Int.natAbs (apSum f d n + f ((n + 1) * d)) := by
                simp [apSum_succ]
        _ ≤ Int.natAbs (apSum f d n) + Int.natAbs (f ((n + 1) * d)) :=
              Int.natAbs_add_le _ _
        _ = Int.natAbs (apSum f d n) + 1 := by
              simp [IsSignSequence.natAbs_eq_one (hf := hf)]
        _ ≤ n + 1 := by
              simpa using Nat.add_le_add_right ih 1

/-- `discrepancy` is invariant under pointwise negation (as a method on `IsSignSequence`). -/
lemma IsSignSequence.discrepancy_neg {f : ℕ → ℤ} (_hf : IsSignSequence f) (d n : ℕ) :
    discrepancy (fun k => -f k) d n = discrepancy f d n := by
  simpa using (_root_.MoltResearch.discrepancy_neg (f := f) (d := d) (n := n))

/-- Normal form for discrepancy after shifting by `a*d` (as a method on `IsSignSequence`). -/
lemma IsSignSequence.discrepancy_shift_mul {f : ℕ → ℤ} (_hf : IsSignSequence f)
    (a d n : ℕ) :
    discrepancy (fun k => f (k + a * d)) d n = Int.natAbs (apSumOffset f d a n) := by
  simpa using (_root_.MoltResearch.discrepancy_shift_mul (f := f) (a := a) (d := d) (n := n))

/-- For a sign sequence, a discrepancy witness at level `C` forces a length `n > C`
(and can be chosen with step `d ≥ 1`). -/
lemma IsSignSequence.exists_witness_d_ge_one_and_length_gt {f : ℕ → ℤ} (hf : IsSignSequence f)
    {C : ℕ} (h : HasDiscrepancyAtLeast f C) :
    ∃ d n, d ≥ 1 ∧ n > C ∧ Int.natAbs (apSum f d n) > C := by
  rcases h with ⟨d, n, hd, hgt⟩
  refine ⟨d, n, Nat.succ_le_of_lt hd, ?_, hgt⟩
  have hle : Int.natAbs (apSum f d n) ≤ n :=
    IsSignSequence.natAbs_apSum_le (hf := hf) (d := d) (n := n)
  exact lt_of_lt_of_le hgt hle

lemma IsSignSequence.neg {f : ℕ → ℤ} (hf : IsSignSequence f) :
    IsSignSequence (fun n => - f n) := by
  intro n
  rcases hf n with h | h
  · right
    simp [h]
  · left
    simp [h]

lemma HasDiscrepancyAtLeast.neg_iff {f : ℕ → ℤ} {C : ℕ} :
    HasDiscrepancyAtLeast (fun n => - f n) C ↔ HasDiscrepancyAtLeast f C := by
  unfold HasDiscrepancyAtLeast
  constructor
  · rintro ⟨d, n, hd, h⟩
    refine ⟨d, n, hd, ?_⟩
    simpa [apSum_neg] using h
  · rintro ⟨d, n, hd, h⟩
    refine ⟨d, n, hd, ?_⟩
    simpa [apSum_neg] using h

lemma IsSignSequence.exists_length_gt_of_hasDiscrepancyAtLeast {f : ℕ → ℤ}
    (hf : IsSignSequence f) {C : ℕ}
    (h : HasDiscrepancyAtLeast f C) :
    ∃ d n, d > 0 ∧ n > C := by
  rcases h with ⟨d, n, hd, hn⟩
  have hle := IsSignSequence.natAbs_apSum_le (hf := hf) d n
  have hC : C < n := by
    have : C < Int.natAbs (apSum f d n) := hn
    exact lt_of_lt_of_le this hle
  exact ⟨d, n, hd, hC⟩

@[simp] lemma apSum_zero_d (f : ℕ → ℤ) (n : ℕ) : apSum f 0 n = n • f 0 := by
  classical
  -- along step size 0, the AP is constant at 0
  simp [apSum]

@[simp] lemma apSumOffset_zero_d (f : ℕ → ℤ) (m n : ℕ) :
    apSumOffset f 0 m n = n • f 0 := by
  classical
  unfold apSumOffset
  simp

end MoltResearch
