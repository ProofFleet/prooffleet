import MoltResearch.Discrepancy.TypicalFactorization

/-!
# The cost of the `𝒮`-restriction in short intervals (Track R, `[mrt]` A.1)

`[mrt]` Theorem A.1 bounds the short-interval mean value of a `1`-bounded
multiplicative function; Theorem A.2 bounds the same quantity with the sum
restricted to the typical set `𝒮`.  The plan recorded in campaign #3044 is
*"A.1 follows from A.2 plus sieve density"*, and this module is that step's
elementary half: **what it costs, in `L²`, to drop the restriction.**

The cost is a count — the number of non-typical integers met by the window —
and the whole content is that this count, summed over a sliding family of
windows, is controlled by the count over the enclosing range.  Three lemmas:

* `sum_card_window_le` — the sliding-window double count.  Each bad integer is
  met by at most `h + 1` of the windows, so the window sums cost one factor of
  the window length and nothing else.
* `card_le_mul_logavg` — the count from the log-average.  On a range with top
  end `Y`, every term of `∑ 1/n` is at least `1/Y`, so the log-average bounds
  the count after one multiplication.  This is the converter between the shape
  the density lemmas deliver (`sifted_logavg_le`,
  `typicalS_complement_logavg_le`, both log-averages) and the shape the
  restriction cost is stated in (a count).
* `sum_norm_sq_window_le_restricted` — the two composed: the unrestricted `L²`
  sum over the windows, against the restricted one plus the density cost.

Everything here is elementary and holds for an arbitrary decidable predicate;
`sum_norm_sq_window_le_typicalS` specialises to `HasFactorInAll`, which is the
`𝒮`-membership of `typicalS`.

**Why this is a leaf module.**  It belongs next to `typicalS`, but
`TypicalFactorization` is imported by `WindowTK` and `WindowAssembly`, so
editing it rebuilds the whole analytic stack.  Importing it costs nothing.
-/

namespace MoltResearch

open Finset

/-- **The sliding-window double count** (Track R, A.1, A1-1).

Summing, over windows `[x, x+h]` with `x` ranging over `[X, Y]`, the number of
integers in the window satisfying `p`, costs at most `h + 1` times the number of
such integers in the enclosing range `[X, Y+h]`.

The mechanism is that each integer `n` is met by the windows with
`n − h ≤ x ≤ n`, of which there are at most `h + 1` — so the double count is a
swap of the two sums followed by that bound, and the factor `h + 1` is the
window length rather than anything about `p`. -/
theorem sum_card_window_le (p : ℕ → Prop) [DecidablePred p] (X Y h : ℕ) :
    ∑ x ∈ Finset.Icc X Y, ((Finset.Icc x (x + h)).filter p).card
      ≤ (h + 1) * ((Finset.Icc X (Y + h)).filter p).card := by
  classical
  -- Write each window count as a sum of indicators over the enclosing range.
  have hstep : ∀ x ∈ Finset.Icc X Y,
      ((Finset.Icc x (x + h)).filter p).card
        = ∑ n ∈ Finset.Icc X (Y + h),
            if p n ∧ x ≤ n ∧ n ≤ x + h then 1 else 0 := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.card_filter]
    rw [← Finset.sum_subset (s₁ := Finset.Icc x (x + h))
      (s₂ := Finset.Icc X (Y + h)) ?_ ?_]
    · exact Finset.sum_congr rfl fun n hn => by
        rw [Finset.mem_Icc] at hn
        simp [hn.1, hn.2]
    · intro n hn
      rw [Finset.mem_Icc] at hn ⊢
      omega
    · intro n _ hn
      rw [Finset.mem_Icc] at hn
      have : ¬ (x ≤ n ∧ n ≤ x + h) := fun hc => hn hc
      simp [this]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  -- Each integer is met by at most `h + 1` windows.
  have hinner : ∀ n ∈ Finset.Icc X (Y + h),
      (∑ x ∈ Finset.Icc X Y, if p n ∧ x ≤ n ∧ n ≤ x + h then 1 else 0)
        ≤ (h + 1) * (if p n then 1 else 0) := by
    intro n _
    by_cases hp : p n
    · simp only [hp, true_and, mul_one, if_pos]
      calc (∑ x ∈ Finset.Icc X Y, if x ≤ n ∧ n ≤ x + h then 1 else 0)
          ≤ ∑ x ∈ Finset.Icc X Y, if x ∈ Finset.Icc (n - h) n then 1 else 0 := by
            refine Finset.sum_le_sum fun x _ => ?_
            by_cases hc : x ≤ n ∧ n ≤ x + h
            · have : x ∈ Finset.Icc (n - h) n := by
                rw [Finset.mem_Icc]; omega
              simp [hc, this]
            · simp [hc]
        _ = ((Finset.Icc X Y).filter
              (fun x => x ∈ Finset.Icc (n - h) n)).card :=
            (Finset.card_filter _ _).symm
        _ ≤ (Finset.Icc (n - h) n).card :=
            Finset.card_le_card fun x hx => (Finset.mem_filter.mp hx).2
        _ ≤ h + 1 := by rw [Nat.card_Icc]; omega
    · simp [hp]
  calc (∑ n ∈ Finset.Icc X (Y + h),
        ∑ x ∈ Finset.Icc X Y, if p n ∧ x ≤ n ∧ n ≤ x + h then 1 else 0)
      ≤ ∑ n ∈ Finset.Icc X (Y + h), (h + 1) * (if p n then 1 else 0) :=
        Finset.sum_le_sum hinner
    _ = (h + 1) * ((Finset.Icc X (Y + h)).filter p).card := by
        rw [← Finset.mul_sum, Finset.card_filter]

/-- **The count, from the log-average** (Track R, A.1, A1-1).

On a range whose top end is `Y`, every term `1/n` of the log-average is at least
`1/Y`, so the count is at most `Y` times the log-average.

This is the converter the A.1 step needs.  The density results in the tree —
`sifted_logavg_le` and `typicalS_complement_logavg_le` — both deliver
**log-averages** `∑ 1/n`, because that is the shape Turán–Kubilius produces; the
restriction cost is a **count**.  On a dyadic block `[X, 2X]` the conversion
loses nothing of substance, since `Y ≍ X` and the log-average of the whole block
is `≍ 1`. -/
theorem card_le_mul_logavg (p : ℕ → Prop) [DecidablePred p] (X Y : ℕ)
    (hX : 1 ≤ X) :
    (((Finset.Icc X Y).filter p).card : ℝ)
      ≤ (Y : ℝ) * ∑ n ∈ (Finset.Icc X Y).filter p, (1 : ℝ) / (n : ℝ) := by
  classical
  rcases Nat.eq_zero_or_pos ((Finset.Icc X Y).filter p).card with hc | hc
  · have hY : (0 : ℝ) ≤ (Y : ℝ) := Nat.cast_nonneg _
    have : ∑ n ∈ (Finset.Icc X Y).filter p, (1 : ℝ) / (n : ℝ) = 0 := by
      rw [Finset.card_eq_zero.mp hc, Finset.sum_empty]
    rw [hc, this]
    simp
  · have hne : ((Finset.Icc X Y).filter p).Nonempty :=
      Finset.card_pos.mp hc
    obtain ⟨m, hm⟩ := hne
    have hYpos : 0 < Y := by
      rw [Finset.mem_filter, Finset.mem_Icc] at hm; omega
    have hY : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hYpos
    rw [← div_le_iff₀' hY]
    have hterm : ∀ n ∈ (Finset.Icc X Y).filter p,
        (1 : ℝ) / (Y : ℝ) ≤ (1 : ℝ) / (n : ℝ) := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_trans hX hn.1.1)
      have hnY : (n : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hn.1.2
      exact one_div_le_one_div_of_le (by linarith) hnY
    calc ((((Finset.Icc X Y).filter p).card : ℝ)) / (Y : ℝ)
        = ∑ _n ∈ (Finset.Icc X Y).filter p, (1 : ℝ) / (Y : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ n ∈ (Finset.Icc X Y).filter p, (1 : ℝ) / (n : ℝ) :=
          Finset.sum_le_sum hterm

/-- **The `L²` cost of dropping the `𝒮`-restriction** (Track R, A.1, A1-1).

The unrestricted short-interval `L²` sum, against the restricted one plus a
density term.  This is the elementary half of `[mrt]`'s *"A.1 follows from A.2
plus sieve density"*: A.2 bounds the first summand on the right, and the second
is what the restriction costs.

**Both factors of `h + 1` are honest and they arise differently.**  One is the
squaring: the error sum over a window is at most the number of bad integers in
that window, and a count in a window of length `h + 1` is at most `h + 1`, so
`(count)² ≤ (h+1)·count`.  The other is the sliding-window double count
(`sum_card_window_le`): each bad integer is met by at most `h + 1` of the
windows.  Neither can be removed, and together they are exactly the `1/h²`
normalisation that `[mrt]` A.1 carries on the left-hand side.

The factor `2` is the `L²` triangle inequality, and it is the usual price for
splitting a sum whose two halves are anchored differently — here, one supported
on `𝒮` and one on its complement, with no orthogonality between them. -/
theorem sum_norm_sq_window_le_restricted (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (p : ℕ → Prop) [DecidablePred p] (X Y h : ℕ) :
    ∑ x ∈ Finset.Icc X Y, ‖∑ n ∈ Finset.Icc x (x + h), f n‖ ^ 2
      ≤ 2 * ∑ x ∈ Finset.Icc X Y,
            ‖∑ n ∈ (Finset.Icc x (x + h)).filter p, f n‖ ^ 2
        + 2 * ((h : ℝ) + 1)
            * ∑ x ∈ Finset.Icc X Y,
                (((Finset.Icc x (x + h)).filter (fun n => ¬ p n)).card : ℝ) := by
  classical
  have hbad : ∀ x : ℕ,
      ‖∑ n ∈ (Finset.Icc x (x + h)).filter (fun n => ¬ p n), f n‖
        ≤ (((Finset.Icc x (x + h)).filter (fun n => ¬ p n)).card : ℝ) := by
    intro x
    calc ‖∑ n ∈ (Finset.Icc x (x + h)).filter (fun n => ¬ p n), f n‖
        ≤ ∑ n ∈ (Finset.Icc x (x + h)).filter (fun n => ¬ p n), ‖f n‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _n ∈ (Finset.Icc x (x + h)).filter (fun n => ¬ p n), (1 : ℝ) :=
          Finset.sum_le_sum fun n _ => hf n
      _ = _ := by simp
  have hcard : ∀ x : ℕ,
      (((Finset.Icc x (x + h)).filter (fun n => ¬ p n)).card : ℝ) ≤ (h : ℝ) + 1 := by
    intro x
    have := Finset.card_le_card
      (Finset.filter_subset (fun n => ¬ p n) (Finset.Icc x (x + h)))
    rw [Nat.card_Icc] at this
    have h' : ((Finset.Icc x (x + h)).filter (fun n => ¬ p n)).card ≤ h + 1 := by omega
    exact_mod_cast h'
  have hterm : ∀ x ∈ Finset.Icc X Y,
      ‖∑ n ∈ Finset.Icc x (x + h), f n‖ ^ 2
        ≤ 2 * ‖∑ n ∈ (Finset.Icc x (x + h)).filter p, f n‖ ^ 2
          + 2 * ((h : ℝ) + 1)
            * (((Finset.Icc x (x + h)).filter (fun n => ¬ p n)).card : ℝ) := by
    intro x _
    have hsplit : ∑ n ∈ Finset.Icc x (x + h), f n
        = (∑ n ∈ (Finset.Icc x (x + h)).filter p, f n)
          + ∑ n ∈ (Finset.Icc x (x + h)).filter (fun n => ¬ p n), f n :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have htri : ‖∑ n ∈ Finset.Icc x (x + h), f n‖ ^ 2
        ≤ 2 * ‖∑ n ∈ (Finset.Icc x (x + h)).filter p, f n‖ ^ 2
          + 2 * ‖∑ n ∈ (Finset.Icc x (x + h)).filter (fun n => ¬ p n), f n‖ ^ 2 := by
      rw [hsplit]
      have htr := norm_add_le (∑ n ∈ (Finset.Icc x (x + h)).filter p, f n)
        (∑ n ∈ (Finset.Icc x (x + h)).filter (fun n => ¬ p n), f n)
      have hsq2 : ‖(∑ n ∈ (Finset.Icc x (x + h)).filter p, f n)
            + ∑ n ∈ (Finset.Icc x (x + h)).filter (fun n => ¬ p n), f n‖ ^ 2
          ≤ (‖∑ n ∈ (Finset.Icc x (x + h)).filter p, f n‖
              + ‖∑ n ∈ (Finset.Icc x (x + h)).filter (fun n => ¬ p n), f n‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htr 2
      nlinarith [hsq2, sq_nonneg (‖∑ n ∈ (Finset.Icc x (x + h)).filter p, f n‖
          - ‖∑ n ∈ (Finset.Icc x (x + h)).filter (fun n => ¬ p n), f n‖)]
    have hsq : ‖∑ n ∈ (Finset.Icc x (x + h)).filter (fun n => ¬ p n), f n‖ ^ 2
        ≤ ((h : ℝ) + 1)
          * (((Finset.Icc x (x + h)).filter (fun n => ¬ p n)).card : ℝ) := by
      have h0 : (0 : ℝ) ≤ ‖∑ n ∈ (Finset.Icc x (x + h)).filter (fun n => ¬ p n), f n‖ :=
        norm_nonneg _
      nlinarith [hbad x, hcard x, Nat.cast_nonneg (α := ℝ)
        (((Finset.Icc x (x + h)).filter (fun n => ¬ p n)).card)]
    linarith
  calc ∑ x ∈ Finset.Icc X Y, ‖∑ n ∈ Finset.Icc x (x + h), f n‖ ^ 2
      ≤ ∑ x ∈ Finset.Icc X Y,
          (2 * ‖∑ n ∈ (Finset.Icc x (x + h)).filter p, f n‖ ^ 2
            + 2 * ((h : ℝ) + 1)
              * (((Finset.Icc x (x + h)).filter (fun n => ¬ p n)).card : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- **The restriction cost, priced by the complement's log-average** (Track R,
A.1, A1-1).

`sum_norm_sq_window_le_restricted` with both counting lemmas substituted: the
sliding-window double count turns the per-window counts into one count over the
enclosing range, and `card_le_mul_logavg` turns that count into the log-average
that `typicalS_complement_logavg_le` actually delivers.

The result is the A.2 → A.1 step in the exact shape the two halves supply it:
`[mrt]` A.2 bounds the restricted sum, `typicalS_complement_logavg_le` bounds
`D`, and nothing else is needed. -/
theorem sum_norm_sq_window_le_restricted_logavg (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (p : ℕ → Prop) [DecidablePred p] (X Y h : ℕ) (hX : 1 ≤ X) (D : ℝ)
    (hD : ∑ n ∈ (Finset.Icc X (Y + h)).filter (fun n => ¬ p n), (1 : ℝ) / (n : ℝ)
      ≤ D) :
    ∑ x ∈ Finset.Icc X Y, ‖∑ n ∈ Finset.Icc x (x + h), f n‖ ^ 2
      ≤ 2 * ∑ x ∈ Finset.Icc X Y,
            ‖∑ n ∈ (Finset.Icc x (x + h)).filter p, f n‖ ^ 2
        + 2 * ((h : ℝ) + 1) ^ 2 * ((Y : ℝ) + (h : ℝ)) * D := by
  classical
  have hh0 : (0 : ℝ) ≤ (h : ℝ) + 1 := by positivity
  -- the sliding-window double count
  have hslide := sum_card_window_le (fun n => ¬ p n) X Y h
  have hslideR : ∑ x ∈ Finset.Icc X Y,
        (((Finset.Icc x (x + h)).filter (fun n => ¬ p n)).card : ℝ)
      ≤ ((h : ℝ) + 1)
        * (((Finset.Icc X (Y + h)).filter (fun n => ¬ p n)).card : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hslide
    push_cast at this
    simpa using this
  -- the count from the log-average
  have hcount := card_le_mul_logavg (fun n => ¬ p n) X (Y + h) hX
  have hcountR : ((((Finset.Icc X (Y + h)).filter (fun n => ¬ p n)).card : ℝ))
      ≤ ((Y : ℝ) + (h : ℝ)) * D := by
    refine hcount.trans ?_
    have hYh : (((Y + h : ℕ)) : ℝ) = (Y : ℝ) + (h : ℝ) := by push_cast; ring
    rw [hYh]
    exact mul_le_mul_of_nonneg_left hD (by positivity)
  have hmain := sum_norm_sq_window_le_restricted f hf p X Y h
  have hchain : ∑ x ∈ Finset.Icc X Y,
        (((Finset.Icc x (x + h)).filter (fun n => ¬ p n)).card : ℝ)
      ≤ ((h : ℝ) + 1) * (((Y : ℝ) + (h : ℝ)) * D) :=
    hslideR.trans (mul_le_mul_of_nonneg_left hcountR hh0)
  nlinarith [hmain, hchain, hh0]


end MoltResearch
