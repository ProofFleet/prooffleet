import MoltResearch.Discrepancy.SpectralWindowBound

/-!
# Source budgets for the finite Fourier reduction

This file audits the only use of the global discrepancy hypothesis in
`spectral_window_bound`.  At a wrap-free frequency-group point `a`, the proof asks for the
single homogeneous progression with dilation `dExp X a` and length `n`.  The exact largest
product `d * n` over those points is `spectralSourceBudget X M n`.

The localized spectral theorem at the end consequently assumes discrepancy only for
progressions inside that finite source budget.  See `Problems/edp_rate_source_budget.md`.
-/

namespace MoltResearch

open Finset

/-- The largest dilation encoded by a wrap-free point of the exponent group, provided
`Nat.log 2 X < M`.  Every coordinate can then have exponent at most
`M - (Nat.log 2 X + 1)`, and this bound is attained simultaneously. -/
def spectralDilationBudget (X M : ℕ) : ℕ :=
  ∏ p ∈ (X + 1).primesBelow.attach, p.1 ^ (M - (Nat.log 2 X + 1))

/-- The exact largest source product `d * n` requested by the good-point part of the
spectral window proof. -/
def spectralSourceBudget (X M n : ℕ) : ℕ :=
  spectralDilationBudget X M * n

/-- Every wrap-free encoded dilation is bounded by `spectralDilationBudget`. -/
theorem dExp_le_spectralDilationBudget {X M : ℕ}
    (a : PrimeIdx X → ZMod M) (ha : WrapFree X M a) :
    dExp X a ≤ spectralDilationBudget X M := by
  unfold dExp spectralDilationBudget
  refine Finset.prod_le_prod' fun p _ => ?_
  apply Nat.pow_le_pow_right (Nat.prime_of_mem_primesBelow p.2).pos
  have hp := ha p
  omega

/-- Every progression queried at a wrap-free point fits in `spectralSourceBudget`. -/
theorem dExp_mul_le_spectralSourceBudget {X M n : ℕ}
    (a : PrimeIdx X → ZMod M) (ha : WrapFree X M a) :
    dExp X a * n ≤ spectralSourceBudget X M n := by
  unfold spectralSourceBudget
  exact Nat.mul_le_mul_right n (dExp_le_spectralDilationBudget a ha)

/-- The point at which every prime exponent is as large as wrap-freeness permits. -/
def spectralMaxWrapFreePoint (X M : ℕ) : PrimeIdx X → ZMod M :=
  fun _ => (M - (Nat.log 2 X + 1) : ℕ)

/-- The coordinatewise maximal point is wrap-free whenever the wrap-free set can be
nonempty. -/
theorem spectralMaxWrapFreePoint_wrapFree {X M : ℕ} [NeZero M]
    (hXM : Nat.log 2 X < M) :
    WrapFree X M (spectralMaxWrapFreePoint X M) := by
  intro p
  have he : M - (Nat.log 2 X + 1) < M := by omega
  rw [spectralMaxWrapFreePoint, ZMod.val_natCast_of_lt he]
  omega

/-- The coordinatewise maximal point attains `spectralDilationBudget`. -/
theorem dExp_spectralMaxWrapFreePoint {X M : ℕ} [NeZero M]
    (hXM : Nat.log 2 X < M) :
    dExp X (spectralMaxWrapFreePoint X M) = spectralDilationBudget X M := by
  have he : M - (Nat.log 2 X + 1) < M := by omega
  unfold dExp spectralDilationBudget spectralMaxWrapFreePoint
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [ZMod.val_natCast_of_lt he]

/-- `spectralSourceBudget` is not merely an upper bound: when `Nat.log 2 X < M`, it is
the greatest product `dExp X a * n` among all wrap-free group points. -/
theorem spectralSourceBudget_isGreatest {X M n : ℕ} [NeZero M]
    (hXM : Nat.log 2 X < M) :
    IsGreatest
      {q : ℕ | ∃ a : PrimeIdx X → ZMod M,
        WrapFree X M a ∧ q = dExp X a * n}
      (spectralSourceBudget X M n) := by
  constructor
  · refine ⟨spectralMaxWrapFreePoint X M,
      spectralMaxWrapFreePoint_wrapFree hXM, ?_⟩
    rw [dExp_spectralMaxWrapFreePoint hXM]
    rfl
  · rintro q ⟨a, ha, rfl⟩
    exact dExp_mul_le_spectralSourceBudget a ha

/-- A wrap-free window needs only the discrepancy bound at its one audited source
progression, rather than a bound on every homogeneous progression. -/
theorem norm_window_smoothEval_le_of_sourceBudget
    {f : ℕ → ℤ} {B X M n : ℕ} [NeZero M]
    (hB : ∀ d m : ℕ, d > 0 →
      d * m ≤ spectralSourceBudget X M n → (apSum f d m).natAbs ≤ B)
    (hnX : n ≤ X) {a : PrimeIdx X → ZMod M} (ha : WrapFree X M a) :
    ‖∑ j ∈ Finset.Icc 1 n, smoothEval f X (a + piExp X M j)‖ ≤ (B : ℝ) := by
  rw [window_smoothEval_eq_apSum hnX ha, Complex.norm_intCast, ← Int.cast_abs]
  have h2 : |apSum f (dExp X a) n| ≤ (B : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hB (dExp X a) n (dExp_pos a)
      (dExp_mul_le_spectralSourceBudget a ha)
  exact_mod_cast h2

/-- Source-localized form of `avg_normSq_window_smoothEval_le`.  The bad points use only
the sign-sequence bound; every good point is discharged by the audited finite budget. -/
theorem avg_normSq_window_smoothEval_le_of_sourceBudget
    {f : ℕ → ℤ} (hs : IsSignSequence f) {B X M n : ℕ} [NeZero M]
    (hB : ∀ d m : ℕ, d > 0 →
      d * m ≤ spectralSourceBudget X M n → (apSum f d m).natAbs ≤ B)
    (hnX : n ≤ X)
    (hM : Fintype.card (PrimeIdx X) * Nat.log 2 X * X ^ 2 ≤ M) :
    (1 / ((M : ℝ)) ^ Fintype.card (PrimeIdx X))
        * ∑ a : PrimeIdx X → ZMod M,
            ‖∑ j ∈ Finset.Icc 1 n, smoothEval f X (a + piExp X M j)‖ ^ 2
      ≤ (B : ℝ) ^ 2 + 1 := by
  classical
  have hM0 : (0 : ℝ) < (M : ℝ) := by
    have := NeZero.ne M
    exact_mod_cast Nat.pos_of_ne_zero this
  have hMr0 : (0 : ℝ) < ((M : ℝ)) ^ Fintype.card (PrimeIdx X) := by positivity
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (PrimeIdx X → ZMod M)) (fun a => WrapFree X M a)]
  have hgood : ∑ a ∈ (Finset.univ : Finset (PrimeIdx X → ZMod M)).filter
      (fun a => WrapFree X M a),
      ‖∑ j ∈ Finset.Icc 1 n, smoothEval f X (a + piExp X M j)‖ ^ 2
        ≤ (((M : ℝ)) ^ Fintype.card (PrimeIdx X)) * (B : ℝ) ^ 2 := by
    have hcardg : (((Finset.univ : Finset (PrimeIdx X → ZMod M)).filter
        (fun a => WrapFree X M a)).card : ℝ)
          ≤ ((M : ℝ)) ^ Fintype.card (PrimeIdx X) := by
      have h1 : ((Finset.univ : Finset (PrimeIdx X → ZMod M)).filter
          (fun a => WrapFree X M a)).card ≤ Fintype.card (PrimeIdx X → ZMod M) :=
        le_trans (Finset.card_filter_le _ _) (Finset.card_univ).le
      have h2 : Fintype.card (PrimeIdx X → ZMod M)
          = M ^ Fintype.card (PrimeIdx X) := by
        rw [Fintype.card_fun, ZMod.card]
      rw [h2] at h1
      calc (((Finset.univ : Finset (PrimeIdx X → ZMod M)).filter
          (fun a => WrapFree X M a)).card : ℝ)
          ≤ ((M ^ Fintype.card (PrimeIdx X) : ℕ) : ℝ) := by exact_mod_cast h1
        _ = ((M : ℝ)) ^ Fintype.card (PrimeIdx X) := by push_cast; ring
    have hstep : ∑ a ∈ (Finset.univ : Finset (PrimeIdx X → ZMod M)).filter
        (fun a => WrapFree X M a),
        ‖∑ j ∈ Finset.Icc 1 n, smoothEval f X (a + piExp X M j)‖ ^ 2
        ≤ ((Finset.univ : Finset (PrimeIdx X → ZMod M)).filter
            (fun a => WrapFree X M a)).card • ((B : ℝ) ^ 2) := by
      refine Finset.sum_le_card_nsmul _ _ _ fun a ha => ?_
      have haw : WrapFree X M a := (Finset.mem_filter.mp ha).2
      have hnorm := norm_window_smoothEval_le_of_sourceBudget hB hnX haw
      have h0 : (0 : ℝ) ≤ ‖∑ j ∈ Finset.Icc 1 n,
          smoothEval f X (a + piExp X M j)‖ := norm_nonneg _
      nlinarith
    rw [nsmul_eq_mul] at hstep
    refine le_trans hstep ?_
    exact mul_le_mul_of_nonneg_right hcardg (by positivity)
  have hbad : ∑ a ∈ (Finset.univ : Finset (PrimeIdx X → ZMod M)).filter
      (fun a => ¬ WrapFree X M a),
      ‖∑ j ∈ Finset.Icc 1 n, smoothEval f X (a + piExp X M j)‖ ^ 2
        ≤ ((Fintype.card (PrimeIdx X) * Nat.log 2 X
            * M ^ (Fintype.card (PrimeIdx X) - 1) : ℕ) : ℝ) * (X : ℝ) ^ 2 := by
    have hstep : ∑ a ∈ (Finset.univ : Finset (PrimeIdx X → ZMod M)).filter
        (fun a => ¬ WrapFree X M a),
        ‖∑ j ∈ Finset.Icc 1 n, smoothEval f X (a + piExp X M j)‖ ^ 2
        ≤ ((Finset.univ : Finset (PrimeIdx X → ZMod M)).filter
            (fun a => ¬ WrapFree X M a)).card • ((X : ℝ) ^ 2) := by
      refine Finset.sum_le_card_nsmul _ _ _ fun a _ => ?_
      have hnorm := norm_window_smoothEval_le (M := M) hs n a
      have hnX' : (n : ℝ) ≤ (X : ℝ) := by exact_mod_cast hnX
      have h0 : (0 : ℝ) ≤ ‖∑ j ∈ Finset.Icc 1 n,
          smoothEval f X (a + piExp X M j)‖ := norm_nonneg _
      nlinarith
    rw [nsmul_eq_mul] at hstep
    refine le_trans hstep ?_
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact_mod_cast card_not_wrapFree_le (X := X) (M := M)
  rcases Nat.eq_zero_or_pos (Fintype.card (PrimeIdx X)) with hr | hr
  · have hbad0 : ((Fintype.card (PrimeIdx X) * Nat.log 2 X
        * M ^ (Fintype.card (PrimeIdx X) - 1) : ℕ) : ℝ) = 0 := by
      rw [hr]
      push_cast
      ring
    rw [hbad0, zero_mul] at hbad
    have hbad' : ∑ a ∈ (Finset.univ : Finset (PrimeIdx X → ZMod M)).filter
        (fun a => ¬ WrapFree X M a),
        ‖∑ j ∈ Finset.Icc 1 n,
          smoothEval f X (a + piExp X M j)‖ ^ 2 ≤ 0 := hbad
    have hsum_nonneg : (0 : ℝ) ≤
        ∑ a ∈ (Finset.univ : Finset (PrimeIdx X → ZMod M)).filter
          (fun a => ¬ WrapFree X M a),
          ‖∑ j ∈ Finset.Icc 1 n,
            smoothEval f X (a + piExp X M j)‖ ^ 2 :=
      Finset.sum_nonneg fun a _ => by positivity
    have hkey : (1 / ((M : ℝ)) ^ Fintype.card (PrimeIdx X))
        * ((((M : ℝ)) ^ Fintype.card (PrimeIdx X)) * (B : ℝ) ^ 2 + 0)
          = (B : ℝ) ^ 2 := by
      field_simp
      ring
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hgood hbad')
      (le_of_lt (by positivity : (0 : ℝ) <
        1 / ((M : ℝ)) ^ Fintype.card (PrimeIdx X)))]
  · have hMsplit : ((M : ℝ)) ^ Fintype.card (PrimeIdx X)
        = (M : ℝ) * ((M : ℝ)) ^ (Fintype.card (PrimeIdx X) - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hbadR : ((Fintype.card (PrimeIdx X) * Nat.log 2 X
        * M ^ (Fintype.card (PrimeIdx X) - 1) : ℕ) : ℝ) * (X : ℝ) ^ 2
          ≤ ((M : ℝ)) ^ Fintype.card (PrimeIdx X) := by
      have hMR : ((Fintype.card (PrimeIdx X) * Nat.log 2 X * X ^ 2 : ℕ) : ℝ)
          ≤ (M : ℝ) := by exact_mod_cast hM
      have hMr1 : (0 : ℝ) ≤ ((M : ℝ)) ^ (Fintype.card (PrimeIdx X) - 1) := by
        positivity
      calc ((Fintype.card (PrimeIdx X) * Nat.log 2 X
            * M ^ (Fintype.card (PrimeIdx X) - 1) : ℕ) : ℝ) * (X : ℝ) ^ 2
          = ((Fintype.card (PrimeIdx X) * Nat.log 2 X * X ^ 2 : ℕ) : ℝ)
            * ((M : ℝ)) ^ (Fintype.card (PrimeIdx X) - 1) := by
            push_cast
            ring
        _ ≤ (M : ℝ) * ((M : ℝ)) ^ (Fintype.card (PrimeIdx X) - 1) :=
            mul_le_mul_of_nonneg_right hMR hMr1
        _ = ((M : ℝ)) ^ Fintype.card (PrimeIdx X) := hMsplit.symm
    have htotal := add_le_add hgood (le_trans hbad hbadR)
    have hdiv := mul_le_mul_of_nonneg_left htotal
      (le_of_lt (by positivity : (0 : ℝ) <
        1 / ((M : ℝ)) ^ Fintype.card (PrimeIdx X)))
    have hfinal : (1 / ((M : ℝ)) ^ Fintype.card (PrimeIdx X))
        * ((((M : ℝ)) ^ Fintype.card (PrimeIdx X)) * (B : ℝ) ^ 2
          + ((M : ℝ)) ^ Fintype.card (PrimeIdx X))
          = (B : ℝ) ^ 2 + 1 := by
      field_simp
    calc (1 / ((M : ℝ)) ^ Fintype.card (PrimeIdx X))
        * (∑ a ∈ (Finset.univ : Finset (PrimeIdx X → ZMod M)).filter
            (fun a => WrapFree X M a),
            ‖∑ j ∈ Finset.Icc 1 n,
              smoothEval f X (a + piExp X M j)‖ ^ 2
          + ∑ a ∈ (Finset.univ : Finset (PrimeIdx X → ZMod M)).filter
              (fun a => ¬ WrapFree X M a),
              ‖∑ j ∈ Finset.Icc 1 n,
                smoothEval f X (a + piExp X M j)‖ ^ 2)
        ≤ (1 / ((M : ℝ)) ^ Fintype.card (PrimeIdx X))
          * ((((M : ℝ)) ^ Fintype.card (PrimeIdx X)) * (B : ℝ) ^ 2
            + ((M : ℝ)) ^ Fintype.card (PrimeIdx X)) := hdiv
      _ = (B : ℝ) ^ 2 + 1 := hfinal

/-- Source-budgeted form of `spectral_window_bound`.  It has the same conclusion and
modulus condition, but its discrepancy premise is restricted to the finite source budget
that covers every progression the proof actually invokes. -/
theorem spectral_window_bound_of_sourceBudget
    {f : ℕ → ℤ} (hs : IsSignSequence f) {B X M n : ℕ} [NeZero M]
    (hB : ∀ d m : ℕ, d > 0 →
      d * m ≤ spectralSourceBudget X M n → (apSum f d m).natAbs ≤ B)
    (hnX : n ≤ X)
    (hM : Fintype.card (PrimeIdx X) * Nat.log 2 X * X ^ 2 ≤ M) :
    ∑ ξ : PrimeIdx X → ZMod M,
        ‖prodDFT (smoothEval f X) ξ‖ ^ 2
          * ‖∑ j ∈ Finset.Icc 1 n, prodChar (piExp X M j) ξ‖ ^ 2
      ≤ (B : ℝ) ^ 2 + 1 := by
  rw [← avg_normSq_shift_sum_eq (Finset.Icc 1 n) (piExp X M) (smoothEval f X)]
  exact avg_normSq_window_smoothEval_le_of_sourceBudget hs hB hnX hM

end MoltResearch
