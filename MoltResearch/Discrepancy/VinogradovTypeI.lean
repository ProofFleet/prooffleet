import MoltResearch.Discrepancy.ExpSums

/-!
# Track R, phase R4v: the linear-phase exponential sum (V1)

The geometric-series bound for the linear phase: away from the integers,
`‖∑_{M ≤ n ≤ N} e(nβ)‖ ≤ 1/‖β‖`, with `‖β‖ = nint β` the distance from
`β` to the nearest integer.  This is `kusmin_landau` at the constant
increment `β − round β`, after the integer part is discarded by
periodicity — the first brick of the Type I/II estimates behind the
Vinogradov classification (`PrimeBlockMajorArcAssumption`).
-/

namespace MoltResearch

namespace ExpSums

open Finset

/-- Periodicity at integer multiples: `e(nβ) = e(n(β − round β))`. -/
theorem e_nat_mul_sub_round (β : ℝ) (n : ℕ) :
    e ((n : ℝ) * β) = e ((n : ℝ) * (β - (round β : ℝ))) := by
  have h : (n : ℝ) * β
      = (n : ℝ) * (β - (round β : ℝ)) + ((n * round β : ℤ) : ℝ) := by
    push_cast
    ring
  rw [h, e_add, e_intCast, mul_one]

/-- **The linear-phase Kusmin–Landau bound** (Track R, V1): for `β` at
distance `nint β > 0` from the integers,
`‖∑_{n ∈ Ico M (N+1)} e(nβ)‖ ≤ 1/nint β`. -/
theorem norm_sum_e_linear_le {β : ℝ} (hβ : 0 < nint β) (M N : ℕ)
    (hMN : M ≤ N) :
    ‖∑ n ∈ Finset.Ico M (N + 1), e ((n : ℝ) * β)‖ ≤ 1 / nint β := by
  have hper : ∑ n ∈ Finset.Ico M (N + 1), e ((n : ℝ) * β)
      = ∑ n ∈ Finset.Ico M (N + 1),
          e ((n : ℝ) * (β - (round β : ℝ))) := by
    exact Finset.sum_congr rfl fun n _ => e_nat_mul_sub_round β n
  rw [hper]
  set γ : ℝ := β - (round β : ℝ) with hγ_def
  have hγ_abs : nint β = |γ| := rfl
  have hγ_half : |γ| ≤ 1 / 2 := by
    rw [← hγ_abs]
    exact nint_le_half β
  have hγ_ne : γ ≠ 0 := by
    intro hc
    rw [hγ_abs, hc, abs_zero] at hβ
    exact lt_irrefl 0 hβ
  rcases lt_or_gt_of_ne hγ_ne with hneg | hpos
  · -- negative increment: conjugate and apply the positive case
    have hconj : ‖∑ n ∈ Finset.Ico M (N + 1), e ((n : ℝ) * γ)‖
        = ‖∑ n ∈ Finset.Ico M (N + 1), e ((n : ℝ) * (-γ))‖ := by
      rw [← RCLike.norm_conj (∑ n ∈ Finset.Ico M (N + 1), e ((n : ℝ) * γ)),
        map_sum]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [e_conj]
      ring_nf
    rw [hconj]
    have h1 : 0 < -γ := by linarith
    have h2 : -γ ≤ 1 - -γ := by
      have : -γ ≤ 1/2 := by
        rw [abs_of_neg hneg] at hγ_half
        linarith
      linarith
    have hkl := kusmin_landau (φ := fun n => (n : ℝ) * (-γ)) (θ := -γ)
      h1 hMN
      (fun n _ _ => by push_cast; ring_nf; linarith)
      (fun n _ _ => by push_cast; ring_nf; linarith [h2])
      (fun n _ _ => by push_cast; ring_nf; linarith)
    refine le_trans hkl ?_
    rw [hγ_abs, abs_of_neg hneg]
  · -- positive increment: apply Kusmin–Landau directly
    have h2 : γ ≤ 1 - γ := by
      have : γ ≤ 1/2 := by
        rw [abs_of_pos hpos] at hγ_half
        linarith
      linarith
    have hkl := kusmin_landau (φ := fun n => (n : ℝ) * γ) (θ := γ)
      hpos hMN
      (fun n _ _ => by push_cast; ring_nf; linarith)
      (fun n _ _ => by push_cast; ring_nf; linarith [h2])
      (fun n _ _ => by push_cast; ring_nf; linarith)
    refine le_trans hkl ?_
    rw [hγ_abs, abs_of_pos hpos]

/-- The trivial companion: the linear sum is at most its length. -/
theorem norm_sum_e_linear_le_card (β : ℝ) (s : Finset ℕ) :
    ‖∑ n ∈ s, e ((n : ℝ) * β)‖ ≤ (s.card : ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  have h : ∀ n ∈ s, ‖e ((n : ℝ) * β)‖ = 1 := fun n _ => norm_e _
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul, mul_one]


/-- `nint` is invariant under integer shifts. -/
theorem nint_add_intCast (x : ℝ) (m : ℤ) : nint (x + m) = nint x := by
  rw [nint, nint, round_add_intCast]
  push_cast
  ring_nf

/-- `nint` is invariant under natural shifts. -/
theorem nint_add_natCast (x : ℝ) (m : ℕ) : nint (x + m) = nint x := by
  have h := nint_add_intCast x (m : ℤ)
  push_cast at h
  exact h

/-- **Nearest-integer minimality**: `nint x` is at most the distance from
`x` to any integer. -/
theorem nint_le_abs_sub_intCast (x : ℝ) (m : ℤ) : nint x ≤ |x - m| := by
  rcases le_or_gt (1/2 : ℝ) |x - m| with h | h
  · exact le_trans (nint_le_half x) h
  · have hm : round x = m := by
      rw [round_eq]
      have h1 : x - m < 1/2 := lt_of_abs_lt h
      have h2 : -(1/2) < x - m := neg_lt_of_abs_lt h
      have h3 : (m : ℝ) ≤ x + 1/2 := by linarith
      have h4 : x + 1/2 < (m : ℝ) + 1 := by linarith
      have := Int.floor_eq_iff.mpr ⟨h3, by push_cast; linarith⟩
      exact this
    rw [nint, hm]

/-- **`nint` is 1-Lipschitz**: `nint x ≤ nint y + |x − y|`. -/
theorem nint_le_nint_add_abs (x y : ℝ) :
    nint x ≤ nint y + |x - y| := by
  have h1 := nint_le_abs_sub_intCast x (round y)
  have h2 : |x - (round y : ℝ)| ≤ |y - (round y : ℝ)| + |x - y| := by
    have := abs_sub_abs_le_abs_sub (x - (round y : ℝ)) (y - (round y : ℝ))
    calc |x - (round y : ℝ)|
        = |(y - (round y : ℝ)) + (x - y)| := by ring_nf
      _ ≤ |y - (round y : ℝ)| + |x - y| := abs_add_le _ _
  calc nint x ≤ |x - (round y : ℝ)| := h1
    _ ≤ |y - (round y : ℝ)| + |x - y| := h2
    _ = nint y + |x - y| := by rw [nint]


/-- **Real-interval lattice count**: at most `B − A + 1` naturals below `q`
lie strictly between the reals `A` and `B`. -/
theorem card_range_filter_Ioo_le (q : ℕ) {A B : ℝ} (hAB : A ≤ B) :
    (((Finset.range q).filter
        (fun k : ℕ => A < (k:ℝ) ∧ (k:ℝ) < B)).card : ℝ) ≤ B - A + 1 := by
  classical
  have hsub : ((Finset.range q).filter (fun k : ℕ => A < (k:ℝ) ∧ (k:ℝ) < B))
      ⊆ (Finset.Icc (⌊A⌋ + 1) (⌈B⌉ - 1)).image Int.toNat := by
    intro k hk
    rw [Finset.mem_filter] at hk
    obtain ⟨-, hA, hB⟩ := hk
    rw [Finset.mem_image]
    refine ⟨(k : ℤ), ?_, Int.toNat_natCast k⟩
    rw [Finset.mem_Icc]
    constructor
    · rw [Int.add_one_le_iff, Int.floor_lt]
      exact_mod_cast hA
    · rw [Int.le_sub_one_iff, Int.lt_ceil]
      exact_mod_cast hB
  calc (((Finset.range q).filter
        (fun k : ℕ => A < (k:ℝ) ∧ (k:ℝ) < B)).card : ℝ)
      ≤ (((Finset.Icc (⌊A⌋ + 1) (⌈B⌉ - 1)).image Int.toNat).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((Finset.Icc (⌊A⌋ + 1) (⌈B⌉ - 1)).card : ℝ) := by
        exact_mod_cast Finset.card_image_le
    _ ≤ B - A + 1 := by
        rw [Int.card_Icc]
        rcases le_or_gt (⌊A⌋ + 1) (⌈B⌉ - 1) with h | h
        · have h1 : ((⌈B⌉ - 1 + 1 - (⌊A⌋ + 1)).toNat : ℝ)
              = (⌈B⌉ : ℝ) - (⌊A⌋ : ℝ) - 1 := by
            exact_mod_cast (by omega :
              ((⌈B⌉ - 1 + 1 - (⌊A⌋ + 1)).toNat : ℤ) = ⌈B⌉ - ⌊A⌋ - 1)
          rw [h1]
          have h2 : (⌈B⌉ : ℝ) ≤ B + 1 := by
            have ha : ((⌈B⌉ : ℤ) : ℝ) ≤ ((⌊B⌋ + 1 : ℤ) : ℝ) := by
              exact_mod_cast Int.ceil_le_floor_add_one B
            have hb : ((⌊B⌋ : ℤ) : ℝ) ≤ B := Int.floor_le B
            push_cast at ha
            linarith
          have h4 : A - 1 ≤ (⌊A⌋ : ℝ) := by
            have := Int.sub_one_lt_floor A
            linarith [this]
          linarith
        · have h1 : (⌈B⌉ - 1 + 1 - (⌊A⌋ + 1)).toNat = 0 := by omega
          rw [h1]
          push_cast
          linarith

end ExpSums

end MoltResearch
