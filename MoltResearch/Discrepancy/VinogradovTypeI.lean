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


/-- **The near-integer window count** (Track R, V2a-ii-b): among the `q`
shifted lattice points `k/q + η`, `k < q`, at most `8qs + 4` lie within
`s` of an integer.  Four rounding candidates `⌊η⌋−1, …, ⌊η⌋+2` cover all
possible nearest integers, and each contributes a real interval of
length `2qs` priced by `card_range_filter_Ioo_le`. -/
theorem card_nint_window_le (q : ℕ) (η s : ℝ) (hs : 0 ≤ s) :
    (((Finset.range q).filter
        (fun k : ℕ => nint ((k:ℝ)/(q:ℝ) + η) < s)).card : ℝ)
      ≤ 8*(q:ℝ)*s + 4 := by
  classical
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · simp
  rcases le_or_gt (1/2 : ℝ) s with hs2 | hs2
  · have h1 : ((Finset.range q).filter
        (fun k : ℕ => nint ((k:ℝ)/(q:ℝ) + η) < s)).card ≤ q := by
      refine le_trans (Finset.card_filter_le _ _) ?_
      rw [Finset.card_range]
    have h2 : (q:ℝ) ≤ 8*(q:ℝ)*s := by
      have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq0
      nlinarith
    have h3 : (((Finset.range q).filter
        (fun k : ℕ => nint ((k:ℝ)/(q:ℝ) + η) < s)).card : ℝ) ≤ (q:ℝ) := by
      exact_mod_cast h1
    linarith
  · have hq0R : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq0
    have hsub : (Finset.range q).filter
        (fun k : ℕ => nint ((k:ℝ)/(q:ℝ) + η) < s)
        ⊆ (Finset.range 4).biUnion (fun i =>
            (Finset.range q).filter (fun k : ℕ =>
              (q:ℝ)*(((⌊η⌋ - 1 + (i:ℤ) : ℤ):ℝ) - η - s) < (k:ℝ)
              ∧ (k:ℝ) < (q:ℝ)*(((⌊η⌋ - 1 + (i:ℤ) : ℤ):ℝ) - η + s))) := by
      intro k hk
      rw [Finset.mem_filter] at hk
      obtain ⟨hkq', hnint⟩ := hk
      have hkq : k < q := Finset.mem_range.mp hkq'
      have hx_lo : η ≤ (k:ℝ)/(q:ℝ) + η := by
        have h0 : (0:ℝ) ≤ (k:ℝ)/(q:ℝ) := by positivity
        linarith
      have hx_hi : (k:ℝ)/(q:ℝ) + η < η + 1 := by
        have h0 : (k:ℝ)/(q:ℝ) < 1 :=
          (div_lt_one hq0R).mpr (by exact_mod_cast hkq)
        linarith
      have hround := abs_sub_round ((k:ℝ)/(q:ℝ) + η)
      have hround' := abs_le.mp hround
      have hfl_le : ((⌊η⌋ : ℤ):ℝ) ≤ η := Int.floor_le η
      have hfl_gt : η < ((⌊η⌋ : ℤ):ℝ) + 1 := Int.lt_floor_add_one η
      have hM_lo : ⌊η⌋ - 1 ≤ round ((k:ℝ)/(q:ℝ) + η) := by
        by_contra hc
        push_neg at hc
        have h3 : ((round ((k:ℝ)/(q:ℝ) + η) : ℤ):ℝ)
            ≤ ((⌊η⌋ : ℤ):ℝ) - 2 := by
          exact_mod_cast (by omega : (round ((k:ℝ)/(q:ℝ) + η) : ℤ)
            ≤ ⌊η⌋ - 2)
        linarith [hround'.2]
      have hM_hi : round ((k:ℝ)/(q:ℝ) + η) ≤ ⌊η⌋ + 2 := by
        by_contra hc
        push_neg at hc
        have h3 : ((⌊η⌋ : ℤ):ℝ) + 3
            ≤ ((round ((k:ℝ)/(q:ℝ) + η) : ℤ):ℝ) := by
          exact_mod_cast (by omega : (⌊η⌋ + 3 : ℤ)
            ≤ round ((k:ℝ)/(q:ℝ) + η))
        linarith [hround'.1]
      rw [Finset.mem_biUnion]
      refine ⟨(round ((k:ℝ)/(q:ℝ) + η) - (⌊η⌋ - 1)).toNat, ?_, ?_⟩
      · rw [Finset.mem_range]
        omega
      · rw [Finset.mem_filter]
        refine ⟨hkq', ?_⟩
        have hcast : ((⌊η⌋ - 1
              + ((round ((k:ℝ)/(q:ℝ) + η) - (⌊η⌋ - 1)).toNat : ℤ) : ℤ):ℝ)
            = ((round ((k:ℝ)/(q:ℝ) + η) : ℤ):ℝ) := by
          exact_mod_cast (by omega : (⌊η⌋ - 1
              + ((round ((k:ℝ)/(q:ℝ) + η) - (⌊η⌋ - 1)).toNat : ℤ) : ℤ)
            = round ((k:ℝ)/(q:ℝ) + η))
        rw [hcast]
        rw [nint] at hnint
        have h5 := abs_lt.mp hnint
        have hdiv : (q:ℝ) * ((k:ℝ)/(q:ℝ)) = (k:ℝ) := by
          field_simp
        constructor
        · have h6 : ((round ((k:ℝ)/(q:ℝ) + η) : ℤ):ℝ) - η - s
              < (k:ℝ)/(q:ℝ) := by
            linarith [h5.1]
          calc (q:ℝ) * (((round ((k:ℝ)/(q:ℝ) + η) : ℤ):ℝ) - η - s)
              < (q:ℝ) * ((k:ℝ)/(q:ℝ)) := mul_lt_mul_of_pos_left h6 hq0R
            _ = (k:ℝ) := hdiv
        · have h6 : (k:ℝ)/(q:ℝ)
              < ((round ((k:ℝ)/(q:ℝ) + η) : ℤ):ℝ) - η + s := by
            linarith [h5.2]
          calc (k:ℝ) = (q:ℝ) * ((k:ℝ)/(q:ℝ)) := hdiv.symm
            _ < (q:ℝ) * (((round ((k:ℝ)/(q:ℝ) + η) : ℤ):ℝ) - η + s) :=
                mul_lt_mul_of_pos_left h6 hq0R
    have hcard1 : ((Finset.range q).filter
        (fun k : ℕ => nint ((k:ℝ)/(q:ℝ) + η) < s)).card
        ≤ ∑ i ∈ Finset.range 4,
            ((Finset.range q).filter (fun k : ℕ =>
              (q:ℝ)*(((⌊η⌋ - 1 + (i:ℤ) : ℤ):ℝ) - η - s) < (k:ℝ)
              ∧ (k:ℝ) < (q:ℝ)*(((⌊η⌋ - 1 + (i:ℤ) : ℤ):ℝ) - η + s))).card :=
      le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le)
    have hcard2 : ∀ i ∈ Finset.range 4,
        (((Finset.range q).filter (fun k : ℕ =>
            (q:ℝ)*(((⌊η⌋ - 1 + (i:ℤ) : ℤ):ℝ) - η - s) < (k:ℝ)
            ∧ (k:ℝ) < (q:ℝ)*(((⌊η⌋ - 1 + (i:ℤ) : ℤ):ℝ) - η + s))).card : ℝ)
          ≤ 2*(q:ℝ)*s + 1 := by
      intro i _
      have hAB : (q:ℝ)*(((⌊η⌋ - 1 + (i:ℤ) : ℤ):ℝ) - η - s)
          ≤ (q:ℝ)*(((⌊η⌋ - 1 + (i:ℤ) : ℤ):ℝ) - η + s) := by
        refine mul_le_mul_of_nonneg_left ?_ hq0R.le
        linarith
      refine le_trans (card_range_filter_Ioo_le q hAB) ?_
      have hexp : (q:ℝ)*(((⌊η⌋ - 1 + (i:ℤ) : ℤ):ℝ) - η + s)
          - (q:ℝ)*(((⌊η⌋ - 1 + (i:ℤ) : ℤ):ℝ) - η - s) = 2*(q:ℝ)*s := by
        ring
      linarith [hexp.le, hexp.ge]
    calc (((Finset.range q).filter
        (fun k : ℕ => nint ((k:ℝ)/(q:ℝ) + η) < s)).card : ℝ)
        ≤ (∑ i ∈ Finset.range 4,
            ((Finset.range q).filter (fun k : ℕ =>
              (q:ℝ)*(((⌊η⌋ - 1 + (i:ℤ) : ℤ):ℝ) - η - s) < (k:ℝ)
              ∧ (k:ℝ) < (q:ℝ)*(((⌊η⌋ - 1 + (i:ℤ) : ℤ):ℝ) - η + s))).card
            : ℝ) := by
          exact_mod_cast hcard1
      _ = ∑ i ∈ Finset.range 4,
            (((Finset.range q).filter (fun k : ℕ =>
              (q:ℝ)*(((⌊η⌋ - 1 + (i:ℤ) : ℤ):ℝ) - η - s) < (k:ℝ)
              ∧ (k:ℝ) < (q:ℝ)*(((⌊η⌋ - 1 + (i:ℤ) : ℤ):ℝ) - η + s))).card
              : ℝ) := by
          push_cast
          ring
      _ ≤ ∑ i ∈ Finset.range 4, (2*(q:ℝ)*s + 1) :=
          Finset.sum_le_sum hcard2
      _ = 8*(q:ℝ)*s + 4 := by
          rw [Finset.sum_const, Finset.card_range]
          push_cast
          ring


/-- **The block count at a rational-plus-drift frequency** (Track R,
V2a-iii): over one block of `q` consecutive integers, at most
`8q(t + q|δ|) + 4` values of `d` put `d·(a/q + δ)` within `t` of an
integer.  The map `d ↦ (d−jq)·a mod q` carries the block injectively
onto the `k/q`-lattice (coprimality), and the drift `d·δ` displaces
each point by at most `q|δ|` from the common shift, priced by the
Lipschitz bound and `card_nint_window_le`. -/
theorem card_block_nint_lt_le (a q : ℕ) (hq : 1 ≤ q)
    (hcop : Nat.Coprime a q) (δ : ℝ) (j : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (((Finset.Ioc (j*q) (j*q + q)).filter
        (fun d : ℕ => nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < t)).card : ℝ)
      ≤ 8*(q:ℝ)*(t + (q:ℝ)*|δ|) + 4 := by
  classical
  have hq0R : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hs0 : (0:ℝ) ≤ t + (q:ℝ)*|δ| := by positivity
  -- the pointwise transfer: filter members map into the window filter
  have hpoint : ∀ d ∈ (Finset.Ioc (j*q) (j*q + q)).filter
      (fun d : ℕ => nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < t),
      ((d - j*q) * a) % q ∈ (Finset.range q).filter
        (fun k : ℕ => nint ((k:ℝ)/(q:ℝ) + ((j*q : ℕ):ℝ) * δ)
          < t + (q:ℝ)*|δ|) := by
    intro d hd
    rw [Finset.mem_filter, Finset.mem_Ioc] at hd
    obtain ⟨⟨hd1, hd2⟩, hdn⟩ := hd
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ (by omega), ?_⟩
    have hr1 : 1 ≤ d - j*q := by omega
    have hrq : d - j*q ≤ q := by omega
    have hd_eq : d = j*q + (d - j*q) := by omega
    have hdm : (q:ℝ) * ((((d - j*q)*a)/q : ℕ):ℝ)
        + ((((d - j*q)*a) % q : ℕ):ℝ) = (((d - j*q)*a : ℕ):ℝ) := by
      exact_mod_cast Nat.div_add_mod ((d - j*q)*a) q
    have hsplit : (d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)
        = (((((d - j*q)*a) % q : ℕ):ℝ)/(q:ℝ) + (d:ℝ)*δ)
          + ((j*a + ((d - j*q)*a)/q : ℕ):ℝ) := by
      have hd_castR : (d:ℝ) = ((j*q : ℕ):ℝ) + (((d - j*q) : ℕ):ℝ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n:ℝ)) hd_eq
      rw [hd_castR]
      have hne : (q:ℝ) ≠ 0 := ne_of_gt hq0R
      field_simp
      push_cast
      push_cast at hdm
      ring_nf
      ring_nf at hdm
      nlinarith [hdm]
    rw [hsplit, nint_add_natCast] at hdn
    have hlip := nint_le_nint_add_abs
      ((((((d - j*q)*a) % q : ℕ):ℝ))/(q:ℝ) + ((j*q : ℕ):ℝ) * δ)
      ((((((d - j*q)*a) % q : ℕ):ℝ))/(q:ℝ) + (d:ℝ)*δ)
    have hdist : |(((((d - j*q)*a) % q : ℕ):ℝ)/(q:ℝ) + ((j*q : ℕ):ℝ) * δ)
        - ((((((d - j*q)*a) % q : ℕ):ℝ))/(q:ℝ) + (d:ℝ)*δ)|
        ≤ (q:ℝ)*|δ| := by
      have h1 : (((((d - j*q)*a) % q : ℕ):ℝ)/(q:ℝ) + ((j*q : ℕ):ℝ) * δ)
          - ((((((d - j*q)*a) % q : ℕ):ℝ))/(q:ℝ) + (d:ℝ)*δ)
          = -((((d - j*q) : ℕ):ℝ) * δ) := by
        have hd_castR : (d:ℝ) = ((j*q : ℕ):ℝ) + (((d - j*q) : ℕ):ℝ) := by
          exact_mod_cast congrArg (fun n : ℕ => (n:ℝ)) hd_eq
        rw [hd_castR]
        ring
      rw [h1, abs_neg, abs_mul]
      have h2 : |(((d - j*q) : ℕ):ℝ)| ≤ (q:ℝ) := by
        rw [abs_of_nonneg (Nat.cast_nonneg _)]
        exact_mod_cast hrq
      have h3 : (0:ℝ) ≤ |δ| := abs_nonneg δ
      nlinarith [h2, h3]
    linarith [hlip, hdn, hdist]
  -- injectivity of the block permutation
  have hinj : Set.InjOn (fun d : ℕ => ((d - j*q) * a) % q)
      ↑((Finset.Ioc (j*q) (j*q + q)).filter
        (fun d : ℕ => nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < t)) := by
    intro d hd d' hd' heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ioc] at hd hd'
    have heq' : ((d - j*q) * a) % q = ((d' - j*q) * a) % q := heq
    have h1 : (d - j*q) * a ≡ (d' - j*q) * a [MOD q] := heq'
    have h2 : (d - j*q) ≡ (d' - j*q) [MOD q] :=
      Nat.ModEq.cancel_right_of_coprime hcop.symm h1
    have h3 : (d - j*q) % q = (d' - j*q) % q := h2
    obtain ⟨⟨hda, hdb⟩, -⟩ := hd
    obtain ⟨⟨hda', hdb'⟩, -⟩ := hd'
    have hr1 : 1 ≤ d - j*q := by omega
    have hrq : d - j*q ≤ q := by omega
    have hr1' : 1 ≤ d' - j*q := by omega
    have hrq' : d' - j*q ≤ q := by omega
    rcases eq_or_lt_of_le hrq with hcase | hcase <;>
      rcases eq_or_lt_of_le hrq' with hcase' | hcase'
    · omega
    · rw [hcase, Nat.mod_self, Nat.mod_eq_of_lt hcase'] at h3
      omega
    · rw [hcase', Nat.mod_self, Nat.mod_eq_of_lt hcase] at h3
      omega
    · rw [Nat.mod_eq_of_lt hcase, Nat.mod_eq_of_lt hcase'] at h3
      omega
  -- assemble
  calc (((Finset.Ioc (j*q) (j*q + q)).filter
      (fun d : ℕ => nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < t)).card : ℝ)
      ≤ (((Finset.range q).filter
          (fun k : ℕ => nint ((k:ℝ)/(q:ℝ) + ((j*q : ℕ):ℝ) * δ)
            < t + (q:ℝ)*|δ|)).card : ℝ) := by
        have hmaps : Set.MapsTo (fun d : ℕ => ((d - j*q) * a) % q)
            ↑((Finset.Ioc (j*q) (j*q + q)).filter
              (fun d : ℕ => nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < t))
            ↑((Finset.range q).filter
              (fun k : ℕ => nint ((k:ℝ)/(q:ℝ) + ((j*q : ℕ):ℝ) * δ)
                < t + (q:ℝ)*|δ|)) := by
          intro d hd
          rw [Finset.mem_coe] at hd ⊢
          exact hpoint d hd
        exact_mod_cast Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ 8*(q:ℝ)*(t + (q:ℝ)*|δ|) + 4 :=
        card_nint_window_le q (((j*q : ℕ):ℝ) * δ) (t + (q:ℝ)*|δ|) hs0

end ExpSums

end MoltResearch
