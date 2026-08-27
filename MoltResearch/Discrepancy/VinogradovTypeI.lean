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


/-- Auxiliary count: a `biUnion` of `n` real-interval filters of common
length bound `L` holds at most `n(L+1)` points. -/
theorem card_biUnion_Ioo_le (q n : ℕ) (A B : ℕ → ℝ) (L : ℝ)
    (hAB : ∀ i ∈ Finset.range n, A i ≤ B i)
    (hlen : ∀ i ∈ Finset.range n, B i - A i ≤ L) :
    ((((Finset.range n).biUnion (fun i => (Finset.range q).filter
        (fun k : ℕ => A i < (k:ℝ) ∧ (k:ℝ) < B i))).card : ℕ) : ℝ)
      ≤ (n:ℝ) * (L + 1) := by
  classical
  calc ((((Finset.range n).biUnion (fun i => (Finset.range q).filter
        (fun k : ℕ => A i < (k:ℝ) ∧ (k:ℝ) < B i))).card : ℕ) : ℝ)
      ≤ ((∑ i ∈ Finset.range n,
          ((Finset.range q).filter
            (fun k : ℕ => A i < (k:ℝ) ∧ (k:ℝ) < B i)).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ∑ i ∈ Finset.range n,
          (((Finset.range q).filter
            (fun k : ℕ => A i < (k:ℝ) ∧ (k:ℝ) < B i)).card : ℝ) := by
        push_cast
        ring
    _ ≤ ∑ i ∈ Finset.range n, (L + 1) := by
        refine Finset.sum_le_sum fun i hi => ?_
        refine le_trans (card_range_filter_Ioo_le q (hAB i hi)) ?_
        linarith [hlen i hi]
    _ = (n:ℝ) * (L + 1) := by
        rw [Finset.sum_const, Finset.card_range]
        push_cast
        ring

/-- **The annulus window count** (Track R, V2b-i): among the `q` shifted
lattice points `k/q + η`, at most `8qw + 16` have `nint` in the annulus
`[t, t+w)`.  Each of the four rounding candidates contributes one
interval of length `≤ qw + 1` on each side of its integer.  Unlike the
cumulative count, this is bounded by a constant on `1/q`-fine shells —
the fact the harmonic assembly of the Type I counting lemma needs. -/
theorem card_nint_annulus_le (q : ℕ) (η t w : ℝ) (ht : 0 ≤ t)
    (hw : 0 ≤ w) :
    (((Finset.range q).filter
        (fun k : ℕ => t ≤ nint ((k:ℝ)/(q:ℝ) + η)
          ∧ nint ((k:ℝ)/(q:ℝ) + η) < t + w)).card : ℝ)
      ≤ 8*(q:ℝ)*w + 16 := by
  classical
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · simp
  have hq0R : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq0
  set R : Finset ℕ := (Finset.range 4).biUnion (fun i =>
      (Finset.range q).filter (fun k : ℕ =>
        (q:ℝ)*(((⌊η⌋ - 1 + (i:ℤ) : ℤ):ℝ) + t - η) - 1 < (k:ℝ)
        ∧ (k:ℝ) < (q:ℝ)*(((⌊η⌋ - 1 + (i:ℤ) : ℤ):ℝ) + t + w - η)))
    with hR_def
  set Lset : Finset ℕ := (Finset.range 4).biUnion (fun i =>
      (Finset.range q).filter (fun k : ℕ =>
        (q:ℝ)*(((⌊η⌋ - 1 + (i:ℤ) : ℤ):ℝ) - t - w - η) < (k:ℝ)
        ∧ (k:ℝ) < (q:ℝ)*(((⌊η⌋ - 1 + (i:ℤ) : ℤ):ℝ) - t - η) + 1))
    with hL_def
  have hsub : (Finset.range q).filter
      (fun k : ℕ => t ≤ nint ((k:ℝ)/(q:ℝ) + η)
        ∧ nint ((k:ℝ)/(q:ℝ) + η) < t + w) ⊆ R ∪ Lset := by
    intro k hk
    rw [Finset.mem_filter] at hk
    obtain ⟨hkq', hann⟩ := hk
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
    rw [nint] at hann
    have hcastM : ((⌊η⌋ - 1
          + ((round ((k:ℝ)/(q:ℝ) + η) - (⌊η⌋ - 1)).toNat : ℤ) : ℤ):ℝ)
        = ((round ((k:ℝ)/(q:ℝ) + η) : ℤ):ℝ) := by
      exact_mod_cast (by omega : (⌊η⌋ - 1
          + ((round ((k:ℝ)/(q:ℝ) + η) - (⌊η⌋ - 1)).toNat : ℤ) : ℤ)
        = round ((k:ℝ)/(q:ℝ) + η))
    have hdiv : (q:ℝ) * ((k:ℝ)/(q:ℝ)) = (k:ℝ) := by
      field_simp
    rw [Finset.mem_union]
    rcases le_or_gt ((round ((k:ℝ)/(q:ℝ) + η) : ℤ):ℝ)
        ((k:ℝ)/(q:ℝ) + η) with hside | hside
    · left
      rw [hR_def, Finset.mem_biUnion]
      refine ⟨(round ((k:ℝ)/(q:ℝ) + η) - (⌊η⌋ - 1)).toNat, ?_, ?_⟩
      · rw [Finset.mem_range]
        omega
      · rw [Finset.mem_filter]
        refine ⟨hkq', ?_⟩
        rw [hcastM]
        have habs : |(k:ℝ)/(q:ℝ) + η
            - ((round ((k:ℝ)/(q:ℝ) + η) : ℤ):ℝ)|
            = (k:ℝ)/(q:ℝ) + η
              - ((round ((k:ℝ)/(q:ℝ) + η) : ℤ):ℝ) :=
          abs_of_nonneg (by linarith)
        rw [habs] at hann
        constructor
        · have h6 : ((round ((k:ℝ)/(q:ℝ) + η) : ℤ):ℝ) + t - η
              ≤ (k:ℝ)/(q:ℝ) := by
            linarith [hann.1]
          have h7 := mul_le_mul_of_nonneg_left h6 hq0R.le
          linarith [h7, hdiv]
        · have h6 : (k:ℝ)/(q:ℝ)
              < ((round ((k:ℝ)/(q:ℝ) + η) : ℤ):ℝ) + t + w - η := by
            linarith [hann.2]
          have h7 := mul_lt_mul_of_pos_left h6 hq0R
          linarith [h7, hdiv]
    · right
      rw [hL_def, Finset.mem_biUnion]
      refine ⟨(round ((k:ℝ)/(q:ℝ) + η) - (⌊η⌋ - 1)).toNat, ?_, ?_⟩
      · rw [Finset.mem_range]
        omega
      · rw [Finset.mem_filter]
        refine ⟨hkq', ?_⟩
        rw [hcastM]
        have habs : |(k:ℝ)/(q:ℝ) + η
            - ((round ((k:ℝ)/(q:ℝ) + η) : ℤ):ℝ)|
            = ((round ((k:ℝ)/(q:ℝ) + η) : ℤ):ℝ)
              - ((k:ℝ)/(q:ℝ) + η) := by
          rw [abs_of_neg (by linarith)]
          ring
        rw [habs] at hann
        constructor
        · have h6 : ((round ((k:ℝ)/(q:ℝ) + η) : ℤ):ℝ) - t - w - η
              < (k:ℝ)/(q:ℝ) := by
            linarith [hann.2]
          have h7 := mul_lt_mul_of_pos_left h6 hq0R
          linarith [h7, hdiv]
        · have h6 : (k:ℝ)/(q:ℝ)
              ≤ ((round ((k:ℝ)/(q:ℝ) + η) : ℤ):ℝ) - t - η := by
            linarith [hann.1]
          have h7 := mul_le_mul_of_nonneg_left h6 hq0R.le
          linarith [h7, hdiv]
  have hcR : ((R.card : ℕ) : ℝ) ≤ 4 * ((q:ℝ)*w + 1 + 1) := by
    rw [hR_def]
    refine card_biUnion_Ioo_le q 4 _ _ ((q:ℝ)*w + 1) ?_ ?_
    · intro i _
      nlinarith [hq0R.le, hw, ht]
    · intro i _
      nlinarith [hq0R.le, hw]
  have hcL : ((Lset.card : ℕ) : ℝ) ≤ 4 * ((q:ℝ)*w + 1 + 1) := by
    rw [hL_def]
    refine card_biUnion_Ioo_le q 4 _ _ ((q:ℝ)*w + 1) ?_ ?_
    · intro i _
      nlinarith [hq0R.le, hw, ht]
    · intro i _
      nlinarith [hq0R.le, hw]
  have hcU : ((R ∪ Lset).card : ℝ) ≤ 8*(q:ℝ)*w + 16 := by
    have h1 : (R ∪ Lset).card ≤ R.card + Lset.card := Finset.card_union_le R Lset
    have h2 : (((R ∪ Lset).card : ℕ) : ℝ)
        ≤ ((R.card + Lset.card : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    linarith [hcR, hcL]
  refine le_trans ?_ hcU
  exact_mod_cast Finset.card_le_card hsub


/-- **The annulus block count** (Track R, V2b-ii): over one block of `q`
consecutive integers at frequency `a/q + δ` with `gcd(a,q) = 1`, at most
`8q(w + 2q|δ|) + 16` values of `d` put `nint(d·β)` in the annulus
`[t, t+w)`.  The coprime permutation carries the block onto the lattice,
and the two-sided Lipschitz transfer widens the annulus by `q|δ|` on
each side (clipped at `0` by `max`). -/
theorem card_block_nint_annulus_le (a q : ℕ) (hq : 1 ≤ q)
    (hcop : Nat.Coprime a q) (δ : ℝ) (j : ℕ) (t w : ℝ) (ht : 0 ≤ t)
    (hw : 0 ≤ w) :
    (((Finset.Ioc (j*q) (j*q + q)).filter
        (fun d : ℕ => t ≤ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
          ∧ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < t + w)).card : ℝ)
      ≤ 8*(q:ℝ)*(w + 2*(q:ℝ)*|δ|) + 16 := by
  classical
  have hq0R : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hjit : (0:ℝ) ≤ (q:ℝ)*|δ| := by positivity
  have ht0 : (0:ℝ) ≤ max 0 (t - (q:ℝ)*|δ|) := le_max_left 0 _
  have hw0 : (0:ℝ) ≤ w + 2*(q:ℝ)*|δ| := by positivity
  have hpoint : ∀ d ∈ (Finset.Ioc (j*q) (j*q + q)).filter
      (fun d : ℕ => t ≤ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
        ∧ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < t + w),
      ((d - j*q) * a) % q ∈ (Finset.range q).filter
        (fun k : ℕ => max 0 (t - (q:ℝ)*|δ|)
            ≤ nint ((k:ℝ)/(q:ℝ) + ((j*q : ℕ):ℝ) * δ)
          ∧ nint ((k:ℝ)/(q:ℝ) + ((j*q : ℕ):ℝ) * δ)
            < max 0 (t - (q:ℝ)*|δ|) + (w + 2*(q:ℝ)*|δ|)) := by
    intro d hd
    rw [Finset.mem_filter, Finset.mem_Ioc] at hd
    obtain ⟨⟨hd1, hd2⟩, hdn1, hdn2⟩ := hd
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
    rw [hsplit, nint_add_natCast] at hdn1 hdn2
    have hdist : |(((((d - j*q)*a) % q : ℕ):ℝ)/(q:ℝ)
          + ((j*q : ℕ):ℝ) * δ)
        - ((((((d - j*q)*a) % q : ℕ):ℝ))/(q:ℝ) + (d:ℝ)*δ)|
        ≤ (q:ℝ)*|δ| := by
      have hd_castR : (d:ℝ) = ((j*q : ℕ):ℝ) + (((d - j*q) : ℕ):ℝ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n:ℝ)) hd_eq
      have h1 : (((((d - j*q)*a) % q : ℕ):ℝ)/(q:ℝ)
            + ((j*q : ℕ):ℝ) * δ)
          - ((((((d - j*q)*a) % q : ℕ):ℝ))/(q:ℝ) + (d:ℝ)*δ)
          = -((((d - j*q) : ℕ):ℝ) * δ) := by
        rw [hd_castR]
        ring
      rw [h1, abs_neg, abs_mul]
      have h2 : |(((d - j*q) : ℕ):ℝ)| ≤ (q:ℝ) := by
        rw [abs_of_nonneg (Nat.cast_nonneg _)]
        exact_mod_cast hrq
      nlinarith [h2, abs_nonneg δ]
    have hlip1 := nint_le_nint_add_abs
      ((((((d - j*q)*a) % q : ℕ):ℝ))/(q:ℝ) + ((j*q : ℕ):ℝ) * δ)
      ((((((d - j*q)*a) % q : ℕ):ℝ))/(q:ℝ) + (d:ℝ)*δ)
    have hlip2 := nint_le_nint_add_abs
      ((((((d - j*q)*a) % q : ℕ):ℝ))/(q:ℝ) + (d:ℝ)*δ)
      ((((((d - j*q)*a) % q : ℕ):ℝ))/(q:ℝ) + ((j*q : ℕ):ℝ) * δ)
    have hdist' : |(((((d - j*q)*a) % q : ℕ):ℝ)/(q:ℝ) + (d:ℝ)*δ)
        - ((((((d - j*q)*a) % q : ℕ):ℝ))/(q:ℝ)
          + ((j*q : ℕ):ℝ) * δ)| ≤ (q:ℝ)*|δ| := by
      rw [abs_sub_comm]
      exact hdist
    constructor
    · refine max_le (nint_nonneg _) ?_
      linarith [hlip2, hdn1, hdist']
    · have hmax : t - (q:ℝ)*|δ| ≤ max 0 (t - (q:ℝ)*|δ|) :=
        le_max_right 0 _
      linarith [hlip1, hdn2, hdist, hmax]
  have hinj : Set.InjOn (fun d : ℕ => ((d - j*q) * a) % q)
      ↑((Finset.Ioc (j*q) (j*q + q)).filter
        (fun d : ℕ => t ≤ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
          ∧ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < t + w)) := by
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
  have hmaps : Set.MapsTo (fun d : ℕ => ((d - j*q) * a) % q)
      ↑((Finset.Ioc (j*q) (j*q + q)).filter
        (fun d : ℕ => t ≤ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
          ∧ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < t + w))
      ↑((Finset.range q).filter
        (fun k : ℕ => max 0 (t - (q:ℝ)*|δ|)
            ≤ nint ((k:ℝ)/(q:ℝ) + ((j*q : ℕ):ℝ) * δ)
          ∧ nint ((k:ℝ)/(q:ℝ) + ((j*q : ℕ):ℝ) * δ)
            < max 0 (t - (q:ℝ)*|δ|) + (w + 2*(q:ℝ)*|δ|))) := by
    intro d hd
    rw [Finset.mem_coe] at hd ⊢
    exact hpoint d hd
  calc (((Finset.Ioc (j*q) (j*q + q)).filter
      (fun d : ℕ => t ≤ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
        ∧ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < t + w)).card : ℝ)
      ≤ (((Finset.range q).filter
          (fun k : ℕ => max 0 (t - (q:ℝ)*|δ|)
              ≤ nint ((k:ℝ)/(q:ℝ) + ((j*q : ℕ):ℝ) * δ)
            ∧ nint ((k:ℝ)/(q:ℝ) + ((j*q : ℕ):ℝ) * δ)
              < max 0 (t - (q:ℝ)*|δ|) + (w + 2*(q:ℝ)*|δ|))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ 8*(q:ℝ)*(w + 2*(q:ℝ)*|δ|) + 16 :=
        card_nint_annulus_le q (((j*q : ℕ):ℝ) * δ)
          (max 0 (t - (q:ℝ)*|δ|)) (w + 2*(q:ℝ)*|δ|) ht0 hw0


/-- **The harmonic sum against the logarithm** (Track R, V2b-iii-a):
`∑_{k=1}^{K} 1/k ≤ log K + 1`, by the telescoping bound
`1/(k+1) ≤ log(k+1) − log k`. -/
theorem sum_inv_le_log (K : ℕ) (hK : 1 ≤ K) :
    ∑ k ∈ Finset.Icc 1 K, (1:ℝ)/(k:ℝ) ≤ Real.log (K:ℝ) + 1 := by
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    have hmem : K + 1 ∉ Finset.Icc 1 K := by
      rw [Finset.mem_Icc]
      omega
    have hins : Finset.Icc 1 (K + 1) = insert (K + 1) (Finset.Icc 1 K) := by
      ext m
      rw [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Icc]
      omega
    rw [hins, Finset.sum_insert hmem]
    have hK0 : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
    have hK10 : (0:ℝ) < ((K:ℝ) + 1) := by linarith
    have hstep : (1:ℝ)/((K:ℝ) + 1)
        ≤ Real.log ((K:ℝ) + 1) - Real.log (K:ℝ) := by
      have hq0 : (0:ℝ) < (K:ℝ)/((K:ℝ) + 1) := by positivity
      have h1 := Real.log_le_sub_one_of_pos hq0
      have h2 : Real.log ((K:ℝ)/((K:ℝ) + 1))
          = Real.log (K:ℝ) - Real.log ((K:ℝ) + 1) :=
        Real.log_div (ne_of_gt hK0) (ne_of_gt hK10)
      rw [h2] at h1
      have h3 : (K:ℝ)/((K:ℝ) + 1) - 1 = -(1/((K:ℝ) + 1)) := by
        field_simp
        ring
      rw [h3] at h1
      linarith
    have hcast : ((K + 1 : ℕ):ℝ) = (K:ℝ) + 1 := by
      push_cast
      ring
    rw [hcast]
    linarith [ih, hstep]


/-- **The per-block sum against the counting machinery** (Track R,
V2b-iii-b): for any summand `g` bounded by `A` and by the reciprocal
distance `1/(2·nint(dβ))` wherever that distance is positive, the block
sum costs `13A` (the near-integer points, priced by the cumulative
count) plus `264q(log 8q + 1)` (the shells, `O(1)` points each by the
annulus count against the harmonic sum).  Stated against an abstract
`g` so that `nint = 0` — where Lean's `1/0 = 0` would poison a `min`
formulation — is priced at `A` like every other near point. -/
theorem sum_block_g_le (a q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime a q)
    (δ : ℝ) (hδ : |δ| ≤ 1/(q:ℝ)^2) (j : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (g : ℕ → ℝ)
    (hg0 : ∀ d ∈ Finset.Ioc (j*q) (j*q + q), 0 ≤ g d)
    (hgA : ∀ d ∈ Finset.Ioc (j*q) (j*q + q), g d ≤ A)
    (hg2 : ∀ d ∈ Finset.Ioc (j*q) (j*q + q),
      0 < nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) →
      g d ≤ 1/(2 * nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)))) :
    ∑ d ∈ Finset.Ioc (j*q) (j*q + q), g d
      ≤ 13*A + 264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1) := by
  classical
  have hq0R : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hqd2 : (q:ℝ)^2*|δ| ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left hδ (by positivity : (0:ℝ) ≤ (q:ℝ)^2)
    calc (q:ℝ)^2*|δ| ≤ (q:ℝ)^2*(1/(q:ℝ)^2) := h1
      _ = 1 := by field_simp
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc (j*q) (j*q + q))
    (fun d : ℕ => nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < 1/(16*(q:ℝ)))]
  have hS0 : ∑ d ∈ (Finset.Ioc (j*q) (j*q + q)).filter
      (fun d : ℕ => nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < 1/(16*(q:ℝ))), g d
      ≤ 13*A := by
    have hcard := card_block_nint_lt_le a q hq hcop δ j
      (1/(16*(q:ℝ))) (by positivity)
    have h16 : 8*(q:ℝ)*(1/(16*(q:ℝ)) + (q:ℝ)*|δ|) + 4 ≤ 13 := by
      have hexp : 8*(q:ℝ)*(1/(16*(q:ℝ))) = 1/2 := by
        field_simp
        ring
      nlinarith [hqd2, hexp]
    have hcard' : (((Finset.Ioc (j*q) (j*q + q)).filter
        (fun d : ℕ => nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
          < 1/(16*(q:ℝ)))).card : ℝ) ≤ 13 := le_trans hcard h16
    have hsum : ∑ d ∈ (Finset.Ioc (j*q) (j*q + q)).filter
        (fun d : ℕ => nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < 1/(16*(q:ℝ))), g d
        ≤ (((Finset.Ioc (j*q) (j*q + q)).filter
          (fun d : ℕ => nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
            < 1/(16*(q:ℝ)))).card : ℝ) * A := by
      have h := Finset.sum_le_card_nsmul ((Finset.Ioc (j*q) (j*q + q)).filter
        (fun d : ℕ => nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < 1/(16*(q:ℝ)))) g A
        (fun d hd => hgA d (Finset.filter_subset _ _ hd))
      rwa [nsmul_eq_mul] at h
    have hfin : (((Finset.Ioc (j*q) (j*q + q)).filter
        (fun d : ℕ => nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
          < 1/(16*(q:ℝ)))).card : ℝ) * A ≤ 13*A := by
      nlinarith [hcard', hA]
    linarith [hsum, hfin]
  have hcomp : ∑ d ∈ (Finset.Ioc (j*q) (j*q + q)).filter
      (fun d : ℕ => ¬ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < 1/(16*(q:ℝ))), g d
      ≤ 264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1) := by
    have hsub : (Finset.Ioc (j*q) (j*q + q)).filter
        (fun d : ℕ => ¬ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < 1/(16*(q:ℝ)))
        ⊆ (Finset.Icc 1 (8*q)).biUnion (fun k =>
          (Finset.Ioc (j*q) (j*q + q)).filter (fun d : ℕ =>
            (k:ℝ)/(16*(q:ℝ)) ≤ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
            ∧ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
              < (k:ℝ)/(16*(q:ℝ)) + 1/(16*(q:ℝ)))) := by
      intro d hd
      rw [Finset.mem_filter] at hd
      obtain ⟨hdblk, hdge⟩ := hd
      push_neg at hdge
      have hpos16 : (0:ℝ) < 16*(q:ℝ) := by positivity
      have hk1 : 1 ≤ ⌊16*(q:ℝ) * nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))⌋₊ := by
        refine Nat.le_floor ?_
        push_cast
        rw [div_le_iff₀ hpos16] at hdge
        linarith [hdge]
      have hk2 : ⌊16*(q:ℝ) * nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))⌋₊ ≤ 8*q := by
        have hhalf := nint_le_half ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
        have h1 : 16*(q:ℝ) * nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
            ≤ ((8*q : ℕ):ℝ) := by
          push_cast
          nlinarith [hhalf, hq0R.le]
        calc ⌊16*(q:ℝ) * nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))⌋₊
            ≤ ⌊((8*q : ℕ):ℝ)⌋₊ := Nat.floor_le_floor h1
          _ = 8*q := Nat.floor_natCast _
      rw [Finset.mem_biUnion]
      refine ⟨⌊16*(q:ℝ) * nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))⌋₊, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        exact ⟨hk1, hk2⟩
      · rw [Finset.mem_filter]
        refine ⟨hdblk, ?_, ?_⟩
        · rw [div_le_iff₀ hpos16]
          have := Nat.floor_le (mul_nonneg (le_of_lt hpos16)
            (nint_nonneg ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))))
          linarith
        · have h2 := Nat.lt_floor_add_one
            (16*(q:ℝ) * nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)))
          rw [div_add_div_same, lt_div_iff₀ hpos16]
          push_cast
          linarith
    have hdisj : (↑(Finset.Icc 1 (8*q)) : Set ℕ).PairwiseDisjoint
        (fun k => (Finset.Ioc (j*q) (j*q + q)).filter (fun d : ℕ =>
          (k:ℝ)/(16*(q:ℝ)) ≤ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
          ∧ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
            < (k:ℝ)/(16*(q:ℝ)) + 1/(16*(q:ℝ)))) := by
      intro k hk k' hk' hne
      rw [Function.onFun, Finset.disjoint_left]
      intro d hd hd'
      rw [Finset.mem_filter] at hd hd'
      obtain ⟨-, h1, h2⟩ := hd
      obtain ⟨-, h1', h2'⟩ := hd'
      have hpos16 : (0:ℝ) < 16*(q:ℝ) := by positivity
      rcases Nat.lt_or_ge k k' with hlt | hge
      · have hstep : (k:ℝ) + 1 ≤ (k':ℝ) := by exact_mod_cast hlt
        have : (k:ℝ)/(16*(q:ℝ)) + 1/(16*(q:ℝ)) ≤ (k':ℝ)/(16*(q:ℝ)) := by
          rw [div_add_div_same, div_le_div_iff₀ hpos16 hpos16]
          nlinarith [hstep, hpos16]
        linarith
      · have hne' : k' < k := by omega
        have hstep : (k':ℝ) + 1 ≤ (k:ℝ) := by exact_mod_cast hne'
        have : (k':ℝ)/(16*(q:ℝ)) + 1/(16*(q:ℝ)) ≤ (k:ℝ)/(16*(q:ℝ)) := by
          rw [div_add_div_same, div_le_div_iff₀ hpos16 hpos16]
          nlinarith [hstep, hpos16]
        linarith
    have hstep1 : ∑ d ∈ (Finset.Ioc (j*q) (j*q + q)).filter
        (fun d : ℕ => ¬ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < 1/(16*(q:ℝ))), g d
        ≤ ∑ d ∈ (Finset.Icc 1 (8*q)).biUnion (fun k =>
          (Finset.Ioc (j*q) (j*q + q)).filter (fun d : ℕ =>
            (k:ℝ)/(16*(q:ℝ)) ≤ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
            ∧ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
              < (k:ℝ)/(16*(q:ℝ)) + 1/(16*(q:ℝ)))), g d := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
      intro d hd _
      rw [Finset.mem_biUnion] at hd
      obtain ⟨k, -, hdk⟩ := hd
      exact hg0 d (Finset.filter_subset _ _ hdk)
    have hstep2 : ∑ d ∈ (Finset.Icc 1 (8*q)).biUnion (fun k =>
        (Finset.Ioc (j*q) (j*q + q)).filter (fun d : ℕ =>
          (k:ℝ)/(16*(q:ℝ)) ≤ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
          ∧ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
            < (k:ℝ)/(16*(q:ℝ)) + 1/(16*(q:ℝ)))), g d
        = ∑ k ∈ Finset.Icc 1 (8*q), ∑ d ∈ (Finset.Ioc (j*q) (j*q + q)).filter
          (fun d : ℕ => (k:ℝ)/(16*(q:ℝ)) ≤ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
            ∧ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
              < (k:ℝ)/(16*(q:ℝ)) + 1/(16*(q:ℝ))), g d :=
      Finset.sum_biUnion hdisj
    have hshell : ∀ k ∈ Finset.Icc 1 (8*q),
        ∑ d ∈ (Finset.Ioc (j*q) (j*q + q)).filter
          (fun d : ℕ => (k:ℝ)/(16*(q:ℝ)) ≤ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
            ∧ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
              < (k:ℝ)/(16*(q:ℝ)) + 1/(16*(q:ℝ))), g d
        ≤ 264*(q:ℝ)/(k:ℝ) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk.1
      have hcard := card_block_nint_annulus_le a q hq hcop δ j
        ((k:ℝ)/(16*(q:ℝ))) (1/(16*(q:ℝ))) (by positivity) (by positivity)
      have hcard33 : (((Finset.Ioc (j*q) (j*q + q)).filter
          (fun d : ℕ => (k:ℝ)/(16*(q:ℝ)) ≤ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
            ∧ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
              < (k:ℝ)/(16*(q:ℝ)) + 1/(16*(q:ℝ)))).card : ℝ) ≤ 33 := by
        have hexp : 8*(q:ℝ)*(1/(16*(q:ℝ)) + 2*(q:ℝ)*|δ|) + 16
            = 1/2 + 16*((q:ℝ)^2*|δ|) + 16 := by
          field_simp
          ring
        refine le_trans hcard ?_
        rw [hexp]
        linarith [hqd2]
      have hgk : ∀ d ∈ (Finset.Ioc (j*q) (j*q + q)).filter
          (fun d : ℕ => (k:ℝ)/(16*(q:ℝ)) ≤ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
            ∧ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
              < (k:ℝ)/(16*(q:ℝ)) + 1/(16*(q:ℝ))),
          g d ≤ 8*(q:ℝ)/(k:ℝ) := by
        intro d hd
        rw [Finset.mem_filter] at hd
        obtain ⟨hdblk, hlo, -⟩ := hd
        have hnpos : (0:ℝ) < nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) := by
          have : (0:ℝ) < (k:ℝ)/(16*(q:ℝ)) := by positivity
          linarith
        refine le_trans (hg2 d hdblk hnpos) ?_
        have h2n : (k:ℝ)/(8*(q:ℝ))
            ≤ 2 * nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) := by
          have : (k:ℝ)/(8*(q:ℝ)) = 2*((k:ℝ)/(16*(q:ℝ))) := by
            field_simp
            ring
          linarith [hlo, this.ge, this.le]
        have hpos8 : (0:ℝ) < (k:ℝ)/(8*(q:ℝ)) := by positivity
        calc 1/(2 * nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)))
            ≤ 1/((k:ℝ)/(8*(q:ℝ))) := one_div_le_one_div_of_le hpos8 h2n
          _ = 8*(q:ℝ)/(k:ℝ) := by
              field_simp
      have hsumk := Finset.sum_le_card_nsmul
        ((Finset.Ioc (j*q) (j*q + q)).filter
          (fun d : ℕ => (k:ℝ)/(16*(q:ℝ)) ≤ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
            ∧ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
              < (k:ℝ)/(16*(q:ℝ)) + 1/(16*(q:ℝ)))) g (8*(q:ℝ)/(k:ℝ)) hgk
      rw [nsmul_eq_mul] at hsumk
      have h8q0 : (0:ℝ) ≤ 8*(q:ℝ)/(k:ℝ) := by positivity
      have hfin2 : (((Finset.Ioc (j*q) (j*q + q)).filter
          (fun d : ℕ => (k:ℝ)/(16*(q:ℝ))
              ≤ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
            ∧ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
              < (k:ℝ)/(16*(q:ℝ)) + 1/(16*(q:ℝ)))).card : ℝ)
          * (8*(q:ℝ)/(k:ℝ)) ≤ 33 * (8*(q:ℝ)/(k:ℝ)) :=
        mul_le_mul_of_nonneg_right hcard33 h8q0
      have heqk : 33 * (8*(q:ℝ)/(k:ℝ)) = 264*(q:ℝ)/(k:ℝ) := by
        ring
      rw [heqk] at hfin2
      linarith [hsumk, hfin2]
    have h8q1 : 1 ≤ 8*q := by omega
    have hharm := sum_inv_le_log (8*q) h8q1
    have hcast8 : ((8*q : ℕ):ℝ) = 8*(q:ℝ) := by push_cast; ring
    rw [hcast8] at hharm
    rw [hstep2] at hstep1
    have hsum3 := Finset.sum_le_sum hshell
    have heq4 : ∑ k ∈ Finset.Icc 1 (8*q), 264*(q:ℝ)/(k:ℝ)
        = 264*(q:ℝ) * ∑ k ∈ Finset.Icc 1 (8*q), (1:ℝ)/(k:ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [heq4] at hsum3
    have hfin : 264*(q:ℝ) * ∑ k ∈ Finset.Icc 1 (8*q), (1:ℝ)/(k:ℝ)
        ≤ 264*(q:ℝ) * (Real.log (8*(q:ℝ)) + 1) := by
      refine mul_le_mul_of_nonneg_left hharm ?_
      positivity
    linarith [hstep1, hsum3, hfin]
  linarith [hS0, hcomp]


/-- **The counting lemma** (Track R, V2c): summing the per-block engine
over blocks.  For any summand bounded by `N/d` and by the reciprocal
distance at positive `nint`, the full range `[1, D]` costs
`13N(1 + (log D + 1)/q)` (the `N/d`-weights, block-by-block against the
harmonic sum) plus `(D/q + 1)·264q(log 8q + 1)` (the per-block shell
budget).  This is Vaughan's `∑ min(N/d, 1/‖dβ‖) ≪ (N/q + D + q)·log`
in the abstract-summand form the Type I estimate consumes. -/
theorem sum_range_g_le (a q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime a q)
    (δ : ℝ) (hδ : |δ| ≤ 1/(q:ℝ)^2) (D : ℕ) (hD : 1 ≤ D)
    (N : ℝ) (hN : 0 ≤ N) (g : ℕ → ℝ)
    (hg0 : ∀ d ∈ Finset.Icc 1 D, 0 ≤ g d)
    (hgN : ∀ d ∈ Finset.Icc 1 D, g d ≤ N/(d:ℝ))
    (hg2 : ∀ d ∈ Finset.Icc 1 D,
      0 < nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) →
      g d ≤ 1/(2 * nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)))) :
    ∑ d ∈ Finset.Icc 1 D, g d
      ≤ 13*N*(1 + (Real.log (D:ℝ) + 1)/(q:ℝ))
        + ((D:ℝ)/(q:ℝ) + 1) * (264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) := by
  classical
  have hq0R : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  set g' : ℕ → ℝ := fun d => if d ∈ Finset.Icc 1 D then g d else 0
    with hg'_def
  have hg'0 : ∀ d, 0 ≤ g' d := by
    intro d
    simp only [hg'_def]
    split
    · exact hg0 d (by assumption)
    · exact le_refl 0
  have heqsum : ∑ d ∈ Finset.Icc 1 D, g d = ∑ d ∈ Finset.Icc 1 D, g' d := by
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [hg'_def]
    rw [if_pos hd]
  have hcover : Finset.Icc 1 D ⊆ (Finset.range (D/q + 1)).biUnion
      (fun j => Finset.Ioc (j*q) (j*q + q)) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    rw [Finset.mem_biUnion]
    refine ⟨(d - 1)/q, ?_, ?_⟩
    · rw [Finset.mem_range]
      have h1 : (d - 1)/q ≤ D/q := Nat.div_le_div_right (by omega)
      omega
    · rw [Finset.mem_Ioc]
      have h2 : (d - 1) % q < q := Nat.mod_lt _ (by omega)
      have h3 : (d - 1)/q * q + (d - 1) % q = d - 1 :=
        Nat.div_add_mod' (d - 1) q
      omega
  have hdisjb : (↑(Finset.range (D/q + 1)) : Set ℕ).PairwiseDisjoint
      (fun j => Finset.Ioc (j*q) (j*q + q)) := by
    intro j hj j' hj' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro d hd hd'
    rw [Finset.mem_Ioc] at hd hd'
    rcases Nat.lt_or_ge j j' with hlt | hge
    · have h1 : (j + 1) * q ≤ j' * q := Nat.mul_le_mul_right q hlt
      have h2 : j*q + q = (j + 1) * q := by ring
      omega
    · have hlt' : j' < j := by omega
      have h1 : (j' + 1) * q ≤ j * q := Nat.mul_le_mul_right q hlt'
      have h2 : j'*q + q = (j' + 1) * q := by ring
      omega
  have hstep1 : ∑ d ∈ Finset.Icc 1 D, g' d
      ≤ ∑ d ∈ (Finset.range (D/q + 1)).biUnion
        (fun j => Finset.Ioc (j*q) (j*q + q)), g' d :=
    Finset.sum_le_sum_of_subset_of_nonneg hcover (fun d _ _ => hg'0 d)
  have hstep2 : ∑ d ∈ (Finset.range (D/q + 1)).biUnion
      (fun j => Finset.Ioc (j*q) (j*q + q)), g' d
      = ∑ j ∈ Finset.range (D/q + 1),
          ∑ d ∈ Finset.Ioc (j*q) (j*q + q), g' d :=
    Finset.sum_biUnion hdisjb
  have hblock : ∀ j ∈ Finset.range (D/q + 1),
      ∑ d ∈ Finset.Ioc (j*q) (j*q + q), g' d
      ≤ 13*(N/((j:ℝ)*(q:ℝ) + 1)) + 264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1) := by
    intro j _
    have hA0 : (0:ℝ) ≤ N/((j:ℝ)*(q:ℝ) + 1) := by positivity
    refine sum_block_g_le a q hq hcop δ hδ j (N/((j:ℝ)*(q:ℝ) + 1)) hA0 g'
      (fun d _ => hg'0 d) ?_ ?_
    · intro d hd
      rw [Finset.mem_Ioc] at hd
      simp only [hg'_def]
      split
      · rename_i hdIcc
        have hdc : (j:ℝ)*(q:ℝ) + 1 ≤ (d:ℝ) := by
          have : j*q + 1 ≤ d := by omega
          push_cast
          exact_mod_cast this
        have hd0 : (0:ℝ) < (j:ℝ)*(q:ℝ) + 1 := by positivity
        have hdpos : (0:ℝ) < (d:ℝ) := by
          have : 0 < d := by omega
          exact_mod_cast this
        refine le_trans (hgN d hdIcc) ?_
        rw [div_le_div_iff₀ hdpos hd0]
        nlinarith [hdc, hN]
      · exact hA0
    · intro d hd hpos
      simp only [hg'_def]
      split
      · rename_i hdIcc
        exact hg2 d hdIcc hpos
      · positivity
  have hsum3 : ∑ j ∈ Finset.range (D/q + 1),
      ∑ d ∈ Finset.Ioc (j*q) (j*q + q), g' d
      ≤ ∑ j ∈ Finset.range (D/q + 1),
        (13*(N/((j:ℝ)*(q:ℝ) + 1))
          + 264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) :=
    Finset.sum_le_sum hblock
  have hexpand : ∑ j ∈ Finset.range (D/q + 1),
      (13*(N/((j:ℝ)*(q:ℝ) + 1)) + 264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1))
      = 13*N * (∑ j ∈ Finset.range (D/q + 1), 1/((j:ℝ)*(q:ℝ) + 1))
        + ((D/q + 1 : ℕ):ℝ) * (264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hinv : ∑ j ∈ Finset.range (D/q + 1), 1/((j:ℝ)*(q:ℝ) + 1)
      ≤ 1 + (Real.log (D:ℝ) + 1)/(q:ℝ) := by
    rw [Finset.sum_range_succ']
    have hrest : ∑ i ∈ Finset.range (D/q),
        1/(((i+1 : ℕ):ℝ)*(q:ℝ) + 1)
        ≤ (Real.log (D:ℝ) + 1)/(q:ℝ) := by
      rcases Nat.eq_zero_or_pos (D/q) with hJ0 | hJ0
      · rw [hJ0]
        simp
        have hlogD : (0:ℝ) ≤ Real.log (D:ℝ) :=
          Real.log_natCast_nonneg D
        positivity
      · have hterm : ∀ i ∈ Finset.range (D/q),
            1/(((i+1 : ℕ):ℝ)*(q:ℝ) + 1)
            ≤ (1/(q:ℝ)) * (1/((i+1 : ℕ):ℝ)) := by
          intro i _
          have hi0 : (0:ℝ) < ((i+1 : ℕ):ℝ) := by
            exact_mod_cast Nat.succ_pos i
          have h1 : (0:ℝ) < ((i+1 : ℕ):ℝ)*(q:ℝ) := by positivity
          have h2 : ((i+1 : ℕ):ℝ)*(q:ℝ) ≤ ((i+1 : ℕ):ℝ)*(q:ℝ) + 1 := by
            linarith
          calc 1/(((i+1 : ℕ):ℝ)*(q:ℝ) + 1)
              ≤ 1/(((i+1 : ℕ):ℝ)*(q:ℝ)) :=
                one_div_le_one_div_of_le h1 h2
            _ = (1/(q:ℝ)) * (1/((i+1 : ℕ):ℝ)) := by
                field_simp
        refine le_trans (Finset.sum_le_sum hterm) ?_
        rw [← Finset.mul_sum]
        have hreidx : ∑ i ∈ Finset.range (D/q), 1/((i+1 : ℕ):ℝ)
            = ∑ k ∈ Finset.Icc 1 (D/q), (1:ℝ)/(k:ℝ) := by
          rw [show Finset.Icc 1 (D/q) = Finset.Ico 1 (D/q + 1) by
            ext m
            rw [Finset.mem_Icc, Finset.mem_Ico]
            omega]
          rw [Finset.sum_Ico_eq_sum_range]
          refine Finset.sum_congr ?_ fun i _ => ?_
          · rw [Nat.add_sub_cancel]
          · rw [Nat.add_comm 1 i]
        have hharm := sum_inv_le_log (D/q) hJ0
        have hJD : Real.log ((D/q : ℕ):ℝ) ≤ Real.log (D:ℝ) := by
          refine Real.log_le_log ?_ ?_
          · exact_mod_cast hJ0
          · exact_mod_cast Nat.div_le_self D q
        rw [hreidx]
        have hcomb : ∑ k ∈ Finset.Icc 1 (D/q), (1:ℝ)/(k:ℝ)
            ≤ Real.log (D:ℝ) + 1 := by
          linarith [hharm, hJD]
        rw [div_eq_mul_one_div (Real.log (D:ℝ) + 1) (q:ℝ), mul_comm
          (Real.log (D:ℝ) + 1) (1/(q:ℝ))]
        refine mul_le_mul_of_nonneg_left hcomb ?_
        positivity
    have hz : (1:ℝ)/(((0:ℕ):ℝ)*(q:ℝ) + 1) = 1 := by
      norm_num
    push_cast
    push_cast at hrest hz
    linarith [hrest, hz.le, hz.ge]
  have hJcast : ((D/q + 1 : ℕ):ℝ) ≤ (D:ℝ)/(q:ℝ) + 1 := by
    have h1 : ((D/q : ℕ):ℝ) ≤ (D:ℝ)/(q:ℝ) := Nat.cast_div_le
    push_cast
    linarith [h1]
  have hC0 : (0:ℝ) ≤ 264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1) := by
    have h8 : (1:ℝ) ≤ 8*(q:ℝ) := by
      have hq1R : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
      linarith
    have := Real.log_nonneg h8
    positivity
  have h13N : (0:ℝ) ≤ 13*N := by linarith
  rw [heqsum]
  refine le_trans hstep1 ?_
  rw [hstep2]
  refine le_trans hsum3 ?_
  rw [hexpand]
  have h1 : 13*N * (∑ j ∈ Finset.range (D/q + 1), 1/((j:ℝ)*(q:ℝ) + 1))
      ≤ 13*N*(1 + (Real.log (D:ℝ) + 1)/(q:ℝ)) :=
    mul_le_mul_of_nonneg_left hinv h13N
  have h2 : ((D/q + 1 : ℕ):ℝ) * (264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1))
      ≤ ((D:ℝ)/(q:ℝ) + 1) * (264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) :=
    mul_le_mul_of_nonneg_right hJcast hC0
  linarith [h1, h2]


/-- **The Type I estimate** (Track R, V3): a divisor-weighted sum of
geometric inner sums at frequency `β = a/q + δ` is controlled by the
counting lemma — each inner sum is priced by its length and by the
linear-phase Kusmin–Landau bound at `nint(dβ)`, and `sum_range_g_le`
does the bookkeeping at summand `‖·‖/2`. -/
theorem typeI_sum_le (a q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime a q)
    (δ : ℝ) (hδ : |δ| ≤ 1/(q:ℝ)^2) (D N : ℕ) (hD : 1 ≤ D)
    (c : ℕ → ℂ) (hc : ∀ d, ‖c d‖ ≤ 1) :
    ∑ d ∈ Finset.Icc 1 D,
        ‖c d * ∑ m ∈ Finset.Icc 1 (N/d),
          e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
      ≤ 13*(N:ℝ)*(1 + (Real.log (D:ℝ) + 1)/(q:ℝ))
        + 2*((D:ℝ)/(q:ℝ) + 1) * (264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) := by
  classical
  have hkey : ∀ d ∈ Finset.Icc 1 D,
      ‖c d * ∑ m ∈ Finset.Icc 1 (N/d),
        e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
      = 2 * (‖c d * ∑ m ∈ Finset.Icc 1 (N/d),
          e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ / 2) := by
    intro d _
    ring
  rw [Finset.sum_congr rfl hkey, ← Finset.mul_sum]
  have hbound := sum_range_g_le a q hq hcop δ hδ D hD ((N:ℝ)/2)
    (by positivity)
    (fun d => ‖c d * ∑ m ∈ Finset.Icc 1 (N/d),
      e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ / 2)
    (fun d _ => by positivity)
    ?_ ?_
  · have hfin : 2 * (13*((N:ℝ)/2)*(1 + (Real.log (D:ℝ) + 1)/(q:ℝ))
        + ((D:ℝ)/(q:ℝ) + 1) * (264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)))
        = 13*(N:ℝ)*(1 + (Real.log (D:ℝ) + 1)/(q:ℝ))
          + 2*((D:ℝ)/(q:ℝ) + 1)
            * (264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) := by
      ring
    rw [← hfin]
    linarith [hbound]
  · -- the length bound: `‖inner‖ ≤ ⌊N/d⌋ ≤ N/d`
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd0 : (0:ℝ) < (d:ℝ) := by
      exact_mod_cast (by omega : 0 < d)
    have h1 : ‖c d * ∑ m ∈ Finset.Icc 1 (N/d),
        e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
        ≤ ((N/d : ℕ):ℝ) := by
      rw [norm_mul]
      have h2 : ‖∑ m ∈ Finset.Icc 1 (N/d),
          e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ ≤ ((N/d : ℕ):ℝ) := by
        refine le_trans (norm_sum_le _ _) ?_
        have h3 : ∀ m ∈ Finset.Icc 1 (N/d),
            ‖e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ = 1 :=
          fun m _ => norm_e _
        rw [Finset.sum_congr rfl h3, Finset.sum_const, nsmul_eq_mul,
          mul_one, Nat.card_Icc]
        simp
      have h4 := hc d
      have h5 := norm_nonneg (∑ m ∈ Finset.Icc 1 (N/d),
        e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
      nlinarith [h2, h4, h5, norm_nonneg (c d)]
    have h6 : ((N/d : ℕ):ℝ) ≤ (N:ℝ)/(d:ℝ) := Nat.cast_div_le
    have h7 : (N:ℝ)/2/(d:ℝ) = ((N:ℝ)/(d:ℝ))/2 := by
      ring
    rw [h7]
    linarith [h1, h6]
  · -- the Kusmin–Landau bound at positive `nint(dβ)`
    intro d hd hpos
    rw [Finset.mem_Icc] at hd
    rcases Nat.eq_zero_or_pos (N/d) with hnd | hnd
    · show ‖c d * ∑ m ∈ Finset.Icc 1 (N/d),
          e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ / 2
        ≤ 1/(2 * nint ((d:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
      rw [hnd, show Finset.Icc 1 0 = (∅ : Finset ℕ) from
        Finset.Icc_eq_empty (by omega)]
      simp only [Finset.sum_empty, mul_zero, norm_zero, zero_div]
      positivity
    · have hphase : ∀ m ∈ Finset.Ico 1 (N/d + 1),
          e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))
          = e ((m:ℝ) * ((d:ℝ)*((a:ℝ)/(q:ℝ) + δ))) := by
        intro m _
        congr 1
        ring
      have hIcc : Finset.Icc 1 (N/d) = Finset.Ico 1 (N/d + 1) := by
        ext m
        rw [Finset.mem_Icc, Finset.mem_Ico]
        omega
      have hkl := norm_sum_e_linear_le
        (β := (d:ℝ)*((a:ℝ)/(q:ℝ) + δ)) hpos 1 (N/d) hnd
      have hnorm : ‖∑ m ∈ Finset.Icc 1 (N/d),
          e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
          ≤ 1 / nint ((d:ℝ)*((a:ℝ)/(q:ℝ) + δ)) := by
        rw [hIcc, Finset.sum_congr rfl hphase]
        exact hkl
      have h4 := hc d
      have h5 := norm_nonneg (∑ m ∈ Finset.Icc 1 (N/d),
        e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
      have h8 : ‖c d * ∑ m ∈ Finset.Icc 1 (N/d),
          e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
          ≤ 1 / nint ((d:ℝ)*((a:ℝ)/(q:ℝ) + δ)) := by
        rw [norm_mul]
        nlinarith [hnorm, h4, h5, norm_nonneg (c d),
          le_of_lt (one_div_pos.mpr hpos)]
      have h9 : 1/(2 * nint ((d:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
          = (1 / nint ((d:ℝ)*((a:ℝ)/(q:ℝ) + δ)))/2 := by
        rw [div_div]
        ring_nf
      rw [h9]
      linarith [h8]


/-- **The constant-cap counting lemma** (Track R, V4a): the Type II
variant of `sum_range_g_le` — when the cap is a constant `A` rather
than `N/d`, each of the `H/q + 1` blocks pays the same
`13A + 264q(log 8q + 1)`, with no harmonic factor. -/
theorem sum_range_g_const_le (a q : ℕ) (hq : 1 ≤ q)
    (hcop : Nat.Coprime a q) (δ : ℝ) (hδ : |δ| ≤ 1/(q:ℝ)^2) (H : ℕ)
    (A : ℝ) (hA : 0 ≤ A) (g : ℕ → ℝ)
    (hg0 : ∀ h ∈ Finset.Icc 1 H, 0 ≤ g h)
    (hgA : ∀ h ∈ Finset.Icc 1 H, g h ≤ A)
    (hg2 : ∀ h ∈ Finset.Icc 1 H,
      0 < nint ((h:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) →
      g h ≤ 1/(2 * nint ((h:ℝ) * ((a:ℝ)/(q:ℝ) + δ)))) :
    ∑ h ∈ Finset.Icc 1 H, g h
      ≤ ((H:ℝ)/(q:ℝ) + 1)
        * (13*A + 264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) := by
  classical
  have hq0R : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  set g' : ℕ → ℝ := fun h => if h ∈ Finset.Icc 1 H then g h else 0
    with hg'_def
  have hg'0 : ∀ h, 0 ≤ g' h := by
    intro h
    simp only [hg'_def]
    split
    · exact hg0 h (by assumption)
    · exact le_refl 0
  have heqsum : ∑ h ∈ Finset.Icc 1 H, g h
      = ∑ h ∈ Finset.Icc 1 H, g' h := by
    refine Finset.sum_congr rfl fun h hh => ?_
    simp only [hg'_def]
    rw [if_pos hh]
  have hcover : Finset.Icc 1 H ⊆ (Finset.range (H/q + 1)).biUnion
      (fun j => Finset.Ioc (j*q) (j*q + q)) := by
    intro h hh
    rw [Finset.mem_Icc] at hh
    rw [Finset.mem_biUnion]
    refine ⟨(h - 1)/q, ?_, ?_⟩
    · rw [Finset.mem_range]
      have h1 : (h - 1)/q ≤ H/q := Nat.div_le_div_right (by omega)
      omega
    · rw [Finset.mem_Ioc]
      have h2 : (h - 1) % q < q := Nat.mod_lt _ (by omega)
      have h3 : (h - 1)/q * q + (h - 1) % q = h - 1 :=
        Nat.div_add_mod' (h - 1) q
      omega
  have hdisjb : (↑(Finset.range (H/q + 1)) : Set ℕ).PairwiseDisjoint
      (fun j => Finset.Ioc (j*q) (j*q + q)) := by
    intro j hj j' hj' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro d hd hd'
    rw [Finset.mem_Ioc] at hd hd'
    rcases Nat.lt_or_ge j j' with hlt | hge
    · have h1 : (j + 1) * q ≤ j' * q := Nat.mul_le_mul_right q hlt
      have h2 : j*q + q = (j + 1) * q := by ring
      omega
    · have hlt' : j' < j := by omega
      have h1 : (j' + 1) * q ≤ j * q := Nat.mul_le_mul_right q hlt'
      have h2 : j'*q + q = (j' + 1) * q := by ring
      omega
  have hstep1 : ∑ h ∈ Finset.Icc 1 H, g' h
      ≤ ∑ h ∈ (Finset.range (H/q + 1)).biUnion
        (fun j => Finset.Ioc (j*q) (j*q + q)), g' h :=
    Finset.sum_le_sum_of_subset_of_nonneg hcover (fun h _ _ => hg'0 h)
  have hstep2 : ∑ h ∈ (Finset.range (H/q + 1)).biUnion
      (fun j => Finset.Ioc (j*q) (j*q + q)), g' h
      = ∑ j ∈ Finset.range (H/q + 1),
          ∑ h ∈ Finset.Ioc (j*q) (j*q + q), g' h :=
    Finset.sum_biUnion hdisjb
  have hblock : ∀ j ∈ Finset.range (H/q + 1),
      ∑ h ∈ Finset.Ioc (j*q) (j*q + q), g' h
      ≤ 13*A + 264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1) := by
    intro j _
    refine sum_block_g_le a q hq hcop δ hδ j A hA g'
      (fun h _ => hg'0 h) ?_ ?_
    · intro h _
      simp only [hg'_def]
      split
      · exact hgA h (by assumption)
      · exact hA
    · intro h _ hpos
      simp only [hg'_def]
      split
      · exact hg2 h (by assumption) hpos
      · positivity
  have hsum3 : ∑ j ∈ Finset.range (H/q + 1),
      ∑ h ∈ Finset.Ioc (j*q) (j*q + q), g' h
      ≤ ∑ j ∈ Finset.range (H/q + 1),
        (13*A + 264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) :=
    Finset.sum_le_sum hblock
  have hconst : ∑ j ∈ Finset.range (H/q + 1),
      (13*A + 264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1))
      = ((H/q + 1 : ℕ):ℝ)
        * (13*A + 264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hJcast : ((H/q + 1 : ℕ):ℝ) ≤ (H:ℝ)/(q:ℝ) + 1 := by
    have h1 : ((H/q : ℕ):ℝ) ≤ (H:ℝ)/(q:ℝ) := Nat.cast_div_le
    push_cast
    linarith [h1]
  have hC0 : (0:ℝ) ≤ 13*A + 264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1) := by
    have hq1R : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    have h8 : (1:ℝ) ≤ 8*(q:ℝ) := by linarith
    have := Real.log_nonneg h8
    positivity
  rw [heqsum]
  refine le_trans hstep1 ?_
  rw [hstep2]
  refine le_trans hsum3 ?_
  rw [hconst]
  exact mul_le_mul_of_nonneg_right hJcast hC0

end ExpSums

end MoltResearch
