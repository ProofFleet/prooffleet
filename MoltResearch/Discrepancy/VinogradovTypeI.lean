import MoltResearch.Discrepancy.ExpSums
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.DiophantineApproximation.Basic

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


/-- **The pair-to-gap count** (Track R, V4b): a sum of a nonnegative
function of the gap `|n − n'|` over all pairs of a set `K ⊆ [1, KM]`
costs at most `|K|` diagonal terms plus twice the gap-sum — for each
fixed `n`, every positive gap has at most one partner on each side. -/
theorem sum_pairs_gap_le (K : Finset ℕ) (KM : ℕ)
    (hK : K ⊆ Finset.Icc 1 KM) (F : ℕ → ℝ) (hF0 : ∀ h, 0 ≤ F h) :
    ∑ p ∈ K ×ˢ K, F (max p.1 p.2 - min p.1 p.2)
      ≤ (K.card : ℝ) * (F 0 + 2 * ∑ h ∈ Finset.Icc 1 KM, F h) := by
  classical
  rw [Finset.sum_product]
  have hper : ∀ n ∈ K, ∑ n' ∈ K, F (max n n' - min n n')
      ≤ F 0 + 2 * ∑ h ∈ Finset.Icc 1 KM, F h := by
    intro n hn
    have hnKM := hK hn
    rw [Finset.mem_Icc] at hnKM
    have hsplit : K = (K.filter (fun n' => n' = n))
        ∪ (K.filter (fun n' => n' ≠ n)) :=
      (Finset.filter_union_filter_neg_eq _ K).symm
    nth_rewrite 1 [hsplit]
    rw [Finset.sum_union (Finset.disjoint_filter_filter_neg K K _)]
    have hdiag : ∑ n' ∈ K.filter (fun n' => n' = n),
        F (max n n' - min n n') ≤ F 0 := by
      have hsub : K.filter (fun n' => n' = n) ⊆ {n} := by
        intro m hm
        rw [Finset.mem_filter] at hm
        rw [Finset.mem_singleton]
        exact hm.2
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun m _ _ => hF0 _)) ?_
      rw [Finset.sum_singleton]
      simp
    have hgt : ∑ n' ∈ K.filter (fun n' => n < n'),
        F (max n n' - min n n') ≤ ∑ h ∈ Finset.Icc 1 KM, F h := by
      have heq : ∑ n' ∈ K.filter (fun n' => n < n'),
          F (max n n' - min n n')
          = ∑ n' ∈ K.filter (fun n' => n < n'), F (n' - n) := by
        refine Finset.sum_congr rfl fun n' hn' => ?_
        rw [Finset.mem_filter] at hn'
        congr 1
        omega
      have hinj : ∀ x ∈ K.filter (fun n' => n < n'),
          ∀ y ∈ K.filter (fun n' => n < n'),
          x - n = y - n → x = y := by
        intro x hx y hy hxy
        rw [Finset.mem_filter] at hx hy
        omega
      rw [heq, ← Finset.sum_image hinj]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_
        (fun h _ _ => hF0 h)
      intro h hh
      rw [Finset.mem_image] at hh
      obtain ⟨n', hn', rfl⟩ := hh
      rw [Finset.mem_filter] at hn'
      have h1 := hK hn'.1
      rw [Finset.mem_Icc] at h1
      rw [Finset.mem_Icc]
      omega
    have hlt : ∑ n' ∈ K.filter (fun n' => n' < n),
        F (max n n' - min n n') ≤ ∑ h ∈ Finset.Icc 1 KM, F h := by
      have heq : ∑ n' ∈ K.filter (fun n' => n' < n),
          F (max n n' - min n n')
          = ∑ n' ∈ K.filter (fun n' => n' < n), F (n - n') := by
        refine Finset.sum_congr rfl fun n' hn' => ?_
        rw [Finset.mem_filter] at hn'
        congr 1
        omega
      have hinj : ∀ x ∈ K.filter (fun n' => n' < n),
          ∀ y ∈ K.filter (fun n' => n' < n),
          n - x = n - y → x = y := by
        intro x hx y hy hxy
        rw [Finset.mem_filter] at hx hy
        omega
      rw [heq, ← Finset.sum_image hinj]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_
        (fun h _ _ => hF0 h)
      intro h hh
      rw [Finset.mem_image] at hh
      obtain ⟨n', hn', rfl⟩ := hh
      rw [Finset.mem_filter] at hn'
      have h1 := hK hn'.1
      rw [Finset.mem_Icc] at h1
      rw [Finset.mem_Icc]
      omega
    have hoff : ∑ n' ∈ K.filter (fun n' => n' ≠ n),
        F (max n n' - min n n')
        ≤ 2 * ∑ h ∈ Finset.Icc 1 KM, F h := by
      have hsplit2 : K.filter (fun n' => n' ≠ n)
          = (K.filter (fun n' => n < n'))
            ∪ (K.filter (fun n' => n' < n)) := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨hmK, hne⟩
          rcases Nat.lt_or_ge n m with h | h
          · exact Or.inl ⟨hmK, h⟩
          · exact Or.inr ⟨hmK, by omega⟩
        · rintro (⟨hmK, h⟩ | ⟨hmK, h⟩)
          · exact ⟨hmK, by omega⟩
          · exact ⟨hmK, by omega⟩
      have hdisj2 : Disjoint (K.filter (fun n' => n < n'))
          (K.filter (fun n' => n' < n)) := by
        rw [Finset.disjoint_left]
        intro m hm hm'
        rw [Finset.mem_filter] at hm hm'
        omega
      rw [hsplit2, Finset.sum_union hdisj2]
      linarith [hgt, hlt]
    linarith [hdiag, hoff]
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [Finset.sum_const, nsmul_eq_mul]


/-- **The per-pair reduction** (Track R, V4c-i): a conjugate-pair inner
sum of the Type II expansion is bounded by the gap phase sum
`F(|n − n'|) = ‖∑_m e(m·|n−n'|·β)‖` — the coefficient product has unit
norm and `e_mul_conj` subtracts the phases; a negative gap conjugates
the whole sum without changing its norm. -/
theorem norm_pair_sum_le_gap (β : ℝ) (M₁ M₂ : ℕ) (bn : ℕ → ℂ)
    (hbn : ∀ n, ‖bn n‖ ≤ 1) (n n' : ℕ) :
    ‖∑ m ∈ Finset.Ico M₁ M₂,
        (bn n * e ((m:ℝ)*(n:ℝ)*β))
          * (starRingEnd ℂ) (bn n' * e ((m:ℝ)*(n':ℝ)*β))‖
      ≤ ‖∑ m ∈ Finset.Ico M₁ M₂,
          e ((m:ℝ)*((max n n' - min n n' : ℕ):ℝ)*β)‖ := by
  classical
  have hfactor : ∀ m : ℕ,
      (bn n * e ((m:ℝ)*(n:ℝ)*β))
        * (starRingEnd ℂ) (bn n' * e ((m:ℝ)*(n':ℝ)*β))
      = (bn n * (starRingEnd ℂ) (bn n'))
        * e ((m:ℝ)*((n:ℝ) - (n':ℝ))*β) := by
    intro m
    have he := e_mul_conj ((m:ℝ)*(n:ℝ)*β) ((m:ℝ)*(n':ℝ)*β)
    have harg : (m:ℝ)*(n:ℝ)*β - (m:ℝ)*(n':ℝ)*β
        = (m:ℝ)*((n:ℝ) - (n':ℝ))*β := by
      ring
    rw [harg] at he
    rw [map_mul, mul_mul_mul_comm, he]
  rw [Finset.sum_congr rfl (fun m _ => hfactor m), ← Finset.mul_sum,
    norm_mul]
  have hb1 : ‖bn n * (starRingEnd ℂ) (bn n')‖ ≤ 1 := by
    rw [norm_mul, RCLike.norm_conj]
    have h1 := hbn n
    have h2 := hbn n'
    nlinarith [norm_nonneg (bn n), norm_nonneg (bn n')]
  have hnn : ‖∑ m ∈ Finset.Ico M₁ M₂, e ((m:ℝ)*((n:ℝ) - (n':ℝ))*β)‖
      = ‖∑ m ∈ Finset.Ico M₁ M₂,
          e ((m:ℝ)*((max n n' - min n n' : ℕ):ℝ)*β)‖ := by
    rcases le_or_gt n' n with hle | hgt
    · have hcast : (n:ℝ) - (n':ℝ) = ((n - n' : ℕ):ℝ) := by
        have : ((n - n' : ℕ):ℝ) = (n:ℝ) - (n':ℝ) := by
          push_cast [hle]
          ring
        linarith [this.le, this.ge]
      have hmm : max n n' - min n n' = n - n' := by
        omega
      rw [hcast, hmm]
    · have hmm : max n n' - min n n' = n' - n := by
        omega
      have hcast : (n:ℝ) - (n':ℝ) = -(((n' - n : ℕ)):ℝ) := by
        have : ((n' - n : ℕ):ℝ) = (n':ℝ) - (n:ℝ) := by
          push_cast [le_of_lt hgt]
          ring
        linarith [this.le, this.ge]
      rw [hcast, hmm]
      rw [← RCLike.norm_conj (∑ m ∈ Finset.Ico M₁ M₂,
        e ((m:ℝ)*(-(((n' - n : ℕ)):ℝ))*β)), map_sum]
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [e_conj]
      congr 1
      ring
  rw [hnn]
  have h0 := norm_nonneg (∑ m ∈ Finset.Ico M₁ M₂,
    e ((m:ℝ)*((max n n' - min n n' : ℕ):ℝ)*β))
  nlinarith [hb1, h0, norm_nonneg (bn n * (starRingEnd ℂ) (bn n'))]


/-- **The Type II bilinear estimate** (Track R, V4c-ii): for unit
coefficient sequences and `β = a/q + δ` with `gcd(a,q) = 1`,
`|δ| ≤ 1/q²`, the squared bilinear sum over `m ∈ [M₁, M₂)`, `n ∈ K ⊆
[1, KM]` is bounded by Cauchy–Schwarz (in `m`), the conjugate-pair
expansion, the pair-to-gap collapse, and the constant-cap counting
lemma at the gap frequencies. -/
theorem typeII_sum_sq_le (a q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime a q)
    (δ : ℝ) (hδ : |δ| ≤ 1/(q:ℝ)^2) (M₁ M₂ KM : ℕ)
    (K : Finset ℕ) (hK : K ⊆ Finset.Icc 1 KM)
    (am bn : ℕ → ℂ) (ham : ∀ m, ‖am m‖ ≤ 1) (hbn : ∀ n, ‖bn n‖ ≤ 1) :
    ‖∑ m ∈ Finset.Ico M₁ M₂,
        am m * ∑ n ∈ K, bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖^2
      ≤ ((M₂ - M₁ : ℕ):ℝ) * ((K.card:ℝ)
          * (((M₂ - M₁ : ℕ):ℝ)
            + 2*(((KM:ℝ)/(q:ℝ) + 1)
              *(13*((M₂ - M₁ : ℕ):ℝ)
                + 528*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1))))) := by
  classical
  have hMc : ((Finset.Ico M₁ M₂).card : ℝ) = ((M₂ - M₁ : ℕ):ℝ) := by
    rw [Nat.card_Ico]
  -- the trivial length bound on the gap phase sums
  have hFtriv : ∀ h : ℕ,
      ‖∑ m ∈ Finset.Ico M₁ M₂,
        e ((m:ℝ)*(h:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ ≤ ((M₂ - M₁ : ℕ):ℝ) := by
    intro h
    refine le_trans (norm_sum_le _ _) ?_
    have h1 : ∀ m ∈ Finset.Ico M₁ M₂,
        ‖e ((m:ℝ)*(h:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ = 1 := fun m _ => norm_e _
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one,
      Nat.card_Ico]
  -- Step 1: Cauchy–Schwarz in `m`, coefficients dropped
  have hcs := norm_sum_sq_le_card_mul (Finset.Ico M₁ M₂)
    (fun m => am m * ∑ n ∈ K, bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
  have hstep1 : ∑ m ∈ Finset.Ico M₁ M₂,
      ‖am m * ∑ n ∈ K, bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖^2
      ≤ ∑ m ∈ Finset.Ico M₁ M₂,
        ‖∑ n ∈ K, bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖^2 := by
    refine Finset.sum_le_sum fun m _ => ?_
    rw [norm_mul, mul_pow]
    have h1 := ham m
    have h2 := norm_nonneg (am m)
    have h3 := sq_nonneg ‖∑ n ∈ K,
      bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
    have h4 : ‖am m‖^2 ≤ 1 := by nlinarith [h1, h2]
    nlinarith [h4, h3]
  -- Step 2: conjugate-pair expansion
  have hexp := sum_norm_sq_expand (Finset.Ico M₁ M₂) K
    (fun m n => bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
  -- Step 3: per-pair reduction to the gap phase
  have hstep3 : ∑ p ∈ K ×ˢ K,
      ‖∑ m ∈ Finset.Ico M₁ M₂,
        (bn p.1 * e ((m:ℝ)*(p.1:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
          * (starRingEnd ℂ)
            (bn p.2 * e ((m:ℝ)*(p.2:ℝ)*((a:ℝ)/(q:ℝ) + δ)))‖
      ≤ ∑ p ∈ K ×ˢ K,
        ‖∑ m ∈ Finset.Ico M₁ M₂,
          e ((m:ℝ)*((max p.1 p.2 - min p.1 p.2 : ℕ):ℝ)
            *((a:ℝ)/(q:ℝ) + δ))‖ :=
    Finset.sum_le_sum fun p _ =>
      norm_pair_sum_le_gap ((a:ℝ)/(q:ℝ) + δ) M₁ M₂ bn hbn p.1 p.2
  -- Step 4: pairs collapse to gaps
  have hgap := sum_pairs_gap_le K KM hK
    (fun h => ‖∑ m ∈ Finset.Ico M₁ M₂,
      e ((m:ℝ)*(h:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖)
    (fun h => norm_nonneg _)
  -- Step 5: the zero gap is the full length
  have hF0 : ‖∑ m ∈ Finset.Ico M₁ M₂,
      e ((m:ℝ)*((0:ℕ):ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ = ((M₂ - M₁ : ℕ):ℝ) := by
    have h1 : ∀ m ∈ Finset.Ico M₁ M₂,
        e ((m:ℝ)*((0:ℕ):ℝ)*((a:ℝ)/(q:ℝ) + δ)) = 1 := by
      intro m _
      have h2 : (m:ℝ)*((0:ℕ):ℝ)*((a:ℝ)/(q:ℝ) + δ) = ((0:ℤ):ℝ) := by
        push_cast
        ring
      rw [h2, e_intCast]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Nat.card_Ico]
    simp
  -- Step 6: the gap-frequency sum via the constant-cap counting lemma
  have hFsum : ∑ h ∈ Finset.Icc 1 KM,
      ‖∑ m ∈ Finset.Ico M₁ M₂,
        e ((m:ℝ)*(h:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
      ≤ ((KM:ℝ)/(q:ℝ) + 1) * (13*((M₂ - M₁ : ℕ):ℝ)
          + 528*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) := by
    have hhalf : ∑ h ∈ Finset.Icc 1 KM,
        ‖∑ m ∈ Finset.Ico M₁ M₂,
          e ((m:ℝ)*(h:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
        = 2 * ∑ h ∈ Finset.Icc 1 KM,
          (‖∑ m ∈ Finset.Ico M₁ M₂,
            e ((m:ℝ)*(h:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ / 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      ring
    have hcc := sum_range_g_const_le a q hq hcop δ hδ KM
      (((M₂ - M₁ : ℕ):ℝ)/2) (by positivity)
      (fun h => ‖∑ m ∈ Finset.Ico M₁ M₂,
        e ((m:ℝ)*(h:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ / 2)
      (fun h _ => by positivity)
      (fun h _ => by
        have := hFtriv h
        linarith)
      ?_
    · rw [hhalf]
      have hring : 2*(((KM:ℝ)/(q:ℝ) + 1)
          *(13*(((M₂ - M₁ : ℕ):ℝ)/2)
            + 264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)))
          = ((KM:ℝ)/(q:ℝ) + 1) * (13*((M₂ - M₁ : ℕ):ℝ)
            + 528*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) := by
        ring
      linarith [hcc, hring.le, hring.ge]
    · intro h hh hpos
      rcases Nat.lt_or_ge M₁ M₂ with hM | hM
      · have hM2 : M₂ = (M₂ - 1) + 1 := by omega
        have hphase : ∀ m ∈ Finset.Ico M₁ ((M₂ - 1) + 1),
            e ((m:ℝ)*(h:ℝ)*((a:ℝ)/(q:ℝ) + δ))
            = e ((m:ℝ) * ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ))) := by
          intro m _
          congr 1
          ring
        have hkl := norm_sum_e_linear_le
          (β := (h:ℝ)*((a:ℝ)/(q:ℝ) + δ)) hpos M₁ (M₂ - 1) (by omega)
        have hb : ‖∑ m ∈ Finset.Ico M₁ M₂,
            e ((m:ℝ)*(h:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
            ≤ 1 / nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ)) := by
          rw [hM2, Finset.sum_congr rfl hphase]
          exact hkl
        have hd : 1/(2 * nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
            = (1 / nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ)))/2 := by
          rw [div_div]
          ring_nf
        rw [hd]
        linarith [hb]
      · have hempty : Finset.Ico M₁ M₂ = ∅ :=
          Finset.Ico_eq_empty (by omega)
        rw [hempty]
        simp only [Finset.sum_empty, norm_zero, zero_div]
        positivity
  -- assemble
  have hKc0 : (0:ℝ) ≤ (K.card:ℝ) := Nat.cast_nonneg _
  have hMc0 : (0:ℝ) ≤ ((M₂ - M₁ : ℕ):ℝ) := Nat.cast_nonneg _
  have hchain1 : ‖∑ m ∈ Finset.Ico M₁ M₂,
      am m * ∑ n ∈ K, bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖^2
      ≤ ((M₂ - M₁ : ℕ):ℝ) * ∑ p ∈ K ×ˢ K,
        ‖∑ m ∈ Finset.Ico M₁ M₂,
          e ((m:ℝ)*((max p.1 p.2 - min p.1 p.2 : ℕ):ℝ)
            *((a:ℝ)/(q:ℝ) + δ))‖ := by
    rw [← hMc]
    have hcm0 : (0:ℝ) ≤ ((Finset.Ico M₁ M₂).card : ℝ) := Nat.cast_nonneg _
    calc ‖∑ m ∈ Finset.Ico M₁ M₂,
        am m * ∑ n ∈ K, bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖^2
        ≤ ((Finset.Ico M₁ M₂).card : ℝ) * ∑ m ∈ Finset.Ico M₁ M₂,
            ‖am m * ∑ n ∈ K,
              bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖^2 := hcs
      _ ≤ ((Finset.Ico M₁ M₂).card : ℝ) * ∑ m ∈ Finset.Ico M₁ M₂,
            ‖∑ n ∈ K,
              bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖^2 :=
          mul_le_mul_of_nonneg_left hstep1 hcm0
      _ ≤ ((Finset.Ico M₁ M₂).card : ℝ) * ∑ p ∈ K ×ˢ K,
            ‖∑ m ∈ Finset.Ico M₁ M₂,
              (bn p.1 * e ((m:ℝ)*(p.1:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
                * (starRingEnd ℂ)
                  (bn p.2 * e ((m:ℝ)*(p.2:ℝ)*((a:ℝ)/(q:ℝ) + δ)))‖ :=
          mul_le_mul_of_nonneg_left hexp hcm0
      _ ≤ ((Finset.Ico M₁ M₂).card : ℝ) * ∑ p ∈ K ×ˢ K,
            ‖∑ m ∈ Finset.Ico M₁ M₂,
              e ((m:ℝ)*((max p.1 p.2 - min p.1 p.2 : ℕ):ℝ)
                *((a:ℝ)/(q:ℝ) + δ))‖ :=
          mul_le_mul_of_nonneg_left hstep3 hcm0
  refine le_trans hchain1 ?_
  refine mul_le_mul_of_nonneg_left ?_ hMc0
  refine le_trans hgap ?_
  refine mul_le_mul_of_nonneg_left ?_ hKc0
  simp only []
  rw [hF0]
  have h2S : 2 * (∑ h ∈ Finset.Icc 1 KM,
      ‖∑ m ∈ Finset.Ico M₁ M₂,
        e ((m:ℝ)*(h:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖)
      ≤ 2 * (((KM:ℝ)/(q:ℝ) + 1) * (13*((M₂ - M₁ : ℕ):ℝ)
          + 528*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1))) := by
    linarith [hFsum]
  linarith [h2S]


/-- **The inner-mass bound** (Track R, V5a-i): the `m`-mean square of
the `K`-polynomials — steps 2–6 of the Type II argument, factored out
so both the unit-coefficient and `ℓ²`-coefficient forms consume it. -/
theorem sum_inner_sq_le (a q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime a q)
    (δ : ℝ) (hδ : |δ| ≤ 1/(q:ℝ)^2) (M₁ M₂ KM : ℕ)
    (K : Finset ℕ) (hK : K ⊆ Finset.Icc 1 KM)
    (bn : ℕ → ℂ) (hbn : ∀ n, ‖bn n‖ ≤ 1) :
    ∑ m ∈ Finset.Ico M₁ M₂,
      ‖∑ n ∈ K, bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖^2
      ≤ (K.card:ℝ) * (((M₂ - M₁ : ℕ):ℝ)
          + 2*(((KM:ℝ)/(q:ℝ) + 1)
            *(13*((M₂ - M₁ : ℕ):ℝ)
              + 528*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)))) := by
  classical
  have hFtriv : ∀ h : ℕ,
      ‖∑ m ∈ Finset.Ico M₁ M₂,
        e ((m:ℝ)*(h:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ ≤ ((M₂ - M₁ : ℕ):ℝ) := by
    intro h
    refine le_trans (norm_sum_le _ _) ?_
    have h1 : ∀ m ∈ Finset.Ico M₁ M₂,
        ‖e ((m:ℝ)*(h:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ = 1 := fun m _ => norm_e _
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one,
      Nat.card_Ico]
  have hexp := sum_norm_sq_expand (Finset.Ico M₁ M₂) K
    (fun m n => bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
  have hstep3 : ∑ p ∈ K ×ˢ K,
      ‖∑ m ∈ Finset.Ico M₁ M₂,
        (bn p.1 * e ((m:ℝ)*(p.1:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
          * (starRingEnd ℂ)
            (bn p.2 * e ((m:ℝ)*(p.2:ℝ)*((a:ℝ)/(q:ℝ) + δ)))‖
      ≤ ∑ p ∈ K ×ˢ K,
        ‖∑ m ∈ Finset.Ico M₁ M₂,
          e ((m:ℝ)*((max p.1 p.2 - min p.1 p.2 : ℕ):ℝ)
            *((a:ℝ)/(q:ℝ) + δ))‖ :=
    Finset.sum_le_sum fun p _ =>
      norm_pair_sum_le_gap ((a:ℝ)/(q:ℝ) + δ) M₁ M₂ bn hbn p.1 p.2
  have hgap := sum_pairs_gap_le K KM hK
    (fun h => ‖∑ m ∈ Finset.Ico M₁ M₂,
      e ((m:ℝ)*(h:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖)
    (fun h => norm_nonneg _)
  have hF0 : ‖∑ m ∈ Finset.Ico M₁ M₂,
      e ((m:ℝ)*((0:ℕ):ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ = ((M₂ - M₁ : ℕ):ℝ) := by
    have h1 : ∀ m ∈ Finset.Ico M₁ M₂,
        e ((m:ℝ)*((0:ℕ):ℝ)*((a:ℝ)/(q:ℝ) + δ)) = 1 := by
      intro m _
      have h2 : (m:ℝ)*((0:ℕ):ℝ)*((a:ℝ)/(q:ℝ) + δ) = ((0:ℤ):ℝ) := by
        push_cast
        ring
      rw [h2, e_intCast]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Nat.card_Ico]
    simp
  have hFsum : ∑ h ∈ Finset.Icc 1 KM,
      ‖∑ m ∈ Finset.Ico M₁ M₂,
        e ((m:ℝ)*(h:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
      ≤ ((KM:ℝ)/(q:ℝ) + 1) * (13*((M₂ - M₁ : ℕ):ℝ)
          + 528*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) := by
    have hhalf : ∑ h ∈ Finset.Icc 1 KM,
        ‖∑ m ∈ Finset.Ico M₁ M₂,
          e ((m:ℝ)*(h:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
        = 2 * ∑ h ∈ Finset.Icc 1 KM,
          (‖∑ m ∈ Finset.Ico M₁ M₂,
            e ((m:ℝ)*(h:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ / 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      ring
    have hcc := sum_range_g_const_le a q hq hcop δ hδ KM
      (((M₂ - M₁ : ℕ):ℝ)/2) (by positivity)
      (fun h => ‖∑ m ∈ Finset.Ico M₁ M₂,
        e ((m:ℝ)*(h:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ / 2)
      (fun h _ => by positivity)
      (fun h _ => by
        have := hFtriv h
        linarith)
      ?_
    · rw [hhalf]
      have hring : 2*(((KM:ℝ)/(q:ℝ) + 1)
          *(13*(((M₂ - M₁ : ℕ):ℝ)/2)
            + 264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)))
          = ((KM:ℝ)/(q:ℝ) + 1) * (13*((M₂ - M₁ : ℕ):ℝ)
            + 528*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) := by
        ring
      linarith [hcc, hring.le, hring.ge]
    · intro h hh hpos
      rcases Nat.lt_or_ge M₁ M₂ with hM | hM
      · have hM2 : M₂ = (M₂ - 1) + 1 := by omega
        have hphase : ∀ m ∈ Finset.Ico M₁ ((M₂ - 1) + 1),
            e ((m:ℝ)*(h:ℝ)*((a:ℝ)/(q:ℝ) + δ))
            = e ((m:ℝ) * ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ))) := by
          intro m _
          congr 1
          ring
        have hkl := norm_sum_e_linear_le
          (β := (h:ℝ)*((a:ℝ)/(q:ℝ) + δ)) hpos M₁ (M₂ - 1) (by omega)
        have hb : ‖∑ m ∈ Finset.Ico M₁ M₂,
            e ((m:ℝ)*(h:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
            ≤ 1 / nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ)) := by
          rw [hM2, Finset.sum_congr rfl hphase]
          exact hkl
        have hd : 1/(2 * nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
            = (1 / nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ)))/2 := by
          rw [div_div]
          ring_nf
        rw [hd]
        linarith [hb]
      · have hempty : Finset.Ico M₁ M₂ = ∅ :=
          Finset.Ico_eq_empty (by omega)
        rw [hempty]
        simp only [Finset.sum_empty, norm_zero, zero_div]
        positivity
  have hKc0 : (0:ℝ) ≤ (K.card:ℝ) := Nat.cast_nonneg _
  refine le_trans hexp ?_
  refine le_trans hstep3 ?_
  refine le_trans hgap ?_
  refine mul_le_mul_of_nonneg_left ?_ hKc0
  simp only []
  rw [hF0]
  linarith [hFsum]

/-- **The `ℓ²`-coefficient Type II estimate** (Track R, V5a-ii): the
form Vaughan's identity needs — the `m`-coefficients enter only through
their square mass, so Möbius partial sums (bounded by the divisor
function, not by `1`) are admissible. -/
theorem typeII_sum_sq_le' (a q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime a q)
    (δ : ℝ) (hδ : |δ| ≤ 1/(q:ℝ)^2) (M₁ M₂ KM : ℕ)
    (K : Finset ℕ) (hK : K ⊆ Finset.Icc 1 KM)
    (am bn : ℕ → ℂ) (hbn : ∀ n, ‖bn n‖ ≤ 1) :
    ‖∑ m ∈ Finset.Ico M₁ M₂,
        am m * ∑ n ∈ K, bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖^2
      ≤ (∑ m ∈ Finset.Ico M₁ M₂, ‖am m‖^2)
        * ((K.card:ℝ) * (((M₂ - M₁ : ℕ):ℝ)
          + 2*(((KM:ℝ)/(q:ℝ) + 1)
            *(13*((M₂ - M₁ : ℕ):ℝ)
              + 528*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1))))) := by
  classical
  have hcs : ‖∑ m ∈ Finset.Ico M₁ M₂,
      am m * ∑ n ∈ K, bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖^2
      ≤ (∑ m ∈ Finset.Ico M₁ M₂, ‖am m‖^2)
        * ∑ m ∈ Finset.Ico M₁ M₂,
          ‖∑ n ∈ K, bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖^2 := by
    have h1 : ‖∑ m ∈ Finset.Ico M₁ M₂,
        am m * ∑ n ∈ K, bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
        ≤ ∑ m ∈ Finset.Ico M₁ M₂,
          ‖am m‖ * ‖∑ n ∈ K,
            bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ := by
      refine le_trans (norm_sum_le _ _) ?_
      refine Finset.sum_le_sum fun m _ => ?_
      rw [norm_mul]
    have h2 := sum_mul_sq_le_sq_mul_sq (Finset.Ico M₁ M₂)
      (fun m => ‖am m‖)
      (fun m => ‖∑ n ∈ K, bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖)
    have h3 : (0:ℝ) ≤ ∑ m ∈ Finset.Ico M₁ M₂,
        ‖am m‖ * ‖∑ n ∈ K,
          bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ :=
      Finset.sum_nonneg fun m _ =>
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc ‖∑ m ∈ Finset.Ico M₁ M₂,
        am m * ∑ n ∈ K, bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖^2
        ≤ (∑ m ∈ Finset.Ico M₁ M₂,
            ‖am m‖ * ‖∑ n ∈ K,
              bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖)^2 := by
          nlinarith [h1, norm_nonneg (∑ m ∈ Finset.Ico M₁ M₂,
            am m * ∑ n ∈ K,
              bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))), h3]
      _ ≤ (∑ m ∈ Finset.Ico M₁ M₂, ‖am m‖^2)
          * ∑ m ∈ Finset.Ico M₁ M₂,
            ‖∑ n ∈ K, bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖^2 :=
          h2
  refine le_trans hcs ?_
  refine mul_le_mul_of_nonneg_left ?_ ?_
  · exact sum_inner_sq_le a q hq hcop δ hδ M₁ M₂ KM K hK bn hbn
  · exact Finset.sum_nonneg fun m _ => sq_nonneg _


/-- **The divisor-pair double count** (Track R, V5b-i-a): the mean
square of the divisor function is a lattice count —
`∑_{m ≤ M} τ(m)² ≤ ∑_{a,b ≤ M} M/lcm(a,b)`: expand `τ(m)²` as the
divisor pairs of `m`, swap the order, and count multiples of each
pair's lcm. -/
theorem sum_tau_sq_le_lcm_sum (M : ℕ) (hM : 1 ≤ M) :
    ∑ m ∈ Finset.Icc 1 M, ((m.divisors.card : ℝ))^2
      ≤ ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
          (M:ℝ)/(Nat.lcm p.1 p.2 : ℝ) := by
  classical
  have hdiv_eq : ∀ m ∈ Finset.Icc 1 M,
      m.divisors = (Finset.Icc 1 M).filter (· ∣ m) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    ext d
    rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hd, hm0⟩
      have h1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (by
        rintro rfl
        exact hm0 (Nat.eq_zero_of_zero_dvd hd))
      have h2 : d ≤ m := Nat.le_of_dvd (by omega) hd
      exact ⟨⟨h1, by omega⟩, hd⟩
    · rintro ⟨-, hd⟩
      exact ⟨hd, by omega⟩
  have hper : ∀ m ∈ Finset.Icc 1 M, ((m.divisors.card : ℝ))^2
      = ((((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter
          (fun p => p.1 ∣ m ∧ p.2 ∣ m)).card : ℝ) := by
    intro m hm
    have h1 : ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter
        (fun p => p.1 ∣ m ∧ p.2 ∣ m)
        = ((Finset.Icc 1 M).filter (· ∣ m))
          ×ˢ ((Finset.Icc 1 M).filter (· ∣ m)) :=
      Finset.filter_product (· ∣ m) (· ∣ m)
    rw [h1, Finset.card_product, ← hdiv_eq m hm]
    push_cast
    ring
  rw [Finset.sum_congr rfl hper]
  have hswap : ∑ m ∈ Finset.Icc 1 M,
      ((((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter
        (fun p => p.1 ∣ m ∧ p.2 ∣ m)).card : ℝ)
      = ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        (((Finset.Icc 1 M).filter
          (fun m => p.1 ∣ m ∧ p.2 ∣ m)).card : ℝ) := by
    have h1 : ∀ m ∈ Finset.Icc 1 M,
        ((((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter
          (fun p => p.1 ∣ m ∧ p.2 ∣ m)).card : ℝ)
        = ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
          (if p.1 ∣ m ∧ p.2 ∣ m then (1:ℝ) else 0) := by
      intro m _
      rw [Finset.sum_boole]
    have h2 : ∀ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        (((Finset.Icc 1 M).filter
          (fun m => p.1 ∣ m ∧ p.2 ∣ m)).card : ℝ)
        = ∑ m ∈ Finset.Icc 1 M,
          (if p.1 ∣ m ∧ p.2 ∣ m then (1:ℝ) else 0) := by
      intro p _
      rw [Finset.sum_boole]
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
    exact Finset.sum_comm
  rw [hswap]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
  have hlcm_pos : 0 < Nat.lcm p.1 p.2 :=
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))
  have hIoc : Finset.Icc 1 M = Finset.Ioc 0 M := by
    ext x
    rw [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hpred : (Finset.Icc 1 M).filter (fun m => p.1 ∣ m ∧ p.2 ∣ m)
      = (Finset.Ioc 0 M).filter (fun m => Nat.lcm p.1 p.2 ∣ m) := by
    rw [hIoc]
    refine Finset.filter_congr fun m _ => ?_
    rw [Nat.lcm_dvd_iff]
  rw [hpred, Nat.Ioc_filter_dvd_card_eq_div]
  have h3 : ((M / Nat.lcm p.1 p.2 : ℕ):ℝ)
      ≤ (M:ℝ)/(Nat.lcm p.1 p.2 : ℝ) := Nat.cast_div_le
  exact h3


/-- **The lcm lattice sum** (Track R, V5b-i-b): grouping by the gcd,
`∑_{a,b ≤ M} M/lcm(a,b) ≤ M(1 + log M)³` — each gcd class contributes
`M·g` times the square of a multiples-harmonic sum `(1/g)(1 + log M)`,
and the class sum is one more harmonic factor. -/
theorem lcm_sum_le (M : ℕ) (hM : 1 ≤ M) :
    ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        (M:ℝ)/(Nat.lcm p.1 p.2 : ℝ)
      ≤ (M:ℝ) * (1 + Real.log (M:ℝ))^3 := by
  classical
  have hlogM0 : (0:ℝ) ≤ Real.log (M:ℝ) := Real.log_natCast_nonneg M
  -- the multiples-harmonic bound, per gcd class
  have hmult : ∀ g ∈ Finset.Icc 1 M,
      ∑ x ∈ (Finset.Icc 1 M).filter (g ∣ ·), (1:ℝ)/(x:ℝ)
      ≤ (1/(g:ℝ)) * (1 + Real.log (M:ℝ)) := by
    intro g hg
    rw [Finset.mem_Icc] at hg
    have hg0R : (0:ℝ) < (g:ℝ) := by exact_mod_cast hg.1
    have himg : (Finset.Icc 1 (M/g)).image (fun a' => g * a')
        = (Finset.Icc 1 M).filter (g ∣ ·) := by
      ext x
      rw [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨a', ha', rfl⟩
        rw [Finset.mem_Icc] at ha'
        have h1 : g * a' ≤ g * (M/g) := Nat.mul_le_mul_left g ha'.2
        have h2 : g * (M/g) ≤ M := Nat.mul_div_le M g
        exact ⟨⟨by nlinarith [hg.1, ha'.1], by omega⟩, ⟨a', rfl⟩⟩
      · rintro ⟨⟨hx1, hxM⟩, a', rfl⟩
        refine ⟨a', ?_, rfl⟩
        rw [Finset.mem_Icc]
        constructor
        · by_contra hc
          push_neg at hc
          have ha0 : a' = 0 := Nat.lt_one_iff.mp hc
          rw [ha0, Nat.mul_zero] at hx1
          omega
        · have h1 : a' ≤ (g * a')/g := by
            rw [Nat.mul_div_cancel_left a' (by omega)]
          have h2 : (g * a')/g ≤ M/g := Nat.div_le_div_right hxM
          omega
    have hinj : Set.InjOn (fun a' => g * a')
        ↑(Finset.Icc 1 (M/g)) := by
      intro x _ y _ h
      exact Nat.eq_of_mul_eq_mul_left (by omega) h
    rw [← himg, Finset.sum_image hinj]
    have hterm : ∀ a' ∈ Finset.Icc 1 (M/g),
        (1:ℝ)/((g * a' : ℕ):ℝ) = (1/(g:ℝ)) * ((1:ℝ)/(a':ℝ)) := by
      intro a' ha'
      rw [Finset.mem_Icc] at ha'
      have ha'0 : (0:ℝ) < (a':ℝ) := by exact_mod_cast ha'.1
      push_cast
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hMg1 : 1 ≤ M/g := (Nat.one_le_div_iff (by omega)).mpr hg.2
    have hharm := sum_inv_le_log (M/g) hMg1
    have hlogle : Real.log ((M/g : ℕ):ℝ) ≤ Real.log (M:ℝ) := by
      refine Real.log_le_log ?_ ?_
      · exact_mod_cast hMg1
      · exact_mod_cast Nat.div_le_self M g
    have h3 : ∑ k ∈ Finset.Icc 1 (M/g), (1:ℝ)/(k:ℝ)
        ≤ 1 + Real.log (M:ℝ) := by
      linarith [hharm, hlogle]
    refine mul_le_mul_of_nonneg_left h3 ?_
    positivity
  -- rewrite each term by `gcd·lcm = a·b` and group by the gcd
  have hper : ∀ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
      (M:ℝ)/(Nat.lcm p.1 p.2 : ℝ)
      = (M:ℝ) * (Nat.gcd p.1 p.2 : ℝ)
        * ((1:ℝ)/(p.1:ℝ) * ((1:ℝ)/(p.2:ℝ))) := by
    intro p hp
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    have h1 : (Nat.gcd p.1 p.2 : ℝ) * (Nat.lcm p.1 p.2 : ℝ)
        = (p.1:ℝ) * (p.2:ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n:ℝ))
        (Nat.gcd_mul_lcm p.1 p.2)
    have hp10 : (0:ℝ) < (p.1:ℝ) := by exact_mod_cast (by omega : 0 < p.1)
    have hp20 : (0:ℝ) < (p.2:ℝ) := by exact_mod_cast (by omega : 0 < p.2)
    have hlcm0 : (0:ℝ) < (Nat.lcm p.1 p.2 : ℝ) := by
      have hl : 0 < Nat.lcm p.1 p.2 := Nat.pos_of_ne_zero (by
        intro hc
        rw [Nat.lcm_eq_zero_iff] at hc
        omega)
      exact_mod_cast hl
    have hgcd0 : (0:ℝ) < (Nat.gcd p.1 p.2 : ℝ) := by
      have hgz : 0 < Nat.gcd p.1 p.2 := Nat.pos_of_ne_zero (by
        intro hc
        rw [Nat.gcd_eq_zero_iff] at hc
        omega)
      exact_mod_cast hgz
    field_simp
    nlinarith [h1]
  rw [Finset.sum_congr rfl hper]
  have hmaps : ∀ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
      Nat.gcd p.1 p.2 ∈ Finset.Icc 1 M := by
    intro p hp
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    rw [Finset.mem_Icc]
    have h1 : 0 < Nat.gcd p.1 p.2 := Nat.pos_of_ne_zero (by
      intro hc
      rw [Nat.gcd_eq_zero_iff] at hc
      omega)
    have h2 : Nat.gcd p.1 p.2 ≤ p.1 := Nat.gcd_le_left _ (by omega)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfiber : ∀ g ∈ Finset.Icc 1 M,
      ∑ p ∈ ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter
        (fun p => Nat.gcd p.1 p.2 = g),
        (M:ℝ) * (Nat.gcd p.1 p.2 : ℝ)
          * ((1:ℝ)/(p.1:ℝ) * ((1:ℝ)/(p.2:ℝ)))
      ≤ (M:ℝ) * (1 + Real.log (M:ℝ))^2 * (1/(g:ℝ)) := by
    intro g hg
    rw [Finset.mem_Icc] at hg
    have hg0R : (0:ℝ) < (g:ℝ) := by exact_mod_cast hg.1
    have hsub : ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter
        (fun p => Nat.gcd p.1 p.2 = g)
        ⊆ ((Finset.Icc 1 M).filter (g ∣ ·))
          ×ˢ ((Finset.Icc 1 M).filter (g ∣ ·)) := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨h1, h2⟩, h3⟩ := hp
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
      exact ⟨⟨h1, h3 ▸ Nat.gcd_dvd_left p.1 p.2⟩,
        ⟨h2, h3 ▸ Nat.gcd_dvd_right p.1 p.2⟩⟩
    have hstep : ∑ p ∈ ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter
        (fun p => Nat.gcd p.1 p.2 = g),
        (M:ℝ) * (Nat.gcd p.1 p.2 : ℝ)
          * ((1:ℝ)/(p.1:ℝ) * ((1:ℝ)/(p.2:ℝ)))
        = ∑ p ∈ ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter
          (fun p => Nat.gcd p.1 p.2 = g),
          (M:ℝ) * (g:ℝ) * ((1:ℝ)/(p.1:ℝ) * ((1:ℝ)/(p.2:ℝ))) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.mem_filter] at hp
      rw [hp.2]
    rw [hstep]
    have hmono : ∑ p ∈ ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter
        (fun p => Nat.gcd p.1 p.2 = g),
        (M:ℝ) * (g:ℝ) * ((1:ℝ)/(p.1:ℝ) * ((1:ℝ)/(p.2:ℝ)))
        ≤ ∑ p ∈ ((Finset.Icc 1 M).filter (g ∣ ·))
          ×ˢ ((Finset.Icc 1 M).filter (g ∣ ·)),
          (M:ℝ) * (g:ℝ) * ((1:ℝ)/(p.1:ℝ) * ((1:ℝ)/(p.2:ℝ))) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
      intro p _ _
      positivity
    refine le_trans hmono ?_
    rw [Finset.sum_product]
    have hfact : ∑ x ∈ (Finset.Icc 1 M).filter (g ∣ ·),
        ∑ y ∈ (Finset.Icc 1 M).filter (g ∣ ·),
          (M:ℝ) * (g:ℝ) * ((1:ℝ)/(x:ℝ) * ((1:ℝ)/(y:ℝ)))
        = (M:ℝ) * (g:ℝ)
          * ((∑ x ∈ (Finset.Icc 1 M).filter (g ∣ ·), (1:ℝ)/(x:ℝ))
            * (∑ y ∈ (Finset.Icc 1 M).filter (g ∣ ·), (1:ℝ)/(y:ℝ))) := by
      have h1 : ∀ x ∈ (Finset.Icc 1 M).filter (g ∣ ·),
          ∑ y ∈ (Finset.Icc 1 M).filter (g ∣ ·),
            (M:ℝ) * (g:ℝ) * ((1:ℝ)/(x:ℝ) * ((1:ℝ)/(y:ℝ)))
          = ((M:ℝ) * (g:ℝ) * ((1:ℝ)/(x:ℝ)))
            * ∑ y ∈ (Finset.Icc 1 M).filter (g ∣ ·), (1:ℝ)/(y:ℝ) := by
        intro x _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring
      have h2 : ∑ x ∈ (Finset.Icc 1 M).filter (g ∣ ·),
          (M:ℝ) * (g:ℝ) * ((1:ℝ)/(x:ℝ))
          = (M:ℝ) * (g:ℝ)
            * ∑ x ∈ (Finset.Icc 1 M).filter (g ∣ ·), (1:ℝ)/(x:ℝ) := by
        rw [Finset.mul_sum]
      rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, h2]
      ring
    rw [hfact]
    have hm := hmult g (by rw [Finset.mem_Icc]; omega)
    have hs0 : (0:ℝ) ≤ ∑ x ∈ (Finset.Icc 1 M).filter (g ∣ ·),
        (1:ℝ)/(x:ℝ) :=
      Finset.sum_nonneg fun x _ => by positivity
    have hMg0 : (0:ℝ) ≤ (M:ℝ) * (g:ℝ) := by positivity
    have hbound : (∑ x ∈ (Finset.Icc 1 M).filter (g ∣ ·), (1:ℝ)/(x:ℝ))
        * (∑ y ∈ (Finset.Icc 1 M).filter (g ∣ ·), (1:ℝ)/(y:ℝ))
        ≤ ((1/(g:ℝ)) * (1 + Real.log (M:ℝ)))^2 := by
      rw [pow_two]
      exact mul_le_mul hm hm hs0 (by positivity)
    calc (M:ℝ) * (g:ℝ)
        * ((∑ x ∈ (Finset.Icc 1 M).filter (g ∣ ·), (1:ℝ)/(x:ℝ))
          * (∑ y ∈ (Finset.Icc 1 M).filter (g ∣ ·), (1:ℝ)/(y:ℝ)))
        ≤ (M:ℝ) * (g:ℝ) * ((1/(g:ℝ)) * (1 + Real.log (M:ℝ)))^2 :=
          mul_le_mul_of_nonneg_left hbound hMg0
      _ = (M:ℝ) * (1 + Real.log (M:ℝ))^2 * (1/(g:ℝ)) := by
          field_simp
  refine le_trans (Finset.sum_le_sum hfiber) ?_
  rw [← Finset.mul_sum]
  have hharmM := sum_inv_le_log M hM
  have hsum1 : ∑ g ∈ Finset.Icc 1 M, (1:ℝ)/(g:ℝ)
      ≤ 1 + Real.log (M:ℝ) := by
    linarith [hharmM]
  have hc0 : (0:ℝ) ≤ (M:ℝ) * (1 + Real.log (M:ℝ))^2 := by positivity
  calc (M:ℝ) * (1 + Real.log (M:ℝ))^2
      * ∑ g ∈ Finset.Icc 1 M, (1:ℝ)/(g:ℝ)
      ≤ (M:ℝ) * (1 + Real.log (M:ℝ))^2 * (1 + Real.log (M:ℝ)) :=
        mul_le_mul_of_nonneg_left hsum1 hc0
    _ = (M:ℝ) * (1 + Real.log (M:ℝ))^3 := by
        ring


/-- **The divisor-square mean value** (Track R, V5b-ii):
`∑_{m ≤ M} τ(m)² ≤ M(1 + log M)³` — the double count against the lcm
lattice sum. -/
theorem sum_tau_sq_le (M : ℕ) (hM : 1 ≤ M) :
    ∑ m ∈ Finset.Icc 1 M, ((m.divisors.card : ℝ))^2
      ≤ (M:ℝ) * (1 + Real.log (M:ℝ))^3 :=
  le_trans (sum_tau_sq_le_lcm_sum M hM) (lcm_sum_le M hM)

/-- **Möbius partial sums are divisor-bounded** (Track R, V5b-ii): the
Type II coefficients of Vaughan's identity, `∑_{d ∣ m, d ≤ U} μ(d)`,
have absolute value at most `τ(m)`. -/
theorem abs_moebius_partial_le_tau (U m : ℕ) :
    |∑ d ∈ m.divisors.filter (· ≤ U), ((ArithmeticFunction.moebius d : ℤ):ℝ)|
      ≤ ((m.divisors.card : ℝ)) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have h1 : ∀ d ∈ m.divisors.filter (· ≤ U),
      |((ArithmeticFunction.moebius d : ℤ):ℝ)| ≤ 1 := by
    intro d _
    have := ArithmeticFunction.abs_moebius_le_one (n := d)
    exact_mod_cast this
  refine le_trans (Finset.sum_le_sum h1) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast Finset.card_filter_le _ _


/-- **The pointwise divisor-pair swap** (Track R, V5c-i): the two
nestings of a double divisor sum agree —
`∑_{b ∣ n} ∑_{c ∣ n/b} = ∑_{c ∣ n} ∑_{b ∣ n/c}`.  The Vaughan
decomposition reorders its triple products through this. -/
theorem sum_divisors_pair_swap {M : Type*} [AddCommMonoid M] (n : ℕ)
    (F : ℕ → ℕ → M) :
    ∑ b ∈ n.divisors, ∑ c ∈ (n/b).divisors, F b c
      = ∑ c ∈ n.divisors, ∑ b ∈ (n/c).divisors, F b c := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => Sigma.mk p.2 p.1)
    (fun q => Sigma.mk q.2 q.1) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨b, c⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp ⊢
    obtain ⟨⟨hb, -⟩, hc, hnb⟩ := hp
    have hcb : b * c ∣ n := (Nat.dvd_div_iff_mul_dvd hb).mp hc
    have hcn : c ∣ n := dvd_trans (dvd_mul_left c b) hcb
    refine ⟨⟨hcn, by omega⟩, ?_, ?_⟩
    · refine (Nat.dvd_div_iff_mul_dvd hcn).mpr ?_
      rw [Nat.mul_comm c b]
      exact hcb
    · refine Nat.div_ne_zero_iff.mpr ⟨?_, Nat.le_of_dvd (by omega) hcn⟩
      intro hc0
      rw [hc0] at hcn
      have := Nat.eq_zero_of_zero_dvd hcn
      omega
  · rintro ⟨c, b⟩ hq
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hq ⊢
    obtain ⟨⟨hc, -⟩, hb, hnc⟩ := hq
    have hbc : c * b ∣ n := (Nat.dvd_div_iff_mul_dvd hc).mp hb
    have hbn : b ∣ n := dvd_trans (dvd_mul_left b c) hbc
    refine ⟨⟨hbn, by omega⟩, ?_, ?_⟩
    · refine (Nat.dvd_div_iff_mul_dvd hbn).mpr ?_
      rw [Nat.mul_comm b c]
      exact hbc
    · refine Nat.div_ne_zero_iff.mpr ⟨?_, Nat.le_of_dvd (by omega) hbn⟩
      intro hb0
      rw [hb0] at hbn
      have := Nat.eq_zero_of_zero_dvd hbn
      omega
  · rintro ⟨b, c⟩ _
    rfl
  · rintro ⟨c, b⟩ _
    rfl
  · rintro ⟨b, c⟩ _
    rfl

/-- **The Möbius divisor sum detects `1`** (Track R, V5c-i):
`∑_{b ∣ m} μ(b) = [m = 1]`, in real form. -/
theorem sum_divisors_moebius_ite (m : ℕ) (hm : m ≠ 0) :
    ∑ b ∈ m.divisors, ((ArithmeticFunction.moebius b : ℤ):ℝ)
      = if m = 1 then 1 else 0 := by
  have h1 : (ArithmeticFunction.moebius * ArithmeticFunction.zeta
      : ArithmeticFunction ℤ) m = (1 : ArithmeticFunction ℤ) m := by
    rw [ArithmeticFunction.moebius_mul_coe_zeta]
  rw [ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.one_apply] at h1
  have h2 : ((∑ i ∈ m.divisors, ArithmeticFunction.moebius i : ℤ):ℝ)
      = ((if m = 1 then 1 else 0 : ℤ):ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z:ℝ)) h1
  push_cast at h2
  exact h2


open ArithmeticFunction in
/-- **Vaughan's identity, pointwise** (Track R, V5c-ii): for `V < n`,

`Λ(n) = ∑_{b∣n, b≤U} μ(b) log(n/b) − ∑_{b∣n, b≤U} μ(b) ∑_{c∣n/b, c≤V} Λ(c)
        + ∑_{c∣n, c>V} Λ(c) ∑_{b∣n/c, b>U} μ(b)`

— the two divisor-pair swaps against `vonMangoldt_sum` and the Möbius
detector.  The three terms are the Type I, Type I', and Type II shapes
of the prime exponential sum estimate. -/
theorem vaughan_pointwise (U V n : ℕ) (hV : V < n) :
    (vonMangoldt n : ℝ)
      = (∑ b ∈ n.divisors.filter (· ≤ U),
          ((moebius b : ℤ):ℝ) * Real.log ((n/b : ℕ):ℝ))
        - (∑ b ∈ n.divisors.filter (· ≤ U), ((moebius b : ℤ):ℝ)
            * ∑ c ∈ (n/b).divisors.filter (· ≤ V), (vonMangoldt c : ℝ))
        + (∑ c ∈ n.divisors.filter (fun c => ¬ c ≤ V),
            (vonMangoldt c : ℝ)
              * ∑ b ∈ (n/c).divisors.filter (fun b => ¬ b ≤ U),
                ((moebius b : ℤ):ℝ)) := by
  classical
  have hn0 : n ≠ 0 := by omega
  -- (1) expand the logarithm in T1
  have hT1 : ∑ b ∈ n.divisors.filter (· ≤ U),
      ((moebius b : ℤ):ℝ) * Real.log ((n/b : ℕ):ℝ)
      = ∑ b ∈ n.divisors.filter (· ≤ U), ((moebius b : ℤ):ℝ)
          * ∑ c ∈ (n/b).divisors, (vonMangoldt c : ℝ) := by
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [Finset.mem_filter, Nat.mem_divisors] at hb
    rw [vonMangoldt_sum]
  -- (2) split the inner sum at V
  have hsplit1 : ∑ b ∈ n.divisors.filter (· ≤ U), ((moebius b : ℤ):ℝ)
      * ∑ c ∈ (n/b).divisors, (vonMangoldt c : ℝ)
      = (∑ b ∈ n.divisors.filter (· ≤ U), ((moebius b : ℤ):ℝ)
          * ∑ c ∈ (n/b).divisors.filter (· ≤ V), (vonMangoldt c : ℝ))
        + ∑ b ∈ n.divisors.filter (· ≤ U), ((moebius b : ℤ):ℝ)
          * ∑ c ∈ (n/b).divisors.filter (fun c => ¬ c ≤ V),
            (vonMangoldt c : ℝ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_add, ← Finset.sum_filter_add_sum_filter_not
      ((n/b).divisors) (· ≤ V)]
  -- (3) the full-b sum with the `c > V` inner collapses to `Λ(n)`
  have hfull : ∑ b ∈ n.divisors, ((moebius b : ℤ):ℝ)
      * ∑ c ∈ (n/b).divisors.filter (fun c => ¬ c ≤ V),
        (vonMangoldt c : ℝ)
      = (vonMangoldt n : ℝ) := by
    have hstep : ∑ b ∈ n.divisors, ((moebius b : ℤ):ℝ)
        * ∑ c ∈ (n/b).divisors.filter (fun c => ¬ c ≤ V),
          (vonMangoldt c : ℝ)
        = ∑ b ∈ n.divisors, ∑ c ∈ (n/b).divisors,
          ((moebius b : ℤ):ℝ)
            * (if ¬ c ≤ V then (vonMangoldt c : ℝ) else 0) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun c _ => ?_
      split <;> simp
    rw [hstep, sum_divisors_pair_swap n (fun b c =>
      ((moebius b : ℤ):ℝ) * (if ¬ c ≤ V then (vonMangoldt c : ℝ) else 0))]
    have hinner : ∀ c ∈ n.divisors,
        ∑ b ∈ (n/c).divisors, ((moebius b : ℤ):ℝ)
          * (if ¬ c ≤ V then (vonMangoldt c : ℝ) else 0)
        = (if ¬ c ≤ V then (vonMangoldt c : ℝ) else 0)
          * (if n/c = 1 then 1 else 0) := by
      intro c hc
      rw [Nat.mem_divisors] at hc
      rw [← Finset.sum_mul, mul_comm, sum_divisors_moebius_ite (n/c)
        (Nat.div_ne_zero_iff.mpr ⟨(by
          intro hc0
          rw [hc0] at hc
          have := Nat.eq_zero_of_zero_dvd hc.1
          omega), Nat.le_of_dvd (by omega) hc.1⟩)]
    rw [Finset.sum_congr rfl hinner]
    have hset : ∀ c ∈ n.divisors,
        (if ¬ c ≤ V then (vonMangoldt c : ℝ) else 0)
          * (if n/c = 1 then 1 else 0)
        = if c = n then (if ¬ c ≤ V then (vonMangoldt c : ℝ) else 0)
          else 0 := by
      intro c hc
      rw [Nat.mem_divisors] at hc
      have hiff : n/c = 1 ↔ c = n := by
        constructor
        · intro h1
          have h2 : n/c * c = n := Nat.div_mul_cancel hc.1
          rw [h1, one_mul] at h2
          exact h2
        · rintro rfl
          exact Nat.div_self (by omega)
      rcases Classical.em (c = n) with rfl | hne
      · rw [if_pos rfl, if_pos (hiff.mpr rfl), mul_one]
      · rw [if_neg hne, if_neg (fun h => hne (hiff.mp h)), mul_zero]
    rw [Finset.sum_congr rfl hset, Finset.sum_ite_eq' n.divisors n
      (fun c => if ¬ c ≤ V then (vonMangoldt c : ℝ) else 0)]
    rw [if_pos (Nat.mem_divisors_self n hn0)]
    rw [if_pos (by omega : ¬ n ≤ V)]
  -- (4) split the full-b sum at U and swap the `b > U` half
  have hsplit2 : ∑ b ∈ n.divisors, ((moebius b : ℤ):ℝ)
      * ∑ c ∈ (n/b).divisors.filter (fun c => ¬ c ≤ V),
        (vonMangoldt c : ℝ)
      = (∑ b ∈ n.divisors.filter (· ≤ U), ((moebius b : ℤ):ℝ)
          * ∑ c ∈ (n/b).divisors.filter (fun c => ¬ c ≤ V),
            (vonMangoldt c : ℝ))
        + ∑ b ∈ n.divisors.filter (fun b => ¬ b ≤ U),
          ((moebius b : ℤ):ℝ)
            * ∑ c ∈ (n/b).divisors.filter (fun c => ¬ c ≤ V),
              (vonMangoldt c : ℝ) :=
    (Finset.sum_filter_add_sum_filter_not n.divisors (· ≤ U) _).symm
  have hswap2 : ∑ b ∈ n.divisors.filter (fun b => ¬ b ≤ U),
      ((moebius b : ℤ):ℝ)
        * ∑ c ∈ (n/b).divisors.filter (fun c => ¬ c ≤ V),
          (vonMangoldt c : ℝ)
      = ∑ c ∈ n.divisors.filter (fun c => ¬ c ≤ V),
        (vonMangoldt c : ℝ)
          * ∑ b ∈ (n/c).divisors.filter (fun b => ¬ b ≤ U),
            ((moebius b : ℤ):ℝ) := by
    have hL : ∑ b ∈ n.divisors.filter (fun b => ¬ b ≤ U),
        ((moebius b : ℤ):ℝ)
          * ∑ c ∈ (n/b).divisors.filter (fun c => ¬ c ≤ V),
            (vonMangoldt c : ℝ)
        = ∑ b ∈ n.divisors, ∑ c ∈ (n/b).divisors,
          (if ¬ b ≤ U then ((moebius b : ℤ):ℝ) else 0)
            * (if ¬ c ≤ V then (vonMangoldt c : ℝ) else 0) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun b _ => ?_
      split
      · rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun c _ => ?_
        split <;> simp
      · simp
    have hR : ∑ c ∈ n.divisors.filter (fun c => ¬ c ≤ V),
        (vonMangoldt c : ℝ)
          * ∑ b ∈ (n/c).divisors.filter (fun b => ¬ b ≤ U),
            ((moebius b : ℤ):ℝ)
        = ∑ c ∈ n.divisors, ∑ b ∈ (n/c).divisors,
          (if ¬ b ≤ U then ((moebius b : ℤ):ℝ) else 0)
            * (if ¬ c ≤ V then (vonMangoldt c : ℝ) else 0) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun c _ => ?_
      split
      · rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun b _ => ?_
        split
        · ring
        · simp
      · simp
    rw [hL, hR, sum_divisors_pair_swap n (fun b c =>
      (if ¬ b ≤ U then ((moebius b : ℤ):ℝ) else 0)
        * (if ¬ c ≤ V then (vonMangoldt c : ℝ) else 0))]
  -- assemble
  have hkey : (∑ b ∈ n.divisors.filter (· ≤ U),
      ((moebius b : ℤ):ℝ) * Real.log ((n/b : ℕ):ℝ))
      = (∑ b ∈ n.divisors.filter (· ≤ U), ((moebius b : ℤ):ℝ)
          * ∑ c ∈ (n/b).divisors.filter (· ≤ V), (vonMangoldt c : ℝ))
        + ((vonMangoldt n : ℝ)
          - ∑ c ∈ n.divisors.filter (fun c => ¬ c ≤ V),
            (vonMangoldt c : ℝ)
              * ∑ b ∈ (n/c).divisors.filter (fun b => ¬ b ≤ U),
                ((moebius b : ℤ):ℝ)) := by
    rw [hT1, hsplit1]
    have h1 : ∑ b ∈ n.divisors.filter (· ≤ U), ((moebius b : ℤ):ℝ)
        * ∑ c ∈ (n/b).divisors.filter (fun c => ¬ c ≤ V),
          (vonMangoldt c : ℝ)
        = (vonMangoldt n : ℝ)
          - ∑ c ∈ n.divisors.filter (fun c => ¬ c ≤ V),
            (vonMangoldt c : ℝ)
              * ∑ b ∈ (n/c).divisors.filter (fun b => ¬ b ≤ U),
                ((moebius b : ℤ):ℝ) := by
      have h2 := hsplit2
      rw [hfull, hswap2] at h2
      linarith [h2]
    linarith [h1]
  linarith [hkey]


/-- **The two-sided range divisor swap** (Track R, V5c-iii-a): summing
over `n ∈ (A, N]` and its divisors equals summing over each modulus `d`
and the cofactors `m` with `A < dm ≤ N` — the exchange that turns the
weighted Vaughan identity into its Type I/II range shapes. -/
theorem sum_Ioc_divisors_swap {M : Type*} [AddCommMonoid M] (A N : ℕ)
    (g : ℕ → ℕ → M) :
    ∑ n ∈ Finset.Ioc A N, ∑ d ∈ n.divisors, g d n
      = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Ioc (A/d) (N/d), g d (d*m) := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => Sigma.mk p.2 (p.1 / p.2))
    (fun q => Sigma.mk (q.1 * q.2) q.1) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, d⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Ioc, Finset.mem_Icc,
      Nat.mem_divisors] at hp ⊢
    obtain ⟨⟨hAn, hnN⟩, hdvd, hn0⟩ := hp
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
    have hdN : d ≤ N := le_trans (Nat.le_of_dvd (by omega) hdvd) hnN
    have hmul : n / d * d = n := Nat.div_mul_cancel hdvd
    refine ⟨⟨by omega, hdN⟩, ?_, Nat.div_le_div_right hnN⟩
    rw [Nat.div_lt_iff_lt_mul hd0]
    omega
  · rintro ⟨d, m⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_Ioc, Finset.mem_Icc,
      Nat.mem_divisors] at hq ⊢
    obtain ⟨⟨hd1, hdN⟩, hAm, hmN⟩ := hq
    have hd0 : 0 < d := by omega
    rw [Nat.div_lt_iff_lt_mul hd0] at hAm
    rw [Nat.le_div_iff_mul_le hd0] at hmN
    have hcomm : m * d = d * m := Nat.mul_comm m d
    refine ⟨⟨by omega, by omega⟩, Dvd.intro m rfl, ?_⟩
    intro hc
    have h0 : m * d = 0 := by
      rw [hcomm]
      exact hc
    omega
  · rintro ⟨n, d⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    obtain ⟨-, hdvd, -⟩ := hp
    have h1 : d * (n / d) = n := Nat.mul_div_cancel' hdvd
    simp only [Sigma.mk.injEq, heq_iff_eq]
    exact ⟨h1, trivial⟩
  · rintro ⟨d, m⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hq
    obtain ⟨⟨hd1, -⟩, -⟩ := hq
    have h1 : d * m / d = m := Nat.mul_div_cancel_left m (by omega)
    simp only [Sigma.mk.injEq, heq_iff_eq]
    exact ⟨trivial, h1⟩
  · rintro ⟨n, d⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    obtain ⟨-, hdvd, -⟩ := hp
    have h1 : d * (n / d) = n := Nat.mul_div_cancel' hdvd
    rw [h1]


open ArithmeticFunction in
/-- **Vaughan's identity, weighted and exchanged** (Track R,
V5c-iii-b): summing the pointwise identity against any weight over
`(n₀, N]` and exchanging each term to modulus-major form.  The three
right-hand sums are the Type I (log weight), Type I' (short von
Mangoldt coefficient), and Type II (Möbius-tail coefficient) shapes. -/
theorem vaughan_weighted (U V n₀ N : ℕ) (hV : V < n₀) (w : ℕ → ℂ) :
    ∑ n ∈ Finset.Ioc n₀ N, ((vonMangoldt n : ℝ):ℂ) * w n
      = (∑ b ∈ (Finset.Icc 1 N).filter (· ≤ U),
          (((moebius b : ℤ):ℝ):ℂ)
            * ∑ m ∈ Finset.Ioc (n₀/b) (N/b),
              ((Real.log (m:ℝ) : ℝ):ℂ) * w (b*m))
        - (∑ b ∈ (Finset.Icc 1 N).filter (· ≤ U),
            (((moebius b : ℤ):ℝ):ℂ)
              * ∑ m ∈ Finset.Ioc (n₀/b) (N/b),
                ((∑ c ∈ m.divisors.filter (· ≤ V),
                  (vonMangoldt c : ℝ) : ℝ):ℂ) * w (b*m))
        + (∑ c ∈ (Finset.Icc 1 N).filter (fun c => ¬ c ≤ V),
            ((vonMangoldt c : ℝ):ℂ)
              * ∑ m ∈ Finset.Ioc (n₀/c) (N/c),
                ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
                  ((moebius b : ℤ):ℝ) : ℝ):ℂ) * w (c*m)) := by
  classical
  -- expand each `Λ(n)·w(n)` by the pointwise identity
  have hpt : ∀ n ∈ Finset.Ioc n₀ N, ((vonMangoldt n : ℝ):ℂ) * w n
      = (∑ b ∈ n.divisors.filter (· ≤ U),
          (((moebius b : ℤ):ℝ):ℂ) * ((Real.log ((n/b : ℕ):ℝ) : ℝ):ℂ))
            * w n
        - (∑ b ∈ n.divisors.filter (· ≤ U),
            (((moebius b : ℤ):ℝ):ℂ)
              * ((∑ c ∈ (n/b).divisors.filter (· ≤ V),
                (vonMangoldt c : ℝ) : ℝ):ℂ)) * w n
        + (∑ c ∈ n.divisors.filter (fun c => ¬ c ≤ V),
            ((vonMangoldt c : ℝ):ℂ)
              * ((∑ b ∈ (n/c).divisors.filter (fun b => ¬ b ≤ U),
                ((moebius b : ℤ):ℝ) : ℝ):ℂ)) * w n := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hid := vaughan_pointwise U V n (by omega)
    have hidC : ((vonMangoldt n : ℝ):ℂ)
        = (∑ b ∈ n.divisors.filter (· ≤ U),
            (((moebius b : ℤ):ℝ):ℂ) * ((Real.log ((n/b : ℕ):ℝ) : ℝ):ℂ))
          - (∑ b ∈ n.divisors.filter (· ≤ U),
              (((moebius b : ℤ):ℝ):ℂ)
                * ((∑ c ∈ (n/b).divisors.filter (· ≤ V),
                  (vonMangoldt c : ℝ) : ℝ):ℂ))
          + (∑ c ∈ n.divisors.filter (fun c => ¬ c ≤ V),
              ((vonMangoldt c : ℝ):ℂ)
                * ((∑ b ∈ (n/c).divisors.filter (fun b => ¬ b ≤ U),
                  ((moebius b : ℤ):ℝ) : ℝ):ℂ)) := by
      rw [show ((vonMangoldt n : ℝ):ℂ)
          = (((∑ b ∈ n.divisors.filter (· ≤ U),
              ((moebius b : ℤ):ℝ) * Real.log ((n/b : ℕ):ℝ))
            - (∑ b ∈ n.divisors.filter (· ≤ U), ((moebius b : ℤ):ℝ)
                * ∑ c ∈ (n/b).divisors.filter (· ≤ V),
                  (vonMangoldt c : ℝ))
            + (∑ c ∈ n.divisors.filter (fun c => ¬ c ≤ V),
                (vonMangoldt c : ℝ)
                  * ∑ b ∈ (n/c).divisors.filter (fun b => ¬ b ≤ U),
                    ((moebius b : ℤ):ℝ)) : ℝ):ℂ) from by
        rw [← hid]]
      push_cast
      ring_nf
    rw [hidC]
    ring
  rw [Finset.sum_congr rfl hpt]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  congr 1
  · congr 1
    · -- Type I exchange
      have h1 : ∀ n ∈ Finset.Ioc n₀ N,
          (∑ b ∈ n.divisors.filter (· ≤ U),
            (((moebius b : ℤ):ℝ):ℂ)
              * ((Real.log ((n/b : ℕ):ℝ) : ℝ):ℂ)) * w n
          = ∑ b ∈ n.divisors,
            (if b ≤ U then (((moebius b : ℤ):ℝ):ℂ) else 0)
              * ((Real.log ((n/b : ℕ):ℝ) : ℝ):ℂ) * w n := by
        intro n _
        rw [Finset.sum_mul, Finset.sum_filter]
        refine Finset.sum_congr rfl fun b _ => ?_
        split <;> simp
      rw [Finset.sum_congr rfl h1, sum_Ioc_divisors_swap n₀ N
        (fun b n => (if b ≤ U then (((moebius b : ℤ):ℝ):ℂ) else 0)
          * ((Real.log ((n/b : ℕ):ℝ) : ℝ):ℂ) * w n)]
      have h2 : ∀ b ∈ Finset.Icc 1 N,
          ∑ m ∈ Finset.Ioc (n₀/b) (N/b),
            (if b ≤ U then (((moebius b : ℤ):ℝ):ℂ) else 0)
              * ((Real.log ((b*m/b : ℕ):ℝ) : ℝ):ℂ) * w (b*m)
          = (if b ≤ U then (((moebius b : ℤ):ℝ):ℂ) else 0)
            * ∑ m ∈ Finset.Ioc (n₀/b) (N/b),
              ((Real.log (m:ℝ) : ℝ):ℂ) * w (b*m) := by
        intro b hb
        rw [Finset.mem_Icc] at hb
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Nat.mul_div_cancel_left m (by omega)]
        ring
      have h3 : ∀ b ∈ Finset.Icc 1 N,
          (if b ≤ U then (((moebius b : ℤ):ℝ):ℂ) else 0)
            * ∑ m ∈ Finset.Ioc (n₀/b) (N/b),
              ((Real.log (m:ℝ) : ℝ):ℂ) * w (b*m)
          = if b ≤ U then (((moebius b : ℤ):ℝ):ℂ)
              * ∑ m ∈ Finset.Ioc (n₀/b) (N/b),
                ((Real.log (m:ℝ) : ℝ):ℂ) * w (b*m) else 0 := by
        intro b _
        split <;> simp
      rw [Finset.sum_congr rfl h2, Finset.sum_congr rfl h3,
        ← Finset.sum_filter]
    · -- Type I' exchange
      have h1 : ∀ n ∈ Finset.Ioc n₀ N,
          (∑ b ∈ n.divisors.filter (· ≤ U),
            (((moebius b : ℤ):ℝ):ℂ)
              * ((∑ c ∈ (n/b).divisors.filter (· ≤ V),
                (vonMangoldt c : ℝ) : ℝ):ℂ)) * w n
          = ∑ b ∈ n.divisors,
            (if b ≤ U then (((moebius b : ℤ):ℝ):ℂ) else 0)
              * ((∑ c ∈ (n/b).divisors.filter (· ≤ V),
                (vonMangoldt c : ℝ) : ℝ):ℂ) * w n := by
        intro n _
        rw [Finset.sum_mul, Finset.sum_filter]
        refine Finset.sum_congr rfl fun b _ => ?_
        split <;> simp
      rw [Finset.sum_congr rfl h1, sum_Ioc_divisors_swap n₀ N
        (fun b n => (if b ≤ U then (((moebius b : ℤ):ℝ):ℂ) else 0)
          * ((∑ c ∈ (n/b).divisors.filter (· ≤ V),
            (vonMangoldt c : ℝ) : ℝ):ℂ) * w n)]
      have h2 : ∀ b ∈ Finset.Icc 1 N,
          ∑ m ∈ Finset.Ioc (n₀/b) (N/b),
            (if b ≤ U then (((moebius b : ℤ):ℝ):ℂ) else 0)
              * ((∑ c ∈ (b*m/b).divisors.filter (· ≤ V),
                (vonMangoldt c : ℝ) : ℝ):ℂ) * w (b*m)
          = (if b ≤ U then (((moebius b : ℤ):ℝ):ℂ) else 0)
            * ∑ m ∈ Finset.Ioc (n₀/b) (N/b),
              ((∑ c ∈ m.divisors.filter (· ≤ V),
                (vonMangoldt c : ℝ) : ℝ):ℂ) * w (b*m) := by
        intro b hb
        rw [Finset.mem_Icc] at hb
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Nat.mul_div_cancel_left m (by omega)]
        ring
      have h3 : ∀ b ∈ Finset.Icc 1 N,
          (if b ≤ U then (((moebius b : ℤ):ℝ):ℂ) else 0)
            * ∑ m ∈ Finset.Ioc (n₀/b) (N/b),
              ((∑ c ∈ m.divisors.filter (· ≤ V),
                (vonMangoldt c : ℝ) : ℝ):ℂ) * w (b*m)
          = if b ≤ U then (((moebius b : ℤ):ℝ):ℂ)
              * ∑ m ∈ Finset.Ioc (n₀/b) (N/b),
                ((∑ c ∈ m.divisors.filter (· ≤ V),
                  (vonMangoldt c : ℝ) : ℝ):ℂ) * w (b*m) else 0 := by
        intro b _
        split <;> simp
      rw [Finset.sum_congr rfl h2, Finset.sum_congr rfl h3,
        ← Finset.sum_filter]
  · -- Type II exchange
    have h1 : ∀ n ∈ Finset.Ioc n₀ N,
        (∑ c ∈ n.divisors.filter (fun c => ¬ c ≤ V),
          ((vonMangoldt c : ℝ):ℂ)
            * ((∑ b ∈ (n/c).divisors.filter (fun b => ¬ b ≤ U),
              ((moebius b : ℤ):ℝ) : ℝ):ℂ)) * w n
        = ∑ c ∈ n.divisors,
          (if ¬ c ≤ V then ((vonMangoldt c : ℝ):ℂ) else 0)
            * ((∑ b ∈ (n/c).divisors.filter (fun b => ¬ b ≤ U),
              ((moebius b : ℤ):ℝ) : ℝ):ℂ) * w n := by
      intro n _
      rw [Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun c _ => ?_
      split <;> simp
    rw [Finset.sum_congr rfl h1, sum_Ioc_divisors_swap n₀ N
      (fun c n => (if ¬ c ≤ V then ((vonMangoldt c : ℝ):ℂ) else 0)
        * ((∑ b ∈ (n/c).divisors.filter (fun b => ¬ b ≤ U),
          ((moebius b : ℤ):ℝ) : ℝ):ℂ) * w n)]
    have h2 : ∀ c ∈ Finset.Icc 1 N,
        ∑ m ∈ Finset.Ioc (n₀/c) (N/c),
          (if ¬ c ≤ V then ((vonMangoldt c : ℝ):ℂ) else 0)
            * ((∑ b ∈ (c*m/c).divisors.filter (fun b => ¬ b ≤ U),
              ((moebius b : ℤ):ℝ) : ℝ):ℂ) * w (c*m)
        = (if ¬ c ≤ V then ((vonMangoldt c : ℝ):ℂ) else 0)
          * ∑ m ∈ Finset.Ioc (n₀/c) (N/c),
            ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
              ((moebius b : ℤ):ℝ) : ℝ):ℂ) * w (c*m) := by
      intro c hc
      rw [Finset.mem_Icc] at hc
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Nat.mul_div_cancel_left m (by omega)]
      ring
    have h3 : ∀ c ∈ Finset.Icc 1 N,
        (if ¬ c ≤ V then ((vonMangoldt c : ℝ):ℂ) else 0)
          * ∑ m ∈ Finset.Ioc (n₀/c) (N/c),
            ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
              ((moebius b : ℤ):ℝ) : ℝ):ℂ) * w (c*m)
        = if ¬ c ≤ V then ((vonMangoldt c : ℝ):ℂ)
            * ∑ m ∈ Finset.Ioc (n₀/c) (N/c),
              ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
                ((moebius b : ℤ):ℝ) : ℝ):ℂ) * w (c*m) else 0 := by
      intro c _
      split <;> simp
    rw [Finset.sum_congr rfl h2, Finset.sum_congr rfl h3,
      ← Finset.sum_filter]


/-- **Discrete Abel summation, monotone-coefficient bound** (Track R,
V6a): if all window partials of `z` are bounded by `B` and `φ` is
nonnegative and nondecreasing, then `‖∑ φ(m) z(m)‖ ≤ 2 φ(Q) B` — the
log-weighted Type I leg reduces to the unweighted one at the price of
one logarithm. -/
theorem abel_mono_bound (P Q : ℕ) (hPQ : P ≤ Q) (φ : ℕ → ℝ) (z : ℕ → ℂ)
    (B : ℝ) (hφ0 : ∀ m, 0 ≤ φ m) (hmono : ∀ m, φ m ≤ φ (m+1))
    (hB : ∀ t, P ≤ t → t ≤ Q → ‖∑ m ∈ Finset.Ioc P t, z m‖ ≤ B) :
    ‖∑ m ∈ Finset.Ioc P Q, ((φ m : ℝ):ℂ) * z m‖ ≤ 2 * φ Q * B := by
  classical
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB P le_rfl hPQ)
  -- the Abel identity
  have habel : ∀ R, P ≤ R → R ≤ Q →
      ∑ m ∈ Finset.Ioc P R, ((φ m : ℝ):ℂ) * z m
      = ((φ R : ℝ):ℂ) * (∑ m ∈ Finset.Ioc P R, z m)
        - ∑ t ∈ Finset.Ico (P+1) R,
          ((φ (t+1) - φ t : ℝ):ℂ) * (∑ m ∈ Finset.Ioc P t, z m) := by
    intro R hPR hRQ
    clear hRQ
    induction R, hPR using Nat.le_induction with
    | base =>
      simp
    | succ R hPR ih =>
      rw [Finset.sum_Ioc_succ_top (by omega), ih]
      rcases Nat.eq_or_lt_of_le hPR with rfl | hlt
      · have he : Finset.Ico (P+1) P = ∅ := Finset.Ico_eq_empty (by omega)
        have he2 : Finset.Ico (P+1) (P+1) = ∅ :=
          Finset.Ico_eq_empty (by omega)
        rw [he, he2]
        have he3 : Finset.Ioc P P = ∅ := Finset.Ioc_self P
        rw [he3]
        rw [Finset.sum_Ioc_succ_top (le_refl P), he3]
        simp
      · rw [Finset.sum_Ico_succ_top (by omega : P + 1 ≤ R)]
        rw [Finset.sum_Ioc_succ_top (by omega : P ≤ R)]
        push_cast
        ring
  rcases Nat.eq_or_lt_of_le hPQ with rfl | hPQ'
  · simp only [Finset.Ioc_self, Finset.sum_empty, norm_zero]
    have := hφ0 P
    nlinarith [hB0]
  rw [habel Q hPQ le_rfl]
  refine le_trans (norm_sub_le _ _) ?_
  have h1 : ‖((φ Q : ℝ):ℂ) * (∑ m ∈ Finset.Ioc P Q, z m)‖
      ≤ φ Q * B := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hφ0 Q)]
    exact mul_le_mul_of_nonneg_left (hB Q hPQ le_rfl) (hφ0 Q)
  have h2 : ‖∑ t ∈ Finset.Ico (P+1) Q,
      ((φ (t+1) - φ t : ℝ):ℂ) * (∑ m ∈ Finset.Ioc P t, z m)‖
      ≤ (φ Q - φ (P+1)) * B := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ t ∈ Finset.Ico (P+1) Q,
        ‖((φ (t+1) - φ t : ℝ):ℂ) * (∑ m ∈ Finset.Ioc P t, z m)‖
        ≤ (φ (t+1) - φ t) * B := by
      intro t ht
      rw [Finset.mem_Ico] at ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [hmono t])]
      exact mul_le_mul (le_refl _) (hB t (by omega) (by omega))
        (norm_nonneg _) (by linarith [hmono t])
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_mul]
    have htel : ∑ t ∈ Finset.Ico (P+1) Q, (φ (t+1) - φ t)
        = φ Q - φ (P+1) := by
      have h := sum_Ico_sub_telescope φ (by omega : P + 1 ≤ Q)
      have h2 : ∑ t ∈ Finset.Ico (P+1) Q, (φ (t+1) - φ t)
          = - ∑ t ∈ Finset.Ico (P+1) Q, (φ t - φ (t+1)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun t _ => ?_
        ring
      rw [h2, h]
      ring
    rw [htel]
  have hle : φ (P+1) ≤ φ Q := by
    have h : P + 1 ≤ Q := by omega
    clear hB habel h1 h2
    induction Q, h using Nat.le_induction with
    | base => exact le_refl _
    | succ Q hQ ih =>
      exact le_trans (ih (by omega) (by omega)) (hmono Q)
  have hpb : 0 ≤ φ (P+1) * B := mul_nonneg (hφ0 _) hB0
  have hexp : (φ Q - φ (P+1)) * B = φ Q * B - φ (P+1) * B := by
    ring
  linarith [h1, h2, hpb, hexp.le, hexp.ge]


open ArithmeticFunction in
/-- **The Type I' regroup** (Track R, V6b-i): in the middle Vaughan
term, expanding `m` through its short `Λ`-divisor `c` and fibering the
double `(b, c)`-sum over the product `t = b*c` produces a Type I shape
at modulus `t ≤ U*V`, with the Dirichlet-convolution partial
`∑_{bc=t, b≤U, c≤V} μ(b)Λ(c)` as coefficient. -/
theorem vaughan_typeI'_regroup (U V n₀ N : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hUV : U*V ≤ N) (w : ℕ → ℂ) :
    ∑ b ∈ (Finset.Icc 1 N).filter (· ≤ U),
        (((moebius b : ℤ):ℝ):ℂ)
          * ∑ m ∈ Finset.Ioc (n₀/b) (N/b),
            ((∑ c ∈ m.divisors.filter (· ≤ V),
              (vonMangoldt c : ℝ) : ℝ):ℂ) * w (b*m)
      = ∑ t ∈ Finset.Icc 1 (U*V),
          ((∑ p ∈ (Finset.Icc 1 U ×ˢ Finset.Icc 1 V).filter
              (fun p => p.1 * p.2 = t),
            ((moebius p.1 : ℤ):ℝ) * (vonMangoldt p.2 : ℝ) : ℝ):ℂ)
            * ∑ k ∈ Finset.Ioc (n₀/t) (N/t), w (t*k) := by
  classical
  have hUN : U ≤ N := by
    calc U = U * 1 := (mul_one U).symm
      _ ≤ U * V := mul_le_mul_left' hV U
      _ ≤ N := hUV
  have hfil : (Finset.Icc 1 N).filter (· ≤ U) = Finset.Icc 1 U := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1b, -⟩, hbU⟩
      exact ⟨h1b, hbU⟩
    · rintro ⟨h1b, hbU⟩
      exact ⟨⟨h1b, le_trans hbU hUN⟩, hbU⟩
  rw [hfil]
  -- per-`b`: expand the `Λ`-coefficient and swap the divisor out
  have hswap : ∀ b ∈ Finset.Icc 1 U,
      (((moebius b : ℤ):ℝ):ℂ)
          * ∑ m ∈ Finset.Ioc (n₀/b) (N/b),
            ((∑ c ∈ m.divisors.filter (· ≤ V),
              (vonMangoldt c : ℝ) : ℝ):ℂ) * w (b*m)
        = ∑ c ∈ Finset.Icc 1 V,
            ((((moebius b : ℤ):ℝ) * (vonMangoldt c : ℝ) : ℝ):ℂ)
              * ∑ k ∈ Finset.Ioc (n₀/(b*c)) (N/(b*c)), w ((b*c)*k) := by
    intro b hb
    rw [Finset.mem_Icc] at hb
    obtain ⟨hb1, hbU⟩ := hb
    have hVNb : V ≤ N/b := by
      rw [Nat.le_div_iff_mul_le (show 0 < b by omega)]
      calc V * b ≤ V * U := mul_le_mul_left' hbU V
        _ = U * V := Nat.mul_comm V U
        _ ≤ N := hUV
    have hinner : ∑ m ∈ Finset.Ioc (n₀/b) (N/b),
        ((∑ c ∈ m.divisors.filter (· ≤ V),
          (vonMangoldt c : ℝ) : ℝ):ℂ) * w (b*m)
        = ∑ m ∈ Finset.Ioc (n₀/b) (N/b), ∑ c ∈ m.divisors,
            (if c ≤ V then ((vonMangoldt c : ℝ):ℂ) * w (b*m) else 0) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Complex.ofReal_sum, Finset.sum_mul, Finset.sum_filter]
    have hswapped : ∑ m ∈ Finset.Ioc (n₀/b) (N/b), ∑ c ∈ m.divisors,
          (if c ≤ V then ((vonMangoldt c : ℝ):ℂ) * w (b*m) else 0)
        = ∑ c ∈ Finset.Icc 1 (N/b),
            ∑ k ∈ Finset.Ioc ((n₀/b)/c) ((N/b)/c),
              (if c ≤ V then ((vonMangoldt c : ℝ):ℂ) * w (b*(c*k)) else 0) :=
      sum_Ioc_divisors_swap (n₀/b) (N/b)
        (fun c m => if c ≤ V then ((vonMangoldt c : ℝ):ℂ) * w (b*m) else 0)
    have hite : ∀ c ∈ Finset.Icc 1 (N/b),
        ∑ k ∈ Finset.Ioc ((n₀/b)/c) ((N/b)/c),
          (if c ≤ V then ((vonMangoldt c : ℝ):ℂ) * w (b*(c*k)) else 0)
        = if c ≤ V then
            ∑ k ∈ Finset.Ioc ((n₀/b)/c) ((N/b)/c),
              ((vonMangoldt c : ℝ):ℂ) * w (b*(c*k))
          else 0 := by
      intro c _
      by_cases hc : c ≤ V
      · simp only [if_pos hc]
      · simp only [if_neg hc, Finset.sum_const_zero]
    have hfe : (Finset.Icc 1 (N/b)).filter (· ≤ V) = Finset.Icc 1 V := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1c, -⟩, hcV⟩
        exact ⟨h1c, hcV⟩
      · rintro ⟨h1c, hcV⟩
        exact ⟨⟨h1c, le_trans hcV hVNb⟩, hcV⟩
    have hidx : ∀ c ∈ Finset.Icc 1 V,
        ∑ k ∈ Finset.Ioc ((n₀/b)/c) ((N/b)/c),
          ((vonMangoldt c : ℝ):ℂ) * w (b*(c*k))
        = ((vonMangoldt c : ℝ):ℂ)
            * ∑ k ∈ Finset.Ioc (n₀/(b*c)) (N/(b*c)), w ((b*c)*k) := by
      intro c _
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_assoc]
    rw [hinner, hswapped, Finset.sum_congr rfl hite, ← Finset.sum_filter,
      hfe, Finset.sum_congr rfl hidx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    push_cast
    ring
  have hprod : ∑ p ∈ Finset.Icc 1 U ×ˢ Finset.Icc 1 V,
      ((((moebius p.1 : ℤ):ℝ) * (vonMangoldt p.2 : ℝ) : ℝ):ℂ)
        * ∑ k ∈ Finset.Ioc (n₀/(p.1*p.2)) (N/(p.1*p.2)), w ((p.1*p.2)*k)
      = ∑ b ∈ Finset.Icc 1 U, ∑ c ∈ Finset.Icc 1 V,
          ((((moebius b : ℤ):ℝ) * (vonMangoldt c : ℝ) : ℝ):ℂ)
            * ∑ k ∈ Finset.Ioc (n₀/(b*c)) (N/(b*c)), w ((b*c)*k) :=
    Finset.sum_product' (Finset.Icc 1 U) (Finset.Icc 1 V)
      (fun b c => ((((moebius b : ℤ):ℝ) * (vonMangoldt c : ℝ) : ℝ):ℂ)
        * ∑ k ∈ Finset.Ioc (n₀/(b*c)) (N/(b*c)), w ((b*c)*k))
  have hmaps : ∀ p ∈ Finset.Icc 1 U ×ˢ Finset.Icc 1 V,
      p.1 * p.2 ∈ Finset.Icc 1 (U*V) := by
    rintro ⟨b, c⟩ hp
    simp only [Finset.mem_product, Finset.mem_Icc] at hp
    rw [Finset.mem_Icc]
    obtain ⟨⟨hb1, hbU⟩, hc1, hcV⟩ := hp
    exact ⟨Nat.mul_pos hb1 hc1, Nat.mul_le_mul hbU hcV⟩
  rw [Finset.sum_congr rfl hswap, ← hprod,
    ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  simp only [Finset.mem_filter] at hp
  rw [hp.2]


open ArithmeticFunction in
/-- **The Type I' coefficient bound** (Track R, V6b-ii): the regrouped
coefficient is at most `log t` in absolute value — a factorization
`t = b*c` is determined by its `c`-leg, `|μ| ≤ 1`, and
`∑_{c ∣ t} Λ(c) = log t`. -/
theorem vaughan_typeI'_coeff_le (U V t : ℕ) (ht : 1 ≤ t) :
    |∑ p ∈ (Finset.Icc 1 U ×ˢ Finset.Icc 1 V).filter
        (fun p => p.1 * p.2 = t),
      ((moebius p.1 : ℤ):ℝ) * (vonMangoldt p.2 : ℝ)|
      ≤ Real.log t := by
  classical
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have h1 : ∀ p ∈ (Finset.Icc 1 U ×ˢ Finset.Icc 1 V).filter
      (fun p => p.1 * p.2 = t),
      |((moebius p.1 : ℤ):ℝ) * (vonMangoldt p.2 : ℝ)|
        ≤ (vonMangoldt p.2 : ℝ) := by
    intro p _
    rw [abs_mul]
    have hμ : |((moebius p.1 : ℤ):ℝ)| ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := p.1)
      exact_mod_cast this
    have hΛ : |(vonMangoldt p.2 : ℝ)| = (vonMangoldt p.2 : ℝ) :=
      abs_of_nonneg vonMangoldt_nonneg
    rw [hΛ]
    calc |((moebius p.1 : ℤ):ℝ)| * (vonMangoldt p.2 : ℝ)
        ≤ 1 * (vonMangoldt p.2 : ℝ) :=
          mul_le_mul_of_nonneg_right hμ vonMangoldt_nonneg
      _ = (vonMangoldt p.2 : ℝ) := one_mul _
  refine le_trans (Finset.sum_le_sum h1) ?_
  -- push forward along the (injective) `c`-projection into `t.divisors`
  have hinj : Set.InjOn (Prod.snd : ℕ × ℕ → ℕ)
      ↑((Finset.Icc 1 U ×ˢ Finset.Icc 1 V).filter
        (fun p => p.1 * p.2 = t)) := by
    intro p hp p' hp' h
    have hp2 : p ∈ (Finset.Icc 1 U ×ˢ Finset.Icc 1 V).filter
        (fun p => p.1 * p.2 = t) := hp
    have hp2' : p' ∈ (Finset.Icc 1 U ×ˢ Finset.Icc 1 V).filter
        (fun p => p.1 * p.2 = t) := hp'
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      at hp2 hp2'
    have hc1 : 1 ≤ p.2 := hp2.1.2.1
    have hmul : p.1 * p.2 = p'.1 * p.2 := by
      rw [hp2.2, h, hp2'.2]
    have hfst : p.1 = p'.1 :=
      Nat.eq_of_mul_eq_mul_right (by omega) hmul
    exact Prod.ext hfst h
  have himg : ∑ p ∈ (Finset.Icc 1 U ×ˢ Finset.Icc 1 V).filter
      (fun p => p.1 * p.2 = t), (vonMangoldt p.2 : ℝ)
      = ∑ c ∈ ((Finset.Icc 1 U ×ˢ Finset.Icc 1 V).filter
          (fun p => p.1 * p.2 = t)).image Prod.snd,
        (vonMangoldt c : ℝ) := (Finset.sum_image hinj).symm
  have hsub : ((Finset.Icc 1 U ×ˢ Finset.Icc 1 V).filter
      (fun p => p.1 * p.2 = t)).image Prod.snd ⊆ t.divisors := by
    intro c hc
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc] at hc
    obtain ⟨p, ⟨-, hpt⟩, rfl⟩ := hc
    rw [Nat.mem_divisors]
    exact ⟨⟨p.1, by rw [← hpt]; exact Nat.mul_comm p.1 p.2⟩, by omega⟩
  rw [himg]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun c _ _ => vonMangoldt_nonneg)) ?_
  rw [vonMangoldt_sum]


/-- **The hyperbola window is an interval** (Track R, V6c-i): filtering
an `m`-interval by two hyperbola constraints `n₀ < n*m ≤ N`,
`n₀ < n'*m ≤ N` leaves an interval of `m`. -/
theorem hyperbola_filter_eq_Ico (M₁ M₂ n₀ N n n' : ℕ) (hn : 1 ≤ n)
    (hn' : 1 ≤ n') :
    (Finset.Ico M₁ M₂).filter
        (fun m => (n₀ < n*m ∧ n*m ≤ N) ∧ (n₀ < n'*m ∧ n'*m ≤ N))
      = Finset.Ico (max M₁ (max (n₀/n + 1) (n₀/n' + 1)))
          (min M₂ (min (N/n + 1) (N/n' + 1))) := by
  have h1 : ∀ k m : ℕ, 1 ≤ k → (n₀ < k*m ↔ n₀/k + 1 ≤ m) := by
    intro k m hk
    rw [Nat.add_one_le_iff, Nat.div_lt_iff_lt_mul (by omega : 0 < k)]
    exact ⟨fun h => by rwa [Nat.mul_comm k m] at h,
      fun h => by rwa [Nat.mul_comm m k] at h⟩
  have h2 : ∀ k m : ℕ, 1 ≤ k → (k*m ≤ N ↔ m < N/k + 1) := by
    intro k m hk
    rw [Nat.lt_add_one_iff, Nat.le_div_iff_mul_le (by omega : 0 < k)]
    exact ⟨fun h => by rwa [Nat.mul_comm k m] at h,
      fun h => by rwa [Nat.mul_comm m k] at h⟩
  ext m
  simp only [Finset.mem_filter, Finset.mem_Ico, max_le_iff, lt_min_iff]
  constructor
  · rintro ⟨⟨hm1, hm2⟩, ⟨ha1, ha2⟩, hb1, hb2⟩
    exact ⟨⟨hm1, (h1 n m hn).mp ha1, (h1 n' m hn').mp hb1⟩,
      hm2, (h2 n m hn).mp ha2, (h2 n' m hn').mp hb2⟩
  · rintro ⟨⟨hm1, ha1, hb1⟩, hm2, ha2, hb2⟩
    exact ⟨⟨hm1, hm2⟩, ⟨(h1 n m hn).mpr ha1, (h2 n m hn).mpr ha2⟩,
      (h1 n' m hn').mpr hb1, (h2 n' m hn').mpr hb2⟩


/-- **The hyperbola pair bound** (Track R, V6c-i): a conjugate pair of
hyperbola-filtered inner terms summed over the outer interval collapses
to a gap phase sum over a sub-interval, so it is bounded both by the
full interval length and — when the gap frequency is separated from the
integers — by the Kusmin–Landau reciprocal. -/
theorem norm_pair_sum_le_gap_hyperbola (β : ℝ) (M₁ M₂ n₀ N : ℕ)
    (bn : ℕ → ℂ) (hbn : ∀ n, ‖bn n‖ ≤ 1) (n n' : ℕ) (hn : 1 ≤ n)
    (hn' : 1 ≤ n') :
    ‖∑ m ∈ Finset.Ico M₁ M₂,
        ((if n₀ < n*m ∧ n*m ≤ N then bn n else 0) * e ((m:ℝ)*(n:ℝ)*β))
          * (starRingEnd ℂ)
            ((if n₀ < n'*m ∧ n'*m ≤ N then bn n' else 0)
              * e ((m:ℝ)*(n':ℝ)*β))‖
      ≤ min (((M₂ - M₁ : ℕ):ℝ))
          (if 0 < nint (((max n n' - min n n' : ℕ):ℝ)*β)
            then 1 / nint (((max n n' - min n n' : ℕ):ℝ)*β)
            else ((M₂ - M₁ : ℕ):ℝ)) := by
  classical
  have hcollapse : ∀ m : ℕ,
      ((if n₀ < n*m ∧ n*m ≤ N then bn n else 0) * e ((m:ℝ)*(n:ℝ)*β))
        * (starRingEnd ℂ)
          ((if n₀ < n'*m ∧ n'*m ≤ N then bn n' else 0)
            * e ((m:ℝ)*(n':ℝ)*β))
      = if (n₀ < n*m ∧ n*m ≤ N) ∧ (n₀ < n'*m ∧ n'*m ≤ N) then
          (bn n * e ((m:ℝ)*(n:ℝ)*β))
            * (starRingEnd ℂ) (bn n' * e ((m:ℝ)*(n':ℝ)*β))
        else 0 := by
    intro m
    by_cases h1 : n₀ < n*m ∧ n*m ≤ N
    · by_cases h2 : n₀ < n'*m ∧ n'*m ≤ N
      · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
      · rw [if_pos h1, if_neg h2, if_neg (fun hc => h2 hc.2), zero_mul,
          map_zero, mul_zero]
    · rw [if_neg h1, zero_mul, zero_mul, if_neg (fun hc => h1 hc.1)]
  rw [Finset.sum_congr rfl (fun m _ => hcollapse m), ← Finset.sum_filter,
    hyperbola_filter_eq_Ico M₁ M₂ n₀ N n n' hn hn']
  set A := max M₁ (max (n₀/n + 1) (n₀/n' + 1)) with hA
  set B := min M₂ (min (N/n + 1) (N/n' + 1)) with hB
  have hAB1 : M₁ ≤ A := by
    rw [hA]
    exact le_max_left _ _
  have hAB2 : B ≤ M₂ := by
    rw [hB]
    exact min_le_left _ _
  have hgap := norm_pair_sum_le_gap β A B bn hbn n n'
  have htriv : ‖∑ m ∈ Finset.Ico A B,
      e ((m:ℝ)*((max n n' - min n n' : ℕ):ℝ)*β)‖
      ≤ ((M₂ - M₁ : ℕ):ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    have h1 : ∀ m ∈ Finset.Ico A B,
        ‖e ((m:ℝ)*((max n n' - min n n' : ℕ):ℝ)*β)‖ = 1 :=
      fun m _ => norm_e _
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one,
      Nat.card_Ico]
    have hsub : B - A ≤ M₂ - M₁ := tsub_le_tsub hAB2 hAB1
    exact_mod_cast hsub
  refine le_trans hgap (le_min htriv ?_)
  by_cases hpos : 0 < nint (((max n n' - min n n' : ℕ):ℝ)*β)
  · rw [if_pos hpos]
    rcases Nat.lt_or_ge A B with hlt | hge
    · have hBe : B = (B - 1) + 1 := by omega
      have hphase : ∀ m ∈ Finset.Ico A ((B - 1) + 1),
          e ((m:ℝ)*((max n n' - min n n' : ℕ):ℝ)*β)
          = e ((m:ℝ) * (((max n n' - min n n' : ℕ):ℝ)*β)) := by
        intro m _
        congr 1
        ring
      have hkl := norm_sum_e_linear_le
        (β := ((max n n' - min n n' : ℕ):ℝ)*β) hpos A (B - 1) (by omega)
      rw [hBe, Finset.sum_congr rfl hphase]
      exact hkl
    · have hempty : Finset.Ico A B = ∅ := Finset.Ico_eq_empty (by omega)
      rw [hempty]
      simp only [Finset.sum_empty, norm_zero]
      exact div_nonneg zero_le_one hpos.le
  · rw [if_neg hpos]
    exact htriv


/-- **The hyperbola-filtered inner-square bound** (Track R, V6c-ii):
the fixed-set inner-square estimate survives the hyperbola coupling
`n₀ < n*m ≤ N` unchanged — the filter is absorbed into the
coefficients, each conjugate pair collapses to a gap phase sum over a
sub-interval, and the pair-to-gap machinery prices every gap by
`min(length, Kusmin–Landau)`. -/
theorem sum_inner_sq_le_hyperbola (a q : ℕ) (hq : 1 ≤ q)
    (hcop : Nat.Coprime a q) (δ : ℝ) (hδ : |δ| ≤ 1/(q:ℝ)^2)
    (M₁ M₂ KM n₀ N : ℕ) (K : Finset ℕ) (hK : K ⊆ Finset.Icc 1 KM)
    (bn : ℕ → ℂ) (hbn : ∀ n, ‖bn n‖ ≤ 1) :
    ∑ m ∈ Finset.Ico M₁ M₂,
      ‖∑ n ∈ K.filter (fun n => n₀ < n*m ∧ n*m ≤ N),
        bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖^2
      ≤ (K.card:ℝ) * (((M₂ - M₁ : ℕ):ℝ)
          + 2*(((KM:ℝ)/(q:ℝ) + 1)
            *(13*((M₂ - M₁ : ℕ):ℝ)
              + 528*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)))) := by
  classical
  have hfilter : ∀ m : ℕ,
      ∑ n ∈ K.filter (fun n => n₀ < n*m ∧ n*m ≤ N),
        bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))
      = ∑ n ∈ K,
          (if n₀ < n*m ∧ n*m ≤ N then bn n else 0)
            * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ)) := by
    intro m
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hP : n₀ < n*m ∧ n*m ≤ N
    · rw [if_pos hP, if_pos hP]
    · rw [if_neg hP, if_neg hP, zero_mul]
  have hLHS : ∑ m ∈ Finset.Ico M₁ M₂,
      ‖∑ n ∈ K.filter (fun n => n₀ < n*m ∧ n*m ≤ N),
        bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖^2
      = ∑ m ∈ Finset.Ico M₁ M₂,
        ‖∑ n ∈ K,
          (if n₀ < n*m ∧ n*m ≤ N then bn n else 0)
            * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖^2 :=
    Finset.sum_congr rfl fun m _ => by rw [hfilter m]
  rw [hLHS]
  have hexp := sum_norm_sq_expand (Finset.Ico M₁ M₂) K
    (fun m n => (if n₀ < n*m ∧ n*m ≤ N then bn n else 0)
      * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
  refine le_trans hexp ?_
  have hpair : ∀ p ∈ K ×ˢ K,
      ‖∑ m ∈ Finset.Ico M₁ M₂,
        ((if n₀ < p.1*m ∧ p.1*m ≤ N then bn p.1 else 0)
          * e ((m:ℝ)*(p.1:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
          * (starRingEnd ℂ)
            ((if n₀ < p.2*m ∧ p.2*m ≤ N then bn p.2 else 0)
              * e ((m:ℝ)*(p.2:ℝ)*((a:ℝ)/(q:ℝ) + δ)))‖
      ≤ min (((M₂ - M₁ : ℕ):ℝ))
          (if 0 < nint (((max p.1 p.2 - min p.1 p.2 : ℕ):ℝ)
              *((a:ℝ)/(q:ℝ) + δ))
            then 1 / nint (((max p.1 p.2 - min p.1 p.2 : ℕ):ℝ)
              *((a:ℝ)/(q:ℝ) + δ))
            else ((M₂ - M₁ : ℕ):ℝ)) := by
    intro p hp
    rw [Finset.mem_product] at hp
    have h1 := hK hp.1
    have h2 := hK hp.2
    rw [Finset.mem_Icc] at h1 h2
    exact norm_pair_sum_le_gap_hyperbola ((a:ℝ)/(q:ℝ) + δ) M₁ M₂ n₀ N
      bn hbn p.1 p.2 h1.1 h2.1
  refine le_trans (Finset.sum_le_sum hpair) ?_
  have hFnn : ∀ h : ℕ,
      (0:ℝ) ≤ min (((M₂ - M₁ : ℕ):ℝ))
        (if 0 < nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ))
          then 1 / nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ))
          else ((M₂ - M₁ : ℕ):ℝ)) := by
    intro h
    refine le_min (Nat.cast_nonneg _) ?_
    by_cases hpos : 0 < nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ))
    · rw [if_pos hpos]
      exact div_nonneg zero_le_one hpos.le
    · rw [if_neg hpos]
      exact Nat.cast_nonneg _
  refine le_trans (sum_pairs_gap_le K KM hK
    (fun h => min (((M₂ - M₁ : ℕ):ℝ))
      (if 0 < nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ))
        then 1 / nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ))
        else ((M₂ - M₁ : ℕ):ℝ))) hFnn) ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  simp only []
  have hdiag : min (((M₂ - M₁ : ℕ):ℝ))
      (if 0 < nint (((0:ℕ):ℝ)*((a:ℝ)/(q:ℝ) + δ))
        then 1 / nint (((0:ℕ):ℝ)*((a:ℝ)/(q:ℝ) + δ))
        else ((M₂ - M₁ : ℕ):ℝ)) ≤ ((M₂ - M₁ : ℕ):ℝ) :=
    min_le_left _ _
  have hsum : ∑ h ∈ Finset.Icc 1 KM,
      min (((M₂ - M₁ : ℕ):ℝ))
        (if 0 < nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ))
          then 1 / nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ))
          else ((M₂ - M₁ : ℕ):ℝ))
      ≤ ((KM:ℝ)/(q:ℝ) + 1) * (13*((M₂ - M₁ : ℕ):ℝ)
          + 528*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) := by
    have hhalf : ∑ h ∈ Finset.Icc 1 KM,
        min (((M₂ - M₁ : ℕ):ℝ))
          (if 0 < nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ))
            then 1 / nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ))
            else ((M₂ - M₁ : ℕ):ℝ))
        = 2 * ∑ h ∈ Finset.Icc 1 KM,
          (min (((M₂ - M₁ : ℕ):ℝ))
            (if 0 < nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ))
              then 1 / nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ))
              else ((M₂ - M₁ : ℕ):ℝ)) / 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      ring
    have hcc := sum_range_g_const_le a q hq hcop δ hδ KM
      (((M₂ - M₁ : ℕ):ℝ)/2) (by positivity)
      (fun h => min (((M₂ - M₁ : ℕ):ℝ))
        (if 0 < nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ))
          then 1 / nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ))
          else ((M₂ - M₁ : ℕ):ℝ)) / 2)
      (fun h _ => div_nonneg (hFnn h) (by norm_num))
      (fun h _ => by
        have := min_le_left (((M₂ - M₁ : ℕ):ℝ))
          (if 0 < nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ))
            then 1 / nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ))
            else ((M₂ - M₁ : ℕ):ℝ))
        linarith)
      (fun h _ hpos => by
        have hite : (if 0 < nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ))
            then 1 / nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ))
            else ((M₂ - M₁ : ℕ):ℝ))
            = 1 / nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ)) := if_pos hpos
        have hle : min (((M₂ - M₁ : ℕ):ℝ))
            (if 0 < nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ))
              then 1 / nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ))
              else ((M₂ - M₁ : ℕ):ℝ))
            ≤ 1 / nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ)) :=
          le_trans (min_le_right _ _) (le_of_eq hite)
        have hd : 1/(2 * nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
            = (1 / nint ((h:ℝ)*((a:ℝ)/(q:ℝ) + δ)))/2 := by
          rw [div_div]
          ring_nf
        rw [hd]
        linarith)
    rw [hhalf]
    have hring : 2*(((KM:ℝ)/(q:ℝ) + 1)
        *(13*(((M₂ - M₁ : ℕ):ℝ)/2)
          + 264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)))
        = ((KM:ℝ)/(q:ℝ) + 1) * (13*((M₂ - M₁ : ℕ):ℝ)
          + 528*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) := by
      ring
    linarith [hcc, hring.le, hring.ge]
  linarith [hdiag, hsum]


/-- **The hyperbola-filtered `ℓ²`-coefficient Type II estimate**
(Track R, V6c-iii): Cauchy–Schwarz in the outer variable on top of the
hyperbola-filtered inner-square bound — the exact shape the third
Vaughan term takes after its dyadic split. -/
theorem typeII_sum_sq_hyperbola (a q : ℕ) (hq : 1 ≤ q)
    (hcop : Nat.Coprime a q) (δ : ℝ) (hδ : |δ| ≤ 1/(q:ℝ)^2)
    (M₁ M₂ KM n₀ N : ℕ) (K : Finset ℕ) (hK : K ⊆ Finset.Icc 1 KM)
    (am bn : ℕ → ℂ) (hbn : ∀ n, ‖bn n‖ ≤ 1) :
    ‖∑ m ∈ Finset.Ico M₁ M₂,
        am m * ∑ n ∈ K.filter (fun n => n₀ < n*m ∧ n*m ≤ N),
          bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖^2
      ≤ (∑ m ∈ Finset.Ico M₁ M₂, ‖am m‖^2)
        * ((K.card:ℝ) * (((M₂ - M₁ : ℕ):ℝ)
          + 2*(((KM:ℝ)/(q:ℝ) + 1)
            *(13*((M₂ - M₁ : ℕ):ℝ)
              + 528*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1))))) := by
  classical
  have hcs : ‖∑ m ∈ Finset.Ico M₁ M₂,
      am m * ∑ n ∈ K.filter (fun n => n₀ < n*m ∧ n*m ≤ N),
        bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖^2
      ≤ (∑ m ∈ Finset.Ico M₁ M₂, ‖am m‖^2)
        * ∑ m ∈ Finset.Ico M₁ M₂,
          ‖∑ n ∈ K.filter (fun n => n₀ < n*m ∧ n*m ≤ N),
            bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖^2 := by
    have h1 : ‖∑ m ∈ Finset.Ico M₁ M₂,
        am m * ∑ n ∈ K.filter (fun n => n₀ < n*m ∧ n*m ≤ N),
          bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
        ≤ ∑ m ∈ Finset.Ico M₁ M₂,
          ‖am m‖ * ‖∑ n ∈ K.filter (fun n => n₀ < n*m ∧ n*m ≤ N),
            bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ := by
      refine le_trans (norm_sum_le _ _) ?_
      refine Finset.sum_le_sum fun m _ => ?_
      rw [norm_mul]
    have h2 := sum_mul_sq_le_sq_mul_sq (Finset.Ico M₁ M₂)
      (fun m => ‖am m‖)
      (fun m => ‖∑ n ∈ K.filter (fun n => n₀ < n*m ∧ n*m ≤ N),
        bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖)
    have h3 : (0:ℝ) ≤ ∑ m ∈ Finset.Ico M₁ M₂,
        ‖am m‖ * ‖∑ n ∈ K.filter (fun n => n₀ < n*m ∧ n*m ≤ N),
          bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ :=
      Finset.sum_nonneg fun m _ =>
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc ‖∑ m ∈ Finset.Ico M₁ M₂,
        am m * ∑ n ∈ K.filter (fun n => n₀ < n*m ∧ n*m ≤ N),
          bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖^2
        ≤ (∑ m ∈ Finset.Ico M₁ M₂,
            ‖am m‖ * ‖∑ n ∈ K.filter (fun n => n₀ < n*m ∧ n*m ≤ N),
              bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖)^2 := by
          nlinarith [h1, norm_nonneg (∑ m ∈ Finset.Ico M₁ M₂,
            am m * ∑ n ∈ K.filter (fun n => n₀ < n*m ∧ n*m ≤ N),
              bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))), h3]
      _ ≤ (∑ m ∈ Finset.Ico M₁ M₂, ‖am m‖^2)
          * ∑ m ∈ Finset.Ico M₁ M₂,
            ‖∑ n ∈ K.filter (fun n => n₀ < n*m ∧ n*m ≤ N),
              bn n * e ((m:ℝ)*(n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖^2 :=
          h2
  refine le_trans hcs ?_
  refine mul_le_mul_of_nonneg_left ?_ ?_
  · exact sum_inner_sq_le_hyperbola a q hq hcop δ hδ M₁ M₂ KM n₀ N K hK
      bn hbn
  · exact Finset.sum_nonneg fun m _ => sq_nonneg _


/-- **Nonresonant rationals are `1/q`-separated from the integers**
(Track R, V6d-i): if `q ∤ k` then `nint (k/q) ≥ 1/q` — the numerator
`k − q·round(k/q)` is a nonzero integer. -/
theorem nint_natCast_div_lower (k q : ℕ) (hq : 1 ≤ q)
    (hnd : ¬ ((q:ℤ) ∣ (k:ℤ))) :
    1/(q:ℝ) ≤ nint ((k:ℝ)/(q:ℝ)) := by
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  set r := round ((k:ℝ)/(q:ℝ)) with hr
  have hne : (k:ℤ) - (q:ℤ)*r ≠ 0 := by
    intro h
    exact hnd ⟨r, by omega⟩
  have habs : (1:ℝ) ≤ |(((k:ℤ) - (q:ℤ)*r : ℤ):ℝ)| := by
    have h1 : (1:ℤ) ≤ |(k:ℤ) - (q:ℤ)*r| := Int.one_le_abs hne
    exact_mod_cast h1
  have hkey : 1/(q:ℝ) ≤ |(k:ℝ)/(q:ℝ) - (r:ℝ)| := by
    have h2 : (k:ℝ)/(q:ℝ) - (r:ℝ) = (((k:ℤ) - (q:ℤ)*r : ℤ):ℝ)/(q:ℝ) := by
      push_cast
      field_simp
    rw [h2, abs_div, abs_of_pos hq0]
    gcongr
  exact hkey


/-- **The lower half of the first block is never deep** (Track R,
V6d-i): for `1 ≤ d` with `2d ≤ q` and `gcd(a,q) = 1`, the frequency
`d·(a/q + δ)` stays `1/(2q)` away from the integers — the resonance
`q ∣ da` would force `q ∣ d`, impossible below `q`, and the
perturbation `d·|δ| ≤ 1/(2q)` cannot bridge the `1/q` gap.  This is
what lets the first-block near-integer charge be priced at `2N/q`
rather than `N`. -/
theorem nint_block0_lower (a q : ℕ) (hcop : Nat.Coprime a q) (δ : ℝ)
    (hδ : |δ| ≤ 1/(q:ℝ)^2) (d : ℕ) (hd1 : 1 ≤ d) (hd2 : 2*d ≤ q) :
    1/(2*(q:ℝ)) ≤ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) := by
  have hq2 : 2 ≤ q := by omega
  have hq0 : (0:ℝ) < (q:ℝ) := by
    have : (0:ℕ) < q := by omega
    exact_mod_cast this
  have hd0 : (0:ℝ) < (d:ℝ) := by
    have : (0:ℕ) < d := by omega
    exact_mod_cast this
  -- no resonance: `q ∤ d*a`
  have hnd : ¬ ((q:ℤ) ∣ ((d*a : ℕ):ℤ)) := by
    intro h
    have hnat : q ∣ d*a := by exact_mod_cast h
    have hdvd : q ∣ d := (Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.symm hcop)) hnat
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hlow := nint_natCast_div_lower (d*a) q (by omega) hnd
  -- the perturbation is at most `1/(2q)`
  have hpert : |((d*a : ℕ):ℝ)/(q:ℝ) - (d:ℝ)*((a:ℝ)/(q:ℝ) + δ)|
      ≤ 1/(2*(q:ℝ)) := by
    have heq : ((d*a : ℕ):ℝ)/(q:ℝ) - (d:ℝ)*((a:ℝ)/(q:ℝ) + δ)
        = -((d:ℝ)*δ) := by
      push_cast
      field_simp
      ring
    rw [heq, abs_neg, abs_mul, abs_of_pos hd0]
    have hdq : (d:ℝ) ≤ (q:ℝ)/2 := by
      have h2d : ((2*d : ℕ):ℝ) ≤ (q:ℝ) := by exact_mod_cast hd2
      push_cast at h2d
      linarith
    calc (d:ℝ) * |δ| ≤ ((q:ℝ)/2) * (1/(q:ℝ)^2) :=
          mul_le_mul hdq hδ (abs_nonneg _) (by positivity)
      _ = 1/(2*(q:ℝ)) := by
          field_simp
  -- Lipschitz transfer
  have hlip := nint_le_nint_add_abs (((d*a : ℕ):ℝ)/(q:ℝ))
    ((d:ℝ)*((a:ℝ)/(q:ℝ) + δ))
  have hhalf : 1/(2*(q:ℝ)) = 1/(q:ℝ) - 1/(2*(q:ℝ)) := by
    field_simp
    ring
  linarith [hlow, hpert, hlip]


/-- **The refined first-block bound** (Track R, V6d-ii): over
`d ∈ [1, q]` with the per-`d` cap `N/d`, the deep points (at most `13`
of them) all live in `(q/2, q]` where the cap is `2N/q`, and the shell
points are priced through the generic block bound at cap `8q` — so the
first block costs `26N/q + 368q(log 8q + 1)` rather than the
`13N + 264q(log 8q + 1)` of the uniform estimate. -/
theorem sum_block0_g_le (a q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime a q)
    (δ : ℝ) (hδ : |δ| ≤ 1/(q:ℝ)^2) (N : ℝ) (hN : 0 ≤ N) (g : ℕ → ℝ)
    (hg0 : ∀ d ∈ Finset.Icc 1 q, 0 ≤ g d)
    (hgN : ∀ d ∈ Finset.Icc 1 q, g d ≤ N/(d:ℝ))
    (hg2 : ∀ d ∈ Finset.Icc 1 q,
      0 < nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) →
      g d ≤ 1/(2 * nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)))) :
    ∑ d ∈ Finset.Icc 1 q, g d
      ≤ 26*N/(q:ℝ) + 368*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1) := by
  classical
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hset0 : Finset.Ioc (0*q) (0*q + q) = Finset.Icc 1 q := by
    ext d
    rw [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hmem : ∀ d, d ∈ Finset.Ioc (0*q) (0*q + q) →
      d ∈ Finset.Icc 1 q := by
    intro d hd
    rw [hset0] at hd
    exact hd
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 q)
    (fun d : ℕ => nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < 1/(16*(q:ℝ)))]
  -- the deep part: at most 13 points, all in the upper half
  have hdeep : ∑ d ∈ (Finset.Icc 1 q).filter
      (fun d : ℕ => nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < 1/(16*(q:ℝ))), g d
      ≤ 26*N/(q:ℝ) := by
    have hcap : ∀ d ∈ (Finset.Icc 1 q).filter
        (fun d : ℕ => nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < 1/(16*(q:ℝ))),
        g d ≤ 2*N/(q:ℝ) := by
      intro d hd
      simp only [Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, hdq⟩, hdw⟩ := hd
      have h2d : ¬ (2*d ≤ q) := by
        intro hle
        have hlow := nint_block0_lower a q hcop δ hδ d hd1 hle
        have h1 : 1/(16*(q:ℝ)) ≤ 1/(2*(q:ℝ)) := by
          gcongr
          linarith
        linarith [hlow, hdw, h1]
      have hdcast : (q:ℝ) ≤ 2*(d:ℝ) := by
        have hlt : q ≤ 2*d := by omega
        have h2 : ((q:ℕ):ℝ) ≤ ((2*d : ℕ):ℝ) := by exact_mod_cast hlt
        push_cast at h2
        linarith
      have hd0 : (0:ℝ) < (d:ℝ) := by
        have : (0:ℕ) < d := by omega
        exact_mod_cast this
      have hgNd := hgN d (by rw [Finset.mem_Icc]; exact ⟨hd1, hdq⟩)
      have hfrac : N/(d:ℝ) ≤ 2*N/(q:ℝ) := by
        rw [div_le_div_iff₀ hd0 hq0]
        nlinarith [hN, hdcast]
      linarith
    have hcard := card_block_nint_lt_le a q hq hcop δ 0
      (1/(16*(q:ℝ))) (by positivity)
    have hqd2 : (q:ℝ)^2*|δ| ≤ 1 := by
      have h1 := mul_le_mul_of_nonneg_left hδ
        (by positivity : (0:ℝ) ≤ (q:ℝ)^2)
      calc (q:ℝ)^2*|δ| ≤ (q:ℝ)^2*(1/(q:ℝ)^2) := h1
        _ = 1 := by field_simp
    have h16 : 8*(q:ℝ)*(1/(16*(q:ℝ)) + (q:ℝ)*|δ|) + 4 ≤ 13 := by
      have hexp : 8*(q:ℝ)*(1/(16*(q:ℝ))) = 1/2 := by
        field_simp
        ring
      nlinarith [hqd2, hexp]
    rw [hset0] at hcard
    have hcard' : (((Finset.Icc 1 q).filter
        (fun d : ℕ => nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
          < 1/(16*(q:ℝ)))).card : ℝ) ≤ 13 := le_trans hcard h16
    have hsum13 := Finset.sum_le_card_nsmul ((Finset.Icc 1 q).filter
      (fun d : ℕ => nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < 1/(16*(q:ℝ)))) g
      (2*N/(q:ℝ)) hcap
    rw [nsmul_eq_mul] at hsum13
    have h26 : (((Finset.Icc 1 q).filter
        (fun d : ℕ => nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))
          < 1/(16*(q:ℝ)))).card : ℝ) * (2*N/(q:ℝ))
        ≤ 13 * (2*N/(q:ℝ)) :=
      mul_le_mul_of_nonneg_right hcard' (by positivity)
    have hring : (13:ℝ) * (2*N/(q:ℝ)) = 26*N/(q:ℝ) := by
      ring
    linarith [hsum13, h26, hring.le, hring.ge]
  -- the shell part: feed the zero-padded summand through the block bound
  have hshell : ∑ d ∈ (Finset.Icc 1 q).filter
      (fun d : ℕ => ¬ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < 1/(16*(q:ℝ))),
      g d
      ≤ 104*(q:ℝ) + 264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1) := by
    have hcond0 : ∀ d ∈ Finset.Ioc (0*q) (0*q + q),
        0 ≤ (if nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < 1/(16*(q:ℝ))
          then 0 else g d) := by
      intro d hd
      by_cases hP : nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < 1/(16*(q:ℝ))
      · rw [if_pos hP]
      · rw [if_neg hP]
        exact hg0 d (hmem d hd)
    have hcondA : ∀ d ∈ Finset.Ioc (0*q) (0*q + q),
        (if nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < 1/(16*(q:ℝ))
          then 0 else g d) ≤ 8*(q:ℝ) := by
      intro d hd
      by_cases hP : nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < 1/(16*(q:ℝ))
      · rw [if_pos hP]
        positivity
      · rw [if_neg hP]
        push_neg at hP
        have hpos : 0 < nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) :=
          lt_of_lt_of_le (by positivity) hP
        have hKL := hg2 d (hmem d hd) hpos
        have hb : 1/(2 * nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))) ≤ 8*(q:ℝ) := by
          rw [div_le_iff₀ (by positivity)]
          have hmul : 16*(q:ℝ)*(1/(16*(q:ℝ)))
              ≤ 16*(q:ℝ)*nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) :=
            mul_le_mul_of_nonneg_left hP (by positivity)
          have h1 : 16*(q:ℝ)*(1/(16*(q:ℝ))) = 1 := by
            field_simp
          nlinarith [hmul, h1]
        linarith
    have hcond2 : ∀ d ∈ Finset.Ioc (0*q) (0*q + q),
        0 < nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) →
        (if nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < 1/(16*(q:ℝ))
          then 0 else g d)
          ≤ 1/(2 * nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ))) := by
      intro d hd hpos
      by_cases hP : nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < 1/(16*(q:ℝ))
      · rw [if_pos hP]
        exact div_nonneg zero_le_one
          (mul_nonneg (by norm_num) (nint_nonneg _))
      · rw [if_neg hP]
        exact hg2 d (hmem d hd) hpos
    have hg'' := sum_block_g_le a q hq hcop δ hδ 0 (8*(q:ℝ))
      (by positivity)
      (fun d => if nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < 1/(16*(q:ℝ))
        then 0 else g d)
      hcond0 hcondA hcond2
    have hconv : ∑ d ∈ (Finset.Icc 1 q).filter
        (fun d : ℕ => ¬ nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < 1/(16*(q:ℝ))),
        g d
        = ∑ d ∈ Finset.Ioc (0*q) (0*q + q),
          (if nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) < 1/(16*(q:ℝ))
            then 0 else g d) := by
      rw [hset0, Finset.sum_filter]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [ite_not]
    rw [hconv]
    have hring2 : (13:ℝ)*(8*(q:ℝ)) = 104*(q:ℝ) := by
      ring
    linarith [hg'', hring2.le, hring2.ge]
  have hlog : 0 ≤ Real.log (8*(q:ℝ)) := by
    refine Real.log_nonneg ?_
    have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    linarith
  have hql : 0 ≤ (q:ℝ)*Real.log (8*(q:ℝ)) := mul_nonneg hq0.le hlog
  have hexp1 : 264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)
      = 264*((q:ℝ)*Real.log (8*(q:ℝ))) + 264*(q:ℝ) := by
    ring
  have hexp2 : 368*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)
      = 368*((q:ℝ)*Real.log (8*(q:ℝ))) + 368*(q:ℝ) := by
    ring
  linarith [hdeep, hshell, hql, hexp1.le, hexp1.ge, hexp2.le, hexp2.ge]


/-- **The refined counting lemma** (Track R, V6d-iii): the range
assembly with the first block priced through `sum_block0_g_le` — the
standalone `13N` of `sum_range_g_le` becomes `26N/q`, so the whole
divisor sum is `O(N·log D/q + (D/q + 1)·q·log q)`.  This is the form
that saves a power of `log` on the minor arc. -/
theorem sum_range_g_le' (a q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime a q)
    (δ : ℝ) (hδ : |δ| ≤ 1/(q:ℝ)^2) (D : ℕ) (hD : 1 ≤ D)
    (N : ℝ) (hN : 0 ≤ N) (g : ℕ → ℝ)
    (hg0 : ∀ d ∈ Finset.Icc 1 D, 0 ≤ g d)
    (hgN : ∀ d ∈ Finset.Icc 1 D, g d ≤ N/(d:ℝ))
    (hg2 : ∀ d ∈ Finset.Icc 1 D,
      0 < nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) →
      g d ≤ 1/(2 * nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)))) :
    ∑ d ∈ Finset.Icc 1 D, g d
      ≤ 13*N*(Real.log (D:ℝ) + 3)/(q:ℝ)
        + ((D:ℝ)/(q:ℝ) + 1) * (368*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) := by
  classical
  have hq0R : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hq1R : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have h8 : (1:ℝ) ≤ 8*(q:ℝ) := by linarith
  have hlogq : 0 ≤ Real.log (8*(q:ℝ)) := Real.log_nonneg h8
  set g' : ℕ → ℝ := fun d => if d ∈ Finset.Icc 1 D then g d else 0
    with hg'_def
  have hg'0 : ∀ d, 0 ≤ g' d := by
    intro d
    simp only [hg'_def]
    split
    · exact hg0 d (by assumption)
    · exact le_refl 0
  have heqsum : ∑ d ∈ Finset.Icc 1 D, g d
      = ∑ d ∈ Finset.Icc 1 D, g' d := by
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
  -- the refined first block
  have hset0 : Finset.Ioc (0*q) (0*q + q) = Finset.Icc 1 q := by
    ext d
    rw [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hblock0 : ∑ d ∈ Finset.Ioc (0*q) (0*q + q), g' d
      ≤ 26*N/(q:ℝ) + 368*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1) := by
    rw [hset0]
    refine sum_block0_g_le a q hq hcop δ hδ N hN g'
      (fun d _ => hg'0 d) ?_ ?_
    · intro d hd
      simp only [hg'_def]
      split
      · rename_i hdIcc
        exact hgN d hdIcc
      · positivity
    · intro d hd hpos
      simp only [hg'_def]
      split
      · rename_i hdIcc
        exact hg2 d hdIcc hpos
      · positivity
  -- blocks `j ≥ 1`, with per-block cap `N/(jq+1)`
  have hblock : ∀ i ∈ Finset.range (D/q),
      ∑ d ∈ Finset.Ioc ((i+1)*q) ((i+1)*q + q), g' d
      ≤ 13*(N/(((i+1 : ℕ):ℝ)*(q:ℝ) + 1))
        + 264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1) := by
    intro i _
    have hA0 : (0:ℝ) ≤ N/(((i+1 : ℕ):ℝ)*(q:ℝ) + 1) := by positivity
    refine sum_block_g_le a q hq hcop δ hδ (i+1)
      (N/(((i+1 : ℕ):ℝ)*(q:ℝ) + 1)) hA0 g' (fun d _ => hg'0 d) ?_ ?_
    · intro d hd
      rw [Finset.mem_Ioc] at hd
      simp only [hg'_def]
      split
      · rename_i hdIcc
        have hdc : ((i+1 : ℕ):ℝ)*(q:ℝ) + 1 ≤ (d:ℝ) := by
          have h1 : (i+1)*q + 1 ≤ d := by omega
          have h2 : (((i+1)*q + 1 : ℕ):ℝ) ≤ (d:ℝ) := by exact_mod_cast h1
          push_cast at h2
          push_cast
          linarith
        have hd0 : (0:ℝ) < ((i+1 : ℕ):ℝ)*(q:ℝ) + 1 := by positivity
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
  have hsplit : ∑ j ∈ Finset.range (D/q + 1),
      ∑ d ∈ Finset.Ioc (j*q) (j*q + q), g' d
      = (∑ i ∈ Finset.range (D/q),
          ∑ d ∈ Finset.Ioc ((i+1)*q) ((i+1)*q + q), g' d)
        + ∑ d ∈ Finset.Ioc (0*q) (0*q + q), g' d :=
    Finset.sum_range_succ'
      (fun j => ∑ d ∈ Finset.Ioc (j*q) (j*q + q), g' d) (D/q)
  have hsum3 : ∑ i ∈ Finset.range (D/q),
      ∑ d ∈ Finset.Ioc ((i+1)*q) ((i+1)*q + q), g' d
      ≤ ∑ i ∈ Finset.range (D/q),
        (13*(N/(((i+1 : ℕ):ℝ)*(q:ℝ) + 1))
          + 264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) :=
    Finset.sum_le_sum hblock
  have hexpand : ∑ i ∈ Finset.range (D/q),
      (13*(N/(((i+1 : ℕ):ℝ)*(q:ℝ) + 1))
        + 264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1))
      = 13*N * (∑ i ∈ Finset.range (D/q), 1/(((i+1 : ℕ):ℝ)*(q:ℝ) + 1))
        + ((D/q : ℕ):ℝ) * (264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hrest : ∑ i ∈ Finset.range (D/q), 1/(((i+1 : ℕ):ℝ)*(q:ℝ) + 1)
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
  have hC0 : (0:ℝ) ≤ 264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1) := by
    positivity
  have h13N : (0:ℝ) ≤ 13*N := by linarith
  have hJcast : ((D/q : ℕ):ℝ) ≤ (D:ℝ)/(q:ℝ) := Nat.cast_div_le
  have h1 : 13*N * (∑ i ∈ Finset.range (D/q), 1/(((i+1 : ℕ):ℝ)*(q:ℝ) + 1))
      ≤ 13*N*((Real.log (D:ℝ) + 1)/(q:ℝ)) :=
    mul_le_mul_of_nonneg_left hrest h13N
  have h2 : ((D/q : ℕ):ℝ) * (264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1))
      ≤ ((D:ℝ)/(q:ℝ)) * (264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) :=
    mul_le_mul_of_nonneg_right hJcast hC0
  have hqL0 : (0:ℝ) ≤ (q:ℝ)*(Real.log (8*(q:ℝ)) + 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hslack : (0:ℝ)
      ≤ ((D:ℝ)/(q:ℝ))*((q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) :=
    mul_nonneg (by positivity) hqL0
  have hE1 : ((D:ℝ)/(q:ℝ) + 1) * (368*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1))
      = 368*(((D:ℝ)/(q:ℝ))*((q:ℝ)*(Real.log (8*(q:ℝ)) + 1)))
        + 368*((q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) := by
    ring
  have hE2 : ((D:ℝ)/(q:ℝ)) * (264*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1))
      = 264*(((D:ℝ)/(q:ℝ))*((q:ℝ)*(Real.log (8*(q:ℝ)) + 1))) := by
    ring
  have hE3 : 368*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)
      = 368*((q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) := by
    ring
  have hE6 : 13*N*(Real.log (D:ℝ) + 3)/(q:ℝ)
      = 13*N*((Real.log (D:ℝ) + 1)/(q:ℝ)) + 26*N/(q:ℝ) := by
    field_simp
    ring
  rw [heqsum]
  refine le_trans hstep1 ?_
  rw [hstep2, hsplit]
  linarith [hsum3, hexpand.le, hexpand.ge, h1, h2, hblock0, hslack,
    hE1.le, hE1.ge, hE2.le, hE2.ge, hE3.le, hE3.ge, hE6.le, hE6.ge]


/-- **The refined Type I estimate on offset ranges** (Track R,
V6d-iv): the divisor-weighted sum of geometric inner sums over
`(n₀/d, N/d]` through the refined counting lemma — every term saves a
`1/q` or a `D/q`.  This is the shape both Vaughan Type I legs take. -/
theorem typeI_Ioc_sum_le (a q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime a q)
    (δ : ℝ) (hδ : |δ| ≤ 1/(q:ℝ)^2) (D n₀ N : ℕ) (hD : 1 ≤ D)
    (c : ℕ → ℂ) (hc : ∀ d, ‖c d‖ ≤ 1) :
    ∑ d ∈ Finset.Icc 1 D,
        ‖c d * ∑ m ∈ Finset.Ioc (n₀/d) (N/d),
          e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
      ≤ 13*(N:ℝ)*(Real.log (D:ℝ) + 3)/(q:ℝ)
        + 2*((D:ℝ)/(q:ℝ) + 1)
          * (368*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) := by
  classical
  have hcoef : ∀ d : ℕ,
      ‖c d * ∑ m ∈ Finset.Ioc (n₀/d) (N/d),
        e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
      ≤ ‖∑ m ∈ Finset.Ioc (n₀/d) (N/d),
        e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ := by
    intro d
    rw [norm_mul]
    have h2 := hc d
    have h3 := norm_nonneg (∑ m ∈ Finset.Ioc (n₀/d) (N/d),
      e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
    nlinarith [norm_nonneg (c d)]
  have hnorm_le : ∀ d : ℕ, 1 ≤ d →
      ‖∑ m ∈ Finset.Ioc (n₀/d) (N/d),
        e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
      ≤ (N:ℝ)/(d:ℝ) := by
    intro d hd1
    refine le_trans (norm_sum_le _ _) ?_
    have h4 : ∀ m ∈ Finset.Ioc (n₀/d) (N/d),
        ‖e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ = 1 :=
      fun m _ => norm_e _
    rw [Finset.sum_congr rfl h4, Finset.sum_const, nsmul_eq_mul, mul_one,
      Nat.card_Ioc]
    have h5 : (N/d - n₀/d : ℕ) ≤ N/d := Nat.sub_le _ _
    have h6 : ((N/d : ℕ):ℝ) ≤ (N:ℝ)/(d:ℝ) := Nat.cast_div_le
    have h7 : ((N/d - n₀/d : ℕ):ℝ) ≤ ((N/d : ℕ):ℝ) := by exact_mod_cast h5
    linarith
  have hKL : ∀ d : ℕ,
      0 < nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) →
      ‖∑ m ∈ Finset.Ioc (n₀/d) (N/d),
        e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
      ≤ 1 / nint ((d:ℝ) * ((a:ℝ)/(q:ℝ) + δ)) := by
    intro d hpos
    rcases Nat.lt_or_ge (n₀/d) (N/d) with hlt | hge
    · have hIoc : Finset.Ioc (n₀/d) (N/d)
          = Finset.Ico (n₀/d + 1) (N/d + 1) := by
        ext m
        rw [Finset.mem_Ioc, Finset.mem_Ico]
        exact ⟨fun h => ⟨h.1, Nat.lt_add_one_iff.mpr h.2⟩,
          fun h => ⟨h.1, Nat.lt_add_one_iff.mp h.2⟩⟩
      have hphase : ∀ m ∈ Finset.Ico (n₀/d + 1) (N/d + 1),
          e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))
          = e ((m:ℝ) * ((d:ℝ)*((a:ℝ)/(q:ℝ) + δ))) := by
        intro m _
        congr 1
        ring
      have hkl := norm_sum_e_linear_le
        (β := (d:ℝ)*((a:ℝ)/(q:ℝ) + δ)) hpos (n₀/d + 1) (N/d) hlt
      rw [hIoc, Finset.sum_congr rfl hphase]
      exact hkl
    · have hempty : Finset.Ioc (n₀/d) (N/d) = ∅ :=
        Finset.Ioc_eq_empty (not_lt.mpr hge)
      rw [hempty]
      simp only [Finset.sum_empty, norm_zero]
      exact div_nonneg zero_le_one hpos.le
  have hkey : ∀ d ∈ Finset.Icc 1 D,
      ‖c d * ∑ m ∈ Finset.Ioc (n₀/d) (N/d),
        e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
      = 2 * (‖c d * ∑ m ∈ Finset.Ioc (n₀/d) (N/d),
          e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ / 2) := by
    intro d _
    ring
  rw [Finset.sum_congr rfl hkey, ← Finset.mul_sum]
  have hbound := sum_range_g_le' a q hq hcop δ hδ D hD ((N:ℝ)/2)
    (by positivity)
    (fun d => ‖c d * ∑ m ∈ Finset.Ioc (n₀/d) (N/d),
      e ((d:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ / 2)
    (fun d _ => by positivity)
    ?_ ?_
  · have hfin : 2 * (13*((N:ℝ)/2)*(Real.log (D:ℝ) + 3)/(q:ℝ)
        + ((D:ℝ)/(q:ℝ) + 1) * (368*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)))
        = 13*(N:ℝ)*(Real.log (D:ℝ) + 3)/(q:ℝ)
          + 2*((D:ℝ)/(q:ℝ) + 1)
            * (368*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) := by
      field_simp
    linarith [hbound, hfin.le, hfin.ge]
  · intro d hd
    rw [Finset.mem_Icc] at hd
    have h := le_trans (hcoef d) (hnorm_le d hd.1)
    have hbr : ((N:ℝ)/2)/(d:ℝ) = ((N:ℝ)/(d:ℝ))/2 := by
      ring
    linarith [h, hbr.le, hbr.ge]
  · intro d hd hpos
    have h := le_trans (hcoef d) (hKL d hpos)
    have hd' : 1/(2 * nint ((d:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
        = (1 / nint ((d:ℝ)*((a:ℝ)/(q:ℝ) + δ)))/2 := by
      rw [div_div]
      ring_nf
    rw [hd']
    linarith [h]


/-- **The log-weighted Type I estimate** (Track R, V6d-v): the first
Vaughan leg — inner sums carry the weight `log m`, which Abel
summation trades for one factor `2·log N` against the partial-sum gap
function, and the refined counting lemma prices the rest. -/
theorem typeI_abel_sum_le (a q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime a q)
    (δ : ℝ) (hδ : |δ| ≤ 1/(q:ℝ)^2) (D n₀ N : ℕ) (hD : 1 ≤ D)
    (hn₀N : n₀ ≤ N) (c : ℕ → ℂ) (hc : ∀ d, ‖c d‖ ≤ 1) :
    ∑ b ∈ Finset.Icc 1 D,
        ‖c b * ∑ m ∈ Finset.Ioc (n₀/b) (N/b),
          ((Real.log (m:ℝ) : ℝ):ℂ)
            * e ((b:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
      ≤ 2*Real.log (N:ℝ)
        * (13*(N:ℝ)*(Real.log (D:ℝ) + 3)/(q:ℝ)
          + 2*((D:ℝ)/(q:ℝ) + 1)
            * (368*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1))) := by
  classical
  have hq0R : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hφ0 : ∀ m : ℕ, 0 ≤ Real.log (m:ℝ) :=
    fun m => Real.log_natCast_nonneg m
  have hmono : ∀ m : ℕ, Real.log (m:ℝ) ≤ Real.log ((m+1 : ℕ):ℝ) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · norm_num [Real.log_zero, Real.log_one]
    · refine Real.log_le_log ?_ ?_
      · exact_mod_cast hm
      · exact_mod_cast Nat.le_succ m
  -- the uniform bound on all partial phase sums
  have hpartial : ∀ b : ℕ, ∀ t : ℕ, t ≤ N/b →
      ‖∑ m ∈ Finset.Ioc (n₀/b) t,
        e ((b:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
      ≤ min ((N:ℝ)/(b:ℝ))
          (if 0 < nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
            then 1 / nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
            else (N:ℝ)/(b:ℝ)) := by
    intro b t ht2
    have htriv : ‖∑ m ∈ Finset.Ioc (n₀/b) t,
        e ((b:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ ≤ (N:ℝ)/(b:ℝ) := by
      refine le_trans (norm_sum_le _ _) ?_
      have h4 : ∀ m ∈ Finset.Ioc (n₀/b) t,
          ‖e ((b:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ = 1 :=
        fun m _ => norm_e _
      rw [Finset.sum_congr rfl h4, Finset.sum_const, nsmul_eq_mul,
        mul_one, Nat.card_Ioc]
      have h5 : (t - n₀/b : ℕ) ≤ N/b := le_trans (Nat.sub_le _ _) ht2
      have h6 : ((N/b : ℕ):ℝ) ≤ (N:ℝ)/(b:ℝ) := Nat.cast_div_le
      have h7 : ((t - n₀/b : ℕ):ℝ) ≤ ((N/b : ℕ):ℝ) := by
        exact_mod_cast h5
      linarith
    refine le_min htriv ?_
    by_cases hpos : 0 < nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
    · rw [if_pos hpos]
      rcases Nat.lt_or_ge (n₀/b) t with hlt | hge
      · have hIoc : Finset.Ioc (n₀/b) t
            = Finset.Ico (n₀/b + 1) (t + 1) := by
          ext m
          rw [Finset.mem_Ioc, Finset.mem_Ico]
          exact ⟨fun h => ⟨h.1, Nat.lt_add_one_iff.mpr h.2⟩,
            fun h => ⟨h.1, Nat.lt_add_one_iff.mp h.2⟩⟩
        have hphase : ∀ m ∈ Finset.Ico (n₀/b + 1) (t + 1),
            e ((b:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))
            = e ((m:ℝ) * ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))) := by
          intro m _
          congr 1
          ring
        have hkl := norm_sum_e_linear_le
          (β := (b:ℝ)*((a:ℝ)/(q:ℝ) + δ)) hpos (n₀/b + 1) t hlt
        rw [hIoc, Finset.sum_congr rfl hphase]
        exact hkl
      · have hempty : Finset.Ioc (n₀/b) t = ∅ :=
          Finset.Ioc_eq_empty (not_lt.mpr hge)
        rw [hempty]
        simp only [Finset.sum_empty, norm_zero]
        exact div_nonneg zero_le_one hpos.le
    · rw [if_neg hpos]
      exact htriv
  have hF0 : ∀ b : ℕ,
      (0:ℝ) ≤ min ((N:ℝ)/(b:ℝ))
        (if 0 < nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
          then 1 / nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
          else (N:ℝ)/(b:ℝ)) := by
    intro b
    refine le_min (by positivity) ?_
    by_cases hpos : 0 < nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
    · rw [if_pos hpos]
      exact div_nonneg zero_le_one hpos.le
    · rw [if_neg hpos]
      positivity
  -- per-`b` Abel summation
  have hperb : ∀ b ∈ Finset.Icc 1 D,
      ‖c b * ∑ m ∈ Finset.Ioc (n₀/b) (N/b),
        ((Real.log (m:ℝ) : ℝ):ℂ)
          * e ((b:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
      ≤ 2*Real.log (N:ℝ)
        * min ((N:ℝ)/(b:ℝ))
          (if 0 < nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
            then 1 / nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
            else (N:ℝ)/(b:ℝ)) := by
    intro b hb
    rw [Finset.mem_Icc] at hb
    have hcoef : ‖c b * ∑ m ∈ Finset.Ioc (n₀/b) (N/b),
        ((Real.log (m:ℝ) : ℝ):ℂ)
          * e ((b:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
        ≤ ‖∑ m ∈ Finset.Ioc (n₀/b) (N/b),
          ((Real.log (m:ℝ) : ℝ):ℂ)
            * e ((b:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ := by
      rw [norm_mul]
      have h2 := hc b
      have h3 := norm_nonneg (∑ m ∈ Finset.Ioc (n₀/b) (N/b),
        ((Real.log (m:ℝ) : ℝ):ℂ)
          * e ((b:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
      nlinarith [norm_nonneg (c b)]
    have habel := abel_mono_bound (n₀/b) (N/b)
      (Nat.div_le_div_right hn₀N)
      (fun m => Real.log (m:ℝ))
      (fun m => e ((b:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
      (min ((N:ℝ)/(b:ℝ))
        (if 0 < nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
          then 1 / nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
          else (N:ℝ)/(b:ℝ)))
      hφ0 hmono
      (fun t _ ht2 => hpartial b t ht2)
    have hlogNb : Real.log ((N/b : ℕ):ℝ) ≤ Real.log (N:ℝ) := by
      rcases Nat.eq_zero_or_pos (N/b) with h0 | hpos'
      · rw [h0, Nat.cast_zero, Real.log_zero]
        exact Real.log_natCast_nonneg N
      · refine Real.log_le_log ?_ ?_
        · exact_mod_cast hpos'
        · exact_mod_cast Nat.div_le_self N b
    have hstep := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlogNb (by norm_num : (0:ℝ) ≤ 2))
      (hF0 b)
    calc ‖c b * ∑ m ∈ Finset.Ioc (n₀/b) (N/b),
        ((Real.log (m:ℝ) : ℝ):ℂ)
          * e ((b:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
        ≤ ‖∑ m ∈ Finset.Ioc (n₀/b) (N/b),
          ((Real.log (m:ℝ) : ℝ):ℂ)
            * e ((b:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖ := hcoef
      _ ≤ 2 * Real.log ((N/b : ℕ):ℝ)
          * min ((N:ℝ)/(b:ℝ))
            (if 0 < nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
              then 1 / nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
              else (N:ℝ)/(b:ℝ)) := habel
      _ ≤ 2*Real.log (N:ℝ)
          * min ((N:ℝ)/(b:ℝ))
            (if 0 < nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
              then 1 / nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
              else (N:ℝ)/(b:ℝ)) := hstep
  -- sum the per-`b` bounds and price the gap function
  have hsum := Finset.sum_le_sum hperb
  have hpull : ∑ b ∈ Finset.Icc 1 D,
      2*Real.log (N:ℝ)
        * min ((N:ℝ)/(b:ℝ))
          (if 0 < nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
            then 1 / nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
            else (N:ℝ)/(b:ℝ))
      = 2*Real.log (N:ℝ)
        * ∑ b ∈ Finset.Icc 1 D,
          min ((N:ℝ)/(b:ℝ))
            (if 0 < nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
              then 1 / nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
              else (N:ℝ)/(b:ℝ)) :=
    (Finset.mul_sum _ _ _).symm
  have hcount := sum_range_g_le' a q hq hcop δ hδ D hD ((N:ℝ)/2)
    (by positivity)
    (fun b => min ((N:ℝ)/(b:ℝ))
      (if 0 < nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
        then 1 / nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
        else (N:ℝ)/(b:ℝ)) / 2)
    (fun b _ => div_nonneg (hF0 b) (by norm_num))
    ?_ ?_
  · have hhalf : ∑ b ∈ Finset.Icc 1 D,
        min ((N:ℝ)/(b:ℝ))
          (if 0 < nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
            then 1 / nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
            else (N:ℝ)/(b:ℝ))
        = 2 * ∑ b ∈ Finset.Icc 1 D,
          (min ((N:ℝ)/(b:ℝ))
            (if 0 < nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
              then 1 / nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
              else (N:ℝ)/(b:ℝ)) / 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    have hfin : 2 * (13*((N:ℝ)/2)*(Real.log (D:ℝ) + 3)/(q:ℝ)
        + ((D:ℝ)/(q:ℝ) + 1) * (368*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)))
        = 13*(N:ℝ)*(Real.log (D:ℝ) + 3)/(q:ℝ)
          + 2*((D:ℝ)/(q:ℝ) + 1)
            * (368*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) := by
      field_simp
    have hFsum : ∑ b ∈ Finset.Icc 1 D,
        min ((N:ℝ)/(b:ℝ))
          (if 0 < nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
            then 1 / nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
            else (N:ℝ)/(b:ℝ))
        ≤ 13*(N:ℝ)*(Real.log (D:ℝ) + 3)/(q:ℝ)
          + 2*((D:ℝ)/(q:ℝ) + 1)
            * (368*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) := by
      rw [hhalf]
      linarith [hcount, hfin.le, hfin.ge]
    have hlogN0 : (0:ℝ) ≤ Real.log (N:ℝ) := Real.log_natCast_nonneg N
    have hmul := mul_le_mul_of_nonneg_left hFsum
      (by linarith : (0:ℝ) ≤ 2*Real.log (N:ℝ))
    calc ∑ b ∈ Finset.Icc 1 D,
        ‖c b * ∑ m ∈ Finset.Ioc (n₀/b) (N/b),
          ((Real.log (m:ℝ) : ℝ):ℂ)
            * e ((b:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
        ≤ ∑ b ∈ Finset.Icc 1 D,
          2*Real.log (N:ℝ)
            * min ((N:ℝ)/(b:ℝ))
              (if 0 < nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
                then 1 / nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
                else (N:ℝ)/(b:ℝ)) := hsum
      _ = 2*Real.log (N:ℝ)
          * ∑ b ∈ Finset.Icc 1 D,
            min ((N:ℝ)/(b:ℝ))
              (if 0 < nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
                then 1 / nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
                else (N:ℝ)/(b:ℝ)) := hpull
      _ ≤ 2*Real.log (N:ℝ)
          * (13*(N:ℝ)*(Real.log (D:ℝ) + 3)/(q:ℝ)
            + 2*((D:ℝ)/(q:ℝ) + 1)
              * (368*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1))) := hmul
  · intro b hb
    rw [Finset.mem_Icc] at hb
    have h := min_le_left ((N:ℝ)/(b:ℝ))
      (if 0 < nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
        then 1 / nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
        else (N:ℝ)/(b:ℝ))
    have hbr : ((N:ℝ)/2)/(b:ℝ) = ((N:ℝ)/(b:ℝ))/2 := by
      ring
    linarith [h, hbr.le, hbr.ge]
  · intro b hb hpos
    have hite : (if 0 < nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
        then 1 / nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ))
        else (N:ℝ)/(b:ℝ))
        = 1 / nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ)) := if_pos hpos
    have h := le_trans (min_le_right ((N:ℝ)/(b:ℝ)) _) (le_of_eq hite)
    have hd' : 1/(2 * nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
        = (1 / nint ((b:ℝ)*((a:ℝ)/(q:ℝ) + δ)))/2 := by
      rw [div_div]
      ring_nf
    rw [hd']
    linarith [h]


/-- **Möbius tail sums are divisor-bounded** (Track R, V6d-vi): the
Type II outer coefficients of Vaughan's identity, `∑_{d ∣ m, d > U}
μ(d)`, have absolute value at most `τ(m)` — the tail variant of
`abs_moebius_partial_le_tau`. -/
theorem abs_moebius_tail_le_tau (U m : ℕ) :
    |∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
      ((ArithmeticFunction.moebius b : ℤ):ℝ)|
      ≤ ((m.divisors.card : ℝ)) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have h1 : ∀ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
      |((ArithmeticFunction.moebius b : ℤ):ℝ)| ≤ 1 := by
    intro b _
    have := ArithmeticFunction.abs_moebius_le_one (n := b)
    exact_mod_cast this
  refine le_trans (Finset.sum_le_sum h1) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast Finset.card_filter_le _ _


/-- **The Type II range swap** (Track R, V6d-vi): the third Vaughan
term, with the modulus `c` outer, re-indexed with the free variable
`m` outer — the hyperbola constraint `n₀ < c·m ≤ N` becomes the inner
filter, exactly the shape the coupled Type II estimate consumes. -/
theorem sum_typeII_swap {M : Type*} [AddCommMonoid M] (V n₀ N : ℕ)
    (h : ℕ → ℕ → M) :
    ∑ c ∈ (Finset.Icc 1 N).filter (fun c => ¬ c ≤ V),
        ∑ m ∈ Finset.Ioc (n₀/c) (N/c), h c m
      = ∑ m ∈ Finset.Icc 1 (N/(V+1)),
          ∑ c ∈ (Finset.Ioc V N).filter
            (fun c => n₀ < c*m ∧ c*m ≤ N), h c m := by
  classical
  have hdiv1 : ∀ c m : ℕ, 1 ≤ c → (n₀/c < m ↔ n₀ < c*m) := by
    intro c m hc
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < c)]
    exact ⟨fun hx => by rwa [Nat.mul_comm m c] at hx,
      fun hx => by rwa [Nat.mul_comm c m] at hx⟩
  have hdiv2 : ∀ c m : ℕ, 1 ≤ c → (m ≤ N/c ↔ c*m ≤ N) := by
    intro c m hc
    rw [Nat.le_div_iff_mul_le (by omega : 0 < c)]
    exact ⟨fun hx => by rwa [Nat.mul_comm m c] at hx,
      fun hx => by rwa [Nat.mul_comm c m] at hx⟩
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => Sigma.mk p.2 p.1)
    (fun p => Sigma.mk p.2 p.1) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨c, m⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_Ioc] at hp ⊢
    obtain ⟨⟨⟨hc1, hcN⟩, hcV⟩, hm1, hm2⟩ := hp
    have ha := (hdiv1 c m hc1).mp hm1
    have hb := (hdiv2 c m hc1).mp hm2
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ha, hb⟩
    · by_contra hm0
      have hz : m = 0 := by omega
      rw [hz, Nat.mul_zero] at ha
      omega
    · rw [Nat.le_div_iff_mul_le (by omega : 0 < V+1)]
      calc m * (V+1) ≤ m * c := mul_le_mul_left' (by omega) m
        _ = c * m := Nat.mul_comm m c
        _ ≤ N := hb
    · omega
    · exact hcN
  · rintro ⟨m, c⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_Ioc] at hq ⊢
    obtain ⟨⟨hm1, hmB⟩, ⟨hcV, hcN⟩, ha, hb⟩ := hq
    have hc1 : 1 ≤ c := by omega
    refine ⟨⟨⟨hc1, hcN⟩, by omega⟩, ?_, ?_⟩
    · exact (hdiv1 c m hc1).mpr ha
    · exact (hdiv2 c m hc1).mpr hb
  · rintro ⟨c, m⟩ _
    rfl
  · rintro ⟨m, c⟩ _
    rfl
  · rintro ⟨c, m⟩ _
    rfl


/-- **The dyadic telescope** (Track R, V6d-vi): capped dyadic blocks
`(min(2^j·V, N), min(2^{j+1}·V, N)]` tile `(min(V,N), min(2^J·V, N)]`. -/
theorem sum_dyadic_tiling {M : Type*} [AddCommMonoid M] (V N J : ℕ)
    (f : ℕ → M) :
    ∑ j ∈ Finset.range J,
        ∑ c ∈ Finset.Ioc (min (2^j * V) N) (min (2^(j+1) * V) N), f c
      = ∑ c ∈ Finset.Ioc (min V N) (min (2^J * V) N), f c := by
  induction J with
  | zero =>
    simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : min V N ≤ min (2^J * V) N := by
      have hVp : V ≤ 2^J * V := by
        calc V = 1 * V := (one_mul V).symm
          _ ≤ 2^J * V := mul_le_mul_right' Nat.one_le_two_pow V
      exact min_le_min hVp le_rfl
    have h2 : min (2^J * V) N ≤ min (2^(J+1) * V) N := by
      have hpow : 2^J * V ≤ 2^(J+1) * V :=
        mul_le_mul_right'
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J)) V
      exact min_le_min hpow le_rfl
    exact Finset.sum_Ioc_consecutive f h1 h2


/-- **`log₂ N + 1` dyadic blocks suffice** (Track R, V6d-vi). -/
theorem lt_two_pow_log2_succ (N : ℕ) (hN : N ≠ 0) :
    N < 2^(N.log2 + 1) :=
  (Nat.log2_lt hN).mp (Nat.lt_succ_self _)


/-- **The dyadic block count is `O(log N)`** (Track R, V6d-vi):
`log₂ N + 1 ≤ 3·log N` for `N ≥ 2`. -/
theorem natLog2_succ_le_log (N : ℕ) (hN : 2 ≤ N) :
    ((N.log2 + 1 : ℕ):ℝ) ≤ 3*Real.log (N:ℝ) := by
  have hN0 : N ≠ 0 := by omega
  have hpow : (2:ℝ)^(N.log2) ≤ (N:ℝ) := by
    have h := Nat.log2_self_le hN0
    exact_mod_cast h
  have hlogpow : (N.log2 : ℝ) * Real.log 2 ≤ Real.log (N:ℝ) := by
    have h1 : Real.log ((2:ℝ)^(N.log2)) ≤ Real.log (N:ℝ) :=
      Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at h1
  have hc := Real.log_two_gt_d9
  have hL : Real.log 2 ≤ Real.log (N:ℝ) := by
    refine Real.log_le_log (by norm_num) ?_
    exact_mod_cast hN
  have hL0 : (0:ℝ) ≤ Real.log (N:ℝ) := by
    linarith
  have hk0 : (0:ℝ) ≤ (N.log2 : ℝ) := Nat.cast_nonneg _
  push_cast
  nlinarith [hlogpow, hc, hL, hL0, hk0]


open ArithmeticFunction in
/-- **The block outer range** (Track R, V6d-vi): in the swapped third
Vaughan term, restricted to one dyadic block, the outer sum lives on
`[U+1, N/(2^j·V+1)]` — below `U+1` the Möbius tail coefficient is an
empty sum, and beyond the cap the hyperbola filter is empty.  In
particular blocks with `2^j·V ≥ N/U` contribute nothing. -/
theorem typeII_block_outer_restrict (U V n₀ N j : ℕ) (F : ℕ → ℕ → ℂ) :
    ∑ m ∈ Finset.Icc 1 (N/(V+1)),
        ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
          ((moebius b : ℤ):ℝ) : ℝ):ℂ)
          * ∑ c ∈ (Finset.Ioc (min (2^j * V) N)
              (min (2^(j+1) * V) N)).filter
              (fun c => n₀ < c*m ∧ c*m ≤ N), F c m
      = ∑ m ∈ Finset.Ico (U+1) (N/(2^j * V + 1) + 1),
          ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
            ((moebius b : ℤ):ℝ) : ℝ):ℂ)
            * ∑ c ∈ (Finset.Ioc (min (2^j * V) N)
                (min (2^(j+1) * V) N)).filter
                (fun c => n₀ < c*m ∧ c*m ≤ N), F c m := by
  classical
  have hsub : Finset.Ico (U+1) (N/(2^j * V + 1) + 1)
      ⊆ Finset.Icc 1 (N/(V+1)) := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    rw [Finset.mem_Icc]
    refine ⟨by omega, ?_⟩
    have h1 : m ≤ N/(2^j * V + 1) := Nat.lt_add_one_iff.mp hm.2
    refine le_trans h1 (Nat.div_le_div_left ?_ (by omega))
    have hV : V ≤ 2^j * V := by
      calc V = 1 * V := (one_mul V).symm
        _ ≤ 2^j * V := mul_le_mul_right' Nat.one_le_two_pow V
    omega
  have hzero : ∀ m ∈ Finset.Icc 1 (N/(V+1)),
      m ∉ Finset.Ico (U+1) (N/(2^j * V + 1) + 1) →
      ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
        ((moebius b : ℤ):ℝ) : ℝ):ℂ)
        * ∑ c ∈ (Finset.Ioc (min (2^j * V) N)
            (min (2^(j+1) * V) N)).filter
            (fun c => n₀ < c*m ∧ c*m ≤ N), F c m = 0 := by
    intro m hm hnot
    rw [Finset.mem_Icc] at hm
    rw [Finset.mem_Ico] at hnot
    push_neg at hnot
    by_cases hU : m ≤ U
    · have hemp : m.divisors.filter (fun b => ¬ b ≤ U) = ∅ := by
        refine Finset.filter_false_of_mem fun b hb => ?_
        rw [Nat.mem_divisors] at hb
        have hbm : b ≤ m := Nat.le_of_dvd (by omega) hb.1
        omega
      rw [hemp, Finset.sum_empty, Complex.ofReal_zero, zero_mul]
    · have hm2 : N/(2^j * V + 1) < m := by
        have := hnot (by omega)
        omega
      have hNlt : N < m * (2^j * V + 1) :=
        (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).mp hm2
      have hemp : (Finset.Ioc (min (2^j * V) N)
          (min (2^(j+1) * V) N)).filter
          (fun c => n₀ < c*m ∧ c*m ≤ N) = ∅ := by
        refine Finset.filter_false_of_mem fun c hc => ?_
        rw [Finset.mem_Ioc] at hc
        rintro ⟨-, hcmN⟩
        rcases le_or_gt (2^j * V) N with hAN | hAN
        · have hc1 : 2^j * V + 1 ≤ c := by
            have h := hc.1
            rw [min_eq_left hAN] at h
            omega
          exact absurd (calc N < m * (2^j * V + 1) := hNlt
            _ ≤ m * c := mul_le_mul_left' hc1 m
            _ = c * m := Nat.mul_comm m c
            _ ≤ N := hcmN) (lt_irrefl N)
        · have hcN : N < c := by
            have h := hc.1
            rw [min_eq_right hAN.le] at h
            exact h
          exact absurd (calc N < c := hcN
            _ = c * 1 := (mul_one c).symm
            _ ≤ c * m := mul_le_mul_left' (by omega) c
            _ ≤ N := hcmN) (lt_irrefl N)
      rw [hemp, Finset.sum_empty, mul_zero]
  exact (Finset.sum_subset hsub hzero).symm


open ArithmeticFunction in
/-- **The per-block Type II bound** (Track R, V6d-vi): one dyadic
block of the swapped third Vaughan term, squared — the Möbius-tail
`ℓ²`-mass is `≤ MJ(1+log N)³` by the divisor-square moment, the
normalized `Λ`-coefficients are unit, and the coupled Type II estimate
prices the block at scale `C = 2^j·V`, outer length `MJ = N/(C+1)`. -/
theorem typeII_block_sq_le (a q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime a q)
    (δ : ℝ) (hδ : |δ| ≤ 1/(q:ℝ)^2) (U V n₀ N j : ℕ) (hN : 2 ≤ N) :
    ‖∑ m ∈ Finset.Ico (U+1) (N/(2^j * V + 1) + 1),
        ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
          ((moebius b : ℤ):ℝ) : ℝ):ℂ)
          * ∑ c ∈ (Finset.Ioc (min (2^j * V) N)
              (min (2^(j+1) * V) N)).filter
              (fun c => n₀ < c*m ∧ c*m ≤ N),
            (if c ≤ N then
              ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
              * e ((m:ℝ)*(c:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖^2
      ≤ ((N/(2^j * V + 1) : ℕ):ℝ) * (1 + Real.log (N:ℝ))^3
        * (((2^j * V : ℕ):ℝ)
          * (((N/(2^j * V + 1) : ℕ):ℝ)
            + 2*(((2*((2^j * V : ℕ):ℝ))/(q:ℝ) + 1)
              *(13*((N/(2^j * V + 1) : ℕ):ℝ)
                + 528*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1))))) := by
  classical
  have hq0R : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hlogN : 0 < Real.log (N:ℝ) := by
    refine Real.log_pos ?_
    exact_mod_cast hN
  have hlog8q : (0:ℝ) ≤ Real.log (8*(q:ℝ)) := by
    refine Real.log_nonneg ?_
    have hq1R : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    linarith
  have hbn : ∀ c : ℕ,
      ‖(if c ≤ N then
        ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)‖ ≤ 1 := by
    intro c
    by_cases hc : c ≤ N
    · rw [if_pos hc, Complex.norm_real, Real.norm_eq_abs]
      have h1 : (0:ℝ) ≤ vonMangoldt c := vonMangoldt_nonneg
      have h2 : vonMangoldt c ≤ Real.log (N:ℝ) := by
        refine le_trans vonMangoldt_le_log ?_
        rcases Nat.eq_zero_or_pos c with rfl | hc0
        · rw [Nat.cast_zero, Real.log_zero]
          exact hlogN.le
        · refine Real.log_le_log ?_ ?_
          · exact_mod_cast hc0
          · exact_mod_cast hc
      rw [abs_of_nonneg (by positivity)]
      rw [div_le_one hlogN]
      exact h2
    · rw [if_neg hc, norm_zero]
      norm_num
  have hK : Finset.Ioc (min (2^j * V) N) (min (2^(j+1) * V) N)
      ⊆ Finset.Icc 1 (min (2^(j+1) * V) N) := by
    intro c hc
    rw [Finset.mem_Ioc] at hc
    rw [Finset.mem_Icc]
    omega
  have happ := typeII_sum_sq_hyperbola a q hq hcop δ hδ
    (U+1) (N/(2^j * V + 1) + 1) (min (2^(j+1) * V) N) n₀ N
    (Finset.Ioc (min (2^j * V) N) (min (2^(j+1) * V) N)) hK
    (fun m => ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
      ((moebius b : ℤ):ℝ) : ℝ):ℂ))
    (fun c => if c ≤ N then
      ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
    hbn
  have hmass : ∑ m ∈ Finset.Ico (U+1) (N/(2^j * V + 1) + 1),
      ‖((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
        ((moebius b : ℤ):ℝ) : ℝ):ℂ)‖^2
      ≤ ((N/(2^j * V + 1) : ℕ):ℝ) * (1 + Real.log (N:ℝ))^3 := by
    rcases Nat.eq_zero_or_pos (N/(2^j * V + 1)) with hMJ0 | hMJpos
    · rw [hMJ0]
      have hemp : Finset.Ico (U+1) (0 + 1) = ∅ :=
        Finset.Ico_eq_empty (by omega)
      rw [hemp, Finset.sum_empty]
      norm_num
    · have hsub2 : Finset.Ico (U+1) (N/(2^j * V + 1) + 1)
          ⊆ Finset.Icc 1 (N/(2^j * V + 1)) := by
        intro m hm
        rw [Finset.mem_Ico] at hm
        rw [Finset.mem_Icc]
        exact ⟨by omega, Nat.lt_add_one_iff.mp hm.2⟩
      have hterm : ∀ m ∈ Finset.Ico (U+1) (N/(2^j * V + 1) + 1),
          ‖((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
            ((moebius b : ℤ):ℝ) : ℝ):ℂ)‖^2
            ≤ ((m.divisors.card : ℝ))^2 := by
        intro m _
        rw [Complex.norm_real, Real.norm_eq_abs]
        have h1 := abs_moebius_tail_le_tau U m
        have h2 : (0:ℝ) ≤ |∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
            ((moebius b : ℤ):ℝ)| := abs_nonneg _
        nlinarith [h1, h2]
      refine le_trans (Finset.sum_le_sum hterm) ?_
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub2
        (fun m _ _ => sq_nonneg _)) ?_
      refine le_trans (sum_tau_sq_le (N/(2^j * V + 1)) hMJpos) ?_
      have hMJN : Real.log ((N/(2^j * V + 1) : ℕ):ℝ)
          ≤ Real.log (N:ℝ) := by
        refine Real.log_le_log ?_ ?_
        · exact_mod_cast hMJpos
        · exact_mod_cast Nat.div_le_self N (2^j * V + 1)
      have h1log : (0:ℝ) ≤ 1 + Real.log ((N/(2^j * V + 1) : ℕ):ℝ) := by
        have := Real.log_natCast_nonneg (N/(2^j * V + 1))
        linarith
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      refine pow_le_pow_left₀ h1log (by linarith) 3
  have hcard : ((Finset.Ioc (min (2^j * V) N)
      (min (2^(j+1) * V) N)).card : ℝ) ≤ ((2^j * V : ℕ):ℝ) := by
    rw [Nat.card_Ioc]
    have hnat : min (2^(j+1) * V) N - min (2^j * V) N ≤ 2^j * V := by
      have h2A : 2^(j+1) * V = 2 * (2^j * V) := by
        rw [pow_succ]
        ring
      rw [h2A]
      generalize (2^j * V) = A
      omega
    exact_mod_cast hnat
  have hlen : (((N/(2^j * V + 1) + 1) - (U+1) : ℕ):ℝ)
      ≤ ((N/(2^j * V + 1) : ℕ):ℝ) := by
    have h : (N/(2^j * V + 1) + 1) - (U+1) ≤ N/(2^j * V + 1) := by
      generalize (N/(2^j * V + 1)) = MJ
      omega
    exact_mod_cast h
  have hKM : ((min (2^(j+1) * V) N : ℕ):ℝ) ≤ 2*((2^j * V : ℕ):ℝ) := by
    have h : min (2^(j+1) * V) N ≤ 2 * (2^j * V) := by
      have h2A : 2^(j+1) * V = 2 * (2^j * V) := by
        rw [pow_succ]
        ring
      rw [← h2A]
      exact min_le_left _ _
    exact_mod_cast h
  refine le_trans happ ?_
  gcongr


open ArithmeticFunction in
/-- **The Type II reshape** (Track R, V6d-vi): the raw third Vaughan
term equals `log N` times the swapped, `Λ/log N`-normalized `m`-outer
form — the shape the dyadic block machinery prices. -/
theorem typeII_reshape (U V n₀ N : ℕ) (hN : 2 ≤ N) (w : ℕ → ℂ) :
    (∑ c ∈ (Finset.Icc 1 N).filter (fun c => ¬ c ≤ V),
        ((vonMangoldt c : ℝ):ℂ)
          * ∑ m ∈ Finset.Ioc (n₀/c) (N/c),
            ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
              ((moebius b : ℤ):ℝ) : ℝ):ℂ) * w (c*m))
      = ((Real.log (N:ℝ) : ℝ):ℂ)
        * ∑ m ∈ Finset.Icc 1 (N/(V+1)),
            ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
              ((moebius b : ℤ):ℝ) : ℝ):ℂ)
              * ∑ c ∈ (Finset.Ioc V N).filter
                  (fun c => n₀ < c*m ∧ c*m ≤ N),
                (if c ≤ N then
                  ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
                  * w (c*m) := by
  classical
  have hlogN : (0:ℝ) < Real.log (N:ℝ) := by
    refine Real.log_pos ?_
    exact_mod_cast hN
  have h1 : (∑ c ∈ (Finset.Icc 1 N).filter (fun c => ¬ c ≤ V),
      ((vonMangoldt c : ℝ):ℂ)
        * ∑ m ∈ Finset.Ioc (n₀/c) (N/c),
          ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
            ((moebius b : ℤ):ℝ) : ℝ):ℂ) * w (c*m))
      = ∑ c ∈ (Finset.Icc 1 N).filter (fun c => ¬ c ≤ V),
          ∑ m ∈ Finset.Ioc (n₀/c) (N/c),
            ((vonMangoldt c : ℝ):ℂ)
              * (((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
                ((moebius b : ℤ):ℝ) : ℝ):ℂ) * w (c*m)) :=
    Finset.sum_congr rfl fun c _ => Finset.mul_sum _ _ _
  have h2 : (∑ c ∈ (Finset.Icc 1 N).filter (fun c => ¬ c ≤ V),
      ∑ m ∈ Finset.Ioc (n₀/c) (N/c),
        ((vonMangoldt c : ℝ):ℂ)
          * (((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
            ((moebius b : ℤ):ℝ) : ℝ):ℂ) * w (c*m)))
      = ∑ m ∈ Finset.Icc 1 (N/(V+1)),
          ∑ c ∈ (Finset.Ioc V N).filter
            (fun c => n₀ < c*m ∧ c*m ≤ N),
            ((vonMangoldt c : ℝ):ℂ)
              * (((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
                ((moebius b : ℤ):ℝ) : ℝ):ℂ) * w (c*m)) :=
    sum_typeII_swap V n₀ N
      (fun c m => ((vonMangoldt c : ℝ):ℂ)
        * (((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
          ((moebius b : ℤ):ℝ) : ℝ):ℂ) * w (c*m)))
  have h3 : ∀ m ∈ Finset.Icc 1 (N/(V+1)),
      ∑ c ∈ (Finset.Ioc V N).filter
        (fun c => n₀ < c*m ∧ c*m ≤ N),
        ((vonMangoldt c : ℝ):ℂ)
          * (((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
            ((moebius b : ℤ):ℝ) : ℝ):ℂ) * w (c*m))
      = ((Real.log (N:ℝ) : ℝ):ℂ)
        * (((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
          ((moebius b : ℤ):ℝ) : ℝ):ℂ)
          * ∑ c ∈ (Finset.Ioc V N).filter
              (fun c => n₀ < c*m ∧ c*m ≤ N),
            (if c ≤ N then
              ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
              * w (c*m)) := by
    intro m _
    have hstep : ∀ c ∈ (Finset.Ioc V N).filter
        (fun c => n₀ < c*m ∧ c*m ≤ N),
        ((vonMangoldt c : ℝ):ℂ)
          * (((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
            ((moebius b : ℤ):ℝ) : ℝ):ℂ) * w (c*m))
        = ((Real.log (N:ℝ) : ℝ):ℂ)
          * (((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
            ((moebius b : ℤ):ℝ) : ℝ):ℂ)
            * ((if c ≤ N then
              ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
              * w (c*m))) := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hc
      rw [if_pos hc.1.2]
      have hval : ((vonMangoldt c : ℝ):ℂ)
          = ((Real.log (N:ℝ) : ℝ):ℂ)
            * ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) := by
        rw [← Complex.ofReal_mul]
        congr 1
        field_simp
      rw [hval]
      ring
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [h1, h2, Finset.sum_congr rfl h3, ← Finset.mul_sum]


open ArithmeticFunction in
/-- **The uniform per-block bound** (Track R, V6d-vi): every dyadic
block of the swapped, normalized third Vaughan term — good or empty —
is at most `√X⋆`, where `X⋆` collects the hyperbola saving
`C·MJ ≤ N` over the good range `V ≤ C ≲ N/U`. -/
theorem typeII_block_le_sqrt (a q : ℕ) (hq : 1 ≤ q)
    (hcop : Nat.Coprime a q) (δ : ℝ) (hδ : |δ| ≤ 1/(q:ℝ)^2)
    (U V n₀ N j : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) (hN : 2 ≤ N) :
    ‖∑ m ∈ Finset.Icc 1 (N/(V+1)),
        ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
          ((moebius b : ℤ):ℝ) : ℝ):ℂ)
          * ∑ c ∈ (Finset.Ioc (min (2^j * V) N)
              (min (2^(j+1) * V) N)).filter
              (fun c => n₀ < c*m ∧ c*m ≤ N),
            (if c ≤ N then
              ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
              * e ((m:ℝ)*(c:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
      ≤ Real.sqrt ((1 + Real.log (N:ℝ))^3
          * (27*(N:ℝ)^2/(V:ℝ) + 52*(N:ℝ)^2/(q:ℝ)
            + 2112*(N:ℝ)^2*(Real.log (8*(q:ℝ)) + 1)/(U:ℝ)
            + 1056*(N:ℝ)*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1))) := by
  classical
  have hrw : ∑ m ∈ Finset.Icc 1 (N/(V+1)),
      ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
        ((moebius b : ℤ):ℝ) : ℝ):ℂ)
        * ∑ c ∈ (Finset.Ioc (min (2^j * V) N)
            (min (2^(j+1) * V) N)).filter
            (fun c => n₀ < c*m ∧ c*m ≤ N),
          (if c ≤ N then
            ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
            * e ((m:ℝ)*(c:ℝ)*((a:ℝ)/(q:ℝ) + δ))
      = ∑ m ∈ Finset.Ico (U+1) (N/(2^j * V + 1) + 1),
          ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
            ((moebius b : ℤ):ℝ) : ℝ):ℂ)
            * ∑ c ∈ (Finset.Ioc (min (2^j * V) N)
                (min (2^(j+1) * V) N)).filter
                (fun c => n₀ < c*m ∧ c*m ≤ N),
              (if c ≤ N then
                ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
                * e ((m:ℝ)*(c:ℝ)*((a:ℝ)/(q:ℝ) + δ)) :=
    typeII_block_outer_restrict U V n₀ N j
      (fun c m => (if c ≤ N then
        ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
        * e ((m:ℝ)*(c:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
  rw [hrw]
  rcases Nat.lt_or_ge (N/(2^j * V + 1)) (U+1) with hbad | hgood
  · have hemp : Finset.Ico (U+1) (N/(2^j * V + 1) + 1) = ∅ := by
      refine Finset.Ico_eq_empty ?_
      intro hlt
      have h1 : N/(2^j * V + 1) + 1 ≤ U + 1 :=
        Nat.succ_le_succ (Nat.lt_succ_iff.mp hbad)
      exact absurd (lt_of_lt_of_le hlt h1) (lt_irrefl _)
    rw [hemp, Finset.sum_empty, norm_zero]
    exact Real.sqrt_nonneg _
  · have hsq := typeII_block_sq_le a q hq hcop δ hδ U V n₀ N j hN
    have hlogN : (0:ℝ) < Real.log (N:ℝ) :=
      Real.log_pos (by exact_mod_cast hN)
    have hL0 : (0:ℝ) ≤ Real.log (8*(q:ℝ)) + 1 := by
      have h8 : (1:ℝ) ≤ 8*(q:ℝ) := by
        have : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
        linarith
      have := Real.log_nonneg h8
      linarith
    have hUR : (1:ℝ) ≤ (U:ℝ) := by exact_mod_cast hU
    have hVR : (1:ℝ) ≤ (V:ℝ) := by exact_mod_cast hV
    have hNR : (0:ℝ) < (N:ℝ) := by
      have h0 : 0 < N := by omega
      exact_mod_cast h0
    have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
    have hf2n : 2^j * V * (N/(2^j * V + 1)) ≤ N := by
      calc 2^j * V * (N/(2^j * V + 1))
          ≤ (2^j * V + 1) * (N/(2^j * V + 1)) :=
            mul_le_mul_right' (Nat.le_succ _) _
        _ = (N/(2^j * V + 1)) * (2^j * V + 1) := Nat.mul_comm _ _
        _ ≤ N := Nat.div_mul_le_self N (2^j * V + 1)
    have hf2 : ((2^j * V : ℕ):ℝ) * ((N/(2^j * V + 1) : ℕ):ℝ) ≤ (N:ℝ) := by
      exact_mod_cast hf2n
    have hf3n : N/(2^j * V + 1) ≤ N/V := by
      refine Nat.div_le_div_left ?_ (by omega)
      have hVC : V ≤ 2^j * V := by
        calc V = 1 * V := (one_mul V).symm
          _ ≤ 2^j * V := mul_le_mul_right' Nat.one_le_two_pow V
      exact le_trans hVC (Nat.le_succ _)
    have hf3 : ((N/(2^j * V + 1) : ℕ):ℝ) ≤ (N:ℝ)/(V:ℝ) := by
      refine le_trans ?_ Nat.cast_div_le
      exact_mod_cast hf3n
    have hgoodn : (U+1) * (2^j * V + 1) ≤ N :=
      (Nat.le_div_iff_mul_le (Nat.succ_pos _)).mp hgood
    have hf4 : ((2^j * V : ℕ):ℝ) ≤ (N:ℝ)/(U:ℝ) := by
      rw [le_div_iff₀ (by linarith : (0:ℝ) < (U:ℝ))]
      have hn : 2^j * V * U ≤ N := by
        calc 2^j * V * U = U * (2^j * V) := Nat.mul_comm _ _
          _ ≤ U * (2^j * V) + (2^j * V + U + 1) := Nat.le_add_right _ _
          _ = (U+1) * (2^j * V + 1) := by ring
          _ ≤ N := hgoodn
      exact_mod_cast hn
    have ht14 : 27*(((2^j * V : ℕ):ℝ) * ((N/(2^j * V + 1) : ℕ):ℝ))
        * ((N/(2^j * V + 1) : ℕ):ℝ)
        ≤ 27*(N:ℝ)*((N:ℝ)/(V:ℝ)) := by
      gcongr
    have ht2 : 52*((((2^j * V : ℕ):ℝ) * ((N/(2^j * V + 1) : ℕ):ℝ))
        * (((2^j * V : ℕ):ℝ) * ((N/(2^j * V + 1) : ℕ):ℝ)))/(q:ℝ)
        ≤ 52*((N:ℝ)*(N:ℝ))/(q:ℝ) := by
      gcongr
    have ht3 : 2112*(((2^j * V : ℕ):ℝ)
        * (((2^j * V : ℕ):ℝ) * ((N/(2^j * V + 1) : ℕ):ℝ))
        * (Real.log (8*(q:ℝ)) + 1))
        ≤ 2112*(((N:ℝ)/(U:ℝ)) * (N:ℝ) * (Real.log (8*(q:ℝ)) + 1)) := by
      gcongr
    have ht5 : 1056*((((2^j * V : ℕ):ℝ) * ((N/(2^j * V + 1) : ℕ):ℝ))
        * ((q:ℝ) * (Real.log (8*(q:ℝ)) + 1)))
        ≤ 1056*((N:ℝ) * ((q:ℝ) * (Real.log (8*(q:ℝ)) + 1))) := by
      gcongr
    have hinner : ((N/(2^j * V + 1) : ℕ):ℝ)
        * (((2^j * V : ℕ):ℝ)
          * (((N/(2^j * V + 1) : ℕ):ℝ)
            + 2*(((2*((2^j * V : ℕ):ℝ))/(q:ℝ) + 1)
              *(13*((N/(2^j * V + 1) : ℕ):ℝ)
                + 528*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)))))
        ≤ 27*(N:ℝ)^2/(V:ℝ) + 52*(N:ℝ)^2/(q:ℝ)
          + 2112*(N:ℝ)^2*(Real.log (8*(q:ℝ)) + 1)/(U:ℝ)
          + 1056*(N:ℝ)*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1) := by
      have hq' : (q:ℝ) ≠ 0 := ne_of_gt hqR
      have hexp : ((N/(2^j * V + 1) : ℕ):ℝ)
          * (((2^j * V : ℕ):ℝ)
            * (((N/(2^j * V + 1) : ℕ):ℝ)
              + 2*(((2*((2^j * V : ℕ):ℝ))/(q:ℝ) + 1)
                *(13*((N/(2^j * V + 1) : ℕ):ℝ)
                  + 528*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)))))
          = 27*(((2^j * V : ℕ):ℝ) * ((N/(2^j * V + 1) : ℕ):ℝ))
              * ((N/(2^j * V + 1) : ℕ):ℝ)
            + 52*((((2^j * V : ℕ):ℝ) * ((N/(2^j * V + 1) : ℕ):ℝ))
              * (((2^j * V : ℕ):ℝ) * ((N/(2^j * V + 1) : ℕ):ℝ)))/(q:ℝ)
            + 2112*(((2^j * V : ℕ):ℝ)
              * (((2^j * V : ℕ):ℝ) * ((N/(2^j * V + 1) : ℕ):ℝ))
              * (Real.log (8*(q:ℝ)) + 1))
            + 1056*((((2^j * V : ℕ):ℝ) * ((N/(2^j * V + 1) : ℕ):ℝ))
              * ((q:ℝ) * (Real.log (8*(q:ℝ)) + 1))) := by
        field_simp
        ring
      rw [hexp]
      refine le_trans
        (add_le_add (add_le_add (add_le_add ht14 ht2) ht3) ht5)
        (le_of_eq ?_)
      ring
    have hpow3 : (0:ℝ) ≤ (1 + Real.log (N:ℝ))^3 :=
      pow_nonneg (by linarith) 3
    have hXle : ((N/(2^j * V + 1) : ℕ):ℝ) * (1 + Real.log (N:ℝ))^3
        * (((2^j * V : ℕ):ℝ)
          * (((N/(2^j * V + 1) : ℕ):ℝ)
            + 2*(((2*((2^j * V : ℕ):ℝ))/(q:ℝ) + 1)
              *(13*((N/(2^j * V + 1) : ℕ):ℝ)
                + 528*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)))))
        ≤ (1 + Real.log (N:ℝ))^3
          * (27*(N:ℝ)^2/(V:ℝ) + 52*(N:ℝ)^2/(q:ℝ)
            + 2112*(N:ℝ)^2*(Real.log (8*(q:ℝ)) + 1)/(U:ℝ)
            + 1056*(N:ℝ)*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)) := by
      have hre : ((N/(2^j * V + 1) : ℕ):ℝ) * (1 + Real.log (N:ℝ))^3
          * (((2^j * V : ℕ):ℝ)
            * (((N/(2^j * V + 1) : ℕ):ℝ)
              + 2*(((2*((2^j * V : ℕ):ℝ))/(q:ℝ) + 1)
                *(13*((N/(2^j * V + 1) : ℕ):ℝ)
                  + 528*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)))))
          = (1 + Real.log (N:ℝ))^3
            * (((N/(2^j * V + 1) : ℕ):ℝ)
              * (((2^j * V : ℕ):ℝ)
                * (((N/(2^j * V + 1) : ℕ):ℝ)
                  + 2*(((2*((2^j * V : ℕ):ℝ))/(q:ℝ) + 1)
                    *(13*((N/(2^j * V + 1) : ℕ):ℝ)
                      + 528*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)))))) := by
        ring
      rw [hre]
      exact mul_le_mul_of_nonneg_left hinner hpow3
    have hnn := norm_nonneg (∑ m ∈ Finset.Ico (U+1)
        (N/(2^j * V + 1) + 1),
      ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
        ((moebius b : ℤ):ℝ) : ℝ):ℂ)
        * ∑ c ∈ (Finset.Ioc (min (2^j * V) N)
            (min (2^(j+1) * V) N)).filter
            (fun c => n₀ < c*m ∧ c*m ≤ N),
          (if c ≤ N then
            ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
            * e ((m:ℝ)*(c:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
    calc ‖∑ m ∈ Finset.Ico (U+1) (N/(2^j * V + 1) + 1),
        ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
          ((moebius b : ℤ):ℝ) : ℝ):ℂ)
          * ∑ c ∈ (Finset.Ioc (min (2^j * V) N)
              (min (2^(j+1) * V) N)).filter
              (fun c => n₀ < c*m ∧ c*m ≤ N),
            (if c ≤ N then
              ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
              * e ((m:ℝ)*(c:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
        = Real.sqrt (‖∑ m ∈ Finset.Ico (U+1) (N/(2^j * V + 1) + 1),
            ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
              ((moebius b : ℤ):ℝ) : ℝ):ℂ)
              * ∑ c ∈ (Finset.Ioc (min (2^j * V) N)
                  (min (2^(j+1) * V) N)).filter
                  (fun c => n₀ < c*m ∧ c*m ≤ N),
                (if c ≤ N then
                  ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
                  * e ((m:ℝ)*(c:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖^2) :=
          (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((1 + Real.log (N:ℝ))^3
          * (27*(N:ℝ)^2/(V:ℝ) + 52*(N:ℝ)^2/(q:ℝ)
            + 2112*(N:ℝ)^2*(Real.log (8*(q:ℝ)) + 1)/(U:ℝ)
            + 1056*(N:ℝ)*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1))) :=
          Real.sqrt_le_sqrt (le_trans hsq hXle)


open ArithmeticFunction in
/-- **The Type II total** (Track R, V6d-vi): the raw third Vaughan
term at the exponential weight is at most `3·(log N)²·√X⋆` — reshape,
retile dyadically, and pay `√X⋆` for each of the `≤ 3 log N` blocks. -/
theorem typeII_total_le (a q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime a q)
    (δ : ℝ) (hδ : |δ| ≤ 1/(q:ℝ)^2) (U V n₀ N : ℕ)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hVN : V ≤ N) (hN : 2 ≤ N) :
    ‖∑ c ∈ (Finset.Icc 1 N).filter (fun c => ¬ c ≤ V),
        ((vonMangoldt c : ℝ):ℂ)
          * ∑ m ∈ Finset.Ioc (n₀/c) (N/c),
            ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
              ((moebius b : ℤ):ℝ) : ℝ):ℂ)
              * e (((c*m : ℕ):ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
      ≤ 3*(Real.log (N:ℝ))^2
        * Real.sqrt ((1 + Real.log (N:ℝ))^3
          * (27*(N:ℝ)^2/(V:ℝ) + 52*(N:ℝ)^2/(q:ℝ)
            + 2112*(N:ℝ)^2*(Real.log (8*(q:ℝ)) + 1)/(U:ℝ)
            + 1056*(N:ℝ)*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1))) := by
  classical
  have hlogN : (0:ℝ) < Real.log (N:ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  -- reshape into the normalized `m`-outer form
  have hre : (∑ c ∈ (Finset.Icc 1 N).filter (fun c => ¬ c ≤ V),
      ((vonMangoldt c : ℝ):ℂ)
        * ∑ m ∈ Finset.Ioc (n₀/c) (N/c),
          ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
            ((moebius b : ℤ):ℝ) : ℝ):ℂ)
            * e (((c*m : ℕ):ℝ)*((a:ℝ)/(q:ℝ) + δ)))
      = ((Real.log (N:ℝ) : ℝ):ℂ)
        * ∑ m ∈ Finset.Icc 1 (N/(V+1)),
            ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
              ((moebius b : ℤ):ℝ) : ℝ):ℂ)
              * ∑ c ∈ (Finset.Ioc V N).filter
                  (fun c => n₀ < c*m ∧ c*m ≤ N),
                (if c ≤ N then
                  ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
                  * e (((c*m : ℕ):ℝ)*((a:ℝ)/(q:ℝ) + δ)) :=
    typeII_reshape U V n₀ N hN
      (fun n => e ((n:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
  rw [hre, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hlogN]
  -- fix the phase into outer-times-inner form
  have hphase : ∑ m ∈ Finset.Icc 1 (N/(V+1)),
      ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
        ((moebius b : ℤ):ℝ) : ℝ):ℂ)
        * ∑ c ∈ (Finset.Ioc V N).filter
            (fun c => n₀ < c*m ∧ c*m ≤ N),
          (if c ≤ N then
            ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
            * e (((c*m : ℕ):ℝ)*((a:ℝ)/(q:ℝ) + δ))
      = ∑ m ∈ Finset.Icc 1 (N/(V+1)),
          ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
            ((moebius b : ℤ):ℝ) : ℝ):ℂ)
            * ∑ c ∈ (Finset.Ioc V N).filter
                (fun c => n₀ < c*m ∧ c*m ≤ N),
              (if c ≤ N then
                ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
                * e ((m:ℝ)*(c:ℝ)*((a:ℝ)/(q:ℝ) + δ)) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 2
    push_cast
    ring
  rw [hphase]
  -- retile the modulus range dyadically
  have hminV : min V N = V := min_eq_left hVN
  have hminJ : min (2^(N.log2 + 1) * V) N = N := by
    refine min_eq_right ?_
    have h1 : N < 2^(N.log2 + 1) := lt_two_pow_log2_succ N (by omega)
    calc N ≤ 2^(N.log2 + 1) := h1.le
      _ = 2^(N.log2 + 1) * 1 := (mul_one _).symm
      _ ≤ 2^(N.log2 + 1) * V := mul_le_mul_left' hV _
  have htile : ∀ m : ℕ,
      ∑ c ∈ (Finset.Ioc V N).filter
          (fun c => n₀ < c*m ∧ c*m ≤ N),
        (if c ≤ N then
          ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
          * e ((m:ℝ)*(c:ℝ)*((a:ℝ)/(q:ℝ) + δ))
      = ∑ j ∈ Finset.range (N.log2 + 1),
          ∑ c ∈ (Finset.Ioc (min (2^j * V) N)
              (min (2^(j+1) * V) N)).filter
              (fun c => n₀ < c*m ∧ c*m ≤ N),
            (if c ≤ N then
              ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
              * e ((m:ℝ)*(c:ℝ)*((a:ℝ)/(q:ℝ) + δ)) := by
    intro m
    rw [Finset.sum_filter]
    have h := sum_dyadic_tiling V N (N.log2 + 1)
      (fun c => if n₀ < c*m ∧ c*m ≤ N then
        (if c ≤ N then
          ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
          * e ((m:ℝ)*(c:ℝ)*((a:ℝ)/(q:ℝ) + δ)) else 0)
    rw [hminV, hminJ] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun m _ => by rw [htile m] :
    ∀ m ∈ Finset.Icc 1 (N/(V+1)),
      ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
        ((moebius b : ℤ):ℝ) : ℝ):ℂ)
        * ∑ c ∈ (Finset.Ioc V N).filter
            (fun c => n₀ < c*m ∧ c*m ≤ N),
          (if c ≤ N then
            ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
            * e ((m:ℝ)*(c:ℝ)*((a:ℝ)/(q:ℝ) + δ))
      = ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
          ((moebius b : ℤ):ℝ) : ℝ):ℂ)
          * ∑ j ∈ Finset.range (N.log2 + 1),
            ∑ c ∈ (Finset.Ioc (min (2^j * V) N)
                (min (2^(j+1) * V) N)).filter
                (fun c => n₀ < c*m ∧ c*m ≤ N),
              (if c ≤ N then
                ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
                * e ((m:ℝ)*(c:ℝ)*((a:ℝ)/(q:ℝ) + δ)))]
  -- push the coefficient in, swap the sums
  have hswap : ∑ m ∈ Finset.Icc 1 (N/(V+1)),
      ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
        ((moebius b : ℤ):ℝ) : ℝ):ℂ)
        * ∑ j ∈ Finset.range (N.log2 + 1),
          ∑ c ∈ (Finset.Ioc (min (2^j * V) N)
              (min (2^(j+1) * V) N)).filter
              (fun c => n₀ < c*m ∧ c*m ≤ N),
            (if c ≤ N then
              ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
              * e ((m:ℝ)*(c:ℝ)*((a:ℝ)/(q:ℝ) + δ))
      = ∑ j ∈ Finset.range (N.log2 + 1),
          ∑ m ∈ Finset.Icc 1 (N/(V+1)),
            ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
              ((moebius b : ℤ):ℝ) : ℝ):ℂ)
              * ∑ c ∈ (Finset.Ioc (min (2^j * V) N)
                  (min (2^(j+1) * V) N)).filter
                  (fun c => n₀ < c*m ∧ c*m ≤ N),
                (if c ≤ N then
                  ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
                  * e ((m:ℝ)*(c:ℝ)*((a:ℝ)/(q:ℝ) + δ)) := by
    rw [Finset.sum_congr rfl (fun m _ => Finset.mul_sum _ _ _)]
    exact Finset.sum_comm
  rw [hswap]
  -- price each block and count
  have hsqrt0 : (0:ℝ) ≤ Real.sqrt ((1 + Real.log (N:ℝ))^3
      * (27*(N:ℝ)^2/(V:ℝ) + 52*(N:ℝ)^2/(q:ℝ)
        + 2112*(N:ℝ)^2*(Real.log (8*(q:ℝ)) + 1)/(U:ℝ)
        + 1056*(N:ℝ)*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1))) :=
    Real.sqrt_nonneg _
  have hblocks : ‖∑ j ∈ Finset.range (N.log2 + 1),
      ∑ m ∈ Finset.Icc 1 (N/(V+1)),
        ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
          ((moebius b : ℤ):ℝ) : ℝ):ℂ)
          * ∑ c ∈ (Finset.Ioc (min (2^j * V) N)
              (min (2^(j+1) * V) N)).filter
              (fun c => n₀ < c*m ∧ c*m ≤ N),
            (if c ≤ N then
              ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
              * e ((m:ℝ)*(c:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
      ≤ ((N.log2 + 1 : ℕ):ℝ)
        * Real.sqrt ((1 + Real.log (N:ℝ))^3
          * (27*(N:ℝ)^2/(V:ℝ) + 52*(N:ℝ)^2/(q:ℝ)
            + 2112*(N:ℝ)^2*(Real.log (8*(q:ℝ)) + 1)/(U:ℝ)
            + 1056*(N:ℝ)*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1))) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hper : ∀ j ∈ Finset.range (N.log2 + 1),
        ‖∑ m ∈ Finset.Icc 1 (N/(V+1)),
          ((∑ b ∈ m.divisors.filter (fun b => ¬ b ≤ U),
            ((moebius b : ℤ):ℝ) : ℝ):ℂ)
            * ∑ c ∈ (Finset.Ioc (min (2^j * V) N)
                (min (2^(j+1) * V) N)).filter
                (fun c => n₀ < c*m ∧ c*m ≤ N),
              (if c ≤ N then
                ((vonMangoldt c / Real.log (N:ℝ) : ℝ):ℂ) else 0)
                * e ((m:ℝ)*(c:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
        ≤ Real.sqrt ((1 + Real.log (N:ℝ))^3
          * (27*(N:ℝ)^2/(V:ℝ) + 52*(N:ℝ)^2/(q:ℝ)
            + 2112*(N:ℝ)^2*(Real.log (8*(q:ℝ)) + 1)/(U:ℝ)
            + 1056*(N:ℝ)*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1))) :=
      fun j _ => typeII_block_le_sqrt a q hq hcop δ hδ U V n₀ N j
        hU hV hN
    refine le_trans (Finset.sum_le_sum hper) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine le_trans (mul_le_mul_of_nonneg_left hblocks hlogN.le) ?_
  have hJ : ((N.log2 + 1 : ℕ):ℝ) ≤ 3*Real.log (N:ℝ) :=
    natLog2_succ_le_log N hN
  have hfin : Real.log (N:ℝ)
      * (((N.log2 + 1 : ℕ):ℝ)
        * Real.sqrt ((1 + Real.log (N:ℝ))^3
          * (27*(N:ℝ)^2/(V:ℝ) + 52*(N:ℝ)^2/(q:ℝ)
            + 2112*(N:ℝ)^2*(Real.log (8*(q:ℝ)) + 1)/(U:ℝ)
            + 1056*(N:ℝ)*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1))))
      ≤ Real.log (N:ℝ)
        * ((3*Real.log (N:ℝ))
          * Real.sqrt ((1 + Real.log (N:ℝ))^3
            * (27*(N:ℝ)^2/(V:ℝ) + 52*(N:ℝ)^2/(q:ℝ)
              + 2112*(N:ℝ)^2*(Real.log (8*(q:ℝ)) + 1)/(U:ℝ)
              + 1056*(N:ℝ)*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)))) := by
    refine mul_le_mul_of_nonneg_left ?_ hlogN.le
    exact mul_le_mul_of_nonneg_right hJ hsqrt0
  refine le_trans hfin (le_of_eq ?_)
  ring


open ArithmeticFunction in
/-- **The master minor-arc bound** (Track R, V6d-vii): Vaughan's
identity over `(n₀, N]` at the exponential weight, all three legs
priced through the refined counting machinery — every right-hand term
carries a `1/q`, a `D/q`, or the Type II square root. -/
theorem vaughan_minor_arc_le (a q : ℕ) (hq : 1 ≤ q)
    (hcop : Nat.Coprime a q) (δ : ℝ) (hδ : |δ| ≤ 1/(q:ℝ)^2)
    (U V n₀ N : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) (hVn₀ : V < n₀)
    (hUV : U*V ≤ N) (hn₀N : n₀ ≤ N) (hN : 2 ≤ N) :
    ‖∑ n ∈ Finset.Ioc n₀ N, ((vonMangoldt n : ℝ):ℂ)
        * e ((n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
      ≤ 2*Real.log (N:ℝ)
          * (13*(N:ℝ)*(Real.log (U:ℝ) + 3)/(q:ℝ)
            + 2*((U:ℝ)/(q:ℝ) + 1)
              * (368*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)))
        + Real.log (N:ℝ)
          * (13*(N:ℝ)*(Real.log ((U*V : ℕ):ℝ) + 3)/(q:ℝ)
            + 2*(((U*V : ℕ):ℝ)/(q:ℝ) + 1)
              * (368*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)))
        + 3*(Real.log (N:ℝ))^2
          * Real.sqrt ((1 + Real.log (N:ℝ))^3
            * (27*(N:ℝ)^2/(V:ℝ) + 52*(N:ℝ)^2/(q:ℝ)
              + 2112*(N:ℝ)^2*(Real.log (8*(q:ℝ)) + 1)/(U:ℝ)
              + 1056*(N:ℝ)*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1))) := by
  classical
  have hlogN : (0:ℝ) < Real.log (N:ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hUN : U ≤ N := by
    calc U = U*1 := (mul_one U).symm
      _ ≤ U*V := mul_le_mul_left' hV U
      _ ≤ N := hUV
  have hvw := vaughan_weighted U V n₀ N hVn₀
    (fun n => e ((n:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
  rw [hvw]
  refine le_trans (le_trans (norm_add_le _ _)
    (add_le_add (norm_sub_le _ _) le_rfl)) ?_
  refine add_le_add (add_le_add ?_ ?_) ?_
  · -- Leg 1: the log-weighted Type I term
    have hfil : (Finset.Icc 1 N).filter (· ≤ U) = Finset.Icc 1 U := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1b, -⟩, hbU⟩
        exact ⟨h1b, hbU⟩
      · rintro ⟨h1b, hbU⟩
        exact ⟨⟨h1b, le_trans hbU hUN⟩, hbU⟩
    rw [hfil]
    have hph : ∀ b ∈ Finset.Icc 1 U,
        (((moebius b : ℤ):ℝ):ℂ)
          * ∑ m ∈ Finset.Ioc (n₀/b) (N/b),
            ((Real.log (m:ℝ) : ℝ):ℂ)
              * e (((b*m : ℕ):ℝ)*((a:ℝ)/(q:ℝ) + δ))
        = (((moebius b : ℤ):ℝ):ℂ)
          * ∑ m ∈ Finset.Ioc (n₀/b) (N/b),
            ((Real.log (m:ℝ) : ℝ):ℂ)
              * e ((b:ℝ)*(m:ℝ)*((a:ℝ)/(q:ℝ) + δ)) := by
      intro b _
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      congr 2
      push_cast
      ring
    rw [Finset.sum_congr rfl hph]
    refine le_trans (norm_sum_le _ _) ?_
    refine typeI_abel_sum_le a q hq hcop δ hδ U n₀ N hU hn₀N
      (fun b => (((moebius b : ℤ):ℝ):ℂ)) ?_
    intro b
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := b)
  · -- Leg 2: the regrouped Type I' term
    rw [vaughan_typeI'_regroup U V n₀ N hU hV hUV
      (fun n => e ((n:ℝ)*((a:ℝ)/(q:ℝ) + δ)))]
    have hsplit : ∀ t ∈ Finset.Icc 1 (U*V),
        ((∑ p ∈ (Finset.Icc 1 U ×ˢ Finset.Icc 1 V).filter
            (fun p => p.1 * p.2 = t),
          ((moebius p.1 : ℤ):ℝ) * (vonMangoldt p.2 : ℝ) : ℝ):ℂ)
          * ∑ k ∈ Finset.Ioc (n₀/t) (N/t),
            e (((t*k : ℕ):ℝ)*((a:ℝ)/(q:ℝ) + δ))
        = ((Real.log (N:ℝ) : ℝ):ℂ)
          * ((((∑ p ∈ (Finset.Icc 1 U ×ˢ Finset.Icc 1 V).filter
              (fun p => p.1 * p.2 = t),
            ((moebius p.1 : ℤ):ℝ) * (vonMangoldt p.2 : ℝ))
              / Real.log (N:ℝ) : ℝ):ℂ)
            * ∑ k ∈ Finset.Ioc (n₀/t) (N/t),
              e ((t:ℝ)*(k:ℝ)*((a:ℝ)/(q:ℝ) + δ))) := by
      intro t _
      have hcoe : ((∑ p ∈ (Finset.Icc 1 U ×ˢ Finset.Icc 1 V).filter
          (fun p => p.1 * p.2 = t),
          ((moebius p.1 : ℤ):ℝ) * (vonMangoldt p.2 : ℝ) : ℝ):ℂ)
          = ((Real.log (N:ℝ) : ℝ):ℂ)
            * (((∑ p ∈ (Finset.Icc 1 U ×ˢ Finset.Icc 1 V).filter
                (fun p => p.1 * p.2 = t),
              ((moebius p.1 : ℤ):ℝ) * (vonMangoldt p.2 : ℝ))
                / Real.log (N:ℝ) : ℝ):ℂ) := by
        rw [← Complex.ofReal_mul]
        congr 1
        field_simp
      have hphk : ∑ k ∈ Finset.Ioc (n₀/t) (N/t),
          e (((t*k : ℕ):ℝ)*((a:ℝ)/(q:ℝ) + δ))
          = ∑ k ∈ Finset.Ioc (n₀/t) (N/t),
            e ((t:ℝ)*(k:ℝ)*((a:ℝ)/(q:ℝ) + δ)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        congr 1
        push_cast
        ring
      rw [hcoe, hphk, mul_assoc]
    rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogN]
    refine mul_le_mul_of_nonneg_left ?_ hlogN.le
    refine le_trans (norm_sum_le _ _) ?_
    refine typeI_Ioc_sum_le a q hq hcop δ hδ (U*V) n₀ N
      (Nat.mul_pos hU hV)
      (fun t => (((∑ p ∈ (Finset.Icc 1 U ×ˢ Finset.Icc 1 V).filter
          (fun p => p.1 * p.2 = t),
        ((moebius p.1 : ℤ):ℝ) * (vonMangoldt p.2 : ℝ))
          / Real.log (N:ℝ) : ℝ):ℂ)) ?_
    intro t
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos hlogN, div_le_one hlogN]
    rcases Nat.eq_zero_or_pos t with rfl | ht1
    · have hemp : (Finset.Icc 1 U ×ˢ Finset.Icc 1 V).filter
          (fun p => p.1 * p.2 = 0) = ∅ := by
        refine Finset.filter_false_of_mem fun p hp => ?_
        rw [Finset.mem_product] at hp
        obtain ⟨hp1, hp2⟩ := hp
        rw [Finset.mem_Icc] at hp1 hp2
        intro h0
        have hpos : 0 < p.1 * p.2 :=
          Nat.mul_pos (by omega) (by omega)
        omega
      rw [hemp, Finset.sum_empty, abs_zero]
      exact hlogN.le
    · rcases le_or_gt t (U*V) with hle | hgt
      · refine le_trans (vaughan_typeI'_coeff_le U V t ht1) ?_
        refine Real.log_le_log ?_ ?_
        · exact_mod_cast ht1
        · exact_mod_cast le_trans hle hUV
      · have hemp : (Finset.Icc 1 U ×ˢ Finset.Icc 1 V).filter
            (fun p => p.1 * p.2 = t) = ∅ := by
          refine Finset.filter_false_of_mem fun p hp => ?_
          rw [Finset.mem_product] at hp
          obtain ⟨hp1, hp2⟩ := hp
          rw [Finset.mem_Icc] at hp1 hp2
          intro heq
          have h1 : p.1 * p.2 ≤ U * V := Nat.mul_le_mul hp1.2 hp2.2
          omega
        rw [hemp, Finset.sum_empty, abs_zero]
        exact hlogN.le
  · -- Leg 3: the Type II term
    exact typeII_total_le a q hq hcop δ hδ U V n₀ N hU hV
      (by omega) hN


/-- **Discrete Abel summation, antitone-coefficient bound** (Track R,
V7a): the decreasing-weight mirror of `abel_mono_bound` — if all
window partials of `z` are bounded by `B` and `φ` is nonnegative and
nonincreasing on `[P+1, ∞)`, then `‖∑ φ(m) z(m)‖ ≤ 2 φ(P+1) B`.
This prices the `1/(p·log p)` weight of the prime-block sum. -/
theorem abel_anti_bound (P Q : ℕ) (hPQ : P ≤ Q) (φ : ℕ → ℝ) (z : ℕ → ℂ)
    (B : ℝ) (hφ0 : ∀ m, 0 ≤ φ m)
    (hanti : ∀ m, P + 1 ≤ m → φ (m+1) ≤ φ m)
    (hB : ∀ t, P ≤ t → t ≤ Q → ‖∑ m ∈ Finset.Ioc P t, z m‖ ≤ B) :
    ‖∑ m ∈ Finset.Ioc P Q, ((φ m : ℝ):ℂ) * z m‖ ≤ 2 * φ (P+1) * B := by
  classical
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB P le_rfl hPQ)
  have habel : ∀ R, P ≤ R → R ≤ Q →
      ∑ m ∈ Finset.Ioc P R, ((φ m : ℝ):ℂ) * z m
      = ((φ R : ℝ):ℂ) * (∑ m ∈ Finset.Ioc P R, z m)
        - ∑ t ∈ Finset.Ico (P+1) R,
          ((φ (t+1) - φ t : ℝ):ℂ) * (∑ m ∈ Finset.Ioc P t, z m) := by
    intro R hPR hRQ
    clear hRQ
    induction R, hPR using Nat.le_induction with
    | base =>
      simp
    | succ R hPR ih =>
      rw [Finset.sum_Ioc_succ_top (by omega), ih]
      rcases Nat.eq_or_lt_of_le hPR with rfl | hlt
      · have he : Finset.Ico (P+1) P = ∅ := Finset.Ico_eq_empty (by omega)
        have he2 : Finset.Ico (P+1) (P+1) = ∅ :=
          Finset.Ico_eq_empty (by omega)
        rw [he, he2]
        have he3 : Finset.Ioc P P = ∅ := Finset.Ioc_self P
        rw [he3]
        rw [Finset.sum_Ioc_succ_top (le_refl P), he3]
        simp
      · rw [Finset.sum_Ico_succ_top (by omega : P + 1 ≤ R)]
        rw [Finset.sum_Ioc_succ_top (by omega : P ≤ R)]
        push_cast
        ring
  rcases Nat.eq_or_lt_of_le hPQ with rfl | hPQ'
  · simp only [Finset.Ioc_self, Finset.sum_empty, norm_zero]
    have := hφ0 (P+1)
    nlinarith [hB0]
  rw [habel Q hPQ le_rfl]
  refine le_trans (norm_sub_le _ _) ?_
  have h1 : ‖((φ Q : ℝ):ℂ) * (∑ m ∈ Finset.Ioc P Q, z m)‖
      ≤ φ Q * B := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hφ0 Q)]
    exact mul_le_mul_of_nonneg_left (hB Q hPQ le_rfl) (hφ0 Q)
  have h2 : ‖∑ t ∈ Finset.Ico (P+1) Q,
      ((φ (t+1) - φ t : ℝ):ℂ) * (∑ m ∈ Finset.Ioc P t, z m)‖
      ≤ (φ (P+1) - φ Q) * B := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ t ∈ Finset.Ico (P+1) Q,
        ‖((φ (t+1) - φ t : ℝ):ℂ) * (∑ m ∈ Finset.Ioc P t, z m)‖
        ≤ (φ t - φ (t+1)) * B := by
      intro t ht
      rw [Finset.mem_Ico] at ht
      have hstep := hanti t ht.1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith)]
      exact mul_le_mul (by linarith) (hB t (by omega) (by omega))
        (norm_nonneg _) (by linarith)
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_mul]
    have htel : ∑ t ∈ Finset.Ico (P+1) Q, (φ t - φ (t+1))
        = φ (P+1) - φ Q :=
      sum_Ico_sub_telescope φ (by omega : P + 1 ≤ Q)
    rw [htel]
  have hqb : 0 ≤ φ Q * B := mul_nonneg (hφ0 _) hB0
  have hpb : 0 ≤ φ (P+1) * B := mul_nonneg (hφ0 _) hB0
  have hexp : (φ (P+1) - φ Q) * B = φ (P+1) * B - φ Q * B := by
    ring
  linarith [h1, h2, hqb, hpb, hexp.le, hexp.ge]


open ArithmeticFunction in
/-- **The prime split** (Track R, V7b): a von Mangoldt sum splits into
its prime part — where `Λ(p) = log p` — and a prime-power remainder. -/
theorem lambda_prime_split (n₀ t : ℕ) (w : ℕ → ℂ) :
    ∑ n ∈ Finset.Ioc n₀ t, ((vonMangoldt n : ℝ):ℂ) * w n
      = (∑ p ∈ (Finset.Ioc n₀ t).filter (fun p => p.Prime),
          ((Real.log (p:ℝ) : ℝ):ℂ) * w p)
        + ∑ n ∈ (Finset.Ioc n₀ t).filter (fun n => ¬ n.Prime),
          ((vonMangoldt n : ℝ):ℂ) * w n := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc n₀ t)
    (fun n => n.Prime)]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  simp only [Finset.mem_filter] at hp
  rw [vonMangoldt_apply_prime hp.2]


open ArithmeticFunction in
/-- **The prime-power remainder is tiny** (Track R, V7b): non-prime
von Mangoldt support in `(n₀, M]` consists of proper prime powers
`p^k`, `p ≤ √M`, `2 ≤ k ≤ log₂ M` — at most `√M·log₂M` points, each
worth at most `log M`. -/
theorem nonprime_lambda_norm_le (n₀ M : ℕ) (hM : 2 ≤ M) (w : ℕ → ℂ)
    (hw : ∀ n, ‖w n‖ ≤ 1) :
    ‖∑ n ∈ (Finset.Ioc n₀ M).filter (fun n => ¬ n.Prime),
        ((vonMangoldt n : ℝ):ℂ) * w n‖
      ≤ ((Nat.sqrt M * M.log2 : ℕ):ℝ) * Real.log (M:ℝ) := by
  classical
  have hM0 : M ≠ 0 := by omega
  have hTsub : (Finset.Ioc n₀ M).filter
      (fun n => ¬ n.Prime ∧ vonMangoldt n ≠ 0)
      ⊆ (Finset.Ioc n₀ M).filter (fun n => ¬ n.Prime) := by
    intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1⟩
  have hzero : ∀ n ∈ (Finset.Ioc n₀ M).filter (fun n => ¬ n.Prime),
      n ∉ (Finset.Ioc n₀ M).filter
        (fun n => ¬ n.Prime ∧ vonMangoldt n ≠ 0) →
      ((vonMangoldt n : ℝ):ℂ) * w n = 0 := by
    intro n hn hnot
    simp only [Finset.mem_filter] at hn hnot
    push_neg at hnot
    have hΛ : vonMangoldt n = 0 := hnot hn.1 hn.2
    rw [hΛ, Complex.ofReal_zero, zero_mul]
  rw [← Finset.sum_subset hTsub hzero]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ n ∈ (Finset.Ioc n₀ M).filter
      (fun n => ¬ n.Prime ∧ vonMangoldt n ≠ 0),
      ‖((vonMangoldt n : ℝ):ℂ) * w n‖ ≤ Real.log (M:ℝ) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg vonMangoldt_nonneg]
    have h1 : vonMangoldt n ≤ Real.log (n:ℝ) := vonMangoldt_le_log
    have h2 : Real.log (n:ℝ) ≤ Real.log (M:ℝ) := by
      refine Real.log_le_log ?_ ?_
      · have h0 : 0 < n := by omega
        exact_mod_cast h0
      · exact_mod_cast hn.1.2
    have h3 := hw n
    have h4 := norm_nonneg (w n)
    nlinarith [vonMangoldt_nonneg (n := n)]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcount : ((Finset.Ioc n₀ M).filter
      (fun n => ¬ n.Prime ∧ vonMangoldt n ≠ 0)).card
      ≤ Nat.sqrt M * M.log2 := by
    have hsub2 : (Finset.Ioc n₀ M).filter
        (fun n => ¬ n.Prime ∧ vonMangoldt n ≠ 0)
        ⊆ ((Finset.Icc 2 (Nat.sqrt M)) ×ˢ (Finset.Icc 2 (M.log2))).image
          (fun pk => pk.1 ^ pk.2) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
      obtain ⟨⟨hn1, hn2⟩, hnp, hΛ⟩ := hn
      have hpp : IsPrimePow n := vonMangoldt_ne_zero_iff.mp hΛ
      rw [isPrimePow_nat_iff] at hpp
      obtain ⟨p, k, hp, hk, hpk⟩ := hpp
      have hk2 : 2 ≤ k := by
        rcases Nat.lt_or_ge k 2 with hk1 | hk2
        · have hke : k = 1 := by omega
          rw [hke, pow_one] at hpk
          rw [← hpk] at hnp
          exact absurd hp hnp
        · exact hk2
      rw [Finset.mem_image]
      refine ⟨(p, k), ?_, hpk⟩
      rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      refine ⟨⟨hp.two_le, ?_⟩, hk2, ?_⟩
      · rw [Nat.le_sqrt]
        calc p * p = p^2 := (Nat.pow_two p).symm
          _ ≤ p^k := Nat.pow_le_pow_right hp.pos hk2
          _ = n := hpk
          _ ≤ M := hn2
      · have h2k : 2^k ≤ M := by
          calc 2^k ≤ p^k := Nat.pow_le_pow_left hp.two_le k
            _ = n := hpk
            _ ≤ M := hn2
        by_contra hcon
        push_neg at hcon
        have hlt := (Nat.log2_lt hM0).mp hcon
        exact absurd h2k (not_le.mpr hlt)
    refine le_trans (Finset.card_le_card hsub2) ?_
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_product, Nat.card_Icc, Nat.card_Icc]
    have h1 : Nat.sqrt M + 1 - 2 ≤ Nat.sqrt M := by omega
    have h2 : M.log2 + 1 - 2 ≤ M.log2 := by omega
    exact Nat.mul_le_mul h1 h2
  have hlogM : 0 ≤ Real.log (M:ℝ) := Real.log_natCast_nonneg M
  have hc : (((Finset.Ioc n₀ M).filter
      (fun n => ¬ n.Prime ∧ vonMangoldt n ≠ 0)).card : ℝ)
      ≤ ((Nat.sqrt M * M.log2 : ℕ):ℝ) := by
    exact_mod_cast hcount
  exact mul_le_mul_of_nonneg_right hc hlogM


open ArithmeticFunction in
/-- **The uniform von Mangoldt partial bound** (Track R, V7c): every
partial sum `∑_{(n₀, t]} Λ(n) e(nβ)`, `n₀ ≤ t ≤ 2n₀`, obeys the
master minor-arc bound evaluated at `N = 2n₀` — each factor of the
right-hand side is monotone in the range endpoint. -/
theorem lambda_partial_le (a q : ℕ) (hq : 1 ≤ q)
    (hcop : Nat.Coprime a q) (δ : ℝ) (hδ : |δ| ≤ 1/(q:ℝ)^2)
    (U V n₀ : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) (hVn₀ : V < n₀)
    (hUVn₀ : U*V ≤ n₀) (hn₀2 : 2 ≤ n₀) (t : ℕ) (ht1 : n₀ ≤ t)
    (ht2 : t ≤ 2*n₀) :
    ‖∑ n ∈ Finset.Ioc n₀ t, ((vonMangoldt n : ℝ):ℂ)
        * e ((n:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
      ≤ 2*Real.log ((2*n₀ : ℕ):ℝ)
          * (13*((2*n₀ : ℕ):ℝ)*(Real.log (U:ℝ) + 3)/(q:ℝ)
            + 2*((U:ℝ)/(q:ℝ) + 1)
              * (368*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)))
        + Real.log ((2*n₀ : ℕ):ℝ)
          * (13*((2*n₀ : ℕ):ℝ)*(Real.log ((U*V : ℕ):ℝ) + 3)/(q:ℝ)
            + 2*(((U*V : ℕ):ℝ)/(q:ℝ) + 1)
              * (368*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)))
        + 3*(Real.log ((2*n₀ : ℕ):ℝ))^2
          * Real.sqrt ((1 + Real.log ((2*n₀ : ℕ):ℝ))^3
            * (27*((2*n₀ : ℕ):ℝ)^2/(V:ℝ) + 52*((2*n₀ : ℕ):ℝ)^2/(q:ℝ)
              + 2112*((2*n₀ : ℕ):ℝ)^2
                *(Real.log (8*(q:ℝ)) + 1)/(U:ℝ)
              + 1056*((2*n₀ : ℕ):ℝ)*(q:ℝ)
                *(Real.log (8*(q:ℝ)) + 1))) := by
  classical
  have hmaster := vaughan_minor_arc_le a q hq hcop δ hδ U V n₀ t
    hU hV hVn₀ (le_trans hUVn₀ ht1) ht1 (by omega)
  refine le_trans hmaster ?_
  have htc : (t:ℝ) ≤ ((2*n₀ : ℕ):ℝ) := by exact_mod_cast ht2
  have hlogt : Real.log (t:ℝ) ≤ Real.log ((2*n₀ : ℕ):ℝ) := by
    refine Real.log_le_log ?_ htc
    have h0 : 0 < t := by omega
    exact_mod_cast h0
  have hlogt0 : (0:ℝ) ≤ Real.log (t:ℝ) := Real.log_natCast_nonneg t
  have hlog8q : (0:ℝ) ≤ Real.log (8*(q:ℝ)) := by
    refine Real.log_nonneg ?_
    have hq1R : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    linarith
  have hlogU0 : (0:ℝ) ≤ Real.log (U:ℝ) := Real.log_natCast_nonneg U
  have hlogUV0 : (0:ℝ) ≤ Real.log ((U*V : ℕ):ℝ) :=
    Real.log_natCast_nonneg _
  gcongr


open ArithmeticFunction in
/-- **The prime-block sum under the minor-arc bound** (Track R, V7c):
the consumer's `1/p`-weighted prime-block exponential sum, priced by
antitone Abel summation at the weight `1/(p·log p)` against the
uniform von Mangoldt partial bound plus the prime-power remainder. -/
theorem primeBlock_sum_le (a q : ℕ) (hq : 1 ≤ q)
    (hcop : Nat.Coprime a q) (δ : ℝ) (hδ : |δ| ≤ 1/(q:ℝ)^2)
    (U V n₀ : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) (hVn₀ : V < n₀)
    (hUVn₀ : U*V ≤ n₀) (hn₀2 : 2 ≤ n₀) :
    ‖∑ p ∈ (Finset.Ioc n₀ (2*n₀)).filter (fun p => p.Prime),
        ((1/(p:ℝ) : ℝ):ℂ) * e ((p:ℝ)*((a:ℝ)/(q:ℝ) + δ))‖
      ≤ 2 * (1/(((n₀+1 : ℕ):ℝ) * Real.log ((n₀+1 : ℕ):ℝ)))
        * ((2*Real.log ((2*n₀ : ℕ):ℝ)
            * (13*((2*n₀ : ℕ):ℝ)*(Real.log (U:ℝ) + 3)/(q:ℝ)
              + 2*((U:ℝ)/(q:ℝ) + 1)
                * (368*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)))
          + Real.log ((2*n₀ : ℕ):ℝ)
            * (13*((2*n₀ : ℕ):ℝ)*(Real.log ((U*V : ℕ):ℝ) + 3)/(q:ℝ)
              + 2*(((U*V : ℕ):ℝ)/(q:ℝ) + 1)
                * (368*(q:ℝ)*(Real.log (8*(q:ℝ)) + 1)))
          + 3*(Real.log ((2*n₀ : ℕ):ℝ))^2
            * Real.sqrt ((1 + Real.log ((2*n₀ : ℕ):ℝ))^3
              * (27*((2*n₀ : ℕ):ℝ)^2/(V:ℝ)
                + 52*((2*n₀ : ℕ):ℝ)^2/(q:ℝ)
                + 2112*((2*n₀ : ℕ):ℝ)^2
                  *(Real.log (8*(q:ℝ)) + 1)/(U:ℝ)
                + 1056*((2*n₀ : ℕ):ℝ)*(q:ℝ)
                  *(Real.log (8*(q:ℝ)) + 1))))
          + ((Nat.sqrt (2*n₀) * (2*n₀).log2 : ℕ):ℝ)
            * Real.log ((2*n₀ : ℕ):ℝ)) := by
  classical
  have hzsum : ∑ p ∈ (Finset.Ioc n₀ (2*n₀)).filter
      (fun p => p.Prime),
      ((1/(p:ℝ) : ℝ):ℂ) * e ((p:ℝ)*((a:ℝ)/(q:ℝ) + δ))
      = ∑ m ∈ Finset.Ioc n₀ (2*n₀),
          ((1/((m:ℝ) * Real.log (m:ℝ)) : ℝ):ℂ)
            * (if m.Prime then
                ((Real.log (m:ℝ) : ℝ):ℂ) * e ((m:ℝ)*((a:ℝ)/(q:ℝ) + δ))
              else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Ioc] at hm
    by_cases hp : m.Prime
    · rw [if_pos hp, if_pos hp]
      have hm2 : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hp.two_le
      have hlogm : (0:ℝ) < Real.log (m:ℝ) := by
        refine Real.log_pos ?_
        linarith
      have hm0 : (0:ℝ) < (m:ℝ) := by linarith
      have hcoe : ((1/(m:ℝ) : ℝ):ℂ)
          = ((1/((m:ℝ) * Real.log (m:ℝ)) : ℝ):ℂ)
            * ((Real.log (m:ℝ) : ℝ):ℂ) := by
        rw [← Complex.ofReal_mul]
        congr 1
        field_simp
      rw [hcoe]
      ring
    · rw [if_neg hp, if_neg hp, mul_zero]
  rw [hzsum]
  refine abel_anti_bound n₀ (2*n₀) (by omega)
    (fun m => 1/((m:ℝ) * Real.log (m:ℝ)))
    (fun m => if m.Prime then
      ((Real.log (m:ℝ) : ℝ):ℂ) * e ((m:ℝ)*((a:ℝ)/(q:ℝ) + δ)) else 0)
    _ ?_ ?_ ?_
  · intro m
    exact div_nonneg zero_le_one
      (mul_nonneg (Nat.cast_nonneg m) (Real.log_natCast_nonneg m))
  · intro m hm
    have hm3 : 3 ≤ m := by omega
    have hmR : (3:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm3
    have hlogm : (0:ℝ) < Real.log (m:ℝ) := by
      refine Real.log_pos ?_
      linarith
    have hpos : (0:ℝ) < (m:ℝ) * Real.log (m:ℝ) :=
      mul_pos (by linarith) hlogm
    refine one_div_le_one_div_of_le hpos ?_
    have hc1 : (m:ℝ) ≤ ((m+1 : ℕ):ℝ) := by
      push_cast
      linarith
    have hc2 : Real.log (m:ℝ) ≤ Real.log ((m+1 : ℕ):ℝ) := by
      refine Real.log_le_log (by linarith) hc1
    exact mul_le_mul hc1 hc2 (Real.log_natCast_nonneg m)
      (Nat.cast_nonneg _)
  · intro t ht1 ht2
    have hzt : ∑ m ∈ Finset.Ioc n₀ t,
        (if m.Prime then
          ((Real.log (m:ℝ) : ℝ):ℂ) * e ((m:ℝ)*((a:ℝ)/(q:ℝ) + δ))
        else 0)
        = ∑ p ∈ (Finset.Ioc n₀ t).filter (fun p => p.Prime),
            ((Real.log (p:ℝ) : ℝ):ℂ) * e ((p:ℝ)*((a:ℝ)/(q:ℝ) + δ)) :=
      (Finset.sum_filter _ _).symm
    rw [hzt]
    have hsplit := lambda_prime_split n₀ t
      (fun n => e ((n:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
    have hprime_eq : ∑ p ∈ (Finset.Ioc n₀ t).filter
        (fun p => p.Prime),
        ((Real.log (p:ℝ) : ℝ):ℂ) * e ((p:ℝ)*((a:ℝ)/(q:ℝ) + δ))
        = (∑ n ∈ Finset.Ioc n₀ t, ((vonMangoldt n : ℝ):ℂ)
            * e ((n:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
          - ∑ n ∈ (Finset.Ioc n₀ t).filter (fun n => ¬ n.Prime),
              ((vonMangoldt n : ℝ):ℂ)
                * e ((n:ℝ)*((a:ℝ)/(q:ℝ) + δ)) := by
      rw [hsplit]
      ring
    rw [hprime_eq]
    refine le_trans (norm_sub_le _ _) ?_
    have hpart := lambda_partial_le a q hq hcop δ hδ U V n₀
      hU hV hVn₀ hUVn₀ hn₀2 t ht1 ht2
    have hcorr := nonprime_lambda_norm_le n₀ t (by omega)
      (fun n => e ((n:ℝ)*((a:ℝ)/(q:ℝ) + δ)))
      (fun n => le_of_eq (norm_e _))
    have hcorrmono : ((Nat.sqrt t * t.log2 : ℕ):ℝ) * Real.log (t:ℝ)
        ≤ ((Nat.sqrt (2*n₀) * (2*n₀).log2 : ℕ):ℝ)
          * Real.log ((2*n₀ : ℕ):ℝ) := by
      have hs : Nat.sqrt t ≤ Nat.sqrt (2*n₀) := Nat.sqrt_le_sqrt ht2
      have hl2 : t.log2 ≤ (2*n₀).log2 := by
        by_contra hcon
        push_neg at hcon
        have h1 := Nat.log2_self_le (n := t) (by omega)
        have h2 := (Nat.log2_lt (n := 2*n₀) (by omega)).mp hcon
        have h3 : 2*n₀ < t := lt_of_lt_of_le h2 h1
        omega
      have hnat : Nat.sqrt t * t.log2
          ≤ Nat.sqrt (2*n₀) * (2*n₀).log2 := Nat.mul_le_mul hs hl2
      have hcast : ((Nat.sqrt t * t.log2 : ℕ):ℝ)
          ≤ ((Nat.sqrt (2*n₀) * (2*n₀).log2 : ℕ):ℝ) := by
        exact_mod_cast hnat
      have hlog : Real.log (t:ℝ) ≤ Real.log ((2*n₀ : ℕ):ℝ) := by
        refine Real.log_le_log ?_ ?_
        · have h0 : 0 < t := by omega
          exact_mod_cast h0
        · exact_mod_cast ht2
      exact mul_le_mul hcast hlog (Real.log_natCast_nonneg t)
        (Nat.cast_nonneg _)
    linarith [hpart, hcorr, hcorrmono]


/-- **Block-sum periodicity** (Track R, V8a): the prime-block sum only
sees its frequency modulo `1`. -/
theorem primeBlock_sum_period (n₀ : ℕ) (β : ℝ) (k : ℤ) :
    ∑ p ∈ (Finset.Ioc n₀ (2*n₀)).filter (fun p => p.Prime),
        ((1/(p:ℝ) : ℝ):ℂ) * e ((p:ℝ)*β)
      = ∑ p ∈ (Finset.Ioc n₀ (2*n₀)).filter (fun p => p.Prime),
          ((1/(p:ℝ) : ℝ):ℂ) * e ((p:ℝ)*(β - (k:ℝ))) := by
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  have harg : (p:ℝ)*β = (p:ℝ)*(β - (k:ℝ)) + (((p:ℤ)*k : ℤ):ℝ) := by
    push_cast
    ring
  rw [harg, e_add, e_intCast, mul_one]


/-- **Dirichlet frequency preparation** (Track R, V8b): every real
frequency is, up to an integer shift, of the form `a/q + δ` with
`q ≤ n`, `gcd(a,q) = 1`, and `|δ| ≤ 1/((n+1)q)`. -/
theorem dirichlet_frequency_split (β : ℝ) (n : ℕ) (hn : 0 < n) :
    ∃ (a q : ℕ) (k : ℤ), 1 ≤ q ∧ q ≤ n ∧ Nat.Coprime a q ∧
      |(β - (k:ℝ)) - (a:ℝ)/(q:ℝ)| ≤ 1/(((n:ℝ)+1)*(q:ℝ)) := by
  obtain ⟨r, hr1, hr2⟩ := Real.exists_rat_abs_sub_le_and_den_le β hn
  have hdenz : (r.den : ℤ) ≠ 0 := by
    exact_mod_cast Rat.den_ne_zero r
  have h0 : (0:ℤ) ≤ r.num % (r.den:ℤ) := Int.emod_nonneg r.num hdenz
  have hmod : (r.den:ℤ) * (r.num / (r.den:ℤ)) + r.num % (r.den:ℤ)
      = r.num := Int.ediv_add_emod r.num (r.den:ℤ)
  refine ⟨(r.num % (r.den:ℤ)).toNat, r.den, r.num / (r.den:ℤ),
    Rat.den_pos r, hr2, ?_, ?_⟩
  · -- coprimality survives the shift
    have hred : r.num.natAbs.Coprime r.den := r.reduced
    have hkey : ∀ d : ℕ, d ∣ (r.num % (r.den:ℤ)).toNat → d ∣ r.den →
        d ∣ r.num.natAbs := by
      intro d hd1 hd2
      have h1 : (d:ℤ) ∣ (r.num % (r.den:ℤ)) := by
        have h1' := Int.natCast_dvd_natCast.mpr hd1
        rwa [Int.toNat_of_nonneg h0] at h1'
      have h2 : (d:ℤ) ∣ (r.den:ℤ) := Int.natCast_dvd_natCast.mpr hd2
      have h3 : (d:ℤ) ∣ r.num := by
        have h4 : (d:ℤ) ∣ (r.den:ℤ) * (r.num / (r.den:ℤ))
            + r.num % (r.den:ℤ) :=
          dvd_add (Dvd.dvd.mul_right h2 _) h1
        rwa [hmod] at h4
      have h5 := Int.natAbs_dvd_natAbs.mpr h3
      rwa [Int.natAbs_natCast] at h5
    have hd1 := Nat.gcd_dvd_left ((r.num % (r.den:ℤ)).toNat) r.den
    have hd2 := Nat.gcd_dvd_right ((r.num % (r.den:ℤ)).toNat) r.den
    have hdvd := Nat.dvd_gcd (hkey _ hd1 hd2) hd2
    exact Nat.dvd_one.mp (hred.gcd_eq_one ▸ hdvd)
  · -- the shifted frequency error is the Dirichlet error
    have hcast : (((r.num % (r.den:ℤ)).toNat : ℕ):ℝ)
        = ((r.num % (r.den:ℤ) : ℤ):ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
    have hden0 : (0:ℝ) < (r.den:ℝ) := by
      exact_mod_cast Rat.den_pos r
    have hmodR : (r.den:ℝ) * ((r.num / (r.den:ℤ) : ℤ):ℝ)
        + ((r.num % (r.den:ℤ) : ℤ):ℝ) = (r.num:ℝ) := by
      exact_mod_cast hmod
    have hkey2 : (β - ((r.num / (r.den:ℤ) : ℤ):ℝ))
        - (((r.num % (r.den:ℤ)).toNat : ℕ):ℝ)/(r.den:ℝ)
        = β - (r:ℝ) := by
      rw [hcast]
      have hrcast : (r:ℝ) = (r.num:ℝ)/(r.den:ℝ) := Rat.cast_def r
      rw [hrcast]
      field_simp
      linarith [hmodR]
    rw [hkey2]
    exact hr1

end ExpSums

end MoltResearch
