import MoltResearch.Discrepancy.PatternLaws
import MoltResearch.Discrepancy.HoeffdingUniform

/-!
# Discrepancy: the decrement observable

Track C, Elliott campaign (`Problems/tao2015_derivation_c.md`, issue #2946,
E6f-5b-i): the observable `F(X_H, Y)` that the entropy decrement argument
evaluates — the rounded conjugate-pair sum gated by the residue coordinates —
and the bridge identifying its joint-law expectation with the log-averaged
triple sum of Proposition `conv`, up to the `O(|ι|·J/K)` rounding cost.
-/

namespace MoltResearch

open Finset
open scoped Function

/-- The pattern, extended to `ℕ` by zero, with grid values decoded. -/
noncomputable def patExt (K H : ℕ) (x : PatternSpace K H) : ℕ → ℂ :=
  fun m => if hm : m < H then roundCVal K (x ⟨m, hm⟩) else 0

theorem patExt_patternMap (g : ℕ → ℂ) (K H n m : ℕ) (hm : m < H) :
    patExt K H (patternMap g K H n) m = roundCVal K (roundC K (g (n + 1 + m))) := by
  rw [patExt, dif_pos hm]
  rfl

section Observable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The decrement observable**: the rounded conjugate-pair sum, gated by the
residue coordinates of `y`. -/
noncomputable def decObs (K H J h : ℕ) (a : ι → ℕ)
    (hcop : Pairwise (Nat.Coprime on a)) [∀ i, NeZero (a i)]
    (x : PatternSpace K H) (y : ZMod (∏ i, a i)) : ℂ :=
  ∑ i, ∑ j ∈ Finset.Icc 1 J,
    (if ZMod.prodEquivPi a hcop y i = -((j : ℕ) : ZMod (a i))
      then patExt K H x (j - 1)
        * (starRingEnd ℂ) (patExt K H x (j - 1 + a i * h)) else 0)

/-- **The pointwise rounding bridge**: at a sampled point, the observable is the
true conjugate-pair divisor sum up to `|ι|·J·12/K`. -/
theorem norm_decObs_sub_le (g : ℕ → ℂ) (huni : Unimodular g)
    (K H J h : ℕ) (hK : 0 < K) (a : ι → ℕ)
    (hcop : Pairwise (Nat.Coprime on a)) [∀ i, NeZero (a i)]
    (hH : ∀ i, J + a i * h ≤ H) (n : ℕ) :
    ‖decObs K H J h a hcop (patternMap g K H n) ((n : ZMod (∏ i, a i)))
        - ∑ i, ∑ j ∈ Finset.Icc 1 J,
          (if (n + j) % a i = 0
            then g (n + j) * (starRingEnd ℂ) (g (n + j + a i * h)) else 0)‖
      ≤ (Fintype.card ι : ℝ) * J * (12 / K) := by
  classical
  rw [decObs, ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  have hper : ∀ i : ι,
      ‖∑ j ∈ Finset.Icc 1 J,
        (if ZMod.prodEquivPi a hcop ((n : ZMod (∏ i, a i))) i
            = -((j : ℕ) : ZMod (a i))
          then patExt K H (patternMap g K H n) (j - 1)
            * (starRingEnd ℂ)
              (patExt K H (patternMap g K H n) (j - 1 + a i * h)) else 0)
        - ∑ j ∈ Finset.Icc 1 J,
          (if (n + j) % a i = 0
            then g (n + j) * (starRingEnd ℂ) (g (n + j + a i * h)) else 0)‖
      ≤ (J : ℝ) * (12 / K) := by
    intro i
    rw [← Finset.sum_sub_distrib]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ j ∈ Finset.Icc 1 J,
        ‖(if ZMod.prodEquivPi a hcop ((n : ZMod (∏ i, a i))) i
              = -((j : ℕ) : ZMod (a i))
            then patExt K H (patternMap g K H n) (j - 1)
              * (starRingEnd ℂ)
                (patExt K H (patternMap g K H n) (j - 1 + a i * h)) else 0)
          - (if (n + j) % a i = 0
              then g (n + j) * (starRingEnd ℂ) (g (n + j + a i * h)) else 0)‖
        ≤ 12 / K := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      -- the two gate conditions agree
      have hcond : (ZMod.prodEquivPi a hcop ((n : ZMod (∏ i, a i))) i
          = -((j : ℕ) : ZMod (a i))) ↔ ((n + j) % a i = 0) := by
        rw [prodEquivPi_natCast]
        constructor
        · intro hc
          have : ((n + j : ℕ) : ZMod (a i)) = 0 := by
            push_cast
            rw [hc]
            ring
          rwa [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero] at this
        · intro hc
          have hdvd : ((n + j : ℕ) : ZMod (a i)) = 0 := by
            rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
            exact hc
          push_cast at hdvd
          exact eq_neg_of_add_eq_zero_left hdvd
      -- decode the pattern values
      have hv1 : patExt K H (patternMap g K H n) (j - 1)
          = roundCVal K (roundC K (g (n + j))) := by
        rw [patExt_patternMap g K H n (j - 1) (by
          have := hH i
          omega)]
        have harg : n + 1 + (j - 1) = n + j := by omega
        rw [harg]
      have hv2 : patExt K H (patternMap g K H n) (j - 1 + a i * h)
          = roundCVal K (roundC K (g (n + j + a i * h))) := by
        rw [patExt_patternMap g K H n (j - 1 + a i * h) (by
          have := hH i
          omega)]
        have harg : n + 1 + (j - 1 + a i * h) = n + j + a i * h := by omega
        rw [harg]
      by_cases hc : (n + j) % a i = 0
      · rw [if_pos (hcond.mpr hc), if_pos hc, hv1, hv2]
        -- ‖r₁ conj r₂ − g₁ conj g₂‖ ≤ 12/K
        have hg1 : ‖g (n + j)‖ = 1 := huni (n + j)
        have hg2 : ‖g (n + j + a i * h)‖ = 1 := huni (n + j + a i * h)
        have hr1 := norm_sub_roundCVal_le hK (le_of_eq hg1)
        have hr2 := norm_sub_roundCVal_le hK (le_of_eq hg2)
        have hrb2 := norm_roundCVal_le hK (roundC K (g (n + j + a i * h)))
        set r1 := roundCVal K (roundC K (g (n + j)))
        set r2 := roundCVal K (roundC K (g (n + j + a i * h)))
        have hsplit : r1 * (starRingEnd ℂ) r2
            - g (n + j) * (starRingEnd ℂ) (g (n + j + a i * h))
            = (r1 - g (n + j)) * (starRingEnd ℂ) r2
              + g (n + j) * ((starRingEnd ℂ) r2
                - (starRingEnd ℂ) (g (n + j + a i * h))) := by
          ring
        rw [hsplit]
        have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
        calc ‖(r1 - g (n + j)) * (starRingEnd ℂ) r2
              + g (n + j) * ((starRingEnd ℂ) r2
                - (starRingEnd ℂ) (g (n + j + a i * h)))‖
            ≤ ‖r1 - g (n + j)‖ * ‖r2‖
              + ‖g (n + j)‖ * ‖r2 - g (n + j + a i * h)‖ := by
              refine le_trans (norm_add_le _ _) ?_
              rw [norm_mul, norm_mul, RCLike.norm_conj]
              have : (starRingEnd ℂ) r2
                  - (starRingEnd ℂ) (g (n + j + a i * h))
                  = (starRingEnd ℂ) (r2 - g (n + j + a i * h)) := by
                rw [map_sub]
              rw [this, RCLike.norm_conj]
          _ ≤ (4 / K) * 2 + 1 * (4 / K) := by
              have hn1 : ‖r1 - g (n + j)‖ ≤ 4 / K := by
                rw [norm_sub_rev]
                exact hr1
              have hn2 : ‖r2 - g (n + j + a i * h)‖ ≤ 4 / K := by
                rw [norm_sub_rev]
                exact hr2
              have h20 : (0 : ℝ) ≤ 2 := by norm_num
              rw [hg1]
              refine add_le_add ?_ ?_
              · exact mul_le_mul hn1 hrb2 (norm_nonneg _) (by positivity)
              · exact mul_le_mul_of_nonneg_left hn2 (by norm_num)
          _ = 12 / K := by ring
      · rw [if_neg (fun hcc => hc (hcond.mp hcc)), if_neg hc, sub_zero,
          norm_zero]
        positivity
    refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have hJc : J + 1 - 1 = J := by omega
    rw [hJc]
  refine le_trans (Finset.sum_le_sum fun i _ => hper i) (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end Observable

end MoltResearch
