import MoltResearch.Discrepancy.PatternLaws
import MoltResearch.Discrepancy.HoeffdingUniform
import MoltResearch.Discrepancy.CircleMethod

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

/-- **The expectation bridge**: the joint-law expectation of the observable is
the normalized triple sum of Proposition `conv`, up to the rounding cost. -/
theorem norm_sum_jointLaw_decObs_sub_le (g : ℕ → ℂ) (huni : Unimodular g)
    (K H J h : ℕ) (hK : 0 < K) (a : ι → ℕ)
    (hcop : Pairwise (Nat.Coprime on a)) [∀ i, NeZero (a i)]
    (hH : ∀ i, J + a i * h ≤ H) {A B : ℕ} (hA : 1 ≤ A) (hAB : A < B) :
    ‖(∑ z : PatternSpace K H × ZMod (∏ i, a i),
        ((jointLaw g K H (∏ i, a i) A B z : ℝ) : ℂ)
          * decObs K H J h a hcop z.1 z.2)
      - (1 / ((∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m : ℝ) : ℂ))
        * ∑ i, ∑ j ∈ Finset.Icc 1 J, ∑ n ∈ Finset.Ioc A B,
            (if (n + j) % a i = 0
              then g (n + j) * (starRingEnd ℂ) (g (n + j + a i * h)) else 0)
              / (n : ℂ)‖
      ≤ (Fintype.card ι : ℝ) * J * (12 / K) := by
  classical
  -- the pulled-back expectation
  have hpush := sum_pushWeight_mul_complex (Finset.Ioc A B) (logWeight A B)
    (fun n => (patternMap g K H n, (n : ZMod (∏ i, a i))))
    (fun z => decObs K H J h a hcop z.1 z.2)
  have hjoint : (∑ z : PatternSpace K H × ZMod (∏ i, a i),
      ((jointLaw g K H (∏ i, a i) A B z : ℝ) : ℂ)
        * decObs K H J h a hcop z.1 z.2)
      = ∑ n ∈ Finset.Ioc A B, ((logWeight A B n : ℝ) : ℂ)
          * decObs K H J h a hcop (patternMap g K H n)
            ((n : ZMod (∏ i, a i))) := hpush
  -- the true divisor-sum observable
  have hdict := sum_logWeight_mul A B (fun n =>
    ∑ i, ∑ j ∈ Finset.Icc 1 J,
      (if (n + j) % a i = 0
        then g (n + j) * (starRingEnd ℂ) (g (n + j + a i * h)) else 0))
  have hexch : ∑ n ∈ Finset.Ioc A B,
      (∑ i, ∑ j ∈ Finset.Icc 1 J,
        (if (n + j) % a i = 0
          then g (n + j) * (starRingEnd ℂ) (g (n + j + a i * h)) else 0))
        / (n : ℂ)
      = ∑ i, ∑ j ∈ Finset.Icc 1 J, ∑ n ∈ Finset.Ioc A B,
          (if (n + j) % a i = 0
            then g (n + j) * (starRingEnd ℂ) (g (n + j + a i * h)) else 0)
            / (n : ℂ) := by
    rw [Finset.sum_congr rfl fun n _ => Finset.sum_div _ _ _]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl fun n _ => Finset.sum_div _ _ _]
    rw [Finset.sum_comm]
  -- assemble: the difference is the aggregated per-point rounding error
  have hsplit : (∑ z : PatternSpace K H × ZMod (∏ i, a i),
      ((jointLaw g K H (∏ i, a i) A B z : ℝ) : ℂ)
        * decObs K H J h a hcop z.1 z.2)
      - (1 / ((∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m : ℝ) : ℂ))
        * ∑ i, ∑ j ∈ Finset.Icc 1 J, ∑ n ∈ Finset.Ioc A B,
            (if (n + j) % a i = 0
              then g (n + j) * (starRingEnd ℂ) (g (n + j + a i * h)) else 0)
              / (n : ℂ)
      = ∑ n ∈ Finset.Ioc A B, ((logWeight A B n : ℝ) : ℂ)
          * (decObs K H J h a hcop (patternMap g K H n)
              ((n : ZMod (∏ i, a i)))
            - ∑ i, ∑ j ∈ Finset.Icc 1 J,
                (if (n + j) % a i = 0
                  then g (n + j) * (starRingEnd ℂ) (g (n + j + a i * h))
                  else 0)) := by
    rw [hjoint, ← hexch, ← hdict]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hsplit]
  refine le_trans (norm_sum_le _ _) ?_
  have hper : ∀ n ∈ Finset.Ioc A B,
      ‖((logWeight A B n : ℝ) : ℂ)
        * (decObs K H J h a hcop (patternMap g K H n)
            ((n : ZMod (∏ i, a i)))
          - ∑ i, ∑ j ∈ Finset.Icc 1 J,
              (if (n + j) % a i = 0
                then g (n + j) * (starRingEnd ℂ) (g (n + j + a i * h))
                else 0))‖
      ≤ logWeight A B n * ((Fintype.card ι : ℝ) * J * (12 / K)) := by
    intro n _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (logWeight_nonneg A B n)]
    exact mul_le_mul_of_nonneg_left
      (norm_decObs_sub_le g huni K H J h hK a hcop hH n)
      (logWeight_nonneg A B n)
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [← Finset.sum_mul, sum_logWeight hA hAB, one_mul]

theorem norm_patExt_le {K H : ℕ} (hK : 0 < K) (x : PatternSpace K H) (m : ℕ) :
    ‖patExt K H x m‖ ≤ 2 := by
  rw [patExt]
  split_ifs with hm
  · exact norm_roundCVal_le hK _
  · rw [norm_zero]
    norm_num

/-- The observable is uniformly bounded by `4·|ι|·J`. -/
theorem norm_decObs_le (K H J h : ℕ) (hK : 0 < K) (a : ι → ℕ)
    (hcop : Pairwise (Nat.Coprime on a)) [∀ i, NeZero (a i)]
    (x : PatternSpace K H) (y : ZMod (∏ i, a i)) :
    ‖decObs K H J h a hcop x y‖ ≤ (Fintype.card ι : ℝ) * J * 4 := by
  rw [decObs]
  refine le_trans (norm_sum_le _ _) ?_
  have hper : ∀ i : ι, ‖∑ j ∈ Finset.Icc 1 J,
      (if ZMod.prodEquivPi a hcop y i = -((j : ℕ) : ZMod (a i))
        then patExt K H x (j - 1)
          * (starRingEnd ℂ) (patExt K H x (j - 1 + a i * h)) else 0)‖
      ≤ (J : ℝ) * 4 := by
    intro i
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ j ∈ Finset.Icc 1 J,
        ‖(if ZMod.prodEquivPi a hcop y i = -((j : ℕ) : ZMod (a i))
          then patExt K H x (j - 1)
            * (starRingEnd ℂ) (patExt K H x (j - 1 + a i * h)) else 0)‖
        ≤ 4 := by
      intro j _
      split_ifs
      · rw [norm_mul, RCLike.norm_conj]
        calc ‖patExt K H x (j - 1)‖ * ‖patExt K H x (j - 1 + a i * h)‖
            ≤ 2 * 2 := mul_le_mul (norm_patExt_le hK x _)
              (norm_patExt_le hK x _) (norm_nonneg _) (by norm_num)
          _ = 4 := by norm_num
      · rw [norm_zero]
        norm_num
    refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have hJc : J + 1 - 1 = J := by omega
    rw [hJc]
  refine le_trans (Finset.sum_le_sum fun i _ => hper i) (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- **The exact `y`-average of the observable**: summing over all residues
collapses each gate to its exact share. -/
theorem sum_decObs_eq (K H J h : ℕ) (a : ι → ℕ)
    (hcop : Pairwise (Nat.Coprime on a)) [∀ i, NeZero (a i)]
    (x : PatternSpace K H) :
    ∑ y : ZMod (∏ i, a i), decObs K H J h a hcop x y
      = ∑ i, (((∏ i', a i') / a i : ℕ) : ℂ)
          * ∑ j ∈ Finset.Icc 1 J, patExt K H x (j - 1)
              * (starRingEnd ℂ) (patExt K H x (j - 1 + a i * h)) := by
  classical
  rw [show (∑ y : ZMod (∏ i, a i), decObs K H J h a hcop x y)
      = ∑ y : ZMod (∏ i, a i), ∑ i, ∑ j ∈ Finset.Icc 1 J,
        (if ZMod.prodEquivPi a hcop y i = -((j : ℕ) : ZMod (a i))
          then patExt K H x (j - 1)
            * (starRingEnd ℂ) (patExt K H x (j - 1 + a i * h)) else 0)
      from rfl]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact sum_zmod_coord_indicator a hcop i (Finset.Icc 1 J)
    (fun j => patExt K H x (j - 1)
      * (starRingEnd ℂ) (patExt K H x (j - 1 + a i * h)))
    (fun j => -((j : ℕ) : ZMod (a i)))

/-- **Truncated versus circular correlation**: replacing the interval pair sum
by its `ZMod J` circular version costs at most `8·s` — the wraparound strip. -/
theorem norm_trunc_sub_circular_le {K H : ℕ} (hK : 0 < K)
    (x : PatternSpace K H) {J s : ℕ} [NeZero J] (hs : s < J) :
    ‖(∑ j ∈ Finset.Icc 1 J, patExt K H x (j - 1)
        * (starRingEnd ℂ) (patExt K H x (j - 1 + s)))
      - ∑ v : ZMod J, patExt K H x v.val
          * (starRingEnd ℂ) (patExt K H x ((v + ((s : ℕ) : ZMod J)).val))‖
      ≤ 8 * s := by
  classical
  have hpair : ∀ m m' : ℕ, ‖patExt K H x m * (starRingEnd ℂ) (patExt K H x m')‖
      ≤ 4 := by
    intro m m'
    rw [norm_mul, RCLike.norm_conj]
    calc ‖patExt K H x m‖ * ‖patExt K H x m'‖
        ≤ 2 * 2 := mul_le_mul (norm_patExt_le hK x m) (norm_patExt_le hK x m')
          (norm_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  -- reindex the interval sum over the residue values
  have hreidx : (∑ j ∈ Finset.Icc 1 J, patExt K H x (j - 1)
      * (starRingEnd ℂ) (patExt K H x (j - 1 + s)))
      = ∑ v : ZMod J, patExt K H x v.val
          * (starRingEnd ℂ) (patExt K H x (v.val + s)) := by
    rw [sum_zmod_eq_sum_range (fun v => patExt K H x v.val
      * (starRingEnd ℂ) (patExt K H x (v.val + s)))]
    refine Finset.sum_bij' (fun j _ => j - 1) (fun m _ => m + 1)
      ?_ ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_Icc] at hj
      rw [Finset.mem_range]
      show j - 1 < J
      omega
    · intro m hm
      rw [Finset.mem_range] at hm
      rw [Finset.mem_Icc]
      show 1 ≤ m + 1 ∧ m + 1 ≤ J
      omega
    · intro j hj
      rw [Finset.mem_Icc] at hj
      show j - 1 + 1 = j
      omega
    · intro m _
      show m + 1 - 1 = m
      omega
    · intro j hj
      rw [Finset.mem_Icc] at hj
      show patExt K H x (j - 1) * (starRingEnd ℂ) (patExt K H x (j - 1 + s))
        = patExt K H x (((j - 1 : ℕ) : ZMod J)).val
          * (starRingEnd ℂ) (patExt K H x ((((j - 1 : ℕ) : ZMod J)).val + s))
      rw [ZMod.val_natCast_of_lt (by omega : j - 1 < J)]
  rw [hreidx, ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  -- terms agree off the wraparound strip
  have hsplit : ∀ v : ZMod J,
      ‖patExt K H x v.val * (starRingEnd ℂ) (patExt K H x (v.val + s))
        - patExt K H x v.val
          * (starRingEnd ℂ) (patExt K H x ((v + ((s : ℕ) : ZMod J)).val))‖
      ≤ if v.val + s < J then 0 else 8 := by
    intro v
    by_cases hv : v.val + s < J
    · rw [if_pos hv]
      have hval : (v + ((s : ℕ) : ZMod J)).val = v.val + s := by
        rw [ZMod.val_add, ZMod.val_natCast_of_lt hs, Nat.mod_eq_of_lt]
        omega
      rw [hval, sub_self, norm_zero]
    · rw [if_neg hv]
      calc ‖patExt K H x v.val * (starRingEnd ℂ) (patExt K H x (v.val + s))
          - patExt K H x v.val
            * (starRingEnd ℂ) (patExt K H x ((v + ((s : ℕ) : ZMod J)).val))‖
          ≤ ‖patExt K H x v.val
              * (starRingEnd ℂ) (patExt K H x (v.val + s))‖
            + ‖patExt K H x v.val
              * (starRingEnd ℂ)
                (patExt K H x ((v + ((s : ℕ) : ZMod J)).val))‖ :=
            norm_sub_le _ _
        _ ≤ 4 + 4 := add_le_add (hpair _ _) (hpair _ _)
        _ = 8 := by norm_num
  refine le_trans (Finset.sum_le_sum fun v _ => hsplit v) ?_
  -- the wraparound strip has at most `s` residues
  have hcard : (Finset.univ.filter
      (fun v : ZMod J => ¬ v.val + s < J)).card ≤ s := by
    have hmaps : ∀ v ∈ Finset.univ.filter
        (fun v : ZMod J => ¬ v.val + s < J),
        v.val - (J - s) ∈ Finset.range s := by
      intro v hv
      rw [Finset.mem_filter] at hv
      rw [Finset.mem_range]
      have := ZMod.val_lt v
      omega
    have hinj : Set.InjOn (fun v : ZMod J => v.val - (J - s))
        ↑(Finset.univ.filter (fun v : ZMod J => ¬ v.val + s < J)) := by
      intro v₁ h₁ v₂ h₂ heq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at h₁ h₂
      simp only at heq
      have hv₁ := ZMod.val_lt v₁
      have hv₂ := ZMod.val_lt v₂
      have hveq : v₁.val = v₂.val := by omega
      exact ZMod.val_injective _ hveq
    have h := Finset.card_le_card_of_injOn
      (fun v : ZMod J => v.val - (J - s))
      (fun v hv => by
        rw [Finset.mem_coe] at hv
        exact Finset.mem_coe.mpr (hmaps v hv))
      hinj
    rwa [Finset.card_range] at h
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp only [smul_zero, zero_add, nsmul_eq_mul]
  calc ((Finset.univ.filter
      (fun v : ZMod J => ¬ v.val + s < J)).card : ℝ) * 8
      ≤ (s : ℝ) * 8 := by
        have := hcard
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast this)
          (by norm_num)
    _ = 8 * s := by ring

open scoped NNReal in
/-- **The per-pattern frequency bound**: the normalized `y`-average of the
observable is controlled by the wraparound strip, the minor frequencies, and
the major-frequency pattern DFT masses — the M1a2 unit of the master theorem. -/
theorem norm_avg_decObs_le (K H J h : ℕ) [NeZero J] (hK : 0 < K)
    (a : ι → ℕ) (hcop : Pairwise (Nat.Coprime on a)) [∀ i, NeZero (a i)]
    (hsJ : ∀ i, a i * h < J) {θ κ : ℝ} (hθ : 0 ≤ θ)
    (hκ : ∑ i, 1 / ((a i : ℝ)) ≤ κ) (x : PatternSpace K H) :
    ‖(1 / ((∏ i, a i : ℕ) : ℂ))
        * ∑ y : ZMod (∏ i, a i), decObs K H J h a hcop x y‖
      ≤ 8 * h * (Fintype.card ι : ℝ) + 4 * θ * J
        + (J : ℝ) * κ * 2
          * ∑ ξ ∈ Finset.univ.filter (fun ξ : ZMod J =>
              θ ≤ ‖∑ i, ((1 / (a i : ℝ) : ℝ) : ℂ)
                * zChar (((a i * h : ℕ) : ZMod J)) ξ‖),
              ‖zDFT (fun v : ZMod J => patExt K H x v.val) (-ξ)‖ := by
  classical
  have hP0 : 0 < ∏ i, a i :=
    Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (NeZero.ne (a i))
  have hPC : ((∏ i, a i : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : (∏ i, a i) ≠ 0)
  -- normalize the exact average
  have hnorm : (1 / ((∏ i, a i : ℕ) : ℂ))
      * ∑ y : ZMod (∏ i, a i), decObs K H J h a hcop x y
      = ∑ i, ((1 / (a i : ℝ) : ℝ) : ℂ)
          * ∑ j ∈ Finset.Icc 1 J, patExt K H x (j - 1)
              * (starRingEnd ℂ) (patExt K H x (j - 1 + a i * h)) := by
    rw [sum_decObs_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hdvd : a i ∣ ∏ i', a i' := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
    have hai : ((a i : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (NeZero.ne (a i))
    have hcast : (((∏ i', a i') / a i : ℕ) : ℂ)
        = ((∏ i', a i' : ℕ) : ℂ) / ((a i : ℕ) : ℂ) := by
      rw [Nat.cast_div hdvd hai]
    rw [hcast]
    rw [show ((1 / (a i : ℝ) : ℝ) : ℂ) = 1 / ((a i : ℕ) : ℂ) from by
      push_cast
      ring]
    field_simp
  rw [hnorm]
  -- swap each truncated correlation for its circular version
  have hswap : ‖(∑ i, ((1 / (a i : ℝ) : ℝ) : ℂ)
      * ∑ j ∈ Finset.Icc 1 J, patExt K H x (j - 1)
          * (starRingEnd ℂ) (patExt K H x (j - 1 + a i * h)))
      - ∑ i, ((1 / (a i : ℝ) : ℝ) : ℂ)
          * ∑ v : ZMod J, patExt K H x v.val
              * (starRingEnd ℂ)
                (patExt K H x ((v + ((a i * h : ℕ) : ZMod J)).val))‖
      ≤ 8 * h * (Fintype.card ι : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    refine le_trans (norm_sum_le _ _) ?_
    have hper : ∀ i : ι, ‖((1 / (a i : ℝ) : ℝ) : ℂ)
        * ∑ j ∈ Finset.Icc 1 J, patExt K H x (j - 1)
            * (starRingEnd ℂ) (patExt K H x (j - 1 + a i * h))
        - ((1 / (a i : ℝ) : ℝ) : ℂ)
          * ∑ v : ZMod J, patExt K H x v.val
              * (starRingEnd ℂ)
                (patExt K H x ((v + ((a i * h : ℕ) : ZMod J)).val))‖
        ≤ 8 * h := by
      intro i
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (a i : ℝ))]
      have hcirc := norm_trunc_sub_circular_le hK x (hsJ i)
      have hai1 : (1 : ℝ) ≤ (a i : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (a i))
      calc (1 / (a i : ℝ))
          * ‖(∑ j ∈ Finset.Icc 1 J, patExt K H x (j - 1)
              * (starRingEnd ℂ) (patExt K H x (j - 1 + a i * h)))
            - ∑ v : ZMod J, patExt K H x v.val
                * (starRingEnd ℂ)
                  (patExt K H x ((v + ((a i * h : ℕ) : ZMod J)).val))‖
          ≤ (1 / (a i : ℝ)) * (8 * (a i * h)) :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast hcirc)
              (by positivity)
        _ = 8 * h * ((a i : ℝ) / (a i : ℝ)) := by
            ring
        _ = 8 * h := by
            rw [div_self (by linarith : (a i : ℝ) ≠ 0), mul_one]
    refine le_trans (Finset.sum_le_sum fun i _ => hper i) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  -- the circular form is the cap bilinear at C = 2
  have hpat2 : ∀ v : ZMod J, ‖patExt K H x v.val‖ ≤ 2 := fun v =>
    norm_patExt_le hK x v.val
  have hconj2 : ∀ v : ZMod J,
      ‖(starRingEnd ℂ) (patExt K H x v.val)‖ ≤ 2 := fun v => by
    rw [RCLike.norm_conj]
    exact norm_patExt_le hK x v.val
  have hcap := norm_block_bilinear_le' (H := J) Finset.univ
    (fun i => 1 / (a i : ℝ)) (fun i => ((a i * h : ℕ) : ZMod J))
    (fun v : ZMod J => patExt K H x v.val)
    (fun v : ZMod J => (starRingEnd ℂ) (patExt K H x v.val))
    (by norm_num : (0 : ℝ) ≤ 2) hpat2 hconj2
    (fun i _ => by positivity) hκ hθ
  have hcap' : ‖∑ i, ((1 / (a i : ℝ) : ℝ) : ℂ)
      * ∑ v : ZMod J, patExt K H x v.val
          * (starRingEnd ℂ)
            (patExt K H x ((v + ((a i * h : ℕ) : ZMod J)).val))‖
      ≤ 2 ^ 2 * θ * J + (J : ℝ) * κ * 2
          * ∑ ξ ∈ Finset.univ.filter (fun ξ : ZMod J =>
              θ ≤ ‖∑ i, ((1 / (a i : ℝ) : ℝ) : ℂ)
                * zChar (((a i * h : ℕ) : ZMod J)) ξ‖),
              ‖zDFT (fun v : ZMod J => patExt K H x v.val) (-ξ)‖ := hcap
  -- assemble by the triangle inequality
  have htri := norm_sub_norm_le
    (∑ i, ((1 / (a i : ℝ) : ℝ) : ℂ)
      * ∑ j ∈ Finset.Icc 1 J, patExt K H x (j - 1)
          * (starRingEnd ℂ) (patExt K H x (j - 1 + a i * h)))
    (∑ i, ((1 / (a i : ℝ) : ℝ) : ℂ)
      * ∑ v : ZMod J, patExt K H x v.val
          * (starRingEnd ℂ)
            (patExt K H x ((v + ((a i * h : ℕ) : ZMod J)).val)))
  have h4 : (2 : ℝ) ^ 2 = 4 := by norm_num
  linarith [hswap, hcap', htri, h4.le, h4.ge]

/-- The coordinate gate: the observable is a sum of per-modulus functions of
the residue coordinates. -/
noncomputable def gateC (K H J h : ℕ) (a : ι → ℕ) (x : PatternSpace K H)
    (i : ι) (r : ZMod (a i)) : ℂ :=
  ∑ j ∈ Finset.Icc 1 J,
    (if r = -((j : ℕ) : ZMod (a i))
      then patExt K H x (j - 1)
        * (starRingEnd ℂ) (patExt K H x (j - 1 + a i * h)) else 0)

theorem decObs_eq_sum_gateC (K H J h : ℕ) (a : ι → ℕ)
    (hcop : Pairwise (Nat.Coprime on a)) [∀ i, NeZero (a i)]
    (x : PatternSpace K H) (y : ZMod (∏ i, a i)) :
    decObs K H J h a hcop x y
      = ∑ i, gateC K H J h a x i (ZMod.prodEquivPi a hcop y i) := rfl

/-- The gate sums over its residues to the full truncated correlation. -/
theorem sum_gateC_eq (K H J h : ℕ) (a : ι → ℕ) [∀ i, NeZero (a i)]
    (x : PatternSpace K H) (i : ι) :
    ∑ r : ZMod (a i), gateC K H J h a x i r
      = ∑ j ∈ Finset.Icc 1 J, patExt K H x (j - 1)
          * (starRingEnd ℂ) (patExt K H x (j - 1 + a i * h)) := by
  classical
  rw [show (∑ r : ZMod (a i), gateC K H J h a x i r)
      = ∑ r : ZMod (a i), ∑ j ∈ Finset.Icc 1 J,
        (if r = -((j : ℕ) : ZMod (a i))
          then patExt K H x (j - 1)
            * (starRingEnd ℂ) (patExt K H x (j - 1 + a i * h)) else 0)
      from rfl]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ (-((j : ℕ) : ZMod (a i)))
    (fun _ => patExt K H x (j - 1)
      * (starRingEnd ℂ) (patExt K H x (j - 1 + a i * h)))]
  rw [if_pos (Finset.mem_univ _)]

/-- **The mean identity**: the global average of a real projection of the
observable is the weighted sum of the per-gate projections. -/
theorem sum_proj_decObs_eq (K H J h : ℕ) (a : ι → ℕ)
    (hcop : Pairwise (Nat.Coprime on a)) [∀ i, NeZero (a i)]
    (x : PatternSpace K H) (φ : ℂ →ₗ[ℝ] ℝ) :
    (∑ y : ZMod (∏ i, a i), φ (decObs K H J h a hcop x y))
        / ((∏ i, a i : ℕ) : ℝ)
      = ∑ i, φ (∑ r : ZMod (a i), gateC K H J h a x i r) / ((a i : ℕ) : ℝ) := by
  classical
  have hP0 : 0 < ∏ i, a i :=
    Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (NeZero.ne (a i))
  have hPne : ((∏ i, a i : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : (∏ i, a i) ≠ 0)
  have hsum : ∑ y : ZMod (∏ i, a i), φ (decObs K H J h a hcop x y)
      = φ (∑ y : ZMod (∏ i, a i), decObs K H J h a hcop x y) :=
    (map_sum φ _ _).symm
  rw [hsum, sum_decObs_eq, map_sum]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdvd : a i ∣ ∏ i', a i' := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
  have haine : ((a i : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne (a i))
  have hsmul : ((((∏ i', a i') / a i : ℕ) : ℂ))
      * ∑ j ∈ Finset.Icc 1 J, patExt K H x (j - 1)
          * (starRingEnd ℂ) (patExt K H x (j - 1 + a i * h))
      = ((((∏ i', a i') / a i : ℕ) : ℝ))
        • ∑ j ∈ Finset.Icc 1 J, patExt K H x (j - 1)
            * (starRingEnd ℂ) (patExt K H x (j - 1 + a i * h)) := by
    rw [Complex.real_smul]
    norm_num
  rw [hsmul, map_smul, smul_eq_mul, sum_gateC_eq]
  have hcast : (((∏ i', a i') / a i : ℕ) : ℝ)
      = ((∏ i', a i' : ℕ) : ℝ) / ((a i : ℕ) : ℝ) := by
    rw [Nat.cast_div hdvd haine]
  rw [hcast]
  field_simp

/-- The gate is bounded by four grid-pairs per residue hit. -/
theorem norm_gateC_le (K H J h : ℕ) (hK : 0 < K) (a : ι → ℕ)
    [∀ i, NeZero (a i)] (x : PatternSpace K H) (i : ι) (r : ZMod (a i)) :
    ‖gateC K H J h a x i r‖ ≤ 4 * ((J / a i + 1 : ℕ) : ℝ) := by
  classical
  rw [gateC]
  refine le_trans (norm_sum_le _ _) ?_
  have hite : ∀ j ∈ Finset.Icc 1 J,
      ‖(if r = -((j : ℕ) : ZMod (a i))
        then patExt K H x (j - 1)
          * (starRingEnd ℂ) (patExt K H x (j - 1 + a i * h)) else 0)‖
      = if ((j : ℕ) : ZMod (a i)) = -r then
          ‖patExt K H x (j - 1)
            * (starRingEnd ℂ) (patExt K H x (j - 1 + a i * h))‖ else 0 := by
    intro j _
    by_cases hc : r = -((j : ℕ) : ZMod (a i))
    · rw [if_pos hc, if_pos (by rw [hc, neg_neg])]
    · rw [if_neg hc, if_neg (fun hcc => hc (by rw [hcc, neg_neg])), norm_zero]
  rw [Finset.sum_congr rfl hite, ← Finset.sum_filter]
  have hper : ∀ j ∈ (Finset.Icc 1 J).filter
      (fun j => ((j : ℕ) : ZMod (a i)) = -r),
      ‖patExt K H x (j - 1)
        * (starRingEnd ℂ) (patExt K H x (j - 1 + a i * h))‖ ≤ 4 := by
    intro j _
    rw [norm_mul, RCLike.norm_conj]
    calc ‖patExt K H x (j - 1)‖ * ‖patExt K H x (j - 1 + a i * h)‖
        ≤ 2 * 2 := mul_le_mul (norm_patExt_le hK x _) (norm_patExt_le hK x _)
          (norm_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcount := card_filter_zmod_Icc_le (p := a i) (J := J) (-r)
  calc (((Finset.Icc 1 J).filter
      (fun j => ((j : ℕ) : ZMod (a i)) = -r)).card : ℝ) * 4
      ≤ ((J / a i + 1 : ℕ) : ℝ) * 4 :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (by norm_num)
    _ = 4 * ((J / a i + 1 : ℕ) : ℝ) := by ring

open scoped NNReal in
/-- **The deviation count for a real projection of the observable**: residues
where `φ ∘ decObs` deviates from its mean by `t` number at most
`2·exp(−t²/(2∑cᵢ²))·P` with `cᵢ = 8(J/aᵢ+1)` — the Hoeffding input of the
decoupling step. -/
theorem card_deviation_decObs_le (K H J h : ℕ) (hK : 0 < K) (a : ι → ℕ)
    (hcop : Pairwise (Nat.Coprime on a)) [∀ i, NeZero (a i)]
    (x : PatternSpace K H) (φ : ℂ →ₗ[ℝ] ℝ) (hφ : ∀ z, |φ z| ≤ ‖z‖)
    {t : ℝ} (ht : 0 ≤ t) :
    ((Finset.univ.filter (fun y : ZMod (∏ i, a i) =>
        t ≤ |φ (decObs K H J h a hcop x y)
          - (∑ y' : ZMod (∏ i, a i), φ (decObs K H J h a hcop x y'))
            / ((∏ i, a i : ℕ) : ℝ)|)).card : ℝ)
      ≤ 2 * Real.exp (-t ^ 2 / (2 * ((∑ i,
            (((8 * (J / a i + 1) : ℕ) : ℝ≥0)) ^ 2 : ℝ≥0) : ℝ)))
        * ((∏ i, a i : ℕ) : ℝ) := by
  classical
  have hP0 : 0 < ∏ i, a i :=
    Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (NeZero.ne (a i))
  have hPR : (0 : ℝ) < ((∏ i, a i : ℕ) : ℝ) := by exact_mod_cast hP0
  set c : ι → ℝ≥0 := fun i => (((8 * (J / a i + 1) : ℕ) : ℝ≥0)) with hc_def
  set f : Π i, ZMod (a i) → ℝ := fun i r =>
    φ (gateC K H J h a x i r)
      - φ (∑ r' : ZMod (a i), gateC K H J h a x i r') / ((a i : ℕ) : ℝ)
    with hf_def
  have hgatebound : ∀ i r, |φ (gateC K H J h a x i r)|
      ≤ 4 * ((J / a i + 1 : ℕ) : ℝ) := fun i r =>
    le_trans (hφ _) (norm_gateC_le K H J h hK a x i r)
  have havg : ∀ i, |φ (∑ r' : ZMod (a i), gateC K H J h a x i r')
      / ((a i : ℕ) : ℝ)| ≤ 4 * ((J / a i + 1 : ℕ) : ℝ) := by
    intro i
    have hpos : (0 : ℝ) < ((a i : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (a i))
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    calc |φ (∑ r' : ZMod (a i), gateC K H J h a x i r')|
        ≤ ‖∑ r' : ZMod (a i), gateC K H J h a x i r'‖ := hφ _
      _ ≤ ∑ r' : ZMod (a i), ‖gateC K H J h a x i r'‖ := norm_sum_le _ _
      _ ≤ ∑ _r' : ZMod (a i), 4 * ((J / a i + 1 : ℕ) : ℝ) :=
          Finset.sum_le_sum fun r' _ => norm_gateC_le K H J h hK a x i r'
      _ = 4 * ((J / a i + 1 : ℕ) : ℝ) * ((a i : ℕ) : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
          ring
  have hcR : ∀ i, ((c i : ℝ≥0) : ℝ) = 8 * ((J / a i + 1 : ℕ) : ℝ) := by
    intro i
    rw [hc_def]
    push_cast
    ring
  have hbound : ∀ i, ∀ r : ZMod (a i), f i r ∈ Set.Icc (-(c i : ℝ)) (c i) := by
    intro i r
    rw [Set.mem_Icc, hf_def]
    simp only []
    have h1 := abs_le.mp (hgatebound i r)
    have h2 := abs_le.mp (havg i)
    rw [hcR i]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hmean : ∀ i, ∑ r, f i r = 0 := by
    intro i
    rw [hf_def]
    simp only []
    rw [Finset.sum_sub_distrib, ← map_sum, Finset.sum_const,
      Finset.card_univ, ZMod.card, nsmul_eq_mul]
    have hne : ((a i : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne (a i))
    field_simp
    ring
  have hdev_eq : ∀ y : ZMod (∏ i, a i),
      φ (decObs K H J h a hcop x y)
        - (∑ y' : ZMod (∏ i, a i), φ (decObs K H J h a hcop x y'))
          / ((∏ i, a i : ℕ) : ℝ)
      = ∑ i, f i (ZMod.prodEquivPi a hcop y i) := by
    intro y
    rw [hf_def]
    simp only []
    rw [Finset.sum_sub_distrib]
    congr 1
    · rw [decObs_eq_sum_gateC, map_sum]
    · rw [sum_proj_decObs_eq K H J h a hcop x φ]
  -- split the two-sided event and count each side
  have hsub : Finset.univ.filter (fun y : ZMod (∏ i, a i) =>
      t ≤ |φ (decObs K H J h a hcop x y)
        - (∑ y' : ZMod (∏ i, a i), φ (decObs K H J h a hcop x y'))
          / ((∏ i, a i : ℕ) : ℝ)|)
      ⊆ (Finset.univ.filter (fun y : ZMod (∏ i, a i) =>
          t ≤ ∑ i, f i (ZMod.prodEquivPi a hcop y i)))
        ∪ Finset.univ.filter (fun y : ZMod (∏ i, a i) =>
            t ≤ ∑ i, (fun i r => - f i r) i (ZMod.prodEquivPi a hcop y i)) := by
    intro y hy
    rw [Finset.mem_filter] at hy
    rw [hdev_eq y] at hy
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases le_abs.mp hy.2 with hpos | hneg
    · exact Or.inl ⟨Finset.mem_univ _, hpos⟩
    · refine Or.inr ⟨Finset.mem_univ _, ?_⟩
      rw [show (∑ i, (fun i r => - f i r) i (ZMod.prodEquivPi a hcop y i))
          = - ∑ i, f i (ZMod.prodEquivPi a hcop y i) from by
        rw [← Finset.sum_neg_distrib]]
      exact hneg
  have hside1 := card_deviation_le_zmod a hcop f c hbound hmean ht
  have hside2 := card_deviation_le_zmod a hcop (fun i r => - f i r) c
    (fun i r => by
      have := hbound i r
      rw [Set.mem_Icc] at this ⊢
      constructor <;> simp only [] <;> linarith [this.1, this.2])
    (fun i => by
      simp only []
      rw [Finset.sum_neg_distrib, hmean i, neg_zero])
    ht
  have hcard := Finset.card_le_card hsub
  have hcard2 := Finset.card_union_le
    (Finset.univ.filter (fun y : ZMod (∏ i, a i) =>
      t ≤ ∑ i, f i (ZMod.prodEquivPi a hcop y i)))
    (Finset.univ.filter (fun y : ZMod (∏ i, a i) =>
      t ≤ ∑ i, (fun i r => - f i r) i (ZMod.prodEquivPi a hcop y i)))
  have hs1 : ((Finset.univ.filter (fun y : ZMod (∏ i, a i) =>
      t ≤ ∑ i, f i (ZMod.prodEquivPi a hcop y i))).card : ℝ)
      ≤ Real.exp (-t ^ 2 / (2 * ((∑ i, (c i) ^ 2 : ℝ≥0) : ℝ)))
        * ((∏ i, a i : ℕ) : ℝ) := by
    rw [← div_le_iff₀ hPR]
    exact hside1
  have hs2 : ((Finset.univ.filter (fun y : ZMod (∏ i, a i) =>
      t ≤ ∑ i, (fun i r => - f i r) i (ZMod.prodEquivPi a hcop y i))).card : ℝ)
      ≤ Real.exp (-t ^ 2 / (2 * ((∑ i, (c i) ^ 2 : ℝ≥0) : ℝ)))
        * ((∏ i, a i : ℕ) : ℝ) := by
    rw [← div_le_iff₀ hPR]
    exact hside2
  have hchain : ((Finset.univ.filter (fun y : ZMod (∏ i, a i) =>
      t ≤ |φ (decObs K H J h a hcop x y)
        - (∑ y' : ZMod (∏ i, a i), φ (decObs K H J h a hcop x y'))
          / ((∏ i, a i : ℕ) : ℝ)|)).card : ℝ)
      ≤ 2 * Real.exp (-t ^ 2 / (2 * ((∑ i, (c i) ^ 2 : ℝ≥0) : ℝ)))
        * ((∏ i, a i : ℕ) : ℝ) := by
    have hc1 : ((Finset.univ.filter (fun y : ZMod (∏ i, a i) =>
        t ≤ |φ (decObs K H J h a hcop x y)
          - (∑ y' : ZMod (∏ i, a i), φ (decObs K H J h a hcop x y'))
            / ((∏ i, a i : ℕ) : ℝ)|)).card : ℝ)
        ≤ ((Finset.univ.filter (fun y : ZMod (∏ i, a i) =>
            t ≤ ∑ i, f i (ZMod.prodEquivPi a hcop y i))).card : ℝ)
          + ((Finset.univ.filter (fun y : ZMod (∏ i, a i) =>
              t ≤ ∑ i, (fun i r => - f i r) i
                (ZMod.prodEquivPi a hcop y i))).card : ℝ) := by
      have := le_trans hcard hcard2
      exact_mod_cast this
    linarith [hs1, hs2]
  exact hchain

end Observable

end MoltResearch
