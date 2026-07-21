import MoltResearch.Discrepancy
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Elliott
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5MatomakiRadziwill
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5QuadrupleSieve

/-!
# Track C: Stage 5 — the Elliott assembly (M3 of issue #2946)

The master unit of the Elliott campaign: composing the merged toolbox
(Proposition `conv`, the decrement observable and its expectation bridge,
the entropy-decrement scale selection, the decoupling step, Hoeffding,
the circle method, and the two cited-input interfaces) into

  `instance [MatomakiRadziwillAssumption] [PrimeQuadrupleCountAssumption] :
      LogElliottNonasymptoticAssumption`

via the `elliott-red` contradiction of arXiv:1509.05422 §3.

This file is Conjectures-side glue: every lemma here is a quantitative
composition of nucleus lemmas; the only assumptions consumed are the two
permanent interfaces above.

Layer 1 (this section): sharpened observable bounds. The merged pointwise
and expectation bridges cost `|ι|·J·(12/K)`; the master schedule needs the
gate-count-sharp form `(∑ᵢ (J/aᵢ + 1))·(12/K)` — per modulus, an interval
of length `J` meets the residue gate at most `J/aᵢ + 1` times.
-/

namespace MoltResearch

open Finset
open scoped Function

section AssemblyHelpers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pushforward expectation dictionary, `ℝ`-valued: integrating an observable
against the pushed law is integrating its pullback. -/
theorem sum_pushWeight_mul_real (s : Finset ℕ) (w : ℕ → ℝ) {β : Type*}
    [Fintype β] [DecidableEq β] (f : ℕ → β) (F : β → ℝ) :
    ∑ b, pushWeight s w f b * F b = ∑ n ∈ s, w n * F (f n) := by
  classical
  rw [show (∑ b, pushWeight s w f b * F b)
      = ∑ b, ∑ n ∈ s.filter (fun n => f n = b), w n * F b from
    Finset.sum_congr rfl fun b _ => by rw [pushWeight, Finset.sum_mul]]
  rw [← Finset.sum_fiberwise_of_maps_to (g := f)
    (fun n _ => Finset.mem_univ (f n)) (fun n => w n * F (f n))]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_filter] at hn
  rw [hn.2]

/-- The observable is bounded by the total gate count: the sharp form of
`norm_decObs_le` the decoupling step needs. -/
theorem norm_decObs_le_sum (K H J h : ℕ) (hK : 0 < K) (a : ι → ℕ)
    (hcop : Pairwise (Nat.Coprime on a)) [∀ i, NeZero (a i)]
    (x : PatternSpace K H) (y : ZMod (∏ i, a i)) :
    ‖decObs K H J h a hcop x y‖ ≤ ∑ i, 4 * ((J / a i + 1 : ℕ) : ℝ) := by
  rw [decObs_eq_sum_gateC]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  exact norm_gateC_le K H J h hK a x i _

omit [Fintype ι] [DecidableEq ι] in
/-- The divisor gate of the true observable opens iff the corresponding
residue gate does. -/
theorem decObs_gate_iff (a : ι → ℕ) [∀ i, NeZero (a i)] (n j : ℕ) (i : ι) :
    (n + j) % a i = 0 ↔ ((j : ℕ) : ZMod (a i)) = -((n : ℕ) : ZMod (a i)) := by
  constructor
  · intro hc
    have hdvd : ((n + j : ℕ) : ZMod (a i)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact Nat.dvd_iff_mod_eq_zero.mpr hc
    push_cast at hdvd
    exact eq_neg_of_add_eq_zero_right hdvd
  · intro hc
    have hdvd : ((n + j : ℕ) : ZMod (a i)) = 0 := by
      push_cast
      rw [hc]
      ring
    rw [ZMod.natCast_eq_zero_iff] at hdvd
    exact Nat.dvd_iff_mod_eq_zero.mp hdvd

/-- **The sharp pointwise rounding bridge**: at a sampled point, the observable
is the true conjugate-pair divisor sum up to `(∑ᵢ (J/aᵢ + 1))·(12/K)` — only
open gates pay the rounding cost. -/
theorem norm_decObs_sub_le' (g : ℕ → ℂ) (huni : Unimodular g)
    (K H J h : ℕ) (hK : 0 < K) (a : ι → ℕ)
    (hcop : Pairwise (Nat.Coprime on a)) [∀ i, NeZero (a i)]
    (hH : ∀ i, J + a i * h ≤ H) (n : ℕ) :
    ‖decObs K H J h a hcop (patternMap g K H n) ((n : ZMod (∏ i, a i)))
        - ∑ i, ∑ j ∈ Finset.Icc 1 J,
          (if (n + j) % a i = 0
            then g (n + j) * (starRingEnd ℂ) (g (n + j + a i * h)) else 0)‖
      ≤ (∑ i, ((J / a i + 1 : ℕ) : ℝ)) * (12 / K) := by
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
      ≤ ((J / a i + 1 : ℕ) : ℝ) * (12 / K) := by
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
        ≤ if (n + j) % a i = 0 then 12 / (K : ℝ) else 0 := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      -- the two gate conditions agree
      have hcond : (ZMod.prodEquivPi a hcop ((n : ZMod (∏ i, a i))) i
          = -((j : ℕ) : ZMod (a i))) ↔ ((n + j) % a i = 0) := by
        rw [prodEquivPi_natCast]
        constructor
        · intro hc
          have hz : ((n + j : ℕ) : ZMod (a i)) = 0 := by
            push_cast
            rw [hc]
            ring
          rw [ZMod.natCast_eq_zero_iff] at hz
          exact Nat.dvd_iff_mod_eq_zero.mp hz
        · intro hc
          have hz : ((n + j : ℕ) : ZMod (a i)) = 0 := by
            rw [ZMod.natCast_eq_zero_iff]
            exact Nat.dvd_iff_mod_eq_zero.mpr hc
          push_cast at hz
          exact eq_neg_of_add_eq_zero_left hz
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
      · rw [if_pos ((hcond.mpr hc :
          ZMod.prodEquivPi a hcop ((n : ZMod (∏ i, a i))) i
            = -((j : ℕ) : ZMod (a i)))), if_pos hc, if_pos hc, hv1, hv2]
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
              have hmap : (starRingEnd ℂ) r2
                  - (starRingEnd ℂ) (g (n + j + a i * h))
                  = (starRingEnd ℂ) (r2 - g (n + j + a i * h)) := by
                rw [map_sub]
              rw [hmap, RCLike.norm_conj]
          _ ≤ (4 / K) * 2 + 1 * (4 / K) := by
              have hn1 : ‖r1 - g (n + j)‖ ≤ 4 / K := by
                rw [norm_sub_rev]
                exact hr1
              have hn2 : ‖r2 - g (n + j + a i * h)‖ ≤ 4 / K := by
                rw [norm_sub_rev]
                exact hr2
              rw [hg1]
              refine add_le_add ?_ ?_
              · exact mul_le_mul hn1 hrb2 (norm_nonneg _) (by positivity)
              · exact mul_le_mul_of_nonneg_left hn2 (by norm_num)
          _ = 12 / K := by ring
      · rw [if_neg (fun hcc => hc (hcond.mp hcc)), if_neg hc, if_neg hc,
          sub_zero, norm_zero]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcount : ((Finset.Icc 1 J).filter
        (fun j => (n + j) % a i = 0)).card ≤ J / a i + 1 := by
      have hfe : (Finset.Icc 1 J).filter (fun j => (n + j) % a i = 0)
          = (Finset.Icc 1 J).filter
            (fun j => ((j : ℕ) : ZMod (a i)) = -((n : ℕ) : ZMod (a i))) :=
        Finset.filter_congr fun j _ => decObs_gate_iff a n j i
      rw [hfe]
      exact card_filter_zmod_Icc_le (-((n : ℕ) : ZMod (a i)))
    have hKR : (0 : ℝ) ≤ 12 / (K : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hKR
  refine le_trans (Finset.sum_le_sum fun i _ => hper i) (le_of_eq ?_)
  rw [Finset.sum_mul]

/-- **The sharp expectation bridge**: the joint-law expectation of the
observable is the normalized triple sum of Proposition `conv`, up to the
gate-count-sharp rounding cost. -/
theorem norm_sum_jointLaw_decObs_sub_le' (g : ℕ → ℂ) (huni : Unimodular g)
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
      ≤ (∑ i, ((J / a i + 1 : ℕ) : ℝ)) * (12 / K) := by
  classical
  have hpush := sum_pushWeight_mul_complex (Finset.Ioc A B) (logWeight A B)
    (fun n => (patternMap g K H n, (n : ZMod (∏ i, a i))))
    (fun z => decObs K H J h a hcop z.1 z.2)
  have hjoint : (∑ z : PatternSpace K H × ZMod (∏ i, a i),
      ((jointLaw g K H (∏ i, a i) A B z : ℝ) : ℂ)
        * decObs K H J h a hcop z.1 z.2)
      = ∑ n ∈ Finset.Ioc A B, ((logWeight A B n : ℝ) : ℂ)
          * decObs K H J h a hcop (patternMap g K H n)
            ((n : ZMod (∏ i, a i))) := hpush
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
      ≤ logWeight A B n * ((∑ i, ((J / a i + 1 : ℕ) : ℝ)) * (12 / K)) := by
    intro n _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (logWeight_nonneg A B n)]
    exact mul_le_mul_of_nonneg_left
      (norm_decObs_sub_le' g huni K H J h hK a hcop hH n)
      (logWeight_nonneg A B n)
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [← Finset.sum_mul, sum_logWeight hA hAB, one_mul]

omit [Fintype ι] [DecidableEq ι] in
/-- The DFT of a pointwise-close pair is close: the rounded→true swap under
the transform. -/
theorem norm_zDFT_sub_le {H : ℕ} [NeZero H] (F G : ZMod H → ℂ) {C : ℝ}
    (hFG : ∀ v, ‖F v - G v‖ ≤ C) (ξ : ZMod H) :
    ‖zDFT F ξ - zDFT G ξ‖ ≤ C := by
  have hsub : zDFT F ξ - zDFT G ξ = zDFT (fun v => F v - G v) ξ := by
    rw [zDFT, zDFT, zDFT, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [hsub]
  exact norm_zDFT_le' _ hFG ξ

omit [Fintype ι] [DecidableEq ι] in
/-- **The Matomäki–Radziwiłł-facing dictionary**: the pattern-window DFT at a
cast frequency is the classical modulated short-interval mean, in norm — the
`ZMod` circle method meets the `e(jα)` interface shape. -/
theorem norm_zDFT_window_eq (g : ℕ → ℂ) {J : ℕ} [NeZero J] (n : ℕ)
    (ξ : ZMod J) :
    ‖zDFT (fun v : ZMod J => g (n + 1 + v.val)) (-ξ)‖
      = (1 / (J : ℝ)) * ‖∑ j ∈ Finset.Icc 1 J,
          g (n + j) * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ)
            * (((ξ.val : ℝ) / (J : ℝ) : ℝ) : ℂ))‖ := by
  classical
  have hJR : (0 : ℝ) < (J : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne J)
  -- unfold the transform and cancel the double conjugation
  have hconj : ∀ v : ZMod J,
      (starRingEnd ℂ) (zChar v (-ξ)) = zChar v ξ := by
    intro v
    rw [conj_zChar, zChar_neg_neg]
  have hdft : zDFT (fun v : ZMod J => g (n + 1 + v.val)) (-ξ)
      = (1 / (J : ℂ)) * ∑ v : ZMod J, g (n + 1 + v.val) * zChar v ξ := by
    rw [zDFT]
    congr 1
    exact Finset.sum_congr rfl fun v _ => by rw [hconj v]
  -- the value-range form
  have hrange : ∑ v : ZMod J, g (n + 1 + v.val) * zChar v ξ
      = ∑ m ∈ Finset.range J, g (n + 1 + m) * zChar ((m : ℕ) : ZMod J) ξ := by
    rw [sum_zmod_eq_sum_range (fun v : ZMod J => g (n + 1 + v.val)
      * zChar v ξ)]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [ZMod.val_natCast_of_lt hm]
  -- the `Icc`-window form, with the unit phase factor pulled out
  have hicc : ∑ j ∈ Finset.Icc 1 J, g (n + j) * zChar ((j : ℕ) : ZMod J) ξ
      = zChar ((1 : ℕ) : ZMod J) ξ
        * ∑ m ∈ Finset.range J, g (n + 1 + m) * zChar ((m : ℕ) : ZMod J) ξ := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij' (fun j _ => j - 1) (fun m _ => m + 1)
      ?_ ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_Icc] at hj
      show j - 1 ∈ Finset.range J
      rw [Finset.mem_range]
      omega
    · intro m hm
      rw [Finset.mem_range] at hm
      show m + 1 ∈ Finset.Icc 1 J
      rw [Finset.mem_Icc]
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
      show g (n + j) * zChar ((j : ℕ) : ZMod J) ξ
        = zChar ((1 : ℕ) : ZMod J) ξ
          * (g (n + 1 + (j - 1)) * zChar (((j - 1 : ℕ)) : ZMod J) ξ)
      have harg : n + 1 + (j - 1) = n + j := by omega
      have hjsplit : ((j : ℕ) : ZMod J) = ((1 : ℕ) : ZMod J)
          + (((j - 1 : ℕ)) : ZMod J) := by
        have hone : ((1 + (j - 1) : ℕ) : ZMod J) = ((j : ℕ) : ZMod J) := by
          congr 1
          omega
        rw [← hone]
        push_cast
        ring
      rw [harg, hjsplit, zChar_add_left]
      ring
  -- assemble, killing the unit factors
  have hexp : ∀ j ∈ Finset.Icc 1 J,
      g (n + j) * zChar ((j : ℕ) : ZMod J) ξ
        = g (n + j) * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ)
            * (((ξ.val : ℝ) / (J : ℝ) : ℝ) : ℂ)) := by
    intro j _
    rw [zChar_natCast_eq_exp]
  calc ‖zDFT (fun v : ZMod J => g (n + 1 + v.val)) (-ξ)‖
      = ‖(1 / (J : ℂ))
          * ∑ m ∈ Finset.range J, g (n + 1 + m) * zChar ((m : ℕ) : ZMod J) ξ‖ := by
        rw [hdft, hrange]
    _ = (1 / (J : ℝ))
        * ‖∑ m ∈ Finset.range J, g (n + 1 + m) * zChar ((m : ℕ) : ZMod J) ξ‖ := by
        rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
    _ = (1 / (J : ℝ))
        * ‖∑ j ∈ Finset.Icc 1 J, g (n + j) * zChar ((j : ℕ) : ZMod J) ξ‖ := by
        rw [hicc, norm_mul, norm_zChar, one_mul]
    _ = (1 / (J : ℝ)) * ‖∑ j ∈ Finset.Icc 1 J,
          g (n + j) * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ)
            * (((ξ.val : ℝ) / (J : ℝ) : ℝ) : ℂ))‖ := by
        rw [Finset.sum_congr rfl hexp]

/-- **The per-frequency pattern-averaged DFT against the true windows**: the
`X`-average of the pattern DFT mass is the log-averaged true-window mass, up
to the rounding swap `4/K`. -/
theorem sum_patternLaw_norm_zDFT_le (g : ℕ → ℂ) (huni : Unimodular g)
    (K H J : ℕ) [NeZero J] (hK : 0 < K) (hJH : J ≤ H)
    {A B : ℕ} (hA : 1 ≤ A) (hAB : A < B) (ξ : ZMod J) :
    ∑ x, patternLaw g K H A B x
        * ‖zDFT (fun v : ZMod J => patExt K H x v.val) (-ξ)‖
      ≤ 4 / K + ∑ n ∈ Finset.Ioc A B, logWeight A B n * ((1 / (J : ℝ))
          * ‖∑ j ∈ Finset.Icc 1 J, g (n + j)
              * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ)
                * (((ξ.val : ℝ) / (J : ℝ) : ℝ) : ℂ))‖) := by
  classical
  have hpush := sum_pushWeight_mul_real (Finset.Ioc A B) (logWeight A B)
    (patternMap g K H)
    (fun x => ‖zDFT (fun v : ZMod J => patExt K H x v.val) (-ξ)‖)
  have hlhs : ∑ x, patternLaw g K H A B x
      * ‖zDFT (fun v : ZMod J => patExt K H x v.val) (-ξ)‖
      = ∑ n ∈ Finset.Ioc A B, logWeight A B n
          * ‖zDFT (fun v : ZMod J =>
              patExt K H (patternMap g K H n) v.val) (-ξ)‖ := hpush
  rw [hlhs]
  have hper : ∀ n ∈ Finset.Ioc A B,
      logWeight A B n * ‖zDFT (fun v : ZMod J =>
          patExt K H (patternMap g K H n) v.val) (-ξ)‖
      ≤ logWeight A B n * (4 / K)
        + logWeight A B n * ((1 / (J : ℝ))
          * ‖∑ j ∈ Finset.Icc 1 J, g (n + j)
              * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ)
                * (((ξ.val : ℝ) / (J : ℝ) : ℝ) : ℂ))‖) := by
    intro n _
    have hswap : ‖zDFT (fun v : ZMod J =>
        patExt K H (patternMap g K H n) v.val) (-ξ)
        - zDFT (fun v : ZMod J => g (n + 1 + v.val)) (-ξ)‖ ≤ 4 / K := by
      refine norm_zDFT_sub_le _ _ (fun v => ?_) (-ξ)
      have hv : v.val < H := lt_of_lt_of_le (ZMod.val_lt v) hJH
      rw [patExt_patternMap g K H n v.val hv]
      rw [norm_sub_rev]
      exact norm_sub_roundCVal_le hK (le_of_eq (huni (n + 1 + v.val)))
    have htri : ‖zDFT (fun v : ZMod J =>
        patExt K H (patternMap g K H n) v.val) (-ξ)‖
        ≤ 4 / K + ‖zDFT (fun v : ZMod J => g (n + 1 + v.val)) (-ξ)‖ := by
      have h := norm_sub_norm_le
        (zDFT (fun v : ZMod J => patExt K H (patternMap g K H n) v.val) (-ξ))
        (zDFT (fun v : ZMod J => g (n + 1 + v.val)) (-ξ))
      linarith [le_trans h hswap]
    rw [norm_zDFT_window_eq g n ξ] at htri
    have hw0 := logWeight_nonneg A B n
    calc logWeight A B n * ‖zDFT (fun v : ZMod J =>
        patExt K H (patternMap g K H n) v.val) (-ξ)‖
        ≤ logWeight A B n * (4 / K + (1 / (J : ℝ))
            * ‖∑ j ∈ Finset.Icc 1 J, g (n + j)
                * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ)
                  * (((ξ.val : ℝ) / (J : ℝ) : ℝ) : ℂ))‖) :=
          mul_le_mul_of_nonneg_left htri hw0
      _ = logWeight A B n * (4 / K)
          + logWeight A B n * ((1 / (J : ℝ))
            * ‖∑ j ∈ Finset.Icc 1 J, g (n + j)
                * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ)
                  * (((ξ.val : ℝ) / (J : ℝ) : ℝ) : ℂ))‖) := by ring
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_logWeight hA hAB, one_mul]

open scoped NNReal in
/-- **The single-scale master upper bound** (the M1 unit): at a scale where the
mutual information is small (`hI`), the residue law is near-uniform (`hunif`),
the observable concentrates (`hdev`), and the true-window modulated means are
small at every major frequency (`hMR`), the joint-law expectation of the
observable is controlled by the decoupling, strip, minor-frequency, rounding,
and Matomäki–Radziwiłł costs. -/
theorem norm_sum_jointLaw_decObs_le (g : ℕ → ℂ)
    (K H J h : ℕ) [NeZero J] (hK : 0 < K)
    (a : ι → ℕ) (hcop : Pairwise (Nat.Coprime on a)) [∀ i, NeZero (a i)]
    (hsJ : ∀ i, a i * h < J)
    {A B : ℕ} (hA : 1 ≤ A) (hAB : A < B)
    {θ κ : ℝ} (hθ : 0 ≤ θ) (hκ : ∑ i, 1 / ((a i : ℝ)) ≤ κ) (hκ0 : 0 ≤ κ)
    {τ τ' θ₀ t D M ρ : ℝ}
    (hM : ∑ i, 4 * ((J / a i + 1 : ℕ) : ℝ) ≤ M) (hM0 : 0 ≤ M)
    (hθ₀ : 0 ≤ θ₀) (hτ' : 0 < τ' + θ₀) (ht : 0 ≤ t) (hD : 0 < D)
    (hI : mutualInfo (jointLaw g K H (∏ i, a i) A B) ≤ τ)
    (hunif : Real.log ((∏ i, a i : ℕ) : ℝ) - θ₀
      ≤ shannonEntropy (residueLaw (∏ i, a i) A B))
    (hdev : ∀ (φ : ℂ →ₗ[ℝ] ℝ), (∀ z, |φ z| ≤ ‖z‖) → ∀ x : PatternSpace K H,
      (((Finset.univ.filter (fun y : ZMod (∏ i, a i) =>
        t ≤ |φ (decObs K H J h a hcop x y)
          - (∑ y', φ (decObs K H J h a hcop x y'))
            / ((∏ i, a i : ℕ) : ℝ)|)).card : ℝ)
        ≤ Real.exp (-D) * ((∏ i, a i : ℕ) : ℝ)))
    {ρ4K : ℝ}
    (hswap : ∀ ξ ∈ Finset.univ.filter (fun ξ : ZMod J =>
        θ ≤ ‖∑ i, ((1 / (a i : ℝ) : ℝ) : ℂ)
          * zChar (((a i * h : ℕ) : ZMod J)) ξ‖),
      ∑ x, patternLaw g K H A B x
          * ‖zDFT (fun v : ZMod J => patExt K H x v.val) (-ξ)‖ ≤ ρ4K + ρ) :
    ‖∑ z : PatternSpace K H × ZMod (∏ i, a i),
        ((jointLaw g K H (∏ i, a i) A B z : ℝ) : ℂ)
          * decObs K H J h a hcop z.1 z.2‖
      ≤ 2 * (t + 2 * M * ((τ + θ₀) / (τ' + θ₀)
            + (τ' + θ₀ + Real.log 2) / D))
        + 2 * (8 * h * (Fintype.card ι : ℝ) + 4 * θ * J
          + (J : ℝ) * κ * 2
            * (((Finset.univ.filter (fun ξ : ZMod J =>
                θ ≤ ‖∑ i, ((1 / (a i : ℝ) : ℝ) : ℂ)
                  * zChar (((a i * h : ℕ) : ZMod J)) ξ‖)).card : ℝ)
              * (ρ4K + ρ))) := by
  classical
  have hP0 : 0 < ∏ i, a i :=
    Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (NeZero.ne (a i))
  have hPR : (0 : ℝ) < ((∏ i, a i : ℕ) : ℝ) := by exact_mod_cast hP0
  set P : ℕ := ∏ i, a i with hPdef
  set E : ℂ := ∑ z : PatternSpace K H × ZMod P,
    ((jointLaw g K H P A B z : ℝ) : ℂ) * decObs K H J h a hcop z.1 z.2
    with hEdef
  set Ξ : Finset (ZMod J) := Finset.univ.filter (fun ξ : ZMod J =>
    θ ≤ ‖∑ i, ((1 / (a i : ℝ) : ℝ) : ℂ)
      * zChar (((a i * h : ℕ) : ZMod J)) ξ‖) with hΞdef
  -- the projected expectation is the expectation of the projection
  have hproj : ∀ (φ : ℂ →ₗ[ℝ] ℝ), φ E
      = ∑ z : PatternSpace K H × ZMod P,
          jointLaw g K H P A B z * φ (decObs K H J h a hcop z.1 z.2) := by
    intro φ
    rw [hEdef, map_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← Complex.real_smul, map_smul, smul_eq_mul]
  -- the shared bound on the decoupled average
  have havg : ∑ x, patternLaw g K H A B x
      * ‖(1 / ((P : ℕ) : ℂ)) * ∑ y : ZMod P, decObs K H J h a hcop x y‖
      ≤ 8 * h * (Fintype.card ι : ℝ) + 4 * θ * J
        + (J : ℝ) * κ * 2 * ((Ξ.card : ℝ) * (ρ4K + ρ)) := by
    have hper : ∀ x : PatternSpace K H,
        ‖(1 / ((P : ℕ) : ℂ)) * ∑ y : ZMod P, decObs K H J h a hcop x y‖
        ≤ 8 * h * (Fintype.card ι : ℝ) + 4 * θ * J
          + (J : ℝ) * κ * 2
            * ∑ ξ ∈ Ξ, ‖zDFT (fun v : ZMod J => patExt K H x v.val) (-ξ)‖ :=
      fun x => norm_avg_decObs_le K H J h hK a hcop hsJ hθ hκ x
    have hpat0 : ∀ x, 0 ≤ patternLaw g K H A B x := patternLaw_nonneg g K H A B
    have hpatsum : ∑ x, patternLaw g K H A B x = 1 :=
      sum_patternLaw g K H hA hAB
    have hswapsum : ∑ x, patternLaw g K H A B x * ∑ ξ ∈ Ξ,
        ‖zDFT (fun v : ZMod J => patExt K H x v.val) (-ξ)‖
        ≤ (Ξ.card : ℝ) * (ρ4K + ρ) := by
      have hcomm : ∑ x, patternLaw g K H A B x * ∑ ξ ∈ Ξ,
          ‖zDFT (fun v : ZMod J => patExt K H x v.val) (-ξ)‖
          = ∑ ξ ∈ Ξ, ∑ x, patternLaw g K H A B x
              * ‖zDFT (fun v : ZMod J => patExt K H x v.val) (-ξ)‖ := by
        rw [Finset.sum_congr rfl fun x _ => Finset.mul_sum _ _ _]
        rw [Finset.sum_comm]
      rw [hcomm]
      calc ∑ ξ ∈ Ξ, ∑ x, patternLaw g K H A B x
          * ‖zDFT (fun v : ZMod J => patExt K H x v.val) (-ξ)‖
          ≤ ∑ _ξ ∈ Ξ, (ρ4K + ρ) :=
            Finset.sum_le_sum fun ξ hξ => hswap ξ hξ
        _ = (Ξ.card : ℝ) * (ρ4K + ρ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hsplit : ∑ x, patternLaw g K H A B x
        * (8 * h * (Fintype.card ι : ℝ) + 4 * θ * J
          + (J : ℝ) * κ * 2 * ∑ ξ ∈ Ξ,
            ‖zDFT (fun v : ZMod J => patExt K H x v.val) (-ξ)‖)
        = (8 * h * (Fintype.card ι : ℝ) + 4 * θ * J)
            * ∑ x, patternLaw g K H A B x
          + (J : ℝ) * κ * 2 * ∑ x, patternLaw g K H A B x * ∑ ξ ∈ Ξ,
              ‖zDFT (fun v : ZMod J => patExt K H x v.val) (-ξ)‖ := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    have hc0 : (0 : ℝ) ≤ (J : ℝ) * κ * 2 := by positivity
    calc ∑ x, patternLaw g K H A B x
        * ‖(1 / ((P : ℕ) : ℂ)) * ∑ y : ZMod P, decObs K H J h a hcop x y‖
        ≤ ∑ x, patternLaw g K H A B x
            * (8 * h * (Fintype.card ι : ℝ) + 4 * θ * J
              + (J : ℝ) * κ * 2 * ∑ ξ ∈ Ξ,
                ‖zDFT (fun v : ZMod J => patExt K H x v.val) (-ξ)‖) :=
          Finset.sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_left (hper x) (hpat0 x)
      _ = (8 * h * (Fintype.card ι : ℝ) + 4 * θ * J)
            * ∑ x, patternLaw g K H A B x
          + (J : ℝ) * κ * 2 * ∑ x, patternLaw g K H A B x * ∑ ξ ∈ Ξ,
              ‖zDFT (fun v : ZMod J => patExt K H x v.val) (-ξ)‖ := hsplit
      _ ≤ (8 * h * (Fintype.card ι : ℝ) + 4 * θ * J) * 1
          + (J : ℝ) * κ * 2 * ((Ξ.card : ℝ) * (ρ4K + ρ)) := by
          rw [hpatsum]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hswapsum hc0)
      _ = 8 * h * (Fintype.card ι : ℝ) + 4 * θ * J
          + (J : ℝ) * κ * 2 * ((Ξ.card : ℝ) * (ρ4K + ρ)) := by ring
  -- the per-projection master bound
  have key : ∀ (φ : ℂ →ₗ[ℝ] ℝ), (∀ z, |φ z| ≤ ‖z‖) →
      |φ E| ≤ (t + 2 * M * ((τ + θ₀) / (τ' + θ₀)
            + (τ' + θ₀ + Real.log 2) / D))
        + (8 * h * (Fintype.card ι : ℝ) + 4 * θ * J
          + (J : ℝ) * κ * 2 * ((Ξ.card : ℝ) * (ρ4K + ρ))) := by
    intro φ hφ
    set F : PatternSpace K H × ZMod P → ℝ :=
      fun z => φ (decObs K H J h a hcop z.1 z.2) with hFdef
    have hFM : ∀ z, |F z| ≤ M := fun z =>
      le_trans (hφ _)
        (le_trans (norm_decObs_le_sum K H J h hK a hcop z.1 z.2) hM)
    have hdec := abs_sum_jointLaw_mul_sub_le g K H P hA hAB F hM0 hFM
      hθ₀ hI hτ' ht hD hunif (hdev φ hφ)
    have hφE : φ E = ∑ z : PatternSpace K H × ZMod P,
        jointLaw g K H P A B z * F z := hproj φ
    have havgF : ∀ x : PatternSpace K H,
        |(∑ y : ZMod P, F (x, y)) / ((P : ℕ) : ℝ)|
        ≤ ‖(1 / ((P : ℕ) : ℂ)) * ∑ y : ZMod P, decObs K H J h a hcop x y‖ := by
      intro x
      have hmap : ∑ y : ZMod P, F (x, y)
          = φ (∑ y : ZMod P, decObs K H J h a hcop x y) := (map_sum φ _ _).symm
      have hnorm : ‖(1 / ((P : ℕ) : ℂ))
          * ∑ y : ZMod P, decObs K H J h a hcop x y‖
          = ‖∑ y : ZMod P, decObs K H J h a hcop x y‖ / ((P : ℕ) : ℝ) := by
        rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
        ring
      rw [hmap, hnorm, abs_div, abs_of_pos hPR]
      gcongr
      exact hφ _
    have hXavg : |∑ x, patternLaw g K H A B x
        * ((∑ y : ZMod P, F (x, y)) / ((P : ℕ) : ℝ))|
        ≤ 8 * h * (Fintype.card ι : ℝ) + 4 * θ * J
          + (J : ℝ) * κ * 2 * ((Ξ.card : ℝ) * (ρ4K + ρ)) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans ?_ havg)
      refine Finset.sum_le_sum fun x _ => ?_
      rw [abs_mul, abs_of_nonneg (patternLaw_nonneg g K H A B x)]
      exact mul_le_mul_of_nonneg_left (havgF x)
        (patternLaw_nonneg g K H A B x)
    rw [hφE]
    have htri := abs_sub_abs_le_abs_sub
      (∑ z : PatternSpace K H × ZMod P, jointLaw g K H P A B z * F z)
      (∑ x, patternLaw g K H A B x
        * ((∑ y : ZMod P, F (x, y)) / ((P : ℕ) : ℝ)))
    have habs : |∑ z : PatternSpace K H × ZMod P,
        jointLaw g K H P A B z * F z|
        ≤ |∑ x, patternLaw g K H A B x
            * ((∑ y : ZMod P, F (x, y)) / ((P : ℕ) : ℝ))|
          + |∑ z : PatternSpace K H × ZMod P, jointLaw g K H P A B z * F z
            - ∑ x, patternLaw g K H A B x
              * ((∑ y : ZMod P, F (x, y)) / ((P : ℕ) : ℝ))| := by
      linarith [htri]
    linarith [habs, hdec, hXavg]
  -- combine the real and imaginary projections
  have hre : |Complex.reLm E| ≤ _ := key Complex.reLm
    (fun z => Complex.abs_re_le_norm z)
  have him : |Complex.imLm E| ≤ _ := key Complex.imLm
    (fun z => Complex.abs_im_le_norm z)
  have hEnorm : ‖E‖ ≤ |Complex.reLm E| + |Complex.imLm E| := by
    have h := Complex.norm_le_abs_re_add_abs_im E
    exact h
  calc ‖E‖ ≤ |Complex.reLm E| + |Complex.imLm E| := hEnorm
    _ ≤ 2 * (t + 2 * M * ((τ + θ₀) / (τ' + θ₀)
          + (τ' + θ₀ + Real.log 2) / D))
        + 2 * (8 * h * (Fintype.card ι : ℝ) + 4 * θ * J
          + (J : ℝ) * κ * 2 * ((Ξ.card : ℝ) * (ρ4K + ρ))) := by
        linarith [hre, him]

end AssemblyHelpers

section ScheduleSupport

/-- `log x ≤ 2·√x` — the crude bound that lets polynomial data dominate its
own logarithm in the schedule arithmetic. -/
theorem log_le_two_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hlog := Real.log_le_sub_one_of_pos hs0
  have hsq : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx0.le
  rw [hsq] at hlog
  nlinarith [hs0]

/-- **The grid ratio bound**: along the polynomial grid the scale logarithm is
dominated by a fixed multiple of the budget denominator `(j+2)·log(j+2)` —
the design property that kills the recursive-log growth. -/
theorem log_polyGrid_le {κ H₀ : ℕ} (hκ : 1 ≤ κ) (hH : 1 ≤ H₀) (j : ℕ) :
    Real.log ((polyGrid κ H₀ j : ℕ) : ℝ)
      ≤ (Real.log H₀ / (2 * Real.log 2) + Real.log κ / Real.log 2 + 2)
        * (((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hH0 : (0 : ℝ) ≤ Real.log H₀ :=
    Real.log_nonneg (by exact_mod_cast hH)
  have hκ0 : (0 : ℝ) ≤ Real.log κ :=
    Real.log_nonneg (by exact_mod_cast hκ)
  have hj2 : (2 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2 ≤ j + 2)
  have hlogj2 : Real.log 2 ≤ Real.log ((j + 2 : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) hj2
  have hlogj0 : (0 : ℝ) < Real.log ((j + 2 : ℕ) : ℝ) :=
    lt_of_lt_of_le hlog2 hlogj2
  -- the closed-form log and the per-step bound
  rw [log_polyGrid_eq hκ hH j]
  have hstep : ∀ m ∈ Finset.range j,
      Real.log ((κ * (m + 2) ^ 2 : ℕ) : ℝ)
        ≤ Real.log κ + 2 * Real.log ((j + 2 : ℕ) : ℝ) := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hκR : (0 : ℝ) < (κ : ℝ) := by exact_mod_cast (by omega : 0 < κ)
    have hm2 : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < m + 2)
    have hcast : ((κ * (m + 2) ^ 2 : ℕ) : ℝ)
        = (κ : ℝ) * ((m + 2 : ℕ) : ℝ) ^ 2 := by push_cast; ring
    rw [hcast, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have hmono : Real.log ((m + 2 : ℕ) : ℝ) ≤ Real.log ((j + 2 : ℕ) : ℝ) :=
      Real.log_le_log hm2 (by exact_mod_cast (by omega : m + 2 ≤ j + 2))
    push_cast
    push_cast at hmono
    linarith
  have hsum : ∑ m ∈ Finset.range j, Real.log ((κ * (m + 2) ^ 2 : ℕ) : ℝ)
      ≤ (j : ℝ) * (Real.log κ + 2 * Real.log ((j + 2 : ℕ) : ℝ)) := by
    refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hjle : (j : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : j ≤ j + 2)
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  -- assemble: each block of the target dominates one summand
  have h1 : Real.log H₀
      ≤ Real.log H₀ / (2 * Real.log 2)
        * (((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have hprod : 2 * Real.log 2
        ≤ ((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ) := by
      nlinarith [hlogj2, hj2, hlog2]
    nlinarith [hprod, hH0]
  have h2 : (j : ℝ) * Real.log κ
      ≤ Real.log κ / Real.log 2
        * (((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    have hprod : (j : ℝ) * Real.log 2
        ≤ ((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ) := by
      nlinarith [hlogj2, hjle, hlog2, hlogj0, hj0]
    nlinarith [hprod, hκ0]
  have h3 : (j : ℝ) * (2 * Real.log ((j + 2 : ℕ) : ℝ))
      ≤ 2 * (((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ)) := by
    nlinarith [hjle, hlogj0, hj0]
  nlinarith [hsum, h1, h2, h3]

/-- **The grid-ratio fixed point**: a natural `κ` beating any linear demand on
its own log — the choice that closes the conditioning-slack versus
decoupling-threshold cycle. -/
theorem exists_grid_kappa (km a : ℝ) (hkm : 0 ≤ km) :
    ∃ κ : ℕ, 1 ≤ κ ∧ km * (a + Real.log κ / Real.log 2) ≤ κ := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set κ : ℕ := ⌈2 * km * a⌉₊ + ⌈(4 * km / Real.log 2) ^ 2⌉₊ + 1 with hκdef
  refine ⟨κ, by omega, ?_⟩
  have hκ1 : (1 : ℝ) ≤ (κ : ℝ) := by exact_mod_cast (by omega : 1 ≤ κ)
  have hκA : 2 * km * a ≤ (κ : ℝ) := by
    have h1 : 2 * km * a ≤ (⌈2 * km * a⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈2 * km * a⌉₊ : ℝ) ≤ (κ : ℝ) := by
      exact_mod_cast (by omega : ⌈2 * km * a⌉₊ ≤ κ)
    linarith
  have hκB : (4 * km / Real.log 2) ^ 2 ≤ (κ : ℝ) := by
    have h1 : (4 * km / Real.log 2) ^ 2 ≤ (⌈(4 * km / Real.log 2) ^ 2⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h2 : (⌈(4 * km / Real.log 2) ^ 2⌉₊ : ℝ) ≤ (κ : ℝ) := by
      exact_mod_cast (by omega : ⌈(4 * km / Real.log 2) ^ 2⌉₊ ≤ κ)
    linarith
  have hsqrt : Real.log (κ : ℝ) ≤ 2 * Real.sqrt (κ : ℝ) := log_le_two_sqrt hκ1
  have hs0 : (0 : ℝ) ≤ Real.sqrt (κ : ℝ) := Real.sqrt_nonneg _
  have hsB : 4 * km / Real.log 2 ≤ Real.sqrt (κ : ℝ) := by
    have := Real.sqrt_le_sqrt hκB
    rwa [Real.sqrt_sq (by positivity)] at this
  have hsq : Real.sqrt (κ : ℝ) * Real.sqrt (κ : ℝ) = (κ : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  -- `km·a ≤ κ/2` and `km·log κ/log 2 ≤ κ/2`
  have hhalf1 : km * a ≤ (κ : ℝ) / 2 := by linarith
  have hhalf2 : km * (Real.log (κ : ℝ) / Real.log 2) ≤ (κ : ℝ) / 2 := by
    have hchain : km * (Real.log (κ : ℝ) / Real.log 2)
        ≤ km * (2 * Real.sqrt (κ : ℝ) / Real.log 2) := by
      have h2 : Real.log (κ : ℝ) / Real.log 2
          ≤ 2 * Real.sqrt (κ : ℝ) / Real.log 2 := by
        gcongr
      exact mul_le_mul_of_nonneg_left h2 hkm
    have hfin : km * (2 * Real.sqrt (κ : ℝ) / Real.log 2)
        ≤ (κ : ℝ) / 2 := by
      have h4 : 2 * km / Real.log 2 * Real.sqrt (κ : ℝ)
          = km * (2 * Real.sqrt (κ : ℝ) / Real.log 2) := by
        field_simp
      rw [← h4]
      have h5 : 2 * km / Real.log 2 ≤ Real.sqrt (κ : ℝ) / 2 := by
        have h45 : 4 * km / Real.log 2 = 2 * (2 * km / Real.log 2) := by
          ring
        rw [h45] at hsB
        linarith
      calc 2 * km / Real.log 2 * Real.sqrt (κ : ℝ)
          ≤ Real.sqrt (κ : ℝ) / 2 * Real.sqrt (κ : ℝ) :=
            mul_le_mul_of_nonneg_right h5 hs0
        _ = (κ : ℝ) / 2 := by
            rw [div_mul_eq_mul_div, hsq]
    linarith
  calc km * (a + Real.log (κ : ℝ) / Real.log 2)
      = km * a + km * (Real.log (κ : ℝ) / Real.log 2) := by ring
    _ ≤ (κ : ℝ) / 2 + (κ : ℝ) / 2 := add_le_add hhalf1 hhalf2
    _ = (κ : ℝ) := by ring

/-- **Scale selection on the polynomial grid, `g`-last form**: the grid length
`J` depends only on the density target and the alphabet — the quantifier order
the `elliott-red` contradiction needs (`J` fixed before the function and the
window are revealed). Proof as in `exists_polyGrid_scale`. -/
theorem exists_polyGrid_scale' (K κ H₀ : ℕ) (Pseq : ℕ → ℕ)
    [∀ j, NeZero (Pseq j)] (hκ : 1 ≤ κ) (hH₀ : 1 ≤ H₀)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ (g : ℕ → ℂ) {A B : ℕ}, 1 ≤ A →
      (∀ j < J, A + κ * (j + 2) ^ 2 * polyGrid κ H₀ j
          + κ * (j + 2) ^ 2 * polyGrid κ H₀ j < B) →
      (∀ j < J,
        shannonEntropy (residueLaw (Pseq j) A B)
            / ((κ * (j + 2) ^ 2 * polyGrid κ H₀ j : ℕ) : ℝ)
          + decrementErr K (polyGrid κ H₀ j) (Pseq j) A B (κ * (j + 2) ^ 2)
            / ((polyGrid κ H₀ j : ℕ) : ℝ)
        ≤ δ / (2 * (((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ)))) →
      ∃ j < J, mutualInfo (jointLaw g K (polyGrid κ H₀ j) (Pseq j) A B)
          / ((polyGrid κ H₀ j : ℕ) : ℝ)
        < δ / (((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ)) := by
  obtain ⟨J, hJgt⟩ := exists_sum_range_one_div_gt
    ((2 / δ) * Real.log ((((K + 1) * (K + 1) : ℕ)) : ℝ))
  have hJ1 : 1 ≤ J := by
    by_contra hJ0
    have hJz : J = 0 := by omega
    rw [hJz, Finset.range_zero, Finset.sum_empty] at hJgt
    have hlogK : 0 ≤ Real.log ((((K + 1) * (K + 1) : ℕ)) : ℝ) :=
      Real.log_nonneg (by
        have h1 : 1 ≤ (K + 1) * (K + 1) := Nat.mul_pos (by omega) (by omega)
        exact_mod_cast h1)
    have h2δ : 0 ≤ 2 / δ := by positivity
    nlinarith
  refine ⟨J, hJ1, ?_⟩
  intro g A B hA hkB hslack
  have hbudget : Real.log ((((K + 1) * (K + 1) : ℕ)) : ℝ)
      < ∑ j ∈ Finset.range J,
        (δ / (((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ))
          - shannonEntropy (residueLaw (Pseq j) A B)
              / ((κ * (j + 2) ^ 2 * polyGrid κ H₀ j : ℕ) : ℝ)
          - decrementErr K (polyGrid κ H₀ j) (Pseq j) A B (κ * (j + 2) ^ 2)
            / ((polyGrid κ H₀ j : ℕ) : ℝ)) := by
    have hhalf : ∀ j ∈ Finset.range J,
        δ / (2 * (((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ)))
        ≤ δ / (((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ))
          - shannonEntropy (residueLaw (Pseq j) A B)
              / ((κ * (j + 2) ^ 2 * polyGrid κ H₀ j : ℕ) : ℝ)
          - decrementErr K (polyGrid κ H₀ j) (Pseq j) A B (κ * (j + 2) ^ 2)
            / ((polyGrid κ H₀ j : ℕ) : ℝ) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hs := hslack j hj
      have hpos : (0 : ℝ) < ((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ) := by
        have h2 : (2 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : 2 ≤ j + 2)
        have hlog : 0 < Real.log ((j + 2 : ℕ) : ℝ) :=
          Real.log_pos (by linarith)
        positivity
      have hsplit : δ / (((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ))
          = δ / (2 * (((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ)))
            + δ / (2 * (((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ))) := by
        field_simp
        norm_num
      linarith [hsplit, hs]
    have hlow : (2 / δ) * Real.log ((((K + 1) * (K + 1) : ℕ)) : ℝ) * (δ / 2)
        < (∑ j ∈ Finset.range J,
            1 / (((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ))) * (δ / 2) :=
      mul_lt_mul_of_pos_right hJgt (by positivity)
    have hcancel : (2 / δ) * Real.log ((((K + 1) * (K + 1) : ℕ)) : ℝ)
        * (δ / 2) = Real.log ((((K + 1) * (K + 1) : ℕ)) : ℝ) := by
      field_simp
    have hsum2 : (∑ j ∈ Finset.range J,
        1 / (((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ))) * (δ / 2)
        = ∑ j ∈ Finset.range J,
          δ / (2 * (((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ))) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      have hpos : (0 : ℝ) < ((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ) := by
        have h2 : (2 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : 2 ≤ j + 2)
        have hlog : 0 < Real.log ((j + 2 : ℕ) : ℝ) :=
          Real.log_pos (by linarith)
        positivity
      field_simp
    rw [hcancel, hsum2] at hlow
    calc Real.log ((((K + 1) * (K + 1) : ℕ)) : ℝ)
        < ∑ j ∈ Finset.range J,
            δ / (2 * (((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ))) := hlow
      _ ≤ ∑ j ∈ Finset.range J,
          (δ / (((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ))
            - shannonEntropy (residueLaw (Pseq j) A B)
                / ((κ * (j + 2) ^ 2 * polyGrid κ H₀ j : ℕ) : ℝ)
            - decrementErr K (polyGrid κ H₀ j) (Pseq j) A B
                (κ * (j + 2) ^ 2)
              / ((polyGrid κ H₀ j : ℕ) : ℝ)) :=
          Finset.sum_le_sum hhalf
  exact exists_scale_mutualInfo_lt g K (polyGrid κ H₀)
    Pseq (fun j => κ * (j + 2) ^ 2) hA (polyGrid_pos hκ hH₀)
    (fun j => Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by positivity)))
    (fun j _ => polyGrid_succ κ H₀ j) hkB hJ1 _ hbudget

end ScheduleSupport

namespace Tao2015

section BlockDictionary

/-- Membership facts for the dyadic prime block. -/
theorem mem_primeBlock {n₀ p : ℕ} (hp : p ∈ primeBlock n₀) :
    p.Prime ∧ n₀ < p ∧ p ≤ 2 * n₀ := by
  rw [primeBlock, Finset.mem_filter] at hp
  have hpp := Nat.prime_of_mem_primesBelow hp.1
  have hlt := Nat.lt_of_mem_primesBelow hp.1
  exact ⟨hpp, hp.2, by omega⟩

/-- Bertrand: the block is inhabited. -/
theorem primeBlock_nonempty {n₀ : ℕ} (hn₀ : 1 ≤ n₀) :
    (primeBlock n₀).Nonempty := by
  obtain ⟨p, hp, hlt, hle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul n₀ (by omega)
  refine ⟨p, ?_⟩
  rw [primeBlock, Finset.mem_filter, Nat.mem_primesBelow]
  exact ⟨⟨by omega, hp⟩, hlt⟩

/-- Sums over the block subtype are sums over the block. -/
theorem sum_primeBlock_coe {n₀ : ℕ} {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) :
    ∑ i : ↥(primeBlock n₀), f (i : ℕ) = ∑ p ∈ primeBlock n₀, f p := by
  rw [Finset.sum_coe_sort_eq_attach]
  exact Finset.sum_attach _ _

/-- Products over the block subtype are products over the block. -/
theorem prod_primeBlock_coe {n₀ : ℕ} (f : ℕ → ℕ) :
    ∏ i : ↥(primeBlock n₀), f (i : ℕ) = ∏ p ∈ primeBlock n₀, f p := by
  rw [Finset.prod_coe_sort_eq_attach]
  exact Finset.prod_attach _ _

/-- The block product is a genuine modulus. -/
theorem two_le_prod_primeBlock {n₀ : ℕ} (hn₀ : 1 ≤ n₀) :
    2 ≤ ∏ p ∈ primeBlock n₀, p := by
  obtain ⟨p, hp⟩ := primeBlock_nonempty hn₀
  have h2 := (mem_primeBlock hp).1.two_le
  have hpos : 0 < ∏ q ∈ primeBlock n₀, q :=
    Finset.prod_pos fun q hq => (mem_primeBlock hq).1.pos
  have hle := Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem _ hp)
  omega

/-- The block product is at most `4^(2n₀)` (Erdős's primorial bound). -/
theorem prod_primeBlock_le_pow (n₀ : ℕ) :
    ∏ p ∈ primeBlock n₀, p ≤ 4 ^ (2 * n₀) := by
  rw [primeBlock]
  exact le_trans (Nat.le_of_dvd (primorial_pos _)
    (prod_block_dvd_primorial n₀)) (primorial_le_4_pow _)

/-- The conditioning budget through the block dictionary. -/
theorem log_prod_primeBlock_le (n₀ : ℕ) :
    Real.log ((∏ p ∈ primeBlock n₀, p : ℕ) : ℝ)
      ≤ 2 * (n₀ : ℝ) * Real.log 4 := by
  rw [primeBlock]
  exact log_prod_block_le n₀

/-- The block cardinality bound through the block dictionary. -/
theorem card_primeBlock_le {n₀ : ℕ} (hn₀ : 2 ≤ n₀) :
    ((primeBlock n₀).card : ℝ) ≤ 2 * n₀ * Real.log 4 / Real.log n₀ := by
  rw [primeBlock]
  exact card_block_le hn₀

/-- The block reciprocal mass upper bound: `∑ 1/p ≤ 2·log 4/log n₀`. -/
theorem sum_one_div_primeBlock_le {n₀ : ℕ} (hn₀ : 2 ≤ n₀) :
    ∑ p ∈ primeBlock n₀, (1 : ℝ) / p
      ≤ 2 * Real.log 4 / Real.log n₀ := by
  have hn₀R : (0 : ℝ) < (n₀ : ℝ) := by exact_mod_cast (by omega : 0 < n₀)
  have hlog : (0 : ℝ) < Real.log n₀ :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n₀))
  have hper : ∀ p ∈ primeBlock n₀, (1 : ℝ) / p ≤ 1 / n₀ := by
    intro p hp
    have h := (mem_primeBlock hp).2.1
    have hpR : (n₀ : ℝ) ≤ (p : ℝ) := by exact_mod_cast h.le
    exact one_div_le_one_div_of_le hn₀R hpR
  calc ∑ p ∈ primeBlock n₀, (1 : ℝ) / p
      ≤ ∑ _p ∈ primeBlock n₀, (1 : ℝ) / n₀ := Finset.sum_le_sum hper
    _ = ((primeBlock n₀).card : ℝ) * (1 / n₀) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * n₀ * Real.log 4 / Real.log n₀) * (1 / n₀) :=
        mul_le_mul_of_nonneg_right (card_primeBlock_le hn₀) (by positivity)
    _ = 2 * Real.log 4 / Real.log n₀ := by
        field_simp

open scoped Function in
/-- Distinct block primes are coprime. -/
theorem pairwise_coprime_primeBlock (n₀ : ℕ) :
    Pairwise (Nat.Coprime on (fun i : ↥(primeBlock n₀) => (i : ℕ))) := by
  intro i j hij
  have hi := (mem_primeBlock i.2).1
  have hj := (mem_primeBlock j.2).1
  exact (Nat.coprime_primes hi hj).mpr
    (fun hc => hij (Subtype.ext hc))

end BlockDictionary

section WindowHandling

/-- Each conjugate-pair summand has norm exactly `1/n`; the pair sum over any
window is bounded by the harmonic mass. -/
theorem norm_pair_le_sum_one_div {g : ℕ → ℂ} (huni : Unimodular g)
    (b₁ b₂ : ℕ) (s : Finset ℕ) :
    ‖∑ n ∈ s, g (n + b₁) * (starRingEnd ℂ) (g (n + b₂)) / (n : ℂ)‖
      ≤ ∑ n ∈ s, (1 : ℝ) / n := by
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_div, norm_mul, RCLike.norm_conj, huni (n + b₁), huni (n + b₂),
    one_mul, Complex.norm_natCast]

/-- **The window trim**: passing to the `max`-trimmed window costs at most
`log NS` of correlation mass. -/
theorem norm_pair_trim {g : ℕ → ℂ} (huni : Unimodular g)
    (b₁ b₂ NS A' B' : ℕ) (hNS1 : 1 ≤ NS) (hA'1 : 1 ≤ A') :
    ‖∑ n ∈ Finset.Ioc A' B',
        g (n + b₁) * (starRingEnd ℂ) (g (n + b₂)) / (n : ℂ)‖
      ≤ ‖∑ n ∈ Finset.Ioc (max A' NS) B',
          g (n + b₁) * (starRingEnd ℂ) (g (n + b₂)) / (n : ℂ)‖
        + Real.log NS := by
  have hlogNS : (0 : ℝ) ≤ Real.log NS :=
    Real.log_nonneg (by exact_mod_cast hNS1)
  by_cases hcase : NS ≤ A'
  · rw [max_eq_left hcase]
    linarith [norm_nonneg (∑ n ∈ Finset.Ioc A' B',
      g (n + b₁) * (starRingEnd ℂ) (g (n + b₂)) / (n : ℂ))]
  · push_neg at hcase
    rw [max_eq_right (le_of_lt hcase)]
    by_cases hBN : B' ≤ NS
    · -- the whole window sits inside the trim: its mass is at most `log NS`
      have hmass : ‖∑ n ∈ Finset.Ioc A' B',
          g (n + b₁) * (starRingEnd ℂ) (g (n + b₂)) / (n : ℂ)‖
          ≤ Real.log NS := by
        refine le_trans (norm_pair_le_sum_one_div huni b₁ b₂ _) ?_
        by_cases hAB : A' ≤ B'
        · refine le_trans (sum_one_div_Ioc_le hA'1 hAB) ?_
          have h1 : Real.log A' ≥ 0 :=
            Real.log_nonneg (by exact_mod_cast hA'1)
          have h2 : Real.log B' ≤ Real.log NS :=
            Real.log_le_log (by exact_mod_cast (by omega : 0 < B') :
              (0 : ℝ) < (B' : ℝ)) (by exact_mod_cast hBN)
          linarith
        · push_neg at hAB
          rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
          exact hlogNS
      linarith [norm_nonneg (∑ n ∈ Finset.Ioc NS B',
        g (n + b₁) * (starRingEnd ℂ) (g (n + b₂)) / (n : ℂ))]
    · push_neg at hBN
      -- split the window at `NS`
      have hsplit := Finset.sum_Ioc_consecutive
        (f := fun n => g (n + b₁) * (starRingEnd ℂ) (g (n + b₂)) / (n : ℂ))
        (le_of_lt hcase) (le_of_lt hBN)
      have htri : ‖∑ n ∈ Finset.Ioc A' B',
          g (n + b₁) * (starRingEnd ℂ) (g (n + b₂)) / (n : ℂ)‖
          ≤ ‖∑ n ∈ Finset.Ioc A' NS,
              g (n + b₁) * (starRingEnd ℂ) (g (n + b₂)) / (n : ℂ)‖
            + ‖∑ n ∈ Finset.Ioc NS B',
              g (n + b₁) * (starRingEnd ℂ) (g (n + b₂)) / (n : ℂ)‖ := by
        rw [← hsplit]
        exact norm_add_le _ _
      have hpre : ‖∑ n ∈ Finset.Ioc A' NS,
          g (n + b₁) * (starRingEnd ℂ) (g (n + b₂)) / (n : ℂ)‖
          ≤ Real.log NS := by
        refine le_trans (norm_pair_le_sum_one_div huni b₁ b₂ _) ?_
        refine le_trans (sum_one_div_Ioc_le hA'1 (le_of_lt hcase)) ?_
        have h1 : Real.log A' ≥ 0 :=
          Real.log_nonneg (by exact_mod_cast hA'1)
        linarith
      linarith

/-- **Harmonic lower bound**, telescoping form: the window mass dominates the
log-length measured one step out. -/
theorem log_le_sum_one_div_Ioc {c d : ℕ} (hcd : c ≤ d) :
    Real.log ((d + 1 : ℕ) : ℝ) - Real.log ((c + 1 : ℕ) : ℝ)
      ≤ ∑ n ∈ Finset.Ioc c d, (1 : ℝ) / n := by
  have hreidx : ∑ n ∈ Finset.Ioc c d, (1 : ℝ) / n
      = ∑ i ∈ Finset.range (d - c), (1 : ℝ) / ((c + 1 + i : ℕ) : ℝ) := by
    refine Finset.sum_bij' (fun n _ => n - (c + 1)) (fun i _ => c + 1 + i)
      ?_ ?_ ?_ ?_ ?_
    · intro n hn
      rw [Finset.mem_Ioc] at hn
      show n - (c + 1) ∈ Finset.range (d - c)
      rw [Finset.mem_range]
      omega
    · intro i hi
      rw [Finset.mem_range] at hi
      show c + 1 + i ∈ Finset.Ioc c d
      rw [Finset.mem_Ioc]
      omega
    · intro n hn
      rw [Finset.mem_Ioc] at hn
      show c + 1 + (n - (c + 1)) = n
      omega
    · intro i _
      show c + 1 + i - (c + 1) = i
      omega
    · intro n hn
      rw [Finset.mem_Ioc] at hn
      show (1 : ℝ) / n = 1 / ((c + 1 + (n - (c + 1)) : ℕ) : ℝ)
      congr 2
      omega
  have htel := Finset.sum_range_sub
    (f := fun i => Real.log ((c + 1 + i : ℕ) : ℝ)) (d - c)
  have hends : Real.log ((c + 1 + (d - c) : ℕ) : ℝ)
      = Real.log ((d + 1 : ℕ) : ℝ) := by
    congr 2
    omega
  have hper : ∀ i ∈ Finset.range (d - c),
      Real.log ((c + 1 + (i + 1) : ℕ) : ℝ) - Real.log ((c + 1 + i : ℕ) : ℝ)
        ≤ (1 : ℝ) / ((c + 1 + i : ℕ) : ℝ) := by
    intro i _
    have hn0 : (0 : ℝ) < ((c + 1 + i : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < c + 1 + i)
    have hsucc : ((c + 1 + (i + 1) : ℕ) : ℝ) = ((c + 1 + i : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    rw [hsucc, ← Real.log_div (by linarith) (ne_of_gt hn0)]
    have hpos : (0 : ℝ) < (((c + 1 + i : ℕ) : ℝ) + 1) / ((c + 1 + i : ℕ) : ℝ) := by
      positivity
    have h := Real.log_le_sub_one_of_pos hpos
    have hval : (((c + 1 + i : ℕ) : ℝ) + 1) / ((c + 1 + i : ℕ) : ℝ) - 1
        = 1 / ((c + 1 + i : ℕ) : ℝ) := by
      field_simp
      ring
    linarith [h, hval.le, hval.ge]
  rw [hreidx]
  calc Real.log ((d + 1 : ℕ) : ℝ) - Real.log ((c + 1 : ℕ) : ℝ)
      = ∑ i ∈ Finset.range (d - c),
          (Real.log ((c + 1 + (i + 1) : ℕ) : ℝ)
            - Real.log ((c + 1 + i : ℕ) : ℝ)) := by
        rw [htel, hends]
    _ ≤ ∑ i ∈ Finset.range (d - c), (1 : ℝ) / ((c + 1 + i : ℕ) : ℝ) :=
        Finset.sum_le_sum hper

/-- **Harmonic mass of the trimmed Elliott window, lower bound**:
`log w − log(NS + 2)`. -/
theorem harmonic_trim_ge (NS : ℕ) (hNS : 1 ≤ NS) {x w : ℝ}
    (hw1 : 1 ≤ w) (hwx : w ≤ x) :
    Real.log w - Real.log ((NS + 2 : ℕ) : ℝ)
      ≤ ∑ n ∈ Finset.Ioc (max ⌊x / w⌋₊ NS) ⌊x⌋₊, (1 : ℝ) / n := by
  have hx1 : (1 : ℝ) ≤ x := le_trans hw1 hwx
  have hw0 : (0 : ℝ) < w := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  set c : ℕ := max ⌊x / w⌋₊ NS with hc_def
  by_cases hcd : c ≤ ⌊x⌋₊
  · refine le_trans ?_ (log_le_sum_one_div_Ioc hcd)
    have hd1 : x ≤ ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.lt_floor_add_one x]
    have hlogd : Real.log x ≤ Real.log ((⌊x⌋₊ + 1 : ℕ) : ℝ) :=
      Real.log_le_log hx0 hd1
    have hcle : ((c + 1 : ℕ) : ℝ) ≤ (x / w) * ((NS + 2 : ℕ) : ℝ) := by
      have h1 : (⌊x / w⌋₊ : ℝ) ≤ x / w := Nat.floor_le (by positivity)
      have h2 : (c : ℝ) ≤ x / w + NS := by
        have hmax : c = max ⌊x / w⌋₊ NS := hc_def
        have hle1 : (⌊x / w⌋₊ : ℝ) ≤ x / w + NS := by
          have hNS0 : (0 : ℝ) ≤ (NS : ℝ) := Nat.cast_nonneg NS
          linarith
        have hle2 : (NS : ℝ) ≤ x / w + NS := by
          have hxw1 : (1 : ℝ) ≤ x / w := (one_le_div hw0).mpr hwx
          linarith
        rcases max_cases ⌊x / w⌋₊ NS with ⟨heq, _⟩ | ⟨heq, _⟩ <;>
          rw [hmax, heq]
        · exact_mod_cast hle1
        · exact_mod_cast hle2
      have hxw1 : (1 : ℝ) ≤ x / w := (one_le_div hw0).mpr hwx
      push_cast
      push_cast at h2
      nlinarith [hxw1]
    have hlogc : Real.log ((c + 1 : ℕ) : ℝ)
        ≤ Real.log x - Real.log w + Real.log ((NS + 2 : ℕ) : ℝ) := by
      have hc0 : (0 : ℝ) < ((c + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < c + 1)
      have := Real.log_le_log hc0 hcle
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_div (ne_of_gt hx0) (ne_of_gt hw0)] at this
      linarith
    linarith [hlogd, hlogc]
  · -- the degenerate case `NS > ⌊x⌋₊`: the window is empty, but then
    -- `w ≤ x < NS + 1`, so the claimed lower bound is nonpositive.
    push_neg at hcd
    rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    have hflmono : ⌊x / w⌋₊ ≤ ⌊x⌋₊ :=
      Nat.floor_le_floor (div_le_self hx0.le hw1)
    have hchoice := max_choice ⌊x / w⌋₊ NS
    have hcNS : c = NS := by
      rw [hc_def]
      rcases hchoice with heq | heq
      · rw [hc_def] at hcd
        omega
      · exact heq
    have hxNS : x < ((NS + 2 : ℕ) : ℝ) := by
      have h1 := Nat.lt_floor_add_one x
      have h2 : (⌊x⌋₊ : ℝ) + 1 ≤ ((NS + 2 : ℕ) : ℝ) := by
        have : ⌊x⌋₊ + 1 ≤ NS + 2 := by omega
        exact_mod_cast this
      linarith
    have hlogw : Real.log w ≤ Real.log ((NS + 2 : ℕ) : ℝ) :=
      Real.log_le_log hw0 (by linarith)
    linarith

/-- **Harmonic mass of the trimmed Elliott window, upper bound**:
`log w + log(NS + 1)`. -/
theorem harmonic_trim_le (NS : ℕ) (hNS : 1 ≤ NS) {x w : ℝ}
    (hw1 : 1 ≤ w) (hwx : w ≤ x) :
    ∑ n ∈ Finset.Ioc (max ⌊x / w⌋₊ NS) ⌊x⌋₊, (1 : ℝ) / n
      ≤ Real.log w + Real.log ((NS + 1 : ℕ) : ℝ) := by
  have hw0 : (0 : ℝ) < w := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogw : (0 : ℝ) ≤ Real.log w := Real.log_nonneg hw1
  have hlogNS : (0 : ℝ) ≤ Real.log ((NS + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ NS + 1))
  set c : ℕ := max ⌊x / w⌋₊ NS with hc_def
  have hc1 : 1 ≤ c := le_trans hNS (le_max_right _ _)
  by_cases hcd : c ≤ ⌊x⌋₊
  · refine le_trans (sum_one_div_Ioc_le hc1 hcd) ?_
    have hlogd : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊x⌋₊))
        (Nat.floor_le hx0.le)
    rcases max_choice ⌊x / w⌋₊ NS with heq | heq
    · -- `c = ⌊x/w⌋₊ ≥ NS ≥ 1`: `c + 1 ≤ 2c` and `c + 1 > x/w`
      have hcval : c = ⌊x / w⌋₊ := heq
      have hfl : x / w < (c : ℝ) + 1 := by
        rw [hcval]
        exact Nat.lt_floor_add_one _
      have hc2 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
      have hxc : x / w ≤ 2 * (c : ℝ) := by linarith
      have hlogc : Real.log x - Real.log w - Real.log 2
          ≤ Real.log (c : ℝ) := by
        have h1 : (0 : ℝ) < x / w := by positivity
        have h2 := Real.log_le_log h1 hxc
        rw [Real.log_div (ne_of_gt hx0) (ne_of_gt hw0),
          Real.log_mul (by norm_num)
            (ne_of_gt (show (0 : ℝ) < (c : ℝ) by linarith))] at h2
        linarith
      have hlog2NS : Real.log 2 ≤ Real.log ((NS + 1 : ℕ) : ℝ) := by
        refine Real.log_le_log (by norm_num) ?_
        exact_mod_cast (by omega : 2 ≤ NS + 1)
      linarith
    · -- `c = NS ≥ ⌊x/w⌋₊`: then `x/w < NS + 1`, so `log x < log w + log(NS+1)`
      have hcval : c = NS := heq
      have hfl : x / w < ((NS + 1 : ℕ) : ℝ) := by
        have h1 : ⌊x / w⌋₊ ≤ NS := by
          rw [hc_def] at hcval
          omega
        have h2 := Nat.lt_floor_add_one (x / w)
        have h3 : (⌊x / w⌋₊ : ℝ) + 1 ≤ ((NS + 1 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : ⌊x / w⌋₊ + 1 ≤ NS + 1)
        linarith
      have hxlt : x < w * ((NS + 1 : ℕ) : ℝ) := by
        have := (div_lt_iff₀ hw0).mp hfl
        linarith [this]
      have hlogx : Real.log x
          ≤ Real.log w + Real.log ((NS + 1 : ℕ) : ℝ) := by
        have h1 := Real.log_le_log hx0 hxlt.le
        rw [Real.log_mul (ne_of_gt hw0) (by positivity)] at h1
        linarith
      have hlogc : (0 : ℝ) ≤ Real.log (c : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hc1)
      linarith
  · push_neg at hcd
    rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    positivity

/-- **Window capacity**: once the window bottom is large, the trimmed left
endpoint fits any fixed multiplicative demand below the right endpoint. -/
theorem window_capacity {NS Cbig : ℕ} (hNS1 : 1 ≤ NS) (hC1 : 1 ≤ Cbig)
    {x w : ℝ}
    (hw : (((Cbig + 1) * (NS + 2) + 4 * Cbig : ℕ) : ℝ) ≤ w) (hwx : w ≤ x) :
    Cbig * (max ⌊x / w⌋₊ NS + 1) ≤ ⌊x⌋₊ := by
  have hwR : ((4 * Cbig : ℕ) : ℝ) ≤ w := by
    refine le_trans ?_ hw
    exact_mod_cast (by omega : 4 * Cbig ≤ (Cbig + 1) * (NS + 2) + 4 * Cbig)
  have hw0 : (0 : ℝ) < w := by
    have : (0 : ℝ) < ((4 * Cbig : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < 4 * Cbig)
    linarith
  have hx0 : (0 : ℝ) < x := by linarith
  refine Nat.le_floor ?_
  rcases max_choice ⌊x / w⌋₊ NS with heq | heq <;> rw [heq]
  · -- left endpoint `⌊x/w⌋₊`: use `⌊x/w⌋₊ + 1 ≤ 2·(x/w)` when it is ≥ 1
    have hfl : (⌊x / w⌋₊ : ℝ) ≤ x / w := Nat.floor_le (by positivity)
    have hb : (1 : ℝ) ≤ x / w := (one_le_div hw0).mpr hwx
    have hfl1 : (1 : ℝ) ≤ (⌊x / w⌋₊ : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) ⌊x / w⌋₊
      linarith
    have hkey : ((Cbig * (⌊x / w⌋₊ + 1) : ℕ) : ℝ)
        ≤ (Cbig : ℝ) * (2 * (x / w)) := by
      push_cast
      nlinarith [hfl, hb]
    have hfin : (Cbig : ℝ) * (2 * (x / w)) ≤ x := by
      have h2C : 2 * (Cbig : ℝ) ≤ w / 2 := by
        have h4 : ((4 * Cbig : ℕ) : ℝ) = 4 * (Cbig : ℝ) := by push_cast; ring
        rw [h4] at hwR
        linarith
      have hxw0 : (0 : ℝ) ≤ x / w := by positivity
      have hxw : x / w * (2 * (Cbig : ℝ)) ≤ x / w * (w / 2) :=
        mul_le_mul_of_nonneg_left h2C hxw0
      have hval : x / w * (w / 2) = x / 2 := by
        field_simp
      nlinarith [hxw, hval, hx0]
    calc ((Cbig * (⌊x / w⌋₊ + 1) : ℕ) : ℝ)
        ≤ (Cbig : ℝ) * (2 * (x / w)) := hkey
      _ ≤ x := hfin
  · -- left endpoint `NS`: the fixed demand is below `w ≤ x`
    have hle : ((Cbig * (NS + 1) : ℕ) : ℝ)
        ≤ (((Cbig + 1) * (NS + 2) + 4 * Cbig : ℕ) : ℝ) := by
      exact_mod_cast (by nlinarith :
        Cbig * (NS + 1) ≤ (Cbig + 1) * (NS + 2) + 4 * Cbig)
    linarith [hw, hwx]

end WindowHandling

section FinalArithmetic

/-- **The master budget arithmetic**: the `prop_conv` lower bound (`hPC`), the
bridge upper bound (`hT`), and the M1 expectation bound (`hM1`) are
incompatible under the audited parameter schedule — the contradiction closing
the entropy-decrement argument. All quantities are abstract reals; the
callers' norm expressions and schedule values enter by unification. -/
theorem elliott_master_arith
    {ε lw lNS lNS2 msj Jl n0 Amax NSR S TN EN SB Mv Kd Ξc Ξm εmr τv τ' θ₀ Ds
      ts θsj Cc hR E1 lgn0 Lfj Rg HsR δ₃ δg κb : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hlw1 : 1 ≤ lw)
    (hPC : Jl * msj * (ε * lw - lNS - 1) - 3 * Jl ^ 2 * n0 / Amax
      - Jl * (2 * Real.log (2 * n0) + 2) ≤ TN)
    (hT : TN ≤ S * (EN + SB * (12 / Kd)))
    (hM1 : EN ≤ 2 * (ts + 2 * Mv * ((τv + θ₀) / (τ' + θ₀)
        + (τ' + θ₀ + Real.log 2) / Ds))
      + 2 * (8 * hR * Cc + 4 * θsj * Jl
        + Jl * κb * 2 * (Ξc * (4 / Kd + 2 * εmr))))
    (hS_pos : 0 < S) (hS2lw : S ≤ 2 * lw)
    (hJl0 : 0 < Jl) (hms0 : 0 < msj)
    (hts_eq : ts = Jl * msj * ε / 64)
    (hθs_eq : θsj = ε * msj / 256)
    (hκms : κb ≤ 48 * msj)
    (hMv4 : Mv = 4 * SB) (hMv0 : 0 ≤ Mv) (hMv_ub : Mv ≤ 193 * (Jl * msj))
    (hcard_ub : Cc ≤ 64 * δ₃ * (Jl * msj))
    (hhR1 : 1 ≤ hR) (hδ₃0 : 0 < δ₃) (hδ₃h : δ₃ * hR = ε / 100000)
    (hΞc0 : 0 ≤ Ξc) (hΞcard : Ξc ≤ Ξm) (hΞm1 : 1 ≤ Ξm)
    (hKd0 : 0 < Kd) (hKdR : 10 ^ 6 * (Ξm + 1) / ε ≤ Kd)
    (hεmr_eq : εmr = ε / (10000 * (Ξm + 1)))
    (hτ'_eq : τ' = ε * Ds / 200000) (hτ'0 : 0 < τ')
    (hθ₀0 : 0 ≤ θ₀) (hθ₀τ' : θ₀ ≤ τ' * ε / 200000)
    (hDs0 : 0 < Ds) (hDs_min : 604000 / ε ≤ Ds)
    (hτv_eq : τv = HsR * δg / Lfj)
    (hδg_eq : δg = ε ^ 4 * δ₃ / (10 ^ 21 * Rg))
    (hRg2 : 2 ≤ Rg) (hLf0 : 0 < Lfj) (hHsR0 : 0 < HsR)
    (hlgn0pos : 0 < lgn0) (hlgn0Rg : lgn0 ≤ Rg * Lfj)
    (hDs_lb : ε ^ 2 * δ₃ * HsR / (10 ^ 10 * lgn0) ≤ Ds)
    (hE1_eq : E1 = 3 * Jl ^ 2 * n0 / NSR + Jl * (2 * Real.log (2 * n0) + 2))
    (hNSR0 : 0 < NSR) (hNSAmax : NSR ≤ Amax) (hn00 : 0 ≤ n0)
    (hlNSle : lNS ≤ lNS2)
    (hbud : 4 * (lNS2 + 1 + E1 / (Jl * msj)) / ε ≤ lw) :
    False := by
  have hlw0 : (0:ℝ) < lw := by linarith
  have hQ0 : (0:ℝ) < Jl * msj := mul_pos hJl0 hms0
  have hRg0 : (0:ℝ) < Rg := by linarith
  -- ================= the lower bound: `(3/4)·Q·ε·lw ≤ TN` =================
  have hAmax0 : (0:ℝ) < Amax := lt_of_lt_of_le hNSR0 hNSAmax
  have herrA : 3 * Jl ^ 2 * n0 / Amax ≤ 3 * Jl ^ 2 * n0 / NSR :=
    div_le_div_of_nonneg_left
      (mul_nonneg (by nlinarith only [sq_nonneg Jl] : (0:ℝ) ≤ 3 * Jl ^ 2) hn00)
      hNSR0 hNSAmax
  have hbudA : lNS2 + 1 + E1 / (Jl * msj) ≤ ε * lw / 4 := by
    have h1 := (div_le_iff₀ hε0).mp hbud
    linarith
  have hE1Q : Jl * msj * (E1 / (Jl * msj)) = E1 := by
    field_simp
  have hbudQ : Jl * msj * (lNS2 + 1) + E1 ≤ Jl * msj * (ε * lw) / 4 := by
    have h2 := mul_le_mul_of_nonneg_left hbudA hQ0.le
    have h3 : Jl * msj * (lNS2 + 1 + E1 / (Jl * msj))
        = Jl * msj * (lNS2 + 1) + Jl * msj * (E1 / (Jl * msj)) := by ring
    have h4 : Jl * msj * (ε * lw / 4) = Jl * msj * (ε * lw) / 4 := by ring
    linarith only [h2, h3.le, h3.ge, hE1Q.le, hE1Q.ge, h4.le, h4.ge]
  have hlow : 3 / 4 * (Jl * msj * (ε * lw)) ≤ TN := by
    have h5 : Jl * msj * (lNS + 1) ≤ Jl * msj * (lNS2 + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hQ0.le
    have h6 : Jl * msj * (ε * lw - lNS - 1)
        = Jl * msj * (ε * lw) - Jl * msj * (lNS + 1) := by ring
    linarith only [hPC, herrA, hE1_eq.le, hE1_eq.ge, h5, h6.le, h6.ge, hbudQ]
  -- ================= the alphabet and swap caps =================
  have hεmr0 : (0:ℝ) ≤ εmr := by
    rw [hεmr_eq]
    exact div_nonneg hε0.le (by linarith)
  have hfac0 : (0:ℝ) ≤ 4 / Kd + 2 * εmr := by
    have := div_nonneg (by norm_num : (0:ℝ) ≤ 4) hKd0.le
    linarith
  have hKdinv2e6 : 1 / Kd ≤ ε / (2 * 10 ^ 6) := by
    have h1 : 2 * 10 ^ 6 / ε ≤ Kd := by
      have h2 : 2 * 10 ^ 6 / ε ≤ 10 ^ 6 * (Ξm + 1) / ε := by
        rw [div_le_div_iff₀ hε0 hε0]
        nlinarith only [hΞm1, hε0]
      linarith only [h2, hKdR]
    rw [div_le_div_iff₀ hKd0 (by norm_num : (0:ℝ) < 2 * 10 ^ 6)]
    have h3 := (div_le_iff₀ hε0).mp h1
    linarith only [h3]
  have hswap_ub : Ξc * (4 / Kd + 2 * εmr) ≤ 21 / 100000 * ε := by
    have h4Kd : 4 / Kd ≤ 4 * ε / (10 ^ 6 * (Ξm + 1)) := by
      rw [div_le_div_iff₀ hKd0
        (by nlinarith only [hΞm1] : (0:ℝ) < 10 ^ 6 * (Ξm + 1))]
      have h5 := (div_le_iff₀ hε0).mp hKdR
      nlinarith only [h5, hε0]
    have hΞstep : Ξc * (4 / Kd + 2 * εmr) ≤ Ξm * (4 / Kd + 2 * εmr) :=
      mul_le_mul_of_nonneg_right hΞcard hfac0
    have hA : Ξm * (4 / Kd) ≤ 4 / 10 ^ 6 * ε := by
      have h6 : Ξm * (4 / Kd) ≤ Ξm * (4 * ε / (10 ^ 6 * (Ξm + 1))) :=
        mul_le_mul_of_nonneg_left h4Kd (by linarith)
      have h7 : Ξm * (4 * ε / (10 ^ 6 * (Ξm + 1))) ≤ 4 / 10 ^ 6 * ε := by
        have hb : Ξm * (4 * ε / (10 ^ 6 * (Ξm + 1)))
            = Ξm * (4 * ε) / (10 ^ 6 * (Ξm + 1)) := by ring
        rw [hb, div_le_iff₀
          (by nlinarith only [hΞm1] : (0:ℝ) < 10 ^ 6 * (Ξm + 1))]
        nlinarith only [hε0]
      linarith only [h6, h7]
    have hB : Ξm * (2 * εmr) ≤ 2 / 10000 * ε := by
      rw [hεmr_eq]
      have h8 : Ξm * (2 * (ε / (10000 * (Ξm + 1))))
          = 2 * ε * Ξm / (10000 * (Ξm + 1)) := by ring
      rw [h8, div_le_iff₀
        (by nlinarith only [hΞm1] : (0:ℝ) < 10000 * (Ξm + 1))]
      nlinarith only [hε0]
    have hsplit : Ξm * (4 / Kd + 2 * εmr)
        = Ξm * (4 / Kd) + Ξm * (2 * εmr) := by ring
    nlinarith only [hΞstep, hsplit.le, hsplit.ge, hA, hB, hε0]
  -- ================= the M1 terms in `Q·ε` units =================
  have hts2 : 2 * ts = 2 / 64 * (Jl * msj * ε) := by rw [hts_eq]; ring
  have hθst : 8 * θsj * Jl = 8 / 256 * (Jl * msj * ε) := by rw [hθs_eq]; ring
  have hMRt : Jl * κb * 2 * (Ξc * (4 / Kd + 2 * εmr))
      ≤ 2016 / 100000 * (Jl * msj * ε) := by
    have h9 : Jl * κb * 2 ≤ 48 * (Jl * msj) * 2 := by
      have := mul_le_mul_of_nonneg_left hκms hJl0.le
      linarith
    have hswap0 : (0:ℝ) ≤ Ξc * (4 / Kd + 2 * εmr) := mul_nonneg hΞc0 hfac0
    have h10 : Jl * κb * 2 * (Ξc * (4 / Kd + 2 * εmr))
        ≤ 48 * (Jl * msj) * 2 * (21 / 100000 * ε) :=
      mul_le_mul h9 hswap_ub hswap0 (by nlinarith only [hQ0])
    have h11 : 48 * (Jl * msj) * 2 * (21 / 100000 * ε)
        = 2016 / 100000 * (Jl * msj * ε) := by ring
    linarith only [h10, h11.le, h11.ge]
  have hstrip : 8 * hR * Cc ≤ 512 / 100000 * (Jl * msj * ε) := by
    have h12 : 8 * hR * Cc ≤ 8 * hR * (64 * δ₃ * (Jl * msj)) :=
      mul_le_mul_of_nonneg_left hcard_ub (by nlinarith only [hhR1])
    have h13 : 8 * hR * (64 * δ₃ * (Jl * msj))
        = 512 * (δ₃ * hR) * (Jl * msj) := by ring
    rw [hδ₃h] at h13
    have h14 : 512 * (ε / 100000) * (Jl * msj)
        = 512 / 100000 * (Jl * msj * ε) := by ring
    linarith only [h12, h13.le, h13.ge, h14.le, h14.ge]
  -- ================= the decoupling ratios =================
  have hδg0 : (0:ℝ) < δg := by
    rw [hδg_eq]
    exact div_pos (mul_pos (pow_pos hε0 4) hδ₃0) (by nlinarith only [hRg0])
  have hτv0 : (0:ℝ) ≤ τv := by
    rw [hτv_eq]
    exact div_nonneg (mul_nonneg hHsR0.le hδg0.le) hLf0.le
  have hτvτ' : τv ≤ 2 / 10 ^ 6 * (ε * τ') := by
    have hb1 : τv = ε ^ 4 * δ₃ * HsR / (10 ^ 21 * (Rg * Lfj)) := by
      rw [hτv_eq, hδg_eq]
      field_simp [ne_of_gt hRg0, ne_of_gt hLf0]
    have hb2 : ε ^ 4 * δ₃ * HsR / (10 ^ 21 * (Rg * Lfj))
        ≤ ε ^ 4 * δ₃ * HsR / (10 ^ 21 * lgn0) := by
      refine div_le_div_of_nonneg_left ?_ ?_ ?_
      · exact mul_nonneg (mul_nonneg (pow_pos hε0 4).le hδ₃0.le) hHsR0.le
      · nlinarith only [hlgn0pos]
      · nlinarith only [hlgn0Rg]
    have hb3 : ε ^ 4 * δ₃ * HsR / (10 ^ 21 * lgn0)
        ≤ 2 / 10 ^ 6 * (ε * τ') := by
      rw [hτ'_eq]
      have hc1 : ε ^ 2 * (ε ^ 2 * δ₃ * HsR / (10 ^ 10 * lgn0)) ≤ ε ^ 2 * Ds :=
        mul_le_mul_of_nonneg_left hDs_lb (by positivity)
      have hc2 : ε ^ 2 * (ε ^ 2 * δ₃ * HsR / (10 ^ 10 * lgn0))
          = 10 ^ 11 * (ε ^ 4 * δ₃ * HsR / (10 ^ 21 * lgn0)) := by
        field_simp [ne_of_gt hlgn0pos]
      have hc3 : 2 / 10 ^ 6 * (ε * (ε * Ds / 200000)) = ε ^ 2 * Ds / 10 ^ 11 := by
        ring
      linarith only [hc1, hc2.le, hc2.ge, hc3.le, hc3.ge]
    linarith only [hb1.le, hb1.ge, hb2, hb3]
  have hR1 : (τv + θ₀) / (τ' + θ₀) ≤ 1 / 100000 * ε := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < τ' + θ₀)]
    linarith only [hτvτ', hθ₀τ', mul_nonneg hε0.le hθ₀0, hτv0]
  have hεDs : (604000:ℝ) ≤ ε * Ds := by
    have := (div_le_iff₀ hε0).mp hDs_min
    linarith
  have hlog2ub : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hlog20 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hR2 : (τ' + θ₀ + Real.log 2) / Ds ≤ 1 / 100000 * ε := by
    rw [div_le_iff₀ hDs0]
    have hd1 : θ₀ ≤ ε * Ds / (4 * 10 ^ 10) := by
      have hθ := hθ₀τ'
      rw [hτ'_eq] at hθ
      have hεε : ε * Ds / 200000 * ε / 200000 ≤ ε * Ds / (4 * 10 ^ 10) := by
        nlinarith only [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - ε)
          (by linarith only [hεDs] : (0:ℝ) ≤ ε * Ds)]
      linarith only [hθ, hεε]
    have hd2 : Real.log 2 ≤ ε * Ds / 604000 := by
      linarith only [hεDs, hlog2ub]
    rw [hτ'_eq]
    linarith only [hd1, hd2, hεDs]
  have hdec : 2 * Mv * ((τv + θ₀) / (τ' + θ₀) + (τ' + θ₀ + Real.log 2) / Ds)
      ≤ 2 * (193 * (Jl * msj)) * (2 / 100000 * ε) := by
    have hr0a : (0:ℝ) ≤ (τv + θ₀) / (τ' + θ₀) :=
      div_nonneg (by linarith) (by linarith)
    have hr0b : (0:ℝ) ≤ (τ' + θ₀ + Real.log 2) / Ds :=
      div_nonneg (by linarith) hDs0.le
    have hrsum : (τv + θ₀) / (τ' + θ₀) + (τ' + θ₀ + Real.log 2) / Ds
        ≤ 2 / 100000 * ε := by linarith only [hR1, hR2]
    exact mul_le_mul (by linarith only [hMv_ub]) hrsum
      (by linarith only [hr0a, hr0b]) (by nlinarith only [hQ0])
  -- ================= the rounding cost =================
  have hBr : SB * (12 / Kd) ≤ 579 / 2000000 * (Jl * msj * ε) := by
    have he1 : SB * (12 / Kd) = 3 * Mv * (1 / Kd) := by
      rw [hMv4]; ring
    rw [he1]
    have he2 : 3 * Mv * (1 / Kd) ≤ 3 * Mv * (ε / (2 * 10 ^ 6)) :=
      mul_le_mul_of_nonneg_left hKdinv2e6 (by linarith only [hMv0])
    have he3 : 3 * Mv * (ε / (2 * 10 ^ 6))
        ≤ 3 * (193 * (Jl * msj)) * (ε / (2 * 10 ^ 6)) :=
      mul_le_mul_of_nonneg_right (by linarith only [hMv_ub])
        (div_nonneg hε0.le (by norm_num))
    have he4 : 3 * (193 * (Jl * msj)) * (ε / (2 * 10 ^ 6))
        = 579 / 2000000 * (Jl * msj * ε) := by ring
    linarith only [he2, he3, he4.le, he4.ge]
  -- ================= assembly =================
  have hEB : EN + SB * (12 / Kd) ≤ 4 / 25 * (Jl * msj * ε) := by
    linarith only [hM1, hts2.le, hts2.ge, hdec, hstrip, hθst.le, hθst.ge,
      hMRt, hBr, mul_nonneg hQ0.le hε0.le]
  have hup : TN ≤ 2 * lw * (4 / 25 * (Jl * msj * ε)) := by
    have hu1 : S * (EN + SB * (12 / Kd)) ≤ S * (4 / 25 * (Jl * msj * ε)) :=
      mul_le_mul_of_nonneg_left hEB hS_pos.le
    have hu2 : S * (4 / 25 * (Jl * msj * ε))
        ≤ 2 * lw * (4 / 25 * (Jl * msj * ε)) :=
      mul_le_mul_of_nonneg_right hS2lw (by nlinarith only [hQ0, hε0])
    linarith only [hT, hu1, hu2]
  have hbridge : 2 * lw * (4 / 25 * (Jl * msj * ε))
      = 8 / 25 * (Jl * msj * (ε * lw)) := by ring
  have hpos : (0:ℝ) < Jl * msj * (ε * lw) :=
    mul_pos hQ0 (mul_pos hε0 hlw0)
  linarith only [hlow, hup, hbridge.le, hbridge.ge, hpos]

end FinalArithmetic

end Tao2015

end MoltResearch
