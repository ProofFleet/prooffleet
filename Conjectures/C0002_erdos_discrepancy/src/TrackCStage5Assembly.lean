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

end Tao2015

end MoltResearch
