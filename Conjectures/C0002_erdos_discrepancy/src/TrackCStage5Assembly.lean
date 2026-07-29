import MoltResearch.Discrepancy
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Elliott
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5MatomakiRadziwill
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5QuadrupleSieve
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5FilteredMR
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5VanDerCorputProof

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

section Master

open scoped NNReal

set_option maxHeartbeats 8000000 in
/-- **The Elliott master theorem, filtered form** (arXiv:1509.05422, Theorem
`elliott-red`, ordered-shift form): the nonasymptotic log-averaged
conjugate-pair bound, derived from the filtered Matomäki–Radziwiłł bound and
the prime-quadruple-sieve interface by the entropy-decrement contradiction.
The Matomäki–Radziwiłł input enters only through `hfil` (the single use-site
is the per-frequency swap input), so both the frozen all-`α` interface and the
Track R weak pair (#3044) instantiate this theorem. -/
theorem elliott_master_of_filtered
    [PrimeQuadrupleCountAssumption]
    (hfil : FilteredMR)
    (b₁ b₂ : ℕ) (hb : b₁ < b₂) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A → 1 ≤ A →
      ∀ x w : ℝ, A ≤ w → w ≤ x →
        ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → Unimodular g →
          NonPretentiousAt g A ⌈x⌉₊ →
          ‖∑ n ∈ Finset.Ioc ⌊x / w⌋₊ ⌊x⌋₊,
              g (n + b₁) * (starRingEnd ℂ) (g (n + b₂)) / (n : ℂ)‖
            ≤ ε * Real.log w := by
  classical
  -- ================= the fixed data =================
  set h : ℕ := b₂ - b₁ with hh_def
  have hh1 : 1 ≤ h := by omega
  have hhR1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh1
  obtain ⟨Cq, hCq0, hCqb⟩ := card_major_le
  -- block density
  set δ₃ : ℝ := ε / (100000 * h) with hδ₃_def
  have hδ₃0 : 0 < δ₃ := by positivity
  have hδ₃1 : δ₃ ≤ 1 := by
    rw [hδ₃_def, div_le_one (by positivity)]
    nlinarith
  have hδ₃h : δ₃ * h = ε / 100000 := by
    rw [hδ₃_def]
    field_simp
  -- major-frequency cap
  set Ξm : ℝ := 6400 ^ 4 * Cq * 2 / (δ₃ * ε ^ 4) + 1 with hΞm_def
  have hΞm1 : 1 ≤ Ξm := by
    have : 0 ≤ 6400 ^ 4 * Cq * 2 / (δ₃ * ε ^ 4) := by positivity
    rw [hΞm_def]
    linarith
  -- the rounding alphabet
  set Kd : ℕ := ⌈(10 : ℝ) ^ 6 * (Ξm + 1) / ε⌉₊ + 1 with hKd_def
  have hKd0 : 0 < Kd := by omega
  have hKdR : (10 : ℝ) ^ 6 * (Ξm + 1) / ε ≤ (Kd : ℝ) := by
    rw [hKd_def]
    push_cast
    linarith [Nat.le_ceil ((10 : ℝ) ^ 6 * (Ξm + 1) / ε)]
  -- the Matomäki–Radziwiłł strength and thresholds
  set εmr : ℝ := ε / (10000 * (Ξm + 1)) with hεmr_def
  have hεmr0 : 0 < εmr := by positivity
  set cθ : ℝ := ε * Real.log 4 / 6144 with hcθ_def
  have hcθ0 : 0 < cθ := by
    have h4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    rw [hcθ_def]
    exact div_pos (mul_pos hε0 h4) (by norm_num)
  obtain ⟨H₀mr, hMR0⟩ := hfil εmr cθ (δ₃ / 2) h hεmr0 hcθ0 (by positivity) hh1
  choose! A₀f hA₀f using hMR0
  -- the base scale
  set H₀ : ℕ := ⌈((10 : ℝ) ^ 20 / (ε ^ 3 * δ₃)) ^ 2⌉₊ + 2 * H₀mr
    + ⌈(2 : ℝ) ^ 30 / δ₃⌉₊ + 100 with hH₀_def
  have hH₀1 : 1 ≤ H₀ := by omega
  have hH₀sq : ((10 : ℝ) ^ 20 / (ε ^ 3 * δ₃)) ^ 2 ≤ (H₀ : ℝ) := by
    rw [hH₀_def]
    push_cast
    linarith [Nat.le_ceil (((10 : ℝ) ^ 20 / (ε ^ 3 * δ₃)) ^ 2),
      Nat.cast_nonneg (α := ℝ) H₀mr,
      Nat.le_ceil ((2 : ℝ) ^ 30 / δ₃),
      (by positivity : (0:ℝ) ≤ (2 : ℝ) ^ 30 / δ₃)]
  have hH₀30 : (2 : ℝ) ^ 30 / δ₃ ≤ (H₀ : ℝ) := by
    rw [hH₀_def]
    push_cast
    linarith [Nat.le_ceil ((2 : ℝ) ^ 30 / δ₃),
      (by positivity : (0:ℝ) ≤ ((10 : ℝ) ^ 20 / (ε ^ 3 * δ₃)) ^ 2),
      Nat.le_ceil (((10 : ℝ) ^ 20 / (ε ^ 3 * δ₃)) ^ 2),
      Nat.cast_nonneg (α := ℝ) H₀mr]
  -- the grid ratio fixed point
  obtain ⟨κg, hκg1, hκgfix⟩ := exists_grid_kappa ((10 : ℝ) ^ 23 / ε ^ 4)
    (Real.log H₀ / (2 * Real.log 2) + 2) (by positivity)
  set Rg : ℝ := Real.log H₀ / (2 * Real.log 2) + 2
    + Real.log κg / Real.log 2 with hRg_def
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hRg2 : 2 ≤ Rg := by
    have h1 : 0 ≤ Real.log H₀ / (2 * Real.log 2) := by
      have := Real.log_nonneg (show (1:ℝ) ≤ (H₀ : ℝ) by exact_mod_cast hH₀1)
      positivity
    have h2 : 0 ≤ Real.log κg / Real.log 2 := by
      have := Real.log_nonneg (show (1:ℝ) ≤ (κg : ℝ) by exact_mod_cast hκg1)
      positivity
    rw [hRg_def]
    linarith
  have hκgR : (10 : ℝ) ^ 23 / ε ^ 4 * Rg ≤ (κg : ℝ) := by
    rw [hRg_def]
    calc (10 : ℝ) ^ 23 / ε ^ 4
        * (Real.log H₀ / (2 * Real.log 2) + 2 + Real.log κg / Real.log 2)
        = (10 : ℝ) ^ 23 / ε ^ 4
          * (Real.log H₀ / (2 * Real.log 2) + 2 + Real.log κg / Real.log 2)
          := rfl
      _ ≤ (κg : ℝ) := by
          have := hκgfix
          calc (10 : ℝ) ^ 23 / ε ^ 4 * (Real.log H₀ / (2 * Real.log 2) + 2
              + Real.log κg / Real.log 2)
              = (10 : ℝ) ^ 23 / ε ^ 4 * ((Real.log H₀ / (2 * Real.log 2) + 2)
                + Real.log κg / Real.log 2) := by ring
            _ ≤ (κg : ℝ) := this
  -- the grid density
  set δg : ℝ := ε ^ 4 * δ₃ / (10 ^ 21 * Rg) with hδg_def
  have hδg0 : 0 < δg := by
    have : (0:ℝ) < Rg := by linarith
    positivity
  -- ================= the scale sequences =================
  set Hs : ℕ → ℕ := fun j => polyGrid κg H₀ j with hHs_def
  have hHspos : ∀ j, 0 < Hs j := fun j => polyGrid_pos hκg1 hH₀1 j
  have hHsge : ∀ j, H₀ ≤ Hs j := by
    intro j
    induction j with
    | zero => exact le_of_eq (polyGrid_zero κg H₀).symm
    | succ m ih =>
      have hstep : Hs m ≤ Hs (m + 1) := by
        rw [hHs_def]
        show polyGrid κg H₀ m ≤ polyGrid κg H₀ (m + 1)
        rw [polyGrid_succ]
        have h1 : 1 ≤ κg * (m + 2) ^ 2 :=
          Nat.one_le_iff_ne_zero.mpr
            (Nat.mul_ne_zero (by omega) (by positivity))
        calc polyGrid κg H₀ m = 1 * polyGrid κg H₀ m := (one_mul _).symm
          _ ≤ κg * (m + 2) ^ 2 * polyGrid κg H₀ m :=
            Nat.mul_le_mul_right _ h1
      exact le_trans ih hstep
  have hHsmono : ∀ i j, i ≤ j → Hs i ≤ Hs j := by
    intro i j hij
    induction j with
    | zero =>
      have h0 : i = 0 := by omega
      exact le_of_eq (by rw [h0])
    | succ m ih =>
      rcases Nat.lt_or_ge i (m + 1) with hlt | hge
      · have h1 := ih (by omega)
        have hstep : Hs m ≤ Hs (m + 1) := by
          rw [hHs_def]
          show polyGrid κg H₀ m ≤ polyGrid κg H₀ (m + 1)
          rw [polyGrid_succ]
          have h2 : 1 ≤ κg * (m + 2) ^ 2 :=
            Nat.one_le_iff_ne_zero.mpr
              (Nat.mul_ne_zero (by omega) (by positivity))
          calc polyGrid κg H₀ m = 1 * polyGrid κg H₀ m := (one_mul _).symm
            _ ≤ κg * (m + 2) ^ 2 * polyGrid κg H₀ m :=
              Nat.mul_le_mul_right _ h2
        exact le_trans h1 hstep
      · have heqi : i = m + 1 := by omega
        exact le_of_eq (by rw [heqi])
  set n0s : ℕ → ℕ := fun j => ⌊δ₃ * ((Hs j : ℕ) : ℝ)⌋₊ with hn0s_def
  have hδ₃Hs : ∀ j, (2 : ℝ) ^ 30 ≤ δ₃ * ((Hs j : ℕ) : ℝ) := by
    intro j
    have h1 : (H₀ : ℝ) ≤ ((Hs j : ℕ) : ℝ) := by exact_mod_cast hHsge j
    have h2 : (2 : ℝ) ^ 30 ≤ δ₃ * (H₀ : ℝ) := by
      rw [div_le_iff₀ hδ₃0] at hH₀30
      linarith [hH₀30]
    nlinarith [hδ₃0]
  have hn0ge : ∀ j, 2 ^ 28 ≤ n0s j := by
    intro j
    rw [hn0s_def]
    refine Nat.le_floor ?_
    have := hδ₃Hs j
    have hcast : ((2 ^ 28 : ℕ) : ℝ) = (2:ℝ) ^ 28 := by push_cast; ring
    rw [hcast]
    nlinarith
  have hn0two : ∀ j, 2 ≤ n0s j := fun j =>
    le_trans (by norm_num) (hn0ge j)
  have hn0le : ∀ j, ((n0s j : ℕ) : ℝ) ≤ δ₃ * ((Hs j : ℕ) : ℝ) := by
    intro j
    rw [hn0s_def]
    exact Nat.floor_le (by positivity)
  have hn0ge2 : ∀ j, δ₃ * ((Hs j : ℕ) : ℝ) / 2 ≤ ((n0s j : ℕ) : ℝ) := by
    intro j
    have h1 := hδ₃Hs j
    have h2 : δ₃ * ((Hs j : ℕ) : ℝ) - 1 ≤ ((n0s j : ℕ) : ℝ) := by
      rw [hn0s_def]
      have := Nat.lt_floor_add_one (δ₃ * ((Hs j : ℕ) : ℝ))
      push_cast
      linarith
    nlinarith
  set Ps : ℕ → ℕ := fun j => ∏ i : ↥(primeBlock (n0s j)), (i : ℕ)
    with hPs_def
  have hPs_coe : ∀ j', Ps j' = ∏ p ∈ primeBlock (n0s j'), p := by
    intro j'
    simp only [hPs_def]
    exact prod_primeBlock_coe (fun p => p)
  haveI hPsNZ : ∀ j, NeZero (Ps j) := by
    intro j
    have hpos : 0 < ∏ p ∈ primeBlock (n0s j), p :=
      Finset.prod_pos fun q hq => (mem_primeBlock hq).1.pos
    refine ⟨?_⟩
    rw [hPs_coe]
    omega
  obtain ⟨Jg, hJg1, hJgsel⟩ :=
    exists_polyGrid_scale' Kd κg H₀ Ps hκg1 hH₀1 hδg0
  have hHspoly : ∀ j, polyGrid κg H₀ j = Hs j := fun _ => rfl
  simp only [hHspoly] at hJgsel
  set Jls : ℕ → ℕ := fun j => Hs j - 2 * n0s j * h with hJls_def
  -- window-fit facts for the shift range
  have hn0h : ∀ j, ((n0s j : ℕ) : ℝ) * h ≤ ((Hs j : ℕ) : ℝ) / 30000 := by
    intro j
    have h1 := hn0le j
    have h2 : ((n0s j : ℕ) : ℝ) * h ≤ δ₃ * ((Hs j : ℕ) : ℝ) * h := by
      have := hδ₃0
      nlinarith [Nat.cast_nonneg (α := ℝ) (Hs j), hhR1]
    have h3 : δ₃ * ((Hs j : ℕ) : ℝ) * h = (δ₃ * h) * ((Hs j : ℕ) : ℝ) := by
      ring
    rw [h3, hδ₃h] at h2
    have h4 : ε / 100000 * ((Hs j : ℕ) : ℝ) ≤ ((Hs j : ℕ) : ℝ) / 30000 := by
      have := Nat.cast_nonneg (α := ℝ) (Hs j)
      nlinarith
    linarith
  have h2n0hHs : ∀ j, 2 * n0s j * h ≤ Hs j := by
    intro j
    have h1 := hn0h j
    have hcast : ((2 * n0s j * h : ℕ) : ℝ) ≤ ((Hs j : ℕ) : ℝ) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) (Hs j)]
    exact_mod_cast hcast
  have hJlscast : ∀ j, ((Jls j : ℕ) : ℝ)
      = ((Hs j : ℕ) : ℝ) - ((2 * n0s j * h : ℕ) : ℝ) := by
    intro j
    rw [hJls_def]
    have := h2n0hHs j
    push_cast [Nat.cast_sub this]
    ring
  have hJlsge : ∀ j, 3 * ((Hs j : ℕ) : ℝ) / 4 ≤ ((Jls j : ℕ) : ℝ) := by
    intro j
    rw [hJlscast j]
    have h1 := hn0h j
    have hcast : ((2 * n0s j * h : ℕ) : ℝ)
        = 2 * (((n0s j : ℕ) : ℝ) * h) := by push_cast; ring
    rw [hcast]
    nlinarith [Nat.cast_nonneg (α := ℝ) (Hs j)]
  have hJlsle : ∀ j, ((Jls j : ℕ) : ℝ) ≤ ((Hs j : ℕ) : ℝ) := by
    intro j
    rw [hJlscast j]
    have : (0:ℝ) ≤ ((2 * n0s j * h : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hJlspos : ∀ j, 0 < Jls j := by
    intro j
    have h1 := hJlsge j
    have h2 : (0:ℝ) < ((Hs j : ℕ) : ℝ) := by exact_mod_cast hHspos j
    have h3 : (0:ℝ) < ((Jls j : ℕ) : ℝ) := by nlinarith
    exact_mod_cast h3
  have h4n0hJls : ∀ j, 4 * n0s j * h < Jls j := by
    intro j
    have h1 := hn0h j
    have h2 := hJlsge j
    have h3 : (0:ℝ) < ((Hs j : ℕ) : ℝ) := by exact_mod_cast hHspos j
    have hcast : ((4 * n0s j * h : ℕ) : ℝ)
        = 4 * (((n0s j : ℕ) : ℝ) * h) := by push_cast; ring
    have h4 : ((4 * n0s j * h : ℕ) : ℝ) < ((Jls j : ℕ) : ℝ) := by
      rw [hcast]
      nlinarith
    exact_mod_cast h4
  haveI hJlsNZ : ∀ j, NeZero (Jls j) := fun j => ⟨(hJlspos j).ne'⟩
  -- ================= per-scale schedule quantities =================
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    have h1 : Real.exp 1 ≤ 4 := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 4 := Real.log_le_log (Real.exp_pos 1) h1
  have hlog4two : Real.log 4 ≤ 2 := by
    have h1 : (4 : ℝ) ≤ Real.exp 2 := by
      have h2 : (2.7 : ℝ) ≤ Real.exp 1 := by
        have := Real.exp_one_gt_d9
        linarith
      have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      nlinarith
    calc Real.log 4 ≤ Real.log (Real.exp 2) :=
        Real.log_le_log (by norm_num) h1
      _ = 2 := Real.log_exp 2
  have hn0R : ∀ j, (2 : ℝ) ≤ ((n0s j : ℕ) : ℝ) := by
    intro j
    exact_mod_cast hn0two j
  have hlogn0pos : ∀ j, 0 < Real.log ((n0s j : ℕ) : ℝ) := by
    intro j
    exact Real.log_pos (by linarith [hn0R j])
  have hlog2n0pos : ∀ j, 0 < Real.log (2 * ((n0s j : ℕ) : ℝ)) := by
    intro j
    exact Real.log_pos (by nlinarith [hn0R j])
  have hlog2n0le : ∀ j, Real.log (2 * ((n0s j : ℕ) : ℝ))
      ≤ 2 * Real.log ((n0s j : ℕ) : ℝ) := by
    intro j
    rw [Real.log_mul (by norm_num) (by linarith [hn0R j])]
    have h1 : Real.log 2 ≤ Real.log ((n0s j : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) (hn0R j)
    linarith
  have hlogn0le2n0 : ∀ j, Real.log ((n0s j : ℕ) : ℝ)
      ≤ Real.log (2 * ((n0s j : ℕ) : ℝ)) := by
    intro j
    refine Real.log_le_log (by linarith [hn0R j]) ?_
    nlinarith [hn0R j]
  set ms : ℕ → ℝ := fun j =>
    Real.log 4 / 12 / Real.log (2 * ((n0s j : ℕ) : ℝ)) with hms_def
  have hms_pos : ∀ j, 0 < ms j := by
    intro j
    have := hlog2n0pos j
    simp only [hms_def]
    positivity
  have hms_lb : ∀ j,
      Real.log 4 / (24 * Real.log ((n0s j : ℕ) : ℝ)) ≤ ms j := by
    intro j
    simp only [hms_def]
    rw [div_div]
    refine div_le_div_of_nonneg_left (by linarith) ?_ ?_
    · have := hlog2n0pos j
      linarith
    · have := hlog2n0le j
      have := hlogn0pos j
      nlinarith
  have hlog2lb : (0.69 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hms_ub : ∀ j, ms j ≤ 1 := by
    intro j
    simp only [hms_def]
    rw [div_div, div_le_one (by nlinarith [hlog2n0pos j])]
    have h1 : Real.log 2 ≤ Real.log (2 * ((n0s j : ℕ) : ℝ)) := by
      refine Real.log_le_log (by norm_num) ?_
      nlinarith [hn0R j]
    nlinarith [hlog2n0pos j]
  set θs : ℕ → ℝ := fun j => ε * ms j / 256 with hθs_def
  have hθs_pos : ∀ j, 0 < θs j := by
    intro j
    have := hms_pos j
    simp only [hθs_def]
    positivity
  set ts : ℕ → ℝ := fun j => ((Jls j : ℕ) : ℝ) * ms j * ε / 64 with hts_def
  have hts_pos : ∀ j, 0 < ts j := by
    intro j
    have h1 := hms_pos j
    have h2 : (0 : ℝ) < ((Jls j : ℕ) : ℝ) := by exact_mod_cast hJlspos j
    simp only [hts_def]
    positivity
  set Sigs : ℕ → ℝ := fun j =>
    ((∑ i : ↥(primeBlock (n0s j)),
      ((((8 * (Jls j / (i : ℕ) + 1) : ℕ)) : ℝ≥0)) ^ 2 : ℝ≥0) : ℝ)
    with hSigs_def
  have hSigs_cast : ∀ j, Sigs j = ∑ i : ↥(primeBlock (n0s j)),
      (((8 * (Jls j / (i : ℕ) + 1) : ℕ)) : ℝ) ^ 2 := by
    intro j
    simp only [hSigs_def]
    push_cast
    rfl
  have hSigs_pos : ∀ j, 0 < Sigs j := by
    intro j
    rw [hSigs_cast j]
    have hn01 : 1 ≤ n0s j := by
      have := hn0two j
      omega
    obtain ⟨p, hp⟩ := primeBlock_nonempty hn01
    have hterm : (0 : ℝ) < (((8 * (Jls j / p + 1) : ℕ)) : ℝ) ^ 2 := by
      have h8 : 0 < 8 * (Jls j / p + 1) :=
        Nat.mul_pos (by norm_num) (Nat.succ_pos _)
      have h8R : (1 : ℝ) ≤ (((8 * (Jls j / p + 1) : ℕ)) : ℝ) := by
        exact_mod_cast h8
      nlinarith
    have hmem : (⟨p, hp⟩ : ↥(primeBlock (n0s j))) ∈ Finset.univ :=
      Finset.mem_univ _
    refine lt_of_lt_of_le hterm ?_
    refine Finset.single_le_sum (f := fun i : ↥(primeBlock (n0s j)) =>
      (((8 * (Jls j / (i : ℕ) + 1) : ℕ)) : ℝ) ^ 2) ?_ hmem
    intro i _
    positivity
  have hq_ub : ∀ j, ∀ i : ↥(primeBlock (n0s j)),
      ((Jls j / (i : ℕ) : ℕ) : ℝ) ≤ 2 / δ₃ := by
    intro j i
    have hfacts := mem_primeBlock i.2
    have hdivle : Jls j / (i : ℕ) ≤ Jls j / n0s j :=
      Nat.div_le_div_left hfacts.2.1.le (by omega)
    have h1 : ((Jls j / (i : ℕ) : ℕ) : ℝ) ≤ ((Jls j / n0s j : ℕ) : ℝ) := by
      exact_mod_cast hdivle
    have h2 : ((Jls j / n0s j : ℕ) : ℝ)
        ≤ ((Jls j : ℕ) : ℝ) / ((n0s j : ℕ) : ℝ) := Nat.cast_div_le
    have hHspos' : (0 : ℝ) < ((Hs j : ℕ) : ℝ) := by exact_mod_cast hHspos j
    have hn0pos : (0 : ℝ) < ((n0s j : ℕ) : ℝ) := by linarith [hn0R j]
    have h3a : ((Jls j : ℕ) : ℝ) / ((n0s j : ℕ) : ℝ)
        ≤ ((Hs j : ℕ) : ℝ) / ((n0s j : ℕ) : ℝ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hJlsle j)
        (inv_nonneg.mpr hn0pos.le)
    have h3b : ((Hs j : ℕ) : ℝ) / ((n0s j : ℕ) : ℝ)
        ≤ ((Hs j : ℕ) : ℝ) / (δ₃ * ((Hs j : ℕ) : ℝ) / 2) :=
      div_le_div_of_nonneg_left hHspos'.le (by positivity) (hn0ge2 j)
    have h4 : ((Hs j : ℕ) : ℝ) / (δ₃ * ((Hs j : ℕ) : ℝ) / 2) = 2 / δ₃ := by
      field_simp
    linarith
  have hc_ub : ∀ j, ∀ i : ↥(primeBlock (n0s j)),
      (((8 * (Jls j / (i : ℕ) + 1) : ℕ)) : ℝ) ≤ 24 / δ₃ := by
    intro j i
    have h1 := hq_ub j i
    have hcast : (((8 * (Jls j / (i : ℕ) + 1) : ℕ)) : ℝ)
        = 8 * ((Jls j / (i : ℕ) : ℕ) : ℝ) + 8 := by push_cast; ring
    have h8 : (8 : ℝ) ≤ 8 / δ₃ := by
      rw [le_div_iff₀ hδ₃0]
      nlinarith
    rw [hcast]
    have h2 : 8 * ((Jls j / (i : ℕ) : ℕ) : ℝ) ≤ 16 / δ₃ := by
      calc 8 * ((Jls j / (i : ℕ) : ℕ) : ℝ) ≤ 8 * (2 / δ₃) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = 16 / δ₃ := by ring
    have h3 : (16 : ℝ) / δ₃ + 8 / δ₃ = 24 / δ₃ := by ring
    linarith
  have hSigs_ub : ∀ j, Sigs j
      ≤ 1152 * Real.log 4 * ((Hs j : ℕ) : ℝ)
        / (δ₃ * Real.log ((n0s j : ℕ) : ℝ)) := by
    intro j
    rw [hSigs_cast j]
    have hper : ∀ i : ↥(primeBlock (n0s j)),
        (((8 * (Jls j / (i : ℕ) + 1) : ℕ)) : ℝ) ^ 2 ≤ (24 / δ₃) ^ 2 := by
      intro i
      have h1 := hc_ub j i
      have h0 : (0 : ℝ) ≤ (((8 * (Jls j / (i : ℕ) + 1) : ℕ)) : ℝ) :=
        Nat.cast_nonneg _
      nlinarith
    have hcard : ∑ i : ↥(primeBlock (n0s j)),
        (((8 * (Jls j / (i : ℕ) + 1) : ℕ)) : ℝ) ^ 2
        ≤ ((primeBlock (n0s j)).card : ℝ) * (24 / δ₃) ^ 2 := by
      calc ∑ i : ↥(primeBlock (n0s j)),
          (((8 * (Jls j / (i : ℕ) + 1) : ℕ)) : ℝ) ^ 2
          ≤ ∑ _i : ↥(primeBlock (n0s j)), (24 / δ₃) ^ 2 :=
            Finset.sum_le_sum fun i _ => hper i
        _ = ((primeBlock (n0s j)).card : ℝ) * (24 / δ₃) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
              nsmul_eq_mul]
    have hcardb := card_primeBlock_le (hn0two j)
    have hlogn0 := hlogn0pos j
    have hn0δ := hn0le j
    have hHspos' : (0 : ℝ) < ((Hs j : ℕ) : ℝ) := by exact_mod_cast hHspos j
    have hchain : ((primeBlock (n0s j)).card : ℝ) * (24 / δ₃) ^ 2
        ≤ (2 * (δ₃ * ((Hs j : ℕ) : ℝ)) * Real.log 4
            / Real.log ((n0s j : ℕ) : ℝ)) * (24 / δ₃) ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      refine le_trans hcardb ?_
      have hnum : 2 * ((n0s j : ℕ) : ℝ) * Real.log 4
          ≤ 2 * (δ₃ * ((Hs j : ℕ) : ℝ)) * Real.log 4 := by
        nlinarith [hlog4]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hnum
        (inv_nonneg.mpr (le_of_lt hlogn0))
    have heq : (2 * (δ₃ * ((Hs j : ℕ) : ℝ)) * Real.log 4
          / Real.log ((n0s j : ℕ) : ℝ)) * (24 / δ₃) ^ 2
        = 1152 * Real.log 4 * ((Hs j : ℕ) : ℝ)
          / (δ₃ * Real.log ((n0s j : ℕ) : ℝ)) := by
      field_simp
      ring
    linarith [hcard, hchain, heq.le, heq.ge]
  -- ================= the deviation scale and its floor =================
  set Ds : ℕ → ℝ := fun j => ts j ^ 2 / (2 * Sigs j) - Real.log 2
    with hDs_def
  set τ's : ℕ → ℝ := fun j => ε * Ds j / 200000 with hτ's_def
  have hts_lb : ∀ j, ε * ((Hs j : ℕ) : ℝ) * Real.log 4
      / (2048 * Real.log ((n0s j : ℕ) : ℝ)) ≤ ts j := by
    intro j
    have h1 := hJlsge j
    have h2 := hms_lb j
    have hlogn0 := hlogn0pos j
    have hHs0 : (0 : ℝ) < ((Hs j : ℕ) : ℝ) := by exact_mod_cast hHspos j
    have hJl0 : (0 : ℝ) ≤ ((Jls j : ℕ) : ℝ) := Nat.cast_nonneg _
    have hprod : (3 * ((Hs j : ℕ) : ℝ) / 4)
        * (Real.log 4 / (24 * Real.log ((n0s j : ℕ) : ℝ)))
        ≤ ((Jls j : ℕ) : ℝ) * ms j :=
      mul_le_mul h1 h2 (by positivity) hJl0
    have heq : (3 * ((Hs j : ℕ) : ℝ) / 4)
        * (Real.log 4 / (24 * Real.log ((n0s j : ℕ) : ℝ))) * ε / 64
        = ε * ((Hs j : ℕ) : ℝ) * Real.log 4
          / (2048 * Real.log ((n0s j : ℕ) : ℝ)) := by
      field_simp
      ring
    simp only [hts_def]
    calc ε * ((Hs j : ℕ) : ℝ) * Real.log 4
        / (2048 * Real.log ((n0s j : ℕ) : ℝ))
        = (3 * ((Hs j : ℕ) : ℝ) / 4)
          * (Real.log 4 / (24 * Real.log ((n0s j : ℕ) : ℝ))) * ε / 64 :=
        heq.symm
      _ ≤ ((Jls j : ℕ) : ℝ) * ms j * ε / 64 := by
        gcongr
  have hHkey : ∀ j, (10 : ℝ) ^ 20 / (2 * ε)
      ≤ ε ^ 2 * δ₃ * ((Hs j : ℕ) : ℝ) / Real.log ((n0s j : ℕ) : ℝ) := by
    intro j
    have hHs1 : (1 : ℝ) ≤ ((Hs j : ℕ) : ℝ) := by
      exact_mod_cast le_trans hH₀1 (hHsge j)
    have hlogHs : Real.log ((n0s j : ℕ) : ℝ)
        ≤ 2 * Real.sqrt ((Hs j : ℕ) : ℝ) := by
      have ha : Real.log ((n0s j : ℕ) : ℝ) ≤ Real.log ((Hs j : ℕ) : ℝ) := by
        refine Real.log_le_log (by linarith [hn0R j]) ?_
        have h1 := hn0le j
        nlinarith [hδ₃1, hHs1]
      exact le_trans ha (log_le_two_sqrt hHs1)
    have hsqrtH₀ : (10 : ℝ) ^ 20 / (ε ^ 3 * δ₃)
        ≤ Real.sqrt ((Hs j : ℕ) : ℝ) := by
      have h1 : ((10 : ℝ) ^ 20 / (ε ^ 3 * δ₃)) ^ 2 ≤ ((Hs j : ℕ) : ℝ) :=
        le_trans hH₀sq (by exact_mod_cast hHsge j)
      have h2 := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_sq (by positivity)] at h2
    have hlog0 := hlogn0pos j
    have hs0 : (0 : ℝ) < Real.sqrt ((Hs j : ℕ) : ℝ) :=
      Real.sqrt_pos.mpr (by linarith)
    have hsq : Real.sqrt ((Hs j : ℕ) : ℝ) * Real.sqrt ((Hs j : ℕ) : ℝ)
        = ((Hs j : ℕ) : ℝ) := Real.mul_self_sqrt (by positivity)
    have hstep1 : ε ^ 2 * δ₃ * ((Hs j : ℕ) : ℝ)
        / (2 * Real.sqrt ((Hs j : ℕ) : ℝ))
        ≤ ε ^ 2 * δ₃ * ((Hs j : ℕ) : ℝ) / Real.log ((n0s j : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hlog0 hlogHs
    have hstep2 : (10 : ℝ) ^ 20 / (2 * ε)
        ≤ ε ^ 2 * δ₃ * ((Hs j : ℕ) : ℝ)
          / (2 * Real.sqrt ((Hs j : ℕ) : ℝ)) := by
      rw [le_div_iff₀ (by positivity)]
      have hkey2 : (10 : ℝ) ^ 20 / ε ≤ ε ^ 2 * δ₃
          * Real.sqrt ((Hs j : ℕ) : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hsqrtH₀
          (by positivity : (0 : ℝ) ≤ ε ^ 2 * δ₃)
        have heq3 : ε ^ 2 * δ₃ * ((10 : ℝ) ^ 20 / (ε ^ 3 * δ₃))
            = 10 ^ 20 / ε := by
          field_simp
        linarith [heq3.le, heq3.ge]
      have hgoal2 : (10 : ℝ) ^ 20 / (2 * ε)
          * (2 * Real.sqrt ((Hs j : ℕ) : ℝ))
          = (10 ^ 20 / ε) * Real.sqrt ((Hs j : ℕ) : ℝ) := by
        field_simp
      rw [hgoal2]
      calc (10 ^ 20 / ε : ℝ) * Real.sqrt ((Hs j : ℕ) : ℝ)
          ≤ (ε ^ 2 * δ₃ * Real.sqrt ((Hs j : ℕ) : ℝ))
            * Real.sqrt ((Hs j : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right hkey2 hs0.le
        _ = ε ^ 2 * δ₃ * ((Hs j : ℕ) : ℝ) := by
            rw [mul_assoc, hsq]
    linarith [hstep1, hstep2]
  have hDs_lb : ∀ j, ε ^ 2 * δ₃ * ((Hs j : ℕ) : ℝ)
      / ((10 : ℝ) ^ 10 * Real.log ((n0s j : ℕ) : ℝ)) ≤ Ds j := by
    intro j
    have hlogn0 := hlogn0pos j
    have hHs0 : (0 : ℝ) < ((Hs j : ℕ) : ℝ) := by exact_mod_cast hHspos j
    have hne1 : Real.log ((n0s j : ℕ) : ℝ) ≠ 0 := ne_of_gt hlogn0
    have hne2 : ((Hs j : ℕ) : ℝ) ≠ 0 := ne_of_gt hHs0
    have hne3 : δ₃ ≠ 0 := ne_of_gt hδ₃0
    have hne4 : Real.log 4 ≠ 0 := by linarith
    -- the quotient at the extremes
    have hQeq : (ε * ((Hs j : ℕ) : ℝ) * Real.log 4
          / (2048 * Real.log ((n0s j : ℕ) : ℝ))) ^ 2
        / (2 * (1152 * Real.log 4 * ((Hs j : ℕ) : ℝ)
          / (δ₃ * Real.log ((n0s j : ℕ) : ℝ))))
        = (ε ^ 2 * δ₃ * ((Hs j : ℕ) : ℝ) / Real.log ((n0s j : ℕ) : ℝ))
          * Real.log 4 / 9663676416 := by
      field_simp
      ring
    -- monotonicity of the quotient in numerator and denominator
    have hts0 := hts_pos j
    have htlb0 : (0 : ℝ) < ε * ((Hs j : ℕ) : ℝ) * Real.log 4
        / (2048 * Real.log ((n0s j : ℕ) : ℝ)) := by
      have : (0:ℝ) < Real.log 4 := by linarith
      positivity
    have hnum : (ε * ((Hs j : ℕ) : ℝ) * Real.log 4
        / (2048 * Real.log ((n0s j : ℕ) : ℝ))) ^ 2 ≤ ts j ^ 2 := by
      have h1 := hts_lb j
      nlinarith [htlb0]
    have hden : 2 * Sigs j ≤ 2 * (1152 * Real.log 4 * ((Hs j : ℕ) : ℝ)
        / (δ₃ * Real.log ((n0s j : ℕ) : ℝ))) := by
      have := hSigs_ub j
      linarith
    have hSig0 := hSigs_pos j
    have hchain1 : (ε * ((Hs j : ℕ) : ℝ) * Real.log 4
          / (2048 * Real.log ((n0s j : ℕ) : ℝ))) ^ 2
        / (2 * (1152 * Real.log 4 * ((Hs j : ℕ) : ℝ)
          / (δ₃ * Real.log ((n0s j : ℕ) : ℝ))))
        ≤ ts j ^ 2 / (2 * Sigs j) := by
      have hA : (ε * ((Hs j : ℕ) : ℝ) * Real.log 4
            / (2048 * Real.log ((n0s j : ℕ) : ℝ))) ^ 2
          / (2 * (1152 * Real.log 4 * ((Hs j : ℕ) : ℝ)
            / (δ₃ * Real.log ((n0s j : ℕ) : ℝ))))
          ≤ (ε * ((Hs j : ℕ) : ℝ) * Real.log 4
            / (2048 * Real.log ((n0s j : ℕ) : ℝ))) ^ 2 / (2 * Sigs j) :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) hden
      have hB : (ε * ((Hs j : ℕ) : ℝ) * Real.log 4
            / (2048 * Real.log ((n0s j : ℕ) : ℝ))) ^ 2 / (2 * Sigs j)
          ≤ ts j ^ 2 / (2 * Sigs j) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hnum
          (inv_nonneg.mpr (by linarith))
      linarith
    -- the size of the ratio
    set X : ℝ := ε ^ 2 * δ₃ * ((Hs j : ℕ) : ℝ)
      / Real.log ((n0s j : ℕ) : ℝ) with hX_def
    have hXlb := hHkey j
    have hX5 : (5 : ℝ) * 10 ^ 19 ≤ X := by
      have hstep : (5 : ℝ) * 10 ^ 19 ≤ (10 : ℝ) ^ 20 / (2 * ε) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      linarith
    have hX0 : (0 : ℝ) ≤ X := by linarith
    have hlog2ub : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    have hXlog4 : X ≤ X * Real.log 4 := by nlinarith
    have hgoal_eq : ε ^ 2 * δ₃ * ((Hs j : ℕ) : ℝ)
        / ((10 : ℝ) ^ 10 * Real.log ((n0s j : ℕ) : ℝ)) = X / 10 ^ 10 := by
      rw [hX_def]
      field_simp
    have hfinal : X / 10 ^ 10 ≤ X * Real.log 4 / 9663676416 - Real.log 2 := by
      have h1 : X / 9663676416 ≤ X * Real.log 4 / 9663676416 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hXlog4 (by norm_num)
      linarith
    have hDval : Ds j = ts j ^ 2 / (2 * Sigs j) - Real.log 2 := by
      simp only [hDs_def]
    rw [hDval, hgoal_eq]
    linarith [hchain1, hQeq.le, hQeq.ge, hfinal]
  have hDs_min : ∀ j, 604000 / ε ≤ Ds j := by
    intro j
    have h1 := hDs_lb j
    have hlogn0 := hlogn0pos j
    have hkey := hHkey j
    have heq : ε ^ 2 * δ₃ * ((Hs j : ℕ) : ℝ)
        / ((10 : ℝ) ^ 10 * Real.log ((n0s j : ℕ) : ℝ))
        = (ε ^ 2 * δ₃ * ((Hs j : ℕ) : ℝ) / Real.log ((n0s j : ℕ) : ℝ))
          / 10 ^ 10 := by
      field_simp
    have h2 : (10 : ℝ) ^ 20 / (2 * ε) / 10 ^ 10
        ≤ (ε ^ 2 * δ₃ * ((Hs j : ℕ) : ℝ) / Real.log ((n0s j : ℕ) : ℝ))
          / 10 ^ 10 := by
      rw [div_eq_mul_inv ((10:ℝ)^20 / (2*ε)), div_eq_mul_inv
        (ε ^ 2 * δ₃ * ((Hs j : ℕ) : ℝ) / Real.log ((n0s j : ℕ) : ℝ))]
      exact mul_le_mul_of_nonneg_right hkey (by norm_num)
    have h3 : 604000 / ε ≤ (10 : ℝ) ^ 20 / (2 * ε) / 10 ^ 10 := by
      rw [div_div]
      rw [div_le_div_iff₀ hε0 (by positivity)]
      nlinarith
    linarith [heq.le, heq.ge]
  have hDs_pos : ∀ j, 0 < Ds j := by
    intro j
    have := hDs_min j
    have h604 : (0 : ℝ) < 604000 / ε := by positivity
    linarith
  have hτ's_pos : ∀ j, 0 < τ's j := by
    intro j
    have := hDs_pos j
    simp only [hτ's_def]
    positivity
  -- make the schedule opaque: every later step is equational
  clear_value δ₃ Ξm Kd εmr H₀ Rg δg Hs n0s Jls ms θs ts Sigs Ds τ's
  -- ================= the fixed caps =================
  set n0m : ℕ := n0s Jg with hn0m_def
  have hn0mub : ∀ j, j ≤ Jg → n0s j ≤ n0m := by
    intro j hj
    simp only [hn0s_def, hn0m_def]
    refine Nat.floor_le_floor ?_
    have h1 : Hs j ≤ Hs Jg := hHsmono j Jg hj
    have h2 : ((Hs j : ℕ) : ℝ) ≤ ((Hs Jg : ℕ) : ℝ) := by exact_mod_cast h1
    nlinarith [hδ₃0]
  set Pm : ℕ := 4 ^ (2 * n0m) with hPm_def
  have hPm1 : 1 ≤ Pm := Nat.one_le_pow _ _ (by norm_num)
  have hPsub : ∀ j, j ≤ Jg → Ps j ≤ Pm := by
    intro j hj
    have h1 : Ps j ≤ 4 ^ (2 * n0s j) := by
      rw [hPs_coe]
      exact prod_primeBlock_le_pow (n0s j)
    refine le_trans h1 ?_
    simp only [hPm_def]
    exact Nat.pow_le_pow_right (by norm_num)
      (by have := hn0mub j hj; omega)
  have hPs2 : ∀ j, 2 ≤ Ps j := by
    intro j
    have h1 : 1 ≤ n0s j := by have := hn0two j; omega
    rw [hPs_coe]
    exact two_le_prod_primeBlock h1
  have hn0mPm : 2 * n0m ≤ 4 * Pm := by
    have h1 : n0m < 4 ^ n0m := Nat.lt_pow_self (by norm_num)
    have h2 : (4:ℕ) ^ n0m ≤ 4 ^ (2 * n0m) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [hPm_def]
    omega
  set NS : ℕ := 4 * Pm + 3 * b₂ + 4 with hNS_def
  have hNS1 : 1 ≤ NS := by omega
  set Wneed : ℕ := 2 * (κg * (Jg + 2) ^ 2 * Hs Jg) + 1 with hWneed_def
  set Cbig : ℕ := Wneed + 2 * n0m + Pm + 2 with hCbig_def
  have hCbig1 : 1 ≤ Cbig := by omega
  set Abase : ℕ := (Cbig + 1) * (NS + 2) + 4 * Cbig with hAbase_def
  -- ================= the log-threshold =================
  set E1f : ℕ → ℝ := fun j =>
    3 * ((Jls j : ℕ) : ℝ) ^ 2 * ((n0s j : ℕ) : ℝ) / NS
      + ((Jls j : ℕ) : ℝ) * (2 * Real.log (2 * ((n0s j : ℕ) : ℝ)) + 2)
    with hE1f_def
  have hE1f0 : ∀ j, 0 ≤ E1f j := by
    intro j
    have h1 := hlog2n0pos j
    have hNS0 : (0:ℝ) < (NS:ℝ) := by exact_mod_cast hNS1
    simp only [hE1f_def]
    positivity
  set cardST : ℕ → ℝ := fun j =>
    (Fintype.card (PatternSpace Kd (Hs j) × ZMod (Ps j)) : ℝ) with hcardST_def
  have hcardST0 : ∀ j, 0 ≤ cardST j := fun j => Nat.cast_nonneg _
  set Lf : ℕ → ℝ := fun j =>
    ((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ) with hLf_def
  have hLf_pos : ∀ j, 0 < Lf j := by
    intro j
    have h2 : (2 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2 ≤ j + 2)
    have hlog : 0 < Real.log ((j + 2 : ℕ) : ℝ) :=
      Real.log_pos (by linarith)
    simp only [hLf_def]
    positivity
  set Λf : ℕ → ℝ := fun j =>
      48 * ((κg * (j + 2) ^ 2 : ℕ) : ℝ) * Lf j / (NS * δg)
    + 6 * ((κg * (j + 2) ^ 2 : ℕ) : ℝ) * ((Hs j : ℕ) : ℝ)
        * (16 * cardST j * Lf j) ^ 2 / (NS * (δg * ((Hs j : ℕ) : ℝ)) ^ 2)
    + 2 * (4 + 2 * Real.log (2 * (Pm : ℝ))) * 200000 / (ε * τ's j)
    + 4 * (Real.log ((NS + 2 : ℕ) : ℝ) + 1
        + E1f j / (((Jls j : ℕ) : ℝ) * ms j)) / ε
    with hΛf_def
  have hlogPm0 : 0 ≤ Real.log (2 * (Pm : ℝ)) := by
    refine Real.log_nonneg ?_
    have : (1:ℝ) ≤ (Pm:ℝ) := by exact_mod_cast hPm1
    linarith
  have hlogNS20 : 0 ≤ Real.log ((NS + 2 : ℕ) : ℝ) := by
    refine Real.log_nonneg ?_
    exact_mod_cast (by omega : 1 ≤ NS + 2)
  have hNSR0 : (0:ℝ) < (NS:ℝ) := by exact_mod_cast hNS1
  have hT1nn : ∀ j, (0:ℝ) ≤ 48 * ((κg * (j + 2) ^ 2 : ℕ) : ℝ) * Lf j
      / (NS * δg) := by
    intro j
    refine div_nonneg ?_ (mul_nonneg hNSR0.le hδg0.le)
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (hLf_pos j).le
  have hT2nn : ∀ j, (0:ℝ) ≤ 6 * ((κg * (j + 2) ^ 2 : ℕ) : ℝ)
      * ((Hs j : ℕ) : ℝ) * (16 * cardST j * Lf j) ^ 2
      / (NS * (δg * ((Hs j : ℕ) : ℝ)) ^ 2) := by
    intro j
    refine div_nonneg ?_ (mul_nonneg hNSR0.le (sq_nonneg _))
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (sq_nonneg _)
  have hT3nn : ∀ j, (0:ℝ) ≤ 2 * (4 + 2 * Real.log (2 * (Pm : ℝ))) * 200000
      / (ε * τ's j) := by
    intro j
    refine div_nonneg ?_ (mul_nonneg hε0.le (hτ's_pos j).le)
    nlinarith [hlogPm0]
  have hT4nn : ∀ j, (0:ℝ) ≤ 4 * (Real.log ((NS + 2 : ℕ) : ℝ) + 1
      + E1f j / (((Jls j : ℕ) : ℝ) * ms j)) / ε := by
    intro j
    have hJl0 : (0:ℝ) < ((Jls j : ℕ) : ℝ) := by exact_mod_cast hJlspos j
    have hE : (0:ℝ) ≤ E1f j / (((Jls j : ℕ) : ℝ) * ms j) :=
      div_nonneg (hE1f0 j) (mul_nonneg hJl0.le (hms_pos j).le)
    refine div_nonneg ?_ hε0.le
    nlinarith [hlogNS20]
  have hΛf0 : ∀ j, 0 ≤ Λf j := by
    intro j
    simp only [hΛf_def]
    linarith [hT1nn j, hT2nn j, hT3nn j, hT4nn j]
  set Λb : ℝ := 1 + Real.log 2 + 2 * Real.log ((NS + 2 : ℕ) : ℝ)
    + 2 * Real.log ((NS + 1 : ℕ) : ℝ)
    + 2 * (4 + 2 * Real.log (2 * (Pm : ℝ))) with hΛb_def
  have hlogNS10 : 0 ≤ Real.log ((NS + 1 : ℕ) : ℝ) := by
    refine Real.log_nonneg ?_
    exact_mod_cast (by omega : 1 ≤ NS + 1)
  have hΛb1 : 1 ≤ Λb := by
    simp only [hΛb_def]
    linarith [hlog2, hlogNS20, hlogNS10, hlogPm0]
  have hne : (Finset.range Jg).Nonempty :=
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  set Λtot : ℝ := Λb + (Finset.range Jg).sup' hne Λf with hΛtot_def
  have hΛtot_b : Λb ≤ Λtot := by
    simp only [hΛtot_def]
    have h1 : Λf 0 ≤ (Finset.range Jg).sup' hne Λf :=
      Finset.le_sup' Λf (Finset.mem_range.mpr (by omega))
    linarith [hΛf0 0]
  have hΛtot_f : ∀ j, j < Jg → Λf j ≤ Λtot := by
    intro j hj
    simp only [hΛtot_def]
    have h1 : Λf j ≤ (Finset.range Jg).sup' hne Λf :=
      Finset.le_sup' Λf (Finset.mem_range.mpr hj)
    linarith [hΛb1]
  set AMR : ℝ := (Finset.range Jg).sup' hne (fun j => A₀f (Jls j))
    with hAMR_def
  have hAMR_f : ∀ j, j < Jg → A₀f (Jls j) ≤ AMR := by
    intro j hj
    simp only [hAMR_def]
    exact Finset.le_sup' (fun j => A₀f (Jls j)) (Finset.mem_range.mpr hj)
  set A₀v : ℝ := ((Abase : ℕ) : ℝ) + Real.exp Λtot + max 0 AMR + 1
    with hA₀v_def
  refine ⟨A₀v, ?_⟩
  intro A hA₀A hA1 x w hAw hwx g hcm huni hnp
  by_contra hbig
  push_neg at hbig
  -- ================= the window =================
  set A' : ℕ := ⌊x / w⌋₊ with hA'_def
  set B' : ℕ := ⌊x⌋₊ with hB'_def
  have hw1 : (1 : ℝ) ≤ w := le_trans hA1 hAw
  have hx1 : (1 : ℝ) ≤ x := le_trans hw1 hwx
  have hw0 : (0 : ℝ) < w := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hexp0 : 0 < Real.exp Λtot := Real.exp_pos _
  have hAbase0 : (0 : ℝ) ≤ ((Abase : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmax0 : (0 : ℝ) ≤ max 0 AMR := le_max_left _ _
  have hwA₀ : A₀v ≤ w := le_trans hA₀A hAw
  have hAbase_w : ((Abase : ℕ) : ℝ) ≤ w := by
    have : ((Abase : ℕ) : ℝ) ≤ A₀v := by
      rw [hA₀v_def]
      linarith
    linarith
  have hAMR_w : ∀ j, j < Jg → A₀f (Jls j) ≤ A := by
    intro j hj
    have h1 : A₀f (Jls j) ≤ AMR := hAMR_f j hj
    have h2 : AMR ≤ max 0 AMR := le_max_right _ _
    have h3 : max 0 AMR ≤ A₀v := by
      rw [hA₀v_def]
      linarith
    linarith [hA₀A]
  have hlogw : Λtot ≤ Real.log w := by
    have h1 : Real.exp Λtot ≤ w := by
      have : Real.exp Λtot ≤ A₀v := by
        rw [hA₀v_def]
        linarith
      linarith
    calc Λtot = Real.log (Real.exp Λtot) := (Real.log_exp _).symm
      _ ≤ Real.log w := Real.log_le_log (Real.exp_pos _) h1
  have hΛbw : Λb ≤ Real.log w := le_trans hΛtot_b hlogw
  have hΛbw' : 1 + Real.log 2 + 2 * Real.log ((NS + 2 : ℕ) : ℝ)
      + 2 * Real.log ((NS + 1 : ℕ) : ℝ)
      + 2 * (4 + 2 * Real.log (2 * (Pm : ℝ))) ≤ Real.log w := by
    rw [hΛb_def] at hΛbw
    exact hΛbw
  have hlogw1 : 1 ≤ Real.log w := by
    linarith [hlog2, hlogNS20, hlogNS10, hlogPm0]
  have hlogw0 : 0 < Real.log w := by linarith
  -- harmonic mass of the trimmed window
  set S : ℝ := ∑ n ∈ Finset.Ioc (max A' NS) B', (1 : ℝ) / n with hS_def
  have hS_ub : S ≤ Real.log w + Real.log ((NS + 1 : ℕ) : ℝ) := by
    rw [hS_def, hA'_def, hB'_def]
    exact harmonic_trim_le NS hNS1 hw1 hwx
  have hS_lb : Real.log w - Real.log ((NS + 2 : ℕ) : ℝ) ≤ S := by
    rw [hS_def, hA'_def, hB'_def]
    exact harmonic_trim_ge NS hNS1 hw1 hwx
  have hS_half : Real.log w / 2 ≤ S := by
    have h1 : 2 * Real.log ((NS + 2 : ℕ) : ℝ) ≤ Real.log w := by
      linarith [hlog2, hlogNS10, hlogPm0]
    linarith
  have hS_2logw : S ≤ 2 * Real.log w := by
    have h1 : Real.log ((NS + 1 : ℕ) : ℝ) ≤ Real.log w := by
      linarith [hlog2, hlogNS20, hlogPm0]
    linarith
  have hS_pos : 0 < S := by linarith
  clear_value A' B' S
  -- basic window inequalities
  have hA'1 : 1 ≤ A' := by
    rw [hA'_def]
    refine Nat.le_floor ?_
    have h1 : (1 : ℝ) ≤ x / w := (one_le_div hw0).mpr hwx
    exact_mod_cast h1
  have hA''NS : NS ≤ max A' NS := le_max_right _ _
  have hA''1 : 1 ≤ max A' NS := le_trans hNS1 hA''NS
  have hcap : ∀ C : ℕ, 1 ≤ C → C ≤ Cbig → C * (max A' NS + 1) ≤ B' := by
    intro C hC1 hCC
    have hwcap : (((Cbig + 1) * (NS + 2) + 4 * Cbig : ℕ) : ℝ) ≤ w := by
      rw [← hAbase_def]
      exact hAbase_w
    have h1 := window_capacity hNS1 hCbig1 hwcap hwx
    rw [← hA'_def, ← hB'_def] at h1
    calc C * (max A' NS + 1) ≤ Cbig * (max A' NS + 1) :=
        Nat.mul_le_mul_right _ hCC
      _ ≤ B' := h1
  have hA''B' : max A' NS < B' := by
    have h1 := hcap 2 (by omega) (by omega)
    omega
  have hA''B'R : ((max A' NS : ℕ) : ℝ) < ((B' : ℕ) : ℝ) := by
    exact_mod_cast hA''B'
  -- ================= trim and shift the correlation =================
  have hb₂ : b₂ = b₁ + h := by omega
  have htrim := norm_pair_trim huni b₁ b₂ NS A' B' hNS1 hA'1
  have hWtrim : ε * Real.log w - Real.log NS
      ≤ ‖∑ n ∈ Finset.Ioc (max A' NS) B',
          g (n + b₁) * (starRingEnd ℂ) (g (n + b₂)) / (n : ℂ)‖ := by
    linarith only [htrim, hbig]
  have hWtrim' : ε * Real.log w - Real.log NS
      ≤ ‖∑ n ∈ Finset.Ioc (max A' NS) B',
          g (n + b₁) * (starRingEnd ℂ) (g (n + b₁ + h)) / (n : ℂ)‖ := by
    have hcong : ∀ n ∈ Finset.Ioc (max A' NS) B',
        g (n + b₁) * (starRingEnd ℂ) (g (n + b₂)) / (n : ℂ)
        = g (n + b₁) * (starRingEnd ℂ) (g (n + b₁ + h)) / (n : ℂ) := by
      intro n _
      have : n + b₂ = n + b₁ + h := by omega
      rw [this]
    rw [← Finset.sum_congr rfl hcong]
    exact hWtrim
  have hS₀ : ε * Real.log w - Real.log NS - 1
      ≤ ‖∑ m ∈ Finset.Ioc (max A' NS) B',
          g m * (starRingEnd ℂ) (g (m + h)) / (m : ℂ)‖ := by
    have hshift := shift_pair_window_ge huni (b₁ := b₁) (h := h)
      (A := max A' NS) (B := B') hA''1 hWtrim'
    have h3b : 3 * (b₁ : ℝ) / ((max A' NS : ℕ) : ℝ) ≤ 1 := by
      have hNSb : 3 * b₁ ≤ NS := by
        rw [hNS_def]
        omega
      have h1 : (3 * (b₁ : ℕ) : ℝ) ≤ ((max A' NS : ℕ) : ℝ) := by
        have : 3 * b₁ ≤ max A' NS := le_trans hNSb hA''NS
        exact_mod_cast this
      have h2 : (0 : ℝ) < ((max A' NS : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < max A' NS)
      rw [div_le_one h2]
      push_cast at h1 ⊢
      linarith
    linarith
  -- ================= scale selection =================
  have hkB : ∀ j, j < Jg → max A' NS + κg * (j + 2) ^ 2 * Hs j
      + κg * (j + 2) ^ 2 * Hs j < B' := by
    intro j hj
    have h1 : κg * (j + 2) ^ 2 * Hs j ≤ κg * (Jg + 2) ^ 2 * Hs Jg := by
      have ha : (j + 2) ^ 2 ≤ (Jg + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have hb : Hs j ≤ Hs Jg := hHsmono j Jg (by omega)
      calc κg * (j + 2) ^ 2 * Hs j ≤ κg * (Jg + 2) ^ 2 * Hs j :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ha)
        _ ≤ κg * (Jg + 2) ^ 2 * Hs Jg := Nat.mul_le_mul_left _ hb
    have h2 := hcap Cbig (by omega) le_rfl
    have h3 : Wneed ≤ Cbig := by
      rw [hCbig_def]
      omega
    have h4 : max A' NS + Wneed ≤ Cbig * (max A' NS + 1) := by
      have ha : Cbig * (max A' NS + 1) = Cbig * max A' NS + Cbig := by ring
      have hb : max A' NS ≤ Cbig * max A' NS :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    have h5 : 2 * (κg * (Jg + 2) ^ 2 * Hs Jg) + 1 = Wneed := by
      rw [hWneed_def]
    omega
  have hcardSTpos : ∀ j, 0 < cardST j := by
    intro j
    have h1 : 0 < Fintype.card (PatternSpace Kd (Hs j) × ZMod (Ps j)) :=
      Fintype.card_pos
    simp only [hcardST_def]
    exact_mod_cast h1
  have hδgκg : 100 * δ₃ ≤ δg * κg := by
    have hRg0 : (0 : ℝ) < Rg := by linarith
    have h1 : δg * ((10 : ℝ) ^ 23 / ε ^ 4 * Rg) ≤ δg * κg :=
      mul_le_mul_of_nonneg_left hκgR (le_of_lt hδg0)
    have h2 : δg * ((10 : ℝ) ^ 23 / ε ^ 4 * Rg) = 100 * δ₃ := by
      rw [hδg_def]
      field_simp
      ring
    linarith
  have hLf_le_sq : ∀ j, Lf j ≤ (((j + 2) ^ 2 : ℕ) : ℝ) := by
    intro j
    have h2 : (2 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2 ≤ j + 2)
    have hlog : Real.log ((j + 2 : ℕ) : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by
      have := Real.log_le_sub_one_of_pos
        (show (0:ℝ) < ((j + 2 : ℕ) : ℝ) by linarith)
      linarith
    have hcast : (((j + 2) ^ 2 : ℕ) : ℝ) = ((j + 2 : ℕ) : ℝ) ^ 2 := by
      push_cast
      ring
    rw [hcast]
    simp only [hLf_def]
    nlinarith
  have hslack : ∀ j, j < Jg →
      shannonEntropy (residueLaw (Ps j) (max A' NS) B')
          / ((κg * (j + 2) ^ 2 * Hs j : ℕ) : ℝ)
        + decrementErr Kd (Hs j) (Ps j) (max A' NS) B' (κg * (j + 2) ^ 2)
          / ((Hs j : ℕ) : ℝ)
      ≤ δg / (2 * Lf j) := by
    intro j hj
    have hHsR : (0 : ℝ) < ((Hs j : ℕ) : ℝ) := by exact_mod_cast hHspos j
    have hLj := hLf_pos j
    have hkR : (0 : ℝ) < ((κg * (j + 2) ^ 2 : ℕ) : ℝ) := by
      have hpos : 0 < κg * (j + 2) ^ 2 :=
        Nat.mul_pos (by omega) (pow_pos (by omega) 2)
      exact_mod_cast hpos
    have hkHsR : (0 : ℝ) < ((κg * (j + 2) ^ 2 * Hs j : ℕ) : ℝ) := by
      have hpos : 0 < κg * (j + 2) ^ 2 * Hs j :=
        Nat.mul_pos (Nat.mul_pos (by omega) (pow_pos (by omega) 2))
          (hHspos j)
      exact_mod_cast hpos
    -- the residue-entropy part
    have hres : shannonEntropy (residueLaw (Ps j) (max A' NS) B')
        / ((κg * (j + 2) ^ 2 * Hs j : ℕ) : ℝ) ≤ δg / (4 * Lf j) := by
      have h1 : shannonEntropy (residueLaw (Ps j) (max A' NS) B')
          ≤ Real.log ((Ps j : ℕ) : ℝ) :=
        shannonEntropy_residueLaw_le (Ps j) hA''1 hA''B'
      have h2 : Real.log ((Ps j : ℕ) : ℝ)
          ≤ 2 * ((n0s j : ℕ) : ℝ) * Real.log 4 := by
        rw [hPs_coe]
        exact log_prod_primeBlock_le (n0s j)
      have h3 : 2 * ((n0s j : ℕ) : ℝ) * Real.log 4
          ≤ 2 * (δ₃ * ((Hs j : ℕ) : ℝ)) * Real.log 4 := by
        nlinarith only [hn0le j, hlog4]
      have hchain : shannonEntropy (residueLaw (Ps j) (max A' NS) B')
          / ((κg * (j + 2) ^ 2 * Hs j : ℕ) : ℝ)
          ≤ 2 * (δ₃ * ((Hs j : ℕ) : ℝ)) * Real.log 4
            / ((κg * (j + 2) ^ 2 * Hs j : ℕ) : ℝ) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (by linarith only [h1, h2, h3])
          (inv_nonneg.mpr hkHsR.le)
      refine le_trans hchain ?_
      -- `2δ₃·Hs·log4/(κg(j+2)²Hs) ≤ δg/(4Lj)` ⟸ `8δ₃log4·Lj ≤ δg·κg·(j+2)²`
      rw [div_le_div_iff₀ hkHsR (by linarith : (0:ℝ) < 4 * Lf j)]
      have hcast : ((κg * (j + 2) ^ 2 * Hs j : ℕ) : ℝ)
          = ((κg : ℕ) : ℝ) * (((j + 2) ^ 2 : ℕ) : ℝ) * ((Hs j : ℕ) : ℝ) := by
        push_cast
        ring
      rw [hcast]
      have hkey : 8 * δ₃ * Real.log 4 * Lf j
          ≤ δg * (((κg : ℕ) : ℝ) * (((j + 2) ^ 2 : ℕ) : ℝ)) := by
        have hLsq := hLf_le_sq j
        have hκg0 : (1 : ℝ) ≤ ((κg : ℕ) : ℝ) := by exact_mod_cast hκg1
        have h16 : 8 * δ₃ * Real.log 4 ≤ 16 * δ₃ := by
          nlinarith only [hlog4two, hδ₃0, hlog4]
        have h100 : 16 * δ₃ ≤ δg * ((κg : ℕ) : ℝ) := by
          have hδκ := hδgκg
          linarith only [hδκ, hδ₃0]
        have hδκnn : (0:ℝ) ≤ δg * ((κg : ℕ) : ℝ) :=
          mul_nonneg hδg0.le (Nat.cast_nonneg _)
        have s0 : 8 * δ₃ * Real.log 4 * Lf j ≤ 16 * δ₃ * Lf j :=
          mul_le_mul_of_nonneg_right h16 hLj.le
        have s1 : 16 * δ₃ * Lf j ≤ δg * ((κg : ℕ) : ℝ) * Lf j :=
          mul_le_mul_of_nonneg_right h100 hLj.le
        have s2 : δg * ((κg : ℕ) : ℝ) * Lf j
            ≤ δg * ((κg : ℕ) : ℝ) * (((j + 2) ^ 2 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hLsq hδκnn
        calc 8 * δ₃ * Real.log 4 * Lf j
            ≤ δg * ((κg : ℕ) : ℝ) * (((j + 2) ^ 2 : ℕ) : ℝ) := by
              linarith only [s0, s1, s2]
          _ = δg * (((κg : ℕ) : ℝ) * (((j + 2) ^ 2 : ℕ) : ℝ)) := by ring
      have hfin := mul_le_mul_of_nonneg_right hkey hHsR.le
      nlinarith only [hfin]
    -- the decrement-error part
    have hdec : decrementErr Kd (Hs j) (Ps j) (max A' NS) B'
        (κg * (j + 2) ^ 2) / ((Hs j : ℕ) : ℝ) ≤ δg / (4 * Lf j) := by
      have hΛfj := le_trans (hΛtot_f j hj) hlogw
      simp only [hΛf_def] at hΛfj
      have ht1 : 48 * ((κg * (j + 2) ^ 2 : ℕ) : ℝ) * Lf j / (NS * δg)
          ≤ Real.log w := by
        linarith only [hΛfj, hT2nn j, hT3nn j, hT4nn j]
      have ht2 : 6 * ((κg * (j + 2) ^ 2 : ℕ) : ℝ) * ((Hs j : ℕ) : ℝ)
          * (16 * cardST j * Lf j) ^ 2
          / (NS * (δg * ((Hs j : ℕ) : ℝ)) ^ 2) ≤ Real.log w := by
        linarith only [hΛfj, hT1nn j, hT3nn j, hT4nn j]
      have hNS0 : (0:ℝ) < (NS:ℝ) := hNSR0
      have hAS : (NS : ℝ) * (Real.log w / 2)
          ≤ ((max A' NS : ℕ) : ℝ) * S := by
        have h1 : (NS : ℝ) ≤ ((max A' NS : ℕ) : ℝ) := by
          exact_mod_cast hA''NS
        nlinarith only [hS_half, hS_pos, hlogw0, h1, hNS0]
      have hASpos : (0:ℝ) < (NS : ℝ) * (Real.log w / 2) :=
        mul_pos hNS0 (by linarith only [hlogw0])
      have hkHsnn : (0:ℝ) ≤ ((κg * (j + 2) ^ 2 * Hs j : ℕ) : ℝ) :=
        Nat.cast_nonneg _
      have hNSlogw : (0:ℝ) < (NS : ℝ) * Real.log w := mul_pos hNS0 hlogw0
      have hqbound : 3 * ((κg * (j + 2) ^ 2 * Hs j : ℕ) : ℝ)
          / (((max A' NS : ℕ) : ℝ) * S)
          ≤ 6 * ((κg * (j + 2) ^ 2 * Hs j : ℕ) : ℝ)
            / ((NS : ℝ) * Real.log w) := by
        have h1 : 3 * ((κg * (j + 2) ^ 2 * Hs j : ℕ) : ℝ)
            / (((max A' NS : ℕ) : ℝ) * S)
            ≤ 3 * ((κg * (j + 2) ^ 2 * Hs j : ℕ) : ℝ)
              / ((NS : ℝ) * (Real.log w / 2)) :=
          div_le_div_of_nonneg_left
            (by nlinarith only [hkHsnn]) hASpos hAS
        have h2 : 3 * ((κg * (j + 2) ^ 2 * Hs j : ℕ) : ℝ)
            / ((NS : ℝ) * (Real.log w / 2))
            = 6 * ((κg * (j + 2) ^ 2 * Hs j : ℕ) : ℝ)
              / ((NS : ℝ) * Real.log w) := by
          field_simp [ne_of_gt hNS0, ne_of_gt hlogw0]
          ring
        linarith only [h1, h2]
      -- the linear term
      have hlin : 3 * ((κg * (j + 2) ^ 2 * Hs j : ℕ) : ℝ)
          / (((max A' NS : ℕ) : ℝ) * S)
          ≤ δg * ((Hs j : ℕ) : ℝ) / (8 * Lf j) := by
        refine le_trans hqbound ?_
        have hcast : ((κg * (j + 2) ^ 2 * Hs j : ℕ) : ℝ)
            = ((κg * (j + 2) ^ 2 : ℕ) : ℝ) * ((Hs j : ℕ) : ℝ) := by
          push_cast
          ring
        rw [hcast, div_le_div_iff₀ hNSlogw
          (by linarith only [hLj] : (0:ℝ) < 8 * Lf j)]
        -- `6kHs·8Lj ≤ δgHs·NSlogw` ⟸ `48kLj ≤ δg·NS·logw`
        have h1 : 48 * ((κg * (j + 2) ^ 2 : ℕ) : ℝ) * Lf j
            ≤ (NS : ℝ) * δg * Real.log w := by
          have hd := (div_le_iff₀ (mul_pos hNS0 hδg0)).mp ht1
          nlinarith only [hd]
        have h2 := mul_le_mul_of_nonneg_right h1 hHsR.le
        nlinarith only [h2]
      -- the sqrt term
      have hsq : 2 * cardST j
          * Real.sqrt (3 * ((κg * (j + 2) ^ 2 * Hs j : ℕ) : ℝ)
            / (((max A' NS : ℕ) : ℝ) * S))
          ≤ δg * ((Hs j : ℕ) : ℝ) / (8 * Lf j) := by
        have hsqmono : Real.sqrt (3 * ((κg * (j + 2) ^ 2 * Hs j : ℕ) : ℝ)
            / (((max A' NS : ℕ) : ℝ) * S))
            ≤ Real.sqrt (6 * ((κg * (j + 2) ^ 2 * Hs j : ℕ) : ℝ)
              / ((NS : ℝ) * Real.log w)) := Real.sqrt_le_sqrt hqbound
        have htarget : Real.sqrt (6 * ((κg * (j + 2) ^ 2 * Hs j : ℕ) : ℝ)
            / ((NS : ℝ) * Real.log w))
            ≤ δg * ((Hs j : ℕ) : ℝ) / (16 * cardST j * Lf j) := by
          have hden16 : (0:ℝ) < 16 * cardST j * Lf j :=
            mul_pos (mul_pos (by norm_num) (hcardSTpos j)) hLj
          have hrhs0 : (0:ℝ) ≤ δg * ((Hs j : ℕ) : ℝ)
              / (16 * cardST j * Lf j) :=
            div_nonneg (mul_nonneg hδg0.le (Nat.cast_nonneg _)) hden16.le
          rw [show δg * ((Hs j : ℕ) : ℝ) / (16 * cardST j * Lf j)
              = Real.sqrt ((δg * ((Hs j : ℕ) : ℝ)
                / (16 * cardST j * Lf j)) ^ 2) from
            (Real.sqrt_sq hrhs0).symm]
          refine Real.sqrt_le_sqrt ?_
          -- `6kHs/(NSlogw) ≤ (δgHs/(16cardST·Lj))²` ⟸ `ht2`
          have hcST := hcardSTpos j
          have hcast : ((κg * (j + 2) ^ 2 * Hs j : ℕ) : ℝ)
              = ((κg * (j + 2) ^ 2 : ℕ) : ℝ) * ((Hs j : ℕ) : ℝ) := by
            push_cast
            ring
          rw [hcast, div_le_iff₀ hNSlogw, ← sub_nonneg]
          have hexp : (δg * ((Hs j : ℕ) : ℝ) / (16 * cardST j * Lf j)) ^ 2
              * ((NS : ℝ) * Real.log w)
              - 6 * (((κg * (j + 2) ^ 2 : ℕ) : ℝ) * ((Hs j : ℕ) : ℝ))
              = ((δg * ((Hs j : ℕ) : ℝ)) ^ 2 * (NS : ℝ)
                  / (16 * cardST j * Lf j) ^ 2)
                * (Real.log w
                  - 6 * ((κg * (j + 2) ^ 2 : ℕ) : ℝ) * ((Hs j : ℕ) : ℝ)
                    * (16 * cardST j * Lf j) ^ 2
                    / ((NS : ℝ) * (δg * ((Hs j : ℕ) : ℝ)) ^ 2)) := by
            field_simp [ne_of_gt hcST, ne_of_gt hLj, ne_of_gt hNS0,
              ne_of_gt hδg0, ne_of_gt hHsR]
          rw [hexp]
          have hfac : (0:ℝ) ≤ (δg * ((Hs j : ℕ) : ℝ)) ^ 2 * (NS : ℝ)
              / (16 * cardST j * Lf j) ^ 2 :=
            div_nonneg (mul_nonneg (sq_nonneg _) hNS0.le) (sq_nonneg _)
          have hdiff : (0:ℝ) ≤ Real.log w
              - 6 * ((κg * (j + 2) ^ 2 : ℕ) : ℝ) * ((Hs j : ℕ) : ℝ)
                * (16 * cardST j * Lf j) ^ 2
                / ((NS : ℝ) * (δg * ((Hs j : ℕ) : ℝ)) ^ 2) := by
            linarith only [ht2]
          exact mul_nonneg hfac hdiff
        have hcST0 : (0:ℝ) ≤ 2 * cardST j := by
          linarith only [hcardSTpos j]
        calc 2 * cardST j
            * Real.sqrt (3 * ((κg * (j + 2) ^ 2 * Hs j : ℕ) : ℝ)
              / (((max A' NS : ℕ) : ℝ) * S))
            ≤ 2 * cardST j * (δg * ((Hs j : ℕ) : ℝ)
              / (16 * cardST j * Lf j)) :=
              mul_le_mul_of_nonneg_left
                (le_trans hsqmono htarget) hcST0
          _ = δg * ((Hs j : ℕ) : ℝ) / (8 * Lf j) := by
              have hcST := hcardSTpos j
              field_simp [ne_of_gt hcST, ne_of_gt hLj]
              ring
      -- combine and divide by the scale
      have hsum : decrementErr Kd (Hs j) (Ps j) (max A' NS) B'
          (κg * (j + 2) ^ 2) ≤ δg * ((Hs j : ℕ) : ℝ) / (4 * Lf j) := by
        rw [decrementErr, ← hS_def]
        have hfold : ((Fintype.card
            (PatternSpace Kd (Hs j) × ZMod (Ps j)) : ℕ) : ℝ) = cardST j := by
          simp only [hcardST_def]
        rw [hfold]
        have hcomb : δg * ((Hs j : ℕ) : ℝ) / (8 * Lf j)
            + δg * ((Hs j : ℕ) : ℝ) / (8 * Lf j)
            = δg * ((Hs j : ℕ) : ℝ) / (4 * Lf j) := by
          field_simp [ne_of_gt hLj]
          ring
        linarith only [hsq, hlin, hcomb]
      have hLj4 : (0:ℝ) < 4 * Lf j := by linarith
      rw [div_le_div_iff₀ hHsR hLj4]
      have h2 := mul_le_mul_of_nonneg_right hsum hLj4.le
      have heqq : δg * ((Hs j : ℕ) : ℝ) / (4 * Lf j) * (4 * Lf j)
          = δg * ((Hs j : ℕ) : ℝ) := by
        field_simp [ne_of_gt hLj]
      linarith only [h2, heqq.le, heqq.ge]
    have hhalf : δg / (4 * Lf j) + δg / (4 * Lf j) = δg / (2 * Lf j) := by
      field_simp [ne_of_gt hLj]
      ring
    linarith only [hres, hdec, hhalf]
  -- ================= the pigeonholed scale =================
  obtain ⟨j, hjJg, hIraw⟩ := hJgsel g hA''1 hkB hslack
  have hHpj : polyGrid κg H₀ j = Hs j := hHspoly j
  have hIf : mutualInfo (jointLaw g Kd (polyGrid κg H₀ j) (Ps j)
      (max A' NS) B') / ((Hs j : ℕ) : ℝ) < δg / Lf j := by
    simp only [hLf_def]
    exact hIraw
  have hHsR : (0 : ℝ) < ((Hs j : ℕ) : ℝ) := by exact_mod_cast hHspos j
  have hJlR : (0 : ℝ) < ((Jls j : ℕ) : ℝ) := by exact_mod_cast hJlspos j
  have hn0j2 : 2 ≤ n0s j := hn0two j
  have hLj := hLf_pos j
  -- the block data at the pigeonholed scale
  haveI hNZa : ∀ i : ↥(primeBlock (n0s j)), NeZero ((i : ℕ)) := fun i =>
    ⟨(mem_primeBlock i.2).1.pos.ne'⟩
  have hcop := pairwise_coprime_primeBlock (n0s j)
  have hPeq : (∏ i : ↥(primeBlock (n0s j)), (i : ℕ)) = Ps j := by
    rw [hPs_def]
  -- shift-range facts
  have hsJ : ∀ i : ↥(primeBlock (n0s j)), (i : ℕ) * h < Jls j := by
    intro i
    have h1 := (mem_primeBlock i.2).2.2
    have h2 := h4n0hJls j
    have h3 : (i : ℕ) * h ≤ 2 * n0s j * h := Nat.mul_le_mul_right _ h1
    have h4 : 2 * (2 * n0s j * h) = 4 * n0s j * h := by ring
    omega
  have hHfit : ∀ i : ↥(primeBlock (n0s j)), Jls j + (i : ℕ) * h ≤ Hs j := by
    intro i
    have h1 := (mem_primeBlock i.2).2.2
    have h2 := h2n0hHs j
    have h3 : (i : ℕ) * h ≤ 2 * n0s j * h := Nat.mul_le_mul_right _ h1
    have h4 : Jls j = Hs j - 2 * n0s j * h := by
      rw [hJls_def]
    omega
  have hJlsHs : Jls j ≤ Hs j := by
    have h4 : Jls j = Hs j - 2 * n0s j * h := by
      rw [hJls_def]
    have h2 := h2n0hHs j
    omega
  -- the block mass
  have hκval : ∑ i : ↥(primeBlock (n0s j)), (1 : ℝ) / ((i : ℕ) : ℝ)
      ≤ 2 * Real.log 4 / Real.log ((n0s j : ℕ) : ℝ) := by
    have h1 : ∑ i : ↥(primeBlock (n0s j)), (1 : ℝ) / ((i : ℕ) : ℝ)
        = ∑ p ∈ primeBlock (n0s j), (1 : ℝ) / p :=
      sum_primeBlock_coe (fun p => (1 : ℝ) / p)
    rw [h1]
    exact sum_one_div_primeBlock_le hn0j2
  have hκv0 : (0:ℝ) ≤ 2 * Real.log 4 / Real.log ((n0s j : ℕ) : ℝ) := by
    have := hlogn0pos j
    positivity
  -- ================= near-uniformity of the residue law =================
  have hPsPm : Ps j ≤ Pm := hPsub j (le_of_lt hjJg)
  have hPsR : (0:ℝ) < ((Ps j : ℕ) : ℝ) := by
    have := hPs2 j
    exact_mod_cast (by omega : 0 < Ps j)
  have h4P : 4 * Ps j ≤ max A' NS := by
    refine le_trans ?_ hA''NS
    rw [hNS_def]
    omega
  have hPB : Ps j * (max A' NS + 1) ≤ B' := by
    have h1 := hcap Pm (by omega) (by rw [hCbig_def]; omega)
    calc Ps j * (max A' NS + 1) ≤ Pm * (max A' NS + 1) :=
        Nat.mul_le_mul_right _ hPsPm
      _ ≤ B' := h1
  have hunif0 := le_shannonEntropy_residueLaw (P := Ps j)
    (hPs2 j) h4P hPB
  rw [← hS_def] at hunif0
  set θ₀v : ℝ := ((Ps j : ℕ) : ℝ) * ((2 / ((Ps j : ℕ) : ℝ)
    + (2 * Real.log (2 * ((Ps j : ℕ) : ℝ)) + 2) / ((Ps j : ℕ) : ℝ)) / S)
    with hθ₀v_def
  have hPs2R : (2:ℝ) ≤ ((Ps j : ℕ) : ℝ) := by exact_mod_cast hPs2 j
  have hlog2Ps0 : (0:ℝ) ≤ Real.log (2 * ((Ps j : ℕ) : ℝ)) := by
    refine Real.log_nonneg ?_
    linarith only [hPs2R]
  have hθ₀eq : θ₀v = (4 + 2 * Real.log (2 * ((Ps j : ℕ) : ℝ))) / S := by
    rw [hθ₀v_def]
    field_simp
    ring
  have hθ₀0 : 0 ≤ θ₀v := by
    rw [hθ₀eq]
    have h1 : (0:ℝ) ≤ 4 + 2 * Real.log (2 * ((Ps j : ℕ) : ℝ)) := by
      linarith
    exact div_nonneg h1 hS_pos.le
  have hlogPsPm : Real.log (2 * ((Ps j : ℕ) : ℝ)) ≤ Real.log (2 * (Pm : ℝ)) := by
    refine Real.log_le_log (by linarith) ?_
    have : ((Ps j : ℕ) : ℝ) ≤ (Pm : ℝ) := by exact_mod_cast hPsPm
    linarith
  have hθ₀ub : θ₀v ≤ 2 * (4 + 2 * Real.log (2 * (Pm : ℝ))) / Real.log w := by
    rw [hθ₀eq]
    rw [div_le_div_iff₀ hS_pos hlogw0]
    have h1 : (4 + 2 * Real.log (2 * ((Ps j : ℕ) : ℝ))) * Real.log w
        ≤ (4 + 2 * Real.log (2 * (Pm : ℝ))) * Real.log w := by
      have := hlogw0
      nlinarith only [hlogPsPm, hlogw0]
    have h2 : (4 + 2 * Real.log (2 * (Pm : ℝ))) * Real.log w
        ≤ 2 * (4 + 2 * Real.log (2 * (Pm : ℝ))) * S := by
      nlinarith only [hS_half, hlogPm0, hlogw0, hS_pos]
    linarith only [h1, h2]
  have hθ₀1 : θ₀v ≤ 1 := by
    have h1 : 2 * (4 + 2 * Real.log (2 * (Pm : ℝ))) ≤ Real.log w := by
      linarith only [hΛbw', hlog2, hlogNS20, hlogNS10]
    have h2 : 2 * (4 + 2 * Real.log (2 * (Pm : ℝ))) / Real.log w ≤ 1 := by
      rw [div_le_one hlogw0]
      exact h1
    linarith only [hθ₀ub, h2]
  have hθ₀τ' : θ₀v ≤ τ's j * ε / 200000 := by
    have hΛfj := le_trans (hΛtot_f j hjJg) hlogw
    simp only [hΛf_def] at hΛfj
    have ht3 : 2 * (4 + 2 * Real.log (2 * (Pm : ℝ))) * 200000
        / (ε * τ's j) ≤ Real.log w := by
      linarith only [hΛfj, hT1nn j, hT2nn j, hT4nn j]
    have hτ' := hτ's_pos j
    have hden : (0:ℝ) < ε * τ's j := mul_pos hε0 hτ'
    rw [div_le_iff₀ hden] at ht3
    -- θ₀ ≤ 2C/logw and 2C·302000 ≤ logw·ε·τ' ⟹ θ₀ ≤ ε·τ'/302000
    have h1 : 2 * (4 + 2 * Real.log (2 * (Pm : ℝ)))
        ≤ Real.log w * (ε * τ's j) / 200000 := by
      linarith only [ht3]
    have h2 : 2 * (4 + 2 * Real.log (2 * (Pm : ℝ))) / Real.log w
        ≤ (Real.log w * (ε * τ's j) / 200000) / Real.log w := by
      rw [div_eq_mul_inv, div_eq_mul_inv
        (Real.log w * (ε * τ's j) / 200000)]
      exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hlogw0.le)
    have h3 : (Real.log w * (ε * τ's j) / 200000) / Real.log w
        = τ's j * ε / 200000 := by
      field_simp [ne_of_gt hlogw0]
    linarith only [hθ₀ub, h2, h3.le, h3.ge]
  -- ================= the Hoeffding deviation input =================
  set Pprod : ℕ := ∏ i : ↥(primeBlock (n0s j)), (i : ℕ) with hPprod_def
  have hPprodPs : Pprod = Ps j := hPeq
  have hdev : ∀ (φ : ℂ →ₗ[ℝ] ℝ), (∀ z, |φ z| ≤ ‖z‖) →
      ∀ x' : PatternSpace Kd (polyGrid κg H₀ j),
      ((Finset.univ.filter
        (fun y : ZMod Pprod =>
        ts j ≤ |φ (decObs Kd (polyGrid κg H₀ j) (Jls j) h
            (fun i : ↥(primeBlock (n0s j)) => (i : ℕ)) hcop x' y)
          - (∑ y', φ (decObs Kd (polyGrid κg H₀ j) (Jls j) h
              (fun i : ↥(primeBlock (n0s j)) => (i : ℕ)) hcop x' y'))
            / ((Pprod : ℕ) : ℝ)|)).card : ℝ)
        ≤ Real.exp (-(Ds j)) * ((Pprod : ℕ) : ℝ) := by
    intro φ hφ x'
    have hcd := card_deviation_decObs_le Kd (polyGrid κg H₀ j) (Jls j) h
      hKd0 (fun i : ↥(primeBlock (n0s j)) => (i : ℕ)) hcop x' φ hφ
      (hts_pos j).le
    refine le_trans hcd ?_
    have hSig_match : ((∑ i : ↥(primeBlock (n0s j)),
        (((8 * (Jls j / ((i : ℕ)) + 1) : ℕ)) : ℝ≥0) ^ 2 : ℝ≥0) : ℝ)
        = Sigs j := by
      simp only [hSigs_def]
    have hexpeq : 2 * Real.exp (-ts j ^ 2 / (2 * Sigs j))
        = Real.exp (-(Ds j)) := by
      have hDval : Ds j = ts j ^ 2 / (2 * Sigs j) - Real.log 2 := by
        rw [hDs_def]
      rw [hDval,
        show -(ts j ^ 2 / (2 * Sigs j) - Real.log 2)
          = Real.log 2 + -(ts j ^ 2 / (2 * Sigs j)) from by ring,
        Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 2),
        show -ts j ^ 2 / (2 * Sigs j) = -(ts j ^ 2 / (2 * Sigs j)) from by
          ring]
    rw [hSig_match, hexpeq]
  -- ================= the per-frequency swap input =================
  have hJlspoly : Jls j ≤ polyGrid κg H₀ j := by
    rw [hHpj]
    exact hJlsHs
  have hH₀mrJ : H₀mr ≤ Jls j := by
    have h1 := hJlsge j
    have h2 : H₀ ≤ Hs j := hHsge j
    have h3 : 2 * H₀mr ≤ H₀ := by
      rw [hH₀_def]
      omega
    have h4 : (H₀mr : ℝ) ≤ ((Jls j : ℕ) : ℝ) := by
      have h5 : 2 * (H₀mr : ℝ) ≤ ((Hs j : ℕ) : ℝ) := by
        exact_mod_cast le_trans h3 h2
      have h6 : (0:ℝ) ≤ (H₀mr : ℝ) := Nat.cast_nonneg _
      nlinarith only [h1, h5, h6]
    exact_mod_cast h4
  have hlwfold : ∀ n : ℕ, logWeight (max A' NS) B' n = 1 / (n : ℝ) / S := by
    intro n
    rw [logWeight, ← hS_def]
  have hswap : ∀ ξ ∈ Finset.univ.filter (fun ξ : ZMod (Jls j) =>
      θs j ≤ ‖∑ i : ↥(primeBlock (n0s j)), ((1 / ((i : ℕ) : ℝ) : ℝ) : ℂ)
        * zChar ((((i : ℕ) * h : ℕ) : ZMod (Jls j))) ξ‖),
      ∑ x', patternLaw g Kd (polyGrid κg H₀ j) (max A' NS) B' x'
          * ‖zDFT (fun v : ZMod (Jls j) =>
              patExt Kd (polyGrid κg H₀ j) x' v.val) (-ξ)‖
        ≤ 4 / Kd + 2 * εmr := by
    intro ξ hξmem
    have hstep := sum_patternLaw_norm_zDFT_le g huni Kd
      (polyGrid κg H₀ j) (Jls j) hKd0 hJlspoly hA''1 hA''B' ξ
    refine le_trans hstep ?_
    have hMRmass : ∑ n ∈ Finset.Ioc (max A' NS) B',
        logWeight (max A' NS) B' n * ((1 / ((Jls j : ℕ) : ℝ))
          * ‖∑ j' ∈ Finset.Icc 1 (Jls j), g (n + j')
              * Complex.exp (2 * Real.pi * Complex.I * (j' : ℂ)
                * (((ξ.val : ℝ) / ((Jls j : ℕ) : ℝ) : ℝ) : ℂ))‖)
        ≤ 2 * εmr := by
      -- rewrite each summand as `(1/S)·(‖·‖/(Jl·n))`
      have hterm : ∀ n ∈ Finset.Ioc (max A' NS) B',
          logWeight (max A' NS) B' n * ((1 / ((Jls j : ℕ) : ℝ))
            * ‖∑ j' ∈ Finset.Icc 1 (Jls j), g (n + j')
                * Complex.exp (2 * Real.pi * Complex.I * (j' : ℂ)
                  * (((ξ.val : ℝ) / ((Jls j : ℕ) : ℝ) : ℝ) : ℂ))‖)
          = (1 / S) * (‖∑ j' ∈ Finset.Icc 1 (Jls j), g (n + j')
                * Complex.exp (2 * Real.pi * Complex.I * (j' : ℂ)
                  * (((ξ.val : ℝ) / ((Jls j : ℕ) : ℝ) : ℝ) : ℂ))‖
              / (((Jls j : ℕ) : ℝ) * (n : ℝ))) := by
        intro n hn
        rw [hlwfold n]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      -- monotone into the full window, then Matomäki–Radziwiłł
      have hsub : ∑ n ∈ Finset.Ioc (max A' NS) B',
          ‖∑ j' ∈ Finset.Icc 1 (Jls j), g (n + j')
              * Complex.exp (2 * Real.pi * Complex.I * (j' : ℂ)
                * (((ξ.val : ℝ) / ((Jls j : ℕ) : ℝ) : ℝ) : ℂ))‖
            / (((Jls j : ℕ) : ℝ) * (n : ℝ))
          ≤ ∑ n ∈ Finset.Ioc A' B',
            ‖∑ j' ∈ Finset.Icc 1 (Jls j), g (n + j')
                * Complex.exp (2 * Real.pi * Complex.I * (j' : ℂ)
                  * (((ξ.val : ℝ) / ((Jls j : ℕ) : ℝ) : ℝ) : ℂ))‖
              / (((Jls j : ℕ) : ℝ) * (n : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Ioc_subset_Ioc (le_max_left A' NS) le_rfl) ?_
        intro n _ _
        positivity
      -- the filter largeness, bridged to the real additive-character form
      have hξθ : θs j ≤ ‖∑ p ∈ primeBlock (n0s j), ((1 / (p : ℝ) : ℝ) : ℂ)
          * ExpSums.e ((p : ℝ) * ((h : ℝ) * ((ξ.val : ℝ) / ((Jls j : ℕ) : ℝ))))‖ := by
        have hmem' := (Finset.mem_filter.mp hξmem).2
        rw [sum_primeBlock_coe (fun p => ((1 / (p : ℝ) : ℝ) : ℂ)
            * zChar (((p * h : ℕ) : ZMod (Jls j))) ξ),
          primeBlock_zChar_sum_eq (n0s j) h ξ] at hmem'
        exact hmem'
      -- the block-density floor `δ₃/2·J ≤ n₀`
      have hn₀lo : δ₃ / 2 * ((Jls j : ℕ) : ℝ) ≤ ((n0s j : ℕ) : ℝ) := by
        have h1 : δ₃ * ((Hs j : ℕ) : ℝ) - 1 < ((n0s j : ℕ) : ℝ) := by
          simp only [hn0s_def]
          exact Nat.sub_one_lt_floor _
        have h2 := hδ₃Hs j
        have h3 : ((Jls j : ℕ) : ℝ) ≤ ((Hs j : ℕ) : ℝ) := by exact_mod_cast hJlsHs
        have hprod : δ₃ * ((Jls j : ℕ) : ℝ) ≤ δ₃ * ((Hs j : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left h3 hδ₃0.le
        have h230 : (2 : ℝ) ≤ (2 : ℝ) ^ 30 := by norm_num
        linarith
      -- the threshold floor `cθ/log n₀ ≤ θ`
      have hLn0 : Real.log ((n0s j : ℕ) : ℝ) ≠ 0 := (hlogn0pos j).ne'
      have hθc : cθ / Real.log ((n0s j : ℕ) : ℝ) ≤ θs j := by
        have h1 := hms_lb j
        have h3 : θs j = ε * ms j / 256 := by simp only [hθs_def]
        have h4 : ε / 256 * (Real.log 4 / (24 * Real.log ((n0s j : ℕ) : ℝ)))
            ≤ ε / 256 * ms j :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        calc cθ / Real.log ((n0s j : ℕ) : ℝ)
            = ε / 256 * (Real.log 4 / (24 * Real.log ((n0s j : ℕ) : ℝ))) := by
              rw [hcθ_def]
              field_simp
              ring
          _ ≤ ε / 256 * ms j := h4
          _ = ε * ms j / 256 := by ring
          _ = θs j := h3.symm
      have hmr := hA₀f (Jls j) hH₀mrJ A (hAMR_w j hjJg) hA1 x w hAw hwx
        g hcm huni hnp (n0s j) hn₀lo (h4n0hJls j) (θs j) hθc ξ hξθ
      rw [← hA'_def, ← hB'_def] at hmr
      have hchain : ∑ n ∈ Finset.Ioc (max A' NS) B',
          ‖∑ j' ∈ Finset.Icc 1 (Jls j), g (n + j')
              * Complex.exp (2 * Real.pi * Complex.I * (j' : ℂ)
                * (((ξ.val : ℝ) / ((Jls j : ℕ) : ℝ) : ℝ) : ℂ))‖
            / (((Jls j : ℕ) : ℝ) * (n : ℝ))
          ≤ εmr * Real.log w := le_trans hsub hmr
      -- `(1/S)·εmr·logw ≤ 2εmr`
      have hS1 : (1 / S) * (εmr * Real.log w) ≤ 2 * εmr := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hS_pos]
        nlinarith only [hS_half, hεmr0, hlogw0]
      have hsum0 : (0:ℝ) ≤ ∑ n ∈ Finset.Ioc (max A' NS) B',
          ‖∑ j' ∈ Finset.Icc 1 (Jls j), g (n + j')
              * Complex.exp (2 * Real.pi * Complex.I * (j' : ℂ)
                * (((ξ.val : ℝ) / ((Jls j : ℕ) : ℝ) : ℝ) : ℂ))‖
            / (((Jls j : ℕ) : ℝ) * (n : ℝ)) := by
        refine Finset.sum_nonneg fun n _ => ?_
        positivity
      have hS0' : (0:ℝ) ≤ 1 / S := by positivity
      calc (1 / S) * ∑ n ∈ Finset.Ioc (max A' NS) B',
          ‖∑ j' ∈ Finset.Icc 1 (Jls j), g (n + j')
              * Complex.exp (2 * Real.pi * Complex.I * (j' : ℂ)
                * (((ξ.val : ℝ) / ((Jls j : ℕ) : ℝ) : ℝ) : ℂ))‖
            / (((Jls j : ℕ) : ℝ) * (n : ℝ))
          ≤ (1 / S) * (εmr * Real.log w) :=
            mul_le_mul_of_nonneg_left hchain hS0'
        _ ≤ 2 * εmr := hS1
    linarith only [hMRmass]
  -- ================= the M1 upper bound at the scale =================
  set Mv : ℝ := ∑ i : ↥(primeBlock (n0s j)),
    4 * (((Jls j / (i : ℕ) + 1 : ℕ)) : ℝ) with hMv_def
  have hMv0 : 0 ≤ Mv := by
    rw [hMv_def]
    refine Finset.sum_nonneg fun i _ => ?_
    positivity
  set τv : ℝ := ((Hs j : ℕ) : ℝ) * δg / Lf j with hτv_def
  have hIv : mutualInfo (jointLaw g Kd (polyGrid κg H₀ j) (Ps j)
      (max A' NS) B') ≤ τv := by
    have h1 := hIf
    rw [div_lt_iff₀ hHsR] at h1
    rw [hτv_def]
    have heq : δg / Lf j * ((Hs j : ℕ) : ℝ)
        = ((Hs j : ℕ) : ℝ) * δg / Lf j := by ring
    linarith only [h1, heq.le, heq.ge]
  have hτ'θ₀pos : 0 < τ's j + θ₀v := by
    have h1 := hτ's_pos j
    linarith only [h1, hθ₀0]
  have hM1 := norm_sum_jointLaw_decObs_le
    (ι := ↥(primeBlock (n0s j))) g Kd (polyGrid κg H₀ j) (Jls j) h hKd0
    (fun i => (i : ℕ)) hcop hsJ hA''1 hA''B'
    (hθs_pos j).le hκval hκv0 (le_of_eq hMv_def.symm) hMv0
    hθ₀0 hτ'θ₀pos (hts_pos j).le (hDs_pos j) hIv hunif0 hdev hswap
  -- ================= the major-frequency count =================
  have hΞcard : ((Finset.univ.filter (fun ξ : ZMod (Jls j) =>
      θs j ≤ ‖∑ i : ↥(primeBlock (n0s j)), ((1 / ((i : ℕ) : ℝ) : ℝ) : ℂ)
        * zChar ((((i : ℕ) * h : ℕ) : ZMod (Jls j))) ξ‖)).card : ℝ)
      ≤ Ξm := by
    have hfilter_eq : Finset.univ.filter (fun ξ : ZMod (Jls j) =>
        θs j ≤ ‖∑ i : ↥(primeBlock (n0s j)), ((1 / ((i : ℕ) : ℝ) : ℝ) : ℂ)
          * zChar ((((i : ℕ) * h : ℕ) : ZMod (Jls j))) ξ‖)
        = Finset.univ.filter (fun ξ : ZMod (Jls j) =>
          θs j ≤ ‖∑ p ∈ primeBlock (n0s j), ((1 / (p : ℝ) : ℝ) : ℂ)
            * zChar (((p * h : ℕ) : ZMod (Jls j))) ξ‖) := by
      refine Finset.filter_congr fun ξ _ => ?_
      rw [sum_primeBlock_coe (fun p => ((1 / (p : ℝ) : ℝ) : ℂ)
        * zChar (((p * h : ℕ) : ZMod (Jls j))) ξ)]
    rw [hfilter_eq]
    have hcq := hCqb (Jls j) h (n0s j) hn0j2 hh1 (h4n0hJls j)
      (θs j) (hθs_pos j)
    refine le_trans hcq ?_
    -- `Cq·Jl/(n0·log⁴n0·θ⁴) ≤ Ξm` via `θ ≥ ε/(4000·log n0)`, `Jl/n0 ≤ 2/δ₃`
    have hlogn0 := hlogn0pos j
    have hθlb : ε / (6400 * Real.log ((n0s j : ℕ) : ℝ)) ≤ θs j := by
      have h1 := hms_lb j
      have h2 : ε * (Real.log 4 / (24 * Real.log ((n0s j : ℕ) : ℝ))) / 256
          ≤ ε * ms j / 256 := by
        have h2a := mul_le_mul_of_nonneg_left h1 hε0.le
        linarith only [h2a]
      have h3 : ε / (6400 * Real.log ((n0s j : ℕ) : ℝ))
          ≤ ε * (Real.log 4 / (24 * Real.log ((n0s j : ℕ) : ℝ))) / 256 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 256)]
        have hexpand : ε * (Real.log 4
            / (24 * Real.log ((n0s j : ℕ) : ℝ))) * (6400
              * Real.log ((n0s j : ℕ) : ℝ))
            = ε * Real.log 4 * (6400 / 24) := by
          field_simp
        rw [hexpand]
        nlinarith only [hlog4, hε0]
      rw [hθs_def]
      linarith only [h2, h3]
    have hJln0 : ((Jls j : ℕ) : ℝ) / ((n0s j : ℕ) : ℝ) ≤ 2 / δ₃ := by
      have hn0pos : (0 : ℝ) < ((n0s j : ℕ) : ℝ) := by linarith [hn0R j]
      have h3a : ((Jls j : ℕ) : ℝ) / ((n0s j : ℕ) : ℝ)
          ≤ ((Hs j : ℕ) : ℝ) / ((n0s j : ℕ) : ℝ) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (hJlsle j)
          (inv_nonneg.mpr hn0pos.le)
      have h3b : ((Hs j : ℕ) : ℝ) / ((n0s j : ℕ) : ℝ)
          ≤ ((Hs j : ℕ) : ℝ) / (δ₃ * ((Hs j : ℕ) : ℝ) / 2) :=
        div_le_div_of_nonneg_left hHsR.le (by positivity) (hn0ge2 j)
      have h4 : ((Hs j : ℕ) : ℝ) / (δ₃ * ((Hs j : ℕ) : ℝ) / 2) = 2 / δ₃ := by
        field_simp
      linarith only [h3a, h3b, h4.le]
    -- `Cq·Jl/(n0·logn0⁴·θ⁴) ≤ Cq·(Jl/n0)·4000⁴/ε⁴ ≤ Ξm − 1 ≤ Ξm`
    have hθ4 : (ε / (6400 * Real.log ((n0s j : ℕ) : ℝ))) ^ 4 ≤ θs j ^ 4 := by
      have h0 : (0:ℝ) ≤ ε / (6400 * Real.log ((n0s j : ℕ) : ℝ)) := by
        positivity
      exact pow_le_pow_left₀ h0 hθlb 4
    have hθspos := hθs_pos j
    have hn0pos : (0 : ℝ) < ((n0s j : ℕ) : ℝ) := by linarith [hn0R j]
    have hchain : Cq * ((Jls j : ℕ) : ℝ)
        / (((n0s j : ℕ) : ℝ) * Real.log ((n0s j : ℕ) : ℝ) ^ 4 * θs j ^ 4)
        ≤ Cq * ((Jls j : ℕ) : ℝ)
          / (((n0s j : ℕ) : ℝ) * Real.log ((n0s j : ℕ) : ℝ) ^ 4
            * (ε / (6400 * Real.log ((n0s j : ℕ) : ℝ))) ^ 4) := by
      refine div_le_div_of_nonneg_left ?_ ?_ ?_
      · exact mul_nonneg hCq0.le (Nat.cast_nonneg _)
      · have h0 : (0:ℝ) < ε / (6400 * Real.log ((n0s j : ℕ) : ℝ)) := by
          positivity
        positivity
      · refine mul_le_mul_of_nonneg_left hθ4 ?_
        positivity
    refine le_trans hchain ?_
    have hval : Cq * ((Jls j : ℕ) : ℝ)
        / (((n0s j : ℕ) : ℝ) * Real.log ((n0s j : ℕ) : ℝ) ^ 4
          * (ε / (6400 * Real.log ((n0s j : ℕ) : ℝ))) ^ 4)
        = Cq * (((Jls j : ℕ) : ℝ) / ((n0s j : ℕ) : ℝ)) * 6400 ^ 4 / ε ^ 4 := by
      field_simp
    rw [hval]
    
    have hfin : Cq * (((Jls j : ℕ) : ℝ) / ((n0s j : ℕ) : ℝ)) * 6400 ^ 4 / ε ^ 4
        ≤ Cq * (2 / δ₃) * 6400 ^ 4 / ε ^ 4 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : Cq * (((Jls j : ℕ) : ℝ) / ((n0s j : ℕ) : ℝ)) * 6400 ^ 4
          ≤ Cq * (2 / δ₃) * 6400 ^ 4 := by
        have h2 := mul_le_mul_of_nonneg_left hJln0 hCq0.le
        nlinarith only [h2]
      nlinarith only [h1, sq_nonneg ε, pow_pos hε0 4]
    refine le_trans hfin ?_
    have hΞval : Cq * (2 / δ₃) * 6400 ^ 4 / ε ^ 4 = Ξm - 1 := by
      rw [hΞm_def]
      field_simp
      ring
    linarith only [hΞval.le]
  -- ================= the bridge and Proposition `conv` =================
  have hHfit' : ∀ i : ↥(primeBlock (n0s j)),
      Jls j + (i : ℕ) * h ≤ polyGrid κg H₀ j := by
    intro i
    rw [hHpj]
    exact hHfit i
  have hBr := norm_sum_jointLaw_decObs_sub_le' g huni Kd (polyGrid κg H₀ j)
    (Jls j) h hKd0 (fun i : ↥(primeBlock (n0s j)) => (i : ℕ)) hcop hHfit'
    hA''1 hA''B'
  rw [← hS_def] at hBr
  beta_reduce at hBr hM1
  -- normalize the bridge into `‖T‖ ≤ S(‖E‖ + Br)`
  have hTup : ∀ (E T : ℂ) (Br : ℝ),
      ‖E - 1 / ((S : ℝ) : ℂ) * T‖ ≤ Br → ‖T‖ ≤ S * (‖E‖ + Br) := by
    intro E T Br hd
    have h1 : ‖1 / ((S : ℝ) : ℂ) * T‖ = ‖T‖ / S := by
      rw [norm_mul, norm_div, norm_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hS_pos]
      ring
    have h2 := norm_sub_norm_le (1 / ((S : ℝ) : ℂ) * T) E
    rw [norm_sub_rev, h1] at h2
    have h3 : ‖T‖ / S ≤ ‖E‖ + Br := by linarith only [h2, hd]
    have h4 : ‖T‖ / S * S = ‖T‖ := by
      field_simp
    calc ‖T‖ = ‖T‖ / S * S := h4.symm
      _ ≤ (‖E‖ + Br) * S := mul_le_mul_of_nonneg_right h3 hS_pos.le
      _ = S * (‖E‖ + Br) := by ring
  have hT := hTup _ _ _ hBr
  -- Proposition `conv` at the scale
  have h2n0A : 2 * n0s j ≤ max A' NS := by
    have h1 : n0s j ≤ n0m := hn0mub j (le_of_lt hjJg)
    refine le_trans ?_ hA''NS
    rw [hNS_def]
    have h2 := hn0mPm
    omega
  have h2n0B : 2 * n0s j * max A' NS ≤ B' := by
    have h1 : n0s j ≤ n0m := hn0mub j (le_of_lt hjJg)
    have h2 := hcap (2 * n0m) (by omega) (by rw [hCbig_def]; omega)
    have h3 : 2 * n0s j * max A' NS ≤ 2 * n0m * (max A' NS + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hPC := prop_conv hcm huni (n₀ := n0s j) (h := h) (J := Jls j)
    (A := max A' NS) (B := B') (hn0ge j) h2n0A h2n0B hS₀
  -- the sum dictionary: `prop_conv`'s block sum is the bridge's subtype sum
  have hTdict : (∑ p ∈ (2 * n0s j + 1).primesBelow.filter
        (fun p => n0s j < p),
      ∑ j' ∈ Finset.Icc 1 (Jls j), ∑ n ∈ Finset.Ioc (max A' NS) B',
        (if (n + j') % p = 0
          then g (n + j') * (starRingEnd ℂ) (g (n + j' + p * h)) else 0)
          / (n : ℂ))
      = ∑ i : ↥(primeBlock (n0s j)),
        ∑ j' ∈ Finset.Icc 1 (Jls j), ∑ n ∈ Finset.Ioc (max A' NS) B',
          (if (n + j') % (i : ℕ) = 0
            then g (n + j') * (starRingEnd ℂ)
              (g (n + j' + (i : ℕ) * h)) else 0) / (n : ℂ) := by
    rw [show (2 * n0s j + 1).primesBelow.filter (fun p => n0s j < p)
        = primeBlock (n0s j) from rfl]
    exact (sum_primeBlock_coe (fun p =>
      ∑ j' ∈ Finset.Icc 1 (Jls j), ∑ n ∈ Finset.Ioc (max A' NS) B',
        (if (n + j') % p = 0
          then g (n + j') * (starRingEnd ℂ) (g (n + j' + p * h)) else 0)
          / (n : ℂ))).symm
  rw [hTdict] at hPC
  -- fold the mass constant
  have hmsfold : Real.log 4 / 12 / Real.log (2 * ((n0s j : ℕ) : ℝ)) = ms j := by
    simp only [hms_def]
  rw [hmsfold] at hPC
  -- ================= the budget ledger =================
  have hJlms_pos : (0:ℝ) < ((Jls j : ℕ) : ℝ) * ms j :=
    mul_pos hJlR (hms_pos j)
  have hlogn0 := hlogn0pos j
  have hJlms_lb : ((Hs j : ℕ) : ℝ) * Real.log 4
      / (32 * Real.log ((n0s j : ℕ) : ℝ)) ≤ ((Jls j : ℕ) : ℝ) * ms j := by
    have h1 := hJlsge j
    have h2 := hms_lb j
    have h3 : (3 * ((Hs j : ℕ) : ℝ) / 4)
        * (Real.log 4 / (24 * Real.log ((n0s j : ℕ) : ℝ)))
        ≤ ((Jls j : ℕ) : ℝ) * ms j :=
      mul_le_mul h1 h2 (by positivity) (Nat.cast_nonneg _)
    have heq : (3 * ((Hs j : ℕ) : ℝ) / 4)
        * (Real.log 4 / (24 * Real.log ((n0s j : ℕ) : ℝ)))
        = ((Hs j : ℕ) : ℝ) * Real.log 4
          / (32 * Real.log ((n0s j : ℕ) : ℝ)) := by
      field_simp
      ring
    linarith only [h3, heq.le, heq.ge]
  have hκms : 2 * Real.log 4 / Real.log ((n0s j : ℕ) : ℝ) ≤ 48 * ms j := by
    have h1 := hms_lb j
    have heq : 48 * (Real.log 4 / (24 * Real.log ((n0s j : ℕ) : ℝ)))
        = 2 * Real.log 4 / Real.log ((n0s j : ℕ) : ℝ) := by
      field_simp
      ring
    linarith only [mul_le_mul_of_nonneg_left h1
      (by norm_num : (0:ℝ) ≤ 48), heq.le, heq.ge]
  have hcard_ub : ((Fintype.card ↥(primeBlock (n0s j))) : ℝ)
      ≤ 64 * δ₃ * (((Jls j : ℕ) : ℝ) * ms j) := by
    have h1 : ((Fintype.card ↥(primeBlock (n0s j))) : ℝ)
        = ((primeBlock (n0s j)).card : ℝ) := by
      rw [Fintype.card_coe]
    rw [h1]
    have h2 := card_primeBlock_le hn0j2
    have h3 : 2 * ((n0s j : ℕ) : ℝ) * Real.log 4
        / Real.log ((n0s j : ℕ) : ℝ)
        ≤ 2 * (δ₃ * ((Hs j : ℕ) : ℝ)) * Real.log 4
          / Real.log ((n0s j : ℕ) : ℝ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr hlogn0.le)
      nlinarith only [hn0le j, hlog4]
    have h4 : 2 * (δ₃ * ((Hs j : ℕ) : ℝ)) * Real.log 4
        / Real.log ((n0s j : ℕ) : ℝ)
        = 64 * δ₃ * (((Hs j : ℕ) : ℝ) * Real.log 4
          / (32 * Real.log ((n0s j : ℕ) : ℝ))) := by
      field_simp
      ring
    have h5 : 64 * δ₃ * (((Hs j : ℕ) : ℝ) * Real.log 4
        / (32 * Real.log ((n0s j : ℕ) : ℝ)))
        ≤ 64 * δ₃ * (((Jls j : ℕ) : ℝ) * ms j) :=
      mul_le_mul_of_nonneg_left hJlms_lb (by positivity)
    linarith only [h2, h3, h4.le, h4.ge, h5]
  have hMv_ub : Mv ≤ 193 * (((Jls j : ℕ) : ℝ) * ms j) := by
    have hper : ∀ i : ↥(primeBlock (n0s j)),
        4 * (((Jls j / (i : ℕ) + 1 : ℕ)) : ℝ)
        ≤ 4 * (((Jls j : ℕ) : ℝ) * (1 / ((i : ℕ) : ℝ)) + 1) := by
      intro i
      have h1 : (((Jls j / (i : ℕ) : ℕ)) : ℝ)
          ≤ ((Jls j : ℕ) : ℝ) / ((i : ℕ) : ℝ) := Nat.cast_div_le
      have h2 : (((Jls j / (i : ℕ) + 1 : ℕ)) : ℝ)
          = (((Jls j / (i : ℕ) : ℕ)) : ℝ) + 1 := by push_cast; ring
      rw [h2]
      have h3 : ((Jls j : ℕ) : ℝ) / ((i : ℕ) : ℝ)
          = ((Jls j : ℕ) : ℝ) * (1 / ((i : ℕ) : ℝ)) := by ring
      nlinarith only [h1, h3.le, h3.ge]
    have hsum : Mv ≤ ∑ i : ↥(primeBlock (n0s j)),
        4 * (((Jls j : ℕ) : ℝ) * (1 / ((i : ℕ) : ℝ)) + 1) := by
      rw [hMv_def]
      exact Finset.sum_le_sum fun i _ => hper i
    have hsplit4 : ∀ i : ↥(primeBlock (n0s j)),
        4 * (((Jls j : ℕ) : ℝ) * (1 / ((i : ℕ) : ℝ)) + 1)
        = 4 * ((Jls j : ℕ) : ℝ) * (1 / ((i : ℕ) : ℝ)) + 4 := by
      intro i
      ring
    have hexpand : ∑ i : ↥(primeBlock (n0s j)),
        4 * (((Jls j : ℕ) : ℝ) * (1 / ((i : ℕ) : ℝ)) + 1)
        = 4 * ((Jls j : ℕ) : ℝ)
            * (∑ i : ↥(primeBlock (n0s j)), (1 : ℝ) / ((i : ℕ) : ℝ))
          + 4 * ((Fintype.card ↥(primeBlock (n0s j))) : ℝ) := by
      rw [Finset.sum_congr rfl fun i _ => hsplit4 i, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]
      ring
    have hmass : 4 * ((Jls j : ℕ) : ℝ)
        * (∑ i : ↥(primeBlock (n0s j)), (1 : ℝ) / ((i : ℕ) : ℝ))
        ≤ 4 * ((Jls j : ℕ) : ℝ)
          * (2 * Real.log 4 / Real.log ((n0s j : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hκval (by positivity)
    have hκpart : 4 * ((Jls j : ℕ) : ℝ)
        * (2 * Real.log 4 / Real.log ((n0s j : ℕ) : ℝ))
        ≤ 4 * ((Jls j : ℕ) : ℝ) * (48 * ms j) :=
      mul_le_mul_of_nonneg_left hκms (by positivity)
    have hδ₃small : 256 * δ₃ ≤ 1 := by
      rw [hδ₃_def]
      have hb : 256 * (ε / (100000 * (h : ℝ)))
          = 256 * ε / (100000 * (h : ℝ)) := by ring
      rw [hb, div_le_one (by linarith only [hhR1] : (0:ℝ) < 100000 * (h : ℝ))]
      linarith only [hε1, hhR1]
    have hcardpart : 4 * ((Fintype.card ↥(primeBlock (n0s j))) : ℝ)
        ≤ (((Jls j : ℕ) : ℝ) * ms j) := by
      have h1 := hcard_ub
      have h2 : 4 * (64 * δ₃ * (((Jls j : ℕ) : ℝ) * ms j))
          = 256 * δ₃ * (((Jls j : ℕ) : ℝ) * ms j) := by ring
      nlinarith only [h1, h2.le, h2.ge, hδ₃small, hJlms_pos]
    nlinarith only [hsum, hexpand.le, hexpand.ge, hmass, hκpart, hcardpart,
      hJlms_pos]
  -- ================= the final contradiction =================
  -- the remaining schedule equations, restated at the pigeonholed scale
  have htseq : ts j = ((Jls j : ℕ) : ℝ) * ms j * ε / 64 := by rw [hts_def]
  have hθseq : θs j = ε * ms j / 256 := by rw [hθs_def]
  have hτ'eq : τ's j = ε * Ds j / 200000 := by rw [hτ's_def]
  have hMv4 : Mv = 4 * ∑ i : ↥(primeBlock (n0s j)),
      ((Jls j / (i : ℕ) + 1 : ℕ) : ℝ) := by
    rw [hMv_def, Finset.mul_sum]
  -- the grid-log bound: the scale logarithm is within the ratio budget
  have hlgn0Rg : Real.log ((n0s j : ℕ) : ℝ) ≤ Rg * Lf j := by
    have h1 : Real.log ((n0s j : ℕ) : ℝ) ≤ Real.log ((Hs j : ℕ) : ℝ) := by
      refine Real.log_le_log (by linarith [hn0R j]) ?_
      nlinarith only [hn0le j, hδ₃1, hHsR]
    have h2 : Real.log ((Hs j : ℕ) : ℝ)
        ≤ (Real.log H₀ / (2 * Real.log 2) + Real.log κg / Real.log 2 + 2)
          * (((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ)) := by
      rw [← hHpj]
      exact log_polyGrid_le hκg1 hH₀1 j
    have h3 : (Real.log H₀ / (2 * Real.log 2) + Real.log κg / Real.log 2 + 2)
        * (((j + 2 : ℕ) : ℝ) * Real.log ((j + 2 : ℕ) : ℝ)) = Rg * Lf j := by
      rw [hRg_def, hLf_def]
      ring
    linarith only [h1, h2, h3.le, h3.ge]
  -- the window-floor comparison and the log budget
  have hE1eq : E1f j = 3 * ((Jls j : ℕ) : ℝ) ^ 2 * ((n0s j : ℕ) : ℝ) / NS
      + ((Jls j : ℕ) : ℝ) * (2 * Real.log (2 * ((n0s j : ℕ) : ℝ)) + 2) := by
    rw [hE1f_def]
  have hNSAmax : ((NS : ℕ) : ℝ) ≤ ((max A' NS : ℕ) : ℝ) := by
    exact_mod_cast hA''NS
  have hlNSle : Real.log ((NS : ℕ) : ℝ) ≤ Real.log ((NS + 2 : ℕ) : ℝ) := by
    refine Real.log_le_log ?_ ?_
    · exact_mod_cast (by omega : 0 < NS)
    · exact_mod_cast (by omega : NS ≤ NS + 2)
  have hΛfj := le_trans (hΛtot_f j hjJg) hlogw
  simp only [hΛf_def] at hΛfj
  have hbud : 4 * (Real.log ((NS + 2 : ℕ) : ℝ) + 1
      + E1f j / (((Jls j : ℕ) : ℝ) * ms j)) / ε ≤ Real.log w := by
    linarith only [hΛfj, hT1nn j, hT2nn j, hT3nn j]
  -- the budget arithmetic refutes the ledger
  exact elliott_master_arith hε0 hε1 hlogw1 hPC hT hM1 hS_pos hS_2logw
    hJlR (hms_pos j) htseq hθseq hκms hMv4 hMv0 hMv_ub hcard_ub hhR1 hδ₃0
    hδ₃h (Nat.cast_nonneg _) hΞcard hΞm1 (by exact_mod_cast hKd0) hKdR
    hεmr_def hτ'eq (hτ's_pos j) hθ₀0 hθ₀τ' (hDs_pos j) (hDs_min j) hτv_def
    hδg_def hRg2 (hLf_pos j) hHsR (hlogn0pos j) hlgn0Rg (hDs_lb j) hE1eq
    hNSR0 hNSAmax (Nat.cast_nonneg _) hlNSle hbud

/-- **The Elliott master theorem** (arXiv:1509.05422, Theorem `elliott-red`,
ordered-shift form): the nonasymptotic log-averaged conjugate-pair bound,
derived from the Matomäki–Radziwiłł and prime-quadruple-sieve interfaces by
the entropy-decrement contradiction. -/
theorem elliott_master [MatomakiRadziwillAssumption]
    [PrimeQuadrupleCountAssumption]
    (b₁ b₂ : ℕ) (hb : b₁ < b₂) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A → 1 ≤ A →
      ∀ x w : ℝ, A ≤ w → w ≤ x →
        ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → Unimodular g →
          NonPretentiousAt g A ⌈x⌉₊ →
          ‖∑ n ∈ Finset.Ioc ⌊x / w⌋₊ ⌊x⌋₊,
              g (n + b₁) * (starRingEnd ℂ) (g (n + b₂)) / (n : ℂ)‖
            ≤ ε * Real.log w :=
  elliott_master_of_filtered filteredMR_of_allAlpha b₁ b₂ hb hε0 hε1

/-- **The Elliott master theorem on the Track R weak pair** (issue #3044): the
same bound with the all-`α` Matomäki–Radziwiłł interface replaced by its
major-arc form composed with the Vinogradov prime-block classification. -/
theorem elliott_master_majorArc [MatomakiRadziwillMajorArcAssumption]
    [PrimeBlockMajorArcAssumption] [PrimeQuadrupleCountAssumption]
    (b₁ b₂ : ℕ) (hb : b₁ < b₂) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A → 1 ≤ A →
      ∀ x w : ℝ, A ≤ w → w ≤ x →
        ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → Unimodular g →
          NonPretentiousAt g A ⌈x⌉₊ →
          ‖∑ n ∈ Finset.Ioc ⌊x / w⌋₊ ⌊x⌋₊,
              g (n + b₁) * (starRingEnd ℂ) (g (n + b₂)) / (n : ℂ)‖
            ≤ ε * Real.log w :=
  elliott_master_of_filtered filteredMR_of_majorArc b₁ b₂ hb hε0 hε1

/-- The master theorem for an arbitrary pair of distinct shifts: the `b₁ > b₂`
case follows from the ordered case by conjugation symmetry of the pair sum. -/
theorem elliott_master_ne [MatomakiRadziwillAssumption]
    [PrimeQuadrupleCountAssumption]
    (b₁ b₂ : ℕ) (hb : b₁ ≠ b₂) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A → 1 ≤ A →
      ∀ x w : ℝ, A ≤ w → w ≤ x →
        ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → Unimodular g →
          NonPretentiousAt g A ⌈x⌉₊ →
          ‖∑ n ∈ Finset.Ioc ⌊x / w⌋₊ ⌊x⌋₊,
              g (n + b₁) * (starRingEnd ℂ) (g (n + b₂)) / (n : ℂ)‖
            ≤ ε * Real.log w := by
  rcases Nat.lt_or_ge b₁ b₂ with hlt | hge
  · exact elliott_master b₁ b₂ hlt hε0 hε1
  · have hgt : b₂ < b₁ := by omega
    obtain ⟨A₀, hA₀⟩ := elliott_master b₂ b₁ hgt hε0 hε1
    refine ⟨A₀, fun A hA hA1 x w hAw hwx g hcm huni hnp => ?_⟩
    rw [norm_pair_sum_conj_symm]
    exact hA₀ A hA hA1 x w hAw hwx g hcm huni hnp

/-- **The Elliott interface is discharged** (issue #2946, M3): the
nonasymptotic log-averaged Elliott estimate holds conditional on exactly the
Matomäki–Radziwiłł and prime-quadruple-sieve interfaces — the entropy-decrement
argument of arXiv:1509.05422 §3, machine-checked. The `ε > 1` regime is
absorbed by monotonicity of the bound in `ε`. -/
instance logElliottNonasymptotic_of_matomakiRadziwill_quadrupleSieve
    [MatomakiRadziwillAssumption] [PrimeQuadrupleCountAssumption] :
    LogElliottNonasymptoticAssumption := by
  refine ⟨fun b₁ b₂ hb ε hε0 => ?_⟩
  rcases le_or_gt ε 1 with hε1 | hε1
  · exact elliott_master_ne b₁ b₂ hb hε0 hε1
  · obtain ⟨A₀, hA₀⟩ := elliott_master_ne b₁ b₂ hb one_pos le_rfl
    refine ⟨A₀, fun A hA hA1 x w hAw hwx g hcm huni hnp => ?_⟩
    have h1 := hA₀ A hA hA1 x w hAw hwx g hcm huni hnp
    have hlw0 : 0 ≤ Real.log w := Real.log_nonneg (le_trans hA1 hAw)
    nlinarith only [h1, hlw0, hε1]

end Master

end Tao2015

end MoltResearch
