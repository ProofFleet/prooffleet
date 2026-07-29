import MoltResearch.Discrepancy
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5MatomakiRadziwillMajorArc
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5PrimeBlockMajorArc

/-!
# Track C: Stage 5 — the filtered Matomäki–Radziwiłł bound (R1 of issue #3044)

The composition of the two Track R interfaces, packaged in the exact shape the
`elliott_master` chain consumes: for a modulation frequency `ξ/H` at which the
`h`-dilated prime-block exponential sum is `θ`-large (the consumer's circle-method
filter), the log-averaged short-interval bound of Proposition `mrp` holds.

Derivation: the `zChar` filter condition is rewritten as a real exponential sum at
frequency `β = h·(ξ.val/H)` (lemma `zChar_natCast_eq_e`); the classification
interface (`PrimeBlockMajorArcAssumption`) places `β` in a major arc; the arc is
transported from `β` to `α = ξ.val/H` (`majorArc_of_mul`) and its parameters
converted from the block scale `n₀` to the interval scale `H` using `n₀ ≤ H` and
`δ₀·H ≤ n₀`; finally the major-arc interface
(`MatomakiRadziwillMajorArcAssumption`) is applied at arc constants
`C' = C·h·(1 + 1/δ₀)`, `B` — fixed before `H₀` is chosen, so the load-bearing
`H`-before-`A` quantifier order survives the composition.

Consumers instantiate `δ₀ := δ₃/2` (the block-density floor of the entropy
decrement argument) and `c := ε·log 4/6144`-type threshold coefficients (from
`hms_lb`); this replaces the all-`α` `MatomakiRadziwillAssumption` at the single
use-site of the Elliott chain (unit R1.3b).
-/

namespace MoltResearch

namespace Tao2015

open Finset ExpSums

/-- **The `zChar`/`e` bridge**: the circle-method character at a natural-number
point is the real additive character at the rational frequency `ξ.val/H`. -/
theorem zChar_natCast_eq_e {H : ℕ} [NeZero H] (m : ℕ) (ξ : ZMod H) :
    zChar (m : ZMod H) ξ = e ((m : ℝ) * ((ξ.val : ℝ) / (H : ℝ))) := by
  have h1 : (m : ZMod H) * ξ = ((m * ξ.val : ℕ) : ZMod H) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [zChar, h1, ZMod.stdAddChar_apply, ZMod.toCircle_natCast, e]
  exact congrArg Complex.exp (by push_cast; ring_nf)

/-- **The filtered Matomäki–Radziwiłł bound**: on the consumer's `θ`-large
frequency set, the `mrp` bound follows from the major-arc interface composed with
the Vinogradov classification.  Stated in the exact shape of the use-site in
`elliott_master` (frequency `ξ.val/H`, filter over the `h`-dilated prime block at
scale `n₀`, thresholds `δ₀·H ≤ n₀ < H/(4h)` and `c/log n₀ ≤ θ`). -/
theorem matomakiRadziwill_filtered_bound
    [MatomakiRadziwillMajorArcAssumption] [PrimeBlockMajorArcAssumption]
    {ε c δ₀ : ℝ} (h : ℕ) (hε : 0 < ε) (hc : 0 < c) (hδ₀ : 0 < δ₀) (hh : 1 ≤ h) :
    ∃ H₀ : ℕ, ∀ H : ℕ, H₀ ≤ H → ∀ [NeZero H],
      ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A → 1 ≤ A →
        ∀ x w : ℝ, A ≤ w → w ≤ x →
          ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → Unimodular g →
            NonPretentiousAt g A ⌈x⌉₊ →
            ∀ n₀ : ℕ, δ₀ * (H : ℝ) ≤ (n₀ : ℝ) → 4 * n₀ * h < H →
              ∀ θ : ℝ, c / Real.log n₀ ≤ θ →
                ∀ ξ : ZMod H,
                  θ ≤ ‖∑ p ∈ primeBlock n₀, ((1 / (p : ℝ) : ℝ) : ℂ)
                      * zChar ((p * h : ℕ) : ZMod H) ξ‖ →
                  ∑ n ∈ Finset.Ioc ⌊x / w⌋₊ ⌊x⌋₊,
                      ‖∑ j ∈ Finset.Icc 1 H,
                          g (n + j) * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ)
                            * (((ξ.val : ℝ) / (H : ℝ) : ℝ) : ℂ))‖
                        / ((H : ℝ) * (n : ℝ))
                    ≤ ε * Real.log w := by
  classical
  -- the classification data, fixed before any scale is chosen
  obtain ⟨N₀, B, C, hC0, hclass⟩ := primeBlockMajorArc_bound hc
  set C' : ℝ := C * (h : ℝ) * (1 + 1 / δ₀) with hC'_def
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hC'0 : 0 < C' := by
    rw [hC'_def]
    have : (0 : ℝ) < 1 + 1 / δ₀ := by positivity
    positivity
  -- the major-arc interface at the composed arc constants
  obtain ⟨H₀w, hW⟩ := matomakiRadziwillMajorArc_bound (C := C') B hε hC'0
  -- the scale threshold absorbing the classification floor
  set N₁ : ℕ := max N₀ 2 with hN₁_def
  refine ⟨max H₀w (⌈(N₁ : ℝ) / δ₀⌉₊ + 1), fun H hH _ => ?_⟩
  have hHw : H₀w ≤ H := le_trans (le_max_left _ _) hH
  obtain ⟨A₀, hA₀⟩ := hW H hHw
  refine ⟨A₀, fun A hA hA1 x w hAw hwx g hcm huni hnp n₀ hn₀lo hn₀hi θ hθlo ξ hξ => ?_⟩
  -- scale bookkeeping: `N₁ ≤ n₀ ≤ H` and positivity
  have hHN₁ : (N₁ : ℝ) ≤ δ₀ * (H : ℝ) := by
    have h1 : (⌈(N₁ : ℝ) / δ₀⌉₊ + 1 : ℕ) ≤ H := le_trans (le_max_right _ _) hH
    have h2 : (N₁ : ℝ) / δ₀ ≤ (⌈(N₁ : ℝ) / δ₀⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : ((⌈(N₁ : ℝ) / δ₀⌉₊ : ℕ) : ℝ) + 1 ≤ (H : ℝ) := by exact_mod_cast h1
    have h4 : (N₁ : ℝ) / δ₀ ≤ (H : ℝ) := by linarith
    calc (N₁ : ℝ) = (N₁ : ℝ) / δ₀ * δ₀ := (div_mul_cancel₀ _ (ne_of_gt hδ₀)).symm
      _ ≤ (H : ℝ) * δ₀ := mul_le_mul_of_nonneg_right h4 hδ₀.le
      _ = δ₀ * (H : ℝ) := mul_comm _ _
  have hn₀N₁ : N₁ ≤ n₀ := by
    have : (N₁ : ℝ) ≤ (n₀ : ℝ) := le_trans hHN₁ hn₀lo
    exact_mod_cast this
  have hn₀N₀ : N₀ ≤ n₀ := le_trans (le_max_left _ _) hn₀N₁
  have hn₀2 : 2 ≤ n₀ := le_trans (le_max_right _ _) hn₀N₁
  have hn₀H : n₀ ≤ H := by
    have h1 : n₀ * 1 ≤ n₀ * h := Nat.mul_le_mul_left _ hh
    have h2 : 4 * n₀ * h = 4 * (n₀ * h) := by ring_nf
    omega
  have hn₀R : (0 : ℝ) < (n₀ : ℝ) := by exact_mod_cast (by omega : 0 < n₀)
  have hHR : (0 : ℝ) < (H : ℝ) := by
    have : 0 < H := by omega
    exact_mod_cast this
  have hlogn₀ : (0 : ℝ) < Real.log n₀ :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n₀))
  have hlogH : Real.log n₀ ≤ Real.log H :=
    Real.log_le_log hn₀R (by exact_mod_cast hn₀H)
  have hlogH0 : (0 : ℝ) < Real.log H := lt_of_lt_of_le hlogn₀ hlogH
  have hpow : Real.log n₀ ^ B ≤ Real.log H ^ B :=
    pow_le_pow_left₀ hlogn₀.le hlogH B
  -- the filter condition as a real exponential sum at frequency `β = h·(ξ.val/H)`
  set α : ℝ := (ξ.val : ℝ) / (H : ℝ) with hα_def
  have hbridge : ∑ p ∈ primeBlock n₀, ((1 / (p : ℝ) : ℝ) : ℂ)
      * zChar ((p * h : ℕ) : ZMod H) ξ
      = ∑ p ∈ primeBlock n₀, ((1 / (p : ℝ) : ℝ) : ℂ)
        * e ((p : ℝ) * ((h : ℝ) * α)) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [zChar_natCast_eq_e (p * h) ξ]
    congr 1
    rw [hα_def]
    push_cast
    ring_nf
  rw [hbridge] at hξ
  -- classification of the dilated frequency, then arc transport to `α`
  obtain ⟨a, q, hq1, hqB, harc⟩ := hclass n₀ hn₀N₀ ((h : ℝ) * α) θ hθlo hξ
  obtain ⟨a', q', hq'1, hq'eq, harc'⟩ := majorArc_of_mul hq1 hh harc
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hq'0 : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast hq'1
  have hq'cast : (q' : ℝ) = (q : ℝ) * (h : ℝ) := by
    rw [hq'eq]; push_cast; ring_nf
  -- arc-format conversion from block scale to interval scale
  have hCC' : C * (h : ℝ) ≤ C' ∧ C / δ₀ ≤ C' := by
    constructor
    · rw [hC'_def]
      have h1 : (1 : ℝ) ≤ 1 + 1 / δ₀ := by
        have : (0 : ℝ) < 1 / δ₀ := by positivity
        linarith
      nlinarith [mul_pos hC0 hh0]
    · rw [hC'_def]
      have h1 : 1 / δ₀ ≤ (h : ℝ) * (1 + 1 / δ₀) := by
        have h2 : (1 : ℝ) * (1 / δ₀) ≤ (h : ℝ) * (1 + 1 / δ₀) := by
          have : (0 : ℝ) < 1 / δ₀ := by positivity
          have hle : (1 : ℝ) / δ₀ ≤ 1 + 1 / δ₀ := by linarith
          calc (1 : ℝ) * (1 / δ₀) = 1 / δ₀ := one_mul _
            _ ≤ 1 + 1 / δ₀ := hle
            _ = 1 * (1 + 1 / δ₀) := (one_mul _).symm
            _ ≤ (h : ℝ) * (1 + 1 / δ₀) := by
                have : (0 : ℝ) < 1 + 1 / δ₀ := by positivity
                exact mul_le_mul_of_nonneg_right (by exact_mod_cast hh) this.le
        linarith [h2]
      rw [div_eq_mul_one_div]
      calc C * (1 / δ₀) ≤ C * ((h : ℝ) * (1 + 1 / δ₀)) :=
            mul_le_mul_of_nonneg_left h1 hC0.le
        _ = C * (h : ℝ) * (1 + 1 / δ₀) := by ring_nf
  have hq'B : (q' : ℝ) ≤ C' * Real.log H ^ B := by
    rw [hq'cast]
    calc (q : ℝ) * (h : ℝ) ≤ (C * Real.log n₀ ^ B) * (h : ℝ) :=
          mul_le_mul_of_nonneg_right hqB hh0.le
      _ = (C * (h : ℝ)) * Real.log n₀ ^ B := by ring_nf
      _ ≤ C' * Real.log H ^ B := by
          have h1 := hCC'.1
          have h2 : (0 : ℝ) ≤ Real.log n₀ ^ B := by positivity
          nlinarith [pow_nonneg hlogn₀.le B, hpow, hC'0]
  have hwidth : |α - (a' : ℝ) / (q' : ℝ)| ≤ C' * Real.log H ^ B / ((H : ℝ) * (q' : ℝ)) := by
    refine harc'.trans ?_
    have hw1 : C * Real.log n₀ ^ B / ((n₀ : ℝ) * (q : ℝ)) / (h : ℝ)
        = C * Real.log n₀ ^ B / ((n₀ : ℝ) * (q' : ℝ)) := by
      rw [hq'cast, div_div, mul_assoc]
    rw [hw1]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hkey : C * (H : ℝ) ≤ C' * (n₀ : ℝ) := by
      have h1 : C * (H : ℝ) = (C / δ₀) * (δ₀ * (H : ℝ)) := by
        rw [div_mul_eq_mul_div, mul_comm δ₀ (H : ℝ), ← mul_assoc,
          mul_div_assoc, div_self (ne_of_gt hδ₀), mul_one]
      calc C * (H : ℝ) = (C / δ₀) * (δ₀ * (H : ℝ)) := h1
        _ ≤ (C / δ₀) * (n₀ : ℝ) :=
            mul_le_mul_of_nonneg_left hn₀lo (by positivity)
        _ ≤ C' * (n₀ : ℝ) := mul_le_mul_of_nonneg_right hCC'.2 hn₀R.le
    have hpow0 : (0 : ℝ) ≤ Real.log n₀ ^ B := by positivity
    calc C * Real.log n₀ ^ B * ((H : ℝ) * (q' : ℝ))
        = (C * (H : ℝ)) * (Real.log n₀ ^ B * (q' : ℝ)) := by ring_nf
      _ ≤ (C' * (n₀ : ℝ)) * (Real.log n₀ ^ B * (q' : ℝ)) :=
          mul_le_mul_of_nonneg_right hkey (by positivity)
      _ ≤ (C' * (n₀ : ℝ)) * (Real.log H ^ B * (q' : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hpow hq'0.le) (by positivity)
      _ = C' * Real.log H ^ B * ((n₀ : ℝ) * (q' : ℝ)) := by ring_nf
  -- the major-arc Matomäki–Radziwiłł bound at the transported arc
  exact hA₀ A hA hA1 x w hAw hwx g hcm huni hnp α a' q' hq'1 hq'B hwidth

end Tao2015

end MoltResearch
