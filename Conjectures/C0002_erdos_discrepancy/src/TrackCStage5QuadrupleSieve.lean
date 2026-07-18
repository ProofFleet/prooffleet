import MoltResearch.Discrepancy
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5Elliott

/-!
# Track C: Stage 5 — the prime-quadruple sieve interface (E6f of issue #2946)

The **second permanent analytic input** of the Elliott campaign, alongside
Matomäki–Radziwiłł: the count of additive prime quadruples in a dyadic block,

  `#{(p₁,p₂,p₃,p₄) ∈ 𝒫(n₀)⁴ : p₁ + p₂ = p₃ + p₄} ≪ n₀³ / (log n₀)⁴`,

where `𝒫(n₀)` is the block of primes in `(n₀, 2n₀]`. The paper (arXiv:1509.05422,
proof of the restriction lemma, footnote) obtains this from a standard upper-bound
sieve (Selberg), or alternatively from the Green–Tao restriction estimate
[gt-selberg, Prop. 4.2]; either route is a cited input exactly like the
Matomäki–Radziwiłł theorem itself. Mathlib's `NumberTheory.SelbergSieve` provides
the sieve framework from which this count should eventually be dischargeable.

Through the `L⁴` identity and Markov (`sum_normPow4_zCharSum`,
`card_filter_le_sum_normPow4`), this bound makes the major-frequency set of the
circle method `H`-independent — which is what lets the Matomäki–Radziwiłł
smallness (fixed before the scale is chosen) win.

No instance of this class is (or may be) declared until the count is actually
formalized; consumers carry it as a hypothesis.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The block of primes in `(n₀, 2n₀]`. -/
noncomputable def primeBlock (n₀ : ℕ) : Finset ℕ :=
  (2 * n₀ + 1).primesBelow.filter (fun p => n₀ < p)

/-- **Prime-quadruple sieve assumption** (arXiv:1509.05422 §3, restriction lemma
footnote; [gt-selberg, Prop. 4.2]): the additive-quadruple count in a dyadic
prime block saves four logarithms. -/
class PrimeQuadrupleCountAssumption : Prop where
  bound : ∃ C : ℝ, 0 < C ∧ ∀ n₀ : ℕ, 2 ≤ n₀ →
    (((((primeBlock n₀ ×ˢ primeBlock n₀) ×ˢ
        (primeBlock n₀ ×ˢ primeBlock n₀)).filter
      (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)).card : ℝ)
      ≤ C * n₀ ^ 3 / Real.log n₀ ^ 4)

/-- Consumer-facing restatement. -/
theorem primeQuadrupleCount_bound [inst : PrimeQuadrupleCountAssumption] :
    ∃ C : ℝ, 0 < C ∧ ∀ n₀ : ℕ, 2 ≤ n₀ →
      (((((primeBlock n₀ ×ˢ primeBlock n₀) ×ˢ
          (primeBlock n₀ ×ˢ primeBlock n₀)).filter
        (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)).card : ℝ)
        ≤ C * n₀ ^ 3 / Real.log n₀ ^ 4) :=
  inst.bound

open scoped NNReal in
/-- **The major-frequency count is `H`-independent** (the restriction lemma of
arXiv:1509.05422 §3): through the `L⁴` identity, wrap control, and the
quadruple-sieve input, the set of frequencies where the block exponential sum
`S(ξ) = ∑_{p ∈ 𝒫(n₀)} e(phξ/H)/p` exceeds `θ` has size `≤ C·H/(n₀·log⁴n₀·θ⁴)`.
With `θ ~ ε²/log H` and `n₀ ~ ε²H` this is `O_ε((log H/log n₀)⁴) = O_ε(1)`. -/
theorem card_major_le [inst : PrimeQuadrupleCountAssumption] :
    ∃ C : ℝ, 0 < C ∧ ∀ (H h n₀ : ℕ) [NeZero H], 2 ≤ n₀ → 1 ≤ h →
      4 * n₀ * h < H → ∀ θ : ℝ, 0 < θ →
      ((Finset.univ.filter (fun ξ : ZMod H =>
          θ ≤ ‖∑ p ∈ primeBlock n₀, ((1 / (p : ℝ) : ℝ) : ℂ)
            * zChar ((p * h : ℕ) : ZMod H) ξ‖)).card : ℝ)
        ≤ C * H / ((n₀ : ℝ) * Real.log n₀ ^ 4 * θ ^ 4) := by
  obtain ⟨C, hC0, hCbound⟩ := inst.bound
  refine ⟨C, hC0, ?_⟩
  intro H h n₀ _ hn₀ hh hHn θ hθ
  classical
  have hblock : ∀ p ∈ primeBlock n₀, n₀ < p ∧ p ≤ 2 * n₀ := by
    intro p hp
    rw [primeBlock, Finset.mem_filter] at hp
    exact ⟨hp.2, by have := Nat.lt_of_mem_primesBelow hp.1; omega⟩
  have hn₀R : (0 : ℝ) < (n₀ : ℝ) := by exact_mod_cast (by omega : 0 < n₀)
  have hlogn₀ : (0 : ℝ) < Real.log n₀ :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n₀))
  -- the L⁴ identity with the concrete block data
  have hL4 := sum_normPow4_zCharSum (H := H) (primeBlock n₀)
    (fun p => 1 / (p : ℝ)) (fun p => ((p * h : ℕ) : ZMod H))
  -- bound the quadruple weights and convert the congruence to equality
  have hterm : ∀ x ∈ primeBlock n₀ ×ˢ primeBlock n₀,
      ∀ y ∈ primeBlock n₀ ×ˢ primeBlock n₀,
      (if ((x.1 * h : ℕ) : ZMod H) + ((x.2 * h : ℕ) : ZMod H)
          = ((y.1 * h : ℕ) : ZMod H) + ((y.2 * h : ℕ) : ZMod H)
        then 1 / (x.1 : ℝ) * (1 / (x.2 : ℝ)) * (1 / (y.1 : ℝ))
          * (1 / (y.2 : ℝ)) else 0)
      ≤ (if x.1 + x.2 = y.1 + y.2 then ((n₀ : ℝ))⁻¹ ^ 4 else 0) := by
    intro x hx y hy
    rw [Finset.mem_product] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    have hb1 := hblock _ hx1
    have hb2 := hblock _ hx2
    have hb3 := hblock _ hy1
    have hb4 := hblock _ hy2
    have hiff := zmod_shift_congr_iff (H := H) hh hb1.2 hb2.2 hb3.2 hb4.2 hHn
    by_cases hcond : x.1 + x.2 = y.1 + y.2
    · rw [if_pos (hiff.mpr hcond), if_pos hcond]
      have hle : ∀ p : ℕ, n₀ < p → 1 / (p : ℝ) ≤ ((n₀ : ℝ))⁻¹ := by
        intro p hp
        rw [inv_eq_one_div]
        exact one_div_le_one_div_of_le hn₀R (by exact_mod_cast hp.le)
      have h1 := hle _ hb1.1
      have h2 := hle _ hb2.1
      have h3 := hle _ hb3.1
      have h4 := hle _ hb4.1
      have hpos : ∀ p : ℕ, n₀ < p → (0 : ℝ) ≤ 1 / (p : ℝ) := fun p hp => by
        positivity
      calc 1 / (x.1 : ℝ) * (1 / (x.2 : ℝ)) * (1 / (y.1 : ℝ)) * (1 / (y.2 : ℝ))
          ≤ ((n₀ : ℝ))⁻¹ * ((n₀ : ℝ))⁻¹ * ((n₀ : ℝ))⁻¹ * ((n₀ : ℝ))⁻¹ := by
            have i0 : (0 : ℝ) ≤ ((n₀ : ℝ))⁻¹ := by positivity
            gcongr
        _ = ((n₀ : ℝ))⁻¹ ^ 4 := by ring
    · rw [if_neg (fun hc => hcond (hiff.mp hc)), if_neg hcond]
  have hquad : ∑ x ∈ primeBlock n₀ ×ˢ primeBlock n₀,
      ∑ y ∈ primeBlock n₀ ×ˢ primeBlock n₀,
        (if x.1 + x.2 = y.1 + y.2 then ((n₀ : ℝ))⁻¹ ^ 4 else 0)
      = ((n₀ : ℝ))⁻¹ ^ 4
        * ((((primeBlock n₀ ×ˢ primeBlock n₀) ×ˢ
            (primeBlock n₀ ×ˢ primeBlock n₀)).filter
          (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)).card : ℝ) := by
    rw [← Finset.sum_product']
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  have hchain : ∑ ξ : ZMod H, ‖∑ p ∈ primeBlock n₀,
      ((1 / (p : ℝ) : ℝ) : ℂ) * zChar ((p * h : ℕ) : ZMod H) ξ‖ ^ 4
      ≤ (H : ℝ) * (((n₀ : ℝ))⁻¹ ^ 4
        * (C * n₀ ^ 3 / Real.log n₀ ^ 4)) := by
    rw [hL4]
    have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
    refine mul_le_mul_of_nonneg_left ?_ hH0
    calc ∑ x ∈ primeBlock n₀ ×ˢ primeBlock n₀,
        ∑ y ∈ primeBlock n₀ ×ˢ primeBlock n₀,
          (if ((x.1 * h : ℕ) : ZMod H) + ((x.2 * h : ℕ) : ZMod H)
              = ((y.1 * h : ℕ) : ZMod H) + ((y.2 * h : ℕ) : ZMod H)
            then 1 / (x.1 : ℝ) * (1 / (x.2 : ℝ)) * (1 / (y.1 : ℝ))
              * (1 / (y.2 : ℝ)) else 0)
        ≤ ∑ x ∈ primeBlock n₀ ×ˢ primeBlock n₀,
            ∑ y ∈ primeBlock n₀ ×ˢ primeBlock n₀,
              (if x.1 + x.2 = y.1 + y.2 then ((n₀ : ℝ))⁻¹ ^ 4 else 0) :=
          Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy =>
            hterm x hx y hy
      _ = ((n₀ : ℝ))⁻¹ ^ 4
          * ((((primeBlock n₀ ×ˢ primeBlock n₀) ×ˢ
              (primeBlock n₀ ×ˢ primeBlock n₀)).filter
            (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)).card : ℝ) := hquad
      _ ≤ ((n₀ : ℝ))⁻¹ ^ 4 * (C * n₀ ^ 3 / Real.log n₀ ^ 4) := by
          refine mul_le_mul_of_nonneg_left (hCbound n₀ hn₀) (by positivity)
  have hmarkov := card_filter_le_sum_normPow4 (H := H) (primeBlock n₀)
    (fun p => 1 / (p : ℝ)) (fun p => ((p * h : ℕ) : ZMod H)) hθ
  have hcomb := le_trans hmarkov hchain
  rw [le_div_iff₀ (by positivity)]
  calc ((Finset.univ.filter (fun ξ : ZMod H =>
      θ ≤ ‖∑ p ∈ primeBlock n₀, ((1 / (p : ℝ) : ℝ) : ℂ)
        * zChar ((p * h : ℕ) : ZMod H) ξ‖)).card : ℝ)
      * ((n₀ : ℝ) * Real.log n₀ ^ 4 * θ ^ 4)
      = (((Finset.univ.filter (fun ξ : ZMod H =>
          θ ≤ ‖∑ p ∈ primeBlock n₀, ((1 / (p : ℝ) : ℝ) : ℂ)
            * zChar ((p * h : ℕ) : ZMod H) ξ‖)).card : ℝ) * θ ^ 4)
        * ((n₀ : ℝ) * Real.log n₀ ^ 4) := by ring
    _ ≤ ((H : ℝ) * (((n₀ : ℝ))⁻¹ ^ 4 * (C * n₀ ^ 3 / Real.log n₀ ^ 4)))
        * ((n₀ : ℝ) * Real.log n₀ ^ 4) :=
        mul_le_mul_of_nonneg_right hcomb (by positivity)
    _ = C * H := by
        field_simp

end Tao2015

end MoltResearch
