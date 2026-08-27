import MoltResearch.Discrepancy.SmoothRankin
import MoltResearch.Discrepancy.HalaszTriple

/-!
# Track C: the §4 pairing chain at an abstract main factor (Track R, M0R-4)

The GHS §4 pairing estimate, re-plumbed so the main factor need not be
a finite Dirichlet polynomial (campaign #3044, M0R-4a).

`pairing_halasz_sqrt_le` is already abstract in its three factors; what
ties the assembled chain (`ghs_pairing_estimate` and its descendants)
to `ghsMainPoly f S` — a *finite* partial sum — is only the discharge
of its side conditions:

* the integrability package uses `continuous_ghsMainPoly`, and
* the tail estimate prices the main factor at its trivial sup
  `norm_ghsMainPoly_le = ∑_{n ∈ S} 1/n`.

Both uses are parametric in nothing but *continuity* and a *global
bound*.  This file re-states the two side-condition lemmas for an
abstract main factor `G : ℝ → ℂ` with hypotheses `Continuous G` and
`∀ ξ, ‖G ξ‖ ≤ Gmax` — the shape the `x`-smooth phase *tsum* (the
truncated Euler product `F_x(1 + 2πiξ)` of `HalaszTriple`) satisfies
with `Gmax` the smooth mass `∑'_{n x-smooth} 1/n`.

That swap is the point of the M0R campaign: the band sup of the smooth
tsum is `e⁵·(2+log x)·e^{−A}` by
`norm_phase_euler_prod_le_of_nonPretentious`, log-free at a single
scale, where the finite polynomial's band sup could only be reached
through the lossy smooth-restriction detour.
-/

namespace MoltResearch

open MeasureTheory Real Complex Finset in
/-- **§4's side conditions at an abstract main factor** (Track R,
M0R-4a): for a continuous `G` bounded by `Gmax` and a continuous window
with `0 ≤ w ≤ C/(1+ξ²)`, every integrability hypothesis of
`pairing_halasz_sqrt_le` holds with `G` in the main-factor slot.

`ghs_pairing_integrability` with `ghsMainPoly f S` replaced by `G`:
the finite polynomial entered that proof only through its continuity
and its trivial sup, so the same script discharges the package from
the two abstract hypotheses.  This is what lets the main factor be an
infinite object — the `x`-smooth phase tsum — rather than a partial
sum. -/
theorem ghs_pairing_integrability_G (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x : ℕ) (P Q : Finset ℕ) (G : ℝ → ℂ) (Gmax : ℝ)
    (hGc : Continuous G) (hGb : ∀ ξ, ‖G ξ‖ ≤ Gmax)
    (w : ℝ → ℝ) (hw : Continuous w) (C : ℝ)
    (hw0 : ∀ ξ, 0 ≤ w ξ) (hwle : ∀ ξ, w ξ ≤ C/(1+ξ^2)) :
    Integrable (fun ξ => ‖G ξ * ghsBlockPoly f x P ξ
          * ghsPrimePoly f Q ξ‖ * w ξ)
      ∧ Integrable (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ)
      ∧ Integrable (fun ξ => ‖ghsPrimePoly f Q ξ‖^2 * w ξ
          * ‖G ξ‖^2)
      ∧ (∀ a b : ℝ, IntervalIntegrable
          (fun t => ‖ghsPrimePoly f Q t‖^2 * w t * ‖G t‖^2)
          volume a b)
      ∧ (∀ a b : ℝ, IntervalIntegrable
          (fun t => (‖ghsPrimePoly f Q t‖^2/(1+t^2)) * ‖G t‖^2)
          volume a b)
      ∧ (∀ a b : ℝ, IntervalIntegrable
          (fun t => ‖ghsPrimePoly f Q t‖^2/(1+t^2)) volume a b)
      ∧ (∀ a b : ℝ, IntervalIntegrable
          (fun t => ‖ghsPrimePoly f Q t‖^2) volume a b) := by
  classical
  -- the two trivial sups
  set S₂ : ℝ := ∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|)
    with hS₂_def
  set S₃ : ℝ := ∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ) with hS₃_def
  have hb₂ : ∀ ξ, ‖ghsBlockPoly f x P ξ‖ ≤ S₂ := norm_ghsBlockPoly_le f hf x P
  have hb₃ : ∀ ξ, ‖ghsPrimePoly f Q ξ‖ ≤ S₃ := norm_ghsPrimePoly_le f hf Q
  have hG0 : (0:ℝ) ≤ Gmax := le_trans (norm_nonneg _) (hGb 0)
  have hS₂0 : (0:ℝ) ≤ S₂ := le_trans (norm_nonneg _) (hb₂ 0)
  have hS₃0 : (0:ℝ) ≤ S₃ := le_trans (norm_nonneg _) (hb₃ 0)
  -- continuity of the three factors
  have hc₁ : Continuous (fun ξ => ‖G ξ‖) := hGc.norm
  have hc₂ : Continuous (fun ξ => ‖ghsBlockPoly f x P ξ‖) :=
    (continuous_ghsBlockPoly f x P).norm
  have hc₃ : Continuous (fun ξ => ‖ghsPrimePoly f Q ξ‖) :=
    (continuous_ghsPrimePoly f Q).norm
  have hden : Continuous (fun t : ℝ => 1 + t^2) := by continuity
  have hden0 : ∀ t : ℝ, (1:ℝ) + t^2 ≠ 0 := fun t => by positivity
  -- `hg0`
  have hg0 : Integrable (fun ξ => ‖G ξ * ghsBlockPoly f x P ξ
      * ghsPrimePoly f Q ξ‖ * w ξ) := by
    have hcont : Continuous (fun ξ => ‖G ξ
        * ghsBlockPoly f x P ξ * ghsPrimePoly f Q ξ‖ * w ξ) :=
      ((hGc.mul (continuous_ghsBlockPoly f x P)).mul
        (continuous_ghsPrimePoly f Q)).norm.mul hw
    have hnn : ∀ ξ, (0:ℝ) ≤ ‖G ξ * ghsBlockPoly f x P ξ
        * ghsPrimePoly f Q ξ‖ * w ξ :=
      fun ξ => mul_nonneg (norm_nonneg _) (hw0 ξ)
    have hdom : ∀ ξ, ‖G ξ * ghsBlockPoly f x P ξ
        * ghsPrimePoly f Q ξ‖ * w ξ ≤ (Gmax*S₂*S₃*C)/(1+ξ^2) := by
      intro ξ
      rw [norm_mul, norm_mul]
      have hprod : ‖G ξ‖ * ‖ghsBlockPoly f x P ξ‖
          * ‖ghsPrimePoly f Q ξ‖ ≤ Gmax * S₂ * S₃ := by
        gcongr <;> [exact hGb ξ; exact hb₂ ξ; exact hb₃ ξ]
      have h1 : ‖G ξ‖ * ‖ghsBlockPoly f x P ξ‖
          * ‖ghsPrimePoly f Q ξ‖ * w ξ ≤ (Gmax*S₂*S₃) * w ξ :=
        mul_le_mul_of_nonneg_right hprod (hw0 ξ)
      have h2 : (Gmax*S₂*S₃) * w ξ ≤ (Gmax*S₂*S₃) * (C/(1+ξ^2)) :=
        mul_le_mul_of_nonneg_left (hwle ξ) (by positivity)
      have h3 : (Gmax*S₂*S₃) * (C/(1+ξ^2)) = (Gmax*S₂*S₃*C)/(1+ξ^2) := by
        ring
      linarith [h1, h2, h3.le, h3.ge]
    exact (integrable_of_le_const_div_one_add_sq _ hcont hnn _ hdom).1
  -- `hg1`
  have hg1 : Integrable (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ) := by
    have hcont : Continuous (fun ξ => ‖ghsBlockPoly f x P ξ‖^2 * w ξ) :=
      (hc₂.pow 2).mul hw
    have hnn : ∀ ξ, (0:ℝ) ≤ ‖ghsBlockPoly f x P ξ‖^2 * w ξ :=
      fun ξ => mul_nonneg (by positivity) (hw0 ξ)
    have hdom : ∀ ξ, ‖ghsBlockPoly f x P ξ‖^2 * w ξ ≤ (S₂^2*C)/(1+ξ^2) := by
      intro ξ
      have hsq : ‖ghsBlockPoly f x P ξ‖^2 ≤ S₂^2 := by
        nlinarith [norm_nonneg (ghsBlockPoly f x P ξ), hb₂ ξ, hS₂0]
      have h1 : ‖ghsBlockPoly f x P ξ‖^2 * w ξ ≤ S₂^2 * w ξ :=
        mul_le_mul_of_nonneg_right hsq (hw0 ξ)
      have h2 : S₂^2 * w ξ ≤ S₂^2 * (C/(1+ξ^2)) :=
        mul_le_mul_of_nonneg_left (hwle ξ) (sq_nonneg S₂)
      have h3 : S₂^2 * (C/(1+ξ^2)) = (S₂^2*C)/(1+ξ^2) := by ring
      linarith [h1, h2, h3.le, h3.ge]
    exact (integrable_of_le_const_div_one_add_sq _ hcont hnn _ hdom).1
  -- `hg2`
  have hg2 : Integrable (fun ξ => ‖ghsPrimePoly f Q ξ‖^2 * w ξ
      * ‖G ξ‖^2) := by
    have hcont : Continuous (fun ξ => ‖ghsPrimePoly f Q ξ‖^2 * w ξ
        * ‖G ξ‖^2) := ((hc₃.pow 2).mul hw).mul (hc₁.pow 2)
    have hnn : ∀ ξ, (0:ℝ) ≤ ‖ghsPrimePoly f Q ξ‖^2 * w ξ
        * ‖G ξ‖^2 :=
      fun ξ => mul_nonneg (mul_nonneg (by positivity) (hw0 ξ)) (by positivity)
    have hdom : ∀ ξ, ‖ghsPrimePoly f Q ξ‖^2 * w ξ * ‖G ξ‖^2
        ≤ (S₃^2*Gmax^2*C)/(1+ξ^2) := by
      intro ξ
      have hsq₃ : ‖ghsPrimePoly f Q ξ‖^2 ≤ S₃^2 := by
        nlinarith [norm_nonneg (ghsPrimePoly f Q ξ), hb₃ ξ, hS₃0]
      have hsq₁ : ‖G ξ‖^2 ≤ Gmax^2 := by
        nlinarith [norm_nonneg (G ξ), hGb ξ, hG0]
      have hw' : w ξ ≤ C/(1+ξ^2) := hwle ξ
      have hn₁ : (0:ℝ) ≤ ‖G ξ‖^2 := by positivity
      have hCq : (0:ℝ) ≤ C/(1+ξ^2) := le_trans (hw0 ξ) hw'
      -- peel the factors one at a time; `nlinarith` will not do a triple
      have hstep : ‖ghsPrimePoly f Q ξ‖^2 * w ξ ≤ S₃^2 * (C/(1+ξ^2)) :=
        le_trans (mul_le_mul_of_nonneg_right hsq₃ (hw0 ξ))
          (mul_le_mul_of_nonneg_left hw' (sq_nonneg S₃))
      have h1 : ‖ghsPrimePoly f Q ξ‖^2 * w ξ * ‖G ξ‖^2
          ≤ S₃^2 * (C/(1+ξ^2)) * Gmax^2 :=
        le_trans (mul_le_mul_of_nonneg_right hstep hn₁)
          (mul_le_mul_of_nonneg_left hsq₁ (by positivity))
      have h3 : S₃^2 * (C/(1+ξ^2)) * Gmax^2 = (S₃^2*Gmax^2*C)/(1+ξ^2) := by
        ring
      linarith [h1, h3.le, h3.ge]
    exact (integrable_of_le_const_div_one_add_sq _ hcont hnn _ hdom).1
  -- the interval conditions: continuity is enough
  refine ⟨hg0, hg1, hg2, fun a b => ?_, fun a b => ?_, fun a b => ?_,
    fun a b => ?_⟩
  · exact (((hc₃.pow 2).mul hw).mul (hc₁.pow 2)).intervalIntegrable a b
  · exact (((hc₃.pow 2).div hden hden0).mul (hc₁.pow 2)).intervalIntegrable a b
  · exact ((hc₃.pow 2).div hden hden0).intervalIntegrable a b
  · exact (hc₃.pow 2).intervalIntegrable a b

open MeasureTheory Real Complex Finset in
/-- **§4's `Mtail` at an abstract main factor** (Track R, M0R-4a): on
any set, the pairing tail is the window's mass there, priced at the
prime-polynomial sup and the main factor's global bound —

  `∫_{ξ ∈ s} ‖P₃‖²·w·‖G‖² ≤ (∑_q log q/q)²·Gmax²·Wtail`

whenever `∫_{ξ ∈ s} w ≤ Wtail`.

`ghs_pairing_tail_le` with the trivial sup `∑_{n ∈ S} 1/n` replaced by
the abstract bound `Gmax`: beyond the band no cancellation is
available, so both factors are discarded against their sups and the
window's tail mass pays for everything.  For the `x`-smooth phase tsum
the price is the smooth mass `∑'_{n x-smooth} 1/n ≍ log x` — the same
size the finite polynomial's sup had, so the tail budget is
unchanged. -/
theorem ghs_pairing_tail_le_G (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x : ℕ) (P Q : Finset ℕ) (G : ℝ → ℂ) (Gmax : ℝ)
    (hGc : Continuous G) (hGb : ∀ ξ, ‖G ξ‖ ≤ Gmax)
    (w : ℝ → ℝ) (hw : Continuous w) (C : ℝ)
    (hw0 : ∀ ξ, 0 ≤ w ξ) (hwle : ∀ ξ, w ξ ≤ C/(1+ξ^2))
    (s : Set ℝ) (Wtail : ℝ) (hWtail : (∫ ξ in s, w ξ) ≤ Wtail) :
    (∫ ξ in s, ‖ghsPrimePoly f Q ξ‖^2 * w ξ * ‖G ξ‖^2)
      ≤ (∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ))^2 * Gmax^2 * Wtail := by
  classical
  set S₃ : ℝ := ∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ) with hS₃_def
  have hb₃ : ∀ ξ, ‖ghsPrimePoly f Q ξ‖ ≤ S₃ := norm_ghsPrimePoly_le f hf Q
  have hG0 : (0:ℝ) ≤ Gmax := le_trans (norm_nonneg _) (hGb 0)
  have hS₃0 : (0:ℝ) ≤ S₃ := le_trans (norm_nonneg _) (hb₃ 0)
  obtain ⟨-, -, hg2, -, -, -, -⟩ :=
    ghs_pairing_integrability_G f hf x P Q G Gmax hGc hGb w hw C hw0 hwle
  obtain ⟨-, -, honw⟩ :=
    integrable_of_le_const_div_one_add_sq w hw hw0 C hwle
  -- discard both factors against their sups
  have hpt : ∀ ξ, ‖ghsPrimePoly f Q ξ‖^2 * w ξ * ‖G ξ‖^2
      ≤ (S₃^2 * Gmax^2) * w ξ := by
    intro ξ
    have hsq₃ : ‖ghsPrimePoly f Q ξ‖^2 ≤ S₃^2 := by
      nlinarith [norm_nonneg (ghsPrimePoly f Q ξ), hb₃ ξ, hS₃0]
    have hsq₁ : ‖G ξ‖^2 ≤ Gmax^2 := by
      nlinarith [norm_nonneg (G ξ), hGb ξ, hG0]
    have hn₁ : (0:ℝ) ≤ ‖G ξ‖^2 := by positivity
    -- peel one factor at a time
    have hstep : ‖ghsPrimePoly f Q ξ‖^2 * w ξ ≤ (S₃^2) * w ξ :=
      mul_le_mul_of_nonneg_right hsq₃ (hw0 ξ)
    have h1 : ‖ghsPrimePoly f Q ξ‖^2 * w ξ * ‖G ξ‖^2
        ≤ (S₃^2 * w ξ) * Gmax^2 :=
      le_trans (mul_le_mul_of_nonneg_right hstep hn₁)
        (mul_le_mul_of_nonneg_left hsq₁ (mul_nonneg (sq_nonneg S₃) (hw0 ξ)))
    have h2 : (S₃^2 * w ξ) * Gmax^2 = (S₃^2 * Gmax^2) * w ξ := by ring
    linarith [h1, h2.le, h2.ge]
  have hmono : (∫ ξ in s, ‖ghsPrimePoly f Q ξ‖^2 * w ξ
        * ‖G ξ‖^2)
      ≤ ∫ ξ in s, (S₃^2 * Gmax^2) * w ξ :=
    MeasureTheory.setIntegral_mono hg2.integrableOn
      ((honw s).const_mul _) hpt
  refine le_trans hmono ?_
  rw [MeasureTheory.integral_const_mul]
  exact mul_le_mul_of_nonneg_left hWtail (by positivity)

end MoltResearch
