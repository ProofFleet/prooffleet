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

open MeasureTheory Real Complex Finset in
/-- **§4's pairing estimate at an abstract main factor** (Track R,
M0R-4a): for a continuous main factor `G` bounded by `Gmax`, the block
and prime polynomials, and any continuous window with
`0 ≤ w ≤ C/(1+t²)`,

  `∫_ℝ ‖G·P₂·P₃‖·w ≤ √(E₁·(5·C·V·L(x)² + Mtail))`.

`ghs_pairing_estimate` with the main-factor slot abstracted: the
integrability package comes from `ghs_pairing_integrability_G` and the
tail from `ghs_pairing_tail_le_G`, so only the four estimates survive —
`hE₁`, `hB`, `hV`, and the window's tail mass, the last now priced at
`Gmax` instead of the finite polynomial's trivial sup. -/
theorem ghs_pairing_estimate_G (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x : ℕ) (P Q : Finset ℕ) (G : ℝ → ℂ) (Gmax : ℝ)
    (hGc : Continuous G) (hGb : ∀ ξ, ‖G ξ‖ ≤ Gmax)
    (w : ℝ → ℝ) (hw : Continuous w)
    (B : ℤ → ℝ) (C V Mtail E₁ Wtail : ℝ)
    (hE₁0 : 0 < E₁) (hQ0 : 0 < 5 * C * V * halaszLSq B x + Mtail)
    (hw0 : ∀ t, 0 ≤ w t) (hwle : ∀ t, w t ≤ C/(1+t^2))
    (hE₁ : (∫ ξ, ‖ghsBlockPoly f x P ξ‖^2 * w ξ) ≤ E₁)
    (hB : ∀ N ∈ halaszRange x, ∀ t ∈ Set.Icc ((N:ℝ) - 1/2) ((N:ℝ) + 1/2),
      ‖G t‖ ≤ B N)
    (hB0 : ∀ N, 0 ≤ B N)
    (hV : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), ‖ghsPrimePoly f Q t‖^2) ≤ V)
    (hWtail : (∫ ξ in {ξ : ℝ | ((halaszM x : ℕ):ℝ) + 1/2 < |ξ|}, w ξ)
      ≤ Wtail)
    (hMtail : (∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ))^2 * Gmax^2 * Wtail ≤ Mtail) :
    (∫ ξ, ‖G ξ * ghsBlockPoly f x P ξ
        * ghsPrimePoly f Q ξ‖ * w ξ)
      ≤ Real.sqrt (E₁ * (5 * C * V * halaszLSq B x + Mtail)) := by
  classical
  have hC0 : (0:ℝ) ≤ C := by
    have h0 := hwle 0
    have hw00 := hw0 0
    norm_num at h0
    linarith
  obtain ⟨hg0, hg1, hg2, hjt, hk1, hk2, hk3⟩ :=
    ghs_pairing_integrability_G f hf x P Q G Gmax hGc hGb w hw C hw0 hwle
  -- the tail estimate: the window's mass, priced at the two sups
  have htail : (∫ ξ in {ξ : ℝ | ((halaszM x : ℕ):ℝ) + 1/2 < |ξ|},
      ‖ghsPrimePoly f Q ξ‖^2 * w ξ * ‖G ξ‖^2) ≤ Mtail :=
    le_trans (ghs_pairing_tail_le_G f hf x P Q G Gmax hGc hGb w hw C hw0
      hwle _ Wtail hWtail) hMtail
  exact pairing_halasz_sqrt_le G (ghsBlockPoly f x P)
    (ghsPrimePoly f Q) w B x C V Mtail E₁ hE₁0 hC0 hQ0 hw0 hwle hE₁ hB hB0 hV
    hg0 hg1 hg2 htail (fun i _ => hjt _ _) (fun N _ => hjt _ _)
    (fun N _ => hk1 _ _) (fun N _ => hk2 _ _) (fun N _ => hk3 _ _)

open MeasureTheory Real Complex Finset in
/-- **§4's pairing estimate at an abstract main factor, uniform band
sup** (Track R, M0R-4a): if `‖G‖ ≤ b` on the whole band then

  `∫_ℝ ‖G·P₂·P₃‖·w ≤ √(E₁·(30·C·V·b² + Mtail))`.

`ghs_pairing_estimate_uniform` abstracted.  This is the form the smooth
phase tsum meets: its band sup is *uniform in the frequency* —
`norm_phase_euler_prod_le_of_nonPretentious` does not vary from one
unit interval to the next — so `halaszLSq`'s dominating function may be
taken constant and `halaszLSq_le_of_bound` collapses `L(x)²` to
`6b²`. -/
theorem ghs_pairing_estimate_uniform_G (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x : ℕ) (P Q : Finset ℕ) (G : ℝ → ℂ) (Gmax : ℝ)
    (hGc : Continuous G) (hGb : ∀ ξ, ‖G ξ‖ ≤ Gmax)
    (w : ℝ → ℝ) (hw : Continuous w)
    (C V Mtail E₁ Wtail b : ℝ)
    (hE₁0 : 0 < E₁) (hb0 : 0 ≤ b) (hV0 : 0 ≤ V) (hMtail0 : 0 < Mtail)
    (hw0 : ∀ t, 0 ≤ w t) (hwle : ∀ t, w t ≤ C/(1+t^2))
    (hE₁ : (∫ ξ, ‖ghsBlockPoly f x P ξ‖^2 * w ξ) ≤ E₁)
    (hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 → ‖G t‖ ≤ b)
    (hV : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), ‖ghsPrimePoly f Q t‖^2) ≤ V)
    (hWtail : (∫ ξ in {ξ : ℝ | ((halaszM x : ℕ):ℝ) + 1/2 < |ξ|}, w ξ)
      ≤ Wtail)
    (hMtail : (∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ))^2 * Gmax^2 * Wtail ≤ Mtail) :
    (∫ ξ, ‖G ξ * ghsBlockPoly f x P ξ
        * ghsPrimePoly f Q ξ‖ * w ξ)
      ≤ Real.sqrt (E₁ * (5 * C * V * (6*b^2) + Mtail)) := by
  classical
  have hC0 : (0:ℝ) ≤ C := by
    have h0 := hwle 0
    have hw00 := hw0 0
    norm_num at h0
    linarith
  -- the constant dominating function
  have hLSq : halaszLSq (fun _ => b) x ≤ 6*b^2 :=
    halaszLSq_le_of_bound (fun _ => b) x b
      (fun N _ => by rw [abs_of_nonneg hb0])
  have hLSq0 : (0:ℝ) ≤ halaszLSq (fun _ => b) x := halaszLSq_nonneg _ _
  have hcoef : (0:ℝ) ≤ 5 * C * V := by positivity
  have hQ0 : 0 < 5 * C * V * halaszLSq (fun _ => b) x + Mtail := by
    nlinarith [hcoef, hLSq0, hMtail0]
  have hmain := ghs_pairing_estimate_G f hf x P Q G Gmax hGc hGb w hw
    (fun _ => b) C V Mtail E₁ Wtail hE₁0 hQ0 hw0 hwle hE₁
    (fun N hN t ht => hBu t (abs_le_halaszM_of_band x N hN t ht))
    (fun _ => hb0) hV hWtail hMtail
  refine le_trans hmain ?_
  refine Real.sqrt_le_sqrt ?_
  have hstep : 5 * C * V * halaszLSq (fun _ => b) x ≤ 5 * C * V * (6*b^2) :=
    mul_le_mul_of_nonneg_left hLSq hcoef
  exact mul_le_mul_of_nonneg_left (by linarith) hE₁0.le

open MeasureTheory Real Complex ArithmeticFunction Finset in
open scoped FourierTransform in
/-- **§4's pairing estimate at the Riesz weight, abstract main factor**
(Track R, M0R-4a):

  `∫_ℝ ‖G·P₂·P₃‖·‖𝓕V‖ ≤ √(E₁·(5·V₃·6b² + Mtail))`,

with `V = rieszWindow` and

  `Mtail ≥ (∑_q log q/q)²·Gmax²·1/(2π²(halaszM x + ½))`.

`ghs_riesz_pairing_le` abstracted: the weight's own hypotheses are
discharged by the same three `rieszWindow` facts — sup `1`, decay
`1/(1+ξ²)`, third-order tail — and nothing about the main factor
survives except its continuity, its global bound, and its band sup. -/
theorem ghs_riesz_pairing_le_G (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (x : ℕ) (P Q : Finset ℕ) (G : ℝ → ℂ) (Gmax : ℝ)
    (hGc : Continuous G) (hGb : ∀ ξ, ‖G ξ‖ ≤ Gmax)
    (V Mtail E₁ b : ℝ)
    (hE₁0 : 0 < E₁) (hb0 : 0 ≤ b) (hV0 : 0 ≤ V) (hMtail0 : 0 < Mtail)
    (hE₁ : (∫ ξ, ‖ghsBlockPoly f x P ξ‖^2
        * ‖𝓕 (fun v => ((ExpSums.rieszWindow v : ℝ) : ℂ)) ξ‖) ≤ E₁)
    (hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 → ‖G t‖ ≤ b)
    (hV : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), ‖ghsPrimePoly f Q t‖^2) ≤ V)
    (hMtail : (∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ))^2 * Gmax^2
        * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2))) ≤ Mtail) :
    (∫ ξ, ‖G ξ * ghsBlockPoly f x P ξ * ghsPrimePoly f Q ξ‖
        * ‖𝓕 (fun v => ((ExpSums.rieszWindow v : ℝ) : ℂ)) ξ‖)
      ≤ Real.sqrt (E₁ * (5 * V * (6*b^2) + Mtail)) := by
  classical
  have hL0 : (0:ℝ) < ((halaszM x : ℕ):ℝ) + 1/2 := by positivity
  have h := ghs_pairing_estimate_uniform_G f hf x P Q G Gmax hGc hGb
    (fun ξ => ‖𝓕 (fun v => ((ExpSums.rieszWindow v : ℝ) : ℂ)) ξ‖)
    ExpSums.continuous_norm_fourier_rieszWindow
    1 V Mtail E₁ (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2))) b
    hE₁0 hb0 hV0 hMtail0
    (fun t => norm_nonneg _)
    ExpSums.norm_fourier_rieszWindow_le
    hE₁ hBu hV
    (ExpSums.fourier_rieszWindow_tail_le _ hL0)
    hMtail
  simpa using h

end MoltResearch
