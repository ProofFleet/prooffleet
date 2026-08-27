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

namespace ExpSums

open Real MeasureTheory Filter
open scoped FourierTransform

/-- **The smooth phase sum** (Track R, M0R-4b): the `x`-smooth tsum

  `G_x(ξ) = ∑'_{n x-smooth} f(n)·n⁻¹·e(−ξ·log n)`,

the abstract main factor of the re-plumbed §4 chain.  This is the
object that replaces the finite `ghsMainPoly f (Icc 1 x)`: on the
Riesz window's support the two agree exactly (every index the window
keeps is `x`-smooth), but the tsum is a truncated Euler product, so its
band sup is log-free where the partial sum's was not. -/
noncomputable def smoothPhaseSum (f : ℕ → ℂ) (x : ℕ) : ℝ → ℂ :=
  fun ξ => ∑' m : (Nat.smoothNumbers x),
    f m * ((m : ℕ) : ℂ)⁻¹ * ((𝐞 (-(Real.log m * ξ)) : Circle) : ℂ)

/-- **The smooth phase sum is the truncated Euler product** (Track R,
M0R-4b): `hasSum_smooth_phase_prod`, read at the tsum. -/
theorem smoothPhaseSum_eq_prod (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (hb : ∀ n, ‖f n‖ ≤ 1) (x : ℕ) (ξ : ℝ) :
    smoothPhaseSum f x ξ
      = ∏ p ∈ x.primesBelow,
          (1 - f p * ((p : ℕ) : ℂ)⁻¹
              * ((𝐞 (-(Real.log p * ξ)) : Circle) : ℂ))⁻¹ :=
  (hasSum_smooth_phase_prod f hcm h1 hb x ξ).tsum_eq

/-- **The log-free band sup of the smooth phase sum** (Track R,
M0R-4b): for `1`-bounded completely multiplicative `f` with
`NonPretentiousAt f A x` and any frequency `|2πξ| ≤ A·x`,

  `‖G_x(ξ)‖ ≤ e⁵·(2 + log x)·e^{−A}`.

`norm_phase_euler_prod_le_of_nonPretentious` transported through
`smoothPhaseSum_eq_prod` — the band-sup hypothesis `hBu` of the
abstract §4 chain, met by the main factor itself.  This is the M0R
campaign's point of contact: the finite polynomial's band sup could
only be reached through the smooth-restriction detour and its
`W ≈ 2×10⁷` losses; the tsum's is a single Euler-product estimate. -/
theorem norm_smoothPhaseSum_le_of_nonPretentious (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (hb : ∀ n, ‖f n‖ ≤ 1) (x : ℕ) (hx : 3 ≤ x)
    (A : ℝ) (h1A : 1 ≤ A) (hA : NonPretentiousAt f A x)
    (ξ : ℝ) (hξ : |2 * Real.pi * ξ| ≤ A * (x:ℝ)) :
    ‖smoothPhaseSum f x ξ‖
      ≤ Real.exp 5 * (2 + Real.log (x:ℝ)) * Real.exp (-A) := by
  rw [smoothPhaseSum_eq_prod f hcm h1 hb x ξ]
  exact norm_phase_euler_prod_le_of_nonPretentious f hb x hx A h1A hA ξ hξ

/-- **The smooth phase sum is continuous** (Track R, M0R-4b): the
regularity half of the abstract main-factor hypotheses.  Uniform
convergence: each term is a constant times a unimodular phase, so the
majorant is the frequency-free weight mass
(`summable_norm_smooth_phase`). -/
theorem continuous_smoothPhaseSum (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (hb : ∀ n, ‖f n‖ ≤ 1) (x : ℕ) :
    Continuous (smoothPhaseSum f x) := by
  unfold smoothPhaseSum
  refine continuous_tsum
    (u := fun m : (Nat.smoothNumbers x) =>
      ‖f m * ((m : ℕ) : ℂ)⁻¹ * ((𝐞 (-(Real.log m * 0)) : Circle) : ℂ)‖)
    (fun m => ?_) (summable_norm_smooth_phase f hcm h1 hb x 0)
    (fun m ξ => ?_)
  · exact continuous_const.mul
      (Continuous.comp continuous_subtype_val
        (Real.continuous_fourierChar.comp (by fun_prop)))
  · have hphase : ∀ (t : ℝ),
        ‖f ↑m * (((m : ℕ) : ℕ) : ℂ)⁻¹
            * ((𝐞 (-(Real.log ↑m * t)) : Circle) : ℂ)‖
          = ‖f ↑m * (((m : ℕ) : ℕ) : ℂ)⁻¹‖ := by
      intro t
      rw [norm_mul, norm_eq_of_mem_sphere, mul_one]
    exact le_of_eq ((hphase ξ).trans (hphase 0).symm)

/-- **The global sup of the smooth phase sum is the smooth mass**
(Track R, M0R-4b):

  `‖G_x(ξ)‖ ≤ ∑'_{n x-smooth} 1/n`,  uniformly in `ξ`.

The abstract chain's `Gmax`: the crude bound that prices the tail,
exactly as `norm_ghsMainPoly_le` did for the finite polynomial —
`≍ log x` in both cases, so the tail budget is unchanged by the
swap. -/
theorem norm_smoothPhaseSum_le (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (hb : ∀ n, ‖f n‖ ≤ 1) (x : ℕ) (ξ : ℝ) :
    ‖smoothPhaseSum f x ξ‖
      ≤ ∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹ := by
  have hsummass : Summable
      (fun m : (Nat.smoothNumbers x) => (((m : ℕ) : ℝ))⁻¹) := by
    have hone : CompletelyMultiplicativeC (fun _ : ℕ => (1:ℂ)) :=
      fun a b _ _ => by simp
    refine (summable_norm_smooth_phase (fun _ => 1) hone rfl
      (fun n => by simp) x 0).congr fun m => ?_
    rw [norm_mul, norm_mul, norm_eq_of_mem_sphere, mul_one, norm_one,
      one_mul, norm_inv, Complex.norm_natCast]
  unfold smoothPhaseSum
  refine le_trans (norm_tsum_le_tsum_norm
    (summable_norm_smooth_phase f hcm h1 hb x ξ)) ?_
  refine Summable.tsum_le_tsum (fun m => ?_)
    (summable_norm_smooth_phase f hcm h1 hb x ξ) hsummass
  rw [norm_mul, norm_mul, norm_eq_of_mem_sphere, mul_one, norm_inv,
    Complex.norm_natCast]
  calc ‖f ↑m‖ * (((m : ℕ) : ℝ))⁻¹
      ≤ 1 * (((m : ℕ) : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right (hb ↑m) (by positivity)
    _ = (((m : ℕ) : ℝ))⁻¹ := one_mul _

-- PR-D1: appended inside namespace ExpSums of HalaszTripleG.lean

/-- **The smooth indicator weight** (Track R, M0R-4b): the `ℕ`-indexed
weight family `n ↦ f(n)/n` on the `x`-smooth numbers and `0` elsewhere —
the form the countable pairing `tsum_translates_eq_integral_char`
consumes.  Its phase sum is `smoothPhaseSum` (the subtype tsum), and
against a window vanishing at non-positive arguments its translate sum
collapses to the finite window sum over `Icc 1 x`. -/
noncomputable def smoothWeight (f : ℕ → ℂ) (x : ℕ) : ℕ → ℂ :=
  fun n => if n ∈ Nat.smoothNumbers x then f n * ((n : ℕ) : ℂ)⁻¹ else 0

/-- **The smooth weight is absolutely summable** (Track R, M0R-4b):
`summable_norm_smooth_phase` read through the indicator. -/
theorem summable_norm_smoothWeight (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (hb : ∀ n, ‖f n‖ ≤ 1) (x : ℕ) :
    Summable (fun n : ℕ => ‖smoothWeight f x n‖) := by
  have hsub : Summable
      (fun m : (Nat.smoothNumbers x) => ‖f m * ((m : ℕ) : ℂ)⁻¹‖) := by
    refine (summable_norm_smooth_phase f hcm h1 hb x 0).congr fun m => ?_
    rw [norm_mul, norm_eq_of_mem_sphere, mul_one]
  have hind := (summable_subtype_iff_indicator
    (f := fun n : ℕ => ‖f n * ((n : ℕ) : ℂ)⁻¹‖)
    (s := Nat.smoothNumbers x)).mp hsub
  refine hind.congr fun n => ?_
  by_cases hn : n ∈ Nat.smoothNumbers x <;>
    simp [smoothWeight, hn]

open scoped FourierTransform in
/-- **The smooth weight's phase sum is the smooth phase sum** (Track R,
M0R-4b): the indicator bridge between the `ℕ`-indexed pairing and the
subtype tsum. -/
theorem tsum_smoothWeight_char (f : ℕ → ℂ) (x : ℕ) (ξ : ℝ) :
    ∑' n : ℕ, smoothWeight f x n
        * ((𝐞 (-(Real.log (n:ℝ) * ξ)) : Circle) : ℂ)
      = smoothPhaseSum f x ξ := by
  unfold smoothPhaseSum
  rw [tsum_subtype (Nat.smoothNumbers x)
    (fun n : ℕ => f n * ((n : ℕ) : ℂ)⁻¹
      * ((𝐞 (-(Real.log (n:ℝ) * ξ)) : Circle) : ℂ))]
  refine tsum_congr fun n => ?_
  by_cases hn : n ∈ Nat.smoothNumbers x <;>
    simp [smoothWeight, hn]

/-- **The window kills everything the smooth weight adds** (Track R,
M0R-4b): for a window vanishing at non-positive arguments and any
`u ≤ log x`, the smooth translate tsum *is* the finite window sum over
`Icc 1 x`:

  `∑'_n smoothWeight(n)·V(u − log n) = ∑_{n ∈ Icc 1 x} (f n/n)·V(u − log n)`.

Three regimes: `n` smooth and `≤ x` — the terms agree; `n > x` — the
window argument is `≤ u − log x ≤ 0`, so both sides vanish; `n ≤ x` not
smooth — then `n = x` exactly (everything *below* `x` is `x`-smooth),
and the window vanishes there too.  This is the observation that makes
the tsum swap free on the time side: the Riesz window never sees an
index where the finite sum and the smooth tsum differ. -/
theorem tsum_smoothWeight_window (f : ℕ → ℂ) (x : ℕ) (hx : 1 ≤ x)
    (V : ℝ → ℝ) (hV0 : ∀ v, v ≤ 0 → V v = 0)
    (u : ℝ) (hu : u ≤ Real.log (x:ℝ)) :
    ∑' n : ℕ, smoothWeight f x n * ((V (u - Real.log (n:ℝ)) : ℝ) : ℂ)
      = ∑ n ∈ Finset.Icc 1 x,
          (f n / (n:ℂ)) * ((V (u - Real.log (n:ℝ)) : ℝ) : ℂ) := by
  have hxR : (0:ℝ) < (x:ℝ) := by
    have : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
    linarith
  rw [tsum_eq_sum (s := Finset.Icc 1 x) ?_]
  · refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.mp hn
    by_cases hsm : n ∈ Nat.smoothNumbers x
    · rw [smoothWeight, if_pos hsm, div_eq_mul_inv]
    · -- not smooth and `≤ x` forces `n = x`, where the window vanishes
      have hnx' : n = x := by
        rcases Nat.lt_or_ge n x with hlt | hge
        · exact absurd (Nat.mem_smoothNumbers_of_lt (by omega) hlt) hsm
        · omega
      have hV : V (u - Real.log (n:ℝ)) = 0 := by
        refine hV0 _ ?_
        rw [hnx']
        linarith
      rw [smoothWeight, if_neg hsm, hV]
      simp
  · intro b hb
    rcases Nat.eq_zero_or_pos b with hb0 | hb1
    · subst hb0
      have h0 : (0:ℕ) ∉ Nat.smoothNumbers x :=
        fun h => (Nat.mem_smoothNumbers.mp h).1 rfl
      rw [smoothWeight, if_neg h0, zero_mul]
    · have hbx : x < b := by
        rcases Nat.lt_or_ge x b with h | h
        · exact h
        · exact absurd (Finset.mem_Icc.mpr ⟨hb1, h⟩) hb
      have hV : V (u - Real.log (b:ℝ)) = 0 := by
        refine hV0 _ ?_
        have hlog : Real.log (x:ℝ) ≤ Real.log (b:ℝ) :=
          Real.log_le_log hxR (by exact_mod_cast hbx.le)
        linarith
      rw [hV]
      simp

/-- **The Riesz window is at most one** (Track R, M0R-4b): the crude
sup that the countable pairing's dominated-convergence step asks for —
`v·e^{−v} ≤ 1` on the support, `0` off it. -/
theorem norm_rieszWindow_ofReal_le_one (v : ℝ) :
    ‖((rieszWindow v : ℝ) : ℂ)‖ ≤ 1 := by
  have hnn : 0 ≤ rieszWindow v := by
    rw [rieszWindow_eq_max]
    positivity
  have hle : rieszWindow v ≤ 1 := by
    rw [rieszWindow_eq_max]
    set m := max v 0 with hm_def
    have hm0 : 0 ≤ m := le_max_right v 0
    have hme : m ≤ Real.exp m := by
      linarith [Real.add_one_le_exp m]
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos m)]
    exact hme
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hle

open MeasureTheory Filter in
open scoped FourierTransform in
/-- **The inner window sum as a pairing against the smooth phase sum**
(Track R, M0R-4b): for `u ≤ log x`,

  `∑_{n ∈ Icc 1 x} (f n/n)·V(u − log n)
     = ∫ e(ξu)·G_x(ξ)·𝓕V(ξ) dξ`,  `V = rieszWindow`.

The countable pairing `tsum_translates_eq_integral_char` at the smooth
indicator weight, with the time side collapsed to the finite window sum
(`tsum_smoothWeight_window`) and the frequency side identified as
`smoothPhaseSum` (`tsum_smoothWeight_char`).  Applied at
`u = log(x/pq)`, the prefactor `e(ξu)` is what carries the `p`- and
`q`-phases out of the tsum — no reindex of the infinite sum is ever
needed. -/
theorem sum_Icc_window_eq_integral_smoothPhase (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (hb : ∀ n, ‖f n‖ ≤ 1) (x : ℕ) (hx : 1 ≤ x)
    (u : ℝ) (hu : u ≤ Real.log (x:ℝ)) :
    ∑ n ∈ Finset.Icc 1 x,
        (f n / (n:ℂ)) * ((rieszWindow (u - Real.log (n:ℝ)) : ℝ) : ℂ)
      = ∫ ξ, (𝐞 (ξ * u) : Circle)
          • (smoothPhaseSum f x ξ
            * 𝓕 (fun v => ((rieszWindow v : ℝ) : ℂ)) ξ) := by
  have hV0 : ∀ v : ℝ, v ≤ 0 → rieszWindow v = 0 := by
    intro v hv
    rw [rieszWindow, if_neg (not_lt.mpr hv)]
  rw [← tsum_smoothWeight_window f x hx rieszWindow hV0 u hu]
  rw [tsum_translates_eq_integral_char
    (fun v => ((rieszWindow v : ℝ) : ℂ))
    continuous_rieszWindow_ofReal integrable_rieszWindow_ofReal
    integrable_fourier_rieszWindow 1 norm_rieszWindow_ofReal_le_one
    (smoothWeight f x) (fun n => Real.log (n:ℝ))
    (summable_norm_smoothWeight f hcm h1 hb x) u]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [tsum_smoothWeight_char f x ξ]

-- PR-D2: appended inside namespace ExpSums of HalaszTripleG.lean (after D1)

open MeasureTheory Real Complex Finset Filter in
open scoped FourierTransform in
/-- **§3's fixed-range triple sum as one frequency integral** (Track R,
M0R-4b): with `G = smoothPhaseSum f x`,

  `∑_p (log p·f_p/log(x/p)) ∑_q (log q·f_q)·((x/pq)·∑_{n ≤ x} (f_n/n)·V(log(x/pq) − log n))`
  `  = ∫ x·e(ξ·log x)·G(ξ)·P₂(ξ)·P₃(ξ)·𝓕V(ξ) dξ`,  `V = rieszWindow`.

The reindex-free realisation of §4's pairing: each inner window sum is
the pairing integral (`sum_Icc_window_eq_integral_smoothPhase`), the
finite `p, q` sums move inside the integral
(`MeasureTheory.integral_finset_sum`, each summand dominated by the
smooth mass times `‖𝓕V‖`), and per frequency the double sum factors
through `char_poly_mul_log` into the block and prime polynomials — the
`e(ξ·log(x/pq))` prefactor is what carries the `p`- and `q`-phases, so
the infinite `n`-sum is never reindexed.  Exact: no error term. -/
theorem ghs_riesz_triple_tsum_eq (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (hf : ∀ n, ‖f n‖ ≤ 1) (x : ℕ) (hx : 1 ≤ x) (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, 0 < p) (hQ : ∀ q ∈ Q, 0 < q) :
    ∑ p ∈ P, ((Real.log (p:ℝ) : ℂ) * f p
        / ((Real.log ((x:ℝ)/(p:ℝ)) : ℝ) : ℂ))
        * ∑ q ∈ Q, ((Real.log (q:ℝ) : ℂ) * f q)
            * ((((x:ℝ)/((p:ℝ)*(q:ℝ)) : ℝ) : ℂ)
              * ∑ n ∈ Finset.Icc 1 x, (f n / (n:ℂ))
                  * ((ExpSums.rieszWindow
                      (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                        - Real.log (n:ℝ)) : ℝ) : ℂ))
      = ∫ ξ, ((x:ℂ))
          * ((𝐞 (ξ * Real.log (x:ℝ)) : Circle) : ℂ)
          * (smoothPhaseSum f x ξ * ghsBlockPoly f x P ξ
            * ghsPrimePoly f Q ξ
            * 𝓕 (fun v => ((rieszWindow v : ℝ) : ℂ)) ξ) := by
  classical
  have hxR : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx
  -- each inner window sum is the pairing integral
  have hswap : ∀ p ∈ P, ∀ q ∈ Q,
      (∑ n ∈ Finset.Icc 1 x, (f n / (n:ℂ))
          * ((ExpSums.rieszWindow
              (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ)) : ℝ) : ℂ))
        = ∫ ξ, (𝐞 (ξ * Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))) : Circle)
            • (smoothPhaseSum f x ξ
              * 𝓕 (fun v => ((rieszWindow v : ℝ) : ℂ)) ξ) := by
    intro p hp q hq
    refine sum_Icc_window_eq_integral_smoothPhase f hcm h1 hf x hx _ ?_
    have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hP p hp
    have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hQ q hq
    have hpq : (1:ℝ) ≤ (p:ℝ) * (q:ℝ) := by nlinarith
    have hle : (x:ℝ)/((p:ℝ)*(q:ℝ)) ≤ (x:ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    exact Real.log_le_log (by positivity) hle
  -- the per-pair integrand, and its integrability
  have hGc : Continuous (smoothPhaseSum f x) :=
    continuous_smoothPhaseSum f hcm h1 hf x
  have hInt : ∀ (c d s : ℂ) (u : ℝ), Integrable (fun ξ =>
      c * (d * (s * (((𝐞 (ξ * u) : Circle) : ℂ)
        * (smoothPhaseSum f x ξ
          * 𝓕 (fun v => ((rieszWindow v : ℝ) : ℂ)) ξ))))) := by
    intro c d s u
    have hshape : ∀ ξ : ℝ,
        (c * d * s * ((𝐞 (ξ * u) : Circle) : ℂ) * smoothPhaseSum f x ξ)
            * 𝓕 (fun v => ((rieszWindow v : ℝ) : ℂ)) ξ
        = c * (d * (s * (((𝐞 (ξ * u) : Circle) : ℂ)
            * (smoothPhaseSum f x ξ
              * 𝓕 (fun v => ((rieszWindow v : ℝ) : ℂ)) ξ)))) := by
      intro ξ
      ring
    have hmeas : AEStronglyMeasurable (fun ξ : ℝ =>
        c * d * s * ((𝐞 (ξ * u) : Circle) : ℂ)
          * smoothPhaseSum f x ξ) volume := by
      refine Continuous.aestronglyMeasurable ?_
      refine (continuous_const.mul ?_).mul hGc
      exact Continuous.comp continuous_subtype_val
        (Real.continuous_fourierChar.comp (by fun_prop))
    have hbound : ∀ᵐ ξ : ℝ ∂volume,
        ‖c * d * s * ((𝐞 (ξ * u) : Circle) : ℂ) * smoothPhaseSum f x ξ‖
          ≤ ‖c * d * s‖
            * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹) := by
      refine Eventually.of_forall fun ξ => ?_
      rw [norm_mul, norm_mul, norm_eq_of_mem_sphere, mul_one]
      exact mul_le_mul_of_nonneg_left
        (norm_smoothPhaseSum_le f hcm h1 hf x ξ) (norm_nonneg _)
    exact Integrable.congr
      (integrable_fourier_rieszWindow.bdd_mul hmeas hbound)
      (Eventually.of_forall fun ξ => hshape ξ)
  -- substitute the pairing and move the finite sums inside the integral
  have hstep : ∑ p ∈ P, ((Real.log (p:ℝ) : ℂ) * f p
        / ((Real.log ((x:ℝ)/(p:ℝ)) : ℝ) : ℂ))
        * ∑ q ∈ Q, ((Real.log (q:ℝ) : ℂ) * f q)
            * ((((x:ℝ)/((p:ℝ)*(q:ℝ)) : ℝ) : ℂ)
              * ∑ n ∈ Finset.Icc 1 x, (f n / (n:ℂ))
                  * ((ExpSums.rieszWindow
                      (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                        - Real.log (n:ℝ)) : ℝ) : ℂ))
      = ∑ r ∈ P ×ˢ Q, ∫ ξ,
          ((Real.log (r.1:ℝ) : ℂ) * f r.1
              / ((Real.log ((x:ℝ)/(r.1:ℝ)) : ℝ) : ℂ))
            * (((Real.log (r.2:ℝ) : ℂ) * f r.2)
              * ((((x:ℝ)/((r.1:ℝ)*(r.2:ℝ)) : ℝ) : ℂ)
                * (((𝐞 (ξ * Real.log ((x:ℝ)/((r.1:ℝ)*(r.2:ℝ)))) : Circle) : ℂ)
                  * (smoothPhaseSum f x ξ
                    * 𝓕 (fun v => ((rieszWindow v : ℝ) : ℂ)) ξ)))) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [hswap p hp q hq, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    dsimp only
    simp only [Circle.smul_def, smul_eq_mul]
  rw [hstep, ← MeasureTheory.integral_finset_sum _
    (fun r _ => hInt _ _ _ _)]
  -- per frequency: the double sum is the product of the two polynomials
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  dsimp only
  -- split each phase at `log(x/pq) = log x − log(pq)`
  have hphase : ∀ r ∈ P ×ˢ Q,
      ((Real.log (r.1:ℝ) : ℂ) * f r.1
          / ((Real.log ((x:ℝ)/(r.1:ℝ)) : ℝ) : ℂ))
        * (((Real.log (r.2:ℝ) : ℂ) * f r.2)
          * ((((x:ℝ)/((r.1:ℝ)*(r.2:ℝ)) : ℝ) : ℂ)
            * (((𝐞 (ξ * Real.log ((x:ℝ)/((r.1:ℝ)*(r.2:ℝ)))) : Circle) : ℂ)
              * (smoothPhaseSum f x ξ
                * 𝓕 (fun v => ((rieszWindow v : ℝ) : ℂ)) ξ))))
      = (((x:ℂ))
          * ((𝐞 (ξ * Real.log (x:ℝ)) : Circle) : ℂ)
          * (smoothPhaseSum f x ξ
            * 𝓕 (fun v => ((rieszWindow v : ℝ) : ℂ)) ξ))
        * (((((Real.log (r.1:ℝ) : ℂ) * f r.1)
              / ((r.1:ℂ) * ((Real.log ((x:ℝ)/(r.1:ℝ)) : ℝ) : ℂ)))
            * (((Real.log (r.2:ℝ) : ℂ) * f r.2) / (r.2:ℂ)))
          * ((Real.fourierChar
              (-(Real.log ((r.1 * r.2 : ℕ):ℝ) * ξ)) : Circle) : ℂ)) := by
    intro r hr
    rw [Finset.mem_product] at hr
    have hp0 : (0:ℝ) < (r.1:ℝ) := by exact_mod_cast hP r.1 hr.1
    have hq0 : (0:ℝ) < (r.2:ℝ) := by exact_mod_cast hQ r.2 hr.2
    have hlog : Real.log ((x:ℝ)/((r.1:ℝ)*(r.2:ℝ)))
        = Real.log (x:ℝ) - Real.log ((r.1 * r.2 : ℕ):ℝ) := by
      push_cast
      rw [Real.log_div (ne_of_gt hxR) (by positivity),
        Real.log_mul (ne_of_gt hp0) (ne_of_gt hq0)]
    have hchar : ((𝐞 (ξ * Real.log ((x:ℝ)/((r.1:ℝ)*(r.2:ℝ)))) : Circle) : ℂ)
        = ((𝐞 (ξ * Real.log (x:ℝ)) : Circle) : ℂ)
          * ((Real.fourierChar
              (-(Real.log ((r.1 * r.2 : ℕ):ℝ) * ξ)) : Circle) : ℂ) := by
      rw [show ξ * Real.log ((x:ℝ)/((r.1:ℝ)*(r.2:ℝ)))
          = ξ * Real.log (x:ℝ)
            + -(Real.log ((r.1 * r.2 : ℕ):ℝ) * ξ) from by
        rw [hlog]; ring]
      rw [Real.fourierChar.map_add_eq_mul]
      push_cast
      ring
    rw [hchar]
    push_cast
    ring
  rw [Finset.sum_congr rfl hphase, ← Finset.mul_sum]
  -- the coefficient sum is the product of the two §4 polynomials
  have hpoly : ∑ r ∈ P ×ˢ Q,
      (((((Real.log (r.1:ℝ) : ℂ) * f r.1)
            / ((r.1:ℂ) * ((Real.log ((x:ℝ)/(r.1:ℝ)) : ℝ) : ℂ)))
          * (((Real.log (r.2:ℝ) : ℂ) * f r.2) / (r.2:ℂ)))
        * ((Real.fourierChar
            (-(Real.log ((r.1 * r.2 : ℕ):ℝ) * ξ)) : Circle) : ℂ))
      = ghsBlockPoly f x P ξ * ghsPrimePoly f Q ξ := by
    rw [ghsBlockPoly, ghsPrimePoly]
    rw [char_poly_mul_log P Q
      (fun p => ((Real.log (p:ℝ) : ℂ) * f p)
        / ((p:ℂ) * ((Real.log ((x:ℝ)/(p:ℝ)) : ℝ) : ℂ)))
      (fun q => ((Real.log (q:ℝ) : ℂ) * f q) / (q:ℂ)) hP hQ ξ]
  rw [hpoly]
  ring

open MeasureTheory Real Complex Finset in
open scoped FourierTransform in
/-- **§3's fixed-range triple sum, bounded through the smooth tsum**
(Track R, M0R-4b):

  `‖∑_p (log p·f_p/log(x/p)) ∑_q (log q·f_q)·((x/pq)·∑_{n≤x}(f_n/n)·V(log(x/pq) − log n))‖`
  `  ≤ x·√(E₁·(5·V₃·6b² + Mtail))`,  `V = rieszWindow`,

with the band sup `b` demanded of `smoothPhaseSum` — the slot the
log-free `e⁵(2+log x)e^{−A}` of M0R-3d fills — and the tail priced at
its global bound `Gmax`.

`ghs_riesz_triple_tsum_eq` followed by `ghs_riesz_pairing_le_G`: take
norms under the integral (the `x·e(ξ·log x)` prefactor contributes
exactly `x`), and what remains is the abstract Riesz pairing.  This is
the tsum counterpart of `ghs_riesz_triple_le_real`'s role: the bound on
the enlarged form `D` of the triple convolution, with no smooth
restriction anywhere. -/
theorem ghs_riesz_triple_tsum_le (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (hf : ∀ n, ‖f n‖ ≤ 1) (x : ℕ) (hx : 1 ≤ x) (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, 0 < p) (hQ : ∀ q ∈ Q, 0 < q)
    (V₃ Mtail E₁ b Gmax : ℝ)
    (hE₁0 : 0 < E₁) (hb0 : 0 ≤ b) (hV₃0 : 0 ≤ V₃) (hMtail0 : 0 < Mtail)
    (hGb : ∀ ξ, ‖smoothPhaseSum f x ξ‖ ≤ Gmax)
    (hE₁ : (∫ ξ, ‖ghsBlockPoly f x P ξ‖^2
        * ‖𝓕 (fun v => ((rieszWindow v : ℝ) : ℂ)) ξ‖) ≤ E₁)
    (hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖smoothPhaseSum f x t‖ ≤ b)
    (hV : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2), ‖ghsPrimePoly f Q t‖^2) ≤ V₃)
    (hMtail : (∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ))^2 * Gmax^2
        * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2))) ≤ Mtail) :
    ‖∑ p ∈ P, ((Real.log (p:ℝ) : ℂ) * f p
        / ((Real.log ((x:ℝ)/(p:ℝ)) : ℝ) : ℂ))
        * ∑ q ∈ Q, ((Real.log (q:ℝ) : ℂ) * f q)
            * ((((x:ℝ)/((p:ℝ)*(q:ℝ)) : ℝ) : ℂ)
              * ∑ n ∈ Finset.Icc 1 x, (f n / (n:ℂ))
                  * ((ExpSums.rieszWindow
                      (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                        - Real.log (n:ℝ)) : ℝ) : ℂ))‖
      ≤ (x:ℝ) * Real.sqrt (E₁ * (5 * V₃ * (6*b^2) + Mtail)) := by
  classical
  have hxR : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
  rw [ghs_riesz_triple_tsum_eq f hcm h1 hf x hx P Q hP hQ]
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
  have hcongr : (∫ ξ, ‖((x:ℂ))
        * ((𝐞 (ξ * Real.log (x:ℝ)) : Circle) : ℂ)
        * (smoothPhaseSum f x ξ * ghsBlockPoly f x P ξ
          * ghsPrimePoly f Q ξ
          * 𝓕 (fun v => ((rieszWindow v : ℝ) : ℂ)) ξ)‖)
      = ∫ ξ, (x:ℝ) * (‖smoothPhaseSum f x ξ * ghsBlockPoly f x P ξ
          * ghsPrimePoly f Q ξ‖
        * ‖𝓕 (fun v => ((rieszWindow v : ℝ) : ℂ)) ξ‖) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    dsimp only
    rw [norm_mul, norm_mul, norm_mul, norm_eq_of_mem_sphere, mul_one,
      Complex.norm_natCast]
  rw [hcongr, MeasureTheory.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ hxR
  exact ghs_riesz_pairing_le_G f hf x P Q (smoothPhaseSum f x) Gmax
    (continuous_smoothPhaseSum f hcm h1 hf x) hGb V₃ Mtail E₁ b
    hE₁0 hb0 hV₃0 hMtail0 hE₁ hBu hV hMtail

open Real Complex Finset in
/-- **The tsum triple bound at a real coefficient sequence** (Track R,
M0R-4b): `ghs_riesz_triple_tsum_le` at the coerced coefficients — the
`ℝ`/`ℂ` interface §3's assembly meets, in exactly the shape of the
enlarged form `D` inside `tripleConvR_le`. -/
theorem ghs_riesz_triple_tsum_le_real (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (hcm : CompletelyMultiplicativeC (fun n => ((f n : ℝ) : ℂ)))
    (h1 : f 1 = 1) (x : ℕ) (hx : 1 ≤ x) (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, 0 < p) (hQ : ∀ q ∈ Q, 0 < q)
    (V₃ Mtail E₁ b Gmax : ℝ)
    (hE₁0 : 0 < E₁) (hb0 : 0 ≤ b) (hV₃0 : 0 ≤ V₃) (hMtail0 : 0 < Mtail)
    (hGb : ∀ ξ, ‖smoothPhaseSum (fun n => ((f n : ℝ) : ℂ)) x ξ‖ ≤ Gmax)
    (hE₁ : (∫ ξ, ‖ghsBlockPoly (fun n => ((f n : ℝ) : ℂ)) x P ξ‖^2
        * ‖𝓕 (fun v => ((rieszWindow v : ℝ) : ℂ)) ξ‖) ≤ E₁)
    (hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖smoothPhaseSum (fun n => ((f n : ℝ) : ℂ)) x t‖ ≤ b)
    (hV : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2),
        ‖ghsPrimePoly (fun n => ((f n : ℝ) : ℂ)) Q t‖^2) ≤ V₃)
    (hMtail : (∑ q ∈ Q, Real.log (q:ℝ)/(q:ℝ))^2 * Gmax^2
        * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2))) ≤ Mtail) :
    |∑ p ∈ P, (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
        * ∑ q ∈ Q, (Real.log (q:ℝ) * f q)
            * (((x:ℝ)/((p:ℝ)*(q:ℝ)))
              * ∑ n ∈ Finset.Icc 1 x, (f n/(n:ℝ))
                  * ExpSums.rieszWindow
                      (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ))) - Real.log (n:ℝ)))|
      ≤ (x:ℝ) * Real.sqrt (E₁ * (5 * V₃ * (6*b^2) + Mtail)) := by
  classical
  have hfc : ∀ n, ‖((f n : ℝ) : ℂ)‖ ≤ 1 := by
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hf n
  have h1c : ((f 1 : ℝ) : ℂ) = 1 := by
    rw [h1]
    norm_num
  have hcast : ((∑ p ∈ P, (Real.log (p:ℝ) * f p / Real.log ((x:ℝ)/(p:ℝ)))
        * ∑ q ∈ Q, (Real.log (q:ℝ) * f q)
            * (((x:ℝ)/((p:ℝ)*(q:ℝ)))
              * ∑ n ∈ Finset.Icc 1 x, (f n/(n:ℝ))
                  * ExpSums.rieszWindow
                      (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                        - Real.log (n:ℝ))) : ℝ) : ℂ)
      = ∑ p ∈ P, ((Real.log (p:ℝ) : ℂ) * ((f p : ℝ) : ℂ)
          / ((Real.log ((x:ℝ)/(p:ℝ)) : ℝ) : ℂ))
          * ∑ q ∈ Q, ((Real.log (q:ℝ) : ℂ) * ((f q : ℝ) : ℂ))
              * ((((x:ℝ)/((p:ℝ)*(q:ℝ)) : ℝ) : ℂ)
                * ∑ n ∈ Finset.Icc 1 x, (((f n : ℝ) : ℂ) / (n:ℂ))
                    * ((ExpSums.rieszWindow
                        (Real.log ((x:ℝ)/((p:ℝ)*(q:ℝ)))
                          - Real.log (n:ℝ)) : ℝ) : ℂ)) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Complex.ofReal_mul]
    refine congrArg₂ (· * ·) (by norm_cast) ?_
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Complex.ofReal_mul]
    refine congrArg₂ (· * ·) (by norm_cast) ?_
    rw [Complex.ofReal_mul]
    refine congrArg₂ (· * ·) (by norm_cast) ?_
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    ring
  have h := ghs_riesz_triple_tsum_le (fun n => ((f n : ℝ) : ℂ))
    hcm h1c hfc x hx P Q hP hQ V₃ Mtail E₁ b Gmax
    hE₁0 hb0 hV₃0 hMtail0 hGb hE₁ hBu hV hMtail
  rw [← hcast, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

end ExpSums

end MoltResearch
