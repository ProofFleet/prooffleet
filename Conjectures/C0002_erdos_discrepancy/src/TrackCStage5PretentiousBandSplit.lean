import Conjectures.C0002_erdos_discrepancy.src.Interfaces.FarRegimeRepulsion

/-!
# Track R VI-9f: the verified mid/far `t₁` split

The compact-band minimizer and the mid-range estimate live in the nucleus.
This file joins the mid range to the single far-regime literature interface.
The small `t₁` window is intentionally not claimed here: the currently
available GHS closed form carries leading `log x` and `loglog x` losses, so it
does not imply the loglog-free `1/(1+|t-t₁|)` estimate required by the design.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The far branch supplied verbatim by the named interface. -/
theorem pretentiousDistSq_archTwist_ge_far
    [FarRegimeRepulsionAssumption] :
    ∃ y0 : ℕ, ∀ (f : ℕ → ℂ) (y : ℕ) (t1 t : ℝ),
      Unimodular f → y0 ≤ y → 3 ≤ y →
      |t1| ≤ y → |t| ≤ y →
      pretentiousDistSq f
          (fun n => (n : ℂ) ^ (-(Complex.I * (t1 : ℂ)))) y ≤
        pretentiousDistSq f
          (fun n => (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) y →
      (Real.log y) ^ (20 : ℕ) < |t - t1| →
      exceptionalRepulsionRho * Real.log (Real.log y) ≤
        pretentiousDistSq f
          (fun n => (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) y :=
  FarRegimeRepulsionAssumption.bound

/-- The complete verified `𝒯₁` strength split outside the small window.
The mid branch is the in-tree zeta-repulsion inequality with its exact numerical
fit exposed; the far branch is the sole new interface. -/
theorem pretentiousDistSq_archTwist_ge_of_mid_or_far
    [FarRegimeRepulsionAssumption] :
    ∃ y0 : ℕ, ∀ (f : ℕ → ℂ) (y : ℕ) (t1 t : ℝ),
      Unimodular f → y0 ≤ y → 3 ≤ y →
      |t1| ≤ y → |t| ≤ y → 6 ≤ |t - t1| →
      pretentiousDistSq f
          (fun n => (n : ℂ) ^ (-(Complex.I * (t1 : ℂ)))) y ≤
        pretentiousDistSq f
          (fun n => (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) y →
      ((|t - t1| ≤ (Real.log y) ^ (20 : ℕ) ∧
        exceptionalRepulsionRho * Real.log (Real.log y) ≤
          ((∑ p ∈ y.primesBelow, (1 : ℝ) / p) -
              Real.log (Real.log (|t - t1| + 2)) - 24) / 3 -
            pretentiousDistSq f
              (fun n => (n : ℂ) ^ (-(Complex.I * (t1 : ℂ)))) y) ∨
        (Real.log y) ^ (20 : ℕ) < |t - t1|) →
      exceptionalRepulsionRho * Real.log (Real.log y) ≤
        pretentiousDistSq f
          (fun n => (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) y := by
  obtain ⟨y0, hfar⟩ :=
    (FarRegimeRepulsionAssumption.bound :
      ∃ y0 : ℕ, ∀ (f : ℕ → ℂ) (y : ℕ) (t1 t : ℝ), _)
  refine ⟨y0, ?_⟩
  intro f y t1 t hf hy0 hy ht1 ht hsep hmin hsplit
  rcases hsplit with ⟨hmid, hfit⟩ | hfarRange
  · exact pretentiousDistSq_archTwist_ge_mid f hf t1 t y hy hsep
      (pretentiousDistSq f
        (fun n => (n : ℂ) ^ (-(Complex.I * (t1 : ℂ)))) y)
      le_rfl hfit
  · exact hfar f y t1 t hf hy0 hy ht1 ht hmin hfarRange

end Tao2015

end MoltResearch
