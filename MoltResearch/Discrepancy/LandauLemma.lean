import MoltResearch.Discrepancy.ZetaBound
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives

/-!
# Track C: the Landau lemma substrate (Track R, campaign #3044, phase P3)

The road to the zero-free region: dividing analytic functions by their roots,
counting roots by the max-modulus principle (the Jensen-free quarter-ball
argument: roots confined to `B(s₀, R/4)` with the boundary at `R` cost a
modulus factor `≥ 3` each, so the count is `≤ M/log 3` outright), and the
Borel–Carathéodory bound on the root-free part — culminating in Landau's
inequality `-Re f'/f(s₀) ≤ C·M/R - ∑ Re 1/(s₀-ρ)`.

This file works with `ℂ → ℂ` throughout; `•` is `*`.
-/

namespace MoltResearch

namespace ExpSums

open Complex

/-- A point where an analytic function vanishes to finite positive order splits
off one linear factor **globally on any open set**: `f = (· - ρ) * g` with `g`
analytic on all of `U`.  (The local factorization from `analyticOrderAt` is
patched together with `f/(· - ρ)` away from `ρ`.) -/
theorem exists_analyticOnNhd_factor_of_zero {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) {ρ : ℂ} (hρ : ρ ∈ U)
    (h0 : f ρ = 0) (hord : analyticOrderAt f ρ ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ ∀ z ∈ U, f z = (z - ρ) * g z := by
  classical
  have hfρ : AnalyticAt ℂ f ρ := hf ρ hρ
  -- the finite order and its local factorization
  obtain ⟨n, hn⟩ : ∃ n : ℕ, analyticOrderAt f ρ = n :=
    ⟨(analyticOrderAt f ρ).toNat, (ENat.coe_toNat hord).symm⟩
  obtain ⟨g₀, hg₀an, hg₀ne, hg₀ev⟩ := (hfρ.analyticOrderAt_eq_natCast).mp hn
  have hn1 : 1 ≤ n := by
    by_contra h
    push_neg at h
    interval_cases n
    have h1 : f ρ = (ρ - ρ) ^ 0 • g₀ ρ := hg₀ev.self_of_nhds
    rw [h0] at h1
    simp at h1
    exact hg₀ne h1.symm
  -- the global quotient, patched at `ρ`
  set g : ℂ → ℂ := fun z =>
    if z = ρ then (0 : ℂ) ^ (n - 1) * g₀ ρ else f z / (z - ρ) with hg_def
  refine ⟨g, ?_, ?_⟩
  · -- analyticity: away from `ρ` by division, at `ρ` by congruence with the
    -- local factor `(· - ρ)^{n-1} * g₀`
    intro w hw
    rcases eq_or_ne w ρ with hwρ | hwρ
    · subst hwρ
      have hloc : AnalyticAt ℂ (fun z => (z - w) ^ (n - 1) * g₀ z) w := by
        exact ((analyticAt_id.sub analyticAt_const).pow _).mul hg₀an
      refine hloc.congr ?_
      have hev : ∀ᶠ z in nhds w, f z = (z - w) ^ n • g₀ z := hg₀ev
      filter_upwards [hev] with z hz
      rcases eq_or_ne z w with hzw | hzw
      · subst hzw
        simp only [hg_def, if_pos rfl, sub_self, smul_eq_mul]
      · simp only [hg_def, if_neg hzw]
        rw [hz, smul_eq_mul]
        have hzw' : z - w ≠ 0 := sub_ne_zero.mpr hzw
        have hsplit : (z - w) ^ n = (z - w) * (z - w) ^ (n - 1) := by
          conv_lhs => rw [show n = 1 + (n - 1) from by omega]
          rw [pow_add, pow_one]
        rw [hsplit]
        field_simp
    · have hden : AnalyticAt ℂ (fun z => z - ρ) w :=
        analyticAt_id.sub analyticAt_const
      have hdiv : AnalyticAt ℂ (fun z => f z / (z - ρ)) w :=
        (hf w hw).div hden (sub_ne_zero.mpr hwρ)
      refine hdiv.congr ?_
      have hopen : IsOpen {z : ℂ | z ≠ ρ} := isOpen_ne
      filter_upwards [hopen.mem_nhds hwρ] with z hz
      simp only [hg_def, if_neg hz]
  · -- the factorization identity on `U`
    intro z _
    rcases eq_or_ne z ρ with hzρ | hzρ
    · subst hzρ
      rw [h0, sub_self, zero_mul]
    · simp only [hg_def, if_neg hzρ]
      have hzρ' : z - ρ ≠ 0 := sub_ne_zero.mpr hzρ
      field_simp

end ExpSums

end MoltResearch
