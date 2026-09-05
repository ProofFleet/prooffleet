import MoltResearch.Discrepancy.Repulsion

/-!
# The minimizing frequency and the mid-range repulsion leg

This leaf isolates the in-tree part of the exceptional `t₁` split.  The
pretentious distance to an archimedean twist is continuous in the frequency,
so it attains a minimum on a compact band.  Away from that minimizer, the
existing zeta-repulsion theorem gives the mid-range distance floor whenever
its displayed numerical remainder fits.
-/

namespace MoltResearch

open Finset

/-- The fixed exponent used for the exceptional non-pretentiousness gain. -/
noncomputable def exceptionalRepulsionRho : ℝ :=
  1 / 6 - 1 / (3 * Real.pi)

theorem exceptionalRepulsionRho_pos : 0 < exceptionalRepulsionRho := by
  unfold exceptionalRepulsionRho
  apply sub_pos.mpr
  rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 3 * Real.pi)
    (by norm_num : (0 : ℝ) < 6)]
  nlinarith [Real.pi_gt_three]

/-- The squared pretentious distance to `n ↦ n⁻ⁱᵗ` varies continuously in
the real frequency `t`. -/
theorem continuous_pretentiousDistSq_archTwist (f : ℕ → ℂ) (y : ℕ) :
    Continuous (fun t : ℝ =>
      pretentiousDistSq f
        (fun n => (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) y) := by
  unfold pretentiousDistSq
  refine continuous_finset_sum _ fun p hp => ?_
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.prime_of_mem_primesBelow hp).ne_zero
  letI : NeZero ((p : ℕ) : ℂ) := ⟨hp0⟩
  fun_prop

/-- The twisted distance attains its minimum on every nonempty symmetric
frequency band. -/
theorem exists_pretentiousDistSq_archTwist_minimizer
    (f : ℕ → ℂ) (y : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ t1 ∈ Set.Icc (-T) T, ∀ t ∈ Set.Icc (-T) T,
      pretentiousDistSq f
          (fun n => (n : ℂ) ^ (-(Complex.I * (t1 : ℂ)))) y ≤
        pretentiousDistSq f
          (fun n => (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) y := by
  obtain ⟨t1, ht1, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr (by linarith : -T ≤ T))
    (continuous_pretentiousDistSq_archTwist f y).continuousOn
  exact ⟨t1, ht1, fun t ht => hmin ht⟩

/-- The existing repulsion theorem supplies the complete mid-range branch.
The hypothesis `hfit` is deliberately the exact residual numerical inequality:
later schedules may discharge it without exposing transcendental arithmetic to
the analytic theorem. -/
theorem pretentiousDistSq_archTwist_ge_mid
    (f : ℕ → ℂ) (hf : Unimodular f) (t1 t : ℝ) (y : ℕ)
    (hy : 3 ≤ y) (hsep : 6 ≤ |t - t1|) (A : ℝ)
    (hA : pretentiousDistSq f
      (fun n => (n : ℂ) ^ (-(Complex.I * (t1 : ℂ)))) y ≤ A)
    (hfit : exceptionalRepulsionRho * Real.log (Real.log y) ≤
      ((∑ p ∈ y.primesBelow, (1 : ℝ) / p) -
          Real.log (Real.log (|t - t1| + 2)) - 24) / 3 - A) :
    exceptionalRepulsionRho * Real.log (Real.log y) ≤
      pretentiousDistSq f
        (fun n => (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) y := by
  exact hfit.trans (pretentiousDistSq_twist_ge f hf t1 t y hy hsep A hA)

end MoltResearch
