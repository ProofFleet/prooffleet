import MoltResearch.Discrepancy.SingularSeries
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Discrepancy: L-function bounds for the character sums

Nucleus module for the Tao 2015 §4 analysis (`Problems/tao2015_derivation_c.md`, issue
#2871, PR E1): the `L`-function inputs of the non-principal character-sum estimate.

- `zetaWeightedSum_char_eq_LFunction`: the zeta-weighted sum of a Dirichlet character *is*
  the analytically-continued `L`-value at `σ > 1` (junk conventions align: both kill `n = 0`).
- `exists_norm_LFunction_le`: for non-principal `χ`, `‖L(χ, σ)‖` is uniformly bounded on
  `σ ∈ [1, 2]` — Mathlib's analytic continuation (`differentiable_LFunction`) plus
  compactness. This replaces the paper's "`L(s,χ₁)` is analytic near `s = 1`" remark.
- `exists_re_tsum_primes_char_le`: consequently the character prime sums
  `Re ∑'_p χ(p)/p^{1+1/log X}` are bounded uniformly in `X ≥ 3` — through the
  log-linearization of `SingularSeries.lean`, modulus-only (no branch-of-log issues).

The finitely-many-characters pattern (`NonPretentiousUniform.eventually_nonPretentiousAt`
style) lets §4 take a single constant over all `χ₁ mod r`, `r ∣ q^k`, since `q, k` are
fixed before `X`.
-/

namespace MoltResearch

open Finset

variable {N : ℕ} [NeZero N]

private lemma one_lt_log'' {X : ℝ} (hX : 3 ≤ X) : 1 < Real.log X := by
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    _ ≤ Real.log X := Real.log_le_log (by norm_num) hX

/-- The zeta-weighted sum of a Dirichlet character is the (analytically continued)
`L`-value, for real `σ > 1`. Junk conventions align: both sides vanish at `n = 0`. -/
theorem zetaWeightedSum_char_eq_LFunction (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) :
    zetaWeightedSum (fun n : ℕ => χ (n : ZMod N)) σ
      = DirichletCharacter.LFunction χ (σ : ℂ) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ (by simpa using hσ), LSeries, zetaWeightedSum]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, show (((0 : ℕ) : ℂ)) = 0 by norm_num,
      Complex.zero_cpow (Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans one_pos hσ))),
      div_zero]
  · rw [LSeries.term_of_ne_zero hn]

/-- **Uniform `L`-value bound near `s = 1`** for a non-principal character: `‖L(χ, σ)‖` is
bounded on the segment `σ ∈ [1, 2]`, by analytic continuation + compactness. -/
theorem exists_norm_LFunction_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ σ : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 →
      ‖DirichletCharacter.LFunction χ (σ : ℂ)‖ ≤ C := by
  have hcont : ContinuousOn (fun σ : ℝ => DirichletCharacter.LFunction χ (σ : ℂ))
      (Set.Icc (1 : ℝ) 2) :=
    ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal).continuousOn
  exact isCompact_Icc.exists_bound_of_continuousOn hcont

/-- **Bounded character prime sums** (the paper's "`log L(s, χ₁)` is bounded" input,
modulus-only form): for non-principal `χ`, the real part of the prime sum
`∑'_p χ(p)/p^{1 + 1/log X}` is bounded above uniformly in `X ≥ 3`.

Route: `∑' χ(n)/n^σ = L(χ, σ)` has bounded norm; `exp(Re T) = ‖L‖` for the Euler log sum
`T`; and `T` linearizes to the prime sum up to `1` (`norm_tsum_neg_log_euler_sub_le`). -/
theorem exists_re_tsum_primes_char_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ X : ℝ, 3 ≤ X →
      (∑' p : Nat.Primes,
          χ (((p : ℕ) : ℕ) : ZMod N)
            / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)).re ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_LFunction_le hχ
  refine ⟨Real.log (max C 1) + 2, ?_⟩
  intro X hX
  have hlog1 : 1 < Real.log X := one_lt_log'' hX
  have hβ0 : 0 < 1 / Real.log X := by positivity
  have hβ1 : 1 / Real.log X ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hσ1 : 1 < 1 + 1 / Real.log X := by linarith
  set gc : ℕ → ℂ := fun n => χ (n : ZMod N) with hgcdef
  have hmul : CompletelyMultiplicativeC gc := by
    intro a b _ _
    rw [hgcdef]
    dsimp only
    rw [Nat.cast_mul, map_mul]
  have hg1 : gc 1 = 1 := by
    rw [hgcdef]
    dsimp only
    rw [Nat.cast_one, map_one]
  have hb : ∀ n, ‖gc n‖ ≤ 1 := fun n => χ.norm_le_one _
  have hnorm := summable_norm_zetaWeight hb hσ1
  have hsumP : Summable fun p : Nat.Primes =>
      gc p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ) :=
    hnorm.of_norm.subtype {p | Nat.Prime p}
  have hE := EulerProduct.exp_tsum_primes_log_eq_tsum
    (f := hmul.zetaWeightHom hg1 (by linarith)) hnorm
  set T : ℂ := ∑' p : Nat.Primes,
    -Complex.log (1 - gc p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)) with hTdef
  set F : ℂ := ∑' p : Nat.Primes,
    gc p / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ) with hFdef
  have hexpT : Real.exp T.re = ‖zetaWeightedSum gc (1 + 1 / Real.log X)‖ := by
    rw [← Complex.norm_exp, hTdef]
    exact congrArg norm hE
  have hLnorm : ‖zetaWeightedSum gc (1 + 1 / Real.log X)‖ ≤ max C 1 := by
    rw [hgcdef, zetaWeightedSum_char_eq_LFunction χ hσ1]
    refine le_trans (hC _ ⟨by linarith, by linarith⟩) (le_max_left C 1)
  have hTre : T.re ≤ Real.log (max C 1) := by
    have h1 : Real.exp T.re ≤ max C 1 := hexpT ▸ hLnorm
    calc T.re = Real.log (Real.exp T.re) := (Real.log_exp _).symm
      _ ≤ Real.log (max C 1) := Real.log_le_log (Real.exp_pos _) h1
  have habs : |T.re - F.re| ≤ 1 := by
    calc |T.re - F.re| = |(T - F).re| := by rw [Complex.sub_re]
      _ ≤ ‖T - F‖ := Complex.abs_re_le_norm _
      _ ≤ 1 := norm_tsum_neg_log_euler_sub_le hb hσ1
  have h2 := (abs_le.mp habs).1
  have : F.re ≤ Real.log (max C 1) + 1 := by linarith
  calc (∑' p : Nat.Primes,
        χ (((p : ℕ) : ℕ) : ZMod N)
          / ((p : ℕ) : ℂ) ^ ((1 + 1 / Real.log X : ℝ) : ℂ)).re
      = F.re := rfl
    _ ≤ Real.log (max C 1) + 1 := this
    _ ≤ Real.log (max C 1) + 2 := by linarith

end MoltResearch
