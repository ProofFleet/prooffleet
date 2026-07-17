import MoltResearch.Discrepancy.LogUniformDist
import MoltResearch.Discrepancy.Discretize
import MoltResearch.Discrepancy.Entropy
import Mathlib.Data.ZMod.Basic

/-!
# Discrepancy: the pattern and residue laws

Track C, Elliott campaign (`Problems/tao2015_derivation_c.md`, issue #2946, E6c): the
random variables of the entropy decrement argument as pushforward weight functions —
`X_H` (the rounded `g`-pattern on a length-`H` window) and `Y` (`𝐧 mod P`), with
their joint. The E1 Shannon layer applies to these verbatim; the marginal
identifications connect the joint to its parts.
-/

namespace MoltResearch

open Finset

/-- The `H`-window pattern alphabet — finite and decidable. -/
abbrev PatternSpace (K H : ℕ) := Fin H → Fin (K + 1) × Fin (K + 1)

/-- The pattern map: the rounded `g`-values on the window `(n, n+H]`. -/
noncomputable def patternMap (g : ℕ → ℂ) (K H : ℕ) : ℕ → PatternSpace K H :=
  fun n => fun i => roundC K (g (n + 1 + i))

/-- The law of `X_H`. -/
noncomputable def patternLaw (g : ℕ → ℂ) (K H A B : ℕ) : PatternSpace K H → ℝ :=
  pushWeight (Finset.Ioc A B) (logWeight A B) (patternMap g K H)

/-- The law of `Y = 𝐧 mod P`. -/
noncomputable def residueLaw (P A B : ℕ) [NeZero P] : ZMod P → ℝ :=
  pushWeight (Finset.Ioc A B) (logWeight A B) (fun n => (n : ZMod P))

/-- The joint law of `(X_H, Y)`. -/
noncomputable def jointLaw (g : ℕ → ℂ) (K H P A B : ℕ) [NeZero P] :
    PatternSpace K H × ZMod P → ℝ :=
  pushWeight (Finset.Ioc A B) (logWeight A B)
    (fun n => (patternMap g K H n, (n : ZMod P)))

theorem patternLaw_nonneg (g : ℕ → ℂ) (K H A B : ℕ) (x : PatternSpace K H) :
    0 ≤ patternLaw g K H A B x :=
  pushWeight_nonneg (fun n _ => logWeight_nonneg A B n) _ x

theorem residueLaw_nonneg (P A B : ℕ) [NeZero P] (r : ZMod P) :
    0 ≤ residueLaw P A B r :=
  pushWeight_nonneg (fun n _ => logWeight_nonneg A B n) _ r

theorem jointLaw_nonneg (g : ℕ → ℂ) (K H P A B : ℕ) [NeZero P]
    (x : PatternSpace K H × ZMod P) : 0 ≤ jointLaw g K H P A B x :=
  pushWeight_nonneg (fun n _ => logWeight_nonneg A B n) _ x

theorem sum_patternLaw (g : ℕ → ℂ) (K H : ℕ) {A B : ℕ} (hA : 1 ≤ A) (hAB : A < B) :
    ∑ x, patternLaw g K H A B x = 1 := by
  rw [patternLaw, sum_pushWeight, sum_logWeight hA hAB]

theorem sum_residueLaw (P : ℕ) [NeZero P] {A B : ℕ} (hA : 1 ≤ A) (hAB : A < B) :
    ∑ r, residueLaw P A B r = 1 := by
  rw [residueLaw, sum_pushWeight, sum_logWeight hA hAB]

theorem sum_jointLaw (g : ℕ → ℂ) (K H P : ℕ) [NeZero P] {A B : ℕ}
    (hA : 1 ≤ A) (hAB : A < B) :
    ∑ x, jointLaw g K H P A B x = 1 := by
  rw [jointLaw, sum_pushWeight, sum_logWeight hA hAB]

/-- The first marginal of the joint is the pattern law. -/
theorem marginal₁_jointLaw (g : ℕ → ℂ) (K H P A B : ℕ) [NeZero P] :
    marginal₁ (jointLaw g K H P A B) = patternLaw g K H A B := by
  classical
  funext a
  rw [show marginal₁ (jointLaw g K H P A B) a
      = ∑ b, jointLaw g K H P A B (a, b) from rfl]
  rw [show patternLaw g K H A B a
      = ∑ n ∈ (Finset.Ioc A B).filter (fun n => patternMap g K H n = a),
          logWeight A B n from rfl]
  rw [show (∑ b, jointLaw g K H P A B (a, b))
      = ∑ b, ∑ n ∈ (Finset.Ioc A B).filter
          (fun n => (patternMap g K H n, ((n : ZMod P))) = (a, b)),
          logWeight A B n from Finset.sum_congr rfl fun b _ => rfl]
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun n => ((n : ℕ) : ZMod P))
    (s := (Finset.Ioc A B).filter (fun n => patternMap g K H n = a))
    (fun n _ => Finset.mem_univ _) (logWeight A B)]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ext n
  simp only [Finset.mem_filter, Prod.mk.injEq, and_assoc]

/-- The second marginal of the joint is the residue law. -/
theorem marginal₂_jointLaw (g : ℕ → ℂ) (K H P A B : ℕ) [NeZero P] :
    marginal₂ (jointLaw g K H P A B) = residueLaw P A B := by
  classical
  funext b
  rw [show marginal₂ (jointLaw g K H P A B) b
      = ∑ a, jointLaw g K H P A B (a, b) from rfl]
  rw [show residueLaw P A B b
      = ∑ n ∈ (Finset.Ioc A B).filter (fun n => ((n : ℕ) : ZMod P) = b),
          logWeight A B n from rfl]
  rw [show (∑ a, jointLaw g K H P A B (a, b))
      = ∑ a, ∑ n ∈ (Finset.Ioc A B).filter
          (fun n => (patternMap g K H n, ((n : ZMod P))) = (a, b)),
          logWeight A B n from Finset.sum_congr rfl fun a _ => rfl]
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun n => patternMap g K H n)
    (s := (Finset.Ioc A B).filter (fun n => ((n : ℕ) : ZMod P) = b))
    (fun n _ => Finset.mem_univ _) (logWeight A B)]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  ext n
  simp only [Finset.mem_filter, Prod.mk.injEq, and_assoc]
  tauto

end MoltResearch
