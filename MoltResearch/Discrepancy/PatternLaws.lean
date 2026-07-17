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

/-- The residue-class dictionary: the `ZMod`-level fiber is the `%`-level class. -/
theorem filter_natCast_zmod_eq {P : ℕ} [NeZero P] (r : ZMod P) (s : Finset ℕ) :
    s.filter (fun n => ((n : ℕ) : ZMod P) = r)
      = s.filter (fun n => n % P = r.val) := by
  refine Finset.filter_congr fun n _ => ?_
  constructor
  · intro h
    rw [← h, ZMod.val_natCast]
  · intro h
    have hcast : ((n : ℕ) : ZMod P) = ((n % P : ℕ) : ZMod P) := by
      rw [ZMod.natCast_mod]
    rw [hcast, h, ZMod.natCast_val, ZMod.cast_id]

/-- **Per-point mass bound for the residue law**: near-uniformity of `𝐧 mod P`
(the finitary (hayah)), normalized. -/
theorem residueLaw_le {P : ℕ} [NeZero P] (hP : 2 ≤ P) {A B : ℕ}
    (h4P : 4 * P ≤ A) (hPB : P * (A + 1) ≤ B) (r : ZMod P) :
    residueLaw P A B r
      ≤ 1 / P + (2 / P + (2 * Real.log (2 * P) + 2) / P)
          / ∑ n ∈ Finset.Ioc A B, (1 : ℝ) / n := by
  classical
  have hP0 : 0 < P := by omega
  have hA1 : 1 ≤ A := by omega
  have hAB : A < B := by
    have h1 : 2 * (A + 1) ≤ P * (A + 1) := Nat.mul_le_mul_right _ hP
    omega
  have hSpos : (0 : ℝ) < ∑ n ∈ Finset.Ioc A B, (1 : ℝ) / n := by
    refine Finset.sum_pos (fun m hm => ?_) ⟨A + 1, by rw [Finset.mem_Ioc]; omega⟩
    rw [Finset.mem_Ioc] at hm
    have : (0 : ℝ) < (m : ℝ) := by
      have : 1 ≤ m := by omega
      exact_mod_cast this
    positivity
  have hval : residueLaw P A B r
      = (∑ n ∈ (Finset.Ioc A B).filter (fun n => n % P = r.val), (1 : ℝ) / n)
        / ∑ n ∈ Finset.Ioc A B, (1 : ℝ) / n := by
    rw [residueLaw, pushWeight, filter_natCast_zmod_eq]
    rw [div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [logWeight, div_eq_mul_inv]
  have hrval : r.val < P := ZMod.val_lt r
  have hE := abs_sum_one_div_residue_sub_le hP hrval h4P hPB
  have hclass : ∑ n ∈ (Finset.Ioc A B).filter (fun n => n % P = r.val), (1 : ℝ) / n
      ≤ (1 / P) * (∑ n ∈ Finset.Ioc A B, (1 : ℝ) / n)
        + (2 * r.val / P ^ 2 + (2 * Real.log (2 * P) + 2) / P) := by
    have h2 := (abs_le.mp hE).2
    linarith
  have hEbound : 2 * (r.val : ℝ) / P ^ 2 + (2 * Real.log (2 * P) + 2) / P
      ≤ 2 / P + (2 * Real.log (2 * P) + 2) / P := by
    have hrP : (r.val : ℝ) ≤ (P : ℝ) := by exact_mod_cast le_of_lt hrval
    have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP0
    have h1 : 2 * (r.val : ℝ) / P ^ 2 ≤ 2 * (P : ℝ) / P ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h2 : 2 * (P : ℝ) / P ^ 2 = 2 / P := by
      rw [pow_two]
      rw [mul_comm (P:ℝ) (P:ℝ), ← div_div]
      rw [mul_div_assoc, div_self (by positivity : (P:ℝ) ≠ 0), mul_one]
    linarith
  rw [hval, div_le_iff₀ hSpos]
  have hgoal : (1 / (P : ℝ) + (2 / P + (2 * Real.log (2 * P) + 2) / P)
        / ∑ n ∈ Finset.Ioc A B, (1 : ℝ) / n)
      * (∑ n ∈ Finset.Ioc A B, (1 : ℝ) / n)
      = (1 / P) * (∑ n ∈ Finset.Ioc A B, (1 : ℝ) / n)
        + (2 / P + (2 * Real.log (2 * P) + 2) / P) := by
    field_simp
  rw [hgoal]
  linarith [hclass, hEbound]

/-- **The residue entropy is near-full** (eq. (hayah)):
`H(𝐧 mod P) ≥ log P − P·E/S`. -/
theorem le_shannonEntropy_residueLaw {P : ℕ} [NeZero P] (hP : 2 ≤ P) {A B : ℕ}
    (h4P : 4 * P ≤ A) (hPB : P * (A + 1) ≤ B) :
    Real.log P
      - (P : ℝ) * ((2 / P + (2 * Real.log (2 * P) + 2) / P)
          / ∑ n ∈ Finset.Ioc A B, (1 : ℝ) / n)
      ≤ shannonEntropy (residueLaw P A B) := by
  classical
  have hP0 : 0 < P := by omega
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP0
  have hA1 : 1 ≤ A := by omega
  have hAB : A < B := by
    have h1 : 2 * (A + 1) ≤ P * (A + 1) := Nat.mul_le_mul_right _ hP
    omega
  have hSpos : (0 : ℝ) < ∑ n ∈ Finset.Ioc A B, (1 : ℝ) / n := by
    refine Finset.sum_pos (fun m hm => ?_) ⟨A + 1, by rw [Finset.mem_Ioc]; omega⟩
    rw [Finset.mem_Ioc] at hm
    have : (0 : ℝ) < (m : ℝ) := by
      have : 1 ≤ m := by omega
      exact_mod_cast this
    positivity
  set E : ℝ := (2 / (P : ℝ) + (2 * Real.log (2 * P) + 2) / P)
      / ∑ n ∈ Finset.Ioc A B, (1 : ℝ) / n with hEdef
  have hE0 : 0 ≤ E := by
    rw [hEdef]
    have hP1 : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP0
    have hlog : (0 : ℝ) ≤ Real.log (2 * (P : ℝ)) := by
      refine Real.log_nonneg ?_
      linarith
    positivity
  have hc0 : (0 : ℝ) < 1 / (P : ℝ) + E := by positivity
  have hfloor := le_shannonEntropy_of_forall_le
    (fun r => residueLaw_nonneg P A B r)
    (sum_residueLaw P hA1 hAB)
    hc0
    (fun r => residueLaw_le hP h4P hPB r)
  refine le_trans ?_ hfloor
  have hlogc : Real.log (1 / (P : ℝ) + E)
      ≤ Real.log (1 / (P : ℝ)) + (P : ℝ) * E := by
    have h1 : 1 / (P : ℝ) + E = (1 / P) * (1 + (P : ℝ) * E) := by
      field_simp
    rw [h1, Real.log_mul (by positivity) (by positivity)]
    have h2 : Real.log (1 + (P : ℝ) * E) ≤ (P : ℝ) * E := by
      have := Real.log_le_sub_one_of_pos
        (show (0 : ℝ) < 1 + (P : ℝ) * E by positivity)
      linarith
    linarith
  have hlogP : Real.log (1 / (P : ℝ)) = -Real.log P := by
    rw [one_div, Real.log_inv]
  linarith [hlogc]

/-- **Data processing for total variation**: pushing two weighted sets forward along
the same map cannot increase the total variation. -/
theorem tvDist_pushWeight_le (s : Finset ℕ) (v w : ℕ → ℝ) {β : Type*} [Fintype β]
    [DecidableEq β] (f : ℕ → β) :
    tvDist (pushWeight s v f) (pushWeight s w f) ≤ ∑ n ∈ s, |v n - w n| := by
  classical
  rw [tvDist]
  have hper : ∀ b, |pushWeight s v f b - pushWeight s w f b|
      ≤ ∑ n ∈ s.filter (fun n => f n = b), |v n - w n| := by
    intro b
    rw [pushWeight, pushWeight, ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  refine le_trans (Finset.sum_le_sum fun b _ => hper b) ?_
  rw [Finset.sum_fiberwise_of_maps_to (fun n _ => Finset.mem_univ (f n))
    (fun n => |v n - w n|)]

end MoltResearch
