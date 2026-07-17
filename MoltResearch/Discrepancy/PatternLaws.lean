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

/-- Reindexing: pushing the `s`-shifted map from `(A, B]` is pushing the original
map from the shifted window `(A+s, B+s]` with shifted weights. -/
theorem pushWeight_shift_eq (A B s : ℕ) (w : ℕ → ℝ) {β : Type*} [Fintype β]
    [DecidableEq β] (f : ℕ → β) :
    pushWeight (Finset.Ioc A B) w (fun n => f (n + s))
      = pushWeight (Finset.Ioc (A + s) (B + s)) (fun m => w (m - s)) f := by
  funext b
  rw [pushWeight, pushWeight, ← Finset.map_add_right_Ioc, Finset.filter_map,
    Finset.sum_map]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [addRightEmbedding_apply]
  rw [Nat.add_sub_cancel]

/-- Pushing an indicator-extended weight from a superset is pushing the original
weight from the subset. -/
theorem pushWeight_extend {s t : Finset ℕ} (hst : s ⊆ t) (w : ℕ → ℝ)
    {β : Type*} [Fintype β] [DecidableEq β] (f : ℕ → β) :
    pushWeight t (fun n => if n ∈ s then w n else 0) f = pushWeight s w f := by
  funext b
  rw [pushWeight, pushWeight, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun n _ => rfl
  ext n
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨-, hfb⟩, hns⟩
    exact ⟨hns, hfb⟩
  · rintro ⟨hns, hfb⟩
    exact ⟨⟨hst hns, hfb⟩, hns⟩

/-- **Shift near-invariance of log-uniform pushforwards**: shifting the sampled
point by `s` moves the pushed law by at most `3s/(A·S)` in total variation,
where `S` is the log-mass of the window `(A, B]`. Two boundary strips of `s`
points each cost `s/(A·S)`; the interior telescopes to a third. -/
theorem tvDist_pushWeight_logWeight_shift_le {A B s : ℕ} (hA : 1 ≤ A)
    (h2s : A + s + s < B) {β : Type*} [Fintype β] [DecidableEq β] (f : ℕ → β) :
    tvDist (pushWeight (Finset.Ioc A B) (logWeight A B) (fun n => f (n + s)))
        (pushWeight (Finset.Ioc A B) (logWeight A B) f)
      ≤ 3 * s / (A * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m) := by
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hSpos : (0 : ℝ) < ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m := by
    refine Finset.sum_pos (fun m hm => ?_) ⟨A + 1, by rw [Finset.mem_Ioc]; omega⟩
    rw [Finset.mem_Ioc] at hm
    have h1 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    positivity
  have hsub1 : Finset.Ioc (A + s) (B + s) ⊆ Finset.Ioc A (B + s) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn ⊢
    omega
  have hsub2 : Finset.Ioc A B ⊆ Finset.Ioc A (B + s) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn ⊢
    omega
  rw [pushWeight_shift_eq,
    ← pushWeight_extend hsub1 (fun m => logWeight A B (m - s)) f,
    ← pushWeight_extend hsub2 (logWeight A B) f]
  refine le_trans (tvDist_pushWeight_le (Finset.Ioc A (B + s)) _ _ f) ?_
  -- the left boundary strip `(A, A+s]`
  have hP1 : ∑ n ∈ Finset.Ioc A (A + s),
      |(if n ∈ Finset.Ioc (A + s) (B + s) then logWeight A B (n - s) else 0)
        - (if n ∈ Finset.Ioc A B then logWeight A B n else 0)|
      ≤ s * (1 / (A * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m)) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _
      (1 / ((A : ℝ) * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m)) fun n hn => ?_) ?_
    · rw [Finset.mem_Ioc] at hn
      rw [if_neg (by rw [Finset.mem_Ioc]; omega),
        if_pos (by rw [Finset.mem_Ioc]; omega), zero_sub, abs_neg,
        abs_of_nonneg (logWeight_nonneg A B n), logWeight, div_div]
      refine one_div_le_one_div_of_le (mul_pos hApos hSpos) ?_
      have hAn : (A : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1.le
      exact mul_le_mul_of_nonneg_right hAn hSpos.le
    · rw [Nat.card_Ioc, nsmul_eq_mul]
      have hcard : A + s - A = s := by omega
      rw [hcard]
  -- the right boundary strip `(B, B+s]`
  have hP3 : ∑ n ∈ Finset.Ioc B (B + s),
      |(if n ∈ Finset.Ioc (A + s) (B + s) then logWeight A B (n - s) else 0)
        - (if n ∈ Finset.Ioc A B then logWeight A B n else 0)|
      ≤ s * (1 / (A * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m)) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _
      (1 / ((A : ℝ) * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m)) fun n hn => ?_) ?_
    · rw [Finset.mem_Ioc] at hn
      rw [if_pos (by rw [Finset.mem_Ioc]; omega),
        if_neg (by rw [Finset.mem_Ioc]; omega), sub_zero,
        abs_of_nonneg (logWeight_nonneg A B (n - s)), logWeight, div_div]
      refine one_div_le_one_div_of_le (mul_pos hApos hSpos) ?_
      have hAn : (A : ℝ) ≤ ((n - s : ℕ) : ℝ) := by
        exact_mod_cast (by omega : A ≤ n - s)
      exact mul_le_mul_of_nonneg_right hAn hSpos.le
    · rw [Nat.card_Ioc, nsmul_eq_mul]
      have hcard : B + s - B = s := by omega
      rw [hcard]
  -- the interior `(A+s, B]`: exact difference of shifted harmonic sums
  have hP2 : ∑ n ∈ Finset.Ioc (A + s) B,
      |(if n ∈ Finset.Ioc (A + s) (B + s) then logWeight A B (n - s) else 0)
        - (if n ∈ Finset.Ioc A B then logWeight A B n else 0)|
      ≤ s * (1 / (A * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m)) := by
    have hFeq : ∀ n ∈ Finset.Ioc (A + s) B,
        |(if n ∈ Finset.Ioc (A + s) (B + s) then logWeight A B (n - s) else 0)
          - (if n ∈ Finset.Ioc A B then logWeight A B n else 0)|
        = (1 / ((n - s : ℕ) : ℝ) - 1 / (n : ℝ))
            * (1 / ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m) := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      have hns : (0 : ℝ) < ((n - s : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < n - s)
      have hmono : (1 : ℝ) / (n : ℝ) ≤ 1 / ((n - s : ℕ) : ℝ) :=
        one_div_le_one_div_of_le hns (by exact_mod_cast Nat.sub_le n s)
      rw [if_pos (by rw [Finset.mem_Ioc]; omega),
        if_pos (by rw [Finset.mem_Ioc]; omega), logWeight, logWeight,
        div_sub_div_same,
        abs_of_nonneg (div_nonneg (sub_nonneg.mpr hmono) hSpos.le),
        div_eq_mul_one_div]
    calc ∑ n ∈ Finset.Ioc (A + s) B,
        |(if n ∈ Finset.Ioc (A + s) (B + s) then logWeight A B (n - s) else 0)
          - (if n ∈ Finset.Ioc A B then logWeight A B n else 0)|
        = ∑ n ∈ Finset.Ioc (A + s) B, (1 / ((n - s : ℕ) : ℝ) - 1 / (n : ℝ))
            * (1 / ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m) :=
          Finset.sum_congr rfl hFeq
      _ = ((∑ n ∈ Finset.Ioc (A + s) B, 1 / ((n - s : ℕ) : ℝ))
            - ∑ n ∈ Finset.Ioc (A + s) B, 1 / (n : ℝ))
            * (1 / ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m) := by
          rw [← Finset.sum_mul, Finset.sum_sub_distrib]
      _ ≤ (s * (1 / (A : ℝ))) * (1 / ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m) := by
          refine mul_le_mul_of_nonneg_right ?_ (one_div_nonneg.mpr hSpos.le)
          have hreidx : ∑ n ∈ Finset.Ioc (A + s) B, 1 / ((n - s : ℕ) : ℝ)
              = ∑ m ∈ Finset.Ioc A (B - s), 1 / (m : ℝ) := by
            have hmap : Finset.Ioc (A + s) B
                = (Finset.Ioc A (B - s)).map (addRightEmbedding s) := by
              have hBs : B - s + s = B := by omega
              rw [Finset.map_add_right_Ioc, hBs]
            rw [hmap, Finset.sum_map]
            refine Finset.sum_congr rfl fun m _ => ?_
            simp only [addRightEmbedding_apply]
            rw [Nat.add_sub_cancel]
          have hsplitL : ∑ m ∈ Finset.Ioc A (B - s), (1 : ℝ) / m
              = ∑ m ∈ Finset.Ioc A (A + s), (1 : ℝ) / m
                + ∑ m ∈ Finset.Ioc (A + s) (B - s), (1 : ℝ) / m :=
            (Finset.sum_Ioc_consecutive _ (by omega) (by omega)).symm
          have hsplitR : ∑ n ∈ Finset.Ioc (A + s) B, (1 : ℝ) / n
              = ∑ n ∈ Finset.Ioc (A + s) (B - s), (1 : ℝ) / n
                + ∑ n ∈ Finset.Ioc (B - s) B, (1 : ℝ) / n :=
            (Finset.sum_Ioc_consecutive _ (by omega) (by omega)).symm
          have hedge : ∑ m ∈ Finset.Ioc A (A + s), (1 : ℝ) / m
              ≤ s * (1 / (A : ℝ)) := by
            refine le_trans (Finset.sum_le_card_nsmul _ _ (1 / (A : ℝ))
              fun m hm => ?_) ?_
            · rw [Finset.mem_Ioc] at hm
              exact one_div_le_one_div_of_le hApos (by exact_mod_cast hm.1.le)
            · rw [Nat.card_Ioc, nsmul_eq_mul]
              have hcard : A + s - A = s := by omega
              rw [hcard]
          have hpos3 : 0 ≤ ∑ n ∈ Finset.Ioc (B - s) B, (1 : ℝ) / n :=
            Finset.sum_nonneg fun n _ => by positivity
          rw [hreidx, hsplitL, hsplitR]
          linarith
      _ = s * (1 / (A * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m)) := by
          ring
  have hU1 : ∑ n ∈ Finset.Ioc A B,
        |(if n ∈ Finset.Ioc (A + s) (B + s) then logWeight A B (n - s) else 0)
          - (if n ∈ Finset.Ioc A B then logWeight A B n else 0)|
      + ∑ n ∈ Finset.Ioc B (B + s),
        |(if n ∈ Finset.Ioc (A + s) (B + s) then logWeight A B (n - s) else 0)
          - (if n ∈ Finset.Ioc A B then logWeight A B n else 0)|
      = ∑ n ∈ Finset.Ioc A (B + s),
        |(if n ∈ Finset.Ioc (A + s) (B + s) then logWeight A B (n - s) else 0)
          - (if n ∈ Finset.Ioc A B then logWeight A B n else 0)| :=
    Finset.sum_Ioc_consecutive _ (by omega) (by omega)
  have hU2 : ∑ n ∈ Finset.Ioc A (A + s),
        |(if n ∈ Finset.Ioc (A + s) (B + s) then logWeight A B (n - s) else 0)
          - (if n ∈ Finset.Ioc A B then logWeight A B n else 0)|
      + ∑ n ∈ Finset.Ioc (A + s) B,
        |(if n ∈ Finset.Ioc (A + s) (B + s) then logWeight A B (n - s) else 0)
          - (if n ∈ Finset.Ioc A B then logWeight A B n else 0)|
      = ∑ n ∈ Finset.Ioc A B,
        |(if n ∈ Finset.Ioc (A + s) (B + s) then logWeight A B (n - s) else 0)
          - (if n ∈ Finset.Ioc A B then logWeight A B n else 0)| :=
    Finset.sum_Ioc_consecutive _ (by omega) (by omega)
  have hring : 3 * ((s : ℝ) * (1 / (A * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m)))
      = 3 * s / (A * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m) := by
    ring
  rw [← hU1, ← hU2]
  linarith

/-- Shift near-invariance of the pattern law, the form consumed by the decrement's
approximate subadditivity. -/
theorem tvDist_patternLaw_shift_le (g : ℕ → ℂ) (K H : ℕ) {A B s : ℕ}
    (hA : 1 ≤ A) (h2s : A + s + s < B) :
    tvDist (pushWeight (Finset.Ioc A B) (logWeight A B)
        (fun n => patternMap g K H (n + s)))
      (patternLaw g K H A B)
      ≤ 3 * s / (A * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m) := by
  rw [patternLaw]
  exact tvDist_pushWeight_logWeight_shift_le hA h2s (patternMap g K H)

/-- Pushforward along an equiv-composed map is relabeling the pushforward. -/
theorem pushWeight_equiv_comp (s : Finset ℕ) (w : ℕ → ℝ) {β γ : Type*}
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (φ : ℕ → β) (e : β ≃ γ) (c : γ) :
    pushWeight s w (fun n => e (φ n)) c = pushWeight s w φ (e.symm c) := by
  rw [pushWeight, pushWeight]
  refine Finset.sum_congr ?_ fun n _ => rfl
  ext n
  simp only [Finset.mem_filter, Equiv.eq_symm_apply]

/-- Relabeling the alphabet by an equiv does not change the entropy of a
pushforward law. -/
theorem shannonEntropy_pushWeight_equiv (s : Finset ℕ) (w : ℕ → ℝ) {β γ : Type*}
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (φ : ℕ → β) (e : β ≃ γ) :
    shannonEntropy (pushWeight s w (fun n => e (φ n)))
      = shannonEntropy (pushWeight s w φ) := by
  have h : pushWeight s w (fun n => e (φ n))
      = fun c => pushWeight s w φ (e.symm c) :=
    funext (pushWeight_equiv_comp s w φ e)
  rw [h, shannonEntropy_comp_equiv (pushWeight s w φ) e.symm]

/-- The first marginal of a paired pushforward is the pushforward of the first
component. -/
theorem marginal₁_pushWeight_pair (s : Finset ℕ) (w : ℕ → ℝ) {β γ : Type*}
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (φ : ℕ → β) (ψ : ℕ → γ) :
    marginal₁ (pushWeight s w (fun n => (φ n, ψ n))) = pushWeight s w φ := by
  classical
  funext a
  rw [show marginal₁ (pushWeight s w (fun n => (φ n, ψ n))) a
      = ∑ b, pushWeight s w (fun n => (φ n, ψ n)) (a, b) from rfl]
  rw [show pushWeight s w φ a
      = ∑ n ∈ s.filter (fun n => φ n = a), w n from rfl]
  rw [show (∑ b, pushWeight s w (fun n => (φ n, ψ n)) (a, b))
      = ∑ b, ∑ n ∈ s.filter (fun n => (φ n, ψ n) = (a, b)), w n
      from Finset.sum_congr rfl fun b _ => rfl]
  rw [← Finset.sum_fiberwise_of_maps_to (g := ψ)
    (s := s.filter (fun n => φ n = a)) (fun n _ => Finset.mem_univ _) w]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ext n
  simp only [Finset.mem_filter, Prod.mk.injEq, and_assoc]

/-- The second marginal of a paired pushforward is the pushforward of the second
component. -/
theorem marginal₂_pushWeight_pair (s : Finset ℕ) (w : ℕ → ℝ) {β γ : Type*}
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (φ : ℕ → β) (ψ : ℕ → γ) :
    marginal₂ (pushWeight s w (fun n => (φ n, ψ n))) = pushWeight s w ψ := by
  classical
  funext b
  rw [show marginal₂ (pushWeight s w (fun n => (φ n, ψ n))) b
      = ∑ a, pushWeight s w (fun n => (φ n, ψ n)) (a, b) from rfl]
  rw [show pushWeight s w ψ b
      = ∑ n ∈ s.filter (fun n => ψ n = b), w n from rfl]
  rw [show (∑ a, pushWeight s w (fun n => (φ n, ψ n)) (a, b))
      = ∑ a, ∑ n ∈ s.filter (fun n => (φ n, ψ n) = (a, b)), w n
      from Finset.sum_congr rfl fun a _ => rfl]
  rw [← Finset.sum_fiberwise_of_maps_to (g := φ)
    (s := s.filter (fun n => ψ n = b)) (fun n _ => Finset.mem_univ _) w]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  ext n
  simp only [Finset.mem_filter, Prod.mk.injEq, and_assoc]
  tauto

/-- A pushforward law never exceeds the total mass. -/
theorem pushWeight_le_sum {s : Finset ℕ} {w : ℕ → ℝ} (hw : ∀ n ∈ s, 0 ≤ w n)
    {β : Type*} [Fintype β] [DecidableEq β] (f : ℕ → β) (b : β) :
    pushWeight s w f b ≤ ∑ n ∈ s, w n := by
  rw [← sum_pushWeight s w f]
  exact Finset.single_le_sum (fun c _ => pushWeight_nonneg hw f c)
    (Finset.mem_univ b)

theorem patternLaw_le_one (g : ℕ → ℂ) (K H : ℕ) {A B : ℕ} (hA : 1 ≤ A)
    (hAB : A < B) (x : PatternSpace K H) : patternLaw g K H A B x ≤ 1 := by
  have h := pushWeight_le_sum (s := Finset.Ioc A B)
    (fun n _ => logWeight_nonneg A B n) (patternMap g K H) x
  rw [sum_logWeight hA hAB] at h
  rw [patternLaw]
  exact h

/-- Splitting a length-`(H₁+H₂)` pattern into its two halves. -/
def patternSplit (K H₁ H₂ : ℕ) :
    PatternSpace K (H₁ + H₂) ≃ PatternSpace K H₁ × PatternSpace K H₂ :=
  ((finSumFinEquiv.arrowCongr (Equiv.refl _)).symm).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

/-- The split of a pattern at `n` is the `H₁`-pattern at `n` paired with the
`H₂`-pattern at `n + H₁`: a long window is two consecutive short windows. -/
theorem patternSplit_patternMap (g : ℕ → ℂ) (K H₁ H₂ n : ℕ) :
    patternSplit K H₁ H₂ (patternMap g K (H₁ + H₂) n)
      = (patternMap g K H₁ n, patternMap g K H₂ (n + H₁)) := by
  refine Prod.ext ?_ ?_
  · funext i
    show patternMap g K (H₁ + H₂) n (finSumFinEquiv (Sum.inl i))
      = patternMap g K H₁ n i
    rw [finSumFinEquiv_apply_left, patternMap, patternMap]
    simp only [Fin.val_castAdd]
  · funext j
    show patternMap g K (H₁ + H₂) n (finSumFinEquiv (Sum.inr j))
      = patternMap g K H₂ (n + H₁) j
    rw [finSumFinEquiv_apply_right, patternMap, patternMap]
    simp only [Fin.val_natAdd]
    have harg : n + 1 + (H₁ + (j : ℕ)) = n + H₁ + 1 + (j : ℕ) := by omega
    rw [harg]

/-- **Approximate subadditivity of pattern entropy**: a long window's entropy is
at most the sum of its two halves' entropies plus the Fannes cost of the shift
`n ↦ n + H₁`, which vanishes as the window grows. This is the paper's
`H(X_{H₁+H₂}) ≤ H(X_{H₁}) + H(X_{H₂}) + o(1)`. -/
theorem shannonEntropy_patternLaw_add_le (g : ℕ → ℂ) (K H₁ H₂ : ℕ) {A B : ℕ}
    (hA : 1 ≤ A) (hH : A + H₁ + H₁ < B) :
    shannonEntropy (patternLaw g K (H₁ + H₂) A B)
      ≤ shannonEntropy (patternLaw g K H₁ A B)
        + shannonEntropy (patternLaw g K H₂ A B)
        + (2 * (Fintype.card (PatternSpace K H₂) : ℝ)
            * Real.sqrt (3 * H₁ / (A * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m))
          + 3 * H₁ / (A * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m)) := by
  classical
  have hAB : A < B := by omega
  -- relabel the long-window law along the splitting equivalence
  have hsplit_fun : (fun n => patternSplit K H₁ H₂ (patternMap g K (H₁ + H₂) n))
      = fun n => (patternMap g K H₁ n, patternMap g K H₂ (n + H₁)) := by
    funext n
    rw [patternSplit_patternMap]
  have hrelabel : shannonEntropy (patternLaw g K (H₁ + H₂) A B)
      = shannonEntropy (pushWeight (Finset.Ioc A B) (logWeight A B)
          (fun n => (patternMap g K H₁ n, patternMap g K H₂ (n + H₁)))) := by
    rw [patternLaw, ← shannonEntropy_pushWeight_equiv (Finset.Ioc A B)
      (logWeight A B) (patternMap g K (H₁ + H₂)) (patternSplit K H₁ H₂),
      hsplit_fun]
  -- E1 subadditivity on the pair law
  have hW0 : ∀ x, 0 ≤ pushWeight (Finset.Ioc A B) (logWeight A B)
      (fun n => (patternMap g K H₁ n, patternMap g K H₂ (n + H₁))) x :=
    pushWeight_nonneg (fun n _ => logWeight_nonneg A B n) _
  have hWsum : ∑ x, pushWeight (Finset.Ioc A B) (logWeight A B)
      (fun n => (patternMap g K H₁ n, patternMap g K H₂ (n + H₁))) x = 1 := by
    rw [sum_pushWeight, sum_logWeight hA hAB]
  have hsub := shannonEntropy_le_add_marginals hW0 hWsum
  rw [marginal₁_pushWeight_pair, marginal₂_pushWeight_pair] at hsub
  have hm1 : pushWeight (Finset.Ioc A B) (logWeight A B)
      (fun n => patternMap g K H₁ n) = patternLaw g K H₁ A B := rfl
  rw [hm1] at hsub
  -- swap the shifted second marginal for the unshifted law via Fannes + shift-TV
  have hTle := tvDist_patternLaw_shift_le g K H₂ (s := H₁) hA hH
  have hshift0 : ∀ x, 0 ≤ pushWeight (Finset.Ioc A B) (logWeight A B)
      (fun n => patternMap g K H₂ (n + H₁)) x :=
    pushWeight_nonneg (fun n _ => logWeight_nonneg A B n) _
  have hshift1 : ∀ x, pushWeight (Finset.Ioc A B) (logWeight A B)
      (fun n => patternMap g K H₂ (n + H₁)) x ≤ 1 := by
    intro x
    have h := pushWeight_le_sum (s := Finset.Ioc A B)
      (fun n _ => logWeight_nonneg A B n)
      (fun n => patternMap g K H₂ (n + H₁)) x
    rw [sum_logWeight hA hAB] at h
    exact h
  have hF := abs_shannonEntropy_sub_le hshift0 hshift1
    (fun x => patternLaw_nonneg g K H₂ A B x)
    (fun x => patternLaw_le_one g K H₂ hA hAB x)
  have hT0 : 0 ≤ tvDist (pushWeight (Finset.Ioc A B) (logWeight A B)
      (fun n => patternMap g K H₂ (n + H₁))) (patternLaw g K H₂ A B) :=
    tvDist_nonneg _ _
  have hsqrt : Real.sqrt (tvDist (pushWeight (Finset.Ioc A B) (logWeight A B)
        (fun n => patternMap g K H₂ (n + H₁))) (patternLaw g K H₂ A B))
      ≤ Real.sqrt (3 * H₁ / (A * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m)) :=
    Real.sqrt_le_sqrt hTle
  have hcard0 : (0 : ℝ) ≤ 2 * (Fintype.card (PatternSpace K H₂) : ℝ) := by
    positivity
  have h1 : shannonEntropy (pushWeight (Finset.Ioc A B) (logWeight A B)
        (fun n => patternMap g K H₂ (n + H₁)))
      - shannonEntropy (patternLaw g K H₂ A B)
      ≤ 2 * (Fintype.card (PatternSpace K H₂) : ℝ)
          * Real.sqrt (tvDist (pushWeight (Finset.Ioc A B) (logWeight A B)
              (fun n => patternMap g K H₂ (n + H₁))) (patternLaw g K H₂ A B))
        + tvDist (pushWeight (Finset.Ioc A B) (logWeight A B)
            (fun n => patternMap g K H₂ (n + H₁))) (patternLaw g K H₂ A B) :=
    le_trans (le_abs_self _) hF
  have h2 := mul_le_mul_of_nonneg_left hsqrt hcard0
  linarith [hsub, hrelabel, h1, h2, hTle]

/-- The `(1,3)`-marginal of a triple pushforward drops the middle component. -/
theorem margAC_pushWeight_triple (s : Finset ℕ) (w : ℕ → ℝ) {α β γ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ]
    [DecidableEq γ] (φ : ℕ → α) (ψ : ℕ → β) (χ : ℕ → γ) :
    margAC (pushWeight s w (fun n => ((φ n, ψ n), χ n)))
      = pushWeight s w (fun n => (φ n, χ n)) := by
  classical
  funext x
  rcases x with ⟨a, c⟩
  rw [show margAC (pushWeight s w (fun n => ((φ n, ψ n), χ n))) (a, c)
      = ∑ b, pushWeight s w (fun n => ((φ n, ψ n), χ n)) ((a, b), c) from rfl]
  rw [show pushWeight s w (fun n => (φ n, χ n)) (a, c)
      = ∑ n ∈ s.filter (fun n => (φ n, χ n) = (a, c)), w n from rfl]
  rw [show (∑ b, pushWeight s w (fun n => ((φ n, ψ n), χ n)) ((a, b), c))
      = ∑ b, ∑ n ∈ s.filter (fun n => ((φ n, ψ n), χ n) = ((a, b), c)), w n
      from Finset.sum_congr rfl fun b _ => rfl]
  rw [← Finset.sum_fiberwise_of_maps_to (g := ψ)
    (s := s.filter (fun n => (φ n, χ n) = (a, c)))
    (fun n _ => Finset.mem_univ _) w]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ext n
  simp only [Finset.mem_filter, Prod.mk.injEq, and_assoc]
  tauto

/-- The `(2,3)`-marginal of a triple pushforward drops the first component. -/
theorem margBC_pushWeight_triple (s : Finset ℕ) (w : ℕ → ℝ) {α β γ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ]
    [DecidableEq γ] (φ : ℕ → α) (ψ : ℕ → β) (χ : ℕ → γ) :
    margBC (pushWeight s w (fun n => ((φ n, ψ n), χ n)))
      = pushWeight s w (fun n => (ψ n, χ n)) := by
  classical
  funext x
  rcases x with ⟨b, c⟩
  rw [show margBC (pushWeight s w (fun n => ((φ n, ψ n), χ n))) (b, c)
      = ∑ a, pushWeight s w (fun n => ((φ n, ψ n), χ n)) ((a, b), c) from rfl]
  rw [show pushWeight s w (fun n => (ψ n, χ n)) (b, c)
      = ∑ n ∈ s.filter (fun n => (ψ n, χ n) = (b, c)), w n from rfl]
  rw [show (∑ a, pushWeight s w (fun n => ((φ n, ψ n), χ n)) ((a, b), c))
      = ∑ a, ∑ n ∈ s.filter (fun n => ((φ n, ψ n), χ n) = ((a, b), c)), w n
      from Finset.sum_congr rfl fun a _ => rfl]
  rw [← Finset.sum_fiberwise_of_maps_to (g := φ)
    (s := s.filter (fun n => (ψ n, χ n) = (b, c)))
    (fun n _ => Finset.mem_univ _) w]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  ext n
  simp only [Finset.mem_filter, Prod.mk.injEq, and_assoc]
  tauto

/-- **The decrement step**: splitting the window inside the joint law with the
residue and applying submodularity, the shifted half is swapped back at Fannes
cost. This is the paper's relative approximate subadditivity
`H(X_{H₁+H₂}|Y) ≤ H(X_{H₁}|Y) + H(X_{H₂}|Y) + o(1)` in unconditional form. -/
theorem shannonEntropy_jointLaw_step (g : ℕ → ℂ) (K H₁ H₂ P : ℕ) [NeZero P]
    {A B : ℕ} (hA : 1 ≤ A) (hH : A + H₁ + H₁ < B) :
    shannonEntropy (jointLaw g K (H₁ + H₂) P A B)
      ≤ shannonEntropy (jointLaw g K H₁ P A B)
        + shannonEntropy (jointLaw g K H₂ P A B)
        - shannonEntropy (residueLaw P A B)
        + (2 * (Fintype.card (PatternSpace K H₂ × ZMod P) : ℝ)
            * Real.sqrt (3 * H₁ / (A * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m))
          + 3 * H₁ / (A * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m)) := by
  classical
  have hAB : A < B := by omega
  -- relabel the long joint law into the triple law
  have htriple_fun : (fun n => ((patternSplit K H₁ H₂).prodCongr
        (Equiv.refl (ZMod P)) (patternMap g K (H₁ + H₂) n, (n : ZMod P))))
      = fun n => ((patternMap g K H₁ n, patternMap g K H₂ (n + H₁)),
          (n : ZMod P)) := by
    funext n
    simp only [Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]
    rw [patternSplit_patternMap]
  have hrelabel : shannonEntropy (jointLaw g K (H₁ + H₂) P A B)
      = shannonEntropy (pushWeight (Finset.Ioc A B) (logWeight A B)
          (fun n => ((patternMap g K H₁ n, patternMap g K H₂ (n + H₁)),
            (n : ZMod P)))) := by
    rw [jointLaw, ← shannonEntropy_pushWeight_equiv (Finset.Ioc A B)
      (logWeight A B) (fun n => (patternMap g K (H₁ + H₂) n, (n : ZMod P)))
      ((patternSplit K H₁ H₂).prodCongr (Equiv.refl (ZMod P))), htriple_fun]
  -- submodularity on the triple law
  have hW0 : ∀ x, 0 ≤ pushWeight (Finset.Ioc A B) (logWeight A B)
      (fun n => ((patternMap g K H₁ n, patternMap g K H₂ (n + H₁)),
        (n : ZMod P))) x :=
    pushWeight_nonneg (fun n _ => logWeight_nonneg A B n) _
  have hsubmod := condEntropy_le_add_condEntropy hW0
  rw [condEntropy, condEntropy, condEntropy] at hsubmod
  have hmAC : margAC (pushWeight (Finset.Ioc A B) (logWeight A B)
      (fun n => ((patternMap g K H₁ n, patternMap g K H₂ (n + H₁)),
        (n : ZMod P)))) = jointLaw g K H₁ P A B :=
    margAC_pushWeight_triple (Finset.Ioc A B) (logWeight A B)
      (fun n => patternMap g K H₁ n) (fun n => patternMap g K H₂ (n + H₁))
      (fun n => (n : ZMod P))
  have hmBC : margBC (pushWeight (Finset.Ioc A B) (logWeight A B)
      (fun n => ((patternMap g K H₁ n, patternMap g K H₂ (n + H₁)),
        (n : ZMod P))))
      = pushWeight (Finset.Ioc A B) (logWeight A B)
          (fun n => (patternMap g K H₂ (n + H₁), (n : ZMod P))) :=
    margBC_pushWeight_triple (Finset.Ioc A B) (logWeight A B)
      (fun n => patternMap g K H₁ n) (fun n => patternMap g K H₂ (n + H₁))
      (fun n => (n : ZMod P))
  have hm2 : marginal₂ (pushWeight (Finset.Ioc A B) (logWeight A B)
      (fun n => ((patternMap g K H₁ n, patternMap g K H₂ (n + H₁)),
        (n : ZMod P)))) = residueLaw P A B :=
    marginal₂_pushWeight_pair (Finset.Ioc A B) (logWeight A B)
      (fun n => (patternMap g K H₁ n, patternMap g K H₂ (n + H₁)))
      (fun n => (n : ZMod P))
  have hm2BC : marginal₂ (pushWeight (Finset.Ioc A B) (logWeight A B)
      (fun n => (patternMap g K H₂ (n + H₁), (n : ZMod P))))
      = residueLaw P A B :=
    marginal₂_pushWeight_pair (Finset.Ioc A B) (logWeight A B)
      (fun n => patternMap g K H₂ (n + H₁)) (fun n => (n : ZMod P))
  rw [hmAC, hmBC, hm2, marginal₂_jointLaw, hm2BC] at hsubmod
  -- swap the shifted joint half for the unshifted joint law
  have hTle : tvDist (pushWeight (Finset.Ioc A B) (logWeight A B)
        (fun n => (patternMap g K H₂ (n + H₁), ((n + H₁ : ℕ) : ZMod P))))
      (jointLaw g K H₂ P A B)
      ≤ 3 * H₁ / (A * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m) :=
    tvDist_pushWeight_logWeight_shift_le hA hH
      (fun m => (patternMap g K H₂ m, (m : ZMod P)))
  have hcast_fun : (fun n => (patternMap g K H₂ (n + H₁),
        ((n + H₁ : ℕ) : ZMod P)))
      = fun n => ((Equiv.refl (PatternSpace K H₂)).prodCongr
          (Equiv.addRight ((H₁ : ℕ) : ZMod P))
          ((patternMap g K H₂ (n + H₁), (n : ZMod P)))) := by
    funext n
    simp only [Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
      Equiv.coe_addRight]
    rw [Nat.cast_add]
  have hswapH : shannonEntropy (pushWeight (Finset.Ioc A B) (logWeight A B)
        (fun n => (patternMap g K H₂ (n + H₁), ((n + H₁ : ℕ) : ZMod P))))
      = shannonEntropy (pushWeight (Finset.Ioc A B) (logWeight A B)
          (fun n => (patternMap g K H₂ (n + H₁), (n : ZMod P)))) := by
    rw [hcast_fun]
    exact shannonEntropy_pushWeight_equiv (Finset.Ioc A B) (logWeight A B)
      (fun n => (patternMap g K H₂ (n + H₁), (n : ZMod P)))
      ((Equiv.refl (PatternSpace K H₂)).prodCongr
        (Equiv.addRight ((H₁ : ℕ) : ZMod P)))
  -- Fannes bounds for the swap
  have hv0 : ∀ x, 0 ≤ pushWeight (Finset.Ioc A B) (logWeight A B)
      (fun n => (patternMap g K H₂ (n + H₁), ((n + H₁ : ℕ) : ZMod P))) x :=
    pushWeight_nonneg (fun n _ => logWeight_nonneg A B n) _
  have hv1 : ∀ x, pushWeight (Finset.Ioc A B) (logWeight A B)
      (fun n => (patternMap g K H₂ (n + H₁), ((n + H₁ : ℕ) : ZMod P))) x ≤ 1 := by
    intro x
    have h := pushWeight_le_sum (s := Finset.Ioc A B)
      (fun n _ => logWeight_nonneg A B n)
      (fun n => (patternMap g K H₂ (n + H₁), ((n + H₁ : ℕ) : ZMod P))) x
    rw [sum_logWeight hA hAB] at h
    exact h
  have hw1 : ∀ x, jointLaw g K H₂ P A B x ≤ 1 := by
    intro x
    have h := pushWeight_le_sum (s := Finset.Ioc A B)
      (fun n _ => logWeight_nonneg A B n)
      (fun n => (patternMap g K H₂ n, (n : ZMod P))) x
    rw [sum_logWeight hA hAB] at h
    exact h
  have hF := abs_shannonEntropy_sub_le hv0 hv1
    (fun x => jointLaw_nonneg g K H₂ P A B x) hw1
  have hT0 := tvDist_nonneg (pushWeight (Finset.Ioc A B) (logWeight A B)
      (fun n => (patternMap g K H₂ (n + H₁), ((n + H₁ : ℕ) : ZMod P))))
    (jointLaw g K H₂ P A B)
  have hsqrt := Real.sqrt_le_sqrt hTle
  have hcard0 : (0 : ℝ)
      ≤ 2 * (Fintype.card (PatternSpace K H₂ × ZMod P) : ℝ) := by positivity
  have h1 := le_trans (le_abs_self _) hF
  have h2 := mul_le_mul_of_nonneg_left hsqrt hcard0
  linarith [hrelabel, hsubmod, hswapH, h1, h2, hTle]

/-- The per-step Fannes cost of the decrement at shift `k·H` on the window
`(A, B]`. -/
noncomputable def decrementErr (K H P A B k : ℕ) [NeZero P] : ℝ :=
  2 * (Fintype.card (PatternSpace K H × ZMod P) : ℝ)
      * Real.sqrt (3 * ((k * H : ℕ) : ℝ)
        / (A * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m))
    + 3 * ((k * H : ℕ) : ℝ) / (A * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m)

theorem decrementErr_nonneg (K H P A B k : ℕ) [NeZero P] :
    0 ≤ decrementErr K H P A B k := by
  rw [decrementErr]
  have hS : (0 : ℝ) ≤ ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m :=
    Finset.sum_nonneg fun m _ => by positivity
  have h1 : (0 : ℝ) ≤ 3 * ((k * H : ℕ) : ℝ)
      / (A * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m) :=
    div_nonneg (by positivity) (by positivity)
  have h2 := Real.sqrt_nonneg (3 * ((k * H : ℕ) : ℝ)
    / (A * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m))
  have hcard0 : (0 : ℝ) ≤ 2 * (Fintype.card (PatternSpace K H × ZMod P) : ℝ) := by
    positivity
  nlinarith

theorem decrementErr_mono (K H P A B : ℕ) [NeZero P] {j k : ℕ} (hjk : j ≤ k) :
    decrementErr K H P A B j ≤ decrementErr K H P A B k := by
  rw [decrementErr, decrementErr]
  have hden : (0 : ℝ) ≤ ((A : ℝ) * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m)⁻¹ := by
    have hS : (0 : ℝ) ≤ ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m :=
      Finset.sum_nonneg fun m _ => by positivity
    have hAS : (0 : ℝ) ≤ (A : ℝ) * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m := by
      positivity
    exact inv_nonneg.mpr hAS
  have hnum : 3 * ((j * H : ℕ) : ℝ) ≤ 3 * ((k * H : ℕ) : ℝ) := by
    have : ((j * H : ℕ) : ℝ) ≤ ((k * H : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_right H hjk
    linarith
  have harg : 3 * ((j * H : ℕ) : ℝ) / (A * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m)
      ≤ 3 * ((k * H : ℕ) : ℝ) / (A * ∑ m ∈ Finset.Ioc A B, (1 : ℝ) / m) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum hden
  have hsqrt := Real.sqrt_le_sqrt harg
  have hcard0 : (0 : ℝ) ≤ 2 * (Fintype.card (PatternSpace K H × ZMod P) : ℝ) := by
    positivity
  have := mul_le_mul_of_nonneg_left hsqrt hcard0
  linarith

/-- **The iterated decrement**: `k` applications of the step give
`H(X_{kH},Y) ≤ k·H(X_H,Y) − (k−1)·H(Y) + k·err`. -/
theorem shannonEntropy_jointLaw_iterate (g : ℕ → ℂ) (K H P : ℕ) [NeZero P]
    {A B : ℕ} (hA : 1 ≤ A) {k : ℕ} (hk : 1 ≤ k)
    (hkB : A + k * H + k * H < B) :
    shannonEntropy (jointLaw g K (k * H) P A B)
      ≤ k * shannonEntropy (jointLaw g K H P A B)
        - ((k : ℝ) - 1) * shannonEntropy (residueLaw P A B)
        + k * decrementErr K H P A B k := by
  induction k with
  | zero => exact absurd hk (by omega)
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hE := decrementErr_nonneg K H P A B 1
      have hidx : (0 + 1) * H = H := by ring
      rw [hidx]
      simp only [zero_add, Nat.cast_one]
      linarith
    · have heq : (m + 1) * H = m * H + H := by ring
      have hle : m * H ≤ (m + 1) * H := Nat.mul_le_mul_right H (by omega)
      have hmB : A + m * H + m * H < B := by omega
      have ihm := ih hm hmB
      have hstep' : shannonEntropy (jointLaw g K (m * H + H) P A B)
          ≤ shannonEntropy (jointLaw g K (m * H) P A B)
            + shannonEntropy (jointLaw g K H P A B)
            - shannonEntropy (residueLaw P A B)
            + decrementErr K H P A B m := by
        rw [decrementErr]
        exact shannonEntropy_jointLaw_step g K (m * H) H P hA hmB
      have hEmono : decrementErr K H P A B m ≤ decrementErr K H P A B (m + 1) :=
        decrementErr_mono K H P A B (Nat.le_succ m)
      have hscale : (m : ℝ) * decrementErr K H P A B m
          ≤ (m : ℝ) * decrementErr K H P A B (m + 1) :=
        mul_le_mul_of_nonneg_left hEmono (Nat.cast_nonneg m)
      have hr1 : ((m + 1 : ℕ) : ℝ) * shannonEntropy (jointLaw g K H P A B)
          = (m : ℝ) * shannonEntropy (jointLaw g K H P A B)
            + shannonEntropy (jointLaw g K H P A B) := by
        push_cast
        ring
      have hr2 : (((m + 1 : ℕ) : ℝ) - 1) * shannonEntropy (residueLaw P A B)
          = ((m : ℝ) - 1) * shannonEntropy (residueLaw P A B)
            + shannonEntropy (residueLaw P A B) := by
        push_cast
        ring
      have hr3 : ((m + 1 : ℕ) : ℝ) * decrementErr K H P A B (m + 1)
          = (m : ℝ) * decrementErr K H P A B (m + 1)
            + decrementErr K H P A B (m + 1) := by
        push_cast
        ring
      rw [heq]
      linarith [hstep', ihm, hscale, hr1, hr2, hr3]

/-- **The splat inequality** (eq. (splat) of arXiv:1509.05422 §3, un-normalized):
the mutual information between `X_H` and `Y` is controlled by the entropy-rate
drop across `k` blocks. -/
theorem mutualInfo_jointLaw_le (g : ℕ → ℂ) (K H P : ℕ) [NeZero P] {A B : ℕ}
    (hA : 1 ≤ A) {k : ℕ} (hk : 1 ≤ k) (hkB : A + k * H + k * H < B) :
    mutualInfo (jointLaw g K H P A B)
      ≤ shannonEntropy (patternLaw g K H A B)
        - shannonEntropy (patternLaw g K (k * H) A B) / k
        + shannonEntropy (residueLaw P A B) / k
        + decrementErr K H P A B k := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hiter := shannonEntropy_jointLaw_iterate g K H P hA hk hkB
  have hmarg : shannonEntropy (patternLaw g K (k * H) A B)
      ≤ shannonEntropy (jointLaw g K (k * H) P A B) := by
    have h := shannonEntropy_marginal₁_le
      (w := jointLaw g K (k * H) P A B) (jointLaw_nonneg g K (k * H) P A B)
    rw [marginal₁_jointLaw] at h
    exact h
  have hI : mutualInfo (jointLaw g K H P A B)
      = shannonEntropy (patternLaw g K H A B)
        + shannonEntropy (residueLaw P A B)
        - shannonEntropy (jointLaw g K H P A B) := by
    rw [mutualInfo, marginal₁_jointLaw, marginal₂_jointLaw]
  have h1 : shannonEntropy (patternLaw g K (k * H) A B)
      ≤ k * shannonEntropy (jointLaw g K H P A B)
        - ((k : ℝ) - 1) * shannonEntropy (residueLaw P A B)
        + k * decrementErr K H P A B k := le_trans hmarg hiter
  have h2 : shannonEntropy (patternLaw g K (k * H) A B) / k
      ≤ shannonEntropy (jointLaw g K H P A B)
        - shannonEntropy (residueLaw P A B)
        + shannonEntropy (residueLaw P A B) / k
        + decrementErr K H P A B k := by
    rw [div_le_iff₀ hk0]
    have hexp : (shannonEntropy (jointLaw g K H P A B)
          - shannonEntropy (residueLaw P A B)
          + shannonEntropy (residueLaw P A B) / k
          + decrementErr K H P A B k) * k
        = k * shannonEntropy (jointLaw g K H P A B)
          - ((k : ℝ) - 1) * shannonEntropy (residueLaw P A B)
          + k * decrementErr K H P A B k := by
      field_simp
      ring
    rw [hexp]
    exact h1
  rw [hI]
  linarith

/-- The pattern alphabet has `((K+1)²)^H` letters. -/
theorem card_patternSpace (K H : ℕ) :
    Fintype.card (PatternSpace K H) = ((K + 1) * (K + 1)) ^ H := by
  rw [show Fintype.card (PatternSpace K H)
      = Fintype.card (Fin (K + 1) × Fin (K + 1)) ^ Fintype.card (Fin H)
      from Fintype.card_fun]
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- **The entropy budget**: `H(X_H) ≤ H·log((K+1)²)` — the trivial bound (jens)
that seeds the decrement chain. -/
theorem shannonEntropy_patternLaw_le_mul (g : ℕ → ℂ) (K H : ℕ) {A B : ℕ}
    (hA : 1 ≤ A) (hAB : A < B) :
    shannonEntropy (patternLaw g K H A B)
      ≤ (H : ℝ) * Real.log (((K + 1) * (K + 1) : ℕ) : ℝ) := by
  have h := shannonEntropy_le_log_card
    (w := patternLaw g K H A B) (patternLaw_nonneg g K H A B)
    (sum_patternLaw g K H hA hAB)
  rw [card_patternSpace] at h
  have hcast : ((((K + 1) * (K + 1)) ^ H : ℕ) : ℝ)
      = ((((K + 1) * (K + 1) : ℕ) : ℝ)) ^ H := by
    push_cast
    ring
  rw [hcast, Real.log_pow] at h
  exact h

/-- **The ratio form of splat**: the entropy rate decrements by the mutual
information density, up to the conditioning and Fannes slacks. This is
eq. (splat) of arXiv:1509.05422 §3; `E6f`'s grid feeds it to
`exists_lt_of_chain_budget`. -/
theorem mutualInfo_ratio_le (g : ℕ → ℂ) (K H P : ℕ) [NeZero P] {A B k : ℕ}
    (hA : 1 ≤ A) (hH : 1 ≤ H) (hk : 1 ≤ k) (hkB : A + k * H + k * H < B) :
    shannonEntropy (patternLaw g K (k * H) A B) / ((k * H : ℕ) : ℝ)
      ≤ shannonEntropy (patternLaw g K H A B) / H
        - mutualInfo (jointLaw g K H P A B) / H
        + shannonEntropy (residueLaw P A B) / ((k * H : ℕ) : ℝ)
        + decrementErr K H P A B k / H := by
  have hsplat := mutualInfo_jointLaw_le g K H P hA hk hkB
  have hH0 : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkH0 : (0 : ℝ) < ((k * H : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by omega) (by omega)
  -- divide splat by H
  have hdivH : mutualInfo (jointLaw g K H P A B) / H
      ≤ (shannonEntropy (patternLaw g K H A B)
          - shannonEntropy (patternLaw g K (k * H) A B) / k
          + shannonEntropy (residueLaw P A B) / k
          + decrementErr K H P A B k) / H := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hsplat (inv_nonneg.mpr hH0.le)
  have hexp : (shannonEntropy (patternLaw g K H A B)
        - shannonEntropy (patternLaw g K (k * H) A B) / k
        + shannonEntropy (residueLaw P A B) / k
        + decrementErr K H P A B k) / H
      = shannonEntropy (patternLaw g K H A B) / H
        - shannonEntropy (patternLaw g K (k * H) A B) / ((k * H : ℕ) : ℝ)
        + shannonEntropy (residueLaw P A B) / ((k * H : ℕ) : ℝ)
        + decrementErr K H P A B k / H := by
    have hcast : ((k * H : ℕ) : ℝ) = (k : ℝ) * (H : ℝ) := by push_cast; ring
    rw [hcast]
    field_simp
  rw [hexp] at hdivH
  linarith

end MoltResearch
