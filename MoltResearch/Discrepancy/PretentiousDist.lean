import MoltResearch.Discrepancy.LogAvgCorr

/-!
# Discrepancy: pretentious (Granville–Soundararajan) distance, finite-`N` form

Language-layer module for the Tao 2015 analytic core (`Problems/tao2015_analytic_core.md`):
the finite-truncation pretentious distance used to state the non-pretentiousness hypothesis of
the logarithmically averaged Elliott theorem (arXiv:1509.05422):

`𝔻(g, h; N)² = ∑_{p prime, p < N} (1 - Re(g p * conj (h p))) / p`.

Conventions:
- The prime range is `Nat.primesBelow N` (primes strictly below `N`) — the Mathlib-idiomatic
  finite prime truncation; interfaces quantifying over all `N` are insensitive to `< N` vs `≤ N`.
- The **squared** distance `pretentiousDistSq` is the primary definition (the literature works
  with `𝔻²` throughout); `pretentiousDist` is its square root.
- Junk values are embraced: without unimodularity hypotheses the summands can be negative, so
  the order lemmas below carry `Unimodular` hypotheses rather than baking them into the
  definition.

Monotonicity basics (this module deliberately stops here):
- `pretentiousDistSq_summand_nonneg`, `pretentiousDistSq_nonneg` — nonnegativity for unimodular
  arguments.
- `pretentiousDistSq_mono` / `pretentiousDist_mono` — monotone in the truncation `N`.
- `Unimodular.pretentiousDistSq_self` — the diagonal vanishes (each summand is `0`).
-/

namespace MoltResearch

/-- Squared finite-`N` pretentious distance (Granville–Soundararajan):

`pretentiousDistSq g h N = ∑_{p prime, p < N} (1 - Re(g p * conj (h p))) / p`.

The non-pretentiousness hypothesis of the log-Elliott interface says this tends to `∞` with `N`
for every character-modulated comparison `h`.
-/
noncomputable def pretentiousDistSq (g h : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ p ∈ N.primesBelow, (1 - (g p * (starRingEnd ℂ) (h p)).re) / p

/-- Finite-`N` pretentious distance: the square root of `pretentiousDistSq`. -/
noncomputable def pretentiousDist (g h : ℕ → ℂ) (N : ℕ) : ℝ :=
  Real.sqrt (pretentiousDistSq g h N)

/-- Degenerate truncation: no primes below `0`. -/
@[simp] theorem pretentiousDistSq_zero_N (g h : ℕ → ℂ) : pretentiousDistSq g h 0 = 0 := by
  simp [pretentiousDistSq]

variable {g h : ℕ → ℂ}

/-- Each summand of `pretentiousDistSq` is nonnegative when `g` is unimodular and the
comparison `h` is 1-bounded: `Re(g p * conj (h p)) ≤ ‖g p‖ * ‖h p‖ ≤ 1`, and the denominator
is a `ℕ`-cast.

The 1-bounded (rather than unimodular) comparison hypothesis matters for the analytic-core
interfaces: character-modulated twists `n ↦ χ(n)·nⁱᵗ` vanish off the coprime locus and at `0`,
so they are 1-bounded but not unimodular. -/
theorem pretentiousDistSq_summand_nonneg_of_norm_le_one (hg : Unimodular g)
    (hh : ∀ p : ℕ, ‖h p‖ ≤ 1) (p : ℕ) :
    0 ≤ (1 - (g p * (starRingEnd ℂ) (h p)).re) / p := by
  apply div_nonneg
  · have hre : (g p * (starRingEnd ℂ) (h p)).re ≤ 1 := by
      calc (g p * (starRingEnd ℂ) (h p)).re
          ≤ ‖g p * (starRingEnd ℂ) (h p)‖ := Complex.re_le_norm _
        _ = ‖h p‖ := by rw [norm_mul, hg p, RCLike.norm_conj, one_mul]
        _ ≤ 1 := hh p
    linarith
  · exact Nat.cast_nonneg p

/-- Each summand of `pretentiousDistSq` is nonnegative for unimodular arguments. -/
theorem pretentiousDistSq_summand_nonneg (hg : Unimodular g) (hh : Unimodular h) (p : ℕ) :
    0 ≤ (1 - (g p * (starRingEnd ℂ) (h p)).re) / p :=
  pretentiousDistSq_summand_nonneg_of_norm_le_one hg (fun p => (hh p).le) p

/-- Nonnegativity of the squared pretentious distance for a 1-bounded comparison. -/
theorem pretentiousDistSq_nonneg_of_norm_le_one (hg : Unimodular g)
    (hh : ∀ p : ℕ, ‖h p‖ ≤ 1) (N : ℕ) :
    0 ≤ pretentiousDistSq g h N :=
  Finset.sum_nonneg fun p _ => pretentiousDistSq_summand_nonneg_of_norm_le_one hg hh p

/-- Nonnegativity of the squared pretentious distance for unimodular arguments. -/
theorem pretentiousDistSq_nonneg (hg : Unimodular g) (hh : Unimodular h) (N : ℕ) :
    0 ≤ pretentiousDistSq g h N :=
  pretentiousDistSq_nonneg_of_norm_le_one hg (fun p => (hh p).le) N

/-- The squared pretentious distance is monotone in the truncation `N` for a 1-bounded
comparison (so that the added summands are nonnegative). -/
theorem pretentiousDistSq_mono_of_norm_le_one (hg : Unimodular g)
    (hh : ∀ p : ℕ, ‖h p‖ ≤ 1) {N M : ℕ} (hNM : N ≤ M) :
    pretentiousDistSq g h N ≤ pretentiousDistSq g h M := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 hNM, hp.2⟩
  · intro p _ _
    exact pretentiousDistSq_summand_nonneg_of_norm_le_one hg hh p

/-- The squared pretentious distance is monotone in the truncation `N`
(for unimodular arguments, so that the added summands are nonnegative). -/
theorem pretentiousDistSq_mono (hg : Unimodular g) (hh : Unimodular h) {N M : ℕ}
    (hNM : N ≤ M) :
    pretentiousDistSq g h N ≤ pretentiousDistSq g h M :=
  pretentiousDistSq_mono_of_norm_le_one hg (fun p => (hh p).le) hNM

/-- The pretentious distance is nonnegative (unconditionally: it is a square root). -/
theorem pretentiousDist_nonneg (g h : ℕ → ℂ) (N : ℕ) : 0 ≤ pretentiousDist g h N :=
  Real.sqrt_nonneg _

/-- The pretentious distance is monotone in the truncation `N` (unimodular arguments). -/
theorem pretentiousDist_mono (hg : Unimodular g) (hh : Unimodular h) {N M : ℕ}
    (hNM : N ≤ M) :
    pretentiousDist g h N ≤ pretentiousDist g h M :=
  Real.sqrt_le_sqrt (pretentiousDistSq_mono hg hh hNM)

namespace Unimodular

/-- Diagonal degeneracy: a unimodular sequence is at squared distance `0` from itself
(each summand has `Re(g p * conj (g p)) = 1`). -/
theorem pretentiousDistSq_self (hg : Unimodular g) (N : ℕ) :
    pretentiousDistSq g g N = 0 := by
  unfold pretentiousDistSq
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [hg.mul_conj_self p]
  simp

/-- Diagonal degeneracy for the (unsquared) distance. -/
theorem pretentiousDist_self (hg : Unimodular g) (N : ℕ) :
    pretentiousDist g g N = 0 := by
  rw [pretentiousDist, hg.pretentiousDistSq_self N, Real.sqrt_zero]

end Unimodular

/-! ### Quasi-triangle inequality

The sharp Granville–Soundararajan triangle inequality for `pretentiousDist` is not needed by
the derivation-(C) bookkeeping (all its pretense bounds are `O(1)`), so we state only the
elementary squared-distance version with constant `3`, which has a pointwise proof on the
closed unit disc. -/

/-- Pointwise quasi-triangle bound on the closed unit disc:
`1 − Re(u·conj v) ≤ 3(1 − Re u) + 3(1 − Re v)` for `‖u‖, ‖v‖ ≤ 1`.

Sharp at `u = v = 1`. Follows from `1 − Re(u·conj v) = ½|u − v|² + ½(1−|u|²) + ½(1−|v|²)`
and elementary estimates; here delegated to `nlinarith`. -/
theorem one_sub_mul_conj_re_le_of_norm_le_one {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    1 - (u * (starRingEnd ℂ) v).re ≤ 3 * (1 - u.re) + 3 * (1 - v.re) := by
  have hu2 : u.re ^ 2 + u.im ^ 2 ≤ 1 := by
    have h := Complex.normSq_eq_norm_sq u
    have : ‖u‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg u) hu
    rw [Complex.normSq_apply] at h
    nlinarith
  have hv2 : v.re ^ 2 + v.im ^ 2 ≤ 1 := by
    have h := Complex.normSq_eq_norm_sq v
    have : ‖v‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg v) hv
    rw [Complex.normSq_apply] at h
    nlinarith
  have hur : u.re ≤ 1 := le_trans (Complex.re_le_norm u) hu
  have hvr : v.re ≤ 1 := le_trans (Complex.re_le_norm v) hv
  have hmul : (u * (starRingEnd ℂ) v).re = u.re * v.re + u.im * v.im := by
    simp [Complex.mul_re]
  rw [hmul]
  nlinarith [sq_nonneg (u.im + v.im), sq_nonneg (u.re - 1), sq_nonneg (v.re - 1),
    mul_nonneg (sub_nonneg.mpr hur) (sub_nonneg.mpr hvr)]

/-- Pointwise quasi-triangle bound through a unimodular pivot `a`:
`1 − Re(b·conj c) ≤ 3(1 − Re(a·conj b)) + 3(1 − Re(a·conj c))` for 1-bounded `b, c`.

This is the per-prime content of the quasi-triangle inequality: multiplying by the
unimodular `a` rotates `b, c` into the disc lemma's frame without changing the left side. -/
theorem one_sub_mul_conj_re_le_pivot {a b c : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ ≤ 1)
    (hc : ‖c‖ ≤ 1) :
    1 - (b * (starRingEnd ℂ) c).re
      ≤ 3 * (1 - (a * (starRingEnd ℂ) b).re) + 3 * (1 - (a * (starRingEnd ℂ) c).re) := by
  have ha1 : a * (starRingEnd ℂ) a = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]
    norm_num
  have hkey : (a * (starRingEnd ℂ) b) * (starRingEnd ℂ) (a * (starRingEnd ℂ) c)
      = (starRingEnd ℂ) b * c := by
    rw [map_mul, Complex.conj_conj]
    calc a * (starRingEnd ℂ) b * ((starRingEnd ℂ) a * c)
        = (a * (starRingEnd ℂ) a) * ((starRingEnd ℂ) b * c) := by ring
      _ = (starRingEnd ℂ) b * c := by rw [ha1, one_mul]
  have hre : ((starRingEnd ℂ) b * c).re = (b * (starRingEnd ℂ) c).re := by
    have h := Complex.conj_re ((starRingEnd ℂ) b * c)
    rw [map_mul, Complex.conj_conj] at h
    exact h.symm
  have hub : ‖a * (starRingEnd ℂ) b‖ ≤ 1 := by
    rw [norm_mul, ha, one_mul, RCLike.norm_conj]
    exact hb
  have huc : ‖a * (starRingEnd ℂ) c‖ ≤ 1 := by
    rw [norm_mul, ha, one_mul, RCLike.norm_conj]
    exact hc
  have h := one_sub_mul_conj_re_le_of_norm_le_one hub huc
  rw [hkey, hre] at h
  exact h

/-- **Quasi-triangle inequality** for the squared pretentious distance: two 1-bounded
comparisons close to a common unimodular `g` are close to each other, with constant `3`:

`𝔻(h₁, h₂; N)² ≤ 3·𝔻(g, h₁; N)² + 3·𝔻(g, h₂; N)²`.

This is the derivation-(C) form of the Granville–Soundararajan triangle inequality (all its
pretense bounds are `O(1)`, so the sharp constant is irrelevant); the Lemma-"tb" consumer
takes `g` a sample of the stochastic function and `hᵢ` two character twists. -/
theorem pretentiousDistSq_quasi_triangle {h₁ h₂ : ℕ → ℂ} (hg : Unimodular g)
    (hh₁ : ∀ p : ℕ, ‖h₁ p‖ ≤ 1) (hh₂ : ∀ p : ℕ, ‖h₂ p‖ ≤ 1) (N : ℕ) :
    pretentiousDistSq h₁ h₂ N
      ≤ 3 * pretentiousDistSq g h₁ N + 3 * pretentiousDistSq g h₂ N := by
  unfold pretentiousDistSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p hp => ?_
  have hppos : (0 : ℝ) < p := by
    exact_mod_cast (Nat.mem_primesBelow.mp hp).2.pos
  have hpt := one_sub_mul_conj_re_le_pivot (hg p) (hh₁ p) (hh₂ p)
  calc (1 - (h₁ p * (starRingEnd ℂ) (h₂ p)).re) / p
      ≤ (3 * (1 - (g p * (starRingEnd ℂ) (h₁ p)).re)
          + 3 * (1 - (g p * (starRingEnd ℂ) (h₂ p)).re)) / p := by
        exact div_le_div_of_nonneg_right hpt hppos.le
    _ = 3 * ((1 - (g p * (starRingEnd ℂ) (h₁ p)).re) / p)
        + 3 * ((1 - (g p * (starRingEnd ℂ) (h₂ p)).re) / p) := by ring

/-! ### Character-modulated archimedean twists and nonasymptotic non-pretentiousness -/

/-- The character-modulated archimedean twist `n ↦ χ(n)·nⁱᵗ` — the comparison family of the
pretentious classification (Tao 2015 / Granville–Soundararajan). Junk values are embraced:
`χ` vanishes off the coprime locus and `cpow` at `0` follows Mathlib's conventions. -/
noncomputable def charTwist (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) : ℕ → ℂ :=
  fun m => χ (m : ZMod q) * (m : ℂ) ^ (Complex.I * (t : ℂ))

/-- Character-modulated twists are 1-bounded (values are `0` or on the unit circle). -/
theorem charTwist_norm_le_one (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) (m : ℕ) :
    ‖charTwist q χ t m‖ ≤ 1 := by
  unfold charTwist
  rw [norm_mul]
  have hχ : ‖χ (m : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have hpow : ‖(m : ℂ) ^ (Complex.I * (t : ℂ))‖ ≤ 1 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rcases eq_or_ne (Complex.I * (t : ℂ)) 0 with h0 | h0
      · simp [h0]
      · simp [Complex.zero_cpow h0]
    · have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hcast : ((m : ℕ) : ℂ) = (((m : ℕ) : ℝ) : ℂ) := by push_cast; rfl
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hm']
      simp [Complex.mul_re]
  calc ‖χ (m : ZMod q)‖ * ‖(m : ℂ) ^ (Complex.I * (t : ℂ))‖
      ≤ 1 * 1 := mul_le_mul hχ hpow (norm_nonneg _) zero_le_one
    _ = 1 := mul_one 1

/-- Nonasymptotic non-pretentiousness at strength `A` and truncation `x` — the hypothesis shape
of the logarithmically averaged nonasymptotic Elliott theorem (arXiv:1509.05363, Theorem 1.10):
`g` is at squared pretentious distance `≥ A` from every character-modulated twist with character
period `≤ A` and frequency `|t| ≤ A·x`.

The parameter `A` plays three roles at once (distance threshold, period range, frequency range),
exactly as in the source statement; consequently this predicate is *not* monotone in `A`. -/
def NonPretentiousAt (g : ℕ → ℂ) (A : ℝ) (x : ℕ) : Prop :=
  ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
    (q : ℝ) ≤ A → |t| ≤ A * x → A ≤ pretentiousDistSq g (charTwist q χ t) x

end MoltResearch
