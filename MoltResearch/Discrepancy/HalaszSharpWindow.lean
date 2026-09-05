import MoltResearch.Discrepancy.HalaszSharpSurvivors
import MoltResearch.Discrepancy.WindowAssembly

/-!
# The sharp Halász window: prefix sums and the twisted Dirichlet block

The plumbing of `halaszBudgetSharp` into the shape the exceptional-cell leg
consumes.  Two differences from the shell plumbing
`sup_partial_le_halaszBudgetShell`:

* **no `log` loss.** The shell version prices the two denominators
  `log X`, `log u` by `36`, which costs a factor `log B'/36` against the
  budget (`Ĥ(z) ≍ z·log z·(…)`).  Here the prefix sums are taken over the
  block `a ≤ u ≤ B'` and both denominators are priced by `log a`, so
  `sharpPartialBudget A δ₀ a B' = 2Ĥ⁺(A,3B')/(δ₀·log a) + (e·B'·δ₀ + 1)
  ≍ B'·(quality/δ₀ + δ₀)` when `B' ≍ a`;
* **fixed strength.** With the sharp budget the quality is
  `(A+1)·e^{−A}` with no `loglog`, so at `δ₀ ≍ √((A+1)e^{−A})` the block
  bound is `≍ (B'/a)·√(A+1)·e^{−A/2}` uniformly in the scale.

`sharp_halasz_twisted_dirichlet_block` is the mirror of
`cheap_halasz_twisted_dirichlet_block` (VI-9e) with the sharp prefix bound in
place of `low_band_block_sup`: the Fourier phase is absorbed into the
archimedean twist (`archTwist_phase_eq`, `nonPretentiousAt_archTwist` at
strength `D/2`), Abel summation sees only the weight `1/n`
(`norm_sum_div_le_of_partial`), and the cost has no `W` and no `T`.
-/

namespace MoltResearch

open ExpSums

open Real Finset in
/-- **The divided sharp capstone** (Track R, T0-5): the initial segment at
scale `x`, with the scale ratio made explicit — for any lower bound `δ₀` on
the log-gap to the auxiliary scale `X`,

  `‖∑_{n ≤ x} f n‖ ≤ (Ĥ⁺(A,X)/log X + Ĥ⁺(A,x)/log x)/δ₀ + (X − x)`.

Mirror of `plain_sumC_le_halaszBudgetShell_div`. -/
theorem plain_sumC_le_halaszBudgetSharp_div (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hcm : CompletelyMultiplicativeC f)
    (h1 : f 1 = 1)
    (x X : ℕ) (hx : 10^16 ≤ x) (hxX : x ≤ X)
    (A : ℝ) (h1A : 1 ≤ A)
    (hAx : NonPretentiousAt f A x)
    (hAX : NonPretentiousAt f A X)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hδX : δ₀ ≤ Real.log (X:ℝ) - Real.log (x:ℝ)) :
    ‖∑ n ∈ Finset.Icc 1 x, f n‖
      ≤ (halaszBudgetSharp A (X:ℝ) / Real.log (X:ℝ)
          + halaszBudgetSharp A (x:ℝ) / Real.log (x:ℝ)) / δ₀
        + ((X:ℝ) - (x:ℝ)) := by
  have h := plain_sumC_le_halaszBudgetSharp f hf hcm h1 x X hx hxX A h1A hAx hAX
  have hA0 : (0:ℝ) ≤ A := by linarith
  have hD : (0:ℝ) < Real.log (X:ℝ) - Real.log (x:ℝ) :=
    lt_of_lt_of_le hδ₀ hδX
  have hxR : (Real.exp 1) ≤ (x:ℝ) := by
    have h3 : (3:ℝ) ≤ (x:ℝ) := by
      have : (3:ℕ) ≤ x := le_trans (by norm_num) hx
      exact_mod_cast this
    linarith [Real.exp_one_lt_d9.le]
  have hXR : (Real.exp 1) ≤ (X:ℝ) := by
    have : (x:ℝ) ≤ (X:ℝ) := by exact_mod_cast hxX
    linarith
  have hlogx : (0:ℝ) < Real.log (x:ℝ) := by
    have hx1 : (1:ℝ) < (x:ℝ) := by
      have : (2:ℕ) ≤ x := le_trans (by norm_num) hx
      exact_mod_cast lt_of_lt_of_le (by norm_num : (1:ℕ) < 2) this
    exact Real.log_pos hx1
  have hlogX : (0:ℝ) < Real.log (X:ℝ) := by
    have : Real.log (x:ℝ) ≤ Real.log (X:ℝ) := by
      have hxx : (x:ℝ) ≤ (X:ℝ) := by exact_mod_cast hxX
      exact Real.log_le_log (by positivity) hxx
    linarith
  have hE0 : (0:ℝ) ≤ halaszBudgetSharp A (X:ℝ) / Real.log (X:ℝ)
      + halaszBudgetSharp A (x:ℝ) / Real.log (x:ℝ) := by
    have hEX := halaszBudgetSharp_nonneg A (X:ℝ) hA0 hXR
    have hEx := halaszBudgetSharp_nonneg A (x:ℝ) hA0 hxR
    have d1 : (0:ℝ) ≤ halaszBudgetSharp A (X:ℝ) / Real.log (X:ℝ) :=
      div_nonneg hEX hlogX.le
    have d2 : (0:ℝ) ≤ halaszBudgetSharp A (x:ℝ) / Real.log (x:ℝ) :=
      div_nonneg hEx hlogx.le
    linarith
  have hkey : (‖∑ n ∈ Finset.Icc 1 x, f n‖ - ((X:ℝ) - (x:ℝ)))
      * (Real.log (X:ℝ) - Real.log (x:ℝ))
      ≤ halaszBudgetSharp A (X:ℝ) / Real.log (X:ℝ)
        + halaszBudgetSharp A (x:ℝ) / Real.log (x:ℝ) := by
    nlinarith [h]
  have h2 : ‖∑ n ∈ Finset.Icc 1 x, f n‖ - ((X:ℝ) - (x:ℝ))
      ≤ (halaszBudgetSharp A (X:ℝ) / Real.log (X:ℝ)
          + halaszBudgetSharp A (x:ℝ) / Real.log (x:ℝ))
        / (Real.log (X:ℝ) - Real.log (x:ℝ)) :=
    (le_div_iff₀ hD).mpr hkey
  have h3 : (halaszBudgetSharp A (X:ℝ) / Real.log (X:ℝ)
        + halaszBudgetSharp A (x:ℝ) / Real.log (x:ℝ))
        / (Real.log (X:ℝ) - Real.log (x:ℝ))
      ≤ (halaszBudgetSharp A (X:ℝ) / Real.log (X:ℝ)
          + halaszBudgetSharp A (x:ℝ) / Real.log (x:ℝ)) / δ₀ := by
    gcongr
  linarith

/-- **The sharp prefix budget** (Track R, T0-5) on a block `a ≤ u ≤ B'`:
`2·Ĥ⁺(A, 3B')/(δ₀·log a) + (e·B'·δ₀ + 1)`. -/
noncomputable def sharpPartialBudget (A δ₀ : ℝ) (a B' : ℕ) : ℝ :=
  2 * halaszBudgetSharp A (3 * (B' : ℝ)) / (δ₀ * Real.log (a : ℝ))
    + (Real.exp 1 * (B' : ℝ) * δ₀ + 1)

set_option maxHeartbeats 1600000 in
open Real Finset in
/-- **The block-uniform prefix bound at the sharp budget** (Track R, T0-5):
under non-pretentiousness at strength `A ≥ 1` at every scale of `[a, 3B']`
(`10¹⁶ ≤ a ≤ B'`), every prefix `∑_{n ≤ u} f(n)` with `a ≤ u ≤ B'` is at most
`sharpPartialBudget A δ₀ a B'`.  The divided capstone at the auxiliary scale
`X_u = ⌈u·e^{δ₀}⌉ ≤ 3B'` prices the prefix; the budget's monotonicity lifts
both numerators to `3B'`, and both denominators are `≥ log a`. -/
theorem prefix_le_sharpPartialBudget (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hcm : CompletelyMultiplicativeC f)
    (h1 : f 1 = 1)
    (a B' : ℕ) (ha : 10^16 ≤ a) (haB : a ≤ B')
    (A : ℝ) (h1A : 1 ≤ A)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₁ : δ₀ ≤ 1)
    (hNP : ∀ u : ℕ, a ≤ u → u ≤ 3*B' → NonPretentiousAt f A u) :
    ∀ u : ℕ, a ≤ u → u ≤ B' →
      ‖∑ k ∈ Finset.Icc 1 u, f k‖ ≤ sharpPartialBudget A δ₀ a B' := by
  intro u hau hu
  have hbig : 10^16 ≤ u := le_trans ha hau
  have hB' : 10^16 ≤ B' := le_trans ha haB
  have hB'R : (10:ℝ)^16 ≤ (B':ℝ) := by exact_mod_cast hB'
  have hA0 : (0:ℝ) ≤ A := by linarith
  have he272 : Real.exp 1 ≤ (2.72:ℝ) := by
    have := Real.exp_one_lt_d9
    linarith
  have hbudget0 : (0:ℝ) ≤ halaszBudgetSharp A (3*(B':ℝ)) := by
    refine halaszBudgetSharp_nonneg A _ hA0 ?_
    linarith [he272]
  have huR : (10:ℝ)^16 ≤ (u:ℝ) := by exact_mod_cast hbig
  have hu0 : (0:ℝ) < (u:ℝ) := by linarith
  set X : ℕ := ⌈(u:ℝ) * Real.exp δ₀⌉₊ with hX_def
  have hXreal : (u:ℝ) * Real.exp δ₀ ≤ (X:ℝ) := Nat.le_ceil _
  have hexpδ1 : (1:ℝ) ≤ Real.exp δ₀ := by
    rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr hδ₀.le
  have hexpδe : Real.exp δ₀ ≤ Real.exp 1 := Real.exp_le_exp.mpr hδ₁
  have huX : u ≤ X := by
    have h1' : (u:ℝ) ≤ (X:ℝ) := by nlinarith [hXreal, hu0]
    exact_mod_cast h1'
  have hXle : (X:ℝ) ≤ (u:ℝ) * Real.exp δ₀ + 1 := by
    have := Nat.ceil_lt_add_one
      (by positivity : (0:ℝ) ≤ (u:ℝ) * Real.exp δ₀)
    linarith
  have hX3B : X ≤ 3*B' := by
    have hc : (X:ℝ) ≤ 3*(B':ℝ) := by
      have huB : (u:ℝ) ≤ (B':ℝ) := by exact_mod_cast hu
      nlinarith [hXle, hexpδe, he272, hB'R]
    exact_mod_cast hc
  have hX16 : 10^16 ≤ X := le_trans hbig huX
  -- the two nonpretentiousness instances
  have hNPu := hNP u hau (by omega)
  have hNPX := hNP X (le_trans hau huX) hX3B
  -- the log-gap
  have hgap : δ₀ ≤ Real.log (X:ℝ) - Real.log (u:ℝ) := by
    have h1' : Real.log ((u:ℝ) * Real.exp δ₀) ≤ Real.log (X:ℝ) :=
      Real.log_le_log (by positivity) hXreal
    rw [Real.log_mul (ne_of_gt hu0) (ne_of_gt (Real.exp_pos _)),
      Real.log_exp] at h1'
    linarith
  -- the divided capstone
  have hdiv := plain_sumC_le_halaszBudgetSharp_div f hf hcm h1 u X hbig huX
    A h1A hNPu hNPX δ₀ hδ₀ hgap
  have h36 : ∀ z : ℕ, 10^16 ≤ z → (36:ℝ) ≤ Real.log (z:ℝ) := by
    intro z hz
    have hz0 : (0:ℝ) < (z:ℝ) := by
      have : (0:ℕ) < z := by omega
      exact_mod_cast this
    rw [Real.le_log_iff_exp_le hz0]
    have he3 : Real.exp (3:ℝ) ≤ 20.1 := by
      have h3 : Real.exp (3:ℝ) = (Real.exp 1)^(3:ℕ) := by
        rw [← Real.exp_nat_mul]
        norm_num
      rw [h3]
      have hcube : (Real.exp 1)^(3:ℕ) ≤ (2.7182818286:ℝ)^(3:ℕ) :=
        pow_le_pow_left₀ (Real.exp_pos 1).le
          (by linarith [Real.exp_one_lt_d9]) 3
      have hnum : (2.7182818286:ℝ)^(3:ℕ) ≤ 20.1 := by norm_num
      linarith
    have h36e : Real.exp (36:ℝ) = (Real.exp 3)^(12:ℕ) := by
      rw [← Real.exp_nat_mul]
      norm_num
    have hp12 : (Real.exp 3)^(12:ℕ) ≤ (20.1:ℝ)^(12:ℕ) :=
      pow_le_pow_left₀ (Real.exp_pos 3).le he3 12
    have hnum12 : (20.1:ℝ)^(12:ℕ) ≤ 10^16 := by norm_num
    have hzR : (10:ℝ)^16 ≤ (z:ℝ) := by exact_mod_cast hz
    rw [h36e]
    linarith
  have h36a := h36 a ha
  -- both denominators are at least `log a`
  have haR : (0:ℝ) < (a:ℝ) := by
    have : (0:ℕ) < a := by omega
    exact_mod_cast this
  have hloga0 : (0:ℝ) < Real.log (a:ℝ) := by linarith
  have hlogau : Real.log (a:ℝ) ≤ Real.log (u:ℝ) :=
    Real.log_le_log haR (by exact_mod_cast hau)
  have hlogaX : Real.log (a:ℝ) ≤ Real.log (X:ℝ) :=
    Real.log_le_log haR (by exact_mod_cast (le_trans hau huX))
  -- lift both numerators to the top scale
  have hmonoX : halaszBudgetSharp A (X:ℝ)
      ≤ halaszBudgetSharp A (3*(B':ℝ)) := by
    refine halaszBudgetSharp_mono A _ _ hA0 ?_ ?_
    · have : (10:ℝ)^16 ≤ (X:ℝ) := by exact_mod_cast hX16
      linarith [he272]
    · have hc : (X:ℝ) ≤ ((3*B' : ℕ):ℝ) := by exact_mod_cast hX3B
      push_cast at hc
      linarith
  have hmonou : halaszBudgetSharp A (u:ℝ)
      ≤ halaszBudgetSharp A (3*(B':ℝ)) := by
    refine halaszBudgetSharp_mono A _ _ hA0 ?_ ?_
    · linarith [he272]
    · have huB : (u:ℝ) ≤ (B':ℝ) := by exact_mod_cast hu
      linarith [hB'R]
  have hquotX : halaszBudgetSharp A (X:ℝ) / Real.log (X:ℝ)
      ≤ halaszBudgetSharp A (3*(B':ℝ)) / Real.log (a:ℝ) :=
    div_le_div₀ hbudget0 hmonoX hloga0 hlogaX
  have hquotu : halaszBudgetSharp A (u:ℝ) / Real.log (u:ℝ)
      ≤ halaszBudgetSharp A (3*(B':ℝ)) / Real.log (a:ℝ) :=
    div_le_div₀ hbudget0 hmonou hloga0 hlogau
  have hsum : halaszBudgetSharp A (X:ℝ)/Real.log (X:ℝ)
      + halaszBudgetSharp A (u:ℝ)/Real.log (u:ℝ)
      ≤ 2 * halaszBudgetSharp A (3*(B':ℝ)) / Real.log (a:ℝ) := by
    have h2 : halaszBudgetSharp A (3*(B':ℝ)) / Real.log (a:ℝ)
        + halaszBudgetSharp A (3*(B':ℝ)) / Real.log (a:ℝ)
        = 2 * halaszBudgetSharp A (3*(B':ℝ)) / Real.log (a:ℝ) := by ring
    linarith [hquotX, hquotu]
  have hsumδ : (halaszBudgetSharp A (X:ℝ)/Real.log (X:ℝ)
      + halaszBudgetSharp A (u:ℝ)/Real.log (u:ℝ)) / δ₀
      ≤ 2 * halaszBudgetSharp A (3*(B':ℝ)) / (δ₀ * Real.log (a:ℝ)) := by
    rw [show 2 * halaszBudgetSharp A (3*(B':ℝ)) / (δ₀ * Real.log (a:ℝ))
      = (2 * halaszBudgetSharp A (3*(B':ℝ)) / Real.log (a:ℝ)) / δ₀ from by
        rw [div_div, mul_comm δ₀]]
    gcongr
  -- the edge term
  have hedge : (X:ℝ) - (u:ℝ) ≤ Real.exp 1 * (B':ℝ) * δ₀ + 1 := by
    have hexp1 : Real.exp δ₀ - 1 ≤ δ₀ * Real.exp δ₀ := by
      have h := Real.add_one_le_exp (-δ₀)
      have hprod : Real.exp δ₀ * Real.exp (-δ₀) = 1 := by
        rw [← Real.exp_add]
        simp
      nlinarith [Real.exp_pos δ₀]
    have huB : (u:ℝ) ≤ (B':ℝ) := by exact_mod_cast hu
    have hstep : (u:ℝ) * (Real.exp δ₀ - 1)
        ≤ (B':ℝ) * (δ₀ * Real.exp 1) := by
      have h1' : (u:ℝ) * (Real.exp δ₀ - 1)
          ≤ (u:ℝ) * (δ₀ * Real.exp δ₀) := by
        refine mul_le_mul_of_nonneg_left hexp1 hu0.le
      have h2' : (u:ℝ) * (δ₀ * Real.exp δ₀)
          ≤ (B':ℝ) * (δ₀ * Real.exp 1) := by
        have hδe0 : (0:ℝ) ≤ δ₀ * Real.exp δ₀ := by positivity
        have hδe : δ₀ * Real.exp δ₀ ≤ δ₀ * Real.exp 1 :=
          mul_le_mul_of_nonneg_left hexpδe hδ₀.le
        nlinarith [hu0.le, huB, hδe0]
      linarith
    nlinarith [hXle, hstep]
  unfold sharpPartialBudget
  linarith [hdiv, hsumδ, hedge]

/-- **The sharp twisted Dirichlet cost** (Track R, T0-5) of a block `(a, b]`:
`2·sharpPartialBudget A δ₀ a b/(a+1)` — no frequency cap `T`, no `W`. -/
noncomputable def sharpTwistedDirichletCost (A δ₀ : ℝ) (a b : ℕ) : ℝ :=
  2 * sharpPartialBudget A δ₀ a b / ((a + 1 : ℕ) : ℝ)

theorem sharpTwistedDirichletCost_nonneg (A δ₀ : ℝ) (a b : ℕ)
    (hA : 0 ≤ A) (hδ₀ : 0 < δ₀) (ha : 3 ≤ a) (hb : 3 ≤ b) :
    0 ≤ sharpTwistedDirichletCost A δ₀ a b := by
  have hbR : Real.exp 1 ≤ 3 * (b:ℝ) := by
    have : (3:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb
    linarith [Real.exp_one_lt_d9.le]
  have hbud := halaszBudgetSharp_nonneg A (3 * (b:ℝ)) hA hbR
  have hloga : (0:ℝ) < Real.log (a:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < a))
  unfold sharpTwistedDirichletCost sharpPartialBudget
  positivity

open Real Finset in
/-- **The sharp twisted Halász bound on a Dirichlet block** (Track R,
T0-5): for `g` completely multiplicative, `1`-bounded, non-pretentious at
strength `D ≥ 2` at every scale of `[a, 3b]` (`10¹⁶ ≤ a < b`), and any
frequency `|2πt| ≤ (D/2)·a`,

  `‖∑_{a<n≤b} g(n)·n⁻¹·e(−t·log n)‖ ≤ sharpTwistedDirichletCost (D/2) δ₀ a b`.

The phase is absorbed into the archimedean twist `g(n)·n^{−2πit}`, which is
`(D/2)`-non-pretentious on the block by `nonPretentiousAt_archTwist`; its
prefixes at `a` and at every `u ≤ b` obey the sharp prefix bound; Abel
summation against `1/n` closes.  Mirror of
`cheap_halasz_twisted_dirichlet_block` with the sharp budget in place of the
`W`-lossy cheap Halász. -/
theorem sharp_halasz_twisted_dirichlet_block
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg1 : g 1 = 1)
    (hgb : ∀ n, ‖g n‖ ≤ 1)
    (a b : ℕ) (hxa : 10^16 ≤ a) (hab : a < b)
    (D : ℝ) (hD : 2 ≤ D)
    (hnp : ∀ u : ℕ, a ≤ u → u ≤ 3 * b → NonPretentiousAt g D u)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₁ : δ₀ ≤ 1)
    (t : ℝ) (ht : |2 * Real.pi * t| ≤ (D / 2) * a) :
    ‖∑ n ∈ Finset.Ioc a b, (g n / (n : ℂ)) *
        ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
      ≤ sharpTwistedDirichletCost (D / 2) δ₀ a b := by
  classical
  let h : ℕ → ℂ := fun n =>
    g n * (n:ℂ)^(Complex.I*((-(2 * Real.pi * t) : ℝ):ℂ))
  have hcmh : CompletelyMultiplicativeC h :=
    hcm.mul (completelyMultiplicativeC_natCast_cpow _)
  have h1h : h 1 = 1 := by
    show g 1 * ((1:ℕ):ℂ)^(Complex.I*((-(2 * Real.pi * t) : ℝ):ℂ)) = 1
    rw [hg1, Nat.cast_one, Complex.one_cpow, mul_one]
  have hbh : ∀ n, ‖h n‖ ≤ 1 := by
    intro n
    show ‖g n * ((n:ℕ):ℂ)^(Complex.I*((-(2 * Real.pi * t) : ℝ):ℂ))‖ ≤ 1
    rw [norm_mul]
    calc ‖g n‖ * ‖((n:ℕ):ℂ)^(Complex.I*((-(2 * Real.pi * t) : ℝ):ℂ))‖
        ≤ 1 * 1 := mul_le_mul (hgb n) (norm_natCast_cpow_I_mul_le_one _ _)
          (norm_nonneg _) zero_le_one
      _ = 1 := mul_one 1
  have hD2 : (1:ℝ) ≤ D / 2 := by linarith
  have hNPh : ∀ u : ℕ, a ≤ u → u ≤ 3 * b → NonPretentiousAt h (D / 2) u := by
    intro u hau hub
    refine nonPretentiousAt_archTwist (hnp u hau hub) (by linarith) ?_
    have hau' : (a:ℝ) ≤ (u:ℝ) := by exact_mod_cast hau
    have hD0 : (0:ℝ) ≤ D / 2 := by linarith
    calc |2 * Real.pi * t| ≤ (D / 2) * (a:ℝ) := ht
      _ ≤ (D / 2) * (u:ℝ) := mul_le_mul_of_nonneg_left hau' hD0
      _ = (D - D / 2) * (u:ℝ) := by ring
  have hpre := prefix_le_sharpPartialBudget h hbh hcmh h1h a b hxa hab.le
    (D / 2) hD2 δ₀ hδ₀ hδ₁ hNPh
  have ha1 : 1 ≤ a + 1 := Nat.succ_pos _
  have hab1 : a + 1 ≤ b := by omega
  have hpartial : ∀ u : ℕ, a + 1 ≤ u → u ≤ b →
      ‖∑ n ∈ Finset.Icc (a + 1) u, h n‖
        ≤ 2 * sharpPartialBudget (D / 2) δ₀ a b := by
    intro u hau hub
    have hset : Finset.Icc (a + 1) u = Finset.Ioc a u := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hset]
    exact norm_sum_Ioc_le_two_prefix h a u (by omega) _
      (hpre a le_rfl hab.le) (hpre u (by omega) hub)
  have habSum := norm_sum_div_le_of_partial h (a + 1) b ha1 hab1
    (2 * sharpPartialBudget (D / 2) δ₀ a b) hpartial
  have hrewrite : ∑ n ∈ Finset.Ioc a b,
      (g n / (n : ℂ)) *
        ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ) =
      ∑ n ∈ Finset.Icc (a + 1) b, h n / (n : ℂ) := by
    rw [show Finset.Ioc a b = Finset.Icc (a + 1) b by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    rw [archTwist_phase_eq t n hn0]
    dsimp [h]
    ring
  rw [hrewrite]
  unfold sharpTwistedDirichletCost
  exact habSum

end MoltResearch
