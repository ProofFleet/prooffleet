import MoltResearch.Discrepancy.HalaszSharpTwist
import MoltResearch.Discrepancy.ExceptionalHalaszTwist

/-!
# The exceptional-cell recut at the windowed sharp Halász cost

VI-9e (`ExceptionalHalaszTwist.lean`) recut the exceptional-cell pointwise
bound so that the Fourier phase rides inside the completely multiplicative
twist (no `3 + 2πT` Abel loss) and every Ramaré quotient is charged its own
long/short cost.  Two things made it unconsumable (design report, "The `𝒯₀`
leg"): its long-quotient input was the cheap twisted Halász with its
`(log b)^{W}` loss, `W ≥ 22`; and its frequency condition
`|2πt| ≤ (D/2)·((A/q)/n₁)` was demanded for *every* `P`-smooth `n₁ ≤ B/q`,
which forces `t = 0` as soon as `B/q > A/q`.

This leaf is the same chain with the long-quotient input replaced by the
windowed sharp twisted Dirichlet block
`sharp_halasz_twisted_dirichlet_block_window` (T0-6), whose cost
`sharpTwistedDirichletCost D δ₀ a b` carries the sharp budget `Ĥ⁺` with
`(D+1)·e^{−D}` and no `loglog`, and whose only hypothesis is the Halász
window of the twisted function on the quotient scales — demanded here **only
on long quotients** (`(A/q)/n₁ ≥ x₀`, a cutoff parameter `x₀ ≥ 10¹⁶` chosen
by the consumer — the bridge from the top scale `N` loses
`2(loglog N − loglog u + 12)`, bounded only for `u ≥ N^{c}`; short quotients
are charged their harmonic mass and need nothing).  The window is stated on `g·n^{−2πit}` at
strength `2D` and transferred to every level-free twist at strength `D` by
Ramaré robustness (`halaszWindowAt_levelFreeTwist_archTwist`); the consumer
supplies it from the top-scale `NonPretentiousAt` through the bridge
`halaszWindowAt_archTwist_of_nonPretentiousAt`, with no constraint tying the
frequency `t` to the quotient scale.

* `sharpQuotientCost`, `norm_filter_levelFreeTwist_quotient_le_sharp` — one
  `P`-free quotient (long: sharp, short: harmonic);
* `sharpRamareCost`, `norm_levelFreeTwist_ramare_poly_le_sharp` — Ramaré
  weight removal with the per-quotient sharp costs (the generic seam
  `norm_ramare_weighted_poly_le_sum_cost` of VI-9e reused verbatim);
* `cellHalaszSharpBound`, `norm_typicalS_quot_block_poly_le_sharp` — the cell
  representative block after inclusion–exclusion, `2^{#rest}` terms.

The `ε`-form (`sharpTwistedDirichletCost ≲ 17(b/a)√E` at `δ₀ ≍ √E`) is the
next unit.
-/

namespace MoltResearch

open Finset ExpSums

/-- **Ramaré robustness for the Halász window** (Track R, T0-6b): the window
of the twisted `g·n^{−iξ}` at strength `2D` gives the window of every twisted
level-free function `levelFreeTwist g levels · n^{−iξ}` at strength `D`. -/
theorem halaszWindowAt_levelFreeTwist_archTwist (g : ℕ → ℂ)
    (hg : ∀ n, ‖g n‖ ≤ 1) (levels : List (Finset ℕ)) (D ξ : ℝ) (u : ℕ)
    (hwin : HalaszWindowAt
      (fun n => g n * (n:ℂ)^(Complex.I*((-ξ : ℝ):ℂ))) (2 * D) u) :
    HalaszWindowAt
      (fun n => levelFreeTwist g levels n * (n:ℂ)^(Complex.I*((-ξ : ℝ):ℂ)))
      D u := by
  intro t ht
  have hbase := hwin t ht
  have heq : (fun n => levelFreeTwist g levels n * (n:ℂ)^(Complex.I*((-ξ : ℝ):ℂ)))
      = fun n => (g n * (n:ℂ)^(Complex.I*((-ξ : ℝ):ℂ))) * levelFreeIndicator levels n := by
    funext n
    rw [levelFreeTwist_eq_mul_indicator]
    ring
  rw [heq]
  have hgtw : ∀ p, ‖g p * (p:ℂ)^(Complex.I*((-ξ : ℝ):ℂ))‖ ≤ 1 := by
    intro p
    rw [norm_mul]
    calc ‖g p‖ * ‖(p:ℂ)^(Complex.I*((-ξ : ℝ):ℂ))‖
        ≤ 1 * 1 := mul_le_mul (hg p) (norm_natCast_cpow_I_mul_le_one _ _)
          (norm_nonneg _) zero_le_one
      _ = 1 := mul_one 1
  have hrobust := pretentiousDistSq_mul_weight_ge_of_norm_le_one
    (fun n => g n * (n:ℂ)^(Complex.I*((-ξ : ℝ):ℂ))) (levelFreeIndicator levels)
    (charTwist 1 1 (2 * Real.pi * t)) u hgtw (charTwist_norm_le_one 1 1 _)
    (fun p => by classical unfold levelFreeIndicator; split_ifs <;> simp)
    (fun p => by classical unfold levelFreeIndicator; split_ifs <;> simp)
    (fun p => by classical unfold levelFreeIndicator; split_ifs <;> simp)
  beta_reduce at hrobust
  linarith

/-- The sharp long/short cost of one Ramaré quotient `(a, b]`: the windowed
sharp twisted Dirichlet cost at strength `D` when `a ≥ x₀` (the consumer's
cutoff, itself `≥ 10¹⁶`), the exact harmonic mass otherwise. -/
noncomputable def sharpQuotientCost (x0 : ℕ) (D δ₀ : ℝ) (a b : ℕ) : ℝ :=
  if x0 ≤ a then sharpTwistedDirichletCost D δ₀ a b
  else cellHalaszTrivialCost a b

theorem sharpQuotientCost_nonneg (x0 : ℕ) (hx0 : cellHalaszThreshold ≤ x0)
    (D δ₀ : ℝ) (a b : ℕ)
    (hD : 0 ≤ D) (hδ₀ : 0 < δ₀) (hab : a ≤ b) :
    0 ≤ sharpQuotientCost x0 D δ₀ a b := by
  unfold sharpQuotientCost
  split_ifs with h
  · have ha3 : 3 ≤ a := le_trans (by norm_num [cellHalaszThreshold]) (le_trans hx0 h)
    exact sharpTwistedDirichletCost_nonneg D δ₀ a b hD hδ₀ ha3 (le_trans ha3 hab)
  · unfold cellHalaszTrivialCost
    positivity

/-- **One `P`-free quotient at the sharp cost** (Track R, T0-6b): the
`P`-free restriction of a level-free twist on `(a, b]` is the unrestricted
twist for `P :: levels`; on a long quotient it is priced by the windowed
sharp block at strength `D` (from the window of `g·n^{−2πit}` at `2D` by
Ramaré robustness), on a short one by its harmonic mass.  The window is
demanded only when the quotient is long. -/
theorem norm_filter_levelFreeTwist_quotient_le_sharp
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg1 : g 1 = 1)
    (hgb : ∀ n, ‖g n‖ ≤ 1)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (levels : List (Finset ℕ)) (hlevels : ∀ Q ∈ levels, ∀ p ∈ Q, p.Prime)
    (x0 : ℕ) (hx0 : cellHalaszThreshold ≤ x0)
    (a b : ℕ) (hab : a ≤ b) (D : ℝ) (hD : 1 ≤ D) (t : ℝ)
    (hwin : x0 ≤ a → ∀ u : ℕ, a ≤ u → u ≤ 3 * b →
      HalaszWindowAt
        (fun n => g n * (n:ℂ)^(Complex.I*((-(2 * Real.pi * t) : ℝ):ℂ))) (2 * D) u)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₁ : δ₀ ≤ 1) :
    ‖∑ n ∈ (Finset.Ioc a b).filter (fun n => ∀ p ∈ P, ¬ p ∣ n),
        (levelFreeTwist g levels n / (n : ℂ)) *
          ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
      ≤ sharpQuotientCost x0 D δ₀ a b := by
  rw [sum_filter_levelFreeTwist_eq_cons]
  have hcons : ∀ Q ∈ P :: levels, ∀ p ∈ Q, p.Prime := by
    intro Q hQ p hp
    rw [List.mem_cons] at hQ
    rcases hQ with rfl | hQ
    · exact hP p hp
    · exact hlevels Q hQ p hp
  by_cases hcut : x0 ≤ a
  · rw [sharpQuotientCost, if_pos hcut]
    have hcut16 : cellHalaszThreshold ≤ a := le_trans hx0 hcut
    rcases eq_or_lt_of_le hab with rfl | hablt
    · simp only [Finset.Ioc_self, sum_empty, norm_zero]
      have ha3 : 3 ≤ a := le_trans (by norm_num [cellHalaszThreshold]) hcut16
      exact sharpTwistedDirichletCost_nonneg D δ₀ a a (by linarith) hδ₀ ha3 ha3
    · exact sharp_halasz_twisted_dirichlet_block_window
        (levelFreeTwist g (P :: levels))
        (completelyMultiplicativeC_levelFreeTwist g hcm (P :: levels) hcons)
        (levelFreeTwist_one g hg1 (P :: levels) hcons)
        (norm_levelFreeTwist_le_one g hgb (P :: levels))
        a b (show 10^16 ≤ a from hcut16) hablt D hD t
        (fun u hau hub => halaszWindowAt_levelFreeTwist_archTwist g hgb
          (P :: levels) D (2 * Real.pi * t) u (hwin hcut u hau hub))
        δ₀ hδ₀ hδ₁
  · rw [sharpQuotientCost, if_neg hcut]
    exact norm_dirichlet_poly_le_harmonic
      (levelFreeTwist g (P :: levels))
      (norm_levelFreeTwist_le_one g hgb (P :: levels)) a b t

/-- The sum of the per-quotient sharp charges after Ramaré weight removal. -/
noncomputable def sharpRamareCost (x0 : ℕ) (D δ₀ : ℝ) (A B : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ n1 ∈ (Finset.Icc 1 B).filter (fun n => n.primeFactors ⊆ P),
    (1 : ℝ) / n1 * sharpQuotientCost x0 D δ₀ (A / n1) (B / n1)

/-- **The Ramaré-weighted level-free twist at the sharp cost** (Track R,
T0-6b): the accounting seam `norm_ramare_weighted_poly_le_sum_cost` with the
sharp quotient charges; the window is demanded only on long quotients. -/
theorem norm_levelFreeTwist_ramare_poly_le_sharp
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg1 : g 1 = 1)
    (hgb : ∀ n, ‖g n‖ ≤ 1)
    (levels : List (Finset ℕ)) (hlevels : ∀ Q ∈ levels, ∀ p ∈ Q, p.Prime)
    (A B : ℕ) (hAB : A ≤ B)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (x0 : ℕ) (hx0 : cellHalaszThreshold ≤ x0)
    (D : ℝ) (hD : 1 ≤ D) (t : ℝ)
    (hwin : ∀ n1 ∈ (Finset.Icc 1 B).filter (fun n => n.primeFactors ⊆ P),
      x0 ≤ A / n1 →
      ∀ u : ℕ, A / n1 ≤ u → u ≤ 3 * (B / n1) →
        HalaszWindowAt
          (fun n => g n * (n:ℂ)^(Complex.I*((-(2 * Real.pi * t) : ℝ):ℂ))) (2 * D) u)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₁ : δ₀ ≤ 1) :
    ‖∑ n ∈ Finset.Ioc A B,
        (levelFreeTwist g levels n / (n : ℂ)) *
          ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ) /
            (((P.filter (· ∣ n)).card : ℂ) + 1)‖
      ≤ sharpRamareCost x0 D δ₀ A B P := by
  unfold sharpRamareCost
  apply norm_ramare_weighted_poly_le_sum_cost
    (levelFreeTwist g levels)
    (completelyMultiplicativeC_levelFreeTwist g hcm levels hlevels)
    (norm_levelFreeTwist_le_one g hgb levels) A B P hP t
    (fun n1 => sharpQuotientCost x0 D δ₀ (A / n1) (B / n1))
  intro n1 hn1
  exact norm_filter_levelFreeTwist_quotient_le_sharp g hcm hg1 hgb P hP
    levels hlevels x0 hx0 (A / n1) (B / n1) (Nat.div_le_div_right hAB) D hD t
    (hwin n1 hn1) δ₀ hδ₀ hδ₁

/-- The complete sharp pointwise envelope of a cell representative block
after inclusion–exclusion: `2^{#rest}` level-free twists, each at the sharp
Ramaré cost. -/
noncomputable def cellHalaszSharpBound (x0 : ℕ)
    (D δ₀ : ℝ) (Aq Bq : ℕ) (P : Finset ℕ) (rest : List (Finset ℕ)) : ℝ :=
  ((2 ^ rest.length : ℕ) : ℝ) * sharpRamareCost x0 D δ₀ Aq Bq P

/-- **The exceptional-cell pointwise bound at the sharp cost** (Track R,
T0-6b): `norm_typicalS_quot_block_poly_le_recut` with the windowed sharp
Halász in place of the cheap one.  For any frequency `t`, under the Halász
window of `g·n^{−2πit}` at strength `2D` on the long quotient ranges
`[(A/q)/n₁, 3·((B/q)/n₁)]` (`(A/q)/n₁ ≥ x₀`) — supplied from the top-scale
`NonPretentiousAt` by `halaszWindowAt_archTwist_of_nonPretentiousAt` — the
representative polynomial is at most
`cellHalaszSharpBound D δ₀ (A/q) (B/q) P rest`. -/
theorem norm_typicalS_quot_block_poly_le_sharp
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg1 : g 1 = 1)
    (hgb : ∀ n, ‖g n‖ ≤ 1)
    (A B q : ℕ) (hAB : A ≤ B)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (hrest : ∀ Q ∈ rest, ∀ p ∈ Q, p.Prime)
    (x0 : ℕ) (hx0 : cellHalaszThreshold ≤ x0)
    (D : ℝ) (hD : 1 ≤ D) (t : ℝ)
    (hwin : ∀ n1 ∈ (Finset.Icc 1 (B / q)).filter (fun n => n.primeFactors ⊆ P),
      x0 ≤ (A / q) / n1 →
      ∀ u : ℕ, (A / q) / n1 ≤ u → u ≤ 3 * ((B / q) / n1) →
        HalaszWindowAt
          (fun n => g n * (n:ℂ)^(Complex.I*((-(2 * Real.pi * t) : ℝ):ℂ))) (2 * D) u)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₁ : δ₀ ≤ 1) :
    ‖∑ n ∈ Finset.Ioc (A / q) (B / q),
        (typicalSQuotCoeff g P (typicalS 0 B rest) n / (n : ℂ)) *
          ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
      ≤ cellHalaszSharpBound x0 D δ₀ (A / q) (B / q) P rest := by
  have hBqB : B / q ≤ B := Nat.div_le_self _ _
  refine (norm_typicalSQuotCoeff_poly_le_inclexcl g P rest
    (A / q) (B / q) B hBqB t).trans ?_
  let C := sharpRamareCost x0 D δ₀ (A / q) (B / q) P
  calc
    (rest.sublists.map fun S =>
        ‖∑ n ∈ Finset.Ioc (A / q) (B / q),
            (levelFreeTwist g S n / (n : ℂ)) *
              ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ) /
                (((P.filter (· ∣ n)).card : ℂ) + 1)‖).sum
        ≤ (rest.sublists.map fun _ => C).sum := by
      apply List.sum_le_sum
      intro S hS
      exact norm_levelFreeTwist_ramare_poly_le_sharp g hcm hg1 hgb S
        (by
          intro Q hQS p hp
          exact hrest Q ((List.mem_sublists.mp hS).mem hQS) p hp)
        (A / q) (B / q) (Nat.div_le_div_right hAB) P hP x0 hx0 D hD t hwin δ₀ hδ₀ hδ₁
    _ = cellHalaszSharpBound x0 D δ₀ (A / q) (B / q) P rest := by
      rw [show (rest.sublists.map fun _ => C) =
          List.replicate rest.sublists.length C from List.map_const,
        List.sum_replicate, List.length_sublists, nsmul_eq_mul]
      simp only [C, cellHalaszSharpBound]

end MoltResearch
