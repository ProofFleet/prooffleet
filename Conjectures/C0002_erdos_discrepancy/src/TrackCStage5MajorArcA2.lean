import MoltResearch.Discrepancy.MajorArcBlockScale

/-!
# Track C: Stage 5 — the `[mrt]` A.2 Prop and the restricted major-arc block bound (R6-8)

`SliceMeanSquareA2` is the **one** Prop the major-arc assembly (Track R, R6/R7) is
conditional on: `[mrt]` Theorem A.2 in the tree's shape — the mean square of the
`𝒮`-restricted window sums of a non-pretentious `1`-bounded completely multiplicative
function over a dyadic block is `ε²h²` times the block's harmonic mass — together with
the two facts about the level list `𝒮 = 𝒮(levels)` that the wrapper consumes without
looking inside the levels.  The list is chosen at a base scale `A₁` and serves the
whole scale window `[A₁, A₁²]`:

* the level primes lie above `C·(log h)^B` for the requested polylog, so that every
  modulus `q ≤ C(log H)^B` of the major arcs is coprime to every level and the residue
  classes dilate inside `𝒮` (`hasFactorInAll_mul_left_iff`);
* the `𝒮ᶜ` log-density on dyadic blocks above `A₀` is at most `εc` (the `[mrt]`
  Lemma-"excep" / Turán–Kubilius fact, `window_typicalS_complement_le`), which prices the
  once-paid `𝒮ᶜ` removal (`sum_card_filter_window_div_le`).

Design (`Problems/tao2015_a1_r6r7_design_report.md` §1.2, §7.3, §8, Finding E and
Phase 4): the residue split precedes the freeze, so **one** window length `h` serves
every class and character, and the Prop is invoked at a single `(ε, h)`; the threshold
in `h` is polynomial in `1/ε` (`C₁/ε^k ≤ h`) because the consumer takes
`ε ≍ ε₀/(log H)^B`, while the density parameter `εc` is fixed and may cost an arbitrary
threshold `h₁`.  The threshold `A₀` is chosen after `h`; then, for every `A₁ ≥ A₀`, a
level list depending on `A₁` serves all `A ∈ [A₁, A₁²]`.  This is `[mrt]`'s `X₀`
device: the underlying level sequence is fixed but its truncation depends on the scale
window, allowing the last anchor level to reach height `(log A₁)^40`.

The theorem `majorArc_block_bound_restricted` is R6-8 of the report: it feeds the A.2
data of one such `(levels, A₀, h, ε)` to every class and character of
`sum_restricted_window_logavg_le_of_meanSquare`, the twists' non-pretentiousness coming
from `nonPretentiousAt_charMul_of_block`.

No instance of, or proof of, `SliceMeanSquareA2` is declared here: it is discharged by the
A.2 campaign (Phase 0 / A2-IV / A2-V of the report).
-/

namespace MoltResearch

namespace Tao2015

open ExpSums

/-- The finite set of A.2 scales consumed on the major-arc dyadic block `(A,2A]`
when all arc denominators are at most `Q`:

`S(A,Q) = [A / ⌈Q⌉₊ - 1, 3A] ∩ ℕ`.

The reindexed class starts used by R6 lie in this interval: their least possible
start is `A / q - 1`, with `q ≤ ⌈Q⌉₊`, and their endpoint guard is
`A' + J ≤ 3A`.  It also contains the two density-clause starts `A` and `2A`
used by the once-paid exceptional-set removal. -/
noncomputable def majorArcScaleSet (A : ℕ) (Q : ℝ) : Finset ℕ :=
  Finset.Icc (A / ⌈Q⌉₊ - 1) (3 * A)

/-- **`[mrt]` Theorem A.2, `𝒮`-restricted, on dyadic blocks** (Track R; the Prop the
major-arc assembly is conditional on).

For every density parameter `εc > 0` and polylog data `(B, C)` there are a threshold
`h₁` and polynomial constants `(C₁, k)` such that for every `ε > 0` and every window
length `h ≥ h₁` with `C₁/ε^k ≤ h` there is a threshold `A₀ ≥ 1`.  For every base scale
`A₁ ≥ A₀` there is a level list `levels`, chosen for that scale window, whose primes
lie above `C(log h)^B`; on every `A ∈ [A₁, A₁²]`, its `𝒮ᶜ` log-density on `(A,2A]` is
at most `εc`, and every `1`-bounded completely multiplicative `g` with `g(1) = 1`,
non-pretentious at strength `A₀` and truncation `2A+1`, has `𝒮`-restricted mean square
at most `ε²h²·∑_{(A,A+J]} 1/n` on `(A,A+J]`, `A/2 ≤ J ≤ A`.

The order `∃ A₀, ∀ A₁, ∃ levels, ∀ A ∈ [A₁,A₁²]` is `[mrt]`'s `X₀` device.  In
particular `A₀` is still chosen after `h`, while the finite level list may grow with
the scale window. -/
def SliceMeanSquareA2 : Prop :=
  ∀ (εc : ℝ), 0 < εc → ∀ (B : ℕ) (C : ℝ), 0 < C →
    ∃ (h₁ : ℕ) (C₁ : ℝ) (k : ℕ), 0 < C₁ ∧
    ∀ (ε : ℝ), 0 < ε → ∀ h : ℕ, h₁ ≤ h → C₁ / ε ^ k ≤ h →
      ∃ A₀ : ℝ, 1 ≤ A₀ ∧
        ∀ A₁ : ℕ, A₀ ≤ A₁ →
          ∃ levels : List (Finset ℕ),
            (∀ P ∈ levels, ∀ p ∈ P, p.Prime) ∧
            (∀ P ∈ levels, ∀ p ∈ P, C * Real.log h ^ B < p) ∧
            (∀ A : ℕ, A₁ ≤ A → A ≤ A₁ ^ 2 →
              ∑ n ∈ (Finset.Ioc A (2 * A)).filter (fun n => ¬ HasFactorInAll levels n), (1:ℝ)/n
                ≤ εc * ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n) ∧
            (∀ A : ℕ, A₁ ≤ A → A ≤ A₁ ^ 2 →
              ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → (∀ n, ‖g n‖ ≤ 1) → g 1 = 1 →
                NonPretentiousAt g A₀ (2 * A + 1) →
                ∀ J : ℕ, A / 2 ≤ J → J ≤ A →
                  ∑ n ∈ Finset.Ioc A (A + J),
                    ‖∑ m ∈ (Finset.Ioc n (n + h)).filter (HasFactorInAll levels), g m‖^2 / n
                    ≤ ε^2 * (h : ℝ)^2 * ∑ n ∈ Finset.Ioc A (A + J), (1:ℝ)/n)

/-- The integer block threshold inherited from `⌈A₀⌉₊ + 1 ≤ A/q` preserves the
scale condition `2 ≤ ε'A₀`. -/
theorem two_le_mul_nat_sub_one_of_ceil_add_one_le (ε' A₀ : ℝ) (A q : ℕ)
    (hε' : 0 ≤ ε') (hε'A₀ : 2 ≤ ε' * A₀) (hA₀q : ⌈A₀⌉₊ + 1 ≤ A / q) :
    2 ≤ ε' * ((A / q - 1 : ℕ) : ℝ) := by
  have hA₀le : A₀ ≤ ((A / q - 1 : ℕ) : ℝ) :=
    le_trans (Nat.le_ceil A₀) (by exact_mod_cast (by omega : ⌈A₀⌉₊ ≤ A / q - 1))
  exact hε'A₀.trans (mul_le_mul_of_nonneg_left hA₀le hε')

/-- **R6-8: the `𝒮`-restricted major-arc bound on a dyadic block, from the A.2 data.**

Given the mean-square clause of `SliceMeanSquareA2` for one `(levels, A₀, h₀, ε')` at
the scales `S(A,Q) = [A / ⌈Q⌉₊ - 1, 3A] ∩ ℕ`, a unimodular completely
multiplicative `g` that is non-pretentious at strength `q·A₀ + 26` and truncation
`6A+1`, a modulus `q ≤ Q` below every level, and the size conditions
`2 ≤ ε'A₀`, `2h₀ ≤ H`, `6qH ≤ A`, `7q² ≤ A`, `⌈A₀⌉₊ + 1 ≤ ⌊A/q⌋`:

  `∑_{n∈(A,2A]} ‖∑_{(n,n+H]∩𝒮} g(m)e(m(a/q+δ))‖/(Hn)
      ≤ (16qε' + qh₀/H + 4πq²|δ|h₀)·∑_{(A,2A]} 1/n`.

The A.2 clause is applied to every twist `χ·g` (`χ` mod `q/d`, `d ∣ q`): completely
multiplicative (`completelyMultiplicativeC_charMul`), `1`-bounded (`norm_charMul_le_one`),
`1` at `1` (`charMul_one`), and non-pretentious at every block truncation `2A'+1`
(`nonPretentiousAt_charMul_of_block`).  The proof invokes it only at the reindexed
starts `A'` in `S(A,Q)`; no assertion at scales outside this finite set is used. -/
theorem majorArc_block_bound_restricted
    (levels : List (Finset ℕ)) (hlv : ∀ P ∈ levels, ∀ p ∈ P, p.Prime)
    (A₀ : ℝ) (hA₀1 : 1 ≤ A₀) (h₀ : ℕ) (ε' : ℝ) (hε' : 0 ≤ ε')
    (hε'A₀ : 2 ≤ ε' * A₀)
    (Q : ℝ) (A : ℕ)
    (hA2 : ∀ A' : ℕ, A' ∈ majorArcScaleSet A Q →
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → (∀ n, ‖g n‖ ≤ 1) → g 1 = 1 →
        NonPretentiousAt g A₀ (2 * A' + 1) →
        ∀ J : ℕ, A' / 2 ≤ J → J ≤ A' →
          ∑ n ∈ Finset.Ioc A' (A' + J),
            ‖∑ m ∈ (Finset.Ioc n (n + h₀)).filter (HasFactorInAll levels), g m‖^2 / n
            ≤ ε'^2 * (h₀ : ℝ)^2 * ∑ n ∈ Finset.Ioc A' (A' + J), (1:ℝ)/n)
    (g : ℕ → ℂ) (hg : CompletelyMultiplicativeC g) (hgu : Unimodular g)
    (q : ℕ) (hq : 0 < q) (hqQ : (q : ℝ) ≤ Q)
    (hql : ∀ P ∈ levels, ∀ p ∈ P, ¬ p ∣ q) (a : ℤ) (δ : ℝ)
    (H : ℕ) (hh₀ : 0 < h₀) (h2h₀ : 2 * h₀ ≤ H) (hA : 6 * q * H ≤ A)
    (hA7 : 7 * q ^ 2 ≤ A) (hA₀q : ⌈A₀⌉₊ + 1 ≤ A / q)
    (hnp : NonPretentiousAt g (q * A₀ + 26) (6 * A + 1)) :
    ∑ n ∈ Finset.Ioc A (2 * A),
        ‖∑ m ∈ (Finset.Ioc n (n + H)).filter (HasFactorInAll levels),
          g m * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ)
            * (((a : ℝ) / (q : ℝ) + δ : ℝ) : ℂ))‖ / ((H : ℝ) * n)
      ≤ (16 * q * ε' + q * h₀ / H + 4 * Real.pi * q^2 * |δ| * h₀)
          * ∑ n ∈ Finset.Ioc A (2 * A), (1:ℝ)/n := by
  have hb : ∀ m, ‖g m‖ ≤ 1 := fun m => (hgu m).le
  have hg1 : g 1 = 1 := hg.map_one_of_unimodular hgu
  have hA₀0 : 0 ≤ A₀ := by linarith
  have hqceil : q ≤ ⌈Q⌉₊ := by
    exact_mod_cast hqQ.trans (Nat.le_ceil Q)
  -- the A.2 input is fed on blocks starting within one of `⌊A/q⌋`
  refine sum_restricted_window_logavg_le_of_meanSquare g hg hb levels hlv q hq hql a δ A H h₀
    hh₀ h2h₀ hA ε' hε' (A / q - 1) (by omega)
      (two_le_mul_nat_sub_one_of_ceil_add_one_le ε' A₀ A q hε' hε'A₀ hA₀q) ?_
  intro d hd0 hdq χ A' J hA'1 hJ2 hJ hA'J
  have hscale : A' ∈ majorArcScaleSet A Q := by
    rw [majorArcScaleSet, Finset.mem_Icc]
    constructor
    · exact (Nat.sub_le_sub_right (Nat.div_le_div_left hqceil hq) 1).trans hA'1
    · omega
  have hA₀A' : A₀ ≤ A' :=
    le_trans (Nat.le_ceil A₀) (by exact_mod_cast (by omega : ⌈A₀⌉₊ ≤ A'))
  have hnp' : NonPretentiousAt (fun n => χ n * g n) A₀ (2 * A' + 1) :=
    nonPretentiousAt_charMul_of_block g hgu hA₀0 hq hd0 hdq χ A A' hA7 (by omega) (by omega) hnp
  exact hA2 A' hscale (fun n => χ n * g n) (completelyMultiplicativeC_charMul g hg χ)
    (norm_charMul_le_one g hb χ) (charMul_one g hg1 χ) hnp' J hJ2 hJ

end Tao2015

end MoltResearch
