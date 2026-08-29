import MoltResearch.Discrepancy

/-!
# Track C: Stage 5 interface — Vinogradov–Korobov twist input (Tao 2015 §4, Lemma "tb")

This file is **Conjectures-only** glue: the typed statement of the third deep input of the
Tao 2015 derivation, identified while decomposing the §4 (generalized Borwein–Choi–Coons)
box on issue #2871.

**The source fact** (arXiv:1509.05363 §4, proof of the `𝐭`-cutting lemma): for a Dirichlet
character `χ₁` of bounded period and a frequency `s` with `X^δ ≤ |s| ≪ X`, the twist
`n ↦ χ₁(n)·n^{is}` does **not** pretend to be `1` at scale `X^δ`; quantitatively

`∑_{exp((log X)^{2/3}) ≤ p ≤ X^δ} (1 − Re χ₁(p) p^{−is})/p ≫ log log X`.

Tao derives this from the **Vinogradov–Korobov zero-free region** for `L(·, χ₁)` (Montgomery
§9.5) together with a `|log L|`-bound in that region and the contour-shifting argument of
[Matomäki–Radziwiłł, "A note on the Liouville function in short intervals", Lemma 2]. The
classical (Hadamard–de la Vallée Poussin) region is quantitatively insufficient here: its
width `c/log|s| ≍ c/log X` is smaller than the needed `≍ 1/(δ log X)` once `δ` is small.

**Why this is load-bearing** (finding recorded on #2871): the `𝐭`-cut `𝐭 = O_ε(X^δ)` cannot
be avoided by re-running Proposition 1.11 at scale `X^δ` — that loses `2·log(1/δ)` in the
pretense constant, which is fatal because `δ` is chosen *after* `H` while the final §4
contradiction needs an `ε`-only constant.

Encoding notes (hygiene: each choice weakens the statement, so it is implied by the source):
- The conclusion sums over all primes `p < ⌊X^δ⌋₊` (`pretentiousDistSq _ _ ⌊X^δ⌋₊` with the
  constant-1 base point); summands are nonnegative (`1` is unimodular, twists are 1-bounded),
  so this is at least the source's sub-range sum.
- The source's `≫ log log X` divergence is weakened to "for every target `M`, eventually
  `≥ M`" — all the §4 consumer needs (defeating an `O_ε(1)` upper bound).
- The frequency range is `X^δ ≤ |s| ≤ T·X` with the sign symmetric (the source's `p^{−is}`
  vs this file's `charTwist` convention `p^{+is}` differ by `s ↦ −s`, which the range absorbs).
- `1 ≤ q` keeps the statement within the source's Dirichlet-character scope (the `q = 0`
  junk case would be vacuously fine but is unsourced).

Axiom hygiene (issue #2843 / card §6): a `class` with **no instance and no axiom** — its
proof needs zero-free-region technology far beyond current Mathlib and stays an interface
for the foreseeable future. Consumers carry it as a hypothesis; the §4 target is
`instance [LogElliottNonasymptoticAssumption] [VinogradovKorobovAssumption] :
BorweinChoiCoonsAssumption`.
-/

namespace MoltResearch

namespace Tao2015

/-- **Vinogradov–Korobov twist input** (Tao 2015, arXiv:1509.05363 §4, Lemma "tb" —
qualitative form): a character twist `n ↦ χ(n)·n^{is}` of bounded period whose frequency is
large for the scale (`X^δ ≤ |s| ≤ T·X`) is eventually arbitrarily far from `1` in pretentious
distance at scale `X^δ`.

Discharged unconditionally by `vinogradovKorobov_unconditional`
(`TrackCStage5VKDischarge.lean`), which proves the interface outright from the elementary
van der Corput zeta bound, so consumers need not carry it as a hypothesis. The class is kept
as the named boundary the §4 branch is stated against. -/
class VinogradovKorobovAssumption : Prop where
  twist_far :
    ∀ Q T M : ℝ, 1 ≤ Q → 1 ≤ T →
      ∀ δ : ℝ, 0 < δ → δ < 1 →
        ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
          ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 1 ≤ q → (q : ℝ) ≤ Q →
            ∀ s : ℝ, X ^ δ ≤ |s| → |s| ≤ T * X →
              M ≤ pretentiousDistSq (fun _ => 1) (charTwist q χ s) ⌊X ^ δ⌋₊

/-- Consumer-facing restatement as a plain theorem, so the §4 `𝐭`-cutting lemma can use it
without projecting the class field. -/
theorem vinogradovKorobov_twist_far [inst : VinogradovKorobovAssumption]
    {Q T M : ℝ} (hQ : 1 ≤ Q) (hT : 1 ≤ T) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 1 ≤ q → (q : ℝ) ≤ Q →
        ∀ s : ℝ, X ^ δ ≤ |s| → |s| ≤ T * X →
          M ≤ pretentiousDistSq (fun _ => 1) (charTwist q χ s) ⌊X ^ δ⌋₊ :=
  inst.twist_far Q T M hQ hT δ hδ0 hδ1

-- Consumer example (compile-only), instantiating every quantifier per the card's gotcha:
-- the Lemma-"tb" call site shape — the composite character `χ·conj χ'` of the two
-- Prop-1.11 events, at frequency `s = 𝐭' − 𝐭` in the critical range, defeats a given
-- pretense bound `M` at scale `X^(1/2)`.
example [VinogradovKorobovAssumption] (M : ℝ) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 1 ≤ q → (q : ℝ) ≤ 7 →
        ∀ s : ℝ, X ^ (1/2 : ℝ) ≤ |s| → |s| ≤ 3 * X →
          M ≤ pretentiousDistSq (fun _ => 1) (charTwist q χ s) ⌊X ^ (1/2 : ℝ)⌋₊ :=
  vinogradovKorobov_twist_far (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Tao2015

end MoltResearch
