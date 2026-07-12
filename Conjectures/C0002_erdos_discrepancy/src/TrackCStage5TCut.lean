import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5VinogradovKorobov

/-!
# Track C: Stage 5 — the `𝐭`-cut, deterministic core (Tao 2015 §4, Lemma "tb")

Consumer of the Vinogradov–Korobov interface (issue #2871, PR F2): the deterministic heart of
the `𝐭`-cutting lemma of arXiv:1509.05363 §4 (proof of the generalized Borwein–Choi–Coons
theorem). There, two applications of Proposition 1.11 at nearby scales produce two pretense
certificates for the *same* multiplicative function `g`:

`𝔻(g, χ(·)·(·)^{i𝐭}; X^δ)² ≤ B` and `𝔻(g, χ'(·)·(·)^{i𝐭'}; X^δ)² ≤ B`,

with bounded periods (`q, q' ≤ Q`) and frequencies of polynomial size (`|𝐭|, |𝐭'| ≤ T·X`).
Tao concludes `|𝐭 − 𝐭'| = O_ε(X^δ)`; this file proves the clean form `|𝐭 − 𝐭'| < X^δ` for all
sufficiently large `X` (threshold depending only on `Q, T, B, δ` — crucially not on `g`).

The three-move proof, exactly as in the source:
1. **Quasi-triangle** (`pretentiousDistSq_quasi_triangle`, pivot `g`, constant `3`): the two
   character twists are within squared distance `3·B + 3·B = 6·B` of each other.
2. **Twist composition** (`pretentiousDistSq_one_charTwist_mul`): that pair distance *equals*
   the distance from the constant `1` to the single composite twist at modulus `q·q'`,
   character `changeLevel χ · (changeLevel χ')⁻¹`, frequency `𝐭 − 𝐭'`.
3. **Vinogradov–Korobov** (`vinogradovKorobov_twist_far` at modulus bound `Q·Q`, frequency
   bound `2·T`, target `M = 6·B + 1`): if `X^δ ≤ |𝐭 − 𝐭'|` (and `|𝐭 − 𝐭'| ≤ |𝐭| + |𝐭'| ≤ 2·T·X`),
   the composite twist is eventually at squared distance `≥ 6·B + 1` from `1` — contradicting
   move 1+2. Hence `|𝐭 − 𝐭'| < X^δ`.

Constants are crude and explicit per house convention (`6·B + 1` where the paper says `≪_ε 1`).
The hypothesis `0 ≤ B` is kept for the natural call-site shape (Prop-1.11 outputs are
nonnegative distances) though the contradiction `6·B + 1 ≤ 6·B` never consults it.
-/

namespace MoltResearch

namespace Tao2015

/-- **The `𝐭`-cut, deterministic core** (Tao 2015, arXiv:1509.05363 §4, Lemma "tb"): under the
Vinogradov–Korobov twist input, for all sufficiently large `X` (threshold depending only on the
period bound `Q`, the frequency bound `T`, the pretense budget `B`, and the scale exponent
`δ ∈ (0,1)`), any two character twists of period `≤ Q` and frequency `≤ T·X` that both pretend
to be the same unimodular `g` at scale `X^δ` — squared pretentious distance `≤ B` — have
frequencies within `X^δ` of each other.

Proof: quasi-triangle through the pivot `g` caps the pair distance by `6·B`; twist composition
rewrites that pair distance as the distance from `1` to the composite twist at modulus `q·q'`
and frequency `t − t'`; if `|t − t'|` were `≥ X^δ`, Vinogradov–Korobov (instantiated at modulus
bound `Q·Q`, frequency bound `2·T`, target `6·B + 1`) would force that same distance
`≥ 6·B + 1` — a contradiction. -/
theorem tcut_of_vinogradovKorobov [VinogradovKorobovAssumption]
    (Q T B : ℝ) (hQ : 1 ≤ Q) (hT : 1 ≤ T) (hB : 0 ≤ B)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ g : ℕ → ℂ, Unimodular g →
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
        1 ≤ q → (q : ℝ) ≤ Q → |t| ≤ T * X →
        pretentiousDistSq g (charTwist q χ t) ⌊X ^ δ⌋₊ ≤ B →
      ∀ (q' : ℕ) (χ' : DirichletCharacter ℂ q') (t' : ℝ),
        1 ≤ q' → (q' : ℝ) ≤ Q → |t'| ≤ T * X →
        pretentiousDistSq g (charTwist q' χ' t') ⌊X ^ δ⌋₊ ≤ B →
        |t - t'| < X ^ δ := by
  -- Vinogradov–Korobov at composite modulus bound `Q·Q`, composite frequency bound `2·T`,
  -- and pretense target `6·B + 1` (one more than the quasi-triangle cap below).
  have hQQ : (1 : ℝ) ≤ Q * Q := by nlinarith
  have h2T : (1 : ℝ) ≤ 2 * T := by linarith
  obtain ⟨X₀, hX₀⟩ := vinogradovKorobov_twist_far (Q := Q * Q) (T := 2 * T)
    (M := 6 * B + 1) hQQ h2T hδ0 hδ1
  refine ⟨X₀, ?_⟩
  intro X hX g hg q χ t hq1 hqQ ht hcert q' χ' t' hq'1 hq'Q ht' hcert'
  by_contra hfar
  rw [not_lt] at hfar
  -- The composite frequency `t − t'` is in the Vinogradov–Korobov range.
  have habs : |t - t'| ≤ 2 * T * X := by
    have h1 : |t - t'| ≤ |t| + |t'| := abs_sub t t'
    linarith
  -- The composite modulus `q·q'` is in the Vinogradov–Korobov range.
  have hq0 : q ≠ 0 := by omega
  have hq'0 : q' ≠ 0 := by omega
  have hqq'1 : 1 ≤ q * q' := by simpa using Nat.mul_le_mul hq1 hq'1
  have hqq'Q : ((q * q' : ℕ) : ℝ) ≤ Q * Q :=
    natCast_mul_le_mul hqQ hq'Q (zero_le_one.trans hQ)
  -- Vinogradov–Korobov: the composite twist is far from `1` ...
  have hVK := hX₀ X hX (q * q')
    (DirichletCharacter.changeLevel (dvd_mul_right q q') χ *
      (DirichletCharacter.changeLevel (dvd_mul_left q' q) χ')⁻¹)
    hqq'1 hqq'Q (t - t') hfar habs
  rw [pretentiousDistSq_one_charTwist_mul hq0 hq'0 χ χ' t t'] at hVK
  -- ... but the quasi-triangle inequality through the pivot `g` caps that distance by `6·B`.
  have htri := pretentiousDistSq_quasi_triangle hg
    (charTwist_norm_le_one q χ t) (charTwist_norm_le_one q' χ' t') ⌊X ^ δ⌋₊
  linarith

-- Consumer example (compile-only), instantiating every quantifier: at period bound `Q = 7`,
-- frequency bound `T = 7`, pretense budget `B = 3`, and scale exponent `δ = 1/2`, any two
-- Prop-1.11 certificates for the same unimodular `g` have frequencies within `X^(1/2)`.
example [VinogradovKorobovAssumption] :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ g : ℕ → ℂ, Unimodular g →
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
        1 ≤ q → (q : ℝ) ≤ 7 → |t| ≤ 7 * X →
        pretentiousDistSq g (charTwist q χ t) ⌊X ^ (1/2 : ℝ)⌋₊ ≤ 3 →
      ∀ (q' : ℕ) (χ' : DirichletCharacter ℂ q') (t' : ℝ),
        1 ≤ q' → (q' : ℝ) ≤ 7 → |t'| ≤ 7 * X →
        pretentiousDistSq g (charTwist q' χ' t') ⌊X ^ (1/2 : ℝ)⌋₊ ≤ 3 →
        |t - t'| < X ^ (1/2 : ℝ) :=
  tcut_of_vinogradovKorobov 7 7 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end Tao2015

end MoltResearch
