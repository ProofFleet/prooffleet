import MoltResearch.Discrepancy

/-!
# Track C: Stage 5 interface — log-averaged two-point Elliott assumption (Tao 2015, input (B))

This file is **Conjectures-only** glue: the typed statement of the second deep input of
Tao's Erdős-discrepancy proof (`Problems/tao2015_analytic_core.md`, interface layer).

**(B) Logarithmically averaged two-point Elliott** (arXiv:1509.05422, Theorem 1.3, in the
two-point shifted-correlation special case recorded on the card): if a completely
multiplicative unimodular `g : ℕ → ℂ` is *non-pretentious* — its pretentious distance to every
character-modulated archimedean twist `n ↦ χ(n)·nⁱᵗ` diverges — then for any distinct shifts
`a ≠ b` the log-averaged correlation `logAvgCorr g a b N` vanishes as `N → ∞`.

The full Theorem 1.3 allows two distinct 1-bounded multiplicative functions and general affine
forms `g₁(a₁n+b₁)·g₂(a₂n+b₂)`; the statement below is the strictly weaker specialization the
derivation (C) consumes (per the card's axiom-hygiene rule, interfaces may be the source
statement or strictly weaker).

Axiom hygiene (issue #2843 / card §6): a `class` with **no instance and no axiom** — its own
proof needs the entropy decrement argument and Matomäki–Radziwiłł and stays an interface for
the foreseeable future. Consumers carry it as a hypothesis.
-/

namespace MoltResearch

namespace Tao2015

/-- Non-pretentiousness (Granville–Soundararajan sense, squared-distance form): `g` does not
pretend to be any character-modulated archimedean twist `n ↦ χ(n)·nⁱᵗ` — for every modulus `q`,
Dirichlet character `χ mod q`, and `t : ℝ`, the finite-truncation squared pretentious distance
diverges.

Junk-value conventions are inherited from the language layer (`pretentiousDistSq`, `cpow` at
`0`); divergence of `𝔻²` is equivalent to divergence of `𝔻`.
-/
def NonPretentious (g : ℕ → ℂ) : Prop :=
  ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
    Filter.Tendsto (fun N => pretentiousDistSq g (charTwist q χ t) N)
      Filter.atTop Filter.atTop

/-- Bridge from the nonasymptotic non-pretentiousness language (`NonPretentiousAt`, the
Theorem-1.10 hypothesis shape) to the asymptotic form: uniform-in-`(χ, t)` nonasymptotic bounds
at every strength imply divergence against each fixed twist.

The converse direction is *not* derivable: the asymptotic form is pointwise in `(q, χ, t)` and
cannot supply the uniformity over the `|t| ≤ A·x` range that `NonPretentiousAt` demands. This
is why derivation (C) consumes the nonasymptotic interface, not this one. -/
theorem NonPretentious.of_forall_eventually_nonPretentiousAt {g : ℕ → ℂ}
    (h : ∀ A : ℝ, ∀ᶠ x in Filter.atTop, NonPretentiousAt g A x) :
    NonPretentious g := by
  intro q χ t
  rw [Filter.tendsto_atTop]
  intro b
  set A : ℝ := max (max b (q : ℝ)) |t| with hA
  have hbA : b ≤ A := le_trans (le_max_left _ _) (le_max_left _ _)
  have hqA : (q : ℝ) ≤ A := le_trans (le_max_right b _) (le_max_left _ _)
  have htA : |t| ≤ A := le_max_right _ _
  have hA0 : 0 ≤ A := le_trans (abs_nonneg t) htA
  filter_upwards [h A, Filter.eventually_ge_atTop 1] with x hx hx1
  have htx : |t| ≤ A * x := by
    calc |t| ≤ A := htA
      _ = A * 1 := (mul_one A).symm
      _ ≤ A * x := by
        have h1x : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
        exact mul_le_mul_of_nonneg_left h1x hA0
  exact le_trans hbA (hx q χ t hqA htx)

/-- **Log-averaged two-point Elliott assumption** (arXiv:1509.05422, Thm 1.3; two-point
shifted-correlation special case).

For completely multiplicative unimodular non-pretentious `g` and distinct shifts `a ≠ b`, the
log-averaged correlation `logAvgCorr g a b N` tends to `0`.

No instance of this class is (or may be) declared in this repository until the theorem is
actually formalized; consumers must carry it as a hypothesis.
-/
class LogElliottAssumption : Prop where
  vanish :
    ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → Unimodular g → NonPretentious g →
      ∀ a b : ℕ, a ≠ b →
        Filter.Tendsto (fun N => logAvgCorr g a b N) Filter.atTop (nhds (0 : ℂ))

/-- Consumer-facing restatement of the Elliott input as a plain theorem, so call sites can use
it without projecting the class field. -/
theorem logElliott_tendsto_zero [inst : LogElliottAssumption] {g : ℕ → ℂ}
    (hmul : CompletelyMultiplicativeC g) (hg : Unimodular g) (hnp : NonPretentious g)
    {a b : ℕ} (hab : a ≠ b) :
    Filter.Tendsto (fun N => logAvgCorr g a b N) Filter.atTop (nhds (0 : ℂ)) :=
  inst.vanish g hmul hg hnp a b hab

-- Consumer example (compile-only): the derivation-(C) call site — a non-pretentious
-- completely multiplicative unimodular sequence has vanishing correlation at distinct shifts,
-- in one application.
example [LogElliottAssumption] {g : ℕ → ℂ}
    (hmul : CompletelyMultiplicativeC g) (hg : Unimodular g) (hnp : NonPretentious g) :
    Filter.Tendsto (fun N => logAvgCorr g 0 1 N) Filter.atTop (nhds (0 : ℂ)) :=
  logElliott_tendsto_zero hmul hg hnp (by norm_num)

end Tao2015

end MoltResearch
