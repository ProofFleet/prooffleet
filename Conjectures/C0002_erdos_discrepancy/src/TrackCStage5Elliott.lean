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

/-- Uniform (inf-form) non-pretentiousness — the hypothesis shape of the paper's *asymptotic*
corollary (arXiv:1509.05422, Corollary 1.5): for every character `χ` and every `A ≥ 1`, the
pretentious distance to the twists `n ↦ χ(n)·nⁱᵗ` diverges **uniformly over `|t| ≤ A·x`** as
the truncation `x` grows.

Strictly stronger than the pointwise `NonPretentious` (see
`NonPretentiousUniform.nonPretentious`); the distinction is load-bearing — the pointwise form
cannot feed the nonasymptotic Theorem 1.3. -/
def NonPretentiousUniform (g : ℕ → ℂ) : Prop :=
  ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (A : ℝ), 1 ≤ A →
    ∀ b : ℝ, ∀ᶠ x : ℕ in Filter.atTop, ∀ t : ℝ, |t| ≤ A * x →
      b ≤ pretentiousDistSq g (charTwist q χ t) x

/-- Uniform non-pretentiousness implies the pointwise form. -/
theorem NonPretentiousUniform.nonPretentious {g : ℕ → ℂ}
    (h : NonPretentiousUniform g) : NonPretentious g := by
  intro q χ t
  rw [Filter.tendsto_atTop]
  intro b
  filter_upwards [h q χ 1 le_rfl b, Filter.eventually_ge_atTop ⌈|t|⌉₊] with x hx hxt
  refine hx t ?_
  calc |t| ≤ (⌈|t|⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (x : ℝ) := by exact_mod_cast hxt
    _ = 1 * (x : ℝ) := (one_mul _).symm

/-- **Log-averaged two-point Elliott assumption** (asymptotic first cut).

For completely multiplicative unimodular `g` that is non-pretentious in the **pointwise** sense
and distinct shifts `a ≠ b`, the log-averaged correlation `logAvgCorr g a b N` tends to `0`.

**Strength warning (found while formalizing the nonasymptotic form):** the paper's asymptotic
corollary (arXiv:1509.05422, Cor 1.5) requires the *uniform* (inf-form) non-pretentiousness
`NonPretentiousUniform`; this class assumes only the weaker pointwise `NonPretentious`, so it
is a **stronger-than-literature** statement, mirroring the deterministic Fourier first cut.
Derivation-(C) work must consume `LogElliottNonasymptoticAssumption` below; this class is
retained as a convenience for toy consumers.

No instance of this class is (or may be) declared in this repository until such a statement is
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

/-- **Nonasymptotic log-averaged two-point Elliott assumption**
(arXiv:1509.05422, Theorem 1.3, restricted to the completely multiplicative subclass — a
strictly weaker statement, sufficient for the van der Corput argument).

Quantifier structure verbatim from the source: affine forms `a₁n+b₁`, `a₂n+b₂` with
`a₁·b₂ ≠ a₂·b₁` (shifts restricted to `ℕ`, again strictly weaker); for every `ε > 0` a
threshold `A₀` (depending on `ε` and the affine data) such that for all `A ≥ max A₀ 1`, all
real `x ≥ w ≥ A`, and all 1-bounded completely multiplicative `g₁, g₂` with `g₁`
non-pretentious at strength `A` and truncation `⌈x⌉₊`, the log-averaged windowed correlation is
at most `ε · log w`.

Encoding notes (junk-value conventions per the derivation card):
- The window `x/w < n ≤ x` is exactly `Finset.Ioc ⌊x/w⌋₊ ⌊x⌋₊` (`Nat.floor_lt` both ways).
- The hypothesis `NonPretentiousAt g₁ A ⌈x⌉₊` *implies* the paper's hypothesis at real
  truncation `x`: its `|t|`-range `A·⌈x⌉₊` contains the paper's `A·x`, and its prime range
  `p < ⌈x⌉₊` is contained in the paper's `p ≤ x` (distance monotone with 1-bounded twists) —
  so this statement follows from Theorem 1.3.

No instance of this class is (or may be) declared until Theorem 1.3 is actually formalized
(entropy decrement + Matomäki–Radziwiłł; expected to stay an interface for a long time).
-/
class LogElliottNonasymptoticAssumption : Prop where
  bound :
    ∀ (a₁ a₂ b₁ b₂ : ℕ), 0 < a₁ → 0 < a₂ → a₁ * b₂ ≠ a₂ * b₁ →
      ∀ ε : ℝ, 0 < ε →
        ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A → 1 ≤ A →
          ∀ x w : ℝ, A ≤ w → w ≤ x →
            ∀ g₁ g₂ : ℕ → ℂ,
              CompletelyMultiplicativeC g₁ → (∀ n, ‖g₁ n‖ ≤ 1) →
              CompletelyMultiplicativeC g₂ → (∀ n, ‖g₂ n‖ ≤ 1) →
              NonPretentiousAt g₁ A ⌈x⌉₊ →
              ‖∑ n ∈ Finset.Ioc ⌊x / w⌋₊ ⌊x⌋₊,
                  g₁ (a₁ * n + b₁) * g₂ (a₂ * n + b₂) / (n : ℂ)‖ ≤ ε * Real.log w

-- Consumer example (compile-only), instantiating every quantifier per the derivation card's
-- gotcha: the two-point shifted-correlation call site of the van der Corput argument
-- (a₁ = a₂ = 1, distinct shifts, g₂ = conj g₁), at concrete window parameters.
example [inst : LogElliottNonasymptoticAssumption] {g : ℕ → ℂ}
    (hmul : CompletelyMultiplicativeC g) (hg1 : ∀ n, ‖g n‖ ≤ 1)
    (hmulc : CompletelyMultiplicativeC fun n => (starRingEnd ℂ) (g n))
    (hg1c : ∀ n, ‖(starRingEnd ℂ) (g n)‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A → 1 ≤ A →
      ∀ x w : ℝ, A ≤ w → w ≤ x →
        NonPretentiousAt g A ⌈x⌉₊ →
        ‖∑ n ∈ Finset.Ioc ⌊x / w⌋₊ ⌊x⌋₊,
            g (1 * n + 0) * (starRingEnd ℂ) (g (1 * n + 1)) / (n : ℂ)‖ ≤ ε * Real.log w := by
  obtain ⟨A₀, hA₀⟩ := inst.bound 1 1 0 1 one_pos one_pos (by norm_num) ε hε
  exact ⟨A₀, fun A hA hA1 x w hAw hwx hnp =>
    hA₀ A hA hA1 x w hAw hwx g (fun n => (starRingEnd ℂ) (g n)) hmul hg1 hmulc hg1c hnp⟩

end Tao2015

end MoltResearch
