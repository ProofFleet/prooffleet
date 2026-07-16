# Source statements: Tao 2015 (EDP + two-point Elliott)

Purpose: the **quotable source of truth** for the Track C / analytic-core interface classes.
Every interface in `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5*.lean` should be
diffable against the text here, not against a paraphrase in a docstring.

Provenance and caveat: transcribed 2026-07-10 from the ar5iv HTML renderings of
arXiv:1509.05363 ("The Erdős discrepancy problem", Discrete Analysis 2016) and
arXiv:1509.05422 ("The logarithmically averaged Chowla and Elliott conjectures for two-point
correlations", Forum Math. Pi 2016). These are faithful quotes/close transcriptions of the
rendered text, but they have **not** been verified against the published PDFs by a human —
do that before relying on fine details (constant conventions, strictness of inequalities) in
proofs. Corrections to this file are one-line PRs.

Notation: `𝐠` (bold) marks *stochastic* objects; `S¹` is the complex unit circle;
`𝔻(g,h;x)²  = ∑_{p≤x} (1 − Re g(p)·conj(h(p)))/p` is the (squared) Granville–Soundararajan
pretentious distance.

---

## arXiv:1509.05363 — The Erdős discrepancy problem

### Theorem 1.1 (EDP, vector-valued)

> For any Hilbert space `H` and function `f : ℕ → H` with `‖f(n)‖_H = 1` for all `n`, the
> discrepancy `sup_{n,d} ‖∑_{j=1}^n f(jd)‖_H` is infinite.

Lean: the surface statement `¬ BoundedDiscrepancy f` for sign sequences (`Corollary 1.2`
specialization) is the Track C target; the vector-valued form is not yet encoded.

### Theorem 1.8 (stochastic multiplicative form)

> If `𝐠 : ℕ → S¹` is a stochastic completely multiplicative function, then
> `sup_n 𝔼|∑_{j=1}^n 𝐠(j)|² = +∞`.

Lean: `Tao2015.theorem18` (`TrackCStage5Derivation.lean`) — currently *conditional* on
`VanDerCorputAssumption` + `BorweinChoiCoonsAssumption`, phrased as
`¬ ∃ C, ∀ n, sndMomentPartialSum G n ≤ C`.

### Theorem 1.9 (measure-theoretic restatement of 1.8)

> Given a probability space `(Ω, μ)` and a measurable `g : Ω → (S¹)^ℕ` with `g(ω)` completely
> multiplicative for almost every `ω`, then `sup_n ∫_Ω |∑_{j=1}^n g(ω)(j)|² dμ(ω) = +∞`.

Lean: this *is* the encoding — `StochasticMultiplicative`
(`MoltResearch/Discrepancy/StochasticMultiplicative.lean`) bundles exactly this data, so no
separate 1.8-vs-1.9 restatement is needed. Deviation: values are `ℂ` with `∀ᵐ` unimodularity
rather than literal `S¹`.

### Theorem 1.10 (= Theorem 1.3 of 1509.05422; see below)

Stated in 1509.05363 as the imported input; the companion paper's numbering (Thm 1.3) is used
by our interfaces.

### Proposition 1.11 (van der Corput argument)

> Suppose that `𝐠 : ℕ → S¹` is a stochastic completely multiplicative function, such that
> `𝔼|∑_{j=1}^n 𝐠(j)|² ≤ C²` for all natural numbers `n`. Then for large `X` and small `ε`,
> with probability `1 − O(ε)`, one can find a stochastic Dirichlet character `𝛘` of period
> `q = O_{C,ε}(1)` and real `𝐭 = O_{C,ε}(X)` such that
> `∑_{p≤X} (1 − Re 𝐠(p)·conj(𝛘(p))·p^{−i𝐭})/p ≪_{C,ε} 1`.

Lean: `VanDerCorputAssumption` (`TrackCStage5VanDerCorput.lean`). Known deviations, each
weakening the statement (hygiene-safe):
- per-sample existential over the event set `pretentiousEvent` instead of a stochastic
  (measurable) selection `(𝛘, 𝐭)`;
- the probability constant `K` may depend on `C` (paper: implied constant in `O(ε)`), but is
  quantified **before** `ε` — `K = K(ε)` would make the statement vacuous;
- bound stated as `C` not `C²` (cosmetic: quantified over all bounds).

### §2 (Fourier reduction; no numbered proposition)

> The failure of Theorem 1.1 (a bounded-discrepancy `f`) implies the failure of Theorem 1.8,
> via Fourier analysis on `(ℤ/Mℤ)^r` over primes up to `X` (building on Polymath5). That is:
> a bounded-discrepancy sequence yields a stochastic completely multiplicative function with
> uniformly bounded second moment of partial sums.

Lean: `FourierReductionStochasticAssumption` (`TrackCStage5Fourier.lean`). The repo also keeps
the **deterministic first cut** `FourierReductionAssumption`, which is *stronger than this
source statement* (it implies the stochastic form via point-mass embedding — machine-checked —
while the converse fails); it is demoted to toy-consumer use.

### §4 (generalized Borwein–Choi–Coons; no numbered theorem)

> A completely multiplicative function satisfying the conclusion of Proposition 1.11 (i.e.
> pretending to be `χ(n)·n^{it}`) has partial sums whose second moment grows (the
> Borwein–Choi–Coons phenomenon, extended to modulated characters and the stochastic
> setting), contradicting the standing bound.

Lean: `BorweinChoiCoonsAssumption` (`TrackCStage5Derivation.lean`), in contrapositive
consumer form. **This is the least literal interface in the repo** (there is no numbered
source statement to transcribe); it is the typed target of the derivation card's two §4
boxes, and should be revised freely if the §4 proof wants a different factoring.

### §4, Lemma "tb" input (Vinogradov–Korobov twist non-pretentiousness)

> For a Dirichlet character `χ₁` of period `O_ε(1)` and `X^δ ≤ |s| ≪_ε X`, one has
> `∑_{exp((log X)^{2/3}) ≤ p ≤ X^δ} (1 − Re χ₁(p) p^{−is})/p ≫ log log X`
> for `X` sufficiently large depending on `ε, δ`.

Derived in the source from the Vinogradov–Korobov zero-free region for `L(·, χ₁)`
(Montgomery §9.5), a `|log L| ≪ log^{O(1)}|t|` bound in that region, and the contour-shifting
argument of [Matomäki–Radziwiłł, short-intervals note, Lemma 2]. The classical zero-free
region is quantitatively insufficient (width `c/log X` vs the needed `≍ 1/(δ log X)`).

Lean: `VinogradovKorobovAssumption` (`TrackCStage5VinogradovKorobov.lean`). Known
deviations, each weakening the statement (hygiene-safe):
- conclusion summed over all primes `p < ⌊X^δ⌋₊` (`pretentiousDistSq` with constant-1 base
  point; summands nonnegative, so at least the source's sub-range sum);
- the `≫ log log X` divergence weakened to "for every `M`, eventually `≥ M`";
- sign convention `p^{+is}` (the symmetric `|s|`-range absorbs `s ↦ −s`);
- restricted to `1 ≤ q` (the source's Dirichlet-character scope).

No instance, no axiom: the §4 target is
`instance [LogElliottNonasymptoticAssumption] [VinogradovKorobovAssumption] :
BorweinChoiCoonsAssumption` (issue #2871).

**Ledger update (2026-07-16, PR #2918)**: the target landed *stronger* than planned —
`instance [VinogradovKorobovAssumption] : BorweinChoiCoonsAssumption`
(`TrackCStage5BCCWrapper.lean`), with **no Elliott input**: the §4 branch needs only the
second-moment bound (Markov), the VK t-cut, and the deterministic endgame. Theorem 1.8's
deep-input set is exactly `{LogElliottNonasymptoticAssumption, VinogradovKorobovAssumption}`
(`theorem18_of_logElliott_vinogradovKorobov`).

---

## arXiv:1509.05422 — log-averaged Chowla/Elliott for two-point correlations

### Theorem 1.3 (logarithmically averaged nonasymptotic Elliott)

> Let `a₁, a₂` be natural numbers, and let `b₁, b₂` be integers such that `a₁b₂ − a₂b₁ ≠ 0`.
> Let `ε > 0`, and suppose that `A` is sufficiently large depending on `ε, a₁, a₂, b₁, b₂`.
> Let `x ≥ ω ≥ A`, and let `g₁, g₂ : ℕ → ℂ` be multiplicative functions with
> `|g₁(n)|, |g₂(n)| ≤ 1` for all `n`, with `g₁` "non-pretentious" in the sense that
> `∑_{p≤x} (1 − Re g₁(p)·conj(χ(p))·p^{−it})/p ≥ A`
> for all Dirichlet characters `χ` of period at most `A`, and all real numbers `t` with
> `|t| ≤ Ax`. Then
> `|∑_{x/ω<n≤x} g₁(a₁n+b₁)·g₂(a₂n+b₂)/n| ≤ ε log ω`.

Lean: `LogElliottNonasymptoticAssumption` (`TrackCStage5Elliott.lean`). Known deviations,
each weakening the statement:
- `g₁, g₂` restricted to **completely** multiplicative (paper: multiplicative);
- shifts `b₁, b₂ : ℕ` (paper: `ℤ`);
- window encoded as `Finset.Ioc ⌊x/w⌋₊ ⌊x⌋₊` (exact: `Nat.floor_lt`);
- non-pretentiousness hypothesis given as `NonPretentiousAt g₁ A ⌈x⌉₊`, which **implies** the
  paper's hypothesis at real truncation `x` (larger `|t|`-range, smaller prime range +
  monotonicity).

### Corollary 1.5 (logarithmically averaged Elliott, asymptotic)

> Let `a₁, a₂` be natural numbers, and let `b₁, b₂` be integers such that `a₁b₂ − a₂b₁ ≠ 0`.
> Let `g₁, g₂ : ℕ → ℂ` be multiplicative functions bounded in magnitude by one, with `g₁`
> non-pretentious in the sense that
> `inf_{|t|≤Ax} ∑_{p≤x} (1 − Re g₁(p)·conj(χ(p))·p^{−it})/p → ∞`
> as `x → ∞`, for all Dirichlet characters `χ` and all `A ≥ 1`. Then for any
> `1 ≤ ω(x) ≤ x` going to infinity as `x → ∞`, one has
> `∑_{x/ω(x)<n≤x} g₁(a₁n+b₁)·g₂(a₂n+b₂)/n = o(log ω(x))`.

**The hypothesis is the uniform (inf-over-`t`) form, not pointwise in `t`.** Lean:
`NonPretentiousUniform` encodes the hypothesis, and the corollary is `Tao2015.corollary15`
(`TrackCStage5Elliott.lean`), **proved** from `LogElliottNonasymptoticAssumption` via the
finitely-many-characters bridge. Known deviations, each weakening the statement: completely
multiplicative `gᵢ`; `ℕ`-shifts; `o(log ω(x))` encoded in `ε`-form
(`∀ ε > 0, ∀ᶠ x, ‖·‖ ≤ ε·log(w x)`); window hypothesis `w x ≤ x` required only eventually and
`1 ≤ ω(x)` dropped (implied eventually by divergence). The repo's earlier
`LogElliottAssumption` (pointwise `NonPretentious` hypothesis) is *stronger than this source
statement* and is demoted to toy-consumer use.
