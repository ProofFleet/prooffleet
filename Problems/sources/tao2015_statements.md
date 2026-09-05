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

---

## Large values of Dirichlet polynomials (Track R, A2-III IV-1/IV-2)

Provenance and caveat: these two are **not** from the two Tao papers above. They are the
literature inputs the Matomäki–Radziwiłł leg quotes, recorded here because this file is the
registry `scripts/check_interfaces.py` diffs interface classes against. Transcribed
2026-08-30 from the Track R design analysis, **not** from the published texts — verify
constants and the exact exponent against the sources before relying on fine details. Both
live in `Conjectures/C0002_erdos_discrepancy/src/Interfaces/LargeValues.lean`; neither has
an instance, and neither may be given one until formalized.

### Iwaniec–Kowalski, *Analytic Number Theory* (AMS Colloq. Publ. 53, 2004), Theorem 9.6

> For a Dirichlet polynomial of length `N` and points `t₁, …, t_R ∈ [−T, T]` that are
> pairwise separated by at least `1`,
> `∑_r |∑_{n≤N} a_n n^{−it_r}|² ≪ (N + R√T)·log(2T)·∑_{n≤N} |a_n|²/n²`.

Lean: `HalaszLargeValuesAssumption`. Deviations, all in the direction of a weaker (easier to
discharge, still sufficient) statement: the implied constant is fixed at `64`; `log(2T)` is
written `log(2T) + 1`; coefficients are `1/n`-normalised to match the repo's phase-polynomial
convention (`a n/n · e(−t log n)`).

### Matomäki–Radziwiłł, *Multiplicative functions in short intervals*, Annals 183 (2016), Lemma 8

> For a Dirichlet polynomial supported on the primes of `[P, 2P]` and `1`-separated points
> in `[−T, T]`, the same sum is bounded by
> `(1 + R·exp(−log P/(log 2T)^{2/3+ε})·(log 2T)²)·(∑_p |a_p|²/p²)·P/log P`.

Lean: `PrimeLargeValuesAssumption`. Deviations: constant fixed at `64`; the exponent
`2/3 + ε` is replaced by the fixed rational `3/4` (any exponent `< 1` carries the consumer,
and a numeral keeps the class statement free of an extra quantifier).

**This is the irreducible input.** Its only known proof is duality plus a Mellin shift of
`ζ'/ζ` into the Vinogradov–Korobov zero-free region; there is no elementary argument, and no
Mathlib substrate at the pinned revision. The in-tree elementary ladder reaches the *measure*
of the large-frequency set (`measure_large_prime_poly_le`) and the measure-to-count bridge for
general polynomials (Gallagher, `sum_norm_sq_le_integral_of_separated`); the prime-supported
*count* is exactly what is missing, and exactly what this class supplies.

### Matomäki--Radziwiłł--Tao, *An averaged form of Chowla's conjecture*, Appendix A

In the proof of Proposition A.3, let `t₁` attain the minimum of the pretentious
distance on `|t| ≤ X`.  The argument preceding Lemma A.4 uses the standard
archimedean-twist repulsion estimate, uniformly for `|t| ≤ X`, to obtain a fixed
positive multiple of `log log X` outside the small window around `t₁`.

Lean: `FarRegimeRepulsionAssumption`.  The class records only the far subrange
`(log y)^20 < |t-t₁|`, assumes both frequencies lie in `[-y,y]` and that `t₁`
is a minimizer, and concludes the weaker fixed floor
`(1/6 - 1/(3π)) log log y`.  An explicit existential lower threshold replaces the
paper's asymptotic qualification.  No instance may be declared until the
Erdős--Turán/equidistribution proof is formalized.

---

## arXiv:1503.05121 — An averaged form of Chowla's conjecture ([mrt])

Provenance and caveat: transcribed 2026-09-03 from the ar5iv HTML rendering of
arXiv:1503.05121 (Matomäki–Radziwiłł–Tao, *An averaged form of Chowla's conjecture*,
Algebra & Number Theory 9 (2015)). Same standard as the rest of this file: a faithful
transcription of rendered text, **not** verified against the published PDF by a human —
check constant conventions and strictness before relying on fine details.

This is the paper the Track R campaign calls `[mrt]`. The A.2 band campaign
(`Problems/tao2015_a2iii_design_report.md`) targets the Dirichlet-polynomial `L²`
bound below; issue #3044's plan reads **A.1 ⟸ A.2 + sieve density** and
**A.2 ⟸ Parseval + A.3**.

### Equation (1.6) — the pretentious distance functional

> `M(g;X) := inf_{|t| ≤ X} 𝔻(g, n ↦ n^{it}; X)²`

The infimum is over **real `t` with `|t| ≤ X`**. `𝔻` is the Granville–Soundararajan
distance already fixed in this file's notation preamble. In-tree this is
`NonPretentiousAt` / `PretentiousDist`.

### The set `𝒮` (Appendix A setup) — "typical factorization"

> `𝒮` is the set of integers `X ≤ n ≤ 2X` having **at least one prime factor in each**
> interval `[P_j, Q_j]`, `j = 1, …, J`, where the intervals satisfy conditions (A.1)
> and (A.2), `Q₁ ≤ exp(√(log X))`, and `J` is the largest index `j` with
> `Q_j ≤ exp((log X)^{1/2})`.

`η ∈ (0, 1/6)` is the parameter entering (A.1)/(A.2). In-tree this is
`MoltResearch.typicalS` (`MoltResearch/Discrepancy/TypicalFactorization.lean:51`),
with `HasFactorInAll` as the "one prime factor in each level" predicate; the cells
`eadicCell` are the `e`-adic refinement of a single `[P_j, Q_j]`.

### Theorem A.1 (unrestricted short-interval mean value)

> Let `f` be a 1-bounded multiplicative function and let `M(f,X)` be as in (1.6). Then,
> for `X ≥ h ≥ 10`,
> `(1/X) ∫_X^{2X} |(1/h) ∑_{x ≤ n ≤ x+h} f(n)|² dx`
> `≪ exp(−M(f,X))·M(f,X) + (log log h)²/(log h)² + 1/(log X)^{1/50}`.

This is the target of the whole Track R leg: it is what discharges
`MatomakiRadziwillMajorArcAssumption` once composed with the major-arc analysis (R6).
No Lean statement yet.

### Theorem A.2 (`𝒮`-restricted short-interval mean value)

> Let `f` be 1-bounded multiplicative. Let `𝒮` be as above with `η ∈ (0, 1/6)`. If
> `[P₁, Q₁] ⊂ [1, h]`, then for `X > X(η)` large and `h ≥ 3`,
> `(1/X) ∫_X^{2X} |(1/h) ∑_{x ≤ n ≤ x+h, n ∈ 𝒮} f(n)|² dx`
> `≪ exp(−M(f,X))·M(f,X) + (log h)^{1/3}/P₁^{1/6−η} + 1/(log X)^{1/50}`.

A.1 follows from this plus the density of the complement of `𝒮` — the step the tree
has the inputs for (`sifted_logavg_le`, `typicalS_complement_logavg_le`) but no bridge.

### Proposition A.3 (the Dirichlet-polynomial `L²` bound)

> Let `f` be 1-bounded multiplicative, `𝒮` as above with `η ∈ (0, 1/6)`, and
> `F(s) = ∑_{X ≤ n ≤ 2X, n ∈ 𝒮} f(n)/n^s`. Then for any `T ≥ 1`,
> `∫_{−T}^{T} |F(1+it)|² dt`
> `≪ (T/(X/Q₁) + 1)·( (log Q₁)^{1/3}/P₁^{1/6−η} + M(f,X)/exp(M(f,X)) + 1/(log X)^{1/50} )`.

**This is what the A2-III band campaign is building.** The correspondence with the
in-tree objects: `F(1+it)` is the normalised phase polynomial
`∑ (f n/n)·e(−t log n)`; the prefactor `(T/(X/Q₁) + 1)` is the sharp mean-value
theorem's `(T/(block length) + 2)`; the three error terms are, in order, the level
legs, the Halász input, and the exceptional `𝒰` leg.

⚠️ **Two arrangement differences to check before wiring A.3, not errors as far as this
transcription can tell.**

1. The paper's level saving is `P₁^{−(1/6−η)}` against the design report §4.3(d)'s
   `P₁^{−(1/2−3η)}`. Note `1/2 − 3η = 3·(1/6 − η)` **identically**, so the in-tree
   exponent is exactly three times the paper's; at the schedule's `η = 1/20` these are
   `0.35` and `7/60`. The report's form is the sharper one and is what
   `levelOne_le_budget` consumes.
2. The paper's prefactor is `(log Q₁)^{1/3}`; the report's is `log Q₁` (via `N₁² log Q₁`).

⚠️ **`1/(log X)^{1/50}` is the paper's own exceptional-leg term**, and it matches the
saving `D = (log A)^{−1/50}` that `BandSchedule.exceptional_W_le` is calibrated against.
That is an independent confirmation of S-cal-5's arithmetic.

### Theorem 2.3 — the parameter range for `W`

> `(log H)^5 ≤ W ≤ min{ H^{1/250}, (log X)^{1/125} }`

The same constraint appears in Proposition 2.4 and Proposition 5.1. This is the
"`Theorem second`" the design report §4.2 calibrates against, and the **upper end is
what Track R re-tunes**: `slice_energy_le` forces `Δ/A ≍ ε`, which costs `(A/Δ)²` in
the `𝒰` Halász step and moves `(log X)^{1/125}` to `(log X)^{1/320}`
(`BandSchedule.exceptional_report_exponent_ok`). The lower bound `(log H)^5` and the
other arm `H^{1/250}` of the `min` are untouched. Harmless for EDP, since `H → ∞`
remains admissible; it must be propagated when R6/R7 are wired.
