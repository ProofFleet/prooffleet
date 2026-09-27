# Formalizing the Erdős discrepancy theorem: notes on the route

These notes are for readers who know Tao's proof of the Erdős discrepancy theorem, or want to, and
wonder what changed on the way to a Lean proof. They say where the formal proof follows the
published papers, where it proves something weaker that is still enough, and where it had to take
a different path. The release record is [`edp-release.md`](edp-release.md); the structured
provenance is [`formalization.yaml`](../formalization.yaml).

A caveat first. The Lean development was written by AI agents (see `formalization.yaml`). The
observations below come from their design reports under `Problems/` and from the Lean sources.
Every statement about one of the four papers below was checked against its arXiv source, cited by
version; references to the book [IK] follow the repository's records. No specialist has reviewed
these notes. They describe one formalization; they are not claims of errors in the papers, and
corrections are welcome.

## The theorem and the shape of the proof

The formal statement is Tao's Corollary 1.2 [T1]: every sequence of signs ±1 has unbounded
discrepancy along homogeneous arithmetic progressions. It is stated with Mathlib alone in
[`PalomarEDP/Challenge.lean`](../PalomarEDP/Challenge.lean). The proof follows Tao's architecture
in three steps.

1. **Fourier reduction** ([T1] §2). A sequence of bounded discrepancy yields a stochastic
   completely multiplicative function with bounded mean-square partial sums
   (`TrackCStage5Fourier*.lean`; the limit uses `MoltResearch/Discrepancy/SpectralLaw.lean`).
2. **The van der Corput argument** ([T1] Proposition 1.11). Using the logarithmically averaged
   two-point Elliott estimate ([T2] Theorem 1.3, quoted as [T1] Theorem 1.10), such a function
   must pretend to be a twisted Dirichlet character `n ↦ χ(n) n^{it}`
   (`TrackCStage5VanDerCorput*.lean`; the Elliott estimate is assembled in
   `TrackCStage5Assembly.lean`).
3. **A generalized Borwein–Choi–Coons argument** ([T1] §4) rules that case out
   (`TrackCStage5BCCWrapper.lean`, `TrackCStage5TCut.lean`, `TrackCStage5VKDischarge.lean`).

The composed theorem is `MoltResearch.Tao2015.erdos_discrepancy_unconditional`
(`TrackCStage5PrimeLargeValuesDischarge.lean`). It depends only on Lean's three standard axioms.
Lean paths without a directory are under `Conjectures/C0002_erdos_discrepancy/src/`.

## Everything the papers cite is proved, usually in a weaker form

A paper may cite a published theorem; a Lean proof has to prove it. The development therefore
proves the results Tao's papers import, but in each case only the special case or the weaker
form this argument needs.

| Cited result | Used for | What the formal proof establishes |
| --- | --- | --- |
| Two-point logarithmically averaged Elliott estimate, [T2] Theorem 1.3 | Proposition 1.11 | Only for a completely multiplicative unimodular `g`, the pair `g`, `ḡ`, and natural-number shifts: the case the discrepancy problem uses |
| Matomäki–Radziwiłł–Tao, [MRT] Theorem A.2 | the major arcs inside the Elliott argument | a fixed-strength form of Theorem A.2, applied to each character twist |
| Large values of Dirichlet polynomials over primes, [MR] Lemma 11 | the exceptional set of frequencies | the saving `exp(−log P/(log T)^{4/5})` with an unspecified constant, instead of the exponent `2/3 + ε` |
| The Vinogradov–Korobov zero-free region for `ζ` | behind [MR] Lemma 11 | a zero-free region `σ > 1 − c (log T)^{−θ}` with `θ = 25/33 + 1/100 ≈ 0.77`, from a growth bound for `ζ` near `Re s = 1` with exponent `33/25` instead of `3/2`, via a weak form of Vinogradov's mean value theorem |
| The Vinogradov–Korobov zero-free region for `L(s, χ)`, [T1] Lemma 4.1 | the bound on the frequency `t` | not used at all: see note 1 |
| The Halász–Montgomery large-values inequality, [IK] Theorem 9.6 | large values of Dirichlet polynomials | proved with the explicit constant 64 |
| Vinogradov's estimates for exponential sums over primes, [IK] §13.5 | classifying frequencies into major and minor arcs | major arcs with denominators up to `(log n)^{20}`: see note 3 |

## Where the route differs

### 1. Section 4 needs much less than Vinogradov–Korobov

In the proof of [T1] Lemma 4.1, Tao applies "the Vinogradov-Korobov zero-free region for
`L(·, χχ̄′)`", a logarithmic bound for `log L` in that region and a contour shift, to show that

    Σ_{exp((log X)^{2/3}) ≤ p ≤ X^δ} (1 − Re χχ̄′(p) p^{−i(t′−t)}) / p  ≫  log log X

whenever `X^δ ≤ |t′ − t| ≪ X`, contradicting an `O_ε(1)` bound. The contradiction only needs
the sum to be unbounded, and that is all the formal proof establishes, with no zero-free region
for any `L`-function (`TrackCStage5VKDischarge.lean`):

- for the untwisted sum, an elementary van der Corput bound for `ζ` (`zeta_LSeries_bound` in
  `MoltResearch/Discrepancy/ZetaBound.lean`) gives a lower bound that grows like
  `log log log X`;
- the character is removed by a power trick: for `|z| = 1`, `1 − Re z^k ≤ k²(1 − Re z)`. With
  `k = φ(q)`, `χ(p)^k = 1` for every prime `p ∤ q`, so each twisted sum is at least `1/k²` times
  the untwisted sum at frequency `k·s`, up to an additive `O(q)`.

The interface file `TrackCStage5VinogradovKorobov.lean` records why a cheaper zero-free region
would not rescue Tao's quantitative form: the classical region's width, of order `1/log X`, is too
narrow once `δ` is small. Proving a weaker divergence sidesteps the question.

### 2. The prime large-values lemma with a weaker zero-free region

[MR] Lemma 11, their "Halász inequality for primes", saves a factor `exp(−log P/(log T)^{2/3+ε})`
for Dirichlet polynomials supported on primes, by shifting a contour into the zero-free region of
`ζ`; that exponent needs a region of Vinogradov–Korobov width. This application needs much less.
The formal proof uses the exponent `4/5` and an unspecified constant
(`Interfaces/LargeValues.lean`), and obtains the zero-free region in the table above from its own
growth bound for `ζ`, in `MoltResearch/Discrepancy/` (`VinogradovMeanValue.lean`,
`ZetaGrowth*.lean`, `ZeroFreeRegion*.lean`, `PrimeLargeValuesFromRegionH.lean`).

### 3. A shortcut that was not available

In the discrepancy application the pair `g₁ = g`, `g₂ = ḡ` has `c_p = 1` for every prime, and
[T2] (the paragraph after Proposition 2.6, and Remark 3.8) notes that the argument then
simplifies: the relevant frequencies are "'major arc' in the sense that `ξ/H` is close to a
rational `a/q` of bounded denominator `q`", so "the exponential sum estimates in [MRT, Lemma 2.2,
Theorem 2.3] can be replaced with the simpler estimate in [MRT, Theorem A.1]".

That description of the major arcs needs a classification of Siegel–Walfisz strength. The formal
proof classifies frequencies with Vinogradov's Type I/II estimates alone
(`TrackCStage5PrimeBlockMajorArcProof.lean`), which leaves major arcs with denominators up to
`(log n)^{20}`. At that size an estimate of Theorem A.1's shape is too weak (its error carries a
density term that cannot absorb a factor `q`), so the formal proof follows [MRT]'s own order:
Theorem A.2 applied to each character twist on a restricted set of integers, with the exceptional
integers removed once at the end (`Problems/tao2015_a1_r6r7_design_report.md`, "Finding D"). The
difference comes from what the formalization had available, not from a problem with the remark:
with bounded-denominator major arcs, the shortcut works as [T2] describes.

### 4. Measurability is never needed

[T1] Proposition 1.11 produces a random character and frequency `(χ, t)`, and its proof ends:
"It is easy to check that the quantities `χ, t` produced by Theorem 1.10 can be selected to be
measurable". The formal statement asserts only that, with high probability, each sample admits
some `(χ, t)`. That per-sample existential turned out to be all §4 needs, so no measurable
selection is ever constructed (`TrackCStage5VanDerCorput.lean`). The same file records a
quantifier order that matters: the constant in the probability bound `1 − O(ε)` must be fixed
before `ε`, or the statement would be vacuous for its consumers.

## A correction from the literature

The Ramaré identity in [MR] uses the weight `1/(ω(m; P, Q) + 1_{(p,m)=1})`. A footnote in the
arXiv version of [MR] explains that the published version wrote `1` in place of `1_{(p,m)=1}`,
"leading to a slight gap in the argument that affected only the proof of Lemma 12", and credits
Alisa Sedunova and Ke Wang for pointing it out. The formal proof uses the corrected weight
(`MoltResearch/Discrepancy/RamareIdentity.lean`).

## A correction to this repository's records

Until 27 September 2026 this repository cited the Halász inequality for primes as "[MR] Lemma 8",
including in the `formalization.yaml` of release `v1.0.1-edp`. In every arXiv version of [MR]
(v1–v4) it is Lemma 11; Lemma 8 there is a different estimate, a count of large values without
the zero-free-region saving. The current `formalization.yaml`, README, transcription file
(`Problems/sources/tao2015_statements.md`) and Lean docstrings use Lemma 11. The campaign reports
under `Problems/` keep the number they were written with.

## Encoding choices

- The stochastic multiplicative functions of [T1] Theorem 1.8 take values in `ℂ` and are
  unimodular almost surely, rather than taking values in the unit circle.
- Complete multiplicativity is imposed only for nonzero arguments. Imposed at `0` as well, the law
  would force every unimodular such function to be identically `1` and make every theorem about
  the class vacuous (`MoltResearch/Discrepancy/MultiplicativeC.lean`).
- The limit in the Fourier reduction is taken through an ultrafilter and Prokhorov's theorem.

## What the formalization does not give

- Tao's Theorem 1.1, for sequences in a Hilbert space, and the complex-valued version are not
  formalized.
- There is no rate: like the paper, the proof shows the discrepancy is unbounded without bounding
  how fast it grows. Some constants are existential, so no explicit bound can be read off.
- The inputs above are proved in the forms this argument needs; they are not general library
  theorems.

## References

- [T1] T. Tao, *The Erdős discrepancy problem*, Discrete Analysis 2016:1; arXiv:1509.05363v6.
- [T2] T. Tao, *The logarithmically averaged Chowla and Elliott conjectures for two-point
  correlations*, Forum of Mathematics, Pi 4 (2016), e8; arXiv:1509.05422v4.
- [MRT] K. Matomäki, M. Radziwiłł, T. Tao, *An averaged form of Chowla's conjecture*, Algebra &
  Number Theory 9 (2015), 2167–2196; arXiv:1503.05121v3.
- [MR] K. Matomäki, M. Radziwiłł, *Multiplicative functions in short intervals*, Annals of
  Mathematics 183 (2016), 1015–1056; arXiv:1501.04585v4.
- [IK] H. Iwaniec, E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53, 2004.
