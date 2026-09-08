# Erdős #1144: literature and proof-claim audit

Research snapshot: 2026-09-08.

## Executive summary

Let \((\varepsilon_p)_p\) be independent uniform signs.  This memo uses three
different models, which must not be conflated:

* the **complete Rademacher model**
  \[
  F(n)=\prod_{p^a\parallel n}\varepsilon_p^a\in\{-1,1\};
  \]
* the **squarefree Rademacher model**
  \[
  g(n)=\mu^2(n)\prod_{p\mid n}\varepsilon_p;
  \]
* the **Steinhaus model**, a completely multiplicative, complex-valued model
  whose prime values are independent and uniform on the unit circle.

The question on the card is whether, almost surely,
\[
  \limsup_{x\to\infty}\frac{S_F(x)}{\sqrt{x}}=+\infty,
  \qquad S_F(x):=\sum_{n\leq x}F(n).                 \tag{T}
\]
It asks for positive, not merely absolute, fluctuations.

**Known in the refereed/preprint literature.**  For the squarefree model,
Harper proved absolute fluctuations
\(\lvert S_g(x)\rvert\geq \sqrt{x}(\log\log x)^{1/4}/V(x)\) at arbitrarily
large \(x\), for every \(V(x)\to\infty\).  Very recent work now gives a
matching \(1/4\) logarithmic exponent in the almost-sure upper bound.  None of
those theorems is about \(F\).  For \(F\), Aymone proved infinitely many sign
changes of \(S_F\), Atherfold proved
\(S_F(x)\ll\sqrt{x}(\log x)^{1+o(1)}\), and Angelo--Xu proved infinitely many
sign changes of \(\sum_{n\leq x}F(n)/\sqrt n\).  These do not imply (T).

**Current proof claim.**  The live problem page has one claim, submitted on
2026-09-06, whose tagged Lean artifact states and kernel-checks exactly (T).
The audit below found no model, normalization, quantifier, or trust-boundary
mismatch.  The tagged source hashes and public CI check pass, and an independent
download and check of the preserved axiom report reproduced its result.  The
endpoint uses only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`; historical axioms elsewhere in that repository are not
dependencies.  This is strong formal evidence, but it is a two-day-old,
207,626-line formalization with no independent mathematical exposition or peer
review yet.  Accordingly this memo records it as a surviving proof claim, not
as established literature.

Labels below mean:

* **Known**: a theorem in a cited paper, or a direct deterministic consequence
  whose proof is displayed.
* **Conjectured**: explicitly conjectural.
* **Our audit/deduction**: checked for this memo but not attributed as a theorem
  of the cited paper.

Throughout, \(\log_k x\) denotes the \(k\)-fold iterated logarithm.

## 1. Classical squarefree Rademacher results

All results in this section concern \(g\), not the complete model \(F\).

### Wintner (1944)

**Known.**  Wintner introduced the squarefree model and proved, for each fixed
\(\epsilon>0\), almost surely
\[
  S_g(x)=O_\epsilon(x^{1/2+\epsilon}),
  \qquad
  S_g(x)\neq O(x^{1/2-\epsilon}).
\]
The second assertion is an almost-sure lower obstruction, not a lower bound of
order \(\sqrt x\).  Sources: A. Wintner, *Random factorizations and Riemann's
hypothesis*, Duke Math. J. 11 (1944), 267--275,
[DOI](https://doi.org/10.1215/S0012-7094-44-01122-1); the statement is also
reproduced in the corrected introduction of Lau--Tenenbaum--Wu below.

### Halász (1983)

**Known.**  For suitable constants \(c_4,c_5>0\), Halász proved almost surely
\[
  S_g(x)\ll \sqrt{x}\,
    \exp\!\left(c_4\sqrt{\log_2x\,\log_3x}\right),              \tag{1}
\]
while the estimate
\[
  S_g(x)\ll \sqrt{x}\,
    \exp\!\left(-c_5\sqrt{\log_2x\,\log_3x}\right)             \tag{2}
\]
is false almost surely.  The upper and lower arguments are substantially
different; their similar-looking exponents do not constitute a law of the
iterated logarithm.  Source: G. Halász, *On random multiplicative functions*,
Publ. Math. Orsay 83-4 (1983), 74--96, in the
[Colloque Hubert Delange proceedings](https://bibliotheque.imo.universite-paris-saclay.fr/media/filer_public/f9/21/f921609e-e577-4f85-9530-190733f3039e/colloque-hubert-delange_1982.pdf).

### Lau--Tenenbaum--Wu (2013, corrected 2021 text)

**Known.**  Their Theorem 1.1 gives, for every \(\epsilon>0\), almost surely
\[
  S_g(x)\ll_{g,\epsilon}\sqrt{x}(\log_2x)^{2+\epsilon}.          \tag{3}
\]
Their Lemma 2.3 also gives the short-increment interpolation needed to pass
from a sparse sequence of test points to all \(x\).

The exponent must be cited from the authors' corrected version: its title page
says that it includes corrections to the published version.  The published
abstract is still often indexed with exponent \(3/2+\epsilon\), whereas the
corrected Theorem 1.1 and abstract say \(2+\epsilon\).  Sources:
[corrected author PDF](https://tenenb.perso.math.cnrs.fr/PPP/RMF.pdf), and the
[published DOI](https://doi.org/10.1090/S0002-9939-2012-11332-2).

### Harper's earlier omega bound (2013)

**Known.**  Harper's Corollary 3 says that for every \(A>5/2\), almost surely
\[
  S_g(x)\neq O\!\left(\frac{\sqrt{x}}{(\log_2x)^A}\right).       \tag{4}
\]
This strengthened the lower side of Halász's work, but still did not rule out
\(S_g(x)=O(\sqrt x)\).  Source: A. J. Harper, *Bounds on the suprema of
Gaussian processes, and omega results for the sum of a random multiplicative
function*, Ann. Appl. Probab. 23 (2013), 584--616,
[arXiv:1012.0210](https://arxiv.org/abs/1012.0210),
[DOI](https://doi.org/10.1214/12-AAP847).

### Harper's low moments and “typical size” (2020)

**Known.**  Uniformly for \(0\leq q\leq1\), Harper determined the low moments
in both the squarefree Rademacher and Steinhaus models:
\[
  \mathbb E\lvert S_g(x)\rvert^{2q}
  \asymp
  \left(\frac{x}{1+(1-q)\sqrt{\log_2x}}\right)^q.               \tag{5}
\]
In particular,
\[
  \mathbb E\lvert S_g(x)\rvert
  \asymp \frac{\sqrt{x}}{(\log_2x)^{1/4}},                     \tag{6}
\]
while \(\mathbb E\lvert S_g(x)\rvert^2\sim(6/\pi^2)x\).  Thus
\(S_g(x)/\sqrt{\mathbb E|S_g(x)|^2}\to0\) in probability.  The phrase
“typical size \(\sqrt{x}/(\log\log x)^{1/4}\)” usually refers to (6) and the
critical-multiplicative-chaos picture.  It should not be upgraded silently to
a median asymptotic or an almost-sure pointwise order theorem; the distribution
has important rare tails.

Source: A. J. Harper, *Moments of random multiplicative functions, I: Low
moments, better than squareroot cancellation, and critical multiplicative
chaos*, Forum Math. Pi 8 (2020), e1,
[arXiv:1703.06654](https://arxiv.org/abs/1703.06654),
[DOI](https://doi.org/10.1017/fmp.2019.7).

### Harper's large fluctuations (2023)

**Known.**  If \(g\) is squarefree Rademacher, or if \(f\) is Steinhaus, then
for every deterministic \(V(x)\to\infty\), almost surely there are arbitrarily
large \(x\) such that
\[
  \left|\sum_{n\leq x}g(n)\right|
  \geq \frac{\sqrt{x}(\log_2x)^{1/4}}{V(x)}.                   \tag{7}
\]
This is an **absolute-value** theorem.  Its proof conditions on all but the
largest prime variables, obtains a multivariate Gaussian approximation over
many endpoints, and proves that most conditional covariances are small using
Euler-product/multiplicative-chaos estimates.  It neither supplies a positive
crossing for \(F\) nor compares the squarefree and complete covariance laws.

Source: A. J. Harper, *Almost sure large fluctuations of random
multiplicative functions*, IMRN 2023(3), 2095--2138,
[arXiv:2012.15809](https://arxiv.org/abs/2012.15809),
[DOI](https://doi.org/10.1093/imrn/rnab299).

### Almost-sure upper bounds after Harper

These results again cover the squarefree Rademacher and Steinhaus models only.

* **Known (Caich, 2023 preprint).**  For every \(\epsilon>0\), almost surely
  \[
    |S_g(x)|\ll_{g,\epsilon}\sqrt{x}(\log_2x)^{3/4+\epsilon}.
  \]
  Source: [arXiv:2304.00943](https://arxiv.org/abs/2304.00943).
* **Known (Durkan--Pearce-Crump, 2026 preprint).**  The exponent was lowered
  to \(1/4+\epsilon\):
  \[
    |S_g(x)|\ll_{g,\epsilon}\sqrt{x}(\log_2x)^{1/4+\epsilon}.
  \]
  Together with (7), this fixes the logarithmic exponent.  Source:
  [arXiv:2607.29429](https://arxiv.org/abs/2607.29429), Theorem 1.
* **Known (Verreault, 2026 preprint).**  A stronger secondary-factor family
  implies, for every \(\epsilon>0\),
  \[
    |S_g(x)|\ll_{g,\epsilon}
      \sqrt{x}(\log_2x)^{1/4}(\log_3x)^{1+\epsilon}.             \tag{8}
  \]
  More exactly, Theorem 1.1 permits
  \(\sqrt{x}(\log_2x)^{1/4}G(\log_3x)\) whenever \(G\) is eventually
  nondecreasing and \(\sum_{\ell\ge3}\ell\log\ell/G(\ell)^2<\infty\).
  Source: [arXiv:2608.21354](https://arxiv.org/abs/2608.21354).

The last two preprints appeared only in July and August 2026.  They update the
historical upper-bound picture, but do not address the card's complete model.

## 2. Exact squarefree/complete identities and their limits

Couple \(F\) and \(g\) using the same prime signs.  Every \(n\ge1\) is uniquely
\(n=ab^2\) with \(a\) squarefree, and then \(F(n)=g(a)\).  Equivalently,
\(F=g*1_{\square}\).  Therefore
\[
\begin{aligned}
S_F(x)
 &=\sum_{a\le x}g(a)\left\lfloor\sqrt{x/a}\right\rfloor\\
 &=\sqrt{x}\,M_g(x)-R_g(x),                                   \tag{9}\\
M_g(x)&:=\sum_{a\le x}\frac{g(a)}{\sqrt a},\\
R_g(x)&:=\sum_{a\le x}g(a)\{\sqrt{x/a}\},
\end{aligned}
\]
and
\[
  \sum_{n\le x}\frac{F(n)}{\sqrt n}
  =\sum_{b\le\sqrt{x}}\frac1b\,M_g(x/b^2).                  \tag{10}
\]
These are Atherfold's equations (1.7) and (1.8).

**Our audit/deduction.**  Orthogonality of \(g(a)\) gives, at each fixed \(x\),
\[
  \mathbb E\left|\frac{R_g(x)}{\sqrt x}\right|^2
  =\frac1x\sum_{\substack{a\le x\\a\ \mathrm{squarefree}}}
    \{\sqrt{x/a}\}^2\le1.                                   \tag{11}
\]
This is only fixed-endpoint \(L^2\) control.  Harper's large endpoint is
random and depends on the same signs as \(R_g\); (11) supplies neither uniform
pathwise control along those endpoints nor the required one-sided crossing.
This is the precise gap in the tempting transfer from (7) through (9).
Atherfold likewise notes that the fractional-part sum destroys the
multiplicative structure used by existing proofs.

There is a second diagnostic showing how different \(F\) is.  Since
\(\mathbb E[F(m)F(n)]=1\) exactly when \(mn\) is a square,
\[
  \mathbb E S_F(x)^2
  =\sum_{\substack{a\le x\\a\ \mathrm{squarefree}}}
       \left\lfloor\sqrt{x/a}\right\rfloor^2
  =\frac6{\pi^2}x\log x+O(x),                                 \tag{12}
\]
and \(\mathbb E S_F(x)=\lfloor\sqrt x\rfloor\).  Thus its normalized
second moment grows like \(\log x\), unlike either model in Section 1.  A
second moment of this size does not by itself imply almost-sure, positive,
unbounded limsup: the mass could occur on rare or highly correlated events.

The Steinhaus model is complete but complex.  It has
\(\mathbb E[f(m)\overline{f(n)}]=1_{m=n}\), variance \(\asymp x\), rotational
symmetry, and no order relation with which to state a positive limsup.  Its
absolute-value theorems therefore do not transfer to (T) merely because both
models are completely multiplicative.

## 3. Results for the complete model

### Aymone (2024)

**Known.**  Aymone's Theorem 1.2 says that for the complete Rademacher model,
for every \(0\le\alpha<1/2\),
\[
  \sum_{n\le x}\frac{F(n)}{n^\alpha}
\]
changes sign infinitely often almost surely.  In particular \(S_F(x)\) has
infinitely many sign changes.  The theorem gives no quantitative size at the
crossings and does not imply (T).  The same paper proved the endpoint
\(\alpha=1/2\) only for the squarefree model and left the complete endpoint
open.  Source: M. Aymone, *Sign changes of the partial sums of a random
multiplicative function II*, C. R. Math. 362 (2024), 895--901,
[arXiv:2303.14682](https://arxiv.org/abs/2303.14682),
[DOI](https://doi.org/10.5802/crmath.615).

### Atherfold (At25, revised 2026): exact statements

Atherfold reserves \(f\) for the squarefree model and \(f^*\) for the complete
model.  In the current arXiv v4 (2026-02-03), the proved statements are:

* **Known, Theorem 1 (squarefree weighted).**  For every \(\epsilon>0\),
  almost surely
  \[
    M_g(x)=\sum_{n\le x}\frac{g(n)}{\sqrt n}
      \ll_{g,\epsilon}(\log_2x)^{3/4+\epsilon}.                 \tag{13}
  \]
* **Known, Theorem 2 (squarefree, one large prime).**  Almost surely
  \[
    \sum_{\substack{n\le x\\P(n)>\sqrt x}}
       \frac{g(n)}{\sqrt n}
      \ll_{g,\epsilon}(\log_2x)^{1/4+\epsilon}.                 \tag{14}
  \]
* **Known, Theorem 3 (squarefree weighted lower bound).**  There are
  arbitrarily large \(x\) such that
  \[
    |M_g(x)|\gg_g(\log_2x)^{-1/2}.                             \tag{15}
  \]
* **Known, Corollary 1 (complete weighted).**  From (10) and (13), almost
  surely
  \[
    \sum_{n\le x}\frac{F(n)}{\sqrt n}
      \ll_{F,\epsilon}\log x\,(\log_2x)^{3/4+\epsilon}.         \tag{16}
  \]
  Partial summation gives the card's unweighted consequence
  \[
    S_F(x)\ll_{F,\epsilon}\sqrt x\,(\log x)^{1+\epsilon},       \tag{17}
  \]
  equivalently \(\sqrt x(\log x)^{1+o(1)}\) after intersecting
  countably many probability-one events.

**Conjectured by Atherfold.**  The exponent \(1/4\) should govern the full
weighted squarefree upper and large-fluctuation scales.  Atherfold explicitly
identifies the fractional-part remainder in (9) as the obstacle to improving
(17) for \(F\).

Source: C. Atherfold, *Almost sure bounds for weighted sums of Rademacher
random multiplicative functions*, [arXiv:2501.11076v4](https://arxiv.org/abs/2501.11076).
Earlier arXiv versions had different numerical exponents; the statements above
are from v4 and should be used in place of cached summaries of older versions.

### A stronger weighted-squarefree lower consequence

**Our checked deduction (also posted in the proof-claim discussion).**  Let
\(U_g(x)=S_g(x)\).  Partial summation gives
\[
  U_g(x)=\sqrt x\,M_g(x)-\frac12\int_1^x\frac{M_g(t)}{\sqrt t}\,dt,
\]
so
\[
  \frac{|U_g(x)|}{\sqrt x}
  \le2\sup_{1\le t\le x}|M_g(t)|.                              \tag{18}
\]
In Harper's theorem choose
\(V(x)=(\log_2x)^{1/4-k}\).  For every fixed \(0<k<1/4\), (7) and (18) imply
almost surely that at arbitrarily large \(t\),
\[
  |M_g(t)|\ge\tfrac12(\log_2t)^k.                              \tag{19}
\]
The maximizing points tend to infinity because the right side before choosing
the maximum tends to infinity.  Thus (19) is much stronger than (15).  It is
still absolute, squarefree, and does not control the correlated remainder in
(9), so it still stops short of (T).

### Angelo--Xu (2026): exact weighted endpoint


**Known, Theorem 1.2.**  For the complete model \(F\), almost surely
\[
  W_F(x):=\sum_{n\le x}\frac{F(n)}{\sqrt n}
\]
changes sign infinitely many times.  This resolves the \(\alpha=1/2\) endpoint
left open by Aymone.

**Known, Theorem 1.1 (initial bias).**  Let \(x\to\infty\) and condition on
\(F(p)=1\) for every prime \(p\le y\).  If
\[
  y=o\!\left((\log x/\log\log x)^2\right),
\]
then the conditional probability that \(\sum_{n\le N}F(n)\ge0\) for every
\(N\le x\) is \(o(1)\).  This complements Kucheriaviy's result on the
\((\log x)^{2+o(1)}\) bias threshold.

Their weighted proof turns eventual nonnegativity into an approximate
monotonicity constraint on Dirichlet series just to the right of \(1/2\), then
contradicts that constraint using asymptotically independent Gaussian
increments of a prime sum.  Sign changes alone give no divergent amplitude,
and the Dirichlet-series smoothing loses the endpoint information needed for
\(S_F(x)/\sqrt x\).  Thus neither theorem implies (T).

Source: R. Angelo and M. W. Xu, *Oscillations of random multiplicative
functions under initial bias*,
[arXiv:2411.14447v3](https://arxiv.org/abs/2411.14447) (2026-08-02 version).
For context, their earlier harmonic-weight paper proves that
\(\sum_{n\le x}F(n)/n\) remains positive for every \(x\) with probability at
least \(1-10^{-45}\), while that probability is strictly less than one:
[arXiv:2205.05822](https://arxiv.org/abs/2205.05822).

## 4. Audit of the live proof claim

### What is claimed

The [problem page](https://www.erdosproblems.com/1144) still labels #1144
“OPEN”, but its [proof-claims tab](https://www.erdosproblems.com/forum/thread/1144/proof-claims)
lists one full proof, submitted by Sigurd William Rachlew Høystad on
2026-09-06.  The claim links a
[v1.0.0 proof guide](https://github.com/saasom/Erdos1144/blob/v1.0.0/notes/1144/complete_proof.md)
and a [tagged formalization](https://github.com/saasom/Erdos1144/tree/v1.0.0).
It claims an unconditional Lean theorem for positive unboundedness in the
complete model, not merely a reduction to an analytic assumption.

### Reproducible checks performed

The audit used tag `v1.0.0`, commit
`a0050daf4bf4992355b5ab189ee9c75cd44795a3`.

1. `sha256sum --check verification/source-snapshot.sha256` accepted all 605
   listed local Lean modules.
2. The public GitHub Actions run for that exact commit
   [completed successfully](https://github.com/saasom/Erdos1144/actions/runs/34025001677):
   its separately reported build and endpoint-audit steps both passed with the
   pinned Lean `v4.30.0-rc2` and Mathlib commit
   `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
3. The preserved `axiom-audit` artifact was downloaded independently and
   passed the tagged `scripts/check_axioms.py`; it reported exactly
   `[propext, Classical.choice, Quot.sound]` for both the instantiated final
   certificate and `Erdos.Problem1144.erdos1144`.

There was one reproducibility wrinkle: on this aarch64 host, the pinned Lean
toolchain's bundled `leantar` was an x86-64 binary, so `lake exe cache get`
downloaded but could not decompress the cache.  The audit used the compatible
aarch64 `leantar 0.1.19` from another installed Lean toolchain to unpack the
same pinned cache artifacts.  A full local rebuild was not completed and is not
counted as evidence above.  This is a release-packaging/host issue rather than a
failure reported by Lean, but exact one-command reproduction currently assumes
a working architecture-matched `leantar`.

### Statement and model audit

The endpoint definitions survive a direct read:

* `Omega := ℕ → Bool`; `mu` is the infinite product of fair Boolean coin
  measures.  Non-prime coordinates are unused noise.
* `eps ω p` is \(\pm1\).  `sfKernel n` selects the primes whose valuation in
  \(n\) is odd, and `f ω n` is their sign product.  Separate proved lemmas show
  `f(1)=1`, `f(p)=eps ω p`, and complete multiplicativity on positive inputs.
* `S ω N` sums over `Finset.Icc 1 N`, so it is the inclusive sum in (T).
* `normSum ω N = S ω (N+1) / sqrt(N+1)`.  The harmless shift avoids zero.
* `Erdos1144` is
  ```lean
  ∀ᵐ omega ∂mu, ∀ A : ℝ, ∃ᶠ N : ℕ in atTop, A ≤ normSum omega N
  ```
  which is positive crossings above every real threshold arbitrarily late,
  all on one probability-one event.  It is equivalent to (T).
* `Final.lean` proves `theorem erdos1144 : Erdos1144` by applying the proved
  `candidate_scheduledGaussianRobustCrossing_certificate` route.

**Our audit conclusion.**  No squarefree/complete substitution, absolute-value
weakening, missing “almost surely”, sign reversal, or quantifier-order defect
was found.  In particular, the theorem is stronger than the previously
published sign-change statements and matches the problem page's positive
limsup.

### Trust boundary and what was not established

The release repository deliberately retains historical alternative routes
declared with `axiom` in `Final.lean`, as well as vendored placeholder tooling.
Consequently, “there are no axioms anywhere in the repository” would be false.
Lean's transitive endpoint audit is the relevant check: none of those
declarations occurs in the proof term of `erdos1144` or its final certificate.

The formal result is compelling conditional on the ordinary Lean kernel,
Mathlib definitions, and the audited statement.  This memo did not manually
re-derive every analytic estimate in 605 local modules, nor find an independent
paper proof.  The release is extremely new and its informal candidate predates
the authoritative formal route.  Sensible next checks are an independent
expert review of the stationary covariance comparison and tail-rate modules,
and reproduction on a second architecture.  Until that social/mathematical
review happens, the conservative status is “exact formal proof claim survived
the present audit,” not “the literature has settled #1144.”

## 5. What is known about lower fluctuations and where each argument stops

This section is intentionally explicit about conclusion strength.

| Model and sum | Best relevant lower information | Why it stops before (T) |
|---|---|---|
| Squarefree \(S_g(x)\), Wintner | Not \(O(x^{1/2-\epsilon})\) a.s. | Below the \(\sqrt x\) scale; wrong model; no direction. |
| Squarefree \(S_g(x)\), Halász | Not \(O(\sqrt x e^{-c\sqrt{\log_2x\log_3x}})\) a.s. | Still below \(\sqrt x\); wrong model; no direction. |
| Squarefree \(S_g(x)\), Harper 2013 | Not \(O(\sqrt x/(\log_2x)^A)\), \(A>5/2\), a.s. | Still below \(\sqrt x\); wrong model; no direction. |
| Squarefree \(S_g(x)\), Harper 2023 | \(|S_g(x)|\ge\sqrt x(\log_2x)^{1/4}/V(x)\) arbitrarily often a.s. | Absolute value and wrong covariance/model; the remainder in (9) is correlated and only fixed-point \(L^2\)-bounded after normalization. |
| Squarefree weighted \(M_g(x)\), Atherfold | \(|M_g(x)|\gg(\log_2x)^{-1/2}\) arbitrarily often a.s. | Bound tends to zero, is absolute, and (9)'s remainder is uncontrolled. |
| Squarefree weighted \(M_g(x)\), deduction (19) | \(|M_g(x)|\gg(\log_2x)^k\) arbitrarily often for every \(0<k<1/4\) a.s. | Diverges, but remains absolute and can be cancelled by the correlated remainder in (9). |
| Complete \(S_F(x)\), Aymone | Infinitely many sign changes a.s. | Gives neither \(|S_F(x)|/\sqrt x\to\infty\) along a subsequence nor positive amplitudes. |
| Complete weighted \(W_F(x)\), Angelo--Xu | Infinitely many sign changes a.s. | Critical Abel smoothing records sign oscillation, not an unbounded normalized endpoint value of \(S_F\). |
| Complete \(S_F(x)\), second moment (12) | \(\mathbb E S_F(x)^2\asymp x\log x\) | An expectation at each fixed point cannot rule out rare-event mass or supply almost-sure repeated positive crossings. |
| Complete \(S_F(x)\), live Lean claim | Exactly (T), kernel-checked with standard axioms | It does not stop logically; the remaining issue is independent review and acceptance of a new proof claim, not a visible gap in the formal endpoint. |

The central analytic bottleneck before the new formal claim is therefore not a
lack of large squarefree fluctuations.  It is a **simultaneous, one-sided,
pathwise transfer** through (9): control the fractional-part process at the
same many endpoints at which the weighted squarefree process crosses, with
enough covariance information to prevent cancellation.  The claimed Lean
proof says it closes precisely that gap by comparing selected squarefree and
complete stationary Gaussian fields and proving the two omitted Gaussian tails
vanish uniformly.  That comparison is the highest-value target for independent
mathematical scrutiny.
