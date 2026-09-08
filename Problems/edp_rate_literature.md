# Quantitative Erdős discrepancy: literature memo

Research snapshot: 2026-09-08.  Throughout, for a sign sequence
\(f:\mathbb N\to\{-1,1\}\), write

\[
  D_f(X):=\max_{md\le X}\left|\sum_{k\le m}f(kd)\right|.
\]

The distinction between the product-bounded region \(md\le X\) and a rectangular
region \(m\le N, d\le R(N)\) matters below.

## Executive readout

### Known

* Erdős repeatedly proposed the product-scale lower bound
  \(D_f(X)\gg\log X\), first explicitly in the requested sources in 1964.  He
  also observed that this order would be best possible.  The 1985 paper instead
  emphasizes the qualitative conjecture and a stronger-looking partial-sum
  question for multiplicative signs. [Er64b, p. 54][Er64b]
  [Er65b, pp. 221--222][Er65b] [Er81, pp. 28--29][Er81]
  [Er85c, p. 78][Er85c]
* Tao proved unbounded discrepancy, including the Hilbert-sphere-valued version,
  but his Section 2 passes to a limiting probability law by subsequential compactness
  and therefore supplies no finite cutoff as a function of the desired discrepancy.
  [Tao16, Theorem 1.1 and Section 2][Tao16]
* McNamara made Tao's architecture quantitative.  In its exact rectangle, his
  result is \((\log\log N)^{1/484-o(1)}\), with
  \(n\le N\) and
  \(d\le\exp(N/(\log\log N)^{1/242})\), not merely an unspecified
  \(d\le e^N\). [Mc21, Theorem 4.1.1, pp. 118--124][Mc21]
* Modified characters give logarithmic upper examples.  The usual ternary
  Borwein--Choi--Coons example has leading constant \(1/\log 3\).  Changing its
  value at 3 from \(+1\) to \(-1\) gives the sharper exact asymptotic constant
  \(1/(2\log 3)=0.4551196133\ldots\); the latter constant is derived explicitly
  in Section 2 below. [BCC08, Theorem 9 and Application 1][BCC08]
  [Tao16, Example 1.4][Tao16]
* SAT computation proves that the longest **unrestricted** discrepancy-2 sign
  sequence has length 1160.  The number 127,645 is instead the exact maximum
  length at discrepancy 3 in each of the **multiplicative** and **completely
  multiplicative** classes; the same paper constructs an unrestricted
  discrepancy-3 sequence of length 130,000. [KL14, Theorems 10--11 and Table 1][KL14]

### Conjectured

The rate problem on this card is the uniform assertion that some absolute
\(c>0\) satisfies \(D_f(X)\ge c\log X\) for every sign sequence (with the
usual harmless choices between \(<\), \(\le\), and sufficiently large \(X\)).
This remains open; Tao also identifies logarithmic growth as the plausible best
order. [Erdős Problems #67, status and quantitative variant][EP67]
[Er64b, p. 54][Er64b] [Tao16, pp. 5--6][Tao16]

### Our deductions and literature verdict

1. The digit formula gives the exact modified-ternary constant
   \(1/(2\log 3)\), not only Tao's description “by a factor of about two.”
   Consequently, any universal asymptotic constant in Erdős's conjecture is at
   most \(1/(2\log 3)\).  This is our elementary deduction from the cited digit
   formula, not a claim quoted from Borwein--Choi--Coons. [BCC08, pp. 12--14][BCC08]
   [Tao16, Example 1.4][Tao16]
2. Reparameterizing McNamara's rectangle gives the product-bounded consequence
   \(D_f(X)\gg(\log\log\log X)^{1/484-o(1)}\).  This deduction is detailed in
   Section 3 and is weaker than the conjectured \(\log X\), but it is an explicit
   diverging rate in Erdős's original product variable. [Mc21, Theorem 4.1.1][Mc21]
3. Later Elliott/Chowla results improve correlation estimates or the density of
   good scales, but none of the papers reviewed below states a uniform
   product-scale EDP rate for arbitrary sign sequences.  The 2025 Tao--Teräväinen
   estimate is potentially useful input to a new finite-scale assembly, not a
   drop-in replacement for that assembly. [TT25, Theorem 3.1][TT25]

## 1. What Erdős actually asked

| Source | Formulation and scope |
|---|---|
| [Er64b, p. 54][Er64b] | For arbitrary \(f(n)\in\{\pm1\}\), first asks whether every fixed threshold is exceeded by some homogeneous progression, then proposes \(\max_{dm<n}|\sum_{k\le m}f(kd)|>c_2\log n\).  The short source wording is: “It is perhaps even true that” followed by the logarithmic display. |
| [Er65b, pp. 221--222][Er65b] | Restates unboundedness and then says “more precisely, perhaps” there is an absolute \(c_1\) such that every \(h\) and every \(x\) admit \(md<x\) with magnitude greater than \(c_1\log x\).  Erdős immediately writes: “It is easy to see that (54) if true is best possible.”  The following page observes that for completely multiplicative \(h\), the homogeneous sums reduce to ordinary partial sums. |
| [Er81, pp. 28--29][Er81] | Calls the qualitative assertion one of his oldest conjectures, going back to the early 1930s, and separately asks whether the maximum over every pair \(m,d\) with \(md<x\) exceeds \(c\log x\).  Again: “It is easy to see that (4) if true is best possible.” |
| [Er85c, p. 78][Er85c] | Restates qualitative EDP as (8), offers $500, then asks for a multiplicative \(f\) whether \(\lim_{n\to\infty}|\sum_{k\le n}f(k)|=\infty\), not just whether the limsup is infinite.  Here “multiplicative” means \(f(ab)=f(a)f(b)\) for \((a,b)=1\).  Erdős attributes this partial-sum question also to Tchudakoff and proposes the strengthening that \(\{n:|\sum_{k\le n}f(k)|<c\}\) have density zero for every \(c\). |

Thus Er64b, Er65b, and Er81 really do state the logarithmic **product-scale**
conjecture.  Er85c is a source for the qualitative and multiplicative variants,
not for a new quantitative constant. [Er64b, p. 54][Er64b]
[Er65b, pp. 221--222][Er65b] [Er81, pp. 28--29][Er81]
[Er85c, p. 78][Er85c]

## 2. Logarithmic upper examples and the exact constant

Let \(\chi_3\) be the nonprincipal real character modulo 3.  Define the completely
multiplicative sign \(f_+\) on primes by

\[
 f_+(3)=1,\qquad f_+(p)=\chi_3(p)\quad(p\ne3).
\]

Borwein--Choi--Coons prove the more general base-\(p\) digit identity for a
modified nonprincipal character.  At \(p=3\), it says

\[
 S_+(n):=\sum_{j\le n}f_+(j)
   = \#\{\text{digits equal to 1 in the ternary expansion of }n\}.
\]

Hence \(0\le S_+(n)\le\lfloor\log_3 n\rfloor+1\), and numbers
\(1+3+\cdots+3^r\) attain one contribution from every digit position.
[BCC08, Theorem 9, Application 1, and Corollary 4][BCC08]

For any completely multiplicative sign \(f\),

\[
 \sum_{k\le m}f(kd)=f(d)\sum_{k\le m}f(k),
 \qquad
 D_f(X)=\max_{m\le X}\left|\sum_{k\le m}f(k)\right|,
\]

because \(|f(d)|=1\) gives the upper bound and \(d=1\) gives equality.  Therefore

\[
 D_{f_+}(X)=\frac{\log X}{\log3}+O(1).
\]

This last equality is our direct consequence of complete multiplicativity and the
cited digit identity. [BCC08, pp. 12--13][BCC08]

There is a better variant.  Put \(f_-(3)=-1\) and retain
\(f_-(p)=\chi_3(p)\) for \(p\ne3\).  Tao notes that this change improves the
discrepancy by about a factor of two. [Tao16, Example 1.4, p. 3][Tao16]
For completeness, the exact computation is as follows (our derivation).  If
\(n=3q+r\), \(0\le r<3\), cancellation of \(\chi_3\) on each complete ternary
block gives

\[
 S_-(3q+r)=-S_-(q)+\mathbf 1_{r=1}.
\]

Writing \(n=\sum_j a_j3^j\) and iterating yields

\[
 S_-(n)=\sum_{j\ge0}(-1)^j\mathbf 1_{a_j=1}.
\]

If the highest occupied position is \(L\), at most \(\lceil(L+1)/2\rceil\) positions of one
parity can contribute with the same sign.  Taking all even (or all odd) positions
equal to 1 shows this bound is attained up to an additive constant as the cutoff
varies.  Complete multiplicativity then gives the exact leading term

\[
 \boxed{D_{f_-}(X)=\frac{1}{2\log3}\log X+O(1)}.
\]

The general Borwein--Choi--Coons identity similarly expresses a modified
character's summatory function as a sum, over base-\(p\) digits, of the short
character sums \(\sum_{m\le a}\chi(m)\).  It supplies many \(O(\log X)\)
examples, but it does not make any arbitrary sign sequence resemble a modified
character. [BCC08, Theorem 9][BCC08]

## 3. McNamara's quantitative theorem

### Exact statement and range

For a sequence \(f\) in the unit sphere of a Hilbert space, McNamara's displayed
Theorem 4.1.1 states, for large \(N\),

\[
 \sup_{\substack{n\le N\\
 d\le \exp(N(\log\log N)^{-1/242})}}
 \left\|\sum_{i\le n}f(id)\right\|
 \gtrsim
 \frac{(\log\log N)^{1/484}}
 {(\log\log\log\log N)^{1/4}
  (\log\log\log\log\log N)^{1/2}}.
\]

In particular it is \((\log\log N)^{1/484-o(1)}\).  The frequently quoted
rectangle \(n\le N,d\le e^N\) is a valid weakening, but it hides the sharper
range in the thesis. [Mc21, Theorem 4.1.1, p. 118][Mc21]

There is an apparent minor iterated-log bookkeeping mismatch in the thesis: the
displayed theorem has the denominator above, while an intermediate \(A^2\) bound
on p. 123 displays a squared fivefold logarithm.  The thesis abstract and the
standard citation retain only \((\log\log N)^{1/484-o(1)}\), which is unaffected.
We likewise use only that robust form in deductions. [Mc21, pp. iii, 118, 123][Mc21]

### Method

The proof is a quantitative traversal of Tao's three stages.  First, a finite
multiplicative Fourier/Plancherel reduction converts uniformly small homogeneous
sums of \(f\) into small second moments for a random completely multiplicative
unit-circle-valued function \(g\).  Second, a nonpretentious branch combines a
two-point logarithmic correlation estimate with a second-moment inequality.
Third, if that correlation estimate is unavailable, pretentious-distance
estimates identify a character twist and a modified-character/Euler-product
argument forces a large second moment. [Mc21, Lemmas 4.2.1 and 4.3.1,
Corollaries 4.3.5 and 4.4.3, and Lemma 4.4.4, pp. 121--124][Mc21]

### Where \(1/484\) comes from

The exponent is visible in the final parameter balance, rather than being an
opaque constant from one black-box theorem.  Corollary 4.3.5 gives a correlation
error \(e^{-B/60}\).  McNamara chooses

\[
 B=\frac{60}{242}\log\log\log N
   +\log\log\log\log\log\log N.
\]

Thus the nonpretentious branch has a \((\log\log N)^{-1/242}\) saving and forces
an \(A^2\)-lower bound with leading power \((\log\log N)^{1/242}\).  In the
pretentious branch, Lemma 4.4.4 has a main factor of the shape
\(k e^{-2B}\), with

\[
 k\asymp\left(\frac{\log\log N}
 {2\log\log\log\log N}\right)^{1/2}.
\]

The leading power is again
\(1/2-2(60/242)=1/242\).  Finally the entire argument bounded **squared** sums by
\(A^2\), so taking a square root changes \(1/242\) to \(1/484\).  The smaller
iterated logarithms pay for the modulus, \(k\), error absorption, and the
\(1/\log\log q\) factor. [Mc21, Corollary 4.3.5 and Lemma 4.4.4,
pp. 122--124][Mc21]

### Product-scale consequence (our reparameterization)

Let \(X\) be large and take

\[
 N=\left\lfloor\tfrac13\log X\,
       (\log\log\log X)^{1/242}\right\rfloor.
\]

Then \(\log\log N=(1+o(1))\log\log\log X\) and
\(N/(\log\log N)^{1/242}=(1/3+o(1))\log X\).  Hence every pair in
McNamara's rectangle has \(d\le X^{1/2}\) and \(n\le X^{1/2}\) for all
sufficiently large \(X\), so \(nd\le X\).  Substitution gives

\[
 \boxed{D_f(X)\gtrsim
   (\log\log\log X)^{1/484-o(1)}}.
\]

This is our deduction from Theorem 4.1.1; it is not presented as a separately
named theorem in the sources reviewed here. [Mc21, Theorem 4.1.1][Mc21]

## 4. Why Tao's limiting law is non-effective

Tao's Section 2 argues contrapositively from a hypothetical discrepancy bound
\(C\).  For each finite cutoff \(X\), Fourier analysis constructs a stochastic
completely multiplicative \(g_X\) whose partial-sum second moments are bounded
uniformly for \(n\le X\).  Its law \(\nu_X\) lives on the compact metrizable
space \(\mathcal M\cong(S^1)^{\mathcal P}\) of completely multiplicative
functions. [Tao16, equations (2.2)--(2.3), pp. 8--10][Tao16]

Prokhorov compactness then extracts an unspecified subsequence
\(\nu_{X_j}\to\nu\).  Since each fixed finite partial-sum functional is
continuous, the limiting law \(\nu\) inherits all fixed-\(n\) moment bounds.
Nothing in subsequential compactness supplies a modulus telling us how large
\(X_j\) must be to approximate the first \(n\) coordinates, so a contradiction
at discrepancy level \(C\) cannot be inverted into an explicit cutoff
\(X(C)\). [Tao16, Section 2, pp. 9--10][Tao16]

Tao flags exactly this point in footnote 4: a quantitative proof “would avoid
this compactness argument,” truncate the later stages too, and control errors
from truncated Euler products.  Separately, Remark 1.12 says the Elliott input
is in principle effective but that the resulting bounds were not tracked and
would likely be poor.  Thus the loss of a rate is not solely the Elliott theorem;
it is the untracked finite-scale assembly beginning with the limiting law.
[Tao16, footnote 4 on p. 9 and Remark 1.12 on pp. 5--6][Tao16]

## 5. Do later quantitative Elliott results apply?

| Result | What it supplies | Verdict for this card |
|---|---|---|
| [Tao16E, Theorem 1.3 and Remark 1.4][Tao16E] | A nonasymptotic logarithmically averaged two-point Elliott theorem: for \(A\) sufficiently large in terms of \(\varepsilon\) and the two linear forms, a quantitative pretentious-distance hypothesis gives correlation at most \(\varepsilon\log\omega\).  Tao says the dependence is effective in principle but not written out, and estimates it as roughly triple exponential in the model case. | This is the input Tao's EDP paper says could be tracked.  McNamara performs a quantitative end-to-end version; merely citing “effective in principle” does not provide the missing constants. |
| [Ter18, Theorem 1.4][Ter18] | A finite-\(x\) binary correlation formula for real multiplicative functions, but with \(x\ge x_0(\varepsilon,h,\omega)\) and an \(o_{\varepsilon\to0}(1)\) error; its entropy-decrement lemma is presented without generalized limits. | Nonasymptotic syntax alone is not an explicit modulus.  The unspecified \(x_0\) and little-oh term do not yield a computable EDP rate without redoing the dependency bookkeeping. |
| [TT19, Corollaries 1.8 and 1.13][TT19] | Unweighted Elliott correlations vanish outside exceptional sets of logarithmic Banach density zero (and along a set whose complement has logarithmic density zero). | Stronger averaging mode at almost all scales, but qualitative exceptional-set limits do not state a uniform finite threshold for the EDP reduction. |
| [KMT23, Theorems 1.2 and 2.5][KMT23] | Two-point Elliott at a set of full upper logarithmic density, plus a density EDP theorem: for every fixed \(M\), a completely multiplicative sign has partial sum at least \(M\) on a set of positive upper logarithmic density (positive lower natural density in the pretentious case). | This strengthens “unbounded” inside the completely multiplicative class, but gives no explicit relation between \(M\) and the first such \(x\), and does not perform the finite Fourier reduction from an arbitrary sign sequence. |
| [Pil23, Theorem 1.1 and Remark 2.8][Pil23] | A fixed small power-of-\(\log x\) saving for the logarithmically averaged two-point Chowla correlation of the Liouville function, and a power saving outside a quantitatively small exceptional set of scales. | Genuinely quantitative, but specialized to \(\lambda\).  The random multiplicative functions arising in EDP are not all Liouville, and the pretentious branch remains. |
| [TT25, Theorem 3.1][TT25] | For general 1-bounded multiplicative \(g_1,g_2\), an \(L^{-c}\) correlation bound outside an exceptional set of logarithmic density \(O(L^{-c})\), under either a quantitative equidistribution hypothesis (plus a technical prime-range condition) or a quantitative nonpretentiousness inequality. | Promising new input for the nonpretentious branch.  To obtain an EDP rate one must still verify its hypotheses uniformly for the stochastic laws, propagate the exceptional scales through the finite Fourier reduction, and join it to the pretentious branch.  The paper does not carry out those EDP-specific steps. |
| [KLM22, Theorem 1.1][KLM22] | Konieczny--Lemańczyk--Müllner classify multiplicative automatic sequences as a prime-adic eventually-periodic factor times an eventually-periodic multiplicative factor.  Konieczny's later generalized-polynomial paper is likewise a structural classification under a strong definability hypothesis. [Kon25, abstract][Kon25] | These “Konieczny-style” structural results apply only after automaticity/generalized-polynomial structure is supplied; Tao's stochastic Fourier output has no such hypothesis.  We found no Konieczny result in this line that is a quantitative Elliott theorem for arbitrary bounded multiplicative functions. |

The cautious conclusion is therefore not that the post-2015 estimates are
irrelevant.  Pilatte and Tao--Teräväinen materially improve the correlation
component, while KMT23 gives a density strengthening in the multiplicative test
case.  What is absent from these sources is a published, end-to-end replacement
of the finite Fourier law, correlation dichotomy, and pretentious analysis that
outputs Erdős's conjectured \(c\log X\) on the product scale. [KMT23, Section 2.3][KMT23]
[Pil23, Section 1][Pil23] [TT25, Theorem 3.1][TT25]

## 6. Computational bounds: exact meanings

Konev and Lisitsa encode the existence of a length-\(n\), discrepancy-at-most-\(C\)
sequence as a SAT instance.  Sequential counters enforce every prefix bound on
every homogeneous progression; additional Boolean clauses encode
multiplicativity or complete multiplicativity.  Satisfying assignments witness
lower bounds, while DRUP certificates witness unsatisfiability and are checked by
an independent verifier. [KL14, Sections 2.2--4][KL14]

Their exact outcomes are:

| Class | \(C=1\) | \(C=2\) | \(C=3\) |
|---|---:|---:|---:|
| completely multiplicative | 9 | 246 | 127,645 |
| multiplicative | 11 | 344 | 127,645 |
| unrestricted | 11 | **1160** | **greater than 130,000**, exact maximum not determined there |

[KL14, Table 1][KL14]

For unrestricted \(C=2\), `edp(2,1160)` is satisfiable and
`edp(2,1161)` is unsatisfiable; the latter had an independently checked 1.67 GB
DRUP certificate in the revised experiment.  For \(C=3\), both restricted
classes are satisfiable through 127,645 and unsatisfiable at 127,646.  Thus the
card's shorthand “discrepancy 3 beyond 127,645” needs the multiplicative
qualifier. [KL14, Theorems 10--11, pp. 11--13][KL14]

## 7. What stops each method (one-page barrier map)

| Method | What it establishes | What stops \(D_f(X)\gg\log X\) |
|---|---|---|
| Modified characters / digit formulae | Explicit completely multiplicative sequences with \(D_f(X)=\Theta(\log X)\), including the upper obstruction \(1/(2\log3)\). [BCC08, Theorem 9][BCC08] | This is an extremal construction, not a lower-bound mechanism.  No cited inverse theorem forces an arbitrary low-discrepancy sign sequence to have the required character-plus-prime-adic form. |
| SAT and finite automata | Exact finite thresholds for \(C=2\), and for \(C=3\) under multiplicativity. [KL14, Theorems 10--11][KL14] | A separate rapidly growing SAT instance is needed for each \((C,n)\); certificates prove isolated thresholds and expose no symbolic relation \(n(C)\), much less the exponential relation equivalent to a logarithmic rate. |
| Tao's compactness reduction | Converts a hypothetical globally bounded sequence into a stochastic completely multiplicative limiting law and proves qualitative contradiction. [Tao16, Section 2][Tao16] | Prokhorov subsequence extraction has no convergence modulus.  All later parameters may depend on earlier qualitative choices, so the contradiction cannot be inverted to \(X(C)\). |
| Qualitative/almost-all-scale Elliott theory | Forces correlation cancellation for nonpretentious multiplicative functions in logarithmic averages or outside sparse exceptional scales. [TT19, Corollary 1.13][TT19] [KMT23, Theorem 1.2][KMT23] | Limits, exceptional sets, and non-uniform thresholds must be synchronized with the finite Fourier distribution and with every scale/shift used by the EDP argument.  The theorems alone do not do that assembly. |
| Quantitative Elliott/Chowla estimates | Give explicit correlation savings for Liouville, and now conditional general-multiplicative savings outside quantitatively small exceptional scale sets. [Pil23, Theorem 1.1][Pil23] [TT25, Theorem 3.1][TT25] | They address the nonpretentious correlation branch.  EDP additionally needs uniform verification of the hypotheses for its random laws, an exceptional-scale selection argument, and the structured/pretentious branch. |
| McNamara's quantitative Tao traversal | Does complete the finite-scale assembly and produces exponent \(1/484\) in the rectangle \(n\le N\), \(d\le\exp(N/(\log\log N)^{1/242})\). [Mc21, Chapter 4][Mc21] | The quantitative losses are enormous: a \(1/242\) correlation/pretentious balance, a square-root loss, iterated logarithms, and exponential dilation.  Rewriting in product scale yields only triple-log growth, far below \(\log X\). |
| Multiplicative automatic/generalized-polynomial classification | Rigidly describes sequences after an automaticity or generalized-polynomial assumption is imposed. [KLM22, Theorem 1.1][KLM22] [Kon25, abstract][Kon25] | The Fourier reduction produces arbitrary stochastic completely multiplicative functions, not automatic or generalized-polynomial ones.  The needed bridge is itself an unsupported inverse theorem. |

The actionable gap is thus a **uniform finite-scale inverse/assembly theorem**, not
simply another qualitative proof that a two-point correlation tends to zero.  A
new route must preserve the product budget \(md\le X\), treat pretentious and
nonpretentious laws with compatible explicit parameters, and avoid any limiting
law without a modulus.  This diagnosis is our synthesis of the cited proofs,
not a theorem from one source. [Tao16, footnote 4][Tao16]
[Mc21, pp. 121--124][Mc21] [TT25, Theorem 3.1][TT25]

## References

[Er64b]: https://combinatorica.hu/~p_erdos/1964-24.pdf
[Er65b]: https://combinatorica.hu/~p_erdos/1965-17.pdf
[Er81]: https://combinatorica.hu/~p_erdos/1981-16.pdf
[Er85c]: https://combinatorica.hu/~p_erdos/1985-17.pdf
[EP67]: https://www.erdosproblems.com/67
[BCC08]: https://arxiv.org/abs/0809.1691
[Tao16]: https://arxiv.org/abs/1509.05363
[Tao16E]: https://arxiv.org/abs/1509.05422
[Mc21]: https://escholarship.org/uc/item/4wr015m0
[Ter18]: https://arxiv.org/abs/1710.01195
[TT19]: https://arxiv.org/abs/1809.02518
[KMT23]: https://arxiv.org/abs/2304.05344
[Pil23]: https://arxiv.org/abs/2310.19357
[TT25]: https://arxiv.org/abs/2512.01739
[KLM22]: https://arxiv.org/abs/2004.04920
[Kon25]: https://arxiv.org/abs/2403.17590
[KL14]: https://arxiv.org/abs/1405.3097

Bibliographic details: Er64b is P. Erdős, *Problems and results on Diophantine
approximations*, Compositio Math. 16 (1964), 52--65.  Er65b is P. Erdős,
*Some recent advances and current problems in number theory*, in *Lectures on
Modern Mathematics*, vol. III (1965), 196--244.  Er81 is P. Erdős, *On the
combinatorial problems which I would most like to see solved*, Combinatorica 1
(1981), 25--42.  Er85c is P. Erdős, *On some of my problems in number theory I
would most like to see solved*, in *Number Theory, Ootacamund 1984*, Lecture
Notes in Mathematics 1122 (1985), 74--84.  The remaining links lead to the
primary paper or dissertation record cited in the text.
