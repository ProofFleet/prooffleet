# Erdős #177: literature and exponent audit

This memo uses

\[
  D_g(d):=\sup_{a\ge 1,\,m\ge 1}
    \left|\sum_{i=0}^{m-1}g(a+id)\right|
\]

for a coloring `g : ℕ → {−1,1}`. The problem is to construct one
$g$ for which every $D_g(d)$ is finite, while making the step-dependent
envelope as small as possible. Endpoints and the convention for whether
$\mathbb N$ begins at zero only change indexing.

The main conclusion of this audit is:

> Beck's exponent $8$ is the exponent $4$ in his arbitrary-family
> prefix-balancing theorem, evaluated at the $\Theta(d^2)$-th sequence needed
> to list all residue-class progressions of step at most $d$.

Thus the visible accounting is $8=4\cdot2$. The factor $2$ is entirely an
enumeration cost; it is not a loss from converting prefixes to intervals.

## Status labels and an access caveat

This memo keeps three kinds of assertions separate:

- **Known** means the assertion is stated in a cited source.
- **Reconstruction** means it is an elementary deduction from a cited theorem,
  written out here so that its quantifiers and exponent losses can be checked.
- **Open / proposed** means no theorem is being claimed.

Beck's 2017 chapter is identified exactly, and its abstract is available in
the [Rutgers repository][beck17-rutgers], but neither that record nor the
publisher exposes open full text. The exact arithmetic-progression theorem is
therefore verified from the author's institutional abstract. The more general
$d^{4+\varepsilon}$ theorem is independently catalogued as Erdős problem
[#178][ep178]. The specialization from that theorem to progressions is fully
reconstructed below. Claims about the *internal proof* of exponent $4$ would
require the unavailable chapter text, so this memo deliberately treats that
result as a black-box lemma rather than inventing a proof narrative.

## Known results

### The original Erdős formulations and the factorial-scale construction

Erdős's 1966 paper records a construction, obtained independently with Cantor,
Schreiber, and Straus, of a sign sequence for which every arithmetic
progression has bounded discrepancy. It also records the useful block
observation

\[
  g(u)=-g(m+u)\qquad(1\le u\le m).
\]

When $d\mid m$, each residue-class sum over the resulting length-$2m$ block
cancels. Iterating compatible anti-periodic blocks is the mechanism behind the
early construction. The printed 1966 estimate is $L(d)<c^d d!$
([scan, printed p. 137][erdos66]).

There is a minor but genuine bibliographic inconsistency worth preserving.
Erdős's 1973 survey writes $h(d)<(cd)!$
([scan, printed p. 121][erdos73]); the Erdős--Graham monograph prints
$h(d)<c d!$ ([scan, printed p. 16][eg80]); and the modern problem page
summarizes it as $h(d)\ll d!$ ([Erdős problem #177][ep177]). All versions are
factorial-scale,

\[
  h(d)=\exp(O(d\log d)),
\]

which is the robust comparison needed here. This audit does not silently
choose one of the incompatible constants inside the factorial.

The same 1973 source poses the more general problem of simultaneously
balancing prefixes of an arbitrary countable family of integer sequences.
Beck solved existence in 1981; his first quantitative bound was
quasipolynomial in the family index. His 2017 result makes it polynomial. The
original papers also state that van der Waerden's theorem forces any
admissible envelope to tend to infinity. This only obstructs a uniform
constant; it gives no useful polynomial exponent.

### Roth's lower bound and the passage from $N^{1/4}$ to $d^{1/2}$

Roth's actual 1964 theorem is a finite-interval discrepancy statement. For a
set $A\subseteq\{1,\dots,N\}$, write its density as $\eta$, let
$\Phi_{q,h}(m)$ count elements of $A\cap[1,m]$ congruent to $h\pmod q$,
subtract the density-predicted count to form $\Phi^*_{q,h}(m)$, and put

\[
  V_q(m)=\sum_{h=1}^{q}|\Phi_{q,h}(m)-\Phi^*_{q,h}(m)|^2.
\]

Roth's displayed theorem is

\[
 \sum_{q\le Q}q^{-1}\sum_{m\le N}V_q(m)
 +Q\sum_{q\le Q}V_q(N)
 \gg \eta(1-\eta)Q^2N.                                \tag{1}
\]

Choosing $Q=\lfloor\sqrt N\rfloor$, Roth explicitly extracts
$q_0\le\sqrt N$ and $m_0\le N$ such that

\[
 q_0^{-1}V_{q_0}(m_0)\gg\eta(1-\eta)N^{1/2}.          \tag{2}
\]

After the standard split between color densities bounded away from $0,1$
and the trivial density-imbalance case, (2) gives the familiar two-color
corollary:

> Every red/blue coloring of $\{1,\dots,N\}$ has a finite arithmetic
> progression with discrepancy $cN^{1/4}$ for an absolute $c>0$; the
> $Q=\sqrt N$ argument can choose its modulus $q\le\sqrt N$.

The original article is freely available from the [Polish Academy journal
page][roth64]. The commonly quoted constant-$1/20$ finite formulation is
stated explicitly in the abstract of [Vijay's paper][vijay06], and Beck's
2017 abstract records $\sqrt d/20$ for the resulting step lower bound. The
original displayed inequalities use $\gg$, so the inference below retains an
unspecified absolute constant rather than conflating these normalizations.

Here is the quantifier conversion hidden by the shorthand
“$h(d)\gg\sqrt d$.” Restrict an infinite coloring $g$ to $[1,N]$. Roth gives
$q_N\le\sqrt N$ with

\[
  D_g(q_N)\ge cN^{1/4}
              \ge c\sqrt{q_N}.                           \tag{R}
\]

If every $D_g(q)$ is finite, the chosen $q_N$ cannot stay in a fixed finite
set as $N\to\infty$, because the first lower bound in (R) diverges. Hence
there are infinitely many distinct steps $q$ satisfying

\[
  D_g(q)\ge c\sqrt q.
\]

Equivalently, every valid envelope has $h(q)\gg\sqrt q$ along an unbounded
sequence of steps (with the cited later normalization giving $1/20$). This is
a limsup/subsequence assertion, **not** a
pointwise lower bound at every step. The distinction matters: the
Thue--Morse example below has bounded discrepancy at every power-of-two step.

### Beck 2017: exact statement

The exact reference is József Beck, “A Discrepancy Problem: Balancing Infinite
Dimensional Vectors,” in *Number Theory -- Diophantine Problems, Uniform
Distribution and Applications*, Springer, 2017, pp. 61--82,
[DOI 10.1007/978-3-319-55357-3_3][beck17-doi].

The institutional abstract states:

> For every $\varepsilon>0$, there are $d_0(\varepsilon)$ and a coloring
> $g:\mathbb N\to\{-1,1\}$ such that
> $D_g(d)\le d^{8+\varepsilon}$ for every $d\ge d_0(\varepsilon)$.

Finitely many exceptional $d$ can be absorbed into a multiplicative constant,
since the same constructed coloring has finite discrepancy at each fixed
step. Thus the common asymptotic formulation is
$D_g(d)\ll_\varepsilon d^{8+\varepsilon}$.

The input theorem behind this corollary is the answer to Erdős problem #178.
For any countable collection

\[
  A_i=\{a_{i1}<a_{i2}<\cdots\}\subseteq\mathbb N,
\]

and any $\delta>0$, there is a single coloring $g$ for which

\[
  \max_{1\le i\le k}\sup_{m\ge1}
  \left|\sum_{j=1}^{m}g(a_{ij})\right|
  \ll_\delta k^{4+\delta}                              \tag{B}
\]

for every $k$. The statement, attribution, and exponent are recorded on the
[problem #178 page][ep178]. Beck's terminology “infinite-dimensional vector
balancing” comes from representing integer $n$ by its incidence vector

\[
  v_n=(\mathbf 1_{n\in A_1},\mathbf 1_{n\in A_2},\ldots).
\]

Choosing $g(n)$ chooses the sign of $v_n$; coordinate $i$, stopped at the
location $a_{im}$, is exactly the prefix sum in (B). Unlike ordinary finite
vector balancing, the theorem controls every stopping time in every one of
countably many coordinates with a bound depending only on coordinate rank.

## Reconstruction: Beck's progression corollary as lemmas

This is the complete specialization of (B); only (B) itself remains a cited
black box.

**Lemma 1 (residue rays are the right sequences).** For every $q\ge1$ and
$0\le r<q$, set

\[
  A_{q,r}=\{n\ge1:n\equiv r\pmod q\},
\]

listed increasingly. Every finite arithmetic progression of difference $q$
is a consecutive interval in exactly one $A_{q,r}$.

**Lemma 2 (prefix control gives interval control at no exponent cost).** If
all prefixes of sequence $A_i$ have discrepancy at most $H(i)$, then every
consecutive interval in it has discrepancy at most $2H(i)$, by subtracting
its two endpoint prefixes. The factor $2$ is an absolute constant.

**Lemma 3 (coordinate rank).** Order pairs $(q,r)$ by increasing $q$, and
arbitrarily within a fixed $q$. The last coordinate of difference $d$ has
rank

\[
  K(d)=\sum_{q=1}^{d}q={d(d+1)\over2}\le d^2.          \tag{C}
\]

This is the sole quadratic loss. Using one sequence per start $a$ would be an
unnecessary infinite duplication; starts sharing a residue are intervals of
one ray.

**Lemma 4 (substitution).** Apply (B) to the ordering in Lemma 3. For a
progression of difference $d$, Lemmas 1--3 give

\[
  D_g(d)\ll_\delta 2K(d)^{4+\delta}
       \le 2(d^2)^{4+\delta}=2d^{8+2\delta}.           \tag{D}
\]

Given the requested $\varepsilon>0$, choose $\delta=\varepsilon/2$.
Equation (D) becomes $D_g(d)\ll_\varepsilon d^{8+\varepsilon}$.

The exponent ledger is therefore:

| operation | input scale | output scale | exponent cost |
|---|---:|---:|---:|
| arbitrary-family theorem (B) | first $K$ sequences | $K^{4+\delta}$ | $4+\delta$ (black box) |
| enumerate all residue rays through step $d$ | $d$ | $K(d)=\Theta(d^2)$ | multiply by $2$ |
| prefixes to arbitrary starts/lengths | $H$ | $2H$ | none |
| set $\delta=\varepsilon/2$ | $d^{8+2\delta}$ | $d^{8+\varepsilon}$ | bookkeeping only |

So no factor of exponent $8$ is lost in an $L^2$-to-$L^\infty$ conversion or
in handling the length. All eight powers visible in the progression
corollary are “four powers per coordinate rank” times “two powers of
coordinate rank per step.” What this access-limited audit cannot honestly
subdivide is exponent $4$ inside Beck's general theorem.

## Related balancing theorems: what transfers and what does not

| theorem | source-backed finite statement | relevance to Beck's chain |
|---|---|---|
| Spencer, “six standard deviations” | An $n$-point, $n$-set system has discrepancy at most $6\sqrt n$. | Powerful one-shot finite balancing, but neither countably many coordinates nor every prefix is controlled. Applying it cutoff by cutoff does not produce a compatible infinite coloring. |
| Banaszczyk vector balancing | If $\lVert v_i\rVert_2\le1/5$ and a symmetric convex body $K\subset\mathbb R^n$ has Gaussian measure at least $1/2$, signs can be chosen with $\sum\pm v_i\in K$. | A final-sum theorem in a fixed finite dimension. Encoding all stopping times creates growing dimension and a body whose Gaussian measure and thresholds must be re-audited; the theorem does not directly replace (B). |
| Matoušek--Spencer | The discrepancy of all arithmetic progressions contained in $[N]$ is $O(N^{1/4})$, matching Roth's lower bound. | Optimal for each finite horizon, but the coloring depends on $N$, and the bound grows with $N$. Compactness gives no fixed bound for a fixed step, so this does not imply Erdős #177. |
| Bansal | A polynomial-time randomized partial-coloring framework recovers several entropy-method discrepancy bounds. | Makes finite existential partial coloring algorithmic; it does not remove the horizon or dimension dependence needed for (B). |
| Lovett--Meka | The edge-walk gives a constructive proof of the partial-coloring lemma and Spencer-type results. | Same obstruction: an algorithm for each truncation is not a coherent coloring of $\mathbb N$ with all-prefix bounds. |

Sources are Spencer's [1985 paper][spencer85], Banaszczyk's [1998
paper][banaszczyk98], the author-hosted [Matoušek--Spencer paper][ms96],
Bansal's [2010 paper][bansal10], and Lovett--Meka's [2012 paper][lm12].

There are two closer comparisons.

1. Beck and Spencer constructed, for each finite parameter $n$, colorings of
   the integers well distributed relative to progressions in a prescribed
   finite range ([1984 paper][bs84]). The dependence on that external range
   prevents a direct diagonal limit with a step-only bound.
2. Modern work on *prefix* vector discrepancy proves finite-horizon analogues
   of Banaszczyk, with bounds depending logarithmically on the dimension and
   time horizon ([Bansal--Jiang--Meka--Singla--Sinha 2022][prefix22]). The
   remaining $T$-dependence still diverges as the horizon tends to infinity;
   the improved smoothed-input result does not apply to the adversarial,
   highly structured incidence vectors here.

Accordingly, none of these results can simply be inserted into Lemma 4 to
improve $8$. A replacement must be infinite/coherent and control all prefixes,
not merely produce a good final signed sum.

## Small-step and structured constructions

The following are direct checks, included as diagnostics rather than new
literature claims.

- The alternating coloring $g(n)=(-1)^n$ has $D_g(1)\le1$, but the step-two
  progression stays in one parity class and has unbounded discrepancy.
- Repeating `++--` has $D_g(1)\le2$ and $D_g(2)\le1$, but every
  periodic coloring of period $P$ fails at step $P$: a residue ray is
  constant.
- For the Thue--Morse coloring $t(n)=(-1)^{s_2(n)}$, one has
  $D_t(2^k)\le2$ for every $k\ge0$. Indeed, write $a=r+2^kq$ with
  $0\le r<2^k$; then $t(a+j2^k)=t(r)t(q+j)$, and every interval sum of
  Thue--Morse is at most two because its prefix sums lie in
  $\{-1,0,1\}$. This explains why Roth's lower bound cannot hold pointwise
  for every $d$.
- Rudin--Shapiro has square-root-size prefix sums, not a length-independent
  bound even when $d=1$, so it is not itself an admissible construction.
- The Cantor--Erdős--Schreiber--Straus anti-periodic block idea is
  qualitatively different: block lengths are chosen recursively so more
  divisibility classes cancel at later stages. Its cost is the
  factorial-scale envelope recorded above.

These examples suggest that excellent control on a sparse multiplicatively
structured set of steps is easy; simultaneous compatibility between unrelated
residue systems is the real issue.

## Open claims and non-claims

- It is open to replace $8$ by any smaller exponent in this infinite,
  step-dependent problem.
- The lower exponent $1/2$ is only known as an unavoidable subsequential
  obstruction. There is no known construction matching it.
- Optimal finite discrepancy $\Theta(N^{1/4})$ does not settle the infinite
  problem.
- This memo proves no new discrepancy bound. Equations (C) and (D) are an
  elementary reconstruction of a published corollary from the published
  arbitrary-family theorem.

## Where the exponent could move

There are exactly two visible attack surfaces.

1. **Improve the arbitrary-family exponent.** If (B) held with
   $k^{\beta+\varepsilon}$, the same enumeration would immediately give
   $D_g(d)\ll d^{2\beta+\varepsilon}$. Any $\beta<4$ beats Beck's $8$.
   The finite balancing theorems above look much stronger numerically, but a
   candidate proof has to supply the missing infinite all-prefix coherence.
2. **Exploit progression structure before invoking general balancing.** The
   quadratic count $K(d)=\Theta(d^2)$ is exact for distinct residue rays, so
   merely reordering them cannot help. An improvement must avoid paying for
   every ray as an unrelated coordinate--for example, by a structured norm,
   a multiscale congruence decomposition, or a theorem whose cost depends on
   the $d$ moduli rather than their $\Theta(d^2)$ residue classes. If exponent
   $4$ stayed unchanged but the effective coordinate scale became
   $O(d^{2-\eta})$, the final exponent would become $8-4\eta$.

The second route is specific to Erdős #177 and is invisible to a theorem for
arbitrary sequence families. The first route is broader but must improve the
black-box part of Beck's chapter. Recovering the full chapter and auditing the
proof of (B) line by line is the necessary next literature step before
assigning its four powers to finer sublemmas.

## References

- [Erdős problem #177][ep177] and the adjacent arbitrary-family [problem
  #178][ep178].
- P. Erdős, “Remarks on number theory V. Extremal problems in number theory
  II,” *Matematikai Lapok* 17 (1966), 135--155. [Author-hosted scan][erdos66].
- P. Erdős, “Problems and results on combinatorial number theory III.”
  [Author-hosted 1973 scan][erdos73].
- P. Erdős and R. L. Graham, *Old and New Problems and Results in
  Combinatorial Number Theory*, Monographie 28, L'Enseignement Mathématique,
  1980. [Author-hosted scan][eg80].
- K. F. Roth, “Remark concerning integer sequences,” *Acta Arithmetica* 9
  (1964), 257--260. [DOI and full text][roth64].
- J. Beck, “Balancing families of integer sequences,” *Combinatorica* 1
  (1981), 209--216. [DOI][beck81].
- J. Beck, “A Discrepancy Problem: Balancing Infinite Dimensional Vectors,”
  2017, pp. 61--82. [Institutional record and abstract][beck17-rutgers];
  [DOI][beck17-doi].

[ep177]: https://www.erdosproblems.com/177
[ep178]: https://www.erdosproblems.com/178
[erdos66]: https://users.renyi.hu/~p_erdos/1966-20.pdf
[erdos73]: https://users.renyi.hu/~p_erdos/1973-21.pdf
[eg80]: https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf
[roth64]: https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/9/3/95469/remark-concerning-integer-sequences
[vijay06]: https://arxiv.org/abs/math/0604511
[beck81]: https://doi.org/10.1007/BF02579326
[beck17-rutgers]: https://scholarship.libraries.rutgers.edu/esploro/outputs/bookChapter/A-Discrepancy-Problem-Balancing-Infinite-Dimensional/991031665483404646
[beck17-doi]: https://doi.org/10.1007/978-3-319-55357-3_3
[spencer85]: https://doi.org/10.2307/2000258
[banaszczyk98]: https://doi.org/10.1002/(SICI)1098-2418(199810)12:4%3C351::AID-RSA3%3E3.0.CO;2-S
[ms96]: https://cs.nyu.edu/~spencer/papers/matousek.pdf
[bansal10]: https://arxiv.org/abs/1002.2259
[lm12]: https://arxiv.org/abs/1203.5747
[bs84]: https://eudml.org/doc/205908
[prefix22]: https://doi.org/10.4230/LIPIcs.ITCS.2022.13
