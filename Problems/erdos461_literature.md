# Erdős #461: literature and route audit

Accessed 2026-09-08.  This memo distinguishes four levels of evidence:

- **Known (proved/cited):** a theorem for which a proof is present in the cited
  source, or an elementary argument proved below.
- **Reported:** an assertion in a primary source for which that source gives no
  proof or further citation.
- **Conjectured / user-supplied:** an open statement or an unrefereed forum
  comment.  The Erdős Problems site explicitly warns that comments are not
  verified.
- **Our assessment:** a deduction about whether a cited result can address
  #461.  These assessments are not claims of new theorems.

The main negative finding is important: the often-cited
`f(n,t) \gg t / log t` estimate is **reported** by Erdős and Graham, but the
two source pages contain neither its proof nor a citation for it.  Exact-phrase
and citation searches found no proof exposition.  Consequently this memo does
not promote that estimate to the "known (proved/cited)" category and does not
substitute a plausible sieve sketch for the missing proof.

## 1. Statement and the Erdős--Graham source

For `t >= 2`, write

\[
  m=s_t(m)r_t(m),
  \qquad
  s_t(m)=\prod_{p<t}p^{v_p(m)}.
\]

Thus every prime factor of `r_t(m)` is at least `t`.  Let

\[
 f(n,t)=\#\{s_t(n+1),\ldots,s_t(n+t)\}.
\]

Printed pp. 91--92 of P. Erdős and R. L. Graham, *Old and New
Problems and Results in Combinatorial Number Theory*, Monographies de
L'Enseignement Mathématique 28 (1980), MR 0592420, make exactly this
factorization (calling the factors `a_i,b_i`), ask whether some absolute
`epsilon > 0` gives a uniform positive lower bound for `f(n,t)/t`, and then
say only: “We can only show”

\[
  f(n,t)>\frac{ct}{\log t}.
\]

The scan is hosted with Ronald Graham's papers
([ErGr80, printed pp. 91--92](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf)).
The modern problem page transcribes the linear question and repeats the
`t/log t` report
([Erdős Problem #461](https://www.erdosproblems.com/461)).

**Source audit.**  The assertion occupies one displayed line.  There is no
proof after it: the book immediately begins an unrelated problem about the
least prime factor.  There is no footnote, named lemma, or reference attached
to the estimate.  The tracker currently says “Proof expositions (0).”  Searches
for the exact factorization sentence, the displayed estimate, “smooth
component,” “largest smooth divisor,” and works citing the monograph located
the monograph and tracker, but no proof of this particular bound.  This is a
search miss, not evidence that no proof exists.

### What can be rigorously reconstructed

The following elementary part is useful, but it stops strictly before the
reported lower bound.

**Lemma 1 (repeated labels are small; known, proof here).**  If `1 <= i < j <= t`
and

\[
  s_t(n+i)=s_t(n+j)=d,
\]

then `d | (j-i)`, so `d<t`.

*Proof.*  The common smooth component divides both integers, hence their
difference.  Since `0<j-i<t`, a positive divisor of `j-i` is below `t`. ∎

In fact `gcd(n+i,n+j)=d`: after division by `d`, a common prime factor would
be at least `t`, but would also divide `j-i<t`.

**Lemma 2 (exact rough fibre; known, proof here).**  Put
`P_t=prod_{p<t} p`.  For `1 <= d<t`,

\[
 s_t(m)=d
 \quad\Longleftrightarrow\quad
 d\mid m\ \text{ and }\ \gcd(m/d,P_t)=1.
 \tag{1}
\]

*Proof.*  Every prime factor of `d` is below `t`.  Thus `d` is the complete
smooth component precisely when the remaining quotient contains no prime
below `t`, equivalently when it is coprime to `P_t`. ∎

If

\[
 A_d(n)=\#\{1\le i\le t:s_t(n+i)=d\},
\]

Lemma 1 gives the exact identity

\[
 f(n,t)=t-\sum_{1\le d<t}(A_d(n)-1)_+.
 \tag{2}
\]

Equation (1) also shows that collision data are periodic modulo
`P_t lcm(1,...,t-1)`.  These facts reduce the reported estimate to a uniform,
simultaneous rough-fibre bound for the support of all `A_d`; an upper-bound
sieve for any one fibre does not prove such a support estimate.

### Why the tempting prime reconstruction is not a proof

The card's first lead associates each prime `p in (t/2,t)` with a multiple in
the interval.  Multiples at *different* positions cannot have the same smooth
component, but distinct primes need not give different positions.  This is a
real obstruction, not a technicality.  Choose an interior offset `h` and take
`n+h` divisible by the product of all primes in `(t/2,t)`.  If both distances
from `h` to the interval's ends are below those primes (for example, take a
central `h`), then `n+h` is the only multiple in the interval of every one of
those primes.  All primes are therefore sent to one position and one smooth
component.

The stronger matching proposal in the comments also has an explicit Hall
failure (Section 2 below).  The 2026 distinct-multiples theorem gives only a
square-root worst-case matching (Section 3).  Neither repairs the missing
`t/log t` proof.

**Conclusion on the requested reconstruction.**  We have reconstructed and
proved the exact collision reduction (1)--(2), and isolated the needed
simultaneous support inequality.  We could not reconstruct a correct proof of
`f(n,t) \gg t/log t` from the cited source or located literature.  The estimate
must remain labelled “reported by Erdős--Graham” until a proof or a precise
source is supplied.

## 2. The seven comments on the live problem page

The page showed seven comments when fetched.  Everything in this section is
**user-supplied and unrefereed** unless a separate source is cited.

1. **Woett, 6 May 2026.**  The proposed graph has left side
   `{1,...,floor(t/2)}`, right side the observed smooth components, and an edge
   when the left integer divides the component.  A full left matching would
   imply `f(n,t)>=floor(t/2)`.  It fails for `n=1407302,t=38`: the six left
   vertices `{13,15,16,17,18,19}` have only five neighbours, represented by
   offsets `{9,10,13,26,28}`
   ([comment 6287](https://www.erdosproblems.com/forum/thread/461#post-6287)).

2. **Pr_Huang, 12 June 2026.**  For `y<t`, averaging over a period gives

   \[
   \inf_n f(n,t)\le
   y+t\left(1-V_tH_y\right),\qquad
   V_t=\prod_{p<t}(1-1/p).
   \]

   Indeed, for `u<=y` the exact periodic density of `s_t(m)=u` is `V_t/u`.
   Taking `y` asymptotic to `e^{-gamma}t/log t` and using Mertens' product
   theorem yields the **upper** bound
   `(1-e^{-gamma}+o(1))t` for `inf_n f(n,t)`.  Thus no uniform lower-bound
   constant can exceed `1-e^{-gamma}`, and the temporary `1/2` strengthening
   is false.  This does not refute the original existence of some positive
   constant
   ([comment 6948](https://www.erdosproblems.com/forum/thread/461#post-6948)).

3. **Thomas Bloom, 16 June 2026.**  Bloom confirms that the preceding argument
   is an upper bound, asks where the `t/2` claim came from, and expects the
   averaging observation to be standard
   ([comment 7021](https://www.erdosproblems.com/forum/thread/461#post-7021)).

4. **Nat Sothanaphan, 16 June 2026.**  The `t/2` threshold came from Woett's
   failed matching idea, not from Erdős and Graham
   ([comment 7025](https://www.erdosproblems.com/forum/thread/461#post-7025)).

5. **Pr_Huang, 16 June 2026.**  The author makes the same correction and
   reiterates that the averaging calculation does not settle `f(n,t) \gg t`
   ([comment 7029](https://www.erdosproblems.com/forum/thread/461#post-7029)).

6. **Pr_Huang, 19 July 2026.**  A proposed Shannon-entropy route is shown to
   demand too much.  In the random prime-power-residue (“ruler”) model, convexity
   gives expected entropy deficit

   \[
   \mathbb E\sum_u m_u\log m_u
   \ge (e^{-\gamma}/2+o(1))t\log t.
   \]

   Hence a uniform `O(t)`, or even `O(t log log t)`, deficit bound is false.
   This is an obstruction to one sufficient condition, not an obstruction to
   the conjecture
   ([comment 7850](https://www.erdosproblems.com/forum/thread/461#post-7850)).

7. **Pr_Huang, 25 July 2026.**  A capped-log-mass argument is proposed for the
   restricted range `0<=n<=t^K`, giving
   `f(n,t) \gg_K t log log t/log t`.  Its key ingredients are the lower bound
   `sum_i log gcd(n+i,L_t^-) = t log t-O(t)`, repeated-fibre spacing, and the
   height bound on singleton rows.  The calculation is plausible, but the
   comment is unrefereed and is not a verified result.  Its additional phrase
   “known restricted-height linear result” for
   `n+t<=t^(43/30-epsilon)` gives no citation; we did not locate a source that
   states that consequence for `f`, so it too remains unverified
   ([comment 8101](https://www.erdosproblems.com/forum/thread/461#post-8101)).

## 3. Matching integers to distinct multiples

Wouter van Doorn, Yanyang Li, and Quanyu Tang define `f(m)` as follows.  For
every `m`-element set `A={a_1<...<a_m}` of positive integers and every open
real interval `I` of length `2a_m`, ask for the largest universally guaranteed
number of disjoint pairs `(a,b)` with `a in A`, `b in I cap Z`, and `a|b`.
Their exact theorem is

\[
 f(m)=\min\{m,\lceil2\sqrt m\rceil\}.
\]

For `m>=4` this is `ceil(2 sqrt(m))`.  Their proof uses the generalized
Hall/König--Ore formula; the key lower bound splits the interval into two
halves and injects a subset of `A` into a product of its two neighbourhoods.
See Theorem 1.1 and Section 2 of W. van Doorn, Y. Li, Q. Tang, *Optimal bounds
for an Erdős problem on matching integers to distinct multiples*, submitted
30 March 2026 ([arXiv:2603.28636](https://arxiv.org/abs/2603.28636),
[PDF](https://arxiv.org/pdf/2603.28636)).  The authors also report a Lean
formalization.

**Our assessment.**  Applying the theorem to divisors of size at most `t/2`
in an interval of length `t` guarantees only `Omega(sqrt(t))` distinct matched
*integers*.  Problem #461 needs distinct *smooth components*: two matched
integers can still have the same component.  The Woett graph instead puts
components, not integers, on the right and has the explicit Hall failure
above.  Restricting to large divisors bounds how many interval elements can
share a component, but multiplying the paper's square-root guarantee by that
spacing information still does not reach `t/log t`.  Thus the exact theorem is
conceptually relevant and provides a sharp warning about arbitrary-set Hall
arguments, but it supplies no Hall-type lower bound usable for #461 as stated.

## 4. Erdős--Hooley divisor concentration

For a positive integer `N`, the Erdős--Hooley Delta function is

\[
 \Delta(N)=\sup_{u\in\mathbb R}
   \#\{d\mid N:e^u<d\le e^{u+1}\}.
\]

A factor-2 dyadic interval is contained in a factor-`e` interval, so the
number of divisors of `N` in `[t/2,t)` is at most `Delta(N)`.

- **Known.**  Hooley proved in 1979

  \[
  \sum_{N\le x}\Delta(N)\ll
  x(\log x)^{4/\pi-1}.
  \]

  The exact citation is C. Hooley, “On a new technique and its applications
  to the theory of numbers,” *Proc. London Math. Soc.* (3) 38 (1979), no. 1,
  115--151.  The formula and bibliography are reproduced in the introduction
  of D. Koukoulopoulos and T. Tao
  ([arXiv:2306.08615, eq. (1.1)](https://arxiv.org/abs/2306.08615)).

- **Known.**  Koukoulopoulos--Tao sharpened the mean upper bound to

  \[
  \sum_{N\le x}\Delta(N)\ll x(\log\log x)^{11/4}.
  \]

  See their Theorem 1
  ([paper and abstract](https://arxiv.org/abs/2306.08615)).  Ford,
  Koukoulopoulos, and Tao proved the complementary mean lower bound
  `\gg_epsilon x(log log x)^(1+eta-epsilon)`
  ([arXiv:2308.11987](https://arxiv.org/abs/2308.11987)).

- **Known.**  Ford, Green, and Koukoulopoulos proved that, for every fixed
  `epsilon>0`,

  \[
  \Delta(N)\ge(\log\log N)^{\eta-\epsilon}
  \quad\text{for almost all }N,
  \qquad \eta=0.3533227727\ldots.
  \]

  They conjecture that this exponent is sharp.  See Theorem 1 of K. Ford,
  B. Green, D. Koukoulopoulos, *Equal sums in random sets and the concentration
  of divisors*, *Invent. Math.* 232 (2023), 1027--1160
  ([arXiv:1908.00378](https://arxiv.org/abs/1908.00378),
  [DOI](https://doi.org/10.1007/s00222-022-01177-y)).

**Our assessment.**  Delta can measure how many candidate divisors in a
dyadic range collapse onto one integer or component.  But all the displayed
results are mean-value or normal-order statements as `N` varies up to `x`.
Problem #461 is uniform in an unbounded shift `n`, and its components may be
highly atypical integers.  Moreover the normal-order lower bound shows that
one should not expect a constant divisor-concentration bound even typically.
No cited Delta theorem supplies the required pointwise Hall inequality.

## 5. Smooth and rough numbers in short intervals

Write `Psi(x,y)` for the number of `y`-smooth integers at most `x`.

### Smooth numbers

Friedlander and Granville prove an all-interval asymptotic

\[
 \Psi(x+z,y)-\Psi(x,y)
 =\frac{z}{x}\Psi(x,y)
 \left(1+O\left(\frac{(\log\log y)^2}{\log y}\right)\right)
\]

in their stated range

\[
 x\ge y\ge\exp((\log x)^{5/6+\epsilon}),\qquad
 x\ge z\ge x^{1/2}y^2\exp((\log x)^{1/6}).
\]

They also obtain a positive-proportion lower bound when
`z>=x^(1/2+delta)` and `y>=x^epsilon`.  See J. B. Friedlander and A. Granville,
*Smoothing “Smooth” Numbers*, *Phil. Trans. R. Soc. Lond. A* 345 (1993),
339--347 ([author PDF](https://dms.umontreal.ca/~andrew/PDF/psinshorts.pdf)).
Their introduction records Hildebrand's earlier asymptotic for
`x/z <= y^(5/12)` in a suitable `y` range.

Younis obtains the long-interval density asymptotic for every
`17/30<theta<=1`, `h>=x^theta`, and
`y>=exp(C(log x)^(2/3)(log log x)^(4/3))`; on RH, his analogous range reaches
every `theta>1/2` with `y>=(log x)^K`.  See Theorems 1.1 and 1.3 of K. Younis,
*Asymptotics for smooth numbers in short intervals*
([arXiv:2409.05761](https://arxiv.org/abs/2409.05761)).  For a recent existence
result near square-root length, see S. Jain, *Existence of Smooth Numbers in
Short Intervals*, *Q. J. Math.* 77 (2026), 397--422
([DOI and theorem statement](https://doi.org/10.1093/qmath/haag010)).

**Our assessment.**  Substituting the #461 parameters `x about n`, `y=t`,
`z=t` violates the Friedlander--Granville all-interval range for arbitrary
`n`; Younis likewise requires `t>=n^theta` plus a lower bound on the
smoothness parameter.  These theorems can inform restricted-height cases,
but not uniform arbitrary `n`.  Counting wholly smooth integers also counts
only the special component `s_t(m)=m`; it does not directly count the support
of all components.

### Rough numbers

Equation (1) makes each fibre a short-interval rough-number problem:

\[
 A_d(n)=\#\{q\in\mathbb N:n<dq\le n+t,\ (q,P_t)=1\}.
\]

Granville studies precisely

\[
 S(x,y,z)=\#\{m\in(x,x+y]:(m,P(z))=1\}
\]

and the sharpness limitations of the Rosser--Jurkat--Richert linear sieve.
See A. Granville, *Sieving intervals and Siegel zeros*, *Acta Arith.* 205
(2022), 235--248
([arXiv:2010.01211](https://arxiv.org/abs/2010.01211)).

**Our assessment.**  Classical upper-bound sieves can control one `A_d` in
ranges where the interval length `t/d` is long enough relative to the sifting
level.  They permit highly uneven short fibres and do not by themselves say
that the union of the supports of all `A_d` is large.  Formula (2) shows that
this simultaneous support question, not a one-fibre rough count, is the
uniform bottleneck.

## 6. What each approach gives and where it stops

| Approach | What it rigorously gives | Where it stops |
|---|---|---|
| Erdős--Graham | A primary-source **report** of `f(n,t)>ct/log t` | The source gives no proof or citation; our search did not locate one |
| Collision/rough-fibre reduction | Lemmas 1--2 and exact identity (2) | Leaves a uniform simultaneous-support inequality |
| Primes in `(t/2,t)` | Different positions carrying different such primes have different components | Many primes can have their sole multiple at one position |
| Woett component matching | Would give `t/2` if Hall held | Explicit Hall counterexample at `(1407302,38)` |
| van Doorn--Li--Tang | Exact `min(m,ceil(2 sqrt m))` distinct-integer matching | Square-root scale; right vertices are integers, not components |
| Erdős--Hooley `Delta` | Strong average and almost-all divisor-concentration information | Not pointwise in the arbitrary components required by #461 |
| Smooth-number short intervals | Asymptotics/existence in substantial restricted ranges | `t` is too short relative to arbitrary `n`; whole smooth numbers are only one part of the support problem |
| Rough-number sieve | Bounds individual fibres `A_d` in suitable ranges | Does not control all fibre supports simultaneously and uniformly |
| Forum entropy/capped mass | Useful proposed obstructions and restricted-height ideas | User-supplied, unverified, and explicitly height-dependent |

The sharpest honest conclusion from this audit is therefore negative but
actionable: the literature routes above do not currently furnish a verified
proof even of the reported `t/log t` estimate.  Any subsequent formalization
should first pin a citable analytic/combinatorial lemma implying the
simultaneous support bound in (2), rather than formalizing the false prime or
full-matching shortcuts.
