# Erdős 461: approach memo and formal reduction

## Executive verdict

The two tempting injections in the card do not survive worst-case intervals.
The prime version already fails at $t=8,n=1255$: the primes 5 and 7 have
only the common multiple 1260 in $(n,n+t]$.  The dyadic-divisor version can
collapse almost completely around a highly divisible central integer.  These
are computations, not a disproof of Erdős 461; the target remains open on the
[problem page][EP461].

The sharpest live reduction found here replaces a perfect matching to
**multiples** by a positive-proportion partial matching directly into the
distinct **smooth-component values**.  This is formalized as
`ProportionalComponentMatchingAssumption`.  The finite-cardinality bridge from
that assumption to `Erdos461` is proved.  The assumption itself is not proved
and is not claimed to follow from the literature.

## Known results and unconditional facts

### Source status

Erdős and Graham define the same smooth component and ask for a uniform
positive-proportion lower bound [ErGr80, p. 92][ErGr80].  They record the
weaker $f(n,t)\gg t/\log t$ bound; the maintained page still labels the
positive-proportion question open [EP461].

### The high-fiber observation is correct

If $s_t(x)=s_t(y)=S$, then `smoothPart_dvd` gives $S\mid x$ and $S\mid y$,
so $S\mid |x-y|$.  Three multiples of an $S\ge t/2$ would have first-to-last
distance at least $2S\ge t$, but two elements of $(n,n+t]$ differ by less
than $t$.  Hence such a fiber has size at most two.

This is machine-checked without assumptions as:

```lean
theorem smoothPartFiber_card_le_two (n t S : ℕ) (ht : t ≤ 2 * S) :
    (smoothPartFiber n t S).card ≤ 2
```

The proof in `Reduction.lean` splits the interval at `n + S` and proves that
each side contains at most one multiple of `S`.

### Why the proposed matching theorems stop

Van Doorn, Li, and Tang prove the exact answer to a different Erdős matching
problem.  If $A=\{a_1<\cdots<a_m\}$ and an open interval has length $2a_m$,
the number of elements of $A$ that can always be matched to distinct
multiples is

\[
\min\bigl(m,\lceil2\sqrt m\rceil\bigr).
\]

This is optimal [van Doorn--Li--Tang, Theorem 1][VDLT].  Applied to
$A=\{1,\ldots,\lfloor t/2\rfloor\}$, it guarantees only $O(\sqrt t)$
distinct multiples.  It does not guarantee distinct smooth components after
the map $m\mapsto s_t(m)$.  Applied to the card's dyadic set
$A=[\lceil t/2\rceil,t)$, its hypothesis asks for an interval of length
about $2t$, twice the length available here.  Thus the 2026 theorem neither
supplies a linear bound nor validates the proposed dyadic route.

The public discussion records a separate failure of a perfect component
matching at $t=38,n=1407302$ [EP461-thread].  The exact $t=8$ obstruction and
the highly divisible-center family were independently found in the B2 search
[B2].

### Why the Erdős--Hooley delta results do not close the gap

The Erdős--Hooley function measures the largest number of divisors of an
integer in a fixed multiplicative-width window.  Ford, Green, and
Koukoulopoulos prove an almost-all lower bound of order
$(\log\log n)^{0.35332277\ldots}$ and study its typical behavior [FGK].
Those are normal-order/concentration results for one integer.  The reduction
here needs a **uniform**, worst-case expansion statement for a divisibility
graph built from every additive interval $(n,n+t]$.  Large divisor
concentration can create Hall obstructions, so the cited result diagnoses the
difficulty but supplies no required lower bound.

## Conjectured or assumed statements

The only original conjecture asserted here is Erdős 461 itself.  The
following matching property is a proposed sufficient condition, isolated as
an assumption rather than claimed as true.

For

\[
L_t=\{1,\ldots,\lfloor t/2\rfloor\},\qquad
R_{n,t}=\{s_t(n+1),\ldots,s_t(n+t)\},
\]

join $d\in L_t$ to $S\in R_{n,t}$ when $d\mid S$.  The formal class asks for
one absolute $c>0$ such that every graph contains a matching on at least
$ct$ left vertices:

```lean
class ProportionalComponentMatchingAssumption : Prop where
  bound : ∃ c : ℝ, 0 < c ∧ ∀ n t : ℕ, 2 ≤ t →
    ∃ M : ComponentMatching n t, c * t ≤ M.domain.card
```

This assumption is stronger than the desired cardinality bound because it
also demands divisor-compatible representatives.  It may ultimately need
weakening or replacement; its value now is to expose a precise, falsifiable
combinatorial bottleneck rather than hide it inside an informal Hall claim.

## Our proposed route

### Formal object

`ComponentMatching n t` contains a finite domain $D\subseteq L_t$, a map
$\phi:D\to R_{n,t}$, proofs of $d\mid\phi(d)$, and injectivity of $\phi$.
The divisibility field records the intended graph, while injectivity is the
load-bearing condition.  The theorem

```lean
theorem ComponentMatching.card_le_smoothComponentCount
    (M : ComponentMatching n t) :
    M.domain.card ≤ smoothComponentCount n t
```

is then just the finite injection bound.  Combining it with the class witness
gives the requested conditional theorem:

```lean
theorem erdos461_of_assumptions
    [ProportionalComponentMatchingAssumption] : Erdos461
```

No instance of the assumption class is declared.

### Dependency DAG

```text
K0  smoothPart_dvd (B0, proved)
 └──> K1  smoothPartFiber_card_le_two (proved outright)

A1  ProportionalComponentMatchingAssumption (open interface)
 └──> K2  ComponentMatching.card_le_smoothComponentCount (proved)
       └──> K3  erdos461_of_assumptions (proved conditional theorem)

K1 + defect-Hall analysis + divisor-concentration control
 ─ ─ ─ future attempted discharge/refinement of A1

VDLT distinct-multiple theorem
 ─ ─ ─ supplies only a sqrt(t) benchmark, not A1
```

In defect-Hall language, a matching of size at least $q$ from a left set $L$
is equivalent to controlling every deficiency
$|U|-|N(U)|$ by $|L|-q$.  That identifies the real Phase-2 target: prove a
linear defect bound for the **component** neighborhood, after explicitly
accounting for highly divisible values.  The product-neighborhood argument
in the 2026 matching paper is a useful model for defect Hall, but its right
vertices are integers and its best general bound is only square-root sized
[VDLT, §3][VDLT].

### What the high-fiber lemma contributes

For right vertices $S\ge t/2$, interval multiplicity is at most two.  This
prevents a large component from absorbing many interval elements.  It does
not control the small-component side: the computational worst cases put all
pair collisions below $t/2$, and a very small smooth component may have many
preimages.  Any proof of A1 therefore needs a multiscale statement, not a
single cutoff at $t/2$.

## Phase-2 items

These are proposed follow-ups; they are not claims of results.

- **B4 (after: B3) — Component-graph foundations.** Prove that a positive
  $d<t$ dividing a positive $m$ divides `smoothPart t m`; prove every
  $d\in L_t$ has a component neighbor; formalize the finite defect-Hall
  criterion for `ComponentMatching` in a new leaf Lean file.
- **B5 (after: B1, B3) — Known-bound route.** Translate the reconstructed
  Erdős--Graham $t/\log t$ proof into precise Lean lemmas, explicitly avoiding
  the false prime injection, and identify the smallest missing sieve input.
- **B6 (after: B2, B3) — Matching obstructions.** Formalize the
  $t=8,n=1255$ counterexample and the highly divisible-center family; compute
  their exact defect profiles to determine which left sets remain viable.
- **B7 (after: B4, B6) — Expansion interface refinement.** State an explicit
  multiscale neighborhood inequality and prove it implies
  `ProportionalComponentMatchingAssumption`.  If the proposed inequality is
  false, retain the exact counterexample and revise the interface rather than
  weaken a theorem silently.
- **B8 (after: B1, B7) — Delta/sieve attack.** Test whether divisor-window
  bounds plus the interval sieve control the total defect after exceptional
  high-divisor components are removed.  A rigorous no-route memo is an
  acceptable outcome.
- **B9 (after: B5, B8) — Milestone decision.** Either discharge the refined
  matching assumption, or land the machine-checked $t/\log t$ theorem and a
  precise statement of the remaining uniform obstruction.

## Where the route stops

The formal reduction is complete, but A1 has no proof.  General
distinct-multiple matching gives only square-root scale and does not survive
the smooth-component quotient.  Typical Erdős--Hooley delta estimates do not
provide worst-case additive-interval expansion.  The next honest step is the
defect profile in B6 followed by a multiscale neighborhood inequality, not an
assertion that the original dyadic matching works.

[B2]: https://github.com/ProofFleet/moltresearch/pull/3738
[EP461]: https://www.erdosproblems.com/461
[EP461-thread]: https://www.erdosproblems.com/forum/thread/461
[ErGr80]: https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf
[FGK]: https://arxiv.org/abs/1908.00378
[VDLT]: https://arxiv.org/abs/2603.28636
