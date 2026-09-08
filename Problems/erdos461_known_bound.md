# Erdős 461: audit of the reported logarithmic bound

## Verdict

I could not reconstruct a proof of the reported uniform bound

\[
  f(n,t) \gg \frac{t}{\log t}.
\]

Erdős and Graham state it on printed p. 92, but the source supplies neither
an argument nor a citation.  The earlier literature audit reached the same
conclusion, and an independent re-check for this item found no proof
exposition.  This is a failure to locate a proof, not evidence that the
assertion is false.

What can be recovered rigorously is an exact one-fibre reduction to rough
numbers.  I formalized that reduction, applied the repository's finite Brun
sieve to every individual fibre, and proved an exact collision ledger.  The
remaining gap is simultaneous: the available sieve estimate controls each
fibre separately but does not control the total loss caused by all fibres at
once.  `KnownBound.lean` records that gap as
`SimultaneousFiberLossAssumption`; it declares no instance and therefore does
not claim the reported bound as a theorem.

## Known and machine-checked facts

For $t\ge 2$, put

\[
  s_t(m)=\prod_{\substack{p\mid m\\p<t}}p^{v_p(m)},
  \qquad
  F_S(n,t)=\{m\in(n,n+t]:s_t(m)=S\}.
\]

The following facts are proved in
[`KnownBound.lean`](../Conjectures/C0004_erdos461_smooth/src/KnownBound.lean).

### 1. Removing the smooth part produces a rough quotient

If $m>0$, then no prime $p<t$ divides $m/s_t(m)$.  The proof compares
the $p$-adic factorization of `smoothPart t m` with that of $m$; it does
not assume unique-factorization facts that are absent from the Lean tree.
The pinned theorem is:

```lean
theorem not_dvd_div_smoothPart_of_prime_lt {t m p : ℕ} (hm : 0 < m)
    (hp : p.Prime) (hpt : p < t) : ¬p ∣ m / smoothPart t m
```

Consequently division by $S$ injects $F_S(n,t)$ into

\[
 Q_S(n,t)=\left\{q:\left\lfloor\frac nS\right\rfloor<q
 \le\left\lfloor\frac{n+t}{S}\right\rfloor,
 \ p\nmid q\text{ for every prime }p<t\right\}.
\]

This is formalized as

```lean
theorem smoothPartFiber_card_le_roughQuotients (n t S : ℕ) :
    (smoothPartFiber n t S).card ≤ (roughQuotients n t S).card
```

The direction is deliberately only an injection for arbitrary $S$.  No
unproved characterization of which $S$'s occur is needed.

### 2. Brun gives an explicit bound for one fibre

The repository already proves a pure upper-bound sieve on any finite integer
interval.  It includes the main Euler-product term, the odd Bonferroni-tail
term, and an explicit endpoint error for all retained subsets; see
[`card_no_factor_Ioc_le_brun`][TreeBrun].  Applying it to $Q_S(n,t)$ proves
`smoothPartFiber_card_le_brun` for every $n,t,S,k$.  In compressed notation,
with $P=\{p:p<t\}$, the result is

\[
 |F_S(n,t)|\le
 \left(\left\lfloor\frac{n+t}{S}\right\rfloor-
       \left\lfloor\frac nS\right\rfloor\right)
 \left(\prod_{p\in P}\left(1-\frac1p\right)
 +\frac{(\sum_{p\in P}1/p)^{2k+1}}{(2k+1)!}\right)
 +( |P|+1)^{2k}.
\]

This is a genuine unconditional theorem, but it is a theorem about one fixed
fibre.

### 3. The collision loss is exact

Let

\[
  E(n,t)=\sum_{S\in\{s_t(n+1),\ldots,s_t(n+t)\}}
             (|F_S(n,t)|-1).
\]

Since the nonempty fibres partition the interval,

\[
  E(n,t)+f(n,t)=t.
\]

Both the partition sum and this identity are proved in Lean as
`sum_smoothPartFiber_card` and
`collisionExcess_add_smoothComponentCount`.  Thus the reported bound is
equivalent to saving $\gg t/\log t$ from the maximum possible collision
loss.

## Reported or conjectured statements

### The 1980 report

Erdős and Graham define this factorization on printed pp. 91--92 and, after
asking for a constant-proportion lower bound, write “We can only show” before
displaying $f(n,t)>ct/\log t$ [ErGr80, p. 92][ErGr80].  The next text starts
a different problem concerning the least prime factor.  There is no proof,
footnote, named result, or bibliographic pointer attached to the display.

The maintained [Erdős Problems entry][EP461] repeats the logarithmic claim
and continues to list the linear bound as open.  The B1 source audit reports
that exact-phrase, terminology, and citation searches found no proof and that
the tracker listed zero proof expositions at the time of access
([draft PR #3730][B1]).  I therefore use **reported**, not **known**, for the
logarithmic estimate.

The target $f(n,t)\gg t$ is the conjecture.  Neither the present memo nor
the Lean file proves it.

### The isolated formal assumption

The Lean definition `Erdos461LogBound` records the reported proposition as a
`def : Prop`, not a theorem.  The only open interface in this item is:

```lean
class SimultaneousFiberLossAssumption : Prop where
  bound : ∃ c : ℝ, 0 < c ∧ ∀ n t : ℕ, 2 ≤ t →
    (collisionExcess n t : ℝ) ≤
      (t : ℝ) - c * (t : ℝ) / Real.log t
```

The conditional theorem
`erdos461LogBound_of_simultaneousFiberLoss` is proved from this class and the
collision identity.  No instance is supplied.  The class is intentionally
close to the missing global estimate: the investigation found no defensible
weaker sieve lemma from which it follows.

## Our route analysis

### Route A: count primes in $(t/2,t)$

A Chebyshev lower bound can supply $\gg t/\log t$ primes in a suitable
dyadic block.  That count is not the missing step.  To turn it into distinct
smooth components, one must assign the primes to distinct interval elements,
or otherwise show that their component values differ.

The proposed assignment is false.  At $t=8,n=1255$, both 5 and 7 have only
the multiple 1260 in $(1255,1263]$; they therefore lead to one position and
one component, not two.  This was found by the reproducible B2 search
([PR #3738][B2]) and is also the obstruction highlighted in the B1 audit.
Hence adding stronger prime-counting estimates cannot repair this route.

### Route B: bound each fibre and divide

The formal Brun theorem bounds $|F_S|$, so one might combine

\[
  t=\sum_S |F_S|

\]

with a uniform maximum-fibre bound.  This loses too much.  For small $S$,
the quotient interval has length about $t/S$; even the expected sieve main
term is about $t/(S\log t)$.  At $S=1$, a bound of that scale would yield
only $f(n,t)\gg\log t$ through the maximum-fibre inequality.  The explicit
finite Brun remainder can make that estimate weaker still unless the
truncation range is large enough.

Thus the one-fibre theorem is correct but has the wrong aggregation geometry
for $t/\log t$.

### Route C: sum the one-fibre Brun bounds

Summing creates two separate losses.

1. The principal lengths contribute approximately
   $\sum_S t/S$, and no available theorem controls this reciprocal weight
   over the **realized** component support in the required worst-case manner.
2. The endpoint term $(|P|+1)^{2k}$ is paid once for every $S$.  A union of
   individually valid upper bounds therefore has no useful uniform error
   before one already knows substantial information about the support.

More fundamentally, an upper bound on every $F_S$ does not encode how the
different sifted quotient intervals correlate.  The target is a lower bound
on how many $S$'s occur, equivalently an upper bound on their **total**
collision excess.  Treating the fibres independently discards exactly that
simultaneous information.

### Route D: use the numerical collision pattern as a theorem

The B2 calculations prove exact minima only through $t=11$, and later rows
are sampled.  Their highly divisible-centre examples have about $t/2$
pair-collisions, all at small components, while still leaving about half the
components distinct.  This explains why large-component fibre bounds and
naive Hall matchings miss the difficult scale.  It does not prove an
asymptotic lower bound, and this item does not extrapolate it.

## Precise obstruction and next usable input

The available facts now form the following implication chain:

```text
exact factorization
  -> fibre injects into one rough quotient interval        (proved)
  -> explicit finite Brun upper bound for that fibre       (proved)

all nonempty fibres partition (n,n+t]                      (proved)
  -> collisionExcess + smoothComponentCount = t            (proved)

uniform simultaneous bound on total collisionExcess         (missing)
  -> f(n,t) >= c t / log t                                  (proved conditionally)
```

The missing input must couple the fibres.  Examples of genuinely useful
forms would be a weighted bound for the total excess, a second-moment bound
for the fibre sizes strong enough to imply $t/\log t$ support, or a
multiscale expansion theorem surviving the B2 Hall obstructions.  The
current Chebyshev and Brun results provide none of these consequences by
themselves.

This is the precise stopping point: the 1980 logarithmic estimate remains
unverified, but the elementary reduction, the strongest directly applicable
tree sieve theorem, and the exact missing global inequality are all pinned in
Lean without proof placeholders or an assumption instance.

[B1]: https://github.com/ProofFleet/moltresearch/pull/3730
[B2]: https://github.com/ProofFleet/moltresearch/pull/3738
[EP461]: https://www.erdosproblems.com/461
[ErGr80]: https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf
[TreeBrun]: https://github.com/ProofFleet/moltresearch/blob/b3336e2aa654e7d731fc9a03c23e0723b7fe91a0/MoltResearch/Discrepancy/BrunIntervalSieve.lean#L754-L762
