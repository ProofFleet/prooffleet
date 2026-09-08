# Structured-branch threshold audit

Research snapshot: 2026-09-08.  This memo audits the structured side of the
finite-rate reduction and documents
[`StructuredThresholds.lean`](../Conjectures/C0003_edp_rate/src/StructuredThresholds.lean).
It separates the published argument, theorems already proved in the formal tree,
and the finite packaging introduced here.  It does **not** prove
`FiniteBorweinChoiCoonsRateAssumption` or an Erdős-discrepancy rate.

## Executive finding

The current formal structured branch already contains more explicit analytic
information than the A3 memo credited it with.  The Mertens loss is `1`, the
finite Euler-product loss is `13`, their zeta-pretense total is `14`, and the
public archimedean-repulsion loss is `24`.  The `t`-cut uses the composite
parameters

\[
  Q_{\rm VK}=Q^2,\qquad T_{\rm VK}=2T,\qquad M_{\rm VK}=6B+1.
\]

Moreover, the formal `t`-cut no longer depends on a zero-free-region hypothesis:
the required twist-distance result was subsequently proved from an elementary
zeta bound and a character power trick.  The zero-free-region chain in this
repository belongs to the separate Matomäki--Radziwiłł branch.  This corrects
the stale dependency description in `Problems/edp_rate_approach.md`.

The new Lean file turns the remaining existential `t`-cut threshold into a
function and defines one terminal natural scale as the exact maximum used by
the qualitative wrapper.  Its theorem proves all ten terminal inequalities at
once.  The fit of this scale below `edpAnalysisCutoff x` is deliberately left to
A9.

## 1. Known

### Known in the literature

Tao's Section 4 fixes the hierarchy

\[
 C \ll 1/\varepsilon \ll H \ll 1/\delta,k \ll X
\]

and applies the pretentiousness conclusion at both `X` and `X^δ`.  Its stated
purpose is exact: “It will be convenient to cut down the size of t.”  Lemma 4.1
then compares the two character twists and invokes a Vinogradov--Korobov
zero-free region to force their frequencies together.  Later, Euler products
turn the structured factor into character-twisted Dirichlet series.  See
[Tao, Section 4, pp. 14--18](https://arxiv.org/pdf/1509.05363).

Tao also identifies the effectivity obligation in footnote 4: a quantitative
proof “requires some treatment of error terms created when truncating Euler
products.”  The paper says those errors can be made negligible by choosing the
truncation extremely large relative to the other parameters, but it does not
record a numerical terminal function.  See
[Tao, Section 2, p. 9](https://arxiv.org/pdf/1509.05363#page=9).

### Known in the formal tree

The following are proved statements, not asymptotic promises.

| Component | Range | Proved loss / parameter map |
|---|---:|---:|
| Mertens floor | `2 ≤ y` | `log log y ≤ Σ_{p<y} 1/p + 1` |
| Truncated Euler bridge | `3 ≤ y` | prime twist sum `≤ log ‖L‖ + 13` |
| Zeta-pretense combination | `3 ≤ y`, `1 ≤ |t|` | total additive loss `1 + 13 = 14` |
| Pure archimedean repulsion | `3 ≤ y`, `6 ≤ |u|` | mass minus `log log (|u|+2) + 24` |
| Two-certificate `t`-cut | `Q,T ≥ 1`, `B ≥ 0`, `0<δ<1` | `(Q², 2T, 6B+1)` passed to twist-farness |

The Mertens statement is
[`log_log_le_sum_one_div_primesBelow`](https://github.com/ProofFleet/moltresearch/blob/ccde5842/MoltResearch/Discrepancy/MertensFloor.lean#L187-L190).
The Euler bridge records the constant `13` directly; its file-level audit splits
this as weight replacement `4`, prime-tail completion `8`, and the full Euler
log bridge `1`.
[`sum_re_twist_div_le_log_norm_LSeries`](https://github.com/ProofFleet/moltresearch/blob/ccde5842/MoltResearch/Discrepancy/TruncatedBridge.lean#L40-L47)
The repulsion theorem records `24` and explicitly notes that no zero-free region
enters.
[`pretentiousDistSq_phase_one_ge`](https://github.com/ProofFleet/moltresearch/blob/ccde5842/MoltResearch/Discrepancy/Repulsion.lean#L152-L163)

The formal `t`-cut is a quasi-triangle contradiction.  Two certificates each
costing `B` give the cap `6B`; the opposite conclusion is requested at `6B+1`
for the product character, whose modulus is at most `Q²` and whose frequency is
at most `2TX`.
[`tcut_of_vinogradovKorobov`](https://github.com/ProofFleet/moltresearch/blob/ccde5842/Conjectures/C0002_erdos_discrepancy/src/TrackCStage5TCut.lean#L37-L66)

The surprising point is historical drift inside the formal development.  Tao's
paper uses a zero-free region, and the old interface retained that name, but the
interface now has an unconditional instance from `ZetaBound.lean`.  That proof
uses a character power trick and a zeta estimate, and its theorem has no
zero-free-region assumption.
[`vinogradovKorobov_unconditional`](https://github.com/ProofFleet/moltresearch/blob/ccde5842/Conjectures/C0002_erdos_discrepancy/src/TrackCStage5VKDischarge.lean#L303-L319)

The same proof even displays a closed witness.  With

\[
 M_1=\max(M,1),\qquad
 E=Q^2(M_1+Q)+15+\log8192+2\log2-\log(\delta/2),
\]

it takes

\[
\begin{split}
X_{\rm VK}=\max\{&3^{1/\delta},
e^{(2/\delta)\log2},Q(T+2),e^e,\\
&e^{1/\delta^2},e^{e^{e^E}}\}.
\end{split}
\]

Thus the analytic threshold is already explicit but extremely large: the last
term is triple exponential in a quantity containing `Q²(M+Q)`.  The present
public `t`-cut API hides that displayed witness behind an existential, which is
why the new leaf file Skolemizes it rather than pretending it is directly
computable from the old theorem.

Finally, the qualitative BCC wrapper already writes its working scale as one
nested maximum.  Its exact inputs and consequences are visible in
[`TrackCStage5BCCWrapper.lean`](https://github.com/ProofFleet/moltresearch/blob/ccde5842/Conjectures/C0002_erdos_discrepancy/src/TrackCStage5BCCWrapper.lean#L380-L412).

## 2. Conjectured and still open

The rate conjecture `D_f(x) ≫ log x` is not advanced to a theorem here.  Even
the much smaller `edpTripleLogRate` from A3 still depends on the three finite
assumption classes.

For this branch specifically, `FiniteBorweinChoiCoonsRateAssumption` remains
open.  A proof must do more than know that every parameter has some terminal
scale.  It must prove that the terminal scale selected from the finite
pretentious package lies below `edpAnalysisCutoff x`, and it must use second
moments only at indices covered by `FiniteSecondMomentBound`.  Neither fact
follows from the qualitative BCC instance.

No conjectural zero-free statement is being smuggled into the new API.  The
formal theorem corresponding to Tao's zero-free use has already been replaced
by an unconditional standard-axiom proof.  The remaining open obligations are
finite scheduling and localization, not an analytic zero-free hypothesis.

## 3. Our function-form package

### Audited constants

`StructuredThresholds.lean` defines

```text
structuredMertensError          = 1
structuredEulerTruncationError = 13
structuredZetaPretenseError    = 14
structuredRepulsionError       = 24
```

It proves wrappers for the three public estimates, so these names cannot drift
away from the underlying formal constants.  It also proves
`structuredZetaPretenseError_eq`, fixing `14 = 1 + 13` in the kernel.

### Function-form `t`-cut

`structuredTCutThreshold Q T B hQ hT hB δ hδ0 hδ1` is
`Classical.choose` applied once to the existing proved `t`-cut.  Its companion
theorem `structured_tcut_after_threshold` proves the entire quantified
specification at every `X` beyond that value.  In particular, the threshold is
uniform in the random sample `g`, the two moduli and characters, and the two
frequencies; it depends only on `(Q,T,B,δ)` and the range proofs.

This is function-form, but noncomputable.  That distinction matters.  A future
refactor could expose the closed `X_VK` above directly from
`TrackCStage5VKDischarge.lean`; A8 does not edit that non-deliverable file or
duplicate its long proof merely to change an API.

### Explicit terminal scale

For a real constant `A` and positive `δ`, define

\[
 L(A)=\max(1,\lceil e^A\rceil),\qquad
 R_\delta(A)=\left\lceil \max(A,1)^{1/\delta}\right\rceil.
\]

The new Lean theorems prove that `X ≥ L(A)` implies `A ≤ log X`, and that
`X ≥ Rδ(A)` implies `A ≤ X^δ`.

After the finite character sweep supplies:

* `Xstart`, the persistent-event starting scale;
* `Xpair`, the maximum of the per-character refutation thresholds;
* `Xzero`, the threshold excluding a modulus-zero certificate;
* `H`, the maximum selected window length;
* `T`, the sanitized frequency constant; and
* `XF2`, the function-form `t`-cut threshold,

the terminal scale is the closed maximum

\[
\begin{split}
X_* = \max\{&X_{\rm start},X_{\rm pair},X_{\rm zero},L(1),
L(4(H+1)^2),\\
&R_\delta(72(H+1)^3(T+1)),
R_\delta(X_{\rm start}+1),R_\delta(X_{\rm zero}+1),
3,\lceil X_{F2}\rceil\}.
\end{split}
\]

`StructuredScaleConditions` names the ten resulting obligations, and
`structuredTerminalScale_spec` proves all of them for every natural
`X ≥ X_*`.  `structuredTerminalScaleOfTCut` substitutes the proved
`structuredTCutThreshold` into this maximum.

This formula exactly mirrors the maximum in the existing BCC wrapper; it only
replaces its elementary existential log/power thresholds by closed functions.
It is therefore ready for A9 to make the one decisive comparison

```text
structuredTerminalScaleOfTCut ... ≤ edpAnalysisCutoff x.
```

## 4. What this audit rules out, and what A9 must do

The terminal-scale bottleneck is not a small omitted `O(1)`.  Even before the
per-character BCC refutation threshold is expanded, the proved `t`-cut contains
a triple exponential.  A9 must not infer that the current
`edpAnalysisCutoff x` dominates it merely because both sides are finite.

Two older witnesses are still passed as explicit inputs to the terminal
constructor: `Xpair` and `Xzero`.  Their constructors are private and
existential in `TrackCStage5BCCWrapper.lean`; A9 will need to Skolemize the
public underlying chain, or report that API boundary as its exact obstruction.
Likewise, converting a global zeta-weighted moment estimate into the finite
moment cap remains a localization question.  This A8 package neither assumes
nor claims those missing comparisons.

The clean next step is therefore mechanical in shape but mathematically
substantial: build the finite character sweep, instantiate the inputs above,
and prove the terminal maximum lies within the common cutoff.  If the stated
cutoff cannot dominate the extracted witnesses, the rate schedule must be
recalibrated rather than replacing the comparison by a qualitative
“sufficiently large” assertion.

