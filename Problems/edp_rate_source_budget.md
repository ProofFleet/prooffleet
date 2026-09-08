# Source-budget audit for the finite Fourier reduction

Research snapshot: 2026-09-08. This memo accompanies
[`SourceBudget.lean`](../Conjectures/C0003_edp_rate/src/SourceBudget.lean). It audits a
finite combinatorial step. It does **not** prove an Erdős-discrepancy rate or instantiate
any of the three assumption classes in
[`Reduction.lean`](../Conjectures/C0003_edp_rate/src/Reduction.lean).

## Result

Write

\[
  L=\lfloor\log_2 X\rfloor=\mathtt{Nat.log\ 2\ X},\qquad
  P_X=\{p\text{ prime}:p<X+1\}.
\]

For the exponent modulus `M` and window length `n`, the exact largest source product
queried at a wrap-free point is

\[
  \operatorname{SourceBudget}(X,M,n)
    =n\prod_{p\in P_X}p^{M-(L+1)}.                 \tag{1}
\]

The exponent uses natural-number subtraction. When `L < M`, equality in (1) is attained
by the group point whose every coordinate is `M - (L + 1)`. The Lean theorem
`spectralSourceBudget_isGreatest` proves this exact maximality. The theorem
`spectral_window_bound_of_sourceBudget` then reproduces the spectral conclusion while
assuming discrepancy only for `d * m ≤ SourceBudget(X,M,n)`, rather than for all
homogeneous progressions.

## 1. Known

### 1.1 Known from Tao's Fourier reduction

Tao's Section 2 evaluates the source sequence on a finite exponent group, separates
group points where adding the exponent vector of each `j ≤ X` does not wrap, and applies
the homogeneous-progression bound at the encoded dilation. Exceptional points receive
only the triangle-inequality bound `n ≤ X`. After square averaging, Tao chooses the
modulus so that, in the paper's exact words, **“M is sufficiently large depending on C,
X”**. Fourier expansion and Plancherel then produce the random completely multiplicative
model. [Tao, Section 2, pp. 9–10][Tao16]

The same section explicitly identifies compactness, not this finite construction, as the
noneffective passage. Footnote 4 says a quantitative proof should **“avoid this compactness
argument and work instead with truncated versions”**, while also controlling truncated
Euler-product errors later in the proof. [Tao, footnote 4, p. 9][Tao16]

Tao's paper takes a deliberately coarse wrap-free box, with prime exponents kept far
enough from the boundary using `M-X`. The formal tree sharpens this elementary part by
using the proved valuation bound `v_p(j) ≤ Nat.log 2 X` for `j ≤ X`.
[Tao, Section 2, pp. 9–10][Tao16]

### 1.2 Known from the formal tree

The following are existing Lean theorems on `main` at commit `ba5d172b`:

1. `dExp X a` is the product of `p^(a p).val` over the primes below `X+1`, and
   `dExp_pos` proves it is positive. [`DilationCover.lean`, lines 36–55][DilationCover]
2. `WrapFree X M a` means `(a p).val + Nat.log 2 X < M` for every prime coordinate.
   [`AveragedWindowBound.lean`, lines 34–39][AveragedWindowBound]
3. At a wrap-free point, `window_smoothEval_eq_apSum` identifies the group window with
   `apSum f (dExp X a) n`. [`AveragedWindowBound.lean`, lines 41–64][WindowEq]
4. `norm_window_smoothEval_le_of_wrapFree` invokes the global hypothesis at exactly
   `d = dExp X a` and `m = n`. There are no other calls to that hypothesis.
   [`AveragedWindowBound.lean`, lines 65–77][GlobalCall]
5. In `avg_normSq_window_smoothEval_le`, the good-point sum calls that norm lemma once.
   The bad-point sum uses only `IsSignSequence f`, the trivial norm bound, and the count
   of non-wrap-free points. [`AveragedWindowBound.lean`, lines 183–260][AverageProof]
6. `spectral_window_bound` itself is Plancherel followed by the averaged bound; it makes
   no further source-sequence query. [`SpectralWindowBound.lean`, lines 48–59][Spectral]

Thus the complete source-query call graph is

```text
spectral_window_bound
  └─ avg_normSq_window_smoothEval_le
       ├─ good a: norm_window_smoothEval_le_of_wrapFree
       │            └─ hB (dExp X a) n
       └─ bad a: IsSignSequence + triangle inequality (no hB call)
```

## 2. Derivation of the exact budget

Fix a wrap-free point `a`. For every `p ∈ P_X`, wrap-freeness says

\[
  (a_p.\mathrm{val})+L<M.
\]

All quantities are natural numbers, so

\[
  a_p.\mathrm{val}\le M-(L+1).
\]

Monotonicity of natural powers and finite products gives

\[
  dExp(X,a)=\prod_{p\in P_X}p^{a_p.\mathrm{val}}
  \le \prod_{p\in P_X}p^{M-(L+1)}.
\]

Multiplying by the requested length `n` proves the upper bound (1). If `L < M`, the
residue class of `M-(L+1)` has that value in `ZMod M`. Taking it in every coordinate is
wrap-free and makes every factor an equality. This also covers the empty-prime case: both
dilation products are `1`. No estimate about prime distribution is used in the Lean
proof.

## 3. Conjectured and still open

The Erdős rate conjecture remains the logarithmic lower bound stated in
[`edp_rate.md`](edp_rate.md). Nothing in this audit proves that conjecture.

For Phase 2, the still-open Fourier obligation is that a spectral construction can be
scheduled inside the outer product cutoff while supplying all moments through
`edpAnalysisCutoff x`. In particular, this PR does not prove
`FiniteFourierReductionAssumption`, does not declare an instance of it, and does not
claim that the present exponent-group construction has a viable schedule.

## 4. Our idea and what the audit changes

The new observation is that “local in the spectral window `n ≤ X`” is not local in the
source sequence. The encoded dilation contains one exponent for every prime up to `X`,
and each exponent can approach `M`. The exact budget (1) is therefore primorial-sized in
the exponent modulus.

This is more severe than the informal warning in the A3 approach memo. The existing
spectral proof requires

\[
  \#P_X\,L\,X^2\le M,
\]

while the source budget raises every prime in `P_X` to approximately that `M`. For the A3
choice `X = edpAnalysisCutoff x`, this points in the wrong direction: increasing `M` makes
wraparound rarer but makes the required source dilations much larger. This growth
comparison is our diagnosis, not a new Lean theorem and not a claim from Tao.

The useful output is the interface rather than a hidden optimism:

- `dExp_le_spectralDilationBudget` proves the dilation bound at each wrap-free point;
- `spectralSourceBudget_isGreatest` proves that the bound is sharp when `L < M`;
- `norm_window_smoothEval_le_of_sourceBudget` replaces the sole global-hypothesis call;
- `avg_normSq_window_smoothEval_le_of_sourceBudget` checks that bad points need no
  discrepancy premise; and
- `spectral_window_bound_of_sourceBudget` provides the same `B^2+1` spectral estimate
  from the finite budget premise.

## 5. Handoff to A5

A5 can use `spectral_window_bound_of_sourceBudget` without reopening the call audit. It
must prove, for every required `n`, that (1) lies below the outer cutoff `x`. If the A3
schedule cannot satisfy that inequality together with the modulus condition, the card
requires A5 to record the exact obstruction instead of silently appealing to global
bounded discrepancy.

The most plausible repair target is the finite Fourier construction itself: replace the
full exponent box, change how boundary points are paid for, or find a representation whose
encoded dilations grow much more slowly with `M`. Choosing a larger `M` alone cannot solve
the source-budget problem exposed here.

## References

[Tao16]: https://arxiv.org/pdf/1509.05363
[DilationCover]: https://github.com/ProofFleet/moltresearch/blob/ba5d172b/MoltResearch/Discrepancy/DilationCover.lean#L36-L55
[AveragedWindowBound]: https://github.com/ProofFleet/moltresearch/blob/ba5d172b/MoltResearch/Discrepancy/AveragedWindowBound.lean#L34-L39
[WindowEq]: https://github.com/ProofFleet/moltresearch/blob/ba5d172b/MoltResearch/Discrepancy/AveragedWindowBound.lean#L41-L64
[GlobalCall]: https://github.com/ProofFleet/moltresearch/blob/ba5d172b/MoltResearch/Discrepancy/AveragedWindowBound.lean#L65-L77
[AverageProof]: https://github.com/ProofFleet/moltresearch/blob/ba5d172b/MoltResearch/Discrepancy/AveragedWindowBound.lean#L183-L260
[Spectral]: https://github.com/ProofFleet/moltresearch/blob/ba5d172b/MoltResearch/Discrepancy/SpectralWindowBound.lean#L48-L59
