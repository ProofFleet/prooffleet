# Function-form Elliott thresholds and the finite van der Corput budget

Research snapshot: 2026-09-08.  This memo documents the A6 deliverable
[`ElliottThresholds.lean`](../Conjectures/C0003_edp_rate/src/ElliottThresholds.lean).
It is a threshold and dependency audit, not an unconditional quantitative Elliott theorem
and not an Erdős-discrepancy rate proof.

## Outcome

The Lean deliverable does three things.

1. `EDPRateElliottThresholdAssumption` is the function-form replacement for the existing
   existential interface.  It carries
   `threshold : ℕ → ℕ → ℝ → ℝ`, with arguments `(b₁,b₂,ε)`, and the Elliott estimate above
   that threshold.  It is a `Type`-valued class because it contains data.  There is a
   compatibility instance from this stronger class to
   `Tao2015.LogElliottNonasymptoticAssumption`, but deliberately no converse instance.
2. For a second-moment cap `C` and probability loss `ε`, the file defines

   ```text
   C'       = max C 1
   H        = max 1 ⌈8 C' / ε⌉₊
   η        = 1 / (8 H)
   A_vdC    = max(1, max_{1 ≤ h,h' ≤ H} threshold(h,h',η)).
   ```

   `edpElliott_bound_of_vdCThreshold` proves that the one value `A_vdC` serves every
   distinct shift pair in the finite van der Corput box.
3. The expectation and Markov steps are reproved from a moment bound only through a finite
   cutoff `L`.  The proof records the exact touched indices: a window based at `n` and of
   length `H` uses `sndMomentPartialSum G n` and
   `sndMomentPartialSum G (n + H)`.  On an Elliott window ending at `X`, the largest requested
   moment index is therefore `X + H`.

The formal theorem `mem_elliottWindow_moment_indices` pins the elementary index calculation,
and the two cutoff-local estimates require the single honest fit condition `X + H ≤ L`.

## Known

### From the literature

Tao's nonasymptotic two-point Elliott theorem assumes that the pretentiousness strength `A`
is sufficiently large as a function of the accuracy and affine data, and then bounds the
logarithmically averaged correlation by `ε log ω`.  The source's exact threshold wording is:
“A is sufficiently large depending on ε, a1, a2, b1, b2.”
[Tao, Theorem 1.3, p. 5][TaoElliottPDF]

The paper does not print that function.  Remark 1.4 says, exactly, “Our arguments are in
principle effective,” and continues that tracking the proof would give an explicit value.
Its footnote estimates roughly triple-exponential dependence on `1/ε` in the completely
multiplicative unit-circle model case.  [Tao, Remark 1.4 and footnote 2, pp. 5–6][TaoElliottPDF]

Tao's Erdős-discrepancy paper imports this as Theorem 1.10 and uses a van der Corput argument
to obtain Proposition 1.11: a stochastic completely multiplicative function with uniformly
bounded partial-sum second moments is usually pretentious at sufficiently large truncations.
[Tao, Theorem 1.10 and Proposition 1.11, pp. 5–6][TaoEDPPDF]

### From the formal tree

These are proved facts about the current repository, not new analytic claims.

- `Tao2015.LogElliottNonasymptoticAssumption.bound` returns
  `∃ A₀, ∀ A ≥ A₀, ...`; the threshold is not available as named data.
- `Tao2015.elliott_master` proves that existential statement conditional on
  `MatomakiRadziwillAssumption` and `PrimeQuadrupleCountAssumption`.  The entropy-decrement
  bookkeeping after its inputs is explicit, but `MatomakiRadziwillAssumption` itself returns
  existential `H₀` and `A₀` thresholds.
- `vanDerCorputAssumption_of_logElliottNonasymptotic` chooses one Elliott threshold per shift
  pair and takes their finite supremum.  Its parameter choices are exactly the `C'`, `H`,
  `η`, and `A_vdC` displayed above (apart from the harmless totalizing `max 1` on `H`).
- `windowSndMoment_le` expands
  `windowSumC g n H = apSumC g 1 (n+H) - apSumC g 1 n`.  Inspecting its proof shows that the
  global hypothesis `∀ m, sndMomentPartialSum G m ≤ C` is invoked only at `m=n` and `m=n+H`.
  The new local theorem `windowSndMoment_le_of_two_indices` makes that dependency part of the
  type.

## Conjectured or still open

The Erdős logarithmic rate remains conjectural.  Nothing in this deliverable proves any
unconditional rate.

The new `EDPRateElliottThresholdAssumption` has no instance.  Constructing its threshold
function from the analytic chain, with a growth estimate strong enough for rate calibration,
is still open in this formalization.  Classical choice applied to the old existential class
would manufacture a function syntactically, but it would expose no bound on that function and
would therefore not solve the finite scheduling problem.  This is why the Lean file provides
only the safe direction from function-form data to the old interface.

In particular, Tao's “effective in principle” remark does not justify a concrete triple
exponential formula without auditing every threshold in the entropy-decrement and
Matomäki–Radziwiłł inputs.

## Our idea and what the audit found

The function-form carrier follows the stale Track-Q design in PR #3022, but is narrowed to the
EDP-rate card and paired with the missing moment ledger.  The finite maximum over the `H²`
shift box removes the qualitative proof's local `choose A₀f` from the eventual A7 consumer:
once actual threshold data exists, the consumer can refer to one named value.

The moment ledger exposes a sharper obstruction than the approach memo recorded.  Let
`L = edpAnalysisCutoff x`.  `FiniteSecondMomentBound μ G x` supplies moments only for
`m ≤ L`, while the present A3 definition `FinitePersistentPretentious μ G x` asks for its
probability estimate at **every** `X ≤ L`.  The existing van der Corput proof at truncation
`X` needs the moment at `X + H`.  At the top endpoint `X=L`, this is unavailable for every
positive `H`.

Thus merely proving `X ≤ L` in A7 is insufficient.  Reusing the present proof requires

```text
X + edpVdCWindowLength C ε ≤ edpAnalysisCutoff x.
```

This can cover only a shortened interval ending at `L-H`, not the full interval required by
`FinitePersistentPretentious`.  Possible repairs are research choices, not results of A6:

- strengthen the Fourier package to supply moment slack through `L+H`;
- weaken the persistent interval to `X ≤ L-H` and verify that the structured branch consumes
  only that interval; or
- redesign the window argument and prove a scale-transfer lemma for pretentious events.

The first two choices change an A3 interface and are outside this item's deliverables.  A7
should not silently discharge the top endpoint with the old global-moment theorem.

## Reproduction

The complete file typechecks with:

```bash
~/.elan/bin/lake env lean Conjectures/C0003_edp_rate/src/ElliottThresholds.lean
```

The important reusable statements are:

- `edpElliott_bound_of_vdCThreshold` — one function-form threshold for every shift pair;
- `windowSndMoment_le_of_two_indices` — exact two-index window bound;
- `integral_sum_div_normSq_windowSumC_le_of_moment_cutoff` — finite expectation estimate;
- `prob_sum_div_normSq_windowSumC_le_of_moment_cutoff` — finite Markov estimate;
- `mem_elliottWindow_moment_indices` — largest touched index `X+H`;
- the two `integral_elliottWindow_*` / `prob_elliottWindow_*` specializations — the exact
  `X+H ≤ L` consumer shape.

## References

[TaoElliottPDF]: https://arxiv.org/pdf/1509.05422
[TaoEDPPDF]: https://arxiv.org/pdf/1509.05363
