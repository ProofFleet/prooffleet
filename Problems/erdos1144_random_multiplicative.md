# Problem Card: Erdős #1144 — large fluctuations of random completely multiplicative functions — OPEN

Status: active (opened 2026-09-08). Research card: the target is an **open problem**; §1 rules apply. Exploratory allocation.

## 0. One-line pitch

Let `f` be a random completely multiplicative function with independent uniform signs `f(p) ∈ {−1, 1}` at the primes. Is
`limsup_{N→∞} (∑_{m ≤ N} f(m)) / √N = +∞` with probability 1? (erdosproblems.com/1144; Va99 1.11.) Known: Atherfold (At25) proved
`∑_{m ≤ N} f(m) ≪ N^{1/2} (log N)^{1+o(1)}` almost surely; the page records one proof claim (to be examined, not believed). The model
must not be confused with the *Rademacher* model that vanishes on non-squarefree integers (problem #520) or the Steinhaus model;
results for those need a justified transfer. The question is about **positive, √N-normalized, almost-sure** divergence, which is
strictly more than unbounded absolute partial sums.

## 1. Rules for this card

As `Problems/edp_rate.md` §1, with branch prefix `rd/`, metadata `Card: Problems/erdos1144_random_multiplicative.md`, `Track: N/A`,
`Checklist item: <verbatim>`. No `sorry` anywhere; open statements are `def … : Prop`; strategies are conditional theorems over
`*Assumption` classes; memos separate known / conjectured / our idea; no claim without the pinned Lean theorem.

## 2. What the tree supplies

- `StochasticMultiplicative μ` and `sndMomentPartialSum` (Track C, `TrackCStage5*`), with Tao's Theorem 1.8 available unconditionally
  modulo one `haveI` (`theorem18_of_sliceMeanSquareA2 sliceMeanSquareA2`): the second moment of the partial sums of a stochastic
  completely multiplicative function is unbounded. That is the tree's closest statement; it is about moments, not almost-sure limsups.
- Multiplicative-function analysis: Halász (`HalaszComplex.lean`, `HalaszEuler.lean`), pretentious distance, Dirichlet-polynomial
  mean values, Mertens, Rankin — the analytic side of Harper-type arguments.
- Mathlib (pinned 2026-02): `MeasureTheory.Measure.infinitePi` / Ionescu-Tulcea kernels for the countable product of Rademacher
  laws (check the exact names available at the pin).

## 3. Decomposition — Phase 1 (four independent items; Phase 2 is written after D3)

- [x] D0: Formal statement — `Conjectures/C0006_erdos1144_random_mult/src/Statement.lean`: the probability space `Ω := Nat.Primes → Bool` (or `→ ℤˣ`) with the product of fair coin measures (name the Mathlib construction used and prove it is a probability measure), `def randomCM (ω : Ω) : ℕ → ℤ` the completely multiplicative extension (via `Nat.factorization`), proved: `randomCM ω` is completely multiplicative and `±1`-valued, `def partialSum (ω) (N)`, and `def Erdos1144 : Prop := ∀ᵐ ω ∂μ, Filter.limsup (fun N => (partialSum ω N : ℝ) / Real.sqrt N) Filter.atTop = ⊤` (as an `EReal`/`ℝ≥0∞`-valued limsup, or the equivalent `∀ M, ∃ᶠ N, M ≤ …` form — pick one and prove the two equivalent if cheap); the Rademacher-on-squarefree and Steinhaus models as separate `def`s so the distinction is visible. Deliverables: `Conjectures/C0006_erdos1144_random_mult/src/Statement.lean`.

- [ ] D1: Literature memo — `Problems/erdos1144_literature.md`: Wintner 1944; Halász 1983; Lau–Tenenbaum–Wu; Harper (the almost-sure upper bounds and the "better than squareroot cancellation" typical size `√N/(log log N)^{1/4}`, and his Ω-results / large fluctuations); Atherfold (At25) exact statement for this model; Angelo–Xu (2026, weighted sums) exact statements; the proof claim on the problem page (what it claims, whether it survives a careful read); which results are for the squarefree-supported model vs the completely multiplicative one and what transfers. Closing section "what is known about lower fluctuations and where each argument stops". Deliverables: `Problems/erdos1144_literature.md`.

- [ ] D2: Numerics — `scripts/research/erdos1144_numerics.py` + `Problems/erdos1144_numerics.md`: simulate many independent `f` up to `N = 10^7` (sieve the primes, sample signs, accumulate partial sums), record `max_{N' ≤ N} S(N')/√N'` and `min`, the empirical distribution of `S(N)/√N` at fixed `N`, and the growth of the running maximum with `log log N`; compare with the `(log log N)^{1/4}` typical scale and with Atherfold's bound. Reproducible with fixed seeds. Deliverables: `scripts/research/erdos1144_numerics.py`, `Problems/erdos1144_numerics.md`.

- [ ] D3: Approach memo and reduction (after: D0) — `Problems/erdos1144_approach.md` + `Conjectures/C0006_erdos1144_random_mult/src/Reduction.lean`: a route to `Erdos1144` (decomposition by prime-factor ranges to expose independence; a lower bound for positive maxima over blocks of scales; a Borel–Cantelli / recurrence argument), as a DAG of precise lemma statements, each a `*Assumption` class citing the memo, with `erdos1144_of_assumptions : [classes] → Erdos1144` proved; Phase-2 items with `after:` edges. Known / conjectured / our idea separated. Deliverables: `Problems/erdos1144_approach.md`, `Conjectures/C0006_erdos1144_random_mult/src/Reduction.lean`.

## 4. Milestones beyond Phase 1

M1 the model and its basic moment identities machine-checked (`E S(N)² = #{squarefree-free…}` — the exact identity is part of D0/D3);
M2 a one-sided fluctuation estimate `limsup S(N)/√N ≥ c > 0` a.s.; M3 `= +∞`.

## 5. References / links

- erdosproblems.com/1144 (and #520 for the squarefree-supported model); Atherfold [At25]; Harper, *Moments of random multiplicative
  functions I* (Forum Math. Pi 2020) and the earlier Ω-results; Angelo–Xu (2026).
