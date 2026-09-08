# Problem Card: Erdős #1144 — large fluctuations of random completely multiplicative functions — OPEN

Status: active (opened 2026-09-08). Research card. **2026-09-08: the problem page carries a full Lean proof claim (saasom/Erdos1144 v1.0.0, submitted 2026-09-06) that survived our D1 audit; the page still says OPEN pending review. The card's near-term goal was independent verification (D3v): done 2026-09-08, verdict *verified* as a reproducible build and statement comparison. D4 (proof-idea audit, twenty referee questions) and D5 (prepared formal-conjectures statement) are merged; the card's items are complete. External steps — a comment on the proof-claim thread, a formal-conjectures submission — require the operator's go-ahead and the public snapshot repository.** Exploratory allocation.

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

- [x] D1: Literature memo — `Problems/erdos1144_literature.md`: Wintner 1944; Halász 1983; Lau–Tenenbaum–Wu; Harper (the almost-sure upper bounds and the "better than squareroot cancellation" typical size `√N/(log log N)^{1/4}`, and his Ω-results / large fluctuations); Atherfold (At25) exact statement for this model; Angelo–Xu (2026, weighted sums) exact statements; the proof claim on the problem page (what it claims, whether it survives a careful read); which results are for the squarefree-supported model vs the completely multiplicative one and what transfers. Closing section "what is known about lower fluctuations and where each argument stops". Deliverables: `Problems/erdos1144_literature.md`.

- [x] D2: Numerics — `scripts/research/erdos1144_numerics.py` + `Problems/erdos1144_numerics.md`: simulate many independent `f` up to `N = 10^7` (sieve the primes, sample signs, accumulate partial sums), record `max_{N' ≤ N} S(N')/√N'` and `min`, the empirical distribution of `S(N)/√N` at fixed `N`, and the growth of the running maximum with `log log N`; compare with the `(log log N)^{1/4}` typical scale and with Atherfold's bound. Reproducible with fixed seeds. Deliverables: `scripts/research/erdos1144_numerics.py`, `Problems/erdos1144_numerics.md`.

- [x] D3: Approach memo and reduction (after: D0) — **read `Problems/erdos1144_literature.md` §4 first: a full Lean proof claim for exactly this statement (saasom/Erdos1144 v1.0.0, 2026-09-06) exists and survived D1's statement/axiom audit; an approach memo must position itself relative to that claim rather than start from zero** — `Problems/erdos1144_approach.md` + `Conjectures/C0006_erdos1144_random_mult/src/Reduction.lean`: a route to `Erdos1144` (decomposition by prime-factor ranges to expose independence; a lower bound for positive maxima over blocks of scales; a Borel–Cantelli / recurrence argument), as a DAG of precise lemma statements, each a `*Assumption` class citing the memo, with `erdos1144_of_assumptions : [classes] → Erdos1144` proved; Phase-2 items with `after:` edges. Known / conjectured / our idea separated. Deliverables: `Problems/erdos1144_approach.md`, `Conjectures/C0006_erdos1144_random_mult/src/Reduction.lean`.

- [x] D3v: Independent verification of the live proof claim (after: D1) **(merged: verdict *verified*, narrowly — the pinned v1.0.0 source rebuilt completely on this aarch64 host (605 source hashes matched, 8,919 jobs, an aarch64 `leantar` from a newer toolchain unpacking the pinned cache), the rebuilt endpoint depends on `[propext, Classical.choice, Quot.sound]`, and the term-by-term comparison found representation differences only, no target mismatch; this is a reproducible build plus statement comparison, not a mathematical review)** — a full local rebuild of `saasom/Erdos1144` at tag `v1.0.0` (commit `a0050daf`) on an architecture-matched toolchain (D1 could not decompress the Mathlib cache on this aarch64 host because the pinned toolchain ships an x86-64 `leantar`; obtain or build a matching `leantar`, or run the rebuild in an x86-64 container), `#print axioms` of `Erdos.Problem1144.erdos1144` from the rebuilt oleans, and a term-by-term comparison of their definitions (`Omega`, `mu`, `eps`, `sfKernel`, `f`, `S`, `normSum`, `Erdos1144`) with ours in `Conjectures/C0006_erdos1144_random_mult/src/Statement.lean`, written as `Problems/erdos1144_verification.md`; conclude "verified" / "not reproduced" / "statement differs (how)". No claim about the mathematics beyond what the rebuild shows. Deliverables: `Problems/erdos1144_verification.md`, `scripts/research/erdos1144_verify.sh`.

- [x] D4: Proof-idea audit (after: D3v) — a human-readable account of the claimed proof's mathematics from `notes/1144/complete_proof.md` and the certificate route (`candidate_scheduledGaussianRobustCrossing_certificate`): the decomposition, where independence is used, how positive crossing mass under finite prime cylinders is obtained, and the cylinder-envelope density-gap closure; for each step, whether it is standard, new, or delicate, with the exact Lean declarations it corresponds to. No verdict beyond what a careful reader can justify; list the questions a referee would ask. Deliverables: `Problems/erdos1144_proof_audit.md`.

- [x] D5: Formal statement for formal-conjectures (after: D3v) **(merged: prepared, not submitted)** — prepare, but do not submit, a `FormalConjectures/ErdosProblems/1144.lean`-style statement file in their conventions (category `research open` until the site records the solution; AMS tags; docstring with the model distinction), derived from our D0 definitions, together with a memo mapping our definitions to it. External submission requires the operator's explicit go-ahead and must cite the public snapshot repository, not this one. Deliverables: `Conjectures/C0006_erdos1144_random_mult/formal_conjectures_1144.lean.txt`, `Problems/erdos1144_formal_conjectures.md`.

## 4. Milestones beyond Phase 1

M1 the model and its basic moment identities machine-checked (`E S(N)² = #{squarefree-free…}` — the exact identity is part of D0/D3);
M2 a one-sided fluctuation estimate `limsup S(N)/√N ≥ c > 0` a.s.; M3 `= +∞`.

## 5. References / links

- erdosproblems.com/1144 (and #520 for the squarefree-supported model); Atherfold [At25]; Harper, *Moments of random multiplicative
  functions I* (Forum Math. Pi 2020) and the earlier Ω-results; Angelo–Xu (2026).
