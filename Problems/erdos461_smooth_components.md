# Problem Card: Erdős #461 — distinct smooth components in a short interval — OPEN

Status: active (opened 2026-09-08). Research card: the target is an **open problem**; see §1 for what a PR may and may not claim.

## 0. One-line pitch

For `t ≥ 2` let `s_t(n)` be the `t`-smooth component of `n` (the product of the prime powers `p^{v_p(n)}` with `p < t`), and let
`f(n, t)` be the number of distinct values of `s_t(m)` for `m ∈ (n, n + t]`. Erdős and Graham (ErGr80, p. 92) ask whether
`f(n, t) ≫ t` uniformly in `n` and `t`; they could show `f(n, t) ≫ t / log t`. (erdosproblems.com/461, tags: number theory,
primes; no formalized statement yet.)

## 1. Rules for this card

Identical to `Problems/edp_rate.md` §1 with branch prefix `rb/`, metadata `Card: Problems/erdos461_smooth_components.md`,
`Track: N/A`, `Checklist item: <verbatim>`. No `sorry` anywhere; open statements are `def … : Prop`; strategies are conditional
theorems over `*Assumption` classes; memos separate known / conjectured / our idea; no claim of a proof without the pinned Lean theorem.

## 2. Why this problem is near what the tree has

The tree's sieve layer — Brun's pure sieve on an interval (`BrunIntervalSieve.lean`), Selberg's Λ² sieve
(`TrackCStage5QuadrupleSieveProof.lean`, explicit constants), Chebyshev blocks, Mertens, Rankin's trick for smooth numbers
(`SmoothRankin.lean`) — is the toolkit of the `t / log t` bound and of any counting of `t`-rough or `t`-smooth integers in an
interval of length `t`. Leads to be checked, not believed: (i) the primes `p ∈ (t/2, t)` give `π(t) − π(t/2) ≫ t / log t` distinct
values (each such `p` has a multiple in the interval whose smooth part it divides, and two such multiples cannot share a smooth part);
(ii) every `s ∈ [t/2, t)` is `t`-smooth and has a multiple `m_s` in the interval with `s ∣ s_t(m_s)`, and a smooth part `S ≥ t/2` is
shared by at most two elements of an interval of length `t`, so `f(n, t)` is at least half the number of **distinct** multiples one
can choose — a Hall-type matching question about divisors of the interval's elements in a dyadic range (the Erdős–Hooley `Δ` function
governs the worst case); a 2026 arXiv paper on "matching integers to distinct multiples" (arXiv:2603.28636) may be directly relevant
and must be read; (iii) the seven comments on the problem page.

## 3. Decomposition — Phase 1 (four independent items; Phase 2 is written after B3)

- [x] B0: Formal statement — `Conjectures/C0004_erdos461_smooth/src/Statement.lean`: `def smoothPart (t n : ℕ) : ℕ` (product over the prime factors `p < t` of `n` of `p ^ (n.factorization p)`; use `Nat.factorization`), `def smoothComponentCount (n t : ℕ) : ℕ := ((Finset.Ioc n (n + t)).image (smoothPart t)).card`, `def Erdos461 : Prop := ∃ c : ℝ, 0 < c ∧ ∀ n t : ℕ, 2 ≤ t → c * t ≤ smoothComponentCount n t`; proved sanity lemmas: `smoothPart_dvd`, `smoothPart` of a `t`-smooth number is itself, `smoothComponentCount n t ≤ t`, and the value for `n = 0` (`= t`, or `t − 1` if `t` is prime — state whichever is true and prove it). Docstrings cite ErGr80 and the problem page. Deliverables: `Conjectures/C0004_erdos461_smooth/src/Statement.lean`.

- [ ] B1: Literature memo **(blocked, draft #3730: no proof or precise source of the reported `t / log t` bound could be found; the naive prime injection is refuted by B2's `t = 8, n = 1255` example, so the claim in ErGr80 p. 92 currently has no verified argument)** — `Problems/erdos461_literature.md`: the Erdős–Graham source text, the `t / log t` argument reconstructed with a proof, the seven comments on erdosproblems.com/461 (fetch the page), the "matching integers to distinct multiples" paper arXiv:2603.28636 (exact statement, does it give a Hall-type lower bound usable here?), the Erdős–Hooley `Δ` function results relevant to divisors in a dyadic range (Ford–Green–Koukoulopoulos 2023, Hooley), and smooth/rough numbers in short intervals (Friedlander–Granville–style results). Each claim cited; a closing section "what each approach gives and where it stops". Deliverables: `Problems/erdos461_literature.md`.

- [x] B2: Numerics — `scripts/research/erdos461_numerics.py` + `Problems/erdos461_numerics.md`: for `t ≤ 40`, minimize `f(n, t)` over `n` (exact search over `n` modulo the relevant lcm where feasible, randomized and structured search — `n ≡ 0` or `−1` or `−t/2` modulo `lcm(1..t)` and modulo products of primes — otherwise), report `min_n f(n, t) / t`, the minimizing `n`, and which residues collide; test the two leads of §2 numerically (how many distinct multiples can be chosen, how often a smooth part is shared by two elements). Reproducible. Deliverables: `scripts/research/erdos461_numerics.py`, `Problems/erdos461_numerics.md`.

- [x] B3: Approach memo and reduction (after: B0) — `Problems/erdos461_approach.md` + `Conjectures/C0004_erdos461_smooth/src/Reduction.lean`: the sharpest proof strategy found (the matching route of §2(ii), or better), written as a DAG of precise lemma statements, each stated in Lean as a `*Assumption` class citing the memo, with the conditional theorem `erdos461_of_assumptions : [classes] → Erdos461` proved; the `at most two elements share a smooth part ≥ t/2` lemma proved outright if it is as easy as it looks; Phase-2 items listed with `after:` edges. Known / conjectured / our idea separated. Deliverables: `Problems/erdos461_approach.md`, `Conjectures/C0004_erdos461_smooth/src/Reduction.lean`.

## 3b. Decomposition — Phase 2 (written 2026-09-08 from the B3 memo `Problems/erdos461_approach.md`; same rules)

The B3 reduction isolates one interface, `ProportionalComponentMatchingAssumption` (a positive-proportion partial matching into
distinct smooth-component values), and proves `erdos461_of_assumptions` from it. The numerics (B2) refuted both matching leads of
§2 at the actual minimizers (`t = 8, n = 1255`: primes 5 and 7 share the single multiple 1260; highly divisible centres collapse the
dyadic-divisor matching). Phase 2 attacks the interface honestly: obstructions first, then a refined interface, then the sieve.

- [x] B4: Component-graph foundations (after: B3) — in a new leaf `Conjectures/C0004_erdos461_smooth/src/ComponentGraph.lean`: a positive `d < t` dividing a positive `m` divides `smoothPart t m`; every `d ∈ L_t` (the left set of the B3 memo) has a component neighbour; the finite defect-Hall criterion for `ComponentMatching` stated and proved. Deliverables: `Conjectures/C0004_erdos461_smooth/src/ComponentGraph.lean`.

- [ ] B5: Known-bound route (after: B3) — first decide whether the Erdős–Graham `t / log t` claim (ErGr80 p. 92, stated without proof; B1 found none) is provable: reconstruct a proof or record a precise obstruction; if provable, the argument as precise Lean lemmas that avoid the false prime injection, in `Conjectures/C0004_erdos461_smooth/src/KnownBound.lean`, proved as far as the tree's Chebyshev/Brun inputs allow; the smallest missing sieve input, if any, stated as a `*Assumption` class citing `Problems/erdos461_known_bound.md`. Deliverables: `Conjectures/C0004_erdos461_smooth/src/KnownBound.lean`, `Problems/erdos461_known_bound.md`.

- [x] B6: Matching obstructions (after: B2, B3) — the `t = 8, n = 1255` counterexample and the highly-divisible-centre family formalized in `Conjectures/C0004_erdos461_smooth/src/Obstructions.lean` (decidable instances, `decide`/`norm_num` proofs), their exact defect profiles computed by `scripts/research/erdos461_numerics.py` (extend it) and recorded in `Problems/erdos461_obstructions.md`, with the conclusion which left sets remain viable. Deliverables: `Conjectures/C0004_erdos461_smooth/src/Obstructions.lean`, `Problems/erdos461_obstructions.md`, `scripts/research/erdos461_numerics.py`.

- [ ] B7: Expansion interface refinement (after: B4, B6) — an explicit multiscale neighbourhood inequality stated as a `*Assumption` class in `Conjectures/C0004_erdos461_smooth/src/Expansion.lean`, with a machine-checked proof that it implies `ProportionalComponentMatchingAssumption`; if the inequality is false on a B6 obstruction, keep the exact counterexample in `Problems/erdos461_expansion.md` and revise the interface rather than weaken any theorem. Deliverables: `Conjectures/C0004_erdos461_smooth/src/Expansion.lean`, `Problems/erdos461_expansion.md`.

- [ ] B8: Delta/sieve attack (after: B1, B7) — whether divisor-window bounds (Erdős–Hooley `Δ`, Ford–Green–Koukoulopoulos) plus the interval sieve control the total defect after exceptional high-divisor components are removed; a rigorous no-route memo is an acceptable outcome. Any proved lemma goes in `Conjectures/C0004_erdos461_smooth/src/DeltaSieve.lean`. Deliverables: `Problems/erdos461_delta_sieve.md`, `Conjectures/C0004_erdos461_smooth/src/DeltaSieve.lean`.

- [ ] B9: Milestone decision (after: B5, B8) — either discharge the refined matching assumption (instance + audit pin in `Conjectures/C0004_erdos461_smooth/src/Discharge.lean`), or land the machine-checked `t / log t` theorem and a precise statement of the remaining uniform obstruction in `Problems/erdos461_status.md`. Deliverables: `Conjectures/C0004_erdos461_smooth/src/Discharge.lean`, `Problems/erdos461_status.md`.

## 4. Milestones beyond Phase 1

M1 `f(n, t) ≫ t / log t` machine-checked (the known bound, from the tree's Chebyshev block); M2 any improvement of the exponent of
`log t`; M3 `f(n, t) ≫ t`.

## 5. References / links

- erdosproblems.com/461; Erdős–Graham, *Old and new problems and results in combinatorial number theory* (1980), p. 92.
- arXiv:2603.28636 (matching integers to distinct multiples); Ford–Green–Koukoulopoulos, *Equal sums in random sets and the
  concentration of divisors* (Invent. Math. 2023) for `Δ`.
