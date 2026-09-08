# Problem Card: Erdős #177 — balancing every arithmetic progression with a step-dependent bound — OPEN

Status: active (opened 2026-09-08). Research card: the target is an **open problem**; §1 rules apply. Main project of the four.

## 0. One-line pitch

Find the slowest-growing `h(d)` for which some `f : ℕ → {−1, 1}` satisfies `|∑_{j<L} f(a + j d)| ≤ h(d)` for **every** start `a`, length
`L` and step `d ≥ 1` (erdosproblems.com/177; Er73, ErGr79, ErGr80). Known: Cantor–Erdős–Schreiber–Straus `h(d) ≪ d!`; van der
Waerden forces `h(d) → ∞`; Roth's discrepancy lower bound gives `h(d) ≫ d^{1/2}`; **Beck (2017)** achieves `h(d) ≤ d^{8+ε}` for every
`ε > 0` by infinite-dimensional vector balancing. The gap between `1/2` and `8` is the problem; **any strict improvement of Beck's
exponent is a research result**. Relation to EDP: EDP forbids one constant bounding all *homogeneous* sums; here the bound may grow
with the step but must be independent of the length.

## 1. Rules for this card

As `Problems/edp_rate.md` §1, with branch prefix `rc/`, metadata `Card: Problems/erdos177_ap_discrepancy.md`, `Track: N/A`,
`Checklist item: <verbatim>`. No `sorry` anywhere; open statements are `def … : Prop`; strategies are conditional theorems over
`*Assumption` classes; memos separate known / conjectured / our idea; no claim of a bound without the pinned Lean theorem.

## 2. What the tree supplies, and one deduction that is free

- Sign sequences, progression sums and their shift/normal-form calculus (`MoltResearch/Discrepancy/Basic.lean`, `apSum`,
  `apSumOffset`, `apSumFrom`, the `_shift_add` lemmas) — the bookkeeping of "every start, every length, every step".
- **A completely multiplicative sign sequence cannot be the construction**: for such `f`, `d = 1` already forces bounded partial
  sums `∑_{k ≤ L} f(k)`, contradicting the multiplicative case of EDP (`erdos_discrepancy_unconditional` with `apSum f d m = f(d)·∑_{k≤m} f(k)`).
  This is provable today from the tree and belongs in C0 as a lemma; it removes the most tempting search direction.
- Exponential sums / Fourier machinery (`ExpSums.lean`, Roth-type arguments) for the lower-bound side; nothing yet for
  balancing/partial-colouring arguments (Beck's side) — that is the new ingredient.

## 3. Decomposition — Phase 1 (four independent items; Phase 2 is written after C3)

- [x] C0: Formal statement — `Conjectures/C0005_erdos177_ap/src/Statement.lean`: `def APDiscrepancyBoundedBy (f : ℕ → ℤ) (h : ℕ → ℝ) : Prop := ∀ a L d : ℕ, 0 < d → |(∑ j ∈ Finset.range L, f (a + j * d) : ℤ)| ≤ h d` (state it with `(… : ℝ)` casts as convenient), `def Erdos177Achievable (h : ℕ → ℝ) : Prop := ∃ f, IsSignSequence f ∧ APDiscrepancyBoundedBy f h`, `def Erdos177Exponent (α : ℝ) : Prop := ∃ C : ℝ, Erdos177Achievable (fun d => C * (d : ℝ) ^ α)`; Beck's theorem and Roth's bound recorded as `def`s of the shape "for every ε, `Erdos177Exponent (8 + ε)`" and "no `f` achieves `c·d^{1/2}`" (both are theorems of the literature, stated here as Props, not proved); the free deduction of §2 **proved**: `not_achievable_of_completelyMultiplicative`. Docstrings cite the sources. Deliverables: `Conjectures/C0005_erdos177_ap/src/Statement.lean`.

- [ ] C1: Literature memo — `Problems/erdos177_literature.md`: the Erdős sources; Cantor–Erdős–Schreiber–Straus (`d!`); Roth 1964 (the `d^{1/2}` lower bound, with the exact statement used and how `h(d) ≫ d^{1/2}` follows); **Beck's paper** (find it: the exact statement, the vector-balancing framework, a reconstruction of the argument at the level of lemmas, and a precise account of **where each factor of the exponent 8 is lost**); related balancing results (Spencer's six standard deviations, Banaszczyk's vector balancing, Matoušek–Spencer for arithmetic progressions in `[N]`, the Lovett–Meka / Bansal algorithmic partial colouring) and whether any of them improves a step in Beck's chain; known constructions with small `h(d)` for small `d`. Cited; closing section "where the exponent could move". Deliverables: `Problems/erdos177_literature.md`.

- [x] C2: Numerics — `scripts/research/erdos177_numerics.py` + `Problems/erdos177_numerics.md`: for `N` up to a few thousand and steps `d ≤ D`, compute (SAT/ILP or local search) sign sequences on `[1, N]` minimizing `max_{d ≤ D} max_{a,L} |∑_{j<L} f(a+jd)| / d^α` for candidate `α`, report the best achievable `h(d)` profile for small `d` (is `h(d) ≈ d^{1/2}` attainable on finite ranges? does the finite optimum degrade with `N`?), and test structured candidates (Thue–Morse-type, Rudin–Shapiro, block constructions, Beck-style random balancing). Reproducible. Deliverables: `scripts/research/erdos177_numerics.py`, `Problems/erdos177_numerics.md`.

- [ ] C3: Approach memo and reduction (after: C0) — `Problems/erdos177_approach.md` + `Conjectures/C0005_erdos177_ap/src/Reduction.lean`: a candidate route to `Erdos177Exponent α` for some `α < 8` (a sharpened balancing lemma exploiting progression structure, or a construction valid for all `L` and `d`), written as a DAG of precise lemma statements, each a `*Assumption` class citing the memo, with `erdos177Exponent_of_assumptions : [classes] → Erdos177Exponent α` proved; the lemmas that are outright provable, proved; Phase-2 items with `after:` edges. Known / conjectured / our idea separated. Deliverables: `Problems/erdos177_approach.md`, `Conjectures/C0005_erdos177_ap/src/Reduction.lean`.

## 4. Milestones beyond Phase 1

M1 Beck's `d^{8+ε}` machine-checked (a known theorem; large); M2 **any exponent `α < 8`**; M3 the lower bound `d^{1/2}` machine-checked;
M4 the truth.

## 5. References / links

- erdosproblems.com/177; Beck, the `d^{8+ε}` paper (to be located in C1); Roth, *Remark concerning integer sequences*, Acta Arith. 9 (1964).
