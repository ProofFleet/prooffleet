# Four open Erdős problems, one day of concurrent agents — run report (2026-09-08)

Cards: `Problems/edp_rate.md`, `Problems/erdos461_smooth_components.md`, `Problems/erdos177_ap_discrepancy.md`,
`Problems/erdos1144_random_multiplicative.md`. This report records what the run produced, what it refuted, and what it did not
do. Every mathematical claim below is either a Lean theorem on `main` (named) or explicitly marked as a memo finding.

## 1. Setup

Four research cards, each with four Phase-1 items (a formal statement as a `Prop` with no `sorry`, a literature memo, reproducible
numerics, an approach memo with a conditional reduction over `*Assumption` classes) and, after the approach memo, a Phase 2 written
by the conductor from the memo's dependency graph. Eight Codex agents (`gpt-5.6-sol`, reasoning effort `xhigh`), two per card,
launched 01:59 local with a generic prompt (claim by draft PR, edit only the item's deliverables, stop and report when blocked,
never claim a proof without the pinned theorem). The conductor merged on green, ticked immediately after every merge, wrote Phase-2
items, and relaunched agents as dependencies opened. The run was interrupted once by a full disk (five agents lost mid-item, resumed
from their claims) and paused once by the operator.

## 2. Outcomes by card

**EDP growth rate (Erdős's `≫ log x` conjecture).** The formal statement (`HasDiscrepancyRateBy`, the conjecture, McNamara's shape,
the multiplicative case); the exact constant `1/(2 log 3) = 1/log 9` of the sign-flipped ternary modified character, which caps any
universal constant, with numerics to `10^7` agreeing (A1, A2); McNamara's rectangle reparameterized to Erdős's product form gives only
`(log log log X)^{1/484}`. The reduction (A3) isolates three finite interfaces and proves a concrete conditional rate
`10^-7 · (log log log x)^{1/500}`. Then: the exact source budget of the spectral window (A4, primorial-sized); the finite Fourier
interface **discharged** (`finiteFourierReductionAssumption_budgetSafe`, A5′) after A5 proved the original schedule's failure is
attained; function-form Elliott and structured thresholds (A6, A8). Both finite packages then blocked on the same defect of the A3
interface at the cutoff's endpoint — Finding A-1, kernel-checked in A7 and A9 — and A3′ repaired the interface (policy-indexed classes,
window slack, capped pretentious parameters) with the rate theorem re-proved. A7′, A9′ and the calibrated rate theorem (A10) are the
remaining items. No unconditional rate is claimed yet.

**Erdős #461 (smooth components in a short interval).** Statement and sanity lemmas (B0: the count at `n = 0` is `t`, or `t − 1` for
prime `t`); exact minima through `t = 11` (`⌊t/2⌋ + 1`) and sampled minima through `t = 40` (B2); both matching leads on the card
refuted at the minimizers (B2, B6, machine-checked: primes 5 and 7 share the single multiple 1260 at `t = 8, n = 1255`); the
`≤ 2` per-fibre lemma proved outright (B3); the finite defect-Hall criterion (B4); the reported `t / log t` bound has **no proof or
citation** in Erdős–Graham (B1 blocked, B5), and is proved equivalent to a simultaneous fibre-loss inequality
(`erdos461LogBound_iff_simultaneousFiberLossAssumption`, B9); the conjecture reduced to a uniform `⌈t/4⌉` component matching,
equivalent to the refined multiscale interface (B7, B9); the Δ/sieve route closed by a machine-checked counterexample (pruning
high-degree components breaks expansion at `t = 38`, B8). Neither bound is proved.

**Erdős #177 (balancing every progression, step-dependent bound).** Statement, Beck's and Roth's results as Props, and the proved
exclusion of completely multiplicative sequences via the EDP theorem (C0); numerics showing periodic and automatic sequences resonate
with particular steps while randomized balancing does not (C2, C5); the residue-prefix normalization with a factor-2 equivalence to
the interval form (C3); the compactness passage **discharged** unconditionally (`residuePrefixCompactnessAssumption`, C4); the
balancing lemma as a rigorous no-route memo with the Lovett–Meka entropy obstruction at the step-1 rows (C6); and the exact
equivalence `erdos177Exponent_iff_finiteResiduePrefixBalancing` (C7). Beck's source chapter could not be obtained (C1 blocked). No
exponent below 8 is claimed.

**Erdős #1144 (random completely multiplicative fluctuations).** Statement with the countable product measure, independence, and the
two alternative models kept distinct (D0); the literature memo found a full Lean proof claim submitted two days earlier
(saasom/Erdos1144 v1.0.0) and audited it (D1); numerics with the exact identity `E S(N) = ⌊√N⌋` (D2); an independent route as a
conditional reduction, positioned relative to the claim (D3); **the claim reproduced**: full rebuild on this host, standard axioms,
term-by-term statement comparison with no target mismatch (D3v, `Problems/erdos1144_verification.md`); a proof-idea audit with twenty
referee questions (D4); a formal-conjectures statement prepared, not submitted (D5). External steps are the operator's call.

## 3. Process numbers

| measure | value |
|---|---|
| research PRs merged (agent-authored) | 35 |
| conductor bookkeeping PRs | 27 |
| wall-clock, first launch → last research merge | 01:59 → 05:36 local |
| merge conflicts in agent PRs | 0 |
| agent PRs whose squash touched files outside the item's deliverables | 0 (verified per merge) |
| first-submission CI pass on ready PRs | 35 / 35 |
| items ending as rigorous no-route or obstruction memos | 7 (A5, A7, A9, B8, C6, B1, C1) |
| card defects caught by agents | 4 (B leads refuted; t/log t unsourced; A3 endpoint defect; C1 source) |
| interfaces discharged unconditionally | 2 (finite Fourier, #177 compactness) |
| exact equivalences proved | 3 (#177 exponent ⇔ balancing; #461 log bound ⇔ fibre loss; #461 expansion ⇔ quarter matching) |
| conductor errors | 2 (one squash deleted nine files, restored; two duplicate claims from delayed ticks, closed) |

## 4. What this shows and what it does not

It shows that the card-and-CI substrate carries genuine research work by concurrent agents: every item ended either as a pinned
theorem, a conditional theorem over a named interface, or a memo with an exact obstruction; agents refused to work around defects
in the cards four times; and the two design errors on the EDP-rate card were caught by two independent agents hitting the same wall
and reporting it precisely. It does not show a new theorem on any of the four problems. The honest summary of the mathematics is:
three exact reductions and two discharged interfaces, one third-party proof independently reproduced, and one "known" bound found
to be unsupported in the literature.

## 5. Open decisions for the operator

- Whether to post the #1144 reproduction on the problem page's proof-claim thread, and whether to submit the prepared statement
  file to formal-conjectures (both require the public snapshot repository for stable links).
- Beck's chapter for #177 (unblocks C1 and the exponent ledger).
- Whether to continue the EDP-rate card to A10 (the first machine-checked rate) after A7′/A9′.
