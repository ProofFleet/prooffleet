# Erdős #1144: prepared Formal Conjectures statement

Prepared on 2026-09-08 against
[`google-deepmind/formal-conjectures` commit `d33e35a5`](https://github.com/google-deepmind/formal-conjectures/tree/d33e35a5f45386a173b31159ae6598b1968bc463).
The proposal is
[`formal_conjectures_1144.lean.txt`](../Conjectures/C0006_erdos1144_random_mult/formal_conjectures_1144.lean.txt).
It has not been submitted outside this repository.

## Status: known, open, and proposed material

### Known and directly checked

- On 2026-09-08 the [Erdős Problems page for #1144](https://www.erdosproblems.com/1144)
  still displayed `OPEN`.  It asks about independent uniform signs at the
  primes, their completely multiplicative extension, and the almost-sure
  positive limsup of the normalized partial sums.
- Formal Conjectures says that `research open` means that no solution is yet
  accepted by the mathematical community.  Its current contribution guide
  also requires one category and at least one AMS subject on every problem
  statement; see the pinned
  [category and AMS guidance](https://github.com/google-deepmind/formal-conjectures/blob/d33e35a5f45386a173b31159ae6598b1968bc463/CONTRIBUTING.md#choosing-a-folder-and-category).
- The closest existing entry is
  [Erdős Problem 520](https://github.com/google-deepmind/formal-conjectures/blob/d33e35a5f45386a173b31159ae6598b1968bc463/FormalConjectures/ErdosProblems/520.lean).
  That file uses tags `AMS 11 60`, but its random multiplicative function is
  zero on nonsquarefree integers.  It is therefore not the model in #1144.
- Our D0 file
  [`Statement.lean`](../Conjectures/C0006_erdos1144_random_mult/src/Statement.lean)
  constructs the prime-indexed fair-coin product measure, proves that it is a
  probability measure, proves independence of the decoded prime signs, proves
  complete multiplicativity and sign-valuedness of the extension, and states
  #1144 in frequent-exceedance form.
- D3v independently rebuilt the public v1.0.0 proof claim and compared its
  endpoint statement with D0.  The narrow result is recorded in the
  [verification memo](erdos1144_verification.md).  The public artifact is
  [`saasom/Erdos1144` v1.0.0](https://github.com/saasom/Erdos1144/tree/v1.0.0).

### Open or not externally settled

- The proposition `Erdos1144.erdos_1144` is the open mathematical statement.
  This proposal contains no proof of it.
- The public Lean artifact is a proof claim whose source has been reproduced
  and whose endpoint has been compared, but the website has not recorded an
  accepted solution.  Accordingly, this proposal does not use a solved
  category and does not attach a `formal_proof` attribute.
- Acceptance of the proof's mathematics and any change to the external status
  belong to mathematical referees and the maintainers of the two public
  problem collections.

### Our adaptation choices

- Use a concrete probability space `Nat.Primes → Bool`, rather than quantify
  over an abstract random-function structure.  This makes the intended law
  canonical and stays closest to the machine-checked D0 construction.
- Decode `true` as `+1` and `false` as `-1`, then extend through
  `Nat.factorization`.  The extension therefore keeps every prime-power
  contribution.
- State divergence by frequent exceedance of every real threshold.  This is
  the D0 formulation of the one-sided infinite limsup and avoids choosing an
  extended-real limsup representation in the external file.
- Include the public proof snapshot as a reference while retaining category
  `research open`.  No private repository is offered as evidence.
- Follow this repository's no-placeholder rule by recording the open
  declaration as an attributed `def : Prop`.  Formal Conjectures normally
  wraps an English yes/no question as a theorem using its `answer` elaborator.
  Converting to that wrapper is an external-integration step, deliberately
  deferred until the operator authorizes a submission and upstream confirms
  the desired status treatment.  The proposition inside the wrapper must
  remain exactly `Erdos1144.erdos_1144`.

## Definition-by-definition map

| D0 declaration | Prepared declaration | Relationship |
|---|---|---|
| `MoltResearch.Ω` | `Erdos1144.Omega` | Both are `Nat.Primes → Bool`; only the name changes to avoid a global Unicode identifier in the external namespace. |
| `MoltResearch.fairCoin` | `Erdos1144.fairCoin` | Identical definition: `PMF.uniformOfFintype Bool` converted to a measure. |
| `MoltResearch.randomCMMeasure` | `Erdos1144.randomCMMeasure` | Identical `Measure.infinitePi` product indexed by `Nat.Primes`. |
| `MoltResearch.primeSign` | `Erdos1144.primeSign` | Same sign convention.  The proposal expands the local helper `boolToSign` as an `if`, removing a MoltResearch-only dependency. |
| `MoltResearch.randomCM` | `Erdos1144.randomCM` | Identical product over `Nat.factorization`; values are integers and all prime exponents are retained. |
| `MoltResearch.partialSum` | `Erdos1144.partialSum` | Identical sum over `Finset.Icc 1 N`, so the junk value at `0` never contributes. |
| `MoltResearch.Erdos1144` | `Erdos1144.erdos_1144` | Identical frequent-exceedance proposition under the corresponding concrete product measure. |

The proposal retains D0's two probability-measure instances but omits its
construction theorems because they are not needed to parse the conjecture.
Those theorems are useful validation of the definitions, not extra hypotheses
in the statement.

## Why this is not Problem 520 or a Steinhaus statement

For a sampled prime sign `epsilon_p`, complete multiplicativity gives

\[
  f(p^k)=\epsilon_p^k\in\{-1,1\}
\]

for every `k`.  By contrast, the squarefree-supported model in the current
Formal Conjectures Problem 520 file sets `f(n)=0` whenever `n` is not
squarefree.  The two partial sums therefore differ already at `p^2`.  The
Steinhaus model also remains separate: it samples each prime on the complex
unit circle, not from two real signs.  The prepared declaration states all
three distinctions in its docstring because literature about one model does
not automatically transfer to another.

## Statement and metadata choices

- **Folder and name:** the intended external path is
  `FormalConjectures/ErdosProblems/1144.lean`, matching the source collection
  and the neighboring numeric filenames.
- **Namespace and declaration:** `namespace Erdos1144` and `erdos_1144`,
  matching existing Erdős entries.
- **Category:** `research open`, because the live source page remains open and
  Formal Conjectures defines “solved” by expert acceptance, not merely by the
  existence of a formal artifact.
- **AMS subjects:** `11` (number theory) and `60` (probability), in sorted
  order.  These are also the tags used by the related Problem 520 entry.
- **Question semantics:** the proposition is positive, one-sided, normalized
  by `sqrt N`, almost sure, and cofinal in `N`.  Large negative fluctuations
  or a single large positive value do not satisfy it.
- **References:** the live Erdős Problems page and the public tagged proof
  snapshot are the only references embedded in the prepared source.

## Checks before any external submission

External submission is outside D5 and requires explicit operator approval.
If that approval is given later, the submitter should:

1. refresh the upstream default branch and confirm that `1144.lean` is still
   absent;
2. recheck the status on erdosproblems.com and resolve with maintainers whether
   the public proof claim has become accepted;
3. preserve the exact completely multiplicative model and the one-sided
   frequent-exceedance proposition;
4. convert the attributed proposition to the then-current open-question
   wrapper without changing its mathematical content;
5. typecheck on Formal Conjectures' pinned Lean/Mathlib release and run its
   linters; and
6. cite `saasom/Erdos1144` v1.0.0 (or a later public archival snapshot), never
   this private worktree, when discussing the formal proof claim.

No issue, branch, pull request, or comment has been created in the external
repository as part of this work.
