# Erdős #1144: independent verification of the live proof claim

Verification snapshot: 2026-09-08.

## Conclusion

**Verdict: verified.**  On an aarch64 host I rebuilt the complete declared
target of [`saasom/Erdos1144` tag `v1.0.0`](https://github.com/saasom/Erdos1144/tree/v1.0.0),
at commit
[`a0050daf4bf4992355b5ab189ee9c75cd44795a3`](https://github.com/saasom/Erdos1144/commit/a0050daf4bf4992355b5ab189ee9c75cd44795a3),
from a state with no project `.lake/build` directory.  The build completed all
8,919 jobs, including `Erdos.Problem1144.Final`, and produced 605 project
`.olean` files.  A query against those rebuilt objects reports exactly

```text
'Erdos.Problem1144.candidate_scheduledGaussianRobustCrossing_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Erdos.Problem1144.erdos1144' depends on axioms: [propext, Classical.choice, Quot.sound]
Erdos.Problem1144.erdos1144 : Erdos.Problem1144.Erdos1144
```

The claim's definitions are not definitionally identical to ours: it adds
unused non-prime coin coordinates, works in `ℝ` instead of `ℤ`, represents
prime exponents by their parity, and shifts the normalized sequence by one.
The term-by-term comparison below shows that these differences preserve the
law of the random function and give an equivalent frequent-exceedance
statement.  I found no squarefree-model substitution, absolute-value
weakening, or quantifier change.

This verdict is deliberately narrow.  It independently reproduces what the
Lean build and kernel dependency query say; it is not an independent paper
proof or a claim that the 207,626-line mathematical development has received
expert review.

## Reproduced facts

These are direct observations from the pinned source, tools, and rebuilt
objects, rather than conjectures.

- `git rev-parse HEAD` returned the pinned claim commit above, and the checked
  out tag was `v1.0.0`.  The dependency checkout was Mathlib commit
  [`5450b53e5ddc75d46418fabb605edbf36bd0beb6`](https://github.com/leanprover-community/mathlib4/commit/5450b53e5ddc75d46418fabb605edbf36bd0beb6).
- All 605 entries in the tagged
  [`verification/source-snapshot.sha256`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/verification/source-snapshot.sha256)
  passed before the build.  `git status --short` in the claim checkout was
  empty.
- The host was `aarch64`.  Lean reported
  `4.30.0-rc2, aarch64-unknown-linux-gnu`, commit
  `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.  The cache was unpacked with
  the aarch64 `leantar 0.1.20` from the installed Lean `v4.33.0` toolchain,
  placed first on `PATH`; this avoids the x86-64 `leantar` packaged in the
  pinned Elan toolchain on this host.  The pinned aarch64 Lean archive is the
  official
  [`lean-4.30.0-rc2-linux_aarch64.tar.zst`](https://github.com/leanprover/lean4/releases/download/v4.30.0-rc2/lean-4.30.0-rc2-linux_aarch64.tar.zst).
- `lake exe cache get` reported 8,297 dependency files already decompressed.
  `lake build` then completed successfully with `8919 jobs`.  The exact
  reproducible procedure and the literal resumed-run commands are in
  [`scripts/research/erdos1144_verify.sh`](../scripts/research/erdos1144_verify.sh).
- `lake env lean Audit.lean` was run only after that build.  The tagged
  `scripts/check_axioms.py` accepted its fresh output and printed: “Both
  public endpoints use exactly Lean's three standard axioms.”  In particular,
  the historical alternative declarations elsewhere in `Final.lean` are not
  dependencies of the public theorem.  The public theorem itself is the
  stationary-candidate route at
  [`Final.lean` lines 263–271](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/Final.lean#L263-L271).

## Term-by-term statement comparison

For this section, let `ω : ℕ → Bool` be a sample in the claim and restrict it
to prime coordinates by

```text
restrict(ω)(p : Nat.Primes) = ω(p.val).
```

Both Boolean decoders send `true` to `+1` and `false` to `-1`.  Thus this
restriction is the direct coupling used in the comparisons below.

### `Omega`

**Pinned claim.** `Omega := ℕ → Bool`; its source explicitly says that
non-prime coordinates are unused noise
([`Model.lean` lines 15–20](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/Model.lean#L15-L20)).

**Our statement.** `Ω := Nat.Primes → Bool`, so it omits exactly that noise
([`Statement.lean`](../Conjectures/C0006_erdos1144_random_mult/src/Statement.lean)).

**Comparison.** The spaces differ, but restriction retains every coordinate
used by the random multiplicative function.  Verdict: same effective sample.

### `mu`

**Pinned claim.** The one-coordinate law is the half-weighted sum of the two
Boolean Dirac measures, and `mu` is its `Measure.infinitePi` product over
`ℕ`.  The file proves both the probability-measure instance and coordinate
independence
([`Model.lean` lines 22–58](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/Model.lean#L22-L58)).

**Our statement.** `fairCoin` is `PMF.uniformOfFintype Bool` converted to a
measure, with singleton mass `1/2`; `randomCMMeasure` is its
`Measure.infinitePi` product over `Nat.Primes`.  It likewise has a proved
probability-measure instance and independent decoded signs.

**Comparison.** The one-coordinate laws agree.  Restricting the claim's
independent product to prime coordinates gives the product law used by ours;
the discarded coordinates do not occur in any later term.  Verdict: same law
for all relevant random variables.

### `eps`

**Pinned claim.** `eps ω p : ℝ` is `1` when `ω p` is true and `-1` otherwise
([`Model.lean` lines 60–70](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/Model.lean#L60-L70)).

**Our statement.** `primeSign` uses the same Boolean decoding in `ℤ` on a
prime and returns irrelevant junk value `1` on a non-prime.  The latter branch
cannot be selected by a factorization support.

**Comparison.** For every prime `p`, the claim's `eps ω p` is the real cast of
our `primeSign (restrict ω) p`.  Verdict: same prime signs.

### `sfKernel`

**Pinned claim.** `sfKernel n` filters `n.primeFactors` to primes whose
factorization exponent is odd
([`Model.lean` lines 119–121](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/Model.lean#L119-L121)).

**Our statement.** There is no separately named squarefree kernel;
`randomCM` takes the product over the full `Nat.factorization`, raising each
prime sign to its exponent.

**Comparison.** Since each prime sign squares to one, an even exponent
contributes `1` and an odd exponent contributes the sign.  The claim's own
source records this equivalence immediately above `f`.  This is a parity
normal form for a completely multiplicative function, not the
squarefree-supported Rademacher model.  Verdict: equivalent representation.

### `f`

**Pinned claim.** `f ω n : ℝ` is the product of `eps ω p` over `sfKernel n`
([`Model.lean` lines 123–145](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/Model.lean#L123-L145)).
The development proves full multiplicativity for positive inputs in
[`Multiplicativity.lean`](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/Multiplicativity.lean).

**Our statement.** `randomCM (restrict ω) n : ℤ` is the exponent product.  We
prove it is completely multiplicative on nonzero inputs and `±1`-valued.
Both constructions assign the harmless value `1` at `0`.

**Comparison.** By the preceding two rows, for every `n`,
`f ω n = (randomCM (restrict ω) n : ℝ)`.  Verdict: same complete random
multiplicative function, after the explicit coordinate restriction and cast.

### `S`

**Pinned claim.** `S ω N : ℝ := ∑ n ∈ Finset.Icc 1 N, f ω n`
([`Statistics.lean` lines 9–17](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/Statistics.lean#L9-L17)).

**Our statement.** `partialSum ω N : ℤ` uses the identical inclusive index
set and is cast to `ℝ` in `Erdos1144`.

**Comparison.** Casting commutes with the finite sum and the summands agree.
Verdict: identical normalized numerator under the coupling.

### `normSum`

**Pinned claim.** `normSum ω N = S ω (N + 1) / sqrt(N + 1)`; the shift avoids
the zero denominator
([`Targets.lean` lines 9–21](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/Targets.lean#L9-L21)).

**Our statement.** The event uses
`(partialSum ω N : ℝ) / Real.sqrt N` directly.

**Comparison.** The claim's sequence is our sequence composed with the
cofinal map `N ↦ N + 1`.  Removing or adding the single index `0` does not
change `Frequently` at `Filter.atTop`.  Verdict: equivalent tail sequence.

### `Erdos1144`

**Pinned claim.** For almost every `ω`, every real `A` is exceeded by
`normSum ω N` frequently at `atTop`
([`Targets.lean` lines 34–40](https://github.com/saasom/Erdos1144/blob/a0050daf4bf4992355b5ab189ee9c75cd44795a3/Erdos/Problem1144/Targets.lean#L34-L40)).

**Our statement.** The quantifier order is the same:
`∀ᵐ ω, ∀ M : ℝ, ∃ᶠ N in atTop, M ≤ partialSum ω N / sqrt N`.

**Comparison.** The law, summands, inclusive cutoff, normalization, one-sided
inequality, almost-everywhere quantifier, and “every threshold frequently”
quantifiers agree, modulo the equivalent coordinate representation and
cofinal shift above.  Verdict: the public theorem proves the proposition
stated on this card.

## Conjectural content and limits of this check

No conjectural lemma or new proof strategy is introduced here.  The only
source-level deductions made by this verification are the elementary coupling,
parity, cast, and cofinal-shift comparisons stated explicitly above.  The
substantive analytic theorem remains the pinned repository's claim.  This
check establishes that the claim rebuilt, that its endpoint has only the
three reported Lean kernel axioms, and that its formal target matches ours; it
does not manually validate each analytic argument or upgrade the claim's
external review status.
