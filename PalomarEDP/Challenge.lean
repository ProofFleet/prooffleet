import Mathlib

/-!
# The Erdős discrepancy theorem: statement of record

This module is the statement surface of the Palomar registry entry *A Lean formalization of the
Erdős discrepancy theorem*. It is meant to be read on its own: it imports only Mathlib, uses no
definition from this repository, and spells the claim out with ordinary Mathlib objects
(`Finset.range`, `Finset.sum`, `Int.natAbs`). Its one theorem is stated without a proof; the
proof lives in `PalomarEDP.Solution`, and Comparator checks mechanically that the two
declarations have exactly the same statement.

## The mathematical claim

Let `f : ℕ → ℤ` take only the values `1` and `-1`. Then for every natural number `C` there are a
step `d ≥ 1` and a length `n` such that

  `|f(d) + f(2d) + ⋯ + f(nd)| > C`.

In other words `sup_{d ≥ 1, n} |∑_{j=1}^{n} f(jd)| = ∞`: every `±1` sequence has unbounded
discrepancy along homogeneous arithmetic progressions. This is the Erdős discrepancy problem,
answered by Terence Tao, *The Erdős discrepancy problem*, Discrete Analysis 2016:1
(arXiv:1509.05363); the statement below is the paper's Corollary 1.2, the original `±1`
formulation. Tao's Theorem 1.1, for functions into the unit sphere of a Hilbert space, is not
formalized here.

## Reading notes

* `f` is an arbitrary function. No multiplicativity or other structure is assumed; the
  hypothesis `hf` says only that every value is `1` or `-1`.
* The sum `(Finset.range n).sum (fun i => f ((i + 1) * d))` is `f(d) + f(2d) + ⋯ + f(nd)`: the
  index `i` runs over `0, …, n - 1`, so the progression starts at `d`, not at `0`.
* The domain is `ℕ`, which contains `0`, and `hf` also constrains `f 0`. Since `d ≥ 1`, the
  progression never evaluates `f 0`, so the statement is the same as for sequences
  `f(1), f(2), …` indexed by the positive integers: such a sequence extends to `ℕ` by either
  choice of `f 0`, and the conclusion does not depend on that choice.
* `n = 0` is allowed and gives the empty sum `0`, which never exceeds `C`; a witness therefore
  always has `n ≥ 1`.
* The witnesses `d` and `n` depend on `C` (and on `f`); the conclusion is strict excess over
  every natural threshold `C`. `Int.natAbs z` is the absolute value of the integer `z` as a
  natural number, so the comparison takes place in `ℕ`.
-/

namespace EDP

/-- **The Erdős discrepancy theorem** (Tao 2015, Corollary 1.2 of arXiv:1509.05363).

Every `±1`-valued sequence `f` has unbounded discrepancy along homogeneous arithmetic
progressions: for every natural number `C` there are `d ≥ 1` and `n` with
`|f(d) + f(2d) + ⋯ + f(nd)| > C`. -/
theorem erdos_discrepancy
    (f : ℕ → ℤ)
    (hf : ∀ n : ℕ, f n = 1 ∨ f n = -1) :
    ∀ C : ℕ, ∃ d n : ℕ,
      0 < d ∧
      C < Int.natAbs ((Finset.range n).sum (fun i => f ((i + 1) * d))) := by
  sorry

end EDP
