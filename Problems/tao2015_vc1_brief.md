# Track R — V-C1 brief: Vinogradov's mean value theorem, weak explicit form (the `p`-adic / Linnik–Karatsuba proof)

**Ground rules:** `Problems/tao2015_vi9g_brief.md` §0 verbatim (no `sorry`/`axiom`/`unsafe` under `MoltResearch/`, `Solutions/`, not even in comments;
new nucleus lemmas only in new leaf files registered in `MoltResearch/DiscrepancyAnalytic.lean` — **but** this unit is pure combinatorics/number
theory with no dependence on the discrepancy nucleus: put it in a new leaf `MoltResearch/Discrepancy/VinogradovMeanValue.lean` importing only
Mathlib and (if useful) `MoltResearch/Discrepancy/ExpSums.lean`; respect `scripts/check_layering.sh`); one commit per unit
`Track R: <one line> (#3044, V-C1-<n>)`; never push/merge/rebase; `CODEX_REPORT.md` uncommitted. Read the design report §"Phase 6" and the V-C
design notes (`Problems/tao2015_vc_design_notes.md`).

## Target (Karatsuba, *Basic Analytic Number Theory*, Ch. VI Thm 1; Vaughan, *The Hardy–Littlewood Method*, Thm 5.2; Ford arXiv:1910.08209 Thm 3 for the sharp form)

```
/-- Vinogradov's integral in counting form. -/
def vinogradovJ (s k P : ℕ) : ℕ :=
  ((Finset.Icc 1 P)^s × (Finset.Icc 1 P)^s).filter (fun (x, y) => ∀ j ∈ Finset.Icc 1 k, ∑ i, (x i)^j = ∑ i, (y i)^j) |>.card
   -- (use `Fin s → ℕ` for the tuples: `Fintype.piFinset`)

theorem vinogradov_mean_value (k : ℕ) (hk : 2 ≤ k) (τ : ℕ) (hτ : 1 ≤ τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℕ, 1 ≤ P →
      (vinogradovJ (k * τ) k P : ℝ) ≤ C * (P : ℝ) ^ (2 * k * τ - k * (k + 1) / 2 + (k ^ 2 / 2) * (1 - 1 / k) ^ τ : ℝ)
```
(the exponent `δ_τ = (k²/2)(1 − 1/k)^τ`; any constant `C = C(k, τ)` is acceptable — record it — and any `δ_τ → 0` as `τ → ∞` with the same
shape would serve V-C2, but state this one.) Note `2kτ − k(k+1)/2 + δ_τ ≥ 0` and the trivial bound `J ≤ P^{2kτ}`.

## The proof, unit by unit (follow Vaughan Ch. 5 §§5.2–5.3 / Karatsuba VI §1; constants are yours)

- **V-C1-1 (elementary structure).** `vinogradovJ` is the number of solutions of the system `∑_i x_i^j = ∑_i y_i^j` (`1 ≤ j ≤ k`); prove
  monotonicity in `P`, the trivial bound, the **translation invariance** (`(x, y)` is a solution iff `(x + a, y + a)` is, by the binomial theorem:
  `∑ (x_i + a)^j = ∑_l C(j,l) a^{j−l} ∑ x_i^l`), and the **Hölder/Cauchy–Schwarz counting inequality**: writing `r_P(c) := #{x ∈ [1,P]^s : (∑ x_i^j)_j = c}`
  one has `J_{s}(P) = ∑_c r_P(c)²`, and for any subset `A ⊆ [1,P]^s` the number of solutions with `x ∈ A` is `≤ (#A)^{1/2}… ` — the standard
  `∑_c r_A(c) r_P(c) ≤ (∑ r_A(c)²)^{1/2}(∑ r_P(c)²)^{1/2}`, and the sub-additivity used to split solutions by cases.
- **V-C1-2 (well-conditioned tuples).** For a prime `p`, call `x ∈ [1,P]^k` *well-conditioned mod `p`* if `x_1, …, x_k` are pairwise distinct
  mod `p`. Count the ill-conditioned ones: `≤ C(k,2)·P^{k−1}·(P/p + 1)`. Split the solutions of `J_{s+k}(P)` according to whether the first `k`
  coordinates of `x` (and of `y`) are well-conditioned; bound the ill-conditioned part by V-C1-1's Cauchy–Schwarz against `J_{s+k}(P)` itself
  (this gives the factor `(k²/p)^{1/2}`-type saving that lets the ill-conditioned part be absorbed for `p ≥ 4k⁴`, or handled as in Vaughan Lemma 5.4).
- **V-C1-3 (Linnik's lemma).** For a prime `p` and `k ≥ 2`: the number of solutions of the congruence system
  `∑_{i=1}^k (x_i^j − y_i^j) ≡ 0 (mod p^j)`, `1 ≤ j ≤ k`, with `1 ≤ x_i, y_i ≤ p^k` and `x` well-conditioned mod `p`, is at most `k!·p^{2k² − k(k+1)/2}`
  (Vaughan Lemma 5.3; Karatsuba VI Lemma 3). Proof: fix `y` (`p^{k²}` choices) and the residues of `x` mod `p` (well-conditioned: `≤ p^k` choices);
  lift level by level: given the `x_i` mod `p^{j−1}`, the `j`-th congruence determines the `j`-th digit vector uniquely up to the Vandermonde
  matrix of the residues, which is invertible mod `p` — so there are exactly `p^{k−1}·…` hmm: count carefully — at level `j` the unknowns are the
  `k` new digits `(x_i mod p^j) = (x_i mod p^{j−1}) + p^{j−1} d_i`, `d ∈ [0,p)^k`, and the `j` congruences for the exponents `1..j` at modulus `p^j`
  … the standard route: the system `∑_i x_i^l ≡ c_l (mod p^l)`, `l ≤ k`, for well-conditioned `x mod p^k` has at most `k!·p^{k² − k(k+1)/2}` solutions
  `x ∈ [1, p^k]^k` (Vaughan Lemma 5.3's core), by induction on `k` via the Newton identities/Vandermonde argument (the map `x ↦ (power sums)` is
  `k!`-to-one on well-conditioned tuples modulo the appropriate powers). Follow Vaughan's proof; state the lemma with an explicit constant.
- **V-C1-4 (the fundamental lemma).** For a prime `p` with `p^k ≤ P` … (choose `p ∈ (P^{1/k}, 2P^{1/k}]`, Bertrand): after translation by `a mod p`
  and the substitution `x_i = p z_i + w_i` for the `s` "free" variables, Linnik's lemma and the counting inequalities give
  `J_{s+k}(P) ≤ C_k · p^{2s + k(k−1)/2}·… · J_s(P/p + 1)` — precisely Vaughan Lemma 5.4 / Karatsuba VI Lemma 5:
  `J_{s+k,k}(P) ≤ k!·k^{2k}… · p^{2s − k(k+1)/2 + …}·J_{s,k}(2P/p)`; derive the exact shape as you prove it and record it.
- **V-C1-5 (the induction).** From V-C1-4 with `p ≍ P^{1/k}`: if `J_{s}(Q) ≤ C Q^{2s − k(k+1)/2 + Δ}` for all `Q`, then
  `J_{s+k}(P) ≤ C' P^{2(s+k) − k(k+1)/2 + Δ(1 − 1/k)}` — the recursion `Δ_{τ+1} = Δ_τ(1 − 1/k)`, `Δ_1 = k²/2·(1 − 1/k)` hmm: with `J_k(P) ≤ k!·P^k`
  (trivial: `Δ_1 = k(k+1)/2 − k = k(k−1)/2 ≤ (k²/2)(1 − 1/k)`) — closes `δ_τ = (k²/2)(1 − 1/k)^τ` by induction on `τ`.
- **V-C1-6.** The theorem statement above, with `C` recorded, plus the two corollaries V-C2 will use: the **exponential-sum form**
  `∫_{[0,1]^k} |∑_{x ≤ P} e(α₁x + ⋯ + α_k x^k)|^{2s} dα = J_{s,k}(P)` (orthogonality of `e(n·α)` on `[0,1]^k`; Mathlib has the Fourier orthogonality
  on `AddCircle`/`[0,1]` — state it for the `k`-fold product) and the **shifted form** (`x` in any interval of length `P`, by translation invariance).

**Verification/report** as always (`lake env lean`, `lake build MoltResearch.DiscrepancyAnalytic`, gates, layering, coverage, `#print axioms`).
**Stop rule:** none expected — this is textbook; if Linnik's lemma resists, record the exact obstruction and prove the theorem with a weaker `δ_τ`
of the same shape (any `(k²/2)(1 − c/k)^τ` with fixed `c > 0` serves V-C2).
