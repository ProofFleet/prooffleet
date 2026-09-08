## RESUME NOTE (run 27) — read before anything else
Run 24 committed V-C2-1…V-C2-7 (`VinogradovWeylSum.lean`: Taylor phase, shift averaging + Hölder, orthogonality, block control by polynomial moments,
coefficient boxes + top-frequency spacing, the exact multiplicity `ν(β) ≤ 2(2(2N+1)^{k+1}/(k²tM^k) + 1)`, the aggregate box reduction on `[−1,2]^k`,
and the phase conversion) and stopped because `vinogradov_mean_value` hides its constant `C_{k,τ}` behind `∃ C` with no public growth bound. **Your
corrected bookkeeping is accepted** (Ford Lemma 6.3: short length `M` at scale `N^{1−λ/(k+1)}`, multiplicity `O(M)`, `τ ≍ k log k`, `s = kτ`, `δ_τ ≤ 1/2`), and the
**target is now the weakened fixed form** `1 − c/(λ³·log²(2λ))` (`a = 3`, `b = 2`), which V-C3 can use. Do:

- **V-C1′ (export the constant envelope).** In a new leaf importing `VinogradovMeanValue.lean` (or by adding a public theorem there — the file is a leaf you own; do
  not change existing statements), prove `vinogradovMeanValueConstant_le : vinogradovMeanValueConstant k τ ≤ D k τ` for an explicit closed form `D` obtained
  by unwinding your own recursion (the construction starts at `k! + 1` and each of the `τ` steps multiplies/adds explicit factors — bound each step by
  `(2k(k+τ))^{c₁ k (k+τ)}`-type and iterate, or prove directly `Real.log (vinogradovMeanValueConstant k τ) ≤ c₂ · k·τ·(k + τ)·Real.log (2k(k+τ))` — any bound with
  `log D_{k,τ}/(2kτ) = O(k log k + τ log τ)`-type growth suffices; record it). If the spec theorem for the named constant is private, add a public one.
- **V-C2-8 (fold the cube).** `[−1, 2]^k` → three unit periods per coordinate (integer-shift periodicity of the majorant, already proved), factor `3^k`.
- **V-C2-9 (assembly).** The long-interval shift assembly with `M` at scale `N^{1−λ/(k+1)}` for `k − 1 ≤ λ ≤ k` (`k := ⌈λ⌉`), `τ := ⌈k log k⌉ + 1`, `s := kτ`; the main
  term `N·(M^{1+δ_τ}·3^k·2^{4s}·2(…)·C_{k,τ}/N)^{1/(2s)}`-type; then the **large-`N`/small-`N` split**: if `log N ≥ K·k³ log²(2k)` (`K` explicit) the prefactor
  `(3^k 2^{4s} C_{k,τ} ν …)^{1/(2s)}` is `≤ N^{c/(2λ³ log²(2λ))}` and the saving `(M/N)^{1/(2s)}·…` gives `N^{1 − c/(λ³ log²(2λ))}`; otherwise the trivial bound `N`
  already is `≤ C·N^{1 − c/(λ³ log²(2λ))}` (since then `N^{c/(λ³ log² 2λ)} ≤ e^{cK}`). Record `c, C, K`.
- **V-C2-10 (small `λ`).** For `λ ≤ 2` (i.e. `t ≤ N²`) use the tree's van der Corput bound (`vdc2` as in `norm_halaszKernel_le`: `|∑_{N<n≤2N} e(f(n))| ≪ N^{1/2}·(t/N)^{1/2}+ N/(t/N)^{1/2}`…
  for `N ≤ t ≤ N²` this is `≪ N^{3/4}`-type) to get a fixed power saving, which is `≤ C N^{1−c/(λ³log²2λ)}` for `λ ≤ 2`. (If `norm_halaszKernel_le`'s form is
  inconvenient, prove the needed block bound directly from `vdc2`.)
- **V-C2-11.** `theorem vinogradov_weyl_sum` in the brief's shape with exponent `1 − c/((log t/log N)^3 · (Real.log (2·log t/log N))^2)`; record the compiled form.

Stop rule unchanged: only an unbounded failure for every admissible parameter choice.

# Track R — V-C2 brief: Weyl sums `∑ n^{−it}` by Vinogradov's method, from `vinogradov_mean_value`

**Ground rules:** `Problems/tao2015_vi9g_brief.md` §0 verbatim (no `sorry`/`axiom`/`unsafe` under `MoltResearch/`, `Solutions/`, not even in comments;
new nucleus lemmas only in new leaf files registered in `MoltResearch/DiscrepancyAnalytic.lean`; never edit `PlancherelHarness`, never append to
`BandSchedule`/`WindowTK`/`WindowAssembly`/`HalaszComplex`; respect `scripts/check_layering.sh`; one commit per unit `Track R: <one line> (#3044, V-C2-<n>)`;
never push/merge/rebase; `CODEX_REPORT.md` uncommitted). Read: the design report §"Phase 6", `Problems/tao2015_vc_design_notes.md`
(the V-C2/V-C3 structure from Ford arXiv:1910.08209 §§4–7), `MoltResearch/Discrepancy/VinogradovMeanValue.lean` (`vinogradovJ`,
`vinogradov_mean_value`, `vinogradovMeanValueConstant`, and — if V-C1-6 landed — the exponential-sum/orthogonality form; otherwise prove it here),
`MoltResearch/Discrepancy/ExpSums.lean` (`e`, `nint`, `kusmin_landau`, `vdc2`), `HalaszMontgomeryLargeValues.lean` (`norm_halaszKernel_le` — the
van der Corput bound for these sums at `|u| ≤ N`-type ranges, useful for the small-`λ` regime).

## Target (Karatsuba, *Basic Analytic Number Theory*, Ch. VI Thm 2; Titchmarsh §§5.10–5.18; Ford Thm 2)

New leaf `MoltResearch/Discrepancy/VinogradovWeylSum.lean`:
```
theorem vinogradov_weyl_sum :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N : ℕ) (t : ℝ), 2 ≤ N → (N : ℝ) ≤ t →
      ∀ (u : ℝ) (R : ℕ), 0 ≤ u → u ≤ 1 → N < R → R ≤ 2 * N →
        ‖∑ n ∈ Finset.Ioc N R, ((n : ℝ) + u : ℂ) ^ (-(t : ℂ) * Complex.I)‖
          ≤ C * (N : ℝ) ^ (1 - c / ((Real.log t / Real.log N) ^ 2 * Real.log (2 * Real.log t / Real.log N)))
```
(`λ := log t/log N ≥ 1`; the saving `N^{−c/(λ² log 2λ)}` is the weak-MVT version of the classical `N^{−c/λ²}`; either serves V-C3.) State the phase as
`e(f(n+u))`-style if more convenient (`(n+u)^{−it} = exp(−it log(n+u))`, Mathlib's `Complex.cpow` for real base > 0); record which form is proved and
give the conversion.

## The proof (Vinogradov's method; constants are yours, record them)

- **V-C2-1 (Taylor of the phase).** For `n ∈ (N, 2N]`, `1 ≤ x ≤ U` with `U ≤ N^{1/2}`: `log(n + u + x) = log(n+u) + ∑_{j=1}^k (−1)^{j−1} x^j/(j (n+u)^j) + ρ`,
  `|ρ| ≤ (x/(n+u))^{k+1}/(k+1)·(1/(1 − x/(n+u)))`; so `e(−(t/2π) log(n+u+x)) = e(−(t/2π)log(n+u))·e(∑_j α_j(n) x^j)·e(−(t/2π)ρ)` with
  `α_j(n) := (−1)^{j} t/(2π j (n+u)^j)` (mod 1) and `|e(−(t/2π)ρ) − 1| ≤ t·(U/N)^{k+1}/(k+1)`. Choose `k` and `U` so that `t U^{k+1}/N^{k+1} ≤ 1/U`
  (then the remainder costs `O(1)` per `n`-block of length `U`... state it as `≤ N·t U^{k+1}/N^{k+1} ≤ N/U`).
- **V-C2-2 (shift averaging + Hölder).** `S := ∑_{N<n≤R} e(f(n))` with `f(n) = −(t/2π) log(n+u)`: `|S| ≤ (1/U)∑_{x=1}^{U} |∑_n e(f(n+x))| + 2U`
  (each shift changes the range by `≤ U` terms), and `∑_n e(f(n+x))` over the shifted range… — rather, the standard form: `U·S = ∑_{x≤U} ∑_{n} e(f(n+x)) + O(U²)`,
  so `|S| ≤ (1/U)|∑_n ∑_{x≤U} e(f(n+x))| + 2U ≤ (1/U)∑_n |∑_{x≤U} e(P_n(x))| + N·(remainder) + 2U`, `P_n(x) := ∑_j α_j(n) x^j`. Hölder:
  `∑_n |∑_x e(P_n(x))| ≤ N^{1 − 1/(2s)}·(∑_n |∑_{x≤U} e(P_n(x))|^{2s})^{1/(2s)}`.
- **V-C2-3 (the frequency boxes — Vinogradov's counting).** For `α ∈ ℝ^k` write `T(α) := ∑_{x≤U} e(α₁x + ⋯ + α_k x^k)`. Lipschitz: `|T(α) − T(β)| ≤ 2π U ∑_j |α_j − β_j| U^j`.
  Partition `[0,1)^k` into boxes `B` of sides `1/(2πk U^{j+1})` in coordinate `j` (so `|T|` varies by `≤ 1` on a box), number of boxes
  `≍ (2πk)^k U^{k(k+1)/2 + k}`. Then `|T(α)|^{2s} ≤ 2^{2s}(min_{β∈B}|T(β)|^{2s} + 1) ≤ 2^{2s}(vol(B)^{−1}∫_B |T|^{2s} + 1)`, hence
  `∑_n |T(α(n))|^{2s} ≤ 2^{2s} ∑_B ν(B)·(vol(B)^{−1}∫_B|T|^{2s} + 1)`, `ν(B) := #{n : α(n) ∈ B}`; with `ν(B) ≤ ν_max`:
  `≤ 2^{2s} ν_max·((2πk)^k U^{k(k+1)/2 + k}·J_{s,k}(U) + #boxes)` using `∫_{[0,1]^k}|T|^{2s} = J_{s,k}(U)` (orthogonality; V-C1-6 or prove:
  expand `|T|^{2s}` and integrate `e(β·c)` over the cube). **The multiplicity**: `α_k(n) = ± t/(2πk(n+u)^k)` is monotone in `n` with
  `|α_k(n) − α_k(n+1)| ≥ t/(2πk (2N)^{k+1})·c₀`, so a box of side `1/(2πk U^{k+1})` in coordinate `k` contains at most
  `ν_max ≤ (2N)^{k+1}/(c₀ t U^{k+1}) + 1` values of `n` — this is where `t ≥ N` matters: with `U^{k+1} ≍ N^{k+1}/t` (the V-C2-1 choice),
  `ν_max = O(1)`! (Vinogradov's choice `U = (N^{k+1}/t)^{1/(k+1)} = N·t^{−1/(k+1)}`.) Record the exact `ν_max`.
- **V-C2-4 (the parameters).** With `U = N t^{−1/(k+1)}`, `k := ⌈λ⌉ + 1` hmm — choose `k` so that `U ≍ N^{1/2}`-ish or larger: `t^{1/(k+1)} ≤ N^{1/2}` iff
  `k + 1 ≥ 2λ`; take `k := ⌈2λ⌉` (so `U ≥ N^{1/2}`) and `s := k·τ` with `τ := ⌈k log k⌉ + 1` so that `δ_τ = (k²/2)(1 − 1/k)^τ ≤ (k²/2)e^{−τ/k} ≤ 1/2`.
  Then `J_{s,k}(U) ≤ C_{k,τ} U^{2s − k(k+1)/2 + 1/2}`, and V-C2-3 gives `∑_n|T|^{2s} ≤ C' U^{2s + k + 1/2}` (the `#boxes` term is smaller), so
  `|S| ≤ N^{1−1/(2s)}·C'^{1/(2s)}·U^{1 + (k + 1/2)/(2s)}/U + N/U + 2U ≤ C''·N·(U/N)^{…}`… — compute honestly: `(1/U)·N^{1−1/(2s)}·U^{1+(k+1/2)/(2s)}
  = N·(U/N)^{1/(2s)}·U^{(k+1/2)/(2s) − 1/(2s)}`… hmm, `N^{1−1/(2s)} U^{(k+1/2)/(2s)} = N·(U^{k+1/2}/N)^{1/(2s)}`. With `U = N t^{−1/(k+1)}`:
  `U^{k+1/2}/N = N^{k−1/2} t^{−(k+1/2)/(k+1)} = N^{k − 1/2 − λ(k+1/2)/(k+1)}`; for `k ≥ 2λ` the exponent is `≤ k − 1/2 − λ + λ/(2(k+1))`… this must be
  **negative** to save; it is not for `k > λ + 1/2`. **So the naive bookkeeping does not save — the saving in Vinogradov's method comes from
  `U^{k(k+1)/2}·J` vs the trivial `U^{2s}`: recompute** — `∑_n |T|^{2s} ≤ 2^{2s} ν_max (2πk)^k U^{k(k+1)/2 + k} J_{s,k}(U)`, and the *trivial* bound is
  `N U^{2s}`; the ratio is `ν_max (2πk)^k U^{k(k+1)/2+k} C U^{2s − k(k+1)/2 + δ}/(N U^{2s}) = ν_max (2πk)^k C U^{k+δ}/N`. With `ν_max = O(1)` and
  `U^{k+δ}/N = N^{k+δ−1} t^{−(k+δ)/(k+1)}`: negative exponent iff `(k+δ−1) log N < ((k+δ)/(k+1)) log t = ((k+δ)/(k+1)) λ log N`, i.e.
  `λ > (k+δ−1)(k+1)/(k+δ) ≈ k` — so we need **`k < λ`**, e.g. `k := ⌊λ⌋ − 1`… but then `U = N t^{−1/(k+1)} < N^{1 − λ/(k+1)} < 1`. Contradiction —
  the resolution in the classical argument is that the `n`-sum is split into blocks of length `≍ U` **and the multiplicity counts `n`-blocks, not `n`**,
  with `U = N^{1−1/k}`-type… **Do the bookkeeping from Karatsuba VI §2 (Lemma 6 and Theorem 2) or Titchmarsh §5.16 exactly rather than from this
  sketch**: the standard choices are `k ≍ λ` (so that `N^{k} ≍ t`, i.e. the `k`-th derivative `t/N^{k+1} ≍ 1/N` is the natural scale), `U ≍ N^{1−1/k}`?
  … The brief's author could not reproduce the constants from memory; **the task includes reconstructing the parameter choice** from the cited sources
  (Titchmarsh §5.16–5.18 gives `∑_{N<n≤2N} n^{−it} ≪ N^{1 − 1/(c λ²)}`-type via the MVT with `k ≍ λ`, `U = N^{1/…}`, and the multiplicity argument on
  the `k`-th coefficient), and reporting it. Any exponent of the form `1 − c/(λ^a log^b(2λ))` with fixed `a, b` is acceptable for V-C3 (record `a, b`).
- **V-C2-5 (small `λ`).** For `λ ≤ λ₀` (a fixed constant, e.g. `2`), the bound `N^{1−c}` with a fixed `c` follows from the van der Corput second-derivative
  test already in the tree (`vdc2`, as used in `norm_halaszKernel_le`: `|∑_{N<n≤2N} e(f(n))| ≪ N/√(t/N²)… ≪ N^{1/2}t^{1/2}/N^{…}`— for `t ≤ N^{λ₀}` this is
  `N^{1 − c(λ₀)}`); include it so the theorem holds for all `N ≤ t`.

**Verification/report** as always (`lake env lean`, `lake build MoltResearch.DiscrepancyAnalytic`, gates, layering, coverage, `#print axioms`).
**Stop rule:** stop only if the exponent obtained is not of the form `1 − c/(λ^a log^b 2λ)` for fixed `a, b, c > 0` (record exactly what was obtained);
constants and parameter choices are yours.
