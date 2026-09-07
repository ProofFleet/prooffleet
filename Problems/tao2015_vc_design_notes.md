# V-C design notes (Vinogradov's method → a zero-free region of width ≥ (log t)^{−4/5}) — 2026-09-06

## What the consumer needs (fixed by V-0/V-B)
A zero-free region `σ ≥ 1 − η(t)` with `η(t) ≥ (log t)^{−θ}` for some `θ < 1` beyond a fixed height, plus `‖ζ'/ζ‖ ≤ (log t)^{m}` on
`Re s ≥ 1 − η(t)/2`. V-B's `ZeroFreeRegionData θ m` packages exactly this; the class exponent `4/5` follows from any `θ < 4/5`
(V-B-2's algebra). Chudakov's region (`θ = 3/4 + ε`) or Vinogradov–Korobov (`θ = 2/3 + ε`) both qualify.

## The route (Karatsuba, *Basic Analytic Number Theory*, Ch. VI; Ford arXiv:1910.08209 for explicit constants)
V-C1 **Mean value theorem (weak form suffices).** `J_{s,k}(P) := #{(x,y) ∈ [1,P]^{2s} : ∑ x_i^j = ∑ y_i^j, j ≤ k}`. Karatsuba Thm VI.1
(Linnik's `p`-adic method): for `s = kτ`, `J_{s,k}(P) ≤ D_τ P^{2s − k(k+1)/2 + δ_τ}`, `δ_τ = (k²/2)(1 − 1/k)^{τ}`, `D_τ = (kτ)^{2kτ}(2k)^{4k(k+1)τ}`-type.
Ingredients: Lemma (Linnik) — the number of solutions of the system with the `x_i` in distinct residue classes mod `p` is `≤ k!·p^{k(k−1)/2}·(P/p+1)^{…}`
(non-singular Jacobian / Newton identities); the `p`-adic shift `x_i = p y_i + z_i`; Hölder to reduce to the distinct-class case; induction on `τ`.
Ford's Thm 3 is the same induction with sharper bookkeeping (Lemmas 3.2–3.6) and Wooley's Lemma 2.4 for the congruence count. **Formalization scope:**
the counting/combinatorics of Diophantine systems, binomial/Newton identities, Hölder for exponential-sum moments (`∫_{[0,1]^k} |∑ e(α·(x,…,x^k))|^{2s} = J`),
the residue-class splitting. Elementary but long (~2–4 Codex runs if the weak form is targeted with generous constants).

V-C2 **Weyl sums by Vinogradov's method.** For `N < n ≤ 2N` and `f(n) = −(t/2π) log n`: Taylor-expand `f(n+u)` to order `k` (`n` fixed, `u ≤ U := N^{…}`),
so the sum over `u` is an exponential sum with polynomial phase `α₁u + … + α_k u^k`; average over the shift, Hölder with exponent `2s`, and the
mean value theorem `J_{s,k}(U)` bound the sum by `N^{1 − c/(k² log k)}`-type savings when `k ≍ log t/log N` — Ford's Thm 2:
`S(N,t) ≤ 9.463·N^{1 − 1/(133.66 λ²)}`, `λ = log t/log N` (major/minor arcs via rational approximation of the `α_j`; Vinogradov's "counting the
frequency box" argument). Scope: 1–2 runs beyond V-C1.

V-C3 **The zeta bound near σ = 1.** From `S(N,t)` bounds, partial summation and the approximate functional equation/Perron truncation
(`ζ(s) = ∑_{n≤X} n^{−s} + O(X^{1−σ}/|t|)`-type for `X ≍ t`, Mathlib/tree: `zeta_LSeries_bound`, `zeta_strip_bound` in `ZetaBound.lean` may already give a
truncated form), dyadic summation over `N ≤ t`: `|ζ(σ+it)| ≤ A t^{B(1−σ)^{3/2}} log^{2/3} t` (Ford Thm 1), or the weaker Karatsuba Thm VI.3
`|ζ(σ+it)| ≤ C t^{c(1−σ)^{3/2}} (log t)^{2/3}`-type. Any `a > 5/4` in `t^{B(1−σ)^{a}}` suffices for `θ = 4/5`.

V-C4 **The region and the `ζ'/ζ` bound** from V-C3 via the tree's Landau/3-4-1 assembly: `zeta_landau_core`, `zeta_norm_lower_341`,
`landau_inequality`, `norm_logDeriv_le_of_ratio_le` (Borel–Carathéodory) — parametrize `zeta_zero_free_region`'s proof by the growth bound
`log‖ζ(σ+it)‖ ≤ φ(t)(1−σ)^{a} + b·loglog t` on `1 − δ ≤ σ ≤ 2`: Karatsuba Thm VI.4 / Titchmarsh 6.15–6.16 give
`σ ≥ 1 − c/((log t)^{1−1/a}(loglog t)^{1/a})` hmm — for `a = 3/2`: `(log t)^{2/3}(loglog t)^{1/3}` ✓ VK. First do V-C4 against
`zeta_norm_upper` (recovering de la Vallée Poussin) to validate the parametrization, then plug V-C3.

## Order and cost
V-C4 (parametrized assembly, ~1 run) → V-C1 (weak MVT, 2–4 runs) → V-C2 (1–2 runs) → V-C3 (1–2 runs) → instance + unconditional endpoint.
Sources to fetch when writing briefs: Karatsuba Ch. VI is not online; use Ford's ar5iv text for the MVT induction and Theorem 2, and Titchmarsh
6.15–6.16 (or Karatsuba VI.4) as reconstructed from the tree's existing 3-4-1 proof.


## V-C2/V-C3 structure (from Ford §§4–7, ar5iv 1910.08209; Karatsuba VI §§2–3)
- **Theorem 2 (Ford).** `S(N,t) := max_{0<u≤1} max_{N<R≤2N} |∑_{N<n≤R} (n+u)^{−it}| ≤ 9.463·N^{1 − 1/(133.66 λ²)}`, `λ = log t/log N`, `N ≤ t`.
  Proof: Taylor-expand `f(n+u) = −(t/2π) log(n+u)` about `N` to order `k` (`log(N+x) = log N + ∑_{j≤k} (−1)^{j−1} x^j/(j N^j) + O((x/N)^{k+1})`),
  so a short sum over `x ≤ U` has polynomial phase `α₁x + ⋯ + α_k x^k` with `α_j ≍ t/(j N^j)`; average over shifts, Hölder with exponent `2s` to
  compare `|∑ e(p(x))|^{2s}` with `∫_{[0,1]^k}|∑_{x≤U} e(α·(x,…,x^k))|^{2s} dα = J_{s,k}(U)` after counting how many shifts produce nearby frequency
  vectors (major/minor arcs by rational approximation of the `α_j`); parameters `k ≍ (log t/loglog t)^{1/3}`-type (Ford needs `k ≥ 1000`, i.e. `λ ≥ 1000`;
  for `λ < 1000` he uses explicit averaging — for us: Karatsuba VI Thm 2 covers all `λ` with `k ≍ λ`, and the blocks with `λ ≤ λ₀` fixed can take the
  tree's van der Corput bounds, since there only a fixed power saving `N^{−c}` is needed), `s ≍ k²`, `U = N/k`.
- **Theorem 1 from Theorem 2.** `ζ(σ+it) = ∑_{n≤X} n^{−σ−it} + X^{1−σ−it}/(σ+it−1) + O(X^{−σ})` for `X ≍ t` (the tree's `ZetaBound.lean` has
  `zeta_strip_bound`/`zeta_LSeries_bound` — check which truncation is available), dyadic blocks `N = 2^k ≤ X`, `|∑_{N<n≤2N} n^{−σ−it}| ≤ (2N)^{−σ}·S(N,t)`
  by partial summation, so `|ζ| ≲ ∑_k 2^{k(1−σ)}·2^{−k/(133.66 λ_k²)}`, `λ_k = log t/(k log 2)`; the terms with `2^{k} ≤ exp((log t)^{2/3}·…)` are bounded
  by the Vinogradov saving and the large-`k` terms by `N^{1−σ}·N^{−c/λ²}`; optimizing gives `t^{B(1−σ)^{3/2}} log^{2/3} t`. **For V-C4 any
  `a > 5/4` suffices**, so V-C2/V-C3 may take generous constants: the weak MVT `δ_τ = (k²/2)(1−1/k)^τ` with `τ ≍ k log k` gives the classical
  Vinogradov saving `N^{1 − c/(k² log k)}` for `k ≍ λ`, i.e. `S(N,t) ≪ N^{1 − c/(λ² log λ)}`, and then `|ζ(σ+it)| ≪ t^{c'(1−σ)^{3/2}}(log t)^{2/3 + o(1)}`
  (Karatsuba VI Thm 3) — a `(loglog)` loss in the exponent's second term is harmless for `θ = 4/5`.
- **Briefs to write after V-C1 lands:** V-C2 (Weyl sums: Taylor expansion, Hölder reduction to `J_{s,k}(U)`, the counting of coincident frequency
  vectors — Karatsuba VI Lemma 6/Thm 2 shape), V-C3 (truncation + dyadic summation + optimization → `ZetaGrowthBound t₀ a B b B₀` with `a = 3/2`).
