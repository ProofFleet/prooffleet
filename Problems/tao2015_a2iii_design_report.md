# A2-III design report — the inner mid-frequency band ([mrt] A.2)

> **Status: design note, not a Problem Card.** The card is
> [`tao2015_derivation_c.md`](tao2015_derivation_c.md); this file is the paper-first
> derivation behind its Matomäki–Radziwiłł checklist item, written in the
> 2026-08-29 design session and committed unchanged (below the errata) on
> 2026-08-30.
>
> It is committed because it is the **only** record of the A2-III ladder's
> error-term shapes — the `E₁`/`E_j` bounds and the exact Lean statements of the
> units — and it is not reconstructible from the tree. It lived in a session
> scratchpad and was very nearly lost.

## Errata — read before building anything from this file

The report has been used to ship the whole A2-III ladder. Eleven of its claims did
not survive contact with Lean — items 1–6 from building the ladder, items 7–8
from calibrating it, and items 9–11 from closing the S1–S7 schedule. The body
below is **unedited**; the corrections are here.

1. **III-2's Euler factor and its constant are wrong — the stated bound is false.**
   The report claims
   `Σ_{r,r' Y-smooth} 1/[r,r'] = ∏_{p∈Y}(1 + 3/p + 4/p² + …) ≤ exp(3 Σ_{p∈Y} 1/p)`.
   The correct local factor is `Σ_{i,j≥0} p^{−max(i,j)} = Σ_{k≥0}(2k+1)p^{−k}
   = (1+x)/(1−x)²` at `x = 1/p`, i.e. `1 + 3/p + 5/p² + 7/p³ + …` — coefficient
   `5`, not `4`. And `exp(3x)` does **not** dominate it at *any* prime, not merely
   at small ones: `6 > 4.482` at `p = 2`, and still `1.03020 > 1.03015` at
   `p = 101`, because `LHS − RHS = 0.5x² + O(x³) > 0`. **The correct constant is
   `4`**: `(1+x)/(1−x)² ≤ e^{4x}` on `(0, 1/2]`. In tree as
   `one_add_div_one_sub_sq_le_exp` (#3532). Any downstream constant quoting
   `exp 3` must be re-derived as `exp 4`; all of them are absolute, so nothing
   material changes.

2. **III-1 came out sharper than the report assumed, and that deleted a
   dependency.** The report bounds the tuple fibre by `k! ·` (smooth divisor
   count). The truth is a clean `k!`: all tuple entries are primes, so the fibre
   is a set of permutations. Consequently the **pure-power** moment `∫‖Q^ℓ‖²`
   needs no Shiu substitute at all — that is why III-3b (#3528) went through on
   `ℓ!` plus the harmonic mass alone. III-2 is still needed for the **full** III-3,
   the moment of `Q^ℓ ·(block polynomial)`, whose support is a product set.

3. **IV-1/IV-2 landed in a different file than the report names.** Not
   `MoltResearch/Discrepancy/LargeValueAssumptions.lean` but
   `Conjectures/C0002_erdos_discrepancy/src/Interfaces/LargeValues.lean` — a new
   hypothesis class must live under `Interfaces/` from its first commit, since
   `scripts/interface_location_allowlist.txt` is a ratchet and forbids new
   entries. They must also be transcribed into `Problems/sources/`, or
   `scripts/check_interfaces.py` warns.

4. **`quotBlock`, used in the II-5 statement, is not an in-tree definition.** The
   II-5 signature below is therefore a sketch, not a transcribable target.

5. **III-2's whole *route* is unnecessary, not just its constant.** Item 1 above
   corrects the Euler factor; this item retires the Euler product. The sum the
   moment estimate actually needs runs over the **finite** set
   `Y^ℓ = (piFinset fun _ : Fin ℓ => Y).image (∏)` — the support of `Q^ℓ` — not
   over the infinitely many `Y`-smooth numbers, so no `smoothDivisorCount`
   definition and no free-commutative-monoid machinery are required. Partition
   `Y^ℓ × Y^ℓ` into the fibres of `(r,r') ↦ Ω(gcd r r')`; on the fibre over `k`
   the map `(r,r') ↦ (g, r/g, r'/g)` with `g = gcd(r,r')` is injective, lands in
   `Y^k × Y^{ℓ−k} × Y^{ℓ−k}`, and carries `1/[r,r']` to `1/(g·(r/g)·(r'/g))`
   because `g·[r,r'] = r·r'`. Pricing each factor by the already-existing
   `sum_one_div_image_prod_le` (#3521) gives

     `∑_{r,r' ∈ Y^ℓ} 1/[r,r'] ≤ (ℓ+1)·σ^ℓ`,  `σ = ∑_{p∈Y} 1/p ≤ 1`,

   and `σ ≤ 1` is free, since `Y ⊆ (P, 2P]` has at most `P` elements each larger
   than `P`. Landed as #3536, #3539, #3541, #3542.

6. **III-2's *statement* is in the wrong normalisation.** The note asks for
   `∑ g(n)²/n²`. The in-tree sharp mean value theorem
   `intervalIntegral_norm_sq_poly_le_sharp_ratio` sends a polynomial
   `∑ (c n/n)·e(−ξ log n)` to `e^π(T/A + 2R)·∑ ‖c n‖²/n` — weight `1/n`. The
   `1/n²` form predates that normalisation and no consumer takes it. The ratio
   must also stay free: `Q^ℓ·R` is supported on `(P^ℓA', 2^{ℓ+1}P^ℓA']`, so a
   dyadic statement would not reach it.

7. **§4.3(a) understates the collar condition, and no absolute `C` is
   available.** The report prices *one* collar at `e^π(T/A+2)·Σ_{collar}1/n
   ≈ 3e^π/N_j`, compares that to `𝔅`, and reads off `N_j ≥ C/ε³` at **absolute**
   `C`. The quantity the tree produces — the error half of
   `setIntegral_norm_sq_cell_prime_block_le` — is the *assembled* one, and it
   carries two factors the report's estimate does not: the Cauchy–Schwarz factor
   `#I` over cells (they are not orthogonal on `G`) and the weight
   `S₂ = ∑_v (∑_{p∈𝒞_v}1/p)²`. Since `#I ≍ 2N log(Q_j/P_j)` grows **linearly in
   `N`**, it cancels the `1/N` that the collar ratio buys, and `C` cannot be
   taken absolute. The leg is nonetheless fine, by a second decay the report does
   not use: an `e`-adic cell has multiplicative width `e^{1/(2N)}`, so
   `σ_v = O(1/(N log P_j))` and `∑_v σ_v² ≤ (max_v σ_v)·∑_v σ_v` supplies a
   second `1/N`. Honest condition: `N ≥ 64·#I·X·S₂/(κc₃ε³)`, with `X` the
   per-prime collar cost. In tree as `collar_ratio_le`, `collar_cost_le`,
   `collar_error_le`, `collar_error_le_budget` (#3592) and `collar_weight_le`.

8. **The outer band does not force `γ`, and comparing it to `𝔅` rather than
   `(2A+1)²·𝔅` makes it look impossible.** `band_energy_outer_le` is the one leg
   stated for the **plain** sum, and its right-hand side already factors out the
   plain-to-normalised conversion `(2A+1)²` of §4.1's `P_plain ≈ 2A·F`. Its
   target is therefore `(2A+1)²·𝔅`. Read against `𝔅` instead, it demands
   `K₂ ≳ B′²A/(c₃ε²) ≫ A`, contradicting `S2`'s own `K₂ ≤ A`. Read correctly, the
   `(2A+1)²` cancels and the surviving conditions are
   `γ ≥ 512e^πB′H/(πκc₃ε²A²)` and `γ ≥ H√(1536e^π/(κc₃))/(εA)` — smaller than
   §4.2's two terms by factors of order `(H/A)²` and `H/A`. So §4.2's `γ` is set
   by the slice and the `L` cut of `S2`, not by this leg, and the opposite
   `H`-dependence of the two expressions is not a contradiction. In tree as
   `outer_le_budget` and `outer_weight_gamma_eq` (#3595).

9. **The later-level moment route needs the explicit endpoint `2 ≤ Pmom`, not
   merely `1 ≤ Pmom`.** The assembled VI-5 interface retained only
   `1 ≤ Pmom j r`, but the Mertens/e-adic estimate used to eliminate the cell
   prime sum has the honest domain `2 ≤ P`. This is not derivable from
   `Pmom < p ≤ 2Pmom`: the cell may begin at `Pmom = 1` and contain `p = 2`.
   The scheduled VI-8 capstone therefore carries `2 ≤ Pmom j r` for every later
   cell. It is a harmless endpoint condition for S5, but it must be named.

10. **`N_j ≥ C/ε³` alone does not discharge replacement: an upper-size
    condition is also required.** Converting
    `(A/(N_jp)+1)/(A/p)` into an explicit `O(1/N_j)` cost uses
    `N_j p ≤ A`; the structural floor inequalities `hLA`/`hLB` only compare the
    quotient intervals and do not imply it. With a common level endpoint
    `p ≤ Q_j`, the honest condition is `N_j Q_j ≤ A` (and analogously
    `N_𝒰 Q_𝒰 ≤ A`). VI-8 states these as `hNbb` and `hNuQ`. Thus S3 must be read
    together with this upper compatibility; choosing `N_j` arbitrarily large
    is not valid.

11. **The exceptional Halász schedule needs a numerical long-quotient cutoff.**
    The in-tree explicit Halász shell is available for
    `(A+Δ)/q_v ≥ 10^16`. S6–S7 as written contain no standalone base-size
    hypothesis from which Lean can derive that inequality for every selected
    representative. VI-8 therefore names
    `10^16 ≤ (A+Δ)/q_v` cell by cell (`hBqCutoff`). A downstream instantiation
    may derive it from the concrete S6 endpoints and a sufficiently large
    `A`, but that largeness condition must be stated rather than hidden.

Three further notes, none an erratum. **§4.3(f) is exact and §4.2's `1/320` is
the right round number**: the `𝒰` leg forces `W ≤ (κ/4)^{4/25}·(log A)^{2/625}`
with `2/625 = 1/312.5`, and `2/625 − 1/320 = 3/40000` is *precisely* the slack
that pays for the constant `(4/κ)^{4/25}` (`exceptional_W_le`,
`exceptional_report_exponent_ok`). **The two margins of §4.3 check out**:
`P₁ = W^{200}` against `C/ε³ = C·W^{15/4}` gives `W^{785/4} = W^{196.25}` (stated
`W^{196}`), and `P₁² ≥ C·E/ε²` gives `W^{795/2} = W^{397.5}` (stated `W^{397}`).
**`S5` discharges the only constraint the level-one estimate uses**: at
`η = 1/20`, `2α_j ∈ [7/20, 2/5)` for every `j ≥ 1`, so `2α < 1` holds uniformly
and `2α₁ = 7/20 = 0.35` is §4.2's `1/2 − 3η`.

One further note, not an erratum: V-0/V-1 landed at least as sharp as specified —
`sum_norm_sq_le_integral_of_separated` integrates over `(−T, T+1]` where the
report's `sum_well_spaced_le_intervalIntegral` uses `(−(T+1), T+1)`.

## What the ladder still owes

**Phase III is closed.** `III-2` and the full `III-3` are on main, by the route of
errata items 5 and 6 rather than the one described below; the `[MR]` moment lemma
`le:moment` is now

  `∫_{−T}^{T}‖Q^ℓ·R‖² ≤ e^π(T/(P^ℓA') + 2·2^{ℓ+1})·(ℓ!)²·2^{ℓ+1}(ℓ+1)·σ^ℓ`

(`intervalIntegral_norm_sq_prime_poly_pow_mul_le`), with `σ ≤ 1` derived rather
than assumed.

Still owed: `II-5b` (`E₁` — but see erratum 4: its signature below is not
transcribable, `quotBlock` does not exist), `III-4` (`E_j`), `IV-0` (which needs
the M0R `ℝ → ℂ` generalisation first, and that is a sub-campaign, not a unit:
`plain_sum_le_halasz_of_nonPretentious` is a thin wrapper over
`rieszMean_log_halasz_le`, so the `ℝ`-ness runs the whole depth of the Halász
chain), `IV-3` (the `𝒰` band energy, conditional on the two interfaces of item 3),
and the `VI-1` capstone.

---

# MR-core design report: the INNER mid-frequency band (Track R / [mrt] A.2)

Paper-first session, no Lean written, no builds. Sources read in full:
`scratchpad/n3_design_report.md`; `scratchpad/mr_annals/ShorterIntervals55.tex`
(Matomäki–Radziwiłł, *Multiplicative functions in short intervals*, Annals 2016 —
the v5.5 source, **including the erratum footnote on `1_{(p,m)=1}`**);
`scratchpad/mrt/Chowla.tex` Appendix A (`complex-app`) and §3/§5; and the in-tree
statements of `WindowTK.lean`, `DyadicMVT.lean`, `WindowAssembly.lean`,
`TypicalFactorization.lean`, `RamareIdentity.lean`, `LargeValues.lean`,
`PlancherelHarness.lean`, `HalaszCapstone.lean`.

---

## 0. Executive summary — read this first

1. **The prior report's model of the [MR] core was wrong in its central structural
   claim.** N3-k/l/m assumed a *cascade over exceptional sets*: level `j` produces a
   bad set that gets re-factored at level `j+1`, with the top level calibrated so the
   moment is collision-free. **MR does no such thing.** The `j = 1…J` structure is a
   **partition of the frequency line**, `[T₀,T] = 𝒯₁ ⊔ … ⊔ 𝒯_J ⊔ 𝒰`, and each `𝒯_j`
   is closed in **one shot** by a **single** Ramaré step plus a **single** moment
   computation. Errors do not propagate between levels; there is no "collar error
   re-entering at the next level" to bookkeep. N3-k and N3-l as stated should be
   **deleted**, not repaired.
2. **The calibrated moment is real, but it lives somewhere else and does something
   else.** MR's Lemma `le:Rupest` does set `k = ⌈log T/log P⌉` so that `P^k ≈ T` —
   exactly the prior report's "calibrate the top level to the band length". But (i) it
   bounds only the **cardinality/measure of the exceptional set**, never the band
   energy; (ii) the mechanism is **not** collision-freeness — it is the mean value
   theorem's `(T + N)` with `N = (2P)^k ≈ T`, plus the elementary coefficient bound
   `Σ(b(n)/n)² ≤ P^{-k} k! (Σ_{p∼P}1/p)^k`; and (iii) the answer is
   `|𝒯| ≪ T^{2 log V/log P} V² 5^k k!`, i.e. **`T^{1/2−η}` — polynomially LARGE, not
   super-polynomially small.** The prior report's "measure ≤ `K₂(16k²/P_J)^{k_J}`,
   super-polynomially small" is **refuted**.
3. **A large, concrete, immediately shippable win exists and it dissolves the prior
   report's headline gap.** The prior report declared "the residual gap is the pure
   off-diagonal `4AΔ(logΔ+1)` vs `c₃ε²sA`: a factor `≈128(logΔ+1)/ε²`. **This
   `ε²/logΔ` gain is the entire job of the [MR] core.**" That is only half true: the
   `log Δ` half is **not** number theory at all — it is a defect of the in-tree
   `intervalIntegral_norm_sq_short_poly_le`, which is a log worse than the sharp
   large sieve. **The in-tree Gaussian kit already contains the sharp large sieve**;
   `intervalIntegral_norm_sq_gaussian_diag_le` + a theta-sum bound gives, with no
   number theory,
   `∫_{-T}^{T}‖Σ_{n∈S}(c n/n)·char n ξ‖² ≤ e^π(T/A + 2)·Σ_{n∈S}‖c n‖²/n`
   for `S ⊆ (A, 2A]`. That kills the `logΔ` **everywhere downstream** (outer band
   constant `γ`, collars, collision, `E₁`, `E_j`, `le:Rupest`). Unit **I-2** below;
   it is the single highest-value PR in this design.
4. **What is left after that is exactly `ε²` over the trivial bound — and that is
   genuine MR, and it does NOT close elementarily.** The `𝒯_j` legs (`j = 1…J`), the
   Ramaré collars, the (corrected) collision term, the sifted term (which is
   **identically zero** on `typicalS` — a fact the prior report missed), and the
   exceptional-set *measure* all close with the sharp MVT and elementary input, with
   large margins (§4). The `𝒰` leg does **not**. It structurally requires
   discretisation to a well-spaced set plus **two large-value theorems**, one of which
   (**Halász's inequality for prime-supported Dirichlet polynomials**, MR
   Lemma 8) is proved only via a **Vinogradov–Korobov-type zero-free region for `ζ`**
   and a Mellin contour shift. Mathlib at the pinned revision (`v4.28.0`) has
   **no zero-free region, no PNT, no large sieve, no Halász–Montgomery**
   (`LSeries/Nonvanishing.lean` is qualitative `ζ(1+it) ≠ 0` only). §5 proves that
   every attempt to replace it by continuous integration + the in-tree Halász
   (`plain_sum_le_halasz_of_nonPretentious`) fails by a **positive power of `X`**, not
   by a constant. **This is a hard negative result, stated plainly in §5.**
5. **Second structural finding: `s ≪ A` is expensive and `s ≍ A` is illegal.** The
   `slice_energy_le` error term `3(6U + H·s/A + 2)²·Σ1/n` forces `s ≤ εA/2`, so the
   block ratio is `Δ/A ≍ ε`. Every place where MR uses "the polynomial is over a full
   dyadic range" then costs a power of `A/Δ ≍ 1/ε`. §4 shows all of these are
   affordable **except** that the `𝒰` leg's Halász-pointwise step costs `(A/Δ)² ≍ 4/ε²`
   by partial summation, which forces re-tuning [mrt]'s `W ≤ (log X)^{1/125}` down to
   `W ≤ (log X)^{1/320}`. That is harmless for EDP (it only shrinks the admissible
   `H`-range, and EDP needs only `H → ∞`), but it is a **downstream numerology change
   in [mrt] Theorem `second`** that must be recorded now.
6. **Recommended deliverable shape.** Ship §6 Phases A–C + E as real theorems (≈16
   units, all elementary, they close `𝒯₁…𝒯_J` + collars + collision + the exceptional
   measure) and expose the `𝒰` endgame as **two named, textbook-shaped assumptions**
   (`HalaszLargeValuesAssumption` = Iwaniec–Kowalski Thm 9.6;
   `PrimeLargeValuesAssumption` = [MR] Lemma 8). That replaces the current single
   opaque `MatomakiRadziwillMajorArcAssumption` by two quotable literature statements
   plus a fully machine-checked reduction — a real and auditable improvement in
   assumption quality, and the correct outcome given (4).

---

## 1. What ShorterIntervals55.tex actually says (task 1)

Line numbers refer to `scratchpad/mr_annals/ShorterIntervals55.tex`.

### 1.1 The scale ladder (`:288–:312`)

`η ∈ (0,1/6)`; intervals `[P_j,Q_j]` with `Q₁ ≤ exp(√log X)` and

* **not too far** `(eq:PjQjnottoofar)`  `log log Q_j / (log P_{j−1} − 1) ≤ η/(4j²)`
* **not too close** `(eq:PjQjnottooclose)` `(η/j²)·log P_j ≥ 8 log Q_{j−1} + 16 log j`

realised by `P_j = exp(j^{4j}(log Q₁)^{j−1}log P₁)`, `Q_j = exp(j^{4j+2}(log Q₁)^j)`,
admissible whenever `exp(√log X) ≥ Q₁ ≥ P₁ ≥ (log Q₁)^{40/η}`. `𝒮` = integers with a
prime factor in **every** `[P_j,Q_j]`, `j ≤ J`, `J` maximal with `Q_J ≤ exp(√log X)`.
Identical to `Definition S-def` in Chowla.tex `:323`.

### 1.2 The frequency partition (`:1090–:1120`) — *not* a cascade

With `H_j := j²P₁^{1/6−η}/(log Q₁)^{1/3}` and the **e-adic prime cells**
`Q_{v,H_j}(s) = Σ_{P_j≤q≤Q_j, e^{v/H_j}≤q≤e^{(v+1)/H_j}} f(q)q^{-s}`,
`v ∈ 𝓘_j := [⌊H_j log P_j⌋, H_j log Q_j]`:

> `t ∈ 𝒯_j` iff `j` is the **smallest** index with `|Q_{v,H_j}(1+it)| ≤ e^{−α_j v/H_j}`
> for **all** `v ∈ 𝓘_j`;  `t ∈ 𝒰` iff no such `j` exists.
> `α_j = 1/4 − η(1 + 1/(2j))`, so `α₁ ≤ α₂ ≤ … ≤ α_J`.

`[T₀,T] = 𝒯₁ ⊔ … ⊔ 𝒯_J ⊔ 𝒰` is a **disjoint partition of the `t`-line**, `T₀ =
(log X)^{1/15}`. **There is no error term passed from level `j` to level `j+1`.**

### 1.3 The Ramaré/Buchstab decomposition, Lemma `lem:decomp` (`:817–:885`)

Hypotheses: `a_{mp} = b_m c_p` whenever `p ∤ m`, `P ≤ p ≤ Q`. Conclusion

```
∫_𝒯 |Σ_{X≤n≤2X} a_n n^{-1-it}|² dt
  ≪ H log(Q/P) · Σ_{v∈𝓘} ∫_𝒯 |Q_{v,H}(1+it) R_{v,H}(1+it)|² dt
    + ((T+X)/X)·( 1/H + 1/P + Σ_{X≤n≤2X, (n,∏_{P≤p≤Q}p)=1} |a_n|²/n )
```

Proof anatomy (this is the bookkeeping the prior report could not see):

* Ramaré identity with the **erratum-corrected** weight
  `1/(ω(m;P,Q) + 1_{(p,m)=1})` (`:440`, footnote: the published version wrote `1`,
  breaking their Lemma 12).
* Replace `a_{pm}` by `b_m c_p` when `p ∤ m`; the `p ∣ m` terms are the **collision**
  term and are re-indexed to `X/p² ≤ m ≤ 2X/p²` — i.e. **at the quotient scale
  `X/p²`, not at the block scale.** (This is exactly the fix the prior session's
  counterexample demanded; see §3.4.)
* Split `p` into e-adic cells and **drop** the coupling `X ≤ mp ≤ 2X`; the
  over/under-count telescopes over `v` and leaves **exactly two** collar polynomials,
  over `[Xe^{−1/H}, Xe^{1/H}]` and `[2X, 2Xe^{1/H}]`, with bounded coefficients.
  Their MVT cost is the `1/H`.
* `1/P` is the collision; the last sum is the **sifted** term.
* Cauchy–Schwarz over `v` (this is where the outer factor `H log(Q/P)` comes from),
  MVT (`le:contMVT`) on everything else.

### 1.4 `E₁` (`:1158`) — the only genuinely easy leg

On `𝒯₁`, `|Q_{v,H₁}| ≤ e^{−α₁v/H₁}` pointwise; MVT on `R_{v,H₁}` gives
`(T + Xe^{−v/H₁})/(Xe^{−v/H₁})`; sum the two geometric series in `v`:

```
E₁ ≪ H₁ log Q₁ Σ_v e^{−2α₁v/H₁}(T + Xe^{−v/H₁})e^{v/H₁}/X
   ≪ H₁² log Q₁ · P₁^{−1/2+3η} · (T/(X/Q₁) + 1)
   ≪ (T/(X/Q₁) + 1)·(log Q₁)^{1/3}/P₁^{1/6−η}     by the choice of H₁.
```

### 1.5 `E_j`, `2 ≤ j ≤ J` (`:1166–:1234`) — the "borrow largeness" trick

`𝒯_j = ⋃_{r∈𝓘_{j−1}} 𝒯_{j,r}` where on `𝒯_{j,r}` the **previous** level is LARGE:
`|Q_{r,H_{j−1}}(1+it)| > e^{−α_{j−1}r/H_{j−1}}`. Multiply the integrand by
`(|Q_{r,H_{j−1}}|e^{α_{j−1}r/H_{j−1}})^{2ℓ} ≥ 1` for free. The point of the
multiplication is **length**: `R_{v,H_j}` has length `X/e^{v/H_j}`, far shorter than
the integration range `T`, so its MVT is inefficient; multiplying by `Q_{r,H_{j−1}}^ℓ`
with

```
ℓ_{j,r} = ⌈ (v/H_j) / (r/H_{j−1}) ⌉
```

restores length `≈ X`. Then `le:moment` (`:873`) gives
`∫_{−T}^{T}|Q^{ℓ}R|² ≪ (T/X + 2^ℓ Y₁)(ℓ+1)!²`, and the accounting
`ℓ log ℓ ≤ (v/H_j)·loglog Q_j/(log P_{j−1}−1) + loglog Q_j + 1` is exactly what
`(eq:PjQjnottoofar)` was designed to control. Net:

```
E_j ≪ (T/X + 1)·j⁶Q_{j−1}³·exp( (2v/H_j)(α_{j−1} − α_j + η/(4j²)) )
    ≪ (T/X + 1)·j⁶Q_{j−1}³·exp( −(η/2j²) log P_j )
    ≪ (T/X + 1)/(j²Q_{j−1})   by (eq:PjQjnottooclose).
```

**So `(eq:PjQjnottoofar)` and `(eq:PjQjnottooclose)` are exactly the two conditions
that make the "borrow largeness" trick pay: the first bounds `ℓ log ℓ`, the second
makes `P_j^{−η/2j²}` beat `Q_{j−1}³`.**

### 1.6 `le:moment` (`:873`) and its Shiu input

Coefficients of `Q^ℓ A` are supported in `[X, 2^{ℓ+1}Y₁X]`; the representation count
is `≤ ℓ!·g(n)` with `g` multiplicative, `g(p^k) = k+1` for `p ∈ [Y₁,2Y₁]` and `1`
otherwise; MR invoke **Shiu's theorem** for `Σ_{Y≤n≤2Y}g(n)² ≪ Y`. **Shiu is not
needed**: `Σ_{n≤N}g(n)² ≤ N·Σ_{r,r'} 1/[r,r'] ≤ N·∏_{Y₁≤p≤2Y₁}(1 + 3/p + O(1/p²))
≪ N·exp(3Σ_{Y₁≤p≤2Y₁}1/p) ≪ N` since `Σ_{Y₁≤p≤2Y₁}1/p ≍ 1/log Y₁`. Elementary,
formalisable, unit **III-2**.

### 1.7 `le:Rupest` (`:689`) — the calibrated moment, correctly located

```
P(s) = Σ_{P≤p≤2P} a_p p^{-s}, |a_p| ≤ 1;  𝒯 ⊂ [−T,T] well-spaced with |P(1+it)| ≥ V^{-1}.
Then |𝒯| ≪ T^{2 log V/log P}·V²·exp(2 (log T/log P) loglog T).
```

Proof: `k = ⌈log T/log P⌉`; `Σ(b(n)/n)² ≤ P^{−k}k!(Σ_{p∼P}1/p)^k`; then **the
discrete MVT `le:discMVT` (IK Thm 9.4)** and Chebyshev:
`|𝒯| ≪ V^{2k}(T + (2P)^k)log((2P)^k)P^{−k}k!(Σ1/p)^k ≪ T^{2log V/log P}V²5^k k!`.
**Calibration = making `(2P)^k ≈ T` so the MVT's `(T+N)` is `≈ T`. Nothing to do with
collisions or diagonality.**

### 1.8 The `𝒰` treatment (`:1234–:1310`) — verbatim anatomy

Fresh Ramaré step with a **completely different, much larger prime range unrelated to
`h`**:

```
P = exp((log X)^{1−1/48}),  Q = exp(log X/loglog X),  H = (log X)^{1/48}
⟹ ∫_𝒰|F|² ≪ H²(log X)² ∫_𝒰|Q_{v,H}R_{v,H}|² + (T/X+1)(1/H + 1/P + log P/log Q).
```

Then, in order:

1. **Discretise**: a well-spaced `𝒯 ⊆ 𝒰` with `∫_𝒰|QR|² ≤ 2Σ_{t∈𝒯}|Q(1+it)|²|R(1+it)|²`.
2. **`|𝒯| ≪ T^{1/2−η}X^{o(1)}`** by `le:Rupest` applied at level `J`
   (uses `P_J ≥ (log X)^{2/η}`).
3. **Split** `𝒯 = 𝒯_S ⊔ 𝒯_L` at `|Q_{v,H}(1+it)| = (log X)^{−100}`.
4. **`𝒯_S`**: `Σ_{𝒯_S}|QR|² ≤ (log X)^{−200}Σ_𝒯|R|²`, and `Σ_𝒯|R|²` is bounded by
   **`le:Hallargevalint` (Halász's inequality for integers, IK Thm 9.6)**:
   `≪ (N + |𝒯|√T)log(2T)Σ|a_n|²`. Result `≪ (log X)^{−199}`.
5. **`𝒯_L`**: `|𝒯_L| ≪ exp((log X)^{1/48+o(1)})` again by `le:Rupest`;
   `max|R_{v,H}| ≪ (log X)^{−ρ+o(1)}·(log Q/log P)` by **`le:Halappl`** (= Halász's
   theorem on multiplicative functions + a smooth-number count + `le:Sinclexcl`);
   and `Σ_{𝒯_L}|Q|²` by **`le:Hallargevalprimes` (Halász for primes)**:
   `≪ (P + |𝒯_L|P exp(−log P/(log T)^{2/3+ε})(log T)²)Σ_{p∼P}|a_p|²/log P`.
6. Assemble: `∫_𝒰|F|² ≪ H(log X)²(log X)^{−1/8+o(1)}(log Q)²/(log P)⁴ + …
   ≪ (T/X+1)(log X)^{−1/48+o(1)}`.

**`le:Hallargevalprimes` is proved by duality + a Mellin contour shift of
`ζ'/ζ` into the zero-free region `σ = 1 − c(log T)^{−2/3+ε}`**, using
`ζ'/ζ(σ+it) ≪ (log T)^{5/3+ε}` there (Ivić (1.52)). Two features are load-bearing:
(i) the coefficient normalisation is `Σ|a_p|²/log P` — **one logarithm better** than
IK 9.6; (ii) the off-diagonal is `|𝒯|·P·exp(−log P/(log T)^{2/3+ε})` — **not**
`|𝒯|√T`. §5 shows both are indispensable.

### 1.9 What [mrt] changes (`Chowla.tex:975–:995`)

Only `le:Halappl`: real-valuedness is replaced by the two-part `𝒯₀/𝒯₁` split around
the pretentious direction `t₁`, giving `ρ := 1/6 − 1/(3π) − ε ≈ 0.0606` in place of
`1/16`, and **`1/48 ↦ ρ/3 > 1/50` in the definitions of `P, Q, H` in the treatment of
`𝒰`**. Everything else in Proposition 1 is quoted unchanged. So the `𝒰`-parameters
we must use are

```
P_𝒰 = exp((log X)^{1−1/50}),  Q_𝒰 = exp(log X/loglog X),  N_𝒰 = (log X)^{1/50}.
```

---

## 2. Verdict on the prior report's RED units and no-gos (task 1, cont.)

| prior claim | verdict |
|---|---|
| N3-k "thin-block factorization with collar error", `δ ≈ ε²s/(AE²logΔ)` | **DELETE.** MR's cells are **e-adic** (`e^{v/H}`), not `(1+δ)`-thin; the collar cost is `1/H` per *level*, telescoped to **two** polynomials, not per-block. The "thin vs fat" tension of no-go (ii) does not arise because the collar is priced by the sharp MVT at the **full** block scale, and `1/N_j ≤ cε³` is met by `N_j ≍ 1/ε³` — a *parameter choice*, not a trade-off. |
| N3-l "cascade step: re-factor the level-`j` bad set at level `j+1`" | **DELETE.** No such step exists. `𝒯_1,…,𝒯_J,𝒰` partition the `t`-line; each `𝒯_j` is one Ramaré step + one moment. |
| N3-m "top-level calibrated exceptional measure, super-polynomially small" | **REFUTE the smallness; KEEP the calibration.** `le:Rupest` calibrates `k = ⌈log T/log P⌉` but delivers `|𝒯| ≪ T^{1/2−η}` — *polynomially large*. Retained as unit **V-1**, with the correct (large) bound. |
| no-go (i): raw fibre C–S loses `E²·logΔ`, C–S must go **through** the prime polynomial; `g` must be completely multiplicative | **CONFIRMED** and it is exactly MR's `a_{pm} = b_m c_p` hypothesis in `lem:decomp`. Keep `CompletelyMultiplicativeC` in the capstone. |
| no-go (ii): factorization/moment tension has no single block width | **SUPERSEDED.** With e-adic cells and the sharp MVT there is no tension; see §4. The `logΔ` half of the tension was an artefact of the lossy in-tree MVT. |
| no-go (iii): single-shot Chebyshev cannot reach the needed rarity; only a calibrated cascade closes elementarily | **HALF-CONFIRMED, HALF-REFUTED.** Confirmed: single-shot Chebyshev is nowhere near enough, and `𝒰` is genuinely the hard leg. Refuted: **no elementary route closes it at all** — not the cascade, not calibration, not collision-freeness. See §5. |
| "one 𝒰-level suffices for typicality and the collision leg" | **CONFIRMED** for the collision leg (§3.4) and, better, the **sifted term vanishes identically** on `typicalS` — the prior report budgeted for it unnecessarily. |
| "the `ε²/logΔ` gain is the entire job of [MR]" | **HALF-REFUTED.** The `1/logΔ` is a defect of `intervalIntegral_norm_sq_short_poly_le` and is removable in-tree (unit **I-2**). The `ε²` is the real MR job. |

---

## 3. Transfer to the repo's band setting

### 3.1 The two settings, aligned

| MR | repo |
|---|---|
| `X` | `A` (block anchor) |
| `[X,2X]`, length `X` | `(A, A+Δ]`, `Δ = s+2H+4U` |
| `h` (interval) | `H` (window) |
| `t` | `2πξ` |
| `F(1+it) = Σ f(n)n^{−1−it}` | `F(ξ) = Σ_{m∈typicalS}(g m/m)·char m ξ` |
| `∫_{T₀}^{X/h}` | `∫_{K ≤ |ξ| ≤ K₂}`, `K₂ = γB′A/(2πH)` |
| trivial bound `T/X + 1` | trivial bound `e^π(K₂/A + 2)·Σ_{block}1/m` |
| target: beat trivial by `ε²` | target: beat trivial by `ε²` |

`char m ξ := ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)` throughout.

**The two settings have the same shape** — beat the mean-value theorem by `ε²` —
provided one measures against the *sharp* MVT. The prior report's despair (`4AΔ(logΔ+1)`
vs `c₃ε²sA`) mixed the `logΔ` defect into this comparison.

### 3.2 The block-ratio constraint `Δ/A ≍ ε` (new, load-bearing)

`slice_energy_le` (`WindowAssembly.lean:784`) carries the error term
`(3U² + 3(6U + H·s/A + 2)²)·Σ_{Ioc A (A+s)}1/n` against a budget `ε²H²Σ1/n`. Hence

```
6U + H·s/A + 2 ≤ εH/√3   ⟹   s ≤ εA/2   (with U ≤ εH/24).
```

Also `hfit : A + s + 2H + 4U ≤ 2A+1` and `hΔA : Δ ≤ A` cap `s ≤ A − 2H − 4U`. So the
usable regime is `Δ/A ≍ ε = W^{−5/4}` — **the block is a genuine dyadic range shrunk
by only `W^{5/4}`, not by a power of `A`.** This is much better than the prior
report's `s ≤ cεA/√(logΔ)`, whose `√logΔ` came from the lossy MVT and disappears with
unit I-2. Every "short block vs dyadic block" loss below is therefore a power of
`1/ε = W^{5/4}`, never a power of `A`. **All of them are affordable except one
(§5.3).**

### 3.3 The sharp short-block MVT is already in reach (the key unit)

`intervalIntegral_norm_sq_gaussian_diag_le` (`DyadicMVT.lean:1855`) states

```
∫ ξ in (-T)..T, ‖Σ_{n∈S}(a n · r n)·char n ξ‖²
  ≤ Σ_{m∈S} ‖a m‖²·r m · Σ_{n∈S} r n · (e^π · T · exp(−πT²(log m − log n)²)).
```

Take `r n = 1/n`. For `m,n ∈ (A, 2A]`, `|log m − log n| ≥ |m−n|/(2A)`, so the inner sum
is `≤ (1/A)Σ_{k∈ℤ}exp(−πT²k²/(4A²)) ≤ (1/A)(1 + 2A/T)`. Hence

```
∫_{−T}^{T} ‖Σ_{n∈S}(c n/n)·char n ξ‖² ≤ e^π·(T/A + 2)·Σ_{n∈S}‖c n‖²/n .
```

This is the Montgomery–Vaughan/Selberg large sieve for the frequencies `log n`, with
constant `e^π ≈ 23.1` instead of the optimal `2`, and **no logarithm**. Compare
in-tree N1: `2LΣ1/n² + (logΔ+1)Σ1/n`. In plain terms N1 gives `8LΔ + 4AΔ(logΔ+1)`
where the truth is `(2L + 2A)Δ`. **Unit I-2 buys back a full `log Δ` in every
downstream estimate**, and directly removes the `√(logΔ)` from `γ` in the outer band.

### 3.4 The corrected collision unit (the prior N3-g was false)

Prior counterexample: `P = {p}`, `S = {n₀}`, `p²∣n₀`, `p² ≈ A` gives LHS `2L/n₀²` vs a
claimed RHS `≈ 8L/n₀³`. The error was pricing the fibre polynomial at the **block**
scale. MR's own re-indexing (`:850`) is at `X/p² ≤ m ≤ 2X/p²`. Corrected recipe:

1. The collision term is `C(ξ) = Σ_{p∈P} C_p(ξ)`,
   `C_p(ξ) = Σ_{n∈S, p²∣n}(g n/n)/ω_P(n)·char n ξ`.
2. Reindex `n = p²k`, `k ∈ (A/p², (A+Δ)/p²]`; complete multiplicativity + `char_mul`
   pull out `(g p²/p²)·char (p²) ξ`, leaving a **quotient-scale** polynomial.
3. Cauchy–Schwarz over `p` with weights `1/p`:
   `|C|² ≤ (Σ_p 1/p)·Σ_p p·|C_p|²`.
4. Apply the **sharp MVT at scale `A/p²`** to each `C_p`:
   `∫_{−T}^{T}|C_p|² ≤ p^{−4}·e^π(Tp²/A + 2)·Σ_k 1/k ≤ e^π(T/(p²A) + 2/p⁴)(Δ/A)`.
5. Total `∫_{−T}^{T}|C|² ≤ e^π·E·(Δ/A)·[(T/A)·E + 2/P₁²]`, `E = Σ_{p∈P}1/p`.

Check against the counterexample: RHS `≥ e^π·2L/(p²Ak₀) ≥ LHS = 2L/(p⁴k₀²)` iff
`e^π p²k₀ ≥ 2A`, true since `p² ≈ A`, `k₀ ≥ 1`. ✔ Budget check in §4.

### 3.5 The sifted term is identically zero

MR's `lem:decomp` error carries `Σ_{X≤n≤2X, (n,∏_{P≤p≤Q}p)=1}|a_n|²/n`. For
`a_n = f(n)1_𝒮(n)` and `[P,Q] = [P_j,Q_j]` with `j ≤ J`, **every `n ∈ 𝒮` has a prime
factor in `[P_j,Q_j]`, so this sum is empty.** In the repo this is
`mem_typicalS` + `hasFactorInAll_cons` — a one-line `simp`. The prior report's N3-h
sibling pair (window Turán–Kubilius for the atypical complement) is still needed, but
**only for the harness-level split `Ioc \ typicalS`**, i.e. `window_typicalS_complement_le`
which is already on main; it is *not* needed inside the band lemma. Good news: one
whole leg of the prior ladder is free.

The sifted term is *not* free in the `𝒰` leg, where `[P_𝒰, Q_𝒰]` is unrelated to `𝒮`
and one pays `log P_𝒰/log Q_𝒰 = (log A)^{−1/50}loglog A`. **That single term is the
origin of the `(log X)^{−1/50}` in [mrt] Proposition A.2.**

---

## 4. Constants end-to-end for the inner band (task 3)

### 4.1 Budget normalisation

Per the prior report's verified slice arithmetic, the band's share of the slice budget
is `∫_band ‖P_plain‖² ≤ c₃ε²sA` with `c₃ = 1/(48C)`. Writing `P_plain ≈ 2A·F` for the
normalised `F(ξ) = Σ(g m/m)char m ξ`:

```
BUDGET:   ∫_{K ≤ |ξ| ≤ K₂} |F(ξ)|² dξ  ≤  c₃ε²·(Δ/A)/8  =:  𝔅.
TRIVIAL:  ∫_{−K₂}^{K₂}|F|² ≤ e^π(K₂/A + 2)(Δ/A) ≈ 3e^π(Δ/A)   (once K₂ ≤ A).
```

Ratio `TRIVIAL/𝔅 = 24e^π/c₃ε²`. **Must beat trivial by `ε²`, exactly as MR.** The
factor `Δ/A` cancels — this is why `Δ/A ≍ ε` costs nothing at this level.

### 4.2 Parameters (EDP calibration, [mrt] `Theorem second`)

```
(log H)^5 ≤ W ≤ (log A)^{1/320}   [re-tuned; was 1/125 — see §5.3]
ε = W^{−5/4}   (so ε² = W^{−5/2} is the required saving)
P₁ = W^{200},  Q₁ = H/W³,  η = 1/20,  α_j = 1/4 − η(1 + 1/(2j)),  2α₁ = 1/2 − 3η = 0.35
[P_j,Q_j] for j>1 by (eq:PjQjchoice);  J = max{j : Q_j ≤ exp(√log A)}
N_j := e-adic resolution at level j  (MR's H_j)
𝒰-block:  P_𝒰 = exp((log A)^{1−1/50}),  Q_𝒰 = exp(log A/loglog A),  N_𝒰 = (log A)^{1/50}
K₂ = γB′A/(2πH),  γ = 34/(√c₃ ε) + 3072B′/(πc₃ε²H)   [√(logΔ) GONE — unit I-2]
⟹ T := K₂,  T/A = γB′/(2πH) =: C_γ/(εH),  C_γ = O(B′).
```

### 4.3 Leg-by-leg arithmetic and margins

**(a) Collars** (two polynomials of length `A/N_j`, coefficient modulus `≤1`):

```
cost = e^π(T/A + 2)·Σ_{collar}1/n ≈ 3e^π/N_j  ≤ c₅·𝔅 = c₅c₃ε³/8
⟹ N_j ≥ C/ε³ = C·W^{15/4}.                    ← binding, but a free parameter
```

**(b) Sifted**: `= 0` (§3.5). **Margin: ∞.**

**(c) Collision** (§3.4), with `E = Σ_{P₁≤p≤Q₁}1/p ≈ log(log Q₁/log P₁) ≤ loglog H`:

```
e^πE[(C_γ/(εH))E + 2/P₁²] ≤ c₄c₃ε³/8·(A/Δ)  →  two conditions:
  H ≥ C·E²/ε³ = C(loglog H)²W^{15/4}      ✔ since H ≥ W^{250} and W ≥ (log H)^5
  P₁² ≥ C·E/ε²  i.e. W^{400} ≥ C(loglog H)W^{5/2}   ✔ margin W^{397}.
```

**(d) `E₁`** (level 1, `𝒯₁`), with the sharp MVT and `Σ_{block}1/m ≈ Δ/A`:

```
E₁ ≲ e^π(Δ/A)·N₁²·log Q₁ ·[ (T/A)·Q₁^{1/2+3η}/(1−2α₁) + 2P₁^{−1/2+3η}/(2α₁) ]
main gain term:  N₁²log Q₁·P₁^{−0.35} = C W^{7.5}·log H·W^{−70} = C W^{−62.5}log H
                 need ≤ c₇ε² = c₇W^{−5/2}  ⟺  log H ≤ C W^{60}    ✔ MARGIN W^{60}
T-term:          N₁²log Q₁·(C_γ/(εH))·Q₁^{0.65} ≈ C W^{8.75}(log H)H^{−0.35}
                 need ≤ c₇W^{−5/2}  ⟺  H^{0.35} ≥ C W^{11.25}log H  ✔ MARGIN W^{76}
```

**(e) `E_j`, `2 ≤ j ≤ J`.** Transfers with one relaxation: in `le:moment` bound the
short-block factorisation count `g_block(n) ≤ g_dyadic(n)` pointwise and use the
elementary Euler product of §1.6. Cost: a factor `A/Δ = 2/ε`. Net

```
E_j ≪ (Δ/A)·(A/Δ)·1/(j²Q_{j−1}) = 1/(j²Q_{j−1}) ≤ 1/(j²P₁)
need ≤ c·ε³ ⟺ P₁ ≥ C/ε³ = CW^{15/4};  P₁ = W^{200}   ✔ MARGIN W^{196}.
```

**(f) `𝒰`.** MR/[mrt] deliver `(log A)^{−1/50+o(1)}` relative to `(T/A+1)`. Two of our
deviations cost:

* the Halász-pointwise bound on `R_{v,N_𝒰}` is applied to a **short** sum; partial
  summation from the long-sum in-tree Halász (`plain_sum_le_halasz_of_nonPretentious`)
  costs `A/Δ = 2/ε`, squared `4/ε²`;
* the budget is `ε³` rather than `ε²` (factor `Δ/A = ε/2` on the left as well) — these
  partly cancel, leaving one net factor `2/ε`:

```
(4/ε²)·(log A)^{−1/50} ≤ c₈ε³   ⟺   (log A)^{1/50} ≥ C ε^{−5} = C W^{25/4}
                                 ⟺   W ≤ C (log A)^{4/1250} ≈ (log A)^{1/313}.
```

Hence the re-tuned `W ≤ (log A)^{1/320}` of §4.2. **This is a calibration, not a
margin: the `𝒰` leg is exactly tight, as it is in MR.** EDP is unaffected in kind — it
needs only that some `W` with `(log H)^5 ≤ W` be admissible, i.e.
`H ≤ exp((log A)^{1/1600})`, which still lets `H → ∞`.

### 4.4 The final schedule constraint set

```
S1  1 ≤ Δ ≤ A,  Δ = s+2H+4U,  3H ≤ A,  2U ≤ H,  U ≤ εH/24,  s ≤ εA/2
S2  γ ≥ 34/(√c₃ ε) + 3072B′/(π c₃ ε² H);  K₂ = γB′A/(2πH);  K₂ ≤ A
    L ≥ 7√s·A·B′/(π√c₃·εH^{3/2});  K₂ ≤ L ≤ A′A/(4π)
S3  N_j ≥ C/ε³   for every level j, and N_𝒰 = (log A)^{1/50}
S4  P₁ = W^{200},  Q₁ = H/W³,  η = 1/20, (eq:PjQjnottoofar)+(eq:PjQjnottooclose),
    J = max{ j : Q_j ≤ exp(√log A) }
S5  α_j = 1/4 − η(1 + 1/(2j));  ℓ_{j,r} = ⌈(v/N_j)/(r/N_{j−1})⌉
S6  P_𝒰 = exp((log A)^{1−1/50}), Q_𝒰 = exp(log A/loglog A)
S7  (log H)^5 ≤ W ≤ (log A)^{1/320},  ε = W^{−5/4},  H ≥ W^{250}
```

**Everything in S1–S6 closes with the stated margins. S7's upper bound is where the
`𝒰` leg is consumed exactly, and the `𝒰` leg is not provable in-tree (§5).**

---

## 5. The negative result (task 4)

> **Claim.** At EDP scales the inner band does **not** close by elementary means, nor
> by any combination of the in-tree toolkit with the completed M0R Halász theorem. The
> obstruction is localised in one leg (`𝒰`) and, inside it, in one statement (a
> Halász-type large-value inequality for prime-supported Dirichlet polynomials), whose
> only known proof uses a Vinogradov–Korobov-type zero-free region for `ζ`.

### 5.1 Sup-times-measure pricing of `𝒰` fails by a power of `A`

`∫_𝒰|F|² ≤ |𝒰|·sup_band|F|²`. With `|𝒰| ≲ T^{2α_J+o(1)}` (the *correct*, large,
`le:Rupest` bound of §1.7) and `sup|F| ≪ e^{−M/2}·polylog` from the in-tree Halász:
we would need `T^{2α_J}e^{−M} ≤ ε²`. Since `M ≤ (1+o(1))loglog A` always, this forces
`α_J ≤ ρ·loglog A/log T`, and then the `𝒯_J` gain `P_J^{−2α_J} = exp(−2α_J log P_J) ≥
exp(−log W/(2√log A)) = 1 − o(1)`: **no gain at all.** The tension
`P^{−2α} ≤ ε²` (needs `α ≥ log(1/ε)/log P`) versus `T^{2α}e^{−M} ≤ ε²` (needs
`α ≤ ρ loglog A/log T`) is only satisfiable when `log P ≥ log(1/ε)log T/(ρ loglog A)`,
i.e. `P ≥ exp(c log A/loglog A)` — which is precisely MR's `Q_𝒰`, and then the *sifted*
term `log P/log Q` is `Ω(1)`. **Circular. Dead.**

### 5.2 Continuous integration over `[−T,T]` fails by `exp(log A/loglog A)`

Suppose we abandon discretisation and bound `∫_𝒰|Q_vR_v|² ≤ (sup_𝒰|Q_v|²)∫_{−T}^{T}|R_v|²`
with the sharp MVT. `R_v` has length `A e^{−v/N_𝒰}` and

```
∫_{−T}^{T}|R_v|² ≤ e^π(T e^{v/N_𝒰}/A + 2)(Δ/A),   e^{v/N_𝒰} up to Q_𝒰 = exp(log A/loglog A).
```

The factor `T·Q_𝒰/A = C_γ Q_𝒰/(εH) = exp((1+o(1))log A/loglog A)` is **super-polynomially
large**. Symmetrically, bounding `sup|R_v|` by Halász and integrating `|Q_v|²` gives an
MVT term `T/(P_𝒰 log P_𝒰) ≈ A^{1−o(1)}`. **Both directions blow up by `A^{1−o(1)}`.**
Choosing `Q_𝒰 ≤ ε³H` to kill the first blow-up forces `log Q_𝒰/log P_𝒰 ≥ 1/(cε²)` from
the sifted constraint, and then the trivial `sup|Q_v| ≤ 1/(N log P_𝒰)` route gives
`≥ 2/(c²ε⁴) ≫ ε²`. **Irreconcilable: the sift wants `log Q ≫ log P`, the prime
polynomial wants `log Q ≪ log P`.** Only a large-value theorem breaks the tie.

### 5.3 Even *with* discretisation, the integer large-values theorem is not enough

Replacing `le:Hallargevalprimes` by `le:Hallargevalint` in step 5 of §1.8 replaces the
off-diagonal `|𝒯_L|·P·exp(−log P/(log T)^{2/3+ε})` by `|𝒯_L|·√T`, and the coefficient
normalisation `Σ|a_p|²/log P` by `Σ|a_p|²`. Redoing MR's computation with MR's own
parameters:

```
prime version total exponent :  1/48 + 2 − 1/8 + 2 − 47/12 = −1/48       (MR's answer)
integer version              :  the same minus the two savings
                                log P·log(2T) = (log X)^{47/48}·log X
                             ⟹  exponent ≈ +1.96 .
```

`|𝒯_L|√T ≈ X^{1/2+o(1)}` versus `P_𝒰 = exp((log X)^{47/48}) = X^{o(1)}`: the integer
version's off-diagonal exceeds the diagonal by `X^{1/2−o(1)}` and no re-optimisation of
`(P_𝒰,Q_𝒰,N_𝒰)` fixes it, because `P_𝒰 ≥ X^{1/2}` would force `log Q_𝒰/log P_𝒰 = O(1)`,
killing the sift term. **`le:Hallargevalprimes` is indispensable.**

### 5.4 Exactly what is missing

| input | statement | status | verdict |
|---|---|---|---|
| **N-1** continuous MVT / large sieve | `∫_{−T}^{T}|A(it)|² ≪ (T+N)Σ|a_n|²` | **reachable in-tree** via the Gaussian kit (unit I-2) | ✅ ship it |
| **N-2** discrete MVT for well-spaced points (IK 9.4) | `Σ_{t∈𝒯}|A(it)|² ≪ (T+N)log2N·Σ|a_n|²` | **replaceable** by Gallagher's Sobolev lemma `Σ_{t∈𝒯}|A|² ≤ ∫(|A|²+2|A||A′|)` + N-1, at a cost of `(log N)²` — absorbed by `5^k k!` in `le:Rupest` | ✅ ship it (unit V-0/V-1) |
| **N-3** Halász–Montgomery large values for integers (IK 9.6) | `Σ_{t∈𝒯}|A(it)|² ≪ (N+|𝒯|√T)log2T·Σ|a_n|²` | needs duality + `ζ(−iτ) ≪ |τ|^{1/2}` (functional equation + Stirling on vertical lines) + the Hilbert inequality `Σ_{r≠r'}|t_r−t_{r'}|^{−1} ≪ R log R`. Mathlib has `riemannCompletedZeta` and a functional equation; Stirling on vertical strips is partial. | ⚠️ **hard but conceivable** (multi-month) |
| **N-4** Halász large values for **primes** ([MR] Lemma 8) | `Σ_{t∈𝒯}|P(it)|² ≪ (P + |𝒯|P e^{−log P/(log T)^{2/3+ε}}(log T)²)Σ_p|a_p|²/log P` | needs a **Vinogradov–Korobov-type zero-free region** for `ζ` and `ζ'/ζ ≪ (log T)^{5/3+ε}` there, plus a Mellin contour shift. Mathlib has **no** zero-free region, **no** PNT (`LSeries/Nonvanishing.lean` is qualitative only). | ❌ **out of reach** |
| **N-5** Halász on multiplicative functions | `le:Halappl` | **IN TREE** (`plain_sum_le_halasz_of_nonPretentious`), modulo ℝ→ℂ, the `1/(ω+1)` wrapper, `le:Sinclexcl` and a Rankin smooth-number count | ✅ wire it |
| **N-6** Shiu | `Σ_{Y≤n≤2Y}g(n)² ≪ Y` | **not needed**; elementary Euler product suffices (§1.6) | ✅ ship it |

**Bottom line: the elementary cascade does not close, and neither does anything else
short of N-4. What would additionally be needed is precisely a quantitative
zero-free region for `ζ` on `σ ≥ 1 − c(log T)^{−2/3+ε}` with the derived bound
`ζ'/ζ(σ+it) ≪ (log T)^{5/3+ε}`, or any substitute yielding
`Σ_{n∼P}Λ(n)n^{iτ} = 𝓕(τ)·P + O(P e^{−(log P)^{δ}})` uniformly for `|τ| ≤ T`.**
That is a genuinely deep, currently unformalised piece of analytic number theory.

---

## 6. The corrected, dependency-ordered unit ladder (task 2)

Conventions: `char m ξ := ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)`;
band sets `{ξ : ℝ | K ≤ |ξ| ∧ |ξ| ≤ K₂}` (volume `setIntegral`); window integrals
`∫ ξ in (-L)..L` (`intervalIntegral`). Status: **G** = ship now, **A** = statement
stable / proof route clear, **X** = assumption interface (not provable in-tree).

### Phase I — the sharp large sieve (do this first; it changes every constant)

**I-1 (G) — theta-sum over a short block.** New, `DyadicMVT.lean`.
```lean
theorem sum_exp_neg_sq_log_diff_le (A : ℕ) (hA : 1 ≤ A) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioc A (2*A)) (m : ℕ) (T : ℝ) (hT : 0 < T) :
    ∑ n ∈ S, Real.exp (-(π*T^2*(Real.log m - Real.log n)^2))
      ≤ 1 + 2*(A:ℝ)/T
```
*Sketch.* (1) log-separation: for `m,n ∈ (A,2A]`, `|log m − log n| ≥ |m−n|/(2A)` — from
`Real.log_le_sub_one_of_pos`/`Real.add_one_le_exp` or directly
`log n − log m = ∫_m^n dt/t ≥ (n−m)/(2A)`; the repo has the ingredient shape at
`LargeValues.lean:112 log_sub_log_ge`. (2) monotone re-indexing `n ↦ n − m` into `ℤ`,
then `Σ_{k∈ℤ}e^{−ck²} ≤ 1 + 2∫₀^∞ e^{−cu²}du = 1 + √(π/c)` with `c = πT²/(4A²)`.
*Risks:* the integral comparison — use `Finset.sum_le_integral`-style monotone
comparison on `k ≥ 1` (the repo already does a shell decomposition of this kind in
`prime_gaussian_block_le`, `DyadicMVT.lean:2648`); `Real.integral_exp_neg_mul_sq` /
`integral_gaussian` exists in Mathlib.

**I-2 (G) — ★ the sharp short-block MVT (log-free).** `DyadicMVT.lean`, beside N1.
```lean
theorem intervalIntegral_norm_sq_short_poly_le_sharp (A Δ : ℕ)
    (hA : 1 ≤ A) (hΔ : 1 ≤ Δ) (hΔA : Δ ≤ A) (S : Finset ℕ)
    (hSlow : ∀ n ∈ S, A < n) (hShigh : ∀ n ∈ S, n ≤ A + Δ)
    (c : ℕ → ℂ) (T : ℝ) (hT : 0 < T) :
    ∫ ξ in (-T)..T,
        ‖∑ n ∈ S, (c n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2
      ≤ Real.exp π * (T/(A:ℝ) + 2) * ∑ n ∈ S, ‖c n‖^2/(n:ℝ)
```
*Sketch.* `intervalIntegral_norm_sq_gaussian_diag_le S c (fun n => 1/n) _ T hT`, then
I-1 on the inner sum with `1/n ≤ 1/A`, then `e^π·T·(1/A)(1 + 2A/T) = e^π(T/A + 2)`.
*Risks:* matching `(c n/(n:ℂ))` with `a n * ((r n : ℝ) : ℂ)` — a cast rewrite
(`Complex.ofReal_inv`, `div_eq_mul_inv`); the `Δ ≤ A` hypothesis is what puts `S` in
`(A,2A]` for I-1.

**I-3 (G) — bounded-coefficient corollary.**
```lean
theorem intervalIntegral_norm_sq_short_poly_le_sharp_of_bound (A Δ : ℕ)
    (hA : 1 ≤ A) (hΔ : 1 ≤ Δ) (hΔA : Δ ≤ A) (S : Finset ℕ)
    (hSlow : ∀ n ∈ S, A < n) (hShigh : ∀ n ∈ S, n ≤ A + Δ)
    (c : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B) (hc : ∀ n, ‖c n‖ ≤ B)
    (T : ℝ) (hT : 0 < T) :
    ∫ ξ in (-T)..T, ‖∑ n ∈ S, (c n/(n:ℂ)) * (char n ξ)‖^2
      ≤ Real.exp π * (T/(A:ℝ) + 2) * B^2 * ∑ n ∈ S, (1:ℝ)/(n:ℝ)
```
*Sketch.* `‖c n‖² ≤ B²`, `Finset.sum_le_sum`. *Risks:* none.

**I-4 (G) — sharp outer band.** Re-cut `ring_energy_decay_le` and `band_energy_outer_le`
(`WindowAssembly.lean:1610, :1916`) against I-3, replacing
`(Real.log Δ + 1)*(∑ 1/n)` by `e^π·2*(∑ 1/n)` throughout. Statement identical modulo
that substitution. *Risks:* mechanical; keep the old lemmas (Deprecated.lean) since
`slice_energy_le` consumers reference them.

### Phase II — the Ramaré / e-adic decomposition of the band polynomial

**II-1 (G) — e-adic prime cells.** `TypicalFactorization.lean` or a new `BandDecomp.lean`.
```lean
def eadicCell (P : Finset ℕ) (N : ℕ) (v : ℕ) : Finset ℕ :=
  P.filter (fun p => Real.exp ((v:ℝ)/N) ≤ (p:ℝ) ∧ (p:ℝ) < Real.exp (((v:ℝ)+1)/N))

theorem eadicCell_biUnion (P : Finset ℕ) (N v₀ v₁ : ℕ)
    (hlo : ∀ p ∈ P, Real.exp ((v₀:ℝ)/N) ≤ (p:ℝ))
    (hhi : ∀ p ∈ P, (p:ℝ) < Real.exp (((v₁:ℝ)+1)/N)) :
    (Finset.Ico v₀ (v₁+1)).biUnion (eadicCell P N) = P
```
*Sketch.* `Finset.ext`; membership `⟺ ∃ v, v/N ≤ log p < (v+1)/N` via
`Nat.floor (N * Real.log p)`; disjointness from the half-open cells.
*Risks:* `Real.exp/Nat.floor` interface friction; prefer to phrase the cell by
`⌊N·log p⌋ = v` (a `Nat` equation) and derive the exp inequalities as lemmas.

**II-2 (A) — ★ the decomposition lemma (analogue of `lem:decomp`).** New.
```lean
theorem typicalS_phase_eadic_decomp (g : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC g) (A Δ N : ℕ) (hN : 0 < N)
    (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (rest : List (Finset ℕ))
    (v₀ v₁ : ℕ) (hcov : (Finset.Ico v₀ (v₁+1)).biUnion (eadicCell P N) = P)
    (ξ : ℝ) :
    ∑ m ∈ typicalS A (A+Δ) (P :: rest), (g m/(m:ℂ)) * (char m ξ)
      = (∑ v ∈ Finset.Ico v₀ (v₁+1),
          (∑ p ∈ eadicCell P N v, (g p/(p:ℂ)) * (char p ξ))
            * (∑ m' ∈ quotBlock A Δ N v (typicalS A (A+Δ) rest),
                ((g m'/(m':ℂ)) * (char m' ξ))
                  / (((P.filter (· ∣ m')).card : ℂ) + 1)))
        + collarLo g A N ξ + collarHi g A Δ N ξ
        + collisionTerm g A Δ P rest ξ
```
where `quotBlock A Δ N v S := (Finset.Ioc ⌈A·e^{-(v+1)/N}⌉ ⌊(A+Δ)·e^{-v/N}⌋).filter (· ∈ S)`
and `collarLo/collarHi` are `Finset.Ioc`-supported polynomials with explicitly bounded
coefficients over `(⌊A·e^{−1/N}⌋, A]` resp. `(A+Δ, ⌈(A+Δ)e^{1/N}⌉]`.
*Sketch.* Start from the **already-merged** `typicalS_phase_main_add_coll`
(`TypicalFactorization.lean:267`), which supplies the corrected Ramaré identity with
the `1/(ω+1)` weight and the `char_mul` fibre factorisation. Then (a) split the `p`-sum
by II-1; (b) for each `v` replace the `p`-dependent fibre range `(A/p,(A+Δ)/p]` by the
`p`-independent `quotBlock`; the symmetric difference telescopes over `v` (each interior
`n = pm` is counted once), leaving `collarLo/collarHi`. This telescoping is the one
genuinely fiddly step. *Risks:* **the `Nat` floor/ceil bookkeeping of the quotient
block is the main formalisation cost of this whole ladder.** Recommendation: prove the
telescoping as a separate `Finset` identity over `ℕ` (`II-2a`) with no analysis in it,
then glue. The `sifted` term of MR's `lem:decomp` is **absent** — discharge it by
`mem_typicalS`+`hasFactorInAll_cons` (unit II-0, 5 lines).

**II-3 (G) — collar cost.**
```lean
theorem band_energy_collar_le (A Δ N : ℕ) (hA : 1 ≤ A) (hN : 0 < N) (hΔA : Δ ≤ A)
    (d : ℕ → ℂ) (hd : ∀ n, ‖d n‖ ≤ 1) (T : ℝ) (hT : 0 < T)
    (C : Finset ℕ) (hC : C ⊆ Finset.Ioc (A - A/N) (A + Δ + (A+Δ)/N)) :
    ∫ ξ in (-T)..T, ‖∑ n ∈ C, (d n/(n:ℂ)) * (char n ξ)‖^2
      ≤ Real.exp π * (T/(A:ℝ) + 2) * (3*(Δ:ℝ)/(A:ℝ) + 6/(N:ℝ))
```
*Sketch.* I-3 with `B = 1`, then `Σ_{n∈C}1/n ≤ log(1 + …) ≤ 3Δ/A + 6/N` via
`log_sub_log_le_sum_one_div_Ico` (`WindowTK.lean:66`) /
`sum_one_div_Ioc_div_sub_le` (`:116`). *Risks:* the `A/N` `Nat`-division edge cases.

**II-4 (G) — ★ the corrected collision unit** (replaces the FALSE N3-g).
```lean
theorem band_energy_collision_le (g : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC g) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Δ : ℕ) (hA : 1 ≤ A) (hΔ : 1 ≤ Δ) (hΔA : Δ ≤ A)
    (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (hPA : ∀ p ∈ P, p*p ≤ A)
    (rest : List (Finset ℕ)) (T : ℝ) (hT : 0 < T) :
    ∫ ξ in (-T)..T,
        ‖∑ p ∈ P, ∑ m' ∈ (((typicalS A (A+Δ) rest).filter (fun n => p ∣ n)).image (· / p)).filter
              (fun m' => p ∣ m'),
            ((g (p*m')/((p*m' : ℕ):ℂ)) * (char (p*m') ξ))
              / (((P.filter (· ∣ (p*m'))).card : ℂ))‖^2
      ≤ (∑ p ∈ P, (1:ℝ)/p) * Real.exp π
          * ((T/(A:ℝ)) * (∑ p ∈ P, (1:ℝ)/p) + 2*(∑ p ∈ P, (1:ℝ)/(p:ℝ)^3))
          * (3*(Δ:ℝ)/(A:ℝ))
```
*Sketch.* (1) Reindex the inner sum by `n = p²k`, `k ∈ (A/p², (A+Δ)/p²]` — use
`sum_filter_dvd_eq_sum_image` (`RamareIdentity.lean:808`) twice and
`image_div_fibre_subset` (`:827`) for the range. (2) `char_mul` + `hcm` pull out
`(g p²/p²)·char (p*p) ξ`, leaving `(1/p²)·Σ_k (b_k/k)char k ξ` with `‖b_k‖ ≤ 1`
(the `ω_P ≥ 1` denominator). (3) Cauchy–Schwarz over `p` with weights `1/p`:
`‖Σ_p x_p‖² ≤ (Σ_p 1/p)(Σ_p p‖x_p‖²)` — `inner_mul_le_norm_mul_norm` or the elementary
`Finset.inner_mul_le_norm_mul_norm` / `Finset.sum_div_pow_mul_fract`… simplest is
`Finset.sum_sq_le_sq_mul_sq`-style with explicit weights; the repo pattern is
`sq_mul_split`. (4) **I-3 at the quotient scale `A/p²`**, giving
`p^{-4}·e^π(T p²/A + 2)·(3Δ/A)`. (5) Sum.
*Risks:* `hPA : p*p ≤ A` is needed so the quotient block is non-degenerate; the
double-reindexing bookkeeping. **Sanity check (must be in the docstring):** with
`P = {p}`, `S = {n₀}`, `p²∣n₀`, `p² ≈ A`, RHS `≥ e^π·2T/(p²Ak₀) ≥ LHS = 2T/(p⁴k₀²)`. ✔

**II-5 (A) — `E₁`: the level-1 band energy from pointwise prime smallness.**
```lean
theorem band_energy_main_le_of_cells_small (g : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC g) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Δ N : ℕ) (hA : 1 ≤ A) (hΔA : Δ ≤ A) (hN : 0 < N)
    (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (rest : List (Finset ℕ))
    (v₀ v₁ : ℕ) (hcov : …) (α : ℝ) (hα : 0 < α) (hα2 : 2*α < 1)
    (G : Set ℝ) (hG : MeasurableSet G)
    (hsmall : ∀ ξ ∈ G, ∀ v ∈ Finset.Ico v₀ (v₁+1),
      ‖∑ p ∈ eadicCell P N v, (g p/(p:ℂ)) * (char p ξ)‖
        ≤ Real.exp (-(α*(v:ℝ)/N)))
    (T : ℝ) (hT : 0 < T) (hGT : G ⊆ {ξ : ℝ | |ξ| ≤ T}) :
    ∫ ξ in G, ‖∑ v ∈ Finset.Ico v₀ (v₁+1),
        (∑ p ∈ eadicCell P N v, (g p/(p:ℂ)) * (char p ξ))
          * (∑ m' ∈ quotBlock A Δ N v (typicalS A (A+Δ) rest), …)‖^2
      ≤ ((v₁ - v₀ : ℕ) + 1) * Real.exp π * (3*(Δ:ℝ)/A)
          * ( (T/(A:ℝ)) * Real.exp ((1-2*α)*((v₁:ℝ)+1)/N) * ((N:ℝ)/(1-2*α) + 1)
            + 2 * Real.exp (-(2*α*(v₀:ℝ)/N)) * ((N:ℝ)/(2*α) + 1) )
```
*Sketch.* Cauchy–Schwarz over `v` (factor `#v`), then per `v`:
`∫_G ≤ e^{−2αv/N}∫_{−T}^{T}|R_v|²`, and I-3 at scale `A e^{−v/N}` gives
`e^π(T e^{v/N}/A + 2)(3Δ/A)`; sum the two geometric series
(`Finset.geom_sum_le`, or the in-tree `geom_sum_le` helper at `WindowAssembly.lean:1890`).
*Risks:* the two geometric sums over a `Finset.Ico` of naturals with real exponents —
factor out as micro-units `sum_exp_neg_mul_le` / `sum_exp_mul_le`.

### Phase III — moments, for levels `2 ≤ j ≤ J`

**III-1 (A) — multinomial collapse.** `DyadicMVT.lean`.
```lean
theorem card_prime_tuple_le_factorial (Y : Finset ℕ) (hY : ∀ p ∈ Y, p.Prime)
    (k n : ℕ) :
    ((Finset.piFinset (fun _ : Fin k => Y)).filter
        (fun t => ∏ i, t i = n)).card
      ≤ k.factorial * (n.divisors.filter (fun r => ∀ p ∈ r.primeFactors, p ∈ Y)).card
```
*Sketch.* Map a tuple to the multiset of its entries; fibres of that map have size
`≤ k!`; the multiset determines `r = ∏ t i`. *Risks:* real combinatorial work; the
`Finset.piFinset` fibre-counting is the fiddly part. Consider stating it as
`≤ k! · g n` with `g` defined directly as the smooth-divisor count, avoiding `divisors`.

**III-2 (A) — the elementary substitute for Shiu.**
```lean
theorem sum_smooth_divisor_count_sq_div_sq_le (Y : Finset ℕ)
    (hY : ∀ p ∈ Y, p.Prime) (Y₁ : ℕ) (hY₁ : ∀ p ∈ Y, Y₁ ≤ p) (hY₁2 : 2 ≤ Y₁)
    (M : ℕ) (hM : 1 ≤ M) :
    ∑ n ∈ Finset.Icc M (2*M), ((smoothDivisorCount Y n : ℝ))^2/(n:ℝ)^2
      ≤ (4/(M:ℝ)) * Real.exp (3 * ∑ p ∈ Y, (1:ℝ)/p)
```
*Sketch.* `Σ_{n≤N}g(n)² ≤ Σ_{r,r' Y-smooth}#{n ≤ N : lcm(r,r')∣n} ≤ N Σ_{r,r'}1/[r,r']`
and `Σ_{r,r'}1/[r,r'] = ∏_{p∈Y}(1 + 3/p + 4/p² + …) ≤ exp(3Σ_{p∈Y}1/p)` for `p ≥ 2`.
*Risks:* the Euler-product manipulation over a `Finset` of primes — the repo has
comparable machinery in `HalaszEuler.lean`; reuse. **No Shiu, no Rankin.**

**III-3 (A) — the moment lemma (`le:moment` analogue, short-block).**
```lean
theorem intervalIntegral_norm_sq_pow_mul_le (Y : Finset ℕ) (hY : ∀ p ∈ Y, p.Prime)
    (Y₁ : ℕ) (hlo : ∀ p ∈ Y, Y₁ ≤ p) (hhi : ∀ p ∈ Y, p ≤ 2*Y₁)
    (b : ℕ → ℂ) (hb : ∀ p, ‖b p‖ ≤ 1)
    (A' Δ' : ℕ) (hA' : 1 ≤ A') (hΔ' : Δ' ≤ A') (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioc A' (A'+Δ')) (a : ℕ → ℂ) (ha : ∀ m, ‖a m‖ ≤ 1)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (T : ℝ) (hT : 0 < T) :
    ∫ ξ in (-T)..T,
        ‖(∑ p ∈ Y, (b p/(p:ℂ)) * (char p ξ))^ℓ
          * (∑ m ∈ S, (a m/(m:ℂ)) * (char m ξ))‖^2
      ≤ Real.exp π * (T/(A':ℝ) + 2^(ℓ+1)*(Y₁:ℝ)) * ((ℓ+1).factorial:ℝ)^2
          * (4 * Real.exp 3 / (A':ℝ))
```
*Sketch.* Expand the `ℓ`-th power into a Dirichlet polynomial supported on
`[A'Y₁^ℓ, 2^{ℓ+1}Y₁A']` (`char_mul` `ℓ+1` times), coefficient bound by III-1, mass by
III-2 (using `g_block ≤ g_dyadic` pointwise — this is where the `A'/Δ'` relaxation of
§4.3(e) is taken), then I-2 at the top scale. *Risks:* the `ℓ`-fold reindex has **no**
Mathlib one-liner; do it by induction on `ℓ` with a convolution step
(`Finset.sum_mul_sum` + `char_mul`), as a separate micro-unit III-0.

**III-4 (A) — `E_j`: the "borrow largeness" step.**
```lean
theorem band_energy_level_le_of_prev_large (…)
    (hlarge : ∀ ξ ∈ G, Real.exp (-(β*(r:ℝ)/Nprev))
                ≤ ‖∑ p ∈ eadicCell Pprev Nprev r, (g p/(p:ℂ)) * (char p ξ)‖)
    (hsmall : ∀ ξ ∈ G, ‖∑ p ∈ eadicCell P N v, (g p/(p:ℂ)) * (char p ξ)‖
                ≤ Real.exp (-(α*(v:ℝ)/N)))
    (ℓ : ℕ) (hℓ : (v:ℝ)/N ≤ ℓ*((r:ℝ)/Nprev)) : … ≤ …
```
*Sketch.* Multiply the integrand by `(‖Q_prev‖·e^{βr/Nprev})^{2ℓ} ≥ 1` (`one_le_pow`),
then III-3, then the exponent arithmetic `2v(α_prev − α)/N + 2ℓβr/Nprev` and the two
MR side conditions. *Risks:* purely arithmetic once III-3 exists; keep `α, β, ℓ, N` as
free reals/naturals with the side conditions as hypotheses so no schedule is baked in.

### Phase IV — the exceptional set (assumption interfaces)

**IV-1 (X) — Halász large values for integers.** New `MoltResearch/Discrepancy/LargeValueAssumptions.lean`.
```lean
/-- Iwaniec–Kowalski, *Analytic Number Theory*, Theorem 9.6. -/
class HalaszLargeValuesAssumption : Prop where
  bound : ∀ (N : ℕ) (a : ℕ → ℂ) (T : ℝ) (𝒯 : Finset ℝ),
    0 < T → (∀ t ∈ 𝒯, |t| ≤ T) →
    (∀ t ∈ 𝒯, ∀ u ∈ 𝒯, t ≠ u → 1 ≤ |t - u|) →
    ∑ t ∈ 𝒯, ‖∑ n ∈ Finset.Icc 1 N, (a n/(n:ℂ)) * (char n t)‖^2
      ≤ 64 * ((N:ℝ) + (𝒯.card:ℝ)*Real.sqrt T) * (Real.log (2*T) + 1)
          * ∑ n ∈ Finset.Icc 1 N, ‖a n‖^2/(n:ℝ)^2
```

**IV-2 (X) — ★ Halász large values for primes** (the irreducible input).
```lean
/-- Matomäki–Radziwiłł, Annals 183 (2016), Lemma 8.  Proved by duality plus a
Mellin shift of `ζ'/ζ` into the Vinogradov–Korobov zero-free region; there is no
known elementary proof and no Mathlib substrate at the pinned revision. -/
class PrimeLargeValuesAssumption : Prop where
  bound : ∀ (P : ℕ) (Y : Finset ℕ), (∀ p ∈ Y, p.Prime) →
    (∀ p ∈ Y, P ≤ p ∧ p ≤ 2*P) → ∀ (a : ℕ → ℂ) (T : ℝ) (𝒯 : Finset ℝ),
    2 ≤ P → 0 < T → (∀ t ∈ 𝒯, |t| ≤ T) →
    (∀ t ∈ 𝒯, ∀ u ∈ 𝒯, t ≠ u → 1 ≤ |t - u|) →
    ∑ t ∈ 𝒯, ‖∑ p ∈ Y, (a p/(p:ℂ)) * (char p t)‖^2
      ≤ 64 * (1 + (𝒯.card:ℝ)
              * Real.exp (-(Real.log P / (Real.log (2*T))^(3/4:ℝ)))
              * (Real.log (2*T))^2)
          * (∑ p ∈ Y, ‖a p‖^2/(p:ℝ)^2) * (P:ℝ) / Real.log P
```
(`(3/4 : ℝ)` in place of MR's `2/3+ε` for a clean statement; any exponent `< 1` works.)

**IV-3 (A) — the `𝒰` band energy, conditional.**
```lean
theorem band_energy_exceptional_le [HalaszLargeValuesAssumption]
    [PrimeLargeValuesAssumption] (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g)
    (hg : ∀ m, ‖g m‖ ≤ 1) (A Δ : ℕ) (levels : List (Finset ℕ))
    (𝒰 : Set ℝ) (h𝒰meas : MeasurableSet 𝒰)
    (h𝒰card : ∀ (𝒯 : Finset ℝ), (well-spaced ⊆ 𝒰) → (𝒯.card : ℝ) ≤ Mbad)
    (hHal : ∀ ξ, K ≤ |ξ| → |ξ| ≤ T →
      ‖∑ m ∈ typicalS A (A+Δ) levels, (g m/(m:ℂ)) * (char m ξ)‖ ≤ δH)
    (ε : ℝ) (hsched : …) :
    ∫ ξ in 𝒰, ‖∑ m ∈ typicalS A (A+Δ) levels, (g m/(m:ℂ)) * (char m ξ)‖^2
      ≤ ε^2 * (Δ:ℝ)/A
```
*Sketch.* II-2 with `[P_𝒰,Q_𝒰]`; discretise (`Gallagher`, unit V-0); split on
`|Q_v| ≷ (log A)^{−100}`; small side by IV-1, large side by V-1 (measure) + `hHal` +
IV-2. `hHal` is discharged by the **in-tree** `plain_sum_le_halasz_of_nonPretentious`
via partial summation (unit IV-0 below). *Risks:* this is the largest unit in the
ladder; split it into ≥4 PRs.

**IV-0 (A) — short-sum Halász from the in-tree long-sum Halász.**
```lean
theorem norm_ramare_weighted_short_poly_le_of_nonPretentious (f : ℕ → ℝ) …
    (A' Δ' : ℕ) (hΔ'A' : Δ' ≤ A') (P Q : ℕ) (hPQ : 2 ≤ P) (hQ : P ≤ Q) :
    ‖∑ m ∈ Finset.Ioc A' (A'+Δ'), ((f m : ℂ)/(m:ℂ))
        / (((Finset.Icc P Q).filter (fun p => p.Prime ∧ p ∣ m)).card + 1) * (char m ξ)‖
      ≤ 3 * (Real.log Q / Real.log P) * δ_Halász(A', A)
```
*Sketch.* Abel summation `Σ_{A'<m≤A'+Δ'} b_m/m^{1+it} = [S(u)/u^{1+it}] + (1+it)∫S(u)/u^{2+it}du`
reduces to `sup_{u ≤ A'+Δ'}|S(u)|/A'`; `S(u)` is an **initial-segment** sum, so
`plain_sum_le_halasz_of_nonPretentious` applies. The `1/(ω+1)` weight is removed as in
`le:Halappl` by splitting `n = n₁n₂` and bounding `Σ_{n₁ smooth}1/n₁ ≪ log Q/log P`;
`le:Sinclexcl` handles the `𝒮`-restriction by inclusion–exclusion over `2^J` sets.
*Risks:* **`f : ℕ → ℝ` throughout M0R** — the ℝ→ℂ generalisation flagged in the Track R
handoff must be done first; the smooth-number (Rankin) term needs a small unit of its
own; the `2^J ≪ (log A)^{o(1)}` inclusion–exclusion count.

### Phase V — the exceptional-set measure (elementary, ship it)

**V-0 (A) — Gallagher's Sobolev lemma** (replaces IK Thm 9.4).
```lean
theorem sum_well_spaced_le_intervalIntegral (F : ℝ → ℂ) (hF : ContDiff ℝ 1 F)
    (T : ℝ) (hT : 0 < T) (𝒯 : Finset ℝ) (h𝒯 : ∀ t ∈ 𝒯, |t| ≤ T)
    (hsp : ∀ t ∈ 𝒯, ∀ u ∈ 𝒯, t ≠ u → 1 ≤ |t - u|) :
    ∑ t ∈ 𝒯, ‖F t‖^2
      ≤ ∫ ξ in (-(T+1))..(T+1), (‖F ξ‖^2 + 2*‖F ξ‖*‖deriv F ξ‖)
```
*Sketch.* `‖F t‖² = ∫_{t−1/2}^{t+1/2}(‖F‖² + 2 Re⟨F,F′⟩·χ)` — the fundamental theorem
of calculus on each unit window; the windows are disjoint by `hsp`.
*Risks:* moderate; Mathlib has `intervalIntegral.integral_deriv_eq_sub`.

**V-1 (A) — the calibrated exceptional-measure bound (`le:Rupest`, honest form).**
```lean
theorem measure_prime_poly_large_le (Y : Finset ℕ) (hY : ∀ p ∈ Y, p.Prime)
    (P : ℕ) (hlo : ∀ p ∈ Y, P ≤ p) (hhi : ∀ p ∈ Y, p ≤ 2*P) (hP : 2 ≤ P)
    (b : ℕ → ℂ) (hb : ∀ p, ‖b p‖ ≤ 1) (V T : ℝ) (hV : 0 < V) (hT : 0 < T)
    (k : ℕ) (hk : 1 ≤ k) (hcal : (2*(P:ℝ))^k ≤ T) :
    (volume {ξ : ℝ | |ξ| ≤ T ∧
        1/V ≤ ‖∑ p ∈ Y, (b p/(p:ℂ)) * (char p ξ)‖}).toReal
      ≤ V^(2*k) * Real.exp π * 3 * (k.factorial : ℝ)
          * ((∑ p ∈ Y, (1:ℝ)/p))^k * 2^k
```
*Sketch.* Chebyshev on `|Q|^{2k} = |Q^k|²`; III-1/III-2 for the coefficient mass
`≤ P^{−k}k!(Σ1/p)^k`; **I-2** at the top scale `(2P)^k ≤ T` so `T/(2P)^k ≤ 1`.
*Note:* this is the **measure** version — it is honest, elementary, and NOT
super-polynomially small. Its `Finset`-cardinality sibling (needed by IV-3) follows
from V-0.

### Phase VI — the capstone

**VI-1 (A) — `band_energy_typicalS_le`, conditional.** Same shape as the prior report's
N3-n, with three changes: `[HalaszLargeValuesAssumption] [PrimeLargeValuesAssumption]`
instance arguments; `hsched` replaced by the explicit S1–S7 inequality bundle of §4.4;
and the `hwsup/hwdecay` window abstraction kept verbatim (it is correct and decouples
the bump plumbing).

```lean
theorem band_energy_typicalS_le [HalaszLargeValuesAssumption]
    [PrimeLargeValuesAssumption] (g : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC g) (hg1 : g 1 = 1) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A s H U Δ : ℕ) (hΔ : Δ = s + 2*H + 4*U) (hΔA : Δ ≤ A) (h3H : 3*H ≤ A)
    (levels : List (Finset ℕ)) (hlv : ∀ P ∈ levels, ∀ q ∈ P, q.Prime)
    (ε B' K K₂ : ℝ) (hε : 0 < ε) (hB' : 0 ≤ B') (hK : 0 < K) (hKK₂ : K ≤ K₂)
    (hsched : …S1–S7…)
    (w : ℝ → ℝ) (hw0 : ∀ ξ, 0 ≤ w ξ)
    (hwsup : ∀ ξ, w ξ ≤ (4*(H:ℝ)/A)^2)
    (hwdecay : ∀ ξ, ξ ≠ 0 → w ξ ≤ (2*B'/(π*|ξ|))^2) :
    ∫ ξ in {ξ : ℝ | K ≤ |ξ| ∧ |ξ| ≤ K₂},
        ‖∑ m ∈ typicalS A (A+Δ) levels, g m * (char m ξ)‖^2 * w ξ
      ≤ ε^2 * (H:ℝ)^2 * (Δ:ℝ)/(A:ℝ)
```

### Dependency order / shipping order

```
I-1 → I-2 → {I-3 → I-4, II-3, II-4, II-5, III-3, V-1}
II-0, II-1 → II-2 → {II-3, II-4, II-5}
III-0 → III-1, III-2 → III-3 → III-4
V-0 → (𝒯-card sibling of V-1)
IV-0 (needs the M0R ℝ→ℂ generalisation first)
IV-1, IV-2 (assumption files, no dependencies)
IV-3 ← {II-2, IV-0, IV-1, IV-2, V-0, V-1}
VI-1 ← everything
```

**Recommended cut order (each one PR):**
`I-1, I-2, I-3, I-4, II-0, II-1, III-0, III-1, III-2, V-0, V-1, II-3, II-4, II-5,
III-3, III-4` — sixteen PRs, all elementary, all correct independently of how the `𝒰`
question resolves. Then `IV-1, IV-2` (assumption files), then the M0R ℝ→ℂ
generalisation, then `IV-0`, then `IV-3` (split into ≥4), then `VI-1`.

---

## 7. Bottom line

* MR's `𝒰`-machinery is now on the table and it is **not** what the prior report
  guessed. Units N3-k and N3-l should be deleted; N3-m survives only as V-1 with a
  *large* (not small) bound; N3-g was false and is corrected as II-4.
* The prior report's headline gap (`ε²/logΔ`) was **half a formalisation artefact**.
  Unit **I-2** — the sharp, log-free short-block mean value theorem, obtainable today
  from the in-tree Gaussian kit — removes the `logΔ` from *every* estimate in this
  track, including the outer band's `γ`. **This is the single highest-value PR
  available and it is blocked on nothing.**
* With I-2, the entire `𝒯₁…𝒯_J` structure, the collars, the (corrected) collision
  term, the vanishing sifted term, and the exceptional-set measure all close at EDP
  scales with margins `W^{60}`–`W^{397}` (§4.3). Sixteen genuine, elementary units.
* The `𝒰` leg does **not** close, and §5 shows the failure is by a positive power of
  `A`, not by constants: sup×measure fails, continuous integration fails, and even
  full discretisation with the *integer* Halász large-values theorem fails by
  `(log A)^{≈2}`. The irreducible input is **Halász's large-value inequality for
  prime-supported Dirichlet polynomials**, i.e. in the end a **quantitative zero-free
  region for `ζ`** — absent from Mathlib and out of reach of this campaign.
* The right move is therefore to **replace one opaque assumption
  (`MatomakiRadziwillMajorArcAssumption`) by two standard, quotable ones**
  (IK Thm 9.6 and [MR] Lemma 8) plus a fully machine-checked reduction. That is a real
  improvement in assumption quality and it is achievable with the ladder above.
* Two numerology consequences to record now: (i) `slice_energy_le` forces `s ≤ εA/2`,
  hence `Δ/A ≍ ε`; (ii) that costs `(A/Δ)² = 4/ε²` in the `𝒰` leg's Halász step, which
  re-tunes [mrt] Theorem `second` from `W ≤ (log X)^{1/125}` to `W ≤ (log X)^{1/320}`.
  Harmless for EDP (`H → ∞` still admissible up to `exp((log X)^{1/1600})`) but it must
  be propagated when R6/R7 are wired.
