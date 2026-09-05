# Track R — VI-9g phase 1: Codex run 6 final report (2026-09-05)

Verbatim final report of Codex run 6 (gpt-5.6-sol, brief `Problems/tao2015_vi9g_brief.md`),
whose two commits shipped as PR #3686 (VI-9g-1, A2-IV-1′). Kept in the tree because its
§"Accounting discrepancies found" and §"Work left undone and exact blocker" correct the brief:
the recut exceptional fit is the **fixed-threshold** one, `2(V₀²·Aint + δ²·Bpri(1+Γ))` with
`Γ ∝ V₀^{−2ℓ}` (the high-moment count), and the `√`-optimised shape
`exceptionalCell_fit_of_schedule` the brief presupposed for VI-9g-2 is **not** an upper bound
(counterexample recorded). The repair chosen (design report, "Phase VI-9g as run") is to retain
`exceptionalSplitThreshold A = (log A)^{−100}` and fit the two direct terms separately.
Paths below are relative to the run's worktree `moltresearch-wt-codex6`; commit hashes are the
run's, before cherry-pick (`7399dd46 → 56fb6a74`, `230a5e8a → c7cbe20b`).

---

# FINAL REPORT — Track R VI-9g / A.2 discharge

Date: 2026-09-05  
Branch: `vex/track-r-vi9g`  
Base: `origin/main` at `574dbe2f`  
Run: <https://chatgpt.com/codex/tasks/01a07239-9d0a-7312-9878-ccbd7a09dc71>

## Commit 1 — VI-9g-1

Commit: `7399dd46b43e1672a004289eae670cc1c6027273`  
File: `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5BandEnergyExceptionalReCut.lean`

### Statements

The complete Lean declarations, including every structural hypothesis, are
verbatim in the cited source. Their mathematical statements are:

1. `setIntegral_band_energy_exceptional_max_le_recut` (source line 29).

   For prime-supported `Y ⊆ (P,2P]`, a `1`-bounded prime coefficient `b`,
   moment `ell ≥ 1`, integer coefficient `a` on `[1,N]`, and a unit-cell cover
   `K` of `G ⊆ [-T,T]`, if the integer polynomial is at most `delta` on the
   large-prime-polynomial part, then

   ```text
   ∫_G |Q(xi)|² |R(xi)|²
     ≤ 2 * (
         V₀² * 64*(N + #K*sqrt(T))*(log(2T)+1)*Σ[n≤N] |a(n)|²/n²
       + delta² * 64*(1
           + primeHighMomentCountCost(P,ell,Y,T,V₀,lam)
               * exp(-log(P)/log(2T)^(3/4))*log(2T)²)
           * Σ[p∈Y] |b(p)|²/p² * P/log(P)).
   ```

2. `setIntegral_band_energy_exceptional_le_budget_recut` (source line 143).

   Under the same support, cover, positivity, and ungated pointwise hypotheses,
   with

   ```text
   Aint = 64*(N + #K*sqrt(T))*(log(2T)+1)*Σ[n≤N] |a(n)|²/n²,
   Bpri = 64*Σ[p∈Y] |b(p)|²/p² * P/log(P),
   Gamma = primeHighMomentCountCost(P,ell,Y,T,Vsplit,lam)
             * exp(-log(P)/log(2T)^(3/4))*log(2T)²,
   ```

   the exact fixed-threshold fit

   ```text
   2*(Vsplit²*Aint + delta²*(Bpri*(1+Gamma)))
     ≤ kappa*bandBudget(c3,eps,rho)
   ```

   implies

   ```text
   ∫_G |Q(xi)|² |R(xi)|² ≤ kappa*bandBudget(c3,eps,rho).
   ```

3. `band_energy_le_budget_of_exceptional_family_recut` (source line 190).

   For a measurable disjoint partition of `G`, ordinary-leg bounds summing to
   at most one, and an exceptional factorisation

   ```text
   ∫_(part u) |F|² ≤ C*Σ[v∈I] ∫_(part u) |Q_v|²|R_v|² + E,
   ```

   the per-cell exact fits from item 2 and

   ```text
   C*Σ[v∈I] kappa'(v)*budget + E ≤ kappa(u)*budget/Cw
   ```

   imply `∫_G |F|²*w ≤ bandBudget(c3,eps,rho)`.

4. `card_cellsMeeting_exceptional_le_highMomentCost` (source line 296).

   For `J>0`, anchors and moments on every e-adic cell of ordinary level
   `J-1`, and cells `K ⊆ [-T,T]`,

   ```text
   #(cellsMeetingSet K
       (bandPartOn (levelSmallSet P N v0 v1 g alpha) J G J))
     ≤ Σ[r∈I_(J-1)] 2*primeHighMomentCountCost(
         Panchor(r), ell(r), eadicCell(P_(J-1),2N_(J-1),r),
         T, exp(-alpha_(J-1)*r/(2N_(J-1))), lam(r)).
   ```

5. `band_energy_typicalS_le_of_cellUniform_fit_recut` (source line 379).

   This is the full cell-uniform capstone. It takes the same factorisation,
   representative, replacement, collision, band-partition, and Fourier-weight
   hypotheses as the old capstone, but uses

   ```text
   Kcov = cellsMeetingSet (bandCells K2)
     (bandPartOn Pset J {xi | K1 ≤ |xi| ∧ |xi| ≤ K2} J),

   Aint_v = 64*(((A+Delta)/q_v) + #Kcov*sqrt(T))*(log(2T)+1)
     * Σ[n≤(A+Delta)/q_v] |cellBlockCoeff_v(n)|²/n²,

   Bpri_v = 64*Σ[p∈cell_v] |g(p)|²/p² * Pc_v/log(Pc_v),

   Gamma_v = primeHighMomentCountCost(Pc_v,ell_v,cell_v,T,Vsplit_v,lam_v)
     * exp(-log(Pc_v)/log(2T)^(3/4))*log(2T)²,
   ```

   and the exact per-cell fit

   ```text
   2*(Vsplit_v²*Aint_v + delta_v²*Bpri_v*(1+Gamma_v))
     ≤ kappa'_v*bandBudget(c3,eps,Delta/A).
   ```

   With the existing replacement/collision total fit, it concludes the same
   full weighted inner-band bound as the pre-recut capstone.

### Finding

The high-moment and covered-cell recut compiles and removes both old structural
costs: there is no separate `T/P` term, and `Aint` contains exactly `#Kcov`
rather than the full `#bandCells`. The true fixed-threshold fit is the direct
one displayed above.

The advertised square-root fit does not follow. The definition on main is

```text
primeHighMomentCountCost(...,V,...) = C / V^(2*ell),
```

whereas `exceptional_threshold_le_budget` applies only to an expression of the
form

```text
V²*Aint + delta²*Bpri*(1 + Gamma/V²)
```

with `Gamma` independent of the optimized `V`. Substitution of the high-moment
count instead gives

```text
V²*Aint + delta²*Bpri*(1 + C/V^(2*ell)*saving).
```

For a concrete counterexample to the requested algebra, take
`ell=2`, `V=1/2`, `Aint=Bpri=delta=1`, and `C*saving=1`. Then
`Gamma(V)=16`. The exact doubled cost is

```text
2*(1/4 + 1*(1+16)) = 34.5,
```

while the advertised doubled square-root expression is

```text
2*(1 + 2*sqrt(1*1*16)) = 18.
```

Thus the advertised expression is not an upper bound.

### Verification

- `lake env lean .../TrackCStage5BandEnergyExceptionalReCut.lean`: exit `0`.
- `lake build Conjectures.C0002_erdos_discrepancy.src.TrackCStage5BandEnergyExceptionalReCut`:
  exit `0` (`8112/8112`, built in 19 seconds after dependencies).

## Commit 2 — A2-IV-1'

Commit: `230a5e8aaf3b7551fcd8a7ec35749d9a13d927d2`  
Files: `MoltResearch/Discrepancy/LowBandTypicalSSharp.lean`,
`MoltResearch/DiscrepancyAnalytic.lean`

### Statements

1. `norm_typicalS_dirichlet_poly_le_low_band_sharp` (source line 20).

   If `g` is completely multiplicative and `1`-bounded with `g(1)=1`, every
   level consists of primes, `10^16 ≤ a < b`, `D≥2`,
   `NonPretentiousAt g (2D) u` for every `a≤u≤3b`, `0<delta0≤1`, and
   `|2*pi*t|≤(D/2)*a`, then

   ```text
   |Σ[m∈typicalS(a,b,levels)] g(m)/m * e(-t log m)|
     ≤ 2^(#levels) * sharpTwistedDirichletCost(D/2,delta0,a,b).
   ```

2. `integral_norm_typicalS_dirichlet_poly_sq_le_low_band_sharp`
   (source line 80).

   Under the preceding hypotheses and `0≤K`,
   `2*pi*K≤(D/2)*a`,

   ```text
   ∫_{|t|<K} |Σ[m∈typicalS(a,b,levels)] g(m)/m * e(-t log m)|²
     ≤ 2K * (2^(#levels)*sharpTwistedDirichletCost(D/2,delta0,a,b))².
   ```

3. `integral_norm_typicalS_dirichlet_poly_sq_le_low_band_eps`
   (source line 132).

   For every `0<eta≤1`, there exist fixed `D0≥2` and `x0≥10^16` such that for
   all data above with `x0≤a<b≤3a`, `D0≤D`, the stated non-pretentiousness on
   `[a,3b]`, and the low-band frequency fit,

   ```text
   ∫_{|t|<K} |Σ[m∈typicalS(a,b,levels)] g(m)/m * e(-t log m)|²
     ≤ 2K * (2^(#levels) * eta*b/(a+1))².
   ```

### Finding

The low-band frequency cap is compatible with the non-windowed sharp block.
Inclusion--exclusion costs exactly `2^(#levels)`, and
`sharpTwistedDirichletCost_le_eps` supplies fixed scale and strength thresholds.
The resulting statement contains neither the old `W` nor a power-of-log loss.

### Verification

- `lake env lean MoltResearch/Discrepancy/LowBandTypicalSSharp.lean`: exit `0`.
- `lake build MoltResearch.Discrepancy.LowBandTypicalSSharp`: exit `0`.
- `lake build MoltResearch.DiscrepancyAnalytic`: exit `0`.

## Accounting discrepancies found

1. The VI-9d high-moment count has threshold exponent `2*ell`, not `2`. The
   VI-9g brief reuses the quadratic threshold optimiser without accounting for
   this change of exponent.
2. Consequently `Gamma_recut := primeHighMomentCountCost(...,V,...) * saving`
   is not independent of the threshold. It cannot occupy the `Gamma` slot of
   `exceptional_threshold_le_budget` while that theorem also chooses `V`.
3. The exact fixed-threshold fit has a `V²*Aint` small-prime-polynomial term and
   a `delta²*Bpri*(1+Gamma(V))` large term. The brief's square-root expression
   omits the fixed-threshold `V²*Aint` cost.
4. The two valid repairs have different numerology: either retain
   `exceptionalSplitThreshold A` and prove both direct terms fit separately, or
   prove a new `2*ell`-power optimizer. The latter produces an
   `(ell+1)`-root cost rather than the advertised square root.

The six discrepancies in `Problems/tao2015_phase0_vi9_report.md` remain
correctly addressed by the mainline T0 work and by the two completed units here:
covered-cell counting, no first-moment `T/P`, no Abel frequency loss, nonuniform
quotient costs, sharp smooth mass, and the loglog-free sharp Halász budget.

## Work left undone and exact blocker

Per the brief's stop rule, VI-9g-2 and VI-9g-3 were not entered after the
VI-9g-1 fit failed as stated. A2-IV-3 and A2-V were therefore also not entered.

The exact blocker is the invalid implication

```text
2*(V²*Aint + delta²*Bpri*(1 + C/V^(2*ell)*saving))
  ≤ 2*(delta²*Bpri
       + 2*delta*sqrt(Aint*Bpri*(C/V^(2*ell)*saving))),
```

which already fails at the numerical values recorded above (`34.5 ≤ 18`).
Proceeding requires a design decision between the two valid repairs in
Accounting discrepancy 4 and a replacement for the VI-9g-2/3 schedule fit.

`theorem sliceMeanSquareA2 : SliceMeanSquareA2` was **not proved** and no new
audit pin was added.

## Final verification

- `./scripts/forbid_sorry.sh`: exit `0`.
- `./scripts/forbid_axiom_unsafe.sh`: exit `0`.
- `./scripts/check_layering.sh`: exit `0`.
- `python3 scripts/check_aggregator_coverage.py`: exit `0`; 178 reachable
  modules and the two known allowlisted modules.
- `python3 scripts/check_interfaces.py`: exit `0`; seven pre-existing
  warning-mode findings.
- `lake build MoltResearch.DiscrepancyAnalytic Conjectures`: exit `0`;
  `8181/8181` jobs, including the new recut capstone, the new sharp low-band
  leaf, `TrackCAxiomAudit`, and `TrackCStage5InnerBandSchedule`.

Final branch state: two commits ahead of `origin/main`; no push, merge, rebase,
or PR action performed. `CODEX_REPORT.md` is intentionally uncommitted.
