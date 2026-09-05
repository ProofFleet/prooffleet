# Track R — VI-9g phase 3a: Codex run 9b final report (2026-09-05)

Verbatim final report of Codex run 9b (gpt-5.6-sol, brief `Problems/tao2015_vi9g_phase3_brief.md` with the
run-9a resume note), whose two commits shipped as the phase-3a PR. Run 9a stopped on the `/16 → /24` constant
(the ℕ-floor `A / 2 ≤ Δ` gives `Δ/A ≥ 1/3`, not `1/2`); run 9b resumed under the clarified stop rule
("unbounded factor only"), carried the `/24` floor into the generic half-budget fit at `/48`, and then stopped
correctly on a genuine unbounded obstruction: with the brief's moment order `ℓ = 1`, the high-moment count
`primeHighMomentCountCost` still contains `(T+1)/P`, so `Γ ≤ 1` on a nonempty cell forces
`e^π(T+1)e^{−log P/(log 2T)^{3/4}}(log 2T)² ≤ 2P²/(log A)^{200}`, which fails by `≈ A·exp(−2(log A)^{49/50})`
at the A.2 scales. The diagnosis and the two repairs (the `[MR]` moment order `ℓ = ⌈log 2T/log Pc⌉ + 1`, and
the level status of the exceptional block — its item 4 below) are in the design report, section
"Two calibration errors of the phase-3 brief (runs 9a/9b)". Commit hashes are the run's, before cherry-pick.

---

# FINAL REPORT — Track R VI-9g phase 3 (run 9b)

Branch: `vex/track-r-vi9g-3`

Base: `177119f84017afafe8897ef61760f534e72aceb8` (`origin/main`)

Result: the natural-division discrepancy from run 9a was repriced at the valid
fixed floor `c3*eps^2/24`, and the half-budget conversion was proved. The next
prescribed step, `ell = 1` in the high-moment count, fails by an unbounded
factor in the ambient scale. The exact necessary inequality was proved for
every positive smoothing parameter `lambda` and every nonempty prime cell.

Under the A.2 scales `T` comparable to `A`,
`P` comparable to `exp((log A)^(49/50))`, and
`V = exceptionalSplitThreshold A = (log A)^(-100)`, `Gamma <= 1` would force

```text
exp(pi) * (T+1) * exp(-log P / log(2T)^(3/4)) * log(2T)^2
  <= 2 * P^2 / (log A)^200.
```

The logarithm of the left/right ratio is

```text
log A - 2*(log A)^(49/50) - (log A)^(23/100)
  + 202*loglog A + O(1),
```

up to the fixed `C/eps^3` coefficient in `log P`; it tends to infinity. This
is not a constant-factor discrepancy. Per the required dependency order,
A2-IV-3 and all later units were not entered.

## Commit `913965dd27115549b87f28175ecfbe65fb36a90a`

Subject: `Track R: expose the floored half-dyadic margin (#3044, VI-9g-3′)`

File:
`Conjectures/C0002_erdos_discrepancy/src/TrackCStage5InnerBandScheduleSharpFit.lean`

### Statements

```lean
theorem half_dyadic_bandBudget_margin_counterexample :
    (3 : ℕ) / 2 ≤ 1 ∧
      ¬ ((1 : ℝ) / 2 ≤ ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) ∧
      ¬ ((1 : ℝ) / 16 ≤
        bandBudget 1 1 (((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)))
```

```lean
theorem exists_half_dyadic_ratio_counterexample_above (A0 : ℕ) :
    ∃ A Delta : ℕ, A0 ≤ A ∧ A / 2 ≤ Delta ∧
      (Delta : ℝ) / (A : ℝ) < (1 : ℝ) / 2
```

```lean
theorem one_third_le_ratio_of_nat_half_le (A Delta : ℕ)
    (hA : 2 ≤ A) (hhalf : A / 2 ≤ Delta) :
    (1 : ℝ) / 3 ≤ (Delta : ℝ) / (A : ℝ)
```

```lean
theorem bandBudget_one_twenty_four_le_of_nat_half_le
    (c3 eps : ℝ) (hc3 : 0 ≤ c3) (A Delta : ℕ)
    (hA : 2 ≤ A) (hhalf : A / 2 ≤ Delta) :
    c3 * eps ^ 2 / 24 ≤ bandBudget c3 eps ((Delta : ℝ) / (A : ℝ))
```

```lean
theorem bandBudget_one_sixteen_le_of_le_two_mul
    (c3 eps : ℝ) (hc3 : 0 ≤ c3) (A Delta : ℕ)
    (hA : 0 < A) (hhalf : A ≤ 2 * Delta) :
    c3 * eps ^ 2 / 16 ≤ bandBudget c3 eps ((Delta : ℝ) / (A : ℝ))
```

### Finding

The floor guard `A / 2 <= Delta` yields the sharp uniform real ratio `1/3`,
not `1/2`, and therefore the fixed budget floor is `c3*eps^2/24`. This is a
constant-only correction and was retained as required.

### Verification

- `lake env lean .../TrackCStage5InnerBandScheduleSharpFit.lean`: exit `0`.
- `lake build Conjectures.C0002_erdos_discrepancy.src.TrackCStage5InnerBandScheduleSharpFit`:
  exit `0`; 8,119 jobs.

## Commit `ff038740fbacadd65e20199552c50caacfdd8561`

Subject: `Track R: isolate the moment-one growth obstruction (#3044, VI-9g-3′)`

File:
`Conjectures/C0002_erdos_discrepancy/src/TrackCStage5InnerBandScheduleSharpFit.lean`

### Statements

```lean
theorem half_bandBudget_fit_of_nat_half_le
    (cost c3 eps kappa : ℝ) (hcost : cost ≤ kappa * c3 * eps ^ 2 / 48)
    (hc3 : 0 ≤ c3) (hkappa : 0 ≤ kappa) (A Delta : ℕ)
    (hA : 2 ≤ A) (hhalf : A / 2 ≤ Delta) :
    cost ≤ kappa / 2 * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ))
```

```lean
theorem one_div_two_mul_le_prime_harmonic_mass
    (P : ℕ) (hP : 0 < P) (Y : Finset ℕ) (p : ℕ)
    (hp0 : 0 < p) (hpY : p ∈ Y) (hpHi : p ≤ 2 * P) :
    (1 : ℝ) / (2 * (P : ℝ)) ≤ ∑ q ∈ Y, (1 : ℝ) / q
```

```lean
theorem primeHighMomentCountCost_one_lower
    (P : ℕ) (hP : 0 < P) (Y : Finset ℕ) (p : ℕ)
    (hp0 : 0 < p) (hpY : p ∈ Y) (hpHi : p ≤ 2 * P)
    (T V lam : ℝ) (hT : 0 ≤ T) (hV : 0 < V) (hlam : 0 < lam) :
    Real.exp Real.pi * ((T + 1) / (P : ℝ))
          * ((1 : ℝ) / (2 * (P : ℝ))) / V ^ 2
      ≤ primeHighMomentCountCost P 1 Y T V lam
```

```lean
theorem time_scale_bound_of_moment_one_Gamma_le_one
    (P : ℕ) (hP : 0 < P) (Y : Finset ℕ) (p : ℕ)
    (hp0 : 0 < p) (hpY : p ∈ Y) (hpHi : p ≤ 2 * P)
    (T V lam : ℝ) (hT : 0 ≤ T) (hV : 0 < V) (hlam : 0 < lam)
    (hGamma : primeHighMomentCountCost P 1 Y T V lam
          * Real.exp (-(Real.log (P : ℝ) /
            (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
          * (Real.log (2 * T)) ^ 2 ≤ 1) :
    Real.exp Real.pi * (T + 1)
          * Real.exp (-(Real.log (P : ℝ) /
            (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
          * (Real.log (2 * T)) ^ 2
      ≤ 2 * (P : ℝ) ^ 2 * V ^ 2
```

```lean
theorem time_scale_bound_of_fixed_split_moment_one_Gamma_le_one
    (A P : ℕ) (hA : 1 < A) (hP : 0 < P) (Y : Finset ℕ) (p : ℕ)
    (hp0 : 0 < p) (hpY : p ∈ Y) (hpHi : p ≤ 2 * P)
    (T lam : ℝ) (hT : 0 ≤ T) (hlam : 0 < lam)
    (hGamma : primeHighMomentCountCost P 1 Y T (exceptionalSplitThreshold A) lam
          * Real.exp (-(Real.log (P : ℝ) /
            (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
          * (Real.log (2 * T)) ^ 2 ≤ 1) :
    Real.exp Real.pi * (T + 1)
          * Real.exp (-(Real.log (P : ℝ) /
            (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
          * (Real.log (2 * T)) ^ 2
      ≤ 2 * (P : ℝ) ^ 2 / Real.log (A : ℝ) ^ 200
```

### Finding

The `/24` repair closes any half-budget hypothesis whose raw cost is at most
`kappa*c3*eps^2/48`. It does not make the stated `Gamma <= 1` proof valid.
For `ell = 1`, the definition of `primeHighMomentCountCost` contains
`(T+1)/P`; a nonempty cell contributes at least `1/(2P)` harmonic mass, and
the remaining lambda factor is at least `1` for every `lambda > 0`. The two
last theorems are the exact necessary inequalities.

With `T` proportional to `A` (the A2 outer cutoff has
`K2 = gamma*B'*A/(2*pi*h)` and `K2+2 <= T`) and every allowed
`P <= Q_U = exp((C/eps^3)*(log A)^(49/50))` at fixed `(h,eps,C)`, the
necessary inequality fails by an unbounded factor. Raising `A0` cannot fix
it. An adaptive moment of order comparable to `log T/log P` is a different
parameter design and would have to be proved before this branch can continue.

### Verification

- `~/.elan/bin/lake env lean Conjectures/C0002_erdos_discrepancy/src/TrackCStage5InnerBandScheduleSharpFit.lean > /tmp/codex9b-lean.log 2>&1`:
  exit `0`.
- `~/.elan/bin/lake build Conjectures.C0002_erdos_discrepancy.src.TrackCStage5InnerBandScheduleSharpFit`:
  exit `0`; 8,119 jobs.
- `git diff --check`: exit `0` before commit.

## Accounting discrepancies found

1. The natural half-dyadic guard supplies `/24`, not `/16`; this is the
   constant-only run-9a discrepancy and has now been carried into the generic
   half-budget fit at denominator `/48`.

2. The phase-3 claim that `primeHighMomentCountCost` is polylogarithmic at
   `ell = 1` is false. Its exact `(T+1)/P` summand remains. Even using only
   the weakest nonempty-cell mass `1/(2P)`, `Gamma <= 1` forces the displayed
   time-scale inequality, which fails by an unbounded factor at the stated
   `P_U`, `Q_U`, and A2 frequency scale.

3. The same issue was forecast in the phase-2 report's accounting item 3:
   an adaptive moment near `log T/log P_U` is required. R8 repaired the
   relative slice budget but did not change the moment-one count.

4. A downstream quantifier issue also remains from the phase-2 report: the
   target `SliceMeanSquareA2` chooses one finite `levels` list before
   universally quantifying the ambient `A`, while the proposed exceptional
   interval `P_U(A), Q_U(A)` varies with `A`. This run did not enter A2-V
   because the earlier moment-one fit already triggered the mandated stop.

## Work left undone and exact blocker

VI-9g-3′ is not discharged. On every nonempty cell and for every positive
`lambda`, its prescribed `ell = 1` estimate must satisfy

```text
Gamma <= 1
  ==>
exp(pi) * (T+1) * exp(-log P / log(2T)^(3/4)) * log(2T)^2
  <= 2 * P^2 / (log A)^200.
```

At `T` proportional to `A` and
`P <= exp((C/eps^3)*(log A)^(49/50))`, the logarithm of the failed ratio is

```text
log A
  - 2*(C/eps^3)*(log A)^(49/50)
  - (C/eps^3)*(log A)^(23/100)
  + 202*loglog A + O(1),
```

which tends to positive infinity for fixed `eps` and `C`. Thus no eventual
threshold `A0` can discharge the stated moment-one `Gamma` fit.

Per the required order, the following dependent units were not entered:

- A2-IV-3;
- A2-V-1, A2-V-2, A2-V-3, and A2-V-4;
- `theorem sliceMeanSquareA2 : SliceMeanSquareA2`;
- the audit pin and card checkbox.

`theorem sliceMeanSquareA2 : SliceMeanSquareA2` was **not proved** and was
**not audit-pinned**. There is consequently no new `#print axioms` output for
that declaration.

## Final verification

- `./scripts/forbid_sorry.sh`: exit `0`.
- `./scripts/forbid_axiom_unsafe.sh`: exit `0`.
- `./scripts/check_layering.sh`: exit `0`.
- `python3 scripts/check_aggregator_coverage.py`: exit `0`; 180 modules, 178
  reachable, with the two pre-existing allowlisted compile-only modules.
- `python3 scripts/check_interfaces.py`: exit `0` in warning mode; its seven
  findings are pre-existing.
- `~/.elan/bin/lake build MoltResearch.DiscrepancyAnalytic Conjectures`:
  exit `0`; 8,184 jobs.

Final branch state: two commits ahead of `origin/main`. No push, merge,
rebase, PR action, or edit to the target Prop/R6/R7 chain was performed.
`CODEX_REPORT.md` is intentionally uncommitted.
