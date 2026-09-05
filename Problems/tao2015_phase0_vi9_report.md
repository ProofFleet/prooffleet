# Track R — Phase 0 "VI-9": Codex run 5 final report (2026-09-05)

Verbatim final report of Codex run 5 (gpt-5.6-sol, brief `Problems/tao2015_phase0_vi9_brief.md`),
whose eight commits shipped as #3675 (VI-9a–d) and #3676 (VI-9e, VI-9f, A2-IV-1, A2-IV-2). Kept in
the tree because its §"Accounting discrepancies found" and §"Work left undone and exact blocker"
are the current state of the A.2 campaign: `SliceMeanSquareA2` is **not** discharged; the two
remaining gaps are the far-regime repulsion (now the cited interface `FarRegimeRepulsionAssumption`)
and the central `T₀` GHS window (no in-tree statement; exact wanted shape and exact available
shell recorded below). Both are the Halász-strength problem of
`Problems/tao2015_a1_r6r7_design_report.md` §6 (Finding C). Paths below are relative to the run's
worktree `moltresearch-wt-codex5`; commit hashes are the run's, before cherry-pick.

---

# FINAL REPORT — Track R Phase 0 VI-9

Date: 2026-09-05  
Branch: `vex/track-r-vi9`  
Starting commit: `41db0f51` (the branch was equal to `origin/main` when the run began)  
Final commit: `ac05d3ae68d2187cb2fdb3b9e0c68ffa635879bc`  
Run: https://chatgpt.com/codex/tasks/01a070e6-5d77-7530-932c-1a4277b68cd8

The run produced eight small verified commits. VI-9a through VI-9e are
implemented. VI-9f is implemented through the compact minimizer and complete
mid/far `T1` split, with the one permitted far-regime interface. The central
`T0` leg does not close from the current GHS capstone, so VI-9g was not attempted.
The independent A2-IV-1 and A2-IV-2 units are complete. A2-IV-3 and A2-V were
not attempted, as required by the brief when an earlier unit remains open.

While this run was active, the local `origin/main` ref advanced by three commits.
No merge, rebase, push, or pull was performed.

## Commit 1 — VI-9a

Commit: `906593d307a2f97b5f0e4ccc6f02be66f55cef14`  
Message: `Track R: retain the exceptional weight in the schedule capstone (#3044, VI-9a)`

Files:

- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5InnerBandSchedule.lean`

Theorem statements:

```lean
theorem ordinaryLegShares_fit_honest (j : ℕ) :
    2 * ordinaryLegShare j + 2 * ordinaryLegShare j + 2 * ordinaryLegShare j
      ≤ (1 : ℝ) / 2 ^ (j + 1)
```

```lean
theorem band_energy_typicalS_le_of_schedule' [HalaszLargeValuesAssumption]
    [PrimeLargeValuesAssumption]
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta H : ℕ) (hA : 0 < A) (hH : 0 < H) (hDeltaA : Delta ≤ A)
    (h3HA : 3 * H ≤ A)
    (Pl : ℕ → Finset ℕ) (Pu : Finset ℕ) (J : ℕ)
    (hPl : ∀ i < J, ∀ p ∈ Pl i, p.Prime)
    (hPu : ∀ p ∈ Pu, p.Prime)
    (hPAl : ∀ i < J, ∀ p ∈ Pl i, p * p ≤ A)
    (hPAu : ∀ p ∈ Pu, p * p ≤ A)
    (hdisj : ∀ i < J, ∀ k < J, i ≠ k → Disjoint (Pl i) (Pl k))
    (hdisjU : ∀ i < J, Disjoint (Pl i) Pu)
    (Nl v₀l v₁l : ℕ → ℕ) (ql : ℕ → ℕ → ℕ)
    (hNl : ∀ j < J, 0 < Nl j)
    (hcovl : ∀ j < J, (Finset.Ico (v₀l j) (v₁l j + 1)).biUnion
      (eadicCell (Pl j) (2 * Nl j)) = Pl j)
    (hqcelll : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ql j v ∈ eadicCell (Pl j) (2 * Nl j) v)
    (hq1l : ∀ j < J, ∀ v, 1 ≤ ql j v)
    (hqAl : ∀ j < J, ∀ v, 2 * ql j v ≤ A)
    (hqminl : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v, ql j v ≤ p)
    (hLAl : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
        A / (Nl j * p) + 1 ≤ A / p)
    (hLBl : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j + 1),
      ∀ p ∈ eadicCell (Pl j) (2 * Nl j) v,
        (A + Delta) / (Nl j * p) + 1 ≤ (A + Delta) / p)
    (Plo Qhi : ℕ → ℝ)
    (hPlo0 : ∀ j < J, 0 < Plo j) (hQhi0 : ∀ j < J, 0 < Qhi j)
    (hPloQhi : ∀ j < J, Plo j ≤ Qhi j)
    (htop : ∀ j < J, (v₁l j : ℝ) ≤ 2 * (Nl j : ℝ) * Real.log (Qhi j))
    (hbot : ∀ j < J,
      2 * (Nl j : ℝ) * Real.log (Plo j) - 1 ≤ (v₀l j : ℝ))
    (R : ℕ) (hR : 1 ≤ R) (hB : A + Delta ≤ R * A)
    (K₁ K₂ T : ℝ) (hT1 : 1 ≤ T) (hTK₂ : K₂ + 2 ≤ T)
    (c₃ eps : ℝ) (hc₃ : 0 ≤ c₃)
    (hscheduleT0 : 0 < J →
      (2 * (Nl 0 : ℝ) * (Real.log (Qhi 0) - Real.log (Plo 0)) + 2)
        * (Real.exp Real.pi * Real.log (2 * (R : ℝ))
          * ((2 * T * Real.exp (1 / ((2 * Nl 0 : ℕ) : ℝ)) / (A : ℝ))
            * ((Qhi 0) ^ (1 - 2 * innerBandScheduleAlpha 0)
              * Real.exp ((1 - 2 * innerBandScheduleAlpha 0) /
                ((2 * Nl 0 : ℕ) : ℝ)))
            * (((2 * Nl 0 : ℕ) : ℝ) / (1 - 2 * innerBandScheduleAlpha 0) + 1)))
      ≤ ordinaryLegShare 0 / 2 * bandBudget c₃ eps ((Delta : ℝ) / A))
    (hscheduleP0 : 0 < J →
      (2 * (Nl 0 : ℝ) * (Real.log (Qhi 0) - Real.log (Plo 0)) + 2)
        * (Real.exp Real.pi * Real.log (2 * (R : ℝ))
          * (4 * (R : ℝ) * ((Plo 0) ^ (-(2 * innerBandScheduleAlpha 0))
              * Real.exp (2 * innerBandScheduleAlpha 0 / ((2 * Nl 0 : ℕ) : ℝ)))
            * (((2 * Nl 0 : ℕ) : ℝ) / (2 * innerBandScheduleAlpha 0) + 1)))
      ≤ ordinaryLegShare 0 / 2 * bandBudget c₃ eps ((Delta : ℝ) / A))
    (A' Delta' Pmom ell : ℕ → ℕ → ℕ)
    (hA' : ∀ j, 0 < j → j < J → ∀ r ∈ Finset.Ico (v₀l (j-1)) (v₁l (j-1)+1), 1 ≤ A' j r)
    (hDelta' : ∀ j, 0 < j → j < J → ∀ r ∈ Finset.Ico (v₀l (j-1)) (v₁l (j-1)+1), Delta' j r ≤ A' j r)
    (hSblk : ∀ j, 0 < j → j < J → ∀ r ∈ Finset.Ico (v₀l (j-1)) (v₁l (j-1)+1),
      ∀ v ∈ Finset.Ico (v₀l j) (v₁l j+1),
        Finset.Ioc (A / ql j v) ((A+Delta) / ql j v) ⊆
          Finset.Ioc (A' j r) (A' j r + Delta' j r))
    (hPmom : ∀ j, 0 < j → j < J → ∀ r ∈ Finset.Ico (v₀l (j-1)) (v₁l (j-1)+1), 1 ≤ Pmom j r)
    (hPmom2 : ∀ j, 0 < j → j < J → ∀ r ∈ Finset.Ico (v₀l (j-1)) (v₁l (j-1)+1), 2 ≤ Pmom j r)
    (hlomom : ∀ j, 0 < j → j < J → ∀ r ∈ Finset.Ico (v₀l (j-1)) (v₁l (j-1)+1),
      ∀ p ∈ eadicCell (Pl (j-1)) (2 * Nl (j-1)) r, Pmom j r < p)
    (hhimom : ∀ j, 0 < j → j < J → ∀ r ∈ Finset.Ico (v₀l (j-1)) (v₁l (j-1)+1),
      ∀ p ∈ eadicCell (Pl (j-1)) (2 * Nl (j-1)) r, p ≤ 2 * Pmom j r)
    (hell : ∀ j, 0 < j → j < J → ∀ r ∈ Finset.Ico (v₀l (j-1)) (v₁l (j-1)+1), 1 ≤ ell j r)
    (hscheduleLater : ∀ j, 0 < j → j < J →
      ∀ r ∈ Finset.Ico (v₀l (j-1)) (v₁l (j-1)+1),
      (2 * (Nl j : ℝ) * (Real.log (Qhi j) - Real.log (Plo j)) + 2)
        * (((Plo j) ^ (-(2 * innerBandScheduleAlpha j))
              * Real.exp (2 * innerBandScheduleAlpha j / ((2 * Nl j : ℕ) : ℝ))
              * (((2 * Nl j : ℕ) : ℝ) / (2 * innerBandScheduleAlpha j) + 1))
          * ((Real.exp Real.pi
                * (T / (((Pmom j r) ^ (ell j r) * A' j r : ℕ) : ℝ)
                  + 2 * ((2 ^ (ell j r + 1) : ℕ) : ℝ)))
            * laterMomentScheduleBound (ell j r) (Pmom j r)
                ((Qhi (j-1)) ^ (-(innerBandScheduleAlpha (j-1)))
                  * Real.exp (-(innerBandScheduleAlpha (j-1) /
                    ((2 * Nl (j-1) : ℕ) : ℝ))))))
      ≤ geometricCellShare (ordinaryLegShare j) r
          * bandBudget c₃ eps ((Delta : ℝ) / A))
    (Pb Kc bb : ℕ → ℕ) (aa : ℕ → ℕ → ℕ)
    (hPb : ∀ j < J, 1 ≤ Pb j) (hKc : ∀ j < J, 2 ≤ Kc j)
    (hbb : ∀ j < J, 3 ≤ bb j)
    (haa : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j+1), Pb j ≤ aa j v)
    (hcell : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j+1),
      eadicCell (Pl j) (2*Nl j) v ⊆ (Finset.Ioc (aa j v) (aa j v+Kc j)).filter Nat.Prime)
    (hlevel : ∀ j < J, ∀ v ∈ Finset.Ico (v₀l j) (v₁l j+1),
      eadicCell (Pl j) (2*Nl j) v ⊆ (Finset.Ioc (Pb j) (bb j)).filter Nat.Prime)
    (hNbb : ∀ j < J, Nl j * bb j ≤ A)
    (hrho : eps ≤ (Delta : ℝ) / A)
    (hscheduleReplacement : ∀ j < J,
      64 * (Finset.Ico (v₀l j) (v₁l j+1)).card * replacementCost A (Nl j) (bb j) T
        * ((256 * Kc j / (Pb j * Real.log (Kc j))) * levelPrimeMassBound (bb j))
      ≤ ordinaryLegShare j * c₃ * eps^3)
    (hscheduleCollision : ∀ j < J,
      8 * (levelPrimeMassBound (bb j)
        * ((levelPrimeMassBound (bb j) / (Pb j)^2)
          * (Real.exp Real.pi * (2*T*(bb j)^2/A + 8) * Real.log (2*R))))
      ≤ ordinaryLegShare j * bandBudget c₃ eps ((Delta : ℝ)/A))
    (Nu v₀u v₁u : ℕ) (hNu : 0 < Nu)
    (hcovU : (Finset.Ico v₀u (v₁u+1)).biUnion (eadicCell Pu (2*Nu)) = Pu)
    (qu : ℕ → ℕ)
    (hqcellU : ∀ v ∈ Finset.Ico v₀u (v₁u+1), qu v ∈ eadicCell Pu (2*Nu) v)
    (hq1U : ∀ v, 1 ≤ qu v)
    (hqminU : ∀ v ∈ Finset.Ico v₀u (v₁u+1), ∀ p ∈ eadicCell Pu (2*Nu) v, qu v ≤ p)
    (hLAU : ∀ v ∈ Finset.Ico v₀u (v₁u+1), ∀ p ∈ eadicCell Pu (2*Nu) v,
      A/(Nu*p)+1 ≤ A/p)
    (hLBU : ∀ v ∈ Finset.Ico v₀u (v₁u+1), ∀ p ∈ eadicCell Pu (2*Nu) v,
      (A+Delta)/(Nu*p)+1 ≤ (A+Delta)/p)
    (w : ℝ → ℝ) (hwm : Measurable w) (hw0 : ∀ xi, 0 ≤ w xi)
    (hwsup : ∀ xi, w xi ≤ (4 * (H : ℝ) / A)^2)
    (PcU : ℕ → ℕ) (hPcU : ∀ v ∈ Finset.Ico v₀u (v₁u+1), 2 ≤ PcU v)
    (hloU : ∀ v ∈ Finset.Ico v₀u (v₁u+1), ∀ p ∈ eadicCell Pu (2*Nu) v, PcU v < p)
    (hhiU : ∀ v ∈ Finset.Ico v₀u (v₁u+1), ∀ p ∈ eadicCell Pu (2*Nu) v, p ≤ 2*PcU v)
    (D delta₀ : ℝ) (hD : 1 ≤ D) (hdelta₀ : 0 < delta₀) (hdelta₁ : delta₀ ≤ 1)
    (yU : ℕ) (hyU : 4 ≤ yU) (hPuy : ∀ p ∈ Pu, p < yU)
    (hBqCutoff : ∀ v ∈ Finset.Ico v₀u (v₁u+1), cellHalaszThreshold ≤ (A+Delta)/qu v)
    (hNP : ∀ u, cellHalaszThreshold ≤ u → u ≤ 3*(A+Delta) → NonPretentiousAt g (2*D) u)
    (hA0 : ∀ v ∈ Finset.Ico v₀u (v₁u+1),
      0 < 64 * (((A+Delta)/qu v : ℕ) + (bandCells K₂).card * Real.sqrt T)
        * (Real.log (2*T)+1)
        * ∑ n ∈ Finset.Icc 1 ((A+Delta)/qu v),
          ‖cellBlockCoeff g A (A+Delta) Pu ((List.range J).map Pl) (qu v) n‖^2 / n^2)
    (hB0 : ∀ v ∈ Finset.Ico v₀u (v₁u+1),
      0 < 64 * (∑ p ∈ eadicCell Pu (2*Nu) v, ‖g p‖^2/p^2) * PcU v / Real.log (PcU v))
    (kappaU : ℕ → ℝ)
    (hscheduleUCell : ∀ v ∈ Finset.Ico v₀u (v₁u+1),
      exceptionalCellScheduleCost
        (exceptionalIntegerSchedule A Delta qu T v)
        (exceptionalPrimeSchedule PcU v)
        (exceptionalRatioSchedule PcU T v)
        (exceptionalDeltaSchedule D delta₀ T A Delta ((List.range J).map Pl) qu yU v)
      ≤ kappaU v * bandBudget c₃ eps ((Delta : ℝ)/A))
    (PminU QmaxU : ℕ) (hPminU : 1 ≤ PminU) (hQmaxU : 3 ≤ QmaxU)
    (hPulo : ∀ p ∈ Pu, PminU < p) (hPuhi : ∀ p ∈ Pu, p ≤ QmaxU)
    (hNuQ : Nu * QmaxU ≤ A)
    (kappaReplacementU kappaCollisionU : ℝ)
    (hkappaReplacementU : 0 ≤ kappaReplacementU * c₃)
    (hscheduleReplacementU :
      64 * (Finset.Ico v₀u (v₁u+1)).card * replacementCost A Nu QmaxU T
        * ((256*QmaxU/(PminU*Real.log QmaxU))*levelPrimeMassBound QmaxU)
      ≤ kappaReplacementU*c₃*eps^3)
    (hscheduleCollisionU :
      8 * (levelPrimeMassBound QmaxU
        * ((levelPrimeMassBound QmaxU/PminU^2)
          * (Real.exp Real.pi*(2*T*QmaxU^2/A+8)*Real.log (2*R))))
      ≤ kappaCollisionU * bandBudget c₃ eps ((Delta : ℝ)/A))
    (hscheduleUShare :
      2 * (Finset.Ico v₀u (v₁u+1)).card
          * (∑ v ∈ Finset.Ico v₀u (v₁u+1), kappaU v)
        + 2*kappaReplacementU + 2*kappaCollisionU ≤ 1 / 2^(J+1)) :
    (∫ xi in {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂},
      ‖∑ m ∈ typicalS A (A+Delta) (innerBandLevels Pl Pu J),
        (g m / (m : ℂ)) *
          ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖^2 * w xi)
      ≤ (4 * (H : ℝ) / A)^2 * bandBudget c₃ eps ((Delta : ℝ)/A)
```

The displayed declaration preserves the full capstone interface. Some numeric
casts above are rendered compactly (`Nat` values in real expressions); the
checked source declaration at lines 612ff is authoritative.

Finding: the exceptional share can honestly be bounded by `1/2^(J+1)`, not by
`(1/2^(J+1))/(4H/A)^2`. Therefore the Fourier-weight factor cannot disappear:
the true result is `(4H/A)^2 * bandBudget`. The old schedule could over-allocate
the exceptional leg by the factor `(A/(4H))^2`, which is unbounded when `H/A`
is small.

Verification:

```text
lake env lean Conjectures/C0002_erdos_discrepancy/src/TrackCStage5InnerBandSchedule.lean  EXIT 0
final lake build MoltResearch.DiscrepancyAnalytic Conjectures                         EXIT 0
```

## Commit 2 — VI-9b

Commit: `0f60acb7126479c5e9fb04ef0591b12e0dae3214`  
Message: `Track R: count separated large prime-polynomial values (#3044, VI-9b)`

Files:

- `MoltResearch/Discrepancy/LargePrimePolynomialCount.lean`
- one registration import in `MoltResearch/DiscrepancyAnalytic.lean`

Full theorem statement:

```lean
theorem card_large_prime_poly_pow_le (Y : Finset ℕ)
    (hY : ∀ p ∈ Y, p.Prime) (P : ℕ) (hP : 1 ≤ P)
    (hlo : ∀ p ∈ Y, P < p) (hhi : ∀ p ∈ Y, p ≤ 2 * P)
    (b : ℕ → ℂ) (hb : ∀ p, ‖b p‖ ≤ 1) (ell : ℕ) (hell : 1 ≤ ell)
    (points : Finset ℝ) (T V lam : ℝ) (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hlam : 0 < lam)
    (hmem : ∀ t ∈ points, t ∈ Set.Icc (-T) T)
    (hsep : ∀ t ∈ points, ∀ u ∈ points, t ≠ u → 1 ≤ |t - u|)
    (hlarge : ∀ t ∈ points,
      V ≤ ‖∑ p ∈ Y, (b p / (p : ℂ))
        * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖) :
    (points.card : ℝ) * V ^ (2 * ell)
      ≤ Real.exp Real.pi
          * ((T + 1) / ((P ^ ell : ℕ) : ℝ) + 2 * ((2 ^ ell : ℕ) : ℝ))
        * ((Nat.factorial ell : ℝ) ^ 2
            * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ)) ^ ell)
        * ((1 + lam) + (1 / lam)
            * (2 * Real.pi * Real.log ((2 * P) ^ ell)) ^ 2)
```

Finding: collapsing `Q^ell` into its product fibers gives support in
`(P^ell,(2P)^ell]`. Unit-cell sampling plus the derivative bound converts the
measure moment into cardinality without losing an uncontrolled cell factor.

Verification:

```text
lake env lean MoltResearch/Discrepancy/LargePrimePolynomialCount.lean  EXIT 0
lake build MoltResearch.Discrepancy.LargePrimePolynomialCount         EXIT 0
final lake build MoltResearch.DiscrepancyAnalytic Conjectures         EXIT 0
```

## Commit 3 — VI-9c

Commit: `252eefd8507596729e3fd3585893228782e0a5cf`  
Message: `Track R: cover and count exceptional unit cells (#3044, VI-9c)`

Files:

- `MoltResearch/Discrepancy/ExceptionalCellCover.lean`
- one registration import in `MoltResearch/DiscrepancyAnalytic.lean`

Definitions:

```lean
noncomputable def cellsMeetingSet (K : Finset ℤ) (G : Set ℝ) : Finset ℤ
noncomputable def largeValueCells (K : Finset ℤ) (F : ℝ → ℂ) (V : ℝ) : Finset ℤ
```

Full theorem statements:

```lean
theorem cellsMeeting_exceptional_subset_biUnion
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (J : ℕ) (hJ : 0 < J) (G : Set ℝ) (K : Finset ℤ) :
    cellsMeetingSet K
        (bandPartOn (levelSmallSet P N v₀ v₁ g alpha) J G J) ⊆
      (Finset.Ico (v₀ (J - 1)) (v₁ (J - 1) + 1)).biUnion fun r =>
        largeValueCells K (levelCellPoly (P (J - 1)) (N (J - 1)) r g)
          (Real.exp (-(alpha (J - 1) * (r : ℝ) /
            ((2 * N (J - 1) : ℕ) : ℝ))))
```

```lean
theorem card_cellsMeeting_exceptional_le_sum
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (J : ℕ) (hJ : 0 < J) (G : Set ℝ) (K : Finset ℤ) :
    (cellsMeetingSet K
        (bandPartOn (levelSmallSet P N v₀ v₁ g alpha) J G J)).card
      ≤ ∑ r ∈ Finset.Ico (v₀ (J - 1)) (v₁ (J - 1) + 1),
          (largeValueCells K (levelCellPoly (P (J - 1)) (N (J - 1)) r g)
            (Real.exp (-(alpha (J - 1) * (r : ℝ) /
              ((2 * N (J - 1) : ℕ) : ℝ))))).card
```

```lean
theorem injectiveOn_cell_samples_of_same_parity (K : Finset ℤ) (tau : ℤ → ℝ)
    (htau : ∀ k ∈ K, tau k ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1))
    (hparity : ∀ k ∈ K, ∀ l ∈ K, k ≠ l → k + 2 ≤ l ∨ l + 2 ≤ k) :
    Set.InjOn tau K
```

```lean
theorem card_largeValueCells_prime_poly_pow_le (Y : Finset ℕ)
    (hY : ∀ p ∈ Y, p.Prime) (P : ℕ) (hP : 1 ≤ P)
    (hlo : ∀ p ∈ Y, P < p) (hhi : ∀ p ∈ Y, p ≤ 2 * P)
    (b : ℕ → ℂ) (hb : ∀ p, ‖b p‖ ≤ 1) (ell : ℕ) (hell : 1 ≤ ell)
    (K : Finset ℤ) (T V lam : ℝ) (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hlam : 0 < lam)
    (hKT : ∀ k ∈ K, -(T : ℝ) ≤ k ∧ (k : ℝ) + 1 ≤ T) :
    ((largeValueCells K
        (fun t => ∑ p ∈ Y, (b p / (p : ℂ))
          * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)) V).card : ℝ)
        * V ^ (2 * ell)
      ≤ 2 * (Real.exp Real.pi
          * ((T + 1) / ((P ^ ell : ℕ) : ℝ) + 2 * ((2 ^ ell : ℕ) : ℝ))
        * ((Nat.factorial ell : ℝ) ^ 2
            * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ)) ^ ell)
        * ((1 + lam) + (1 / lam)
            * (2 * Real.pi * Real.log ((2 * P) ^ ell)) ^ 2))
```

Finding: `firstPrevLargePart_*` has the strict precondition `j < J`, so it
cannot be invoked at the top index `j = J`. At the top level the proof must
unfold the complement directly; this yields last ordinary level `J-1`. The
even/odd cell split contributes the explicit factor `2`.

Verification:

```text
lake env lean MoltResearch/Discrepancy/ExceptionalCellCover.lean  EXIT 0
lake build MoltResearch.Discrepancy.ExceptionalCellCover         EXIT 0
final lake build MoltResearch.DiscrepancyAnalytic Conjectures    EXIT 0
```

## Commit 4 — VI-9d

Commit: `9f0581ed92c20aea06aaaec0681223b52fc60751`  
Message: `Track R: recut the exceptional large-value split (#3044, VI-9d)`

Files:

- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5ExceptionalReCut.lean`

Definitions:

```lean
noncomputable def exceptionalSplitThreshold (A : ℕ) : ℝ :=
  1 / Real.log A ^ 100

noncomputable def primeHighMomentCountCost (P ell : ℕ) (Y : Finset ℕ)
    (T V lam : ℝ) : ℝ :=
  (Real.exp Real.pi
      * ((T + 1) / ((P ^ ell : ℕ) : ℝ) + 2 * ((2 ^ ell : ℕ) : ℝ))
    * ((Nat.factorial ell : ℝ) ^ 2
        * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ)) ^ ell)
    * ((1 + lam) + (1 / lam)
        * (2 * Real.pi * Real.log ((2 * P) ^ ell)) ^ 2)) / V ^ (2 * ell)
```

Full theorem statements:

```lean
theorem exceptionalSplitThreshold_pos (A : ℕ) (hA : 1 < A) :
    0 < exceptionalSplitThreshold A
```

```lean
theorem sum_prime_integer_energy_large_card_le [HalaszLargeValuesAssumption]
    [PrimeLargeValuesAssumption]
    (P : ℕ) (hP : 2 ≤ P) (Y : Finset ℕ) (hY : ∀ p ∈ Y, p.Prime)
    (hYP : ∀ p ∈ Y, P ≤ p ∧ p ≤ 2 * P) (b : ℕ → ℂ)
    (N : ℕ) (a : ℕ → ℂ)
    (T : ℝ) (hT : 0 < T) (points : Finset ℝ)
    (hmem : ∀ t ∈ points, |t| ≤ T)
    (hsep : ∀ t ∈ points, ∀ u ∈ points, t ≠ u → 1 ≤ |t - u|)
    (V₀ delta CL : ℝ) (hV₀ : 0 ≤ V₀)
    (hlarge : ∀ t ∈ points.filter (fun t =>
      V₀ < ‖∑ p ∈ Y, (b p / (p : ℂ))
        * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖),
      ‖∑ n ∈ Finset.Icc 1 N, (a n / (n : ℂ))
        * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ delta)
    (hcard : ((points.filter (fun t =>
      V₀ < ‖∑ p ∈ Y, (b p / (p : ℂ))
        * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖)).card : ℝ) ≤ CL) :
    ∑ t ∈ points, ‖∑ p ∈ Y, (b p / (p : ℂ))
          * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖ ^ 2
        * ‖∑ n ∈ Finset.Icc 1 N, (a n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ^ 2
      ≤ V₀ ^ 2 * (64 * ((N : ℝ) + (points.card : ℝ) * Real.sqrt T)
            * (Real.log (2 * T) + 1)
            * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2)
        + delta ^ 2 * (64 * (1 + CL
              * Real.exp (-(Real.log P / (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
              * (Real.log (2 * T)) ^ 2)
            * (∑ p ∈ Y, ‖b p‖ ^ 2 / (p : ℝ) ^ 2)
            * (P : ℝ) / Real.log P)
```

```lean
theorem sum_prime_integer_energy_high_moment_le [HalaszLargeValuesAssumption]
    [PrimeLargeValuesAssumption]
    (P : ℕ) (hP : 2 ≤ P) (Y : Finset ℕ) (hY : ∀ p ∈ Y, p.Prime)
    (hlo : ∀ p ∈ Y, P < p) (hhi : ∀ p ∈ Y, p ≤ 2 * P)
    (b : ℕ → ℂ) (hb : ∀ p, ‖b p‖ ≤ 1)
    (ell : ℕ) (hell : 1 ≤ ell)
    (N : ℕ) (a : ℕ → ℂ)
    (T : ℝ) (hT : 0 < T) (points : Finset ℝ)
    (hmem : ∀ t ∈ points, |t| ≤ T)
    (hsep : ∀ t ∈ points, ∀ u ∈ points, t ≠ u → 1 ≤ |t - u|)
    (V₀ delta lam : ℝ) (hV₀ : 0 < V₀) (hlam : 0 < lam)
    (hlarge : ∀ t ∈ points.filter (fun t =>
      V₀ < ‖∑ p ∈ Y, (b p / (p : ℂ))
        * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖),
      ‖∑ n ∈ Finset.Icc 1 N, (a n / (n : ℂ))
        * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ delta) :
    ∑ t ∈ points, ‖∑ p ∈ Y, (b p / (p : ℂ))
          * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖ ^ 2
        * ‖∑ n ∈ Finset.Icc 1 N, (a n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ^ 2
      ≤ V₀ ^ 2 * (64 * ((N : ℝ) + (points.card : ℝ) * Real.sqrt T)
            * (Real.log (2 * T) + 1)
            * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2)
        + delta ^ 2 * (64 * (1 + primeHighMomentCountCost P ell Y T V₀ lam
              * Real.exp (-(Real.log P / (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
              * (Real.log (2 * T)) ^ 2)
            * (∑ p ∈ Y, ‖b p‖ ^ 2 / (p : ℝ) ^ 2)
            * (P : ℝ) / Real.log P)
```

Finding: the prime-support term now contains `CL` (then the explicit
high-moment cost) multiplied by the MR exponential saving. There is no additive
`T/P` term. The integer-support term remains in the native IK 9.6 shape
`N + #points * sqrt T`.

Verification:

```text
lake env lean Conjectures/C0002_erdos_discrepancy/src/TrackCStage5ExceptionalReCut.lean  EXIT 0
final lake build MoltResearch.DiscrepancyAnalytic Conjectures                          EXIT 0
```

## Commit 5 — VI-9e

Commit: `a006fd68c336b00f5b7cac78b0d70a4a6b9121df`  
Message: `Track R: twist the exceptional Halasz leg before Abel (#3044, VI-9e)`

Files:

- `MoltResearch/Discrepancy/ExceptionalHalaszTwist.lean`
- one registration import in `MoltResearch/DiscrepancyAnalytic.lean`

Definitions:

```lean
noncomputable def cheapTwistedDirichletCost
    (eps W D : ℝ) (a b : ℕ) : ℝ :=
  2 * (b : ℝ) *
      (eps + Real.exp (W * Real.log (Real.log b) + W - D / 2)) /
    ((a + 1 : ℕ) : ℝ)

noncomputable def exceptionalTwistedQuotientCost
    (x0 : ℕ) (eps W D : ℝ) (a b : ℕ) : ℝ :=
  if x0 ≤ a then cheapTwistedDirichletCost eps W D a b
  else cellHalaszTrivialCost a b

noncomputable def exceptionalTwistedRamareCost
noncomputable def cellHalaszReCutBound
```

Full theorem statements (the two composition statements use the definitions
above verbatim):

```lean
theorem cheap_halasz_twisted_dirichlet_block (eps : ℝ) (heps : 0 < eps) :
    ∃ (x0 : ℕ) (W : ℝ), 0 < W ∧
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → g 1 = 1 →
        (∀ n, ‖g n‖ ≤ 1) →
      ∀ a b : ℕ, x0 ≤ a → a < b →
      ∀ D : ℝ, 2 ≤ D →
        (∀ u : ℕ, a ≤ u → u ≤ b → NonPretentiousAt g D u) →
      ∀ t : ℝ, |2 * Real.pi * t| ≤ (D / 2) * a →
        ‖∑ n ∈ Finset.Ioc a b, (g n / (n : ℂ)) *
            ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
          ≤ cheapTwistedDirichletCost eps W D a b
```

```lean
theorem cheap_halasz_levelFreeTwist_dirichlet_block
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (x0 : ℕ) (W : ℝ), 0 < W ∧
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → g 1 = 1 →
        (∀ n, ‖g n‖ ≤ 1) →
      ∀ levels : List (Finset ℕ),
        (∀ Q ∈ levels, ∀ p ∈ Q, p.Prime) →
      ∀ a b : ℕ, x0 ≤ a → a < b →
      ∀ D : ℝ, 2 ≤ D →
        (∀ u : ℕ, a ≤ u → u ≤ b → NonPretentiousAt g (2 * D) u) →
      ∀ t : ℝ, |2 * Real.pi * t| ≤ (D / 2) * a →
        ‖∑ n ∈ Finset.Ioc a b,
            (levelFreeTwist g levels n / (n : ℂ)) *
              ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
          ≤ cheapTwistedDirichletCost eps W D a b
```

```lean
theorem exceptionalTwistedQuotientCost_nonneg
    (x0 : ℕ) (eps W D : ℝ) (a b : ℕ) (heps : 0 ≤ eps) :
    0 ≤ exceptionalTwistedQuotientCost x0 eps W D a b
```

```lean
theorem norm_filter_levelFreeTwist_quotient_le_recut
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (x0 : ℕ) (W : ℝ), cellHalaszThreshold ≤ x0 ∧ 0 < W ∧
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → g 1 = 1 →
        (∀ n, ‖g n‖ ≤ 1) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ∀ levels : List (Finset ℕ),
        (∀ Q ∈ levels, ∀ p ∈ Q, p.Prime) →
      ∀ a b : ℕ, a ≤ b →
      ∀ D : ℝ, 2 ≤ D →
        (∀ u : ℕ, a ≤ u → u ≤ b → NonPretentiousAt g (2 * D) u) →
      ∀ t : ℝ, |2 * Real.pi * t| ≤ (D / 2) * a →
        ‖∑ n ∈ (Finset.Ioc a b).filter (fun n => ∀ p ∈ P, ¬ p ∣ n),
            (levelFreeTwist g levels n / (n : ℂ)) *
              ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
          ≤ exceptionalTwistedQuotientCost x0 eps W D a b
```

```lean
theorem norm_ramare_weighted_poly_le_sum_cost
    (g : ℕ → ℂ) (P : Finset ℕ) (levels : List (Finset ℕ))
    (A B : ℕ) (t : ℝ) (C : ℕ → ℕ → ℝ)
    (hquot : ∀ n1 ∈ (Finset.Icc 1 B).filter (fun n => n.primeFactors ⊆ P),
      ‖∑ n ∈ (Finset.Ioc (A / n1) (B / n1)).filter
          (fun n => ∀ p ∈ P, ¬ p ∣ n),
          (levelFreeTwist g levels n / (n : ℂ)) *
            ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
        ≤ C (A / n1) (B / n1)) :
    ‖∑ n ∈ Finset.Ioc A B,
        (levelFreeTwist g levels n / (n : ℂ)) *
          ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ) /
            (((P.filter (· ∣ n)).card : ℂ) + 1)‖
      ≤ ∑ n1 ∈ (Finset.Icc 1 B).filter (fun n => n.primeFactors ⊆ P),
          (1 : ℝ) / n1 * C (A / n1) (B / n1)
```

```lean
theorem norm_levelFreeTwist_ramare_poly_le_recut
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (x0 : ℕ) (W : ℝ), cellHalaszThreshold ≤ x0 ∧ 0 < W ∧
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → g 1 = 1 →
        (∀ n, ‖g n‖ ≤ 1) →
      ∀ levels : List (Finset ℕ), (∀ Q ∈ levels, ∀ p ∈ Q, p.Prime) →
      ∀ A B : ℕ, A ≤ B → ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ∀ D : ℝ, 2 ≤ D →
      (∀ n1 ∈ (Finset.Icc 1 B).filter (fun n => n.primeFactors ⊆ P),
        ∀ u, A/n1 ≤ u → u ≤ B/n1 → NonPretentiousAt g (2*D) u) →
      ∀ t : ℝ,
      (∀ n1 ∈ (Finset.Icc 1 B).filter (fun n => n.primeFactors ⊆ P),
        |2*Real.pi*t| ≤ (D/2) * (A/n1 : ℕ)) →
      ‖∑ n ∈ Finset.Ioc A B,
        (levelFreeTwist g levels n/(n:ℂ)) *
          ((Real.fourierChar (-(Real.log n*t)) : Circle) : ℂ) /
          (((P.filter (· ∣ n)).card : ℂ)+1)‖
        ≤ exceptionalTwistedRamareCost x0 eps W D A B P
```

```lean
theorem pSmoothHarmonicMass_le_exp_primeMass
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (B : ℕ) :
    pSmoothHarmonicMass B P ≤ Real.exp (2 * ∑ p ∈ P, (1 : ℝ) / p)
```

```lean
theorem norm_typicalS_quot_block_poly_le_recut
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (x0 : ℕ) (W : ℝ), cellHalaszThreshold ≤ x0 ∧ 0 < W ∧
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → g 1 = 1 →
        (∀ n, ‖g n‖ ≤ 1) →
      ∀ A B q : ℕ, 1 ≤ q → A ≤ B →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ∀ rest : List (Finset ℕ), (∀ Q ∈ rest, ∀ p ∈ Q, p.Prime) →
      ∀ D : ℝ, 2 ≤ D →
      (∀ n1 ∈ (Finset.Icc 1 (B/q)).filter (fun n => n.primeFactors ⊆ P),
        ∀ u, (A/q)/n1 ≤ u → u ≤ (B/q)/n1 → NonPretentiousAt g (2*D) u) →
      ∀ t : ℝ,
      (∀ n1 ∈ (Finset.Icc 1 (B/q)).filter (fun n => n.primeFactors ⊆ P),
        |2*Real.pi*t| ≤ (D/2) * (((A/q)/n1 : ℕ) : ℝ)) →
      ‖∑ n ∈ Finset.Ioc (A/q) (B/q),
        (typicalSQuotCoeff g P (typicalS 0 B rest) n/(n:ℂ)) *
          ((Real.fourierChar (-(Real.log n*t)) : Circle) : ℂ)‖
        ≤ cellHalaszReCutBound x0 eps W D (A/q) (B/q) P rest
```

Finding: the frequency is absorbed into the completely multiplicative twist
before Abel summation. Thus the cost contains no factor `3+2πT`. Long quotients
use the twisted Halász cost; short quotients keep their own harmonic mass.
The smooth factor is bounded by `exp(2*sum_{p in P} 1/p)`, rather than a uniform
maximum over every quotient.

Verification:

```text
lake env lean MoltResearch/Discrepancy/ExceptionalHalaszTwist.lean  EXIT 0
lake build MoltResearch.Discrepancy.ExceptionalHalaszTwist         EXIT 0
final lake build MoltResearch.DiscrepancyAnalytic Conjectures      EXIT 0
```

## Commit 6 — VI-9f (verified mid/far part)

Commit: `9d0a613ffb458b839813fe2609e33ac6e9df28a8`  
Message: `Track R: split mid and far pretentious frequencies (#3044, VI-9f)`

Files:

- `MoltResearch/Discrepancy/PretentiousBandSplit.lean`
- `Conjectures/C0002_erdos_discrepancy/src/Interfaces/FarRegimeRepulsion.lean`
- `Conjectures/C0002_erdos_discrepancy/src/TrackCStage5PretentiousBandSplit.lean`
- `Problems/sources/tao2015_statements.md`
- one registration import in `MoltResearch/DiscrepancyAnalytic.lean`

Definition:

```lean
noncomputable def exceptionalRepulsionRho : ℝ :=
  1 / 6 - 1 / (3 * Real.pi)
```

Full theorem and interface statements:

```lean
theorem exceptionalRepulsionRho_pos : 0 < exceptionalRepulsionRho
```

```lean
theorem continuous_pretentiousDistSq_archTwist (f : ℕ → ℂ) (y : ℕ) :
    Continuous (fun t : ℝ =>
      pretentiousDistSq f
        (fun n => (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) y)
```

```lean
theorem exists_pretentiousDistSq_archTwist_minimizer
    (f : ℕ → ℂ) (y : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ t1 ∈ Set.Icc (-T) T, ∀ t ∈ Set.Icc (-T) T,
      pretentiousDistSq f
          (fun n => (n : ℂ) ^ (-(Complex.I * (t1 : ℂ)))) y ≤
        pretentiousDistSq f
          (fun n => (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) y
```

```lean
theorem pretentiousDistSq_archTwist_ge_mid
    (f : ℕ → ℂ) (hf : Unimodular f) (t1 t : ℝ) (y : ℕ)
    (hy : 3 ≤ y) (hsep : 6 ≤ |t - t1|) (A : ℝ)
    (hA : pretentiousDistSq f
      (fun n => (n : ℂ) ^ (-(Complex.I * (t1 : ℂ)))) y ≤ A)
    (hfit : exceptionalRepulsionRho * Real.log (Real.log y) ≤
      ((∑ p ∈ y.primesBelow, (1 : ℝ) / p) -
          Real.log (Real.log (|t - t1| + 2)) - 24) / 3 - A) :
    exceptionalRepulsionRho * Real.log (Real.log y) ≤
      pretentiousDistSq f
        (fun n => (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) y
```

```lean
class FarRegimeRepulsionAssumption : Prop where
  bound : ∃ y0 : ℕ, ∀ (f : ℕ → ℂ) (y : ℕ) (t1 t : ℝ),
    Unimodular f → y0 ≤ y → 3 ≤ y →
    |t1| ≤ y → |t| ≤ y →
    pretentiousDistSq f
        (fun n => (n : ℂ) ^ (-(Complex.I * (t1 : ℂ)))) y ≤
      pretentiousDistSq f
        (fun n => (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) y →
    (Real.log y) ^ (20 : ℕ) < |t - t1| →
    exceptionalRepulsionRho * Real.log (Real.log y) ≤
      pretentiousDistSq f
        (fun n => (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) y
```

```lean
theorem pretentiousDistSq_archTwist_ge_far
    [FarRegimeRepulsionAssumption] :
    ∃ y0 : ℕ, ∀ (f : ℕ → ℂ) (y : ℕ) (t1 t : ℝ),
      Unimodular f → y0 ≤ y → 3 ≤ y → |t1| ≤ y → |t| ≤ y →
      pretentiousDistSq f (fun n => (n:ℂ)^(-(Complex.I*(t1:ℂ)))) y ≤
        pretentiousDistSq f (fun n => (n:ℂ)^(-(Complex.I*(t:ℂ)))) y →
      (Real.log y)^20 < |t-t1| →
      exceptionalRepulsionRho * Real.log (Real.log y) ≤
        pretentiousDistSq f (fun n => (n:ℂ)^(-(Complex.I*(t:ℂ)))) y
```

```lean
theorem pretentiousDistSq_archTwist_ge_of_mid_or_far
    [FarRegimeRepulsionAssumption] :
    ∃ y0 : ℕ, ∀ (f : ℕ → ℂ) (y : ℕ) (t1 t : ℝ),
      Unimodular f → y0 ≤ y → 3 ≤ y → |t1| ≤ y → |t| ≤ y →
      6 ≤ |t-t1| →
      pretentiousDistSq f (fun n => (n:ℂ)^(-(Complex.I*(t1:ℂ)))) y ≤
        pretentiousDistSq f (fun n => (n:ℂ)^(-(Complex.I*(t:ℂ)))) y →
      ((|t-t1| ≤ (Real.log y)^20 ∧
        exceptionalRepulsionRho * Real.log (Real.log y) ≤
          ((∑ p ∈ y.primesBelow, (1:ℝ)/p) -
            Real.log (Real.log (|t-t1|+2)) - 24)/3 -
            pretentiousDistSq f (fun n => (n:ℂ)^(-(Complex.I*(t1:ℂ)))) y) ∨
        (Real.log y)^20 < |t-t1|) →
      exceptionalRepulsionRho * Real.log (Real.log y) ≤
        pretentiousDistSq f (fun n => (n:ℂ)^(-(Complex.I*(t:ℂ)))) y
```

Finding: the compact minimizer and mid regime compose directly with
`pretentiousDistSq_twist_ge`. The far regime did not close from current Track L
lemmas and is isolated as the single permitted interface, cited to
arXiv:1503.05121, Appendix A, Proposition A.3. No instance is declared.

Additional blocker found during the required audit: the central `T0` estimate
does not follow from the current GHS closed forms. In particular,
`rieszMeanC_log_halasz_shell_le` contains

```text
loglog x * x * sqrt((exp pi)^2 * 10^15 * ((exp 5*(2+log x)*exp(-A))^2 + 1))
```

and `rieszMean_log_le_closed` also has the leading term
`x*(93*log x + 2*loglog x + 491)`. The `+1` floor and the displayed log factors
cannot yield the required loglog-free
`exp(-M/2)/(1+|t-t1|) + (log x)^(-1/16)` pointwise estimate. The brief permits
only one new interface, specifically the far-regime one, so a second interface
was not introduced.

Verification:

```text
lake env lean MoltResearch/Discrepancy/PretentiousBandSplit.lean                           EXIT 0
lake build MoltResearch.Discrepancy.PretentiousBandSplit                                  EXIT 0
lake env lean Conjectures/C0002_erdos_discrepancy/src/Interfaces/FarRegimeRepulsion.lean  EXIT 0
lake env lean Conjectures/C0002_erdos_discrepancy/src/TrackCStage5PretentiousBandSplit.lean EXIT 0
python3 scripts/check_interfaces.py                                                       EXIT 0
final lake build MoltResearch.DiscrepancyAnalytic Conjectures                             EXIT 0
```

## Commit 7 — A2-IV-2

Commit: `895b376fb34dc2f08ff88a7697ceb8822821ba2a`  
Message: `Track R: prove slice weight conversion (#3044, A2-IV-2)`

Files:

- `MoltResearch/Discrepancy/SliceWeightConversion.lean`
- one registration import in `MoltResearch/DiscrepancyAnalytic.lean`

Full theorem statements:

```lean
theorem weight_conversion_coefficient_le (A n H m : ℕ)
    (hA : 0 < A) (hn : 0 < n) (hmn : n < m) (hmH : m ≤ n + H) :
    ‖(1 : ℂ) - (n : ℂ) / (A : ℂ) * ((A : ℂ) / (m : ℂ))‖
      ≤ (H : ℝ) / n

theorem norm_short_sum_sub_scaled_weighted_le
    (f : ℕ → ℂ) (hf : ∀ m, ‖f m‖ ≤ 1)
    (A n H : ℕ) (hA : 0 < A) (hn : 0 < n) :
    ‖(∑ m ∈ Finset.Ioc n (n + H), f m) -
        (n : ℂ) / (A : ℂ) *
          ∑ m ∈ Finset.Ioc n (n + H), f m * ((A : ℂ) / (m : ℂ))‖
      ≤ (H : ℝ)^2 / n

theorem slice_scale_sq_le (A s n : ℕ) (hA : 0 < A)
    (hn : n ∈ Finset.Ioc A (A + s)) :
    ((n : ℝ) / A)^2 ≤ (((A + s : ℕ) : ℝ) / A)^2

theorem slice_weight_conversion_error_le (A s H : ℕ) (hA : 0 < A) :
    ∑ n ∈ Finset.Ioc A (A + s), 2 * (((H : ℝ)^2 / n)^2) / n
      ≤ 2 * (H : ℝ)^4 * s / (A : ℝ)^3

theorem slice_energy_le_scaled_weighted_energy
    (f : ℕ → ℂ) (hf : ∀ m, ‖f m‖ ≤ 1)
    (A s H : ℕ) (hA : 0 < A) :
    ∑ n ∈ Finset.Ioc A (A + s),
        ‖∑ m ∈ Finset.Ioc n (n + H), f m‖^2 / n
      ≤ 2 * (((A + s : ℕ) : ℝ) / A)^2 *
          (∑ n ∈ Finset.Ioc A (A + s),
            ‖∑ m ∈ Finset.Ioc n (n + H),
                f m * ((A : ℂ) / (m : ℂ))‖^2 / n) +
        2 * (H : ℝ)^4 * s / (A : ℝ)^3
```

Finding: the conversion is purely elementary. Each coefficient changes by at
most `H/n`, there are `H` coefficients, and the slice square inequality gives
exactly the advertised `2*((A+s)/A)^2` main factor and `2H^4s/A^3` error.

Verification:

```text
lake env lean MoltResearch/Discrepancy/SliceWeightConversion.lean  EXIT 0
lake build MoltResearch.Discrepancy.SliceWeightConversion         EXIT 0
forbid scripts and aggregator coverage                            EXIT 0
final lake build MoltResearch.DiscrepancyAnalytic Conjectures     EXIT 0
```

## Commit 8 — A2-IV-1

Commit: `ac05d3ae68d2187cb2fdb3b9e0c68ffa635879bc`  
Message: `Track R: prove typical-set low band (#3044, A2-IV-1)`

Files:

- `MoltResearch/Discrepancy/LowBandTypicalS.lean`
- one registration import in `MoltResearch/DiscrepancyAnalytic.lean`

Full theorem statements:

```lean
theorem sum_filter_eq_levelFreeTwist_dirichlet
    (g : ℕ → ℂ) (S : List (Finset ℕ)) (a b : ℕ) (t : ℝ) :
    ∑ m ∈ (Finset.Ioc a b).filter
        (fun n => ∀ Q ∈ S, ∀ p ∈ Q, ¬ p ∣ n),
        (g m / (m : ℂ)) *
          ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ) =
      ∑ m ∈ Finset.Ioc a b,
        (levelFreeTwist g S m / (m : ℂ)) *
          ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)

theorem norm_typicalS_dirichlet_poly_le_low_band
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (x0 : ℕ) (W : ℝ), 0 < W ∧
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → g 1 = 1 →
        (∀ n, ‖g n‖ ≤ 1) →
      ∀ levels : List (Finset ℕ),
        (∀ Q ∈ levels, ∀ p ∈ Q, p.Prime) →
      ∀ a b : ℕ, x0 ≤ a → a < b →
      ∀ D : ℝ, 2 ≤ D →
        (∀ u : ℕ, a ≤ u → u ≤ b → NonPretentiousAt g (2 * D) u) →
      ∀ t : ℝ, |2 * Real.pi * t| ≤ (D / 2) * a →
        ‖∑ m ∈ typicalS a b levels,
            (g m / (m : ℂ)) *
              ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖
          ≤ (2 ^ levels.length : ℕ) *
              cheapTwistedDirichletCost eps W D a b

theorem abs_lt_set_eq_Ioo (K : ℝ) :
    {t : ℝ | |t| < K} = Set.Ioo (-K) K

theorem integral_norm_typicalS_dirichlet_poly_sq_le_low_band
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (x0 : ℕ) (W : ℝ), 0 < W ∧
      ∀ g : ℕ → ℂ, CompletelyMultiplicativeC g → g 1 = 1 →
        (∀ n, ‖g n‖ ≤ 1) →
      ∀ levels : List (Finset ℕ),
        (∀ Q ∈ levels, ∀ p ∈ Q, p.Prime) →
      ∀ a b : ℕ, x0 ≤ a → a < b →
      ∀ D : ℝ, 2 ≤ D →
        (∀ u : ℕ, a ≤ u → u ≤ b → NonPretentiousAt g (2 * D) u) →
      ∀ K : ℝ, 0 ≤ K → 2 * Real.pi * K ≤ (D / 2) * a →
        (∫ t in {t : ℝ | |t| < K},
          ‖∑ m ∈ typicalS a b levels,
              (g m / (m : ℂ)) *
                ((Real.fourierChar (-(Real.log m * t)) : Circle) : ℂ)‖^2)
          ≤ 2 * K *
              ((2 ^ levels.length : ℕ) *
                cheapTwistedDirichletCost eps W D a b)^2
```

Finding: inclusion--exclusion produces exactly `2^levels.length` terms. Every
term is the normalized polynomial of a `levelFreeTwist`, so VI-9e applies at
half the base distance strength. Integrating the uniform bound over `(-K,K)`
costs exactly `2K`.

Verification:

```text
lake env lean MoltResearch/Discrepancy/LowBandTypicalS.lean  EXIT 0
lake build MoltResearch.Discrepancy.LowBandTypicalS         EXIT 0
forbid scripts and aggregator coverage                      EXIT 0
final lake build MoltResearch.DiscrepancyAnalytic Conjectures EXIT 0
```

## Final verification

All required commands were run from the worktree root after the final commit:

```text
./scripts/forbid_sorry.sh                                      EXIT 0
./scripts/forbid_axiom_unsafe.sh                               EXIT 0
./scripts/check_layering.sh                                    EXIT 0
python3 scripts/check_aggregator_coverage.py                   EXIT 0
python3 scripts/check_interfaces.py                            EXIT 0
lake build MoltResearch.DiscrepancyAnalytic Conjectures        EXIT 0
```

`check_aggregator_coverage.py` reported 173 modules, 171 reachable, plus the two
known allowlisted example modules. `check_interfaces.py` scanned 70 files and
found 16 interface classes. It retained seven unrelated pre-existing warnings;
the new `FarRegimeRepulsionAssumption` has both a citation and registry entry.
The final build completed all 8171 jobs successfully.

## Accounting discrepancies found

1. **Fourier-weight accounting.** The old exceptional schedule allowed
   `exceptional shares ≤ dyadic share / (4H/A)^2` and then concluded an unscaled
   budget. The honest share is only `≤ dyadic share`; the conclusion retains
   `(4H/A)^2`. The old permitted allocation is larger by `(A/(4H))^2`.

2. **Prime large-value count.** The old first-moment route inserted `T/P` into
   the prime-support term. The high-moment separated count removes that term;
   the only cardinality contribution is `CL * exp(-log P/(log 2T)^(3/4)) *
   (log 2T)^2`.

3. **Abel frequency loss.** Estimating an untwisted partial sum and then
   differentiating the phase inserted `3+2πT`. Twisting first removes the
   entire factor. Abel now differentiates only `1/n`.

4. **Nonuniform quotient costs.** A maximum quotient cost incorrectly charged
   every short branch at the worst scale. The re-cut retains one cost per
   quotient; short quotients pay their own harmonic mass.

5. **Smooth mass.** The selected prime smooth mass is now bounded directly by
   `exp(2*sum_{p in P}1/p)`, rather than hidden in the old broad envelope.

6. **Central `T0` GHS leg.** The current tree does not expose the needed
   loglog-free `1/(1+|t-t1|)` pointwise result. Its best shell statement retains
   a `+1` floor under the square root and external `loglog` multipliers. This is
   an additional genuine fit failure beyond the far-regime gap anticipated in
   the brief.

## Work left undone and exact blocker

### VI-9f central window

Wanted:

```text
|F(1+it)| ≤ C * (exp(-M/2)/(1+|t-t1|) + (log A)^(-1/16))
```

uniformly for `|t-t1| ≤ (log A)^(1/16)`, with the exponential quality free of
extra `loglog A` factors, followed by its squared integration.

Available shell term:

```text
loglog x * x * sqrt((exp pi)^2 * 10^15 *
  ((exp 5 * (2+log x) * exp(-A))^2 + 1))
```

The `+1` floor survives even as `A` grows, and the outside `loglog x` does not
fit the fixed-strength central budget. `rieszMean_log_le_closed` is weaker still
because of its leading `x*(93*log x + 2*loglog x + 491)` term. This is the exact
reason the central-window theorem was not stated.

### VI-9g

Not attempted. Its fixed-ε S6 schedule needs the complete VI-9f exceptional
estimate, including the central `T0` window. The far-regime interface alone is
not sufficient.

### A2-IV-3, A2-V, and `sliceMeanSquareA2`

Not attempted, in accordance with the instruction not to enter A2-IV-3/A2-V
unless every predecessor is complete. Consequently this run does **not** claim
the theorem `sliceMeanSquareA2 : SliceMeanSquareA2`.

## Far-regime status

The far-regime lemma did not close in-tree. It is represented by exactly one
new class, `FarRegimeRepulsionAssumption`, with source citation and no instance.
The minimizer and the entire mid/far consumer split compile against that class.
