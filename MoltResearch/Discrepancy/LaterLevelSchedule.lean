import MoltResearch.Discrepancy.LevelSizes
import MoltResearch.Discrepancy.PrimeMassCell

/-!
# Later inner-band levels in schedule form (Track R, A2-III, VI-8b)

The later-level fit in the assembly still contains the prime mass of the
previous e-adic cell and a factorial moment.  Brun--Titchmarsh replaces that
mass by `256 / log Pmom`; `levelJ_moment_le` then replaces the whole factorial
ratio by

`2(ℓ+1) · (2ℓ²(256/log Pmom)/large²)^ℓ`.

The `large` used here is already the schedule lower envelope supplied by
`levelLargeness_ge`, namely
`Qprev^(-β) exp(-β/(2Nprev))`.  Thus the resulting fit has no cell prime
sum and is one explicit inequality per previous cell.
-/

namespace MoltResearch

/-- The closed moment envelope used by every later-level cell. -/
noncomputable def laterMomentScheduleBound (ell Pmom : ℕ) (large : ℝ) : ℝ :=
  2 * ((ell : ℝ) + 1)
    * (2 * (ell : ℝ) ^ 2 * (256 / Real.log Pmom) / large ^ 2) ^ ell

/-- The factorial moment of a dyadic prime cell, divided by the schedule's
largeness envelope, is bounded by a closed expression. -/
theorem dyadic_moment_ratio_le_schedule (ell Pmom : ℕ) (Y : Finset ℕ)
    (large : ℝ) (hPmom : 2 ≤ Pmom) (hlarge : 0 < large)
    (hY : ∀ p ∈ Y, p.Prime) (hlo : ∀ p ∈ Y, Pmom < p)
    (hhi : ∀ p ∈ Y, p ≤ 2 * Pmom) :
    ((Nat.factorial ell : ℝ) ^ 2
        * (((2 ^ (ell + 1) : ℕ) : ℝ) * ((ell : ℝ) + 1)
          * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ)) ^ ell)) /
        large ^ (2 * ell)
      ≤ laterMomentScheduleBound ell Pmom large := by
  have hsigma0 : 0 ≤ ∑ p ∈ Y, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_nonneg fun p _ => by positivity
  have hsigma := sum_one_div_prime_dyadic_le Pmom hPmom Y hY hlo hhi
  have hlog : 0 < Real.log Pmom := Real.log_pos (by exact_mod_cast hPmom)
  have hbase :
      2 * (ell : ℝ) ^ 2 * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ)) / large ^ 2
        ≤ 2 * (ell : ℝ) ^ 2 * (256 / Real.log Pmom) / large ^ 2 := by
    gcongr
  refine (levelJ_moment_le ell _ large hsigma0 hlarge).trans ?_
  have hbase0 : 0 ≤
      2 * (ell : ℝ) ^ 2 * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ)) / large ^ 2 := by
    positivity
  have hpows :
      (2 * (ell : ℝ) ^ 2 * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ)) / large ^ 2) ^ ell
        ≤ (2 * (ell : ℝ) ^ 2 * (256 / Real.log Pmom) / large ^ 2) ^ ell := by
    exact pow_le_pow_left₀ hbase0 hbase ell
  unfold laterMomentScheduleBound
  gcongr

/-- The exact later-level fit required by the assembly follows from one
closed inequality with the dyadic moment envelope. -/
theorem laterLevel_fit_of_schedule
    (Ncur Nprev v₀cur v₁cur ell Pmom Aint : ℕ) (Y : Finset ℕ)
    (Pcur Qcur alpha Qprev beta T c₃ eps rho kappa : ℝ)
    (hNcur : 0 < Ncur) (hNprev : 0 < Nprev)
    (halpha : 0 < alpha) (hbeta : 0 ≤ beta)
    (hPcur : 0 < Pcur) (hPQcur : Pcur ≤ Qcur) (hQprev : 0 < Qprev)
    (hPmom : 2 ≤ Pmom) (hT : 0 ≤ T)
    (hY : ∀ p ∈ Y, p.Prime) (hlo : ∀ p ∈ Y, Pmom < p)
    (hhi : ∀ p ∈ Y, p ≤ 2 * Pmom)
    (hschedule :
      (2 * (Ncur : ℝ) * (Real.log Qcur - Real.log Pcur) + 2)
        * ((Pcur ^ (-(2 * alpha))
              * Real.exp (2 * alpha / ((2 * Ncur : ℕ) : ℝ))
              * (((2 * Ncur : ℕ) : ℝ) / (2 * alpha) + 1))
          * ((Real.exp Real.pi
                * (T / (((Pmom ^ ell) * Aint : ℕ) : ℝ)
                  + 2 * ((2 ^ (ell + 1) : ℕ) : ℝ)))
            * laterMomentScheduleBound ell Pmom
                (Qprev ^ (-beta)
                  * Real.exp (-(beta / ((2 * Nprev : ℕ) : ℝ))))))
        ≤ kappa * bandBudget c₃ eps rho) :
    (2 * (Ncur : ℝ) * (Real.log Qcur - Real.log Pcur) + 2)
        * ((Pcur ^ (-(2 * alpha))
              * Real.exp (2 * alpha / ((2 * Ncur : ℕ) : ℝ))
              * (((2 * Ncur : ℕ) : ℝ) / (2 * alpha) + 1))
          * ((Real.exp Real.pi
                * (T / (((Pmom ^ ell) * Aint : ℕ) : ℝ)
                  + 2 * ((2 ^ (ell + 1) : ℕ) : ℝ)))
            * (((Nat.factorial ell : ℝ) ^ 2
              * (((2 ^ (ell + 1) : ℕ) : ℝ) * ((ell : ℝ) + 1)
                * (∑ p ∈ Y, (1 : ℝ) / (p : ℝ)) ^ ell)) /
                (Qprev ^ (-beta)
                  * Real.exp (-(beta / ((2 * Nprev : ℕ) : ℝ)))) ^ (2 * ell))))
      ≤ kappa * bandBudget c₃ eps rho := by
  let large := Qprev ^ (-beta)
    * Real.exp (-(beta / ((2 * Nprev : ℕ) : ℝ)))
  have hlarge : 0 < large := by
    dsimp [large]
    positivity
  have hmoment := dyadic_moment_ratio_le_schedule ell Pmom Y large
    hPmom hlarge hY hlo hhi
  have hcount0 : 0 ≤ 2 * (Ncur : ℝ) * (Real.log Qcur - Real.log Pcur) + 2 := by
    have hlog := Real.log_le_log hPcur hPQcur
    have hN0 : (0 : ℝ) ≤ (Ncur : ℝ) := by positivity
    nlinarith [mul_nonneg hN0 (sub_nonneg.mpr hlog)]
  have hsmall0 : 0 ≤ Pcur ^ (-(2 * alpha))
      * Real.exp (2 * alpha / ((2 * Ncur : ℕ) : ℝ))
      * (((2 * Ncur : ℕ) : ℝ) / (2 * alpha) + 1) := by
    positivity
  have hE0 : 0 ≤ Real.exp Real.pi
      * (T / (((Pmom ^ ell) * Aint : ℕ) : ℝ)
        + 2 * ((2 ^ (ell + 1) : ℕ) : ℝ)) := by positivity
  dsimp [large] at hmoment
  calc
    (2 * (Ncur : ℝ) * (Real.log Qcur - Real.log Pcur) + 2) * _
        ≤ (2 * (Ncur : ℝ) * (Real.log Qcur - Real.log Pcur) + 2)
          * ((Pcur ^ (-(2 * alpha))
                * Real.exp (2 * alpha / ((2 * Ncur : ℕ) : ℝ))
                * (((2 * Ncur : ℕ) : ℝ) / (2 * alpha) + 1))
            * ((Real.exp Real.pi
                  * (T / (((Pmom ^ ell) * Aint : ℕ) : ℝ)
                    + 2 * ((2 ^ (ell + 1) : ℕ) : ℝ)))
              * laterMomentScheduleBound ell Pmom
                  (Qprev ^ (-beta)
                    * Real.exp (-(beta / ((2 * Nprev : ℕ) : ℝ)))))) := by
      gcongr
    _ ≤ kappa * bandBudget c₃ eps rho := hschedule

end MoltResearch
