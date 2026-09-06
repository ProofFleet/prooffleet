import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalAggregate

/-!
# Track R A2-V': the exceptional raw-cover envelope

The raw number of frequency cells in the exceptional band is controlled at
the last ordinary level.  This leaf chooses the adaptive moment at each
ordinary anchor and reduces the raw cover to the sum of the closed
high-moment envelopes.  The remaining estimate is purely numerical.
-/

namespace MoltResearch

namespace Tao2015

open Finset ExpSums

/-- Adaptive moment used to count the exceptional frequency cover from the
last ordinary level. -/
noncomputable def sliceA2OrdinaryCoverMoment
    (P0 ratio0 eta J : ℕ) (eps rho0 T : ℝ) (r : ℕ) : ℕ :=
  adaptivePrimeMoment
    (sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r) T

theorem sliceA2OrdinaryCoverMoment_one_le
    (P0 ratio0 eta J : ℕ) (eps rho0 T : ℝ) (r : ℕ) :
    1 ≤ sliceA2OrdinaryCoverMoment P0 ratio0 eta J eps rho0 T r := by
  exact adaptivePrimeMoment_one_le _ _

/-- The literal raw cover used by the shifted capstone is at most the sum of
the closed moment envelopes at the last ordinary cells. -/
theorem sliceA2ExceptionalCover_le_envelopes
    (g : ℕ → ℂ) (hg : ∀ p, ‖g p‖ ≤ 1)
    (P0 ratio0 eta J A1 : ℕ) (eps epsc rho0 K1 K2 T : ℝ)
    (hP0 : 2 ≤ P0) (hJ : 0 < J) (hT : 1 ≤ T) (hTK2 : K2 + 2 ≤ T)
    (hanchor : ∀ r ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (J - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (J - 1) eps rho0 + 1),
      6 ≤ sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r)
    (hlogAnchor : ∀ r ∈ Finset.Ico
      (sliceA2OrdinaryV0 P0 ratio0 eta (J - 1) eps rho0)
      (sliceA2OrdinaryV1 P0 ratio0 eta (J - 1) eps rho0 + 1),
      256 ≤ Real.log
        (sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r : ℝ)) :
    sliceA2ExceptionalCover g P0 ratio0 eta J A1
        eps epsc rho0 K1 K2 ≤
      ∑ r ∈ Finset.Ico
          (sliceA2OrdinaryV0 P0 ratio0 eta (J - 1) eps rho0)
          (sliceA2OrdinaryV1 P0 ratio0 eta (J - 1) eps rho0 + 1),
        2 * ordinaryCoverMomentEnvelope
          (sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0 r)
          (sliceA2OrdinaryCoverMoment P0 ratio0 eta J eps rho0 T r)
          (Real.exp (-(innerBandScheduleAlpha (J - 1) * (r : ℝ) /
            ((2 * sliceA2OrdinaryN P0 ratio0 eta (J - 1)
              eps rho0 : ℕ) : ℝ)))) := by
  let Pl := sliceA2LadderPrimes P0 ratio0 eta
  let Nl := fun j => sliceA2OrdinaryN P0 ratio0 eta j eps rho0
  let v0l := fun j => sliceA2OrdinaryV0 P0 ratio0 eta j eps rho0
  let v1l := fun j => sliceA2OrdinaryV1 P0 ratio0 eta j eps rho0
  let Panchor := sliceA2OrdinaryAnchor P0 ratio0 eta J eps rho0
  let ell := sliceA2OrdinaryCoverMoment P0 ratio0 eta J eps rho0 T
  let G : Set ℝ := {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2}
  let K := bandCells K2
  have hbounds := sliceA2OrdinaryAnchor_cell_bounds P0 ratio0 eta J eps rho0
    hP0 hJ hanchor
  have hraw := card_cellsMeeting_exceptional_le_highMomentCost
    Pl Nl v0l v1l g hg innerBandScheduleAlpha J hJ G K Panchor ell
      (fun _ => 1)
    (fun p hp => sliceA2LadderPrimes_prime P0 ratio0 eta (J - 1) p hp)
    (fun r hr => by
      have h6 : 6 ≤ Panchor r := by
        simpa [Panchor] using hanchor r (by simpa [v0l, v1l] using hr)
      omega)
    (fun r hr p hp => (hbounds r (by simpa [v0l, v1l] using hr) p hp).1)
    (fun r hr p hp => (hbounds r (by simpa [v0l, v1l] using hr) p hp).2)
    (fun r hr => sliceA2OrdinaryCoverMoment_one_le
      P0 ratio0 eta J eps rho0 T r)
    (fun _ _ => by norm_num) T (by linarith)
    (fun k hk => bandCells_mem_Icc K2 T hTK2 k hk)
  have henvelope := sharpExceptionalCoverBound_le_envelopes
    Pl Nl v0l v1l innerBandScheduleAlpha J Panchor ell T
    (by linarith)
    (fun r hr => by
      have h6 : 6 ≤ Panchor r := by
        simpa [Panchor] using hanchor r (by simpa [v0l, v1l] using hr)
      omega)
    (fun r hr => adaptivePrimeMoment_time_term_le_one (Panchor r) T
      (by
        have h6 : 6 ≤ Panchor r := by
          simpa [Panchor] using hanchor r (by simpa [v0l, v1l] using hr)
        omega) hT)
    (by
      simpa [Pl, Nl, v0l, v1l, Panchor] using
        sliceA2Ordinary_cell_mass_le_one P0 ratio0 eta J eps rho0 hP0 hJ
          hanchor hlogAnchor)
  exact hraw.trans (by
    simpa [sliceA2ExceptionalCover, sharpExceptionalCoverBound, Pl, Nl,
      v0l, v1l, Panchor, ell, G, K] using henvelope)

end Tao2015

end MoltResearch
