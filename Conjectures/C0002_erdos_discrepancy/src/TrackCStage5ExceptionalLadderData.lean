import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5ExceptionalPrimeFit

/-!
# Track R L3-6: exceptional-level data

This file packages the finite and natural-division data for the remote prime
interval.  The lower endpoint is `exp((log A1)^(49/50))`, the interval ratio
is fixed after `epsc`, and the e-adic cell resolution remains a separate
parameter chosen large enough for the wide replacement leg.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-! ## The remote interval -/

/-- The remote lower endpoint.  `max 3` only makes the small-scale definition
total; it is inactive once the Phase-4 threshold is imposed. -/
noncomputable def exceptionalPrimeLower (A1 : ℕ) : ℕ :=
  max 3 ⌈Real.exp ((Real.log (A1 : ℝ)) ^ (49 / 50 : ℝ))⌉₊

/-- The fixed logarithmic length of the remote interval. -/
noncomputable def exceptionalIntervalRatio (epsc : ℝ) : ℕ :=
  max 3 ⌈Real.exp (4 / epsc + 13)⌉₊

noncomputable def exceptionalPrimeUpper (A1 : ℕ) (epsc : ℝ) : ℕ :=
  exceptionalPrimeLower A1 ^ exceptionalIntervalRatio epsc

noncomputable def exceptionalPrimes (A1 : ℕ) (epsc : ℝ) : Finset ℕ :=
  (Finset.Ioc (exceptionalPrimeLower A1)
    (exceptionalPrimeUpper A1 epsc)).filter Nat.Prime

theorem exceptionalPrimeLower_three_le (A1 : ℕ) :
    3 ≤ exceptionalPrimeLower A1 := by
  unfold exceptionalPrimeLower
  exact le_max_left _ _

theorem exceptionalIntervalRatio_three_le (epsc : ℝ) :
    3 ≤ exceptionalIntervalRatio epsc := by
  unfold exceptionalIntervalRatio
  exact le_max_left _ _

theorem exceptionalPrimeLower_le_upper (A1 : ℕ) (epsc : ℝ) :
    exceptionalPrimeLower A1 ≤ exceptionalPrimeUpper A1 epsc := by
  unfold exceptionalPrimeUpper
  exact Nat.le_pow (lt_of_lt_of_le (by norm_num)
    (exceptionalIntervalRatio_three_le epsc))

theorem exceptionalPrimes_prime
    (A1 : ℕ) (epsc : ℝ) (p : ℕ) (hp : p ∈ exceptionalPrimes A1 epsc) :
    p.Prime := (Finset.mem_filter.mp hp).2

theorem exceptionalPrimes_bounds
    (A1 : ℕ) (epsc : ℝ) (p : ℕ) (hp : p ∈ exceptionalPrimes A1 epsc) :
    exceptionalPrimeLower A1 < p ∧ p ≤ exceptionalPrimeUpper A1 epsc :=
  Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1

theorem exceptionalPrimes_card_le_upper (A1 : ℕ) (epsc : ℝ) :
    (exceptionalPrimes A1 epsc).card ≤ exceptionalPrimeUpper A1 epsc := by
  calc
    (exceptionalPrimes A1 epsc).card ≤
        (Finset.Ioc (exceptionalPrimeLower A1)
          (exceptionalPrimeUpper A1 epsc)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ exceptionalPrimeUpper A1 epsc := by
      rw [Nat.card_Ioc]
      omega

theorem exceptionalPrimes_mass_le_mertens (A1 : ℕ) (epsc : ℝ) :
    ∑ p ∈ exceptionalPrimes A1 epsc, (1 : ℝ) / p ≤
      Real.log (Real.log ((exceptionalPrimeUpper A1 epsc : ℝ) + 1)) -
        Real.log (Real.log ((exceptionalPrimeLower A1 : ℝ) + 1)) + 12 := by
  exact prime_Ioc_mass_upper_mertens
    (exceptionalPrimeLower A1) (exceptionalPrimeUpper A1 epsc)
    (exceptionalPrimeLower_three_le A1)
    (exceptionalPrimeLower_le_upper A1 epsc)

theorem exceptionalPrimes_sq_mass_le_card (A1 : ℕ) (epsc : ℝ) :
    ∑ p ∈ exceptionalPrimes A1 epsc, (1 : ℝ) / (p : ℝ) ^ 2 ≤
      ((exceptionalPrimes A1 epsc).card : ℝ) /
        (exceptionalPrimeLower A1 : ℝ) ^ 2 := by
  have hP0 : (0 : ℝ) < exceptionalPrimeLower A1 := by
    exact_mod_cast (show 0 < exceptionalPrimeLower A1 by
      have := exceptionalPrimeLower_three_le A1
      omega)
  have hterm : ∀ p ∈ exceptionalPrimes A1 epsc,
      (1 : ℝ) / (p : ℝ) ^ 2 ≤
        1 / (exceptionalPrimeLower A1 : ℝ) ^ 2 := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by
      exact_mod_cast (exceptionalPrimes_prime A1 epsc p hp).pos
    have hle : (exceptionalPrimeLower A1 : ℝ) ^ 2 ≤ (p : ℝ) ^ 2 := by
      have hb : (exceptionalPrimeLower A1 : ℝ) ≤ p := by
        exact_mod_cast (exceptionalPrimes_bounds A1 epsc p hp).1.le
      exact pow_le_pow_left₀ hP0.le hb 2
    exact one_div_le_one_div_of_le (sq_pos_of_pos hP0) hle
  calc
    ∑ p ∈ exceptionalPrimes A1 epsc, (1 : ℝ) / (p : ℝ) ^ 2 ≤
        ∑ _p ∈ exceptionalPrimes A1 epsc,
          1 / (exceptionalPrimeLower A1 : ℝ) ^ 2 :=
      Finset.sum_le_sum hterm
    _ = ((exceptionalPrimes A1 epsc).card : ℝ) /
        (exceptionalPrimeLower A1 : ℝ) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Every ordinary level below the remote lower endpoint is disjoint from the
exceptional interval. -/
theorem ordinaryLadderPrimes_disjoint_exceptional
    (P0 eta A1 : ℕ) (epsc : ℝ) (j : ℕ)
    (hsep : ordinaryLadderQ P0 eta j ≤ exceptionalPrimeLower A1) :
    Disjoint (ordinaryLadderPrimes P0 eta j) (exceptionalPrimes A1 epsc) :=
  ordinaryLadderPrimes_disjoint_interval P0 eta j
    (exceptionalPrimeLower A1) (exceptionalPrimeUpper A1 epsc) hsep

/-- A square bound on the upper endpoint is precisely the exceptional
`hPAu` hypothesis. -/
theorem exceptionalPrimes_square_le
    (A1 A : ℕ) (epsc : ℝ)
    (hQsq : exceptionalPrimeUpper A1 epsc ^ 2 ≤ A) :
    ∀ p ∈ exceptionalPrimes A1 epsc, p * p ≤ A := by
  intro p hp
  have hpQ := (exceptionalPrimes_bounds A1 epsc p hp).2
  calc
    p * p = p ^ 2 := by ring
    _ ≤ exceptionalPrimeUpper A1 epsc ^ 2 := by
      rw [pow_two, pow_two]
      exact Nat.mul_le_mul hpQ hpQ
    _ ≤ A := hQsq

/-! ## E-adic cells and representatives -/

noncomputable def exceptionalV0 (A1 Nu : ℕ) : ℕ :=
  eadicCoverIndexLower (2 * Nu) (exceptionalPrimeLower A1)

noncomputable def exceptionalV1 (A1 Nu : ℕ) (epsc : ℝ) : ℕ :=
  eadicCoverIndexUpper (2 * Nu) (exceptionalPrimeUpper A1 epsc)

noncomputable def exceptionalRepresentative
    (A1 Nu v : ℕ) (epsc : ℝ) : ℕ :=
  scaleCellRepresentative (exceptionalPrimes A1 epsc) Nu v

/-- All cover and representative hypotheses of the shifted wide capstone. -/
theorem exceptionalLevel_cell_data
    (A1 Nu : ℕ) (epsc : ℝ) (hNu : 0 < Nu) :
    ((Finset.Ico (exceptionalV0 A1 Nu)
        (exceptionalV1 A1 Nu epsc + 1)).biUnion
      (eadicCell (exceptionalPrimes A1 epsc) (2 * Nu)) =
        exceptionalPrimes A1 epsc) ∧
    (∀ v ∈ Finset.Ico (exceptionalV0 A1 Nu)
        (exceptionalV1 A1 Nu epsc + 1),
      (exceptionalRepresentative A1 Nu v epsc : ℝ) ≤
        Real.exp (((v : ℝ) + 1) / (2 * (Nu : ℝ)))) ∧
    (∀ v, 1 ≤ exceptionalRepresentative A1 Nu v epsc) ∧
    (∀ v ∈ Finset.Ico (exceptionalV0 A1 Nu)
        (exceptionalV1 A1 Nu epsc + 1),
      ∀ p ∈ eadicCell (exceptionalPrimes A1 epsc) (2 * Nu) v,
        exceptionalRepresentative A1 Nu v epsc ≤ p) ∧
    (∀ v ∈ Finset.Ico (exceptionalV0 A1 Nu)
        (exceptionalV1 A1 Nu epsc + 1),
      ∀ p ∈ eadicCell (exceptionalPrimes A1 epsc) (2 * Nu) v,
        Nu * p ≤ (Nu + 1) * exceptionalRepresentative A1 Nu v epsc) := by
  have hprime : ∀ p ∈ exceptionalPrimes A1 epsc, p.Prime :=
    fun p hp => exceptionalPrimes_prime A1 epsc p hp
  have hone : ∀ p ∈ exceptionalPrimes A1 epsc, 1 ≤ p :=
    fun p hp => (hprime p hp).one_le
  constructor
  · simpa [exceptionalV0, exceptionalV1] using
      eadicCell_biUnion_Ico_eq (exceptionalPrimes A1 epsc) (2 * Nu)
        (exceptionalPrimeLower A1) (exceptionalPrimeUpper A1 epsc)
        (by omega : 0 < 2 * Nu)
        (by
          have h3 := exceptionalPrimeLower_three_le A1
          omega)
        (fun p hp => (exceptionalPrimes_bounds A1 epsc p hp).1)
        (fun p hp => (exceptionalPrimes_bounds A1 epsc p hp).2)
  constructor
  · intro v hv
    exact qup_of_ceil_or_one (exceptionalPrimes A1 epsc) Nu v hNu hone
  constructor
  · intro v
    exact one_le_scaleCellRepresentative (exceptionalPrimes A1 epsc) Nu v
  constructor
  · intro v hv p hp
    exact scaleCellRepresentative_le_mem hNu hp
      (hprime p (mem_eadicCell.mp hp).1).one_le
  · intro v hv p hp
    exact scaleCellRepresentative_ratio_le hNu hp
      (hprime p (mem_eadicCell.mp hp).1).one_le

theorem exceptionalLevel_cell_card_le
    (A1 Nu : ℕ) (epsc : ℝ) (hNu : 0 < Nu) :
    ((Finset.Ico (exceptionalV0 A1 Nu)
        (exceptionalV1 A1 Nu epsc + 1)).card : ℝ) ≤
      2 * (Nu : ℝ) *
        (Real.log (exceptionalPrimeUpper A1 epsc) -
          Real.log (exceptionalPrimeLower A1)) + 2 := by
  simpa [exceptionalV0, exceptionalV1] using
    ordinaryLevel_cell_card_le (exceptionalPrimeLower A1)
      (exceptionalPrimeUpper A1 epsc) Nu
      (by
        have h3 := exceptionalPrimeLower_three_le A1
        omega)
      (exceptionalPrimeLower_le_upper A1 epsc) hNu

/-- With `L = log P_U`, the exceptional cell count has the fixed shape
`3*Nu*ratio*L`. -/
theorem exceptionalLevel_cell_card_fixed
    (A1 Nu : ℕ) (epsc : ℝ) (hNu : 0 < Nu)
    (hlog : 1 ≤ Real.log (exceptionalPrimeLower A1 : ℝ)) :
    ((Finset.Ico (exceptionalV0 A1 Nu)
        (exceptionalV1 A1 Nu epsc + 1)).card : ℝ) ≤
      3 * (Nu : ℝ) * (exceptionalIntervalRatio epsc : ℝ) *
        Real.log (exceptionalPrimeLower A1 : ℝ) := by
  have hraw := exceptionalLevel_cell_card_le A1 Nu epsc hNu
  have hratio : (1 : ℝ) ≤ exceptionalIntervalRatio epsc := by
    exact_mod_cast (show 1 ≤ exceptionalIntervalRatio epsc by
      have h3 := exceptionalIntervalRatio_three_le epsc
      omega)
  have hratio2 : (2 : ℝ) ≤ exceptionalIntervalRatio epsc := by
    exact_mod_cast (show 2 ≤ exceptionalIntervalRatio epsc by
      have h3 := exceptionalIntervalRatio_three_le epsc
      omega)
  have hNuR : (1 : ℝ) ≤ Nu := by exact_mod_cast hNu
  rw [exceptionalPrimeUpper, Nat.cast_pow, Real.log_pow] at hraw
  have hprod : (2 : ℝ) ≤ (Nu : ℝ) *
      (exceptionalIntervalRatio epsc : ℝ) *
        Real.log (exceptionalPrimeLower A1 : ℝ) := by
    calc
      (2 : ℝ) ≤ 1 * 2 * 1 := by norm_num
      _ ≤ (Nu : ℝ) * (exceptionalIntervalRatio epsc : ℝ) *
          Real.log (exceptionalPrimeLower A1 : ℝ) := by gcongr
  have hlog0 : 0 ≤ Real.log (exceptionalPrimeLower A1 : ℝ) := by linarith
  have hdrop : 0 ≤ 2 * (Nu : ℝ) *
      Real.log (exceptionalPrimeLower A1 : ℝ) := by positivity
  nlinarith

/-- The corrected representative never exceeds the remote upper endpoint,
including on empty cells where it is `1`. -/
theorem exceptionalRepresentative_le_upper
    (A1 Nu v : ℕ) (epsc : ℝ) (hNu : 0 < Nu) :
    exceptionalRepresentative A1 Nu v epsc ≤ exceptionalPrimeUpper A1 epsc := by
  classical
  unfold exceptionalRepresentative scaleCellRepresentative
  split_ifs with hcell
  · obtain ⟨p, hp⟩ := hcell
    have hprime := exceptionalPrimes_prime A1 epsc p (mem_eadicCell.mp hp).1
    exact (ceil_cell_lower_le hNu hp hprime.one_le).trans
      (exceptionalPrimes_bounds A1 epsc p (mem_eadicCell.mp hp).1).2
  · exact (by
      have hP := exceptionalPrimeLower_le_upper A1 epsc
      have h3 := exceptionalPrimeLower_three_le A1
      omega)

/-- `Q_U^2 ≤ A` supplies the quotient cutoff for every exceptional
representative. -/
theorem exceptionalRepresentative_two_mul_le
    (A1 A Nu v : ℕ) (epsc : ℝ) (hNu : 0 < Nu)
    (hQsq : exceptionalPrimeUpper A1 epsc ^ 2 ≤ A) :
    2 * exceptionalRepresentative A1 Nu v epsc ≤ A := by
  have hqQ := exceptionalRepresentative_le_upper A1 Nu v epsc hNu
  have hQ2 : 2 ≤ exceptionalPrimeUpper A1 epsc :=
    (by
      have hP := exceptionalPrimeLower_le_upper A1 epsc
      have h3 := exceptionalPrimeLower_three_le A1
      omega)
  calc
    2 * exceptionalRepresentative A1 Nu v epsc ≤
        2 * exceptionalPrimeUpper A1 epsc := Nat.mul_le_mul_left 2 hqQ
    _ ≤ exceptionalPrimeUpper A1 epsc ^ 2 := by
      rw [pow_two]
      nlinarith
    _ ≤ A := hQsq

theorem exceptionalRepresentative_quotient_one_le
    (A1 A Nu v : ℕ) (epsc : ℝ) (hNu : 0 < Nu)
    (hQsq : exceptionalPrimeUpper A1 epsc ^ 2 ≤ A) :
    1 ≤ A / exceptionalRepresentative A1 Nu v epsc := by
  have hq1 : 0 < exceptionalRepresentative A1 Nu v epsc :=
    lt_of_lt_of_le (by norm_num)
      (one_le_scaleCellRepresentative (exceptionalPrimes A1 epsc) Nu v)
  apply (Nat.one_le_div_iff hq1).mpr
  have htwo := exceptionalRepresentative_two_mul_le A1 A Nu v epsc hNu hQsq
  omega

/-! ## Brun anchors and adaptive moments -/

noncomputable def exceptionalCellAnchor (Nu v : ℕ) : ℕ :=
  eadicCellLowerAnchor Nu v

/-- Once the remote-cell anchors clear the harmless rounding threshold, they
supply `hPcU`, `hloU`, and `hhiU` simultaneously. -/
theorem exceptionalCellAnchor_data
    (A1 Nu : ℕ) (epsc : ℝ) (hNu : 2 ≤ Nu)
    (hanchor : ∀ v ∈ Finset.Ico (exceptionalV0 A1 Nu)
      (exceptionalV1 A1 Nu epsc + 1), 6 ≤ exceptionalCellAnchor Nu v) :
    (∀ v ∈ Finset.Ico (exceptionalV0 A1 Nu)
      (exceptionalV1 A1 Nu epsc + 1), 2 ≤ exceptionalCellAnchor Nu v) ∧
    (∀ v ∈ Finset.Ico (exceptionalV0 A1 Nu)
      (exceptionalV1 A1 Nu epsc + 1),
      ∀ p ∈ eadicCell (exceptionalPrimes A1 epsc) (2 * Nu) v,
        exceptionalCellAnchor Nu v < p) ∧
    (∀ v ∈ Finset.Ico (exceptionalV0 A1 Nu)
      (exceptionalV1 A1 Nu epsc + 1),
      ∀ p ∈ eadicCell (exceptionalPrimes A1 epsc) (2 * Nu) v,
        p ≤ 2 * exceptionalCellAnchor Nu v) := by
  have hprime : ∀ p ∈ exceptionalPrimes A1 epsc, p.Prime :=
    fun p hp => exceptionalPrimes_prime A1 epsc p hp
  refine ⟨fun v hv => (by
      have h6 := hanchor v hv
      omega), ?_, ?_⟩
  · intro v hv p hp
    exact (eadicCell_mem_lowerAnchor_dyadic
      (exceptionalPrimes A1 epsc) hprime Nu v hNu (hanchor v hv) p hp).1
  · intro v hv p hp
    exact (eadicCell_mem_lowerAnchor_dyadic
      (exceptionalPrimes A1 epsc) hprime Nu v hNu (hanchor v hv) p hp).2

noncomputable def exceptionalCellMoment (Nu v : ℕ) (T : ℝ) : ℕ :=
  adaptivePrimeMoment (exceptionalCellAnchor Nu v) T

theorem exceptionalCellMoment_one_le (Nu v : ℕ) (T : ℝ) :
    1 ≤ exceptionalCellMoment Nu v T :=
  adaptivePrimeMoment_one_le (exceptionalCellAnchor Nu v) T

theorem exceptionalCellMoment_time_term_le_one
    (Nu v : ℕ) (T : ℝ) (hanchor : 2 ≤ exceptionalCellAnchor Nu v)
    (hT : 1 ≤ T) :
    (T + 1) /
        (((exceptionalCellAnchor Nu v) ^ exceptionalCellMoment Nu v T : ℕ) : ℝ) ≤ 1 := by
  exact adaptivePrimeMoment_time_term_le_one
    (exceptionalCellAnchor Nu v) T hanchor hT

/-- Fine-cell Brun--Titchmarsh for the chosen exceptional anchors. -/
theorem exceptionalCell_card_le_brun
    (A1 Nu v : ℕ) (epsc : ℝ) (hNu : 0 < Nu)
    (hscale : 4 * Nu ^ 2 ≤ exceptionalCellAnchor Nu v) :
    ((eadicCell (exceptionalPrimes A1 epsc) (2 * Nu) v).card : ℝ) ≤
      1024 * (exceptionalCellAnchor Nu v : ℝ) /
        ((Nu : ℝ) * Real.log (exceptionalCellAnchor Nu v)) := by
  exact card_eadicCell_le_brun (exceptionalPrimes A1 epsc)
    (fun p hp => exceptionalPrimes_prime A1 epsc p hp) Nu v hNu hscale

/-! ## Natural-division collars -/

/-- If the cell resolution times the prime lies below the window endpoint,
the replacement collar has at least one step. -/
theorem collar_division_fit_of_mul_le
    (X Nu p : ℕ) (hNu : 2 ≤ Nu) (hp : 0 < p) (hfit : Nu * p ≤ X) :
    X / (Nu * p) + 1 ≤ X / p := by
  have hNu0 : 0 < Nu := by omega
  have hx : Nu ≤ X / p := (Nat.le_div_iff_mul_le hp).mpr hfit
  have hx2 : 2 ≤ X / p := hNu.trans hx
  have hdiv : (X / p) / Nu ≤ (X / p) / 2 :=
    Nat.div_le_div_left hNu (by omega)
  calc
    X / (Nu * p) + 1 = X / (p * Nu) + 1 := by rw [Nat.mul_comm Nu p]
    _ = (X / p) / Nu + 1 := by rw [Nat.div_div_eq_div_mul]
    _ ≤ (X / p) / 2 + 1 := by omega
    _ ≤ X / p := by omega

/-- The single guard `Nu*Q ≤ A` supplies both exceptional collar families. -/
theorem exceptionalLevel_collar_data
    (A1 A Delta Nu : ℕ) (epsc : ℝ) (hNu : 2 ≤ Nu)
    (hNuQ : Nu * exceptionalPrimeUpper A1 epsc ≤ A) :
    (∀ v ∈ Finset.Ico (exceptionalV0 A1 Nu)
        (exceptionalV1 A1 Nu epsc + 1),
      ∀ p ∈ eadicCell (exceptionalPrimes A1 epsc) (2 * Nu) v,
        A / (Nu * p) + 1 ≤ A / p) ∧
    (∀ v ∈ Finset.Ico (exceptionalV0 A1 Nu)
        (exceptionalV1 A1 Nu epsc + 1),
      ∀ p ∈ eadicCell (exceptionalPrimes A1 epsc) (2 * Nu) v,
        (A + Delta) / (Nu * p) + 1 ≤ (A + Delta) / p) := by
  constructor <;> intro v hv p hp
  · apply collar_division_fit_of_mul_le A Nu p hNu
      (exceptionalPrimes_prime A1 epsc p (mem_eadicCell.mp hp).1).pos
    exact (Nat.mul_le_mul_left Nu
      (exceptionalPrimes_bounds A1 epsc p (mem_eadicCell.mp hp).1).2).trans hNuQ
  · apply collar_division_fit_of_mul_le (A + Delta) Nu p hNu
      (exceptionalPrimes_prime A1 epsc p (mem_eadicCell.mp hp).1).pos
    exact (Nat.mul_le_mul_left Nu
      (exceptionalPrimes_bounds A1 epsc p (mem_eadicCell.mp hp).1).2).trans
      (hNuQ.trans (Nat.le_add_right A Delta))

/-! ## The combined wide-error leg -/

/-- The exact wide error in `hfitU`, bounded after `T/A ≤ 1`. -/
theorem exceptionalWideCost_le
    (A Nu : ℕ) (P : Finset ℕ) (T E E2 : ℝ)
    (hA : 0 < A) (hNu : 0 < Nu) (hTA : T ≤ A)
    (hmass : ∑ p ∈ P, (1 : ℝ) / p ≤ E)
    (hmass2 : ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2 ≤ E2) :
    2 * (2 * replacementEnergyBoundWide A P Nu T +
        2 * (4 * collisionEnergyBoundWide A P T)) ≤
      1152 * Real.exp Real.pi *
          (E / (Nu : ℝ) + (P.card : ℝ) / A) +
        80 * Real.exp Real.pi *
          (2 * E2 + (P.card : ℝ) / A) := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hratio : T / (A : ℝ) ≤ 1 :=
    (div_le_one hA0).2 (by exact_mod_cast hTA)
  have hrepl0 : 0 ≤
      (∑ p ∈ P, (1 : ℝ) / p) / (Nu : ℝ) + (P.card : ℝ) / A := by
    positivity
  have hcoll0 : 0 ≤
      2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) +
        (P.card : ℝ) / A := by positivity
  have hrepl : 4 * replacementEnergyBoundWide A P Nu T ≤
      1152 * Real.exp Real.pi *
        (E / (Nu : ℝ) + (P.card : ℝ) / A) := by
    unfold replacementEnergyBoundWide
    calc
      4 * (Real.exp Real.pi * (T / (A : ℝ) + 8) *
          (32 * ((∑ p ∈ P, (1 : ℝ) / p) / (Nu : ℝ) +
            (P.card : ℝ) / A))) =
        128 * Real.exp Real.pi * (T / (A : ℝ) + 8) *
          ((∑ p ∈ P, (1 : ℝ) / p) / (Nu : ℝ) +
            (P.card : ℝ) / A) := by ring
      _ ≤ 128 * Real.exp Real.pi * 9 *
          ((∑ p ∈ P, (1 : ℝ) / p) / (Nu : ℝ) +
            (P.card : ℝ) / A) := by gcongr; linarith
      _ = 1152 * Real.exp Real.pi *
          ((∑ p ∈ P, (1 : ℝ) / p) / (Nu : ℝ) +
            (P.card : ℝ) / A) := by ring
      _ ≤ 1152 * Real.exp Real.pi *
          (E / (Nu : ℝ) + (P.card : ℝ) / A) := by gcongr
  have hcoll : 16 * collisionEnergyBoundWide A P T ≤
      80 * Real.exp Real.pi *
        (2 * E2 + (P.card : ℝ) / A) := by
    unfold collisionEnergyBoundWide
    have hfactor : Real.exp Real.pi * (T / (A : ℝ) + 4) ≤
        Real.exp Real.pi * 5 := by
      exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg _)
    calc
      16 * (Real.exp Real.pi * (T / (A : ℝ) + 4) *
          (2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) +
            (P.card : ℝ) / A)) ≤
        16 * Real.exp Real.pi * 5 *
          (2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) +
            (P.card : ℝ) / A) := by
        calc
          _ ≤ 16 * (Real.exp Real.pi * 5 *
              (2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) +
                (P.card : ℝ) / A)) := by
            gcongr
          _ = _ := by ring
      _ = 80 * Real.exp Real.pi *
          (2 * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) +
            (P.card : ℝ) / A) := by ring
      _ ≤ 80 * Real.exp Real.pi *
          (2 * E2 + (P.card : ℝ) / A) := by gcongr
  convert add_le_add hrepl hcoll using 1 <;> ring

/-- A capstone-ready sufficient condition allocating `c3*eps^2/96` to the
combined wide exceptional error. -/
theorem exceptionalWideCost_fit
    (A Nu : ℕ) (P : Finset ℕ) (T E E2 c3 eps : ℝ)
    (hA : 0 < A) (hNu : 0 < Nu) (hTA : T ≤ A)
    (hmass : ∑ p ∈ P, (1 : ℝ) / p ≤ E)
    (hmass2 : ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2 ≤ E2)
    (hfit : 1152 * Real.exp Real.pi *
          (E / (Nu : ℝ) + (P.card : ℝ) / A) +
        80 * Real.exp Real.pi *
          (2 * E2 + (P.card : ℝ) / A) ≤ c3 * eps ^ 2 / 96) :
    2 * (2 * replacementEnergyBoundWide A P Nu T +
        2 * (4 * collisionEnergyBoundWide A P T)) ≤ c3 * eps ^ 2 / 96 :=
  (exceptionalWideCost_le A Nu P T E E2 hA hNu hTA hmass hmass2).trans hfit

/-! ## Sharp cutoff and delta -/

noncomputable def exceptionalSharpCutoff (A : ℕ) : ℕ :=
  ⌈Real.sqrt (3 * (2 * (A : ℝ) + 1))⌉₊

theorem exceptionalSharpCutoff_real_lower (A : ℕ) :
    Real.sqrt (3 * (2 * (A : ℝ) + 1)) ≤ exceptionalSharpCutoff A := by
  exact Nat.le_ceil _

noncomputable def exceptionalDelta0 (epsPrime : ℝ) : ℝ :=
  epsPrime / (8 * Real.exp 1)

theorem exceptionalDelta0_pos (epsPrime : ℝ) (hepsPrime : 0 < epsPrime) :
    0 < exceptionalDelta0 epsPrime := by
  unfold exceptionalDelta0
  positivity

theorem exceptionalDelta0_le_one
    (epsPrime : ℝ) (hepsPrime : epsPrime ≤ 8 * Real.exp 1) :
    exceptionalDelta0 epsPrime ≤ 1 := by
  unfold exceptionalDelta0
  rw [div_le_one (by positivity)]
  exact hepsPrime

/-- A convenient algebraic margin for the capstone's sharp strength. -/
theorem exceptional_strengthSharp_of_margin
    (A0 D logLoss : ℝ)
    (hmargin : 6 * D + 6 * logLoss ≤ A0) :
    2 * D ≤ A0 / 3 - 2 * logLoss := by
  linarith

/-- A convenient algebraic margin for the capstone's sharp frequency range. -/
theorem exceptional_rangeSharp_of_margin
    (A0 T M N : ℝ)
    (hmargin : 6 * Real.pi * (T + M + 1) ≤ A0 * N) :
    2 * Real.pi * T + 2 * Real.pi * (M + 1) ≤ (A0 / 3) * N := by
  nlinarith

end Tao2015

end MoltResearch
