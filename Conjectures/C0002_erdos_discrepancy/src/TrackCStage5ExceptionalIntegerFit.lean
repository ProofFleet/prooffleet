import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5LadderCutoff

/-!
# Track R L3-4: exceptional integer-part fit

The raw cover cardinality is first bounded at the last ordinary anchors by a
closed high-moment envelope.  Separately, the `n^-2` coefficient mass turns
the exceptional integer part into a scale-free expression.  After the outer
Cauchy factor, its exact cost is at most

`1024 * #cells^2 * V0^2 * L * (1 + Kcov*sqrt(T)*Q/A)`.

Thus `V0 = (log A)^-100` leaves the full `(log A)^-200` saving advertised in
the Phase-4 calculation.
-/

namespace MoltResearch

namespace Tao2015

/-- Closed upper envelope for one ordinary anchor in the exceptional cover. -/
noncomputable def ordinaryCoverMomentEnvelope
    (P ell : ℕ) (V : ℝ) : ℝ :=
  (Real.exp Real.pi *
      (1 + 2 * ((2 ^ ell : ℕ) : ℝ)) *
      (Nat.factorial ell : ℝ) ^ 2 *
      (2 + (2 * Real.pi * Real.log ((2 * P : ℕ) ^ ell)) ^ 2)) /
    V ^ (2 * ell)

/-- If the adaptive moment pays the time quotient and the dyadic cell mass
is at most one, its high-moment count is bounded by the closed envelope. -/
theorem primeHighMomentCountCost_le_coverEnvelope
    (P ell : ℕ) (Y : Finset ℕ) (T V : ℝ)
    (hP : 1 ≤ P) (hT : 0 ≤ T) (hV : 0 < V)
    (htime : (T + 1) / ((P ^ ell : ℕ) : ℝ) ≤ 1)
    (hmass0 : 0 ≤ ∑ p ∈ Y, (1 : ℝ) / p)
    (hmass : ∑ p ∈ Y, (1 : ℝ) / p ≤ 1) :
    primeHighMomentCountCost P ell Y T V 1 ≤
      ordinaryCoverMomentEnvelope P ell V := by
  have htimeTerm0 : 0 ≤ (T + 1) / ((P ^ ell : ℕ) : ℝ) := by
    positivity
  have hmassPow : (∑ p ∈ Y, (1 : ℝ) / p) ^ ell ≤ 1 :=
    pow_le_one₀ hmass0 hmass
  unfold primeHighMomentCountCost ordinaryCoverMomentEnvelope
  norm_num only [one_div, inv_one, one_mul]
  norm_num only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
  have htime' : (T + 1) / (P : ℝ) ^ ell ≤ 1 := by
    simpa only [Nat.cast_pow] using htime
  have hden : 0 < V ^ (2 * ell) := pow_pos hV _
  apply (div_le_div_iff_of_pos_right hden).2
  have hfacmass :
      (Nat.factorial ell : ℝ) ^ 2 *
          (∑ p ∈ Y, (p : ℝ)⁻¹) ^ ell ≤
        (Nat.factorial ell : ℝ) ^ 2 := by
    have htmp := mul_le_mul_of_nonneg_left hmassPow
      (sq_nonneg (Nat.factorial ell : ℝ))
    simpa only [one_div, mul_one] using htmp
  have hlogfactor : 0 ≤
      2 + (2 * Real.pi * Real.log ((2 * (P : ℝ)) ^ ell)) ^ 2 := by positivity
  calc
    Real.exp Real.pi *
          ((T + 1) / (P : ℝ) ^ ell + 2 * (2 : ℝ) ^ ell) *
          ((Nat.factorial ell : ℝ) ^ 2 *
            (∑ p ∈ Y, (p : ℝ)⁻¹) ^ ell) *
          (2 + (2 * Real.pi * Real.log ((2 * (P : ℝ)) ^ ell)) ^ 2) ≤
      Real.exp Real.pi *
          (1 + 2 * (2 : ℝ) ^ ell) *
          ((Nat.factorial ell : ℝ) ^ 2 *
            (∑ p ∈ Y, (p : ℝ)⁻¹) ^ ell) *
          (2 + (2 * Real.pi * Real.log ((2 * (P : ℝ)) ^ ell)) ^ 2) := by
        gcongr
    _ ≤ Real.exp Real.pi * (1 + 2 * (2 : ℝ) ^ ell) *
          (Nat.factorial ell : ℝ) ^ 2 *
          (2 + (2 * Real.pi * Real.log ((2 * (P : ℝ)) ^ ell)) ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ hlogfactor
      apply mul_le_mul_of_nonneg_left hfacmass
      positivity

/-- The last ordinary cover is bounded by the sum of the closed envelopes. -/
theorem sharpExceptionalCoverBound_le_envelopes
    (P : ℕ → Finset ℕ) (N v0 v1 : ℕ → ℕ) (alpha : ℕ → ℝ)
    (J : ℕ) (Panchor coverEll : ℕ → ℕ) (T : ℝ)
    (hT : 0 ≤ T)
    (hPanchor : ∀ r ∈ Finset.Ico (v0 (J - 1)) (v1 (J - 1) + 1),
      1 ≤ Panchor r)
    (htime : ∀ r ∈ Finset.Ico (v0 (J - 1)) (v1 (J - 1) + 1),
      (T + 1) / ((Panchor r ^ coverEll r : ℕ) : ℝ) ≤ 1)
    (hmass : ∀ r ∈ Finset.Ico (v0 (J - 1)) (v1 (J - 1) + 1),
      ∑ p ∈ eadicCell (P (J - 1)) (2 * N (J - 1)) r,
        (1 : ℝ) / p ≤ 1) :
    sharpExceptionalCoverBound P N v0 v1 alpha J Panchor coverEll T
        (fun _ => 1) ≤
      ∑ r ∈ Finset.Ico (v0 (J - 1)) (v1 (J - 1) + 1),
        2 * ordinaryCoverMomentEnvelope (Panchor r) (coverEll r)
          (Real.exp (-(alpha (J - 1) * (r : ℝ) /
            ((2 * N (J - 1) : ℕ) : ℝ)))) := by
  unfold sharpExceptionalCoverBound
  apply Finset.sum_le_sum
  intro r hr
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply primeHighMomentCountCost_le_coverEnvelope
  · exact hPanchor r hr
  · exact hT
  · positivity
  · exact htime r hr
  · exact Finset.sum_nonneg fun p _ => by positivity
  · exact hmass r hr

/-- The integer-dependent part of one exceptional cell cost. -/
noncomputable def exceptionalIntegerCellCost
    (V0 Bq Kcov T L coeffMass : ℝ) : ℝ :=
  2 * (V0 ^ 2 *
    (64 * (Bq + Kcov * Real.sqrt T) * L * coeffMass))

/-- The exceptional split contributes exactly two hundred powers of the
ambient logarithm after squaring. -/
theorem exceptionalSplitThreshold_sq (A : ℕ) :
    exceptionalSplitThreshold A ^ 2 =
      1 / Real.log (A : ℝ) ^ 200 := by
  unfold exceptionalSplitThreshold
  rw [div_pow]
  norm_num
  rw [← pow_mul]

/-- The quotient rounding estimate needed to cancel the coefficient tail. -/
theorem one_div_quotient_add_one_le
    (A q Q : ℕ) (hq : 1 ≤ q) (h2qA : 2 * q ≤ A) (hqQ : q ≤ Q) :
    1 / (((A / q + 1 : ℕ) : ℝ)) ≤ 2 * (Q : ℝ) / (A : ℝ) := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hbase := time_div_quotient_le_two_mul_scale A q Q 1 hq hqQ h2qA
    (by norm_num)
  have hAq : 1 ≤ A / q := (Nat.one_le_div_iff (by omega : 0 < q)).mpr (by omega)
  have hden : (0 : ℝ) < ((A / q : ℕ) : ℝ) := by exact_mod_cast hAq
  have hadd : ((A / q : ℕ) : ℝ) ≤ ((A / q + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ (A / q)
  calc
    1 / (((A / q + 1 : ℕ) : ℝ)) ≤ 1 / ((A / q : ℕ) : ℝ) := by
      exact one_div_le_one_div_of_le hden hadd
    _ ≤ 2 * 1 * (Q : ℝ) / (A : ℝ) := by simpa using hbase
    _ = 2 * (Q : ℝ) / (A : ℝ) := by ring

/-- After summing the coefficient-tail bound and paying the outer Cauchy
factor, the whole `V0` leg has the displayed fixed envelope. -/
theorem exceptionalIntegerAggregate_le
    (I : Finset ℕ) (A Q : ℕ) (q : ℕ → ℕ)
    (Bq coeffMass : ℕ → ℝ) (V0 Kcov T L : ℝ)
    (hA : 0 < A) (hK : 0 ≤ Kcov) (hL : 0 ≤ L)
    (hq : ∀ v ∈ I, 1 ≤ q v)
    (hqQ : ∀ v ∈ I, q v ≤ Q)
    (h2qA : ∀ v ∈ I, 2 * q v ≤ A)
    (hBq : ∀ v ∈ I, Bq v ≤ 2 * ((A / q v + 1 : ℕ) : ℝ))
    (hcoeff0 : ∀ v ∈ I, 0 ≤ coeffMass v)
    (hcoeff : ∀ v ∈ I,
      coeffMass v ≤ 2 / (((A / q v + 1 : ℕ) : ℝ))) :
    2 * (I.card : ℝ) *
        (∑ v ∈ I,
          exceptionalIntegerCellCost V0 (Bq v) Kcov T L (coeffMass v)) ≤
      1024 * (I.card : ℝ) ^ 2 * V0 ^ 2 * L *
        (1 + Kcov * Real.sqrt T * (Q : ℝ) / (A : ℝ)) := by
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hpoint : ∀ v ∈ I,
      exceptionalIntegerCellCost V0 (Bq v) Kcov T L (coeffMass v) ≤
        512 * V0 ^ 2 * L *
          (1 + Kcov * Real.sqrt T * (Q : ℝ) / (A : ℝ)) := by
    intro v hv
    have htail := one_div_quotient_add_one_le A (q v) Q
      (hq v hv) (h2qA v hv) (hqQ v hv)
    have hden : (0 : ℝ) < ((A / q v + 1 : ℕ) : ℝ) := by positivity
    have hBpart : Bq v * coeffMass v ≤ 4 := by
      calc
        Bq v * coeffMass v ≤
            (2 * ((A / q v + 1 : ℕ) : ℝ)) *
              (2 / (((A / q v + 1 : ℕ) : ℝ))) := by
                exact mul_le_mul (hBq v hv) (hcoeff v hv)
                  (hcoeff0 v hv) (by positivity)
        _ = 4 := by field_simp; norm_num
    have hKpart :
        (Kcov * Real.sqrt T) * coeffMass v ≤
          4 * Kcov * Real.sqrt T * (Q : ℝ) / (A : ℝ) := by
      calc
        (Kcov * Real.sqrt T) * coeffMass v ≤
            (Kcov * Real.sqrt T) *
              (2 / (((A / q v + 1 : ℕ) : ℝ))) := by
                exact mul_le_mul_of_nonneg_left (hcoeff v hv) (by positivity)
        _ ≤ (Kcov * Real.sqrt T) * (4 * (Q : ℝ) / (A : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc
            2 / (((A / q v + 1 : ℕ) : ℝ)) =
                2 * (1 / (((A / q v + 1 : ℕ) : ℝ))) := by ring
            _ ≤ 2 * (2 * (Q : ℝ) / (A : ℝ)) :=
              mul_le_mul_of_nonneg_left htail (by norm_num)
            _ = 4 * (Q : ℝ) / (A : ℝ) := by ring
        _ = 4 * Kcov * Real.sqrt T * (Q : ℝ) / (A : ℝ) := by ring
    unfold exceptionalIntegerCellCost
    have hbase :
        (Bq v + Kcov * Real.sqrt T) * coeffMass v ≤
          4 * (1 + Kcov * Real.sqrt T * (Q : ℝ) / (A : ℝ)) := by
      calc
        (Bq v + Kcov * Real.sqrt T) * coeffMass v =
            Bq v * coeffMass v +
              (Kcov * Real.sqrt T) * coeffMass v := by ring
        _ ≤ 4 + 4 * Kcov * Real.sqrt T * (Q : ℝ) / (A : ℝ) :=
          add_le_add hBpart hKpart
        _ = 4 * (1 + Kcov * Real.sqrt T * (Q : ℝ) / (A : ℝ)) := by ring
    calc
      2 * (V0 ^ 2 * (64 * (Bq v + Kcov * Real.sqrt T) * L * coeffMass v)) =
          128 * V0 ^ 2 * L *
            ((Bq v + Kcov * Real.sqrt T) * coeffMass v) := by ring
      _ ≤ 128 * V0 ^ 2 * L *
          (4 * (1 + Kcov * Real.sqrt T * (Q : ℝ) / (A : ℝ))) := by gcongr
      _ = 512 * V0 ^ 2 * L *
          (1 + Kcov * Real.sqrt T * (Q : ℝ) / (A : ℝ)) := by ring
  have hsum :
      (∑ v ∈ I, exceptionalIntegerCellCost V0 (Bq v) Kcov T L (coeffMass v)) ≤
        (I.card : ℝ) *
          (512 * V0 ^ 2 * L *
            (1 + Kcov * Real.sqrt T * (Q : ℝ) / (A : ℝ))) := by
    calc
      (∑ v ∈ I, exceptionalIntegerCellCost V0 (Bq v) Kcov T L (coeffMass v)) ≤
          ∑ _v ∈ I, 512 * V0 ^ 2 * L *
            (1 + Kcov * Real.sqrt T * (Q : ℝ) / (A : ℝ)) := by
              exact Finset.sum_le_sum fun v hv => hpoint v hv
      _ = (I.card : ℝ) *
          (512 * V0 ^ 2 * L *
            (1 + Kcov * Real.sqrt T * (Q : ℝ) / (A : ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  calc
    2 * (I.card : ℝ) *
        (∑ v ∈ I, exceptionalIntegerCellCost V0 (Bq v) Kcov T L (coeffMass v)) ≤
      2 * (I.card : ℝ) * ((I.card : ℝ) *
        (512 * V0 ^ 2 * L *
          (1 + Kcov * Real.sqrt T * (Q : ℝ) / (A : ℝ)))) := by gcongr
    _ = 1024 * (I.card : ℝ) ^ 2 * V0 ^ 2 * L *
        (1 + Kcov * Real.sqrt T * (Q : ℝ) / (A : ℝ)) := by ring

end Tao2015

end MoltResearch
