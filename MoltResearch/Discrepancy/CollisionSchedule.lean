import MoltResearch.Discrepancy.LevelLegs
import MoltResearch.Discrepancy.LevelOneSchedule

/-!
# The collision leg in schedule form (Track R, A2-III, VI-8d)

`collisionEnergyBound` has the corrected cubic prime weight: one harmonic
weight from the outer Cauchy--Schwarz inequality and two more powers from
extracting `p²`.  This file bounds its quotient harmonic mass and quotient
scale, leaving the closed schedule envelope

`E²/P² · e^π · (2TQ²/A + 8) · log(2R)`.

Here `E` bounds the harmonic prime mass of the level, `P` and `Q` are its
prime endpoints, and `B ≤ R A`.  The factor `2` and `log(2R)` are the honest
natural-division losses.
-/

namespace MoltResearch

/-- A quotient scale loses at most a factor two to natural-number division. -/
theorem quotient_scale_le_of_le (A q : ℕ) (T Q : ℝ) (hq : 1 ≤ q)
    (hqA : q ≤ A) (hT : 0 ≤ T) (hQ : (q : ℝ) ≤ Q) :
    T / ((A / q : ℕ) : ℝ) ≤ 2 * T * Q / (A : ℝ) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hqA)
  have ha : 1 ≤ A / q := (Nat.one_le_div_iff (by omega : 0 < q)).mpr hqA
  have ha0 : (0 : ℝ) < ((A / q : ℕ) : ℝ) := by exact_mod_cast ha
  have hdm : (q : ℝ) * ((A / q : ℕ) : ℝ) + ((A % q : ℕ) : ℝ) = (A : ℝ) := by
    exact_mod_cast Nat.div_add_mod A q
  have hmod : ((A % q : ℕ) : ℝ) < (q : ℝ) := by
    exact_mod_cast Nat.mod_lt A (by omega : 0 < q)
  have hfloor : (A : ℝ) / (2 * (q : ℝ)) ≤ ((A / q : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have hqd : (q : ℝ) ≤ (q : ℝ) * ((A / q : ℕ) : ℝ) := by
      calc
        (q : ℝ) = (q : ℝ) * 1 := by ring
        _ ≤ (q : ℝ) * ((A / q : ℕ) : ℝ) := by
          gcongr
          exact_mod_cast ha
    nlinarith [hdm, hmod, hqd]
  calc
    T / ((A / q : ℕ) : ℝ) ≤ T / ((A : ℝ) / (2 * (q : ℝ))) := by
      gcongr
    _ = 2 * T * (q : ℝ) / (A : ℝ) := by field_simp
    _ ≤ 2 * T * Q / (A : ℝ) := by gcongr

/-- The collision quotient support has harmonic mass at most `log(2R)`. -/
theorem collisionQuotSupport_harmonic_le (A B R : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ)) (p : ℕ) (hp : p.Prime) (hppA : p * p ≤ A)
    (hR : 1 ≤ R) (hB : B ≤ R * A) :
    ∑ k ∈ collisionQuotSupport (typicalS A B rest) p, (1 : ℝ) / (k : ℝ)
      ≤ Real.log (2 * (R : ℝ)) := by
  have hsub := collisionQuotSupport_subset A B (typicalS A B rest)
    (typicalS_subset_Ioc A B rest) hp.pos
  have hmono :
      ∑ k ∈ collisionQuotSupport (typicalS A B rest) p, (1 : ℝ) / (k : ℝ)
        ≤ ∑ k ∈ Finset.Ioc (A / (p * p)) (B / (p * p)),
            (1 : ℝ) / (k : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
  exact hmono.trans (quotient_harmonic_le_log_two_mul A B (p * p) R
    (by have hpp0 : 0 < p * p := Nat.mul_pos hp.pos hp.pos; omega) hppA hR hB)

/-- Prime cubic mass is bounded by harmonic mass divided by the square of the
lower endpoint. -/
theorem sum_one_div_cube_le_mass_div_sq (P : Finset ℕ) (Plo E : ℝ)
    (hPlo : 0 < Plo) (hlo : ∀ p ∈ P, Plo ≤ (p : ℝ))
    (hmass : ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ≤ E) :
    ∑ p ∈ P, ((1 : ℝ) / (p : ℝ)) ^ 3 ≤ E / Plo ^ 2 := by
  have hterm : ∀ p ∈ P,
      ((1 : ℝ) / (p : ℝ)) ^ 3
        ≤ ((1 : ℝ) / (p : ℝ)) * (1 / Plo ^ 2) := by
    intro p hp
    have hp0 : 0 < (p : ℝ) := lt_of_lt_of_le hPlo (hlo p hp)
    have hsq : Plo ^ 2 ≤ (p : ℝ) ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self hPlo.le (hlo p hp)
    have hinv : 1 / (p : ℝ) ^ 2 ≤ 1 / Plo ^ 2 :=
      one_div_le_one_div_of_le (by positivity) hsq
    calc
      ((1 : ℝ) / (p : ℝ)) ^ 3
          = ((1 : ℝ) / (p : ℝ)) * (1 / (p : ℝ) ^ 2) := by ring
      _ ≤ ((1 : ℝ) / (p : ℝ)) * (1 / Plo ^ 2) := by gcongr
  calc
    ∑ p ∈ P, ((1 : ℝ) / (p : ℝ)) ^ 3
        ≤ ∑ p ∈ P, ((1 : ℝ) / (p : ℝ)) * (1 / Plo ^ 2) :=
      Finset.sum_le_sum hterm
    _ = (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) / Plo ^ 2 := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ E / Plo ^ 2 := by gcongr

/-- The literal `collisionEnergyBound`, bounded only by schedule parameters. -/
theorem collisionEnergyBound_le_schedule (A B R : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ)) (T Plo Q E : ℝ)
    (hA : 0 < A) (hR : 1 ≤ R) (hB : B ≤ R * A) (hT : 0 ≤ T)
    (hPlo : 0 < Plo) (hQ : 0 ≤ Q)
    (hprime : ∀ p ∈ P, p.Prime) (hppA : ∀ p ∈ P, p * p ≤ A)
    (hlo : ∀ p ∈ P, Plo ≤ (p : ℝ)) (hhi : ∀ p ∈ P, (p : ℝ) ≤ Q)
    (hmass : ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ≤ E) :
    collisionEnergyBound A B P rest T
      ≤ E * ((E / Plo ^ 2) *
        (Real.exp Real.pi * (2 * T * Q ^ 2 / (A : ℝ) + 8)
          * Real.log (2 * (R : ℝ)))) := by
  let X := Real.exp Real.pi * (2 * T * Q ^ 2 / (A : ℝ) + 8)
    * Real.log (2 * (R : ℝ))
  have hlogR : 0 ≤ Real.log (2 * (R : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * R))
  have hX0 : 0 ≤ X := by
    dsimp [X]
    positivity
  have hE0 : 0 ≤ E := le_trans
    (Finset.sum_nonneg fun p _ => by positivity) hmass
  have hcubic := sum_one_div_cube_le_mass_div_sq P Plo E hPlo hlo hmass
  have hcost : ∀ p ∈ P,
      Real.exp Real.pi * (T / ((A / (p * p) : ℕ) : ℝ) + 8)
          * ∑ k ∈ collisionQuotSupport (typicalS A B rest) p, (1 : ℝ) / (k : ℝ)
        ≤ X := by
    intro p hp
    have hpq : ((p * p : ℕ) : ℝ) ≤ Q ^ 2 := by
      push_cast
      nlinarith [hhi p hp]
    have hscale := quotient_scale_le_of_le A (p * p) T (Q ^ 2)
      (by
        have hpp0 : 0 < p * p := Nat.mul_pos (hprime p hp).pos (hprime p hp).pos
        omega)
      (hppA p hp) hT hpq
    have hmassq := collisionQuotSupport_harmonic_le A B R P rest p
      (hprime p hp) (hppA p hp) hR hB
    dsimp [X]
    have hleft0 : 0 ≤ Real.exp Real.pi *
        (T / ((A / (p * p) : ℕ) : ℝ) + 8) := by positivity
    have hright0 : 0 ≤ Real.exp Real.pi *
        (2 * T * Q ^ 2 / (A : ℝ) + 8) := by positivity
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le)
      hmassq (Finset.sum_nonneg fun k _ => by positivity) hright0
  have hinner :
      ∑ p ∈ P, ((1 : ℝ) / (p : ℝ))
          * (((1 : ℝ) / (p : ℝ)) ^ 2
            * (Real.exp Real.pi * (T / ((A / (p * p) : ℕ) : ℝ) + 8)
              * ∑ k ∈ collisionQuotSupport (typicalS A B rest) p,
                  (1 : ℝ) / (k : ℝ)))
        ≤ X * (E / Plo ^ 2) := by
    calc
      ∑ p ∈ P, ((1 : ℝ) / (p : ℝ))
            * (((1 : ℝ) / (p : ℝ)) ^ 2
              * (Real.exp Real.pi * (T / ((A / (p * p) : ℕ) : ℝ) + 8)
                * ∑ k ∈ collisionQuotSupport (typicalS A B rest) p,
                    (1 : ℝ) / (k : ℝ)))
          ≤ ∑ p ∈ P, ((1 : ℝ) / (p : ℝ)) ^ 3 * X := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hp0 : 0 ≤ (1 : ℝ) / (p : ℝ) := by positivity
        calc
          ((1 : ℝ) / (p : ℝ)) * (((1 : ℝ) / (p : ℝ)) ^ 2 * _)
              = ((1 : ℝ) / (p : ℝ)) ^ 3 *
                  (Real.exp Real.pi * (T / ((A / (p * p) : ℕ) : ℝ) + 8)
                    * ∑ k ∈ collisionQuotSupport (typicalS A B rest) p,
                        (1 : ℝ) / (k : ℝ)) := by ring
          _ ≤ ((1 : ℝ) / (p : ℝ)) ^ 3 * X := by
            exact mul_le_mul_of_nonneg_left (hcost p hp) (by positivity)
      _ = X * ∑ p ∈ P, ((1 : ℝ) / (p : ℝ)) ^ 3 := by
        rw [← Finset.sum_mul]
        ring
      _ ≤ X * (E / Plo ^ 2) := mul_le_mul_of_nonneg_left hcubic hX0
  unfold collisionEnergyBound
  have houter0 : 0 ≤ ∑ p ∈ P, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_nonneg fun p _ => by positivity
  have hinner0 : 0 ≤ ∑ p ∈ P, ((1 : ℝ) / (p : ℝ))
      * (((1 : ℝ) / (p : ℝ)) ^ 2
        * (Real.exp Real.pi * (T / ((A / (p * p) : ℕ) : ℝ) + 8)
          * ∑ k ∈ collisionQuotSupport (typicalS A B rest) p,
              (1 : ℝ) / (k : ℝ))) := Finset.sum_nonneg fun p _ => by positivity
  calc
    (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) * _ ≤ E * _ :=
      mul_le_mul_of_nonneg_right hmass hinner0
    _ ≤ E * (X * (E / Plo ^ 2)) := mul_le_mul_of_nonneg_left hinner hE0
    _ = E * ((E / Plo ^ 2) *
        (Real.exp Real.pi * (2 * T * Q ^ 2 / (A : ℝ) + 8)
          * Real.log (2 * (R : ℝ)))) := by
      dsimp [X]
      ring

/-- The collision fit is discharged by one explicit closed-form inequality. -/
theorem collision_fit_of_schedule (A B R : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ)) (T Plo Q E c₃ eps rho kappa : ℝ)
    (hA : 0 < A) (hR : 1 ≤ R) (hB : B ≤ R * A) (hT : 0 ≤ T)
    (hPlo : 0 < Plo) (hQ : 0 ≤ Q)
    (hprime : ∀ p ∈ P, p.Prime) (hppA : ∀ p ∈ P, p * p ≤ A)
    (hlo : ∀ p ∈ P, Plo ≤ (p : ℝ)) (hhi : ∀ p ∈ P, (p : ℝ) ≤ Q)
    (hmass : ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ≤ E)
    (hschedule : 8 * (E * ((E / Plo ^ 2) *
        (Real.exp Real.pi * (2 * T * Q ^ 2 / (A : ℝ) + 8)
          * Real.log (2 * (R : ℝ)))))
      ≤ kappa * bandBudget c₃ eps rho) :
    8 * collisionEnergyBound A B P rest T
      ≤ kappa * bandBudget c₃ eps rho := by
  exact (mul_le_mul_of_nonneg_left
    (collisionEnergyBound_le_schedule A B R P rest T Plo Q E hA hR hB hT
      hPlo hQ hprime hppA hlo hhi hmass) (by norm_num)).trans hschedule

end MoltResearch
