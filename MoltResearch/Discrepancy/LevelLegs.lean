import MoltResearch.Discrepancy.BandCapstone
import MoltResearch.Discrepancy.LevelSizes
import MoltResearch.Discrepancy.PrimeMassCell

/-!
# The level legs of the `[mrt]` A.2 inner band (Track R, A2-III, VI-2)

The A.2 capstone takes the first-index partition abstractly.  This module binds
that partition to the small-value sets of the e-adic cell polynomials and then
composes the already proved level estimates with the schedule arithmetic.
-/

namespace MoltResearch

/-- The prime polynomial carried by one e-adic cell of a level. -/
noncomputable def levelCellPoly (P : Finset ℕ) (N v : ℕ) (g : ℕ → ℂ)
    (xi : ℝ) : ℂ :=
  ∑ p ∈ eadicCell P (2 * N) v, (g p / (p : ℂ))
    * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ)

/-! ## The exact level decomposition -/

/-- The noncollision fibre in the Ramaré decomposition of the typical-set
polynomial. -/
noncomputable def typicalSMainFibre (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (p : ℕ) (xi : ℝ) : ℂ :=
  (g p / (p : ℂ))
      * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ)
      * ∑ m ∈ (((typicalS A B rest).filter (fun n => p ∣ n)).image (· / p)).filter
          (fun m => ¬ p ∣ m),
        ((g m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
          / (((P.filter (· ∣ m)).card : ℂ) + 1)

/-- The repeated-prime fibre left by the Ramaré decomposition. -/
noncomputable def typicalSCollision (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (xi : ℝ) : ℂ :=
  ∑ p ∈ P, ∑ m ∈ (((typicalS A B rest).filter
      (fun n => p ∣ n)).image (· / p)).filter (fun m => p ∣ m),
    ((g (p * m) / ((p * m : ℕ) : ℂ))
        * ((Real.fourierChar (-(Real.log (p * m : ℕ) * xi)) : Circle) : ℂ))
      / (((P.filter (· ∣ (p * m))).card : ℂ))

/-- The quotient support after extracting both copies of a repeated prime. -/
def collisionQuotSupport (S : Finset ℕ) (p : ℕ) : Finset ℕ :=
  ((((S.filter (fun n => p ∣ n)).image (· / p)).filter
      (fun m => p ∣ m)).image (· / p))

/-- The Ramaré coefficient on a twice-extracted collision fibre. -/
noncomputable def collisionQuotCoeff (g : ℕ → ℂ) (P : Finset ℕ)
    (p k : ℕ) : ℂ :=
  g (p * (p * k)) / (((P.filter (· ∣ (p * (p * k)))).card : ℂ))

/-- Double extraction puts every collision fibre at the scale `A / p²`. -/
theorem collisionQuotSupport_subset (A B : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioc A B) {p : ℕ} (hp : 0 < p) :
    collisionQuotSupport S p ⊆ Finset.Ioc (A / (p * p)) (B / (p * p)) := by
  intro k hk
  have hfirst : ((S.filter (fun n => p ∣ n)).image (· / p)) ⊆
      Finset.Ioc (A / p) (B / p) :=
    image_div_fibre_subset A B S hS hp
  have hsecond := image_div_fibre_subset (A / p) (B / p)
    ((S.filter (fun n => p ∣ n)).image (· / p)) hfirst hp hk
  simpa only [collisionQuotSupport, Nat.div_div_eq_div_mul] using hsecond

/-- The collision divisor count never enlarges a `1`-bounded coefficient. -/
theorem norm_collisionQuotCoeff_le_one (g : ℕ → ℂ)
    (hg : ∀ n, ‖g n‖ ≤ 1) (P : Finset ℕ) (p k : ℕ) :
    ‖collisionQuotCoeff g P p k‖ ≤ 1 := by
  classical
  unfold collisionQuotCoeff
  by_cases hzero : (P.filter (· ∣ (p * (p * k)))).card = 0
  · simp [hzero]
  · rw [norm_div, Complex.norm_natCast, div_le_one (by positivity)]
    exact (hg _).trans (by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hzero))

/-- **A repeated-prime fibre is a quotient-scale polynomial.**

The second exact divisibility reindex writes `m = p*k`.  The two factors
`1/p` are deliberately separated: one is the harmonic weight used by the
outer weighted Cauchy–Schwarz inequality, and the other remains on the
quotient polynomial.  This is what retains the second-order `p` saving.
-/
theorem typicalSCollision_fibre_eq_factored
    (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ)) {p : ℕ} (hp : 0 < p) (xi : ℝ) :
    (∑ m ∈ (((typicalS A B rest).filter (fun n => p ∣ n)).image
          (· / p)).filter (fun m => p ∣ m),
        ((g (p * m) / ((p * m : ℕ) : ℂ))
            * ((Real.fourierChar (-(Real.log (p * m : ℕ) * xi)) : Circle) : ℂ))
          / (((P.filter (· ∣ (p * m))).card : ℂ)))
      = (((1 : ℂ) / (p : ℂ))
          * ((Real.fourierChar (-(Real.log (p * p : ℕ) * xi)) : Circle) : ℂ))
        * (((1 : ℂ) / (p : ℂ))
          * ∑ k ∈ collisionQuotSupport (typicalS A B rest) p,
            (collisionQuotCoeff g P p k / (k : ℂ))
              * ((Real.fourierChar (-(Real.log k * xi)) : Circle) : ℂ)) := by
  classical
  let S := ((typicalS A B rest).filter (fun n => p ∣ n)).image (· / p)
  rw [sum_filter_dvd_eq_sum_image S hp]
  change (∑ k ∈ collisionQuotSupport (typicalS A B rest) p,
      ((g (p * (p * k)) / ((p * (p * k) : ℕ) : ℂ))
          * ((Real.fourierChar
            (-(Real.log (p * (p * k) : ℕ) * xi)) : Circle) : ℂ))
        / (((P.filter (· ∣ (p * (p * k)))).card : ℂ))) = _
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hksub := collisionQuotSupport_subset A B (typicalS A B rest)
    (typicalS_subset_Ioc A B rest) hp hk
  have hk0 : k ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hksub).1)
  rw [show p * (p * k) = (p * p) * k by ring,
    char_log_mul (p * p) k (by positivity) hk0 xi]
  unfold collisionQuotCoeff
  push_cast
  field_simp
  ring

/-- The harmonic outer weight of a twice-extracted collision fibre. -/
noncomputable def collisionPrimeWeight (p : ℕ) (xi : ℝ) : ℂ :=
  ((1 : ℂ) / (p : ℂ))
    * ((Real.fourierChar (-(Real.log (p * p : ℕ) * xi)) : Circle) : ℂ)

/-- The remaining quotient polynomial, including the second factor `1/p`. -/
noncomputable def collisionQuotPoly (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (p : ℕ) (xi : ℝ) : ℂ :=
  ((1 : ℂ) / (p : ℂ))
    * ∑ k ∈ collisionQuotSupport (typicalS A B rest) p,
      (collisionQuotCoeff g P p k / (k : ℂ))
        * ((Real.fourierChar (-(Real.log k * xi)) : Circle) : ℂ)

/-- **The whole repeated-prime term is a harmonically weighted quotient sum.** -/
theorem typicalSCollision_eq_weighted_quotient_sum
    (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (rest : List (Finset ℕ)) (xi : ℝ) :
    typicalSCollision g A B P rest xi
      = ∑ p ∈ P, collisionPrimeWeight p xi
          * collisionQuotPoly g A B P rest p xi := by
  classical
  unfold typicalSCollision
  refine Finset.sum_congr rfl fun p hpP => ?_
  exact typicalSCollision_fibre_eq_factored g A B P rest (hP p hpP).pos xi

/-- Collision prime weights are continuous in frequency. -/
theorem continuous_collisionPrimeWeight (p : ℕ) :
    Continuous (collisionPrimeWeight p) := by
  unfold collisionPrimeWeight
  exact continuous_const.mul (continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp (by fun_prop)))

/-- Collision quotient polynomials are continuous in frequency. -/
theorem continuous_collisionQuotPoly
    (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ)) (p : ℕ) :
    Continuous (collisionQuotPoly g A B P rest p) := by
  unfold collisionQuotPoly
  refine continuous_const.mul (continuous_finset_sum _ fun k _ => ?_)
  exact continuous_const.mul (continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp (by fun_prop)))

/-- The outer collision weight has exactly the harmonic norm `1/p`. -/
theorem norm_collisionPrimeWeight (p : ℕ) (xi : ℝ) :
    ‖collisionPrimeWeight p xi‖ = (1 : ℝ) / (p : ℝ) := by
  unfold collisionPrimeWeight
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast,
    norm_eq_of_mem_sphere, mul_one]

open MeasureTheory Finset ExpSums in
/-- **One collision quotient polynomial retains a second `1/p`.**

The sharp mean-value theorem is applied after both copies of `p` have been
extracted, at base `A / p²`.  Natural-number division can double the block
ratio, so the harmless absolute term is `8`; the leading factor `1/p²` is
kept outside and is the saving needed by the collision schedule.
-/
theorem intervalIntegral_norm_sq_collisionQuotPoly_le
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (A Delta : ℕ) (hDeltaA : Delta ≤ A)
    (P : Finset ℕ) (rest : List (Finset ℕ))
    {p : ℕ} (hp : p.Prime) (hppA : p * p ≤ A)
    (T : ℝ) (hT : 0 < T) :
    (∫ xi in (-T)..T, ‖collisionQuotPoly g A (A + Delta) P rest p xi‖ ^ 2)
      ≤ ((1 : ℝ) / (p : ℝ)) ^ 2
          * (Real.exp Real.pi
            * (T / ((A / (p * p) : ℕ) : ℝ) + 8)
            * ∑ k ∈ collisionQuotSupport (typicalS A (A + Delta) rest) p,
                (1 : ℝ) / (k : ℝ)) := by
  classical
  let K := collisionQuotSupport (typicalS A (A + Delta) rest) p
  let c : ℕ → ℂ := fun k => ((1 : ℂ) / (p : ℂ)) * collisionQuotCoeff g P p k
  have hp0 : 0 < p := hp.pos
  have hpp0 : 0 < p * p := Nat.mul_pos hp0 hp0
  have hbase : 1 ≤ A / (p * p) := (Nat.one_le_div_iff hpp0).mpr hppA
  have hKraw : K ⊆ Finset.Ioc (A / (p * p)) ((A + Delta) / (p * p)) :=
    collisionQuotSupport_subset A (A + Delta) (typicalS A (A + Delta) rest)
      (typicalS_subset_Ioc A (A + Delta) rest) hp0
  have hwindow : Finset.Ioc (A / (p * p)) ((A + Delta) / (p * p)) ⊆
      Finset.Ioc (A / (p * p)) (4 * (A / (p * p))) := by
    have hratio := Ioc_div_subset_Ioc_two_mul_ratio A (A + Delta) 2 (p * p)
      (by omega) hppA (by norm_num) (by omega)
    simpa only [Nat.reduceMul] using hratio
  have hK : K ⊆ Finset.Ioc (A / (p * p)) (4 * (A / (p * p))) :=
    hKraw.trans hwindow
  have hshape : ∀ xi : ℝ, collisionQuotPoly g A (A + Delta) P rest p xi
      = ∑ k ∈ K, (c k / (k : ℂ))
          * ((Real.fourierChar (-(Real.log k * xi)) : Circle) : ℂ) := by
    intro xi
    unfold collisionQuotPoly
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp only [c]
    ring
  have hMVT := intervalIntegral_norm_sq_poly_le_sharp_ratio
    (A / (p * p)) 4 hbase (by norm_num) K hK c T hT
  have hmass : ∑ k ∈ K, ‖c k‖ ^ 2 / (k : ℝ)
      ≤ ((1 : ℝ) / (p : ℝ)) ^ 2 * ∑ k ∈ K, (1 : ℝ) / (k : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk0 : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp (hK hk)).1)
    have hcp : ‖c k‖ ≤ (1 : ℝ) / (p : ℝ) := by
      dsimp only [c]
      rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
      exact mul_le_of_le_one_right (by positivity) (norm_collisionQuotCoeff_le_one g hg P p k)
    have hsq : ‖c k‖ ^ 2 ≤ ((1 : ℝ) / (p : ℝ)) ^ 2 := by
      nlinarith [norm_nonneg (c k)]
    calc
      ‖c k‖ ^ 2 / (k : ℝ) ≤ ((1 : ℝ) / (p : ℝ)) ^ 2 / (k : ℝ) := by
        exact div_le_div_of_nonneg_right hsq hk0.le
      _ = ((1 : ℝ) / (p : ℝ)) ^ 2 * (1 / (k : ℝ)) := by ring
  calc
    (∫ xi in (-T)..T, ‖collisionQuotPoly g A (A + Delta) P rest p xi‖ ^ 2)
        = ∫ xi in (-T)..T, ‖∑ k ∈ K, (c k / (k : ℂ))
            * ((Real.fourierChar (-(Real.log k * xi)) : Circle) : ℂ)‖ ^ 2 := by
          apply intervalIntegral.integral_congr
          intro xi _
          exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (hshape xi)
    _
        ≤ Real.exp Real.pi
            * (T / ((A / (p * p) : ℕ) : ℝ) + 2 * (4 : ℝ))
            * ∑ k ∈ K, ‖c k‖ ^ 2 / (k : ℝ) := hMVT
    _ ≤ Real.exp Real.pi
            * (T / ((A / (p * p) : ℕ) : ℝ) + 8)
            * (((1 : ℝ) / (p : ℝ)) ^ 2
              * ∑ k ∈ K, (1 : ℝ) / (k : ℝ)) := by
          gcongr
          norm_num
    _ = ((1 : ℝ) / (p : ℝ)) ^ 2
          * (Real.exp Real.pi
            * (T / ((A / (p * p) : ℕ) : ℝ) + 8)
            * ∑ k ∈ K, (1 : ℝ) / (k : ℝ)) := by ring

/-- The explicit weighted mean-value envelope for the repeated-prime term. -/
noncomputable def collisionEnergyBound (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (T : ℝ) : ℝ :=
  (∑ p ∈ P, (1 : ℝ) / (p : ℝ))
    * ∑ p ∈ P, ((1 : ℝ) / (p : ℝ))
      * (((1 : ℝ) / (p : ℝ)) ^ 2
        * (Real.exp Real.pi * (T / ((A / (p * p) : ℕ) : ℝ) + 8)
          * ∑ k ∈ collisionQuotSupport (typicalS A B rest) p,
              (1 : ℝ) / (k : ℝ)))

open MeasureTheory Finset ExpSums in
/-- **Weighted Cauchy–Schwarz assembles the repeated-prime collision.**

The outer factors have norm `1/p`, so weighted Cauchy–Schwarz costs the
prime harmonic mass rather than the number of primes.  Each quotient energy
then retains `1/p²`; together the non-window part is cubic in `1/p`, exactly
the corrected collision scaling.
-/
theorem intervalIntegral_norm_sq_typicalSCollision_le
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (A Delta : ℕ) (hDeltaA : Delta ≤ A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hPA : ∀ p ∈ P, p * p ≤ A)
    (rest : List (Finset ℕ)) (T : ℝ) (hT : 0 < T) :
    (∫ xi in (-T)..T, ‖typicalSCollision g A (A + Delta) P rest xi‖ ^ 2)
      ≤ collisionEnergyBound A (A + Delta) P rest T := by
  have hweighted := intervalIntegral_norm_sq_freq_weighted_sum_le P
    collisionPrimeWeight (fun p => (1 : ℝ) / (p : ℝ))
    (fun p xi => (norm_collisionPrimeWeight p xi).le)
    continuous_collisionPrimeWeight
    (collisionQuotPoly g A (A + Delta) P rest)
    (continuous_collisionQuotPoly g A (A + Delta) P rest)
    T hT.le
  calc
    (∫ xi in (-T)..T, ‖typicalSCollision g A (A + Delta) P rest xi‖ ^ 2)
        = ∫ xi in (-T)..T, ‖∑ p ∈ P, collisionPrimeWeight p xi
            * collisionQuotPoly g A (A + Delta) P rest p xi‖ ^ 2 := by
          apply intervalIntegral.integral_congr
          intro xi _
          exact congrArg (fun z : ℂ => ‖z‖ ^ 2)
            (typicalSCollision_eq_weighted_quotient_sum
              g A (A + Delta) P hP rest xi)
    _ ≤ (∑ p ∈ P, (1 : ℝ) / (p : ℝ))
          * ∑ p ∈ P, ((1 : ℝ) / (p : ℝ))
            * ∫ xi in (-T)..T,
                ‖collisionQuotPoly g A (A + Delta) P rest p xi‖ ^ 2 := hweighted
    _ ≤ (∑ p ∈ P, (1 : ℝ) / (p : ℝ))
          * ∑ p ∈ P, ((1 : ℝ) / (p : ℝ))
            * (((1 : ℝ) / (p : ℝ)) ^ 2
              * (Real.exp Real.pi
                * (T / ((A / (p * p) : ℕ) : ℝ) + 8)
                * ∑ k ∈ collisionQuotSupport
                    (typicalS A (A + Delta) rest) p,
                    (1 : ℝ) / (k : ℝ))) := by
          gcongr with p hpP
          exact intervalIntegral_norm_sq_collisionQuotPoly_le g hg A Delta
            hDeltaA P rest (hP p hpP) (hPA p hpP) T hT
    _ = collisionEnergyBound A (A + Delta) P rest T := rfl

/-- The quotient coefficient of the terms added to complete a full block. -/
noncomputable def addedCollisionQuotCoeff (g : ℕ → ℂ) (P : Finset ℕ)
    (p k : ℕ) : ℂ :=
  (g p * g (p * k)) / ((((P.filter (· ∣ (p * k))).card : ℂ) + 1))

/-- The full-block correction coefficient is still `1`-bounded. -/
theorem norm_addedCollisionQuotCoeff_le_one (g : ℕ → ℂ)
    (hg : ∀ n, ‖g n‖ ≤ 1) (P : Finset ℕ) (p k : ℕ) :
    ‖addedCollisionQuotCoeff g P p k‖ ≤ 1 := by
  classical
  unfold addedCollisionQuotCoeff
  rw [norm_div, norm_mul]
  have hnum : ‖g p‖ * ‖g (p * k)‖ ≤ 1 := by
    nlinarith [hg p, hg (p * k), norm_nonneg (g p), norm_nonneg (g (p * k))]
  have hden : ‖((P.filter (· ∣ (p * k))).card : ℂ) + 1‖
      = ((P.filter (· ∣ (p * k))).card : ℝ) + 1 := by
    rw [show ((P.filter (· ∣ (p * k))).card : ℂ) + 1 =
        (((P.filter (· ∣ (p * k))).card + 1 : ℕ) : ℂ) by push_cast; ring,
      Complex.norm_natCast]
    push_cast
    ring
  rw [hden, div_le_one (by positivity)]
  exact hnum.trans (by
    have hcard : (0 : ℝ) ≤ ((P.filter (· ∣ (p * k))).card : ℝ) := by positivity
    linarith)

/-- The quotient polynomial formed by the compensating full-block terms. -/
noncomputable def addedCollisionQuotPoly (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (p : ℕ) (xi : ℝ) : ℂ :=
  ((1 : ℂ) / (p : ℂ))
    * ∑ k ∈ collisionQuotSupport (typicalS A B rest) p,
      (addedCollisionQuotCoeff g P p k / (k : ℂ))
        * ((Real.fourierChar (-(Real.log k * xi)) : Circle) : ℂ)

/-- One compensating fibre has the same quotient-scale shape as a collision. -/
theorem typicalSAddedTerms_fibre_eq_factored
    (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ)) {p : ℕ} (hp : 0 < p) (xi : ℝ) :
    ((g p / (p : ℂ))
          * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
        * ∑ m ∈ (((typicalS A B rest).filter
            (fun n => p ∣ n)).image (· / p)).filter (fun m => p ∣ m),
          ((g m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
            / (((P.filter (· ∣ m)).card : ℂ) + 1)
      = collisionPrimeWeight p xi * addedCollisionQuotPoly g A B P rest p xi := by
  classical
  let S := ((typicalS A B rest).filter (fun n => p ∣ n)).image (· / p)
  rw [sum_filter_dvd_eq_sum_image S hp]
  unfold addedCollisionQuotPoly collisionPrimeWeight
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hksub := collisionQuotSupport_subset A B (typicalS A B rest)
    (typicalS_subset_Ioc A B rest) hp hk
  have hk0 : k ≠ 0 :=
    Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hksub).1)
  rw [char_log_mul p k hp.ne' hk0 xi, char_log_mul p p hp.ne' hp.ne' xi]
  unfold addedCollisionQuotCoeff
  push_cast
  field_simp

/-- The compensating quotient polynomials are continuous in frequency. -/
theorem continuous_addedCollisionQuotPoly
    (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ)) (p : ℕ) :
    Continuous (addedCollisionQuotPoly g A B P rest p) := by
  unfold addedCollisionQuotPoly
  refine continuous_const.mul (continuous_finset_sum _ fun k _ => ?_)
  exact continuous_const.mul (continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp (by fun_prop)))

open MeasureTheory Finset ExpSums in
/-- The quotient-scale mean-value estimate depends only on support and a
`1`-bounded coefficient. -/
theorem intervalIntegral_norm_sq_scaled_quotient_le
    (A Delta : ℕ) (hDeltaA : Delta ≤ A)
    {p : ℕ} (hp : p.Prime) (hppA : p * p ≤ A)
    (K : Finset ℕ)
    (hKraw : K ⊆ Finset.Ioc (A / (p * p)) ((A + Delta) / (p * p)))
    (c : ℕ → ℂ) (hc : ∀ k, ‖c k‖ ≤ 1)
    (T : ℝ) (hT : 0 < T) :
    (∫ xi in (-T)..T, ‖((1 : ℂ) / (p : ℂ))
        * ∑ k ∈ K, (c k / (k : ℂ))
          * ((Real.fourierChar (-(Real.log k * xi)) : Circle) : ℂ)‖ ^ 2)
      ≤ ((1 : ℝ) / (p : ℝ)) ^ 2
          * (Real.exp Real.pi
            * (T / ((A / (p * p) : ℕ) : ℝ) + 8)
            * ∑ k ∈ K, (1 : ℝ) / (k : ℝ)) := by
  classical
  let cp : ℕ → ℂ := fun k => ((1 : ℂ) / (p : ℂ)) * c k
  have hp0 : 0 < p := hp.pos
  have hpp0 : 0 < p * p := Nat.mul_pos hp0 hp0
  have hbase : 1 ≤ A / (p * p) := (Nat.one_le_div_iff hpp0).mpr hppA
  have hwindow : Finset.Ioc (A / (p * p)) ((A + Delta) / (p * p)) ⊆
      Finset.Ioc (A / (p * p)) (4 * (A / (p * p))) := by
    have hratio := Ioc_div_subset_Ioc_two_mul_ratio A (A + Delta) 2 (p * p)
      (by omega) hppA (by norm_num) (by omega)
    simpa only [Nat.reduceMul] using hratio
  have hK : K ⊆ Finset.Ioc (A / (p * p)) (4 * (A / (p * p))) :=
    hKraw.trans hwindow
  have hshape : ∀ xi : ℝ,
      ((1 : ℂ) / (p : ℂ)) * ∑ k ∈ K, (c k / (k : ℂ))
          * ((Real.fourierChar (-(Real.log k * xi)) : Circle) : ℂ)
        = ∑ k ∈ K, (cp k / (k : ℂ))
          * ((Real.fourierChar (-(Real.log k * xi)) : Circle) : ℂ) := by
    intro xi
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp only [cp]
    ring
  have hMVT := intervalIntegral_norm_sq_poly_le_sharp_ratio
    (A / (p * p)) 4 hbase (by norm_num) K hK cp T hT
  have hmass : ∑ k ∈ K, ‖cp k‖ ^ 2 / (k : ℝ)
      ≤ ((1 : ℝ) / (p : ℝ)) ^ 2 * ∑ k ∈ K, (1 : ℝ) / (k : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk0 : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp (hK hk)).1)
    have hcp : ‖cp k‖ ≤ (1 : ℝ) / (p : ℝ) := by
      dsimp only [cp]
      rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
      exact mul_le_of_le_one_right (by positivity) (hc k)
    have hsq : ‖cp k‖ ^ 2 ≤ ((1 : ℝ) / (p : ℝ)) ^ 2 := by
      nlinarith [norm_nonneg (cp k)]
    calc
      ‖cp k‖ ^ 2 / (k : ℝ) ≤ ((1 : ℝ) / (p : ℝ)) ^ 2 / (k : ℝ) := by
        exact div_le_div_of_nonneg_right hsq hk0.le
      _ = ((1 : ℝ) / (p : ℝ)) ^ 2 * (1 / (k : ℝ)) := by ring
  calc
    (∫ xi in (-T)..T, ‖((1 : ℂ) / (p : ℂ))
        * ∑ k ∈ K, (c k / (k : ℂ))
          * ((Real.fourierChar (-(Real.log k * xi)) : Circle) : ℂ)‖ ^ 2)
        = ∫ xi in (-T)..T, ‖∑ k ∈ K, (cp k / (k : ℂ))
            * ((Real.fourierChar (-(Real.log k * xi)) : Circle) : ℂ)‖ ^ 2 := by
          apply intervalIntegral.integral_congr
          intro xi _
          exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (hshape xi)
    _ ≤ Real.exp Real.pi
          * (T / ((A / (p * p) : ℕ) : ℝ) + 2 * (4 : ℝ))
          * ∑ k ∈ K, ‖cp k‖ ^ 2 / (k : ℝ) := hMVT
    _ ≤ Real.exp Real.pi
          * (T / ((A / (p * p) : ℕ) : ℝ) + 8)
          * (((1 : ℝ) / (p : ℝ)) ^ 2
            * ∑ k ∈ K, (1 : ℝ) / (k : ℝ)) := by
        gcongr
        norm_num
    _ = ((1 : ℝ) / (p : ℝ)) ^ 2
          * (Real.exp Real.pi
            * (T / ((A / (p * p) : ℕ) : ℝ) + 8)
            * ∑ k ∈ K, (1 : ℝ) / (k : ℝ)) := by ring

/-- The compensating quotient has the same energy envelope as the original
collision quotient. -/
theorem intervalIntegral_norm_sq_addedCollisionQuotPoly_le
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (A Delta : ℕ) (hDeltaA : Delta ≤ A)
    (P : Finset ℕ) (rest : List (Finset ℕ))
    {p : ℕ} (hp : p.Prime) (hppA : p * p ≤ A)
    (T : ℝ) (hT : 0 < T) :
    (∫ xi in (-T)..T, ‖addedCollisionQuotPoly g A (A + Delta) P rest p xi‖ ^ 2)
      ≤ ((1 : ℝ) / (p : ℝ)) ^ 2
          * (Real.exp Real.pi
            * (T / ((A / (p * p) : ℕ) : ℝ) + 8)
            * ∑ k ∈ collisionQuotSupport (typicalS A (A + Delta) rest) p,
                (1 : ℝ) / (k : ℝ)) := by
  exact intervalIntegral_norm_sq_scaled_quotient_le A Delta hDeltaA hp hppA
    (collisionQuotSupport (typicalS A (A + Delta) rest) p)
    (collisionQuotSupport_subset A (A + Delta) (typicalS A (A + Delta) rest)
      (typicalS_subset_Ioc A (A + Delta) rest) hp.pos)
    (addedCollisionQuotCoeff g P p)
    (norm_addedCollisionQuotCoeff_le_one g hg P p) T hT

open Finset in
/-- **The exact typical-set decomposition, grouped by e-adic cells.**

The useful first half of the decomposition is purely algebraic:
`typicalS_phase_main_add_coll` supplies the corrected `1/(ω+1)` quotient
weight and the repeated-prime term, while disjointness of `eadicCell` changes
the outer prime sum into the level's cell range.  No estimate and no enlarged
quotient block enters this equality.

The cover is kept explicit because the analytic schedule normally indexes only
the cells between its endpoints `v₀` and `v₁`, rather than every cell from
zero. -/
theorem typicalS_phase_eq_eadic_main_add_collision
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g)
    (A B : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (xi : ℝ) :
    ∑ m ∈ typicalS A (A + B) (P :: rest), (g m / (m : ℂ))
        * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)
      = (∑ v ∈ Finset.Ico v₀ (v₁ + 1),
          ∑ p ∈ eadicCell P (2 * N) v,
            typicalSMainFibre g A (A + B) P rest p xi)
        + typicalSCollision g A (A + B) P rest xi := by
  classical
  rw [typicalS_phase_main_add_coll g hcm A B P hP rest xi]
  change (∑ p ∈ P, typicalSMainFibre g A (A + B) P rest p xi)
      + typicalSCollision g A (A + B) P rest xi = _
  congr 1
  have hdisj : Set.PairwiseDisjoint
      (↑(Finset.Ico v₀ (v₁ + 1)) : Set ℕ) (eadicCell P (2 * N)) :=
    fun v _ w _ hvw => eadicCell_disjoint P (2 * N) hvw
  calc
    ∑ p ∈ P, typicalSMainFibre g A (A + B) P rest p xi =
        ∑ p ∈ (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)),
          typicalSMainFibre g A (A + B) P rest p xi := by
            rw [hcov]
    _ = ∑ v ∈ Finset.Ico v₀ (v₁ + 1),
          ∑ p ∈ eadicCell P (2 * N) v,
            typicalSMainFibre g A (A + B) P rest p xi :=
      Finset.sum_biUnion hdisj

open Finset in
/-- **N3-f reaches the prime-block interface once its fibres are identified.**

The exact N3-f quotient support depends on the extracted prime `p`, whereas
`setIntegral_norm_sq_cell_prime_block_le` consumes a full quotient interval
with one coefficient function `c`.  This lemma isolates that sole algebraic
obligation as `hfibre`.  After it is supplied, regrouping by e-adic cells is
already enough to put the main term into the precise shape of II-2e; the
repeated-prime collision remains additive.
-/
theorem typicalS_phase_eq_eadic_prime_block_add_collision_of_fibres
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g)
    (A Delta : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (c : ℕ → ℂ)
    (hfibre : ∀ p ∈ P, ∀ xi : ℝ,
      (∑ m ∈ (((typicalS A (A + Delta) rest).filter
            (fun n => p ∣ n)).image (· / p)).filter (fun m => ¬ p ∣ m),
          ((g m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
            / (((P.filter (· ∣ m)).card : ℂ) + 1))
        = ∑ m ∈ Finset.Ioc (A / p) ((A + Delta) / p),
            (c m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
    (xi : ℝ) :
    ∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
        * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)
      = (∑ v ∈ Finset.Ico v₀ (v₁ + 1),
          ∑ p ∈ eadicCell P (2 * N) v,
            ((g p / (p : ℂ))
                * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
              * (∑ m ∈ Finset.Ioc (A / p) ((A + Delta) / p),
                  (c m / (m : ℂ))
                    * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)))
        + typicalSCollision g A (A + Delta) P rest xi := by
  rw [typicalS_phase_eq_eadic_main_add_collision g hcm A Delta P hP rest N v₀ v₁
    hcov xi]
  congr 1
  refine Finset.sum_congr rfl fun v hv => ?_
  refine Finset.sum_congr rfl fun p hp => ?_
  unfold typicalSMainFibre
  rw [hfibre p (mem_eadicCell.mp hp).1 xi]

open MeasureTheory Finset ExpSums in
/-- **The exact decomposition costs one `L²` triangle.**

After the N3-f main term has been regrouped by cells, separating it from the
repeated-prime term costs precisely
`2 ∫‖main‖² + 2 ∫‖collision‖²`.  This is the pointwise inequality
`‖x+y‖² ≤ 2‖x‖²+2‖y‖²` integrated on the actual frequency set; the set is
not enlarged, so later small- and large-value information remains available.
-/
theorem setIntegral_norm_sq_typicalS_le_eadic_main_collision
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g)
    (A Delta : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (T : ℝ) (G : Set ℝ) (hGm : MeasurableSet G)
    (hGT : G ⊆ Set.Ioc (-T) T) :
    (∫ xi in G, ‖∑ m ∈ typicalS A (A + Delta) (P :: rest),
        (g m / (m : ℂ))
          * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
      ≤ 2 * (∫ xi in G,
          ‖∑ v ∈ Finset.Ico v₀ (v₁ + 1),
            ∑ p ∈ eadicCell P (2 * N) v,
              typicalSMainFibre g A (A + Delta) P rest p xi‖ ^ 2)
        + 2 * (∫ xi in G,
          ‖typicalSCollision g A (A + Delta) P rest xi‖ ^ 2) := by
  classical
  have hchar : ∀ w : ℝ, Continuous fun xi : ℝ =>
      ((Real.fourierChar (-(w * xi)) : Circle) : ℂ) := fun w =>
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hfibre : ∀ p : ℕ, Continuous fun xi : ℝ =>
      typicalSMainFibre g A (A + Delta) P rest p xi := by
    intro p
    unfold typicalSMainFibre
    refine (continuous_const.mul (hchar (Real.log p))).mul ?_
    refine continuous_finset_sum _ fun m _ => ?_
    exact (continuous_const.mul (hchar (Real.log m))).div_const _
  have hmain : Continuous fun xi : ℝ =>
      ∑ v ∈ Finset.Ico v₀ (v₁ + 1),
        ∑ p ∈ eadicCell P (2 * N) v,
          typicalSMainFibre g A (A + Delta) P rest p xi := by
    exact continuous_finset_sum _ fun v _ =>
      continuous_finset_sum _ fun p _ => hfibre p
  have hcollision : Continuous fun xi : ℝ =>
      typicalSCollision g A (A + Delta) P rest xi := by
    unfold typicalSCollision
    refine continuous_finset_sum _ fun p _ => ?_
    refine continuous_finset_sum _ fun m _ => ?_
    exact (continuous_const.mul (hchar (Real.log (p * m : ℕ)))).div_const _
  calc
    (∫ xi in G, ‖∑ m ∈ typicalS A (A + Delta) (P :: rest),
        (g m / (m : ℂ))
          * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
        = ∫ xi in G,
            ‖(∑ v ∈ Finset.Ico v₀ (v₁ + 1),
                ∑ p ∈ eadicCell P (2 * N) v,
                  typicalSMainFibre g A (A + Delta) P rest p xi)
              + typicalSCollision g A (A + Delta) P rest xi‖ ^ 2 := by
          apply setIntegral_congr_fun hGm
          intro xi _
          exact congrArg (· ^ 2) (congrArg norm
            (typicalS_phase_eq_eadic_main_add_collision g hcm A Delta P hP
              rest N v₀ v₁ hcov xi))
    _ ≤ 2 * (∫ xi in G,
          ‖∑ v ∈ Finset.Ico v₀ (v₁ + 1),
            ∑ p ∈ eadicCell P (2 * N) v,
              typicalSMainFibre g A (A + Delta) P rest p xi‖ ^ 2)
        + 2 * (∫ xi in G,
          ‖typicalSCollision g A (A + Delta) P rest xi‖ ^ 2) :=
      setIntegral_norm_add_sq_le _ _ hmain hcollision T G hGm hGT

/-! ## The quotient coefficients -/

/-- The `1/(ω_P+1)`-weighted coefficient of the quotient polynomial,
extended by zero away from its typical support. -/
noncomputable def typicalSQuotCoeff (g : ℕ → ℂ) (P S : Finset ℕ)
    (m : ℕ) : ℂ :=
  if m ∈ S then g m / (((P.filter (· ∣ m)).card : ℂ) + 1) else 0

/-- The Ramaré weight never enlarges a `1`-bounded coefficient. -/
theorem norm_typicalSQuotCoeff_le_one (g : ℕ → ℂ)
    (hg : ∀ m, ‖g m‖ ≤ 1) (P S : Finset ℕ) (m : ℕ) :
    ‖typicalSQuotCoeff g P S m‖ ≤ 1 := by
  classical
  unfold typicalSQuotCoeff
  split_ifs
  · rw [norm_div]
    have hden : ‖((P.filter (· ∣ m)).card : ℂ) + 1‖
        = ((P.filter (· ∣ m)).card : ℝ) + 1 := by
      rw [show ((P.filter (· ∣ m)).card : ℂ) + 1 =
          (((P.filter (· ∣ m)).card + 1 : ℕ) : ℂ) by push_cast; ring,
        Complex.norm_natCast]
      push_cast
      ring
    rw [hden, div_le_one (by positivity)]
    exact (hg m).trans (by
      have : (0 : ℝ) ≤ ((P.filter (· ∣ m)).card : ℝ) := by positivity
      linarith)
  · simp

/-- On every quotient block, the squared mass of the weighted typical
coefficient is no larger than the unweighted harmonic mass. -/
theorem typicalSQuotCoeff_mass_le (g : ℕ → ℂ)
    (hg : ∀ m, ‖g m‖ ≤ 1) (P S : Finset ℕ) (a b : ℕ) :
    ∑ m ∈ Finset.Ioc a b, ‖typicalSQuotCoeff g P S m‖ ^ 2 / (m : ℝ)
      ≤ ∑ m ∈ Finset.Ioc a b, (1 : ℝ) / (m : ℝ) := by
  classical
  refine Finset.sum_le_sum fun m hm => ?_
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (by have := (Finset.mem_Ioc.mp hm).1; omega : 0 < m)
  rw [div_le_div_iff₀ hm0 hm0]
  have hc := norm_typicalSQuotCoeff_le_one g hg P S m
  have hsq : ‖typicalSQuotCoeff g P S m‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (typicalSQuotCoeff g P S m)]
  exact mul_le_mul_of_nonneg_right hsq hm0.le

/-- **A support identity discharges the quotient-fibre identity.**

Once the prime-dependent noncollision support from N3-f is identified with a
full quotient interval filtered by a fixed support `S`, extending the weighted
coefficient by zero makes the two Dirichlet polynomials literally equal.  Thus
the unresolved part of `hfibre` is set-theoretic; the phase and the
`1/(ω+1)` normalization introduce no further obligation.
-/
theorem typicalS_main_fibre_eq_block_of_support_eq
    (g : ℕ → ℂ) (A Delta : ℕ) (P S : Finset ℕ)
    (rest : List (Finset ℕ)) (p : ℕ)
    (hsupport : (((typicalS A (A + Delta) rest).filter
          (fun n => p ∣ n)).image (· / p)).filter (fun m => ¬ p ∣ m)
        = (Finset.Ioc (A / p) ((A + Delta) / p)).filter (fun m => m ∈ S))
    (xi : ℝ) :
    (∑ m ∈ (((typicalS A (A + Delta) rest).filter
          (fun n => p ∣ n)).image (· / p)).filter (fun m => ¬ p ∣ m),
        ((g m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
          / (((P.filter (· ∣ m)).card : ℂ) + 1))
      = ∑ m ∈ Finset.Ioc (A / p) ((A + Delta) / p),
          (typicalSQuotCoeff g P S m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ) := by
  classical
  rw [hsupport, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : m ∈ S
  · simp only [hm, if_true, typicalSQuotCoeff]
    ring
  · simp [hm, typicalSQuotCoeff]

/-- **Disjoint prime levels give the quotient-support stability condition.**

Multiplying by a prime from the extracted level cannot create a factor in any
remaining level when those levels are disjoint.  The reverse implication is
immediate from divisibility.  Thus the support-stability hypothesis used by
the full-block replacement is a consequence of the usual disjoint-level
schedule, rather than an additional analytic input.
-/
theorem hasFactorInAll_mul_iff_of_disjoint
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ))
    (hrest : ∀ Q ∈ rest, ∀ q ∈ Q, q.Prime)
    (hdisj : ∀ Q ∈ rest, Disjoint P Q)
    {p : ℕ} (hpP : p ∈ P) (m : ℕ) :
    HasFactorInAll rest (p * m) ↔ HasFactorInAll rest m := by
  constructor
  · intro h Q hQ
    obtain ⟨q, hq⟩ := Finset.card_pos.mp (h Q hQ)
    rw [Finset.mem_filter] at hq
    obtain ⟨hqQ, hqpm⟩ := hq
    rcases (hrest Q hQ q hqQ).dvd_mul.mp hqpm with hqp | hqm
    · have hqpEq : q = p :=
        (Nat.prime_dvd_prime_iff_eq (hrest Q hQ q hqQ) (hP p hpP)).mp hqp
      exact (Finset.disjoint_left.mp (hdisj Q hQ) hpP (hqpEq ▸ hqQ)).elim
    · exact Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨hqQ, hqm⟩⟩
  · intro h Q hQ
    obtain ⟨q, hq⟩ := Finset.card_pos.mp (h Q hQ)
    rw [Finset.mem_filter] at hq
    obtain ⟨hqQ, hqm⟩ := hq
    exact Finset.card_pos.mpr
      ⟨q, Finset.mem_filter.mpr ⟨hqQ, dvd_mul_of_dvd_right hqm p⟩⟩

/-- **A stable remaining-level condition identifies the full quotient
support.**

If multiplication by the extracted prime preserves `HasFactorInAll rest`, the
quotient image of the `p`-fibre of `typicalS A B rest` is exactly the quotient
interval filtered by `typicalS 0 B rest`.  This is the set-theoretic bridge
that permits adding the omitted `p ∣ m` terms to the main fibre while keeping one
coefficient function independent of `p`.
-/
theorem typicalS_fibre_image_eq_quotient_support
    (A B p : ℕ) (hp : 0 < p) (rest : List (Finset ℕ))
    (hstable : ∀ m, HasFactorInAll rest (p * m) ↔ HasFactorInAll rest m) :
    ((typicalS A B rest).filter (fun n => p ∣ n)).image (· / p)
      = (Finset.Ioc (A / p) (B / p)).filter
          (fun m => m ∈ typicalS 0 B rest) := by
  classical
  ext m
  constructor
  · intro hm
    rw [Finset.mem_image] at hm
    obtain ⟨n, hn, hnm⟩ := hm
    rw [Finset.mem_filter] at hn
    have hnEq : n = p * m := by
      calc
        n = p * (n / p) := (Nat.mul_div_cancel' hn.2).symm
        _ = p * m := by rw [hnm]
    rw [Finset.mem_filter, Finset.mem_Ioc]
    rw [mem_typicalS] at hn
    subst n
    have hlo : A / p < m := by
      apply (Nat.div_lt_iff_lt_mul hp).mpr
      rw [mul_comm]
      exact hn.1.1.1
    have hhi : m ≤ B / p := by
      apply (Nat.le_div_iff_mul_le hp).mpr
      rw [mul_comm]
      exact hn.1.1.2
    exact ⟨⟨hlo, hhi⟩, (mem_typicalS.mpr
      ⟨⟨lt_of_le_of_lt (Nat.zero_le (A / p)) hlo,
          le_trans hhi (Nat.div_le_self B p)⟩,
        (hstable m).mp hn.1.2⟩)⟩
  · intro hm
    rw [Finset.mem_filter, Finset.mem_Ioc] at hm
    rw [mem_typicalS] at hm
    rw [Finset.mem_image]
    refine ⟨p * m, ?_, Nat.mul_div_cancel_left m hp⟩
    rw [Finset.mem_filter, mem_typicalS]
    have hlo : A < p * m := by
      have := (Nat.div_lt_iff_lt_mul hp).mp hm.1.1
      simpa [mul_comm] using this
    have hhi : p * m ≤ B := by
      have := (Nat.le_div_iff_mul_le hp).mp hm.1.2
      simpa [mul_comm] using this
    exact ⟨⟨⟨hlo, hhi⟩, (hstable m).mpr hm.2.2⟩, dvd_mul_right p m⟩

/-- Under the same stability condition, the full quotient image carries the
fixed zero-extended Ramaré coefficient. -/
theorem typicalS_full_fibre_eq_block
    (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ)) (p : ℕ) (hp : 0 < p)
    (hstable : ∀ m, HasFactorInAll rest (p * m) ↔ HasFactorInAll rest m)
    (xi : ℝ) :
    (∑ m ∈ ((typicalS A B rest).filter (fun n => p ∣ n)).image (· / p),
        ((g m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
          / (((P.filter (· ∣ m)).card : ℂ) + 1))
      = ∑ m ∈ Finset.Ioc (A / p) (B / p),
          (typicalSQuotCoeff g P (typicalS 0 B rest) m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ) := by
  classical
  rw [typicalS_fibre_image_eq_quotient_support A B p hp rest hstable,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : m ∈ typicalS 0 B rest
  · simp only [hm, if_true, typicalSQuotCoeff]
    ring
  · simp [hm, typicalSQuotCoeff]

/-- The `p ∣ m` terms added when a noncollision fibre is enlarged to its full
quotient support, grouped over the same e-adic cells as the main term. -/
noncomputable def typicalSAddedTerms (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) (xi : ℝ) : ℂ :=
  ∑ v ∈ Finset.Ico v₀ (v₁ + 1), ∑ p ∈ eadicCell P (2 * N) v,
    ((g p / (p : ℂ))
        * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
      * ∑ m ∈ (((typicalS A B rest).filter
          (fun n => p ∣ n)).image (· / p)).filter (fun m => p ∣ m),
        ((g m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
          / (((P.filter (· ∣ m)).card : ℂ) + 1)

open Finset in
/-- **The full-block correction is a weighted collision family.**

The e-adic cover is used only to flatten the cell indexing back to `P`.
After that, every compensating fibre has the same outer harmonic weight and
twice-extracted support as the original repeated-prime term.
-/
theorem typicalSAddedTerms_eq_weighted_quotient_sum
    (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (rest : List (Finset ℕ))
    (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (xi : ℝ) :
    typicalSAddedTerms g A B P rest N v₀ v₁ xi
      = ∑ p ∈ P, collisionPrimeWeight p xi
          * addedCollisionQuotPoly g A B P rest p xi := by
  classical
  have hdisj : Set.PairwiseDisjoint
      (↑(Finset.Ico v₀ (v₁ + 1)) : Set ℕ) (eadicCell P (2 * N)) :=
    fun v _ w _ hvw => eadicCell_disjoint P (2 * N) hvw
  calc
    typicalSAddedTerms g A B P rest N v₀ v₁ xi
        = ∑ v ∈ Finset.Ico v₀ (v₁ + 1), ∑ p ∈ eadicCell P (2 * N) v,
            collisionPrimeWeight p xi
              * addedCollisionQuotPoly g A B P rest p xi := by
          unfold typicalSAddedTerms
          refine Finset.sum_congr rfl fun v _ => ?_
          refine Finset.sum_congr rfl fun p hp => ?_
          exact typicalSAddedTerms_fibre_eq_factored g A B P rest
            (hP p (mem_eadicCell.mp hp).1).pos xi
    _ = ∑ p ∈ (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)),
          collisionPrimeWeight p xi
            * addedCollisionQuotPoly g A B P rest p xi :=
      (Finset.sum_biUnion hdisj).symm
    _ = ∑ p ∈ P, collisionPrimeWeight p xi
          * addedCollisionQuotPoly g A B P rest p xi := by rw [hcov]

open MeasureTheory Finset ExpSums in
/-- **The full-block correction costs the same collision envelope.** -/
theorem intervalIntegral_norm_sq_typicalSAddedTerms_le
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (A Delta : ℕ) (hDeltaA : Delta ≤ A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hPA : ∀ p ∈ P, p * p ≤ A)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (T : ℝ) (hT : 0 < T) :
    (∫ xi in (-T)..T,
      ‖typicalSAddedTerms g A (A + Delta) P rest N v₀ v₁ xi‖ ^ 2)
      ≤ collisionEnergyBound A (A + Delta) P rest T := by
  have hweighted := intervalIntegral_norm_sq_freq_weighted_sum_le P
    collisionPrimeWeight (fun p => (1 : ℝ) / (p : ℝ))
    (fun p xi => (norm_collisionPrimeWeight p xi).le)
    continuous_collisionPrimeWeight
    (addedCollisionQuotPoly g A (A + Delta) P rest)
    (continuous_addedCollisionQuotPoly g A (A + Delta) P rest)
    T hT.le
  calc
    (∫ xi in (-T)..T,
      ‖typicalSAddedTerms g A (A + Delta) P rest N v₀ v₁ xi‖ ^ 2)
        = ∫ xi in (-T)..T, ‖∑ p ∈ P, collisionPrimeWeight p xi
            * addedCollisionQuotPoly g A (A + Delta) P rest p xi‖ ^ 2 := by
          apply intervalIntegral.integral_congr
          intro xi _
          exact congrArg (fun z : ℂ => ‖z‖ ^ 2)
            (typicalSAddedTerms_eq_weighted_quotient_sum
              g A (A + Delta) P hP rest N v₀ v₁ hcov xi)
    _ ≤ (∑ p ∈ P, (1 : ℝ) / (p : ℝ))
          * ∑ p ∈ P, ((1 : ℝ) / (p : ℝ))
            * ∫ xi in (-T)..T,
                ‖addedCollisionQuotPoly g A (A + Delta) P rest p xi‖ ^ 2 := hweighted
    _ ≤ (∑ p ∈ P, (1 : ℝ) / (p : ℝ))
          * ∑ p ∈ P, ((1 : ℝ) / (p : ℝ))
            * (((1 : ℝ) / (p : ℝ)) ^ 2
              * (Real.exp Real.pi
                * (T / ((A / (p * p) : ℕ) : ℝ) + 8)
                * ∑ k ∈ collisionQuotSupport
                    (typicalS A (A + Delta) rest) p,
                    (1 : ℝ) / (k : ℝ))) := by
          gcongr with p hpP
          exact intervalIntegral_norm_sq_addedCollisionQuotPoly_le g hg A Delta
            hDeltaA P rest (hP p hpP) (hPA p hpP) T hT
    _ = collisionEnergyBound A (A + Delta) P rest T := rfl

open Finset in
/-- **The N3-f main term in the full block shape consumed by II-2e.**

Enlarge every noncollision quotient fibre by the omitted `p ∣ m` terms.  The
stability hypothesis identifies the enlarged support with
`Ioc (A/p) (B/p)` carrying the single coefficient
`typicalSQuotCoeff g P (typicalS 0 B rest)`.  Subtracting the added terms from
N3-f's repeated-prime term preserves equality, leaving exactly a full
prime-block main term plus one adjusted collision error.
-/
theorem typicalS_phase_eq_eadic_prime_block_add_adjusted_collision
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g)
    (A Delta : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (hstable : ∀ p ∈ P, ∀ m,
      HasFactorInAll rest (p * m) ↔ HasFactorInAll rest m)
    (xi : ℝ) :
    ∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
        * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)
      = (∑ v ∈ Finset.Ico v₀ (v₁ + 1),
          ∑ p ∈ eadicCell P (2 * N) v,
            ((g p / (p : ℂ))
                * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
              * (∑ m ∈ Finset.Ioc (A / p) ((A + Delta) / p),
                  (typicalSQuotCoeff g P (typicalS 0 (A + Delta) rest) m /
                      (m : ℂ))
                    * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)))
        + (typicalSCollision g A (A + Delta) P rest xi
            - typicalSAddedTerms g A (A + Delta) P rest N v₀ v₁ xi) := by
  rw [typicalS_phase_eq_eadic_main_add_collision g hcm A Delta P hP rest N v₀ v₁
    hcov xi]
  have hfull :
      (∑ v ∈ Finset.Ico v₀ (v₁ + 1),
          ∑ p ∈ eadicCell P (2 * N) v,
            ((g p / (p : ℂ))
                * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
              * (∑ m ∈ Finset.Ioc (A / p) ((A + Delta) / p),
                  (typicalSQuotCoeff g P (typicalS 0 (A + Delta) rest) m /
                      (m : ℂ))
                    * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)))
        = (∑ v ∈ Finset.Ico v₀ (v₁ + 1),
            ∑ p ∈ eadicCell P (2 * N) v,
              typicalSMainFibre g A (A + Delta) P rest p xi)
          + typicalSAddedTerms g A (A + Delta) P rest N v₀ v₁ xi := by
    unfold typicalSAddedTerms
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpP := (mem_eadicCell.mp hp).1
    have hp0 := (hP p hpP).pos
    rw [← typicalS_full_fibre_eq_block g A (A + Delta) P rest p hp0
      (hstable p hpP) xi]
    unfold typicalSMainFibre
    rw [← mul_add]
    congr 1
    have hpart := Finset.sum_filter_add_sum_filter_not
      (((typicalS A (A + Delta) rest).filter
        (fun n => p ∣ n)).image (· / p)) (fun m => ¬ p ∣ m)
      (fun m => ((g m / (m : ℂ))
          * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
        / (((P.filter (· ∣ m)).card : ℂ) + 1))
    simpa only [not_not] using hpart.symm
  rw [hfull]
  ring

/-- The full prime-indexed quotient-block main term obtained from N3-f. -/
noncomputable def typicalSPrimeBlock (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) (xi : ℝ) : ℂ :=
  ∑ v ∈ Finset.Ico v₀ (v₁ + 1), ∑ p ∈ eadicCell P (2 * N) v,
    ((g p / (p : ℂ))
        * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
      * (∑ m ∈ Finset.Ioc (A / p) (B / p),
          (typicalSQuotCoeff g P (typicalS 0 B rest) m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))

/-- The adjusted collision: N3-f's repeated-prime term minus the terms added
to make every main fibre a full quotient block. -/
noncomputable def typicalSAdjustedCollision (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) (xi : ℝ) : ℂ :=
  typicalSCollision g A B P rest xi - typicalSAddedTerms g A B P rest N v₀ v₁ xi

/-- The full-block decomposition in named-function form, ready for the energy
lemmas. -/
theorem typicalS_phase_eq_primeBlock_add_adjustedCollision
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g)
    (A Delta : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (hstable : ∀ p ∈ P, ∀ m,
      HasFactorInAll rest (p * m) ↔ HasFactorInAll rest m)
    (xi : ℝ) :
    ∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
        * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)
      = typicalSPrimeBlock g A (A + Delta) P rest N v₀ v₁ xi
        + typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁ xi := by
  simpa [typicalSPrimeBlock, typicalSAdjustedCollision] using
    typicalS_phase_eq_eadic_prime_block_add_adjusted_collision
      g hcm A Delta P hP rest N v₀ v₁ hcov hstable xi

/-- The full prime-block main term is continuous in frequency. -/
theorem continuous_typicalSPrimeBlock (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) :
    Continuous (typicalSPrimeBlock g A B P rest N v₀ v₁) := by
  classical
  have hchar : ∀ w : ℝ, Continuous fun xi : ℝ =>
      ((Real.fourierChar (-(w * xi)) : Circle) : ℂ) := fun w =>
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  unfold typicalSPrimeBlock
  refine continuous_finset_sum _ fun v _ => ?_
  refine continuous_finset_sum _ fun p _ => ?_
  refine (continuous_const.mul (hchar (Real.log p))).mul ?_
  exact continuous_finset_sum _ fun m _ =>
    continuous_const.mul (hchar (Real.log m))

/-- The adjusted collision is continuous in frequency. -/
theorem continuous_typicalSAdjustedCollision (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) :
    Continuous (typicalSAdjustedCollision g A B P rest N v₀ v₁) := by
  classical
  have hchar : ∀ w : ℝ, Continuous fun xi : ℝ =>
      ((Real.fourierChar (-(w * xi)) : Circle) : ℂ) := fun w =>
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  unfold typicalSAdjustedCollision typicalSCollision typicalSAddedTerms
  apply Continuous.sub
  · refine continuous_finset_sum _ fun p _ => ?_
    refine continuous_finset_sum _ fun m _ => ?_
    exact (continuous_const.mul (hchar (Real.log (p * m : ℕ)))).div_const _
  · refine continuous_finset_sum _ fun v _ => ?_
    refine continuous_finset_sum _ fun p _ => ?_
    refine (continuous_const.mul (hchar (Real.log p))).mul ?_
    refine continuous_finset_sum _ fun m _ => ?_
    exact (continuous_const.mul (hchar (Real.log m))).div_const _

/-- The original repeated-prime term is continuous in frequency. -/
theorem continuous_typicalSCollision (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) :
    Continuous (typicalSCollision g A B P rest) := by
  classical
  unfold typicalSCollision
  refine continuous_finset_sum _ fun p _ => ?_
  refine continuous_finset_sum _ fun m _ => ?_
  exact (continuous_const.mul (continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp (by fun_prop)))).div_const _

/-- The compensating full-block terms are continuous in frequency. -/
theorem continuous_typicalSAddedTerms (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) :
    Continuous (typicalSAddedTerms g A B P rest N v₀ v₁) := by
  classical
  unfold typicalSAddedTerms
  refine continuous_finset_sum _ fun v _ => ?_
  refine continuous_finset_sum _ fun p _ => ?_
  refine (continuous_const.mul (continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp (by fun_prop)))).mul ?_
  refine continuous_finset_sum _ fun m _ => ?_
  exact (continuous_const.mul (continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp (by fun_prop)))).div_const _

open MeasureTheory ExpSums in
/-- **The adjusted collision has four times the explicit collision envelope.**

Completing the quotient blocks replaces the original repeated-prime term by
its difference with the compensating family.  Both halves have the same
weighted quotient-scale bound, so one `L²` triangle costs exactly four copies
of `collisionEnergyBound`.
-/
theorem intervalIntegral_norm_sq_typicalSAdjustedCollision_le
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (A Delta : ℕ) (hDeltaA : Delta ≤ A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hPA : ∀ p ∈ P, p * p ≤ A)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (T : ℝ) (hT : 0 < T) :
    (∫ xi in (-T)..T,
      ‖typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁ xi‖ ^ 2)
      ≤ 4 * collisionEnergyBound A (A + Delta) P rest T := by
  let F := typicalSCollision g A (A + Delta) P rest
  let E := typicalSAddedTerms g A (A + Delta) P rest N v₀ v₁
  have hsplit := intervalIntegral_norm_add_sq_le F (fun xi => -E xi)
    (continuous_typicalSCollision g A (A + Delta) P rest)
    (continuous_typicalSAddedTerms g A (A + Delta) P rest N v₀ v₁).neg
    T hT.le
  have hcoll := intervalIntegral_norm_sq_typicalSCollision_le g hg A Delta
    hDeltaA P hP hPA rest T hT
  have hadd := intervalIntegral_norm_sq_typicalSAddedTerms_le g hg A Delta
    hDeltaA P hP hPA rest N v₀ v₁ hcov T hT
  change (∫ xi in (-T)..T, ‖F xi - E xi‖ ^ 2)
      ≤ 4 * collisionEnergyBound A (A + Delta) P rest T
  have hsplit' : (∫ xi in (-T)..T, ‖F xi - E xi‖ ^ 2)
      ≤ 2 * (∫ xi in (-T)..T, ‖F xi‖ ^ 2)
        + 2 * (∫ xi in (-T)..T, ‖E xi‖ ^ 2) := by
    simpa only [sub_eq_add_neg, norm_neg] using hsplit
  change (∫ xi in (-T)..T, ‖F xi‖ ^ 2)
      ≤ collisionEnergyBound A (A + Delta) P rest T at hcoll
  change (∫ xi in (-T)..T, ‖E xi‖ ^ 2)
      ≤ collisionEnergyBound A (A + Delta) P rest T at hadd
  exact hsplit'.trans (by linarith)

open MeasureTheory in
/-- **An explicit collision fit supplies the capstone collision share.**

The level part may be any subset of the enclosing frequency interval.  Thus
the schedule only has to compare eight copies of the weighted collision
envelope with its declared band-budget share: four from completing the block,
and two from the final square split.
-/
theorem typicalSAdjustedCollision_le_budget
    (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (A Delta : ℕ) (hDeltaA : Delta ≤ A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hPA : ∀ p ∈ P, p * p ≤ A)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (T : ℝ) (hT : 0 < T) (G : Set ℝ) (hGT : G ⊆ Set.Ioc (-T) T)
    (kappa c₃ eps rho : ℝ)
    (hfit : 8 * collisionEnergyBound A (A + Delta) P rest T
      ≤ kappa * bandBudget c₃ eps rho) :
    2 * (∫ xi in G,
      ‖typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁ xi‖ ^ 2)
      ≤ kappa * bandBudget c₃ eps rho := by
  have hset := ExpSums.setIntegral_le_intervalIntegral_of_nonneg
    (fun xi => ‖typicalSAdjustedCollision
      g A (A + Delta) P rest N v₀ v₁ xi‖ ^ 2)
    ((continuous_typicalSAdjustedCollision
      g A (A + Delta) P rest N v₀ v₁).norm.pow 2)
    (fun xi => sq_nonneg _)
    T hT.le G hGT
  have hint := intervalIntegral_norm_sq_typicalSAdjustedCollision_le g hg
    A Delta hDeltaA P hP hPA rest N v₀ v₁ hcov T hT
  linarith

/-- The cell-uniform main envelope appearing in
`setIntegral_norm_sq_cell_prime_block_le`. -/
noncomputable def cellUniformEnergyBound (v₀ v₁ : ℕ) (q : ℕ → ℕ)
    (A B R : ℕ) (c : ℕ → ℂ) (T : ℝ)
    (small : ℕ → ℝ) : ℝ :=
  ((Finset.Ico v₀ (v₁ + 1)).card : ℝ)
    * ∑ v ∈ Finset.Ico v₀ (v₁ + 1), (small v) ^ 2
      * (Real.exp Real.pi * (T / ((A / q v : ℕ) : ℝ) + 4 * (R : ℝ))
        * ∑ m ∈ Finset.Ioc (A / q v) (B / q v), ‖c m‖ ^ 2 / (m : ℝ))

/-- The cell-replacement collar envelope appearing in
`setIntegral_norm_sq_cell_prime_block_le`. -/
noncomputable def cellReplacementEnergyBound (P : Finset ℕ)
    (N v₀ v₁ A B : ℕ) (T : ℝ) : ℝ :=
  ((Finset.Ico v₀ (v₁ + 1)).card : ℝ)
    * ∑ v ∈ Finset.Ico v₀ (v₁ + 1),
      (∑ p ∈ eadicCell P (2 * N) v, (1 : ℝ) / (p : ℝ))
        * ∑ p ∈ eadicCell P (2 * N) v, ((1 : ℝ) / (p : ℝ))
          * (2 * (Real.exp Real.pi * (T / ((A / p : ℕ) : ℝ) + 4)
              * (((A / (N * p) + 1 : ℕ) : ℝ) / ((A / p : ℕ) : ℝ)))
            + 2 * (Real.exp Real.pi * (T / ((B / p : ℕ) : ℝ) + 4)
              * (((B / (N * p) + 1 : ℕ) : ℝ) / ((B / p : ℕ) : ℝ))))

open MeasureTheory Finset ExpSums in
/-- **The typical-set level energy after cell-uniform replacement.**

The exact full-block N3-f decomposition is followed by the existing II-2e
cell-uniform estimate.  Two `L²` triangles are paid: the outer split between
the full main and adjusted collision, and the inner split between the
cell-uniform main and its endpoint collars.  Hence the final coefficients are
`4`, `4`, and `2`, with no hidden constants.
-/
theorem setIntegral_norm_sq_typicalS_le_cell_uniform_add_errors
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta R : ℕ) (hR : 1 ≤ R) (hB : A + Delta ≤ R * A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) (hN : 0 < N)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (hstable : ∀ p ∈ P, ∀ m,
      HasFactorInAll rest (p * m) ↔ HasFactorInAll rest m)
    (q : ℕ → ℕ)
    (hqcell : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), q v ∈ eadicCell P (2 * N) v)
    (hq1 : ∀ v, 1 ≤ q v) (hqA : ∀ v, q v ≤ A)
    (hqmin : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, q v ≤ p)
    (hLA : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, A / (N * p) + 1 ≤ A / p)
    (hLB : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v,
        (A + Delta) / (N * p) + 1 ≤ (A + Delta) / p)
    (T : ℝ) (hT : 0 < T) (G : Set ℝ) (hGm : MeasurableSet G)
    (hGT : G ⊆ Set.Ioc (-T) T) (small : ℕ → ℝ)
    (hsmall : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), ∀ xi ∈ G,
      ‖levelCellPoly P N v g xi‖ ≤ small v) :
    (∫ xi in G, ‖∑ m ∈ typicalS A (A + Delta) (P :: rest),
        (g m / (m : ℂ))
          * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
      ≤ 4 * cellUniformEnergyBound v₀ v₁ q A (A + Delta) R
            (typicalSQuotCoeff g P (typicalS 0 (A + Delta) rest)) T small
        + 4 * cellReplacementEnergyBound P N v₀ v₁ A (A + Delta) T
        + 2 * (∫ xi in G,
            ‖typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁ xi‖ ^ 2) := by
  let c := typicalSQuotCoeff g P (typicalS 0 (A + Delta) rest)
  have hblock := setIntegral_norm_sq_cell_prime_block_le P N v₀ v₁ hN q
    A (A + Delta) R hR (by omega) hB hqcell hq1 hqA hqmin hLA hLB
    g c hg (norm_typicalSQuotCoeff_le_one g hg P (typicalS 0 (A + Delta) rest))
    T hT G hGm hGT small (by simpa [levelCellPoly] using hsmall)
  have hblock' : (∫ xi in G,
      ‖typicalSPrimeBlock g A (A + Delta) P rest N v₀ v₁ xi‖ ^ 2)
      ≤ 2 * cellUniformEnergyBound v₀ v₁ q A (A + Delta) R c T small
        + 2 * cellReplacementEnergyBound P N v₀ v₁ A (A + Delta) T := by
    simpa [typicalSPrimeBlock, cellUniformEnergyBound,
      cellReplacementEnergyBound, c] using hblock
  have hsplit : (∫ xi in G, ‖∑ m ∈ typicalS A (A + Delta) (P :: rest),
        (g m / (m : ℂ))
          * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
      ≤ 2 * (∫ xi in G,
          ‖typicalSPrimeBlock g A (A + Delta) P rest N v₀ v₁ xi‖ ^ 2)
        + 2 * (∫ xi in G,
          ‖typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁ xi‖ ^ 2) := by
    calc
      (∫ xi in G, ‖∑ m ∈ typicalS A (A + Delta) (P :: rest),
          (g m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
        = ∫ xi in G, ‖typicalSPrimeBlock g A (A + Delta) P rest N v₀ v₁ xi
            + typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁ xi‖ ^ 2 := by
          apply setIntegral_congr_fun hGm
          intro xi _
          exact congrArg (· ^ 2) (congrArg norm
            (typicalS_phase_eq_primeBlock_add_adjustedCollision
              g hcm A Delta P hP rest N v₀ v₁ hcov hstable xi))
      _ ≤ _ := setIntegral_norm_add_sq_le _ _
        (continuous_typicalSPrimeBlock g A (A + Delta) P rest N v₀ v₁)
        (continuous_typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁)
        T G hGm hGT
  calc
    (∫ xi in G, ‖∑ m ∈ typicalS A (A + Delta) (P :: rest),
        (g m / (m : ℂ))
          * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
      ≤ 2 * (∫ xi in G,
          ‖typicalSPrimeBlock g A (A + Delta) P rest N v₀ v₁ xi‖ ^ 2)
        + 2 * (∫ xi in G,
          ‖typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁ xi‖ ^ 2) := hsplit
    _ ≤ 2 * (2 * cellUniformEnergyBound v₀ v₁ q A (A + Delta) R c T small
          + 2 * cellReplacementEnergyBound P N v₀ v₁ A (A + Delta) T)
        + 2 * (∫ xi in G,
          ‖typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁ xi‖ ^ 2) := by
      gcongr
    _ = _ := by
      dsimp [c]
      ring

/-- The cell-uniform main function obtained by replacing every quotient block
in a cell by the block at its representative `q v`. -/
noncomputable def typicalSCellUniformMain (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (q : ℕ → ℕ) (xi : ℝ) : ℂ :=
  ∑ v ∈ Finset.Ico v₀ (v₁ + 1),
    levelCellPoly P N v g xi
      * (∑ m ∈ Finset.Ioc (A / q v) (B / q v),
          (typicalSQuotCoeff g P (typicalS 0 B rest) m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))

/-- The endpoint-replacement error between every prime's quotient block and
its cell representative's block. -/
noncomputable def typicalSCellReplacement (g : ℕ → ℂ) (A B : ℕ)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (q : ℕ → ℕ) (xi : ℝ) : ℂ :=
  ∑ v ∈ Finset.Ico v₀ (v₁ + 1), ∑ p ∈ eadicCell P (2 * N) v,
    ((g p / (p : ℂ))
        * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
      * ((∑ m ∈ Finset.Ioc (A / p) (B / p),
            (typicalSQuotCoeff g P (typicalS 0 B rest) m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
        - (∑ m ∈ Finset.Ioc (A / q v) (B / q v),
            (typicalSQuotCoeff g P (typicalS 0 B rest) m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)))

/-- The full prime block is exactly its cell-uniform main plus the replacement
error. -/
theorem typicalSPrimeBlock_eq_cellUniform_add_replacement
    (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) (q : ℕ → ℕ) (xi : ℝ) :
    typicalSPrimeBlock g A B P rest N v₀ v₁ xi
      = typicalSCellUniformMain g A B P rest N v₀ v₁ q xi
        + typicalSCellReplacement g A B P rest N v₀ v₁ q xi := by
  classical
  unfold typicalSPrimeBlock typicalSCellUniformMain typicalSCellReplacement levelCellPoly
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- **The final pointwise level decomposition.**

The typical-set polynomial is the cell-uniform main plus a combined error
consisting of the II-2e endpoint replacement and the adjusted N3-f collision.
This is the exact two-term shape consumed by
`typicalS_level_leg_le_budget_of_decomposition`.
-/
theorem typicalS_phase_eq_cellUniform_add_errors
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g)
    (A Delta : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (hstable : ∀ p ∈ P, ∀ m,
      HasFactorInAll rest (p * m) ↔ HasFactorInAll rest m)
    (q : ℕ → ℕ) (xi : ℝ) :
    ∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
        * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)
      = typicalSCellUniformMain g A (A + Delta) P rest N v₀ v₁ q xi
        + (typicalSCellReplacement g A (A + Delta) P rest N v₀ v₁ q xi
          + typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁ xi) := by
  rw [typicalS_phase_eq_primeBlock_add_adjustedCollision
    g hcm A Delta P hP rest N v₀ v₁ hcov hstable xi,
    typicalSPrimeBlock_eq_cellUniform_add_replacement]
  ring

/-- The cell-uniform main is continuous in frequency. -/
theorem continuous_typicalSCellUniformMain
    (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ) (rest : List (Finset ℕ))
    (N v₀ v₁ : ℕ) (q : ℕ → ℕ) :
    Continuous (typicalSCellUniformMain g A B P rest N v₀ v₁ q) := by
  classical
  have hchar : ∀ w : ℝ, Continuous fun xi : ℝ =>
      ((Real.fourierChar (-(w * xi)) : Circle) : ℂ) := fun w =>
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  unfold typicalSCellUniformMain levelCellPoly
  refine continuous_finset_sum _ fun v _ => Continuous.mul ?_ ?_
  · exact continuous_finset_sum _ fun p _ =>
      continuous_const.mul (hchar (Real.log p))
  · exact continuous_finset_sum _ fun m _ =>
      continuous_const.mul (hchar (Real.log m))

/-- The cell-replacement error is continuous in frequency. -/
theorem continuous_typicalSCellReplacement
    (g : ℕ → ℂ) (A B : ℕ) (P : Finset ℕ) (rest : List (Finset ℕ))
    (N v₀ v₁ : ℕ) (q : ℕ → ℕ) :
    Continuous (typicalSCellReplacement g A B P rest N v₀ v₁ q) := by
  classical
  have hchar : ∀ w : ℝ, Continuous fun xi : ℝ =>
      ((Real.fourierChar (-(w * xi)) : Circle) : ℂ) := fun w =>
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  unfold typicalSCellReplacement
  refine continuous_finset_sum _ fun v _ => ?_
  refine continuous_finset_sum _ fun p _ => ?_
  refine (continuous_const.mul (hchar (Real.log p))).mul ?_
  apply Continuous.sub
  · exact continuous_finset_sum _ fun m _ =>
      continuous_const.mul (hchar (Real.log m))
  · exact continuous_finset_sum _ fun m _ =>
      continuous_const.mul (hchar (Real.log m))

open MeasureTheory Finset ExpSums in
/-- **The standalone II-2e replacement estimate for the typical quotient
coefficient.**

Each cell is bounded by `intervalIntegral_norm_sq_cell_replace_le`; the cells
are then reassembled over `G` by Cauchy–Schwarz and monotonicity into the
enclosing interval.  The right side is exactly `cellReplacementEnergyBound`,
the expression consumed by `eadic_replacement_error_le_budget`.
-/
theorem setIntegral_norm_sq_typicalSCellReplacement_le
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1) (A B : ℕ) (hAB : A ≤ B)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) (hN : 0 < N)
    (q : ℕ → ℕ)
    (hqcell : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), q v ∈ eadicCell P (2 * N) v)
    (hq1 : ∀ v, 1 ≤ q v)
    (hqmin : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, q v ≤ p)
    (hLA : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, A / (N * p) + 1 ≤ A / p)
    (hLB : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, B / (N * p) + 1 ≤ B / p)
    (T : ℝ) (hT : 0 < T) (G : Set ℝ) (hGm : MeasurableSet G)
    (hGT : G ⊆ Set.Ioc (-T) T) :
    (∫ xi in G, ‖typicalSCellReplacement g A B P rest N v₀ v₁ q xi‖ ^ 2)
      ≤ cellReplacementEnergyBound P N v₀ v₁ A B T := by
  let c := typicalSQuotCoeff g P (typicalS 0 B rest)
  let E : ℕ → ℝ → ℂ := fun v xi =>
    ∑ p ∈ eadicCell P (2 * N) v,
      ((g p / (p : ℂ))
          * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
        * ((∑ m ∈ Finset.Ioc (A / p) (B / p),
              (c m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
          - (∑ m ∈ Finset.Ioc (A / q v) (B / q v),
              (c m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)))
  have hEc : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), Continuous (E v) := by
    intro v _
    have hchar : ∀ w : ℝ, Continuous fun xi : ℝ =>
        ((Real.fourierChar (-(w * xi)) : Circle) : ℂ) := fun w =>
      continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
    refine continuous_finset_sum _ fun p _ => ?_
    refine (continuous_const.mul (hchar (Real.log p))).mul ?_
    apply Continuous.sub <;>
      exact continuous_finset_sum _ fun m _ =>
        continuous_const.mul (hchar (Real.log m))
  have hraw := setIntegral_norm_sq_sum_le_card_mul E
    (Finset.Ico v₀ (v₁ + 1)) hEc T hT.le G hGm hGT
    (fun v => (∑ p ∈ eadicCell P (2 * N) v, (1 : ℝ) / (p : ℝ))
      * ∑ p ∈ eadicCell P (2 * N) v, ((1 : ℝ) / (p : ℝ))
        * (2 * (Real.exp Real.pi * (T / ((A / p : ℕ) : ℝ) + 4)
            * (((A / (N * p) + 1 : ℕ) : ℝ) / ((A / p : ℕ) : ℝ)))
          + 2 * (Real.exp Real.pi * (T / ((B / p : ℕ) : ℝ) + 4)
            * (((B / (N * p) + 1 : ℕ) : ℝ) / ((B / p : ℕ) : ℝ)))))
    (fun v hv => intervalIntegral_norm_sq_cell_replace_le hN
      (hqcell v hv) (hq1 v) (hqmin v hv) A B hAB (hLA v hv) (hLB v hv)
      g c hg (norm_typicalSQuotCoeff_le_one g hg P (typicalS 0 B rest)) T hT)
  simpa [typicalSCellReplacement, cellReplacementEnergyBound, E, c] using hraw

open MeasureTheory in
/-- **The complete capstone-facing level leg, with the three analytic costs
separated.**

The exact decomposition supplies a cell-uniform main, the II-2e endpoint
replacement, and the adjusted repeated-prime collision.  If their square-split
energies cost shares `κ_main`, `κ_replace`, and `κ_collision`, then the two
successive `L²` triangles make the total unweighted cost
`2(κ_main+κ_replace+κ_collision)`.  Multiplying once by `(4H/A)²` and
checking that against `2⁻⁽ʲ⁺¹⁾` gives exactly the `hleg` shape of
`band_energy_typicalS_le`.

`band_energy_level_one_main_le_budget` or the later-level ladder supplies
`hmain`; `setIntegral_norm_sq_typicalSCellReplacement_le` followed by
`eadic_replacement_error_le_budget` supplies `hreplacement`.  The remaining
`hcollision` is deliberately separate because M-10 is a collar theorem, not a
repeated-prime theorem.
-/
theorem typicalS_level_leg_le_budget
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g)
    (A Delta H : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (hstable : ∀ p ∈ P, ∀ m,
      HasFactorInAll rest (p * m) ↔ HasFactorInAll rest m)
    (q : ℕ → ℕ)
    (K₁ K₂ T : ℝ) (J j : ℕ) (Pset : ℕ → Set ℝ)
    (hPset : ∀ i, MeasurableSet (Pset i))
    (hpartT : bandPartOn Pset J {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j
      ⊆ Set.Ioc (-T) T)
    (kappaMain kappaReplacement kappaCollision c₃ eps : ℝ)
    (hc₃ : 0 ≤ c₃)
    (hmain : (∫ xi in bandPartOn Pset J
        {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
          ‖typicalSCellUniformMain g A (A + Delta) P rest N v₀ v₁ q xi‖ ^ 2)
      ≤ kappaMain * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hreplacement : 2 * (∫ xi in bandPartOn Pset J
        {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
          ‖typicalSCellReplacement g A (A + Delta) P rest N v₀ v₁ q xi‖ ^ 2)
      ≤ kappaReplacement * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hcollision : 2 * (∫ xi in bandPartOn Pset J
        {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
          ‖typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁ xi‖ ^ 2)
      ≤ kappaCollision * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hshare : (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (2 * kappaMain + 2 * kappaReplacement + 2 * kappaCollision)
      ≤ (1 : ℝ) / 2 ^ (j + 1)) :
    (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (∫ xi in bandPartOn Pset J
            {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
          ‖∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
      ≤ (1 / 2 ^ (j + 1))
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
  let Gpart := bandPartOn Pset J {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j
  let main := typicalSCellUniformMain g A (A + Delta) P rest N v₀ v₁ q
  let replacement := typicalSCellReplacement g A (A + Delta) P rest N v₀ v₁ q
  let collision := typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁
  have hGpart : MeasurableSet Gpart :=
    bandPartOn_measurableSet Pset hPset J _ (measurableSet_inner_band K₁ K₂) j
  have herror : 2 * (∫ xi in Gpart, ‖replacement xi + collision xi‖ ^ 2)
      ≤ (2 * (kappaReplacement + kappaCollision))
        * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    have hsplit := ExpSums.setIntegral_norm_add_sq_le replacement collision
      (continuous_typicalSCellReplacement g A (A + Delta) P rest N v₀ v₁ q)
      (continuous_typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁)
      T Gpart hGpart hpartT
    change 2 * (∫ xi in Gpart, ‖replacement xi‖ ^ 2)
      ≤ kappaReplacement * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))
      at hreplacement
    change 2 * (∫ xi in Gpart, ‖collision xi‖ ^ 2)
      ≤ kappaCollision * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))
      at hcollision
    linarith
  let F : ℝ → ℂ := fun xi =>
    ∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
      * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)
  let error : ℝ → ℂ := fun xi => replacement xi + collision xi
  have houter : (∫ xi in Gpart, ‖F xi‖ ^ 2)
      ≤ 2 * (∫ xi in Gpart, ‖main xi‖ ^ 2)
        + 2 * (∫ xi in Gpart, ‖error xi‖ ^ 2) := by
    calc
      (∫ xi in Gpart, ‖F xi‖ ^ 2) =
          ∫ xi in Gpart, ‖main xi + error xi‖ ^ 2 := by
            apply setIntegral_congr_fun hGpart
            intro xi _
            exact congrArg (· ^ 2) (congrArg norm
              (typicalS_phase_eq_cellUniform_add_errors
                g hcm A Delta P hP rest N v₀ v₁ hcov hstable q xi))
      _ ≤ _ := ExpSums.setIntegral_norm_add_sq_le main error
        (continuous_typicalSCellUniformMain g A (A + Delta) P rest N v₀ v₁ q)
        ((continuous_typicalSCellReplacement g A (A + Delta) P rest N v₀ v₁ q).add
          (continuous_typicalSAdjustedCollision g A (A + Delta) P rest N v₀ v₁))
        T Gpart hGpart hpartT
  change (∫ xi in Gpart, ‖main xi‖ ^ 2)
      ≤ kappaMain * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) at hmain
  change 2 * (∫ xi in Gpart, ‖error xi‖ ^ 2)
      ≤ 2 * (kappaReplacement + kappaCollision)
        * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) at herror
  have hB0 : 0 ≤ bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) :=
    bandBudget_nonneg c₃ eps _ hc₃ (by positivity)
  have hparts : 2 * (∫ xi in Gpart, ‖main xi‖ ^ 2)
        + 2 * (∫ xi in Gpart, ‖error xi‖ ^ 2)
      ≤ (2 * kappaMain + 2 * kappaReplacement + 2 * kappaCollision)
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
    calc
      2 * (∫ xi in Gpart, ‖main xi‖ ^ 2)
          + 2 * (∫ xi in Gpart, ‖error xi‖ ^ 2)
        ≤ 2 * (kappaMain * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
            + 2 * (kappaReplacement + kappaCollision)
              * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by linarith
      _ = _ := by ring
  change (4 * (H : ℝ) / (A : ℝ)) ^ 2 * (∫ xi in Gpart, ‖F xi‖ ^ 2)
    ≤ (1 / 2 ^ (j + 1)) * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))
  calc
    (4 * (H : ℝ) / (A : ℝ)) ^ 2 * (∫ xi in Gpart, ‖F xi‖ ^ 2)
      ≤ (4 * (H : ℝ) / (A : ℝ)) ^ 2
          * (2 * (∫ xi in Gpart, ‖main xi‖ ^ 2)
            + 2 * (∫ xi in Gpart, ‖error xi‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left houter (sq_nonneg _)
    _ ≤ (4 * (H : ℝ) / (A : ℝ)) ^ 2
          * ((2 * kappaMain + 2 * kappaReplacement + 2 * kappaCollision)
            * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ))) :=
        mul_le_mul_of_nonneg_left hparts (sq_nonneg _)
    _ = ((4 * (H : ℝ) / (A : ℝ)) ^ 2
          * (2 * kappaMain + 2 * kappaReplacement + 2 * kappaCollision))
            * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by ring
    _ ≤ (1 / 2 ^ (j + 1)) * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) :=
      mul_le_mul_of_nonneg_right hshare hB0

open MeasureTheory in
/-- **The capstone level leg with the collision reduced to an explicit fit.**

This is the literal `hleg` conclusion with no collision integral left as a
hypothesis.  The new schedule obligation is numerical:
`8 * collisionEnergyBound ≤ κ_collision * bandBudget`; the factor eight
records the full-block correction and the final error split exactly once.
-/
theorem typicalS_level_leg_le_budget_of_collision_fit
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta H : ℕ) (hDeltaA : Delta ≤ A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hPA : ∀ p ∈ P, p * p ≤ A)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (hstable : ∀ p ∈ P, ∀ m,
      HasFactorInAll rest (p * m) ↔ HasFactorInAll rest m)
    (q : ℕ → ℕ)
    (K₁ K₂ T : ℝ) (hT : 0 < T) (J j : ℕ) (Pset : ℕ → Set ℝ)
    (hPset : ∀ i, MeasurableSet (Pset i))
    (hpartT : bandPartOn Pset J {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j
      ⊆ Set.Ioc (-T) T)
    (kappaMain kappaReplacement kappaCollision c₃ eps : ℝ)
    (hc₃ : 0 ≤ c₃)
    (hmain : (∫ xi in bandPartOn Pset J
        {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
          ‖typicalSCellUniformMain g A (A + Delta) P rest N v₀ v₁ q xi‖ ^ 2)
      ≤ kappaMain * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hreplacement : 2 * (∫ xi in bandPartOn Pset J
        {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
          ‖typicalSCellReplacement g A (A + Delta) P rest N v₀ v₁ q xi‖ ^ 2)
      ≤ kappaReplacement * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hcollisionFit : 8 * collisionEnergyBound A (A + Delta) P rest T
      ≤ kappaCollision * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hshare : (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (2 * kappaMain + 2 * kappaReplacement + 2 * kappaCollision)
      ≤ (1 : ℝ) / 2 ^ (j + 1)) :
    (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (∫ xi in bandPartOn Pset J
            {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
          ‖∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
      ≤ (1 / 2 ^ (j + 1))
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
  apply typicalS_level_leg_le_budget g hcm A Delta H P hP rest N v₀ v₁
    hcov hstable q K₁ K₂ T J j Pset hPset hpartT
    kappaMain kappaReplacement kappaCollision c₃ eps hc₃ hmain hreplacement
  · exact typicalSAdjustedCollision_le_budget g hg A Delta hDeltaA P hP hPA
      rest N v₀ v₁ hcov T hT
      (bandPartOn Pset J {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j)
      hpartT kappaCollision c₃ eps ((Delta : ℝ) / (A : ℝ)) hcollisionFit
  · exact hshare

open MeasureTheory Finset ExpSums in
/-- **The level-one main term meets its schedule share.**

`band_energy_level_one_le` supplies the closed-form energy of the cell-uniform
main term and `levelOne_le_budget` converts that expression to a band-budget
share.  For the Ramaré quotient coefficient the former's coefficient-mass
hypothesis reduces to the displayed harmonic-mass bound: boundedness of `g`
and `1/(ω+1) ≤ 1` are discharged by `typicalSQuotCoeff_mass_le`.
-/
theorem band_energy_level_one_main_le_budget
    (P : Finset ℕ) (N : ℕ) (hN : 0 < N) (v₀ v₁ : ℕ) (q : ℕ → ℕ)
    (A B R : ℕ) (hR : 1 ≤ R) (hB : B ≤ R * A)
    (hq1 : ∀ v, 1 ≤ q v) (hqA : ∀ v, 2 * q v ≤ A)
    (hqcell : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      q v ∈ eadicCell P (2 * N) v)
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1) (S : Finset ℕ)
    (T : ℝ) (hT : 0 < T)
    (G : Set ℝ) (hGm : MeasurableSet G) (hGT : G ⊆ Set.Ioc (-T) T)
    (alpha : ℝ) (hAlpha : 0 < alpha) (hAlpha2 : 2 * alpha < 1)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∑ m ∈ Finset.Ioc (A / q v) (B / q v), (1 : ℝ) / (m : ℝ) ≤ C)
    (hsmall : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), ∀ xi ∈ G,
      ‖levelCellPoly P N v g xi‖
        ≤ Real.exp (-(alpha * (v : ℝ) / ((2 * N : ℕ) : ℝ))))
    (Plo Qhi c₃ eps rho kappa : ℝ)
    (hPlo0 : 0 < Plo) (hQhi0 : 0 < Qhi)
    (htop : (v₁ : ℝ) ≤ 2 * (N : ℝ) * Real.log Qhi)
    (hbot : 2 * (N : ℝ) * Real.log Plo - 1 ≤ (v₀ : ℝ))
    (hfitT : ((Finset.Ico v₀ (v₁ + 1)).card : ℝ)
        * (Real.exp Real.pi * C
          * ((2 * T * Real.exp (1 / ((2 * N : ℕ) : ℝ)) / (A : ℝ))
            * (Qhi ^ (1 - 2 * alpha)
                * Real.exp ((1 - 2 * alpha) / ((2 * N : ℕ) : ℝ)))
            * (((2 * N : ℕ) : ℝ) / (1 - 2 * alpha) + 1)))
      ≤ kappa / 2 * bandBudget c₃ eps rho)
    (hfitP : ((Finset.Ico v₀ (v₁ + 1)).card : ℝ)
        * (Real.exp Real.pi * C
          * (4 * (R : ℝ)
            * (Plo ^ (-(2 * alpha))
                * Real.exp (2 * alpha / ((2 * N : ℕ) : ℝ)))
            * (((2 * N : ℕ) : ℝ) / (2 * alpha) + 1)))
      ≤ kappa / 2 * bandBudget c₃ eps rho) :
    (∫ xi in G, ‖∑ v ∈ Finset.Ico v₀ (v₁ + 1),
        levelCellPoly P N v g xi
          * (∑ m ∈ Finset.Ioc (A / q v) (B / q v),
              (typicalSQuotCoeff g P S m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))‖ ^ 2)
      ≤ kappa * bandBudget c₃ eps rho := by
  have hraw := band_energy_level_one_le P N hN v₀ v₁ q A B R hR hB hq1 hqA
    hqcell g (typicalSQuotCoeff g P S) T hT G hGm hGT alpha hAlpha hAlpha2 C hC0
    (fun v hv => (typicalSQuotCoeff_mass_le g hg P S _ _).trans (hC v hv))
    (by simpa [levelCellPoly] using hsmall)
  exact hraw.trans (levelOne_le_budget N R
    ((Finset.Ico v₀ (v₁ + 1)).card : ℝ) T A C Plo Qhi alpha c₃ eps rho kappa
    hN (by positivity) hC0 hT.le (by
      have hqa := hqA v₀
      have hq := hq1 v₀
      exact_mod_cast (by omega : 0 < A)) hAlpha hAlpha2 hPlo0 hQhi0 v₀ v₁
    htop hbot hfitT hfitP)

open MeasureTheory Finset ExpSums in
/-- **A later-level main term meets its schedule share after fixing the
previous large cell.**

The three existing layers line up without algebraic slack.  M-3 turns the
previous cell threshold into the uniform lower bound
`Qprev⁻ᵝ·exp(-β/(2Nprev))`; III-4 bounds each current cell after borrowing
`ℓ` copies of that previous polynomial; and M-9 sums the current cells and
converts their e-adic smallness into the level endpoints `Plo,Qhi`.

The previous cell index `r` is fixed in this statement.  On a whole
first-index part it is supplied by `exists_prev_cell_large_of_mem_bandPartOn`
and requires the standard further partition by the first offending cell.
-/
theorem band_energy_later_main_le_budget
    (Pcur Pprev : Finset ℕ) (Ncur Nprev r v₁prev : ℕ)
    (hNcur : 0 < Ncur) (hNprev : 0 < Nprev)
    (v₀ v₁ : ℕ) (Sblk : ℕ → Finset ℕ)
    (A' Delta' : ℕ) (hA' : 1 ≤ A') (hDelta' : Delta' ≤ A')
    (hSblk : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      Sblk v ⊆ Finset.Ioc A' (A' + Delta'))
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1) (Sco : Finset ℕ)
    (Pmom : ℕ) (hPmom : 1 ≤ Pmom)
    (hPprev : ∀ p ∈ Pprev, p.Prime)
    (hlo : ∀ p ∈ eadicCell Pprev (2 * Nprev) r, Pmom < p)
    (hhi : ∀ p ∈ eadicCell Pprev (2 * Nprev) r, p ≤ 2 * Pmom)
    (ell : ℕ) (hell : 1 ≤ ell)
    (T : ℝ) (hT : 0 < T)
    (G : Set ℝ) (hGm : MeasurableSet G) (hGT : G ⊆ Set.Ioc (-T) T)
    (alpha beta Plo Qhi Qprev : ℝ)
    (hAlpha : 0 < alpha) (hBeta : 0 ≤ beta)
    (hPlo0 : 0 < Plo) (hPloQhi : Plo ≤ Qhi) (hQprev0 : 0 < Qprev)
    (hr : r ≤ v₁prev)
    (htopPrev : (v₁prev : ℝ) ≤ 2 * (Nprev : ℝ) * Real.log Qprev)
    (hsmall : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), ∀ xi ∈ G,
      ‖levelCellPoly Pcur Ncur v g xi‖
        ≤ Real.exp (-(alpha * (v : ℝ) / ((2 * Ncur : ℕ) : ℝ))))
    (hlargeCell : ∀ xi ∈ G,
      Real.exp (-(beta * (r : ℝ) / ((2 * Nprev : ℕ) : ℝ)))
        ≤ ‖levelCellPoly Pprev Nprev r g xi‖)
    (htop : (v₁ : ℝ) ≤ 2 * (Ncur : ℝ) * Real.log Qhi)
    (hbot : 2 * (Ncur : ℝ) * Real.log Plo - 1 ≤ (v₀ : ℝ))
    (c₃ eps rho kappa : ℝ)
    (hfit : (2 * (Ncur : ℝ) * (Real.log Qhi - Real.log Plo) + 2)
        * ((Plo ^ (-(2 * alpha))
              * Real.exp (2 * alpha / ((2 * Ncur : ℕ) : ℝ))
              * (((2 * Ncur : ℕ) : ℝ) / (2 * alpha) + 1))
            * ((Real.exp Real.pi
                  * (T / ((Pmom ^ ell * A' : ℕ) : ℝ)
                    + 2 * ((2 ^ (ell + 1) : ℕ) : ℝ)))
              * (((Nat.factorial ell : ℝ) ^ 2
                * (((2 ^ (ell + 1) : ℕ) : ℝ) * ((ell : ℝ) + 1)
                  * (∑ p ∈ eadicCell Pprev (2 * Nprev) r,
                      (1 : ℝ) / (p : ℝ)) ^ ell))
                / (Qprev ^ (-beta)
                    * Real.exp (-(beta / ((2 * Nprev : ℕ) : ℝ)))) ^
                      (2 * ell))))
      ≤ kappa * bandBudget c₃ eps rho) :
    (∫ xi in G, ‖∑ v ∈ Finset.Ico v₀ (v₁ + 1),
        levelCellPoly Pcur Ncur v g xi
          * (∑ m ∈ Sblk v,
              (typicalSQuotCoeff g Pcur Sco m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))‖ ^ 2)
      ≤ kappa * bandBudget c₃ eps rho := by
  let large : ℝ := Qprev ^ (-beta)
    * Real.exp (-(beta / ((2 * Nprev : ℕ) : ℝ)))
  let E : ℝ := Real.exp Real.pi
    * (T / ((Pmom ^ ell * A' : ℕ) : ℝ)
      + 2 * ((2 ^ (ell + 1) : ℕ) : ℝ))
  let M : ℝ := (Nat.factorial ell : ℝ) ^ 2
    * (((2 ^ (ell + 1) : ℕ) : ℝ) * ((ell : ℝ) + 1)
      * (∑ p ∈ eadicCell Pprev (2 * Nprev) r, (1 : ℝ) / (p : ℝ)) ^ ell)
  have hlarge0 : 0 < large := by
    dsimp [large]
    positivity
  have hprime : ∀ p ∈ eadicCell Pprev (2 * Nprev) r, p.Prime :=
    fun p hp => hPprev p (mem_eadicCell.mp hp).1
  have hlarge : ∀ xi ∈ G, large ≤
      ‖∑ p ∈ eadicCell Pprev (2 * Nprev) r, (g p / (p : ℂ))
        * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ)‖ := by
    intro xi hxi
    change large ≤ ‖levelCellPoly Pprev Nprev r g xi‖
    exact (levelLargeness_ge Nprev r v₁prev Qprev beta hNprev hBeta hQprev0 hr
      htopPrev).trans (hlargeCell xi hxi)
  have hraw := setIntegral_norm_sq_level_sum_of_prev_large_le
    (eadicCell Pprev (2 * Nprev) r) hprime Pmom hPmom hlo hhi g hg ell hell
    A' Delta' hA' hDelta' (Finset.Ico v₀ (v₁ + 1)) Sblk hSblk
    (typicalSQuotCoeff g Pcur Sco)
    (norm_typicalSQuotCoeff_le_one g hg Pcur Sco)
    (fun v xi => levelCellPoly Pcur Ncur v g xi)
    (fun v _ => ExpSums.continuous_char_poly (eadicCell Pcur (2 * Ncur) v)
      (fun p => g p / (p : ℂ)) (fun p => Real.log p))
    T hT G hGm hGT
    (fun v => Real.exp (-(alpha * (v : ℝ) / ((2 * Ncur : ℕ) : ℝ))))
    large hlarge0 hsmall hlarge
  have hsched : ((Finset.Ico v₀ (v₁ + 1)).card : ℝ)
      * ∑ v ∈ Finset.Ico v₀ (v₁ + 1),
        (Real.exp (-(alpha * (v : ℝ) / ((2 * Ncur : ℕ) : ℝ)))) ^ 2
          / large ^ (2 * ell) * (E * M)
      ≤ kappa * bandBudget c₃ eps rho := by
    apply levelJ_le_budget_eadic Ncur v₀ v₁ ell Plo Qhi alpha large E M
      c₃ eps rho kappa hNcur hAlpha hPlo0 hPloQhi hlarge0
      (by dsimp [E]; positivity) (by dsimp [M]; positivity) htop hbot
    simpa [large, E, M] using hfit
  exact hraw.trans (by simpa [E, M] using hsched)

open MeasureTheory in
/-- **A decomposed level leg meets its weighted budget share.**

If `F = main + error` on the level part, the main energy costs twice its
declared share and the already square-split error costs its declared share.
Multiplication by the window supremum `Cw` is postponed to this final join, so
the unweighted level estimates keep their native statements.  The single
numerical condition `Cw * (2κ_main + κ_error) ≤ κ` records all bookkeeping.

The `error` slot is intentionally the *combined* replacement and collision
term.  The collar estimate M-10 can price the replacement component, while the
repeated-prime component needs its own collision estimate.
-/
theorem setIntegral_norm_sq_decomp_le_budget
    (F main error : ℝ → ℂ) (hmainc : Continuous main)
    (herrorc : Continuous error) (T : ℝ)
    (G : Set ℝ) (hGm : MeasurableSet G) (hGT : G ⊆ Set.Ioc (-T) T)
    (hdecomp : ∀ xi ∈ G, F xi = main xi + error xi)
    (Cw kappaMain kappaError kappa c₃ eps rho : ℝ)
    (hCw : 0 ≤ Cw) (hc₃ : 0 ≤ c₃) (hrho : 0 ≤ rho)
    (hmain : (∫ xi in G, ‖main xi‖ ^ 2)
      ≤ kappaMain * bandBudget c₃ eps rho)
    (herror : 2 * (∫ xi in G, ‖error xi‖ ^ 2)
      ≤ kappaError * bandBudget c₃ eps rho)
    (hshare : Cw * (2 * kappaMain + kappaError) ≤ kappa) :
    Cw * (∫ xi in G, ‖F xi‖ ^ 2)
      ≤ kappa * bandBudget c₃ eps rho := by
  have hB0 : 0 ≤ bandBudget c₃ eps rho :=
    bandBudget_nonneg c₃ eps rho hc₃ hrho
  have hsplit : (∫ xi in G, ‖F xi‖ ^ 2)
      ≤ 2 * (∫ xi in G, ‖main xi‖ ^ 2)
        + 2 * (∫ xi in G, ‖error xi‖ ^ 2) := by
    calc
      (∫ xi in G, ‖F xi‖ ^ 2) =
          ∫ xi in G, ‖main xi + error xi‖ ^ 2 := by
            apply setIntegral_congr_fun hGm
            intro xi hxi
            exact congrArg (· ^ 2) (congrArg norm (hdecomp xi hxi))
      _ ≤ 2 * (∫ xi in G, ‖main xi‖ ^ 2)
          + 2 * (∫ xi in G, ‖error xi‖ ^ 2) :=
        ExpSums.setIntegral_norm_add_sq_le main error hmainc herrorc T G hGm hGT
  have hparts : 2 * (∫ xi in G, ‖main xi‖ ^ 2)
        + 2 * (∫ xi in G, ‖error xi‖ ^ 2)
      ≤ (2 * kappaMain + kappaError) * bandBudget c₃ eps rho := by
    calc
      2 * (∫ xi in G, ‖main xi‖ ^ 2)
          + 2 * (∫ xi in G, ‖error xi‖ ^ 2)
        ≤ 2 * (kappaMain * bandBudget c₃ eps rho)
            + kappaError * bandBudget c₃ eps rho := by linarith
      _ = (2 * kappaMain + kappaError) * bandBudget c₃ eps rho := by ring
  calc
    Cw * (∫ xi in G, ‖F xi‖ ^ 2)
      ≤ Cw * (2 * (∫ xi in G, ‖main xi‖ ^ 2)
          + 2 * (∫ xi in G, ‖error xi‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hsplit hCw
    _ ≤ Cw * ((2 * kappaMain + kappaError)
          * bandBudget c₃ eps rho) :=
        mul_le_mul_of_nonneg_left hparts hCw
    _ = (Cw * (2 * kappaMain + kappaError))
          * bandBudget c₃ eps rho := by ring
    _ ≤ kappa * bandBudget c₃ eps rho :=
      mul_le_mul_of_nonneg_right hshare hB0

open MeasureTheory in
/-- **The capstone-facing level leg for the typical-set polynomial.**

This is the literal `hleg` shape required by `band_energy_typicalS_le`, at the
geometric share `2⁻⁽ʲ⁺¹⁾`.  A caller supplies a pointwise decomposition of
the typical-set polynomial into the cell/block main term and one combined
error.  The level-one main hypothesis is produced by
`band_energy_level_one_main_le_budget`; for later levels it is produced by
`band_energy_later_main_le_budget` after fixing the previous offending cell.
The error hypothesis is already square-split, matching the conclusion of the
collar and collision estimates.
-/
theorem typicalS_level_leg_le_budget_of_decomposition
    (g : ℕ → ℂ) (A Delta H : ℕ) (levels : List (Finset ℕ))
    (K₁ K₂ T : ℝ) (J j : ℕ) (Pset : ℕ → Set ℝ)
    (hPset : ∀ i, MeasurableSet (Pset i))
    (hpartT : bandPartOn Pset J {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j
      ⊆ Set.Ioc (-T) T)
    (main error : ℝ → ℂ) (hmainc : Continuous main)
    (herrorc : Continuous error)
    (hdecomp : ∀ xi ∈
      bandPartOn Pset J {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
      (∑ m ∈ typicalS A (A + Delta) levels, (g m / (m : ℂ))
          * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
        = main xi + error xi)
    (kappaMain kappaError c₃ eps : ℝ) (hc₃ : 0 ≤ c₃)
    (hmain : (∫ xi in bandPartOn Pset J
        {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j, ‖main xi‖ ^ 2)
      ≤ kappaMain * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (herror : 2 * (∫ xi in bandPartOn Pset J
        {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j, ‖error xi‖ ^ 2)
      ≤ kappaError * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)))
    (hshare : (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (2 * kappaMain + kappaError) ≤ (1 : ℝ) / 2 ^ (j + 1)) :
    (4 * (H : ℝ) / (A : ℝ)) ^ 2
        * (∫ xi in bandPartOn Pset J
            {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j,
          ‖∑ m ∈ typicalS A (A + Delta) levels, (g m / (m : ℂ))
            * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
      ≤ (1 / 2 ^ (j + 1))
          * bandBudget c₃ eps ((Delta : ℝ) / (A : ℝ)) := by
  let G : Set ℝ :=
    bandPartOn Pset J {xi : ℝ | K₁ ≤ |xi| ∧ |xi| ≤ K₂} j
  have hGm : MeasurableSet G :=
    bandPartOn_measurableSet Pset hPset J _ (measurableSet_inner_band K₁ K₂) j
  exact setIntegral_norm_sq_decomp_le_budget
    (fun xi => ∑ m ∈ typicalS A (A + Delta) levels, (g m / (m : ℂ))
      * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
    main error hmainc herrorc T G hGm hpartT hdecomp
    ((4 * (H : ℝ) / (A : ℝ)) ^ 2) kappaMain kappaError
    ((1 : ℝ) / 2 ^ (j + 1)) c₃ eps ((Delta : ℝ) / (A : ℝ))
    (sq_nonneg _) hc₃ (by positivity) hmain herror hshare

/-- The frequencies where every cell polynomial of level `j` meets its
schedule threshold. -/
noncomputable def levelSmallSet (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ)
    (g : ℕ → ℂ) (alpha : ℕ → ℝ) (j : ℕ) : Set ℝ :=
  {xi | ∀ v ∈ Finset.Ico (v₀ j) (v₁ j + 1),
    ‖levelCellPoly (P j) (N j) v g xi‖
      ≤ Real.exp (-(alpha j * (v : ℝ) / ((2 * N j : ℕ) : ℝ)))}

@[simp] theorem mem_levelSmallSet
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (j : ℕ) (xi : ℝ) :
    xi ∈ levelSmallSet P N v₀ v₁ g alpha j ↔
      ∀ v ∈ Finset.Ico (v₀ j) (v₁ j + 1),
        ‖levelCellPoly (P j) (N j) v g xi‖
          ≤ Real.exp (-(alpha j * (v : ℝ) / ((2 * N j : ℕ) : ℝ))) :=
  Iff.rfl

/-- The level small-value sets are measurable. -/
theorem levelSmallSet_measurableSet
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (j : ℕ) :
    MeasurableSet (levelSmallSet P N v₀ v₁ g alpha j) := by
  classical
  rw [show levelSmallSet P N v₀ v₁ g alpha j =
      ⋂ v ∈ Finset.Ico (v₀ j) (v₁ j + 1),
        {xi : ℝ | ‖levelCellPoly (P j) (N j) v g xi‖
          ≤ Real.exp (-(alpha j * (v : ℝ) / ((2 * N j : ℕ) : ℝ)))} by
    ext xi
    simp]
  refine Finset.measurableSet_biInter _ fun v _ =>
    measurableSet_le ?_ measurable_const
  exact (ExpSums.continuous_char_poly (eadicCell (P j) (2 * N j) v)
    (fun p => g p / (p : ℂ)) (fun p => Real.log p)).norm.measurable

/-- On a nonexceptional first-index part, the current level is small in every
cell. -/
theorem levelSmallSet_small_of_mem_bandPartOn
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (J j : ℕ) (G : Set ℝ) (xi : ℝ)
    (hjJ : j < J)
    (hxi : xi ∈ bandPartOn (levelSmallSet P N v₀ v₁ g alpha) J G j) :
    ∀ v ∈ Finset.Ico (v₀ j) (v₁ j + 1),
      ‖levelCellPoly (P j) (N j) v g xi‖
        ≤ Real.exp (-(alpha j * (v : ℝ) / ((2 * N j : ℕ) : ℝ))) := by
  rw [bandPartOn, bandPart, if_pos hjJ] at hxi
  exact hxi.2.1

/-- On a later first-index part, failure of the previous level's smallness
selects a previous cell whose prime polynomial is large. -/
theorem exists_prev_cell_large_of_mem_bandPartOn
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (J j : ℕ) (G : Set ℝ) (xi : ℝ)
    (hj0 : 0 < j) (hjJ : j < J)
    (hxi : xi ∈ bandPartOn (levelSmallSet P N v₀ v₁ g alpha) J G j) :
    ∃ r ∈ Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1),
      Real.exp (-(alpha (j - 1) * (r : ℝ) /
          ((2 * N (j - 1) : ℕ) : ℝ)))
        < ‖levelCellPoly (P (j - 1)) (N (j - 1)) r g xi‖ := by
  rw [bandPartOn, bandPart, if_pos hjJ] at hxi
  have hprev : xi ∉ levelSmallSet P N v₀ v₁ g alpha (j - 1) := by
    intro h
    exact hxi.2.2 (Set.mem_iUnion₂.mpr
      ⟨j - 1, Finset.mem_range.mpr (by omega), h⟩)
  simp only [levelSmallSet, Set.mem_setOf_eq] at hprev
  push_neg at hprev
  exact hprev

/-! ## Refining a later level by its first large previous cell -/

/-- The frequencies where one specified e-adic cell polynomial exceeds its
schedule threshold. -/
noncomputable def levelLargeSet (P : Finset ℕ) (N v : ℕ) (g : ℕ → ℂ)
    (beta : ℝ) : Set ℝ :=
  {xi | Real.exp (-(beta * (v : ℝ) / ((2 * N : ℕ) : ℝ)))
    < ‖levelCellPoly P N v g xi‖}

/-- A one-cell large-value set is measurable. -/
theorem levelLargeSet_measurableSet (P : Finset ℕ) (N v : ℕ)
    (g : ℕ → ℂ) (beta : ℝ) :
    MeasurableSet (levelLargeSet P N v g beta) := by
  exact measurableSet_lt measurable_const
    (ExpSums.continuous_char_poly (eadicCell P (2 * N) v)
      (fun p => g p / (p : ℂ)) (fun p => Real.log p)).norm.measurable

/-- The part of level `j` assigned to the least previous cell whose estimate
fails.  The `if` makes indices outside the previous level empty. -/
noncomputable def firstPrevLargePart
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (J : ℕ) (G : Set ℝ) (j r : ℕ) : Set ℝ :=
  if _hr : r ∈ Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1) then
    (bandPartOn (levelSmallSet P N v₀ v₁ g alpha) J G j
        ∩ levelLargeSet (P (j - 1)) (N (j - 1)) r g (alpha (j - 1)))
      \ ⋃ s ∈ (Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1)).filter
          (fun s => s < r),
        levelLargeSet (P (j - 1)) (N (j - 1)) s g (alpha (j - 1))
  else ∅

/-- The least-large-cell refinement is measurable whenever the ambient band
is measurable. -/
theorem firstPrevLargePart_measurableSet
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (J : ℕ) (G : Set ℝ) (hG : MeasurableSet G)
    (j r : ℕ) : MeasurableSet (firstPrevLargePart P N v₀ v₁ g alpha J G j r) := by
  classical
  unfold firstPrevLargePart
  split
  · refine ((bandPartOn_measurableSet _
        (levelSmallSet_measurableSet P N v₀ v₁ g alpha) J G hG j).inter
        (levelLargeSet_measurableSet _ _ _ _ _)).diff ?_
    exact MeasurableSet.biUnion
      ((Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1)).filter
        (fun s => s < r)).countable_toSet
      (fun s _ => levelLargeSet_measurableSet _ _ _ _ _)
  · exact MeasurableSet.empty

/-- Each refined part stays inside its original first-index level. -/
theorem firstPrevLargePart_subset_bandPartOn
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (J : ℕ) (G : Set ℝ) (j r : ℕ) :
    firstPrevLargePart P N v₀ v₁ g alpha J G j r ⊆
      bandPartOn (levelSmallSet P N v₀ v₁ g alpha) J G j := by
  classical
  unfold firstPrevLargePart
  split
  · exact fun _ h => h.1.1
  · exact Set.empty_subset _

/-- On the part indexed by `r`, that fixed previous cell is large. -/
theorem firstPrevLargePart_large
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (J : ℕ) (G : Set ℝ) (j r : ℕ)
    (hr : r ∈ Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1))
    {xi : ℝ} (hxi : xi ∈ firstPrevLargePart P N v₀ v₁ g alpha J G j r) :
    Real.exp (-(alpha (j - 1) * (r : ℝ) /
        ((2 * N (j - 1) : ℕ) : ℝ)))
      < ‖levelCellPoly (P (j - 1)) (N (j - 1)) r g xi‖ := by
  rw [firstPrevLargePart, dif_pos hr] at hxi
  exact hxi.1.2

/-- Distinct least-large-cell parts are disjoint. -/
theorem firstPrevLargePart_pairwiseDisjoint
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (J : ℕ) (G : Set ℝ) (j : ℕ) :
    Set.Pairwise
      (↑(Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1)) : Set ℕ)
      (Function.onFun Disjoint (firstPrevLargePart P N v₀ v₁ g alpha J G j)) := by
  classical
  intro r hr s hs hrs
  have hrF : r ∈ Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1) := by
    simpa using hr
  have hsF : s ∈ Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1) := by
    simpa using hs
  change Disjoint
    (firstPrevLargePart P N v₀ v₁ g alpha J G j r)
    (firstPrevLargePart P N v₀ v₁ g alpha J G j s)
  rw [Set.disjoint_left]
  intro xi hxr hxs
  rcases lt_or_gt_of_ne hrs with hrs' | hsr'
  · rw [firstPrevLargePart, dif_pos hsF] at hxs
    exact hxs.2 (Set.mem_iUnion₂.mpr ⟨r,
      Finset.mem_filter.mpr ⟨hrF, hrs'⟩,
      firstPrevLargePart_large P N v₀ v₁ g alpha J G j r hrF hxr⟩)
  · rw [firstPrevLargePart, dif_pos hrF] at hxr
    exact hxr.2 (Set.mem_iUnion₂.mpr ⟨s,
      Finset.mem_filter.mpr ⟨hsF, hsr'⟩,
      firstPrevLargePart_large P N v₀ v₁ g alpha J G j s hsF hxs⟩)

/-- At every later nonexceptional level, the least-large-cell parts cover the
whole first-index part. -/
theorem firstPrevLargePart_cover
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (J : ℕ) (G : Set ℝ) (j : ℕ)
    (hj0 : 0 < j) (hjJ : j < J) :
    bandPartOn (levelSmallSet P N v₀ v₁ g alpha) J G j ⊆
      ⋃ r ∈ Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1),
        firstPrevLargePart P N v₀ v₁ g alpha J G j r := by
  classical
  intro xi hxi
  obtain ⟨r, hr, hlarge⟩ :=
    exists_prev_cell_large_of_mem_bandPartOn P N v₀ v₁ g alpha J j G xi
      hj0 hjJ hxi
  let W := (Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1)).filter
    (fun s => xi ∈ levelLargeSet (P (j - 1)) (N (j - 1)) s g (alpha (j - 1)))
  have hW : W.Nonempty := by
    refine ⟨r, Finset.mem_filter.mpr ⟨hr, ?_⟩⟩
    exact hlarge
  let r₀ := W.min' hW
  have hr₀W : r₀ ∈ W := Finset.min'_mem W hW
  have hr₀ := (Finset.mem_filter.mp hr₀W).1
  have hr₀large := (Finset.mem_filter.mp hr₀W).2
  refine Set.mem_iUnion₂.mpr ⟨r₀, hr₀, ?_⟩
  rw [firstPrevLargePart, dif_pos hr₀]
  refine ⟨⟨hxi, hr₀large⟩, ?_⟩
  intro hsmaller
  obtain ⟨s, hs, hslarge⟩ := Set.mem_iUnion₂.mp hsmaller
  have hsW : s ∈ W := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1, hslarge⟩
  have hr₀s : r₀ ≤ s := Finset.min'_le W s hsW
  exact (Nat.not_lt_of_ge hr₀s) (Finset.mem_filter.mp hs).2

open MeasureTheory in
/-- **Per-previous-cell bounds assemble to a later-level main bound.**

The least-offending-cell refinement is a measurable disjoint cover, so a
continuous nonnegative energy on the full later first-index part is at most the
sum of its energies on the refined parts.  Consequently per-cell shares
`κ_r` cost only `∑_r κ_r`; no cardinality factor is introduced by this
refinement.
-/
theorem setIntegral_norm_sq_later_le_budget_of_firstPrev
    (P : ℕ → Finset ℕ) (N v₀ v₁ : ℕ → ℕ) (g : ℕ → ℂ)
    (alpha : ℕ → ℝ) (J : ℕ) (G : Set ℝ) (hG : MeasurableSet G)
    (j : ℕ) (hj0 : 0 < j) (hjJ : j < J)
    (F : ℝ → ℂ) (hF : Continuous F) (T : ℝ)
    (hpartT : bandPartOn (levelSmallSet P N v₀ v₁ g alpha) J G j
      ⊆ Set.Ioc (-T) T)
    (kappaCell : ℕ → ℝ) (kappa c₃ eps rho : ℝ)
    (hc₃ : 0 ≤ c₃) (hrho : 0 ≤ rho)
    (hcell : ∀ r ∈ Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1),
      (∫ xi in firstPrevLargePart P N v₀ v₁ g alpha J G j r, ‖F xi‖ ^ 2)
        ≤ kappaCell r * bandBudget c₃ eps rho)
    (hshares : ∑ r ∈ Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1),
      kappaCell r ≤ kappa) :
    (∫ xi in bandPartOn (levelSmallSet P N v₀ v₁ g alpha) J G j,
        ‖F xi‖ ^ 2)
      ≤ kappa * bandBudget c₃ eps rho := by
  let I := Finset.Ico (v₀ (j - 1)) (v₁ (j - 1) + 1)
  let part := firstPrevLargePart P N v₀ v₁ g alpha J G j
  have hpartT' : ∀ r ∈ I, part r ⊆ Set.Ioc (-T) T := by
    intro r _
    exact (firstPrevLargePart_subset_bandPartOn P N v₀ v₁ g alpha J G j r).trans
      hpartT
  have hint : ∀ r ∈ I, IntegrableOn (fun xi => ‖F xi‖ ^ 2) (part r) := by
    intro r hr
    exact ((hF.norm.pow 2).integrableOn_Ioc (a := -T) (b := T)).mono_set
      (hpartT' r hr)
  have hcover := firstPrevLargePart_cover P N v₀ v₁ g alpha J G j hj0 hjJ
  have hsplit : (∫ xi in bandPartOn
      (levelSmallSet P N v₀ v₁ g alpha) J G j, ‖F xi‖ ^ 2)
      ≤ ∑ r ∈ I, ∫ xi in part r, ‖F xi‖ ^ 2 := by
    exact ExpSums.setIntegral_le_sum_of_cover (fun xi => ‖F xi‖ ^ 2)
      (fun xi => sq_nonneg ‖F xi‖)
      (bandPartOn (levelSmallSet P N v₀ v₁ g alpha) J G j)
      I part
      (fun r _ => firstPrevLargePart_measurableSet P N v₀ v₁ g alpha J G hG j r)
      (firstPrevLargePart_pairwiseDisjoint P N v₀ v₁ g alpha J G j)
      hcover hint
  have hB0 : 0 ≤ bandBudget c₃ eps rho :=
    bandBudget_nonneg c₃ eps rho hc₃ hrho
  calc
    (∫ xi in bandPartOn (levelSmallSet P N v₀ v₁ g alpha) J G j,
        ‖F xi‖ ^ 2)
      ≤ ∑ r ∈ I, ∫ xi in part r, ‖F xi‖ ^ 2 := hsplit
    _ ≤ ∑ r ∈ I, kappaCell r * bandBudget c₃ eps rho := by
      exact Finset.sum_le_sum fun r hr => hcell r hr
    _ = (∑ r ∈ I, kappaCell r) * bandBudget c₃ eps rho := by
      rw [Finset.sum_mul]
    _ ≤ kappa * bandBudget c₃ eps rho :=
      mul_le_mul_of_nonneg_right hshares hB0

/-! ## The cell-replacement error -/

/-- **M-10 prices the exact e-adic cell-replacement error.**

Specializing `collar_error_le_budget_eadic` to the actual cell family removes
its abstract pairwise-disjointness hypothesis: distinct `eadicCell`s are
disjoint by construction.  The two displayed costs are exactly the endpoint
terms in `setIntegral_norm_sq_cell_prime_block_le`, so the conclusion can be
fed to `setIntegral_norm_sq_decomp_le_budget` without reshaping.

This theorem does not include `typicalSCollision`; that repeated-prime term is
separate in N3-f and needs a collision estimate in addition to M-10.
-/
theorem eadic_replacement_error_le_budget
    (P : Finset ℕ) (N v₀ v₁ A B Pb Kc bb : ℕ) (T X c₃ eps rho kappa : ℝ)
    (aa : ℕ → ℕ)
    (hPb : 1 ≤ Pb) (hKc : 2 ≤ Kc) (hbb : 3 ≤ bb) (hX0 : 0 ≤ X)
    (hcostA : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v,
        Real.exp Real.pi * (T / ((A / p : ℕ) : ℝ) + 4)
            * (((A / (N * p) + 1 : ℕ) : ℝ) / ((A / p : ℕ) : ℝ)) ≤ X)
    (hcostB : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v,
        Real.exp Real.pi * (T / ((B / p : ℕ) : ℝ) + 4)
            * (((B / (N * p) + 1 : ℕ) : ℝ) / ((B / p : ℕ) : ℝ)) ≤ X)
    (haa : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), Pb ≤ aa v)
    (hcell : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      eadicCell P (2 * N) v ⊆
        (Finset.Ioc (aa v) (aa v + Kc)).filter Nat.Prime)
    (hlevel : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      eadicCell P (2 * N) v ⊆ (Finset.Ioc Pb bb).filter Nat.Prime)
    (hkappac : 0 ≤ kappa * c₃) (hrho : eps ≤ rho)
    (hfit : 64 * ((Finset.Ico v₀ (v₁ + 1)).card : ℝ) * X
        * ((256 * (Kc : ℝ) / ((Pb : ℝ) * Real.log Kc))
          * (Real.log (Real.log ((bb : ℝ) + 1)) + 11))
      ≤ kappa * c₃ * eps ^ 3) :
    2 * (((Finset.Ico v₀ (v₁ + 1)).card : ℝ)
      * ∑ v ∈ Finset.Ico v₀ (v₁ + 1),
        (∑ p ∈ eadicCell P (2 * N) v, (1 : ℝ) / (p : ℝ))
          * ∑ p ∈ eadicCell P (2 * N) v, ((1 : ℝ) / (p : ℝ))
            * (2 * (Real.exp Real.pi * (T / ((A / p : ℕ) : ℝ) + 4)
                * (((A / (N * p) + 1 : ℕ) : ℝ) / ((A / p : ℕ) : ℝ)))
              + 2 * (Real.exp Real.pi * (T / ((B / p : ℕ) : ℝ) + 4)
                * (((B / (N * p) + 1 : ℕ) : ℝ) / ((B / p : ℕ) : ℝ)))))
      ≤ kappa * bandBudget c₃ eps rho := by
  apply collar_error_le_budget_eadic
    (Finset.Ico v₀ (v₁ + 1)) (eadicCell P (2 * N))
    (fun p => Real.exp Real.pi * (T / ((A / p : ℕ) : ℝ) + 4)
      * (((A / (N * p) + 1 : ℕ) : ℝ) / ((A / p : ℕ) : ℝ)))
    (fun p => Real.exp Real.pi * (T / ((B / p : ℕ) : ℝ) + 4)
      * (((B / (N * p) + 1 : ℕ) : ℝ) / ((B / p : ℕ) : ℝ)))
    aa Pb Kc bb X c₃ eps rho kappa hPb hKc hbb hX0
    hcostA hcostB haa hcell hlevel
  · intro v _ w _ hvw
    exact eadicCell_disjoint P (2 * N) hvw
  · exact hkappac
  · exact hrho
  · exact hfit

end MoltResearch
