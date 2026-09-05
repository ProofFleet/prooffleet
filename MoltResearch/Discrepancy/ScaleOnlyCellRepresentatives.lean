import MoltResearch.Discrepancy.LevelLegs

/-!
# Scale-only representatives for e-adic cells

The level-one main term only needs an upper scale bound for its quotient
representative.  This leaf records that interface and a representative which
also behaves correctly on empty cells.
-/

namespace MoltResearch

open Finset Set

/-- Quotient-scale conversion from the upper scale bound alone. -/
theorem quotient_scale_le_cell_scale_of_le {N v : ℕ} (hN : 0 < N)
    {q : ℕ}
    (hqup : (q : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ))))
    (hq1 : 1 ≤ q) (A : ℕ) (hqA : 2 * q ≤ A) (T : ℝ) (hT : 0 ≤ T) :
    T / ((A / q : ℕ) : ℝ)
      ≤ 2 * T * Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ))) / (A : ℝ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hmod : ((A % q : ℕ) : ℝ) < (q : ℝ) := by
    exact_mod_cast Nat.mod_lt _ (by omega : 0 < q)
  have hdm : (q : ℝ) * ((A / q : ℕ) : ℝ) + ((A % q : ℕ) : ℝ) = (A : ℝ) := by
    exact_mod_cast Nat.div_add_mod A q
  have hqhalf : 2 * (q : ℝ) ≤ (A : ℝ) := by exact_mod_cast hqA
  have hfloor : (A : ℝ) / (2 * (q : ℝ)) ≤ ((A / q : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hdm, hmod, hqhalf]
  calc
    T / ((A / q : ℕ) : ℝ) ≤ T / ((A : ℝ) / (2 * (q : ℝ))) := by gcongr
    _ = 2 * T * (q : ℝ) / (A : ℝ) := by field_simp
    _ ≤ 2 * T * Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ))) / (A : ℝ) := by
      gcongr

open MeasureTheory Finset ExpSums in
/-- The collar estimate with the exact arithmetic ratio exposed instead of
membership of the representative in the prime set. -/
theorem intervalIntegral_norm_sq_cell_fibre_sub_le_of_ratio
    {N : ℕ} (hN : 0 < N) {p q : ℕ} (hq1 : 1 ≤ q) (hqp : q ≤ p)
    (hratio : N * p ≤ (N + 1) * q)
    (A B : ℕ) (hAB : A ≤ B)
    (hLA : A / (N * p) + 1 ≤ A / p) (hLB : B / (N * p) + 1 ≤ B / p)
    (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (T : ℝ) (hT : 0 < T) :
    (∫ xi in (-T)..T,
        ‖(∑ m ∈ Finset.Ioc (A / p) (B / p),
              (c m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
          - (∑ m ∈ Finset.Ioc (A / q) (B / q),
              (c m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))‖ ^ 2)
      ≤ 2 * (Real.exp Real.pi * (T / ((A / p : ℕ) : ℝ) + 4)
              * (((A / (N * p) + 1 : ℕ) : ℝ) / ((A / p : ℕ) : ℝ)))
        + 2 * (Real.exp Real.pi * (T / ((B / p : ℕ) : ℝ) + 4)
              * (((B / (N * p) + 1 : ℕ) : ℝ) / ((B / p : ℕ) : ℝ))) := by
  have hAq := div_le_div_add_div_add_one A N p q hN hq1 hqp hratio
  have hBq := div_le_div_add_div_add_one B N p q hN hq1 hqp hratio
  have hdivA : A / p ≤ A / q := Nat.div_le_div_left hqp hq1
  have hdivB : B / p ≤ B / q := Nat.div_le_div_left hqp hq1
  have hcolA : A / q ≤ A / p + (A / (N * p) + 1) := by
    rw [← Nat.add_assoc]
    exact hAq
  have hcolB : B / q ≤ B / p + (B / (N * p) + 1) := by
    rw [← Nat.add_assoc]
    exact hBq
  have hA1 : 1 ≤ A / p := le_trans (Nat.le_add_left 1 (A / (N * p))) hLA
  have hB1 : 1 ≤ B / p := le_trans (Nat.le_add_left 1 (B / (N * p))) hLB
  have hminA : min (A / p) (A / q) = A / p := min_eq_left hdivA
  have hminB : min (B / p) (B / q) = B / p := min_eq_left hdivB
  have hmaxA : max (A / p) (A / q) = A / q := max_eq_right hdivA
  have hmaxB : max (B / p) (B / q) = B / q := max_eq_right hdivB
  have hkey := intervalIntegral_norm_sq_window_sub_le
    (A / p) (B / p) (A / q) (B / q) (A / (N * p) + 1) (B / (N * p) + 1)
    (Nat.div_le_div_right hAB) (Nat.div_le_div_right hAB)
    (by rw [hmaxA, hminA]; exact hcolA) (by rw [hmaxB, hminB]; exact hcolB)
    (by rw [hminA]; exact hLA) (by rw [hminB]; exact hLB)
    (by rw [hminA]; exact hA1) (by rw [hminB]; exact hB1)
    c hc T hT
  rwa [hminA, hminB] at hkey

open MeasureTheory Finset ExpSums in
/-- Cell-uniform replacement with an explicit ratio hypothesis.  The ratio is
what controls the collar; an upper scale bound by itself cannot do so. -/
theorem intervalIntegral_norm_sq_cell_replace_le_of_ratio
    {P : Finset ℕ} {N v : ℕ} (hN : 0 < N) {q : ℕ} (hq1 : 1 ≤ q)
    (hqmin : ∀ p ∈ eadicCell P (2 * N) v, q ≤ p)
    (hqratio : ∀ p ∈ eadicCell P (2 * N) v, N * p ≤ (N + 1) * q)
    (A B : ℕ) (hAB : A ≤ B)
    (hLA : ∀ p ∈ eadicCell P (2 * N) v, A / (N * p) + 1 ≤ A / p)
    (hLB : ∀ p ∈ eadicCell P (2 * N) v, B / (N * p) + 1 ≤ B / p)
    (g c : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1)
    (T : ℝ) (hT : 0 < T) :
    (∫ xi in (-T)..T, ‖∑ p ∈ eadicCell P (2 * N) v,
        ((g p / (p : ℂ))
            * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
          * ((∑ m ∈ Finset.Ioc (A / p) (B / p), (c m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
              - (∑ m ∈ Finset.Ioc (A / q) (B / q), (c m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)))‖ ^ 2)
      ≤ (∑ p ∈ eadicCell P (2 * N) v, (1 : ℝ) / (p : ℝ))
          * ∑ p ∈ eadicCell P (2 * N) v, ((1 : ℝ) / (p : ℝ))
              * (2 * (Real.exp Real.pi * (T / ((A / p : ℕ) : ℝ) + 4)
                      * (((A / (N * p) + 1 : ℕ) : ℝ) / ((A / p : ℕ) : ℝ)))
                 + 2 * (Real.exp Real.pi * (T / ((B / p : ℕ) : ℝ) + 4)
                      * (((B / (N * p) + 1 : ℕ) : ℝ) / ((B / p : ℕ) : ℝ)))) := by
  classical
  have hchar : ∀ w : ℝ, Continuous fun xi : ℝ =>
      ((Real.fourierChar (-(w * xi)) : Circle) : ℂ) := fun w =>
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hwbd : ∀ p xi, ‖(g p / (p : ℂ))
      * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ)‖
      ≤ (1 : ℝ) / (p : ℝ) := by
    intro p xi
    rw [norm_mul, norm_eq_of_mem_sphere, mul_one, norm_div, Complex.norm_natCast]
    gcongr
    exact hg p
  have hwcont : ∀ p : ℕ, Continuous fun xi : ℝ =>
      (g p / (p : ℂ))
        * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ) :=
    fun p => continuous_const.mul (hchar (Real.log p))
  have hzcont : ∀ p : ℕ, Continuous fun xi : ℝ =>
      (∑ m ∈ Finset.Ioc (A / p) (B / p), (c m / (m : ℂ))
          * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
        - (∑ m ∈ Finset.Ioc (A / q) (B / q), (c m / (m : ℂ))
          * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)) := by
    intro p
    refine Continuous.sub ?_ ?_ <;>
      exact continuous_finset_sum _ fun m _ =>
        continuous_const.mul (hchar (Real.log m))
  refine le_trans (intervalIntegral_norm_sq_freq_weighted_sum_le
    (eadicCell P (2 * N) v)
    (fun p xi => (g p / (p : ℂ))
      * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
    (fun p => (1 : ℝ) / (p : ℝ)) hwbd hwcont
    (fun p xi =>
      (∑ m ∈ Finset.Ioc (A / p) (B / p), (c m / (m : ℂ))
          * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
        - (∑ m ∈ Finset.Ioc (A / q) (B / q), (c m / (m : ℂ))
          * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)))
    hzcont T hT.le) ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p hp => ?_) ?_
  · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact intervalIntegral_norm_sq_cell_fibre_sub_le_of_ratio hN hq1
      (hqmin p hp) (hqratio p hp) A B hAB (hLA p hp) (hLB p hp) c hc T hT
  · exact Finset.sum_nonneg fun p _ => by positivity

open MeasureTheory Finset ExpSums in
/-- The prime-block decomposition with scale-only representatives.  The
additional arithmetic ratio is exactly what the replacement collars require.
-/
theorem setIntegral_norm_sq_cell_prime_block_le_of_qup
    (P : Finset ℕ) (N v₀ v₁ : ℕ) (hN : 0 < N) (q : ℕ → ℕ)
    (A B R : ℕ) (hR : 1 ≤ R) (hAB : A ≤ B) (hB : B ≤ R * A)
    (hqup : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      (q v : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ))))
    (hq1 : ∀ v, 1 ≤ q v) (hqA : ∀ v, q v ≤ A)
    (hqmin : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, q v ≤ p)
    (hqratio : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, N * p ≤ (N + 1) * q v)
    (hLA : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, A / (N * p) + 1 ≤ A / p)
    (hLB : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, B / (N * p) + 1 ≤ B / p)
    (g c : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1)
    (T : ℝ) (hT : 0 < T)
    (G : Set ℝ) (hGm : MeasurableSet G) (hGT : G ⊆ Set.Ioc (-T) T)
    (s : ℕ → ℝ)
    (hsmall : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), ∀ xi ∈ G,
      ‖∑ p ∈ eadicCell P (2 * N) v, (g p / (p : ℂ))
          * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ)‖ ≤ s v) :
    (∫ xi in G, ‖∑ v ∈ Finset.Ico v₀ (v₁ + 1), ∑ p ∈ eadicCell P (2 * N) v,
        ((g p / (p : ℂ))
            * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
          * (∑ m ∈ Finset.Ioc (A / p) (B / p), (c m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))‖ ^ 2)
      ≤ 2 * (((Finset.Ico v₀ (v₁ + 1)).card : ℝ)
              * ∑ v ∈ Finset.Ico v₀ (v₁ + 1), (s v) ^ 2
                  * (Real.exp Real.pi * (T / ((A / q v : ℕ) : ℝ) + 4 * (R : ℝ))
                      * ∑ m ∈ Finset.Ioc (A / q v) (B / q v),
                          ‖c m‖ ^ 2 / (m : ℝ)))
        + 2 * (((Finset.Ico v₀ (v₁ + 1)).card : ℝ)
              * ∑ v ∈ Finset.Ico v₀ (v₁ + 1),
                  (∑ p ∈ eadicCell P (2 * N) v, (1 : ℝ) / (p : ℝ))
                    * ∑ p ∈ eadicCell P (2 * N) v, ((1 : ℝ) / (p : ℝ))
                        * (2 * (Real.exp Real.pi * (T / ((A / p : ℕ) : ℝ) + 4)
                                * (((A / (N * p) + 1 : ℕ) : ℝ) /
                                  ((A / p : ℕ) : ℝ)))
                           + 2 * (Real.exp Real.pi * (T / ((B / p : ℕ) : ℝ) + 4)
                                * (((B / (N * p) + 1 : ℕ) : ℝ) /
                                  ((B / p : ℕ) : ℝ))))) := by
  classical
  have _hscale := hqup
  have hchar : ∀ w : ℝ, Continuous fun xi : ℝ =>
      ((Real.fourierChar (-(w * xi)) : Circle) : ℂ) := fun w =>
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have key : ∀ xi : ℝ,
      (∑ v ∈ Finset.Ico v₀ (v₁ + 1), ∑ p ∈ eadicCell P (2 * N) v,
        ((g p / (p : ℂ))
            * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
          * (∑ m ∈ Finset.Ioc (A / p) (B / p), (c m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)))
      = (∑ v ∈ Finset.Ico v₀ (v₁ + 1),
            (∑ p ∈ eadicCell P (2 * N) v, (g p / (p : ℂ))
                * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
              * (∑ m ∈ Finset.Ioc (A / q v) (B / q v), (c m / (m : ℂ))
                  * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)))
        + ∑ v ∈ Finset.Ico v₀ (v₁ + 1), ∑ p ∈ eadicCell P (2 * N) v,
            ((g p / (p : ℂ))
                * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
              * ((∑ m ∈ Finset.Ioc (A / p) (B / p), (c m / (m : ℂ))
                    * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
                  - (∑ m ∈ Finset.Ioc (A / q v) (B / q v), (c m / (m : ℂ))
                    * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))) := by
    intro xi
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  have hcell : ∀ v : ℕ, Continuous fun xi : ℝ =>
      ∑ p ∈ eadicCell P (2 * N) v, (g p / (p : ℂ))
        * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ) := fun v =>
    continuous_finset_sum _ fun p _ => continuous_const.mul (hchar (Real.log p))
  have hblk : ∀ n : ℕ, Continuous fun xi : ℝ =>
      ∑ m ∈ Finset.Ioc (A / n) (B / n), (c m / (m : ℂ))
        * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ) := fun n =>
    continuous_finset_sum _ fun m _ => continuous_const.mul (hchar (Real.log m))
  have hMc : Continuous fun xi : ℝ =>
      ∑ v ∈ Finset.Ico v₀ (v₁ + 1),
        (∑ p ∈ eadicCell P (2 * N) v, (g p / (p : ℂ))
            * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
          * (∑ m ∈ Finset.Ioc (A / q v) (B / q v), (c m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)) :=
    continuous_finset_sum _ fun v _ => (hcell v).mul (hblk (q v))
  have hEc : ∀ v : ℕ, Continuous fun xi : ℝ =>
      ∑ p ∈ eadicCell P (2 * N) v,
        ((g p / (p : ℂ))
            * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
          * ((∑ m ∈ Finset.Ioc (A / p) (B / p), (c m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
              - (∑ m ∈ Finset.Ioc (A / q v) (B / q v), (c m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))) :=
    fun v => continuous_finset_sum _ fun p _ =>
      (continuous_const.mul (hchar (Real.log p))).mul ((hblk p).sub (hblk (q v)))
  have hHc : Continuous fun xi : ℝ =>
      ∑ v ∈ Finset.Ico v₀ (v₁ + 1), ∑ p ∈ eadicCell P (2 * N) v,
        ((g p / (p : ℂ))
            * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
          * ((∑ m ∈ Finset.Ioc (A / p) (B / p), (c m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
              - (∑ m ∈ Finset.Ioc (A / q v) (B / q v), (c m / (m : ℂ))
                * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))) :=
    continuous_finset_sum _ fun v _ => hEc v
  calc
    (∫ xi in G, ‖∑ v ∈ Finset.Ico v₀ (v₁ + 1), ∑ p ∈ eadicCell P (2 * N) v,
        ((g p / (p : ℂ))
            * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
          * (∑ m ∈ Finset.Ioc (A / p) (B / p), (c m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))‖ ^ 2)
      = ∫ xi in G, ‖(∑ v ∈ Finset.Ico v₀ (v₁ + 1),
            (∑ p ∈ eadicCell P (2 * N) v, (g p / (p : ℂ))
                * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
              * (∑ m ∈ Finset.Ioc (A / q v) (B / q v), (c m / (m : ℂ))
                  * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)))
          + (∑ v ∈ Finset.Ico v₀ (v₁ + 1), ∑ p ∈ eadicCell P (2 * N) v,
            ((g p / (p : ℂ))
                * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
              * ((∑ m ∈ Finset.Ioc (A / p) (B / p), (c m / (m : ℂ))
                    * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
                  - (∑ m ∈ Finset.Ioc (A / q v) (B / q v), (c m / (m : ℂ))
                    * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))))‖ ^ 2 := by
        simp_rw [key]
    _ ≤ 2 * (∫ xi in G, ‖∑ v ∈ Finset.Ico v₀ (v₁ + 1),
            (∑ p ∈ eadicCell P (2 * N) v, (g p / (p : ℂ))
                * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
              * (∑ m ∈ Finset.Ioc (A / q v) (B / q v), (c m / (m : ℂ))
                  * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))‖ ^ 2)
        + 2 * (∫ xi in G, ‖∑ v ∈ Finset.Ico v₀ (v₁ + 1),
            ∑ p ∈ eadicCell P (2 * N) v,
            ((g p / (p : ℂ))
                * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
              * ((∑ m ∈ Finset.Ioc (A / p) (B / p), (c m / (m : ℂ))
                    * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
                  - (∑ m ∈ Finset.Ioc (A / q v) (B / q v), (c m / (m : ℂ))
                    * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)))‖ ^ 2) :=
        setIntegral_norm_add_sq_le _ _ hMc hHc T G hGm hGT
    _ ≤ 2 * (((Finset.Ico v₀ (v₁ + 1)).card : ℝ)
              * ∑ v ∈ Finset.Ico v₀ (v₁ + 1), (s v) ^ 2
                  * (Real.exp Real.pi * (T / ((A / q v : ℕ) : ℝ) + 4 * (R : ℝ))
                      * ∑ m ∈ Finset.Ioc (A / q v) (B / q v),
                          ‖c m‖ ^ 2 / (m : ℝ)))
        + 2 * (((Finset.Ico v₀ (v₁ + 1)).card : ℝ)
              * ∑ v ∈ Finset.Ico v₀ (v₁ + 1),
                  (∑ p ∈ eadicCell P (2 * N) v, (1 : ℝ) / (p : ℝ))
                    * ∑ p ∈ eadicCell P (2 * N) v, ((1 : ℝ) / (p : ℝ))
                        * (2 * (Real.exp Real.pi * (T / ((A / p : ℕ) : ℝ) + 4)
                                * (((A / (N * p) + 1 : ℕ) : ℝ) /
                                  ((A / p : ℕ) : ℝ)))
                           + 2 * (Real.exp Real.pi * (T / ((B / p : ℕ) : ℝ) + 4)
                                * (((B / (N * p) + 1 : ℕ) : ℝ) /
                                  ((B / p : ℕ) : ℝ))))) := by
        gcongr
        · exact setIntegral_norm_sq_cell_block_sum_le P N v₀ v₁ q A B R hR hB
            hq1 hqA g c T hT G hGm hGT s hsmall
        · exact setIntegral_norm_sq_sum_le_card_mul _ _
            (fun v _ => hEc v) T hT.le G hGm hGT _
            (fun v hv => intervalIntegral_norm_sq_cell_replace_le_of_ratio hN
              (hq1 v) (hqmin v hv) (hqratio v hv) A B hAB
              (hLA v hv) (hLB v hv) g c hg hc T hT)

open MeasureTheory Finset ExpSums in
/-- The typical-set decomposition using a scale-only representative and the
explicit collar-ratio condition. -/
theorem setIntegral_norm_sq_typicalS_le_cell_uniform_add_errors_of_qup
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta R : ℕ) (hR : 1 ≤ R) (hB : A + Delta ≤ R * A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) (hN : 0 < N)
    (hcov : (Finset.Ico v₀ (v₁ + 1)).biUnion (eadicCell P (2 * N)) = P)
    (hstable : ∀ p ∈ P, ∀ m,
      HasFactorInAll rest (p * m) ↔ HasFactorInAll rest m)
    (q : ℕ → ℕ)
    (hqup : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      (q v : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ))))
    (hq1 : ∀ v, 1 ≤ q v) (hqA : ∀ v, q v ≤ A)
    (hqmin : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, q v ≤ p)
    (hqratio : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, N * p ≤ (N + 1) * q v)
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
  have hblock := setIntegral_norm_sq_cell_prime_block_le_of_qup P N v₀ v₁ hN q
    A (A + Delta) R hR (by omega) hB hqup hq1 hqA hqmin hqratio hLA hLB
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

open MeasureTheory Finset ExpSums in
/-- Standalone replacement estimate with scale-only representatives and the
collar-ratio condition made explicit. -/
theorem setIntegral_norm_sq_typicalSCellReplacement_le_of_qup
    (g : ℕ → ℂ) (hg : ∀ m, ‖g m‖ ≤ 1) (A B : ℕ) (hAB : A ≤ B)
    (P : Finset ℕ) (rest : List (Finset ℕ)) (N v₀ v₁ : ℕ) (hN : 0 < N)
    (q : ℕ → ℕ)
    (hqup : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      (q v : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ))))
    (hq1 : ∀ v, 1 ≤ q v)
    (hqmin : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, q v ≤ p)
    (hqratio : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, N * p ≤ (N + 1) * q v)
    (hLA : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, A / (N * p) + 1 ≤ A / p)
    (hLB : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∀ p ∈ eadicCell P (2 * N) v, B / (N * p) + 1 ≤ B / p)
    (T : ℝ) (hT : 0 < T) (G : Set ℝ) (hGm : MeasurableSet G)
    (hGT : G ⊆ Set.Ioc (-T) T) :
    (∫ xi in G, ‖typicalSCellReplacement g A B P rest N v₀ v₁ q xi‖ ^ 2)
      ≤ cellReplacementEnergyBound P N v₀ v₁ A B T := by
  have _hscale := hqup
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
    (fun v hv => intervalIntegral_norm_sq_cell_replace_le_of_ratio hN
      (hq1 v) (hqmin v hv) (hqratio v hv) A B hAB (hLA v hv) (hLB v hv)
      g c hg (norm_typicalSQuotCoeff_le_one g hg P (typicalS 0 B rest)) T hT)
  simpa [typicalSCellReplacement, cellReplacementEnergyBound, E, c] using hraw

open MeasureTheory Finset ExpSums in
/-- The level-one main estimate with an upper scale hypothesis in place of
cell membership for the representative. -/
theorem band_energy_level_one_le_of_qup
    (P : Finset ℕ) (N : ℕ) (hN : 0 < N) (v₀ v₁ : ℕ) (q : ℕ → ℕ)
    (A B R : ℕ) (hR : 1 ≤ R) (hB : B ≤ R * A)
    (hq1 : ∀ v, 1 ≤ q v) (hqA : ∀ v, 2 * q v ≤ A)
    (hqup : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      (q v : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ))))
    (g c : ℕ → ℂ) (T : ℝ) (hT : 0 < T)
    (G : Set ℝ) (hGm : MeasurableSet G) (hGT : G ⊆ Set.Ioc (-T) T)
    (alpha : ℝ) (hAlpha : 0 < alpha) (hAlpha2 : 2 * alpha < 1)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      ∑ m ∈ Finset.Ioc (A / q v) (B / q v), ‖c m‖ ^ 2 / (m : ℝ) ≤ C)
    (hsmall : ∀ v ∈ Finset.Ico v₀ (v₁ + 1), ∀ xi ∈ G,
      ‖∑ p ∈ eadicCell P (2 * N) v, (g p / (p : ℂ))
          * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ)‖
        ≤ Real.exp (-(alpha * (v : ℝ) / ((2 * N : ℕ) : ℝ)))) :
    (∫ xi in G, ‖∑ v ∈ Finset.Ico v₀ (v₁ + 1),
        (∑ p ∈ eadicCell P (2 * N) v, (g p / (p : ℂ))
            * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
          * (∑ m ∈ Finset.Ioc (A / q v) (B / q v), (c m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))‖ ^ 2)
      ≤ ((Finset.Ico v₀ (v₁ + 1)).card : ℝ)
          * (Real.exp Real.pi * C
              * ((2 * T * Real.exp (1 / ((2 * N : ℕ) : ℝ)) / (A : ℝ))
                    * Real.exp ((1 - 2 * alpha) * ((v₁ : ℝ) + 1) /
                      ((2 * N : ℕ) : ℝ))
                    * (((2 * N : ℕ) : ℝ) / (1 - 2 * alpha) + 1)
                + 4 * (R : ℝ) * Real.exp (-(2 * alpha * (v₀ : ℝ) /
                    ((2 * N : ℕ) : ℝ)))
                    * (((2 * N : ℕ) : ℝ) / (2 * alpha) + 1))) := by
  classical
  have hA0 : (0 : ℝ) < A := by
    exact_mod_cast (by
      have hqa := hqA v₀
      have hq := hq1 v₀
      omega : 0 < A)
  have hN2 : 0 < 2 * N := by omega
  have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  refine le_trans (setIntegral_norm_sq_cell_block_sum_le P N v₀ v₁ q
    A B R hR hB hq1 (fun v => le_trans (by omega) (hqA v))
    g c T hT G hGm hGT _ hsmall) ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine le_trans (Finset.sum_le_sum ?_)
    (sum_level_energy_le alpha hAlpha hAlpha2 (2 * N) hN2 v₀ v₁ (A : ℝ)
      (2 * T * Real.exp (1 / ((2 * N : ℕ) : ℝ))) (4 * (R : ℝ)) C hA0
      (by positivity) (by positivity) hC0)
  intro v hv
  have hscale : T / ((A / q v : ℕ) : ℝ)
      ≤ (2 * T * Real.exp (1 / ((2 * N : ℕ) : ℝ)))
          * Real.exp ((v : ℝ) / ((2 * N : ℕ) : ℝ)) / (A : ℝ) := by
    refine le_trans (quotient_scale_le_cell_scale_of_le hN (hqup v hv)
      (hq1 v) A (hqA v) T hT.le) (le_of_eq ?_)
    rw [hcast]
    have hsplit : Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ)))
        = Real.exp (1 / (2 * (N : ℝ)))
            * Real.exp ((v : ℝ) / (2 * (N : ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [div_eq_div_iff (by positivity) (by positivity), hsplit]
    ring
  gcongr
  exact hC v hv

open MeasureTheory Finset ExpSums in
/-- Budget form of `band_energy_level_one_le_of_qup`. -/
theorem band_energy_level_one_main_le_budget_of_qup
    (P : Finset ℕ) (N : ℕ) (hN : 0 < N) (v₀ v₁ : ℕ) (q : ℕ → ℕ)
    (A B R : ℕ) (hR : 1 ≤ R) (hB : B ≤ R * A)
    (hq1 : ∀ v, 1 ≤ q v) (hqA : ∀ v, 2 * q v ≤ A)
    (hqup : ∀ v ∈ Finset.Ico v₀ (v₁ + 1),
      (q v : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ))))
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
  have hraw := band_energy_level_one_le_of_qup P N hN v₀ v₁ q A B R hR hB
    hq1 hqA hqup g (typicalSQuotCoeff g P S) T hT G hGm hGT
    alpha hAlpha hAlpha2 C hC0
    (fun v hv => (typicalSQuotCoeff_mass_le g hg P S _ _).trans (hC v hv))
    (by simpa [levelCellPoly] using hsmall)
  exact hraw.trans (levelOne_le_budget N R
    ((Finset.Ico v₀ (v₁ + 1)).card : ℝ) T A C Plo Qhi alpha c₃ eps rho kappa
    hN (by positivity) hC0 hT.le (by
      have hqa := hqA v₀
      have hq := hq1 v₀
      exact_mod_cast (by omega : 0 < A)) hAlpha hAlpha2 hPlo0 hQhi0 v₀ v₁
    htop hbot hfitT hfitP)

/-- Cell membership supplies the scale-only upper bound. -/
theorem qup_of_mem {P : Finset ℕ} {N v q : ℕ} (hN : 0 < N)
    (hq : q ∈ eadicCell P (2 * N) v) (hq1 : 1 ≤ q) :
    (q : ℝ) ≤ Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ))) := by
  have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  have hub := (eadicCell_bounds (by omega : 0 < 2 * N) hq hq1).2
  rw [hcast] at hub
  exact hub.le

/-- A representative which is the lower-endpoint ceiling on occupied cells
and `1` on empty cells. -/
noncomputable def scaleCellRepresentative (P : Finset ℕ) (N v : ℕ) : ℕ :=
  if (eadicCell P (2 * N) v).Nonempty then
    ⌈Real.exp ((v : ℝ) / (2 * (N : ℝ)))⌉₊
  else 1

/-- The occupied-cell lower-endpoint ceiling lies below every member. -/
theorem ceil_cell_lower_le {P : Finset ℕ} {N v p : ℕ} (hN : 0 < N)
    (hp : p ∈ eadicCell P (2 * N) v) (hp1 : 1 ≤ p) :
    ⌈Real.exp ((v : ℝ) / (2 * (N : ℝ)))⌉₊ ≤ p := by
  apply Nat.ceil_le.mpr
  have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  have hlo := (eadicCell_bounds (by omega : 0 < 2 * N) hp hp1).1
  rw [hcast] at hlo
  exact hlo

/-- The corrected ceiling-or-one representative has the required upper
scale bound, including on empty cells. -/
theorem qup_of_ceil_or_one (P : Finset ℕ) (N v : ℕ) (hN : 0 < N)
    (hP1 : ∀ p ∈ P, 1 ≤ p) :
    (scaleCellRepresentative P N v : ℝ)
      ≤ Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ))) := by
  classical
  by_cases hcell : (eadicCell P (2 * N) v).Nonempty
  · obtain ⟨p, hp⟩ := hcell
    have hp1 : 1 ≤ p := by
      exact hP1 p (mem_eadicCell.mp hp).1
    have hceil := ceil_cell_lower_le hN hp hp1
    have hup := qup_of_mem hN hp hp1
    rw [scaleCellRepresentative, if_pos ⟨p, hp⟩]
    exact (by exact_mod_cast hceil :
      (⌈Real.exp ((v : ℝ) / (2 * (N : ℝ)))⌉₊ : ℝ) ≤ (p : ℝ)).trans hup
  · rw [scaleCellRepresentative, if_neg hcell]
    norm_num only [Nat.cast_one]
    exact Real.one_le_exp (by positivity)

/-- The corrected representative is positive. -/
theorem one_le_scaleCellRepresentative (P : Finset ℕ) (N v : ℕ) :
    1 ≤ scaleCellRepresentative P N v := by
  classical
  rw [scaleCellRepresentative]
  split_ifs
  · exact Nat.one_le_ceil_iff.mpr (Real.exp_pos _)
  · rfl

/-- On any occupied cell, the corrected representative is no larger than a
cell member. -/
theorem scaleCellRepresentative_le_mem {P : Finset ℕ} {N v p : ℕ}
    (hN : 0 < N) (hp : p ∈ eadicCell P (2 * N) v) (hp1 : 1 ≤ p) :
    scaleCellRepresentative P N v ≤ p := by
  classical
  rw [scaleCellRepresentative, if_pos ⟨p, hp⟩]
  exact ceil_cell_lower_le hN hp hp1

/-- A real upper bound on the representative supplies the natural cutoff
needed by quotient blocks. -/
theorem two_mul_scaleCellRepresentative_le {P : Finset ℕ} {N v A : ℕ}
    (hN : 0 < N) (hP1 : ∀ p ∈ P, 1 ≤ p)
    (hA : 2 * Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ))) ≤ (A : ℝ)) :
    2 * scaleCellRepresentative P N v ≤ A := by
  have hq := qup_of_ceil_or_one P N v hN hP1
  exact_mod_cast (mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 2) |>.trans hA)

/-- On an occupied cell the corrected representative has the same
`1 + 1/N` ratio control as a genuine cell member. -/
theorem scaleCellRepresentative_ratio_le {P : Finset ℕ} {N v p : ℕ}
    (hN : 0 < N) (hp : p ∈ eadicCell P (2 * N) v) (hp1 : 1 ≤ p) :
    N * p ≤ (N + 1) * scaleCellRepresentative P N v := by
  classical
  let q := scaleCellRepresentative P N v
  have hne : (eadicCell P (2 * N) v).Nonempty := ⟨p, hp⟩
  have hqdef : q = ⌈Real.exp ((v : ℝ) / (2 * (N : ℝ)))⌉₊ := by
    simp only [q, scaleCellRepresentative, if_pos hne]
  have hqlb : Real.exp ((v : ℝ) / (2 * (N : ℝ))) ≤ (q : ℝ) := by
    rw [hqdef]
    exact Nat.le_ceil _
  have hN2 : 0 < 2 * N := by omega
  have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  have hpub := (eadicCell_bounds hN2 hp hp1).2
  rw [hcast] at hpub
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsplit : ((v : ℝ) + 1) / (2 * (N : ℝ))
      = (v : ℝ) / (2 * (N : ℝ)) + 1 / (2 * (N : ℝ)) := by
    field_simp
  have hx0 : (0 : ℝ) < 1 / (2 * (N : ℝ)) := by positivity
  have hx1 : |1 / (2 * (N : ℝ))| ≤ 1 := by
    rw [abs_of_pos hx0, div_le_one (by positivity)]
    exact_mod_cast (show 1 ≤ 2 * N by omega)
  have hexp : Real.exp (1 / (2 * (N : ℝ))) ≤ 1 + 1 / (N : ℝ) := by
    have habs := Real.abs_exp_sub_one_le hx1
    have h1 := (abs_le.mp habs).2
    rw [abs_of_pos hx0] at h1
    have : (2 : ℝ) * (1 / (2 * (N : ℝ))) = 1 / (N : ℝ) := by field_simp
    linarith
  have hchain : (p : ℝ) < (q : ℝ) * (1 + 1 / (N : ℝ)) := by
    calc
      (p : ℝ) < Real.exp (((v : ℝ) + 1) / (2 * (N : ℝ))) := hpub
      _ = Real.exp ((v : ℝ) / (2 * (N : ℝ)))
          * Real.exp (1 / (2 * (N : ℝ))) := by rw [hsplit, Real.exp_add]
      _ ≤ (q : ℝ) * (1 + 1 / (N : ℝ)) := by
        refine mul_le_mul hqlb hexp (by positivity) ?_
        exact (Real.exp_pos _).le.trans hqlb
  have hfinal : (N : ℝ) * (p : ℝ) < ((N : ℝ) + 1) * (q : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hchain hN0
    calc
      (N : ℝ) * (p : ℝ) < (N : ℝ) * ((q : ℝ) * (1 + 1 / (N : ℝ))) := hmul
      _ = ((N : ℝ) + 1) * (q : ℝ) := by field_simp
  have : N * p < (N + 1) * q := by exact_mod_cast hfinal
  exact this.le

end MoltResearch
