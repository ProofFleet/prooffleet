import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5ExceptionalReCut
import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5BandCapstoneFamily

/-!
# Track C Stage 5 — the high-moment exceptional capstone

This is the VI-9g re-plumbing of the exceptional-frequency energy.  The
integer large-values term is sampled only on cells which meet the exceptional
part, while the prime term uses the high-moment count from VI-9d.  Thus the
two old full-band costs, `#bandCells` and `T / P`, do not occur in the fit.
-/

namespace MoltResearch

namespace Tao2015

open Finset

-- The parity split and the high-moment count are the two expensive pieces of
-- elaboration in this direct mirror of the original maximum-sample theorem.
set_option maxHeartbeats 800000 in
open MeasureTheory in
/-- **Phase 0 VI-9g-1 — maximum-sample exceptional energy after the recut.**

The cover `K` is deliberately arbitrary.  In the capstone below it is the
subfamily of unit cells which actually meets the exceptional part.  The
prime off-diagonal factor is the high-moment cardinality cost, with no
first-moment `T / P` term. -/
theorem setIntegral_band_energy_exceptional_max_le_recut
    [HalaszLargeValuesAssumption] [PrimeLargeValuesAssumption]
    (P : ℕ) (hP : 2 ≤ P) (Y : Finset ℕ) (hY : ∀ p ∈ Y, p.Prime)
    (hlo : ∀ p ∈ Y, P < p) (hhi : ∀ p ∈ Y, p ≤ 2 * P)
    (b : ℕ → ℂ) (hb : ∀ p, ‖b p‖ ≤ 1)
    (ell : ℕ) (hell : 1 ≤ ell)
    (N : ℕ) (a : ℕ → ℂ) (T : ℝ) (hT1 : 1 ≤ T)
    (G : Set ℝ) (K : Finset ℤ)
    (hcover : G ⊆ ⋃ k ∈ K, Set.Ico (k : ℝ) ((k : ℝ) + 1))
    (hKT : ∀ k ∈ K, -T ≤ (k : ℝ) ∧ (k : ℝ) + 1 ≤ T)
    (V₀ delta lam : ℝ) (hV₀ : 0 < V₀) (hlam : 0 < lam)
    (hdelta : ∀ t : ℝ, |t| ≤ T →
      V₀ < ‖∑ p ∈ Y, (b p / (p : ℂ))
          * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖ →
      ‖∑ n ∈ Finset.Icc 1 N, (a n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ delta) :
    (∫ xi in G, ‖∑ p ∈ Y, (b p / (p : ℂ))
            * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ)‖ ^ 2
          * ‖∑ n ∈ Finset.Icc 1 N, (a n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ)‖ ^ 2)
      ≤ 2 * (V₀ ^ 2 * (64 * ((N : ℝ) + (K.card : ℝ) * Real.sqrt T)
                  * (Real.log (2 * T) + 1)
                  * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2)
            + delta ^ 2 * (64 * (1 + primeHighMomentCountCost P ell Y T V₀ lam
                    * Real.exp (-(Real.log P /
                      (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
                    * (Real.log (2 * T)) ^ 2)
                * (∑ p ∈ Y, ‖b p‖ ^ 2 / (p : ℝ) ^ 2)
                * (P : ℝ) / Real.log P)) := by
  classical
  have hT : (0 : ℝ) < T := by linarith
  have hlog2T : (0 : ℝ) ≤ Real.log (2 * T) + 1 := by
    have hlog := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * T)
    linarith
  have hchar : ∀ v : ℝ, Continuous fun xi : ℝ =>
      ((Real.fourierChar (-(v * xi)) : Circle) : ℂ) := fun v =>
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hQc : Continuous fun xi : ℝ => ∑ p ∈ Y, (b p / (p : ℂ))
      * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ) :=
    continuous_finset_sum _ fun p _ => continuous_const.mul (hchar (Real.log p))
  have hRc : Continuous fun xi : ℝ => ∑ n ∈ Finset.Icc 1 N, (a n / (n : ℂ))
      * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ) :=
    continuous_finset_sum _ fun n _ => continuous_const.mul (hchar (Real.log n))
  obtain ⟨tau, htau, hlad⟩ :=
    MoltResearch.setIntegral_norm_sq_mul_le_two_separated_max _ _ hQc hRc G K hcover
  have hTmem : ∀ k ∈ K, |tau k| ≤ T := by
    intro k hk
    obtain ⟨hlo', hhi'⟩ := hKT k hk
    obtain ⟨h1, h2⟩ := htau k hk
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hfam : ∀ K' : Finset ℤ, K' ⊆ K →
      (∀ k ∈ K', ∀ l ∈ K', k ≠ l → k + 2 ≤ l ∨ l + 2 ≤ k) →
      ∑ t ∈ K'.image tau, ‖∑ p ∈ Y, (b p / (p : ℂ))
            * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖ ^ 2
          * ‖∑ n ∈ Finset.Icc 1 N, (a n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ^ 2
        ≤ V₀ ^ 2 * (64 * ((N : ℝ) + (K.card : ℝ) * Real.sqrt T)
                * (Real.log (2 * T) + 1)
                * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2)
          + delta ^ 2 * (64 * (1 + primeHighMomentCountCost P ell Y T V₀ lam
                  * Real.exp (-(Real.log P /
                    (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
                  * (Real.log (2 * T)) ^ 2)
              * (∑ p ∈ Y, ‖b p‖ ^ 2 / (p : ℝ) ^ 2)
              * (P : ℝ) / Real.log P) := by
    intro K' hK'K hgap
    have htau' : ∀ k ∈ K', tau k ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1) :=
      fun k hk => htau k (hK'K hk)
    have hmem : ∀ t ∈ K'.image tau, |t| ≤ T := by
      intro t ht
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
      exact hTmem k (hK'K hk)
    have hsep := MoltResearch.ExpSums.separated_of_sample_gap_two K' tau htau' hgap
    have hlargeF : ∀ t ∈ (K'.image tau).filter (fun t =>
        V₀ < ‖∑ p ∈ Y, (b p / (p : ℂ))
          * ((Real.fourierChar (-(Real.log p * t)) : Circle) : ℂ)‖),
        ‖∑ n ∈ Finset.Icc 1 N, (a n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ delta := by
      intro t ht
      obtain ⟨htm, htl⟩ := Finset.mem_filter.mp ht
      exact hdelta t (hmem t htm) htl
    have hmain := sum_prime_integer_energy_high_moment_le P hP Y hY hlo hhi b hb
      ell hell N a T hT (K'.image tau) hmem hsep V₀ delta lam hV₀ hlam hlargeF
    refine hmain.trans ?_
    have hcard : ((K'.image tau).card : ℝ) ≤ (K.card : ℝ) := by
      exact_mod_cast (Finset.card_image_le).trans (Finset.card_le_card hK'K)
    gcongr
  have hgapE : ∀ k ∈ K.filter (fun k => Even k), ∀ l ∈ K.filter (fun k => Even k),
      k ≠ l → k + 2 ≤ l ∨ l + 2 ≤ k := by
    intro k hk l hl hkl
    obtain ⟨m, hm⟩ := (Finset.mem_filter.mp hk).2
    obtain ⟨n, hn⟩ := (Finset.mem_filter.mp hl).2
    omega
  have hgapO : ∀ k ∈ K.filter (fun k => ¬ Even k),
      ∀ l ∈ K.filter (fun k => ¬ Even k), k ≠ l → k + 2 ≤ l ∨ l + 2 ≤ k := by
    intro k hk l hl hkl
    have hke := (Finset.mem_filter.mp hk).2
    have hle := (Finset.mem_filter.mp hl).2
    rw [Int.not_even_iff_odd] at hke hle
    obtain ⟨m, hm⟩ := hke
    obtain ⟨n, hn⟩ := hle
    omega
  have hE := hfam _ (Finset.filter_subset _ _) hgapE
  have hO := hfam _ (Finset.filter_subset _ _) hgapO
  linarith [hlad, hE, hO]

open MeasureTheory in
/-- **Phase 0 VI-9g-1 — the recut exceptional leg against one budget share.**

The pointwise hypothesis remains ungated.  The high-moment theorem has
threshold dependence `V0^(-2*ell)`, so the fixed split threshold remains in
the exact fit.  In particular it cannot be passed through the quadratic
threshold optimiser, whose input has threshold dependence `V0^(-2)`.
-/
theorem setIntegral_band_energy_exceptional_le_budget_recut
    [HalaszLargeValuesAssumption] [PrimeLargeValuesAssumption]
    (P : ℕ) (hP : 2 ≤ P) (Y : Finset ℕ) (hY : ∀ p ∈ Y, p.Prime)
    (hlo : ∀ p ∈ Y, P < p) (hhi : ∀ p ∈ Y, p ≤ 2 * P)
    (b : ℕ → ℂ) (hb : ∀ p, ‖b p‖ ≤ 1)
    (ell : ℕ) (hell : 1 ≤ ell)
    (N : ℕ) (a : ℕ → ℂ) (T : ℝ) (hT1 : 1 ≤ T)
    (G : Set ℝ) (K : Finset ℤ)
    (hcover : G ⊆ ⋃ k ∈ K, Set.Ico (k : ℝ) ((k : ℝ) + 1))
    (hKT : ∀ k ∈ K, -T ≤ (k : ℝ) ∧ (k : ℝ) + 1 ≤ T)
    (Vsplit delta lam : ℝ) (hVsplit : 0 < Vsplit) (hlam : 0 < lam)
    (hdelta : ∀ t : ℝ, |t| ≤ T →
      ‖∑ n ∈ Finset.Icc 1 N, (a n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ delta)
    (Aint Bpri Gamma : ℝ)
    (hAint : Aint = 64 * ((N : ℝ) + (K.card : ℝ) * Real.sqrt T)
      * (Real.log (2 * T) + 1)
      * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2)
    (hBpri : Bpri = 64 * (∑ p ∈ Y, ‖b p‖ ^ 2 / (p : ℝ) ^ 2)
      * (P : ℝ) / Real.log P)
    (hGamma : Gamma = primeHighMomentCountCost P ell Y T Vsplit lam
      * Real.exp (-(Real.log P / (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
      * (Real.log (2 * T)) ^ 2)
    (c3 eps rho kappa : ℝ)
    (hfit : 2 * (Vsplit ^ 2 * Aint
        + delta ^ 2 * (Bpri * (1 + Gamma)))
      ≤ kappa * bandBudget c3 eps rho) :
    (∫ xi in G, ‖∑ p ∈ Y, (b p / (p : ℂ))
            * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ)‖ ^ 2
          * ‖∑ n ∈ Finset.Icc 1 N, (a n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ)‖ ^ 2)
      ≤ kappa * bandBudget c3 eps rho := by
  have hmain := setIntegral_band_energy_exceptional_max_le_recut P hP Y hY hlo hhi
    b hb ell hell N a T hT1 G K hcover hKT Vsplit delta lam hVsplit hlam
    (fun t ht _ => hdelta t ht)
  refine hmain.trans (le_trans (le_of_eq ?_) hfit)
  subst hAint hBpri hGamma
  ring

open MeasureTheory in
/-- **Phase 0 VI-9g-1 — the exceptional family seam with the fixed high-moment
split.**

Every member of the factorisation family may choose its own moment, split
threshold, and Gallagher parameter.  The common frequency cover is supplied
by the caller; the cell-uniform capstone chooses only cells meeting the
exceptional part. -/
theorem band_energy_le_budget_of_exceptional_family_recut
    [HalaszLargeValuesAssumption] [PrimeLargeValuesAssumption]
    {ι : Type*} [DecidableEq ι] {ι' : Type*}
    (F : ℝ → ℂ) (w : ℝ → ℝ) (hw0 : ∀ xi, 0 ≤ w xi)
    (Cw : ℝ) (hCw : 0 < Cw) (hwC : ∀ xi, w xi ≤ Cw)
    (G : Set ℝ) (parts : Finset ι) (part : ι → Set ℝ)
    (hmeas : ∀ i ∈ parts, MeasurableSet (part i))
    (hdisj : Set.Pairwise (↑parts) (Function.onFun Disjoint part))
    (hcover : G ⊆ ⋃ i ∈ parts, part i)
    (hint : ∀ i ∈ parts, IntegrableOn (fun xi => ‖F xi‖ ^ 2) (part i))
    (hintw : ∀ i ∈ parts, IntegrableOn (fun xi => ‖F xi‖ ^ 2 * w xi) (part i))
    (kappa : ι → ℝ) (c3 eps rho : ℝ) (hc3 : 0 ≤ c3) (hrho : 0 ≤ rho)
    (hkappa : ∑ i ∈ parts, kappa i ≤ 1)
    (u : ι) (hu : u ∈ parts)
    (hleg : ∀ i ∈ parts, i ≠ u → Cw * ∫ xi in part i, ‖F xi‖ ^ 2
      ≤ kappa i * bandBudget c3 eps rho)
    (I : Finset ι') (P : ι' → ℕ) (hP : ∀ v ∈ I, 2 ≤ P v)
    (Y : ι' → Finset ℕ) (hY : ∀ v ∈ I, ∀ p ∈ Y v, p.Prime)
    (hlo : ∀ v ∈ I, ∀ p ∈ Y v, P v < p)
    (hhi : ∀ v ∈ I, ∀ p ∈ Y v, p ≤ 2 * P v)
    (b : ι' → ℕ → ℂ) (hb : ∀ v ∈ I, ∀ p, ‖b v p‖ ≤ 1)
    (ell : ι' → ℕ) (hell : ∀ v ∈ I, 1 ≤ ell v)
    (N : ι' → ℕ) (a : ι' → ℕ → ℂ) (T : ℝ) (hT1 : 1 ≤ T)
    (K : Finset ℤ)
    (hcoverU : part u ⊆ ⋃ k ∈ K, Set.Ico (k : ℝ) ((k : ℝ) + 1))
    (hKT : ∀ k ∈ K, -T ≤ (k : ℝ) ∧ (k : ℝ) + 1 ≤ T)
    (Vsplit delta lam : ι' → ℝ)
    (hVsplit : ∀ v ∈ I, 0 < Vsplit v)
    (hlam : ∀ v ∈ I, 0 < lam v)
    (hdelta : ∀ v ∈ I, ∀ t : ℝ, |t| ≤ T →
      ‖∑ n ∈ Finset.Icc 1 (N v), (a v n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ delta v)
    (C E : ℝ) (hC0 : 0 ≤ C)
    (hfac : (∫ xi in part u, ‖F xi‖ ^ 2)
      ≤ C * ∑ v ∈ I, (∫ xi in part u,
          ‖∑ p ∈ Y v, (b v p / (p : ℂ))
              * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ)‖ ^ 2
            * ‖∑ n ∈ Finset.Icc 1 (N v), (a v n / (n : ℂ))
              * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ)‖ ^ 2) + E)
    (Aint Bpri Gamma : ι' → ℝ)
    (hAint : ∀ v ∈ I, Aint v = 64 * ((N v : ℝ) + (K.card : ℝ) * Real.sqrt T)
      * (Real.log (2 * T) + 1)
      * ∑ n ∈ Finset.Icc 1 (N v), ‖a v n‖ ^ 2 / (n : ℝ) ^ 2)
    (hBpri : ∀ v ∈ I, Bpri v = 64
      * (∑ p ∈ Y v, ‖b v p‖ ^ 2 / (p : ℝ) ^ 2)
      * (P v : ℝ) / Real.log (P v))
    (hGamma : ∀ v ∈ I, Gamma v =
      primeHighMomentCountCost (P v) (ell v) (Y v) T (Vsplit v) (lam v)
        * Real.exp (-(Real.log (P v) / (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
        * (Real.log (2 * T)) ^ 2)
    (kappa' : ι' → ℝ)
    (hfit : ∀ v ∈ I, 2 * ((Vsplit v) ^ 2 * Aint v
        + (delta v) ^ 2 * (Bpri v * (1 + Gamma v)))
      ≤ kappa' v * bandBudget c3 eps rho)
    (hfitU : C * (∑ v ∈ I, kappa' v) * bandBudget c3 eps rho + E
      ≤ kappa u * bandBudget c3 eps rho / Cw) :
    (∫ xi in G, ‖F xi‖ ^ 2 * w xi) ≤ bandBudget c3 eps rho := by
  have hcell : ∀ v ∈ I,
      (∫ xi in part u, ‖∑ p ∈ Y v, (b v p / (p : ℂ))
            * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ)‖ ^ 2
          * ‖∑ n ∈ Finset.Icc 1 (N v), (a v n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ)‖ ^ 2)
        ≤ kappa' v * bandBudget c3 eps rho := fun v hv =>
    setIntegral_band_energy_exceptional_le_budget_recut
      (P v) (hP v hv) (Y v) (hY v hv) (hlo v hv) (hhi v hv)
      (b v) (hb v hv) (ell v) (hell v hv) (N v) (a v) T hT1
      (part u) K hcoverU hKT (Vsplit v) (delta v) (lam v)
      (hVsplit v hv) (hlam v hv) (hdelta v hv)
      (Aint v) (Bpri v) (Gamma v) (hAint v hv) (hBpri v hv)
      (hGamma v hv) c3 eps rho (kappa' v) (hfit v hv)
  have hUleg : Cw * ∫ xi in part u, ‖F xi‖ ^ 2
      ≤ kappa u * bandBudget c3 eps rho := by
    have hsum := Finset.sum_le_sum hcell
    have h1 : (∫ xi in part u, ‖F xi‖ ^ 2)
        ≤ kappa u * bandBudget c3 eps rho / Cw := by
      calc
        (∫ xi in part u, ‖F xi‖ ^ 2)
            ≤ C * ∑ v ∈ I, (∫ xi in part u,
                ‖∑ p ∈ Y v, (b v p / (p : ℂ))
                    * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ)‖ ^ 2
                  * ‖∑ n ∈ Finset.Icc 1 (N v), (a v n / (n : ℂ))
                    * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ)‖ ^ 2)
                + E := hfac
        _ ≤ C * ∑ v ∈ I, kappa' v * bandBudget c3 eps rho + E :=
          add_le_add (mul_le_mul_of_nonneg_left hsum hC0) le_rfl
        _ = C * (∑ v ∈ I, kappa' v) * bandBudget c3 eps rho + E := by
          rw [← Finset.sum_mul, ← mul_assoc]
        _ ≤ kappa u * bandBudget c3 eps rho / Cw := hfitU
    calc
      Cw * ∫ xi in part u, ‖F xi‖ ^ 2
          ≤ Cw * (kappa u * bandBudget c3 eps rho / Cw) :=
            mul_le_mul_of_nonneg_left h1 hCw.le
      _ = kappa u * bandBudget c3 eps rho := by field_simp
  refine band_energy_le_budget F w hw0 Cw hwC G parts part hmeas hdisj hcover
    hint hintw kappa c3 eps rho hc3 hrho (fun i hi => ?_) hkappa
  by_cases hiu : i = u
  · subst hiu
    exact hUleg
  · exact hleg i hi hiu

set_option maxHeartbeats 800000 in
/-- **Phase 0 VI-9g-1 — the covered-cell count in schedule form.**

This is VI-9c's exceptional cover followed cell by cell by its high-moment
large-value estimate.  It is the bound used to simplify the covered-cell
cardinality appearing in `Aint` below. -/
theorem card_cellsMeeting_exceptional_le_highMomentCost
    (P : ℕ → Finset ℕ) (N v0 v1 : ℕ → ℕ) (g : ℕ → ℂ)
    (hg : ∀ p, ‖g p‖ ≤ 1) (alpha : ℕ → ℝ)
    (J : ℕ) (hJ : 0 < J) (G : Set ℝ) (K : Finset ℤ)
    (Panchor ell : ℕ → ℕ) (lam : ℕ → ℝ)
    (hprime : ∀ p ∈ P (J - 1), p.Prime)
    (hPanchor : ∀ r ∈ Finset.Ico (v0 (J - 1)) (v1 (J - 1) + 1),
      1 ≤ Panchor r)
    (hlo : ∀ r ∈ Finset.Ico (v0 (J - 1)) (v1 (J - 1) + 1),
      ∀ p ∈ eadicCell (P (J - 1)) (2 * N (J - 1)) r, Panchor r < p)
    (hhi : ∀ r ∈ Finset.Ico (v0 (J - 1)) (v1 (J - 1) + 1),
      ∀ p ∈ eadicCell (P (J - 1)) (2 * N (J - 1)) r, p ≤ 2 * Panchor r)
    (hell : ∀ r ∈ Finset.Ico (v0 (J - 1)) (v1 (J - 1) + 1), 1 ≤ ell r)
    (hlam : ∀ r ∈ Finset.Ico (v0 (J - 1)) (v1 (J - 1) + 1), 0 < lam r)
    (T : ℝ) (hT : 0 ≤ T)
    (hKT : ∀ k ∈ K, -T ≤ (k : ℝ) ∧ (k : ℝ) + 1 ≤ T) :
    ((cellsMeetingSet K
        (bandPartOn (levelSmallSet P N v0 v1 g alpha) J G J)).card : ℝ)
      ≤ ∑ r ∈ Finset.Ico (v0 (J - 1)) (v1 (J - 1) + 1),
          2 * primeHighMomentCountCost (Panchor r) (ell r)
            (eadicCell (P (J - 1)) (2 * N (J - 1)) r) T
            (Real.exp (-(alpha (J - 1) * (r : ℝ) /
              ((2 * N (J - 1) : ℕ) : ℝ)))) (lam r) := by
  classical
  let Iprev := Finset.Ico (v0 (J - 1)) (v1 (J - 1) + 1)
  let threshold : ℕ → ℝ := fun r =>
    Real.exp (-(alpha (J - 1) * (r : ℝ) / ((2 * N (J - 1) : ℕ) : ℝ)))
  have hbaseNat := card_cellsMeeting_exceptional_le_sum P N v0 v1 g alpha J hJ G K
  have hbase : ((cellsMeetingSet K
        (bandPartOn (levelSmallSet P N v0 v1 g alpha) J G J)).card : ℝ)
      ≤ ∑ r ∈ Iprev,
          ((largeValueCells K (levelCellPoly (P (J - 1)) (N (J - 1)) r g)
            (threshold r)).card : ℝ) := by
    exact_mod_cast hbaseNat
  refine hbase.trans (Finset.sum_le_sum fun r hr => ?_)
  have hcellPrime : ∀ p ∈ eadicCell (P (J - 1)) (2 * N (J - 1)) r, p.Prime :=
    fun p hp => hprime p (mem_eadicCell.mp hp).1
  have hraw := card_largeValueCells_prime_poly_pow_le
    (eadicCell (P (J - 1)) (2 * N (J - 1)) r) hcellPrime
    (Panchor r) (hPanchor r hr) (hlo r hr) (hhi r hr) g hg
    (ell r) (hell r hr) K T (threshold r) (lam r) hT
    (Real.exp_pos _).le (hlam r hr) hKT
  have hpow : 0 < (threshold r) ^ (2 * ell r) := pow_pos (Real.exp_pos _) _
  unfold primeHighMomentCountCost
  rw [show 2 * ((Real.exp Real.pi
          * ((T + 1) / (((Panchor r) ^ (ell r) : ℕ) : ℝ)
              + 2 * (((2 : ℕ) ^ (ell r) : ℕ) : ℝ))
          * ((Nat.factorial (ell r) : ℝ) ^ 2
              * (∑ p ∈ eadicCell (P (J - 1)) (2 * N (J - 1)) r,
                  (1 : ℝ) / (p : ℝ)) ^ (ell r))
          * ((1 + lam r) + (1 / lam r)
              * (2 * Real.pi * Real.log ((2 * Panchor r) ^ (ell r))) ^ 2)) /
        (threshold r) ^ (2 * ell r)) =
      (2 * (Real.exp Real.pi
          * ((T + 1) / (((Panchor r) ^ (ell r) : ℕ) : ℝ)
              + 2 * (((2 : ℕ) ^ (ell r) : ℕ) : ℝ))
          * ((Nat.factorial (ell r) : ℝ) ^ 2
              * (∑ p ∈ eadicCell (P (J - 1)) (2 * N (J - 1)) r,
                  (1 : ℝ) / (p : ℝ)) ^ (ell r))
          * ((1 + lam r) + (1 / lam r)
              * (2 * Real.pi * Real.log ((2 * Panchor r) ^ (ell r))) ^ 2))) /
        (threshold r) ^ (2 * ell r) by ring]
  rw [le_div_iff₀ hpow]
  exact hraw

-- This capstone contains the decomposition, the exceptional-cell cover, and
-- the two error estimates, so grant the same bounded elaboration headroom as
-- the pre-recut family capstone.
set_option maxHeartbeats 800000 in
open MeasureTheory in
/-- **Phase 0 VI-9g-1 — the cell-uniform band capstone after the recut.**

The frequency cover is
`cellsMeetingSet (bandCells K2) (bandPartOn Pset J innerBand J)`.  Hence the
integer large-values factor contains precisely the number of covered cells,
not the full `bandCells K2`.  When `Pset` is the ordinary-level small-set
family, `card_cellsMeeting_exceptional_le_sum` and
`card_largeValueCells_prime_poly_pow_le` bound this cardinality from the last
ordinary level.

The displayed fit is the exact fixed-threshold consequence of VI-9d.  Its
prime term contains `primeHighMomentCountCost`, and therefore has no separate
`T / P` summand. -/
theorem band_energy_typicalS_le_of_cellUniform_fit_recut
    [HalaszLargeValuesAssumption] [PrimeLargeValuesAssumption]
    (g : ℕ → ℂ) (hcm : CompletelyMultiplicativeC g) (hg : ∀ m, ‖g m‖ ≤ 1)
    (A Delta H : ℕ) (hA : 0 < A) (hH : 0 < H) (hDeltaA : Delta ≤ A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPA : ∀ p ∈ P, p * p ≤ A)
    (rest : List (Finset ℕ))
    (N v0 v1 : ℕ) (hN : 0 < N)
    (hcov : (Finset.Ico v0 (v1 + 1)).biUnion (eadicCell P (2 * N)) = P)
    (hstable : ∀ p ∈ P, ∀ m,
      HasFactorInAll rest (p * m) ↔ HasFactorInAll rest m)
    (q : ℕ → ℕ)
    (hqcell : ∀ v ∈ Finset.Ico v0 (v1 + 1), q v ∈ eadicCell P (2 * N) v)
    (hq1 : ∀ v, 1 ≤ q v)
    (hqmin : ∀ v ∈ Finset.Ico v0 (v1 + 1),
      ∀ p ∈ eadicCell P (2 * N) v, q v ≤ p)
    (hLA : ∀ v ∈ Finset.Ico v0 (v1 + 1),
      ∀ p ∈ eadicCell P (2 * N) v, A / (N * p) + 1 ≤ A / p)
    (hLB : ∀ v ∈ Finset.Ico v0 (v1 + 1),
      ∀ p ∈ eadicCell P (2 * N) v,
        (A + Delta) / (N * p) + 1 ≤ (A + Delta) / p)
    (w : ℝ → ℝ) (hwm : Measurable w) (hw0 : ∀ xi, 0 ≤ w xi)
    (hwsup : ∀ xi, w xi ≤ (4 * (H : ℝ) / (A : ℝ)) ^ 2)
    (K1 K2 : ℝ)
    (J : ℕ) (Pset : ℕ → Set ℝ) (hPset : ∀ j, MeasurableSet (Pset j))
    (c3 eps : ℝ) (hc3 : 0 ≤ c3)
    (hleg : ∀ j ∈ Finset.range (J + 1), j ≠ J →
      (4 * (H : ℝ) / (A : ℝ)) ^ 2
          * ∫ xi in bandPartOn Pset J {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} j,
            ‖∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
              * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2
        ≤ (1 / 2 ^ (j + 1)) * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)))
    (Pc : ℕ → ℕ) (hPc : ∀ v ∈ Finset.Ico v0 (v1 + 1), 2 ≤ Pc v)
    (hlo : ∀ v ∈ Finset.Ico v0 (v1 + 1),
      ∀ p ∈ eadicCell P (2 * N) v, Pc v < p)
    (hhi : ∀ v ∈ Finset.Ico v0 (v1 + 1),
      ∀ p ∈ eadicCell P (2 * N) v, p ≤ 2 * Pc v)
    (T : ℝ) (hT1 : 1 ≤ T) (hTK2 : K2 + 2 ≤ T)
    (ell : ℕ → ℕ) (hell : ∀ v ∈ Finset.Ico v0 (v1 + 1), 1 ≤ ell v)
    (Vsplit delta lam : ℕ → ℝ)
    (hVsplit : ∀ v ∈ Finset.Ico v0 (v1 + 1), 0 < Vsplit v)
    (hlam : ∀ v ∈ Finset.Ico v0 (v1 + 1), 0 < lam v)
    (hdelta : ∀ v ∈ Finset.Ico v0 (v1 + 1), ∀ t : ℝ, |t| ≤ T →
      ‖∑ n ∈ Finset.Icc 1 ((A + Delta) / q v),
          (cellBlockCoeff g A (A + Delta) P rest (q v) n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ≤ delta v)
    (kappa' : ℕ → ℝ)
    (hfit : ∀ v ∈ Finset.Ico v0 (v1 + 1),
      2 * ((Vsplit v) ^ 2
            * (64 * ((((A + Delta) / q v : ℕ) : ℝ)
                + ((cellsMeetingSet (bandCells K2)
                    (bandPartOn Pset J {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} J)).card : ℝ)
                    * Real.sqrt T)
              * (Real.log (2 * T) + 1)
              * ∑ n ∈ Finset.Icc 1 ((A + Delta) / q v),
                  ‖cellBlockCoeff g A (A + Delta) P rest (q v) n‖ ^ 2 /
                    (n : ℝ) ^ 2)
          + (delta v) ^ 2
            * ((64 * (∑ p ∈ eadicCell P (2 * N) v,
                    ‖g p‖ ^ 2 / (p : ℝ) ^ 2)
                * (Pc v : ℝ) / Real.log (Pc v))
              * (1 + primeHighMomentCountCost (Pc v) (ell v)
                  (eadicCell P (2 * N) v) T (Vsplit v) (lam v)
                * Real.exp (-(Real.log (Pc v) /
                  (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
                * (Real.log (2 * T)) ^ 2)))
        ≤ kappa' v * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)))
    (hfitU : 2 * ((Finset.Ico v0 (v1 + 1)).card : ℝ)
          * (∑ v ∈ Finset.Ico v0 (v1 + 1), kappa' v)
          * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ))
        + 2 * (2 * cellReplacementEnergyBound P N v0 v1 A (A + Delta) T
            + 2 * (4 * collisionEnergyBound A (A + Delta) P rest T))
      ≤ (1 / 2 ^ (J + 1)) * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)) /
          (4 * (H : ℝ) / (A : ℝ)) ^ 2) :
    (∫ xi in {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2},
        ‖∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
          * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2 * w xi)
      ≤ bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)) := by
  let G : Set ℝ := bandPartOn Pset J {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} J
  let Kcov : Finset ℤ := cellsMeetingSet (bandCells K2) G
  let I := Finset.Ico v0 (v1 + 1)
  let error : ℝ → ℂ := fun xi =>
    typicalSCellReplacement g A (A + Delta) P rest N v0 v1 q xi
      + typicalSAdjustedCollision g A (A + Delta) P rest N v0 v1 xi
  have hAreal : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hHreal : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hCw : (0 : ℝ) < (4 * (H : ℝ) / (A : ℝ)) ^ 2 := by positivity
  have hT : (0 : ℝ) < T := by linarith
  have hGT : G ⊆ Set.Ioc (-T) T := by
    intro xi hxi
    have h := inner_band_subset_Icc K1 K2 (bandPartOn_subset Pset J _ J hxi)
    rw [Set.mem_Icc] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hGm : MeasurableSet G :=
    bandPartOn_measurableSet Pset hPset J _ (measurableSet_inner_band K1 K2) J
  have hcoverBand : G ⊆ ⋃ k ∈ bandCells K2, Set.Ico (k : ℝ) ((k : ℝ) + 1) :=
    (bandPartOn_subset Pset J _ J).trans (inner_band_subset_bandCells K1 K2)
  have hcoverCov : G ⊆ ⋃ k ∈ Kcov, Set.Ico (k : ℝ) ((k : ℝ) + 1) := by
    intro xi hxi
    have hxcover := hcoverBand hxi
    rw [Set.mem_iUnion₂] at hxcover
    obtain ⟨k, hk, hxik⟩ := hxcover
    have hkcov : k ∈ Kcov := by
      dsimp [Kcov]
      rw [mem_cellsMeetingSet]
      exact ⟨hk, xi, ⟨hxik.1, hxik.2.le⟩, hxi⟩
    exact Set.mem_iUnion₂.mpr ⟨k, hkcov, hxik⟩
  have hKTCov : ∀ k ∈ Kcov, -T ≤ (k : ℝ) ∧ (k : ℝ) + 1 ≤ T := by
    intro k hk
    have hkband : k ∈ bandCells K2 := (mem_cellsMeetingSet.mp hk).1
    exact bandCells_mem_Icc K2 T hTK2 k hkband
  have hFc : Continuous fun xi : ℝ =>
      ∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
        * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ) :=
    ExpSums.continuous_char_poly (typicalS A (A + Delta) (P :: rest))
      (fun m => g m / (m : ℂ)) (fun m => Real.log m)
  have hwnorm : ∀ xi, ‖w xi‖ ≤ (4 * (H : ℝ) / (A : ℝ)) ^ 2 := fun xi => by
    rw [Real.norm_of_nonneg (hw0 xi)]
    exact hwsup xi
  have herrorc : Continuous error :=
    (continuous_typicalSCellReplacement g A (A + Delta) P rest N v0 v1 q).add
      (continuous_typicalSAdjustedCollision g A (A + Delta) P rest N v0 v1)
  have hX : ∀ v ∈ I, Continuous fun xi : ℝ =>
      (∑ p ∈ eadicCell P (2 * N) v, (g p / (p : ℂ))
          * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
        * (∑ n ∈ Finset.Icc 1 ((A + Delta) / q v),
          (cellBlockCoeff g A (A + Delta) P rest (q v) n / (n : ℂ))
            * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ)) := by
    intro v hv
    exact (ExpSums.continuous_char_poly (eadicCell P (2 * N) v)
      (fun p => g p / (p : ℂ)) (fun p => Real.log p)).mul
        (ExpSums.continuous_char_poly (Finset.Icc 1 ((A + Delta) / q v))
          (fun n => cellBlockCoeff g A (A + Delta) P rest (q v) n / (n : ℂ))
          (fun n => Real.log n))
  have hdecomp : ∀ xi ∈ G,
      ∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
          * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)
        = (∑ v ∈ I, (∑ p ∈ eadicCell P (2 * N) v, (g p / (p : ℂ))
              * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ))
            * (∑ n ∈ Finset.Icc 1 ((A + Delta) / q v),
              (cellBlockCoeff g A (A + Delta) P rest (q v) n / (n : ℂ))
                * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ)))
          + error xi := by
    intro xi hxi
    rw [typicalS_phase_eq_cellUniform_add_errors g hcm A Delta P hP rest N v0 v1
      hcov hstable q xi]
    congr 1
    unfold typicalSCellUniformMain levelCellPoly
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [sum_cellBlockCoeff_Icc_eq g A (A + Delta) P rest (q v) xi]
  have hfac0 := setIntegral_norm_sq_le_family_of_decomp
    (fun xi => ∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
      * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
    I _ error hX herrorc T G hGm hGT hdecomp
  simp_rw [norm_mul, mul_pow] at hfac0
  have hrepl : (∫ xi in G,
        ‖typicalSCellReplacement g A (A + Delta) P rest N v0 v1 q xi‖ ^ 2)
      ≤ cellReplacementEnergyBound P N v0 v1 A (A + Delta) T :=
    setIntegral_norm_sq_typicalSCellReplacement_le g hg A (A + Delta)
      (Nat.le_add_right A Delta) P rest N v0 v1 hN q hqcell hq1 hqmin hLA hLB
      T hT G hGm hGT
  have hcoll : (∫ xi in G,
        ‖typicalSAdjustedCollision g A (A + Delta) P rest N v0 v1 xi‖ ^ 2)
      ≤ 4 * collisionEnergyBound A (A + Delta) P rest T :=
    (ExpSums.setIntegral_le_intervalIntegral_of_nonneg
      (fun xi => ‖typicalSAdjustedCollision g A (A + Delta) P rest N v0 v1 xi‖ ^ 2)
      ((continuous_typicalSAdjustedCollision g A (A + Delta) P rest N v0 v1).norm.pow 2)
      (fun xi => sq_nonneg _) T hT.le G hGT).trans
      (intervalIntegral_norm_sq_typicalSAdjustedCollision_le g hg A Delta hDeltaA
        P hP hPA rest N v0 v1 hcov T hT)
  have hsplit : (∫ xi in G, ‖error xi‖ ^ 2)
      ≤ 2 * cellReplacementEnergyBound P N v0 v1 A (A + Delta) T
        + 2 * (4 * collisionEnergyBound A (A + Delta) P rest T) := by
    have htri := ExpSums.setIntegral_norm_add_sq_le
      (typicalSCellReplacement g A (A + Delta) P rest N v0 v1 q)
      (typicalSAdjustedCollision g A (A + Delta) P rest N v0 v1)
      (continuous_typicalSCellReplacement g A (A + Delta) P rest N v0 v1 q)
      (continuous_typicalSAdjustedCollision g A (A + Delta) P rest N v0 v1)
      T G hGm hGT
    dsimp [error]
    linarith [htri, hrepl, hcoll]
  have hfac : (∫ xi in G,
        ‖∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
          * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ)‖ ^ 2)
      ≤ 2 * (I.card : ℝ) * ∑ v ∈ I, (∫ xi in G,
          ‖∑ p ∈ eadicCell P (2 * N) v, (g p / (p : ℂ))
              * ((Real.fourierChar (-(Real.log p * xi)) : Circle) : ℂ)‖ ^ 2
            * ‖∑ n ∈ Finset.Icc 1 ((A + Delta) / q v),
              (cellBlockCoeff g A (A + Delta) P rest (q v) n / (n : ℂ))
                * ((Real.fourierChar (-(Real.log n * xi)) : Circle) : ℂ)‖ ^ 2)
        + 2 * (2 * cellReplacementEnergyBound P N v0 v1 A (A + Delta) T
            + 2 * (4 * collisionEnergyBound A (A + Delta) P rest T)) := by
    linarith [hfac0, hsplit]
  exact band_energy_le_budget_of_exceptional_family_recut
    (fun xi => ∑ m ∈ typicalS A (A + Delta) (P :: rest), (g m / (m : ℂ))
      * ((Real.fourierChar (-(Real.log m * xi)) : Circle) : ℂ))
    w hw0 ((4 * (H : ℝ) / (A : ℝ)) ^ 2) hCw hwsup
    {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2} (Finset.range (J + 1))
    (bandPartOn Pset J {xi : ℝ | K1 ≤ |xi| ∧ |xi| ≤ K2})
    (fun j _ => bandPartOn_measurableSet Pset hPset J _
      (measurableSet_inner_band K1 K2) j)
    (bandPartOn_pairwiseDisjoint Pset J _)
    (bandPartOn_cover Pset J _)
    (fun j _ => integrableOn_norm_sq_inner_band _ hFc K1 K2 _
      (bandPartOn_subset Pset J _ j))
    (fun j _ => integrableOn_norm_sq_mul_inner_band _ hFc w hwm _ hwnorm K1 K2 _
      (bandPartOn_subset Pset J _ j))
    (fun j => 1 / 2 ^ (j + 1)) c3 eps ((Delta : ℝ) / (A : ℝ)) hc3
    (by positivity) (geometric_shares_le_one (J + 1)) J
    (Finset.mem_range.mpr (Nat.lt_succ_self J)) hleg
    I Pc hPc (fun v => eadicCell P (2 * N) v)
    (fun v hv p hp => hP p (mem_eadicCell.mp hp).1) hlo hhi
    (fun _ => g) (fun _ _ p => hg p) ell hell
    (fun v => (A + Delta) / q v)
    (fun v => cellBlockCoeff g A (A + Delta) P rest (q v)) T hT1
    Kcov hcoverCov hKTCov Vsplit delta lam hVsplit hlam hdelta
    (2 * (I.card : ℝ))
    (2 * (2 * cellReplacementEnergyBound P N v0 v1 A (A + Delta) T
      + 2 * (4 * collisionEnergyBound A (A + Delta) P rest T)))
    (by positivity) hfac
    (fun v => 64 * ((((A + Delta) / q v : ℕ) : ℝ)
        + (Kcov.card : ℝ) * Real.sqrt T) * (Real.log (2 * T) + 1)
      * ∑ n ∈ Finset.Icc 1 ((A + Delta) / q v),
          ‖cellBlockCoeff g A (A + Delta) P rest (q v) n‖ ^ 2 / (n : ℝ) ^ 2)
    (fun v => 64 * (∑ p ∈ eadicCell P (2 * N) v,
        ‖g p‖ ^ 2 / (p : ℝ) ^ 2) * (Pc v : ℝ) / Real.log (Pc v))
    (fun v => primeHighMomentCountCost (Pc v) (ell v) (eadicCell P (2 * N) v)
        T (Vsplit v) (lam v)
      * Real.exp (-(Real.log (Pc v) / (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
      * (Real.log (2 * T)) ^ 2)
    (fun v _ => rfl) (fun v _ => rfl) (fun v _ => rfl) kappa' (by
      intro v hv
      simpa [I, Kcov, G] using hfit v hv) (by simpa [I] using hfitU)

end Tao2015

end MoltResearch
