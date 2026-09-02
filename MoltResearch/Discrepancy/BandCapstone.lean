import MoltResearch.Discrepancy.WindowTK
import MoltResearch.Discrepancy.WindowAssembly

/-!
# The band-energy capstone (Track R, `[mrt]` A.2, Phase VI)

The `[mrt]` A.2 band estimate is assembled from legs that live in two
*import-sibling* modules.  `WindowAssembly` carries the level-one estimate
`band_energy_level_one_le`, the cell/block mean value
`setIntegral_norm_sq_cell_block_sum_le`, the outer band `band_energy_outer_le`
and the capstone glue (`setIntegral_le_sum_of_cover`, `setIntegral_weight_mono`,
`setIntegral_norm_add_sq_le`, `setIntegral_norm_sq_sum_le_card_mul`).
`WindowTK` carries the level-`j` estimate `band_energy_level_le_of_prev_large`,
the collar cost `intervalIntegral_norm_sq_cell_replace_le` and the elementary
large-values count `card_large_prime_poly_le`.

**Neither module imports the other** — they meet only in
`MoltResearch.DiscrepancyAnalytic` — so no composition of a `WindowAssembly` leg
with a `WindowTK` leg can be stated in either file.  That is the whole reason
this module exists.  It is the first place in the tree where both halves of the
band machinery are simultaneously in scope.

The remaining leg, the exceptional band `𝒰`, is *not* here: it is conditional on
`HalaszLargeValuesAssumption` and `PrimeLargeValuesAssumption`, and
`scripts/check_layering.sh` forbids `MoltResearch/` from importing the
`Conjectures/` tree where those classes live.  So the capstone splits at the
same seam that split IV-3 — an elementary half here, a conditional half in
`Conjectures/C0002_erdos_discrepancy/src/`.
-/

namespace MoltResearch

open MeasureTheory Finset ExpSums in
/-- **A2-III VI-1c-4 — one level of the `[MR]` ladder, from prime-indexed
decomposition to band bound.**

The `[MR]` decomposition lemma hands each level a sum indexed by **primes**, in
which every prime carries its *own* quotient block `Ioc (A/p) (B/p)`.  Every
mean value estimate in the tree is indexed by **cells**, with one block per cell
fixed by a representative `q v`.  This is the lemma that crosses the gap, and it
costs exactly one `L²` triangle inequality:

* the **main term** `∑_v (∑_{p ∈ cell v} w_p) · Z_{q_v}` is priced by
  `setIntegral_norm_sq_cell_block_sum_le` — smallness of the cell polynomial on
  `G` against the mean value of the block at the cell's representative;
* the **replacement error** `∑_v ∑_{p ∈ cell v} w_p (Z_p − Z_{q_v})` is priced by
  `intervalIntegral_norm_sq_cell_replace_le`, cell by cell, and reassembled by
  `setIntegral_norm_sq_sum_le_card_mul`.

The algebraic split is `sum_eq_cell_rep_add_cell_error` specialised to a
double sum already grouped by cells; it is re-derived inline here rather than
invoked, because that lemma enters from `∑_{p ∈ P}` through
`sum_eq_sum_eadicCells` and so is indexed by `Finset.range (V+1)`, while every
band estimate is indexed by `Finset.Ico v₀ (v₁+1)`.  The consumer bridges the
two with `Finset.range_eq_Ico`.

**Both `2`s are honest.**  The first is the `L²` triangle: the main term and the
error are anchored at different scales — one at the cell representative, one at
each prime — so their energies cannot be merged into a single mean value
application.  The second is the Cauchy–Schwarz factor `#I` inside each half; on
the main term it is the one `band_energy_level_one_le` already carries, and on
the error term it is there for the same reason, that the cell contributions are
not orthogonal on `G`.

⚠️ `hqcell` forces every cell in `Ico v₀ (v₁+1)` to be **nonempty**.  That is
inherited from `band_energy_level_one_le`, which makes the same demand, and it
is a real modelling debt for the consumer rather than something this lemma can
discharge: at fine e-adic resolution the prime gaps leave cells empty, and the
index range must be restricted to the occupied cells before this applies. -/
theorem setIntegral_norm_sq_cell_prime_block_le
    (P : Finset ℕ) (N v₀ v₁ : ℕ) (hN : 0 < N) (q : ℕ → ℕ)
    (A B R : ℕ) (hR : 1 ≤ R) (hAB : A ≤ B) (hB : B ≤ R * A)
    (hqcell : ∀ v ∈ Finset.Ico v₀ (v₁+1), q v ∈ eadicCell P (2*N) v)
    (hq1 : ∀ v, 1 ≤ q v) (hqA : ∀ v, q v ≤ A)
    (hqmin : ∀ v ∈ Finset.Ico v₀ (v₁+1),
      ∀ p ∈ eadicCell P (2*N) v, q v ≤ p)
    (hLA : ∀ v ∈ Finset.Ico v₀ (v₁+1),
      ∀ p ∈ eadicCell P (2*N) v, A/(N*p) + 1 ≤ A/p)
    (hLB : ∀ v ∈ Finset.Ico v₀ (v₁+1),
      ∀ p ∈ eadicCell P (2*N) v, B/(N*p) + 1 ≤ B/p)
    (g c : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1)
    (T : ℝ) (hT : 0 < T)
    (G : Set ℝ) (hGm : MeasurableSet G) (hGT : G ⊆ Set.Ioc (-T) T)
    (s : ℕ → ℝ)
    (hsmall : ∀ v ∈ Finset.Ico v₀ (v₁+1), ∀ ξ ∈ G,
      ‖∑ p ∈ eadicCell P (2*N) v, (g p/(p:ℂ))
          * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖ ≤ s v) :
    (∫ ξ in G, ‖∑ v ∈ Finset.Ico v₀ (v₁+1), ∑ p ∈ eadicCell P (2*N) v,
        ((g p/(p:ℂ)) * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))
          * (∑ m ∈ Finset.Ioc (A/p) (B/p), (c m/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))‖^2)
      ≤ 2 * (((Finset.Ico v₀ (v₁+1)).card : ℝ)
              * ∑ v ∈ Finset.Ico v₀ (v₁+1), (s v)^2
                  * (Real.exp Real.pi * (T/((A/(q v) : ℕ):ℝ) + 4*(R:ℝ))
                      * ∑ m ∈ Finset.Ioc (A/(q v)) (B/(q v)),
                          ‖c m‖^2/(m:ℝ)))
        + 2 * (((Finset.Ico v₀ (v₁+1)).card : ℝ)
              * ∑ v ∈ Finset.Ico v₀ (v₁+1),
                  (∑ p ∈ eadicCell P (2*N) v, (1:ℝ)/(p:ℝ))
                    * ∑ p ∈ eadicCell P (2*N) v, ((1:ℝ)/(p:ℝ))
                        * (2 * (Real.exp Real.pi * (T/((A/p : ℕ):ℝ) + 4)
                                * (((A/(N*p) + 1 : ℕ):ℝ)/((A/p : ℕ):ℝ)))
                           + 2 * (Real.exp Real.pi * (T/((B/p : ℕ):ℝ) + 4)
                                * (((B/(N*p) + 1 : ℕ):ℝ)/((B/p : ℕ):ℝ))))) := by
  classical
  have hchar : ∀ w : ℝ, Continuous fun ξ : ℝ =>
      ((Real.fourierChar (-(w * ξ)) : Circle) : ℂ) := fun w =>
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  -- the cell-representative split, at each frequency
  have key : ∀ ξ : ℝ,
      (∑ v ∈ Finset.Ico v₀ (v₁+1), ∑ p ∈ eadicCell P (2*N) v,
        ((g p/(p:ℂ)) * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))
          * (∑ m ∈ Finset.Ioc (A/p) (B/p), (c m/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)))
      = (∑ v ∈ Finset.Ico v₀ (v₁+1),
            (∑ p ∈ eadicCell P (2*N) v, (g p/(p:ℂ))
                * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))
              * (∑ m ∈ Finset.Ioc (A/(q v)) (B/(q v)), (c m/(m:ℂ))
                  * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)))
        + ∑ v ∈ Finset.Ico v₀ (v₁+1), ∑ p ∈ eadicCell P (2*N) v,
            ((g p/(p:ℂ))
                * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))
              * ((∑ m ∈ Finset.Ioc (A/p) (B/p), (c m/(m:ℂ))
                    * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
                  - (∑ m ∈ Finset.Ioc (A/(q v)) (B/(q v)), (c m/(m:ℂ))
                    * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))) := by
    intro ξ
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  -- continuity of the two halves
  have hcell : ∀ v : ℕ, Continuous fun ξ : ℝ =>
      ∑ p ∈ eadicCell P (2*N) v, (g p/(p:ℂ))
        * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ) := fun v =>
    continuous_finset_sum _ fun p _ => continuous_const.mul (hchar (Real.log p))
  have hblk : ∀ n : ℕ, Continuous fun ξ : ℝ =>
      ∑ m ∈ Finset.Ioc (A/n) (B/n), (c m/(m:ℂ))
        * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) := fun n =>
    continuous_finset_sum _ fun m _ => continuous_const.mul (hchar (Real.log m))
  have hMc : Continuous fun ξ : ℝ =>
      ∑ v ∈ Finset.Ico v₀ (v₁+1),
        (∑ p ∈ eadicCell P (2*N) v, (g p/(p:ℂ))
            * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))
          * (∑ m ∈ Finset.Ioc (A/(q v)) (B/(q v)), (c m/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)) :=
    continuous_finset_sum _ fun v _ => (hcell v).mul (hblk (q v))
  have hEc : ∀ v : ℕ, Continuous fun ξ : ℝ =>
      ∑ p ∈ eadicCell P (2*N) v,
        ((g p/(p:ℂ)) * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))
          * ((∑ m ∈ Finset.Ioc (A/p) (B/p), (c m/(m:ℂ))
                * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
              - (∑ m ∈ Finset.Ioc (A/(q v)) (B/(q v)), (c m/(m:ℂ))
                * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))) :=
    fun v => continuous_finset_sum _ fun p _ =>
      (continuous_const.mul (hchar (Real.log p))).mul
        ((hblk p).sub (hblk (q v)))
  have hHc : Continuous fun ξ : ℝ =>
      ∑ v ∈ Finset.Ico v₀ (v₁+1), ∑ p ∈ eadicCell P (2*N) v,
        ((g p/(p:ℂ)) * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))
          * ((∑ m ∈ Finset.Ioc (A/p) (B/p), (c m/(m:ℂ))
                * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
              - (∑ m ∈ Finset.Ioc (A/(q v)) (B/(q v)), (c m/(m:ℂ))
                * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))) :=
    continuous_finset_sum _ fun v _ => hEc v
  calc (∫ ξ in G, ‖∑ v ∈ Finset.Ico v₀ (v₁+1), ∑ p ∈ eadicCell P (2*N) v,
        ((g p/(p:ℂ)) * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))
          * (∑ m ∈ Finset.Ioc (A/p) (B/p), (c m/(m:ℂ))
              * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))‖^2)
      = ∫ ξ in G, ‖(∑ v ∈ Finset.Ico v₀ (v₁+1),
            (∑ p ∈ eadicCell P (2*N) v, (g p/(p:ℂ))
                * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))
              * (∑ m ∈ Finset.Ioc (A/(q v)) (B/(q v)), (c m/(m:ℂ))
                  * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)))
          + (∑ v ∈ Finset.Ico v₀ (v₁+1), ∑ p ∈ eadicCell P (2*N) v,
            ((g p/(p:ℂ))
                * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))
              * ((∑ m ∈ Finset.Ioc (A/p) (B/p), (c m/(m:ℂ))
                    * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
                  - (∑ m ∈ Finset.Ioc (A/(q v)) (B/(q v)), (c m/(m:ℂ))
                    * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))))‖^2 := by
        simp_rw [key]
    _ ≤ 2 * (∫ ξ in G, ‖∑ v ∈ Finset.Ico v₀ (v₁+1),
            (∑ p ∈ eadicCell P (2*N) v, (g p/(p:ℂ))
                * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))
              * (∑ m ∈ Finset.Ioc (A/(q v)) (B/(q v)), (c m/(m:ℂ))
                  * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))‖^2)
        + 2 * (∫ ξ in G, ‖∑ v ∈ Finset.Ico v₀ (v₁+1),
            ∑ p ∈ eadicCell P (2*N) v,
            ((g p/(p:ℂ))
                * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ))
              * ((∑ m ∈ Finset.Ioc (A/p) (B/p), (c m/(m:ℂ))
                    * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))
                  - (∑ m ∈ Finset.Ioc (A/(q v)) (B/(q v)), (c m/(m:ℂ))
                    * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ)))‖^2) :=
        setIntegral_norm_add_sq_le _ _ hMc hHc T G hGm hGT
    _ ≤ 2 * (((Finset.Ico v₀ (v₁+1)).card : ℝ)
              * ∑ v ∈ Finset.Ico v₀ (v₁+1), (s v)^2
                  * (Real.exp Real.pi * (T/((A/(q v) : ℕ):ℝ) + 4*(R:ℝ))
                      * ∑ m ∈ Finset.Ioc (A/(q v)) (B/(q v)),
                          ‖c m‖^2/(m:ℝ)))
        + 2 * (((Finset.Ico v₀ (v₁+1)).card : ℝ)
              * ∑ v ∈ Finset.Ico v₀ (v₁+1),
                  (∑ p ∈ eadicCell P (2*N) v, (1:ℝ)/(p:ℝ))
                    * ∑ p ∈ eadicCell P (2*N) v, ((1:ℝ)/(p:ℝ))
                        * (2 * (Real.exp Real.pi * (T/((A/p : ℕ):ℝ) + 4)
                                * (((A/(N*p) + 1 : ℕ):ℝ)/((A/p : ℕ):ℝ)))
                           + 2 * (Real.exp Real.pi * (T/((B/p : ℕ):ℝ) + 4)
                                * (((B/(N*p) + 1 : ℕ):ℝ)/((B/p : ℕ):ℝ))))) := by
        gcongr
        · exact setIntegral_norm_sq_cell_block_sum_le P N v₀ v₁ q A B R hR hB
            hq1 hqA g c T hT G hGm hGT s hsmall
        · exact setIntegral_norm_sq_sum_le_card_mul _ _
            (fun v _ => hEc v) T hT.le G hGm hGT _
            (fun v hv => intervalIntegral_norm_sq_cell_replace_le hN
              (hqcell v hv) (hq1 v) (hqmin v hv) A B hAB (hLA v hv) (hLB v hv)
              g c hg hc T hT)

end MoltResearch
