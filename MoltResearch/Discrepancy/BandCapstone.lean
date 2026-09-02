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

open MeasureTheory Finset ExpSums in
/-- **A2-III VI-1c-5 — Cauchy-Schwarz over levels, staying on `G`.**

The frequency-set-native companion of `setIntegral_norm_sq_sum_le_card_mul`.
That lemma prices each level by an estimate on the enclosing interval, because
the collar cost it consumes is an interval statement.  The level-`j` leg
`band_energy_level_le_of_prev_large` is different: it is already proved *on an
abstract `G`*, since its saving comes from the pointwise largeness of the
previous level's prime polynomial on `G` and would be destroyed by enlarging to
`(-T)..T`, where no such largeness holds.

So the level-`j` main term needs the same Cauchy-Schwarz over levels with the
interval enlargement omitted — the cell contributions are not orthogonal on `G`,
which is what the factor `#I` pays for, but there is nothing to enlarge.

Stated with `hGT` even though the interval is never used for monotonicity: it is
what supplies integrability of the summands on `G`, via
`Continuous.integrableOn_Ioc` and `.mono_set`. -/
theorem setIntegral_norm_sq_sum_le_card_mul_of_setIntegral (F : ℕ → ℝ → ℂ)
    (I : Finset ℕ) (hF : ∀ v ∈ I, Continuous (F v)) (T : ℝ)
    (G : Set ℝ) (hGm : MeasurableSet G) (hGT : G ⊆ Set.Ioc (-T) T)
    (M : ℕ → ℝ) (hM : ∀ v ∈ I, (∫ ξ in G, ‖F v ξ‖^2) ≤ M v) :
    (∫ ξ in G, ‖∑ v ∈ I, F v ξ‖^2) ≤ (I.card : ℝ) * ∑ v ∈ I, M v := by
  classical
  have hFc : ∀ v ∈ I, Continuous fun ξ => ‖F v ξ‖^2 := fun v hv =>
    ((hF v hv).norm.pow 2)
  have hFi : ∀ v ∈ I, IntegrableOn (fun ξ => ‖F v ξ‖^2) G := fun v hv =>
    ((hFc v hv).integrableOn_Ioc (a := -T) (b := T)).mono_set hGT
  have hsumc : Continuous fun ξ => ‖∑ v ∈ I, F v ξ‖^2 :=
    ((continuous_finset_sum I fun v hv => hF v hv).norm.pow 2)
  have hsumi : IntegrableOn (fun ξ => ‖∑ v ∈ I, F v ξ‖^2) G :=
    (hsumc.integrableOn_Ioc (a := -T) (b := T)).mono_set hGT
  calc (∫ ξ in G, ‖∑ v ∈ I, F v ξ‖^2)
      ≤ ∫ ξ in G, (I.card : ℝ) * ∑ v ∈ I, ‖F v ξ‖^2 :=
        setIntegral_mono_on hsumi
          ((integrable_finset_sum I fun v hv => hFi v hv).const_mul _)
          hGm (fun ξ _ => norm_sum_sq_le_card_mul I (fun v => F v ξ))
    _ = (I.card : ℝ) * ∑ v ∈ I, ∫ ξ in G, ‖F v ξ‖^2 := by
        rw [integral_const_mul, integral_finset_sum I (fun v hv => hFi v hv)]
    _ ≤ (I.card : ℝ) * ∑ v ∈ I, M v := by
        refine mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun v hv => hM v hv) (by positivity)

open MeasureTheory Finset ExpSums in
/-- **A2-III VI-1c-6 — the level-`j` leg, summed over cells.**

The level-`j` counterpart of `setIntegral_norm_sq_cell_prime_block_le`.  At
level `j > 1` the `[MR]` estimate is `band_energy_level_le_of_prev_large`, whose
saving `small²/large^{2ℓ}` comes from the previous level's prime polynomial
being *large* on `G` while this level's cell polynomial is *small* there.

**Why this leg is shorter than the level-one leg.**  Two of the three steps that
lemma needed are absent here.  There is no cell-representative split, because
`band_energy_level_le_of_prev_large` already takes its first factor as an
abstract continuous `Q` — a cell polynomial goes straight in, and the block `S v`
is whatever the decomposition produced, with no requirement that it be the
quotient window of a distinguished prime.  Consequently there is no replacement
error, and so no `L²` triangle inequality: the whole level is one term, not two.

What does survive is the Cauchy-Schwarz over cells, and it must be the
`G`-native form `setIntegral_norm_sq_sum_le_card_mul_of_setIntegral`.  Enlarging
to `(-T)..T`, as the level-one error term does, would discard `hlarge` — the
previous level's polynomial is large only on `G` — and with it the entire
saving.  That is the reason the two Cauchy-Schwarz lemmas both exist.

`large` and the moment factor are shared across cells; only `small` varies, so
the estimate could be presented with the constant pulled out of the sum.  It is
left inside to match the shape of the level-one leg, which the partition
assembly consumes uniformly. -/
theorem setIntegral_norm_sq_level_sum_of_prev_large_le
    (Y : Finset ℕ) (hY : ∀ p ∈ Y, p.Prime) (P : ℕ) (hP : 1 ≤ P)
    (hlo : ∀ p ∈ Y, P < p) (hhi : ∀ p ∈ Y, p ≤ 2*P)
    (b : ℕ → ℂ) (hb : ∀ p, ‖b p‖ ≤ 1) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (A' Δ' : ℕ) (hA' : 1 ≤ A') (hΔ' : Δ' ≤ A')
    (I : Finset ℕ) (S : ℕ → Finset ℕ)
    (hS : ∀ v ∈ I, S v ⊆ Finset.Ioc A' (A'+Δ'))
    (a : ℕ → ℂ) (ha : ∀ m, ‖a m‖ ≤ 1)
    (Q : ℕ → ℝ → ℂ) (hQ : ∀ v ∈ I, Continuous (Q v))
    (T : ℝ) (hT : 0 < T) (G : Set ℝ) (hGm : MeasurableSet G)
    (hGT : G ⊆ Set.Ioc (-T) T)
    (small : ℕ → ℝ) (large : ℝ) (hlarge0 : 0 < large)
    (hsmall : ∀ v ∈ I, ∀ ξ ∈ G, ‖Q v ξ‖ ≤ small v)
    (hlarge : ∀ ξ ∈ G, large ≤ ‖∑ p ∈ Y, (b p/(p:ℂ))
        * ((Real.fourierChar (-(Real.log p * ξ)) : Circle) : ℂ)‖) :
    (∫ ξ in G, ‖∑ v ∈ I, Q v ξ * (∑ m ∈ S v, (a m/(m:ℂ))
        * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ))‖^2)
      ≤ (I.card : ℝ) * ∑ v ∈ I, (small v)^2/large^(2*ℓ)
          * (Real.exp Real.pi * (T/((P^ℓ*A' : ℕ):ℝ) + 2*((2^(ℓ+1) : ℕ):ℝ))
              * ((Nat.factorial ℓ : ℝ)^2
                  * (((2^(ℓ+1) : ℕ):ℝ) * ((ℓ:ℝ)+1)
                      * (∑ p ∈ Y, (1:ℝ)/(p:ℝ))^ℓ))) := by
  classical
  have hchar : ∀ w : ℝ, Continuous fun ξ : ℝ =>
      ((Real.fourierChar (-(w * ξ)) : Circle) : ℂ) := fun w =>
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hblk : ∀ v : ℕ, Continuous fun ξ : ℝ =>
      ∑ m ∈ S v, (a m/(m:ℂ))
        * ((Real.fourierChar (-(Real.log m * ξ)) : Circle) : ℂ) := fun v =>
    continuous_finset_sum _ fun m _ => continuous_const.mul (hchar (Real.log m))
  exact setIntegral_norm_sq_sum_le_card_mul_of_setIntegral _ I
    (fun v hv => (hQ v hv).mul (hblk v)) T G hGm hGT _
    (fun v hv => band_energy_level_le_of_prev_large Y hY P hP hlo hhi b hb ℓ hℓ
      A' Δ' hA' hΔ' (S v) (hS v hv) a ha (Q v) (hQ v hv) T hT G hGm hGT
      (small v) large hlarge0 (hsmall v hv) hlarge)

end MoltResearch
