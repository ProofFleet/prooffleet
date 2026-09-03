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

open MeasureTheory Finset ExpSums in
/-- **A2-III VI-1d-1a — every unit cell has a maximising sample point.**

For a continuous `F` and any finite family of integer cells there is a choice
function `τ` picking, from each cell `[k, k+1]`, a point at which `‖F‖` attains
its maximum on that cell.  Compactness of `Icc` and continuity of `‖F‖`; the
content is only that the choice is made uniformly in `k`, which is what a
`Finset`-indexed sum downstream needs.

The maximiser is taken over the *closed* cell while the covering family is
half-open, and that mismatch is deliberate: `Ico` cells tile the line, so the
integral splits over them with no overlap, while `Icc` is what carries the
maximum.  `Ico ⊆ Icc` reconciles the two for free. -/
theorem exists_cell_max_sample (F : ℝ → ℂ) (hFc : Continuous F) :
    ∃ τ : ℤ → ℝ, (∀ k : ℤ, τ k ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1)) ∧
      ∀ k : ℤ, ∀ v ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1), ‖F v‖ ≤ ‖F (τ k)‖ := by
  classical
  have hchoice : ∀ k : ℤ, ∃ t, t ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1) ∧
      ∀ v ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1), ‖F v‖ ≤ ‖F t‖ := by
    intro k
    obtain ⟨t, ht, hmax⟩ :=
      (isCompact_Icc (a := (k : ℝ)) (b := (k : ℝ) + 1)).exists_isMaxOn
        (Set.nonempty_Icc.mpr (by linarith)) hFc.norm.continuousOn
    exact ⟨t, ht, fun v hv => isMaxOn_iff.mp hmax v hv⟩
  choose τ hmem hmax using hchoice
  exact ⟨τ, hmem, hmax⟩

open MeasureTheory Finset ExpSums in
/-- **A2-III VI-1d-1 — the discretisation, tail-free.**

  `∫_G ‖F‖² ≤ ∑_{t ∈ 𝒯even} ‖F t‖² + ∑_{t ∈ 𝒯odd} ‖F t‖²`

for a family of integer cells covering `G`, with **no derivative correction**.

This is the same statement as `setIntegral_norm_sq_le_two_separated` (IV-3d-3)
with the term `∑_{k ∈ K} ∫_k^{k+1} 2‖F‖‖F′‖` deleted, and the deletion is not a
sharpening of that lemma's proof but a change of tool.  IV-3d-3 prices
`∫_{cell} ‖F‖²` by the value of `F` at an *arbitrary* point of the cell, which
is Gallagher's Sobolev inequality and costs the derivative.  A cell has length
**one**, so if the sample point is chosen to *maximise* `‖F‖` on the cell —
which `exists_cell_max_sample` does — then `∫_{cell} ‖F‖² ≤ max_{cell} ‖F‖²`
outright and nothing is owed.

**Why this matters rather than merely tidying.**  The `𝒰` leg is the one leg of
the A.2 band estimate with no margin (`BandSchedule.exceptional_report_exponent_ok`:
the gap `2/625 − 1/320 = 3/40000` is spent exactly on the leg's constant).  The
Gallagher remainder is not payable inside it: pricing it by the sharp mean value
theorem on the full range gives `≍ log(PN)` times the *trivial* energy, against a
main term that is `(log A)^{−1/50}` times the trivial energy; and pricing it
`𝒰`-aware — applying the large-values machinery to `F′`, whose coefficients are
`2π log n` times those of `F` — still loses one factor `log(2PN)`.  Either way the
correction dominates the saving it was supposed to correct.  So the tail had to
go, and this is how it goes.

The factor `2` — the two parity classes — is untouched, and is still `[MR]`'s:
distinct integers of one parity differ by at least `2`, so each family is
`1`-separated, which is what the large-values interfaces require.  Only the
third summand disappears.

`τ` is existentially quantified rather than taken as a parameter because its
defining property (maximality on its cell) is not something a consumer can be
asked to supply; the consumer needs only membership, which is returned alongside
and is all the separation and frequency-range hypotheses downstream consume. -/
theorem setIntegral_norm_sq_le_two_separated_max (F : ℝ → ℂ) (hFc : Continuous F)
    (G : Set ℝ) (K : Finset ℤ)
    (hcover : G ⊆ ⋃ k ∈ K, Set.Ico (k : ℝ) ((k : ℝ) + 1)) :
    ∃ τ : ℤ → ℝ, (∀ k ∈ K, τ k ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1)) ∧
      (∫ ξ in G, ‖F ξ‖ ^ 2)
        ≤ (∑ t ∈ (K.filter (fun k => Even k)).image τ, ‖F t‖ ^ 2)
          + (∑ t ∈ (K.filter (fun k => ¬ Even k)).image τ, ‖F t‖ ^ 2) := by
  classical
  obtain ⟨τ, hτmem, hτmax⟩ := exists_cell_max_sample F hFc
  refine ⟨τ, fun k _ => hτmem k, ?_⟩
  have hsq : Continuous fun ξ : ℝ => ‖F ξ‖ ^ 2 := hFc.norm.pow 2
  have hnn : ∀ ξ : ℝ, 0 ≤ ‖F ξ‖ ^ 2 := fun ξ => sq_nonneg _
  have hint : ∀ k : ℤ, IntegrableOn (fun ξ : ℝ => ‖F ξ‖ ^ 2)
      (Set.Ico (k : ℝ) ((k : ℝ) + 1)) := fun k =>
    (hsq.integrableOn_Icc).mono_set Set.Ico_subset_Icc_self
  -- Distinct integer cells are disjoint.
  have hdisj : Set.Pairwise (↑K)
      (Function.onFun Disjoint fun k : ℤ => Set.Ico (k : ℝ) ((k : ℝ) + 1)) := by
    intro k _ l _ hkl
    show Disjoint (Set.Ico (k : ℝ) ((k : ℝ) + 1)) (Set.Ico (l : ℝ) ((l : ℝ) + 1))
    rw [Set.disjoint_left]
    intro x hx hx'
    rcases lt_or_gt_of_ne hkl with h | h
    · have : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr h)
      linarith [hx.2, hx'.1]
    · have : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr h)
      linarith [hx'.2, hx.1]
  -- Step 1: split the integral over the cells.
  have hsplit := setIntegral_le_sum_of_cover (fun ξ => ‖F ξ‖ ^ 2) hnn G K
    (fun k : ℤ => Set.Ico (k : ℝ) ((k : ℝ) + 1))
    (fun k _ => measurableSet_Ico) hdisj hcover (fun k _ => hint k)
  -- Step 2: a unit cell's integral is at most its maximum.
  have hcell : ∀ k : ℤ, (∫ ξ in Set.Ico (k : ℝ) ((k : ℝ) + 1), ‖F ξ‖ ^ 2)
      ≤ ‖F (τ k)‖ ^ 2 := by
    intro k
    have hmono : (∫ ξ in Set.Ico (k : ℝ) ((k : ℝ) + 1), ‖F ξ‖ ^ 2)
        ≤ ∫ _ξ in Set.Ico (k : ℝ) ((k : ℝ) + 1), ‖F (τ k)‖ ^ 2 := by
      have hfin : volume (Set.Ico (k : ℝ) ((k : ℝ) + 1)) ≠ ⊤ := by
        rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top
      refine setIntegral_mono_on (hint k) (integrableOn_const hfin) measurableSet_Ico ?_
      intro v hv
      have hle := hτmax k v (Set.Ico_subset_Icc_self hv)
      have h0 : (0 : ℝ) ≤ ‖F v‖ := norm_nonneg _
      nlinarith [norm_nonneg (F (τ k))]
    rwa [setIntegral_const, Real.volume_real_Ico_of_le (by linarith),
      add_sub_cancel_left, one_smul] at hmono
  -- Step 3: the two parity classes recombine.
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
  rw [sum_image_sample_eq _ τ (fun t => ‖F t‖ ^ 2)
      (fun k hk => hτmem k) hgapE,
    sum_image_sample_eq _ τ (fun t => ‖F t‖ ^ 2)
      (fun k hk => hτmem k) hgapO,
    Finset.sum_filter_add_sum_filter_not]
  exact hsplit.trans (Finset.sum_le_sum fun k _ => hcell k)

open MeasureTheory Finset ExpSums in
/-- **A2-III VI-1d-1′ — the tail-free discretisation for a product.**

The form the `𝒰` leg consumes: the band integrand there is `‖Q‖²‖R‖²` for a
prime polynomial `Q` and an integer polynomial `R`, and the large-values
interfaces price the two factors separately at each sample point.  Same
statement as `setIntegral_norm_sq_mul_le_two_separated` (IV-3d-3′) with the
derivative correction gone, and with the `HasDerivAt` hypotheses gone with it —
continuity of the two factors is now the whole input. -/
theorem setIntegral_norm_sq_mul_le_two_separated_max (Q R : ℝ → ℂ)
    (hQc : Continuous Q) (hRc : Continuous R)
    (G : Set ℝ) (K : Finset ℤ)
    (hcover : G ⊆ ⋃ k ∈ K, Set.Ico (k : ℝ) ((k : ℝ) + 1)) :
    ∃ τ : ℤ → ℝ, (∀ k ∈ K, τ k ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1)) ∧
      (∫ ξ in G, ‖Q ξ‖ ^ 2 * ‖R ξ‖ ^ 2)
        ≤ (∑ t ∈ (K.filter (fun k => Even k)).image τ, ‖Q t‖ ^ 2 * ‖R t‖ ^ 2)
          + (∑ t ∈ (K.filter (fun k => ¬ Even k)).image τ,
              ‖Q t‖ ^ 2 * ‖R t‖ ^ 2) := by
  obtain ⟨τ, hmem, hbd⟩ := setIntegral_norm_sq_le_two_separated_max
    (fun ξ => Q ξ * R ξ) (hQc.mul hRc) G K hcover
  refine ⟨τ, hmem, ?_⟩
  simpa only [norm_mul, mul_pow] using hbd


end MoltResearch
