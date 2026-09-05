import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5InnerBandAssembly
import MoltResearch.Discrepancy.SmoothRankinTail

/-!
# Track R T0-7c: the exceptional cells at the sharp Halász cost, for every frequency

The inner-band schedule feeds its abstract-`δ` capstone
`band_energy_typicalS_le_of_cellUniform_fit` with, per exceptional cell `v`,
a pointwise bound `hδ : ∀ t, |t| ≤ T → ‖cell block polynomial at t‖ ≤ δ v`
(uniform in the frequency), its positivity, and the fit
`exceptionalCellScheduleCost … (δ v) ≤ κ_v·budget`.  VI-6/VI-8 supplied `δ v`
as `cellHalaszBound`, whose Halász input was the shell budget at a fixed strength
`2D` on `[10¹⁶, 3(A+Δ)]` — `loglog`-lossy at fixed strength (Finding C), and with
the untwisted Abel factor `3 + 2πT`.

This leaf supplies the sharp `δ`:

* `halaszM_mono`, `halaszWindowAt_twist_of_top` — from the interface's single
  top-scale `NonPretentiousAt g A₀ N`, the Halász window of `g·n^{−2πit}` at
  strength `2D` at every scale `u ∈ [x₀, N]`, for **every** `|t| ≤ T` with
  `2πT + 2π(halaszM N + 1) ≤ A₀·N`, as soon as
  `2D ≤ A₀ − 2(loglog N − loglog x₀ + 12)` (the bridge
  `halaszWindowAt_archTwist_of_nonPretentiousAt`; no minimiser `t₁`, no `𝒯₁`);
* `norm_cellBlock_poly_le_cellHalaszSharpBound(_of_top)` — the cell block
  polynomial is at most `cellHalaszSharpBound x₀ D δ₀ (A/q) ((A+Δ)/q) P rest`
  (`sum_cellBlockCoeff_Icc_eq` + `norm_typicalS_quot_block_poly_le_sharp`);
* `cellHalaszSharpBound_pos` — the positivity the capstone's `hδ0` asks for;
* `cellHalaszSharpBound_le_explicit` — the `ε`-form:
  `≤ 2^{#rest}·(2ε·e^{2E_P} + (log Bq + 1)·(Aq/x₀)^{−s}·exp(2∑_{p∈P} p^{−(1−s)}))`
  at strength `D ≥ D₀(ε)` and cutoff `x₀ ≥ x₀(ε)`, from `sharpRamareCost_le_eps`,
  `pSmoothHarmonicMass_le_exp_primeMass` and `prod_inv_one_sub_le_exp`.

Design report, "The `t₁`-split is unnecessary at fixed `ε`": these are the
`hδ`, `hδ0` and (through VI-9g's fixed-`ε` S6) the `hfitUCell` of a sharp
schedule capstone.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- `halaszM` is monotone in the scale. -/
theorem halaszM_mono {u N : ℕ} (hu : 1 ≤ u) (huN : u ≤ N) : halaszM u ≤ halaszM N := by
  unfold halaszM
  have hu0 : (0:ℝ) < u := by exact_mod_cast hu
  have hlog : Real.log (u:ℝ) ≤ Real.log (N:ℝ) :=
    Real.log_le_log hu0 (by exact_mod_cast huN)
  have hlog0 : 0 ≤ Real.log (u:ℝ) := Real.log_natCast_nonneg u
  have hpow : (Real.log (u:ℝ))^4 ≤ (Real.log (N:ℝ))^4 := pow_le_pow_left₀ hlog0 hlog 4
  have hceil : ⌈(Real.log (u:ℝ))^4⌉ ≤ ⌈(Real.log (N:ℝ))^4⌉ := Int.ceil_le_ceil hpow
  exact Int.toNat_le_toNat (by omega)

/-- **The window at every frequency of the band, from the top scale** (Track R,
T0-7c): if `g` is `A₀`-non-pretentious at the top scale `N`, the band and the
Halász window fit inside the range (`2πT + 2π(halaszM N + 1) ≤ A₀·N`), and the
strength survives the descent to `x₀` (`2D ≤ A₀ − 2(loglog N − loglog x₀ + 12)`),
then for every `|t| ≤ T` and every scale `x₀ ≤ u ≤ N` the twisted function
`g·n^{−2πit}` satisfies the Halász window at strength `2D`. -/
theorem halaszWindowAt_twist_of_top (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (A₀ : ℝ) (N : ℕ) (hNP : NonPretentiousAt g A₀ N) (h1A₀ : 1 ≤ A₀)
    (T : ℝ)
    (hrange : 2 * Real.pi * T + 2 * Real.pi * (((halaszM N : ℕ):ℝ) + 1) ≤ A₀ * (N:ℝ))
    (x0 : ℕ) (hx04 : 4 ≤ x0) (D : ℝ)
    (hstrength : 2 * D ≤ A₀ - 2 * (Real.log (Real.log (N:ℝ))
      - Real.log (Real.log (x0:ℝ)) + 12))
    (t : ℝ) (ht : |t| ≤ T) (u : ℕ) (hx0u : x0 ≤ u) (huN : u ≤ N) :
    HalaszWindowAt (fun n => g n * (n:ℂ)^(Complex.I*((-(2 * Real.pi * t) : ℝ):ℂ)))
      (2 * D) u := by
  have hu4 : 4 ≤ u := le_trans hx04 hx0u
  refine halaszWindowAt_archTwist_of_nonPretentiousAt hg hNP h1A₀ hu4 huN
    (2 * Real.pi * t) ?_ (2 * D) ?_
  · have h1 : |2 * Real.pi * t| ≤ 2 * Real.pi * T := by
      rw [abs_mul, abs_of_pos Real.two_pi_pos]
      exact mul_le_mul_of_nonneg_left ht Real.two_pi_pos.le
    have h2 : ((halaszM u : ℕ):ℝ) ≤ ((halaszM N : ℕ):ℝ) := by
      exact_mod_cast halaszM_mono (by omega) huN
    have h3 : 2 * Real.pi * (((halaszM u : ℕ):ℝ) + 1)
        ≤ 2 * Real.pi * (((halaszM N : ℕ):ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) Real.two_pi_pos.le
    linarith
  · have hx0R : (1:ℝ) < (x0:ℝ) := by exact_mod_cast (by omega : 1 < x0)
    have hlogx0 : 0 < Real.log (x0:ℝ) := Real.log_pos hx0R
    have hll : Real.log (Real.log (x0:ℝ)) ≤ Real.log (Real.log (u:ℝ)) :=
      Real.log_le_log hlogx0 (Real.log_le_log (by linarith) (by exact_mod_cast hx0u))
    linarith

/-- **The cell block polynomial at the sharp cost** (Track R, T0-7c): the mirror
of `norm_cellBlock_poly_le_cellHalaszBound` with the windowed sharp recut, the
window demanded only on long quotients. -/
theorem norm_cellBlock_poly_le_cellHalaszSharpBound (g : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC g) (hg : ∀ n, ‖g n‖ ≤ 1) (h1 : g 1 = 1)
    (A Δ q : ℕ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (hrest : ∀ Q ∈ rest, ∀ p ∈ Q, p.Prime)
    (x0 : ℕ) (hx0 : cellHalaszThreshold ≤ x0)
    (D : ℝ) (hD : 1 ≤ D) (δ₀ : ℝ) (hδ0 : 0 < δ₀) (hδ1 : δ₀ ≤ 1) (t : ℝ)
    (hwin : ∀ n1 ∈ (Finset.Icc 1 ((A + Δ) / q)).filter (fun n => n.primeFactors ⊆ P),
      x0 ≤ (A / q) / n1 →
      ∀ u : ℕ, (A / q) / n1 ≤ u → u ≤ 3 * (((A + Δ) / q) / n1) →
        HalaszWindowAt
          (fun n => g n * (n:ℂ)^(Complex.I*((-(2 * Real.pi * t) : ℝ):ℂ))) (2 * D) u) :
    ‖∑ n ∈ Finset.Icc 1 ((A + Δ) / q),
        (cellBlockCoeff g A (A + Δ) P rest q n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
      ≤ cellHalaszSharpBound x0 D δ₀ (A / q) ((A + Δ) / q) P rest := by
  rw [sum_cellBlockCoeff_Icc_eq]
  exact norm_typicalS_quot_block_poly_le_sharp g hcm h1 hg A (A + Δ) q
    (Nat.le_add_right A Δ) P hP rest hrest x0 hx0 D hD t hwin δ₀ hδ0 hδ1

/-- **The same, from the top scale alone** (Track R, T0-7c): the window
hypotheses discharged by `halaszWindowAt_twist_of_top` for a single top scale
`N ≥ 3·((A+Δ)/q)`, uniformly for every `|t| ≤ T`. -/
theorem norm_cellBlock_poly_le_cellHalaszSharpBound_of_top (g : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC g) (hg : ∀ n, ‖g n‖ ≤ 1) (h1 : g 1 = 1)
    (A Δ q : ℕ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (rest : List (Finset ℕ)) (hrest : ∀ Q ∈ rest, ∀ p ∈ Q, p.Prime)
    (x0 : ℕ) (hx0 : cellHalaszThreshold ≤ x0)
    (D : ℝ) (hD : 1 ≤ D) (δ₀ : ℝ) (hδ0 : 0 < δ₀) (hδ1 : δ₀ ≤ 1)
    (A₀ : ℝ) (N : ℕ) (hNP : NonPretentiousAt g A₀ N) (h1A₀ : 1 ≤ A₀)
    (hN : 3 * ((A + Δ) / q) ≤ N)
    (T : ℝ)
    (hrange : 2 * Real.pi * T + 2 * Real.pi * (((halaszM N : ℕ):ℝ) + 1) ≤ A₀ * (N:ℝ))
    (hstrength : 2 * D ≤ A₀ - 2 * (Real.log (Real.log (N:ℝ))
      - Real.log (Real.log (x0:ℝ)) + 12))
    (t : ℝ) (ht : |t| ≤ T) :
    ‖∑ n ∈ Finset.Icc 1 ((A + Δ) / q),
        (cellBlockCoeff g A (A + Δ) P rest q n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖
      ≤ cellHalaszSharpBound x0 D δ₀ (A / q) ((A + Δ) / q) P rest := by
  have hx04 : 4 ≤ x0 := le_trans (by norm_num [cellHalaszThreshold]) hx0
  apply norm_cellBlock_poly_le_cellHalaszSharpBound g hcm hg h1 A Δ q P hP rest hrest
    x0 hx0 D hD δ₀ hδ0 hδ1 t
  intro n1 _ hlong u hu1 hu2
  have huN : u ≤ N :=
    le_trans hu2 (le_trans (Nat.mul_le_mul_left 3 (Nat.div_le_self _ _)) hN)
  exact halaszWindowAt_twist_of_top g hg A₀ N hNP h1A₀ T hrange x0 hx04 D hstrength
    t ht u (le_trans hlong hu1) huN

/-- **The sharp cell bound is strictly positive** on a nonempty block: the
`n₁ = 1` term of the Ramaré sum is positive (a long block has cost
`2·(… + 1)/(a+1) > 0`, a short one the harmonic mass of a nonempty block), and
every other term is nonnegative. -/
theorem cellHalaszSharpBound_pos (x0 : ℕ) (hx0 : cellHalaszThreshold ≤ x0)
    (D δ₀ : ℝ) (hD : 0 ≤ D) (hδ0 : 0 < δ₀)
    (Aq Bq : ℕ) (hAq : 1 ≤ Aq) (hAB : Aq < Bq)
    (P : Finset ℕ) (rest : List (Finset ℕ)) :
    0 < cellHalaszSharpBound x0 D δ₀ Aq Bq P rest := by
  classical
  unfold cellHalaszSharpBound
  have hpow : (0:ℝ) < ((2 ^ rest.length : ℕ) : ℝ) := by positivity
  have hone : 1 ∈ (Finset.Icc 1 Bq).filter (fun n => n.primeFactors ⊆ P) := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_refl 1, by omega⟩, by simp⟩
  -- the `n₁ = 1` term
  have hcost1 : 0 < (1:ℝ) / (1:ℕ) * sharpQuotientCost x0 D δ₀ (Aq / 1) (Bq / 1) := by
    rw [Nat.div_one, Nat.div_one, Nat.cast_one, div_one, one_mul]
    unfold sharpQuotientCost
    split_ifs with hlong
    · unfold sharpTwistedDirichletCost sharpPartialBudget
      have hBq3 : Real.exp 1 ≤ 3 * (Bq:ℝ) := by
        have : (1:ℝ) ≤ (Bq:ℝ) := by exact_mod_cast (by omega : 1 ≤ Bq)
        linarith [Real.exp_one_lt_d9.le]
      have hbud := halaszBudgetSharp_nonneg D (3 * (Bq:ℝ)) hD hBq3
      have hloga : 0 < Real.log (Aq:ℝ) := by
        have h16 : (10:ℝ)^16 ≤ (Aq:ℝ) := by
          have : cellHalaszThreshold ≤ Aq := le_trans hx0 hlong
          unfold cellHalaszThreshold at this
          exact_mod_cast this
        exact Real.log_pos (by linarith)
      have h1' : (0:ℝ) ≤ 2 * halaszBudgetSharp D (3 * (Bq:ℝ)) / (δ₀ * Real.log (Aq:ℝ)) := by
        positivity
      have h2' : (0:ℝ) ≤ Real.exp 1 * (Bq:ℝ) * δ₀ := by positivity
      have hden : (0:ℝ) < ((Aq + 1 : ℕ):ℝ) := by positivity
      apply div_pos _ hden
      linarith
    · unfold cellHalaszTrivialCost
      refine Finset.sum_pos' (fun n _ => by positivity) ⟨Bq, ?_, ?_⟩
      · rw [Finset.mem_Ioc]
        exact ⟨hAB, le_refl _⟩
      · have : (0:ℝ) < (Bq:ℝ) := by exact_mod_cast (by omega : 0 < Bq)
        positivity
  have hsum : 0 < sharpRamareCost x0 D δ₀ Aq Bq P := by
    unfold sharpRamareCost
    refine lt_of_lt_of_le hcost1 (Finset.single_le_sum (f := fun n1 =>
      (1:ℝ) / n1 * sharpQuotientCost x0 D δ₀ (Aq / n1) (Bq / n1)) ?_ hone)
    intro n1 hn1
    rw [Finset.mem_filter, Finset.mem_Icc] at hn1
    have hab : Aq / n1 ≤ Bq / n1 := Nat.div_le_div_right hAB.le
    exact mul_nonneg (by positivity) (sharpQuotientCost_nonneg x0 hx0 D δ₀ _ _ hD hδ0 hab)
  positivity

/-- **The sharp cell bound in `ε`-form** (Track R, T0-7c): for every `ε > 0`
there are `D₀ ≥ 1` and `x₀ ≥ 10¹⁶` such that at `δ₀ = ε/(8e)`, for every
strength `D ≥ D₀`, cutoff `x₀' ≥ x₀`, block `1 ≤ Aq ≤ Bq ≤ 2Aq+1`, prime set `P`
with `p^{−(1−s)} ≤ 1/2` (`0 < s < 1`), and every `rest`,

  `cellHalaszSharpBound x₀' D (ε/(8e)) Aq Bq P rest
     ≤ 2^{#rest}·(2ε·exp(2∑_{p∈P} 1/p) + (log Bq + 1)·(Aq/x₀')^{−s}·exp(2∑_{p∈P} p^{−(1−s)}))`. -/
theorem cellHalaszSharpBound_le_explicit (ε : ℝ) (hε : 0 < ε) :
    ∃ (D₀ : ℝ) (x₀ : ℕ), 1 ≤ D₀ ∧ 10^16 ≤ x₀ ∧
      ∀ D : ℝ, D₀ ≤ D → ∀ x0 : ℕ, x₀ ≤ x0 →
      ∀ Aq Bq : ℕ, 1 ≤ Aq → Aq ≤ Bq → Bq ≤ 2 * Aq + 1 →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ∀ s : ℝ, 0 < s → s < 1 → (∀ p ∈ P, (p:ℝ) ^ (-(1 - s)) ≤ 1 / 2) →
      ∀ rest : List (Finset ℕ),
        cellHalaszSharpBound x0 D (ε / (8 * Real.exp 1)) Aq Bq P rest
          ≤ ((2 ^ rest.length : ℕ) : ℝ)
            * (2 * ε * Real.exp (2 * ∑ p ∈ P, (1:ℝ) / p)
              + (Real.log (Bq:ℝ) + 1)
                * (((Aq:ℝ) / x0) ^ (-s) * Real.exp (2 * ∑ p ∈ P, (p:ℝ) ^ (-(1 - s))))) := by
  obtain ⟨D₀, x₀, hD₀, hx₀, hram⟩ := sharpRamareCost_le_eps ε hε
  refine ⟨D₀, x₀, hD₀, hx₀, ?_⟩
  intro D hD x0 hx0 Aq Bq hAq hAB hB P hP s hs0 hs1 hhalf rest
  unfold cellHalaszSharpBound
  have hpow : (0:ℝ) ≤ ((2 ^ rest.length : ℕ) : ℝ) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hpow
  have h1 := hram D hD x0 hx0 Aq Bq hAq hAB hB P hP s hs0 hs1
  have hmass := pSmoothHarmonicMass_le_exp_primeMass Bq P hP
  have hprod := prod_inv_one_sub_le_exp P (fun p => (p:ℝ) ^ (-(1 - s)))
    (fun p _ => by positivity) hhalf
  have hlogB : 0 ≤ Real.log (Bq:ℝ) + 1 := by
    have : (1:ℝ) ≤ (Bq:ℝ) := by exact_mod_cast le_trans hAq hAB
    linarith [Real.log_nonneg this]
  have hy0 : (0:ℝ) ≤ ((Aq:ℝ) / x0) ^ (-s) := by positivity
  have h2 : (Real.log (Bq:ℝ) + 1)
        * (((Aq:ℝ) / x0) ^ (-s) * ∏ p ∈ P, (1 - (p:ℝ) ^ (-(1 - s)))⁻¹)
      ≤ (Real.log (Bq:ℝ) + 1)
        * (((Aq:ℝ) / x0) ^ (-s) * Real.exp (2 * ∑ p ∈ P, (p:ℝ) ^ (-(1 - s)))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod hy0) hlogB
  have h3 : 2 * ε * pSmoothHarmonicMass Bq P
      ≤ 2 * ε * Real.exp (2 * ∑ p ∈ P, (1:ℝ) / p) :=
    mul_le_mul_of_nonneg_left hmass (by positivity)
  linarith

end Tao2015

end MoltResearch
