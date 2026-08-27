import MoltResearch.Discrepancy.RieszCapstone
import MoltResearch.Discrepancy.HalaszTripleG

/-!
# Track C: the Riesz capstone through the smooth tsum (Track R, M0R-5)

The capstone chain of `RieszCapstone.lean`, rewired through
`tripleConvR_le'`: the per-block sharp estimate with the band sup
demanded of the smooth phase sum — the truncated Euler product — rather
than the finite `ghsMainPoly`.  The `b`-parametric assembly
`rieszMean_log_le_of_nonPretentious` already exists at the full Riesz
mean; this file rebuilds its per-block input so that `b` can be
instantiated log-freely by `norm_smoothPhaseSum_le_of_nonPretentious`,
with the tail priced at the smooth mass (`smooth_mass_le`) instead of
the harmonic sum over `Icc 1 x`.
-/

namespace MoltResearch

open MeasureTheory Real Complex Finset in
/-- **The per-block sharp estimate through the smooth tsum** (Track R,
M0R-5): `tripleConvR_block_sharp_le` with the `hBu` slot moved to
`smoothPhaseSum` and the tail mass priced at the smooth mass.  The
suppliers (`ghsBlock_E1_riesz_block_le`,
`ghsPrimePoly_unit_energy_primesBelow_le`) are untouched; only the §4
step changes, through `tripleConvR_le'`.  Complete multiplicativity is
the one new price — the Euler product needs it. -/
theorem tripleConvR_block_sharp_le' (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (hmul : ∀ a b, f (a*b) = f a * f b) (h1 : f 1 = 1)
    (x k : ℕ) (hx : 2 ≤ x) (hk : 1 ≤ k) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k)
    (hfit : 2 * blockHi x k ≤ x)
    (hX3 : 3 ≤ x / blockLo x k)
    (T : ℝ) (hT : 5 ≤ T) (hPT : ∀ p ∈ P, T^2 ≤ (p:ℝ))
    (b : ℝ) (hb0 : 0 ≤ b)
    (hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖ExpSums.smoothPhaseSum (fun n => ((f n : ℝ) : ℂ)) x t‖ ≤ b) :
    |tripleConvR f x P|
      ≤ (x:ℝ) * Real.sqrt
          ((Real.exp π *
              (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
                  * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ))
                        * Real.log (x:ℝ) + Real.log 2) + 4 * Real.log 4))
                + T * (6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
                    * (16/(Real.log (x:ℝ))^2
                        + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
            + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
                * (1/(2*Real.pi^2*T)))
          * (5 * (2 * (Real.exp π * (12290
                * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
                + 4*T * (6144 + Real.exp (-(π*T^2/64))
                    * (((x / blockLo x k : ℕ):ℝ) * Real.log 4))))
              + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
                    (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
                  Real.log (q:ℝ)/(q:ℝ))^2)
              * (6*b^2)
            + (∑ q ∈ (x / blockLo x k).primesBelow,
                  Real.log (q:ℝ)/(q:ℝ))^2
                * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2
                * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))))
        + 2*(x:ℝ)*Real.log 4 := by
  classical
  have hx1 : 1 ≤ x := by omega
  obtain ⟨hlo1, hlohi⟩ := blockLo_le_blockHi x k hx1
  have hfc : ∀ n, ‖((f n : ℝ) : ℂ)‖ ≤ 1 := by
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hf n
  have hcm : CompletelyMultiplicativeC (fun n => ((f n : ℝ) : ℂ)) := by
    intro a b _ _
    show ((f (a*b) : ℝ) : ℂ) = ((f a : ℝ) : ℂ) * ((f b : ℝ) : ℂ)
    rw [hmul]
    push_cast
    ring
  have h1c : ((f 1 : ℝ) : ℂ) = 1 := by
    rw [h1]
    norm_num
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have h2p : ∀ p ∈ P, 2*p ≤ x := by
    intro p hp
    obtain ⟨-, -, hpB⟩ := hP p hp
    omega
  have hX2 : 2 ≤ x / blockLo x k := by omega
  -- the enlarged inner range
  have hQp : ∀ q ∈ (x / blockLo x k).primesBelow, q.Prime :=
    fun q hq => (Nat.mem_primesBelow.mp hq).2
  have hQpos : ∀ q ∈ (x / blockLo x k).primesBelow, 0 < q :=
    fun q hq => (hQp q hq).pos
  have hQsub : ∀ p ∈ P, (x/p).primesBelow ⊆ (x / blockLo x k).primesBelow := by
    intro p hp q hq
    obtain ⟨-, hlop, -⟩ := hP p hp
    rw [Nat.mem_primesBelow] at hq ⊢
    exact ⟨lt_of_lt_of_le hq.1 (Nat.div_le_div_left hlop (by omega)), hq.2⟩
  -- positivity of the block energy
  have hlogx : (0:ℝ) < Real.log (x:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 2 ≤ x))
  have he1 : (0:ℝ) < Real.exp 1 - 1 := by
    have := Real.add_one_le_exp (1:ℝ)
    linarith
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hT0 : (0:ℝ) < T := by linarith
  have hsqx : (0:ℝ) < Real.sqrt ((Nat.sqrt x : ℕ):ℝ) := by
    refine Real.sqrt_pos.mpr ?_
    have : 1 ≤ Nat.sqrt x := by
      have := Nat.sqrt_pos.mpr (by omega : 0 < x)
      omega
    exact_mod_cast this
  have hE₁0 : (0:ℝ) < Real.exp π *
      (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
          * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ))
                * Real.log (x:ℝ) + Real.log 2) + 4 * Real.log 4))
        + T * (6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
            * (16/(Real.log (x:ℝ))^2
                + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
      + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
          * (1/(2*Real.pi^2*T)) := by
    have hA : (0:ℝ) < 12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
        * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ))
              * Real.log (x:ℝ) + Real.log 2) + 4 * Real.log 4)) := by
      have h1 : (0:ℝ) < (Real.exp 1 - 1) * Real.exp (-(k:ℝ))
          * Real.log (x:ℝ) := by positivity
      positivity
    have hB' : (0:ℝ) ≤ T * (6144 + Real.exp (-(π*T^2/64))
        * ((x:ℝ) * Real.log 4))
        * (16/(Real.log (x:ℝ))^2
            + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)) := by
      positivity
    have hC : (0:ℝ) ≤ (∑ p ∈ P, Real.log (p:ℝ)
        /((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2 * (1/(2*Real.pi^2*T)) := by
      positivity
    nlinarith [Real.exp_pos π, mul_pos (Real.exp_pos π) hA,
      mul_nonneg (Real.exp_pos π).le hB']
  -- non-negativity of the unit-interval energy
  have hV₃0 : (0:ℝ) ≤ 2 * (Real.exp π * (12290
        * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
        + 4*T * (6144 + Real.exp (-(π*T^2/64))
            * (((x / blockLo x k : ℕ):ℝ) * Real.log 4))))
      + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
            (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
          Real.log (q:ℝ)/(q:ℝ))^2 := by
    have hlogX1 : (0:ℝ) ≤ Real.log ((x / blockLo x k + 1 : ℕ):ℝ) :=
      Real.log_natCast_nonneg _
    positivity
  -- strict positivity of the tail mass: `2` is in the inner range
  have h2mem : 2 ∈ (x / blockLo x k).primesBelow :=
    Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩
  have hQsum : (0:ℝ) < ∑ q ∈ (x / blockLo x k).primesBelow,
      Real.log (q:ℝ)/(q:ℝ) := by
    have hle : Real.log ((2:ℕ):ℝ)/((2:ℕ):ℝ)
        ≤ ∑ q ∈ (x / blockLo x k).primesBelow, Real.log (q:ℝ)/(q:ℝ) :=
      Finset.single_le_sum
        (fun q _ => div_nonneg (Real.log_natCast_nonneg q)
          (Nat.cast_nonneg q)) h2mem
    have h2 : (0:ℝ) < Real.log ((2:ℕ):ℝ)/((2:ℕ):ℝ) := by
      have : ((2:ℕ):ℝ) = (2:ℝ) := by norm_num
      rw [this]
      positivity
    linarith
  have hsummass : Summable
      (fun m : (Nat.smoothNumbers x) => (((m : ℕ) : ℝ))⁻¹) := by
    have hone : CompletelyMultiplicativeC (fun _ : ℕ => (1:ℂ)) :=
      fun a b _ _ => by simp
    refine (ExpSums.summable_norm_smooth_phase (fun _ => 1) hone rfl
      (fun n => by simp) x 0).congr fun m => ?_
    rw [norm_mul, norm_mul, norm_eq_of_mem_sphere, mul_one, norm_one,
      one_mul, norm_inv, Complex.norm_natCast]
  have hnsum : (0:ℝ) < ∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹ := by
    have h1mem : (1:ℕ) ∈ Nat.smoothNumbers x :=
      Nat.mem_smoothNumbers_of_lt one_pos (by omega)
    refine hsummass.tsum_pos (fun m => by positivity) ⟨1, h1mem⟩ ?_
    show (0:ℝ) < (((1:ℕ):ℝ))⁻¹
    norm_num
  have hMtail0 : (0:ℝ) < (∑ q ∈ (x / blockLo x k).primesBelow,
        Real.log (q:ℝ)/(q:ℝ))^2
      * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2
      * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2))) := by
    have hM : (0:ℝ) < ((halaszM x : ℕ):ℝ) + 1/2 := by positivity
    have hpi := Real.pi_pos
    positivity
  -- the suppliers
  have hE₁ := ghsBlock_E1_riesz_block_le (fun n => ((f n : ℝ) : ℂ)) hfc
    x k hx hk P T hT hP hfit hPT
  have hV : ∀ N ∈ halaszRange x,
      (∫ t in ((N:ℝ) - 1/2)..((N:ℝ) + 1/2),
        ‖ghsPrimePoly (fun n => ((f n : ℝ) : ℂ))
          (x / blockLo x k).primesBelow t‖^2)
      ≤ 2 * (Real.exp π * (12290
            * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
            + 4*T * (6144 + Real.exp (-(π*T^2/64))
                * (((x / blockLo x k : ℕ):ℝ) * Real.log 4))))
          + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
                (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
              Real.log (q:ℝ)/(q:ℝ))^2 :=
    fun N _ => ghsPrimePoly_unit_energy_primesBelow_le
      (fun n => ((f n : ℝ) : ℂ)) hfc (x / blockLo x k) hX2 T hT (N:ℝ)
  exact tripleConvR_le' f hf hcm h1 x hx P hPp h2p
    (x / blockLo x k).primesBelow hQp hQpos hQsub
    _ _ _ b _ hE₁0 hb0 hV₃0 hMtail0
    (fun ξ => ExpSums.norm_smoothPhaseSum_le
      (fun n => ((f n : ℝ) : ℂ)) hcm h1c hfc x ξ)
    hE₁ hBu hV le_rfl

open Real in
/-- **The band weight against the smooth mass** (Track R, M0R-5c):

  `(1/(2π²(halaszM x + ½)))·(log²x·(∑'_{n x-smooth} 1/n)²) ≤ 2000`.

`bandWeight_mass_le_one` with the harmonic sum replaced by the smooth
mass.  The mass is `e⁵`-times larger (`smooth_mass_le`), so the old
`≤ 1` budget fails by the absolute factor `≈ e¹⁰/2π²`; the budget is
raised to `2000` — an absolute constant, which the balanced envelope
absorbs at the price of a constant factor and nothing else.  The band
`halaszM ≥ log⁴x + 1` pays for everything once `log x ≥ 8`. -/
theorem bandWeight_smooth_mass_le (x : ℕ) (hx : 3000 ≤ x) :
    (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))
      * ((Real.log (x:ℝ))^2
        * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2) ≤ 2000 := by
  have hx3 : 3 ≤ x := by omega
  have hL0 : (0:ℝ) < Real.log (x:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 2 ≤ x))
  have hπ2 : (9:ℝ) ≤ Real.pi^2 := by
    have := Real.pi_gt_three
    nlinarith
  -- `log x ≥ 8`, from `e⁸ ≤ 2981 ≤ x`
  have hL8 : (8:ℝ) ≤ Real.log (x:ℝ) := by
    have hx0 : (0:ℝ) < (x:ℝ) := by positivity
    rw [Real.le_log_iff_exp_le hx0]
    have he : Real.exp 1 ≤ (2.7182818286:ℝ) := Real.exp_one_lt_d9.le
    have h8 : Real.exp 8 = (Real.exp 1)^8 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have hpow : (Real.exp 1)^8 ≤ (2.7182818286:ℝ)^8 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he 8
    have hnum : (2.7182818286:ℝ)^8 ≤ 2981 := by norm_num
    have hxc : (2981:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 2981 ≤ x)
    linarith [h8 ▸ hpow]
  -- the mass, numerically
  have hmass := ExpSums.smooth_mass_le x hx3
  have hmass0 : (0:ℝ) ≤ ∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹ :=
    tsum_nonneg fun m => by positivity
  have he5 : Real.exp 5 ≤ (149:ℝ) := by
    have he : Real.exp 1 ≤ (2.7182818286:ℝ) := Real.exp_one_lt_d9.le
    have h5 : Real.exp 5 = (Real.exp 1)^5 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have hpow : (Real.exp 1)^5 ≤ (2.7182818286:ℝ)^5 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he 5
    have hnum : (2.7182818286:ℝ)^5 ≤ 149 := by norm_num
    linarith [h5 ▸ hpow]
  have hmass' : ∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹
      ≤ 149 * (2 + Real.log (x:ℝ)) := by
    refine le_trans hmass ?_
    have h2L : (0:ℝ) ≤ 2 + Real.log (x:ℝ) := by linarith
    exact mul_le_mul_of_nonneg_right he5 h2L
  -- the band dominates `L⁴ + 1`
  have hM : (Real.log (x:ℝ))^4 + 1 ≤ ((halaszM x : ℕ):ℝ) := by
    have h4 : (0:ℝ) ≤ (Real.log (x:ℝ))^4 := by positivity
    have hle := Int.le_ceil ((Real.log (x:ℝ))^4)
    have hnn : (0:ℤ) ≤ ⌈(Real.log (x:ℝ))^4⌉ + 1 := by
      have := Int.ceil_nonneg h4
      omega
    calc (Real.log (x:ℝ))^4 + 1
        ≤ ((⌈(Real.log (x:ℝ))^4⌉ : ℤ):ℝ) + 1 := by
          linarith
      _ = ((⌈(Real.log (x:ℝ))^4⌉ + 1 : ℤ):ℝ) := by push_cast; ring
      _ = (((⌈(Real.log (x:ℝ))^4⌉ + 1).toNat : ℕ):ℝ) := by
          rw [show ((((⌈(Real.log (x:ℝ))^4⌉ + 1).toNat : ℕ)):ℝ)
              = ((((⌈(Real.log (x:ℝ))^4⌉ + 1).toNat : ℕ) : ℤ):ℝ) by
            push_cast; ring,
            Int.toNat_of_nonneg hnn]
      _ = ((halaszM x : ℕ):ℝ) := by rw [halaszM]
  -- numerator against the band
  have hsq : (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2
      ≤ (149 * (2 + Real.log (x:ℝ)))^2 := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self hmass0 hmass'
  have hnum : (Real.log (x:ℝ))^2
      * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2
      ≤ 36000 * ((Real.log (x:ℝ))^4 + 1) := by
    have h1 := mul_le_mul_of_nonneg_left hsq (sq_nonneg (Real.log (x:ℝ)))
    have h2 : (Real.log (x:ℝ))^2 * (149 * (2 + Real.log (x:ℝ)))^2
        ≤ 36000 * ((Real.log (x:ℝ))^4 + 1) := by
      nlinarith [hL8, hL0, sq_nonneg (Real.log (x:ℝ)),
        mul_nonneg hL0.le hL0.le,
        mul_nonneg (mul_nonneg hL0.le hL0.le) hL0.le,
        sq_nonneg (Real.log (x:ℝ) - 8)]
    linarith
  -- denominator dominates
  have hden0 : (0:ℝ) < 2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2) := by
    have : (0:ℝ) ≤ ((halaszM x : ℕ):ℝ) := Nat.cast_nonneg _
    nlinarith [hπ2]
  rw [show (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))
      * ((Real.log (x:ℝ))^2
        * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2)
      = ((Real.log (x:ℝ))^2
        * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2)
        / (2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)) by ring,
    div_le_iff₀ hden0]
  have hfin : 36000 * ((Real.log (x:ℝ))^4 + 1)
      ≤ 2000 * (2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)) := by
    nlinarith [hπ2, hM,
      (show (0:ℝ) ≤ ((halaszM x : ℕ):ℝ) from Nat.cast_nonneg _),
      pow_nonneg hL0.le 4]
  linarith

open Real in
/-- **The balance at the smooth-mass budget** (Track R, M0R-5c): the
N187 envelope with the tail-weight constraint relaxed to
`W·L²·HS² ≤ 2000`, at the price of the same factor on the envelope:

  `… ≤ 2000·(e^π)²·10¹⁵·((SM² + T + 1)·b² + 1)`.

No new balancing: `balance_product_le` is applied at the scaled weight
`W/2000`, and the true product exceeds the scaled one by exactly
`1999·A·m ≤ 1999·(scaled bound)` since the `b²`-part of the second
factor is non-negative.  The constant `2000` covers the smooth mass
(`bandWeight_smooth_mass_le`); nothing else moves. -/
theorem balance_product_le' (L u T b γ S Mp SM HS W : ℝ)
    (hL2 : Real.log 2 ≤ u * L) (hu0 : 0 < u) (hu1 : u ≤ 1) (hL1 : 1 ≤ L)
    (hT5 : 5 ≤ T) (hTL : T ≤ L) (hLT : L ≤ T^2)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hS0 : 0 ≤ S) (hSL : S * L ≤ 1)
    (hMp0 : 0 ≤ Mp) (hMp : Mp ≤ 18)
    (hSM0 : 0 ≤ SM) (hHS0 : 0 ≤ HS)
    (hW0 : 0 ≤ W) (hW : W * (L^2 * HS^2) ≤ 2000)
    (hb0 : 0 ≤ b) :
    (Real.exp π * (12290 * ((1/(u^2*L^2))
          * (4*(Real.exp 1 - 1)*(u*L) + (4*Real.log 2 + 4*Real.log 4))))
        + Real.exp π * (T * (6144 + γ) * (16/L^2 + S))
      + Mp^2 * (1/(2*Real.pi^2*T)))
    * (5 * (2 * (Real.exp π * (12290 * (Real.exp 1 * (u*L) + Real.log 2 + 2)
          + 4*T*(6144 + γ))) + 2*SM^2) * (6*b^2)
      + (Real.exp 1 * (u*L) + 2)^2 * HS^2 * W)
    ≤ 2000 * ((Real.exp π)^2 * 10^15 * ((SM^2 + T + 1) * b^2 + 1)) := by
  have hW0' : (0:ℝ) ≤ W/2000 := by positivity
  have hW' : W/2000 * (L^2 * HS^2) ≤ 1 := by
    have hid : W/2000 * (L^2 * HS^2) = W * (L^2 * HS^2)/2000 := by ring
    rw [hid]
    linarith
  have hbal := balance_product_le L u T b γ S Mp SM HS (W/2000)
    hL2 hu0 hu1 hL1 hT5 hTL hLT hγ0 hγ1 hS0 hSL hMp0 hMp hSM0 hHS0
    hW0' hW' hb0
  -- opaque names for the two factors and the scaled tail term
  obtain ⟨A, hA_def⟩ : ∃ a : ℝ, a = Real.exp π * (12290 * ((1/(u^2*L^2))
        * (4*(Real.exp 1 - 1)*(u*L) + (4*Real.log 2 + 4*Real.log 4))))
      + Real.exp π * (T * (6144 + γ) * (16/L^2 + S))
      + Mp^2 * (1/(2*Real.pi^2*T)) := ⟨_, rfl⟩
  obtain ⟨B, hB_def⟩ : ∃ a : ℝ, a = 5 * (2 * (Real.exp π
        * (12290 * (Real.exp 1 * (u*L) + Real.log 2 + 2)
          + 4*T*(6144 + γ))) + 2*SM^2) * (6*b^2) := ⟨_, rfl⟩
  obtain ⟨m, hm_def⟩ : ∃ a : ℝ,
      a = (Real.exp 1 * (u*L) + 2)^2 * HS^2 * (W/2000) := ⟨_, rfl⟩
  rw [← hA_def, ← hB_def, ← hm_def] at hbal
  rw [← hA_def, ← hB_def,
    show (Real.exp 1 * (u*L) + 2)^2 * HS^2 * W = 2000 * m from by
      rw [hm_def]; ring]
  -- both factors are non-negative
  have he1 : (0:ℝ) ≤ Real.exp 1 - 1 := by
    have := Real.add_one_le_exp (1:ℝ)
    linarith
  have hlog2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hL0 : (0:ℝ) < L := by linarith
  have huL : (0:ℝ) ≤ u * L := by positivity
  have hA : (0:ℝ) ≤ A := by
    rw [hA_def]
    have h1 : (0:ℝ) ≤ 4*(Real.exp 1 - 1)*(u*L)
        + (4*Real.log 2 + 4*Real.log 4) := by
      have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) he1) huL
      linarith
    have h2 : (0:ℝ) ≤ 16/L^2 + S := by positivity
    have h3 : (0:ℝ) ≤ 6144 + γ := by linarith
    have hT0 : (0:ℝ) < T := by linarith
    positivity
  have hB : (0:ℝ) ≤ B := by
    rw [hB_def]
    have h1 : (0:ℝ) ≤ Real.exp 1 * (u*L) + Real.log 2 + 2 := by
      have := mul_nonneg (Real.exp_pos 1).le huL
      linarith
    have h3 : (0:ℝ) ≤ 6144 + γ := by linarith
    have hT0 : (0:ℝ) < T := by linarith
    positivity
  have hAB : (0:ℝ) ≤ A * B := mul_nonneg hA hB
  have hexp1 : A * (B + 2000*m) = A*B + 2000*(A*m) := by ring
  have hexp2 : A * (B + m) = A*B + A*m := by ring
  rw [hexp1]
  rw [hexp2] at hbal
  linarith

end MoltResearch
