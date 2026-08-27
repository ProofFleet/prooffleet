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


open Real in
/-- `e^{2k}/L² = 1/((e^{−k})²·L²)` — N188's bridge, the block index as
`u = e^{−k}` (restated: the capstone's copy is private). -/
private lemma exp_two_k_div_sq (k : ℕ) (L : ℝ) :
    Real.exp (2*(k:ℝ)) / L^2 = 1/((Real.exp (-(k:ℝ)))^2 * L^2) := by
  have h : (Real.exp (-(k:ℝ)))^2 = Real.exp (-(2*(k:ℝ))) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [h, Real.exp_neg]
  field_simp

open Real in
/-- `e^{1−k}·L = e·(e^{−k}·L)` — N185's decay in the balance's `e·P`
shape (restated: the capstone's copy is private). -/
private lemma exp_one_sub_k_mul (k : ℕ) (L : ℝ) :
    Real.exp (1 - (k:ℝ)) * L = Real.exp 1 * (Real.exp (-(k:ℝ)) * L) := by
  rw [show (1 - (k:ℝ)) = 1 + (-(k:ℝ)) by ring, Real.exp_add]
  ring

open Real in
/-- `1 ≤ log x` for `x ≥ 3` — the balance's `hL1` (restated: the
capstone's copy is private). -/
private lemma one_le_log_of_three_le (x : ℕ) (hx : 3 ≤ x) :
    (1:ℝ) ≤ Real.log (x:ℝ) := by
  have he : Real.exp 1 ≤ (x:ℝ) := by
    have h3 : (3:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
    have := Real.exp_one_lt_d9
    linarith
  calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (x:ℝ) := Real.log_le_log (Real.exp_pos 1) he

set_option maxHeartbeats 3200000 in
open MeasureTheory Real Complex Finset in
/-- **§3's per-block estimate, balanced, through the smooth tsum**
(Track R, M0R-5): N189 with the band sup demanded of the smooth phase
sum and the tail weight at the smooth-mass budget:

  `|tripleConvR f x P| ≤ x·√(2000·(e^π)²·10¹⁵·((SM² + T + 1)·b² + 1)) + 2x·log 4`.

The chain is verbatim N189 with `tripleConvR_block_sharp_le'` at the
bottom and `balance_product_le'` at the top: the energy side is
ring-equal to the `u`-form, the `V`-side and tail lose exactly the
N185/N186 monotonicities, and `hW` is now the smooth-mass budget
`≤ 2000` (discharged later by `bandWeight_smooth_mass_le`).  Complete
multiplicativity is the one new hypothesis — the Euler product behind
the band sup needs it. -/
theorem tripleConvR_block_balanced_le' (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (hmul : ∀ a b, f (a*b) = f a * f b) (h1 : f 1 = 1)
    (x k : ℕ) (hx3 : 3 ≤ x) (hk : 1 ≤ k) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k)
    (hfit : 2 * blockHi x k ≤ x)
    (hX3 : 3 ≤ x / blockLo x k)
    (T : ℝ) (hT : 5 ≤ T) (hPT : ∀ p ∈ P, T^2 ≤ (p:ℝ))
    (b : ℝ) (hb0 : 0 ≤ b)
    (hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖ExpSums.smoothPhaseSum (fun n => ((f n : ℝ) : ℂ)) x t‖ ≤ b)
    (hTL : T ≤ Real.log (x:ℝ)) (hLT : Real.log (x:ℝ) ≤ T^2)
    (hγ1 : Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4) ≤ 1)
    (hSL : 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)
      * Real.log (x:ℝ) ≤ 1)
    (hMp : ∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|)
      ≤ 18)
    (hW : (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))
      * ((Real.log (x:ℝ))^2
        * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2) ≤ 2000) :
    |tripleConvR f x P|
      ≤ (x:ℝ) * Real.sqrt (2000 * ((Real.exp π)^2 * 10^15
          * (((∑ q ∈ (x / blockLo x k).primesBelow.filter
                (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
              Real.log (q:ℝ)/(q:ℝ))^2 + T + 1) * b^2 + 1)))
        + 2*(x:ℝ)*Real.log 4 := by
  classical
  have hx : 2 ≤ x := by omega
  have hxR0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
  have hL0 : (0:ℝ) < Real.log (x:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 2 ≤ x))
  have hu0 : (0:ℝ) < Real.exp (-(k:ℝ)) := Real.exp_pos _
  have hu1 : Real.exp (-(k:ℝ)) ≤ 1 := by
    rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (Nat.cast_nonneg k))
  refine le_trans (tripleConvR_block_sharp_le' f hf hmul h1 x k hx hk P hP
    hfit hX3 T hT hPT b hb0 hBu) ?_
  -- the √-argument chain
  have hX1 : 1 ≤ x / blockLo x k := by omega
  have hXx : x / blockLo x k ≤ x := Nat.div_le_self x _
  -- (i) the enlarged-range γ is dominated by the global one
  have hγmono : Real.exp (-(π*T^2/64)) * (((x / blockLo x k : ℕ):ℝ) * Real.log 4)
      ≤ Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4) := by
    have hc : ((x / blockLo x k : ℕ):ℝ) ≤ (x:ℝ) := by exact_mod_cast hXx
    have h4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hc h4) (Real.exp_pos _).le
  -- (ii) `log(X+1) + 2 ≤ e·(u·L) + log 2 + 2`
  have hlogX1 : Real.log ((x / blockLo x k + 1 : ℕ):ℝ)
      ≤ Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + Real.log 2 := by
    have hle2X : ((x / blockLo x k + 1 : ℕ):ℝ)
        ≤ 2 * ((x / blockLo x k : ℕ):ℝ) := by
      have : x / blockLo x k + 1 ≤ 2 * (x / blockLo x k) := by omega
      exact_mod_cast this
    have hX0 : (0:ℝ) < ((x / blockLo x k : ℕ):ℝ) := by
      exact_mod_cast (by omega : 0 < x / blockLo x k)
    calc Real.log ((x / blockLo x k + 1 : ℕ):ℝ)
        ≤ Real.log (2 * ((x / blockLo x k : ℕ):ℝ)) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < x / blockLo x k + 1))
            hle2X
      _ = Real.log 2 + Real.log ((x / blockLo x k : ℕ):ℝ) :=
          Real.log_mul (by norm_num) (ne_of_gt hX0)
      _ ≤ Real.log 2 + Real.exp (1 - (k:ℝ)) * Real.log (x:ℝ) := by
          linarith [log_div_blockLo_le x k hx]
      _ = Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + Real.log 2 := by
          rw [exp_one_sub_k_mul]
          ring
  -- (iii) the tail mass in the `e·P + 2` shape
  have hqm : ∑ q ∈ (x / blockLo x k).primesBelow, Real.log (q:ℝ)/(q:ℝ)
      ≤ Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + 2 := by
    have h := qMass_le x k hx (by omega)
    rw [exp_one_sub_k_mul] at h
    linarith
  have hqm0 : (0:ℝ) ≤ ∑ q ∈ (x / blockLo x k).primesBelow,
      Real.log (q:ℝ)/(q:ℝ) :=
    Finset.sum_nonneg fun q _ => div_nonneg (Real.log_natCast_nonneg q)
      (Nat.cast_nonneg q)
  have hqm_sq : (∑ q ∈ (x / blockLo x k).primesBelow,
        Real.log (q:ℝ)/(q:ℝ))^2
      ≤ (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + 2)^2 := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self hqm0 hqm
  -- non-negativity of the energy factor
  have he1nn : (0:ℝ) ≤ Real.exp 1 - 1 := by linarith [Real.exp_one_gt_d9.le]
  have hA1nn : (0:ℝ) ≤ 4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ))
      * Real.log (x:ℝ) + Real.log 2) + 4 * Real.log 4 := by
    have hp1 : (0:ℝ) ≤ (Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ) :=
      mul_nonneg (mul_nonneg he1nn hu0.le) hL0.le
    have hp2 := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)
    have hp4 := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)
    linarith
  have hE0 : (0:ℝ) ≤ Real.exp π *
      (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
          * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
              + Real.log 2) + 4 * Real.log 4))
        + T * (6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
            * (16/(Real.log (x:ℝ))^2
                + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
      + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
          * (1/(2*Real.pi^2*T)) := by
    have hT0 : (0:ℝ) < T := by linarith
    have hb1 : (0:ℝ) ≤ Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2 := by positivity
    have hb2 : (0:ℝ) ≤ T * (6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
        * (16/(Real.log (x:ℝ))^2
            + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)) := by
      positivity
    have hb3 : (0:ℝ) ≤ (∑ p ∈ P, Real.log (p:ℝ)
        /((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2 * (1/(2*Real.pi^2*T)) := by
      positivity
    have hb4 : (0:ℝ) ≤ 12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
        * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
            + Real.log 2) + 4 * Real.log 4)) := by
      have := mul_nonneg hb1 hA1nn
      nlinarith [this]
    have := mul_nonneg (Real.exp_pos π).le (add_nonneg hb4 hb2)
    linarith
  -- the V-side monotonicity
  have hT0' : (0:ℝ) ≤ T := by linarith
  have hVinner : 12290 * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
        + 4*T*(6144 + Real.exp (-(π*T^2/64))
            * (((x / blockLo x k : ℕ):ℝ) * Real.log 4))
      ≤ 12290 * (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
            + Real.log 2 + 2)
        + 4*T*(6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4)) := by
    have hm1 : Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2
        ≤ Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
          + Real.log 2 + 2 := by linarith [hlogX1]
    have hm2 : (6144:ℝ) + Real.exp (-(π*T^2/64))
        * (((x / blockLo x k : ℕ):ℝ) * Real.log 4)
        ≤ 6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4) := by
      linarith [hγmono]
    have hm3 := mul_le_mul_of_nonneg_left hm1 (by norm_num : (0:ℝ) ≤ 12290)
    have hm4 := mul_le_mul_of_nonneg_left hm2
      (by positivity : (0:ℝ) ≤ 4*T)
    linarith
  have hVle : 2 * (Real.exp π * (12290
        * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
        + 4*T*(6144 + Real.exp (-(π*T^2/64))
            * (((x / blockLo x k : ℕ):ℝ) * Real.log 4))))
      + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
            (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
          Real.log (q:ℝ)/(q:ℝ))^2
      ≤ 2 * (Real.exp π * (12290
            * (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
              + Real.log 2 + 2)
            + 4*T*(6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))))
        + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
              (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
            Real.log (q:ℝ)/(q:ℝ))^2 := by
    have := mul_le_mul_of_nonneg_left hVinner (Real.exp_pos π).le
    linarith
  -- the tail-mass monotonicity, at the smooth mass
  have hMtle : (∑ q ∈ (x / blockLo x k).primesBelow,
        Real.log (q:ℝ)/(q:ℝ))^2
      * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2
      * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))
      ≤ (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + 2)^2
        * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2
        * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2))) := by
    have hm1 := mul_le_mul_of_nonneg_right hqm_sq
      (sq_nonneg (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹))
    exact mul_le_mul_of_nonneg_right hm1 (by positivity)
  -- the bracket
  have hbrk : 5 * (2 * (Real.exp π * (12290
        * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
        + 4*T*(6144 + Real.exp (-(π*T^2/64))
            * (((x / blockLo x k : ℕ):ℝ) * Real.log 4))))
      + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
            (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
          Real.log (q:ℝ)/(q:ℝ))^2) * (6*b^2)
      + (∑ q ∈ (x / blockLo x k).primesBelow,
            Real.log (q:ℝ)/(q:ℝ))^2
          * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2
          * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))
      ≤ 5 * (2 * (Real.exp π * (12290
            * (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
              + Real.log 2 + 2)
            + 4*T*(6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))))
          + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
                (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
              Real.log (q:ℝ)/(q:ℝ))^2) * (6*b^2)
        + (Real.exp 1 * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ)) + 2)^2
          * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2
          * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2))) := by
    have hm5 := mul_le_mul_of_nonneg_left hVle (by norm_num : (0:ℝ) ≤ 5)
    have hm56 := mul_le_mul_of_nonneg_right hm5
      (by positivity : (0:ℝ) ≤ 6*b^2)
    linarith [hMtle]
  -- E-rewrite into the u-form
  have hEeq : Real.exp π *
      (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
          * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
              + Real.log 2) + 4 * Real.log 4))
        + T * (6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
            * (16/(Real.log (x:ℝ))^2
                + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
      + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
          * (1/(2*Real.pi^2*T))
      = Real.exp π * (12290 * (1/((Real.exp (-(k:ℝ)))^2*(Real.log (x:ℝ))^2)
          * (4*(Real.exp 1 - 1)*(Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
            + (4*Real.log 2 + 4*Real.log 4))))
        + Real.exp π * (T * (6144 + Real.exp (-(π*T^2/64))
            * ((x:ℝ) * Real.log 4))
          * (16/(Real.log (x:ℝ))^2
              + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
        + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
            * (1/(2*Real.pi^2*T)) := by
    rw [exp_two_k_div_sq]
    ring
  -- the full argument bound
  have harg : (Real.exp π *
      (12290 * ((Real.exp (2*(k:ℝ))/(Real.log (x:ℝ))^2)
          * (4 * ((Real.exp 1 - 1) * Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
              + Real.log 2) + 4 * Real.log 4))
        + T * (6144 + Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
            * (16/(Real.log (x:ℝ))^2
                + 4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2)))
      + (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))^2
          * (1/(2*Real.pi^2*T)))
      * (5 * (2 * (Real.exp π * (12290
            * (Real.log ((x / blockLo x k + 1 : ℕ):ℝ) + 2)
            + 4*T*(6144 + Real.exp (-(π*T^2/64))
                * (((x / blockLo x k : ℕ):ℝ) * Real.log 4))))
          + 2 * (∑ q ∈ (x / blockLo x k).primesBelow.filter
                (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
              Real.log (q:ℝ)/(q:ℝ))^2) * (6*b^2)
        + (∑ q ∈ (x / blockLo x k).primesBelow,
              Real.log (q:ℝ)/(q:ℝ))^2
            * (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)^2
            * (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2))))
      ≤ 2000 * ((Real.exp π)^2 * 10^15
          * (((∑ q ∈ (x / blockLo x k).primesBelow.filter
                (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
              Real.log (q:ℝ)/(q:ℝ))^2 + T + 1) * b^2 + 1)) := by
    refine le_trans (mul_le_mul_of_nonneg_left hbrk hE0) ?_
    rw [hEeq]
    exact balance_product_le' (Real.log (x:ℝ)) (Real.exp (-(k:ℝ))) T b
      (Real.exp (-(π*T^2/64)) * ((x:ℝ) * Real.log 4))
      (4/(Real.sqrt ((Nat.sqrt x : ℕ):ℝ) * (Real.log 2)^2))
      (∑ p ∈ P, Real.log (p:ℝ)/((p:ℝ) * |Real.log ((x:ℝ)/(p:ℝ))|))
      (∑ q ∈ (x / blockLo x k).primesBelow.filter
          (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)), Real.log (q:ℝ)/(q:ℝ))
      (∑' m : (Nat.smoothNumbers x), (((m : ℕ) : ℝ))⁻¹)
      (1/(2*Real.pi^2*(((halaszM x : ℕ):ℝ) + 1/2)))
      (block_index_le_of_fit x k hx hfit) hu0 hu1
      (one_le_log_of_three_le x hx3) hT hTL hLT
      (by positivity) hγ1 (by positivity) hSL
      (Finset.sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p)
        (by positivity)) hMp
      (Finset.sum_nonneg fun q _ => div_nonneg (Real.log_natCast_nonneg q)
        (Nat.cast_nonneg q))
      (tsum_nonneg fun m => by positivity)
      (by positivity) hW hb0
  have hs := Real.sqrt_le_sqrt harg
  have hxs := mul_le_mul_of_nonneg_left hs hxR0
  linarith


set_option maxHeartbeats 3200000 in
open Real Finset in
/-- **§3's head, closed, through the smooth tsum** (Track R, M0R-5):
N196 with the band sup demanded of the smooth phase sum and every
rider discharged at the smooth-mass budget — the per-block input is
`tripleConvR_block_balanced_le'`, its `hW` is
`bandWeight_smooth_mass_le`, and the envelope carries the constant
`2000`:

  `|tripleConvR f x (survivors)| ≤ K₀·(x·√(2000·(e^π)²·10¹⁵·(((log⌈T²⌉+2)² + T + 1)·b² + 1)) + 2x·log 4) + 2·x·(16((e−1)·e·log 2 + log 2) + 16·log 4)`.

The boundary blocks are priced fit-free exactly as in N196 — the tail
branch never sees the band sup. -/
theorem tripleConvR_survivors_balanced_le' (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (hmul : ∀ a b, f (a*b) = f a * f b) (h1 : f 1 = 1)
    (x y K₀ : ℕ) (hx : 10^16 ≤ x) (hy2 : 2 ≤ y)
    (T : ℝ) (hT1 : Real.sqrt (21 * Real.log (x:ℝ)) ≤ T)
    (hT2 : T ≤ Real.log (x:ℝ)) (hTy : T^2 ≤ (y:ℝ))
    (hK₀1 : 1 ≤ K₀)
    (hK₀low : Real.exp 1 * Real.log 2
      ≤ Real.exp (-(K₀:ℝ)) * Real.log (x:ℝ))
    (hK₀max : Real.exp (-((K₀:ℝ)+1)) * Real.log (x:ℝ)
      < Real.exp 1 * Real.log 2)
    (hX3 : ∀ k ∈ Finset.Icc 1 K₀, 3 ≤ x / blockLo x k)
    (b : ℝ) (hb0 : 0 ≤ b)
    (hBu : ∀ t : ℝ, |t| ≤ ((halaszM x : ℕ):ℝ) + 1 →
      ‖ExpSums.smoothPhaseSum (fun n => ((f n : ℝ) : ℂ)) x t‖ ≤ b) :
    |tripleConvR f x ((((Finset.Icc 1 x).filter Nat.Prime).filter
        (fun p => ¬ p < y)).filter (fun p => ¬ x < 2*p))|
      ≤ (K₀:ℝ) * ((x:ℝ) * Real.sqrt (2000 * ((Real.exp π)^2 * 10^15
            * (((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1) * b^2 + 1)))
          + 2*(x:ℝ)*Real.log 4)
        + 2 * ((x:ℝ) * (16 * ((Real.exp 1 - 1) * (Real.exp 1 * Real.log 2)
            + Real.log 2) + 16 * Real.log 4)) := by
  classical
  have hx2 : (2:ℕ) ≤ x := le_trans (by norm_num) hx
  have hx3' : (3:ℕ) ≤ x := le_trans (by norm_num) hx
  have hx3000 : (3000:ℕ) ≤ x := le_trans (by norm_num) hx
  have hx1 : (1:ℕ) ≤ x := by omega
  have hL0 : (0:ℝ) < Real.log (x:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 2 ≤ x))
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨h5T, hLT2, hγT⟩ := T_window_conditions x T hx hT1 hT2
  -- split validity at `K₀+2`
  have hK : Real.exp (-((K₀+2:ℕ):ℝ)) * Real.log (x:ℝ) < Real.log 2 := by
    have hs1 : Real.exp (-((K₀+2:ℕ):ℝ))
        = Real.exp (-1) * Real.exp (-((K₀:ℝ)+1)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    have hs2 : Real.exp (-1) * (Real.exp 1 * Real.log 2) = Real.log 2 := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    calc Real.exp (-((K₀+2:ℕ):ℝ)) * Real.log (x:ℝ)
        = Real.exp (-1) * (Real.exp (-((K₀:ℝ)+1)) * Real.log (x:ℝ)) := by
          rw [hs1]; ring
      _ < Real.exp (-1) * (Real.exp 1 * Real.log 2) := by
          exact mul_lt_mul_of_pos_left hK₀max (Real.exp_pos _)
      _ = Real.log 2 := hs2
  -- split, triangle, k-split
  rw [tripleConvR_survivor_split f x y (K₀+2) hx1 hK]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine tripleConvR_ksplit_le f x K₀ (K₀+2) (by omega)
    (fun k => (((Finset.Ico (blockLo x k) (blockHi x k)).filter
      Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p))) _ _ ?_ ?_
  · -- the head: the primed N189 per block, then the SM-monotone step
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk1 : 1 ≤ k := hk.1
    have hkK : k ≤ K₀ := hk.2
    -- the block-membership facts
    have hP : ∀ p ∈ (((Finset.Ico (blockLo x k) (blockHi x k)).filter
        Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p)),
        p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Ico] at hp
      exact ⟨hp.1.2, hp.1.1.1, hp.1.1.2⟩
    have hPT : ∀ p ∈ (((Finset.Ico (blockLo x k) (blockHi x k)).filter
        Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p)),
        T^2 ≤ (p:ℝ) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Ico] at hp
      have hyp : y ≤ p := Nat.le_of_not_lt hp.2.1
      have : (y:ℝ) ≤ (p:ℝ) := by exact_mod_cast hyp
      linarith [hTy]
    -- the per-block mass floor
    have huL : Real.exp 1 * Real.log 2
        ≤ Real.exp (-(k:ℝ)) * Real.log (x:ℝ) := by
      have hmono : Real.exp (-(K₀:ℝ)) ≤ Real.exp (-(k:ℝ)) := by
        refine Real.exp_le_exp.mpr ?_
        have : (k:ℝ) ≤ (K₀:ℝ) := by exact_mod_cast hkK
        linarith
      have := mul_le_mul_of_nonneg_right hmono hL0.le
      linarith [hK₀low]
    have hMp := blockMass_le_const x k hx2 hk1 _ hP huL
    have hγ1 := gamma_le_one_of x T hx2 hγT
    have hSL := tailS_mul_log_le_one x hx
    have hW := bandWeight_smooth_mass_le x hx3000
    have hbal := tripleConvR_block_balanced_le' f hf hmul h1 x k hx3' hk1 _ hP
      (fit_of_mass_floor x k (by omega) huL)
      (hX3 k (by rw [Finset.mem_Icc]; omega)) T h5T hPT
      b hb0 hBu hT2 hLT2 hγ1 hSL hMp hW
    refine le_trans hbal ?_
    -- the SM-monotone step: `SM(k) ≤ log⌈T²⌉ + 2`, under the `2000`
    have hSM := smallMass_le (x / blockLo x k) T h5T
    have hSM0 : (0:ℝ) ≤ ∑ q ∈ (x / blockLo x k).primesBelow.filter
        (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)), Real.log (q:ℝ)/(q:ℝ) :=
      Finset.sum_nonneg fun q _ => div_nonneg (Real.log_natCast_nonneg q)
        (Nat.cast_nonneg q)
    have hSMsq : (∑ q ∈ (x / blockLo x k).primesBelow.filter
          (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)), Real.log (q:ℝ)/(q:ℝ))^2
        ≤ (Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 := by
      nlinarith [hSM, hSM0]
    have hargmono : 2000 * ((Real.exp π)^2 * 10^15
        * (((∑ q ∈ (x / blockLo x k).primesBelow.filter
            (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
          Real.log (q:ℝ)/(q:ℝ))^2 + T + 1) * b^2 + 1))
        ≤ 2000 * ((Real.exp π)^2 * 10^15
          * (((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1) * b^2 + 1)) := by
      have hq1 : ((∑ q ∈ (x / blockLo x k).primesBelow.filter
            (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
          Real.log (q:ℝ)/(q:ℝ))^2 + T + 1) * b^2
          ≤ ((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1) * b^2 :=
        mul_le_mul_of_nonneg_right (by linarith [hSMsq]) (sq_nonneg b)
      have hq2 : (0:ℝ) ≤ (Real.exp π)^2 * 10^15 := by positivity
      have hq3 := mul_le_mul_of_nonneg_left
        (by linarith [hq1] :
          ((∑ q ∈ (x / blockLo x k).primesBelow.filter
              (fun q : ℕ => ¬ T^2 ≤ (q:ℝ)),
            Real.log (q:ℝ)/(q:ℝ))^2 + T + 1) * b^2 + 1
          ≤ ((Real.log ((⌈T^2⌉₊ : ℕ):ℝ) + 2)^2 + T + 1) * b^2 + 1) hq2
      exact mul_le_mul_of_nonneg_left hq3 (by norm_num : (0:ℝ) ≤ 2000)
    have hxR0 : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
    have hs := Real.sqrt_le_sqrt hargmono
    have := mul_le_mul_of_nonneg_left hs hxR0
    linarith
  · -- the tail: two boundary blocks, fit-free
    have htb : ∀ k ∈ Finset.Icc (K₀+1) (K₀+2),
        |tripleConvR f x (((Finset.Ico (blockLo x k) (blockHi x k)).filter
          Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p))|
        ≤ (x:ℝ) * (16 * ((Real.exp 1 - 1) * (Real.exp 1 * Real.log 2)
            + Real.log 2) + 16 * Real.log 4) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hk1 : 1 ≤ k := by omega
      obtain ⟨hlo1, hlohi⟩ := blockLo_le_blockHi x k hx1
      have hP' : ∀ p ∈ (((Finset.Ico (blockLo x k) (blockHi x k)).filter
          Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p)),
          p.Prime ∧ blockLo x k ≤ p ∧ p < blockHi x k := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ico] at hp
        exact ⟨hp.1.2, hp.1.1.1, hp.1.1.2⟩
      have h2P : ∀ p ∈ (((Finset.Ico (blockLo x k) (blockHi x k)).filter
          Nat.Prime).filter (fun p => ¬ p < y ∧ ¬ x < 2*p)), 2*p ≤ x := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ico] at hp
        omega
      refine le_trans (norm_tripleConvR_le'' f hf x (blockLo x k)
        (blockHi x k) hlo1 hlohi _ hP' h2P) ?_
      have hw := log_blockHi_sub_log_blockLo_le x k hx2 hk1
      have hmono : Real.exp (-(k:ℝ)) ≤ Real.exp (-((K₀:ℝ)+1)) := by
        refine Real.exp_le_exp.mpr ?_
        have hc1 : ((K₀+1:ℕ):ℝ) ≤ (k:ℝ) := by exact_mod_cast hk.1
        push_cast at hc1
        linarith
      have huk : Real.exp (-(k:ℝ)) * Real.log (x:ℝ)
          ≤ Real.exp 1 * Real.log 2 := by
        have hc2 := mul_le_mul_of_nonneg_right hmono hL0.le
        linarith [hK₀max]
      have he1nn : (0:ℝ) ≤ Real.exp 1 - 1 := by
        linarith [Real.exp_one_gt_d9.le]
      have hwidth2 : Real.log ((blockHi x k : ℕ):ℝ)
          - Real.log ((blockLo x k : ℕ):ℝ)
          ≤ (Real.exp 1 - 1) * (Real.exp 1 * Real.log 2) + Real.log 2 := by
        have hc3 : (Real.exp 1 - 1) * (Real.exp (-(k:ℝ)) * Real.log (x:ℝ))
            ≤ (Real.exp 1 - 1) * (Real.exp 1 * Real.log 2) :=
          mul_le_mul_of_nonneg_left huk he1nn
        nlinarith [hw, hc3]
      have hx0' : (0:ℝ) ≤ (x:ℝ) := Nat.cast_nonneg _
      refine mul_le_mul_of_nonneg_left ?_ hx0'
      linarith [hwidth2]
    refine le_trans (Finset.sum_le_sum htb) ?_
    rw [Finset.sum_const, Nat.card_Icc]
    have h2c : K₀+2+1 - (K₀+1) = 2 := by omega
    rw [h2c]
    simp [nsmul_eq_mul]

end MoltResearch
