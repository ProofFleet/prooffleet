import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5InnerBandScheduleSharpNumerology

/-!
# Track R VI-9g-3': the floored half-dyadic margin

The phase-3 parameter choice starts from the claim that the natural-number
guard `A / 2 <= Delta` implies `1 / 2 <= Delta / A`, and hence

`c3 * eps^2 / 16 <= bandBudget c3 eps (Delta / A)`.

That implication fails when `A` is odd.  At the first positive-slice example,
`A = 3` and `Delta = 1`, the guard reads `1 <= 1`, while `Delta / A = 1 / 3`
and the budget is `c3 * eps^2 / 24`.  The first theorem below records the
counterexample with all constants.  The following two lemmas record the exact
uniform repair: the existing guard gives the weaker denominator `24` for
`A >= 2`, while denominator `16` requires the ceiling-style guard
`A <= 2 * Delta`.

The phase-3 continuation prices both half-budget fits against the valid
denominator `24`.  The final lemmas below also isolate the next asymptotic
check: at moment one, the high-moment count retains its `(T+1)/P` summand.
-/

namespace MoltResearch

namespace Tao2015

/-- The natural half-dyadic guard does not imply the advertised real ratio or
the resulting `bandBudget` lower bound. -/
theorem half_dyadic_bandBudget_margin_counterexample :
    (3 : ℕ) / 2 ≤ 1 ∧
      ¬ ((1 : ℝ) / 2 ≤ ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) ∧
      ¬ ((1 : ℝ) / 16 ≤
        bandBudget 1 1 (((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ))) := by
  norm_num [bandBudget]

/-- Floor division produces a ratio strictly below `1/2` above every natural
threshold, so increasing `A0` cannot recover the advertised implication. -/
theorem exists_half_dyadic_ratio_counterexample_above (A0 : ℕ) :
    ∃ A Delta : ℕ, A0 ≤ A ∧ A / 2 ≤ Delta ∧
      (Delta : ℝ) / (A : ℝ) < (1 : ℝ) / 2 := by
  refine ⟨2 * A0 + 1, A0, by omega, by omega, ?_⟩
  have hden : (0 : ℝ) < ((2 * A0 + 1 : ℕ) : ℝ) := by positivity
  apply (div_lt_iff₀ hden).2
  push_cast
  linarith

/-- With the existing floored guard, `1/3` is the sharp uniform real lower
bound once `A >= 2`. -/
theorem one_third_le_ratio_of_nat_half_le (A Delta : ℕ)
    (hA : 2 ≤ A) (hhalf : A / 2 ≤ Delta) :
    (1 : ℝ) / 3 ≤ (Delta : ℝ) / (A : ℝ) := by
  have hAthree : A ≤ 3 * (A / 2) := by omega
  have hADelta : A ≤ 3 * Delta :=
    hAthree.trans (Nat.mul_le_mul_left 3 hhalf)
  have hADeltaR : (A : ℝ) ≤ 3 * (Delta : ℝ) := by
    exact_mod_cast hADelta
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  apply (le_div_iff₀ hA0).2
  nlinarith

/-- The budget margin actually supplied uniformly by `A / 2 <= Delta` is
`c3 * eps^2 / 24`. -/
theorem bandBudget_one_twenty_four_le_of_nat_half_le
    (c3 eps : ℝ) (hc3 : 0 ≤ c3) (A Delta : ℕ)
    (hA : 2 ≤ A) (hhalf : A / 2 ≤ Delta) :
    c3 * eps ^ 2 / 24 ≤ bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)) := by
  have hratio := one_third_le_ratio_of_nat_half_le A Delta hA hhalf
  have hscale : 0 ≤ c3 * eps ^ 2 / 8 := by positivity
  unfold bandBudget
  calc
    c3 * eps ^ 2 / 24 = (c3 * eps ^ 2 / 8) * ((1 : ℝ) / 3) := by ring
    _ ≤ (c3 * eps ^ 2 / 8) * ((Delta : ℝ) / (A : ℝ)) :=
      mul_le_mul_of_nonneg_left hratio hscale
    _ = c3 * eps ^ 2 * ((Delta : ℝ) / (A : ℝ)) / 8 := by ring

/-- The advertised denominator `16` is valid under the non-floored
ceiling-style guard `A <= 2 * Delta`. -/
theorem bandBudget_one_sixteen_le_of_le_two_mul
    (c3 eps : ℝ) (hc3 : 0 ≤ c3) (A Delta : ℕ)
    (hA : 0 < A) (hhalf : A ≤ 2 * Delta) :
    c3 * eps ^ 2 / 16 ≤ bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)) := by
  have hhalfR : (A : ℝ) ≤ 2 * (Delta : ℝ) := by exact_mod_cast hhalf
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hratio : (1 : ℝ) / 2 ≤ (Delta : ℝ) / (A : ℝ) := by
    apply (le_div_iff₀ hA0).2
    nlinarith
  have hscale : 0 ≤ c3 * eps ^ 2 / 8 := by positivity
  unfold bandBudget
  calc
    c3 * eps ^ 2 / 16 = (c3 * eps ^ 2 / 8) * ((1 : ℝ) / 2) := by ring
    _ ≤ (c3 * eps ^ 2 / 8) * ((Delta : ℝ) / (A : ℝ)) :=
      mul_le_mul_of_nonneg_left hratio hscale
    _ = c3 * eps ^ 2 * ((Delta : ℝ) / (A : ℝ)) / 8 := by ring

/-- The corrected fixed margin converts a numerical cost bound at denominator
`48` into either of the sharp schedule's half-budget hypotheses. -/
theorem half_bandBudget_fit_of_nat_half_le
    (cost c3 eps kappa : ℝ) (hcost : cost ≤ kappa * c3 * eps ^ 2 / 48)
    (hc3 : 0 ≤ c3) (hkappa : 0 ≤ kappa) (A Delta : ℕ)
    (hA : 2 ≤ A) (hhalf : A / 2 ≤ Delta) :
    cost ≤ kappa / 2 * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)) := by
  have hbudget := bandBudget_one_twenty_four_le_of_nat_half_le
    c3 eps hc3 A Delta hA hhalf
  calc
    cost ≤ kappa * c3 * eps ^ 2 / 48 := hcost
    _ = kappa / 2 * (c3 * eps ^ 2 / 24) := by ring
    _ ≤ kappa / 2 * bandBudget c3 eps ((Delta : ℝ) / (A : ℝ)) :=
      mul_le_mul_of_nonneg_left hbudget (by positivity)

/-- A nonempty cell in `(P,2P]` supplies a reciprocal-prime mass of at least
`1/(2P)`.  This is the lower bound that makes the moment-one `T/P` term
visible. -/
theorem one_div_two_mul_le_prime_harmonic_mass
    (P : ℕ) (hP : 0 < P) (Y : Finset ℕ) (p : ℕ)
    (hp0 : 0 < p) (hpY : p ∈ Y) (hpHi : p ≤ 2 * P) :
    (1 : ℝ) / (2 * (P : ℝ)) ≤ ∑ q ∈ Y, (1 : ℝ) / q := by
  have hp0R : (0 : ℝ) < p := by exact_mod_cast hp0
  have h2P0 : (0 : ℝ) < 2 * P := by positivity
  have hpHiR : (p : ℝ) ≤ 2 * P := by exact_mod_cast hpHi
  have hsingle : (1 : ℝ) / (2 * P) ≤ 1 / p :=
    one_div_le_one_div_of_le hp0R hpHiR
  refine hsingle.trans ?_
  exact Finset.single_le_sum
    (f := fun q : ℕ => (1 : ℝ) / q) (fun q _ => by positivity) hpY

/-- At moment `ell = 1`, the proposed high-moment count is bounded below by
the displayed `(T+1)/P` contribution.  No upper-bound simplification may
discard this term. -/
theorem primeHighMomentCountCost_one_lower
    (P : ℕ) (hP : 0 < P) (Y : Finset ℕ) (p : ℕ)
    (hp0 : 0 < p) (hpY : p ∈ Y) (hpHi : p ≤ 2 * P)
    (T V lam : ℝ) (hT : 0 ≤ T) (hV : 0 < V) (hlam : 0 < lam) :
    Real.exp Real.pi * ((T + 1) / (P : ℝ))
          * ((1 : ℝ) / (2 * (P : ℝ))) / V ^ 2
      ≤ primeHighMomentCountCost P 1 Y T V lam := by
  have hmass := one_div_two_mul_le_prime_harmonic_mass P hP Y p hp0 hpY hpHi
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hT1 : 0 ≤ (T + 1) / (P : ℝ) := by positivity
  have hfirst : (T + 1) / (P : ℝ) ≤ (T + 1) / (P : ℝ) + 4 := by
    linarith
  have hlogSq : 0 ≤
      (2 * Real.pi * Real.log (2 * (P : ℝ))) ^ 2 := sq_nonneg _
  have hlast : (1 : ℝ) ≤
      (1 + lam) + (1 / lam)
        * (2 * Real.pi * Real.log (2 * (P : ℝ))) ^ 2 := by
    have hlam0 : 0 ≤ lam := hlam.le
    have hinv0 : 0 ≤ (1 : ℝ) / lam := by positivity
    nlinarith [mul_nonneg hinv0 hlogSq]
  have hexp0 : 0 ≤ Real.exp Real.pi := (Real.exp_pos _).le
  have hmass0 : 0 ≤ ∑ q ∈ Y, (1 : ℝ) / q := by positivity
  have hnum :
    Real.exp Real.pi * ((T + 1) / (P : ℝ)) * (2 * (P : ℝ))⁻¹
      ≤ Real.exp Real.pi * (((T + 1) / (P : ℝ)) + 4)
          * (∑ q ∈ Y, ((q : ℝ))⁻¹)
          * ((1 + lam) + (1 / lam)
            * (2 * Real.pi * Real.log (2 * (P : ℝ))) ^ 2) := by
    calc
    Real.exp Real.pi * ((T + 1) / (P : ℝ)) * (2 * (P : ℝ))⁻¹
        ≤ Real.exp Real.pi * (((T + 1) / (P : ℝ)) + 4)
            * (2 * (P : ℝ))⁻¹ := by
          gcongr
    _ ≤ Real.exp Real.pi * (((T + 1) / (P : ℝ)) + 4)
            * (∑ q ∈ Y, ((q : ℝ))⁻¹) := by
          exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using hmass)
            (by positivity)
    _ ≤ Real.exp Real.pi * (((T + 1) / (P : ℝ)) + 4)
            * (∑ q ∈ Y, ((q : ℝ))⁻¹)
            * ((1 + lam) + (1 / lam)
              * (2 * Real.pi * Real.log (2 * (P : ℝ))) ^ 2) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hlast (by positivity)
  unfold primeHighMomentCountCost
  norm_num only [Nat.cast_one, Nat.pow_one, Nat.factorial_one, one_pow,
    mul_one, Nat.cast_mul, Nat.cast_ofNat]
  apply (div_le_div_iff_of_pos_right (pow_pos hV 2)).2
  simpa using hnum

/-- Consequently, `Gamma ≤ 1` at moment one forces an explicit upper bound
on the time scale.  For the phase-3 choices this reads

`exp(pi) * (T+1) * exp(-log P/log(2T)^(3/4)) * log(2T)^2
  ≤ 2 * P^2 * V^2`.

Thus the factor `(T+1)/P` has not become polylogarithmic: it survives with a
second factor `1/P` coming only from the weakest possible nonempty-cell mass
bound.  At the phase-3 scales `T ≍ A`, `P ≍ exp((log A)^(49/50))`, and
`V = (log A)^(-100)`, the ratio of the two sides has logarithm

`log A - 2*(log A)^(49/50) - (log A)^(23/100) + 202*loglog A + O(1)`,

which tends to infinity.  This is an unbounded-in-`A` failure, rather than a
constant-factor discrepancy. -/
theorem time_scale_bound_of_moment_one_Gamma_le_one
    (P : ℕ) (hP : 0 < P) (Y : Finset ℕ) (p : ℕ)
    (hp0 : 0 < p) (hpY : p ∈ Y) (hpHi : p ≤ 2 * P)
    (T V lam : ℝ) (hT : 0 ≤ T) (hV : 0 < V) (hlam : 0 < lam)
    (hGamma : primeHighMomentCountCost P 1 Y T V lam
          * Real.exp (-(Real.log (P : ℝ) /
            (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
          * (Real.log (2 * T)) ^ 2 ≤ 1) :
    Real.exp Real.pi * (T + 1)
          * Real.exp (-(Real.log (P : ℝ) /
            (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
          * (Real.log (2 * T)) ^ 2
      ≤ 2 * (P : ℝ) ^ 2 * V ^ 2 := by
  have hcost := primeHighMomentCountCost_one_lower
    P hP Y p hp0 hpY hpHi T V lam hT hV hlam
  have hsave0 : 0 ≤ Real.exp (-(Real.log (P : ℝ) /
      (Real.log (2 * T)) ^ (3 / 4 : ℝ))) := (Real.exp_pos _).le
  have hlog0 : 0 ≤ (Real.log (2 * T)) ^ 2 := sq_nonneg _
  have hlower :
      (Real.exp Real.pi * ((T + 1) / (P : ℝ))
            * ((1 : ℝ) / (2 * (P : ℝ))) / V ^ 2)
          * Real.exp (-(Real.log (P : ℝ) /
            (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
          * (Real.log (2 * T)) ^ 2 ≤ 1 := by
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcost hsave0) hlog0).trans hGamma
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hden : 0 < 2 * (P : ℝ) ^ 2 * V ^ 2 := by positivity
  have heq :
      (Real.exp Real.pi * ((T + 1) / (P : ℝ))
            * ((1 : ℝ) / (2 * (P : ℝ))) / V ^ 2)
          * Real.exp (-(Real.log (P : ℝ) /
            (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
          * (Real.log (2 * T)) ^ 2 =
        (Real.exp Real.pi * (T + 1)
            * Real.exp (-(Real.log (P : ℝ) /
              (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
            * (Real.log (2 * T)) ^ 2) / (2 * (P : ℝ) ^ 2 * V ^ 2) := by
    field_simp
  rw [heq] at hlower
  have hcross := (div_le_iff₀ hden).mp hlower
  simpa using hcross

/-- The preceding necessary condition at the fixed split threshold used by
the sharp schedule.  Its right-hand side is exactly `2P²/(log A)^200`; the
moment-one count therefore leaves the ambient time scale on the left. -/
theorem time_scale_bound_of_fixed_split_moment_one_Gamma_le_one
    (A P : ℕ) (hA : 1 < A) (hP : 0 < P) (Y : Finset ℕ) (p : ℕ)
    (hp0 : 0 < p) (hpY : p ∈ Y) (hpHi : p ≤ 2 * P)
    (T lam : ℝ) (hT : 0 ≤ T) (hlam : 0 < lam)
    (hGamma : primeHighMomentCountCost P 1 Y T (exceptionalSplitThreshold A) lam
          * Real.exp (-(Real.log (P : ℝ) /
            (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
          * (Real.log (2 * T)) ^ 2 ≤ 1) :
    Real.exp Real.pi * (T + 1)
          * Real.exp (-(Real.log (P : ℝ) /
            (Real.log (2 * T)) ^ (3 / 4 : ℝ)))
          * (Real.log (2 * T)) ^ 2
      ≤ 2 * (P : ℝ) ^ 2 / Real.log (A : ℝ) ^ 200 := by
  have hV := exceptionalSplitThreshold_pos A hA
  have hmain := time_scale_bound_of_moment_one_Gamma_le_one
    P hP Y p hp0 hpY hpHi T (exceptionalSplitThreshold A) lam hT hV hlam hGamma
  calc
    _ ≤ 2 * (P : ℝ) ^ 2 * exceptionalSplitThreshold A ^ 2 := hmain
    _ = 2 * (P : ℝ) ^ 2 / Real.log (A : ℝ) ^ 200 := by
      unfold exceptionalSplitThreshold
      ring

end Tao2015

end MoltResearch
