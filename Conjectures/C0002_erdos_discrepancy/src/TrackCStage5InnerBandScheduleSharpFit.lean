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
denominator `24`.  The next lemmas isolate the moment-one obstruction from
run 9b and verify the adaptive choice requested in run 9d:

`adaptivePrimeMoment P T = ceil(log(2T)/log P) + 1`

makes `P^ell >= 2T`, so it removes the old `(T+1)/P^ell` growth when the
prime scale itself grows with the ambient scale.

The last lemmas record a further obstruction in the run-9d prescription.
The exceptional cover is anchored in the last *ordinary* level, whose prime
scale is fixed before the universal ambient scale.  If that fixed cell
contains `p <= 2P`, then for every moment order

`primeHighMomentCountCost P ell cell T V lambda
  >= exp(pi) * (T+1) / (2P)^(4P)`

whenever `0 < V <= 1`.  In particular, adaptively increasing `ell` cannot
make `sharpExceptionalCoverBound` polylogarithmic: such an upper bound would
force `T+1 <= (2P)^(4P)(log A)^k/(2 exp(pi))`.  In the A.2 assembly the outer
cutoff has `T` proportional to `A/h`, with `h` and `P` already fixed.  The
integer half-fit therefore retains the exact necessary lower bound displayed
by `fixed_anchor_hfitInt_forces_linear_time`; after
`V = (log A)^(-100)` it grows like `sqrt A/(log A)^200`.  This is unbounded
in `A`, independently of the choice of moment.
-/

namespace MoltResearch

namespace Tao2015

/-- The adaptive moment from `[MR]`'s large-value calibration. -/
noncomputable def adaptivePrimeMoment (P : ℕ) (T : ℝ) : ℕ :=
  ⌈Real.log (2 * T) / Real.log P⌉₊ + 1

/-- The adaptive moment is always admissible for the high-moment count. -/
theorem adaptivePrimeMoment_one_le (P : ℕ) (T : ℝ) :
    1 ≤ adaptivePrimeMoment P T := by
  unfold adaptivePrimeMoment
  omega

/-- At the adaptive moment the prime power reaches the full time scale. -/
theorem two_mul_time_le_pow_adaptivePrimeMoment
    (P : ℕ) (T : ℝ) (hP : 2 ≤ P) (hT : 0 < T) :
    2 * T ≤ ((P ^ adaptivePrimeMoment P T : ℕ) : ℝ) := by
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < P))
  have hratio : Real.log (2 * T) / Real.log P ≤
      (adaptivePrimeMoment P T : ℝ) := by
    calc
      Real.log (2 * T) / Real.log P ≤
          (⌈Real.log (2 * T) / Real.log P⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (adaptivePrimeMoment P T : ℝ) := by
        exact_mod_cast (by unfold adaptivePrimeMoment; omega :
          ⌈Real.log (2 * T) / Real.log P⌉₊ ≤ adaptivePrimeMoment P T)
  have hlog : Real.log (2 * T) ≤
      (adaptivePrimeMoment P T : ℝ) * Real.log P := by
    exact (div_le_iff₀ hlogP).mp hratio
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (by positivity : (0 : ℝ) < 2 * T)] at hexp
  rw [show (adaptivePrimeMoment P T : ℝ) * Real.log P =
      (adaptivePrimeMoment P T : ℕ) * Real.log P by norm_cast,
    Real.exp_nat_mul, Real.exp_log (by exact_mod_cast (by omega : 0 < P))] at hexp
  norm_cast at hexp ⊢

/-- Consequently the adaptive moment removes the explicit time quotient in
the exceptional cell's high-moment count. -/
theorem adaptivePrimeMoment_time_term_le_one
    (P : ℕ) (T : ℝ) (hP : 2 ≤ P) (hT : 1 ≤ T) :
    (T + 1) / ((P ^ adaptivePrimeMoment P T : ℕ) : ℝ) ≤ 1 := by
  have hpow := two_mul_time_le_pow_adaptivePrimeMoment P T hP (by linarith)
  have hden : (0 : ℝ) < ((P ^ adaptivePrimeMoment P T : ℕ) : ℝ) := by positivity
  apply (div_le_iff₀ hden).2
  linarith

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

/-- For a fixed anchor `P` and a cell prime `p <= 2P`, the factorial in every
moment is large enough to offset both prime-power denominators up to the fixed
factor `(2P)^(4P)`. -/
theorem fixed_anchor_denominator_le (P ell p : ℕ) (hP : 1 ≤ P)
    (hpHi : p ≤ 2 * P) :
    P ^ ell * p ^ ell ≤ (Nat.factorial ell) ^ 2 * (2 * P) ^ (4 * P) := by
  by_cases hell : ell < 2 * P
  · have hPtwo : P ≤ 2 * P := by omega
    have hpowP : P ^ ell ≤ (2 * P) ^ ell := Nat.pow_le_pow_left hPtwo ell
    have hpowp : p ^ ell ≤ (2 * P) ^ ell := Nat.pow_le_pow_left hpHi ell
    have hpowexp : (2 * P) ^ (2 * ell) ≤ (2 * P) ^ (4 * P) := by
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hfac : 1 ≤ (Nat.factorial ell) ^ 2 := by
      have := Nat.factorial_pos ell
      nlinarith
    calc
      P ^ ell * p ^ ell ≤ (2 * P) ^ ell * (2 * P) ^ ell :=
        Nat.mul_le_mul hpowP hpowp
      _ = (2 * P) ^ (2 * ell) := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ (2 * P) ^ (4 * P) := hpowexp
      _ = 1 * (2 * P) ^ (4 * P) := by simp
      _ ≤ (Nat.factorial ell) ^ 2 * (2 * P) ^ (4 * P) := by gcongr
  · have h2Pell : 2 * P ≤ ell := by omega
    have hfacRaw := Nat.factorial_mul_pow_sub_le_factorial h2Pell
    have hfac : (2 * P) ^ (ell - 2 * P) ≤ Nat.factorial ell := by
      exact le_trans (Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)) hfacRaw
    have hpowP : P ^ ell ≤ (2 * P) ^ ell :=
      Nat.pow_le_pow_left (by omega) ell
    have hpowp : p ^ ell ≤ (2 * P) ^ ell := Nat.pow_le_pow_left hpHi ell
    calc
      P ^ ell * p ^ ell ≤ (2 * P) ^ ell * (2 * P) ^ ell :=
        Nat.mul_le_mul hpowP hpowp
      _ = (2 * P) ^ (ell + ell) := by rw [← pow_add]
      _ = (2 * P) ^ ((ell - 2 * P) * 2 + 4 * P) := by
        congr 1
        omega
      _ = ((2 * P) ^ (ell - 2 * P)) ^ 2 * (2 * P) ^ (4 * P) := by
        rw [pow_add, pow_mul]
      _ ≤ (Nat.factorial ell) ^ 2 * (2 * P) ^ (4 * P) := by
        gcongr

/-- **Run-9d fixed-anchor obstruction.**  A nonempty cell at a fixed ordinary
prime scale has high-moment cost at least a fixed positive multiple of the
full time length, for every moment order.  Thus changing from moment one to
`adaptivePrimeMoment` repairs the moving exceptional scale but cannot make the
ordinary-level exceptional cover polylogarithmic. -/
theorem primeHighMomentCountCost_fixed_anchor_lower
    (P ell : ℕ) (Y : Finset ℕ) (p : ℕ)
    (hP : 1 ≤ P) (hp0 : 0 < p) (hpY : p ∈ Y) (hpHi : p ≤ 2 * P)
    (T V lam : ℝ) (hT : 0 ≤ T) (hV : 0 < V) (hV1 : V ≤ 1)
    (hlam : 0 < lam) :
    Real.exp Real.pi * (T + 1) / (((2 * P) ^ (4 * P) : ℕ) : ℝ) ≤
      primeHighMomentCountCost P ell Y T V lam := by
  have hP0 : 0 < P := by omega
  have hPpow : (0 : ℝ) < ((P ^ ell : ℕ) : ℝ) := by positivity
  have hppow : (0 : ℝ) < ((p ^ ell : ℕ) : ℝ) := by positivity
  have hC : (0 : ℝ) < (((2 * P) ^ (4 * P) : ℕ) : ℝ) := by positivity
  have hdenNat := fixed_anchor_denominator_le P ell p hP hpHi
  have hden : ((P ^ ell : ℕ) : ℝ) * ((p ^ ell : ℕ) : ℝ) ≤
      (Nat.factorial ell : ℝ) ^ 2 * (((2 * P) ^ (4 * P) : ℕ) : ℝ) := by
    exact_mod_cast hdenNat
  have hratio : (1 : ℝ) / (((2 * P) ^ (4 * P) : ℕ) : ℝ) ≤
      (Nat.factorial ell : ℝ) ^ 2 /
        (((P ^ ell : ℕ) : ℝ) * ((p ^ ell : ℕ) : ℝ)) := by
    apply (div_le_div_iff₀ hC (mul_pos hPpow hppow)).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hden
  have hT1 : 0 ≤ T + 1 := by linarith
  have hcore : (T + 1) / (((2 * P) ^ (4 * P) : ℕ) : ℝ) ≤
      ((T + 1) / ((P ^ ell : ℕ) : ℝ)) *
        ((Nat.factorial ell : ℝ) ^ 2 * ((1 : ℝ) / p) ^ ell) := by
    have hmul := mul_le_mul_of_nonneg_left hratio hT1
    have hinvPow : ((1 : ℝ) / p) ^ ell =
        1 / ((p ^ ell : ℕ) : ℝ) := by
      rw [one_div_pow]
      norm_cast
    rw [hinvPow]
    convert hmul using 1 <;> field_simp
  have hmass : (1 : ℝ) / p ≤ ∑ q ∈ Y, (1 : ℝ) / q := by
    exact Finset.single_le_sum (s := Y) (f := fun q : ℕ => (1 : ℝ) / q)
      (fun q _ => by positivity) hpY
  have hmassPow : ((1 : ℝ) / p) ^ ell ≤
      (∑ q ∈ Y, (1 : ℝ) / q) ^ ell := by
    exact pow_le_pow_left₀ (by positivity) hmass ell
  have hcoreY : (T + 1) / (((2 * P) ^ (4 * P) : ℕ) : ℝ) ≤
      ((T + 1) / ((P ^ ell : ℕ) : ℝ)) *
        ((Nat.factorial ell : ℝ) ^ 2 *
          (∑ q ∈ Y, (1 : ℝ) / q) ^ ell) := by
    refine hcore.trans ?_
    gcongr
  have hfirst : (T + 1) / ((P ^ ell : ℕ) : ℝ) ≤
      (T + 1) / ((P ^ ell : ℕ) : ℝ) + 2 * ((2 ^ ell : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ 2 * ((2 ^ ell : ℕ) : ℝ) := by positivity
    linarith
  have hlast : (1 : ℝ) ≤
      (1 + lam) + (1 / lam) *
        (2 * Real.pi * Real.log ((2 * P) ^ ell)) ^ 2 := by
    have hinv : 0 ≤ (1 : ℝ) / lam := by positivity
    have hsq := sq_nonneg (2 * Real.pi * Real.log ((2 * P) ^ ell))
    nlinarith [mul_nonneg hinv hsq]
  have hmass0 : 0 ≤ (Nat.factorial ell : ℝ) ^ 2 *
      (∑ q ∈ Y, (1 : ℝ) / q) ^ ell := by
    positivity
  let numerator : ℝ := Real.exp Real.pi *
      ((T + 1) / ((P ^ ell : ℕ) : ℝ) + 2 * ((2 ^ ell : ℕ) : ℝ)) *
      ((Nat.factorial ell : ℝ) ^ 2 *
        (∑ q ∈ Y, (1 : ℝ) / q) ^ ell) *
      ((1 + lam) + (1 / lam) *
        (2 * Real.pi * Real.log ((2 * P) ^ ell)) ^ 2)
  have hnum0 : 0 ≤ numerator := by
    dsimp [numerator]
    positivity
  have htoNum : Real.exp Real.pi * (T + 1) /
      (((2 * P) ^ (4 * P) : ℕ) : ℝ) ≤ numerator := by
    calc
      Real.exp Real.pi * (T + 1) / (((2 * P) ^ (4 * P) : ℕ) : ℝ)
          = Real.exp Real.pi * ((T + 1) /
              (((2 * P) ^ (4 * P) : ℕ) : ℝ)) := by ring
      _ ≤ Real.exp Real.pi *
          (((T + 1) / ((P ^ ell : ℕ) : ℝ)) *
            ((Nat.factorial ell : ℝ) ^ 2 *
              (∑ q ∈ Y, (1 : ℝ) / q) ^ ell)) := by
        gcongr
      _ ≤ Real.exp Real.pi *
          (((T + 1) / ((P ^ ell : ℕ) : ℝ) + 2 * ((2 ^ ell : ℕ) : ℝ)) *
            ((Nat.factorial ell : ℝ) ^ 2 *
              (∑ q ∈ Y, (1 : ℝ) / q) ^ ell)) := by
        gcongr
      _ ≤ numerator := by
        dsimp [numerator]
        have hcoef : 0 ≤ Real.exp Real.pi *
            (((T + 1) / ((P ^ ell : ℕ) : ℝ) + 2 * ((2 ^ ell : ℕ) : ℝ)) *
              ((Nat.factorial ell : ℝ) ^ 2 *
                (∑ q ∈ Y, (1 : ℝ) / q) ^ ell)) := by
          positivity
        simpa only [mul_one, mul_assoc] using
          mul_le_mul_of_nonneg_left hlast hcoef
  have hVpow : 0 < V ^ (2 * ell) := pow_pos hV _
  have hVpow1 : V ^ (2 * ell) ≤ 1 := pow_le_one₀ hV.le hV1
  have hnumDiv : numerator ≤ numerator / V ^ (2 * ell) := by
    apply (le_div_iff₀ hVpow).2
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hVpow1 hnum0
  refine htoNum.trans ?_
  rw [show primeHighMomentCountCost P ell Y T V lam =
      numerator / V ^ (2 * ell) by
    unfold primeHighMomentCountCost numerator
    rfl]
  exact hnumDiv

/-- Nonnegativity of the high-moment cost with the conditions used by the
exceptional cover. -/
theorem primeHighMomentCountCost_nonneg_of
    (P ell : ℕ) (Y : Finset ℕ) (T V lam : ℝ)
    (hT : 0 ≤ T) (hV : V ≠ 0) (hlam : 0 < lam) :
    0 ≤ primeHighMomentCountCost P ell Y T V lam := by
  unfold primeHighMomentCountCost
  have hsum : 0 ≤ ∑ p ∈ Y, (1 : ℝ) / p := by positivity
  have hfirst : 0 ≤ (T + 1) / ((P ^ ell : ℕ) : ℝ) +
      2 * ((2 ^ ell : ℕ) : ℝ) := by positivity
  have hlast : 0 ≤ (1 + lam) + (1 / lam) *
      (2 * Real.pi * Real.log ((2 * P) ^ ell)) ^ 2 := by
    have : 0 ≤ (1 / lam) *
        (2 * Real.pi * Real.log ((2 * P) ^ ell)) ^ 2 := by positivity
    linarith
  have hden : 0 ≤ V ^ (2 * ell) := by
    rw [Nat.mul_comm 2 ell, pow_mul]
    positivity
  exact div_nonneg (mul_nonneg (mul_nonneg (by positivity)
    (mul_nonneg (by positivity) (pow_nonneg hsum ell))) hlast) hden

/-- A nonempty cell of the last fixed ordinary level inserts the preceding
linear lower bound into `sharpExceptionalCoverBound` itself. -/
theorem sharpExceptionalCoverBound_fixed_anchor_lower
    (P : ℕ → Finset ℕ) (N v0 v1 : ℕ → ℕ) (alpha : ℕ → ℝ)
    (J : ℕ) (Panchor coverEll : ℕ → ℕ) (T : ℝ)
    (coverLam : ℕ → ℝ) (r p : ℕ)
    (hr : r ∈ Finset.Ico (v0 (J - 1)) (v1 (J - 1) + 1))
    (hN : 0 < N (J - 1)) (halpha : 0 ≤ alpha (J - 1))
    (hPanchor : 1 ≤ Panchor r)
    (hp0 : 0 < p)
    (hp : p ∈ eadicCell (P (J - 1)) (2 * N (J - 1)) r)
    (hpHi : p ≤ 2 * Panchor r)
    (hT : 0 ≤ T)
    (hlam : ∀ s ∈ Finset.Ico (v0 (J - 1)) (v1 (J - 1) + 1),
      0 < coverLam s) :
    2 * (Real.exp Real.pi * (T + 1) /
        (((2 * Panchor r) ^ (4 * Panchor r) : ℕ) : ℝ)) ≤
      sharpExceptionalCoverBound P N v0 v1 alpha J Panchor coverEll T coverLam := by
  let I := Finset.Ico (v0 (J - 1)) (v1 (J - 1) + 1)
  let threshold : ℕ → ℝ := fun s =>
    Real.exp (-(alpha (J - 1) * (s : ℝ) /
      ((2 * N (J - 1) : ℕ) : ℝ)))
  have hthreshold0 : 0 < threshold r := Real.exp_pos _
  have hden : (0 : ℝ) < ((2 * N (J - 1) : ℕ) : ℝ) := by positivity
  have hexpNonpos : -(alpha (J - 1) * (r : ℝ) /
      ((2 * N (J - 1) : ℕ) : ℝ)) ≤ 0 := by
    have : 0 ≤ alpha (J - 1) * (r : ℝ) /
        ((2 * N (J - 1) : ℕ) : ℝ) := by positivity
    linarith
  have hthreshold1 : threshold r ≤ 1 := by
    dsimp [threshold]
    exact Real.exp_le_one_iff.mpr hexpNonpos
  have hcostLower := primeHighMomentCountCost_fixed_anchor_lower
    (Panchor r) (coverEll r)
    (eadicCell (P (J - 1)) (2 * N (J - 1)) r) p
    hPanchor hp0 hp hpHi T (threshold r) (coverLam r)
    hT hthreshold0 hthreshold1 (hlam r hr)
  have hterm : 2 * (Real.exp Real.pi * (T + 1) /
      (((2 * Panchor r) ^ (4 * Panchor r) : ℕ) : ℝ)) ≤
      2 * primeHighMomentCountCost (Panchor r) (coverEll r)
        (eadicCell (P (J - 1)) (2 * N (J - 1)) r) T
        (threshold r) (coverLam r) := by
    gcongr
  have hsum : 2 * primeHighMomentCountCost (Panchor r) (coverEll r)
        (eadicCell (P (J - 1)) (2 * N (J - 1)) r) T
        (threshold r) (coverLam r) ≤
      ∑ s ∈ I, 2 * primeHighMomentCountCost (Panchor s) (coverEll s)
        (eadicCell (P (J - 1)) (2 * N (J - 1)) s) T
        (threshold s) (coverLam s) := by
    apply Finset.single_le_sum (s := I)
      (f := fun s => 2 * primeHighMomentCountCost (Panchor s) (coverEll s)
        (eadicCell (P (J - 1)) (2 * N (J - 1)) s) T
        (threshold s) (coverLam s))
    · intro s hs
      exact mul_nonneg (by norm_num) (primeHighMomentCountCost_nonneg_of
        (Panchor s) (coverEll s)
        (eadicCell (P (J - 1)) (2 * N (J - 1)) s) T
        (threshold s) (coverLam s) hT (Real.exp_ne_zero _)
        (hlam s (by simpa [I] using hs)))
    · simpa [I] using hr
  refine hterm.trans ?_
  simpa [sharpExceptionalCoverBound, I, threshold] using hsum

/-- Any proposed upper bound for a cover containing a fixed ordinary anchor
forces the time scale to obey the displayed linear upper bound. -/
theorem time_scale_bound_of_fixed_anchor_cover_le
    (P : ℕ) (hP : 1 ≤ P) (T K L : ℝ)
    (hKlower : 2 * (Real.exp Real.pi * (T + 1) /
      (((2 * P) ^ (4 * P) : ℕ) : ℝ)) ≤ K)
    (hKupper : K ≤ L) :
    T + 1 ≤ (((2 * P) ^ (4 * P) : ℕ) : ℝ) * L /
      (2 * Real.exp Real.pi) := by
  have hC : (0 : ℝ) < (((2 * P) ^ (4 * P) : ℕ) : ℝ) := by
    have : 0 < P := by omega
    positivity
  have hexp : 0 < 2 * Real.exp Real.pi := by positivity
  have hraw := hKlower.trans hKupper
  have hraw' : (2 * Real.exp Real.pi * (T + 1)) /
      (((2 * P) ^ (4 * P) : ℕ) : ℝ) ≤ L := by
    convert hraw using 1
    ring
  have hcross : 2 * Real.exp Real.pi * (T + 1) ≤
      (((2 * P) ^ (4 * P) : ℕ) : ℝ) * L := by
    have := (div_le_iff₀ hC).mp hraw'
    nlinarith
  apply (le_div_iff₀ hexp).2
  nlinarith

/-- The exact contribution which any `hfitInt` using a fixed ordinary anchor
must absorb.  Substituting `V = (log A)^(-100)`, `D <= A+1`, and the A.2
cutoff `T` proportional to `A/h` makes the left side a fixed multiple of
`sqrt A/(log A)^200`. -/
theorem fixed_anchor_hfitInt_forces_linear_time
    (T V X K L D C budget : ℝ)
    (hT : 0 ≤ T) (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hD : 0 < D) (hC : 0 < C)
    (hKlower : 2 * (Real.exp Real.pi * (T + 1) / C) ≤ K)
    (hfit : 2 * V ^ 2 * (64 * ((X + K * Real.sqrt T) * L * (2 / D))) ≤ budget) :
    512 * Real.exp Real.pi * V ^ 2 * (T + 1) * Real.sqrt T * L /
        (C * D) ≤ budget := by
  have hsqrt : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
  have hlower :
      2 * V ^ 2 *
          (64 * (((2 * (Real.exp Real.pi * (T + 1) / C)) * Real.sqrt T) *
            L * (2 / D))) ≤
        2 * V ^ 2 * (64 * ((X + K * Real.sqrt T) * L * (2 / D))) := by
    gcongr
    nlinarith
  calc
    512 * Real.exp Real.pi * V ^ 2 * (T + 1) * Real.sqrt T * L /
          (C * D) =
        2 * V ^ 2 *
          (64 * (((2 * (Real.exp Real.pi * (T + 1) / C)) * Real.sqrt T) *
            L * (2 / D))) := by field_simp; ring
    _ ≤ 2 * V ^ 2 * (64 * ((X + K * Real.sqrt T) * L * (2 / D))) := hlower
    _ ≤ budget := hfit

/-- The preceding obstruction specialized to the exact `hfitInt` expression
of `band_energy_typicalS_le_of_schedule_sharp`. -/
theorem schedule_hfitInt_forces_fixed_anchor_term
    (P : ℕ → Finset ℕ) (N v0 v1 : ℕ → ℕ) (alpha : ℕ → ℝ)
    (J : ℕ) (Panchor coverEll : ℕ → ℕ) (T : ℝ)
    (coverLam : ℕ → ℝ) (r p A Delta q : ℕ) (budget : ℝ)
    (hr : r ∈ Finset.Ico (v0 (J - 1)) (v1 (J - 1) + 1))
    (hN : 0 < N (J - 1)) (halpha : 0 ≤ alpha (J - 1))
    (hPanchor : 1 ≤ Panchor r)
    (hp0 : 0 < p)
    (hp : p ∈ eadicCell (P (J - 1)) (2 * N (J - 1)) r)
    (hpHi : p ≤ 2 * Panchor r)
    (hT1 : 1 ≤ T)
    (hlam : ∀ s ∈ Finset.Ico (v0 (J - 1)) (v1 (J - 1) + 1),
      0 < coverLam s)
    (hfit :
      2 * exceptionalSplitThreshold A ^ 2 *
        (64 * ((((A + Delta) / q : ℕ) : ℝ) +
            sharpExceptionalCoverBound P N v0 v1 alpha J
              Panchor coverEll T coverLam * Real.sqrt T) *
          (Real.log (2 * T) + 1) *
          (2 / (((A / q + 1 : ℕ) : ℝ)))) ≤ budget) :
    512 * Real.exp Real.pi * exceptionalSplitThreshold A ^ 2 *
        (T + 1) * Real.sqrt T * (Real.log (2 * T) + 1) /
        ((((2 * Panchor r) ^ (4 * Panchor r) : ℕ) : ℝ) *
          (((A / q + 1 : ℕ) : ℝ))) ≤ budget := by
  have hT : 0 ≤ T := zero_le_one.trans hT1
  have hlog : 0 ≤ Real.log (2 * T) + 1 := by
    have htwo : (1 : ℝ) ≤ 2 * T := by linarith
    have := Real.log_nonneg htwo
    linarith
  have hcover := sharpExceptionalCoverBound_fixed_anchor_lower
    P N v0 v1 alpha J Panchor coverEll T coverLam r p hr hN halpha
    hPanchor hp0 hp hpHi hT hlam
  exact fixed_anchor_hfitInt_forces_linear_time T (exceptionalSplitThreshold A)
    (((A + Delta) / q : ℕ) : ℝ)
    (sharpExceptionalCoverBound P N v0 v1 alpha J Panchor coverEll T coverLam)
    (Real.log (2 * T) + 1) ((A / q + 1 : ℕ) : ℝ)
    (((2 * Panchor r) ^ (4 * Panchor r) : ℕ) : ℝ) budget
    hT (by positivity) hlog (by positivity) (by positivity) hcover
    (by simpa only [mul_assoc] using hfit)

/-- The square-root growth in the preceding necessary condition beats the
fixed split loss by any prescribed constant. -/
theorem exists_const_mul_log_pow_le_sqrt (M : ℝ) (hM : 0 < M) :
    ∃ A0 : ℕ, ∀ A : ℕ, A0 ≤ A →
      M * Real.log (A : ℝ) ^ 200 ≤ Real.sqrt A := by
  obtain ⟨A0, hA0⟩ := exists_forall_polylog_le (M ^ 2) 1 (sq_pos_of_pos hM)
    (by norm_num) 1 400
  refine ⟨A0, fun A hA => ?_⟩
  obtain ⟨hA2, hbound⟩ := hA0 A hA
  have hlog0 : 0 ≤ Real.log (A : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ A))
  have hlogMax : Real.log (A : ℝ) ≤ max (Real.log (A : ℝ)) 1 :=
    le_max_left _ _
  have hpow : Real.log (A : ℝ) ^ 400 ≤
      max (Real.log (A : ℝ)) 1 ^ 400 :=
    pow_le_pow_left₀ hlog0 hlogMax 400
  have hsquare : (M * Real.log (A : ℝ) ^ 200) ^ 2 ≤ (A : ℝ) := by
    have hM20 : 0 ≤ M ^ 2 := sq_nonneg M
    calc
      (M * Real.log (A : ℝ) ^ 200) ^ 2 =
          M ^ 2 * Real.log (A : ℝ) ^ 400 := by ring
      _ ≤ M ^ 2 * max (Real.log (A : ℝ)) 1 ^ 400 :=
        mul_le_mul_of_nonneg_left hpow hM20
      _ = M ^ 2 * max (1 * Real.log (A : ℝ) ^ 1) 1 ^ 400 := by simp
      _ ≤ (A : ℝ) := hbound
  exact Real.le_sqrt_of_sq_le hsquare

end Tao2015

end MoltResearch
