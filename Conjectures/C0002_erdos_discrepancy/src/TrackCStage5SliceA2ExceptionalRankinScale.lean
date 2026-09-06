import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalRankinBasic

/-!
# Track R A2-V': exceptional Rankin scale

After the square-root cutoff and representative are removed, the quotient
retains one eighth of `log A₁`.  Dividing by `log Q_U` converts this into
the decay exponent `(log A₁)^(1/50)/(16 R)`.
-/

namespace MoltResearch

namespace Tao2015

/-- The remote upper endpoint has its defining sublinear logarithmic size. -/
theorem exceptionalPrimeUpper_log_le
    (A1 : ℕ) (epsc : ℝ) (hA1 : 1 ≤ A1) :
    Real.log (exceptionalPrimeUpper A1 epsc : ℝ) ≤
      (exceptionalIntervalRatio epsc : ℝ) *
        (Real.log 4 + (Real.log (A1 : ℝ)) ^ (49 / 50 : ℝ)) := by
  let P := exceptionalPrimeLower A1
  let R := exceptionalIntervalRatio epsc
  let X := Real.log (A1 : ℝ)
  have hPpos : (0 : ℝ) < P := by
    exact_mod_cast (show 0 < P by
      dsimp [P]
      have := exceptionalPrimeLower_three_le A1
      omega)
  have hbase := exceptionalPrimeLower_cast_le_four_exp A1 hA1
  have hlogP : Real.log (P : ℝ) ≤
      Real.log 4 + X ^ (49 / 50 : ℝ) := by
    calc
      Real.log (P : ℝ) ≤
          Real.log (4 * Real.exp (X ^ (49 / 50 : ℝ))) :=
        Real.log_le_log hPpos (by simpa [P, X] using hbase)
      _ = Real.log 4 + X ^ (49 / 50 : ℝ) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_exp]
  unfold exceptionalPrimeUpper
  rw [Nat.cast_pow, Real.log_pow]
  exact mul_le_mul_of_nonneg_left hlogP (by positivity)

/-- The integer quotient divided by the square-root cutoff keeps one eighth
of the base logarithm. -/
theorem sliceA2Exceptional_cutoff_quotient_log_lower
    (A1 A q : ℕ) (hA1 : 2 ≤ A1) (hA : A1 ≤ A) (hq : 1 ≤ q)
    (hq4 : q ^ 4 ≤ A1)
    (hlog8 : 8 * Real.log 8 ≤ Real.log (A1 : ℝ)) :
    Real.log (A1 : ℝ) / 8 ≤
      Real.log (((A / q : ℕ) : ℝ) / exceptionalSharpCutoff A) := by
  let a := A / q
  let x0 := exceptionalSharpCutoff A
  have hq0 : 0 < q := by omega
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hq2q4 : q ^ 2 ≤ q ^ 4 := pow_le_pow_right' hq (by omega)
  have hq2A : q * q ≤ A := by
    simpa [pow_two] using hq2q4.trans (hq4.trans hA)
  have hqa : q ≤ a := by
    dsimp [a]
    exact (Nat.le_div_iff_mul_le hq0).2 hq2A
  have ha : 1 ≤ a := hq.trans hqa
  have hA_lt : A < q * (a + 1) := by
    simpa [a] using Nat.lt_mul_div_succ A hq0
  have hA_twoqa : A < 2 * q * a := by
    calc
      A < q * (a + 1) := hA_lt
      _ ≤ q * (2 * a) := Nat.mul_le_mul_left q (by omega)
      _ = 2 * q * a := by ring
  have hlogA_twoqa : Real.log (A : ℝ) ≤
      Real.log 2 + Real.log (q : ℝ) + Real.log (a : ℝ) := by
    have hcast : (A : ℝ) ≤ 2 * (q : ℝ) * (a : ℝ) := by
      exact_mod_cast hA_twoqa.le
    calc
      Real.log (A : ℝ) ≤ Real.log (2 * (q : ℝ) * (a : ℝ)) :=
        Real.log_le_log hApos hcast
      _ = Real.log 2 + Real.log (q : ℝ) + Real.log (a : ℝ) := by
        rw [Real.log_mul (by positivity : (2 : ℝ) * q ≠ 0)
            (by exact_mod_cast (show a ≠ 0 by omega)),
          Real.log_mul (by norm_num) (by exact_mod_cast hq0.ne')]
  have hlogq : Real.log (q : ℝ) ≤ Real.log (A1 : ℝ) / 4 := by
    have hcast : ((q : ℝ) ^ 4) ≤ (A1 : ℝ) := by exact_mod_cast hq4
    have hlogs := Real.log_le_log (by positivity) hcast
    rw [Real.log_pow] at hlogs
    norm_num at hlogs
    linarith
  have hlogA1A : Real.log (A1 : ℝ) ≤ Real.log (A : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hA)
  have hx0log := exceptionalSharpCutoff_log_le A (by omega)
  have hx0pos : (0 : ℝ) < x0 := by
    have hlower := exceptionalSharpCutoff_real_lower A
    have hsqrt : 0 < Real.sqrt (3 * (2 * (A : ℝ) + 1)) := by positivity
    exact hsqrt.trans_le (by simpa [x0] using hlower)
  have hapos : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  change Real.log (A1 : ℝ) / 8 ≤ Real.log ((a : ℝ) / (x0 : ℝ))
  rw [Real.log_div hapos.ne' hx0pos.ne']
  have hlog8eq : Real.log 8 = Real.log 2 + Real.log 4 := by
    rw [show (8 : ℝ) = 2 * 4 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  rw [hlog8eq] at hlog8
  have hx0log' : Real.log (x0 : ℝ) ≤
      Real.log 4 + Real.log (A : ℝ) / 2 := by simpa [x0] using hx0log
  linarith

/-- The Rankin factor from the retained quotient scale has the stated
one-fiftieth-power exponential decay. -/
theorem sliceA2Exceptional_rankin_rpow_le_decay
    (A1 A q : ℕ) (epsc : ℝ)
    (hA1 : 4 ≤ A1) (hA : A1 ≤ A) (hq : 1 ≤ q) (hq4 : q ^ 4 ≤ A1)
    (hlog8 : 8 * Real.log 8 ≤ Real.log (A1 : ℝ)) :
    ((((A / q : ℕ) : ℝ) / exceptionalSharpCutoff A) ^
        (-sliceA2ExceptionalRankinS A1 epsc)) ≤
      Real.exp (-((Real.log (A1 : ℝ)) ^ (1 / 50 : ℝ) /
        (16 * (exceptionalIntervalRatio epsc : ℝ)))) := by
  let X := Real.log (A1 : ℝ)
  let Q := exceptionalPrimeUpper A1 epsc
  let R : ℝ := exceptionalIntervalRatio epsc
  let base : ℝ := ((A / q : ℕ) : ℝ) / exceptionalSharpCutoff A
  have hX1 : 1 ≤ X := by
    have hfour : Real.exp 1 < 4 := Real.exp_one_lt_three.trans_le (by norm_num)
    apply (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < A1)).2
    exact hfour.le.trans (by exact_mod_cast hA1)
  have hXpos : 0 < X := zero_lt_one.trans_le hX1
  have hRpos : 0 < R := by
    dsimp [R]
    exact_mod_cast (show 0 < exceptionalIntervalRatio epsc by
      have := exceptionalIntervalRatio_three_le epsc
      omega)
  have hQ3 : 3 ≤ Q := (exceptionalPrimeLower_three_le A1).trans
    (exceptionalPrimeLower_le_upper A1 epsc)
  have hlogQpos : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hroot2 : (2 : ℝ) ≤ X ^ (1 / 2 : ℝ) := by
    have hX4 : (4 : ℝ) ≤ X := by
      have := hlog8
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at this
      norm_num at this
      nlinarith [Real.log_two_gt_d9]
    have hr := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 4) hX4
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc
      (2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) := by norm_num
      _ ≤ X ^ (1 / 2 : ℝ) := hr
  have hlog4 : Real.log 4 ≤ X ^ (49 / 50 : ℝ) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hX1
      (by norm_num : (1 / 2 : ℝ) ≤ 49 / 50)
    have : Real.log 4 ≤ 2 := log_four_le.trans (by norm_num)
    exact this.trans (hroot2.trans hpow)
  have hlogQ : Real.log (Q : ℝ) ≤ 2 * R * X ^ (49 / 50 : ℝ) := by
    have h := exceptionalPrimeUpper_log_le A1 epsc (by omega)
    dsimp [Q, R, X]
    calc
      Real.log (exceptionalPrimeUpper A1 epsc : ℝ) ≤
          (exceptionalIntervalRatio epsc : ℝ) *
            (Real.log 4 + X ^ (49 / 50 : ℝ)) := by simpa [X] using h
      _ ≤ (exceptionalIntervalRatio epsc : ℝ) *
            (2 * X ^ (49 / 50 : ℝ)) := by gcongr; linarith
      _ = 2 * R * X ^ (49 / 50 : ℝ) := by ring
  have hbaseLog : X / 8 ≤ Real.log base := by
    simpa [X, base] using sliceA2Exceptional_cutoff_quotient_log_lower
      A1 A q (by omega) hA hq hq4 hlog8
  have hbasePos : 0 < base := by
    dsimp [base]
    have hq0 : 0 < q := by omega
    have hq2q4 : q ^ 2 ≤ q ^ 4 := pow_le_pow_right' hq (by omega)
    have hq2A : q * q ≤ A := by
      simpa [pow_two] using hq2q4.trans (hq4.trans hA)
    have ha : 1 ≤ A / q := hq.trans ((Nat.le_div_iff_mul_le hq0).2 hq2A)
    have hx0 : 0 < exceptionalSharpCutoff A := by
      have hlower := exceptionalSharpCutoff_real_lower A
      have hsqrt : 0 < Real.sqrt (3 * (2 * (A : ℝ) + 1)) := by positivity
      have : (0 : ℝ) < exceptionalSharpCutoff A := hsqrt.trans_le hlower
      exact_mod_cast this
    positivity
  have hprod : X ^ (1 / 50 : ℝ) * X ^ (49 / 50 : ℝ) = X := by
    rw [← Real.rpow_add hXpos]
    norm_num
  have hdecay : X ^ (1 / 50 : ℝ) / (16 * R) ≤
      Real.log base / Real.log (Q : ℝ) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 16 * R) hlogQpos).2
    have hleft : X ^ (1 / 50 : ℝ) * Real.log (Q : ℝ) ≤
        2 * R * X := by
      calc
        X ^ (1 / 50 : ℝ) * Real.log (Q : ℝ) ≤
            X ^ (1 / 50 : ℝ) *
              (2 * R * X ^ (49 / 50 : ℝ)) := by gcongr
        _ = 2 * R *
            (X ^ (1 / 50 : ℝ) * X ^ (49 / 50 : ℝ)) := by ring
        _ = 2 * R * X := by rw [hprod]
    have hbmul := mul_le_mul_of_nonneg_left hbaseLog
      (by positivity : 0 ≤ 16 * R)
    calc
      X ^ (1 / 50 : ℝ) * Real.log (Q : ℝ) ≤ 2 * R * X := hleft
      _ ≤ Real.log base * (16 * R) := by nlinarith
  rw [Real.rpow_def_of_pos hbasePos]
  apply Real.exp_le_exp.mpr
  unfold sliceA2ExceptionalRankinS
  dsimp [Q] at hdecay
  have : Real.log base * (-(1 / Real.log (Q : ℝ))) =
      -(Real.log base / Real.log (Q : ℝ)) := by ring
  rw [this]
  linarith

end Tao2015

end MoltResearch
