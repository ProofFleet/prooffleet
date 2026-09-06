import Conjectures.C0002_erdos_discrepancy.src.TrackCStage5SliceA2ExceptionalDomination

/-!
# Track R A2-V'-23: uniform endpoint density-error envelopes

The reciprocal-prime mass in `(P,P^R]` is also bounded above by
`log(R+1)+12`.  Together with the lower mass from A2-V'-20, this turns the
finite Turan--Kubilius error into an elementary cardinality-over-scale term.
-/

namespace MoltResearch

namespace Tao2015

open Finset

/-- The upper Mertens estimate over a natural power interval. -/
theorem prime_power_Ioc_mass_upper
    (P R : ℕ) (hP : 3 ≤ P) (hR : 1 ≤ R) :
    ∑ p ∈ (Ioc P (P ^ R)).filter Nat.Prime, (1 : ℝ) / p ≤
      Real.log ((R : ℝ) + 1) + 12 := by
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hPaddpos : (0 : ℝ) < P + 1 := by positivity
  have hlogPadd : 0 < Real.log ((P : ℝ) + 1) :=
    Real.log_pos (by exact_mod_cast (show 1 < P + 1 by omega))
  have hRaddpos : (0 : ℝ) < R + 1 := by positivity
  have hPle : P ≤ P ^ R := Nat.le_pow (by omega)
  have hnat : P ^ R + 1 ≤ (P + 1) ^ (R + 1) := by
    have hpow : P ^ R ≤ (P + 1) ^ R :=
      pow_le_pow_left' (by omega : P ≤ P + 1) R
    have hone : 1 ≤ (P + 1) ^ R := Nat.one_le_pow R (P + 1) (by omega)
    calc
      P ^ R + 1 ≤ (P + 1) ^ R + (P + 1) ^ R :=
        Nat.add_le_add hpow hone
      _ ≤ (P + 1) * (P + 1) ^ R := by
        nlinarith [pow_pos (by omega : 0 < P + 1) R]
      _ = (P + 1) ^ (R + 1) := by
        rw [pow_succ]
        ring
  have hlog0 :
      Real.log (((P ^ R : ℕ) : ℝ) + 1) ≤
        ((R : ℝ) + 1) * Real.log ((P : ℝ) + 1) := by
    calc
      Real.log (((P ^ R : ℕ) : ℝ) + 1) ≤
          Real.log ((((P + 1) ^ (R + 1) : ℕ) : ℝ)) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast hnat
      _ = ((R : ℝ) + 1) * Real.log ((P : ℝ) + 1) := by
        rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Real.log_pow]
        push_cast
        rfl
  have hloglog :
      Real.log (Real.log (((P ^ R : ℕ) : ℝ) + 1)) ≤
        Real.log (((R : ℝ) + 1) * Real.log ((P : ℝ) + 1)) := by
    apply Real.log_le_log
    · exact Real.log_pos (by
        have hpPow : (0 : ℝ) < ((P ^ R : ℕ) : ℝ) := by
          exact_mod_cast (pow_pos (show 0 < P by omega) R)
        linarith)
    · exact hlog0
  have hmertens := prime_Ioc_mass_upper_mertens P (P ^ R) hP hPle
  rw [Real.log_mul hRaddpos.ne' hlogPadd.ne'] at hloglog
  linarith

/-- A lower mass, upper mass, and cardinality bound give a closed envelope
for one finite TK error. -/
theorem sliceA2TKFiniteError_le
    (A : ℕ) (P : Finset ℕ) (epsc Emax Q : ℝ)
    (hA : 0 < A) (hepsc : 0 < epsc) (hEmax : 0 ≤ Emax)
    (hmassLo : 4 / epsc ≤ ∑ p ∈ P, (1 : ℝ) / p)
    (hmassHi : ∑ p ∈ P, (1 : ℝ) / p ≤ Emax)
    (hcard : (P.card : ℝ) ≤ Q) :
    sliceA2TKFiniteError A P ≤
      (epsc ^ 2 / 16) *
        (3 * (Q + Q ^ 2) + 6 * Emax * Q) / A := by
  let E := ∑ p ∈ P, (1 : ℝ) / p
  let c : ℝ := P.card
  have hE : 0 < E := lt_of_lt_of_le (by positivity) hmassLo
  have hc0 : 0 ≤ c := by positivity
  have hQ0 : 0 ≤ Q := hc0.trans hcard
  have hrecip : 1 / E ≤ epsc / 4 := by
    rw [div_le_iff₀ hE]
    have hmassLo' : 4 / epsc ≤ E := by simpa [E] using hmassLo
    calc
      1 = (epsc / 4) * (4 / epsc) := by field_simp
      _ ≤ (epsc / 4) * E :=
        mul_le_mul_of_nonneg_left hmassLo' (by positivity)
  have hrecipSq : 1 / E ^ 2 ≤ epsc ^ 2 / 16 := by
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / E) hrecip 2
    calc
      1 / E ^ 2 = (1 / E) ^ 2 := by ring
      _ ≤ (epsc / 4) ^ 2 := hs
      _ = epsc ^ 2 / 16 := by ring
  have hquad : c + c ^ 2 ≤ Q + Q ^ 2 := by
    have hs : c ^ 2 ≤ Q ^ 2 := (sq_le_sq₀ hc0 hQ0).2 hcard
    linarith
  have hnum :
      3 * (c + c ^ 2) + 6 * E * c ≤
        3 * (Q + Q ^ 2) + 6 * Emax * Q := by
    have hEc : E * c ≤ Emax * Q :=
      mul_le_mul (by simpa [E] using hmassHi) hcard hc0 hEmax
    linarith
  have hnum0 : 0 ≤ 3 * (c + c ^ 2) + 6 * E * c := by positivity
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  unfold sliceA2TKFiniteError
  dsimp only
  change (3 * ((c + c ^ 2) / (A : ℝ)) +
      2 * E * (3 * (c / (A : ℝ)))) / E ^ 2 ≤ _
  calc
    (3 * ((c + c ^ 2) / (A : ℝ)) +
        2 * E * (3 * (c / (A : ℝ)))) / E ^ 2 =
        (1 / E ^ 2) * (3 * (c + c ^ 2) + 6 * E * c) / A := by
      field_simp
      ring
    _ ≤ (epsc ^ 2 / 16) *
        (3 * (c + c ^ 2) + 6 * E * c) / A := by
      gcongr
    _ ≤ (epsc ^ 2 / 16) *
        (3 * (Q + Q ^ 2) + 6 * Emax * Q) / A := by
      gcongr

end Tao2015

end MoltResearch
